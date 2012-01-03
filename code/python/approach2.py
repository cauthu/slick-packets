'''
this is the "use-a-primary-path" approach.

currently, assumes all links in the original graph have unit weights.

unless otherwise specified, sources and destinations are s and d or
Src and Dst.

definitions:
 
- "primary path": the main path from src to dst. it might be the
  shortest path, or might be some other path, depending on what the
  user wants. some abbrivations: pp.
 
- "primary node": is a node on the primary path. unless otherwise
  specified, these nodes have upper-case labels. some abbrivations:
  pnode.

- "secondary node": is a node not on the primary path. its purpose of
  course is to serve detour paths. some abbrivations: snode.

- "detour path": each primary node, if possible, is given an alternate
  route to the destination in case its outgoing link is down. a detour
  path might require traversing backwards along the primary
  path. NOTE/XXX/TODO: each primary node might have multiple
  "alternate" successors, but only ONE is for itself, the others are
  MEANT to serve as alternate for successor primary nodes when they
  need to backtrack. MAYBE we will consider allowing a primary node to
  these nodes when both its own primary and detours links are down.

- "detour node": is a node on a detour path. it could be a primary
  node or a secondary node. some abbrivations: dnode.
 
- "backtracking": is the portion of a detour path that traverses
  backwards farther away from the destination. the backtracking
  portion ALWAYS ends at a primary node, after which it gets back on a
  secondary portion getting closer to the destination.

  backtracking might involve traversing multiple segments of primary
  nodes and secondary nodes.

  for example:

       k--l--m--n--o--p
       |              |
       | B  D  F      q
       |/\ /\ /\      |
  Src--A  C  E  G-----Dst
        \/ \/ \/
         h  i  j

  the detour path for G has to backtrack to A and then proceed thru
  k. however, the detour path MIGHT go through F or j, D or i, B or h.
  whole portion of this detour path from F (or j) up to and including
  A is backtracking.

if our goal is to be resilient againt only one _link_ failure, then
non-primary nodes should only need one successor.
 
example (returned by genGraph1):
 
     g-----h--i
     | f      |
     |/\      |
Src--A--B-----C--D--E--Dst
     |              |
     j--k--l--m--n--o
 
source is Src. destination is Dst.
 
suppose the user wants the shortest paths when picking the primary
path and detour paths, then:
     
the primary path is Src->A->B->C->D->E->Dst.
 
the detour paths are:
 
- for primary node A: A->f->B. there is no backtracking.
 
- for primary node B: B->A->g->.... this requires backtracking.
 
- for primary node C: C->B->A->j->.... this requires backtracking.
 
- for primary node D: D->C->B->A->j->.... this requires backtracking
 
- for primary node E: none.
 
primary node A has 3 detour successors f, g, and j. only f is for A
itself. g is to serve B\'s backtrack, and j is to serve C and D\'s
backtrack.
'''

import sys

# so that we get a dev version of nx, which doesnt have the problem
# where draw_graphviz errors on edges that contain non-string
# attributes, eg, the algorithms require edge weights to be numbers.
sys.path = ['/home/me/.local/lib/python2.6/site-packages'] + sys.path

#  import matplotlib.pyplot as plt


import networkx as nx # requires networkx version >= 1.0rc1

import math, re
import os
import copy

import pdb

draw = nx.draw
drawg = nx.draw_graphviz

NaN = float('nan')


Revision = '$Revision: 1034 $'
Id = '$Id$'


###################################################################3
def getDg(G, s, d, weighted,
          everyOtherNodeUsePredecessor=False,
          onlySrcHasRealDetourPaths=False,
          preferDownStreamPEdges=False):
    '''

    !!!!!  NOTE !!!!!

    will NOT make a copy of G. will remove edges from it and add them
    back in. the intention is to effectively leave G the same at the
    end.

    !!!!!!!!!!!!!!!!!

    "weighted": if true, will use networkx.dijkstra_path(). otherwise,
    use networkx.shortest_path(). dijkstra_path() takes much longer,
    for example, with the caida graph, it could take 5 seconds, while
    shortest_path() is instantaneous.


    high level: pick a primary path. then if possible, for each node
    on the primary path, give it a detour (**) in case the successor
    link/node fails. the detour might involve backtracking, ie,
    revisting our predecessor.

    "everyOtherNodeUsePredecessor": if true, then only primary nodes
    at indices 0 (the source), 2, 4, etc have their own detour paths,
    and those at indices 1, 3, 5 etc backtrack to their predecessors
    and use their predecessors\' detour paths if exist. if the
    predecessor doesnt have a detour path, then these nodes at 1, 3, 5
    etc use their own detour paths.

    "preferDownStreamPEdges": if true, when finding the detour paths,
    prefer downstream edges of the primary path. for each node, it
    sets the weights of all the downstream primary edges to zero
    before finding the detour path. then the original weights are
    restored.
    
    "onlySrcHasRealDetourPaths": if True, then once a primary path has
    been selected, src will have a dpath that is edge- and
    node-disjoint with the primary path. if no such path is possible,
    then will return nothing. otherwise, all the other primary nodes
    will simply backtrack to src and use src\'s detour path.

    the primary path will be used as long as there are no link/node
    failures, which we assume is majority of the time, so we want the
    primary path to be as short as possible.



    step 1: pick the primary path: get shortest path (*) s->d. add
    those nodes and edges to the final graph.

    step 2: for each node U on the shortest path, pretend its next
    edge is "removed", then again find a new shortest path U->d. add
    those nodes and edges to the final graph.


    (*) NOTE: that this might not always result in the smallest
    graph. for example, consider this graph:

       a--b--c
     s/       \d
     |\e__f__g/|
     | |  |  | |
     |_h__i__j_|


     there are 3 shortest paths: s-a-b-c-d, s-e-f-g-d, and s-h-i-j-d.

     if we pick s-a-b-c-d to be primary path, then the detour for each
     node on that path requires backtracking and traversing either of
     the other two shortest paths.

     the links in the primary path:

     s->a, ..., c->d  (4 edges)

     and the links in the detours:

     s->e, a->s, b->a, c->b, plus the links in s->e->...->d (only
     counting 1 edge s->e here)

     to prevent loops, if we use the "virtual" node approach for the
     detours, then:

       * for failure of link a->b, we need a separate "node" s\' for
         the backtrack edge a->s\' and also edge s\'->e.  (2 edges)

       * similarly, for failure of link b->c, we need a\' for the
         backtrack edge b->a\' and also edge a\'->s\'.  (2 edges)

       * for failure of link c->d, we need b\' for backtrack edge
         c->b\' and also edge b\'->a\'.  (2 edges)

         thats a total of 11 nodes and 14 edges.

     but if we pick s-e-f-g-d, then the detour does not require
     backtracking.

     the links in the primary path:

     s->e, ..., g->d

     then the detours:

     s->h, g->h, f->i, g->j, j->d

     thats a total of 8 nodes and 11 edges if we use the "virtual"
     node approach.

     ===> XXX: so a naive shortest path as the primary path is not the
     best.


     (**) NOTE: when creating detours, it\'s possible to form cycles,
     either "backtracking", or the following graph.

       c-e-f
      /|   |
     s-a---b-d

     primart path is s->a->b->d.

     the shortest detour path when s->a fails is s->c->a->..., and the
     shortest detour path when a->b fails is a->c->e->...

    '''

    if weighted:
        getPrimaryPath = getDetourPath = nx.dijkstra_path
        pass
    else:
        getPrimaryPath = getDetourPath = nx.shortest_path
        if preferDownStreamPEdges:
            getDetourPath = nx.dijkstra_path
            pass
        pass

    g = G

    primaryPath = None
    try:
        primaryPath = getPrimaryPath(g, s, d)
        pass
    except nx.NetworkXNoPath, exc:
        pass

    if not primaryPath:
        # no path possible
        return None, None

    if onlySrcHasRealDetourPaths:
        detourPaths = {}
        # remove all nodes in the primaryPath except src and dst
        savedEdges = [] # includes edge data
        for pnode in primaryPath[1:-1]:
            savedEdges.extend(g.edges(pnode, data=True))
            g.remove_node(pnode)
            pass
        # now find a detour path for the src
        src_dp = None
        try:
            src_dp = getDetourPath(g, s, d)
            pass
        except nx.NetworkXNoPath, exc:
            pass
        if not src_dp:
            primaryPath = detourPaths = None
            pass
        else:
            # src has a dpath, so now make all other pnodes backtrack
            # to src. each node just grabs its predecessor's dpath,
            # and prepend itself to get its own dpath.
            detourPaths[s] = src_dp
            for i in xrange(1, len(primaryPath)-1):
                pnode = primaryPath[i]
                detourPaths[pnode] = [pnode] + detourPaths[primaryPath[i-1]]
                pass
            pass
        # restore the removed edges
        g.add_edges_from(savedEdges)
        return primaryPath, detourPaths

    # this is number of nodes in primary path. NOT the number of edges
    # or the sum of edge weights.
    primaryPathLen = len(primaryPath)

    if preferDownStreamPEdges:
        # save the edge weights
#        assert weighted
        origEdgeWeights = {}
        for _i in xrange(0, primaryPathLen - 1):
            _u = primaryPath[_i]
            _v = primaryPath[_i+1]
            origEdgeWeights[(_u, _v)] = g.edge[_u][_v]['weight']
            pass
        pass

    # to save the detour paths for each node along the primary
    # path. the node name is the key, and the path is the value. if a
    # node does not have any detour path, then we will not add it to
    # this dictionary.
    detourPaths = {}

    # for each node (except destination d) in the primaryPath, finds
    # its detour.
    for i in range(0, primaryPathLen - 1):
#        pdb.set_trace()
        # temporarily remove edge from g
        u = primaryPath[i]
        v = primaryPath[i+1]

        # see if i need to and can use my predecessor's detour
        # path. otherwise use my own.
        if everyOtherNodeUsePredecessor and ((i % 2) == 1):
            predecessor = primaryPath[i - 1]
            predecessorDetourPath = detourPaths.get(predecessor, None)
            if predecessorDetourPath:
                detourPaths[u] = [u] + predecessorDetourPath
                continue
            # if predecessor doesnt have a detour path, keep going as
            # usual so i use my own.
            pass

        savedEdgeData = copy.copy(g.edge[u][v])
        g.remove_edge(u, v)

        if preferDownStreamPEdges:
            # set the weight of all downstream primary edges to zero
            for _i in xrange(i+1, primaryPathLen - 1):
                _u = primaryPath[_i]
                _v = primaryPath[_i+1]
                g.edge[_u][_v]['weight'] = 0
                pass
            pass

        detourPath = None
        try:
            # get the detour path from u->d in the undirected graph g.
            detourPath = getDetourPath(g, u, d)
            pass
        except nx.NetworkXNoPath, exc:
            # no detourpath possible
            pass

        if detourPath:
            # XXX/TODO: there might be multiple equal-distance detour
            # paths, should pick one that results in smaller graph
            # size. genGraph7() is a possible test case. genGraph8()
            # also is a test case.
            #
            # another is in rocketfuel/6461/weights.intra (captured by
            # genGraph8):
            #
            # s,d="527","728"
            #
            # in general, try to reuse primary nodes and secondary
            # nodes.

            # to fix the above, we consider the middle of the
            # detourPath, ie except u and d,
            #
            # or equivalently, detourPath[1:-1].
            #
            # this portion consists of:
            #
            # [<btpnodes>] [<snodes0>] [<pnodes0> <snodes1>...]
            #
            #
            # <btpnodes> is a sequence of primary nodes in the
            # backtrack. <snodes0> is a sequence of secondary nodes.
            # <pnodes0> is sequence of primary nodes that are down
            # stream. and so on. each of these sequences might or
            # might not exist, but the important one for us is to look
            # for the start of <pnodes0>, i.e., where the detour path
            # merges into a down stream primary node. after this node,
            # the detour path might switch back and forth between
            # secondary nodes and primary nodes if they have equal
            # weights. however, to keep the graph small, we force the
            # detour path to use only the primary nodes once it has
            # merged into one down stream one.
            #
            #
            #      j-----k--l E     H
            #      |     |  |/\    /\
            # Src--A--B--C--D  F--G  I--Dst
            #                \/    \/
            #                 m     n
            #
            # for example, A\'s detour path might be:
            #
            # * <snodes0> of <j,k>, then <pnodes0> of <C,D>, then
            # might 1. switch to <snodes1> of <m>, or 2. continue
            # <pnodes0> with E.
            #
            # * <snodes0> of <j,k,l>, then <pnodes0> of <D>, then
            # might ... (simiar to above)
            #
            #       13
            # Src ------- B --- Dst
            #     \     /
            #     2\   /9
            #        A
            #
            # in the above weighted example, primary path is
            # Src-A-B-Dst. then:
            #
            # * Src's detour path is Src-B-Dst (no backtracking and no
            # secondary nodes)
            #
            # * A's detour path is Src-B-Dst (with backtracking but
            # also no secondary nodes).
            #
            # so our strategy will be quite simple:
            #
            # - find the 1st pnode that is downstream from this node.
            #
            # - then replace the rest of the detourPath with the
            # portion of primaryPath starting at pnode. XXX/we can do
            # this because we pnode is on the primary path, which we
            # chose to be shortest or one of the shortests.
            #
            # if we only consider A's detour, then j-k-C-D is better
            # than j-k-l-D. however, the strategy above won't be able
            # to detect that, ie, it doesnt select which detour path,
            # it only modifies the suffix of the one already selected.
            # 
            # XXX/note that, although we prefer j-k-C-D instead of
            # j-k-l-D when we consider only A\'s detour, if we
            # consider the bigger picture, taking into account C\'s
            # detour and also using the virtual nodes, then j-k-l-D is
            # better, because then C can just go to virtual node k
            # already created by A's detour, instead of having to
            # create another virtual k for C itself in addition for
            # virtual node k for A.

            found = False
            _i = 1
            for _i in xrange(1, len(detourPath) - 1):
                try:
                    idxInPrimaryPath = primaryPath.index(detourPath[_i])
                    if idxInPrimaryPath > i:
                        found = True
                        break
                    pass
                except ValueError:
                    # keep going
                    pass
                pass

            if found:
                tmp = detourPath[0:_i+1] + \
                      primaryPath[primaryPath.index(detourPath[_i])+1:]
                detourPath = tmp
                pass

            detourPaths[u] = detourPath
            pass

        if preferDownStreamPEdges:
            # restore downstream edge weights to their original
            for _i in xrange(i+1, primaryPathLen - 1):
                _u = primaryPath[_i]
                _v = primaryPath[_i+1]
                g.edge[_u][_v]['weight'] = origEdgeWeights[(_u, _v)]
                pass
            pass

        # restore the edge back into g
        g.add_edge(u, v, attr_dict=savedEdgeData)
        pass

    return primaryPath, detourPaths



def getCommonSuffixIndices(l1, l2):
    '''
    find the indices within l1 and l2 where their common suffices
    start.

    return a tuple (<index in l1>, <index2 in l2>). if <index in l1>
    is -1 (in which case <index in l2> is undefined), there is no
    common suffix.

    example: l1 = [1,2,3,4], l2 = [2,3,4] then will return (1, 0).
    '''

    # go through the lists backwards and compare their elements. keep
    # going when they are equal. stop when they differ.

    len1 = len(l1)
    len2 = len(l2)

    diffLen2Len1 = len2 - len1

    l1resultindex = -1

    for l1index in range(len1 - 1, -1, -1):
        l2index = l1index + diffLen2Len1

        if l2index < 0:
            break

        if l1[l1index] == l2[l2index]:
            l1resultindex = l1index
            continue
        else:
            break
        pass

    return l1resultindex, l1resultindex + diffLen2Len1

gcsi = getCommonSuffixIndices

def getDagWithVnodes(primaryPath, detourPaths,
                     returnDetourPathsWithVNodes=False):
    '''
    given the primaryPath and detourPaths, return an acyclic directed
    graph that uses "virtual" nodes to represent the backtrack.

    note that each non-primary node should have only one successor.
    '''

    s = primaryPath[0]
    d = primaryPath[-1]

    dg = nx.DiGraph()

    # NOTE!!! this is number of nodes in primary path. NOT the number
    # of edges or the sum of edge weights.
    primaryPathLen = len(primaryPath)

    # make dg contain the primaryPath
    for i in range(0, primaryPathLen - 1):
        dg.add_edge(primaryPath[i], primaryPath[i+1])
        pass

    virtualDetourPaths = {}

    # for each primary node (except d) starting at s, process its
    # detour path if any.
    for pnodeIdx in range(0, primaryPathLen - 1):
        pnode = primaryPath[pnodeIdx]
        detourPath = detourPaths.get(pnode, None)
        if not detourPath:
            # no detour path
            continue

        # it has a detour path

        # does the detour path (minus the starting node--which is
        # pnode--and the ending node--which should be the destination)
        # involve with backtracking?

        # all the node names (except the starting and ending nodes) on
        # the detour path of pnode will have names
        # <originalname>_<pnodename> where <originalname> is original
        # name of the detour node. note then that the name will be a
        # string. however, to keep the graph small, try to reuse other
        # nodes as much as possible.

        # for example, to handle graph3:
        # for each pnode's detour path:

        # 1. find the longest common suffix with the primary path.

        # 2. find the longest common suffix with the ALL of
        # predecessors' detour paths.

        # 3. get the longest of 1. and 2.

        # 4. use that longest suffix for OUR detour path's suffix. our
        # prefix that is not common with any other path, we will have
        # to create new virtual nodes.

        # the "pathSuffix" DOES include the final node d


        ##
        ## find the longest suffix among the primary path and the
        ## detour paths of all the predecessors
        ##

        # each element is a triple: (<index in our detour path>,
        # <index in the other path>, <the other path>)
        commonSuffices = []

        # first, get the common suffix with the primary path
        commonSuffices.append(
            getCommonSuffixIndices(detourPath, primaryPath) + (primaryPath,))

        # now get the common suffices with the detour paths of all the
        # predecessors. yes, do want to include 0.
        for i in range(0, pnodeIdx):
            predecessorNode = primaryPath[i]
            predecessorDetourPath = detourPaths.get(predecessorNode, None)

            if predecessorDetourPath:
                idx1, idx2 = getCommonSuffixIndices(
                    detourPath,
                    predecessorDetourPath)
                if idx1 > -1:
                    commonSuffices.append(
                        (idx1, idx2, virtualDetourPaths[predecessorNode]))
                    pass
                pass
            pass

        # now, find the best one, ie, the one where <index in our
        # detour path> is smallest.
        best = min(commonSuffices, key=lambda triple: triple[0])
        smallerIdx1, idx2, pathWithLongestCommonSuffix = best

        pathSuffix = pathWithLongestCommonSuffix[idx2:]

        #####
        #####

        # lastBacktrackingIdx is index within detourPath where
        # backtracking stops. if it is -1, then there is no
        # backtracking.

        lastBacktrackingIdx = -1
        for i, dnode in enumerate(detourPath[:-1]):
            try:
                idxInPrimaryPath = primaryPath.index(dnode)
                # a primary node
                if idxInPrimaryPath < pnodeIdx:
                    # dnode is upstream -> still backtracking
                    lastBacktrackingIdx = i
                    pass
                elif idxInPrimaryPath > pnodeIdx:
                    # dnode is downstream -> no longer
                    # backtracking. stop looking.
                    break
                pass
            except ValueError:
                # keep going
                continue
            pass

        detourPathLen = len(detourPath)
        if smallerIdx1 == -1:
            smallerIdx1 = detourPathLen
            pass
        else:
            # cap the backtracking index at smallerIdx1
            if lastBacktrackingIdx > smallerIdx1:
                lastBacktrackingIdx = smallerIdx1
                pass
            pass

        virtualDetourPath = []

        # start the with first part of detourPath up till JUST BEFORE
        # "smallerIdx1", at the last iteration, joining it to the
        # first part of pathSuffix.

        for i in range(0, smallerIdx1):
            u = detourPath[i]
            if i != 0:
                # should be virtual node if not the first one.
                u = '%s~%s' % (u, pnode)
                pass

            if (i + 1) == smallerIdx1:
                # this is the end of this 1st part, so we need to
                # point to the first node in the 2nd part, ie, the
                # pathSuffix.
                v = pathSuffix[0]
                if (i + 1) == lastBacktrackingIdx:
                    # if that first node in the pathSuffix is part of
                    # the backtracking portion, we need to make it a
                    # virtual node, too.
                    v = '%s~%s' % (v, pnode)
                    pass
                pass
            else:
                # not the end of the first part, so use virtual node.
                v = '%s~%s' % (detourPath[i+1], pnode)
                pass

            virtualDetourPath.append(u)
            dg.add_edge(u, v)
            pass

        # now use the pathSuffix.
        for i in range(0, len(pathSuffix) - 1):
            u = pathSuffix[i]

            if (i + smallerIdx1) == lastBacktrackingIdx:
                # same special case as in the 1st part: only to handle
                # the joining node.
                u = '%s~%s' % (u, pnode)
                pass

            virtualDetourPath.append(u)
            dg.add_edge(u, pathSuffix[i+1])
            pass

        # this should always be destination d
        assert pathSuffix[-1] == d
        virtualDetourPath.append(pathSuffix[-1])

        virtualDetourPaths[pnode] = virtualDetourPath

        pass

    if returnDetourPathsWithVNodes:
        return dg, virtualDetourPaths
    else:
        return dg

def dotStr2Graph(dotstr):
    tfile = os.tmpfile()
    tfile.write(dotstr)
    tfile.seek(0)

    g = nx.read_dot(tfile)

    tfile.close()

    return g












###
###
### this section has some test graphs and also has some unit testing
### code
###
###


class TestCase:
    def __init__(self, g, s, d, expectedResult):
        self.g = g
        self.s = s
        self.d = d
        self.expectedResult = expectedResult
        return

class ExpectedResult:
    def __init__(self, primaryPath, detourPaths, dagEdge, dagNode):
        self.primaryPath = primaryPath
        self.detourPaths = detourPaths
        self.dagEdge = dagEdge
        self.dagNode = dagNode
        return

def genGraph1():
    '''
    features of this graph:

    - a primary node (A) has multiple alternate successors: f is its
      own, g and j are to serve B and C.

    - D shares the detour path with C.

    - E has no detour path.
    

         g-----h--i
         | f      |
         |/\      |
    Src--A--B-----C--D--E--Dst
         |              |
         j--k--l--m--n--o

    '''

    s,d='Src','Dst'

    expectedPrimaryPath = [s, 'A', 'B', 'C', 'D', 'E', d]
    expectedDetourPaths = {'A': ['A', 'f', 'B', 'C', 'D', 'E', d], 'C': ['C', 'B', 'A', 'j', 'k', 'l', 'm', 'n', 'o', 'E', d], 'B': ['B', 'A', 'g', 'h', 'i', 'C', 'D', 'E', d], 'D': ['D', 'C', 'B', 'A', 'j', 'k', 'l', 'm', 'n', 'o', 'E', d]}

    expectedDagNode = {'A': {}, s: {}, 'C': {}, 'B': {}, 'E': {}, 'D': {}, 'f~A': {}, 'm~C': {}, 'o~C': {}, d: {}, 'j~C': {}, 'B~C': {}, 'C~D': {}, 'g~B': {}, 'i~B': {}, 'k~C': {}, 'l~C': {}, 'h~B': {}, 'n~C': {}, 'A~C': {}, 'A~B': {}}

    expectedDagEdge = {'A': {'f~A': {}, 'B': {}}, s: {'A': {}}, 'C': {'D': {}, 'B~C': {}}, 'B': {'C': {}, 'A~B': {}}, 'E': {d: {}}, 'D': {'C~D': {}, 'E': {}}, 'f~A': {'B': {}}, 'm~C': {'n~C': {}}, 'o~C': {'E': {}}, d: {}, 'j~C': {'k~C': {}}, 'B~C': {'A~C': {}}, 'C~D': {'B~C': {}}, 'g~B': {'h~B': {}}, 'i~B': {'C': {}}, 'k~C': {'l~C': {}}, 'l~C': {'m~C': {}}, 'h~B': {'i~B': {}}, 'n~C': {'o~C': {}}, 'A~C': {'j~C': {}}, 'A~B': {'g~B': {}}}

    dotstr = '''
    graph test {
      Src--A--B--C--D--E--Dst;
      A--f--B;
      A--g--h--i--C;
      A--j--k--l--m--n--o--E;
    }
    '''

    return dotStr2Graph(dotstr), s, d, \
           ExpectedResult(primaryPath=expectedPrimaryPath,
                          detourPaths=expectedDetourPaths,
                          dagNode=expectedDagNode,
                          dagEdge=expectedDagEdge)

def genGraph2():
    '''
    features:

    - no backtracking.

    - D has high in-degree (and also has no detour).


         h---i----j
         |        |
         |       e|
         |      /\|
    Src--A--B--C--D--Dst
            |     |
            f-----g
    '''

    s,d='Src','Dst'

    expectedPrimaryPath = [s, 'A', 'B', 'C', 'D', d]
    expectedDetourPaths = {'A': ['A', 'h', 'i', 'j', 'D', d], 'C': ['C', 'e', 'D', d], 'B': ['B', 'f', 'g', 'D', d]}

    expectedDagNode = {'A': {}, s: {}, 'C': {}, 'B': {}, 'D': {}, 'h~A': {}, d: {}, 'f~B': {}, 'e~C': {}, 'g~B': {}, 'i~A': {}, 'j~A': {}}
    expectedDagEdge = {'A': {'B': {}, 'h~A': {}}, s: {'A': {}}, 'C': {'e~C': {}, 'D': {}}, 'B': {'C': {}, 'f~B': {}}, 'D': {d: {}}, 'h~A': {'i~A': {}}, d: {}, 'f~B': {'g~B': {}}, 'e~C': {'D': {}}, 'g~B': {'D': {}}, 'i~A': {'j~A': {}}, 'j~A': {'D': {}}}


    dotstr = '''
    graph test {
      Src--A--B--C--D--Dst;
      C--e--D;
      B--f--g--D;
      A--h--i--j--D;
    }
    '''

    # good position to use for the nodes to draw with nx.draw
    pos = {'A': (60, 100), 'Src': (30, 100), 'C': (120, 100), 'B': (90, 100), 'e': (135, 115), 'D': (150, 100), 'g': (150, 85), 'f': (90, 85), 'i': (100, 130), 'h': (60, 130), 'Dst': (180, 100), 'j': (150, 130)}


    return dotStr2Graph(dotstr), s, d, \
           ExpectedResult(primaryPath=expectedPrimaryPath,
                          detourPaths=expectedDetourPaths,
                          dagNode=expectedDagNode,
                          dagEdge=expectedDagEdge)

def genGraph3():
    '''
    features:

    - Src\' detour path i-j-l-n-C and A\'s detour path k-j-l-n-C have
      common j-l-n-C. and A\s detour path and B\'s detour path m-l-n-C
      have common l-n-C.

    - C\'s detour path n-o-p-D doesnt have a common part with any
      other primary node.

    - D and E have no detour paths.

    - F, G, and H detour paths have common q-r-s-Dst.

    - Src (and A, B, and C) detour paths merge back into the primary
      path at D _forward_, so they only need to express their detour
      paths up to D.

    these facts should be exploited to keep the final graph/header
    small.

     i---j--l--n--o
     |   |  |  |  |
     |   k  m  |  p     q----r----s
     |   |  |  |  |     |         |
    Src--A--B--C--D--E--F--G--H--Dst

    '''

    s,d='Src','Dst'

    expectedPrimaryPath = [s, 'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', d]
    expectedDetourPaths = {'A': ['A', 'k', 'j', 'l', 'n', 'C', 'D', 'E', 'F', 'G', 'H', d], s: [s, 'i', 'j', 'l', 'n', 'C', 'D', 'E', 'F', 'G', 'H', d], 'C': ['C', 'n', 'o', 'p', 'D', 'E', 'F', 'G', 'H', d], 'B': ['B', 'm', 'l', 'n', 'C', 'D', 'E', 'F', 'G', 'H', d], 'G': ['G', 'F', 'q', 'r', 's', d], 'F': ['F', 'q', 'r', 's', d], 'H': ['H', 'G', 'F', 'q', 'r', 's', d]}

    expectedDagNode = {'m~B': {}, d: {}, 'n~Src': {}, 'G~H': {}, 'k~A': {}, 'q~F': {}, 'n~C': {}, 'A': {}, s: {}, 'C': {}, 'B': {}, 'E': {}, 'D': {}, 'G': {}, 'F': {}, 'H': {}, 'p~C': {}, 'l~Src': {}, 'F~G': {}, 'j~Src': {}, 'o~C': {}, 's~F': {}, 'i~Src': {}, 'r~F': {}}
    expectedDagEdge = {'m~B': {'l~Src': {}}, d: {}, 'n~Src': {'C': {}}, 'G~H': {'F~G': {}}, 'k~A': {'j~Src': {}}, 'q~F': {'r~F': {}}, 'n~C': {'o~C': {}}, 'A': {'B': {}, 'k~A': {}}, s: {'A': {}, 'i~Src': {}}, 'C': {'n~C': {}, 'D': {}}, 'B': {'m~B': {}, 'C': {}}, 'E': {'F': {}}, 'D': {'E': {}}, 'G': {'H': {}, 'F~G': {}}, 'F': {'q~F': {}, 'G': {}}, 'H': {'G~H': {}, d: {}}, 'p~C': {'D': {}}, 'l~Src': {'n~Src': {}}, 'F~G': {'q~F': {}}, 'j~Src': {'l~Src': {}}, 'o~C': {'p~C': {}}, 's~F': {d: {}}, 'i~Src': {'j~Src': {}}, 'r~F': {'s~F': {}}}

    dotstr = '''
    graph test {
      Src--A--B--C--D--E--F--G--H--Dst;
      Src--i--j--l--n--o--p;
      A--k--j;
      B--m--l;
      C--n;
      D--p--o;
      F--q--r--s--Dst;
    }
    '''

    return dotStr2Graph(dotstr), s, d, \
           ExpectedResult(primaryPath=expectedPrimaryPath,
                          detourPaths=expectedDetourPaths,
                          dagNode=expectedDagNode,
                          dagEdge=expectedDagEdge)

def genGraph4():
    '''
           B      E
          /\     /\
    Src--A  C---D  F--Dst
     |    \/     \/    |
     |     g      h    |
     |                 |
     i--j--k--l--m--n--o


    the backtrack from F has 4 equal-distance options, through E and
    B, or E and g, or h and B, or h and g.

    proly for all cases, but certainly for this case, we want the
    backtrack to go through E and B. at least to keep the graph small.



    NOTE: the nx shortest path algo seems to always pick h vs E when
    they are equal distance.

    '''

    s,d='Src','Dst'

    expectedPrimaryPath = [s, 'A', 'B', 'C', 'D', 'h', 'F', d]
    expectedDetourPaths = {'A': ['A', 'g', 'C', 'D', 'h', 'F', d], s: [s, 'i', 'j', 'k', 'l', 'm', 'n', 'o', d], 'C': ['C', 'B', 'A', s, 'i', 'j', 'k', 'l', 'm', 'n', 'o', d], 'B': ['B', 'A', 'g', 'C', 'D', 'h', 'F', d], 'D': ['D', 'E', 'F', d], 'F': ['F', 'h', 'D', 'C', 'B', 'A', s, 'i', 'j', 'k', 'l', 'm', 'n', 'o', d], 'h': ['h', 'D', 'E', 'F', d]}


    expectedDagNode = {'D~F': {}, d: {}, 'm~Src': {}, 'n~Src': {}, 'D~h': {}, 'g~A': {}, 'k~Src': {}, 'A~C': {}, 'A~B': {}, 'A': {}, s: {}, 'C': {}, 'B': {}, 'D': {}, 'F': {}, 'o~Src': {}, 'E~D': {}, 'C~F': {}, 'h~F': {}, 'l~Src': {}, 'j~Src': {}, 'h': {}, 'Src~C': {}, 'B~C': {}, 'i~Src': {}}

    expectedDagEdge = {'D~F': {'C~F': {}}, d: {}, 'm~Src': {'n~Src': {}}, 'n~Src': {'o~Src': {}}, 'D~h': {'E~D': {}}, 'g~A': {'C': {}}, 'k~Src': {'l~Src': {}}, 'A~C': {'Src~C': {}}, 'A~B': {'g~A': {}}, 'A': {'g~A': {}, 'B': {}}, s: {'A': {}, 'i~Src': {}}, 'C': {'D': {}, 'B~C': {}}, 'B': {'C': {}, 'A~B': {}}, 'D': {'h': {}, 'E~D': {}}, 'F': {'h~F': {}, d: {}}, 'o~Src': {d: {}}, 'E~D': {'F': {}}, 'C~F': {'B~C': {}}, 'h~F': {'D~F': {}}, 'l~Src': {'m~Src': {}}, 'j~Src': {'k~Src': {}}, 'h': {'D~h': {}, 'F': {}}, 'Src~C': {'i~Src': {}}, 'B~C': {'A~C': {}}, 'i~Src': {'j~Src': {}}}


    
    dotstr = '''
    graph test {
      Src--A--B--C--D--E--F--Dst;
      A--g--C;
      D--h--F;
      Src--i--j--k--l--m--n--o--Dst;
    }
    '''

    return dotStr2Graph(dotstr), s, d, \
           ExpectedResult(primaryPath=expectedPrimaryPath,
                          detourPaths=expectedDetourPaths,
                          dagNode=expectedDagNode,
                          dagEdge=expectedDagEdge)

def genGraph5():
    '''
    main features of this graph:

    - A, B, and C detour paths have common portions A-d-e-f. this fact
      should be exploited to keep the final graph/header small.

    Src--A--B--C--D--E--Dst
         |              |
         f--g--h--i-----j

    '''

    s,d='Src','Dst'

    expectedPrimaryPath = [s, 'A', 'B', 'C', 'D', 'E', d]
    expectedDetourPaths = {'A': ['A', 'f', 'g', 'h', 'i', 'j', d], 'C': ['C', 'B', 'A', 'f', 'g', 'h', 'i', 'j', d], 'B': ['B', 'A', 'f', 'g', 'h', 'i', 'j', d], 'E': ['E', 'D', 'C', 'B', 'A', 'f', 'g', 'h', 'i', 'j', d], 'D': ['D', 'C', 'B', 'A', 'f', 'g', 'h', 'i', 'j', d]}

    expectedDagNode = {'A': {}, s: {}, 'C': {}, 'B': {}, 'E': {}, 'D': {}, 'f~A': {}, 'B~C': {}, d: {}, 'i~A': {}, 'h~A': {}, 'C~D': {}, 'j~A': {}, 'g~A': {}, 'A~B': {}, 'D~E': {}}
    expectedDagEdge = {'A': {'B': {}, 'f~A': {}}, s: {'A': {}}, 'C': {'B~C': {}, 'D': {}}, 'B': {'C': {}, 'A~B': {}}, 'E': {'D~E': {}, d: {}}, 'D': {'C~D': {}, 'E': {}}, 'f~A': {'g~A': {}}, 'B~C': {'A~B': {}}, d: {}, 'i~A': {'j~A': {}}, 'h~A': {'i~A': {}}, 'C~D': {'B~C': {}}, 'j~A': {d: {}}, 'g~A': {'h~A': {}}, 'A~B': {'f~A': {}}, 'D~E': {'C~D': {}}}

    dotstr = '''
    graph test {
      Src--A--B--C--D--E--Dst;
      A--f--g--h--i--j--Dst;
    }
    '''

    return dotStr2Graph(dotstr), s, d, \
           ExpectedResult(primaryPath=expectedPrimaryPath,
                          detourPaths=expectedDetourPaths,
                          dagNode=expectedDagNode,
                          dagEdge=expectedDagEdge)

def genGraph6():
    '''
    features:

    - if A--B... is chosen as the primary path, the final graph will
      have to be bigger because the detour paths are longer than if
      D--E... is chosen as the primary path.


        A--B--C
       /       \
    Src         Dst
       \       /
        D--E--F
        |  |  |
        G--H--I

    '''
    
    dotstr = '''
    graph test {
      Src--A--B--C--Dst;
      Src--D--E--F--Dst;
      D--G--H--I--F;
      E--H;
    }
    '''

    return dotStr2Graph(dotstr), 'Src', 'Dst'

def genGraph7():
    '''
    this graph is the subgraph of the gnm_1024_10_1.txt graph. there
    was a bug when handling this graph with s,d="898","642"

    '''
    
    dotstr = """
    graph test {
      898--17--565--642;
      898--127--879--642;
      17--127;
      17--747--476--642;
    }
    """

    # this set of detour paths do not cause problems

    # gdp = {'898': ['898', '127', '879', '642'], '565': ['565', '17', '747', '476', '642'], '17': ['17', '127', '879', '642']}

    # this is the set of detour paths that causes problems.

    # bdp = {'898': ['898', '127', '879', '642'], '565': ['565', '17', '127', '879', '642'], '17': ['17', '747', '476', '642']}

    # this difference is that 565 and 17 swapped their detour path
    # suffices.


    return dotStr2Graph(dotstr), '898', '642'

def genGraph8():
    '''

    found when debuggin in rocketfuel/6461/weights.intra:
    s,d="527","728"

    A--B--C--D is picked as the primary path.

    then Src\'s detour path goes throug e--f--B, and then it picks h
    instead of C. we want it to pick C because that will help keep the
    graph small.

    similar for A\'s detour path: after going through g--B, we want it
    to pick C instead of h also for reason of graph size.

    these detour paths are already picked by getDg() before our
    "prefer path with longest common suffix" in getDagWithVnodes()
    code.


       e--f   C
      /    \ /\
    Src--A--B  D--Dst
          \/ \/
           g  h
    '''

    s,d='Src','Dst'
    
    dotstr = """
    graph test {
      Src--A--B--C--D--Dst;
      Src--e--f--B;
      A--g--B;
      B--h--D;
    }
    """

    return dotStr2Graph(dotstr), s, d


unitTests = [
    genGraph1,
    genGraph2,
    genGraph3,
    genGraph4,
    genGraph5,
    ]

def runtests(tests=unitTests):
    failedTests = []
    for test in tests:
        testfunc = test
        g,s,d,er = testfunc()

        pp,dp = getDg(g,s,d)
        dg = getDagWithVnodes(pp, dp)

        # make sure things are as expected
        if pp != er.primaryPath or \
           dp != er.detourPaths or \
           dg.node != er.dagNode or \
           dg.edge != er.dagEdge:
            failedTests.append(test)
            pass
        pass

    print 'number of        tests: [%d]' % len(tests)
    print 'number of failed tests: [%d]' % len(failedTests)
    if failedTests:
        print 'the failed tests are:'
        for failedTest in failedTests:
            print failedTest.__name__
            pass
        pass

    return


'''
XXX: problems:

----------------

1. FIXED in getDg() by preferring the detour path to merge back into
the primaryPath if equal distance.

in rocketfuel/6461/weights.intra:

s,d="527","728"

and in rocketfuel/1239/weights.intra:

s,d="4108","4033"



'''
