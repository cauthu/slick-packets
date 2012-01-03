
# UNSOLVED ISSUES:
#
# 1. in some cases, the computeEdgeCosts() function when
# "resolveCycle" is true, removes an edge that completely cuts off the
# path to a node.
#
# use "weights.intra": s,d=4024,6752
#
#

# deprecated
#versionDate = 'Wed Dec  2 11:59:13 CST 2009'

Revision = '$Revision: 534 $'
Id = '$Id$'

import sys

# so that we get a dev version of nx, which doesnt have the problem
# where draw_graphviz errors on edges that contain non-string
# attributes, eg, the algorithms require edge weights to be numbers.
sys.path = ['/home/me/.local/lib/python2.6/site-packages'] + sys.path

try:
    import matplotlib.pyplot as plt
    pass
except:
    print 'error importing matplotlib.pyplot so cannot plot graphs'
    pass

import networkx as nx # requires networkx version >= 1.0rc1

import random
import math, re
import cPickle

#import pdb

draw = nx.draw
drawg = nx.draw_graphviz

NaN = float('nan')

def genCDF(sortedList, toFilename=None,
           bucketsize=None):
    retval = None
    length = len(sortedList)
    if toFilename:
        fil = open(toFilename, 'w')
        pass
    else:
        retval = []
        pass
    ###

    if bucketsize:
        # this should be able to handle negative values as well.  (-0
        # == 0) is True

        # each bucket is represented by its upper bound.  for example,
        # if bucketsize is 10, then buckets are (-10, 0], (0, 10],
        # (10, 20], ... and the representatives of the groups are 0,
        # 10, and 20 respectively.

        # bucketUpperBound -> count
        bucketCountDict = {}

        # this loop is not exploiting the fact that the sortedList
        # list is already sorted, but this is simpler.
        for val in sortedList:
            # which bucket should this go into?
            bucketUpperBound = math.ceil((float(val)) / bucketsize) * bucketsize
            if bucketUpperBound in bucketCountDict:
                # bucket exists already -> increment its count
                bucketCountDict[bucketUpperBound] += 1
                pass
            else:
                # create the bucket
                bucketCountDict[bucketUpperBound] = 1
                pass
            pass

        print '***** buckets and their counts: ', bucketCountDict

        bucketUpperBounds = bucketCountDict.keys()
        bucketUpperBounds.sort()

        cumulativeCount = 0
        for bucketUpperBound in bucketUpperBounds:
            cumulativeCount += bucketCountDict[bucketUpperBound]
            fraction = float(cumulativeCount) / len(sortedList)
            if toFilename:
                fil.write('%f\t%f\n' % (bucketUpperBound, fraction))
                pass
            else:
                retval.append((bucketUpperBound, fraction))
                pass
            pass
        pass
    else:
        for idx, val in enumerate(sortedList):
            if toFilename:
                fil.write('%f\t%f\n' % (val, (idx + 1.0) / length))
                pass
            else:
                retval.append((val, (idx + 1.0) / length))
                pass
            pass
        pass
    ###

    if toFilename:
        fil.close()
        pass
    return retval

# if weighted is true, then the returned value is the max path LENGTH
# (not hop count) between all node pairs
def diameter(g, weighted):
    if not weighted:
        return nx.diameter(g)
    else:
        ret = nx.all_pairs_dijkstra_path_length(g)
        return max(map(lambda perSourceDists: max(perSourceDists.values()), ret.values()))
        pass

def unpickleStuff(filename, protocol=2):
    '''
    simply a wrapper to handle the file stuff as well
    '''
    if protocol >= 1:
        f = open(filename, 'rb')
        pass
    else:
        f = open(filename, 'r')
        pass
    retval = cPickle.load(f)
    f.close()
    return retval

def pickleStuff(filename, obj, protocol=2):
    '''
    simply a wrapper to handle the file stuff as well
    '''
    f = open(filename, 'w')
    cPickle.dump(obj, f, protocol)
    f.close()
    return


def textToG(filename, shortenNames=True, genLocalLinkIDs=True,
            useInt=True, ignoreWeights=True,
            onlyTheseNodes=None):
    '''
    each line represents a link, thus must have at least 2 parts (for
    node names), separated by white space.

    only the node names are used. any other field is currently
    ignored.

    -----------------
    "genLocalLinkIDs": True to have each node associate a local link
    ID to each of its link (for example, maybe like the physical
    interface ID). these wil be GENERATED (not read from the file)
    sequentially starting from 0, with the first encountered neighbor
    having ID 0.

    the processing considers each line bidirectional, ie, it will
    process both nodes of the line. for example:

    A C
    A B
    B E
    B A
    A D
    ...

    1st line: A uses local link ID 0 for C, and C uses local link ID 0
    for A.

    2nd line: A uses local link ID 1 for B, and B uses local link ID 0
    for A.

    3rd line: B uses local link ID 1 for E, and E uses local link ID 0
    for B.

    4th line: effectively skipped because A and B already have local
    link IDs for each other.

    5th line: A uses local link ID 2 for D, and D uses local link ID 0
    for A.

    because in graph g, two neighbors share the same "data" dictionary
    (ie, g[A][B] is same object as g[B][A]), we will return the local
    link IDs dictionary separate from the graph g.

    the dictionary will have each node as a key, and the value will be
    a dictionary with each of its neighbors as key, and the value will
    be the integer ID.

    for example, for the graph above, the result will be like:

    {
      A: {D: 2, C: 0, B: 1},
      D: {A: 0},
      B: {A: 0, E: 1},
      E: {B: 0},
      C: {A: 0},
      ...
    }


    '''

    if shortenNames:
        # use this to make sure we're not losing info like this:
        # full name -> short: abcd1234 -> 1234
        # full name -> short: DFGH1234 -> 1234
        #
        # when something like that is detected, we should fail.

        shortToFullNames = {}
        pass

    # this will be returned
    retLocalLinkIDs = {}

    if (genLocalLinkIDs):

        # this dictionary is to keep track, for each node, the local
        # link ID that its next found neighbor should use. when that
        # is used, the value in the dictionary should be incremented.

        # if there is no such value, then it's assumed to be 0 and
        # after used should be incremented to 1.
        
        # this is only for tmp processing

        linkIdsToUse = {}
        pass

    pattern = re.compile('[^0-9]*([0-9]+).*')
    fil = open(filename, 'r')
    g = nx.Graph()
    for line in fil:
        parts = line.split()

        for partIdx in (0, 1):
            if shortenNames:
                fullName = parts[partIdx]
                assert (not (fullName is None))
                shortName = re.match(pattern, fullName).group(1)
                assert (not (shortName is None))

                curFullName = shortToFullNames.get(shortName, None)

                assert (curFullName is None) or (curFullName == fullName)

                if useInt:
                    parts[partIdx] = int(shortName)
                    pass
                else:
                    parts[partIdx] = shortName
                    pass

                shortToFullNames[shortName] = fullName
                pass
            pass

        u = parts[0]
        v = parts[1]

        if onlyTheseNodes != None:
            if (not u in onlyTheseNodes) or (not v in onlyTheseNodes):
                continue
            pass

        if ignoreWeights:
            g.add_edge(u, v)
            pass
        else:
            assert len(parts) == 3
            g.add_edge(u, v, weight=float(parts[2]))
            pass

        if (genLocalLinkIDs):
            # handle u-v
            linkIdToUse = linkIdsToUse.get(u, None)
            if linkIdToUse is None:
                # first time we've seen "u"
                linkIdToUse = 0
                retLocalLinkIDs[u] = {}
                pass

            if not retLocalLinkIDs[u].has_key(v):
                retLocalLinkIDs[u][v] = linkIdToUse
                linkIdsToUse[u] = linkIdToUse + 1
                pass

            # handle v-u
            linkIdToUse = linkIdsToUse.get(v, None)
            if linkIdToUse is None:
                # first time we've seen "v"
                linkIdToUse = 0
                retLocalLinkIDs[v] = {}
                pass

            if not retLocalLinkIDs[v].has_key(u):
                retLocalLinkIDs[v][u] = linkIdToUse
                linkIdsToUse[v] = linkIdToUse + 1
                pass

            pass
        pass # end for loop
    fil.close()
    return g, retLocalLinkIDs

######################################################################

def dgToDag(dg, s='Src'):
    '''
    ie, remove cycles, by removing backedges.
    '''

    def _helper(u, predecessors):
        predecessors = predecessors + [u]
        neighbors = dg.neighbors(u)
        for v in neighbors:
            if v in predecessors:
                dg.remove_edge(u, v)
                print 'removed back edge %s->%s' % (u, v)
                pass
            else:
                _helper(v, predecessors)
                pass
            pass
        return

    _helper(s, [])
    return dg


def addDistDAttr(dag, d='Dst'):
    dag.reverse(copy=False)
    distD = nx.single_source_shortest_path_length(dag, d)
    for v in dag.nodes():
        dag.add_node(v, distD=distD.get(v, NaN))
        pass
    dag.reverse(copy=False)
    return

######################################################################

def getDAG(orig_g, s, d, reliabilityWeight=1, distDWeight=0,
           preferSiblingOrItsSuccessor=False,
           preferHigherIndegree=True):
    g = orig_g.copy()
    trim(g, s, d)
    intermediateDg = create_dg(g, s, d)

    # hmm, can addDistDAttr handle cycles?
    addDistDAttr(intermediateDg, d)

    computeEdgeCosts(intermediateDg, s, d,
                     reliabilityWeight, distDWeight,
                     resolveCycle=True)
    finalDAG = getFinalDG(intermediateDg, s, d,
                          preferSiblingOrItsSuccessor,
                          preferHigherIndegree)
    return finalDAG

######################################################################

def getNodeColorList(g, s='Src', d='Dst',
                     primaryPath=None, otherColor='blue'):
    '''
    s will be green, d will be red, and other nodes will be
    "otherColor".

    s and d nodes must exist.
    '''
    nodes = g.nodes()
    colorlist = [otherColor] * len(nodes)
    colorlist[nodes.index(s)] = 'green'
    colorlist[nodes.index(d)] = 'red'
    if primaryPath:
        for u in primaryPath[1 : len(primaryPath)-1]:
            colorlist[nodes.index(u)] = 'yellow'
            pass
        pass
    return colorlist

gncl = getNodeColorList

######################################################################

def renameSrcDst(orig_g, s, d, layout=None):
    '''
    currently only undirected "g" are supported.
    
    change the nodes s and d into nodes "Src" and "Dst". of course
    edges are preserved.

    TODO: make sure that attributes of nodes and their edges are
    preserved, too.

    return a new g and its updated (if "layout" was specified) layout.
    '''

    g = orig_g.copy()
    if layout:
        import copy
        g_layout = copy.copy(layout)
        pass
    else:
        g_layout = nx.graphviz_layout(g)
        pass
    for oldlabel, newlabel in ((s, 'Src'),
                               (d, 'Dst')):
        for neighbor in g.neighbors(oldlabel):
            g.add_edge(newlabel, neighbor)
            pass
        g.remove_node(oldlabel)
        g_layout[newlabel]=g_layout[oldlabel]
        del g_layout[oldlabel]
        pass
    return g, g_layout

rsd = renameSrcDst

################################################################

debugGetFinalDG = False
def getFinalDG(dg, s='Src', d='Dst',
               preferSiblingOrItsSuccessor=True,
               preferHigherIndegree=False):

    '''
    Sun Nov 15 15:41:11 CST 2009: make nodes that are predecessors of
    the destination d use only one edge to d itself, even if there are
    more edges available. no point in going around.

    for example: with this graph, A has three possible links to Dst,
    but we will just use one link: A->Dst.

        B
       /\
      /  \
     /    \
    A ---- Dst
     \    /
      \  /
       \/
        C


    Sun Nov 15 15:41:11 CST 2009: for the algorithm to pick
    successors, when two successors have the same edge weights, to
    keep the graph size small, should either pick one that is our
    sibling or a successor of our sibling (use
    "preferSiblingOrItsSuccessor"), or on that has higher indegree
    (use "preferHigherIndegree")

    for illustration, run on the "typeE" graph generated by
    "gen_graph_typeE". (with that graph, using either preference will
    result in a smaller graph than using neither, ie, simply comparing
    edge weights.)

    '''

    def _debughelper(num_indent, s):
        if debugGetFinalDG:
            print num_indent*' ' + s
            pass
        return
    ########

    def _helper(u, num_indent=0, sibling=None):
        '''
        depth-first. for each node, pick (at most) 2 out-edges with
        the least costs, add them to finalDG, and recursively follow
        them.

        '''

        if u == d:
            return

        _debughelper(num_indent, 'u is [%s]' % u)

        successors = dg.successors(u)

        _debughelper(num_indent, 'successors are [%s]' % str(successors))

        if d in successors:
            finalDG.add_edge(u, d)
            return

        # filter out edges with infinite costs (ie, deadends)
        successors = filter(
            lambda n: not math.isnan(dg[u][n]['weight']),
            successors)

        ###
        ### sort the successors
        ###

        def cmpSuccessors(s1, s2):
            # first compare their edge weights.
            result = cmp(dg[u][s1]['weight'], dg[u][s2]['weight'])
            if result == 0:
                ## tie

                if preferSiblingOrItsSuccessor:
                    if sibling != None:
                        # then prefer the successor that is
                        # either our sibling itself ...
                        if s1 == sibling:
                            return -1
                        if s2 == sibling:
                            return +1
                        # ... or also a successor of our sibling.
                        if (dg.has_successor(sibling, s1)) and \
                               (dg.has_successor(sibling, s2)):
                            # both are successors of our sibling -> still tie
                            return 0
                        if (dg.has_successor(sibling, s1)):
                            return -1
                        if (dg.has_successor(sibling, s2)):
                            return +1
                        pass
                    pass
                elif preferHigherIndegree:
                    # higher degree is preferred, thus "smaller"
                    return -1 * cmp(dg.in_degree(s1),
                                    dg.in_degree(s2))
                pass

            return result
        #####
        
        successors.sort(cmp=cmpSuccessors)

        _debughelper(num_indent, 'filtered/sorted successors are [%s]' % (str(successors)))


        ###
        ### successors are sorted... now follow them
        ###

        # get at most the 2 successors at the front

        if len(successors) == 1:
            v = successors[0]
            finalDG.add_edge(u, v)
            _helper(v, num_indent + 2)
            pass
        elif len(successors) > 1:
            v1 = successors[0]
            v2 = successors[1]

            finalDG.add_edge(u, v1)
            _helper(v1, num_indent + 2, v2)

            finalDG.add_edge(u, v2)
            _helper(v2, num_indent + 2, v1)
            pass

        return
    ######################


    finalDG = nx.DiGraph()
    _helper(s, 0)
    return finalDG

gfdg = getFinalDG

######################################################################
debugComputeedgecosts = False
def computeEdgeCosts(dg, s='Src', d='Dst',
                     reliabilityWeight=1,
                     distDWeight=1,
                     resolveCycle=False):
    '''

    "dg" must be an a-cyclic graph with edges generally pointing from
    "s" towards "d". "downstream" means "towards d".

    if "resolveCycle" is False, then will exit when cycle detected. if
    True, then when cycle is detected, the back-edge will be removed
    from dg, and the operation continues.

    compute the costs of "useful" edges. useful means edges
    followable/reachable from s.

    will use dg.add_edge(..., weight=...) to update dg.

    at high level, the cost C of an edge, is the smallest (ie, best)
    number of downstream nodes that have outdegrees <= 1.

    intuitively, if this edge is taken, then all possible paths
    (towards d) that follow, will encounter at least W number of nodes
    that have outdegrees <= 1.

    edges incident on d will have costs of zero.

    the nodes/edges\'s distances from d are NOT incorporated in this
    version.


    TODO/XXX: to increase reliability, we want to handle double-edges
    between two nodes, with the assumption that such double-edges are
    present only if the two nodes are equi-distant from s and d.

    '''

    def _debughelper(num_indent, s):
        if debugComputeedgecosts:
            print num_indent*' ' + s
            pass
        return

    # cost of each edge takes the value of its out-node.
    #
    # cost of each node V is:
    # -> 0 if V is destination d.
    # -> "min cost of all out-edges" if outdegree(V) > 1.
    # -> "1 + min cost of all out-edges" if outdegree(V) <= 1.
    #
    # "predecessors": the list of nodes we went through to get here to u.
    #
    # this is to detect cycle: first: we do NOT check for ourselves in
    # the list. we assume our parent caller has ensured no cycle
    # before calling us. second: we check each of our neighbors to
    # make sure they dont cause a cycle before following/calling
    # down to them.
    #
    # raise exception on cycle if resolveCycle=False. otherwise, if
    # resolveCycle=True, then return value will be as if there was no
    # cycle.

    def _helper(u, predecessors, num_indent=0):
        _debughelper(num_indent, 'u is [%s]' % u)

        # not detecting cycle here. do it when looking at neighbors.

        # use "==", dont use "is"
        if u == d:
            return 0
        elif u in nodeCosts:
            _debughelper(
                num_indent,
                'u already computed -> returning [%s]' % nodeCosts[u])
            return nodeCosts[u]

        # assume that except for d, no other node can have out degree
        # of zero.
        #
        # if node has outdegree of zero, its cost should be large,
        # ideally infinity.

        runningMinCost = NaN
        predecessors = predecessors + [u]
        neighbors = dg.neighbors(u)

        for v in neighbors:
            _debughelper(num_indent, 'out neighbor [%s]' % v)

            # detect and handle cycle.
            if v in predecessors:
                #print 'cycle! predecessors [%s]' % predecessors
                if resolveCycle:
                    dg.remove_edge(u, v)
                    # continue to next neighbor
                    continue
                else:
                    raise Exception('cycle! predecessors [%s]' % \
                                    predecessors)
                pass

            # neighbor v itself doesnt form a cycle.
            vCost = _helper(v, predecessors, num_indent+2)

            _debughelper(num_indent,
                         'has computed vCost of [%s]' % vCost)
            # update cost of edge
            dg[u][v]['weight']=vCost

            if not math.isnan(vCost) and \
                   (math.isnan(runningMinCost) or vCost < runningMinCost):
                runningMinCost = vCost
                pass
            pass

        if dg.out_degree(u) > 1:
            nodeCosts[u] = (reliabilityWeight * runningMinCost) + \
                           (distDWeight * dg.node[u]['distD'])
            pass
        else:
            # "nan" + any number = "nan"
            nodeCosts[u] = (reliabilityWeight * (runningMinCost + 1)) + \
                           (distDWeight * dg.node[u]['distD'])
            pass
        _debughelper(
            num_indent,
            'returning nodeCosts[%s] of [%s]' % (u, nodeCosts[u]))
        return nodeCosts[u]

    ##############

    nodeCosts = {d:0}
    # yes, the "predecessors" arg should be empty list [] because
    # source s doesnt have predecessors.
    _helper(s, [], 0)
    return

cec=computeEdgeCosts


###############################################################

def toggleEdgeWeightType(g):
    '''
    not necessary if using latest (dev) networkx version.

    workaround for bug in networkx, where edge weights need to be
    integer for the paths algorithms to work, but
    draw_graphviz/agraph.py\'s bug requires attributes to be str.
    '''
    for u, v in g.edges():
        edgedatadict = g.get_edge_data(u, v)
        W = edgedatadict.get('weight', None)
        if isinstance(W, str):
            #g.add_edge(u, v, weight=int(W))
            g[u][v]['weight']=int(W)
            pass
        elif isinstance(W, int):
            #g.add_edge(u, v, weight=str(W))
            g[u][v]['weight']=str(W)
            pass
        pass
    return


# given an undirected graph, source s, and destination d, iteratively
# trim all "non-transit nodes", ie, nodes that have degree <= 1. the
# final graph should contain nodes (except s and d) with degrees >= 2.

# this is a good type of graph to test the trim alg
# g = nx.generators.random_graphs.random_powerlaw_tree(100, 2.5)
#
# g = nx.generators.random_graphs.powerlaw_cluster_graph(40, 3, .5)


def trim(g, s='Src', d='Dst'):
    visited = set([s, d])
    while len(visited) < g.number_of_nodes():
        for n in g.nodes():
            if not n in visited: # and (not n is s) and (not n is d)
                if g.degree(n) <= 1:
                    # not adding n to visited because we will want to
                    # remove it anyway.
                    #
                    # we want to remove n. as a result of that, we also
                    # want to remove any neighbor of n that has degree <=
                    # 2 (because after n is removed, that neighbor will
                    # have degree <= 1). but to keep it simple, dont
                    # remove those neighbors now. simply mark them as
                    # "unvisited" and they will be visited again.
                    #
                    # also be careful to not remove s and d from "visited"
                    for neighbor in g.neighbors(n):
                        if (neighbor in visited) and (not neighbor == s) and \
                           (not neighbor == d):
                            visited.remove(neighbor)
                            pass
                        pass
                    # now delte n from g
                    # g.delete_node(n)
                    g.remove_node(n)
                    pass
                else:
                    visited.add(n)
                    pass
                pass
            pass
        pass

    return



debug_create_dg = False
def create_dg(g, s='Src', d='Dst'):
    '''
    create dg from g, s, d. the resulting dg\'s edges have attribute
    weight = 0.

    there might be cycles!
    '''

    def debug(s):
        if debug_create_dg:
            print s
            pass
        return

    # if v2 is closer to s than v1, wont do anything.
    def myadd_edge(dg, v1, v2):
        if distS[v1] < distS[v2]:
            debug( 'create_dg: distS[%s] < distS[%s]' % (v1, v2))
            if distD[v1] >= distD[v2]:
                debug( 'create_dg:   distD[%s] >= distD[%s]:  add %s->%s' %\
                       (v1, v2, v1, v2))
                dg.add_edge(v1, v2)
                pass
            else:
                # XXXXXXX/ need to figure out: v1 is closer to both S and D.
                debug( 'create_dg:   distD[%s] < distD[%s]' % \
                       (v1, v2))

                if distS[v1] > distD[v1]:
                    #   +-+-----+-----+
                    #  v2 v1    d     s
                    dg.add_edge(v2, v1)
                    debug('create_dg:     distS[%s] > distD[%s]:  add %s->%s'%\
                          (v1, v1, v2, v1))
                    pass
                else:
                    #   +-+-----+-----+
                    #  v2 v1    s     d
                    dg.add_edge(v1, v2)
                    debug('create_dg:     distS[%s] <=distD[%s]:  add %s->%s'%\
                          (v1, v1, v1, v2))
                    pass
                pass
            pass
        else:
            debug( 'create_dg: distS[%s] > distS[%s]. do nothing.' % (v1, v2))
            pass
        return

    #############################
        
    # this returns dictionary: node->distance
    distS = nx.single_source_shortest_path_length(g, s)
    distD = nx.single_source_shortest_path_length(g, d)

    # create a directed graph out of g's nodes
    dg = nx.DiGraph()
    dg.add_nodes_from(g.nodes())

    # now go through g's edges and turn them into directed edges in dg.
    for v1, v2 in g.edges():
        debug( 'create_dg: -------------------------------')
        debug( 'create_dg: handling undirected edge: %s %s' % (v1, v2))
        
        ####### always point away from s and towards d
        if (v1 == s) or (v2 == d):
            dg.add_edge(v1, v2)
            continue
        elif (v2 == s) or (v1 == d):
            dg.add_edge(v2, v1)
            continue

        ####### special case
        if distS[v1] == distS[v2] and distD[v1] == distD[v2]:
            debug( 'create_dg: special case.')
            # yes, add both edges!
            dg.add_edge(v1, v2)
            dg.add_edge(v2, v1)
            continue

        #######

        # XXX/not well designed

        if distS[v1] == distS[v2]:
            debug('create_dg: distS[%s] == distS[%s].' % (v1, v2))
            if distD[v1] < distD[v2]:
                debug('create_dg:   distD[%s] < distD[%s]: %s->%s' %\
                      (v1, v2, v2, v1))
                dg.add_edge(v2, v1)
                pass
            else:
                # this can only mean distD[v1] > distD[v2], because
                # the == case would have been handled by the special
                # case near top of loop.
                debug('create_dg:   distD[%s] > distD[%s]: %s->%s' %\
                      (v1, v2, v1, v2))
                dg.add_edge(v1, v2)
                pass
            pass
        else:
            # do mean to call twice with the 2 nodes reversed
            myadd_edge(dg, v1, v2)
            myadd_edge(dg, v2, v1)
            pass
        pass

    return dg




# s should be 0
# d should be 19
def gen_graph_typeC():

    # about 22 nodes

    g = nx.Graph()
    g.add_nodes_from(range(0, 23))

    # create the edges

    # create the thick "arch"

    for n in range(1, 19):
        if (n % 2) == 1:
            g.add_edge(n, n + 2)
            g.add_edge(n, n + 3)
            pass
        else:
            g.add_edge(n, n + 1)
            g.add_edge(n, n + 2)
            pass
        pass

    g.add_edge(1, 2)
    g.add_edge(2, 22)

    g.add_edge(0, 1)
    g.add_edge(0, 2)
    g.add_edge(0, 22)

    g.add_edge(17, 19)
    g.add_edge(18, 19)

    g.add_edge(19, 20)
    g.add_edge(20, 21)
    g.add_edge(21, 22)

    return g, 0, 19


def gen_graph_typeC2():
    # s should be "S"
    # d should be "D"

    numericS = 0
    numericD = 19
    realS = "S"
    realD = "D"

    def _add_edge(g, v1, v2):
        if v1 == numericS:
            v1 = realS
            pass
        elif v1 == numericD:
            v1 = realD
            pass

        if v2 == numericS:
            v2 = realS
            pass
        elif v2 == numericD:
            v2 = realD
            pass

        g.add_edge(v1, v2)
        return

    # about 22 nodes
    nodes = range(0, 23)
    nodes.remove(numericS)
    nodes.remove(numericD)
    nodes.append(realS)
    nodes.append(realD)

    g = nx.Graph()
    g.add_nodes_from(nodes)

    # create the edges

    # create the thick "arch"

    for n in range(1, 19):
        if (n % 2) == 1:
            _add_edge(g, n, n + 2)
            _add_edge(g, n, n + 3)
            pass
        else:
            _add_edge(g, n, n + 1)
            _add_edge(g, n, n + 2)
            pass
        pass

    _add_edge(g, 1, 2)
    _add_edge(g, 2, 22)

    _add_edge(g, 0, 1)
    _add_edge(g, 0, 2)
    _add_edge(g, 0, 22)

    _add_edge(g, 17, 19)
    _add_edge(g, 18, 19)

    _add_edge(g, 19, 20)
    _add_edge(g, 20, 21)
    _add_edge(g, 21, 22)

    return g, realS, realD


def gen_graph_typeE():

    g = nx.Graph()

    g.add_edge(1, 2)
    g.add_edge(1, 3)

    ###
    
    g.add_edge(2, 4)
    g.add_edge(2, 5)

    g.add_edge(3, 5)
    g.add_edge(3, 6)

    ###

    g.add_edge(4, 7)
    g.add_edge(4, 8)

    g.add_edge(5, 8)
    g.add_edge(5, 9)

    g.add_edge(6, 9)
    g.add_edge(6, 10)

    ###

    g.add_edge(7, 8)
    g.add_edge(10, 9)


    g.add_edge(7, 13)
    g.add_edge(8, 13)
    g.add_edge(9, 13)
    g.add_edge(10, 13)

    g.add_edge(2, 8)
    g.add_edge(3, 9)


    return g, 1, 13

