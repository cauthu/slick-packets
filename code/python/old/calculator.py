import cPickle
import networkx as nx
import os
import sys
import struct

Id = '$Id$'
Revision = '$Revision$'


def calculateForDAG(g, shortestPath, failureDetectionTime,
                    routerNotifiesSource,
                    shortestPathLengthFunction):
    # NOTE: this will not consider failing the source's outgoing link
    # because the stretch will be the same in all cases, for all
    # schemes: as soon as the source detects the failure, the stretch
    # will be 1.
    
    # "shortestPath" should be that returned by networkx's path
    # algorithms, as in [0] is the source, [-1] is the destination.

    # "routerNotifiesSource": True to have the router adjacent notify
    # the source of failure. False to have it only mark the packet on
    # its way to the destination, which then notifies the source,
    # which takes longer for source to be notified.

    s = shortestPath[0]
    d = shortestPath[-1]
    shortestPathWithNoFailure = shortestPath

    results = []

    # iteratively fail each link along the shortest path
    for i in xrange(1, len(shortestPath) - 1):
        # "fail node 1" is closer to the source than is fail node 2
        fn1 = shortestPath[i]
        fn2 = shortestPath[i+1]

        # now find out when the source gets the news of the link
        # failure. assume zero processing/congestion/etc delay at
        # nodes, ie, only link latencies (distance) determine how fast
        # the update travel.

        savedEdgeAttr = g[fn1][fn2].copy()
        g.remove_edge(fn1, fn2)

        shortestLengthWithFailure = None
        try:
            shortestLengthWithFailure = shortestPathLengthFunction(g, s, d)
            pass
        except nx.exception.NetworkXError:
            pass

        if not shortestLengthWithFailure:
            # restore edge
            g.add_edge(fn1, fn2, attr_dict=savedEdgeAttr)
            continue

        distFromSToFn1 = shortestPathLengthFunction(g, s, fn1)
        distFromFn1ToD = shortestPathLengthFunction(g, fn1, d)
        takenPathLen = distFromSToFn1 + distFromFn1ToD

        timeAfterFailure2Stretch = []

        # this stretch is when failure is detected
        stretch = float(takenPathLen)/shortestLengthWithFailure
        timeAfterFailure2Stretch.append((failureDetectionTime, stretch))
        if stretch != 1:
            # after the source receives the news, the stretch is 1
            if routerNotifiesSource:
                # we assume bidirectional, so from s to fn1 is same as
                # from fn1 to s (because no link failure between s and
                # fn1)
                sourceUpdatedTime = failureDetectionTime + distFromSToFn1
                pass
            else:
                sourceUpdatedTime = failureDetectionTime + distFromFn1ToD + \
                                    shortestPathLengthFunction(g, d, s)
                pass
            timeAfterFailure2Stretch.append((sourceUpdatedTime, 1))
            pass

        results.append(timeAfterFailure2Stretch)
        # restore edge
        g.add_edge(fn1, fn2, attr_dict=savedEdgeAttr)
        pass

    return results

def calculateForSafeGuard(g, shortestPath, failureDetectionTime,
                          shortestPathLengthFunction):
    # NOTE: this will not consider failing the source's outgoing link
    # because the stretch will be the same in all cases, for all
    # schemes: as soon as the source detects the failure, the stretch
    # will be 1.
    #
    # shortestPath should be that returned by networkx's path
    # algorithms, as in [0] is the source, [-1] is the destination.
    s = shortestPath[0]
    d = shortestPath[-1]
    shortestPathWithNoFailure = shortestPath

    results = []

    # iteratively fail each link along the shortest path
    for i in xrange(1, len(shortestPath) - 1):
        # "fail node 1" is closer to the source than is fail node 2
        fn1 = shortestPath[i]
        fn2 = shortestPath[i+1]

        # now find out when each node gets the news of the link
        # failure. note that we assume both ends of the link detect
        # the failure and broadcast the link-state update at the same
        # time. also assume zero processing/congestion/etc delay at
        # nodes, ie, only link latencies (distance) determine how fast
        # the update travel.
        #
        # so, 1) remove the fail link, 2) all nodes' shortest path
        # lengths from one end of the failure, 3) same as 2) from the
        # other end, 4) for each node, take the min value from 2) and
        # 3).

        savedEdgeAttr = g[fn1][fn2].copy()
        g.remove_edge(fn1, fn2)

        shortestLengthWithFailure = None
        try:
            shortestLengthWithFailure = shortestPathLengthFunction(g, s, d)
            pass
        except nx.exception.NetworkXError:
            pass

        if not shortestLengthWithFailure:
            # restore edge
            g.add_edge(fn1, fn2, attr_dict=savedEdgeAttr)
            continue

        node2updatedTime = {}

        for n in shortestPath:
            if n == fn1 or n == fn2:
                node2updatedTime[n] = failureDetectionTime
                pass
            else:
                node2updatedTime[n] = failureDetectionTime + \
                                      min(shortestPathLengthFunction(g, fn1, n),
                                          shortestPathLengthFunction(g, fn2, n))
                pass
            pass

        # with the failed link removed, for each of the node before
        # the failure (ie, closer to the source), including fn1, find
        # the shortest path length to the destination.

        # the stretch is largest at the moment fn1 knows about the
        # failure, and the stretch gradually decreases until s knows
        # about the failure, when the stretch should be down to 1.

        timeAfterFailure2Stretch = []

        for j in xrange(shortestPathWithNoFailure.index(fn1), -1, -1):
            n = shortestPathWithNoFailure[j]
            # the packet will reach this node and then get rerouted,
            # so its path length will be [distance s->n] + [distance
            # n->d with failed link removed]
            takenPathLen = shortestPathLengthFunction(g, s, n) + \
                           shortestPathLengthFunction(g, n, d)
            stretch = float(takenPathLen)/shortestLengthWithFailure
            timeAfterFailure2Stretch.append(
                (node2updatedTime[n], stretch))
            if stretch == 1:
                # we've got back down to 1, no need to look further
                break
            pass

        results.append(timeAfterFailure2Stretch)
        # restore edge
        g.add_edge(fn1, fn2, attr_dict=savedEdgeAttr)
        pass

    return results

# an example 

'''
  1    5     1     1     1
s---b-----c-----f--X--g-----t
     \    |           |    /
     5 \  |5         5|  / 5
         \|     4     |/
          d-----------e
'''


if __name__ == '__main__':
    if len(sys.argv) < 3:
        print 'Usage: %s [--weighted] <outputdir> <graphfile>' % (sys.argv[0])
        sys.exit(0)
        pass
    weighted = False
    argvidx = 1
    if sys.argv[argvidx] == '--weighted':
        weighted = True
        argvidx += 1
        pass
    if weighted:
        shortestPathFunction = nx.dijkstra_path
        shortestPathLengthFunction = nx.dijkstra_path_length
        pass
    else:
        shortestPathFunction = nx.shortest_path
        shortestPathLengthFunction = nx.shortest_path_length
        pass
    outputdir = sys.argv[argvidx]
    argvidx += 1
    graphFile = sys.argv[argvidx]
    import utils
    g,_ = utils.textToG(graphFile, ignoreWeights=False, useInt=False)
    allNodes = g.nodes()
    numNodes = len(allNodes)
    alreadySeenPairs = set()
    DAGRouterNotifiesSrcResults = []
    DAGDstNotifiesSrcResults = []
    SafeGuardResults = []
    pickleEvery = 10
    for i in xrange(20):
        idx1 = (struct.unpack('I', os.urandom(4))[0]) % numNodes
        idx2 = (struct.unpack('I', os.urandom(4))[0]) % numNodes

        while idx2 == idx1:
            idx2 = (struct.unpack('I', os.urandom(4))[0]) % numNodes
            pass
        s,d = allNodes[idx1], allNodes[idx2]
        if (s,d) in alreadySeenPairs:
            continue
        else:
            alreadySeenPairs.add((s,d))
            pass

        shortestPath = None
        try:
            shortestPath = shortestPathFunction(g, s, d)
            pass
        except nx.exception.NetworkXError:
            pass
        if not shortestPath:
            continue

        DAGRouterNotifiesSrcResults.extend(calculateForDAG(g, shortestPath, 0.5, True, shortestPathLengthFunction))
        DAGDstNotifiesSrcResults.extend(calculateForDAG(g, shortestPath, 0.5, False, shortestPathLengthFunction))
        SafeGuardResults.extend(calculateForSafeGuard(g, shortestPath, 0.5, shortestPathLengthFunction))

        if ((i + 1) % pickleEvery) == 0:
            for listname in ('DAGRouterNotifiesSrcResults',
                             'DAGDstNotifiesSrcResults',
                             'SafeGuardResults',
                             ):
                exec 'utils.pickleStuff(outputdir + "/" + listname + "%%u-%%u" %% (i + 1 - pickleEvery, i), %s)' % (listname)
                exec '%s = []' % (listname)
                pass
            pass
        pass

    pass
