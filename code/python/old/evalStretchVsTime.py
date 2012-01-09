import cPickle
import networkx as nx
import os
import sys
import struct
from random import Random
import getopt
import pdb
import time
import math

import utils

Id = '$Id$'
Revision = '$Revision$'

# NOTE/XXX: currently we are having the link failure happens at the
# time when the first packet reaches the fail link. this is not
# exactly like what the safeguard paper does. they have the link fail
# at time zero. failing the link at time zero makes safeguard better
# because the link update will have spread to nearby routers before
# the first packet reaches them. this does not affect our DAG
# schemes. but we should also compare against safeguard failing the
# link at time 0.
#

# edge "e" is (u, v) tuple. "path" is list of nodes.
#
# note that the edge is undirectioned. so returns true if either u--v
# or v--u is in the path.
def isEdgeInPath(e, path):
    # find u
    try:
        idx = path.index(e[0])
        # is v either side of u?
        v = e[1]
        if idx == 0:
            # u is at beginning of path
            return path[1] == v
        elif idx == (len(path) - 1):
            # u is at end of path
            return path[-2] == v
        else:
            # u is in middle of path
            return (path[idx-1] == v) or (path[idx+1] == v)
        pass
    except ValueError:
        pass
    return False

##########################################################
def pairsThatUseEdge(g,
                     e, # edge is (node1,node2) tuple
                     nodeList, # list of nodes of graph g
                     shortestPathFunc, cachedSrc2ShortestPaths,
                     # two random sources to sample source and destination
                     srcrandom, dstrandom,
                     srcSampleSize=10, dstSampleSizePerSrc=100):
    # returns a dictionary mapping from [source] to [list of
    # destinations to which the source's shortest paths contain edge
    # e]. the list might be empty since we're sampling randomly.
    #
    # do this by brute force:
    #
    # loop while numSrcs less than "srcSampleSize":
    #     pick a random source.
    #     run singleSourceShortestPathFunc if source not in cache.
    #     filter to obtain all paths that contain edge e
    #     if fewer than "maxNumDstsPerSrc", then add all to results
    #     else add "maxNumDstsPerSrc" random dsts to results
    #
    #
    # "e" is the edge, which is a tuple (u, v). assume that e is a
    # valid edge in the graph.
    #
    # "max" is maximum
    # number of pairs to return. the returned list might be shorter 
    #

    # map from src to list of dsts
    src2Dsts = {}
    srcs = srcrandom.sample(nodeList, min(len(nodeList), srcSampleSize))
    for src in srcs:
        src2Dsts[src] = []
        # map from: dst, to: shortest src-dst path.
        shortestPaths = cachedSrc2ShortestPaths.get(src, {})
        cachedSrc2ShortestPaths[src] = shortestPaths

        ## this block could be replaced with
        ## "single_source_shortest_path(g, src)", but for big graphs,
        ## it could take a long time while there's a good chance most
        ## of the dsts won't be used.
        #
        # this loop serves both purposes: (find and save all paths)
        # and (find and save paths that contain e).
        dsts = dstrandom.sample(nodeList,
                                min(len(nodeList), dstSampleSizePerSrc))
        for dst in dsts:
            if (dst == src):
                continue
            if not dst in shortestPaths:
                # if we do NOT already have it, then compute it
                shortestPath = None
                try:
                    shortestPath = shortestPathFunc(g, src, dst)
                    pass
                except:
                    pass
                # whether path exists or not, save it
                shortestPaths[dst] = shortestPath
                pass
            else:
                # we already have it
                shortestPath = shortestPaths[dst]
                pass

            # ok, now we have the shortest path, either valid or invalid
            if shortestPath and isEdgeInPath(e, shortestPath):
                src2Dsts[src].append(dst)
                pass
            pass
        if len(src2Dsts[src]) == 0:
            del src2Dsts[src]
            pass
        pass
    return src2Dsts

##########################################################
def calculateForFastDAG_wrapper(g, shortestPath, fn1, fn2,
                                shortestLengthWithFailure,
                                preCalculatedPathLengthsDict,
                                processingDelay,
                                passThruDelay, timeOfFailure,
                                ):
    return calculateForDAG(
        g=g, shortestPath=shortestPath,
        fn1=fn1, fn2=fn2, shortestLengthWithFailure=shortestLengthWithFailure,
        preCalculatedPathLengthsDict=preCalculatedPathLengthsDict,
        mode='fast',
        processingDelay=processingDelay,
        passThruDelay=passThruDelay,
        timeOfFailure=timeOfFailure,
        )

def calculateForSlowDAG_wrapper(g, shortestPath, fn1, fn2,
                                shortestLengthWithFailure,
                                preCalculatedPathLengthsDict,
                                processingDelay,
                                passThruDelay, timeOfFailure,
                                ):
    return calculateForDAG(
        g=g, shortestPath=shortestPath,
        fn1=fn1, fn2=fn2, shortestLengthWithFailure=shortestLengthWithFailure,
        preCalculatedPathLengthsDict=preCalculatedPathLengthsDict,
        mode='slow',
        processingDelay=processingDelay,
        passThruDelay=passThruDelay,
        timeOfFailure=timeOfFailure,
        )

def calculateForFloodedDAG_wrapper(g, shortestPath, fn1, fn2,
                                   shortestLengthWithFailure,
                                   preCalculatedPathLengthsDict,
                                   processingDelay,
                                   passThruDelay, timeOfFailure,
                                   ):
    return calculateForDAG(
        g=g, shortestPath=shortestPath,
        fn1=fn1, fn2=fn2, shortestLengthWithFailure=shortestLengthWithFailure,
        preCalculatedPathLengthsDict=preCalculatedPathLengthsDict,
        mode='flooded',
        processingDelay=processingDelay,
        passThruDelay=passThruDelay,
        timeOfFailure=timeOfFailure,
        )

def calculateForDAG(g, shortestPath, fn1, fn2,
                    shortestLengthWithFailure, preCalculatedPathLengthsDict,
                    mode,
                    processingDelay,
                    passThruDelay, timeOfFailure,
                    ):
    # "shortestPath" should be that returned by networkx's path
    # algorithms, as in [0] is the source, [-1] is the destination.

    # "mode": must be one of "flooded", "fast", and "slow".

    s = shortestPath[0]
    d = shortestPath[-1]
    shortestPathWithNoFailure = shortestPath

    # "fail node 1" must be the node closer to the source than is fail
    # node 2.

    # now find out when the source gets the news of the link
    # failure. assume zero processing/congestion/etc delay at
    # nodes, ie, only link latencies (distance) determine how fast
    # the update travel.

    distFromSToFn1 = preCalculatedPathLengthsDict[fn1][s]
    distFromFn1ToD = preCalculatedPathLengthsDict[fn1][d]
    takenPathLen = distFromSToFn1 + distFromFn1ToD

    packetSentTime2Stretch = []

    # this stretch is before the source is notified
    stretch = float(takenPathLen)/shortestLengthWithFailure

    # t_tx of the first packet that is redirected
    t_tx = max(0, timeOfFailure - distFromSToFn1)
    packetSentTime2Stretch.append((t_tx, stretch))
    if stretch != 1:
        # after the source receives the news, the stretch is 1
        if mode == 'flooded':
            sourceUpdatedTime = timeOfFailure + \
                                distFromSToFn1 + \
                                shortestPath.index(fn1)*passThruDelay + \
                                processingDelay
            pass
        elif mode == 'fast':
            sourceUpdatedTime = max(timeOfFailure, distFromSToFn1) + \
                                distFromSToFn1 + \
                                processingDelay
            pass
        elif mode == 'slow':
            sourceUpdatedTime = max(timeOfFailure, distFromSToFn1) + \
                                distFromFn1ToD + \
                                shortestLengthWithFailure + \
                                processingDelay
        else:
            raise ("invalid mode [%s]" % (mode))
            pass
        packetSentTime2Stretch.append((sourceUpdatedTime, 1))
        pass

    if packetSentTime2Stretch[0][0] > 0:
        packetSentTime2Stretch.insert(0, (0, 1))
        pass
    if packetSentTime2Stretch[-1][1] != 1:
        raise Exception('the last stretch must be 1, shortestPath [%s], '
                        'failedLink [%s], packetSentTime2Stretch [%s]' % \
                        (shortestPath, (fn1, fn2), packetSentTime2Stretch))

    return packetSentTime2Stretch

##########################################################
def calculateForFastVSR(g, shortestPath, fn1, fn2,
                        shortestLengthWithFailure, preCalculatedPathLengthsDict,
                        processingDelay,
                        passThruDelay, timeOfFailure,
                        ):
    # "shortestPath" should be that returned by networkx's path
    # algorithms, as in [0] is the source, [-1] is the destination.

    s = shortestPath[0]
    d = shortestPath[-1]
    shortestPathWithNoFailure = shortestPath

    # "fail node 1" must be the node closer to the source than is fail
    # node 2.

    # there are actually two intervals/types here:
    #
    # 1. between start of failure and when the source is notified. the
    # packets sent in this interval are "dropped" and thus have to be
    # resent by the source once it has figured out the new path to
    # send. this interval is 0--ie, no packets dropped/resent--if the
    # source is the same as r_0/fn1.
    #
    # 2. then once the source knows about the link failure, packets
    # sent between then and processingDelay are not actually sent but
    # delayed until processingDelay time later, when the source knows
    # which path to use. if processingDelay == 0, then no packets of
    # this type.
    #
    # so here is special case:

    if (s == fn1) and (processingDelay == 0):
        return [(min(0, timeOfFailure), 1)]


    #
    #
    # after here, we have s != fn1 (which means there are
    # dropped/resent packets) AND/OR processingDelay > 0 (which means
    # there are delayed--by the source--packets)
    #
    #

    distFromSToFn1 = preCalculatedPathLengthsDict[fn1][s]
    distFromFn1ToD = preCalculatedPathLengthsDict[fn1][d]

    packetSentTime2Stretch = []

    if (s != fn1):
        # t_tx of the first packet that is "dropped" and has to be
        # resent.
        t_tx_firstResent = max(0, timeOfFailure - distFromSToFn1)
        stretch_firstResent = \
            float((2*distFromSToFn1) + processingDelay + shortestLengthWithFailure) / shortestLengthWithFailure
        packetSentTime2Stretch.append((t_tx_firstResent, stretch_firstResent))

        # at this time, the source has been notified, and thus it
        # stops sending out packets that are to be dropped anyway.

        # XXX/technically packet sent at this time actually belongs to
        # the next interval/type, whichever that is. in other words,
        # packets sent in the range [t_tx_firstResent,
        # t_tx_lastResent) are dropped/resent.

        t_tx_lastResent = t_tx_firstResent + (2*distFromSToFn1)

        # the packets that are sent in the range [t_tx_firstResent,
        # t_tx_lastResent) have different (decreasing) stretches, so
        # we simulate them here. denote p_fr as the first packet that
        # is resent. because we're assuming that all resent packets
        # will LATER be (re)sent out at the same time, a packet p that
        # is ORIGINALLY sent X amount of time after p_fr is sent will
        # take X amount of time LESS to reach destination compared to
        # p_fr, so the stretch of p can be computed from the stretch
        # of p_fr.
        start = int(t_tx_firstResent) + 1
        start_stretch = stretch_firstResent - \
                        (float(start - t_tx_firstResent) / \
                         shortestLengthWithFailure)
        stop = int(math.ceil(t_tx_lastResent)) - 1
        if (start < stop):
            stop_stretch = stretch_firstResent - \
                           (float(stop - t_tx_firstResent) / \
                            shortestLengthWithFailure)
            packetSentTime2Stretch.append(
                (start, start_stretch, stop, stop_stretch))
            pass
        else:
            packetSentTime2Stretch.append(
                (start, start_stretch))
            pass

        t_tx_converged = t_tx_lastResent
        pass


    if (processingDelay > 0):
        # this is the packet that starts being "sent" right at the
        # time the source is notified, so it is actually not sent but
        # is buffered until processingDelay has elapsed (to compute
        # new SPT & update FIB).
        t_tx_firstDelayed = max(0, timeOfFailure - distFromSToFn1) + \
                            (2*distFromSToFn1)
        stretch_firstDelayed = (float(processingDelay) + shortestLengthWithFailure) / shortestLengthWithFailure
        packetSentTime2Stretch.append((t_tx_firstDelayed, stretch_firstDelayed))

        # t_tx of one past the last delayed packet, ie, first packet
        # that is normal, i.e., has stretch-1, i.e., after source has
        # detected the problem and updated SPT/FIB. this is always
        # processingDelay after t_tx of the first packet that is
        # resent.

        t_tx_lastDelayed = t_tx_firstDelayed + processingDelay

        # the packets that are sent in the range [t_tx_firstDelayed,
        # t_tx_lastDelayed) have different (decreasing) stretches, so
        # we simulate them here. because we're assuming that all
        # delayed packets will LATER be (re)sent out at the same time,
        # a packet p that is ORIGINALLY sent X amount of time after
        # t_tx_firstDelayed will be delayed X amount of time LESS and
        # thus will take X amount of time LESS to reach destination
        # compared to packet sent at t_tx_firstDelayed.
        start = int(t_tx_firstDelayed) + 1
        start_stretch = stretch_firstDelayed - \
                      (float(start - t_tx_firstDelayed) / \
                       shortestLengthWithFailure)
        stop = int(math.ceil(t_tx_lastDelayed)) - 1
        if (start < stop):
            stop_stretch = stretch_firstDelayed - \
                           (float(stop - t_tx_firstDelayed) / \
                            shortestLengthWithFailure)
            packetSentTime2Stretch.append(
                (start, start_stretch, stop, stop_stretch))
            pass
        else:
            packetSentTime2Stretch.append(
                (start, start_stretch))
            pass

        t_tx_converged = t_tx_lastDelayed
        pass

    packetSentTime2Stretch.append((t_tx_converged, 1))

    if packetSentTime2Stretch[0][0] > 0:
        packetSentTime2Stretch.insert(0, (0, 1))
        pass
    if packetSentTime2Stretch[-1][1] != 1:
        raise Exception('the last stretch must be 1, shortestPath [%s], '
                        'failedLink [%s], packetSentTime2Stretch [%s]' % \
                        (shortestPath, (fn1, fn2), packetSentTime2Stretch))

    return packetSentTime2Stretch

##########################################################
def calculateForSafeGuard(g, shortestPath, fn1, fn2,
                          shortestLengthWithFailure,
                          preCalculatedPathLengthsDict,
                          processingDelay,
                          passThruDelay, timeOfFailure,
                          ):
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

    # "fail node 1" must be the node closer to the source than is fail
    # node 2.

    # we assume that paths/distances between any node pair involving
    # nodes between s and fn1, are the same before and after the link
    # failure.
    #
    # also, distance between x and y are same as distance between y
    # and x.




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

    # h(x,y) is hopcount between x and y, and A and B have hopcounts
    # of 2 and 1, respectively, from fn1 in the following graph:
    # A--B--fn1.
    #
    # d(x,y): distance (sum of edges' weights for weighted graphs, or
    # h(x,y) for unweighted graphs) from x to y.
    #
    # The first packet leaves the source at time 0 and reaches fn1 at
    # time dist(src, fn1), which is when the link fails.
    #
    # So we have the first tuple (0, stretchByfn1). XXX/giang: this is
    # a simplification because if processingDelay is > 0, then packets sent
    # between times 0 and processingDelay actually are dropped because the
    # forwarding table is still using the down link. it should really
    # be (processingDelay, stretchByfn1).
    #
    # Then, iteratively, we consider each router R on the primary
    # path, backwards, from the fn1 to the source router.  For each,
    # we find:
    #
    # 0. At what time does this router R "receive" the link status
    # update? t_rxLSA
    #
    # * if r != fn1:
    #
    # = timeOfFailure + (h(fn1,r) - 1)*passThruDelay + d(fn1,r)
    #
    # * if r == fn1:
    #
    # = timeOfFailure
    #
    # 1. At what time does this router update its FIB (reflecting the
    # removal of the link)? t_updatedFIB
    #
    # = [timeItReceivesLinkStatusUpdate] + [processingDelays]
    #
    # = t_rxLSA + [processingDelay]
    #
    # 2. The first packet to get the stretch offered by router r is
    # that which arrives at the router at the same time the router
    # updates its FIB, i.e., the time found in 1. Thus, the packet's
    # sent time: t_tx
    #
    # = [timeRouterRUpdatesItsFIB] - [timeDistanceFromSourceRouterToR]
    #
    # = t_updatedFIB - d(src,r)
    #
    # = t_rxLSA + processingDelay - d(src,r)

    # with the failed link removed, for each of the node before
    # the failure (ie, closer to the source), including fn1, find
    # the shortest path length to the destination.

    # the stretch is largest at the moment fn1 knows about the
    # failure, and the stretch gradually decreases until s knows about
    # the failure, when the stretch should be down to 1. however, it's
    # possible that the stretch goes down to 1 earlier, or never never
    # is higher than 1, depending on the location of the failed link
    # relative to the source and destination.

    # attempt to optimize:
    #
    # this one is just an example showing that the stretch can be > 1
    # even if there is no backtracking. consider this graph: after
    # link b-t fails, packets redirected by c have higher stretch than
    # packets redirected by b and they do not backtrack through
    # b. packets redirected by a have stretch-1.
    #
    #             d---e
    #            /|   |
    #          /  |   |
    # s---a---b---c-X-t
    #
    # the above graph also shows that if the shortest (alternate) path
    # from SRC to dst AFTER the link failure includes a node n, then
    # node n has stretch-1. (this is obvious because if a node n is on
    # a shortest path p from s to d, then (one of) n's shortest path
    # to d is the suffix of p.) we implement this optimization by
    # stopping the loop when we have stretch-1.

    packetSentTime2Stretch = []
#    previousStretch = None
    fn1Idx = shortestPathWithNoFailure.index(fn1)
    for j in xrange(fn1Idx, -1, -1):
        r = shortestPathWithNoFailure[j]

        # we assume that paths/distances between any node pair
        # involving nodes between s and fn1, are the same before and
        # after the link failure.
        #
        # also, distance between x and y are same as distance between
        # y and x.

        ssspl_r = preCalculatedPathLengthsDict[r]

        # find the stretch
        if j == fn1Idx:
            # this is "r_0", we have to handle specially because r_0
            # buffers packets while it's computing new SPT etc

            # sent time of the first packet that will be buffered.
            t_tx = max(0,
                       timeOfFailure - ssspl_r[s])
            # its stretch
            stretch = float(ssspl_r[s] + ssspl_r[d] + processingDelay) / shortestLengthWithFailure

            assert len(packetSentTime2Stretch) == 0
            packetSentTime2Stretch.append((t_tx, stretch))

            if processingDelay > 0:
                # sent time of the first packet that will arrive at
                # r_0 right when it's finished computing new SPT and
                # updating FIB, etc... ie, this packet will not have
                # to be buffered.
                t_tx = max(0,
                           timeOfFailure + processingDelay - ssspl_r[s])
                # its stretch
                stretch = float(ssspl_r[s] + ssspl_r[d]) / shortestLengthWithFailure

                if packetSentTime2Stretch[-1][0] == t_tx:
                    # the last t_tx is the same as our t_tx
                    assert t_tx == 0 and len(packetSentTime2Stretch) == 1
                    # instead of appending, we should replace
                    packetSentTime2Stretch[0] = (t_tx, stretch)
                    pass
                else:
                    packetSentTime2Stretch.append((t_tx, stretch))

                    # the packets that are buffered really have
                    # different (decreasing) stretches, so we simulate
                    # them here. we assume that once r_0 has computed
                    # the new SPT and updated the FIB, then all the
                    # buffered packets will be sent out essentially at
                    # the same time (line speed).
                    start = int(packetSentTime2Stretch[0][0]) + 1
                    start_stretch = packetSentTime2Stretch[-1][1] + \
                                    float(packetSentTime2Stretch[-1][0] - start) / \
                                    shortestLengthWithFailure
                    stop = int(math.ceil(packetSentTime2Stretch[1][0])) - 1
                    if (start < stop):
                        stop_stretch = packetSentTime2Stretch[-1][1] + \
                                       float(packetSentTime2Stretch[-1][0] - stop) / \
                                       shortestLengthWithFailure
                        packetSentTime2Stretch.insert(
                            -1, (start, start_stretch, stop, stop_stretch))
                        pass
                    else:
                        packetSentTime2Stretch.insert(
                            -1, (start, start_stretch))
                        pass
                    pass
                pass

            # we have handled special case of r_0, do a "continue"
            continue
        else:
            stretch = float(ssspl_r[s] + ssspl_r[d]) / shortestLengthWithFailure

            # packet sent time
            t_tx = max(0,
                       timeOfFailure + ssspl_r[fn1] + (fn1Idx - j)*passThruDelay +\
                       processingDelay - ssspl_r[s])
            pass

        ## if stretch == previousStretch:
        ##     # effectively no change in stretch -> dont add it. this
        ##     # CAN legitimately happen. eg, in graph 1239 latencies,
        ##     # shortest path [6603, 4104, 4116, 6605], fail link (4116,
        ##     # 6605)
        ##     if stretch != 1:
        ##         # this is just making sure this corner case (if at all
        ##         # possible) doesn't screw us
        ##         continue
        ##     pass
        ## else:
        ##     previousStretch = stretch
        ##     pass

        # append to or or update result
        if len(packetSentTime2Stretch) == 0:
            packetSentTime2Stretch.append((t_tx, stretch))
            pass
        else:
            assert t_tx >= packetSentTime2Stretch[-1][0]
            if packetSentTime2Stretch[-1][0] == t_tx:
                # the last t_tx is the same
                assert t_tx == 0 and len(packetSentTime2Stretch) == 1
                # instead of appending, we should replace
                packetSentTime2Stretch[0] = (t_tx, stretch)
                pass
            else:
                packetSentTime2Stretch.append((t_tx, stretch))
                pass
            pass

        if stretch == 1:
            break
        pass

    if packetSentTime2Stretch[0][0] > 0:
        packetSentTime2Stretch.insert(0, (0, 1))
        pass
    if packetSentTime2Stretch[-1][1] != 1:
        raise Exception('the last stretch must be 1, shortestPath [%s], '
                        'failedLink [%s], packetSentTime2Stretch [%s]' % \
                        (shortestPath, (fn1, fn2), packetSentTime2Stretch))

    return packetSentTime2Stretch


def getPathCommonality(g, shortestPath, failedLink,
                       shortestPathFunction,
                       ):
    s = shortestPath[0]
    d = shortestPath[-1]
    shortestPathWithNoFailure = shortestPath

    # "fail node 1" must be the node closer to the source than is fail
    # node 2.
    if shortestPath.index(failedLink[0]) < shortestPath.index(failedLink[1]):
        fn1 = failedLink[0]
        fn2 = failedLink[1]
        pass
    else:
        fn1 = failedLink[1]
        fn2 = failedLink[0]
        pass

    savedEdgeAttr = g[fn1][fn2].copy()
    g.remove_edge(fn1, fn2)

    shortestPathWithFailure = None
    try:
        shortestPathWithFailure = shortestPathFunction(g, s, d)
        pass
    except nx.exception.NetworkXError:
        pass

    if not shortestPathWithFailure:
        # restore edge
        g.add_edge(fn1, fn2, attr_dict=savedEdgeAttr)
        return None

    fn1idx = shortestPathWithNoFailure.index(fn1)
    # no need to check idx 0
    i = 0 # i MUST be the highest idx where the paths share a node
    for i in xrange(1, fn1idx+1, 1):
        if shortestPathWithFailure[i] != shortestPathWithNoFailure[i]:
            i -= 1
            break
        pass

    # restore edge
    g.add_edge(failedLink[0], failedLink[1], attr_dict=savedEdgeAttr)

    return fn1idx, i

# an example 

'''
  1    5     1     1     1
s---b-----c-----f--X--g-----t
     \    |           |    /
     5 \  |5         5|  / 5
         \|     4     |/
          d-----------e
'''

##########################################################

class EvalResult:
    def __init__(self, graphFile,
                 argv,
                 linkSampleSize, srcSampleSize, dstSampleSize,
                 weighted,
                 startdateSecs, enddateSecs, schemeToResult,
                 srcSeed, linkSeed, dstSeed,
                 revision, utilsRevision):

        self.graphFile = graphFile
        self.argv = argv

        self.linkSampleSize = linkSampleSize
        self.srcSampleSize = srcSampleSize
        self.dstSampleSize = dstSampleSize
        self.weighted = weighted

        self.startdateSecs = startdateSecs
        self.enddateSecs = enddateSecs
        self.schemeToResult = schemeToResult

        self.srcSeed = srcSeed
        self.linkSeed = linkSeed
        self.dstSeed = dstSeed

        self.revision = revision
        self.utilsRevision = utilsRevision

        return

def getEdgesAndPaths(g, src, singleSourceShortestPathFunc,
                     edgeSampleSize, edgerandomObj,
                     dstSampleSize, dstrandomObj):
    # get all shortest paths
    shortestPaths = singleSourceShortestPathFunc(g, src)
    del shortestPaths[src]
    shortestPaths = shortestPaths.values()
    # gather all the edges in all the paths
    allEdges = set()
    for path in shortestPaths:
        for i in xrange(len(path)-1):
            allEdges.add((path[i], path[i+1]))
            pass
        pass
    edges = edgerandomObj.sample(allEdges,
                                 min(len(allEdges), edgeSampleSize))
    edge2PathsThatUseEdge = {}
    for edge in edges:
        pathsThatUseEdge = filter(lambda path: isEdgeInPath(edge, path),
                                  shortestPaths)
        edge2PathsThatUseEdge[edge] = dstrandomObj.sample(
            pathsThatUseEdge,
            min(len(pathsThatUseEdge), dstSampleSize))
        pass
    return edge2PathsThatUseEdge

def cmd_runeval(argv):
    assert argv[0] == 'runeval'
    def usageAndExit(progname):
        print '''
Usage: %s [--cache-shortest-paths] [--weighted] -l ... -s ... -d ...
          [--srcStartIdx ...] [--srcEndIdx ...]
          [--srcSeed ...] [--linkSeed ...] [--dstSeed ...]
          --timeOfFailure ... --processingDelay ... --passThruDelay ...
          <graphfile>

sample the sources first. then for each source, get all the links that
are used by its single source shortest paths to all
destinations. sample those links. for each link, sample
path/destination.

         -s: size of random sample of sources to examine. might be
             fewer if graph is smaller.

         -l: size of random sample of links to fail. might be fewer if
             graph is smaller. also, link (u,v) is same as (v,u).

         -d: size of random sample of destinations to examine per
             failed link per source. might be fewer if graph is
             smaller.

         --weighted: take edge weights into account when computing
                     shortest paths.
''' % (progname)
        sys.exit(-1)
        return

    startdateSecs = int(time.time())
    print "start date: [%s]" % (time.ctime())
    print "Revision:           [%s]" % (Revision)
    print "utils.Revision:     [%s]" % (utils.Revision)

    weighted = False
    linkSampleSize = srcSampleSize = dstSampleSize = None
    srcSeed = linkSeed = dstSeed = None
    srcStartIdx = srcEndIdx = None
    timeOfFailure = processingDelay = passThruDelay = None

    print ' '.join(argv)

    opts, args = getopt.getopt(argv[1:], 'l:s:d:',
                               ['weighted', 'timeOfFailure=',
                                'processingDelay=', 'passThruDelay=',
                                'srcSeed=', 'linkSeed=', 'dstSeed=',
                                'srcStartIdx=', 'srcEndIdx=',
                                ])

    ## parse options
    for o, a in opts:
        if o == '-l':
            linkSampleSize = int(a)
            assert linkSampleSize > 0
            pass
        elif o == '-s':
            srcSampleSize = int(a)
            assert srcSampleSize > 0
            pass
        elif o == '-d':
            dstSampleSize = int(a)
            assert dstSampleSize > 0
            pass
        elif o == '--weighted':
            weighted = True
            pass
        elif o == '--srcStartIdx':
            srcStartIdx = int(a)
            pass
        elif o == '--srcEndIdx':
            srcEndIdx = int(a)
            pass
        elif o == '--srcSeed':
            srcSeed = int(a)
            pass
        elif o == '--linkSeed':
            linkSeed = int(a)
            pass
        elif o == '--dstSeed':
            dstSeed = int(a)
            pass
        elif o == '--timeOfFailure':
            timeOfFailure = float(a)
            assert timeOfFailure >= 0
            pass
        elif o == '--processingDelay':
            processingDelay = float(a)
            assert processingDelay >= 0
            pass
        elif o == '--passThruDelay':
            passThruDelay = float(a)
            assert passThruDelay >= 0
            pass
        pass

    if not (linkSampleSize and srcSampleSize and dstSampleSize and \
            timeOfFailure != None and processingDelay != None and \
            passThruDelay != None):
        usageAndExit(argv[0])
        pass

    if weighted:
        singleSourceShortestPathFunction = nx.single_source_dijkstra_path
        singleSourceShortestPathLengthFunction = nx.single_source_dijkstra_path_length
        shortestPathLengthFunction = nx.dijkstra_path_length
        pass
    else:
        singleSourceShortestPathFunction = nx.single_source_shortest_path
        singleSourceShortestPathLengthFunction = nx.single_source_shortest_path_length
        shortestPathLengthFunction = nx.shortest_path_length
        pass

    graphFile = args[0]
    g,_ = utils.textToG(graphFile, ignoreWeights=(not weighted), useInt=True)
    allNodes = tuple(sorted(g.nodes()))

    if srcStartIdx is None:
        srcStartIdx = 0
        pass
    if srcEndIdx is None:
        srcEndIdx = len(allNodes) - 1
        pass
    assert 0 <= srcStartIdx <= srcEndIdx <= (len(allNodes) - 1)

    assert srcSampleSize <= (srcEndIdx - srcStartIdx + 1)

    if srcSeed is None:
        srcSeed = struct.unpack('I', os.urandom(4))[0]
        pass
    if linkSeed is None:
        linkSeed = struct.unpack('I', os.urandom(4))[0]
        pass
    if dstSeed is None:
        dstSeed = struct.unpack('I', os.urandom(4))[0]
        pass

    print
    print 'srcSeed', srcSeed
    print 'linkSeed', linkSeed
    print 'dstSeed', dstSeed
    print

    schemeToResult = {
        'Flooded-DAG': [],
        'Fast-DAG': [],
        'Slow-DAG': [],
        'SafeGuard': [],
        'Fast-VSR': [],
        }

    schemeToCalcFunc = (
        (schemeToResult['Flooded-DAG'], calculateForFloodedDAG_wrapper),
        (schemeToResult['Fast-DAG'], calculateForFastDAG_wrapper),
        (schemeToResult['Slow-DAG'], calculateForSlowDAG_wrapper),
        (schemeToResult['SafeGuard'], calculateForSafeGuard),
        (schemeToResult['Fast-VSR'], calculateForFastVSR),
        )

    cachedSrc2ShortestPaths = {}

    linkrandom = Random(linkSeed)
    srcrandom = Random(srcSeed)
    dstrandom = Random(dstSeed)

    ## origEdges = g.edges(data=True)
    ## origNodes = g.nodes()

    # sample the sources
    srcs = srcrandom.sample(allNodes[srcStartIdx:srcEndIdx+1], srcSampleSize)
    for i, src in enumerate(srcs):
        # for each source
        print 'src', src, 'i', i
        sys.stdout.flush()

        link2Paths = getEdgesAndPaths(
            g, src, singleSourceShortestPathFunction, linkSampleSize, linkrandom,
            dstSampleSize, dstrandom)
        for e, paths in link2Paths.iteritems():
            for shortestPath in paths:
                s = shortestPath[0]
                d = shortestPath[-1]
                # the calculators expect fn1 is closer to s than it is
                # to d.
                fn1 = e[0]
                fn2 = e[1]
                savedEdgeAttr = g[fn1][fn2].copy()
                g.remove_edge(fn1, fn2)
                shortestLengthWithFailure = None
                try:
                    shortestLengthWithFailure = shortestPathLengthFunction(g, s, d)
                    pass
                except nx.exception.NetworkXError:
                    pass
                if not shortestLengthWithFailure:
                    # restore edge and move on to next edge
                    g.add_edge(fn1, fn2, attr_dict=savedEdgeAttr)
                    continue
                # prepare the preCalculatedPathLengthsDict
                preCalculatedPathLengthsDict = {}
                for r_idx in xrange(shortestPath.index(fn1), -1, -1):
                    r = shortestPath[r_idx]
                    preCalculatedPathLengthsDict[r] = {}
                    for target in (s, d, fn1):
                        preCalculatedPathLengthsDict[r][target] = \
                            shortestPathLengthFunction(g, r, target)
                        pass
                    pass
                # run the calculators
                for scmResults, scmCalcFunc in schemeToCalcFunc:
                    result = scmCalcFunc(
                        g=g, shortestPath=shortestPath, fn1=fn1, fn2=fn2,
                        shortestLengthWithFailure=shortestLengthWithFailure,
                        preCalculatedPathLengthsDict=preCalculatedPathLengthsDict,
                        processingDelay=processingDelay,
                        passThruDelay=passThruDelay,
                        timeOfFailure=timeOfFailure,
                        )
                    if result:
                        scmResults.append(result)
                        pass
                    pass
                # restore edge
                g.add_edge(fn1, fn2, attr_dict=savedEdgeAttr)
                pass
            pass
        pass

    ## assert origEdges == g.edges(data=True)
    ## assert origNodes == g.nodes()

    enddateSecs = int(time.time())
    print "end date: [%s]" % (time.ctime())

    evalResult = EvalResult(
        graphFile=graphFile,
        argv=argv,
        linkSampleSize=linkSampleSize,
        srcSampleSize=srcSampleSize,
        dstSampleSize=dstSampleSize,
        weighted=weighted,
        startdateSecs=startdateSecs, enddateSecs=enddateSecs,
        schemeToResult=schemeToResult,
        srcSeed=srcSeed, linkSeed=linkSeed, dstSeed=dstSeed,
        revision=Revision, utilsRevision=utils.Revision)

    pickleFilename = 'stretchVsTimeResult.pickle_%u_%u_%s' % \
        (srcStartIdx, srcEndIdx, time.strftime('%m%d%y_%H%M%S',
                                               time.localtime(startdateSecs)))
    utils.pickleStuff(pickleFilename, evalResult)

    pass

def cmd_getpathcommonality(argv):
    assert argv[0] == 'getpathcommonality'
    def usageAndExit(progname):
        print '''
Usage: %s [--cache-shortest-paths] [--weighted] -l ... -s ... -d ...
          [--srcStartIdx ...] [--srcEndIdx ...]
          [--srcSeed ...] [--linkSeed ...] [--dstSeed ...]
          --timeOfFailure ... --processingDelay ... --passThruDelay ...
          <graphfile>

sample the sources first. then for each source, get all the links that
are used by its single source shortest paths to all
destinations. sample those links. for each link, sample
path/destination.

         -s: size of random sample of sources to examine. might be
             fewer if graph is smaller.

         -l: size of random sample of links to fail. might be fewer if
             graph is smaller. also, link (u,v) is same as (v,u).

         -d: size of random sample of destinations to examine per
             failed link per source. might be fewer if graph is
             smaller.

         --weighted: take edge weights into account when computing
                     shortest paths.
''' % (progname)
        sys.exit(-1)
        return

    startdateSecs = int(time.time())
    print "start date: [%s]" % (time.ctime())
    print "Revision:           [%s]" % (Revision)
    print "utils.Revision:     [%s]" % (utils.Revision)

    weighted = False
    linkSampleSize = srcSampleSize = dstSampleSize = None
    srcSeed = linkSeed = dstSeed = None
    srcStartIdx = srcEndIdx = None
    timeOfFailure = processingDelay = passThruDelay = None

    print ' '.join(argv)

    opts, args = getopt.getopt(argv[1:], 'l:s:d:',
                               ['weighted', 'srcSeed=', 'linkSeed=', 'dstSeed=',
                                'srcStartIdx=', 'srcEndIdx=',
                                ])
    ## parse options
    for o, a in opts:
        if o == '-l':
            linkSampleSize = int(a)
            assert linkSampleSize > 0
            pass
        elif o == '-s':
            srcSampleSize = int(a)
            assert srcSampleSize > 0
            pass
        elif o == '-d':
            dstSampleSize = int(a)
            assert dstSampleSize > 0
            pass
        elif o == '--weighted':
            weighted = True
            pass
        elif o == '--srcStartIdx':
            srcStartIdx = int(a)
            pass
        elif o == '--srcEndIdx':
            srcEndIdx = int(a)
            pass
        elif o == '--srcSeed':
            srcSeed = int(a)
            pass
        elif o == '--linkSeed':
            linkSeed = int(a)
            pass
        elif o == '--dstSeed':
            dstSeed = int(a)
            pass
        else:
            raise Exception('unrecognized option [%s]' % (o))
        pass

    if not (linkSampleSize and srcSampleSize and dstSampleSize):
        usageAndExit(argv[0])
        pass

    if weighted:
        shortestPathFunction = nx.dijkstra_path
        singleSourceShortestPathFunction = nx.single_source_dijkstra_path
        pass
    else:
        shortestPathFunction = nx.shortest_path
        singleSourceShortestPathFunction = nx.single_source_shortest_path
        pass

    graphFile = args[0]
    g,_ = utils.textToG(graphFile, ignoreWeights=(not weighted), useInt=True)
    allNodes = tuple(sorted(g.nodes()))

    if srcStartIdx is None:
        srcStartIdx = 0
        pass
    if srcEndIdx is None:
        srcEndIdx = len(allNodes) - 1
        pass
    assert 0 <= srcStartIdx <= srcEndIdx <= (len(allNodes) - 1)

    assert srcSampleSize <= (srcEndIdx - srcStartIdx + 1)

    if srcSeed is None:
        srcSeed = struct.unpack('I', os.urandom(4))[0]
        pass
    if linkSeed is None:
        linkSeed = struct.unpack('I', os.urandom(4))[0]
        pass
    if dstSeed is None:
        dstSeed = struct.unpack('I', os.urandom(4))[0]
        pass

    print
    print 'srcSeed', srcSeed
    print 'linkSeed', linkSeed
    print 'dstSeed', dstSeed
    print

    linkrandom = Random(linkSeed)
    srcrandom = Random(srcSeed)
    dstrandom = Random(dstSeed)

    ## origEdges = g.edges(data=True)
    ## origNodes = g.nodes()

    numPreFailureNodes = []
    numCommonNodes = []
    numDiffNodes = []
    cumuNumPreFailureNode = 0
    cumuNumCommonNode = 0
    cumuNumDiffNode = 0
    count = 0

    # sample the sources
    srcs = srcrandom.sample(allNodes[srcStartIdx:srcEndIdx+1], srcSampleSize)
    for i, src in enumerate(srcs):
        # for each source
        print 'src', src, 'i', i
        sys.stdout.flush()

        link2Paths = getEdgesAndPaths(
            g, src, singleSourceShortestPathFunction, linkSampleSize, linkrandom,
            dstSampleSize, dstrandom)
        for e, paths in link2Paths.iteritems():
            for path in paths:
                shortestPath = path
                result = getPathCommonality(
                        g=g, shortestPath=shortestPath, failedLink=e,
                        shortestPathFunction=shortestPathFunction,
                        )
                if result:
                    fn1idx, highestCommonIdx = result
                    numPreFailureNode = fn1idx + 1
                    numCommonNode = highestCommonIdx + 1
                    cumuNumPreFailureNode += numPreFailureNode
                    cumuNumCommonNode += numCommonNode
                    cumuNumDiffNode += numPreFailureNode - numCommonNode
                    count += 1
                    numPreFailureNodes.append(numPreFailureNode)
                    numCommonNodes.append(numCommonNode)
                    numDiffNodes.append(numPreFailureNode - numCommonNode)
                    pass
                pass
            pass
        pass

    numPreFailureNodes.sort()
    numCommonNodes.sort()
    numDiffNodes.sort()

    print 'count', count
    print 'numPreFailureNode: total %u, avg %f' % (cumuNumPreFailureNode, float(cumuNumPreFailureNode) / count)
    print 'numCommonNode: total %u, avg %f' % (cumuNumCommonNode, float(cumuNumCommonNode) / count)
    print 'numDiffNode: total %u, avg %f' % (cumuNumDiffNode, float(cumuNumDiffNode) / count)

    utils.genCDF(sorted(numPreFailureNodes), 'cdf_numPreFailureNodes',
                 bucketsize=1)
    utils.genCDF(sorted(numCommonNodes), 'cdf_numCommonNodes',
                 bucketsize=1)
    utils.genCDF(sorted(numDiffNodes), 'cdf_numDiffNodes',
                 bucketsize=1)

    ## assert origEdges == g.edges(data=True)
    ## assert origNodes == g.nodes()

    return


#########################
def sanityCheckValues(timeInterval, startAtTime, values):
    # "values" is a list of time2Stretch (as returned by the
    # "calculate..." functions) lists

    curtime = startAtTime

    # find the end time: the latest (largest) time among all data
    # points

    endtime = max(map(lambda time2Stretch:
                      time2Stretch[-1][0], values))
    print 'first, do some sanity checking...',
    count = len(values)
    assert endtime > curtime

    for lst in values:
        if not lst[-1][1] == 1: # must end with stretch-1
            print lst
            raise Exception()
        for i in xrange(len(lst) - 1):
            # the time must be non-negative and increasing
            if (len(lst[i]) == 2):
                assert lst[i][0] >= 0 and lst[i][0] < lst[i+1][0], \
                       'time must be non-negative and increasing'
                pass
            else:
                assert 0 <= lst[i][0] < lst[i][2] < lst[i+1][0], \
                       'time must be non-negative and increasing'
                pass
            # the stretch must be non-increasing vs time, except when
            # it's increasing from (time=0, stretch=1), i.e. the first
            # stretch2time pair.
            if i > 0:
                if (len(lst[i]) == 2):
                    assert lst[i][1] >= lst[i+1][1], '%f must be >= %f' % (lst[i][1], lst[i+1][1])
                    pass
                else:
                    assert lst[i][1] > lst[i][3] > lst[i+1][1]
                    pass
                pass
            pass
        pass
    print 'passed'
    return True

def getAvgStretchVsTime(timeInterval, startAtTime, values):
    # "values" is a list of time2Stretch (as returned by the
    # "calculate..." functions) lists

    curtime = startAtTime

    # find the end time: the latest (largest) time among all data
    # points

    endtime = max(map(lambda time2Stretch:
                      time2Stretch[-1][0], values))
    count = len(values)
    assert endtime > curtime

    # list of (time, avgStretch) tuples
    time2AvgStretch = []

    while curtime <= endtime:

        sumOfStretches = float(0)

        for time2Stretch in values:
            # this is a list like [(0.5, 1.66), (3.0, 1.33), (16.0, 1)]

            # stretch at the "curtime". the goal is to figure out what
            # the stretch was at curtime.
            curstretch = None

            # special optimization case
            if (curtime >= time2Stretch[-1][0]):
                curstretch = time2Stretch[-1][1]
                sumOfStretches += curstretch
                continue

            for i in xrange(len(time2Stretch) - 1):
                leftTime = time2Stretch[i][0]
                assert not (curtime < leftTime)
                if (len(time2Stretch[i]) == 2):
                    rightTime = time2Stretch[i+1][0]
                    if (leftTime <= curtime < rightTime):
                        # then it's left stretch
                        curstretch = time2Stretch[i][1]
                        break
                    else:
                        # check the next range
                        continue
                    pass
                else:
                    rightTime = time2Stretch[i][2]
                    # for this one we use "<=" for both comparisons
                    # because this range is inclusive.
                    if (leftTime <= curtime <= rightTime):
                        # then it's left stretch
                        left_stretch = time2Stretch[i][1]
                        right_stretch = time2Stretch[i][3]
                        slope = (float(right_stretch) - left_stretch) / \
                                (float(rightTime) - leftTime)
                        curstretch = slope*(curtime - leftTime) + left_stretch
                        break
                    else:
                        # check the next range
                        continue
                    pass
                pass
            if not curstretch:
                assert curtime >= time2Stretch[-1][0]
                curstretch = time2Stretch[-1][1]
                pass
            sumOfStretches += curstretch
            pass

        avgStretch = float(sumOfStretches) / count

        time2AvgStretch.append((curtime, avgStretch))
        curtime += timeInterval
        pass

    return time2AvgStretch

#########################
def getMaxStretchVsTime(timeInterval, startAtTime, values):
    # "values" is a list of time2Stretch (as returned by the
    # "calculate..." functions) lists

    curtime = startAtTime

    # find the end time: the latest (largest) time among all data
    # points

    endtime = max(map(lambda time2Stretch:
                      time2Stretch[-1][0], values))
    count = len(values)
    assert endtime > curtime

    # list of (time, avgStretch) tuples
    time2MaxStretch = []

    while curtime <= endtime:

        maxstretch = 0

        for time2Stretch in values:
            # this is a list like [(0.5, 1.66), (3.0, 1.33), (16.0, 1)]

            # stretch at the "curtime". the goal is to figure out what
            # the stretch was at curtime.
            curstretch = None

            # special optimization case
            if (curtime >= time2Stretch[-1][0]):
                curstretch = time2Stretch[-1][1]
                if curstretch > maxstretch:
                    maxstretch = curstretch
                    pass
                continue

            for i in xrange(len(time2Stretch) - 1):
                leftTime = time2Stretch[i][0]
                assert not (curtime < leftTime)
                if (len(time2Stretch[i]) == 2):
                    rightTime = time2Stretch[i+1][0]
                    if (leftTime <= curtime < rightTime):
                        # then it's left stretch
                        curstretch = time2Stretch[i][1]
                        break
                    else:
                        # check the next range
                        continue
                    pass
                else:
                    rightTime = time2Stretch[i][2]
                    # for this one we use "<=" for both comparisons
                    # because this range is inclusive.
                    if (leftTime <= curtime <= rightTime):
                        # then it's left stretch
                        left_stretch = time2Stretch[i][1]
                        right_stretch = time2Stretch[i][3]
                        slope = (float(right_stretch) - left_stretch) / \
                                (float(rightTime) - leftTime)
                        curstretch = slope*(curtime - leftTime) + left_stretch
                        break
                    else:
                        # check the next range
                        continue
                    pass
                pass
            if not curstretch:
                assert curtime >= time2Stretch[-1][0]
                curstretch = time2Stretch[-1][1]
                pass
            if curstretch > maxstretch:
                maxstretch = curstretch
                pass
            pass

        time2MaxStretch.append((curtime, maxstretch))
        curtime += timeInterval
        pass

    return time2MaxStretch

#########################
def getFractionWithStretch1VsTime(timeInterval, startAtTime, values):
    # "values" is a list of time2Stretch (as returned by the
    # "calculate..." functions) lists

    curtime = startAtTime

    # find the end time: the latest (largest) time among all data
    # points

    endtime = max(map(lambda time2Stretch:
                      time2Stretch[-1][0], values))
    count = len(values)
    assert endtime > curtime

    # list of (time, fraction) tuples
    time2FractionWithStretch1 = []

    while curtime <= endtime:

        countThatHaveConverged = 0

        for time2Stretch in values:
            # this is a list like [(0.5, 1.66), (3.0, 1.33), (16.0, 1)]

            # stretch at the "curtime". the goal is to figure out what
            # the stretch was at curtime.
            curstretch = None

            # special optimization case
            if (curtime >= time2Stretch[-1][0]):
                curstretch = time2Stretch[-1][1]
                assert (curstretch == 1)
                countThatHaveConverged += 1
                continue

            for i in xrange(len(time2Stretch) - 1):
                leftTime = time2Stretch[i][0]
                assert not (curtime < leftTime)
                if (len(time2Stretch[i]) == 2):
                    rightTime = time2Stretch[i+1][0]
                    if (leftTime <= curtime < rightTime):
                        # then it's left stretch
                        curstretch = time2Stretch[i][1]
                        break
                    else:
                        # check the next range
                        continue
                    pass
                else:
                    rightTime = time2Stretch[i][2]
                    # for this one we use "<=" for both comparisons
                    # because this range is inclusive.
                    if (leftTime <= curtime <= rightTime):
                        # then it's left stretch
                        left_stretch = time2Stretch[i][1]
                        right_stretch = time2Stretch[i][3]
                        slope = (float(right_stretch) - left_stretch) / \
                                (float(rightTime) - leftTime)
                        curstretch = slope*(curtime - leftTime) + left_stretch
                        break
                    else:
                        # check the next range
                        continue
                    pass
                pass
            if not curstretch:
                assert curtime >= time2Stretch[-1][0]
                curstretch = time2Stretch[-1][1]
                pass
            if (curstretch == 1):
                countThatHaveConverged += 1
                pass
            pass

        time2FractionWithStretch1.append((curtime, float(countThatHaveConverged) / count))
        curtime += timeInterval
        pass

    return time2FractionWithStretch1

#########################
def showtimevspercenthasconverged(timeInterval, startAtTime, values):
    # "values" is a list of time2Stretch (as returned by the
    # "calculate..." functions) lists

    curtime = startAtTime

    # find the end time: the latest (largest) time among all data
    # points

    endtime = max(map(lambda time2Stretch:
                      time2Stretch[-1][0], values))
    count = len(values)
    assert endtime > curtime

    for lst in values:
        for i in xrange(len(lst) - 1):
            # the time must be non-negative and increasing
            assert lst[i][0] >= 0 and lst[i][0] < lst[i+1][0], \
                   'time must be non-negative and increasing'
            # the stretch must be non-increasing vs time, except when
            # it's increasing from (time=0, stretch=1), i.e. the first
            # stretch2time pair.
            if i > 0:
                assert lst[i][1] >= lst[i+1][1], '%f must be >= %f' % (lst[i][1], lst[i+1][1])
                pass
            pass
        pass

    # list of (time, avgStretch) tuples
    time2PercentHaveConverged = []

    while curtime <= endtime:

        countThatHaveConverged = 0

        for time2Stretch in values:
            # this is a list like [(0.5, 1.66), (3.0, 1.33), (16.0, 1)]

            # stretch at the "curtime". the goal is to figure out what
            # the stretch was at curtime.
            curstretch = None
            for i in xrange(len(time2Stretch) - 1):
                leftTime = time2Stretch[i][0]
                rightTime = time2Stretch[i+1][0]
                assert not (curtime < leftTime)
                if (leftTime <= curtime < rightTime):
                    # then it's left stretch
                    curstretch = time2Stretch[i][1]
                    break
                else:
                    # check the next range
                    continue
                pass
            if not curstretch:
                assert curtime >= time2Stretch[-1][0]
                curstretch = time2Stretch[-1][1]
                pass
            if curstretch == 1:
                countThatHaveConverged += 1
                pass
            pass

        percent = float(countThatHaveConverged) / count

        time2PercentHaveConverged.append((curtime, percent))
        curtime += timeInterval
        pass

    return time2PercentHaveConverged

def cmd_processdata(argv):
    assert argv[0] == 'processdata'

    def usageAndExit(progname):
        print '''
Usage: %s property -i ... [-s ...] <resultPickleFile>

         -i: time interval/step to use

         -s: the start time in the plot
''' % (progname)
        sys.exit(-1)
        return
    ####

    if len(argv) < 3:
        usageAndExit(argv[0])
        return

    prop = argv[1]

    prop2func = {'avgStretch': getAvgStretchVsTime,
                 'maxStretch': getMaxStretchVsTime,
                 'fractionWithStretch1': getFractionWithStretch1VsTime,
                 }
    if not prop in prop2func:
        usageAndExit(argv[0])
        return

    timeInterval = None
    startAtTime = 0
    opts, args = getopt.getopt(argv[2:], 'i:s:',
                               [])

    ## parse options
    for o, a in opts:
        if o == '-i':
            timeInterval = float(a)
            assert timeInterval > 0
            pass
        elif o == '-s':
            startAtTime = float(a)
            assert startAtTime >= 0
            pass
        pass

    assert timeInterval

    # this is used to be as sure as possible that all the pickle files
    # are from the same eval
    evalProperties = None

    # gather all the results from all the pickle files here, then
    # we'll process afterwards.
    schemesToResults = {}

    for i, filename in enumerate(args):
        evalResult = utils.unpickleStuff(filename)

        if i == 0:
            evalProperties = [
                evalResult.graphFile, evalResult.weighted,
                sorted(evalResult.schemeToResult.keys()),
                evalResult.revision, evalResult.utilsRevision,
                ]
            pass
        else:
            assert evalProperties == [
                evalResult.graphFile, evalResult.weighted,
                sorted(evalResult.schemeToResult.keys()),
                evalResult.revision, evalResult.utilsRevision,
                ]
            pass

        # TODO? make sure the revisions of the obj match ours
        for schemeName, time2Stretch in evalResult.schemeToResult.iteritems():
            if i == 0:
                schemesToResults[schemeName] = time2Stretch
                pass
            else:
                schemesToResults[schemeName].extend(time2Stretch)
                pass
            pass

        del evalResult

        pass

    func = prop2func[prop]
    for schemeName, time2Stretch in schemesToResults.iteritems():
        assert sanityCheckValues(timeInterval, startAtTime, time2Stretch) == True
        time2value = func(timeInterval, startAtTime, time2Stretch)
        f = open(prop + '_' + schemeName, 'w')
        for time, value in time2value:
            f.write('%f  %f\n' % (time, value))
            pass
        f.close()
        pass

    return

def cmd_processdataTextFormat(argv):
    assert argv[0] == 'processdataTextFormat'

    def usageAndExit(progname):
        print '''
Usage: %s property -i ... [-s ...] <dirWithResultFiles>

         -i: time interval/step to use

         -s: the start time in the plot
''' % (progname)
        sys.exit(-1)
        return
    ####

    if len(argv) < 3:
        usageAndExit(argv[0])
        return

    prop = argv[1]

    prop2func = {'avgStretch': getAvgStretchVsTime,
                 'maxStretch': getMaxStretchVsTime,
                 'fractionWithStretch1': getFractionWithStretch1VsTime,
                 }
    if not prop in prop2func:
        usageAndExit(argv[0])
        return

    timeInterval = None
    startAtTime = 0
    opts, args = getopt.getopt(argv[2:], 'i:s:',
                               [])

    ## parse options
    for o, a in opts:
        if o == '-i':
            timeInterval = float(a)
            assert timeInterval > 0
            pass
        elif o == '-s':
            startAtTime = float(a)
            assert startAtTime >= 0
            pass
        pass

    assert timeInterval

    # this is used to be as sure as possible that all the pickle files
    # are from the same eval
    evalProperties = None

    # gather all the results from all the pickle files here, then
    # we'll process afterwards.
    schemesToResults = {}

    dirpath = args[0]

    for filename in os.listdir(dirpath):
        assert not (filename in schemesToResults)
        results = []

        print 'processing file', filename
        filepath = dirpath + '/' + filename
        f = open(filepath)
        for line in f:
            if line[0] == '#':
                # skip comments
                continue
            # has format "time2stretch[|time2stretch[|...]]  where
            # "time2stretch" could be 2-tuple "time,stretch" form or
            # 4-tuple "time,stretch,time,stretch" form.
            time2Stretch_list = line.strip().split('|')
            resultForOnePair = []
            for time2stretch in time2Stretch_list:
                parts = time2stretch.split(',')
                assert (len(parts) == 2 or len(parts) == 4)
                resultForOnePair.append(tuple(map(float, parts)))
                pass
            results.append(resultForOnePair)
            pass
        f.close()
        schemesToResults[filename] = results
        pass

    func = prop2func[prop]
    for schemeName, time2Stretch in schemesToResults.iteritems():
        assert sanityCheckValues(timeInterval, startAtTime, time2Stretch) == True
        time2value = func(timeInterval, startAtTime, time2Stretch)
        f = open(prop + '_' + schemeName, 'w')
        for time, value in time2value:
            f.write('%f  %f\n' % (time, value))
            pass
        f.close()
        pass

    pass

def cmd_showtimevspercenthasconverged(argv):
    assert argv[0] == 'showtimevspercenthasconverged'

    def usageAndExit(progname):
        print '''
Usage: %s -i ... [-s ...] <resultPickleFile>

         -i: time interval/step to use

         -s: the start time in the plot
''' % (progname)
        sys.exit(-1)
        return
    ####

    if len(argv) < 2:
        usageAndExit(argv[0])
        return

    timeInterval = None
    startAtTime = 0
    opts, args = getopt.getopt(argv[1:], 'i:s:',
                               [])

    ## parse options
    for o, a in opts:
        if o == '-i':
            timeInterval = float(a)
            assert timeInterval > 0
            pass
        elif o == '-s':
            startAtTime = float(a)
            assert startAtTime >= 0
            pass
        pass

    assert timeInterval

    filename = args[0]

    evalResult = utils.unpickleStuff(filename)

    # TODO? make sure the revisions of the obj match ours
    for schemeName, time2Stretch in evalResult.schemeToResult.iteritems():
        time2PercentHaveConverged = showtimevspercenthasconverged(timeInterval, startAtTime, time2Stretch)
        f = open(schemeName, 'w')
        for time, percent in time2PercentHaveConverged:
            f.write('%f  %f\n' % (time, percent))
            pass
        f.close()
        pass

    return

####################

cmds = {
    'runeval' : cmd_runeval,
    'processdata' : cmd_processdata,
    'processdataTextFormat' : cmd_processdataTextFormat,
    'showtimevspercenthasconverged' : cmd_showtimevspercenthasconverged,
    'getpathcommonality': cmd_getpathcommonality,
    }

if __name__ == '__main__':
    if len(sys.argv) < 2:
        print 'Usage: %s cmd [cmd options]' % (sys.argv[0])
        print '        possible cmds are: ' + ', '.join(cmds.keys())
        sys.exit(0)
        pass
    cmdname = sys.argv[1]
    cmdfunc = cmds.get(cmdname, None)
    if cmdfunc:
        cmdfunc(sys.argv[1:])
        pass
    else:
        print 'cmd must be one of the following:\n' + '\n'.join(cmds.keys())
        sys.exit(0)
        pass
    pass
