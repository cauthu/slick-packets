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
import igraph
import utils

Id = '$Id$'
Revision = '$Revision: 575 $'

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
def calculateForFastDAG_wrapper(g, shortestPath, failedLink,
                                shortestPathLengthFunction,
                                singleSourceShortestPathLengthFunction,
                                processingDelay,
                                passThruDelay, timeOfFailure,
                                ):
    return calculateForDAG(
        g=g, shortestPath=shortestPath,
        failedLink=failedLink,
        mode='fast',
        shortestPathLengthFunction=shortestPathLengthFunction,
        singleSourceShortestPathLengthFunction=singleSourceShortestPathLengthFunction,
        processingDelay=processingDelay,
        passThruDelay=passThruDelay,
        timeOfFailure=timeOfFailure,
        )

def calculateForSlowDAG_wrapper(g, shortestPath, failedLink,
                                shortestPathLengthFunction,
                                singleSourceShortestPathLengthFunction,
                                processingDelay,
                                passThruDelay, timeOfFailure,
                                ):
    return calculateForDAG(
        g=g, shortestPath=shortestPath,
        failedLink=failedLink,
        mode='slow',
        shortestPathLengthFunction=shortestPathLengthFunction,
        singleSourceShortestPathLengthFunction=singleSourceShortestPathLengthFunction,
        processingDelay=processingDelay,
        passThruDelay=passThruDelay,
        timeOfFailure=timeOfFailure,
        )

def calculateForFloodedDAG_wrapper(g, shortestPath, failedLink,
                                   shortestPathLengthFunction,
                                   singleSourceShortestPathLengthFunction,
                                   processingDelay,
                                   passThruDelay, timeOfFailure,
                                   ):
    return calculateForDAG(
        g=g, shortestPath=shortestPath,
        failedLink=failedLink,
        mode='flooded',
        shortestPathLengthFunction=shortestPathLengthFunction,
        singleSourceShortestPathLengthFunction=singleSourceShortestPathLengthFunction,
        processingDelay=processingDelay,
        passThruDelay=passThruDelay,
        timeOfFailure=timeOfFailure,
        )

def calculateForDAG(g, shortestPath, failedLink,
                    mode,
                    shortestPathLengthFunction,
                    singleSourceShortestPathLengthFunction,
                    processingDelay,
                    passThruDelay, timeOfFailure,
                    ):
    # "shortestPath" should be that returned by networkx's path
    # algorithms, as in [0] is the source, [-1] is the destination.

    # "mode": must be one of "flooded", "fast", and "slow".

    # "routerNotifiesSource": True to have the router adjacent notify
    # the source of failure. False to have it only mark the packet on
    # its way to the destination, which then notifies the source,
    # which takes longer for source to be notified.

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

    # now find out when the source gets the news of the link
    # failure. assume zero processing/congestion/etc delay at
    # nodes, ie, only link latencies (distance) determine how fast
    # the update travel.

    savedEdgeAttr = removeEdge(g, fn1, fn2)

    shortestLengthWithFailure = None
    try:
        shortestLengthWithFailure = shortestPathLengthFunction(g, s, d)
        pass
    except:
        pass

    if not shortestLengthWithFailure:
        # restore edge
        addEdge(g, fn1, fn2, savedEdgeAttr)
        return None

    ssspl_fn1 = singleSourceShortestPathLengthFunction(g, fn1)
    distFromSToFn1 = ssspl_fn1[s]
    distFromFn1ToD = ssspl_fn1[d]
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
                        (shortestPath, failedLink, packetSentTime2Stretch))

    # restore edge
    addEdge(g, fn1, fn2, savedEdgeAttr)

    return packetSentTime2Stretch

##########################################################
def calculateForVSR(g, shortestPath, failedLink,
                    shortestPathLengthFunction,
                    singleSourceShortestPathLengthFunction,
                    processingDelay,
                    passThruDelay, timeOfFailure,
                    ):
    # "shortestPath" should be that returned by networkx's path
    # algorithms, as in [0] is the source, [-1] is the destination.

    # "routerNotifiesSource": True to have the router adjacent notify
    # the source of failure.

    routerNotifiesSource = True
    assert routerNotifiesSource, 'only True is implemented'

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

    savedEdgeAttr = removeEdge(g, fn1, fn2)

    shortestLengthWithFailure = None
    try:
        shortestLengthWithFailure = shortestPathLengthFunction(g, s, d)
        pass
    except:
        pass

    if not shortestLengthWithFailure:
        # restore edge
        addEdge(g, fn1, fn2, savedEdgeAttr)
        return None

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
        # restore edge
        addEdge(g, fn1, fn2, savedEdgeAttr)
        return [(min(0, timeOfFailure), 1)]


    #
    #
    # after here, we have s != fn1 (which means there are
    # dropped/resent packets) AND/OR processingDelay > 0 (which means
    # there are delayed--by the source--packets)
    #
    #

    ssspl_fn1 = singleSourceShortestPathLengthFunction(g, fn1)
    distFromSToFn1 = ssspl_fn1[s]
    distFromFn1ToD = ssspl_fn1[d]

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
        stop = int(math.ceil(t_tx_lastResent))
        for t_tx in xrange(start, stop, 1):
            stretch = stretch_firstResent - \
                      (float(t_tx - t_tx_firstResent) / \
                       shortestLengthWithFailure)
            packetSentTime2Stretch.append((t_tx, stretch))
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
        stop = int(math.ceil(t_tx_lastDelayed))
        for t_tx in xrange(start, stop, 1):
            stretch = stretch_firstDelayed - \
                      (float(t_tx - t_tx_firstDelayed) / \
                       shortestLengthWithFailure)
            packetSentTime2Stretch.append((t_tx, stretch))
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
                        (shortestPath, failedLink, packetSentTime2Stretch))

    # restore edge
    addEdge(g, fn1, fn2, savedEdgeAttr)

    return packetSentTime2Stretch

def removeEdge(g, u, v):
#    print 'before removing (%s,%s)...' % (u,v), g.ecount()
    eid = g.get_eid(u, v)
    savedEdgeAttrs = g.es[eid].attributes().copy()
    g.delete_edges([(u,v), (v,u)])
    return savedEdgeAttrs

def addEdge(g, u, v, edgeAttrs={}):
#    print 'before adding (%s,%s)...' % (u,v), g.ecount()
    g.add_edges([(u,v), (v,u)])
    if len(edgeAttrs):
        for eid in (g.get_eid(u, v), g.get_eid(v, u)):
            for k,v in edgeAttrs.iteritems():
                g.es[eid][k] = v
                pass
            pass
        pass
    return

def igraph_unweightedSinglePairShortestPathLengthFunc(g, s, t):
    lengths = g.shortest_paths(s, weights=None, mode=igraph.ALL)[0]
    if lengths[t] == float('inf'):
        return None
    return lengths[t]

def igraph_unweightedSingleSourceShortestPathLengthFunc(g, s):
    lengths = g.shortest_paths(s, weights=None, mode=igraph.ALL)[0]
    return lengths

def igraph_weightedSinglePairShortestPathLengthFunc(g, s, t):
    lengths = g.shortest_paths(s, weights='weight', mode=igraph.ALL)[0]
    if lengths[t] == float('inf'):
        return None
    return lengths[t]

def igraph_weightedSingleSourceShortestPathLengthFunc(g, s):
    lengths = g.shortest_paths(s, weights='weight', mode=igraph.ALL)[0]
    return lengths

def igraph_weightedSingleSourceShortestPathFunc(g, s):
    shortestPathList = g.get_shortest_paths(s, weights='weight',mode=igraph.ALL)
    del shortestPathList[s]
    return shortestPathList

def igraph_unweightedSingleSourceShortestPathFunc(g, s):
    shortestPathList = g.get_shortest_paths(s, weights=None, mode=igraph.ALL)
    del shortestPathList[s]
    return shortestPathList

##########################################################
def calculateForSafeGuard(g, shortestPath, failedLink,
                          shortestPathLengthFunction,
                          singleSourceShortestPathLengthFunction,
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
    if shortestPath.index(failedLink[0]) < shortestPath.index(failedLink[1]):
        fn1 = failedLink[0]
        fn2 = failedLink[1]
        pass
    else:
        fn1 = failedLink[1]
        fn2 = failedLink[0]
        pass


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

    savedEdgeAttr = removeEdge(g, fn1, fn2)

    shortestLengthWithFailure = None
    try:
        shortestLengthWithFailure = shortestPathLengthFunction(g, s, d)
        pass
    except nx.exception.NetworkXError:
        pass

    if not shortestLengthWithFailure:
        # restore edge
        addEdge(g, fn1, fn2, savedEdgeAttr)
        return None

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

        ssspl_r = singleSourceShortestPathLengthFunction(g,r)

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
                    stop = int(math.ceil(packetSentTime2Stretch[1][0]))
                    for t_tx in xrange(start, stop, 1):
                        # packetSentTime2Stretch[-1] is always the
                        # first packet that that arrives after the
                        # processingDelay has elapsed, i.e., it is NOT
                        # buffered. call it p_nb. a packet p that is
                        # sent X amount of time before p_nb is sent
                        # will take X amount of time longer to reach
                        # destination compared to p_nb, so the stretch
                        # of p can be computed from the stretch of
                        # p_nb.
                        stretch = packetSentTime2Stretch[-1][1] + \
                                  float(packetSentTime2Stretch[-1][0] - t_tx) / \
                                  shortestLengthWithFailure
                        packetSentTime2Stretch.insert(-1, (t_tx, stretch))
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
                        (shortestPath, failedLink, packetSentTime2Stretch))

    # restore edge
    addEdge(g, fn1, fn2, savedEdgeAttr)

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

    savedEdgeAttr = removeEdge(g, fn1, fn2)

    shortestPathWithFailure = None
    try:
        shortestPathWithFailure = shortestPathFunction(g, s, d)
        pass
    except nx.exception.NetworkXError:
        pass

    if not shortestPathWithFailure:
        # restore edge
        addEdge(g, fn1, fn2, savedEdgeAttr)
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
    addEdge(g, fn1, fn2, savedEdgeAttr)

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

# "singleSourceShortestPathFunc" must take exactly 2 args: the graph
# and the source. it must return a list of shortest paths to all OTHER
# nodes in the graph. each of shortest paths must be a list of nodes
# that starts at the source and ends at the destination.
def getEdgesAndPaths(g, src, singleSourceShortestPathFunc,
                     edgeSampleSize, edgerandomObj,
                     dstSampleSize, dstrandomObj):
    # get all shortest paths
    shortestPaths = singleSourceShortestPathFunc(g, src)
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
        singleSourceShortestPathFunction = igraph_weightedSingleSourceShortestPathFunc
        singleSourceShortestPathLengthFunction = igraph_weightedSingleSourceShortestPathLengthFunc
        shortestPathLengthFunction = igraph_weightedSinglePairShortestPathLengthFunc
        pass
    else:
        singleSourceShortestPathFunction = igraph_unweightedSingleSourceShortestPathFunc
        singleSourceShortestPathLengthFunction = igraph_unweightedSingleSourceShortestPathLengthFunc
        shortestPathLengthFunction = igraph_unweightedSinglePairShortestPathLengthFunc
        pass

    graphFile = args[0]
    g = igraph.load(graphFile, format='ncol', weights=weighted)
    ## for e in g.es:
    ##     try:
    ##         while True:
    ##             reverse_eid = g.get_eid(e.target, e.source)
    ##             g.delete_edges(reverse_eid)
    ##             pass
    ##         pass
    ##     except:
    ##         pass
    ##     pass
    allNodes = tuple(sorted(map(lambda vobj: vobj.index, g.vs)))

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
        'VSR': [],
        }

    schemeToCalcFunc = (
        (schemeToResult['Flooded-DAG'], calculateForFloodedDAG_wrapper),
        (schemeToResult['Fast-DAG'], calculateForFastDAG_wrapper),
        (schemeToResult['Slow-DAG'], calculateForSlowDAG_wrapper),
        (schemeToResult['SafeGuard'], calculateForSafeGuard),
        (schemeToResult['VSR'], calculateForVSR),
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
            for path in paths:
                shortestPath = path
                for scmResults, scmCalcFunc in schemeToCalcFunc:
                    result = scmCalcFunc(
                        g=g, shortestPath=shortestPath, failedLink=e,
                        shortestPathLengthFunction=shortestPathLengthFunction,
                        singleSourceShortestPathLengthFunction=singleSourceShortestPathLengthFunction,
                        processingDelay=processingDelay,
                        passThruDelay=passThruDelay,
                        timeOfFailure=timeOfFailure,
                        )
                    if result:
                        scmResults.append(result)
                        pass
                    pass
                pass
            pass
        pass

    ## assert origEdges == g.edges(data=True)
    ## assert origNodes == g.nodes()

    enddateSecs = int(time.time())

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

    pickleFilename = 'evalStretchVsTimeResult.pickle_%s' % \
                     (time.strftime('%m%d%y_%H%M%S',
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
def process(timeInterval, startAtTime, values):
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
        if not lst[-1][1] == 1: # must end with stretch-1
            print lst
            raise Exception()
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
    time2AvgStretch = []

    while curtime <= endtime:

        sumOfStretches = float(0)

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
            sumOfStretches += curstretch
            pass

        avgStretch = float(sumOfStretches) / count

        time2AvgStretch.append((curtime, avgStretch))
        curtime += timeInterval
        pass

    return time2AvgStretch

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

    for schemeName, time2Stretch in schemesToResults.iteritems():
        time2AvgStretch = process(timeInterval, startAtTime, time2Stretch)
        f = open(schemeName, 'w')
        for time, avgStretch in time2AvgStretch:
            f.write('%f  %f\n' % (time, avgStretch))
            pass
        f.close()
        pass

    return

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
