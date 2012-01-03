# copied from eval3, but this is to compare our DAGs size (num node
# and num edge) against the lower/upper bounds from Rachit's formulae.


'''
uses approach2 (primary-path-then-detour-paths one), with vnodes, all
ptr sizes inside pkt are same, ptrs are absolute (no topological
sort).

use this same module to run the eval and then process data.

the eval will keep track of result (graph size, header size, etc) for
each pair (s,d), and at the end will pickle ALL the pairs.

first intended use of this is to generate CDF. one might say, why not
generating the CDF during the eval and avoid pickling. well, we migth
later want to generate other statistics.

'''

import os, struct
import utils, approach2
import time
import cPickle
import math
import copy
#import pdb
import networkx as nx

Revision = '$Revision: 318 $'
Id = '$Id$'


# only support these offsetPtrAlignments
offsetPtrAlignments = (1, 4, 8) # in bits


class SrcDstPairResult3:
    def __init__(self, lowerBound, upperBound, numEdges):
        # "numEdges" is of the actual graph, while the two "bounds"
        # are from Rachit's formulae
        self.lowerBound = lowerBound
        self.upperBound = upperBound
        self.numEdges = numEdges
        return
    pass

class FileResult3:
    def __init__(self, filename,
                 startdateSecs, enddateSecs,
                 srcDstPairResults3):
        self.filename = filename
        self.startdateSecs = startdateSecs
        self.enddateSecs = enddateSecs
        self.srcDstPairResults3 = srcDstPairResults3
        return
    pass

class EvalResult3:
    '''
    "pairIsOrdered": True: (a,b) same as (b,a), which means that once
    (a,b) has been encountered, the evaluation will skip (b,a). If
    False, then it will evaluate (b,a).

    "fileResults3" is list of FileResult3 objects.
    '''
    def __init__(self, numberOfPairsToTry, pairIsOrdered,
                 startdateSecs, enddateSecs, fileResults3,
                 revision, utilsRevision, approach2Revision, weighted):

        self.numberOfPairsToTry = numberOfPairsToTry
        self.pairIsOrdered = pairIsOrdered
        self.startdateSecs = startdateSecs
        self.enddateSecs = enddateSecs
        self.fileResults3 = fileResults3

        self.revision = revision
        self.utilsRevision = utilsRevision
        self.approach2Revision = approach2Revision

        self.weighted = weighted
        return

    pass



def evalOneFile(filename, numberOfPairsToTry, pairIsOrdered=False,
                weighted=False):
    startdateSecs = int(time.time())
    print '''
    _______________________________________________
    filename: [%s]
    start date: [%s]
    ''' % (filename, time.ctime(startdateSecs))
    g, lli = utils.textToG(filename, useInt=False, ignoreWeights=False)
    allNodes = g.nodes()
    numNodes = len(allNodes)
    i = 0

    srcDstPairResults3 = {}

    if numberOfPairsToTry > 0:
        while i < numberOfPairsToTry:
            # this is crypto random integer
            idx1 = (struct.unpack('I', os.urandom(4))[0]) % numNodes
            idx2 = (struct.unpack('I', os.urandom(4))[0]) % numNodes

            while idx2 == idx1:
                idx2 = (struct.unpack('I', os.urandom(4))[0]) % numNodes
                pass

            # yes, i do want to increment i here because maybe the graph
            # is too small, then the total number of possible pairs is too
            # small, and we will never be able to reach the
            # numberOfPairsToTry
#            i += 1

            s,d = allNodes[idx1], allNodes[idx2]
            if (s,d) in srcDstPairResults3:
                # definitely skip
                print 'pair (%s,%s) already encountered -> skip' % (s,d)
                continue
            elif (d,s) in srcDstPairResults3:
                # not seen (s,d) yet but seen (d,s), should skip or not?
                if not pairIsOrdered:
                    print 'pairs are not ordered, and (%s,%s) already encountered -> skip' % (d,s)
                    continue
                pass

            # do this so we know we have seen this (s, d) pair
            srcDstPairResults3[(s, d)] = None # init to None (which will
                # mean disconnected)

            print 's,d="%s","%s"' % (s,d)

            i += 1
            pass # end while i < numberOfPairsToTry
        pass # end if numberOfPairsToTry > 0
    else:
        # numberOfPairsToTry is <= 0, so we do all (un-ordered)
        # pairs. the graph'd better be not too big.
        for i in range(numNodes - 1):
            for j in range(i + 1, numNodes):
                s = allNodes[i]
                d = allNodes[j]
                print 's,d="%s","%s"' % (s,d)
                srcDstPairResults3[(s, d)] = None # init to None (which will
                # mean disconnected)
                pass
            pass
        pass

    ###########################
    # now that we have the pairs we want to eval, eval them

    def computeBounds(g, s, d, primaryPath, M, pathFunction):
        # M is largest weight divided by smallest weight

        numPnodes = len(primaryPath)
        numPedges = numPnodes - 1
        if weighted:
            lowerBound = (2 * numPedges) + 1
            pass
        else:
            if (numPedges % 2) == 0:
                # even
                lowerBound = 2.5 * numPedges
                pass
            else:
                # odd
                lowerBound = (2.5 * numPedges) + 0.5
                pass
            pass

        ### upperbound is more involved
        upperBound = None

        savedEdgesData = {}
        # remove edges in ppath
        for i in xrange(numPnodes - 1):
            savedEdgesData[(primaryPath[i], primaryPath[i + 1])] = \
                copy.copy(g.edge[primaryPath[i]][primaryPath[i + 1]])
            g.remove_edge(primaryPath[i], primaryPath[i + 1])
            pass
        primaryPathPrime = None
        try:
            primaryPathPrime = pathFunction(g, s, d)
            pass
        except nx.exception.NetworkXError, exc:
            # no path
            pass
        # add back the removed edges
        for i in xrange(numPnodes - 1):
            g.add_edge(primaryPath[i], primaryPath[i + 1],
                       attr_dict=savedEdgesData[(primaryPath[i], primaryPath[i + 1])])
            pass
        if primaryPathPrime:
            numPPrimeEdges = len(primaryPathPrime) - 1
            upperBound = (numPedges * ((M * numPedges) - M + (2 * numPPrimeEdges) + 2)) / 2
            pass
        return lowerBound, upperBound
    #####

    if weighted:
        pathFunction = nx.dijkstra_path
        pass
    else:
        pathFunction = nx.shortest_path
        pass

    weights = map(lambda (u, v, edgeData): edgeData['weight'],
                  g.edges(data=True))
    maxWeight = max(weights)
    minWeight = min(weights)
    assert minWeight > 0
    M = float(maxWeight) / float(minWeight)

    for s, d in srcDstPairResults3.keys():
        #### use approach2
        pp, dp = approach2.getDg(g, s, d, weighted)
        if (not pp) or (not dp):
            print 'no path: s,d="%s","%s"' % (s,d)
            continue

        dag = approach2.getDagWithVnodes(pp, dp)

        lowerBound, upperBound = computeBounds(g, s, d, pp, M, pathFunction)

        srcDstPairResults3[(s, d)] = SrcDstPairResult3(
            lowerBound, upperBound, dag.number_of_edges())

        pass # end while loop

    enddateSecs = int(time.time())

    fileResult3 = FileResult3(filename, startdateSecs, enddateSecs,
                              srcDstPairResults3)

    return fileResult3




def cmd_runeval(argv):
    assert argv[0] == 'runeval'
    if len(argv) < 3:
        print 'usage: %s [--weighted] <number of pairs> <graph file path> [<graph file path> ...]' % (argv[0])
        print '        <number of pairs> can be <= 0 to mean: all possible non-ordered pairs (the graph should not be too big).'
        sys.exit(-1)
        pass

    startdateSecs = int(time.time())
    print "start date: [%s]" % (time.ctime())
    print "eval3.Revision:     [%s]" % (Revision)
    print "utils.Revision:     [%s]" % (utils.Revision)
    print "approach2.Revision: [%s]" % (approach2.Revision)

    weighted = False
    argvidx = 1
    if argv[argvidx] == '--weighted':
        weighted = True
        argvidx += 1
        pass
    numberOfPairsToTry = int(argv[argvidx])
    argvidx += 1
    print 'number of pairs to try: [%d]\n' % numberOfPairsToTry

    fileResults3 = []
    for filename in argv[argvidx:]:
        fileResult3 = evalOneFile(
            filename, numberOfPairsToTry=numberOfPairsToTry,
            pairIsOrdered=False, weighted=weighted)
        fileResults3.append(fileResult3)
        pass

    enddateSecs = int(time.time())

    evalResult3 = EvalResult3(
        numberOfPairsToTry, False,
        startdateSecs, enddateSecs, fileResults3,
        revision=Revision, utilsRevision=utils.Revision,
        approach2Revision=approach2.Revision,
        weighted=weighted)

    pickleFilename = 'evalBoundResults.pickle_%s' % \
                     (time.strftime('%m%d%y_%H%M%S',
                                    time.localtime(startdateSecs)))
    utils.pickleStuff(pickleFilename, evalResult3)

    pass



####################################################################

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

def cmd_gencdf(argv):
    def usage(cmdname):
        print 'usage: %s <whichvalue> [--bucket-size ...] <graph file path> [<graph file path> ...]' % (cmdname)
        print '         --bucket-size integer: instead of outputting individual data points, put them into buckets of the specified size. each bucket is represented by its upperbound. this reduces the number of data points in output.'
        return
    ####

    argvidx = 0
    cmdname = argv[argvidx]
    assert cmdname == 'gencdf'
    if len(argv) < 3:
        usage(cmdname)
        sys.exit(-1)
        pass
    argvidx += 1
    ###

    whichvalue = argv[argvidx]
    knownvalues = ['values', 'diffs']
    print whichvalue
    if not whichvalue in knownvalues:
        print '<whichvalue> must be one of the following:\n' + '\n'.join(knownvalues)
        sys.exit(-1)
        pass
    argvidx += 1
    ###

    bucketsize = None
    if argv[argvidx] == '--bucket-size':
        bucketsize = int(argv[argvidx + 1])
        assert bucketsize > 0
        argvidx += 2
        pass
    ###

    filenames = argv[argvidx:]

    if whichvalue == 'values':
        lowerBounds = []
        upperBounds = []
        actualSizes = []
        pass
    elif whichvalue == 'diffs':
        diffsWithLowerBounds = []
        diffsWithUpperBounds = []
        pass

    for filename in filenames:
        evalResult3 = utils.unpickleStuff(filename)

        # make sure the revisions of the obj match ours

        for fileResult3 in evalResult3.fileResults3:
            for srcDstPairResult3 in fileResult3.srcDstPairResults3.values():
                if srcDstPairResult3 is None:
                    # might be None if the (s,d) pair was disconnected
                    continue
                if whichvalue == 'values':
                    lowerBounds.append(srcDstPairResult3.lowerBound)
                    if srcDstPairResult3.upperBound != None:
                        upperBounds.append(srcDstPairResult3.upperBound)
                        pass
                    actualSizes.append(srcDstPairResult3.numEdges)
                    pass
                elif whichvalue == 'diffs':
                    diffsWithLowerBounds.append(srcDstPairResult3.numEdges - srcDstPairResult3.lowerBound)
                    if srcDstPairResult3.upperBound != None:
                        diffsWithUpperBounds.append(srcDstPairResult3.upperBound - srcDstPairResult3.numEdges)
                        pass
                    pass
                pass
            pass
        pass

    # finished gathering the data

    if whichvalue == 'values':
        genCDF(sorted(lowerBounds), 'cdflowerbounds', bucketsize=bucketsize)
        genCDF(sorted(upperBounds), 'cdfupperbounds', bucketsize=bucketsize)
        genCDF(sorted(actualSizes), 'cdfactualsizes', bucketsize=bucketsize)
        pass
    elif whichvalue == 'diffs':
        genCDF(sorted(diffsWithLowerBounds), 'cdfdiffswithlowerbounds', bucketsize=bucketsize)
        genCDF(sorted(diffsWithUpperBounds), 'cdfdiffswithupperbounds', bucketsize=bucketsize)
        pass

    return


cmds = {
    'runeval' : cmd_runeval,
    'gencdf' : cmd_gencdf,
    }

if __name__ == '__main__':
    import sys
    if len(sys.argv) < 2:
        print 'Usage: %s cmd [cmd options]' % (sys.argv[0])
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
