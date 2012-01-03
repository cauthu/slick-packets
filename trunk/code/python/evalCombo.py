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
import getopt
import pdb
import random
import copy
import networkx as nx
import codec2
import codec3
import codec4
import inspect

Revision = '$Revision: 1060 $'
Id = '$Id$'

stretches = (1, )

class PartialResult:
    def __init__(self, filename,
                 startdateSecs, enddateSecs,
                 codec2HdrLen_stretchToCounts,
                 codec4HdrLen_stretchToCounts,
                 singlePath_encodingLen_counts,
                 dagSize_stretchToCounts,
                 pairsWithLargeCodec4Encodings,
                 lowerBoundCounts,
                 pairsWithDagSizeSmallerThanLowerBound,
                 argv, seed, weighted):
        self.revision = Revision
        self.utilsRevision = utils.Revision
        self.approach2Revision = approach2.Revision
        self.codec2Revision = codec2.Revision
        self.codec4Revision = codec4.Revision
        self.argv = argv
        self.seed = seed
        self.weighted = weighted

        self.filename = filename
        self.startdateSecs = startdateSecs
        self.enddateSecs = enddateSecs
        self.codec2HdrLen_stretchToCounts = codec2HdrLen_stretchToCounts
        self.codec4HdrLen_stretchToCounts = codec4HdrLen_stretchToCounts
        # singlePath_encodingLen is based off codec 4 (no pointers,
        # simply all the link labels in sequence. link label length
        # being log of node degree)
        self.singlePath_encodingLen_counts = singlePath_encodingLen_counts
        self.dagSize_stretchToCounts = dagSize_stretchToCounts
        self.lowerBoundCounts = lowerBoundCounts
        self.pairsWithLargeCodec4Encodings = pairsWithLargeCodec4Encodings
        self.pairsWithDagSizeSmallerThanLowerBound = \
            pairsWithDagSizeSmallerThanLowerBound
        return
    pass


def computeBounds(g, s, d, primaryPath, M, weighted):
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
    return lowerBound

def getDgWithStretch(g, s, d, weighted, stretch):
    # "weighted": whether the GRAPH is intended to be weighted

    return approach2.getDg(g, s, d, weighted=weighted)
#####

def evalOneFile(filename, headerLengthThreshold,
                numberOfPairsToTry, pairIsOrdered,
                partialResultSize, outputDir,
                argv,
                weighted, seed=None,
                srcStartIdx=None, srcEndIdx=None,
                ):

    def addValueCount(countsDict, value):
        if value in countsDict:
            countsDict[value] += 1
            pass
        else:
            countsDict[value] = 1
            pass
        return
    #####

    def evalOnePair(g, lli, localLinkLabelLens, s, d,
                    lowerBoundCounts,
                    dagSize_stretchToCounts,
                    pairsWithDagSizeSmallerThanLowerBound,
                    codec2HdrLen_stretchToCounts,
                    codec4HdrLen_stretchToCounts,
                    singlePath_encodingLen_counts,
                    pairsWithLargeCodec4Encodings,
                    M):
        lowerBound = None
        for stretch in stretches:
            pp, dp = getDgWithStretch(g, s, d, weighted, stretch)
            if (not pp):
                print 'no path: s,d="%s","%s"' % (s,d)
                return
            if dp == None:
                dp = {}
                pass

            dag, virtualDetourPaths = approach2.getDagWithVnodes(
                pp, dp, returnDetourPathsWithVNodes=True)
            try:
                # in bits
                codec2HdrLen = codec2.encode(
                    dag, pp, virtualDetourPaths, lli, False, s, d,
                    useLinkIdLenPrefix=False,
                    localLinkLabelLens=localLinkLabelLens,
                    returnActualEncoding=False,
                    roundUpToMultipleBits=1)[0]
                pass
            except Exception, e:
                print 'WARNING: pair s=%s,d=%s is problematic\n' %(s,d)
                print str(e)
                return
            # convert to bytes
            codec2HdrLen = int(math.ceil(float(codec2HdrLen)/8))
            addValueCount(codec2HdrLen_stretchToCounts[stretch], codec2HdrLen)

            # in bits
            codec4HdrLen = codec4.encode(
                pp, dp, lli, localLinkLabelLens, s, d, roundUpToMultipleBits=1,
                returnActualEncoding=False)
            # convert to bytes
            codec4HdrLen = int(math.ceil(float(codec4HdrLen)/8))
            addValueCount(codec4HdrLen_stretchToCounts[stretch], codec4HdrLen)

            # just sum up the all the link label lengths
            singlePath_encodingLen = sum(map(lambda n: localLinkLabelLens[n], pp[:-1]))
            # get number of bytes from number of bits
            singlePath_encodingLen = int(math.ceil(float(singlePath_encodingLen)/8))
            addValueCount(singlePath_encodingLen_counts, singlePath_encodingLen)

            dagSize = dag.number_of_edges()
            addValueCount(dagSize_stretchToCounts[stretch], dagSize)

            if codec4HdrLen > headerLengthThreshold:
                pairsWithLargeCodec4Encodings[stretch].append((s,d))
                pass

            if lowerBound is None:
                lowerBound = computeBounds(g, s, d, pp, M, weighted)
                addValueCount(lowerBoundCounts, lowerBound)
                pass
            if dagSize < lowerBound:
                pairsWithDagSizeSmallerThanLowerBound[stretch].append((s,d))
                pass
            pass
        return
    #########


    startdateSecs = int(time.time())
    print '''
    _______________________________________________
    filename: [%s]
    start date: [%s]
    ''' % (filename, time.ctime(startdateSecs))
    g, lli = utils.textToG(filename, useInt=False, ignoreWeights=False)
    localLinkLabelLens = {}
    for node in lli.keys():
        if len(lli[node]) == 1:
            # special case, otherwise it would be length of zero.
            localLinkLabelLens[node] = 1
            pass
        else:
            localLinkLabelLens[node] = int(
                math.ceil(math.log(len(lli[node]), 2)))
            pass
        pass
    allNodes = tuple(g.nodes())
    numNodes = len(allNodes)
    i = 0

    assert pairIsOrdered, 'un-ordered currently not supported'

    srcDstPairs = set()

    assert (numberOfPairsToTry != None)

    if not seed:
        seed = int(time.time())
        pass
    randObj = random.Random(seed)

    if srcStartIdx is None:
        srcStartIdx = 0
        pass
    else:
        assert srcStartIdx >= 0
        pass
    if srcEndIdx is None:
        srcEndIdx = numNodes - 1
        pass
    else:
        assert srcEndIdx <= numNodes - 1
        pass
    assert srcStartIdx <= srcEndIdx


    # calculate M for computeBounds()
    if weighted:
        weights = map(lambda (u, v, edgeData): edgeData['weight'],
                      g.edges(data=True))
        maxWeight = max(weights)
        minWeight = min(weights)
        assert minWeight > 0
        M = float(maxWeight) / float(minWeight)
        pass
    else:
        M = float(1)
        pass

    lowerBoundCounts = {}
    pairsWithLargeCodec4Encodings = {}
    pairsWithDagSizeSmallerThanLowerBound = {}
    dagSize_stretchToCounts = {}
    codec2HdrLen_stretchToCounts = {}
    codec4HdrLen_stretchToCounts = {}
    singlePath_encodingLen_counts = {}
    for stretch in stretches:
        dagSize_stretchToCounts[stretch] = {}
        codec2HdrLen_stretchToCounts[stretch] = {}
        codec4HdrLen_stretchToCounts[stretch] = {}
        pairsWithLargeCodec4Encodings[stretch] = []
        pairsWithDagSizeSmallerThanLowerBound[stretch] = []
        pass

    if numberOfPairsToTry > 0:
        # must be <= the number of possible ordered pairs
        assert numberOfPairsToTry <= ((srcEndIdx - srcStartIdx + 1) * (numNodes - 1)), '%u must be <= than %u' % (numberOfPairsToTry, ((srcEndIdx - srcStartIdx + 1) * (numNodes - 1)))

        numPairsProcessed = 0
        partialResultNum = 0
        i = 0
        startdateSecs = int(time.time())
        while i < numberOfPairsToTry:
            idx1 = randObj.randint(srcStartIdx, srcEndIdx) # inclusive
            idx2 = randObj.randint(0, numNodes - 1)

            while idx2 == idx1:
                idx2 = randObj.randint(0, numNodes - 1)
                pass

            s,d = allNodes[idx1], allNodes[idx2]
            if (s,d) in srcDstPairs:
                # definitely skip
                print 'pair (%s,%s) already encountered -> skip' % (s,d)
                continue
            ## elif (d,s) in srcDstPairs:
            ##     # not seen (s,d) yet but seen (d,s), should skip or not?
            ##     if not pairIsOrdered:
            ##         print 'pairs are not ordered, and (%s,%s) already encountered -> skip' % (d,s)
            ##         continue
            ##     pass

            # do this so we know we have seen this (s, d) pair
            srcDstPairs.add((s, d))

            print 's,d="%s","%s"' % (s,d)
            evalOnePair(g=g, lli=lli, localLinkLabelLens=localLinkLabelLens, s=s, d=d,
                        lowerBoundCounts=lowerBoundCounts,
                        dagSize_stretchToCounts=dagSize_stretchToCounts,
                        pairsWithDagSizeSmallerThanLowerBound=pairsWithDagSizeSmallerThanLowerBound,
                        codec2HdrLen_stretchToCounts=codec2HdrLen_stretchToCounts,
                        codec4HdrLen_stretchToCounts=codec4HdrLen_stretchToCounts,
                        singlePath_encodingLen_counts=singlePath_encodingLen_counts,
                        pairsWithLargeCodec4Encodings=pairsWithLargeCodec4Encodings,
                        M=M)
            numPairsProcessed += 1
            if 0 == (numPairsProcessed % partialResultSize):
                # pickle the partial result and re-init the vars
                enddateSecs = int(time.time())
                partialResultNum += 1
                pr = PartialResult(
                    filename, startdateSecs, enddateSecs,
                    codec2HdrLen_stretchToCounts=codec2HdrLen_stretchToCounts,
                    codec4HdrLen_stretchToCounts=codec4HdrLen_stretchToCounts,
                    singlePath_encodingLen_counts=singlePath_encodingLen_counts,
                    dagSize_stretchToCounts=dagSize_stretchToCounts,
                    pairsWithLargeCodec4Encodings=pairsWithLargeCodec4Encodings,
                    lowerBoundCounts=lowerBoundCounts,
                    pairsWithDagSizeSmallerThanLowerBound=pairsWithDagSizeSmallerThanLowerBound,
                    argv=argv, seed=seed, weighted=weighted)
                pickleFilepath = '%s/partialResult_srcIdx_%u_%u_num_%u' % (
                    outputDir, srcStartIdx, srcEndIdx, partialResultNum)
                utils.pickleStuff(pickleFilepath, pr)
                # re-init
                startdateSecs = enddateSecs
                lowerBoundCounts = {}
                pairsWithLargeCodec4Encodings = {}
                pairsWithDagSizeSmallerThanLowerBound = {}
                dagSize_stretchToCounts = {}
                codec2HdrLen_stretchToCounts = {}
                codec4HdrLen_stretchToCounts = {}
                singlePath_encodingLen_counts = {}
                for stretch in stretches:
                    dagSize_stretchToCounts[stretch] = {}
                    codec2HdrLen_stretchToCounts[stretch] = {}
                    codec4HdrLen_stretchToCounts[stretch] = {}
                    pairsWithLargeCodec4Encodings[stretch] = []
                    pairsWithDagSizeSmallerThanLowerBound[stretch] = []
                    pass
                pass
            i += 1
            pass # end while i < numberOfPairsToTry
        pass # end if numberOfPairsToTry > 0
    else:
        # numberOfPairsToTry is <= 0, so we do all (ordered)
        # pairs. the graph'd better be not too big.
        numPairsProcessed = 0
        partialResultNum = 0
        startdateSecs = int(time.time())
        for i in xrange(srcStartIdx, srcEndIdx + 1):
            s = allNodes[i]
            for j in xrange(numNodes):
                if j == i:
                    continue
                d = allNodes[j]
                print 's,d="%s","%s"' % (s,d)
                evalOnePair(g=g, lli=lli, localLinkLabelLens=localLinkLabelLens, s=s, d=d,
                            lowerBoundCounts=lowerBoundCounts,
                            dagSize_stretchToCounts=dagSize_stretchToCounts,
                            pairsWithDagSizeSmallerThanLowerBound=pairsWithDagSizeSmallerThanLowerBound,
                            codec2HdrLen_stretchToCounts=codec2HdrLen_stretchToCounts,
                            codec4HdrLen_stretchToCounts=codec4HdrLen_stretchToCounts,
                            singlePath_encodingLen_counts=singlePath_encodingLen_counts,
                            pairsWithLargeCodec4Encodings=pairsWithLargeCodec4Encodings,
                            M=M)
                numPairsProcessed += 1
                if 0 == (numPairsProcessed % partialResultSize):
                    # pickle the partial result and re-init the vars
                    enddateSecs = int(time.time())
                    partialResultNum += 1
                    pr = PartialResult(
                        filename, startdateSecs, enddateSecs,
                        codec2HdrLen_stretchToCounts=codec2HdrLen_stretchToCounts,
                        codec4HdrLen_stretchToCounts=codec4HdrLen_stretchToCounts,
                        singlePath_encodingLen_counts=singlePath_encodingLen_counts,
                        dagSize_stretchToCounts=dagSize_stretchToCounts,
                        pairsWithLargeCodec4Encodings=pairsWithLargeCodec4Encodings,
                        lowerBoundCounts=lowerBoundCounts,
                        pairsWithDagSizeSmallerThanLowerBound=pairsWithDagSizeSmallerThanLowerBound,
                        argv=argv, seed=seed, weighted=weighted)
                    pickleFilepath = '%s/partialResult_srcIdx_%u_%u_num_%u' % (
                        outputDir, srcStartIdx, srcEndIdx, partialResultNum)
                    utils.pickleStuff(pickleFilepath, pr)
                    # re-init
                    startdateSecs = enddateSecs
                    lowerBoundCounts = {}
                    pairsWithLargeCodec4Encodings = {}
                    pairsWithDagSizeSmallerThanLowerBound = {}
                    dagSize_stretchToCounts = {}
                    codec2HdrLen_stretchToCounts = {}
                    codec4HdrLen_stretchToCounts = {}
                    singlePath_encodingLen_counts = {}
                    for stretch in stretches:
                        dagSize_stretchToCounts[stretch] = {}
                        codec2HdrLen_stretchToCounts[stretch] = {}
                        codec4HdrLen_stretchToCounts[stretch] = {}
                        pairsWithLargeCodec4Encodings[stretch] = []
                        pairsWithDagSizeSmallerThanLowerBound[stretch] = []
                        pass
                    pass
                pass
            pass
        pass

    # the last bunch might not have reached partialResultSize
    if len(lowerBoundCounts) > 0:
        enddateSecs = int(time.time())
        partialResultNum += 1
        pr = PartialResult(
            filename, startdateSecs, enddateSecs,
            codec2HdrLen_stretchToCounts=codec2HdrLen_stretchToCounts,
            codec4HdrLen_stretchToCounts=codec4HdrLen_stretchToCounts,
            singlePath_encodingLen_counts=singlePath_encodingLen_counts,
            dagSize_stretchToCounts=dagSize_stretchToCounts,
            pairsWithLargeCodec4Encodings=pairsWithLargeCodec4Encodings,
            lowerBoundCounts=lowerBoundCounts,
            pairsWithDagSizeSmallerThanLowerBound=pairsWithDagSizeSmallerThanLowerBound,
            argv=argv, seed=seed, weighted=weighted)
        pickleFilepath = '%s/partialResult_srcIdx_%u_%u_num_%u' % (
            outputDir, srcStartIdx, srcEndIdx, partialResultNum)
        utils.pickleStuff(pickleFilepath, pr)
        pass

    print '''
    end date: [%s]
    ''' % (time.ctime())
    return




def cmd_runeval(argv):
    assert argv[0] == 'runeval'

    def usageAndExit(progname):
        print '''
usage: %s [--weighted] -n ... [--srcStartIdx ...] [--srcEndIdx ...]
          [--seed ...] --headerLengthThreshold ... --partialResultSize ...
          --outputdir ... <graph file path>

         --weighted: whether the graph should be considered weighted. False if
                     not specified.

         --headerLengthThreshold: src-dst pairs whose hdr lengths are
                                  greater than this value will be
                                  recorded (for later analysis).

         --partialResultSize: should pickle the partial result for
                              groups of this number of processed
                              src-dst pairs.

         --outputDir: directory into which to place the partial result
                      pickle files.

         the following args control the size of the eval.

         -n ... : controls the number of randomly sampled src-dst
                  pairs to evaluate, within the range specified by
                  other arguments. can be 0 to mean all possible
                  ordered pairs within that range.

         the following args define the range of the source indices (in
         the sorted list of all source node names) to use.

         --srcStartIdx ...: the smallest index, inclusise, to
                            use. default to 0.

         --srcEndIdx ...: the largest index, inclusive, to
                          use. default to number of nodes - 1.

         the effective source end index must be >= than the effective
         source start index.

         so "--srcStartIdx 3 --srcEndIdx 5" means only sources in the
         index range [3, 5] are used, and "--srcStartIdx 6 --srcEndIdx
         5" is invalid.

         --seed ...: if specified, should be an integer to seed the
                     single deterministic pseudo-random generator used
                     for sampling src and destination nodes.
''' % (progname)
        sys.exit(-1)
        return

    startdateSecs = int(time.time())
    print "start date: [%s]" % (time.ctime())
    print "evalCombo.Revision: [%s]" % (Revision)
    print "utils.Revision:     [%s]" % (utils.Revision)
    print "approach2.Revision: [%s]" % (approach2.Revision)
    print "codec2.Revision:    [%s]" % (codec2.Revision)
    print "codec4.Revision:    [%s]" % (codec4.Revision)
    print "argv:\n", ' '.join(argv)
    print

    weighted = False
    numberOfPairsToTry = None
    srcStartIdx = srcEndIdx = None
    headerLengthThreshold = partialResultSize = None
    seed = None

    opts, args = getopt.getopt(argv[1:], 'n:',
                               ['weighted', 'srcStartIdx=', 'srcEndIdx=',
                                'headerLengthThreshold=', 'seed=',
                                'partialResultSize=',
                                'outputDir=',
                                ])
    ## parse options
    for o, a in opts:
        if o == '-n':
            numberOfPairsToTry = int(a)
            pass
        elif o == '--weighted':
            weighted = True
            pass
        elif o == '--headerLengthThreshold':
            headerLengthThreshold = int(a)
            pass
        elif o == '--partialResultSize':
            partialResultSize = int(a)
            pass
        elif o == '--outputDir':
            outputDir = a
            assert os.path.isdir(outputDir), '%s is not a directory' % outputDir
            pass
        elif o == '--srcStartIdx':
            srcStartIdx = int(a)
            pass
        elif o == '--srcEndIdx':
            srcEndIdx = int(a)
            pass
        elif o == '--seed':
            seed = int(a)
            pass
        pass

    if (numberOfPairsToTry is None):
        usageAndExit(argv[0])
        pass

    assert outputDir != None

    assert headerLengthThreshold > 0 and partialResultSize > 0

    if (srcStartIdx != None) and (srcEndIdx != None):
        assert not (srcStartIdx > srcEndIdx or srcStartIdx < 0 or srcEndIdx < 0)
        pass

    filename = args[0]
    evalOneFile(
        filename, numberOfPairsToTry=numberOfPairsToTry,
        partialResultSize=partialResultSize,
        srcStartIdx=srcStartIdx, srcEndIdx=srcEndIdx,
        pairIsOrdered=True, weighted=weighted,
        argv=argv, seed=seed,
        outputDir=outputDir,
        headerLengthThreshold=headerLengthThreshold,
        )

    pass



####################################################################
def genCDFFromCounts(valueToCounts, outFilePath):
    totalCount = sum(valueToCounts.values())
    fil = open(outFilePath, 'w')
    fil.write('# total count: %u\n' % (totalCount))
    cumulativeCount = 0
    for value in sorted(valueToCounts.keys()):
        cumulativeCount += valueToCounts[value]
        fraction = float(cumulativeCount) / totalCount
        fil.write('%f\t%f  # count of this value: %u\n' % (value, fraction, valueToCounts[value]))
        pass
    fil.close()
    return

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

def cmd_showPairsWithDagSizeSmallerThanLowerBound(argv):
    argvidx = 0
    cmdname = argv[argvidx]
    argvidx += 1
    assert 'cmd_' + cmdname == inspect.stack()[0][3]

    showDetails = False

    opts, args = getopt.getopt(argv[argvidx:], '',
                               ['showDetails', ])
    ## parse options
    for o, a in opts:
        if o == '--showDetails':
            showDetails = True
            pass
        pass

    dirpaths = args
    assert len(dirpaths) > 0

    curGraphFilePath = None

    for dirpath in dirpaths:
        filenames = os.listdir(dirpath)
        for filename in filenames:
            filepath = dirpath + '/' + filename

            pr = utils.unpickleStuff(filepath)

            if showDetails and (pr.filename != curGraphFilePath):
                g, _ = utils.textToG(pr.filename, useInt=False,
                                       ignoreWeights=not pr.weighted)

                # calculate M for computeBounds()
                if pr.weighted:
                    weights = map(lambda (u, v, edgeData): edgeData['weight'],
                                  g.edges(data=True))
                    maxWeight = max(weights)
                    minWeight = min(weights)
                    assert minWeight > 0
                    M = float(maxWeight) / float(minWeight)
                    pass
                else:
                    M = float(1)
                    pass
                pass
                
            for stretch in stretches:
                for (s,d) in pr.pairsWithDagSizeSmallerThanLowerBound[stretch]:
                    if showDetails:
                        pp, dp = getDgWithStretch(g, s, d, pr.weighted, stretch)
                        if dp is None:
                            dp = {}
                            pass
                        dag, virtualDetourPaths = approach2.getDagWithVnodes(
                            pp, dp, returnDetourPathsWithVNodes=True)
                        lowerBound = computeBounds(g, s, d, pp, M, pr.weighted)
                        print 's,d=%s,%s; #OfEdges(pp)=%u, #OfEdges(dps)=%u, lowerBound=%u, dagSize=%u' % (
                            repr(s), repr(d), len(pp)-1,
                            sum(map(lambda p: len(p) - 1, dp.values())),
                            lowerBound, dag.number_of_edges()
                            )
                        pass
                    else:
                        print 's,d=%s,%s' % (repr(s),repr(d))
                        pass
                    pass
                pass
            pass
        pass
    return

def cmd_showTotalDagSizes(argv):
    argvidx = 0
    cmdname = argv[argvidx]
    argvidx += 1
    assert 'cmd_' + cmdname == inspect.stack()[0][3]

    opts, args = getopt.getopt(argv[argvidx:], '', [])

    ## parse options
    for o, a in opts:
        pass

    ###

    dagSize_stretchToTotal = {}
    for stretch in stretches:
        dagSize_stretchToTotal[stretch] = 0
        pass

    dirpaths = args

    for dirpath in dirpaths:
        filenames = os.listdir(dirpath)
        for filename in filenames:
            filepath = dirpath + '/' + filename

            pr = utils.unpickleStuff(filepath)

            for stretch in stretches:
                dagSize_stretchToTotal[stretch] += \
                                                sum(map(lambda (size, count): size*count, pr.dagSize_stretchToCounts[stretch].items()))
                pass
            pass
        pass

    for stretch in stretches:
        print 'stretch', stretch, ': ', dagSize_stretchToTotal[stretch]
        pass
    return

def cmd_gencdf(argv):
    knownvalues = ['all']

    def usage(cmdname):
        print 'usage: %s <whichvalue> [-n ...] [--bucket-size ...] dir [dir ...]' % (cmdname)
        print '         <whichvalue> must be one of the following: ' + ','.join(knownvalues)
        print '         -n integer: instead of processing all available datapoints, process only the first this number of data points. Error if data does not contain enough data points.'
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
    print whichvalue
    if not whichvalue in knownvalues:
        print '<whichvalue> must be one of the following:\n' + '\n'.join(knownvalues)
        sys.exit(-1)
        pass
    argvidx += 1
    ###

    bucketsize = None
    exactlyNumDataPoints = None

    opts, args = getopt.getopt(argv[argvidx:], 'n:',
                               ['bucket-size=', ])

    ## parse options
    for o, a in opts:
        if o == '-n':
            exactlyNumDataPoints = int(a)
            raise Exception("not yet supported")
            assert exactlyNumDataPoints > 0
            pass
        elif o == '--bucket-size':
            bucketsize = int(a)
            assert bucketsize > 0
            pass
        pass

    ###

    def updateCounts(curValueToCounts, moreValueToCounts):
        for value, count in moreValueToCounts.iteritems():
            if value in curValueToCounts:
                curValueToCounts[value] += count
                pass
            else:
                curValueToCounts[value] = count
                pass
            pass
        pass
    ###

    lowerBoundCounts = {}
    dagSize_stretchToCounts = {}
    codec2HdrLen_stretchToCounts = {}
    codec4HdrLen_stretchToCounts = {}
    singlePath_encodingLen_counts = {}
    for stretch in stretches:
        dagSize_stretchToCounts[stretch] = {}
        codec2HdrLen_stretchToCounts[stretch] = {}
        codec4HdrLen_stretchToCounts[stretch] = {}
        pass

    dirpaths = args

    for dirpath in dirpaths:
        filenames = os.listdir(dirpath)
        for filename in filenames:
            filepath = dirpath + '/' + filename

            pr = utils.unpickleStuff(filepath)

            updateCounts(lowerBoundCounts, pr.lowerBoundCounts)
            updateCounts(
                singlePath_encodingLen_counts, pr.singlePath_encodingLen_counts)

            for stretch in stretches:
                updateCounts(
                    dagSize_stretchToCounts[stretch],
                    pr.dagSize_stretchToCounts[stretch])
                updateCounts(
                    codec2HdrLen_stretchToCounts[stretch],
                    pr.codec2HdrLen_stretchToCounts[stretch])
                updateCounts(
                    codec4HdrLen_stretchToCounts[stretch],
                    pr.codec4HdrLen_stretchToCounts[stretch])
                pass
            pass
        pass

    genCDFFromCounts(lowerBoundCounts, 'cdf_lowerBound')
    genCDFFromCounts(
        singlePath_encodingLen_counts, 'cdf_singlePath_encodingLen')

    for stretch in stretches:
        genCDFFromCounts(
            dagSize_stretchToCounts[stretch],
            'cdf_dagSize_stretch_%u' % (stretch))
        genCDFFromCounts(
            codec2HdrLen_stretchToCounts[stretch],
            'cdf_codec2HdrLen_stretch_%u' % (stretch))
        genCDFFromCounts(
            codec4HdrLen_stretchToCounts[stretch],
            'cdf_codec4HdrLen_stretch_%u' % (stretch))
        pass

    return


cmds = {
    'runeval' : cmd_runeval,
    'gencdf' : cmd_gencdf,
    'showPairsWithDagSizeSmallerThanLowerBound' :
        cmd_showPairsWithDagSizeSmallerThanLowerBound,
    'showTotalDagSizes' :
        cmd_showTotalDagSizes,
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
