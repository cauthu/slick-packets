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
import array
import pdb
import codec4

Revision = '$Revision$'
Id = '$Id$'


class PartialResult:
    '''
    "hdrLenCounts" is dictionary mapping from hdr len to count.

    "srcDstPairsWithLargeEncodings" is a list of (s,d) tuples that
    have encodings longer than some threshold, which is up to the
    caller. we dont enforce anything here.

    "srcIdxRange", if specified, is a tuple of two indices, inclusive,
    denoting the range of sources used for this partial result.
    '''
    def __init__(self, filename,
                 startdateSecs, enddateSecs,
                 pairsWithLargeEncodings,
                 hdrLenCounts,
                 srcIdxRange=None):
        self.filename = filename
        self.startdateSecs = startdateSecs
        self.enddateSecs = enddateSecs
        self.hdrLenCounts = hdrLenCounts
        self.pairsWithLargeEncodings = pairsWithLargeEncodings
        self.srcIdxRange = srcIdxRange
        return
    pass



def evalOneFile(filename, headerLengthThreshold, partialResultSize, outputDir,
                numberOfPairsToTry=None, pairIsOrdered=False,
                weighted=False,
                srcStartIdx=None, srcEndIdx=None,
                ):

    def addHdrLen(countsDict, hdrlen):
        if hdrlen in countsDict:
            countsDict[hdrlen] += 1
            pass
        else:
            countsDict[hdrlen] = 1
            pass
        return

    def evalOnePair(s, d, hdrLenCounts, pairsWithLargeEncodings):
        pp, dp = approach2.getDg(g, s, d, weighted)
        if (not pp):
            print 'no path: s,d="%s","%s"' % (s,d)
            return

        if dp == None:
            dp = {}
            pass
        hdrLen4 = codec4.encode(
            pp, dp, lli, s, d,
            roundUpToMultipleBits=8)

        if hdrLen4 > headerLengthThreshold:
            pairsWithLargeEncodings.append((s,d))
            pass

        addHdrLen(hdrLenCounts, hdrLen4)
        return
    #########

    startdateSecs = int(time.time())
    print '''
    _______________________________________________
    filename: [%s]
    start date: [%s]
    ''' % (filename, time.ctime(startdateSecs))
    g, lli = utils.textToG(filename, useInt=False)
    allNodes = tuple(sorted(g.nodes()))
    numNodes = len(allNodes)
    i = 0

    assert (numberOfPairsToTry != None) ^ (srcStartIdx != None or srcEndIdx != None)
    pairsWithLargeEncodings = []
    hdrLenCounts = {}

    if numberOfPairsToTry != None and numberOfPairsToTry > 0:
        srcDstPairs = set()
        while i < numberOfPairsToTry:
            # this is crypto random integer
            idx1 = (struct.unpack('I', os.urandom(4))[0]) % numNodes
            idx2 = (struct.unpack('I', os.urandom(4))[0]) % numNodes

            while idx2 == idx1:
                idx2 = (struct.unpack('I', os.urandom(4))[0]) % numNodes
                pass

            s,d = allNodes[idx1], allNodes[idx2]
            if (s,d) in srcDstPairs:
                # definitely skip
                print 'pair (%s,%s) already encountered -> skip' % (s,d)
                continue
            elif (d,s) in srcDstPairs:
                # not seen (s,d) yet but seen (d,s), should skip or not?
                if not pairIsOrdered:
                    print 'pairs are not ordered, and (%s,%s) already encountered -> skip' % (d,s)
                    continue
                pass

            # do this so we know we have seen this (s, d) pair
            srcDstPairs.add((s, d))

            print 's,d="%s","%s"' % (s,d)

            evalOnePair(s,d, hdrLenCounts, pairsWithLargeEncodings)

            i += 1
            pass # end while i < numberOfPairsToTry
        pass # end if numberOfPairsToTry > 0
    elif numberOfPairsToTry != None and numberOfPairsToTry <= 0:
        # numberOfPairsToTry is <= 0, so we do all (un-ordered)
        # pairs. the graph'd better be not too big.
        for i in xrange(numNodes):
            for j in xrange(i + 1, numNodes):
                s = allNodes[i]
                d = allNodes[j]
                print 's,d="%s","%s"' % (s,d)
                evalOnePair(s, d, hdrLenCounts, pairsWithLargeEncodings)
                pass
            pass
        pass
    else:
        assert srcStartIdx != None or srcEndIdx != None
        if srcStartIdx == None:
            srcStartIdx = 0
            pass
        assert 0 <= srcStartIdx < numNodes
        if srcEndIdx == None:
            srcEndIdx = numNodes - 1
            pass
        assert 0 <= srcEndIdx < numNodes
        assert srcStartIdx <= srcEndIdx
        numSrcsProcessed = 0
        curPartialSrcRange = []
        for si in xrange(srcStartIdx, srcEndIdx+1):
            s = allNodes[si]
            if len(curPartialSrcRange) == 0:
                curPartialSrcRange.append(si)
                startdateSecs = int(time.time())
                pass
            for d in allNodes:
                if d != s:
                    evalOnePair(s, d, hdrLenCounts, pairsWithLargeEncodings)
                    pass
                pass
            numSrcsProcessed += 1
            if numSrcsProcessed == partialResultSize:
                # pickle the partial result and re-init the vars
                curPartialSrcRange.append(si)
                enddateSecs = int(time.time())
                pr = PartialResult(
                    filename, startdateSecs, enddateSecs,
                    pairsWithLargeEncodings,
                    hdrLenCounts=hdrLenCounts,
                    srcIdxRange=(curPartialSrcRange[0], curPartialSrcRange[1]),
                    )
                pickleFilepath = '%s/partialResult_%u_%u' % (
                    outputDir, curPartialSrcRange[0], curPartialSrcRange[1])
                utils.pickleStuff(pickleFilepath, pr)
                # re-init
                del hdrLenCounts, pairsWithLargeEncodings, curPartialSrcRange
                hdrLenCounts = {}
                # be < 256 (bytes)
                pairsWithLargeEncodings = []
                curPartialSrcRange = []
                numSrcsProcessed = 0
                pass
            pass

        # the last bunch might not have reached partialResultSize
        if len(hdrLenCounts) > 0:
            curPartialSrcRange.append(si)
            enddateSecs = int(time.time())
            pr = PartialResult(
                filename, startdateSecs, enddateSecs,
                pairsWithLargeEncodings,
                hdrLenCounts=hdrLenCounts,
                srcIdxRange=(curPartialSrcRange[0], curPartialSrcRange[1]),
                )
            pickleFilepath = '%s/partialResult_%u_%u' % (
                outputDir, curPartialSrcRange[0], curPartialSrcRange[1])
            utils.pickleStuff(pickleFilepath, pr)
            pass
        pass

    return




def cmd_runeval(argv):
    assert argv[0] == 'runeval'

    def usageAndExit(progname):
        print '''
usage: %s [--weighted] [-n ...] [--srcStartIdx ...] [--srcEndIdx ...]
          --headerLengthThreshold ... --partialResultSize ... --outputdir ...
          <graph file path>

         --weighted: whether the graph should be considered weighted. False if
                     not specified.

         --headerLengthThreshold: src-dst pairs whose hdr lengths are
                                  greater than this value will be
                                  recorded (for later analysis).

         --partialResultSize: should pickle the partial result for
                              groups of this number of processed
                              source indices/src-dst pairs.

         --outputDir: directory into which to place the partial result
                      pickle files.

         the following args control the size of the eval.

         -n <number of pairs>: can be <= 0 to mean all possible
                               non-ordered pairs (the graph should not
                               be too big). otherwise, the pairs will
                               be sampled randomly.

         if any of the following args is used, the list of node names
         will be sorted. they specify the range of the source indices
         to use.

         --srcStartIdx ...: "source start index": the smallest index,
                            inclusise, to use. default to 0.

         --srcEndIdx ...: "source end index": the largest index,
                          inclusive, to use. default to number of
                          nodes - 1.

         the effective source end index must be <= than the effective
         source start index.

         so "--srcStartIdx 3 --srcEndIdx 5" means only sources in the
         index range [3, 5] are used, and "--srcStartIdx 6 --srcEndIdx
         5" is invalid.

         at least one of -n, --srcStartIdx, and --srcEndIdx must be
         specified.

''' % (progname)
        sys.exit(-1)
        return

    startdateSecs = int(time.time())
    print "start date: [%s]" % (time.ctime())
    print "Revision:     [%s]" % (Revision)
    print "utils.Revision:     [%s]" % (utils.Revision)
    print "approach2.Revision: [%s]" % (approach2.Revision)

    weighted = False
    numberOfPairsToTry = None
    srcStartIdx = srcEndIdx = None
    headerLengthThreshold = partialResultSize = None
    outputDir = None

    opts, args = getopt.getopt(argv[1:], 'n:',
                               ['weighted', 'srcStartIdx=', 'srcEndIdx=',
                                'headerLengthThreshold=',
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
        pass

    if not ((numberOfPairsToTry != None) ^ (srcStartIdx != None or srcEndIdx != None)):
        usageAndExit(argv[0])
        pass

    assert outputDir != None

    assert headerLengthThreshold > 0 and partialResultSize > 0

    filename = args[0]

    evalOneFile(
        filename, numberOfPairsToTry=numberOfPairsToTry, outputDir=outputDir,
        srcStartIdx=srcStartIdx, srcEndIdx=srcEndIdx,
        pairIsOrdered=False, weighted=weighted,
        headerLengthThreshold=headerLengthThreshold,
        partialResultSize=partialResultSize,
        )

    pass



####################################################################

def cmd_gencdf(argv):
    knownvalues = ['hdrsizes']

    def usage(cmdname):
        print 'usage: %s <whichvalue> [-n ...] [--bucket-size ...] dir [dir ...]' % (cmdname)
        print '         <whichvalue> must be one of the following: ' + ','.join(knownvalues)
        print '         -n integer: instead of processing all available datapoints, process only the first this number of data points. Error if data does not contain enough data points.'
        print '         --bucket-size integer: instead of outputting individual data points, put them into buckets of the specified size. each bucket is represented by its upperbound. this reduces the number of data points in output.'
        print '         each dir should contain only partial result pickle files.'
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

    opts, args = getopt.getopt(argv[argvidx:], '')

    ###

    dirpaths = args

    hdrLenCounts = {}

    for dirpath in dirpaths:
        filenames = os.listdir(dirpath)
        for filename in filenames:
            filepath = dirpath + '/' + filename

            pr = utils.unpickleStuff(filepath)

            for hdrLen, count in pr.hdrLenCounts.iteritems():
                if hdrLen in hdrLenCounts:
                    hdrLenCounts[hdrLen] += count
                    pass
                else:
                    hdrLenCounts[hdrLen] = count
                    pass
                pass
            pass
        pass

    totalCount = sum(hdrLenCounts.values())

    hdrLens = sorted(hdrLenCounts.keys())

    fil = open('cdfCodec4', 'w')
    fil.write('# total count: %u\n' % (totalCount))
    cumulativeCount = 0
    for hdrLen in hdrLens:
        cumulativeCount += hdrLenCounts[hdrLen]
        fraction = float(cumulativeCount) / totalCount
        fil.write('%u\t%f  # count of this value: %u\n' % (hdrLen, fraction, hdrLenCounts[hdrLen]))
        pass
    fil.close()
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
