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
#import pdb


Revision = '$Revision$'
Id = '$Id$'


# only support these offsetPtrAlignments
offsetPtrAlignments = (1, 4, 8) # in bits


class SrcDstPairResult3:
    '''
    "hdrLens" and "ptrLens" are dictionaries, with the keys being the
    offset ptr alignment.
    '''
    def __init__(self, hdrLens2Normal, dagsizeNormal, hdrLens2Smaller, dagsizeSmaller):
        # these two are from "getHeader2()"
        self.hdrLens2Normal = hdrLens2Normal
        self.dagsizeNormal = dagsizeNormal

        self.hdrLens2Smaller = hdrLens2Smaller
        self.dagsizeSmaller = dagsizeSmaller
        

        # from "getHeader3()"

        return
    pass

class FileResult3:
    '''
    "srcDstPairResults3" is a dictionary, with tuples (s,d) as keys,
    and values are SrcDstPairResult3 objects. the value is None if s
    and d are disconnected.
    '''
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
                 revision, utilsRevision, approach2Revision,
                 weighted):

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
    g, lli = utils.textToG(filename, useInt=False, ignoreWeights=(not weighted))
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

    for s, d in srcDstPairResults3.keys():
        #### use approach2
        hdrLens2Normal = {}
        dagsizeNormal = []
        hdrLens2Smaller = {}
        dagsizeSmaller = []

        for hdrlenDict, dagsizeList, preferDownStreamPEdges \
            in ((hdrLens2Normal, dagsizeNormal, False),
                (hdrLens2Smaller, dagsizeSmaller, True)):

            pp, dp = approach2.getDg(g, s, d, weighted=weighted,
                                     preferDownStreamPEdges=preferDownStreamPEdges)
            if (not pp) or (not dp):
                print 'no path: s,d="%s","%s"' % (s,d)
                continue

            dag, virtualDetourPaths = approach2.getDagWithVnodes(
                pp, dp, returnDetourPathsWithVNodes=True)

            dagsizeList.append(dag.number_of_edges())
            for offsetPtrAlignment in offsetPtrAlignments:
                hdrlenDict[offsetPtrAlignment], \
                    _ = approach2.getHeader2(
                    dag, pp, virtualDetourPaths, lli, False, s, d,
                    roundUpToMultipleBits=offsetPtrAlignment)
                pass
            pass

        if len(hdrLens2Smaller) == 0:
            assert len(hdrLens2Normal) == len(dagsizeSmaller) == len(dagsizeNormal) == 0
            pass
        else:
            srcDstPairResults3[(s, d)] = SrcDstPairResult3(
                hdrLens2Normal, dagsizeNormal[0], hdrLens2Smaller, dagsizeSmaller[0])
            pass

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

    pickleFilename = 'evalResult3.pickle_%s' % \
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
    knownvalues = ['hdrsizes']

    def usage(cmdname):
        print 'usage: %s <whichvalue> [-n ...] [--bucket-size ...] <graph file path> [<graph file path> ...]' % (cmdname)
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
            assert exactlyNumDataPoints > 0
            pass
        elif o == '--bucket-size':
            bucketsize = int(a)
            assert bucketsize > 0
            pass
        pass

    ###

    filenames = args

    hdrLen2NormalLists = {}
    hdrLen2SmallerLists = {}
    for offsetPtrAlignment in offsetPtrAlignments:
        hdrLen2NormalLists[offsetPtrAlignment] = []
        hdrLen2SmallerLists[offsetPtrAlignment] = []
        pass
    dagsizeNormal = []
    dagsizeSmaller = []

    numdatapointssofar = 0
    for filename in filenames:
        evalResult3 = utils.unpickleStuff(filename)

        # make sure the revisions of the obj match ours

        for fileResult3 in evalResult3.fileResults3:
            for srcDstPairResult3 in fileResult3.srcDstPairResults3.values():
                if srcDstPairResult3 is None:
                    # might be None if the (s,d) pair was disconnected
                    continue
                numdatapointssofar += 1
                if whichvalue == 'hdrsizes':
                    # assume that these offsetPtrAlignment are same as
                    # we expected them
                    for offsetPtrAlignment, hdrlen in srcDstPairResult3.hdrLens2Normal.iteritems():
                        hdrLen2NormalLists[offsetPtrAlignment].append(float(hdrlen) / ( float(8) / offsetPtrAlignment))
                        pass

                    for offsetPtrAlignment, hdrlen in srcDstPairResult3.hdrLens2Smaller.iteritems():
                        hdrLen2SmallerLists[offsetPtrAlignment].append(float(hdrlen) / ( float(8) / offsetPtrAlignment))
                        pass

                    dagsizeNormal.append(srcDstPairResult3.dagsizeNormal)
                    dagsizeSmaller.append(srcDstPairResult3.dagsizeSmaller)
                    pass

                # have we collected enough?
                if exactlyNumDataPoints and exactlyNumDataPoints == numdatapointssofar:
                    break
                pass
            pass
        pass

    # finished gathering the data
    if exactlyNumDataPoints and (numdatapointssofar < exactlyNumDataPoints):
        raise Exception('found only %u data points.' % (numdatapointssofar))

    for offsetPtrAlignment in offsetPtrAlignments:
        hdrLen2NormalLists[offsetPtrAlignment].sort()
        hdrLen2SmallerLists[offsetPtrAlignment].sort()

        genCDF(hdrLen2NormalLists[offsetPtrAlignment], 'cdfGetHeader2NormalForAlignment%d' % offsetPtrAlignment, bucketsize=bucketsize)
        genCDF(hdrLen2SmallerLists[offsetPtrAlignment], 'cdfGetHeader2SmallerForAlignment%d' % offsetPtrAlignment, bucketsize=bucketsize)

        pass

    dagsizeNormal.sort()
    dagsizeSmaller.sort()

    genCDF(dagsizeNormal, 'cdfdagsizenormal', bucketsize=bucketsize)
    genCDF(dagsizeSmaller, 'cdfdagsizesmaller', bucketsize=bucketsize)

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
