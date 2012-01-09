# find distributions of nodes that have detour paths.


'''
uses approach2 (primary-path-then-detour-paths one), with vnodes

use this same module to run the eval and then process data.

the eval will keep track of result (graph size, header size, etc) for
each pair (s,d), and at the end will pickle ALL the pairs.

first intended use of this is to generate CDF. one might say, why not
generating the CDF during the eval and avoid pickling. well, we might
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


class SrcDstPairResult3:
    def __init__(self, fractionWithDetour):
        self.fractionWithDetour = fractionWithDetour
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
    g, lli = utils.textToG(filename, useInt=False)
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
        assert numberOfPairsToTry > 0
        pass

    ###########################
    # now that we have the pairs we want to eval, eval them

    for s, d in srcDstPairResults3.keys():
        #### use approach2
        pp, dp = approach2.getDg(g, s, d, weighted)
        if (not pp) or (not dp):
            print 'no path: s,d="%s","%s"' % (s,d)
            continue

        numPNodes = len(pp) - 1 # don't want to count the destination

        fractionWithDetour = len(dp) / float(numPNodes)
        srcDstPairResults3[(s, d)] = SrcDstPairResult3(
            fractionWithDetour)

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

    pickleFilename = 'detourDistributionResult.pickle_%s' % \
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
    knownvalues = ['detourDistribution']

    def usage(cmdname):
        print 'usage: %s <whichvalue> [-n ...] [--bucket-size ...] <pickle file path>' % (cmdname)
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

    percentlist = []

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
                if whichvalue == 'detourDistribution':
                    percentlist.append(srcDstPairResult3.fractionWithDetour * 100)
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

    genCDF(sorted(percentlist), 'cdfDetourDistribution', bucketsize=bucketsize)

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
