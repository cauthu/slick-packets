import utils
import math

Id = '$Id$'
Revision = '$Revision: 504 $'

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
    knownvalues = ['maxStretch', 'timeStretchDownTo1']

    def usage(cmdname):
        print 'usage: %s <whichvalue> [--bucket-size ...] <result file path> [<result file path> ...]' % (cmdname)
        print '         <whichvalue> must be one of the following: ' + ', '.join(knownvalues)
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
    knownvalues = ['maxStretch', 'timeStretchDownTo1']
    print whichvalue
    if not whichvalue in knownvalues:
        print '<whichvalue> must be one of the following:\n' + '\n'.join(knownvalues)
        sys.exit(-1)
        pass
    argvidx += 1
    ###

    bucketsize = None
    if argv[argvidx] == '--bucket-size':
        bucketsize = float(argv[argvidx + 1])
        assert bucketsize > 0
        argvidx += 2
        pass
    ###

    filenames = argv[argvidx:]

    dataPoints = []

    for filename in filenames:
        calculatorOutput = utils.unpickleStuff(filename)

        # make sure the revisions of the obj match ours

        for timeAfterFailure2Stretch in calculatorOutput:
            if whichvalue == 'maxStretch':
                maxStretch = max(map(lambda x: x[1], timeAfterFailure2Stretch))
                dataPoints.append(maxStretch)
                pass
            elif whichvalue == 'timeStretchDownTo1':
                timeStretchDownTo1 = filter(lambda x: x[1] == 1, timeAfterFailure2Stretch)[0][0]
                dataPoints.append(timeStretchDownTo1)
                pass
            pass
        pass

    # finished gathering the data
    dataPoints.sort()
    if whichvalue == 'maxStretch':
        genCDF(dataPoints, 'cdfmaxstretch', bucketsize=bucketsize)
        pass
    elif whichvalue == 'timeStretchDownTo1':
        genCDF(dataPoints, 'timeStretchDownTo1', bucketsize=bucketsize)
        pass

    return


cmds = {
    'gencdf' : cmd_gencdf,
    }

if __name__ == '__main__':
    import sys
    if len(sys.argv) < 2:
        print 'Usage: %s cmd [cmd options]' % (sys.argv[0])
        print '  cmd must be one of the following:\n' + '\n'.join(cmds.keys())
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
