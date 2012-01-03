import getopt
import sys
import struct
import os

import bitstring
import utils
import approach2
import codec3

Revision = '$Revision: 481 $'
Id = '$Id$'

def usageAndExit(progname):
    print '''
Generate type-2 encodings for random src-dst pairs from the input
graph, writing the binary encodings into the output file.

Usage: %s [--weighted] [--ordered-pairs] -i INPUT -n NUMPAIRS -o OUTPUT

    -i INPUT: the input graph file

    -n NUMPAIRS: number of src-dst pairs to use. can be 0, and will
                 use all possible pairs.

    -o OUTPUT: the output file to contain the encodings.
''' % (progname)
    sys.exit(0)
    pass
    
if __name__ == '__main__':
    if len(sys.argv) < 2:
        usageAndExit(sys.argv[0])
        pass

    opts, args = getopt.getopt(sys.argv[1:], 'i:n:o:',
                               ['weighted', 'ordered-pairs'])
    weighted = False
    numberOfPairsToTry = 0
    inputGraphFile = outputFilePath = None
    pairIsOrdered = False

    ## parse options
    for o, a in opts:
        if o == '-n':
            numberOfPairsToTry = int(a)
            pass
        elif o == '-i':
            inputGraphFile = a
            pass
        elif o == '-o':
            outputFilePath = a
            pass
        elif o == '--weighted':
            weighted = True
            pass
        elif o == '--ordered-pairs':
            pairIsOrdered = True
            pass
        pass

    if numberOfPairsToTry < 0 or inputGraphFile == None or outputFilePath == None:
        usageAndExit(sys.argv[0])
        pass

    g, lli = utils.textToG(inputGraphFile, useInt=False,
                           ignoreWeights=not weighted)
    allNodes = g.nodes()
    numNodes = len(allNodes)

    srcDstPairs = set()

    if numberOfPairsToTry > 0:
        i = 0
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

            i += 1
            pass # end while i < numberOfPairsToTry
        pass # end if numberOfPairsToTry > 0
    else:
        # numberOfPairsToTry is <= 0, so we do all
        # pairs. the graph'd better be not too big.
        for i in xrange(numNodes):
            s = allNodes[i]
            if not pairIsOrdered:
                for j in xrange(i + 1, numNodes):
                    d = allNodes[j]
                    print 's,d="%s","%s"' % (s,d)
                    srcDstPairs.add((s, d))
                    pass
                pass
            else:
                for d in allNodes:
                    if d == s:
                        continue
                    print 's,d="%s","%s"' % (s,d)
                    srcDstPairs.add((s, d))
                    pass
                pass
            pass
        pass

    ###########################
    # now that we have the pairs we want to eval, eval them

    outputFile = open(outputFilePath, 'w')

    outputFile.write('\n\xff %s, codec3, argv: %s\n' % (Revision, str(sys.argv)))

    for i, (s, d) in enumerate(srcDstPairs):
        #### use approach2
        # comment must start with 2 bytes '\n\xff'
        outputFile.write('\n\xff pair num %u s,d=%s,%s...' % (i,s,d))

        pp, dp = approach2.getDg(g, s, d, weighted)
        if (not pp):
            print 'no path: s,d="%s","%s"' % (s,d)
            outputFile.write(' no path.\n')
            continue

        if dp == None:
            dp = {}
            pass

        # end the comment, must end with 1 byte '\n'
        outputFile.write('\n')

        bs = codec3.encode(pp,dp,lli,s,d,roundUpToMultipleBits=1,returnActualEncoding=True)

        asBytes = bs.tobytes()

        assert len(asBytes) < 2**8

        # need to do the 2-byte meta-info

        # the len in bytes
        finalBs = bitstring.BitString(length=8, uint=len(asBytes))
        # the num bits in the last byte
        numBitsInLastByte = (bs.length % 8);
        if (numBitsInLastByte == 0):
            # the last byte is full
            numBitsInLastByte = 8
            pass
        finalBs.append(bitstring.BitString(length=4, uint=numBitsInLastByte))
        # the encoding type
        finalBs.append(bitstring.BitString(length=4, uint=3))

        finalBs.append(bs)

        outputFile.write(finalBs.tobytes())
        pass # end while loop

    pass
