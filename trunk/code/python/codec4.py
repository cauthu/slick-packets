import inspect

import approach2, utils
from codec_common import *

Revision = '$Revision: 1060 $'
Id = '$Id$'

###################################################################3
def encode(primaryPath, detourPaths, localLinkIDs,
           localLinkLabelLens,
           s='Src', d='Dst',
           returnActualEncoding=False,
           roundUpToMultipleBits=1):
    '''

    "localLinkLabelLens": this must be a map from node to label
    length.

    this is based on codec 3. but here are the differences:

    1) the length of each link label is log-of-node-degree bits
    long. we dont use link id length prefix.

    2) we dont use null link labels. instead:

      a) immediately after each <p-link> will be the number of bits of
      its detour path. this allows the router to know how many bits to
      strip off before forwarding along the primary path. if this is
      zero, then it has no detour path.

      b) the "egress" marker is when the encoding is completely
      empty. zero bits long.

    <on-detour?> | <p-link><d-path-len>[<d-link>...] | <p-link>... | ... 

    <on-detour?>: 1-bit: 0 for "proceeding along primary path." when a
                  router has had to switch to its detour path, should
                  toggle the bit to 1, which means it is now
                  proceeding on a detour path. since we do not "repair
                  a repaired" path, ie, we only care to protect
                  against 1 link failure, when the bit is 1, and the
                  out-link is dead, then drop the packet.


    each primary node should encode its primary link as
    <p-link>.

    <d-path-len>: length in bits of its entire detour path, i.e., all
    the <d-link> labels. <d-path-len> is a variable length field.

    the length spec of this field is:

    0    -- 5 bits
    10   -- 7 bits

    110  -- 0 bits


    the way forwarding/processing works is. coming soon...:

    '''

    class _DPathLenBitString:
        '''
        0    -- 5 bits
        10   -- 7 bits

        110  -- 0 bits
        '''
        def __init__(self, dpathlen):
            assert dpathlen >= 0

            bs = None
            if dpathlen == 0:
                bs = bitstring.BitString('0b110')
                pass
            else:
                if dpathlen < 2**5:
                    length = 5
                    bs = bitstring.BitString('0b0')
                    pass
                elif dpathlen < 2**7:
                    length = 7
                    bs = bitstring.BitString('0b10')
                    pass
                else:
                    raise Exception('dpathlen of %u is too long' % (dpathlen))

                bs.append(bitstring.BitString(length=length, uint=dpathlen))
                pass

            self.bs = bs
            pass

        def getLength(self):
            # the length of the all fields in the bitstring.
            return self.bs.len

        def getBs(self):
            return self.bs
        pass

    class _SuccessorBitString:
        # "linkIdLen" is in units of bits. must be enough to fit
        # localLinkId.

        def __init__(self, localLinkId, linkIdLen,
                     computeLengthOnly=True, u=None,v=None):

            # we're assuming link IDs are 0-based.
            assert localLinkId != None
            assert localLinkId < (2**linkIdLen)

            linkBs = None
            if not computeLengthOnly:
                linkBs = bitstring.BitString(length=linkIdLen, uint=localLinkId)
                pass

            self._totalLength = linkIdLen

            self.linkBs = linkBs
            self.u = u
            self.v = v
            self.localLinkId = localLinkId
            return

        def getLength(self):
            return self._totalLength

        def getBs(self):
            assert self.linkBs != None
            return self.linkBs

        def __str__(self):
            return 's,d=(%s, %s); linkId=%s; bs=%s' % (self.u, self.v, self.localLinkId, self.linkBs)

        pass
        #################################

#    pdb.set_trace()
    thebitstrings = []
    totalLengthInBits = 1 # for the on-detour? bit

    for i in xrange(len(primaryPath) - 1):
        # "node" is original (non-virtual) name and also final name
        # because this is the primary path.

        ###### the primary successor
        node = primaryPath[i]

        linkIdLen = localLinkLabelLens[node]
        totalLengthInBits += linkIdLen

        if returnActualEncoding:
            localLinkId = localLinkIDs[node][primaryPath[i + 1]]
            thebitstrings.append(_SuccessorBitString(
                localLinkId, linkIdLen,
                computeLengthOnly=not returnActualEncoding,
                u=node, v=primaryPath[i + 1]))
            pass

        ##### process the detour path
        dlinklabelBitstrings = []
        dpathLengthInBits = 0

        detourPath = detourPaths.get(node, None)
        if detourPath != None:
            for j in xrange(len(detourPath) - 1): # skip the egress
                _node = detourPath[j]

                linkIdLen = localLinkLabelLens[_node]
                dpathLengthInBits += linkIdLen

                if returnActualEncoding:
                    _localLinkId = localLinkIDs[_node][detourPath[j + 1]]
                    dlinklabelBitstrings.append(
                        _SuccessorBitString(
                        _localLinkId, linkIdLen,
                        computeLengthOnly=not returnActualEncoding,
                        u=_node, v=detourPath[j + 1]))
                    pass
                pass
            pass

        dpathlenBs = _DPathLenBitString(dpathLengthInBits)

        totalLengthInBits += dpathlenBs.getLength() + dpathLengthInBits

        if returnActualEncoding:
            thebitstrings.append(dpathlenBs)
            thebitstrings.extend(dlinklabelBitstrings)
            pass
        pass

    if returnActualEncoding:
        encodingBs = bitstring.BitString('0b0') # the on-detour? bit
        for bs in thebitstrings:
            encodingBs.append(bs.getBs())
            pass
        return encodingBs
    elif roundUpToMultipleBits == 1:
        return totalLengthInBits
    else:
        return int(math.ceil(float(totalLengthInBits)/roundUpToMultipleBits))
    pass


def testRocketFuel3967():
    filepath = '../../../graphs/rocketfuel/3967/weights.intra'
    g, lli = utils.textToG(filepath, useInt=False)
    weighted = True

    testCases = (
        ('317', '431', '01100010101101010001001010100010101010',),

        )

    failureSrcDstPairs = []

    for s,d, expectedString in testCases:
        expectedEncodingBs = bitstring.BitString('0b' + expectedString)

        pp, dp = approach2.getDg(g, s, d, weighted)

        dag = approach2.getDagWithVnodes(
            pp, dp, returnDetourPathsWithVNodes=False)

        encodingBs = encode(
            pp, dp, lli, s, d, returnActualEncoding=True,
            roundUpToMultipleBits=1)

        if encodingBs != expectedEncodingBs:
            failureSrcDstPairs.append((s,d))
            pass

        pass

    func_name = inspect.getframeinfo(inspect.currentframe())[2]

    print 'Test', func_name, 'result:'
    if len(failureSrcDstPairs) == 0:
        print '  passed'
        pass
    else:
        print '  failed'
        print '  The failed src-dst pairs:'
        for s,d in (failureSrcDstPairs):
            print 's,d=%s,%s' %(repr(s),repr(d))
            pass
        pass
    return
