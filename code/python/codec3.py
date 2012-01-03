from codec_common import *
import utils
import approach2
import inspect

Revision = '$Revision: 484 $'
Id = '$Id$'

###################################################################3
def encode(primaryPath, detourPaths, localLinkIDs,
               s='Src', d='Dst',
           returnActualEncoding=False,
               roundUpToMultipleBits=8):
    '''



    <on-detour?> | <p-link><d-link>...<null-link> | <p-link><null-link> | ... | <null-link>

    <on-detour?>: 1-bit: 0 for "proceeding along primary path." when a
                  router has had to switch to its detour path, should
                  toggle the bit to 1, which means it is now
                  proceeding on a detour path. since we do not "repair
                  a repaired" path, ie, we only care to protect
                  against 1 link failure, when the bit is 1, and the
                  out-link is dead, then drop the packet.


    each primary node should encode its primary link as
    <p-link>. then, if it has a detour path, it should encode the
    entire path, potentially including other primary nodes, as a
    sequence of <d-link>\'s, ended by a <null-link>.

    each link is <length><link value> where:

    * <length> begins with bit 1:
       10   for 3 bits
       110  for 6 bits
       1110 for 11 bits

    * special <null-link> is just one bit 0, i.e., length field is a
      single bit of zero, and no <link value> field.

    the <null-link> also serves as the path "terminator" for the
    detour path. if the detour path is empty, it still must have a
    <null-link>. so at the end of the encoding, it should always be
    two <null-link>, the first one terminating the previous primary
    node\'s detour path, and the second one terminating that primary
    node\'s primary path.

    the way forwarding/processing works is:

    <verbatim>
    begin:
    link label L = label at the front of the encoding

    if link L is <null-link>:
        # i am the egress/destination router, do whatever ...
    elif link L works:
        if <on-detour?> is 0:
            strip off link labels at front of encoding one-by-one until
            and including the <null-link>
        else:
            strip only link L
        fi
        forward out link L
    else:
        if <on-detour?> is 0:
            peek at the next link label Lnext
            if link Lnext is <null-link>:
                # a primary node that does not have a detour path
                drop packet
            else:
                set <on-detour?> to 1
                strip off link L
                goto "begin:"
            fi
        else:
            drop packet
        fi
    fi
    </verbatim>

    '''

##     class LinkLabelBitString:

    class _SuccessorBitString:
        # special "localLinkId" of None to make it a <null-link>

        #         0    for 0 bits, i.e., special null-link
        #         10   for 3 bits
        #         110  for 6 bits
        #         1110 for 11 bits

        def __init__(self, localLinkId, computeLengthOnly=True, u=None,v=None):
            # the length of the entire link label including the length
            # field and the value field.

            linkBs = None
            # we're assuming link IDs are 0-based.
            if localLinkId is None:
                # special <null-link>
                length = 1
                if not computeLengthOnly:
                    linkBs = bitstring.BitString('0b0')
                    pass
                pass
            elif localLinkId < 8:
                length = 2 + 3 # len("10") + 3 bit value
                if not computeLengthOnly:
                    linkBs = bitstring.BitString('0b10')
                    linkBs.append(bitstring.BitString(length=3, uint=localLinkId))
                    pass
                pass
            elif localLinkId < 64:
                length = 3 + 6 # "110" + 6 bit value
                if not computeLengthOnly:
                    linkBs = bitstring.BitString('0b110')
                    linkBs.append(bitstring.BitString(length=6, uint=localLinkId))
                    pass
                pass
            else:
                assert localLinkId < (2 ** 11), "localLinkId too big"
                length = 4 + 11
                if not computeLengthOnly:
                    linkBs = bitstring.BitString('0b1110')
                    linkBs.append(bitstring.BitString(length=11, uint=localLinkId))
                    pass
                pass

            self._totalLength = length

            self.linkBs = linkBs
            self.u = u
            self.v = v
            self.localLinkId = localLinkId
            return

        def getLength(self):
            # this returns the total length in bits of this link
            # label, counting all fields, ie, legnth field and value
            # field.
            return self._totalLength

        def getBs(self):
            assert self.linkBs != None
            return self.linkBs

        def __str__(self):
            return 's,d=(%s, %s); linkId=%s; bs=%s' % (self.u, self.v, self.localLinkId, self.linkBs)

        pass
        #################################

#    pdb.set_trace()
    linklabelbitstrings = []

    for i in xrange(len(primaryPath) - 1):
        # "node" is original (non-virtual) name and also final name
        # because this is the primary path.
        node = primaryPath[i]

        ###### add the primary successor
        localLinkId = localLinkIDs[node][primaryPath[i + 1]]
        linklabelbitstrings.append(_SuccessorBitString(localLinkId,
                                                       computeLengthOnly=not returnActualEncoding,
                                                       u=node,
                                                       v=primaryPath[i + 1]))

        ##### process the detour path, which must always end with
        ##### <null-link>, even if the path is empty
        detourPath = detourPaths.get(node, None)
        if detourPath != None:
            for j in xrange(len(detourPath) - 1):
                _node = detourPath[j]
                _localLinkId = localLinkIDs[_node][detourPath[j + 1]]
                linklabelbitstrings.append(_SuccessorBitString(_localLinkId,
                                                               computeLengthOnly=not returnActualEncoding,
                                                               u=_node,
                                                               v=detourPath[j + 1]))
                pass
            pass
        # null-terminate the detour path
        linklabelbitstrings.append(_SuccessorBitString(None,
                                                       computeLengthOnly=not returnActualEncoding))
        pass

    # null-terminate the primary path
    linklabelbitstrings.append(_SuccessorBitString(None,
                                                   computeLengthOnly=not returnActualEncoding))

    # plus 1 for the <on-detour?> bit
    lengthInBits = 1 + sum(map(lambda llbs: llbs.getLength(), linklabelbitstrings))

    if returnActualEncoding:
        encodingBs = bitstring.BitString('0b0') # the on-detour? bit
        for bs in linklabelbitstrings:
            encodingBs.append(bs.getBs())
            pass
        return encodingBs
    if roundUpToMultipleBits == 1:
        return lengthInBits
    else:
        return int(math.ceil(float(lengthInBits)/roundUpToMultipleBits))
    pass


def testRocketFuel3967():
    filepath = '../../../graphs/rocketfuel/3967/weights.intra'
    g, lli = utils.textToG(filepath, useInt=False)
    weighted = True

    testCases = (
        ('317', '431', '010011100011001010001010001100101001001000110000100101001000',),

        )

    failureSrcDstPairs = []

    for s,d, expectedString in testCases:
        expectedEncodingBs = bitstring.BitString('0b' + expectedString)

        pp, dp = approach2.getDg(g, s, d, weighted)

        ## dag = approach2.getDagWithVnodes(
        ##     pp, dp, returnDetourPathsWithVNodes=False)

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
