from codec_common import *
import traceback

Revision = '$Revision: 1060 $'
Id = '$Id$'

##################
def encode(dg, primaryPath, virtualDetourPaths, localLinkIDs, optimize1,
               s='Src', d='Dst',
               roundUpToMultipleBits=1, # NOTE!!! this is pointer alignment.
               useLinkIdLenPrefix=True,
               localLinkLabelLens=None,
               returnActualEncoding=False):
    '''

    we have found pointer alignment of 1 performs best. alignment of 1
    means there is no wasted padding, but the pointers have to be
    larger. but proly the wasted padding hurt more.
    
    "useLinkIdLenPrefix": if true, then link labels are variable
    length and use prefix-codes. if false, then all of a node\'s link
    labels use same length, and this length is from
    "localLinkLabelLens" map.

    "localLinkLabelLens": required if "useLinkIdLenPrefix" is
    false. this must be a map from node to label length.

    NOTE: "offset" and "pointer" are used interchangably.

    "returnActualEncoding": if true, will also return the actual
    encoding as a bitstring.BitString object, and the list of node
    names in the order they are encoded/appear in the encoding.

    a "current ptr" value of zero means at
    the destination (router). so in all paths, primary of detour, the
    nodes before the destination router have to contain a ptr of zero.

    also, the destination router does not need to be part of the
    conding because it has no out-links.

    this is trying to reduce encoding size by
    placing nodes that are adjacent in the graph adjacent in the
    encoding, so that each of those nodes can eliminate one
    out-neighbor\'s offset ptr (it can instead include the offset from
    itself, or not include an offset at all and let the router compute
    it).

    more specifically, if a node has two successors, we can place one
    successor node (1st or 2nd--doesnt matter) right after this node
    and thus its "successor" bitstring does not need to contain an
    offset ptr. the other "successor" bitstring has to contain an
    offset ptr.

    if a node has only one successor, then of course that sole
    successor bitstring can skip the offset ptr if the successor Node
    can be placed immediately after this Node.

    So....

    a) group all the nodes in the primary path and all nodes in the
    penultimate primary node\'s detour paths.

    specifically, primary node N will have as its 1st successor
    bitstring its primary successor, ie, primary node N+1, and can
    skip the offset pointer. its 2nd successor bitstring will be its
    detour node, which will require an offset pointer.

    then, since we do not encode the destination router, the
    penultimate primary node will have as its 1st successor bitstring
    an offset ptr value of zero. which means, its 2nd successor, if
    applicable, can be part of the group as well, and the bitstring
    can skip the pointer as well.

    then, we can continue to group in the remaining virtual nodes of
    the penultimate primary node\'s detour path.

    b) then among the detour paths, find the longest sequence of
    [nodes that do not already appear in any group], then group
    them. should have a threshold under which it is no longer worth
    creating a group.

    * <len of ptr><current ptr><Node>[<Node>...]

    - len of ptr: "0" for 4 bits, "10" for 6 bits, "110" for 8 bits,
      "1110" for 10 bits, "11110" for 12 bits, and "111110" for 16
      bits.

      we are using one fixed size ptr throughout a header, so this
      doesnt apply, but if we allow each node to have a different ptr
      size, then the nodes with the higest indegrees should be placed
      earlier in the header to keep the offsets small, because the
      offsets will be referred to by many other nodes.


    * <Node> = <# of successors><Successor>[<Successor>...]

    - # of successors: 1 bit


    * <Successor> = <len of ID><ID><contains ptr?><ptr (if "contains ptr" is true>

    - len of ID: 1 bit: "0" for 4 bits, "1" for 8 bits

    - contains ptr?: 1 bit: "0" for no, in which case, this node is
      part of a "bunch". so, the router is expected to compute the
      offset of the node that follows it into the global "current
      ptr".

    - ptr: its len is from the first part of the header.


    algorithm: the tricky part is to find out the smallest sufficient
    length of ptr. this is clearly recursive because ptrs are part of
    the packet.

    so for now use this iterative algo:

    - assume the length needs to be 4 bits.

    - add everything to get the total length of the packet in number
      of "roundUpToMultipleBits" of bits (WITH individual padding, ie,
      each <Node> should be aligned to "roundUpToMultipleBits" number
      of bits)

    - if that is larger than 4 bits can address, try again with 8
      bits, etc

    '''

    class _NodeBitString:
        def __init__(self, name, outdegree):
            '''
            "name" is the node name.
        
            "outdegree": only 1 and 2 are supported.

            "successors": should be a list of _SuccessorBitString
            objects. caller is responsible for ensuring any needed
            consistency between "outdegree" and "successors".
            '''

            if outdegree == 1:
                headerBs = bitstring.BitString('0b0')
                pass
            elif outdegree == 2:
                headerBs = bitstring.BitString('0b1')
                pass
            else:
                raise Exception("node %s has unexpected outdegree %u" %(node, outdegree))

            self.headerBs = headerBs
            self.successorBsList = []
            self.name = name
            return

        def getBitstring(self, roundUpToMultipleBits,
                         successorOffsetLengthInBits):
            bs = bitstring.BitString(self.headerBs)
            for successorBs in self.successorBsList:
                bs.append(successorBs.getBitstring(
                    offsetLengthInBits=successorOffsetLengthInBits))
                pass
            if roundUpToMultipleBits > 1:
                spill = bs.length % roundUpToMultipleBits
                if spill != 0:
                    # need to pad
                    bs.append(bitstring.BitString(
                        length=roundUpToMultipleBits-spill, uint=0))
                    pass
                pass
            return bs

        def getLength(self, roundUpToMultiple=1,
                      includeSuccessorOffests=True,
                      successorOffsetLengthInBits=None):
            '''
            <"# of successors" bit><Successor>[<Successor>...]

            return the length of this node, including the # of
            successors bit, and all the successors.

            "roundUpToMultiple" is the multiple of bits to round up
            to. for example, total size is 13 bits, and
            roundUpToMultiple is 8, then returned val will be 2,
            because ceil(13/8)=2. thus, roundUpToMultiple of 1 means
            to get the length in bits, 8 means to get the length in
            bytes.

            if "includeSuccessorOffests" is False, then will not count
            the Successors\'s offset ptrs (and their related stuff).

            if "includeSuccessorOffests" is True, then will count the
            offset ptrs. in which case, if
            "successorOffsetLengthInBits" is specified, then will be
            used. otherwise, will use the actual lengths of the
            successor bitstrings.
            '''

            lengthInBits = 1 # num of successors

            for successorBs in self.successorBsList:
                lengthInBits += successorBs.getLength(
                    roundUpToMultiple=1, # this is "1" to get len in bits
                    includeOffsets=includeSuccessorOffests,
                    offsetLengthInBits=successorOffsetLengthInBits)
                pass

            if roundUpToMultiple == 1:
                return lengthInBits
            else:
                raise Exception("should not reach: we have found 1 to be the best, so if not 1, then likely a bug")
                return int(math.ceil(float(lengthInBits)/roundUpToMultiple))
        pass
        #####

    class _SuccessorBitString:
        '''

        * <len of ID>

        * <ID>: length is specified in <len of ID>

        * <contains ptr?>: 1 bit: "0" for no, "1" for yes.

        * <ptr>: this part exists only if <contains ptr?> is "1".

        '''
        def __init__(self, localLinkId, containsPtr, offset=None, name=None,
                     linkIdLen=None):
            # "name" is the node name of this successor. it is not
            # encoded but aids the final stage of encoding: placing
            # actual offsets into the successor bitstrings, which
            # requires looking up the successor's offset. it's
            # required if "containsPtr" is true.

            # "linkIdLen": if specified, should be the number of bits
            # to use for the link id, and the len prefix will be
            # skipped. if None, the len prefix will be determined by
            # the value of the link id.

            self.name = name
            if containsPtr:
                assert (self.name != None)
                pass

            if linkIdLen:
                assert localLinkId < (2 ** linkIdLen)
                length = linkIdLen
                linkBs = bitstring.BitString()
                pass
            else:
                # its len

                # we're assuming link IDs are 0-based.
                if localLinkId < 8:
                    linkBs = bitstring.BitString('0b0')
                    length = 3
                    pass
                elif localLinkId < 64:
                    linkBs = bitstring.BitString('0b10')
                    length = 6
                    pass
                else:
                    assert localLinkId < (2 ** 12), "localLinkId too big"
                    linkBs = bitstring.BitString('0b110')
                    length = 12
                    pass
                pass

            # the ID itself
            linkBs.append(bitstring.BitString(length=length, uint=localLinkId))

            self.linkBs = linkBs
            self.offset = None
            self.containsPtr = containsPtr
            return

        def getBitstring(self, offsetLengthInBits):
            # get the full bitstring, not leaving out anything

            bs = bitstring.BitString(self.linkBs)

            if self.containsPtr:
                assert self.offset != None
                assert self.offset < (2**offsetLengthInBits)

                bs.append(bitstring.BitString(length=1, uint=1))
                bs.append(bitstring.BitString(length=offsetLengthInBits,
                                              uint=self.offset))
                pass
            else:
                bs.append(bitstring.BitString(length=1, uint=0))
                pass

            return bs

        def getLength(self, roundUpToMultiple=1,
                      includeOffsets=False,
                      offsetLengthInBits=None):

            if includeOffsets and self.containsPtr:
                if offsetLengthInBits == None:
                    raise Exception("nyi")
                    lengthInBits = self.linkBs.length + self.offsetBs.length
                    pass
                else:
                    lengthInBits = self.linkBs.length + offsetLengthInBits
                    pass
                pass
            else:
                lengthInBits = self.linkBs.length
                pass

            # for the the "containsPtr?" bit
            lengthInBits += 1

            if roundUpToMultiple == 1:
                return lengthInBits
            else:
                raise Exception("should not reach")
                return int(math.ceil(float(lengthInBits)/roundUpToMultiple))

        pass
        #################################

    if useLinkIdLenPrefix:
        assert localLinkLabelLens
        pass

    # map from final node names to their bitstrings, eg, "foo" and
    # "foo~blah" are two different keys.
    bitstrings = {}

    # this list contains the same bitstring elements, but will be in
    # the order in which they are added.
    listBitstrings = []

    # handle the primary path, skipping the destination because it
    # doesnt need a node
    for i in xrange(len(primaryPath) - 1):
        # "node" is original (non-virtual) name and also final name
        # because this is the primary path.
        node = primaryPath[i]

        bs = _NodeBitString(node, dg.out_degree(node))

        isPenultimateNode = (i == (len(primaryPath) - 2))

        if useLinkIdLenPrefix:
            linkIdLen = None
            pass
        else:
            linkIdLen = localLinkLabelLens[node]
            pass

        ###### add the primary successor
        localLinkId = localLinkIDs[node][primaryPath[i + 1]]
        if not isPenultimateNode:
            successorBs = _SuccessorBitString(localLinkId, False,
                                              linkIdLen=linkIdLen)
            pass
        else:
            # penultimate node -> contain ptr (of value zero)
            successorBs = _SuccessorBitString(localLinkId, True,
                                              linkIdLen=linkIdLen,
                                              name=primaryPath[i + 1])
            pass
        bs.successorBsList.append(successorBs)

        ##### add any detour successor
        import copy
        successors = copy.copy(dg.successors(node))
        successors.remove(primaryPath[i + 1]) # remove primary successor
        assert len(successors) <= 1

        if len(successors) == 1:
            successor = successors[0]
            # need the successor's original (non-virtual) node name to
            # look up in localLinkIDs
            originalsuccessorname = re.match(vnodePattern, str(successor))
            if originalsuccessorname != None:
                originalsuccessorname = originalsuccessorname.group(1)
                pass
            else:
                originalsuccessorname = successor
                pass

            localLinkId = localLinkIDs[node][originalsuccessorname]
            if not isPenultimateNode:
                successorBs = _SuccessorBitString(localLinkId, True,
                                                  linkIdLen=linkIdLen,
                                                  name=successor)
                pass
            else:
                # penultimate node -> do NOT include the ptr. we will
                # place the successor's node descriptor immediately
                # after this.
                successorBs = _SuccessorBitString(localLinkId, False,
                                                  linkIdLen=linkIdLen)
                pass
            bs.successorBsList.append(successorBs)
            pass

        #####
        assert node not in bitstrings
        bitstrings[node] = bs
        listBitstrings.append(bs)
        pass

    # just finished the primary path, now continue with the 2nd part
    # of the first group: the penultimate primary node's detour path,
    # if exists. it is actually handled like all other detour paths:
    # they all start with a primary node and merge back into a primary
    # node, possibly the destination node.

    def _processDetourNodes(vdp):
        # skip first and last nodes, which are always primary nodes
        for i in xrange(1, len(vdp) - 1):
            node = vdp[i]
            if node in bitstrings:
                # already processed. assume all subsequent nodes are
                # already processed, too
                break
            bs = _NodeBitString(node, 1)

            successor = vdp[i + 1]

            # need original names to get the link id
            originalnodename = re.match(vnodePattern, str(node))
            if originalnodename != None:
                originalnodename = originalnodename.group(1)
                pass
            else:
                originalnodename = node
                pass
            originalsuccessorname = re.match(vnodePattern, str(successor))
            if originalsuccessorname != None:
                originalsuccessorname = originalsuccessorname.group(1)
                pass
            else:
                originalsuccessorname = successor
                pass

            if useLinkIdLenPrefix:
                linkIdLen = None
                pass
            else:
                linkIdLen = localLinkLabelLens[originalnodename]
                pass

            try:
                localLinkId = localLinkIDs[originalnodename][originalsuccessorname]
            except Exception, e:
                print 'WARNING: s=%s,d=%s,originalnodename=%s,originalsuccessorname=%s: exception:\n' % (s,d,originalnodename,originalsuccessorname)
                traceback.print_exc()
                raise e
                pass
            # if successor is a primary node (possibly destination) or
            # an already-processed detour node, then we need to use a
            # pointer
            if (successor in primaryPath) or (successor in bitstrings):
                successorBs = _SuccessorBitString(localLinkId, True,
                                                  linkIdLen=linkIdLen,
                                                  name=successor)
                pass
            else:
                successorBs = _SuccessorBitString(localLinkId, False,
                                                  linkIdLen=linkIdLen)
                pass
            bs.successorBsList.append(successorBs)

            assert node not in bitstrings
            bitstrings[node] = bs
            listBitstrings.append(bs)
            pass
        pass
    ####

    # Optimization: among the detour paths, find the longest portion
    # that contains yet-to-be-processed; virtual primary nodes--those
    # created to do backtracking--are counted because they are
    # distinct nodes in the graph and encoding. keep in mind that a
    # detour path starts with a primary node, which is already taken
    # care of above.

    if optimize1:
        unprocessedDetourPaths = virtualDetourPaths.values()
        while len(unprocessedDetourPaths) > 0:
            # find the dpath with the longest contiguous portion of
            # unprocessed nodes, process it, remove it from the list,
            # then repeat.
            idx2LengthTuples = []
            for idx, path in enumerate(unprocessedDetourPaths):
                length = 0
                for node in path[1:-1]:
                    if node in bitstrings:
                        break
                    else:
                        length += 1
                        pass
                    pass
                idx2LengthTuples.append((idx, length))
                pass
            idx2LengthTuples.sort(key=lambda t: t[1], reverse=True)
            _processDetourNodes(unprocessedDetourPaths.pop(idx2LengthTuples[0][0]))
            pass
        pass
    else:
        # encode the penultimate primary node's detour path first, if
        # any, before encoding other detour paths
        _s = set(virtualDetourPaths.keys())
        penultimatePNode = primaryPath[-2]
        if penultimatePNode in _s:
            _s.remove(penultimatePNode)
            assert not (penultimatePNode in _s)
            _processDetourNodes(virtualDetourPaths[penultimatePNode])
            pass
        for pnode in _s:
            _processDetourNodes(virtualDetourPaths[pnode])
            pass
        pass

    # we must have all bitstrings for all nodes in the dag, except the
    # destination
    assert set(bitstrings.keys()) == (set(dg.nodes()).difference(set([d])))

    # from experiments, majority of average ptr size is ~8 bits (for
    # byte- and nybble-aligned).  so, we SHOULD try offsetLength = 8
    # bits first, if not enough, then we have underestimated ->
    # simple, try again with (offsetLength + N) bits.  overestimation
    # detection is a little more involved: if [(total *
    # roundUpToMultipleBits) - (N * numEdges) - N] is less than (or equal
    # to) 2^(offsetLength - N), then we have overestimated and should
    # try again with (offsetLength - N) bits.
    #
    # "- (N * numEdges) - N" is AT LEAST the number of bits we would
    # save if we used (offsetLength - N). "AT LEAST" because of effect
    # of padding to align. "- N" is for the single ptr in the main
    # area of the header.

    assert len(bitstrings) == len(listBitstrings)

    node2Offset = {}

    offsetLengthsToTry = [4, 6, 8, 10, 12, 16] # in bits
    for i, offsetLengthToTry in enumerate(offsetLengthsToTry):
#        _debug('offsetLengthToTry [%d]' % offsetLengthToTry)

        # tally up the length of the packet with this offset length

        # NOTE: this is not always in bits, but is in
        # "roundUpToMultipleBits" number of bits, because that's what
        # "getLength()" will return.
        packetLength = PacketHeaderBitString(offsetLengthToTry).getLength(roundUpToMultiple=roundUpToMultipleBits)

        currentOffset = packetLength
        node2Offset.clear()

        for bs in listBitstrings:
            node2Offset[bs.name] = currentOffset
            packetLength += bs.getLength(
                roundUpToMultiple=roundUpToMultipleBits,
                includeSuccessorOffests=True,
                successorOffsetLengthInBits=offsetLengthToTry)
            currentOffset = packetLength
            pass

#        _debug('packet length [%d]' % packetLength)

        if packetLength > (2 ** offsetLengthToTry):
            # if the number of required bits is greater the current
            # offsetLength, then we need more bits.
            continue
        else:
            # we have enough bits -> break
            break
        pass

    if returnActualEncoding:
        # now, actually get the final bitstring, with everything,
        # including the offset pointers, in place
        node2Offset[primaryPath[-1]] = 0

        encodingBs = PacketHeaderBitString(offsetLengthToTry,
                                           offset=node2Offset[primaryPath[0]]).getBitstring(roundUpToMultiple=roundUpToMultipleBits)

        assert (encodingBs.length % roundUpToMultipleBits) == 0

        nodeNames = []
        for nodeBs in listBitstrings:
            # need to set the successors' offsets before being able to
            # call getBitstring() on them.
            for successorBs in nodeBs.successorBsList:
                if successorBs.containsPtr:
                    successorBs.offset = node2Offset[successorBs.name]
                    pass
                pass
            encodingBs.append(
                nodeBs.getBitstring(roundUpToMultipleBits=roundUpToMultipleBits,
                                    successorOffsetLengthInBits=offsetLengthToTry))
            nodeNames.append(nodeBs.name)
            pass

        return encodingBs, offsetLengthToTry, nodeNames
    else:
        return packetLength, offsetLengthToTry
