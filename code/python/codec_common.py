import bitstring
import re
import math

Revision = '$Revision: 406 $'
Id = '$Id$'

vnodePattern = re.compile("^([a-zA-Z0-9]+)~[a-zA-Z0-9]+$")

# map from the length of the ptr to the len of its "len" field
offsetPtrLenFieldLenMap = {
    10 : 1, # 0b0
    8: 2,   # 0b10
    6: 3,   # 0b110
    4: 4,   # 0b1110
}


class PacketHeaderBitString:
    def __init__(self, offsetLengthInBits, offset=None):
        offsetPtrLenFieldLen = offsetPtrLenFieldLenMap.get(offsetLengthInBits, None)
        assert offsetPtrLenFieldLen != None, \
               'invalid offsetLengthInBits: %d' % (offsetLengthInBits)

        # (offsetPtrLenFieldLen - 1) number bits of 1 followed by 1
        # bit of 0.
        bs = bitstring.BitString('0b%s0' % ('1' * (offsetPtrLenFieldLen - 1)))

        self.bs = bs
        self.offsetLengthInBits = offsetLengthInBits
        self.offset = offset
        return

    def getBitstring(self, roundUpToMultiple):
        assert self.offset != None
        assert self.offset < (2**self.offsetLengthInBits)
        bs = bitstring.BitString(self.bs)
        bs.append(bitstring.BitString(length=self.offsetLengthInBits,
                                      uint=self.offset))
        if roundUpToMultiple > 1:
            spill = bs.length % roundUpToMultiple
            if spill != 0:
                # need to pad
                bs.append(bitstring.BitString(length=roundUpToMultiple-spill,
                                              uint=0))
                pass
            pass
        return bs

    def getLength(self, roundUpToMultiple=1):
        lengthInBits = self.bs.length + self.offsetLengthInBits

        return int(math.ceil(float(lengthInBits)/roundUpToMultiple))
