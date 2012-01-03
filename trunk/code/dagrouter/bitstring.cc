/* $Id$ */

#include <assert.h>
#include <stdlib.h>
#include <string.h>
#include "bitstring.h"

/* using a char array to represent a bitstring */

bitstring newBitString(const unsigned int& numBits)
{
    int numChars = numBits / 8;

    assert (numBits > 0);
    
    if ((numBits % 8) != 0) {
        numChars += 1;
    }

    return (bitstring)calloc(numChars, 1);
}

bitstring newBitStringFromBoolArray(const bool boolArray[],
                                    const unsigned int& arrayLength)
{
    assert (arrayLength > 0);
    bitstring bs = newBitString(arrayLength);
    for (int i = 0; i < arrayLength; i++) {
        setValIntoBitstring(bs, i, 1, boolArray[i]);
    }
    return bs;
}

void freeBitString(bitstring* bits){
    free(*bits);
    *bits = NULL;
}

/* big-endian: "bitnum" 0 means the most significant bit */
bool getBitInBs(const bitstring bits,
                const unsigned int& bitNum)
{
    int charNum = bitNum / 8;
    int bitNumInChar = bitNum % 8;
    unsigned char c = bits[charNum];

    return GET_BIT_IN_CHAR(c, bitNumInChar);
}
    
/*
 * big-endianness: bit at index (0+fromIdx) will be the most
 * significant bit in the returned integer value.
 *
 * "numBits" is the number of bits to use, not the total length of the
 * bitstring. must be <= 32.
 *
 * assumes that fromIdx and numBits are valid for the bitstring.
 */
int getValFromBitstring(const bitstring bits,
                      const unsigned int& fromIdx,
                      const unsigned int& numBits)
{
    assert (numBits > 0 && numBits <= 32);

    /* process the bits from right to left (least significant to most
     * significant)
     */

    int val = 0;
    int charNum = (fromIdx + numBits - 1) / 8;
    int bitNumInChar = (fromIdx + numBits - 1) % 8;
    int numProcessedBits = 0;

    do {
        unsigned char c = bits[charNum] >> (8 - bitNumInChar - 1);
        for (; (bitNumInChar >= 0) && (numProcessedBits < numBits);
             bitNumInChar--, numProcessedBits++)
        {
            if (c & 1) {
                val |= (1 << numProcessedBits);
            }
            else {
                val &= ~(1 << numProcessedBits);
            }
            c >>= 1;
        }
        charNum--;
        // reset bitnuminchar
        bitNumInChar = 7;
    }
    while (numProcessedBits < numBits);

    return val;
}

int setValIntoBitstring(bitstring bits,
                        const unsigned int& fromIdx,
                        const unsigned int& numBits,
                        unsigned int val)
{
    assert (numBits > 0 && numBits <= 32);

    /* process the bits from right to left (least significant to most
     * significant)
     */

    int charNum = (fromIdx + numBits - 1) / 8;
    int bitNumInChar = (fromIdx + numBits - 1) % 8;
    int numProcessedBits = 0;

    do {
        for (; (bitNumInChar >= 0) && (numProcessedBits < numBits);
             bitNumInChar--, numProcessedBits++)
        {
            if (val & 1) {
                bits[charNum] |= (1 << (7 - bitNumInChar));
            }
            else {
                bits[charNum] &= ~(1 << (7 - bitNumInChar));
            }
            val >>= 1;
        }
        charNum--;
        // reset bitnuminchar
        bitNumInChar = 7;
    }
    while (numProcessedBits < numBits);

    return 0;
}

/************************************************************************/
int findFirstInBitstring(const bitstring bits,
                         const unsigned int& bit,
                         const unsigned int& fromIdx,
                         const unsigned int& numBits)
{
    assert (numBits > 0);
    assert (bit == 0 || bit == 1);

    int charNum = fromIdx / 8;
    int bitNumInChar = fromIdx % 8;
    int numProcessedBits = 0;

    do {
        unsigned char c = bits[charNum];
        for (; (bitNumInChar < 8) && (numProcessedBits < numBits);
             bitNumInChar++, numProcessedBits++)
        {
            // GET_BIT_IN_CHAR gives non-zero if bit is set.
            unsigned int b = GET_BIT_IN_CHAR(c, bitNumInChar);
            if ((b == 0 && bit == 0) || (b != 0 && bit == 1)) {
                return fromIdx + numProcessedBits;
            }
            else {
                // continue to look at next bit
            }
        }
        charNum++;
        bitNumInChar = 0;
    }
    while (numProcessedBits < numBits);

    return -1;
}

int removeFromBitstring(bitstring bits,
                        const unsigned int& origNumBits,
                        const unsigned int& atIdx,
                        const unsigned int& numBitsToRemove)
{
    assert (origNumBits > 0 && numBitsToRemove < origNumBits);
    assert ((atIdx + numBitsToRemove) <= origNumBits);

#undef CHUNK_SIZE
#define CHUNK_SIZE (32)

    /* copy inplace "fromIdx" to "toIdx" (fromIdx is greater than
     * toIdx) */

    unsigned int fromIdx = atIdx + numBitsToRemove;
    unsigned int toIdx = atIdx;

    while (fromIdx < origNumBits) {
        int val = 0;
        int thischunksize = origNumBits - fromIdx;
        if (thischunksize > CHUNK_SIZE) {
            thischunksize = CHUNK_SIZE;
        }
        val = getValFromBitstring(bits, fromIdx, thischunksize);
        setValIntoBitstring(bits, toIdx, thischunksize, val);

        fromIdx += thischunksize;
        toIdx += thischunksize;
    }

    return 0;
}

/***************************************************/

int getVarLenValFromBitstring(bitstring bs,
                              const unsigned int& bsLen,
                              const unsigned int& fromIdx,
                              const unsigned int numSetBits2Len[],
                              const unsigned int& arraySize,
                              unsigned int* ret_val,
                              unsigned int* ret_lenSpecNumBits,
                              unsigned int* ret_totalNumBits)
{
    if (fromIdx >= bsLen) {
        return -1;
    }

    // find the zero-terminator
    int idxOfZero = findFirstInBitstring(bs, 0, fromIdx, arraySize);

    if (idxOfZero < fromIdx || idxOfZero >= (fromIdx + arraySize)) {
        // out of bounds
        return -1;
    }

    assert (bsLen > 0);

    unsigned int len = numSetBits2Len[idxOfZero - fromIdx];

    assert (len <= 32);

    if ((idxOfZero + len) >= bsLen) {
        // out of bounds
        return -1;
    }

    if (ret_lenSpecNumBits) {
        *ret_lenSpecNumBits = (idxOfZero - fromIdx) + 1;
    }

    if (ret_totalNumBits) {
        *ret_totalNumBits = ((idxOfZero - fromIdx) + 1) + (len);
    }

    if (0 == len) {
        // zero length
        return -2;
    }

    if (ret_val) {
        *ret_val = getValFromBitstring(bs, idxOfZero+1, len);
    }

    return 0;
}
