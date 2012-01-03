/* $Id$ */

#include <assert.h>

/* using a char array to represent a bitstring
 *
 *
 !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
 !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!

 * NOTE/XXX unless otherwise specified, all functionality here assumes
 * big-endianness: "bitnum" 0 means the most significant bit

 !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
 !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!

 */

typedef unsigned char* bitstring;

/* NOTE: this gives 0 if bit is cleared, non-zero (not necessarily 1)
 * if bit is set */
#define GET_BIT_IN_CHAR(c, bitnum) \
    ((c) & (1 << (8 - (bitnum) - 1)))

bitstring newBitString(const unsigned int& numBits);
bitstring newBitStringFromBoolArray(const bool boolArray[],
                                    const unsigned int& arrayLength);
void freeBitString(bitstring* bits);

/* this gives 0 if bit is cleared, non-zero (not necessarily 1) if bit
 * is set.
 *
 * can also get similar effect out of "bitstringToInt()".
 */
#define GET_BIT_IN_BS(bs, bitNum) \
    GET_BIT_IN_CHAR((bs)[(bitNum) / 8] , (bitNum) % 8)

/*
 * convert a sub-sequence of bits, starting at "fromIdx", in "bits" to
 * an integer value.
 *
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
                        const unsigned int& numBits);

/*
 * set the "val" into the bitstring "bits"
 *
 * "fromIdx" is the bit position within the bitstring at which to
 * start setting the "val."
 *
 * "numBits" is the number of bits of "val" to use, not the total
 * length of the bitstring. must be <= 32.
 *
 * assumes that fromIdx and numBits are valid for the bitstring.
 */
int setValIntoBitstring(bitstring bits,
                        const unsigned int& fromIdx,
                        const unsigned int& numBits,
                        unsigned int val);

/*
 * find the first occurrence in bitstring "bits" of the bit "bit"
 * starting at index "fromIdx". look at at most "numBits" bits.
 *
 * "bit" is the bit to search for: must be 0 or 1.
 *
 * returns -1 if not found.
 */
int findFirstInBitstring(const bitstring bits,
                         const unsigned int& bit,
                         const unsigned int& fromIdx,
                         const unsigned int& numBits);

/*
 * remove IN PLACE "numBitsToRemove" from bitstring "bits", starting
 * at "atIdx"
 *
 * "origNumBits" is the length of "bits" before removal.
 *
 */
int removeFromBitstring(bitstring bits,
                        const unsigned int& origNumBits,
                        const unsigned int& atIdx,
                        const unsigned int& numBitsToRemove);

/* get a variable-length val out of a bitstring, starting at the
 * "fromIdx"th bit.
 *
 * the expected format is: length spec, optionally followed by the val
 * itself.
 *
 * the length spec is a sequence of N set (1) bits and always
 * terminates at the first cleared (0) bit. N can be zero.
 *
 * [1...]0
 *
 * the value of N maps to the length of the value. this mapping is
 * provided in the "numSetBits2Len" array, where the array indices are
 * values of N, and the corresponding array elements are the lengths
 * of the value.
 *
 * if the length of the value is 0, then there is no value. the length
 * must be <= 32.
 *
 *
 * "bsLen" is the total length in bits of the bitstring bs. it is an
 * error if processing would have to go past the length.
 *
 * "arraySize": size of the "numSetBits2Len" array.
 *
 * "ret_val": if not NULL, this will the value, if applicable, from
 * the bitstring.
 *
 * "ret_lenSpecNumBits": if not NULL, will be the number of bits in
 * the length spec (INCLUDING the zero-terminator).
 *
 * "ret_totalNumBits": if not NULL, will be the total number of bits
 * occupied by this value, INCLUDING the length spec.
 *
 * returns: -1 on errors, -2 if there's no value, 0 if there is a
 * value.
 *
 * examples:
 *
 * suppose fromIdx = 0, and numSetBits2Len[] = {3, 0, 1,}, in other
 * words, if there are 2 set bits, i.e., "110", then the value is only
 * 1 bit.
 *
 * bs         | ret_val | ret_totalNumBits | ret_lenSpecNumBits | return code
 * 0110101... | 6       | 4                | 1                  | 0
 * 1011010... | n/a     | 2                | 2                  | -2
 * 1101101... | 1       | 4                | 3                  | 0
 * 1110110... | 3       | n/a              | n/a                | -1 (N > 2)
 */
int getVarLenValFromBitstring(bitstring bs,
                              const unsigned int& bsLen,
                              const unsigned int& fromIdx,
                              const unsigned numSetBits2Len[],
                              const unsigned int& arraySize,
                              unsigned int* ret_val,
                              unsigned int* ret_lenSpecNumBits,
                              unsigned int* ret_totalNumBits);
