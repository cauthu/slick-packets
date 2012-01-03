/* $Id$ */

#include <assert.h>
#include <stdlib.h>
#include <string.h>
#include "../bitstring.h"
#include "../utils.h"

int testFindFirstInBitstring()
{
    bitstring bs = newBitString(256);

    bs[0] = 0b01010011;
    bs[1] = 0b11000100;
    bs[2] = 0b00000000;
    bs[3] = 0b11111111;
    bs[4] = 0b11111111;
    bs[5] = 0b11111110;

    assert (0 == findFirstInBitstring(bs, 0, 0, 1));
    assert (0 == findFirstInBitstring(bs, 0, 0, 2));
    assert (0 == findFirstInBitstring(bs, 0, 0, 3));

    assert (-1 == findFirstInBitstring(bs, 1, 0, 1));
    assert ( 1 == findFirstInBitstring(bs, 1, 0, 2));
    assert ( 1 == findFirstInBitstring(bs, 1, 0, 3));

    assert (4 == findFirstInBitstring(bs, 0, 4, 1));
    assert (4 == findFirstInBitstring(bs, 0, 4, 2));
    assert (4 == findFirstInBitstring(bs, 0, 4, 9));
    assert (4 == findFirstInBitstring(bs, 0, 4, 27));

    assert (-1 == findFirstInBitstring(bs, 1, 4, 1));
    assert (-1 == findFirstInBitstring(bs, 1, 4, 2));
    assert ( 6 == findFirstInBitstring(bs, 1, 4, 9));
    assert ( 6 == findFirstInBitstring(bs, 1, 4, 27));

    assert (-1 == findFirstInBitstring(bs, 0, 6, 1));
    assert (-1 == findFirstInBitstring(bs, 0, 6, 2));
    assert (-1 == findFirstInBitstring(bs, 0, 6, 3));
    assert (-1 == findFirstInBitstring(bs, 0, 6, 4));

    assert (10 == findFirstInBitstring(bs, 0, 6, 5));
    assert (10 == findFirstInBitstring(bs, 0, 6, 6));
    assert (10 == findFirstInBitstring(bs, 0, 6, 9));
    assert (10 == findFirstInBitstring(bs, 0, 6, 13));

    assert (-1 == findFirstInBitstring(bs, 1, 14, 1));
    assert (-1 == findFirstInBitstring(bs, 1, 14, 2));
    assert (-1 == findFirstInBitstring(bs, 1, 14, 3));
    assert (-1 == findFirstInBitstring(bs, 1, 14, 10));

    assert (24 == findFirstInBitstring(bs, 1, 14, 11));
    assert (24 == findFirstInBitstring(bs, 1, 14, 20));

    assert (-1 == findFirstInBitstring(bs, 0, 24, 11));
    assert (-1 == findFirstInBitstring(bs, 0, 24, 20));
    assert (-1 == findFirstInBitstring(bs, 0, 24, 23));
    assert (47 == findFirstInBitstring(bs, 0, 24, 24));

    freeBitString(&bs);
    return 0;
}

int testGetValFromBitstring()
{
    bitstring bs = newBitString(256);

    /* these assign chars */
    bs[0] = 83;  /* 01010011 */
    bs[1] = 197; /* 11000101 */
    bs[2] = 218; /* 11011010 */
    bs[3] = 74;  /* 01001010 */
    bs[4] = 181; /* 10110101 */

    /* one bit */
    assert (0 == getValFromBitstring(bs, 0, 1));
    assert (1 == getValFromBitstring(bs, 1, 1));
    assert (0 == getValFromBitstring(bs, 2, 1));
    assert (1 == getValFromBitstring(bs, 3, 1));
    assert (0 == getValFromBitstring(bs, 4, 1));
    assert (0 == getValFromBitstring(bs, 5, 1));
    assert (1 == getValFromBitstring(bs, 6, 1));
    assert (1 == getValFromBitstring(bs, 7, 1));

    assert (1 == getValFromBitstring(bs, 8, 1));
    assert (1 == getValFromBitstring(bs, 9, 1));
    assert (0 == getValFromBitstring(bs, 10, 1));
    assert (0 == getValFromBitstring(bs, 11, 1));
    assert (0 == getValFromBitstring(bs, 12, 1));
    assert (1 == getValFromBitstring(bs, 13, 1));
    assert (0 == getValFromBitstring(bs, 14, 1));
    assert (1 == getValFromBitstring(bs, 15, 1));

    /* multiple bits */

    assert (2 == getValFromBitstring(bs, 0, 3));
    assert (5 == getValFromBitstring(bs, 0, 4));
    assert (5 == getValFromBitstring(bs, 1, 3));
    assert (83 == getValFromBitstring(bs, 0, 8));
    assert (83 == getValFromBitstring(bs, 1, 7));

    assert (30 == getValFromBitstring(bs, 5, 6));
    assert (60 == getValFromBitstring(bs, 5, 7));
    assert (120 == getValFromBitstring(bs, 5, 8));
    assert (241 == getValFromBitstring(bs, 5, 9));
    assert (482 == getValFromBitstring(bs, 5, 10));
    assert (965 == getValFromBitstring(bs, 5, 11));
    assert (1931 == getValFromBitstring(bs, 5, 12));
    
    assert (69 == getValFromBitstring(bs, 9, 7));
    assert (139 == getValFromBitstring(bs, 9, 8));
    assert (279 == getValFromBitstring(bs, 9, 9));
    assert (558 == getValFromBitstring(bs, 9, 10));
    assert (1117 == getValFromBitstring(bs, 9, 11));
    assert (2235 == getValFromBitstring(bs, 9, 12));
    assert (4470 == getValFromBitstring(bs, 9, 13));
    assert (8941 == getValFromBitstring(bs, 9, 14));
    assert (17882 == getValFromBitstring(bs, 9, 15));
    assert (35764 == getValFromBitstring(bs, 9, 16));
    assert (71529 == getValFromBitstring(bs, 9, 17));

    assert (73245867 == getValFromBitstring(bs, 9, 27));

    freeBitString(&bs);
}

int testSetValIntoBitstring()
{
    bitstring bs = newBitString(256);

    /* these assign chars */
    bs[0] = 83;  /* 01010011 */
    bs[1] = 197; /* 11000101 */
    bs[2] = 218; /* 11011010 */
    bs[3] = 74;  /* 01001010 */

    assert (83 == getValFromBitstring(bs, 0, 8));
    assert (197 == getValFromBitstring(bs, 8, 8));
    assert (218 == getValFromBitstring(bs, 16, 8));
    assert (74 == getValFromBitstring(bs, 24, 8));

    /* set one bit */
    setValIntoBitstring(bs, 0, 1, 0b1);
    assert (0b11010011 == getValFromBitstring(bs, 0, 8));

    setValIntoBitstring(bs, 0, 1, 0b0);
    assert (0b01010011 == getValFromBitstring(bs, 0, 8));

    setValIntoBitstring(bs, 7, 1, 0b1);
    assert (0b01010011 == getValFromBitstring(bs, 0, 8));

    setValIntoBitstring(bs, 7, 1, 0b0);
    assert (0b01010010 == getValFromBitstring(bs, 0, 8));

    setValIntoBitstring(bs, 7, 1, 0b1);
    assert (0b01010011 == getValFromBitstring(bs, 0, 8));

    setValIntoBitstring(bs, 8, 1, 0b1);
    assert (0b11000101 == getValFromBitstring(bs, 8, 8));

    setValIntoBitstring(bs, 8, 1, 0b0);
    assert (0b01000101 == getValFromBitstring(bs, 8, 8));

    setValIntoBitstring(bs, 8, 1, 0b1);
    assert (0b11000101 == getValFromBitstring(bs, 8, 8));

    setValIntoBitstring(bs, 21, 1, 0b1);
    assert (0b11011110 == getValFromBitstring(bs, 16, 8));

    setValIntoBitstring(bs, 21, 1, 0b0);
    assert (0b11011010 == getValFromBitstring(bs, 16, 8));

    /* set multiple bits */

    setValIntoBitstring(bs, 0, 2, 0b10101010);
    assert (0b10010011 == getValFromBitstring(bs, 0, 8));

    setValIntoBitstring(bs, 1, 3, 0b10101010);
    assert (0b10100011 == getValFromBitstring(bs, 0, 8));

    setValIntoBitstring(bs, 2, 5, 0b10101010);
    assert (0b10010101 == getValFromBitstring(bs, 0, 8));

    setValIntoBitstring(bs, 0, 8, 0b01010011);
    assert (0b01010011 == getValFromBitstring(bs, 0, 8));
    assert (0b1100010111011010 == getValFromBitstring(bs, 8, 16));

    setValIntoBitstring(bs, 8, 7, 0b10010010);
    assert (0b00100101 == getValFromBitstring(bs, 8, 8));

    setValIntoBitstring(bs, 8, 8, 0b11000101);
    assert (0b11000101 == getValFromBitstring(bs, 8, 8));

    setValIntoBitstring(bs, 25, 4, 0b10010010);
    assert (0b00010010 == getValFromBitstring(bs, 24, 8));

    setValIntoBitstring(bs, 24, 8, 0b01001010);
    assert (0b01001010 == getValFromBitstring(bs, 24, 8));

    /* cross byte boundaries */

    setValIntoBitstring(bs, 1, 8, 0b10101010);
    assert (0b010101010 == getValFromBitstring(bs, 0, 9));

    setValIntoBitstring(bs, 5, 11, 0b11101010100);
    assert (0b0101011101010100 == getValFromBitstring(bs, 0, 16));

    setValIntoBitstring(bs, 7, 18, 0b001011101010100001);
    assert (0b01010110010111010101000011001010  == getValFromBitstring(bs, 0, 32));

    freeBitString(&bs);
    return 0;
}

int testGetBitInBs()
{
    bitstring bs = newBitString(256);

    /* these assign chars */
    bs[0] = 83;  /* 01010011 */
    bs[1] = 197; /* 11000101 */
    bs[2] = 218; /* 11011010 */
    bs[3] = 74;  /* 01001010 */

    assert (  0 == GET_BIT_IN_BS(bs,   0));
    assert (  0 != GET_BIT_IN_BS(bs,   1));
    assert (  0 == GET_BIT_IN_BS(bs,   2));
    assert (  0 != GET_BIT_IN_BS(bs,   3));
    assert (  0 == GET_BIT_IN_BS(bs,   4));
    assert (  0 == GET_BIT_IN_BS(bs,   5));
    assert (  0 != GET_BIT_IN_BS(bs,   6));
    assert (  0 != GET_BIT_IN_BS(bs,   7));

    assert (  0 != GET_BIT_IN_BS(bs,   8));
    assert (  0 != GET_BIT_IN_BS(bs,   9));
    assert (  0 == GET_BIT_IN_BS(bs,  10));
    assert (  0 == GET_BIT_IN_BS(bs,  11));
    assert (  0 == GET_BIT_IN_BS(bs,  12));
    assert (  0 != GET_BIT_IN_BS(bs,  13));
    assert (  0 == GET_BIT_IN_BS(bs,  14));
    assert (  0 != GET_BIT_IN_BS(bs,  15));

    assert (  0 != GET_BIT_IN_BS(bs,  16));
    assert (  0 != GET_BIT_IN_BS(bs,  17));
    assert (  0 == GET_BIT_IN_BS(bs,  18));
    assert (  0 != GET_BIT_IN_BS(bs,  19));
    assert (  0 != GET_BIT_IN_BS(bs,  20));
    assert (  0 == GET_BIT_IN_BS(bs,  21));
    assert (  0 != GET_BIT_IN_BS(bs,  22));
    assert (  0 == GET_BIT_IN_BS(bs,  23));

    assert (  0 == GET_BIT_IN_BS(bs,  24));
    assert (  0 != GET_BIT_IN_BS(bs,  25));
    assert (  0 == GET_BIT_IN_BS(bs,  26));
    assert (  0 == GET_BIT_IN_BS(bs,  27));
    assert (  0 != GET_BIT_IN_BS(bs,  28));
    assert (  0 == GET_BIT_IN_BS(bs,  29));
    assert (  0 != GET_BIT_IN_BS(bs,  30));
    assert (  0 == GET_BIT_IN_BS(bs,  31));

    freeBitString(&bs);
}

int testRemoveFromBitstring()
{
    // to generate: print '%s,' % (','.join(bitstring.BitString(length=32, uint=random.randint(0,2**31)).bin[2:]))

#undef REINIT
#define REINIT(array)                                               \
    lengthInBits = ARRAY_LENGTH((array));                           \
    freeBitString(&bs);                                             \
    bs = newBitStringFromBoolArray((array), lengthInBits)

    unsigned int lengthInBits = 0;
    bitstring bs = NULL;

    ////////////
    static const bool array1[] = {
        0,0,1,0,1,
    };

    REINIT(array1);
    assert (0 == removeFromBitstring(bs, lengthInBits, 0, 1));
    assert (0b0101 == getValFromBitstring(bs, 0, 4));

    REINIT(array1);
    assert (0 == removeFromBitstring(bs, lengthInBits, 1, 1));
    assert (0b0101 == getValFromBitstring(bs, 0, 4));

    REINIT(array1);
    assert (0 == removeFromBitstring(bs, lengthInBits, 2, 1));
    assert (0b0001 == getValFromBitstring(bs, 0, 4));

    REINIT(array1);
    assert (0 == removeFromBitstring(bs, lengthInBits, 3, 1));
    assert (0b0011 == getValFromBitstring(bs, 0, 4));

    REINIT(array1);
    assert (0 == removeFromBitstring(bs, lengthInBits, 4, 1));
    assert (0b0010 == getValFromBitstring(bs, 0, 4));

    // remove 2 bits

    REINIT(array1);
    assert (0 == removeFromBitstring(bs, lengthInBits, 0, 2));
    assert (0b101 == getValFromBitstring(bs, 0, 3));

    REINIT(array1);
    assert (0 == removeFromBitstring(bs, lengthInBits, 1, 2));
    assert (0b001 == getValFromBitstring(bs, 0, 3));

    REINIT(array1);
    assert (0 == removeFromBitstring(bs, lengthInBits, 2, 2));
    assert (0b001 == getValFromBitstring(bs, 0, 3));

    REINIT(array1);
    assert (0 == removeFromBitstring(bs, lengthInBits, 3, 2));
    assert (0b001 == getValFromBitstring(bs, 0, 3));

    // remove 3 bits

    REINIT(array1);
    assert (0 == removeFromBitstring(bs, lengthInBits, 0, 3));
    assert (0b01 == getValFromBitstring(bs, 0, 2));

    REINIT(array1);
    assert (0 == removeFromBitstring(bs, lengthInBits, 1, 3));
    assert (0b01 == getValFromBitstring(bs, 0, 2));

    REINIT(array1);
    assert (0 == removeFromBitstring(bs, lengthInBits, 2, 3));
    assert (0b00 == getValFromBitstring(bs, 0, 2));

    // remove 4 bits

    REINIT(array1);
    assert (0 == removeFromBitstring(bs, lengthInBits, 0, 4));
    assert (0b1 == getValFromBitstring(bs, 0, 1));

    REINIT(array1);
    assert (0 == removeFromBitstring(bs, lengthInBits, 1, 4));
    assert (0b0 == getValFromBitstring(bs, 0, 1));

    ///////////
    static const bool array2[] = {
        0,0,1,0,0,1,1,0,1,1,0,1,1,1,1,0,1,1,0,0,1,1,1,1,0,0,0,1,0,1,0,0,

        0,0,0,1,1,0,1,1,0,0,1,1,1,0,1,1,0,1,1,0,0,0,1,0,1,1,0,0,1,1,1,1,

        1,0,1,1,0,1,0,1,0,1,0,1,1,1,1,1,0,1,1,1,0,1,1,0,0,1,1,0,1,0,0,1,

        0,0,0,0,1,0,0,1,0,0,0,0,1,0,1,1,1,0,0,1,1,1,1,0,1,0,1,0,0,0,1,0,
    };

    REINIT(array2);
    assert (0 == removeFromBitstring(bs, lengthInBits, 0, 7));
    assert (0b0110111101100111100010100 == getValFromBitstring(bs, 0, 25));

    REINIT(array2);
    assert (0 == removeFromBitstring(bs, lengthInBits, 1, 7));
    assert (0b0110111101100111100010100 == getValFromBitstring(bs, 0, 25));

    REINIT(array2);
    assert (0 == removeFromBitstring(bs, lengthInBits, 2, 7));
    assert (0b0010111101100111100010100 == getValFromBitstring(bs, 0, 25)); 

    REINIT(array2);
    assert (0 == removeFromBitstring(bs, lengthInBits, 3, 7));
    assert (0b0010111101100111100010100 == getValFromBitstring(bs, 0, 25));

    REINIT(array2);
    assert (0 == removeFromBitstring(bs, lengthInBits, 0, 8));
    assert (0b110111101100111100010100 == getValFromBitstring(bs, 0, 24));

    REINIT(array2);
    assert (0 == removeFromBitstring(bs, lengthInBits, 1, 8));
    assert (0b010111101100111100010100 == getValFromBitstring(bs, 0, 24));

    REINIT(array2);
    assert (0 == removeFromBitstring(bs, lengthInBits, 0, 32));
    assert (0b00011011001110110110001011001111 == getValFromBitstring(bs, 0, 32));

    REINIT(array2);
    assert (0 == removeFromBitstring(bs, lengthInBits, 1, 32));
    assert (0b00011011001110110110001011001111 == getValFromBitstring(bs, 0, 32));

    REINIT(array2);
    assert (0 == removeFromBitstring(bs, lengthInBits, 2, 32));
    assert (0b00011011001110110110001011001111 == getValFromBitstring(bs, 0, 32));

    REINIT(array2);
    assert (0 == removeFromBitstring(bs, lengthInBits, 3, 32));
    assert (0b00111011001110110110001011001111 == getValFromBitstring(bs, 0, 32));

    REINIT(array2);
    assert (0 == removeFromBitstring(bs, lengthInBits, 17, 32));
    assert (0b00100110110111101110001011001111 == getValFromBitstring(bs, 0, 32));

    REINIT(array2);
    assert (0 == removeFromBitstring(bs, lengthInBits, 21, 33));
    assert (0b00100110110111101100110110011111 == getValFromBitstring(bs, 0, 32));
    assert (0b01101010101111101110110011010010 == getValFromBitstring(bs, 32, 32));

    REINIT(array2);
    assert (0 == removeFromBitstring(bs, lengthInBits, 9, 63));
    assert (0b00100110101011111011101100110100 == getValFromBitstring(bs, 0, 32));
    assert (0b10000100100001011100111101010001 == getValFromBitstring(bs, 32, 32));

    REINIT(array2);
    assert (0 == removeFromBitstring(bs, lengthInBits, 9, 64));
    assert (0b00100110110111110111011001101001 == getValFromBitstring(bs, 0, 32));
    assert (0b00001001000010111001111010100010 == getValFromBitstring(bs, 32, 32));

    REINIT(array2);
    assert (0 == removeFromBitstring(bs, lengthInBits, 9, 65));
    assert (0b00100110101111101110110011010010 == getValFromBitstring(bs, 0, 32));
    assert (0b0001001000010111001111010100010 == getValFromBitstring(bs, 32, 31));
   
    ////////////
    freeBitString(&bs);
    return 0;
}

int testGetVarLenValFromBitstring()
{
    unsigned int fromIdx;
    unsigned int arraySize;
    unsigned int val;
    unsigned int totalNumBits;
    unsigned int lenSpecNumBits;
    int retcode;

    bitstring bs = newBitString(256);

#undef REINIT
#define REINIT(bs, numBits, val2)                                       \
    totalNumBits = lenSpecNumBits = val = 0;                            \
    assert(0 == setValIntoBitstring((bs), 0, (numBits), (val2)))

#undef CALL_GET_VAR_LEN_VAL
#define CALL_GET_VAR_LEN_VAL(fromIdx, bsLen, lengthSpecArray, maxNumSetBits) \
    retcode = getVarLenValFromBitstring(bs, (bsLen), (fromIdx),         \
                                        (lengthSpecArray), (maxNumSetBits), \
                                        &val, &lenSpecNumBits,          \
                                        &totalNumBits)

    static unsigned int numSetBits2Len[] = {
        3, 0, 2, 6, 11, 26, 32,
    };

    ////////////////////////////

    REINIT(bs, 7, 0b0110101);
    CALL_GET_VAR_LEN_VAL(0, 1, numSetBits2Len, 3);
    assert (-1 == retcode);

    REINIT(bs, 7, 0b0110101);
    CALL_GET_VAR_LEN_VAL(0, 2, numSetBits2Len, 3);
    assert (-1 == retcode);

    REINIT(bs, 7, 0b0110101);
    CALL_GET_VAR_LEN_VAL(0, 3, numSetBits2Len, 3);
    assert (-1 == retcode);

    REINIT(bs, 7, 0b0110101);
    CALL_GET_VAR_LEN_VAL(0, 4, numSetBits2Len, 3);
    assert (0 == retcode && 6 == val && 1 == lenSpecNumBits && 4 == totalNumBits);

    REINIT(bs, 7, 0b0110101);
    CALL_GET_VAR_LEN_VAL(0, 5, numSetBits2Len, 3);
    assert (0 == retcode && 6 == val && 1 == lenSpecNumBits && 4 == totalNumBits);


    REINIT(bs, 7, 0b1011010);
    CALL_GET_VAR_LEN_VAL(0, 1, numSetBits2Len, 3);
    assert (-1 == retcode);

    REINIT(bs, 7, 0b1011010);
    CALL_GET_VAR_LEN_VAL(0, 2, numSetBits2Len, 3);
    assert (-2 == retcode && 2 == lenSpecNumBits && 2 == totalNumBits);

    REINIT(bs, 7, 0b1011010);
    CALL_GET_VAR_LEN_VAL(0, 3, numSetBits2Len, 3);
    assert (-2 == retcode && 2 == lenSpecNumBits && 2 == totalNumBits);



    REINIT(bs, 7, 0b1101101);
    CALL_GET_VAR_LEN_VAL(0, 1, numSetBits2Len, 3);
    assert (-1 == retcode);

    REINIT(bs, 7, 0b1101101);
    CALL_GET_VAR_LEN_VAL(0, 2, numSetBits2Len, 3);
    assert (-1 == retcode);

    REINIT(bs, 7, 0b1101101);
    CALL_GET_VAR_LEN_VAL(0, 3, numSetBits2Len, 3);
    assert (-1 == retcode);

    REINIT(bs, 7, 0b1101101);
    CALL_GET_VAR_LEN_VAL(0, 4, numSetBits2Len, 3);
    assert (-1 == retcode);

    REINIT(bs, 7, 0b1101101);
    CALL_GET_VAR_LEN_VAL(0, 5, numSetBits2Len, 3);
    assert (0 == retcode && 3 == val && 3 == lenSpecNumBits && 5 == totalNumBits);

    REINIT(bs, 7, 0b1110110);
    CALL_GET_VAR_LEN_VAL(0, 7, numSetBits2Len, 3);
    assert (-1 == retcode);



    REINIT(bs, 10, 0b1110110010);
    CALL_GET_VAR_LEN_VAL(0, 9, numSetBits2Len, 4);
    assert (-1 == retcode);

    REINIT(bs, 10, 0b1110110010);
    CALL_GET_VAR_LEN_VAL(0, 10, numSetBits2Len, 4);
    assert (0 == retcode && 0b110010 == val && 4 == lenSpecNumBits && 10 == totalNumBits);


    REINIT(bs, 11, 0b11110110010);
    CALL_GET_VAR_LEN_VAL(0, 11, numSetBits2Len, 4);
    assert (-1 == retcode);

    REINIT(bs, 11, 0b10111111111);
    CALL_GET_VAR_LEN_VAL(0, 11, numSetBits2Len, 4);
    assert (-2 == retcode && 2 == lenSpecNumBits && 2 == totalNumBits);

    REINIT(bs, 16, 0b1111010011101000);
    CALL_GET_VAR_LEN_VAL(0, 15, numSetBits2Len, 5);
    assert (-1 == retcode);

    REINIT(bs, 16, 0b1111010011101000);
    CALL_GET_VAR_LEN_VAL(0, 16, numSetBits2Len, 5);
    assert (0 == retcode && 0b10011101000 == val && 5 == lenSpecNumBits && 16 == totalNumBits);


    REINIT(bs, 32, 0b11111010110001010110100011010111);
    CALL_GET_VAR_LEN_VAL(0, 31, numSetBits2Len, 6);
    assert (-1 == retcode);

    REINIT(bs, 32, 0b11111010110001010110100011010111);
    CALL_GET_VAR_LEN_VAL(0, 32, numSetBits2Len, 6);
    assert (0 == retcode && 0b10110001010110100011010111 == val && 6 == lenSpecNumBits && 32 == totalNumBits);


    REINIT(bs, 32, 0b11111010110001010110100011010111);
    CALL_GET_VAR_LEN_VAL(1, 31, numSetBits2Len, 6);
    assert (0 == retcode && 0b10110001010 == val && 5 == lenSpecNumBits && 16 == totalNumBits);

    REINIT(bs, 32, 0b11111010110001010110100011010111);
    CALL_GET_VAR_LEN_VAL(1, 32, numSetBits2Len, 6);
    assert (0 == retcode && 0b10110001010 == val && 5 == lenSpecNumBits && 16 == totalNumBits);


    REINIT(bs, 32, 0b11111010110001010110100011010111);
    CALL_GET_VAR_LEN_VAL(2, 31, numSetBits2Len, 6);
    assert (0 == retcode && 0b101100 == val && 4 == lenSpecNumBits && 10 == totalNumBits);

    REINIT(bs, 32, 0b11111010110001010110100011010111);
    CALL_GET_VAR_LEN_VAL(2, 32, numSetBits2Len, 6);
    assert (0 == retcode && 0b101100 == val && 4 == lenSpecNumBits && 10 == totalNumBits);


    CALL_GET_VAR_LEN_VAL(3, 32, numSetBits2Len, 6);
    assert (0 == retcode && 0b10 == val && 3 == lenSpecNumBits && 5 == totalNumBits);

    CALL_GET_VAR_LEN_VAL(4, 32, numSetBits2Len, 6);
    assert (-2 == retcode);

    CALL_GET_VAR_LEN_VAL(5, 32, numSetBits2Len, 6);
    assert (0 == retcode && 0b101 == val && 1 == lenSpecNumBits && 4 == totalNumBits);

    REINIT(bs, 32, 0b11111101011000101011010001101011);
    CALL_GET_VAR_LEN_VAL(0, 32, numSetBits2Len, 6);
    assert (-1 == retcode);

    REINIT(bs, 32, 0b10101011111111101011000101011010);
    assert(0 == setValIntoBitstring(
               bs, 32, 32,
               0b01101000101001101000111011101101));
    CALL_GET_VAR_LEN_VAL(8, 32, numSetBits2Len, 7);
    assert (-1 == retcode);
    CALL_GET_VAR_LEN_VAL(8, 47, numSetBits2Len, 7);
    assert (-1 == retcode);
    CALL_GET_VAR_LEN_VAL(9, 48, numSetBits2Len, 7);
    assert (0 == retcode && 0b10110001010110100110100010100110 == val && 7 == lenSpecNumBits && 39 == totalNumBits);

    ////////////////////////////
    freeBitString(&bs);
    return 0;
}

int main()
{
    testGetValFromBitstring();
    testSetValIntoBitstring();
    testGetBitInBs();
    testFindFirstInBitstring();
    testRemoveFromBitstring();
    testGetVarLenValFromBitstring();

    return 0;
}
