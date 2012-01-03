/* $Id$ */

#include "../encoding3.cc"

using namespace std;

int testConsumeLinkLabel()
{
    bitstring bs = NULL;
    unsigned int bsLen = 0;
    unsigned int bitNum = 0;
    bool isNull = false;

#define REINIT(array)                                               \
    bitNum = 0;                                                     \
    isNull = false;                                                 \
    freeBitString(&bs);                                             \
    bsLen = ARRAY_LENGTH((array));                                  \
    bs = newBitStringFromBoolArray((array), bsLen)

    ////////
    static const bool arrayZero[] = {
        /* null-link. */
        0,
    };
    REINIT(arrayZero);

    assert (0 == consumeLinkLabel(bs, 1, bitNum, isNull));
    assert (1 == bitNum);
    assert (isNull);

    ////
    static const bool arrayOne[] = {
        /* null-link, 6-bit link 22. */
        0,   1,1,0, 0,1,0,1,1,0,
    };
    REINIT(arrayOne);

    assert (0 == consumeLinkLabel(bs, bsLen, bitNum, isNull));
    assert (1 == bitNum);
    assert (isNull);
    assert (-1 == consumeLinkLabel(bs, 9, bitNum, isNull));
    assert (1 == bitNum);
    assert (0b010110 == consumeLinkLabel(bs, bsLen, bitNum, isNull));
    assert (10 == bitNum);
    assert (!isNull);

    ////
    static const bool arrayTwo[] = {
        /* 3-bit link 0, null-link, 3-bit link 2, null-link, null-link */
        1,0, 0,0,0,    0,   1,0, 0,1,0,   0,   0,
    };
    REINIT(arrayTwo);

    assert (-1 == consumeLinkLabel(bs, 4, bitNum, isNull));
    assert (0 == bitNum);

    assert (0 == consumeLinkLabel(bs, bsLen, bitNum, isNull));
    assert (5 == bitNum);
    assert (!isNull);

    assert (0 == consumeLinkLabel(bs, bsLen, bitNum, isNull));
    assert (6 == bitNum);
    assert (isNull);

    assert (-1 == consumeLinkLabel(bs, 10, bitNum, isNull));
    assert (6 == bitNum);

    assert (0b010 == consumeLinkLabel(bs, bsLen, bitNum, isNull));
    assert (11 == bitNum);
    assert (!isNull);

    assert (0 == consumeLinkLabel(bs, bsLen, bitNum, isNull));
    assert (12 == bitNum);
    assert (isNull);

    assert (0 == consumeLinkLabel(bs, bsLen, bitNum, isNull));
    assert (13 == bitNum);
    assert (isNull);


    ////
    static const bool arrayThree[] = {
        /* 6-bit link 33, 11-bit link 2047 */
        1,1,0, 1,0,0,0,0,1,    1,1,1,0, 1,1,1,1,1,1,1,1,1,1,1,
    };
    REINIT(arrayThree);

    assert (-1 == consumeLinkLabel(bs, 8, bitNum, isNull));
    assert (0 == bitNum);
    assert (0b100001 == consumeLinkLabel(bs, bsLen, bitNum, isNull));
    assert (9 == bitNum);
    assert (!isNull);

    assert (-1 == consumeLinkLabel(bs, 23, bitNum, isNull));
    assert (9 == bitNum);
    assert (0b11111111111 == consumeLinkLabel(bs, bsLen, bitNum, isNull));
    assert (24 == bitNum);
    assert (!isNull);

    bitNum = 0;
    consumeLinkLabel(bs, bsLen, bitNum, isNull);
    assert (9 == bitNum);
    assert (!isNull);
    assert (0b11111111111 == consumeLinkLabel(bs, bsLen, bitNum, isNull));
    assert (24 == bitNum);
    assert (!isNull);

    ////
    static const bool arrayFour[] = {
        /* error */
        1,1,1,1,0,
    };
    REINIT(arrayFour);

    assert (-1 == consumeLinkLabel(bs, bsLen, bitNum, isNull));

    cout << __func__ << "() passed." << endl;
    freeBitString(&bs);
    return 0;
}

int testConsumeUpToIncludingNullLinkLabel()
{
    bitstring bs = NULL;
    unsigned int bitNum = 0;
    unsigned int bsLen = 0;

#undef REINIT
#define REINIT(array)                                               \
    bitNum = 0;                                                     \
    bsLen = ARRAY_LENGTH((array));                                  \
    freeBitString(&bs);                                             \
    bs = newBitStringFromBoolArray((array), bsLen)

    /////////////////////
    static const bool array1[] = {
        /* null-link. */
        0,
    };

    REINIT(array1);

    assert (0 == consumeUpToIncludingNullLinkLabel(bs, bsLen, bitNum));
    assert (1 == bitNum);

    ///////////
    static bool array2[] = {
        /* null-link, 6-bit link 22. */
        0,   1,1,0, 0,1,0,1,1,0,   1,
    };

    REINIT(array2);

    assert (0 == consumeUpToIncludingNullLinkLabel(bs, bsLen, bitNum));
    assert (1 == bitNum);
    assert (-1 == consumeUpToIncludingNullLinkLabel(bs, 9, bitNum));
    assert (1 == bitNum);

    /* change the last bit to 0 */
    setValIntoBitstring(bs, 10, 1, 0);

    // still fails
    assert (-1 == consumeUpToIncludingNullLinkLabel(bs, 10, bitNum));
    assert (1 == bitNum);

    // do look at last bit -> succeed
    assert (0 == consumeUpToIncludingNullLinkLabel(bs, bsLen, bitNum));
    assert (11 == bitNum);

    /*****************************************/
    static const bool array3[] = {
        /* 6-bit link, 3-bit link, 11-bit link, null-link */
        1,1,0, 0,0,0,0,0,0,   1,0, 0,0,0,
        1,1,1,0, 0,0,0,0,0,0,0,0,0,0,0,   1,
    };

    REINIT(array3);

    assert (-1 == consumeUpToIncludingNullLinkLabel(
                bs, bsLen - 1, bitNum));
    assert (0 == bitNum);
    assert (-1 == consumeUpToIncludingNullLinkLabel(
                bs, bsLen, bitNum));
    assert (0 == bitNum);
    
    setValIntoBitstring(bs, bsLen - 1, 1, 0);

    assert (-1 == consumeUpToIncludingNullLinkLabel(
                bs, bsLen - 1, bitNum));
    assert (0 == bitNum);
    assert (0 == consumeUpToIncludingNullLinkLabel(
                bs, bsLen, bitNum));
    assert (bsLen == bitNum);

    /// make it malformed
    setValIntoBitstring(bs, 17, 1, 1);

    bitNum = 0;
    assert (-1 == consumeUpToIncludingNullLinkLabel(
                bs, bitNum, bsLen));
    assert (0 == bitNum);
    bitNum = 9;
    assert (-1 == consumeUpToIncludingNullLinkLabel(
                bs, bitNum, bsLen));
    assert (9 == bitNum);

    /*****************************************/
    static const bool array4[] = {
        /* 3-bit link 0, null-link, 3-bit link 2, null-link, null-link */
        1,0, 0,0,0,    0,   1,0, 0,1,0,   0,   0,   0,
    };

    REINIT(array4);

    assert (-1 == consumeUpToIncludingNullLinkLabel(
                bs, 5, bitNum));
    assert (0 == bitNum);
    assert (0 == consumeUpToIncludingNullLinkLabel(
                bs, 6, bitNum));
    assert (6 == bitNum);

    assert (-1 == consumeUpToIncludingNullLinkLabel(
                bs, 11, bitNum));
    assert (6 == bitNum);
    assert (0 == consumeUpToIncludingNullLinkLabel(
                bs, 12, bitNum));
    assert (12 == bitNum);

    assert (-1 == consumeUpToIncludingNullLinkLabel(
                bs, 12, bitNum));
    assert (12 == bitNum);
    assert (0 == consumeUpToIncludingNullLinkLabel(
                bs, 13, bitNum));
    assert (13 == bitNum);

    assert (0 == consumeUpToIncludingNullLinkLabel(
                bs, bsLen, bitNum));
    assert (14 == bitNum);

    /*****************************************/
    /* no null-link */
    static const bool array5[] = {
        /* 3-bit link, 11-bit link, 3-bit link, 6-bit link */
        1,0, 0,0,0,
        1,1,1,0, 0,1,0,0,0,0,1,1,0,1,0,
        1,0, 1,0,1,
        1,1,0, 0,0,0,1,1,0,
    };

    REINIT(array5);
    assert (-1 == consumeUpToIncludingNullLinkLabel(
                bs, bsLen, bitNum));
    assert (0 == bitNum);


    cout << __func__ << "() passed." << endl;

    freeBitString(&bs);

    return 0;
}

int testProcessEncoding3()
{
    bool linkId2UpStatus4[] = {
        1, 1, 1, 1,
    };
    bool linkId2UpStatus8[] = {
        1, 1, 1, 1, 1, 1, 1, 1,
    };
    bool linkId2UpStatus16[] = {
        1, 1, 1, 1, 1, 1, 1, 1,   1, 1, 1, 1, 1, 1, 1, 1,
    };
    bool linkId2UpStatus32[] = {
        1, 1, 1, 1, 1, 1, 1, 1,   1, 1, 1, 1, 1, 1, 1, 1,
        1, 1, 1, 1, 1, 1, 1, 1,   1, 1, 1, 1, 1, 1, 1, 1,
    };
    unsigned int numLinks = 0;

    action_t action;
    unsigned int outLinkId = 0;
    unsigned char* encoding = NULL;
    unsigned int lengthInBits = 0;
    unsigned int newLengthInBits = 0;
    int retval = 0;

#undef REINIT
#define REINIT(encodingBitArray, linkStatusArray)                       \
    do {                                                                \
        action = action_inval;                                          \
        outLinkId = newLengthInBits = 0;                                \
        freeBitString(&encoding);                                       \
        lengthInBits = ARRAY_LENGTH((encodingBitArray));                \
        encoding = newBitStringFromBoolArray((encodingBitArray), lengthInBits); \
        numLinks = ARRAY_LENGTH((linkStatusArray));                     \
    }                                                                   \
    while (0)

#define CALL_PROCESS_ENCODING(linkStatusArray)                          \
    retval = processEncoding3(encoding, lengthInBits, (linkStatusArray), \
                              numLinks, &action, &outLinkId,   \
                              &newLengthInBits)

    /* **************************************************/
    static const bool array1[] = {
        0,  1,1,1,1,0,
    };

    REINIT(array1, linkId2UpStatus4);
    CALL_PROCESS_ENCODING(linkId2UpStatus4);
    assert (retval == -1);

    /* **************************************************/
    static const bool array2[] = {
        0,   0,
    };

    REINIT(array2, linkId2UpStatus4);
    CALL_PROCESS_ENCODING(linkId2UpStatus4);
    assert (retval == 0);
    assert (action_deliver == action);

    /* **************************************************/
    static const bool array3[] = {
        1,   0,
    };

    REINIT(array3, linkId2UpStatus4);
    CALL_PROCESS_ENCODING(linkId2UpStatus4);
    assert (retval == 0);
    assert (action_deliver == action);

    /* **************************************************/
    static bool array4[] = {
        0,   1,0, 0,1,1,    0,   0,
    };

    REINIT(array4, linkId2UpStatus4);
    CALL_PROCESS_ENCODING(linkId2UpStatus4);
    assert (retval == 0);
    assert (action_forward == action && outLinkId == 3 && newLengthInBits == 2);
    assert (0b00 == getValFromBitstring(encoding, 0, 2));
    CALL_PROCESS_ENCODING(linkId2UpStatus4);
    assert (retval == 0);
    assert (action_deliver == action && newLengthInBits == 2);
    assert (0b00 == getValFromBitstring(encoding, 0, 2));

    /* make bad link */
    REINIT(array4, linkId2UpStatus4);
    assert (0 == setValIntoBitstring(encoding, 3, 3, 0b100));
    CALL_PROCESS_ENCODING(linkId2UpStatus4);
    assert (retval == -2);

    /* **************************************************/
    static const bool array5[] = {
        0,   1,1,0, 0,0,1,0,0,0,    1,1,1,1,0,   0,
    };

    REINIT(array5, linkId2UpStatus16);
    CALL_PROCESS_ENCODING(linkId2UpStatus16);
    assert (retval == -3);

    /* **************************************************/
    static const bool array6[] = {
        0,   1,1,0, 0,0,1,0,0,0,    1,0, 1,0,1,    1,1,0, 1,1,1,1,1,1,    1,1,1,1,0,   0,
    };

    REINIT(array6, linkId2UpStatus16);
    CALL_PROCESS_ENCODING(linkId2UpStatus16);
    assert (retval == -3);

    /* **************************************************/
    static const bool array7[] = {
        0,   1,1,0, 0,0,1,1,0,1,    1,0, 0,0,0,    1,1,0, 1,1,1,1,1,1,    1,1,1,0, 1,1,1,1,1,1,1,1,1,1,1,   0,

        // this remains (in addition to the on-detour bit.
        1,1,0, 1,0,0,1,1,0,0,1,0,0,0,1,0,1,1,0,1,
    };

    REINIT(array7, linkId2UpStatus16);
    CALL_PROCESS_ENCODING(linkId2UpStatus16);
    assert (retval == 0);
    assert (action_forward == action && 13 == outLinkId && 21 == newLengthInBits);
    assert (0b011010011001000101101 == getValFromBitstring(encoding, 0, 21));

    /* **************************************************/
    // on detour, repeatedly strip off link label at the front until egress
    static const bool array8[] = {
        1,   1,1,0, 0,0,1,1,1,1,    1,0, 0,0,0,    1,1,0, 0,1,1,1,1,1,    1,1,1,0, 0,0,0,0,0,0,0,0,1,1,0,   0,

        // this remains (in addition to the on-detour bit.
        1,1,0, 1,0,0,1,1,0,0,1,0,0,0,1,0,1,1,0,1,
    };

    REINIT(array8, linkId2UpStatus32);
    CALL_PROCESS_ENCODING(linkId2UpStatus32);
    assert (retval == 0);
    assert (action_forward == action && 15 == outLinkId && newLengthInBits == (ARRAY_LENGTH(array8) - 9));

    lengthInBits = newLengthInBits;
    CALL_PROCESS_ENCODING(linkId2UpStatus32);
    assert (retval == 0);
    assert (action_forward == action && 0 == outLinkId && newLengthInBits == (ARRAY_LENGTH(array8) - (9 + 5)));
    assert (0b1110011111111000000000110011010 == getValFromBitstring(encoding, 0, 31));

    lengthInBits = newLengthInBits;
    CALL_PROCESS_ENCODING(linkId2UpStatus32);
    assert (retval == 0);
    assert (action_forward == action && 31 == outLinkId && newLengthInBits == (ARRAY_LENGTH(array8) - (9 + 5 + 9)));
    assert (0b11110000000001100110100110010001 == getValFromBitstring(encoding, 0, 32));

    lengthInBits = newLengthInBits;
    CALL_PROCESS_ENCODING(linkId2UpStatus32);
    assert (retval == 0);
    assert (action_forward == action && 6 == outLinkId && newLengthInBits == (ARRAY_LENGTH(array8) - (9 + 5 + 9 + 15)));
    assert (0b1011010011001000101101 == getValFromBitstring(encoding, 0, 22));

    lengthInBits = newLengthInBits;
    CALL_PROCESS_ENCODING(linkId2UpStatus32);
    assert (retval == 0);
    assert (action_deliver == action && 6 == outLinkId && newLengthInBits == (ARRAY_LENGTH(array8) - (9 + 5 + 9 + 15)));
    assert (0b1011010011001000101101 == getValFromBitstring(encoding, 0, 22));

    /* **************************************************/
    // link is down, not on detour

    static bool array9[] = {
        0,   1,1,0, 0,0,1,1,0,1,    1,1,1,1,0,0,0,0,0,

        // this remains in addition to the on detour bit
        0,1,1,0,1,1,1,1,0,0,1,0,0,1,1,0,0,0,0,1,0,1,0,1,
    };
    linkId2UpStatus16[13] = 0; // mark the link as failed

    // error grabbing at next label
    REINIT(array9, linkId2UpStatus16);
    CALL_PROCESS_ENCODING(linkId2UpStatus16);
    assert (retval == -4);

    // next link label is invalid
    array9[12] = 0;
    REINIT(array9, linkId2UpStatus16);
    CALL_PROCESS_ENCODING(linkId2UpStatus16);
    assert (retval == -5);

    // next link is null-link -> drop
    array9[10] = 0;
    REINIT(array9, linkId2UpStatus16);
    CALL_PROCESS_ENCODING(linkId2UpStatus16);
    assert (retval == 0);
    assert (action_drop == action);

    // next link is also down -> drop
    REINIT(array9, linkId2UpStatus16);
    setValIntoBitstring(encoding, 10, 9, 0b110000101);
    linkId2UpStatus16[5] = 0;
    CALL_PROCESS_ENCODING(linkId2UpStatus16);
    assert (retval == 0);
    assert (action_drop == action);

    // next link is also down -> drop
    REINIT(array9, linkId2UpStatus16);
    setValIntoBitstring(encoding, 10, 9, 0b110001001);
    linkId2UpStatus16[9] = 1;
    CALL_PROCESS_ENCODING(linkId2UpStatus16);
    assert (retval == 0);
    assert (action_forward == action && outLinkId == 9 &&
            (ARRAY_LENGTH(array9) - 18) == newLengthInBits);
    assert (0b1011011110010011000010101 == getValFromBitstring(encoding, 0, 25));

    // already on detour, link is down
    array9[0] = 1;
    REINIT(array9, linkId2UpStatus16);
    CALL_PROCESS_ENCODING(linkId2UpStatus16);
    assert (retval == 0);
    assert (action_drop == action);

    ///////////
    cout << __func__ << "() passed." << endl;
    free(encoding);
    return 0;
}

int main()
{
    testConsumeLinkLabel();
    testConsumeUpToIncludingNullLinkLabel();
    testProcessEncoding3();
    return 0;
}
