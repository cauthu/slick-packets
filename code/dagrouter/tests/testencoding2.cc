/* $Id$ */

// to enable unit testing features in encoding2.cc
#define UNIT_TESTING

#include <stdio.h>
#include "../encoding2.cc"

int testParseOneSuccessor()
{
    bitstring bs = NULL;
    successor_t successor;
    int retcode = 0;
    unsigned int totalSucessorLen = 0;
    unsigned bsLen = 0;

#undef REINIT
#define REINIT(boolArray)                                               \
    totalSucessorLen = 0;                                               \
    bsLen = ARRAY_LENGTH((boolArray));                                  \
    freeBitString(&bs);                                                 \
    bs = newBitStringFromBoolArray((boolArray), bsLen)

#undef CALL_PARSE_ONE_SUCESSOR
#define CALL_PARSE_ONE_SUCESSOR(bsLen, fromIdx, ptrLen)             \
    retcode = parseOneSuccessor(bs, (bsLen), (fromIdx), (ptrLen),   \
                                &totalSucessorLen, &successor)

    ////////////
    static bool array1[] = {
        0, 0,1,0, 0, 1,0,1,1,0,1,0,0,0,1,0,1,0,0,
    };

    REINIT(array1);
    CALL_PARSE_ONE_SUCESSOR(0, 0, 4);
    assert (-1 == retcode);
    CALL_PARSE_ONE_SUCESSOR(1, 0, 4);
    assert (-2 == retcode);
    CALL_PARSE_ONE_SUCESSOR(2, 0, 4);
    assert (-2 == retcode);
    CALL_PARSE_ONE_SUCESSOR(3, 0, 4);
    assert (-2 == retcode);
    CALL_PARSE_ONE_SUCESSOR(4, 0, 4);
    assert (-3 == retcode);
    CALL_PARSE_ONE_SUCESSOR(5, 0, 4);
    assert (0 == retcode && 5 == totalSucessorLen &&
            0b010 == successor.linkId &&
            !successor.containsPtr);


    setValIntoBitstring(bs, 3, 2, 0b11);
    CALL_PARSE_ONE_SUCESSOR(0, 0, 4);
    assert (-1 == retcode);
    CALL_PARSE_ONE_SUCESSOR(1, 0, 4);
    assert (-2 == retcode);
    CALL_PARSE_ONE_SUCESSOR(2, 0, 4);
    assert (-2 == retcode);
    CALL_PARSE_ONE_SUCESSOR(3, 0, 4);
    assert (-2 == retcode);
    CALL_PARSE_ONE_SUCESSOR(4, 0, 4);
    assert (-3 == retcode);
    CALL_PARSE_ONE_SUCESSOR(5, 0, 4);
    assert (-4 == retcode);
    CALL_PARSE_ONE_SUCESSOR(6, 0, 4);
    assert (-4 == retcode);
    CALL_PARSE_ONE_SUCESSOR(7, 0, 4);
    assert (-4 == retcode);
    CALL_PARSE_ONE_SUCESSOR(8, 0, 4);
    assert (-4 == retcode);
    CALL_PARSE_ONE_SUCESSOR(9, 0, 4);
    assert (0 == retcode && 9 == totalSucessorLen &&
            0b011 == successor.linkId &&
            successor.containsPtr && 0b1011 == successor.nodePtr);


    setValIntoBitstring(bs, 1, 3, 0b110);
    CALL_PARSE_ONE_SUCESSOR(0, 0, 6);
    assert (-1 == retcode);
    CALL_PARSE_ONE_SUCESSOR(1, 0, 6);
    assert (-2 == retcode);
    CALL_PARSE_ONE_SUCESSOR(3, 0, 6);
    assert (-2 == retcode);
    CALL_PARSE_ONE_SUCESSOR(4, 0, 6);
    assert (-3 == retcode);
    CALL_PARSE_ONE_SUCESSOR(5, 0, 6);
    assert (-4 == retcode);
    CALL_PARSE_ONE_SUCESSOR(10, 0, 6);
    assert (-4 == retcode);
    CALL_PARSE_ONE_SUCESSOR(bsLen, 0, 6);
    assert (0 == retcode && 11 == totalSucessorLen &&
            0b110 == successor.linkId &&
            successor.containsPtr && 0b101101 == successor.nodePtr);



    setValIntoBitstring(bs, 1, 3, 0b101);
    CALL_PARSE_ONE_SUCESSOR(0, 0, 8);
    assert (-1 == retcode);
    CALL_PARSE_ONE_SUCESSOR(1, 0, 8);
    assert (-2 == retcode);
    CALL_PARSE_ONE_SUCESSOR(3, 0, 8);
    assert (-2 == retcode);
    CALL_PARSE_ONE_SUCESSOR(4, 0, 8);
    assert (-3 == retcode);
    CALL_PARSE_ONE_SUCESSOR(5, 0, 8);
    assert (-4 == retcode);
    CALL_PARSE_ONE_SUCESSOR(12, 0, 8);
    assert (-4 == retcode);
    CALL_PARSE_ONE_SUCESSOR(bsLen, 0, 8);
    assert (0 == retcode && 13 == totalSucessorLen &&
            0b101 == successor.linkId &&
            successor.containsPtr && 0b10110100 == successor.nodePtr);


    setValIntoBitstring(bs, 1, 3, 0b111);
    CALL_PARSE_ONE_SUCESSOR(0, 0, 10);
    assert (-1 == retcode);
    CALL_PARSE_ONE_SUCESSOR(1, 0, 10);
    assert (-2 == retcode);
    CALL_PARSE_ONE_SUCESSOR(3, 0, 10);
    assert (-2 == retcode);
    CALL_PARSE_ONE_SUCESSOR(4, 0, 10);
    assert (-3 == retcode);
    CALL_PARSE_ONE_SUCESSOR(5, 0, 10);
    assert (-4 == retcode);
    CALL_PARSE_ONE_SUCESSOR(14, 0, 10);
    assert (-4 == retcode);
    CALL_PARSE_ONE_SUCESSOR(bsLen, 0, 10);
    assert (0 == retcode && 15 == totalSucessorLen &&
            0b111 == successor.linkId &&
            successor.containsPtr && 0b1011010001 == successor.nodePtr);

    setValIntoBitstring(bs, 1, 3, 0b001);
    CALL_PARSE_ONE_SUCESSOR(0, 0, 12);
    assert (-1 == retcode);
    CALL_PARSE_ONE_SUCESSOR(1, 0, 12);
    assert (-2 == retcode);
    CALL_PARSE_ONE_SUCESSOR(3, 0, 12);
    assert (-2 == retcode);
    CALL_PARSE_ONE_SUCESSOR(4, 0, 12);
    assert (-3 == retcode);
    CALL_PARSE_ONE_SUCESSOR(5, 0, 12);
    assert (-4 == retcode);
    CALL_PARSE_ONE_SUCESSOR(16, 0, 12);
    assert (-4 == retcode);
    CALL_PARSE_ONE_SUCESSOR(bsLen, 0, 12);
    assert (0 == retcode && 17 == totalSucessorLen &&
            0b001 == successor.linkId &&
            successor.containsPtr && 0b101101000101 == successor.nodePtr);

    setValIntoBitstring(bs, 1, 3, 0b000);
    CALL_PARSE_ONE_SUCESSOR(0, 0, 14);
    assert (-1 == retcode);
    CALL_PARSE_ONE_SUCESSOR(1, 0, 14);
    assert (-2 == retcode);
    CALL_PARSE_ONE_SUCESSOR(3, 0, 14);
    assert (-2 == retcode);
    CALL_PARSE_ONE_SUCESSOR(4, 0, 14);
    assert (-3 == retcode);
    CALL_PARSE_ONE_SUCESSOR(5, 0, 14);
    assert (-4 == retcode);
    CALL_PARSE_ONE_SUCESSOR(18, 0, 14);
    assert (-4 == retcode);
    CALL_PARSE_ONE_SUCESSOR(bsLen, 0, 14);
    assert (0 == retcode && 19 == totalSucessorLen &&
            0b000 == successor.linkId &&
            successor.containsPtr && 0b10110100010100 == successor.nodePtr);

    ///////
    static bool array2[] = {
        1,1,1,0, 1,0,0,0,0,1,0,1,1,0,1, 0, 1,0,1,1,0,0,0,0,0,1,0,1,0,1,
    };

    REINIT(array2);
    CALL_PARSE_ONE_SUCESSOR(bsLen, 0, 4);
    assert (-2 == retcode);

    CALL_PARSE_ONE_SUCESSOR(bsLen, 1, 4);
    assert (0 == retcode && 15 == totalSucessorLen &&
            0b10000101101 == successor.linkId &&
            !successor.containsPtr);

    setValIntoBitstring(bs, 15, 1, 0b1);
    CALL_PARSE_ONE_SUCESSOR(bsLen, 1, 14);
    assert (0 == retcode && 29 == totalSucessorLen &&
            0b10000101101 == successor.linkId &&
            successor.containsPtr && 0b10110000010101 == successor.nodePtr);

    ///////
    static bool array3[] = {
        1,1,1,1,1,0,0,

        1,0, 1,0,0,0,1,0, 0, 1,0,1,1,0,0,0,0,0,1,0,1,0,1,
    };

    REINIT(array3);
    CALL_PARSE_ONE_SUCESSOR(bsLen, 7, 14);
    assert (0 == retcode && 9 == totalSucessorLen &&
            0b100010 == successor.linkId &&
            !successor.containsPtr);

    setValIntoBitstring(bs, 9, 7, 0b1110011);
    CALL_PARSE_ONE_SUCESSOR(bsLen, 7, 4);
    assert (0 == retcode && 13 == totalSucessorLen &&
            0b111001 == successor.linkId &&
            successor.containsPtr && 0b1011 == successor.nodePtr);

    ///////
    static bool array4[] = {
        1,1,1,1,1,0,0,0, 1,1,1,1,1,0,0,0, /* 0-15 */
        1,1,1,1,1,0,0,0, 1,1,1,1,1,0,0,0, /* 16-31 */

        1,1,1, /* 32-34 */

        1,0, 1,1,0,0,0,1, 0, 1,1,0,1,0,1,0,0,0,1,0,1,0,1,
    };

    REINIT(array4);
    CALL_PARSE_ONE_SUCESSOR(33, 33, 8);
    assert (-1 == retcode);
    CALL_PARSE_ONE_SUCESSOR(bsLen, 33, 8);
    assert (-2 == retcode);
    CALL_PARSE_ONE_SUCESSOR(35, 34, 8);
    assert (-2 == retcode);
    CALL_PARSE_ONE_SUCESSOR(36, 35, 8);
    assert (-2 == retcode);
    CALL_PARSE_ONE_SUCESSOR(42, 35, 8);
    assert (-2 == retcode);
    CALL_PARSE_ONE_SUCESSOR(43, 35, 8);
    assert (-3 == retcode);

    CALL_PARSE_ONE_SUCESSOR(44, 35, 8);
    assert (0 == retcode && 9 == totalSucessorLen &&
            0b110001 == successor.linkId &&
            !successor.containsPtr);

    setValIntoBitstring(bs, 37, 11, 0b10101011000);
    CALL_PARSE_ONE_SUCESSOR(36, 35, 8);
    assert (-2 == retcode);
    CALL_PARSE_ONE_SUCESSOR(42, 35, 8);
    assert (-2 == retcode);
    CALL_PARSE_ONE_SUCESSOR(43, 35, 8);
    assert (-3 == retcode);
    CALL_PARSE_ONE_SUCESSOR(44, 35, 8);
    assert (-4 == retcode);
    CALL_PARSE_ONE_SUCESSOR(51, 35, 8);
    assert (-4 == retcode);
    CALL_PARSE_ONE_SUCESSOR(52, 35, 8);
    assert (0 == retcode && 17 == totalSucessorLen &&
            0b101010 == successor.linkId &&
            successor.containsPtr && 0b10000100 == successor.nodePtr);
    
    CALL_PARSE_ONE_SUCESSOR(bsLen - 1, 35, 14);
    assert (-4 == retcode);
    CALL_PARSE_ONE_SUCESSOR(bsLen, 35, 14);
    assert (0 == retcode && 23 == totalSucessorLen &&
            0b101010 == successor.linkId &&
            successor.containsPtr && 0b10000100010101 == successor.nodePtr);

    ////////////
    printf("%s() passed.\n", __func__);
    freeBitString(&bs);
    return 0;
}

int testProcessEncoding2_curPtr()
{
    bitstring bs = NULL;
    bool linkId2UpStatus[] = {1,1,1,1,1,1,1,1};
    unsigned int numLinks = ARRAY_LENGTH(linkId2UpStatus);
    action_t action;
    unsigned int outLinkId = 0;
    unsigned int lengthInBits = 0;
    unsigned int newLengthInBits = 0;
    int retcode = 0;

#undef REINIT
#define REINIT(boolArray)                                               \
    action = action_inval;                                              \
    lengthInBits = ARRAY_LENGTH((boolArray));                           \
    freeBitString(&bs);                                                 \
    bs = newBitStringFromBoolArray((boolArray), lengthInBits)

#undef CALL_PROCESS_ENCODING2
#define CALL_PROCESS_ENCODING2(bsLen)                               \
    retcode = processEncoding2(bs, (bsLen), linkId2UpStatus,        \
                               numLinks, &action, &outLinkId,       \
                               &newLengthInBits)

    /******* errors, not enough bits to parse the curptr ******/
    bool array1[] = {
        0, 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    };

    REINIT(array1);
    CALL_PROCESS_ENCODING2(10);
    assert (-1 == retcode);
    CALL_PROCESS_ENCODING2(11);
    assert (-1 != retcode);

    setValIntoBitstring(bs, 0, 2, 0b10);
    CALL_PROCESS_ENCODING2(9);
    assert (-1 == retcode);
    CALL_PROCESS_ENCODING2(10);
    assert (-1 != retcode);

    setValIntoBitstring(bs, 0, 3, 0b110);
    CALL_PROCESS_ENCODING2(8);
    assert (-1 == retcode);
    CALL_PROCESS_ENCODING2(9);
    assert (-1 != retcode);

    setValIntoBitstring(bs, 0, 4, 0b1110);
    CALL_PROCESS_ENCODING2(7);
    assert (-1 == retcode);
    CALL_PROCESS_ENCODING2(8);
    assert (-1 != retcode);

    /*******************/
    // alternate b/w 0 (deliver), too small, and too big

    bool array2[] = {
        0, 0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0,0,
    };

    // 10-bit ptr
    REINIT(array2);

    action = action_inval;
    setValIntoBitstring(bs, 0, 11, 0b00000000000);
    CALL_PROCESS_ENCODING2(11);
    assert (0 == retcode && action_deliver == action);

    setValIntoBitstring(bs, 0, 11, 0b00000001010);
    CALL_PROCESS_ENCODING2(11);
    assert (-8 == retcode);

    setValIntoBitstring(bs, 0, 11, 0b00000001011);
    CALL_PROCESS_ENCODING2(11);
    assert (-2 == retcode);

    // 8-bit ptr
    action = action_inval;
    setValIntoBitstring(bs, 0, 10, 0b1000000000);
    CALL_PROCESS_ENCODING2(10);
    assert (0 == retcode && action_deliver == action);

    setValIntoBitstring(bs, 0, 10, 0b1000001001);
    CALL_PROCESS_ENCODING2(10);
    assert (-8 == retcode);

    setValIntoBitstring(bs, 0, 10, 0b1000001010);
    CALL_PROCESS_ENCODING2(10);
    assert (-2 == retcode);

    // 6-bit ptr
    action = action_inval;
    setValIntoBitstring(bs, 0, 9, 0b110000000);
    CALL_PROCESS_ENCODING2(9);
    assert (0 == retcode && action_deliver == action);

    setValIntoBitstring(bs, 0, 9, 0b110001000);
    CALL_PROCESS_ENCODING2(9);
    assert (-8 == retcode);

    setValIntoBitstring(bs, 0, 9, 0b110001001);
    CALL_PROCESS_ENCODING2(9);
    assert (-2 == retcode);

    // 4-bit ptr
    action = action_inval;
    setValIntoBitstring(bs, 0, 8, 0b11100000);
    CALL_PROCESS_ENCODING2(8);
    assert (0 == retcode && action_deliver == action);

    setValIntoBitstring(bs, 0, 8, 0b11100111);
    CALL_PROCESS_ENCODING2(8);
    assert (-8 == retcode);

    setValIntoBitstring(bs, 0, 8, 0b11101000);
    CALL_PROCESS_ENCODING2(8);
    assert (-2 == retcode);

    //////////
    printf("%s() passed.\n", __func__);
    freeBitString(&bs);
    return 0;
}

int testProcessEncoding2_oneSuccessor()
{
    bitstring bs = NULL;
    bool linkId2UpStatus[] = {
        1,1,1,1,1,1,1,1, 1,1,1,1,1,1,1,1,
        1,1,1,1,1,1,1,1, 1,1,1,1,1,1,1,1,
        1,1,1,1,1,1,1,1, 1,1,1,1,1,1,1,1,
        1,1,1,1,1,1,1,1, 1,1,1,1,1,1,1,1,
    };
    unsigned int numLinks = ARRAY_LENGTH(linkId2UpStatus);
    action_t action;
    unsigned int outLinkId = 0;
    unsigned int lengthInBits = 0;
    unsigned int newLengthInBits = 0xbeefcafe; // processEncoding2()
                                               // shouldn't touch this
    int retcode = 0;

#undef REINIT
#define REINIT(boolArray)                                               \
    lengthInBits = ARRAY_LENGTH((boolArray));                           \
    freeBitString(&bs);                                                 \
    bs = newBitStringFromBoolArray((boolArray), lengthInBits)

#undef CALL_PROCESS_ENCODING2
#define CALL_PROCESS_ENCODING2(lengthInBits)                        \
    action = action_inval;                                          \
    outLinkId = 0xdeadcafe;                                         \
    retcode = processEncoding2(bs, (lengthInBits), linkId2UpStatus, \
                               numLinks, &action, &outLinkId,       \
                               &newLengthInBits);                   \
    assert (0xbeefcafe == newLengthInBits)

#undef CALL_PROCESS_ENCODING2_NUMLINKS
#define CALL_PROCESS_ENCODING2_NUMLINKS(lengthInBits, numLinks)     \
    retcode = processEncoding2(bs, (lengthInBits), linkId2UpStatus, \
                               (numLinks), &action, &outLinkId,     \
                               &newLengthInBits)

    //////////
    bool array1[] = {
        1,0, 0,0,0,0,1,0,1,0, /* 0-9 */
        0, 1,1,1,0, 1,0,1,0, 0,0,0,0,0,0,0,0,0,
    };

    REINIT(array1);

    // bad linkId len spec
    CALL_PROCESS_ENCODING2(lengthInBits);
    assert (-3 == retcode);
    assert (0b1000001010011101010000000000 == getValFromBitstring(bs, 0, 28));

    // linkId too big
    setValIntoBitstring(bs, 10, 4, 0b0100);
    CALL_PROCESS_ENCODING2_NUMLINKS(lengthInBits, 10);
    assert (-4 == retcode);
    assert (0b1000001010010001010000000000 == getValFromBitstring(bs, 0, 28));

    // too short for linkId
    CALL_PROCESS_ENCODING2(18);
    assert (-3 == retcode);
    assert (0b1000001010010001010000000000 == getValFromBitstring(bs, 0, 28));

    // too short for "containsPtr?"
    CALL_PROCESS_ENCODING2(19);
    assert (-3 == retcode);
    assert (0b1000001010010001010000000000 == getValFromBitstring(bs, 0, 28));

    // link is down
    linkId2UpStatus[10] = false;
    CALL_PROCESS_ENCODING2_NUMLINKS(20, 11);
    assert (4 == retcode && action_drop == action);
    assert (0b1000001010010001010000000000 == getValFromBitstring(bs, 0, 28));

    // all good, link is up, no ptr -> curptr == 20
    linkId2UpStatus[10] = true;
    CALL_PROCESS_ENCODING2_NUMLINKS(20, 11);
    assert (3 == retcode && 20 == getValFromBitstring(bs, 2, 8) &&
            action_forward == action && 10 == outLinkId);
    assert (0b1000010100010001010000000000 == getValFromBitstring(bs, 0, 28));

    // too short for successor ptr
    setValIntoBitstring(bs, 2, 8, 0b00001010);
    setValIntoBitstring(bs, 19, 9, 0b110101011);
    CALL_PROCESS_ENCODING2(27);
    assert (-3 == retcode);
    assert (0b1000001010010001010110101011 == getValFromBitstring(bs, 0, 28));

    // all good, link is up, there is ptr
    CALL_PROCESS_ENCODING2(28);
    assert (1 == retcode && 0b10101011 == getValFromBitstring(bs, 2, 8) &&
            action_forward == action && 10 == outLinkId);
    assert (0b1010101011010001010110101011 == getValFromBitstring(bs, 0, 28));

    //////////
    bool array2[] = {
        1,1,0, 0,1,1,1,1,1, /* 0-8 */
        0, 1,0, 0,0,1,0,0,1, 0, /* 9-18 */
        0, 0, 1,1,1, 1, 0,0,0,0,0,0, /* 19-30 */
        0, 1,1,0, 0,0,0,0,0,0,1,1,1,0,1, 1, 0,0,1,0,0,1, /* 31-52 */
    };

    REINIT(array2);

    // ptr currently at the last node descriptor
    CALL_PROCESS_ENCODING2(lengthInBits);
    assert (1 == retcode && 0b11101 == outLinkId && action_forward == action);
    assert (0b11000100101000100100011110000000 == getValFromBitstring(bs,0,32));
    assert (0b0110000000111011001001 == getValFromBitstring(bs,31,22));

    // ptr now at the first node descriptor
    CALL_PROCESS_ENCODING2(lengthInBits);
    assert (3 == retcode && 0b1001 == outLinkId && action_forward == action);
    assert (0b11001001101000100100011110000000 == getValFromBitstring(bs,0,32));
    assert (0b0110000000111011001001 == getValFromBitstring(bs,31,22));

    // ptr now at the second node descriptor
    CALL_PROCESS_ENCODING2(lengthInBits);
    assert (1 == retcode && 0b111 == outLinkId && action_forward == action);
    assert (0b11000000001000100100011110000000 == getValFromBitstring(bs,0,32));
    assert (0b0110000000111011001001 == getValFromBitstring(bs,31,22));

    // ptr now should be 0
    CALL_PROCESS_ENCODING2(lengthInBits);
    assert (0 == retcode && action_deliver == action);
    assert (0b11000000001000100100011110000000 == getValFromBitstring(bs,0,32));
    assert (0b0110000000111011001001 == getValFromBitstring(bs,31,22));

    //////////
    printf("%s() passed.\n", __func__);
    freeBitString(&bs);
    return 0;
}

int testProcessEncoding2_twoSuccessors()
{
    bitstring bs = NULL;
    bool linkId2UpStatus[] = {
        1,1,1,1,1,1,1,1, 1,1,1,1,1,1,1,1,
        1,1,1,1,1,1,1,1, 1,1,1,1,1,1,1,1,
        1,1,1,1,1,1,1,1, 1,1,1,1,1,1,1,1,
        1,1,1,1,1,1,1,1, 1,1,1,1,1,1,1,1,
    };
    unsigned int numLinks = ARRAY_LENGTH(linkId2UpStatus);
    action_t action;
    unsigned int outLinkId = 0;
    unsigned int lengthInBits = 0;
    unsigned int newLengthInBits = 0xbeefcafe; // processEncoding2()
                                               // shouldn't touch this
    int retcode = 0;

#undef REINIT
#define REINIT(boolArray)                                       \
    lengthInBits = ARRAY_LENGTH((boolArray));                   \
    freeBitString(&bs);                                         \
    bs = newBitStringFromBoolArray((boolArray), lengthInBits)

#undef CALL_PROCESS_ENCODING2
#define CALL_PROCESS_ENCODING2(lengthInBits)                        \
    action = action_inval;                                          \
    outLinkId = 0xdeadcafe;                                         \
    retcode = processEncoding2(bs, (lengthInBits), linkId2UpStatus, \
                               numLinks, &action, &outLinkId,       \
                               &newLengthInBits);                   \
    assert (0xbeefcafe == newLengthInBits)

#undef CALL_PROCESS_ENCODING2_NUMLINKS
#define CALL_PROCESS_ENCODING2_NUMLINKS(lengthInBits, numLinks)     \
    retcode = processEncoding2(bs, (lengthInBits), linkId2UpStatus, \
                               (numLinks), &action, &outLinkId,     \
                               &newLengthInBits)

    ///////
    // this section is all about testing the 2nd successor. when the
    // 1st successor link is up, then because it doesnt contain a ptr,
    // we will have to parse the 2nd successor to compute the new
    // ptr. when the 1st successor link is down, then of course has to
    // parse the 2nd successor.
    ///////
    bool array1[] = {
        1,0, 0,0,0,0,1,0,1,0, /* 0-9 */
        1,
          0, 0,0,0, 0,  /* 1st successor */
          1,1,1, 0,0,0,0,0,0,1,0,0,1,0, 0, 1,1,1,1,1,0,0,1, /* 2nd successor */
    };

    REINIT(array1);

    // bad linkId len spec
    linkId2UpStatus[0] = 1;
    CALL_PROCESS_ENCODING2(lengthInBits);
    assert (-5 == retcode);
    assert (0b100000101010000011100000010 == getValFromBitstring(bs, 0, 27));

    linkId2UpStatus[0] = 0;
    CALL_PROCESS_ENCODING2(lengthInBits);
    assert (-6 == retcode);
    assert (0b100000101010000011100000010 == getValFromBitstring(bs, 0, 27));

    // too short for linkId
    setValIntoBitstring(bs, 18, 1, 0b0);
    linkId2UpStatus[0] = 1;
    CALL_PROCESS_ENCODING2(29);
    assert (-5 == retcode);
    assert (0b10000010101000001100000001001 == getValFromBitstring(bs, 0, 29));

    linkId2UpStatus[0] = 0;
    CALL_PROCESS_ENCODING2(29);
    assert (-6 == retcode);
    assert (0b10000010101000001100000001001 == getValFromBitstring(bs, 0, 29));

    // too short for "containsPtr?"
    linkId2UpStatus[0] = 1;
    CALL_PROCESS_ENCODING2(30);
    assert (-5 == retcode);
    assert (0b100000101010000011000000010010 == getValFromBitstring(bs, 0, 30));

    linkId2UpStatus[0] = 0;
    CALL_PROCESS_ENCODING2(30);
    assert (-6 == retcode);
    assert (0b100000101010000011000000010010 == getValFromBitstring(bs, 0, 30));

    // no parsing error, containsPtr==false
    linkId2UpStatus[0] = 1;
    CALL_PROCESS_ENCODING2(31);
    assert (2 == retcode && action_forward == action && 0b0 == outLinkId);
    assert (0b1000011111100000110000000100100 == getValFromBitstring(bs, 0,31));

    linkId2UpStatus[0] = 0;
    setValIntoBitstring(bs, 0, 30, 0b100000101010000011000000010010);
    CALL_PROCESS_ENCODING2_NUMLINKS(31, 16); // make the link id too
                                             // big
    assert (-7 == retcode);
    assert (0b100000101010000011000000010010 == getValFromBitstring(bs, 0, 30));

    // too short for the ptr
    REINIT(array1);
    setValIntoBitstring(bs, 18, 1, 0b0);
    setValIntoBitstring(bs, 30, 1, 0b1); // make containsPtr true

    linkId2UpStatus[0] = 1;
    CALL_PROCESS_ENCODING2(38);
    assert (-5 == retcode);
    assert (0b10000010101000001100000001001011 == getValFromBitstring(bs,0,32));
    assert (0b1111001 == getValFromBitstring(bs,32,7));

    linkId2UpStatus[0] = 0;
    CALL_PROCESS_ENCODING2(38);
    assert (-6 == retcode);
    assert (0b10000010101000001100000001001011 == getValFromBitstring(bs,0,32));
    assert (0b1111001 == getValFromBitstring(bs,32,7));

    // no parsing error, contains ptr
    linkId2UpStatus[0] = 1;
    CALL_PROCESS_ENCODING2(39);
    assert (2 == retcode && action_forward == action && 0b0 == outLinkId);
    assert (0b10001001111000001100000001001011 == getValFromBitstring(bs,0,32));
    assert (0b1111001 == getValFromBitstring(bs,32,7));

    ////

    //// 1st successor link down
    linkId2UpStatus[0] = 0;

    REINIT(array1);
    setValIntoBitstring(bs, 18, 1, 0b0);

    // 2nd successor link down
    linkId2UpStatus[18] = 0;
    CALL_PROCESS_ENCODING2(31);
    assert (7 == retcode && action_drop == action);
    assert (0b1000001010100000110000000100100 == getValFromBitstring(bs,0,31));

    // 2nd successor link is up, no ptr
    linkId2UpStatus[18] = 1;
    CALL_PROCESS_ENCODING2(31);
    assert (6 == retcode && action_forward == action && 18 == outLinkId);
    assert (0b1000011111100000110000000100100 == getValFromBitstring(bs,0,31));

    ////
    REINIT(array1);
    setValIntoBitstring(bs, 18, 1, 0b0);
    setValIntoBitstring(bs, 30, 1, 0b1); // make containsPtr true

    CALL_PROCESS_ENCODING2(39);
    assert (5 == retcode && action_forward == action && 18 == outLinkId);
    assert (0b10111110011000001100000001001011 == getValFromBitstring(bs,0,32));
    assert (0b1111001 == getValFromBitstring(bs,32,7));

    //////////
    bool array2[] = {
        1,0, 0,1,0,0,0,1,1,0, /* 0-9 */

        1,
          0, 1,0,0, 1, 1,0,1,1,1,0,0,0,  /* 1st successor, 11-23 */
          1,1,0, 0,0,0,0,0,0,0,1,1,0,1, 0, /* 2nd successor, 24-38 */

        1,
          1,0, 0,1,1,1,1,1, 1, 0,1,0,1,0,1,0,1, /* 1st successor, 40-56 */
          0, 0,1,1, 1, 0,1,1,0,0,0,1,1, /* 2nd successor, 57-69 */

        1,
          1,1,0, 0,0,0,0,0,0,1,0,1,0,0, 0, /* 1st successor, 71-85 */
          0, 0,0,0, 1, 0,0,0,0,1,0,1,0, /* 2nd successor, 86-98 */

        1,
          0, 1,1,1, 0, /* 1st successor, 100-104 */
          1,0, 0,0,1,1,1,1, 0, /* 2nd successor, 105-113 */

        1,
          0, 1,0,0, 1, 1,1,1,1,1,1,1,1, /* 1st successor, 115-127 */
          0, 0,1,1, 1, 0,0,0,0,0,0,0,0, /* 2nd successor */

    };

    // prepare the link status array
    for (int i = 0; i < ARRAY_LENGTH(linkId2UpStatus); i++) {
        if (0b100 == i || 0b11111 == i || 0b10100 == i) {
            linkId2UpStatus[i] = false;
        }
        else {
            linkId2UpStatus[i] = true;
        }
    }

    REINIT(array2);

    // ptr currently at the 3rd node descriptor

    CALL_PROCESS_ENCODING2(lengthInBits);
    assert (5 == retcode && 0 == outLinkId && action_forward == action);
    assert (0b00001010 == getValFromBitstring(bs,2,8));
    assert (0b10000010101010011011100011000000 == getValFromBitstring(bs,0,32));
    assert (0b00110101100111111010101010011101 == getValFromBitstring(bs,32,32));
    assert (0b10001111100000001010000000100001 == getValFromBitstring(bs,64,32));
    assert (0b01010111010001111010100111111111 == getValFromBitstring(bs,96,32));
    assert (0b0011100000000 == getValFromBitstring(bs,128,13));

    // ptr currently at the 1st node descriptor

    CALL_PROCESS_ENCODING2(lengthInBits);
    assert (6 == retcode && 0b1101 == outLinkId && action_forward == action);
    assert (0b00100111 == getValFromBitstring(bs,2,8));
    assert (0b10001001111010011011100011000000 == getValFromBitstring(bs,0,32));
    assert (0b00110101100111111010101010011101 == getValFromBitstring(bs,32,32));
    assert (0b10001111100000001010000000100001 == getValFromBitstring(bs,64,32));
    assert (0b01010111010001111010100111111111 == getValFromBitstring(bs,96,32));
    assert (0b0011100000000 == getValFromBitstring(bs,128,13));

    // ptr currently at the 2nd node descriptor

    CALL_PROCESS_ENCODING2(lengthInBits);
    assert (5 == retcode && 0b011 == outLinkId && action_forward == action);
    assert (0b01100011 == getValFromBitstring(bs,2,8));
    assert (0b10011000111010011011100011000000 == getValFromBitstring(bs,0,32));
    assert (0b00110101100111111010101010011101 == getValFromBitstring(bs,32,32));
    assert (0b10001111100000001010000000100001 == getValFromBitstring(bs,64,32));
    assert (0b01010111010001111010100111111111 == getValFromBitstring(bs,96,32));
    assert (0b0011100000000 == getValFromBitstring(bs,128,13));

    // ptr currently at the 4th node descriptor

    CALL_PROCESS_ENCODING2(lengthInBits);
    assert (2 == retcode && 0b111 == outLinkId && action_forward == action);
    assert (0b01110010 == getValFromBitstring(bs,2,8));
    assert (0b10011100101010011011100011000000 == getValFromBitstring(bs,0,32));
    assert (0b00110101100111111010101010011101 == getValFromBitstring(bs,32,32));
    assert (0b10001111100000001010000000100001 == getValFromBitstring(bs,64,32));
    assert (0b01010111010001111010100111111111 == getValFromBitstring(bs,96,32));
    assert (0b0011100000000 == getValFromBitstring(bs,128,13));

    // ptr currently at the 5th node descriptor

    CALL_PROCESS_ENCODING2(lengthInBits);
    assert (5 == retcode && 0b011 == outLinkId && action_forward == action);
    assert (0b00000000 == getValFromBitstring(bs,2,8));
    assert (0b10000000001010011011100011000000 == getValFromBitstring(bs,0,32));
    assert (0b00110101100111111010101010011101 == getValFromBitstring(bs,32,32));
    assert (0b10001111100000001010000000100001 == getValFromBitstring(bs,64,32));
    assert (0b01010111010001111010100111111111 == getValFromBitstring(bs,96,32));
    assert (0b0011100000000 == getValFromBitstring(bs,128,13));

    // ptr currently has value 0 -> deliver

    CALL_PROCESS_ENCODING2(lengthInBits);
    assert (0 == retcode && action_deliver == action);
    assert (0b00000000 == getValFromBitstring(bs,2,8));
    assert (0b10000000001010011011100011000000 == getValFromBitstring(bs,0,32));
    assert (0b00110101100111111010101010011101 == getValFromBitstring(bs,32,32));
    assert (0b10001111100000001010000000100001 == getValFromBitstring(bs,64,32));
    assert (0b01010111010001111010100111111111 == getValFromBitstring(bs,96,32));
    assert (0b0011100000000 == getValFromBitstring(bs,128,13));

    //////////
    printf("%s() passed.\n", __func__);
    freeBitString(&bs);
    return 0;
}

int main()
{
    testParseOneSuccessor();
    testProcessEncoding2_curPtr();
    testProcessEncoding2_oneSuccessor();
    testProcessEncoding2_twoSuccessors();
    return 0;
}
