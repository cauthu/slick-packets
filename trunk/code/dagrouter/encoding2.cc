#include <stdlib.h>
#include <assert.h>
#include <vector>
#include <map>
#include <iostream>
#include "bitstring.h"
#include "encoding2.h"
#include "utils.h"

/* this contains stuff for encoding type 2 */
                
static char rcsid[] =
    "$Id$";

/*

  !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
  !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
  !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!

  NOTE: only bit alignment is currently supported.

  !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
  !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
  !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
  
    * <len of ptr><current ptr><Node>[<Node>...]

    - len of ALL ptrs in this encoding.

    0      -> all ptrs are   10 bits
    10     ->                8
    110    ->                6
    1110   ->                4

    * <Node> = <# of successors><Successor>[<Successor>]

    - # of successors: 1 bit: "0" for 1 successor, "1" for 2 successors.

    * <Successor> = <len of ID><ID><contains ptr?>[<ptr>]

    - len of ID:

    0   -> ID is 3 bits
    10  ->       6
    110 ->       11

    - contains ptr?: 1 bit: "0" for no, in which case, this node is
      part of a "group". so, the node descriptor of the successor
      immediately follows this node descriptor, so the offset to put
      into the global current ptr can be computed.

    - ptr: this field exists if and only if "contains ptr?" is true
      ("1").

*/

static const unsigned int g_ptrLen_numSetBits2Len[] = {
    10, 8, 6, 4,
};

static const unsigned int g_linkIdLen_numSetBits2Len[] = {
    3, 6, 11,
};

typedef struct {
    unsigned int linkId;
    bool containsPtr;
    unsigned int nodePtr; // valid iff containsPtr==true
} successor_t;

/***************************************************/
static int parseOneSuccessor(const bitstring encoding,
                             const unsigned int& encodingLen,
                             const unsigned int& fromIdx,
                             const unsigned int& ptrLen,
                             unsigned int* ret_totalSuccessorLen,
                             successor_t* ret_successor)
{
    unsigned int ptr = fromIdx;
    bool containsPtr = false;
    unsigned int valnumbits = 0;
    int retcode = 0;

    if (fromIdx >= encodingLen) {
        // out of bounds
        return -1;
    }

    retcode = getVarLenValFromBitstring(
        encoding, encodingLen, ptr, g_linkIdLen_numSetBits2Len,
        ARRAY_LENGTH(g_linkIdLen_numSetBits2Len),
        ret_successor ? &(ret_successor->linkId) : NULL,
        NULL, &valnumbits);
    if (0 != retcode) {
        return -2;
    }

    ptr += valnumbits;

    /////
    if (ptr >= encodingLen) {
        return -3;
    }
    containsPtr = (1 == getValFromBitstring(encoding, ptr, 1));
    if (ret_successor) {
        ret_successor->containsPtr = containsPtr;
    }

    ptr += 1;

    /////
    if (containsPtr) {
        if ((ptr + ptrLen - 1) >= encodingLen) {
            // out of bounds
            return -4;
        }
        if (ret_successor) {
            ret_successor->nodePtr = getValFromBitstring(encoding, ptr, ptrLen);
        }
        ptr += ptrLen;
    }

    if (ret_totalSuccessorLen) {
        *ret_totalSuccessorLen = ptr - fromIdx;
    }

    return 0;
}

/***************************************************/
/* this function is required to return 0 on success, and any non-zero
 * value will be considered an error.
 *
 * however, to aid unit testing, will also return various distinct
 * positive values for success, to indicate various points of code
 * that is reached. to enable the return of possible values, then
 * define UNIT_TESTING.
 *
 */

int processEncoding2(unsigned char* encoding,
                     const unsigned int& encodingLen,
                     const bool linkId2UpStatus[],
                     const unsigned int& numLinks,
                     action_t* ret_action,
                     unsigned int* ret_outLinkId,
                     unsigned int* ret_newEncodingLen)
{
    unsigned int ptrLen = 0;
    unsigned int curNodePtr = 0; /* this is the one at the front of
                                  * the encoding. */
    unsigned int newNodePtr = 0; /* update the encoding with this. */
    unsigned int ptr = 0; /* this is for tmp usage */
    int retcode;
    unsigned int lenSpecNumBits = 0; /* len in bits of the ptr len
                                      * spec */
    unsigned int curNodePtrTotalNumBits = 0;

    unsigned int numSuccessors = 0;
    successor_t successor;
    unsigned int successorLen = 0; /* len in bits of a successor */

#undef ASSIGN_RETCODE

/* if unit_testing, then keep the code as is, otherwise, make all
 * positive values of code into 0 for retcode.
 */
#ifndef UNIT_TESTING
#define ASSIGN_RETCODE(code)                     \
    do {                                         \
        int _code = (code);                      \
        retcode = (_code >= 0) ? 0 : _code;      \
    }                                            \
    while (0)

#else
#define ASSIGN_RETCODE(code)                     \
    retcode = (code)

#endif

    *ret_action = action_inval;

    /* determine the ptr len and the current ptr */
    retcode = getVarLenValFromBitstring(
        encoding, encodingLen, 0, g_ptrLen_numSetBits2Len,
        ARRAY_LENGTH(g_ptrLen_numSetBits2Len),
        &curNodePtr, &lenSpecNumBits, &curNodePtrTotalNumBits);
    if (0 != retcode) {
        ASSIGN_RETCODE( -1);
        goto bail;
    }
    if (0 == curNodePtr) {
        *ret_action = action_deliver;
        ASSIGN_RETCODE( 0);
        goto bail;
    }
    if (curNodePtr < curNodePtrTotalNumBits) {
        ASSIGN_RETCODE( -8);
        goto bail;
    }
    ptr = curNodePtr;

    ptrLen = curNodePtrTotalNumBits - lenSpecNumBits; // length of all ptrs

    // get the number of successors
    if (ptr >= encodingLen) {
        ASSIGN_RETCODE( -2);
        goto bail;
    }
    if (0 == getValFromBitstring(encoding, ptr, 1)) {
        numSuccessors = 1;
    }
    else {
        numSuccessors = 2;
    }
    ptr += 1;

    // get the first successor
    // parseOneSuccessor() checks the bounds.
    retcode = parseOneSuccessor(
        encoding, encodingLen, ptr, ptrLen, &successorLen, &successor);
    if (0 != retcode) {
        ASSIGN_RETCODE( -3);
        goto bail;
    }
    if (successor.linkId >= numLinks) {
        ASSIGN_RETCODE( -4);
        goto bail;
    }
    ptr += successorLen;

    // is the link up?
    if (linkId2UpStatus[successor.linkId]) {
        // update the newNodePtr

        // is there a ptr?
        if (successor.containsPtr) {
            newNodePtr = successor.nodePtr;
            // TODO: maybe check bounds.
            ASSIGN_RETCODE( 1);
        }
        else {
            // there's no ptr -> it should be the next node descriptor
            if (2 == numSuccessors) {
                retcode = parseOneSuccessor(
                    encoding, encodingLen, ptr, ptrLen, &successorLen, NULL);
                if (0 != retcode) {
                    ASSIGN_RETCODE( -5);
                    goto bail;
                }
                newNodePtr = ptr + successorLen;
                ASSIGN_RETCODE( 2);
            }
            else {
                newNodePtr = ptr;
                ASSIGN_RETCODE( 3);
            }
            // TODO: maybe check bounds
        }
    }
    else {
        // link is down
        if (1 == numSuccessors) {
            *ret_action = action_drop;
            ASSIGN_RETCODE( 4);
            goto bail;
        }

        // there's an alternate successor
        retcode = parseOneSuccessor(
            encoding, encodingLen, ptr, ptrLen, &successorLen, &successor);
        if (0 != retcode) {
            ASSIGN_RETCODE( -6);
            goto bail;
        }
        if (successor.linkId >= numLinks) {
            ASSIGN_RETCODE( -7);
            goto bail;
        }
        ptr += successorLen;

        if (linkId2UpStatus[successor.linkId]) {
            // link is up

            // update the newNodePtr
            if (successor.containsPtr) {
                newNodePtr = successor.nodePtr;
                ASSIGN_RETCODE( 5);
            }
            else {
                newNodePtr = ptr;
                ASSIGN_RETCODE( 6);
            }
            // TODO: maybe check bounds
        }
        else {
            // link is down
            *ret_action = action_drop;
            ASSIGN_RETCODE( 7);
            goto bail;
        }
    }

    *ret_action = action_forward;
    *ret_outLinkId = successor.linkId;

    //////// prepare the new encoding
    assert (0 == setValIntoBitstring(
                encoding, lenSpecNumBits, ptrLen, newNodePtr));

bail:
    return retcode;
}
