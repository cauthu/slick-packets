#include <stdlib.h>
#include <assert.h>
#include <vector>
#include <map>
#include <iostream>
#include "bitstring.h"
#include "encoding3.h"
#include "utils.h"

/* this contains stuff for encoding type 3 */

/*
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

    the high level forwarding algorithm is (though it differs a little
    from the code below because the code below does only the
    processing logic, not the forwarding):

    <verbatim>
    link label L = label at the front of the encoding
    strip L off the encoding

    if link L is <null-link>:
        # i am the egress/destination router, do whatever ...
        exit
    elif link L works:
        if <on-detour?> is 0:
            strip off link labels at front of encoding one-by-one until
            and including the <null-link>
        fi
        forward out link L
        exit
    else:
        if <on-detour?> is 0:
            L = label at the front of the encoding
            strip L off the encoding
            if link L is <null-link>:
                # a primary node that does not have a detour path
                drop packet
                exit
            else:
                if link L is down:
                    drop packet
                    exit
                else:
                    set <on-detour?> to 1
                    forward out link L
                    exit
                fi
            fi
        else:
            drop packet
            exit
        fi
    fi
    </verbatim>
*/
                
static char rcsid[] = "$Id$";

static int consumeLinkLabel(const bitstring encoding,
                            const unsigned int& encodingLen,
                            unsigned int& curBitNum,
                            bool& isNull);
static int consumeUpToIncludingNullLinkLabel(bitstring encoding,
                                             const unsigned int& encodingLen,
                                             unsigned int& curBitNum);


/*
  each link is <length><link value> where:

  <length> begins with bit 1:
  10   for 3 bits
  110  for 6 bits
  1110 for 11 bits
 
  special <null-link> is just one bit 0, i.e., length field is a
  single bit of zero, and no <link value> field.
*/
static const unsigned int numSetBits2Len[] = {
    0, 3, 6, 11,
};

/* starting at "curBitNum", consume all link labels up to and
 * including the first found null-link label.
 *
 * "encodingLen" is the length in bits of the encoding. it's an error
 * if having to go past the length.
 *
 * on success, return 0. "curBitNum" will be updated to be just PAST
 * the end of the first found null-link label.
 *
 * on errors, return -1. "curBitNum" not changed.
 *
 */
static int consumeUpToIncludingNullLinkLabel(bitstring encoding,
                                             const unsigned int& encodingLen,
                                             unsigned int& curBitNum)
{
    int mybitnum = curBitNum;

    do {
        if (mybitnum >= encodingLen) {
            return -1;
        }

        unsigned int valnumbits = 0; // num bits occupied by this
                                     // var-len value.
        int retcode = getVarLenValFromBitstring(
            encoding, encodingLen, mybitnum, numSetBits2Len,
            ARRAY_LENGTH(numSetBits2Len), NULL, NULL, &valnumbits);

        if (-1 == retcode) {
            // malformed encoding
            return -1;
        }
        else if (-2 == retcode) {
            // found null link, done
            curBitNum = mybitnum + valnumbits;
            return 0;
        }
        else {
            // found a non-null link
            mybitnum += valnumbits;
        }
    }
    while (true);

    // did not find null link
    return -1;
}

/* consume a link label starting at "curBitNum" of the encoding. if a
 * link label is successfully "consumed", the "curBitNum" will be
 * updated to be PAST the end of the consumed link label.
 *
 * "encodingLen" is the length in bits of the encoding. it's an error
 * if having to go past the length.
 *
 * "isNull" will be cleared first.
 *
 * return the integer link label (possibly 0). if the special
 * null-link, then "isNull" will be true.
 *
 * on error, returns negative value, and curBitNum is not changed.
 */
static int consumeLinkLabel(const bitstring encoding,
                            const unsigned int& encodingLen,
                            unsigned int& curBitNum,
                            bool& isNull)
{
    unsigned int linkId = 0;
    unsigned int valnumbits = 0; // num bits occupied by this var-len
                                 // value.

    isNull = false;

    int retcode = getVarLenValFromBitstring(
        encoding, encodingLen, curBitNum, numSetBits2Len,
        ARRAY_LENGTH(numSetBits2Len), &linkId, NULL, &valnumbits);
    if (0 == retcode) {
        // good
        retcode = linkId;
    }
    else if (-2 == retcode) {
        isNull = true;
        retcode = 0;
    }
    else {
        return -1;
    }

    curBitNum += valnumbits;
    return retcode;
}

/***************************************************/
int processEncoding3(unsigned char* encoding,
                     const unsigned int& encodingLen,
                     const bool linkId2UpStatus[],
                     const unsigned int& numLinks,
                     action_t* ret_action,
                     unsigned int* ret_outLinkId,
                     unsigned int* ret_newEncodingLen)
{
    int linkId = 0;
    unsigned int curBitNum = 1; // bit 0th is "on-detour?"
    bool isNull = false;
    int onDetour = encoding[0] & (0x80);

    *ret_action = action_inval;

    linkId = consumeLinkLabel(encoding, encodingLen, curBitNum, isNull);

    if (linkId < 0) {
        // error
        return -1;
    }
    else if (linkId >= numLinks) {
        return -2;
    }
    else if (isNull) {
        *ret_action = action_deliver;
        return 0;
    }
    else if (linkId2UpStatus[linkId]) {
        // link is online
        if (!onDetour) {
            // not on detour -> strip off my entire the detour path
            if (consumeUpToIncludingNullLinkLabel(
                    encoding, encodingLen, curBitNum) < 0)
            {
                // error
                return -3;
            }
        }
    }
    else {
        // link is down
        if (!onDetour) {
            // not yet on detour

            linkId = consumeLinkLabel(
                encoding, encodingLen, curBitNum, isNull);
            if (linkId < 0) {
                // error
                return -4;
            }
            else if (linkId >= numLinks) {
                return -5;
            }
            else if (isNull) {
                // a primary node that does not have a detour path
                *ret_action = action_drop;
                return 0;
            }
            else {
                if (!linkId2UpStatus[linkId]) {
                    *ret_action = action_drop;
                    return 0;
                }
                // toggle "onDetour"
                onDetour = 1;
            }
        }
        else {
            // already on detour
            *ret_action = action_drop;
            return 0;
        }
    }

    *ret_action = action_forward;
    *ret_outLinkId = linkId;

    //////// prepare the new encoding

    // the onDetour bit
    setValIntoBitstring(encoding, 0, 1, onDetour ? 1 : 0);
    *ret_newEncodingLen = encodingLen - (curBitNum - 1);
    removeFromBitstring(encoding, encodingLen, 1, curBitNum - 1);
    return 0;
}
