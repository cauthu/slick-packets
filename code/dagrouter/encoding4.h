#ifndef ENCODING4_H
#define ENCODING4_H

#include "encoding.h"

int processEncoding4(unsigned char* encoding,
                     const unsigned int& lengthInBits,
                     const bool linkId2UpStatus[],
                     const unsigned int& numLinks,
                     action_t* ret_action,
                     unsigned int* ret_outLinkId,
                     unsigned int* ret_newLengthInBits);

#endif /* ENCODING4_H */
