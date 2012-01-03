#ifndef ENCODING3_H
#define ENCODING3_H

#include "encoding.h"

int processEncoding3(unsigned char* encoding,
                     const unsigned int& lengthInBits,
                     const bool linkId2UpStatus[],
                     const unsigned int& numLinks,
                     action_t* ret_action,
                     unsigned int* ret_outLinkId,
                     unsigned int* ret_newLengthInBits);

#endif /* ENCODING3_H */
