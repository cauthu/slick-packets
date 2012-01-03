#ifndef ENCODING2_H
#define ENCODING2_H

#include "encoding.h"

/*
  !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
  !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
  !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!

  NOTE: only bit alignment is currently supported.

  !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
  !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
  !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
*/

int processEncoding2(unsigned char* encoding,
                     const unsigned int& lengthInBits,
                     const bool linkId2UpStatus[],
                     const unsigned int& numLinks,
                     action_t* ret_action,
                     unsigned int* ret_outLinkId,
                     unsigned int* ret_newLengthInBits);

#endif /* ENCODING2_H */
