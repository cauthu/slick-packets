#ifndef ENCODING_H
#define ENCODING_H

/* $Id$ */

typedef enum {
  action_forward,
  action_drop,
  action_deliver,
  action_inval,
} action_t;

/* the return value should be 0 for success. any non-zero value is
 * considered an error.
 */
typedef int (*encoding_process_func_t)(unsigned char* encoding,
                                       const unsigned int& encodingLen,
                                       const bool linkId2UpStatus[],
                                       const unsigned int& numLinks,
                                       action_t* ret_action,
                                       unsigned int* ret_outLinkId,
                                       unsigned int* ret_newEncodingLen);

#endif /* ENCODING_H */
