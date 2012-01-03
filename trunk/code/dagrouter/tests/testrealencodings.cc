/* this program simulates both a client and a router. it reads from
 * input filenames the encodings, one by one, and sends them, one by
 * one, to the simulated router function.
 *
 * the input file can be in text format or binary format.
 *
 * the text format is: each encoding is on a separate line in the
 * file. each line should be:
 *
 * char 0th: the encoding type.
 * char 1st: a space.
 *
 * chars 2nd-nth: the encoding, with each char (ascii '1' or '0')
 * representing a single bit. effectively, (n-2)+1 bits.
 *
 *-------------------
 *
 * the binary format is simply one encoding after the other. each
 * encoding should be exactly as is expected by the router. because
 * the encoding has the 2 bytes meta-data, which includes the length
 * of the encoding, we can simply use that to know how much to read.
 *
 * ie, we will read 2 bytes. the 0th byte tells us how many more bytes
 * (say, N) to read. then the encoding is simply the 2+N bytes
 * together. then repeat.
 *
 * comments are supported and must start with 2 bytes, \n\xff, and end
 * with \n.
 *
 *
 * this keeps counts of the various errors that the dagrouter can run
 * into (including a "loop" error--where the same packet causes more
 * than g_maxRecurseLevel number recursive calls of the sim function.
 *
 */

#include <sys/types.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <stdio.h>
#include <unistd.h>
#include <errno.h>
#include <string.h>
#include <stdlib.h>
#include <iostream>
#include <assert.h>
#include <getopt.h>
#include <netdb.h>
#include "../utils.h"
#include "../bitstring.h"
#include "../encoding.h"
#include "../encoding2.h"
#include "../encoding3.h"

static const char rcsid[] =
    "$Id$";

static bool* g_linkId2UpStatus = NULL;
static unsigned int g_numNeighbors = 0;
static unsigned int g_maxRecurseLevel = 17*3;
static bool g_verbose = false;
static unsigned int g_retvalCount[16] = {0};

static const encoding_process_func_t encodingProcessFunctions[] = {
    NULL,
    NULL,
    processEncoding2,
    processEncoding3,
};

/*****************************************************/

/* this is the main packet processing code (copied) from
 * dagrouter.cc:loop(), only here we're dealing with only the encoding
 * part, and we're recursively calling ourselves.
 */

int dagrouter_sim(unsigned char* recv_data,
                  const int bytes_read,
                  const int recurseLevel)
{
    if (recurseLevel > g_maxRecurseLevel) {
        if (g_verbose) {
            printf("\nerror: reach max recurse level\n");
        }
        return 1;
    }

    if (g_verbose) {
        printf("\n--------------------"
               "\nrecv pkt of %d bytes\n", bytes_read);
    }

    // the encoding should be preceded by 2 bytes of meta-info
    // that is common to all encoding types.

    /* at least 2 bytes of meta-info */
    if (bytes_read < 2) {
        // drop packet
        if (g_verbose) {
            printf("  not at least 2 bytes --> drop\n");
        }
        return 2;
    }

    // how many bytes? max of 255
    unsigned char numBytes = recv_data[0];
    // how many bits IN the last byte? must be in range (1,8]
    // this is the 4 most significant bits of the 2nd byte
    unsigned char numBitsInLastByte = (recv_data[1] >> 4) & 0xf;
    // the 4 least significant bits of the 2nd byte
    unsigned char type = (recv_data[1]) & 0xf;

    if (g_verbose) {
        printf("  encoding: type %d\n"
               "            %d bytes,\n"
               "            %d bits in last byte\n",
               type, numBytes, numBitsInLastByte);
    }

    if (numBitsInLastByte < 1 || numBitsInLastByte > 8) {
        // drop packet
        if (g_verbose) {
            printf("  numBitsInLastByte < 1 || numBitsInLastByte > 8 --> drop\n");
        }
        return 3;
    }
    if ((2 + numBytes) != bytes_read) {
        // drop packet
        if (g_verbose) {
            printf("  (2 + numBytes) != bytes_read --> drop\n");
        }
        return 4;
    }
    if (type >= ARRAY_LENGTH(encodingProcessFunctions)) {
        // drop packet
        if (g_verbose) {
            printf("  type >= %d --> drop", ARRAY_LENGTH(encodingProcessFunctions));
        }
        return 5;
    }

    encoding_process_func_t processFunc = encodingProcessFunctions[type];

    if (processFunc == NULL) {
        // drop packet
        return 6;
    }

    action_t action = action_inval;
    unsigned int outLinkId = 0;
    unsigned int lengthInBits = ((numBytes - 1) * 8) + numBitsInLastByte;
    unsigned int newLengthInBits = lengthInBits;
    int retcode = processFunc(recv_data + 2,
                              lengthInBits,
                              g_linkId2UpStatus,
                              g_numNeighbors,
                              &action,
                              &outLinkId,
                              &newLengthInBits);

    if (retcode != 0) {
        // drop packet
        if (g_verbose) {
            printf("  error processing encoding --> drop\n");
        }
        return 7;
    }
    else if (action_drop == action) {
        if (g_verbose) {
            printf("  action_drop == action --> drop\n");
        }
        return 0;
    }
    else if (action_deliver == action) {
        // deliver packet
        if (g_verbose) {
            printf("  action_deliver == action --> deliver\n");
        }
        return 0;
    }
    else if (action_forward == action) {
        // we are to forward the packet. the encoding has been updated
        // appropriately
        assert (newLengthInBits > 0);

        if (g_verbose) {
            printf("  action_forward == action\n");
        }
        if (newLengthInBits != lengthInBits) {
            // update the meta-info with the new length
            numBitsInLastByte = (newLengthInBits % 8);
            if (numBitsInLastByte == 0) {
                // the last byte is full
                numBitsInLastByte = 8;
            }
            numBytes = (newLengthInBits / 8);
            if (numBitsInLastByte != 8) {
                numBytes += 1;
            }

            recv_data[0] = numBytes;
            recv_data[1] = (type) & 0xf;
            recv_data[1] |= ((numBitsInLastByte << 4) & /* in case
                                                         * 1's are
                                                         * pulled
                                                         * in */ 0xf0);
        }

        if (g_verbose) {
            printf("  forwarding out linkId %d\n", outLinkId);
        }
        // forward out link outLinkId
        return dagrouter_sim(recv_data, numBytes+2, recurseLevel+1);
    }

    assert (false); // not reached
    return 0;
}

/***************************************************/
void usageAndExit(const char* prog)
{
    printf("\n"
           "Usage: %s [-v] [-m MAXRECURSE] -n NUMNEIGHBORS -t|-b FILE\n"
           "\n"
           " Run a simulated client that reads encodings from FILE and feeds\n"
           " them to a simulated DAG router.\n"
           "\n"
           " -m MAXRECURSE: max number of recursive calls allowed for each encoding.\n"
           "\n"
           " -n NUMNEIGHBORS: number of neigbors.\n"
           "\n"
           " -t: encoding file is text format.\n"
           "\n"
           " -b: encoding file is binary format.\n"
           "\n"
           " -v: verbose.\n",
           prog);
    exit(0);
    return;
}

/*****************************************************/

int main(int argc, char* argv[])
{
    // the input encodings, whether they are text or binary
    int binary = 0;
    int text = 0;
    bitstring encoding = NULL;
    unsigned int encodingNum = 0;

    int c;

    // disable stdout buffering
    setvbuf(stdout, NULL, _IONBF, 0);

    while ((c = getopt(argc, argv, "m:n:vbt")) != -1) {
        switch (c) {
        case 'm':
            g_maxRecurseLevel = strtol(optarg, (char **) NULL, 10);
            break;
        case 'n':
            g_numNeighbors = strtol(optarg, (char **) NULL, 10);
            break;
        case 'b':
            binary = 1;
            break;
        case 't':
            text = 1;
            break;
        case 'v':
            g_verbose = true;
            break;
        default:
            abort();
        }
    }

    if (!(g_numNeighbors > 0)) {
        usageAndExit(argv[0]);
    }

    g_linkId2UpStatus = (bool*)calloc(g_numNeighbors, sizeof(bool));
    assert (g_linkId2UpStatus);

    // for now, make all links up by default
    for (int i = 0; i < g_numNeighbors; i++) {
        g_linkId2UpStatus[i] = true;
    }

    if (!(optind < argc)) {
        usageAndExit(argv[0]);
    }

    if (!(binary ^ text)) {
        usageAndExit(argv[0]);
    }

    if (text) {
        const char *filename = argv[optind];

        FILE *file = fopen(filename, "r");
        if (file != NULL) {
            // each line starts with one char specifying the encoding
            // type (0-3), followed by a space, then the encoding,
            // which is a sequence of "1" or "0" characters, until the
            // end of the line.

            static const int size = 3000;
            char line[size];
            while (fgets(line, sizeof(line) - 1, file) != NULL) {
                unsigned char encodingType = (line[0] - '0');
                assert (encodingType >= 0 && encodingType <= 3);
                assert (line[1] == ' ');
                // find the newline
                char* idxOfNewline = strchr(line + 2, '\n');
                assert (idxOfNewline != NULL);
                unsigned int lengthInBits = idxOfNewline - (line+2);

                assert (lengthInBits <= (8*255));

                freeBitString(&encoding);
                // "+ 2*8" for the 2 bytes of meta-data
                encoding = newBitString(lengthInBits + 2*8);
                assert (encoding != NULL);

                // setting the encoding (after the 2-byte meta-data)
                for (int i = 0; i < lengthInBits; i++) {
                    switch (line[2 + i]) {
                    case '1':
                        setValIntoBitstring(encoding, i+16, 1, 1);
                        break;
                    case '0':
                        setValIntoBitstring(encoding, i+16, 1, 0);
                        break;
                    default:
                        abort();
                    }
                }

                unsigned char numBitsInLastByte = (lengthInBits % 8);
                if (numBitsInLastByte == 0) {
                    // the last byte is full
                    numBitsInLastByte = 8;
                }
                unsigned char numBytes = (lengthInBits / 8);
                if (numBitsInLastByte != 8) {
                    numBytes += 1;
                }

                encoding[0] = numBytes;
                encoding[1] = encodingType & 0xf;
                encoding[1] |= ((numBitsInLastByte << 4) & /* in case
                                                            * 1's are
                                                            * pulled
                                                            * in */ 0xf0);

                printf("\nencoding number: %u\n", encodingNum++);
                // now send the pkt
                int retval = dagrouter_sim(encoding, numBytes+2, 0);
                assert (retval < ARRAY_LENGTH(g_retvalCount));
                g_retvalCount[retval]++;
                printf("  processing retval: %u\n", retval);
            }
        }
        else {
            perror("file");
            exit(-1);
        }
    }
    else {
        const char *filename = argv[optind];

        FILE *file = fopen(filename, "rb");
        if (file != NULL) {
            // the encoding should be exactly as is expected by the router.

            // ie, we will read 2 bytes. the 0th byte tells us how
            // many more bytes (say, N) to read. then the encoding is
            // simply the 2+N bytes together.

            static const int size = 3000;
            unsigned char line[size];
            while (fread(line, 1, 2, file) == 2) {
                if (line[0] == '\n' && line[1] == 0xff) {
                    // a comment, read to (including) next new line
                    fgets((char *)line, sizeof(line) - 1, file);
                    continue;
                }
                unsigned char *encoding = line;
                const int numBytes = encoding[0];
                if (fread(&(encoding[2]), 1, numBytes, file) == numBytes) {
                    // now send the pkt
                    printf("\nencoding number: %u\n", encodingNum++);
                    int retval = dagrouter_sim(encoding, numBytes+2, 0);
                    assert (retval < ARRAY_LENGTH(g_retvalCount));
                    g_retvalCount[retval]++;
                    printf("  processing retval: %u\n", retval);
                }
                else {
                    perror("reading the encoding");
                    exit(-1);
                }
            }
        }
        else {
            perror("file");
            exit(-1);
        }
    }

    freeBitString(&encoding);
    return 0;
}
