/* this program acts as a client. it reads from input filenames the
 * encodings, one by one, and sends them, one by one, to the specified
 * router (IP:port).
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
#include "utils.h"
#include "bitstring.h"

static const char rcsid[] =
    "$Id$";

/***************************************************/
void usageAndExit(const char* prog)
{
    printf("\n"
           "Usage: %s -r ROUTER -t|-b FILE\n"
           "\n"
           " Run a DAG client to send packets to a router. The sent packets will contain\n"
           " encodings that are contained in the FILE argument. For each encoding, will\n"
           " generate and send one packet to the specified router.\n"
           "\n"
           " -r ROUTER: where ROUTER is IP:port.\n"
           "\n"
           " -t: the FILE is in text format.\n"
           "\n"
           " -b: the FILE is in binary format.\n"
           "\n"
           " FILE: the file, in either text or binary format, containing any number\n"
           " of encodings.\n",
           prog);
    exit(0);
    return;
}

int main(int argc, char* argv[])
{
    char *straddr = NULL; /* dont free */
    char *strport = NULL; /* dont free */
    char *savedptr = NULL; /* dont free */
    int port = -1;
    struct sockaddr_in router_sockaddr_in;
    int router_sock = -1;
    // the input encodings, whether they are text or binary
    int binary = 0;
    int text = 0;
    bitstring encoding = NULL;

    int c;

    // disable stdout buffering
    setvbuf(stdout, NULL, _IONBF, 0);

    while ((c = getopt(argc, argv, "r:bt")) != -1) {
        switch (c) {
        case 'r':
            straddr = strtok_r(optarg, ":", &savedptr);
            assert (straddr);
            assert (1 == inet_pton(AF_INET, straddr,
                                   &(router_sockaddr_in.sin_addr)));
            strport = strtok_r(NULL, ":", &savedptr);
            assert (strport);
            port = strtol(strport, (char **) NULL, 10);
            if (port < 0 || port > 65535) {
                printf("bad port %d\n", port);
                abort();
            }
            router_sockaddr_in.sin_port = htons(port);
            router_sockaddr_in.sin_family = AF_INET;
            bzero(&(router_sockaddr_in.sin_zero),
                  sizeof(router_sockaddr_in.sin_zero));
            router_sock = socket(AF_INET, SOCK_DGRAM, 0);
            assert (router_sock != -1);
            break;
        case 'b':
            binary = 1;
            break;
        case 't':
            text = 1;
            break;
        default:
            usageAndExit(argv[0]);
        }
    }

    if (!(optind < argc)) {
        usageAndExit(argv[0]);
    }

    if (!(binary ^ text)) {
        usageAndExit(argv[0]);
    }

    uint64_t numSentPackets = 0;

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

                // now send the pkt
                sendto(router_sock, encoding, numBytes+2, 0,
                       (struct sockaddr *)&(router_sockaddr_in),
                       sizeof(struct sockaddr));

                numSentPackets += 1;
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
                    sendto(router_sock, encoding, numBytes+2, 0,
                           (struct sockaddr *)&(router_sockaddr_in),
                           sizeof(struct sockaddr));

                    numSentPackets += 1;
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

    printf("numSentPackets: %llu\n", numSentPackets);
    freeBitString(&encoding);
    return 0;
}
