/* $Id$ */

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
#include "encoding.h"
#include "encoding3.h"
#include "encoding2.h"

typedef struct {
    int sock;
    struct sockaddr_in sockaddr_in;
} neighbor_t;

// linkId is used as index, and value is whether the link is up or
// down.
static bool* g_linkId2UpStatus = NULL;
static neighbor_t* g_neighbors = NULL;
static unsigned int g_numNeighbors = 0;

static const encoding_process_func_t encodingProcessFunctions[] = {
    NULL,
    NULL,
    processEncoding2,
    processEncoding3,
};

/***************************************************/

/*
 * The "header" is actually the data portion of the UDP packet.
 *
 * The header contains 2 bytes of meta-data, followed by the DAG
 * encoding:
 *
 *   bytes[0]: How many total bytes is the ENCODING? Thus the size of
 *   the whole data portion should be equal to this value + 2.
 *
 *   4 most significant bits of bytes[1]: How many bits are IN THE
 *   LAST byte of the encoding? This value should thus be in range
 *   [1,8].
 *
 *   4 least significant bits of bytes[1]: The type of the
 *   encoding. Currently we have two encoding types, 2 and 3.
 *
 *   bytes[2]: The start of the encoding.
 *
 * The router computes the length in BITS of the encoding, then sends:
 *   the encoding,
 *   the length in bits of the encoding,
 *   the current status (up/down) of all the links.
 *
 * to the encoding processing function for the encoding type.
 *
 * All encoding processing functions should return 0 for success,
 * non-zero for any error.
 *
 * If error, the router should drop the packet.
 *
 * Otherwise, the processing function returns one of three actions for
 * the packet: drop, deliver, or forward.
 *
 * For drop and deliver, the router does not need to do anything to
 * the header.
 *
 * If forward, the router should:
 *   - Update the meta-data if the encoding has changed in length.
 *   - Forward to link ID returned by the processing function.
 *
 * Done.
 */

int loop(int sock)
{
    static const int DATA_SIZE = 512;

    while (1) {
        unsigned char recv_data[DATA_SIZE];
        int bytes_read = recvfrom(sock, recv_data, DATA_SIZE, 0, NULL, NULL);

        printf("\n--------------------"
               "\nrecv pkt of %d bytes\n", bytes_read);

        // the encoding should be preceded by 2 bytes of meta-info
        // that is common to all encoding types.

        /* at least 2 bytes of meta-info */
        if (bytes_read < 2) {
            // drop packet
            printf("  not at least 2 bytes --> drop\n");
            continue;
        }

        // how many bytes? max of 255
        unsigned char numBytes = recv_data[0];
        // how many bits IN the last byte? must be in range (1,8]
        // this is the 4 most significant bits of the 2nd byte
        unsigned char numBitsInLastByte = (recv_data[1] >> 4) & 0xf;
        // the 4 least significant bits of the 2nd byte
        unsigned char type = (recv_data[1]) & 0xf;

        printf("  encoding: type %d\n"
               "            %d bytes,\n"
               "            %d bits in last byte\n",
               type, numBytes, numBitsInLastByte);

        if (numBitsInLastByte < 1 || numBitsInLastByte > 8) {
            // drop packet
            printf("  numBitsInLastByte < 1 || numBitsInLastByte > 8 --> drop\n");
            continue;
        }
        if ((2 + numBytes) != bytes_read) {
            // drop packet
            printf("  (2 + numBytes) != bytes_read --> drop\n");
            continue;
        }
        if (type >= ARRAY_LENGTH(encodingProcessFunctions)) {
            // drop packet
            printf("  type >= %d --> drop", ARRAY_LENGTH(encodingProcessFunctions));
            continue;
        }

        encoding_process_func_t processFunc = encodingProcessFunctions[type];

        if (processFunc == NULL) {
            // drop packet
            continue;
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
            printf("  error processing encoding --> drop\n");
            continue;
        }
        else if (action_drop == action) {
            printf("  action_drop == action --> drop\n");
            continue;
        }
        else if (action_deliver == action) {
            // deliver packet
            printf("  action_deliver == action --> deliver\n");
            continue;
        }
        else if (action_forward == action) {
            // we are to forward the packet. the encoding has been updated
            // appropriately
            assert (newLengthInBits > 0);

            printf("  action_forward == action\n");
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

            printf("  forwarding out linkId %d\n", outLinkId);

            // forward out link outLinkId
            neighbor_t* neigborPtr = &(g_neighbors[outLinkId]);

            sendto(neigborPtr->sock, recv_data, numBytes+2, 0,
                   (struct sockaddr *)&(neigborPtr->sockaddr_in),
                   sizeof(struct sockaddr));
            continue;
        }
    }

    return 0;
}

/***************************************************/
int getNeighborsInfo(char* ipPorts[],
                     unsigned int numNeighbors,
                     unsigned int numDups)
{
    assert (numNeighbors > 0);

    g_numNeighbors = numDups ? numDups : numNeighbors;

    g_neighbors = (neighbor_t*)calloc(g_numNeighbors, sizeof(neighbor_t));
    assert (g_neighbors);

    for (int i = 0; i < g_numNeighbors; i++) {
        char *straddr = NULL;
        char *strport = NULL;
        char *savedptr = NULL;
        int port = -1;

        straddr = strtok_r(numDups ? ipPorts[0] : ipPorts[i], ":", &savedptr);
        assert (straddr);

        assert (1 == inet_pton(AF_INET, straddr,
                               &(g_neighbors[i].sockaddr_in.sin_addr)));

        strport = strtok_r(NULL, ":", &savedptr);
        if (NULL == strport) {
            printf("addr %s is missing port\n", straddr);
            abort();
        }
        port = strtol(strport, (char **) NULL, 10);

        if (port < 0 || port > 65535) {
            printf("bad port %d\n", port);
            abort();
        }
        //////
        straddr[strlen(straddr)] = ':';
        //////
        g_neighbors[i].sockaddr_in.sin_port = htons(port);

        g_neighbors[i].sockaddr_in.sin_family = AF_INET;
        bzero(&(g_neighbors[i].sockaddr_in.sin_zero),
              sizeof(g_neighbors[i].sockaddr_in.sin_zero));


        g_neighbors[i].sock = socket(AF_INET, SOCK_DGRAM, 0);
        assert (g_neighbors[i].sock != -1);
    }

    g_linkId2UpStatus = (bool*)calloc(g_numNeighbors, sizeof(bool));
    assert (g_linkId2UpStatus);

    // for now, make all links up by default
    for (int i = 0; i < g_numNeighbors; i++) {
        g_linkId2UpStatus[i] = true;
    }

    printf("All %d links are considered online.\n", g_numNeighbors);

    return 0;
}

/***************************************************/
void usageAndExit(const char* prog)
{
    printf("\n"
           "Usage: %s -p PORT NEIGHBOR [NEIGHBOR ...]\n"
           "\n"
           " Run a DAG router on the localhost.\n"
           "\n"
           " -p PORT: the port to listen on for incoming packets.\n"
           "\n"
           " -d NUMDUPS: use NUMDUPS duplicates of NEIGHBOR.\n"
           "\n"
           " NEIGHBOR: IP:port of a neighbor. The neighbors will have (link)\n"
           "           IDs starting from zero.\n"
           "\n",
           prog);
    exit(0);
    return;
}

/***************************************************/
int main(int argc, char *argv[])
{
    int port = -1;
    int numdups = 0;
    int c;

    // disable stdout buffering
    setvbuf(stdout, NULL, _IONBF, 0);

    while ((c = getopt(argc, argv, "p:d:")) != -1) {
        switch (c) {
        case 'p':
            port = strtol(optarg, (char **) NULL, 10);
            break;
        case 'd':
            numdups = strtol(optarg, (char **) NULL, 10);
            break;
        default:
            usageAndExit(argv[0]);
        }
    }

    if (port < 0 || port > 65535) {
        printf("bad port %d\n", port);
        usageAndExit(argv[0]);
    }

    if (optind >= argc) {
        printf("need at least one neighbor\n");
        usageAndExit(argv[0]);
    }

    if (getNeighborsInfo(argv+optind, argc-optind, numdups)) {
        printf("some errors in processing the neighbors list\n");
        usageAndExit(argv[0]);
    }

    int sock;
    struct sockaddr_in server_addr;

    if ((sock = socket(AF_INET, SOCK_DGRAM, 0)) == -1) {
        perror("Socket");
        exit(1);
    }

    server_addr.sin_family = AF_INET;
    server_addr.sin_port = htons(port);
    server_addr.sin_addr.s_addr = INADDR_ANY;
    bzero(&(server_addr.sin_zero), sizeof(server_addr.sin_zero));

    if (bind(sock,(struct sockaddr *)&server_addr,
             sizeof(struct sockaddr)) == -1)
    {
        perror("Bind");
        exit(1);
    }

    printf("\nWaiting for packets on port %d.\n", port);

    loop(sock);

    return 0;
}
