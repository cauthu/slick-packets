# $Id: Makefile 593 2010-11-01 11:18:56Z nguyen59 $

CC=g++
CFLAGS=-c -Wall
LDFLAGS=-g
SOURCES=dagrouter.cc encoding2.cc encoding3.cc bitstring.cc
OBJECTS=$(SOURCES:.cpp=.o)
EXECUTABLE=dagrouter

all: $(SOURCES) $(EXECUTABLE)

$(EXECUTABLE): $(OBJECTS) 
	$(CC) $(LDFLAGS) $(OBJECTS) -o $@

.cpp.o:
	$(CC) $(CFLAGS) $< -o $@

client: bitstring.o client.cc
	$(CC) $(LDFLAGS) bitstring.o client.cc -o client

clean:
	rm -f *.o ${EXECUTABLE} client
