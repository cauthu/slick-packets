CXX = g++
CXXFLAGS = -O0 -g -Wall

INCLUDE= \

LDFLAGS= \
	-lboost_system \

evalStretchVsTime_sample_link_first: evalStretchVsTime_sample_link_first.cpp
	$(CXX) $(CXXFLAGS) $(INCLUDE) $(LDFLAGS) -o $@ $<

all: evalStretchVsTime_sample_link_first

.PHONY: clean

clean:
	-rm -f evalStretchVsTime_sample_link_first *.o *~ core TAGS
