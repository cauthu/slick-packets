#!/bin/sh

# $Id: runevalStretch.sh 619 2010-11-04 00:28:30Z nguyen59 $

# need to cover different ways different distributions install
export PYTHONPATH=${PYTHONPATH}:../../../usr/lib/python2.4/site-packages:../../../usr/lib/python2.5/site-packages:../../../usr/local/lib/python2.6/dist-packages

python evalStretchVsTime.py runeval \
    --timeOfFailure 0 --processingDelay 0 --passThruDelay 0 -s ${3} -l 328 -d 161 \
    --srcSeed 1822909331 --linkSeed 3957622909 --dstSeed 3034726054 \
    --srcStartIdx ${1} --srcEndIdx ${2} \
    ../../../graphs/rocketfuel/3257/latencies.intra > output_${1}_${2} 2>&1

