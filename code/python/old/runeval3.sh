#!/bin/sh

# $Id: runeval3.sh 438 2010-09-23 20:46:30Z nguyen59 $

RESULTDIR=resultdir
if [ -d $RESULTDIR ]; then
    echo "result directory $RESULTDIR already exists--make sure not to overwrite it"
    exit 1
fi

mkdir $RESULTDIR

# need to cover different ways different distributions install
export PYTHONPATH=${PYTHONPATH}:../../../usr/lib/python2.4/site-packages:../../../usr/lib/python2.5/site-packages:../../../usr/local/lib/python2.6/dist-packages

python eval3.py runeval \
    --headerLengthThreshold 60 -n 47620 --partialResultSize 1000 \
    --outputDir $RESULTDIR \
    --srcStartIdx ${1} --srcEndIdx ${2} \
    ../../../graphs/as-level/as-level-topology.txt
