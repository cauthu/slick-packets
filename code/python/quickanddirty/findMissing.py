#!/usr/bin/python

import sys
import os
import re

Id = '$Id$'

if __name__ == '__main__':
    found = set()
    pattern = re.compile('partialResult_([0-9]+)_([0-9]+)')
    for dirpath in sys.argv[1:]:
        filenames = os.listdir(dirpath)
        for filename in filenames:
            match = re.match(pattern, filename)
            assert match != None
            # both "start" and "end" are inclusive
            start = int(match.group(1))
            end = int(match.group(2))
            found.update(range(start, end+1))
            pass
        pass

    all = set(range(0, 33508))

    missing = sorted(list(all.difference(found)))

    missingRanges = []

    i = 0
    while i < (len(missing)):
        start = missing[i]
        j = i + 1
        while j < len(missing):
            if missing[j] == (start + j - i):
                j += 1
                pass
            else:
                break
            pass
        end = missing[j - 1]
        missingRanges.append((start, end))
        i = j
        pass

    print missingRanges

    print 'total:', sum(map(lambda (start, end): end - start + 1, missingRanges))
    pass
