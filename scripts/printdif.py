#!/usr/bin/env python3

import sys

filea = open(sys.argv[1])
lines = set(filea.readlines())
filea.close()

fileb = open(sys.argv[2])
rmlines = set(fileb.readlines())
lines.difference_update(rmlines)
fileb.close()

for l in lines:
    print('let var', l.strip(), '= et')
