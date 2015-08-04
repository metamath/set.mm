#!/usr/bin/env python3

import sys

f1, f2 = open(sys.argv[1]), open(sys.argv[2])

toks = set()

for line in f1.readlines():
    toks.update({tok for tok in line.split() if tok.startswith('$')})

for line in f2.readlines():
    toks.difference_update({tok for tok in line.split() if tok.startswith('$')})

for t in toks:
    print('let v', t, '= et')
