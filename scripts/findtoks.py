#!/usr/bin/env python3

import fileinput

toks = set()

for line in fileinput.input():
    toks.update({tok in line.split() if tok.startswith('$')})

for tok in toks:
    print('let v', tok, '= et')
