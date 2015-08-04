#!/usr/bin/env python3

import re
import sys
import fileinput

i = 1
for l in fileinput.input():
	if (i%1000) == 0: print(i,file=sys.stderr)
	list(map(print,re.findall(r'\$\d+',l)))
	i+=1

