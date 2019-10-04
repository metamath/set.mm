#!/usr/bin/env python3
# iset-match.py: Report where iset.mm statements differ from set.mm.
# Author: David A. Wheeler
# SPDX-License-Identifier: MIT

import os,re

# Generate list of statements in set.mm and iset.mm.
os.system("metamath 'read set.mm' 'set width 9999' 'show statement *' quit > ,set-mm-statements")
os.system("metamath 'read iset.mm' 'set width 9999' 'show statement *' quit > ,iset-mm-statements")

# The lines we want have this form:
# 70 mpd $p |- ( ph -> ch ) $= ... $.
# with a beginning number, label, $[aep], and statement.

useful = re.compile(r'[0-9]+ ([^ ]+) (\$[aep]) (.*)')

# Utility functions to clean up statements.

# https://stackoverflow.com/questions/3663450/python-remove-substring-only-at-the-end-of-string
def rchop(thestring, ending):
  if thestring.endswith(ending):
    return thestring[:-len(ending)]
  return thestring

def cleanup_expr(expr):
  t1 = rchop(expr, ' $= ... $.')
  t2 = rchop(t1, ' $.')
  return t2.strip()

setmm_statements = {}

# Read set.mm statement list
with open(',set-mm-statements', 'r') as setmm:
  for line in setmm:
    # print(line)
    res = useful.match(line)
    if res:
      label = res[1]
      expr = cleanup_expr(res[3])
      # print(label + ' ' + expr)
      setmm_statements[label] = expr

# print(setmm_statements)

# Read iset.mm statement list, report ones differing from set.mm.
with open(',iset-mm-statements', 'r') as isetmm:
  for line in isetmm:
    # print(line)
    res = useful.match(line)
    if res:
      label = res[1]
      label_type = res[2]
      expr = cleanup_expr(res[3])
      # print(label + ' ' + expr)
      if label in setmm_statements and setmm_statements[label] != expr:
        print('{} {}: {} DIFFERENT_FROM {}'.format(
          label, label_type, setmm_statements[label], expr))
