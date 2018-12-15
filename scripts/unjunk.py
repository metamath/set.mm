#!/bin/python
# Replace img references with `...` references
# Reads from stdin and sends to stdout.  By default the mmfile is "set.mm".
# Copyright 2018, David A. Wheeler
# SPDX-License-Identifier: MIT

# This is a rough translation; must sometimes hand-fix results.

# E.g., replace this:
# <IMG SRC='_ltbbr.gif' WIDTH=20 HEIGHT=19 ALT=' &lt;RR' TITLE='&lt;RR'>
# with this:
# ` <RR `

# Here's a simple test:
# python scripts/unjunk.py < mmcomplex.html > ,unjunked
# python scripts/typeset.py --html < ,unjunked > ,rejunked
# diff -u mmcomplex.html ,rejunked

from __future__ import print_function

import sys, re

# This searches for img references
re_img = re.compile(r'<IMG\s[^>]*\sALT=[\'"] *([^\' "]+) *[\'"][^>]*>')

# We temporarily replace function calls with this so we can handle them.
function_call_stub = 'FUNCTION_CALL_STUB_' + 'XYZZY'

def replace_img(m):
    inner = m.group(1) # The text to change
    inner = inner.strip()
    inner = inner.replace('&lt;', '<')
    inner = inner.replace('&gt;', '>')
    inner = inner.replace('&quot;', '"')
    inner = inner.replace('&apos;', "'")
    inner = inner.replace('&amp;', '&')
    inner = inner.replace('`', function_call_stub)
    return '` {} `'.format(inner)

# Read in entire file.  Not efficient, but easy to manage.
source = sys.stdin.read()
result = re.sub(re_img, replace_img, source)

# Patch up results that are followed by punctuation (imperfect)
result = result.replace(' `` ', ' ')
result = result.replace(' ` ` ', ' ')
result = result.replace(' `.', ' ` .')
result = result.replace(' `,', ' ` ,')
result = result.replace(' `;', ' ` ;')
result = result.replace(' `<', ' ` <')

# Weird special case: MPE Home image is translated. Fix it back.
mpe_gif = '''<IMG SRC="mm.gif"
      BORDER=0
      ALT="Metamath Proof Explorer Home"
      TITLE="Metamath Proof Explorer Home"
      HEIGHT=32 WIDTH=32 ALIGN=TOP STYLE="margin-bottom:0px">'''
result = result.replace('` Metamath Proof Explorer Home `', mpe_gif)

# Use real function call reference
result = result.replace(function_call_stub, '``')

# Remove trailing whitespace on lines
result = re.sub(r' *$', '', result, flags=re.MULTILINE)

# Print final result
print(result)
