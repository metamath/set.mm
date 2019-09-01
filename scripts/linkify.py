#!/bin/python
# linkify - convert <A HREF="NAME.html">NAME</A> into ~ NAME .
# Reads from stdin, writes to stdout

# Copyright 2018, David A. Wheeler
# SPDX-License-Identifier: MIT

# Per "Metamath: A Computer Language for Pure Mathematics" by Norman Megill,
# section 4.1.1, "A label token consists of any combination of
# letters, digits, and the characters hyphen, underscore, and period.
# In extended regular expression syntax this is "[A-Za-z0-9_\.\-]+"

# This is a rough translation; must sometimes hand-fix results.

# Here's a simple sample use:
# python scripts/linkify.py < mmset.raw.html > ,linkified
# diff -u mmset.raw.html ,linkified # Okay?
# mv ,linkified mmset.raw.html # Accept changes

from __future__ import print_function

import sys, re

# This searches for A HREF references
# re_href = re.compile(r's/ *<A\s+HREF="([A-Za-z0-9_\.\-]+)\.html">\1<\/A> *')
re_href = re.compile(r' *<A\s+HREF="([A-Za-z0-9_\.\-]+)\.html">\1<\/A> *')

def replace_href(m):
    inner = m.group(1) # The text to change
    return ' ~ {} '.format(inner)

# Read in entire file.  Not efficient, but easy to manage.
source = sys.stdin.read()
result = re.sub(re_href, replace_href, source)

# Remove leading space followed by ~ (not needed)
result = re.sub(r'^ \~ ', '~ ', result, flags=re.MULTILINE)

# Remove trailing whitespace on lines
result = re.sub(r' *$', '', result, flags=re.MULTILINE)

# Print final result
print(result)
