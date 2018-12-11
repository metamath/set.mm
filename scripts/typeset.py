#!/bin/python
# Process a file's `...` instructions using an mmfile's typographical commands
# Reads from stdin and sends to stdout.
# Use the "--help" option to see all the options.

# Copyright 2018, David A. Wheeler
# SPDX-License-Identifier: MIT

from __future__ import print_function

import sys
import re
import fileinput
import argparse

# TODO: Currently each `...` must not cross lines.
# TODO: Currently this doesn't handle 'no space if followed by punctuation'.

# Apply typographical definitions in MMFILE which look like this:
# htmldef "(" as "<IMG SRC='lp.gif' WIDTH=5 HEIGHT=19 ALT=' (' TITLE='('>";

# We read in the typographical instructions using a simple
# recursive descent parser, then translate what is in `...`.

# Default options
required_start = 'althtmldef '
mmfile = 'set.mm'

# We read typo definitions from typo_file.
typo_file = None
# "remains" is what's left to read on this line from typo_file
remains = ''

# This is the set of definitions we read from typo_file.
# Each key can be in `...`; the corresponding values are their translations.
typo_definition = {}

def read_fill_line():
    '''
    Clear out leading space, and if current line is empty, read next line
    from typo_file into "remains". Returns '' when at end of file.
    '''
    global remains
    remains = remains.lstrip()
    if remains == '':
        remains = typo_file.readline()
        if remains == '': return # File done
        read_fill_line() # Recurse until we find something

def read_comment():
    '''Skip through a /* ... */ comment'''
    global remains
    while '*/' not in remains:
        remains = ''
        read_fill_line()
    comment, junk, remains = remains.partition('*/')

def read_required(value):
    '''Read a required symbol; error out if it is not there'''
    global remains
    read_fill_line()
    if not remains.startswith(value):
        raise 0
    remains = remains[len(value):]
    read_fill_line()

def read_string():
    '''Read a typograhical string, which may continue using +'''
    global remains
    read_fill_line()
    if remains == '':
        return result # EOF
    elif remains[0] == '"' or remains[0] == "'":
        result, junk, remains = remains[1:].partition(remains[0])
        read_fill_line()
        # Recurse if we have +
        if remains and remains[0] == '+':
            read_required('+')
            return result + read_string()
        return result
    elif remains.startswith('/*'):
        # This presumes /*..*/ comments stay on one line
        comment, junk, remains = remains.partition('*/')
        return read_string()
    else:
        raise 0 # BOGUS

def read_definition():
    '''Read in a definition from typo_file given remains'''
    symbol = read_string()
    read_required('as')
    result = read_string()
    read_required(';')
    typo_definition[symbol] = result # Set definition in typo_definition.

def read_definitions():
    '''Read all definitions from typo_file'''
    global typo_file
    global remains
    typo_file = open(mmfile)
    while True:
        read_fill_line()
        if remains == '': break # We have reached end of file.
        stripped = remains.lstrip()
        if stripped.startswith('/*'): # Skip comments
            if '*/' in stripped:
                comment, junk, remains = remains.partition('*/')
            else:
                read_comment()
        if stripped.startswith(required_start): # Found our definition?
            remains = stripped[len(required_start):]
            read_definition()
        else:
            remains = '' # clear out line so we'll read next one

# This searches for backquoted text in a line.
backquoted = re.compile(r'(^| )` +(([^`]|``)*) `($| )')

def replace_typographically(m):
    '''
    Given a match item, return string; each word replaced using typo_definition
    '''
    inner = m.group(2) # The text to change
    translated_list = list(map(lambda i: typo_definition[i], inner.split()))
    translation = ' '.join(translated_list)
    return ' ' + translation + ' '

# Set up option handling
my_parser = argparse.ArgumentParser()
my_parser.add_argument('--html', help='Use older HTML format',
    action="store_true")
my_parser.add_argument('--althtml', help='Use ALTHTML format (default)',
    action="store_true")
my_parser.add_argument('--latex', help='Use LaTex format',
    action="store_true")
my_parser.add_argument('--mmfile', help='Use this mmfile (default set.mm)')
args = my_parser.parse_args()

# Handle command-line options
if args.html:
    required_start = 'htmldef '
if args.althtml:
    required_start = 'althtmldef '
if args.latex:
    required_start = 'latexdef '
if args.mmfile:
    mmfile = args.mmfile

# Read in the typographic definitions.
read_definitions()

# print(typo_definition)

# Now translate stdin using those definitions.

for line in sys.stdin:
    s = backquoted.search(line)
    new_line = re.sub(backquoted, replace_typographically, line)
    print(new_line)
