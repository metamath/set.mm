#!/usr/bin/env python3

""" Creative Commons Zero v1.0 Universal

Permission to use, copy, modify, and/or distribute this software for any
purpose with or without fee is hereby granted.

This code is licensed under CC0 - https://creativecommons.org/publicdomain/zero/1.0/

Author: Gino Giotto

This script collects LaTeX definitions from a Metamath database.

Place the Metamath database in the same folder as this code.
Launch this script with $ python3 latex_collector.py database-name.mm output-name.tex.
E.g. $ python3 latex_collector.py set.mm list-set.tex to collect latex
definitions from the 'set.mm' database and show them in the 'list-set.tex' file.
"""

import argparse, re, sys

def collect(database, output):
    with database:
        text = database.read()
    
    pattern = r"latexdef\s+['\"](?P<token>\S+)['\"]\s+as(?P<tex>(?:\s*\n?\s*['\"].+['\"]\s*\+?)+);"
    matches = re.finditer(pattern, text)

    # Generation of the TeX file
    with output:
        output.write("\\documentclass[10pt]{article}\n")
        output.write("\\usepackage{longtable} % for the 'longtable' environment\n")
        output.write("\\usepackage{multicol} % for the 'multicols' environment\n")
        output.write("\\usepackage{amssymb} % load before phonetic\n")
        output.write("\\usepackage{phonetic} % for \\riota\n")
        output.write("\\usepackage{mathrsfs} % for \\mathscr\n")
        output.write("\\usepackage{mathtools} % loads package amsmath\n")
        output.write("\\usepackage{accents} % load after mathtools\n")
        output.write("\\usepackage[tmargin=1cm,bmargin=5mm,includefoot,footskip=5mm]{geometry}\n")
        output.write("\\newsavebox\ltmcbox\n")
        output.write("\\begin{document}\n\n")
        output.write("\\begin{multicols}{2}\n")
        output.write("\\setbox\\ltmcbox\\vbox{\\makeatletter\\col@number\\@ne\n")
        output.write("\\begin{longtable}{|c|c|}\n")
        output.write("\\hline\n")
        output.write("\\verb!ascii! & \\LaTeX\\ \\\\\n")
        output.write("\\hline\n")
        for match in matches:
            tex_part = (match.group("tex")).strip()
            token = match.group("token")
            trimmed = tex_part[1:-1].strip()
            final = re.sub(r"['\"]\s*\+\n\s*['\"]","", trimmed)
            output.write("\\verb!" + token + "! & $" + final + "$ \\\\\n")
        output.write("\\hline\n")
        output.write("\\end{longtable}\n")
        output.write("\\unskip\\unpenalty\\unpenalty}\\unvbox\\ltmcbox\n")
        output.write("\\end{multicols}\n")
        output.write("\\end{document}")
        
if __name__ == '__main__':
    parser = argparse.ArgumentParser(description='Collect LaTeX definitions from a Metamath database.')
    parser.add_argument(
        'database',
        nargs='?',
        type=argparse.FileType(mode='r',encoding='ascii'),
        default=sys.stdin,
        help="""The database (Metamath file) that contains the LaTeX definitions to collect, expressed using relative
          path (defaults to <stdin>)""")
    parser.add_argument(
        'output',
        nargs='?',
        type=argparse.FileType(mode='w',encoding='ascii'),
        default=sys.stdout,
        help="""The output TeX file containing the LaTeX definitions collected from the database, expressed using relative path (defaults to
          <stdout>).""")
    args = parser.parse_args()
    collect(args.database, args.output)
