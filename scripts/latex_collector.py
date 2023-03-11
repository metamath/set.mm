#!/usr/bin/env python3

# Creative Commons Zero v1.0 Universal
#
# Permission to use, copy, modify, and/or distribute this software for any
# purpose with or without fee is hereby granted.
#
# This code is licensed under CC0 - https://creativecommons.org/publicdomain/zero/1.0/
#
# Author: Gino Giotto

# Place the Metamath database in the same folder of this code and call the function 'collect()'
# with the name of the file as argument. E.g. collect('set.mm') for collecting latex
# definitions from the set.mm database.

import re, sys
def collect(filename):
    with open(filename, 'r') as file:
        text = file.read()
    
    pattern = r"latexdef\s+['\"](?P<token>\S+)['\"]\s+as(?P<tex>(?:\s*\n?\s*['\"].+['\"]\s*\+?)+);"
    matches = re.finditer(pattern, text)

    # Creation of the tex file
    with open("list.tex", "w") as fileID: # Output file
        fileID.write("\\documentclass{article}\n")
        fileID.write("\\usepackage{longtable} % for the 'longtable' environment\n")
        fileID.write("\\usepackage{phonetic} % for \\riota\n")
        fileID.write("\\usepackage{mathrsfs} % for \\mathscr\n")
        fileID.write("\\usepackage{amssymb}\n")
        fileID.write("\\usepackage{mathtools} % loads package amsmath\n")
        fileID.write("\\begin{document}\n")
        fileID.write("\n")
        fileID.write("\\begin{longtable}{|c|c|}\n")
        fileID.write("\\hline\n")
        fileID.write("\\verb!ascii! & \\LaTeX\\ \\\\\n")
        fileID.write("\\hline\n")
        for match in matches:
            tex_part = (match.group("tex")).strip()
            token = match.group("token")
            trimmed = tex_part[1:-1].strip()
            final = re.sub(r"['\"]\s*\+\n\s*['\"]","", trimmed)
            fileID.write("\\verb!" + token + "! & $" + final + "$ \\\\\n")
        fileID.write("\\hline\n")
        fileID.write("\\end{longtable}\n")
        fileID.write("\n")
        fileID.write("\\end{document}")
        
if __name__ == '__main__':
    collect(sys.argv[1])
    
