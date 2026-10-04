#!/usr/bin/env python3
"""Generate a LaTeX symbol table from Metamath typesetting definitions.

Pair latexdef and althtmldef entries by token. Convert supported HTML
formatting and Unicode characters to ASCII TeX commands.

Usage: python3 latex_collector_fixed.py database.mm output.tex

Omitted paths or '-' mean stdin/stdout. Metamath includes are not expanded.
Compile the generated document with LuaLaTeX or XeLaTeX.

CC0 1.0 Universal: https://creativecommons.org/publicdomain/zero/1.0/
Based on the original script by Gino Giotto.
"""

import argparse
import re
import sys
from pathlib import Path
from html.parser import HTMLParser
from collections.abc import Iterator, Sequence


PREAMBLE = r"""\documentclass[10pt]{article}
\usepackage{longtable}
\usepackage{amssymb} % Load this {amssymb} before {phonetic}.
\usepackage{phonetic} % for \riota
\usepackage{mathrsfs} % for \mathscr
\usepackage{mathtools} % This loads the package {amsmath}.
\usepackage{upgreek}
\usepackage[no-math]{fontspec}
\newfontfamily\unicodefont[
  AutoFakeBold=1.5,
  AutoFakeSlant=0.2
]{STIXTwoMath-Regular.otf}
\usepackage[vmargin=1cm,hmargin=1cm,includefoot]{geometry}
\newsavebox{\ltmcbox}
\begin{document}
\begin{longtable}{|c|c|c|}
\hline
Token & unicode & \LaTeX \\
\hline
"""

POSTAMBLE = r"""\hline
\end{longtable}
\end{document}
"""

# Quotes are escaped by doubling them; backslashes are literal.
STRING = r'''(?:"(?:[^"\r\n]|"")*"|'(?:[^'\r\n]|'')*')'''
VALUE = rf"{STRING}(?:\s*\+\s*{STRING})*"
DEFINITION = re.compile(
    rf"(?:latexdef|althtmldef)\s+({VALUE})\s+as\s+({VALUE})")
LEXEME = re.compile(
    rf'''{STRING}|/\*.*?(?:\*/|\Z)|[+;]|[^\s'"+;/]+|\S''', re.DOTALL)
COMMENTS = re.compile(
    r"(?<!\S)\$\((?!\S)(.*?)(?:(?<!\S)(\$\))(?!\S)|\Z)", re.DOTALL)

ESCAPES = str.maketrans({
    "\\": r"\textbackslash{}", "{": r"\{", "}": r"\}",
    "&": r"\&", "%": r"\%", "$": r"\$", "#": r"\#", "_": r"\_",
    "~": r"\textasciitilde{}", "^": r"\textasciicircum{}",
    "\u00a0": "~",  # HTML nonbreaking space
})


class HTMLToTeX(HTMLParser):
    """Convert supported HTML tags and text to ASCII TeX.

    Attributes on span and font are ignored. Other attributes and
    unsupported tags are rejected. Tag nesting is checked, but this
    class does not perform complete HTML validation.
    """

    tags = {"sub": r"\textsubscript{", "sup": r"\textsuperscript{", "span": r"{", "font": r"{",
            "small": r"{\small ", "u": r"\underline{", "b": r"\textbf{", "i": r"\textit{"}

    def __init__(self):
        """Initialize the HTML parser and conversion state."""
        super().__init__(convert_charrefs=True)
        self.parts = []
        self.stack = []

    def handle_starttag(self, tag, attrs):
        """Validate an opening tag, emit its TeX, and record its nesting."""
        if tag not in self.tags or (attrs and tag not in {"span", "font"}):
            raise ValueError(f"unsupported HTML tag or attributes: <{tag}>")
        self.parts.append(self.tags[tag])
        self.stack.append(tag)

    def handle_endtag(self, tag):
        """Check the closing tag and emit the corresponding TeX brace."""
        if not self.stack or self.stack.pop() != tag:
            raise ValueError(f"mismatched HTML closing tag: </{tag}>")
        self.parts.append("}")

    def handle_data(self, data):
        """Encode text as ASCII TeX, escaping special characters."""
        for char in data:
            code = ord(char)
            if code in ESCAPES:
                self.parts.append(ESCAPES[code])
            elif code > 127:
                self.parts.append(rf'\symbol{{"{code:X}}}')
            else:
                self.parts.append(char)


def html_to_tex(fragment: str) -> str:
    """Convert an HTML fragment to TeX, checking supported tags and nesting."""
    parser = HTMLToTeX()
    parser.feed(fragment)
    parser.close()
    if parser.stack:
        raise ValueError("unclosed HTML tag")
    return "".join(parser.parts)


def decode(value: str) -> str:
    """Join quoted fragments and decode doubled quotation marks."""
    return "".join(s[1:-1].replace(s[0] * 2, s[0])
                   for s in re.findall(STRING, value))


def definitions(text: str, kind: str = "latexdef") -> Iterator[tuple[str, str]]:
    """Yield (token, value) pairs for kind from Metamath $t comments."""
    seen = set()
    for comment in COMMENTS.finditer(text):
        if comment[2] is None:
            raise ValueError("unterminated Metamath comment")
        body = comment[1].lstrip()
        if not re.match(r"\$t(?=\s)", body):
            continue
        statement = []
        for item in LEXEME.findall(body[2:]):
            if item.startswith("/*"):
                if not item.endswith("*/"):
                    raise ValueError("unterminated typesetting comment")
                continue
            if item in ("'", '"'):
                raise ValueError(
                    "unterminated quote or newline inside a string")
            if item != ";":
                statement.append(item)
                continue
            if statement and statement[0] == kind:
                match = DEFINITION.fullmatch(" ".join(statement))
                if match is None:
                    raise ValueError(f"malformed {kind} statement")
                token, value = map(decode, match.groups())
                if not token or any(c.isspace() for c in token):
                    raise ValueError(
                        "empty token or whitespace inside a token")
                if token in seen:
                    raise ValueError(
                        f"duplicate {kind} definition for {token!r}")
                seen.add(token)
                yield token, value
            statement = []
        if statement:
            raise ValueError("typesetting statement is missing its final ';'")


def collect(text: str) -> str:
    """Build the complete LaTeX document without performing I/O."""
    unicode_defs = dict(definitions(text, "althtmldef"))
    rows = []
    for token, tex in definitions(text):
        unicode_value = html_to_tex(unicode_defs.get(token, ""))
        rows.append(
            rf"\texttt{{{token.translate(ESCAPES)}}}"
            rf" & {{\unicodefont {unicode_value}}}"
            rf" & \({tex}\) \\" + "\n"
        )
    if not rows:
        raise ValueError("no latexdef definitions found in a $t comment")
    return PREAMBLE + "".join(rows) + POSTAMBLE


def main(argv: Sequence[str] | None = None) -> None:
    """Parse command-line arguments, write the document, and report errors."""
    parser = argparse.ArgumentParser(
        description="Collect Metamath LaTeX definitions.")
    parser.add_argument("database", nargs="?", default="-",
                        help="input path (default: stdin)")
    parser.add_argument("output", nargs="?", default="-",
                        help="output path (default: stdout)")
    args = parser.parse_args(argv)
    try:
        if args.database != "-" and args.output != "-":
            if Path(args.output).exists() and Path(args.database).samefile(args.output):
                raise ValueError("input and output identify the same file")
        text = (sys.stdin.read() if args.database == "-"
                else Path(args.database).read_text(encoding="ascii"))
        document = collect(text)
        document.encode("ascii")  # Validate before writing anything.
        if args.output == "-":
            sys.stdout.write(document)
        else:
            Path(args.output).write_text(document, encoding="ascii")
    except (OSError, ValueError) as error:
        parser.exit(1, f"{parser.prog}: {error}\n")


if __name__ == "__main__":
    main()
