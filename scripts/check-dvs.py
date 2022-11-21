#!/usr/bin/env python3
# Copyright 2021 Jerry James <loganjerry@gmail.com>
# SPDX-License-Identifier: MIT
#
# This file is released under the terms of the MIT license, as follows.
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to
# deal in the Software without restriction, including without limitation the
# rights to use, copy, modify, merge, publish, distribute, sublicense, and/or
# sell copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in
# all copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.  IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
# FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS
# IN THE SOFTWARE.

"""
Check for unnecessary dv conditions in a metamath file.

In particular, this program checks for variables that are named in a $d
statement, but are not named in any theorem or proof in the same scope.
The input files are assumed to be syntactically correct Metamath files;
i.e., this program does not check for syntax errors and may behave badly
if a syntactically incorrect file is given.

The output is a (possibly empty) list of lines of the following form:

Found [variable] at [file]:[line]:[column]
"""

from __future__ import annotations
from collections.abc import Hashable
from enum import auto, Enum
from typing import Any, Callable, Dict, List, Optional, Set, TextIO, Union
import string
import sys

class TokenType(Enum):
    """Type of tokens in a metamath file."""
    BOF = auto()
    EOF = auto()
    DA = auto()
    DC = auto()
    DD = auto()
    DE = auto()
    DF = auto()
    DP = auto()
    DV = auto()
    DDOT = auto()
    DEQ = auto()
    DLBRACE = auto()
    DRBRACE = auto()
    DLBRACK = auto()
    DRBRACK = auto()
    SYMBOL = auto()

token_map: Dict[str, TokenType] = {
    '$a': TokenType.DA,
    '$c': TokenType.DC,
    '$d': TokenType.DD,
    '$e': TokenType.DE,
    '$f': TokenType.DF,
    '$p': TokenType.DP,
    '$v': TokenType.DV,
    '$.': TokenType.DDOT,
    '$=': TokenType.DEQ,
    '${': TokenType.DLBRACE,
    '$}': TokenType.DRBRACE,
    '$[': TokenType.DLBRACK,
    '$]': TokenType.DRBRACK
}

class MetamathToken(Hashable):
    """One token in a metamath file."""

    __slots__ = ["column", "fil", "line", "typ", "text"]

    def __init__(self, typ: TokenType, fil: str, line: int, column: int,
                 text: str) -> None:
        """Create a metamath token.

        :param TokenType typ: the type of this token
        :param str fil: the file containing the token
        :param int line: the line number containing the token
        :param int column: the column number of the first character of the token
        :param str text: the text of the token
        """
        self.typ = typ
        self.fil = fil
        self.line = line
        self.column = column
        self.text = text

    def __hash__(self) -> int:
        """Compute a hash value for this token.

        The hash value is based solely on the text of the token, so that tokens
        can be added to containers and searched for by name.

        :return: the hash value of this token
        :rettype: int
        """
        return hash(self.text)

    def __eq__(self, other: Any) -> bool:
        """Compare two tokens for equality.

        Comparison is based solely on the text of the token, so that tokens can
        be added to containers and searched for by name.

        :return: True if the token is equal to the argument, otherwise False
        :rettype: bool
        """
        return self.text == str(other)

    def __str__(self) -> str:
        """Return a string representation of this token.

        :return: a string representation of this token
        :rettype: str
        """
        return self.text

class MetamathLexer:
    """Lexer for metamath files."""

    __slots__ = ["fil", "filename", "index", "line", "lineno", "proxy"]

    def __init__(self, filename: str) -> None:
        """
        Create a new metamath lexer to read from a given file.

        :param str filename: the name of the file to check
        """
        self.filename: str = filename
        self.fil: Optional[TextIO] = None
        self.line: str = ""
        self.lineno: int = 0
        self.index: int = 0
        self.proxy: Optional[MetamathLexer] = None

    def __enter__(self) -> MetamathLexer:
        self.fil = open(self.filename, 'r')
        self.get_line()
        return self

    def __exit__(self, exc_type: Any, exc_value: Any, traceback: Any) -> None:
        if self.proxy:
            self.proxy.__exit__(exc_type, exc_value, traceback)
            self.proxy = None
        if self.fil:
            self.fil.close()
            self.fil = None
        return None

    def get_line(self) -> bool:
        """Get another line from the metamath file.

        :return: True on success, False if no more lines are available
        :rtype: bool
        """
        line = self.fil.readline() if self.fil else None
        if not line:
            return False
        self.line = line
        self.lineno += 1
        self.index = 0
        return True

    def skip_spaces(self) -> bool:
        """Skip over spaces in the input.

        :return: True on success, False if no more lines are available
        :rtype: bool
        """
        length: int = len(self.line)
        while True:
            while (self.index < length and
                   self.line[self.index] in string.whitespace):
                self.index += 1
            if self.index < length:
                return True
            if not self.get_line():
                return False
            length = len(self.line)

    def skip_comment(self) -> bool:
        """Skip over comments in the input.

        :return: True on success, False if no more lines are available
        :rtype: bool
        """
        # We are looking at the $( that starts the comment, so skip it
        self.index += 2

        length: int = len(self.line)
        while True:
            while (self.index + 1 < length and
                   (self.line[self.index] != '$' or
                    self.line[self.index + 1] != ')')):
                self.index += 1
            if self.index + 1 < length:
                # We are looking at the $) that ends the comment, so skip it
                self.index += 2
                return True
            if not self.get_line():
                return False
            length = len(self.line)

    def skip_spaces_and_comments(self) -> bool:
        """Skip over spaces and comments in the input.

        :return: True on success, False if no more lines are available
        :rtype: bool
        """
        while True:
            if not self.skip_spaces():
                return False
            if (self.index + 1 >= len(self.line) or
                self.line[self.index] != '$' or
                self.line[self.index + 1] != '('):
                return True
            if not self.skip_comment():
                return False

    def _token(self) -> MetamathToken:
        """Get the next token from the underlying file without file inclusion.

        :return: the next token as a string, or None if the end of the file has
            been reached
        :rtype: Optional[str]
        """
        if self.skip_spaces_and_comments():
            for i in range(self.index, len(self.line)):
                if self.line[i] in string.whitespace:
                    break
            sym = self.line[self.index:i]
            typ = token_map.get(sym, TokenType.SYMBOL)
        else:
            sym = ""
            typ = TokenType.EOF
            i = -1
        token = MetamathToken(typ, self.filename, self.lineno, self.index, sym)
        # We may as well skip over any trailing whitespace, hence the +1
        self.index = i + 1
        return token

    def get_token(self) -> MetamathToken:
        """Get the next token from the underlying file.

        :return: the next token as a string, or None if the end of the file has
            been reached
        :rtype: Optional[MetamathToken]
        """
        while True:
            # Get a token from the proxy if we are including another file
            if self.proxy:
                token = self.proxy.get_token()
                if token.typ != TokenType.EOF:
                    return token
                self.proxy.__exit__(None, None, None)
                self.proxy = None

            # Get a token from the underlying file
            token = self._token()
            if token.typ != TokenType.DLBRACK:
                return token

            filename_token = self._token()
            end_token = self._token()
            if not filename_token or filename_token.typ != TokenType.SYMBOL or \
               not end_token or end_token.typ != TokenType.DRBRACK:
                raise NameError(f"Bad file inclusion on line {self.line} of {self.filename}")
            self.proxy = MetamathLexer(filename_token.text)
            self.proxy.__enter__()

class Scope:
    """A metamath scope."""

    __slots__ = ["d_vars", "e_vars", "f_vars", "proof_vars"]

    def __init__(self) -> None:
        """Initialize a metamath scope."""
        self.proof_vars: Dict[str, str] = dict()
        self.f_vars: Set[str] = set()
        self.e_vars: Set[str] = set()
        self.d_vars: Set[MetamathToken] = set()

    def add_f_decl(self, proof_name: str, theorem_name: str) -> None:
        """Add a $f declaration to this scope.

        :param str proof_name: the name used in proofs, e.g., "vx"
        :param str theorem_name: the named used in theorems, e.g., "x"
        """
        self.proof_vars[proof_name] = theorem_name
        self.f_vars.add(theorem_name)

    def add_d_variable(self, var: MetamathToken) -> None:
        """Add a variable to the set of variables named in $d statements.
        If the variable was already used in an $e statement, skip it.

        :param MetamathToken var: the name of the variable
        """
        self.d_vars.add(var)

    def add_e_variable(self, var: MetamathToken) -> None:
        """Add a variable to the set of variables named in $e statements.

        :param MetamathToken var: the name of the variable
        """
        self.e_vars.add(var)

    def remove_theorem_var(self, var: str) -> None:
        """Remove a variable seen in a theorem from the $d variables in this
        scope.

        :param str var: the name of the variable
        """
        self.d_vars.discard(var) # type: ignore

    def remove_proof_var(self, var: str) -> None:
        """Remove a variable seen in a proof from the $d variables in this
        scope.

        :param str var: the name of the variable
        """
        v = self.proof_vars.get(var, None)
        if v:
            self.d_vars.discard(v) # type: ignore

    def find_proof_var(self, var: str) -> Optional[str]:
        """Map a variable name in a proof to a theorem variable name.

        :param str var: the name of the variable in a proof
        :return: the mapped name of the variable, or None if no mapping exists
        :rtype: Optional[str]
        """
        return self.proof_vars.get(var, None)

    def report_d_vars(self) -> None:
        """Report on any $d variables that have not been seen."""
        for var in self.d_vars:
            print(f"Found {var.text} at {var.fil}:{var.line}:{var.column}")

class Scopes:
    """All active metamath scopes, including the top-level scope."""

    __slots__ = ["scopes"]

    def __init__(self) -> None:
        """Initialize a stack of metamath file scopes."""
        self.scopes: List[Scope] = [Scope()]

    def push_scope(self) -> None:
        """Add a new scope to the stack of scopes."""
        self.scopes.append(Scope())

    def pop_scope(self) -> None:
        """Remove a scope from the stack of scopes."""
        scope = self.scopes.pop()
        scope.report_d_vars()

    def add_f_decl(self, proof_name: str, theorem_name: str) -> None:
        """Add a $f declaration to this scope.

        :param str proof_name: the name used in proofs, e.g., "vx"
        :param str theorem_name: the named used in theorems, e.g., "x"
        """
        self.scopes[-1].add_f_decl(proof_name, theorem_name)

    def add_d_variable(self, var: MetamathToken) -> None:
        """Add a variable to the set of variables named in $d statements.

        :param MetamathToken var: the name of the variable
        """
        for scope in self.scopes:
            if var in scope.e_vars:
                return
        self.scopes[-1].add_d_variable(var)

    def add_e_variable(self, var: MetamathToken) -> None:
        """Add a variable to the set of variables named in $e statements.

        :param MetamathToken var: the name of the variable
        """
        self.scopes[-1].add_e_variable(var)

    def remove_theorem_var(self, var: str) -> None:
        """Remove a variable seen in a theorem from the $d variables in all
        scopes.

        :param str var: the name of the variable
        """
        for scope in self.scopes:
            scope.remove_theorem_var(var)

    def remove_proof_var(self, var: str) -> None:
        """Remove a variable seen in a proof from the $d variables in all
        scopes.

        :param str var: the name of the variable
        """
        theorem_var = None
        for scope in self.scopes:
            theorem_var = scope.find_proof_var(var)
            if theorem_var:
                self.remove_theorem_var(theorem_var)
                break

class DVChecker:
    """Check a metamath file for unnecessary dv conditions."""

    __slots__ = ["action", "last", "scopes", "token"]

    def __init__(self) -> None:
        """Initialize a metamath file dv checker."""
        self.scopes: Scopes = Scopes()
        self.last: MetamathToken = MetamathToken(TokenType.BOF, "None", 0, 0, "")
        self.token: MetamathToken = self.last
        self.action: Dict[TokenType, Callable[[MetamathLexer], None]] = {
            TokenType.DA: self.remove_var,
            TokenType.DD: self.add_vars,
            TokenType.DE: self.remember_var,
            TokenType.DF: self.process_f,
            TokenType.DP: self.process_p,
            TokenType.DLBRACE: self.dlbrace,
            TokenType.DRBRACE: self.drbrace
        }

    def get_token(self, lexer: MetamathLexer) -> MetamathToken:
        """Get the next token from the metamath file.

        :param MetamathLexer lexer: the lexer for fetching tokens
        :return: The next token, or None if no further tokens are available.
        :rtype: Optional[MetamathToken]
        """
        self.last = self.token
        self.token = lexer.get_token()
        return self.token

    def process_f(self, lexer: MetamathLexer) -> None:
        """Process a $f statement.

        :param MetamathLexer lexer: the lexer for fetching tokens
        """
        last = self.last
        df = self.token
        typ = self.get_token(lexer)
        name = self.get_token(lexer)
        dot = self.get_token(lexer)
        if (not typ or not name or not dot or dot.typ != TokenType.DDOT):
            if dot:
                last_line = dot.line
                last_col = dot.column
            elif name:
                last_line = name.line
                last_col = name.column
            elif typ:
                last_line = typ.line
                last_col = typ.column
            else:
                last_line = df.line
                last_col = df.column
            raise SyntaxError("Malformed $f declaration",
                              {"filename": last.fil,
                               "lineno": last.line,
                               "offset": last.column,
                               "text": last.text,
                               "end_lineno": last_line,
                               "end_offset": last_col})
        self.scopes.add_f_decl(last.text, name.text)

    def add_vars(self, lexer: MetamathLexer) -> None:
        """Process the variables in a $d statement.

        :param MetamathLexer lexer: the lexer for fetching tokens
        """
        token = self.get_token(lexer)
        while token.typ != TokenType.EOF and token.typ != TokenType.DDOT:
            self.scopes.add_d_variable(token)
            token = self.get_token(lexer)

    def remove_var(self, lexer: MetamathLexer) -> None:
        """Process the variables in a $a statement.

        :param MetamathLexer lexer: the lexer for fetching tokens
        """
        token = self.get_token(lexer)
        while token.typ != TokenType.EOF and token.typ != TokenType.DDOT:
            self.scopes.remove_theorem_var(token.text)
            token = self.get_token(lexer)

    def remember_var(self, lexer: MetamathLexer) -> None:
        """Process the variables in a $e statement.
        In particular, remember the variables in case they are mentioned in a
        subsequent $d statement.

        :param MetamathLexer lexer: the lexer for fetching tokens
        """
        token = self.get_token(lexer)
        while token.typ != TokenType.EOF and token.typ != TokenType.DDOT:
            self.scopes.remove_theorem_var(token.text)
            self.scopes.add_e_variable(token.text)
            token = self.get_token(lexer)

    def process_p(self, lexer: MetamathLexer) -> None:
        """Process the variables in a $p statement.

        :param MetamathLexer lexer: the lexer for fetching tokens
        """
        token = self.get_token(lexer)
        while token.typ != TokenType.EOF and token.typ != TokenType.DEQ:
            self.scopes.remove_theorem_var(token.text)
            token = self.get_token(lexer)
        token = self.get_token(lexer)
        while token.typ != TokenType.EOF and token.typ != TokenType.DDOT:
            self.scopes.remove_proof_var(token.text)
            token = self.get_token(lexer)

    def dlbrace(self, lexer: MetamathLexer) -> None:
        """Process a ${ token.

        :param MetamathLexer lexer: the lexer for fetching tokens
        """
        self.scopes.push_scope()

    def drbrace(self, lexer: MetamathLexer) -> None:
        """Process a $} token.

        :param MetamathLexer lexer: the lexer for fetching tokens
        """
        self.scopes.pop_scope()

    def check(self, filename: str) -> None:
        """Check the metamath file for unnecessary dv conditions.

        :param str filename: the name of the file to check
        """
        print(f"Checking {filename}")
        with MetamathLexer(filename) as lexer:
            token: MetamathToken = self.get_token(lexer)
            while token.typ != TokenType.EOF:
                f = self.action.get(token.typ, None)
                if f:
                    f(lexer)
                token = self.get_token(lexer)

if __name__ == '__main__':
    if len(sys.argv) < 2:
        print(f"Usage: {sys.argv[0]} file.mm...")
    else:
        for i in range(1, len(sys.argv)):
            checker = DVChecker()
            checker.check(sys.argv[i])
