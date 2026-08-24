#!/usr/bin/env python3
# Rewrap Metamath comments without the metamath C program.
# Vincent Gonzalez <vincegonzalez@me.com>
# SPDX-License-Identifier: CC0-1.0
#
# scripts/rewrap runs "write source /rewrap" through the metamath executable,
# which also runs "save proof */compressed/fast" and reindents proof bodies.
# This does only the comment filling, so it is enough when a change touches
# comments and not proofs.  Change a proof and you still need the executable.
#
#   rewrap-comments.py set.mm --check      report comments that need rewrapping
#   rewrap-comments.py set.mm --in-place   rewrap them
#
# Comments it does not model are left untouched and their labels printed: those
# containing <HTML>, those not attached to a $a or $p, and those holding a run
# too long to break (a ~ reference followed by a long URL).
#
# It also differs from the metamath executable in one respect: file inclusions
# are not resolved.  The executable parses after resolving them; this reads a
# single file, so a comment in an included file is checked only if the tool is
# run on that file as well.  No database in this repository uses inclusions.
#
# The rules below are transcribed from rewrapComment() in mmpars.c and the
# line-breaking loop of printLongLine() in mminou.c.

import argparse
import re
import sys

WIDTH = 79
NB = "\x04"  # ASCII_4 in mmpars.c: a space the line may not break at

OPENING = "(['\""
CLOSING = ".,;)?!:]'\""
SENTENCE_END = ")'\""

PROOF_DISCOURAGED = "(Proof modification is discouraged.)"
USAGE_DISCOURAGED = "(New usage is discouraged.)"

COMMENT = re.compile(r"\$\(.*?\$\)", re.S)
# A file inclusion may sit between a comment and the statement it describes.
# The metamath executable resolves inclusions before parsing, so step over
# them here rather than reading "$[" as a label.
STATEMENT = re.compile(r"(?:\s*\$\[.*?\$\])*\s*[A-Za-z0-9_.\-]+\s+\$[ap]\s",
                       re.S)


def space_surround(s, ch, subscript_exception=False):
    # A closing backtick followed by _ or - takes no space: ` a `_2 renders as a
    # subscript and ` a ` _2 does not.  mmpars.c carries the same exception.
    out = list(s)
    i = 1
    mathmode = 0
    while i < len(out) - 1:
        if out[i] != ch:
            i += 1
            continue
        if out[i - 1] == ch or (i + 1 < len(out) and out[i + 1] == ch):
            i += 2  # `` or ~~ escape
            continue
        mathmode = 1 - mathmode
        nxt = out[i + 1] if i + 1 < len(out) else ""
        if nxt not in (" ", "\n", ""):
            if not subscript_exception or mathmode == 1 or nxt not in ("_", "-"):
                out.insert(i + 1, " ")
        if out[i - 1] != " ":
            out.insert(i, " ")
            i += 1
        i += 1
    return "".join(out)


def two_spaces_after_sentences(c):
    # Only when the next character is a capital or opening punctuation, and not
    # after an initial.  This is why "[Margaris] p. 49" keeps one space.
    for ch in ".?!:":
        i = 1
        while True:
            p = c.find(ch, i)
            if p < 0:
                break
            i = p + 1
            if ch == "." and p > 0 and "A" <= c[p - 1] <= "Z":
                continue
            q = p + 1
            if q < len(c) and c[q] in SENTENCE_END:
                q += 1
            if q >= len(c) or c[q] != " ":
                continue
            nxt = c[q + 1] if q + 1 < len(c) else ""
            if ("A" <= nxt <= "Z") or (nxt and nxt in OPENING):
                c = c[:q + 1] + " " + c[q + 1:]
                i = q + 2
    return c


def mark_nonbreaking(c):
    n = len(c)
    tmpl = [" "] * n
    for p in range(2, n - 2):
        if c[p] != " ":
            continue
        if c[p - 1] == "~" and c[p - 2] != "~":
            tmpl[p] = NB  # do not split "~ label"
        elif (c[p - 2] == " " or c[p - 2] in OPENING) and c[p - 1] in OPENING:
            tmpl[p] = NB
        elif (p + 2 < n
              and (c[p + 2] in (" ", "\n", NB) or c[p + 2] in CLOSING)
              and c[p + 1] in CLOSING):
            tmpl[p] = NB
        elif c[p - 3] == " " and c[p - 2] == "p" and c[p - 1] == ".":
            tmpl[p] = NB  # do not split " p. 49"
    if n >= 3:
        tmpl[n - 3] = NB  # the space before "$)"
    return "".join(NB if tmpl[p] == NB else c[p] for p in range(n))


def normalize(comment):
    c = space_surround(comment, "`", subscript_exception=True)
    if "`" not in c[1:]:
        c = space_surround(c, "~")

    # A single newline becomes a space; a doubled one is a paragraph break.
    body = list(c)
    for p in range(2, len(body) - 2):
        if body[p] == "\n" and body[p - 1] != "\n" and body[p + 1] != "\n":
            body[p] = " "
    c = re.sub(r"  +", " ", "".join(body))

    while len(c) >= 4 and c[-4] in (" ", "\n"):
        c = c[:-4] + c[-2:]
    if len(c) >= 4 and c[-4].islower():
        c = c[:-3] + ". $)"

    out = []
    math = False
    for p, ch in enumerate(c):
        if ch == "`":
            math = not math
        out.append(NB if (math and ch == " " and 2 <= p < len(c) - 2) else ch)
    c = "".join(out)

    for markup in (PROOF_DISCOURAGED, USAGE_DISCOURAGED):
        p = c.find(markup)
        if p >= 0:
            c = c[:p] + markup.replace(" ", NB) + c[p + len(markup):]

    return mark_nonbreaking(two_spaces_after_sentences(c))


def fill(text, first_prefix, cont_prefix, width=WIDTH):
    # printLongLine() scans back from one past the margin for a space to break
    # at.  When there is none it widens the margin rather than splitting a
    # token, which is how long URLs stay intact.
    lines = []
    line = first_prefix + text
    first = True
    while len(line) > width:
        p = width
        while p > 0 and line[p] != " ":
            p -= 1
        if p <= len(first_prefix if first else cont_prefix):
            q = line.find(" ", width)
            if q < 0:
                break
            p = q
        lines.append(line[:p].rstrip(" " + NB))
        line = cont_prefix + line[p + 1:].lstrip()
        first = False
    lines.append(line.rstrip(" " + NB))
    return lines


def rewrap_comment(block, indent, width=WIDTH):
    """Rewrap one $( ... $) comment whose $( sits at column indent."""
    if not (block.startswith("$(") and block.endswith("$)")):
        raise ValueError("not a comment")
    c = normalize(block)
    pad = " " * indent
    out = []
    for k, para in enumerate(c.split("\n\n")):
        # mmpars.c strips the leading spaces after each newline before adding
        # indent + 3; keeping them puts every later paragraph a column deep.
        body = para.strip("\n").lstrip(" ")
        out.append("\n".join(fill(body, pad if k == 0 else pad + "   ",
                                  pad + "   ", width)))
    return "\n\n".join(out).replace(NB, " ")


def modelled(block, indent, following, width=WIDTH):
    """Whether this reproduces rewrap for this comment.  If not, leave it be."""
    if "<HTML>" in block:
        return False
    if not STATEMENT.match(following):
        # The rewrapping in outputStatement() sits inside the $a/$p case, so
        # a comment not attached to a statement is never reflowed by the
        # metamath executable.
        return False
    budget = width - indent - 3
    for run in normalize(block).split(" "):
        if len(run.replace(NB, " ").strip()) > budget:
            return False
    return True


def process(text):
    """Returns the rewrapped text, the labels changed, and the labels skipped."""
    out = []
    pos = 0
    changed = []
    skipped = []
    for m in COMMENT.finditer(text):
        out.append(text[pos:m.start()])
        start = text.rfind("\n", 0, m.start()) + 1
        prefix = text[start:m.start()]
        block = m.group(0)
        following = text[m.end():m.end() + 160]
        label = STATEMENT.match(following)
        label = following.split()[0] if label else "?"
        if prefix.strip() or not modelled(block, len(prefix), following):
            out.append(block)
            if not prefix.strip() and STATEMENT.match(following):
                skipped.append(label)
        else:
            new = rewrap_comment(block, len(prefix))[len(prefix):]
            out.append(new)
            if new != block:
                changed.append(label)
        pos = m.end()
    out.append(text[pos:])
    return "".join(out), changed, skipped


def main():
    ap = argparse.ArgumentParser(
        description="Rewrap Metamath comments without the metamath "
                    "executable.")
    ap.add_argument("database")
    ap.add_argument("--check", action="store_true",
                    help="exit 1 if any comment needs rewrapping")
    ap.add_argument("--in-place", action="store_true",
                    help="write the database back")
    ap.add_argument("--verbose", action="store_true",
                    help="name the comments left alone even when none changed")
    args = ap.parse_args()

    with open(args.database, encoding="utf-8", errors="replace") as f:
        text = f.read()
    result, changed, skipped = process(text)

    # Name the ones left alone only when there is something to act on;
    # a passing check should be quiet.
    if skipped and (changed or args.verbose):
        print("left alone (%d): %s" %
              (len(skipped), ", ".join(skipped[:12])
               + ("..." if len(skipped) > 12 else "")), file=sys.stderr)

    if args.check:
        if changed:
            print("%d comment(s) need rewrapping: %s" %
                  (len(changed), ", ".join(changed[:12])
                   + ("..." if len(changed) > 12 else "")))
            return 1
        print("rewrapped already; %d comment(s) not modelled" % len(skipped))
        return 0

    if args.in_place:
        with open(args.database, "w", encoding="utf-8", newline="\n") as f:
            f.write(result)
        print("rewrapped %d comment(s)" % len(changed))
    else:
        sys.stdout.write(result)
    return 0


if __name__ == "__main__":
    sys.exit(main())
