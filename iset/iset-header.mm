$( !
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Contents of this header
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

* Quick "How To"
* Bibliography
* Metamath syntax summary
* Other notes
* Acceptable shorter proofs


=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Quick "How To"
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

How to use this file under Windows 95/98/NT/2K/XP/Vista:

1. Download the program metamath.exe per the instructions on the
   Metamath home page (https://us.metamath.org) and put it in the same
   directory as this file.
2. In Windows Explorer, double-click on metamath.exe.
3. Type "read iset.mm" and press Enter.
4. Type "help" for a list of help topics, and "help demo" for some
   command examples.


=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Bibliography
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

Bibliographical references are made by bracketing an identifer in a theorem's
comment, such as [RussellWhitehead].  These refer to HTML tags on the following
web pages:

  Logic and set theory - see https://us.metamath.org/mpegif/mmset.html#bib
  Hilbert space - see https://us.metamath.org/mpegif/mmhil.html#ref

A bracketed reference must be preceded by a theorem number, etc. and followed
by a page number.  See "MM> HELP WRITE BIBLIOGRAPHY" for details.


=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Metamath syntax summary
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

The HELP LANGUAGE command in the Metamath program will give you a quick
overview of Metamath.  The specification is found on pp. 92--95 of the
Metamath book.  The following syntax summary is provided for convenience
but may omit some details.

A Metamath database (set of one or more ASCII source files) is a sequence of
_tokens_, which are normally separated by spaces or line breaks.  The only
tokens that are built into the Metamath language are those (two-character
sequences) beginning with $, shown in the following. These tokens are called
_keywords_:

          $c ... $. - Constant declaration
          $v ... $. - Variable declaration
          $d ... $. - Disjoint (distinct) variable restriction
  <label> $f ... $. - "Floating" hypothesis (i.e. variable type declaration)
  <label> $e ... $. - "Essential" hypothesis (i.e. a logical assumption for a
                      theorem or axiom)
  <label> $a ... $. - Axiom or definition or syntax construction
  <label> $p ... $= ... $. - Theorem and its proof
          ${ ... $} - Block for defining the scope of the above statements
                      (except $a, $p which are forever active)
$)        $( ... $)
$(                  - Comments (may not be nested); see HELP LANGUAGE
                      for markup features
          $[ ... $] - Include a file

The above two-character sequences beginning with "$" are the only primitives
built into the Metamath language.  The only "logic" Metamath uses in its proof
verification algorithm is the substitution of expressions for variables while
checking for distinct variable violations.  Everything else, including the
axioms for logic, is defined in this database file.

All other tokens are user-defined, and their names are arbitrary.  There are
two kinds of user-defined tokens, called math symbols (or just symbols) and
labels.  A _symbol_ may contain any non-whitespace printable character except
"$".  A _label_ may contain only alphanumeric characters and the characters "."
(period), "-" (hyphen), and "_" (underscore).  Symbols and labels are
case-sensitive.  All labels (except in proofs) must be distinct.  A label may
not have the same name as a symbol (to simplify the coding of certain parsers
and translators).

Here is some more detail about the syntax:

  $c <symbollist> $.
      <symbollist> is a (whitespace-separated) list of distinct symbols that
      haven't been used before.
  $v <symbollist> $.
      <symbollist> is a list of distinct symbols that haven't been used yet
      in the current scope (see ${ ... $} below).
  $d <symbollist> $.
      <symbollist> is a (whitespace-separated) list of distinct symbols
      previously declared with $v in current scope.  It means that
      substitutions into these symbols may not have variables in common.
  <label> $f <symbollist> $.
      <symbollist> is a list of 2 symbols, the first of which must be
      previously declared with $c in the current scope.
  <label> $e <symbollist> $.
      <symbollist> is a list of 2 or more symbols, the first of which must be
      previously declared with $c in the current scope.
  <label> $a <symbollist> $.
      <symbollist> is a list of 2 or more symbols, the first of which must be
      previously declared with $c in the current scope.
  <label> $p <symbollist> $= <proof> $.
      <symbollist> is a list of 2 or more symbols, the first of which must be
      previously declared with $c in the current scope.  <proof> is either a
      whitespace-delimited sequence of previous labels (created by
      SAVE PROOF <label> /NORMAL) or a compressed proof (created by
      SAVE PROOF <label> /COMPRESSED).  After using SAVE PROOF, use
      WRITE SOURCE to save the database file to disk.
  ${ ... $}
      Block for scoping the above statements (except $a, $p which are forever
      active).  Currently, $c may not occur inside of a block.
$)
  $( <any text> $)
$(    Comment.  Note: <any text> may not contain adjacent "$" and ")"
      characters.
  $[ <filename> $]
      Insert contents of <filename> at this point.  If <filename> is current
      file or has been already been inserted, it will not be inserted again.

Inside of comments, it is recommended that labels be preceded with a tilde (~)
and math symbol tokens be enclosed in grave accents (` `).  This way the LaTeX
and HTML rendition of comments will be accurate, and (future) tools to globally
change labels and math symbols will also change them in comments.  Note that ``
inside of grave accents is interpreted as a single ` .  A special comment
containing $ t defines LaTeX and HTML symbols.  See HELP LANGUAGE and
HELP HTML for other markup features in comments.

The proofs in this file are in "compressed" format for storage efficiency.  The
Metamath program reads the compressed format directly.  This format is
described in an Appendix of the Metamath book.  It is not intended to be read
by humans.  For viewing proofs you should use the various SHOW PROOF commands
described in the Metamath book (or the online HELP).

The Metamath program does not normally affect any content of this file other
than proofs, i.e., the text between "$=" and "$." (and some rewrapping).  All
other content is user-created.  Proofs are created or modified with the PROVE
command.


=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Other notes
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

1. It is recommended that you be familiar with Chapters 2 and 4 of the
Metamath book to understand the Metamath language.  Chapters 2, 3 and 5 explain
how to use the Metamath program.  Chapter 3 gives an informal overview of what
this source file is all about.  Appendix A gives the standard mathematical
symbols corresponding to some of the ASCII tokens used in this file.

The ASCII tokens may seem cryptic at first, even if you are familiar with set
theory, but a review of the definition summary in Chapter 3 should quickly
enable you to see the correspondence to standard mathematical notation.  To
easily find the definition of a token, search for the first occurrences of the
token surrounded by spaces.  Some odd-looking ones include "-." for "not", and
"C_" for "is a subset of".  The Metamath program "MM> HELP TEX" command
explains how to obtain a LaTeX output to see the real mathematical symbols.
Let us know if you have better suggestions for naming ASCII tokens.

2. Logic and set theory provide a foundation for all of mathematics.  To learn
about them, you should study one or more of the references listed below.  The
textbooks provide a motivation for what we are doing, whereas Metamath lets you
see in detail all hidden and implicit steps.  Most standard theorems are
accompanied by citations.  Some closely followed texts include the following:

  Axioms of propositional calculus - [Margaris].
  Axioms of predicate calculus - [Megill] (System S3' in the article
      referenced).
  Theorems of propositional calculus - [WhiteheadRussell].
  Theorems of pure predicate calculus - [Margaris].
  Theorems of equality and substitution - [Monk2], [Tarski], [Megill].
  Axioms of set theory - [BellMachover].
  Development of set theory - [TakeutiZaring].  (The first part of [Quine]
      has a good explanation of the powerful device of "virtual" or
      class abstractions, which is essential to our development.)
  Construction of real and complex numbers - [Gleason]
  Theorems about real numbers - [Apostol]
  Intuitionistic logic and constructive mathematics - [Bauer] is an sampling
    of theorems and arguments which give a flavor of constructive mathematics.
    [Heyting] is a more comprehensive treatment of intuitionistic logic.

3. Convention:  All $a statements starting with "|-" have labels
starting with "ax-" (axioms) or "df-" (definitions).  "ax-" corresponds
to what is traditionally called an axiom.  "df-" introduces new symbols
or a new relationship among symbols that can be eliminated; they always
extend the definition of a wff or class.  Metamath blindly treats $a
statements as new given facts but does not try to justify them.  The
mmj2 program will justify the definitions as sound, except for four of them
(df-bi, df-clab, df-cleq, df-clel) that require a more complex metalogical
justification by hand.

4. Our method of definition, the axioms for predicate calculus, and the
development of substitution are somewhat different from those found in standard
texts.  The axioms were designed for direct derivation of standard results
without excessive use of metatheorems.  (See Theorem 9.7 of [Megill] for a
rigorous justification.)  Typically we are minimalist when introducing new
definitions; they are introduced only when a clear advantage becomes apparent
for reducing the number of symbols, shortening proofs, etc.  We generally avoid
the introduction of gratuitous definitions because each one requires associated
theorems and additional elimination steps in proofs.

5. Where possible, the notation attempts to conform to modern conventions, with
variations due to our choice of the axiom system or to make proofs shorter.
Listed below are some important conventions and how they correspond to textbook
language.  The notation is usually explained in more detail when first
introduced.

  Typically, Greek letters (ph = phi, ps = psi, ch = chi, etc.) are used for
      propositional (wff) variables; x,y,z,... for individual (i.e. set)
      variables; and A,B,C,... for class variables.
  "|-", meaning "It is provable that," is the first token of all assertions
      and hypotheses that aren't syntax constructions.  This is a standard
      convention in logic.  For us, it also prevents any ambiguity with
      statements that are syntax constructions, such as "wff -. ph".
  "$e |- ( ph -> A. x ph ) $." should be read "Assume variable x is
      (effectively) not free in wff phi."  Literally, this says "Assume it is
      provable that phi implies for all x phi."
  "|- ( -. A. x x = y -> ..." should be read "If x and y are distinct
      variables, then..."  This antecedent provides us with a technical
      device (called a "distinctor" in [Megill]) to avoid the need for the
      $d statement early in our development of predicate calculus, permitting
      unrestricted substitituions as conceptually simple as those in
      propositional calculus.  However, the $d eventually becomes a
      requirement, and after that this device is rarely used.
  "[ y / x ] ph" should be read "the wff that results when y is properly
      substituted for x in ph."
  "$d x y $." should be read "Assume x and y are distinct variables."
  "$d x ph $." should be read "Assume x does not occur in phi $."  Sometimes
      a theorem is proved with "$e |- ( ph -> A. x ph ) $." in place of
      "$d x ph $." when a more general result is desired; ~ ax-17 can be used
      to derive the $d version.  For an example of how to get from the $d
      version back to the $e version, see the proof of ~ euf from ~ df-eu .
  "$d x A $." should be read "Assume x is not a variable occurring in class A."
  "$d x A $.  $d x ps $.  $e |- ( x = A -> ( ph <-> ps ) ) $." is an idiom
      often used instead of explicit substitution, meaning "Assume psi results
      from the substitution of A for x in phi."
  "$e |- A e. _V $." should be read "Assume class A is a set (i.e. exists)."
      This is a convenient convention used by [Quine].
  "$d x y $.  $e |- y e. A -> A. x y e. A $." should be read "Assume x is
      (effectively) not a free variable in class A."
  "`' R" should be read "converse of (relation) R" and is the same as the more
      standard notation R^{-1}.
  "( f ` x )" should be read "the value of function f at x" and is the same as
      the more familiar f(x).
  The Deduction Theorem of standard logic is never used.  Instead, in set
      theory, we use other tricks to make a $e hypothesis become an antecedent.
      See the comment for Theorem ~ dedth below.


=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Acceptable shorter proofs
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

Shorter proofs are welcome, and any shorter proof I accept will be acknowledged
in the theorem's description.  However, in some cases a proof may be "shorter"
or not depending on how it is formatted.  This section provides general
guidelines.

Usually I will automatically accept shorter proofs that (1) shorten the set.mm
file (with compressed proofs), (2) reduce the size of the HTML file generated
with SHOW STATEMENT xx / HTML, (3) use only existing, unmodified theorems in
the database (the order of theorems may be changed, though), and (4) use no
additional axioms.

Usually I will also automatically accept a _new_ theorem that is used to
shorten multiple proofs, if the total size of set.mm (including the comment of
the new theorem, not including the acknowledgment) decreases as a result.

In borderline cases, I typically place more importance on the number of
compressed proof steps and less on the length of the label section (since the
names are in principal arbitrary).  If two proofs have the same number of
compressed proof steps, I will typically give preference to the one with the
smaller number of different labels, or if these numbers are the same, the proof
with the fewest number of characters that the proofs happen to have by chance
when label lengths are included.

A few theorems have a longer proof than necessary in order to avoid the use of
certain axioms, for pedagogical purposes, and for other reasons.  Usually this
is clear from the theorem's description.  For example, ~ idALT shows a proof
directly from axioms.  Shorter proofs for such cases won't be accepted, of
course, unless the criteria described continues to be satisfied.

$)

