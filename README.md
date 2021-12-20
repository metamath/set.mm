[![Build Status](https://github.com/metamath/set.mm/workflows/verifiers/badge.svg)](https://github.com/metamath/set.mm/actions?query=workflow%3Averifiers)

# Metamath set.mm repository

This is a collection of rigorously-verified [Metamath](http://us.metamath.org/)
databases that specify mathematical axioms and
formal proofs of theorems derived from those axioms.

Please join us to improve it further!

## What is Metamath?

Metamath is a computer language and associated computer program for
archiving, verifying, and studying mathematical proofs.

Unlike some other systems, Metamath does not build a particular set
of axioms into the system. Instead, the Matamath language is simple and robust,
with an almost total absence of hard-wired syntax.
In Metamath you express the axioms *and* the theorems in a database.
To prove a theorem, every proof step *must* be proven using an axiom or
a previously proven theorem; as a result, nothing is hidden.
We believe Metamath provides about the simplest possible framework that
allows essentially all of mathematics to be expressed with absolute rigor.

For more information see
the [Metamath Home Page](http://us.metamath.org/), the
[Metamath Proof Explorer Home Page](http://us.metamath.org/mpeuni/mmset.html),
the [Metamath book](http://us.metamath.org#book), or the
[video "Metamath Proof Explorer: A Modern Principia Mathematica"](https://www.youtube.com/watch?v=8WH4Rd4UKGE).

## What databases are included in this collection?

This is a collection of many databases.
A "database" in Metamath parlance is a collection of one or more text files
that define axioms, theorems, and their proofs.
Since "set.mm" is by far
the most actively maintained, you may want to look at it first even if you
plan to eventually work on something else.
The databases included and links to their generated displays,
in (approximate) decreasing size, are:

* "[set.mm](./set.mm)" aka "Metamath Proof Explorer (MPE)" -
  uses classical logic and
  Zermelo–Fraenkel set theory with the axiom of choice (ZFC).
  This is one of the largest collections of formally verified mathematics
  in the world (e.g., it has completed many challenge theorems in the
  [Formalizing-100 Theorems](https://www.cs.ru.nl/~freek/100/) challenge list);
  [this video visualizes set.mm's growth through 2020-04-29](https://www.youtube.com/watch?v=LVGSeDjWzUo).
  [[Generated display](http://us.metamath.org/mpeuni/mmset.html)]
* "[iset.mm](./iset.mm)" aka "Intuitionistic Logic Explorer" -
  uses intuitionistic set theory.
  In particular, it does not presume that the law of excluded middle is
  necessarily true in all cases.
  [[Generated display](http://us.metamath.org/mpeuni/mmil.html)]
* "[nf.mm](.nf.mm)" aka "New Foundations Explorer" -
  constructs mathematics using
  Quine's New Foundations (NF) set theory axioms, a direct derivative
  of the "hierarchy of types" set theory originally presented in
  Whitehead and Russell's *Principia Mathematica*.
  [[Generated display](http://us.metamath.org/nfeuni/mmnf.html)]
* "[ql.mm](./ql.mm)" aka "Quantum Logic Explorer" - Starts from the
  orthomodular lattice properties proved in the Hilbert Space Explorer and
  takes you into quantum logic.
  [[Generated display](http://us.metamath.org/qleuni/mmql.html)]
* "[hol.mm](./hol.mm)" aka "Higher-Order Logic Explorer" - Starts with
  higher-order logic (HOL, also called simple type theory) and derives
  equivalents to ZFC axioms, connecting the two approaches.
  [[Generated display](http://us.metamath.org/holuni/mmhol.html)]
* "[peano.mm](./peano.mm)" - Peano arithmetic.
* "[big-unifier.mm](./big-unifier.mm)" - a unification and substitution test for
  Metamath verifiers, where small input expressions blow up to thousands
  of symbols. It is a translation of William McCune's "big-unifier.in"
  for the OTTER theorem prover.
* "[miu.mm](./miu.mm)"  - a simple formal system for use as a
  demonstration based on work by Hofstadter.
* "[demo0.mm](./demo0.mm)" - a simple formal system used as a demonstration in
  Chapter 2 of the Metamath book.

## How are they verified?

We work to provide *extremely* high confidence that the
proofs are completely correct in these databases,
especially for the set.mm and iset.mm databases (the
primary databases under active development).
Most published mathematical proofs don't have a formal proof at all
(a formal proof is a proof where every step is completely and
automatically verified by machine).
Most other projects would be delighted to have formal verification of
proofs by a *single* verification tool.
We could do that in Metamath, too, but we go much further.

Changes ("commits") to any database are first automatically verified
before they are accepted, using GitHub actions.
In *every* change, the proofs of *each* of the set.mm and iset.mm databases
is re-verified by *five* different verifiers:

* metamath.exe aka Cmetamath (the original C verifier by Norman Megill)
* checkmm (a C++ verifier by Eric Schmidt)
* smetamath-rs (smm3) (a Rust verifier by Stefan O'Rear)
* mmj2 (a Java verifier by Mel L. O'Cat and Mario Carneiro)
* mmverify.py (a Python verifier by Raph Levien)

Note that these are different verifiers written in different programming
languages by different people. The verification algorithm
is also intentionally simple (it fits in two pages in the Matamath book),
so it's relatively easy to implement a verifier, it's more likely to be
correct (because of its simplicity), and it's relatively
easy to review a verifier.

All other databases' proofs are verified by one verifier (metamath.exe).

Other checks are also performed.
Text markup is checked by metamath-exe, and definitions are checked by mmj2.

## How can I contribute? How are contributions evaluated?

We're a friendly community, and we would love to have more collaborators!

See [CONTRIBUTING.md](CONTRIBUTING.md) for more information on
how to create a contribution, as well as how contributions are evaluated
to decide if they will be merged in.

## Credits and a memorium

Our sincere thanks to *everyone* who has contributed to this work.

This entire collection is dedicated to the memory of
[Norman "Norm" Dwight Megill, Ph.D. (1950-2021)](https://www.legacy.com/us/obituaries/bostonglobe/name/norman-megill-obituary?id=31842140),
creator of the Metamath system and cultivator of an international
community of people with the shared dream of digitizing and
formally verifying mathematics.
His ideas and design have been influential in formal mathematics
around the world. He is missed.
