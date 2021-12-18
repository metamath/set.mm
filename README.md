[![Build Status](https://github.com/metamath/set.mm/workflows/verifiers/badge.svg)](https://github.com/metamath/set.mm/actions?query=workflow%3Averifiers)

# Metamath set.mm repository

This is a collection of databases that specify mathematical axioms and
rigorous formal proofs of various mathematical theorems
derived from those axioms.
This collection is specified and derived using the Metamath system.
A "database" in Metamath parlance is a collection of one or more text files.

This collection is being actively improved by an international community.
Please join us!

The two largest databases in this collection are "set.mm" and "iset.mm".
The "set.mm" database is one of the largest
collections of formally-verified mathematics in the world (e.g., it
has completed many challenge theorems in the
[Formalizing-100 Theorems](https://www.cs.ru.nl/~freek/100/) challenge list).
It is also one of the most rigorously verified collection of
formally-verified mathematics in the world; it's verified by
5 different verifiers written by 5 different people
in 5 different programming languages.

## What is Metamath?

Metamath is a computer language and associated computer program for
archiving, verifying, and studying mathematical proofs.

Unlike some other systems, Metamath does not build a particular set
of axioms into the system. Instead, the Matamath language is simple and robust,
with an almost total absence of hard-wired syntax.
In Metamath you express the axioms *and* the theorems in a database.
To prove a theorem, every proof step *must* be proven using an axiom or
a previously-proven theorem; as a result, nothing is hidden.
We believe Metamath provides about the simplest possible framework that
allows essentially of mathematics to be expressed with absolute rigor.

For more information see
the [Metamath Home Page](http://us.metamath.org/), the
[Metamath Proof Explorer Home Page](http://us.metamath.org/mpeuni/mmset.html),
the [Metamath book](http://us.metamath.org#book), or the
[video "Metamath Proof Explorer: A Modern Principia Mathematica](https://www.youtube.com/watch?v=8WH4Rd4UKGE).

## What databases are included in this collection?

This is a collection of many databases, but since "set.mm" is by far
the most actively maintained, you may want to look at it first even if you
plan to eventually work on something else.
[The video "Metamath Proof Explorer (set.mm) contributions visualized with Gource through 2019-10-04"]( https://www.youtube.com/watch?v=XC1g8FmFcUU&list=PL1jSu6GGefBm7RBP0Id2Sa9uyVuyhioAC&index=4) shows set.mm's growth over time.

The databases included, in (approximate) decreasing size, are:

* "set.mm" aka Metamath Proof Explorer (MPE) -
  uses classical logic and
  Zermelo–Fraenkel set theory with the axiom of choice (ZFC).
* "iset.mm" aka "Intuitionistic Logic Explorer" -
  uses intuitionistic logic instead of classical logic,
  e.g., it does not presume that the law of the implied middle is true
  in all cases.
* "nf.mm" aka "New Foundations Explorer" - constructs mathematics using
  Quine's "New Foundations" (NF) set theory axioms, a direct derivative
  of the "hierarchy of types" set theory originally presented in
  Whitehead and Russell's *Principia Mathematica*.
* "ql.mm" aka "Quantum Logic Explorer" - Starts from the orthomodular
  lattice properties proved in the Hilbert Space Explorer and takes
  you into quantum logic.
* "hol.mm" aka "Higher-Order Logic Explorer" - Starts with HOL (also
  called simple type theory) and derives equivalents to ZFC axioms,
  connecting the two approaches.
* "peano.mm" - Peano arithmetic.
* "big-unifier.mm" - a unification and substitution test for
  Metamath verifiers, where small input expressions blow up to thousands
  of symbols.  It is a translation of William McCune's "big-unifier.in"
  for the OTTER theorem prover.
* "miu.mm"  - a simple formal system for use as a demonstration based
  on work by Hofstadter.
* "demo0.mm" - a simple formal system used as a demonstration in
  Chapter 2 of the Metamath book.

## How are they verified?

Changes ("commits") to any database are first automatically verified
before they are accepted, using GitHub actions.

The set.mm and iset.mm databases are the ones primarily being updated.
Every change to these databases are verified by the following
different verifiers:

* metamath.exe aka Cmetamath (the original C verifier by Norman Megill)
* checkmm (a C++ verifier by Eric Schmidt)
* smetamath-rs (smm3) (a Rust verifier by Stefan O'Rear)
* mmj2 (a Java verifier by Mel L. O'Cat and Mario Carneiro)
* mmverify.py (a Python verifier by Raph Levien)

Note that these are different verifiers written in different programming
languages by different people. In addition, the verification algorithm
is intentionally simple (it fits in two pages in the Matamath book).
This provides *extremely* high confidence that the proofs are correct.
Most math proofs are not formally verified at all (that is, where a
computer verification verifies every step). The rest are typically only
verified by a single program (which might have an error in it).
These multiple independent verifications provide very high confidence
of their being correct.

All other databases are verified by at least one verifier.

## How can I contribute?

First, take a look at some existing proofs.
Walking through the 
[Metamath Proof Explorer (MPE, aka set.mm)](http://us.metamath.org/mpegif/mmset.html) is a good way to start.

To create a proof, you need to pick a tool.
The Metamath system specifies a common file format, not a single tool
everyone has to use.
Many in the community use the [mmj2 tool](http://us.metamath.org#book).
The video [Introduction to Metamath and mmj2](https://www.youtube.com/watch?v=Rst2hZpWUbU) demonstrates using mmj2.
The mmj2 tool includes an interactive tutorial, and if you just want to watch,
there's a video giving a
[Walkthrough of the tutorial in mmj2](https://www.youtube.com/watch?v=87mnU1ckbI0&t=2094s).
You should start small and try to reprove what's already
proven with Metamath before you try to prove something new.
If you're contributing to set.mm or iset.mm, take a look at its
[conventions and style](http://us.metamath.org/mpegif/conventions.html).

At some point you should join the
[Metamath mailing list](https://groups.google.com/g/metamath).
We're a friendly community and we would love to have more collaborators!

The Wiki page
[Getting started with contributing](https://github.com/metamath/set.mm/wiki/Getting-started-with-contributing) will walk you the process of contributing
a final proof once you have one.
Basically, you'll create a "pull request" on GitHub to request
merging of some change(s).
**Warning**: Changes are made to the **develop** branch.

## What are the requirements for acceptance (merging)?

A pull request (proposed change) *must* pass all verifiers before
it will be merged (accepted). This even enforces some style rules on
some databases, e.g., we want a name and date for each new theorem.

To be merged, a pull request must be approved by a different existing
contributor (someone who's already had some previous contributions accepted).
You can approve a change by viewing the pull request, selecting
the tab "Files Changed", clicking on the "Review Changes" button,
clicking on "Approve", and submitting the review.
You can also approve by using the comment "+1".
Feel free to approve something others have approved, that makes it clear
there's no serious issue.

Once a pull request is approved (other than the person
originally proposing the change), any maintainer can merge it,
including the approver.
A maintainer is a member or owner of the Metamath GitHub organization.

We-generally tend to have a bias towards "merge this now" with separate
follow-up fixes for minor issues (e.g., to use a better name). That reduces the
risk of losing good ideas, or a lot of rework, due to some minor
blemish like an odd name. It's a pain to fix "merge conflicts"
because differences have accumulated over time, and we'd rather avoid
merge conflicts if there's no good reason to have them.

We encourage changes to be smaller, focusing on a single logical idea.
That makes changes much easier to review.
It also makes it easy to accept some changes while not accepting others.

Many contributors have or create a personal "mathbox" - a sandbox of work that
is visible to others. Changes to ones' own mathbox still go through a
review, but usually it's cursory - we generally just want to ensure that those
changes don't interfere with or confuse others.
Mathbox changes must still pass all verifiers, though, and that is
a very rigorous check.

Some areas may have "area maintainers" - changes to those areas
must generally also be approved by at least one of the area maintainer(s).
Similarly, mathboxes should normally only be changed by the owner of the
mathbox (unless it's a general improvement that applies across the database).
We don't currently have a list of area maintainers; please propose
a change to this README (here) if you want to be an area maintainer.

## Credits and a memorium

Our sincere thanks to *everyone* who has contributed to this work.

In addition, this entire collection is dedicated to the memory of
[Norman "Norm" Dwight Megill, Ph.D. (1950-2021)](https://www.legacy.com/us/obituaries/bostonglobe/name/norman-megill-obituary?id=31842140),
creator of the Metamath system and cultivator of an international
community of people with the shared dream of digitizing and
formally verifying mathematics.
His ideas and design have been influential in formal mathematics
around the world. He is missed.
