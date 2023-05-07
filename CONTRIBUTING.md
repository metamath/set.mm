# Contributing and Acceptance

We're a friendly community, and we would love to have more collaborators!

This document briefly explains
[how to contribute proposed changes](#how-can-i-contribute)
("contributions" or "merge requests") to this collection of databases.
We also discuss
[Formatting recommendation prior to submitting a pull request](#formatting-recommendation-prior-to-submitting-a-pull-request), and for the rare cases
when it's needed, information on
[regenerating the `discouraged` file](#regenerating-the-discouraged-file).
This page also describes
[how these proposed changes are evaluated](#what-are-the-requirements-for-acceptance-merging)
to decide if they will be accepted, since presumably you'll want to
meet those criteria when creating a contribution.

## How can I contribute?

First, take a look at some existing proofs.
Walking through the
[Metamath Proof Explorer (MPE, aka set.mm)](http://us.metamath.org/mpeuni/mmset.html) is a good way to start.

To create a proof, you need to pick a tool.
The Metamath system specifies a common file format, not a single tool
everyone has to use.
Many in the community use the [mmj2 tool](http://us.metamath.org#book), and
many of the rest use the original metamath C program (aka "metamath.exe").
The page
[Metamath Proof Assistants](https://github.com/metamath/set.mm/wiki/Metamath-Proof-Assistants)
provides more information about each tool.
The video [Introduction to Metamath and mmj2](https://www.youtube.com/watch?v=Rst2hZpWUbU) demonstrates using mmj2.
The mmj2 tool includes an interactive tutorial, and if you just want
to watch it, there's a video giving a
[Walkthrough of the tutorial in mmj2](https://www.youtube.com/watch?v=87mnU1ckbI0).

You should start small and try to reprove what's already
proven with Metamath before you try to prove something new.
If you're contributing to set.mm or iset.mm, take a look at its
[conventions and style](http://us.metamath.org/mpeuni/conventions.html).

At some point you should join the
[Metamath mailing list](https://groups.google.com/g/metamath).
If you're seriously working on proofs, we'd love to help you get started!

For contributing a final proof once you have one,
you'll basically create a "pull request" on GitHub to request
merging of some change(s) into the corresponding Git repository.
**Warning**: Changes are made to the **develop** branch.
The Wiki page
[Getting started with contributing](https://github.com/metamath/set.mm/wiki/Getting-started-with-contributing)
will walk you through the process of contributing a final proof once you have one.

**NOTE**: Any proposed contribution must be licensed under the
[Creative Commons 0 (CC0) License](LICENSE), so any proposed contribution
is automatically licensed as such.

## Formatting recommendation prior to submitting a pull request

On pull requests we check that set.mm and iset.mm have been rewrapped to
help conform to their formatting conventions.

Locally you will need to run `scripts/rewrap set.mm` to avoid failing this
check.

If you prefer to run metamath yourself rather than via `scripts/rewrap`,
the following commands should do the same thing, and/or help you detect
other problems before submission. But if you want you can just leave it up to
the automated verification checks and worry about rewrapping and the
others if and when something fails.

<PRE>
./metamath
MM> read set.mm
MM> write source set.mm /rewrap
MM> erase
MM> read set.mm
MM> save proof */compressed/fast
MM> verify markup */file_skip/top_date_skip
MM> verify proof *
MM> write source set.mm
MM> quit
</PRE>

This can also be done as a single command in bash:

<PRE>
./metamath 'read set.mm' 'write source set.mm /rewrap' \
   erase 'read set.mm' 'save proof */compressed/fast' \
   'verify markup */file_skip/top_date_skip' 'verify proof *' \
   'write source set.mm' quit
</PRE>

or in one line, for ease of copypasting:

<PRE>
./metamath 'read set.mm' 'write source set.mm /rewrap' erase 'read set.mm' 'save proof */compressed/fast' 'verify markup */file_skip/top_date_skip' 'verify proof *' 'write source set.mm' quit
</PRE>

and for iset.mm:

<PRE>
./metamath 'read iset.mm' 'write source iset.mm /rewrap' erase 'read iset.mm' 'save proof */compressed/fast' 'verify markup */file_skip/top_date_skip' 'verify proof *' 'write source iset.mm' quit
</PRE>

The reason for doing /rewrap first is so that 'save proof' will subsequently
adjust the proof indentation to match any indentation changes made by /rewrap.
Then, 'verify markup' will check that no lines became too long due to different
indentation.  Finally, 'verify proof' is there because you might as well.

(You can also check definitional soundness with mmj2 and any 'discouraged'
markup changes before submission if you want, or you can just leave it up to
the automated verification checks to check those.)

## Regenerating the `discouraged` file

In almost all cases, especially when you're starting, you won't need to
regenerate the `discouraged` file. So if you're just starting out, you can
probably ignore this section. However, there are rare cases when that
is needed. This section explains what the discouraged file is all about.

Some statement descriptions in `set.mm` and `iset.mm` have one or both of the
markup tags `(New usage is discouraged.)` and `(Proof modification is discouraged.)`.
In order to monitor accidental violations of these tags in set.mm and iset.mm,
we store the usage and proof lengths of statements with these tags in a file
called `discouraged` for set.mm and `iset-discouraged` for iset.mm.
The automated check will return an error if this file does not exactly match the
one that it generates for a set.mm pull request.

If you make modifications that affect the `discouraged` file, you should
regenerate it with the following command under Linux or Cygwin bash:

<PRE>
./metamath 'read set.mm' 'set width 9999' 'show discouraged' quit \
    | tr -d '\015' | grep '^SHOW DISCOURAGED.' \
    | sed -E -e 's/^SHOW DISCOURAGED.  ?//' | LC_ALL=C sort > discouraged
</PRE>

or in one line, for ease of copypasting:

<PRE>
./metamath 'read set.mm' 'set width 9999' 'show discouraged' quit | tr -d '\015' | grep '^SHOW DISCOURAGED.' | sed -E -e 's/^SHOW DISCOURAGED.  ?//' | LC_ALL=C sort > discouraged
</PRE>

and for iset.mm:

<PRE>
./metamath 'read iset.mm' 'set width 9999' 'show discouraged' quit | tr -d '\015' | grep '^SHOW DISCOURAGED.' | sed -E -e 's/^SHOW DISCOURAGED.  ?//' | LC_ALL=C sort > iset-discouraged
</PRE>

The "tr -d '\015'" is needed with Cygwin to strip carriage returns and has no
effect in Linux.

The `discouraged` file can also be regenerated with mmj2, which currently runs
faster than metamath.exe for this function.
See the automated verification script for the details.


The metamath.exe and mmj2 proof assistants will prevent most accidental
violations.  The behavior of the metamath.exe proof assistant in the presence
of these tags and how to override them is described in the 11-May-2016 entry of
<http://us.metamath.org/mpeuni/mmnotes.txt>.

Please note that when you regenerate the `discouraged` file, before comitting
it you should compare it to the existing one to make sure the differences are
what you expected and there are no accidental changes elsewhere.
The purpose of this file is to help detect such accidental changes, and if it
is not inspected manually that purpose is defeated.

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

*Note*: Reviewers should investigate a commit that changes a
`discouraged` file, since this means the commit is doing something
that is normally discouraged.  That doesn't make it wrong, it just means a
rationale is needed.

Once a pull request is approved (other than the person
originally proposing the change), any maintainer can merge it,
including the approver.
A maintainer is a member or owner of the Metamath GitHub organization.

We generally tend to have a bias towards "merge this now" with separate
follow-up fixes for minor issues (e.g., to use a better name). That reduces the
risk of losing good ideas, or a lot of rework, due to some minor
blemish like an odd name. It's a pain to fix "merge conflicts"
because differences have accumulated over time, and we'd rather avoid
merge conflicts if there's no good reason to have them.

We encourage changes to be smaller, focusing on a single logical idea.
That makes changes much easier to review.
It also makes it easy to accept some changes while not accepting others.

Many contributors have or create a personal "mathbox" - a sandbox of work that
is visible to others. Changes to someone's own mathbox still go through a
review, but usually it's cursory - we generally just want to ensure that those
changes don't interfere with or confuse others.
Mathbox changes must still pass all verifiers, though, and that is
a very rigorous check.
Mathboxes should normally only be changed by the owner of the
mathbox (unless it's a general improvement that applies across the database).

The following people are active and are willing to be contacted
concerning the areas listed.  This area maintainership is not (at least
currently) part of the approval/merge process described above, but hopefully
this list will help you find people who work on a particular area.
Please propose a change to this file if you want to be an area maintainer.

* Mario Carneiro (@digama0): Any part of set.mm or iset.mm

* Benoit Jubin (@benjub): set.mm and the CZF part of iset.mm

* Jim Kingdon (@jkingdon): iset.mm, df-tau

## For more information

For more general information, see the [README.md](README.md) file.
