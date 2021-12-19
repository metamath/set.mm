# Contributing and Acceptance

We're a friendly community, and we would love to have more collaborators!

This document briefly explains
[how to contribute proposed changes](#how-can-i-contribute)
("contributions" or "merge requests") to this collection of databases
It also describes
[how these proposed changes are evaluated](#what-are-the-requirements-for-acceptance-merging)
to decide if they will be accepted, since presumably you'll want to
meet those criteria when creating a contribution.

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
[Walkthrough of the tutorial in mmj2](https://www.youtube.com/watch?v=87mnU1ckbI0).
You should start small and try to reprove what's already
proven with Metamath before you try to prove something new.
If you're contributing to set.mm or iset.mm, take a look at its
[conventions and style](http://us.metamath.org/mpegif/conventions.html).

At some point you should join the
[Metamath mailing list](https://groups.google.com/g/metamath).

The Wiki page
[Getting started with contributing](https://github.com/metamath/set.mm/wiki/Getting-started-with-contributing) will walk you the process of contributing
a final proof once you have one.
Basically, you'll create a "pull request" on GitHub to request
merging of some change(s).
**Warning**: Changes are made to the **develop** branch.

**NOTE**: Any proposed contribution must be licensed under the
[Creative Commons 0 (CC0) License](LICENSE), so any proposed contribution
is automatically licensed as such.

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
is visible to others. Changes to someone's own mathbox still go through a
review, but usually it's cursory - we generally just want to ensure that those
changes don't interfere with or confuse others.
Mathbox changes must still pass all verifiers, though, and that is
a very rigorous check.

Some areas may have "area maintainers" - changes to those areas
must generally also be approved by at least one of the area maintainer(s).
Similarly, mathboxes should normally only be changed by the owner of the
mathbox (unless it's a general improvement that applies across the database).
We don't currently have a list of area maintainers; please propose
a change to this file if you want to be an area maintainer.

## For more information

For more general information, see the [README.md](README.md) file.
