If you are new to GitHub and git, the basic instructions for
contributing changes to set.mm are described in the wiki,
[Getting started with contributing](https://github.com/metamath/set.mm/wiki/Getting-started-with-contributing).
(Feel free to enhance the wiki.)

The rest of this note shows how to achieve the recommended
formatting for set.mm prior to submitting your changes.

### Formatting recommendation prior to submitting a pull request

Periodically we rewrap set.mm to help conform to its formatting conventions.  This may affect your mathbox if you submitted it without rewrapping, possibly causing merge conflicts with your work in progress.

Here is the procedure recommended prior to submitting a pull request:

<PRE>
metamath
MM> read set.mm
MM> write source set.mm /rewrap
MM> erase
MM> read set.mm
MM> save proof */compressed/fast
MM> verify markup */file_skip
MM> verify proof *
MM> write source set.mm
MM> quit
</PRE>

This can also be done as a single command in bash:

<PRE>
./metamath 'read set.mm' 'write source set.mm /rewrap' \
   erase 'read set.mm' 'save proof */compressed/fast' \
   'verify markup */file_skip' 'verify proof *' \
   'write source set.mm' quit
</PRE>

The reason for doing /rewrap first is so that 'save proof' will adjust the proof indentation to match any indentation changes made by /rewrap.  'verify markup' will check that no lines became too long due to different indentation.  'verify proof' is there because you might as well.

(You can also check definitional soundness with mmj2 and any 'discouraged' markup changes before submission if you want, or you can just leave it up to Travis to check those.)
