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

The reason for doing /rewrap first is so that 'save proof' will subsequently adjust the proof indentation to match any indentation changes made by /rewrap.  'verify markup' will check that no lines became too long due to different indentation.  'verify proof' is there because you might as well.

(You can also check definitional soundness with mmj2 and any 'discouraged' markup changes before submission if you want, or you can just leave it up to Travis to check those.)


### Regenerating the `discouraged` file

Some statement descriptions in `set.mm` have one or both of the markup tags `(New usage is discouraged.)` and `(Proof modification is discouraged.)`  In order to monitor accidental violations of these tags in set.mm, we store the usage and proof lengths of statements with these tags set.mm in a file called `discouraged`.  The Travis check will return an error if this file doesn't exactly match the one that it generates for a set.mm pull request.

If you make modifications that affect the `discouraged` file, you should regenerate it with the following command under Linux or Cygwin bash:
<pre>
./metamath 'read set.mm' 'set width 9999' 'show discouraged' quit \
    | tr -d '\015' | grep '^SHOW DISCOURAGED.' \
    | sed -E -e 's/^SHOW DISCOURAGED.  ?//' | LC_ALL=C sort > discouraged
</pre>
or in one line, for ease of copypasting:
<pre>
./metamath 'read set.mm' 'set width 9999' 'show discouraged' quit | tr -d '\015' | grep '^SHOW DISCOURAGED.' | sed -E -e 's/^SHOW DISCOURAGED.  ?//' | LC_ALL=C sort > discouraged
</pre>

The "tr -d '\015'" is needed with Cygwin to strip carriage returns and has no effect in Linux.

The `discouraged` file can also be regenerated with mmj2, which currently runs faster than metamath.exe for this function.  See the Travis script for the details.


The metamath.exe and mmj2 proof assistants will prevent most accidental violations.  The behavior of the metamath.exe proof assistant in the presence of these tags and how to override them is described in the 11-May-2016 entry of http://us.metamath.org/mpeuni/mmnotes.txt.

Please note that when you regenerate the `discouraged` file, before comitting it you should compare it to the existing one to make sure the differences are what you expected and not accidental changes elsewhere.  The purpose of this file is to help detect such accidental changes, and if it isn't inspected manually that purpose is defeated.
