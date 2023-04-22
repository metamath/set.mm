$( miu.mm  20-Oct-2008 $)

$(

                           ~~ PUBLIC DOMAIN ~~
This work is waived of all rights, including copyright, according to the CC0
Public Domain Dedication.  http://creativecommons.org/publicdomain/zero/1.0/

Norman Megill

$)

$( The MIU-system:  A simple formal system $)

$( Note:  This formal system is unusual in that it allows empty wffs.
To work with a proof, you must type SET EMPTY_SUBSTITUTION ON before
using the PROVE command.  By default this is OFF in order to reduce the
number of ambiguous unification possibilities that have to be selected
during the construction of a proof.  $)

$(
Hofstadter's MIU-system is a simple example of a formal
system that illustrates some concepts of Metamath.  See
Douglas R. Hofstadter, "G\"{o}del, Escher, Bach:  An Eternal
Golden Braid" (Vintage Books, New York, 1979), pp. 33ff. for
a description of the MIU-system.

The system has 3 constant symbols, M, I, and U.  The sole
axiom of the system is MI. There are 4 rules:
     Rule I:  If you possess a string whose last letter is I,
     you can add on a U at the end.
     Rule II:  Suppose you have Mx.  Then you may add Mxx to
     your collection.
     Rule III:  If III occurs in one of the strings in your
     collection, you may make a new string with U in place
     of III.
     Rule IV:  If UU occurs inside one of your strings, you
     can drop it.

Note:  The following comment applied to an old version of the Metamath
spec that didn't require $f (variable type) hypotheses for variables and
is no longer applicable.  The current spec was made stricter primarily
to reduce the likelihood of inconsistent toy axiom systems, effectively
requiring the concept of an "MIU wff" anyway.  However, I am keeping the
comment for historical reasons, if only to point out an intrinsic
difference in Rules III and IV that might have relevance to other proof
systems.

  Old comment, obsolete:  "Unfortunately, Rules III and IV do not have
  unique results:  strings could have more than one occurrence of III or
  UU.  This requires that we introduce the concept of an "MIU well-formed
  formula" or wff, which allows us to construct unique symbol sequences to
  which Rules III and IV can be applied."

Under the old Metamath spec, the problem this caused was that without
the construction of specific wffs to substitute for their variables,
Rules III and IV would sometimes not have unique unifications (as
required by the spec) during a proof, making proofs more difficult or
even impossible.
$)

$( First, we declare the constant symbols of the language.
Note that we need two symbols to distinguish the assertion
that a sequence is a wff from the assertion that it is a
theorem; we have arbitrarily chosen "wff" and "|-". $)
      $c M I U |- wff $. $( Declare constants $)

$( Next, we declare some variables. $)
     $v x y $.

$( Throughout our theory, we shall assume that these
variables represent wffs. $)
 wx   $f wff x $.
 wy   $f wff y $.

$( Define MIU-wffs.  We allow the empty sequence to be a
wff. $)

 $( The empty sequence is a wff. $)
 we   $a wff $.
 $( "M" after any wff is a wff. $)
 wM   $a wff x M $.
 $( "I" after any wff is a wff. $)
 wI   $a wff x I $.
 $( "U" after any wff is a wff. $)
 wU   $a wff x U $.
 $( If "x" and "y" are wffs, so is "x y".  This allows the conclusion of
    ` IV ` to be provable as a wff before substitutions into it, for those
    parsers requiring it.  (Added per suggestion of Mel O'Cat 4-Dec-04.) $)
 wxy  $a wff x y $.

 $( Assert the axiom. $)
 ax   $a |- M I $.

 $( Assert the rules. $)
 ${
   Ia   $e |- x I $.
   $( Given any theorem ending with "I", it remains a theorem
      if "U" is added after it.  (We distinguish the label I_
      from the math symbol I to conform to the 24-Jun-2006
      Metamath spec change.) $)
   I_    $a |- x I U $.
 $}

 ${
   IIa  $e |- M x $.
   $( Given any theorem starting with "M", it remains a theorem
      if the part after the "M" is added again after it. $)
   II   $a |- M x x $.
 $}

 ${
   IIIa $e |- x I I I y $.
   $( Given any theorem with "III" in the middle, it remains a
      theorem if the "III" is replace with "U". $)
   III  $a |- x U y $.
 $}

 ${
   IVa  $e |- x U U y $.
   $( Given any theorem with "UU" in the middle, it remains a
      theorem if the "UU" is deleted. $)
   IV   $a |- x y $.
 $}

 $( Now we prove the theorem MUIIU.  You may be interested in
    comparing this proof with that of Hofstadter (pp. 35 - 36). $)
 theorem1  $p |- M U I I U $=
      we wM wU wI we wI wU we wU wI wU we wM we wI wU we wM
      wI wI wI we wI wI we wI ax II II I_ III II IV $.
