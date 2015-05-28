$c set  A. = e.  E. $.
$v x y z w u v t $.

$( -*-text-*- $)

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
                           Pre-logic
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

  $( Declare the primitive constant symbols for propositional calculus. $)
  $c ( $.  $( Left parenthesis $)
  $c ) $.  $( Right parenthesis $)
  $c -> $. $( Right arrow (read:  "implies") $)
  $c -. $. $( Right handle (read:  "not") $)
  $c wff $. $( Well-formed formula symbol (read:  "the following symbol
               sequence is a wff") $)
  $c |- $. $( Turnstile (read:  "the following symbol sequence is provable" or
              'a proof exists for") $)

  $( Introduce some variable names we will use to represent well-formed
     formulas (wff's). $)
  $v ph $. $( Greek phi $)
  $v ps $.  $( Greek psi $)
  $v ch $.  $( Greek chi $)
  $v th $.  $( Greek theta $)
  $v ta $.  $( Greek tau $)

  $( Specify some variables that we will use to represent wff's.
     The fact that a variable represents a wff is relevant only to a theorem
     referring to that variable, so we may use $f hypotheses.  The symbol
     ` wff ` specifies that the variable that follows it represents a wff. $)
  $( Let variable ` ph ` be a wff. $)
  wph $f wff ph $.
  $( Let variable ` ps ` be a wff. $)
  wps $f wff ps $.
  $( Let variable ` ch ` be a wff. $)
  wch $f wff ch $.
  $( Let variable ` th ` be a wff. $)
  wth $f wff th $.
  $( Let variable ` ta ` be a wff. $)
  wta $f wff ta $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
          Dummy link theorem for assisting proof development
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    dummylink.1 $e |- ph $.
    dummylink.2 $e |- ps $.
    $( (_Note_:  This theorem will never appear in a completed proof and can be
       ignored if you are using this database to learn logic - please start
       with the next statement, ~ wn .)

       This is a technical theorem to assist proof development.  It provides a
       temporary way to add an independent subproof to a proof under
       development, for later assignment to a normal proof step.

       The Metamath program's Proof Assistant requires proofs to be developed
       backwards from the conclusion with no gaps, and it has no mechanism that
       lets the user to work on isolated subproofs.  This theorem provides a
       workaround for this limitation.  It can be inserted at any point in a
       proof to allow an independent subproof to be developed on the side, for
       later use as part of the final proof.

       _Instructions_:  (1) Assign this theorem to any unknown step in the
       proof.  Typically, the last unknown step is the most convenient, since
       'assign last' can be used.  This step will be replicated in hypothesis
       dummylink.1, from where the development of the main proof can continue.
       (2) Develop the independent subproof backwards from hypothesis
       dummylink.2.  If desired, use a 'let' command to pre-assign the
       conclusion of the independent subproof to dummylink.2.  (3) After the
       independent subproof is complete, use 'improve all' to assign it
       automatically to an unknown step in the main proof that matches it.
       (4) After the entire proof is complete, use
       'minimize */n/b/e 3syl,we?,wsb' to clean up (discard) all dummylink
       references automatically.

       This theorem was originally designed to assist importing partially
       completed Proof Worksheets from Mel O'Cat's mmj2 Proof Assistant GUI,
       but it can also be useful on its own.  Interestingly, this "theorem" -
       or more precisely, inference - requires no axioms for its proof. $)
    dummylink $p |- ph $=
      (  ) C $.
      $( [8-Feb-2006] $) $( [7-Feb-2006] $)
  $}

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
                           Propositional calculus
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Recursively define primitive wffs for propositional calculus
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( If ` ph ` is a wff, so is ` -. ph ` or "not ` ph ` ."  Part of the
     recursive definition of a wff (well-formed formula).  In classical logic
     (which is our logic), a wff is interpreted as either true or false.
     So if ` ph ` is true, then ` -. ph ` is false; if ` ph ` is false, then
     ` -. ph ` is true.  Traditionally, Greek letters are used to represent
     wffs, and we follow this convention.  In propositional calculus, we define
     only wffs built up from other wffs, i.e. there is no starting or "atomic"
     wff.  Later, in predicate calculus, we will extend the basic wff
     definition by including atomic wffs ( ~ weq and ~ wel ). $)
  wn $a wff -. ph $.

  $( If ` ph ` and ` ps ` are wff's, so is ` ( ph -> ps ) ` or " ` ph ` implies
     ` ps ` ."  Part of the recursive definition of a wff.  The resulting wff
     is (interpreted as) false when ` ph ` is true and ` ps ` is false; it is
     true otherwise.  (Think of the truth table for an OR gate with input
     ` ph ` connected through an inverter.)  The left-hand wff is called the
     antecedent, and the right-hand wff is called the consequent.  In the case
     of ` ( ph -> ( ps -> ch ) ) ` , the middle ` ps ` may be informally called
     either an antecedent or part of the consequent depending on context. $)
  wi $a wff ( ph -> ps ) $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        The axioms of propositional calculus
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $(
     Postulate the three axioms of classical propositional calculus.
  $)

  $( Axiom _Simp_.  Axiom A1 of [Margaris] p. 49.  One of the 3 axioms of
     propositional calculus.  The 3 axioms are also given as Definition 2.1
     of [Hamilton] p. 28.  This axiom is called _Simp_ or "the principle of
     simplification" in _Principia Mathematica_ (Theorem *2.02 of
     [WhiteheadRussell] p. 100) because "it enables us to pass from the joint
     assertion of ` ph ` and ` ps ` to the assertion of ` ph ` simply."

     _General remarks_:  Propositional calculus (axioms ~ ax-1 through ~ ax-3
     and rule ~ ax-mp ) can be thought of as asserting formulas that are
     universally "true" when their variables are replaced by any combination
     of "true" and "false."  Propositional calculus was first formalized by
     Frege in 1879, using as his axioms (in addition to rule ~ ax-mp ) the
     wffs ~ ax-1 , ~ ax-2 , ~ pm2.04 , ~ con3 , ~ notnot2 , and ~ notnot1 .
     Around 1930, Lukasiewicz simplified the system by eliminating the third
     (which follows from the first two, as you can see by looking at the proof
     of ~ pm2.04 ) and replacing the last three with our ~ ax-3 .  (Thanks to
     Ted Ulrich for this information.)

     The theorems of propositional calculus are also called _tautologies_.
     Tautologies can be proved very simply using truth tables, based on the
     true/false interpretation of propositional calculus.  To do this, we
     assign all possible combinations of true and false to the wff variables
     and verify that the result (using the rules described in ~ wi and ~ wn )
     always evaluates to true.  This is called the _semantic_ approach.  Our
     approach is called the _syntactic_ approach, in which everything is
     derived from axioms.  A metatheorem called the Completeness Theorem for
     Propositional Calculus shows that the two approaches are equivalent and
     even provides an algorithm for automatically generating syntactic proofs
     from a truth table.  Those proofs, however, tend to be long, and the
     much shorter proofs that we show here were found manually.  Truth tables
     grow exponentially with the number of variables, but it is unknown if the
     same is true of proofs - an answer to this would resolve the P=NP
     conjecture in complexity theory. $)
  ax-1 $a |- ( ph -> ( ps -> ph ) ) $.
  $( [ ?] $) $( [ ?] $)

  $( Axiom _Frege_.  Axiom A2 of [Margaris] p. 49.  One of the 3 axioms of
     propositional calculus.  It "distributes" an antecedent over two
     consequents.  This axiom was part of Frege's original system and is known
     as _Frege_ in the literature.  It is also proved as Theorem *2.77 of
     [WhiteheadRussell] p. 108.  The other direction of this axiom also
     turns out to be true, as demonstrated by ~ pm5.41 . $)
  ax-2 $a |- ( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) ) ) $.

  $( Axiom _Transp_.  Axiom A3 of [Margaris] p. 49.  One of the 3 axioms of
     propositional calculus.  It swaps or "transposes" the order of the
     consequents when negation is removed.  An informal example is that the
     statement "if there are no clouds in the sky, it is not raining" implies
     the statement "if it is raining, there are clouds in the sky."  This
     axiom is called _Transp_ or "the principle of transposition" in
     _Principia Mathematica_ (Theorem *2.17 of [WhiteheadRussell] p. 103).
     We will also use the term "contraposition" for this principle, although
     the reader is advised that in the field of philosophical logic,
     "contraposition" has a different technical meaning. $)
  ax-3 $a |- ( ( -. ph -> -. ps ) -> ( ps -> ph ) ) $.

  $(
     Postulate the modus ponens rule of inference.
  $)

  ${
    $( Minor premise for modus ponens. $)
    min $e |- ph $.
    $( Major premise for modus ponens. $)
    maj $e |- ( ph -> ps ) $.
    $( Rule of Modus Ponens.  The postulated inference rule of propositional
       calculus.  See e.g. Rule 1 of [Hamilton] p. 73.  The rule says, "if
       ` ph ` is true, and ` ph ` implies ` ps ` , then ` ps ` must also be
       true."  This rule is sometimes called "detachment," since it detaches
       the minor premise from the major premise.

       Note:  In some web page displays such as the Statement List, the symbols
       "&" and "=>" informally indicate the relationship between the hypotheses
       and the assertion (conclusion), abbreviating the English words "and" and
       "implies."  They are not part of the formal language. $)
    ax-mp $a |- ps $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Logical implication
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$( The results in this section make use of the first 2 axioms only.  In
   an implication, the wff before the arrow is called the "antecedent"
   and the wff after the arrow is called the "consequent." $)

$( We will use the following descriptive terms very loosely:  A "theorem"
   usually has no $e hypotheses.  An "inference" has one or more $e hypotheses.
   A "deduction" is an inference in which the hypotheses and the result
   share the same antecedent. $)

  ${
    $( Premise for ~ a1i . $)
    a1i.1 $e |- ph $.
    $( Inference derived from axiom ~ ax-1 .  See ~ a1d for an explanation of
       our informal use of the terms "inference" and "deduction."  See also
       the comment in ~ syld . $)
    a1i $p |- ( ps -> ph ) $=
      ( wi ax-1 ax-mp ) ABADCABEF $.
      $( [5-Aug-1993] $)
  $}

  ${
    a1i12.1 $e |- ch $.
    $( Add two antecedents to a wff.  (Contributed by Jeff Hankins,
       4-Aug-2009.) $)
    a1i12 $p |- ( ph -> ( ps -> ch ) ) $=
      ( wi a1i ) BCEACBDFF $.
      $( [18-Apr-2010] $) $( [4-Aug-2009] $)
  $}

  ${
    $( Premise for ~ a2i . $)
    a2i.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Inference derived from axiom ~ ax-2 . $)
    a2i $p |- ( ( ph -> ps ) -> ( ph -> ch ) ) $=
      ( wi ax-2 ax-mp ) ABCEEABEACEEDABCFG $.
      $( [5-Aug-1993] $)
  $}

  ${
    $( First of 2 premises for ~ syl . $)
    syl.1 $e |- ( ph -> ps ) $.
    $( Second of 2 premises for ~ syl . $)
    syl.2 $e |- ( ps -> ch ) $.
    $( An inference version of the transitive laws for implication ~ imim2 and
       ~ imim1 , which Russell and Whitehead call "the principle of the
       syllogism...because...the syllogism in Barbara is derived from them"
       (quote after Theorem *2.06 of [WhiteheadRussell] p. 101).  Some authors
       call this law a "hypothetical syllogism."

       (A bit of trivia:  this is the most commonly referenced assertion in our
       database.  In second place is ~ ax-mp , followed by ~ visset , ~ bitri ,
       ~ imp , and ~ ex .  The Metamath program command 'show usage' shows the
       number of references.) $)
    syl $p |- ( ph -> ch ) $=
      ( wi a1i a2i ax-mp ) ABFACFDABCBCFAEGHI $.
      $( [5-Aug-1993] $)
  $}

  ${
    $( Premise for ~ com12 .  See ~ pm2.04 for the theorem form. $)
    com12.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Inference that swaps (commutes) antecedents in an implication. $)
    com12 $p |- ( ps -> ( ph -> ch ) ) $=
      ( wi ax-1 a2i syl ) BABEACEBAFABCDGH $.
      $( [5-Aug-1993] $)
  $}

  ${
    a1d.1 $e |- ( ph -> ps ) $.
    $( Deduction introducing an embedded antecedent.  (The proof was revised by
       Stefan Allan, 20-Mar-2006.)

       _Naming convention_:  We often call a theorem a "deduction" and suffix
       its label with "d" whenever the hypotheses and conclusion are each
       prefixed with the same antecedent.  This allows us to use the theorem in
       places where (in traditional textbook formalizations) the standard
       Deduction Theorem would be used; here ` ph ` would be replaced with a
       conjunction ( ~ df-an ) of the hypotheses of the would-be deduction.  By
       contrast, we tend to call the simpler version with no common antecedent
       an "inference" and suffix its label with "i"; compare theorem ~ a1i .
       Finally, a "theorem" would be the form with no hypotheses; in this case
       the "theorem" form would be the original axiom ~ ax-1 .  We usually show
       the theorem form without a suffix on its label (e.g. ~ pm2.43 vs.
       ~ pm2.43i vs. ~ pm2.43d ).  When an inference is converted to a theorem
       by eliminating an "is a set" hypothesis, we sometimes suffix the theorem
       form with "g" (for "more general") as in ~ uniex vs. ~ uniexg . $)
    a1d $p |- ( ph -> ( ch -> ps ) ) $=
      ( wi ax-1 syl ) ABCBEDBCFG $.
      $( [20-Mar-2006] $) $( [5-Aug-1993] $)
  $}

  ${
    a2d.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    $( Deduction distributing an embedded antecedent. $)
    a2d $p |- ( ph -> ( ( ps -> ch ) -> ( ps -> th ) ) ) $=
      ( wi ax-2 syl ) ABCDFFBCFBDFFEBCDGH $.
      $( [23-Jun-1994] $)
  $}

  $( A closed form of syllogism (see ~ syl ).  Theorem *2.05 of
     [WhiteheadRussell] p. 100. $)
  imim2 $p |- ( ( ph -> ps ) -> ( ( ch -> ph ) -> ( ch -> ps ) ) ) $=
    ( wi ax-1 a2d ) ABDZCABGCEF $.
    $( [5-Aug-1993] $)

  $( A closed form of syllogism (see ~ syl ).  Theorem *2.06 of
     [WhiteheadRussell] p. 100. $)
  imim1 $p |- ( ( ph -> ps ) -> ( ( ps -> ch ) -> ( ph -> ch ) ) ) $=
    ( wi imim2 com12 ) BCDABDACDBCAEF $.
    $( [5-Aug-1993] $)

  ${
    imim1i.1 $e |- ( ph -> ps ) $.
    $( Inference adding common consequents in an implication, thereby
       interchanging the original antecedent and consequent. $)
    imim1i $p |- ( ( ps -> ch ) -> ( ph -> ch ) ) $=
      ( wi imim1 ax-mp ) ABEBCEACEEDABCFG $.
      $( [5-Aug-1993] $)

    $( Inference adding common antecedents in an implication. $)
    imim2i $p |- ( ( ch -> ph ) -> ( ch -> ps ) ) $=
      ( wi a1i a2i ) CABABECDFG $.
      $( [5-Aug-1993] $)
  $}

  ${
    imim12i.1 $e |- ( ph -> ps ) $.
    imim12i.2 $e |- ( ch -> th ) $.
    $( Inference joining two implications. $)
    imim12i $p |- ( ( ps -> ch ) -> ( ph -> th ) ) $=
      ( wi imim2i imim1i syl ) BCGBDGADGCDBFHABDEIJ $.
      $( [5-Aug-1993] $)
  $}

  ${
    imim3i.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Inference adding three nested antecedents. $)
    imim3i $p |- ( ( th -> ph ) -> ( ( th -> ps ) -> ( th -> ch ) ) ) $=
      ( wi imim2i a2d ) DAFDBCABCFDEGH $.
      $( [19-Dec-2006] $) $( [19-Dec-2006] $)
  $}

  ${
    3syl.1 $e |- ( ph -> ps ) $.
    3syl.2 $e |- ( ps -> ch ) $.
    3syl.3 $e |- ( ch -> th ) $.
    $( Inference chaining two syllogisms. $)
    3syl $p |- ( ph -> th ) $=
      ( syl ) ACDABCEFHGH $.
      $( [5-Aug-1993] $)
  $}

  ${
    syl5.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syl5.2 $e |- ( th -> ps ) $.
    $( A syllogism rule of inference.  The second premise is used to replace
       the second antecedent of the first premise. $)
    syl5 $p |- ( ph -> ( th -> ch ) ) $=
      ( wi imim1i syl ) ABCGDCGEDBCFHI $.
      $( [5-Aug-1993] $)
  $}

  ${
    syl6.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syl6.2 $e |- ( ch -> th ) $.
    $( A syllogism rule of inference.  The second premise is used to replace
       the consequent of the first premise. $)
    syl6 $p |- ( ph -> ( ps -> th ) ) $=
      ( wi imim2i syl ) ABCGBDGECDBFHI $.
      $( [5-Aug-1993] $)
  $}

  ${
    syl7.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    syl7.2 $e |- ( ta -> ch ) $.
    $( A syllogism rule of inference.  The second premise is used to replace
       the third antecedent of the first premise. $)
    syl7 $p |- ( ph -> ( ps -> ( ta -> th ) ) ) $=
      ( wi imim1i syl6 ) ABCDHEDHFECDGIJ $.
      $( [5-Aug-1993] $)
  $}

  ${
    syl8.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    syl8.2 $e |- ( th -> ta ) $.
    $( A syllogism rule of inference.  The second premise is used to replace
       the consequent of the first premise. $)
    syl8 $p |- ( ph -> ( ps -> ( ch -> ta ) ) ) $=
      ( wi imim2i syl6 ) ABCDHCEHFDECGIJ $.
      $( [1-Aug-1994] $)
  $}

  ${
    imim2d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction adding nested antecedents. $)
    imim2d $p |- ( ph -> ( ( th -> ps ) -> ( th -> ch ) ) ) $=
      ( wi a1d a2d ) ADBCABCFDEGH $.
      $( [5-Aug-1993] $)
  $}

  ${
    mpd.1 $e |- ( ph -> ps ) $.
    mpd.2 $e |- ( ph -> ( ps -> ch ) ) $.
    $( A modus ponens deduction. $)
    mpd $p |- ( ph -> ch ) $=
      ( wi a2i ax-mp ) ABFACFDABCEGH $.
      $( [5-Aug-1993] $)
  $}

  ${
    syld.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syld.2 $e |- ( ph -> ( ch -> th ) ) $.
    $( Syllogism deduction.  (The proof was shortened by O'Cat, 19-Feb-2008.)

       Notice that ~ syld can be obtained from ~ syl by replacing each
       hypothesis and conclusion ` ta ` by ` ( ph -> ta ) ` .  In general, this
       process will always yield a new propositional calculus theorem because
       of something called the Deduction Theorem for propositional calculus. $)
    syld $p |- ( ph -> ( ps -> th ) ) $=
      ( wi imim2d mpd ) ABCGBDGEACDBFHI $.
      $( [19-Feb-2008] $) $( [5-Aug-1993] $)
  $}

  ${
    3syld.1 $e |- ( ph -> ( ps -> ch ) ) $.
    3syld.2 $e |- ( ph -> ( ch -> th ) ) $.
    3syld.3 $e |- ( ph -> ( th -> ta ) ) $.
    $( Triple syllogism deduction.  (Contributed by Jeff Hankins,
       4-Aug-2009.) $)
    3syld $p |- ( ph -> ( ps -> ta ) ) $=
      ( syld ) ABDEABCDFGIHI $.
      $( [24-Sep-2010] $) $( [4-Aug-2009] $)
  $}

  ${
    imim1d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction adding nested consequents. $)
    imim1d $p |- ( ph -> ( ( ch -> th ) -> ( ps -> th ) ) ) $=
      ( wi imim1 syl ) ABCFCDFBDFFEBCDGH $.
      $( [3-Apr-1994] $)
  $}

  ${
    imim12d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    imim12d.2 $e |- ( ph -> ( th -> ta ) ) $.
    $( Deduction combining antecedents and consequents. $)
    imim12d $p |- ( ph -> ( ( ch -> th ) -> ( ps -> ta ) ) ) $=
      ( wi imim1d imim2d syld ) ACDHBDHBEHABCDFIADEBGJK $.
      $( [7-Aug-1994] $)
  $}

  $( Swap antecedents.  Theorem *2.04 of [WhiteheadRussell] p. 100. $)
  pm2.04 $p |- ( ( ph -> ( ps -> ch ) ) -> ( ps -> ( ph -> ch ) ) ) $=
    ( wi ax-2 ax-1 syl5 ) ABCDDABDACDBABCEBAFG $.
    $( [5-Aug-1993] $)

  $( Theorem *2.83 of [WhiteheadRussell] p. 108. $)
  pm2.83 $p |-  ( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ( ch -> th ) ) ->
                ( ph -> ( ps -> th ) ) ) ) $=
    ( wi imim1 imim3i ) BCECDEBDEABCDFG $.
    $( [13-Jan-2005] $) $( [3-Jan-2005] $)

  ${
    com3.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    $( Commutation of antecedents.  Swap 2nd and 3rd. $)
    com23 $p |- ( ph -> ( ch -> ( ps -> th ) ) ) $=
      ( wi pm2.04 syl ) ABCDFFCBDFFEBCDGH $.
      $( [5-Aug-1993] $)

    $( Commutation of antecedents.  Swap 1st and 3rd. $)
    com13 $p |- ( ch -> ( ps -> ( ph -> th ) ) ) $=
      ( wi com12 com23 ) BCADFBACDABCDFEGHG $.
      $( [25-Apr-1994] $)

    $( Commutation of antecedents.  Rotate left. $)
    com3l $p |- ( ps -> ( ch -> ( ph -> th ) ) ) $=
      ( com23 com13 ) ACBDABCDEFG $.
      $( [25-Apr-1994] $)

    $( Commutation of antecedents.  Rotate right. $)
    com3r $p |- ( ch -> ( ph -> ( ps -> th ) ) ) $=
      ( com3l ) BCADABCDEFF $.
      $( [25-Apr-1994] $)
  $}

  ${
    com4.1 $e |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $.
    $( Commutation of antecedents.  Swap 3rd and 4th. $)
    com34 $p |- ( ph -> ( ps -> ( th -> ( ch -> ta ) ) ) ) $=
      ( wi pm2.04 syl6 ) ABCDEGGDCEGGFCDEHI $.
      $( [25-Apr-1994] $)

    $( Commutation of antecedents.  Swap 2nd and 4th. $)
    com24 $p |- ( ph -> ( th -> ( ch -> ( ps -> ta ) ) ) ) $=
      ( wi com34 com23 ) ADBCEABDCEGABCDEFHIH $.
      $( [25-Apr-1994] $)

    $( Commutation of antecedents.  Swap 1st and 4th. $)
    com14 $p |- ( th -> ( ps -> ( ch -> ( ph -> ta ) ) ) ) $=
      ( wi com34 com13 ) DBACEABDCEGABCDEFHIH $.
      $( [25-Apr-1994] $)

    $( Commutation of antecedents.  Rotate left.  (The proof was shortened by
       O'Cat, 15-Aug-2004.) $)
    com4l $p |- ( ps -> ( ch -> ( th -> ( ph -> ta ) ) ) ) $=
      ( wi com14 com3l ) DBCAEGABCDEFHI $.
      $( [15-Aug-2004] $) $( [25-Apr-1994] $)

    $( Commutation of antecedents.  Rotate twice. $)
    com4t $p |- ( ch -> ( th -> ( ph -> ( ps -> ta ) ) ) ) $=
      ( com4l ) BCDAEABCDEFGG $.
      $( [25-Apr-1994] $)

    $( Commutation of antecedents.  Rotate right. $)
    com4r $p |- ( th -> ( ph -> ( ps -> ( ch -> ta ) ) ) ) $=
      ( com4t com4l ) CDABEABCDEFGH $.
      $( [25-Apr-1994] $)
  $}

  ${
    $v et $.
    com5.et $f wff et $.
    com5.1 $e |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $.
    $( Commutation of antecedents.  Swap 4th and 5th.  (Contributed by Jeff
       Hankins, 28-Jun-2009.) $)
    com45 $p |- ( ph -> ( ps -> ( ch -> ( ta -> ( th -> et ) ) ) ) ) $=
      ( wi pm2.04 syl8 ) ABCDEFHHEDFHHGDEFIJ $.
      $( [18-Apr-2010] $) $( [28-Jun-2009] $)

    $( Commutation of antecedents.  Swap 3rd and 5th.  (Contributed by Jeff
       Hankins, 28-Jun-2009.) $)
    com35 $p |- ( ph -> ( ps -> ( ta -> ( th -> ( ch -> et ) ) ) ) ) $=
      ( wi com34 com45 ) ABDECFHABDCEFABCDEFHGIJI $.
      $( [18-Apr-2010] $) $( [28-Jun-2009] $)

    $( Commutation of antecedents.  Swap 2nd and 5th.  (Contributed by Jeff
       Hankins, 28-Jun-2009.) $)
    com25 $p |- ( ph -> ( ta -> ( ch -> ( th -> ( ps -> et ) ) ) ) ) $=
      ( wi com24 com45 ) ADCEBFHADCBEFABCDEFHGIJI $.
      $( [18-Apr-2010] $) $( [28-Jun-2009] $)

    $( Commutation of antecedents.  Swap 1st and 5th.  (Contributed by Jeff
       Hankins, 28-Jun-2009.) $)
    com15 $p |- ( ta -> ( ps -> ( ch -> ( th -> ( ph -> et ) ) ) ) ) $=
      ( wi com14 com45 ) DBCEAFHDBCAEFABCDEFHGIJI $.
      $( [18-Apr-2010] $) $( [28-Jun-2009] $)

    $( Commutation of antecedents.  Rotate left.  (Contributed by Jeff
       Hankins, 28-Jun-2009.) $)
    com5l $p |- ( ps -> ( ch -> ( th -> ( ta -> ( ph -> et ) ) ) ) ) $=
      ( com45 com35 com25 com15 ) ACDEBFABDECFABCEDFABCDEFGHIJK $.
      $( [18-Apr-2010] $) $( [28-Jun-2009] $)

    $( Commutation of antecedents.  Rotate left twice.  (Contributed by Jeff
       Hankins, 28-Jun-2009.) $)
    com52l $p |- ( ch -> ( th -> ( ta -> ( ph -> ( ps -> et ) ) ) ) ) $=
      ( com5l ) BCDEAFABCDEFGHH $.
      $( [18-Apr-2010] $) $( [28-Jun-2009] $)

    $( Commutation of antecedents.  Rotate right twice.  (Contributed by Jeff
       Hankins, 28-Jun-2009.) $)
    com52r $p |- ( th -> ( ta -> ( ph -> ( ps -> ( ch -> et ) ) ) ) ) $=
      ( com52l com5l ) CDEABFABCDEFGHI $.
      $( [18-Apr-2010] $) $( [28-Jun-2009] $)
  $}

  ${
    a1dd.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction introducing a nested embedded antecedent.  (The proof was
       shortened by O'Cat, 15-Jan-2008.) $)
    a1dd $p |- ( ph -> ( ps -> ( th -> ch ) ) ) $=
      ( wi ax-1 syl6 ) ABCDCFECDGH $.
      $( [15-Jan-2008] $) $( [17-Dec-2004] $)
  $}

  ${
    mp2.1 $e |- ph $.
    mp2.2 $e |- ps $.
    mp2.3 $e |- ( ph -> ( ps -> ch ) ) $.
    $( A double modus ponens inference. $)
    mp2 $p |- ch $=
      ( wi ax-mp ) BCEABCGDFHH $.
      $( [5-Apr-1994] $)
  $}

  ${
    mpi.1 $e |- ps $.
    mpi.2 $e |- ( ph -> ( ps -> ch ) ) $.
    $( A nested modus ponens inference.  (The proof was shortened by Stefan
       Allan, 20-Mar-2006.) $)
    mpi $p |- ( ph -> ch ) $=
      ( a1i mpd ) ABCBADFEG $.
      $( [20-Mar-2006] $) $( [5-Aug-1993] $)
  $}

  ${
    mpii.1 $e |- ch $.
    mpii.2 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    $( A doubly nested modus ponens inference. $)
    mpii $p |- ( ph -> ( ps -> th ) ) $=
      ( wi com23 mpi ) ACBDGEABCDFHI $.
      $( [31-Dec-1993] $)
  $}

  ${
    mpdd.1 $e |- ( ph -> ( ps -> ch ) ) $.
    mpdd.2 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    $( A nested modus ponens deduction. $)
    mpdd $p |- ( ph -> ( ps -> th ) ) $=
      ( wi a2d mpd ) ABCGBDGEABCDFHI $.
      $( [13-Dec-2004] $) $( [12-Dec-2004] $)
  $}

  ${
    mpid.1 $e |- ( ph -> ch ) $.
    mpid.2 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    $( A nested modus ponens deduction. $)
    mpid $p |- ( ph -> ( ps -> th ) ) $=
      ( a1d mpdd ) ABCDACBEGFH $.
      $( [16-Dec-2004] $) $( [14-Dec-2004] $)
  $}

  ${
    mpdi.1 $e |- ( ps -> ch ) $.
    mpdi.2 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    $( A nested modus ponens deduction.  (The proof was shortened by O'Cat,
       15-Jan-2008.) $)
    mpdi $p |- ( ph -> ( ps -> th ) ) $=
      ( wi a1i mpdd ) ABCDBCGAEHFI $.
      $( [15-Jan-2008] $) $( [16-Apr-2005] $)
  $}

  ${
    mpcom.1 $e |- ( ps -> ph ) $.
    mpcom.2 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Modus ponens inference with commutation of antecedents. $)
    mpcom $p |- ( ps -> ch ) $=
      ( com12 mpd ) BACDABCEFG $.
      $( [17-Mar-1996] $)
  $}

  ${
    syldd.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    syldd.2 $e |- ( ph -> ( ps -> ( th -> ta ) ) ) $.
    $( Nested syllogism deduction. $)
    syldd $p |- ( ph -> ( ps -> ( ch -> ta ) ) ) $=
      ( wi imim2 syl6 mpdd ) ABCDHZCEHZFABDEHLMHGDECIJK $.
      $( [13-Dec-2004] $) $( [12-Dec-2004] $)
  $}

  ${
    sylcom.1 $e |- ( ph -> ( ps -> ch ) ) $.
    sylcom.2 $e |- ( ps -> ( ch -> th ) ) $.
    $( Syllogism inference with commutation of antecedents.  (The proof was
       shortened by O'Cat, 2-Feb-2006 and shortened further by Stefan Allan,
       23-Feb-2006.) $)
    sylcom $p |- ( ph -> ( ps -> th ) ) $=
      ( wi a2i syl ) ABCGBDGEBCDFHI $.
      $( [24-Feb-2006] $) $( [29-Aug-2004] $)
  $}

  ${
    syl5com.2 $e |- ( ph -> ( ps -> ch ) ) $.
    syl5com.1 $e |- ( th -> ps ) $.
    $( Syllogism inference with commuted antecedents. $)
    syl5com $p |- ( th -> ( ph -> ch ) ) $=
      ( a1d sylcom ) DABCDBAFGEH $.
      $( [25-May-2005] $) $( [24-May-2005] $)
  $}

  ${
    syl6com.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syl6com.2 $e |- ( ch -> th ) $.
    $( Syllogism inference with commuted antecedents. $)
    syl6com $p |- ( ps -> ( ph -> th ) ) $=
      ( syl6 com12 ) ABDABCDEFGH $.
      $( [26-May-2005] $) $( [25-May-2005] $)
  $}

  ${
    syli.1 $e |- ( ps -> ( ph -> ch ) ) $.
    syli.2 $e |- ( ch -> ( ph -> th ) ) $.
    $( Syllogism inference with common nested antecedent. $)
    syli $p |- ( ps -> ( ph -> th ) ) $=
      ( com12 sylcom ) BACDECADFGH $.
      $( [5-Nov-2004] $) $( [4-Nov-2004] $)
  $}

  ${
    syl5d.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    syl5d.2 $e |- ( ph -> ( ta -> ch ) ) $.
    $( A nested syllogism deduction.  (The proof was shortened by Josh
       Purinton, 29-Dec-2000 and shortened further by O'Cat, 2-Feb-2006.) $)
    syl5d $p |- ( ph -> ( ps -> ( ta -> th ) ) ) $=
      ( wi a1d syldd ) ABECDAECHBGIFJ $.
      $( [3-Feb-2006] $) $( [5-Aug-1993] $)
  $}

  ${
    syl6d.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    syl6d.2 $e |- ( ph -> ( th -> ta ) ) $.
    $( A nested syllogism deduction.  (The proof was shortened by Josh
       Purinton, 29-Dec-2000 and shortened further by O'Cat, 2-Feb-2006.) $)
    syl6d $p |- ( ph -> ( ps -> ( ch -> ta ) ) ) $=
      ( wi a1d syldd ) ABCDEFADEHBGIJ $.
      $( [3-Feb-2006] $) $( [5-Aug-1993] $)
  $}

  ${
    syl9.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syl9.2 $e |- ( th -> ( ch -> ta ) ) $.
    $( A nested syllogism inference with different antecedents.  (The proof
       was shortened by Josh Purinton, 29-Dec-2000.) $)
    syl9 $p |- ( ph -> ( th -> ( ps -> ta ) ) ) $=
      ( wi a1i syl5d ) ADCEBDCEHHAGIFJ $.
      $( [5-Aug-1993] $)
  $}

  ${
    syl9r.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syl9r.2 $e |- ( th -> ( ch -> ta ) ) $.
    $( A nested syllogism inference with different antecedents. $)
    syl9r $p |- ( th -> ( ph -> ( ps -> ta ) ) ) $=
      ( wi syl9 com12 ) ADBEHABCDEFGIJ $.
      $( [5-Aug-1993] $)
  $}

  $( Principle of identity.  Theorem *2.08 of [WhiteheadRussell] p. 101.
     For another version of the proof directly from axioms, see ~ id1 .
     (The proof was shortened by Stefan Allan, 20-Mar-2006.) $)
  id $p |- ( ph -> ph ) $=
    ( wi ax-1 mpd ) AAABZAAACAECD $.
    $( [20-Mar-2006] $) $( [20-Mar-2006] $)

  $( Principle of identity.  Theorem *2.08 of [WhiteheadRussell] p. 101.  This
     version is proved directly from the axioms for demonstration purposes.
     This proof is a popular example in the literature and is identical,
     step for step, to the proofs of Theorem 1 of [Margaris] p. 51,
     Example 2.7(a) of [Hamilton] p. 31, Lemma 10.3 of [BellMachover] p. 36,
     and Lemma 1.8 of [Mendelson] p. 36.  It is also
     "Our first proof" in Hirst and Hirst's _A Primer for Logic and Proof_
     p. 16 (PDF p. 22) at
     ~ http://www.mathsci.appstate.edu/~~jlh/primer/hirst.pdf .
     For a shorter version of the proof that takes advantage of previously
     proved theorems, see ~ id . $)
  id1 $p |- ( ph -> ph ) $=
    ( wi ax-1 ax-2 ax-mp ) AAABZBZFAACAFABBGFBAFCAFADEE $.
    $( [5-Aug-1993] $)

  $( Principle of identity with antecedent. $)
  idd $p |- ( ph -> ( ps -> ps ) ) $=
    ( wi id a1i ) BBCABDE $.
    $( [26-Nov-1995] $)

  $( This theorem, called "Assertion," can be thought of as closed form of
     modus ponens ~ ax-mp .  Theorem *2.27 of [WhiteheadRussell] p. 104. $)
  pm2.27 $p |- ( ph -> ( ( ph -> ps ) -> ps ) ) $=
    ( wi id com12 ) ABCZABFDE $.
    $( [5-Aug-1993] $)

  $( Absorption of redundant antecedent.  Also called the "Contraction" or
     "Hilbert" axiom.  Theorem *2.43 of [WhiteheadRussell] p. 106.  (The proof
     was shortened by O'Cat, 15-Aug-2004.) $)
  pm2.43 $p |- ( ( ph -> ( ph -> ps ) ) -> ( ph -> ps ) ) $=
    ( wi pm2.27 a2i ) AABCBABDE $.
    $( [15-Aug-2004] $) $( [5-Aug-1993] $)

  ${
    pm2.43i.1 $e |- ( ph -> ( ph -> ps ) ) $.
    $( Inference absorbing redundant antecedent.  (The proof was shortened by
       O'Cat, 28-Nov-2008.) $)
    pm2.43i $p |- ( ph -> ps ) $=
      ( id mpd ) AABADCE $.
      $( [29-Nov-2008] $) $( [5-Aug-1993] $)
  $}

  ${
    pm2.43d.1 $e |- ( ph -> ( ps -> ( ps -> ch ) ) ) $.
    $( Deduction absorbing redundant antecedent.  (The proof was shortened by
       O'Cat, 28-Nov-2008.) $)
    pm2.43d $p |- ( ph -> ( ps -> ch ) ) $=
      ( id mpdi ) ABBCBEDF $.
      $( [29-Nov-2008] $) $( [18-Aug-1993] $)
  $}

  ${
    pm2.43a.1 $e |- ( ps -> ( ph -> ( ps -> ch ) ) ) $.
    $( Inference absorbing redundant antecedent.  (The proof was shortened by
       O'Cat, 28-Nov-2008.) $)
    pm2.43a $p |- ( ps -> ( ph -> ch ) ) $=
      ( id mpid ) BABCBEDF $.
      $( [29-Nov-2008] $) $( [7-Nov-1995] $)

    $( Inference absorbing redundant antecedent. $)
    pm2.43b $p |- ( ph -> ( ps -> ch ) ) $=
      ( pm2.43a com12 ) BACABCDEF $.
      $( [31-Oct-1995] $)
  $}

  ${
    sylc.1 $e |- ( ph -> ( ps -> ch ) ) $.
    sylc.2 $e |- ( th -> ph ) $.
    sylc.3 $e |- ( th -> ps ) $.
    $( A syllogism inference combined with contraction. $)
    sylc $p |- ( th -> ch ) $=
      ( wi syl mpd ) DBCGDABCHFEIJ $.
      $( [4-May-1994] $)
  $}

  $( Converse of axiom ~ ax-2 .  Theorem *2.86 of [WhiteheadRussell] p. 108. $)
  pm2.86 $p |- ( ( ( ph -> ps ) -> ( ph -> ch ) ) ->
               ( ph -> ( ps -> ch ) ) ) $=
    ( wi ax-1 imim1i com23 ) ABDZACDZDBACBHIBAEFG $.
    $( [25-Apr-1994] $)

  ${
    pm2.86i.1 $e |- ( ( ph -> ps ) -> ( ph -> ch ) ) $.
    $( Inference based on ~ pm2.86 . $)
    pm2.86i $p |- ( ph -> ( ps -> ch ) ) $=
      ( wi pm2.86 ax-mp ) ABEACEEABCEEDABCFG $.
      $( [5-Aug-1993] $)
  $}

  ${
    pm2.86d.1 $e |- ( ph -> ( ( ps -> ch ) -> ( ps -> th ) ) ) $.
    $( Deduction based on ~ pm2.86 . $)
    pm2.86d $p |- ( ph -> ( ps -> ( ch -> th ) ) ) $=
      ( wi pm2.86 syl ) ABCFBDFFBCDFFEBCDGH $.
      $( [29-Jun-1995] $)
  $}

  $( The Linearity Axiom of the infinite-valued sentential logic (L-infinity)
     of Lukasiewicz.  (Contributed by O'Cat, 12-Aug-2004.) $)
  loolin $p |- ( ( ( ph -> ps ) -> ( ps -> ph ) ) -> ( ps -> ph ) ) $=
    ( wi ax-1 imim1i pm2.43d ) ABCZBACZCBABGHBADEF $.
    $( [14-Aug-2004] $) $( [12-Aug-2004] $)

  $( An alternate for the Linearity Axiom of the infinite-valued sentential
     logic (L-infinity) of Lukasiewicz, due to Barbara Wozniakowska, _Reports
     on Mathematical Logic_ 10, 129-137 (1978).  (Contributed by O'Cat,
     8-Aug-2004.) $)
  loowoz $p |- ( ( ( ph -> ps ) -> ( ph -> ch ) ) ->
                 ( ( ps -> ph ) -> ( ps -> ch ) ) ) $=
    ( wi ax-1 imim1i a2d ) ABDZACDZDBACBHIBAEFG $.
    $( [9-Aug-2004] $) $( [8-Aug-2004] $)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Logical negation
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$( This section makes our first use of the third axiom of propositonal
   calculus. $)

  ${
    con4i.1 $e |- ( -. ph -> -. ps ) $.
    $( Inference rule derived from axiom ~ ax-3 . $)
    con4i $p |- ( ps -> ph ) $=
      ( wn wi ax-3 ax-mp ) ADBDEBAECABFG $.
      $( [5-Aug-1993] $)
  $}

  ${
    con4d.1 $e |- ( ph -> ( -. ps -> -. ch ) ) $.
    $( Deduction derived from axiom ~ ax-3 . $)
    con4d $p |- ( ph -> ( ch -> ps ) ) $=
      ( wn wi ax-3 syl ) ABECEFCBFDBCGH $.
      $( [26-Mar-1995] $)
  $}

  $( From a wff and its negation, anything is true.  Theorem *2.21 of
     [WhiteheadRussell] p. 104.  Also called the Duns Scotus law. $)
  pm2.21 $p |- ( -. ph -> ( ph -> ps ) ) $=
    ( wn ax-1 con4d ) ACZBAFBCDE $.
    $( [5-Aug-1993] $)

  ${
    pm2.21i.1 $e |- -. ph $.
    $( A contradiction implies anything.  Inference from ~ pm2.21 . $)
    pm2.21i $p |- ( ph -> ps ) $=
      ( wn a1i con4i ) BAADBDCEF $.
      $( [16-Sep-1993] $)
  $}

  ${
    pm2.21d.1 $e |- ( ph -> -. ps ) $.
    $( A contradiction implies anything.  Deduction from ~ pm2.21 . $)
    pm2.21d $p |- ( ph -> ( ps -> ch ) ) $=
      ( wn a1d con4d ) ACBABECEDFG $.
      $( [10-Feb-1996] $)
  $}

  $( Theorem *2.24 of [WhiteheadRussell] p. 104. $)
  pm2.24 $p |-  ( ph -> ( -. ph -> ps ) ) $=
    ( wn pm2.21 com12 ) ACABABDE $.
    $( [6-Jan-2005] $) $( [3-Jan-2005] $)

  ${
    pm2.24ii.1 $e |- ph $.
    pm2.24ii.2 $e |- -. ph $.
    $( A contradiction implies anything.  Inference from ~ pm2.24 . $)
    pm2.24ii $p |- ps $=
      ( pm2.21i ax-mp ) ABCABDEF $.
      $( [27-Feb-2008] $) $( [27-Feb-2008] $)
  $}

  $( Proof by contradiction.  Theorem *2.18 of [WhiteheadRussell] p. 103.
     Also called the Law of Clavius. $)
  pm2.18 $p |- ( ( -. ph -> ph ) -> ph ) $=
    ( wn wi pm2.21 a2i con4d pm2.43i ) ABZACZAIAIHAIBZAJDEFG $.
    $( [5-Aug-1993] $)

  $( Peirce's axiom.  This odd-looking theorem is the "difference" between
     an intuitionistic system of propositional calculus and a classical system
     and is not accepted by intuitionists.  When Peirce's axiom is added to an
     intuitionistic system, the system becomes equivalent to our classical
     system ~ ax-1 through ~ ax-3 .  A curious fact about this
     theorem is that it requires ~ ax-3 for its proof even though the
     result has no negation connectives in it. $)
  peirce $p |- ( ( ( ph -> ps ) -> ph ) -> ph ) $=
    ( wi wn pm2.21 imim1i pm2.18 syl ) ABCZACADZACAJIAABEFAGH $.
    $( [5-Aug-1993] $)

  $( The Inversion Axiom of the infinite-valued sentential logic (L-infinity)
     of Lukasiewicz.  Using ~ dfor2 , we can see that this essentially
     expresses "disjunction commutes."  Theorem *2.69 of [WhiteheadRussell]
     p. 108. $)
  looinv $p |- ( ( ( ph -> ps ) -> ps ) -> ( ( ps -> ph ) -> ph ) ) $=
    ( wi imim1 peirce syl6 ) ABCZBCBACGACAGBADABEF $.
    $( [20-Aug-2004] $) $( [12-Aug-2004] $)

  $( Converse of double negation.  Theorem *2.14 of [WhiteheadRussell] p. 102.
     (The proof was shortened by David Harvey, 5-Sep-1999.  An even shorter
     proof found by Josh Purinton, 29-Dec-2000.) $)
  notnot2 $p |- ( -. -. ph -> ph ) $=
    ( wn wi pm2.21 pm2.18 syl ) ABZBGACAGADAEF $.
    $( [5-Aug-1993] $)

  ${
    negai.1 $e |- -. -. ph $.
    $( Inference from double negation. $)
    notnotri $p |- ph $=
      ( wn notnot2 ax-mp ) ACCABADE $.
      $( [27-Feb-2008] $) $( [27-Feb-2008] $)
  $}

  $( Converse of double negation.  Theorem *2.12 of [WhiteheadRussell]
     p. 101. $)
  notnot1 $p |- ( ph -> -. -. ph ) $=
    ( wn notnot2 con4i ) ABZBAECD $.
    $( [5-Aug-1993] $)

  ${
    negbi.1 $e |- ph $.
    $( Infer double negation. $)
    notnoti $p |- -. -. ph $=
      ( wn notnot1 ax-mp ) AACCBADE $.
      $( [27-Feb-2008] $) $( [27-Feb-2008] $)
  $}

  $( Reductio ad absurdum.  Theorem *2.01 of [WhiteheadRussell] p. 100.  (The
     proof was shortened by O'Cat, 21-Nov-2008. $)
  pm2.01 $p |- ( ( ph -> -. ph ) -> -. ph ) $=
    ( wn wi pm2.18 looinv ax-mp ) ABZACACAGCGCADGAEF $.
    $( [21-Nov-2008] $) $( [18-Aug-1993] $)

  ${
    pm2.01d.1 $e |- ( ph -> ( ps -> -. ps ) ) $.
    $( Deduction based on reductio ad absurdum. $)
    pm2.01d $p |- ( ph -> -. ps ) $=
      ( wn wi pm2.01 syl ) ABBDZEHCBFG $.
      $( [18-Aug-1993] $)
  $}

  $( Contraposition.  Theorem *2.03 of [WhiteheadRussell] p. 100. $)
  con2 $p |- ( ( ph -> -. ps ) -> ( ps -> -. ph ) ) $=
    ( wn wi notnot2 imim1i con4d ) ABCZDACZBICAHAEFG $.
    $( [5-Aug-1993] $)

  ${
    con2d.1 $e |- ( ph -> ( ps -> -. ch ) ) $.
    $( A contraposition deduction. $)
    con2d $p |- ( ph -> ( ch -> -. ps ) ) $=
      ( wn wi con2 syl ) ABCEFCBEFDBCGH $.
      $( [19-Aug-1993] $)
  $}

  $( Contraposition.  Theorem *2.15 of [WhiteheadRussell] p. 102. $)
  con1 $p |- ( ( -. ph -> ps ) -> ( -. ps -> ph ) ) $=
    ( wn wi notnot1 imim2i con4d ) ACZBDABCZBICHBEFG $.
    $( [5-Aug-1993] $)

  ${
    con1d.1 $e |- ( ph -> ( -. ps -> ch ) ) $.
    $( A contraposition deduction. $)
    con1d $p |- ( ph -> ( -. ch -> ps ) ) $=
      ( wn wi con1 syl ) ABECFCEBFDBCGH $.
      $( [5-Aug-1993] $)
  $}

  $( Contraposition.  Theorem *2.16 of [WhiteheadRussell] p. 103. $)
  con3 $p |- ( ( ph -> ps ) -> ( -. ps -> -. ph ) ) $=
    ( wi wn notnot1 imim2i con2d ) ABCABDZBHDABEFG $.
    $( [5-Aug-1993] $)

  ${
    con3d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( A contraposition deduction. $)
    con3d $p |- ( ph -> ( -. ch -> -. ps ) ) $=
      ( wi wn con3 syl ) ABCECFBFEDBCGH $.
      $( [5-Aug-1993] $)
  $}

  ${
    con1.a $e |- ( -. ph -> ps ) $.
    $( A contraposition inference.  (The proof was shortened by O'Cat,
       28-Nov-2008.) $)
    con1i $p |- ( -. ps -> ph ) $=
      ( wn wi con1 ax-mp ) ADBEBDAECABFG $.
      $( [29-Nov-2008] $) $( [5-Aug-1993] $)
  $}

  ${
    con2.a $e |- ( ph -> -. ps ) $.
    $( A contraposition inference.  (The proof was shortened by O'Cat,
       28-Nov-2008.) $)
    con2i $p |- ( ps -> -. ph ) $=
      ( wn wi con2 ax-mp ) ABDEBADECABFG $.
      $( [29-Nov-2008] $) $( [5-Aug-1993] $)
  $}

  ${
    con3.a $e |- ( ph -> ps ) $.
    $( A contraposition inference. $)
    con3i $p |- ( -. ps -> -. ph ) $=
      ( wn notnot2 syl con1i ) ADZBHDABAECFG $.
      $( [5-Aug-1993] $)
  $}

  $( Theorem *2.5 of [WhiteheadRussell] p. 107. $)
  pm2.5 $p |-  ( -. ( ph -> ps ) -> ( -. ph -> ps ) ) $=
    ( wi wn pm2.21 con3i pm2.21d ) ABCZDADZBIHABEFG $.
    $( [27-Jan-2005] $) $( [3-Jan-2005] $)

  $( Theorem *2.51 of [WhiteheadRussell] p. 107. $)
  pm2.51 $p |-  ( -. ( ph -> ps ) -> ( ph -> -. ps ) ) $=
    ( wi wn ax-1 con3i a1d ) ABCZDBDABHBAEFG $.
    $( [27-Jan-2005] $) $( [3-Jan-2005] $)

  $( Theorem *2.52 of [WhiteheadRussell] p. 107. $)
  pm2.52 $p |-  ( -. ( ph -> ps ) -> ( -. ph -> -. ps ) ) $=
    ( wi wn ax-1 con3i a1d ) ABCZDBDADBHBAEFG $.
    $( [27-Jan-2005] $) $( [3-Jan-2005] $)

  $( Theorem *2.521 of [WhiteheadRussell] p. 107. $)
  pm2.521 $p |-  ( -. ( ph -> ps ) -> ( ps -> ph ) ) $=
    ( wi wn pm2.52 con4d ) ABCDABABEF $.
    $( [6-Feb-2005] $) $( [3-Jan-2005] $)

  ${
    pm2.24i.1 $e |- ph $.
    $( Inference version of ~ pm2.24 . $)
    pm2.24i $p |- ( -. ph -> ps ) $=
      ( wn a1i con1i ) BAABDCEF $.
      $( [20-Aug-2001] $)
  $}

  ${
    pm2.24d.1 $e |- ( ph -> ps ) $.
    $( Deduction version of ~ pm2.21 . $)
    pm2.24d $p |- ( ph -> ( -. ps -> ch ) ) $=
      ( wn a1d con1d ) ACBABCEDFG $.
      $( [31-Jan-2006] $) $( [30-Jan-2006] $)
  $}

  ${
    mto.1 $e |- -. ps $.
    mto.2 $e |- ( ph -> ps ) $.
    $( The rule of modus tollens. $)
    mto $p |- -. ph $=
      ( wn con3i ax-mp ) BEAECABDFG $.
      $( [19-Aug-1993] $)
  $}

  ${
    mtoi.1 $e |- -. ch $.
    mtoi.2 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Modus tollens inference. $)
    mtoi $p |- ( ph -> -. ps ) $=
      ( wn con3d mpi ) ACFBFDABCEGH $.
      $( [5-Jul-1994] $)
  $}

  ${
    mtod.1 $e |- ( ph -> -. ch ) $.
    mtod.2 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Modus tollens deduction. $)
    mtod $p |- ( ph -> -. ps ) $=
      ( wn con3d mpd ) ACFBFDABCEGH $.
      $( [3-Apr-1994] $)
  $}

  ${
    mt2.1 $e |- ps $.
    mt2.2 $e |- ( ph -> -. ps ) $.
    $( A rule similar to modus tollens. $)
    mt2 $p |- -. ph $=
      ( wn con2i ax-mp ) BAECABDFG $.
      $( [19-Aug-1993] $)
  $}

  ${
    mt2i.1 $e |- ch $.
    mt2i.2 $e |- ( ph -> ( ps -> -. ch ) ) $.
    $( Modus tollens inference. $)
    mt2i $p |- ( ph -> -. ps ) $=
      ( wn con2d mpi ) ACBFDABCEGH $.
      $( [26-Mar-1995] $)
  $}

  ${
    mt2d.1 $e |- ( ph -> ch ) $.
    mt2d.2 $e |- ( ph -> ( ps -> -. ch ) ) $.
    $( Modus tollens deduction. $)
    mt2d $p |- ( ph -> -. ps ) $=
      ( wn con2d mpd ) ACBFDABCEGH $.
      $( [4-Jul-1994] $)
  $}

  ${
    mt3.1 $e |- -. ps $.
    mt3.2 $e |- ( -. ph -> ps ) $.
    $( A rule similar to modus tollens. $)
    mt3 $p |- ph $=
      ( wn con1i ax-mp ) BEACABDFG $.
      $( [18-May-1994] $)
  $}

  ${
    mt3i.1 $e |- -. ch $.
    mt3i.2 $e |- ( ph -> ( -. ps -> ch ) ) $.
    $( Modus tollens inference. $)
    mt3i $p |- ( ph -> ps ) $=
      ( wn con1d mpi ) ACFBDABCEGH $.
      $( [26-Mar-1995] $)
  $}

  ${
    mt3d.1 $e |- ( ph -> -. ch ) $.
    mt3d.2 $e |- ( ph -> ( -. ps -> ch ) ) $.
    $( Modus tollens deduction. $)
    mt3d $p |- ( ph -> ps ) $=
      ( wn con1d mpd ) ACFBDABCEGH $.
      $( [26-Mar-1995] $)
  $}

  ${
    mt4d.1 $e |- ( ph -> ps ) $.
    mt4d.2 $e |- ( ph -> ( -. ch -> -. ps ) ) $.
    $( Modus tollens deduction. $)
    mt4d $p |- ( ph -> ch ) $=
      ( con4d mpd ) ABCDACBEFG $.
      $( [18-Jun-2006] $) $( [9-Jun-2006] $)
  $}

  ${
    nsyl.1 $e |- ( ph -> -. ps ) $.
    nsyl.2 $e |- ( ch -> ps ) $.
    $( A negated syllogism inference. $)
    nsyl $p |- ( ph -> -. ch ) $=
      ( wn con3i syl ) ABFCFDCBEGH $.
      $( [31-Dec-1993] $)
  $}

  ${
    nsyld.1 $e |- ( ph -> ( ps -> -. ch ) ) $.
    nsyld.2 $e |- ( ph -> ( ta -> ch ) ) $.
    $( A negated syllogism deduction. $)
    nsyld $p |- ( ph -> ( ps -> -. ta ) ) $=
      ( wn con3d syld ) ABCGDGEADCFHI $.
      $( [10-Apr-2005] $) $( [9-Apr-2005] $)
  $}

  ${
    nsyl2.1 $e |- ( ph -> -. ps ) $.
    nsyl2.2 $e |- ( -. ch -> ps ) $.
    $( A negated syllogism inference. $)
    nsyl2 $p |- ( ph -> ch ) $=
      ( wn con1i syl ) ABFCDCBEGH $.
      $( [26-Jun-1994] $)
  $}

  ${
    nsyl3.1 $e |- ( ph -> -. ps ) $.
    nsyl3.2 $e |- ( ch -> ps ) $.
    $( A negated syllogism inference. $)
    nsyl3 $p |- ( ch -> -. ph ) $=
      ( wn con2i syl ) CBAFEABDGH $.
      $( [1-Dec-1995] $)
  $}

  ${
    nsyl4.1 $e |- ( ph -> ps ) $.
    nsyl4.2 $e |- ( -. ph -> ch ) $.
    $( A negated syllogism inference. $)
    nsyl4 $p |- ( -. ch -> ps ) $=
      ( wn con1i syl ) CFABACEGDH $.
      $( [15-Feb-1996] $)
  $}

  ${
    nsyli.1 $e |- ( ph -> ( ps -> ch ) ) $.
    nsyli.2 $e |- ( th -> -. ch ) $.
    $( A negated syllogism inference. $)
    nsyli $p |- ( ph -> ( th -> -. ps ) ) $=
      ( wn con3d syl5 ) ACGBGDABCEHFI $.
      $( [3-May-1994] $)
  $}

  $( Theorem *3.2 of [WhiteheadRussell] p. 111, expressed with primitive
     connectives.  (The proof was shortened by Josh Purinton, 29-Dec-2000.) $)
  pm3.2im $p |- ( ph -> ( ps -> -. ( ph -> -. ps ) ) ) $=
    ( wn wi pm2.27 con2d ) AABCZDBAGEF $.
    $( [5-Aug-1993] $)

  $( Theorem 8 of [Margaris] p. 60.  (The proof was shortened by Josh Purinton,
     29-Dec-2000.) $)
  mth8 $p |- ( ph -> ( -. ps -> -. ( ph -> ps ) ) ) $=
    ( wi pm2.27 con3d ) AABCBABDE $.
    $( [5-Aug-1993] $)

  $( Theorem *2.61 of [WhiteheadRussell] p. 107.  Useful for eliminating an
     antecedent. $)
  pm2.61 $p |- ( ( ph -> ps ) -> ( ( -. ph -> ps ) -> ps ) ) $=
    ( wn wi con1 imim1d pm2.18 syl6com ) ACBDZABDBCZBDBIJABABEFBGH $.
    $( [6-Mar-2008] $) $( [5-Aug-1993] $)

  ${
    pm2.61i.1 $e |- ( ph -> ps ) $.
    pm2.61i.2 $e |- ( -. ph -> ps ) $.
    $( Inference eliminating an antecedent. $)
    pm2.61i $p |- ps $=
      ( wi wn pm2.61 mp2 ) ABEAFBEBCDABGH $.
      $( [5-Apr-1994] $)
  $}

  ${
    pm2.61d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    pm2.61d.2 $e |- ( ph -> ( -. ps -> ch ) ) $.
    $( Deduction eliminating an antecedent. $)
    pm2.61d $p |- ( ph -> ch ) $=
      ( wi com12 wn pm2.61i ) BACFABCDGABHCEGI $.
      $( [27-Apr-1994] $)
  $}

  ${
    pm2.61d1.1 $e |- ( ph -> ( ps -> ch ) ) $.
    pm2.61d1.2 $e |- ( -. ps -> ch ) $.
    $( Inference eliminating an antecedent. $)
    pm2.61d1 $p |- ( ph -> ch ) $=
      ( wn wi a1i pm2.61d ) ABCDBFCGAEHI $.
      $( [20-Jul-2005] $) $( [15-Jul-2005] $)
  $}

  ${
    pm2.61d2.1 $e |- ( ph -> ( -. ps -> ch ) ) $.
    pm2.61d2.2 $e |- ( ps -> ch ) $.
    $( Inference eliminating an antecedent. $)
    pm2.61d2 $p |- ( ph -> ch ) $=
      ( wi a1i pm2.61d ) ABCBCFAEGDH $.
      $( [18-Aug-1993] $)
  $}

  ${
    pm2.61ii.1 $e |- ( -. ph -> ( -. ps -> ch ) ) $.
    pm2.61ii.2 $e |- ( ph -> ch ) $.
    pm2.61ii.3 $e |- ( ps -> ch ) $.
    $( Inference eliminating two antecedents.  (The proof was shortened by Josh
       Purinton,  29-Dec-2000.) $)
    pm2.61ii $p |- ch $=
      ( wn pm2.61d2 pm2.61i ) ACEAGBCDFHI $.
      $( [5-Aug-1993] $)
  $}

  ${
    pm2.61nii.1 $e |- ( ph -> ( ps -> ch ) ) $.
    pm2.61nii.2 $e |- ( -. ph -> ch ) $.
    pm2.61nii.3 $e |- ( -. ps -> ch ) $.
    $( Inference eliminating two antecedents. $)
    pm2.61nii $p |- ch $=
      ( com12 pm2.61d1 pm2.61i ) BCBACABCDGEHFI $.
      $( [5-Aug-1993] $)
  $}

  ${
    pm2.61iii.1 $e |- ( -. ph -> ( -. ps -> ( -. ch -> th ) ) ) $.
    pm2.61iii.2 $e |- ( ph -> th ) $.
    pm2.61iii.3 $e |- ( ps -> th ) $.
    pm2.61iii.4 $e |- ( ch -> th ) $.
    $( Inference eliminating three antecedents. $)
    pm2.61iii $p |- th $=
      ( wn wi a1d pm2.61i pm2.61ii ) BCDABIZCIZDJZJAPNADOFKKELGHM $.
      $( [2-Jan-2002] $)
  $}

  $( Theorem *2.6 of [WhiteheadRussell] p. 107. $)
  pm2.6 $p |-  ( ( -. ph -> ps ) -> ( ( ph -> ps ) -> ps ) ) $=
    ( wi wn pm2.61 com12 ) ABCADBCBABEF $.
    $( [1-Feb-2005] $) $( [3-Jan-2005] $)

  $( Theorem *2.65 of [WhiteheadRussell] p. 107.  Proof by contradiction. $)
  pm2.65 $p |- ( ( ph -> ps ) -> ( ( ph -> -. ps ) -> -. ph ) ) $=
    ( wi wn pm3.2im a2i con2d ) ABCAABDCZABHDABEFG $.
    $( [5-Aug-1993] $)

  ${
    pm2.65i.1 $e |- ( ph -> ps ) $.
    pm2.65i.2 $e |- ( ph -> -. ps ) $.
    $( Inference rule for proof by contradiction. $)
    pm2.65i $p |- -. ph $=
      ( wi wn pm2.65 mp2 ) ABEABFEAFCDABGH $.
      $( [18-May-1994] $)
  $}

  ${
    pm2.65d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    pm2.65d.2 $e |- ( ph -> ( ps -> -. ch ) ) $.
    $( Deduction rule for proof by contradiction. $)
    pm2.65d $p |- ( ph -> -. ps ) $=
      ( wi wn pm2.65 sylc ) BCFBCGFBGABCHDEI $.
      $( [26-Jun-1994] $)
  $}

  ${
    ja.1 $e |- ( -. ph -> ch ) $.
    ja.2 $e |- ( ps -> ch ) $.
    $( Inference joining the antecedents of two premises.  (The proof was
       shortened by O'Cat, 19-Feb-2008.) $)
    ja $p |- ( ( ph -> ps ) -> ch ) $=
      ( wi imim2i pm2.61d1 ) ABFACBCAEGDH $.
      $( [19-Feb-2008] $) $( [5-Aug-1993] $)
  $}

  ${
    jc.1 $e |- ( ph -> ps ) $.
    jc.2 $e |- ( ph -> ch ) $.
    $( Inference joining the consequents of two premises. $)
    jc $p |- ( ph -> -. ( ps -> -. ch ) ) $=
      ( wn wi pm3.2im sylc ) BCBCFGFABCHDEI $.
      $( [5-Aug-1993] $)
  $}

  $( Simplification.  Similar to Theorem *3.26 (Simp) of [WhiteheadRussell]
     p. 112. $)
  pm3.26im $p |- ( -. ( ph -> -. ps ) -> ph ) $=
    ( wn wi pm2.21 con1i ) AABCZDAGEF $.
    $( [5-Aug-1993] $)

  $( Simplification.  Similar to Theorem *3.27 (Simp) of [WhiteheadRussell]
     p. 112. $)
  pm3.27im $p |- ( -. ( ph -> -. ps ) -> ps ) $=
    ( wn wi ax-1 con1i ) BABCZDGAEF $.
    $( [5-Aug-1993] $)

  $( Importation theorem expressed with primitive connectives. $)
  impt $p |- ( ( ph -> ( ps -> ch ) ) -> ( -. ( ph -> -. ps ) -> ch ) ) $=
    ( wi wn con3 imim2i com23 con1d ) ABCDZDZCABEZDKACEZLJMLDABCFGHI $.
    $( [25-Apr-1994] $)

  $( Exportation theorem expressed with primitive connectives. $)
  expt $p |- ( ( -. ( ph -> -. ps ) -> ch ) -> ( ph -> ( ps -> ch ) ) ) $=
    ( wn wi pm3.2im imim1d com12 ) AABDEDZCEBCEABICABFGH $.
    $( [5-Aug-1993] $)

  ${
    impi.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( An importation inference. $)
    impi $p |- ( -. ( ph -> -. ps ) -> ch ) $=
      ( wi wn impt ax-mp ) ABCEEABFEFCEDABCGH $.
      $( [5-Aug-1993] $)
  $}

  ${
    expi.1 $e |- ( -. ( ph -> -. ps ) -> ch ) $.
    $( An exportation inference.  (The proof was shortened by O'Cat,
       28-Nov-2008.) $)
    expi $p |- ( ph -> ( ps -> ch ) ) $=
      ( wn wi pm3.2im syl6 ) ABABEFECABGDH $.
      $( [29-Nov-2008] $) $( [5-Aug-1993] $)
  $}

  $( Theorem used to justify definition of biconditional ~ df-bi .  (The proof
     was shortened by Josh Purinton, 29-Dec-2000.) $)
  bijust $p |- -. ( ( ph -> ph ) -> -. ( ph -> ph ) ) $=
    ( wi wn id pm2.01 mt2 ) AABZGCBGADGEF $.
    $( [11-May-1999] $)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Logical equivalence
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Declare the biconditional connective. $)
  $c <-> $. $( Double arrow (read:  'if and only if' or
               'is logically equivalent to') $)

  $( Extend our wff definition to include the biconditional connective. $)
  wb $a wff ( ph <-> ps ) $.

  $( This is our first definition, which introduces and defines the
     biconditional connective ` <-> ` .  We define a wff of the form
     ` ( ph <-> ps ) ` as an abbreviation for
     ` -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) ` .

     Unlike most traditional developments, we have chosen not to have a
     separate symbol such as "Df." to mean "is defined as."  Instead, we will
     later use the biconditional connective for this purpose ( ~ df-or is its
     first use), as it allows us to use logic to manipulate definitions
     directly.  This greatly simplifies many proofs since it eliminates the
     need for a separate mechanism for introducing and eliminating
     definitions.  Of course, we cannot use this mechanism to define the
     biconditional itself, since it hasn't been introduced yet.  Instead, we
     use a more general form of definition, described as follows.

     In its most general form, a definition is simply an assertion that
     introduces a new symbol (or a new combination of existing symbols, as in
     ~ df-3an ) that is eliminable and does not strengthen the existing
     language.  The latter requirement means that the set of provable
     statements not containing the new symbol (or new combination) should
     remain exactly the same after the definition is introduced.  Our
     definition of the biconditional may look unusual compared to most
     definitions, but it strictly satisfies these requirements.

     The justification for our definition is that if we mechanically replace
     the first wff above (the definiendum i.e. the thing being defined) with
     the second (the definiens i.e. the defining expression) in the
     definition, the definition becomes a substitution instance of previously
     proved theorem ~ bijust .  It is impossible to use ~ df-bi to prove any
     statement expressed in the original language that can't be proved from
     the original axioms.  For if it were, we could replace it with instances
     of ~ bijust throughout the proof, thus obtaining a proof from the
     original axioms (contradiction).

     Note that from Metamath's point of view, a definition is just another
     axiom - i.e. an assertion we claim to be true - but from our high level
     point of view, we are are not strengthening the language.  To indicate
     this fact, we prefix definition labels with "df-" instead of "ax-".
     (This prefixing is an informal convention that means nothing to the
     Metamath proof verifier; it is just for human readability.)

     See ~ dfbi1 , ~ dfbi2 , and ~ dfbi3 for theorems suggesting typical
     textbook definitions of ` <-> ` , showing that our definition has the
     properties we expect.  Theorem ~ dfbi shows this definition rewritten
     in an abbreviated form after conjunction is introduced, for easier
     understanding. $)
  df-bi $a |- -. ( ( ( ph <-> ps ) -> -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) )
        -> -. ( -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) -> ( ph <-> ps ) ) ) $.

  $( Property of the biconditional connective. $)
  bi1 $p |- ( ( ph <-> ps ) -> ( ph -> ps ) ) $=
    ( wb wi wn df-bi pm3.26im ax-mp syl ) ABCZABDZBADZEDEZKJMDZMJDZEDENABFNOGHK
    LGI $.
    $( [11-May-1999] $)

  $( Property of the biconditional connective. $)
  bi2 $p |- ( ( ph <-> ps ) -> ( ps -> ph ) ) $=
    ( wb wi wn df-bi pm3.26im ax-mp pm3.27im syl ) ABCZABDZBADZEDEZMKNDZNKDZEDE
    OABFOPGHLMIJ $.
    $( [11-May-1999] $)

  $( Property of the biconditional connective. $)
  bi3 $p |- ( ( ph -> ps ) -> ( ( ps -> ph ) -> ( ph <-> ps ) ) ) $=
    ( wi wb wn df-bi pm3.27im ax-mp expi ) ABCZBACZABDZLJKECEZCZMLCZECEOABFNOGH
    I $.
    $( [11-May-1999] $)

  ${
    biimp.1 $e |- ( ph <-> ps ) $.
    $( Infer an implication from a logical equivalence. $)
    biimpi $p |- ( ph -> ps ) $=
      ( wb wi bi1 ax-mp ) ABDABECABFG $.
      $( [5-Aug-1993] $)
  $}

  ${
    biimpr.1 $e |- ( ph <-> ps ) $.
    $( Infer a converse implication from a logical equivalence. $)
    biimpri $p |- ( ps -> ph ) $=
      ( wb wi bi2 ax-mp ) ABDBAECABFG $.
      $( [5-Aug-1993] $)
  $}

  ${
    biimpd.1 $e |- ( ph -> ( ps <-> ch ) ) $.

    $( Deduce an implication from a logical equivalence. $)
    biimpd $p |- ( ph -> ( ps -> ch ) ) $=
      ( wb wi bi1 syl ) ABCEBCFDBCGH $.
      $( [5-Aug-1993] $)

   $( Deduce a converse implication from a logical equivalence. $)
    biimprd $p |- ( ph -> ( ch -> ps ) ) $=
      ( wb wi bi2 syl ) ABCECBFDBCGH $.
      $( [5-Aug-1993] $)

   $( Deduce a commuted implication from a logical equivalence. $)
    biimpcd $p |- ( ps -> ( ph -> ch ) ) $=
      ( biimpd com12 ) ABCABCDEF $.
      $( [3-May-1994] $)

   $( Deduce a converse commuted implication from a logical equivalence. $)
    biimprcd $p |- ( ch -> ( ph -> ps ) ) $=
      ( biimprd com12 ) ACBABCDEF $.
      $( [3-May-1994] $)
  $}

  ${
    impbi.1 $e |- ( ph -> ps ) $.
    impbi.2 $e |- ( ps -> ph ) $.
    $( Infer an equivalence from an implication and its converse. $)
    impbii $p |- ( ph <-> ps ) $=
      ( wi wb bi3 mp2 ) ABEBAEABFCDABGH $.
      $( [5-Aug-1993] $)
  $}

  $( Relate the biconditional connective to primitive connectives.  See
     ~ dfbi1gb for an unusual version proved directly from axioms. $)
  dfbi1 $p |- ( ( ph <-> ps ) <-> -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) ) $=
    ( wb wi wn bi1 bi2 jc bi3 impi impbii ) ABCZABDZBADZEDELMNABFABGHMNLABIJK 
    $.
    $( [5-Aug-1993] $)

  $( This proof of ~ dfbi1 , discovered by Gregory Bush on 8-Mar-2004, has
     several curious properties.  First, it has only 17 steps directly
     from the axioms and ~ df-bi , compared to over 800 steps were the proof
     of ~ dfbi1 expanded into axioms.  Second, step 2 demands only the property
     of "true"; any axiom (or theorem) could be used.  It might be thought,
     therefore, that it is in some sense redundant, but in fact no proof
     is shorter than this (measured by number of steps).  Third, it illustrates
     how intermediate steps can "blow up" in size even in short proofs.
     Fourth, the compressed proof is only 182 bytes (or 17 bytes in D-proof
     notation), but the generated web page is over 200kB with intermediate
     steps that are essentially incomprehensible to humans (other than Gregory
     Bush).  If there were an obfuscated code contest for proofs, this would be
     a contender. $)
  dfbi1gb $p |- ( ( ph <-> ps ) <-> -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) ) $=
    ( wch wth wb wi wn df-bi ax-1 ax-mp ax-3 ax-2 ) ABEZABFBAFGFGZFNMFGFGZMNEZA
    BHCDCFFZOPFZCDIRGZQGZFZQRFSPOFZSFZFZUASUBISUCTFZFZUDUAFUEUFTGZUCGZFZUEUHUIM
    NHUHUGIJTUCKJUESIJSUCTLJJRQKJJJ $.
    $( [10-Mar-2004] $) $( [10-Mar-2004] $)

  $( Logical equivalence of commuted antecedents.  Part of Theorem *4.87 of
     [WhiteheadRussell] p. 122. $)
  bi2.04 $p |- ( ( ph -> ( ps -> ch ) ) <-> ( ps -> ( ph -> ch ) ) ) $=
    ( wi pm2.04 impbii ) ABCDDBACDDABCEBACEF $.
    $( [5-Aug-1993] $)

  $( Double negation.  Theorem *4.13 of [WhiteheadRussell] p. 117. $)
  notnot $p |- ( ph <-> -. -. ph ) $=
    ( wn notnot1 notnot2 impbii ) AABBACADE $.
    $( [5-Aug-1993] $)

  $( Theorem *4.8 of [WhiteheadRussell] p. 122. $)
  pm4.8 $p |-  ( ( ph -> -. ph ) <-> -. ph ) $=
    ( wn wi pm2.01 ax-1 impbii ) AABZCGADGAEF $.
    $( [5-Feb-2005] $) $( [3-Jan-2005] $)

  $( Theorem *4.81 of [WhiteheadRussell] p. 122. $)
  pm4.81 $p |-  ( ( -. ph -> ph ) <-> ph ) $=
    ( wn wi pm2.18 pm2.24 impbii ) ABACAADAAEF $.
    $( [10-Feb-2005] $) $( [3-Jan-2005] $)

  $( Contraposition.  Bidirectional version of ~ con1 . $)
  con1b $p |- ( ( -. ph -> ps ) <-> ( -. ps -> ph ) ) $=
    ( wn wi con1 impbii ) ACBDBCADABEBAEF $.
    $( [5-Aug-1993] $)

  $( Contraposition.  Bidirectional version of ~ con2 . $)
  con2b $p |- ( ( ph -> -. ps ) <-> ( ps -> -. ph ) ) $=
    ( wn wi con2 impbii ) ABCDBACDABEBAEF $.
    $( [5-Aug-1993] $)

  $( Contraposition.  Theorem *4.1 of [WhiteheadRussell] p. 116. $)
  con34b $p |- ( ( ph -> ps ) <-> ( -. ps -> -. ph ) ) $=
    ( wi wn con3 ax-3 impbii ) ABCBDADCABEBAFG $.
    $( [5-Aug-1993] $)

  $( Antecedent absorption implication.  Theorem *5.4 of
     [WhiteheadRussell] p. 125. $)
  pm5.4 $p |- ( ( ph -> ( ph -> ps ) ) <-> ( ph -> ps ) ) $=
    ( wi pm2.43 ax-1 impbii ) AABCZCGABDGAEF $.
    $( [5-Aug-1993] $)

  $( Distributive law for implication.  Compare Theorem *5.41 of
     [WhiteheadRussell] p. 125. $)
  imdi $p |- ( ( ph -> ( ps -> ch ) ) <->
               ( ( ph -> ps ) -> ( ph -> ch ) ) ) $=
    ( wi ax-2 pm2.86 impbii ) ABCDDABDACDDABCEABCFG $.
    $( [5-Aug-1993] $)

  $( Theorem *5.41 of [WhiteheadRussell] p. 125. $)
  pm5.41 $p |-  ( ( ( ph -> ps ) -> ( ph -> ch ) ) <->
                ( ph -> ( ps -> ch ) ) ) $=
    ( wi pm2.86 ax-2 impbii ) ABDACDDABCDDABCEABCFG $.
    $( [10-Feb-2005] $) $( [3-Jan-2005] $)

  $( Principle of identity for logical equivalence.  Theorem *4.2 of
     [WhiteheadRussell] p. 117. $)
  biid $p |- ( ph <-> ph ) $=
    ( id impbii ) AAABZDC $.
    $( [5-Aug-1993] $)

  $( Principle of identity with antecedent. $)
  biidd $p |- ( ph -> ( ps <-> ps ) ) $=
    ( wb biid a1i ) BBCABDE $.
    $( [25-Nov-1995] $)

  ${
    bicomi.1 $e |- ( ph <-> ps ) $.
    $( Inference from commutative law for logical equivalence. $)
    bicomi $p |- ( ps <-> ph ) $=
      ( biimpri biimpi impbii ) BAABCDABCEF $.
      $( [5-Aug-1993] $)
  $}

  ${
    bitri.1 $e |- ( ph <-> ps ) $.
    bitri.2 $e |- ( ps <-> ch ) $.
    $( An inference from transitive law for logical equivalence. $)
    bitri $p |- ( ph <-> ch ) $=
      ( biimpi syl biimpri impbii ) ACABCABDFBCEFGCBABCEHABDHGI $.
      $( [5-Aug-1993] $)
  $}

  ${
    bitr2i.1 $e |- ( ph <-> ps ) $.
    bitr2i.2 $e |- ( ps <-> ch ) $.
    $( An inference from transitive law for logical equivalence. $)
    bitr2i $p |- ( ch <-> ph ) $=
      ( bitri bicomi ) ACABCDEFG $.
      $( [5-Aug-1993] $)
  $}

  ${
    bitr3i.1 $e |- ( ps <-> ph ) $.
    bitr3i.2 $e |- ( ps <-> ch ) $.
    $( An inference from transitive law for logical equivalence. $)
    bitr3i $p |- ( ph <-> ch ) $=
      ( bicomi bitri ) ABCBADFEG $.
      $( [5-Aug-1993] $)
  $}

  ${
    bitr4i.1 $e |- ( ph <-> ps ) $.
    bitr4i.2 $e |- ( ch <-> ps ) $.
    $( An inference from transitive law for logical equivalence. $)
    bitr4i $p |- ( ph <-> ch ) $=
      ( bicomi bitri ) ABCDCBEFG $.
      $( [5-Aug-1993] $)
  $}

  ${
    3bitri.1 $e |- ( ph <-> ps ) $.
    3bitri.2 $e |- ( ps <-> ch ) $.
    3bitri.3 $e |- ( ch <-> th ) $.
    $( A chained inference from transitive law for logical equivalence. $)
    3bitri $p |- ( ph <-> th ) $=
      ( bitri ) ABDEBCDFGHH $.
      $( [5-Aug-1993] $)

    $( A chained inference from transitive law for logical equivalence. $)
    3bitrri $p |- ( th <-> ph ) $=
      ( bitr2i bitr3i ) DCAGABCEFHI $.
      $( [10-Aug-2006] $) $( [4-Aug-2006] $)
  $}

  ${
    3bitr2i.1 $e |- ( ph <-> ps ) $.
    3bitr2i.2 $e |- ( ch <-> ps ) $.
    3bitr2i.3 $e |- ( ch <-> th ) $.
    $( A chained inference from transitive law for logical equivalence. $)
    3bitr2i $p |- ( ph <-> th ) $=
      ( bitr4i bitri ) ACDABCEFHGI $.
      $( [10-Aug-2006] $) $( [4-Aug-2006] $)

    $( A chained inference from transitive law for logical equivalence. $)
    3bitr2ri $p |- ( th <-> ph ) $=
      ( bitr4i bitr2i ) ACDABCEFHGI $.
      $( [10-Aug-2006] $) $( [4-Aug-2006] $)
  $}

  ${
    3bitr3i.1 $e |- ( ph <-> ps ) $.
    3bitr3i.2 $e |- ( ph <-> ch ) $.
    3bitr3i.3 $e |- ( ps <-> th ) $.
    $( A chained inference from transitive law for logical equivalence. $)
    3bitr3i $p |- ( ch <-> th ) $=
      ( bitr3i bitri ) CBDCABFEHGI $.
      $( [19-Aug-1993] $)

    $( A chained inference from transitive law for logical equivalence. $)
    3bitr3ri $p |- ( th <-> ch ) $=
      ( bitr3i ) DBCGBACEFHH $.
      $( [5-Aug-1993] $)
  $}

  ${
    3bitr4i.1 $e |- ( ph <-> ps ) $.
    3bitr4i.2 $e |- ( ch <-> ph ) $.
    3bitr4i.3 $e |- ( th <-> ps ) $.
    $( A chained inference from transitive law for logical equivalence.  This
       inference is frequently used to apply a definition to both sides of a
       logical equivalence. $)
    3bitr4i $p |- ( ch <-> th ) $=
      ( bitr4i bitri ) CADFABDEGHI $.
      $( [5-Aug-1993] $)

    $( A chained inference from transitive law for logical equivalence. $)
    3bitr4ri $p |- ( th <-> ch ) $=
      ( bitr4i bitr2i ) CADFABDEGHI $.
      $( [2-Sep-1995] $)
  $}

  $( The next three rules are useful for building up wff's around a
     definition, in order to make use of the definition. $)

  ${
    bi.a $e |- ( ph <-> ps ) $.

    $( Introduce an antecedent to both sides of a logical equivalence. $)
    imbi2i $p |- ( ( ch -> ph ) <-> ( ch -> ps ) ) $=
      ( wi biimpi imim2i biimpri impbii ) CAECBEABCABDFGBACABDHGI $.
      $( [5-Aug-1993] $)

    $( Introduce a consequent to both sides of a logical equivalence. $)
    imbi1i $p |- ( ( ph -> ch ) <-> ( ps -> ch ) ) $=
      ( wi biimpri imim1i biimpi impbii ) ACEBCEBACABDFGABCABDHGI $.
      $( [5-Aug-1993] $)

    $( Negate both sides of a logical equivalence. $)
    notbii $p |- ( -. ph <-> -. ps ) $=
      ( wn biimpri con3i biimpi impbii ) ADBDBAABCEFABABCGFH $.
      $( [5-Aug-1993] $)

  $}

  ${
    imbi12i.1 $e |- ( ph <-> ps ) $.
    imbi12i.2 $e |- ( ch <-> th ) $.
    $( Join two logical equivalences to form equivalence of implications. $)
    imbi12i $p |- ( ( ph -> ch ) <-> ( ps -> th ) ) $=
      ( wi imbi2i imbi1i bitri ) ACGADGBDGCDAFHABDEIJ $.
      $( [5-Aug-1993] $)
  $}

  ${
    mpbi.min $e |- ph $.
    mpbi.maj $e |- ( ph <-> ps ) $.
    $( An inference from a biconditional, related to modus ponens. $)
    mpbi $p |- ps $=
      ( biimpi ax-mp ) ABCABDEF $.
      $( [5-Aug-1993] $)
  $}

  ${
    mpbir.min $e |- ps $.
    mpbir.maj $e |- ( ph <-> ps ) $.
    $( An inference from a biconditional, related to modus ponens. $)
    mpbir $p |- ph $=
      ( biimpri ax-mp ) BACABDEF $.
      $( [5-Aug-1993] $)
  $}

  ${
    mtbi.1 $e |- -. ph $.
    mtbi.2 $e |- ( ph <-> ps ) $.
    $( An inference from a biconditional, related to modus tollens. $)
    mtbi $p |- -. ps $=
      ( wn notbii mpbi ) AEBECABDFG $.
      $( [15-Nov-1994] $)
  $}

  ${
    mtbir.1 $e |- -. ps $.
    mtbir.2 $e |- ( ph <-> ps ) $.
    $( An inference from a biconditional, related to modus tollens. $)
    mtbir $p |- -. ph $=
      ( wn notbii mpbir ) AEBECABDFG $.
      $( [15-Nov-1994] $)
  $}

  ${
    mpbii.min $e |- ps $.
    mpbii.maj $e |- ( ph -> ( ps <-> ch ) ) $.
    $( An inference from a nested biconditional, related to modus ponens. $)
    mpbii $p |- ( ph -> ch ) $=
      ( biimpd mpi ) ABCDABCEFG $.
      $( [5-Aug-1993] $)
  $}

  ${
    mpbiri.min $e |- ch $.
    mpbiri.maj $e |- ( ph -> ( ps <-> ch ) ) $.
    $( An inference from a nested biconditional, related to modus ponens. $)
    mpbiri $p |- ( ph -> ps ) $=
      ( biimprd mpi ) ACBDABCEFG $.
      $( [5-Aug-1993] $)
  $}

  ${
    mpbid.min $e |- ( ph -> ps ) $.
    mpbid.maj $e |- ( ph -> ( ps <-> ch ) ) $.
    $( A deduction from a biconditional, related to modus ponens. $)
    mpbid $p |- ( ph -> ch ) $=
      ( biimpd mpd ) ABCDABCEFG $.
      $( [5-Aug-1993] $)
  $}

  ${
    mpbird.min $e |- ( ph -> ch ) $.
    mpbird.maj $e |- ( ph -> ( ps <-> ch ) ) $.
    $( A deduction from a biconditional, related to modus ponens. $)
    mpbird $p |- ( ph -> ps ) $=
      ( biimprd mpd ) ACBDABCEFG $.
      $( [5-Aug-1993] $)
  $}

  ${
    a1bi.1 $e |- ph $.
    $( Inference rule introducing a theorem as an antecedent. $)
    a1bi $p |- ( ps <-> ( ph -> ps ) ) $=
      ( wi ax-1 pm2.27 ax-mp impbii ) BABDZBAEAIBDCABFGH $.
      $( [5-Aug-1993] $)
  $}

  ${
    sylib.1 $e |- ( ph -> ps ) $.
    sylib.2 $e |- ( ps <-> ch ) $.
    $( A mixed syllogism inference from an implication and a biconditional. $)
    sylib $p |- ( ph -> ch ) $=
      ( biimpi syl ) ABCDBCEFG $.
      $( [5-Aug-1993] $)
  $}

  ${
    sylbi.1 $e |- ( ph <-> ps ) $.
    sylbi.2 $e |- ( ps -> ch ) $.
    $( A mixed syllogism inference from a biconditional and an implication.
       Useful for substituting an antecedent with a definition. $)
    sylbi $p |- ( ph -> ch ) $=
      ( biimpi syl ) ABCABDFEG $.
      $( [5-Aug-1993] $)
  $}

  ${
    sylibr.1 $e |- ( ph -> ps ) $.
    sylibr.2 $e |- ( ch <-> ps ) $.
    $( A mixed syllogism inference from an implication and a biconditional.
       Useful for substituting a consequent with a definition. $)
    sylibr $p |- ( ph -> ch ) $=
      ( biimpri syl ) ABCDCBEFG $.
      $( [5-Aug-1993] $)
  $}

  ${
    sylbir.1 $e |- ( ps <-> ph ) $.
    sylbir.2 $e |- ( ps -> ch ) $.
    $( A mixed syllogism inference from a biconditional and an implication. $)
    sylbir $p |- ( ph -> ch ) $=
      ( biimpri syl ) ABCBADFEG $.
      $( [5-Aug-1993] $)
  $}

  ${
    sylibd.1 $e |- ( ph -> ( ps -> ch ) ) $.
    sylibd.2 $e |- ( ph -> ( ch <-> th ) ) $.
    $( A syllogism deduction. $)
    sylibd $p |- ( ph -> ( ps -> th ) ) $=
      ( biimpd syld ) ABCDEACDFGH $.
      $( [3-Aug-1994] $)
  $}

  ${
    sylbid.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    sylbid.2 $e |- ( ph -> ( ch -> th ) ) $.
    $( A syllogism deduction. $)
    sylbid $p |- ( ph -> ( ps -> th ) ) $=
      ( biimpd syld ) ABCDABCEGFH $.
      $( [3-Aug-1994] $)
  $}

  ${
    sylibrd.1 $e |- ( ph -> ( ps -> ch ) ) $.
    sylibrd.2 $e |- ( ph -> ( th <-> ch ) ) $.
    $( A syllogism deduction. $)
    sylibrd $p |- ( ph -> ( ps -> th ) ) $=
      ( biimprd syld ) ABCDEADCFGH $.
      $( [3-Aug-1994] $)
  $}

  ${
    sylbird.1 $e |- ( ph -> ( ch <-> ps ) ) $.
    sylbird.2 $e |- ( ph -> ( ch -> th ) ) $.
    $( A syllogism deduction. $)
    sylbird $p |- ( ph -> ( ps -> th ) ) $=
      ( biimprd syld ) ABCDACBEGFH $.
      $( [3-Aug-1994] $)
  $}

  ${
    syl5ib.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syl5ib.2 $e |- ( th <-> ps ) $.
    $( A mixed syllogism inference from a nested implication and a
       biconditional.  Useful for substituting an embedded antecedent with a
       definition. $)
    syl5ib $p |- ( ph -> ( th -> ch ) ) $=
      ( biimpi syl5 ) ABCDEDBFGH $.
      $( [5-Aug-1993] $)
  $}

  ${
    syl5ibr.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syl5ibr.2 $e |- ( ps <-> th ) $.
    $( A mixed syllogism inference from a nested implication and a
       biconditional. $)
    syl5ibr $p |- ( ph -> ( th -> ch ) ) $=
      ( biimpri syl5 ) ABCDEBDFGH $.
      $( [5-Aug-1993] $)
  $}

  ${
    syl5bi.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    syl5bi.2 $e |- ( th -> ps ) $.
    $( A mixed syllogism inference. $)
    syl5bi $p |- ( ph -> ( th -> ch ) ) $=
      ( biimpd syl5 ) ABCDABCEGFH $.
      $( [5-Aug-1993] $)

    $( A mixed syllogism inference. $)
    syl5cbi $p |- ( th -> ( ph -> ch ) ) $=
      ( syl5bi com12 ) ADCABCDEFGH $.
      $( [22-Jun-2007] $) $( [19-Jun-2007] $)
  $}

  ${
    syl5bir.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    syl5bir.2 $e |- ( th -> ch ) $.
    $( A mixed syllogism inference. $)
    syl5bir $p |- ( ph -> ( th -> ps ) ) $=
      ( biimprd syl5 ) ACBDABCEGFH $.
      $( [3-Apr-1994] $)

    $( A mixed syllogism inference. $)
    syl5cbir $p |- ( th -> ( ph -> ps ) ) $=
      ( syl5bir com12 ) ADBABCDEFGH $.
      $( [20-Jun-2007] $) $( [20-Jun-2007] $)
  $}

  ${
    syl6ib.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syl6ib.2 $e |- ( ch <-> th ) $.
    $( A mixed syllogism inference from a nested implication and a
       biconditional. $)
    syl6ib $p |- ( ph -> ( ps -> th ) ) $=
      ( biimpi syl6 ) ABCDECDFGH $.
      $( [5-Aug-1993] $)
  $}

  ${
    syl6ibr.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syl6ibr.2 $e |- ( th <-> ch ) $.
    $( A mixed syllogism inference from a nested implication and a
       biconditional.  Useful for substituting an embedded consequent with a
       definition. $)
    syl6ibr $p |- ( ph -> ( ps -> th ) ) $=
      ( biimpri syl6 ) ABCDEDCFGH $.
      $( [5-Aug-1993] $)
  $}


  ${
    syl6bi.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    syl6bi.2 $e |- ( ch -> th ) $.
    $( A mixed syllogism inference. $)
    syl6bi $p |- ( ph -> ( ps -> th ) ) $=
      ( biimpd syl6 ) ABCDABCEGFH $.
      $( [2-Jan-1994] $)
  $}

  ${
    syl6bir.1 $e |- ( ph -> ( ch <-> ps ) ) $.
    syl6bir.2 $e |- ( ch -> th ) $.
    $( A mixed syllogism inference. $)
    syl6bir $p |- ( ph -> ( ps -> th ) ) $=
      ( biimprd syl6 ) ABCDACBEGFH $.
      $( [18-May-1994] $)
  $}

  ${
    syl7ib.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    syl7ib.2 $e |- ( ta <-> ch ) $.
    $( A mixed syllogism inference from a doubly nested implication and a
       biconditional. $)
    syl7ib $p |- ( ph -> ( ps -> ( ta -> th ) ) ) $=
      ( biimpi syl7 ) ABCDEFECGHI $.
      $( [5-Aug-1993] $)
  $}

  ${
    syl8ib.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    syl8ib.2 $e |- ( th <-> ta ) $.
    $( A syllogism rule of inference.  The second premise is used to replace
       the consequent of the first premise. $)
    syl8ib $p |- ( ph -> ( ps -> ( ch -> ta ) ) ) $=
      ( biimpi syl8 ) ABCDEFDEGHI $.
      $( [1-Aug-1994] $)
  $}

  ${
    3imtr3.1 $e |- ( ph -> ps ) $.
    3imtr3.2 $e |- ( ph <-> ch ) $.
    3imtr3.3 $e |- ( ps <-> th ) $.
    $( A mixed syllogism inference, useful for removing a definition from both
       sides of an implication. $)
    3imtr3i $p |- ( ch -> th ) $=
      ( sylbir sylib ) CBDCABFEHGI $.
      $( [10-Aug-1994] $)
  $}

  ${
    3imtr4.1 $e |- ( ph -> ps ) $.
    3imtr4.2 $e |- ( ch <-> ph ) $.
    3imtr4.3 $e |- ( th <-> ps ) $.
    $( A mixed syllogism inference, useful for applying a definition to both
       sides of an implication. $)
    3imtr4i $p |- ( ch -> th ) $=
      ( sylbi sylibr ) CBDCABFEHGI $.
      $( [5-Aug-1993] $)
  $}

  ${
    con1bii.1 $e |- ( -. ph <-> ps ) $.
    $( A contraposition inference. $)
    con1bii $p |- ( -. ps <-> ph ) $=
      ( wn biimpi con1i biimpri con2i impbii ) BDAABADZBCEFBAJBCGHI $.
      $( [5-Aug-1993] $)
  $}

  ${
    con2bii.1 $e |- ( ph <-> -. ps ) $.
    $( A contraposition inference. $)
    con2bii $p |- ( ps <-> -. ph ) $=
      ( wn bicomi con1bii ) ADBBAABDCEFE $.
      $( [5-Aug-1993] $)
  $}

  $( For ~ bicon3 :  See ~ notbii . $)

  $( For ~ con4bii :  Later. $)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Logical disjunction and conjunction
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Declare connectives for disjunction ('or') and conjunction ('and'). $)
  $c \/ $. $( Vee (read:  'or') $)
  $c /\ $. $( Wedge (read:  'and') $)

  $( Extend wff definition to include disjunction ('or'). $)
  wo $a wff ( ph \/ ps ) $.
  $( Extend wff definition to include conjunction ('and'). $)
  wa $a wff ( ph /\ ps ) $.

  $( Define disjunction (logical 'or').  This is our first use of the
     biconditional connective in a definition; we use it in place of the
     traditional "<=def=>", which means the same thing, except that we can
     manipulate the biconditional connective directly in proofs rather than
     having to rely on an informal definition substitution rule.  Note that
     if we mechanically substitute ` ( -. ph -> ps ) ` for ` ( ph \/ ps ) ` ,
     we end up with an instance of previously proved theorem ~ biid .  This
     is the justification for the definition, along with the fact that it
     introduces a new symbol ` \/ ` .  Definition of [Margaris] p. 49. $)
  df-or $a |- ( ( ph \/ ps ) <-> ( -. ph -> ps ) ) $.

  $( Define conjunction (logical 'and').  Definition of [Margaris] p. 49. $)
  df-an $a |- ( ( ph /\ ps ) <-> -. ( ph -> -. ps ) ) $.

  $( Theorem *4.64 of [WhiteheadRussell] p. 120. $)
  pm4.64 $p |-  ( ( -. ph -> ps ) <-> ( ph \/ ps ) ) $=
    ( wo wn wi df-or bicomi ) ABCADBEABFG $.
    $( [1-Feb-2005] $) $( [3-Jan-2005] $)

  $( Theorem *2.54 of [WhiteheadRussell] p. 107. $)
  pm2.54 $p |-  ( ( -. ph -> ps ) -> ( ph \/ ps ) ) $=
    ( wo wn wi df-or biimpri ) ABCADBEABFG $.
    $( [10-Feb-2005] $) $( [3-Jan-2005] $)

  $( Theorem *4.63 of [WhiteheadRussell] p. 120. $)
  pm4.63 $p |-  ( -. ( ph -> -. ps ) <-> ( ph /\ ps ) ) $=
    ( wa wn wi df-an bicomi ) ABCABDEDABFG $.
    $( [19-Feb-2005] $) $( [3-Jan-2005] $)

  $( Logical 'or' expressed in terms of implication only.  Theorem *5.25 of
     [WhiteheadRussell] p. 124. $)
  dfor2 $p |- ( ( ph \/ ps ) <-> ( ( ph -> ps ) -> ps ) ) $=
    ( wo wn wi df-or pm2.6 pm2.21 imim1i impbii bitri ) ABCADZBEZABEZBEZABFMOAB
    GLNBABHIJK $.
    $( [20-Aug-2004] $) $( [12-Aug-2004] $)

  ${
    ori.1 $e |- ( ph \/ ps ) $.
    $( Infer implication from disjunction. $)
    ori $p |- ( -. ph -> ps ) $=
      ( wo wn wi df-or mpbi ) ABDAEBFCABGH $.
      $( [11-Jun-1994] $)
  $}

  ${
    orri.1 $e |- ( -. ph -> ps ) $.
    $( Infer implication from disjunction. $)
    orri $p |- ( ph \/ ps ) $=
      ( wo wn wi df-or mpbir ) ABDAEBFCABGH $.
      $( [11-Jun-1994] $)
  $}

  ${
    ord.1 $e |- ( ph -> ( ps \/ ch ) ) $.
    $( Deduce implication from disjunction. $)
    ord $p |- ( ph -> ( -. ps -> ch ) ) $=
      ( wo wn wi df-or sylib ) ABCEBFCGDBCHI $.
      $( [18-May-1994] $)
  $}

  ${
    orrd.1 $e |- ( ph -> ( -. ps -> ch ) ) $.
    $( Deduce implication from disjunction. $)
    orrd $p |- ( ph -> ( ps \/ ch ) ) $=
      ( wn wi wo df-or sylibr ) ABECFBCGDBCHI $.
      $( [27-Nov-1995] $)
  $}

  $( Implication in terms of disjunction.  Theorem *4.6 of
     [WhiteheadRussell] p. 120. $)
  imor $p |- ( ( ph -> ps ) <-> ( -. ph \/ ps ) ) $=
    ( wi wn wo notnot imbi1i df-or bitr4i ) ABCADZDZBCJBEAKBAFGJBHI $.
    $( [5-Aug-1993] $)

  $( Theorem *4.62 of [WhiteheadRussell] p. 120. $)
  pm4.62 $p |-  ( ( ph -> -. ps ) <-> ( -. ph \/ -. ps ) ) $=
    ( wn imor ) ABCD $.
    $( [24-Feb-2005] $) $( [3-Jan-2005] $)

  $( Theorem *4.66 of [WhiteheadRussell] p. 120. $)
  pm4.66 $p |-  ( ( -. ph -> -. ps ) <-> ( ph \/ -. ps ) ) $=
    ( wn pm4.64 ) ABCD $.
    $( [1-Feb-2005] $) $( [3-Jan-2005] $)

  $( Express implication in terms of conjunction.  Theorem 3.4(27) of [Stoll]
     p. 176. $)
  iman $p |- ( ( ph -> ps ) <-> -. ( ph /\ -. ps ) ) $=
    ( wi wn wa notnot imbi2i df-an con2bii bitri ) ABCABDZDZCZAKEZDBLABFGNMAKHI
    J $.
    $( [5-Aug-1993] $)

  $( Express conjunction in terms of implication. $)
  annim $p |- ( ( ph /\ -. ps ) <-> -. ( ph -> ps ) ) $=
    ( wi wn wa iman con2bii ) ABCABDEABFG $.
    $( [2-Aug-1994] $)

  $( Theorem *4.61 of [WhiteheadRussell] p. 120. $)
  pm4.61 $p |-  ( -. ( ph -> ps ) <-> ( ph /\ -. ps ) ) $=
    ( wn wa wi annim bicomi ) ABCDABECABFG $.
    $( [24-Feb-2005] $) $( [3-Jan-2005] $)

  $( Theorem *4.65 of [WhiteheadRussell] p. 120. $)
  pm4.65 $p |-  ( -. ( -. ph -> ps ) <-> ( -. ph /\ -. ps ) ) $=
    ( wn pm4.61 ) ACBD $.
    $( [24-Feb-2005] $) $( [3-Jan-2005] $)

  $( Theorem *4.67 of [WhiteheadRussell] p. 120. $)
  pm4.67 $p |-  ( -. ( -. ph -> -. ps ) <-> ( -. ph /\ ps ) ) $=
    ( wn pm4.63 ) ACBD $.
    $( [27-Feb-2005] $) $( [3-Jan-2005] $)

  $( Express implication in terms of conjunction. $)
  imnan $p |- ( ( ph -> -. ps ) <-> -. ( ph /\ ps ) ) $=
    ( wa wn wi df-an con2bii ) ABCABDEABFG $.
    $( [9-Apr-1994] $)

  $( Idempotent law for disjunction.  Theorem *4.25 of [WhiteheadRussell]
     p. 117. $)
  oridm $p |- ( ( ph \/ ph ) <-> ph ) $=
    ( wo wn wi df-or pm2.24 pm2.18 impbii bitr4i ) AABACADZAAAEAJAAFAGHI $.
    $( [5-Aug-1993] $)

  $( Theorem *4.25 of [WhiteheadRussell] p. 117. $)
  pm4.25 $p |-  ( ph <-> ( ph \/ ph ) ) $=
    ( wo oridm bicomi ) AABAACD $.
    $( [27-Feb-2005] $) $( [3-Jan-2005] $)

  $( Axiom *1.2 (Taut) of [WhiteheadRussell] p. 96. $)
  pm1.2 $p |-  ( ( ph \/ ph ) -> ph ) $=
    ( wo oridm biimpi ) AABAACD $.
    $( [27-Feb-2005] $) $( [3-Jan-2005] $)

  $( Commutative law for disjunction.  Theorem *4.31 of [WhiteheadRussell]
     p. 118. $)
  orcom $p |- ( ( ph \/ ps ) <-> ( ps \/ ph ) ) $=
    ( wn wi wo con1b df-or 3bitr4i ) ACBDBCADABEBAEABFABGBAGH $.
    $( [5-Aug-1993] $)

  $( Axiom *1.4 of [WhiteheadRussell] p. 96. $)
  pm1.4 $p |-  ( ( ph \/ ps ) -> ( ps \/ ph ) ) $=
    ( wo orcom biimpi ) ABCBACABDE $.
    $( [27-Feb-2005] $) $( [3-Jan-2005] $)

  $( Theorem *2.62 of [WhiteheadRussell] p. 107. $)
  pm2.62 $p |-  ( ( ph \/ ps ) -> ( ( ph -> ps ) -> ps ) ) $=
    ( wo wi dfor2 biimpi ) ABCABDBDABEF $.
    $( [6-Jan-2005] $) $( [3-Jan-2005] $)

  $( Theorem *2.621 of [WhiteheadRussell] p. 107. $)
  pm2.621 $p |-  ( ( ph -> ps ) -> ( ( ph \/ ps ) -> ps ) ) $=
    ( wo wi pm2.62 com12 ) ABCABDBABEF $.
    $( [6-Jan-2005] $) $( [3-Jan-2005] $)

  $( Theorem *2.68 of [WhiteheadRussell] p. 108. $)
  pm2.68 $p |-  ( ( ( ph -> ps ) -> ps ) -> ( ph \/ ps ) ) $=
    ( wo wi dfor2 biimpri ) ABCABDBDABEF $.
    $( [27-Feb-2005] $) $( [3-Jan-2005] $)

  $( Elimination of disjunction by denial of a disjunct.  Theorem *2.55 of
     [WhiteheadRussell] p. 107. $)
  orel1 $p |- ( -. ph -> ( ( ph \/ ps ) -> ps ) ) $=
    ( wo wn wi df-or biimpi com12 ) ABCZADZBIJBEABFGH $.
    $( [12-Aug-1994] $)

  $( Elimination of disjunction by denial of a disjunct.  Theorem *2.56 of
     [WhiteheadRussell] p. 107. $)
  orel2 $p |- ( -. ph -> ( ( ps \/ ph ) -> ps ) ) $=
    ( wn wo orel1 orcom syl5ib ) ACABDBBADABEBAFG $.
    $( [12-Aug-1994] $)

  $( Theorem *2.25 of [WhiteheadRussell] p. 104. $)
  pm2.25 $p |-  ( ph \/ ( ( ph \/ ps ) -> ps ) ) $=
    ( wo wi orel1 orri ) AABCBDABEF $.
    $( [1-Mar-2005] $) $( [3-Jan-2005] $)

  $( Theorem *2.53 of [WhiteheadRussell] p. 107. $)
  pm2.53 $p |-  ( ( ph \/ ps ) -> ( -. ph -> ps ) ) $=
    ( wn wo orel1 com12 ) ACABDBABEF $.
    $( [1-Mar-2005] $) $( [3-Jan-2005] $)

  ${
    orbi2i.1 $e |- ( ph <-> ps ) $.

    $( Inference adding a left disjunct to both sides of a logical
       equivalence. $)
    orbi2i $p |- ( ( ch \/ ph ) <-> ( ch \/ ps ) ) $=
      ( wn wi wo imbi2i df-or 3bitr4i ) CEZAFKBFCAGCBGABKDHCAICBIJ $.
      $( [5-Aug-1993] $)

    $( Inference adding a right disjunct to both sides of a logical
       equivalence. $)
    orbi1i $p |- ( ( ph \/ ch ) <-> ( ps \/ ch ) ) $=
      ( wo orcom orbi2i 3bitri ) ACECAECBEBCEACFABCDGCBFH $.
      $( [5-Aug-1993] $)

  $}

  ${
    orbi12i.1 $e |- ( ph <-> ps ) $.
    orbi12i.2 $e |- ( ch <-> th ) $.
    $( Infer the disjunction of two equivalences. $)
    orbi12i $p |- ( ( ph \/ ch ) <-> ( ps \/ th ) ) $=
      ( wo orbi2i orbi1i bitri ) ACGADGBDGCDAFHABDEIJ $.
      $( [5-Aug-1993] $)
  $}

  $( A rearrangement of disjuncts. $)
  or12 $p |- ( ( ph \/ ( ps \/ ch ) ) <-> ( ps \/ ( ph \/ ch ) ) ) $=
    ( wn wo wi bi2.04 df-or imbi2i 3bitr4ri 3bitr4i ) ADZBCEZFZBDZACEZFZAMEBPEO
    LCFZFLOCFZFQNOLCGPROACHIMSLBCHIJAMHBPHK $.
    $( [5-Aug-1993] $)

  $( Axiom *1.5 (Assoc) of [WhiteheadRussell] p. 96. $)
  pm1.5 $p |-  ( ( ph \/ ( ps \/ ch ) ) -> ( ps \/ ( ph \/ ch ) ) ) $=
    ( wo or12 biimpi ) ABCDDBACDDABCEF $.
    $( [1-Mar-2005] $) $( [3-Jan-2005] $)

  $( Associative law for disjunction.  Theorem *4.33 of [WhiteheadRussell]
     p. 118. $)
  orass $p |- ( ( ( ph \/ ps ) \/ ch ) <-> ( ph \/ ( ps \/ ch ) ) ) $=
    ( wo or12 orcom orbi2i 3bitr4i ) CABDZDACBDZDICDABCDZDCABEICFKJABCFGH $.
    $( [5-Aug-1993] $)

  $( Theorem *2.31 of [WhiteheadRussell] p. 104. $)
  pm2.31 $p |-  ( ( ph \/ ( ps \/ ch ) ) -> ( ( ph \/ ps ) \/ ch ) ) $=
    ( wo orass biimpri ) ABDCDABCDDABCEF $.
    $( [2-Mar-2005] $) $( [3-Jan-2005] $)

  $( Theorem *2.32 of [WhiteheadRussell] p. 105. $)
  pm2.32 $p |-  ( ( ( ph \/ ps ) \/ ch ) -> ( ph \/ ( ps \/ ch ) ) ) $=
    ( wo orass biimpi ) ABDCDABCDDABCEF $.
    $( [6-Mar-2005] $) $( [3-Jan-2005] $)

  $( A rearrangement of disjuncts. $)
  or23 $p |- ( ( ( ph \/ ps ) \/ ch ) <-> ( ( ph \/ ch ) \/ ps ) ) $=
    ( wo orcom orbi2i orass 3bitr4i ) ABCDZDACBDZDABDCDACDBDIJABCEFABCGACBGH $.
    $( [18-Oct-1995] $)

  $( Rearrangement of 4 disjuncts. $)
  or4 $p |- ( ( ( ph \/ ps ) \/ ( ch \/ th ) ) <->
                ( ( ph \/ ch ) \/ ( ps \/ th ) ) ) $=
    ( wo or12 orbi2i orass 3bitr4i ) ABCDEZEZEACBDEZEZEABEJEACELEKMABCDFGABJHAC
    LHI $.
    $( [12-Aug-1994] $)

  $( Rearrangement of 4 disjuncts. $)
  or42 $p |- ( ( ( ph \/ ps ) \/ ( ch \/ th ) ) <->
                 ( ( ph \/ ch ) \/ ( th \/ ps ) ) ) $=
    ( wo or4 orcom orbi2i bitri ) ABECDEEACEZBDEZEJDBEZEABCDFKLJBDGHI $.
    $( [11-Jan-2005] $) $( [10-Jan-2005] $)

  $( Distribution of disjunction over disjunction. $)
  orordi $p |- ( ( ph \/ ( ps \/ ch ) ) <->
               ( ( ph \/ ps ) \/ ( ph \/ ch ) ) ) $=
    ( wo oridm orbi1i or4 bitr3i ) ABCDZDAADZIDABDACDDJAIAEFAABCGH $.
    $( [25-Feb-1995] $)

  $( Distribution of disjunction over disjunction. $)
  orordir $p |- ( ( ( ph \/ ps ) \/ ch ) <->
               ( ( ph \/ ch ) \/ ( ps \/ ch ) ) ) $=
    ( wo oridm orbi2i or4 bitr3i ) ABDZCDICCDZDACDBCDDJCICEFABCCGH $.
    $( [25-Feb-1995] $)

  $( Introduction of a disjunct.  Axiom *1.3 of [WhiteheadRussell] p. 96. $)
  olc $p |- ( ph -> ( ps \/ ph ) ) $=
    ( wn ax-1 orrd ) ABAABCDE $.
    $( [30-Aug-1993] $)

  $( Introduction of a disjunct.  Theorem *2.2 of [WhiteheadRussell] p. 104. $)
  orc $p |- ( ph -> ( ph \/ ps ) ) $=
    ( pm2.24 orrd ) AABABCD $.
    $( [30-Aug-1993] $)

  ${
    orci.1 $e |- ph $.
    $( Deduction introducing a disjunct. $)
    orci $p |- ( ph \/ ps ) $=
      ( wo orc ax-mp ) AABDCABEF $.
      $( [20-Jan-2008] $) $( [19-Jan-2008] $)

    $( Deduction introducing a disjunct. $)
    olci $p |- ( ps \/ ph ) $=
      ( wo olc ax-mp ) ABADCABEF $.
      $( [20-Jan-2008] $) $( [19-Jan-2008] $)
  $}

  ${
    orcd.1 $e |- ( ph -> ps ) $.
    $( Deduction introducing a disjunct. $)
    orcd $p |- ( ph -> ( ps \/ ch ) ) $=
      ( wo orc syl ) ABBCEDBCFG $.
      $( [19-Feb-2008] $) $( [20-Sep-2007] $)

    $( Deduction introducing a disjunct. $)
    olcd $p |- ( ph -> ( ch \/ ps ) ) $=
      ( wo olc syl ) ABCBEDBCFG $.
      $( [11-Apr-2008] $) $( [11-Apr-2008] $)
  $}

  ${
    orcs.1 $e |- ( ( ph \/ ps ) -> ch ) $.
    $( Deduction eliminating disjunct. $)
    orcs $p |- ( ph -> ch ) $=
      ( wo orc syl ) AABECABFDG $.
      $( [21-Jun-1994] $)
  $}

  ${
    olcs.1 $e |- ( ( ph \/ ps ) -> ch ) $.
    $( Deduction eliminating disjunct. $)
    olcs $p |- ( ps -> ch ) $=
      ( wo olc syl ) BABECBAFDG $.
      $( [21-Jun-1994] $)
  $}

  $( Theorem *2.07 of [WhiteheadRussell] p. 101. $)
  pm2.07 $p |-  ( ph -> ( ph \/ ph ) ) $=
    ( olc ) AAB $.
    $( [6-Mar-2005] $) $( [3-Jan-2005] $)

  $( Theorem *2.45 of [WhiteheadRussell] p. 106. $)
  pm2.45 $p |-  ( -. ( ph \/ ps ) -> -. ph ) $=
    ( wo orc con3i ) AABCABDE $.
    $( [8-Jan-2005] $) $( [3-Jan-2005] $)

  $( Theorem *2.46 of [WhiteheadRussell] p. 106. $)
  pm2.46 $p |-  ( -. ( ph \/ ps ) -> -. ps ) $=
    ( wo olc con3i ) BABCBADE $.
    $( [8-Jan-2005] $) $( [3-Jan-2005] $)

  $( Theorem *2.47 of [WhiteheadRussell] p. 107. $)
  pm2.47 $p |-  ( -. ( ph \/ ps ) -> ( -. ph \/ ps ) ) $=
    ( wo wn pm2.45 orcd ) ABCDADBABEF $.
    $( [6-Mar-2005] $) $( [3-Jan-2005] $)

  $( Theorem *2.48 of [WhiteheadRussell] p. 107. $)
  pm2.48 $p |-  ( -. ( ph \/ ps ) -> ( ph \/ -. ps ) ) $=
    ( wo wn pm2.46 olcd ) ABCDBDAABEF $.
    $( [9-Jan-2005] $) $( [3-Jan-2005] $)

  $( Theorem *2.49 of [WhiteheadRussell] p. 107. $)
  pm2.49 $p |-  ( -. ( ph \/ ps ) -> ( -. ph \/ -. ps ) ) $=
    ( wo wn pm2.46 olcd ) ABCDBDADABEF $.
    $( [7-Mar-2005] $) $( [3-Jan-2005] $)

  $( Theorem *2.67 of [WhiteheadRussell] p. 107. $)
  pm2.67 $p |-  ( ( ( ph \/ ps ) -> ps ) -> ( ph -> ps ) ) $=
    ( wo orc imim1i ) AABCBABDE $.
    $( [6-Jan-2005] $) $( [3-Jan-2005] $)

  $( Join antecedents with conjunction.  Theorem *3.2 of [WhiteheadRussell]
     p. 111. $)
  pm3.2 $p |- ( ph -> ( ps -> ( ph /\ ps ) ) ) $=
    ( wa wn wi df-an biimpri expi ) ABABCZIABDEDABFGH $.
    $( [5-Aug-1993] $)

  $( Join antecedents with conjunction.  Theorem *3.21 of
     [WhiteheadRussell] p. 111. $)
  pm3.21 $p |- ( ph -> ( ps -> ( ps /\ ph ) ) ) $=
    ( wa pm3.2 com12 ) BABACBADE $.
    $( [5-Aug-1993] $)

  ${
    pm3.2i.1 $e |- ph $.
    pm3.2i.2 $e |- ps $.
    $( Infer conjunction of premises. $)
    pm3.2i $p |- ( ph /\ ps ) $=
      ( wa pm3.2 mp2 ) ABABECDABFG $.
      $( [5-Aug-1993] $)
  $}

  $( Theorem *3.37 (Transp) of [WhiteheadRussell] p. 112. $)
  pm3.37 $p |-  ( ( ( ph /\ ps ) -> ch ) -> ( ( ph /\ -. ch ) -> -. ps ) ) $=
    ( wa wi wn pm3.21 imim1d com12 iman syl6ib con2d ) ABDZCEZBACFDZNBACEZOFBNP
    BAMCBAGHIACJKL $.
    $( [7-Mar-2005] $) $( [3-Jan-2005] $)

  $( Nested conjunction of antecedents. $)
  pm3.43i $p |- ( ( ph -> ps ) ->
                ( ( ph -> ch ) -> ( ph -> ( ps /\ ch ) ) ) ) $=
    ( wa pm3.2 imim3i ) BCBCDABCEF $.
    $( [5-Aug-1993] $)

  ${
    jca.1 $e |- ( ph -> ps ) $.
    jca.2 $e |- ( ph -> ch ) $.
    $( Deduce conjunction of the consequents of two implications ("join
       consequents with 'and'"). $)
    jca $p |- ( ph -> ( ps /\ ch ) ) $=
      ( wn wi wa jc df-an sylibr ) ABCFGFBCHABCDEIBCJK $.
      $( [5-Aug-1993] $)
  $}

  ${
    jca31.1 $e |- ( ph -> ps ) $.
    jca31.2 $e |- ( ph -> ch ) $.
    jca31.3 $e |- ( ph -> th ) $.
    $( Join three consequents.  (Contributed by Jeff Hankins, 1-Aug-2009.) $)
    jca31 $p |- ( ph -> ( ( ps /\ ch ) /\ th ) ) $=
      ( wa jca ) ABCHDABCEFIGI $.
      $( [18-Apr-2010] $) $( [1-Aug-2009] $)

    $( Join three consequents.  (Contributed by FL, 1-Aug-2009.) $)
    jca32 $p |- ( ph -> ( ps /\ ( ch /\ th ) ) ) $=
      ( wa jca ) ABCDHEACDFGII $.
      $( [18-Apr-2010] $) $( [1-Aug-2009] $)
  $}

  ${
    jcai.1 $e |- ( ph -> ps ) $.
    jcai.2 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction replacing implication with conjunction. $)
    jcai $p |- ( ph -> ( ps /\ ch ) ) $=
      ( mpd jca ) ABCDABCDEFG $.
      $( [5-Aug-1993] $)
  $}

  ${
    jctl.1 $e |- ps $.
    $( Inference conjoining a theorem to the left of a consequent. $)
    jctl $p |- ( ph -> ( ps /\ ph ) ) $=
      ( a1i id jca ) ABABACDAEF $.
      $( [31-Dec-1993] $)
  $}

  ${
    jctr.1 $e |- ps $.
    $( Inference conjoining a theorem to the right of a consequent. $)
    jctr $p |- ( ph -> ( ph /\ ps ) ) $=
      ( id a1i jca ) AABADBACEF $.
      $( [18-Aug-1993] $)
  $}

  ${
    jctil.1 $e |- ( ph -> ps ) $.
    jctil.2 $e |- ch $.
    $( Inference conjoining a theorem to left of consequent in an
       implication. $)
    jctil $p |- ( ph -> ( ch /\ ps ) ) $=
      ( a1i jca ) ACBCAEFDG $.
      $( [31-Dec-1993] $)
  $}

  ${
    jctir.1 $e |- ( ph -> ps ) $.
    jctir.2 $e |- ch $.
    $( Inference conjoining a theorem to right of consequent in an
       implication. $)
    jctir $p |- ( ph -> ( ps /\ ch ) ) $=
      ( a1i jca ) ABCDCAEFG $.
      $( [31-Dec-1993] $)
  $}

  $( Conjoin antecedent to left of consequent. $)
  ancl $p |- ( ( ph -> ps ) -> ( ph -> ( ph /\ ps ) ) ) $=
    ( wa pm3.2 a2i ) ABABCABDE $.
    $( [15-Aug-1994] $)

  $( Conjoin antecedent to right of consequent. $)
  ancr $p |- ( ( ph -> ps ) -> ( ph -> ( ps /\ ph ) ) ) $=
    ( wa pm3.21 a2i ) ABBACABDE $.
    $( [15-Aug-1994] $)

  ${
    ancli.1 $e |- ( ph -> ps ) $.
    $( Deduction conjoining antecedent to left of consequent. $)
    ancli $p |- ( ph -> ( ph /\ ps ) ) $=
      ( id jca ) AABADCE $.
      $( [12-Aug-1993] $)
  $}

  ${
    ancri.1 $e |- ( ph -> ps ) $.
    $( Deduction conjoining antecedent to right of consequent. $)
    ancri $p |- ( ph -> ( ps /\ ph ) ) $=
      ( id jca ) ABACADE $.
      $( [15-Aug-1994] $)
  $}

  ${
    ancld.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction conjoining antecedent to left of consequent in nested
       implication. $)
    ancld $p |- ( ph -> ( ps -> ( ps /\ ch ) ) ) $=
      ( wi wa ancl syl ) ABCEBBCFEDBCGH $.
      $( [15-Aug-1994] $)
  $}

  ${
    ancrd.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction conjoining antecedent to right of consequent in nested
       implication. $)
    ancrd $p |- ( ph -> ( ps -> ( ch /\ ps ) ) ) $=
      ( wi wa ancr syl ) ABCEBCBFEDBCGH $.
      $( [15-Aug-1994] $)
  $}

  $( Conjoin antecedent to left of consequent in nested implication. $)
  anc2l $p |- ( ( ph -> ( ps -> ch ) ) -> ( ph -> ( ps -> ( ph /\ ch ) ) ) ) $=
    ( wi wa pm3.2 imim2d a2i ) ABCDBACEZDACIBACFGH $.
    $( [10-Aug-1994] $)

  $( Conjoin antecedent to right of consequent in nested implication. $)
  anc2r $p |- ( ( ph -> ( ps -> ch ) ) -> ( ph -> ( ps -> ( ch /\ ph ) ) ) ) $=
    ( wi wa pm3.21 imim2d a2i ) ABCDBCAEZDACIBACFGH $.
    $( [15-Aug-1994] $)

  ${
    anc2li.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction conjoining antecedent to left of consequent in nested
       implication. $)
    anc2li $p |- ( ph -> ( ps -> ( ph /\ ch ) ) ) $=
      ( wi wa anc2l ax-mp ) ABCEEABACFEEDABCGH $.
      $( [10-Aug-1994] $)
  $}

  ${
    anc2ri.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction conjoining antecedent to right of consequent in nested
       implication. $)
    anc2ri $p |- ( ph -> ( ps -> ( ch /\ ph ) ) ) $=
      ( wi wa anc2r ax-mp ) ABCEEABCAFEEDABCGH $.
      $( [15-Aug-1994] $)
  $}

  $( Conjunction in terms of disjunction (DeMorgan's law).  Theorem *4.5 of
     [WhiteheadRussell] p. 120. $)
  anor $p |- ( ( ph /\ ps ) <-> -. ( -. ph \/ -. ps ) ) $=
    ( wa wn wi wo df-an pm4.62 notbii bitri ) ABCABDZEZDADKFZDABGLMABHIJ $.
    $( [5-Aug-1993] $)

  $( Negated conjunction in terms of disjunction (DeMorgan's law).  Theorem
     *4.51 of [WhiteheadRussell] p. 120. $)
  ianor $p |- ( -. ( ph /\ ps ) <-> ( -. ph \/ -. ps ) ) $=
    ( wa wn wo anor notbii notnot bitr4i ) ABCZDADBDEZDZDKJLABFGKHI $.
    $( [5-Aug-1993] $)

  $( Negated disjunction in terms of conjunction (DeMorgan's law).  Compare
     Theorem *4.56 of [WhiteheadRussell] p. 120. $)
  ioran $p |- ( -. ( ph \/ ps ) <-> ( -. ph /\ -. ps ) ) $=
    ( wo wn wa notnot orbi12i notbii anor bitr4i ) ABCZDADZDZBDZDZCZDLNEKPAMBOA
    FBFGHLNIJ $.
    $( [5-Aug-1993] $)

  $( Theorem *4.52 of [WhiteheadRussell] p. 120. $)
  pm4.52 $p |-  ( ( ph /\ -. ps ) <-> -. ( -. ph \/ ps ) ) $=
    ( wn wa wo anor notnot orbi2i notbii bitr4i ) ABCZDACZKCZEZCLBEZCAKFONBMLBG
    HIJ $.
    $( [11-Mar-2005] $) $( [3-Jan-2005] $)

  $( Theorem *4.53 of [WhiteheadRussell] p. 120. $)
  pm4.53 $p |-  ( -. ( ph /\ -. ps ) <-> ( -. ph \/ ps ) ) $=
    ( wn wo wa pm4.52 con2bii bicomi ) ACBDZABCEZCJIABFGH $.
    $( [11-Mar-2005] $) $( [3-Jan-2005] $)

  $( Theorem *4.54 of [WhiteheadRussell] p. 120. $)
  pm4.54 $p |-  ( ( -. ph /\ ps ) <-> -. ( ph \/ -. ps ) ) $=
    ( wn wa wo anor notnot orbi1i notbii bitr4i ) ACZBDKCZBCZEZCAMEZCKBFONALMAG
    HIJ $.
    $( [11-Mar-2005] $) $( [3-Jan-2005] $)

  $( Theorem *4.55 of [WhiteheadRussell] p. 120. $)
  pm4.55 $p |-  ( -. ( -. ph /\ ps ) <-> ( ph \/ -. ps ) ) $=
    ( wn wo wa pm4.54 con2bii bicomi ) ABCDZACBEZCJIABFGH $.
    $( [11-Mar-2005] $) $( [3-Jan-2005] $)

  $( Theorem *4.56 of [WhiteheadRussell] p. 120. $)
  pm4.56 $p |-  ( ( -. ph /\ -. ps ) <-> -. ( ph \/ ps ) ) $=
    ( wo wn wa ioran bicomi ) ABCDADBDEABFG $.
    $( [11-Mar-2005] $) $( [3-Jan-2005] $)

  $( Disjunction in terms of conjunction (DeMorgan's law).  Compare Theorem
     *4.57 of [WhiteheadRussell] p. 120. $)
  oran $p |- ( ( ph \/ ps ) <-> -. ( -. ph /\ -. ps ) ) $=
    ( wo wn wa notnot ioran notbii bitri ) ABCZJDZDADBDEZDJFKLABGHI $.
    $( [5-Aug-1993] $)

  $( Theorem *4.57 of [WhiteheadRussell] p. 120. $)
  pm4.57 $p |-  ( -. ( -. ph /\ -. ps ) <-> ( ph \/ ps ) ) $=
    ( wo wn wa oran bicomi ) ABCADBDEDABFG $.
    $( [11-Mar-2005] $) $( [3-Jan-2005] $)

  $( Theorem *3.1 of [WhiteheadRussell] p. 111. $)
  pm3.1 $p |-  ( ( ph /\ ps ) -> -. ( -. ph \/ -. ps ) ) $=
    ( wa wn wo anor biimpi ) ABCADBDEDABFG $.
    $( [21-Mar-2005] $) $( [3-Jan-2005] $)

  $( Theorem *3.11 of [WhiteheadRussell] p. 111. $)
  pm3.11 $p |-  ( -. ( -. ph \/ -. ps ) -> ( ph /\ ps ) ) $=
    ( wa wn wo anor biimpri ) ABCADBDEDABFG $.
    $( [25-Mar-2005] $) $( [3-Jan-2005] $)

  $( Theorem *3.12 of [WhiteheadRussell] p. 111. $)
  pm3.12 $p |-  ( ( -. ph \/ -. ps ) \/ ( ph /\ ps ) ) $=
    ( wn wo wa pm3.11 orri ) ACBCDABEABFG $.
    $( [25-Mar-2005] $) $( [3-Jan-2005] $)

  $( Theorem *3.13 of [WhiteheadRussell] p. 111. $)
  pm3.13 $p |-  ( -. ( ph /\ ps ) -> ( -. ph \/ -. ps ) ) $=
    ( wn wo wa pm3.11 con1i ) ACBCDABEABFG $.
    $( [25-Mar-2005] $) $( [3-Jan-2005] $)

  $( Theorem *3.14 of [WhiteheadRussell] p. 111. $)
  pm3.14 $p |-  ( ( -. ph \/ -. ps ) -> -. ( ph /\ ps ) ) $=
    ( wa wn wo pm3.1 con2i ) ABCADBDEABFG $.
    $( [25-Mar-2005] $) $( [3-Jan-2005] $)

  $( Elimination of a conjunct.  Theorem *3.26 (Simp) of [WhiteheadRussell]
     p. 112. $)
  pm3.26 $p |- ( ( ph /\ ps ) -> ph ) $=
    ( wa wn wi df-an pm3.26im sylbi ) ABCABDEDAABFABGH $.
    $( [5-Aug-1993] $)

  ${
    pm3.26i.1 $e |- ( ph /\ ps ) $.
    $( Inference eliminating a conjunct. $)
    pm3.26i $p |- ph $=
      ( wa pm3.26 ax-mp ) ABDACABEF $.
      $( [15-Jun-1994] $)
  $}

  ${
    pm3.26d.1 $e |- ( ph -> ( ps /\ ch ) ) $.
    $( Deduction eliminating a conjunct. $)
    pm3.26d $p |- ( ph -> ps ) $=
      ( wa pm3.26 syl ) ABCEBDBCFG $.
      $( [5-Aug-1993] $)
  $}

  ${
    pm3.26bi.1 $e |- ( ph <-> ( ps /\ ch ) ) $.
    $( Deduction eliminating a conjunct. $)
    pm3.26bi $p |- ( ph -> ps ) $=
      ( wa biimpi pm3.26d ) ABCABCEDFG $.
      $( [27-May-1998] $)
  $}

  $( Elimination of a conjunct.  Theorem *3.27 (Simp) of [WhiteheadRussell]
     p. 112. $)
  pm3.27 $p |- ( ( ph /\ ps ) -> ps ) $=
    ( wa wn wi df-an pm3.27im sylbi ) ABCABDEDBABFABGH $.
    $( [5-Aug-1993] $)

  ${
    pm3.27i.1 $e |- ( ph /\ ps ) $.
    $( Inference eliminating a conjunct. $)
    pm3.27i $p |- ps $=
      ( wa pm3.27 ax-mp ) ABDBCABEF $.
      $( [15-Jun-1994] $)
  $}

  ${
    pm3.27d.1 $e |- ( ph -> ( ps /\ ch ) ) $.
    $( Deduction eliminating a conjunct. $)
    pm3.27d $p |- ( ph -> ch ) $=
      ( wa pm3.27 syl ) ABCECDBCFG $.
      $( [5-Aug-1993] $)
  $}

  ${
    pm3.27bi.1 $e |- ( ph <-> ( ps /\ ch ) ) $.
    $( Deduction eliminating a conjunct. $)
    pm3.27bi $p |- ( ph -> ch ) $=
      ( wa biimpi pm3.27d ) ABCABCEDFG $.
      $( [27-May-1998] $)
  $}

  $( Theorem *3.41 of [WhiteheadRussell] p. 113. $)
  pm3.41 $p |-  ( ( ph -> ch ) -> ( ( ph /\ ps ) -> ch ) ) $=
    ( wa pm3.26 imim1i ) ABDACABEF $.
    $( [21-Mar-2005] $) $( [3-Jan-2005] $)

  $( Theorem *3.42 of [WhiteheadRussell] p. 113. $)
  pm3.42 $p |-  ( ( ps -> ch ) -> ( ( ph /\ ps ) -> ch ) ) $=
    ( wa pm3.27 imim1i ) ABDBCABEF $.
    $( [27-Mar-2005] $) $( [3-Jan-2005] $)

  $( Conjoin antecedent to left of consequent.  Theorem *4.7 of
     [WhiteheadRussell] p. 120. $)
  anclb $p |- ( ( ph -> ps ) <-> ( ph -> ( ph /\ ps ) ) ) $=
    ( wi wa ancl pm3.27 imim2i impbii ) ABCAABDZCABEIBAABFGH $.
    $( [25-Jul-1999] $)

  $( Conjoin antecedent to right of consequent. $)
  ancrb $p |- ( ( ph -> ps ) <-> ( ph -> ( ps /\ ph ) ) ) $=
    ( wi wa ancr pm3.26 imim2i impbii ) ABCABADZCABEIBABAFGH $.
    $( [25-Jul-1999] $)

  $( Conjunction implies implication.  Theorem *3.4 of [WhiteheadRussell]
     p. 113. $)
  pm3.4 $p |- ( ( ph /\ ps ) -> ( ph -> ps ) ) $=
    ( wa pm3.27 a1d ) ABCBAABDE $.
    $( [31-Jul-1995] $)

  $( Conjunction with implication.  Compare Theorem *4.45 of
     [WhiteheadRussell] p. 119. $)
  pm4.45im $p |- ( ph <-> ( ph /\ ( ps -> ph ) ) ) $=
    ( wi wa ax-1 ancli pm3.26 impbii ) AABACZDAIABEFAIGH $.
    $( [17-May-1998] $)

  ${
    anim12i.1 $e |- ( ph -> ps ) $.
    anim12i.2 $e |- ( ch -> th ) $.
    $( Conjoin antecedents and consequents of two premises. $)
    anim12i $p |- ( ( ph /\ ch ) -> ( ps /\ th ) ) $=
      ( wa pm3.26 syl pm3.27 jca ) ACGZBDLABACHEILCDACJFIK $.
      $( [5-Aug-1993] $)
  $}

  ${
    anim1i.1 $e |- ( ph -> ps ) $.
    $( Introduce conjunct to both sides of an implication. $)
    anim1i $p |- ( ( ph /\ ch ) -> ( ps /\ ch ) ) $=
      ( id anim12i ) ABCCDCEF $.
      $( [5-Aug-1993] $)

    $( Introduce conjunct to both sides of an implication. $)
    anim2i $p |- ( ( ch /\ ph ) -> ( ch /\ ps ) ) $=
      ( id anim12i ) CCABCEDF $.
      $( [5-Aug-1993] $)
  $}

  ${
    orim12i.1 $e |- ( ph -> ps ) $.
    orim12i.2 $e |- ( ch -> th ) $.
    $( Disjoin antecedents and consequents of two premises. $)
    orim12i $p |- ( ( ph \/ ch ) -> ( ps \/ th ) ) $=
      ( wn wa wo con3i anim12i oran 3imtr4i ) AGZCGZHZGBGZDGZHZGACIBDISPQNROABE
      JCDFJKJACLBDLM $.
      $( [6-Jun-1994] $)
  $}

  ${
    orim1i.1 $e |- ( ph -> ps ) $.
    $( Introduce disjunct to both sides of an implication. $)
    orim1i $p |- ( ( ph \/ ch ) -> ( ps \/ ch ) ) $=
      ( id orim12i ) ABCCDCEF $.
      $( [6-Jun-1994] $)

    $( Introduce disjunct to both sides of an implication. $)
    orim2i $p |- ( ( ch \/ ph ) -> ( ch \/ ps ) ) $=
      ( id orim12i ) CCABCEDF $.
      $( [6-Jun-1994] $)
  $}

  $( Theorem *2.3 of [WhiteheadRussell] p. 104. $)
  pm2.3 $p |-  ( ( ph \/ ( ps \/ ch ) ) -> ( ph \/ ( ch \/ ps ) ) ) $=
    ( wo pm1.4 orim2i ) BCDCBDABCEF $.
    $( [2-Apr-2005] $) $( [3-Jan-2005] $)

  $( Disjunction of antecedents.  Compare Theorem *3.44 of
     [WhiteheadRussell] p. 113. $)
  jao $p |- ( ( ph -> ps ) -> ( ( ch -> ps ) -> ( ( ph \/ ch ) -> ps ) ) ) $=
    ( wi wn wo con3 wa pm3.43i con1 syl6 oran syl7ib syl5 syl ) ABDBEZAEZDZCBDZ
    ACFZBDZDABGRPCEZDZUASRUCQUBHZEZBTRUCPUDDUEBDPQUBIBUDJKACLMCBGNO $.
    $( [5-Apr-1994] $)

  ${
    jaoi.1 $e |- ( ph -> ps ) $.
    jaoi.2 $e |- ( ch -> ps ) $.
    $( Inference disjoining the antecedents of two implications. $)
    jaoi $p |- ( ( ph \/ ch ) -> ps ) $=
      ( wi wo jao mp2 ) ABFCBFACGBFDEABCHI $.
      $( [5-Apr-1994] $)
  $}

  $( Theorem *2.41 of [WhiteheadRussell] p. 106. $)
  pm2.41 $p |-  ( ( ps \/ ( ph \/ ps ) ) -> ( ph \/ ps ) ) $=
    ( wo olc id jaoi ) BABCZGBADGEF $.
    $( [2-Apr-2005] $) $( [3-Jan-2005] $)

  $( Theorem *2.42 of [WhiteheadRussell] p. 106. $)
  pm2.42 $p |-  ( ( -. ph \/ ( ph -> ps ) ) -> ( ph -> ps ) ) $=
    ( wn wi pm2.21 id jaoi ) ACABDZHABEHFG $.
    $( [2-Apr-2005] $) $( [3-Jan-2005] $)

  $( Theorem *2.4 of [WhiteheadRussell] p. 106. $)
  pm2.4 $p |-  ( ( ph \/ ( ph \/ ps ) ) -> ( ph \/ ps ) ) $=
    ( wo orc id jaoi ) AABCZGABDGEF $.
    $( [2-Apr-2005] $) $( [3-Jan-2005] $)

  $( Theorem *4.44 of [WhiteheadRussell] p. 119. $)
  pm4.44 $p |-  ( ph <-> ( ph \/ ( ph /\ ps ) ) ) $=
    ( wa wo orc id pm3.26 jaoi impbii ) AAABCZDAJEAAJAFABGHI $.
    $( [2-Apr-2005] $) $( [3-Jan-2005] $)

  $( Theorem *5.63 of [WhiteheadRussell] p. 125. $)
  pm5.63 $p |-  ( ( ph \/ ps ) <-> ( ph \/ ( -. ph /\ ps ) ) ) $=
    ( wo wn wa pm2.53 ancld orrd wi pm2.24 pm3.4 jaoi impbii ) ABCZAADZBEZCZNAP
    NOBABFGHQABAOBIPABJOBKLHM $.
    $( [2-Apr-2005] $) $( [3-Jan-2005] $)

  $( Import-export theorem.  Part of Theorem *4.87 of [WhiteheadRussell]
     p. 122. $)
  impexp $p |- ( ( ( ph /\ ps ) -> ch ) <-> ( ph -> ( ps -> ch ) ) ) $=
    ( wa wi wn df-an imbi1i expt impt impbii bitri ) ABDZCEABFEFZCEZABCEEZMNCAB
    GHOPABCIABCJKL $.
    $( [5-Aug-1993] $)

  $( Theorem *3.3 (Exp) of [WhiteheadRussell] p. 112. $)
  pm3.3 $p |-  ( ( ( ph /\ ps ) -> ch ) -> ( ph -> ( ps -> ch ) ) ) $=
    ( wa wi impexp biimpi ) ABDCEABCEEABCFG $.
    $( [10-Apr-2005] $) $( [3-Jan-2005] $)

  $( Theorem *3.31 (Imp) of [WhiteheadRussell] p. 112. $)
  pm3.31 $p |-  ( ( ph -> ( ps -> ch ) ) -> ( ( ph /\ ps ) -> ch ) ) $=
    ( wa wi impexp biimpri ) ABDCEABCEEABCFG $.
    $( [14-Apr-2005] $) $( [3-Jan-2005] $)

  ${
    imp.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Importation inference.  (The proof was shortened by Eric Schmidt,
       22-Dec-2006.) $)
    imp $p |- ( ( ph /\ ps ) -> ch ) $=
      ( wa wi impexp mpbir ) ABECFABCFFDABCGH $.
      $( [22-Dec-2006] $) $( [5-Aug-1993] $)

    $( Importation inference with commuted antecedents. $)
    impcom $p |- ( ( ps /\ ph ) -> ch ) $=
      ( com12 imp ) BACABCDEF $.
      $( [26-May-2005] $) $( [25-May-2005] $)
  $}

  $( Theorem *4.14 of [WhiteheadRussell] p. 117. $)
  pm4.14 $p |-  ( ( ( ph /\ ps ) -> ch ) <-> ( ( ph /\ -. ch ) -> -. ps ) ) $=
    ( wa wi wn impexp bi2.04 bitri iman imbi2i con2b 3bitri ) ABDCEZBACEZEZBACF
    DZFZEQBFENABCEEPABCGABCHIORBACJKBQLM $.
    $( [11-Apr-2005] $) $( [3-Jan-2005] $)

  $( Theorem *4.15 of [WhiteheadRussell] p. 117. $)
  pm4.15 $p |-  ( ( ( ph /\ ps ) -> -. ch ) <-> ( ( ps /\ ch ) -> -. ph ) ) $=
    ( wa wn wi impexp imnan imbi2i con2b 3bitri ) ABDCEZFABLFZFABCDZEZFNAEFABLG
    MOABCHIANJK $.
    $( [11-Apr-2005] $) $( [3-Jan-2005] $)

  $( Theorem *4.78 of [WhiteheadRussell] p. 121. $)
  pm4.78 $p |-  ( ( ( ph -> ps ) \/ ( ph -> ch ) ) <->
                ( ph -> ( ps \/ ch ) ) ) $=
    ( wi wn wo wa impexp annim imbi1i bi2.04 imbi2i pm5.4 bitri 3bitr3i df-or 
    3bitr4i ) ABDZEZACDZDZABEZCDZDZRTFABCFZDAUBGZTDAUBTDZDZUAUDAUBTHUFSTABIJUHA
    UDDUDUGUDAUBACKLAUCMNORTPUEUCABCPLQ $.
    $( [10-Apr-2005] $) $( [3-Jan-2005] $)

  $( Theorem *4.79 of [WhiteheadRussell] p. 121. $)
  pm4.79 $p |-  ( ( ( ps -> ph ) \/ ( ch -> ph ) ) <->
                ( ( ps /\ ch ) -> ph ) ) $=
    ( wn wi wo wa pm4.78 ianor imbi2i bitr4i con34b orbi12i 3bitr4i ) ADZBDZEZO
    CDZEZFZOBCGZDZEZBAEZCAEZFUAAETOPRFZEUCOPRHUBUFOBCIJKUDQUESBALCALMUAALN $.
    $( [14-Apr-2005] $) $( [3-Jan-2005] $)

  $( Theorem *4.87 of [WhiteheadRussell] p. 122.  (The proof was shortened by
     Eric Schmidt, 26-Oct-2006.) $)
  pm4.87 $p |-  ( ( ( ( ( ph /\ ps ) -> ch ) <-> ( ph -> ( ps -> ch ) ) ) /\
                ( ( ph -> ( ps -> ch ) ) <-> ( ps -> ( ph -> ch ) ) ) ) /\
                ( ( ps -> ( ph -> ch ) ) <-> ( ( ps /\ ph ) -> ch ) ) ) $=
    ( wa wi wb impexp bi2.04 pm3.2i bicomi ) ABDCEABCEEZFZKBACEEZFZDMBADCEZFLNA
    BCGABCHIOMBACGJI $.
    $( [27-Oct-2006] $) $( [3-Jan-2005] $)

  $( Theorem *3.33 (Syll) of [WhiteheadRussell] p. 112. $)
  pm3.33 $p |-  ( ( ( ph -> ps ) /\ ( ps -> ch ) ) -> ( ph -> ch ) ) $=
    ( wi imim1 imp ) ABDBCDACDABCEF $.
    $( [16-Apr-2005] $) $( [3-Jan-2005] $)

  $( Theorem *3.34 (Syll) of [WhiteheadRussell] p. 112. $)
  pm3.34 $p |-  ( ( ( ps -> ch ) /\ ( ph -> ps ) ) -> ( ph -> ch ) ) $=
    ( wi imim2 imp ) BCDABDACDBCAEF $.
    $( [16-Apr-2005] $) $( [3-Jan-2005] $)

  $( Conjunctive detachment.  Theorem *3.35 of [WhiteheadRussell] p. 112. $)
  pm3.35 $p |- ( ( ph /\ ( ph -> ps ) ) -> ps ) $=
    ( wi pm2.27 imp ) AABCBABDE $.
    $( [14-Dec-2002] $)

  $( Theorem *5.31 of [WhiteheadRussell] p. 125. $)
  pm5.31 $p |-  ( ( ch /\ ( ph -> ps ) ) -> ( ph -> ( ps /\ ch ) ) ) $=
    ( wi wa pm3.21 imim2d imp ) CABDABCEZDCBIACBFGH $.
    $( [19-Apr-2005] $) $( [3-Jan-2005] $)

  ${
    imp3.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.

    $( Importation deduction. $)
    imp3a $p |- ( ph -> ( ( ps /\ ch ) -> th ) ) $=
      ( wi wa impexp sylibr ) ABCDFFBCGDFEBCDHI $.
      $( [31-Mar-1994] $)

    $( An importation inference. $)
    imp31 $p |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $=
      ( wa wi imp ) ABFCDABCDGEHH $.
      $( [26-Apr-1994] $)

    $( An importation inference. $)
    imp32 $p |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $=
      ( wa imp3a imp ) ABCFDABCDEGH $.
      $( [26-Apr-1994] $)

  $}

  ${
    imp4.1 $e |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $.

    $( An importation inference. $)
    imp4a $p |- ( ph -> ( ps -> ( ( ch /\ th ) -> ta ) ) ) $=
      ( wi wa impexp syl6ibr ) ABCDEGGCDHEGFCDEIJ $.
      $( [26-Apr-1994] $)

    $( An importation inference. $)
    imp4b $p |- ( ( ph /\ ps ) -> ( ( ch /\ th ) -> ta ) ) $=
      ( wa wi imp4a imp ) ABCDGEHABCDEFIJ $.
      $( [26-Apr-1994] $)

    $( An importation inference. $)
    imp4c $p |- ( ph -> ( ( ( ps /\ ch ) /\ th ) -> ta ) ) $=
      ( wa wi imp3a ) ABCGDEABCDEHFII $.
      $( [26-Apr-1994] $)

    $( An importation inference. $)
    imp4d $p |- ( ph -> ( ( ps /\ ( ch /\ th ) ) -> ta ) ) $=
      ( wa imp4a imp3a ) ABCDGEABCDEFHI $.
      $( [26-Apr-1994] $)

    $( An importation inference. $)
    imp41 $p |- ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) -> ta ) $=
      ( wa wi imp imp31 ) ABGCDEABCDEHHFIJ $.
      $( [26-Apr-1994] $)

    $( An importation inference. $)
    imp42 $p |- ( ( ( ph /\ ( ps /\ ch ) ) /\ th ) -> ta ) $=
      ( wa wi imp32 imp ) ABCGGDEABCDEHFIJ $.
      $( [26-Apr-1994] $)

    $( An importation inference. $)
    imp43 $p |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) -> ta ) $=
      ( wa imp4b imp ) ABGCDGEABCDEFHI $.
      $( [26-Apr-1994] $)

    $( An importation inference. $)
    imp44 $p |- ( ( ph /\ ( ( ps /\ ch ) /\ th ) ) -> ta ) $=
      ( wa imp4c imp ) ABCGDGEABCDEFHI $.
      $( [26-Apr-1994] $)

    $( An importation inference. $)
    imp45 $p |- ( ( ph /\ ( ps /\ ( ch /\ th ) ) ) -> ta ) $=
      ( wa imp4d imp ) ABCDGGEABCDEFHI $.
      $( [26-Apr-1994] $)

  $}

  ${
    exp.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( Exportation inference.  (This theorem used to be labeled "exp" but was
       changed to "ex" so as not to conflict with the math token "exp", per
       the June 2006 Metamath spec change.)  (The proof was shortened by Eric
       Schmidt, 22-Dec-2006.) $)
    ex $p |- ( ph -> ( ps -> ch ) ) $=
      ( wa wi impexp mpbi ) ABECFABCFFDABCGH $.
      $( [22-Dec-2006] $) $( [5-Aug-1993] $)

    $( Exportation inference with commuted antecedents. $)
    expcom $p |- ( ps -> ( ph -> ch ) ) $=
      ( ex com12 ) ABCABCDEF $.
      $( [26-May-2005] $) $( [25-May-2005] $)
  $}

  ${
    expimpd.1 $e |- ( ( ph /\ ps ) -> ( ch -> th ) ) $.
    $( Exportation followed by a deduction version of importation. $)
    expimpd $p |- ( ph -> ( ( ps /\ ch ) -> th ) ) $=
      ( wi ex imp3a ) ABCDABCDFEGH $.
      $( [8-Sep-2008] $) $( [6-Sep-2008] $)
  $}

  ${
    exp3a.1 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
    $( Exportation deduction. $)
    exp3a $p |- ( ph -> ( ps -> ( ch -> th ) ) ) $=
      ( wa wi impexp sylib ) ABCFDGBCDGGEBCDHI $.
      $( [20-Aug-1993] $)

    $( A deduction version of exportation, followed by importation. $)
    expdimp $p |- ( ( ph /\ ps ) -> ( ch -> th ) ) $=
      ( wi exp3a imp ) ABCDFABCDEGH $.
      $( [7-Sep-2008] $) $( [6-Sep-2008] $)
  $}

  ${
    exp31.1 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
    $( An exportation inference. $)
    exp31 $p |- ( ph -> ( ps -> ( ch -> th ) ) ) $=
      ( wi wa ex ) ABCDFABGCDEHH $.
      $( [26-Apr-1994] $)
  $}

  ${
    exp32.1 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
    $( An exportation inference. $)
    exp32 $p |- ( ph -> ( ps -> ( ch -> th ) ) ) $=
      ( wa ex exp3a ) ABCDABCFDEGH $.
      $( [26-Apr-1994] $)
  $}

  ${
    exp4a.1 $e |- ( ph -> ( ps -> ( ( ch /\ th ) -> ta ) ) ) $.
    $( An exportation inference. $)
    exp4a $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $=
      ( wa wi impexp syl6ib ) ABCDGEHCDEHHFCDEIJ $.
      $( [26-Apr-1994] $)
  $}

  ${
    exp4b.1 $e |- ( ( ph /\ ps ) -> ( ( ch /\ th ) -> ta ) ) $.
    $( An exportation inference. $)
    exp4b $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $=
      ( wi wa exp3a ex ) ABCDEGGABHCDEFIJ $.
      $( [26-Apr-1994] $)
  $}

  ${
    exp4c.1 $e |- ( ph -> ( ( ( ps /\ ch ) /\ th ) -> ta ) ) $.
    $( An exportation inference. $)
    exp4c $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $=
      ( wi wa exp3a ) ABCDEGABCHDEFII $.
      $( [26-Apr-1994] $)
  $}

  ${
    exp4d.1 $e |- ( ph -> ( ( ps /\ ( ch /\ th ) ) -> ta ) ) $.
    $( An exportation inference. $)
    exp4d $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $=
      ( wa exp3a exp4a ) ABCDEABCDGEFHI $.
      $( [26-Apr-1994] $)
  $}

  ${
    exp41.1 $e |- ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) -> ta ) $.
    $( An exportation inference. $)
    exp41 $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $=
      ( wi wa ex exp31 ) ABCDEGABHCHDEFIJ $.
      $( [26-Apr-1994] $)
  $}

  ${
    exp42.1 $e |- ( ( ( ph /\ ( ps /\ ch ) ) /\ th ) -> ta ) $.
    $( An exportation inference. $)
    exp42 $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $=
      ( wi wa exp31 exp3a ) ABCDEGABCHDEFIJ $.
      $( [26-Apr-1994] $)
  $}

  ${
    exp43.1 $e |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) -> ta ) $.
    $( An exportation inference. $)
    exp43 $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $=
      ( wa ex exp4b ) ABCDEABGCDGEFHI $.
      $( [26-Apr-1994] $)
  $}

  ${
    exp44.1 $e |- ( ( ph /\ ( ( ps /\ ch ) /\ th ) ) -> ta ) $.
    $( An exportation inference. $)
    exp44 $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $=
      ( wi wa exp32 exp3a ) ABCDEGABCHDEFIJ $.
      $( [26-Apr-1994] $)
  $}

  ${
    exp45.1 $e |- ( ( ph /\ ( ps /\ ( ch /\ th ) ) ) -> ta ) $.
    $( An exportation inference. $)
    exp45 $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $=
      ( wa exp32 exp4a ) ABCDEABCDGEFHI $.
      $( [26-Apr-1994] $)
  $}

  ${
    impac.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Importation with conjunction in consequent. $)
    impac $p |- ( ( ph /\ ps ) -> ( ch /\ ps ) ) $=
      ( wa ancrd imp ) ABCBEABCDFG $.
      $( [9-Aug-1994] $)
  $}

  ${
    adantl.1 $e |- ( ph -> ps ) $.
    $( Inference adding a conjunct to the left of an antecedent. $)
    adantl $p |- ( ( ch /\ ph ) -> ps ) $=
      ( wi a1i imp ) CABABECDFG $.
      $( [30-Aug-1993] $)
  $}

  ${
    adantr.1 $e |- ( ph -> ps ) $.
    $( Inference adding a conjunct to the right of an antecedent. $)
    adantr $p |- ( ( ph /\ ch ) -> ps ) $=
      ( a1d imp ) ACBABCDEF $.
      $( [30-Aug-1993] $)
  $}

  ${
    adantld.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction adding a conjunct to the left of an antecedent. $)
    adantld $p |- ( ph -> ( ( th /\ ps ) -> ch ) ) $=
      ( wi a1d imp3a ) ADBCABCFDEGH $.
      $( [4-May-1994] $)
  $}

  ${
    adantrd.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction adding a conjunct to the right of an antecedent. $)
    adantrd $p |- ( ph -> ( ( ps /\ th ) -> ch ) ) $=
      ( wa pm3.26 syl5 ) ABCBDFEBDGH $.
      $( [4-May-1994] $)
  $}

  ${
    adant2.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( Deduction adding a conjunct to antecedent. $)
    adantll $p |- ( ( ( th /\ ph ) /\ ps ) -> ch ) $=
      ( wa wi ex adantl imp ) DAFBCABCGDABCEHIJ $.
      $( [4-May-1994] $)

    $( Deduction adding a conjunct to antecedent. $)
    adantlr $p |- ( ( ( ph /\ th ) /\ ps ) -> ch ) $=
      ( wa wi ex adantr imp ) ADFBCABCGDABCEHIJ $.
      $( [4-May-1994] $)

    $( Deduction adding a conjunct to antecedent. $)
    adantrl $p |- ( ( ph /\ ( th /\ ps ) ) -> ch ) $=
      ( wa ex adantld imp ) ADBFCABCDABCEGHI $.
      $( [4-May-1994] $)

    $( Deduction adding a conjunct to antecedent. $)
    adantrr $p |- ( ( ph /\ ( ps /\ th ) ) -> ch ) $=
      ( wa ex adantrd imp ) ABDFCABCDABCEGHI $.
      $( [4-May-1994] $)
  $}

  ${
    adantl2.1 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
    $( Deduction adding a conjunct to antecedent. $)
    adantlll $p |- ( ( ( ( ta /\ ph ) /\ ps ) /\ ch ) -> th ) $=
      ( wi exp31 a1i imp41 ) EABCDABCDGGGEABCDFHIJ $.
      $( [31-Dec-2004] $) $( [26-Dec-2004] $)

    $( Deduction adding a conjunct to antecedent. $)
    adantllr $p |- ( ( ( ( ph /\ ta ) /\ ps ) /\ ch ) -> th ) $=
      ( wi exp31 a1d imp41 ) AEBCDABCDGGEABCDFHIJ $.
      $( [23-Apr-2005] $) $( [26-Dec-2004] $)

    $( Deduction adding a conjunct to antecedent. $)
    adantlrl $p |- ( ( ( ph /\ ( ta /\ ps ) ) /\ ch ) -> th ) $=
      ( wi exp31 a1d imp42 ) AEBCDABCDGGEABCDFHIJ $.
      $( [31-Dec-2004] $) $( [26-Dec-2004] $)

    $( Deduction adding a conjunct to antecedent. $)
    adantlrr $p |- ( ( ( ph /\ ( ps /\ ta ) ) /\ ch ) -> th ) $=
      ( wi exp31 a1dd imp42 ) ABECDABCDGEABCDFHIJ $.
      $( [5-Jan-2005] $) $( [26-Dec-2004] $)
  $}

  ${
    adantr2.1 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
    $( Deduction adding a conjunct to antecedent. $)
    adantrll $p |- ( ( ph /\ ( ( ta /\ ps ) /\ ch ) ) -> th ) $=
      ( wi exp32 a1d imp44 ) AEBCDABCDGGEABCDFHIJ $.
      $( [31-Dec-2004] $) $( [26-Dec-2004] $)

    $( Deduction adding a conjunct to antecedent. $)
    adantrlr $p |- ( ( ph /\ ( ( ps /\ ta ) /\ ch ) ) -> th ) $=
      ( wi exp32 a1dd imp44 ) ABECDABCDGEABCDFHIJ $.
      $( [31-Dec-2004] $) $( [26-Dec-2004] $)

    $( Deduction adding a conjunct to antecedent. $)
    adantrrl $p |- ( ( ph /\ ( ps /\ ( ta /\ ch ) ) ) -> th ) $=
      ( wi exp32 a1dd imp45 ) ABECDABCDGEABCDFHIJ $.
      $( [31-Dec-2004] $) $( [26-Dec-2004] $)

    $( Deduction adding a conjunct to antecedent. $)
    adantrrr $p |- ( ( ph /\ ( ps /\ ( ch /\ ta ) ) ) -> th ) $=
      ( wi wa a1d exp32 imp45 ) ABCEDABCEDGABCHHDEFIJK $.
      $( [31-Dec-2004] $) $( [26-Dec-2004] $)
  $}

  ${
    ad2ant.1 $e |- ( ph -> ps ) $.
    $( Deduction adding conjuncts to antecedent. $)
    ad2antrr $p |- ( ( ( ph /\ ch ) /\ th ) -> ps ) $=
      ( wa adantr ) ACFBDABCEGG $.
      $( [19-Oct-1999] $)

    $( Deduction adding conjuncts to antecedent. $)
    ad2antlr $p |- ( ( ( ch /\ ph ) /\ th ) -> ps ) $=
      ( wa adantl adantr ) CAFBDABCEGH $.
      $( [19-Oct-1999] $)

    $( Deduction adding conjuncts to antecedent. $)
    ad2antrl $p |- ( ( ch /\ ( ph /\ th ) ) -> ps ) $=
      ( wa adantr adantl ) ADFBCABDEGH $.
      $( [19-Oct-1999] $)

    $( Deduction adding conjuncts to antecedent. $)
    ad2antll $p |- ( ( ch /\ ( th /\ ph ) ) -> ps ) $=
      ( wa adantl ) DAFBCABDEGG $.
      $( [19-Oct-1999] $)
  $}

  ${
    ad2ant2.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( Deduction adding two conjuncts to antecedent. $)
    ad2ant2l $p |- ( ( ( th /\ ph ) /\ ( ta /\ ps ) ) -> ch ) $=
      ( wa adantrl adantll ) AEBGCDABCEFHI $.
      $( [9-Jan-2006] $) $( [8-Jan-2006] $)

    $( Deduction adding two conjuncts to antecedent. $)
    ad2ant2r $p |- ( ( ( ph /\ th ) /\ ( ps /\ ta ) ) -> ch ) $=
      ( wa adantrr adantlr ) ABEGCDABCEFHI $.
      $( [9-Jan-2006] $) $( [8-Jan-2006] $)

    $( Deduction adding two conjuncts to antecedent. $)
    ad2ant2lr $p |- ( ( ( th /\ ph ) /\ ( ps /\ ta ) ) -> ch ) $=
      ( wa adantrr adantll ) ABEGCDABCEFHI $.
      $( [23-Nov-2007] $) $( [23-Nov-2007] $)

    $( Deduction adding two conjuncts to antecedent. $)
    ad2ant2rl $p |- ( ( ( ph /\ th ) /\ ( ta /\ ps ) ) -> ch ) $=
      ( wa adantrl adantlr ) AEBGCDABCEFHI $.
      $( [24-Nov-2007] $) $( [24-Nov-2007] $)
  $}

  $( Simplification of a conjunction. $)
  simpll $p |- ( ( ( ph /\ ps ) /\ ch ) -> ph ) $=
    ( id ad2antrr ) AABCADE $.
    $( [19-Mar-2007] $) $( [18-Mar-2007] $)

  $( Simplification of a conjunction. $)
  simplr $p |- ( ( ( ph /\ ps ) /\ ch ) -> ps ) $=
    ( id ad2antlr ) BBACBDE $.
    $( [20-Mar-2007] $) $( [20-Mar-2007] $)

  $( Simplification of a conjunction. $)
  simprl $p |- ( ( ph /\ ( ps /\ ch ) ) -> ps ) $=
    ( id ad2antrl ) BBACBDE $.
    $( [21-Mar-2007] $) $( [21-Mar-2007] $)

  $( Simplification of a conjunction. $)
  simprr $p |- ( ( ph /\ ( ps /\ ch ) ) -> ch ) $=
    ( id ad2antll ) CCABCDE $.
    $( [21-Mar-2007] $) $( [21-Mar-2007] $)

  $( Simplification of a conjunction.  (Contributed by Jeff Hankins,
     28-Jul-2009.) $)
  simplll $p |- ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) -> ph ) $=
    ( wa pm3.26 ad2antrr ) ABEACDABFG $.
    $( [18-Apr-2010] $) $( [28-Jul-2009] $)

  $( Simplification of a conjunction.  (Contributed by Jeff Hankins,
     28-Jul-2009.) $)
  simpllr $p |- ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) -> ps ) $=
    ( wa pm3.27 ad2antrr ) ABEBCDABFG $.
    $( [18-Apr-2010] $) $( [28-Jul-2009] $)

  $( Simplification of a conjunction.  (Contributed by Jeff Hankins,
     28-Jul-2009.) $)
  simplrl $p |- ( ( ( ph /\ ( ps /\ ch ) ) /\ th ) -> ps ) $=
    ( wa pm3.26 ad2antlr ) BCEBADBCFG $.
    $( [18-Apr-2010] $) $( [28-Jul-2009] $)

  $( Simplification of a conjunction.  (Contributed by Jeff Hankins,
     28-Jul-2009.) $)
  simplrr $p |- ( ( ( ph /\ ( ps /\ ch ) ) /\ th ) -> ch ) $=
    ( wa pm3.27 ad2antlr ) BCECADBCFG $.
    $( [18-Apr-2010] $) $( [28-Jul-2009] $)

  $( Simplification of a conjunction.  (Contributed by Jeff Hankins,
     28-Jul-2009.) $)
  simprll $p |- ( ( ph /\ ( ( ps /\ ch ) /\ th ) ) -> ps ) $=
    ( wa pm3.26 ad2antrl ) BCEBADBCFG $.
    $( [18-Apr-2010] $) $( [28-Jul-2009] $)

  $( Simplification of a conjunction.  (Contributed by Jeff Hankins,
     28-Jul-2009.) $)
  simprlr $p |- ( ( ph /\ ( ( ps /\ ch ) /\ th ) ) -> ch ) $=
    ( wa pm3.27 ad2antrl ) BCECADBCFG $.
    $( [18-Apr-2010] $) $( [28-Jul-2009] $)

  $( Simplification of a conjunction.  (Contributed by Jeff Hankins,
     28-Jul-2009.) $)
  simprrl $p |- ( ( ph /\ ( ps /\ ( ch /\ th ) ) ) -> ch ) $=
    ( wa pm3.26 ad2antll ) CDECABCDFG $.
    $( [18-Apr-2010] $) $( [28-Jul-2009] $)

  $( Simplification of a conjunction.  (Contributed by Jeff Hankins,
     28-Jul-2009.) $)
  simprrr $p |- ( ( ph /\ ( ps /\ ( ch /\ th ) ) ) -> th ) $=
    ( wa pm3.27 ad2antll ) CDEDABCDFG $.
    $( [18-Apr-2010] $) $( [28-Jul-2009] $)

  ${
    biimpa.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Inference from a logical equivalence. $)
    biimpa $p |- ( ( ph /\ ps ) -> ch ) $=
      ( biimpd imp ) ABCABCDEF $.
      $( [3-May-1994] $)

    $( Inference from a logical equivalence. $)
    biimpar $p |- ( ( ph /\ ch ) -> ps ) $=
      ( biimprd imp ) ACBABCDEF $.
      $( [3-May-1994] $)

    $( Inference from a logical equivalence. $)
    biimpac $p |- ( ( ps /\ ph ) -> ch ) $=
      ( biimpcd imp ) BACABCDEF $.
      $( [3-May-1994] $)

    $( Inference from a logical equivalence. $)
    biimparc $p |- ( ( ch /\ ph ) -> ps ) $=
      ( biimprcd imp ) CABABCDEF $.
      $( [3-May-1994] $)
  $}

  ${
    pm3.26bda.1 $e |- ( ph -> ( ps <-> ( ch /\ th ) ) ) $.
    $( Deduction eliminating a conjunct. $)
    pm3.26bda $p |- ( ( ph /\ ps ) -> ch ) $=
      ( wa biimpa pm3.26d ) ABFCDABCDFEGH $.
      $( [23-Oct-2007] $) $( [22-Oct-2007] $)

    $( Deduction eliminating a conjunct. $)
    pm3.27bda $p |- ( ( ph /\ ps ) -> th ) $=
      ( wa biimpa pm3.27d ) ABFCDABCDFEGH $.
      $( [25-Oct-2007] $) $( [22-Oct-2007] $)
  $}

  $( Disjunction of antecedents.  Compare Theorem *4.77 of
     [WhiteheadRussell] p. 121. $)
  jaob $p |- ( ( ( ph \/ ch ) -> ps ) <-> ( ( ph -> ps ) /\ ( ch -> ps ) ) ) $=
    ( wo wi wa orc imim1i olc jca jao imp impbii ) ACDZBEZABEZCBEZFOPQANBACGHCN
    BCAIHJPQOABCKLM $.
    $( [30-May-1994] $)

  $( Theorem *4.77 of [WhiteheadRussell] p. 121. $)
  pm4.77 $p |-  ( ( ( ps -> ph ) /\ ( ch -> ph ) ) <->
                ( ( ps \/ ch ) -> ph ) ) $=
    ( wo wi wa jaob bicomi ) BCDAEBAECAEFBACGH $.
    $( [10-Apr-2005] $) $( [3-Jan-2005] $)

  ${
    jaod.1 $e |- ( ph -> ( ps -> ch ) ) $.
    jaod.2 $e |- ( ph -> ( th -> ch ) ) $.
    $( Deduction disjoining the antecedents of two implications. $)
    jaod $p |- ( ph -> ( ( ps \/ th ) -> ch ) ) $=
      ( wi wo jao sylc ) BCGDCGBDHCGABCDIEFJ $.
      $( [18-Aug-1994] $)
  $}

  ${
    jaoian.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    jaoian.2 $e |- ( ( th /\ ps ) -> ch ) $.
    $( Inference disjoining the antecedents of two implications. $)
    jaoian $p |- ( ( ( ph \/ th ) /\ ps ) -> ch ) $=
      ( wo wi ex jaoi imp ) ADGBCABCHDABCEIDBCFIJK $.
      $( [26-Oct-2005] $) $( [23-Oct-2005] $)
  $}

  ${
    jaodan.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    jaodan.2 $e |- ( ( ph /\ th ) -> ch ) $.
    $( Deduction disjoining the antecedents of two implications. $)
    jaodan $p |- ( ( ph /\ ( ps \/ th ) ) -> ch ) $=
      ( wo ex jaod imp ) ABDGCABCDABCEHADCFHIJ $.
      $( [24-Oct-2005] $) $( [14-Oct-2005] $)
  $}

  ${
    jaao.1 $e |- ( ph -> ( ps -> ch ) ) $.
    jaao.2 $e |- ( th -> ( ta -> ch ) ) $.
    $( Inference conjoining and disjoining the antecedents of two
       implications. $)
    jaao $p |- ( ( ph /\ th ) -> ( ( ps \/ ta ) -> ch ) ) $=
      ( wa wi adantr adantl jaod ) ADHBCEABCIDFJDECIAGKL $.
      $( [30-Sep-1999] $)

    $( Inference disjoining and conjoining the antecedents of two
       implications.  (Contributed by Stefan Allan, 1-Nov-2008.) $)
    jaoa $p |-  ( ( ph \/ th ) -> ( ( ps /\ ta ) -> ch ) ) $=
      ( wa wi adantrd adantld jaoi ) ABEHCIDABCEFJDECBGKL $.
      $( [2-Nov-2008] $) $( [1-Nov-2008] $)
  $}

  $( Theorem *2.63 of [WhiteheadRussell] p. 107. $)
  pm2.63 $p |-  ( ( ph \/ ps ) -> ( ( -. ph \/ ps ) -> ps ) ) $=
    ( wo wn pm2.53 idd jaod ) ABCZADBBABEHBFG $.
    $( [19-Apr-2005] $) $( [3-Jan-2005] $)

  $( Theorem *2.64 of [WhiteheadRussell] p. 107. $)
  pm2.64 $p |-  ( ( ph \/ ps ) -> ( ( ph \/ -. ps ) -> ph ) ) $=
    ( wn wo wi ax-1 orel2 jaoi com12 ) ABCZDABDZAAKAEJAKFBAGHI $.
    $( [19-Apr-2005] $) $( [3-Jan-2005] $)

  $( Theorem *3.44 of [WhiteheadRussell] p. 113. $)
  pm3.44 $p |-  ( ( ( ps -> ph ) /\ ( ch -> ph ) ) ->
                ( ( ps \/ ch ) -> ph ) ) $=
    ( wo wi wa jaob biimpri ) BCDAEBAECAEFBACGH $.
    $( [24-Apr-2005] $) $( [3-Jan-2005] $)

  $( Theorem *4.43 of [WhiteheadRussell] p. 119. $)
  pm4.43 $p |-  ( ph <-> ( ( ph \/ ps ) /\ ( ph \/ -. ps ) ) ) $=
    ( wo wn wa orc jca pm2.64 imp impbii ) AABCZABDZCZEAKMABFALFGKMAABHIJ $.
    $( [25-Apr-2005] $) $( [3-Jan-2005] $)

  $( Idempotent law for conjunction. $)
  anidm $p |- ( ( ph /\ ph ) <-> ph ) $=
    ( wa pm3.26 pm3.2 pm2.43i impbii ) AABZAAACAGAADEF $.
    $( [5-Aug-1993] $)

  $( Theorem *4.24 of [WhiteheadRussell] p. 117. $)
  pm4.24 $p |-  ( ph <-> ( ph /\ ph ) ) $=
    ( wa anidm bicomi ) AABAACD $.
    $( [17-Jan-2005] $) $( [3-Jan-2005] $)

  ${
    anidms.1 $e |- ( ( ph /\ ph ) -> ps ) $.
    $( Inference from idempotent law for conjunction. $)
    anidms $p |- ( ph -> ps ) $=
      ( ex pm2.43i ) ABAABCDE $.
      $( [15-Jun-1994] $)
  $}

  $( Conjunction idempotence with antecedent. (Contributed by Roy F.
     Longton, 8-Aug-2005.) $)
  anidmdbi $p |- ( ( ph -> ( ps /\ ps ) ) <-> ( ph -> ps ) ) $=
    ( wa anidm imbi2i ) BBCBABDE $.
    $( [31-Oct-2007] $) $( [8-Aug-2005] $)

  $( Commutative law for conjunction.  Theorem *4.3 of [WhiteheadRussell]
     p. 118. $)
  ancom $p |- ( ( ph /\ ps ) <-> ( ps /\ ph ) ) $=
    ( wa pm3.27 pm3.26 jca impbii ) ABCZBACZHBAABDABEFIABBADBAEFG $.
    $( [25-Jun-1998] $)

  ${
    ancomd.1 $e |- ( ph -> ( ps /\ ch ) ) $.
    $( Commutation of conjuncts in consequent.  (Contributed by Jeff Hankins,
       14-Aug-2009.)  $)
    ancomd $p |- ( ph -> ( ch /\ ps ) ) $=
      ( wa ancom sylib ) ABCECBEDBCFG $.
      $( [18-Apr-2010] $) $( [14-Aug-2009] $)
  $}

  ${
    ancoms.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( Inference commuting conjunction in antecedent.  _Notational convention_:
       We sometimes suffix with "s" the label of an inference that manipulates
       an antecedent, leaving the consequent unchanged.  The "s" means that the
       inference eliminates the need for a syllogism ( ~ syl ) -type inference
       in a proof. $)
    ancoms $p |- ( ( ps /\ ph ) -> ch ) $=
      ( wa ancom sylbi ) BAEABECBAFDG $.
      $( [21-Apr-1994] $)
  $}

  ${
    ancomsd.1 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
    $( Deduction commuting conjunction in antecedent. $)
    ancomsd $p |- ( ph -> ( ( ch /\ ps ) -> th ) ) $=
      ( wa ancom syl5ib ) ABCFDCBFECBGH $.
      $( [13-Dec-2004] $) $( [12-Dec-2004] $)
  $}

  $( Theorem *3.22 of [WhiteheadRussell] p. 111. $)
  pm3.22 $p |-  ( ( ph /\ ps ) -> ( ps /\ ph ) ) $=
    ( wa ancom biimpi ) ABCBACABDE $.
    $( [17-Jan-2005] $) $( [3-Jan-2005] $)

  $( Associative law for conjunction.  Theorem *4.32 of [WhiteheadRussell]
     p. 118. $)
  anass $p |- ( ( ( ph /\ ps ) /\ ch ) <-> ( ph /\ ( ps /\ ch ) ) ) $=
    ( wa wn wi impexp imnan imbi2i bitri notbii df-an 3bitr4i ) ABDZCEZFZEABCDZ
    EZFZENCDAQDPSPABOFZFSABOGTRABCHIJKNCLAQLM $.
    $( [5-Aug-1993] $)

  ${
    anasss.1 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
    $( Associative law for conjunction applied to antecedent (eliminates
       syllogism). $)
    anasss $p |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $=
      ( exp31 imp32 ) ABCDABCDEFG $.
      $( [15-Nov-2002] $)
  $}

  ${
    anassrs.1 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
    $( Associative law for conjunction applied to antecedent (eliminates
       syllogism). $)
    anassrs $p |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $=
      ( exp32 imp31 ) ABCDABCDEFG $.
      $( [15-Nov-2002] $)
  $}

  $( Distribution of implication with conjunction. $)
  imdistan $p |- ( ( ph -> ( ps -> ch ) ) <->
                 ( ( ph /\ ps ) -> ( ph /\ ch ) ) ) $=
    ( wi wa anc2l imp3a pm3.27 imim2i exp3a impbii ) ABCDDZABEZACEZDZLABNABCFGO
    ABCNCMACHIJK $.
    $( [31-May-1999] $)

  ${
    imdistani.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Distribution of implication with conjunction. $)
    imdistani $p |- ( ( ph /\ ps ) -> ( ph /\ ch ) ) $=
      ( wa anc2li imp ) ABACEABCDFG $.
      $( [1-Aug-1994] $)
  $}

  ${
    imdistanri.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Distribution of implication with conjunction. $)
    imdistanri $p |- ( ( ps /\ ph ) -> ( ch /\ ph ) ) $=
      ( com12 impac ) BACABCDEF $.
      $( [8-Jan-2002] $)
  $}

  ${
    imdistand.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    $( Distribution of implication with conjunction (deduction rule). $)
    imdistand $p |- ( ph -> ( ( ps /\ ch ) -> ( ps /\ th ) ) ) $=
      ( wi wa imdistan sylib ) ABCDFFBCGBDGFEBCDHI $.
      $( [28-Aug-2004] $) $( [27-Aug-2004] $)
  $}

  $( Theorem *5.3 of [WhiteheadRussell] p. 125. $)
  pm5.3 $p |-  ( ( ( ph /\ ps ) -> ch ) <->
               ( ( ph /\ ps ) -> ( ph /\ ch ) ) ) $=
    ( wa wi pm3.3 imdistand pm3.27 imim2i impbii ) ABDZCEZKACDZELABCABCFGMCKACH
    IJ $.
    $( [27-Apr-2005] $) $( [3-Jan-2005] $)

  $( Theorem *5.61 of [WhiteheadRussell] p. 125. $)
  pm5.61 $p |-  ( ( ( ph \/ ps ) /\ -. ps ) <-> ( ph /\ -. ps ) ) $=
    ( wo wn wa orel2 imdistanri orc anim1i impbii ) ABCZBDZEALELKABAFGAKLABHIJ 
    $.
    $( [10-Apr-2005] $) $( [3-Jan-2005] $)

  ${
    sylan.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    ${
      sylan.2 $e |- ( th -> ph ) $.
      $( A syllogism inference. $)
      sylan $p |- ( ( th /\ ps ) -> ch ) $=
        ( wi ex syl imp ) DBCDABCGFABCEHIJ $.
        $( [21-Apr-1994] $)
    $}

    ${
      sylanb.2 $e |- ( th <-> ph ) $.
      $( A syllogism inference. $)
      sylanb $p |- ( ( th /\ ps ) -> ch ) $=
        ( biimpi sylan ) ABCDEDAFGH $.
        $( [18-May-1994] $)
    $}

    ${
      sylanbr.2 $e |- ( ph <-> th ) $.
      $( A syllogism inference. $)
      sylanbr $p |- ( ( th /\ ps ) -> ch ) $=
        ( biimpri sylan ) ABCDEADFGH $.
        $( [18-May-1994] $)
    $}

    ${
      sylan2.2 $e |- ( th -> ps ) $.
      $( A syllogism inference. $)
      sylan2 $p |- ( ( ph /\ th ) -> ch ) $=
        ( ex syl5 imp ) ADCABCDABCEGFHI $.
        $( [21-Apr-1994] $)
    $}

    ${
      sylan2b.2 $e |- ( th <-> ps ) $.
      $( A syllogism inference. $)
      sylan2b $p |- ( ( ph /\ th ) -> ch ) $=
        ( biimpi sylan2 ) ABCDEDBFGH $.
        $( [21-Apr-1994] $)
    $}

    ${
      sylan2br.2 $e |- ( ps <-> th ) $.
      $( A syllogism inference. $)
      sylan2br $p |- ( ( ph /\ th ) -> ch ) $=
        ( biimpri sylan2 ) ABCDEBDFGH $.
        $( [21-Apr-1994] $)
    $}

    ${
      syl2an.2 $e |- ( th -> ph ) $.
      syl2an.3 $e |- ( ta -> ps ) $.
      $( A double syllogism inference. $)
      syl2an $p |- ( ( th /\ ta ) -> ch ) $=
        ( sylan sylan2 ) DBCEABCDFGIHJ $.
        $( [31-Jan-1997] $)
    $}

    ${
      syl2anb.2 $e |- ( th <-> ph ) $.
      syl2anb.3 $e |- ( ta <-> ps ) $.
      $( A double syllogism inference. $)
      syl2anb $p |- ( ( th /\ ta ) -> ch ) $=
        ( sylanb sylan2b ) DBCEABCDFGIHJ $.
        $( [29-Jul-1999] $)
    $}

    ${
      syl2anbr.2 $e |- ( ph <-> th ) $.
      syl2anbr.3 $e |- ( ps <-> ta ) $.
      $( A double syllogism inference. $)
      syl2anbr $p |- ( ( th /\ ta ) -> ch ) $=
        ( sylanbr sylan2br ) DBCEABCDFGIHJ $.
        $( [29-Jul-1999] $)
    $}
  $}

  ${
    syland.1 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
    syland.2 $e |- ( ph -> ( ta -> ps ) ) $.
    $( A syllogism deduction. $)
    syland $p |- ( ph -> ( ( ta /\ ch ) -> th ) ) $=
      ( wi exp3a syld imp3a ) AECDAEBCDHGABCDFIJK $.
      $( [17-Dec-2004] $) $( [15-Dec-2004] $)
  $}

  ${
    sylan2d.1 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
    sylan2d.2 $e |- ( ph -> ( ta -> ch ) ) $.
    $( A syllogism deduction. $)
    sylan2d $p |- ( ph -> ( ( ps /\ ta ) -> th ) ) $=
      ( ancomsd syland ) AEBDACBDEABCDFHGIH $.
      $( [17-Dec-2004] $) $( [15-Dec-2004] $)
  $}

  ${
    $v et $. $( Greek eta $)
    syl2and.wet $f wff et $.
    syl2and.1 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
    syl2and.2 $e |- ( ph -> ( ta -> ps ) ) $.
    syl2and.3 $e |- ( ph -> ( et -> ch ) ) $.
    $( A syllogism deduction. $)
    syl2and $p |- ( ph -> ( ( ta /\ et ) -> th ) ) $=
      ( sylan2d syland ) ABFDEABCDFGIJHK $.
      $( [17-Dec-2004] $) $( [15-Dec-2004] $)
  $}

  ${
    sylanl1.1 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
    sylanl1.2 $e |- ( ta -> ph ) $.
    $( A syllogism inference. $)
    sylanl1 $p |- ( ( ( ta /\ ps ) /\ ch ) -> th ) $=
      ( wa anim1i sylan ) ABHCDEBHFEABGIJ $.
      $( [30-Apr-2005] $) $( [10-Mar-2005] $)
  $}

  ${
    sylanl2.1 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
    sylanl2.2 $e |- ( ta -> ps ) $.
    $( A syllogism inference. $)
    sylanl2 $p |- ( ( ( ph /\ ta ) /\ ch ) -> th ) $=
      ( wa anim2i sylan ) ABHCDAEHFEBAGIJ $.
      $( [2-Jan-2005] $) $( [1-Jan-2005] $)
  $}

  ${
    sylanr1.1 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
    sylanr1.2 $e |- ( ta -> ps ) $.
    $( A syllogism inference. $)
    sylanr1 $p |- ( ( ph /\ ( ta /\ ch ) ) -> th ) $=
      ( wa anim1i sylan2 ) ABCHDECHFEBCGIJ $.
      $( [15-May-2005] $) $( [9-Apr-2005] $)
  $}

  ${
    sylanr2.1 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
    sylanr2.2 $e |- ( ta -> ch ) $.
    $( A syllogism inference. $)
    sylanr2 $p |- ( ( ph /\ ( ps /\ ta ) ) -> th ) $=
      ( wa anim2i sylan2 ) ABCHDBEHFECBGIJ $.
      $( [1-May-2005] $) $( [9-Apr-2005] $)
  $}

  ${
    sylani.1 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
    sylani.2 $e |- ( ta -> ps ) $.
    $( A syllogism inference. $)
    sylani $p |- ( ph -> ( ( ta /\ ch ) -> th ) ) $=
      ( wi a1i syland ) ABCDEFEBHAGIJ $.
      $( [2-May-1996] $)
  $}

  ${
    sylan2i.1 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
    sylan2i.2 $e |- ( ta -> ch ) $.
    $( A syllogism inference. $)
    sylan2i $p |- ( ph -> ( ( ps /\ ta ) -> th ) ) $=
      ( wi a1i sylan2d ) ABCDEFECHAGIJ $.
      $( [1-Aug-1994] $)
  $}

  ${
    $v et $. $( Greek eta $)
    syl2ani.wet $f wff et $.
    syl2ani.1 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
    syl2ani.2 $e |- ( ta -> ps ) $.
    syl2ani.3 $e |- ( et -> ch ) $.
    $( A syllogism inference. $)
    syl2ani $p |- ( ph -> ( ( ta /\ et ) -> th ) ) $=
      ( sylan2i sylani ) ABFDEABCDFGIJHK $.
      $( [3-Aug-1999] $)
  $}

  ${
    syldan.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    syldan.2 $e |- ( ( ph /\ ch ) -> th ) $.
    $( A syllogism deduction with conjoined antecents. $)
    syldan $p |- ( ( ph /\ ps ) -> th ) $=
      ( ex syld imp ) ABDABCDABCEGACDFGHI $.
      $( [26-Feb-2005] $) $( [24-Feb-2005] $)
  $}

  ${
    sylan9.1 $e |- ( ph -> ( ps -> ch ) ) $.
    sylan9.2 $e |- ( th -> ( ch -> ta ) ) $.
    $( Nested syllogism inference conjoining dissimilar antecedents. $)
    sylan9 $p |- ( ( ph /\ th ) -> ( ps -> ta ) ) $=
      ( wa wi adantr adantl syld ) ADHBCEABCIDFJDCEIAGKL $.
      $( [5-Aug-1993] $)
  $}

  ${
    sylan9r.1 $e |- ( ph -> ( ps -> ch ) ) $.
    sylan9r.2 $e |- ( th -> ( ch -> ta ) ) $.
    $( Nested syllogism inference conjoining dissimilar antecedents. $)
    sylan9r $p |- ( ( th /\ ph ) -> ( ps -> ta ) ) $=
      ( wi syl9r imp ) DABEHABCDEFGIJ $.
      $( [5-Aug-1993] $)
  $}

  ${
    mpan9.1 $e |- ( ph -> ps ) $.
    mpan9.2 $e |- ( ch -> ( ps -> th ) ) $.
    $( Modus ponens conjoining dissimilar antecedents. $)
    mpan9 $p |- ( ( ph /\ ch ) -> th ) $=
      ( wa adantr wi adantl mpd ) ACGBDABCEHCBDIAFJK $.
      $( [1-Feb-2008] $) $( [1-Feb-2008] $)
  $}

  ${
    sylanc.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    sylanc.2 $e |- ( th -> ph ) $.
    sylanc.3 $e |- ( th -> ps ) $.
    $( A syllogism inference combined with contraction. $)
    sylanc $p |- ( th -> ch ) $=
      ( ex sylc ) ABCDABCEHFGI $.
      $( [3-Oct-1999] $)
  $}

  ${
    sylancl.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    sylancl.2 $e |- ( th -> ph ) $.
    sylancl.3 $e |- ps $.
    $( Syllogism inference.  (Contributed by Jeff Madsen, 2-Sep-2009.) $)
    sylancl $p |- ( th -> ch ) $=
      ( a1i sylanc ) ABCDEFBDGHI $.
      $( [18-Apr-2010] $) $( [2-Sep-2009] $)
  $}

  ${
    sylancr.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    sylancr.2 $e |- ph $.
    sylancr.3 $e |- ( th -> ps ) $.
    $( Syllogism inference.  (Contributed by Jeff Madsen, 2-Sep-2009.) $)
    sylancr $p |- ( th -> ch ) $=
      ( a1i sylanc ) ABCDEADFHGI $.
      $( [2-Sep-2009] $)
  $}

  ${
    $v et $. $( Greek eta $)
    syl2anc.wet $f wff et $.
    syl2anc.1 $e |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) -> ta ) $.
    syl2anc.2 $e |- ( et -> ph ) $.
    syl2anc.3 $e |- ( et -> ps ) $.
    syl2anc.4 $e |- ( et -> ch ) $.
    syl2anc.5 $e |- ( et -> th ) $.
    $( A syllogism inference combined with contraction. $)
    syl2anc $p |- ( et -> ta ) $=
      ( wa jca sylanc ) ABLCDLEFGFABHIMFCDJKMN $.
      $( [18-Jun-2007] $) $( [16-Jun-2007] $)
  $}

  ${
    sylancb.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    sylancb.2 $e |- ( th <-> ph ) $.
    sylancb.3 $e |- ( th <-> ps ) $.
    $( A syllogism inference combined with contraction. $)
    sylancb $p |- ( th -> ch ) $=
      ( syl2anb anidms ) DCABCDDEFGHI $.
      $( [9-Sep-2004] $) $( [3-Sep-2004] $)
  $}

  ${
    sylancbr.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    sylancbr.2 $e |- ( ph <-> th ) $.
    sylancbr.3 $e |- ( ps <-> th ) $.
    $( A syllogism inference combined with contraction. $)
    sylancbr $p |- ( th -> ch ) $=
      ( syl2anbr anidms ) DCABCDDEFGHI $.
      $( [14-Sep-2004] $) $( [3-Sep-2004] $)
  $}

  ${
    sylancom.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    sylancom.2 $e |- ( ( ch /\ ps ) -> th ) $.
    $( Syllogism inference with commutation of antecents. $)
    sylancom $p |- ( ( ph /\ ps ) -> th ) $=
      ( wa pm3.27 sylanc ) CBDABGFEABHI $.
      $( [2-Jul-2008] $) $( [2-Jul-2008] $)
  $}

  ${
    pm2.61ian.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    pm2.61ian.2 $e |- ( ( -. ph /\ ps ) -> ch ) $.
    $( Elimination of an antecedent. $)
    pm2.61ian $p |- ( ps -> ch ) $=
      ( wi ex wn pm2.61i ) ABCFABCDGAHBCEGI $.
      $( [3-Jan-2005] $) $( [1-Jan-2005] $)
  $}

  ${
    pm2.61dan.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    pm2.61dan.2 $e |- ( ( ph /\ -. ps ) -> ch ) $.
    $( Elimination of an antecedent. $)
    pm2.61dan $p |- ( ph -> ch ) $=
      ( ex wn pm2.61d ) ABCABCDFABGCEFH $.
      $( [3-Jan-2005] $) $( [1-Jan-2005] $)
  $}

  ${
    condan.1 $e |- ( ( ph /\ -. ps ) -> ch ) $.
    condan.2 $e |- ( ( ph /\ -. ps ) -> -. ch ) $.
    $( Proof by contradiction. $)
    condan $p |- ( ph -> ps ) $=
      ( wn ex pm2.65d notnot2 syl ) ABFZFBAKCAKCDGAKCFEGHBIJ $.
      $( [21-Feb-2006] $) $( [9-Feb-2006] $)
  $}

  $( Introduce one conjunct as an antecedent to the another. $)
  abai $p |- ( ( ph /\ ps ) <-> ( ph /\ ( ph -> ps ) ) ) $=
    ( wa wi pm3.26 pm3.4 jca pm3.35 impbii ) ABCZAABDZCZJAKABEABFGLABAKEABHGI 
    $.
    $( [12-Aug-1993] $)

  ${
    bi.aa $e |- ( ph <-> ps ) $.

    $( Introduce a left conjunct to both sides of a logical equivalence. $)
    anbi2i $p |- ( ( ch /\ ph ) <-> ( ch /\ ps ) ) $=
      ( wa biimpi anim2i biimpri impbii ) CAECBEABCABDFGBACABDHGI $.
      $( [5-Aug-1993] $)

    $( Introduce a right conjunct to both sides of a logical equivalence. $)
    anbi1i $p |- ( ( ph /\ ch ) <-> ( ps /\ ch ) ) $=
      ( wa ancom anbi2i 3bitri ) ACECAECBEBCEACFABCDGCBFH $.
      $( [5-Aug-1993] $)
  $}

  ${
    anbi12.1 $e |- ( ph <-> ps ) $.
    anbi12.2 $e |- ( ch <-> th ) $.
    $( Conjoin both sides of two equivalences. $)
    anbi12i $p |- ( ( ph /\ ch ) <-> ( ps /\ th ) ) $=
      ( wa anbi1i anbi2i bitri ) ACGBCGBDGABCEHCDBFIJ $.
      $( [5-Aug-1993] $)
  $}

  $( Theorem *5.53 of [WhiteheadRussell] p. 125. $)
  pm5.53 $p |-  ( ( ( ( ph \/ ps ) \/ ch ) -> th ) <->
                ( ( ( ph -> th ) /\ ( ps -> th ) ) /\ ( ch -> th ) ) ) $=
    ( wo wi wa jaob anbi1i bitri ) ABEZCEDFKDFZCDFZGADFBDFGZMGKDCHLNMADBHIJ $.
    $( [28-Apr-2005] $) $( [3-Jan-2005] $)

  $( A rearrangement of conjuncts. $)
  an12 $p |- ( ( ph /\ ( ps /\ ch ) ) <-> ( ps /\ ( ph /\ ch ) ) ) $=
    ( wa ancom anbi1i anass 3bitr3i ) ABDZCDBADZCDABCDDBACDDIJCABEFABCGBACGH $.
    $( [12-Mar-1995] $)

  $( A rearrangement of conjuncts. $)
  an23 $p |- ( ( ( ph /\ ps ) /\ ch ) <-> ( ( ph /\ ch ) /\ ps ) ) $=
    ( wa ancom anbi2i anass 3bitr4i ) ABCDZDACBDZDABDCDACDBDIJABCEFABCGACBGH $.
    $( [12-Mar-1995] $)

  ${
    an1s.1 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
    $( Deduction rearranging conjuncts. $)
    an1s $p |- ( ( ps /\ ( ph /\ ch ) ) -> th ) $=
      ( wa an12 sylbi ) BACFFABCFFDBACGEH $.
      $( [13-Mar-1996] $)

    $( Inference commuting a nested conjunction in antecedent. $)
    ancom2s $p |- ( ( ph /\ ( ch /\ ps ) ) -> th ) $=
      ( exp32 com23 imp32 ) ACBDABCDABCDEFGH $.
      $( [25-May-2006] $) $( [24-May-2006] $)

    $( Deduction rearranging conjuncts. $)
    ancom13s $p |- ( ( ch /\ ( ps /\ ph ) ) -> th ) $=
      ( exp32 com13 imp32 ) CBADABCDABCDEFGH $.
      $( [31-May-2006] $) $( [31-May-2006] $)
  $}

  ${
    an1rs.1 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
    $( Deduction rearranging conjuncts. $)
    an1rs $p |- ( ( ( ph /\ ch ) /\ ps ) -> th ) $=
      ( wa an23 sylbi ) ACFBFABFCFDACBGEH $.
      $( [13-Mar-1996] $)

    $( Inference commuting a nested conjunction in antecedent. $)
    ancom1s $p |- ( ( ( ps /\ ph ) /\ ch ) -> th ) $=
      ( wi exp31 com12 imp31 ) BACDABCDFABCDEGHI $.
      $( [25-May-2006] $) $( [24-May-2006] $)

    $( Deduction rearranging conjuncts. $)
    ancom31s $p |- ( ( ( ch /\ ps ) /\ ph ) -> th ) $=
      ( exp31 com13 imp31 ) CBADABCDABCDEFGH $.
      $( [2-Jun-2006] $) $( [31-May-2006] $)
  $}

  $( Absorption into embedded conjunct. $)
  anabs1 $p |- ( ( ( ph /\ ps ) /\ ph ) <-> ( ph /\ ps ) ) $=
    ( wa pm3.26 ancli impbii ) ABCZACGGADGAABDEF $.
    $( [4-Sep-1995] $)

  $( Absorption into embedded conjunct. $)
  anabs5 $p |- ( ( ph /\ ( ph /\ ps ) ) <-> ( ph /\ ps ) ) $=
    ( wa ancom anabs1 bitr3i ) AABCZCGACGGADABEF $.
    $( [20-Jul-1996] $)

  $( Absorption into embedded conjunct. $)
  anabs7 $p |- ( ( ps /\ ( ph /\ ps ) ) <-> ( ph /\ ps ) ) $=
    ( wa pm3.27 ancri impbii ) BABCZCGBGDGBABDEF $.
    $( [20-Jul-1996] $)

  ${
    anabsi5.1 $e |- ( ph -> ( ( ph /\ ps ) -> ch ) ) $.
    $( Absorption of antecedent into conjunction. $)
    anabsi5 $p |- ( ( ph /\ ps ) -> ch ) $=
      ( wa wi adantr pm2.43i ) ABEZCAICFBDGH $.
      $( [11-Jun-1995] $)
  $}

  ${
    anabsi6.1 $e |- ( ph -> ( ( ps /\ ph ) -> ch ) ) $.
    $( Absorption of antecedent into conjunction. $)
    anabsi6 $p |- ( ( ph /\ ps ) -> ch ) $=
      ( ancomsd anabsi5 ) ABCABACDEF $.
      $( [14-Aug-2000] $)
  $}

  ${
    anabsi7.1 $e |- ( ps -> ( ( ph /\ ps ) -> ch ) ) $.
    $( Absorption of antecedent into conjunction. $)
    anabsi7 $p |- ( ( ph /\ ps ) -> ch ) $=
      ( exp3a pm2.43b imp ) ABCABCBABCDEFG $.
      $( [20-Jul-1996] $)
  $}

  ${
    anabsi8.1 $e |- ( ps -> ( ( ps /\ ph ) -> ch ) ) $.
    $( Absorption of antecedent into conjunction. $)
    anabsi8 $p |- ( ( ph /\ ps ) -> ch ) $=
      ( anabsi5 ancoms ) BACBACDEF $.
      $( [26-Sep-1999] $)
  $}

  ${
    anabss1.1 $e |- ( ( ( ph /\ ps ) /\ ph ) -> ch ) $.
    $( Absorption of antecedent into conjunction. $)
    anabss1 $p |- ( ( ph /\ ps ) -> ch ) $=
      ( wa adantrr anidms ) ABEZCHACBDFG $.
      $( [20-Jul-1996] $)
  $}

  ${
    anabss3.1 $e |- ( ( ( ph /\ ps ) /\ ps ) -> ch ) $.
    $( Absorption of antecedent into conjunction. $)
    anabss3 $p |- ( ( ph /\ ps ) -> ch ) $=
      ( wa adantrl anidms ) ABEZCHBCADFG $.
      $( [20-Jul-1996] $)
  $}

  ${
    anabss4.1 $e |- ( ( ( ps /\ ph ) /\ ps ) -> ch ) $.
    $( Absorption of antecedent into conjunction. $)
    anabss4 $p |- ( ( ph /\ ps ) -> ch ) $=
      ( anabss1 ancoms ) BACBACDEF $.
      $( [20-Jul-1996] $)
  $}

  ${
    anabss5.1 $e |- ( ( ph /\ ( ph /\ ps ) ) -> ch ) $.
    $( Absorption of antecedent into conjunction. $)
    anabss5 $p |- ( ( ph /\ ps ) -> ch ) $=
      ( wa adantlr anidms ) ABEZCAHCBDFG $.
      $( [10-May-1994] $)
  $}

  ${
    anabss7.1 $e |- ( ( ps /\ ( ph /\ ps ) ) -> ch ) $.
    $( Absorption of antecedent into conjunction. $)
    anabss7 $p |- ( ( ph /\ ps ) -> ch ) $=
      ( wa ex anabsi7 ) ABCBABECDFG $.
      $( [20-Jul-1996] $)
  $}

  ${
    anabsan.1 $e |- ( ( ( ph /\ ph ) /\ ps ) -> ch ) $.
    $( Absorption of antecedent with conjunction. $)
    anabsan $p |- ( ( ph /\ ps ) -> ch ) $=
      ( an1rs anabss1 ) ABCAABCDEF $.
      $( [24-Mar-1996] $)
  $}

  ${
    anabsan2.1 $e |- ( ( ph /\ ( ps /\ ps ) ) -> ch ) $.
    $( Absorption of antecedent with conjunction. $)
    anabsan2 $p |- ( ( ph /\ ps ) -> ch ) $=
      ( anassrs anabss3 ) ABCABBCDEF $.
      $( [10-May-2004] $) $( [10-May-2004] $)
  $}

  $( Rearrangement of 4 conjuncts. $)
  an4 $p |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) <->
              ( ( ph /\ ch ) /\ ( ps /\ th ) ) ) $=
    ( wa an12 anbi2i anass 3bitr4i ) ABCDEZEZEACBDEZEZEABEJEACELEKMABCDFGABJHAC
    LHI $.
    $( [10-Jul-1994] $)

  $( Rearrangement of 4 conjuncts. $)
  an42 $p |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) <->
                 ( ( ph /\ ch ) /\ ( th /\ ps ) ) ) $=
    ( wa an4 ancom anbi2i bitri ) ABECDEEACEZBDEZEJDBEZEABCDFKLJBDGHI $.
    $( [7-Feb-1996] $)

  ${
    an4s.1 $e |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) -> ta ) $.
    $( Inference rearranging 4 conjuncts in antecedent. $)
    an4s $p |- ( ( ( ph /\ ch ) /\ ( ps /\ th ) ) -> ta ) $=
      ( wa an4 sylbi ) ACGBDGGABGCDGGEACBDHFI $.
      $( [10-Aug-1995] $)
  $}

  ${
    an41r3s.1 $e |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) -> ta ) $.
    $( Inference rearranging 4 conjuncts in antecedent. $)
    an42s $p |- ( ( ( ph /\ ch ) /\ ( th /\ ps ) ) -> ta ) $=
      ( wa an42 sylbir ) ACGDBGGABGCDGGEABCDHFI $.
      $( [10-Aug-1995] $)
  $}

  $( Distribution of conjunction over conjunction. $)
  anandi $p |- ( ( ph /\ ( ps /\ ch ) ) <->
               ( ( ph /\ ps ) /\ ( ph /\ ch ) ) ) $=
    ( wa anidm anbi1i an4 bitr3i ) ABCDZDAADZIDABDACDDJAIAEFAABCGH $.
    $( [14-Aug-1995] $)

  $( Distribution of conjunction over conjunction. $)
  anandir $p |- ( ( ( ph /\ ps ) /\ ch ) <->
               ( ( ph /\ ch ) /\ ( ps /\ ch ) ) ) $=
    ( wa anidm anbi2i an4 bitr3i ) ABDZCDICCDZDACDBCDDJCICEFABCCGH $.
    $( [24-Aug-1995] $)

  ${
    anandis.1 $e |- ( ( ( ph /\ ps ) /\ ( ph /\ ch ) ) -> ta ) $.
    $( Inference that undistributes conjunction in the antecedent. $)
    anandis $p |- ( ( ph /\ ( ps /\ ch ) ) -> ta ) $=
      ( wa an4s anabsan ) ABCFDABACDEGH $.
      $( [7-Jun-2004] $) $( [7-Jun-2004] $)
  $}

  ${
    anandirs.1 $e |- ( ( ( ph /\ ch ) /\ ( ps /\ ch ) ) -> ta ) $.
    $( Inference that undistributes conjunction in the antecedent. $)
    anandirs $p |- ( ( ( ph /\ ps ) /\ ch ) -> ta ) $=
      ( wa an4s anabsan2 ) ABFCDACBCDEGH $.
      $( [8-Jun-2004] $) $( [7-Jun-2004] $)
  $}

  $( A theorem similar to the standard definition of the biconditional.
     Definition of [Margaris] p. 49. $)
  dfbi2 $p |- ( ( ph <-> ps ) <-> ( ( ph -> ps ) /\ ( ps -> ph ) ) ) $=
    ( wb wi wn wa dfbi1 df-an bitr4i ) ABCABDZBADZEDEJKFABGJKHI $.
    $( [5-Aug-1993] $)

  $( Definition ~ df-bi rewritten in an abbreviated form to help intuitive
     understanding of that definition.  Note that it is a conjunction of
     two implications; one which asserts properties that follow from the
     biconditional and one which asserts properties that imply the
     biconditional. $)
  dfbi $p |- ( ( ( ph <-> ps ) -> ( ( ph -> ps ) /\ ( ps -> ph ) ) )
        /\ ( ( ( ph -> ps ) /\ ( ps -> ph ) ) -> ( ph <-> ps ) ) ) $=
    ( wb wi wa dfbi2 biimpi biimpri pm3.2i ) ABCZABDBADEZDKJDJKABFZGJKLHI $.
    $( [16-Aug-2008] $) $( [15-Aug-2008] $)

  ${
    impbid.1 $e |- ( ph -> ( ps -> ch ) ) $.
    impbid.2 $e |- ( ph -> ( ch -> ps ) ) $.
    $( Deduce an equivalence from two implications. $)
    impbid $p |- ( ph -> ( ps <-> ch ) ) $=
      ( wi wa wb jca dfbi2 sylibr ) ABCFZCBFZGBCHALMDEIBCJK $.
      $( [5-Aug-1993] $)
  $}

  ${
    impbid1.1 $e |- ( ph -> ( ps -> ch ) ) $.
    impbid1.2 $e |- ( ch -> ps ) $.
    $( Infer an equivalence from two implications. $)
    impbid1 $p |- ( ph -> ( ps <-> ch ) ) $=
      ( wi a1i impbid ) ABCDCBFAEGH $.
      $( [7-Mar-2007] $) $( [6-Mar-2007] $)
  $}

  ${
    impbid2.1 $e |- ( ps -> ch ) $.
    impbid2.2 $e |- ( ph -> ( ch -> ps ) ) $.
    $( Infer an equivalence from two implications. $)
    impbid2 $p |- ( ph -> ( ps <-> ch ) ) $=
      ( wi a1i impbid ) ABCBCFADGEH $.
      $( [7-Mar-2007] $) $( [6-Mar-2007] $)
  $}

  ${
    impbida.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    impbida.2 $e |- ( ( ph /\ ch ) -> ps ) $.
    $( Deduce an equivalence from two implications. $)
    impbida $p |- ( ph -> ( ps <-> ch ) ) $=
      ( ex impbid ) ABCABCDFACBEFG $.
      $( [20-Feb-2007] $) $( [17-Feb-2007] $)
  $}

  $( Commutative law for equivalence.  Theorem *4.21 of [WhiteheadRussell]
     p. 117. $)
  bicom $p |- ( ( ph <-> ps ) <-> ( ps <-> ph ) ) $=
    ( wi wa wb ancom dfbi2 3bitr4i ) ABCZBACZDJIDABEBAEIJFABGBAGH $.
    $( [5-Aug-1993] $)

  ${
    bicomd.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Commute two sides of a biconditional in a deduction. $)
    bicomd $p |- ( ph -> ( ch <-> ps ) ) $=
      ( wb bicom sylib ) ABCECBEDBCFG $.
      $( [5-Aug-1993] $)
  $}

  $( Contraposition.  Theorem *4.11 of [WhiteheadRussell] p. 117. $)
  notbi $p |- ( ( ph <-> ps ) <-> ( -. ph <-> -. ps ) ) $=
    ( wb wn wi wa con34b anbi12i dfbi2 3bitr4i bicom bitri ) ABCZBDZADZCZONCABE
    ZBAEZFNOEZONEZFMPQSRTABGBAGHABINOIJNOKL $.
    $( [21-May-1994] $)

  ${
    con4bii.1 $e |- ( -. ph <-> -. ps ) $.
    $( A contraposition inference. $)
    con4bii $p |- ( ph <-> ps ) $=
      ( wb wn notbi mpbir ) ABDAEBEDCABFG $.
      $( [21-May-1994] $)
  $}

  ${
    con4bid.1 $e |- ( ph -> ( -. ps <-> -. ch ) ) $.
    $( A contraposition deduction. $)
    con4bid $p |- ( ph -> ( ps <-> ch ) ) $=
      ( wn wb notbi sylibr ) ABECEFBCFDBCGH $.
      $( [21-May-1994] $)
  $}

  $( Contraposition.  Theorem *4.12 of [WhiteheadRussell] p. 117. $)
  con2bi $p |- ( ( ph <-> -. ps ) <-> ( ps <-> -. ph ) ) $=
    ( wn wi wa wb con2b con1b anbi12i dfbi2 3bitr4i ) ABCZDZLADZEBACZDZOBDZEALF
    BOFMPNQABGBAHIALJBOJK $.
    $( [15-Apr-1995] $)

  ${
    con2bid.1 $e |- ( ph -> ( ps <-> -. ch ) ) $.
    $( A contraposition deduction. $)
    con2bid $p |- ( ph -> ( ch <-> -. ps ) ) $=
      ( wn wb con2bi sylibr ) ABCEFCBEFDCBGH $.
      $( [15-Apr-1995] $)
  $}

  ${
    con1bid.1 $e |- ( ph -> ( -. ps <-> ch ) ) $.
    $( A contraposition deduction. $)
    con1bid $p |- ( ph -> ( -. ch <-> ps ) ) $=
      ( wn bicomd con2bid ) ABCEACBABECDFGF $.
      $( [9-Oct-1999] $)
  $}

  ${
    bitrd.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    bitrd.2 $e |- ( ph -> ( ch <-> th ) ) $.
    $( Deduction form of ~ bitri . $)
    bitrd $p |- ( ph -> ( ps <-> th ) ) $=
      ( biimpd sylibd biimprd sylibrd impbid ) ABDABCDABCEGFHADCBACDFIEJK $.
      $( [5-Aug-1993] $)
  $}

  ${
    bitr2d.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    bitr2d.2 $e |- ( ph -> ( ch <-> th ) ) $.
    $( Deduction form of ~ bitr2i . $)
    bitr2d $p |- ( ph -> ( th <-> ps ) ) $=
      ( bitrd bicomd ) ABDABCDEFGH $.
      $( [11-Jun-2004] $) $( [9-Jun-2004] $)
  $}

  ${
    bitr3d.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    bitr3d.2 $e |- ( ph -> ( ps <-> th ) ) $.
    $( Deduction form of ~ bitr3i . $)
    bitr3d $p |- ( ph -> ( ch <-> th ) ) $=
      ( bicomd bitrd ) ACBDABCEGFH $.
      $( [5-Aug-1993] $)
  $}

  ${
    bitr4d.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    bitr4d.2 $e |- ( ph -> ( th <-> ch ) ) $.
    $( Deduction form of ~ bitr4i . $)
    bitr4d $p |- ( ph -> ( ps <-> th ) ) $=
      ( bicomd bitrd ) ABCDEADCFGH $.
      $( [5-Aug-1993] $)
  $}

  ${
    syl5bb.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    syl5bb.2 $e |- ( th <-> ps ) $.
    $( A syllogism inference from two biconditionals. $)
    syl5bb $p |- ( ph -> ( th <-> ch ) ) $=
      ( wb a1i bitrd ) ADBCDBGAFHEI $.
      $( [5-Aug-1993] $)
  $}

  ${
    syl5rbb.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    syl5rbb.2 $e |- ( th <-> ps ) $.
    $( A syllogism inference from two biconditionals. $)
    syl5rbb $p |- ( ph -> ( ch <-> th ) ) $=
      ( syl5bb bicomd ) ADCABCDEFGH $.
      $( [5-Aug-1993] $)
  $}

  ${
    syl5bbr.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    syl5bbr.2 $e |- ( ps <-> th ) $.
    $( A syllogism inference from two biconditionals. $)
    syl5bbr $p |- ( ph -> ( th <-> ch ) ) $=
      ( bicomi syl5bb ) ABCDEBDFGH $.
      $( [5-Aug-1993] $)
  $}

  ${
    syl5rbbr.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    syl5rbbr.2 $e |- ( ps <-> th ) $.
    $( A syllogism inference from two biconditionals. $)
    syl5rbbr $p |- ( ph -> ( ch <-> th ) ) $=
      ( bicomi syl5rbb ) ABCDEBDFGH $.
      $( [25-Nov-1994] $)
  $}

  ${
    syl6bb.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    syl6bb.2 $e |- ( ch <-> th ) $.
    $( A syllogism inference from two biconditionals. $)
    syl6bb $p |- ( ph -> ( ps <-> th ) ) $=
      ( wb a1i bitrd ) ABCDECDGAFHI $.
      $( [5-Aug-1993] $)
  $}

  ${
    syl6rbb.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    syl6rbb.2 $e |- ( ch <-> th ) $.
    $( A syllogism inference from two biconditionals. $)
    syl6rbb $p |- ( ph -> ( th <-> ps ) ) $=
      ( syl6bb bicomd ) ABDABCDEFGH $.
      $( [5-Aug-1993] $)
  $}

  ${
    syl6bbr.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    syl6bbr.2 $e |- ( th <-> ch ) $.
    $( A syllogism inference from two biconditionals. $)
    syl6bbr $p |- ( ph -> ( ps <-> th ) ) $=
      ( bicomi syl6bb ) ABCDEDCFGH $.
      $( [5-Aug-1993] $)
  $}

  ${
    syl6rbbr.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    syl6rbbr.2 $e |- ( th <-> ch ) $.
    $( A syllogism inference from two biconditionals. $)
    syl6rbbr $p |- ( ph -> ( th <-> ps ) ) $=
      ( bicomi syl6rbb ) ABCDEDCFGH $.
      $( [25-Nov-1994] $)
  $}

  ${
    sylan9bb.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    sylan9bb.2 $e |- ( th -> ( ch <-> ta ) ) $.
    $( Nested syllogism inference conjoining dissimilar antecedents. $)
    sylan9bb $p |- ( ( ph /\ th ) -> ( ps <-> ta ) ) $=
      ( wa wb adantr adantl bitrd ) ADHBCEABCIDFJDCEIAGKL $.
      $( [4-Mar-1995] $)
  $}

  ${
    sylan9bbr.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    sylan9bbr.2 $e |- ( th -> ( ch <-> ta ) ) $.
    $( Nested syllogism inference conjoining dissimilar antecedents. $)
    sylan9bbr $p |- ( ( th /\ ph ) -> ( ps <-> ta ) ) $=
      ( wb sylan9bb ancoms ) ADBEHABCDEFGIJ $.
      $( [4-Mar-1995] $)
  $}

  ${
    3imtr3d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    3imtr3d.2 $e |- ( ph -> ( ps <-> th ) ) $.
    3imtr3d.3 $e |- ( ph -> ( ch <-> ta ) ) $.
    $( More general version of ~ 3imtr3i .  Useful for converting
       conditional definitions in a formula. $)
    3imtr3d $p |- ( ph -> ( th -> ta ) ) $=
      ( sylibd sylbird ) ADBEGABCEFHIJ $.
      $( [8-Apr-1996] $)
  $}

  ${
    3imtr4d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    3imtr4d.2 $e |- ( ph -> ( th <-> ps ) ) $.
    3imtr4d.3 $e |- ( ph -> ( ta <-> ch ) ) $.
    $( More general version of ~ 3imtr4i .  Useful for converting
       conditional definitions in a formula. $)
    3imtr4d $p |- ( ph -> ( th -> ta ) ) $=
      ( sylibrd sylbid ) ADBEGABCEFHIJ $.
      $( [26-Oct-1995] $)
  $}

  ${
    3bitrd.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    3bitrd.2 $e |- ( ph -> ( ch <-> th ) ) $.
    3bitrd.3 $e |- ( ph -> ( th <-> ta ) ) $.
    $( Deduction from transitivity of biconditional. $)
    3bitrd $p |- ( ph -> ( ps <-> ta ) ) $=
      ( bitrd ) ABDEABCDFGIHI $.
      $( [13-Aug-1999] $)

    $( Deduction from transitivity of biconditional. $)
    3bitrrd $p |- ( ph -> ( ta <-> ps ) ) $=
      ( bitr2d bitr3d ) ADEBHABCDFGIJ $.
      $( [11-Aug-2006] $) $( [4-Aug-2006] $)
  $}

  ${
    3bitr2d.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    3bitr2d.2 $e |- ( ph -> ( th <-> ch ) ) $.
    3bitr2d.3 $e |- ( ph -> ( th <-> ta ) ) $.
    $( Deduction from transitivity of biconditional. $)
    3bitr2d $p |- ( ph -> ( ps <-> ta ) ) $=
      ( bitr4d bitrd ) ABDEABCDFGIHJ $.
      $( [11-Aug-2006] $) $( [4-Aug-2006] $)

    $( Deduction from transitivity of biconditional. $)
    3bitr2rd $p |- ( ph -> ( ta <-> ps ) ) $=
      ( bitr4d bitr2d ) ABDEABCDFGIHJ $.
      $( [11-Aug-2006] $) $( [4-Aug-2006] $)
  $}

  ${
    3bitr3d.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    3bitr3d.2 $e |- ( ph -> ( ps <-> th ) ) $.
    3bitr3d.3 $e |- ( ph -> ( ch <-> ta ) ) $.
    $( Deduction from transitivity of biconditional.  Useful for converting
       conditional definitions in a formula. $)
    3bitr3d $p |- ( ph -> ( th <-> ta ) ) $=
      ( bitr3d bitrd ) ADCEABDCGFIHJ $.
      $( [24-Apr-1996] $)

    $( Deduction from transitivity of biconditional. $)
    3bitr3rd $p |- ( ph -> ( ta <-> th ) ) $=
      ( bitr3d ) ACEDHABCDFGII $.
      $( [11-Aug-2006] $) $( [4-Aug-2006] $)
  $}

  ${
    3bitr4d.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    3bitr4d.2 $e |- ( ph -> ( th <-> ps ) ) $.
    3bitr4d.3 $e |- ( ph -> ( ta <-> ch ) ) $.
    $( Deduction from transitivity of biconditional.  Useful for converting
       conditional definitions in a formula. $)
    3bitr4d $p |- ( ph -> ( th <-> ta ) ) $=
      ( bitr4d bitrd ) ADBEGABCEFHIJ $.
      $( [18-Oct-1995] $)

    $( Deduction from transitivity of biconditional. $)
    3bitr4rd $p |- ( ph -> ( ta <-> th ) ) $=
      ( bitr4d ) AEBDAECBHFIGI $.
      $( [11-Aug-2006] $) $( [4-Aug-2006] $)
  $}

  ${
    3imtr3g.1 $e |- ( ph -> ( ps -> ch ) ) $.
    3imtr3g.2 $e |- ( ps <-> th ) $.
    3imtr3g.3 $e |- ( ch <-> ta ) $.
    $( More general version of ~ 3imtr3i .  Useful for converting
       definitions in a formula. $)
    3imtr3g $p |- ( ph -> ( th -> ta ) ) $=
      ( wa imp anbi2i 3imtr3i ex ) ADEABICADIEABCFJBDAGKHLM $.
      $( [20-May-1996] $)
  $}

  ${
    3imtr4g.1 $e |- ( ph -> ( ps -> ch ) ) $.
    3imtr4g.2 $e |- ( th <-> ps ) $.
    3imtr4g.3 $e |- ( ta <-> ch ) $.
    $( More general version of ~ 3imtr4i .  Useful for converting
       definitions in a formula. $)
    3imtr4g $p |- ( ph -> ( th -> ta ) ) $=
      ( bicomi 3imtr3g ) ABCDEFDBGIECHIJ $.
      $( [20-May-1996] $)
  $}

  ${
    3bitr3g.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    3bitr3g.2 $e |- ( ps <-> th ) $.
    3bitr3g.3 $e |- ( ch <-> ta ) $.
    $( More general version of ~ 3bitr3i .  Useful for converting
       definitions in a formula. $)
    3bitr3g $p |- ( ph -> ( th <-> ta ) ) $=
      ( syl5bbr syl6bb ) ADCEABCDFGIHJ $.
      $( [4-Jun-1995] $)
  $}

  ${
    3bitr4g.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    3bitr4g.2 $e |- ( th <-> ps ) $.
    3bitr4g.3 $e |- ( ta <-> ch ) $.
    $( More general version of ~ 3bitr4i .  Useful for converting
       definitions in a formula. $)
    3bitr4g $p |- ( ph -> ( th <-> ta ) ) $=
      ( syl5bb syl6bbr ) ADCEABCDFGIHJ $.
      $( [5-Aug-1993] $)
  $}

  $( Theorem *3.47 of [WhiteheadRussell] p. 113.  It was proved by Leibniz, and
     it evidently pleased him enough to call it 'praeclarum theorema' (splendid
     theorem). $)
  prth $p |- ( ( ( ph -> ps ) /\ ( ch -> th ) ) ->
               ( ( ph /\ ch ) -> ( ps /\ th ) ) ) $=
    ( wi wa pm3.2 imim2d imim2i com23 imp4b ) ABEZCDEZACBDFZLAMCNEZBMOEABDNCBDG
    HIJK $.
    $( [12-Aug-1993] $)

  $( Theorem *3.48 of [WhiteheadRussell] p. 114. $)
  pm3.48 $p |- ( ( ( ph -> ps ) /\ ( ch -> th ) ) ->
               ( ( ph \/ ch ) -> ( ps \/ th ) ) ) $=
    ( wi wa wn wo pm3.26 con3d pm3.27 imim12d df-or 3imtr4g ) ABEZCDEZFZAGZCEBG
    ZDEACHBDHQSRCDQABOPIJOPKLACMBDMN $.
    $( [28-Jan-1997] $)

  ${
    anim12d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    anim12d.2 $e |- ( ph -> ( th -> ta ) ) $.
    $( Conjoin antecedents and consequents in a deduction. $)
    anim12d $p |- ( ph -> ( ( ps /\ th ) -> ( ch /\ ta ) ) ) $=
      ( wi wa prth sylanc ) BCHDEHBDICEIHABCDEJFGK $.
      $( [3-Apr-1994] $)
  $}

  ${
    anim12ii.1 $e |- ( ph -> ( ps -> ch ) ) $.
    anim12ii.2 $e |- ( th -> ( ps -> ta ) ) $.
    $( Conjoin antecedents and consequents in a deduction. $)
    anim12ii $p |- ( ( ph /\ th ) -> ( ps -> ( ch /\ ta ) ) ) $=
      ( wa com12 anim12d ) BADHCEHBACDEABCFIDBEGIJI $.
      $( [12-Nov-2007] $) $( [11-Nov-2007] $)
  $}

  ${
    anim1d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Add a conjunct to right of antecedent and consequent in a deduction. $)
    anim1d $p |- ( ph -> ( ( ps /\ th ) -> ( ch /\ th ) ) ) $=
      ( idd anim12d ) ABCDDEADFG $.
      $( [3-Apr-1994] $)

    $( Add a conjunct to left of antecedent and consequent in a deduction. $)
    anim2d $p |- ( ph -> ( ( th /\ ps ) -> ( th /\ ch ) ) ) $=
      ( idd anim12d ) ADDBCADFEG $.
      $( [5-Aug-1993] $)
  $}

  $( Theorem *3.45 (Fact) of [WhiteheadRussell] p. 113. $)
  pm3.45 $p |-  ( ( ph -> ps ) -> ( ( ph /\ ch ) -> ( ps /\ ch ) ) ) $=
    ( wi id anim1d ) ABDZABCGEF $.
    $( [17-Jan-2005] $) $( [3-Jan-2005] $)

  ${
    $v et $. $( Greek eta $)
    im2an9.wet $f wff et $.
    im2an9.1 $e |- ( ph -> ( ps -> ch ) ) $.
    im2an9.2 $e |- ( th -> ( ta -> et ) ) $.

    $( Deduction joining nested implications to form implication of
       conjunctions. $)
    im2anan9 $p |- ( ( ph /\ th ) -> ( ( ps /\ ta ) -> ( ch /\ et ) ) ) $=
      ( wa wi adantr adantl anim12d ) ADIBCEFABCJDGKDEFJAHLM $.
      $( [29-Feb-1996] $)

    $( Deduction joining nested implications to form implication of
       conjunctions. $)
    im2anan9r $p |- ( ( th /\ ph ) -> ( ( ps /\ ta ) -> ( ch /\ et ) ) ) $=
      ( wa wi adantl adantr anim12d ) DAIBCEFABCJDGKDEFJAHLM $.
      $( [29-Feb-1996] $)

  $}

  ${
    orim12d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    orim12d.2 $e |- ( ph -> ( th -> ta ) ) $.
    $( Disjoin antecedents and consequents in a deduction. $)
    orim12d $p |- ( ph -> ( ( ps \/ th ) -> ( ch \/ ta ) ) ) $=
      ( wi wo pm3.48 sylanc ) BCHDEHBDICEIHABCDEJFGK $.
      $( [10-May-1994] $)
  $}

  ${
    orim1d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Disjoin antecedents and consequents in a deduction. $)
    orim1d $p |- ( ph -> ( ( ps \/ th ) -> ( ch \/ th ) ) ) $=
      ( idd orim12d ) ABCDDEADFG $.
      $( [23-Apr-1995] $)

    $( Disjoin antecedents and consequents in a deduction. $)
    orim2d $p |- ( ph -> ( ( th \/ ps ) -> ( th \/ ch ) ) ) $=
      ( idd orim12d ) ADDBCADFEG $.
      $( [23-Apr-1995] $)
  $}

  $( Axiom *1.6 (Sum) of [WhiteheadRussell] p. 97. $)
  orim2 $p |-  ( ( ps -> ch ) -> ( ( ph \/ ps ) -> ( ph \/ ch ) ) ) $=
    ( wi id orim2d ) BCDZBCAGEF $.
    $( [16-May-2005] $) $( [3-Jan-2005] $)

  $( Theorem *2.38 of [WhiteheadRussell] p. 105. $)
  pm2.38 $p |-  ( ( ps -> ch ) -> ( ( ps \/ ph ) -> ( ch \/ ph ) ) ) $=
    ( wi id orim1d ) BCDZBCAGEF $.
    $( [6-Mar-2008] $) $( [6-Mar-2008] $)

  $( Theorem *2.36 of [WhiteheadRussell] p. 105. $)
  pm2.36 $p |-  ( ( ps -> ch ) -> ( ( ph \/ ps ) -> ( ch \/ ph ) ) ) $=
    ( wi wo pm2.38 pm1.4 syl5 ) BCDBAECAEABEABCFABGH $.
    $( [6-Mar-2008] $) $( [6-Mar-2008] $)

  $( Theorem *2.37 of [WhiteheadRussell] p. 105. $)
  pm2.37 $p |-  ( ( ps -> ch ) -> ( ( ps \/ ph ) -> ( ph \/ ch ) ) ) $=
    ( wi wo pm2.38 pm1.4 syl6 ) BCDBAECAEACEABCFCAGH $.
    $( [6-Mar-2008] $) $( [6-Mar-2008] $)

  $( Theorem *2.73 of [WhiteheadRussell] p. 108. $)
  pm2.73 $p |-  ( ( ph -> ps ) -> ( ( ( ph \/ ps ) \/ ch ) ->
                ( ps \/ ch ) ) ) $=
    ( wi wo pm2.621 orim1d ) ABDABEBCABFG $.
    $( [29-Apr-2005] $) $( [3-Jan-2005] $)

  $( Theorem *2.74 of [WhiteheadRussell] p. 108. $)
  pm2.74 $p |-  ( ( ps -> ph ) -> ( ( ( ph \/ ps ) \/ ch ) ->
                ( ph \/ ch ) ) ) $=
    ( wo wi wn orel2 orim1d orc a1d ja ) BAABDZCDZACDZEBFLACBAGHANMACIJK $.
    $( [9-May-2005] $) $( [3-Jan-2005] $)

  $( Theorem *2.75 of [WhiteheadRussell] p. 108. $)
  pm2.75 $p |-  ( ( ph \/ ps ) ->
                ( ( ph \/ ( ps -> ch ) ) -> ( ph \/ ch ) ) ) $=
    ( wi wo orc a1d pm2.27 orim2d jaoi ) AABCDZEZACEZDBAMLACFGBKCABCHIJ $.
    $( [14-May-2005] $) $( [3-Jan-2005] $)

  $( Theorem *2.76 of [WhiteheadRussell] p. 108. $)
  pm2.76 $p |-  ( ( ph \/ ( ps -> ch ) ) ->
                ( ( ph \/ ps ) -> ( ph \/ ch ) ) ) $=
    ( wo wi pm2.75 com12 ) ABDABCEDACDABCFG $.
    $( [16-May-2005] $) $( [3-Jan-2005] $)

  $( Theorem *2.8 of [WhiteheadRussell] p. 108. $)
  pm2.8 $p |-  ( ( ps \/ ch ) -> ( ( -. ch \/ th ) -> ( ps \/ th ) ) ) $=
    ( wn wo wi orc a1d pm2.24 orim1d jaoi ) ABDZCEZACEZFBANMACGHBLACBAIJK $.
    $( [16-May-2005] $) $( [3-Jan-2005] $)

  $( Theorem *2.81 of [WhiteheadRussell] p. 108. $)
  pm2.81 $p |-  ( ( ps -> ( ch -> th ) ) -> ( ( ph \/ ps ) ->
                ( ( ph \/ ch ) -> ( ph \/ th ) ) ) ) $=
    ( wi wo orim2 pm2.76 syl6 ) BCDEZEABFAJFACFADFEABJGACDHI $.
    $( [17-May-2005] $) $( [3-Jan-2005] $)

  $( Theorem *2.82 of [WhiteheadRussell] p. 108. $)
  pm2.82 $p |-  ( ( ( ph \/ ps ) \/ ch ) -> ( ( ( ph \/ -. ch ) \/ th ) ->
                ( ( ph \/ ps ) \/ th ) ) ) $=
    ( wo wn wi ax-1 pm2.24 orim2d jaoi orim1d ) ABEZCEACFZEZMDMOMGCMOHCNBACBIJK
    L $.
    $( [18-May-2005] $) $( [3-Jan-2005] $)

  $( Theorem *2.85 of [WhiteheadRussell] p. 108. $)
  pm2.85 $p |-  ( ( ( ph \/ ps ) -> ( ph \/ ch ) ) ->
                ( ph \/ ( ps -> ch ) ) ) $=
    ( wo wi wn imor pm2.48 orim1i sylbi orbi2i orordi bitr2i sylib ) ABDZACDZEZ
    ABFZDZPDZABCEZDZQOFZPDTOPGUCSPABHIJUBARCDZDTUAUDABCGKARCLMN $.
    $( [9-Jan-2005] $) $( [3-Jan-2005] $)

  ${
    pm3.2ni.1 $e |- -. ph $.
    pm3.2ni.2 $e |- -. ps $.
    $( Infer negated disjunction of negated premises. $)
    pm3.2ni $p |- -. ( ph \/ ps ) $=
      ( wo wn wa pm3.2i ioran mpbir ) ABEFAFZBFZGKLCDHABIJ $.
      $( [4-Apr-1995] $)
  $}

  $( Absorption of redundant internal disjunct.  Compare Theorem *4.45
     of [WhiteheadRussell] p. 119. $)
  orabs $p |- ( ph <-> ( ( ph \/ ps ) /\ ph ) ) $=
    ( wo wa orc ancri pm3.27 impbii ) AABCZADAIABEFIAGH $.
    $( [5-Aug-1993] $)

  $( Absorb a disjunct into a conjunct.  (Contributed by Roy F. Longton
     23-Jun-2005.) $)
  oranabs $p |- ( ( ( ph \/ -. ps ) /\ ps ) <-> ( ph /\ ps ) ) $=
    ( wn wo wa pm5.61 notnot anbi2i 3bitr4i ) ABCZDZJCZEALEKBEABEAJFBLKBGZHBLAM
    HI $.
    $( [12-Apr-2008] $) $( [23-Jun-2005] $)

  $( Distribution of implication over biconditional.  Theorem *5.74 of
     [WhiteheadRussell] p. 126. $)
  pm5.74 $p |- ( ( ph -> ( ps <-> ch ) ) <->
               ( ( ph -> ps ) <-> ( ph -> ch ) ) ) $=
    ( wb wi bi1 imim3i bi2 impbid wa pm2.86d anim12d pm4.24 dfbi2 3imtr4g 
    impbii ) ABCDZEZABEZACEZDZRSTQBCABCFGQCBABCHGIUAAAJBCEZCBEZJAQUAAUBAUCUAABC
    STFKUAACBSTHKLAMBCNOP $.
    $( [1-Aug-1994] $)

  ${
    pm5.74i.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Distribution of implication over biconditional (inference rule). $)
    pm5.74i $p |- ( ( ph -> ps ) <-> ( ph -> ch ) ) $=
      ( wb wi pm5.74 mpbi ) ABCEFABFACFEDABCGH $.
      $( [1-Aug-1994] $)
  $}

  ${
    pm5.74d.1 $e |- ( ph -> ( ps -> ( ch <-> th ) ) ) $.
    $( Distribution of implication over biconditional (deduction rule). $)
    pm5.74d $p |- ( ph -> ( ( ps -> ch ) <-> ( ps -> th ) ) ) $=
      ( wb wi pm5.74 sylib ) ABCDFGBCGBDGFEBCDHI $.
      $( [21-Mar-1996] $)
  $}

  ${
    pm5.74da.1 $e |- ( ( ph /\ ps ) -> ( ch <-> th ) ) $.
    $( Distribution of implication over biconditional (deduction rule). $)
    pm5.74da $p |- ( ph -> ( ( ps -> ch ) <-> ( ps -> th ) ) ) $=
      ( wb ex pm5.74d ) ABCDABCDFEGH $.
      $( [5-May-2007] $) $( [4-May-2007] $)
  $}

  ${
    pm5.74ri.1 $e |- ( ( ph -> ps ) <-> ( ph -> ch ) ) $.
    $( Distribution of implication over biconditional (reverse inference
       rule). $)
    pm5.74ri $p |- ( ph -> ( ps <-> ch ) ) $=
      ( wb wi pm5.74 mpbir ) ABCEFABFACFEDABCGH $.
      $( [1-Aug-1994] $)
  $}

  ${
    pm5.74rd.1 $e |- ( ph -> ( ( ps -> ch ) <-> ( ps -> th ) ) ) $.
    $( Distribution of implication over biconditional (deduction rule). $)
    pm5.74rd $p |- ( ph -> ( ps -> ( ch <-> th ) ) ) $=
      ( wi wb pm5.74 sylibr ) ABCFBDFGBCDGFEBCDHI $.
      $( [19-Mar-1997] $)
  $}

  ${
    mpbidi.min $e |- ( th -> ( ph -> ps ) ) $.
    mpbidi.maj $e |- ( ph -> ( ps <-> ch ) ) $.
    $( A deduction from a biconditional, related to modus ponens. $)
    mpbidi $p |- ( th -> ( ph -> ch ) ) $=
      ( wi pm5.74i sylib ) DABGACGEABCFHI $.
      $( [9-Aug-1994] $)
  $}

  $( Implication in terms of implication and biconditional. $)
  ibib $p |- ( ( ph -> ps ) <-> ( ph -> ( ph <-> ps ) ) ) $=
    ( wb wa pm3.4 pm3.26 a1d impbid ex bi1 com12 pm5.74i ) ABABCZABMABMABDZABAB
    ENABABFGHIMABABJKHL $.
    $( [31-Mar-1994] $)

  $( Implication in terms of implication and biconditional. $)
  ibibr $p |- ( ( ph -> ps ) <-> ( ph -> ( ps <-> ph ) ) ) $=
    ( wi wb ibib bicom imbi2i bitri ) ABCAABDZCABADZCABEIJAABFGH $.
    $( [6-Jun-2005] $) $( [29-Apr-2005] $)

  ${
    ibi.1 $e |- ( ph -> ( ph <-> ps ) ) $.
    $( Inference that converts a biconditional implied by one of its arguments,
       into an implication. $)
    ibi $p |- ( ph -> ps ) $=
      ( biimpd pm2.43i ) ABAABCDE $.
      $( [17-Oct-2003] $) $( [17-Oct-2003] $)
  $}

  ${
    ibir.1 $e |- ( ph -> ( ps <-> ph ) ) $.
    $( Inference that converts a biconditional implied by one of its arguments,
       into an implication. $)
    ibir $p |- ( ph -> ps ) $=
      ( bicomd ibi ) ABABACDE $.
      $( [28-Jul-2004] $) $( [22-Jul-2004] $)
  $}

  ${
    ibd.1 $e |- ( ph -> ( ps -> ( ps <-> ch ) ) ) $.
    $( Deduction that converts a biconditional implied by one of its arguments,
       into an implication. $)
    ibd $p |- ( ph -> ( ps -> ch ) ) $=
      ( wb wi ibib sylibr ) ABBCEFBCFDBCGH $.
      $( [27-Jun-2004] $) $( [26-Jun-2004] $)
  $}

  $( Theorem *5.501 of [WhiteheadRussell] p. 125. $)
  pm5.501 $p |-  ( ph -> ( ps <-> ( ph <-> ps ) ) ) $=
    ( wb ibib pm5.74ri ) ABABCABDE $.
    $( [1-Feb-2005] $) $( [3-Jan-2005] $)

  $( Distributive law for disjunction.  Theorem *4.41 of [WhiteheadRussell]
     p. 119. $)
  ordi $p |- ( ( ph \/ ( ps /\ ch ) ) <-> ( ( ph \/ ps ) /\ ( ph \/ ch ) ) ) $=
    ( wa wo pm3.26 orim2i pm3.27 jca wn wi df-or pm3.43i 3imtr4g sylbi imp 
    impbii ) ABCDZEZABEZACEZDSTUARBABCFGRCABCHGITUASTAJZBKZUASKABLUCUBCKUBRKUAS
    UBBCMACLARLNOPQ $.
    $( [5-Aug-1993] $)

  $( Distributive law for disjunction. $)
  ordir $p |- ( ( ( ph /\ ps ) \/ ch ) <->
              ( ( ph \/ ch ) /\ ( ps \/ ch ) ) ) $=
    ( wa wo ordi orcom anbi12i 3bitr4i ) CABDZECAEZCBEZDJCEACEZBCEZDCABFJCGMKNL
    ACGBCGHI $.
    $( [12-Aug-1994] $)

  $( Distributive law for implication over conjunction.  Compare Theorem
     *4.76 of [WhiteheadRussell] p. 121. $)
  jcab $p |- ( ( ph -> ( ps /\ ch ) ) <->
                 ( ( ph -> ps ) /\ ( ph -> ch ) ) ) $=
    ( wn wa wo wi ordi imor anbi12i 3bitr4i ) ADZBCEZFLBFZLCFZEAMGABGZACGZELBCH
    AMIPNQOABIACIJK $.
    $( [3-Apr-1994] $)

  $( Theorem *4.76 of [WhiteheadRussell] p. 121. $)
  pm4.76 $p |-  ( ( ( ph -> ps ) /\ ( ph -> ch ) ) <->
                ( ph -> ( ps /\ ch ) ) ) $=
    ( wa wi jcab bicomi ) ABCDEABEACEDABCFG $.
    $( [22-May-2005] $) $( [3-Jan-2005] $)

  ${
    jcad.1 $e |- ( ph -> ( ps -> ch ) ) $.
    jcad.2 $e |- ( ph -> ( ps -> th ) ) $.
    $( Deduction conjoining the consequents of two implications. $)
    jcad $p |- ( ph -> ( ps -> ( ch /\ th ) ) ) $=
      ( wa imp jca ex ) ABCDGABGCDABCEHABDFHIJ $.
      $( [5-Aug-1993] $)
  $}

  ${
    jctild.1 $e |- ( ph -> ( ps -> ch ) ) $.
    jctild.2 $e |- ( ph -> th ) $.
    $( Deduction conjoining a theorem to left of consequent in an
       implication. $)
    jctild $p |- ( ph -> ( ps -> ( th /\ ch ) ) ) $=
      ( a1d jcad ) ABDCADBFGEH $.
      $( [22-Apr-2005] $) $( [21-Apr-2005] $)
  $}

  ${
    jctird.1 $e |- ( ph -> ( ps -> ch ) ) $.
    jctird.2 $e |- ( ph -> th ) $.
    $( Deduction conjoining a theorem to right of consequent in an
       implication. $)
    jctird $p |- ( ph -> ( ps -> ( ch /\ th ) ) ) $=
      ( a1d jcad ) ABCDEADBFGH $.
      $( [22-Apr-2005] $) $( [21-Apr-2005] $)
  $}

  $( Theorem *3.43 (Comp) of [WhiteheadRussell] p. 113. $)
  pm3.43 $p |-  ( ( ( ph -> ps ) /\ ( ph -> ch ) ) ->
                ( ph -> ( ps /\ ch ) ) ) $=
    ( wa wi jcab biimpri ) ABCDEABEACEDABCFG $.
    $( [27-May-2005] $) $( [3-Jan-2005] $)

  $( Distributive law for conjunction.  Theorem *4.4 of [WhiteheadRussell]
     p. 118. $)
  andi $p |- ( ( ph /\ ( ps \/ ch ) ) <-> ( ( ph /\ ps ) \/ ( ph /\ ch ) ) ) $=
    ( wn wo wa ordi ioran orbi2i ianor anbi12i 3bitr4i notbii anor oran ) ADZBC
    EZDZEZDABFZDZACFZDZFZDAQFTUBESUDPBDZCDZFZEPUEEZPUFEZFSUDPUEUFGRUGPBCHIUAUHU
    CUIABJACJKLMAQNTUBOL $.
    $( [5-Aug-1993] $)

  $( Distributive law for conjunction. $)
  andir $p |- ( ( ( ph \/ ps ) /\ ch ) <->
              ( ( ph /\ ch ) \/ ( ps /\ ch ) ) ) $=
    ( wo wa andi ancom orbi12i 3bitr4i ) CABDZECAEZCBEZDJCEACEZBCEZDCABFJCGMKNL
    ACGBCGHI $.
    $( [12-Aug-1994] $)

  $( Double distributive law for disjunction. $)
  orddi $p |- ( ( ( ph /\ ps ) \/ ( ch /\ th ) ) <->
              ( ( ( ph \/ ch ) /\ ( ph \/ th ) ) /\
              ( ( ps \/ ch ) /\ ( ps \/ th ) ) ) ) $=
    ( wa wo ordir ordi anbi12i bitri ) ABECDEZFAKFZBKFZEACFADFEZBCFBDFEZEABKGLN
    MOACDHBCDHIJ $.
    $( [12-Aug-1994] $)

  $( Double distributive law for conjunction. $)
  anddi $p |- ( ( ( ph \/ ps ) /\ ( ch \/ th ) ) <->
              ( ( ( ph /\ ch ) \/ ( ph /\ th ) ) \/
              ( ( ps /\ ch ) \/ ( ps /\ th ) ) ) ) $=
    ( wo wa andir andi orbi12i bitri ) ABECDEZFAKFZBKFZEACFADFEZBCFBDFEZEABKGLN
    MOACDHBCDHIJ $.
    $( [12-Aug-1994] $)

  $( Prove formula-building rules for the biconditional connective. $)

  ${
    bibi.a $e |- ( ph <-> ps ) $.

    $( Inference adding a biconditional to the left in an equivalence. $)
    bibi2i $p |- ( ( ch <-> ph ) <-> ( ch <-> ps ) ) $=
      ( wb wi wa dfbi2 imbi1i anbi2i imbi2i anbi1i bitr4i 3bitri ) CAECAFZACFZG
      OBCFZGZCBEZCAHPQOABCDIJRCBFZQGSOTQABCDKLCBHMN $.
      $( [5-Aug-1993] $)

    $( Inference adding a biconditional to the right in an equivalence. $)
    bibi1i $p |- ( ( ph <-> ch ) <-> ( ps <-> ch ) ) $=
      ( wb bicom bibi2i 3bitri ) ACECAECBEBCEACFABCDGCBFH $.
      $( [5-Aug-1993] $)

    ${
      bibi12.2 $e |- ( ch <-> th ) $.
      $( The equivalence of two equivalences. $)
      bibi12i $p |- ( ( ph <-> ch ) <-> ( ps <-> th ) ) $=
        ( wb bibi2i bibi1i bitri ) ACGADGBDGCDAFHABDEIJ $.
        $( [5-Aug-1993] $)
    $}
  $}

  ${
    bid.1 $e |- ( ph -> ( ps <-> ch ) ) $.

    $( Deduction negating both sides of a logical equivalence. $)
    notbid $p |- ( ph -> ( -. ps <-> -. ch ) ) $=
      ( wb wn notbi sylib ) ABCEBFCFEDBCGH $.
      $( [21-May-1994] $)

    $( Deduction adding an antecedent to both sides of a logical
       equivalence. $)
    imbi2d $p |- ( ph -> ( ( th -> ps ) <-> ( th -> ch ) ) ) $=
      ( wb a1d pm5.74d ) ADBCABCFDEGH $.
      $( [5-Aug-1993] $)

    $( Deduction adding a consequent to both sides of a logical equivalence. $)
    imbi1d $p |- ( ph -> ( ( ps -> th ) <-> ( ch -> th ) ) ) $=
      ( wn wi notbid imbi2d con34b 3bitr4g ) ADFZBFZGLCFZGBDGCDGAMNLABCEHIBDJCD
      JK $.
      $( [5-Aug-1993] $)

    $( Deduction adding a left disjunct to both sides of a logical
       equivalence. $)
    orbi2d $p |- ( ph -> ( ( th \/ ps ) <-> ( th \/ ch ) ) ) $=
      ( wn wi wo imbi2d df-or 3bitr4g ) ADFZBGLCGDBHDCHABCLEIDBJDCJK $.
      $( [5-Aug-1993] $)

    $( Deduction adding a right disjunct to both sides of a logical
       equivalence. $)
    orbi1d $p |- ( ph -> ( ( ps \/ th ) <-> ( ch \/ th ) ) ) $=
      ( wo orbi2d orcom 3bitr4g ) ADBFDCFBDFCDFABCDEGBDHCDHI $.
      $( [5-Aug-1993] $)

    $( Deduction adding a left conjunct to both sides of a logical
       equivalence. $)
    anbi2d $p |- ( ph -> ( ( th /\ ps ) <-> ( th /\ ch ) ) ) $=
      ( wa biimpd anim2d biimprd impbid ) ADBFDCFABCDABCEGHACBDABCEIHJ $.
      $( [5-Aug-1993] $)

    $( Deduction adding a right conjunct to both sides of a logical
       equivalence. $)
    anbi1d $p |- ( ph -> ( ( ps /\ th ) <-> ( ch /\ th ) ) ) $=
      ( wa anbi2d ancom 3bitr4g ) ADBFDCFBDFCDFABCDEGBDHCDHI $.
      $( [5-Aug-1993] $)

    $( Deduction adding a biconditional to the left in an equivalence. $)
    bibi2d $p |- ( ph -> ( ( th <-> ps ) <-> ( th <-> ch ) ) ) $=
      ( wi wa wb imbi2d anbi1d imbi1d anbi2d bitrd dfbi2 3bitr4g ) ADBFZBDFZGZD
      CFZCDFZGZDBHDCHARSQGUAAPSQABCDEIJAQTSABCDEKLMDBNDCNO $.
      $( [5-Aug-1993] $)

    $( Deduction adding a biconditional to the right in an equivalence. $)
    bibi1d $p |- ( ph -> ( ( ps <-> th ) <-> ( ch <-> th ) ) ) $=
      ( wb bibi2d bicom 3bitr4g ) ADBFDCFBDFCDFABCDEGBDHCDHI $.
      $( [5-Aug-1993] $)

  $}

  $( Theorem *4.37 of [WhiteheadRussell] p. 118. $)
  orbi1 $p |-  ( ( ph <-> ps ) -> ( ( ph \/ ch ) <-> ( ps \/ ch ) ) ) $=
    ( wb id orbi1d ) ABDZABCGEF $.
    $( [12-Jun-2005] $) $( [3-Jan-2005] $)

  $( Theorem *4.36 of [WhiteheadRussell] p. 118. $)
  anbi1 $p |-  ( ( ph <-> ps ) -> ( ( ph /\ ch ) <-> ( ps /\ ch ) ) ) $=
    ( wb id anbi1d ) ABDZABCGEF $.
    $( [15-Jun-2005] $) $( [3-Jan-2005] $)

  $( Theorem *4.22 of [WhiteheadRussell] p. 117. $)
  bitr $p |-  ( ( ( ph <-> ps ) /\ ( ps <-> ch ) ) -> ( ph <-> ch ) ) $=
    ( wb id bibi1d biimpar ) ABDZACDBCDHABCHEFG $.
    $( [30-May-2005] $) $( [3-Jan-2005] $)

  $( Theorem *4.84 of [WhiteheadRussell] p. 122. $)
  imbi1 $p |-  ( ( ph <-> ps ) -> ( ( ph -> ch ) <-> ( ps -> ch ) ) ) $=
    ( wb id imbi1d ) ABDZABCGEF $.
    $( [9-Jan-2005] $) $( [3-Jan-2005] $)

  $( Theorem *4.85 of [WhiteheadRussell] p. 122. $)
  imbi2 $p |-  ( ( ph <-> ps ) -> ( ( ch -> ph ) <-> ( ch -> ps ) ) ) $=
    ( wb ax-1 pm5.74d ) ABDZCABGCEF $.
    $( [9-Jan-2005] $) $( [3-Jan-2005] $)

  $( Theorem *4.86 of [WhiteheadRussell] p. 122. $)
  bibi1 $p |-  ( ( ph <-> ps ) -> ( ( ph <-> ch ) <-> ( ps <-> ch ) ) ) $=
    ( wb id bibi1d ) ABDZABCGEF $.
    $( [15-Jun-2005] $) $( [3-Jan-2005] $)

  ${
    bi12d.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    bi12d.2 $e |- ( ph -> ( th <-> ta ) ) $.
    $( Deduction joining two equivalences to form equivalence of
       implications. $)
    imbi12d $p |- ( ph -> ( ( ps -> th ) <-> ( ch -> ta ) ) ) $=
      ( wi imbi1d imbi2d bitrd ) ABDHCDHCEHABCDFIADECGJK $.
      $( [5-Aug-1993] $)

    $( Deduction joining two equivalences to form equivalence of
       disjunctions. $)
    orbi12d $p |- ( ph -> ( ( ps \/ th ) <-> ( ch \/ ta ) ) ) $=
      ( wo orbi1d orbi2d bitrd ) ABDHCDHCEHABCDFIADECGJK $.
      $( [5-Aug-1993] $)

    $( Deduction joining two equivalences to form equivalence of
       conjunctions. $)
    anbi12d $p |- ( ph -> ( ( ps /\ th ) <-> ( ch /\ ta ) ) ) $=
      ( wa anbi1d anbi2d bitrd ) ABDHCDHCEHABCDFIADECGJK $.
      $( [5-Aug-1993] $)

    $( Deduction joining two equivalences to form equivalence of
       biconditionals. $)
    bibi12d $p |- ( ph -> ( ( ps <-> th ) <-> ( ch <-> ta ) ) ) $=
      ( wb bibi1d bibi2d bitrd ) ABDHCDHCEHABCDFIADECGJK $.
      $( [5-Aug-1993] $)

  $}

  $( Theorem *4.39 of [WhiteheadRussell] p. 118. $)
  pm4.39 $p |-  ( ( ( ph <-> ch ) /\ ( ps <-> th ) ) ->
                ( ( ph \/ ps ) <-> ( ch \/ th ) ) ) $=
    ( wb wa pm3.26 pm3.27 orbi12d ) ACEZBDEZFACBDJKGJKHI $.
    $( [30-May-2005] $) $( [3-Jan-2005] $)

  $( Theorem *4.38 of [WhiteheadRussell] p. 118. $)
  pm4.38 $p |-  ( ( ( ph <-> ch ) /\ ( ps <-> th ) ) ->
                ( ( ph /\ ps ) <-> ( ch /\ th ) ) ) $=
    ( wb wa pm3.26 pm3.27 anbi12d ) ACEZBDEZFACBDJKGJKHI $.
    $( [30-May-2005] $) $( [3-Jan-2005] $)

  ${
    $v et $. $( Greek eta $)
    bi2an9.wet $f wff et $.
    bi2an9.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    bi2an9.2 $e |- ( th -> ( ta <-> et ) ) $.

    $( Deduction joining two equivalences to form equivalence of
       conjunctions. $)
    bi2anan9 $p |- ( ( ph /\ th ) -> ( ( ps /\ ta ) <-> ( ch /\ et ) ) ) $=
      ( wa anbi1d anbi2d sylan9bb ) ABEICEIDCFIABCEGJDEFCHKL $.
      $( [31-Jul-1995] $)

    $( Deduction joining two equivalences to form equivalence of
       conjunctions. $)
    bi2anan9r $p |- ( ( th /\ ph ) -> ( ( ps /\ ta ) <-> ( ch /\ et ) ) ) $=
      ( wa wb bi2anan9 ancoms ) ADBEICFIJABCDEFGHKL $.
      $( [19-Feb-1996] $)

    $( Deduction joining two biconditionals with different antecedents. $)
    bi2bian9 $p |- ( ( ph /\ th ) -> ( ( ps <-> ta ) <-> ( ch <-> et ) ) ) $=
      ( wa wb adantr adantl bibi12d ) ADIBCEFABCJDGKDEFJAHLM $.
      $( [14-May-2004] $) $( [12-May-2004] $)
  $}

  $( Implication in terms of biconditional and conjunction.  Theorem *4.71 of
     [WhiteheadRussell] p. 120. $)
  pm4.71 $p |- ( ( ph -> ps ) <-> ( ph <-> ( ph /\ ps ) ) ) $=
    ( wi wa wb ancl pm3.26 impbid1 bi1 pm3.27 syl6 impbii ) ABCZAABDZEZMANABFAB
    GHOANBANIABJKL $.
    $( [5-Aug-1993] $)

  $( Implication in terms of biconditional and conjunction.  Theorem *4.71 of
     [WhiteheadRussell] p. 120 (with conjunct reversed). $)
  pm4.71r $p |- ( ( ph -> ps ) <-> ( ph <-> ( ps /\ ph ) ) ) $=
    ( wi wa wb pm4.71 ancom bibi2i bitri ) ABCAABDZEABADZEABFJKAABGHI $.
    $( [25-Jul-1999] $)

  ${
    pm4.71i.1 $e |- ( ph -> ps ) $.
    $( Inference converting an implication to a biconditional with conjunction.
       Inference from Theorem *4.71 of [WhiteheadRussell] p. 120. $)
    pm4.71i $p |- ( ph <-> ( ph /\ ps ) ) $=
      ( wi wa wb pm4.71 mpbi ) ABDAABEFCABGH $.
      $( [6-Jan-2004] $) $( [4-Jan-2004] $)
  $}

  ${
    pm4.71ri.1 $e |- ( ph -> ps ) $.
    $( Inference converting an implication to a biconditional with conjunction.
       Inference from Theorem *4.71 of [WhiteheadRussell] p. 120 (with
       conjunct reversed). $)
    pm4.71ri $p |- ( ph <-> ( ps /\ ph ) ) $=
      ( wi wa wb pm4.71r mpbi ) ABDABAEFCABGH $.
      $( [1-Dec-2003] $) $( [1-Dec-2003] $)
  $}

  ${
    pm4.71rd.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction converting an implication to a biconditional with conjunction.
       Deduction from Theorem *4.71 of [WhiteheadRussell] p. 120. $)
    pm4.71rd $p |- ( ph -> ( ps <-> ( ch /\ ps ) ) ) $=
      ( wi wa wb pm4.71r sylib ) ABCEBCBFGDBCHI $.
      $( [12-Feb-2005] $) $( [10-Feb-2005] $)
  $}

  $( Theorem *4.45 of [WhiteheadRussell] p. 119. $)
  pm4.45 $p |-  ( ph <-> ( ph /\ ( ph \/ ps ) ) ) $=
    ( wo orc pm4.71i ) AABCABDE $.
    $( [30-May-2005] $) $( [3-Jan-2005] $)

  $( Implication in terms of biconditional and disjunction.  Theorem *4.72 of
     [WhiteheadRussell] p. 121. $)
  pm4.72 $p |- ( ( ph -> ps ) <-> ( ps <-> ( ph \/ ps ) ) ) $=
    ( wi wo wb olc pm2.621 impbid2 bi2 pm2.67 syl impbii ) ABCZBABDZEZMBNBAFABG
    HONBCMBNIABJKL $.
    $( [30-Aug-1993] $)

  $( Introduction of antecedent as conjunct.  Theorem *4.73 of
     [WhiteheadRussell] p. 121. $)
  iba $p |- ( ph -> ( ps <-> ( ps /\ ph ) ) ) $=
    ( wa ancrb pm5.74ri ) ABBACABDE $.
    $( [30-Mar-1994] $)

  $( Introduction of antecedent as conjunct. $)
  ibar $p |- ( ph -> ( ps <-> ( ph /\ ps ) ) ) $=
    ( wa anclb pm5.74ri ) ABABCABDE $.
    $( [5-Dec-1995] $)

  $( Distribution of implication over biconditional.  Theorem *5.32 of
     [WhiteheadRussell] p. 125. $)
  pm5.32 $p |- ( ( ph -> ( ps <-> ch ) ) <->
               ( ( ph /\ ps ) <-> ( ph /\ ch ) ) ) $=
    ( wb wi wn wa notbi imbi2i pm5.74 3bitri df-an bibi12i bitr4i ) ABCDZEZABFZ
    EZFZACFZEZFZDZABGZACGZDPAQTDZERUADUCOUFABCHIAQTJRUAHKUDSUEUBABLACLMN $.
    $( [1-Aug-1994] $)

  ${
    pm5.32i.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Distribution of implication over biconditional (inference rule). $)
    pm5.32i $p |- ( ( ph /\ ps ) <-> ( ph /\ ch ) ) $=
      ( wb wi wa pm5.32 mpbi ) ABCEFABGACGEDABCHI $.
      $( [1-Aug-1994] $)

    $( Distribution of implication over biconditional (inference rule). $)
    pm5.32ri $p |- ( ( ps /\ ph ) <-> ( ch /\ ph ) ) $=
      ( wa pm5.32i ancom 3bitr4i ) ABEACEBAECAEABCDFBAGCAGH $.
      $( [12-Mar-1995] $)
  $}

  ${
    pm5.32d.1 $e |- ( ph -> ( ps -> ( ch <-> th ) ) ) $.
    $( Distribution of implication over biconditional (deduction rule). $)
    pm5.32d $p |- ( ph -> ( ( ps /\ ch ) <-> ( ps /\ th ) ) ) $=
      ( wb wi wa pm5.32 sylib ) ABCDFGBCHBDHFEBCDIJ $.
      $( [29-Oct-1996] $)

    $( Distribution of implication over biconditional (deduction rule). $)
    pm5.32rd $p |- ( ph -> ( ( ch /\ ps ) <-> ( th /\ ps ) ) ) $=
      ( wa pm5.32d ancom 3bitr4g ) ABCFBDFCBFDBFABCDEGCBHDBHI $.
      $( [1-Jan-2005] $) $( [25-Dec-2004] $)
  $}

  ${
    pm5.32da.1 $e |- ( ( ph /\ ps ) -> ( ch <-> th ) ) $.
    $( Distribution of implication over biconditional (deduction rule). $)
    pm5.32da $p |- ( ph -> ( ( ps /\ ch ) <-> ( ps /\ th ) ) ) $=
      ( wb ex pm5.32d ) ABCDABCDFEGH $.
      $( [10-Dec-2006] $) $( [9-Dec-2006] $)
  $}

  $( Theorem *5.33 of [WhiteheadRussell] p. 125. $)
  pm5.33 $p |-  ( ( ph /\ ( ps -> ch ) ) <->
                ( ph /\ ( ( ph /\ ps ) -> ch ) ) ) $=
    ( wi wa ibar imbi1d pm5.32i ) ABCDABEZCDABICABFGH $.
    $( [31-May-2005] $) $( [3-Jan-2005] $)

  $( Theorem *5.36 of [WhiteheadRussell] p. 125. $)
  pm5.36 $p |-  ( ( ph /\ ( ph <-> ps ) ) <-> ( ps /\ ( ph <-> ps ) ) ) $=
    ( wb id pm5.32ri ) ABCZABFDE $.
    $( [31-May-2005] $) $( [3-Jan-2005] $)

  $( Theorem *5.42 of [WhiteheadRussell] p. 125. $)
  pm5.42 $p |-  ( ( ph -> ( ps -> ch ) ) <->
                ( ph -> ( ps -> ( ph /\ ch ) ) ) ) $=
    ( wi wa ibar imbi2d pm5.74i ) ABCDBACEZDACIBACFGH $.
    $( [3-Jun-2005] $) $( [3-Jan-2005] $)

  ${
    bianabs.1 $e |- ( ph -> ( ps <-> ( ph /\ ch ) ) ) $.
    $( Absorb a hypothesis into the second member of a biconditional.
       (Contributed by FL, 15-Feb-2007.) $)
    bianabs $p |- ( ph -> ( ps <-> ch ) ) $=
      ( wa ibar bitr4d ) ABACECDACFG $.
      $( [22-May-2008] $) $( [15-Feb-2007] $)
  $}

  $( Absorption of disjunction into equivalence. $)
  oibabs $p |- ( ( ( ph \/ ps ) -> ( ph <-> ps ) ) <-> ( ph <-> ps ) ) $=
    ( wo wb wi orc imim1i ibd olc ibibr sylibr impbid ax-1 impbii ) ABCZABDZEZP
    QABQABAOPABFGHQBPEBAEBOPBAIGBAJKLPOMN $.
    $( [29-Jan-2008] $)  $( [6-Aug-1995] $)

  $( Law of excluded middle, also called the principle of _tertium non datur_.
     Theorem *2.11 of [WhiteheadRussell] p. 101.  It says that something is
     either true or not true; there are no in-between values of truth.  This is
     an essential distinction of our classical logic and is not a theorem of
     intuitionistic logic. $)
  exmid $p |- ( ph \/ -. ph ) $=
    ( wn id orri ) AABZECD $.
    $( [5-Aug-1993] $)

  $( Theorem *2.1 of [WhiteheadRussell] p. 101. $)
  pm2.1 $p |-  ( -. ph \/ ph ) $=
    ( wn notnot2 orri ) ABAACD $.
    $( [7-Jan-2005] $) $( [3-Jan-2005] $)

  $( Theorem *2.13 of [WhiteheadRussell] p. 101. $)
  pm2.13 $p |-  ( ph \/ -. -. -. ph ) $=
    ( wn notnot1 orri ) AABZBBECD $.
    $( [4-Jun-2005] $) $( [3-Jan-2005] $)

  $( Law of noncontradiction.  Theorem *3.24 of [WhiteheadRussell] p. 111
     (who call it the "law of contradiction"). $)
  pm3.24 $p |- -. ( ph /\ -. ph ) $=
    ( wn wa wo exmid ianor mpbir ) AABZCBHHBDHEAHFG $.
    $( [16-Sep-1993] $)

  $( Theorem *2.26 of [WhiteheadRussell] p. 104. $)
  pm2.26 $p |-  ( -. ph \/ ( ( ph -> ps ) -> ps ) ) $=
    ( wn wi notnot2 imim1i com12 orri ) ACZABDZBDJICZBKABAEFGH $.
    $( [5-Jun-2005] $) $( [3-Jan-2005] $)

  $( Theorem *5.18 of [WhiteheadRussell] p. 124.  This theorem says that
     logical equivalence is the same as negated "exclusive-or." $)
  pm5.18 $p |- ( ( ph <-> ps ) <-> -. ( ph <-> -. ps ) ) $=
    ( wb wn bicom wi wa pm2.61 pm2.65 con2 syl5 anim12d dfbi2 syl5ib annim 
    syl6ib com12 imnan sylib notbii sylibr wo pm2.5 pm2.21 adantl sylbir jca 
    ax-1 adantr pm2.51 jaoi ianor 3imtr4i sylbi impbii bitri con2bii ) ABCBACZA
    BDZCZDABEUTURUTUSACZURDZAUSEVAVBVABAFZABFZGZDZVBVAVCVDDZFVFVCVAVGVCVAAUSGZV
    GVCUSAFZAUSFZGZVHVAVCVIAVJUSBAHVCBADZFUSVJBAIABJKLUSAMZNABOZPQVCVDRSURVEBAM
    TZUAVBVFVAVOVCDZVGUBVKVFVAVPVKVGVPVIVJBAUCVPBVLGVJBAOVLVJBAUSUDUEUFUGVGVIVJ
    VGVHVIVNAVIUSAUSUHUIUFABUJUGUKVCVDULVMUMUNUOUPUQUP $.
    $( [28-Jun-2002] $)

  $( Move negation outside of biconditional.  Compare Theorem *5.18 of
     [WhiteheadRussell] p. 124. $)
  nbbn $p |- ( ( -. ph <-> ps ) <-> -. ( ph <-> ps ) ) $=
    ( wn wb bicom pm5.18 bitri con2bii ) ACZBDBIDZABDZCIBEKJKBADJCABEBAFGHG $.
    $( [27-Jun-2002] $)

  $( Theorem *5.11 of [WhiteheadRussell] p. 123. $)
  pm5.11 $p |-  ( ( ph -> ps ) \/ ( -. ph -> ps ) ) $=
    ( wi wn pm2.5 orri ) ABCADBCABEF $.
    $( [17-Jun-2005] $) $( [3-Jan-2005] $)

  $( Theorem *5.12 of [WhiteheadRussell] p. 123. $)
  pm5.12 $p |-  ( ( ph -> ps ) \/ ( ph -> -. ps ) ) $=
    ( wi wn pm2.51 orri ) ABCABDCABEF $.
    $( [17-Jun-2005] $) $( [3-Jan-2005] $)

  $( Theorem *5.13 of [WhiteheadRussell] p. 123. $)
  pm5.13 $p |-  ( ( ph -> ps ) \/ ( ps -> ph ) ) $=
    ( wi pm2.521 orri ) ABCBACABDE $.
    $( [7-Jun-2005] $) $( [3-Jan-2005] $)

  $( Theorem *5.14 of [WhiteheadRussell] p. 123. $)
  pm5.14 $p |-  ( ( ph -> ps ) \/ ( ps -> ch ) ) $=
    ( wi wn ax-1 con3i pm2.21d orri ) ABDZBCDJEBCBJBAFGHI $.
    $( [17-Jun-2005] $) $( [3-Jan-2005] $)

  $( Theorem *5.15 of [WhiteheadRussell] p. 124. $)
  pm5.15 $p |-  ( ( ph <-> ps ) \/ ( ph <-> -. ps ) ) $=
    ( wb wn pm5.18 biimpri con1i orri ) ABCZABDCZJIIJDABEFGH $.
    $( [1-Feb-2005] $) $( [3-Jan-2005] $)

  $( Theorem *5.16 of [WhiteheadRussell] p. 124. $)
  pm5.16 $p |-  -. ( ( ph <-> ps ) /\ ( ph <-> -. ps ) ) $=
    ( wb wn wa wo wi pm5.18 biimpi pm4.62 mpbi ianor mpbir ) ABCZABDCZEDNDODZFZ
    NPGQNPABHINOJKNOLM $.
    $( [17-Jun-2005] $) $( [3-Jan-2005] $)

  $( Theorem *5.17 of [WhiteheadRussell] p. 124. $)
  pm5.17 $p |-  ( ( ( ph \/ ps ) /\ -. ( ph /\ ps ) ) <-> ( ph <-> -. ps ) ) $=
    ( wo wa wn wi wb orcom df-or bitri imnan bicomi anbi12i dfbi2 bicom 
    3bitr2i ) ABCZABDEZDBEZAFZASFZDSAGASGQTRUAQBACTABHBAIJUARABKLMSANSAOP $.
    $( [22-Mar-2005] $) $( [3-Jan-2005] $)

  $( Theorem *5.19 of [WhiteheadRussell] p. 124. $)
  pm5.19 $p |-  -. ( ph <-> -. ph ) $=
    ( wb wn biid pm5.18 mpbi ) AABAACBCADAAEF $.
    $( [1-Feb-2005] $) $( [3-Jan-2005] $)

  $( An alternate definition of the biconditional.  Theorem *5.23 of
     [WhiteheadRussell] p. 124. $)
  dfbi3 $p |- ( ( ph <-> ps ) <-> ( ( ph /\ ps ) \/ ( -. ph /\ -. ps ) ) ) $=
    ( wb wn wa wo pm5.18 wi imnan con1b iman bitri anbi12i dfbi2 ioran 
    3bitr4ri con1bii ) ABCABDZCZDABEZADZREZFZABGUCSARHZRAHZETDZUBDZESUCDUDUFUEU
    GABIUEUABHUGBAJUABKLMARNTUBOPQL $.
    $( [27-Jun-2002] $)

  $( Two ways to express "exclusive or."  Theorem *5.22 of [WhiteheadRussell]
     p. 124. $)
  xor $p |-  ( -. ( ph <-> ps ) <->
                ( ( ph /\ -. ps ) \/ ( ps /\ -. ph ) ) ) $=
    ( wn wb wa wo dfbi3 nbbn ancom notnot anbi1i orbi12i orcom bitr3i 3bitr3i 
    ) ACZBDPBEZPCZBCZEZFZABDCASEZBPEZFZPBGABHUAUCUBFUDUCQUBTBPIARSAJKLUCUBMNO 
    $.
    $( [11-Jan-2005] $) $( [3-Jan-2005] $)

  $( Theorem *5.24 of [WhiteheadRussell] p. 124. $)
  pm5.24 $p |-  ( -. ( ( ph /\ ps ) \/ ( -. ph /\ -. ps ) ) <->
                ( ( ph /\ -. ps ) \/ ( ps /\ -. ph ) ) ) $=
    ( wa wn wo wb dfbi3 notbii xor bitr3i ) ABCADZBDZCEZDABFZDALCBKCENMABGHABIJ
    $.
    $( [11-Feb-2005] $) $( [3-Jan-2005] $)

  $( Two ways to express "exclusive or." $)
  xor2 $p |-  ( -. ( ph <-> ps ) <-> ( ( ph \/ ps ) /\ -. ( ph /\ ps ) ) ) $=
    ( wb wn wa wo xor ioran pm5.24 oran anbi2i ancom bitr3i 3bitr3i bitri ) ABC
    DABDZEBADZEFZABFZABEZDZEZABGTQPEZFDUAUCDZEZRUBTUCHABIUEUASEUBSUDUAABJKUASLM
    NO $.
    $( [11-Feb-2005] $) $( [3-Jan-2005] $)

  $( Two ways to express "exclusive or." $)
  xor3 $p |-  ( -. ( ph <-> ps ) <-> ( ph <-> -. ps ) ) $=
    ( wn wb pm5.18 con2bii bicomi ) ABCDZABDZCIHABEFG $.
    $( [4-Jan-2006] $) $( [1-Jan-2006] $)

  $( Conjunction distributes over exclusive-or, using ` -. ( ph <-> ps ) `
     to express exclusive-or.  This is one way to interpret the distributive
     law of multiplication over addition in modulo 2 arithmetic. $)
  xordi $p |- ( ( ph /\ -. ( ps <-> ch ) ) <->
                -. ( ( ph /\ ps ) <-> ( ph /\ ch ) ) ) $=
    ( wb wn wa wi annim pm5.32 notbii bitri ) ABCDZEFALGZEABFACFDZEALHMNABCIJK 
    $.
    $( [3-Oct-2008] $) $( [3-Oct-2008] $)

  $( Theorem *5.55 of [WhiteheadRussell] p. 125. $)
  pm5.55 $p |-  ( ( ( ph \/ ps ) <-> ph ) \/ ( ( ph \/ ps ) <-> ps ) ) $=
    ( wi wo wb pm5.13 pm4.72 orcom bibi2i bicom 3bitri bitri orbi12i mpbi ) BAC
    ZABCZDABDZAEZQBEZDBAFORPSOABADZEAQERBAGTQABAHIAQJKPBQESABGBQJLMN $.
    $( [7-Jun-2005] $) $( [3-Jan-2005] $)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Miscellaneous theorems of propositional calculus
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Two propositions are equivalent if they are both true.  Theorem *5.1 of
     [WhiteheadRussell] p. 123. $)
  pm5.1 $p |- ( ( ph /\ ps ) -> ( ph <-> ps ) ) $=
    ( wb pm5.501 biimpa ) ABABCABDE $.
    $( [21-May-1994] $)

  $( Two propositions are equivalent if they are both false.  Theorem *5.21 of
     [WhiteheadRussell] p. 124. $)
  pm5.21 $p |- ( ( -. ph /\ -. ps ) -> ( ph <-> ps ) ) $=
    ( wn wa pm5.1 con4bid ) ACZBCZDABGHEF $.
    $( [21-May-1994] $)


  ${
    pm5.21ni.1 $e |- ( ph -> ps ) $.
    pm5.21ni.2 $e |- ( ch -> ps ) $.
    $( Two propositions implying a false one are equivalent. $)
    pm5.21ni $p |- ( -. ps -> ( ph <-> ch ) ) $=
      ( wn wb pm5.21 con3i sylanc ) AFCFACGBFACHABDICBEIJ $.
      $( [16-Feb-1996] $)

    ${
      pm5.21nii.3 $e |- ( ps -> ( ph <-> ch ) ) $.
      $( Eliminate an antecedent implied by each side of a biconditional. $)
      pm5.21nii $p |- ( ph <-> ch ) $=
        ( wb pm5.21ni pm2.61i ) BACGFABCDEHI $.
        $( [21-May-1999] $)
    $}
  $}

  ${
    pm5.21nd.1 $e |- ( ( ph /\ ps ) -> th ) $.
    pm5.21nd.2 $e |- ( ( ph /\ ch ) -> th ) $.
    pm5.21nd.3 $e |- ( th -> ( ps <-> ch ) ) $.
    $( Eliminate an antecedent implied by each side of a biconditional. $)
    pm5.21nd $p |- ( ph -> ( ps <-> ch ) ) $=
      ( wb wn wa ex con3d jcad pm5.21 syl6 pm2.61d2 ) ADBCHZADIZBIZCIZJQARSTABD
      ABDEKLACDACDFKLMBCNOGP $.
      $( [23-Nov-2005] $) $( [20-Nov-2005] $)
  $}

  $( Transfer negation via an equivalence. $)
  bibif $p |- ( -. ps -> ( ( ph <-> ps ) <-> -. ph ) ) $=
    ( wn wb bi1 con3d com12 pm5.21 expcom impbid ) BCZABDZACZLKMLABABEFGMKLABHI
    J $.
    $( [7-Nov-2007] $) $( [3-Oct-2007] $)

  $( Theorem *5.35 of [WhiteheadRussell] p. 125. $)
  pm5.35 $p |-  ( ( ( ph -> ps ) /\ ( ph -> ch ) ) ->
                ( ph -> ( ps <-> ch ) ) ) $=
    ( wi wa pm5.1 pm5.74rd ) ABDZACDZEABCHIFG $.
    $( [28-Jun-2005] $) $( [3-Jan-2005] $)

  $( Theorem *5.54 of [WhiteheadRussell] p. 125. $)
  pm5.54 $p |-  ( ( ( ph /\ ps ) <-> ph ) \/ ( ( ph /\ ps ) <-> ps ) ) $=
    ( wa wb pm5.1 anabss1 iba bicomd pm5.21ni orri ) ABCZADZKBDKLBABLKAEFBAKBAG
    HIJ $.
    $( [28-Jun-2005] $) $( [3-Jan-2005] $)

  $( Elimination of antecedents in an implication. (The proof was shortened by
     Juha Arpiainen, 19-Jan-2006.) $)
  elimant $p |- ( ( ( ph -> ps ) /\ ( ( ps -> ch ) -> ( ph -> th ) ) ) ->
                ( ph -> ( ch -> th ) ) ) $=
    ( wi wa pm3.27 ax-1 syl5 com23 ) ABEZBCEZADEZEZFZCADOLMCKNGCBHIJ $.
    $( [21-Jan-2006] $) $( [13-Oct-1999] $)

  ${
    baib.1 $e |- ( ph <-> ( ps /\ ch ) ) $.
    $( Move conjunction outside of biconditional. $)
    baib $p |- ( ps -> ( ph <-> ch ) ) $=
      ( wa ibar syl6rbbr ) BCBCEABCFDG $.
      $( [13-May-1999] $)
  $}

  ${
    baibr.1 $e |- ( ph <-> ( ps /\ ch ) ) $.
    $( Move conjunction outside of biconditional. $)
    baibr $p |- ( ps -> ( ch <-> ph ) ) $=
      ( baib bicomd ) BACABCDEF $.
      $( [11-Jul-1994] $)
  $}

  $( Theorem *5.44 of [WhiteheadRussell] p. 125. $)
  pm5.44 $p |-  ( ( ph -> ps ) -> ( ( ph -> ch ) <->
                ( ph -> ( ps /\ ch ) ) ) ) $=
    ( wa wi jcab baibr ) ABCDEABEACEABCFG $.
    $( [28-Jun-2005] $) $( [3-Jan-2005] $)

  $( Conjunction in antecedent versus disjunction in consequent.  Theorem *5.6
     of [WhiteheadRussell] p. 125. $)
  pm5.6 $p |-  ( ( ( ph /\ -. ps ) -> ch ) <-> ( ph -> ( ps \/ ch ) ) ) $=
    ( wn wa wi wo impexp df-or imbi2i bitr4i ) ABDZECFALCFZFABCGZFALCHNMABCIJK 
    $.
    $( [22-Mar-2005] $) $( [8-Jun-1994] $)

  $( Theorem to move a conjunct in and out of a negation. $)
  nan $p |- ( ( ph -> -. ( ps /\ ch ) ) <-> ( ( ph /\ ps ) -> -. ch ) ) $=
    ( wa wn wi impexp imnan imbi2i bitr2i ) ABDCEZFABKFZFABCDEZFABKGLMABCHIJ $.
    $( [9-Nov-2003] $) $( [9-Nov-2003] $)

  ${
    orcanai.1 $e |- ( ph -> ( ps \/ ch ) ) $.
    $( Change disjunction in consequent to conjunction in antecedent. $)
    orcanai $p |- ( ( ph /\ -. ps ) -> ch ) $=
      ( wn ord imp ) ABECABCDFG $.
      $( [8-Jun-1994] $)
  $}


  ${
    intnan.1 $e |- -. ph $.
    $( Introduction of conjunct inside of a contradiction. $)
    intnan $p |- -. ( ps /\ ph ) $=
      ( wa pm3.27 mto ) BADACBAEF $.
      $( [16-Sep-1993] $)

    $( Introduction of conjunct inside of a contradiction. $)
    intnanr $p |- -. ( ph /\ ps ) $=
      ( wa pm3.26 mto ) ABDACABEF $.
      $( [3-Apr-1995] $)
  $}

  ${
    intnand.1 $e |- ( ph -> -. ps ) $.
    $( Introduction of conjunct inside of a contradiction. $)
    intnand $p |- ( ph -> -. ( ch /\ ps ) ) $=
      ( wa pm3.27 nsyl ) ABCBEDCBFG $.
      $( [12-Jul-2005] $) $( [10-Jul-2005] $)

    $( Introduction of conjunct inside of a contradiction. $)
    intnanrd $p |- ( ph -> -. ( ps /\ ch ) ) $=
      ( wa pm3.26 nsyl ) ABBCEDBCFG $.
      $( [12-Jul-2005] $) $( [10-Jul-2005] $)
  $}

  ${
    mpan.1 $e |- ph $.
    mpan.2 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( An inference based on modus ponens. $)
    mpan $p |- ( ps -> ch ) $=
      ( wi ex ax-mp ) ABCFDABCEGH $.
      $( [30-Aug-1993] $)
  $}

  ${
    mpan2.1 $e |- ps $.
    mpan2.2 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( An inference based on modus ponens. $)
    mpan2 $p |- ( ph -> ch ) $=
      ( ex mpi ) ABCDABCEFG $.
      $( [16-Sep-1993] $)
  $}

  ${
    mp2an.1 $e |- ph $.
    mp2an.2 $e |- ps $.
    mp2an.3 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( An inference based on modus ponens. $)
    mp2an $p |- ch $=
      ( mpan ax-mp ) BCEABCDFGH $.
      $( [13-Apr-1995] $)
  $}

  ${
    mpani.1 $e |- ps $.
    mpani.2 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
    $( An inference based on modus ponens. $)
    mpani $p |- ( ph -> ( ch -> th ) ) $=
      ( wi exp3a mpi ) ABCDGEABCDFHI $.
      $( [10-Apr-1994] $)
  $}

  ${
    mpan2i.1 $e |- ch $.
    mpan2i.2 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
    $( An inference based on modus ponens. $)
    mpan2i $p |- ( ph -> ( ps -> th ) ) $=
      ( exp3a mpii ) ABCDEABCDFGH $.
      $( [10-Apr-1994] $)
  $}

  ${
    mp2ani.1 $e |- ps $.
    mp2ani.2 $e |- ch $.
    mp2ani.3 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
    $( An inference based on modus ponens. $)
    mp2ani $p |- ( ph -> th ) $=
      ( mpani mpi ) ACDFABCDEGHI $.
      $( [13-Dec-2004] $) $( [12-Dec-2004] $)
  $}

  ${
    mpand.1 $e |- ( ph -> ps ) $.
    mpand.2 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
    $( A deduction based on modus ponens. $)
    mpand $p |- ( ph -> ( ch -> th ) ) $=
      ( wi exp3a mpd ) ABCDGEABCDFHI $.
      $( [13-Dec-2004] $) $( [12-Dec-2004] $)
  $}

  ${
    mpan2d.1 $e |- ( ph -> ch ) $.
    mpan2d.2 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
    $( A deduction based on modus ponens. $)
    mpan2d $p |- ( ph -> ( ps -> th ) ) $=
      ( exp3a mpid ) ABCDEABCDFGH $.
      $( [13-Dec-2004] $) $( [12-Dec-2004] $)
  $}

  ${
    mp2and.1 $e |- ( ph -> ps ) $.
    mp2and.2 $e |- ( ph -> ch ) $.
    mp2and.3 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
    $( A deduction based on modus ponens. $)
    mp2and $p |- ( ph -> th ) $=
      ( mpand mpd ) ACDFABCDEGHI $.
      $( [13-Dec-2004] $) $( [12-Dec-2004] $)
  $}

  ${
    mpdan.1 $e |- ( ph -> ps ) $.
    mpdan.2 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( An inference based on modus ponens. $)
    mpdan $p |- ( ph -> ch ) $=
      ( ex mpd ) ABCDABCEFG $.
      $( [23-May-1999] $)
  $}

  ${
    mpancom.1 $e |- ( ps -> ph ) $.
    mpancom.2 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( An inference based on modus ponens with commutation of antecedents. $)
    mpancom $p |- ( ps -> ch ) $=
      ( ancoms mpdan ) BACDABCEFG $.
      $( [13-Mar-2004] $) $( [28-Oct-2003] $)
  $}

  ${
    mpanl1.1 $e |- ph $.
    mpanl1.2 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
    $( An inference based on modus ponens. $)
    mpanl1 $p |- ( ( ps /\ ch ) -> th ) $=
      ( wi wa ex mpan imp ) BCDABCDGEABHCDFIJK $.
      $( [16-Aug-1994] $)
  $}

  ${
    mpanl2.1 $e |- ps $.
    mpanl2.2 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
    $( An inference based on modus ponens. $)
    mpanl2 $p |- ( ( ph /\ ch ) -> th ) $=
      ( wi wa ex mpan2 imp ) ACDABCDGEABHCDFIJK $.
      $( [16-Aug-1994] $)
  $}

  ${
    mpanl12.1 $e |- ph $.
    mpanl12.2 $e |- ps $.
    mpanl12.3 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
    $( An inference based on modus ponens. $)
    mpanl12 $p |- ( ch -> th ) $=
      ( mpanl1 mpan ) BCDFABCDEGHI $.
      $( [15-Jul-2005] $) $( [13-Jul-2005] $)
  $}

  ${
    mpanr1.1 $e |- ps $.
    mpanr1.2 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
    $( An inference based on modus ponens. $)
    mpanr1 $p |- ( ( ph /\ ch ) -> th ) $=
      ( wa ex mpani imp ) ACDABCDEABCGDFHIJ $.
      $( [3-May-1994] $)
  $}

  ${
    mpanr2.1 $e |- ch $.
    mpanr2.2 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
    $( An inference based on modus ponens. $)
    mpanr2 $p |- ( ( ph /\ ps ) -> th ) $=
      ( wa ex mpan2i imp ) ABDABCDEABCGDFHIJ $.
      $( [3-May-1994] $)
  $}

  ${
    mpanr12.1 $e |- ps $.
    mpanr12.2 $e |- ch $.
    mpanr12.3 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
    $( An inference based on modus ponens. $)
    mpanr12 $p |- ( ph -> th ) $=
      ( mpanr1 mpan2 ) ACDFABCDEGHI $.
      $( [26-Jul-2009] $) $( [24-Jul-2009] $)
  $}

  ${
    mpanlr1.1 $e |- ps $.
    mpanlr1.2 $e |- ( ( ( ph /\ ( ps /\ ch ) ) /\ th ) -> ta ) $.
    $( An inference based on modus ponens. $)
    mpanlr1 $p |- ( ( ( ph /\ ch ) /\ th ) -> ta ) $=
      ( wa wi ex mpanr1 imp ) ACHDEABCDEIFABCHHDEGJKL $.
      $( [7-Jan-2005] $) $( [30-Dec-2004] $)
  $}

  $( Modus-tollens-like theorem. $)
  mtt $p |- ( -. ph -> ( -. ps <-> ( ps -> ph ) ) ) $=
    ( wn wi pm2.21 con3 com12 impbid2 ) ACZBCZBADZBAEKIJBAFGH $.
    $( [7-Apr-2001] $)

  ${
    mt2bi.1 $e |- ph $.
    $( A false consequent falsifies an antecedent. $)
    mt2bi $p |- ( -. ps <-> ( ps -> -. ph ) ) $=
      ( wn wi pm2.21 con2 mpi impbii ) BDZBADZEZBKFLAJCBAGHI $.
      $( [19-Aug-1993] $)
  $}

  ${
    mtbid.min $e |- ( ph -> -. ps ) $.
    mtbid.maj $e |- ( ph -> ( ps <-> ch ) ) $.
    $( A deduction from a biconditional, similar to modus tollens. $)
    mtbid $p |- ( ph -> -. ch ) $=
      ( biimprd mtod ) ACBDABCEFG $.
      $( [26-Nov-1995] $)
  $}

  ${
    mtbird.min $e |- ( ph -> -. ch ) $.
    mtbird.maj $e |- ( ph -> ( ps <-> ch ) ) $.
    $( A deduction from a biconditional, similar to modus tollens. $)
    mtbird $p |- ( ph -> -. ps ) $=
      ( biimpd mtod ) ABCDABCEFG $.
      $( [10-May-1994] $)
  $}

  ${
    mtbii.min $e |- -. ps $.
    mtbii.maj $e |- ( ph -> ( ps <-> ch ) ) $.
    $( An inference from a biconditional, similar to modus tollens. $)
    mtbii $p |- ( ph -> -. ch ) $=
      ( biimprd mtoi ) ACBDABCEFG $.
      $( [27-Nov-1995] $)
  $}

  ${
    mtbiri.min $e |- -. ch $.
    mtbiri.maj $e |- ( ph -> ( ps <-> ch ) ) $.
    $( An inference from a biconditional, similar to modus tollens. $)
    mtbiri $p |- ( ph -> -. ps ) $=
      ( biimpd mtoi ) ABCDABCEFG $.
      $( [24-Aug-1995] $)
  $}

  ${
    2th.1 $e |- ph $.
    2th.2 $e |- ps $.
    $( Two truths are equivalent. $)
    2th $p |- ( ph <-> ps ) $=
      ( a1i impbii ) ABBADEABCEF $.
      $( [18-Aug-1993] $)
  $}

  ${
    2false.1 $e |- -. ph $.
    2false.2 $e |- -. ps $.
    $( Two falsehoods are equivalent. $)
    2false $p |- ( ph <-> ps ) $=
      ( wn wb pm5.21 mp2an ) AEBEABFCDABGH $.
      $( [5-Apr-2005] $) $( [4-Apr-2005] $)
  $}

  ${
    tbt.1 $e |- ph $.
    $( A wff is equivalent to its equivalence with truth. (The proof was
       shortened by Juha Arpiainen, 19-Jan-2006.) $)
    tbt $p |- ( ps <-> ( ps <-> ph ) ) $=
      ( wb pm5.501 ax-mp bicom bitri ) BABDZBADABIDCABEFABGH $.
      $( [21-Jan-2006] $) $( [18-Aug-1993] $)
  $}

  $( The negation of a wff is equivalent to the wff's equivalence to
     falsehood.  (Contributed by Juha Arpiainen, 19-Jan-2006.) $)
  nbn2 $p |- ( -. ph -> ( -. ps <-> ( ph <-> ps ) ) ) $=
    ( wn wb pm5.21 ex notbi biimpi biimpcd impbid ) ACZBCZABDZKLMABEFMKLMKLDABG
    HIJ $.
    $( [21-Jan-2006] $) $( [19-Jan-2006] $)

  ${
    nbn.1 $e |- -. ph $.
    $( The negation of a wff is equivalent to the wff's equivalence to
       falsehood. $)
    nbn $p |- ( -. ps <-> ( ps <-> ph ) ) $=
      ( wn wb nbn2 ax-mp bicom bitri ) BDZABEZBAEADJKECABFGABHI $.
      $( [5-Aug-1993] $)
  $}

  ${
    nbn3.1 $e |- ph $.
    $( Transfer falsehood via equivalence. $)
    nbn3 $p |- ( -. ps <-> ( ps <-> -. ph ) ) $=
      ( wn notnoti nbn ) ADBACEF $.
      $( [12-Sep-2006] $) $( [11-Sep-2006] $)
  $}

  ${
    biantru.1 $e |- ph $.
    $( A wff is equivalent to its conjunction with truth. $)
    biantru $p |- ( ps <-> ( ps /\ ph ) ) $=
      ( wa wb iba ax-mp ) ABBADECABFG $.
      $( [5-Aug-1993] $)
  $}

  ${
    biantrur.1 $e |- ph $.
    $( A wff is equivalent to its conjunction with truth. $)
    biantrur $p |- ( ps <-> ( ph /\ ps ) ) $=
      ( wa wb ibar ax-mp ) ABABDECABFG $.
      $( [3-Aug-1994] $)
  $}

  ${
    biantrud.1 $e |- ( ph -> ps ) $.
    $( A wff is equivalent to its conjunction with truth. $)
    biantrud $p |- ( ph -> ( ch <-> ( ch /\ ps ) ) ) $=
      ( wa anim2i expcom pm3.26 impbid1 ) ACCBEZCAJABCDFGCBHI $.
      $( [2-Aug-1994] $)

    $( A wff is equivalent to its conjunction with truth. $)
    biantrurd $p |- ( ph -> ( ch <-> ( ps /\ ch ) ) ) $=
      ( wa biantrud ancom syl6bb ) ACCBEBCEABCDFCBGH $.
      $( [1-May-1995] $)
  $}

  ${
    mpbiran.1 $e |- ( ph <-> ( ps /\ ch ) ) $.
    ${
      mpbiran.2 $e |- ps $.
      $( Detach truth from conjunction in biconditional. $)
      mpbiran $p |- ( ph <-> ch ) $=
        ( wa biantrur bitr4i ) ABCFCDBCEGH $.
        $( [27-Feb-1996] $)
    $}

    ${
      mpbiran2.2 $e |- ch $.
      $( Detach truth from conjunction in biconditional. $)
      mpbiran2 $p |- ( ph <-> ps ) $=
        ( wa biantru bitr4i ) ABCFBDCBEGH $.
        $( [22-Feb-1996] $)
    $}

    ${
      mpbir2an.2 $e |- ps $.
      mpbir2an.3 $e |- ch $.
      $( Detach a conjunction of truths in a biconditional. $)
      mpbir2an $p |- ph $=
        ( mpbiran mpbir ) ACFABCDEGH $.
        $( [12-May-2005] $) $( [10-May-2005] $)
    $}
  $}

  $( A wff is equivalent to itself with true antecedent. $)
  biimt $p |- ( ph -> ( ps <-> ( ph -> ps ) ) ) $=
    ( wi ax-1 pm2.27 impbid2 ) ABABCBADABEF $.
    $( [28-Jan-1996] $)

  $( Theorem *5.5 of [WhiteheadRussell] p. 125. $)
  pm5.5 $p |-  ( ph -> ( ( ph -> ps ) <-> ps ) ) $=
    ( wi biimt bicomd ) ABABCABDE $.
    $( [28-Jun-2005] $) $( [3-Jan-2005] $)

  $( Theorem *5.62 of [WhiteheadRussell] p. 125.  (Contributed by Roy F.
     Longton, 21-Jun-2005.) $)
  pm5.62 $p |-  ( ( ( ph /\ ps ) \/ -. ps ) <-> ( ph \/ -. ps ) ) $=
    ( wa wn wo ordir exmid mpbiran2 ) ABCBDZEAIEBIEABIFBGH $.
    $( [22-Jun-2005] $) $( [21-Jun-2005] $)

  $( A wff is disjoined with truth is true. $)
  biort $p |- ( ph -> ( ph <-> ( ph \/ ps ) ) ) $=
    ( wo orc ax-1 impbid2 ) AAABCZABDAGEF $.
    $( [23-May-1999] $)

  $( A wff is equivalent to its disjunction with falsehood.  Theorem *4.74 of
     [WhiteheadRussell] p. 121. $)
  biorf $p |- ( -. ph -> ( ps <-> ( ph \/ ps ) ) ) $=
    ( wn wi wo biimt df-or syl6bbr ) ACZBIBDABEIBFABGH $.
    $( [23-Mar-1995] $)

  ${
    biorfi.1 $e |- -. ph $.
    $( A wff is equivalent to its disjunction with falsehood. $)
    biorfi $p |- ( ps <-> ( ps \/ ph ) ) $=
      ( wo wn wb biorf ax-mp orcom bitri ) BABDZBADAEBKFCABGHABIJ $.
      $( [23-Mar-1995] $)
  $}

  ${
    bianfi.1 $e |- -. ph $.
    $( A wff conjoined with falsehood is false. $)
    bianfi $p |- ( ph <-> ( ps /\ ph ) ) $=
      ( wa pm2.21i pm3.27 impbii ) ABADZAHCEBAFG $.
      $( [5-Aug-1993] $)
  $}

  ${
    bianfd.1 $e |- ( ph -> -. ps ) $.
    $( A wff conjoined with falsehood is false. $)
    bianfd $p |- ( ph -> ( ps <-> ( ps /\ ch ) ) ) $=
      ( wa pm2.21d pm3.26 impbid1 ) ABBCEZABIDFBCGH $.
      $( [27-Mar-1995] $)
  $}

  $( Theorem *4.82 of [WhiteheadRussell] p. 122. $)
  pm4.82 $p |-  ( ( ( ph -> ps ) /\ ( ph -> -. ps ) ) <-> -. ph ) $=
    ( wi wn wa pm2.65 imp pm2.21 jca impbii ) ABCZABDZCZEADZKMNABFGNKMABHALHIJ 
    $.
    $( [28-Jun-2005] $) $( [3-Jan-2005] $)

  $( Theorem *4.83 of [WhiteheadRussell] p. 122. $)
  pm4.83 $p |-  ( ( ( ph -> ps ) /\ ( -. ph -> ps ) ) <-> ps ) $=
    ( wn wo wi wa exmid a1bi jaob bitr2i ) BAACZDZBEABEKBEFLBAGHABKIJ $.
    $( [28-Jun-2005] $) $( [3-Jan-2005] $)

  $( Negation inferred from embedded conjunct. $)
  pclem6 $p |- ( ( ph <-> ( ps /\ -. ph ) ) -> -. ps ) $=
    ( wn wa wb bi1 pm3.27 syl6 pm2.01d wi bi2 exp3a com23 con3 syli mpd ) ABACZ
    DZEZQBCZSASARQARFBQGHIQSBAJTSBQASBQAARKLMBANOP $.
    $( [20-Aug-1993] $)

  $( A transitive law of equivalence.  Compare Theorem *4.22 of
     [WhiteheadRussell] p. 117. $)
  biantr $p |- ( ( ( ph <-> ps ) /\ ( ch <-> ps ) ) -> ( ph <-> ch ) ) $=
    ( wb id bibi2d biimparc ) CBDZACDABDHCBAHEFG $.
    $( [18-Aug-1993] $)


  $( Disjunction distributes over the biconditional.  An axiom of system DS in
     Vladimir Lifschitz, "On calculational proofs" (1998),
     ~ http://citeseer.ist.psu.edu/lifschitz98calculational.html . $)
  orbidi $p |-  ( ( ph \/ ( ps <-> ch ) ) <->
                ( ( ph \/ ps ) <-> ( ph \/ ch ) ) ) $=
    ( wb wo orc a1d impbid id orbi2d jaoi wi wa pm2.85 anim12i dfbi2 orbi2i 
    ordi bitri 3imtr4i impbii ) ABCDZEZABEZACEZDZAUFUBAUDUEAUEUDACFGAUDUEABFGHU
    BBCAUBIJKUDUELZUEUDLZMABCLZEZACBLZEZMZUFUCUGUJUHULABCNACBNOUDUEPUCAUIUKMZEU
    MUBUNABCPQAUIUKRSTUA $.
    $( [9-Jan-2005] $) $( [8-Jan-2005] $)

  $( Associative law for the biconditional.  An axiom of system DS in Vladimir
     Lifschitz, "On calculational proofs" (1998),
     ~ http://citeseer.ist.psu.edu/lifschitz98calculational.html .
     Interestingly, this law was not included in _Principia Mathematica_ but
     was apparently first noted by Jan Lukasiewicz circa 1923.  (The proof was
     shortened by Juha Arpiainen, 19-Jan-2006.) $)
  biass $p |- ( ( ( ph <-> ps ) <-> ch ) <-> ( ph <-> ( ps <-> ch ) ) ) $=
    ( wb pm5.501 bibi1d bitr3d wn nbbn a1i nbn2 3bitr3d pm2.61i ) AABDZCDZABCDZ
    DZDAPOQABNCABEFAPEGAHZBHZCDZPHZOQTUADRBCIJRSNCABKFAPKLM $.
    $( [21-Jan-2006] $) $( [8-Jan-2005] $)

  $( Lukasiewicz's shortest axiom for equivalential calculus.  Storrs McCall,
     ed., _Polish Logic 1920-1939_ (Oxford, 1967), p. 96. $)
  biluk $p |- ( ( ph <-> ps ) <-> ( ( ch <-> ps ) <-> ( ph <-> ch ) ) ) $=
    ( wb bicom bibi1i biass bitri mpbi bitr4i ) ABDZCBACDZDZDZCBDLDKCDZMDKNDOBA
    DZCDMKPCABEFBACGHKCMGICBLGJ $.
    $( [11-Jan-2005] $) $( [10-Jan-2005] $)

  $( Disjunction distributes over the biconditional.  Theorem *5.7 of
     [WhiteheadRussell] p. 125.  This theorem is similar to ~ orbidi .
     (Contributed by Roy F. Longton, 21-Jun-2005.) $)
  pm5.7 $p |-  ( ( ( ph \/ ch ) <-> ( ps \/ ch ) ) <->
               ( ch \/ ( ph <-> ps ) ) ) $=
    ( wb wo orbidi orcom bibi12i bitr2i ) CABDECAEZCBEZDACEZBCEZDCABFJLKMCAGCBG
    HI $.
    $( [22-Jun-2005] $) $( [21-Jun-2005] $)

  $( Dijkstra-Scholten's Golden Rule for calculational proofs. $)
  bigolden $p |- ( ( ( ph /\ ps ) <-> ph ) <-> ( ps <-> ( ph \/ ps ) ) ) $=
    ( wi wa wb wo pm4.71 pm4.72 bicom 3bitr3ri ) ABCAABDZEBABFEKAEABGABHAKIJ $.
    $( [12-Jan-2005] $) $( [10-Jan-2005] $)

  $( Theorem *5.71 of [WhiteheadRussell] p. 125.  (Contributed by Roy F.
     Longton, 23-Jun-2005.) $)
  pm5.71 $p |-  ( ( ps -> -. ch ) -> ( ( ( ph \/ ps ) /\ ch ) <->
                ( ph /\ ch ) ) ) $=
    ( wn wo wa wb orel2 orc impbid1 anbi1d pm2.21 pm5.32rd ja ) BCDZABEZCFACFGB
    DZPACQPABAHABIJKOCPACPAGLMN $.
    $( [24-Jun-2005] $) $( [23-Jun-2005] $)

  $( Theorem *5.75 of [WhiteheadRussell] p. 126. $)
  pm5.75 $p |-  ( ( ( ch -> -. ps ) /\ ( ph <-> ( ps \/ ch ) ) ) ->
                ( ( ph /\ -. ps ) <-> ch ) ) $=
    ( wn wi wo wb wa bi1 pm5.6 sylibr adantl bi2 olc imim12i syl exp3a a2d 
    impcom pm3.26 jcad impbid ) CBDZEZABCFZGZHZAUCHZCUFUHCEZUDUFAUEEUIAUEIABCJK
    LUGCAUCUFUDCAEUFCUCAUFCUCAUFCBAFZEZCUCHAEUFUEAEUKAUEMCUEAUJCBNABNOPCBAJKQRS
    UDUFTUAUB $.
    $( [22-Mar-2005] $) $( [3-Jan-2005] $)

  $( Removal of conjunct from one side of an equivalence. $)
  bimsc1 $p |- ( ( ( ph -> ps ) /\ ( ch <-> ( ps /\ ph ) ) )
               -> ( ch <-> ph ) ) $=
    ( wa wb wi id pm4.71r biimpi bicomd sylan9bbr ) CBADZEZCLABFZAMGNALNALEABHI
    JK $.
    $( [5-Aug-1993] $)

  ${
    ecase2d.1 $e |- ( ph -> ps ) $.
    ecase2d.2 $e |- ( ph -> -. ( ps /\ ch ) ) $.
    ecase2d.3 $e |- ( ph -> -. ( ps /\ th ) ) $.
    ecase2d.4 $e |- ( ph -> ( ta \/ ( ch \/ th ) ) ) $.
    $( Deduction for elimination by cases. $)
    ecase2d $p |- ( ph -> ta ) $=
      ( wo wn wa wi imnan sylibr mpd jca ioran orcom sylib ord ) ACDJZKZEACKZDK
      ZLUCAUDUEABUDFABCLKBUDMGBCNOPABUEFABDLKBUEMHBDNOPQCDROAUBEAEUBJUBEJIEUBST
      UAP $.
      $( [21-Apr-1994] $)
  $}

  ${
    ecase3.1 $e |- ( ph -> ch ) $.
    ecase3.2 $e |- ( ps -> ch ) $.
    ecase3.3 $e |- ( -. ( ph \/ ps ) -> ch ) $.
    $( Inference for elimination by cases. $)
    ecase3 $p |- ch $=
      ( wn wa wo ioran sylbir ex pm2.61ii ) ABCAGZBGZCNOHABIGCABJFKLDEM $.
      $( [23-Mar-1995] $)
  $}

  ${
    ecase.1 $e |- ( -. ph -> ch ) $.
    ecase.2 $e |- ( -. ps -> ch ) $.
    ecase.3 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( Inference for elimination by cases. $)
    ecase $p |- ch $=
      ( ex pm2.61nii ) ABCABCFGDEH $.
      $( [22-Jul-2005] $) $( [13-Jul-2005] $)
  $}

  ${
    ecase3d.1 $e |- ( ph -> ( ps -> th ) ) $.
    ecase3d.2 $e |- ( ph -> ( ch -> th ) ) $.
    ecase3d.3 $e |- ( ph -> ( -. ( ps \/ ch ) -> th ) ) $.
    $( Deduction for elimination by cases. $)
    ecase3d $p |- ( ph -> th ) $=
      ( wi com12 wo wn ecase3 ) BCADHABDEIACDFIABCJKDGIL $.
      $( [2-May-1996] $)
  $}

  ${
    ccase.1 $e |- ( ( ph /\ ps ) -> ta ) $.
    ccase.2 $e |- ( ( ch /\ ps ) -> ta ) $.
    ccase.3 $e |- ( ( ph /\ th ) -> ta ) $.
    ccase.4 $e |- ( ( ch /\ th ) -> ta ) $.
    $( Inference for combining cases. $)
    ccase $p |- ( ( ( ph \/ ch ) /\ ( ps \/ th ) ) -> ta ) $=
      ( wo wa anddi or4 bitri jaoi sylbi ) ACJBDJKZABKZCBKZJZADKZCDKZJZJZEQRUAJ
      SUBJJUDACBDLRUASUBMNTEUCRESFGOUAEUBHIOOP $.
      $( [29-Jul-1999] $)
  $}

  ${
    $v et $. $( Greek eta $)
    ccasedwet $f wff et $.
    ccased.1 $e |- ( ph -> ( ( ps /\ ch ) -> et ) ) $.
    ccased.2 $e |- ( ph -> ( ( th /\ ch ) -> et ) ) $.
    ccased.3 $e |- ( ph -> ( ( ps /\ ta ) -> et ) ) $.
    ccased.4 $e |- ( ph -> ( ( th /\ ta ) -> et ) ) $.
    $( Deduction for combining cases. $)
    ccased $p |- ( ph -> ( ( ( ps \/ th ) /\ ( ch \/ ta ) ) -> et ) ) $=
      ( wa wo jaod anddi or4 bitri syl5ib ) ABCKZDCKZLZBEKZDEKZLZLZFBDLCELKZATF
      UCARFSGHMAUAFUBIJMMUERUALSUBLLUDBDCENRUASUBOPQ $.
      $( [10-May-2004] $) $( [9-May-2004] $)
  $}

  ${
    ccase2.1 $e |- ( ( ph /\ ps ) -> ta ) $.
    ccase2.2 $e |- ( ch -> ta ) $.
    ccase2.3 $e |- ( th -> ta ) $.
    $( Inference for combining cases. $)
    ccase2 $p |- ( ( ( ph \/ ch ) /\ ( ps \/ th ) ) -> ta ) $=
      ( adantr adantl ccase ) ABCDEFCEBGIDEAHJDECHJK $.
      $( [29-Jul-1999] $)
  $}

  ${
    4cases.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    4cases.2 $e |- ( ( ph /\ -. ps ) -> ch ) $.
    4cases.3 $e |- ( ( -. ph /\ ps ) -> ch ) $.
    4cases.4 $e |- ( ( -. ph /\ -. ps ) -> ch ) $.
    $( Inference eliminating two antecedents from the four possible cases that
       result from their true/false combinations. $)
    4cases $p |- ch $=
      ( pm2.61ian wn pm2.61i ) BCABCDFHABICEGHJ $.
      $( [25-Oct-2003] $) $( [25-Oct-2003] $)
  $}

  ${
    niabn.1 $e |- ph $.
    $( Miscellaneous inference relating falsehoods. $)
    niabn $p |- ( -. ps -> ( ( ch /\ ps ) <-> -. ph ) ) $=
      ( wa wn pm3.27 pm2.24i pm5.21ni ) CBEBAFCBGABDHI $.
      $( [31-Mar-1994] $)
  $}

  $( Lemma for an alternate version of weak deduction theorem. $)
  dedlem0a $p |- ( ph -> ( ps <-> ( ( ch -> ph ) -> ( ps /\ ph ) ) ) ) $=
    ( wi wa ax-1 imim1i com12 impbid2 iba imbi2d bitrd ) ABCADZBDZMBAEZDABNBMFN
    ABAMBACFGHIABOMABJKL $.
    $( [2-Apr-1994] $)

  $( Lemma for an alternate version of weak deduction theorem. $)
  dedlem0b $p |- ( -. ph -> ( ps <-> ( ( ps -> ph ) -> ( ch /\ ph ) ) ) ) $=
    ( wn wi wa pm2.21 imim2d com23 pm3.27 imim12i con1d com12 impbid ) ADZBBAEZ
    CAFZEZOPBQOAQBAQGHIROBRBABDPQABAGCAJKLMN $.
    $( [2-Apr-1994] $)

  $( Lemma for weak deduction theorem. $)
  dedlema $p |- ( ph -> ( ps <-> ( ( ps /\ ph ) \/ ( ch /\ -. ph ) ) ) ) $=
    ( wn wa wo orc idd pm2.24 adantld jaod impbid2 iba orbi1d bitrd ) ABBCADZEZ
    FZBAEZQFABRBQGABBQABHAPBCABIJKLABSQABMNO $.
    $( [26-Jun-2002] $)

  $( Lemma for weak deduction theorem. $)
  dedlemb $p |- ( -. ph -> ( ch <-> ( ( ps /\ ph ) \/ ( ch /\ -. ph ) ) ) ) $=
    ( wn wa wo olc expcom wi pm2.21 com23 imp3a pm3.26 a1i jaod impbid ) ADZCBA
    EZCQEZFZCQTSRGHQRCSQBACQABCABCIJKLSCIQCQMNOP $.
    $( [15-May-1999] $)

  ${
    elimh.1 $e |- ( ( ph <-> ( ( ph /\ ch ) \/ ( ps /\ -. ch ) ) )
                     -> ( ch <-> ta ) ) $.
    elimh.2 $e |- ( ( ps <-> ( ( ph /\ ch ) \/ ( ps /\ -. ch ) ) )
                     -> ( th <-> ta ) ) $.
    elimh.3 $e |- th $.
    $( Hypothesis builder for weak deduction theorem.  For more information,
       see the Deduction Theorem link on the Metamath Proof Explorer home
       page. $)
    elimh $p |- ta $=
      ( wa wn wo wb dedlema syl ibi dedlemb mpbii pm2.61i ) CECECAACIBCJZIKZLCE
      LCABMFNOSDEHSBTLDELCABPGNQR $.
      $( [26-Jun-2002] $)
  $}

  ${
    dedt.1 $e |- ( ( ph <-> ( ( ph /\ ch ) \/ ( ps /\ -. ch ) ) )
                     -> ( th <-> ta ) ) $.
    dedt.2 $e |- ta $.
    $( The weak deduction theorem.  For more information, see the Deduction
       Theorem link on the Metamath Proof Explorer home page. $)
    dedt $p |- ( ch -> th ) $=
      ( wa wn wo wb dedlema mpbiri syl ) CAACHBCIHJKZDCABLODEGFMN $.
      $( [26-Jun-2002] $)
  $}

  $( Contraposition.  Theorem *2.16 of [WhiteheadRussell] p. 103.  This version
     of ~ con3 demonstrates the use of the weak deduction theorem to derive
     it from ~ con3i . $)
  con3th $p |- ( ( ph -> ps ) -> ( -. ps -> -. ph ) ) $=
    ( wi wn wa wo wb id notbid imbi1d imbi2d elimh con3i dedt ) BAABCZBDZADZCBO
    EAODEFZDZQCBRGZPSQTBRTHZIJARBAOAACARCTBRAUAKARGZARAUBHKAHLMN $.
    $( [27-Jun-2002] $)

  $( The consensus theorem.  This theorem and its dual (with ` \/ ` and ` /\ `
     interchanged) are commonly used in computer logic design to eliminate
     redundant terms from Boolean expressions.  Specifically, we prove that the
     term ` ( ps /\ ch ) ` on the left-hand side is redundant. $)
  consensus $p |- ( ( ( ( ph /\ ps ) \/ ( -. ph /\ ch ) ) \/ ( ps /\ ch ) ) <->
                      ( ( ph /\ ps ) \/ ( -. ph /\ ch ) ) ) $=
    ( wa wn wo id wi dedlema biimpd adantrd dedlemb adantld pm2.61i ancom 
    orbi12i sylib jaoi orc impbii ) ABDZAEZCDZFZBCDZFUDUDUDUEUDGUEBADZCUBDZFZUD
    AUEUHHABUHCABUHABCIJKUBCUHBUBCUHABCLJMNUFUAUGUCBAOCUBOPQRUDUEST $.
    $( [16-May-2003] $)

  $( Theorem *4.42 of [WhiteheadRussell] p. 119.  (Contributed by Roy F.
     Longton, 21-Jun-2005.) $)
  pm4.42 $p |-  ( ph <-> ( ( ph /\ ps ) \/ ( ph /\ -. ps ) ) ) $=
    ( wa wn wo wb dedlema dedlemb pm2.61i ) BAABCABDCEFBAAGBAAHI $.
    $( [21-Jun-2005] $) $( [21-Jun-2005] $)

  ${
    ninba.1 $e |- ph $.
    $( Miscellaneous inference relating falsehoods. $)
    ninba $p |- ( -. ps -> ( -. ph <-> ( ch /\ ps ) ) ) $=
      ( wn wa niabn bicomd ) BECBFAEABCDGH $.
      $( [31-Mar-1994] $)
  $}

  ${
    $v et $. $( Greek eta $)
    wet $f wff et $.
    prlem1.1 $e |- ( ph -> ( et <-> ch ) ) $.
    prlem1.2 $e |- ( ps -> -. th ) $.
    $( A specialized lemma for set theory (to derive the Axiom of Pairing). $)
    prlem1 $p |- ( ph -> ( ps ->
                  ( ( ( ps /\ ch ) \/ ( th /\ ta ) ) -> et ) ) ) $=
      ( wa wo wi biimprcd adantl a1dd wn pm2.24 syl5 adantr a1d jaoi com3l ) BC
      IZDEIZJABFUBABFKZKUCUBAFBCAFKBAFCGLMNUCUDADUDEDDOFBDFPHQRSTUA $.
      $( [18-Oct-1995] $)
  $}

  $( A specialized lemma for set theory (to derive the Axiom of Pairing). $)
  prlem2 $p |- ( ( ( ph /\ ps ) \/ ( ch /\ th ) ) <->
               ( ( ph \/ ch ) /\ ( ( ph /\ ps ) \/ ( ch /\ th ) ) ) ) $=
    ( wa wo orabs anbi1i anass bitri orcom orbi12i andi bitr4i ) ABEZCDEZFZACFZ
    OEZRPEZFRQEOSPTORAEZBESAUABACGHRABIJPRCEZDETCUBDCCAFZCEUBCAGUCRCCAKHJHRCDIJ
    LROPMN $.
    $( [5-Aug-1993] $)

  ${
    oplem1.1 $e |- ( ph -> ( ps \/ ch ) ) $.
    oplem1.2 $e |- ( ph -> ( th \/ ta ) ) $.
    oplem1.3 $e |- ( ps <-> th ) $.
    oplem1.4 $e |- ( ch -> ( th <-> ta ) ) $.
    $( A specialized lemma for set theory (ordered pair theorem). $)
    oplem1 $p |- ( ph -> ps ) $=
      ( wn wi wa ord notbii syl5ib jcad syl5bb biimpar syl6 pm2.18 syl ) ABJZBK
      BAUBCELBAUBCEABCFMADJEUBADEGMBDHNOPCBECDEBIHQRSBTUA $.
      $( [18-Oct-1995] $)
  $}

  $( Lemma used in construction of real numbers. $)
  rnlem $p |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) <->
  ( ( ( ph /\ ch ) /\ ( ps /\ th ) ) /\ ( ( ph /\ th ) /\ ( ps /\ ch ) ) ) ) $=
    ( wa anandir anandi anbi12i ancom anbi2i an4 bitri 3bitri ) ABECDEZEANEZBNE
    ZEACEZADEZEZBCEZBDEZEZEZQUAERTEEZABNFOSPUBACDGBCDGHUCSUATEZEUDUBUESTUAIJQRU
    ATKLM $.
    $( [4-Sep-1995] $)

  $( A single axiom for Boolean algebra known as DN_1.  See
     ~ http://www-unix.mcs.anl.gov/~~mccune/papers/basax/v12.pdf .
     (Contributed by Jeffrey Hankins, 3-Jul-2009.) $)
  dn1 $p |- ( -. ( -. ( -. ( ph \/ ps ) \/ ch ) \/
            -. ( ph \/ -. ( -. ch \/ -. ( ch \/ th ) ) ) ) <-> ch ) $=
    ( wo wn wa anor wi ioran pm2.24 com23 ax-1 a1d adantr sylbir jaoi com13 
    imp sylbi olc imp3a syl5ib jaod con3d orrd jca impbii bitr3i ) ABEFZCEZFACF
    ZCDEZFZEZFZEZFEFUKUQGZCUKUQHURCUKUQCUJUQCIZCUJAFZBFZGUSABJUTVAUSUQVAUTCAVAU
    TCIZIZUPAUTVACAVACIKLUPCUMGVCCUMHCVCUMCVBVACUTMNOPQRSTCUQMQSCUKUQCUJUACAUPC
    UOACULAUNCAKCULDFZGAUNCULVDACVDAIKUBCDJUCUDUEUFUGUHUI $.
    $( [8-Jul-2009] $) $( [22-Jun-2005] $)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Abbreviated conjunction and disjunction of three wff's
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Extend wff definition to include 3-way disjunction ('or'). $)
  w3o $a wff ( ph \/ ps \/ ch ) $.
  $( Extend wff definition to include 3-way conjunction ('and'). $)
  w3a $a wff ( ph /\ ps /\ ch ) $.

  $( These abbreviations help eliminate parentheses to aid readability. $)

  $( Define disjunction ('or') of 3 wff's.  Definition *2.33 of
     [WhiteheadRussell] p. 105.  This abbreviation reduces the number of
     parentheses and emphasizes that the order of bracketing is not
     important by virtue of the associative law ~ orass . $)
  df-3or $a |- ( ( ph \/ ps \/ ch ) <-> ( ( ph \/ ps ) \/ ch ) ) $.

  $( Define conjunction ('and') of 3 wff.s.  Definition *4.34 of
     [WhiteheadRussell] p. 118.  This abbreviation reduces the number of
     parentheses and emphasizes that the order of bracketing is not
     important by virtue of the associative law ~ anass . $)
  df-3an $a |- ( ( ph /\ ps /\ ch ) <-> ( ( ph /\ ps ) /\ ch ) ) $.

  $( Associative law for triple disjunction. $)
  3orass $p |- ( ( ph \/ ps \/ ch ) <-> ( ph \/ ( ps \/ ch ) ) ) $=
    ( w3o wo df-3or orass bitri ) ABCDABECEABCEEABCFABCGH $.
    $( [8-Apr-1994] $)

  $( Associative law for triple conjunction. $)
  3anass $p |- ( ( ph /\ ps /\ ch ) <-> ( ph /\ ( ps /\ ch ) ) ) $=
    ( w3a wa df-3an anass bitri ) ABCDABECEABCEEABCFABCGH $.
    $( [8-Apr-1994] $)

  $( Rotation law for triple conjunction. $)
  3anrot $p |- ( ( ph /\ ps /\ ch ) <-> ( ps /\ ch /\ ph ) ) $=
    ( wa w3a ancom 3anass df-3an 3bitr4i ) ABCDZDJADABCEBCAEAJFABCGBCAHI $.
    $( [8-Apr-1994] $)

  $( Rotation law for triple disjunction. $)
  3orrot $p |- ( ( ph \/ ps \/ ch ) <-> ( ps \/ ch \/ ph ) ) $=
    ( wo w3o orcom 3orass df-3or 3bitr4i ) ABCDZDJADABCEBCAEAJFABCGBCAHI $.
    $( [4-Apr-1995] $)

  $( Commutation law for triple conjunction. $)
  3ancoma $p |- ( ( ph /\ ps /\ ch ) <-> ( ps /\ ph /\ ch ) ) $=
    ( wa w3a ancom anbi1i df-3an 3bitr4i ) ABDZCDBADZCDABCEBACEJKCABFGABCHBACHI
    $.
    $( [21-Apr-1994] $)

  $( Commutation law for triple conjunction. $)
  3ancomb $p |- ( ( ph /\ ps /\ ch ) <-> ( ph /\ ch /\ ps ) ) $=
    ( w3a 3ancoma 3anrot bitri ) ABCDBACDACBDABCEBACFG $.
    $( [21-Apr-1994] $)

  $( Reversal law for triple conjunction. $)
  3anrev $p |- ( ( ph /\ ps /\ ch ) <-> ( ch /\ ps /\ ph ) ) $=
    ( w3a 3ancoma 3anrot bitr4i ) ABCDBACDCBADABCECBAFG $.
    $( [21-Apr-1994] $)

  $( Simplification of triple conjunction. $)
  3simpa $p |- ( ( ph /\ ps /\ ch ) -> ( ph /\ ps ) ) $=
    ( w3a wa df-3an pm3.26bi ) ABCDABECABCFG $.
    $( [21-Apr-1994] $)

  $( Simplification of triple conjunction. $)
  3simpb $p |- ( ( ph /\ ps /\ ch ) -> ( ph /\ ch ) ) $=
    ( w3a wa 3ancomb 3simpa sylbi ) ABCDACBDACEABCFACBGH $.
    $( [21-Apr-1994] $)

  $( Simplification of triple conjunction. $)
  3simpc $p |- ( ( ph /\ ps /\ ch ) -> ( ps /\ ch ) ) $=
    ( w3a wa 3anrot 3simpa sylbi ) ABCDBCADBCEABCFBCAGH $.
    $( [21-Apr-1994] $)

  $( Simplification of triple conjunction. $)
  3simp1 $p |- ( ( ph /\ ps /\ ch ) -> ph ) $=
    ( w3a 3simpa pm3.26d ) ABCDABABCEF $.
    $( [21-Apr-1994] $)

  $( Simplification of triple conjunction. $)
  3simp2 $p |- ( ( ph /\ ps /\ ch ) -> ps ) $=
    ( w3a 3simpa pm3.27d ) ABCDABABCEF $.
    $( [21-Apr-1994] $)

  $( Simplification of triple conjunction. $)
  3simp3 $p |- ( ( ph /\ ps /\ ch ) -> ch ) $=
    ( w3a 3simpc pm3.27d ) ABCDBCABCEF $.
    $( [21-Apr-1994] $)

  $( Simplification rule.  (Contributed by Jeff Hankins, 17-Nov-2009.) $)
  3simpl1 $p |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ph ) $=
    ( w3a 3simp1 adantr ) ABCEADABCFG $.
    $( [18-Apr-2010] $) $( [17-Nov-2009] $)

  $( Simplification rule.  (Contributed by Jeff Hankins, 17-Nov-2009.) $)
  3simpl2 $p |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ps ) $=
    ( w3a 3simp2 adantr ) ABCEBDABCFG $.
    $( [18-Apr-2010] $) $( [17-Nov-2009] $)

  $( Simplification rule.  (Contributed by Jeff Hankins, 17-Nov-2009.) $)
  3simpl3 $p |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ch ) $=
    ( w3a 3simp3 adantr ) ABCECDABCFG $.
    $( [18-Apr-2010] $) $( [17-Nov-2009] $)

  $( Simplification rule.  (Contributed by Jeff Hankins, 17-Nov-2009.) $)
  3simpr1 $p |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> ps ) $=
    ( w3a 3simp1 adantl ) BCDEBABCDFG $.
    $( [18-Apr-2010] $) $( [17-Nov-2009] $)

  $( Simplification rule.  (Contributed by Jeff Hankins, 17-Nov-2009.) $)
  3simpr2 $p |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> ch ) $=
    ( w3a 3simp2 adantl ) BCDECABCDFG $.
    $( [18-Apr-2010] $) $( [17-Nov-2009] $)

  $( Simplification rule.  (Contributed by Jeff Hankins, 17-Nov-2009.) $)
  3simpr3 $p |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> th ) $=
    ( w3a 3simp3 adantl ) BCDEDABCDFG $.
    $( [18-Apr-2010] $) $( [17-Nov-2009] $)

  ${
    3simp1i.1 $e |- ( ph /\ ps /\ ch ) $.
    $( Infer a conjunct from a triple conjunction. $)
    3simp1i $p |- ph $=
      ( w3a 3simp1 ax-mp ) ABCEADABCFG $.
      $( [21-Apr-2005] $) $( [19-Apr-2005] $)

    $( Infer a conjunct from a triple conjunction. $)
    3simp2i $p |- ps $=
      ( w3a 3simp2 ax-mp ) ABCEBDABCFG $.
      $( [21-Apr-2005] $) $( [19-Apr-2005] $)

    $( Infer a conjunct from a triple conjunction. $)
    3simp3i $p |- ch $=
      ( w3a 3simp3 ax-mp ) ABCECDABCFG $.
      $( [21-Apr-2005] $) $( [19-Apr-2005] $)
  $}

  ${
    3simp1d.1 $e |- ( ph -> ( ps /\ ch /\ th ) ) $.
    $( Deduce a conjunct from a triple conjunction. $)
    3simp1d $p |- ( ph -> ps ) $=
      ( w3a 3simp1 syl ) ABCDFBEBCDGH $.
      $( [6-Sep-2005] $) $( [4-Sep-2005] $)

    $( Deduce a conjunct from a triple conjunction. $)
    3simp2d $p |- ( ph -> ch ) $=
      ( w3a 3simp2 syl ) ABCDFCEBCDGH $.
      $( [6-Sep-2005] $) $( [4-Sep-2005] $)

    $( Deduce a conjunct from a triple conjunction. $)
    3simp3d $p |- ( ph -> th ) $=
      ( w3a 3simp3 syl ) ABCDFDEBCDGH $.
      $( [7-Sep-2005] $) $( [4-Sep-2005] $)
  $}

  ${
    3adant.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( Deduction adding a conjunct to antecedent. $)
    3adant1 $p |- ( ( th /\ ph /\ ps ) -> ch ) $=
      ( w3a wa 3simpc syl ) DABFABGCDABHEI $.
      $( [16-Jul-1995] $)

    $( Deduction adding a conjunct to antecedent. $)
    3adant2 $p |- ( ( ph /\ th /\ ps ) -> ch ) $=
      ( w3a wa 3simpb syl ) ADBFABGCADBHEI $.
      $( [16-Jul-1995] $)

    $( Deduction adding a conjunct to antecedent. $)
    3adant3 $p |- ( ( ph /\ ps /\ th ) -> ch ) $=
      ( w3a wa 3simpa syl ) ABDFABGCABDHEI $.
      $( [16-Jul-1995] $)
  $}

  ${
    3ad2ant.1 $e |- ( ph -> ch ) $.
    $( Deduction adding conjuncts to an antecedent. $)
    3ad2ant1 $p |- ( ( ph /\ ps /\ th ) -> ch ) $=
      ( adantr 3adant2 ) ADCBACDEFG $.
      $( [23-Apr-2005] $) $( [21-Apr-2005] $)

    $( Deduction adding conjuncts to an antecedent. $)
    3ad2ant2 $p |- ( ( ps /\ ph /\ th ) -> ch ) $=
      ( adantr 3adant1 ) ADCBACDEFG $.
      $( [23-Apr-2005] $) $( [21-Apr-2005] $)

    $( Deduction adding conjuncts to an antecedent. $)
    3ad2ant3 $p |- ( ( ps /\ th /\ ph ) -> ch ) $=
      ( adantl 3adant1 ) DACBACDEFG $.
      $( [23-Apr-2005] $) $( [21-Apr-2005] $)
  $}

  ${
    3adantl.1 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
    $( Deduction adding a conjunct to antecedent. $)
    3adantl1 $p |- ( ( ( ta /\ ph /\ ps ) /\ ch ) -> th ) $=
      ( w3a wi wa ex 3adant1 imp ) EABGCDABCDHEABICDFJKL $.
      $( [26-Feb-2005] $) $( [24-Feb-2005] $)

    $( Deduction adding a conjunct to antecedent. $)
    3adantl2 $p |- ( ( ( ph /\ ta /\ ps ) /\ ch ) -> th ) $=
      ( w3a wi wa ex 3adant2 imp ) AEBGCDABCDHEABICDFJKL $.
      $( [25-Feb-2005] $) $( [24-Feb-2005] $)

    $( Deduction adding a conjunct to antecedent. $)
    3adantl3 $p |- ( ( ( ph /\ ps /\ ta ) /\ ch ) -> th ) $=
      ( w3a wi wa ex 3adant3 imp ) ABEGCDABCDHEABICDFJKL $.
      $( [28-Apr-2005] $) $( [24-Feb-2005] $)
  $}

  ${
    3adantr.1 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
    $( Deduction adding a conjunct to antecedent. $)
    3adantr1 $p |- ( ( ph /\ ( ta /\ ps /\ ch ) ) -> th ) $=
      ( w3a wa ancoms 3adantl1 ) EBCGADBCADEABCHDFIJI $.
      $( [27-Jun-2005] $) $( [27-Apr-2005] $)

    $( Deduction adding a conjunct to antecedent. $)
    3adantr2 $p |- ( ( ph /\ ( ps /\ ta /\ ch ) ) -> th ) $=
      ( w3a wa ancoms 3adantl2 ) BECGADBCADEABCHDFIJI $.
      $( [28-Apr-2005] $) $( [27-Apr-2005] $)

    $( Deduction adding a conjunct to antecedent. $)
    3adantr3 $p |- ( ( ph /\ ( ps /\ ch /\ ta ) ) -> th ) $=
      ( w3a wa ancoms 3adantl3 ) BCEGADBCADEABCHDFIJI $.
      $( [28-Apr-2005] $) $( [27-Apr-2005] $)
  $}

  ${
    3ad2antl.1 $e |- ( ( ph /\ ch ) -> th ) $.
    $( Deduction adding conjuncts to antecedent. $)
    3ad2antl1 $p |- ( ( ( ph /\ ps /\ ta ) /\ ch ) -> th ) $=
      ( adantlr 3adantl2 ) AECDBACDEFGH $.
      $( [4-Aug-2007] $) $( [4-Aug-2007] $)

    $( Deduction adding conjuncts to antecedent. $)
    3ad2antl2 $p |- ( ( ( ps /\ ph /\ ta ) /\ ch ) -> th ) $=
      ( adantlr 3adantl1 ) AECDBACDEFGH $.
      $( [4-Aug-2007] $) $( [4-Aug-2007] $)

    $( Deduction adding conjuncts to antecedent. $)
    3ad2antl3 $p |- ( ( ( ps /\ ta /\ ph ) /\ ch ) -> th ) $=
      ( adantll 3adantl1 ) EACDBACDEFGH $.
      $( [4-Aug-2007] $) $( [4-Aug-2007] $)

    $( Deduction adding a conjuncts to antecedent. $)
    3ad2antr1 $p |- ( ( ph /\ ( ch /\ ps /\ ta ) ) -> th ) $=
      ( adantrr 3adantr3 ) ACBDEACDBFGH $.
      $( [25-Dec-2007] $) $( [25-Dec-2007] $)

    $( Deduction adding a conjuncts to antecedent. $)
    3ad2antr2 $p |- ( ( ph /\ ( ps /\ ch /\ ta ) ) -> th ) $=
      ( adantrl 3adantr3 ) ABCDEACDBFGH $.
      $( [27-Dec-2007] $) $( [27-Dec-2007] $)

    $( Deduction adding a conjuncts to antecedent. $)
    3ad2antr3 $p |- ( ( ph /\ ( ps /\ ta /\ ch ) ) -> th ) $=
      ( adantrl 3adantr1 ) AECDBACDEFGH $.
      $( [30-Dec-2007] $) $( [30-Dec-2007] $)
  $}

  $( Introduction in triple disjunction. $)
  3mix1 $p |- ( ph -> ( ph \/ ps \/ ch ) ) $=
    ( wo w3o orc 3orass sylibr ) AABCDZDABCEAIFABCGH $.
    $( [4-Apr-1995] $)

  $( Introduction in triple disjunction. $)
  3mix2 $p |- ( ph -> ( ps \/ ph \/ ch ) ) $=
    ( w3o 3mix1 3orrot sylibr ) AACBDBACDACBEBACFG $.
    $( [4-Apr-1995] $)

  $( Introduction in triple disjunction. $)
  3mix3 $p |- ( ph -> ( ps \/ ch \/ ph ) ) $=
    ( w3o 3mix1 3orrot sylib ) AABCDBCADABCEABCFG $.
    $( [4-Apr-1995] $)

  ${
    3pm3.2i.1 $e |- ph $.
    3pm3.2i.2 $e |- ps $.
    3pm3.2i.3 $e |- ch $.
    $( Infer conjunction of premises. $)
    3pm3.2i $p |- ( ph /\ ps /\ ch ) $=
      ( w3a wa df-3an pm3.2i mpbir2an ) ABCGABHCABCIABDEJFK $.
      $( [10-Feb-1995] $)
  $}

  ${
    3jca.1 $e |- ( ph -> ps ) $.
    3jca.2 $e |- ( ph -> ch ) $.
    3jca.3 $e |- ( ph -> th ) $.
    $( Join consequents with conjunction. $)
    3jca $p |- ( ph -> ( ps /\ ch /\ th ) ) $=
      ( wa w3a jca df-3an sylibr ) ABCHZDHBCDIAMDABCEFJGJBCDKL $.
      $( [9-Apr-1994] $)
  $}

  ${
    3jcad.1 $e |- ( ph -> ( ps -> ch ) ) $.
    3jcad.2 $e |- ( ph -> ( ps -> th ) ) $.
    3jcad.3 $e |- ( ph -> ( ps -> ta ) ) $.
    $( Deduction conjoining the consequents of three implications. $)
    3jcad $p |- ( ph -> ( ps -> ( ch /\ th /\ ta ) ) ) $=
      ( w3a wa imp 3jca ex ) ABCDEIABJCDEABCFKABDGKABEHKLM $.
      $( [3-Oct-2005] $) $( [25-Sep-2005] $)
  $}

  ${
    $v et $. $( Greek eta $)
    i3wet $f wff et $.
    3anim123i.1 $e |- ( ph -> ps ) $.
    3anim123i.2 $e |- ( ch -> th ) $.
    3anim123i.3 $e |- ( ta -> et ) $.
    $( Join antecedents and consequents with conjunction. $)
    3anim123i $p |- ( ( ph /\ ch /\ ta ) -> ( ps /\ th /\ et ) ) $=
      ( wa w3a anim12i df-3an 3imtr4i ) ACJZEJBDJZFJACEKBDFKOPEFABCDGHLILACEMBD
      FMN $.
      $( [8-Apr-1994] $)
  $}

  ${
    $v et $. $( Greek eta $)
    b3wet $f wff et $.
    bi3.1 $e |- ( ph <-> ps ) $.
    bi3.2 $e |- ( ch <-> th ) $.
    bi3.3 $e |- ( ta <-> et ) $.
    $( Join 3 biconditionals with conjunction. $)
    3anbi123i $p |- ( ( ph /\ ch /\ ta ) <-> ( ps /\ th /\ et ) ) $=
      ( wa w3a anbi12i df-3an 3bitr4i ) ACJZEJBDJZFJACEKBDFKOPEFABCDGHLILACEMBD
      FMN $.
      $( [21-Apr-1994] $)

    $( Join 3 biconditionals with disjunction. $)
    3orbi123i $p |- ( ( ph \/ ch \/ ta ) <-> ( ps \/ th \/ et ) ) $=
      ( wo w3o orbi12i df-3or 3bitr4i ) ACJZEJBDJZFJACEKBDFKOPEFABCDGHLILACEMBD
      FMN $.
      $( [17-May-1994] $)
  $}

  ${
    3anbi1i.1 $e |- ( ph <-> ps ) $.
    $( Inference adding two conjuncts to each side of a biconditional. $)
    3anbi1i $p |- ( ( ph /\ ch /\ th ) <-> ( ps /\ ch /\ th ) ) $=
      ( biid 3anbi123i ) ABCCDDECFDFG $.
      $( [8-Sep-2006] $) $( [8-Sep-2006] $)

    $( Inference adding two conjuncts to each side of a biconditional. $)
    3anbi2i $p |- ( ( ch /\ ph /\ th ) <-> ( ch /\ ps /\ th ) ) $=
      ( biid 3anbi123i ) CCABDDCFEDFG $.
      $( [5-Oct-2006] $) $( [8-Sep-2006] $)

    $( Inference adding two conjuncts to each side of a biconditional. $)
    3anbi3i $p |- ( ( ch /\ th /\ ph ) <-> ( ch /\ th /\ ps ) ) $=
      ( biid 3anbi123i ) CCDDABCFDFEG $.
      $( [18-Oct-2006] $) $( [8-Sep-2006] $)
  $}

  ${
    3imp.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    $( Importation inference. $)
    3imp $p |- ( ( ph /\ ps /\ ch ) -> th ) $=
      ( w3a wa df-3an imp31 sylbi ) ABCFABGCGDABCHABCDEIJ $.
      $( [8-Apr-1994] $)
  $}

  ${
    3impa.1 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
    $( Importation from double to triple conjunction. $)
    3impa $p |- ( ( ph /\ ps /\ ch ) -> th ) $=
      ( exp31 3imp ) ABCDABCDEFG $.
      $( [20-Aug-1995] $)
  $}

  ${
    3impb.1 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
    $( Importation from double to triple conjunction. $)
    3impb $p |- ( ( ph /\ ps /\ ch ) -> th ) $=
      ( exp32 3imp ) ABCDABCDEFG $.
      $( [20-Aug-1995] $)
  $}

  ${
    3impia.1 $e |- ( ( ph /\ ps ) -> ( ch -> th ) ) $.
    $( Importation to triple conjunction. $)
    3impia $p |- ( ( ph /\ ps /\ ch ) -> th ) $=
      ( wi ex 3imp ) ABCDABCDFEGH $.
      $( [13-Jun-2006] $) $( [13-Jun-2006] $)
  $}

  ${
    3impib.1 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
    $( Importation to triple conjunction. $)
    3impib $p |- ( ( ph /\ ps /\ ch ) -> th ) $=
      ( exp3a 3imp ) ABCDABCDEFG $.
      $( [15-Jun-2006] $) $( [13-Jun-2006] $)
  $}

  ${
    3exp.1 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
    $( Exportation inference. $)
    3exp $p |- ( ph -> ( ps -> ( ch -> th ) ) ) $=
      ( wa w3a df-3an sylbir exp31 ) ABCDABFCFABCGDABCHEIJ $.
      $( [30-May-1994] $)

    $( Exportation from triple to double conjunction. $)
    3expa $p |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $=
      ( 3exp imp31 ) ABCDABCDEFG $.
      $( [20-Aug-1995] $)

    $( Exportation from triple to double conjunction. $)
    3expb $p |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $=
      ( 3exp imp32 ) ABCDABCDEFG $.
      $( [20-Aug-1995] $)

    $( Exportation from triple conjunction. $)
    3expia $p |- ( ( ph /\ ps ) -> ( ch -> th ) ) $=
      ( wi 3exp imp ) ABCDFABCDEGH $.
      $( [19-May-2007] $) $( [19-May-2007] $)

    $( Exportation from triple conjunction. $)
    3expib $p |- ( ph -> ( ( ps /\ ch ) -> th ) ) $=
      ( 3exp imp3a ) ABCDABCDEFG $.
      $( [20-May-2007] $) $( [19-May-2007] $)

    $( Commutation in antecedent.  Swap 1st and 3rd. $)
    3com12 $p |- ( ( ps /\ ph /\ ch ) -> th ) $=
      ( wi 3exp com12 3imp ) BACDABCDFABCDEGHI $.
      $( [28-Jan-1996] $)

    $( Commutation in antecedent.  Swap 1st and 3rd. $)
    3com13 $p |- ( ( ch /\ ps /\ ph ) -> th ) $=
      ( w3a 3anrev sylbi ) CBAFABCFDCBAGEH $.
      $( [28-Jan-1996] $)

    $( Commutation in antecedent.  Swap 2nd and 3rd. $)
    3com23 $p |- ( ( ph /\ ch /\ ps ) -> th ) $=
      ( 3exp com23 3imp ) ACBDABCDABCDEFGH $.
      $( [28-Jan-1996] $)

    $( Commutation in antecedent.  Rotate left. $)
    3coml $p |- ( ( ps /\ ch /\ ph ) -> th ) $=
      ( 3com23 3com13 ) ACBDABCDEFG $.
      $( [28-Jan-1996] $)

    $( Commutation in antecedent.  Rotate right. $)
    3comr $p |- ( ( ch /\ ph /\ ps ) -> th ) $=
      ( 3coml ) BCADABCDEFF $.
      $( [28-Jan-1996] $)

    $( Deduction adding a conjunct to antecedent. $)
    3adant3r1 $p |- ( ( ph /\ ( ta /\ ps /\ ch ) ) -> th ) $=
      ( 3expb 3adantr1 ) ABCDEABCDFGH $.
      $( [16-Feb-2008] $) $( [16-Feb-2008] $)

    $( Deduction adding a conjunct to antecedent. $)
    3adant3r2 $p |- ( ( ph /\ ( ps /\ ta /\ ch ) ) -> th ) $=
      ( 3expb 3adantr2 ) ABCDEABCDFGH $.
      $( [17-Feb-2008] $) $( [17-Feb-2008] $)

    $( Deduction adding a conjunct to antecedent. $)
    3adant3r3 $p |- ( ( ph /\ ( ps /\ ch /\ ta ) ) -> th ) $=
      ( 3expb 3adantr3 ) ABCDEABCDFGH $.
      $( [18-Feb-2008] $) $( [18-Feb-2008] $)
  $}

  ${
    3an1rs.1 $e |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ta ) $.
    $( Swap conjuncts. $)
    3an1rs $p |- ( ( ( ph /\ ps /\ th ) /\ ch ) -> ta ) $=
      ( w3a wi ex 3exp com34 3imp imp ) ABDGCEABDCEHABCDEABCDEHABCGDEFIJKLM $.
      $( [3-Apr-2008] $) $( [16-Dec-2007] $)
  $}

  ${
    3imp1.1 $e |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $.
    $( Importation to left triple conjunction. $)
    3imp1 $p |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ta ) $=
      ( w3a wi 3imp imp ) ABCGDEABCDEHFIJ $.
      $( [26-Feb-2005] $) $( [24-Feb-2005] $)

    $( Importation deduction for triple conjunction. $)
    3impd $p |- ( ph -> ( ( ps /\ ch /\ th ) -> ta ) ) $=
      ( w3a wi com4l 3imp com12 ) BCDGAEBCDAEHABCDEFIJK $.
      $( [28-Oct-2006] $) $( [26-Oct-2006] $)

    $( Importation to right triple conjunction. $)
    3imp2 $p |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> ta ) $=
      ( w3a 3impd imp ) ABCDGEABCDEFHI $.
      $( [28-Oct-2006] $) $( [26-Oct-2006] $)
  $}

  ${
    3exp1.1 $e |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ta ) $.
    $( Exportation from left triple conjunction. $)
    3exp1 $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $=
      ( wi w3a ex 3exp ) ABCDEGABCHDEFIJ $.
      $( [26-Feb-2005] $) $( [24-Feb-2005] $)
  $}

  ${
    3expd.1 $e |- ( ph -> ( ( ps /\ ch /\ th ) -> ta ) ) $.
    $( Exportation deduction for triple conjunction. $)
    3expd $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $=
      ( wi w3a com12 3exp com4r ) BCDAEBCDAEGABCDHEFIJK $.
      $( [27-Oct-2006] $) $( [26-Oct-2006] $)
  $}

  ${
    3exp2.1 $e |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> ta ) $.
    $( Exportation from right triple conjunction. $)
    3exp2 $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $=
      ( w3a ex 3expd ) ABCDEABCDGEFHI $.
      $( [28-Oct-2006] $) $( [26-Oct-2006] $)
  $}

  ${
    3adant1l.1 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
    $( Deduction adding a conjunct to antecedent. $)
    3adant1l $p |- ( ( ( ta /\ ph ) /\ ps /\ ch ) -> th ) $=
      ( wa 3expb adantll 3impb ) EAGBCDABCGDEABCDFHIJ $.
      $( [12-Jan-2006] $) $( [8-Jan-2006] $)

    $( Deduction adding a conjunct to antecedent. $)
    3adant1r $p |- ( ( ( ph /\ ta ) /\ ps /\ ch ) -> th ) $=
      ( wa 3expb adantlr 3impb ) AEGBCDABCGDEABCDFHIJ $.
      $( [17-Jan-2006] $) $( [8-Jan-2006] $)

    $( Deduction adding a conjunct to antecedent. $)
    3adant2l $p |- ( ( ph /\ ( ta /\ ps ) /\ ch ) -> th ) $=
      ( wa 3com12 3adant1l ) EBGACDBACDEABCDFHIH $.
      $( [22-Feb-2006] $) $( [8-Jan-2006] $)

    $( Deduction adding a conjunct to antecedent. $)
    3adant2r $p |- ( ( ph /\ ( ps /\ ta ) /\ ch ) -> th ) $=
      ( wa 3com12 3adant1r ) BEGACDBACDEABCDFHIH $.
      $( [23-Jan-2006] $) $( [8-Jan-2006] $)

    $( Deduction adding a conjunct to antecedent. $)
    3adant3l $p |- ( ( ph /\ ps /\ ( ta /\ ch ) ) -> th ) $=
      ( wa 3com13 3adant1l ) ECGBADCBADEABCDFHIH $.
      $( [5-Feb-2006] $) $( [8-Jan-2006] $)

    $( Deduction adding a conjunct to antecedent. $)
    3adant3r $p |- ( ( ph /\ ps /\ ( ch /\ ta ) ) -> th ) $=
      ( wa 3com13 3adant1r ) CEGBADCBADEABCDFHIH $.
      $( [27-Jan-2006] $) $( [8-Jan-2006] $)
  $}

  ${
    syl3anc.1 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
    syl3anc.2 $e |- ( ta -> ph ) $.
    syl3anc.3 $e |- ( ta -> ps ) $.
    syl3anc.4 $e |- ( ta -> ch ) $.
    $( A syllogism inference combined with contraction. $)
    syl3anc $p |- ( ta -> th ) $=
      ( w3a 3jca syl ) EABCJDEABCGHIKFL $.
      $( [2-Jan-2005] $) $( [1-Jan-2005] $)
  $}

  ${
    $v et $. $( Greek eta $)
    $v ze $. $( Greek zeta $)
    syl3an.we $f wff et $.
    syl3an.wz $f wff ze $.
    syl3an.1 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
    ${
      syl3an1.2 $e |- ( ta -> ph ) $.
      $( A syllogism inference. $)
      syl3an1 $p |- ( ( ta /\ ps /\ ch ) -> th ) $=
        ( wa 3expb sylan 3impb ) EBCDABCHDEABCDFIGJK $.
        $( [22-Aug-1995] $)
    $}

    ${
      syl3an2.2 $e |- ( ta -> ps ) $.
      $( A syllogism inference. $)
      syl3an2 $p |- ( ( ph /\ ta /\ ch ) -> th ) $=
        ( wi 3exp syl5 3imp ) AECDABCDHEABCDFIGJK $.
        $( [22-Aug-1995] $)
    $}

    ${
      syl3an3.2 $e |- ( ta -> ch ) $.
      $( A syllogism inference. $)
      syl3an3 $p |- ( ( ph /\ ps /\ ta ) -> th ) $=
        ( 3exp syl7 3imp ) ABEDABCDEABCDFHGIJ $.
        $( [22-Aug-1995] $)
    $}

    ${
      syl3an1b.2 $e |- ( ta <-> ph ) $.
      $( A syllogism inference. $)
      syl3an1b $p |- ( ( ta /\ ps /\ ch ) -> th ) $=
        ( biimpi syl3an1 ) ABCDEFEAGHI $.
        $( [22-Aug-1995] $)
    $}

    ${
      syl3an2b.2 $e |- ( ta <-> ps ) $.
      $( A syllogism inference. $)
      syl3an2b $p |- ( ( ph /\ ta /\ ch ) -> th ) $=
        ( biimpi syl3an2 ) ABCDEFEBGHI $.
        $( [22-Aug-1995] $)
    $}

    ${
      syl3an3b.2 $e |- ( ta <-> ch ) $.
      $( A syllogism inference. $)
      syl3an3b $p |- ( ( ph /\ ps /\ ta ) -> th ) $=
        ( biimpi syl3an3 ) ABCDEFECGHI $.
        $( [22-Aug-1995] $)
    $}

    ${
      syl3an1br.2 $e |- ( ph <-> ta ) $.
      $( A syllogism inference. $)
      syl3an1br $p |- ( ( ta /\ ps /\ ch ) -> th ) $=
        ( biimpri syl3an1 ) ABCDEFAEGHI $.
        $( [22-Aug-1995] $)
    $}

    ${
      syl3an2br.2 $e |- ( ps <-> ta ) $.
      $( A syllogism inference. $)
      syl3an2br $p |- ( ( ph /\ ta /\ ch ) -> th ) $=
        ( biimpri syl3an2 ) ABCDEFBEGHI $.
        $( [22-Aug-1995] $)
    $}

    ${
      syl3an3br.2 $e |- ( ch <-> ta ) $.
      $( A syllogism inference. $)
      syl3an3br $p |- ( ( ph /\ ps /\ ta ) -> th ) $=
        ( biimpri syl3an3 ) ABCDEFCEGHI $.
        $( [22-Aug-1995] $)
    $}

    ${
      syl3an.2 $e |- ( ta -> ph ) $.
      syl3an.3 $e |- ( et -> ps ) $.
      syl3an.4 $e |- ( ze -> ch ) $.
      $( A triple syllogism inference. $)
      syl3an $p |- ( ( ta /\ et /\ ze ) -> th ) $=
        ( w3a 3anim123i syl ) EFGLABCLDEAFBGCIJKMHN $.
        $( [14-May-2004] $) $( [13-May-2004] $)
    $}

    ${
      syl3anb.2 $e |- ( ta <-> ph ) $.
      syl3anb.3 $e |- ( et <-> ps ) $.
      syl3anb.4 $e |- ( ze <-> ch ) $.
      $( A triple syllogism inference. $)
      syl3anb $p |- ( ( ta /\ et /\ ze ) -> th ) $=
        ( w3a 3anbi123i sylbi ) EFGLABCLDEAFBGCIJKMHN $.
        $( [20-Oct-2005] $) $( [15-Oct-2005] $)
    $}

    ${
      syld3an3.2 $e |- ( ( ph /\ ps /\ ta ) -> ch ) $.
      $( A syllogism inference. $)
      syld3an3 $p |- ( ( ph /\ ps /\ ta ) -> th ) $=
        ( w3a 3simp1 3simp2 syl3anc ) ABCDABEHFABEIABEJGK $.
        $( [23-May-2007] $) $( [20-May-2007] $)
    $}

    ${
      syld3an1.2 $e |- ( ( ta /\ ps /\ ch ) -> ph ) $.
      $( A syllogism inference. $)
      syld3an1 $p |- ( ( ta /\ ps /\ ch ) -> th ) $=
        ( 3com13 syld3an3 ) CBEDCBADEABCDFHEBCAGHIH $.
        $( [14-Jul-2008] $) $( [7-Jul-2008] $)
    $}

    ${
      syld3an2.2 $e |- ( ( ph /\ ta /\ ch ) -> ps ) $.
      $( A syllogism inference. $)
      syld3an2 $p |- ( ( ph /\ ta /\ ch ) -> th ) $=
        ( 3com23 syld3an3 ) ACEDACBDEABCDFHAECBGHIH $.
        $( [24-May-2007] $) $( [20-May-2007] $)
    $}
  $}

  ${
    $v et $. $( Greek eta $)
    $v ze $. $( Greek zeta $)
    $v si $. $( Greek sigma $)
    syl3anl1.we $f wff et $.
    syl3anl1.wz $f wff ze $.
    syl3anl1.ws $f wff si $.
    syl3anl1.1 $e |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ta ) $.
    ${
      syl3anl1.2 $e |- ( et -> ph ) $.
      $( A syllogism inference. $)
      syl3anl1 $p |- ( ( ( et /\ ps /\ ch ) /\ th ) -> ta ) $=
        ( w3a wi ex syl3an1 imp ) FBCIDEABCDEJFABCIDEGKHLM $.
        $( [28-Apr-2005] $) $( [24-Feb-2005] $)
    $}

    ${
      syl3anl2.2 $e |- ( et -> ps ) $.
      $( A syllogism inference. $)
      syl3anl2 $p |- ( ( ( ph /\ et /\ ch ) /\ th ) -> ta ) $=
        ( w3a wi ex syl3an2 imp ) AFCIDEABCDEJFABCIDEGKHLM $.
        $( [26-Feb-2005] $) $( [24-Feb-2005] $)
    $}

    ${
      syl3anl3.2 $e |- ( et -> ch ) $.
      $( A syllogism inference. $)
      syl3anl3 $p |- ( ( ( ph /\ ps /\ et ) /\ th ) -> ta ) $=
        ( w3a wi ex syl3an3 imp ) ABFIDEABCDEJFABCIDEGKHLM $.
        $( [27-Jun-2005] $) $( [24-Feb-2005] $)
    $}

    ${
      syl3anl.2 $e |- ( et -> ph ) $.
      syl3anl.3 $e |- ( ze -> ps ) $.
      syl3anl.4 $e |- ( si -> ch ) $.
      $( A triple syllogism inference. $)
      syl3anl $p |- ( ( ( et /\ ze /\ si ) /\ th ) -> ta ) $=
        ( w3a 3anim123i sylan ) ABCMDEFGHMIFAGBHCJKLNO $.
        $( [24-Dec-2006] $) $( [24-Dec-2006] $)
    $}
  $}

  ${
    $v et $. $( Greek eta $)
    $v ze $. $( Greek zeta $)
    $v si $. $( Greek sigma $)
    syl3anr1.we $f wff et $.
    syl3anr1.1 $e |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> ta ) $.
    ${
      syl3anr1.2 $e |- ( et -> ps ) $.
      $( A syllogism inference. $)
      syl3anr1 $p |- ( ( ph /\ ( et /\ ch /\ th ) ) -> ta ) $=
        ( w3a ancoms syl3anl1 ) FCDIAEBCDAEFABCDIEGJHKJ $.
        $( [16-Aug-2007] $) $( [31-Jul-2007] $)
    $}

    ${
      syl3anr2.2 $e |- ( et -> ch ) $.
      $( A syllogism inference. $)
      syl3anr2 $p |- ( ( ph /\ ( ps /\ et /\ th ) ) -> ta ) $=
        ( w3a ancoms syl3anl2 ) BFDIAEBCDAEFABCDIEGJHKJ $.
        $( [6-Aug-2007] $) $( [1-Aug-2007] $)
    $}

    ${
      syl3anr3.2 $e |- ( et -> th ) $.
      $( A syllogism inference. $)
      syl3anr3 $p |- ( ( ph /\ ( ps /\ ch /\ et ) ) -> ta ) $=
        ( w3a ancoms syl3anl3 ) BCFIAEBCDAEFABCDIEGJHKJ $.
        $( [23-Aug-2007] $) $( [23-Aug-2007] $)
    $}
  $}

  ${
    3impdi.1 $e |- ( ( ( ph /\ ps ) /\ ( ph /\ ch ) ) -> th ) $.
    $( Importation inference (undistribute conjunction). $)
    3impdi $p |- ( ( ph /\ ps /\ ch ) -> th ) $=
      ( anandis 3impb ) ABCDABCDEFG $.
      $( [14-Aug-1995] $)
  $}

  ${
    3impdir.1 $e |- ( ( ( ph /\ ps ) /\ ( ch /\ ps ) ) -> th ) $.
    $( Importation inference (undistribute conjunction). $)
    3impdir $p |- ( ( ph /\ ch /\ ps ) -> th ) $=
      ( anandirs 3impa ) ACBDACBDEFG $.
      $( [20-Aug-1995] $)
  $}

  ${
    3anidm12.1 $e |- ( ( ph /\ ph /\ ps ) -> ch ) $.
    $( Inference from idempotent law for conjunction. $)
    3anidm12 $p |- ( ( ph /\ ps ) -> ch ) $=
      ( wi 3exp pm2.43i imp ) ABCABCEAABCDFGH $.
      $( [7-Mar-2008] $) $( [7-Mar-2008] $)
  $}

  ${
    3anidm13.1 $e |- ( ( ph /\ ps /\ ph ) -> ch ) $.
    $( Inference from idempotent law for conjunction. $)
    3anidm13 $p |- ( ( ph /\ ps ) -> ch ) $=
      ( 3com23 3anidm12 ) ABCABACDEF $.
      $( [10-Mar-2008] $) $( [7-Mar-2008] $)
  $}

  ${
    3anidm23.1 $e |- ( ( ph /\ ps /\ ps ) -> ch ) $.
    $( Inference from idempotent law for conjunction. $)
    3anidm23 $p |- ( ( ph /\ ps ) -> ch ) $=
      ( 3exp pm2.43d imp ) ABCABCABBCDEFG $.
      $( [1-Feb-2007] $) $( [1-Feb-2007] $)
  $}

  ${
    3ori.1 $e |- ( ph \/ ps \/ ch ) $.
    $( Infer implication from triple disjunction. $)
    3ori $p |- ( ( -. ph /\ -. ps ) -> ch ) $=
      ( wn wa wo ioran w3o df-3or mpbi ori sylbir ) AEBEFABGZECABHNCABCINCGDABC
      JKLM $.
      $( [28-Sep-2006] $) $( [26-Sep-2006] $)
  $}

  $( Disjunction of 3 antecedents. $)
  3jao $p |- ( ( ( ph -> ps ) /\ ( ch -> ps ) /\ ( th -> ps ) ) ->
              ( ( ph \/ ch \/ th ) -> ps ) ) $=
    ( wi w3a wo w3o jao syl6 3imp df-3or syl5ib ) ABEZCBEZDBEZFACGZDGZBACDHNOPR
    BEZNOQBEPSEABCIQBDIJKACDLM $.
    $( [8-Apr-1994] $)

  ${
    3jaoi.1 $e |- ( ph -> ps ) $.
    3jaoi.2 $e |- ( ch -> ps ) $.
    3jaoi.3 $e |- ( th -> ps ) $.
    $( Disjunction of 3 antecedents (inference). $)
    3jaoi $p |- ( ( ph \/ ch \/ th ) -> ps ) $=
      ( wi w3a w3o 3pm3.2i 3jao ax-mp ) ABHZCBHZDBHZIACDJBHNOPEFGKABCDLM $.
      $( [12-Sep-1995] $)
  $}

  ${
    3jaod.1 $e |- ( ph -> ( ps -> ch ) ) $.
    3jaod.2 $e |- ( ph -> ( th -> ch ) ) $.
    3jaod.3 $e |- ( ph -> ( ta -> ch ) ) $.
    $( Disjunction of 3 antecedents (deduction). $)
    3jaod $p |- ( ph -> ( ( ps \/ th \/ ta ) -> ch ) ) $=
      ( wi w3o 3jao syl3anc ) BCIDCIECIBDEJCIABCDEKFGHL $.
      $( [16-Oct-2005] $) $( [14-Oct-2005] $)
  $}

  ${
    3jaoian.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    3jaoian.2 $e |- ( ( th /\ ps ) -> ch ) $.
    3jaoian.3 $e |- ( ( ta /\ ps ) -> ch ) $.
    $( Disjunction of 3 antecedents (inference). $)
    3jaoian $p |- ( ( ( ph \/ th \/ ta ) /\ ps ) -> ch ) $=
      ( w3o wi ex 3jaoi imp ) ADEIBCABCJDEABCFKDBCGKEBCHKLM $.
      $( [17-Oct-2005] $) $( [14-Oct-2005] $)
  $}

  ${
    3jaodan.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    3jaodan.2 $e |- ( ( ph /\ th ) -> ch ) $.
    3jaodan.3 $e |- ( ( ph /\ ta ) -> ch ) $.
    $( Disjunction of 3 antecedents (deduction). $)
    3jaodan $p |- ( ( ph /\ ( ps \/ th \/ ta ) ) -> ch ) $=
      ( w3o ex 3jaod imp ) ABDEICABCDEABCFJADCGJAECHJKL $.
      $( [21-Oct-2005] $) $( [14-Oct-2005] $)
  $}

  ${
    $v et $. $( Greek eta $)
    $v ze $. $( Greek zeta $)
    syl3an9b.we $f wff et $.
    syl3an9b.wz $f wff ze $.
    syl3an9b.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    syl3an9b.2 $e |- ( th -> ( ch <-> ta ) ) $.
    syl3an9b.3 $e |- ( et -> ( ta <-> ze ) ) $.
    $( Nested syllogism inference conjoining 3 dissimilar antecedents. $)
    syl3an9b $p |- ( ( ph /\ th /\ et ) -> ( ps <-> ze ) ) $=
      ( wb wa sylan9bb 3impa ) ADFBGKADLBEFGABCDEHIMJMN $.
      $( [1-May-1995] $)
  $}

  ${
    $v et $. $( Greek eta $)
    $v ze $. $( Greek zeta $)
    bi3d.we $f wff et $.
    bi3d.wz $f wff ze $.
    bi3d.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    bi3d.2 $e |- ( ph -> ( th <-> ta ) ) $.
    bi3d.3 $e |- ( ph -> ( et <-> ze ) ) $.
    $( Deduction joining 3 equivalences to form equivalence of disjunctions. $)
    3orbi123d $p |- ( ph -> ( ( ps \/ th \/ et ) <-> ( ch \/ ta \/ ze ) ) ) $=
      ( wo w3o orbi12d df-3or 3bitr4g ) ABDKZFKCEKZGKBDFLCEGLAPQFGABCDEHIMJMBDF
      NCEGNO $.
      $( [20-Apr-1994] $)

    $( Deduction joining 3 equivalences to form equivalence of conjunctions. $)
    3anbi123d $p |- ( ph -> ( ( ps /\ th /\ et ) <-> ( ch /\ ta /\ ze ) ) ) $=
      ( wa w3a anbi12d df-3an 3bitr4g ) ABDKZFKCEKZGKBDFLCEGLAPQFGABCDEHIMJMBDF
      NCEGNO $.
      $( [22-Apr-1994] $)
  $}

  ${
    $v et $. $( Greek eta $)
    3anbi12d.we $f wff et $.
    3anbi12d.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    3anbi12d.2 $e |- ( ph -> ( th <-> ta ) ) $.
    $( Deduction conjoining and adding a conjunct to equivalences. $)
    3anbi12d $p |- ( ph -> ( ( ps /\ th /\ et ) <-> ( ch /\ ta /\ et ) ) ) $=
      ( biidd 3anbi123d ) ABCDEFFGHAFIJ $.
      $( [8-Sep-2006] $) $( [8-Sep-2006] $)

    $( Deduction conjoining and adding a conjunct to equivalences. $)
    3anbi13d $p |- ( ph -> ( ( ps /\ et /\ th ) <-> ( ch /\ et /\ ta ) ) ) $=
      ( biidd 3anbi123d ) ABCFFDEGAFIHJ $.
      $( [9-Sep-2006] $) $( [8-Sep-2006] $)

    $( Deduction conjoining and adding a conjunct to equivalences. $)
    3anbi23d $p |- ( ph -> ( ( et /\ ps /\ th ) <-> ( et /\ ch /\ ta ) ) ) $=
      ( biidd 3anbi123d ) AFFBCDEAFIGHJ $.
      $( [10-Sep-2006] $) $( [8-Sep-2006] $)
  $}

  ${
    3anbi1d.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Deduction adding conjuncts to an equivalence. $)
    3anbi1d $p |- ( ph -> ( ( ps /\ th /\ ta ) <-> ( ch /\ th /\ ta ) ) ) $=
      ( biidd 3anbi12d ) ABCDDEFADGH $.
      $( [9-Sep-2006] $) $( [8-Sep-2006] $)

    $( Deduction adding conjuncts to an equivalence. $)
    3anbi2d $p |- ( ph -> ( ( th /\ ps /\ ta ) <-> ( th /\ ch /\ ta ) ) ) $=
      ( biidd 3anbi12d ) ADDBCEADGFH $.
      $( [2-Nov-2006] $) $( [8-Sep-2006] $)

    $( Deduction adding conjuncts to an equivalence. $)
    3anbi3d $p |- ( ph -> ( ( th /\ ta /\ ps ) <-> ( th /\ ta /\ ch ) ) ) $=
      ( biidd 3anbi13d ) ADDBCEADGFH $.
      $( [11-Sep-2006] $) $( [8-Sep-2006] $)
  $}

  ${
    $v et $. $( Greek eta $)
    $v ze $. $( Greek zeta $)
    3anim123d.we $f wff et $.
    3anim123d.wz $f wff ze $.
    3anim123d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    3anim123d.2 $e |- ( ph -> ( th -> ta ) ) $.
    3anim123d.3 $e |- ( ph -> ( et -> ze ) ) $.
    $( Deduction joining 3 implications to form implication of conjunctions. $)
    3anim123d $p |- ( ph -> ( ( ps /\ th /\ et ) -> ( ch /\ ta /\ ze ) ) ) $=
      ( wa w3a anim12d df-3an 3imtr4g ) ABDKZFKCEKZGKBDFLCEGLAPQFGABCDEHIMJMBDF
      NCEGNO $.
      $( [30-Jun-2005] $) $( [24-Feb-2005] $)

    $( Deduction joining 3 implications to form implication of disjunctions. $)
    3orim123d $p |- ( ph -> ( ( ps \/ th \/ et ) -> ( ch \/ ta \/ ze ) ) ) $=
      ( wo w3o orim12d df-3or 3imtr4g ) ABDKZFKCEKZGKBDFLCEGLAPQFGABCDEHIMJMBDF
      NCEGNO $.
      $( [4-Apr-1997] $)
  $}

  ${
    $v et $. $( Greek eta $)
    an6wet $f wff et $.
    $( Rearrangement of 6 conjuncts. $)
    an6 $p |- ( ( ( ph /\ ps /\ ch ) /\ ( th /\ ta /\ et ) ) <->
              ( ( ph /\ th ) /\ ( ps /\ ta ) /\ ( ch /\ et ) ) ) $=
      ( w3a wa df-3an anbi12i an4 anbi1i 3bitri bitr4i ) ABCGZDEFGZHZADHZBEHZHZ
      CFHZHZRSUAGQABHZCHZDEHZFHZHUCUEHZUAHUBOUDPUFABCIDEFIJUCCUEFKUGTUAABDEKLMR
      SUAIN $.
      $( [13-Mar-1995] $)
  $}

  ${
    mp3an1.1 $e |- ph $.
    mp3an1.2 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
    $( An inference based on modus ponens. $)
    mp3an1 $p |- ( ( ps /\ ch ) -> th ) $=
      ( wa 3expb mpan ) ABCGDEABCDFHI $.
      $( [21-Nov-1994] $)
  $}

  ${
    mp3an2.1 $e |- ps $.
    mp3an2.2 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
    $( An inference based on modus ponens. $)
    mp3an2 $p |- ( ( ph /\ ch ) -> th ) $=
      ( 3expa mpanl2 ) ABCDEABCDFGH $.
      $( [21-Nov-1994] $)
  $}

  ${
    mp3an3.1 $e |- ch $.
    mp3an3.2 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
    $( An inference based on modus ponens. $)
    mp3an3 $p |- ( ( ph /\ ps ) -> th ) $=
      ( wa 3expa mpan2 ) ABGCDEABCDFHI $.
      $( [21-Nov-1994] $)
  $}

  ${
    mp3an12.1 $e |- ph $.
    mp3an12.2 $e |- ps $.
    mp3an12.3 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
    $( An inference based on modus ponens. $)
    mp3an12 $p |- ( ch -> th ) $=
      ( mp3an1 mpan ) BCDFABCDEGHI $.
      $( [15-Jul-2005] $) $( [13-Jul-2005] $)
  $}

  ${
    mp3an13.1 $e |- ph $.
    mp3an13.2 $e |- ch $.
    mp3an13.3 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
    $( An inference based on modus ponens. $)
    mp3an13 $p |- ( ps -> th ) $=
      ( mp3an3 mpan ) ABDEABCDFGHI $.
      $( [16-Jul-2005] $) $( [14-Jul-2005] $)
  $}

  ${
    mp3an23.1 $e |- ps $.
    mp3an23.2 $e |- ch $.
    mp3an23.3 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
    $( An inference based on modus ponens. $)
    mp3an23 $p |- ( ph -> th ) $=
      ( mp3an3 mpan2 ) ABDEABCDFGHI $.
      $( [16-Jul-2005] $) $( [14-Jul-2005] $)
  $}

  ${
    mp3an1i.1 $e |- ps $.
    mp3an1i.2 $e |- ( ph -> ( ( ps /\ ch /\ th ) -> ta ) ) $.
    $( An inference based on modus ponens. $)
    mp3an1i $p |- ( ph -> ( ( ch /\ th ) -> ta ) ) $=
      ( wa wi w3a com12 mp3an1 ) CDHAEBCDAEIFABCDJEGKLK $.
      $( [9-Jul-2005] $) $( [5-Jul-2005] $)
  $}

  ${
    mp3anl1.1 $e |- ph $.
    mp3anl1.2 $e |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ta ) $.
    $( An inference based on modus ponens. $)
    mp3anl1 $p |- ( ( ( ps /\ ch ) /\ th ) -> ta ) $=
      ( wa wi w3a ex mp3an1 imp ) BCHDEABCDEIFABCJDEGKLM $.
      $( [25-Feb-2005] $) $( [24-Feb-2005] $)
  $}

  ${
    mp3anl2.1 $e |- ps $.
    mp3anl2.2 $e |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ta ) $.
    $( An inference based on modus ponens. $)
    mp3anl2 $p |- ( ( ( ph /\ ch ) /\ th ) -> ta ) $=
      ( wa wi w3a ex mp3an2 imp ) ACHDEABCDEIFABCJDEGKLM $.
      $( [26-Feb-2005] $) $( [24-Feb-2005] $)
  $}

  ${
    mp3anl3.1 $e |- ch $.
    mp3anl3.2 $e |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ta ) $.
    $( An inference based on modus ponens. $)
    mp3anl3 $p |- ( ( ( ph /\ ps ) /\ th ) -> ta ) $=
      ( wa wi w3a ex mp3an3 imp ) ABHDEABCDEIFABCJDEGKLM $.
      $( [25-Feb-2005] $) $( [24-Feb-2005] $)
  $}

  ${
    mp3anr1.1 $e |- ps $.
    mp3anr1.2 $e |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> ta ) $.
    $( An inference based on modus ponens. $)
    mp3anr1 $p |- ( ( ph /\ ( ch /\ th ) ) -> ta ) $=
      ( wa w3a ancoms mp3anl1 ) CDHAEBCDAEFABCDIEGJKJ $.
      $( [6-Nov-2006] $) $( [4-Nov-2006] $)
  $}

  ${
    mp3anr2.1 $e |- ch $.
    mp3anr2.2 $e |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> ta ) $.
    $( An inference based on modus ponens. $)
    mp3anr2 $p |- ( ( ph /\ ( ps /\ th ) ) -> ta ) $=
      ( wa w3a ancoms mp3anl2 ) BDHAEBCDAEFABCDIEGJKJ $.
      $( [25-Nov-2006] $) $( [24-Nov-2006] $)
  $}

  ${
    mp3anr3.1 $e |- th $.
    mp3anr3.2 $e |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> ta ) $.
    $( An inference based on modus ponens. $)
    mp3anr3 $p |- ( ( ph /\ ( ps /\ ch ) ) -> ta ) $=
      ( wa w3a ancoms mp3anl3 ) BCHAEBCDAEFABCDIEGJKJ $.
      $( [19-Oct-2007] $) $( [19-Oct-2007] $)
  $}

  ${
    mp3an.1 $e |- ph $.
    mp3an.2 $e |- ps $.
    mp3an.3 $e |- ch $.
    mp3an.4 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
    $( An inference based on modus ponens. $)
    mp3an $p |- th $=
      ( mp3an1 mp2an ) BCDFGABCDEHIJ $.
      $( [14-May-1999] $)
  $}

  ${
    mpd3an3.2 $e |- ( ( ph /\ ps ) -> ch ) $.
    mpd3an3.3 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
    $( An inference based on modus ponens. $)
    mpd3an3 $p |- ( ( ph /\ ps ) -> th ) $=
      ( wa 3expa mpdan ) ABGCDEABCDFHI $.
      $( [12-Nov-2007] $) $( [8-Nov-2007] $)
  $}

  ${
    mpd3an23.1 $e |- ( ph -> ps ) $.
    mpd3an23.2 $e |- ( ph -> ch ) $.
    mpd3an23.3 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
    $( An inference based on modus ponens. $)
    mpd3an23 $p |- ( ph -> th ) $=
      ( id syl3anc ) ABCDAGAHEFI $.
      $( [5-Dec-2006] $) $( [4-Dec-2006] $)
  $}

  ${
    biimp3a.1 $e |- ( ( ph /\ ps ) -> ( ch <-> th ) ) $.
    $( Infer implication from a logical equivalence.  Similar to ~ biimpa . $)
    biimp3a $p |- ( ( ph /\ ps /\ ch ) -> th ) $=
      ( wa biimpa 3impa ) ABCDABFCDEGH $.
      $( [6-Sep-2005] $) $( [4-Sep-2005] $)

    $( Infer implication from a logical equivalence.  Similar to ~ biimpar . $)
    biimp3ar $p |- ( ( ph /\ ps /\ th ) -> ch ) $=
      ( wa biimpar 3impa ) ABDCABFCDEGH $.
      $( [9-Jan-2009] $) $( [2-Jan-2009] $)
  $}

  ${
    3anandis.1 $e |- ( ( ( ph /\ ps ) /\ ( ph /\ ch ) /\ ( ph /\ th ) )
                      -> ta ) $.
    $( Inference that undistributes a triple conjunction in the antecedent. $)
    3anandis $p |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> ta ) $=
      ( wa w3a 3simp1 anim2i 3simp2 3simp3 syl3anc ) ABGACGADGEABCDHZGFNBABCDIJ
      NCABCDKJNDABCDLJM $.
      $( [21-Apr-2007] $) $( [18-Apr-2007] $)
  $}

  ${
    3anandirs.1 $e |- ( ( ( ph /\ th ) /\ ( ps /\ th ) /\ ( ch /\ th ) )
                      -> ta ) $.
    $( Inference that undistributes a triple conjunction in the antecedent. $)
    3anandirs $p |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ta ) $=
      ( wa w3a 3simp1 anim1i 3simp2 3simp3 syl3anc ) ADGBDGCDGEABCHZDGFNADABCIJ
      NBDABCKJNCDABCLJM $.
      $( [18-Apr-2007] $) $( [25-Jul-2006] $)
  $}

  ${
    ecase23d.1 $e |- ( ph -> -. ch ) $.
    ecase23d.2 $e |- ( ph -> -. th ) $.
    ecase23d.3 $e |- ( ph -> ( ps \/ ch \/ th ) ) $.
    $( Deduction for elimination by cases. $)
    ecase23d $p |- ( ph -> ps ) $=
      ( wo wn wa jca ioran sylibr w3o 3orass sylib ord mt3d ) ABCDHZACIZDIZJSIA
      TUAEFKCDLMABSABCDNBSHGBCDOPQR $.
      $( [15-Jul-2005] $) $( [22-Apr-1994] $)
  $}

  ${
    3ecase.1 $e |- ( -. ph -> th ) $.
    3ecase.2 $e |- ( -. ps -> th ) $.
    3ecase.3 $e |- ( -. ch -> th ) $.
    3ecase.4 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
    $( Inference for elimination by cases. $)
    3ecase $p |- th $=
      ( wi 3exp wn a1d pm2.61i pm2.61nii ) BCDABCDIZIABCDHJAKZOBPDCELLMFGN $.
      $( [19-Jul-2005] $) $( [13-Jul-2005] $)
  $}


$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
      Other axiomatizations of classical propositional calculus
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
      Derive the Lukasiewicz axioms from Meredith's sole axiom
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Carew Meredith's sole axiom for propositional calculus.  This amazing
     formula is thought to be the shortest possible single axiom for
     propositional calculus with inference rule ~ ax-mp , where negation and
     implication are primitive.  Here we prove Meredith's axiom from ~ ax-1 ,
     ~ ax-2 , and ~ ax-3 .  Then from it we derive the Lukasiewicz axioms
     ~ luk-1 , ~ luk-2 , and ~ luk-3 .  Using these we finally re-derive our
     axioms as ~ ax1 , ~ ax2 , and ~ ax3 , thus proving the equivalence of
     all three systems.  C. A. Meredith, "Single Axioms for the Systems
     (C,N), (C,O) and (A,N) of the Two-Valued Propositional Calculus," _The
     Journal of Computing Systems_ vol. 1 (1953), pp. 155-164.  Meredith
     claimed to be close to a proof that this axiom is the shortest possible,
     but the proof was apparently never completed.

     An obscure Irish lecturer, Meredith (1904-1976) became enamored with
     logic somewhat late in life after attending talks by Lukasiewicz and
     produced many remarkable results such as this axiom.  From his obituary:
     "He did logic whenever time and opportunity presented themselves, and he
     did it on whatever materials came to hand:  in a pub, his favored pint
     of porter within reach, he would use the inside of cigarette packs to
     write proofs for logical colleagues." $)
  meredith $p |- ( ( ( ( ( ph -> ps ) -> ( -. ch -> -. th ) ) -> ch ) ->
       ta ) -> ( ( ta -> ph ) -> ( th -> ph ) ) ) $=
    ( wi wn ax-3 pm2.21 imim1i com23 syl5 con3d pm2.27 impi com12 imim2d a2d 
    con3 syl6 syl ) ABFZCGZDGZFZFZCFZEFZEGZUCUCAGZUDFZFZGFZGZFZEAFZDAFZFUHUMEUM
    UGEUMULCUFCULHUFUJUCUDUJUBUEABIJKLJMUOUPUKUQUOUJUIFUKUPUOUJUIUDUJUOUIUDFUJU
    NUDUIUNUJUDUCULUKUCUKNOPQPREASLADHTUA $.
    $( [14-Dec-2002] $)

  $( Step 3 of Meredith's proof of Lukasiewicz axioms from his sole axiom.
     (The step numbers refer to Meredith's original paper.) $)
  merlem1 $p |- ( ( ( ch -> ( -. ph -> ps ) ) -> ta ) -> ( ph -> ta ) ) $=
    ( wn wi meredith ax-mp ) DAEZFIBFZEZIFFZJFCJFZFZMDFADFFJDECEFZEKEFZFOFDFLFN
    IBOKDGJPDCLGHDIJAMGH $.
    $( [14-Dec-2002] $)

  $( Step 4 of Meredith's proof of Lukasiewicz axioms from his sole axiom. $)
  merlem2 $p |- ( ( ( ph -> ph ) -> ch ) -> ( th -> ch ) ) $=
    ( wi wn merlem1 meredith ax-mp ) BBDZAECEZDDADAADZDKBDCBDDAJIAFBBACKGH $.
    $( [14-Dec-2002] $)

  $( Step 7 of Meredith's proof of Lukasiewicz axioms from his sole axiom. $)
  merlem3 $p |- ( ( ( ps -> ch ) -> ph ) -> ( ch -> ph ) ) $=
    ( wi wn merlem2 ax-mp meredith ) AADZCEZJDZDZCDBCDZDZMADCADZDOBEZPDDBDZLDZN
    KKDLDRJKIFKLQFGCABBLHGAACCMHG $.
    $( [14-Dec-2002] $)

  $( Step 8 of Meredith's proof of Lukasiewicz axioms from his sole axiom. $)
  merlem4 $p |- ( ta -> ( ( ta -> ph ) -> ( th -> ph ) ) ) $=
    ( wi wn meredith merlem3 ax-mp ) AADBEZIDDBDZCDCADBADDZDCKDAABBCFKJCGH $.
    $( [14-Dec-2002] $)

  $( Step 11 of Meredith's proof of Lukasiewicz axioms from his sole axiom. $)
  merlem5 $p |- ( ( ph -> ps ) -> ( -. -. ph -> ps ) ) $=
    ( wi wn meredith merlem1 merlem4 ax-mp ) BBCZBDZJCCBCBCIICCZABCZADZDZBCCZBB
    BBBEIJNDCCBCZACZOCZKOCZBBBNAEOKDZCMTCCZACQCZRSCUAUBMBLTFAPUAGHOTAKQEHHH $.
    $( [14-Dec-2002] $)

  $( Step 12 of Meredith's proof of Lukasiewicz axioms from his sole axiom. $)
  merlem6 $p |- ( ch -> ( ( ( ps -> ch ) -> ph ) -> ( th -> ph ) ) ) $=
    ( wi merlem4 merlem3 ax-mp ) BCEZIAEDAEEZECJEADIFJBCGH $.
    $( [14-Dec-2002] $)

  $( Between steps 14 and 15 of Meredith's proof of Lukasiewicz axioms from his
     sole axiom. $)
  merlem7 $p |- ( ph -> ( ( ( ps -> ch ) -> th ) -> ( ( ( ch -> ta ) ->
                  ( -. th -> -. ps ) ) -> th ) ) ) $=
    ( wi wn merlem4 merlem6 meredith ax-mp ) BCFZLDFZCEFDGBGFFZDFZFZFZAPFZDNLHP
    AGZFCGZSFFZCFLFZQRFOUAFUBSMOTICEDBUAJKPSCALJKK $.
    $( [22-Dec-2002] $)

  $( Step 15 of Meredith's proof of Lukasiewicz axioms from his sole axiom. $)
  merlem8 $p |- ( ( ( ps -> ch ) -> th ) -> ( ( ( ch -> ta ) ->
                  ( -. th -> -. ps ) ) -> th ) ) $=
    ( wph wi wn meredith merlem7 ax-mp ) EEFZEGZLFFEFEFKKFFZABFCFBDFCGAGFFCFFEE
    EEEHMABCDIJ $.
    $( [22-Dec-2002] $)

  ${
    $v et $. $( Greek eta $)
    meredith.we $f wff et $.
    $( Step 18 of Meredith's proof of Lukasiewicz axioms from his sole
       axiom. $)
    merlem9 $p |- ( ( ( ph -> ps ) -> ( ch -> ( th -> ( ps -> ta ) ) ) ) ->
                    ( et -> ( ch -> ( th -> ( ps -> ta ) ) ) ) ) $=
      ( wi wn merlem6 merlem8 ax-mp meredith ) CDBEGZGZGZFHZGBHZPGGZBGABGZGZSOG
      FOGGMRHDHGZHAHGZGUAGRGZTNRGUCPCNQIDMRUBJKBEUAARLKOPBFSLK $.
      $( [22-Dec-2002] $)
  $}

  $( Step 19 of Meredith's proof of Lukasiewicz axioms from his sole axiom. $)
  merlem10 $p |- ( ( ph -> ( ph -> ps ) ) -> ( th -> ( ph -> ps ) ) ) $=
    ( wi wn meredith merlem9 ax-mp ) AADZAEZJDDADADIIDDZAABDZDZCLDDZAAAAAFLADJC
    EDDADZADNDKNDLAACAFOAMCBKGHH $.
    $( [14-Dec-2002] $)

  $( Step 20 of Meredith's proof of Lukasiewicz axioms from his sole axiom. $)
  merlem11 $p |- ( ( ph -> ( ph -> ps ) ) -> ( ph -> ps ) ) $=
    ( wi wn meredith merlem10 ax-mp ) AACZADZICCACACHHCCZAABCZCZKCZAAAAAELMCJMC
    ABLFLKJFGG $.
    $( [14-Dec-2002] $)

  $( Step 28 of Meredith's proof of Lukasiewicz axioms from his sole axiom. $)
  merlem12 $p |- ( ( ( th -> ( -. -. ch -> ch ) ) -> ph ) -> ph ) $=
    ( wn wi merlem5 merlem2 ax-mp merlem4 merlem11 ) CBDDBEZEZAEZMAEZEZNLOBBEKE
    LBBFBKCGHAMLIHMAJH $.
    $( [14-Dec-2002] $)

  $( Step 35 of Meredith's proof of Lukasiewicz axioms from his sole axiom. $)
  merlem13 $p |- ( ( ph -> ps ) ->
              ( ( ( th -> ( -. -. ch -> ch ) ) -> -. -. ph ) -> ps ) ) $=
    ( wi wn merlem12 merlem5 ax-mp merlem6 meredith merlem11 ) BBEZAFZDCFFCEEZN
    FZEZFZEZEAEZAEZABEQBEETUAEZUASUBOREZREZSRCDGRBEZRFPEZEREUCEZUDSEUFUGQPEUFPC
    DGQPHIRUEUFOJIRBRNUCKIIAMSTJITALIBBAQAKI $.
    $( [14-Dec-2002] $)

  $( 1 of 3 axioms for propositional calculus due to Lukasiewicz, derived from
     Meredith's sole axiom. $)
  luk-1 $p |- ( ( ph -> ps ) -> ( ( ps -> ch ) -> ( ph -> ch ) ) ) $=
    ( wi wn meredith merlem13 ax-mp ) CCDZAEZEZEJDDKDBDZBCDACDDZDZABDZMDZCCKABF
    MADZOEZEZERDDSDLDZNPDOLDTABJIGOLRQGHMASOLFHH $.
    $( [14-Dec-2002] $)

  $( 2 of 3 axioms for propositional calculus due to Lukasiewicz, derived from
     Meredith's sole axiom. $)
  luk-2 $p |- ( ( -. ph -> ph ) -> ph ) $=
    ( wn wi merlem5 merlem4 ax-mp merlem11 meredith ) ABZACZJACZCZKAJBZCIBMCCZI
    CZICZLOPCZPNQAMDIONEFOIGFAMIJIHFJAGF $.
    $( [14-Dec-2002] $)

  $( 3 of 3 axioms for propositional calculus due to Lukasiewicz, derived from
     Meredith's sole axiom. $)
  luk-3 $p |- ( ph -> ( -. ph -> ps ) ) $=
    ( wn wi merlem11 merlem1 ax-mp ) ACZHBDZDIDAIDHBEABHIFG $.
    $( [14-Dec-2002] $)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
      Derive the standard axioms from the Lukasiewicz axioms
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    luklem1.1 $e |- ( ph -> ps ) $.
    luklem1.2 $e |- ( ps -> ch ) $.
    $( Used to rederive standard propositional axioms from Lukasiewicz'. $)
    luklem1 $p |- ( ph -> ch ) $=
      ( wi luk-1 ax-mp ) BCFZACFZEABFIJFDABCGHH $.
      $( [23-Dec-2002] $)
  $}

  $( Used to rederive standard propositional axioms from Lukasiewicz'. $)
  luklem2 $p |- ( ( ph -> -. ps ) ->
                ( ( ( ph -> ch ) -> th ) -> ( ps -> th ) ) ) $=
    ( wn wi luk-1 luk-3 ax-mp luklem1 ) ABEZFZBACFZFZMDFBDFFLKCFZMFZNAKCGBOFPNF
    BCHBOMGIJBMDGJ $.
    $( [22-Dec-2002] $)

  $( Used to rederive standard propositional axioms from Lukasiewicz'. $)
  luklem3 $p |- ( ph -> ( ( ( -. ph -> ps ) -> ch ) -> ( th -> ch ) ) ) $=
    ( wn wi luk-3 luklem2 luklem1 ) AAEZDEZFJBFCFDCFFAKGJDBCHI $.
    $( [22-Dec-2002] $)

  $( Used to rederive standard propositional axioms from Lukasiewicz'. $)
  luklem4 $p |- ( ( ( ( -. ph -> ph ) -> ph ) -> ps ) -> ps ) $=
    ( wn wi luk-2 luklem3 ax-mp luk-1 luklem1 ) ACADADZBDZBCZBDZBLJDZKMDJCJDJDZ
    NJEJONDAEJJJLFGGLJBHGBEI $.
    $( [22-Dec-2002] $)

  $( Used to rederive standard propositional axioms from Lukasiewicz'. $)
  luklem5 $p |- ( ph -> ( ps -> ph ) ) $=
    ( wn wi luklem3 luklem4 luklem1 ) AACADADBADZDHAAABEAHFG $.
    $( [22-Dec-2002] $)

  $( Used to rederive standard propositional axioms from Lukasiewicz'. $)
  luklem6 $p |- ( ( ph -> ( ph -> ps ) ) -> ( ph -> ps ) ) $=
    ( wi luk-1 wn luklem5 luklem2 luklem4 luklem1 ax-mp ) AABCZCKBCZKCZKAKBDKEZ
    KCZKCMKCZCZPMOCZQNLCRNBEZNCZLNSFTSBCBCLCLSKBBGBLHIINLKDJMOKDJKPHJI $.
    $( [22-Dec-2002] $)

  $( Used to rederive standard propositional axioms from Lukasiewicz'. $)
  luklem7 $p |- ( ( ph -> ( ps -> ch ) ) -> ( ps -> ( ph -> ch ) ) ) $=
    ( wi luk-1 luklem5 luklem1 luklem6 ax-mp ) ABCDZDJCDZACDZDZBLDZAJCEBKDMNDBJ
    KDZKBJBDOBJFJBCEGJCHGBKLEIG $.
    $( [22-Dec-2002] $)

  $( Used to rederive standard propositional axioms from Lukasiewicz'. $)
  luklem8 $p |- ( ( ph -> ps ) -> ( ( ch -> ph ) -> ( ch -> ps ) ) ) $=
    ( wi luk-1 luklem7 ax-mp ) CADZABDZCBDZDDIHJDDCABEHIJFG $.
    $( [22-Dec-2002] $)

  $( Standard propositional axiom derived from Lukasiewicz axioms. $)
  ax1 $p |- ( ph -> ( ps -> ph ) ) $=
    ( luklem5 ) ABC $.
    $( [22-Dec-2002] $)

  $( Standard propositional axiom derived from Lukasiewicz axioms. $)
  ax2 $p |- ( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) ) ) $=
    ( wi luklem7 luklem8 luklem6 ax-mp luklem1 ) ABCDDBACDZDZABDZJDZABCEKLAJDZD
    ZMBJAFNJDOMDACGNJLFHII $.
    $( [22-Dec-2002] $)

  $( Standard propositional axiom derived from Lukasiewicz axioms. $)
  ax3 $p |- ( ( -. ph -> -. ps ) -> ( ps -> ph ) ) $=
    ( wn wi luklem2 luklem4 luklem1 ) ACZBCDHADADBADZDIHBAAEAIFG $.
    $( [22-Dec-2002] $)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Logical 'nand' (Sheffer stroke)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c -/\ $. $( 'nand' ) $)
  $( Extend wff definition to include 'nand'. $)
  wnand $a wff ( ph -/\ ps ) $.

  $( Define  incompatibility ('not-and' or 'nand').  This is also called the
     Sheffer stroke, represented by a vertical bar, but we use a different
     symbol to avoid ambiguity with other uses of the vertical bar. $)
  df-nand $a |- ( ( ph -/\ ps ) <-> -. ( ph /\ ps ) ) $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
           Derive Nicod's axiom from the standard axioms
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Lemma for handling nested 'nand's. $)
  nic-justlem $p |- ( ( ph -/\ ( ch -/\ ps ) ) <-> ( ph -> ( ch /\ ps ) ) ) $=
    ( wnand wa wn wi df-nand anbi2i notbii iman 3bitr4i ) ACBDZEZFACBEZFZEZFAMD
    AOGNQMPACBHIJAMHAOKL $.
    $( [11-Dec-2008] $) $( [19-Nov-2007] $)

  $( Show equivalence between implication and the Nicod version.  To derive
     ~ nic-dfim , apply ~ nic-justbi . $)
  nic-justim $p |- ( ( ph -> ps ) <-> ( ph -/\ ( ps -/\ ps ) ) ) $=
    ( wnand wa wi nic-justlem anidmdbi bitr2i ) ABBCCABBDEABEABBFABGH $.
    $( [17-Dec-2008] $) $( [19-Nov-2007] $)

  $( Show equivalence between negation and the Nicod version.  To derive
     ~ nic-dfneg , apply ~ nic-justbi . $)
  nic-justneg $p |- ( -. ps <-> ( ps -/\ ps ) ) $=
    ( wnand wa wn df-nand anidm notbii bitr2i ) AABAACZDADAAEIAAFGH $.
    $( [16-Dec-2008] $) $( [19-Nov-2007] $)

  $( Show equivalence between the bidirectional and the Nicod version.
     (Contributed by Jeff Hoffman, 19-Nov-2007.) $)
  nic-justbi $p |- ( ( ph <-> ps ) <->
          ( ( ph -/\ ps ) -/\ ( ( ph -/\ ph ) -/\ ( ps -/\ ps ) ) ) ) $=
    ( wa wn wo wnand wb pm4.57 df-nand nic-justneg anbi12i notbii bitr4i bitri 
    dfbi3 3bitr4ri ) ABCZDZADZBDZCZDZCZDZQUAEABFZAAFZBBFZFZFZABGQUAHUIUEUHCZDUD
    UEUHIUJUCUERUHUBABIUHUFUGCZDUBUFUGIUAUKSUFTUGAJBJKLMKLNABOP $.
    $( [11-Dec-2008] $) $( [19-Nov-2007] $)

$( [exclude from the Table of Contents by breaking whitespace after "$","("]
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
           Prove Nicod's axiom and implication and negation definitions
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Define implication in terms of 'nand'.  Analogous to
     ` ( ( ph -/\ ( ps -/\ ps ) ) <-> ( ph -> ps ) ) ` .  In a pure
     (standalone) treatment of Nicod's axiom, this theorem would be changed
     to a definition ($a statement). $)
  nic-dfim $p |- ( ( ( ph -/\ ( ps -/\ ps ) ) -/\ ( ph -> ps ) ) -/\
                   ( ( ( ph -/\ ( ps -/\ ps ) ) -/\ ( ph -/\ ( ps -/\ ps ) ) )
                          -/\
                     ( ( ph -> ps ) -/\ ( ph -> ps ) ) ) ) $=
    ( wnand wi wb nic-justim bicomi nic-justbi mpbi ) ABBCCZABDZEJKCJJCKKCCCKJA
    BFGJKHI $.
    $( [11-Dec-2008] $) $( [11-Dec-2008] $)

  $( Define negation in terms of 'nand'.  Analogous to
     ` ( ( ph -/\ ph ) <-> -. ph ) ` .  In a pure (standalone) treatment of
     Nicod's axiom, this theorem would be changed to a definition ($a
     statement). $)
  nic-dfneg $p |- ( ( ( ph -/\ ph ) -/\ -. ph ) -/\
                    ( ( ( ph -/\ ph ) -/\ ( ph -/\ ph ) ) -/\
                      ( -. ph -/\ -. ph ) ) ) $=
    ( wnand wn wb nic-justneg bicomi nic-justbi mpbi ) AABZACZDIJBIIBJJBBBJIAEF
    IJGH $.
    $( [11-Dec-2008] $) $( [11-Dec-2008] $)

  ${
    $( Minor premise. $)
    nic-jmin $e |- ph $.
    $( Major premise. $)
    nic-jmaj $e |- ( ph -/\ ( ch -/\ ps ) ) $.
    $( Derive Nicod's rule of modus ponens using 'nand', from the standard
       one.  Although the major and minor premise together also imply ` ch ` ,
       this form is necessary for useful derivations from ~ nic-ax .  In a
       pure (standalone) treatment of Nicod's axiom, this theorem would be
       changed to an axiom ($a statement).  (Contributed by Jeff Hoffman,
       19-Nov-2007.) $)
    nic-mp $p |- ps $=
      ( wnand wa wi nic-justlem mpbi pm3.27d ax-mp ) ABDACBACBFFACBGHEABCIJKL 
      $.
      $( [11-Dec-2008] $) $( [19-Nov-2007] $)

    $( A direct proof of ~ nic-mp . $)
    nic-mpALT $p |- ps $=
      ( wa wi wn wnand df-nand anbi2i notbii bitri mpbi iman mpbir pm3.27d 
      ax-mp ) ABDACBACBFZGASHZFZHZACBIZIZUBEUDAUCFZHUBAUCJUEUAUCTACBJKLMNASOPQR
      $.
      $( [13-Jan-2009] $) $( [30-Dec-2008] $)
  $}

  $( Nicod's axiom derived from the standard ones.  See _Intro. to Math. Phil._
     by B. Russell, p. 152.  Like ~ meredith , the usual axioms can be derived
     from this and vice versa.  Unlike ~ meredith , Nicod uses a different
     connective ('nand'), so another form of modus ponens must be used in
     proofs, e.g. ` { ` ~ nic-ax , ~ nic-mp  ` } ` is equivalent to
     ` { ` ~ luk-1 , ~ luk-2 , ~ luk-3 , ~ ax-mp ` } ` .  In a pure
     (standalone) treatment of Nicod's axiom, this theorem would be changed
     to an axiom ($a statement).  (Contributed by Jeff Hoffman,
     19-Nov-2007.) $)
  nic-ax $p |- ( ( ph -/\ ( ch -/\ ps ) ) -/\
                   ( ( ta -/\ ( ta -/\ ta ) ) -/\
                     ( ( th -/\ ch ) -/\
                       ( ( ph -/\ th ) -/\ ( ph -/\ th ) ) ) ) ) $=
    ( wnand wa wi nic-justlem biimpi pm3.26 imim2i wn con3 imim2d imnan con2b 
    df-nand 3bitr4ri syl6ibr bitr4i syl5ibr nic-justim sylib 3syl pm4.24 mpbir 
    jctil ) ACBFFZEEEFFZDCFZADFZULFFZFFUIUJUMGHUIUMUJUIACBGZHZACHZUMUIUOABCIJUN
    CACBKLUPUKULHUMUPDCMZHZULUKUPURDAMZHZULUPUQUSDACNOADMHADGMUTULADPDAQADRSTUR
    DCGMUKDCPDCRUAUBUKULUCUDUEUJEEEGZHEVAEUFJEEEIUGUHUIUMUJIUG $.
    $( [11-Dec-2008] $) $( [19-Nov-2007] $)

  $( A direct proof of ~ nic-ax . $)
  nic-axALT $p |- ( ( ph -/\ ( ch -/\ ps ) ) -/\ ( ( ta -/\ ( ta -/\ ta ) )
          -/\ ( ( th -/\ ch ) -/\ ( ( ph -/\ th ) -/\ ( ph -/\ th ) ) ) ) ) $=
    ( wnand wa wn wi pm3.26 imim2i con3 imim2d syl anidm biimpri jctil df-nand 
    anbi2i notbii iman 3bitr4i imnan bitr4i con2b bitr3i 3bitri bitri anbi12i 
    mpbir ) ACBFZFZEEEFZFZDCFZADFZUPFZFZFZFULUSGZHZVAACBGZIZEEEGZIZDCHZIZDAHZIZ
    IZGZIZVCVJVEVCACIZVJVBCACBJKVMVFVHDACLMNVDEEOPQVAVCVKHZGZHVLUTVOULVCUSVNAUK
    GZHAVBHZGZHULVCVPVRUKVQACBRSTAUKRAVBUAUBUSUNURGZHVNUNURRVSVKUNVEURVJEUMGZHE
    VDHZGZHUNVEVTWBUMWAEEERSTEUMREVDUAUBUOUQGZHVGVIHZGZHURVJWCWEUOVGUQWDUODCGHV
    GDCRDCUCUDUQUPUPGZHWDUPUPRWFVIWFUPADGHZVIUPOADRWGADHIVIADUCADUEUFUGTUHUITUO
    UQRVGVIUAUBUITUHUITVCVKUAUDUJULUSRUJ $.
    $( [25-Dec-2008] $) $( [11-Dec-2008] $)



$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
          Derive the Lukasiewicz axioms from Nicod's axiom
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $( Minor premise. $)
    nic-imp.1 $e |- ( ph -/\ ( ch -/\ ps ) ) $.
     $( Inference for ~ nic-mp using ~ nic-ax as major premise.  (Contributed
        by Jeff Hoffman, 17-Nov-2007.)  $)
    nic-imp $p |- ( ( th -/\ ch ) -/\ ( ( ph -/\ th ) -/\ ( ph -/\ th ) ) ) $=
      ( wta wnand nic-ax nic-mp ) ACBGGDCGADGZJGGFFFGGEABCDFHI $.
      $( [11-Dec-2008] $) $( [17-Nov-2007] $)
  $}

  $( Lemma for ~ nic-id . $)
  nic-idlem1 $p |- ( ( th -/\ ( ta -/\ ( ta -/\ ta ) ) ) -/\
                 ( ( ( ph -/\ ( ch -/\ ps ) ) -/\ th ) -/\
                   ( ( ph -/\ ( ch -/\ ps ) ) -/\ th ) ) ) $=
    ( wnand nic-ax nic-imp ) ACBFFACFAAFZIFFEEEFFDABCAEGH $.
    $( [11-Dec-2008] $) $( [17-Nov-2007] $)

  ${
    $v et $. $( Greek eta $)
    nic-idlem2.we $f wff et $.
    nic-idlem2.1 $e |- ( et -/\ ( ( ph -/\ ( ch -/\ ps ) ) -/\ th ) ) $.
     $( Lemma for ~ nic-id .  Inference used by ~ nic-id . $)
    nic-idlem2 $p |- ( ( th -/\ ( ta -/\ ( ta -/\ ta ) ) ) -/\ et ) $=
      ( wnand nic-ax nic-imp nic-mp ) FACBHHZDHZHDEEEHHZHZFHZPGOMMFLACHAAHZQHHN
      DABCAEIJJK $.
      $( [11-Dec-2008] $) $( [17-Nov-2007] $)
  $}

  $( Theorem ~ id expressed with ` -/\ ` .  (Contributed by Jeff Hoffman,
     17-Nov-2007.) $)
  nic-id $p |- ( ta -/\ ( ta -/\ ta ) ) $=
    ( wph wps wch wth wnand nic-ax nic-idlem2 nic-idlem1 nic-mp ) BCFZCBFZLFFZD
    DDFZFZFZCCCFFZFAAAFFZOEEEMDQCCCBEGHMNDPCORFKLLOAIHJ $.
    $( [11-Dec-2008] $) $( [17-Nov-2007] $)

  $( ` -/\ ` is symmetric.  (Contributed by Jeff Hoffman, 17-Nov-2007.)  $)
  nic-swap $p |- ( ( th -/\ ph ) -/\ ( ( ph -/\ th ) -/\ ( ph -/\ th ) ) ) $=
    ( wta wnand nic-id nic-ax nic-mp ) AAADDBADABDZHDDCCCDDAEAAABCFG $.
    $( [11-Dec-2008] $) $( [17-Nov-2007] $)

  ${
    nic-isw1.1 $e |- ( th -/\ ph ) $.
    $( Inference version of ~ nic-swap .  (Contributed by Jeff Hoffman,
       17-Nov-2007.) $)
    nic-isw1 $p |- ( ph -/\ th ) $=
      ( wnand nic-swap nic-mp ) BADABDZGCABEF $.
      $( [11-Dec-2008] $) $( [17-Nov-2007] $)
  $}

  ${
    nic-isw2.1 $e |- ( ps -/\ ( th -/\ ph ) ) $.
    $( Inference for swapping nested terms.  (Contributed by Jeff Hoffman,
       17-Nov-2007.) $)
    nic-isw2 $p |- ( ps -/\ ( ph -/\ th ) ) $=
      ( wnand nic-swap nic-imp nic-mp nic-isw1 ) BACEZBCAEZEJBEZLDJKKBCAFGHI $.
      $( [11-Dec-2008] $) $( [17-Nov-2007] $)
  $}

  ${
    nic-iimp1.1 $e |- ( ph -/\ ( ch -/\ ps ) ) $.
    nic-iimp1.2 $e |- ( th -/\ ch ) $.
    $( Inference version of ~ nic-imp using right-handed term.  (Contributed
       by Jeff Hoffman, 17-Nov-2007.) $)
    nic-iimp1 $p |- ( th -/\ ph ) $=
      ( wnand nic-imp nic-mp nic-isw1 ) DADCGADGZKFABCDEHIJ $.
      $( [11-Dec-2008] $) $( [17-Nov-2007] $)
  $}

  ${
    nic-iimp2.1 $e |- ( ( ph -/\ ps ) -/\ ( ch -/\ ch ) ) $.
    nic-iimp2.2 $e |- ( th -/\ ph ) $.
    $( Inference version of ~ nic-imp using left-handed term.  (Contributed
       by Jeff Hoffman, 17-Nov-2007.) $)
    nic-iimp2 $p |- ( th -/\ ( ch -/\ ch ) ) $=
      ( wnand nic-isw1 nic-iimp1 ) CCGZBADJABGEHFI $.
      $( [11-Dec-2008] $) $( [17-Nov-2007] $)
  $}

  ${
    nic-idel.1 $e |- ( ph -/\ ( ch -/\ ps ) ) $.
    $( Inference to remove the trailing term.  (Contributed by Jeff Hoffman,
       17-Nov-2007.) $)
    nic-idel $p |- ( ph -/\ ( ch -/\ ch ) ) $=
      ( wnand nic-id nic-isw1 nic-imp nic-mp ) CCEZCEAJEZKJCCFGABCJDHI $.
      $( [11-Dec-2008] $) $( [17-Nov-2007] $)
  $}

  ${
    nic-ich.1 $e |- ( ph -/\ ( ps -/\ ps ) ) $.
    nic-ich.2 $e |- ( ps -/\ ( ch -/\ ch ) ) $.
    $( Chained inference.  (Contributed by Jeff Hoffman, 17-Nov-2007.) $)
    nic-ich $p |- ( ph -/\ ( ch -/\ ch ) ) $=
      ( wnand nic-isw1 nic-imp nic-mp ) CCFZBFAJFZKJBEGABBJDHI $.
      $( [11-Dec-2008] $) $( [17-Nov-2007] $)
  $}

  ${
    nic-idbl.1 $e |- ( ph -/\ ( ps -/\ ps ) ) $.
    $( Double the terms.  Since doubling is the same as negation,
       this can be viewed as a contraposition Inference.  (Contributed
       by Jeff Hoffman, 17-Nov-2007.) $)
    nic-idbl $p |- ( ( ps -/\ ps ) -/\ ( ( ph -/\ ph ) -/\ ( ph -/\ ph ) ) ) $=
      ( wnand nic-imp nic-ich ) BBDABDAADABBBCEABBACEF $.
      $( [11-Dec-2008] $) $( [17-Nov-2007] $)
  $}

$( (not in Table of Contents)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Biconditional justification from Nicod's axiom
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( For nic-* definitions, the biconditional connective is not used.  Instead,
     definitions are made based on this form.  ~ nic-bi1 and ~ nic-bi2 are
     used to convert the definitions into usable theorems about one side of the
     implication.  (Contributed by Jeff Hoffman, 18-Nov-2007.)  $)
  nic-bijust $p |- ( ( ta -/\ ta ) -/\ ( ( ta -/\ ta ) -/\ ( ta -/\ ta ) ) ) $=
    ( wnand nic-id ) AABC $.
    $( [11-Dec-2008] $) $( [18-Nov-2007] $)

  ${
    $( 'Biconditional' premise.  (Contributed by Jeff Hoffman, 18-Nov-2007.) $)
    nic-bi1.1 $e |- ( ( ph -/\ ps ) -/\ ( ( ph -/\ ph )
         -/\ ( ps -/\ ps ) ) ) $.
    $( Inference to extract one side of an implication from a definition $)
    nic-bi1 $p |- ( ph -/\ ( ps -/\ ps ) ) $=
      ( wnand nic-id nic-iimp1 nic-isw2 nic-idel ) AABBAAABDBBDAADACAEFGH $.
      $( [11-Dec-2008] $) $( [18-Nov-2007] $)
  $}

  ${
    $( 'Biconditional' premise.  (Contributed by Jeff Hoffman, 18-Nov-2007.) $)
    nic-bi2.1 $e |- ( ( ph -/\ ps ) -/\ ( ( ph -/\ ph )
         -/\ ( ps -/\ ps ) ) ) $.
    $( Inference to extract the other side of an implication from a
        'biconditional' definition. $)
    nic-bi2 $p |- ( ps -/\ ( ph -/\ ph ) ) $=
      ( wnand nic-isw2 nic-id nic-iimp1 nic-idel ) BBAABDZAADZBBDZBKIJCEBFGH $.
      $( [11-Dec-2008] $) $( [18-Nov-2007] $)
  $}

$( (not in Table of Contents)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
             Prove the Lukasiewicz axioms from Nicod's axiom
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $( Minor premise. $)
    nic-smin $e |- ph $.
    $( Major premise. $)
    nic-smaj $e |- ( ph -> ps ) $.
    $( Derive the standard modus ponens from ~ nic-mp .  (Contributed by Jeff
       Hoffman, 18-Nov-2007.) $)
    nic-stdmp $p |- ps $=
      ( wi wnand nic-dfim nic-bi2 nic-mp ) ABBCABEZABBFFZKDKJABGHII $.
      $( [11-Dec-2008] $) $( [18-Nov-2007] $)
  $}

  $( Proof of ~ luk-1 from ~ nic-ax and ~ nic-mp (and definitions
     ~ nic-dfim and ~ nic-dfneg ).  Note that the standard axioms ~ ax-1 ,
     ~ ax-2 , and ~ ax-3 are proved from the Lukasiewicz axioms by theorems
     ~ ax1 , ~ ax2 , and ~ ax3 .  (Contributed by Jeff Hoffman,
     18-Nov-2007.) $)
  nic-luk1 $p |- ( ( ph -> ps ) -> ( ( ps -> ch ) -> ( ph -> ch ) ) ) $=
    ( wta wi wnand nic-dfim nic-bi2 nic-ax nic-isw2 nic-idel nic-bi1 nic-idbl 
    nic-imp nic-swap nic-ich nic-mp ) ABEZBCEZACEZEZUAFFZRUAEZUCRABBFFZUAUDRABG
    HUDSTTFZFZUAUDCCFZBFZAUGFZUIFZFZUFUDDDDFFZUKUKUDULABBUGDIJKUKUEUHFUFUEUJUJU
    HUITUITACGLMNSUHUHUESBUGFZUHUMSBCGHUGBOPNPPUFUASTGLPPUBUCRUAGLQ $.
    $( [11-Dec-2008] $) $( [18-Nov-2007] $)

  $( Proof of ~ luk-2 from ~ nic-ax and ~ nic-mp .  (Contributed by Jeff
     Hoffman, 18-Nov-2007.) $)
  nic-luk2 $p |- ( ( -. ph ->  ph ) -> ph ) $=
    ( wn wi wnand nic-dfim nic-bi2 nic-dfneg nic-id nic-iimp1 nic-isw2 
    nic-isw1 nic-bi1 nic-mp ) ABZACZAADZDZOACZROPONPDZSPSONAEFNPPPNDNNDPPDPAGPH
    IJIKQROAELM $.
    $( [11-Dec-2008] $) $( [18-Nov-2007] $)

  $( Proof of ~ luk-3 from ~ nic-ax and ~ nic-mp .  (Contributed by Jeff
     Hoffman, 18-Nov-2007.) $)
  nic-luk3 $p |- ( ph -> ( -. ph -> ps ) ) $=
    ( wn wi wnand nic-dfim nic-bi1 nic-dfneg nic-bi2 nic-id nic-iimp1 
    nic-iimp2 nic-mp ) AACZBDZOEEZAODZQNBBEZOANREONBFGNAAEZSASNAHIAJKLPQAOFGM 
    $.
    $( [11-Dec-2008] $) $( [18-Nov-2007] $)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
             Spartan set theory 
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


vx $f set x $.
vy $f set y $.
vz $f set z $.
vw $f set w $.
vv $f set v $.
vu $f set u $.
vt $f set t $.

wal $a wff A. x ph $.
wex $a wff E. x ph $.
weq $a wff x = y $.
wel $a wff x e. y $.

ax-467 $a |- ( ( A. x A. y -. A. x A. y ph -> A. x ph ) -> ph ) $.
ax-5 $a |- ( A. x ( A. x ph -> ps ) -> ( A. x ph -> A. x ps ) ) $.
ax-8 $a |- ( x = y -> ( x = z -> y = z ) ) $.
ax-9 $a |- -. A. x -. x = y $.
ax-10 $a |- ( A. x x = y -> ( A. x ph -> A. y ph ) ) $.
ax-12 $a |- ( -. A. z z = x -> ( -. A. z z = y ->
            ( x = y -> A. z x = y ) ) ) $.
ax-13 $a |- ( x = y -> ( x e. z -> y e. z ) ) $.
ax-14 $a |- ( x = y -> ( z e. x -> z e. y ) ) $.
ax-15 $a |- ( -. A. z z = x -> ( -. A. z z = y ->
            ( x e. y -> A. z x e. y ) ) ) $.
ax-ext $a |- -. A. x -. ( ( x e. y -> x e. z ) -> 
  	     ( ( x e. z -> x e. y ) -> y = z ) ) $.
ax-rep $a |- -. A. x -. ( -. A. y -. A. z ( ph -> z = y ) -> 
  	     A. z -. ( ( A. y z e. x -> -. A. x ( A. z x e. y -> 
	     -. A. y ph ) ) -> -. ( -. A. x ( A. z x e. y -> -. A. y ph ) 
	     -> A. y z e. x ) ) ) $.
ax-un $a  |- -. A. x -. A. y ( -. A. x ( y e. x -> -. x e. z ) 
  	     -> y e. x ) $.
ax-pow $a |- ( A. x -. A. y ( A. x ( -. A. z -. x e. y -> A. y x e. z ) 
  	     -> y e. x ) -> x = y ) $.
ax-reg $a |- ( x e. y -> 
  	     -. A. x ( x e. y -> -. A. z ( z e. x -> -. z e. y ) ) ) $.
ax-inf $a |- -. A. x -. ( y e. z -> -. ( y e. x -> 
  	     -. A. y ( y e. x -> -. A. z ( y e. z -> -. z e. x ) ) ) ) $.
ax-ac  $a |- -. A. x -. A. y A. z ( A. x -. ( y e. z -> -. z e. w ) -> 
  	       	  -. A. w -. A. y -. ( ( -. A. w ( y e. z -> ( z e. w -> 
		  ( y e. w -> -. w e. x ) ) ) -> y = w ) -> -. ( y = w -> 
		  -. A. w ( y e. z -> ( z e. w -> ( y e. w -> -. w e. x ) 
		  ) ) ) ) ) $.
${ $d x y $.
   ax-two $a |- -. A. x x = y $.
$}

${
  ax-gen.1 $e |- ph $.

  ax-gen $a |- A. x ph $.
$}

df-ex $a |- ( E. x ph <-> -. A. x -. ph ) $.


${ $d x z $. $d y z $.
   ax17eq $p |- ( x = y -> A. z x = y ) $=
     ( weq wal wn wi ax-two ax-12 mp2 ) CADCEFCBDCEFABDZKCEGCAHCBHABCIJ $.
     $( [?] $) $( [15-Nov-2010] $)
   
   ax17el $p |- ( x e. y -> A. z x e. y ) $=
     ( weq wal wn wel wi ax-two ax-15 mp2 ) CADCEFCBDCEFABGZLCEHCAICBIABCJK $.
     $( [?] $) $( [15-Nov-2010] $)
$}

${ $d x y $.
   ax16 $p |- ( A. x x = y -> ( ph -> A. x ph ) ) $=
     ( weq wal wn wi ax-two pm2.21 ax-mp ) BCDBEZFKAABEGZGBCHKLIJ $.
     $( [?] $) $( [15-Nov-2010] $)
$}

ax-4 $p |- ( A. x ph -> ph ) $=
  ( wal wn wi ax-1 ax-467 syl ) ABCZIBCDBCBCZIEAIJFABBGH $.
  $( [?] $) $( [15-Nov-2010] $)

${
   mpg.1 $e |- ( A. x ph -> ps ) $.
   mpg.2 $e |- ph $.

   mpg $p |- ps $=
     ( wal ax-gen ax-mp ) ACFBACEGDH $.
     $( [?] $) $( [15-Nov-2010] $)
$}

${
   a4s.1 $e |- ( ph -> ps ) $.
   a4s $p |- ( A. x ph -> ps ) $=
     ( wal ax-4 syl ) ACEABACFDG $.
     $( [?] $) $( [15-Nov-2010] $)
$}

${ 
   19.20i.1 $e |- ( ph -> ps ) $.
   19.20i $p |- ( A. x ph -> A. x ps ) $=
     ( wal wi ax-5 a4s mpg ) ACEZBFJBCEFCABCGABCDHI $.
     $( [?] $) $( [15-Nov-2010] $)
$}

hba1 $p |- ( A. x ph -> A. x A. x ph ) $=
  ( wal wi ax-5 id mpg ) ABCZHDHHBCDBAHBEHFG $.

ax-6 $p |- ( -. A. x -. A. x ph -> ph ) $=
  ( wal wn wi ax-4 hba1 con3 ax-mp 19.20i syl pm2.21 ax-467 ) ABCZDZBCZDZNBCZDZ
  BCZBCZNEZAQUADZUBUAPEQUCEUATPTBFSOBNRESOEABGNRHIJKUAPHIUANLKABBMK $.

ax-7 $p |- ( A. x A. y ph -> A. y A. x ph ) $=
  ( wal wn wi ax-6 ax-3 ax-mp con1 pm2.21 ax-467 syl 19.20i ) ACDBDZOEZCDZEZCDZ
  ABDZCDSEPFOSFPCGSOHIRTCRQBDZEZBDZTUCEQFRUCFQBGUCQJIUBABUBUATFAUATKABCLMNMNM 
  $.

hbalt $p |- ( A. x ( ph -> A. y ps ) -> ( A. x ph -> A. y A. x ps ) ) $=
  ( wal wi ax-4 imim1i 19.20i ax-5 syl ax-7 syl6 ) ABDEZFZCEZACEZNCEZBCEDEPQNFZ
  CEQRFOSCQANACGHIANCJKBCDLM $.
  $( [?] $) $( [28-Oct-2010] $)

hbnt $p |- ( A. x ( ph -> A. x ps ) -> ( -. ps -> A. x -. ph ) ) $=
  ( wal wi wn con3 ax-4 syl5 19.20i ax-5 syl ax-6 con1i ) ABCDZEZCDZOFZCDZAFZCD
  ZBFQSTEZCDSUAEPUBCPRTSAOGRCHIJRTCKLSBBCMNI $.
  $( [?] $) $( [15-Nov-2010] $)

hbimt $p |- ( A. x ( ph -> A. x ps ) -> ( ( ch -> A. x th ) -> ( ( ps -> ch ) -> A. x ( ph -> th ) ) ) ) $=
  ( wal wi wn ax-4 pm2.21 syl9r 19.20i ax-5 syl ax-6 nsyl4 com12 ax-1 imim2i 
  imim2d pm2.61 syl6 com3r ) ABEFZGZEFZBHZADGZEFZGZCDEFZGZBCGZUIGGUGUFUIUDHZEFZ
  UFUIGZBUOUFUHGZEFUPUNUQEUFAUDUNDUEEIUDDJKLUEUHEMNBEOPQULUMUJUIULUMBUIGUJUIGUL
  CUIBUKUICDUHEDARLSTBUIUAUBUCN $.
  $( [?] $) $( [28-Oct-2010] $)

${
   hbn.1 $e |- ( ph -> A. x ps ) $.

   hbn $p |- ( -. ps -> A. x -. ph ) $=
     ( wal wi wn hbnt mpg ) ABCEFBGAGCEFCABCHDI $.
     $( [?] $) $( [15-Nov-2010] $)
$}

${
   hbim.1 $e |- ( ph -> A. x ps ) $.
   hbim.2 $e |- ( ch -> A. x th ) $.

   hbim $p |- ( ( ps -> ch ) -> A. x ( ph -> th ) ) $=
     ( wal wi hbimt mpg ax-mp ) CDEHIZBCIADIEHIZGABEHIMNIEABCDEJFKL $.
     $( [?] $) $( [15-Nov-2010] $)
$}

19.9t $p |- ( A. x ( ph -> A. x ps ) -> ( E. x ph -> ps ) ) $=
  ( wal wi wn wex hbnt con1d df-ex syl5ib ) ABCDECDZAFCDZFBACGLBMABCHIACJK $.
  $( [?] $) $( [15-Nov-2010] $)

19.8a $p |- ( ph -> E. x ph ) $=
  ( wn wal wex ax-4 con2i df-ex sylibr ) AACZBDZCABEKAJBFGABHI $.
  $( [?] $) $( [15-Nov-2010] $)

${
   19.9.1 $e |- ( ph -> A. x ph ) $.

   19.9 $p |- ( E. x ph <-> ph ) $=
     ( wex wal wi 19.9t mpg 19.8a impbii ) ABDZAAABEFKAFBAABGCHABIJ $.
     $( [?] $) $( [15-Nov-2010] $)
$}

19.20 $p |- ( A. x ( ph -> ps ) -> ( A. x ph -> A. x ps ) ) $=
  ( wi wal ax-4 imim1i 19.20i ax-5 syl ) ABDZCEACEZBDZCELBCEDKMCLABACFGHABCIJ 
  $.
  $( [?] $) $( [15-Nov-2010] $)

${
   19.20ii.1 $e |- ( ph -> ( ps -> ch ) ) $.

   19.20ii $p |- ( A. x ph -> ( A. x ps -> A. x ch ) ) $=
     ( wal wi 19.20i 19.20 syl ) ADFBCGZDFBDFCDFGAKDEHBCDIJ $.
     $( [?] $) $( [15-Nov-2010] $)
$}

19.26 $p |- ( A. x ( ph /\ ps ) <-> ( A. x ph /\ A. x ps ) ) $=
  ( wa wal pm3.26 19.20i pm3.27 jca pm3.2 19.20ii imp impbii ) ABDZCEZACEZBCEZD
  OPQNACABFGNBCABHGIPQOABNCABJKLM $.
  $( [?] $) $( [15-Nov-2010] $)

${
   hban.1 $e |- ( ph -> A. x ps ) $.
   hban.2 $e |- ( ch -> A. x th ) $.

   hban $p |- ( ( ph /\ ch ) -> A. x ( ps /\ th ) ) $=
     ( wa wal anim12i 19.26 sylibr ) ACHBEIZDEIZHBDHEIAMCNFGJBDEKL $.
     $( [?] $) $( [15-Nov-2010] $)
$}

${
  albii.1 $e |- ( ph <-> ps ) $.

  albii $p |- ( A. x ph <-> A. x ps ) $=
    ( wal biimpi 19.20i biimpri impbii ) ACEBCEABCABDFGBACABDHGI $.
    $( [?] $) $( [15-Nov-2010] $)
$}

19.35 $p |- ( E. x ( ph -> ps ) <-> ( A. x ph -> E. x ps ) ) $=
  ( wal wn wi wex wa 19.26 annim albii df-an 3bitr3i con2bii df-ex imbi2i 
  3bitr4ri ) ACDZBEZCDZEZFZABFZEZCDZERBCGZFUCCGUEUBASHZCDRTHUEUBEASCIUGUDCABJKR
  TLMNUFUARBCOPUCCOQ $.
  $( [?] $) $( [15-Nov-2010] $)

${
   exbii.1 $e |- ( ph <-> ps ) $.

   exbii $p |- ( E. x ph <-> E. x ps ) $=
     ( wn wal wex notbii albii df-ex 3bitr4i ) AEZCFZEBEZCFZEACGBCGMOLNCABDHIHA
     CJBCJK $.
     $( [?] $) $( [15-Nov-2010] $)
$}

alex $p |- ( A. x ph <-> -. E. x -. ph ) $=
  ( wal wn wex notnot albii df-ex con2bii bitri ) ABCADZDZBCZKBEZDALBAFGNMKBHIJ
  $.
  $( [?] $) $( [15-Nov-2010] $)

exnal $p |- ( E. x -. ph <-> -. A. x ph ) $=
  ( wal wn wex alex con2bii ) ABCADBEABFG $.
  $( [?] $) $( [15-Nov-2010] $)

hbn1 $p |- ( -. A. x ph -> A. x -. A. x ph ) $=
  ( wal hba1 hbn ) ABCZFBABDE $.
  $( [?] $) $( [15-Nov-2010] $)

hbe1 $p |- ( E. x ph -> A. x E. x ph ) $=
  ( wn wal wex hbn1 df-ex albii 3imtr4i ) ACZBDCZKBDABEZLBDJBFABGZLKBMHI $.
  $( [?] $) $( [15-Nov-2010] $)

19.22 $p |- ( A. x ( ph -> ps ) -> ( E. x ph -> E. x ps ) ) $=
  ( wi wal wn wex con3 19.20ii con3d df-ex 3imtr4g ) ABDZCEZAFZCEZFBFZCEZFACGBC
  GNRPMQOCABHIJACKBCKL $.
  $( [?] $) $( [15-Nov-2010] $)

${
  19.22i.1 $e |- ( ph -> ps ) $.

  19.22i $p |- ( E. x ph -> E. x ps ) $=
    ( wi wex 19.22 mpg ) ABEACFBCFECABCGDH $.
    $( [?] $) $( [15-Nov-2010] $)
$}

${ 
   19.23ai.1 $e |- ( ps -> A. x ps ) $.
   19.23ai.2 $e |- ( ph -> ps ) $.

   19.23ai $p |- ( E. x ph -> ps ) $=
     ( wex 19.22i 19.9 sylib ) ACFBCFBABCEGBCDHI $.
     $( [?] $) $( [15-Nov-2010] $)
$}


${
   a7s.1 $e |- ( A. x A. y ph -> ps ) $.
   a7s $p |- ( A. y A. x ph -> ps ) $=
     ( wal ax-7 syl ) ACFDFADFCFBADCGEH $.
     $( [?] $) $( [15-Nov-2010] $)
$}

${
   19.21ai.1 $e |- ( ph -> A. x ph ) $.
   19.21ai.2 $e |- ( ph -> ps ) $.

   19.21ai $p |- ( ph -> A. x ps ) $=
     ( wal 19.20i syl ) AACFBCFDABCEGH $.
     $( [?] $) $( [15-Nov-2010] $)
$}

stdpc6 $p |- A. x x = x $=
  ( weq wal wn ax-9 hbn1 wi ax-12 pm2.43i con3d 19.21ai mt3 ) AABZACZMDZACAAEND
  ZOAMAFPOPMNPMNGAAAHIJIKL $.
  $( [?] $) $( [15-Nov-2010] $)

equid $p |- x = x $=
  ( weq wal stdpc6 ax-4 ax-mp ) AABZACGADGAEF $.
  $( [?] $) $( [15-Nov-2010] $)

equcomi $p |- ( x = y -> y = x ) $=
  ( weq equid ax-8 mpi ) ABCAACBACADABAEF $.
  $( [?] $) $( [15-Nov-2010] $)

${
   equcoms.1 $e |- ( x = y -> ph ) $.

   equcoms $p |- ( y = x -> ph ) $=
     ( weq equcomi syl ) CBEBCEACBFDG $.
     $( [?] $) $( [15-Nov-2010] $)
$}

equcom $p |- ( x = y <-> y = x ) $=
  ( weq equcomi impbii ) ABCBACABDBADE $.
  $( [?] $) $( [15-Nov-2010] $)

elequ1 $p |- ( x = y -> ( x e. z <-> y e. z ) ) $=
  ( weq wel ax-13 wi equcoms impbid ) ABDACEZBCEZABCFKJGBABACFHI $.
  $( [?] $) $( [15-Nov-2010] $)

elequ2 $p |- ( x = y -> ( z e. x <-> z e. y ) ) $=
  ( weq wel ax-14 wi equcoms impbid ) ABDCAEZCBEZABCFKJGBABACFHI $.
  $( [?] $) $( [15-Nov-2010] $)

equequ1 $p |- ( x = y -> ( x = z <-> y = z ) ) $=
  ( weq ax-8 wi equcoms impbid ) ABDACDZBCDZABCEJIFBABACEGH $.
  $( [?] $) $( [6-Dec-2010] $)

equequ2 $p |- ( x = y -> ( z = x <-> z = y ) ) $=
  ( weq equequ1 equcom 3bitr4g ) ABDACDBCDCADCBDABCECAFCBFG $.
  $( [?] $) $( [6-Dec-2010] $)

${
   cbv1.1 $e |- ( ph -> ( ps -> A. y ps ) ) $.
   cbv1.2 $e |- ( ph -> ( ch -> A. x ch ) ) $.
   cbv1.3 $e |- ( ph -> ( x = y -> ( ps -> ch ) ) ) $.

   cbv1 $p |- ( A. x A. y ph -> ( A. x ps -> A. y ch ) ) $=
     ( wal wi a4s 19.20ii ax-7 syl6 weq com23 syl6d wn ax-9 con3 19.20i 19.20 
     syl con3d mpi ax-6 a7s syld ) AEIZDIZBDIZUKEIZCEIZUJUKBEIZDIULUIBUNDABUNJE
     FKLBDEMNAULUMJEDADIZUKCEUOUKDEOZCDIZJZDIZCABURDABUPCUQAUPBCHPGQLUSUQRZDIZR
     ZCUSUPRZDIZRVBDESUSVAVDUSUTVCJZDIVAVDJURVEDUPUQTUAUTVCDUBUCUDUECDUFUCNLUGU
     H $.
     $( [?] $) $( [15-Nov-2010] $)
$}

${
   cbv2.1 $e |- ( ph -> ( ps -> A. y ps ) ) $.
   cbv2.2 $e |- ( ph -> ( ch -> A. x ch ) ) $.
   cbv2.3 $e |- ( ph -> ( x = y -> ( ps <-> ch ) ) ) $.

   cbv2 $p |- ( A. x A. y ph -> ( A. x ps <-> A. y ch ) ) $=
     ( wal weq wb wi bi1 syl6 cbv1 bi2 equcomi syl5 a7s impbid ) AEIDIBDIZCEIZA
     BCDEFGADEJZBCKZBCLHBCMNOAUBUALEDACBEDGFAUCCBLZEDJAUCUDUEHBCPNEDQROST $.
     $( [?] $) $( [15-Nov-2010] $)
$}

${
   cbval.1 $e |- ( ph -> A. y ph ) $.
   cbval.2 $e |- ( ps -> A. x ps ) $.
   cbval.3 $e |- ( x = y -> ( ph <-> ps ) ) $.

   cbval $p |- ( A. x ph <-> A. y ps ) $=
     ( wi wal wb a1i weq cbv2 id ax-gen mpg ) AAHZDIACIBDIJCQABCDAADIHQEKBBCIHQ
     FKCDLABJHQGKMQDANOP $.
     $( [?] $) $( [15-Nov-2010] $)

   cbvex $p |- ( E. x ph <-> E. y ps ) $=
     ( wn wal wex hbn weq notbid cbval notbii df-ex 3bitr4i ) AHZCIZHBHZDIZHACJ
     BDJSUARTCDAADEKBBCFKCDLABGMNOACPBDPQ $.
     $( [?] $) $( [15-Nov-2010] $)
$}


${
   hbal.1 $e |- ( ph -> A. x ps ) $.


   hbal $p |- ( A. y ph -> A. x A. y ps ) $=
     ( wal 19.20i ax-7 syl ) ADFBCFZDFBDFCFAJDEGBDCHI $.
     $( [?] $) $( [18-Nov-2010] $)
   hbex $p |- ( E. y ph -> A. x E. y ps ) $=
     ( wn wal wex hbn hbal df-ex albii 3imtr4i ) AFZDGZFBFZDGZFZCGADHBDHZCGQOCP
     NCDABCEIJIADKSRCBDKLM $.
     $( [?] $) $( [18-Nov-2010] $)
$}

19.15 $p |- ( A. x ( ps <-> ch ) -> ( A. x ps <-> A. x ch ) ) $=
  ( wb wal bi1 19.20ii bi2 impbid ) ABDZCEACEBCEJABCABFGJBACABHGI $.
  $( [?] $) $( [6-Dec-2010] $)

${
   albid.1 $e |- ( ph -> A. x ph ) $.
   albid.2 $e |- ( ph -> ( ps <-> ch ) ) $.

   albid $p |- ( ph -> ( A. x ps <-> A. x ch ) ) $=
     ( wb wal 19.21ai 19.15 syl ) ABCGZDHBDHCDHGALDEFIBCDJK $.
     $( [?] $) $( [6-Dec-2010] $)
$}

19.3 $p |- ( A. x A. x ph <-> A. x ph ) $=
  ( wal ax-4 hba1 impbii ) ABCZBCGGBDABEF $.
  $( [?] $) $( [6-Dec-2010] $)

${
   hbdf.1 $e |- ( ph -> A. x ph ) $.
   hbdf.2 $e |- ( ps -> A. x ps ) $.

   hbor $p |- ( ( ph \/ ps ) -> A. x ( ph \/ ps ) ) $=
     ( wn wi wal wo hbn hbim df-or albii 3imtr4i ) AFZBGZPCHABIZQCHOOBBCAACDJEK
     ABLZQPCRMN $.
     $( [?] $) $( [6-Dec-2010] $)
   hbbi $p |- ( ( ph <-> ps ) -> A. x ( ph <-> ps ) ) $=
     ( wi wa wal wb hbim hban dfbi2 albii 3imtr4i ) ABFZBAFZGZQCHABIZRCHOOPPCAA
     BBCDEJBBAACEDJKABLZRQCSMN $.
     $( [?] $) $( [6-Dec-2010] $)
$}


${
   19.35i.1 $e |- E. x ( ph -> ps ) $.

   19.35i $p |- ( A. x ph -> E. x ps ) $=
     ( wi wex wal 19.35 mpbi ) ABECFACGBCFEDABCHI $.
     $( [?] $) $( [6-Dec-2010] $)
$}

ax9o $p |- ( A. x ( x = y -> A. x ph ) -> ph ) $=
  ( weq wal wi wex wn ax-9 df-ex mpbir 19.22 mpi biimpi ax-6 3syl ) BCDZABEZFBE
  ZRBGZRHBEHZASQBGZTUBQHBEHBCIQBJKQRBLMTUARBJNABOP $.
  $( [?] $) $( [6-Dec-2010] $)

${
   a4im.1 $e |- ( ps -> A. x ps ) $.
   a4im.2 $e |- ( x = y -> ( ph -> ps ) ) $.

   a4im $p |- ( A. x ph -> ps ) $=
     ( wal weq wi syl6com 19.20i ax9o syl ) ACGCDHZBCGZIZCGBAPCNABOFEJKBCDLM $.
     $( [?] $) $( [6-Dec-2010] $)
$}

${
   chv2.1 $e |- ( ps -> A. x ps ) $.
   chv2.2 $e |- ( x = y -> ( ph <-> ps ) ) $.
   chv2.3 $e |- ph $.

   chvar $p |- ps $=
     ( weq biimpd a4im mpg ) ABCABCDECDHABFIJGK $.
     $( [?] $) $( [6-Dec-2010] $)
$}

${
   exbid.1 $e |- ( ph -> A. x ph ) $.
   exbid.2 $e |- ( ph -> ( ps <-> ch ) ) $.
   
   exbid $p |- ( ph -> ( E. x ps <-> E. x ch ) ) $=
     ( wn wal wex notbid albid df-ex 3bitr4g ) ABGZDHZGCGZDHZGBDICDIAOQANPDEABC
     FJKJBDLCDLM $.
     $( [?] $) $( [6-Dec-2010] $)
$}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
             Rederive original set theory
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)



${ $d x z $. $d y z $.
   axext $p |- ( A. z ( z e. x <-> z e. y ) -> x = y ) $=
     ( wel wb wal weq wex wi wn ax-ext wa dfbi2 imbi1i impexp bitri exbii 
     df-ex mpbir 19.35i ax17eq 19.9 sylib ) CADZCBDZEZCFABGZCHUGUFUGCUFUGIZCHZU
     DUEIZUEUDIZUGIIZJCFJZCABKUIULCHUMUHULCUHUJUKLZUGIULUFUNUGUDUEMNUJUKUGOPQUL
     CRPSTUGCABCUAUBUC $.
     $( [?] $) $( [15-Nov-2010] $)
$}


axreg $p |- ( E. y y e. x -> 
      	      E. y ( y e. x /\ A. z ( z e. y -> -. z e. x ) ) ) $=
  ( wel wn wi wal wa wex hbe1 ax-reg df-an exbii exnal bitri sylibr 19.23ai ) 
  BADZRCBDCADEFCGZHZBIZBTBJRRSEFZBGEZUABACKUAUBEZBIUCTUDBRSLMUBBNOPQ $.
  $( [?] $) $( [15-Nov-2010] $)


${ $d x y w $. $d z y w $.  
  axun $p |- E. y A. z ( E. w ( z e. w /\ w e. x ) -> z e. y ) $=
    ( wel wa wex wi wal wn ax-un df-an exbii exnal bitri imbi1i albii df-ex 
    mpbir ax17el hban weq elequ2 elequ1 anbi12d cbvex ) CDEZDAEZFZDGZCBEZHZCIZB
    GUKBAEZFZBGZUKHZCIZBGZUSUKUNJHZBIJZUKHZCIZJBIJZBCAKUSVCBGVDURVCBUQVBCUPVAUK
    UPUTJZBGVAUOVEBUKUNLMUTBNOPQMVCBROSUMURBULUQCUJUPUKUIUODBUGUGUHUHBCDBTDABTU
    AUKUKUNUNDCBDTBADTUADBUBUGUKUHUNDBCUCDBAUDUEUFPQMS $.
    $( [?] $) $( [15-Nov-2010] $)
$}


${ $d w x y z $.
  axrep $p |- ( A. w E. y A. z ( A. y ph -> z = y ) -> E. y A. z ( z e. y <-> E. w ( w e. x /\ A. y ph ) ) ) $=
    ( wal weq wi wex wel wa wb hbe1 ax17el hba1 hban hbex hbbi hbal hbim 
    ax17eq elequ2 anbi1d exbid bibi2d albid imbi2d wn ax-rep df-ex df-an exbii 
    exnal bitri bibi2i dfbi1 albii imbi12i mpbir ax-4 impbii anbi1i bibi12i 
    imbi2i mpbi chvar 19.35i 19.3 anbi2i a1i bibi12d cbvex sylib ) ACFZDCGHDFZC
    IZEFDEJZEBJZVNCFZKZEIZLZDFZEIDCJZVRVNKZEIZLZDFZCIVPWCEVPVQECJZVSKZEIZLZDFZH
    ZEIZVPWCHZEICBWPWPCEVPVPWCWCCVOCMWBWBCDVQWACDECNZVTVTCEVRVRVSVSCEBCNVNCOPQR
    SZTQCBGZWNWPECBEUAZWSWMWCVPWSWLWBDCBDUAWSWKWAVQWSWJVTEWTWSWIVRVSCBEUBUCUDUE
    UFUGUDVPVQCFZWIDFZVSKZEIZLZDFZHZEIZWOXHVOUHCFUHZXAXBVSUHHZEFUHZHXKXAHUHHUHZ
    DFZHZUHEFUHZVNECDUIXHXNEIXOXGXNEVPXIXFXMVOCUJXEXLDXEXAXKLXLXDXKXAXDXJUHZEIX
    KXCXPEXBVSUKULXJEUMUNUOXAXKUPUNUQURULXNEUJUNUSXGWNEXFWMVPXEWLDXAVQXDWKXAVQV
    QCUTWQVAXCWJEXBWIVSXBWIWIDUTECDNVAVBULVCUQVDULVEVFVGWCWHECWRWGWGEDWDWFEDCEN
    WEEMRSECGZWBWGDECDUAXQVQWDWAWFECDUBWAWFLXQVTWEEVSVNVRACVHVIULVJVKUFVLVM $.
    $( [?] $) $( [6-Dec-2010] $)
$}

${ $d x y z w $. 
   axpow $p |- E. y A. z ( A. w ( w e. z -> w e. x ) -> z e. y ) $=
     ( wel wi wal wex weq wn ax-two exnal mpbir hbe1 df-ex imbi1i albii notbii 
     ax-pow sylbi con3i sylibr 19.23ai ax-mp ax17el 19.9 ax-4 impbii imbi12i 
     exbii mpbi hbim elequ1 imbi12d cbval ) DCEZDAEZFZDGZCBEZFZCGZBHBCEZBAEZFZB
     GZUTFZCGZBHZVCAHZVDCGZFZBGZUTFZCGZBHZVIBCIZJZBHZVPVSVQBGJBCKVQBLMVRVPBVOBN
     VRVOJZBGZJVPWAVQWAVCJAGJZVKFZBGZUTFZCGZJZBGVQVTWGBVOWFVNWECVMWDUTVLWCBVJWB
     VKVCAOPQPQRQBCASTUAVOBOUBUCUDVOVHBVNVGCVMVFUTVLVEBVJVCVKVDVCABCAUEUFVKVDVD
     CUGBACUEUHUIQPQUJUKVBVHBVAVGCUSVFUTURVEDBUPUPUQUQBDCBUEDABUEULVCVCVDVDDBCD
     UEBADUEULDBIUPVCUQVDDBCUMDBAUMUNUOPQUJM $.
     $( [?] $) $( [6-Dec-2010] $)
$}

${ $d x y z w $. 
   el $p |- E. y x e. y $=
     ( vw vz wel wi wal wex axpow id ax-gen ax17el hbim hbal weq ax17eq elequ2 
     imbi1d albid elequ1 imbi12d biimpd a4im mpi 19.22i ax-mp ) CDEZCAEZFZCGZDB
     EZFZDGZBHABEZBHABDCIUMUNBUMUHUHFZCGZUNUOCUHJKULUPUNFZDAUPUPUNUNDUOUODCUHUH
     UHUHDCADLZURMNABDLMDAOZULUQUSUJUPUKUNUSUIUOCDACPUSUGUHUHDACQRSDABTUAUBUCUD
     UEUF $.
     $( [?] $) $( [6-Dec-2010] $)
$}


${ $d w x y z $. 
  axinf $p |- E. y ( x e. y /\ A. z ( z e. y -> E. w ( z e. w /\ w e. y ) ) ) $=
    ( wel wa wex wi wal el ax17el hbe1 hbim hbal hban hbex wn ax-inf df-an 
    exbii exnal bitri imbi2i albii anbi2i df-ex mpbir 19.35i syl 19.23ai ax-mp 
    weq elequ1 ax17eq anbi1d exbid imbi12d cbval ) ABEZCBEZCDEZDBEZFZDGZHZCIZFZ
    BGUSUSADEZVBFZDGZHZAIZFZBGZVHDGVNADJVHVNDVMVMDBUSUSVLVLDABDKZVKVKDAUSUSVJVJ
    DVOVIDLMNOPVHVHBIVNADBKVHVMBVHVMHZBGZVHUSUSVHVBQHZDIQZHZAIZQHQZHZQBIQZBADRV
    QWCBGWDVPWCBVMWBVHVMUSWAFWBVLWAUSVKVTAVJVSUSVJVRQZDGVSVIWEDVHVBSTVRDUAUBUCU
    DUEUSWASUBUCTWCBUFUBUGUHUIUJUKVGVMBVFVLUSVEVKCAUTUTVDVDACBAKVCVCADVAVAVBVBA
    CDAKDBAKOPMUSUSVJVJCABCKVIVICDVHVHVBVBCADCKDBCKOPMCAULZUTUSVDVJCABUMWFVCVID
    CADUNWFVAVHVBCADUMUOUPUQURUETUG $.
    $( [?] $) $( [18-Nov-2010] $)
$}

${ $d t u w x y $. $d u v w x y z $.
   axac $p |- E. y A. z A. w ( ( z e. w /\ w e. x ) -> E. v A. u ( E. t ( ( u e. w /\ w e. t ) /\ ( u e. t /\ t e. y ) ) <-> u = v ) ) $=
     ( wel wa wex weq wb wal wi wn ax-ac df-an albii anass annim pm4.63 anbi2i 
     bitr3i 3bitr2i exbii exnal bitri bibi1i dfbi1 df-ex imbi12i mpbir ax-4 
     ax17el hban impbii imbi1i mpbi hbex ax17eq hbbi hbal equequ2 bibi2d 
     elequ2 anbi2d elequ1 anbi12d cbvex syl6bb albid anbi1d exbid equequ1 
     bibi12d cbval imbi2i ) CDHZDAHZIZFDHZDGHZIZFGHZGBHZIZIZGJZFEKZLZFMZEJZNZDM
     ZCMZBJVTVTCAHZABHZIZIZAJZCAKZLZCMZAJZNZDMZCMZBJZVTBMZXDNZDMZCMZBJZXHXMVRVS
     ONOZBMZVRVSWPWQONZNZNZAMOZXANXAXSNONOZCMZOAMOZNZDMZCMZOBMOZBCDAPXMYEBJYFXL
     YEBXKYDCXJYCDXIXOXDYBVTXNBVRVSQRXDYAAJYBXCYAAXBXTCXBXSXALXTWTXSXAWTXROZAJX
     SWSYGAWSVRVSWRIZIVRXQOZIYGVRVSWRSYIYHVRYIVSXPOZIYHVSXPTYJWRVSWPWQUAUBUCUBV
     RXQTUDUEXRAUFUGUHXSXAUIUGRUEYAAUJUGUKRRUEYEBUJUGULXLXGBXKXFCXJXEDXIVTXDXIV
     TVTBUMVRVRVSVSBCDBUNDABUNUOUPUQRRUEURWOXGBWNXFCWMXEDWLXDVTWKXCEAWJWJAFWHWI
     AWGWGAGWCWCWFWFAWAWAWBWBAFDAUNDGAUNUOWDWDWEWEAFGAUNGBAUNUOUOZUSFEAUTVAVBXB
     XBECWTXAEWSWSEAVTVTWRWREVRVRVSVSECDEUNDAEUNUOWPWPWQWQECAEUNABEUNUOUOUSCAEU
     TVAVBEAKZWKWAVSIZFAHZWQIZIZAJZFAKZLZFMXCYLWJYSFEAFUTYLWJWHYRLYSYLWIYRWHEAF
     VCVDWHYQYRWGYPGAYKYMYMYOYOGWAWAVSVSGFDGUNDAGUNUOYNYNWQWQGFAGUNABGUNUOUOGAK
     ZWCYMWFYOYTWBVSWAGADVEVFYTWDYNWEWQGAFVEGABVGVHVHVIUHVJVKYSXBFCYQYRCYPYPCAY
     MYMYOYOCWAWAVSVSCFDCUNDACUNUOYNYNWQWQCFACUNABCUNUOUOUSFACUTVAWTXAFWSWSFAVT
     VTWRWRFVRVRVSVSFCDFUNDAFUNUOWPWPWQWQFCAFUNABFUNUOUOUSCAFUTVAFCKZYQWTYRXAUU
     AYPWSAFCAUTUUAYMVTYOWRUUAWAVRVSFCDVGVLUUAYNWPWQFCAVGVLVHVMFCAVNVOVPVJVIVQR
     RUEUL $.
     $( [?] $) $( [6-Dec-2010] $)
$}
