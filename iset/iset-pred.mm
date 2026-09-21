
$( The following header is the first to appear in the Theorem List contents,
   because higher-level headers suppress all previous same-level or
   lower-level headers in the same comment area between $a and $p statements.
   See "MM> HELP WRITE THEOREM_LIST" for information about headers. $)


$(
###############################################################################
  INTUITIONISTIC FIRST-ORDER LOGIC WITH EQUALITY
###############################################################################

  Logic can be defined as the "study of the principles of correct reasoning"
  (Merrilee H. Salmon's 1991 "Informal Reasoning and Informal Logic" in
  _Informal Reasoning and Education_ ) or as "a formal system using symbolic
  techniques and mathematical methods to establish truth-values" (the Oxford
  English Dictionary).

  This section formally defines the logic system we will use.  In particular,
  it defines symbols for declaring truthful statements, along with rules for
  deriving truthful statements from other truthful statements.  The system
  defined here is intuitionistic first-order logic with equality.

  We begin with a few housekeeping items in pre-logic, and then introduce
  propositional calculus (both its axioms and important theorems that can be
  derived from them).  Propositional calculus deals with general truths about
  well-formed formulas (wffs) regardless of how they are constructed.  This is
  followed by proofs that other axiomatizations of classical propositional
  calculus can be derived from the axioms we have chosen to use.

  We then define predicate calculus, which adds additional symbols and rules
  useful for discussing objects (beyond simply true or false).  In particular,
  it introduces the symbols ` = ` ("equals"), ` e. ` ("is a member of"), and `
  A. ` ("for all").  The first two are called "predicates".  A predicate
  specifies a true or false relationship between its two arguments.

$)


$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Pre-logic
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#

  This section includes a few "housekeeping" mechanisms before we begin
  defining the basics of logic.

$)

  $( Declare the primitive constant symbols for propositional calculus. $)
  $c ( $.  $( Left parenthesis $)
  $c ) $.  $( Right parenthesis $)
  $c -> $.  $( Right arrow (read:  "implies") $)
  $c -. $.  $( Right handle (read:  "not") $)
  $c wff $.  $( Well-formed formula symbol (read:  "the following symbol
                sequence is a wff") $)
  $c |- $.  $( Turnstile (read:  "the following symbol sequence is provable" or
               'a proof exists for") $)

  $( Define the syntax and logical typecodes, and declare that our grammar is
     unambiguous (verifiable using the KLR parser, with compositing depth 5).
     (This $ j comment need not be read by verifiers, but is useful for parsers
     like mmj2.) $)
  $( $j
    syntax 'wff';
    syntax '|-' as 'wff';
    unambiguous 'klr 5';
  $)

  $( Declare typographical constant symbols that are not directly used in the
     formalism but are useful to explain it in comments. $)

  $c & $.  $( Ampersand (read: "and"). $)
  $c => $.  $( Double right arrow (read: "implies"). $)

  $( wff variable sequence:  ph ps ch th ta et ze si rh mu la ka $)
  $( Introduce some variable names we will use to represent well-formed
     formulas (wff's). $)
  $v ph $.  $( Greek phi $)
  $v ps $.  $( Greek psi $)
  $v ch $.  $( Greek chi $)
  $v th $.  $( Greek theta $)
  $v ta $.  $( Greek tau $)
  $v et $.  $( Greek eta $)
  $v ze $.  $( Greek zeta $)
  $v si $.  $( Greek sigma $)
  $v rh $.  $( Greek rho $)
  $v mu $.  $( Greek mu $)
  $v la $.  $( Greek lambda $)
  $v ka $.  $( Greek kappa $)

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
  $( Let variable ` et ` be a wff. $)
  wet $f wff et $.
  $( Let variable ` ze ` be a wff. $)
  wze $f wff ze $.
  $( Let variable ` si ` be a wff. $)
  wsi $f wff si $.
  $( Let variable ` rh ` be a wff. $)
  wrh $f wff rh $.
  $( Let variable ` mu ` be a wff. $)
  wmu $f wff mu $.
  $( Let variable ` la ` be a wff. $)
  wla $f wff la $.
  $( Let variable ` ka ` be a wff. $)
  wka $f wff ka $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Inferences for assisting proof development
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  The inference rules in this section will normally never appear in a completed
  proof.  They can be ignored if you are using this database to assist learning
  logic - please start with the statement ~ wn instead.

$)

  ${
    idi.1 $e |- ph $.
    $( (_Note_:  This inference rule and the next one, ~ a1ii , will normally
       never appear in a completed proof.  They can be ignored if you are using
       this database to assist learning logic; please start with the statement
       ~ wn instead.)

       This inference says "if ` ph ` is true then ` ph ` is true".  This
       inference requires no axioms for its proof, and is useful as a
       copy-paste mechanism during proof development in mmj2.  It is normally
       not referenced in the final version of a proof, since it is always
       redundant.  You can remove this using the metamath-exe (Metamath
       program) Proof Assistant using the "MM-PA> MINIMIZE__WITH *" command.
       This is the inference associated with ~ id , hence its name.
       (Contributed by Alan Sare, 31-Dec-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    idi $p |- ph $=
      (  ) B $.
  $}

  ${
    a1ii.1 $e |- ph $.
    a1ii.2 $e |- ps $.
    $( (_Note_:  This inference rule and the previous one, ~ idi , will
       normally never appear in a completed proof.)

       This is a technical inference to assist proof development.  It provides
       a temporary way to add an independent subproof to a proof under
       development, for later assignment to a normal proof step.

       The Metamath (Metamath-exe) program Proof Assistant requires proofs to
       be developed backwards from the conclusion with no gaps, and it has no
       mechanism that lets the user work on isolated subproofs.  This inference
       provides a workaround for this limitation.  It can be inserted at any
       point in a proof to allow an independent subproof to be developed on the
       side, for later use as part of the final proof.

       _Instructions_:  (1) Assign this inference to any unknown step in the
       proof.  Typically, the last unknown step is the most convenient, since
       "MM-PA> ASSIGN LAST" can be used.  This step will be replicated in
       hypothesis a1ii.1, from where the development of the main proof can
       continue.  (2) Develop the independent subproof backwards from
       hypothesis a1ii.2.  If desired, use a "MM-PA> LET STEP" command to
       pre-assign the conclusion of the independent subproof to a1ii.2.  (3)
       After the independent subproof is complete, use "MM-PA> IMPROVE ALL" to
       assign it automatically to an unknown step in the main proof that
       matches it.  (4) After the entire proof is complete, use "MM-PA>
       MINIMIZE__WITH *" to clean up (discard) all ~ a1ii references
       automatically.

       This inference was originally designed to assist importing partially
       completed Proof Worksheets from the mmj2 Proof Assistant GUI, but it can
       also be useful on its own.  Interestingly, no axioms are required for
       its proof.  It is the inference associated with ~ a1i .  (Contributed by
       NM, 7-Feb-2006.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    a1ii $p |- ph $=
      (  ) C $.
  $}


$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Propositional calculus
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#

  Propositional calculus deals with general truths about well-formed formulas
  (wffs) regardless of how they are constructed.  The simplest propositional
  truth is ` ( ph -> ph ) ` , which can be read "if something is true, then it
  is true" - rather trivial and obvious, but nonetheless it must be proved from
  the axioms (see Theorem ~ id ).

  Our system of propositional calculus consists of a few basic axioms and a
  unique rule of inference, modus ponens.

  The propositional calculus used here is the intuitionistic propositional
  calculus.

  All 194 axioms, definitions, and theorems for propositional calculus in
  _Principia Mathematica_ (specifically *1.2 through *5.75) are axioms or
  formally proven.  See the Bibliographic Cross-References at
  ~ https://us.metamath.org/ileuni/mmbiblio.html for a complete
  cross-reference from sources used to its formalization in the Intuitionistic
  Logic Explorer.

$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Recursively define primitive wffs for propositional calculus
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( If ` ph ` is a wff, so is ` -. ph ` or "not ` ph ` ".  Part of the
     recursive definition of a wff (well-formed formula).  Traditionally, Greek
     letters are used to represent wffs, and we follow this convention.  In
     propositional calculus, we define only wffs built up from other wffs,
     i.e., there is no starting or "atomic" wff.  Later, in predicate calculus,
     we will extend the basic wff definition by including atomic wffs ( ~ weq
     and ~ wel ). $)
  wn $a wff -. ph $.

  $( Register negation '-.' as a primitive expression (lacking a
     definition). $)
  $( $j primitive 'wn'; $)

  $( If ` ph ` and ` ps ` are wff's, so is ` ( ph -> ps ) ` or " ` ph ` implies
     ` ps ` ".  Part of the recursive definition of a wff.  The left-hand wff
     is called the antecedent, and the right-hand wff is called the consequent.
     In the case of ` ( ph -> ( ps -> ch ) ) ` , the middle ` ps ` may be
     informally called either an antecedent or part of the consequent depending
     on context. $)
  wi $a wff ( ph -> ps ) $.

  $( Register implication '->' as a primitive expression (lacking a
     definition). $)
  $( $j primitive 'wi'; $)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Propositional logic axioms for implication
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $( Minor premise for modus ponens. $)
    min $e |- ph $.
    $( Major premise for modus ponens. $)
    maj $e |- ( ph -> ps ) $.
    $( Rule of Modus Ponens.  The postulated inference rule of propositional
       calculus.  See, e.g., Rule 1 of [Hamilton] p. 73.  The rule says, "if
       ` ph ` is true, and ` ph ` implies ` ps ` , then ` ps ` must also be
       true".  This rule is sometimes called "detachment", since it detaches
       the minor premise from the major premise.  "Modus ponens" is short for
       "modus ponendo ponens", a Latin phrase that means "the mode that by
       affirming affirms" - remark in [Sanford] p. 39.  This rule is similar to
       the rule of modus tollens ~ mto .

       Note:  In some web page displays such as the Statement List, the
       symbols " ` & ` " and " ` => ` " informally indicate the relationship
       between the hypotheses and the assertion (conclusion), abbreviating the
       English words "and" and "implies".  They are not part of the formal
       language.  (Contributed by NM, 30-Sep-1992.) $)
    ax-mp $a |- ps $.
  $}

  $( Axiom _Simp_.  Axiom A1 of [Margaris] p. 49.  One of the axioms of
     propositional calculus.  This axiom is called _Simp_ or "the principle of
     simplification" in _Principia Mathematica_ (Theorem *2.02 of
     [WhiteheadRussell] p. 100) because "it enables us to pass from the joint
     assertion of ` ph ` and ` ps ` to the assertion of ` ph ` simply."

     The theorems of propositional calculus are also called _tautologies_.
     Although classical propositional logic tautologies can be proved using
     truth tables, there is no similarly simple system for intuitionistic
     propositional logic, so proving tautologies from axioms is the preferred
     approach.  (Contributed by NM, 5-Aug-1993.) $)
  ax-1 $a |- ( ph -> ( ps -> ph ) ) $.

  $( Axiom _Frege_.  Axiom A2 of [Margaris] p. 49.  This axiom "distributes" an
     antecedent over two consequents.  This axiom was part of Frege's original
     system and is known as _Frege_ in the literature.  It is also proved as
     Theorem *2.77 of [WhiteheadRussell] p. 108.  The other direction of this
     axiom also turns out to be true, as demonstrated by ~ pm5.41 .
     (Contributed by NM, 5-Aug-1993.) $)
  ax-2 $a |- ( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) ) ) $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Logical implication
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  The results in this section are based on implication only, and only use
  ~ ax-1 , ~ ax-2 , and ~ ax-mp .  In an implication, the wff before the arrow
  is called the "antecedent" and the wff after the arrow is called the
  "consequent".

  We will use the following descriptive terms very loosely:  A "closed form" or
  "tautology" has no $e hypotheses.  An "inference" has one or more $e
  hypotheses.  A "deduction" is an inference in which the hypotheses and the
  conclusion share the same antecedent.

$)

  ${
    mp2b.1 $e |- ph $.
    mp2b.2 $e |- ( ph -> ps ) $.
    mp2b.3 $e |- ( ps -> ch ) $.
    $( A double modus ponens inference.  (Contributed by Mario Carneiro,
       24-Jan-2013.) $)
    mp2b $p |- ch $=
      ( ax-mp ) BCABDEGFG $.
  $}

  ${
    $( Premise for ~ a1i . $)
    a1i.1 $e |- ph $.
    $( Inference derived from Axiom ~ ax-1 .  See ~ a1d for an explanation of
       our informal use of the terms "inference" and "deduction".  See also the
       comment in ~ syld .  (Contributed by NM, 5-Aug-1993.) $)
    a1i $p |- ( ps -> ph ) $=
      ( wi ax-1 ax-mp ) ABADCABEF $.
  $}

  ${
    mp1i.a $e |- ph $.
    mp1i.b $e |- ( ph -> ps ) $.
    $( Drop and replace an antecedent.  (Contributed by Stefan O'Rear,
       29-Jan-2015.) $)
    mp1i $p |- ( ch -> ps ) $=
      ( ax-mp a1i ) BCABDEFG $.
  $}

  ${
    $( Premise for ~ a2i . $)
    a2i.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Inference derived from Axiom ~ ax-2 .  (Contributed by NM,
       5-Aug-1993.) $)
    a2i $p |- ( ( ph -> ps ) -> ( ph -> ch ) ) $=
      ( wi ax-2 ax-mp ) ABCEEABEACEEDABCFG $.
  $}

  ${
    imim2i.1 $e |- ( ph -> ps ) $.
    $( Inference adding common antecedents in an implication.  (Contributed by
       NM, 5-Aug-1993.) $)
    imim2i $p |- ( ( ch -> ph ) -> ( ch -> ps ) ) $=
      ( wi a1i a2i ) CABABECDFG $.
  $}

  ${
    mpd.1 $e |- ( ph -> ps ) $.
    mpd.2 $e |- ( ph -> ( ps -> ch ) ) $.
    $( A modus ponens deduction.  (Contributed by NM, 5-Aug-1993.) $)
    mpd $p |- ( ph -> ch ) $=
      ( wi a2i ax-mp ) ABFACFDABCEGH $.
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
       call this law a "hypothetical syllogism".  (Contributed by NM,
       5-Aug-1993.)  (Proof shortened by O'Cat, 20-Oct-2011.)  (Proof shortened
       by Wolf Lammen, 26-Jul-2012.) $)
    syl $p |- ( ph -> ch ) $=
      ( wi a1i mpd ) ABCDBCFAEGH $.
  $}

  ${
    mpi.1 $e |- ps $.
    mpi.2 $e |- ( ph -> ( ps -> ch ) ) $.
    $( A nested modus ponens inference.  (Contributed by NM, 5-Aug-1993.)
       (Proof shortened by Stefan Allan, 20-Mar-2006.) $)
    mpi $p |- ( ph -> ch ) $=
      ( a1i mpd ) ABCBADFEG $.
  $}

  ${
    mp2.1 $e |- ph $.
    mp2.2 $e |- ps $.
    mp2.3 $e |- ( ph -> ( ps -> ch ) ) $.
    $( A double modus ponens inference.  (Contributed by NM, 5-Apr-1994.)
       (Proof shortened by Wolf Lammen, 23-Jul-2013.) $)
    mp2 $p |- ch $=
      ( mpi ax-mp ) ACDABCEFGH $.
  $}

  ${
    3syl.1 $e |- ( ph -> ps ) $.
    3syl.2 $e |- ( ps -> ch ) $.
    3syl.3 $e |- ( ch -> th ) $.
    $( Inference chaining two syllogisms.  (Contributed by NM, 5-Aug-1993.) $)
    3syl $p |- ( ph -> th ) $=
      ( syl ) ACDABCEFHGH $.
  $}

  ${
    4syl.1 $e |- ( ph -> ps ) $.
    4syl.2 $e |- ( ps -> ch ) $.
    4syl.3 $e |- ( ch -> th ) $.
    4syl.4 $e |- ( th -> ta ) $.
    $( Inference chaining three syllogisms.  The use of this theorem is marked
       "discouraged" because it can cause the "minimize" command to have very
       long run times.  However, feel free to use "minimize 4syl /override" if
       you wish.  (Contributed by BJ, 14-Jul-2018.)
       (New usage is discouraged.) $)
    4syl $p |- ( ph -> ta ) $=
      ( 3syl syl ) ADEABCDFGHJIK $.
  $}

  $( Principle of identity.  Theorem *2.08 of [WhiteheadRussell] p. 101.  For
     another version of the proof directly from axioms, see ~ idALT .
     (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Stefan Allan,
     20-Mar-2006.) $)
  id $p |- ( ph -> ph ) $=
    ( wi ax-1 mpd ) AAABZAAACAECD $.

  $( Principle of identity.  Theorem *2.08 of [WhiteheadRussell] p. 101.  This
     version is proved directly from the axioms for demonstration purposes.
     This proof is a popular example in the literature and is identical, step
     for step, to the proofs of Theorem 1 of [Margaris] p. 51, Example 2.7(a)
     of [Hamilton] p. 31, Lemma 10.3 of [BellMachover] p. 36, and Lemma 1.8 of
     [Mendelson] p. 36.  It is also "Our first proof" in Hirst and Hirst's _A
     Primer for Logic and Proof_ p. 17 (PDF p. 23) at
     ~ http://www.mathsci.appstate.edu/~~jlh/primer/hirst.pdf .  For a shorter
     version of the proof that takes advantage of previously proved theorems,
     see ~ id .  (Contributed by NM, 5-Aug-1993.)
     (Proof modification is discouraged.)  Use ~ id instead.
     (New usage is discouraged.) $)
  idALT $p |- ( ph -> ph ) $=
    ( wi ax-1 ax-2 ax-mp ) AAABZBZFAACAFABBGFBAFCAFADEE $.

  $( Principle of identity with antecedent.  (Contributed by NM,
     26-Nov-1995.) $)
  idd $p |- ( ph -> ( ps -> ps ) ) $=
    ( wi id a1i ) BBCABDE $.

  ${
    a1d.1 $e |- ( ph -> ps ) $.
    $( Deduction introducing an embedded antecedent.  (The proof was revised by
       Stefan Allan, 20-Mar-2006.)

       _Naming convention_:  We often call a theorem a "deduction" and suffix
       its label with "d" whenever the hypotheses and conclusion are each
       prefixed with the same antecedent.  This allows us to use the theorem in
       places where (in traditional textbook formalizations) the standard
       Deduction Theorem would be used; here ` ph ` would be replaced with a
       conjunction ( ~ wa ) of the hypotheses of the would-be deduction.  By
       contrast, we tend to call the simpler version with no common antecedent
       an "inference" and suffix its label with "i"; compare Theorem ~ a1i .
       Finally, a "theorem" would be the form with no hypotheses; in this case
       the "theorem" form would be the original axiom ~ ax-1 .  We usually show
       the theorem form without a suffix on its label (e.g., ~ pm2.43 versus
       ~ pm2.43i versus ~ pm2.43d ).  (Contributed by NM, 5-Aug-1993.)
       (Revised by NM, 20-Mar-2006.) $)
    a1d $p |- ( ph -> ( ch -> ps ) ) $=
      ( wi ax-1 syl ) ABCBEDBCFG $.
  $}

  ${
    2a1d.1 $e |- ( ph -> ps ) $.
    $( Deduction introducing two antecedents.  Two applications of ~ a1d .
       Deduction associated with ~ 2a1 and ~ 2a1i .  (Contributed by BJ,
       10-Aug-2020.) $)
    2a1d $p |- ( ph -> ( ch -> ( th -> ps ) ) ) $=
      ( wi a1d ) ADBFCABDEGG $.
  $}

  ${
    a1i13.1 $e |- ( ps -> th ) $.
    $( Add two antecedents to a wff.  (Contributed by Jeff Hankins,
       4-Aug-2009.) $)
    a1i13 $p |- ( ph -> ( ps -> ( ch -> th ) ) ) $=
      ( wi a1d a1i ) BCDFFABDCEGH $.
  $}

  $( A double form of ~ ax-1 .  Its associated inference is ~ 2a1i .  Its
     associated deduction is ~ 2a1d .  (Contributed by BJ, 10-Aug-2020.)
     (Proof shortened by Wolf Lammen, 1-Sep-2020.) $)
  2a1 $p |- ( ph -> ( ps -> ( ch -> ph ) ) ) $=
    ( id 2a1d ) AABCADE $.

  ${
    a2d.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    $( Deduction distributing an embedded antecedent.  (Contributed by NM,
       23-Jun-1994.) $)
    a2d $p |- ( ph -> ( ( ps -> ch ) -> ( ps -> th ) ) ) $=
      ( wi ax-2 syl ) ABCDFFBCFBDFFEBCDGH $.
  $}

  ${
    2a1i.1 $e |- ch $.
    $( Add two antecedents to a wff.  (Contributed by Jeff Hankins,
       4-Aug-2009.)  (Proof shortened by Wolf Lammen, 23-Jul-2013.) $)
    2a1i $p |- ( ph -> ( ps -> ch ) ) $=
      ( a1i a1d ) ACBCADEF $.
  $}

  ${
    sylcom.1 $e |- ( ph -> ( ps -> ch ) ) $.
    sylcom.2 $e |- ( ps -> ( ch -> th ) ) $.
    $( Syllogism inference with commutation of antecedents.  (Contributed by
       NM, 29-Aug-2004.)  (Proof shortened by O'Cat, 2-Feb-2006.)  (Proof
       shortened by Stefan Allan, 23-Feb-2006.) $)
    sylcom $p |- ( ph -> ( ps -> th ) ) $=
      ( wi a2i syl ) ABCGBDGEBCDFHI $.
  $}

  ${
    syl5com.1 $e |- ( ph -> ps ) $.
    syl5com.2 $e |- ( ch -> ( ps -> th ) ) $.
    $( Syllogism inference with commuted antecedents.  (Contributed by NM,
       24-May-2005.) $)
    syl5com $p |- ( ph -> ( ch -> th ) ) $=
      ( a1d sylcom ) ACBDABCEGFH $.
  $}

  ${
    $( Premise for ~ com12 .  See ~ pm2.04 for the theorem form. $)
    com12.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Inference that swaps (commutes) antecedents in an implication.
       (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen,
       4-Aug-2012.) $)
    com12 $p |- ( ps -> ( ph -> ch ) ) $=
      ( id syl5com ) BBACBEDF $.
  $}

  ${
    syl11.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syl11.2 $e |- ( th -> ph ) $.
    $( A syllogism inference.  Commuted form of an instance of ~ syl .
       (Contributed by BJ, 25-Oct-2021.) $)
    syl11 $p |- ( ps -> ( th -> ch ) ) $=
      ( wi syl com12 ) DBCDABCGFEHI $.
  $}

  ${
    syl5.1 $e |- ( ph -> ps ) $.
    syl5.2 $e |- ( ch -> ( ps -> th ) ) $.
    $( A syllogism rule of inference.  The second premise is used to replace
       the second antecedent of the first premise.  (Contributed by NM,
       5-Aug-1993.)  (Proof shortened by Wolf Lammen, 25-May-2013.) $)
    syl5 $p |- ( ch -> ( ph -> th ) ) $=
      ( syl5com com12 ) ACDABCDEFGH $.
  $}

  ${
    syl6.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syl6.2 $e |- ( ch -> th ) $.
    $( A syllogism rule of inference.  The second premise is used to replace
       the consequent of the first premise.  (Contributed by NM, 5-Aug-1993.)
       (Proof shortened by Wolf Lammen, 30-Jul-2012.) $)
    syl6 $p |- ( ph -> ( ps -> th ) ) $=
      ( wi a1i sylcom ) ABCDECDGBFHI $.
  $}

  ${
    syl56.1 $e |- ( ph -> ps ) $.
    syl56.2 $e |- ( ch -> ( ps -> th ) ) $.
    syl56.3 $e |- ( th -> ta ) $.
    $( Combine ~ syl5 and ~ syl6 .  (Contributed by NM, 14-Nov-2013.) $)
    syl56 $p |- ( ch -> ( ph -> ta ) ) $=
      ( syl6 syl5 ) ABCEFCBDEGHIJ $.
  $}

  ${
    syl6com.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syl6com.2 $e |- ( ch -> th ) $.
    $( Syllogism inference with commuted antecedents.  (Contributed by NM,
       25-May-2005.) $)
    syl6com $p |- ( ps -> ( ph -> th ) ) $=
      ( syl6 com12 ) ABDABCDEFGH $.
  $}

  ${
    mpcom.1 $e |- ( ps -> ph ) $.
    mpcom.2 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Modus ponens inference with commutation of antecedents.  (Contributed by
       NM, 17-Mar-1996.) $)
    mpcom $p |- ( ps -> ch ) $=
      ( com12 mpd ) BACDABCEFG $.
  $}

  ${
    syli.1 $e |- ( ps -> ( ph -> ch ) ) $.
    syli.2 $e |- ( ch -> ( ph -> th ) ) $.
    $( Syllogism inference with common nested antecedent.  (Contributed by NM,
       4-Nov-2004.) $)
    syli $p |- ( ps -> ( ph -> th ) ) $=
      ( com12 sylcom ) BACDECADFGH $.
  $}

  ${
    syl2im.1 $e |- ( ph -> ps ) $.
    syl2im.2 $e |- ( ch -> th ) $.
    syl2im.3 $e |- ( ps -> ( th -> ta ) ) $.
    $( Replace two antecedents.  Implication-only version of ~ syl2an .
       (Contributed by Wolf Lammen, 14-May-2013.) $)
    syl2im $p |- ( ph -> ( ch -> ta ) ) $=
      ( wi syl5 syl ) ABCEIFCDBEGHJK $.

    $( A commuted version of ~ syl2im .  Implication-only version of
       ~ syl2anr .  (Contributed by BJ, 20-Oct-2021.) $)
    syl2imc $p |- ( ch -> ( ph -> ta ) ) $=
      ( syl2im com12 ) ACEABCDEFGHIJ $.
  $}

  $( This theorem, called "Assertion," can be thought of as closed form of
     modus ponens ~ ax-mp .  Theorem *2.27 of [WhiteheadRussell] p. 104.
     (Contributed by NM, 5-Aug-1993.) $)
  pm2.27 $p |- ( ph -> ( ( ph -> ps ) -> ps ) ) $=
    ( wi id com12 ) ABCZABFDE $.

  ${
    mpdd.1 $e |- ( ph -> ( ps -> ch ) ) $.
    mpdd.2 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    $( A nested modus ponens deduction.  (Contributed by NM, 12-Dec-2004.) $)
    mpdd $p |- ( ph -> ( ps -> th ) ) $=
      ( wi a2d mpd ) ABCGBDGEABCDFHI $.
  $}

  ${
    mpid.1 $e |- ( ph -> ch ) $.
    mpid.2 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    $( A nested modus ponens deduction.  (Contributed by NM, 14-Dec-2004.) $)
    mpid $p |- ( ph -> ( ps -> th ) ) $=
      ( a1d mpdd ) ABCDACBEGFH $.
  $}

  ${
    mpdi.1 $e |- ( ps -> ch ) $.
    mpdi.2 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    $( A nested modus ponens deduction.  (Contributed by NM, 16-Apr-2005.)
       (Proof shortened by O'Cat, 15-Jan-2008.) $)
    mpdi $p |- ( ph -> ( ps -> th ) ) $=
      ( wi a1i mpdd ) ABCDBCGAEHFI $.
  $}

  ${
    mpii.1 $e |- ch $.
    mpii.2 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    $( A doubly nested modus ponens inference.  (Contributed by NM,
       31-Dec-1993.)  (Proof shortened by Wolf Lammen, 31-Jul-2012.) $)
    mpii $p |- ( ph -> ( ps -> th ) ) $=
      ( a1i mpdi ) ABCDCBEGFH $.
  $}

  ${
    syld.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syld.2 $e |- ( ph -> ( ch -> th ) ) $.
    $( Syllogism deduction.

       Notice that ~ syld has the same form as ~ syl with ` ph ` added in front
       of each hypothesis and conclusion.  When all theorems referenced in a
       proof are converted in this way, we can replace ` ph ` with a hypothesis
       of the proof, allowing the hypothesis to be eliminated with ~ id and
       become an antecedent.  The Deduction Theorem for propositional calculus,
       e.g., Theorem 3 in [Margaris] p. 56, tells us that this procedure is
       always possible.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by
       O'Cat, 19-Feb-2008.)  (Proof shortened by Wolf Lammen, 3-Aug-2012.) $)
    syld $p |- ( ph -> ( ps -> th ) ) $=
      ( wi a1d mpdd ) ABCDEACDGBFHI $.
    $( Syllogism deduction.  Commuted form of ~ syld .  (Contributed by BJ,
       25-Oct-2021.) $)
    syldc $p |- ( ps -> ( ph -> th ) ) $=
      ( syld com12 ) ABDABCDEFGH $.
  $}

  ${
    mp2d.1 $e |- ( ph -> ps ) $.
    mp2d.2 $e |- ( ph -> ch ) $.
    mp2d.3 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    $( A double modus ponens deduction.  (Contributed by NM, 23-May-2013.)
       (Proof shortened by Wolf Lammen, 23-Jul-2013.) $)
    mp2d $p |- ( ph -> th ) $=
      ( mpid mpd ) ABDEABCDFGHI $.
  $}

  ${
    a1dd.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction introducing a nested embedded antecedent.  (Contributed by NM,
       17-Dec-2004.)  (Proof shortened by O'Cat, 15-Jan-2008.) $)
    a1dd $p |- ( ph -> ( ps -> ( th -> ch ) ) ) $=
      ( wi ax-1 syl6 ) ABCDCFECDGH $.
  $}

  ${
    pm2.43i.1 $e |- ( ph -> ( ph -> ps ) ) $.
    $( Inference absorbing redundant antecedent.  (Contributed by NM,
       5-Aug-1993.)  (Proof shortened by O'Cat, 28-Nov-2008.) $)
    pm2.43i $p |- ( ph -> ps ) $=
      ( id mpd ) AABADCE $.
  $}

  ${
    pm2.43d.1 $e |- ( ph -> ( ps -> ( ps -> ch ) ) ) $.
    $( Deduction absorbing redundant antecedent.  (Contributed by NM,
       18-Aug-1993.)  (Proof shortened by O'Cat, 28-Nov-2008.) $)
    pm2.43d $p |- ( ph -> ( ps -> ch ) ) $=
      ( id mpdi ) ABBCBEDF $.
  $}

  ${
    pm2.43a.1 $e |- ( ps -> ( ph -> ( ps -> ch ) ) ) $.
    $( Inference absorbing redundant antecedent.  (Contributed by NM,
       7-Nov-1995.)  (Proof shortened by O'Cat, 28-Nov-2008.) $)
    pm2.43a $p |- ( ps -> ( ph -> ch ) ) $=
      ( id mpid ) BABCBEDF $.
  $}

  ${
    pm2.43b.1 $e |- ( ps -> ( ph -> ( ps -> ch ) ) ) $.
    $( Inference absorbing redundant antecedent.  (Contributed by NM,
       31-Oct-1995.) $)
    pm2.43b $p |- ( ph -> ( ps -> ch ) ) $=
      ( pm2.43a com12 ) BACABCDEF $.
  $}

  $( Absorption of redundant antecedent.  Also called the "Contraction" or
     "Hilbert" axiom.  Theorem *2.43 of [WhiteheadRussell] p. 106.
     (Contributed by NM, 5-Aug-1993.)  (Proof shortened by O'Cat,
     15-Aug-2004.) $)
  pm2.43 $p |- ( ( ph -> ( ph -> ps ) ) -> ( ph -> ps ) ) $=
    ( wi pm2.27 a2i ) AABCBABDE $.

  ${
    imim2d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction adding nested antecedents.  (Contributed by NM,
       5-Aug-1993.) $)
    imim2d $p |- ( ph -> ( ( th -> ps ) -> ( th -> ch ) ) ) $=
      ( wi a1d a2d ) ADBCABCFDEGH $.
  $}

  $( A closed form of syllogism (see ~ syl ).  Theorem *2.05 of
     [WhiteheadRussell] p. 100.  (Contributed by NM, 5-Aug-1993.)  (Proof
     shortened by Wolf Lammen, 6-Sep-2012.) $)
  imim2 $p |- ( ( ph -> ps ) -> ( ( ch -> ph ) -> ( ch -> ps ) ) ) $=
    ( wi id imim2d ) ABDZABCGEF $.

  ${
    embantd.1 $e |- ( ph -> ps ) $.
    embantd.2 $e |- ( ph -> ( ch -> th ) ) $.
    $( Deduction embedding an antecedent.  (Contributed by Wolf Lammen,
       4-Oct-2013.) $)
    embantd $p |- ( ph -> ( ( ps -> ch ) -> th ) ) $=
      ( wi imim2d mpid ) ABCGBDEACDBFHI $.
  $}

  ${
    3syld.1 $e |- ( ph -> ( ps -> ch ) ) $.
    3syld.2 $e |- ( ph -> ( ch -> th ) ) $.
    3syld.3 $e |- ( ph -> ( th -> ta ) ) $.
    $( Triple syllogism deduction.  (Contributed by Jeff Hankins,
       4-Aug-2009.) $)
    3syld $p |- ( ph -> ( ps -> ta ) ) $=
      ( syld ) ABDEABCDFGIHI $.
  $}

  ${
    sylsyld.1 $e |- ( ph -> ps ) $.
    sylsyld.2 $e |- ( ph -> ( ch -> th ) ) $.
    sylsyld.3 $e |- ( ps -> ( th -> ta ) ) $.
    $( A double syllogism inference.  (Contributed by Alan Sare,
       20-Apr-2011.) $)
    sylsyld $p |- ( ph -> ( ch -> ta ) ) $=
      ( wi syl syld ) ACDEGABDEIFHJK $.
  $}

  ${
    imim12i.1 $e |- ( ph -> ps ) $.
    imim12i.2 $e |- ( ch -> th ) $.
    $( Inference joining two implications.  (Contributed by NM, 5-Aug-1993.)
       (Proof shortened by O'Cat, 29-Oct-2011.) $)
    imim12i $p |- ( ( ps -> ch ) -> ( ph -> th ) ) $=
      ( wi imim2i syl5 ) ABBCGDECDBFHI $.
  $}

  ${
    imim1i.1 $e |- ( ph -> ps ) $.
    $( Inference adding common consequents in an implication, thereby
       interchanging the original antecedent and consequent.  (Contributed by
       NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen, 4-Aug-2012.) $)
    imim1i $p |- ( ( ps -> ch ) -> ( ph -> ch ) ) $=
      ( id imim12i ) ABCCDCEF $.
  $}

  ${
    imim3i.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Inference adding three nested antecedents.  (Contributed by NM,
       19-Dec-2006.) $)
    imim3i $p |- ( ( th -> ph ) -> ( ( th -> ps ) -> ( th -> ch ) ) ) $=
      ( wi imim2i a2d ) DAFDBCABCFDEGH $.
  $}

  ${
    sylc.1 $e |- ( ph -> ps ) $.
    sylc.2 $e |- ( ph -> ch ) $.
    sylc.3 $e |- ( ps -> ( ch -> th ) ) $.
    $( A syllogism inference combined with contraction.  (Contributed by NM,
       4-May-1994.)  (Revised by NM, 13-Jul-2013.) $)
    sylc $p |- ( ph -> th ) $=
      ( syl2im pm2.43i ) ADABACDEFGHI $.
  $}

  ${
    syl3c.1 $e |- ( ph -> ps ) $.
    syl3c.2 $e |- ( ph -> ch ) $.
    syl3c.3 $e |- ( ph -> th ) $.
    syl3c.4 $e |- ( ps -> ( ch -> ( th -> ta ) ) ) $.
    $( A syllogism inference combined with contraction.  (Contributed by Alan
       Sare, 7-Jul-2011.) $)
    syl3c $p |- ( ph -> ta ) $=
      ( wi sylc mpd ) ADEHABCDEJFGIKL $.
  $}

  ${
    syl6mpi.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syl6mpi.2 $e |- th $.
    syl6mpi.3 $e |- ( ch -> ( th -> ta ) ) $.
    $( ~ syl6 combined with ~ mpi .  (Contributed by Alan Sare, 8-Jul-2011.)
       (Proof shortened by Wolf Lammen, 13-Sep-2012.) $)
    syl6mpi $p |- ( ph -> ( ps -> ta ) ) $=
      ( mpi syl6 ) ABCEFCDEGHIJ $.
  $}

  ${
    mpsyl.1 $e |- ph $.
    mpsyl.2 $e |- ( ps -> ch ) $.
    mpsyl.3 $e |- ( ph -> ( ch -> th ) ) $.
    $( Modus ponens combined with a syllogism inference.  (Contributed by Alan
       Sare, 20-Apr-2011.) $)
    mpsyl $p |- ( ps -> th ) $=
      ( a1i sylc ) BACDABEHFGI $.
  $}

  ${
    syl6c.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syl6c.2 $e |- ( ph -> ( ps -> th ) ) $.
    syl6c.3 $e |- ( ch -> ( th -> ta ) ) $.
    $( Inference combining ~ syl6 with contraction.  (Contributed by Alan Sare,
       2-May-2011.) $)
    syl6c $p |- ( ph -> ( ps -> ta ) ) $=
      ( wi syl6 mpdd ) ABDEGABCDEIFHJK $.
  $}

  ${
    syldd.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    syldd.2 $e |- ( ph -> ( ps -> ( th -> ta ) ) ) $.
    $( Nested syllogism deduction.  (Contributed by NM, 12-Dec-2004.)  (Proof
       shortened by Wolf Lammen, 11-May-2013.) $)
    syldd $p |- ( ph -> ( ps -> ( ch -> ta ) ) ) $=
      ( wi imim2 syl6c ) ABDEHCDHCEHGFDECIJ $.
  $}

  ${
    syl5d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syl5d.2 $e |- ( ph -> ( th -> ( ch -> ta ) ) ) $.
    $( A nested syllogism deduction.  (Contributed by NM, 5-Aug-1993.)  (Proof
       shortened by Josh Purinton, 29-Dec-2000.)  (Proof shortened by O'Cat,
       2-Feb-2006.) $)
    syl5d $p |- ( ph -> ( th -> ( ps -> ta ) ) ) $=
      ( wi a1d syldd ) ADBCEABCHDFIGJ $.
  $}

  ${
    syl7.1 $e |- ( ph -> ps ) $.
    syl7.2 $e |- ( ch -> ( th -> ( ps -> ta ) ) ) $.
    $( A syllogism rule of inference.  The second premise is used to replace
       the third antecedent of the first premise.  (Contributed by NM,
       5-Aug-1993.)  (Proof shortened by Wolf Lammen, 3-Aug-2012.) $)
    syl7 $p |- ( ch -> ( th -> ( ph -> ta ) ) ) $=
      ( wi a1i syl5d ) CABDEABHCFIGJ $.
  $}

  ${
    syl6d.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    syl6d.2 $e |- ( ph -> ( th -> ta ) ) $.
    $( A nested syllogism deduction.  (Contributed by NM, 5-Aug-1993.)  (Proof
       shortened by Josh Purinton, 29-Dec-2000.)  (Proof shortened by O'Cat,
       2-Feb-2006.)  (Revised by NM, 3-Feb-2006.) $)
    syl6d $p |- ( ph -> ( ps -> ( ch -> ta ) ) ) $=
      ( wi a1d syldd ) ABCDEFADEHBGIJ $.
  $}

  ${
    syl8.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    syl8.2 $e |- ( th -> ta ) $.
    $( A syllogism rule of inference.  The second premise is used to replace
       the consequent of the first premise.  (Contributed by NM, 1-Aug-1994.)
       (Proof shortened by Wolf Lammen, 3-Aug-2012.) $)
    syl8 $p |- ( ph -> ( ps -> ( ch -> ta ) ) ) $=
      ( wi a1i syl6d ) ABCDEFDEHAGIJ $.
  $}

  ${
    syl9.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syl9.2 $e |- ( th -> ( ch -> ta ) ) $.
    $( A nested syllogism inference with different antecedents.  (Contributed
       by NM, 5-Aug-1993.)  (Proof shortened by Josh Purinton, 29-Dec-2000.) $)
    syl9 $p |- ( ph -> ( th -> ( ps -> ta ) ) ) $=
      ( wi a1i syl5d ) ABCDEFDCEHHAGIJ $.
  $}

  ${
    syl9r.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syl9r.2 $e |- ( th -> ( ch -> ta ) ) $.
    $( A nested syllogism inference with different antecedents.  (Contributed
       by NM, 5-Aug-1993.) $)
    syl9r $p |- ( th -> ( ph -> ( ps -> ta ) ) ) $=
      ( wi syl9 com12 ) ADBEHABCDEFGIJ $.
  $}

  ${
    imim12d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    imim12d.2 $e |- ( ph -> ( th -> ta ) ) $.
    $( Deduction combining antecedents and consequents.  (Contributed by NM,
       7-Aug-1994.)  (Proof shortened by O'Cat, 30-Oct-2011.) $)
    imim12d $p |- ( ph -> ( ( ch -> th ) -> ( ps -> ta ) ) ) $=
      ( wi imim2d syl5d ) ABCCDHEFADECGIJ $.
  $}

  ${
    imim1d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction adding nested consequents.  (Contributed by NM, 3-Apr-1994.)
       (Proof shortened by Wolf Lammen, 12-Sep-2012.) $)
    imim1d $p |- ( ph -> ( ( ch -> th ) -> ( ps -> th ) ) ) $=
      ( idd imim12d ) ABCDDEADFG $.
  $}

  $( A closed form of syllogism (see ~ syl ).  Theorem *2.06 of
     [WhiteheadRussell] p. 100.  (Contributed by NM, 5-Aug-1993.)  (Proof
     shortened by Wolf Lammen, 25-May-2013.) $)
  imim1 $p |- ( ( ph -> ps ) -> ( ( ps -> ch ) -> ( ph -> ch ) ) ) $=
    ( wi id imim1d ) ABDZABCGEF $.

  $( Theorem *2.83 of [WhiteheadRussell] p. 108.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.83 $p |- ( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ( ch -> th ) ) ->
                ( ph -> ( ps -> th ) ) ) ) $=
    ( wi imim1 imim3i ) BCECDEBDEABCDFG $.

  ${
    com3.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    $( Commutation of antecedents.  Swap 2nd and 3rd.  (Contributed by NM,
       5-Aug-1993.)  (Proof shortened by Wolf Lammen, 4-Aug-2012.) $)
    com23 $p |- ( ph -> ( ch -> ( ps -> th ) ) ) $=
      ( wi pm2.27 syl9 ) ABCDFCDECDGH $.

    $( Commutation of antecedents.  Rotate right.  (Contributed by NM,
       25-Apr-1994.) $)
    com3r $p |- ( ch -> ( ph -> ( ps -> th ) ) ) $=
      ( wi com23 com12 ) ACBDFABCDEGH $.

    $( Commutation of antecedents.  Swap 1st and 3rd.  (Contributed by NM,
       25-Apr-1994.)  (Proof shortened by Wolf Lammen, 28-Jul-2012.) $)
    com13 $p |- ( ch -> ( ps -> ( ph -> th ) ) ) $=
      ( com3r com23 ) CABDABCDEFG $.

    $( Commutation of antecedents.  Rotate left.  (Contributed by NM,
       25-Apr-1994.)  (Proof shortened by Wolf Lammen, 28-Jul-2012.) $)
    com3l $p |- ( ps -> ( ch -> ( ph -> th ) ) ) $=
      ( com3r ) CABDABCDEFF $.
  $}

  $( Swap antecedents.  Theorem *2.04 of [WhiteheadRussell] p. 100.
     (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen,
     12-Sep-2012.) $)
  pm2.04 $p |- ( ( ph -> ( ps -> ch ) ) -> ( ps -> ( ph -> ch ) ) ) $=
    ( wi id com23 ) ABCDDZABCGEF $.

  ${
    com4.1 $e |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $.
    $( Commutation of antecedents.  Swap 3rd and 4th.  (Contributed by NM,
       25-Apr-1994.) $)
    com34 $p |- ( ph -> ( ps -> ( th -> ( ch -> ta ) ) ) ) $=
      ( wi pm2.04 syl6 ) ABCDEGGDCEGGFCDEHI $.

    $( Commutation of antecedents.  Rotate left.  (Contributed by NM,
       25-Apr-1994.)  (Proof shortened by O'Cat, 15-Aug-2004.) $)
    com4l $p |- ( ps -> ( ch -> ( th -> ( ph -> ta ) ) ) ) $=
      ( wi com3l com34 ) BCADEABCDEGFHI $.

    $( Commutation of antecedents.  Rotate twice.  (Contributed by NM,
       25-Apr-1994.) $)
    com4t $p |- ( ch -> ( th -> ( ph -> ( ps -> ta ) ) ) ) $=
      ( com4l ) BCDAEABCDEFGG $.

    $( Commutation of antecedents.  Rotate right.  (Contributed by NM,
       25-Apr-1994.) $)
    com4r $p |- ( th -> ( ph -> ( ps -> ( ch -> ta ) ) ) ) $=
      ( com4t com4l ) CDABEABCDEFGH $.

    $( Commutation of antecedents.  Swap 2nd and 4th.  (Contributed by NM,
       25-Apr-1994.)  (Proof shortened by Wolf Lammen, 28-Jul-2012.) $)
    com24 $p |- ( ph -> ( th -> ( ch -> ( ps -> ta ) ) ) ) $=
      ( wi com4t com13 ) CDABEGABCDEFHI $.

    $( Commutation of antecedents.  Swap 1st and 4th.  (Contributed by NM,
       25-Apr-1994.)  (Proof shortened by Wolf Lammen, 28-Jul-2012.) $)
    com14 $p |- ( th -> ( ps -> ( ch -> ( ph -> ta ) ) ) ) $=
      ( wi com4l com3r ) BCDAEGABCDEFHI $.
  $}

  ${
    com5.1 $e |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $.
    $( Commutation of antecedents.  Swap 4th and 5th.  (Contributed by Jeff
       Hankins, 28-Jun-2009.) $)
    com45 $p |- ( ph -> ( ps -> ( ch -> ( ta -> ( th -> et ) ) ) ) ) $=
      ( wi pm2.04 syl8 ) ABCDEFHHEDFHHGDEFIJ $.

    $( Commutation of antecedents.  Swap 3rd and 5th.  (Contributed by Jeff
       Hankins, 28-Jun-2009.) $)
    com35 $p |- ( ph -> ( ps -> ( ta -> ( th -> ( ch -> et ) ) ) ) ) $=
      ( wi com34 com45 ) ABDECFHABDCEFABCDEFHGIJI $.

    $( Commutation of antecedents.  Swap 2nd and 5th.  (Contributed by Jeff
       Hankins, 28-Jun-2009.) $)
    com25 $p |- ( ph -> ( ta -> ( ch -> ( th -> ( ps -> et ) ) ) ) ) $=
      ( wi com24 com45 ) ADCEBFHADCBEFABCDEFHGIJI $.

    $( Commutation of antecedents.  Rotate left.  (Contributed by Jeff Hankins,
       28-Jun-2009.)  (Proof shortened by Wolf Lammen, 29-Jul-2012.) $)
    com5l $p |- ( ps -> ( ch -> ( th -> ( ta -> ( ph -> et ) ) ) ) ) $=
      ( wi com4l com45 ) BCDAEFABCDEFHGIJ $.

    $( Commutation of antecedents.  Swap 1st and 5th.  (Contributed by Jeff
       Hankins, 28-Jun-2009.)  (Proof shortened by Wolf Lammen,
       29-Jul-2012.) $)
    com15 $p |- ( ta -> ( ps -> ( ch -> ( th -> ( ph -> et ) ) ) ) ) $=
      ( wi com5l com4r ) BCDEAFHABCDEFGIJ $.

    $( Commutation of antecedents.  Rotate left twice.  (Contributed by Jeff
       Hankins, 28-Jun-2009.) $)
    com52l $p |- ( ch -> ( th -> ( ta -> ( ph -> ( ps -> et ) ) ) ) ) $=
      ( com5l ) BCDEAFABCDEFGHH $.

    $( Commutation of antecedents.  Rotate right twice.  (Contributed by Jeff
       Hankins, 28-Jun-2009.) $)
    com52r $p |- ( th -> ( ta -> ( ph -> ( ps -> ( ch -> et ) ) ) ) ) $=
      ( com52l com5l ) CDEABFABCDEFGHI $.

    $( Commutation of antecedents.  Rotate right.  (Contributed by Wolf Lammen,
       29-Jul-2012.) $)
    com5r $p |- ( ta -> ( ph -> ( ps -> ( ch -> ( th -> et ) ) ) ) ) $=
      ( com52l ) CDEABFABCDEFGHH $.
  $}

  $( Elimination of a nested antecedent.  (Contributed by Wolf Lammen,
     9-May-2013.) $)
  jarr $p |- ( ( ( ph -> ps ) -> ch ) -> ( ps -> ch ) ) $=
    ( wi ax-1 imim1i ) BABDCBAEF $.

  ${
    jarri.1 $e |- ( ( ph -> ps ) -> ch ) $.
    $( Inference associated with ~ jarr .  (Contributed by Wolf Lammen,
       20-Sep-2013.) $)
    jarri $p |- ( ps -> ch ) $=
      ( wi ax-1 syl ) BABECBAFDG $.
  $}

  ${
    pm2.86i.1 $e |- ( ( ph -> ps ) -> ( ph -> ch ) ) $.
    $( Inference based on ~ pm2.86 .  (Contributed by NM, 5-Aug-1993.)  (Proof
       shortened by Wolf Lammen, 3-Apr-2013.) $)
    pm2.86i $p |- ( ph -> ( ps -> ch ) ) $=
      ( wi ax-1 syl com12 ) BACBABEACEBAFDGH $.
  $}

  ${
    pm2.86d.1 $e |- ( ph -> ( ( ps -> ch ) -> ( ps -> th ) ) ) $.
    $( Deduction based on ~ pm2.86 .  (Contributed by NM, 29-Jun-1995.)  (Proof
       shortened by Wolf Lammen, 3-Apr-2013.) $)
    pm2.86d $p |- ( ph -> ( ps -> ( ch -> th ) ) ) $=
      ( wi ax-1 syl5 com23 ) ACBDCBCFABDFCBGEHI $.
  $}

  $( Converse of Axiom ~ ax-2 .  Theorem *2.86 of [WhiteheadRussell] p. 108.
     (Contributed by NM, 25-Apr-1994.)  (Proof shortened by Wolf Lammen,
     3-Apr-2013.) $)
  pm2.86 $p |- ( ( ( ph -> ps ) -> ( ph -> ch ) ) ->
              ( ph -> ( ps -> ch ) ) ) $=
    ( wi id pm2.86d ) ABDACDDZABCGEF $.

  $( The Linearity Axiom of the infinite-valued sentential logic (L-infinity)
     of Lukasiewicz.  (Contributed by O'Cat, 12-Aug-2004.) $)
  loolin $p |- ( ( ( ph -> ps ) -> ( ps -> ph ) ) -> ( ps -> ph ) ) $=
    ( wi jarr pm2.43d ) ABCBACZCBAABFDE $.

  $( An alternate for the Linearity Axiom of the infinite-valued sentential
     logic (L-infinity) of Lukasiewicz, due to Barbara Wozniakowska, _Reports
     on Mathematical Logic_ 10, 129-137 (1978).  (Contributed by O'Cat,
     8-Aug-2004.) $)
  loowoz $p |- ( ( ( ph -> ps ) -> ( ph -> ch ) ) ->
                 ( ( ps -> ph ) -> ( ps -> ch ) ) ) $=
    ( wi jarr a2d ) ABDACDZDBACABGEF $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Logical conjunction and logical equivalence
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Declare connectives for conjunction ('and') and biconditional. $)
  $c /\ $. $( Wedge (read:  'and') $)
  $c <-> $. $( Double arrow (read:  'if and only if' or
               'is logically equivalent to') $)

  $( Extend wff definition to include conjunction ('and'). $)
  wa $a wff ( ph /\ ps ) $.

  $( Extend our wff definition to include the biconditional connective. $)
  wb $a wff ( ph <-> ps ) $.

  $( Left 'and' elimination.  One of the axioms of propositional logic.  Use
     its alias ~ simpl instead for naming consistency with set.mm.
     (New usage is discouraged.)  (Contributed by Mario Carneiro,
     31-Jan-2015.) $)
  ax-ia1 $a |- ( ( ph /\ ps ) -> ph ) $.

  $( Right 'and' elimination.  One of the axioms of propositional logic.
     (Contributed by Mario Carneiro, 31-Jan-2015.)  Use its alias ~ simpr
     instead for naming consistency with set.mm.
     (New usage is discouraged.) $)
  ax-ia2 $a |- ( ( ph /\ ps ) -> ps ) $.

  $( 'And' introduction.  One of the axioms of propositional logic.
     (Contributed by Mario Carneiro, 31-Jan-2015.) $)
  ax-ia3 $a |- ( ph -> ( ps -> ( ph /\ ps ) ) ) $.

  $( Elimination of a conjunct.  Theorem *3.26 (Simp) of [WhiteheadRussell]
     p. 112.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf
     Lammen, 13-Nov-2012.) $)
  simpl $p |- ( ( ph /\ ps ) -> ph ) $=
    ( ax-ia1 ) ABC $.

  $( Elimination of a conjunct.  Theorem *3.27 (Simp) of [WhiteheadRussell]
     p. 112.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf
     Lammen, 13-Nov-2012.) $)
  simpr $p |- ( ( ph /\ ps ) -> ps ) $=
    ( ax-ia2 ) ABC $.

  ${
    simpli.1 $e |- ( ph /\ ps ) $.
    $( Inference eliminating a conjunct.  (Contributed by NM, 15-Jun-1994.) $)
    simpli $p |- ph $=
      ( wa simpl ax-mp ) ABDACABEF $.
  $}

  ${
    simpld.1 $e |- ( ph -> ( ps /\ ch ) ) $.
    $( Deduction eliminating a conjunct.  (Contributed by NM, 5-Aug-1993.) $)
    simpld $p |- ( ph -> ps ) $=
      ( wa simpl syl ) ABCEBDBCFG $.
  $}

  ${
    simpri.1 $e |- ( ph /\ ps ) $.
    $( Inference eliminating a conjunct.  (Contributed by NM, 15-Jun-1994.) $)
    simpri $p |- ps $=
      ( wa simpr ax-mp ) ABDBCABEF $.
  $}

  ${
    simprd.1 $e |- ( ph -> ( ps /\ ch ) ) $.
    $( Deduction eliminating a conjunct.  (Contributed by NM, 5-Aug-1993.)
       (Proof shortened by Wolf Lammen, 3-Oct-2013.) $)
    simprd $p |- ( ph -> ch ) $=
      ( wa simpr syl ) ABCECDBCFG $.
  $}

  ${
    exp.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( Exportation inference.  (This theorem used to be labeled "exp" but was
       changed to "ex" so as not to conflict with the math token "exp", per the
       June 2006 Metamath spec change.)  (Contributed by NM, 5-Aug-1993.)
       (Proof shortened by Eric Schmidt, 22-Dec-2006.) $)
    ex $p |- ( ph -> ( ps -> ch ) ) $=
      ( wa ax-ia3 syl6 ) ABABECABFDG $.

    $( Exportation inference with commuted antecedents.  (Contributed by NM,
       25-May-2005.) $)
    expcom $p |- ( ps -> ( ph -> ch ) ) $=
      ( ex com12 ) ABCABCDEF $.
  $}

  $( This is our first definition, which introduces and defines the
     biconditional connective ` <-> ` , also called biimplication.  We define a
     wff of the form ` ( ph <-> ps ) ` as an abbreviation for
     ` ( ( ph -> ps ) /\ ( ps -> ph ) ) ` .

     Unlike most traditional developments, we have chosen not to have a
     separate symbol such as "Df." to mean "is defined as."  Instead, we will
     later use the biconditional connective for this purpose, as it allows us
     to use logic to manipulate definitions directly.  For an example of such a
     definition, see ~ df-3or .  This greatly simplifies many proofs since it
     eliminates the need for a separate mechanism for introducing and
     eliminating definitions.  Of course, we cannot use this mechanism to
     define the biconditional itself, since it hasn't been introduced yet.
     Instead, we use a more general form of definition, described as follows.

     In its most general form, a definition is simply an assertion that
     introduces a new symbol (or a new combination of existing symbols, as in
     ~ df-3an ) that is eliminable and does not strengthen the existing
     language.  The latter requirement means that the set of provable
     statements not containing the new symbol (or new combination) should
     remain exactly the same after the definition is introduced.  Our
     definition of the biconditional may look unusual compared to most
     definitions, but it strictly satisfies these requirements.

     The justification for our definition is that if we mechanically replace
     ` ( ph <-> ps ) ` (the definiendum i.e. the thing being defined) with
     ` ( ( ph -> ps ) /\ ( ps -> ph ) ) ` (the definiens i.e. the defining
     expression) in the definition, the definition becomes the previously
     proved theorem ~ biijust .  It is impossible to use ~ df-bi to prove any
     statement expressed in the original language that can't be proved from the
     original axioms, because if we simply replace each instance of ~ df-bi in
     the proof with the corresponding ~ biijust instance, we will end up with a
     proof from the original axioms.

     Note that from Metamath's point of view, a definition is just another
     axiom - i.e. an assertion we claim to be true - but from our high level
     point of view, we are are not strengthening the language.  To indicate
     this fact, we prefix definition labels with "df-" instead of "ax-".  (This
     prefixing is an informal convention that means nothing to the Metamath
     proof verifier; it is just for human readability.)

     ~ df-bi itself is a conjunction of two implications (to avoid using the
     biconditional in its own definition), but once we have the biconditional,
     we can prove ~ dfbi2 which uses the biconditional instead.

     Other definitions of the biconditional, such as ~ dfbi3dc , only hold for
     decidable propositions, not all propositions.  (Contributed by NM,
     5-Aug-1993.)  (Revised by Jim Kingdon, 24-Nov-2017.) $)
  df-bi $a |- ( ( ( ph <-> ps ) -> ( ( ph -> ps ) /\ ( ps -> ph ) ) )
        /\ ( ( ( ph -> ps ) /\ ( ps -> ph ) ) -> ( ph <-> ps ) ) ) $.

  $( Property of the biconditional connective.  (Contributed by NM,
     11-May-1999.)  (Revised by NM, 31-Jan-2015.) $)
  biimp $p |- ( ( ph <-> ps ) -> ( ph -> ps ) ) $=
    ( wb wi wa df-bi simpli simpld ) ABCZABDZBADZIJKEZDLIDABFGH $.

  $( Property of the biconditional connective.  (Contributed by NM,
     11-May-1999.) $)
  bi3 $p |- ( ( ph -> ps ) -> ( ( ps -> ph ) -> ( ph <-> ps ) ) ) $=
    ( wi wb wa df-bi simpri ex ) ABCZBACZABDZKIJEZCLKCABFGH $.

  ${
    biimpi.1 $e |- ( ph <-> ps ) $.
    $( Infer an implication from a logical equivalence.  (Contributed by NM,
       5-Aug-1993.) $)
    biimpi $p |- ( ph -> ps ) $=
      ( wb wi biimp ax-mp ) ABDABECABFG $.
  $}

  ${
    sylbi.1 $e |- ( ph <-> ps ) $.
    sylbi.2 $e |- ( ps -> ch ) $.
    $( A mixed syllogism inference from a biconditional and an implication.
       Useful for substituting an antecedent with a definition.  (Contributed
       by NM, 3-Jan-1993.) $)
    sylbi $p |- ( ph -> ch ) $=
      ( biimpi syl ) ABCABDFEG $.
  $}

  ${
    sylib.1 $e |- ( ph -> ps ) $.
    sylib.2 $e |- ( ps <-> ch ) $.
    $( A mixed syllogism inference from an implication and a biconditional.
       (Contributed by NM, 3-Jan-1993.) $)
    sylib $p |- ( ph -> ch ) $=
      ( biimpi syl ) ABCDBCEFG $.
  $}

  ${
    sylbb.1 $e |- ( ph <-> ps ) $.
    sylbb.2 $e |- ( ps <-> ch ) $.
    $( A mixed syllogism inference from two biconditionals.  (Contributed by
       BJ, 30-Mar-2019.) $)
    sylbb $p |- ( ph -> ch ) $=
      ( biimpi sylbi ) ABCDBCEFG $.
  $}

  ${
    imp.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Importation inference.  (Contributed by NM, 5-Aug-1993.)  (Proof
       shortened by Eric Schmidt, 22-Dec-2006.) $)
    imp $p |- ( ( ph /\ ps ) -> ch ) $=
      ( wa simpl simpr sylc ) ABEABCABFABGDH $.

    $( Importation inference with commuted antecedents.  (Contributed by NM,
       25-May-2005.) $)
    impcom $p |- ( ( ps /\ ph ) -> ch ) $=
      ( com12 imp ) BACABCDEF $.
  $}

  ${
    impbii.1 $e |- ( ph -> ps ) $.
    impbii.2 $e |- ( ps -> ph ) $.
    $( Infer an equivalence from an implication and its converse.  (Contributed
       by NM, 5-Aug-1993.) $)
    impbii $p |- ( ph <-> ps ) $=
      ( wi wb bi3 mp2 ) ABEBAEABFCDABGH $.
  $}

  ${
    impbidd.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    impbidd.2 $e |- ( ph -> ( ps -> ( th -> ch ) ) ) $.
    $( Deduce an equivalence from two implications.  (Contributed by Rodolfo
       Medina, 12-Oct-2010.) $)
    impbidd $p |- ( ph -> ( ps -> ( ch <-> th ) ) ) $=
      ( wi wb bi3 syl6c ) ABCDGDCGCDHEFCDIJ $.
  $}

  ${
    impbid21d.1 $e |- ( ps -> ( ch -> th ) ) $.
    impbid21d.2 $e |- ( ph -> ( th -> ch ) ) $.
    $( Deduce an equivalence from two implications.  (Contributed by Wolf
       Lammen, 12-May-2013.) $)
    impbid21d $p |- ( ph -> ( ps -> ( ch <-> th ) ) ) $=
      ( wi a1i a1d impbidd ) ABCDBCDGGAEHADCGBFIJ $.
  $}

  ${
    impbid.1 $e |- ( ph -> ( ps -> ch ) ) $.
    impbid.2 $e |- ( ph -> ( ch -> ps ) ) $.
    $( Deduce an equivalence from two implications.  (Contributed by NM,
       5-Aug-1993.)  (Revised by Wolf Lammen, 3-Nov-2012.) $)
    impbid $p |- ( ph -> ( ps <-> ch ) ) $=
      ( wb impbid21d pm2.43i ) ABCFAABCDEGH $.
  $}

  $( Property of the biconditional connective.  (Contributed by NM,
     11-May-1999.)  (Proof shortened by Wolf Lammen, 11-Nov-2012.) $)
  biimpr $p |- ( ( ph <-> ps ) -> ( ps -> ph ) ) $=
    ( wb wi wa df-bi simpli simprd ) ABCZABDZBADZIJKEZDLIDABFGH $.

  $( Commutative law for equivalence.  (Contributed by Wolf Lammen,
     10-Nov-2012.) $)
  bicom1 $p |- ( ( ph <-> ps ) -> ( ps <-> ph ) ) $=
    ( wb biimpr biimp impbid ) ABCBAABDABEF $.

  ${
    bicomi.1 $e |- ( ph <-> ps ) $.
    $( Inference from commutative law for logical equivalence.  (Contributed by
       NM, 5-Aug-1993.)  (Revised by NM, 16-Sep-2013.) $)
    bicomi $p |- ( ps <-> ph ) $=
      ( wb bicom1 ax-mp ) ABDBADCABEF $.
  $}

  ${
    biimpri.1 $e |- ( ph <-> ps ) $.
    $( Infer a converse implication from a logical equivalence.  (Contributed
       by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen, 16-Sep-2013.) $)
    biimpri $p |- ( ps -> ph ) $=
      ( bicomi biimpi ) BAABCDE $.
  $}

  ${
    sylibr.1 $e |- ( ph -> ps ) $.
    sylibr.2 $e |- ( ch <-> ps ) $.
    $( A mixed syllogism inference from an implication and a biconditional.
       Useful for substituting a consequent with a definition.  (Contributed by
       NM, 5-Aug-1993.) $)
    sylibr $p |- ( ph -> ch ) $=
      ( biimpri syl ) ABCDCBEFG $.
  $}

  ${
    sylbir.1 $e |- ( ps <-> ph ) $.
    sylbir.2 $e |- ( ps -> ch ) $.
    $( A mixed syllogism inference from a biconditional and an implication.
       (Contributed by NM, 5-Aug-1993.) $)
    sylbir $p |- ( ph -> ch ) $=
      ( biimpri syl ) ABCBADFEG $.
  $}

  ${
    sylbbr.1 $e |- ( ph <-> ps ) $.
    sylbbr.2 $e |- ( ps <-> ch ) $.
    $( A mixed syllogism inference from two biconditionals.

       Note on the various syllogism-like statements in set.mm.  The
       hypothetical syllogism ~ syl infers an implication from two implications
       (and there are ~ 3syl and ~ 4syl for chaining more inferences).  There
       are four inferences inferring an implication from one implication and
       one biconditional: ~ sylbi , ~ sylib , ~ sylbir , ~ sylibr ; four
       inferences inferring an implication from two biconditionals: ~ sylbb ,
       ~ sylbbr , ~ sylbb1 , ~ sylbb2 ; four inferences inferring a
       biconditional from two biconditionals: ~ bitri , ~ bitr2i , ~ bitr3i ,
       ~ bitr4i (and more for chaining more biconditionals).  There are also
       closed forms and deduction versions of these, like, among many others,
       ~ syld , ~ syl5 , ~ syl6 , ~ mpbid , ~ bitrd , ~ bitrid , ~ bitrdi and
       variants.  (Contributed by BJ, 21-Apr-2019.) $)
    sylbbr $p |- ( ch -> ph ) $=
      ( biimpri sylibr ) CBABCEFDG $.
  $}

  ${
    sylbb1.1 $e |- ( ph <-> ps ) $.
    sylbb1.2 $e |- ( ph <-> ch ) $.
    $( A mixed syllogism inference from two biconditionals.  (Contributed by
       BJ, 21-Apr-2019.) $)
    sylbb1 $p |- ( ps -> ch ) $=
      ( biimpri sylib ) BACABDFEG $.
  $}

  ${
    sylbb2.1 $e |- ( ph <-> ps ) $.
    sylbb2.2 $e |- ( ch <-> ps ) $.
    $( A mixed syllogism inference from two biconditionals.  (Contributed by
       BJ, 21-Apr-2019.) $)
    sylbb2 $p |- ( ph -> ch ) $=
      ( biimpri sylbi ) ABCDCBEFG $.
  $}

  $( Join antecedents with conjunction.  Theorem *3.2 of [WhiteheadRussell]
     p. 111.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf
     Lammen, 12-Nov-2012.)  (Proof shortened by Jia Ming, 17-Nov-2020.) $)
  pm3.2 $p |- ( ph -> ( ps -> ( ph /\ ps ) ) ) $=
    ( ax-ia3 ) ABC $.

  $( Commutative law for equivalence.  Theorem *4.21 of [WhiteheadRussell]
     p. 117.  (Contributed by NM, 5-Aug-1993.)  (Revised by NM,
     11-Nov-2012.) $)
  bicom $p |- ( ( ph <-> ps ) <-> ( ps <-> ph ) ) $=
    ( wb bicom1 impbii ) ABCBACABDBADE $.

  ${
    bicomd.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Commute two sides of a biconditional in a deduction.  (Contributed by
       NM, 5-Aug-1993.) $)
    bicomd $p |- ( ph -> ( ch <-> ps ) ) $=
      ( wb bicom sylib ) ABCECBEDBCFG $.
  $}

  ${
    impbid1.1 $e |- ( ph -> ( ps -> ch ) ) $.
    impbid1.2 $e |- ( ch -> ps ) $.
    $( Infer an equivalence from two implications.  (Contributed by NM,
       6-Mar-2007.) $)
    impbid1 $p |- ( ph -> ( ps <-> ch ) ) $=
      ( wi a1i impbid ) ABCDCBFAEGH $.
  $}

  ${
    impbid2.1 $e |- ( ps -> ch ) $.
    impbid2.2 $e |- ( ph -> ( ch -> ps ) ) $.
    $( Infer an equivalence from two implications.  (Contributed by NM,
       6-Mar-2007.)  (Proof shortened by Wolf Lammen, 27-Sep-2013.) $)
    impbid2 $p |- ( ph -> ( ps <-> ch ) ) $=
      ( impbid1 bicomd ) ACBACBEDFG $.
  $}

  ${
    biimpd.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Deduce an implication from a logical equivalence.  (Contributed by NM,
       5-Aug-1993.) $)
    biimpd $p |- ( ph -> ( ps -> ch ) ) $=
      ( wb wi biimp syl ) ABCEBCFDBCGH $.
  $}

  ${
    mpbi.min $e |- ph $.
    mpbi.maj $e |- ( ph <-> ps ) $.
    $( An inference from a biconditional, related to modus ponens.
       (Contributed by NM, 5-Aug-1993.) $)
    mpbi $p |- ps $=
      ( biimpi ax-mp ) ABCABDEF $.
  $}

  ${
    mpbir.min $e |- ps $.
    mpbir.maj $e |- ( ph <-> ps ) $.
    $( An inference from a biconditional, related to modus ponens.
       (Contributed by NM, 5-Aug-1993.) $)
    mpbir $p |- ph $=
      ( biimpri ax-mp ) BACABDEF $.
  $}

  ${
    mpbid.min $e |- ( ph -> ps ) $.
    mpbid.maj $e |- ( ph -> ( ps <-> ch ) ) $.
    $( A deduction from a biconditional, related to modus ponens.  (Contributed
       by NM, 5-Aug-1993.) $)
    mpbid $p |- ( ph -> ch ) $=
      ( biimpd mpd ) ABCDABCEFG $.
  $}

  ${
    mpbii.min $e |- ps $.
    mpbii.maj $e |- ( ph -> ( ps <-> ch ) ) $.
    $( An inference from a nested biconditional, related to modus ponens.
       (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen,
       25-Oct-2012.) $)
    mpbii $p |- ( ph -> ch ) $=
      ( a1i mpbid ) ABCBADFEG $.
  $}

  ${
    sylibd.1 $e |- ( ph -> ( ps -> ch ) ) $.
    sylibd.2 $e |- ( ph -> ( ch <-> th ) ) $.
    $( A syllogism deduction.  (Contributed by NM, 3-Aug-1994.) $)
    sylibd $p |- ( ph -> ( ps -> th ) ) $=
      ( biimpd syld ) ABCDEACDFGH $.
  $}

  ${
    sylbid.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    sylbid.2 $e |- ( ph -> ( ch -> th ) ) $.
    $( A syllogism deduction.  (Contributed by NM, 3-Aug-1994.) $)
    sylbid $p |- ( ph -> ( ps -> th ) ) $=
      ( biimpd syld ) ABCDABCEGFH $.
  $}

  ${
    mpbidi.min $e |- ( th -> ( ph -> ps ) ) $.
    mpbidi.maj $e |- ( ph -> ( ps <-> ch ) ) $.
    $( A deduction from a biconditional, related to modus ponens.  (Contributed
       by NM, 9-Aug-1994.) $)
    mpbidi $p |- ( th -> ( ph -> ch ) ) $=
      ( biimpd sylcom ) DABCEABCFGH $.
  $}

  ${
    biimtrid.1 $e |- ( ph <-> ps ) $.
    biimtrid.2 $e |- ( ch -> ( ps -> th ) ) $.
    $( A mixed syllogism inference from a nested implication and a
       biconditional.  Useful for substituting an embedded antecedent with a
       definition.  (Contributed by NM, 5-Aug-1993.) $)
    biimtrid $p |- ( ch -> ( ph -> th ) ) $=
      ( biimpi syl5 ) ABCDABEGFH $.
  $}

  ${
    biimtrrid.1 $e |- ( ps <-> ph ) $.
    biimtrrid.2 $e |- ( ch -> ( ps -> th ) ) $.
    $( A mixed syllogism inference from a nested implication and a
       biconditional.  (Contributed by NM, 5-Aug-1993.) $)
    biimtrrid $p |- ( ch -> ( ph -> th ) ) $=
      ( biimpri syl5 ) ABCDBAEGFH $.
  $}

  ${
    imbitrid.1 $e |- ( ph -> ps ) $.
    imbitrid.2 $e |- ( ch -> ( ps <-> th ) ) $.
    $( A mixed syllogism inference.  (Contributed by NM, 12-Jan-1993.) $)
    imbitrid $p |- ( ch -> ( ph -> th ) ) $=
      ( biimpd syl5 ) ABCDECBDFGH $.

    $( A mixed syllogism inference.  (Contributed by NM, 19-Jun-2007.) $)
    syl5ibcom $p |- ( ph -> ( ch -> th ) ) $=
      ( imbitrid com12 ) CADABCDEFGH $.
  $}

  ${
    imbitrrid.1 $e |- ( ph -> th ) $.
    imbitrrid.2 $e |- ( ch -> ( ps <-> th ) ) $.
    $( A mixed syllogism inference.  (Contributed by NM, 3-Apr-1994.)  (Revised
       by NM, 22-Sep-2013.) $)
    imbitrrid $p |- ( ch -> ( ph -> ps ) ) $=
      ( bicomd imbitrid ) ADCBECBDFGH $.

    $( A mixed syllogism inference.  (Contributed by NM, 20-Jun-2007.) $)
    syl5ibrcom $p |- ( ph -> ( ch -> ps ) ) $=
      ( imbitrrid com12 ) CABABCDEFGH $.
  $}

  ${
    biimprd.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Deduce a converse implication from a logical equivalence.  (Contributed
       by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen, 22-Sep-2013.) $)
    biimprd $p |- ( ph -> ( ch -> ps ) ) $=
      ( id imbitrrid ) CBACCEDF $.
  $}

  ${
    biimpcd.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Deduce a commuted implication from a logical equivalence.  (Contributed
       by NM, 3-May-1994.)  (Proof shortened by Wolf Lammen, 22-Sep-2013.) $)
    biimpcd $p |- ( ps -> ( ph -> ch ) ) $=
      ( id syl5ibcom ) BBACBEDF $.

    $( Deduce a converse commuted implication from a logical equivalence.
       (Contributed by NM, 3-May-1994.)  (Proof shortened by Wolf Lammen,
       20-Dec-2013.) $)
    biimprcd $p |- ( ch -> ( ph -> ps ) ) $=
      ( id syl5ibrcom ) CBACCEDF $.
  $}

  ${
    imbitrdi.1 $e |- ( ph -> ( ps -> ch ) ) $.
    imbitrdi.2 $e |- ( ch <-> th ) $.
    $( A mixed syllogism inference from a nested implication and a
       biconditional.  (Contributed by NM, 5-Aug-1993.) $)
    imbitrdi $p |- ( ph -> ( ps -> th ) ) $=
      ( biimpi syl6 ) ABCDECDFGH $.
  $}

  ${
    imbitrrdi.1 $e |- ( ph -> ( ps -> ch ) ) $.
    imbitrrdi.2 $e |- ( th <-> ch ) $.
    $( A mixed syllogism inference from a nested implication and a
       biconditional.  Useful for substituting an embedded consequent with a
       definition.  (Contributed by NM, 5-Aug-1993.) $)
    imbitrrdi $p |- ( ph -> ( ps -> th ) ) $=
      ( biimpri syl6 ) ABCDEDCFGH $.
  $}

  ${
    biimtrdi.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    biimtrdi.2 $e |- ( ch -> th ) $.
    $( A mixed syllogism inference.  (Contributed by NM, 2-Jan-1994.) $)
    biimtrdi $p |- ( ph -> ( ps -> th ) ) $=
      ( biimpd syl6 ) ABCDABCEGFH $.
  $}

  ${
    biimtrrdi.1 $e |- ( ph -> ( ch <-> ps ) ) $.
    biimtrrdi.2 $e |- ( ch -> th ) $.
    $( A mixed syllogism inference.  (Contributed by NM, 18-May-1994.) $)
    biimtrrdi $p |- ( ph -> ( ps -> th ) ) $=
      ( biimprd syl6 ) ABCDACBEGFH $.
  $}

  ${
    syl7bi.1 $e |- ( ph <-> ps ) $.
    syl7bi.2 $e |- ( ch -> ( th -> ( ps -> ta ) ) ) $.
    $( A mixed syllogism inference from a doubly nested implication and a
       biconditional.  (Contributed by NM, 5-Aug-1993.) $)
    syl7bi $p |- ( ch -> ( th -> ( ph -> ta ) ) ) $=
      ( biimpi syl7 ) ABCDEABFHGI $.
  $}

  ${
    syl8ib.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    syl8ib.2 $e |- ( th <-> ta ) $.
    $( A syllogism rule of inference.  The second premise is used to replace
       the consequent of the first premise.  (Contributed by NM,
       1-Aug-1994.) $)
    syl8ib $p |- ( ph -> ( ps -> ( ch -> ta ) ) ) $=
      ( biimpi syl8 ) ABCDEFDEGHI $.
  $}

  ${
    mpbird.min $e |- ( ph -> ch ) $.
    mpbird.maj $e |- ( ph -> ( ps <-> ch ) ) $.
    $( A deduction from a biconditional, related to modus ponens.  (Contributed
       by NM, 5-Aug-1993.) $)
    mpbird $p |- ( ph -> ps ) $=
      ( biimprd mpd ) ACBDABCEFG $.
  $}

  ${
    mpbiri.min $e |- ch $.
    mpbiri.maj $e |- ( ph -> ( ps <-> ch ) ) $.
    $( An inference from a nested biconditional, related to modus ponens.
       (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen,
       25-Oct-2012.) $)
    mpbiri $p |- ( ph -> ps ) $=
      ( a1i mpbird ) ABCCADFEG $.
  $}

  ${
    sylibrd.1 $e |- ( ph -> ( ps -> ch ) ) $.
    sylibrd.2 $e |- ( ph -> ( th <-> ch ) ) $.
    $( A syllogism deduction.  (Contributed by NM, 3-Aug-1994.) $)
    sylibrd $p |- ( ph -> ( ps -> th ) ) $=
      ( biimprd syld ) ABCDEADCFGH $.
  $}

  ${
    sylbird.1 $e |- ( ph -> ( ch <-> ps ) ) $.
    sylbird.2 $e |- ( ph -> ( ch -> th ) ) $.
    $( A syllogism deduction.  (Contributed by NM, 3-Aug-1994.) $)
    sylbird $p |- ( ph -> ( ps -> th ) ) $=
      ( biimprd syld ) ABCDACBEGFH $.
  $}

  $( Principle of identity for logical equivalence.  Theorem *4.2 of
     [WhiteheadRussell] p. 117.  (Contributed by NM, 5-Aug-1993.) $)
  biid $p |- ( ph <-> ph ) $=
    ( id impbii ) AAABZDC $.

  $( Principle of identity with antecedent.  (Contributed by NM,
     25-Nov-1995.) $)
  biidd $p |- ( ph -> ( ps <-> ps ) ) $=
    ( wb biid a1i ) BBCABDE $.

  $( Two propositions are equivalent if they are both true.  Closed form of
     ~ 2th .  Equivalent to a ~ biimp -like version of the xor-connective.
     This theorem stays true, no matter how you permute its operands.  This is
     evident from its sharper version ` ( ph <-> ( ps <-> ( ph <-> ps ) ) ) ` .
     (Contributed by Wolf Lammen, 12-May-2013.) $)
  pm5.1im $p |- ( ph -> ( ps -> ( ph <-> ps ) ) ) $=
    ( ax-1 impbid21d ) ABABBACABCD $.

  ${
    2th.1 $e |- ph $.
    2th.2 $e |- ps $.
    $( Two truths are equivalent.  (Contributed by NM, 18-Aug-1993.) $)
    2th $p |- ( ph <-> ps ) $=
      ( a1i impbii ) ABBADEABCEF $.
  $}

  ${
    2thd.1 $e |- ( ph -> ps ) $.
    2thd.2 $e |- ( ph -> ch ) $.
    $( Two truths are equivalent (deduction form).  (Contributed by NM,
       3-Jun-2012.)  (Revised by NM, 29-Jan-2013.) $)
    2thd $p |- ( ph -> ( ps <-> ch ) ) $=
      ( wb pm5.1im sylc ) ABCBCFDEBCGH $.
  $}

  ${
    ibi.1 $e |- ( ph -> ( ph <-> ps ) ) $.
    $( Inference that converts a biconditional implied by one of its arguments,
       into an implication.  (Contributed by NM, 17-Oct-2003.) $)
    ibi $p |- ( ph -> ps ) $=
      ( biimpd pm2.43i ) ABAABCDE $.
  $}

  ${
    ibir.1 $e |- ( ph -> ( ps <-> ph ) ) $.
    $( Inference that converts a biconditional implied by one of its arguments,
       into an implication.  (Contributed by NM, 22-Jul-2004.) $)
    ibir $p |- ( ph -> ps ) $=
      ( bicomd ibi ) ABABACDE $.
  $}

  ${
    ibd.1 $e |- ( ph -> ( ps -> ( ps <-> ch ) ) ) $.
    $( Deduction that converts a biconditional implied by one of its arguments,
       into an implication.  (Contributed by NM, 26-Jun-2004.) $)
    ibd $p |- ( ph -> ( ps -> ch ) ) $=
      ( wb biimp syli ) BABCECDBCFG $.
  $}

  $( Distribution of implication over biconditional.  Theorem *5.74 of
     [WhiteheadRussell] p. 126.  (Contributed by NM, 1-Aug-1994.)  (Proof
     shortened by Wolf Lammen, 11-Apr-2013.) $)
  pm5.74 $p |- ( ( ph -> ( ps <-> ch ) ) <->
               ( ( ph -> ps ) <-> ( ph -> ch ) ) ) $=
    ( wb wi biimp imim3i biimpr impbid pm2.86d impbidd impbii ) ABCDZEZABEZACEZ
    DZNOPMBCABCFGMCBABCHGIQABCQABCOPFJQACBOPHJKL $.

  ${
    pm5.74i.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Distribution of implication over biconditional (inference form).
       (Contributed by NM, 1-Aug-1994.) $)
    pm5.74i $p |- ( ( ph -> ps ) <-> ( ph -> ch ) ) $=
      ( wb wi pm5.74 mpbi ) ABCEFABFACFEDABCGH $.
  $}

  ${
    pm5.74ri.1 $e |- ( ( ph -> ps ) <-> ( ph -> ch ) ) $.
    $( Distribution of implication over biconditional (reverse inference form).
       (Contributed by NM, 1-Aug-1994.) $)
    pm5.74ri $p |- ( ph -> ( ps <-> ch ) ) $=
      ( wb wi pm5.74 mpbir ) ABCEFABFACFEDABCGH $.
  $}

  ${
    pm5.74d.1 $e |- ( ph -> ( ps -> ( ch <-> th ) ) ) $.
    $( Distribution of implication over biconditional (deduction form).
       (Contributed by NM, 21-Mar-1996.) $)
    pm5.74d $p |- ( ph -> ( ( ps -> ch ) <-> ( ps -> th ) ) ) $=
      ( wb wi pm5.74 sylib ) ABCDFGBCGBDGFEBCDHI $.
  $}

  ${
    pm5.74rd.1 $e |- ( ph -> ( ( ps -> ch ) <-> ( ps -> th ) ) ) $.
    $( Distribution of implication over biconditional (deduction form).
       (Contributed by NM, 19-Mar-1997.) $)
    pm5.74rd $p |- ( ph -> ( ps -> ( ch <-> th ) ) ) $=
      ( wi wb pm5.74 sylibr ) ABCFBDFGBCDGFEBCDHI $.
  $}

  ${
    bitri.1 $e |- ( ph <-> ps ) $.
    bitri.2 $e |- ( ps <-> ch ) $.
    $( An inference from transitive law for logical equivalence.  (Contributed
       by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen, 13-Oct-2012.) $)
    bitri $p |- ( ph <-> ch ) $=
      ( biimpi sylib biimpri sylibr impbii ) ACABCABDFEGCBABCEHDIJ $.
  $}

  ${
    bitr2i.1 $e |- ( ph <-> ps ) $.
    bitr2i.2 $e |- ( ps <-> ch ) $.
    $( An inference from transitive law for logical equivalence.  (Contributed
       by NM, 5-Aug-1993.) $)
    bitr2i $p |- ( ch <-> ph ) $=
      ( bitri bicomi ) ACABCDEFG $.
  $}

  ${
    bitr3i.1 $e |- ( ps <-> ph ) $.
    bitr3i.2 $e |- ( ps <-> ch ) $.
    $( An inference from transitive law for logical equivalence.  (Contributed
       by NM, 5-Aug-1993.) $)
    bitr3i $p |- ( ph <-> ch ) $=
      ( bicomi bitri ) ABCBADFEG $.
  $}

  ${
    bitr4i.1 $e |- ( ph <-> ps ) $.
    bitr4i.2 $e |- ( ch <-> ps ) $.
    $( An inference from transitive law for logical equivalence.  (Contributed
       by NM, 5-Aug-1993.) $)
    bitr4i $p |- ( ph <-> ch ) $=
      ( bicomi bitri ) ABCDCBEFG $.
  $}

  ${
    bitrd.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    bitrd.2 $e |- ( ph -> ( ch <-> th ) ) $.
    $( Deduction form of ~ bitri .  (Contributed by NM, 5-Aug-1993.)  (Proof
       shortened by Wolf Lammen, 14-Apr-2013.) $)
    bitrd $p |- ( ph -> ( ps <-> th ) ) $=
      ( wi pm5.74i bitri pm5.74ri ) ABDABGACGADGABCEHACDFHIJ $.
  $}

  ${
    bitr2d.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    bitr2d.2 $e |- ( ph -> ( ch <-> th ) ) $.
    $( Deduction form of ~ bitr2i .  (Contributed by NM, 9-Jun-2004.) $)
    bitr2d $p |- ( ph -> ( th <-> ps ) ) $=
      ( bitrd bicomd ) ABDABCDEFGH $.
  $}

  ${
    bitr3d.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    bitr3d.2 $e |- ( ph -> ( ps <-> th ) ) $.
    $( Deduction form of ~ bitr3i .  (Contributed by NM, 5-Aug-1993.) $)
    bitr3d $p |- ( ph -> ( ch <-> th ) ) $=
      ( bicomd bitrd ) ACBDABCEGFH $.
  $}

  ${
    bitr4d.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    bitr4d.2 $e |- ( ph -> ( th <-> ch ) ) $.
    $( Deduction form of ~ bitr4i .  (Contributed by NM, 5-Aug-1993.) $)
    bitr4d $p |- ( ph -> ( ps <-> th ) ) $=
      ( bicomd bitrd ) ABCDEADCFGH $.
  $}

  ${
    bitrid.1 $e |- ( ph <-> ps ) $.
    bitrid.2 $e |- ( ch -> ( ps <-> th ) ) $.
    $( A syllogism inference from two biconditionals.  (Contributed by NM,
       12-Mar-1993.) $)
    bitrid $p |- ( ch -> ( ph <-> th ) ) $=
      ( wb a1i bitrd ) CABDABGCEHFI $.
  $}

  ${
    bitr2id.1 $e |- ( ph <-> ps ) $.
    bitr2id.2 $e |- ( ch -> ( ps <-> th ) ) $.
    $( A syllogism inference from two biconditionals.  (Contributed by NM,
       5-Aug-1993.) $)
    bitr2id $p |- ( ch -> ( th <-> ph ) ) $=
      ( bitrid bicomd ) CADABCDEFGH $.
  $}

  ${
    bitr3id.1 $e |- ( ps <-> ph ) $.
    bitr3id.2 $e |- ( ch -> ( ps <-> th ) ) $.
    $( A syllogism inference from two biconditionals.  (Contributed by NM,
       5-Aug-1993.) $)
    bitr3id $p |- ( ch -> ( ph <-> th ) ) $=
      ( bicomi bitrid ) ABCDBAEGFH $.
  $}

  ${
    bitr3di.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    bitr3di.2 $e |- ( ps <-> th ) $.
    $( A syllogism inference from two biconditionals.  (Contributed by NM,
       25-Nov-1994.) $)
    bitr3di $p |- ( ph -> ( ch <-> th ) ) $=
      ( bicomi bitr2id ) DBACBDFGEH $.
  $}

  ${
    bitrdi.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    bitrdi.2 $e |- ( ch <-> th ) $.
    $( A syllogism inference from two biconditionals.  (Contributed by NM,
       5-Aug-1993.) $)
    bitrdi $p |- ( ph -> ( ps <-> th ) ) $=
      ( wb a1i bitrd ) ABCDECDGAFHI $.
  $}

  ${
    bitr2di.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    bitr2di.2 $e |- ( ch <-> th ) $.
    $( A syllogism inference from two biconditionals.  (Contributed by NM,
       5-Aug-1993.) $)
    bitr2di $p |- ( ph -> ( th <-> ps ) ) $=
      ( bitrdi bicomd ) ABDABCDEFGH $.
  $}

  ${
    bitr4di.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    bitr4di.2 $e |- ( th <-> ch ) $.
    $( A syllogism inference from two biconditionals.  (Contributed by NM,
       5-Aug-1993.) $)
    bitr4di $p |- ( ph -> ( ps <-> th ) ) $=
      ( bicomi bitrdi ) ABCDEDCFGH $.
  $}

  ${
    bitr4id.2 $e |- ( ps <-> ch ) $.
    bitr4id.1 $e |- ( ph -> ( th <-> ch ) ) $.
    $( A syllogism inference from two biconditionals.  (Contributed by NM,
       25-Nov-1994.) $)
    bitr4id $p |- ( ph -> ( ps <-> th ) ) $=
      ( bicomi bitr2di ) ADCBFBCEGH $.
  $}

  ${
    3imtr3.1 $e |- ( ph -> ps ) $.
    3imtr3.2 $e |- ( ph <-> ch ) $.
    3imtr3.3 $e |- ( ps <-> th ) $.
    $( A mixed syllogism inference, useful for removing a definition from both
       sides of an implication.  (Contributed by NM, 10-Aug-1994.) $)
    3imtr3i $p |- ( ch -> th ) $=
      ( sylbir sylib ) CBDCABFEHGI $.
  $}

  ${
    3imtr4.1 $e |- ( ph -> ps ) $.
    3imtr4.2 $e |- ( ch <-> ph ) $.
    3imtr4.3 $e |- ( th <-> ps ) $.
    $( A mixed syllogism inference, useful for applying a definition to both
       sides of an implication.  (Contributed by NM, 5-Aug-1993.) $)
    3imtr4i $p |- ( ch -> th ) $=
      ( sylbi sylibr ) CBDCABFEHGI $.
  $}

  ${
    3imtr3d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    3imtr3d.2 $e |- ( ph -> ( ps <-> th ) ) $.
    3imtr3d.3 $e |- ( ph -> ( ch <-> ta ) ) $.
    $( More general version of ~ 3imtr3i .  Useful for converting conditional
       definitions in a formula.  (Contributed by NM, 8-Apr-1996.) $)
    3imtr3d $p |- ( ph -> ( th -> ta ) ) $=
      ( sylibd sylbird ) ADBEGABCEFHIJ $.
  $}

  ${
    3imtr4d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    3imtr4d.2 $e |- ( ph -> ( th <-> ps ) ) $.
    3imtr4d.3 $e |- ( ph -> ( ta <-> ch ) ) $.
    $( More general version of ~ 3imtr4i .  Useful for converting conditional
       definitions in a formula.  (Contributed by NM, 26-Oct-1995.) $)
    3imtr4d $p |- ( ph -> ( th -> ta ) ) $=
      ( sylibrd sylbid ) ADBEGABCEFHIJ $.
  $}

  ${
    3imtr3g.1 $e |- ( ph -> ( ps -> ch ) ) $.
    3imtr3g.2 $e |- ( ps <-> th ) $.
    3imtr3g.3 $e |- ( ch <-> ta ) $.
    $( More general version of ~ 3imtr3i .  Useful for converting definitions
       in a formula.  (Contributed by NM, 20-May-1996.)  (Proof shortened by
       Wolf Lammen, 20-Dec-2013.) $)
    3imtr3g $p |- ( ph -> ( th -> ta ) ) $=
      ( biimtrrid imbitrdi ) ADCEDBACGFIHJ $.
  $}

  ${
    3imtr4g.1 $e |- ( ph -> ( ps -> ch ) ) $.
    3imtr4g.2 $e |- ( th <-> ps ) $.
    3imtr4g.3 $e |- ( ta <-> ch ) $.
    $( More general version of ~ 3imtr4i .  Useful for converting definitions
       in a formula.  (Contributed by NM, 20-May-1996.)  (Proof shortened by
       Wolf Lammen, 20-Dec-2013.) $)
    3imtr4g $p |- ( ph -> ( th -> ta ) ) $=
      ( biimtrid imbitrrdi ) ADCEDBACGFIHJ $.
  $}

  ${
    3bitri.1 $e |- ( ph <-> ps ) $.
    3bitri.2 $e |- ( ps <-> ch ) $.
    3bitri.3 $e |- ( ch <-> th ) $.
    $( A chained inference from transitive law for logical equivalence.
       (Contributed by NM, 5-Aug-1993.) $)
    3bitri $p |- ( ph <-> th ) $=
      ( bitri ) ABDEBCDFGHH $.

    $( A chained inference from transitive law for logical equivalence.
       (Contributed by NM, 4-Aug-2006.) $)
    3bitrri $p |- ( th <-> ph ) $=
      ( bitr2i bitr3i ) DCAGABCEFHI $.
  $}

  ${
    3bitr2i.1 $e |- ( ph <-> ps ) $.
    3bitr2i.2 $e |- ( ch <-> ps ) $.
    3bitr2i.3 $e |- ( ch <-> th ) $.
    $( A chained inference from transitive law for logical equivalence.
       (Contributed by NM, 4-Aug-2006.) $)
    3bitr2i $p |- ( ph <-> th ) $=
      ( bitr4i bitri ) ACDABCEFHGI $.

    $( A chained inference from transitive law for logical equivalence.
       (Contributed by NM, 4-Aug-2006.) $)
    3bitr2ri $p |- ( th <-> ph ) $=
      ( bitr4i bitr2i ) ACDABCEFHGI $.
  $}

  ${
    3bitr3i.1 $e |- ( ph <-> ps ) $.
    3bitr3i.2 $e |- ( ph <-> ch ) $.
    3bitr3i.3 $e |- ( ps <-> th ) $.
    $( A chained inference from transitive law for logical equivalence.
       (Contributed by NM, 19-Aug-1993.) $)
    3bitr3i $p |- ( ch <-> th ) $=
      ( bitr3i bitri ) CBDCABFEHGI $.

    $( A chained inference from transitive law for logical equivalence.
       (Contributed by NM, 5-Aug-1993.) $)
    3bitr3ri $p |- ( th <-> ch ) $=
      ( bitr3i ) DBCGBACEFHH $.
  $}

  ${
    3bitr4i.1 $e |- ( ph <-> ps ) $.
    3bitr4i.2 $e |- ( ch <-> ph ) $.
    3bitr4i.3 $e |- ( th <-> ps ) $.
    $( A chained inference from transitive law for logical equivalence.  This
       inference is frequently used to apply a definition to both sides of a
       logical equivalence.  (Contributed by NM, 5-Aug-1993.) $)
    3bitr4i $p |- ( ch <-> th ) $=
      ( bitr4i bitri ) CADFABDEGHI $.

    $( A chained inference from transitive law for logical equivalence.
       (Contributed by NM, 2-Sep-1995.) $)
    3bitr4ri $p |- ( th <-> ch ) $=
      ( bitr4i bitr2i ) CADFABDEGHI $.
  $}

  ${
    3bitrd.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    3bitrd.2 $e |- ( ph -> ( ch <-> th ) ) $.
    3bitrd.3 $e |- ( ph -> ( th <-> ta ) ) $.
    $( Deduction from transitivity of biconditional.  (Contributed by NM,
       13-Aug-1999.) $)
    3bitrd $p |- ( ph -> ( ps <-> ta ) ) $=
      ( bitrd ) ABDEABCDFGIHI $.

    $( Deduction from transitivity of biconditional.  (Contributed by NM,
       4-Aug-2006.) $)
    3bitrrd $p |- ( ph -> ( ta <-> ps ) ) $=
      ( bitr2d bitr3d ) ADEBHABCDFGIJ $.
  $}

  ${
    3bitr2d.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    3bitr2d.2 $e |- ( ph -> ( th <-> ch ) ) $.
    3bitr2d.3 $e |- ( ph -> ( th <-> ta ) ) $.
    $( Deduction from transitivity of biconditional.  (Contributed by NM,
       4-Aug-2006.) $)
    3bitr2d $p |- ( ph -> ( ps <-> ta ) ) $=
      ( bitr4d bitrd ) ABDEABCDFGIHJ $.

    $( Deduction from transitivity of biconditional.  (Contributed by NM,
       4-Aug-2006.) $)
    3bitr2rd $p |- ( ph -> ( ta <-> ps ) ) $=
      ( bitr4d bitr2d ) ABDEABCDFGIHJ $.
  $}

  ${
    3bitr3d.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    3bitr3d.2 $e |- ( ph -> ( ps <-> th ) ) $.
    3bitr3d.3 $e |- ( ph -> ( ch <-> ta ) ) $.
    $( Deduction from transitivity of biconditional.  Useful for converting
       conditional definitions in a formula.  (Contributed by NM,
       24-Apr-1996.) $)
    3bitr3d $p |- ( ph -> ( th <-> ta ) ) $=
      ( bitr3d bitrd ) ADCEABDCGFIHJ $.

    $( Deduction from transitivity of biconditional.  (Contributed by NM,
       4-Aug-2006.) $)
    3bitr3rd $p |- ( ph -> ( ta <-> th ) ) $=
      ( bitr3d ) ACEDHABCDFGII $.
  $}

  ${
    3bitr4d.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    3bitr4d.2 $e |- ( ph -> ( th <-> ps ) ) $.
    3bitr4d.3 $e |- ( ph -> ( ta <-> ch ) ) $.
    $( Deduction from transitivity of biconditional.  Useful for converting
       conditional definitions in a formula.  (Contributed by NM,
       18-Oct-1995.) $)
    3bitr4d $p |- ( ph -> ( th <-> ta ) ) $=
      ( bitr4d bitrd ) ADBEGABCEFHIJ $.

    $( Deduction from transitivity of biconditional.  (Contributed by NM,
       4-Aug-2006.) $)
    3bitr4rd $p |- ( ph -> ( ta <-> th ) ) $=
      ( bitr4d ) AEBDAECBHFIGI $.
  $}

  ${
    3bitr3g.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    3bitr3g.2 $e |- ( ps <-> th ) $.
    3bitr3g.3 $e |- ( ch <-> ta ) $.
    $( More general version of ~ 3bitr3i .  Useful for converting definitions
       in a formula.  (Contributed by NM, 4-Jun-1995.) $)
    3bitr3g $p |- ( ph -> ( th <-> ta ) ) $=
      ( bitr3id bitrdi ) ADCEDBACGFIHJ $.
  $}

  ${
    3bitr4g.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    3bitr4g.2 $e |- ( th <-> ps ) $.
    3bitr4g.3 $e |- ( ta <-> ch ) $.
    $( More general version of ~ 3bitr4i .  Useful for converting definitions
       in a formula.  (Contributed by NM, 5-Aug-1993.) $)
    3bitr4g $p |- ( ph -> ( th <-> ta ) ) $=
      ( bitrid bitr4di ) ADCEDBACGFIHJ $.
  $}

  ${
    bi3ant.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Construct a biconditional in antecedent position.  (Contributed by Wolf
       Lammen, 14-May-2013.) $)
    bi3ant $p |- ( ( ( th -> ta ) -> ph ) -> ( ( ( ta -> th ) -> ps ) ->
                                                ( ( th <-> ta ) -> ch ) ) ) $=
      ( wi wb biimp imim1i biimpr imim3i syl2im ) DEGZAGDEHZAGEDGZBGOBGOCGONADE
      IJOPBDEKJABCOFLM $.
  $}

  $( Express symmetries of theorems in terms of biconditionals.  (Contributed
     by Wolf Lammen, 14-May-2013.) $)
  bisym $p |- ( ( ( ph -> ps ) -> ( ch -> th ) ) -> ( ( ( ps -> ph )
      -> ( th -> ch ) ) -> ( ( ph <-> ps ) -> ( ch <-> th ) ) ) ) $=
    ( wi wb bi3 bi3ant ) CDEDCECDFABCDGH $.

  $( The next three rules are useful for building up wff's around a
     definition, in order to make use of the definition. $)

  ${
    bi.a $e |- ( ph <-> ps ) $.
    $( Introduce an antecedent to both sides of a logical equivalence.
       (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen,
       6-Feb-2013.) $)
    imbi2i $p |- ( ( ch -> ph ) <-> ( ch -> ps ) ) $=
      ( wb a1i pm5.74i ) CABABECDFG $.
  $}

  ${
    bibi.a $e |- ( ph <-> ps ) $.
    $( Inference adding a biconditional to the left in an equivalence.
       (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Andrew Salmon,
       7-May-2011.)  (Proof shortened by Wolf Lammen, 16-May-2013.) $)
    bibi2i $p |- ( ( ch <-> ph ) <-> ( ch <-> ps ) ) $=
      ( wb id bitrdi bitr4di impbii ) CAEZCBEZJCABJFDGKCBAKFDHI $.

    $( Inference adding a biconditional to the right in an equivalence.
       (Contributed by NM, 5-Aug-1993.) $)
    bibi1i $p |- ( ( ph <-> ch ) <-> ( ps <-> ch ) ) $=
      ( wb bicom bibi2i 3bitri ) ACECAECBEBCEACFABCDGCBFH $.

    ${
      bibi12.2 $e |- ( ch <-> th ) $.
      $( The equivalence of two equivalences.  (Contributed by NM,
         5-Aug-1993.) $)
      bibi12i $p |- ( ( ph <-> ch ) <-> ( ps <-> th ) ) $=
        ( wb bibi2i bibi1i bitri ) ACGADGBDGCDAFHABDEIJ $.
    $}
  $}

  ${
    imbid.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Deduction adding an antecedent to both sides of a logical equivalence.
       (Contributed by NM, 5-Aug-1993.) $)
    imbi2d $p |- ( ph -> ( ( th -> ps ) <-> ( th -> ch ) ) ) $=
      ( wb a1d pm5.74d ) ADBCABCFDEGH $.

    $( Deduction adding a consequent to both sides of a logical equivalence.
       (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen,
       17-Sep-2013.) $)
    imbi1d $p |- ( ph -> ( ( ps -> th ) <-> ( ch -> th ) ) ) $=
      ( wi biimprd imim1d biimpd impbid ) ABDFCDFACBDABCEGHABCDABCEIHJ $.

    $( Deduction adding a biconditional to the left in an equivalence.
       (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen,
       19-May-2013.) $)
    bibi2d $p |- ( ph -> ( ( th <-> ps ) <-> ( th <-> ch ) ) ) $=
      ( wb wi pm5.74i bibi2i pm5.74 3bitr4i pm5.74ri ) ADBFZDCFZADGZABGZFOACGZF
      AMGANGPQOABCEHIADBJADCJKL $.

    $( Deduction adding a biconditional to the right in an equivalence.
       (Contributed by NM, 5-Aug-1993.) $)
    bibi1d $p |- ( ph -> ( ( ps <-> th ) <-> ( ch <-> th ) ) ) $=
      ( wb bibi2d bicom 3bitr4g ) ADBFDCFBDFCDFABCDEGBDHCDHI $.
  $}

  ${
    imbi12d.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    imbi12d.2 $e |- ( ph -> ( th <-> ta ) ) $.
    $( Deduction joining two equivalences to form equivalence of implications.
       (Contributed by NM, 5-Aug-1993.) $)
    imbi12d $p |- ( ph -> ( ( ps -> th ) <-> ( ch -> ta ) ) ) $=
      ( wi imbi1d imbi2d bitrd ) ABDHCDHCEHABCDFIADECGJK $.
    $( Deduction joining two equivalences to form equivalence of
       biconditionals.  (Contributed by NM, 5-Aug-1993.) $)
    bibi12d $p |- ( ph -> ( ( ps <-> th ) <-> ( ch <-> ta ) ) ) $=
      ( wb bibi1d bibi2d bitrd ) ABDHCDHCEHABCDFIADECGJK $.
  $}

  $( Theorem *4.84 of [WhiteheadRussell] p. 122.  (Contributed by NM,
     3-Jan-2005.) $)
  imbi1 $p |- ( ( ph <-> ps ) -> ( ( ph -> ch ) <-> ( ps -> ch ) ) ) $=
    ( wb id imbi1d ) ABDZABCGEF $.

  $( Theorem *4.85 of [WhiteheadRussell] p. 122.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 19-May-2013.) $)
  imbi2 $p |- ( ( ph <-> ps ) -> ( ( ch -> ph ) <-> ( ch -> ps ) ) ) $=
    ( wb id imbi2d ) ABDZABCGEF $.

  ${
    imbi1i.1 $e |- ( ph <-> ps ) $.
    $( Introduce a consequent to both sides of a logical equivalence.
       (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen,
       17-Sep-2013.) $)
    imbi1i $p |- ( ( ph -> ch ) <-> ( ps -> ch ) ) $=
      ( wb wi imbi1 ax-mp ) ABEACFBCFEDABCGH $.
  $}

  ${
    imbi12i.1 $e |- ( ph <-> ps ) $.
    imbi12i.2 $e |- ( ch <-> th ) $.
    $( Join two logical equivalences to form equivalence of implications.
       (Contributed by NM, 5-Aug-1993.) $)
    imbi12i $p |- ( ( ph -> ch ) <-> ( ps -> th ) ) $=
      ( wi imbi2i imbi1i bitri ) ACGADGBDGCDAFHABDEIJ $.
  $}

  $( Theorem *4.86 of [WhiteheadRussell] p. 122.  (Contributed by NM,
     3-Jan-2005.) $)
  bibi1 $p |- ( ( ph <-> ps ) -> ( ( ph <-> ch ) <-> ( ps <-> ch ) ) ) $=
    ( wb id bibi1d ) ABDZABCGEF $.

  $( A wff is equivalent to itself with true antecedent.  (Contributed by NM,
     28-Jan-1996.) $)
  biimt $p |- ( ph -> ( ps <-> ( ph -> ps ) ) ) $=
    ( wi ax-1 pm2.27 impbid2 ) ABABCBADABEF $.

  $( Theorem *5.5 of [WhiteheadRussell] p. 125.  (Contributed by NM,
     3-Jan-2005.) $)
  pm5.5 $p |- ( ph -> ( ( ph -> ps ) <-> ps ) ) $=
    ( wi biimt bicomd ) ABABCABDE $.

  ${
    a1bi.1 $e |- ph $.
    $( Inference introducing a theorem as an antecedent.  (Contributed by NM,
       5-Aug-1993.)  (Proof shortened by Wolf Lammen, 11-Nov-2012.) $)
    a1bi $p |- ( ps <-> ( ph -> ps ) ) $=
      ( wi wb biimt ax-mp ) ABABDECABFG $.
  $}

  $( Theorem *5.501 of [WhiteheadRussell] p. 125.  (Contributed by NM,
     3-Jan-2005.)  (Revised by NM, 24-Jan-2013.) $)
  pm5.501 $p |- ( ph -> ( ps <-> ( ph <-> ps ) ) ) $=
    ( wb pm5.1im biimp com12 impbid ) ABABCZABDHABABEFG $.

  $( Implication in terms of implication and biconditional.  (Contributed by
     NM, 31-Mar-1994.)  (Proof shortened by Wolf Lammen, 24-Jan-2013.) $)
  ibib $p |- ( ( ph -> ps ) <-> ( ph -> ( ph <-> ps ) ) ) $=
    ( wb pm5.501 pm5.74i ) ABABCABDE $.

  $( Implication in terms of implication and biconditional.  (Contributed by
     NM, 29-Apr-2005.)  (Proof shortened by Wolf Lammen, 21-Dec-2013.) $)
  ibibr $p |- ( ( ph -> ps ) <-> ( ph -> ( ps <-> ph ) ) ) $=
    ( wb pm5.501 bicom bitrdi pm5.74i ) ABBACZABABCHABDABEFG $.

  ${
    tbt.1 $e |- ph $.
    $( A wff is equivalent to its equivalence with truth.  (Contributed by NM,
       18-Aug-1993.)  (Proof shortened by Andrew Salmon, 13-May-2011.) $)
    tbt $p |- ( ps <-> ( ps <-> ph ) ) $=
      ( wb ibibr pm5.74ri ax-mp ) ABBADZDCABHABEFG $.
  $}

  $( Logical equivalence of commuted antecedents.  Part of Theorem *4.87 of
     [WhiteheadRussell] p. 122.  (Contributed by NM, 5-Aug-1993.) $)
  bi2.04 $p |- ( ( ph -> ( ps -> ch ) ) <-> ( ps -> ( ph -> ch ) ) ) $=
    ( wi pm2.04 impbii ) ABCDDBACDDABCEBACEF $.

  $( Antecedent absorption implication.  Theorem *5.4 of [WhiteheadRussell]
     p. 125.  (Contributed by NM, 5-Aug-1993.) $)
  pm5.4 $p |- ( ( ph -> ( ph -> ps ) ) <-> ( ph -> ps ) ) $=
    ( wi pm2.43 ax-1 impbii ) AABCZCGABDGAEF $.

  $( Distributive law for implication.  Compare Theorem *5.41 of
     [WhiteheadRussell] p. 125.  (Contributed by NM, 5-Aug-1993.) $)
  imdi $p |- ( ( ph -> ( ps -> ch ) ) <->
               ( ( ph -> ps ) -> ( ph -> ch ) ) ) $=
    ( wi ax-2 pm2.86 impbii ) ABCDDABDACDDABCEABCFG $.

  $( Theorem *5.41 of [WhiteheadRussell] p. 125.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 12-Oct-2012.) $)
  pm5.41 $p |- ( ( ( ph -> ps ) -> ( ph -> ch ) ) <->
                ( ph -> ( ps -> ch ) ) ) $=
    ( wi imdi bicomi ) ABCDDABDACDDABCEF $.

  $( The antecedent of one side of a biconditional can be moved out of the
     biconditional to become the antecedent of the remaining biconditional.
     (Contributed by BJ, 1-Jan-2025.)  (Proof shortened by Wolf Lammen,
     5-Jan-2025.) $)
  imbibi $p |- ( ( ( ph -> ps ) <-> ch ) -> ( ph -> ( ps <-> ch ) ) ) $=
    ( wi wb pm5.4 imbi2 bitr3id pm5.74rd ) ABDZCEZABCJAJDKACDABFJCAGHI $.

  $( Simplify an implication between two implications when the antecedent of
     the first is a consequence of the antecedent of the second.  The reverse
     form is useful in producing the successor step in induction proofs.
     (Contributed by Paul Chapman, 22-Jun-2011.)  (Proof shortened by Wolf
     Lammen, 14-Sep-2013.) $)
  imim21b $p |- ( ( ps -> ph ) -> ( ( ( ph -> ch ) -> ( ps -> th ) ) <->
                                    ( ps -> ( ch -> th ) ) ) ) $=
    ( wi bi2.04 wb pm5.5 imbi1d imim2i pm5.74d bitrid ) ACEZBDEEBMDEZEBAEZBCDEZ
    EMBDFOBNPANPGBAMCDACHIJKL $.

  ${
    imp3.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    $( Importation deduction.  (Contributed by NM, 31-Mar-1994.) $)
    impd $p |- ( ph -> ( ( ps /\ ch ) -> th ) ) $=
      ( wa wi com3l imp com12 ) BCFADBCADGABCDEHIJ $.

    $( Importation deduction with commuted antecedents.  (Contributed by Peter
       Mazsa, 24-Sep-2022.)  (Proof shortened by Wolf Lammen, 22-Oct-2022.) $)
    impcomd $p |- ( ph -> ( ( ch /\ ps ) -> th ) ) $=
      ( com23 impd ) ACBDABCDEFG $.

    $( An importation inference.  (Contributed by NM, 26-Apr-1994.) $)
    imp31 $p |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $=
      ( wa wi imp ) ABFCDABCDGEHH $.

    $( An importation inference.  (Contributed by NM, 26-Apr-1994.) $)
    imp32 $p |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $=
      ( wa impd imp ) ABCFDABCDEGH $.
  $}

  ${
    exp3a.1 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
    $( Exportation deduction.  (Contributed by NM, 20-Aug-1993.) $)
    expd $p |- ( ph -> ( ps -> ( ch -> th ) ) ) $=
      ( wi wa com12 ex com3r ) BCADBCADFABCGDEHIJ $.

    $( A deduction version of exportation, followed by importation.
       (Contributed by NM, 6-Sep-2008.) $)
    expdimp $p |- ( ( ph /\ ps ) -> ( ch -> th ) ) $=
      ( wi expd imp ) ABCDFABCDEGH $.
  $}

  ${
    impancom.1 $e |- ( ( ph /\ ps ) -> ( ch -> th ) ) $.
    $( Mixed importation/commutation inference.  (Contributed by NM,
       22-Jun-2013.) $)
    impancom $p |- ( ( ph /\ ch ) -> ( ps -> th ) ) $=
      ( wi ex com23 imp ) ACBDFABCDABCDFEGHI $.
  $}

  $( Theorem *3.3 (Exp) of [WhiteheadRussell] p. 112.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 24-Mar-2013.) $)
  pm3.3 $p |- ( ( ( ph /\ ps ) -> ch ) -> ( ph -> ( ps -> ch ) ) ) $=
    ( wa wi id expd ) ABDCEZABCHFG $.

  $( Theorem *3.31 (Imp) of [WhiteheadRussell] p. 112.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 24-Mar-2013.) $)
  pm3.31 $p |- ( ( ph -> ( ps -> ch ) ) -> ( ( ph /\ ps ) -> ch ) ) $=
    ( wi id impd ) ABCDDZABCGEF $.

  $( Import-export theorem.  Part of Theorem *4.87 of [WhiteheadRussell]
     p. 122.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf
     Lammen, 24-Mar-2013.) $)
  impexp $p |- ( ( ( ph /\ ps ) -> ch ) <-> ( ph -> ( ps -> ch ) ) ) $=
    ( wa wi pm3.3 pm3.31 impbii ) ABDCEABCEEABCFABCGH $.

  $( Join antecedents with conjunction.  Theorem *3.21 of [WhiteheadRussell]
     p. 111.  (Contributed by NM, 5-Aug-1993.) $)
  pm3.21 $p |- ( ph -> ( ps -> ( ps /\ ph ) ) ) $=
    ( wa pm3.2 com12 ) BABACBADE $.

  $( Theorem *3.22 of [WhiteheadRussell] p. 111.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 13-Nov-2012.) $)
  pm3.22 $p |- ( ( ph /\ ps ) -> ( ps /\ ph ) ) $=
    ( wa pm3.21 imp ) ABBACABDE $.

  $( Commutative law for conjunction.  Theorem *4.3 of [WhiteheadRussell]
     p. 118.  (Contributed by NM, 25-Jun-1998.)  (Proof shortened by Wolf
     Lammen, 4-Nov-2012.) $)
  ancom $p |- ( ( ph /\ ps ) <-> ( ps /\ ph ) ) $=
    ( wa pm3.22 impbii ) ABCBACABDBADE $.

  ${
    ancomd.1 $e |- ( ph -> ( ps /\ ch ) ) $.
    $( Commutation of conjuncts in consequent.  (Contributed by Jeff Hankins,
       14-Aug-2009.) $)
    ancomd $p |- ( ph -> ( ch /\ ps ) ) $=
      ( wa ancom sylib ) ABCECBEDBCFG $.
  $}

  ${
    ancoms.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( Inference commuting conjunction in antecedent.  (Contributed by NM,
       21-Apr-1994.) $)
    ancoms $p |- ( ( ps /\ ph ) -> ch ) $=
      ( expcom imp ) BACABCDEF $.
  $}

  ${
    ancomsd.1 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
    $( Deduction commuting conjunction in antecedent.  (Contributed by NM,
       12-Dec-2004.) $)
    ancomsd $p |- ( ph -> ( ( ch /\ ps ) -> th ) ) $=
      ( wa ancom biimtrid ) CBFBCFADCBGEH $.
  $}

  ${
    biancomi.1 $e |- ( ph <-> ( ch /\ ps ) ) $.
    $( Commuting conjunction in a biconditional.  (Contributed by Peter Mazsa,
       17-Jun-2018.) $)
    biancomi $p |- ( ph <-> ( ps /\ ch ) ) $=
      ( wa ancom bitr4i ) ACBEBCEDBCFG $.
  $}

  ${
    biancomd.1 $e |- ( ph -> ( ps <-> ( th /\ ch ) ) ) $.
    $( Commuting conjunction in a biconditional, deduction form.  (Contributed
       by Peter Mazsa, 3-Oct-2018.) $)
    biancomd $p |- ( ph -> ( ps <-> ( ch /\ th ) ) ) $=
      ( wa ancom bitrdi ) ABDCFCDFEDCGH $.
  $}

  ${
    pm3.2i.1 $e |- ph $.
    pm3.2i.2 $e |- ps $.
    $( Infer conjunction of premises.  (Contributed by NM, 5-Aug-1993.) $)
    pm3.2i $p |- ( ph /\ ps ) $=
      ( wa pm3.2 mp2 ) ABABECDABFG $.
  $}

  $( Nested conjunction of antecedents.  (Contributed by NM, 5-Aug-1993.) $)
  pm3.43i $p |- ( ( ph -> ps ) ->
                ( ( ph -> ch ) -> ( ph -> ( ps /\ ch ) ) ) ) $=
    ( wa pm3.2 imim3i ) BCBCDABCEF $.

  ${
    simplbi.1 $e |- ( ph <-> ( ps /\ ch ) ) $.
    $( Deduction eliminating a conjunct.  (Contributed by NM, 27-May-1998.) $)
    simplbi $p |- ( ph -> ps ) $=
      ( wa biimpi simpld ) ABCABCEDFG $.
  $}

  ${
    simprbi.1 $e |- ( ph <-> ( ps /\ ch ) ) $.
    $( Deduction eliminating a conjunct.  (Contributed by NM, 27-May-1998.) $)
    simprbi $p |- ( ph -> ch ) $=
      ( wa biimpi simprd ) ABCABCEDFG $.
  $}

  ${
    adantr.1 $e |- ( ph -> ps ) $.
    $( Inference adding a conjunct to the right of an antecedent.  (Contributed
       by NM, 30-Aug-1993.) $)
    adantr $p |- ( ( ph /\ ch ) -> ps ) $=
      ( a1d imp ) ACBABCDEF $.
  $}

  ${
    adantl.1 $e |- ( ph -> ps ) $.
    $( Inference adding a conjunct to the left of an antecedent.  (Contributed
       by NM, 30-Aug-1993.)  (Proof shortened by Wolf Lammen, 23-Nov-2012.) $)
    adantl $p |- ( ( ch /\ ph ) -> ps ) $=
      ( adantr ancoms ) ACBABCDEF $.
  $}

  ${
    adantld.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction adding a conjunct to the left of an antecedent.  (Contributed
       by NM, 4-May-1994.)  (Proof shortened by Wolf Lammen, 20-Dec-2012.) $)
    adantld $p |- ( ph -> ( ( th /\ ps ) -> ch ) ) $=
      ( wa simpr syl5 ) DBFBACDBGEH $.
  $}

  ${
    adantrd.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction adding a conjunct to the right of an antecedent.  (Contributed
       by NM, 4-May-1994.) $)
    adantrd $p |- ( ph -> ( ( ps /\ th ) -> ch ) ) $=
      ( wa simpl syl5 ) BDFBACBDGEH $.
  $}

  ${
    impel.1 $e |- ( ph -> ( ps -> ch ) ) $.
    impel.2 $e |- ( th -> ps ) $.
    $( An inference for implication elimination.  (Contributed by Giovanni
       Mascellani, 23-May-2019.)  (Proof shortened by Wolf Lammen,
       2-Sep-2020.) $)
    impel $p |- ( ( ph /\ th ) -> ch ) $=
      ( syl5 imp ) ADCDBACFEGH $.
  $}

  ${
    mpan9.1 $e |- ( ph -> ps ) $.
    mpan9.2 $e |- ( ch -> ( ps -> th ) ) $.
    $( Modus ponens conjoining dissimilar antecedents.  (Contributed by NM,
       1-Feb-2008.)  (Proof shortened by Andrew Salmon, 7-May-2011.) $)
    mpan9 $p |- ( ( ph /\ ch ) -> th ) $=
      ( syl5 impcom ) CADABCDEFGH $.
  $}

  ${
    syldan.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    syldan.2 $e |- ( ( ph /\ ch ) -> th ) $.
    $( A syllogism deduction with conjoined antecents.  (Contributed by NM,
       24-Feb-2005.)  (Proof shortened by Wolf Lammen, 6-Apr-2013.) $)
    syldan $p |- ( ( ph /\ ps ) -> th ) $=
      ( wa expcom adantrd mpcom ) CABGDECADBACDFHIJ $.
  $}

  ${
    sylan.1 $e |- ( ph -> ps ) $.
    sylan.2 $e |- ( ( ps /\ ch ) -> th ) $.
    $( A syllogism inference.  (Contributed by NM, 21-Apr-1994.)  (Proof
       shortened by Wolf Lammen, 22-Nov-2012.) $)
    sylan $p |- ( ( ph /\ ch ) -> th ) $=
      ( expcom mpan9 ) ABCDEBCDFGH $.
  $}

  ${
    sylanb.1 $e |- ( ph <-> ps ) $.
    sylanb.2 $e |- ( ( ps /\ ch ) -> th ) $.
    $( A syllogism inference.  (Contributed by NM, 18-May-1994.) $)
    sylanb $p |- ( ( ph /\ ch ) -> th ) $=
      ( biimpi sylan ) ABCDABEGFH $.
  $}

  ${
    sylanbr.1 $e |- ( ps <-> ph ) $.
    sylanbr.2 $e |- ( ( ps /\ ch ) -> th ) $.
    $( A syllogism inference.  (Contributed by NM, 18-May-1994.) $)
    sylanbr $p |- ( ( ph /\ ch ) -> th ) $=
      ( biimpri sylan ) ABCDBAEGFH $.
  $}

  ${
    sylan2.1 $e |- ( ph -> ch ) $.
    sylan2.2 $e |- ( ( ps /\ ch ) -> th ) $.
    $( A syllogism inference.  (Contributed by NM, 21-Apr-1994.)  (Proof
       shortened by Wolf Lammen, 22-Nov-2012.) $)
    sylan2 $p |- ( ( ps /\ ph ) -> th ) $=
      ( adantl syldan ) BACDACBEGFH $.
  $}

  ${
    sylan2b.1 $e |- ( ph <-> ch ) $.
    sylan2b.2 $e |- ( ( ps /\ ch ) -> th ) $.
    $( A syllogism inference.  (Contributed by NM, 21-Apr-1994.) $)
    sylan2b $p |- ( ( ps /\ ph ) -> th ) $=
      ( biimpi sylan2 ) ABCDACEGFH $.
  $}

  ${
    sylan2br.1 $e |- ( ch <-> ph ) $.
    sylan2br.2 $e |- ( ( ps /\ ch ) -> th ) $.
    $( A syllogism inference.  (Contributed by NM, 21-Apr-1994.) $)
    sylan2br $p |- ( ( ps /\ ph ) -> th ) $=
      ( biimpri sylan2 ) ABCDCAEGFH $.
  $}

  ${
    syl2an.1 $e |- ( ph -> ps ) $.
    syl2an.2 $e |- ( ta -> ch ) $.
    syl2an.3 $e |- ( ( ps /\ ch ) -> th ) $.
    $( A double syllogism inference.  (Contributed by NM, 31-Jan-1997.) $)
    syl2an $p |- ( ( ph /\ ta ) -> th ) $=
      ( sylan sylan2 ) EACDGABCDFHIJ $.

    $( A double syllogism inference.  (Contributed by NM, 17-Sep-2013.) $)
    syl2anr $p |- ( ( ta /\ ph ) -> th ) $=
      ( syl2an ancoms ) AEDABCDEFGHIJ $.
  $}

  ${
    syl2anb.1 $e |- ( ph <-> ps ) $.
    syl2anb.2 $e |- ( ta <-> ch ) $.
    syl2anb.3 $e |- ( ( ps /\ ch ) -> th ) $.
    $( A double syllogism inference.  (Contributed by NM, 29-Jul-1999.) $)
    syl2anb $p |- ( ( ph /\ ta ) -> th ) $=
      ( sylanb sylan2b ) EACDGABCDFHIJ $.
  $}

  ${
    syl2anbr.1 $e |- ( ps <-> ph ) $.
    syl2anbr.2 $e |- ( ch <-> ta ) $.
    syl2anbr.3 $e |- ( ( ps /\ ch ) -> th ) $.
    $( A double syllogism inference.  (Contributed by NM, 29-Jul-1999.) $)
    syl2anbr $p |- ( ( ph /\ ta ) -> th ) $=
      ( sylanbr sylan2br ) EACDGABCDFHIJ $.
  $}

  ${
    syland.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syland.2 $e |- ( ph -> ( ( ch /\ th ) -> ta ) ) $.
    $( A syllogism deduction.  (Contributed by NM, 15-Dec-2004.) $)
    syland $p |- ( ph -> ( ( ps /\ th ) -> ta ) ) $=
      ( wi expd syld impd ) ABDEABCDEHFACDEGIJK $.
  $}

  ${
    sylan2d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    sylan2d.2 $e |- ( ph -> ( ( th /\ ch ) -> ta ) ) $.
    $( A syllogism deduction.  (Contributed by NM, 15-Dec-2004.) $)
    sylan2d $p |- ( ph -> ( ( th /\ ps ) -> ta ) ) $=
      ( ancomsd syland ) ABDEABCDEFADCEGHIH $.
  $}

  ${
    syl2and.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syl2and.2 $e |- ( ph -> ( th -> ta ) ) $.
    syl2and.3 $e |- ( ph -> ( ( ch /\ ta ) -> et ) ) $.
    $( A syllogism deduction.  (Contributed by NM, 15-Dec-2004.) $)
    syl2and $p |- ( ph -> ( ( ps /\ th ) -> et ) ) $=
      ( sylan2d syland ) ABCDFGADECFHIJK $.
  $}

  ${
    biimpa.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Inference from a logical equivalence.  (Contributed by NM,
       3-May-1994.) $)
    biimpa $p |- ( ( ph /\ ps ) -> ch ) $=
      ( biimpd imp ) ABCABCDEF $.

    $( Inference from a logical equivalence.  (Contributed by NM,
       3-May-1994.) $)
    biimpar $p |- ( ( ph /\ ch ) -> ps ) $=
      ( biimprd imp ) ACBABCDEF $.

    $( Inference from a logical equivalence.  (Contributed by NM,
       3-May-1994.) $)
    biimpac $p |- ( ( ps /\ ph ) -> ch ) $=
      ( biimpcd imp ) BACABCDEF $.

    $( Inference from a logical equivalence.  (Contributed by NM,
       3-May-1994.) $)
    biimparc $p |- ( ( ch /\ ph ) -> ps ) $=
      ( biimprcd imp ) CABABCDEF $.
  $}

  $( Introduction of antecedent as conjunct.  Theorem *4.73 of
     [WhiteheadRussell] p. 121.  (Contributed by NM, 30-Mar-1994.)  (Revised by
     NM, 24-Mar-2013.) $)
  iba $p |- ( ph -> ( ps <-> ( ps /\ ph ) ) ) $=
    ( wa pm3.21 simpl impbid1 ) ABBACABDBAEF $.

  $( Introduction of antecedent as conjunct.  (Contributed by NM, 5-Dec-1995.)
     (Revised by NM, 24-Mar-2013.) $)
  ibar $p |- ( ph -> ( ps <-> ( ph /\ ps ) ) ) $=
    ( wa pm3.2 simpr impbid1 ) ABABCABDABEF $.

  ${
    biantru.1 $e |- ph $.
    $( A wff is equivalent to its conjunction with truth.  (Contributed by NM,
       5-Aug-1993.) $)
    biantru $p |- ( ps <-> ( ps /\ ph ) ) $=
      ( wa wb iba ax-mp ) ABBADECABFG $.
  $}

  ${
    biantrur.1 $e |- ph $.
    $( A wff is equivalent to its conjunction with truth.  (Contributed by NM,
       3-Aug-1994.) $)
    biantrur $p |- ( ps <-> ( ph /\ ps ) ) $=
      ( wa wb ibar ax-mp ) ABABDECABFG $.
  $}

  ${
    biantrud.1 $e |- ( ph -> ps ) $.
    $( A wff is equivalent to its conjunction with truth.  (Contributed by NM,
       2-Aug-1994.)  (Proof shortened by Wolf Lammen, 23-Oct-2013.) $)
    biantrud $p |- ( ph -> ( ch <-> ( ch /\ ps ) ) ) $=
      ( wa wb iba syl ) ABCCBEFDBCGH $.

    $( A wff is equivalent to its conjunction with truth.  (Contributed by NM,
       1-May-1995.)  (Proof shortened by Andrew Salmon, 7-May-2011.) $)
    biantrurd $p |- ( ph -> ( ch <-> ( ps /\ ch ) ) ) $=
      ( wa wb ibar syl ) ABCBCEFDBCGH $.
  $}

  ${
    jca.1 $e |- ( ph -> ps ) $.
    jca.2 $e |- ( ph -> ch ) $.
    $( Deduce conjunction of the consequents of two implications ("join
       consequents with 'and'").  (Contributed by NM, 5-Aug-1993.)  (Proof
       shortened by Wolf Lammen, 25-Oct-2012.) $)
    jca $p |- ( ph -> ( ps /\ ch ) ) $=
      ( wa pm3.2 sylc ) ABCBCFDEBCGH $.
  $}

  ${
    jcad.1 $e |- ( ph -> ( ps -> ch ) ) $.
    jcad.2 $e |- ( ph -> ( ps -> th ) ) $.
    $( Deduction conjoining the consequents of two implications.  (Contributed
       by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen, 23-Jul-2013.) $)
    jcad $p |- ( ph -> ( ps -> ( ch /\ th ) ) ) $=
      ( wa pm3.2 syl6c ) ABCDCDGEFCDHI $.
  $}

  ${
    jca2.1 $e |- ( ph -> ( ps -> ch ) ) $.
    jca2.2 $e |- ( ps -> th ) $.
    $( Inference conjoining the consequents of two implications.  (Contributed
       by Rodolfo Medina, 12-Oct-2010.) $)
    jca2 $p |- ( ph -> ( ps -> ( ch /\ th ) ) ) $=
      ( wi a1i jcad ) ABCDEBDGAFHI $.
  $}

  ${
    jca31.1 $e |- ( ph -> ps ) $.
    jca31.2 $e |- ( ph -> ch ) $.
    jca31.3 $e |- ( ph -> th ) $.
    $( Join three consequents.  (Contributed by Jeff Hankins, 1-Aug-2009.) $)
    jca31 $p |- ( ph -> ( ( ps /\ ch ) /\ th ) ) $=
      ( wa jca ) ABCHDABCEFIGI $.

    $( Join three consequents.  (Contributed by FL, 1-Aug-2009.) $)
    jca32 $p |- ( ph -> ( ps /\ ( ch /\ th ) ) ) $=
      ( wa jca ) ABCDHEACDFGII $.
  $}

  ${
    jcai.1 $e |- ( ph -> ps ) $.
    jcai.2 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction replacing implication with conjunction.  (Contributed by NM,
       5-Aug-1993.) $)
    jcai $p |- ( ph -> ( ps /\ ch ) ) $=
      ( mpd jca ) ABCDABCDEFG $.
  $}

  ${
    jctil.1 $e |- ( ph -> ps ) $.
    jctil.2 $e |- ch $.
    $( Inference conjoining a theorem to left of consequent in an implication.
       (Contributed by NM, 31-Dec-1993.) $)
    jctil $p |- ( ph -> ( ch /\ ps ) ) $=
      ( a1i jca ) ACBCAEFDG $.

    $( Inference conjoining a theorem to right of consequent in an implication.
       (Contributed by NM, 31-Dec-1993.) $)
    jctir $p |- ( ph -> ( ps /\ ch ) ) $=
      ( a1i jca ) ABCDCAEFG $.
  $}

  ${
    jctl.1 $e |- ps $.
    $( Inference conjoining a theorem to the left of a consequent.
       (Contributed by NM, 31-Dec-1993.)  (Proof shortened by Wolf Lammen,
       24-Oct-2012.) $)
    jctl $p |- ( ph -> ( ps /\ ph ) ) $=
      ( id jctil ) AABADCE $.

    $( Inference conjoining a theorem to the right of a consequent.
       (Contributed by NM, 18-Aug-1993.)  (Proof shortened by Wolf Lammen,
       24-Oct-2012.) $)
    jctr $p |- ( ph -> ( ph /\ ps ) ) $=
      ( id jctir ) AABADCE $.
  $}

  ${
    jctild.1 $e |- ( ph -> ( ps -> ch ) ) $.
    jctild.2 $e |- ( ph -> th ) $.
    $( Deduction conjoining a theorem to left of consequent in an implication.
       (Contributed by NM, 21-Apr-2005.) $)
    jctild $p |- ( ph -> ( ps -> ( th /\ ch ) ) ) $=
      ( a1d jcad ) ABDCADBFGEH $.
  $}

  ${
    jctird.1 $e |- ( ph -> ( ps -> ch ) ) $.
    jctird.2 $e |- ( ph -> th ) $.
    $( Deduction conjoining a theorem to right of consequent in an implication.
       (Contributed by NM, 21-Apr-2005.) $)
    jctird $p |- ( ph -> ( ps -> ( ch /\ th ) ) ) $=
      ( a1d jcad ) ABCDEADBFGH $.
  $}

  $( Conjoin antecedent to left of consequent.  (Contributed by NM,
     15-Aug-1994.) $)
  ancl $p |- ( ( ph -> ps ) -> ( ph -> ( ph /\ ps ) ) ) $=
    ( wa pm3.2 a2i ) ABABCABDE $.

  $( Conjoin antecedent to left of consequent.  Theorem *4.7 of
     [WhiteheadRussell] p. 120.  (Contributed by NM, 25-Jul-1999.)  (Proof
     shortened by Wolf Lammen, 24-Mar-2013.) $)
  anclb $p |- ( ( ph -> ps ) <-> ( ph -> ( ph /\ ps ) ) ) $=
    ( wa ibar pm5.74i ) ABABCABDE $.

  $( Theorem *5.42 of [WhiteheadRussell] p. 125.  (Contributed by NM,
     3-Jan-2005.) $)
  pm5.42 $p |- ( ( ph -> ( ps -> ch ) ) <->
                ( ph -> ( ps -> ( ph /\ ch ) ) ) ) $=
    ( wi wa ibar imbi2d pm5.74i ) ABCDBACEZDACIBACFGH $.

  $( Conjoin antecedent to right of consequent.  (Contributed by NM,
     15-Aug-1994.) $)
  ancr $p |- ( ( ph -> ps ) -> ( ph -> ( ps /\ ph ) ) ) $=
    ( wa pm3.21 a2i ) ABBACABDE $.

  $( Conjoin antecedent to right of consequent.  (Contributed by NM,
     25-Jul-1999.)  (Proof shortened by Wolf Lammen, 24-Mar-2013.) $)
  ancrb $p |- ( ( ph -> ps ) <-> ( ph -> ( ps /\ ph ) ) ) $=
    ( wa iba pm5.74i ) ABBACABDE $.

  ${
    ancli.1 $e |- ( ph -> ps ) $.
    $( Deduction conjoining antecedent to left of consequent.  (Contributed by
       NM, 12-Aug-1993.) $)
    ancli $p |- ( ph -> ( ph /\ ps ) ) $=
      ( id jca ) AABADCE $.
  $}

  ${
    ancri.1 $e |- ( ph -> ps ) $.
    $( Deduction conjoining antecedent to right of consequent.  (Contributed by
       NM, 15-Aug-1994.) $)
    ancri $p |- ( ph -> ( ps /\ ph ) ) $=
      ( id jca ) ABACADE $.
  $}

  ${
    ancld.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction conjoining antecedent to left of consequent in nested
       implication.  (Contributed by NM, 15-Aug-1994.)  (Proof shortened by
       Wolf Lammen, 1-Nov-2012.) $)
    ancld $p |- ( ph -> ( ps -> ( ps /\ ch ) ) ) $=
      ( idd jcad ) ABBCABEDF $.
  $}

  ${
    ancrd.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction conjoining antecedent to right of consequent in nested
       implication.  (Contributed by NM, 15-Aug-1994.)  (Proof shortened by
       Wolf Lammen, 1-Nov-2012.) $)
    ancrd $p |- ( ph -> ( ps -> ( ch /\ ps ) ) ) $=
      ( idd jcad ) ABCBDABEF $.
  $}

  $( Conjoin antecedent to left of consequent in nested implication.
     (Contributed by NM, 10-Aug-1994.)  (Proof shortened by Wolf Lammen,
     14-Jul-2013.) $)
  anc2l $p |- ( ( ph -> ( ps -> ch ) ) -> ( ph -> ( ps -> ( ph /\ ch ) ) ) ) $=
    ( wi wa pm5.42 biimpi ) ABCDDABACEDDABCFG $.

  $( Conjoin antecedent to right of consequent in nested implication.
     (Contributed by NM, 15-Aug-1994.) $)
  anc2r $p |- ( ( ph -> ( ps -> ch ) ) -> ( ph -> ( ps -> ( ch /\ ph ) ) ) ) $=
    ( wi wa pm3.21 imim2d a2i ) ABCDBCAEZDACIBACFGH $.

  ${
    anc2li.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction conjoining antecedent to left of consequent in nested
       implication.  (Contributed by NM, 10-Aug-1994.)  (Proof shortened by
       Wolf Lammen, 7-Dec-2012.) $)
    anc2li $p |- ( ph -> ( ps -> ( ph /\ ch ) ) ) $=
      ( id jctild ) ABCADAEF $.
  $}

  ${
    anc2ri.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction conjoining antecedent to right of consequent in nested
       implication.  (Contributed by NM, 15-Aug-1994.)  (Proof shortened by
       Wolf Lammen, 7-Dec-2012.) $)
    anc2ri $p |- ( ph -> ( ps -> ( ch /\ ph ) ) ) $=
      ( id jctird ) ABCADAEF $.
  $}

  $( Theorem *3.41 of [WhiteheadRussell] p. 113.  (Contributed by NM,
     3-Jan-2005.) $)
  pm3.41 $p |- ( ( ph -> ch ) -> ( ( ph /\ ps ) -> ch ) ) $=
    ( wa simpl imim1i ) ABDACABEF $.

  $( Theorem *3.42 of [WhiteheadRussell] p. 113.  (Contributed by NM,
     3-Jan-2005.) $)
  pm3.42 $p |- ( ( ps -> ch ) -> ( ( ph /\ ps ) -> ch ) ) $=
    ( wa simpr imim1i ) ABDBCABEF $.

  $( Conjunction implies implication.  Theorem *3.4 of [WhiteheadRussell]
     p. 113.  (Contributed by NM, 31-Jul-1995.) $)
  pm3.4 $p |- ( ( ph /\ ps ) -> ( ph -> ps ) ) $=
    ( wa simpr a1d ) ABCBAABDE $.

  $( Conjunction with implication.  Compare Theorem *4.45 of [WhiteheadRussell]
     p. 119.  (Contributed by NM, 17-May-1998.) $)
  pm4.45im $p |- ( ph <-> ( ph /\ ( ps -> ph ) ) ) $=
    ( wi wa ax-1 ancli simpl impbii ) AABACZDAIABEFAIGH $.

  ${
    anim12d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    anim12d.2 $e |- ( ph -> ( th -> ta ) ) $.
    $( Conjoin antecedents and consequents in a deduction.  (Contributed by NM,
       3-Apr-1994.)  (Proof shortened by Wolf Lammen, 18-Dec-2013.) $)
    anim12d $p |- ( ph -> ( ( ps /\ th ) -> ( ch /\ ta ) ) ) $=
      ( wa idd syl2and ) ABCDECEHZFGAKIJ $.
  $}

  ${
    anim1d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Add a conjunct to right of antecedent and consequent in a deduction.
       (Contributed by NM, 3-Apr-1994.) $)
    anim1d $p |- ( ph -> ( ( ps /\ th ) -> ( ch /\ th ) ) ) $=
      ( idd anim12d ) ABCDDEADFG $.

    $( Add a conjunct to left of antecedent and consequent in a deduction.
       (Contributed by NM, 5-Aug-1993.) $)
    anim2d $p |- ( ph -> ( ( th /\ ps ) -> ( th /\ ch ) ) ) $=
      ( idd anim12d ) ADDBCADFEG $.
  $}

  ${
    anim12i.1 $e |- ( ph -> ps ) $.
    anim12i.2 $e |- ( ch -> th ) $.
    $( Conjoin antecedents and consequents of two premises.  (Contributed by
       NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen, 14-Dec-2013.) $)
    anim12i $p |- ( ( ph /\ ch ) -> ( ps /\ th ) ) $=
      ( wa id syl2an ) ABDBDGZCEFJHI $.

    $( Variant of ~ anim12i with commutation.  (Contributed by Jonathan
       Ben-Naim, 3-Jun-2011.) $)
    anim12ci $p |- ( ( ph /\ ch ) -> ( th /\ ps ) ) $=
      ( wa anim12i ancoms ) CADBGCDABFEHI $.
  $}

  ${
    anim1i.1 $e |- ( ph -> ps ) $.
    $( Introduce conjunct to both sides of an implication.  (Contributed by NM,
       5-Aug-1993.) $)
    anim1i $p |- ( ( ph /\ ch ) -> ( ps /\ ch ) ) $=
      ( id anim12i ) ABCCDCEF $.

    $( Introduce conjunct to both sides of an implication.  (Contributed by
       Peter Mazsa, 24-Sep-2022.) $)
    anim1ci $p |- ( ( ph /\ ch ) -> ( ch /\ ps ) ) $=
      ( id anim12ci ) ABCCDCEF $.

    $( Introduce conjunct to both sides of an implication.  (Contributed by NM,
       5-Aug-1993.) $)
    anim2i $p |- ( ( ch /\ ph ) -> ( ch /\ ps ) ) $=
      ( id anim12i ) CCABCEDF $.
  $}

  ${
    anim12ii.1 $e |- ( ph -> ( ps -> ch ) ) $.
    anim12ii.2 $e |- ( th -> ( ps -> ta ) ) $.
    $( Conjoin antecedents and consequents in a deduction.  (Contributed by NM,
       11-Nov-2007.)  (Proof shortened by Wolf Lammen, 19-Jul-2013.) $)
    anim12ii $p |- ( ( ph /\ th ) -> ( ps -> ( ch /\ ta ) ) ) $=
      ( wa wi adantr adantl jcad ) ADHBCEABCIDFJDBEIAGKL $.
  $}

  $( Theorem *3.47 of [WhiteheadRussell] p. 113.  It was proved by Leibniz, and
     it evidently pleased him enough to call it 'praeclarum theorema' (splendid
     theorem).  (Contributed by NM, 12-Aug-1993.)  (Proof shortened by Wolf
     Lammen, 7-Apr-2013.) $)
  anim12 $p |- ( ( ( ph -> ps ) /\ ( ch -> th ) ) ->
                 ( ( ph /\ ch ) -> ( ps /\ th ) ) ) $=
    ( wi wa simpl simpr anim12d ) ABEZCDEZFABCDJKGJKHI $.

  $( Theorem *3.33 (Syll) of [WhiteheadRussell] p. 112.  (Contributed by NM,
     3-Jan-2005.) $)
  pm3.33 $p |- ( ( ( ph -> ps ) /\ ( ps -> ch ) ) -> ( ph -> ch ) ) $=
    ( wi imim1 imp ) ABDBCDACDABCEF $.

  $( Theorem *3.34 (Syll) of [WhiteheadRussell] p. 112.  (Contributed by NM,
     3-Jan-2005.) $)
  pm3.34 $p |- ( ( ( ps -> ch ) /\ ( ph -> ps ) ) -> ( ph -> ch ) ) $=
    ( wi imim2 imp ) BCDABDACDBCAEF $.

  $( Conjunctive detachment.  Theorem *3.35 of [WhiteheadRussell] p. 112.
     (Contributed by NM, 14-Dec-2002.) $)
  pm3.35 $p |- ( ( ph /\ ( ph -> ps ) ) -> ps ) $=
    ( wi pm2.27 imp ) AABCBABDE $.

  $( Theorem *5.31 of [WhiteheadRussell] p. 125.  (Contributed by NM,
     3-Jan-2005.) $)
  pm5.31 $p |- ( ( ch /\ ( ph -> ps ) ) -> ( ph -> ( ps /\ ch ) ) ) $=
    ( wi wa pm3.21 imim2d imp ) CABDABCEZDCBIACBFGH $.

  ${
    imp4.1 $e |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $.
    $( An importation inference.  (Contributed by NM, 26-Apr-1994.) $)
    imp4a $p |- ( ph -> ( ps -> ( ( ch /\ th ) -> ta ) ) ) $=
      ( wi wa impexp imbitrrdi ) ABCDEGGCDHEGFCDEIJ $.

    $( An importation inference.  (Contributed by NM, 26-Apr-1994.) $)
    imp4b $p |- ( ( ph /\ ps ) -> ( ( ch /\ th ) -> ta ) ) $=
      ( wa wi imp4a imp ) ABCDGEHABCDEFIJ $.

    $( An importation inference.  (Contributed by NM, 26-Apr-1994.) $)
    imp4c $p |- ( ph -> ( ( ( ps /\ ch ) /\ th ) -> ta ) ) $=
      ( wa wi impd ) ABCGDEABCDEHFII $.

    $( An importation inference.  (Contributed by NM, 26-Apr-1994.) $)
    imp4d $p |- ( ph -> ( ( ps /\ ( ch /\ th ) ) -> ta ) ) $=
      ( wa imp4a impd ) ABCDGEABCDEFHI $.

    $( An importation inference.  (Contributed by NM, 26-Apr-1994.) $)
    imp41 $p |- ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) -> ta ) $=
      ( wa wi imp imp31 ) ABGCDEABCDEHHFIJ $.

    $( An importation inference.  (Contributed by NM, 26-Apr-1994.) $)
    imp42 $p |- ( ( ( ph /\ ( ps /\ ch ) ) /\ th ) -> ta ) $=
      ( wa wi imp32 imp ) ABCGGDEABCDEHFIJ $.

    $( An importation inference.  (Contributed by NM, 26-Apr-1994.) $)
    imp43 $p |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) -> ta ) $=
      ( wa imp4b imp ) ABGCDGEABCDEFHI $.

    $( An importation inference.  (Contributed by NM, 26-Apr-1994.) $)
    imp44 $p |- ( ( ph /\ ( ( ps /\ ch ) /\ th ) ) -> ta ) $=
      ( wa imp4c imp ) ABCGDGEABCDEFHI $.

    $( An importation inference.  (Contributed by NM, 26-Apr-1994.) $)
    imp45 $p |- ( ( ph /\ ( ps /\ ( ch /\ th ) ) ) -> ta ) $=
      ( wa imp4d imp ) ABCDGGEABCDEFHI $.
  $}

  ${
    imp5.1 $e |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $.
    $( An importation inference.  (Contributed by Jeff Hankins, 7-Jul-2009.) $)
    imp5a $p |- ( ph -> ( ps -> ( ch -> ( ( th /\ ta ) -> et ) ) ) ) $=
      ( wi wa pm3.31 syl8 ) ABCDEFHHDEIFHGDEFJK $.

    $( An importation inference.  (Contributed by Jeff Hankins, 7-Jul-2009.) $)
    imp5d $p |- ( ( ( ph /\ ps ) /\ ch ) -> ( ( th /\ ta ) -> et ) ) $=
      ( wa wi imp31 impd ) ABHCHDEFABCDEFIIGJK $.

    $( An importation inference.  (Contributed by Jeff Hankins, 7-Jul-2009.) $)
    imp5g $p |- ( ( ph /\ ps ) -> ( ( ( ch /\ th ) /\ ta ) -> et ) ) $=
      ( wa wi imp imp4c ) ABHCDEFABCDEFIIIGJK $.

    $( An importation inference.  (Contributed by Jeff Hankins, 7-Jul-2009.) $)
    imp55 $p |- ( ( ( ph /\ ( ps /\ ( ch /\ th ) ) ) /\ ta ) -> et ) $=
      ( wa wi imp4a imp42 ) ABCDHEFABCDEFIGJK $.

    $( An importation inference.  (Contributed by Jeff Hankins, 7-Jul-2009.) $)
    imp511 $p |- ( ( ph /\ ( ( ps /\ ( ch /\ th ) ) /\ ta ) ) -> et ) $=
      ( wa wi imp4a imp44 ) ABCDHEFABCDEFIGJK $.
  $}

  ${
    expimpd.1 $e |- ( ( ph /\ ps ) -> ( ch -> th ) ) $.
    $( Exportation followed by a deduction version of importation.
       (Contributed by NM, 6-Sep-2008.) $)
    expimpd $p |- ( ph -> ( ( ps /\ ch ) -> th ) ) $=
      ( wi ex impd ) ABCDABCDFEGH $.
  $}

  ${
    exp31.1 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
    $( An exportation inference.  (Contributed by NM, 26-Apr-1994.) $)
    exp31 $p |- ( ph -> ( ps -> ( ch -> th ) ) ) $=
      ( wi wa ex ) ABCDFABGCDEHH $.
  $}

  ${
    exp32.1 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
    $( An exportation inference.  (Contributed by NM, 26-Apr-1994.) $)
    exp32 $p |- ( ph -> ( ps -> ( ch -> th ) ) ) $=
      ( wa ex expd ) ABCDABCFDEGH $.
  $}

  ${
    exp4a.1 $e |- ( ph -> ( ps -> ( ( ch /\ th ) -> ta ) ) ) $.
    $( An exportation inference.  (Contributed by NM, 26-Apr-1994.) $)
    exp4a $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $=
      ( wa wi impexp imbitrdi ) ABCDGEHCDEHHFCDEIJ $.
  $}

  ${
    exp4b.1 $e |- ( ( ph /\ ps ) -> ( ( ch /\ th ) -> ta ) ) $.
    $( An exportation inference.  (Contributed by NM, 26-Apr-1994.)  (Proof
       shortened by Wolf Lammen, 23-Nov-2012.) $)
    exp4b $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $=
      ( wa wi ex exp4a ) ABCDEABCDGEHFIJ $.
  $}

  ${
    exp4c.1 $e |- ( ph -> ( ( ( ps /\ ch ) /\ th ) -> ta ) ) $.
    $( An exportation inference.  (Contributed by NM, 26-Apr-1994.) $)
    exp4c $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $=
      ( wi wa expd ) ABCDEGABCHDEFII $.
  $}

  ${
    exp4d.1 $e |- ( ph -> ( ( ps /\ ( ch /\ th ) ) -> ta ) ) $.
    $( An exportation inference.  (Contributed by NM, 26-Apr-1994.) $)
    exp4d $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $=
      ( wa expd exp4a ) ABCDEABCDGEFHI $.
  $}

  ${
    exp41.1 $e |- ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) -> ta ) $.
    $( An exportation inference.  (Contributed by NM, 26-Apr-1994.) $)
    exp41 $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $=
      ( wi wa ex exp31 ) ABCDEGABHCHDEFIJ $.
  $}

  ${
    exp42.1 $e |- ( ( ( ph /\ ( ps /\ ch ) ) /\ th ) -> ta ) $.
    $( An exportation inference.  (Contributed by NM, 26-Apr-1994.) $)
    exp42 $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $=
      ( wi wa exp31 expd ) ABCDEGABCHDEFIJ $.
  $}

  ${
    exp43.1 $e |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) -> ta ) $.
    $( An exportation inference.  (Contributed by NM, 26-Apr-1994.) $)
    exp43 $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $=
      ( wa ex exp4b ) ABCDEABGCDGEFHI $.
  $}

  ${
    exp44.1 $e |- ( ( ph /\ ( ( ps /\ ch ) /\ th ) ) -> ta ) $.
    $( An exportation inference.  (Contributed by NM, 26-Apr-1994.) $)
    exp44 $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $=
      ( wi wa exp32 expd ) ABCDEGABCHDEFIJ $.
  $}

  ${
    exp45.1 $e |- ( ( ph /\ ( ps /\ ( ch /\ th ) ) ) -> ta ) $.
    $( An exportation inference.  (Contributed by NM, 26-Apr-1994.) $)
    exp45 $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $=
      ( wa exp32 exp4a ) ABCDEABCDGEFHI $.
  $}

  ${
    expr.1 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
    $( Export a wff from a right conjunct.  (Contributed by Jeff Hankins,
       30-Aug-2009.) $)
    expr $p |- ( ( ph /\ ps ) -> ( ch -> th ) ) $=
      ( wi exp32 imp ) ABCDFABCDEGH $.
  $}

  ${
    exp5c.1 $e |- ( ph -> ( ( ps /\ ch ) -> ( ( th /\ ta ) -> et ) ) ) $.
    $( An exportation inference.  (Contributed by Jeff Hankins, 7-Jul-2009.) $)
    exp5c $p |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $=
      ( wi wa exp4a expd ) ABCDEFHHABCIDEFGJK $.
  $}

  ${
    exp53.1 $e |- ( ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) /\ ta ) -> et ) $.
    $( An exportation inference.  (Contributed by Jeff Hankins,
       30-Aug-2009.) $)
    exp53 $p |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $=
      ( wi wa ex exp43 ) ABCDEFHABICDIIEFGJK $.
  $}

  ${
    expl.1 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
    $( Export a wff from a left conjunct.  (Contributed by Jeff Hankins,
       28-Aug-2009.) $)
    expl $p |- ( ph -> ( ( ps /\ ch ) -> th ) ) $=
      ( exp31 impd ) ABCDABCDEFG $.
  $}

  ${
    impr.1 $e |- ( ( ph /\ ps ) -> ( ch -> th ) ) $.
    $( Import a wff into a right conjunct.  (Contributed by Jeff Hankins,
       30-Aug-2009.) $)
    impr $p |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $=
      ( wi ex imp32 ) ABCDABCDFEGH $.
  $}

  ${
    impl.1 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
    $( Export a wff from a left conjunct.  (Contributed by Mario Carneiro,
       9-Jul-2014.) $)
    impl $p |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $=
      ( expd imp31 ) ABCDABCDEFG $.
  $}

  ${
    impac.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Importation with conjunction in consequent.  (Contributed by NM,
       9-Aug-1994.) $)
    impac $p |- ( ( ph /\ ps ) -> ( ch /\ ps ) ) $=
      ( wa ancrd imp ) ABCBEABCDFG $.
  $}

  ${
    exbiri.1 $e |- ( ( ph /\ ps ) -> ( ch <-> th ) ) $.
    $( Inference form of ~ exbir .  (Contributed by Alan Sare, 31-Dec-2011.)
       (Proof shortened by Wolf Lammen, 27-Jan-2013.) $)
    exbiri $p |- ( ph -> ( ps -> ( th -> ch ) ) ) $=
      ( wa biimpar exp31 ) ABDCABFCDEGH $.
  $}

  ${
    pm3.26bda.1 $e |- ( ph -> ( ps <-> ( ch /\ th ) ) ) $.
    $( Deduction eliminating a conjunct.  (Contributed by NM, 22-Oct-2007.) $)
    simprbda $p |- ( ( ph /\ ps ) -> ch ) $=
      ( wa biimpa simpld ) ABFCDABCDFEGH $.

    $( Deduction eliminating a conjunct.  (Contributed by NM, 22-Oct-2007.) $)
    simplbda $p |- ( ( ph /\ ps ) -> th ) $=
      ( wa biimpa simprd ) ABFCDABCDFEGH $.
  $}

  ${
    pm3.26bi2.1 $e |- ( ph <-> ( ps /\ ch ) ) $.
    $( Deduction eliminating a conjunct.  (Contributed by Alan Sare,
       31-Dec-2011.) $)
    simplbi2 $p |- ( ps -> ( ch -> ph ) ) $=
      ( wa biimpri ex ) BCAABCEDFG $.
  $}

  ${
    birani.1 $e |- ( ph <-> ps ) $.
    $( Inference adding a conjunct to the left-hand side of a biconditional.
       (Contributed by Matthew House, 22-May-2026.) $)
    birani $p |- ( ( ph /\ ch ) -> ps ) $=
      ( biimpi adantr ) ABCABDEF $.

    $( Inference adding a conjunct to the left-hand side of a biconditional.
       (Contributed by Matthew House, 22-May-2026.) $)
    bilani $p |- ( ( ch /\ ph ) -> ps ) $=
      ( biimpi adantl ) ABCABDEF $.

    $( Inference adding a conjunct to the right-hand side of a biconditional.
       (Contributed by Matthew House, 22-May-2026.) $)
    biranri $p |- ( ( ps /\ ch ) -> ph ) $=
      ( biimpri adantr ) BACABDEF $.

    $( Inference adding a conjunct to the right-hand side of a biconditional.
       (Contributed by Matthew House, 22-May-2026.) $)
    bilanri $p |- ( ( ch /\ ps ) -> ph ) $=
      ( biimpri adantl ) BACABDEF $.
  $}

  ${
    simpl2im.1 $e |- ( ph -> ( ps /\ ch ) ) $.
    simpl2im.2 $e |- ( ch -> th ) $.
    $( Implication from an eliminated conjunct implied by the antecedent.
       (Contributed by BJ/AV, 5-Apr-2021.) $)
    simpl2im $p |- ( ph -> th ) $=
      ( wa simpr 3syl ) ABCGCDEBCHFI $.
  $}

  ${
    simplbiim.1 $e |- ( ph <-> ( ps /\ ch ) ) $.
    simplbiim.2 $e |- ( ch -> th ) $.
    $( Implication from an eliminated conjunct equivalent to the antecedent.
       (Contributed by Jonathan Ben-Naim, 3-Jun-2011.) $)
    simplbiim $p |- ( ph -> th ) $=
      ( wa adantl sylbi ) ABCGDECDBFHI $.
  $}

  $( A theorem similar to the standard definition of the biconditional.
     Definition of [Margaris] p. 49.  (Contributed by NM, 5-Aug-1993.)
     (Revised by NM, 31-Jan-2015.) $)
  dfbi2 $p |- ( ( ph <-> ps ) <-> ( ( ph -> ps ) /\ ( ps -> ph ) ) ) $=
    ( wb wi wa df-bi simpli simpri impbii ) ABCZABDBADEZJKDZKJDZABFZGLMNHI $.

  $( Implication in terms of biconditional and conjunction.  Theorem *4.71 of
     [WhiteheadRussell] p. 120.  (Contributed by NM, 5-Aug-1993.)  (Proof
     shortened by Wolf Lammen, 2-Dec-2012.) $)
  pm4.71 $p |- ( ( ph -> ps ) <-> ( ph <-> ( ph /\ ps ) ) ) $=
    ( wa wi wb simpl biantru anclb dfbi2 3bitr4i ) AABCZDZLKADZCABDAKEMLABFGABH
    AKIJ $.

  $( Implication in terms of biconditional and conjunction.  Theorem *4.71 of
     [WhiteheadRussell] p. 120 (with conjunct reversed).  (Contributed by NM,
     25-Jul-1999.) $)
  pm4.71r $p |- ( ( ph -> ps ) <-> ( ph <-> ( ps /\ ph ) ) ) $=
    ( wi wa wb pm4.71 ancom bibi2i bitri ) ABCAABDZEABADZEABFJKAABGHI $.

  ${
    pm4.71i.1 $e |- ( ph -> ps ) $.
    $( Inference converting an implication to a biconditional with conjunction.
       Inference from Theorem *4.71 of [WhiteheadRussell] p. 120.  (Contributed
       by NM, 4-Jan-2004.) $)
    pm4.71i $p |- ( ph <-> ( ph /\ ps ) ) $=
      ( wi wa wb pm4.71 mpbi ) ABDAABEFCABGH $.
  $}

  ${
    pm4.71ri.1 $e |- ( ph -> ps ) $.
    $( Inference converting an implication to a biconditional with conjunction.
       Inference from Theorem *4.71 of [WhiteheadRussell] p. 120 (with conjunct
       reversed).  (Contributed by NM, 1-Dec-2003.) $)
    pm4.71ri $p |- ( ph <-> ( ps /\ ph ) ) $=
      ( wi wa wb pm4.71r mpbi ) ABDABAEFCABGH $.
  $}

  ${
    pm4.71rd.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction converting an implication to a biconditional with conjunction.
       Deduction from Theorem *4.71 of [WhiteheadRussell] p. 120.  (Contributed
       by Mario Carneiro, 25-Dec-2016.) $)
    pm4.71d $p |- ( ph -> ( ps <-> ( ps /\ ch ) ) ) $=
      ( wi wa wb pm4.71 sylib ) ABCEBBCFGDBCHI $.

    $( Deduction converting an implication to a biconditional with conjunction.
       Deduction from Theorem *4.71 of [WhiteheadRussell] p. 120.  (Contributed
       by NM, 10-Feb-2005.) $)
    pm4.71rd $p |- ( ph -> ( ps <-> ( ch /\ ps ) ) ) $=
      ( wi wa wb pm4.71r sylib ) ABCEBCBFGDBCHI $.
  $}

  $( Theorem *4.24 of [WhiteheadRussell] p. 117.  (Contributed by NM,
     3-Jan-2005.)  (Revised by NM, 14-Mar-2014.) $)
  pm4.24 $p |- ( ph <-> ( ph /\ ph ) ) $=
    ( id pm4.71i ) AAABC $.

  $( Idempotent law for conjunction.  (Contributed by NM, 5-Aug-1993.)  (Proof
     shortened by Wolf Lammen, 14-Mar-2014.) $)
  anidm $p |- ( ( ph /\ ph ) <-> ph ) $=
    ( wa pm4.24 bicomi ) AAABACD $.

  ${
    anidms.1 $e |- ( ( ph /\ ph ) -> ps ) $.
    $( Inference from idempotent law for conjunction.  (Contributed by NM,
       15-Jun-1994.) $)
    anidms $p |- ( ph -> ps ) $=
      ( ex pm2.43i ) ABAABCDE $.
  $}

  $( Conjunction idempotence with antecedent.  (Contributed by Roy F. Longton,
     8-Aug-2005.) $)
  anidmdbi $p |- ( ( ph -> ( ps /\ ps ) ) <-> ( ph -> ps ) ) $=
    ( wa anidm imbi2i ) BBCBABDE $.

  ${
    anasss.1 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
    $( Associative law for conjunction applied to antecedent (eliminates
       syllogism).  (Contributed by NM, 15-Nov-2002.) $)
    anasss $p |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $=
      ( exp31 imp32 ) ABCDABCDEFG $.
  $}

  ${
    anassrs.1 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
    $( Associative law for conjunction applied to antecedent (eliminates
       syllogism).  (Contributed by NM, 15-Nov-2002.) $)
    anassrs $p |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $=
      ( exp32 imp31 ) ABCDABCDEFG $.
  $}

  $( Associative law for conjunction.  Theorem *4.32 of [WhiteheadRussell]
     p. 118.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf
     Lammen, 24-Nov-2012.) $)
  anass $p |- ( ( ( ph /\ ps ) /\ ch ) <-> ( ph /\ ( ps /\ ch ) ) ) $=
    ( wa id anassrs anasss impbii ) ABDCDZABCDDZABCJJEFABCIIEGH $.

  ${
    sylanl1.1 $e |- ( ph -> ps ) $.
    sylanl1.2 $e |- ( ( ( ps /\ ch ) /\ th ) -> ta ) $.
    $( A syllogism inference.  (Contributed by NM, 10-Mar-2005.) $)
    sylanl1 $p |- ( ( ( ph /\ ch ) /\ th ) -> ta ) $=
      ( wa anim1i sylan ) ACHBCHDEABCFIGJ $.
  $}

  ${
    sylanl2.1 $e |- ( ph -> ch ) $.
    sylanl2.2 $e |- ( ( ( ps /\ ch ) /\ th ) -> ta ) $.
    $( A syllogism inference.  (Contributed by NM, 1-Jan-2005.) $)
    sylanl2 $p |- ( ( ( ps /\ ph ) /\ th ) -> ta ) $=
      ( wa anim2i sylan ) BAHBCHDEACBFIGJ $.
  $}

  ${
    sylanr1.1 $e |- ( ph -> ch ) $.
    sylanr1.2 $e |- ( ( ps /\ ( ch /\ th ) ) -> ta ) $.
    $( A syllogism inference.  (Contributed by NM, 9-Apr-2005.) $)
    sylanr1 $p |- ( ( ps /\ ( ph /\ th ) ) -> ta ) $=
      ( wa anim1i sylan2 ) ADHBCDHEACDFIGJ $.
  $}

  ${
    sylanr2.1 $e |- ( ph -> th ) $.
    sylanr2.2 $e |- ( ( ps /\ ( ch /\ th ) ) -> ta ) $.
    $( A syllogism inference.  (Contributed by NM, 9-Apr-2005.) $)
    sylanr2 $p |- ( ( ps /\ ( ch /\ ph ) ) -> ta ) $=
      ( wa anim2i sylan2 ) CAHBCDHEADCFIGJ $.
  $}

  ${
    sylani.1 $e |- ( ph -> ch ) $.
    sylani.2 $e |- ( ps -> ( ( ch /\ th ) -> ta ) ) $.
    $( A syllogism inference.  (Contributed by NM, 2-May-1996.) $)
    sylani $p |- ( ps -> ( ( ph /\ th ) -> ta ) ) $=
      ( wi a1i syland ) BACDEACHBFIGJ $.
  $}

  ${
    sylan2i.1 $e |- ( ph -> th ) $.
    sylan2i.2 $e |- ( ps -> ( ( ch /\ th ) -> ta ) ) $.
    $( A syllogism inference.  (Contributed by NM, 1-Aug-1994.) $)
    sylan2i $p |- ( ps -> ( ( ch /\ ph ) -> ta ) ) $=
      ( wi a1i sylan2d ) BADCEADHBFIGJ $.
  $}

  ${
    syl2ani.1 $e |- ( ph -> ch ) $.
    syl2ani.2 $e |- ( et -> th ) $.
    syl2ani.3 $e |- ( ps -> ( ( ch /\ th ) -> ta ) ) $.
    $( A syllogism inference.  (Contributed by NM, 3-Aug-1999.) $)
    syl2ani $p |- ( ps -> ( ( ph /\ et ) -> ta ) ) $=
      ( sylan2i sylani ) ABCFEGFBCDEHIJK $.
  $}

  ${
    sylan9.1 $e |- ( ph -> ( ps -> ch ) ) $.
    sylan9.2 $e |- ( th -> ( ch -> ta ) ) $.
    $( Nested syllogism inference conjoining dissimilar antecedents.
       (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Andrew Salmon,
       7-May-2011.) $)
    sylan9 $p |- ( ( ph /\ th ) -> ( ps -> ta ) ) $=
      ( wi syl9 imp ) ADBEHABCDEFGIJ $.
  $}

  ${
    sylan9r.1 $e |- ( ph -> ( ps -> ch ) ) $.
    sylan9r.2 $e |- ( th -> ( ch -> ta ) ) $.
    $( Nested syllogism inference conjoining dissimilar antecedents.
       (Contributed by NM, 5-Aug-1993.) $)
    sylan9r $p |- ( ( th /\ ph ) -> ( ps -> ta ) ) $=
      ( wi syl9r imp ) DABEHABCDEFGIJ $.
  $}

  ${
    syl2anc.1 $e |- ( ph -> ps ) $.
    syl2anc.2 $e |- ( ph -> ch ) $.
    syl2anc.3 $e |- ( ( ps /\ ch ) -> th ) $.
    $( Syllogism inference combined with contraction.  (Contributed by NM,
       16-Mar-2012.) $)
    syl2anc $p |- ( ph -> th ) $=
      ( ex sylc ) ABCDEFBCDGHI $.
  $}

  ${
    syl2anc2.1 $e |- ( ph -> ps ) $.
    syl2anc2.2 $e |- ( ps -> ch ) $.
    syl2anc2.3 $e |- ( ( ps /\ ch ) -> th ) $.
    $( Double syllogism inference combined with contraction.  (Contributed by
       BTernaryTau, 29-Sep-2023.) $)
    syl2anc2 $p |- ( ph -> th ) $=
      ( syl syl2anc ) ABCDEABCEFHGI $.
  $}

  ${
    sylancl.1 $e |- ( ph -> ps ) $.
    sylancl.2 $e |- ch $.
    sylancl.3 $e |- ( ( ps /\ ch ) -> th ) $.
    $( Syllogism inference combined with modus ponens.  (Contributed by Jeff
       Madsen, 2-Sep-2009.) $)
    sylancl $p |- ( ph -> th ) $=
      ( a1i syl2anc ) ABCDECAFHGI $.
  $}

  ${
    sylancr.1 $e |- ps $.
    sylancr.2 $e |- ( ph -> ch ) $.
    sylancr.3 $e |- ( ( ps /\ ch ) -> th ) $.
    $( Syllogism inference combined with modus ponens.  (Contributed by Jeff
       Madsen, 2-Sep-2009.) $)
    sylancr $p |- ( ph -> th ) $=
      ( a1i syl2anc ) ABCDBAEHFGI $.
  $}

  ${
    sylanblc.1 $e |- ( ph -> ps ) $.
    sylanblc.2 $e |- ch $.
    sylanblc.3 $e |- ( ( ps /\ ch ) <-> th ) $.
    $( Syllogism inference combined with a biconditional.  (Contributed by BJ,
       25-Apr-2019.) $)
    sylanblc $p |- ( ph -> th ) $=
      ( wa biimpi sylancl ) ABCDEFBCHDGIJ $.
  $}

  ${
    sylanblrc.1 $e |- ( ph -> ps ) $.
    sylanblrc.2 $e |- ch $.
    sylanblrc.3 $e |- ( th <-> ( ps /\ ch ) ) $.
    $( Syllogism inference combined with a biconditional.  (Contributed by BJ,
       25-Apr-2019.) $)
    sylanblrc $p |- ( ph -> th ) $=
      ( wa biimpri sylancl ) ABCDEFDBCHGIJ $.
  $}

  ${
    sylanbrc.1 $e |- ( ph -> ps ) $.
    sylanbrc.2 $e |- ( ph -> ch ) $.
    sylanbrc.3 $e |- ( th <-> ( ps /\ ch ) ) $.
    $( Syllogism inference.  (Contributed by Jeff Madsen, 2-Sep-2009.) $)
    sylanbrc $p |- ( ph -> th ) $=
      ( wa jca sylibr ) ABCHDABCEFIGJ $.
  $}

  ${
    sylancb.1 $e |- ( ph <-> ps ) $.
    sylancb.2 $e |- ( ph <-> ch ) $.
    sylancb.3 $e |- ( ( ps /\ ch ) -> th ) $.
    $( A syllogism inference combined with contraction.  (Contributed by NM,
       3-Sep-2004.) $)
    sylancb $p |- ( ph -> th ) $=
      ( syl2anb anidms ) ADABCDAEFGHI $.
  $}

  ${
    sylancbr.1 $e |- ( ps <-> ph ) $.
    sylancbr.2 $e |- ( ch <-> ph ) $.
    sylancbr.3 $e |- ( ( ps /\ ch ) -> th ) $.
    $( A syllogism inference combined with contraction.  (Contributed by NM,
       3-Sep-2004.) $)
    sylancbr $p |- ( ph -> th ) $=
      ( syl2anbr anidms ) ADABCDAEFGHI $.
  $}

  ${
    sylancom.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    sylancom.2 $e |- ( ( ch /\ ps ) -> th ) $.
    $( Syllogism inference with commutation of antecents.  (Contributed by NM,
       2-Jul-2008.) $)
    sylancom $p |- ( ( ph /\ ps ) -> th ) $=
      ( wa simpr syl2anc ) ABGCBDEABHFI $.
  $}

  ${
    mpdan.1 $e |- ( ph -> ps ) $.
    mpdan.2 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( An inference based on modus ponens.  (Contributed by NM, 23-May-1999.)
       (Proof shortened by Wolf Lammen, 22-Nov-2012.) $)
    mpdan $p |- ( ph -> ch ) $=
      ( id syl2anc ) AABCAFDEG $.
  $}

  ${
    mpancom.1 $e |- ( ps -> ph ) $.
    mpancom.2 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( An inference based on modus ponens with commutation of antecedents.
       (Contributed by NM, 28-Oct-2003.)  (Proof shortened by Wolf Lammen,
       7-Apr-2013.) $)
    mpancom $p |- ( ps -> ch ) $=
      ( id syl2anc ) BABCDBFEG $.
  $}

  ${
    mpidan.1 $e |- ( ph -> ch ) $.
    mpidan.2 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
    $( A deduction which "stacks" a hypothesis.  (Contributed by Stanislas
       Polu, 9-Mar-2020.)  (Proof shortened by Wolf Lammen, 28-Mar-2021.) $)
    mpidan $p |- ( ( ph /\ ps ) -> th ) $=
      ( wa adantr mpdan ) ABGCDACBEHFI $.
  $}

  ${
    mpan.1 $e |- ph $.
    mpan.2 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( An inference based on modus ponens.  (Contributed by NM, 30-Aug-1993.)
       (Proof shortened by Wolf Lammen, 7-Apr-2013.) $)
    mpan $p |- ( ps -> ch ) $=
      ( a1i mpancom ) ABCABDFEG $.
  $}

  ${
    mpan2.1 $e |- ps $.
    mpan2.2 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( An inference based on modus ponens.  (Contributed by NM, 16-Sep-1993.)
       (Proof shortened by Wolf Lammen, 19-Nov-2012.) $)
    mpan2 $p |- ( ph -> ch ) $=
      ( a1i mpdan ) ABCBADFEG $.
  $}

  ${
    mp2an.1 $e |- ph $.
    mp2an.2 $e |- ps $.
    mp2an.3 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( An inference based on modus ponens.  (Contributed by NM,
       13-Apr-1995.) $)
    mp2an $p |- ch $=
      ( mpan ax-mp ) BCEABCDFGH $.
  $}

  ${
    mp4an.1 $e |- ph $.
    mp4an.2 $e |- ps $.
    mp4an.3 $e |- ch $.
    mp4an.4 $e |- th $.
    mp4an.5 $e |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) -> ta ) $.
    $( An inference based on modus ponens.  (Contributed by Jeff Madsen,
       15-Jun-2011.) $)
    mp4an $p |- ta $=
      ( wa pm3.2i mp2an ) ABKCDKEABFGLCDHILJM $.
  $}

  ${
    mpan2d.1 $e |- ( ph -> ch ) $.
    mpan2d.2 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
    $( A deduction based on modus ponens.  (Contributed by NM, 12-Dec-2004.) $)
    mpan2d $p |- ( ph -> ( ps -> th ) ) $=
      ( expd mpid ) ABCDEABCDFGH $.
  $}

  ${
    mpand.1 $e |- ( ph -> ps ) $.
    mpand.2 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
    $( A deduction based on modus ponens.  (Contributed by NM, 12-Dec-2004.)
       (Proof shortened by Wolf Lammen, 7-Apr-2013.) $)
    mpand $p |- ( ph -> ( ch -> th ) ) $=
      ( ancomsd mpan2d ) ACBDEABCDFGH $.
  $}

  ${
    mpani.1 $e |- ps $.
    mpani.2 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
    $( An inference based on modus ponens.  (Contributed by NM, 10-Apr-1994.)
       (Proof shortened by Wolf Lammen, 19-Nov-2012.) $)
    mpani $p |- ( ph -> ( ch -> th ) ) $=
      ( a1i mpand ) ABCDBAEGFH $.
  $}

  ${
    mpan2i.1 $e |- ch $.
    mpan2i.2 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
    $( An inference based on modus ponens.  (Contributed by NM, 10-Apr-1994.)
       (Proof shortened by Wolf Lammen, 19-Nov-2012.) $)
    mpan2i $p |- ( ph -> ( ps -> th ) ) $=
      ( a1i mpan2d ) ABCDCAEGFH $.
  $}

  ${
    mp2ani.1 $e |- ps $.
    mp2ani.2 $e |- ch $.
    mp2ani.3 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
    $( An inference based on modus ponens.  (Contributed by NM,
       12-Dec-2004.) $)
    mp2ani $p |- ( ph -> th ) $=
      ( mpani mpi ) ACDFABCDEGHI $.
  $}

  ${
    mp2and.1 $e |- ( ph -> ps ) $.
    mp2and.2 $e |- ( ph -> ch ) $.
    mp2and.3 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
    $( A deduction based on modus ponens.  (Contributed by NM, 12-Dec-2004.) $)
    mp2and $p |- ( ph -> th ) $=
      ( mpand mpd ) ACDFABCDEGHI $.
  $}

  ${
    mpanl1.1 $e |- ph $.
    mpanl1.2 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
    $( An inference based on modus ponens.  (Contributed by NM, 16-Aug-1994.)
       (Proof shortened by Wolf Lammen, 7-Apr-2013.) $)
    mpanl1 $p |- ( ( ps /\ ch ) -> th ) $=
      ( wa jctl sylan ) BABGCDBAEHFI $.
  $}

  ${
    mpanl2.1 $e |- ps $.
    mpanl2.2 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
    $( An inference based on modus ponens.  (Contributed by NM, 16-Aug-1994.)
       (Proof shortened by Andrew Salmon, 7-May-2011.) $)
    mpanl2 $p |- ( ( ph /\ ch ) -> th ) $=
      ( wa jctr sylan ) AABGCDABEHFI $.
  $}

  ${
    mpanl12.1 $e |- ph $.
    mpanl12.2 $e |- ps $.
    mpanl12.3 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
    $( An inference based on modus ponens.  (Contributed by NM,
       13-Jul-2005.) $)
    mpanl12 $p |- ( ch -> th ) $=
      ( mpanl1 mpan ) BCDFABCDEGHI $.
  $}

  ${
    mpanr1.1 $e |- ps $.
    mpanr1.2 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
    $( An inference based on modus ponens.  (Contributed by NM, 3-May-1994.)
       (Proof shortened by Andrew Salmon, 7-May-2011.) $)
    mpanr1 $p |- ( ( ph /\ ch ) -> th ) $=
      ( anassrs mpanl2 ) ABCDEABCDFGH $.
  $}

  ${
    mpanr2.1 $e |- ch $.
    mpanr2.2 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
    $( An inference based on modus ponens.  (Contributed by NM, 3-May-1994.)
       (Proof shortened by Andrew Salmon, 7-May-2011.)  (Proof shortened by
       Wolf Lammen, 7-Apr-2013.) $)
    mpanr2 $p |- ( ( ph /\ ps ) -> th ) $=
      ( wa jctr sylan2 ) BABCGDBCEHFI $.
  $}

  ${
    mpanr12.1 $e |- ps $.
    mpanr12.2 $e |- ch $.
    mpanr12.3 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
    $( An inference based on modus ponens.  (Contributed by NM,
       24-Jul-2009.) $)
    mpanr12 $p |- ( ph -> th ) $=
      ( mpanr1 mpan2 ) ACDFABCDEGHI $.
  $}

  ${
    mpanlr1.1 $e |- ps $.
    mpanlr1.2 $e |- ( ( ( ph /\ ( ps /\ ch ) ) /\ th ) -> ta ) $.
    $( An inference based on modus ponens.  (Contributed by NM, 30-Dec-2004.)
       (Proof shortened by Wolf Lammen, 7-Apr-2013.) $)
    mpanlr1 $p |- ( ( ( ph /\ ch ) /\ th ) -> ta ) $=
      ( wa jctl sylanl2 ) CABCHDECBFIGJ $.
  $}

  ${
    mpbirand.1 $e |- ( ph -> ch ) $.
    mpbirand.2 $e |- ( ph -> ( ps <-> ( ch /\ th ) ) ) $.
    $( Detach truth from conjunction in biconditional.  (Contributed by Glauco
       Siliprandi, 3-Mar-2021.) $)
    mpbirand $p |- ( ph -> ( ps <-> th ) ) $=
      ( wa biantrurd bitr4d ) ABCDGDFACDEHI $.
  $}

  ${
    mpbiran2d.1 $e |- ( ph -> th ) $.
    mpbiran2d.2 $e |- ( ph -> ( ps <-> ( ch /\ th ) ) ) $.
    $( Detach truth from conjunction in biconditional.  Deduction form.
       (Contributed by Peter Mazsa, 24-Sep-2022.) $)
    mpbiran2d $p |- ( ph -> ( ps <-> ch ) ) $=
      ( wa biantrud bitr4d ) ABCDGCFADCEHI $.
  $}

  ${
    pm5.74da.1 $e |- ( ( ph /\ ps ) -> ( ch <-> th ) ) $.
    $( Distribution of implication over biconditional (deduction form).
       (Contributed by NM, 4-May-2007.) $)
    pm5.74da $p |- ( ph -> ( ( ps -> ch ) <-> ( ps -> th ) ) ) $=
      ( wb ex pm5.74d ) ABCDABCDFEGH $.
  $}

  $( Distribution of implication with conjunction.  (Contributed by NM,
     31-May-1999.)  (Proof shortened by Wolf Lammen, 6-Dec-2012.) $)
  imdistan $p |- ( ( ph -> ( ps -> ch ) ) <->
                ( ( ph /\ ps ) -> ( ph /\ ch ) ) ) $=
    ( wi wa pm5.42 impexp bitr4i ) ABCDDABACEZDDABEIDABCFABIGH $.

  ${
    imdistani.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Distribution of implication with conjunction.  (Contributed by NM,
       1-Aug-1994.) $)
    imdistani $p |- ( ( ph /\ ps ) -> ( ph /\ ch ) ) $=
      ( wa anc2li imp ) ABACEABCDFG $.
  $}

  ${
    imdistanri.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Distribution of implication with conjunction.  (Contributed by NM,
       8-Jan-2002.) $)
    imdistanri $p |- ( ( ps /\ ph ) -> ( ch /\ ph ) ) $=
      ( com12 impac ) BACABCDEF $.
  $}

  ${
    imdistand.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    $( Distribution of implication with conjunction (deduction form).
       (Contributed by NM, 27-Aug-2004.) $)
    imdistand $p |- ( ph -> ( ( ps /\ ch ) -> ( ps /\ th ) ) ) $=
      ( wi wa imdistan sylib ) ABCDFFBCGBDGFEBCDHI $.
  $}

  ${
    imdistanda.1 $e |- ( ( ph /\ ps ) -> ( ch -> th ) ) $.
    $( Distribution of implication with conjunction (deduction version with
       conjoined antecedent).  (Contributed by Jeff Madsen, 19-Jun-2011.) $)
    imdistanda $p |- ( ph -> ( ( ps /\ ch ) -> ( ps /\ th ) ) ) $=
      ( wi ex imdistand ) ABCDABCDFEGH $.
  $}

  ${
    syldanl.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    syldanl.2 $e |- ( ( ( ph /\ ch ) /\ th ) -> ta ) $.
    $( A syllogism deduction with conjoined antecedents.  (Contributed by Jeff
       Madsen, 20-Jun-2011.) $)
    syldanl $p |- ( ( ( ph /\ ps ) /\ th ) -> ta ) $=
      ( wa ex imdistani sylan ) ABHACHDEABCABCFIJGK $.
  $}

  ${
    pm5.32d.1 $e |- ( ph -> ( ps -> ( ch <-> th ) ) ) $.
    $( Distribution of implication over biconditional (deduction form).
       (Contributed by NM, 29-Oct-1996.)  (Revised by NM, 31-Jan-2015.) $)
    pm5.32d $p |- ( ph -> ( ( ps /\ ch ) <-> ( ps /\ th ) ) ) $=
      ( wa wb wi biimp syl6 imdistand biimpr impbid ) ABCFBDFABCDABCDGZCDHECDIJ
      KABDCABNDCHECDLJKM $.

    $( Distribution of implication over biconditional (deduction form).
       (Contributed by NM, 25-Dec-2004.) $)
    pm5.32rd $p |- ( ph -> ( ( ch /\ ps ) <-> ( th /\ ps ) ) ) $=
      ( wa pm5.32d ancom 3bitr4g ) ABCFBDFCBFDBFABCDEGCBHDBHI $.
  $}

  ${
    pm5.32da.1 $e |- ( ( ph /\ ps ) -> ( ch <-> th ) ) $.
    $( Distribution of implication over biconditional (deduction form).
       (Contributed by NM, 9-Dec-2006.) $)
    pm5.32da $p |- ( ph -> ( ( ps /\ ch ) <-> ( ps /\ th ) ) ) $=
      ( wb ex pm5.32d ) ABCDABCDFEGH $.
  $}

  $( Distribution of implication over biconditional.  Theorem *5.32 of
     [WhiteheadRussell] p. 125.  (Contributed by NM, 1-Aug-1994.)  (Revised by
     NM, 31-Jan-2015.) $)
  pm5.32 $p |- ( ( ph -> ( ps <-> ch ) ) <->
               ( ( ph /\ ps ) <-> ( ph /\ ch ) ) ) $=
    ( wb wi wa id pm5.32d ibar bibi12d biimprcd impbii ) ABCDZEZABFZACFZDZNABCN
    GHAMQABOCPABIACIJKL $.

  ${
    pm5.32i.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Distribution of implication over biconditional (inference form).
       (Contributed by NM, 1-Aug-1994.) $)
    pm5.32i $p |- ( ( ph /\ ps ) <-> ( ph /\ ch ) ) $=
      ( wb wi wa pm5.32 mpbi ) ABCEFABGACGEDABCHI $.

    $( Distribution of implication over biconditional (inference form).
       (Contributed by NM, 12-Mar-1995.) $)
    pm5.32ri $p |- ( ( ps /\ ph ) <-> ( ch /\ ph ) ) $=
      ( wa pm5.32i ancom 3bitr4i ) ABEACEBAECAEABCDFBAGCAGH $.
  $}

  ${
    biadan2.1 $e |- ( ph -> ps ) $.
    biadan2.2 $e |- ( ps -> ( ph <-> ch ) ) $.
    $( Add a conjunction to an equivalence.  (Contributed by Jeff Madsen,
       20-Jun-2011.) $)
    biadan2 $p |- ( ph <-> ( ps /\ ch ) ) $=
      ( wa pm4.71ri pm5.32i bitri ) ABAFBCFABDGBACEHI $.
  $}

  ${
    bi.aa $e |- ( ph <-> ps ) $.
    $( Introduce a left conjunct to both sides of a logical equivalence.
       (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen,
       16-Nov-2013.) $)
    anbi2i $p |- ( ( ch /\ ph ) <-> ( ch /\ ps ) ) $=
      ( wb a1i pm5.32i ) CABABECDFG $.

    $( Introduce a right conjunct to both sides of a logical equivalence.
       (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen,
       16-Nov-2013.) $)
    anbi1i $p |- ( ( ph /\ ch ) <-> ( ps /\ ch ) ) $=
      ( wb a1i pm5.32ri ) CABABECDFG $.

    $( Variant of ~ anbi2i with commutation.  (Contributed by Jonathan
       Ben-Naim, 3-Jun-2011.)  (Proof shortened by Andrew Salmon,
       14-Jun-2011.) $)
    anbi2ci $p |- ( ( ph /\ ch ) <-> ( ch /\ ps ) ) $=
      ( wa anbi1i ancom bitri ) ACEBCECBEABCDFBCGH $.
  $}

  ${
    anbi12.1 $e |- ( ph <-> ps ) $.
    anbi12.2 $e |- ( ch <-> th ) $.
    $( Conjoin both sides of two equivalences.  (Contributed by NM,
       5-Aug-1993.) $)
    anbi12i $p |- ( ( ph /\ ch ) <-> ( ps /\ th ) ) $=
      ( wa anbi1i anbi2i bitri ) ACGBCGBDGABCEHCDBFIJ $.

    $( Variant of ~ anbi12i with commutation.  (Contributed by Jonathan
       Ben-Naim, 3-Jun-2011.) $)
    anbi12ci $p |- ( ( ph /\ ch ) <-> ( th /\ ps ) ) $=
      ( wa anbi12i ancom bitri ) ACGBDGDBGABCDEFHBDIJ $.
  $}

  ${
    sylan9bb.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    sylan9bb.2 $e |- ( th -> ( ch <-> ta ) ) $.
    $( Nested syllogism inference conjoining dissimilar antecedents.
       (Contributed by NM, 4-Mar-1995.) $)
    sylan9bb $p |- ( ( ph /\ th ) -> ( ps <-> ta ) ) $=
      ( wa wb adantr adantl bitrd ) ADHBCEABCIDFJDCEIAGKL $.
  $}

  ${
    sylan9bbr.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    sylan9bbr.2 $e |- ( th -> ( ch <-> ta ) ) $.
    $( Nested syllogism inference conjoining dissimilar antecedents.
       (Contributed by NM, 4-Mar-1995.) $)
    sylan9bbr $p |- ( ( th /\ ph ) -> ( ps <-> ta ) ) $=
      ( wb sylan9bb ancoms ) ADBEHABCDEFGIJ $.
  $}

  ${
    anbid.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Deduction adding a left conjunct to both sides of a logical equivalence.
       (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen,
       16-Nov-2013.) $)
    anbi2d $p |- ( ph -> ( ( th /\ ps ) <-> ( th /\ ch ) ) ) $=
      ( wb a1d pm5.32d ) ADBCABCFDEGH $.

    $( Deduction adding a right conjunct to both sides of a logical
       equivalence.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf
       Lammen, 16-Nov-2013.) $)
    anbi1d $p |- ( ph -> ( ( ps /\ th ) <-> ( ch /\ th ) ) ) $=
      ( wb a1d pm5.32rd ) ADBCABCFDEGH $.
  $}

  $( Introduce a right conjunct to both sides of a logical equivalence.
     Theorem *4.36 of [WhiteheadRussell] p. 118.  (Contributed by NM,
     3-Jan-2005.) $)
  anbi1 $p |- ( ( ph <-> ps ) -> ( ( ph /\ ch ) <-> ( ps /\ ch ) ) ) $=
    ( wb id anbi1d ) ABDZABCGEF $.

  $( Introduce a left conjunct to both sides of a logical equivalence.
     (Contributed by NM, 16-Nov-2013.) $)
  anbi2 $p |- ( ( ph <-> ps ) -> ( ( ch /\ ph ) <-> ( ch /\ ps ) ) ) $=
    ( wb id anbi2d ) ABDZABCGEF $.

  ${
    anbi1cd.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Introduce a proposition as left conjunct on the left-hand side and right
       conjunct on the right-hand side of an equivalence.  Deduction form.
       (Contributed by Peter Mazsa, 22-May-2021.) $)
    anbi1cd $p |- ( ph -> ( ( th /\ ps ) <-> ( ch /\ th ) ) ) $=
      ( wa anbi2d biancomd ) ADBFCDABCDEGH $.
  $}

  ${
    bianass.1 $e |- ( ph <-> ( ps /\ ch ) ) $.
    $( An inference to merge two lists of conjuncts.  (Contributed by Giovanni
       Mascellani, 23-May-2019.) $)
    bianass $p |- ( ( et /\ ph ) <-> ( ( et /\ ps ) /\ ch ) ) $=
      ( wa anbi2i anass bitr4i ) DAFDBCFZFDBFCFAJDEGDBCHI $.

    $( An inference to merge two lists of conjuncts.  (Contributed by Peter
       Mazsa, 24-Sep-2022.) $)
    bianassc $p |- ( ( et /\ ph ) <-> ( ( ps /\ et ) /\ ch ) ) $=
      ( wa bianass ancom anbi1i bitri ) DAFDBFZCFBDFZCFABCDEGKLCDBHIJ $.
  $}

  $( Swap two conjuncts.  (Contributed by Peter Mazsa, 18-Sep-2022.) $)
  an21 $p |- ( ( ( ph /\ ps ) /\ ch ) <-> ( ps /\ ( ph /\ ch ) ) ) $=
    ( wa biid bianassc bicomi ) BACDZDABDCDHACBHEFG $.

  $( Theorem *4.22 of [WhiteheadRussell] p. 117.  (Contributed by NM,
     3-Jan-2005.) $)
  bitr $p |- ( ( ( ph <-> ps ) /\ ( ps <-> ch ) ) -> ( ph <-> ch ) ) $=
    ( wb bibi1 biimpar ) ABDACDBCDABCEF $.

  ${
    anbi12d.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    anbi12d.2 $e |- ( ph -> ( th <-> ta ) ) $.
    $( Deduction joining two equivalences to form equivalence of conjunctions.
       (Contributed by NM, 5-Aug-1993.) $)
    anbi12d $p |- ( ph -> ( ( ps /\ th ) <-> ( ch /\ ta ) ) ) $=
      ( wa anbi1d anbi2d bitrd ) ABDHCDHCEHABCDFIADECGJK $.
  $}

  $( Modus ponens mixed with several conjunctions.  (Contributed by Jim
     Kingdon, 7-Jan-2018.) $)
  mpan10 $p |- ( ( ( ( ph -> ps ) /\ ch ) /\ ph ) -> ( ps /\ ch ) ) $=
    ( wi wa ancom anbi2i anass 3bitr4i id imp anim1i sylbi ) ABDZCEAEZNAEZCEZBC
    ENCAEZENACEZEOQRSNCAFGNCAHNACHIPBCNABNJKLM $.

  $( Theorem *5.3 of [WhiteheadRussell] p. 125.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Andrew Salmon, 7-May-2011.) $)
  pm5.3 $p |- ( ( ( ph /\ ps ) -> ch ) <->
               ( ( ph /\ ps ) -> ( ph /\ ch ) ) ) $=
    ( wa wi impexp imdistan bitri ) ABDZCEABCEEIACDEABCFABCGH $.

  ${
    adant2.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       4-May-1994.)  (Proof shortened by Wolf Lammen, 24-Nov-2012.) $)
    adantll $p |- ( ( ( th /\ ph ) /\ ps ) -> ch ) $=
      ( wa simpr sylan ) DAFABCDAGEH $.

    $( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       4-May-1994.)  (Proof shortened by Wolf Lammen, 24-Nov-2012.) $)
    adantlr $p |- ( ( ( ph /\ th ) /\ ps ) -> ch ) $=
      ( wa simpl sylan ) ADFABCADGEH $.

    $( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       4-May-1994.)  (Proof shortened by Wolf Lammen, 24-Nov-2012.) $)
    adantrl $p |- ( ( ph /\ ( th /\ ps ) ) -> ch ) $=
      ( wa simpr sylan2 ) DBFABCDBGEH $.

    $( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       4-May-1994.)  (Proof shortened by Wolf Lammen, 24-Nov-2012.) $)
    adantrr $p |- ( ( ph /\ ( ps /\ th ) ) -> ch ) $=
      ( wa simpl sylan2 ) BDFABCBDGEH $.
  $}

  ${
    adantl2.1 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
    $( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       26-Dec-2004.)  (Proof shortened by Wolf Lammen, 2-Dec-2012.) $)
    adantlll $p |- ( ( ( ( ta /\ ph ) /\ ps ) /\ ch ) -> th ) $=
      ( wa simpr sylanl1 ) EAGABCDEAHFI $.

    $( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       26-Dec-2004.)  (Proof shortened by Wolf Lammen, 4-Dec-2012.) $)
    adantllr $p |- ( ( ( ( ph /\ ta ) /\ ps ) /\ ch ) -> th ) $=
      ( wa simpl sylanl1 ) AEGABCDAEHFI $.

    $( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       26-Dec-2004.)  (Proof shortened by Wolf Lammen, 4-Dec-2012.) $)
    adantlrl $p |- ( ( ( ph /\ ( ta /\ ps ) ) /\ ch ) -> th ) $=
      ( wa simpr sylanl2 ) EBGABCDEBHFI $.

    $( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       26-Dec-2004.)  (Proof shortened by Wolf Lammen, 4-Dec-2012.) $)
    adantlrr $p |- ( ( ( ph /\ ( ps /\ ta ) ) /\ ch ) -> th ) $=
      ( wa simpl sylanl2 ) BEGABCDBEHFI $.
  $}

  ${
    adantr2.1 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
    $( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       26-Dec-2004.)  (Proof shortened by Wolf Lammen, 4-Dec-2012.) $)
    adantrll $p |- ( ( ph /\ ( ( ta /\ ps ) /\ ch ) ) -> th ) $=
      ( wa simpr sylanr1 ) EBGABCDEBHFI $.

    $( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       26-Dec-2004.)  (Proof shortened by Wolf Lammen, 4-Dec-2012.) $)
    adantrlr $p |- ( ( ph /\ ( ( ps /\ ta ) /\ ch ) ) -> th ) $=
      ( wa simpl sylanr1 ) BEGABCDBEHFI $.

    $( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       26-Dec-2004.)  (Proof shortened by Wolf Lammen, 4-Dec-2012.) $)
    adantrrl $p |- ( ( ph /\ ( ps /\ ( ta /\ ch ) ) ) -> th ) $=
      ( wa simpr sylanr2 ) ECGABCDECHFI $.

    $( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       26-Dec-2004.)  (Proof shortened by Wolf Lammen, 4-Dec-2012.) $)
    adantrrr $p |- ( ( ph /\ ( ps /\ ( ch /\ ta ) ) ) -> th ) $=
      ( wa simpl sylanr2 ) CEGABCDCEHFI $.
  $}

  ${
    ad2ant.1 $e |- ( ph -> ps ) $.
    $( Deduction adding two conjuncts to antecedent.  (Contributed by NM,
       19-Oct-1999.)  (Proof shortened by Wolf Lammen, 20-Nov-2012.) $)
    ad2antrr $p |- ( ( ( ph /\ ch ) /\ th ) -> ps ) $=
      ( adantr adantlr ) ADBCABDEFG $.

    $( Deduction adding two conjuncts to antecedent.  (Contributed by NM,
       19-Oct-1999.)  (Proof shortened by Wolf Lammen, 20-Nov-2012.) $)
    ad2antlr $p |- ( ( ( ch /\ ph ) /\ th ) -> ps ) $=
      ( adantr adantll ) ADBCABDEFG $.

    $( Deduction adding two conjuncts to antecedent.  (Contributed by NM,
       19-Oct-1999.) $)
    ad2antrl $p |- ( ( ch /\ ( ph /\ th ) ) -> ps ) $=
      ( wa adantr adantl ) ADFBCABDEGH $.

    $( Deduction adding conjuncts to antecedent.  (Contributed by NM,
       19-Oct-1999.) $)
    ad2antll $p |- ( ( ch /\ ( th /\ ph ) ) -> ps ) $=
      ( wa adantl ) DAFBCABDEGG $.

    $( Deduction adding three conjuncts to antecedent.  (Contributed by NM,
       28-Jul-2012.) $)
    ad3antrrr $p |- ( ( ( ( ph /\ ch ) /\ th ) /\ ta ) -> ps ) $=
      ( wa adantr ad2antrr ) ACGBDEABCFHI $.

    $( Deduction adding three conjuncts to antecedent.  (Contributed by Mario
       Carneiro, 5-Jan-2017.) $)
    ad3antlr $p |- ( ( ( ( ch /\ ph ) /\ th ) /\ ta ) -> ps ) $=
      ( wa ad2antlr adantr ) CAGDGBEABCDFHI $.

    $( Deduction adding 4 conjuncts to antecedent.  (Contributed by Mario
       Carneiro, 4-Jan-2017.) $)
    ad4antr $p |- ( ( ( ( ( ph /\ ch ) /\ th ) /\ ta ) /\ et ) -> ps ) $=
      ( wa ad3antrrr adantr ) ACHDHEHBFABCDEGIJ $.

    $( Deduction adding 4 conjuncts to antecedent.  (Contributed by Mario
       Carneiro, 5-Jan-2017.) $)
    ad4antlr $p |- ( ( ( ( ( ch /\ ph ) /\ th ) /\ ta ) /\ et ) -> ps ) $=
      ( wa ad3antlr adantr ) CAHDHEHBFABCDEGIJ $.

    $( Deduction adding 5 conjuncts to antecedent.  (Contributed by Mario
       Carneiro, 4-Jan-2017.) $)
    ad5antr $p |- ( ( ( ( ( ( ph /\ ch ) /\ th ) /\ ta ) /\ et )
      /\ ze ) -> ps ) $=
      ( wa ad4antr adantr ) ACIDIEIFIBGABCDEFHJK $.

    $( Deduction adding 5 conjuncts to antecedent.  (Contributed by Mario
       Carneiro, 5-Jan-2017.) $)
    ad5antlr $p |- ( ( ( ( ( ( ch /\ ph ) /\ th ) /\ ta ) /\ et )
      /\ ze ) -> ps ) $=
      ( wa ad4antlr adantr ) CAIDIEIFIBGABCDEFHJK $.

    $( Deduction adding 6 conjuncts to antecedent.  (Contributed by Mario
       Carneiro, 4-Jan-2017.) $)
    ad6antr $p |- ( ( ( ( ( ( ( ph /\ ch ) /\ th ) /\ ta ) /\ et )
      /\ ze ) /\ si ) -> ps ) $=
      ( wa ad5antr adantr ) ACJDJEJFJGJBHABCDEFGIKL $.

    $( Deduction adding 6 conjuncts to antecedent.  (Contributed by Mario
       Carneiro, 5-Jan-2017.) $)
    ad6antlr $p |- ( ( ( ( ( ( ( ch /\ ph ) /\ th ) /\ ta ) /\ et )
      /\ ze ) /\ si ) -> ps ) $=
      ( wa ad5antlr adantr ) CAJDJEJFJGJBHABCDEFGIKL $.

    $( Deduction adding 7 conjuncts to antecedent.  (Contributed by Mario
       Carneiro, 4-Jan-2017.) $)
    ad7antr $p |- ( ( ( ( ( ( ( ( ph /\ ch ) /\ th ) /\ ta ) /\ et )
      /\ ze ) /\ si ) /\ rh ) -> ps ) $=
      ( wa ad6antr adantr ) ACKDKEKFKGKHKBIABCDEFGHJLM $.

    $( Deduction adding 7 conjuncts to antecedent.  (Contributed by Mario
       Carneiro, 5-Jan-2017.) $)
    ad7antlr $p |- ( ( ( ( ( ( ( ( ch /\ ph ) /\ th ) /\ ta ) /\ et )
      /\ ze ) /\ si ) /\ rh ) -> ps ) $=
      ( wa ad6antlr adantr ) CAKDKEKFKGKHKBIABCDEFGHJLM $.

    $( Deduction adding 8 conjuncts to antecedent.  (Contributed by Mario
       Carneiro, 4-Jan-2017.) $)
    ad8antr $p |- ( ( ( ( ( ( ( ( ( ph /\ ch ) /\ th ) /\ ta ) /\ et )
      /\ ze ) /\ si ) /\ rh ) /\ mu ) -> ps ) $=
      ( wa ad7antr adantr ) ACLDLELFLGLHLILBJABCDEFGHIKMN $.

    $( Deduction adding 8 conjuncts to antecedent.  (Contributed by Mario
       Carneiro, 5-Jan-2017.) $)
    ad8antlr $p |- ( ( ( ( ( ( ( ( ( ch /\ ph ) /\ th ) /\ ta ) /\ et )
      /\ ze ) /\ si ) /\ rh ) /\ mu ) -> ps ) $=
      ( wa ad7antlr adantr ) CALDLELFLGLHLILBJABCDEFGHIKMN $.

    $( Deduction adding 9 conjuncts to antecedent.  (Contributed by Mario
       Carneiro, 4-Jan-2017.) $)
    ad9antr $p |- ( ( ( ( ( ( ( ( ( ( ph /\ ch ) /\ th ) /\ ta ) /\ et )
      /\ ze ) /\ si ) /\ rh ) /\ mu ) /\ la ) -> ps ) $=
      ( wa ad8antr adantr ) ACMDMEMFMGMHMIMJMBKABCDEFGHIJLNO $.

    $( Deduction adding 9 conjuncts to antecedent.  (Contributed by Mario
       Carneiro, 5-Jan-2017.) $)
    ad9antlr $p |- ( ( ( ( ( ( ( ( ( ( ch /\ ph ) /\ th ) /\ ta ) /\ et )
      /\ ze ) /\ si ) /\ rh ) /\ mu ) /\ la ) -> ps ) $=
      ( wa ad8antlr adantr ) CAMDMEMFMGMHMIMJMBKABCDEFGHIJLNO $.

    $( Deduction adding 10 conjuncts to antecedent.  (Contributed by Mario
       Carneiro, 4-Jan-2017.) $)
    ad10antr $p |- ( ( ( ( ( ( ( ( ( ( ( ph /\ ch ) /\ th ) /\ ta ) /\ et )
      /\ ze ) /\ si ) /\ rh ) /\ mu ) /\ la ) /\ ka ) -> ps ) $=
      ( wa ad9antr adantr ) ACNDNENFNGNHNINJNKNBLABCDEFGHIJKMOP $.

    $( Deduction adding 10 conjuncts to antecedent.  (Contributed by Mario
       Carneiro, 5-Jan-2017.) $)
    ad10antlr $p |- ( ( ( ( ( ( ( ( ( ( ( ch /\ ph ) /\ th ) /\ ta ) /\ et )
      /\ ze ) /\ si ) /\ rh ) /\ mu ) /\ la ) /\ ka ) -> ps ) $=
      ( wa ad9antlr adantr ) CANDNENFNGNHNINJNKNBLABCDEFGHIJKMOP $.
  $}

  ${
    ad2ant2.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( Deduction adding two conjuncts to antecedent.  (Contributed by NM,
       8-Jan-2006.) $)
    ad2ant2l $p |- ( ( ( th /\ ph ) /\ ( ta /\ ps ) ) -> ch ) $=
      ( wa adantrl adantll ) AEBGCDABCEFHI $.

    $( Deduction adding two conjuncts to antecedent.  (Contributed by NM,
       8-Jan-2006.) $)
    ad2ant2r $p |- ( ( ( ph /\ th ) /\ ( ps /\ ta ) ) -> ch ) $=
      ( wa adantrr adantlr ) ABEGCDABCEFHI $.

    $( Deduction adding two conjuncts to antecedent.  (Contributed by NM,
       23-Nov-2007.) $)
    ad2ant2lr $p |- ( ( ( th /\ ph ) /\ ( ps /\ ta ) ) -> ch ) $=
      ( wa adantrr adantll ) ABEGCDABCEFHI $.

    $( Deduction adding two conjuncts to antecedent.  (Contributed by NM,
       24-Nov-2007.) $)
    ad2ant2rl $p |- ( ( ( ph /\ th ) /\ ( ta /\ ps ) ) -> ch ) $=
      ( wa adantrl adantlr ) AEBGCDABCEFHI $.
  $}

  ${
    adantl3r.1 $e |- ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) -> ta ) $.
    $( Deduction adding 1 conjunct to antecedent.  (Contributed by Alan Sare,
       17-Oct-2017.) $)
    adantl3r $p |- ( ( ( ( ( ph /\ et ) /\ ps ) /\ ch ) /\ th ) -> ta ) $=
      ( wa id adantlr sylanl1 ) AFHBHABHZCDEABLFLIJGK $.
  $}

  ${
    ad4ant2.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( Deduction adding conjuncts to antecedent.  (Contributed by Alan Sare,
       17-Oct-2017.)  (Proof shortened by Wolf Lammen, 14-Apr-2022.) $)
    ad4ant13 $p |- ( ( ( ( ph /\ th ) /\ ps ) /\ ta ) -> ch ) $=
      ( wa adantr adantllr ) ABECDABGCEFHI $.

    $( Deduction adding conjuncts to antecedent.  (Contributed by Alan Sare,
       17-Oct-2017.)  (Proof shortened by Wolf Lammen, 14-Apr-2022.) $)
    ad4ant14 $p |- ( ( ( ( ph /\ th ) /\ ta ) /\ ps ) -> ch ) $=
      ( wa adantlr ) ADGBCEABCDFHH $.

    $( Deduction adding conjuncts to antecedent.  (Contributed by Alan Sare,
       17-Oct-2017.)  (Proof shortened by Wolf Lammen, 14-Apr-2022.) $)
    ad4ant23 $p |- ( ( ( ( th /\ ph ) /\ ps ) /\ ta ) -> ch ) $=
      ( wa adantr adantlll ) ABECDABGCEFHI $.

    $( Deduction adding conjuncts to antecedent.  (Contributed by Alan Sare,
       17-Oct-2017.)  (Proof shortened by Wolf Lammen, 14-Apr-2022.) $)
    ad4ant24 $p |- ( ( ( ( th /\ ph ) /\ ta ) /\ ps ) -> ch ) $=
      ( adantlr adantlll ) AEBCDABCEFGH $.
  $}

  ${
    adantl4r.1 $e |- ( ( ( ( ( ph /\ si ) /\ rh ) /\ mu ) /\ la ) -> ka ) $.
    $( Deduction adding 1 conjunct to antecedent.  (Contributed by Thierry
       Arnoux, 11-Feb-2018.) $)
    adantl4r $p |- ( ( ( ( ( ( ph /\ ze ) /\ si ) /\ rh ) /\ mu ) /\ la )
      -> ka ) $=
      ( wa wi ex adantl3r imp ) ABICIDIEIFGACDEFGJBACIDIEIFGHKLM $.
  $}

  ${
    ad5ant2.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( Deduction adding conjuncts to antecedent.  (Contributed by Alan Sare,
       17-Oct-2017.) $)
    ad5ant12 $p |- ( ( ( ( ( ph /\ ps ) /\ th ) /\ ta ) /\ et ) -> ch ) $=
      ( wa ad3antrrr ) ABHCDEFGI $.

    $( Deduction adding conjuncts to antecedent.  (Contributed by Alan Sare,
       17-Oct-2017.)  (Proof shortened by Wolf Lammen, 14-Apr-2022.) $)
    ad5ant13 $p |- ( ( ( ( ( ph /\ th ) /\ ps ) /\ ta ) /\ et ) -> ch ) $=
      ( wa adantlr ad2antrr ) ADHBHCEFABCDGIJ $.

    $( Deduction adding conjuncts to antecedent.  (Contributed by Alan Sare,
       17-Oct-2017.)  (Proof shortened by Wolf Lammen, 14-Apr-2022.) $)
    ad5ant14 $p |- ( ( ( ( ( ph /\ th ) /\ ta ) /\ ps ) /\ et ) -> ch ) $=
      ( wa adantlr ad4ant13 ) ADHBCEFABCDGIJ $.

    $( Deduction adding conjuncts to antecedent.  (Contributed by Alan Sare,
       17-Oct-2017.)  (Proof shortened by Wolf Lammen, 14-Apr-2022.) $)
    ad5ant15 $p |- ( ( ( ( ( ph /\ th ) /\ ta ) /\ et ) /\ ps ) -> ch ) $=
      ( wa adantlr ad4ant14 ) ADHBCEFABCDGIJ $.

    $( Deduction adding conjuncts to antecedent.  (Contributed by Alan Sare,
       17-Oct-2017.)  (Proof shortened by Wolf Lammen, 14-Apr-2022.) $)
    ad5ant23 $p |- ( ( ( ( ( th /\ ph ) /\ ps ) /\ ta ) /\ et ) -> ch ) $=
      ( wa adantll ad2antrr ) DAHBHCEFABCDGIJ $.

    $( Deduction adding conjuncts to antecedent.  (Contributed by Alan Sare,
       17-Oct-2017.)  (Proof shortened by Wolf Lammen, 14-Apr-2022.) $)
    ad5ant24 $p |- ( ( ( ( ( th /\ ph ) /\ ta ) /\ ps ) /\ et ) -> ch ) $=
      ( wa adantll ad4ant13 ) DAHBCEFABCDGIJ $.

    $( Deduction adding conjuncts to antecedent.  (Contributed by Alan Sare,
       17-Oct-2017.)  (Proof shortened by Wolf Lammen, 14-Apr-2022.) $)
    ad5ant25 $p |- ( ( ( ( ( th /\ ph ) /\ ta ) /\ et ) /\ ps ) -> ch ) $=
      ( wa adantll ad4ant14 ) DAHBCEFABCDGIJ $.
  $}

  ${
    adantl5r.1 $e |- ( ( ( ( ( ( ph /\ ze ) /\ si ) /\ rh ) /\ mu ) /\ la )
      -> ka ) $.
    $( Deduction adding 1 conjunct to antecedent.  (Contributed by Thierry
       Arnoux, 11-Feb-2018.) $)
    adantl5r $p |- ( ( ( ( ( ( ( ph /\ et ) /\ ze ) /\ si ) /\ rh ) /\ mu )
      /\ la ) -> ka ) $=
      ( wa wi ex adantl4r imp ) ABJCJDJEJFJGHABCDEFGHKACJDJEJFJGHILMN $.
  $}

  ${
    adantl6r.1 $e |- ( ( ( ( ( ( ( ph /\ et ) /\ ze ) /\ si ) /\ rh ) /\ mu )
      /\ la ) -> ka ) $.
    $( Deduction adding 1 conjunct to antecedent.  (Contributed by Thierry
       Arnoux, 11-Feb-2018.) $)
    adantl6r $p |- ( ( ( ( ( ( ( ( ph /\ ta ) /\ et ) /\ ze ) /\ si ) /\ rh )
      /\ mu ) /\ la ) -> ka ) $=
      ( wa wi ex adantl5r imp ) ABKCKDKEKFKGKHIABCDEFGHILACKDKEKFKGKHIJMNO $.
  $}

  $( Simplification of a conjunction.  (Contributed by NM, 18-Mar-2007.) $)
  simpll $p |- ( ( ( ph /\ ps ) /\ ch ) -> ph ) $=
    ( id ad2antrr ) AABCADE $.

  ${
    simplld.1 $e |- ( ph -> ( ( ps /\ ch ) /\ th ) ) $.
    $( Deduction form of ~ simpll , eliminating a double conjunct.
       (Contributed by Glauco Siliprandi, 11-Dec-2019.) $)
    simplld $p |- ( ph -> ps ) $=
      ( wa simpld ) ABCABCFDEGG $.
  $}

  $( Simplification of a conjunction.  (Contributed by NM, 20-Mar-2007.) $)
  simplr $p |- ( ( ( ph /\ ps ) /\ ch ) -> ps ) $=
    ( id ad2antlr ) BBACBDE $.

  ${
    simplrd.1 $e |- ( ph -> ( ( ps /\ ch ) /\ th ) ) $.
    $( Deduction eliminating a double conjunct.  (Contributed by Glauco
       Siliprandi, 11-Dec-2019.) $)
    simplrd $p |- ( ph -> ch ) $=
      ( wa simpld simprd ) ABCABCFDEGH $.
  $}

  $( Simplification of a conjunction.  (Contributed by NM, 21-Mar-2007.) $)
  simprl $p |- ( ( ph /\ ( ps /\ ch ) ) -> ps ) $=
    ( id ad2antrl ) BBACBDE $.

  ${
    simprld.1 $e |- ( ph -> ( ps /\ ( ch /\ th ) ) ) $.
    $( Deduction eliminating a double conjunct.  (Contributed by Glauco
       Siliprandi, 11-Dec-2019.) $)
    simprld $p |- ( ph -> ch ) $=
      ( wa simprd simpld ) ACDABCDFEGH $.
  $}

  $( Simplification of a conjunction.  (Contributed by NM, 21-Mar-2007.) $)
  simprr $p |- ( ( ph /\ ( ps /\ ch ) ) -> ch ) $=
    ( id ad2antll ) CCABCDE $.

  ${
    simprrd.1 $e |- ( ph -> ( ps /\ ( ch /\ th ) ) ) $.
    $( Deduction form of ~ simprr , eliminating a double conjunct.
       (Contributed by Glauco Siliprandi, 11-Dec-2019.) $)
    simprrd $p |- ( ph -> th ) $=
      ( wa simprd ) ACDABCDFEGG $.
  $}

  $( Simplification of a conjunction.  (Contributed by Jeff Hankins,
     28-Jul-2009.) $)
  simplll $p |- ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) -> ph ) $=
    ( wa simpl ad2antrr ) ABEACDABFG $.

  $( Simplification of a conjunction.  (Contributed by Jeff Hankins,
     28-Jul-2009.) $)
  simpllr $p |- ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) -> ps ) $=
    ( wa simpr ad2antrr ) ABEBCDABFG $.

  $( Simplification of a conjunction.  (Contributed by Jeff Hankins,
     28-Jul-2009.) $)
  simplrl $p |- ( ( ( ph /\ ( ps /\ ch ) ) /\ th ) -> ps ) $=
    ( wa simpl ad2antlr ) BCEBADBCFG $.

  $( Simplification of a conjunction.  (Contributed by Jeff Hankins,
     28-Jul-2009.) $)
  simplrr $p |- ( ( ( ph /\ ( ps /\ ch ) ) /\ th ) -> ch ) $=
    ( wa simpr ad2antlr ) BCECADBCFG $.

  $( Simplification of a conjunction.  (Contributed by Jeff Hankins,
     28-Jul-2009.) $)
  simprll $p |- ( ( ph /\ ( ( ps /\ ch ) /\ th ) ) -> ps ) $=
    ( wa simpl ad2antrl ) BCEBADBCFG $.

  $( Simplification of a conjunction.  (Contributed by Jeff Hankins,
     28-Jul-2009.) $)
  simprlr $p |- ( ( ph /\ ( ( ps /\ ch ) /\ th ) ) -> ch ) $=
    ( wa simpr ad2antrl ) BCECADBCFG $.

  $( Simplification of a conjunction.  (Contributed by Jeff Hankins,
     28-Jul-2009.) $)
  simprrl $p |- ( ( ph /\ ( ps /\ ( ch /\ th ) ) ) -> ch ) $=
    ( wa simpl ad2antll ) CDECABCDFG $.

  $( Simplification of a conjunction.  (Contributed by Jeff Hankins,
     28-Jul-2009.) $)
  simprrr $p |- ( ( ph /\ ( ps /\ ( ch /\ th ) ) ) -> th ) $=
    ( wa simpr ad2antll ) CDEDABCDFG $.

  $( Simplification of a conjunction.  (Contributed by Mario Carneiro,
     4-Jan-2017.) $)
  simp-4l $p |- ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta ) -> ph ) $=
    ( wa simplll adantr ) ABFCFDFAEABCDGH $.

  $( Simplification of a conjunction.  (Contributed by Mario Carneiro,
     4-Jan-2017.) $)
  simp-4r $p |- ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta ) -> ps ) $=
    ( wa simpllr adantr ) ABFCFDFBEABCDGH $.

  $( Simplification of a conjunction.  (Contributed by Mario Carneiro,
     4-Jan-2017.) $)
  simp-5l $p |- ( ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta )
    /\ et ) -> ph ) $=
    ( wa simp-4l adantr ) ABGCGDGEGAFABCDEHI $.

  $( Simplification of a conjunction.  (Contributed by Mario Carneiro,
     4-Jan-2017.) $)
  simp-5r $p |- ( ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta )
    /\ et ) -> ps ) $=
    ( wa simp-4r adantr ) ABGCGDGEGBFABCDEHI $.

  $( Simplification of a conjunction.  (Contributed by Mario Carneiro,
     4-Jan-2017.) $)
  simp-6l $p |- ( ( ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta )
    /\ et ) /\ ze ) -> ph ) $=
    ( wa simp-5l adantr ) ABHCHDHEHFHAGABCDEFIJ $.

  $( Simplification of a conjunction.  (Contributed by Mario Carneiro,
     4-Jan-2017.) $)
  simp-6r $p |- ( ( ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta )
    /\ et ) /\ ze ) -> ps ) $=
    ( wa simp-5r adantr ) ABHCHDHEHFHBGABCDEFIJ $.

  $( Simplification of a conjunction.  (Contributed by Mario Carneiro,
     4-Jan-2017.) $)
  simp-7l $p |- ( ( ( ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta )
    /\ et ) /\ ze ) /\ si ) -> ph ) $=
    ( wa simp-6l adantr ) ABICIDIEIFIGIAHABCDEFGJK $.

  $( Simplification of a conjunction.  (Contributed by Mario Carneiro,
     4-Jan-2017.) $)
  simp-7r $p |- ( ( ( ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta )
    /\ et ) /\ ze ) /\ si ) -> ps ) $=
    ( wa simp-6r adantr ) ABICIDIEIFIGIBHABCDEFGJK $.

  $( Simplification of a conjunction.  (Contributed by Mario Carneiro,
     4-Jan-2017.) $)
  simp-8l $p |- ( ( ( ( ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta )
    /\ et ) /\ ze ) /\ si ) /\ rh ) -> ph ) $=
    ( wa simp-7l adantr ) ABJCJDJEJFJGJHJAIABCDEFGHKL $.

  $( Simplification of a conjunction.  (Contributed by Mario Carneiro,
     4-Jan-2017.) $)
  simp-8r $p |- ( ( ( ( ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta )
    /\ et ) /\ ze ) /\ si ) /\ rh ) -> ps ) $=
    ( wa simp-7r adantr ) ABJCJDJEJFJGJHJBIABCDEFGHKL $.

  $( Simplification of a conjunction.  (Contributed by Mario Carneiro,
     4-Jan-2017.) $)
  simp-9l $p |- ( ( ( ( ( ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta )
    /\ et ) /\ ze ) /\ si ) /\ rh ) /\ mu ) -> ph ) $=
    ( wa simp-8l adantr ) ABKCKDKEKFKGKHKIKAJABCDEFGHILM $.

  $( Simplification of a conjunction.  (Contributed by Mario Carneiro,
     4-Jan-2017.) $)
  simp-9r $p |- ( ( ( ( ( ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta )
    /\ et ) /\ ze ) /\ si ) /\ rh ) /\ mu ) -> ps ) $=
    ( wa simp-8r adantr ) ABKCKDKEKFKGKHKIKBJABCDEFGHILM $.

  $( Simplification of a conjunction.  (Contributed by Mario Carneiro,
     4-Jan-2017.) $)
  simp-10l $p |- ( ( ( ( ( ( ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta )
    /\ et ) /\ ze ) /\ si ) /\ rh ) /\ mu ) /\ la ) -> ph ) $=
    ( wa simp-9l adantr ) ABLCLDLELFLGLHLILJLAKABCDEFGHIJMN $.

  $( Simplification of a conjunction.  (Contributed by Mario Carneiro,
     4-Jan-2017.) $)
  simp-10r $p |- ( ( ( ( ( ( ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta )
    /\ et ) /\ ze ) /\ si ) /\ rh ) /\ mu ) /\ la ) -> ps ) $=
    ( wa simp-9r adantr ) ABLCLDLELFLGLHLILJLBKABCDEFGHIJMN $.

  $( Simplification of a conjunction.  (Contributed by Mario Carneiro,
     4-Jan-2017.) $)
  simp-11l $p |- ( ( ( ( ( ( ( ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta )
    /\ et ) /\ ze ) /\ si ) /\ rh ) /\ mu ) /\ la ) /\ ka ) -> ph ) $=
    ( wa simp-10l adantr ) ABMCMDMEMFMGMHMIMJMKMALABCDEFGHIJKNO $.

  $( Simplification of a conjunction.  (Contributed by Mario Carneiro,
     4-Jan-2017.) $)
  simp-11r $p |- ( ( ( ( ( ( ( ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta )
    /\ et ) /\ ze ) /\ si ) /\ rh ) /\ mu ) /\ la ) /\ ka ) -> ps ) $=
    ( wa simp-10r adantr ) ABMCMDMEMFMGMHMIMJMKMBLABCDEFGHIJKNO $.

  $( Theorem *4.87 of [WhiteheadRussell] p. 122.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Eric Schmidt, 26-Oct-2006.) $)
  pm4.87 $p |- ( ( ( ( ( ph /\ ps ) -> ch ) <-> ( ph -> ( ps -> ch ) ) ) /\
                ( ( ph -> ( ps -> ch ) ) <-> ( ps -> ( ph -> ch ) ) ) ) /\
                ( ( ps -> ( ph -> ch ) ) <-> ( ( ps /\ ph ) -> ch ) ) ) $=
    ( wa wi wb impexp bi2.04 pm3.2i bicomi ) ABDCEABCEEZFZKBACEEZFZDMBADCEZFLNA
    BCGABCHIOMBACGJI $.

  ${
    a2and.1 $e |- ( ph -> ( ( ps /\ rh ) -> ( ta -> th ) ) ) $.
    a2and.2 $e |- ( ph -> ( ( ps /\ rh ) -> ch ) ) $.
    $( Deduction distributing a conjunction as embedded antecedent.
       (Contributed by AV, 25-Oct-2019.)  (Proof shortened by Wolf Lammen,
       19-Jan-2020.) $)
    a2and $p |- ( ph -> ( ( ( ps /\ ch ) -> ta )
                            -> ( ( ps /\ rh ) -> th ) ) ) $=
      ( wa wi expd imdistand imp embantd ex com23 ) ABFIZBCIZEJZDAQSDJAQIREDAQR
      ABFCABFCHKLMAQEDJGMNOP $.
  $}

  ${
    animpimp2impd.1 $e |- ( ( ps /\ ph ) -> ( ch -> ( th -> et ) ) ) $.
    animpimp2impd.2 $e |- ( ( ps /\ ( ph /\ th ) ) -> ( et -> ta ) ) $.
    $( Deduction deriving nested implications from conjunctions.  (Contributed
       by AV, 21-Aug-2022.) $)
    animpimp2impd $p |- ( ph -> ( ( ps -> ch ) -> ( ps -> ( th -> ta ) ) ) ) $=
      ( wi wa expr a2d syld expcom ) ABCDEIZBACOIBAJZCDFIOGPDFEBADFEIHKLMNL $.
  $}

  $( Introduce one conjunct as an antecedent to the other.  "abai" stands for
     "and, biconditional, and, implication".  (Contributed by NM, 12-Aug-1993.)
     (Proof shortened by Wolf Lammen, 7-Dec-2012.) $)
  abai $p |- ( ( ph /\ ps ) <-> ( ph /\ ( ph -> ps ) ) ) $=
    ( wi biimt pm5.32i ) ABABCABDE $.

  $( Swap two conjuncts.  Note that the first digit (1) in the label refers to
     the outer conjunct position, and the next digit (2) to the inner conjunct
     position.  (Contributed by NM, 12-Mar-1995.) $)
  an12 $p |- ( ( ph /\ ( ps /\ ch ) ) <-> ( ps /\ ( ph /\ ch ) ) ) $=
    ( wa ancom anbi1i anass 3bitr3i ) ABDZCDBADZCDABCDDBACDDIJCABEFABCGBACGH $.

  $( A rearrangement of conjuncts.  (Contributed by NM, 12-Mar-1995.)  (Proof
     shortened by Wolf Lammen, 25-Dec-2012.) $)
  an32 $p |- ( ( ( ph /\ ps ) /\ ch ) <-> ( ( ph /\ ch ) /\ ps ) ) $=
    ( wa anass an12 ancom 3bitri ) ABDCDABCDDBACDZDIBDABCEABCFBIGH $.

  $( A rearrangement of conjuncts.  (Contributed by NM, 24-Jun-2012.)  (Proof
     shortened by Wolf Lammen, 31-Dec-2012.) $)
  an13 $p |- ( ( ph /\ ( ps /\ ch ) ) <-> ( ch /\ ( ps /\ ph ) ) ) $=
    ( wa an12 anass ancom 3bitr2i ) ABCDDBACDDBADZCDCIDABCEBACFICGH $.

  $( A rearrangement of conjuncts.  (Contributed by NM, 24-Jun-2012.)  (Proof
     shortened by Wolf Lammen, 31-Dec-2012.) $)
  an31 $p |- ( ( ( ph /\ ps ) /\ ch ) <-> ( ( ch /\ ps ) /\ ph ) ) $=
    ( wa an13 anass 3bitr4i ) ABCDDCBADDABDCDCBDADABCEABCFCBAFG $.

  ${
    an12s.1 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
    $( Swap two conjuncts in antecedent.  The label suffix "s" means that
       ~ an12 is combined with ~ syl (or a variant).  (Contributed by NM,
       13-Mar-1996.) $)
    an12s $p |- ( ( ps /\ ( ph /\ ch ) ) -> th ) $=
      ( wa an12 sylbi ) BACFFABCFFDBACGEH $.

    $( Inference commuting a nested conjunction in antecedent.  (Contributed by
       NM, 24-May-2006.)  (Proof shortened by Wolf Lammen, 24-Nov-2012.) $)
    ancom2s $p |- ( ( ph /\ ( ch /\ ps ) ) -> th ) $=
      ( wa pm3.22 sylan2 ) CBFABCFDCBGEH $.

    $( Swap two conjuncts in antecedent.  (Contributed by NM, 31-May-2006.) $)
    an13s $p |- ( ( ch /\ ( ps /\ ph ) ) -> th ) $=
      ( exp32 com13 imp32 ) CBADABCDABCDEFGH $.
  $}

  ${
    an32s.1 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
    $( Swap two conjuncts in antecedent.  (Contributed by NM, 13-Mar-1996.) $)
    an32s $p |- ( ( ( ph /\ ch ) /\ ps ) -> th ) $=
      ( wa an32 sylbi ) ACFBFABFCFDACBGEH $.

    $( Inference commuting a nested conjunction in antecedent.  (Contributed by
       NM, 24-May-2006.)  (Proof shortened by Wolf Lammen, 24-Nov-2012.) $)
    ancom1s $p |- ( ( ( ps /\ ph ) /\ ch ) -> th ) $=
      ( wa pm3.22 sylan ) BAFABFCDBAGEH $.

    $( Swap two conjuncts in antecedent.  (Contributed by NM, 31-May-2006.) $)
    an31s $p |- ( ( ( ch /\ ps ) /\ ph ) -> th ) $=
      ( exp31 com13 imp31 ) CBADABCDABCDEFGH $.
  $}

  ${
    anass1rs.1 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
    $( Commutative-associative law for conjunction in an antecedent.
       (Contributed by Jeff Madsen, 19-Jun-2011.) $)
    anass1rs $p |- ( ( ( ph /\ ch ) /\ ps ) -> th ) $=
      ( anassrs an32s ) ABCDABCDEFG $.
  $}

  $( Absorption into embedded conjunct.  (Contributed by NM, 4-Sep-1995.)
     (Proof shortened by Wolf Lammen, 16-Nov-2013.) $)
  anabs1 $p |- ( ( ( ph /\ ps ) /\ ph ) <-> ( ph /\ ps ) ) $=
    ( wa simpl pm4.71i bicomi ) ABCZGACGAABDEF $.

  $( Absorption into embedded conjunct.  (Contributed by NM, 20-Jul-1996.)
     (Proof shortened by Wolf Lammen, 9-Dec-2012.) $)
  anabs5 $p |- ( ( ph /\ ( ph /\ ps ) ) <-> ( ph /\ ps ) ) $=
    ( wa ibar bicomd pm5.32i ) AABCZBABGABDEF $.

  $( Absorption into embedded conjunct.  (Contributed by NM, 20-Jul-1996.)
     (Proof shortened by Wolf Lammen, 17-Nov-2013.) $)
  anabs7 $p |- ( ( ps /\ ( ph /\ ps ) ) <-> ( ph /\ ps ) ) $=
    ( wa simpr pm4.71ri bicomi ) ABCZBGCGBABDEF $.

  ${
    anabsan.1 $e |- ( ( ( ph /\ ph ) /\ ps ) -> ch ) $.
    $( Absorption of antecedent with conjunction.  (Contributed by NM,
       24-Mar-1996.)  (Revised by NM, 18-Nov-2013.) $)
    anabsan $p |- ( ( ph /\ ps ) -> ch ) $=
      ( wa pm4.24 sylanb ) AAAEBCAFDG $.
  $}

  ${
    anabss1.1 $e |- ( ( ( ph /\ ps ) /\ ph ) -> ch ) $.
    $( Absorption of antecedent into conjunction.  (Contributed by NM,
       20-Jul-1996.)  (Proof shortened by Wolf Lammen, 31-Dec-2012.) $)
    anabss1 $p |- ( ( ph /\ ps ) -> ch ) $=
      ( an32s anabsan ) ABCABACDEF $.
  $}

  ${
    anabss4.1 $e |- ( ( ( ps /\ ph ) /\ ps ) -> ch ) $.
    $( Absorption of antecedent into conjunction.  (Contributed by NM,
       20-Jul-1996.) $)
    anabss4 $p |- ( ( ph /\ ps ) -> ch ) $=
      ( anabss1 ancoms ) BACBACDEF $.
  $}

  ${
    anabss5.1 $e |- ( ( ph /\ ( ph /\ ps ) ) -> ch ) $.
    $( Absorption of antecedent into conjunction.  (Contributed by NM,
       10-May-1994.)  (Proof shortened by Wolf Lammen, 1-Jan-2013.) $)
    anabss5 $p |- ( ( ph /\ ps ) -> ch ) $=
      ( anassrs anabsan ) ABCAABCDEF $.
  $}

  ${
    anabsi5.1 $e |- ( ph -> ( ( ph /\ ps ) -> ch ) ) $.
    $( Absorption of antecedent into conjunction.  (Contributed by NM,
       11-Jun-1995.)  (Proof shortened by Wolf Lammen, 18-Nov-2013.) $)
    anabsi5 $p |- ( ( ph /\ ps ) -> ch ) $=
      ( wa imp anabss5 ) ABCAABECDFG $.
  $}

  ${
    anabsi6.1 $e |- ( ph -> ( ( ps /\ ph ) -> ch ) ) $.
    $( Absorption of antecedent into conjunction.  (Contributed by NM,
       14-Aug-2000.) $)
    anabsi6 $p |- ( ( ph /\ ps ) -> ch ) $=
      ( ancomsd anabsi5 ) ABCABACDEF $.
  $}

  ${
    anabsi7.1 $e |- ( ps -> ( ( ph /\ ps ) -> ch ) ) $.
    $( Absorption of antecedent into conjunction.  (Contributed by NM,
       20-Jul-1996.)  (Proof shortened by Wolf Lammen, 18-Nov-2013.) $)
    anabsi7 $p |- ( ( ph /\ ps ) -> ch ) $=
      ( anabsi6 ancoms ) BACBACDEF $.
  $}

  ${
    anabsi8.1 $e |- ( ps -> ( ( ps /\ ph ) -> ch ) ) $.
    $( Absorption of antecedent into conjunction.  (Contributed by NM,
       26-Sep-1999.) $)
    anabsi8 $p |- ( ( ph /\ ps ) -> ch ) $=
      ( anabsi5 ancoms ) BACBACDEF $.
  $}

  ${
    anabss7.1 $e |- ( ( ps /\ ( ph /\ ps ) ) -> ch ) $.
    $( Absorption of antecedent into conjunction.  (Contributed by NM,
       20-Jul-1996.)  (Proof shortened by Wolf Lammen, 19-Nov-2013.) $)
    anabss7 $p |- ( ( ph /\ ps ) -> ch ) $=
      ( anassrs anabss4 ) ABCBABCDEF $.
  $}

  ${
    anabsan2.1 $e |- ( ( ph /\ ( ps /\ ps ) ) -> ch ) $.
    $( Absorption of antecedent with conjunction.  (Contributed by NM,
       10-May-2004.)  (Revised by NM, 1-Jan-2013.) $)
    anabsan2 $p |- ( ( ph /\ ps ) -> ch ) $=
      ( an12s anabss7 ) ABCABBCDEF $.
  $}

  ${
    anabss3.1 $e |- ( ( ( ph /\ ps ) /\ ps ) -> ch ) $.
    $( Absorption of antecedent into conjunction.  (Contributed by NM,
       20-Jul-1996.)  (Proof shortened by Wolf Lammen, 1-Jan-2013.) $)
    anabss3 $p |- ( ( ph /\ ps ) -> ch ) $=
      ( anasss anabsan2 ) ABCABBCDEF $.
  $}

  $( Rearrangement of 4 conjuncts.  (Contributed by NM, 10-Jul-1994.) $)
  an4 $p |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) <->
              ( ( ph /\ ch ) /\ ( ps /\ th ) ) ) $=
    ( wa an12 anbi2i anass 3bitr4i ) ABCDEZEZEACBDEZEZEABEJEACELEKMABCDFGABJHAC
    LHI $.

  $( Rearrangement of 4 conjuncts.  (Contributed by NM, 7-Feb-1996.) $)
  an42 $p |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) <->
                 ( ( ph /\ ch ) /\ ( th /\ ps ) ) ) $=
    ( wa an4 ancom anbi2i bitri ) ABECDEEACEZBDEZEJDBEZEABCDFKLJBDGHI $.

  $( Rearrangement of 4 conjuncts.  (Contributed by Rodolfo Medina,
     24-Sep-2010.)  (Proof shortened by Andrew Salmon, 29-Jun-2011.) $)
  an43 $p |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) <->
               ( ( ph /\ th ) /\ ( ps /\ ch ) ) ) $=
    ( wa an42 bicomi ) ADEBCEEABECDEEADBCFG $.

  $( A rearrangement of conjuncts.  (Contributed by Rodolfo Medina,
     25-Sep-2010.) $)
  an3 $p |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) -> ( ph /\ th ) ) $=
    ( wa an43 simplbi ) ABECDEEADEBCEABCDFG $.

  ${
    an4s.1 $e |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) -> ta ) $.
    $( Inference rearranging 4 conjuncts in antecedent.  (Contributed by NM,
       10-Aug-1995.) $)
    an4s $p |- ( ( ( ph /\ ch ) /\ ( ps /\ th ) ) -> ta ) $=
      ( wa an4 sylbi ) ACGBDGGABGCDGGEACBDHFI $.
  $}

  ${
    an41r3s.1 $e |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) -> ta ) $.
    $( Inference rearranging 4 conjuncts in antecedent.  (Contributed by NM,
       10-Aug-1995.) $)
    an42s $p |- ( ( ( ph /\ ch ) /\ ( th /\ ps ) ) -> ta ) $=
      ( wa an4s ancom2s ) ACGBDEABCDEFHI $.
  $}

  $( Distribution of conjunction over conjunction.  (Contributed by NM,
     14-Aug-1995.) $)
  anandi $p |- ( ( ph /\ ( ps /\ ch ) ) <->
               ( ( ph /\ ps ) /\ ( ph /\ ch ) ) ) $=
    ( wa anidm anbi1i an4 bitr3i ) ABCDZDAADZIDABDACDDJAIAEFAABCGH $.

  $( Distribution of conjunction over conjunction.  (Contributed by NM,
     24-Aug-1995.) $)
  anandir $p |- ( ( ( ph /\ ps ) /\ ch ) <->
               ( ( ph /\ ch ) /\ ( ps /\ ch ) ) ) $=
    ( wa anidm anbi2i an4 bitr3i ) ABDZCDICCDZDACDBCDDJCICEFABCCGH $.

  ${
    anandis.1 $e |- ( ( ( ph /\ ps ) /\ ( ph /\ ch ) ) -> ta ) $.
    $( Inference that undistributes conjunction in the antecedent.
       (Contributed by NM, 7-Jun-2004.) $)
    anandis $p |- ( ( ph /\ ( ps /\ ch ) ) -> ta ) $=
      ( wa an4s anabsan ) ABCFDABACDEGH $.
  $}

  ${
    anandirs.1 $e |- ( ( ( ph /\ ch ) /\ ( ps /\ ch ) ) -> ta ) $.
    $( Inference that undistributes conjunction in the antecedent.
       (Contributed by NM, 7-Jun-2004.) $)
    anandirs $p |- ( ( ( ph /\ ps ) /\ ch ) -> ta ) $=
      ( wa an4s anabsan2 ) ABFCDACBCDEGH $.
  $}

  ${
    syl2an2.1 $e |- ( ph -> ps ) $.
    syl2an2.2 $e |- ( ( ch /\ ph ) -> th ) $.
    syl2an2.3 $e |- ( ( ps /\ th ) -> ta ) $.
    $( ~ syl2an with antecedents in standard conjunction form.  (Contributed by
       Alan Sare, 27-Aug-2016.) $)
    syl2an2 $p |- ( ( ch /\ ph ) -> ta ) $=
      ( wa syl2an anabss7 ) CAEABDECAIFGHJK $.
  $}

  ${
    syl2an2r.1 $e |- ( ph -> ps ) $.
    syl2an2r.2 $e |- ( ( ph /\ ch ) -> th ) $.
    syl2an2r.3 $e |- ( ( ps /\ th ) -> ta ) $.
    $( ~ syl2anr with antecedents in standard conjunction form.  (Contributed
       by Alan Sare, 27-Aug-2016.) $)
    syl2an2r $p |- ( ( ph /\ ch ) -> ta ) $=
      ( wa syl2an anabss5 ) ACEABDEACIFGHJK $.
  $}

  ${
    impbida.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    impbida.2 $e |- ( ( ph /\ ch ) -> ps ) $.
    $( Deduce an equivalence from two implications.  (Contributed by NM,
       17-Feb-2007.) $)
    impbida $p |- ( ph -> ( ps <-> ch ) ) $=
      ( ex impbid ) ABCABCDFACBEFG $.
  $}

  $( Theorem *3.45 (Fact) of [WhiteheadRussell] p. 113.  (Contributed by NM,
     3-Jan-2005.) $)
  pm3.45 $p |- ( ( ph -> ps ) -> ( ( ph /\ ch ) -> ( ps /\ ch ) ) ) $=
    ( wi id anim1d ) ABDZABCGEF $.

  ${
    im2an9.1 $e |- ( ph -> ( ps -> ch ) ) $.
    im2an9.2 $e |- ( th -> ( ta -> et ) ) $.
    $( Deduction joining nested implications to form implication of
       conjunctions.  (Contributed by NM, 29-Feb-1996.) $)
    im2anan9 $p |- ( ( ph /\ th ) -> ( ( ps /\ ta ) -> ( ch /\ et ) ) ) $=
      ( wa wi adantr adantl anim12d ) ADIBCEFABCJDGKDEFJAHLM $.

    $( Deduction joining nested implications to form implication of
       conjunctions.  (Contributed by NM, 29-Feb-1996.) $)
    im2anan9r $p |- ( ( th /\ ph ) -> ( ( ps /\ ta ) -> ( ch /\ et ) ) ) $=
      ( wa wi im2anan9 ancoms ) ADBEICFIJABCDEFGHKL $.
  $}

  ${
    anim12dan.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    anim12dan.2 $e |- ( ( ph /\ th ) -> ta ) $.
    $( Conjoin antecedents and consequents in a deduction.  (Contributed by
       Mario Carneiro, 12-May-2014.) $)
    anim12dan $p |- ( ( ph /\ ( ps /\ th ) ) -> ( ch /\ ta ) ) $=
      ( wa ex anim12d imp ) ABDHCEHABCDEABCFIADEGIJK $.
  $}

  $( Two propositions are equivalent if they are both true.  Theorem *5.1 of
     [WhiteheadRussell] p. 123.  (Contributed by NM, 21-May-1994.) $)
  pm5.1 $p |- ( ( ph /\ ps ) -> ( ph <-> ps ) ) $=
    ( wb pm5.501 biimpa ) ABABCABDE $.

  $( Theorem *3.43 (Comp) of [WhiteheadRussell] p. 113.  (Contributed by NM,
     3-Jan-2005.)  (Revised by NM, 27-Nov-2013.) $)
  pm3.43 $p |- ( ( ( ph -> ps ) /\ ( ph -> ch ) ) ->
                ( ph -> ( ps /\ ch ) ) ) $=
    ( wi wa pm3.43i imp ) ABDACDABCEDABCFG $.

  $( Distributive law for implication over conjunction.  Compare Theorem *4.76
     of [WhiteheadRussell] p. 121.  (Contributed by NM, 3-Apr-1994.)  (Proof
     shortened by Wolf Lammen, 27-Nov-2013.) $)
  jcab $p |- ( ( ph -> ( ps /\ ch ) ) <->
                ( ( ph -> ps ) /\ ( ph -> ch ) ) ) $=
    ( wa wi simpl imim2i simpr jca pm3.43 impbii ) ABCDZEZABEZACEZDMNOLBABCFGLC
    ABCHGIABCJK $.

  $( Theorem *4.76 of [WhiteheadRussell] p. 121.  (Contributed by NM,
     3-Jan-2005.) $)
  pm4.76 $p |- ( ( ( ph -> ps ) /\ ( ph -> ch ) ) <->
                ( ph -> ( ps /\ ch ) ) ) $=
    ( wa wi jcab bicomi ) ABCDEABEACEDABCFG $.

  $( Theorem *4.38 of [WhiteheadRussell] p. 118.  (Contributed by NM,
     3-Jan-2005.) $)
  pm4.38 $p |- ( ( ( ph <-> ch ) /\ ( ps <-> th ) ) ->
                ( ( ph /\ ps ) <-> ( ch /\ th ) ) ) $=
    ( wb wa simpl simpr anbi12d ) ACEZBDEZFACBDJKGJKHI $.

  ${
    bi2an9.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    bi2an9.2 $e |- ( th -> ( ta <-> et ) ) $.
    $( Deduction joining two equivalences to form equivalence of conjunctions.
       (Contributed by NM, 31-Jul-1995.) $)
    bi2anan9 $p |- ( ( ph /\ th ) -> ( ( ps /\ ta ) <-> ( ch /\ et ) ) ) $=
      ( wa anbi1d anbi2d sylan9bb ) ABEICEIDCFIABCEGJDEFCHKL $.

    $( Deduction joining two equivalences to form equivalence of conjunctions.
       (Contributed by NM, 19-Feb-1996.) $)
    bi2anan9r $p |- ( ( th /\ ph ) -> ( ( ps /\ ta ) <-> ( ch /\ et ) ) ) $=
      ( wa wb bi2anan9 ancoms ) ADBEICFIJABCDEFGHKL $.

    $( Deduction joining two biconditionals with different antecedents.
       (Contributed by NM, 12-May-2004.) $)
    bi2bian9 $p |- ( ( ph /\ th ) -> ( ( ps <-> ta ) <-> ( ch <-> et ) ) ) $=
      ( wa wb adantr adantl bibi12d ) ADIBCEFABCJDGKDEFJAHLM $.
  $}

  $( Theorem *5.33 of [WhiteheadRussell] p. 125.  (Contributed by NM,
     3-Jan-2005.) $)
  pm5.33 $p |- ( ( ph /\ ( ps -> ch ) ) <->
                ( ph /\ ( ( ph /\ ps ) -> ch ) ) ) $=
    ( wi wa ibar imbi1d pm5.32i ) ABCDABEZCDABICABFGH $.

  $( Theorem *5.36 of [WhiteheadRussell] p. 125.  (Contributed by NM,
     3-Jan-2005.) $)
  pm5.36 $p |- ( ( ph /\ ( ph <-> ps ) ) <-> ( ps /\ ( ph <-> ps ) ) ) $=
    ( wb id pm5.32ri ) ABCZABFDE $.

  ${
    bianabs.1 $e |- ( ph -> ( ps <-> ( ph /\ ch ) ) ) $.
    $( Absorb a hypothesis into the second member of a biconditional.
       (Contributed by FL, 15-Feb-2007.) $)
    bianabs $p |- ( ph -> ( ps <-> ch ) ) $=
      ( wa ibar bitr4d ) ABACECDACFG $.
  $}

  ${
    biadani.1 $e |- ( ph -> ps ) $.
    $( An implication implies to the equivalence of some implied equivalence
       and some other equivalence involving a conjunction.  (Contributed by BJ,
       4-Mar-2023.) $)
    biadani $p |- ( ( ps -> ( ph <-> ch ) ) <-> ( ph <-> ( ps /\ ch ) ) ) $=
      ( wb wi wa pm5.32 pm4.71ri bibi1i bitr4i ) BACEFBAGZBCGZEAMEBACHALMABDIJK
      $.

    biadanii.2 $e |- ( ps -> ( ph <-> ch ) ) $.
    $( Inference associated with ~ biadani .  Add a conjunction to an
       equivalence.  (Contributed by Jeff Madsen, 20-Jun-2011.)  (Proof
       shortened by BJ, 4-Mar-2023.) $)
    biadanii $p |- ( ph <-> ( ps /\ ch ) ) $=
      ( wb wi wa biadani mpbi ) BACFGABCHFEABCDIJ $.
  $}

  ${
    biadanid.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    biadanid.2 $e |- ( ( ph /\ ch ) -> ( ps <-> th ) ) $.
    $( Deduction associated with ~ biadani .  Add a conjunction to an
       equivalence.  (Contributed by Thierry Arnoux, 16-Jun-2024.) $)
    biadanid $p |- ( ph -> ( ps <-> ( ch /\ th ) ) ) $=
      ( wa biimpa an32s mpdan jca biimpar anasss impbida ) ABCDGABGZCDEOCDEACBD
      ACGZBDFHIJKACDBPBDFLMN $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Logical negation (intuitionistic)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( 'Not' introduction.  One of the axioms of propositional logic.
     (Contributed by Mario Carneiro, 31-Jan-2015.)  Use its alias ~ pm2.01
     instead.  (New usage is discouraged.) $)
  ax-in1 $a |- ( ( ph -> -. ph ) -> -. ph ) $.

  $( 'Not' elimination.  One of the axioms of propositional logic.
     (Contributed by Mario Carneiro, 31-Jan-2015.) $)
  ax-in2 $a |- ( -. ph -> ( ph -> ps ) ) $.

  $( Reductio ad absurdum.  Theorem *2.01 of [WhiteheadRussell] p. 100.  This
     is valid intuitionistically (in the terminology of Section 1.2 of [Bauer]
     p. 482 it is a proof of negation not a proof by contradiction); compare
     with ~ pm2.18dc which only holds for some propositions.  Also called weak
     Clavius law.  (Contributed by Mario Carneiro, 12-May-2015.) $)
  pm2.01 $p |- ( ( ph -> -. ph ) -> -. ph ) $=
    ( ax-in1 ) AB $.

  $( From a wff and its negation, anything is true.  Theorem *2.21 of
     [WhiteheadRussell] p. 104.  Also called the Duns Scotus law.  (Contributed
     by Mario Carneiro, 12-May-2015.) $)
  pm2.21 $p |- ( -. ph -> ( ph -> ps ) ) $=
    ( ax-in2 ) ABC $.

  ${
    pm2.01d.1 $e |- ( ph -> ( ps -> -. ps ) ) $.
    $( Deduction based on reductio ad absurdum.  (Contributed by NM,
       18-Aug-1993.)  (Revised by Mario Carneiro, 31-Jan-2015.) $)
    pm2.01d $p |- ( ph -> -. ps ) $=
      ( wn wi pm2.01 syl ) ABBDZEHCBFG $.
  $}

  ${
    pm2.21d.1 $e |- ( ph -> -. ps ) $.
    $( A contradiction implies anything.  Deduction from ~ pm2.21 .
       (Contributed by NM, 10-Feb-1996.) $)
    pm2.21d $p |- ( ph -> ( ps -> ch ) ) $=
      ( wn wi pm2.21 syl ) ABEBCFDBCGH $.
  $}

  ${
    pm2.21dd.1 $e |- ( ph -> ps ) $.
    pm2.21dd.2 $e |- ( ph -> -. ps ) $.
    $( A contradiction implies anything.  Deduction from ~ pm2.21 .
       (Contributed by Mario Carneiro, 9-Feb-2017.) $)
    pm2.21dd $p |- ( ph -> ch ) $=
      ( pm2.21d mpd ) ABCDABCEFG $.
  $}

  $( Theorem *2.24 of [WhiteheadRussell] p. 104.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.24 $p |- ( ph -> ( -. ph -> ps ) ) $=
    ( wn pm2.21 com12 ) ACABABDE $.

  ${
    pm2.24d.1 $e |- ( ph -> ps ) $.
    $( Deduction version of ~ pm2.24 .  (Contributed by NM, 30-Jan-2006.)
       (Revised by Mario Carneiro, 31-Jan-2015.) $)
    pm2.24d $p |- ( ph -> ( -. ps -> ch ) ) $=
      ( wn wi pm2.24 syl ) ABBECFDBCGH $.
  $}

  ${
    pm2.24i.1 $e |- ph $.
    $( Inference version of ~ pm2.24 .  (Contributed by NM, 20-Aug-2001.)
       (Revised by Mario Carneiro, 31-Jan-2015.) $)
    pm2.24i $p |- ( -. ph -> ps ) $=
      ( wn pm2.21 mpi ) ADABCABEF $.
  $}

  ${
    con2d.1 $e |- ( ph -> ( ps -> -. ch ) ) $.
    $( A contraposition deduction.  (Contributed by NM, 19-Aug-1993.)  (Revised
       by NM, 12-Feb-2013.) $)
    con2d $p |- ( ph -> ( ch -> -. ps ) ) $=
      ( wn wi ax-in2 syl6 com23 pm2.01 ) ACBBEZFKABCKABCECKFDCKGHIBJH $.
  $}

  ${
    mt2d.1 $e |- ( ph -> ch ) $.
    mt2d.2 $e |- ( ph -> ( ps -> -. ch ) ) $.
    $( Modus tollens deduction.  (Contributed by NM, 4-Jul-1994.) $)
    mt2d $p |- ( ph -> -. ps ) $=
      ( wn con2d mpd ) ACBFDABCEGH $.
  $}

  ${
    nsyl3.1 $e |- ( ph -> -. ps ) $.
    nsyl3.2 $e |- ( ch -> ps ) $.
    $( A negated syllogism inference.  (Contributed by NM, 1-Dec-1995.)
       (Revised by NM, 13-Jun-2013.) $)
    nsyl3 $p |- ( ch -> -. ph ) $=
      ( wn wi a1i mt2d ) CABEABFGCDHI $.
  $}

  ${
    con2i.a $e |- ( ph -> -. ps ) $.
    $( A contraposition inference.  (Contributed by NM, 5-Aug-1993.)  (Proof
       shortened by O'Cat, 28-Nov-2008.)  (Proof shortened by Wolf Lammen,
       13-Jun-2013.) $)
    con2i $p |- ( ps -> -. ph ) $=
      ( id nsyl3 ) ABBCBDE $.
  $}

  ${
    nsyl.1 $e |- ( ph -> -. ps ) $.
    nsyl.2 $e |- ( ch -> ps ) $.
    $( A negated syllogism inference.  (Contributed by NM, 31-Dec-1993.)
       (Proof shortened by Wolf Lammen, 2-Mar-2013.) $)
    nsyl $p |- ( ph -> -. ch ) $=
      ( nsyl3 con2i ) CAABCDEFG $.
  $}

  $( Double negation introduction.  Theorem *2.12 of [WhiteheadRussell] p. 101.
     The converse need not hold.  It holds exactly for stable propositions (by
     definition, see ~ df-stab ) and in particular for decidable propositions
     (see ~ notnotrdc ).  See also ~ notnotnot .  (Contributed by NM,
     28-Dec-1992.)  (Proof shortened by Wolf Lammen, 2-Mar-2013.) $)
  notnot $p |- ( ph -> -. -. ph ) $=
    ( wn id con2i ) ABZAECD $.

  ${
    notnotd.1 $e |- ( ph -> ps ) $.
    $( Deduction associated with ~ notnot and ~ notnoti .  (Contributed by
       Jarvin Udandy, 2-Sep-2016.)  Avoid biconditional.  (Revised by Wolf
       Lammen, 27-Mar-2021.) $)
    notnotd $p |- ( ph -> -. -. ps ) $=
      ( wn notnot syl ) ABBDDCBEF $.
  $}

  ${
    con3d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( A contraposition deduction.  (Contributed by NM, 5-Aug-1993.)  (Revised
       by NM, 31-Jan-2015.) $)
    con3d $p |- ( ph -> ( -. ch -> -. ps ) ) $=
      ( wn notnot syl6 con2d ) ABCEZABCIEDCFGH $.
  $}

  ${
    con3i.a $e |- ( ph -> ps ) $.
    $( A contraposition inference.  (Contributed by NM, 5-Aug-1993.)  (Proof
       shortened by Wolf Lammen, 20-Jun-2013.) $)
    con3i $p |- ( -. ps -> -. ph ) $=
      ( wn id nsyl ) BDZBAGECF $.
  $}

  ${
    con3rr3.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Rotate through consequent right.  (Contributed by Wolf Lammen,
       3-Nov-2013.) $)
    con3rr3 $p |- ( -. ch -> ( ph -> -. ps ) ) $=
      ( wn con3d com12 ) ACEBEABCDFG $.
  $}

  $( Triple negation is equivalent to negation.  (Contributed by Jim Kingdon,
     28-Jul-2018.) $)
  notnotnot $p |- ( -. -. -. ph <-> -. ph ) $=
    ( wn notnot con3i impbii ) ABZBZBFAGACDFCE $.

  ${
    con3dimp.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Variant of ~ con3d with importation.  (Contributed by Jonathan Ben-Naim,
       3-Jun-2011.) $)
    con3dimp $p |- ( ( ph /\ -. ch ) -> -. ps ) $=
      ( wn con3d imp ) ACEBEABCDFG $.
  $}

  ${
    pm2.01da.1 $e |- ( ( ph /\ ps ) -> -. ps ) $.
    $( Deduction based on reductio ad absurdum.  (Contributed by Mario
       Carneiro, 9-Feb-2017.) $)
    pm2.01da $p |- ( ph -> -. ps ) $=
      ( wn ex pm2.01d ) ABABBDCEF $.
  $}

  $( In classical logic, this is just a restatement of ~ pm3.2 .  In
     intuitionistic logic, it still holds, but is weaker than pm3.2.
     (Contributed by Mario Carneiro, 12-May-2015.) $)
  pm3.2im $p |- ( ph -> ( ps -> -. ( ph -> -. ps ) ) ) $=
    ( wn wi pm2.27 con2d ) AABCZDBAGEF $.

  ${
    expi.1 $e |- ( -. ( ph -> -. ps ) -> ch ) $.
    $( An exportation inference.  (Contributed by NM, 5-Aug-1993.)  (Proof
       shortened by O'Cat, 28-Nov-2008.) $)
    expi $p |- ( ph -> ( ps -> ch ) ) $=
      ( wn wi pm3.2im syl6 ) ABABEFECABGDH $.
  $}

  ${
    pm2.65i.1 $e |- ( ph -> ps ) $.
    pm2.65i.2 $e |- ( ph -> -. ps ) $.
    $( Inference for proof by contradiction.  (Contributed by NM, 18-May-1994.)
       (Proof shortened by Wolf Lammen, 11-Sep-2013.) $)
    pm2.65i $p |- -. ph $=
      ( wn wi nsyl3 pm2.01 ax-mp ) AAEZFJABADCGAHI $.
  $}

  ${
    mt2.1 $e |- ps $.
    mt2.2 $e |- ( ph -> -. ps ) $.
    $( A rule similar to modus tollens.  (Contributed by NM, 19-Aug-1993.)
       (Proof shortened by Wolf Lammen, 10-Sep-2013.) $)
    mt2 $p |- -. ph $=
      ( a1i pm2.65i ) ABBACEDF $.
  $}

  $( Theorem used to justify definition of intuitionistic biconditional
     ~ df-bi .  (Contributed by NM, 24-Nov-2017.) $)
  biijust $p  |- ( ( ( ( ph -> ps ) /\ ( ps -> ph ) )
        -> ( ( ph -> ps ) /\ ( ps -> ph ) ) )
    /\ ( ( ( ph -> ps ) /\ ( ps -> ph ) )
           -> ( ( ph -> ps ) /\ ( ps -> ph ) ) ) ) $=
    ( wi wa id pm3.2i ) ABCBACDZGCZHGEZIF $.

  $( Contraposition.  Theorem *2.16 of [WhiteheadRussell] p. 103.  (Contributed
     by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen, 13-Feb-2013.) $)
  con3 $p |- ( ( ph -> ps ) -> ( -. ps -> -. ph ) ) $=
    ( wi id con3d ) ABCZABFDE $.

  $( Contraposition.  Theorem *2.03 of [WhiteheadRussell] p. 100.  (Contributed
     by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen, 12-Feb-2013.) $)
  con2 $p |- ( ( ph -> -. ps ) -> ( ps -> -. ph ) ) $=
    ( wn wi id con2d ) ABCDZABGEF $.

  ${
    mt2i.1 $e |- ch $.
    mt2i.2 $e |- ( ph -> ( ps -> -. ch ) ) $.
    $( Modus tollens inference.  (Contributed by NM, 26-Mar-1995.)  (Proof
       shortened by Wolf Lammen, 15-Sep-2012.) $)
    mt2i $p |- ( ph -> -. ps ) $=
      ( a1i mt2d ) ABCCADFEG $.
  $}

  ${
    negbi.1 $e |- ph $.
    $( Infer double negation.  (Contributed by NM, 27-Feb-2008.) $)
    notnoti $p |- -. -. ph $=
      ( wn notnot ax-mp ) AACCBADE $.
  $}

  ${
    pm2.21i.1 $e |- -. ph $.
    $( A contradiction implies anything.  Inference from ~ pm2.21 .
       (Contributed by NM, 16-Sep-1993.)  (Revised by Mario Carneiro,
       31-Jan-2015.) $)
    pm2.21i $p |- ( ph -> ps ) $=
      ( wn wi pm2.21 ax-mp ) ADABECABFG $.
  $}

  ${
    pm2.24ii.1 $e |- ph $.
    pm2.24ii.2 $e |- -. ph $.
    $( A contradiction implies anything.  Inference from ~ pm2.24 .
       (Contributed by NM, 27-Feb-2008.) $)
    pm2.24ii $p |- ps $=
      ( pm2.21i ax-mp ) ABCABDEF $.
  $}

  ${
    nsyld.1 $e |- ( ph -> ( ps -> -. ch ) ) $.
    nsyld.2 $e |- ( ph -> ( ta -> ch ) ) $.
    $( A negated syllogism deduction.  (Contributed by NM, 9-Apr-2005.) $)
    nsyld $p |- ( ph -> ( ps -> -. ta ) ) $=
      ( wn con3d syld ) ABCGDGEADCFHI $.
  $}

  ${
    nsyli.1 $e |- ( ph -> ( ps -> ch ) ) $.
    nsyli.2 $e |- ( th -> -. ch ) $.
    $( A negated syllogism inference.  (Contributed by NM, 3-May-1994.) $)
    nsyli $p |- ( ph -> ( th -> -. ps ) ) $=
      ( wn con3d syl5 ) DCGABGFABCEHI $.
  $}

  ${
    nsyl4.1 $e |- ( ph -> ps ) $.
    nsyl4.2 $e |- ( -. ph -> ch ) $.
    $( A negated syllogism inference.  (Contributed by Wolf Lammen,
       20-May-2024.) $)
    nsyl5 $p |- ( -. ps -> ch ) $=
      ( wn con3i syl ) BFAFCABDGEH $.
  $}

  ${
    jc.1 $e |- ( ph -> ps ) $.
    jc.2 $e |- ( ph -> ch ) $.
    $( Inference joining the consequents of two premises.  (Contributed by NM,
       5-Aug-1993.) $)
    jc $p |- ( ph -> -. ( ps -> -. ch ) ) $=
      ( wn wi pm3.2im sylc ) ABCBCFGFDEBCHI $.
  $}

  $( Theorem joining the consequents of two premises.  Theorem 8 of [Margaris]
     p. 60.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Josh
     Purinton, 29-Dec-2000.) $)
  jcn $p |- ( ph -> ( -. ps -> -. ( ph -> ps ) ) ) $=
    ( wi pm2.27 con3d ) AABCBABDE $.

  ${
    jcnd.1 $e |- ( ph -> ps ) $.
    jcnd.2 $e |- ( ph -> -. ch ) $.
    $( Deduction joining the consequents of two premises.  (Contributed by
       Glauco Siliprandi, 11-Dec-2019.)  (Proof shortened by Wolf Lammen,
       10-Apr-2024.) $)
    jcnd $p |- ( ph -> -. ( ps -> ch ) ) $=
      ( wn wi jcn sylc ) ABCFBCGFDEBCHI $.
  $}

  $( Contrapositive of ~ ax-1 .  (Contributed by BJ, 28-Oct-2023.) $)
  conax1 $p |- ( -. ( ph -> ps ) -> -. ps ) $=
    ( wi ax-1 con3i ) BABCBADE $.

  $( Weakening of ~ conax1 .  General instance of ~ pm2.51 and of ~ pm2.52 .
     (Contributed by BJ, 28-Oct-2023.) $)
  conax1k $p |- ( -. ( ph -> ps ) -> ( ch -> -. ps ) ) $=
    ( wi wn conax1 a1d ) ABDEBECABFG $.

  $( Theorem *2.51 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.51 $p |- ( -. ( ph -> ps ) -> ( ph -> -. ps ) ) $=
    ( conax1k ) ABAC $.

  $( Theorem *2.52 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.)  (Revised by Mario Carneiro, 31-Jan-2015.) $)
  pm2.52 $p |- ( -. ( ph -> ps ) -> ( -. ph -> -. ps ) ) $=
    ( wn conax1k ) ABACD $.

  $( Exportation theorem ~ pm3.3 (closed form of ~ ex ) expressed with
     primitive connectives.  (Contributed by NM, 5-Aug-1993.) $)
  expt $p |- ( ( -. ( ph -> -. ps ) -> ch ) -> ( ph -> ( ps -> ch ) ) ) $=
    ( wn wi pm3.2im imim1d com12 ) AABDEDZCEBCEABICABFGH $.

  $( Elimination of a nested antecedent.  (Contributed by Wolf Lammen,
     10-May-2013.) $)
  jarl $p |- ( ( ( ph -> ps ) -> ch ) -> ( -. ph -> ch ) ) $=
    ( wn wi pm2.21 imim1i ) ADABECABFG $.

  $( Theorem *2.65 of [WhiteheadRussell] p. 107.  Proof by contradiction.
     Proofs, such as this one, which assume a proposition, here ` ph ` , derive
     a contradiction, and therefore conclude ` -. ph ` , are valid
     intuitionistically (and can be called "proof of negation", for example by
     Section 1.2 of [Bauer] p. 482).  By contrast, proofs which assume
     ` -. ph ` , derive a contradiction, and conclude ` ph ` , such as
     ~ condandc , are only valid for decidable propositions.  (Contributed by
     NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen, 8-Mar-2013.) $)
  pm2.65 $p |- ( ( ph -> ps ) -> ( ( ph -> -. ps ) -> -. ph ) ) $=
    ( wi wn pm2.27 con2d a2i ) ABCAABDZCZABIDAIBAHEFGF $.

  ${
    pm2.65d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    pm2.65d.2 $e |- ( ph -> ( ps -> -. ch ) ) $.
    $( Deduction for proof by contradiction.  (Contributed by NM, 26-Jun-1994.)
       (Proof shortened by Wolf Lammen, 26-May-2013.) $)
    pm2.65d $p |- ( ph -> -. ps ) $=
      ( nsyld pm2.01d ) ABABCBEDFG $.
  $}

  ${
    pm2.65da.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    pm2.65da.2 $e |- ( ( ph /\ ps ) -> -. ch ) $.
    $( Deduction for proof by contradiction.  (Contributed by NM,
       12-Jun-2014.) $)
    pm2.65da $p |- ( ph -> -. ps ) $=
      ( ex wn pm2.65d ) ABCABCDFABCGEFH $.
  $}

  ${
    mto.1 $e |- -. ps $.
    mto.2 $e |- ( ph -> ps ) $.
    $( The rule of modus tollens.  (Contributed by NM, 19-Aug-1993.)  (Proof
       shortened by Wolf Lammen, 11-Sep-2013.) $)
    mto $p |- -. ph $=
      ( wn a1i pm2.65i ) ABDBEACFG $.
  $}

  ${
    mtod.1 $e |- ( ph -> -. ch ) $.
    mtod.2 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Modus tollens deduction.  (Contributed by NM, 3-Apr-1994.)  (Proof
       shortened by Wolf Lammen, 11-Sep-2013.) $)
    mtod $p |- ( ph -> -. ps ) $=
      ( wn a1d pm2.65d ) ABCEACFBDGH $.
  $}

  ${
    mtoi.1 $e |- -. ch $.
    mtoi.2 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Modus tollens inference.  (Contributed by NM, 5-Jul-1994.)  (Proof
       shortened by Wolf Lammen, 15-Sep-2012.) $)
    mtoi $p |- ( ph -> -. ps ) $=
      ( wn a1i mtod ) ABCCFADGEH $.
  $}

  ${
    mtand.1 $e |- ( ph -> -. ch ) $.
    mtand.2 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( A modus tollens deduction.  (Contributed by Jeff Hankins,
       19-Aug-2009.) $)
    mtand $p |- ( ph -> -. ps ) $=
      ( ex mtod ) ABCDABCEFG $.
  $}

  $( Equivalence property for negation.  Closed form.  (Contributed by BJ,
     27-Jan-2020.) $)
  notbi $p |- ( ( ph <-> ps ) -> ( -. ph <-> -. ps ) ) $=
    ( wb wn biimpr con3d biimp impbid ) ABCZADBDIBAABEFIABABGFH $.

  ${
    notbid.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Equivalence property for negation.  Deduction form.  (Contributed by NM,
       21-May-1994.)  (Revised by Mario Carneiro, 31-Jan-2015.) $)
    notbid $p |- ( ph -> ( -. ps <-> -. ch ) ) $=
      ( wb wn notbi syl ) ABCEBFCFEDBCGH $.
  $}

  ${
    notbii.1 $e |- ( ph <-> ps ) $.
    $( Equivalence property for negation.  Inference form.  (Contributed by NM,
       5-Aug-1993.)  (Revised by Mario Carneiro, 31-Jan-2015.) $)
    notbii $p |- ( -. ph <-> -. ps ) $=
      ( wb wn notbi ax-mp ) ABDAEBEDCABFG $.
  $}

  $( Contraposition.  Bidirectional version of ~ con2 .  (Contributed by NM,
     5-Aug-1993.) $)
  con2b $p |- ( ( ph -> -. ps ) <-> ( ps -> -. ph ) ) $=
    ( wn wi con2 impbii ) ABCDBACDABEBAEF $.

  $( A conjunction with a negated conjunction.  (Contributed by AV,
     8-Mar-2022.)  (Proof shortened by Wolf Lammen, 1-Apr-2022.) $)
  annotanannot $p |- ( ( ph /\ -. ( ph /\ ps ) ) <-> ( ph /\ -. ps ) ) $=
    ( wa wn ibar bicomd notbid pm5.32i ) AABCZDBDAIBABIABEFGH $.

  ${
    mtbi.1 $e |- -. ph $.
    mtbi.2 $e |- ( ph <-> ps ) $.
    $( An inference from a biconditional, related to modus tollens.
       (Contributed by NM, 15-Nov-1994.)  (Proof shortened by Wolf Lammen,
       25-Oct-2012.) $)
    mtbi $p |- -. ps $=
      ( biimpri mto ) BACABDEF $.
  $}

  ${
    mtbir.1 $e |- -. ps $.
    mtbir.2 $e |- ( ph <-> ps ) $.
    $( An inference from a biconditional, related to modus tollens.
       (Contributed by NM, 15-Nov-1994.)  (Proof shortened by Wolf Lammen,
       14-Oct-2012.) $)
    mtbir $p |- -. ph $=
      ( bicomi mtbi ) BACABDEF $.
  $}

  ${
    mtbid.min $e |- ( ph -> -. ps ) $.
    mtbid.maj $e |- ( ph -> ( ps <-> ch ) ) $.
    $( A deduction from a biconditional, similar to modus tollens.
       (Contributed by NM, 26-Nov-1995.) $)
    mtbid $p |- ( ph -> -. ch ) $=
      ( biimprd mtod ) ACBDABCEFG $.
  $}

  ${
    mtbird.min $e |- ( ph -> -. ch ) $.
    mtbird.maj $e |- ( ph -> ( ps <-> ch ) ) $.
    $( A deduction from a biconditional, similar to modus tollens.
       (Contributed by NM, 10-May-1994.) $)
    mtbird $p |- ( ph -> -. ps ) $=
      ( biimpd mtod ) ABCDABCEFG $.
  $}

  ${
    mtbii.min $e |- -. ps $.
    mtbii.maj $e |- ( ph -> ( ps <-> ch ) ) $.
    $( An inference from a biconditional, similar to modus tollens.
       (Contributed by NM, 27-Nov-1995.) $)
    mtbii $p |- ( ph -> -. ch ) $=
      ( biimprd mtoi ) ACBDABCEFG $.
  $}

  ${
    mtbiri.min $e |- -. ch $.
    mtbiri.maj $e |- ( ph -> ( ps <-> ch ) ) $.
    $( An inference from a biconditional, similar to modus tollens.
       (Contributed by NM, 24-Aug-1995.) $)
    mtbiri $p |- ( ph -> -. ps ) $=
      ( biimpd mtoi ) ABCDABCEFG $.
  $}

  ${
    sylnib.1 $e |- ( ph -> -. ps ) $.
    sylnib.2 $e |- ( ps <-> ch ) $.
    $( A mixed syllogism inference from an implication and a biconditional.
       (Contributed by Wolf Lammen, 16-Dec-2013.) $)
    sylnib $p |- ( ph -> -. ch ) $=
      ( wb a1i mtbid ) ABCDBCFAEGH $.
  $}

  ${
    sylnibr.1 $e |- ( ph -> -. ps ) $.
    sylnibr.2 $e |- ( ch <-> ps ) $.
    $( A mixed syllogism inference from an implication and a biconditional.
       Useful for substituting an consequent with a definition.  (Contributed
       by Wolf Lammen, 16-Dec-2013.) $)
    sylnibr $p |- ( ph -> -. ch ) $=
      ( bicomi sylnib ) ABCDCBEFG $.
  $}

  ${
    sylnbi.1 $e |- ( ph <-> ps ) $.
    sylnbi.2 $e |- ( -. ps -> ch ) $.
    $( A mixed syllogism inference from a biconditional and an implication.
       Useful for substituting an antecedent with a definition.  (Contributed
       by Wolf Lammen, 16-Dec-2013.) $)
    sylnbi $p |- ( -. ph -> ch ) $=
      ( wn notbii sylbi ) AFBFCABDGEH $.
  $}

  ${
    sylnbir.1 $e |- ( ps <-> ph ) $.
    sylnbir.2 $e |- ( -. ps -> ch ) $.
    $( A mixed syllogism inference from a biconditional and an implication.
       (Contributed by Wolf Lammen, 16-Dec-2013.) $)
    sylnbir $p |- ( -. ph -> ch ) $=
      ( bicomi sylnbi ) ABCBADFEG $.
  $}

  ${
    xchnxbi.1 $e |- ( -. ph <-> ps ) $.
    xchnxbi.2 $e |- ( ph <-> ch ) $.
    $( Replacement of a subexpression by an equivalent one.  (Contributed by
       Wolf Lammen, 27-Sep-2014.) $)
    xchnxbi $p |- ( -. ch <-> ps ) $=
      ( wn notbii bitr3i ) CFAFBACEGDH $.
  $}

  ${
    xchnxbir.1 $e |- ( -. ph <-> ps ) $.
    xchnxbir.2 $e |- ( ch <-> ph ) $.
    $( Replacement of a subexpression by an equivalent one.  (Contributed by
       Wolf Lammen, 27-Sep-2014.) $)
    xchnxbir $p |- ( -. ch <-> ps ) $=
      ( bicomi xchnxbi ) ABCDCAEFG $.
  $}

  ${
    xchbinx.1 $e |- ( ph <-> -. ps ) $.
    xchbinx.2 $e |- ( ps <-> ch ) $.
    $( Replacement of a subexpression by an equivalent one.  (Contributed by
       Wolf Lammen, 27-Sep-2014.) $)
    xchbinx $p |- ( ph <-> -. ch ) $=
      ( wn notbii bitri ) ABFCFDBCEGH $.
  $}

  ${
    xchbinxr.1 $e |- ( ph <-> -. ps ) $.
    xchbinxr.2 $e |- ( ch <-> ps ) $.
    $( Replacement of a subexpression by an equivalent one.  (Contributed by
       Wolf Lammen, 27-Sep-2014.) $)
    xchbinxr $p |- ( ph <-> -. ch ) $=
      ( bicomi xchbinx ) ABCDCBEFG $.
  $}

  ${
    mt2bi.1 $e |- ph $.
    $( A false consequent falsifies an antecedent.  (Contributed by NM,
       19-Aug-1993.)  (Proof shortened by Wolf Lammen, 12-Nov-2012.) $)
    mt2bi $p |- ( -. ps <-> ( ps -> -. ph ) ) $=
      ( wn wi a1bi con2b bitri ) BDZAIEBADEAICFABGH $.
  $}

  $( Modus-tollens-like theorem.  (Contributed by NM, 7-Apr-2001.)  (Revised by
     Mario Carneiro, 31-Jan-2015.) $)
  mtt $p |- ( -. ph -> ( -. ps <-> ( ps -> ph ) ) ) $=
    ( wn wi pm2.21 con3 com12 impbid2 ) ACZBCZBADZBAEKIJBAFGH $.

  $( Express conjunction in terms of implication.  One direction of Theorem
     *4.61 of [WhiteheadRussell] p. 120.  The converse holds for decidable
     propositions, as can be seen at ~ annimdc .  (Contributed by Jim Kingdon,
     24-Dec-2017.) $)
  annimim $p |- ( ( ph /\ -. ps ) -> -. ( ph -> ps ) ) $=
    ( wn wi pm2.27 con3 syl imp ) ABCZABDZCZAJBDIKDABEJBFGH $.

  $( One direction of Theorem *4.65 of [WhiteheadRussell] p. 120.  The converse
     holds in classical logic.  (Contributed by Jim Kingdon, 28-Jul-2018.) $)
  pm4.65r $p |- ( ( -. ph /\ -. ps ) -> -. ( -. ph -> ps ) ) $=
    ( wn annimim ) ACBD $.

  $( Express implication in terms of conjunction.  The converse only holds
     given a decidability condition; see ~ imandc .  (Contributed by Jim
     Kingdon, 24-Dec-2017.) $)
  imanim $p |- ( ( ph -> ps ) -> -. ( ph /\ -. ps ) ) $=
    ( wn wa wi annimim con2i ) ABCDABEABFG $.

  $( Theorem *3.37 (Transp) of [WhiteheadRussell] p. 112.  (Contributed by NM,
     3-Jan-2005.) $)
  pm3.37 $p |- ( ( ( ph /\ ps ) -> ch ) -> ( ( ph /\ -. ch ) -> -. ps ) ) $=
    ( wa wi wn pm3.3 con3 syl6 impd ) ABDCEZACFZBFZKABCELMEABCGBCHIJ $.

  $( Express implication in terms of conjunction.  (Contributed by NM,
     9-Apr-1994.)  (Revised by Mario Carneiro, 1-Feb-2015.) $)
  imnan $p |- ( ( ph -> -. ps ) <-> -. ( ph /\ ps ) ) $=
    ( wn wi wa pm3.2im imp con2i pm3.2 con3rr3 impbii ) ABCDZABEZCMLABLCABFGHAB
    MABIJK $.

  ${
    imnani.1 $e |- -. ( ph /\ ps ) $.
    $( Express implication in terms of conjunction.  (Contributed by Mario
       Carneiro, 28-Sep-2015.) $)
    imnani $p |- ( ph -> -. ps ) $=
      ( wn wi wa imnan mpbir ) ABDEABFDCABGH $.
  $}

  $( Theorem to move a conjunct in and out of a negation.  (Contributed by NM,
     9-Nov-2003.) $)
  nan $p |- ( ( ph -> -. ( ps /\ ch ) ) <-> ( ( ph /\ ps ) -> -. ch ) ) $=
    ( wa wn wi impexp imnan imbi2i bitr2i ) ABDCEZFABKFZFABCDEZFABKGLMABCHIJ $.

  ${
    mpnanrd.1 $e |- ( ph -> ps ) $.
    mpnanrd.2 $e |- ( ph -> -. ( ps /\ ch ) ) $.
    $( Eliminate the right side of a negated conjunction in an implication.
       (Contributed by ML, 17-Oct-2020.) $)
    mpnanrd $p |- ( ph -> -. ch ) $=
      ( wn wa wi imnan sylibr mpd ) ABCFZDABCGFBLHEBCIJK $.
  $}

  $( Law of noncontradiction.  Theorem *3.24 of [WhiteheadRussell] p. 111 (who
     call it the "law of contradiction").  (Contributed by NM, 16-Sep-1993.)
     (Revised by Mario Carneiro, 2-Feb-2015.) $)
  pm3.24 $p |- -. ( ph /\ -. ph ) $=
    ( wn wi wa notnot imnan mpbi ) AABZBCAHDBAEAHFG $.

  $( Theorem *4.15 of [WhiteheadRussell] p. 117.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 18-Nov-2012.) $)
  pm4.15 $p |- ( ( ( ph /\ ps ) -> -. ch ) <-> ( ( ps /\ ch ) -> -. ph ) ) $=
    ( wa wn wi con2b nan bitr2i ) BCDZAEFAJEFABDCEFJAGABCHI $.

  $( Two propositions are equivalent if they are both false.  Theorem *5.21 of
     [WhiteheadRussell] p. 124.  (Contributed by NM, 21-May-1994.)  (Revised by
     Mario Carneiro, 31-Jan-2015.) $)
  pm5.21 $p |- ( ( -. ph /\ -. ps ) -> ( ph <-> ps ) ) $=
    ( wn wa simpl pm2.21d simpr impbid ) ACZBCZDZABKABIJEFKBAIJGFH $.

  $( Two propositions are equivalent if they are both false.  Closed form of
     ~ 2false .  Equivalent to a ~ biimpr -like version of the xor-connective.
     (Contributed by Wolf Lammen, 13-May-2013.)  (Revised by Mario Carneiro,
     31-Jan-2015.) $)
  pm5.21im $p |- ( -. ph -> ( -. ps -> ( ph <-> ps ) ) ) $=
    ( wn wb pm5.21 ex ) ACBCABDABEF $.

  $( The negation of a wff is equivalent to the wff's equivalence to falsehood.
     (Contributed by Juha Arpiainen, 19-Jan-2006.)  (Revised by Mario Carneiro,
     31-Jan-2015.) $)
  nbn2 $p |- ( -. ph -> ( -. ps <-> ( ph <-> ps ) ) ) $=
    ( wn wb pm5.21im wi biimpr mtt imbitrrid impbid ) ACZBCZABDZABEMLKBAFABGABH
    IJ $.

  $( Transfer negation via an equivalence.  (Contributed by NM, 3-Oct-2007.)
     (Proof shortened by Wolf Lammen, 28-Jan-2013.) $)
  bibif $p |- ( -. ps -> ( ( ph <-> ps ) <-> -. ph ) ) $=
    ( wn wb nbn2 bicom bitr2di ) BCACBADABDBAEBAFG $.

  ${
    nbn.1 $e |- -. ph $.
    $( The negation of a wff is equivalent to the wff's equivalence to
       falsehood.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf
       Lammen, 3-Oct-2013.) $)
    nbn $p |- ( -. ps <-> ( ps <-> ph ) ) $=
      ( wb wn bibif ax-mp bicomi ) BADZBEZAEIJDCBAFGH $.
  $}

  ${
    nbn3.1 $e |- ph $.
    $( Transfer falsehood via equivalence.  (Contributed by NM,
       11-Sep-2006.) $)
    nbn3 $p |- ( -. ps <-> ( ps <-> -. ph ) ) $=
      ( wn notnoti nbn ) ADBACEF $.
  $}

  ${
    2false.1 $e |- -. ph $.
    2false.2 $e |- -. ps $.
    $( Two falsehoods are equivalent.  (Contributed by NM, 4-Apr-2005.)
       (Revised by Mario Carneiro, 31-Jan-2015.) $)
    2false $p |- ( ph <-> ps ) $=
      ( pm2.21i impbii ) ABABCEBADEF $.
  $}

  ${
    2falsed.1 $e |- ( ph -> -. ps ) $.
    2falsed.2 $e |- ( ph -> -. ch ) $.
    $( Two falsehoods are equivalent (deduction form).  (Contributed by NM,
       11-Oct-2013.) $)
    2falsed $p |- ( ph -> ( ps <-> ch ) ) $=
      ( pm2.21d impbid ) ABCABCDFACBEFG $.
  $}

  ${
    pm5.21ni.1 $e |- ( ph -> ps ) $.
    pm5.21ni.2 $e |- ( ch -> ps ) $.
    $( Two propositions implying a false one are equivalent.  (Contributed by
       NM, 16-Feb-1996.)  (Proof shortened by Wolf Lammen, 19-May-2013.) $)
    pm5.21ni $p |- ( -. ps -> ( ph <-> ch ) ) $=
      ( wn con3i 2falsed ) BFACABDGCBEGH $.

    pm5.21nii.3 $e |- ( ps -> ( ph <-> ch ) ) $.
    $( Eliminate an antecedent implied by each side of a biconditional.
       (Contributed by NM, 21-May-1999.)  (Revised by Mario Carneiro,
       31-Jan-2015.) $)
    pm5.21nii $p |- ( ph <-> ch ) $=
      ( wb syl ibi ibir impbii ) ACACABACGZDFHICACBLEFHJK $.
  $}

  ${
    pm5.21ndd.1 $e |- ( ph -> ( ch -> ps ) ) $.
    pm5.21ndd.2 $e |- ( ph -> ( th -> ps ) ) $.
    pm5.21ndd.3 $e |- ( ph -> ( ps -> ( ch <-> th ) ) ) $.
    $( Eliminate an antecedent implied by each side of a biconditional,
       deduction version.  (Contributed by Paul Chapman, 21-Nov-2012.)
       (Revised by Mario Carneiro, 31-Jan-2015.) $)
    pm5.21ndd $p |- ( ph -> ( ch <-> th ) ) $=
      ( wb syld ibd bicom1 syl6 impbid ) ACDACDACBCDHZEGIJADCADNDCHADBNFGICDKLJ
      M $.
  $}

  $( Theorem *5.19 of [WhiteheadRussell] p. 124.  (Contributed by NM,
     3-Jan-2005.)  (Revised by Mario Carneiro, 31-Jan-2015.) $)
  pm5.19 $p |- -. ( ph <-> -. ph ) $=
    ( wn wb biimp pm2.01d id mpbird pm2.65i ) AABZCZAJAIJAAIDEZJFGKH $.

  $( Theorem *4.8 of [WhiteheadRussell] p. 122.  This one holds for all
     propositions, but compare with ~ pm4.81dc which requires a decidability
     condition.  (Contributed by NM, 3-Jan-2005.) $)
  pm4.8 $p |- ( ( ph -> -. ph ) <-> -. ph ) $=
    ( wn wi pm2.01 ax-1 impbii ) AABZCGADGAEF $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Logical disjunction
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Declare the connective for disjunction ('or'). $)
  $c \/ $. $( Vee (read:  'or') $)

  $( Extend wff definition to include disjunction ('or'). $)
  wo $a wff ( ph \/ ps ) $.

  $( Definition of 'or'.  One of the axioms of propositional logic.
     (Contributed by Mario Carneiro, 31-Jan-2015.)  Use its alias ~ jaob
     instead.  (New usage is discouraged.) $)
  ax-io $a |-
             ( ( ( ph \/ ch ) -> ps ) <-> ( ( ph -> ps ) /\ ( ch -> ps ) ) ) $.

  $( Disjunction of antecedents.  Compare Theorem *4.77 of [WhiteheadRussell]
     p. 121.  Alias of ~ ax-io .  (Contributed by NM, 30-May-1994.)  (Revised
     by Mario Carneiro, 31-Jan-2015.) $)
  jaob $p |- ( ( ( ph \/ ch ) -> ps ) <-> ( ( ph -> ps ) /\ ( ch -> ps ) ) ) $=
    ( ax-io ) ABCD $.

  $( Introduction of a disjunct.  Axiom *1.3 of [WhiteheadRussell] p. 96.
     (Contributed by NM, 30-Aug-1993.)  (Revised by NM, 31-Jan-2015.) $)
  olc $p |- ( ph -> ( ps \/ ph ) ) $=
    ( wo wi wa id jaob mpbi simpri ) BBACZDZAJDZJJDKLEJFBJAGHI $.

  $( Introduction of a disjunct.  Theorem *2.2 of [WhiteheadRussell] p. 104.
     (Contributed by NM, 30-Aug-1993.)  (Revised by NM, 31-Jan-2015.) $)
  orc $p |- ( ph -> ( ph \/ ps ) ) $=
    ( wo wi wa id jaob mpbi simpli ) AABCZDZBJDZJJDKLEJFAJBGHI $.

  $( Slight generalization of Theorem *2.67 of [WhiteheadRussell] p. 107.
     (Contributed by NM, 3-Jan-2005.)  (Revised by NM, 9-Dec-2012.) $)
  pm2.67-2 $p |- ( ( ( ph \/ ch ) -> ps ) -> ( ph -> ps ) ) $=
    ( wo orc imim1i ) AACDBACEF $.

  $( Absorption of disjunction into equivalence.  (Contributed by NM,
     6-Aug-1995.)  (Proof shortened by Wolf Lammen, 3-Nov-2013.) $)
  oibabs $p |- ( ( ( ph \/ ps ) -> ( ph <-> ps ) ) <-> ( ph <-> ps ) ) $=
    ( wo wb wi pm2.67-2 ibd olc imim1i ibibr sylibr impbid ax-1 impbii ) ABCZAB
    DZEZPQABQABAPBFGQBPEBAEBOPBAHIBAJKLPOMN $.

  $( Theorem *3.44 of [WhiteheadRussell] p. 113.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 3-Oct-2013.) $)
  pm3.44 $p |- ( ( ( ps -> ph ) /\ ( ch -> ph ) ) ->
                ( ( ps \/ ch ) -> ph ) ) $=
    ( wo wi wa jaob biimpri ) BCDAEBAECAEFBACGH $.

  ${
    jaoi.1 $e |- ( ph -> ps ) $.
    jaoi.2 $e |- ( ch -> ps ) $.
    $( Inference disjoining the antecedents of two implications.  (Contributed
       by NM, 5-Apr-1994.)  (Revised by NM, 31-Jan-2015.) $)
    jaoi $p |- ( ( ph \/ ch ) -> ps ) $=
      ( wi wo pm3.44 mp2an ) ABFCBFACGBFDEBACHI $.
  $}

  ${
    jaod.1 $e |- ( ph -> ( ps -> ch ) ) $.
    jaod.2 $e |- ( ph -> ( th -> ch ) ) $.
    $( Deduction disjoining the antecedents of two implications.  (Contributed
       by NM, 18-Aug-1994.)  (Revised by NM, 4-Apr-2013.) $)
    jaod $p |- ( ph -> ( ( ps \/ th ) -> ch ) ) $=
      ( wo wi com12 jaoi ) BDGACBACHDABCEIADCFIJI $.

    jaod.3 $e |- ( ph -> ( ps \/ th ) ) $.
    $( Eliminate a disjunction in a deduction.  (Contributed by Mario Carneiro,
       29-May-2016.) $)
    mpjaod $p |- ( ph -> ch ) $=
      ( wo jaod mpd ) ABDHCGABCDEFIJ $.
  $}

  ${
    jaao.1 $e |- ( ph -> ( ps -> ch ) ) $.
    jaao.2 $e |- ( th -> ( ta -> ch ) ) $.
    $( Inference conjoining and disjoining the antecedents of two implications.
       (Contributed by NM, 30-Sep-1999.) $)
    jaao $p |- ( ( ph /\ th ) -> ( ( ps \/ ta ) -> ch ) ) $=
      ( wa wi adantr adantl jaod ) ADHBCEABCIDFJDECIAGKL $.

    $( Inference disjoining and conjoining the antecedents of two implications.
       (Contributed by Stefan Allan, 1-Nov-2008.) $)
    jaoa $p |- ( ( ph \/ th ) -> ( ( ps /\ ta ) -> ch ) ) $=
      ( wa wi adantrd adantld jaoi ) ABEHCIDABCEFJDECBGKL $.
  $}

  $( Implication in terms of disjunction.  One direction of theorem *4.6 of
     [WhiteheadRussell] p. 120.  The converse holds for decidable propositions,
     as seen at ~ imordc .  (Contributed by Jim Kingdon, 21-Jul-2018.) $)
  imorr $p |- ( ( -. ph \/ ps ) -> ( ph -> ps ) ) $=
    ( wn wi ax-in2 ax-1 jaoi ) ACABDBABEBAFG $.

  $( Theorem *2.53 of [WhiteheadRussell] p. 107.  This holds
     intuitionistically, although its converse does not (see ~ pm2.54dc ).
     (Contributed by NM, 3-Jan-2005.)  (Revised by NM, 31-Jan-2015.) $)
  pm2.53 $p |- ( ( ph \/ ps ) -> ( -. ph -> ps ) ) $=
    ( wn wi pm2.24 ax-1 jaoi ) AACZBDBABEBHFG $.

  ${
    ori.1 $e |- ( ph \/ ps ) $.
    $( Infer implication from disjunction.  (Contributed by NM, 11-Jun-1994.)
       (Revised by Mario Carneiro, 31-Jan-2015.) $)
    ori $p |- ( -. ph -> ps ) $=
      ( wo wn wi pm2.53 ax-mp ) ABDAEBFCABGH $.
  $}

  ${
    ord.1 $e |- ( ph -> ( ps \/ ch ) ) $.
    $( Deduce implication from disjunction.  (Contributed by NM, 18-May-1994.)
       (Revised by Mario Carneiro, 31-Jan-2015.) $)
    ord $p |- ( ph -> ( -. ps -> ch ) ) $=
      ( wo wn wi pm2.53 syl ) ABCEBFCGDBCHI $.
  $}

  $( Elimination of disjunction by denial of a disjunct.  Theorem *2.55 of
     [WhiteheadRussell] p. 107.  (Contributed by NM, 12-Aug-1994.)  (Proof
     shortened by Wolf Lammen, 21-Jul-2012.) $)
  orel1 $p |- ( -. ph -> ( ( ph \/ ps ) -> ps ) ) $=
    ( wo wn pm2.53 com12 ) ABCADBABEF $.

  $( Elimination of disjunction by denial of a disjunct.  Theorem *2.56 of
     [WhiteheadRussell] p. 107.  (Contributed by NM, 12-Aug-1994.)  (Proof
     shortened by Wolf Lammen, 5-Apr-2013.) $)
  orel2 $p |- ( -. ph -> ( ( ps \/ ph ) -> ps ) ) $=
    ( wn idd pm2.21 jaod ) ACZBBAGBDABEF $.

  $( Axiom *1.4 of [WhiteheadRussell] p. 96.  (Contributed by NM, 3-Jan-2005.)
     (Revised by NM, 15-Nov-2012.) $)
  pm1.4 $p |- ( ( ph \/ ps ) -> ( ps \/ ph ) ) $=
    ( wo olc orc jaoi ) ABACBABDBAEF $.

  $( Commutative law for disjunction.  Theorem *4.31 of [WhiteheadRussell]
     p. 118.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf
     Lammen, 15-Nov-2012.) $)
  orcom $p |- ( ( ph \/ ps ) <-> ( ps \/ ph ) ) $=
    ( wo pm1.4 impbii ) ABCBACABDBADE $.

  ${
    orcomd.1 $e |- ( ph -> ( ps \/ ch ) ) $.
    $( Commutation of disjuncts in consequent.  (Contributed by NM,
       2-Dec-2010.) $)
    orcomd $p |- ( ph -> ( ch \/ ps ) ) $=
      ( wo orcom sylib ) ABCECBEDBCFG $.
  $}

  ${
    orcoms.1 $e |- ( ( ph \/ ps ) -> ch ) $.
    $( Commutation of disjuncts in antecedent.  (Contributed by NM,
       2-Dec-2012.) $)
    orcoms $p |- ( ( ps \/ ph ) -> ch ) $=
      ( wo pm1.4 syl ) BAEABECBAFDG $.
  $}

  ${
    orci.1 $e |- ph $.
    $( Deduction introducing a disjunct.  (Contributed by NM, 19-Jan-2008.)
       (Revised by Mario Carneiro, 31-Jan-2015.) $)
    orci $p |- ( ph \/ ps ) $=
      ( wo orc ax-mp ) AABDCABEF $.

    $( Deduction introducing a disjunct.  (Contributed by NM, 19-Jan-2008.)
       (Revised by Mario Carneiro, 31-Jan-2015.) $)
    olci $p |- ( ps \/ ph ) $=
      ( wo olc ax-mp ) ABADCABEF $.
  $}

  ${
    orcd.1 $e |- ( ph -> ps ) $.
    $( Deduction introducing a disjunct.  (Contributed by NM, 20-Sep-2007.) $)
    orcd $p |- ( ph -> ( ps \/ ch ) ) $=
      ( wo orc syl ) ABBCEDBCFG $.

    $( Deduction introducing a disjunct.  (Contributed by NM, 11-Apr-2008.)
       (Proof shortened by Wolf Lammen, 3-Oct-2013.) $)
    olcd $p |- ( ph -> ( ch \/ ps ) ) $=
      ( orcd orcomd ) ABCABCDEF $.
  $}

  ${
    orcs.1 $e |- ( ( ph \/ ps ) -> ch ) $.
    $( Deduction eliminating disjunct. _Notational convention_:  We sometimes
       suffix with "s" the label of an inference that manipulates an
       antecedent, leaving the consequent unchanged.  The "s" means that the
       inference eliminates the need for a syllogism ( ~ syl ) -type inference
       in a proof.  (Contributed by NM, 21-Jun-1994.) $)
    orcs $p |- ( ph -> ch ) $=
      ( wo orc syl ) AABECABFDG $.
  $}

  ${
    olcs.1 $e |- ( ( ph \/ ps ) -> ch ) $.
    $( Deduction eliminating disjunct.  (Contributed by NM, 21-Jun-1994.)
       (Proof shortened by Wolf Lammen, 3-Oct-2013.) $)
    olcs $p |- ( ps -> ch ) $=
      ( orcoms orcs ) BACABCDEF $.
  $}

  $( Theorem *2.07 of [WhiteheadRussell] p. 101.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.07 $p |- ( ph -> ( ph \/ ph ) ) $=
    ( olc ) AAB $.

  $( Theorem *2.45 of [WhiteheadRussell] p. 106.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.45 $p |- ( -. ( ph \/ ps ) -> -. ph ) $=
    ( wo orc con3i ) AABCABDE $.

  $( Theorem *2.46 of [WhiteheadRussell] p. 106.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.46 $p |- ( -. ( ph \/ ps ) -> -. ps ) $=
    ( wo olc con3i ) BABCBADE $.

  $( Theorem *2.47 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.47 $p |- ( -. ( ph \/ ps ) -> ( -. ph \/ ps ) ) $=
    ( wo wn pm2.45 orcd ) ABCDADBABEF $.

  $( Theorem *2.48 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.48 $p |- ( -. ( ph \/ ps ) -> ( ph \/ -. ps ) ) $=
    ( wo wn pm2.46 olcd ) ABCDBDAABEF $.

  $( Theorem *2.49 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.49 $p |- ( -. ( ph \/ ps ) -> ( -. ph \/ -. ps ) ) $=
    ( wo wn pm2.46 olcd ) ABCDBDADABEF $.

  $( Theorem *2.67 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.)  (Revised by NM, 9-Dec-2012.) $)
  pm2.67 $p |- ( ( ( ph \/ ps ) -> ps ) -> ( ph -> ps ) ) $=
    ( pm2.67-2 ) ABBC $.

  $( A wff is equivalent to its disjunction with falsehood.  Theorem *4.74 of
     [WhiteheadRussell] p. 121.  (Contributed by NM, 23-Mar-1995.)  (Proof
     shortened by Wolf Lammen, 18-Nov-2012.) $)
  biorf $p |- ( -. ph -> ( ps <-> ( ph \/ ps ) ) ) $=
    ( wn wo olc orel1 impbid2 ) ACBABDBAEABFG $.

  $( A wff is equivalent to its negated disjunction with falsehood.
     (Contributed by NM, 9-Jul-2012.) $)
  biortn $p |- ( ph -> ( ps <-> ( -. ph \/ ps ) ) ) $=
    ( wn wo wb notnot biorf syl ) AACZCBIBDEAFIBGH $.

  ${
    biorfi.1 $e |- -. ph $.
    $( A wff is equivalent to its disjunction with falsehood.  (Contributed by
       NM, 23-Mar-1995.) $)
    biorfi $p |- ( ps <-> ( ps \/ ph ) ) $=
      ( wn wo wb orc orel2 impbid2 ax-mp ) ADZBBAEZFCKBLBAGABHIJ $.
  $}

  $( Theorem *2.621 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.)  (Revised by NM, 13-Dec-2013.) $)
  pm2.621 $p |- ( ( ph -> ps ) -> ( ( ph \/ ps ) -> ps ) ) $=
    ( wi id idd jaod ) ABCZABBGDGBEF $.

  $( Theorem *2.62 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 13-Dec-2013.) $)
  pm2.62 $p |- ( ( ph \/ ps ) -> ( ( ph -> ps ) -> ps ) ) $=
    ( wi wo pm2.621 com12 ) ABCABDBABEF $.

  ${
    imorri.1 $e |- ( -. ph \/ ps ) $.
    $( Infer implication from disjunction.  (Contributed by Jonathan Ben-Naim,
       3-Jun-2011.)  (Revised by Mario Carneiro, 31-Jan-2015.) $)
    imorri $p |- ( ph -> ps ) $=
      ( wn wo wi pm2.21 ax-1 jaoi ax-mp ) ADZBEABFZCKLBABGBAHIJ $.
  $}

  $( One direction of theorem *4.52 of [WhiteheadRussell] p. 120.  The converse
     also holds in classical logic.  (Contributed by Jim Kingdon,
     27-Jul-2018.) $)
  pm4.52im $p |- ( ( ph /\ -. ps ) -> -. ( -. ph \/ ps ) ) $=
    ( wn wa wi wo annimim imorr nsyl ) ABCDABEACBFABGABHI $.

  $( One direction of theorem *4.53 of [WhiteheadRussell] p. 120.  The converse
     also holds in classical logic.  (Contributed by Jim Kingdon,
     27-Jul-2018.) $)
  pm4.53r $p |- ( ( -. ph \/ ps ) -> -. ( ph /\ -. ps ) ) $=
    ( wn wa wo pm4.52im con2i ) ABCDACBEABFG $.

  $( Negated disjunction in terms of conjunction.  This version of DeMorgan's
     law is a biconditional for all propositions (not just decidable ones),
     unlike ~ oranim , ~ anordc , or ~ ianordc .  Compare Theorem *4.56 of
     [WhiteheadRussell] p. 120.  (Contributed by NM, 5-Aug-1993.)  (Revised by
     Mario Carneiro, 31-Jan-2015.) $)
  ioran $p |- ( -. ( ph \/ ps ) <-> ( -. ph /\ -. ps ) ) $=
    ( wo wn wa pm2.45 pm2.46 jca simpl con2i simpr jaoi impbii ) ABCZDZADZBDZEZ
    OPQABFABGHNRARDBRAPQIJRBPQKJLJM $.

  $( Theorem *3.14 of [WhiteheadRussell] p. 111.  One direction of De Morgan's
     law).  The biconditional holds for decidable propositions as seen at
     ~ ianordc .  The converse holds for decidable propositions, as seen at
     ~ pm3.13dc .  (Contributed by NM, 3-Jan-2005.)  (Revised by Mario
     Carneiro, 31-Jan-2015.) $)
  pm3.14 $p |- ( ( -. ph \/ -. ps ) -> -. ( ph /\ ps ) ) $=
    ( wn wa simpl con3i simpr jaoi ) ACABDZCBCIAABEFIBABGFH $.

  $( Theorem *3.1 of [WhiteheadRussell] p. 111.  The converse holds for
     decidable propositions, as seen at ~ anordc .  (Contributed by NM,
     3-Jan-2005.)  (Revised by Mario Carneiro, 31-Jan-2015.) $)
  pm3.1 $p |- ( ( ph /\ ps ) -> -. ( -. ph \/ -. ps ) ) $=
    ( wn wo wa pm3.14 con2i ) ACBCDABEABFG $.

  $( Disjunction of antecedents.  Compare Theorem *3.44 of [WhiteheadRussell]
     p. 113.  (Contributed by NM, 5-Apr-1994.)  (Proof shortened by Wolf
     Lammen, 4-Apr-2013.) $)
  jao $p |- ( ( ph -> ps ) -> ( ( ch -> ps ) -> ( ( ph \/ ch ) -> ps ) ) ) $=
    ( wi wo pm3.44 ex ) ABDCBDACEBDBACFG $.

  $( Axiom *1.2 (Taut) of [WhiteheadRussell] p. 96.  (Contributed by NM,
     3-Jan-2005.)  (Revised by NM, 10-Mar-2013.) $)
  pm1.2 $p |- ( ( ph \/ ph ) -> ph ) $=
    ( id jaoi ) AAAABZDC $.

  $( Idempotent law for disjunction.  Theorem *4.25 of [WhiteheadRussell]
     p. 117.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Andrew
     Salmon, 16-Apr-2011.)  (Proof shortened by Wolf Lammen, 10-Mar-2013.) $)
  oridm $p |- ( ( ph \/ ph ) <-> ph ) $=
    ( wo pm1.2 pm2.07 impbii ) AABAACADE $.

  $( Theorem *4.25 of [WhiteheadRussell] p. 117.  (Contributed by NM,
     3-Jan-2005.) $)
  pm4.25 $p |- ( ph <-> ( ph \/ ph ) ) $=
    ( wo oridm bicomi ) AABAACD $.

  ${
    orim12i.1 $e |- ( ph -> ps ) $.
    orim12i.2 $e |- ( ch -> th ) $.
    $( Disjoin antecedents and consequents of two premises.  (Contributed by
       NM, 6-Jun-1994.)  (Proof shortened by Wolf Lammen, 25-Jul-2012.) $)
    orim12i $p |- ( ( ph \/ ch ) -> ( ps \/ th ) ) $=
      ( wo orcd olcd jaoi ) ABDGCABDEHCDBFIJ $.
  $}

  ${
    orim1i.1 $e |- ( ph -> ps ) $.
    $( Introduce disjunct to both sides of an implication.  (Contributed by NM,
       6-Jun-1994.) $)
    orim1i $p |- ( ( ph \/ ch ) -> ( ps \/ ch ) ) $=
      ( id orim12i ) ABCCDCEF $.

    $( Introduce disjunct to both sides of an implication.  (Contributed by NM,
       6-Jun-1994.) $)
    orim2i $p |- ( ( ch \/ ph ) -> ( ch \/ ps ) ) $=
      ( id orim12i ) CCABCEDF $.
  $}

  ${
    orbi2i.1 $e |- ( ph <-> ps ) $.
    $( Inference adding a left disjunct to both sides of a logical equivalence.
       (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen,
       12-Dec-2012.) $)
    orbi2i $p |- ( ( ch \/ ph ) <-> ( ch \/ ps ) ) $=
      ( wo biimpi orim2i biimpri impbii ) CAECBEABCABDFGBACABDHGI $.

    $( Inference adding a right disjunct to both sides of a logical
       equivalence.  (Contributed by NM, 5-Aug-1993.) $)
    orbi1i $p |- ( ( ph \/ ch ) <-> ( ps \/ ch ) ) $=
      ( wo orcom orbi2i 3bitri ) ACECAECBEBCEACFABCDGCBFH $.
  $}

  ${
    orbi12i.1 $e |- ( ph <-> ps ) $.
    orbi12i.2 $e |- ( ch <-> th ) $.
    $( Infer the disjunction of two equivalences.  (Contributed by NM,
       5-Aug-1993.) $)
    orbi12i $p |- ( ( ph \/ ch ) <-> ( ps \/ th ) ) $=
      ( wo orbi2i orbi1i bitri ) ACGADGBDGCDAFHABDEIJ $.
  $}

  $( Axiom *1.5 (Assoc) of [WhiteheadRussell] p. 96.  (Contributed by NM,
     3-Jan-2005.) $)
  pm1.5 $p |- ( ( ph \/ ( ps \/ ch ) ) -> ( ps \/ ( ph \/ ch ) ) ) $=
    ( wo orc olcd olc orim2i jaoi ) ABACDZDBCDAJBACEFCJBCAGHI $.

  $( Swap two disjuncts.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by
     Wolf Lammen, 14-Nov-2012.) $)
  or12 $p |- ( ( ph \/ ( ps \/ ch ) ) <-> ( ps \/ ( ph \/ ch ) ) ) $=
    ( wo pm1.5 impbii ) ABCDDBACDDABCEBACEF $.

  $( Associative law for disjunction.  Theorem *4.33 of [WhiteheadRussell]
     p. 118.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Andrew
     Salmon, 26-Jun-2011.) $)
  orass $p |- ( ( ( ph \/ ps ) \/ ch ) <-> ( ph \/ ( ps \/ ch ) ) ) $=
    ( wo orcom or12 orbi2i 3bitri ) ABDZCDCIDACBDZDABCDZDICECABFJKACBEGH $.

  $( Theorem *2.31 of [WhiteheadRussell] p. 104.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.31 $p |- ( ( ph \/ ( ps \/ ch ) ) -> ( ( ph \/ ps ) \/ ch ) ) $=
    ( wo orass biimpri ) ABDCDABCDDABCEF $.

  $( Theorem *2.32 of [WhiteheadRussell] p. 105.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.32 $p |- ( ( ( ph \/ ps ) \/ ch ) -> ( ph \/ ( ps \/ ch ) ) ) $=
    ( wo orass biimpi ) ABDCDABCDDABCEF $.

  $( A rearrangement of disjuncts.  (Contributed by NM, 18-Oct-1995.)  (Proof
     shortened by Andrew Salmon, 26-Jun-2011.) $)
  or32 $p |- ( ( ( ph \/ ps ) \/ ch ) <-> ( ( ph \/ ch ) \/ ps ) ) $=
    ( wo orass or12 orcom 3bitri ) ABDCDABCDDBACDZDIBDABCEABCFBIGH $.

  $( Rearrangement of 4 disjuncts.  (Contributed by NM, 12-Aug-1994.) $)
  or4 $p |- ( ( ( ph \/ ps ) \/ ( ch \/ th ) ) <->
                ( ( ph \/ ch ) \/ ( ps \/ th ) ) ) $=
    ( wo or12 orbi2i orass 3bitr4i ) ABCDEZEZEACBDEZEZEABEJEACELEKMABCDFGABJHAC
    LHI $.

  $( Rearrangement of 4 disjuncts.  (Contributed by NM, 10-Jan-2005.) $)
  or42 $p |- ( ( ( ph \/ ps ) \/ ( ch \/ th ) ) <->
                 ( ( ph \/ ch ) \/ ( th \/ ps ) ) ) $=
    ( wo or4 orcom orbi2i bitri ) ABECDEEACEZBDEZEJDBEZEABCDFKLJBDGHI $.

  $( Distribution of disjunction over disjunction.  (Contributed by NM,
     25-Feb-1995.) $)
  orordi $p |- ( ( ph \/ ( ps \/ ch ) ) <->
               ( ( ph \/ ps ) \/ ( ph \/ ch ) ) ) $=
    ( wo oridm orbi1i or4 bitr3i ) ABCDZDAADZIDABDACDDJAIAEFAABCGH $.

  $( Distribution of disjunction over disjunction.  (Contributed by NM,
     25-Feb-1995.) $)
  orordir $p |- ( ( ( ph \/ ps ) \/ ch ) <->
               ( ( ph \/ ch ) \/ ( ps \/ ch ) ) ) $=
    ( wo oridm orbi2i or4 bitr3i ) ABDZCDICCDZDACDBCDDJCICEFABCCGH $.

  $( Theorem *2.3 of [WhiteheadRussell] p. 104.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.3 $p |- ( ( ph \/ ( ps \/ ch ) ) -> ( ph \/ ( ch \/ ps ) ) ) $=
    ( wo pm1.4 orim2i ) BCDCBDABCEF $.

  $( Theorem *2.41 of [WhiteheadRussell] p. 106.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.41 $p |- ( ( ps \/ ( ph \/ ps ) ) -> ( ph \/ ps ) ) $=
    ( wo olc id jaoi ) BABCZGBADGEF $.

  $( Theorem *2.42 of [WhiteheadRussell] p. 106.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.42 $p |- ( ( -. ph \/ ( ph -> ps ) ) -> ( ph -> ps ) ) $=
    ( wn wi pm2.21 id jaoi ) ACABDZHABEHFG $.

  $( Theorem *2.4 of [WhiteheadRussell] p. 106.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.4 $p |- ( ( ph \/ ( ph \/ ps ) ) -> ( ph \/ ps ) ) $=
    ( wo orc id jaoi ) AABCZGABDGEF $.

  $( Theorem *4.44 of [WhiteheadRussell] p. 119.  (Contributed by NM,
     3-Jan-2005.) $)
  pm4.44 $p |- ( ph <-> ( ph \/ ( ph /\ ps ) ) ) $=
    ( wa wo orc id simpl jaoi impbii ) AAABCZDAJEAAJAFABGHI $.

  $( Theorem *4.56 of [WhiteheadRussell] p. 120.  (Contributed by NM,
     3-Jan-2005.) $)
  pm4.56 $p |- ( ( -. ph /\ -. ps ) <-> -. ( ph \/ ps ) ) $=
    ( wo wn wa ioran bicomi ) ABCDADBDEABFG $.

  $( Disjunction in terms of conjunction (DeMorgan's law).  One direction of
     Theorem *4.57 of [WhiteheadRussell] p. 120.  The converse does not hold
     intuitionistically but does hold in classical logic.  (Contributed by Jim
     Kingdon, 25-Jul-2018.) $)
  oranim $p |- ( ( ph \/ ps ) -> -. ( -. ph /\ -. ps ) ) $=
    ( wn wa wo pm4.56 biimpi con2i ) ACBCDZABEZIJCABFGH $.

  $( Implication distributes over disjunction.  One direction of Theorem *4.78
     of [WhiteheadRussell] p. 121.  The converse holds in classical logic.
     (Contributed by Jim Kingdon, 15-Jan-2018.) $)
  pm4.78i $p |- ( ( ( ph -> ps ) \/ ( ph -> ch ) ) ->
       ( ph -> ( ps \/ ch ) ) ) $=
    ( wi wo orc imim2i olc jaoi ) ABDABCEZDACDBJABCFGCJACBHGI $.

  ${
    mtord.1 $e |- ( ph -> -. ch ) $.
    mtord.2 $e |- ( ph -> -. th ) $.
    mtord.3 $e |- ( ph -> ( ps -> ( ch \/ th ) ) ) $.
    $( A modus tollens deduction involving disjunction.  (Contributed by Jeff
       Hankins, 15-Jul-2009.)  (Revised by Mario Carneiro, 31-Jan-2015.) $)
    mtord $p |- ( ph -> -. ps ) $=
      ( wo wn pm2.21d jaod syld pm2.01d ) ABABCDHBIZGACNDACNEJADNFJKLM $.
  $}

  $( Theorem *4.45 of [WhiteheadRussell] p. 119.  (Contributed by NM,
     3-Jan-2005.) $)
  pm4.45 $p |- ( ph <-> ( ph /\ ( ph \/ ps ) ) ) $=
    ( wo orc pm4.71i ) AABCABDE $.

  $( Theorem *3.48 of [WhiteheadRussell] p. 114.  (Contributed by NM,
     28-Jan-1997.)  (Revised by NM, 1-Dec-2012.) $)
  pm3.48 $p |- ( ( ( ph -> ps ) /\ ( ch -> th ) ) ->
               ( ( ph \/ ch ) -> ( ps \/ th ) ) ) $=
    ( wi wo orc imim2i olc jaao ) ABEABDFZCDECBKABDGHDKCDBIHJ $.

  ${
    orim12d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    orim12d.2 $e |- ( ph -> ( th -> ta ) ) $.
    $( Disjoin antecedents and consequents in a deduction.  (Contributed by NM,
       10-May-1994.) $)
    orim12d $p |- ( ph -> ( ( ps \/ th ) -> ( ch \/ ta ) ) ) $=
      ( wi wo pm3.48 syl2anc ) ABCHDEHBDICEIHFGBCDEJK $.
  $}

  ${
    orim1d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Disjoin antecedents and consequents in a deduction.  (Contributed by NM,
       23-Apr-1995.) $)
    orim1d $p |- ( ph -> ( ( ps \/ th ) -> ( ch \/ th ) ) ) $=
      ( idd orim12d ) ABCDDEADFG $.

    $( Disjoin antecedents and consequents in a deduction.  (Contributed by NM,
       23-Apr-1995.) $)
    orim2d $p |- ( ph -> ( ( th \/ ps ) -> ( th \/ ch ) ) ) $=
      ( idd orim12d ) ADDBCADFEG $.
  $}

  $( Axiom *1.6 (Sum) of [WhiteheadRussell] p. 97.  (Contributed by NM,
     3-Jan-2005.) $)
  orim2 $p |- ( ( ps -> ch ) -> ( ( ph \/ ps ) -> ( ph \/ ch ) ) ) $=
    ( wi id orim2d ) BCDZBCAGEF $.

  ${
    orbid.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Deduction adding a left disjunct to both sides of a logical equivalence.
       (Contributed by NM, 5-Aug-1993.)  (Revised by Mario Carneiro,
       31-Jan-2015.) $)
    orbi2d $p |- ( ph -> ( ( th \/ ps ) <-> ( th \/ ch ) ) ) $=
      ( wo biimpd orim2d biimprd impbid ) ADBFDCFABCDABCEGHACBDABCEIHJ $.

    $( Deduction adding a right disjunct to both sides of a logical
       equivalence.  (Contributed by NM, 5-Aug-1993.) $)
    orbi1d $p |- ( ph -> ( ( ps \/ th ) <-> ( ch \/ th ) ) ) $=
      ( wo orbi2d orcom 3bitr4g ) ADBFDCFBDFCDFABCDEGBDHCDHI $.
  $}

  $( Theorem *4.37 of [WhiteheadRussell] p. 118.  (Contributed by NM,
     3-Jan-2005.) $)
  orbi1 $p |- ( ( ph <-> ps ) -> ( ( ph \/ ch ) <-> ( ps \/ ch ) ) ) $=
    ( wb id orbi1d ) ABDZABCGEF $.

  ${
    orbi12d.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    orbi12d.2 $e |- ( ph -> ( th <-> ta ) ) $.
    $( Deduction joining two equivalences to form equivalence of disjunctions.
       (Contributed by NM, 5-Aug-1993.) $)
    orbi12d $p |- ( ph -> ( ( ps \/ th ) <-> ( ch \/ ta ) ) ) $=
      ( wo orbi1d orbi2d bitrd ) ABDHCDHCEHABCDFIADECGJK $.
  $}

  $( Theorem *5.61 of [WhiteheadRussell] p. 125.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 30-Jun-2013.) $)
  pm5.61 $p |- ( ( ( ph \/ ps ) /\ -. ps ) <-> ( ph /\ -. ps ) ) $=
    ( wn wo biorf orcom bitr2di pm5.32ri ) BCZABDZAIABADJBAEBAFGH $.

  ${
    jaoian.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    jaoian.2 $e |- ( ( th /\ ps ) -> ch ) $.
    $( Inference disjoining the antecedents of two implications.  (Contributed
       by NM, 23-Oct-2005.) $)
    jaoian $p |- ( ( ( ph \/ th ) /\ ps ) -> ch ) $=
      ( wo wi ex jaoi imp ) ADGBCABCHDABCEIDBCFIJK $.
  $}

  ${
    jao1i.1 $e |- ( ps -> ( ch -> ph ) ) $.
    $( Add a disjunct in the antecedent of an implication.  (Contributed by
       Rodolfo Medina, 24-Sep-2010.) $)
    jao1i $p |- ( ( ph \/ ps ) -> ( ch -> ph ) ) $=
      ( wi ax-1 jaoi ) ACAEBACFDG $.
  $}

  ${
    jaodan.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    jaodan.2 $e |- ( ( ph /\ th ) -> ch ) $.
    $( Deduction disjoining the antecedents of two implications.  (Contributed
       by NM, 14-Oct-2005.) $)
    jaodan $p |- ( ( ph /\ ( ps \/ th ) ) -> ch ) $=
      ( wo ex jaod imp ) ABDGCABCDABCEHADCFHIJ $.

    jaodan.3 $e |- ( ph -> ( ps \/ th ) ) $.
    $( Eliminate a disjunction in a deduction.  A translation of natural
       deduction rule ` \/ ` E ( ` \/ ` elimination).  (Contributed by Mario
       Carneiro, 29-May-2016.) $)
    mpjaodan $p |- ( ph -> ch ) $=
      ( wo jaodan mpdan ) ABDHCGABCDEFIJ $.
  $}

  $( Theorem *4.77 of [WhiteheadRussell] p. 121.  (Contributed by NM,
     3-Jan-2005.) $)
  pm4.77 $p |- ( ( ( ps -> ph ) /\ ( ch -> ph ) ) <->
                ( ( ps \/ ch ) -> ph ) ) $=
    ( wo wi wa jaob bicomi ) BCDAEBAECAEFBACGH $.

  $( Theorem *2.63 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.63 $p |- ( ( ph \/ ps ) -> ( ( -. ph \/ ps ) -> ps ) ) $=
    ( wo wn pm2.53 idd jaod ) ABCZADBBABEHBFG $.

  $( Theorem *2.64 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.64 $p |- ( ( ph \/ ps ) -> ( ( ph \/ -. ps ) -> ph ) ) $=
    ( wn wo wi ax-1 orel2 jaoi com12 ) ABCZDABDZAAKAEJAKFBAGHI $.

  $( Theorem *5.53 of [WhiteheadRussell] p. 125.  (Contributed by NM,
     3-Jan-2005.) $)
  pm5.53 $p |- ( ( ( ( ph \/ ps ) \/ ch ) -> th ) <->
                ( ( ( ph -> th ) /\ ( ps -> th ) ) /\ ( ch -> th ) ) ) $=
    ( wo wi wa jaob anbi1i bitri ) ABEZCEDFKDFZCDFZGADFBDFGZMGKDCHLNMADBHIJ $.

  $( Theorem *2.38 of [WhiteheadRussell] p. 105.  (Contributed by NM,
     6-Mar-2008.) $)
  pm2.38 $p |- ( ( ps -> ch ) -> ( ( ps \/ ph ) -> ( ch \/ ph ) ) ) $=
    ( wi id orim1d ) BCDZBCAGEF $.

  $( Theorem *2.36 of [WhiteheadRussell] p. 105.  (Contributed by NM,
     6-Mar-2008.) $)
  pm2.36 $p |- ( ( ps -> ch ) -> ( ( ph \/ ps ) -> ( ch \/ ph ) ) ) $=
    ( wo wi pm1.4 pm2.38 syl5 ) ABDBADBCECADABFABCGH $.

  $( Theorem *2.37 of [WhiteheadRussell] p. 105.  (Contributed by NM,
     6-Mar-2008.) $)
  pm2.37 $p |- ( ( ps -> ch ) -> ( ( ps \/ ph ) -> ( ph \/ ch ) ) ) $=
    ( wi wo pm2.38 pm1.4 syl6 ) BCDBAECAEACEABCFCAGH $.

  $( Theorem *2.73 of [WhiteheadRussell] p. 108.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.73 $p |- ( ( ph -> ps ) -> ( ( ( ph \/ ps ) \/ ch ) ->
                ( ps \/ ch ) ) ) $=
    ( wi wo pm2.621 orim1d ) ABDABEBCABFG $.

  $( Theorem *2.74 of [WhiteheadRussell] p. 108.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Mario Carneiro, 31-Jan-2015.) $)
  pm2.74 $p |- ( ( ps -> ph ) -> ( ( ( ph \/ ps ) \/ ch ) ->
                ( ph \/ ch ) ) ) $=
    ( wi wo idd id jaod orim1d ) BADZABEACJAABJAFJGHI $.

  $( Theorem *2.76 of [WhiteheadRussell] p. 108.  (Contributed by NM,
     3-Jan-2005.)  (Revised by Mario Carneiro, 31-Jan-2015.) $)
  pm2.76 $p |- ( ( ph \/ ( ps -> ch ) ) ->
                ( ( ph \/ ps ) -> ( ph \/ ch ) ) ) $=
    ( wo wi orc a1d orim2 jaoi ) AABDZACDZEBCEAKJACFGABCHI $.

  $( Theorem *2.75 of [WhiteheadRussell] p. 108.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 4-Jan-2013.) $)
  pm2.75 $p |- ( ( ph \/ ps ) ->
                ( ( ph \/ ( ps -> ch ) ) -> ( ph \/ ch ) ) ) $=
    ( wi wo pm2.76 com12 ) ABCDEABEACEABCFG $.

  $( Theorem *2.8 of [WhiteheadRussell] p. 108.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Mario Carneiro, 31-Jan-2015.) $)
  pm2.8 $p |- ( ( ph \/ ps ) -> ( ( -. ps \/ ch ) -> ( ph \/ ch ) ) ) $=
    ( wo wn pm1.4 ord orim1d ) ABDZBEACIBAABFGH $.

  $( Theorem *2.81 of [WhiteheadRussell] p. 108.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.81 $p |- ( ( ps -> ( ch -> th ) ) -> ( ( ph \/ ps ) ->
                ( ( ph \/ ch ) -> ( ph \/ th ) ) ) ) $=
    ( wi wo orim2 pm2.76 syl6 ) BCDEZEABFAJFACFADFEABJGACDHI $.

  $( Theorem *2.82 of [WhiteheadRussell] p. 108.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.82 $p |- ( ( ( ph \/ ps ) \/ ch ) -> ( ( ( ph \/ -. ch ) \/ th ) ->
                ( ( ph \/ ps ) \/ th ) ) ) $=
    ( wo wn wi ax-1 pm2.24 orim2d jaoi orim1d ) ABEZCEACFZEZMDMOMGCMOHCNBACBIJK
    L $.

  ${
    pm3.2ni.1 $e |- -. ph $.
    pm3.2ni.2 $e |- -. ps $.
    $( Infer negated disjunction of negated premises.  (Contributed by NM,
       4-Apr-1995.) $)
    pm3.2ni $p |- -. ( ph \/ ps ) $=
      ( wo id pm2.21i jaoi mto ) ABEACAABAFBADGHI $.
  $}

  $( Absorption of redundant internal disjunct.  Compare Theorem *4.45 of
     [WhiteheadRussell] p. 119.  (Contributed by NM, 5-Aug-1993.)  (Proof
     shortened by Wolf Lammen, 28-Feb-2014.) $)
  orabs $p |- ( ph <-> ( ( ph \/ ps ) /\ ph ) ) $=
    ( wo orc pm4.71ri ) AABCABDE $.

  $( Absorb a disjunct into a conjunct.  (Contributed by Roy F. Longton,
     23-Jun-2005.)  (Proof shortened by Wolf Lammen, 10-Nov-2013.) $)
  oranabs $p |- ( ( ( ph \/ -. ps ) /\ ps ) <-> ( ph /\ ps ) ) $=
    ( wn wo biortn orcom bitr2di pm5.32ri ) BABCZDZABAIADJBAEIAFGH $.

  $( Distributive law for disjunction.  Theorem *4.41 of [WhiteheadRussell]
     p. 119.  (Contributed by NM, 5-Aug-1993.)  (Revised by Mario Carneiro,
     31-Jan-2015.) $)
  ordi $p |- ( ( ph \/ ( ps /\ ch ) ) <-> ( ( ph \/ ps ) /\ ( ph \/ ch ) ) ) $=
    ( wa wo simpl orim2i simpr jca orc adantl adantr olc jaoian jaodan impbii )
    ABCDZEZABEZACEZDRSTQBABCFGQCABCHGISARCARSAQJZKACRBARCUALQAMNOP $.

  $( Distributive law for disjunction.  (Contributed by NM, 12-Aug-1994.) $)
  ordir $p |- ( ( ( ph /\ ps ) \/ ch ) <->
              ( ( ph \/ ch ) /\ ( ps \/ ch ) ) ) $=
    ( wa wo ordi orcom anbi12i 3bitr4i ) CABDZECAEZCBEZDJCEACEZBCEZDCABFJCGMKNL
    ACGBCGHI $.

  $( Distributive law for conjunction.  Theorem *4.4 of [WhiteheadRussell]
     p. 118.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf
     Lammen, 5-Jan-2013.) $)
  andi $p |- ( ( ph /\ ( ps \/ ch ) ) <-> ( ( ph /\ ps ) \/ ( ph /\ ch ) ) ) $=
    ( wo wa orc olc jaodan anim2i jaoi impbii ) ABCDZEZABEZACEZDZABPCNOFONGHNMO
    BLABCFICLACBGIJK $.

  $( Distributive law for conjunction.  (Contributed by NM, 12-Aug-1994.) $)
  andir $p |- ( ( ( ph \/ ps ) /\ ch ) <->
              ( ( ph /\ ch ) \/ ( ps /\ ch ) ) ) $=
    ( wo wa andi ancom orbi12i 3bitr4i ) CABDZECAEZCBEZDJCEACEZBCEZDCABFJCGMKNL
    ACGBCGHI $.

  $( Double distributive law for disjunction.  (Contributed by NM,
     12-Aug-1994.) $)
  orddi $p |- ( ( ( ph /\ ps ) \/ ( ch /\ th ) ) <->
              ( ( ( ph \/ ch ) /\ ( ph \/ th ) ) /\
              ( ( ps \/ ch ) /\ ( ps \/ th ) ) ) ) $=
    ( wa wo ordir ordi anbi12i bitri ) ABECDEZFAKFZBKFZEACFADFEZBCFBDFEZEABKGLN
    MOACDHBCDHIJ $.

  $( Double distributive law for conjunction.  (Contributed by NM,
     12-Aug-1994.) $)
  anddi $p |- ( ( ( ph \/ ps ) /\ ( ch \/ th ) ) <->
              ( ( ( ph /\ ch ) \/ ( ph /\ th ) ) \/
              ( ( ps /\ ch ) \/ ( ps /\ th ) ) ) ) $=
    ( wo wa andir andi orbi12i bitri ) ABECDEZFAKFZBKFZEACFADFEZBCFBDFEZEABKGLN
    MOACDHBCDHIJ $.

  $( Prove formula-building rules for the biconditional connective. $)

  $( Theorem *4.39 of [WhiteheadRussell] p. 118.  (Contributed by NM,
     3-Jan-2005.) $)
  pm4.39 $p |- ( ( ( ph <-> ch ) /\ ( ps <-> th ) ) ->
                ( ( ph \/ ps ) <-> ( ch \/ th ) ) ) $=
    ( wb wa simpl simpr orbi12d ) ACEZBDEZFACBDJKGJKHI $.

  $( Conjunction implies disjunction with one common formula (1/4).
     (Contributed by BJ, 4-Oct-2019.) $)
  animorl $p |- ( ( ph /\ ps ) -> ( ph \/ ch ) ) $=
    ( wa simpl orcd ) ABDACABEF $.

  $( Conjunction implies disjunction with one common formula (2/4).
     (Contributed by BJ, 4-Oct-2019.) $)
  animorr $p |- ( ( ph /\ ps ) -> ( ch \/ ps ) ) $=
    ( wa simpr olcd ) ABDBCABEF $.

  $( Conjunction implies disjunction with one common formula (3/4).
     (Contributed by BJ, 4-Oct-2019.) $)
  animorlr $p |- ( ( ph /\ ps ) -> ( ch \/ ph ) ) $=
    ( wa simpl olcd ) ABDACABEF $.

  $( Conjunction implies disjunction with one common formula (4/4).
     (Contributed by BJ, 4-Oct-2019.) $)
  animorrl $p |- ( ( ph /\ ps ) -> ( ps \/ ch ) ) $=
    ( wa simpr orcd ) ABDBCABEF $.

  $( Implication in terms of biconditional and disjunction.  Theorem *4.72 of
     [WhiteheadRussell] p. 121.  (Contributed by NM, 30-Aug-1993.)  (Proof
     shortened by Wolf Lammen, 30-Jan-2013.) $)
  pm4.72 $p |- ( ( ph -> ps ) <-> ( ps <-> ( ph \/ ps ) ) ) $=
    ( wi wo wb olc pm2.621 impbid2 orc biimpr syl5 impbii ) ABCZBABDZEZMBNBAFAB
    GHANOBABIBNJKL $.

  $( Theorem *5.16 of [WhiteheadRussell] p. 124.  (Contributed by NM,
     3-Jan-2005.)  (Revised by Mario Carneiro, 31-Jan-2015.) $)
  pm5.16 $p |- -. ( ( ph <-> ps ) /\ ( ph <-> -. ps ) ) $=
    ( wb wn wa pm5.19 simpl simpr bitr3d mto ) ABCZABDZCZEZBLCBFNABLKMGKMHIJ $.

  $( A disjunction with a true formula is equivalent to that true formula.
     (Contributed by NM, 23-May-1999.) $)
  biort $p |- ( ph -> ( ph <-> ( ph \/ ps ) ) ) $=
    ( wo id orc 2thd ) AAABCADABEF $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Stable propositions
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Declare connective for stability. $)
  $c STAB $.

  $( Extend wff definition to include stability. $)
  wstab $a wff STAB ph $.

  $( Propositions where a double-negative can be removed are called stable.
     See Chapter 2 [Moschovakis] p. 2.

     Our notation for stability is a connective ` STAB ` which we place before
     the formula in question.  For example, ` STAB x = y ` corresponds
     to " ` x = y ` is stable".

     (Contributed by David A. Wheeler, 13-Aug-2018.) $)
  df-stab $a |- ( STAB ph <-> ( -. -. ph -> ph ) ) $.

  ${
    stbid.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( The equivalent of a stable proposition is stable.  (Contributed by Jim
       Kingdon, 12-Aug-2022.) $)
    stbid $p |- ( ph -> ( STAB ps <-> STAB ch ) ) $=
      ( wn wi wstab notbid imbi12d df-stab 3bitr4g ) ABEZEZBFCEZEZCFBGCGAMOBCAL
      NABCDHHDIBJCJK $.
  $}

  $( Every negated formula is stable.  (Contributed by David A. Wheeler,
     13-Aug-2018.) $)
  stabnot $p |- STAB -. ph $=
    ( wn wstab wi notnotnot biimpi df-stab mpbir ) ABZCIBBZIDJIAEFIGH $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Decidable propositions
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Declare connective for decidability. $)
  $c DECID $.

  $( Extend wff definition to include decidability. $)
  wdc $a wff DECID ph $.

  $( Propositions which are known to be true or false are called decidable.
     The (classical) Law of the Excluded Middle corresponds to the principle
     that all propositions are decidable, but even given intuitionistic logic,
     particular kinds of propositions may be decidable (for example, the
     proposition that two natural numbers are equal will be decidable under
     most sets of axioms).

     Our notation for decidability is a connective ` DECID ` which we place
     before the formula in question.  For example, ` DECID x = y ` corresponds
     to " ` x = y ` is decidable".

     We could transform intuitionistic logic to classical logic by adding
     unconditional forms of ~ condc , ~ exmiddc , ~ peircedc , or ~ notnotrdc ,
     any of which would correspond to the assertion that all propositions are
     decidable.

     (Contributed by Jim Kingdon, 11-Mar-2018.) $)
  df-dc $a |- ( DECID ph <-> ( ph \/ -. ph ) ) $.

  $( Law of excluded middle, for a decidable proposition.  The law of the
     excluded middle is also called the principle of _tertium non datur_.
     Theorem *2.11 of [WhiteheadRussell] p. 101.  It says that something is
     either true or not true; there are no in-between values of truth.  The key
     way in which intuitionistic logic differs from classical logic is that
     intuitionistic logic says that excluded middle only holds for some
     propositions, and classical logic says that it holds for all propositions.
     (Contributed by Jim Kingdon, 12-May-2018.) $)
  exmiddc $p |- ( DECID ph -> ( ph \/ -. ph ) ) $=
    ( wdc wn wo df-dc biimpi ) ABAACDAEF $.

  $( Commuted law of the excluded middle for a decidable proposition.  Based on
     theorem *2.1 of [WhiteheadRussell] p. 101.  (Contributed by Jim Kingdon,
     25-Mar-2018.) $)
  pm2.1dc $p |- ( DECID ph -> ( -. ph \/ ph ) ) $=
    ( wdc wn wo df-dc orcom bitri biimpi ) ABZACZADZIAJDKAEAJFGH $.

  ${
    dcbid.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Equivalence property for decidability.  Deduction form.  (Contributed by
       Jim Kingdon, 7-Sep-2019.) $)
    dcbid $p |- ( ph -> ( DECID ps <-> DECID ch ) ) $=
      ( wn wo wdc notbid orbi12d df-dc 3bitr4g ) ABBEZFCCEZFBGCGABCLMDABCDHIBJC
      JK $.
  $}

  $( Equivalence property for decidability.  Closed form.  (Contributed by BJ,
     27-Jan-2020.) $)
  dcbiit $p |- ( ( ph <-> ps ) -> ( DECID ph <-> DECID ps ) ) $=
    ( wb id dcbid ) ABCZABFDE $.

  ${
    dcbii.1 $e |- ( ph <-> ps ) $.
    $( Equivalence property for decidability.  Inference form.  (Contributed by
       Jim Kingdon, 28-Mar-2018.) $)
    dcbii $p |- ( DECID ph <-> DECID ps ) $=
      ( wb wdc dcbiit ax-mp ) ABDAEBEDCABFG $.
  $}

  $( An implication between two decidable propositions is decidable.
     (Contributed by Jim Kingdon, 28-Mar-2018.) $)
  dcim $p |- ( DECID ph -> ( DECID ps -> DECID ( ph -> ps ) ) ) $=
    ( wn wo wi df-dc wa anbi2i andi bitri pm3.4 annimim orim12i sylbi sylibr ex
    wdc ax-in2 a1d orc syl6 jaoi ) AQAACZDBQZABEZQZEZAFAUGUCAUDUFAUDGZUEUECZDZU
    FUHABGZABCZGZDZUJUHABULDZGUNUDUOABFHABULIJUKUEUMUIABKABLMNUEFZOPUCUDUEUFUCU
    EUDABRSUEUJUFUEUITUPOUAUBN $.

  $( The negation of a decidable proposition is decidable.  The converse need
     not hold, but does hold for negated propositions, see ~ dcnn .
     (Contributed by Jim Kingdon, 25-Mar-2018.) $)
  dcn $p |- ( DECID ph -> DECID -. ph ) $=
    ( wn wo wdc notnot orim2i orcoms df-dc 3imtr4i ) AABZCJJBZCZADJDJALAKJAEFGA
    HJHI $.

  $( Double negation elimination for a decidable proposition.  The converse,
     ~ notnot , holds for all propositions, not just decidable ones.  This is
     Theorem *2.14 of [WhiteheadRussell] p. 102, but with a decidability
     condition added.  (Contributed by Jim Kingdon, 11-Mar-2018.) $)
  notnotrdc $p |- ( DECID ph -> ( -. -. ph -> ph ) ) $=
    ( wdc wn wo wi df-dc orcom bitri pm2.53 sylbi ) ABZACZADZLCAEKALDMAFALGHLAI
    J $.

  $( Decidability implies stability.  The converse need not hold.  (Contributed
     by David A. Wheeler, 13-Aug-2018.) $)
  dcstab $p |- ( DECID ph -> STAB ph ) $=
    ( wdc wn wi wstab notnotrdc df-stab sylibr ) ABACCADAEAFAGH $.

  $( A formula is decidable if and only if its negation is decidable and it is
     stable (that is, it is testable and stable).  (Contributed by David A.
     Wheeler, 13-Aug-2018.)  (Proof shortened by BJ, 28-Oct-2023.) $)
  stdcndc $p |- ( ( STAB ph /\ DECID -. ph ) <-> DECID ph ) $=
    ( wstab wn wdc wa wo df-stab df-dc pm2.36 imp syl2anb sylibr dcstab dcn jca
    wi impbii ) ABZACZDZEZADZUAASFZUBRSCZAPZSUDFZUCTAGSHUEUFUCSUDAIJKAHLUBRTAMA
    NOQ $.

  $( Obsolete version of ~ stdcndc as of 28-Oct-2023.  (Contributed by David A.
     Wheeler, 13-Aug-2018.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  stdcndcOLD $p |- ( ( STAB ph /\ DECID -. ph ) <-> DECID ph ) $=
    ( wstab wn wdc wa wo exmiddc adantl df-stab biimpi orim2d adantr mpd orcomd
    wi df-dc sylibr dcstab dcn jca impbii ) ABZACZDZEZADZUEAUCFUFUEUCAUEUCUCCZF
    ZUCAFZUDUHUBUCGHUBUHUIOUDUBUGAUCUBUGAOAIJKLMNAPQUFUBUDARASTUA $.

  $( A formula is stable if and only if the decidability of its negation
     implies its decidability.  Note that the right-hand side of this
     biconditional is the converse of ~ dcn .  (Contributed by BJ,
     18-Nov-2023.) $)
  stdcn $p |- ( STAB ph <-> ( DECID -. ph -> DECID ph ) ) $=
    ( wstab wn wdc wi wa stdcndc biimpi ex wo imim1i orel2 sylcom df-dc imbi12i
    olc df-stab 3imtr4i impbii ) ABZACZDZADZEZTUBUCTUBFUCAGHIUAUACZJZAUAJZEZUEA
    EUDTUHUEUGAUEUFUGUEUAPKUAALMUBUFUCUGUANANOAQRS $.

  $( Decidability of the negation of a proposition is equivalent to
     decidability of its double negation.  See also ~ dcn .  The relation
     between ~ dcn and ~ dcnn is analogous to that between ~ notnot and
     ~ notnotnot (and directly stems from it).  Using the notion of "testable
     proposition" (proposition whose negation is decidable), ~ dcnn means that
     a proposition is testable if and only if its negation is testable, and
     ~ dcn means that decidability implies testability.  (Contributed by David
     A. Wheeler, 6-Dec-2018.)  (Proof shortened by BJ, 25-Nov-2023.) $)
  dcnn $p |- ( DECID -. ph <-> DECID -. -. ph ) $=
    ( wn wdc dcn wstab wi stabnot stdcn mpbi impbii ) ABZCZKBCZKDKEMLFAGKHIJ $.

  $( Obsolete proof of ~ dcnnOLD as of 25-Nov-2023.  (Contributed by David A.
     Wheeler, 6-Dec-2018.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  dcnnOLD $p |- ( DECID -. ph <-> DECID -. -. ph ) $=
    ( wn wo wdc notnotnot orbi2i orcom bitri df-dc 3bitr4ri ) ABZBZLBZCZKLCZLDK
    DNLKCOMKLAEFLKGHLIKIJ $.

  $( Double negation of decidability of a formula.  See also comment of ~ nndc
     to avoid a pitfall that could come from the label "nnexmid".  This theorem
     can also be proved from ~ bj-nnor as in ~ bj-nndcALT .  (Contributed by
     BJ, 9-Oct-2019.) $)
  nnexmid $p |- -. -. ( ph \/ -. ph ) $=
    ( wn wo wa pm3.24 ioran mtbir ) AABZCBHHBDHEAHFG $.

  $( Double negation of decidability of a formula.  Intuitionistic logic
     refutes the negation of decidability (but does not prove decidability) of
     any formula.

     This should not trick the reader into thinking that ` -. -. EXMID ` is
     provable in intuitionistic logic.  Indeed, if we could quantify over
     formula metavariables, then generalizing ~ nnexmid over ` ph ` would
     give " ` |- A. ph -. -. DECID ph ` ", but ` EXMID `
     is " ` A. ph DECID ph ` ", so proving ` -. -. EXMID ` would amount to
     proving " ` -. -. A. ph DECID ph ` ", which is not implied by the above
     theorem.  Indeed, the converse of ~ nnal does not hold.  Since our system
     does not allow quantification over formula metavariables, we can reproduce
     this argument by representing formulas as subsets of ` ~P 1o ` , like we
     do in our definition of ` EXMID ` ( ~ df-exmid ): then, we can prove
     ` A. x e. ~P 1o -. -. DECID x = 1o ` but we cannot prove
     ` -. -. A. x e. ~P 1o DECID x = 1o ` because the converse of ~ nnral does
     not hold.

     Actually, ` -. -. EXMID ` is not provable in intuitionistic logic since
     intuitionistic logic has models satisfying ` -. EXMID ` and
     noncontradiction holds ( ~ pm3.24 ).  (Contributed by BJ, 9-Oct-2019.)
     Add explanation on non-provability of ` -. -. EXMID ` .  (Revised by BJ,
     11-Aug-2024.) $)
  nndc $p |- -. -. DECID ph $=
    ( wdc wn wo nnexmid df-dc notbii mtbir ) ABZCAACDZCAEIJAFGH $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Theorems of decidable propositions
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  Many theorems of logic hold in intuitionistic logic just as they do in
  classical (non-intuitionistic) logic, for all propositions.  Other theorems
  only hold for decidable propositions, such as the law of the excluded middle
  ( ~ df-dc ), double negation elimination ( ~ notnotrdc ), or contraposition
  ( ~ condc ).  Our goal is to prove all well-known or important classical
  theorems, but with suitable decidability conditions so that the proofs follow
  from intuitionistic axioms.  This section is focused on such proofs, given
  decidability conditions.

  Many theorems of this section actually hold for stable propositions (see
  ~ df-stab ).  Decidable propositions are stable ( ~ dcstab ), but the
  converse need not hold.

$)

  $( Contraposition when the antecedent is a negated stable proposition.  See
     comment of ~ condc .  (Contributed by BJ, 18-Nov-2023.)  (Proof shortened
     by BJ, 11-Nov-2024.) $)
  const $p |- ( STAB ph -> ( ( -. ph -> -. ps ) -> ( ps -> ph ) ) ) $=
    ( wn wi wstab con2 df-stab biimpi syl9r ) ACZBCDBJCZAEZAJBFLKADAGHI $.

  $( Contraposition of a decidable proposition.

     This theorem swaps or "transposes" the order of the consequents when
     negation is removed.  An informal example is that the statement "if there
     are no clouds in the sky, it is not raining" implies the statement "if it
     is raining, there are clouds in the sky".  This theorem (without the
     decidability condition, of course) is called _Transp_ or "the principle of
     transposition" in _Principia Mathematica_ (Theorem *2.17 of
     [WhiteheadRussell] p. 103) and is Axiom A3 of [Margaris] p. 49.  We will
     also use the term "contraposition" for this principle, although the reader
     is advised that in the field of philosophical logic, "contraposition" has
     a different technical meaning.

     (Contributed by Jim Kingdon, 13-Mar-2018.)  (Proof shortened by BJ,
     18-Nov-2023.) $)
  condc $p |- ( DECID ph -> ( ( -. ph -> -. ps ) -> ( ps -> ph ) ) ) $=
    ( wdc wstab wn wi dcstab const syl ) ACADAEBEFBAFFAGABHI $.

  $( Obsolete proof of ~ condc as of 18-Nov-2023.  (Contributed by Jim Kingdon,
     13-Mar-2018.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  condcOLD $p |- ( DECID ph -> ( ( -. ph -> -. ps ) -> ( ps -> ph ) ) ) $=
    ( wdc wn wo wi df-dc ax-1 a1d pm2.27 ax-in2 syl6 jaoi sylbi ) ACAADZEOBDZFZ
    BAFZFZAGASOARQABHIOQPROPJBAKLMN $.

  $( Proof by contradiction for a decidable proposition.  Based on Theorem
     *2.18 of [WhiteheadRussell] p. 103 (also called Clavius law).
     Intuitionistically it requires a decidability assumption, but compare with
     ~ pm2.01 which does not.  (Contributed by Jim Kingdon, 24-Mar-2018.) $)
  pm2.18dc $p |- ( DECID ph -> ( ( -. ph -> ph ) -> ph ) ) $=
    ( wdc wn wi pm2.21 a2i condc syl5 pm2.43d ) ABZACZADZALKLCZDJLADKAMAMEFALGH
    I $.

  $( Contraposition for a decidable proposition.  Based on theorem *2.15 of
     [WhiteheadRussell] p. 102.  (Contributed by Jim Kingdon, 29-Mar-2018.) $)
  con1dc $p |- ( DECID ph -> ( ( -. ph -> ps ) -> ( -. ps -> ph ) ) ) $=
    ( wn wi wdc notnot imim2i condc syl5 ) ACZBDJBCZCZDAEKADBLJBFGAKHI $.

  ${
    con4biddc.1 $e |- ( ph -> ( DECID ps -> ( DECID ch ->
        ( -. ps <-> -. ch ) ) ) ) $.
    $( A contraposition deduction.  (Contributed by Jim Kingdon,
       18-May-2018.) $)
    con4biddc $p |- ( ph -> ( DECID ps -> ( DECID ch -> ( ps <-> ch ) ) ) ) $=
      ( wdc wb wa wi wn biimpr syl8 condc syl6 imp31 biimp imim2d sylcom impbid
      a2i exp31 ) ABEZCEZBCFAUAGUBGBCAUAUBBCHZAUAUBCIZBIZHZHUBUCHAUAUBUEUDFZUFD
      UEUDJKUBUFUCCBLSMNAUAUBCBHZAUAUBUEUDHZHUBUHHAUAUBUGUIDUEUDOKUAUIUHUBBCLPQ
      NRT $.
  $}

  ${
    impidc.1 $e |- ( DECID ch -> ( ph -> ( ps -> ch ) ) ) $.
    $( An importation inference for a decidable consequent.  (Contributed by
       Jim Kingdon, 30-Apr-2018.) $)
    impidc $p |- ( DECID ch -> ( -. ( ph -> -. ps ) -> ch ) ) $=
      ( wdc wn wi wa imp con3d ex com23 con1dc mpd ) CEZCFZABFZGZGRFCGOAPQOAPQG
      OAHBCOABCGDIJKLCRMN $.
  $}

  $( Simplification given a decidable proposition.  Similar to Theorem *3.27
     (Simp) of [WhiteheadRussell] p. 112.  (Contributed by Jim Kingdon,
     30-Apr-2018.) $)
  simprimdc $p |- ( DECID ps -> ( -. ( ph -> -. ps ) -> ps ) ) $=
    ( wi wdc idd a1i impidc ) ABBABBCCBDABEFG $.

  $( Simplification for a decidable proposition.  Similar to Theorem *3.26
     (Simp) of [WhiteheadRussell] p. 112.  (Contributed by Jim Kingdon,
     29-Mar-2018.) $)
  simplimdc $p |- ( DECID ph -> ( -. ( ph -> ps ) -> ph ) ) $=
    ( wdc wn wi pm2.21 con1dc mpi ) ACADABEZEIDAEABFAIGH $.

  ${
    pm2.61ddc.1 $e |- ( ph -> ( ps -> ch ) ) $.
    pm2.61ddc.2 $e |- ( ph -> ( -. ps -> ch ) ) $.
    $( Deduction eliminating a decidable antecedent.  (Contributed by Jim
       Kingdon, 4-May-2018.) $)
    pm2.61ddc $p |- ( DECID ps -> ( ph -> ch ) ) $=
      ( wdc wn wo wi df-dc com12 jaoi sylbi ) BFBBGZHACIZBJBONABCDKANCEKLM $.
  $}

  $( Case elimination for a decidable proposition.  Based on theorem *2.6 of
     [WhiteheadRussell] p. 107.  (Contributed by Jim Kingdon, 25-Mar-2018.) $)
  pm2.6dc $p |- ( DECID ph ->
      ( ( -. ph -> ps ) -> ( ( ph -> ps ) -> ps ) ) ) $=
    ( wdc wn wi wo wa pm2.1dc pm3.44 syl5com expd ) ACZADZBEZABEZBLMAFNOGBAHBMA
    IJK $.

  ${
    jadc.1 $e |- ( DECID ph -> ( -. ph -> ch ) ) $.
    jadc.2 $e |- ( ps -> ch ) $.
    $( Inference forming an implication from the antecedents of two premises,
       where a decidable antecedent is negated.  (Contributed by Jim Kingdon,
       25-Mar-2018.) $)
    jadc $p |- ( DECID ph -> ( ( ph -> ps ) -> ch ) ) $=
      ( wi wdc imim2i wn pm2.6dc mpd syl5 ) ABFACFZAGZCBCAEHNAICFMCFDACJKL $.
  $}

  ${
    jaddc.1 $e |- ( ph -> ( DECID ps -> ( -. ps -> th ) ) ) $.
    jaddc.2 $e |- ( ph -> ( ch -> th ) ) $.
    $( Deduction forming an implication from the antecedents of two premises,
       where a decidable antecedent is negated.  (Contributed by Jim Kingdon,
       26-Mar-2018.) $)
    jaddc $p |- ( ph -> ( DECID ps -> ( ( ps -> ch ) -> th ) ) ) $=
      ( wi wdc imim2d wn pm2.6dc sylcom syl5d ) ABCGBDGZBHZDACDBFIAOBJDGNDGEBDK
      LM $.
  $}

  $( Case elimination for a decidable proposition.  Theorem *2.61 of
     [WhiteheadRussell] p. 107 under a decidability condition.  (Contributed by
     Jim Kingdon, 29-Mar-2018.) $)
  pm2.61dc $p |- ( DECID ph ->
                   ( ( ph -> ps ) -> ( ( -. ph -> ps ) -> ps ) ) ) $=
    ( wdc wn wi pm2.6dc com23 ) ACADBEABEBABFG $.

  $( Negating an implication for a decidable antecedent.  General instance of
     Theorem *2.5 of [WhiteheadRussell] p. 107 under a decidability condition.
     (Contributed by Jim Kingdon, 29-Mar-2018.) $)
  pm2.5gdc $p |- ( DECID ph -> ( -. ( ph -> ps ) -> ( -. ph -> ch ) ) ) $=
    ( wdc wi wn wa simplimdc imp pm2.24d ex ) ADZABEFZAFCELMGACLMAABHIJK $.

  $( Negating an implication for a decidable antecedent.  Theorem *2.5 of
     [WhiteheadRussell] p. 107 under a decidability condition.  (Contributed by
     Jim Kingdon, 29-Mar-2018.) $)
  pm2.5dc $p |- ( DECID ph -> ( -. ( ph -> ps ) -> ( -. ph -> ps ) ) ) $=
    ( pm2.5gdc ) ABBC $.

  $( A general instance of Theorem *2.521 of [WhiteheadRussell] p. 107, under a
     decidability condition.  (Contributed by BJ, 28-Oct-2023.) $)
  pm2.521gdc $p |- ( DECID ph -> ( -. ( ph -> ps ) -> ( ch -> ph ) ) ) $=
    ( wdc wi wn pm2.5gdc condc syld ) ADABEFAFCFZECAEABJGACHI $.

  $( Theorem *2.521 of [WhiteheadRussell] p. 107, but with an additional
     decidability condition.  Note that by replacing in proof ~ pm2.52 with
     ~ conax1k , we obtain a proof of the more general instance where the last
     occurrence of ` ph ` is replaced with any ` ch ` .  (Contributed by Jim
     Kingdon, 5-May-2018.) $)
  pm2.521dc $p |- ( DECID ph -> ( -. ( ph -> ps ) -> ( ps -> ph ) ) ) $=
    ( pm2.521gdc ) ABBC $.

  $( Alternate proof of ~ pm2.521dc .  (Contributed by Jim Kingdon,
     5-May-2018.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  pm2.521dcALT $p |- ( DECID ph -> ( -. ( ph -> ps ) -> ( ps -> ph ) ) ) $=
    ( wi wn wdc pm2.52 condc syl5 ) ABCDADBDCAEBACABFABGH $.

  $( Contraposition.  Theorem *4.1 of [WhiteheadRussell] p. 116, but for a
     decidable proposition.  (Contributed by Jim Kingdon, 24-Apr-2018.) $)
  con34bdc $p |- ( DECID ps -> ( ( ph -> ps ) <-> ( -. ps -> -. ph ) ) ) $=
    ( wdc wi wn con3 condc impbid2 ) BCABDBEAEDABFBAGH $.

  $( Double negation equivalence for a decidable proposition.  Like Theorem
     *4.13 of [WhiteheadRussell] p. 117, but with a decidability antecendent.
     The forward direction, ~ notnot , holds for all propositions, not just
     decidable ones.  (Contributed by Jim Kingdon, 13-Mar-2018.) $)
  notnotbdc $p |- ( DECID ph -> ( ph <-> -. -. ph ) ) $=
    ( wdc wn notnot notnotrdc impbid2 ) ABAACCADAEF $.

  $( Contraposition.  (Contributed by Jim Kingdon, 4-Apr-2018.) $)
  con1biimdc $p |- ( DECID ph -> ( ( -. ph <-> ps ) -> ( -. ps <-> ph ) ) ) $=
    ( wdc wn wb wi biimp con1dc syl5 biimpr con2d a1i impbidd ) ACZADZBEZBDZAPO
    BFNQAFOBGABHIPAQFFNPBAOBJKLM $.

  $( Contraposition.  (Contributed by Jim Kingdon, 17-Apr-2018.) $)
  con1bidc $p |- ( DECID ph -> ( DECID ps ->
      ( ( -. ph <-> ps ) <-> ( -. ps <-> ph ) ) ) ) $=
    ( wdc wn wb wa wi con1biimdc adantr adantl impbid ex ) ACZBCZADBEZBDAEZEMNF
    OPMOPGNABHINPOGMBAHJKL $.

  $( Contraposition.  (Contributed by Jim Kingdon, 17-Apr-2018.) $)
  con2bidc $p |- ( DECID ph -> ( DECID ps ->
      ( ( ph <-> -. ps ) <-> ( ps <-> -. ph ) ) ) ) $=
    ( wdc wn wb wa con1bidc imp bicom 3bitr3g bicomd ex ) ACZBCZABDZEZBADZEZEMN
    FZRPSQBEZOAEZRPMNTUAEABGHQBIOAIJKL $.

  ${
    con1biddc.1 $e |- ( ph -> ( DECID ps -> ( -. ps <-> ch ) ) ) $.
    $( A contraposition deduction.  (Contributed by Jim Kingdon,
       4-Apr-2018.) $)
    con1biddc $p |- ( ph -> ( DECID ps -> ( -. ch <-> ps ) ) ) $=
      ( wdc wn wb con1biimdc sylcom ) ABEBFCGCFBGDBCHI $.
  $}

  ${
    con1biidc.1 $e |- ( DECID ph -> ( -. ph <-> ps ) ) $.
    $( A contraposition inference.  (Contributed by Jim Kingdon,
       15-Mar-2018.) $)
    con1biidc $p |- ( DECID ph -> ( -. ps <-> ph ) ) $=
      ( wdc wn notnotbdc notbid bitrd bicomd ) ADZABEZJAAEZEKAFJLBCGHI $.
  $}

  $( Contraposition.  Bidirectional version of ~ con1dc .  (Contributed by NM,
     5-Aug-1993.) $)
  con1bdc $p |- ( DECID ph -> ( DECID ps ->
                  ( ( -. ph -> ps ) <-> ( -. ps -> ph ) ) ) ) $=
    ( wdc wn wi wb wa con1dc adantr adantl impbid ex ) ACZBCZADBEZBDAEZFMNGOPMO
    PENABHINPOEMBAHJKL $.

  ${
    con2biidc.1 $e |- ( DECID ps -> ( ph <-> -. ps ) ) $.
    $( A contraposition inference.  (Contributed by Jim Kingdon,
       15-Mar-2018.) $)
    con2biidc $p |- ( DECID ps -> ( ps <-> -. ph ) ) $=
      ( wdc wn bicomd con1biidc ) BDZAEBBAHABECFGF $.
  $}

  ${
    con2biddc.1 $e |- ( ph -> ( DECID ch -> ( ps <-> -. ch ) ) ) $.
    $( A contraposition deduction.  (Contributed by Jim Kingdon,
       11-Apr-2018.) $)
    con2biddc $p |- ( ph -> ( DECID ch -> ( ch <-> -. ps ) ) ) $=
      ( wdc wn wb bicom imbitrdi con1biddc ) ACEZBFZCGCLGACBAKBCFZGMBGDBMHIJLCH
      I $.
  $}

  ${
    condandc.1 $e |- ( ( ph /\ -. ps ) -> ch ) $.
    condandc.2 $e |- ( ( ph /\ -. ps ) -> -. ch ) $.
    $( Proof by contradiction.  This only holds for decidable propositions, as
       it is part of the family of theorems which assume ` -. ps ` , derive a
       contradiction, and therefore conclude ` ps ` .  By contrast, assuming
       ` ps ` , deriving a contradiction, and therefore concluding ` -. ps ` ,
       as in ~ pm2.65 , is valid for all propositions.  (Contributed by Jim
       Kingdon, 13-May-2018.) $)
    condandc $p |- ( DECID ps -> ( ph -> ps ) ) $=
      ( wn wdc pm2.65da notnotrdc syl5 ) ABFZFBGBAKCDEHBIJ $.
  $}

  ${
    bijadc.1 $e |- ( ph -> ( ps -> ch ) ) $.
    bijadc.2 $e |- ( -. ph -> ( -. ps -> ch ) ) $.
    $( Combine antecedents into a single biconditional.  This inference is
       reminiscent of ~ jadc .  (Contributed by Jim Kingdon, 4-May-2018.) $)
    bijadc $p |- ( DECID ps -> ( ( ph <-> ps ) -> ch ) ) $=
      ( wb biimpr syli wn biimp con3d pm2.61ddc ) ABFZBCBMACABGDHBIMAICMABABJKE
      HL $.
  $}

  $( Relationship between an equivalence and an equivalence with some negation,
     for decidable propositions.  Based on theorem *5.18 of [WhiteheadRussell]
     p. 124.  Given decidability, we can consider ` -. ( ph <-> -. ps ) ` to
     represent "negated exclusive-or".  (Contributed by Jim Kingdon,
     4-Apr-2018.) $)
  pm5.18dc $p |- ( DECID ph -> ( DECID ps ->
        ( ( ph <-> ps ) <-> -. ( ph <-> -. ps ) ) ) ) $=
    ( wdc wn wo wb wi df-dc wa pm5.501 a1d con1biddc imp adantr bitr2d dcn nbn2
    ex syl5 jaoi sylbi ) ACAADZEBCZABFZABDZFZDZFZGZAHAUIUBAUCUHAUCIUGBUDAUCUGBF
    ABUFAUEUFFUCAUEJKLMABUDFUCABJNORUBUCUHUBUCIUGUEUDUBUCUGUEFZUCUECZUBUJBPUBUE
    UFUBUEDUFFUKAUEQKLSMUBUEUDFUCABQNORTUA $.

  $( Definition of 'and' in terms of negation and implication, for decidable
     propositions.  The forward direction holds for all propositions, and can
     (basically) be found at ~ pm3.2im .  (Contributed by Jim Kingdon,
     30-Apr-2018.) $)
  dfandc $p |- ( DECID ph -> ( DECID ps ->
      ( ( ph /\ ps ) <-> -. ( ph -> -. ps ) ) ) ) $=
    ( wdc wa wn wi wb pm3.2im imp simplimdc adantr simprimdc adantl jca impbid2
    ex ) ACZBCZABDZABEZFEZGQRDZSUAABUAABHIUBUASUBUADABUBUAAQUAAFRATJKIUBUABRUAB
    FQABLMINPOP $.

  $( A decidable proposition or its triple negation is true.  Theorem *2.13 of
     [WhiteheadRussell] p. 101 with decidability condition added.  (Contributed
     by Jim Kingdon, 13-May-2018.) $)
  pm2.13dc $p |- ( DECID ph -> ( ph \/ -. -. -. ph ) ) $=
    ( wdc wn wo df-dc notnotrdc con3d orim2d biimtrid pm2.43i ) ABZAACZCZCZDZKA
    LDKOAEKLNAKMAAFGHIJ $.

  $( Theorem *4.63 of [WhiteheadRussell] p. 120, for decidable propositions.
     (Contributed by Jim Kingdon, 1-May-2018.) $)
  pm4.63dc $p |- ( DECID ph -> ( DECID ps ->
      ( -. ( ph -> -. ps ) <-> ( ph /\ ps ) ) ) ) $=
    ( wdc wn wi wa wb dfandc imp bicomd ex ) ACZBCZABDEDZABFZGLMFONLMONGABHIJK
    $.

  $( Theorem *4.67 of [WhiteheadRussell] p. 120, for decidable propositions.
     (Contributed by Jim Kingdon, 1-May-2018.) $)
  pm4.67dc $p |- ( DECID ph -> ( DECID ps ->
      ( -. ( -. ph -> -. ps ) <-> ( -. ph /\ ps ) ) ) ) $=
    ( wdc wn wi wa wb dcn pm4.63dc syl ) ACADZCBCKBDEDKBFGEAHKBIJ $.

  $( Express implication in terms of conjunction.  Theorem 3.4(27) of [Stoll]
     p. 176.  (Contributed by NM, 12-Mar-1993.)  (Proof shortened by Wolf
     Lammen, 30-Oct-2012.) $)
  imanst $p |- ( STAB ps -> ( ( ph -> ps ) <-> -. ( ph /\ -. ps ) ) ) $=
    ( wstab wi wn wa notnot df-stab biimpi impbid2 imbi2d imnan bitrdi ) BCZABD
    ABEZEZDAOFENBPANBPBGNPBDBHIJKAOLM $.

  $( Express implication in terms of conjunction.  Theorem 3.4(27) of [Stoll]
     p. 176, with an added decidability condition.  The forward direction,
     ~ imanim , holds for all propositions, not just decidable ones.
     (Contributed by Jim Kingdon, 25-Apr-2018.) $)
  imandc $p |- ( DECID ps -> ( ( ph -> ps ) <-> -. ( ph /\ -. ps ) ) ) $=
    ( wdc wstab wi wn wa wb dcstab imanst syl ) BCBDABEABFGFHBIABJK $.

  $( Theorem *4.14 of [WhiteheadRussell] p. 117, given a decidability
     condition.  (Contributed by Jim Kingdon, 24-Apr-2018.) $)
  pm4.14dc $p |- ( DECID ch ->
      ( ( ( ph /\ ps ) -> ch ) <-> ( ( ph /\ -. ch ) -> -. ps ) ) ) $=
    ( wdc wi wn wa con34bdc imbi2d impexp 3bitr4g ) CDZABCEZEACFZBFZEZEABGCEANG
    OELMPABCHIABCJANOJK $.

  $( Deriving disjunction from implication for a decidable proposition.  Based
     on theorem *2.54 of [WhiteheadRussell] p. 107.  The converse, ~ pm2.53 ,
     holds whether the proposition is decidable or not.  (Contributed by Jim
     Kingdon, 26-Mar-2018.) $)
  pm2.54dc $p |- ( DECID ph -> ( ( -. ph -> ps ) -> ( ph \/ ps ) ) ) $=
    ( wdc wn wi wo dcn notnotrdc orc syl6 a1d olc a1i jaddc mpd ) ACZADZCZQBEAB
    FZEAGPQBSPQDZSERPTASAHABIJKBSEPBALMNO $.

  $( Definition of disjunction in terms of negation and implication for a
     decidable proposition.  Based on definition of [Margaris] p. 49.  One
     direction, ~ pm2.53 , holds for all propositions, not just decidable ones.
     (Contributed by Jim Kingdon, 26-Mar-2018.) $)
  dfordc $p |- ( DECID ph -> ( ( ph \/ ps ) <-> ( -. ph -> ps ) ) ) $=
    ( wdc wo wn wi pm2.53 pm2.54dc impbid2 ) ACABDAEBFABGABHI $.

  $( Elimination of disjunction based on a disjunction, for a decidable
     proposition.  Based on theorem *2.25 of [WhiteheadRussell] p. 104.
     (Contributed by NM, 3-Jan-2005.) $)
  pm2.25dc $p |- ( DECID ph -> ( ph \/ ( ( ph \/ ps ) -> ps ) ) ) $=
    ( wdc wn wo wi df-dc orel1 orim2i sylbi ) ACAADZEAABEBFZEAGKLAABHIJ $.

  $( Concluding disjunction from implication for a decidable proposition.
     Based on theorem *2.68 of [WhiteheadRussell] p. 108.  Converse of ~ pm2.62
     and one half of ~ dfor2dc .  (Contributed by Jim Kingdon, 27-Mar-2018.) $)
  pm2.68dc $p |- ( DECID ph -> ( ( ( ph -> ps ) -> ps ) -> ( ph \/ ps ) ) ) $=
    ( wi wn wdc wo jarl pm2.54dc syl5 ) ABCBCADBCAEABFABBGABHI $.

  $( Disjunction expressed in terms of implication only, for a decidable
     proposition.  Based on theorem *5.25 of [WhiteheadRussell] p. 124.
     (Contributed by Jim Kingdon, 27-Mar-2018.) $)
  dfor2dc $p |- ( DECID ph -> ( ( ph \/ ps ) <-> ( ( ph -> ps ) -> ps ) ) ) $=
    ( wdc wo wi pm2.62 pm2.68dc impbid2 ) ACABDABEBEABFABGH $.

  $( Simplify an implication between implications, for a decidable proposition.
     (Contributed by Jim Kingdon, 18-Mar-2018.) $)
  imimorbdc $p |- ( DECID ps -> ( ( ( ps -> ch ) -> ( ph -> ch ) ) <->
                  ( ph -> ( ps \/ ch ) ) ) ) $=
    ( wdc wi wo bi2.04 dfor2dc imbi2d bitr4id ) BDZBCEZACEEALCEZEABCFZELACGKNMA
    BCHIJ $.

  $( Implication in terms of disjunction for a decidable proposition.  Based on
     theorem *4.6 of [WhiteheadRussell] p. 120.  The reverse direction,
     ~ imorr , holds for all propositions.  (Contributed by Jim Kingdon,
     20-Apr-2018.) $)
  imordc $p |- ( DECID ph -> ( ( ph -> ps ) <-> ( -. ph \/ ps ) ) ) $=
    ( wdc wi wn wo notnotbdc imbi1d wb dcn dfordc syl bitr4d ) ACZABDAEZEZBDZOB
    FZNAPBAGHNOCRQIAJOBKLM $.

  $( Implication in terms of disjunction.  Like Theorem *4.62 of
     [WhiteheadRussell] p. 120, but for a decidable antecedent.  (Contributed
     by Jim Kingdon, 21-Apr-2018.) $)
  pm4.62dc $p |- ( DECID ph -> ( ( ph -> -. ps ) <-> ( -. ph \/ -. ps ) ) ) $=
    ( wn imordc ) ABCD $.

  $( Negated conjunction in terms of disjunction (DeMorgan's law).  Theorem
     *4.51 of [WhiteheadRussell] p. 120, but where one proposition is
     decidable.  The reverse direction, ~ pm3.14 , holds for all propositions,
     but the equivalence only holds where one proposition is decidable.
     (Contributed by Jim Kingdon, 21-Apr-2018.) $)
  ianordc $p |- ( DECID ph -> ( -. ( ph /\ ps ) <-> ( -. ph \/ -. ps ) ) ) $=
    ( wa wn wi wdc wo imnan pm4.62dc bitr3id ) ABCDABDZEAFADKGABHABIJ $.

  $( Theorem *4.64 of [WhiteheadRussell] p. 120, given a decidability
     condition.  The reverse direction, ~ pm2.53 , holds for all propositions.
     (Contributed by Jim Kingdon, 2-May-2018.) $)
  pm4.64dc $p |- ( DECID ph -> ( ( -. ph -> ps ) <-> ( ph \/ ps ) ) ) $=
    ( wdc wo wn wi dfordc bicomd ) ACABDAEBFABGH $.

  $( Theorem *4.66 of [WhiteheadRussell] p. 120, given a decidability
     condition.  (Contributed by Jim Kingdon, 2-May-2018.) $)
  pm4.66dc $p |- ( DECID ph -> ( ( -. ph -> -. ps ) <-> ( ph \/ -. ps ) ) ) $=
    ( wn pm4.64dc ) ABCD $.

  $( Theorem *4.54 of [WhiteheadRussell] p. 120, for decidable propositions.
     One form of DeMorgan's law.  (Contributed by Jim Kingdon, 2-May-2018.) $)
  pm4.54dc $p |- ( DECID ph -> ( DECID ps ->
      ( ( -. ph /\ ps ) <-> -. ( ph \/ -. ps ) ) ) ) $=
    ( wdc wn wa wo wb wi dcn dfandc syl imp pm4.66dc adantr notbid bitrd ex ) A
    CZBCZADZBEZABDZFZDZGRSEZUATUBHZDZUDRSUAUGGZRTCSUHHAITBJKLUEUFUCRUFUCGSABMNO
    PQ $.

  $( Equivalence between a disjunction of two implications, and a conjunction
     and an implication.  Based on theorem *4.79 of [WhiteheadRussell] p. 121
     but with additional decidability antecedents.  (Contributed by Jim
     Kingdon, 28-Mar-2018.) $)
  pm4.79dc $p |- ( DECID ph -> ( DECID ps ->
                 ( ( ( ps -> ph ) \/ ( ch -> ph ) ) <->
                   ( ( ps /\ ch ) -> ph ) ) ) ) $=
    ( wdc wi wo wa wb id jaoa simplimdc pm3.3 syl9 dcim pm2.54dc syl6 syl5d imp
    wn impbid2 expcom ) BDZADZBAEZCAEZFZBCGAEZHUBUCGUFUGUDBAUECUDIUEIJUBUCUGUFE
    UBUGUDSZUEEZUCUFUBUHBUGUEBAKBCALMUBUCUDDUIUFEBANUDUEOPQRTUA $.

  $( Two ways of stating exclusive-or which are equivalent for a decidable
     proposition.  Based on theorem *5.17 of [WhiteheadRussell] p. 124.
     (Contributed by Jim Kingdon, 16-Apr-2018.) $)
  pm5.17dc $p |- ( DECID ps ->
      ( ( ( ph \/ ps ) /\ -. ( ph /\ ps ) ) <-> ( ph <-> -. ps ) ) ) $=
    ( wn wb wdc wo wa bicom dfbi2 orcom dfordc bitr2id imnan a1i anbi12d bitrid
    wi ) ABCZDRADZBEZABFZABGCZGZARHSRAQZARQZGTUCRAITUDUAUEUBUABAFTUDABJBAKLUEUB
    DTABMNOPL $.

  $( Reverse distribution of disjunction over implication, given decidability.
     Based on theorem *2.85 of [WhiteheadRussell] p. 108.  (Contributed by Jim
     Kingdon, 1-Apr-2018.) $)
  pm2.85dc $p |- ( DECID ph -> ( ( ( ph \/ ps ) -> ( ph \/ ch ) ) ->
                ( ph \/ ( ps -> ch ) ) ) ) $=
    ( wdc wn wo wi df-dc orc a1d olc imim1i orel1 syl9r syl6 jaoi sylbi ) ADAAE
    ZFABFZACFZGZABCGZFZGZAHAUDRAUCUAAUBIJRUAUBUCUABTRCBSTBAKLACMNUBAKOPQ $.

  $( Disjunction distributes over implication.  The forward direction,
     ~ pm2.76 , is valid intuitionistically.  The reverse direction holds if
     ` ph ` is decidable, as can be seen at ~ pm2.85dc .  (Contributed by Jim
     Kingdon, 1-Apr-2018.) $)
  orimdidc $p |- ( DECID ph -> ( ( ph \/ ( ps -> ch ) ) <->
                ( ( ph \/ ps ) -> ( ph \/ ch ) ) ) ) $=
    ( wdc wi wo pm2.76 pm2.85dc impbid2 ) ADABCEFABFACFEABCGABCHI $.

  $( Decidable proposition version of theorem *2.26 of [WhiteheadRussell]
     p. 104.  (Contributed by Jim Kingdon, 20-Apr-2018.) $)
  pm2.26dc $p |- ( DECID ph -> ( -. ph \/ ( ( ph -> ps ) -> ps ) ) ) $=
    ( wdc wi wn wo pm2.27 imordc mpbii ) ACAABDBDZDAEJFABGAJHI $.

  $( Theorem *4.81 of [WhiteheadRussell] p. 122, for decidable propositions.
     This one needs a decidability condition, but compare with ~ pm4.8 which
     holds for all propositions.  (Contributed by Jim Kingdon, 4-Jul-2018.) $)
  pm4.81dc $p |- ( DECID ph -> ( ( -. ph -> ph ) <-> ph ) ) $=
    ( wdc wn wi pm2.18dc pm2.24 impbid1 ) ABACADAAEAAFG $.

  $( A decidable proposition or its negation implies a second proposition.
     Based on theorem *5.11 of [WhiteheadRussell] p. 123.  (Contributed by Jim
     Kingdon, 29-Mar-2018.) $)
  pm5.11dc $p |- ( DECID ph -> ( DECID ps ->
                   ( ( ph -> ps ) \/ ( -. ph -> ps ) ) ) ) $=
    ( wdc wi wn wo dcim pm2.5dc pm2.54dc syl5com syld ) ACZBCABDZCZMAEBDZFZABGL
    MEODNPABHMOIJK $.

  $( Excluded middle with antecedents for a decidable consequent.  Based on
     theorem *5.12 of [WhiteheadRussell] p. 123.  (Contributed by Jim Kingdon,
     30-Mar-2018.) $)
  pm5.12dc $p |- ( DECID ps -> ( ( ph -> ps ) \/ ( ph -> -. ps ) ) ) $=
    ( wdc wn wo wi df-dc ax-1 orim12i sylbi ) BCBBDZEABFZAKFZEBGBLKMBAHKAHIJ $.

  $( A decidable proposition is implied by or implies other propositions.
     Based on theorem *5.14 of [WhiteheadRussell] p. 123.  (Contributed by Jim
     Kingdon, 30-Mar-2018.) $)
  pm5.14dc $p |- ( DECID ps -> ( ( ph -> ps ) \/ ( ps -> ch ) ) ) $=
    ( wdc wn wo wi df-dc ax-1 ax-in2 orim12i sylbi ) BDBBEZFABGZBCGZFBHBNMOBAIB
    CJKL $.

  $( An implication holds in at least one direction, where one proposition is
     decidable.  Based on theorem *5.13 of [WhiteheadRussell] p. 123.
     (Contributed by Jim Kingdon, 30-Mar-2018.) $)
  pm5.13dc $p |- ( DECID ps -> ( ( ph -> ps ) \/ ( ps -> ph ) ) ) $=
    ( pm5.14dc ) ABAC $.

  $( A disjunction is equivalent to one of its disjuncts, given a decidable
     disjunct.  Based on theorem *5.55 of [WhiteheadRussell] p. 125.
     (Contributed by Jim Kingdon, 30-Mar-2018.) $)
  pm5.55dc $p |- ( DECID ph ->
        ( ( ( ph \/ ps ) <-> ph ) \/ ( ( ph \/ ps ) <-> ps ) ) ) $=
    ( wdc wn wo wb df-dc biort bicomd biorf orim12i sylbi ) ACAADZEABEZAFZNBFZE
    AGAOMPAANABHIMBNABJIKL $.

  $( Peirce's theorem for a decidable proposition.  This odd-looking theorem
     can be seen as an alternative to ~ exmiddc , ~ condc , or ~ notnotrdc in
     the sense of expressing the "difference" between an intuitionistic system
     of propositional calculus and a classical system.  In intuitionistic
     logic, it only holds for decidable propositions.  (Contributed by Jim
     Kingdon, 3-Jul-2018.) $)
  peircedc $p |- ( DECID ph -> ( ( ( ph -> ps ) -> ph ) -> ph ) ) $=
    ( wdc wn wo wi df-dc ax-1 pm2.21 imim1i com12 jaoi sylbi ) ACAADZEABFZAFZAF
    ZAGAQNAPHPNANOAABIJKLM $.

  $( The Inversion Axiom of the infinite-valued sentential logic (L-infinity)
     of Lukasiewicz, but where one of the propositions is decidable.  Using
     ~ dfor2dc , we can see that this expresses "disjunction is commutative".
     Theorem *2.69 of [WhiteheadRussell] p. 108 (plus the decidability
     condition).  (Contributed by NM, 12-Aug-2004.) $)
  looinvdc $p |- ( DECID ph ->
      ( ( ( ph -> ps ) -> ps ) -> ( ( ps -> ph ) -> ph ) ) ) $=
    ( wi wdc imim1 peircedc syl9r ) ABCZBCBACHACADAHBAEABFG $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Miscellaneous theorems of propositional calculus
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    pm5.21nd.1 $e |- ( ( ph /\ ps ) -> th ) $.
    pm5.21nd.2 $e |- ( ( ph /\ ch ) -> th ) $.
    pm5.21nd.3 $e |- ( th -> ( ps <-> ch ) ) $.
    $( Eliminate an antecedent implied by each side of a biconditional.
       (Contributed by NM, 20-Nov-2005.)  (Proof shortened by Wolf Lammen,
       4-Nov-2013.) $)
    pm5.21nd $p |- ( ph -> ( ps <-> ch ) ) $=
      ( ex wb wi a1i pm5.21ndd ) ADBCABDEHACDFHDBCIJAGKL $.
  $}

  $( Theorem *5.35 of [WhiteheadRussell] p. 125.  (Contributed by NM,
     3-Jan-2005.) $)
  pm5.35 $p |- ( ( ( ph -> ps ) /\ ( ph -> ch ) ) ->
                ( ph -> ( ps <-> ch ) ) ) $=
    ( wi wa pm5.1 pm5.74rd ) ABDZACDZEABCHIFG $.

  $( A conjunction is equivalent to one of its conjuncts, given a decidable
     conjunct.  Based on theorem *5.54 of [WhiteheadRussell] p. 125.
     (Contributed by Jim Kingdon, 30-Mar-2018.) $)
  pm5.54dc $p |- ( DECID ph ->
                   ( ( ( ph /\ ps ) <-> ph ) \/ ( ( ph /\ ps ) <-> ps ) ) ) $=
    ( wdc wa wb wn df-dc simpr ax-ia3 impbid2 simpl ax-in2 orim12i sylbi orcomd
    wo ) ACZABDZBEZRAEZQAAFZPSTPAGASUATARBABHABIJUARAABKARLJMNO $.

  ${
    baib.1 $e |- ( ph <-> ( ps /\ ch ) ) $.
    $( Move conjunction outside of biconditional.  (Contributed by NM,
       13-May-1999.) $)
    baib $p |- ( ps -> ( ph <-> ch ) ) $=
      ( wa ibar bitr4id ) BABCECDBCFG $.

    $( Move conjunction outside of biconditional.  (Contributed by NM,
       11-Jul-1994.) $)
    baibr $p |- ( ps -> ( ch <-> ph ) ) $=
      ( baib bicomd ) BACABCDEF $.

    $( Move conjunction outside of biconditional.  (Contributed by Mario
       Carneiro, 11-Sep-2015.) $)
    rbaib $p |- ( ch -> ( ph <-> ps ) ) $=
      ( wa ancom bitri baib ) ACBABCECBEDBCFGH $.

    $( Move conjunction outside of biconditional.  (Contributed by Mario
       Carneiro, 11-Sep-2015.) $)
    rbaibr $p |- ( ch -> ( ps <-> ph ) ) $=
      ( wa ancom bitri baibr ) ACBABCECBEDBCFGH $.
  $}

  ${
    baibd.1 $e |- ( ph -> ( ps <-> ( ch /\ th ) ) ) $.
    $( Move conjunction outside of biconditional.  (Contributed by Mario
       Carneiro, 11-Sep-2015.) $)
    baibd $p |- ( ( ph /\ ch ) -> ( ps <-> th ) ) $=
      ( wa ibar bicomd sylan9bb ) ABCDFZCDECDJCDGHI $.

    $( Move conjunction outside of biconditional.  (Contributed by Mario
       Carneiro, 11-Sep-2015.) $)
    rbaibd $p |- ( ( ph /\ th ) -> ( ps <-> ch ) ) $=
      ( wa iba bicomd sylan9bb ) ABCDFZDCEDCJDCGHI $.
  $}

  $( Theorem *5.44 of [WhiteheadRussell] p. 125.  (Contributed by NM,
     3-Jan-2005.) $)
  pm5.44 $p |- ( ( ph -> ps ) -> ( ( ph -> ch ) <->
                ( ph -> ( ps /\ ch ) ) ) ) $=
    ( wa wi jcab baibr ) ABCDEABEACEABCFG $.

  $( Conjunction in antecedent versus disjunction in consequent, for a
     decidable proposition.  Theorem *5.6 of [WhiteheadRussell] p. 125, with
     decidability condition added.  The reverse implication holds for all
     propositions (see ~ pm5.6r ).  (Contributed by Jim Kingdon,
     2-Apr-2018.) $)
  pm5.6dc $p |- ( DECID ps ->
        ( ( ( ph /\ -. ps ) -> ch ) <-> ( ph -> ( ps \/ ch ) ) ) ) $=
    ( wdc wn wa wi wo impexp dfordc imbi2d bitr4id ) BDZABEZFCGANCGZGABCHZGANCI
    MPOABCJKL $.

  $( Conjunction in antecedent versus disjunction in consequent.  One direction
     of Theorem *5.6 of [WhiteheadRussell] p. 125.  If ` ps ` is decidable, the
     converse also holds (see ~ pm5.6dc ).  (Contributed by Jim Kingdon,
     4-Aug-2018.) $)
  pm5.6r $p |- ( ( ph -> ( ps \/ ch ) ) -> ( ( ph /\ -. ps ) -> ch ) ) $=
    ( wo wi wn pm2.53 imim2i impd ) ABCDZEABFZCJKCEABCGHI $.

  ${
    orcanai.1 $e |- ( ph -> ( ps \/ ch ) ) $.
    $( Change disjunction in consequent to conjunction in antecedent.
       (Contributed by NM, 8-Jun-1994.) $)
    orcanai $p |- ( ( ph /\ -. ps ) -> ch ) $=
      ( wn ord imp ) ABECABCDFG $.
  $}

  ${
    intnan.1 $e |- -. ph $.
    $( Introduction of conjunct inside of a contradiction.  (Contributed by NM,
       16-Sep-1993.) $)
    intnan $p |- -. ( ps /\ ph ) $=
      ( wa simpr mto ) BADACBAEF $.

    $( Introduction of conjunct inside of a contradiction.  (Contributed by NM,
       3-Apr-1995.) $)
    intnanr $p |- -. ( ph /\ ps ) $=
      ( wa simpl mto ) ABDACABEF $.
  $}

  ${
    intnand.1 $e |- ( ph -> -. ps ) $.
    $( Introduction of conjunct inside of a contradiction.  (Contributed by NM,
       10-Jul-2005.) $)
    intnand $p |- ( ph -> -. ( ch /\ ps ) ) $=
      ( wa simpr nsyl ) ABCBEDCBFG $.

    $( Introduction of conjunct inside of a contradiction.  (Contributed by NM,
       10-Jul-2005.) $)
    intnanrd $p |- ( ph -> -. ( ps /\ ch ) ) $=
      ( wa simpl nsyl ) ABBCEDBCFG $.
  $}

  ${
    dcand.1 $e |- ( ph -> DECID ps ) $.
    dcand.2 $e |- ( ph -> DECID ch ) $.
    $( A conjunction of two decidable propositions is decidable.  (Contributed
       by Jim Kingdon, 12-Apr-2018.)  (Revised by BJ, 14-Nov-2024.) $)
    dcand $p |- ( ph -> DECID ( ps /\ ch ) ) $=
      ( wa wn wo wdc df-dc id intnanrd orim2i sylbi syl intnand sylanbrc sylibr
      ordir ) ABCFZTGZHZTIABUAHZCUAHZUBABIZUCDUEBBGZHUCBJUFUABUFBCUFKLMNOACIZUD
      EUGCCGZHUDCJUHUACUHCBUHKPMNOBCUASQTJR $.
  $}

  $( A conjunction of two decidable propositions is decidable.  (Contributed by
     Jim Kingdon, 12-Apr-2018.) $)
  dcan $p |- ( ( DECID ph /\ DECID ps ) -> DECID ( ph /\ ps ) ) $=
    ( wdc wa simpl simpr dcand ) ACZBCZDABHIEHIFG $.

  $( A conjunction of two decidable propositions is decidable, expressed in a
     curried form as compared to ~ dcan .  This is deprecated; it's trivial to
     recreate with ~ ex , but it's here in case someone is using this older
     form.  (Contributed by Jim Kingdon, 12-Apr-2018.)
     (New usage is discouraged.) $)
  dcan2 $p |- ( DECID ph -> ( DECID ps -> DECID ( ph /\ ps ) ) ) $=
    ( wdc wa dcan ex ) ACBCABDCABEF $.

  $( A disjunction of two decidable propositions is decidable.  (Contributed by
     Jim Kingdon, 21-Apr-2018.) $)
  dcor $p |- ( DECID ph -> ( DECID ps -> DECID ( ph \/ ps ) ) ) $=
    ( wdc wn wo wi df-dc orc orcd sylibr a1d wa olc adantl ioran biimpri jaodan
    olcd sylan2b ex jaoi sylbi ) ACAADZEBCZABEZCZFZAGAUGUCAUFUDAUEUEDZEZUFAUEUH
    ABHIUEGZJKUCUDUFUDUCBBDZEUFBGUCBUFUKUCBLZUIUFULUEUHBUEUCBAMNIUJJUCUKLZUIUFU
    MUHUEUHUMABOPRUJJQSTUAUB $.

  $( An equivalence of two decidable propositions is decidable.  (Contributed
     by Jim Kingdon, 12-Apr-2018.) $)
  dcbi $p |- ( DECID ph -> ( DECID ps -> DECID ( ph <-> ps ) ) ) $=
    ( wdc wi wa wb dcim com12 dcan ex syl6c dfbi2 dcbii imbitrrdi ) ACZBCZABDZB
    ADZEZCZABFZCOPQCZRCZTABGPOUCBAGHUBUCTQRIJKUASABLMN $.

  $( Express conjunction in terms of implication.  The forward direction,
     ~ annimim , is valid for all propositions, but as an equivalence, it
     requires a decidability condition.  (Contributed by Jim Kingdon,
     25-Apr-2018.) $)
  annimdc $p |- ( DECID ph -> ( DECID ps ->
      ( ( ph /\ -. ps ) <-> -. ( ph -> ps ) ) ) ) $=
    ( wdc wn wa wi wb imandc adantl dcim imp dcan sylan2 con2bidc sylc mpbid ex
    dcn ) ACZBCZABDZEZABFZDGZSTEZUCUBDGZUDTUFSABHIUEUCCZUBCZUFUDGSTUGABJKTSUACU
    HBRAUALMUCUBNOPQ $.

  $( Theorem *4.55 of [WhiteheadRussell] p. 120, for decidable propositions.
     (Contributed by Jim Kingdon, 2-May-2018.) $)
  pm4.55dc $p |- ( DECID ph -> ( DECID ps ->
      ( -. ( -. ph /\ ps ) <-> ( ph \/ -. ps ) ) ) ) $=
    ( wdc wn wa wo wb pm4.54dc imp dcor impel dcan sylan con2bidc sylc 3bitr2rd
    dcn mpbird ex ) ACZBCZADZBEZDZABDZFZGTUAEZUFUDUFUDUGUFUDGZUCUFDGZTUAUIABHIU
    GUFCZUCCZUHUIGTUECUJUAAUEJBQKTUBCUAUKAQUBBLMUFUCNORZULULPS $.

  $( Disjunction in terms of conjunction (De Morgan's law), for decidable
     propositions.  Compare Theorem *4.57 of [WhiteheadRussell] p. 120.
     (Contributed by Jim Kingdon, 13-Dec-2021.) $)
  orandc $p |- ( ( DECID ph /\ DECID ps ) ->
      ( ( ph \/ ps ) <-> -. ( -. ph /\ -. ps ) ) ) $=
    ( wdc wa wn wo wb pm4.56 dcn dcan syl2an dcor imp con2bidc sylc mpbii ) ACZ
    BCZDZAEZBEZDZABFZEGZUCUBEGZABHSUBCZUCCZUDUEGQTCUACUFRAIBITUAJKQRUGABLMUBUCN
    OP $.

  ${
    mpbiran.1 $e |- ps $.
    mpbiran.2 $e |- ( ph <-> ( ps /\ ch ) ) $.
    $( Detach truth from conjunction in biconditional.  (Contributed by NM,
       27-Feb-1996.)  (Revised by NM, 9-Jan-2015.) $)
    mpbiran $p |- ( ph <-> ch ) $=
      ( wa biantrur bitr4i ) ABCFCEBCDGH $.
  $}

  ${
    mpbiran2.1 $e |- ch $.
    mpbiran2.2 $e |- ( ph <-> ( ps /\ ch ) ) $.
    $( Detach truth from conjunction in biconditional.  (Contributed by NM,
       22-Feb-1996.)  (Revised by NM, 9-Jan-2015.) $)
    mpbiran2 $p |- ( ph <-> ps ) $=
      ( wa biantru bitr4i ) ABCFBECBDGH $.
  $}

  ${
    mpbir2an.1 $e |- ps $.
    mpbir2an.2 $e |- ch $.
    mpbiran2an.1 $e |- ( ph <-> ( ps /\ ch ) ) $.
    $( Detach a conjunction of truths in a biconditional.  (Contributed by NM,
       10-May-2005.)  (Revised by NM, 9-Jan-2015.) $)
    mpbir2an $p |- ph $=
      ( mpbiran mpbir ) ACEABCDFGH $.
  $}

  ${
    mpbi2and.1 $e |- ( ph -> ps ) $.
    mpbi2and.2 $e |- ( ph -> ch ) $.
    mpbi2and.3 $e |- ( ph -> ( ( ps /\ ch ) <-> th ) ) $.
    $( Detach a conjunction of truths in a biconditional.  (Contributed by NM,
       6-Nov-2011.)  (Proof shortened by Wolf Lammen, 24-Nov-2012.) $)
    mpbi2and $p |- ( ph -> th ) $=
      ( wa jca mpbid ) ABCHDABCEFIGJ $.
  $}

  ${
    mpbir2and.1 $e |- ( ph -> ch ) $.
    mpbir2and.2 $e |- ( ph -> th ) $.
    mpbir2and.3 $e |- ( ph -> ( ps <-> ( ch /\ th ) ) ) $.
    $( Detach a conjunction of truths in a biconditional.  (Contributed by NM,
       6-Nov-2011.)  (Proof shortened by Wolf Lammen, 24-Nov-2012.) $)
    mpbir2and $p |- ( ph -> ps ) $=
      ( wa jca mpbird ) ABCDHACDEFIGJ $.
  $}

  $( Theorem *5.62 of [WhiteheadRussell] p. 125, for a decidable proposition.
     (Contributed by Jim Kingdon, 12-May-2018.) $)
  pm5.62dc $p |- ( DECID ps ->
      ( ( ( ph /\ ps ) \/ -. ps ) <-> ( ph \/ -. ps ) ) ) $=
    ( wdc wn wo wa wb df-dc ordir simplbi simplbi2 com12 impbid2 sylbi ) BCBBDZ
    EZABFOEZAOEZGBHPQRQRPABOIZJRPQQRPSKLMN $.

  $( Theorem *5.63 of [WhiteheadRussell] p. 125, for a decidable proposition.
     (Contributed by Jim Kingdon, 12-May-2018.) $)
  pm5.63dc $p |- ( DECID ph ->
      ( ( ph \/ ps ) <-> ( ph \/ ( -. ph /\ ps ) ) ) ) $=
    ( wdc wo wn wa wi df-dc ordi simplbi2 sylbi simprbi impbid1 ) ACZABDZAAEZBF
    DZNAPDZOQGAHQROAPBIZJKQROSLM $.

  ${
    bianfi.1 $e |- -. ph $.
    $( A wff conjoined with falsehood is false.  (Contributed by NM,
       5-Aug-1993.)  (Proof shortened by Wolf Lammen, 26-Nov-2012.) $)
    bianfi $p |- ( ph <-> ( ps /\ ph ) ) $=
      ( wa intnan 2false ) ABADCABCEF $.
  $}

  ${
    bianfd.1 $e |- ( ph -> -. ps ) $.
    $( A wff conjoined with falsehood is false.  (Contributed by NM,
       27-Mar-1995.)  (Proof shortened by Wolf Lammen, 5-Nov-2013.) $)
    bianfd $p |- ( ph -> ( ps <-> ( ps /\ ch ) ) ) $=
      ( wa intnanrd 2falsed ) ABBCEDABCDFG $.
  $}

  $( Theorem *4.43 of [WhiteheadRussell] p. 119.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 26-Nov-2012.) $)
  pm4.43 $p |- ( ph <-> ( ( ph \/ ps ) /\ ( ph \/ -. ps ) ) ) $=
    ( wn wa wo pm3.24 biorfi ordi bitri ) AABBCZDZEABEAJEDKABFGABJHI $.

  $( Theorem *4.82 of [WhiteheadRussell] p. 122.  (Contributed by NM,
     3-Jan-2005.) $)
  pm4.82 $p |- ( ( ( ph -> ps ) /\ ( ph -> -. ps ) ) <-> -. ph ) $=
    ( wi wn wa pm2.65 imp pm2.21 jca impbii ) ABCZABDZCZEADZKMNABFGNKMABHALHIJ
    $.

  $( Theorem *4.83 of [WhiteheadRussell] p. 122, for decidable propositions.
     As with other case elimination theorems, like ~ pm2.61dc , it only holds
     for decidable propositions.  (Contributed by Jim Kingdon, 12-May-2018.) $)
  pm4.83dc $p |- ( DECID ph ->
      ( ( ( ph -> ps ) /\ ( -. ph -> ps ) ) <-> ps ) ) $=
    ( wdc wi wn wa wo df-dc pm3.44 com12 sylbi ax-1 jca impbid1 ) ACZABDZAEZBDZ
    FZBOAQGZSBDAHSTBBAQIJKBPRBALBQLMN $.

  $( A transitive law of equivalence.  Compare Theorem *4.22 of
     [WhiteheadRussell] p. 117.  (Contributed by NM, 18-Aug-1993.) $)
  biantr $p |- ( ( ( ph <-> ps ) /\ ( ch <-> ps ) ) -> ( ph <-> ch ) ) $=
    ( wb id bibi2d biimparc ) CBDZACDABDHCBAHEFG $.

  $( Disjunction distributes over the biconditional, for a decidable
     proposition.  Based on an axiom of system DS in Vladimir Lifschitz, "On
     calculational proofs" (1998),
     ~ http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.25.3384 .
     (Contributed by Jim Kingdon, 2-Apr-2018.) $)
  orbididc $p |- ( DECID ph -> ( ( ph \/ ( ps <-> ch ) ) <->
                ( ( ph \/ ps ) <-> ( ph \/ ch ) ) ) ) $=
    ( wdc wi wo wa wb orimdidc anbi12d dfbi2 orbi2i ordi bitri 3bitr4g ) ADZABC
    EZFZACBEZFZGZABFZACFZEZUCUBEZGABCHZFZUBUCHPRUDTUEABCIACBIJUGAQSGZFUAUFUHABC
    KLAQSMNUBUCKO $.

  $( Disjunction distributes over the biconditional, for a decidable
     proposition.  Based on theorem *5.7 of [WhiteheadRussell] p. 125.  This
     theorem is similar to ~ orbididc .  (Contributed by Jim Kingdon,
     2-Apr-2018.) $)
  pm5.7dc $p |- ( DECID ch -> ( ( ( ph \/ ch ) <-> ( ps \/ ch ) ) <->
               ( ch \/ ( ph <-> ps ) ) ) ) $=
    ( wdc wb wo orbididc orcom bibi12i bitr2di ) CDCABEFCAFZCBFZEACFZBCFZECABGK
    MLNCAHCBHIJ $.

  $( Dijkstra-Scholten's Golden Rule for calculational proofs.  (Contributed by
     NM, 10-Jan-2005.) $)
  bigolden $p |- ( ( ( ph /\ ps ) <-> ph ) <-> ( ps <-> ( ph \/ ps ) ) ) $=
    ( wi wa wb wo pm4.71 pm4.72 bicom 3bitr3ri ) ABCAABDZEBABFEKAEABGABHAKIJ $.

  $( Conjunction in terms of disjunction (DeMorgan's law).  Theorem *4.5 of
     [WhiteheadRussell] p. 120, but where the propositions are decidable.  The
     forward direction, ~ pm3.1 , holds for all propositions, but the
     equivalence only holds given decidability.  (Contributed by Jim Kingdon,
     21-Apr-2018.) $)
  anordc $p |- ( DECID ph -> ( DECID ps ->
      ( ( ph /\ ps ) <-> -. ( -. ph \/ -. ps ) ) ) ) $=
    ( wdc wa wn wo wb dcan ex ianordc 3bitr2rd a1d con2biddc syld ) ACZBCZABDZC
    ZQAEBEFZEGOPRABHIOSQOSQEZGROTSTSABJZUAUAKLMN $.

  $( Theorem *3.11 of [WhiteheadRussell] p. 111, but for decidable
     propositions.  The converse, ~ pm3.1 , holds for all propositions, not
     just decidable ones.  (Contributed by Jim Kingdon, 22-Apr-2018.) $)
  pm3.11dc $p |- ( DECID ph -> ( DECID ps ->
      ( -. ( -. ph \/ -. ps ) -> ( ph /\ ps ) ) ) ) $=
    ( wdc wn wo wa wi wb anordc imp biimprd ex ) ACZBCZADBDEDZABFZGMNFPOMNPOHAB
    IJKL $.

  $( Theorem *3.12 of [WhiteheadRussell] p. 111, but for decidable
     propositions.  (Contributed by Jim Kingdon, 22-Apr-2018.) $)
  pm3.12dc $p |- ( DECID ph -> ( DECID ps ->
      ( ( -. ph \/ -. ps ) \/ ( ph /\ ps ) ) ) ) $=
    ( wdc wn wo wa wi pm3.11dc imp wb dcn dcor syl2im dfordc syl6 mpbird ex ) A
    CZBCZADZBDZEZABFZEZRSFUDUBDUCGZRSUEABHIRSUDUEJZRSUBCZUFRTCSUACUGAKBKTUALMUB
    UCNOIPQ $.

  $( Theorem *3.13 of [WhiteheadRussell] p. 111, but for decidable
     propositions.  The converse, ~ pm3.14 , holds for all propositions.
     (Contributed by Jim Kingdon, 22-Apr-2018.) $)
  pm3.13dc $p |- ( DECID ph -> ( DECID ps ->
      ( -. ( ph /\ ps ) -> ( -. ph \/ -. ps ) ) ) ) $=
    ( wdc wn wo wa wi dcn dcor syl2im pm3.11dc con1dc syl6c ) ACZBCZADZBDZEZCZR
    DABFZGTDRGNPCOQCSAHBHPQIJABKRTLM $.

  $( DN_1 for decidable propositions.  Without the decidability conditions,
     DN_1 can serve as a single axiom for Boolean algebra.  See
     ~ http://www-unix.mcs.anl.gov/~~mccune/papers/basax/v12.pdf .
     (Contributed by Jim Kingdon, 22-Apr-2018.) $)
  dn1dc $p |- ( ( DECID ph /\ ( DECID ps /\ ( DECID ch /\ DECID th ) ) ) ->
      ( -. ( -. ( -. ( ph \/ ps ) \/ ch ) \/
            -. ( ph \/ -. ( -. ch \/ -. ( ch \/ th ) ) ) ) <-> ch ) ) $=
    ( wo wn wa wdc wi pm2.45 imnan mpbi biorfi wb dcor imp anordc sylc dcn syl
    orcom ordir 3bitri pm4.45 simprrl ad2antll bitrid orbi2d anbi2d syl6 syldan
    adantrr bitrd bitr2id ) CABEZFZCEZACEZGZAHZBHZCHZDHZGZGZGZUQFACFZCDEZFZEZFZ
    EZFEFZCCUPAGZEVNCEUSVNCUPAFIVNFABJUPAKLMCVNUAUPACUBUCVFUSUQVLGZVMVFURVLUQVF
    CVKACCVHGZVFVKCDUDVFVBVHHZVPVKNUTVAVBVCUEZVDVQUTVAVBVCVQCDOPUFZCVHQRUGUHUIV
    FUQHZVLHZVOVMNVFUPHZVBVTUTVAWBVDUTVAWBUTVAUOHWBABOUOSUJPULVRUPCORUTVEVKHZWA
    VFVJHZWCVFVGHZVIHZWDVFVBWEVRCSTVFVQWFVSVHSTVGVIORVJSTUTWCWAAVKOPUKUQVLQRUMU
    N $.

  $( Decidable proposition version of theorem *5.71 of [WhiteheadRussell]
     p. 125.  (Contributed by Roy F. Longton, 23-Jun-2005.)  (Modified for
     decidability by Jim Kingdon, 19-Apr-2018.) $)
  pm5.71dc $p |- ( DECID ps ->
      ( ( ps -> -. ch ) -> ( ( ( ph \/ ps ) /\ ch ) <-> ( ph /\ ch ) ) ) ) $=
    ( wn wo wa wb wi wdc orel2 orc impbid1 anbi1d a1i pm2.21 pm5.32rd jadc ) BC
    DZABEZCFACFGZBDZTHBIUASACUASABAJABKLMNRCSACSAGOPQ $.

  $( Theorem *5.75 of [WhiteheadRussell] p. 126.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Andrew Salmon, 7-May-2011.)  (Proof
     shortened by Wolf Lammen, 23-Dec-2012.) $)
  pm5.75 $p |- ( ( ( ch -> -. ps ) /\ ( ph <-> ( ps \/ ch ) ) ) ->
                ( ( ph /\ -. ps ) <-> ch ) ) $=
    ( wo wb wn wa wi anbi1 anbi1i pm5.61 bitrdi pm4.71 biimpi bicomd sylan9bbr
    orcom bitri ) ABCDZEZABFZGZCUAGZCUAHZCTUBSUAGZUCASUAIUECBDZUAGUCSUFUABCQJCB
    KRLUDCUCUDCUCECUAMNOP $.

  $( Removal of conjunct from one side of an equivalence.  (Contributed by NM,
     5-Aug-1993.) $)
  bimsc1 $p |- ( ( ( ph -> ps ) /\ ( ch <-> ( ps /\ ph ) ) )
               -> ( ch <-> ph ) ) $=
    ( wi wa wb simpr ancr impbid2 bibi2d biimpa ) ABDZCBAEZFCAFLMACLMABAGABHIJK
    $.

  ${
    ccase.1 $e |- ( ( ph /\ ps ) -> ta ) $.
    ccase.2 $e |- ( ( ch /\ ps ) -> ta ) $.
    ccase.3 $e |- ( ( ph /\ th ) -> ta ) $.
    ccase.4 $e |- ( ( ch /\ th ) -> ta ) $.
    $( Inference for combining cases.  (Contributed by NM, 29-Jul-1999.)
       (Proof shortened by Wolf Lammen, 6-Jan-2013.) $)
    ccase $p |- ( ( ( ph \/ ch ) /\ ( ps \/ th ) ) -> ta ) $=
      ( wo jaoian jaodan ) ACJBEDABECFGKADECHIKL $.
  $}

  ${
    ccased.1 $e |- ( ph -> ( ( ps /\ ch ) -> et ) ) $.
    ccased.2 $e |- ( ph -> ( ( th /\ ch ) -> et ) ) $.
    ccased.3 $e |- ( ph -> ( ( ps /\ ta ) -> et ) ) $.
    ccased.4 $e |- ( ph -> ( ( th /\ ta ) -> et ) ) $.
    $( Deduction for combining cases.  (Contributed by NM, 9-May-2004.) $)
    ccased $p |- ( ph -> ( ( ( ps \/ th ) /\ ( ch \/ ta ) ) -> et ) ) $=
      ( wo wa wi com12 ccase ) BDKCEKLAFBCDEAFMABCLFGNADCLFHNABELFINADELFJNON
      $.
  $}

  ${
    ccase2.1 $e |- ( ( ph /\ ps ) -> ta ) $.
    ccase2.2 $e |- ( ch -> ta ) $.
    ccase2.3 $e |- ( th -> ta ) $.
    $( Inference for combining cases.  (Contributed by NM, 29-Jul-1999.) $)
    ccase2 $p |- ( ( ( ph \/ ch ) /\ ( ps \/ th ) ) -> ta ) $=
      ( adantr adantl ccase ) ABCDEFCEBGIDEAHJDECHJK $.
  $}

  ${
    niabn.1 $e |- ph $.
    $( Miscellaneous inference relating falsehoods.  (Contributed by NM,
       31-Mar-1994.) $)
    niabn $p |- ( -. ps -> ( ( ch /\ ps ) <-> -. ph ) ) $=
      ( wa wn simpr pm2.24i pm5.21ni ) CBEBAFCBGABDHI $.
  $}

  $( Alternate version of ~ dedlema .  (Contributed by NM, 2-Apr-1994.)  (Proof
     shortened by Andrew Salmon, 7-May-2011.)  (Proof shortened by Wolf Lammen,
     4-Dec-2012.) $)
  dedlem0a $p |- ( ph -> ( ps <-> ( ( ch -> ph ) -> ( ps /\ ph ) ) ) ) $=
    ( wa wi iba wb ax-1 biimt syl bitrd ) ABBADZCAEZLEZABFAMLNGACHMLIJK $.

  $( Lemma for ~ iftrue .  (Contributed by NM, 26-Jun-2002.)  (Proof shortened
     by Andrew Salmon, 7-May-2011.) $)
  dedlema $p |- ( ph -> ( ps <-> ( ( ps /\ ph ) \/ ( ch /\ -. ph ) ) ) ) $=
    ( wa wn wo orc expcom wi simpl a1i pm2.24 adantld jaod impbid ) ABBADZCAEZD
    ZFZBASPRGHAPBRPBIABAJKAQBCABLMNO $.

  $( Lemma for ~ iffalse .  (Contributed by NM, 15-May-1999.)  (Proof shortened
     by Andrew Salmon, 7-May-2011.) $)
  dedlemb $p |- ( -. ph -> ( ch <-> ( ( ps /\ ph ) \/ ( ch /\ -. ph ) ) ) ) $=
    ( wn wa wo olc expcom pm2.21 adantld wi simpl a1i jaod impbid ) ADZCBAEZCPE
    ZFZCPSRQGHPQCRPACBACIJRCKPCPLMNO $.

  $( One direction of Theorem *4.42 of [WhiteheadRussell] p. 119.  (Contributed
     by Jim Kingdon, 4-Aug-2018.) $)
  pm4.42r $p |- ( ( ( ph /\ ps ) \/ ( ph /\ -. ps ) ) -> ph ) $=
    ( wa wn simpl jaoi ) ABCAABDZCABEAGEF $.

  ${
    ninba.1 $e |- ph $.
    $( Miscellaneous inference relating falsehoods.  (Contributed by NM,
       31-Mar-1994.) $)
    ninba $p |- ( -. ps -> ( -. ph <-> ( ch /\ ps ) ) ) $=
      ( wn wa niabn bicomd ) BECBFAEABCDGH $.
  $}

  ${
    prlem1.1 $e |- ( ph -> ( et <-> ch ) ) $.
    prlem1.2 $e |- ( ps -> -. th ) $.
    $( A specialized lemma for set theory (to derive the Axiom of Pairing).
       (Contributed by NM, 18-Oct-1995.)  (Proof shortened by Andrew Salmon,
       13-May-2011.)  (Proof shortened by Wolf Lammen, 5-Jan-2013.) $)
    prlem1 $p |- ( ph -> ( ps ->
                  ( ( ( ps /\ ch ) \/ ( th /\ ta ) ) -> et ) ) ) $=
      ( wa wo wi biimprd adantld pm2.21d adantrd jaao ex ) ABBCIZDEIZJFKARFBSAC
      FBAFCGLMBDFEBDFHNOPQ $.
  $}

  $( A specialized lemma for set theory (to derive the Axiom of Pairing).
     (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Andrew Salmon,
     13-May-2011.)  (Proof shortened by Wolf Lammen, 9-Dec-2012.) $)
  prlem2 $p |- ( ( ( ph /\ ps ) \/ ( ch /\ th ) ) <->
              ( ( ph \/ ch ) /\ ( ( ph /\ ps ) \/ ( ch /\ th ) ) ) ) $=
    ( wa wo simpl orim12i pm4.71ri ) ABEZCDEZFACFJAKCABGCDGHI $.

  ${
    oplem1.1 $e |- ( ph -> ( ps \/ ch ) ) $.
    oplem1.2 $e |- ( ph -> ( th \/ ta ) ) $.
    oplem1.3 $e |- ( ps <-> th ) $.
    oplem1.4 $e |- ( ch -> ( th <-> ta ) ) $.
    $( A specialized lemma for set theory (ordered pair theorem).  (Contributed
       by NM, 18-Oct-1995.)  (Proof shortened by Wolf Lammen, 8-Dec-2012.)
       (Proof shortened by Mario Carneiro, 2-Feb-2015.) $)
    oplem1 $p |- ( ph -> ps ) $=
      ( wo idd wi ax-1 biimprcd jaoi syl imbitrrdi jaod mpd ) ABCJBFABBCABKACDB
      ADEJCDLZGDTEDCMCDEINOPHQRS $.
  $}

  $( Lemma used in construction of real numbers.  (Contributed by NM,
     4-Sep-1995.)  (Proof shortened by Andrew Salmon, 26-Jun-2011.) $)
  rnlem $p |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) <->
  ( ( ( ph /\ ch ) /\ ( ps /\ th ) ) /\ ( ( ph /\ th ) /\ ( ps /\ ch ) ) ) ) $=
    ( wa an4 biimpi an42 biimpri jca adantl impbii ) ABECDEEZACEBDEEZADEBCEEZEM
    NOMNABCDFGOMADBCHZIJOMNOMPGKL $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  The conditional operator for propositions
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  This subsection introduces the conditional operator for propositions, denoted
  by ` if- ( ph , ps , ch ) ` (see ~ df-ifp ).  It is the analogue for
  propositions of the conditional operator for classes, denoted by
  ` if ( ph , A , B ) ` (see ~ df-if ).

$)

  $( Comma.  Also used later for adders, pairs, tuples, etc. $)
  $c , $.

  $( Symbol for the conditional operator for propositions. $)
  $c if- $.

  $( Extend wff notation to include the conditional operator for
     propositions. $)
  wif $a wff if- ( ph , ps , ch ) $.

  $( Definition of the conditional operator for propositions.  The expression
     ` if- ( ph , ps , ch ) ` is read "if ` ph ` then ` ps ` else ` ch ` ".
     See ~ dfifp2dc , ~ dfifp3dc , ~ dfifp4dc and ~ dfifp5dc for alternate
     definitions.

     This definition (in the form of ~ dfifp2dc ) appears in Section II.24 of
     [Church] p. 129 (Definition D12 page 132), where it is called "conditioned
     disjunction".  Church's ` [ ps , ph , ch ] ` corresponds to our
     ` if- ( ph , ps , ch ) ` (note the permutation of the first two
     variables).

     This form was chosen as the definition rather than ~ dfifp2dc for
     compatibility with intuitionistic logic development: with this form, it is
     clear that ` if- ( ph , ps , ch ) ` implies decidability of ` ph `
     ( ~ ifpdc ), which is most often what is wanted.

     (Contributed by BJ, 22-Jun-2019.) $)
  df-ifp $a |-
            ( if- ( ph , ps , ch ) <-> ( ( ph /\ ps ) \/ ( -. ph /\ ch ) ) ) $.

  $( The conditional operator for propositions implies decidability.
     (Contributed by Jim Kingdon, 25-Jan-2026.) $)
  ifpdc $p |- ( if- ( ph , ps , ch ) -> DECID ph ) $=
    ( wa wn wo wif wdc simpl orim12i df-ifp df-dc 3imtr4i ) ABDZAEZCDZFAOFABCGA
    HNAPOABIOCIJABCKALM $.

  $( Forward direction of ~ dfifp2dc .  This direction does not require
     decidability.  (Contributed by Jim Kingdon, 25-Jan-2026.) $)
  ifp2 $p |- ( if- ( ph , ps , ch ) -> ( ( ph -> ps ) /\ ( -. ph -> ch ) ) ) $=
    ( wif wa wn wo wi df-ifp pm3.4 pm2.24 adantr jca ax-in2 jaoi sylbi ) ABCDAB
    EZAFZCEZGABHZRCHZEZABCIQUBSQTUAABJAUABACKLMSTUARTCABNLRCJMOP $.

  $( Alternate definition of the conditional operator for decidable
     propositions.  The value of ` if- ( ph , ps , ch ) ` is "if ` ph ` then
     ` ps ` , and if not ` ph ` then ` ch ` ".  This is the definition used in
     Section II.24 of [Church] p. 129 (Definition D12 page 132) (see comment of
     ~ df-ifp ).  (Contributed by BJ, 22-Jun-2019.) $)
  dfifp2dc $p |- ( DECID ph ->
      ( if- ( ph , ps , ch ) <-> ( ( ph -> ps ) /\ ( -. ph -> ch ) ) ) ) $=
    ( wdc wif wi wn wa ifp2 wo exmiddc simpl simprl jcai orcd simprr olcd sylan
    jaoian df-ifp sylibr ex impbid2 ) ADZABCEZABFZAGZCFZHZABCIUDUIUEUDUIHABHZUG
    CHZJZUEUDAUGJUIULAKAUIULUGAUIHZUJUKUMABAUILAUFUHMNOUGUIHZUKUJUNUGCUGUILUGUF
    UHPNQSRABCTUAUBUC $.

  $( Alternate definition of the conditional operator for propositions.
     (Contributed by BJ, 30-Sep-2019.) $)
  dfifp3dc $p |- ( DECID ph ->
      ( if- ( ph , ps , ch ) <-> ( ( ph -> ps ) /\ ( ph \/ ch ) ) ) ) $=
    ( wdc wif wi wn wa wo dfifp2dc pm4.64dc anbi2d bitrd ) ADZABCEABFZAGCFZHOAC
    IZHABCJNPQOACKLM $.

  $( Alternate definition of the conditional operator for propositions.
     (Contributed by BJ, 30-Sep-2019.) $)
  dfifp4dc $p |- ( DECID ph ->
      ( if- ( ph , ps , ch ) <-> ( ( -. ph \/ ps ) /\ ( ph \/ ch ) ) ) ) $=
    ( wdc wif wi wo wa wn dfifp3dc imordc anbi1d bitrd ) ADZABCEABFZACGZHAIBGZP
    HABCJNOQPABKLM $.

  $( Alternate definition of the conditional operator for propositions.
     (Contributed by BJ, 2-Oct-2019.) $)
  dfifp5dc $p |- ( DECID ph ->
      ( if- ( ph , ps , ch ) <-> ( ( -. ph \/ ps ) /\ ( -. ph -> ch ) ) ) ) $=
    ( wdc wif wi wn wa wo dfifp2dc imordc anbi1d bitrd ) ADZABCEABFZAGZCFZHPBIZ
    QHABCJNORQABKLM $.

  $( Define the biconditional as conditional logic operator.  (Contributed by
     RP, 20-Apr-2020.)  (Proof shortened by Wolf Lammen, 30-Apr-2024.) $)
  ifpdfbidc $p |- ( DECID ph ->
      ( ( ph <-> ps ) <-> if- ( ph , ps , -. ps ) ) ) $=
    ( wdc wi wa wn wb wif con34bdc anbi2d dfbi2 a1i dfifp2dc 3bitr4d ) ACZABDZB
    ADZEZPAFBFZDZEABGZABSHOQTPBAIJUARGOABKLABSMN $.

  $( The conditional operator is implied by the conjunction of its possible
     outputs.  Dual statement of ~ ifpor .  (Contributed by BJ,
     30-Sep-2019.) $)
  anifpdc $p |- ( DECID ph -> ( ( ps /\ ch ) -> if- ( ph , ps , ch ) ) ) $=
    ( wa wif wdc wn wo olc anim12i dfifp4dc imbitrrid ) BCDABCEAFAGZBHZACHZDBNC
    OBMICAIJABCKL $.

  $( The conditional operator implies the disjunction of its possible outputs.
     Dual statement of ~ anifpdc .  (Contributed by BJ, 1-Oct-2019.) $)
  ifpor $p |- ( if- ( ph , ps , ch ) -> ( ps \/ ch ) ) $=
    ( wif wa wn wo df-ifp simpr orim12i sylbi ) ABCDABEZAFZCEZGBCGABCHLBNCABIMC
    IJK $.

  $( Conditional operator for the negation of a proposition.  (Contributed by
     BJ, 30-Sep-2019.)  (Proof shortened by Wolf Lammen, 5-May-2024.) $)
  ifpnst $p |- ( STAB ph ->
      ( if- ( ph , ps , ch ) <-> if- ( -. ph , ch , ps ) ) ) $=
    ( wstab wif wn wdc ifpdc adantl wa biimpi sylan2 wi wo dfifp5dc biancomd wb
    stdcndc dcn dfifp3dc syl bitr4d pm5.21nd ) ADZABCEZAFZCBEZAGZUEUHUDABCHIUGU
    DUFGZUHUFCBHUDUIJUHARKLUHUEUFCMZUFBNZJZUGUHUEUJUKABCOPUHUIUGULQASUFCBTUAUBU
    C $.

  $( Value of the conditional operator for propositions when its first argument
     is true.  Analogue for propositions of ~ iftrue .  This is essentially
     ~ dedlema .  (Contributed by BJ, 20-Sep-2019.)  (Proof shortened by Wolf
     Lammen, 10-Jul-2020.) $)
  ifptru $p |- ( ph -> ( if- ( ph , ps , ch ) <-> ps ) ) $=
    ( wif wa wn wo df-ifp ancom orbi12i bitri dedlema bitr4id ) AABCDZBAEZCAFZE
    ZGZBNABEZPCEZGRABCHSOTQABIPCIJKABCLM $.

  $( Value of the conditional operator for propositions when its first argument
     is false.  Analogue for propositions of ~ iffalse .  This is essentially
     ~ dedlemb .  (Contributed by BJ, 20-Sep-2019.)  (Proof shortened by Wolf
     Lammen, 25-Jun-2020.) $)
  ifpfal $p |- ( -. ph -> ( if- ( ph , ps , ch ) <-> ch ) ) $=
    ( wn wif wa wo df-ifp ancom orbi12i bitri dedlemb bitr4id ) ADZABCEZBAFZCNF
    ZGZCOABFZNCFZGRABCHSPTQABINCIJKABCLM $.

  $( Value of the conditional operator for propositions when the same
     proposition is returned in either case.  Analogue for propositions of
     ~ ifiddc .  (Contributed by BJ, 20-Sep-2019.) $)
  ifpiddc $p |- ( DECID ph -> ( if- ( ph , ps , ps ) <-> ps ) ) $=
    ( wdc wn wo wif wb exmiddc ifptru ifpfal jaoi syl ) ACAADZEABBFBGZAHANMABBI
    ABBJKL $.

  ${
    ifpbi123d.1 $e |- ( ph -> ( ps <-> ta ) ) $.
    ifpbi123d.2 $e |- ( ph -> ( ch <-> et ) ) $.
    ifpbi123d.3 $e |- ( ph -> ( th <-> ze ) ) $.
    $( Equivalence deduction for conditional operator for propositions.
       (Contributed by AV, 30-Dec-2020.)  (Proof shortened by Wolf Lammen,
       17-Apr-2024.) $)
    ifpbi123d $p |- ( ph -> ( if- ( ps , ch , th )
                              <-> if- ( ta , et , ze ) ) ) $=
      ( wa wn wo wif anbi12d notbid orbi12d df-ifp 3bitr4g ) ABCKZBLZDKZMEFKZEL
      ZGKZMBCDNEFGNATUCUBUEABECFHIOAUAUDDGABEHPJOQBCDREFGRS $.
  $}

  ${
    ifpbi23d.1 $e |- ( ph -> ( ch <-> et ) ) $.
    ifpbi23d.2 $e |- ( ph -> ( th <-> ze ) ) $.
    $( Equivalence deduction for conditional operator for propositions.
       Convenience theorem for a frequent case.  (Contributed by Wolf Lammen,
       28-Apr-2024.) $)
    ifpbi23d $p |- ( ph -> ( if- ( ps , ch , th )
                              <-> if- ( ps , et , ze ) ) ) $=
      ( biidd ifpbi123d ) ABCDBEFABIGHJ $.
  $}

  ${
    1fpid3.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( The value of the conditional operator for propositions is its third
       argument if the first and second argument imply the third argument.
       (Contributed by AV, 4-Apr-2021.) $)
    1fpid3 $p |- ( if- ( ph , ps , ch ) -> ch ) $=
      ( wif wa wn wo df-ifp simpr jaoi sylbi ) ABCEABFZAGZCFZHCABCIMCODNCJKL $.
  $}


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
     parentheses and emphasizes that the order of bracketing is not important
     by virtue of the associative law ~ orass .  (Contributed by NM,
     8-Apr-1994.) $)
  df-3or $a |- ( ( ph \/ ps \/ ch ) <-> ( ( ph \/ ps ) \/ ch ) ) $.

  $( Define conjunction ('and') of 3 wff.s.  Definition *4.34 of
     [WhiteheadRussell] p. 118.  This abbreviation reduces the number of
     parentheses and emphasizes that the order of bracketing is not important
     by virtue of the associative law ~ anass .  (Contributed by NM,
     8-Apr-1994.) $)
  df-3an $a |- ( ( ph /\ ps /\ ch ) <-> ( ( ph /\ ps ) /\ ch ) ) $.

  $( Associative law for triple disjunction.  (Contributed by NM,
     8-Apr-1994.) $)
  3orass $p |- ( ( ph \/ ps \/ ch ) <-> ( ph \/ ( ps \/ ch ) ) ) $=
    ( w3o wo df-3or orass bitri ) ABCDABECEABCEEABCFABCGH $.

  $( Associative law for triple conjunction.  (Contributed by NM,
     8-Apr-1994.) $)
  3anass $p |- ( ( ph /\ ps /\ ch ) <-> ( ph /\ ( ps /\ ch ) ) ) $=
    ( w3a wa df-3an anass bitri ) ABCDABECEABCEEABCFABCGH $.

  $( Rotation law for triple conjunction.  (Contributed by NM, 8-Apr-1994.) $)
  3anrot $p |- ( ( ph /\ ps /\ ch ) <-> ( ps /\ ch /\ ph ) ) $=
    ( wa w3a ancom 3anass df-3an 3bitr4i ) ABCDZDJADABCEBCAEAJFABCGBCAHI $.

  $( Rotation law for triple disjunction.  (Contributed by NM, 4-Apr-1995.) $)
  3orrot $p |- ( ( ph \/ ps \/ ch ) <-> ( ps \/ ch \/ ph ) ) $=
    ( wo w3o orcom 3orass df-3or 3bitr4i ) ABCDZDJADABCEBCAEAJFABCGBCAHI $.

  $( Commutation law for triple conjunction.  (Contributed by NM,
     21-Apr-1994.) $)
  3ancoma $p |- ( ( ph /\ ps /\ ch ) <-> ( ps /\ ph /\ ch ) ) $=
    ( wa w3a ancom anbi1i df-3an 3bitr4i ) ABDZCDBADZCDABCEBACEJKCABFGABCHBACHI
    $.

  $( Commutation law for triple conjunction.  (Contributed by NM,
     21-Apr-1994.) $)
  3ancomb $p |- ( ( ph /\ ps /\ ch ) <-> ( ph /\ ch /\ ps ) ) $=
    ( w3a 3ancoma 3anrot bitri ) ABCDBACDACBDABCEBACFG $.

  $( Commutation law for triple disjunction.  (Contributed by Scott Fenton,
     20-Apr-2011.) $)
  3orcomb $p |- ( ( ph \/ ps \/ ch ) <-> ( ph \/ ch \/ ps ) ) $=
    ( wo w3o orcom orbi2i 3orass 3bitr4i ) ABCDZDACBDZDABCEACBEJKABCFGABCHACBHI
    $.

  $( Reversal law for triple conjunction.  (Contributed by NM, 21-Apr-1994.) $)
  3anrev $p |- ( ( ph /\ ps /\ ch ) <-> ( ch /\ ps /\ ph ) ) $=
    ( w3a 3ancoma 3anrot bitr4i ) ABCDBACDCBADABCECBAFG $.

  $( Convert triple conjunction to conjunction, then commute.  (Contributed by
     Jonathan Ben-Naim, 3-Jun-2011.) $)
  3anan32 $p |- ( ( ph /\ ps /\ ch ) <-> ( ( ph /\ ch ) /\ ps ) ) $=
    ( w3a wa df-3an an32 bitri ) ABCDABECEACEBEABCFABCGH $.

  $( Convert triple conjunction to conjunction, then commute.  (Contributed by
     Jonathan Ben-Naim, 3-Jun-2011.)  (Proof shortened by Andrew Salmon,
     14-Jun-2011.) $)
  3anan12 $p |- ( ( ph /\ ps /\ ch ) <-> ( ps /\ ( ph /\ ch ) ) ) $=
    ( w3a wa 3ancoma 3anass bitri ) ABCDBACDBACEEABCFBACGH $.

  $( Distribution of triple conjunction over conjunction.  (Contributed by
     David A. Wheeler, 4-Nov-2018.) $)
  anandi3 $p |- ( ( ph /\ ps /\ ch ) <-> ( ( ph /\ ps ) /\ ( ph /\ ch ) ) )
    $=
    ( w3a wa 3anass anandi bitri ) ABCDABCEEABEACEEABCFABCGH $.

  $( Distribution of triple conjunction over conjunction.  (Contributed by
     David A. Wheeler, 4-Nov-2018.) $)
  anandi3r $p |- ( ( ph /\ ps /\ ch ) <-> ( ( ph /\ ps ) /\ ( ch /\ ps ) ) )
    $=
    ( w3a wa 3anan32 anandir bitri ) ABCDACEBEABECBEEABCFACBGH $.

  $( Negated triple disjunction as triple conjunction.  (Contributed by Scott
     Fenton, 19-Apr-2011.) $)
  3ioran $p |- ( -. ( ph \/ ps \/ ch ) <-> ( -. ph /\ -. ps /\ -. ch ) ) $=
    ( wo wn wa w3o w3a ioran anbi1i df-3or xchnxbir df-3an 3bitr4i ) ABDZEZCEZF
    ZAEZBEZFZQFABCGZESTQHPUAQABIJOCDRUBOCIABCKLSTQMN $.

  $( Simplification of triple conjunction.  (Contributed by NM,
     21-Apr-1994.) $)
  3simpa $p |- ( ( ph /\ ps /\ ch ) -> ( ph /\ ps ) ) $=
    ( w3a wa df-3an simplbi ) ABCDABECABCFG $.

  $( Simplification of triple conjunction.  (Contributed by NM,
     21-Apr-1994.) $)
  3simpb $p |- ( ( ph /\ ps /\ ch ) -> ( ph /\ ch ) ) $=
    ( w3a wa 3ancomb 3simpa sylbi ) ABCDACBDACEABCFACBGH $.

  $( Simplification of triple conjunction.  (Contributed by NM, 21-Apr-1994.)
     (Proof shortened by Andrew Salmon, 13-May-2011.) $)
  3simpc $p |- ( ( ph /\ ps /\ ch ) -> ( ps /\ ch ) ) $=
    ( w3a wa 3anrot 3simpa sylbi ) ABCDBCADBCEABCFBCAGH $.

  $( Simplification of triple conjunction.  (Contributed by NM,
     21-Apr-1994.) $)
  simp1 $p |- ( ( ph /\ ps /\ ch ) -> ph ) $=
    ( w3a 3simpa simpld ) ABCDABABCEF $.

  $( Simplification of triple conjunction.  (Contributed by NM,
     21-Apr-1994.) $)
  simp2 $p |- ( ( ph /\ ps /\ ch ) -> ps ) $=
    ( w3a 3simpa simprd ) ABCDABABCEF $.

  $( Simplification of triple conjunction.  (Contributed by NM,
     21-Apr-1994.) $)
  simp3 $p |- ( ( ph /\ ps /\ ch ) -> ch ) $=
    ( w3a 3simpc simprd ) ABCDBCABCEF $.

  $( Simplification rule.  (Contributed by Jeff Hankins, 17-Nov-2009.) $)
  simpl1 $p |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ph ) $=
    ( w3a simp1 adantr ) ABCEADABCFG $.

  $( Simplification rule.  (Contributed by Jeff Hankins, 17-Nov-2009.) $)
  simpl2 $p |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ps ) $=
    ( w3a simp2 adantr ) ABCEBDABCFG $.

  $( Simplification rule.  (Contributed by Jeff Hankins, 17-Nov-2009.) $)
  simpl3 $p |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ch ) $=
    ( w3a simp3 adantr ) ABCECDABCFG $.

  $( Simplification rule.  (Contributed by Jeff Hankins, 17-Nov-2009.) $)
  simpr1 $p |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> ps ) $=
    ( w3a simp1 adantl ) BCDEBABCDFG $.

  $( Simplification rule.  (Contributed by Jeff Hankins, 17-Nov-2009.) $)
  simpr2 $p |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> ch ) $=
    ( w3a simp2 adantl ) BCDECABCDFG $.

  $( Simplification rule.  (Contributed by Jeff Hankins, 17-Nov-2009.) $)
  simpr3 $p |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> th ) $=
    ( w3a simp3 adantl ) BCDEDABCDFG $.

  ${
    3simp1i.1 $e |- ( ph /\ ps /\ ch ) $.
    $( Infer a conjunct from a triple conjunction.  (Contributed by NM,
       19-Apr-2005.) $)
    simp1i $p |- ph $=
      ( w3a simp1 ax-mp ) ABCEADABCFG $.

    $( Infer a conjunct from a triple conjunction.  (Contributed by NM,
       19-Apr-2005.) $)
    simp2i $p |- ps $=
      ( w3a simp2 ax-mp ) ABCEBDABCFG $.

    $( Infer a conjunct from a triple conjunction.  (Contributed by NM,
       19-Apr-2005.) $)
    simp3i $p |- ch $=
      ( w3a simp3 ax-mp ) ABCECDABCFG $.
  $}

  ${
    3simp1d.1 $e |- ( ph -> ( ps /\ ch /\ th ) ) $.
    $( Deduce a conjunct from a triple conjunction.  (Contributed by NM,
       4-Sep-2005.) $)
    simp1d $p |- ( ph -> ps ) $=
      ( w3a simp1 syl ) ABCDFBEBCDGH $.

    $( Deduce a conjunct from a triple conjunction.  (Contributed by NM,
       4-Sep-2005.) $)
    simp2d $p |- ( ph -> ch ) $=
      ( w3a simp2 syl ) ABCDFCEBCDGH $.

    $( Deduce a conjunct from a triple conjunction.  (Contributed by NM,
       4-Sep-2005.) $)
    simp3d $p |- ( ph -> th ) $=
      ( w3a simp3 syl ) ABCDFDEBCDGH $.
  $}

  ${
    3simp1bi.1 $e |- ( ph <-> ( ps /\ ch /\ th ) ) $.
    $( Deduce a conjunct from a triple conjunction.  (Contributed by Jonathan
       Ben-Naim, 3-Jun-2011.) $)
    simp1bi $p |- ( ph -> ps ) $=
      ( w3a biimpi simp1d ) ABCDABCDFEGH $.

    $( Deduce a conjunct from a triple conjunction.  (Contributed by Jonathan
       Ben-Naim, 3-Jun-2011.) $)
    simp2bi $p |- ( ph -> ch ) $=
      ( w3a biimpi simp2d ) ABCDABCDFEGH $.

    $( Deduce a conjunct from a triple conjunction.  (Contributed by Jonathan
       Ben-Naim, 3-Jun-2011.) $)
    simp3bi $p |- ( ph -> th ) $=
      ( w3a biimpi simp3d ) ABCDABCDFEGH $.
  $}

  ${
    3adant.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       16-Jul-1995.) $)
    3adant1 $p |- ( ( th /\ ph /\ ps ) -> ch ) $=
      ( w3a wa 3simpc syl ) DABFABGCDABHEI $.

    $( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       16-Jul-1995.) $)
    3adant2 $p |- ( ( ph /\ th /\ ps ) -> ch ) $=
      ( w3a wa 3simpb syl ) ADBFABGCADBHEI $.

    $( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       16-Jul-1995.) $)
    3adant3 $p |- ( ( ph /\ ps /\ th ) -> ch ) $=
      ( w3a wa 3simpa syl ) ABDFABGCABDHEI $.
  $}

  ${
    3ad2ant.1 $e |- ( ph -> ch ) $.
    $( Deduction adding conjuncts to an antecedent.  (Contributed by NM,
       21-Apr-2005.) $)
    3ad2ant1 $p |- ( ( ph /\ ps /\ th ) -> ch ) $=
      ( adantr 3adant2 ) ADCBACDEFG $.

    $( Deduction adding conjuncts to an antecedent.  (Contributed by NM,
       21-Apr-2005.) $)
    3ad2ant2 $p |- ( ( ps /\ ph /\ th ) -> ch ) $=
      ( adantr 3adant1 ) ADCBACDEFG $.

    $( Deduction adding conjuncts to an antecedent.  (Contributed by NM,
       21-Apr-2005.) $)
    3ad2ant3 $p |- ( ( ps /\ th /\ ph ) -> ch ) $=
      ( adantl 3adant1 ) DACBACDEFG $.
  $}

  $( Simplification of triple conjunction.  (Contributed by NM, 9-Nov-2011.) $)
  simp1l $p |- ( ( ( ph /\ ps ) /\ ch /\ th ) -> ph ) $=
    ( wa simpl 3ad2ant1 ) ABECADABFG $.

  $( Simplification of triple conjunction.  (Contributed by NM, 9-Nov-2011.) $)
  simp1r $p |- ( ( ( ph /\ ps ) /\ ch /\ th ) -> ps ) $=
    ( wa simpr 3ad2ant1 ) ABECBDABFG $.

  $( Simplification of triple conjunction.  (Contributed by NM, 9-Nov-2011.) $)
  simp2l $p |- ( ( ph /\ ( ps /\ ch ) /\ th ) -> ps ) $=
    ( wa simpl 3ad2ant2 ) BCEABDBCFG $.

  $( Simplification of triple conjunction.  (Contributed by NM, 9-Nov-2011.) $)
  simp2r $p |- ( ( ph /\ ( ps /\ ch ) /\ th ) -> ch ) $=
    ( wa simpr 3ad2ant2 ) BCEACDBCFG $.

  $( Simplification of triple conjunction.  (Contributed by NM, 9-Nov-2011.) $)
  simp3l $p |- ( ( ph /\ ps /\ ( ch /\ th ) ) -> ch ) $=
    ( wa simpl 3ad2ant3 ) CDEACBCDFG $.

  $( Simplification of triple conjunction.  (Contributed by NM, 9-Nov-2011.) $)
  simp3r $p |- ( ( ph /\ ps /\ ( ch /\ th ) ) -> th ) $=
    ( wa simpr 3ad2ant3 ) CDEADBCDFG $.

  $( Simplification of doubly triple conjunction.  (Contributed by NM,
     17-Nov-2011.) $)
  simp11 $p |- ( ( ( ph /\ ps /\ ch ) /\ th /\ ta ) -> ph ) $=
    ( w3a simp1 3ad2ant1 ) ABCFDAEABCGH $.

  $( Simplification of doubly triple conjunction.  (Contributed by NM,
     17-Nov-2011.) $)
  simp12 $p |- ( ( ( ph /\ ps /\ ch ) /\ th /\ ta ) -> ps ) $=
    ( w3a simp2 3ad2ant1 ) ABCFDBEABCGH $.

  $( Simplification of doubly triple conjunction.  (Contributed by NM,
     17-Nov-2011.) $)
  simp13 $p |- ( ( ( ph /\ ps /\ ch ) /\ th /\ ta ) -> ch ) $=
    ( w3a simp3 3ad2ant1 ) ABCFDCEABCGH $.

  $( Simplification of doubly triple conjunction.  (Contributed by NM,
     17-Nov-2011.) $)
  simp21 $p |- ( ( ph /\ ( ps /\ ch /\ th ) /\ ta ) -> ps ) $=
    ( w3a simp1 3ad2ant2 ) BCDFABEBCDGH $.

  $( Simplification of doubly triple conjunction.  (Contributed by NM,
     17-Nov-2011.) $)
  simp22 $p |- ( ( ph /\ ( ps /\ ch /\ th ) /\ ta ) -> ch ) $=
    ( w3a simp2 3ad2ant2 ) BCDFACEBCDGH $.

  $( Simplification of doubly triple conjunction.  (Contributed by NM,
     17-Nov-2011.) $)
  simp23 $p |- ( ( ph /\ ( ps /\ ch /\ th ) /\ ta ) -> th ) $=
    ( w3a simp3 3ad2ant2 ) BCDFADEBCDGH $.

  $( Simplification of doubly triple conjunction.  (Contributed by NM,
     17-Nov-2011.) $)
  simp31 $p |- ( ( ph /\ ps /\ ( ch /\ th /\ ta ) ) -> ch ) $=
    ( w3a simp1 3ad2ant3 ) CDEFACBCDEGH $.

  $( Simplification of doubly triple conjunction.  (Contributed by NM,
     17-Nov-2011.) $)
  simp32 $p |- ( ( ph /\ ps /\ ( ch /\ th /\ ta ) ) -> th ) $=
    ( w3a simp2 3ad2ant3 ) CDEFADBCDEGH $.

  $( Simplification of doubly triple conjunction.  (Contributed by NM,
     17-Nov-2011.) $)
  simp33 $p |- ( ( ph /\ ps /\ ( ch /\ th /\ ta ) ) -> ta ) $=
    ( w3a simp3 3ad2ant3 ) CDEFAEBCDEGH $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simpll1 $p |- ( ( ( ( ph /\ ps /\ ch ) /\ th ) /\ ta ) -> ph ) $=
    ( w3a wa simpl1 adantr ) ABCFDGAEABCDHI $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simpll2 $p |- ( ( ( ( ph /\ ps /\ ch ) /\ th ) /\ ta ) -> ps ) $=
    ( w3a wa simpl2 adantr ) ABCFDGBEABCDHI $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simpll3 $p |- ( ( ( ( ph /\ ps /\ ch ) /\ th ) /\ ta ) -> ch ) $=
    ( w3a wa simpl3 adantr ) ABCFDGCEABCDHI $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simplr1 $p |- ( ( ( th /\ ( ph /\ ps /\ ch ) ) /\ ta ) -> ph ) $=
    ( w3a wa simpr1 adantr ) DABCFGAEDABCHI $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simplr2 $p |- ( ( ( th /\ ( ph /\ ps /\ ch ) ) /\ ta ) -> ps ) $=
    ( w3a wa simpr2 adantr ) DABCFGBEDABCHI $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simplr3 $p |- ( ( ( th /\ ( ph /\ ps /\ ch ) ) /\ ta ) -> ch ) $=
    ( w3a wa simpr3 adantr ) DABCFGCEDABCHI $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simprl1 $p |- ( ( ta /\ ( ( ph /\ ps /\ ch ) /\ th ) ) -> ph ) $=
    ( w3a wa simpl1 adantl ) ABCFDGAEABCDHI $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simprl2 $p |- ( ( ta /\ ( ( ph /\ ps /\ ch ) /\ th ) ) -> ps ) $=
    ( w3a wa simpl2 adantl ) ABCFDGBEABCDHI $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simprl3 $p |- ( ( ta /\ ( ( ph /\ ps /\ ch ) /\ th ) ) -> ch ) $=
    ( w3a wa simpl3 adantl ) ABCFDGCEABCDHI $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simprr1 $p |- ( ( ta /\ ( th /\ ( ph /\ ps /\ ch ) ) ) -> ph ) $=
    ( w3a wa simpr1 adantl ) DABCFGAEDABCHI $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simprr2 $p |- ( ( ta /\ ( th /\ ( ph /\ ps /\ ch ) ) ) -> ps ) $=
    ( w3a wa simpr2 adantl ) DABCFGBEDABCHI $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simprr3 $p |- ( ( ta /\ ( th /\ ( ph /\ ps /\ ch ) ) ) -> ch ) $=
    ( w3a wa simpr3 adantl ) DABCFGCEDABCHI $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simpl1l $p |- ( ( ( ( ph /\ ps ) /\ ch /\ th ) /\ ta ) -> ph ) $=
    ( wa w3a simp1l adantr ) ABFCDGAEABCDHI $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simpl1r $p |- ( ( ( ( ph /\ ps ) /\ ch /\ th ) /\ ta ) -> ps ) $=
    ( wa w3a simp1r adantr ) ABFCDGBEABCDHI $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simpl2l $p |- ( ( ( ch /\ ( ph /\ ps ) /\ th ) /\ ta ) -> ph ) $=
    ( wa w3a simp2l adantr ) CABFDGAECABDHI $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simpl2r $p |- ( ( ( ch /\ ( ph /\ ps ) /\ th ) /\ ta ) -> ps ) $=
    ( wa w3a simp2r adantr ) CABFDGBECABDHI $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simpl3l $p |- ( ( ( ch /\ th /\ ( ph /\ ps ) ) /\ ta ) -> ph ) $=
    ( wa w3a simp3l adantr ) CDABFGAECDABHI $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simpl3r $p |- ( ( ( ch /\ th /\ ( ph /\ ps ) ) /\ ta ) -> ps ) $=
    ( wa w3a simp3r adantr ) CDABFGBECDABHI $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simpr1l $p |- ( ( ta /\ ( ( ph /\ ps ) /\ ch /\ th ) ) -> ph ) $=
    ( wa w3a simp1l adantl ) ABFCDGAEABCDHI $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simpr1r $p |- ( ( ta /\ ( ( ph /\ ps ) /\ ch /\ th ) ) -> ps ) $=
    ( wa w3a simp1r adantl ) ABFCDGBEABCDHI $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simpr2l $p |- ( ( ta /\ ( ch /\ ( ph /\ ps ) /\ th ) ) -> ph ) $=
    ( wa w3a simp2l adantl ) CABFDGAECABDHI $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simpr2r $p |- ( ( ta /\ ( ch /\ ( ph /\ ps ) /\ th ) ) -> ps ) $=
    ( wa w3a simp2r adantl ) CABFDGBECABDHI $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simpr3l $p |- ( ( ta /\ ( ch /\ th /\ ( ph /\ ps ) ) ) -> ph ) $=
    ( wa w3a simp3l adantl ) CDABFGAECDABHI $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simpr3r $p |- ( ( ta /\ ( ch /\ th /\ ( ph /\ ps ) ) ) -> ps ) $=
    ( wa w3a simp3r adantl ) CDABFGBECDABHI $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp1ll $p |- ( ( ( ( ph /\ ps ) /\ ch ) /\ th /\ ta ) -> ph ) $=
    ( wa simpll 3ad2ant1 ) ABFCFDAEABCGH $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp1lr $p |- ( ( ( ( ph /\ ps ) /\ ch ) /\ th /\ ta ) -> ps ) $=
    ( wa simplr 3ad2ant1 ) ABFCFDBEABCGH $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp1rl $p |- ( ( ( ch /\ ( ph /\ ps ) ) /\ th /\ ta ) -> ph ) $=
    ( wa simprl 3ad2ant1 ) CABFFDAECABGH $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp1rr $p |- ( ( ( ch /\ ( ph /\ ps ) ) /\ th /\ ta ) -> ps ) $=
    ( wa simprr 3ad2ant1 ) CABFFDBECABGH $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp2ll $p |- ( ( th /\ ( ( ph /\ ps ) /\ ch ) /\ ta ) -> ph ) $=
    ( wa simpll 3ad2ant2 ) ABFCFDAEABCGH $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp2lr $p |- ( ( th /\ ( ( ph /\ ps ) /\ ch ) /\ ta ) -> ps ) $=
    ( wa simplr 3ad2ant2 ) ABFCFDBEABCGH $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp2rl $p |- ( ( th /\ ( ch /\ ( ph /\ ps ) ) /\ ta ) -> ph ) $=
    ( wa simprl 3ad2ant2 ) CABFFDAECABGH $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp2rr $p |- ( ( th /\ ( ch /\ ( ph /\ ps ) ) /\ ta ) -> ps ) $=
    ( wa simprr 3ad2ant2 ) CABFFDBECABGH $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp3ll $p |- ( ( th /\ ta /\ ( ( ph /\ ps ) /\ ch ) ) -> ph ) $=
    ( wa simpll 3ad2ant3 ) ABFCFDAEABCGH $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp3lr $p |- ( ( th /\ ta /\ ( ( ph /\ ps ) /\ ch ) ) -> ps ) $=
    ( wa simplr 3ad2ant3 ) ABFCFDBEABCGH $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp3rl $p |- ( ( th /\ ta /\ ( ch /\ ( ph /\ ps ) ) ) -> ph ) $=
    ( wa simprl 3ad2ant3 ) CABFFDAECABGH $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp3rr $p |- ( ( th /\ ta /\ ( ch /\ ( ph /\ ps ) ) ) -> ps ) $=
    ( wa simprr 3ad2ant3 ) CABFFDBECABGH $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simpl11 $p |- ( ( ( ( ph /\ ps /\ ch ) /\ th /\ ta ) /\ et ) -> ph ) $=
    ( w3a simp11 adantr ) ABCGDEGAFABCDEHI $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simpl12 $p |- ( ( ( ( ph /\ ps /\ ch ) /\ th /\ ta ) /\ et ) -> ps ) $=
    ( w3a simp12 adantr ) ABCGDEGBFABCDEHI $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simpl13 $p |- ( ( ( ( ph /\ ps /\ ch ) /\ th /\ ta ) /\ et ) -> ch ) $=
    ( w3a simp13 adantr ) ABCGDEGCFABCDEHI $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simpl21 $p |- ( ( ( th /\ ( ph /\ ps /\ ch ) /\ ta ) /\ et ) -> ph ) $=
    ( w3a simp21 adantr ) DABCGEGAFDABCEHI $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simpl22 $p |- ( ( ( th /\ ( ph /\ ps /\ ch ) /\ ta ) /\ et ) -> ps ) $=
    ( w3a simp22 adantr ) DABCGEGBFDABCEHI $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simpl23 $p |- ( ( ( th /\ ( ph /\ ps /\ ch ) /\ ta ) /\ et ) -> ch ) $=
    ( w3a simp23 adantr ) DABCGEGCFDABCEHI $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simpl31 $p |- ( ( ( th /\ ta /\ ( ph /\ ps /\ ch ) ) /\ et ) -> ph ) $=
    ( w3a simp31 adantr ) DEABCGGAFDEABCHI $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simpl32 $p |- ( ( ( th /\ ta /\ ( ph /\ ps /\ ch ) ) /\ et ) -> ps ) $=
    ( w3a simp32 adantr ) DEABCGGBFDEABCHI $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simpl33 $p |- ( ( ( th /\ ta /\ ( ph /\ ps /\ ch ) ) /\ et ) -> ch ) $=
    ( w3a simp33 adantr ) DEABCGGCFDEABCHI $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simpr11 $p |- ( ( et /\ ( ( ph /\ ps /\ ch ) /\ th /\ ta ) ) -> ph ) $=
    ( w3a simp11 adantl ) ABCGDEGAFABCDEHI $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simpr12 $p |- ( ( et /\ ( ( ph /\ ps /\ ch ) /\ th /\ ta ) ) -> ps ) $=
    ( w3a simp12 adantl ) ABCGDEGBFABCDEHI $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simpr13 $p |- ( ( et /\ ( ( ph /\ ps /\ ch ) /\ th /\ ta ) ) -> ch ) $=
    ( w3a simp13 adantl ) ABCGDEGCFABCDEHI $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simpr21 $p |- ( ( et /\ ( th /\ ( ph /\ ps /\ ch ) /\ ta ) ) -> ph ) $=
    ( w3a simp21 adantl ) DABCGEGAFDABCEHI $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simpr22 $p |- ( ( et /\ ( th /\ ( ph /\ ps /\ ch ) /\ ta ) ) -> ps ) $=
    ( w3a simp22 adantl ) DABCGEGBFDABCEHI $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simpr23 $p |- ( ( et /\ ( th /\ ( ph /\ ps /\ ch ) /\ ta ) ) -> ch ) $=
    ( w3a simp23 adantl ) DABCGEGCFDABCEHI $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simpr31 $p |- ( ( et /\ ( th /\ ta /\ ( ph /\ ps /\ ch ) ) ) -> ph ) $=
    ( w3a simp31 adantl ) DEABCGGAFDEABCHI $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simpr32 $p |- ( ( et /\ ( th /\ ta /\ ( ph /\ ps /\ ch ) ) ) -> ps ) $=
    ( w3a simp32 adantl ) DEABCGGBFDEABCHI $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simpr33 $p |- ( ( et /\ ( th /\ ta /\ ( ph /\ ps /\ ch ) ) ) -> ch ) $=
    ( w3a simp33 adantl ) DEABCGGCFDEABCHI $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp1l1 $p |- ( ( ( ( ph /\ ps /\ ch ) /\ th ) /\ ta /\ et ) -> ph ) $=
    ( w3a wa simpl1 3ad2ant1 ) ABCGDHEAFABCDIJ $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp1l2 $p |- ( ( ( ( ph /\ ps /\ ch ) /\ th ) /\ ta /\ et ) -> ps ) $=
    ( w3a wa simpl2 3ad2ant1 ) ABCGDHEBFABCDIJ $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp1l3 $p |- ( ( ( ( ph /\ ps /\ ch ) /\ th ) /\ ta /\ et ) -> ch ) $=
    ( w3a wa simpl3 3ad2ant1 ) ABCGDHECFABCDIJ $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp1r1 $p |- ( ( ( th /\ ( ph /\ ps /\ ch ) ) /\ ta /\ et ) -> ph ) $=
    ( w3a wa simpr1 3ad2ant1 ) DABCGHEAFDABCIJ $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp1r2 $p |- ( ( ( th /\ ( ph /\ ps /\ ch ) ) /\ ta /\ et ) -> ps ) $=
    ( w3a wa simpr2 3ad2ant1 ) DABCGHEBFDABCIJ $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp1r3 $p |- ( ( ( th /\ ( ph /\ ps /\ ch ) ) /\ ta /\ et ) -> ch ) $=
    ( w3a wa simpr3 3ad2ant1 ) DABCGHECFDABCIJ $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp2l1 $p |- ( ( ta /\ ( ( ph /\ ps /\ ch ) /\ th ) /\ et ) -> ph ) $=
    ( w3a wa simpl1 3ad2ant2 ) ABCGDHEAFABCDIJ $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp2l2 $p |- ( ( ta /\ ( ( ph /\ ps /\ ch ) /\ th ) /\ et ) -> ps ) $=
    ( w3a wa simpl2 3ad2ant2 ) ABCGDHEBFABCDIJ $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp2l3 $p |- ( ( ta /\ ( ( ph /\ ps /\ ch ) /\ th ) /\ et ) -> ch ) $=
    ( w3a wa simpl3 3ad2ant2 ) ABCGDHECFABCDIJ $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp2r1 $p |- ( ( ta /\ ( th /\ ( ph /\ ps /\ ch ) ) /\ et ) -> ph ) $=
    ( w3a wa simpr1 3ad2ant2 ) DABCGHEAFDABCIJ $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp2r2 $p |- ( ( ta /\ ( th /\ ( ph /\ ps /\ ch ) ) /\ et ) -> ps ) $=
    ( w3a wa simpr2 3ad2ant2 ) DABCGHEBFDABCIJ $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp2r3 $p |- ( ( ta /\ ( th /\ ( ph /\ ps /\ ch ) ) /\ et ) -> ch ) $=
    ( w3a wa simpr3 3ad2ant2 ) DABCGHECFDABCIJ $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp3l1 $p |- ( ( ta /\ et /\ ( ( ph /\ ps /\ ch ) /\ th ) ) -> ph ) $=
    ( w3a wa simpl1 3ad2ant3 ) ABCGDHEAFABCDIJ $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp3l2 $p |- ( ( ta /\ et /\ ( ( ph /\ ps /\ ch ) /\ th ) ) -> ps ) $=
    ( w3a wa simpl2 3ad2ant3 ) ABCGDHEBFABCDIJ $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp3l3 $p |- ( ( ta /\ et /\ ( ( ph /\ ps /\ ch ) /\ th ) ) -> ch ) $=
    ( w3a wa simpl3 3ad2ant3 ) ABCGDHECFABCDIJ $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp3r1 $p |- ( ( ta /\ et /\ ( th /\ ( ph /\ ps /\ ch ) ) ) -> ph ) $=
    ( w3a wa simpr1 3ad2ant3 ) DABCGHEAFDABCIJ $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp3r2 $p |- ( ( ta /\ et /\ ( th /\ ( ph /\ ps /\ ch ) ) ) -> ps ) $=
    ( w3a wa simpr2 3ad2ant3 ) DABCGHEBFDABCIJ $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp3r3 $p |- ( ( ta /\ et /\ ( th /\ ( ph /\ ps /\ ch ) ) ) -> ch ) $=
    ( w3a wa simpr3 3ad2ant3 ) DABCGHECFDABCIJ $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp11l $p |- ( ( ( ( ph /\ ps ) /\ ch /\ th ) /\ ta /\ et ) -> ph ) $=
    ( wa w3a simp1l 3ad2ant1 ) ABGCDHEAFABCDIJ $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp11r $p |- ( ( ( ( ph /\ ps ) /\ ch /\ th ) /\ ta /\ et ) -> ps ) $=
    ( wa w3a simp1r 3ad2ant1 ) ABGCDHEBFABCDIJ $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp12l $p |- ( ( ( ch /\ ( ph /\ ps ) /\ th ) /\ ta /\ et ) -> ph ) $=
    ( wa w3a simp2l 3ad2ant1 ) CABGDHEAFCABDIJ $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp12r $p |- ( ( ( ch /\ ( ph /\ ps ) /\ th ) /\ ta /\ et ) -> ps ) $=
    ( wa w3a simp2r 3ad2ant1 ) CABGDHEBFCABDIJ $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp13l $p |- ( ( ( ch /\ th /\ ( ph /\ ps ) ) /\ ta /\ et ) -> ph ) $=
    ( wa w3a simp3l 3ad2ant1 ) CDABGHEAFCDABIJ $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp13r $p |- ( ( ( ch /\ th /\ ( ph /\ ps ) ) /\ ta /\ et ) -> ps ) $=
    ( wa w3a simp3r 3ad2ant1 ) CDABGHEBFCDABIJ $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp21l $p |- ( ( ta /\ ( ( ph /\ ps ) /\ ch /\ th ) /\ et ) -> ph ) $=
    ( wa w3a simp1l 3ad2ant2 ) ABGCDHEAFABCDIJ $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp21r $p |- ( ( ta /\ ( ( ph /\ ps ) /\ ch /\ th ) /\ et ) -> ps ) $=
    ( wa w3a simp1r 3ad2ant2 ) ABGCDHEBFABCDIJ $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp22l $p |- ( ( ta /\ ( ch /\ ( ph /\ ps ) /\ th ) /\ et ) -> ph ) $=
    ( wa w3a simp2l 3ad2ant2 ) CABGDHEAFCABDIJ $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp22r $p |- ( ( ta /\ ( ch /\ ( ph /\ ps ) /\ th ) /\ et ) -> ps ) $=
    ( wa w3a simp2r 3ad2ant2 ) CABGDHEBFCABDIJ $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp23l $p |- ( ( ta /\ ( ch /\ th /\ ( ph /\ ps ) ) /\ et ) -> ph ) $=
    ( wa w3a simp3l 3ad2ant2 ) CDABGHEAFCDABIJ $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp23r $p |- ( ( ta /\ ( ch /\ th /\ ( ph /\ ps ) ) /\ et ) -> ps ) $=
    ( wa w3a simp3r 3ad2ant2 ) CDABGHEBFCDABIJ $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp31l $p |- ( ( ta /\ et /\ ( ( ph /\ ps ) /\ ch /\ th ) ) -> ph ) $=
    ( wa w3a simp1l 3ad2ant3 ) ABGCDHEAFABCDIJ $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp31r $p |- ( ( ta /\ et /\ ( ( ph /\ ps ) /\ ch /\ th ) ) -> ps ) $=
    ( wa w3a simp1r 3ad2ant3 ) ABGCDHEBFABCDIJ $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp32l $p |- ( ( ta /\ et /\ ( ch /\ ( ph /\ ps ) /\ th ) ) -> ph ) $=
    ( wa w3a simp2l 3ad2ant3 ) CABGDHEAFCABDIJ $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp32r $p |- ( ( ta /\ et /\ ( ch /\ ( ph /\ ps ) /\ th ) ) -> ps ) $=
    ( wa w3a simp2r 3ad2ant3 ) CABGDHEBFCABDIJ $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp33l $p |- ( ( ta /\ et /\ ( ch /\ th /\ ( ph /\ ps ) ) ) -> ph ) $=
    ( wa w3a simp3l 3ad2ant3 ) CDABGHEAFCDABIJ $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp33r $p |- ( ( ta /\ et /\ ( ch /\ th /\ ( ph /\ ps ) ) ) -> ps ) $=
    ( wa w3a simp3r 3ad2ant3 ) CDABGHEBFCDABIJ $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp111 $p |- ( ( ( ( ph /\ ps /\ ch ) /\ th /\ ta ) /\ et /\ ze ) -> ph ) $=
    ( w3a simp11 3ad2ant1 ) ABCHDEHFAGABCDEIJ $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp112 $p |- ( ( ( ( ph /\ ps /\ ch ) /\ th /\ ta ) /\ et /\ ze ) -> ps ) $=
    ( w3a simp12 3ad2ant1 ) ABCHDEHFBGABCDEIJ $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp113 $p |- ( ( ( ( ph /\ ps /\ ch ) /\ th /\ ta ) /\ et /\ ze ) -> ch ) $=
    ( w3a simp13 3ad2ant1 ) ABCHDEHFCGABCDEIJ $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp121 $p |- ( ( ( th /\ ( ph /\ ps /\ ch ) /\ ta ) /\ et /\ ze ) -> ph ) $=
    ( w3a simp21 3ad2ant1 ) DABCHEHFAGDABCEIJ $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp122 $p |- ( ( ( th /\ ( ph /\ ps /\ ch ) /\ ta ) /\ et /\ ze ) -> ps ) $=
    ( w3a simp22 3ad2ant1 ) DABCHEHFBGDABCEIJ $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp123 $p |- ( ( ( th /\ ( ph /\ ps /\ ch ) /\ ta ) /\ et /\ ze ) -> ch ) $=
    ( w3a simp23 3ad2ant1 ) DABCHEHFCGDABCEIJ $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp131 $p |- ( ( ( th /\ ta /\ ( ph /\ ps /\ ch ) ) /\ et /\ ze ) -> ph ) $=
    ( w3a simp31 3ad2ant1 ) DEABCHHFAGDEABCIJ $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp132 $p |- ( ( ( th /\ ta /\ ( ph /\ ps /\ ch ) ) /\ et /\ ze ) -> ps ) $=
    ( w3a simp32 3ad2ant1 ) DEABCHHFBGDEABCIJ $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp133 $p |- ( ( ( th /\ ta /\ ( ph /\ ps /\ ch ) ) /\ et /\ ze ) -> ch ) $=
    ( w3a simp33 3ad2ant1 ) DEABCHHFCGDEABCIJ $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp211 $p |- ( ( et /\ ( ( ph /\ ps /\ ch ) /\ th /\ ta ) /\ ze ) -> ph ) $=
    ( w3a simp11 3ad2ant2 ) ABCHDEHFAGABCDEIJ $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp212 $p |- ( ( et /\ ( ( ph /\ ps /\ ch ) /\ th /\ ta ) /\ ze ) -> ps ) $=
    ( w3a simp12 3ad2ant2 ) ABCHDEHFBGABCDEIJ $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp213 $p |- ( ( et /\ ( ( ph /\ ps /\ ch ) /\ th /\ ta ) /\ ze ) -> ch ) $=
    ( w3a simp13 3ad2ant2 ) ABCHDEHFCGABCDEIJ $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp221 $p |- ( ( et /\ ( th /\ ( ph /\ ps /\ ch ) /\ ta ) /\ ze ) -> ph ) $=
    ( w3a simp21 3ad2ant2 ) DABCHEHFAGDABCEIJ $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp222 $p |- ( ( et /\ ( th /\ ( ph /\ ps /\ ch ) /\ ta ) /\ ze ) -> ps ) $=
    ( w3a simp22 3ad2ant2 ) DABCHEHFBGDABCEIJ $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp223 $p |- ( ( et /\ ( th /\ ( ph /\ ps /\ ch ) /\ ta ) /\ ze ) -> ch ) $=
    ( w3a simp23 3ad2ant2 ) DABCHEHFCGDABCEIJ $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp231 $p |- ( ( et /\ ( th /\ ta /\ ( ph /\ ps /\ ch ) ) /\ ze ) -> ph ) $=
    ( w3a simp31 3ad2ant2 ) DEABCHHFAGDEABCIJ $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp232 $p |- ( ( et /\ ( th /\ ta /\ ( ph /\ ps /\ ch ) ) /\ ze ) -> ps ) $=
    ( w3a simp32 3ad2ant2 ) DEABCHHFBGDEABCIJ $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp233 $p |- ( ( et /\ ( th /\ ta /\ ( ph /\ ps /\ ch ) ) /\ ze ) -> ch ) $=
    ( w3a simp33 3ad2ant2 ) DEABCHHFCGDEABCIJ $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp311 $p |- ( ( et /\ ze /\ ( ( ph /\ ps /\ ch ) /\ th /\ ta ) ) -> ph ) $=
    ( w3a simp11 3ad2ant3 ) ABCHDEHFAGABCDEIJ $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp312 $p |- ( ( et /\ ze /\ ( ( ph /\ ps /\ ch ) /\ th /\ ta ) ) -> ps ) $=
    ( w3a simp12 3ad2ant3 ) ABCHDEHFBGABCDEIJ $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp313 $p |- ( ( et /\ ze /\ ( ( ph /\ ps /\ ch ) /\ th /\ ta ) ) -> ch ) $=
    ( w3a simp13 3ad2ant3 ) ABCHDEHFCGABCDEIJ $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp321 $p |- ( ( et /\ ze /\ ( th /\ ( ph /\ ps /\ ch ) /\ ta ) ) -> ph ) $=
    ( w3a simp21 3ad2ant3 ) DABCHEHFAGDABCEIJ $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp322 $p |- ( ( et /\ ze /\ ( th /\ ( ph /\ ps /\ ch ) /\ ta ) ) -> ps ) $=
    ( w3a simp22 3ad2ant3 ) DABCHEHFBGDABCEIJ $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp323 $p |- ( ( et /\ ze /\ ( th /\ ( ph /\ ps /\ ch ) /\ ta ) ) -> ch ) $=
    ( w3a simp23 3ad2ant3 ) DABCHEHFCGDABCEIJ $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp331 $p |- ( ( et /\ ze /\ ( th /\ ta /\ ( ph /\ ps /\ ch ) ) ) -> ph ) $=
    ( w3a simp31 3ad2ant3 ) DEABCHHFAGDEABCIJ $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp332 $p |- ( ( et /\ ze /\ ( th /\ ta /\ ( ph /\ ps /\ ch ) ) ) -> ps ) $=
    ( w3a simp32 3ad2ant3 ) DEABCHHFBGDEABCIJ $.

  $( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
  simp333 $p |- ( ( et /\ ze /\ ( th /\ ta /\ ( ph /\ ps /\ ch ) ) ) -> ch ) $=
    ( w3a simp33 3ad2ant3 ) DEABCHHFCGDEABCIJ $.

  ${
    3adantl.1 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
    $( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       24-Feb-2005.) $)
    3adantl1 $p |- ( ( ( ta /\ ph /\ ps ) /\ ch ) -> th ) $=
      ( w3a wa 3simpc sylan ) EABGABHCDEABIFJ $.

    $( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       24-Feb-2005.) $)
    3adantl2 $p |- ( ( ( ph /\ ta /\ ps ) /\ ch ) -> th ) $=
      ( w3a wa 3simpb sylan ) AEBGABHCDAEBIFJ $.

    $( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       24-Feb-2005.) $)
    3adantl3 $p |- ( ( ( ph /\ ps /\ ta ) /\ ch ) -> th ) $=
      ( w3a wa 3simpa sylan ) ABEGABHCDABEIFJ $.
  $}

  ${
    3adantr.1 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
    $( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       27-Apr-2005.) $)
    3adantr1 $p |- ( ( ph /\ ( ta /\ ps /\ ch ) ) -> th ) $=
      ( w3a wa 3simpc sylan2 ) EBCGABCHDEBCIFJ $.

    $( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       27-Apr-2005.) $)
    3adantr2 $p |- ( ( ph /\ ( ps /\ ta /\ ch ) ) -> th ) $=
      ( w3a wa 3simpb sylan2 ) BECGABCHDBECIFJ $.

    $( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       27-Apr-2005.) $)
    3adantr3 $p |- ( ( ph /\ ( ps /\ ch /\ ta ) ) -> th ) $=
      ( w3a wa 3simpa sylan2 ) BCEGABCHDBCEIFJ $.
  $}

  ${
    3ad2antl.1 $e |- ( ( ph /\ ch ) -> th ) $.
    $( Deduction adding conjuncts to antecedent.  (Contributed by NM,
       4-Aug-2007.) $)
    3ad2antl1 $p |- ( ( ( ph /\ ps /\ ta ) /\ ch ) -> th ) $=
      ( adantlr 3adantl2 ) AECDBACDEFGH $.

    $( Deduction adding conjuncts to antecedent.  (Contributed by NM,
       4-Aug-2007.) $)
    3ad2antl2 $p |- ( ( ( ps /\ ph /\ ta ) /\ ch ) -> th ) $=
      ( adantlr 3adantl1 ) AECDBACDEFGH $.

    $( Deduction adding conjuncts to antecedent.  (Contributed by NM,
       4-Aug-2007.) $)
    3ad2antl3 $p |- ( ( ( ps /\ ta /\ ph ) /\ ch ) -> th ) $=
      ( adantll 3adantl1 ) EACDBACDEFGH $.

    $( Deduction adding a conjuncts to antecedent.  (Contributed by NM,
       25-Dec-2007.) $)
    3ad2antr1 $p |- ( ( ph /\ ( ch /\ ps /\ ta ) ) -> th ) $=
      ( adantrr 3adantr3 ) ACBDEACDBFGH $.

    $( Deduction adding a conjuncts to antecedent.  (Contributed by NM,
       27-Dec-2007.) $)
    3ad2antr2 $p |- ( ( ph /\ ( ps /\ ch /\ ta ) ) -> th ) $=
      ( adantrl 3adantr3 ) ABCDEACDBFGH $.

    $( Deduction adding a conjuncts to antecedent.  (Contributed by NM,
       30-Dec-2007.) $)
    3ad2antr3 $p |- ( ( ph /\ ( ps /\ ta /\ ch ) ) -> th ) $=
      ( adantrl 3adantr1 ) AECDBACDEFGH $.
  $}

  ${
    3anibar.1 $e |- ( ( ph /\ ps /\ ch ) -> ( th <-> ( ch /\ ta ) ) ) $.
    $( Remove a hypothesis from the second member of a biconditional.
       (Contributed by FL, 22-Jul-2008.) $)
    3anibar $p |- ( ( ph /\ ps /\ ch ) -> ( th <-> ta ) ) $=
      ( w3a wa simp3 biantrurd bitr4d ) ABCGZDCEHEFLCEABCIJK $.
  $}

  $( Introduction in triple disjunction.  (Contributed by NM, 4-Apr-1995.) $)
  3mix1 $p |- ( ph -> ( ph \/ ps \/ ch ) ) $=
    ( wo w3o orc 3orass sylibr ) AABCDZDABCEAIFABCGH $.

  $( Introduction in triple disjunction.  (Contributed by NM, 4-Apr-1995.) $)
  3mix2 $p |- ( ph -> ( ps \/ ph \/ ch ) ) $=
    ( w3o 3mix1 3orrot sylibr ) AACBDBACDACBEBACFG $.

  $( Introduction in triple disjunction.  (Contributed by NM, 4-Apr-1995.) $)
  3mix3 $p |- ( ph -> ( ps \/ ch \/ ph ) ) $=
    ( w3o 3mix1 3orrot sylib ) AABCDBCADABCEABCFG $.

  ${
    3mixi.1 $e |- ph $.
    $( Introduction in triple disjunction.  (Contributed by Mario Carneiro,
       6-Oct-2014.) $)
    3mix1i $p |- ( ph \/ ps \/ ch ) $=
      ( w3o 3mix1 ax-mp ) AABCEDABCFG $.

    $( Introduction in triple disjunction.  (Contributed by Mario Carneiro,
       6-Oct-2014.) $)
    3mix2i $p |- ( ps \/ ph \/ ch ) $=
      ( w3o 3mix2 ax-mp ) ABACEDABCFG $.

    $( Introduction in triple disjunction.  (Contributed by Mario Carneiro,
       6-Oct-2014.) $)
    3mix3i $p |- ( ps \/ ch \/ ph ) $=
      ( w3o 3mix3 ax-mp ) ABCAEDABCFG $.
  $}

  ${
    3mixd.1 $e |- ( ph -> ps ) $.
    $( Deduction introducing triple disjunction.  (Contributed by Scott Fenton,
       8-Jun-2011.) $)
    3mix1d $p |- ( ph -> ( ps \/ ch \/ th ) ) $=
      ( w3o 3mix1 syl ) ABBCDFEBCDGH $.

    $( Deduction introducing triple disjunction.  (Contributed by Scott Fenton,
       8-Jun-2011.) $)
    3mix2d $p |- ( ph -> ( ch \/ ps \/ th ) ) $=
      ( w3o 3mix2 syl ) ABCBDFEBCDGH $.

    $( Deduction introducing triple disjunction.  (Contributed by Scott Fenton,
       8-Jun-2011.) $)
    3mix3d $p |- ( ph -> ( ch \/ th \/ ps ) ) $=
      ( w3o 3mix3 syl ) ABCDBFEBCDGH $.
  $}

  ${
    3pm3.2i.1 $e |- ph $.
    3pm3.2i.2 $e |- ps $.
    3pm3.2i.3 $e |- ch $.
    $( Infer conjunction of premises.  (Contributed by NM, 10-Feb-1995.) $)
    3pm3.2i $p |- ( ph /\ ps /\ ch ) $=
      ( w3a wa pm3.2i df-3an mpbir2an ) ABCGABHCABDEIFABCJK $.
  $}

  $( ~ pm3.2 for a triple conjunction.  (Contributed by Alan Sare,
     24-Oct-2011.) $)
  pm3.2an3 $p |- ( ph -> ( ps -> ( ch -> ( ph /\ ps /\ ch ) ) ) ) $=
    ( wa w3a wi pm3.2 ex df-3an bicomi syl8ib ) ABCABDZCDZABCEZABCMFLCGHNMABCIJ
    K $.

  ${
    3jca.1 $e |- ( ph -> ps ) $.
    3jca.2 $e |- ( ph -> ch ) $.
    3jca.3 $e |- ( ph -> th ) $.
    $( Join consequents with conjunction.  (Contributed by NM, 9-Apr-1994.) $)
    3jca $p |- ( ph -> ( ps /\ ch /\ th ) ) $=
      ( wa w3a jca31 df-3an sylibr ) ABCHDHBCDIABCDEFGJBCDKL $.
  $}

  ${
    3jcad.1 $e |- ( ph -> ( ps -> ch ) ) $.
    3jcad.2 $e |- ( ph -> ( ps -> th ) ) $.
    3jcad.3 $e |- ( ph -> ( ps -> ta ) ) $.
    $( Deduction conjoining the consequents of three implications.
       (Contributed by NM, 25-Sep-2005.) $)
    3jcad $p |- ( ph -> ( ps -> ( ch /\ th /\ ta ) ) ) $=
      ( w3a wa imp 3jca ex ) ABCDEIABJCDEABCFKABDGKABEHKLM $.
  $}

  ${
    mpbir3an.1 $e |- ps $.
    mpbir3an.2 $e |- ch $.
    mpbir3an.3 $e |- th $.
    mpbir3an.4 $e |- ( ph <-> ( ps /\ ch /\ th ) ) $.
    $( Detach a conjunction of truths in a biconditional.  (Contributed by NM,
       16-Sep-2011.)  (Revised by NM, 9-Jan-2015.) $)
    mpbir3an $p |- ph $=
      ( w3a 3pm3.2i mpbir ) ABCDIBCDEFGJHK $.
  $}

  ${
    mpbir3and.1 $e |- ( ph -> ch ) $.
    mpbir3and.2 $e |- ( ph -> th ) $.
    mpbir3and.3 $e |- ( ph -> ta ) $.
    mpbir3and.4 $e |- ( ph -> ( ps <-> ( ch /\ th /\ ta ) ) ) $.
    $( Detach a conjunction of truths in a biconditional.  (Contributed by
       Mario Carneiro, 11-May-2014.) $)
    mpbir3and $p |- ( ph -> ps ) $=
      ( w3a 3jca mpbird ) ABCDEJACDEFGHKIL $.
  $}

  ${
    syl3anbrc.1 $e |- ( ph -> ps ) $.
    syl3anbrc.2 $e |- ( ph -> ch ) $.
    syl3anbrc.3 $e |- ( ph -> th ) $.
    syl3anbrc.4 $e |- ( ta <-> ( ps /\ ch /\ th ) ) $.
    $( Syllogism inference.  (Contributed by Mario Carneiro, 11-May-2014.) $)
    syl3anbrc $p |- ( ph -> ta ) $=
      ( w3a 3jca sylibr ) ABCDJEABCDFGHKIL $.
  $}

  ${
    syl21anbrc.1 $e |- ( ph -> ps ) $.
    syl21anbrc.2 $e |- ( ph -> ch ) $.
    syl21anbrc.3 $e |- ( ph -> th ) $.
    syl21anbrc.4 $e |- ( ta <-> ( ( ps /\ ch ) /\ th ) ) $.
    $( Syllogism inference.  (Contributed by Peter Mazsa, 18-Sep-2022.) $)
    syl21anbrc $p |- ( ph -> ta ) $=
      ( wa jca31 sylibr ) ABCJDJEABCDFGHKIL $.
  $}

  ${
    3imp3i2an.1 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
    3imp3i2an.2 $e |- ( ( ph /\ ch ) -> ta ) $.
    3imp3i2an.3 $e |- ( ( th /\ ta ) -> et ) $.
    $( An elimination deduction.  (Contributed by Alan Sare, 17-Oct-2017.)
       (Proof shortened by Wolf Lammen, 13-Apr-2022.) $)
    3imp3i2an $p |- ( ( ph /\ ps /\ ch ) -> et ) $=
      ( w3a 3adant2 syl2anc ) ABCJDEFGACEBHKIL $.
  $}

  ${
    3anim123i.1 $e |- ( ph -> ps ) $.
    3anim123i.2 $e |- ( ch -> th ) $.
    3anim123i.3 $e |- ( ta -> et ) $.
    $( Join antecedents and consequents with conjunction.  (Contributed by NM,
       8-Apr-1994.) $)
    3anim123i $p |- ( ( ph /\ ch /\ ta ) -> ( ps /\ th /\ et ) ) $=
      ( w3a 3ad2ant1 3ad2ant2 3ad2ant3 3jca ) ACEJBDFACBEGKCADEHLEAFCIMN $.
  $}

  ${
    3animi.1 $e |- ( ph -> ps ) $.
    $( Add two conjuncts to antecedent and consequent.  (Contributed by Jeff
       Hankins, 16-Aug-2009.) $)
    3anim1i $p |- ( ( ph /\ ch /\ th ) -> ( ps /\ ch /\ th ) ) $=
      ( id 3anim123i ) ABCCDDECFDFG $.

    $( Add two conjuncts to antecedent and consequent.  (Contributed by AV,
       21-Nov-2019.) $)
    3anim2i $p |- ( ( ch /\ ph /\ th ) -> ( ch /\ ps /\ th ) ) $=
      ( id 3anim123i ) CCABDDCFEDFG $.

    $( Add two conjuncts to antecedent and consequent.  (Contributed by Jeff
       Hankins, 19-Aug-2009.) $)
    3anim3i $p |- ( ( ch /\ th /\ ph ) -> ( ch /\ th /\ ps ) ) $=
      ( id 3anim123i ) CCDDABCFDFEG $.
  $}

  ${
    bi3.1 $e |- ( ph <-> ps ) $.
    bi3.2 $e |- ( ch <-> th ) $.
    bi3.3 $e |- ( ta <-> et ) $.
    $( Join 3 biconditionals with conjunction.  (Contributed by NM,
       21-Apr-1994.) $)
    3anbi123i $p |- ( ( ph /\ ch /\ ta ) <-> ( ps /\ th /\ et ) ) $=
      ( wa w3a anbi12i df-3an 3bitr4i ) ACJZEJBDJZFJACEKBDFKOPEFABCDGHLILACEMBD
      FMN $.

    $( Join 3 biconditionals with disjunction.  (Contributed by NM,
       17-May-1994.) $)
    3orbi123i $p |- ( ( ph \/ ch \/ ta ) <-> ( ps \/ th \/ et ) ) $=
      ( wo w3o orbi12i df-3or 3bitr4i ) ACJZEJBDJZFJACEKBDFKOPEFABCDGHLILACEMBD
      FMN $.
  $}

  ${
    3anbi1i.1 $e |- ( ph <-> ps ) $.
    $( Inference adding two conjuncts to each side of a biconditional.
       (Contributed by NM, 8-Sep-2006.) $)
    3anbi1i $p |- ( ( ph /\ ch /\ th ) <-> ( ps /\ ch /\ th ) ) $=
      ( biid 3anbi123i ) ABCCDDECFDFG $.

    $( Inference adding two conjuncts to each side of a biconditional.
       (Contributed by NM, 8-Sep-2006.) $)
    3anbi2i $p |- ( ( ch /\ ph /\ th ) <-> ( ch /\ ps /\ th ) ) $=
      ( biid 3anbi123i ) CCABDDCFEDFG $.

    $( Inference adding two conjuncts to each side of a biconditional.
       (Contributed by NM, 8-Sep-2006.) $)
    3anbi3i $p |- ( ( ch /\ th /\ ph ) <-> ( ch /\ th /\ ps ) ) $=
      ( biid 3anbi123i ) CCDDABCFDFEG $.
  $}

  ${
    3imp.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    $( Importation inference.  (Contributed by NM, 8-Apr-1994.) $)
    3imp $p |- ( ( ph /\ ps /\ ch ) -> th ) $=
      ( w3a wa df-3an imp31 sylbi ) ABCFABGCGDABCHABCDEIJ $.
  $}

  ${
    3impa.1 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
    $( Importation from double to triple conjunction.  (Contributed by NM,
       20-Aug-1995.) $)
    3impa $p |- ( ( ph /\ ps /\ ch ) -> th ) $=
      ( exp31 3imp ) ABCDABCDEFG $.
  $}

  ${
    ex3.1 $e |- ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) -> ta ) $.
    $( Apply ~ ex to a hypothesis with a 3-right-nested conjunction antecedent,
       with the antecedent of the assertion being a triple conjunction rather
       than a 2-right-nested conjunction.  (Contributed by Alan Sare,
       22-Apr-2018.) $)
    ex3 $p |- ( ( ph /\ ps /\ ch ) -> ( th -> ta ) ) $=
      ( wi wa ex 3impa ) ABCDEGABHCHDEFIJ $.
  $}

  ${
    3imp31.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    $( The importation inference ~ 3imp with commutation of the first and third
       conjuncts of the assertion relative to the hypothesis.  (Contributed by
       Alan Sare, 11-Sep-2016.) $)
    3imp31 $p |- ( ( ch /\ ps /\ ph ) -> th ) $=
      ( com13 3imp ) CBADABCDEFG $.

    $( Importation inference.  (Contributed by Alan Sare, 17-Oct-2017.) $)
    3imp231 $p |- ( ( ps /\ ch /\ ph ) -> th ) $=
      ( com3l 3imp ) BCADABCDEFG $.

    $( The importation inference ~ 3imp with commutation of the first and
       second conjuncts of the assertion relative to the hypothesis.
       (Contributed by Alan Sare, 11-Sep-2016.)  (Revised to shorten ~ 3com12
       by Wolf Lammen, 23-Jun-2022.) $)
    3imp21 $p |- ( ( ps /\ ph /\ ch ) -> th ) $=
      ( com13 3imp231 ) CBADABCDEFG $.
  $}

  ${
    3impb.1 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
    $( Importation from double to triple conjunction.  (Contributed by NM,
       20-Aug-1995.) $)
    3impb $p |- ( ( ph /\ ps /\ ch ) -> th ) $=
      ( exp32 3imp ) ABCDABCDEFG $.
  $}

  ${
    3impia.1 $e |- ( ( ph /\ ps ) -> ( ch -> th ) ) $.
    $( Importation to triple conjunction.  (Contributed by NM, 13-Jun-2006.) $)
    3impia $p |- ( ( ph /\ ps /\ ch ) -> th ) $=
      ( wi ex 3imp ) ABCDABCDFEGH $.
  $}

  ${
    3impib.1 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
    $( Importation to triple conjunction.  (Contributed by NM, 13-Jun-2006.) $)
    3impib $p |- ( ( ph /\ ps /\ ch ) -> th ) $=
      ( expd 3imp ) ABCDABCDEFG $.
  $}

  ${
    3exp.1 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
    $( Exportation inference.  (Contributed by NM, 30-May-1994.) $)
    3exp $p |- ( ph -> ( ps -> ( ch -> th ) ) ) $=
      ( w3a pm3.2an3 syl8 ) ABCABCFDABCGEH $.

    $( Exportation from triple to double conjunction.  (Contributed by NM,
       20-Aug-1995.) $)
    3expa $p |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $=
      ( 3exp imp31 ) ABCDABCDEFG $.

    $( Exportation from triple to double conjunction.  (Contributed by NM,
       20-Aug-1995.) $)
    3expb $p |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $=
      ( 3exp imp32 ) ABCDABCDEFG $.

    $( Exportation from triple conjunction.  (Contributed by NM,
       19-May-2007.) $)
    3expia $p |- ( ( ph /\ ps ) -> ( ch -> th ) ) $=
      ( wi 3exp imp ) ABCDFABCDEGH $.

    $( Exportation from triple conjunction.  (Contributed by NM,
       19-May-2007.) $)
    3expib $p |- ( ph -> ( ( ps /\ ch ) -> th ) ) $=
      ( 3exp impd ) ABCDABCDEFG $.

    $( Commutation in antecedent.  Swap 1st and 3rd.  (Contributed by NM,
       28-Jan-1996.)  (Proof shortened by Andrew Salmon, 13-May-2011.) $)
    3com12 $p |- ( ( ps /\ ph /\ ch ) -> th ) $=
      ( w3a 3ancoma sylbi ) BACFABCFDBACGEH $.

    $( Commutation in antecedent.  Swap 1st and 3rd.  (Contributed by NM,
       28-Jan-1996.) $)
    3com13 $p |- ( ( ch /\ ps /\ ph ) -> th ) $=
      ( w3a 3anrev sylbi ) CBAFABCFDCBAGEH $.

    $( Commutation in antecedent.  Swap 2nd and 3rd.  (Contributed by NM,
       28-Jan-1996.) $)
    3com23 $p |- ( ( ph /\ ch /\ ps ) -> th ) $=
      ( 3exp com23 3imp ) ACBDABCDABCDEFGH $.

    $( Commutation in antecedent.  Rotate left.  (Contributed by NM,
       28-Jan-1996.) $)
    3coml $p |- ( ( ps /\ ch /\ ph ) -> th ) $=
      ( 3com23 3com13 ) ACBDABCDEFG $.

    $( Commutation in antecedent.  Rotate right.  (Contributed by NM,
       28-Jan-1996.) $)
    3comr $p |- ( ( ch /\ ph /\ ps ) -> th ) $=
      ( 3coml ) BCADABCDEFF $.

    $( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       16-Feb-2008.) $)
    3adant3r1 $p |- ( ( ph /\ ( ta /\ ps /\ ch ) ) -> th ) $=
      ( 3expb 3adantr1 ) ABCDEABCDFGH $.

    $( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       17-Feb-2008.) $)
    3adant3r2 $p |- ( ( ph /\ ( ps /\ ta /\ ch ) ) -> th ) $=
      ( 3expb 3adantr2 ) ABCDEABCDFGH $.

    $( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       18-Feb-2008.) $)
    3adant3r3 $p |- ( ( ph /\ ( ps /\ ch /\ ta ) ) -> th ) $=
      ( 3expb 3adantr3 ) ABCDEABCDFGH $.
  $}

  ${
    ad4ant3.1 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
    $( Deduction adding conjuncts to antecedent.  (Contributed by Alan Sare,
       17-Oct-2017.)  (Proof shortened by Wolf Lammen, 14-Apr-2022.) $)
    ad4ant123 $p |- ( ( ( ( ph /\ ps ) /\ ch ) /\ ta ) -> th ) $=
      ( wa 3expa adantr ) ABGCGDEABCDFHI $.

    $( Deduction adding conjuncts to antecedent.  (Contributed by Alan Sare,
       17-Oct-2017.)  (Proof shortened by Wolf Lammen, 14-Apr-2022.) $)
    ad4ant124 $p |- ( ( ( ( ph /\ ps ) /\ ta ) /\ ch ) -> th ) $=
      ( wa 3expa adantlr ) ABGCDEABCDFHI $.

    $( Deduction adding conjuncts to antecedent.  (Contributed by Alan Sare,
       17-Oct-2017.)  (Proof shortened by Wolf Lammen, 14-Apr-2022.) $)
    ad4ant134 $p |- ( ( ( ( ph /\ ta ) /\ ps ) /\ ch ) -> th ) $=
      ( 3expa adantllr ) ABCDEABCDFGH $.

    $( Deduction adding conjuncts to antecedent.  (Contributed by Alan Sare,
       17-Oct-2017.)  (Proof shortened by Wolf Lammen, 14-Apr-2022.) $)
    ad4ant234 $p |- ( ( ( ( ta /\ ph ) /\ ps ) /\ ch ) -> th ) $=
      ( 3expa adantlll ) ABCDEABCDFGH $.
  $}

  ${
    3an1rs.1 $e |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ta ) $.
    $( Swap conjuncts.  (Contributed by NM, 16-Dec-2007.) $)
    3an1rs $p |- ( ( ( ph /\ ps /\ th ) /\ ch ) -> ta ) $=
      ( w3a wi ex 3exp com34 3imp imp ) ABDGCEABDCEHABCDEABCDEHABCGDEFIJKLM $.
  $}

  ${
    3imp1.1 $e |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $.
    $( Importation to left triple conjunction.  (Contributed by NM,
       24-Feb-2005.) $)
    3imp1 $p |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ta ) $=
      ( w3a wi 3imp imp ) ABCGDEABCDEHFIJ $.

    $( Importation deduction for triple conjunction.  (Contributed by NM,
       26-Oct-2006.) $)
    3impd $p |- ( ph -> ( ( ps /\ ch /\ th ) -> ta ) ) $=
      ( w3a wi com4l 3imp com12 ) BCDGAEBCDAEHABCDEFIJK $.

    $( Importation to right triple conjunction.  (Contributed by NM,
       26-Oct-2006.) $)
    3imp2 $p |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> ta ) $=
      ( w3a 3impd imp ) ABCDGEABCDEFHI $.
  $}

  ${
    3exp1.1 $e |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ta ) $.
    $( Exportation from left triple conjunction.  (Contributed by NM,
       24-Feb-2005.) $)
    3exp1 $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $=
      ( wi w3a ex 3exp ) ABCDEGABCHDEFIJ $.
  $}

  ${
    3expd.1 $e |- ( ph -> ( ( ps /\ ch /\ th ) -> ta ) ) $.
    $( Exportation deduction for triple conjunction.  (Contributed by NM,
       26-Oct-2006.) $)
    3expd $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $=
      ( wi w3a com12 3exp com4r ) BCDAEBCDAEGABCDHEFIJK $.
  $}

  ${
    3exp2.1 $e |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> ta ) $.
    $( Exportation from right triple conjunction.  (Contributed by NM,
       26-Oct-2006.) $)
    3exp2 $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $=
      ( w3a ex 3expd ) ABCDEABCDGEFHI $.
  $}

  ${
    exp5o.1 $e |- ( ( ph /\ ps /\ ch ) -> ( ( th /\ ta ) -> et ) ) $.
    $( A triple exportation inference.  (Contributed by Jeff Hankins,
       8-Jul-2009.) $)
    exp5o $p |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $=
      ( wi w3a expd 3exp ) ABCDEFHHABCIDEFGJK $.
  $}

  ${
    exp516.1 $e |- ( ( ( ph /\ ( ps /\ ch /\ th ) ) /\ ta ) -> et ) $.
    $( A triple exportation inference.  (Contributed by Jeff Hankins,
       8-Jul-2009.) $)
    exp516 $p |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $=
      ( wi w3a exp31 3expd ) ABCDEFHABCDIEFGJK $.
  $}

  ${
    exp520.1 $e |- ( ( ( ph /\ ps /\ ch ) /\ ( th /\ ta ) ) -> et ) $.
    $( A triple exportation inference.  (Contributed by Jeff Hankins,
       8-Jul-2009.) $)
    exp520 $p |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $=
      ( w3a wa ex exp5o ) ABCDEFABCHDEIFGJK $.
  $}

  ${
    3anassrs.1 $e |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> ta ) $.
    $( Associative law for conjunction applied to antecedent (eliminates
       syllogism).  (Contributed by Mario Carneiro, 4-Jan-2017.) $)
    3anassrs $p |- ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) -> ta ) $=
      ( 3exp2 imp41 ) ABCDEABCDEFGH $.
  $}

  ${
    3adant1l.1 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
    $( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       8-Jan-2006.) $)
    3adant1l $p |- ( ( ( ta /\ ph ) /\ ps /\ ch ) -> th ) $=
      ( wa 3expb adantll 3impb ) EAGBCDABCGDEABCDFHIJ $.

    $( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       8-Jan-2006.) $)
    3adant1r $p |- ( ( ( ph /\ ta ) /\ ps /\ ch ) -> th ) $=
      ( wa 3expb adantlr 3impb ) AEGBCDABCGDEABCDFHIJ $.

    $( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       8-Jan-2006.) $)
    3adant2l $p |- ( ( ph /\ ( ta /\ ps ) /\ ch ) -> th ) $=
      ( wa 3com12 3adant1l ) EBGACDBACDEABCDFHIH $.

    $( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       8-Jan-2006.) $)
    3adant2r $p |- ( ( ph /\ ( ps /\ ta ) /\ ch ) -> th ) $=
      ( wa 3com12 3adant1r ) BEGACDBACDEABCDFHIH $.

    $( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       8-Jan-2006.) $)
    3adant3l $p |- ( ( ph /\ ps /\ ( ta /\ ch ) ) -> th ) $=
      ( wa 3com13 3adant1l ) ECGBADCBADEABCDFHIH $.

    $( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       8-Jan-2006.) $)
    3adant3r $p |- ( ( ph /\ ps /\ ( ch /\ ta ) ) -> th ) $=
      ( wa 3com13 3adant1r ) CEGBADCBADEABCDFHIH $.
  $}

  ${
    ad5ant.1 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
    $( Deduction adding conjuncts to antecedent.  (Contributed by Alan Sare,
       17-Oct-2017.)  (Proof shortened by Wolf Lammen, 14-Apr-2022.) $)
    ad5ant245 $p |- ( ( ( ( ( ta /\ ph ) /\ et ) /\ ps ) /\ ch ) -> th ) $=
      ( wa 3adant1l ad4ant134 ) EAHBCDFABCDEGIJ $.

    $( Deduction adding conjuncts to antecedent.  (Contributed by Alan Sare,
       17-Oct-2017.)  (Proof shortened by Wolf Lammen, 14-Apr-2022.) $)
    ad5ant234 $p |- ( ( ( ( ( ta /\ ph ) /\ ps ) /\ ch ) /\ et ) -> th ) $=
      ( wa ad4ant234 adantr ) EAHBHCHDFABCDEGIJ $.

    $( Deduction adding conjuncts to antecedent.  (Contributed by Alan Sare,
       17-Oct-2017.)  (Proof shortened by Wolf Lammen, 14-Apr-2022.) $)
    ad5ant235 $p |- ( ( ( ( ( ta /\ ph ) /\ ps ) /\ et ) /\ ch ) -> th ) $=
      ( wa ad4ant234 adantlr ) EAHBHCDFABCDEGIJ $.

    $( Deduction adding conjuncts to antecedent.  (Contributed by Alan Sare,
       17-Oct-2017.)  (Proof shortened by Wolf Lammen, 23-Jun-2022.) $)
    ad5ant123 $p |- ( ( ( ( ( ph /\ ps ) /\ ch ) /\ ta ) /\ et ) -> th ) $=
      ( wa 3expa ad2antrr ) ABHCHDEFABCDGIJ $.

    $( Deduction adding conjuncts to antecedent.  (Contributed by Alan Sare,
       17-Oct-2017.)  (Proof shortened by Wolf Lammen, 23-Jun-2022.) $)
    ad5ant124 $p |- ( ( ( ( ( ph /\ ps ) /\ ta ) /\ ch ) /\ et ) -> th ) $=
      ( wa ad4ant124 adantr ) ABHEHCHDFABCDEGIJ $.

    $( Deduction adding conjuncts to antecedent.  (Contributed by Alan Sare,
       17-Oct-2017.)  (Proof shortened by Wolf Lammen, 23-Jun-2022.) $)
    ad5ant125 $p |- ( ( ( ( ( ph /\ ps ) /\ ta ) /\ et ) /\ ch ) -> th ) $=
      ( wa wi 3expia 2a1d imp41 ) ABHZEFCDMCDIEFABCDGJKL $.

    $( Deduction adding conjuncts to antecedent.  (Contributed by Alan Sare,
       17-Oct-2017.)  (Proof shortened by Wolf Lammen, 23-Jun-2022.) $)
    ad5ant134 $p |- ( ( ( ( ( ph /\ ta ) /\ ps ) /\ ch ) /\ et ) -> th ) $=
      ( wa ad4ant134 adantr ) AEHBHCHDFABCDEGIJ $.

    $( Deduction adding conjuncts to antecedent.  (Contributed by Alan Sare,
       17-Oct-2017.)  (Proof shortened by Wolf Lammen, 23-Jun-2022.) $)
    ad5ant135 $p |- ( ( ( ( ( ph /\ ta ) /\ ps ) /\ et ) /\ ch ) -> th ) $=
      ( wa ad4ant134 adantlr ) AEHBHCDFABCDEGIJ $.

    $( Deduction adding conjuncts to antecedent.  (Contributed by Alan Sare,
       17-Oct-2017.)  (Proof shortened by Wolf Lammen, 23-Jun-2022.) $)
    ad5ant145 $p |- ( ( ( ( ( ph /\ ta ) /\ et ) /\ ps ) /\ ch ) -> th ) $=
      ( wa ad4ant134 adantllr ) AEHBCDFABCDEGIJ $.
  $}

  ${
    sylXanc.1 $e |- ( ph -> ps ) $.
    sylXanc.2 $e |- ( ph -> ch ) $.
    sylXanc.3 $e |- ( ph -> th ) $.
    ${
      syl12anc.4 $e |- ( ( ps /\ ( ch /\ th ) ) -> ta ) $.
      $( Syllogism combined with contraction.  (Contributed by Jeff Hankins,
         1-Aug-2009.) $)
      syl12anc $p |- ( ph -> ta ) $=
        ( wa jca32 syl ) ABCDJJEABCDFGHKIL $.
    $}

    ${
      syl21anc.4 $e |- ( ( ( ps /\ ch ) /\ th ) -> ta ) $.
      $( Syllogism combined with contraction.  (Contributed by Jeff Hankins,
         1-Aug-2009.) $)
      syl21anc $p |- ( ph -> ta ) $=
        ( wa jca31 syl ) ABCJDJEABCDFGHKIL $.
    $}

    ${
      syl111anc.4 $e |- ( ( ps /\ ch /\ th ) -> ta ) $.
      $( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
      syl3anc $p |- ( ph -> ta ) $=
        ( w3a 3jca syl ) ABCDJEABCDFGHKIL $.
    $}

    sylXanc.4 $e |- ( ph -> ta ) $.
    ${
      syl22anc.5 $e |- ( ( ( ps /\ ch ) /\ ( th /\ ta ) ) -> et ) $.
      $( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
      syl22anc $p |- ( ph -> et ) $=
        ( wa jca syl12anc ) ABCLDEFABCGHMIJKN $.
    $}

    ${
      syl13anc.5 $e |- ( ( ps /\ ( ch /\ th /\ ta ) ) -> et ) $.
      $( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
      syl13anc $p |- ( ph -> et ) $=
        ( w3a 3jca syl2anc ) ABCDELFGACDEHIJMKN $.
    $}

    ${
      syl31anc.5 $e |- ( ( ( ps /\ ch /\ th ) /\ ta ) -> et ) $.
      $( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
      syl31anc $p |- ( ph -> et ) $=
        ( w3a 3jca syl2anc ) ABCDLEFABCDGHIMJKN $.
    $}

    ${
      syl112anc.5 $e |- ( ( ps /\ ch /\ ( th /\ ta ) ) -> et ) $.
      $( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
      syl112anc $p |- ( ph -> et ) $=
        ( wa jca syl3anc ) ABCDELFGHADEIJMKN $.
    $}

    ${
      syl121anc.5 $e |- ( ( ps /\ ( ch /\ th ) /\ ta ) -> et ) $.
      $( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
      syl121anc $p |- ( ph -> et ) $=
        ( wa jca syl3anc ) ABCDLEFGACDHIMJKN $.
    $}

    ${
      syl211anc.5 $e |- ( ( ( ps /\ ch ) /\ th /\ ta ) -> et ) $.
      $( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
      syl211anc $p |- ( ph -> et ) $=
        ( wa jca syl3anc ) ABCLDEFABCGHMIJKN $.
    $}

    sylXanc.5 $e |- ( ph -> et ) $.
    ${
      syl23anc.6 $e |- ( ( ( ps /\ ch ) /\ ( th /\ ta /\ et ) ) -> ze ) $.
      $( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
      syl23anc $p |- ( ph -> ze ) $=
        ( wa jca syl13anc ) ABCNDEFGABCHIOJKLMP $.
    $}

    ${
      syl32anc.6 $e |- ( ( ( ps /\ ch /\ th ) /\ ( ta /\ et ) ) -> ze ) $.
      $( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
      syl32anc $p |- ( ph -> ze ) $=
        ( wa jca syl31anc ) ABCDEFNGHIJAEFKLOMP $.
    $}

    ${
      syl122anc.6 $e |- ( ( ps /\ ( ch /\ th ) /\ ( ta /\ et ) ) -> ze ) $.
      $( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
      syl122anc $p |- ( ph -> ze ) $=
        ( wa jca syl121anc ) ABCDEFNGHIJAEFKLOMP $.
    $}

    ${
      syl212anc.6 $e |- ( ( ( ps /\ ch ) /\ th /\ ( ta /\ et ) ) -> ze ) $.
      $( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
      syl212anc $p |- ( ph -> ze ) $=
        ( wa jca syl211anc ) ABCDEFNGHIJAEFKLOMP $.
    $}

    ${
      syl221anc.6 $e |- ( ( ( ps /\ ch ) /\ ( th /\ ta ) /\ et ) -> ze ) $.
      $( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
      syl221anc $p |- ( ph -> ze ) $=
        ( wa jca syl211anc ) ABCDENFGHIADEJKOLMP $.
    $}

    ${
      syl113anc.6 $e |- ( ( ps /\ ch /\ ( th /\ ta /\ et ) ) -> ze ) $.
      $( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
      syl113anc $p |- ( ph -> ze ) $=
        ( w3a 3jca syl3anc ) ABCDEFNGHIADEFJKLOMP $.
    $}

    ${
      syl131anc.6 $e |- ( ( ps /\ ( ch /\ th /\ ta ) /\ et ) -> ze ) $.
      $( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
      syl131anc $p |- ( ph -> ze ) $=
        ( w3a 3jca syl3anc ) ABCDENFGHACDEIJKOLMP $.
    $}

    ${
      syl311anc.6 $e |- ( ( ( ps /\ ch /\ th ) /\ ta /\ et ) -> ze ) $.
      $( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
      syl311anc $p |- ( ph -> ze ) $=
        ( w3a 3jca syl3anc ) ABCDNEFGABCDHIJOKLMP $.
    $}

    sylXanc.6 $e |- ( ph -> ze ) $.
    ${
      syl33anc.7 $e |- ( ( ( ps /\ ch /\ th ) /\ ( ta /\ et /\ ze ) )
           -> si ) $.
      $( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
      syl33anc $p |- ( ph -> si ) $=
        ( w3a 3jca syl13anc ) ABCDPEFGHABCDIJKQLMNOR $.
    $}

    ${
      syl222anc.7 $e |- ( ( ( ps /\ ch ) /\ ( th /\ ta ) /\ ( et /\ ze ) )
           -> si ) $.
      $( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
      syl222anc $p |- ( ph -> si ) $=
        ( wa jca syl221anc ) ABCDEFGPHIJKLAFGMNQOR $.
    $}

    ${
      syl123anc.7 $e |- ( ( ps /\ ( ch /\ th ) /\ ( ta /\ et /\ ze ) )
           -> si ) $.
      $( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
      syl123anc $p |- ( ph -> si ) $=
        ( wa jca syl113anc ) ABCDPEFGHIACDJKQLMNOR $.
    $}

    ${
      syl132anc.7 $e |- ( ( ps /\ ( ch /\ th /\ ta ) /\ ( et /\ ze ) )
           -> si ) $.
      $( Syllogism combined with contraction.  (Contributed by NM,
         11-Jul-2012.) $)
      syl132anc $p |- ( ph -> si ) $=
        ( wa jca syl131anc ) ABCDEFGPHIJKLAFGMNQOR $.
    $}

    ${
      syl213anc.7 $e |- ( ( ( ps /\ ch ) /\ th /\ ( ta /\ et /\ ze ) )
           -> si ) $.
      $( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
      syl213anc $p |- ( ph -> si ) $=
        ( wa jca syl113anc ) ABCPDEFGHABCIJQKLMNOR $.
    $}

    ${
      syl231anc.7 $e |- ( ( ( ps /\ ch ) /\ ( th /\ ta /\ et ) /\ ze )
           -> si ) $.
      $( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
      syl231anc $p |- ( ph -> si ) $=
        ( wa jca syl131anc ) ABCPDEFGHABCIJQKLMNOR $.
    $}

    ${
      syl312anc.7 $e |- ( ( ( ps /\ ch /\ th ) /\ ta /\ ( et /\ ze ) )
           -> si ) $.
      $( Syllogism combined with contraction.  (Contributed by NM,
         11-Jul-2012.) $)
      syl312anc $p |- ( ph -> si ) $=
        ( wa jca syl311anc ) ABCDEFGPHIJKLAFGMNQOR $.
    $}

    ${
      syl321anc.7 $e |- ( ( ( ps /\ ch /\ th ) /\ ( ta /\ et ) /\ ze )
           -> si ) $.
      $( Syllogism combined with contraction.  (Contributed by NM,
         11-Jul-2012.) $)
      syl321anc $p |- ( ph -> si ) $=
        ( wa jca syl311anc ) ABCDEFPGHIJKAEFLMQNOR $.
    $}

    sylXanc.7 $e |- ( ph -> si ) $.
    ${
      syl133anc.8 $e |- ( ( ps /\ ( ch /\ th /\ ta ) /\ ( et /\ ze /\ si ) )
           -> rh ) $.
      $( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
      syl133anc $p |- ( ph -> rh ) $=
        ( w3a 3jca syl131anc ) ABCDEFGHRIJKLMAFGHNOPSQT $.
    $}

    ${
      syl313anc.8 $e |- ( ( ( ps /\ ch /\ th ) /\ ta /\ ( et /\ ze /\ si ) )
           -> rh ) $.
      $( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
      syl313anc $p |- ( ph -> rh ) $=
        ( w3a 3jca syl311anc ) ABCDEFGHRIJKLMAFGHNOPSQT $.
    $}

    ${
      syl331anc.8 $e |- ( ( ( ps /\ ch /\ th ) /\ ( ta /\ et /\ ze ) /\ si )
           -> rh ) $.
      $( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
      syl331anc $p |- ( ph -> rh ) $=
        ( w3a 3jca syl311anc ) ABCDEFGRHIJKLAEFGMNOSPQT $.
    $}

    ${
      syl223anc.8 $e |- ( ( ( ps /\ ch ) /\ ( th /\ ta ) /\ ( et /\ ze /\ si )
          ) -> rh ) $.
      $( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
      syl223anc $p |- ( ph -> rh ) $=
        ( wa jca syl213anc ) ABCDERFGHIJKADELMSNOPQT $.
    $}

    ${
      syl232anc.8 $e |- ( ( ( ps /\ ch ) /\ ( th /\ ta /\ et ) /\ ( ze /\ si )
          ) -> rh ) $.
      $( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
      syl232anc $p |- ( ph -> rh ) $=
        ( wa jca syl231anc ) ABCDEFGHRIJKLMNAGHOPSQT $.
    $}

    ${
      syl322anc.8 $e |- ( ( ( ps /\ ch /\ th ) /\ ( ta /\ et ) /\ ( ze /\ si )
          ) -> rh ) $.
      $( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
      syl322anc $p |- ( ph -> rh ) $=
        ( wa jca syl321anc ) ABCDEFGHRIJKLMNAGHOPSQT $.
    $}

    sylXanc.8 $e |- ( ph -> rh ) $.
    ${
      syl233anc.9 $e |- ( ( ( ps /\ ch ) /\ ( th /\ ta /\ et ) /\ ( ze /\ si /\
          rh ) ) -> mu ) $.
      $( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
      syl233anc $p |- ( ph -> mu ) $=
        ( wa jca syl133anc ) ABCTDEFGHIJABCKLUAMNOPQRSUB $.
    $}

    ${
      syl323anc.9 $e |- ( ( ( ps /\ ch /\ th ) /\ ( ta /\ et ) /\ ( ze /\ si /\
          rh ) ) -> mu ) $.
      $( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
      syl323anc $p |- ( ph -> mu ) $=
        ( wa jca syl313anc ) ABCDEFTGHIJKLMAEFNOUAPQRSUB $.
    $}

    ${
      syl332anc.9 $e |- ( ( ( ps /\ ch /\ th ) /\ ( ta /\ et /\ ze ) /\ ( si /\
          rh ) ) -> mu ) $.
      $( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
      syl332anc $p |- ( ph -> mu ) $=
        ( wa jca syl331anc ) ABCDEFGHITJKLMNOPAHIQRUASUB $.
    $}

    sylXanc.9 $e |- ( ph -> mu ) $.
    ${
      syl333anc.10 $e |- ( ( ( ps /\ ch /\ th ) /\ ( ta /\ et /\ ze )
          /\ ( si /\ rh /\ mu ) ) -> la ) $.
      $( A syllogism inference combined with contraction.  (Contributed by NM,
         10-Mar-2012.) $)
      syl333anc $p |- ( ph -> la ) $=
        ( w3a 3jca syl331anc ) ABCDEFGHIJUBKLMNOPQAHIJRSTUCUAUD $.
    $}
  $}

  ${
    syl3an1.1 $e |- ( ph -> ps ) $.
    syl3an1.2 $e |- ( ( ps /\ ch /\ th ) -> ta ) $.
    $( A syllogism inference.  (Contributed by NM, 22-Aug-1995.) $)
    syl3an1 $p |- ( ( ph /\ ch /\ th ) -> ta ) $=
      ( w3a 3anim1i syl ) ACDHBCDHEABCDFIGJ $.
  $}

  ${
    syl3an2.1 $e |- ( ph -> ch ) $.
    syl3an2.2 $e |- ( ( ps /\ ch /\ th ) -> ta ) $.
    $( A syllogism inference.  (Contributed by NM, 22-Aug-1995.) $)
    syl3an2 $p |- ( ( ps /\ ph /\ th ) -> ta ) $=
      ( wi 3exp syl5 3imp ) BADEACBDEHFBCDEGIJK $.
  $}

  ${
    syl3an3.1 $e |- ( ph -> th ) $.
    syl3an3.2 $e |- ( ( ps /\ ch /\ th ) -> ta ) $.
    $( A syllogism inference.  (Contributed by NM, 22-Aug-1995.) $)
    syl3an3 $p |- ( ( ps /\ ch /\ ph ) -> ta ) $=
      ( 3exp syl7 3imp ) BCAEADBCEFBCDEGHIJ $.
  $}

  ${
    syl3an1b.1 $e |- ( ph <-> ps ) $.
    syl3an1b.2 $e |- ( ( ps /\ ch /\ th ) -> ta ) $.
    $( A syllogism inference.  (Contributed by NM, 22-Aug-1995.) $)
    syl3an1b $p |- ( ( ph /\ ch /\ th ) -> ta ) $=
      ( biimpi syl3an1 ) ABCDEABFHGI $.
  $}

  ${
    syl3an2b.1 $e |- ( ph <-> ch ) $.
    syl3an2b.2 $e |- ( ( ps /\ ch /\ th ) -> ta ) $.
    $( A syllogism inference.  (Contributed by NM, 22-Aug-1995.) $)
    syl3an2b $p |- ( ( ps /\ ph /\ th ) -> ta ) $=
      ( biimpi syl3an2 ) ABCDEACFHGI $.
  $}

  ${
    syl3an3b.1 $e |- ( ph <-> th ) $.
    syl3an3b.2 $e |- ( ( ps /\ ch /\ th ) -> ta ) $.
    $( A syllogism inference.  (Contributed by NM, 22-Aug-1995.) $)
    syl3an3b $p |- ( ( ps /\ ch /\ ph ) -> ta ) $=
      ( biimpi syl3an3 ) ABCDEADFHGI $.
  $}

  ${
    syl3an1br.1 $e |- ( ps <-> ph ) $.
    syl3an1br.2 $e |- ( ( ps /\ ch /\ th ) -> ta ) $.
    $( A syllogism inference.  (Contributed by NM, 22-Aug-1995.) $)
    syl3an1br $p |- ( ( ph /\ ch /\ th ) -> ta ) $=
      ( biimpri syl3an1 ) ABCDEBAFHGI $.
  $}

  ${
    syl3an2br.1 $e |- ( ch <-> ph ) $.
    syl3an2br.2 $e |- ( ( ps /\ ch /\ th ) -> ta ) $.
    $( A syllogism inference.  (Contributed by NM, 22-Aug-1995.) $)
    syl3an2br $p |- ( ( ps /\ ph /\ th ) -> ta ) $=
      ( biimpri syl3an2 ) ABCDECAFHGI $.
  $}

  ${
    syl3an3br.1 $e |- ( th <-> ph ) $.
    syl3an3br.2 $e |- ( ( ps /\ ch /\ th ) -> ta ) $.
    $( A syllogism inference.  (Contributed by NM, 22-Aug-1995.) $)
    syl3an3br $p |- ( ( ps /\ ch /\ ph ) -> ta ) $=
      ( biimpri syl3an3 ) ABCDEDAFHGI $.
  $}

  ${
    syl3an.1 $e |- ( ph -> ps ) $.
    syl3an.2 $e |- ( ch -> th ) $.
    syl3an.3 $e |- ( ta -> et ) $.
    syl3an.4 $e |- ( ( ps /\ th /\ et ) -> ze ) $.
    $( A triple syllogism inference.  (Contributed by NM, 13-May-2004.) $)
    syl3an $p |- ( ( ph /\ ch /\ ta ) -> ze ) $=
      ( w3a 3anim123i syl ) ACELBDFLGABCDEFHIJMKN $.
  $}

  ${
    syl3anb.1 $e |- ( ph <-> ps ) $.
    syl3anb.2 $e |- ( ch <-> th ) $.
    syl3anb.3 $e |- ( ta <-> et ) $.
    syl3anb.4 $e |- ( ( ps /\ th /\ et ) -> ze ) $.
    $( A triple syllogism inference.  (Contributed by NM, 15-Oct-2005.) $)
    syl3anb $p |- ( ( ph /\ ch /\ ta ) -> ze ) $=
      ( w3a 3anbi123i sylbi ) ACELBDFLGABCDEFHIJMKN $.
  $}

  ${
    syl3anbr.1 $e |- ( ps <-> ph ) $.
    syl3anbr.2 $e |- ( th <-> ch ) $.
    syl3anbr.3 $e |- ( et <-> ta ) $.
    syl3anbr.4 $e |- ( ( ps /\ th /\ et ) -> ze ) $.
    $( A triple syllogism inference.  (Contributed by NM, 29-Dec-2011.) $)
    syl3anbr $p |- ( ( ph /\ ch /\ ta ) -> ze ) $=
      ( bicomi syl3anb ) ABCDEFGBAHLDCILFEJLKM $.
  $}

  ${
    syld3an3.1 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
    syld3an3.2 $e |- ( ( ph /\ ps /\ th ) -> ta ) $.
    $( A syllogism inference.  (Contributed by NM, 20-May-2007.) $)
    syld3an3 $p |- ( ( ph /\ ps /\ ch ) -> ta ) $=
      ( w3a simp1 simp2 syl3anc ) ABCHABDEABCIABCJFGK $.
  $}

  ${
    syld3an1.1 $e |- ( ( ch /\ ps /\ th ) -> ph ) $.
    syld3an1.2 $e |- ( ( ph /\ ps /\ th ) -> ta ) $.
    $( A syllogism inference.  (Contributed by NM, 7-Jul-2008.) $)
    syld3an1 $p |- ( ( ch /\ ps /\ th ) -> ta ) $=
      ( 3com13 syld3an3 ) DBCEDBCAECBDAFHABDEGHIH $.
  $}

  ${
    syld3an2.1 $e |- ( ( ph /\ ch /\ th ) -> ps ) $.
    syld3an2.2 $e |- ( ( ph /\ ps /\ th ) -> ta ) $.
    $( A syllogism inference.  (Contributed by NM, 20-May-2007.) $)
    syld3an2 $p |- ( ( ph /\ ch /\ th ) -> ta ) $=
      ( 3com23 syld3an3 ) ADCEADCBEACDBFHABDEGHIH $.
  $}

  ${
    syl3anl1.1 $e |- ( ph -> ps ) $.
    syl3anl1.2 $e |- ( ( ( ps /\ ch /\ th ) /\ ta ) -> et ) $.
    $( A syllogism inference.  (Contributed by NM, 24-Feb-2005.) $)
    syl3anl1 $p |- ( ( ( ph /\ ch /\ th ) /\ ta ) -> et ) $=
      ( w3a 3anim1i sylan ) ACDIBCDIEFABCDGJHK $.
  $}

  ${
    syl3anl2.1 $e |- ( ph -> ch ) $.
    syl3anl2.2 $e |- ( ( ( ps /\ ch /\ th ) /\ ta ) -> et ) $.
    $( A syllogism inference.  (Contributed by NM, 24-Feb-2005.) $)
    syl3anl2 $p |- ( ( ( ps /\ ph /\ th ) /\ ta ) -> et ) $=
      ( w3a wi ex syl3an2 imp ) BADIEFABCDEFJGBCDIEFHKLM $.
  $}

  ${
    syl3anl3.1 $e |- ( ph -> th ) $.
    syl3anl3.2 $e |- ( ( ( ps /\ ch /\ th ) /\ ta ) -> et ) $.
    $( A syllogism inference.  (Contributed by NM, 24-Feb-2005.) $)
    syl3anl3 $p |- ( ( ( ps /\ ch /\ ph ) /\ ta ) -> et ) $=
      ( w3a 3anim3i sylan ) BCAIBCDIEFADBCGJHK $.
  $}

  ${
    syl3anl.1 $e |- ( ph -> ps ) $.
    syl3anl.2 $e |- ( ch -> th ) $.
    syl3anl.3 $e |- ( ta -> et ) $.
    syl3anl.4 $e |- ( ( ( ps /\ th /\ et ) /\ ze ) -> si ) $.
    $( A triple syllogism inference.  (Contributed by NM, 24-Dec-2006.) $)
    syl3anl $p |- ( ( ( ph /\ ch /\ ta ) /\ ze ) -> si ) $=
      ( w3a 3anim123i sylan ) ACEMBDFMGHABCDEFIJKNLO $.
  $}

  ${
    syl3anr1.1 $e |- ( ph -> ps ) $.
    syl3anr1.2 $e |- ( ( ch /\ ( ps /\ th /\ ta ) ) -> et ) $.
    $( A syllogism inference.  (Contributed by NM, 31-Jul-2007.) $)
    syl3anr1 $p |- ( ( ch /\ ( ph /\ th /\ ta ) ) -> et ) $=
      ( w3a 3anim1i sylan2 ) ADEICBDEIFABDEGJHK $.
  $}

  ${
    syl3anr2.1 $e |- ( ph -> th ) $.
    syl3anr2.2 $e |- ( ( ch /\ ( ps /\ th /\ ta ) ) -> et ) $.
    $( A syllogism inference.  (Contributed by NM, 1-Aug-2007.) $)
    syl3anr2 $p |- ( ( ch /\ ( ps /\ ph /\ ta ) ) -> et ) $=
      ( w3a ancoms syl3anl2 ) BAEICFABDECFGCBDEIFHJKJ $.
  $}

  ${
    syl3anr3.1 $e |- ( ph -> ta ) $.
    syl3anr3.2 $e |- ( ( ch /\ ( ps /\ th /\ ta ) ) -> et ) $.
    $( A syllogism inference.  (Contributed by NM, 23-Aug-2007.) $)
    syl3anr3 $p |- ( ( ch /\ ( ps /\ th /\ ph ) ) -> et ) $=
      ( w3a 3anim3i sylan2 ) BDAICBDEIFAEBDGJHK $.
  $}

  ${
    syldbl2.1 $e |- ( ( ph /\ ps ) -> ( ps -> th ) ) $.
    $( Stacked hypotheseis implies goal.  (Contributed by Stanislas Polu,
       9-Mar-2020.) $)
    syldbl2 $p |- ( ( ph /\ ps ) -> th ) $=
      ( wa com12 anabsi7 ) ABCABEBCDFG $.
  $}

  ${
    3impdi.1 $e |- ( ( ( ph /\ ps ) /\ ( ph /\ ch ) ) -> th ) $.
    $( Importation inference (undistribute conjunction).  (Contributed by NM,
       14-Aug-1995.) $)
    3impdi $p |- ( ( ph /\ ps /\ ch ) -> th ) $=
      ( anandis 3impb ) ABCDABCDEFG $.
  $}

  ${
    3impdir.1 $e |- ( ( ( ph /\ ps ) /\ ( ch /\ ps ) ) -> th ) $.
    $( Importation inference (undistribute conjunction).  (Contributed by NM,
       20-Aug-1995.) $)
    3impdir $p |- ( ( ph /\ ch /\ ps ) -> th ) $=
      ( anandirs 3impa ) ACBDACBDEFG $.
  $}

  ${
    3anidm12.1 $e |- ( ( ph /\ ph /\ ps ) -> ch ) $.
    $( Inference from idempotent law for conjunction.  (Contributed by NM,
       7-Mar-2008.) $)
    3anidm12 $p |- ( ( ph /\ ps ) -> ch ) $=
      ( 3expib anabsi5 ) ABCAABCDEF $.
  $}

  ${
    3anidm13.1 $e |- ( ( ph /\ ps /\ ph ) -> ch ) $.
    $( Inference from idempotent law for conjunction.  (Contributed by NM,
       7-Mar-2008.) $)
    3anidm13 $p |- ( ( ph /\ ps ) -> ch ) $=
      ( 3com23 3anidm12 ) ABCABACDEF $.
  $}

  ${
    3anidm23.1 $e |- ( ( ph /\ ps /\ ps ) -> ch ) $.
    $( Inference from idempotent law for conjunction.  (Contributed by NM,
       1-Feb-2007.) $)
    3anidm23 $p |- ( ( ph /\ ps ) -> ch ) $=
      ( 3expa anabss3 ) ABCABBCDEF $.
  $}

  ${
    syl2an3an.1 $e |- ( ph -> ps ) $.
    syl2an3an.2 $e |- ( ph -> ch ) $.
    syl2an3an.3 $e |- ( th -> ta ) $.
    syl2an3an.4 $e |- ( ( ps /\ ch /\ ta ) -> et ) $.
    $( ~ syl3an with antecedents in standard conjunction form.  (Contributed by
       Alan Sare, 31-Aug-2016.) $)
    syl2an3an $p |- ( ( ph /\ th ) -> et ) $=
      ( syl3an 3anidm12 ) ADFABACDEFGHIJKL $.
  $}

  ${
    syl2an23an.1 $e |- ( ph -> ps ) $.
    syl2an23an.2 $e |- ( ph -> ch ) $.
    syl2an23an.3 $e |- ( ( th /\ ph ) -> ta ) $.
    syl2an23an.4 $e |- ( ( ps /\ ch /\ ta ) -> et ) $.
    $( Deduction related to ~ syl3an with antecedents in standard conjunction
       form.  (Contributed by Alan Sare, 31-Aug-2016.) $)
    syl2an23an $p |- ( ( th /\ ph ) -> et ) $=
      ( wa wi 3exp sylc syl5 anabsi7 ) DAFDAKEAFIABCEFLGHBCEFJMNOP $.
  $}

  ${
    3ori.1 $e |- ( ph \/ ps \/ ch ) $.
    $( Infer implication from triple disjunction.  (Contributed by NM,
       26-Sep-2006.) $)
    3ori $p |- ( ( -. ph /\ -. ps ) -> ch ) $=
      ( wn wa wo ioran w3o df-3or mpbi ori sylbir ) AEBEFABGZECABHNCABCINCGDABC
      JKLM $.
  $}

  $( Disjunction of 3 antecedents.  (Contributed by NM, 8-Apr-1994.) $)
  3jao $p |- ( ( ( ph -> ps ) /\ ( ch -> ps ) /\ ( th -> ps ) ) ->
              ( ( ph \/ ch \/ th ) -> ps ) ) $=
    ( w3o wo wi w3a df-3or jao syl6 3imp biimtrid ) ACDEACFZDFZABGZCBGZDBGZHBAC
    DIPQROBGZPQNBGRSGABCJNBDJKLM $.

  $( Disjunction of 3 antecedents.  (Contributed by NM, 13-Sep-2011.) $)
  3jaob $p |- ( ( ( ph \/ ch \/ th ) -> ps ) <->
              ( ( ph -> ps ) /\ ( ch -> ps ) /\ ( th -> ps ) ) ) $=
    ( w3o wi w3a 3mix1 imim1i 3mix2 3mix3 3jca 3jao impbii ) ACDEZBFZABFZCBFZDB
    FZGPQRSAOBACDHICOBCADJIDOBDACKILABCDMN $.

  ${
    3jaoi.1 $e |- ( ph -> ps ) $.
    3jaoi.2 $e |- ( ch -> ps ) $.
    3jaoi.3 $e |- ( th -> ps ) $.
    $( Disjunction of 3 antecedents (inference).  (Contributed by NM,
       12-Sep-1995.) $)
    3jaoi $p |- ( ( ph \/ ch \/ th ) -> ps ) $=
      ( wi w3a w3o 3pm3.2i 3jao ax-mp ) ABHZCBHZDBHZIACDJBHNOPEFGKABCDLM $.
  $}

  ${
    3jaod.1 $e |- ( ph -> ( ps -> ch ) ) $.
    3jaod.2 $e |- ( ph -> ( th -> ch ) ) $.
    3jaod.3 $e |- ( ph -> ( ta -> ch ) ) $.
    $( Disjunction of 3 antecedents (deduction).  (Contributed by NM,
       14-Oct-2005.) $)
    3jaod $p |- ( ph -> ( ( ps \/ th \/ ta ) -> ch ) ) $=
      ( wi w3o 3jao syl3anc ) ABCIDCIECIBDEJCIFGHBCDEKL $.
  $}

  ${
    3jaoian.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    3jaoian.2 $e |- ( ( th /\ ps ) -> ch ) $.
    3jaoian.3 $e |- ( ( ta /\ ps ) -> ch ) $.
    $( Disjunction of 3 antecedents (inference).  (Contributed by NM,
       14-Oct-2005.) $)
    3jaoian $p |- ( ( ( ph \/ th \/ ta ) /\ ps ) -> ch ) $=
      ( w3o wi ex 3jaoi imp ) ADEIBCABCJDEABCFKDBCGKEBCHKLM $.
  $}

  ${
    3jaodan.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    3jaodan.2 $e |- ( ( ph /\ th ) -> ch ) $.
    3jaodan.3 $e |- ( ( ph /\ ta ) -> ch ) $.
    $( Disjunction of 3 antecedents (deduction).  (Contributed by NM,
       14-Oct-2005.) $)
    3jaodan $p |- ( ( ph /\ ( ps \/ th \/ ta ) ) -> ch ) $=
      ( w3o ex 3jaod imp ) ABDEICABCDEABCFJADCGJAECHJKL $.
  $}

  ${
    mpjao3dan.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    mpjao3dan.2 $e |- ( ( ph /\ th ) -> ch ) $.
    mpjao3dan.3 $e |- ( ( ph /\ ta ) -> ch ) $.
    mpjao3dan.4 $e |- ( ph -> ( ps \/ th \/ ta ) ) $.
    $( Eliminate a 3-way disjunction in a deduction.  (Contributed by Thierry
       Arnoux, 13-Apr-2018.) $)
    mpjao3dan $p |- ( ph -> ch ) $=
      ( wo jaodan w3o df-3or sylib mpjaodan ) ABDJZCEABCDFGKHABDELPEJIBDEMNO $.
  $}

  ${
    3jaao.1 $e |- ( ph -> ( ps -> ch ) ) $.
    3jaao.2 $e |- ( th -> ( ta -> ch ) ) $.
    3jaao.3 $e |- ( et -> ( ze -> ch ) ) $.
    $( Inference conjoining and disjoining the antecedents of three
       implications.  (Contributed by Jeff Hankins, 15-Aug-2009.)  (Proof
       shortened by Andrew Salmon, 13-May-2011.) $)
    3jaao $p |- ( ( ph /\ th /\ et ) -> ( ( ps \/ ta \/ ze ) -> ch ) ) $=
      ( w3a wi 3ad2ant1 3ad2ant2 3ad2ant3 3jaod ) ADFKBCEGADBCLFHMDAECLFINFAGCL
      DJOP $.
  $}

  $( Triple disjunction implies negated triple conjunction.  (Contributed by
     Jim Kingdon, 23-Dec-2018.) $)
  3ianorr $p |- ( ( -. ph \/ -. ps \/ -. ch ) -> -. ( ph /\ ps /\ ch ) ) $=
    ( wn w3a simp1 con3i simp2 simp3 3jaoi ) ADABCEZDBDCDKAABCFGKBABCHGKCABCIGJ
    $.

  ${
    syl3an9b.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    syl3an9b.2 $e |- ( th -> ( ch <-> ta ) ) $.
    syl3an9b.3 $e |- ( et -> ( ta <-> ze ) ) $.
    $( Nested syllogism inference conjoining 3 dissimilar antecedents.
       (Contributed by NM, 1-May-1995.) $)
    syl3an9b $p |- ( ( ph /\ th /\ et ) -> ( ps <-> ze ) ) $=
      ( wb wa sylan9bb 3impa ) ADFBGKADLBEFGABCDEHIMJMN $.
  $}

  ${
    bi3d.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    bi3d.2 $e |- ( ph -> ( th <-> ta ) ) $.
    bi3d.3 $e |- ( ph -> ( et <-> ze ) ) $.
    $( Deduction joining 3 equivalences to form equivalence of disjunctions.
       (Contributed by NM, 20-Apr-1994.) $)
    3orbi123d $p |- ( ph -> ( ( ps \/ th \/ et ) <-> ( ch \/ ta \/ ze ) ) ) $=
      ( wo w3o orbi12d df-3or 3bitr4g ) ABDKZFKCEKZGKBDFLCEGLAPQFGABCDEHIMJMBDF
      NCEGNO $.

    $( Deduction joining 3 equivalences to form equivalence of conjunctions.
       (Contributed by NM, 22-Apr-1994.) $)
    3anbi123d $p |- ( ph -> ( ( ps /\ th /\ et ) <-> ( ch /\ ta /\ ze ) ) ) $=
      ( wa w3a anbi12d df-3an 3bitr4g ) ABDKZFKCEKZGKBDFLCEGLAPQFGABCDEHIMJMBDF
      NCEGNO $.
  $}

  ${
    3anbi12d.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    3anbi12d.2 $e |- ( ph -> ( th <-> ta ) ) $.
    $( Deduction conjoining and adding a conjunct to equivalences.
       (Contributed by NM, 8-Sep-2006.) $)
    3anbi12d $p |- ( ph -> ( ( ps /\ th /\ et ) <-> ( ch /\ ta /\ et ) ) ) $=
      ( biidd 3anbi123d ) ABCDEFFGHAFIJ $.

    $( Deduction conjoining and adding a conjunct to equivalences.
       (Contributed by NM, 8-Sep-2006.) $)
    3anbi13d $p |- ( ph -> ( ( ps /\ et /\ th ) <-> ( ch /\ et /\ ta ) ) ) $=
      ( biidd 3anbi123d ) ABCFFDEGAFIHJ $.

    $( Deduction conjoining and adding a conjunct to equivalences.
       (Contributed by NM, 8-Sep-2006.) $)
    3anbi23d $p |- ( ph -> ( ( et /\ ps /\ th ) <-> ( et /\ ch /\ ta ) ) ) $=
      ( biidd 3anbi123d ) AFFBCDEAFIGHJ $.
  $}

  ${
    3anbi1d.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Deduction adding conjuncts to an equivalence.  (Contributed by NM,
       8-Sep-2006.) $)
    3anbi1d $p |- ( ph -> ( ( ps /\ th /\ ta ) <-> ( ch /\ th /\ ta ) ) ) $=
      ( biidd 3anbi12d ) ABCDDEFADGH $.

    $( Deduction adding conjuncts to an equivalence.  (Contributed by NM,
       8-Sep-2006.) $)
    3anbi2d $p |- ( ph -> ( ( th /\ ps /\ ta ) <-> ( th /\ ch /\ ta ) ) ) $=
      ( biidd 3anbi12d ) ADDBCEADGFH $.

    $( Deduction adding conjuncts to an equivalence.  (Contributed by NM,
       8-Sep-2006.) $)
    3anbi3d $p |- ( ph -> ( ( th /\ ta /\ ps ) <-> ( th /\ ta /\ ch ) ) ) $=
      ( biidd 3anbi13d ) ADDBCEADGFH $.
  $}

  ${
    3anim123d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    3anim123d.2 $e |- ( ph -> ( th -> ta ) ) $.
    3anim123d.3 $e |- ( ph -> ( et -> ze ) ) $.
    $( Deduction joining 3 implications to form implication of conjunctions.
       (Contributed by NM, 24-Feb-2005.) $)
    3anim123d $p |- ( ph -> ( ( ps /\ th /\ et ) -> ( ch /\ ta /\ ze ) ) ) $=
      ( wa w3a anim12d df-3an 3imtr4g ) ABDKZFKCEKZGKBDFLCEGLAPQFGABCDEHIMJMBDF
      NCEGNO $.

    $( Deduction joining 3 implications to form implication of disjunctions.
       (Contributed by NM, 4-Apr-1997.) $)
    3orim123d $p |- ( ph -> ( ( ps \/ th \/ et ) -> ( ch \/ ta \/ ze ) ) ) $=
      ( wo w3o orim12d df-3or 3imtr4g ) ABDKZFKCEKZGKBDFLCEGLAPQFGABCDEHIMJMBDF
      NCEGNO $.
  $}

  $( Rearrangement of 6 conjuncts.  (Contributed by NM, 13-Mar-1995.) $)
  an6 $p |- ( ( ( ph /\ ps /\ ch ) /\ ( th /\ ta /\ et ) ) <->
              ( ( ph /\ th ) /\ ( ps /\ ta ) /\ ( ch /\ et ) ) ) $=
    ( w3a wa df-3an anbi12i an4 anbi1i 3bitri bitr4i ) ABCGZDEFGZHZADHZBEHZHZCF
    HZHZRSUAGQABHZCHZDEHZFHZHUCUEHZUAHUBOUDPUFABCIDEFIJUCCUEFKUGTUAABDEKLMRSUAI
    N $.

  $( Analog of ~ an4 for triple conjunction.  (Contributed by Scott Fenton,
     16-Mar-2011.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)
  3an6 $p |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) /\ ( ta /\ et ) ) <->
                ( ( ph /\ ch /\ ta ) /\ ( ps /\ th /\ et ) ) ) $=
    ( w3a wa an6 bicomi ) ACEGBDFGHABHCDHEFHGACEBDFIJ $.

  $( Analog of ~ or4 for triple conjunction.  (Contributed by Scott Fenton,
     16-Mar-2011.) $)
  3or6 $p |- ( ( ( ph \/ ps ) \/ ( ch \/ th ) \/ ( ta \/ et ) ) <->
                ( ( ph \/ ch \/ ta ) \/ ( ps \/ th \/ et ) ) ) $=
    ( wo w3o or4 orbi1i bitr2i df-3or orbi12i 3bitr4i ) ABGZCDGZGZEFGZGZACGZEGZ
    BDGZFGZGZOPRHACEHZBDFHZGUDTUBGZRGSTEUBFIUGQRACBDIJKOPRLUEUAUFUCACELBDFLMN
    $.

  ${
    mp3an1.1 $e |- ph $.
    mp3an1.2 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
    $( An inference based on modus ponens.  (Contributed by NM,
       21-Nov-1994.) $)
    mp3an1 $p |- ( ( ps /\ ch ) -> th ) $=
      ( wa 3expb mpan ) ABCGDEABCDFHI $.
  $}

  ${
    mp3an2.1 $e |- ps $.
    mp3an2.2 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
    $( An inference based on modus ponens.  (Contributed by NM,
       21-Nov-1994.) $)
    mp3an2 $p |- ( ( ph /\ ch ) -> th ) $=
      ( 3expa mpanl2 ) ABCDEABCDFGH $.
  $}

  ${
    mp3an3.1 $e |- ch $.
    mp3an3.2 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
    $( An inference based on modus ponens.  (Contributed by NM,
       21-Nov-1994.) $)
    mp3an3 $p |- ( ( ph /\ ps ) -> th ) $=
      ( wa 3expia mpi ) ABGCDEABCDFHI $.
  $}

  ${
    mp3an12.1 $e |- ph $.
    mp3an12.2 $e |- ps $.
    mp3an12.3 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
    $( An inference based on modus ponens.  (Contributed by NM,
       13-Jul-2005.) $)
    mp3an12 $p |- ( ch -> th ) $=
      ( mp3an1 mpan ) BCDFABCDEGHI $.
  $}

  ${
    mp3an13.1 $e |- ph $.
    mp3an13.2 $e |- ch $.
    mp3an13.3 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
    $( An inference based on modus ponens.  (Contributed by NM,
       14-Jul-2005.) $)
    mp3an13 $p |- ( ps -> th ) $=
      ( mp3an3 mpan ) ABDEABCDFGHI $.
  $}

  ${
    mp3an23.1 $e |- ps $.
    mp3an23.2 $e |- ch $.
    mp3an23.3 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
    $( An inference based on modus ponens.  (Contributed by NM,
       14-Jul-2005.) $)
    mp3an23 $p |- ( ph -> th ) $=
      ( mp3an3 mpan2 ) ABDEABCDFGHI $.
  $}

  ${
    mp3an1i.1 $e |- ps $.
    mp3an1i.2 $e |- ( ph -> ( ( ps /\ ch /\ th ) -> ta ) ) $.
    $( An inference based on modus ponens.  (Contributed by NM, 5-Jul-2005.) $)
    mp3an1i $p |- ( ph -> ( ( ch /\ th ) -> ta ) ) $=
      ( wa wi w3a com12 mp3an1 ) CDHAEBCDAEIFABCDJEGKLK $.
  $}

  ${
    mp3anl1.1 $e |- ph $.
    mp3anl1.2 $e |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ta ) $.
    $( An inference based on modus ponens.  (Contributed by NM,
       24-Feb-2005.) $)
    mp3anl1 $p |- ( ( ( ps /\ ch ) /\ th ) -> ta ) $=
      ( wa wi w3a ex mp3an1 imp ) BCHDEABCDEIFABCJDEGKLM $.
  $}

  ${
    mp3anl2.1 $e |- ps $.
    mp3anl2.2 $e |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ta ) $.
    $( An inference based on modus ponens.  (Contributed by NM,
       24-Feb-2005.) $)
    mp3anl2 $p |- ( ( ( ph /\ ch ) /\ th ) -> ta ) $=
      ( wa wi w3a ex mp3an2 imp ) ACHDEABCDEIFABCJDEGKLM $.
  $}

  ${
    mp3anl3.1 $e |- ch $.
    mp3anl3.2 $e |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ta ) $.
    $( An inference based on modus ponens.  (Contributed by NM,
       24-Feb-2005.) $)
    mp3anl3 $p |- ( ( ( ph /\ ps ) /\ th ) -> ta ) $=
      ( wa wi w3a ex mp3an3 imp ) ABHDEABCDEIFABCJDEGKLM $.
  $}

  ${
    mp3anr1.1 $e |- ps $.
    mp3anr1.2 $e |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> ta ) $.
    $( An inference based on modus ponens.  (Contributed by NM, 4-Nov-2006.) $)
    mp3anr1 $p |- ( ( ph /\ ( ch /\ th ) ) -> ta ) $=
      ( wa w3a ancoms mp3anl1 ) CDHAEBCDAEFABCDIEGJKJ $.
  $}

  ${
    mp3anr2.1 $e |- ch $.
    mp3anr2.2 $e |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> ta ) $.
    $( An inference based on modus ponens.  (Contributed by NM,
       24-Nov-2006.) $)
    mp3anr2 $p |- ( ( ph /\ ( ps /\ th ) ) -> ta ) $=
      ( wa w3a ancoms mp3anl2 ) BDHAEBCDAEFABCDIEGJKJ $.
  $}

  ${
    mp3anr3.1 $e |- th $.
    mp3anr3.2 $e |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> ta ) $.
    $( An inference based on modus ponens.  (Contributed by NM,
       19-Oct-2007.) $)
    mp3anr3 $p |- ( ( ph /\ ( ps /\ ch ) ) -> ta ) $=
      ( wa w3a ancoms mp3anl3 ) BCHAEBCDAEFABCDIEGJKJ $.
  $}

  ${
    mp3an.1 $e |- ph $.
    mp3an.2 $e |- ps $.
    mp3an.3 $e |- ch $.
    mp3an.4 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
    $( An inference based on modus ponens.  (Contributed by NM,
       14-May-1999.) $)
    mp3an $p |- th $=
      ( mp3an1 mp2an ) BCDFGABCDEHIJ $.
  $}

  ${
    mpd3an3.2 $e |- ( ( ph /\ ps ) -> ch ) $.
    mpd3an3.3 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
    $( An inference based on modus ponens.  (Contributed by NM, 8-Nov-2007.) $)
    mpd3an3 $p |- ( ( ph /\ ps ) -> th ) $=
      ( wa 3expa mpdan ) ABGCDEABCDFHI $.
  $}

  ${
    mpd3an23.1 $e |- ( ph -> ps ) $.
    mpd3an23.2 $e |- ( ph -> ch ) $.
    mpd3an23.3 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
    $( An inference based on modus ponens.  (Contributed by NM, 4-Dec-2006.) $)
    mpd3an23 $p |- ( ph -> th ) $=
      ( id syl3anc ) AABCDAHEFGI $.
  $}

  ${
    mp3and.1 $e |- ( ph -> ps ) $.
    mp3and.2 $e |- ( ph -> ch ) $.
    mp3and.3 $e |- ( ph -> th ) $.
    mp3and.4 $e |- ( ph -> ( ( ps /\ ch /\ th ) -> ta ) ) $.
    $( A deduction based on modus ponens.  (Contributed by Mario Carneiro,
       24-Dec-2016.) $)
    mp3and $p |- ( ph -> ta ) $=
      ( w3a 3jca mpd ) ABCDJEABCDFGHKIL $.
  $}

  ${
    mp3an12i.1 $e |- ph $.
    mp3an12i.2 $e |- ps $.
    mp3an12i.3 $e |- ( ch -> th ) $.
    mp3an12i.4 $e |- ( ( ph /\ ps /\ th ) -> ta ) $.
    $( ~ mp3an with antecedents in standard conjunction form and with one
       hypothesis an implication.  (Contributed by Alan Sare, 28-Aug-2016.) $)
    mp3an12i $p |- ( ch -> ta ) $=
      ( mp3an12 syl ) CDEHABDEFGIJK $.
  $}

  ${
    mp3an2i.1 $e |- ph $.
    mp3an2i.2 $e |- ( ps -> ch ) $.
    mp3an2i.3 $e |- ( ps -> th ) $.
    mp3an2i.4 $e |- ( ( ph /\ ch /\ th ) -> ta ) $.
    $( ~ mp3an with antecedents in standard conjunction form and with two
       hypotheses which are implications.  (Contributed by Alan Sare,
       28-Aug-2016.) $)
    mp3an2i $p |- ( ps -> ta ) $=
      ( mp3an1 syl2anc ) BCDEGHACDEFIJK $.
  $}

  ${
    mp3an3an.1 $e |- ph $.
    mp3an3an.2 $e |- ( ps -> ch ) $.
    mp3an3an.3 $e |- ( th -> ta ) $.
    mp3an3an.4 $e |- ( ( ph /\ ch /\ ta ) -> et ) $.
    $( ~ mp3an with antecedents in standard conjunction form and with two
       hypotheses which are implications.  (Contributed by Alan Sare,
       28-Aug-2016.) $)
    mp3an3an $p |- ( ( ps /\ th ) -> et ) $=
      ( mp3an1 syl2an ) BCEFDHIACEFGJKL $.
  $}

  ${
    mp3an2ani.1 $e |- ph $.
    mp3an2ani.2 $e |- ( ps -> ch ) $.
    mp3an2ani.3 $e |- ( ( ps /\ th ) -> ta ) $.
    mp3an2ani.4 $e |- ( ( ph /\ ch /\ ta ) -> et ) $.
    $( An elimination deduction.  (Contributed by Alan Sare, 17-Oct-2017.) $)
    mp3an2ani $p |- ( ( ps /\ th ) -> et ) $=
      ( wa mp3an3an anabss5 ) BDFABCBDKEFGHIJLM $.
  $}

  ${
    biimp3a.1 $e |- ( ( ph /\ ps ) -> ( ch <-> th ) ) $.
    $( Infer implication from a logical equivalence.  Similar to ~ biimpa .
       (Contributed by NM, 4-Sep-2005.) $)
    biimp3a $p |- ( ( ph /\ ps /\ ch ) -> th ) $=
      ( wa biimpa 3impa ) ABCDABFCDEGH $.

    $( Infer implication from a logical equivalence.  Similar to ~ biimpar .
       (Contributed by NM, 2-Jan-2009.) $)
    biimp3ar $p |- ( ( ph /\ ps /\ th ) -> ch ) $=
      ( exbiri 3imp ) ABDCABCDEFG $.
  $}

  ${
    3anandis.1 $e |- ( ( ( ph /\ ps ) /\ ( ph /\ ch ) /\ ( ph /\ th ) )
                      -> ta ) $.
    $( Inference that undistributes a triple conjunction in the antecedent.
       (Contributed by NM, 18-Apr-2007.) $)
    3anandis $p |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> ta ) $=
      ( w3a wa simpl simpr1 simpr2 simpr3 syl222anc ) ABCDGZHABACADEANIZABCDJOA
      BCDKOABCDLFM $.
  $}

  ${
    3anandirs.1 $e |- ( ( ( ph /\ th ) /\ ( ps /\ th ) /\ ( ch /\ th ) )
                      -> ta ) $.
    $( Inference that undistributes a triple conjunction in the antecedent.
       (Contributed by NM, 25-Jul-2006.)  (Revised by NM, 18-Apr-2007.) $)
    3anandirs $p |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ta ) $=
      ( w3a wa simpl1 simpr simpl2 simpl3 syl222anc ) ABCGZDHADBDCDEABCDINDJZAB
      CDKOABCDLOFM $.
  $}

  ${
    ecased.1 $e |- ( ph -> -. ch ) $.
    ecased.2 $e |- ( ph -> ( ps \/ ch ) ) $.
    $( Deduction form of disjunctive syllogism.  (Contributed by Jim Kingdon,
       9-Dec-2017.) $)
    ecased $p |- ( ph -> ps ) $=
      ( wn wo wa jca orel2 imp syl ) ACFZBCGZHBAMNDEIMNBCBJKL $.
  $}

  ${
    ecase23d.1 $e |- ( ph -> -. ch ) $.
    ecase23d.2 $e |- ( ph -> -. th ) $.
    ecase23d.3 $e |- ( ph -> ( ps \/ ch \/ th ) ) $.
    $( Variation of ~ ecased with three disjuncts instead of two.  (Contributed
       by NM, 22-Apr-1994.)  (Revised by Jim Kingdon, 9-Dec-2017.) $)
    ecase23d $p |- ( ph -> ps ) $=
      ( wo w3o df-3or sylib ecased ) ABCEABCHZDFABCDIMDHGBCDJKLL $.
  $}

  ${
    ecase2d.1 $e |- ( ph -> ps ) $.
    ecase2d.2 $e |- ( ph -> -. ( ps /\ ch ) ) $.
    ecase2d.3 $e |- ( ph -> -. ( ps /\ th ) ) $.
    ecase2d.4 $e |- ( ph -> ( ta \/ ( ch \/ th ) ) ) $.
    $( Deduction for elimination by cases.  (Contributed by NM, 21-Apr-1994.)
       (Proof shortened by Wolf Lammen, 19-Sep-2024.) $)
    ecase2d $p |- ( ph -> ta ) $=
      ( wo wn mpnanrd ioran sylanbrc ecased ) AECDJZACKDKPKABCFGLABDFHLCDMNIO
      $.
  $}

  ${
    3biorfd.1 $e |- ( ph -> -. th ) $.
    $( A disjunction is equivalent to a threefold disjunction with single
       falsehood, analogous to ~ biorf .  (Contributed by Alexander van der
       Vekens, 8-Sep-2017.) $)
    3bior1fd $p |- ( ph -> ( ( ch \/ ps ) <-> ( th \/ ch \/ ps ) ) ) $=
      ( wo w3o wn wb biorf syl 3orass bitr4di ) ACBFZDNFZDCBGADHNOIEDNJKDCBLM
      $.

    $( A disjunction is equivalent to a threefold disjunction with single
       falsehood of a conjunction.  (Contributed by Alexander van der Vekens,
       8-Sep-2017.) $)
    3bior1fand $p |- ( ph -> ( ( ch \/ ps )
                       <-> ( ( th /\ ta ) \/ ch \/ ps ) ) ) $=
      ( wa intnanrd 3bior1fd ) ABCDEGADEFHI $.

    3biorfd.2 $e |- ( ph -> -. ch ) $.
    $( A wff is equivalent to its threefold disjunction with double falsehood,
       analogous to ~ biorf .  (Contributed by Alexander van der Vekens,
       8-Sep-2017.) $)
    3bior2fd $p |- ( ph -> ( ps <-> ( th \/ ch \/ ps ) ) ) $=
      ( wo w3o wn wb biorf syl 3bior1fd bitrd ) ABCBGZDCBHACIBOJFCBKLABCDEMN $.
  $}

  ${
    3biantd.1 $e |- ( ph -> th ) $.
    $( A conjunction is equivalent to a threefold conjunction with single
       truth, analogous to ~ biantrud .  (Contributed by Alexander van der
       Vekens, 26-Sep-2017.) $)
    3biant1d $p |- ( ph -> ( ( ch /\ ps ) <-> ( th /\ ch /\ ps ) ) ) $=
      ( wa w3a biantrurd 3anass bitr4di ) ACBFZDKFDCBGADKEHDCBIJ $.
  $}

  ${
    intn3and.1 $e |- ( ph -> -. ps ) $.
    $( Introduction of a triple conjunct inside a contradiction.  (Contributed
       by FL, 27-Dec-2007.)  (Proof shortened by Andrew Salmon,
       26-Jun-2011.) $)
    intn3an1d $p |- ( ph -> -. ( ps /\ ch /\ th ) ) $=
      ( w3a simp1 nsyl ) ABBCDFEBCDGH $.

    $( Introduction of a triple conjunct inside a contradiction.  (Contributed
       by FL, 27-Dec-2007.)  (Proof shortened by Andrew Salmon,
       26-Jun-2011.) $)
    intn3an2d $p |- ( ph -> -. ( ch /\ ps /\ th ) ) $=
      ( w3a simp2 nsyl ) ABCBDFECBDGH $.

    $( Introduction of a triple conjunct inside a contradiction.  (Contributed
       by FL, 27-Dec-2007.)  (Proof shortened by Andrew Salmon,
       26-Jun-2011.) $)
    intn3an3d $p |- ( ph -> -. ( ch /\ th /\ ps ) ) $=
      ( w3a simp3 nsyl ) ABCDBFECDBGH $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  True and false constants
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Universal quantifier for use by df-tru
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  Even though it is not ordinarily part of propositional calculus, the
  universal quantifier ` A. ` is introduced here so that the soundness of
  Definition ~ df-tru can be checked by the same algorithm that is used for
  predicate calculus.  Its first real use is in Axiom ~ ax-5 in the
  predicate calculus section below.  For those who want propositional calculus
  to be self-contained, i.e., to use wff variables only, the alternate
  Definition ~ dftru2 may be adopted and this subsection moved down to the
  start of the subsection with ~ wex below.  However, the use of ~ dftru2 as a
  definition requires a more elaborate definition checking algorithm that we
  prefer to avoid.

$)

  $( Declare new symbols needed for predicate calculus. $)
  $c A. $.  $( "inverted A" universal quantifier (read:  "for all") $)
  $c setvar $.  $( Individual variable type (read:  "the following is an
                   individual (set) variable") $)

  $( Add 'setvar' as a typecode for bound variables. $)
  $( $j syntax 'setvar'; bound 'setvar'; $)

  ${
    $v x $.
    $( Let ` x ` be an individual variable (temporary declaration). $)
    vx.wal $f setvar x $.
    $( Extend wff definition to include the universal quantifier ("for all").
       ` A. x ph ` is read " ` ph ` (phi) is true for all ` x ` ".  Typically,
       in its final application ` ph ` would be replaced with a wff containing
       a (free) occurrence of the variable ` x ` , for example ` x = y ` .  In
       a universe with a finite number of objects, "for all" is equivalent to a
       big conjunction (AND) with one wff for each possible case of ` x ` .
       When the universe is infinite (as with set theory), such a
       propositional-calculus equivalent is not possible because an infinitely
       long formula has no meaning, but conceptually the idea is the same. $)
    wal $a wff A. x ph $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Equality predicate for use by df-tru
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  Even though it is not ordinarily part of propositional calculus, the equality
  predicate ` = ` is introduced here so that the soundness of definition
  ~ df-tru can be checked by the same algorithm as is used for predicate
  calculus.  Its first real use is in Axiom ~ ax-8 in the predicate calculus
  section below.  For those who want propositional calculus to be
  self-contained, i.e., to use wff variables only, the alternate definition
  ~ dftru2 may be adopted and this subsection moved down to just above ~ weq
  below.  However, the use of ~ dftru2 as a definition requires a more
  elaborate definition checking algorithm that we prefer to avoid.

$)

  $c class $.

  $( Add 'class' as a typecode. $)
  $( $j syntax 'class'; $)

  ${
    $v x $.
    $( Let ` x ` be an individual variable (temporary declaration). $)
    vx.cv $f setvar x $.
    $( This syntax construction states that a variable ` x ` , which has been
       declared to be a setvar variable by $f statement vx, is also a class
       expression.  This can be justified informally as follows.  We know that
       the class builder ` { y | y e. x } ` is a class by ~ cab .  Since (when
       ` y ` is distinct from ` x ` ) we have ` x = { y | y e. x } ` by
       ~ cvjust , we can argue that the syntax " ` class x ` " can be viewed as
       an abbreviation for " ` class { y | y e. x } ` ".  See the discussion
       under the definition of class in [Jech] p. 4 showing that "Every set can
       be considered to be a class."

       While it is tempting and perhaps occasionally useful to view ~ cv as a
       "type conversion" from a setvar variable to a class variable, keep in
       mind that ~ cv is intrinsically no different from any other
       class-building syntax such as ~ cab , ~ cun , or ~ c0 .

       For a general discussion of the theory of classes and the role of ~ cv ,
       see ~ https://us.metamath.org/mpeuni/mmset.html#class .

       (The description above applies to set theory, not predicate calculus.
       The purpose of introducing ` class x ` here, and not in set theory where
       it belongs, is to allow us to express i.e.  "prove" the ~ weq of
       predicate calculus from the ~ wceq of set theory, so that we don't
       overload the ` = ` connective with two syntax definitions.  This is done
       to prevent ambiguity that would complicate some Metamath parsers.) $)
    cv $a class x $.
  $}

  $( Declare the equality predicate symbol. $)
  $c = $.  $( Equal sign (read:  'is equal to') $)

  ${
    $v A $.
    $v B $.
    $( Temporary declarations of ` A ` and ` B ` . $)
    cA.wceq $f class A $.
    cB.wceq $f class B $.
    $( Extend wff definition to include class equality.

       For a general discussion of the theory of classes, see
       ~ https://us.metamath.org/mpeuni/mmset.html#class .

       (The purpose of introducing ` wff A = B ` here, and not in set theory
       where it belongs, is to allow us to express i.e.  "prove" the ~ weq of
       predicate calculus in terms of the ~ wceq of set theory, so that we
       don't "overload" the ` = ` connective with two syntax definitions.  This
       is done to prevent ambiguity that would complicate some Metamath
       parsers.  For example, some parsers - although not the Metamath program
       - stumble on the fact that the ` = ` in ` x = y ` could be the ` = ` of
       either ~ weq or ~ wceq , although mathematically it makes no difference.
       The class variables ` A ` and ` B ` are introduced temporarily for the
       purpose of this definition but otherwise not used in predicate calculus.
       See ~ df-cleq for more information on the set theory usage of
       ~ wceq .) $)
    wceq $a wff A = B $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Define the true and false constants
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $c T. $.

  $( ` T. ` is a wff. $)
  wtru $a wff T. $.

  ${
    $v x $.
    $v y $.
    $( Temporary declarations of ` x ` and ` y ` for local use by ~ df-tru .
       These will be redeclared globally in the predicate calculus section. $)
    vx.tru $f setvar x $.
    vy.tru $f setvar y $.
    $( Soundness justification theorem for ~ df-tru .  (Contributed by Mario
       Carneiro, 17-Nov-2013.)  (Revised by NM, 11-Jul-2019.) $)
    trujust $p |- ( ( A. x x = x -> A. x x = x )
              <-> ( A. y y = y -> A. y y = y ) ) $=
      ( cv wceq wal wi id 2th ) ACZIDAEZJFBCZKDBEZLFJGLGH $.

    $( Definition of the truth value "true", or "verum", denoted by ` T. ` .
       This is a tautology, as proved by ~ tru .  In this definition, an
       instance of ~ id is used as the definiens, although any tautology, such
       as an axiom, can be used in its place.  This particular ~ id instance
       was chosen so this definition can be checked by the same algorithm that
       is used for predicate calculus.  This definition should be referenced
       directly only by ~ tru , and other proofs should depend on ~ tru
       (directly or indirectly) instead of this definition, since there are
       many alternate ways to define ` T. ` .  (Contributed by Anthony Hart,
       13-Oct-2010.)  (Revised by NM, 11-Jul-2019.)
       (New usage is discouraged.) $)
    df-tru $a |- ( T. <-> ( A. x x = x -> A. x x = x ) ) $.

    $( The truth value ` T. ` is provable.  (Contributed by Anthony Hart,
       13-Oct-2010.) $)
    tru $p |- T. $=
      ( vx.tru wtru cv wceq wal wi id df-tru mpbir ) BACZJDAEZKFKGAHI $.
  $}

  $c F. $.

  $( ` F. ` is a wff. $)
  wfal $a wff F. $.

  $( Definition of the truth value "false", or "falsum", denoted by ` F. ` .
     See also ~ df-tru .  (Contributed by Anthony Hart, 22-Oct-2010.) $)
  df-fal $a |- ( F. <-> -. T. ) $.

  $( The truth value ` F. ` is refutable.  (Contributed by Anthony Hart,
     22-Oct-2010.)  (Proof shortened by Mel L. O'Cat, 11-Mar-2012.) $)
  fal $p |- -. F. $=
    ( wfal wtru wn tru notnoti df-fal mtbir ) ABCBDEFG $.

  $( An alternate definition of "true".  (Contributed by Anthony Hart,
     13-Oct-2010.)  (Revised by BJ, 12-Jul-2019.)
     (New usage is discouraged.) $)
  dftru2 $p |- ( T. <-> ( ph -> ph ) ) $=
    ( wtru wi tru id 2th ) BAACDAEF $.

  ${
    mptru.1 $e |- ( T. -> ph ) $.
    $( Eliminate ` T. ` as an antecedent.  A proposition implied by ` T. ` is
       true.  (Contributed by Mario Carneiro, 13-Mar-2014.) $)
    mptru $p |- ph $=
      ( wtru tru ax-mp ) CADBE $.
  $}

  $( A proposition is equivalent to itself being equivalent to ` T. ` .
     (Contributed by Anthony Hart, 14-Aug-2011.) $)
  tbtru $p |- ( ph <-> ( ph <-> T. ) ) $=
    ( wtru tru tbt ) BACD $.

  $( The negation of a proposition is equivalent to itself being equivalent to
     ` F. ` .  (Contributed by Anthony Hart, 14-Aug-2011.) $)
  nbfal $p |- ( -. ph <-> ( ph <-> F. ) ) $=
    ( wfal fal nbn ) BACD $.

  ${
    bitru.1 $e |- ph $.
    $( A theorem is equivalent to truth.  (Contributed by Mario Carneiro,
       9-May-2015.) $)
    bitru $p |- ( ph <-> T. ) $=
      ( wtru tru 2th ) ACBDE $.
  $}

  ${
    bifal.1 $e |- -. ph $.
    $( A contradiction is equivalent to falsehood.  (Contributed by Mario
       Carneiro, 9-May-2015.) $)
    bifal $p |- ( ph <-> F. ) $=
      ( wfal fal 2false ) ACBDE $.
  $}

  $( The truth value ` F. ` implies anything.  Also called the principle of
     explosion, or "ex falso quodlibet".  (Contributed by FL, 20-Mar-2011.)
     (Proof shortened by Anthony Hart, 1-Aug-2011.) $)
  falim $p |- ( F. -> ph ) $=
    ( wfal fal pm2.21i ) BACD $.

  $( The truth value ` F. ` implies anything.  (Contributed by Mario Carneiro,
     9-Feb-2017.) $)
  falimd $p |- ( ( ph /\ F. ) -> ps ) $=
    ( wfal falim adantl ) CBABDE $.

  $( Anything implies ` T. ` .  (Contributed by FL, 20-Mar-2011.)  (Proof
     shortened by Anthony Hart, 1-Aug-2011.) $)
  trud $p |- ( ph -> T. ) $=
    ( wtru tru a1i ) BACD $.

  $( True can be removed from a conjunction.  (Contributed by FL, 20-Mar-2011.)
     (Proof shortened by Wolf Lammen, 21-Jul-2019.) $)
  truan $p |- ( ( T. /\ ph ) <-> ph ) $=
    ( wtru wa tru biantrur bicomi ) ABACBADEF $.

  $( Given falsum, we can define the negation of a wff ` ph ` as the statement
     that a contradiction follows from assuming ` ph ` .  (Contributed by Mario
     Carneiro, 9-Feb-2017.)  (Proof shortened by Wolf Lammen, 21-Jul-2019.) $)
  dfnot $p |- ( -. ph <-> ( ph -> F. ) ) $=
    ( wfal wn wi wb fal mtt ax-mp ) BCACABDEFBAGH $.

  ${
    inegd.1 $e |- ( ( ph /\ ps ) -> F. ) $.
    $( Negation introduction rule from natural deduction.  (Contributed by
       Mario Carneiro, 9-Feb-2017.) $)
    inegd $p |- ( ph -> -. ps ) $=
      ( wfal wi wn ex dfnot sylibr ) ABDEBFABDCGBHI $.
  $}

  ${
    pm2.21fal.1 $e |- ( ph -> ps ) $.
    pm2.21fal.2 $e |- ( ph -> -. ps ) $.
    $( If a wff and its negation are provable, then falsum is provable.
       (Contributed by Mario Carneiro, 9-Feb-2017.) $)
    pm2.21fal $p |- ( ph -> F. ) $=
      ( wfal pm2.21dd ) ABECDF $.
  $}

  $( Negation inferred from embedded conjunct.  (Contributed by NM,
     20-Aug-1993.)  (Proof rewritten by Jim Kingdon, 4-May-2018.) $)
  pclem6 $p |- ( ( ph <-> ( ps /\ -. ph ) ) -> -. ps ) $=
    ( wn wa wb wfal biimp pm3.4 com12 ax-ia3 biimpr syl9 impbidd pm5.19 pm2.21i
    wi syl9r syl6com dfnot sylibr ) ABACZDZEZBFPBCBUCAUAEZFBUCAUAUCAUBBUAAUBGUB
    BUABUAHIQBUAUBUCABUAJAUBKLMUDFANORBST $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Logical 'xor'
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Declare connective for exclusive disjunction ('xor'). $)
  $c \/_ $. $( Underlined 'vee' (read:  'xor') $)

  $( Extend wff definition to include exclusive disjunction ('xor'). $)
  wxo $a wff ( ph \/_ ps ) $.

  $( Define exclusive disjunction (logical 'xor').  Return true if either the
     left or right, but not both, are true.  Contrast with ` /\ ` ( ~ wa ),
     ` \/ ` ( ~ wo ), and ` -> ` ( ~ wi ) .  (Contributed by FL, 22-Nov-2010.)
     (Modified by Jim Kingdon, 1-Mar-2018.) $)
  df-xor $a |- ( ( ph \/_ ps ) <-> ( ( ph \/ ps ) /\ -. ( ph /\ ps ) ) ) $.

  $( One way of defining exclusive or.  Equivalent to ~ df-xor .  (Contributed
     by Jim Kingdon and Mario Carneiro, 1-Mar-2018.) $)
  xoranor $p |- ( ( ph \/_ ps ) <-> ( ( ph \/ ps ) /\ ( -. ph \/ -. ps ) ) ) $=
    ( wxo wo wn wa df-xor ax-ia3 con3d olc syl6 pm3.21 orc jaoi imdistani sylbi
    wi pm3.14 anim2i sylibr impbii ) ABCZABDZAEZBEZDZFZUBUCABFZEZFZUGABGZUCUIUF
    AUIUFQBAUIUEUFABUHABHIUEUDJKBUIUDUFBAUHBALIUDUEMKNOPUGUJUBUFUIUCABRSUKTUA
    $.

  $( This tautology shows that xor is really exclusive.  (Contributed by FL,
     22-Nov-2010.)  (Proof rewritten by Jim Kingdon, 5-May-2018.) $)
  excxor $p |- ( ( ph \/_ ps ) <->
       ( ( ph /\ -. ps ) \/ ( -. ph /\ ps ) ) ) $=
    ( wxo wn wa wo xoranor andi orcom pm3.24 biorfi andir pm5.61 orbi12i 3bitri
    3bitr4ri ancom orbi2i ) ABCZBADZEZABDZEZFZUCUAFUCTBEZFSABFZTUBFEUFTEZUFUBEZ
    FUDABGUFTUBHUGUAUHUCUAATEZFUIUAFUAUGUAUIIUIUAAJKABTLPABMNOUAUCIUAUEUCBTQRO
    $.

  $( XOR implies OR. (Contributed by BJ, 19-Apr-2019.) $)
  xoror $p |- ( ( ph \/_ ps ) -> ( ph \/ ps ) ) $=
    ( wxo wo wn xoranor simplbi ) ABCABDAEBEDABFG $.

  ${
    xorbid.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Deduction joining an equivalence and a left operand to form equivalence
       of exclusive-or.  (Contributed by Jim Kingdon, 7-Oct-2018.) $)
    xorbi2d $p |- ( ph -> ( ( th \/_ ps ) <-> ( th \/_ ch ) ) ) $=
      ( wo wa wn wxo orbi2d anbi2d notbid anbi12d df-xor 3bitr4g ) ADBFZDBGZHZG
      DCFZDCGZHZGDBIDCIAPSRUAABCDEJAQTABCDEKLMDBNDCNO $.

    $( Deduction joining an equivalence and a right operand to form equivalence
       of exclusive-or.  (Contributed by Jim Kingdon, 7-Oct-2018.) $)
    xorbi1d $p |- ( ph -> ( ( ps \/_ th ) <-> ( ch \/_ th ) ) ) $=
      ( wo wa wn wxo orbi1d anbi1d notbid anbi12d df-xor 3bitr4g ) ABDFZBDGZHZG
      CDFZCDGZHZGBDICDIAPSRUAABCDEJAQTABCDEKLMBDNCDNO $.
  $}

  ${
    xorbi12d.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    xorbi12d.2 $e |- ( ph -> ( th <-> ta ) ) $.
    $( Deduction joining two equivalences to form equivalence of exclusive-or.
       (Contributed by Jim Kingdon, 7-Oct-2018.) $)
    xorbi12d $p |- ( ph -> ( ( ps \/_ th ) <-> ( ch \/_ ta ) ) ) $=
      ( wxo xorbi1d xorbi2d bitrd ) ABDHCDHCEHABCDFIADECGJK $.
  $}

  ${
    xorbi12.1 $e |- ( ph <-> ps ) $.
    xorbi12.2 $e |- ( ch <-> th ) $.
    $( Equality property for XOR. (Contributed by Mario Carneiro,
       4-Sep-2016.) $)
    xorbi12i $p |- ( ( ph \/_ ch ) <-> ( ps \/_ th ) ) $=
      ( wxo wb wtru a1i xorbi12d mptru ) ACGBDGHIABCDABHIEJCDHIFJKL $.
  $}

  $( A consequence of exclusive or.  In classical logic the converse also
     holds.  (Contributed by Jim Kingdon, 8-Mar-2018.) $)
  xorbin $p  |- ( ( ph \/_ ps ) -> ( ph <-> -. ps ) ) $=
    ( wn wo wa wi df-xor imnan biimpri adantl sylbi pm2.53 orcoms adantr impbid
    wxo ) ABPZABCZQABDZABECZEZARFZABGZTUBSUBTABHIJKQUARAFZUCSUDTBAUDBALMNKO $.

  $( One direction of ~ pm5.18dc , which holds for all propositions, not just
     decidable propositions.  (Contributed by Jim Kingdon, 10-Mar-2018.) $)
  pm5.18im $p |- ( ( ph <-> ps ) -> -. ( ph <-> -. ps ) ) $=
    ( wb wn pm5.19 bibi1 notbid mpbiri ) ABCZABDZCZDBJCZDBEIKLABJFGH $.

  $( A consequence of exclusive or.  For decidable propositions this is an
     equivalence, as seen at ~ xornbidc .  (Contributed by Jim Kingdon,
     10-Mar-2018.) $)
  xornbi $p  |- ( ( ph \/_ ps ) -> -. ( ph <-> ps ) ) $=
    ( wxo wn wb xorbin pm5.18im con2i syl ) ABCABDEZABEZDABFKJABGHI $.

  $( Two ways to express "exclusive or" between decidable propositions.
     (Contributed by Jim Kingdon, 12-Apr-2018.) $)
  xor3dc $p |- ( DECID ph -> ( DECID ps ->
      ( -. ( ph <-> ps ) <-> ( ph <-> -. ps ) ) ) ) $=
    ( wdc wb wn wa dcn dcbi syl5 imp pm5.18dc a1d con2biddc mpd bicomd ex ) ACZ
    BCZABDZEZABEZDZDQRFZUBTUCUBCZUBTDQRUDRUACQUDBGAUAHIJUCSUBUCSUBEDZUDQRUEABKJ
    LMNOP $.

  $( ` \/_ ` is commutative.  (Contributed by David A. Wheeler, 6-Oct-2018.) $)
  xorcom $p |- ( ( ph \/_ ps ) <-> ( ps \/_ ph ) ) $=
    ( wo wa wn wxo orcom ancom notbii anbi12i df-xor 3bitr4i ) ABCZABDZEZDBACZB
    ADZEZDABFBAFMPORABGNQABHIJABKBAKL $.

  $( A decidable proposition is equivalent to a decidable proposition or its
     negation.  Based on theorem *5.15 of [WhiteheadRussell] p. 124.
     (Contributed by Jim Kingdon, 18-Apr-2018.) $)
  pm5.15dc $p |- ( DECID ph -> ( DECID ps ->
      ( ( ph <-> ps ) \/ ( ph <-> -. ps ) ) ) ) $=
    ( wdc wb wn wo wa wi xor3dc imp biimpd dcbi dfordc syl mpbird ex ) ACZBCZAB
    DZABEDZFZQRGZUASEZTHZUBUCTQRUCTDABIJKUBSCZUAUDDQRUEABLJSTMNOP $.

  $( Two ways to express "exclusive or" between decidable propositions.
     (Contributed by Jim Kingdon, 17-Apr-2018.) $)
  xor2dc $p |- ( DECID ph -> ( DECID ps ->
      ( -. ( ph <-> ps ) <-> ( ( ph \/ ps ) /\ -. ( ph /\ ps ) ) ) ) ) $=
    ( wdc wb wn wo wa xor3dc imp pm5.17dc adantl bitr4d ex ) ACZBCZABDEZABFABGE
    GZDNOGPABEDZQNOPRDABHIOQRDNABJKLM $.

  $( Exclusive or is equivalent to negated biconditional for decidable
     propositions.  (Contributed by Jim Kingdon, 27-Apr-2018.) $)
  xornbidc $p  |- ( DECID ph -> ( DECID ps ->
      ( ( ph \/_ ps ) <-> -. ( ph <-> ps ) ) ) ) $=
    ( wdc wxo wb wn wa wo df-xor xor2dc imp bitr4id ex ) ACZBCZABDZABEFZENOGPAB
    HABGFGZQABINOQREABJKLM $.

  $( Two ways to express "exclusive or" between decidable propositions.
     Theorem *5.22 of [WhiteheadRussell] p. 124, but for decidable
     propositions.  (Contributed by Jim Kingdon, 5-May-2018.) $)
  xordc $p |- ( DECID ph -> ( DECID ps ->
      ( -. ( ph <-> ps ) <-> ( ( ph /\ -. ps ) \/ ( ps /\ -. ph ) ) ) ) ) $=
    ( wdc wb wn wa wo wxo xornbidc imp excxor ancom orbi2i bitri bitr3di ex ) A
    CZBCZABDEZABEFZBAEZFZGZDQRFABHZSUCQRUDSDABIJUDTUABFZGUCABKUEUBTUABLMNOP $.

  $( Exclusive or implies the left proposition is decidable.  (Contributed by
     Jim Kingdon, 12-Mar-2018.) $)
  xordc1 $p |- ( ( ph \/_ ps ) -> DECID ph ) $=
    ( wo wa wn wxo wdc andir simpl imnan ancom xchbinxr pm3.35 sylan2br orim12i
    wi sylbi df-xor df-dc 3imtr4i ) ABCABDZEZDZAAEZCZABFAGUCAUBDZBUBDZCUEABUBHU
    FAUGUDAUBIUBBBUDPZUDUHBADUABAJABKLBUDMNOQABRAST $.

  $( Move negation outside of biconditional, for decidable propositions.
     Compare Theorem *5.18 of [WhiteheadRussell] p. 124.  (Contributed by Jim
     Kingdon, 18-Apr-2018.) $)
  nbbndc $p |- ( DECID ph -> ( DECID ps ->
      ( ( -. ph <-> ps ) <-> -. ( ph <-> ps ) ) ) ) $=
    ( wdc wn wb wa xor3dc imp con2bidc bitrd bicom bitr2di ex ) ACZBCZADZBEZABE
    DZENOFZRBPEZQSRABDEZTNORUAEABGHNOUATEABIHJBPKLM $.

  $( Associative law for the biconditional, for decidable propositions.

     The classical version (without the decidability conditions) is an axiom of
     system DS in Vladimir Lifschitz, "On calculational proofs", Annals of Pure
     and Applied Logic, 113:207-224, 2002,
     ~ http://www.cs.utexas.edu/users/ai-lab/pub-view.php?PubID=26805 , and,
     interestingly, was not included in _Principia Mathematica_ but was
     apparently first noted by Jan Lukasiewicz circa 1923.  (Contributed by Jim
     Kingdon, 4-May-2018.) $)
  biassdc $p |- ( DECID ph -> ( DECID ps -> ( DECID ch ->
      ( ( ( ph <-> ps ) <-> ch ) <-> ( ph <-> ( ps <-> ch ) ) ) ) ) ) $=
    ( wdc wb wn wo wa wi df-dc pm5.501 bibi1d bitr3d a1d nbbndc imp adantl nbn2
    adantr ex jaoi sylbi expd ) ADZBDZCDZABEZCEZABCEZEZEZUDAAFZGUEUFHZUKIZAJAUN
    ULAUKUMAUIUHUJABUGCABKLAUIKMNULUMUKULUMHZUIFZUHUJUOBFZCEZUPUHUMURUPEZULUEUF
    USBCOPQULURUHEUMULUQUGCABRLSMULUPUJEUMAUIRSMTUAUBUC $.

  $( Lukasiewicz's shortest axiom for equivalential calculus (but modified to
     require decidable propositions).  Storrs McCall, ed., _Polish Logic
     1920-1939_ (Oxford, 1967), p. 96.  (Contributed by Jim Kingdon,
     5-May-2018.) $)
  bilukdc $p |- ( ( ( DECID ph /\ DECID ps ) /\ DECID ch ) ->
      ( ( ph <-> ps ) <-> ( ( ch <-> ps ) <-> ( ph <-> ch ) ) ) ) $=
    ( wdc wa wb bicom bibi1i biassdc imp31 bitrid ancom1s dcbi imp adantr simpr
    syl9 syl3c mpbid simplr adantlr bitr4d ) ADZBDZEZCDZEZABFZCBACFZFZFZCBFUIFZ
    UGUHCFZUJFZUHUKFZUDUCUFUNUMBAFZCFZUDUCEUFEUJUHUPCABGHUDUCUFUQUJFBACIJKLUGUH
    DZUFUJDZUNUOFUEURUFUCUDURABMNOUEUFPZUCUDUFUSUCUFUIDZUDUSACMZBUIMQJUHCUJIRSU
    GUFUDVAULUKFUTUCUDUFTUCUFVAUDUCUFVAVBNUACBUIIRUB $.

  $( An alternate definition of the biconditional for decidable propositions.
     Theorem *5.23 of [WhiteheadRussell] p. 124, but with decidability
     conditions.  (Contributed by Jim Kingdon, 5-May-2018.) $)
  dfbi3dc $p |- ( DECID ph -> ( DECID ps ->
      ( ( ph <-> ps ) <-> ( ( ph /\ ps ) \/ ( -. ph /\ -. ps ) ) ) ) ) $=
    ( wdc wb wa wn dcn xordc imp sylan2 pm5.18dc notnotbdc anbi2d ancom orbi12d
    wo a1i adantl 3bitr4d ex ) ACZBCZABDZABEZAFZBFZEZPZDUAUBEAUFDFZAUFFZEZUFUEE
    ZPZUCUHUBUAUFCZUIUMDZBGUAUNUOAUFHIJUAUBUCUIDABKIUBUHUMDUAUBUDUKUGULUBBUJABL
    MUGULDUBUEUFNQORST $.

  $( Theorem *5.24 of [WhiteheadRussell] p. 124, but for decidable
     propositions.  (Contributed by Jim Kingdon, 5-May-2018.) $)
  pm5.24dc $p |- ( DECID ph -> ( DECID ps ->
      ( -. ( ( ph /\ ps ) \/ ( -. ph /\ -. ps ) ) <->
                ( ( ph /\ -. ps ) \/ ( ps /\ -. ph ) ) ) ) ) $=
    ( wdc wa wn wo wb dfbi3dc imp notbid xordc bitr3d ex ) ACZBCZABDAEZBEZDFZEZ
    AQDBPDFZGNODZABGZEZSTUAUBRNOUBRGABHIJNOUCTGABKILM $.

  $( Conjunction distributes over exclusive-or, for decidable propositions.
     This is one way to interpret the distributive law of multiplication over
     addition in modulo 2 arithmetic.  (Contributed by Jim Kingdon,
     14-Jul-2018.) $)
  xordidc $p |- ( DECID ph -> ( DECID ps -> ( DECID ch ->
    ( ( ph /\ ( ps \/_ ch ) ) <->
      ( ( ph /\ ps ) \/_ ( ph /\ ch ) ) ) ) ) ) $=
    ( wdc wxo wa wb wn dcbi imp wi annimdc pm5.32 notbii bitrdi sylan2 xornbidc
    adantl anbi2d dcan adantrr adantrl sylc 3bitr4d exp32 ) ADZBDZCDZABCEZFZABF
    ZACFZEZGUFUGUHFZFZABCGZHZFZUKULGZHZUJUMUNUFUPDZURUTGUGUHVABCIJUFVAFURAUPKZH
    ZUTUFVAURVCGAUPLJVBUSABCMNOPUOUIUQAUNUIUQGZUFUGUHVDBCQJRSUOUKDZULDZUMUTGUFU
    GVEUHABTUAUFUHVFUGACTUBUKULQUCUDUE $.

  $( Conjunction distributes over exclusive-or.  (Contributed by Mario Carneiro
     and Jim Kingdon, 7-Oct-2018.) $)
  anxordi $p |- ( ( ph /\ ( ps \/_ ch ) ) <->
      ( ( ph /\ ps ) \/_ ( ph /\ ch ) ) ) $=
    ( wxo wa simpl wo wn df-xor simplbi jaoi syl ibar xorbi12d bitr3d pm5.21nii
    ) ABCDZEZAABEZACEZDZAQFUASTGZAUAUBSTEHSTIJSATABFACFKLAQRUAAQMABSCTABMACMNOP
    $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Truth tables: Operations on true and false constants
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  For classical logic, truth tables can be used to define propositional
  logic operations, by showing the results of those operations for all
  possible combinations of true ( ` T. ` ) and false ( ` F. ` ).

  Although the intuitionistic logic connectives are not as simply defined,
  ` T. ` and ` F. ` do play similar roles as in classical logic and most
  theorems from classical logic continue to hold.

  Here we show that our definitions and axioms produce equivalent results for
  ` T. ` and ` F. ` as we would get from truth tables for
  ` /\ ` (conjunction aka logical 'and') ~ wa ,
  ` \/ ` (disjunction aka logical inclusive 'or') ~ wo ,
  ` -> ` (implies) ~ wi ,
  ` -. ` (not) ~ wn ,
  ` <-> ` (logical equivalence) ~ df-bi , and
  ` \/_ ` (exclusive or) ~ df-xor .
$)

  $( A ` /\ ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.) $)
  truantru $p |- ( ( T. /\ T. ) <-> T. ) $=
    ( wtru anidm ) AB $.

  $( A ` /\ ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.) $)
  truanfal $p |- ( ( T. /\ F. ) <-> F. ) $=
    ( wfal truan ) AB $.

  $( A ` /\ ` identity.  (Contributed by David A. Wheeler, 23-Feb-2018.) $)
  falantru $p |- ( ( F. /\ T. ) <-> F. ) $=
    ( wfal wtru wa simpl falim impbii ) ABCZAABDGEF $.

  $( A ` /\ ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.) $)
  falanfal $p |- ( ( F. /\ F. ) <-> F. ) $=
    ( wfal anidm ) AB $.

  $( A ` \/ ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.)  (Proof
     shortened by Andrew Salmon, 13-May-2011.) $)
  truortru $p |- ( ( T. \/ T. ) <-> T. ) $=
    ( wtru oridm ) AB $.

  $( A ` \/ ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.) $)
  truorfal $p |- ( ( T. \/ F. ) <-> T. ) $=
    ( wtru wfal wo tru orci bitru ) ABCABDEF $.

  $( A ` \/ ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.) $)
  falortru $p |- ( ( F. \/ T. ) <-> T. ) $=
    ( wfal wtru wo tru olci bitru ) ABCBADEF $.

  $( A ` \/ ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.)  (Proof
     shortened by Andrew Salmon, 13-May-2011.) $)
  falorfal $p |- ( ( F. \/ F. ) <-> F. ) $=
    ( wfal oridm ) AB $.

  $( A ` -> ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.) $)
  truimtru $p |- ( ( T. -> T. ) <-> T. ) $=
    ( wtru wi id bitru ) AABACD $.

  $( A ` -> ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.)  (Proof
     shortened by Andrew Salmon, 13-May-2011.) $)
  truimfal $p |- ( ( T. -> F. ) <-> F. ) $=
    ( wfal wtru wi tru a1bi bicomi ) ABACBADEF $.

  $( A ` -> ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.) $)
  falimtru $p |- ( ( F. -> T. ) <-> T. ) $=
    ( wfal wtru wi falim bitru ) ABCBDE $.

  $( A ` -> ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.) $)
  falimfal $p |- ( ( F. -> F. ) <-> T. ) $=
    ( wfal wi id bitru ) AABACD $.

  $( A ` -. ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.) $)
  nottru $p |- ( -. T. <-> F. ) $=
    ( wfal wtru wn df-fal bicomi ) ABCDE $.

  $( A ` -. ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.)  (Proof
     shortened by Andrew Salmon, 13-May-2011.) $)
  notfal $p |- ( -. F. <-> T. ) $=
    ( wfal wn fal bitru ) ABCD $.

  $( A ` <-> ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.)  (Proof
     shortened by Andrew Salmon, 13-May-2011.) $)
  trubitru $p |- ( ( T. <-> T. ) <-> T. ) $=
    ( wtru wb biid bitru ) AABACD $.

  $( A ` <-> ` identity.  (Contributed by David A. Wheeler, 23-Feb-2018.) $)
  trubifal $p |- ( ( T. <-> F. ) <-> F. ) $=
    ( wtru wfal wb wi wa dfbi2 truimfal falimtru anbi12i falantru 3bitri ) ABCA
    BDZBADZEBAEBABFLBMAGHIJK $.

  $( A ` <-> ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.)  (Proof
     shortened by Andrew Salmon, 13-May-2011.) $)
  falbitru $p |- ( ( F. <-> T. ) <-> F. ) $=
    ( wfal wtru wb bicom trubifal bitri ) ABCBACAABDEF $.

  $( A ` <-> ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.)  (Proof
     shortened by Andrew Salmon, 13-May-2011.) $)
  falbifal $p |- ( ( F. <-> F. ) <-> T. ) $=
    ( wfal wb biid bitru ) AABACD $.

  $( A ` \/_ ` identity.  (Contributed by David A. Wheeler, 2-Mar-2018.) $)
  truxortru $p |- ( ( T. \/_ T. ) <-> F. ) $=
    ( wtru wxo wo wa wn df-xor oridm nottru anidm xchnxbir anbi12i truan 3bitri
    wfal ) AABAACZAADZEZDANDNAAFOAQNAGANPHAIJKNLM $.

  $( A ` \/_ ` identity.  (Contributed by David A. Wheeler, 2-Mar-2018.) $)
  truxorfal $p |- ( ( T. \/_ F. ) <-> T. ) $=
    ( wtru wfal wxo wo wa wn df-xor truorfal notfal truan xchnxbir anidm 3bitri
    anbi12i ) ABCABDZABEZFZEAAEAABGOAQAHBAPIBJKNALM $.

  $( A ` \/_ ` identity.  (Contributed by David A. Wheeler, 2-Mar-2018.) $)
  falxortru $p |- ( ( F. \/_ T. ) <-> T. ) $=
    ( wfal wtru wo wa wn df-xor falortru notfal falantru xchnxbir anbi12i anidm
    wxo 3bitri ) ABMABCZABDZEZDBBDBABFOBQBGABPHIJKBLN $.

  $( A ` \/_ ` identity.  (Contributed by David A. Wheeler, 2-Mar-2018.) $)
  falxorfal $p |- ( ( F. \/_ F. ) <-> F. ) $=
    ( wfal wxo wo wa wn wtru df-xor oridm notfal anidm xchnxbir falantru 3bitri
    anbi12i ) AABAACZAADZEZDAFDAAAGOAQFAHAFPIAJKNLM $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Stoic logic indemonstrables (Chrysippus of Soli)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  The Greek Stoics developed a system of logic.  The Stoic Chrysippus, in
  particular, was often considered one of the greatest logicians of antiquity.
  Stoic logic is different from Aristotle's system, since it focuses on
  propositional logic, though later thinkers did combine the systems of the
  Stoics with Aristotle.  Jan Lukasiewicz reports, "For anybody familiar with
  mathematical logic it is self-evident that the Stoic dialectic is the ancient
  form of modern propositional logic"
  ( _On the history of the logic of proposition_ by Jan Lukasiewicz (1934),
  translated in: _Selected Works_ - Edited by Ludwik Borkowski -
  Amsterdam, North-Holland, 1970 pp. 197-217,
  referenced in "History of Logic"
  ~ https://www.historyoflogic.com/logic-stoics.htm ).
  For more about Aristotle's system, see barbara and related theorems.

  A key part of the Stoic logic system is a set of five "indemonstrables"
  assigned to Chrysippus of Soli by Diogenes Laertius, though in general it is
  difficult to assign specific ideas to specific thinkers.  The indemonstrables
  are described in, for example, [Lopez-Astorga] p. 11 , [Sanford] p. 39, and
  [Hitchcock] p. 5.  These indemonstrables are modus ponendo ponens (modus
  ponens) ~ ax-mp , modus tollendo tollens (modus tollens) ~ mto , modus
  ponendo tollens I ~ mptnan , modus ponendo tollens II ~ mptxor , and modus
  tollendo ponens (exclusive-or version) ~ mtpxor .  The first is an axiom, the
  second is already proved; in this section we prove the other three.  Since we
  assume or prove all of indemonstrables, the system of logic we use here is as
  at least as strong as the set of Stoic indemonstrables.  Note that modus
  tollendo ponens ~ mtpxor originally used exclusive-or, but over time the name
  modus tollendo ponens has increasingly referred to an inclusive-or variation,
  which is proved in ~ mtpor .  This set of indemonstrables is not the entire
  system of Stoic logic.

$)

  ${
    $( Minor premise for modus ponendo tollens 1. $)
    mptnan.min $e |- ph $.
    $( Major premise for modus ponendo tollens 1. $)
    mptnan.maj $e |- -. ( ph /\ ps ) $.
    $( Modus ponendo tollens 1, one of the "indemonstrables" in Stoic logic.
       See rule 1 on [Lopez-Astorga] p. 12 , rule 1 on [Sanford] p. 40, and
       rule A3 in [Hitchcock] p. 5.  Sanford describes this rule second (after
       ~ mptxor ) as a "safer, and these days much more common" version of
       modus ponendo tollens because it avoids confusion between inclusive-or
       and exclusive-or.  (Contributed by David A. Wheeler, 3-Jul-2016.) $)
    mptnan $p |- -. ps $=
      ( wn imnani ax-mp ) ABECABDFG $.
  $}

  ${
    $( Minor premise for modus ponendo tollens 2. $)
    mptxor.min $e |- ph $.
    $( Major premise for modus ponendo tollens 2. $)
    mptxor.maj $e |- ( ph \/_ ps ) $.
    $( Modus ponendo tollens 2, one of the "indemonstrables" in Stoic logic.
       Note that this uses exclusive-or ` \/_ ` .  See rule 2 on
       [Lopez-Astorga] p. 12 , rule 4 on [Sanford] p. 39 and rule A4 in
       [Hitchcock] p. 5 .  (Contributed by David A. Wheeler, 2-Mar-2018.) $)
    mptxor $p |- -. ps $=
      ( wo wa wn wxo df-xor mpbi simpri mptnan ) ABCABEZABFGZABHMNFDABIJKL $.
  $}

  ${
    $( Minor premise for modus tollendo ponens (inclusive-or version). $)
    mtpor.min $e |- -. ph $.
    $( Major premise for modus tollendo ponens (inclusive-or version). $)
    mtpor.max $e |- ( ph \/ ps ) $.
    $( Modus tollendo ponens (inclusive-or version), aka disjunctive syllogism.
       This is similar to ~ mtpxor , one of the five original "indemonstrables"
       in Stoic logic.  However, in Stoic logic this rule used exclusive-or,
       while the name modus tollendo ponens often refers to a variant of the
       rule that uses inclusive-or instead.  The rule says, "if ` ph ` is not
       true, and ` ph ` or ` ps ` (or both) are true, then ` ps ` must be
       true".  An alternate phrasing is, "Once you eliminate the impossible,
       whatever remains, no matter how improbable, must be the truth". --
       Sherlock Holmes (Sir Arthur Conan Doyle, 1890:  The Sign of the Four,
       ch. 6).  (Contributed by David A. Wheeler, 3-Jul-2016.)  (Proof
       shortened by Wolf Lammen, 11-Nov-2017.) $)
    mtpor $p |- ps $=
      ( wn ori ax-mp ) AEBCABDFG $.
  $}

  ${
    $( Minor premise for modus tollendo ponens (original exclusive-or version).
    $)
    mtpxor.min $e |- -. ph $.
    $( Major premise for modus tollendo ponens (original exclusive-or version).
    $)
    mtpxor.maj $e |- ( ph \/_ ps ) $.
    $( Modus tollendo ponens (original exclusive-or version), aka disjunctive
       syllogism, similar to ~ mtpor , one of the five "indemonstrables" in
       Stoic logic.  The rule says, "if ` ph ` is not true, and either ` ph `
       or ` ps ` (exclusively) are true, then ` ps ` must be true".  Today the
       name "modus tollendo ponens" often refers to a variant, the inclusive-or
       version as defined in ~ mtpor .  See rule 3 on [Lopez-Astorga] p. 12
       (note that the "or" is the same as ~ mptxor , that is, it is
       exclusive-or ~ df-xor ), rule 3 of [Sanford] p. 39 (where it is not as
       clearly stated which kind of "or" is used but it appears to be in the
       same sense as ~ mptxor ), and rule A5 in [Hitchcock] p. 5 (exclusive-or
       is expressly used).  (Contributed by David A. Wheeler, 4-Jul-2016.)
       (Proof shortened by Wolf Lammen, 11-Nov-2017.)  (Proof shortened by BJ,
       19-Apr-2019.) $)
    mtpxor $p |- ps $=
      ( wxo wo xoror ax-mp mtpor ) ABCABEABFDABGHI $.
  $}

  ${
    $( Premise for Stoic logic thema 1. $)
    stoic1.1 $e |- ( ( ph /\ ps ) -> th ) $.
    $( Stoic logic Thema 1 (part a).

       The first thema of the four Stoic logic themata, in its basic form, was:

       "When from two (assertibles) a third follows, then from either of them
       together with the contradictory of the conclusion the contradictory of
       the other follows."  (Apuleius Int. 209.9-14), see [Bobzien] p. 117 and
       ~ https://plato.stanford.edu/entries/logic-ancient/

       We will represent thema 1 as two very similar rules ~ stoic1a and
       ~ stoic1b to represent each side.  (Contributed by David A. Wheeler,
       16-Feb-2019.)  (Proof shortened by Wolf Lammen, 21-May-2020.) $)
    stoic1a $p |- ( ( ph /\ -. th ) -> -. ps ) $=
      ( ex con3dimp ) ABCABCDEF $.

    $( Stoic logic Thema 1 (part b).  The other part of thema 1 of Stoic logic;
       see ~ stoic1a .  (Contributed by David A. Wheeler, 16-Feb-2019.) $)
    stoic1b $p |- ( ( ps /\ -. th ) -> -. ph ) $=
      ( ancoms stoic1a ) BACABCDEF $.
  $}

  ${
    $( Premise 1 for Stoic logic thema 2 version a. $)
    stoic2a.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( Premise 2 for Stoic logic thema 2 version a. $)
    stoic2a.2 $e |- ( ( ph /\ ch ) -> th ) $.
    $( Stoic logic Thema 2 version a.

       Statement T2 of [Bobzien] p. 117 shows a reconstructed version of Stoic
       logic thema 2 as follows:  "When from two assertibles a third follows,
       and from the third and one (or both) of the two another follows, then
       this other follows from the first two."

       Bobzien uses constructs such as ` ph ` , ` ps |- ch ` ; in Metamath we
       will represent that construct as ` ph /\ ps -> ch ` .

       This version a is without the phrase "or both"; see ~ stoic2b for the
       version with the phrase "or both".  We already have this rule as
       ~ syldan , so here we show the equivalence and discourage its use.
       (New usage is discouraged.)  (Contributed by David A. Wheeler,
       17-Feb-2019.) $)
    stoic2a $p |- ( ( ph /\ ps ) -> th ) $=
      ( syldan ) ABCDEFG $.
  $}

  ${
    $( Premise 1 for Stoic logic thema 2 version b. $)
    stoic2b.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( Premise 2 for Stoic logic thema 2 version b. $)
    stoic2b.2 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
    $( Stoic logic Thema 2 version b.  See ~ stoic2a .

       Version b is with the phrase "or both".  We already have this rule as
       ~ mpd3an3 , so here we prove the equivalence and discourage its use.
       (New usage is discouraged.)  (Contributed by David A. Wheeler,
       17-Feb-2019.) $)
    stoic2b $p |- ( ( ph /\ ps ) -> th ) $=
      ( mpd3an3 ) ABCDEFG $.
  $}

  ${
    $( Premise 1 for Stoic logic thema 3. $)
    stoic3.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( Premise 2 for Stoic logic thema 3. $)
    stoic3.2 $e |- ( ( ch /\ th ) -> ta ) $.
    $( Stoic logic Thema 3.

       Statement T3 of [Bobzien] p. 116-117 discusses Stoic logic thema 3.

       "When from two (assemblies) a third follows, and from the one that
       follows (i.e., the third) together with another, external external
       assumption, another follows, then other follows from the first two and
       the externally co-assumed one.  (Simp.  Cael. 237.2-4)" (Contributed by
       David A. Wheeler, 17-Feb-2019.) $)
    stoic3 $p |- ( ( ph /\ ps /\ th ) -> ta ) $=
      ( wa sylan 3impa ) ABDEABHCDEFGIJ $.
  $}

  ${
    $( Premise 1 for Stoic logic thema 4a. $)
    stoic4a.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( Premise 2 for Stoic logic thema 4a. $)
    stoic4a.2 $e |- ( ( ch /\ ph /\ th ) -> ta ) $.
    $( Stoic logic Thema 4 version a.

       Statement T4 of [Bobzien] p. 117 shows a reconstructed version of Stoic
       logic thema 4:  "When from two assertibles a third follows, and from the
       third and one (or both) of the two and one (or more) external
       assertible(s) another follows, then this other follows from the first
       two and the external(s)."

       We use ` th ` to represent the "external" assertibles.  This is version
       a, which is without the phrase "or both"; see ~ stoic4b for the version
       with the phrase "or both".  (Contributed by David A. Wheeler,
       17-Feb-2019.) $)
    stoic4a $p |- ( ( ph /\ ps /\ th ) -> ta ) $=
      ( w3a 3adant3 simp1 simp3 syl3anc ) ABDHCADEABCDFIABDJABDKGL $.
  $}

  ${
    $( Premise 1 for Stoic logic thema 4b. $)
    stoic4b.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( Premise 2 for Stoic logic thema 4b. $)
    stoic4b.2 $e |- ( ( ( ch /\ ph /\ ps ) /\ th ) -> ta ) $.
    $( Stoic logic Thema 4 version b.

       This is version b, which is with the phrase "or both".  See ~ stoic4a
       for more information.  (Contributed by David A. Wheeler,
       17-Feb-2019.) $)
    stoic4b $p |- ( ( ph /\ ps /\ th ) -> ta ) $=
      ( w3a 3adant3 simp1 simp2 simp3 syl31anc ) ABDHCABDEABCDFIABDJABDKABDLGM
      $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Logical implication (continued)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    syl6an.1 $e |- ( ph -> ps ) $.
    syl6an.2 $e |- ( ph -> ( ch -> th ) ) $.
    syl6an.3 $e |- ( ( ps /\ th ) -> ta ) $.
    $( A syllogism deduction combined with conjoining antecedents.
       (Contributed by Alan Sare, 28-Oct-2011.) $)
    syl6an $p |- ( ph -> ( ch -> ta ) ) $=
      ( wa jctild syl6 ) ACBDIEACDBGFJHK $.
  $}

  ${
    syl10.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syl10.2 $e |- ( ph -> ( ps -> ( th -> ta ) ) ) $.
    syl10.3 $e |- ( ch -> ( ta -> et ) ) $.
    $( A nested syllogism inference.  (Contributed by Alan Sare,
       17-Jul-2011.) $)
    syl10 $p |- ( ph -> ( ps -> ( th -> et ) ) ) $=
      ( wi syl6 syldd ) ABDEFHABCEFJGIKL $.
  $}

  ${
    a1ddd.1 $e |- ( ph -> ( ps -> ( ch -> ta ) ) ) $.
    $( Triple deduction introducing an antecedent to a wff.  Deduction
       associated with ~ a1dd .  Double deduction associated with ~ a1d .
       Triple deduction associated with ~ ax-1 and ~ a1i .  (Contributed by
       Jeff Hankins, 4-Aug-2009.) $)
    a1ddd $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $=
      ( wi ax-1 syl8 ) ABCEDEGFEDHI $.
  $}

  $( Exportation implication also converting head from biconditional to
     conditional.  (Contributed by Alan Sare, 31-Dec-2011.) $)
  exbir $p |- ( ( ( ph /\ ps ) -> ( ch <-> th ) ) ->
              ( ph -> ( ps -> ( th -> ch ) ) ) ) $=
    ( wa wb wi biimpr imim2i expd ) ABEZCDFZGABDCGZLMKCDHIJ $.

  $( ~ impexp with a 3-conjunct antecedent.  (Contributed by Alan Sare,
     31-Dec-2011.) $)
  3impexp $p |- ( ( ( ph /\ ps /\ ch ) -> th ) <->
                ( ph -> ( ps -> ( ch -> th ) ) ) ) $=
    ( w3a wi id 3expd 3impd impbii ) ABCEDFZABCDFFFZKABCDKGHLABCDLGIJ $.

  $( ~ 3impexp with biconditional consequent of antecedent that is commuted in
     consequent.  (Contributed by Alan Sare, 31-Dec-2011.) $)
  3impexpbicom $p |- ( ( ( ph /\ ps /\ ch ) -> ( th <-> ta ) ) <->
                     ( ph -> ( ps -> ( ch -> ( ta <-> th ) ) ) ) ) $=
    ( w3a wb wi bicom imbi2 biimpcd mpi 3expd 3impexp biimpri imbitrrdi impbii
    ) ABCFZDEGZHZABCEDGZHHHZTABCUATSUAGZRUAHZDEIZUCTUDSUARJKLMUBRUASUDUBABCUANO
    UEPQ $.

  ${
    3impexpbicomi.1 $e |- ( ( ph /\ ps /\ ch ) -> ( th <-> ta ) ) $.
    $( Deduction form of ~ 3impexpbicom .  (Contributed by Alan Sare,
       31-Dec-2011.) $)
    3impexpbicomi $p |- ( ph -> ( ps -> ( ch -> ( ta <-> th ) ) ) ) $=
      ( wb w3a bicomd 3exp ) ABCEDGABCHDEFIJ $.
  $}

  $( Closed form of ~ ancoms .  (Contributed by Alan Sare, 31-Dec-2011.) $)
  ancomsimp $p |- ( ( ( ph /\ ps ) -> ch ) <-> ( ( ps /\ ph ) -> ch ) ) $=
    ( wa ancom imbi1i ) ABDBADCABEF $.

  ${
    expcomd.1 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
    $( Deduction form of ~ expcom .  (Contributed by Alan Sare,
       22-Jul-2012.) $)
    expcomd $p |- ( ph -> ( ch -> ( ps -> th ) ) ) $=
      ( expd com23 ) ABCDABCDEFG $.
  $}

  ${
    expdcom.1 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
    $( Commuted form of ~ expd .  (Contributed by Alan Sare, 18-Mar-2012.) $)
    expdcom $p |- ( ps -> ( ch -> ( ph -> th ) ) ) $=
      ( expd com3l ) ABCDABCDEFG $.
  $}

  $( Implication form of ~ simplbi2com .  (Contributed by Alan Sare,
     22-Jul-2012.) $)
  simplbi2comg $p |- ( ( ph <-> ( ps /\ ch ) ) -> ( ch -> ( ps -> ph ) ) ) $=
    ( wa wb biimpr expcomd ) ABCDZEBCAAHFG $.

  ${
    simplbi2com.1 $e |- ( ph <-> ( ps /\ ch ) ) $.
    $( A deduction eliminating a conjunct, similar to ~ simplbi2 .
       (Contributed by Alan Sare, 22-Jul-2012.)  (Proof shortened by Wolf
       Lammen, 10-Nov-2012.) $)
    simplbi2com $p |- ( ch -> ( ps -> ph ) ) $=
      ( simplbi2 com12 ) BCAABCDEF $.
  $}

  ${
    syl6ci.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syl6ci.2 $e |- ( ph -> th ) $.
    syl6ci.3 $e |- ( ch -> ( th -> ta ) ) $.
    $( A syllogism inference combined with contraction.  (Contributed by Alan
       Sare, 18-Mar-2012.) $)
    syl6ci $p |- ( ph -> ( ps -> ta ) ) $=
      ( a1d syl6c ) ABCDEFADBGIHJ $.
  $}

  ${
    mpisyl.1 $e |- ( ph -> ps ) $.
    mpisyl.2 $e |- ch $.
    mpisyl.3 $e |- ( ps -> ( ch -> th ) ) $.
    $( A syllogism combined with a modus ponens inference.  (Contributed by
       Alan Sare, 25-Jul-2011.) $)
    mpisyl $p |- ( ph -> th ) $=
      ( mpi syl ) ABDEBCDFGHI $.
  $}

  ${
    dcfromnotnotr.1 $e |- ( ph <-> ( ps \/ -. ps ) ) $.
    dcfromnotnotr.2 $e |- ( -. -. ph -> ph ) $.
    $( The decidability of a proposition ` ps ` follows from a suitable
       instance of double negation elimination (DNE).  Therefore, if we were to
       introduce DNE as a general principle (without the decidability condition
       in ~ notnotrdc ), then we could prove that every proposition is
       decidable, giving us the classical system of propositional calculus
       (since DNE itself is classically valid).  (Contributed by Adrian
       Ducourtial, 6-Oct-2025.) $)
    dcfromnotnotr $p |- DECID ps
        $=
      ( wdc wn wo nnexmid notbii 3imtr3i ax-mp df-dc mpbir ) BEBBFGZNFZFZNBHAFZ
      FAPNDQOANCIICJKBLM $.
  $}

  ${
    dcfromcon.1 $e |- ( ph <-> ( ch \/ -. ch ) ) $.
    dcfromcon.2 $e |- ( ps <-> T. ) $.
    dcfromcon.3 $e |- ( ( -. ph -> -. ps ) -> ( ps -> ph ) ) $.
    $( The decidability of a proposition ` ch ` follows from a suitable
       instance of the principle of contraposition.  Therefore, if we were to
       introduce contraposition as a general principle (without the
       decidability condition in ~ condc ), then we could prove that every
       proposition is decidable, giving us the classical system of
       propositional calculus (since the principle of contraposition is itself
       classically valid).  (Contributed by Adrian Ducourtial, 6-Oct-2025.) $)
    dcfromcon $p |- DECID ch
          $=
      ( wdc wn wo wtru nnexmid pm2.21i notbii imbi12i 3imtr3i ax-mp mptru df-dc
      wi mpbir ) CGCCHIZUAUAHZJHZSZJUASZUBUCCKLAHZBHZSBASUDUEFUFUBUGUCAUADMBJEM
      NBJAUAEDNOPQCRT $.
  $}

  ${
    dcfrompeirce.1 $e |- ( ph <-> ( ch \/ -. ch ) ) $.
    dcfrompeirce.2 $e |- ( ps <-> F. ) $.
    dcfrompeirce.3 $e |- ( ( ( ph -> ps ) -> ph ) -> ph ) $.
    $( The decidability of a proposition ` ch ` follows from a suitable
       instance of Peirce's law.  Therefore, if we were to introduce Peirce's
       law as a general principle (without the decidability condition in
       ~ peircedc ), then we could prove that every proposition is decidable,
       giving us the classical system of propositional calculus (since Perice's
       law is itself classically valid).  (Contributed by Adrian Ducourtial,
       6-Oct-2025.) $)
    dcfrompeirce $p |- DECID ch
          $=
      ( wdc wn wo wfal wi pm2.67-2 dfnot olcd imbi12i 3imtr3i ax-mp df-dc mpbir
      sylibr ) CGCCHZIZUBJKZUBKZUBUCUACUCCJKUACJUALCMTNABKZAKAUDUBFUEUCAUBAUBBJ
      DEODODPQCRS $.
  $}


$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Predicate calculus mostly without distinct variables
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Universal quantifier (continued)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  The universal quantifier was introduced above in ~ wal for use by ~ df-tru .
  See the comments in that section.  In this section, we continue with the
  first "real" use of it.
$)

  $( Declare some names for individual variables. $)
  $v x $.
  $v y $.
  $v z $.
  $v w $.
  $v v $.
  $v u $.
  $v t $.
  $( Let ` x ` be an individual variable. $)
  vx $f setvar x $.
  $( Let ` y ` be an individual variable. $)
  vy $f setvar y $.
  $( Let ` z ` be an individual variable. $)
  vz $f setvar z $.
  $( Let ` w ` be an individual variable. $)
  vw $f setvar w $.
  $( Let ` v ` be an individual variable. $)
  vv $f setvar v $.
  $( Let ` u ` be an individual variable. $)
  vu $f setvar u $.
  $( Let ` t ` be an individual variable. $)
  vt $f setvar t $.

  $( Axiom of Quantified Implication.  Axiom C4 of [Monk2] p. 105.
     (Contributed by NM, 5-Aug-1993.) $)
  ax-5 $a |- ( A. x ( ph -> ps ) -> ( A. x ph -> A. x ps ) ) $.

  $( Axiom of Quantifier Commutation.  This axiom says universal quantifiers
     can be swapped.  One of the predicate logic axioms which do not involve
     equality.  Axiom scheme C6' in [Megill] p. 448 (p. 16 of the preprint).
     Also appears as Lemma 12 of [Monk2] p. 109 and Axiom C5-3 of [Monk2]
     p. 113.  (Contributed by NM, 5-Aug-1993.) $)
  ax-7 $a |- ( A. x A. y ph -> A. y A. x ph ) $.

  ${
    ax-g.1 $e |- ph $.
    $( Rule of Generalization.  The postulated inference rule of predicate
       calculus.  See, e.g., Rule 2 of [Hamilton] p. 74.  This rule says that
       if something is unconditionally true, then it is true for all values of
       a variable.  For example, if we have proved ` x = x ` , we can conclude
       ` A. x x = x ` or even ` A. y x = x ` .  Theorem ~ spi shows we can go
       the other way also: in other words we can add or remove universal
       quantifiers from the beginning of any theorem as required.  (Contributed
       by NM, 5-Aug-1993.) $)
    ax-gen $a |- A. x ph $.
  $}

  ${
    gen2.1 $e |- ph $.
    $( Generalization applied twice.  (Contributed by NM, 30-Apr-1998.) $)
    gen2 $p |- A. x A. y ph $=
      ( wal ax-gen ) ACEBACDFF $.
  $}

  ${
    mpg.1 $e |- ( A. x ph -> ps ) $.
    mpg.2 $e |- ph $.
    $( Modus ponens combined with generalization.  (Contributed by NM,
       24-May-1994.) $)
    mpg $p |- ps $=
      ( wal ax-gen ax-mp ) ACFBACEGDH $.
  $}

  ${
    mpgbi.1 $e |- ( A. x ph <-> ps ) $.
    mpgbi.2 $e |- ph $.
    $( Modus ponens on biconditional combined with generalization.
       (Contributed by NM, 24-May-1994.)  (Proof shortened by Stefan Allan,
       28-Oct-2008.) $)
    mpgbi $p |- ps $=
      ( wal ax-gen mpbi ) ACFBACEGDH $.
  $}

  ${
    mpgbir.1 $e |- ( ph <-> A. x ps ) $.
    mpgbir.2 $e |- ps $.
    $( Modus ponens on biconditional combined with generalization.
       (Contributed by NM, 24-May-1994.)  (Proof shortened by Stefan Allan,
       28-Oct-2008.) $)
    mpgbir $p |- ph $=
      ( wal ax-gen mpbir ) ABCFBCEGDH $.
  $}

  ${
    a7s.1 $e |- ( A. x A. y ph -> ps ) $.
    $( Swap quantifiers in an antecedent.  (Contributed by NM, 5-Aug-1993.) $)
    a7s $p |- ( A. y A. x ph -> ps ) $=
      ( wal ax-7 syl ) ACFDFADFCFBADCGEH $.
  $}

  ${
    alimi.1 $e |- ( ph -> ps ) $.
    $( Inference quantifying both antecedent and consequent.  (Contributed by
       NM, 5-Aug-1993.) $)
    alimi $p |- ( A. x ph -> A. x ps ) $=
      ( wi wal ax-5 mpg ) ABEACFBCFECABCGDH $.

    $( Inference doubly quantifying both antecedent and consequent.
       (Contributed by NM, 3-Feb-2005.) $)
    2alimi $p |- ( A. x A. y ph -> A. x A. y ps ) $=
      ( wal alimi ) ADFBDFCABDEGG $.
  $}

  $( Theorem 19.20 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.)
     (Proof shortened by O'Cat, 30-Mar-2008.) $)
  alim $p |- ( A. x ( ph -> ps ) -> ( A. x ph -> A. x ps ) ) $=
    ( ax-5 ) ABCD $.

  ${
    al2imi.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Inference quantifying antecedent, nested antecedent, and consequent.
       (Contributed by NM, 5-Aug-1993.) $)
    al2imi $p |- ( A. x ph -> ( A. x ps -> A. x ch ) ) $=
      ( wal wi alimi alim syl ) ADFBCGZDFBDFCDFGAKDEHBCDIJ $.
  $}

  ${
    alanimi.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( Variant of ~ al2imi with conjunctive antecedent.  (Contributed by Andrew
       Salmon, 8-Jun-2011.) $)
    alanimi $p |- ( ( A. x ph /\ A. x ps ) -> A. x ch ) $=
      ( wal ex al2imi imp ) ADFBDFCDFABCDABCEGHI $.
  $}

  $c F/ $.  $( The not-free symbol. $)

  $( Extend wff definition to include the not-free predicate. $)
  wnf $a wff F/ x ph $.

  $( Define the not-free predicate for wffs.  This is read " ` x ` is not free
     in ` ph ` ".  Not-free means that the value of ` x ` cannot affect the
     value of ` ph ` , e.g., any occurrence of ` x ` in ` ph ` is effectively
     bound by a "for all" or something that expands to one (such as "there
     exists").  In particular, substitution for a variable not free in a wff
     does not affect its value ( ~ sbf ).  An example of where this is used is
     ~ stdpc5 .  See ~ nf2 for an alternate definition which does not involve
     nested quantifiers on the same variable.

     Nonfreeness is a commonly used condition, so it is useful to have a
     notation for it.  Surprisingly, there is no common formal notation for it,
     so here we devise one.  Our definition lets us work with the notion of
     nonfreeness within the logic itself rather than as a metalogical side
     condition.

     To be precise, our definition really means "effectively not free", because
     it is slightly less restrictive than the usual textbook definition for
     "not free" (which considers syntactic freedom).  For example, ` x ` is
     effectively not free in the expression ` x = x ` (even though ` x ` is
     syntactically free in it, so would be considered "free" in the usual
     textbook definition) because the value of ` x ` in the formula ` x = x `
     does not affect the truth of that formula (and thus substitutions will not
     change the result), see ~ nfequid .  (Contributed by Mario Carneiro,
     11-Aug-2016.) $)
  df-nf $a |- ( F/ x ph <-> A. x ( ph -> A. x ph ) ) $.

  ${
    nfi.1 $e |- ( ph -> A. x ph ) $.
    $( Deduce that ` x ` is not free in ` ph ` from the definition.
       (Contributed by Mario Carneiro, 11-Aug-2016.) $)
    nfi $p |- F/ x ph $=
      ( wnf wal wi df-nf mpgbir ) ABDAABEFBABGCH $.
  $}

  ${
    hbth.1 $e |- ph $.
    $( No variable is (effectively) free in a theorem.

       This and later "hypothesis-building" lemmas, with labels starting
       "hb...", allow us to construct proofs of formulas of the form
       ` |- ( ph -> A. x ph ) ` from smaller formulas of this form.  These are
       useful for constructing hypotheses that state " ` x ` is (effectively)
       not free in ` ph ` ".  (Contributed by NM, 5-Aug-1993.) $)
    hbth $p |- ( ph -> A. x ph ) $=
      ( wal ax-gen a1i ) ABDAABCEF $.

    $( No variable is (effectively) free in a theorem.  (Contributed by Mario
       Carneiro, 11-Aug-2016.) $)
    nfth $p |- F/ x ph $=
      ( hbth nfi ) ABABCDE $.
  $}

  ${
    nfnth.1 $e |- -. ph $.
    $( No variable is (effectively) free in a non-theorem.  (Contributed by
       Mario Carneiro, 6-Dec-2016.) $)
    nfnth $p |- F/ x ph $=
      ( wal pm2.21i nfi ) ABAABDCEF $.
  $}

  $( The true constant has no free variables.  (This can also be proven in one
     step with ~ nfv , but this proof does not use ~ ax-17 .)  (Contributed by
     Mario Carneiro, 6-Oct-2016.) $)
  nftru $p |- F/ x T. $=
    ( wtru tru nfth ) BACD $.

  ${
    alimdh.1 $e |- ( ph -> A. x ph ) $.
    alimdh.2 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction from Theorem 19.20 of [Margaris] p. 90.  (Contributed by NM,
       4-Jan-2002.) $)
    alimdh $p |- ( ph -> ( A. x ps -> A. x ch ) ) $=
      ( wal wi al2imi syl ) AADGBDGCDGHEABCDFIJ $.
  $}

  $( Theorem 19.15 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)
  albi $p |- ( A. x ( ph <-> ps ) -> ( A. x ph <-> A. x ps ) ) $=
    ( wb wal biimp al2imi biimpr impbid ) ABDZCEACEBCEJABCABFGJBACABHGI $.

  ${
    alrimih.1 $e |- ( ph -> A. x ph ) $.
    alrimih.2 $e |- ( ph -> ps ) $.
    $( Inference from Theorem 19.21 of [Margaris] p. 90.  (Contributed by NM,
       5-Aug-1993.)  (New usage is discouraged.) $)
    alrimih $p |- ( ph -> A. x ps ) $=
      ( wal alimi syl ) AACFBCFDABCEGH $.
  $}

  ${
    albii.1 $e |- ( ph <-> ps ) $.
    $( Inference adding universal quantifier to both sides of an equivalence.
       (Contributed by NM, 7-Aug-1994.) $)
    albii $p |- ( A. x ph <-> A. x ps ) $=
      ( wb wal albi mpg ) ABEACFBCFECABCGDH $.

    $( Inference adding 2 universal quantifiers to both sides of an
       equivalence.  (Contributed by NM, 9-Mar-1997.) $)
    2albii $p |- ( A. x A. y ph <-> A. x A. y ps ) $=
      ( wal albii ) ADFBDFCABDEGG $.
  $}

  ${
    hbxfrbi.1 $e |- ( ph <-> ps ) $.
    hbxfrbi.2 $e |- ( ps -> A. x ps ) $.
    $( A utility lemma to transfer a bound-variable hypothesis builder into a
       definition.  (Contributed by Jonathan Ben-Naim, 3-Jun-2011.) $)
    hbxfrbi $p |- ( ph -> A. x ph ) $=
      ( wal albii 3imtr4i ) BBCFAACFEDABCDGH $.
  $}

  ${
    nfbii.1 $e |- ( ph <-> ps ) $.
    $( Equality theorem for not-free.  (Contributed by Mario Carneiro,
       11-Aug-2016.) $)
    nfbii $p |- ( F/ x ph <-> F/ x ps ) $=
      ( wal wi wnf albii imbi12i df-nf 3bitr4i ) AACEZFZCEBBCEZFZCEACGBCGMOCABL
      NDABCDHIHACJBCJK $.

    ${
      nfxfr.2 $e |- F/ x ps $.
      $( A utility lemma to transfer a bound-variable hypothesis builder into a
         definition.  (Contributed by Mario Carneiro, 11-Aug-2016.) $)
      nfxfr $p |- F/ x ph $=
        ( wnf nfbii mpbir ) ACFBCFEABCDGH $.
    $}

    ${
      nfxfrd.2 $e |- ( ch -> F/ x ps ) $.
      $( A utility lemma to transfer a bound-variable hypothesis builder into a
         definition.  (Contributed by Mario Carneiro, 24-Sep-2016.) $)
      nfxfrd $p |- ( ch -> F/ x ph ) $=
        ( wnf nfbii sylibr ) CBDGADGFABDEHI $.
    $}
  $}

  ${
    alcoms.1 $e |- ( A. x A. y ph -> ps ) $.
    $( Swap quantifiers in an antecedent.  (Contributed by NM, 11-May-1993.) $)
    alcoms $p |- ( A. y A. x ph -> ps ) $=
      ( wal ax-7 syl ) ACFDFADFCFBADCGEH $.
  $}

  ${
    hbal.1 $e |- ( ph -> A. x ph ) $.
    $( If ` x ` is not free in ` ph ` , it is not free in ` A. y ph ` .
       (Contributed by NM, 5-Aug-1993.) $)
    hbal $p |- ( A. y ph -> A. x A. y ph ) $=
      ( wal alimi ax-7 syl ) ACEZABEZCEIBEAJCDFACBGH $.
  $}

  $( Theorem 19.5 of [Margaris] p. 89.  (Contributed by NM, 5-Aug-1993.) $)
  alcom $p |- ( A. x A. y ph <-> A. y A. x ph ) $=
    ( wal ax-7 impbii ) ACDBDABDCDABCEACBEF $.

  ${
    alrimdh.1 $e |- ( ph -> A. x ph ) $.
    alrimdh.2 $e |- ( ps -> A. x ps ) $.
    alrimdh.3 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction from Theorem 19.21 of [Margaris] p. 90.  (Contributed by NM,
       10-Feb-1997.)  (Proof shortened by Andrew Salmon, 13-May-2011.) $)
    alrimdh $p |- ( ph -> ( ps -> A. x ch ) ) $=
      ( wal alimdh syl5 ) BBDHACDHFABCDEGIJ $.
  $}

  ${
    albidh.1 $e |- ( ph -> A. x ph ) $.
    albidh.2 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for universal quantifier (deduction form).
       (Contributed by NM, 5-Aug-1993.) $)
    albidh $p |- ( ph -> ( A. x ps <-> A. x ch ) ) $=
      ( wb wal alrimih albi syl ) ABCGZDHBDHCDHGALDEFIBCDJK $.
  $}

  $( Theorem 19.26 of [Margaris] p. 90.  Also Theorem *10.22 of
     [WhiteheadRussell] p. 119.  (Contributed by NM, 5-Aug-1993.)  (Proof
     shortened by Wolf Lammen, 4-Jul-2014.) $)
  19.26 $p |- ( A. x ( ph /\ ps ) <-> ( A. x ph /\ A. x ps ) ) $=
    ( wa wal simpl alimi simpr jca id alanimi impbii ) ABDZCEZACEZBCEZDNOPMACAB
    FGMBCABHGIABMCMJKL $.

  $( Theorem 19.26 of [Margaris] p. 90 with two quantifiers.  (Contributed by
     NM, 3-Feb-2005.) $)
  19.26-2 $p |- ( A. x A. y ( ph /\ ps ) <->
                ( A. x A. y ph /\ A. x A. y ps ) ) $=
    ( wa wal 19.26 albii bitri ) ABEDFZCFADFZBDFZEZCFKCFLCFEJMCABDGHKLCGI $.

  $( Theorem 19.26 of [Margaris] p. 90 with triple conjunction.  (Contributed
     by NM, 13-Sep-2011.) $)
  19.26-3an $p |- ( A. x ( ph /\ ps /\ ch )
                   <-> ( A. x ph /\ A. x ps /\ A. x ch ) ) $=
    ( wa wal w3a 19.26 anbi1i bitri df-3an albii 3bitr4i ) ABEZCEZDFZADFZBDFZEZ
    CDFZEZABCGZDFQRTGPNDFZTEUANCDHUCSTABDHIJUBODABCKLQRTKM $.

  $( Theorem 19.33 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)
  19.33 $p |- ( ( A. x ph \/ A. x ps ) -> A. x ( ph \/ ps ) ) $=
    ( wal wo orc alimi olc jaoi ) ACDABEZCDBCDAJCABFGBJCBAHGI $.

  $( Theorem *11.21 in [WhiteheadRussell] p. 160.  (Contributed by Andrew
     Salmon, 24-May-2011.) $)
  alrot3 $p |- ( A. x A. y A. z ph <-> A. y A. z A. x ph ) $=
    ( wal alcom albii bitri ) ADEZCEBEIBEZCEABEDEZCEIBCFJKCABDFGH $.

  $( Rotate 4 universal quantifiers twice.  (Contributed by NM, 2-Feb-2005.)
     (Proof shortened by Wolf Lammen, 28-Jun-2014.) $)
  alrot4 $p |- ( A. x A. y A. z A. w ph <-> A. z A. w A. x A. y ph ) $=
    ( wal alrot3 albii alcom 3bitri ) AEFDFCFZBFACFZEFZDFZBFMBFZDFLBFEFZDFKNBAC
    DEGHMBDIOPDLBEIHJ $.

  $( Split a biconditional and distribute quantifier.  (Contributed by NM,
     18-Aug-1993.) $)
  albiim $p |- ( A. x ( ph <-> ps ) <->
             ( A. x ( ph -> ps ) /\ A. x ( ps -> ph ) ) ) $=
    ( wb wal wi wa dfbi2 albii 19.26 bitri ) ABDZCEABFZBAFZGZCEMCENCEGLOCABHIMN
    CJK $.

  $( Split a biconditional and distribute 2 quantifiers.  (Contributed by NM,
     3-Feb-2005.) $)
  2albiim $p |- ( A. x A. y ( ph <-> ps ) <->
             ( A. x A. y ( ph -> ps ) /\ A. x A. y ( ps -> ph ) ) ) $=
    ( wb wal wi wa albiim albii 19.26 bitri ) ABEDFZCFABGDFZBAGDFZHZCFNCFOCFHMP
    CABDIJNOCKL $.

  ${
    hband.1 $e |- ( ph -> ( ps -> A. x ps ) ) $.
    hband.2 $e |- ( ph -> ( ch -> A. x ch ) ) $.
    $( Deduction form of bound-variable hypothesis builder ~ hban .
       (Contributed by NM, 2-Jan-2002.) $)
    hband $p |- ( ph -> ( ( ps /\ ch ) -> A. x ( ps /\ ch ) ) ) $=
      ( wa wal anim12d 19.26 imbitrrdi ) ABCGZBDHZCDHZGLDHABMCNEFIBCDJK $.
  $}

  ${
    hb3and.1 $e |- ( ph -> ( ps -> A. x ps ) ) $.
    hb3and.2 $e |- ( ph -> ( ch -> A. x ch ) ) $.
    hb3and.3 $e |- ( ph -> ( th -> A. x th ) ) $.
    $( Deduction form of bound-variable hypothesis builder ~ hb3an .
       (Contributed by NM, 17-Feb-2013.) $)
    hb3and $p |- ( ph -> ( ( ps /\ ch /\ th ) -> A. x ( ps /\ ch /\ th ) ) ) $=
      ( w3a wal 3anim123d 19.26-3an imbitrrdi ) ABCDIZBEJZCEJZDEJZINEJABOCPDQFG
      HKBCDELM $.
  $}

  ${
    hbald.1 $e |- ( ph -> A. y ph ) $.
    hbald.2 $e |- ( ph -> ( ps -> A. x ps ) ) $.
    $( Deduction form of bound-variable hypothesis builder ~ hbal .
       (Contributed by NM, 2-Jan-2002.) $)
    hbald $p |- ( ph -> ( A. y ps -> A. x A. y ps ) ) $=
      ( wal alimdh ax-7 syl6 ) ABDGZBCGZDGKCGABLDEFHBDCIJ $.
  $}

  $( Declare the existential quantifier symbol. $)
  $c E. $.   $( Backwards E (read:  "there exists") $)

  $( Extend wff definition to include the existential quantifier ("there
     exists"). $)
  wex $a wff E. x ph $.

  $( ` x ` is bound in ` E. x ph ` .  One of the axioms of predicate logic.
     (Contributed by Mario Carneiro, 31-Jan-2015.) $)
  ax-ie1 $a |- ( E. x ph -> A. x E. x ph ) $.

  $( Define existential quantification. ` E. x ph ` means "there exists at
     least one set ` x ` such that ` ph ` is true".  One of the axioms of
     predicate logic.  (Contributed by Mario Carneiro, 31-Jan-2015.) $)
  ax-ie2 $a |- ( A. x ( ps -> A. x ps ) ->
               ( A. x ( ph -> ps ) <-> ( E. x ph -> ps ) ) ) $.

  $( ` x ` is not free in ` E. x ph ` .  (Contributed by NM, 5-Aug-1993.) $)
  hbe1 $p |- ( E. x ph -> A. x E. x ph ) $=
    ( ax-ie1 ) ABC $.

  $( ` x ` is not free in ` E. x ph ` .  (Contributed by Mario Carneiro,
     11-Aug-2016.) $)
  nfe1 $p |- F/ x E. x ph $=
    ( wex hbe1 nfi ) ABCBABDE $.

  $( Closed form of Theorem 19.23 of [Margaris] p. 90.  (Contributed by NM,
     7-Nov-2005.)  (Revised by Mario Carneiro, 1-Feb-2015.) $)
  19.23ht $p |- ( A. x ( ps -> A. x ps ) ->
               ( A. x ( ph -> ps ) <-> ( E. x ph -> ps ) ) ) $=
    ( ax-ie2 ) ABCD $.

  ${
    19.23h.1 $e |- ( ps -> A. x ps ) $.
    $( Theorem 19.23 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.)
       (Revised by Mario Carneiro, 1-Feb-2015.) $)
    19.23h $p |- ( A. x ( ph -> ps ) <-> ( E. x ph -> ps ) ) $=
      ( wal wi wex wb ax-gen 19.23ht ax-mp ) BBCEFZCEABFCEACGBFHLCDIABCJK $.
  $}

  $( Theorem 19.7 of [Margaris] p. 89.  To read this intuitionistically, think
     of it as "if ` ph ` can be refuted for all ` x ` , then it is not possible
     to find an ` x ` for which ` ph ` holds" (and likewise for the converse).
     Comparing this with ~ dfexdc illustrates that statements which look
     similar (to someone used to classical logic) can be different
     intuitionistically due to different placement of negations.  (Contributed
     by NM, 5-Aug-1993.)  (Revised by NM, 1-Feb-2015.)  (Revised by Mario
     Carneiro, 12-May-2015.) $)
  alnex $p |- ( A. x -. ph <-> -. E. x ph ) $=
    ( wfal wi wal wex wn fal pm2.21i 19.23h dfnot albii 3bitr4i ) ACDZBEABFZCDA
    GZBEOGACBCCBEHIJPNBAKLOKM $.

  ${
    nex.1 $e |- -. ph $.
    $( Generalization rule for negated wff.  (Contributed by NM,
       18-May-1994.) $)
    nex $p |- -. E. x ph $=
      ( wn wex alnex mpgbi ) ADABEDBABFCG $.
  $}

  $( Defining ` E. x ph ` given decidability.  It is common in classical logic
     to define ` E. x ph ` as ` -. A. x -. ph ` but in intuitionistic logic
     without a decidability condition, that is only an implication not an
     equivalence, as seen at ~ exalim .  (Contributed by Jim Kingdon,
     15-Mar-2018.) $)
  dfexdc $p |- ( DECID E. x ph
                 -> ( E. x ph <-> -. A. x -. ph ) ) $=
    ( wn wal wex wb wdc alnex a1i con2biidc ) ACBDZABEZKLCFLGABHIJ $.

  $( One direction of a classical definition of existential quantification.
     One direction of Definition of [Margaris] p. 49.  For a decidable
     proposition, this is an equivalence, as seen as ~ dfexdc .  (Contributed
     by Jim Kingdon, 29-Jul-2018.) $)
  exalim $p |- ( E. x ph -> -. A. x -. ph ) $=
    ( wn wal wex alnex biimpi con2i ) ACBDZABEZIJCABFGH $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Equality predicate (continued)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  The equality predicate was introduced above in ~ wceq for use by ~ df-tru .
  See the comments in that section.  In this section, we continue with the
  first "real" use of it.

$)

  $( Extend wff definition to include atomic formulas using the equality
     predicate.

     (Instead of introducing ~ weq as an axiomatic statement, as was done in an
     older version of this database, we introduce it by "proving" a special
     case of set theory's more general ~ wceq .  This lets us avoid overloading
     the ` = ` connective, thus preventing ambiguity that would complicate
     certain Metamath parsers.  However, logically ~ weq is considered to be a
     primitive syntax, even though here it is artificially "derived" from
     ~ wceq .  Note:  To see the proof steps of this syntax proof, type "show
     proof weq /all" in the Metamath program.)  (Contributed by NM,
     24-Jan-2006.) $)
  weq $p wff x = y $=
    ( cv wceq ) ACBCD $.

  $( Axiom of Equality.  One of the equality and substitution axioms of
     predicate calculus with equality.  This is similar to, but not quite, a
     transitive law for equality (proved later as ~ equtr ).  Axiom scheme C8'
     in [Megill] p. 448 (p. 16 of the preprint).  Also appears as Axiom C7 of
     [Monk2] p. 105.

     Axioms ~ ax-8 through ~ ax-16 are the axioms having to do with equality,
     substitution, and logical properties of our binary predicate ` e. ` (which
     later in set theory will mean "is a member of").  Note that all axioms
     except ~ ax-16 and ~ ax-17 are still valid even when ` x ` , ` y ` , and
     ` z ` are replaced with the same variable because they do not have any
     distinct variable (Metamath's $d) restrictions.  Distinct variable
     restrictions are required for ~ ax-16 and ~ ax-17 only.  (Contributed by
     NM, 5-Aug-1993.) $)
  ax-8 $a |- ( x = y -> ( x = z -> y = z ) ) $.

  $( Axiom of Quantifier Substitution.  One of the equality and substitution
     axioms of predicate calculus with equality.  Appears as Lemma L12 in
     [Megill] p. 445 (p. 12 of the preprint).

     The original version of this axiom was ~ ax-10o ("o" for "old") and was
     replaced with this shorter ~ ax-10 in May 2008.  The old axiom is proved
     from this one as Theorem ~ ax10o .  Conversely, this axiom is proved from
     ~ ax-10o as Theorem ~ ax10 .  (Contributed by NM, 5-Aug-1993.) $)
  ax-10 $a |- ( A. x x = y -> A. y y = x ) $.

  $( Axiom of Variable Substitution.  One of the 5 equality axioms of predicate
     calculus.  The final consequent ` A. x ( x = y -> ph ) ` is a way of
     expressing " ` y ` substituted for ` x ` in wff ` ph ` " (cf. ~ sb6 ).  It
     is based on Lemma 16 of [Tarski] p. 70 and Axiom C8 of [Monk2] p. 105,
     from which it can be proved by cases.

     Variants of this axiom which are equivalent in classical logic but which
     have not been shown to be equivalent for intuitionistic logic are
     ~ ax11v , ~ ax11v2 and ~ ax-11o .  (Contributed by NM, 5-Aug-1993.) $)
  ax-11 $a |- ( x = y -> ( A. y ph -> A. x ( x = y -> ph ) ) ) $.

  $( Axiom of Quantifier Introduction.  One of the equality and substitution
     axioms of predicate calculus with equality.  Informally, it says that
     whenever ` z ` is distinct from ` x ` and ` y ` , and ` x = y ` is true,
     then ` x = y ` quantified with ` z ` is also true.  In other words, ` z `
     is irrelevant to the truth of ` x = y ` .  Axiom scheme C9' in [Megill]
     p. 448 (p. 16 of the preprint).  It apparently does not otherwise appear
     in the literature but is easily proved from textbook predicate calculus by
     cases.

     This axiom has been modified from the original ~ ax12 for compatibility
     with intuitionistic logic.  (Contributed by Mario Carneiro, 31-Jan-2015.)
     Use its alias ~ ax12or instead, for labeling consistency.
     (New usage is discouraged.) $)
  ax-i12 $a |- ( A. z z = x \/ ( A. z z = y \/
                 A. z ( x = y -> A. z x = y ) ) ) $.

  $( Alias for ~ ax-i12 , to be used in place of it for labeling consistency.
     (Contributed by NM, 3-Feb-2015.) $)
  ax12or $p |- ( A. z z = x \/ ( A. z z = y \/
                 A. z ( x = y -> A. z x = y ) ) ) $=
    ( ax-i12 ) ABCD $.

  $( Axiom of bundling.  The general idea of this axiom is that two variables
     are either distinct or non-distinct.  That idea could be expressed as
     ` A. z z = x \/ -. A. z z = x ` .  However, we instead choose an axiom
     which has many of the same consequences, but which is different with
     respect to a universe which contains only one object. ` A. z z = x ` holds
     if ` z ` and ` x ` are the same variable, likewise for ` z ` and ` y ` ,
     and ` A. x A. z ( x = y -> A. z x = y ) ` holds if ` z ` is distinct from
     the others (and the universe has at least two objects).

     As with other statements of the form "x is decidable (either true or
     false)", this does not entail the full Law of the Excluded Middle (which
     is the proposition that all statements are decidable), but instead merely
     the assertion that particular kinds of statements are decidable (or in
     this case, an assertion similar to decidability).

     This axiom implies ~ ax-i12 as can be seen at ~ axi12 .  Whether ~ ax-bndl
     can be proved from the remaining axioms including ~ ax-i12 is not known.

     The reason we call this "bundling" is that a statement without a distinct
     variable constraint "bundles" together two statements, one in which the
     two variables are the same and one in which they are different.
     (Contributed by Mario Carneiro and Jim Kingdon, 14-Mar-2018.) $)
  ax-bndl $a |- ( A. z z = x \/
                       ( A. z z = y \/ A. x A. z ( x = y -> A. z x = y ) ) ) $.

  $( Axiom of Specialization.  A quantified wff implies the wff without a
     quantifier (i.e. an instance, or special case, of the generalized wff).
     In other words if something is true for all ` x ` , it is true for any
     specific ` x ` (that would typically occur as a free variable in the wff
     substituted for ` ph ` ).  (A free variable is one that does not occur in
     the scope of a quantifier: ` x ` and ` y ` are both free in ` x = y ` ,
     but only ` x ` is free in ` A. y x = y ` .)  Axiom scheme C5' in [Megill]
     p. 448 (p. 16 of the preprint).  Also appears as Axiom B5 of [Tarski]
     p. 67 (under his system S2, defined in the last paragraph on p. 77).

     Note that the converse of this axiom does not hold in general, but a
     weaker inference form of the converse holds and is expressed as rule
     ~ ax-gen .  Conditional forms of the converse are given by ~ ax12 ,
     ~ ax-16 , and ~ ax-17 .

     Unlike the more general textbook Axiom of Specialization, we cannot choose
     a variable different from ` x ` for the special case.  For use, that
     requires the assistance of equality axioms, and we deal with it later
     after we introduce the definition of proper substitution - see ~ stdpc4 .

     (Contributed by NM, 5-Aug-1993.) $)
  ax-4 $a |- ( A. x ph -> ph ) $.

  $( Specialization.  Another name for ~ ax-4 .  (Contributed by NM,
     21-May-2008.) $)
  sp $p |- ( A. x ph -> ph ) $=
    ( ax-4 ) ABC $.

  $( Rederive the original version of the axiom from ~ ax-i12 .  (Contributed
     by Mario Carneiro, 3-Feb-2015.) $)
  ax12 $p |- ( -. A. z z = x -> ( -. A. z z = y ->
              ( x = y -> A. z x = y ) ) ) $=
    ( cv wceq wal wn wi wo ax12or ori ord ax-4 syl6 ) CDZADZECFZGZOBDZECFZGPSEZ
    UACFHZCFZUBRTUCQTUCIABCJKLUBCMN $.

  $( Bound-variable hypothesis builder for ` x = x ` .  This theorem tells us
     that any variable, including ` x ` , is effectively not free in
     ` x = x ` , even though ` x ` is technically free according to the
     traditional definition of free variable.

     The proof uses only ~ ax-8 and ~ ax-i12 on top of (the FOL analogue of)
     modal logic KT. This shows that this can be proved without ~ ax-i9 , even
     though Theorem ~ equid cannot.  A shorter proof using ~ ax-i9 is
     obtainable from ~ equid and ~ hbth .  (Contributed by NM, 13-Jan-2011.)
     (Proof shortened by Wolf Lammen, 23-Mar-2014.) $)
  hbequid $p |- ( x = x -> A. y x = x ) $=
    ( cv wceq wal wi wo ax12or ax-8 pm2.43i alimi a1d ax-4 jaoi ax-mp ) BCACZDZ
    BEZRPPDZSBEZFZBEZGZGUAAABHRUAUCRTSQSBQSBAAIJKLZRUAUBUDUABMNNO $.

  $( Proof that ~ ax-i12 follows from ~ ax-bndl .  So that we can track which
     theorems rely on ~ ax-bndl , proofs should reference ~ ax12or rather than
     this theorem.  (Contributed by Jim Kingdon, 17-Aug-2018.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  axi12 $p |- ( A. z z = x \/ ( A. z z = y \/
                 A. z ( x = y -> A. z x = y ) ) ) $=
    ( cv wceq wal wi wo ax-bndl sp orim2i ax-mp ) CDZADZECFZMBDZECFZNPEZRCFGCFZ
    AFZHZHOQSHZHABCIUAUBOTSQSAJKKL $.

  $( Commutation law for identical variable specifiers.  The antecedent and
     consequent are true when ` x ` and ` y ` are substituted with the same
     variable.  Lemma L12 in [Megill] p. 445 (p. 12 of the preprint).
     (Contributed by NM, 5-Aug-1993.) $)
  alequcom $p |- ( A. x x = y -> A. y y = x ) $=
    ( ax-10 ) ABC $.

  ${
    alequcoms.1 $e |- ( A. x x = y -> ph ) $.
    $( A commutation rule for identical variable specifiers.  (Contributed by
       NM, 5-Aug-1993.) $)
    alequcoms $p |- ( A. y y = x -> ph ) $=
      ( weq wal alequcom syl ) CBECFBCEBFACBGDH $.
  $}

  ${
    nalequcoms.1 $e |- ( -. A. x x = y -> ph ) $.
    $( A commutation rule for distinct variable specifiers.  (Contributed by
       NM, 2-Jan-2002.)  (Revised by Mario Carneiro, 2-Feb-2015.) $)
    nalequcoms $p |- ( -. A. y y = x -> ph ) $=
      ( cv wceq wal wn alequcom con3i syl ) CEZBEZFCGZHMLFBGZHAONBCIJDK $.
  $}

  $( Consequence of the definition of not-free.  (Contributed by Mario
     Carneiro, 26-Sep-2016.) $)
  nfr $p |- ( F/ x ph -> ( ph -> A. x ph ) ) $=
    ( wnf wal wi df-nf sp sylbi ) ABCAABDEZBDIABFIBGH $.

  ${
    nfri.1 $e |- F/ x ph $.
    $( Consequence of the definition of not-free.  (Contributed by Mario
       Carneiro, 11-Aug-2016.) $)
    nfri $p |- ( ph -> A. x ph ) $=
      ( wnf wal wi nfr ax-mp ) ABDAABEFCABGH $.
  $}

  ${
    nfrd.1 $e |- ( ph -> F/ x ps ) $.
    $( Consequence of the definition of not-free in a context.  (Contributed by
       Mario Carneiro, 11-Aug-2016.) $)
    nfrd $p |- ( ph -> ( ps -> A. x ps ) ) $=
      ( wnf wal wi nfr syl ) ABCEBBCFGDBCHI $.
  $}

  ${
    alimd.1 $e |- F/ x ph $.
    alimd.2 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction from Theorem 19.20 of [Margaris] p. 90.  (Contributed by Mario
       Carneiro, 24-Sep-2016.) $)
    alimd $p |- ( ph -> ( A. x ps -> A. x ch ) ) $=
      ( nfri alimdh ) ABCDADEGFH $.
  $}

  ${
    alrimi.1 $e |- F/ x ph $.
    alrimi.2 $e |- ( ph -> ps ) $.
    $( Inference from Theorem 19.21 of [Margaris] p. 90.  (Contributed by Mario
       Carneiro, 24-Sep-2016.) $)
    alrimi $p |- ( ph -> A. x ps ) $=
      ( nfri alrimih ) ABCACDFEG $.
  $}

  ${
    nfd.1 $e |- F/ x ph $.
    nfd.2 $e |- ( ph -> ( ps -> A. x ps ) ) $.
    $( Deduce that ` x ` is not free in ` ps ` in a context.  (Contributed by
       Mario Carneiro, 24-Sep-2016.) $)
    nfd $p |- ( ph -> F/ x ps ) $=
      ( wal wi wnf nfri alrimih df-nf sylibr ) ABBCFGZCFBCHAMCACDIEJBCKL $.
  $}

  ${
    nfdh.1 $e |- ( ph -> A. x ph ) $.
    nfdh.2 $e |- ( ph -> ( ps -> A. x ps ) ) $.
    $( Deduce that ` x ` is not free in ` ps ` in a context.  (Contributed by
       Mario Carneiro, 24-Sep-2016.) $)
    nfdh $p |- ( ph -> F/ x ps ) $=
      ( nfi nfd ) ABCACDFEG $.
  $}

  ${
    nfrimi.1 $e |- F/ x ph $.
    nfrimi.2 $e |- F/ x ( ph -> ps ) $.
    $( Moving an antecedent outside ` F/ ` .  (Contributed by Jim Kingdon,
       23-Mar-2018.) $)
    nfrimi $p |- ( ph -> F/ x ps ) $=
      ( wal wi nfri ax-5 syl2im pm2.86i nfd ) ABCDABBCFZABGZNCFAACFMNCEHACDHABC
      IJKL $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Axiom ax-17 - first use of the $d distinct variable statement
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x ph $.
    $( Axiom to quantify a variable over a formula in which it does not occur.
       Axiom C5 in [Megill] p. 444 (p. 11 of the preprint).  Also appears as
       Axiom B6 (p. 75) of system S2 of [Tarski] p. 77 and Axiom C5-1 of
       [Monk2] p. 113.

       (Contributed by NM, 5-Aug-1993.) $)
    ax-17 $a |- ( ph -> A. x ph ) $.
  $}

  ${
    $d x ps $.
    $( ~ ax-17 with antecedent.  (Contributed by NM, 1-Mar-2013.) $)
    a17d $p |- ( ph -> ( ps -> A. x ps ) ) $=
      ( wal wi ax-17 a1i ) BBCDEABCFG $.
  $}

  ${
    $d x ph $.
    $( If ` x ` is not present in ` ph ` , then ` x ` is not free in ` ph ` .
       (Contributed by Mario Carneiro, 11-Aug-2016.) $)
    nfv $p |- F/ x ph $=
      ( ax-17 nfi ) ABABCD $.
  $}

  ${
    $d x ps $.
    $( ~ nfv with antecedent.  Useful in proofs of deduction versions of
       bound-variable hypothesis builders such as ~ nfimd .  (Contributed by
       Mario Carneiro, 6-Oct-2016.) $)
    nfvd $p |- ( ph -> F/ x ps ) $=
      ( wnf nfv a1i ) BCDABCEF $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Introduce Axiom of Existence
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Axiom of Existence.  One of the equality and substitution axioms of
     predicate calculus with equality.  One thing this axiom tells us is that
     at least one thing exists (although ~ ax-4 and possibly others also tell
     us that, i.e. they are not valid in the empty domain of a "free logic").
     In this form (not requiring that ` x ` and ` y ` be distinct) it was used
     in an axiom system of Tarski (see Axiom B7' in footnote 1 of
     [KalishMontague] p. 81.)  Another name for this theorem is ~ a9e , which
     has additional remarks.  (Contributed by Mario Carneiro, 31-Jan-2015.) $)
  ax-i9 $a |- E. x x = y $.

  $( Derive ~ ax-9 from ~ ax-i9 , the modified version for intuitionistic
     logic.  Although ~ ax-9 does hold intuistionistically, in intuitionistic
     logic it is weaker than ~ ax-i9 .  (Contributed by NM, 3-Feb-2015.) $)
  ax-9 $p |- -. A. x -. x = y $=
    ( cv wceq wn wal wex ax-i9 notnoti alnex mtbir ) ACBCDZEAFLAGZEMABHILAJK $.

  $( ~ equid with some quantification and negation without using ~ ax-4 or
     ~ ax-17 .  (Contributed by NM, 13-Jan-2011.)  (Proof shortened by Wolf
     Lammen, 27-Feb-2014.) $)
  equidqe $p |- -. A. y -. x = x $=
    ( weq wn wal ax-9 ax-8 pm2.43i con3i alimi mto ) AACZDZBEBACZDZBEBAFMOBNLNL
    BAAGHIJK $.

  $( A special case of ~ ax-4 without using ~ ax-4 or ~ ax-17 .  (Contributed
     by NM, 13-Jan-2011.) $)
  ax4sp1 $p |- ( A. y -. x = x -> -. x = x ) $=
    ( weq wn wal equidqe pm2.21i ) AACDZBEHABFG $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Additional intuitionistic axioms
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( ` x ` is not free in ` A. x ph ` .  One of the axioms of predicate logic.
     (Contributed by Mario Carneiro, 31-Jan-2015.) $)
  ax-ial $a |- ( A. x ph -> A. x A. x ph ) $.

  $( Axiom of quantifier collection.  (Contributed by Mario Carneiro,
     31-Jan-2015.) $)
  ax-i5r $a |- ( ( A. x ph -> A. x ps ) -> A. x ( A. x ph -> ps ) ) $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Predicate calculus including ax-4, without distinct variables
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    spi.1 $e |- A. x ph $.
    $( Inference reversing generalization (specialization).  (Contributed by
       NM, 5-Aug-1993.) $)
    spi $p |- ph $=
      ( wal ax-4 ax-mp ) ABDACABEF $.
  $}

  ${
    sps.1 $e |- ( ph -> ps ) $.
    $( Generalization of antecedent.  (Contributed by NM, 5-Aug-1993.) $)
    sps $p |- ( A. x ph -> ps ) $=
      ( wal sp syl ) ACEABACFDG $.
  $}

  ${
    spsd.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction generalizing antecedent.  (Contributed by NM, 17-Aug-1994.) $)
    spsd $p |- ( ph -> ( A. x ps -> ch ) ) $=
      ( wal sp syl5 ) BDFBACBDGEH $.
  $}

  ${
    nfbidf.1 $e |- F/ x ph $.
    nfbidf.2 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( An equality theorem for effectively not free.  (Contributed by Mario
       Carneiro, 4-Oct-2016.) $)
    nfbidf $p |- ( ph -> ( F/ x ps <-> F/ x ch ) ) $=
      ( wal wi wnf nfri albidh imbi12d df-nf 3bitr4g ) ABBDGZHZDGCCDGZHZDGBDICD
      IAPRDADEJZABCOQFABCDSFKLKBDMCDMN $.
  $}

  $( ` x ` is not free in ` A. x ph ` .  Example in Appendix in [Megill] p. 450
     (p. 19 of the preprint).  Also Lemma 22 of [Monk2] p. 114.  (Contributed
     by NM, 5-Aug-1993.) $)
  hba1 $p |- ( A. x ph -> A. x A. x ph ) $=
    ( ax-ial ) ABC $.

  $( ` x ` is not free in ` A. x ph ` .  (Contributed by Mario Carneiro,
     11-Aug-2016.) $)
  nfa1 $p |- F/ x A. x ph $=
    ( wal hba1 nfi ) ABCBABDE $.

  ${
    axc4i.1 $e |- ( A. x ph -> ps ) $.
    $( Inference version of ~ 19.21 .  (Contributed by NM, 3-Jan-1993.) $)
    axc4i $p |- ( A. x ph -> A. x ps ) $=
      ( wal nfa1 alrimi ) ACEBCACFDG $.
  $}

  ${
    a5i.1 $e |- ( A. x ph -> ps ) $.
    $( Inference generalizing a consequent.  (Contributed by NM,
       5-Aug-1993.) $)
    a5i $p |- ( A. x ph -> A. x ps ) $=
      ( wal wi hba1 ax-5 syl5 mpg ) ACEZBFZKBCEZFCKKCELCEMACGKBCHIDJ $.
  $}

  $( ` x ` is not free in ` F/ x ph ` .  (Contributed by Mario Carneiro,
     11-Aug-2016.) $)
  nfnf1 $p |- F/ x F/ x ph $=
    ( wnf wal wi df-nf nfa1 nfxfr ) ABCAABDEZBDBABFIBGH $.

  ${
    hb.1 $e |- ( ph -> A. x ph ) $.
    hb.2 $e |- ( ps -> A. x ps ) $.
    $( If ` x ` is not free in ` ph ` and ` ps ` , it is not free in
       ` ( ph -> ps ) ` .  (Contributed by NM, 5-Aug-1993.)  (Proof shortened
       by O'Cat, 3-Mar-2008.)  (Revised by Mario Carneiro, 2-Feb-2015.) $)
    hbim $p |- ( ( ph -> ps ) -> A. x ( ph -> ps ) ) $=
      ( wi wal ax-4 imim12i ax-i5r imim1i alimi 3syl ) ABFZACGZBCGZFOBFZCGNCGOA
      BPACHEIABCJQNCAOBDKLM $.

    $( If ` x ` is not free in ` ph ` and ` ps ` , it is not free in
       ` ( ph \/ ps ) ` .  (Contributed by NM, 5-Aug-1993.)  (Revised by NM,
       2-Feb-2015.) $)
    hbor $p |- ( ( ph \/ ps ) -> A. x ( ph \/ ps ) ) $=
      ( wo wal orc alimi syl olc jaoi ) AABFZCGZBAACGNDAMCABHIJBBCGNEBMCBAKIJL
      $.

    $( If ` x ` is not free in ` ph ` and ` ps ` , it is not free in
       ` ( ph /\ ps ) ` .  (Contributed by NM, 5-Aug-1993.)  (Proof shortened
       by Mario Carneiro, 2-Feb-2015.) $)
    hban $p |- ( ( ph /\ ps ) -> A. x ( ph /\ ps ) ) $=
      ( wa wal anim12i 19.26 sylibr ) ABFZACGZBCGZFKCGALBMDEHABCIJ $.

    $( If ` x ` is not free in ` ph ` and ` ps ` , it is not free in
       ` ( ph <-> ps ) ` .  (Contributed by NM, 5-Aug-1993.) $)
    hbbi $p |- ( ( ph <-> ps ) -> A. x ( ph <-> ps ) ) $=
      ( wb wi wa dfbi2 hbim hban hbxfrbi ) ABFABGZBAGZHCABIMNCABCDEJBACEDJKL $.

    hb.3 $e |- ( ch -> A. x ch ) $.
    $( If ` x ` is not free in ` ph ` , ` ps ` , and ` ch ` , it is not free in
       ` ( ph \/ ps \/ ch ) ` .  (Contributed by NM, 14-Sep-2003.) $)
    hb3or $p |- ( ( ph \/ ps \/ ch ) -> A. x ( ph \/ ps \/ ch ) ) $=
      ( w3o wo df-3or hbor hbxfrbi ) ABCHABIZCIDABCJMCDABDEFKGKL $.

    $( If ` x ` is not free in ` ph ` , ` ps ` , and ` ch ` , it is not free in
       ` ( ph /\ ps /\ ch ) ` .  (Contributed by NM, 14-Sep-2003.) $)
    hb3an $p |- ( ( ph /\ ps /\ ch ) -> A. x ( ph /\ ps /\ ch ) ) $=
      ( w3a wa df-3an hban hbxfrbi ) ABCHABIZCIDABCJMCDABDEFKGKL $.
  $}

  $( Lemma 24 of [Monk2] p. 114.  (Contributed by NM, 29-May-2008.) $)
  hba2 $p |- ( A. y A. x ph -> A. x A. y A. x ph ) $=
    ( wal hba1 hbal ) ABDBCABEF $.

  $( Lemma 23 of [Monk2] p. 114.  (Contributed by NM, 29-May-2008.) $)
  hbia1 $p |- ( ( A. x ph -> A. x ps ) -> A. x ( A. x ph -> A. x ps ) ) $=
    ( wal hba1 hbim ) ACDBCDCACEBCEF $.

  ${
    19.3h.1 $e |- ( ph -> A. x ph ) $.
    $( A wff may be quantified with a variable not free in it.  Theorem 19.3 of
       [Margaris] p. 89.  (Contributed by NM, 5-Aug-1993.)  (Revised by NM,
       21-May-2007.) $)
    19.3h $p |- ( A. x ph <-> ph ) $=
      ( wal ax-4 impbii ) ABDAABECF $.
  $}

  ${
    19.3.1 $e |- F/ x ph $.
    $( A wff may be quantified with a variable not free in it.  Theorem 19.3 of
       [Margaris] p. 89.  (Contributed by NM, 5-Aug-1993.)  (Revised by Mario
       Carneiro, 24-Sep-2016.) $)
    19.3 $p |- ( A. x ph <-> ph ) $=
      ( wal sp nfri impbii ) ABDAABEABCFG $.
  $}

  ${
    19.16.1 $e |- F/ x ph $.
    $( Theorem 19.16 of [Margaris] p. 90.  (Contributed by NM, 12-Mar-1993.) $)
    19.16 $p |- ( A. x ( ph <-> ps ) -> ( ph <-> A. x ps ) ) $=
      ( wal wb 19.3 albi bitr3id ) AACEABFCEBCEACDGABCHI $.
  $}

  ${
    19.17.1 $e |- F/ x ps $.
    $( Theorem 19.17 of [Margaris] p. 90.  (Contributed by NM, 12-Mar-1993.) $)
    19.17 $p |- ( A. x ( ph <-> ps ) -> ( A. x ph <-> ps ) ) $=
      ( wb wal albi 19.3 bitrdi ) ABECFACFBCFBABCGBCDHI $.
  $}

  ${
    19.21h.1 $e |- ( ph -> A. x ph ) $.
    $( Theorem 19.21 of [Margaris] p. 90.  The hypothesis can be thought of
       as " ` x ` is not free in ` ph ` ".  New proofs should use ~ 19.21
       instead.  (Contributed by NM, 5-Aug-1993.)
       (New usage is discouraged.) $)
    19.21h $p |- ( A. x ( ph -> ps ) <-> ( ph -> A. x ps ) ) $=
      ( wi wal alim syl5 hba1 hbim ax-4 imim2i alrimih impbii ) ABEZCFZABCFZEZA
      ACFPQDABCGHROCAQCDBCIJQBABCKLMN $.
  $}

  ${
    19.21bi.1 $e |- ( ph -> A. x ps ) $.
    $( Inference from Theorem 19.21 of [Margaris] p. 90.  (Contributed by NM,
       5-Aug-1993.) $)
    19.21bi $p |- ( ph -> ps ) $=
      ( wal ax-4 syl ) ABCEBDBCFG $.
  $}

  ${
    19.21bbi.1 $e |- ( ph -> A. x A. y ps ) $.
    $( Inference removing double quantifier.  (Contributed by NM,
       20-Apr-1994.) $)
    19.21bbi $p |- ( ph -> ps ) $=
      ( wal 19.21bi ) ABDABDFCEGG $.
  $}

  ${
    19.27h.1 $e |- ( ps -> A. x ps ) $.
    $( Theorem 19.27 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)
    19.27h $p |- ( A. x ( ph /\ ps ) <-> ( A. x ph /\ ps ) ) $=
      ( wa wal 19.26 19.3h anbi2i bitri ) ABECFACFZBCFZEKBEABCGLBKBCDHIJ $.
  $}

  ${
    19.27.1 $e |- F/ x ps $.
    $( Theorem 19.27 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)
    19.27 $p |- ( A. x ( ph /\ ps ) <-> ( A. x ph /\ ps ) ) $=
      ( wa wal 19.26 19.3 anbi2i bitri ) ABECFACFZBCFZEKBEABCGLBKBCDHIJ $.
  $}

  ${
    19.28h.1 $e |- ( ph -> A. x ph ) $.
    $( Theorem 19.28 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)
    19.28h $p |- ( A. x ( ph /\ ps ) <-> ( ph /\ A. x ps ) ) $=
      ( wa wal 19.26 19.3h anbi1i bitri ) ABECFACFZBCFZEALEABCGKALACDHIJ $.
  $}

  ${
    19.28.1 $e |- F/ x ph $.
    $( Theorem 19.28 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)
    19.28 $p |- ( A. x ( ph /\ ps ) <-> ( ph /\ A. x ps ) ) $=
      ( wa wal 19.26 19.3 anbi1i bitri ) ABECFACFZBCFZEALEABCGKALACDHIJ $.
  $}

  ${
    nfan1.1 $e |- F/ x ph $.
    nfan1.2 $e |- ( ph -> F/ x ps ) $.
    $( A closed form of ~ nfan .  (Contributed by Mario Carneiro,
       3-Oct-2016.) $)
    nfan1 $p |- F/ x ( ph /\ ps ) $=
      ( wa wal nfrd imdistani nfri 19.28h sylibr nfi ) ABFZCNABCGZFNCGABOABCEHI
      ABCACDJKLM $.
  $}

  ${
    nfan.1 $e |- F/ x ph $.
    nfan.2 $e |- F/ x ps $.
    $( If ` x ` is not free in ` ph ` and ` ps ` , it is not free in
       ` ( ph /\ ps ) ` .  (Contributed by Mario Carneiro, 11-Aug-2016.)
       (Proof shortened by Wolf Lammen, 13-Jan-2018.) $)
    nfan $p |- F/ x ( ph /\ ps ) $=
      ( wnf a1i nfan1 ) ABCDBCFAEGH $.

    nfan.3 $e |- F/ x ch $.
    $( If ` x ` is not free in ` ph ` , ` ps ` , and ` ch ` , it is not free in
       ` ( ph /\ ps /\ ch ) ` .  (Contributed by Mario Carneiro,
       11-Aug-2016.) $)
    nf3an $p |- F/ x ( ph /\ ps /\ ch ) $=
      ( w3a wa df-3an nfan nfxfr ) ABCHABIZCIDABCJMCDABDEFKGKL $.
  $}

  ${
    nford.1 $e |- ( ph -> F/ x ps ) $.
    nford.2 $e |- ( ph -> F/ x ch ) $.
    $( If in a context ` x ` is not free in ` ps ` and ` ch ` , it is not free
       in ` ( ps \/ ch ) ` .  (Contributed by Jim Kingdon, 29-Oct-2019.) $)
    nford $p |- ( ph -> F/ x ( ps \/ ch ) ) $=
      ( wo wal wi wnf wa df-nf anbi12i biimpi syl2anc 19.26 sylibr alimi imim2i
      orc olc jaao syl ) ABCGZUDDHZIZDHZUDDJABBDHZIZCCDHZIZKZDHZUGAUIDHZUKDHZKZ
      UMABDJZCDJZUPEFUQURKUPUQUNURUOBDLCDLMNOUIUKDPQULUFDUIBUEUKCUHUEBBUDDBCTRS
      UJUECCUDDCBUARSUBRUCUDDLQ $.
  $}

  ${
    nfand.1 $e |- ( ph -> F/ x ps ) $.
    nfand.2 $e |- ( ph -> F/ x ch ) $.
    $( If in a context ` x ` is not free in ` ps ` and ` ch ` , it is not free
       in ` ( ps /\ ch ) ` .  (Contributed by Mario Carneiro, 7-Oct-2016.) $)
    nfand $p |- ( ph -> F/ x ( ps /\ ch ) ) $=
      ( wa wal wi wnf jca df-nf anbi12i 19.26 bitr4i anim12 imbitrrdi alimi syl
      sylbi sylibr ) ABCGZUBDHZIZDHZUBDJABDJZCDJZGZUEAUFUGEFKUHBBDHZIZCCDHZIZGZ
      DHZUEUHUJDHZULDHZGUNUFUOUGUPBDLCDLMUJULDNOUMUDDUMUBUIUKGUCBUICUKPBCDNQRTS
      UBDLUA $.

    nfand.3 $e |- ( ph -> F/ x th ) $.
    $( Deduction form of bound-variable hypothesis builder ~ nf3an .
       (Contributed by NM, 17-Feb-2013.)  (Revised by Mario Carneiro,
       16-Oct-2016.) $)
    nf3and $p |- ( ph -> F/ x ( ps /\ ch /\ th ) ) $=
      ( w3a wa df-3an nfand nfxfrd ) BCDIBCJZDJAEBCDKANDEABCEFGLHLM $.
  $}

  ${
    hbim1.1 $e |- ( ph -> A. x ph ) $.
    hbim1.2 $e |- ( ph -> ( ps -> A. x ps ) ) $.
    $( A closed form of ~ hbim .  (Contributed by NM, 5-Aug-1993.) $)
    hbim1 $p |- ( ( ph -> ps ) -> A. x ( ph -> ps ) ) $=
      ( wi wal a2i 19.21h sylibr ) ABFZABCGZFKCGABLEHABCDIJ $.
  $}

  ${
    nfim1.1 $e |- F/ x ph $.
    nfim1.2 $e |- ( ph -> F/ x ps ) $.
    $( A closed form of ~ nfim .  (Contributed by NM, 5-Aug-1993.)  (Revised by
       Mario Carneiro, 24-Sep-2016.)  (Proof shortened by Wolf Lammen,
       2-Jan-2018.) $)
    nfim1 $p |- F/ x ( ph -> ps ) $=
      ( wi nfri nfrd hbim1 nfi ) ABFCABCACDGABCEHIJ $.
  $}

  ${
    nfim.1 $e |- F/ x ph $.
    nfim.2 $e |- F/ x ps $.
    $( If ` x ` is not free in ` ph ` and ` ps ` , it is not free in
       ` ( ph -> ps ) ` .  (Contributed by Mario Carneiro, 11-Aug-2016.)
       (Proof shortened by Wolf Lammen, 2-Jan-2018.) $)
    nfim $p |- F/ x ( ph -> ps ) $=
      ( wnf a1i nfim1 ) ABCDBCFAEGH $.
  $}

  ${
    hbimd.1 $e |- ( ph -> A. x ph ) $.
    hbimd.2 $e |- ( ph -> ( ps -> A. x ps ) ) $.
    hbimd.3 $e |- ( ph -> ( ch -> A. x ch ) ) $.
    $( Deduction form of bound-variable hypothesis builder ~ hbim .
       (Contributed by NM, 1-Jan-2002.)  (Revised by NM, 2-Feb-2015.) $)
    hbimd $p |- ( ph -> ( ( ps -> ch ) -> A. x ( ps -> ch ) ) ) $=
      ( wi wal imim2d ax-4 imim1i ax-i5r syl syl6 imim1d alimdh syld ) ABCHZBDI
      ZCHZDIZSDIASBCDIZHZUBACUCBGJUDTUCHUBTBUCBDKLBCDMNOAUASDEABTCFPQR $.
  $}

  ${
    nfor.1 $e |- F/ x ph $.
    nfor.2 $e |- F/ x ps $.
    $( If ` x ` is not free in ` ph ` and ` ps ` , it is not free in
       ` ( ph \/ ps ) ` .  (Contributed by Jim Kingdon, 11-Mar-2018.) $)
    nfor $p |- F/ x ( ph \/ ps ) $=
      ( wo nfri hbor nfi ) ABFCABCACDGBCEGHI $.
  $}

  ${
    hbbid.1 $e |- ( ph -> A. x ph ) $.
    hbbid.2 $e |- ( ph -> ( ps -> A. x ps ) ) $.
    hbbid.3 $e |- ( ph -> ( ch -> A. x ch ) ) $.
    $( Deduction form of bound-variable hypothesis builder ~ hbbi .
       (Contributed by NM, 1-Jan-2002.) $)
    hbbid $p |- ( ph -> ( ( ps <-> ch ) -> A. x ( ps <-> ch ) ) ) $=
      ( wi wa wal wb hbimd anim12d dfbi2 albiim 3imtr4g ) ABCHZCBHZIQDJZRDJZIBC
      KZUADJAQSRTABCDEFGLACBDEGFLMBCNBCDOP $.
  $}

  ${
    nfal.1 $e |- F/ x ph $.
    $( If ` x ` is not free in ` ph ` , it is not free in ` A. y ph ` .
       (Contributed by Mario Carneiro, 11-Aug-2016.)  Remove dependency on
       ~ ax-4 .  (Revised by GG, 25-Aug-2024.) $)
    nfal $p |- F/ x A. y ph $=
      ( wnf wal wi df-nf biimpi alimi ax-7 ax-5 syl6 3syl sylibr mpg ) ABEZACFZ
      BEZCQCFZRRBFZGZBFZSTAABFZGZBFZCFUECFZBFUCQUFCQUFABHIJUECBKUGUBBUGRUDCFUAA
      UDCLACBKMJNRBHODP $.
    $( $j usage 'nfal' avoids 'ax-4'; $)

    $( If ` x ` is not free in ` ph ` , it is not free in ` F/ y ph ` .
       (Contributed by Mario Carneiro, 11-Aug-2016.)  (Proof shortened by Wolf
       Lammen, 30-Dec-2017.) $)
    nfnf $p |- F/ x F/ y ph $=
      ( wnf wal wi df-nf nfal nfim nfxfr ) ACEAACFZGZCFBACHMBCALBDABCDIJIK $.
  $}

  $( Closed form of ~ nfal .  (Contributed by Jim Kingdon, 11-May-2018.) $)
  nfalt $p |- ( A. y F/ x ph -> F/ x A. y ph ) $=
    ( wal wi wnf alim alcom imbitrdi alimi df-nf albii bitri 3imtr4i ) AABDZEZC
    DZBDZACDZSBDZEZBDABFZCDZSBFQUABQSOCDTAOCGACBHIJUCPBDZCDRUBUDCABKLPCBHMSBKN
    $.

  $( Lemma 24 of [Monk2] p. 114.  (Contributed by Mario Carneiro,
     24-Sep-2016.) $)
  nfa2 $p |- F/ x A. y A. x ph $=
    ( wal nfa1 nfal ) ABDBCABEF $.

  $( Lemma 23 of [Monk2] p. 114.  (Contributed by Mario Carneiro,
     24-Sep-2016.) $)
  nfia1 $p |- F/ x ( A. x ph -> A. x ps ) $=
    ( wal nfa1 nfim ) ACDBCDCACEBCEF $.

  $( Closed form of Theorem 19.21 of [Margaris] p. 90.  (Contributed by NM,
     27-May-1997.)  (New usage is discouraged.) $)
  19.21ht $p |- ( A. x ( ph -> A. x ph ) ->
               ( A. x ( ph -> ps ) <-> ( ph -> A. x ps ) ) ) $=
    ( wal wi alim imim2d com12 sps hba1 ax-4 a1i hbimd imim2i alimi syl6 impbid
    ) AACDZEZCDZABEZCDZABCDZEZSUBUDECUBSUDUBRUCAABCFGHITUDUDCDUBTAUCCSCJSCKUCUC
    CDETBCJLMUDUACUCBABCKNOPQ $.

  $( Closed form of Theorem 19.21 of [Margaris] p. 90.  (Contributed by NM,
     27-May-1997.) $)
  19.21t $p |- ( F/ x ph ->
               ( A. x ( ph -> ps ) <-> ( ph -> A. x ps ) ) ) $=
    ( wnf wal wi wb df-nf 19.21ht sylbi ) ACDAACEFCEABFCEABCEFGACHABCIJ $.

  ${
    19.21.1 $e |- F/ x ph $.
    $( Theorem 19.21 of [Margaris] p. 90.  The hypothesis can be thought of
       as " ` x ` is not free in ` ph ` ".  (Contributed by NM, 5-Aug-1993.)
       (Revised by Mario Carneiro, 24-Sep-2016.) $)
    19.21 $p |- ( A. x ( ph -> ps ) <-> ( ph -> A. x ps ) ) $=
      ( wnf wi wal wb 19.21t ax-mp ) ACEABFCGABCGFHDABCIJ $.
  $}

  ${
    stdpc5.1 $e |- F/ x ph $.
    $( An axiom scheme of standard predicate calculus that emulates Axiom 5 of
       [Mendelson] p. 69.  The hypothesis ` F/ x ph ` can be thought of as
       emulating " ` x ` is not free in ` ph ` ".  With this definition, the
       meaning of "not free" is less restrictive than the usual textbook
       definition; for example ` x ` would not (for us) be free in ` x = x ` by
       ~ nfequid .  This theorem scheme can be proved as a metatheorem of
       Mendelson's axiom system, even though it is slightly stronger than his
       Axiom 5.  (Contributed by NM, 22-Sep-1993.)  (Revised by Mario Carneiro,
       12-Oct-2016.)  (Proof shortened by Wolf Lammen, 1-Jan-2018.) $)
    stdpc5 $p |- ( A. x ( ph -> ps ) -> ( ph -> A. x ps ) ) $=
      ( wi wal 19.21 biimpi ) ABECFABCFEABCDGH $.
  $}

  ${
    nfimd.1 $e |- ( ph -> F/ x ps ) $.
    nfimd.2 $e |- ( ph -> F/ x ch ) $.
    $( If in a context ` x ` is not free in ` ps ` and ` ch ` , then it is not
       free in ` ( ps -> ch ) ` .  (Contributed by Mario Carneiro,
       24-Sep-2016.)  (Proof shortened by Wolf Lammen, 30-Dec-2017.) $)
    nfimd $p |- ( ph -> F/ x ( ps -> ch ) ) $=
      ( wnf wi wal nfnf1 nfri nfr imim2d 19.21t biimprd syl9r alrimdh imbitrrdi
      df-nf sylc ) ABDGZCDGZBCHZDGZEFUAUBUCUCDIZHZDIUDUAUBUFDUADBDJKUBDCDJKUBUC
      BCDIZHZUAUEUBCUGBCDLMUAUEUHBCDNOPQUCDSRT $.
  $}

  ${
    aaanh.1 $e |- ( ph -> A. y ph ) $.
    aaanh.2 $e |- ( ps -> A. x ps ) $.
    $( Rearrange universal quantifiers.  (Contributed by NM, 12-Aug-1993.) $)
    aaanh $p |- ( A. x A. y ( ph /\ ps ) <-> ( A. x ph /\ A. y ps ) ) $=
      ( wa wal 19.28h albii hbal 19.27h bitri ) ABGDHZCHABDHZGZCHACHOGNPCABDEIJ
      AOCBCDFKLM $.
  $}

  ${
    aaan.1 $e |- F/ y ph $.
    aaan.2 $e |- F/ x ps $.
    $( Rearrange universal quantifiers.  (Contributed by NM, 12-Aug-1993.) $)
    aaan $p |- ( A. x A. y ( ph /\ ps ) <-> ( A. x ph /\ A. y ps ) ) $=
      ( wa wal 19.28 albii nfal 19.27 bitri ) ABGDHZCHABDHZGZCHACHOGNPCABDEIJAO
      CBCDFKLM $.
  $}

  ${
    nfbid.1 $e |- ( ph -> F/ x ps ) $.
    nfbid.2 $e |- ( ph -> F/ x ch ) $.
    $( If in a context ` x ` is not free in ` ps ` and ` ch ` , then it is not
       free in ` ( ps <-> ch ) ` .  (Contributed by Mario Carneiro,
       24-Sep-2016.)  (Proof shortened by Wolf Lammen, 29-Dec-2017.) $)
    nfbid $p |- ( ph -> F/ x ( ps <-> ch ) ) $=
      ( wb wi wa dfbi2 nfimd nfand nfxfrd ) BCGBCHZCBHZIADBCJANODABCDEFKACBDFEK
      LM $.
  $}

  ${
    nfbi.1 $e |- F/ x ph $.
    nfbi.2 $e |- F/ x ps $.
    $( If ` x ` is not free in ` ph ` and ` ps ` , then it is not free in
       ` ( ph <-> ps ) ` .  (Contributed by Mario Carneiro, 11-Aug-2016.)
       (Proof shortened by Wolf Lammen, 2-Jan-2018.) $)
    nfbi $p |- F/ x ( ph <-> ps ) $=
      ( wb wnf wtru a1i nfbid mptru ) ABFCGHABCACGHDIBCGHEIJK $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  The existential quantifier
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( If a wff is true, then it is true for at least one instance.  Special case
     of Theorem 19.8 of [Margaris] p. 89.  (Contributed by NM, 5-Aug-1993.) $)
  19.8a $p |- ( ph -> E. x ph ) $=
    ( wex wi wal id hbe1 19.23h mpbir spi ) AABCZDZBLBEKKDKFAKBABGHIJ $.

  ${
    19.8ad.1 $e |- ( ph -> ps ) $.
    $( If a wff is true, it is true for at least one instance.  Deduction form
       of ~ 19.8a .  (Contributed by DAW, 13-Feb-2017.) $)
    19.8ad $p |- ( ph -> E. x ps ) $=
      ( wex 19.8a syl ) ABBCEDBCFG $.
  $}

  ${
    19.23bi.1 $e |- ( E. x ph -> ps ) $.
    $( Inference from Theorem 19.23 of [Margaris] p. 90.  (Contributed by NM,
       5-Aug-1993.) $)
    19.23bi $p |- ( ph -> ps ) $=
      ( wex 19.8a syl ) AACEBACFDG $.
  $}

  ${
    exlimih.1 $e |- ( ps -> A. x ps ) $.
    exlimih.2 $e |- ( ph -> ps ) $.
    $( Inference from Theorem 19.23 of [Margaris] p. 90.  (Contributed by NM,
       5-Aug-1993.)  (Proof shortened by Andrew Salmon, 13-May-2011.) $)
    exlimih $p |- ( E. x ph -> ps ) $=
      ( wi wex 19.23h mpgbi ) ABFACGBFCABCDHEI $.
  $}

  ${
    exlimi.1 $e |- F/ x ps $.
    exlimi.2 $e |- ( ph -> ps ) $.
    $( Inference from Theorem 19.23 of [Margaris] p. 90.  (Contributed by Mario
       Carneiro, 24-Sep-2016.) $)
    exlimi $p |- ( E. x ph -> ps ) $=
      ( nfri exlimih ) ABCBCDFEG $.
  $}

  ${
    exlimd2.1 $e |- ( ph -> A. x ph ) $.
    exlimd2.2 $e |- ( ph -> ( ch -> A. x ch ) ) $.
    exlimd2.3 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction from Theorem 19.23 of [Margaris] p. 90.  Similar to ~ exlimdh
       but with one slightly different hypothesis.  (Contributed by Jim
       Kingdon, 30-Dec-2017.) $)
    exlimd2 $p |- ( ph -> ( E. x ps -> ch ) ) $=
      ( wal wi wex alrimih 19.23ht biimpd sylc ) ACCDHIZDHZBCIZDHZBDJCIZAODEFKA
      QDEGKPRSBCDLMN $.
  $}

  ${
    exlimdh.1 $e |- ( ph -> A. x ph ) $.
    exlimdh.2 $e |- ( ch -> A. x ch ) $.
    exlimdh.3 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction from Theorem 19.23 of [Margaris] p. 90.  (Contributed by NM,
       28-Jan-1997.) $)
    exlimdh $p |- ( ph -> ( E. x ps -> ch ) ) $=
      ( wi wal wex alrimih 19.23h sylib ) ABCHZDIBDJCHANDEGKBCDFLM $.
  $}

  ${
    exlimd.1 $e |- F/ x ph $.
    exlimd.2 $e |- F/ x ch $.
    exlimd.3 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction from Theorem 19.9 of [Margaris] p. 89.  (Contributed by Mario
       Carneiro, 24-Sep-2016.)  (Proof rewritten by Jim Kingdon,
       18-Jun-2018.) $)
    exlimd $p |- ( ph -> ( E. x ps -> ch ) ) $=
      ( nfri exlimdh ) ABCDADEHCDFHGI $.
  $}

  ${
    $d x ps $.
    exlimiv.1 $e |- ( ph -> ps ) $.
    $( Inference from Theorem 19.23 of [Margaris] p. 90.

       This inference, along with our many variants is used to implement a
       metatheorem called "Rule C" that is given in many logic textbooks.  See,
       for example, Rule C in [Mendelson] p. 81, Rule C in [Margaris] p. 40, or
       Rule C in Hirst and Hirst's _A Primer for Logic and Proof_ p. 59 (PDF
       p. 65) at ~ http://www.mathsci.appstate.edu/~~jlh/primer/hirst.pdf .

       In informal proofs, the statement "Let C be an element such that..."
       almost always means an implicit application of Rule C.

       In essence, Rule C states that if we can prove that some element ` x `
       exists satisfying a wff, i.e. ` E. x ph ( x ) ` where ` ph ( x ) ` has
       ` x ` free, then we can use ` ph ( ` C ` ) ` as a hypothesis for the
       proof where C is a new (ficticious) constant not appearing previously in
       the proof, nor in any axioms used, nor in the theorem to be proved.  The
       purpose of Rule C is to get rid of the existential quantifier.

       We cannot do this in Metamath directly.  Instead, we use the original
       ` ph ` (containing ` x ` ) as an antecedent for the main part of the
       proof.  We eventually arrive at ` ( ph -> ps ) ` where ` ps ` is the
       theorem to be proved and does not contain ` x ` .  Then we apply
       ~ exlimiv to arrive at ` ( E. x ph -> ps ) ` .  Finally, we separately
       prove ` E. x ph ` and detach it with modus ponens ~ ax-mp to arrive at
       the final theorem ` ps ` .  (Contributed by NM, 5-Aug-1993.)  (Revised
       by NM, 25-Jul-2012.) $)
    exlimiv $p |- ( E. x ph -> ps ) $=
      ( ax-17 exlimih ) ABCBCEDF $.
  $}

  $( Theorem 19.22 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.)
     (Proof shortened by Wolf Lammen, 4-Jul-2014.) $)
  exim $p |- ( A. x ( ph -> ps ) -> ( E. x ph -> E. x ps ) ) $=
    ( wi wal wex hba1 hbe1 19.8a imim2i sps exlimdh ) ABDZCEABCFZCMCGBCHMANDCBN
    ABCIJKL $.

  ${
    eximi.1 $e |- ( ph -> ps ) $.
    $( Inference adding existential quantifier to antecedent and consequent.
       (Contributed by NM, 5-Aug-1993.) $)
    eximi $p |- ( E. x ph -> E. x ps ) $=
      ( wi wex exim mpg ) ABEACFBCFECABCGDH $.

    $( Inference adding 2 existential quantifiers to antecedent and consequent.
       (Contributed by NM, 3-Feb-2005.) $)
    2eximi $p |- ( E. x E. y ph -> E. x E. y ps ) $=
      ( wex eximi ) ADFBDFCABDEGG $.
  $}

  ${
    eximii.1 $e |- E. x ph $.
    eximii.2 $e |- ( ph -> ps ) $.
    $( Inference associated with ~ eximi .  (Contributed by BJ, 3-Feb-2018.) $)
    eximii $p |- E. x ps $=
      ( wex eximi ax-mp ) ACFBCFDABCEGH $.
  $}

  $( A transformation of quantifiers and logical connectives.  (Contributed by
     NM, 19-Aug-1993.) $)
  alinexa $p |- ( A. x ( ph -> -. ps ) <-> -. E. x ( ph /\ ps ) ) $=
    ( wn wi wal wa wex imnan albii alnex bitri ) ABDEZCFABGZDZCFNCHDMOCABIJNCKL
    $.

  $( Theorem 19.18 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)
  exbi $p |- ( A. x ( ph <-> ps ) -> ( E. x ph <-> E. x ps ) ) $=
    ( wb wal wex wi biimp alimi exim syl biimpr impbid ) ABDZCEZACFZBCFZOABGZCE
    PQGNRCABHIABCJKOBAGZCEQPGNSCABLIBACJKM $.

  ${
    exbii.1 $e |- ( ph <-> ps ) $.
    $( Inference adding existential quantifier to both sides of an equivalence.
       (Contributed by NM, 24-May-1994.) $)
    exbii $p |- ( E. x ph <-> E. x ps ) $=
      ( wb wex exbi mpg ) ABEACFBCFECABCGDH $.

    $( Inference adding 2 existential quantifiers to both sides of an
       equivalence.  (Contributed by NM, 16-Mar-1995.) $)
    2exbii $p |- ( E. x E. y ph <-> E. x E. y ps ) $=
      ( wex exbii ) ADFBDFCABDEGG $.

    $( Inference adding 3 existential quantifiers to both sides of an
       equivalence.  (Contributed by NM, 2-May-1995.) $)
    3exbii $p |- ( E. x E. y E. z ph <-> E. x E. y E. z ps ) $=
      ( wex exbii 2exbii ) AEGBEGCDABEFHI $.
  $}

  $( Commutation of conjunction inside an existential quantifier.  (Contributed
     by NM, 18-Aug-1993.) $)
  exancom $p |- ( E. x ( ph /\ ps ) <-> E. x ( ps /\ ph ) ) $=
    ( wa ancom exbii ) ABDBADCABEF $.

  ${
    alrimdd.1 $e |- F/ x ph $.
    alrimdd.2 $e |- ( ph -> F/ x ps ) $.
    alrimdd.3 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction from Theorem 19.21 of [Margaris] p. 90.  (Contributed by Mario
       Carneiro, 24-Sep-2016.) $)
    alrimdd $p |- ( ph -> ( ps -> A. x ch ) ) $=
      ( wal nfrd alimd syld ) ABBDHCDHABDFIABCDEGJK $.
  $}

  ${
    alrimd.1 $e |- F/ x ph $.
    alrimd.2 $e |- F/ x ps $.
    alrimd.3 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction from Theorem 19.21 of [Margaris] p. 90.  (Contributed by Mario
       Carneiro, 24-Sep-2016.) $)
    alrimd $p |- ( ph -> ( ps -> A. x ch ) ) $=
      ( wnf a1i alrimdd ) ABCDEBDHAFIGJ $.
  $}

  ${
    eximdh.1 $e |- ( ph -> A. x ph ) $.
    eximdh.2 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction from Theorem 19.22 of [Margaris] p. 90.  (Contributed by NM,
       20-May-1996.) $)
    eximdh $p |- ( ph -> ( E. x ps -> E. x ch ) ) $=
      ( wi wal wex alrimih exim syl ) ABCGZDHBDICDIGAMDEFJBCDKL $.
  $}

  ${
    eximd.1 $e |- F/ x ph $.
    eximd.2 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction from Theorem 19.22 of [Margaris] p. 90.  (Contributed by Mario
       Carneiro, 24-Sep-2016.) $)
    eximd $p |- ( ph -> ( E. x ps -> E. x ch ) ) $=
      ( nfri eximdh ) ABCDADEGFH $.
  $}

  ${
    nexd.1 $e |- ( ph -> A. x ph ) $.
    nexd.2 $e |- ( ph -> -. ps ) $.
    $( Deduction for generalization rule for negated wff.  (Contributed by NM,
       2-Jan-2002.) $)
    nexd $p |- ( ph -> -. E. x ps ) $=
      ( wn wal wex alrimih alnex sylib ) ABFZCGBCHFALCDEIBCJK $.
  $}

  ${
    exbidh.1 $e |- ( ph -> A. x ph ) $.
    exbidh.2 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for existential quantifier (deduction form).
       (Contributed by NM, 5-Aug-1993.) $)
    exbidh $p |- ( ph -> ( E. x ps <-> E. x ch ) ) $=
      ( wb wal wex alrimih exbi syl ) ABCGZDHBDICDIGAMDEFJBCDKL $.
  $}

  ${
    albid.1 $e |- F/ x ph $.
    albid.2 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for universal quantifier (deduction form).
       (Contributed by Mario Carneiro, 24-Sep-2016.) $)
    albid $p |- ( ph -> ( A. x ps <-> A. x ch ) ) $=
      ( nfri albidh ) ABCDADEGFH $.
  $}

  ${
    exbid.1 $e |- F/ x ph $.
    exbid.2 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for existential quantifier (deduction form).
       (Contributed by Mario Carneiro, 24-Sep-2016.) $)
    exbid $p |- ( ph -> ( E. x ps <-> E. x ch ) ) $=
      ( nfri exbidh ) ABCDADEGFH $.
  $}

  $( Simplification of an existentially quantified conjunction.  (Contributed
     by Rodolfo Medina, 25-Sep-2010.)  (Proof shortened by Andrew Salmon,
     29-Jun-2011.) $)
  exsimpl $p |- ( E. x ( ph /\ ps ) -> E. x ph ) $=
    ( wa simpl eximi ) ABDACABEF $.

  $( Simplification of an existentially quantified conjunction.  (Contributed
     by Rodolfo Medina, 25-Sep-2010.)  (Proof shortened by Andrew Salmon,
     29-Jun-2011.) $)
  exsimpr $p |- ( E. x ( ph /\ ps ) -> E. x ps ) $=
    ( wa simpr eximi ) ABDBCABEF $.

  $( Theorem 19.6 of [Margaris] p. 89, given a decidability condition.  The
     forward direction holds for all propositions, as seen at ~ alexim .
     (Contributed by Jim Kingdon, 2-Jun-2018.) $)
  alexdc $p |- ( A. x DECID ph -> ( A. x ph <-> -. E. x -. ph ) ) $=
    ( wdc wal wn wex nfa1 wb notnotbdc sps albid alnex bitrdi ) ACZBDZABDAEZEZB
    DPBFEOAQBNBGNAQHBAIJKPBLM $.

  $( Theorem 19.29 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.)
     (Proof shortened by Andrew Salmon, 13-May-2011.) $)
  19.29 $p |- ( ( A. x ph /\ E. x ps ) -> E. x ( ph /\ ps ) ) $=
    ( wal wex wa wi pm3.2 alimi exim syl imp ) ACDZBCEZABFZCEZMBOGZCDNPGAQCABHI
    BOCJKL $.

  $( Variation of Theorem 19.29 of [Margaris] p. 90.  (Contributed by NM,
     18-Aug-1993.) $)
  19.29r $p |- ( ( E. x ph /\ A. x ps ) -> E. x ( ph /\ ps ) ) $=
    ( wal wex wa 19.29 ancom exancom 3imtr4i ) BCDZACEZFBAFCELKFABFCEBACGLKHABC
    IJ $.

  $( Variation of Theorem 19.29 of [Margaris] p. 90 with double quantification.
     (Contributed by NM, 3-Feb-2005.) $)
  19.29r2 $p |- ( ( E. x E. y ph /\ A. x A. y ps ) ->
             E. x E. y ( ph /\ ps ) ) $=
    ( wex wal wa 19.29r eximi syl ) ADEZCEBDFZCFGKLGZCEABGDEZCEKLCHMNCABDHIJ $.

  $( Variation of Theorem 19.29 of [Margaris] p. 90 with mixed quantification.
     (Contributed by NM, 11-Feb-2005.) $)
  19.29x $p |- ( ( E. x A. y ph /\ A. x E. y ps ) ->
             E. x E. y ( ph /\ ps ) ) $=
    ( wal wex wa 19.29r 19.29 eximi syl ) ADEZCFBDFZCEGLMGZCFABGDFZCFLMCHNOCABD
    IJK $.

  $( Forward direction of Theorem 19.35 of [Margaris] p. 90.  The converse
     holds for classical logic but not (for all propositions) in intuitionistic
     logic.  (Contributed by Mario Carneiro, 2-Feb-2015.) $)
  19.35-1 $p |- ( E. x ( ph -> ps ) -> ( A. x ph -> E. x ps ) ) $=
    ( wal wi wex wa 19.29 pm3.35 eximi syl expcom ) ACDZABEZCFZBCFZMOGANGZCFPAN
    CHQBCABIJKL $.

  ${
    19.35i.1 $e |- E. x ( ph -> ps ) $.
    $( Inference from Theorem 19.35 of [Margaris] p. 90.  (Contributed by NM,
       5-Aug-1993.)  (Revised by NM, 2-Feb-2015.) $)
    19.35i $p |- ( A. x ph -> E. x ps ) $=
      ( wi wex wal 19.35-1 ax-mp ) ABECFACGBCFEDABCHI $.
  $}

  $( Theorem 19.25 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.)
     (Revised by NM, 2-Feb-2015.) $)
  19.25 $p |- ( A. y E. x ( ph -> ps ) ->
              ( E. y A. x ph -> E. y E. x ps ) ) $=
    ( wi wex wal 19.35-1 alimi exim syl ) ABECFZDGACGZBCFZEZDGMDFNDFELODABCHIMN
    DJK $.

  $( Theorem 19.30 of [Margaris] p. 90, with an additional decidability
     condition.  (Contributed by Jim Kingdon, 21-Jul-2018.) $)
  19.30dc $p |- ( DECID E. x ps ->
      ( A. x ( ph \/ ps ) -> ( A. x ph \/ E. x ps ) ) ) $=
    ( wex wdc wn wo wal df-dc olc a1d alnex orel2 al2imi sylbir syl6 jaoi sylbi
    wi orc ) BCDZEUAUAFZGABGZCHZACHZUAGZSZUAIUAUGUBUAUFUDUAUEJKUBUDUEUFUBBFZCHU
    DUESBCLUHUCACBAMNOUEUATPQR $.

  $( Theorem 19.43 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.)
     (Proof shortened by Mario Carneiro, 2-Feb-2015.) $)
  19.43 $p |- ( E. x ( ph \/ ps ) <-> ( E. x ph \/ E. x ps ) ) $=
    ( wo wex hbe1 hbor 19.8a orim12i exlimih orc eximi olc jaoi impbii ) ABDZCE
    ZACEZBCEZDZPTCRSCACFBCFGARBSACHBCHIJRQSAPCABKLBPCBAMLNO $.

  $( The antecedent provides a condition implying the converse of ~ 19.33 .
     Compare Theorem 19.33 of [Margaris] p. 90.  This variation of ~ 19.33bdc
     is intuitionistically valid without a decidability condition.
     (Contributed by Mario Carneiro, 2-Feb-2015.) $)
  19.33b2 $p |- ( ( -. E. x ph \/ -. E. x ps ) ->
               ( A. x ( ph \/ ps ) <-> ( A. x ph \/ A. x ps ) ) ) $=
    ( wex wn wo wal orcom alnex orbi12i bitr4i wi pm2.53 orcoms al2imi biimtrid
    orim12d com12 19.33 impbid1 ) ACDEZBCDEZFZABFZCGZACGZBCGZFZUEUCUHUCBEZCGZAE
    ZCGZFZUEUHUCUBUAFUMUAUBHUJUBULUABCIACIJKUEUJUFULUGUDUIACBAUIALBAMNOUDUKBCAB
    MOQPRABCST $.

  $( Converse of ~ 19.33 given ` -. ( E. x ph /\ E. x ps ) ` and a decidability
     condition.  Compare Theorem 19.33 of [Margaris] p. 90.  For a version
     which does not require a decidability condition, see ~ 19.33b2
     (Contributed by Jim Kingdon, 23-Apr-2018.) $)
  19.33bdc $p |- ( DECID E. x ph -> ( -. ( E. x ph /\ E. x ps ) ->
               ( A. x ( ph \/ ps ) <-> ( A. x ph \/ A. x ps ) ) ) ) $=
    ( wex wdc wa wn wo wal wb ianordc 19.33b2 biimtrdi ) ACDZENBCDZFGNGOGHABHCI
    ACIBCIHJNOKABCLM $.

  $( Theorem 19.40 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)
  19.40 $p |- ( E. x ( ph /\ ps ) -> ( E. x ph /\ E. x ps ) ) $=
    ( wa wex exsimpl simpr eximi jca ) ABDZCEACEBCEABCFJBCABGHI $.

  $( Theorem *11.42 in [WhiteheadRussell] p. 163.  Theorem 19.40 of [Margaris]
     p. 90 with 2 quantifiers.  (Contributed by Andrew Salmon, 24-May-2011.) $)
  19.40-2 $p |- ( E. x E. y ( ph /\ ps ) ->
        ( E. x E. y ph /\ E. x E. y ps ) ) $=
    ( wa wex 19.40 eximi syl ) ABEDFZCFADFZBDFZEZCFKCFLCFEJMCABDGHKLCGI $.

  $( Add/remove a conjunct in the scope of an existential quantifier.
     (Contributed by Raph Levien, 3-Jul-2006.) $)
  exintrbi $p |- ( A. x ( ph -> ps ) -> ( E. x ph <-> E. x ( ph /\ ps ) ) ) $=
    ( wi wal wa wb wex pm4.71 albii exbi sylbi ) ABDZCEAABFZGZCEACHNCHGMOCABIJA
    NCKL $.

  $( Introduce a conjunct in the scope of an existential quantifier.
     (Contributed by NM, 11-Aug-1993.) $)
  exintr $p |- ( A. x ( ph -> ps ) -> ( E. x ph -> E. x ( ph /\ ps ) ) ) $=
    ( wi wal wex wa exintrbi biimpd ) ABDCEACFABGCFABCHI $.

  $( Theorem *10.3 in [WhiteheadRussell] p. 150.  (Contributed by Andrew
     Salmon, 8-Jun-2011.) $)
  alsyl $p |- ( ( A. x ( ph -> ps ) /\ A. x ( ps -> ch ) ) ->
        A. x ( ph -> ch ) ) $=
    ( wi pm3.33 alanimi ) ABEBCEACEDABCFG $.

  ${
    hbex.1 $e |- ( ph -> A. x ph ) $.
    $( If ` x ` is not free in ` ph ` , it is not free in ` E. y ph ` .
       (Contributed by NM, 5-Aug-1993.)  (Revised by NM, 2-Feb-2015.) $)
    hbex $p |- ( E. y ph -> A. x E. y ph ) $=
      ( wex wal hbe1 hbal 19.8a alrimih exlimih ) AACEZBFCLCBACGHALBDACIJK $.
  $}

  ${
    nfex.1 $e |- F/ x ph $.
    $( If ` x ` is not free in ` ph ` , it is not free in ` E. y ph ` .
       (Contributed by Mario Carneiro, 11-Aug-2016.)  (Proof shortened by Wolf
       Lammen, 30-Dec-2017.) $)
    nfex $p |- F/ x E. y ph $=
      ( wex nfri hbex nfi ) ACEBABCABDFGH $.
  $}

  $( Theorem 19.2 of [Margaris] p. 89, generalized to use two setvar variables.
     (Contributed by O'Cat, 31-Mar-2008.) $)
  19.2 $p |- ( A. x ph -> E. y ph ) $=
    ( wex 19.8a sps ) AACDBACEF $.

  ${
    i19.24.1 $e |- ( ( A. x ph -> E. x ps ) -> E. x ( ph -> ps ) ) $.
    $( Theorem 19.24 of [Margaris] p. 90, with an additional hypothesis.  The
       hypothesis is the converse of ~ 19.35-1 , and is a theorem of classical
       logic, but in intuitionistic logic it will only be provable for some
       propositions.  (Contributed by Jim Kingdon, 22-Jul-2018.) $)
    i19.24 $p |- ( ( A. x ph -> A. x ps ) -> E. x ( ph -> ps ) ) $=
      ( wal wi wex 19.2 imim2i syl ) ACEZBCEZFKBCGZFABFCGLMKBCCHIDJ $.

    $( Theorem 19.39 of [Margaris] p. 90, with an additional hypothesis.  The
       hypothesis is the converse of ~ 19.35-1 , and is a theorem of classical
       logic, but in intuitionistic logic it will only be provable for some
       propositions.  (Contributed by Jim Kingdon, 22-Jul-2018.) $)
    i19.39 $p |- ( ( E. x ph -> E. x ps ) -> E. x ( ph -> ps ) ) $=
      ( wex wi wal 19.2 imim1i syl ) ACEZBCEZFACGZLFABFCEMKLACCHIDJ $.
  $}

  $( A closed version of one direction of ~ 19.9 .  (Contributed by NM,
     5-Aug-1993.) $)
  19.9ht $p |- ( A. x ( ph -> A. x ph ) -> ( E. x ph -> ph ) ) $=
    ( wal wi wex id ax-gen 19.23ht mpbii ) AABCDBCAADZBCABEADJBAFGAABHI $.

  $( A closed version of ~ 19.9 .  (Contributed by NM, 5-Aug-1993.)  (Revised
     by Mario Carneiro, 24-Sep-2016.)  (Proof shortended by Wolf Lammen,
     30-Dec-2017.) $)
  19.9t $p |- ( F/ x ph -> ( E. x ph <-> ph ) ) $=
    ( wnf wex wal wi df-nf 19.9ht sylbi 19.8a impbid1 ) ABCZABDZALAABEFBEMAFABG
    ABHIABJK $.

  ${
    19.9h.1 $e |- ( ph -> A. x ph ) $.
    $( A wff may be existentially quantified with a variable not free in it.
       Theorem 19.9 of [Margaris] p. 89.  (Contributed by FL, 24-Mar-2007.) $)
    19.9h $p |- ( E. x ph <-> ph ) $=
      ( wex wal wi 19.9ht mpg 19.8a impbii ) ABDZAAABEFKAFBABGCHABIJ $.
  $}

  ${
    19.9.1 $e |- F/ x ph $.
    $( A wff may be existentially quantified with a variable not free in it.
       Theorem 19.9 of [Margaris] p. 89.  (Contributed by FL, 24-Mar-2007.)
       (Revised by Mario Carneiro, 24-Sep-2016.)  (Proof shortened by Wolf
       Lammen, 30-Dec-2017.) $)
    19.9 $p |- ( E. x ph <-> ph ) $=
      ( nfri 19.9h ) ABABCDE $.
  $}

  $( One direction of Theorem 19.6 of [Margaris] p. 89.  The converse holds
     given a decidability condition, as seen at ~ alexdc .  (Contributed by Jim
     Kingdon, 2-Jul-2018.) $)
  alexim $p |- ( A. x ph -> -. E. x -. ph ) $=
    ( wal wn wex wfal wi pm2.24 alimi exim syl nfv 19.9 imbitrdi dfnot sylibr )
    ABCZADZBEZFGSDQSFBEZFQRFGZBCSTGAUABAFHIRFBJKFBFBLMNSOP $.

  $( One direction of Theorem 19.14 of [Margaris] p. 90.  The converse holds in
     classical but not in intuitionistic logic.  (Contributed by Jim Kingdon,
     15-Jul-2018.) $)
  exnalim $p |- ( E. x -. ph -> -. A. x ph ) $=
    ( wal wn wex alexim con2i ) ABCADBEABFG $.

  $( A transformation of quantifiers and logical connectives.  The converse
     holds in classical but not in intuitionistic logic.  (Contributed by Jim
     Kingdon, 15-Jul-2018.) $)
  exanaliim $p |- ( E. x ( ph /\ -. ps ) -> -. A. x ( ph -> ps ) ) $=
    ( wn wa wex wi wal annimim eximi exnalim syl ) ABDEZCFABGZDZCFNCHDMOCABIJNC
    KL $.

  $( A relationship between two quantifiers and negation.  (Contributed by Jim
     Kingdon, 27-Aug-2018.) $)
  alexnim $p |- ( A. x E. y -. ph -> -. E. x A. y ph ) $=
    ( wn wex wal exnalim alimi alnex sylib ) ADCEZBFACFZDZBFLBEDKMBACGHLBIJ $.

  $( The double negation of a universal quantification implies the universal
     quantification of the double negation.  The converse holds in classical
     but not in intuitionistic logic.  (Contributed by BJ, 24-Nov-2023.) $)
  nnal $p |- ( -. -. A. x ph -> A. x -. -. ph ) $=
    ( wal wn wex exnalim con3i alnex sylibr ) ABCDZDADZBEZDKDBCLJABFGKBHI $.

  ${
    hbn.1 $e |- ( ph -> A. x ph ) $.
    $( If ` x ` is not free in ` ph ` , then it is not free in ` -. ph ` .
       This theorem does not depend on ~ ax-ial , contrary to ~ hbn1 and
       ~ hbnt .  (Contributed by NM, 5-Aug-1993.)  Remove dependency on
       ~ ax-ial .  (Revised by GD, 27-Jan-2018.) $)
    hbn $p |- ( -. ph -> A. x -. ph ) $=
      ( wn wex wal id exlimih con3i alnex sylibr ) ADZABEZDLBFMAAABCAGHIABJK $.
    $( $j usage 'hbn' avoids 'ax-ial'; $)
  $}

  $( Quantified Negation.  Axiom C5-2 of [Monk2] p. 113.  The setvar ` x ` is
     not free in ` -. A. x ph ` .  (Contributed by NM, 5-Aug-1993.)  (Proof
     shortened by Wolf Lammen, 18-Aug-2014.)  (Proof shortened by GD,
     27-Jan-2018.) $)
  hbn1 $p |- ( -. A. x ph -> A. x -. A. x ph ) $=
    ( wal ax-ial hbn ) ABCBABDE $.

  $( Closed form of bound-variable hypothesis builder ~ hbn .  (Contributed by
     NM, 5-Aug-1993.)  (Revised by NM, 2-Feb-2015.) $)
  hbnt $p |- ( A. x ( ph -> A. x ph ) -> ( -. ph -> A. x -. ph ) ) $=
    ( wn wal wi ax-4 con3i hbn1 syl con3 al2imi syl5 ) ACZABDZCZBDZANEZBDMBDMOP
    NAABFGABHIQOMBANJKL $.

  ${
    hbnOLD.1 $e |- ( ph -> A. x ph ) $.
    $( Obsolete proof of ~ hbn as of 2-May-2026.  (Contributed by NM,
       5-Aug-1993.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    hbnOLD $p |- ( -. ph -> A. x -. ph ) $=
      ( wal wi wn hbnt mpg ) AABDEAFZIBDEBABGCH $.
  $}

  ${
    hbnd.1 $e |- ( ph -> A. x ph ) $.
    hbnd.2 $e |- ( ph -> ( ps -> A. x ps ) ) $.
    $( Deduction form of bound-variable hypothesis builder ~ hbn .
       (Contributed by NM, 3-Jan-2002.) $)
    hbnd $p |- ( ph -> ( -. ps -> A. x -. ps ) ) $=
      ( wal wi wn alrimih hbnt syl ) ABBCFGZCFBHZMCFGALCDEIBCJK $.
  $}

  $( If ` x ` is not free in ` ph ` , then it is not free in ` -. ph ` .
     (Contributed by Mario Carneiro, 24-Sep-2016.)  (Proof shortened by Wolf
     Lammen, 28-Dec-2017.)  (Revised by BJ, 24-Jul-2019.) $)
  nfnt $p |- ( F/ x ph -> F/ x -. ph ) $=
    ( wnf wn nfnf1 wal wi df-nf hbnt sylbi nfd ) ABCZADZBABELAABFGBFMMBFGABHABI
    JK $.

  ${
    nfnd.1 $e |- ( ph -> F/ x ps ) $.
    $( Deduction associated with ~ nfnt .  (Contributed by Mario Carneiro,
       24-Sep-2016.) $)
    nfnd $p |- ( ph -> F/ x -. ps ) $=
      ( wnf wn nfnt syl ) ABCEBFCEDBCGH $.
  $}

  ${
    nfn.1 $e |- F/ x ph $.
    $( Inference associated with ~ nfnt .  (Contributed by Mario Carneiro,
       11-Aug-2016.) $)
    nfn $p |- F/ x -. ph $=
      ( wnf wn nfnt ax-mp ) ABDAEBDCABFG $.
  $}

  ${
    nfdc.1 $e |- F/ x ph $.
    $( If ` x ` is not free in ` ph ` , it is not free in ` DECID ph ` .
       (Contributed by Jim Kingdon, 11-Mar-2018.) $)
    nfdc $p |- F/ x DECID ph $=
      ( wdc wn wo df-dc nfn nfor nfxfr ) ADAAEZFBAGAKBCABCHIJ $.
  $}

  $( The analog in our predicate calculus of axiom 5 of modal logic S5.
     (Contributed by NM, 5-Oct-2005.) $)
  modal-5 $p |- ( -. A. x -. ph -> A. x -. A. x -. ph ) $=
    ( wn hbn1 ) ACBD $.

  ${
    19.9d.1 $e |- ( ps -> F/ x ph ) $.
    $( A deduction version of one direction of ~ 19.9 .  (Contributed by NM,
       5-Aug-1993.)  (Revised by Mario Carneiro, 24-Sep-2016.) $)
    19.9d $p |- ( ps -> ( E. x ph -> ph ) ) $=
      ( wex wnf wb 19.9t syl biimpd ) BACEZABACFKAGDACHIJ $.
  $}

  ${
    19.9hd.1 $e |- ( ps -> A. x ps ) $.
    19.9hd.2 $e |- ( ps -> ( ph -> A. x ph ) ) $.
    $( A deduction version of one direction of ~ 19.9 .  This is an older
       variation of this theorem; new proofs should use ~ 19.9d .  (Contributed
       by NM, 5-Aug-1993.)  (New usage is discouraged.) $)
    19.9hd $p |- ( ps -> ( E. x ph -> ph ) ) $=
      ( wal wi wex alimi 19.9ht 3syl ) BBCFAACFGZCFACHAGDBLCEIACJK $.
  $}

  $( One direction of Theorem 19.11 of [Margaris] p. 89.  (Contributed by NM,
     5-Aug-1993.) $)
  excomim $p |- ( E. x E. y ph -> E. y E. x ph ) $=
    ( wex 19.8a 2eximi hbe1 hbex 19.9h sylib ) ACDBDABDZCDZBDLAKBCABEFLBKBCABGH
    IJ $.

  $( Theorem 19.11 of [Margaris] p. 89.  (Contributed by NM, 5-Aug-1993.) $)
  excom $p |- ( E. x E. y ph <-> E. y E. x ph ) $=
    ( wex excomim impbii ) ACDBDABDCDABCEACBEF $.

  $( Theorem 19.12 of [Margaris] p. 89.  Assuming the converse is a mistake
     sometimes made by beginners!  (Contributed by NM, 5-Aug-1993.) $)
  19.12 $p |- ( E. x A. y ph -> A. y E. x ph ) $=
    ( wal wex hba1 hbex ax-4 eximi alrimih ) ACDZBEABECKCBACFGKABACHIJ $.

  ${
    19.19.1 $e |- F/ x ph $.
    $( Theorem 19.19 of [Margaris] p. 90.  (Contributed by NM, 12-Mar-1993.) $)
    19.19 $p |- ( A. x ( ph <-> ps ) -> ( ph <-> E. x ps ) ) $=
      ( wex wb wal 19.9 exbi bitr3id ) AACEABFCGBCEACDHABCIJ $.
  $}

  ${
    19.21-2.1 $e |- F/ x ph $.
    19.21-2.2 $e |- F/ y ph $.
    $( Theorem 19.21 of [Margaris] p. 90 but with 2 quantifiers.  (Contributed
       by NM, 4-Feb-2005.) $)
    19.21-2 $p |- ( A. x A. y ( ph -> ps ) <-> ( ph -> A. x A. y ps ) ) $=
      ( wi wal 19.21 albii bitri ) ABGDHZCHABDHZGZCHAMCHGLNCABDFIJAMCEIK $.
  $}

  $( An alternate definition of ~ df-nf , which does not involve nested
     quantifiers on the same variable.  (Contributed by Mario Carneiro,
     24-Sep-2016.) $)
  nf2 $p |- ( F/ x ph <-> ( E. x ph -> A. x ph ) ) $=
    ( wnf wal wi wex df-nf nfa1 nfri 19.23h bitri ) ABCAABDZEBDABFLEABGALBLBABH
    IJK $.

  $( An alternate definition of ~ df-nf .  (Contributed by Mario Carneiro,
     24-Sep-2016.) $)
  nf3 $p |- ( F/ x ph <-> A. x ( E. x ph -> ph ) ) $=
    ( wnf wex wal wi nf2 nfe1 nfri 19.21h bitr4i ) ABCABDZABEFLAFBEABGLABLBABHI
    JK $.

  $( Variable ` x ` is effectively not free in ` ph ` iff ` ph ` is always true
     or always false, given a decidability condition.  The reverse direction,
     ~ nf4r , holds for all propositions.  (Contributed by Jim Kingdon,
     21-Jul-2018.) $)
  nf4dc $p |- ( DECID E. x ph -> ( F/ x ph <-> ( A. x ph \/ A. x -. ph ) ) ) $=
    ( wex wdc wnf wn wal wo nf2 imordc bitrid orcom alnex orbi2i bitr4i bitrdi
    wi ) ABCZDZABEZRFZABGZHZUBAFBGZHZTRUBQSUCABIRUBJKUCUBUAHUEUAUBLUDUAUBABMNOP
    $.

  $( If ` ph ` is always true or always false, then variable ` x ` is
     effectively not free in ` ph ` .  The converse holds given a decidability
     condition, as seen at ~ nf4dc .  (Contributed by Jim Kingdon,
     21-Jul-2018.) $)
  nf4r $p |- ( ( A. x ph \/ A. x -. ph ) -> F/ x ph ) $=
    ( wal wn wo wex wnf orcom alnex orbi2i bitr4i wi imorr nf2 sylibr sylbir )
    ABCZADBCZEZABFZDZQEZABGZUBQUAESUAQHRUAQABIJKUBTQLUCTQMABNOP $.

  ${
    19.36i.1 $e |- F/ x ps $.
    19.36i.2 $e |- E. x ( ph -> ps ) $.
    $( Inference from Theorem 19.36 of [Margaris] p. 90.  (Contributed by NM,
       5-Aug-1993.)  (Revised by NM, 2-Feb-2015.) $)
    19.36i $p |- ( A. x ph -> ps ) $=
      ( wal wex 19.35i id exlimi syl ) ACFBCGBABCEHBBCDBIJK $.
  $}

  ${
    19.36-1.1 $e |- F/ x ps $.
    $( Closed form of ~ 19.36i .  One direction of Theorem 19.36 of [Margaris]
       p. 90.  The converse holds in classical logic, but does not hold (for
       all propositions) in intuitionistic logic.  (Contributed by Jim Kingdon,
       20-Jun-2018.) $)
    19.36-1 $p |- ( E. x ( ph -> ps ) -> ( A. x ph -> ps ) ) $=
      ( wi wex wal 19.35-1 19.9 imbitrdi ) ABECFACGBCFBABCHBCDIJ $.
  $}

  ${
    19.37-1.1 $e |- F/ x ph $.
    $( One direction of Theorem 19.37 of [Margaris] p. 90.  The converse holds
       in classical logic but not, in general, here.  (Contributed by Jim
       Kingdon, 21-Jun-2018.) $)
    19.37-1 $p |- ( E. x ( ph -> ps ) -> ( ph -> E. x ps ) ) $=
      ( wal wi wex 19.3 19.35-1 biimtrrid ) AACEABFCGBCGACDHABCIJ $.
  $}

  ${
    $d x ph $.
    19.37aiv.1 $e |- E. x ( ph -> ps ) $.
    $( Inference from Theorem 19.37 of [Margaris] p. 90.  (Contributed by NM,
       5-Aug-1993.) $)
    19.37aiv $p |- ( ph -> E. x ps ) $=
      ( wi wex nfv 19.37-1 ax-mp ) ABECFABCFEDABCACGHI $.
  $}

  $( Theorem 19.38 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)
  19.38 $p |- ( ( E. x ph -> A. x ps ) -> A. x ( ph -> ps ) ) $=
    ( wex wal wi hbe1 hba1 hbim 19.8a ax-4 imim12i alrimih ) ACDZBCEZFABFCNOCAC
    GBCHIANOBACJBCKLM $.

  $( Closed form of Theorem 19.23 of [Margaris] p. 90.  (Contributed by NM,
     7-Nov-2005.)  (Proof shortened by Wolf Lammen, 2-Jan-2018.) $)
  19.23t $p |- ( F/ x ps -> ( A. x ( ph -> ps ) <-> ( E. x ph -> ps ) ) ) $=
    ( wnf wi wal wex exim 19.9t biimpd syl9r nfr imim2d 19.38 syl6 impbid ) BCD
    ZABECFZACGZBEZRSBCGZQBABCHQUABBCIJKQTSBCFZERQBUBSBCLMABCNOP $.

  ${
    19.23.1 $e |- F/ x ps $.
    $( Theorem 19.23 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.)
       (Revised by Mario Carneiro, 24-Sep-2016.) $)
    19.23 $p |- ( A. x ( ph -> ps ) <-> ( E. x ph -> ps ) ) $=
      ( wnf wi wal wex wb 19.23t ax-mp ) BCEABFCGACHBFIDABCJK $.
  $}

  ${
    19.32dc.1 $e |- F/ x ph $.
    $( Theorem 19.32 of [Margaris] p. 90, where ` ph ` is decidable.
       (Contributed by Jim Kingdon, 4-Jun-2018.) $)
    19.32dc $p |- ( DECID ph ->
        ( A. x ( ph \/ ps ) <-> ( ph \/ A. x ps ) ) ) $=
      ( wdc wn wi wal wo wb nfn 19.21 a1i nfdc dfordc albid 3bitr4d ) AEZAFZBGZ
      CHZSBCHZGZABIZCHAUBIUAUCJRSBCACDKLMRUDTCACDNABOPAUBOQ $.
  $}

  ${
    19.32r.1 $e |- F/ x ph $.
    $( One direction of Theorem 19.32 of [Margaris] p. 90.  The converse holds
       if ` ph ` is decidable, as seen at ~ 19.32dc .  (Contributed by Jim
       Kingdon, 28-Jul-2018.) $)
    19.32r $p |- ( ( ph \/ A. x ps ) -> A. x ( ph \/ ps ) ) $=
      ( wo wal orc alrimi olc alimi jaoi ) AABEZCFBCFALCDABGHBLCBAIJK $.
  $}

  ${
    19.31r.1 $e |- F/ x ps $.
    $( One direction of Theorem 19.31 of [Margaris] p. 90.  The converse holds
       in classical logic, but not intuitionistic logic.  (Contributed by Jim
       Kingdon, 28-Jul-2018.) $)
    19.31r $p |- ( ( A. x ph \/ ps ) -> A. x ( ph \/ ps ) ) $=
      ( wal wo 19.32r orcom albii 3imtr4i ) BACEZFBAFZCEKBFABFZCEBACDGKBHMLCABH
      IJ $.
  $}

  ${
    19.44.1 $e |- F/ x ps $.
    $( Theorem 19.44 of [Margaris] p. 90.  (Contributed by NM, 12-Mar-1993.) $)
    19.44 $p |- ( E. x ( ph \/ ps ) <-> ( E. x ph \/ ps ) ) $=
      ( wo wex 19.43 19.9 orbi2i bitri ) ABECFACFZBCFZEKBEABCGLBKBCDHIJ $.
  $}

  ${
    19.45.1 $e |- F/ x ph $.
    $( Theorem 19.45 of [Margaris] p. 90.  (Contributed by NM, 12-Mar-1993.) $)
    19.45 $p |- ( E. x ( ph \/ ps ) <-> ( ph \/ E. x ps ) ) $=
      ( wo wex 19.43 19.9 orbi1i bitri ) ABECFACFZBCFZEALEABCGKALACDHIJ $.
  $}

  $( Theorem 19.34 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)
  19.34 $p |- ( ( A. x ph \/ E. x ps ) -> E. x ( ph \/ ps ) ) $=
    ( wal wex wo 19.2 orim1i 19.43 sylibr ) ACDZBCEZFACEZLFABFCEKMLACCGHABCIJ
    $.

  ${
    19.41h.1 $e |- ( ps -> A. x ps ) $.
    $( Theorem 19.41 of [Margaris] p. 90.  New proofs should use ~ 19.41
       instead.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Andrew
       Salmon, 25-May-2011.)  (New usage is discouraged.) $)
    19.41h $p |- ( E. x ( ph /\ ps ) <-> ( E. x ph /\ ps ) ) $=
      ( wa wex 19.40 id exlimih anim2i syl pm3.21 eximdh impcom impbii ) ABEZCF
      ZACFZBEZQRBCFZESABCGTBRBBCDBHIJKBRQBAPCDBALMNO $.
  $}

  ${
    19.41.1 $e |- F/ x ps $.
    $( Theorem 19.41 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.)
       (Proof shortened by Andrew Salmon, 25-May-2011.)  (Proof shortened by
       Wolf Lammen, 12-Jan-2018.) $)
    19.41 $p |- ( E. x ( ph /\ ps ) <-> ( E. x ph /\ ps ) ) $=
      ( wa wex 19.40 19.9 anbi2i sylib pm3.21 eximd impcom impbii ) ABEZCFZACFZ
      BEZPQBCFZERABCGSBQBCDHIJBQPBAOCDBAKLMN $.
  $}

  ${
    19.42h.1 $e |- ( ph -> A. x ph ) $.
    $( Theorem 19.42 of [Margaris] p. 90.  New proofs should use ~ 19.42
       instead.  (Contributed by NM, 18-Aug-1993.)
       (New usage is discouraged.) $)
    19.42h $p |- ( E. x ( ph /\ ps ) <-> ( ph /\ E. x ps ) ) $=
      ( wa wex 19.41h exancom ancom 3bitr4i ) BAECFBCFZAEABECFAKEBACDGABCHAKIJ
      $.
  $}

  ${
    19.42.1 $e |- F/ x ph $.
    $( Theorem 19.42 of [Margaris] p. 90.  (Contributed by NM, 18-Aug-1993.) $)
    19.42 $p |- ( E. x ( ph /\ ps ) <-> ( ph /\ E. x ps ) ) $=
      ( wa wex 19.41 exancom ancom 3bitr4i ) BAECFBCFZAEABECFAKEBACDGABCHAKIJ
      $.
  $}

  $( Swap 1st and 3rd existential quantifiers.  (Contributed by NM,
     9-Mar-1995.) $)
  excom13 $p |- ( E. x E. y E. z ph <-> E. z E. y E. x ph ) $=
    ( wex excom exbii 3bitri ) ADEZCEBEIBEZCEABEZDEZCEKCEDEIBCFJLCABDFGKCDFH $.

  $( Rotate existential quantifiers.  (Contributed by NM, 17-Mar-1995.) $)
  exrot3 $p |- ( E. x E. y E. z ph <-> E. y E. z E. x ph ) $=
    ( wex excom13 excom bitri ) ADECEBEABEZCEDEIDECEABCDFIDCGH $.

  $( Rotate existential quantifiers twice.  (Contributed by NM, 9-Mar-1995.) $)
  exrot4 $p |- ( E. x E. y E. z E. w ph <-> E. z E. w E. x E. y ph ) $=
    ( wex excom13 exbii bitri ) AEFDFCFZBFACFZDFEFZBFKBFEFDFJLBACDEGHKBEDGI $.

  ${
    nexr.1 $e |- -. E. x ph $.
    $( Inference from ~ 19.8a .  (Contributed by Jeff Hankins, 26-Jul-2009.) $)
    nexr $p |- -. ph $=
      ( wex 19.8a mto ) AABDCABEF $.
  $}

  ${
    exan.1 $e |- ( E. x ph /\ ps ) $.
    $( Place a conjunct in the scope of an existential quantifier.
       (Contributed by NM, 18-Aug-1993.)  (Proof shortened by Andrew Salmon,
       25-May-2011.) $)
    exan $p |- E. x ( ph /\ ps ) $=
      ( wex wal wa hbe1 19.28h mpgbi 19.29r ax-mp ) ACEZBCFGZABGCEMBGNCMBCACHID
      JABCKL $.
  $}

  ${
    hbexd.1 $e |- ( ph -> A. y ph ) $.
    hbexd.2 $e |- ( ph -> ( ps -> A. x ps ) ) $.
    $( Deduction form of bound-variable hypothesis builder ~ hbex .
       (Contributed by NM, 2-Jan-2002.) $)
    hbexd $p |- ( ph -> ( E. y ps -> A. x E. y ps ) ) $=
      ( wex wal eximdh 19.12 syl6 ) ABDGZBCHZDGLCHABMDEFIBDCJK $.
  $}

  ${
    eeor.1 $e |- F/ y ph $.
    eeor.2 $e |- F/ x ps $.
    $( Rearrange existential quantifiers.  (Contributed by NM, 8-Aug-1994.) $)
    eeor $p |- ( E. x E. y ( ph \/ ps ) <-> ( E. x ph \/ E. y ps ) ) $=
      ( wo wex 19.45 exbii nfex 19.44 bitri ) ABGDHZCHABDHZGZCHACHOGNPCABDEIJAO
      CBCDFKLM $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Equality theorems without distinct variables
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( At least one individual exists.  This is not a theorem of free logic,
     which is sound in empty domains.  For such a logic, we would add this
     theorem as an axiom of set theory (Axiom 0 of [Kunen] p. 10).  In the
     system consisting of ~ ax-5 through ~ ax-14 and ~ ax-17 , all axioms other
     than ~ ax-9 are believed to be theorems of free logic, although the system
     without ~ ax-9 is probably not complete in free logic.  (Contributed by
     NM, 5-Aug-1993.)  (Revised by NM, 3-Feb-2015.) $)
  a9e $p |- E. x x = y $=
    ( ax-i9 ) ABC $.

  ${
    $d x y $.
    $( At least one individual exists.  Weaker version of ~ a9e .  (Contributed
       by NM, 3-Aug-2017.) $)
    a9ev $p |- E. x x = y $=
      ( ax-i9 ) ABC $.
  $}

  $( An implication related to substitution.  (Contributed by NM, 5-Aug-1993.)
     (Revised by NM, 3-Feb-2015.) $)
  ax9o $p |- ( A. x ( x = y -> A. x ph ) -> ph ) $=
    ( cv wceq wex wal wi a9e wa 19.29r hba1 pm3.35 exlimih ax-4 syl mpan ) BDCD
    EZBFZRABGZHZBGZABCISUBJRUAJZBFZARUABKUDTAUCTBABLRTMNABOPPQ $.

  ${
    $d x y $.
    spimfv.nf $e |- F/ x ps $.
    spimfv.1 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( Specialization, using implicit substitution.  Version of ~ spim with a
       disjoint variable condition.  See ~ spimv for another variant.
       (Contributed by NM, 10-Jan-1993.)  (Revised by BJ, 31-May-2019.) $)
    spimfv $p |- ( A. x ph -> ps ) $=
      ( weq wi a9ev eximii 19.36i ) ABCECDGABHCCDIFJK $.
  $}

  ${
    $d x y $.
    chvarfv.nf $e |- F/ x ps $.
    chvarfv.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    chvarfv.2 $e |- ph $.
    $( Implicit substitution of ` y ` for ` x ` into a theorem.  Version of
       ~ chvar with a disjoint variable condition.  (Contributed by Raph
       Levien, 9-Jul-2003.)  (Revised by BJ, 31-May-2019.) $)
    chvarfv $p |- ps $=
      ( weq biimpd spimfv mpg ) ABCABCDECDHABFIJGK $.
  $}

  ${
    $d x y $.
    $( Identity law for equality (reflexivity).  Lemma 6 of [Tarski] p. 68.
       This is often an axiom of equality in textbook systems, but we don't
       need it as an axiom since it can be proved from our other axioms.

       This proof is similar to Tarski's and makes use of a dummy variable
       ` y ` .  It also works in intuitionistic logic, unlike some other
       possible ways of proving this theorem.  (Contributed by NM,
       1-Apr-2005.) $)
    equid $p |- x = x $=
      ( vy weq wex a9e ax-17 ax-8 pm2.43i exlimih ax-mp ) BACZBDAACZBAEKLBLBFKL
      BAAGHIJ $.
  $}

  $( Bound-variable hypothesis builder for ` x = x ` .  This theorem tells us
     that any variable, including ` x ` , is effectively not free in
     ` x = x ` , even though ` x ` is technically free according to the
     traditional definition of free variable.  (Contributed by NM,
     13-Jan-2011.)  (Revised by NM, 21-Aug-2017.) $)
  nfequid $p |- F/ y x = x $=
    ( weq equid nfth ) AACBADE $.

  $( One of the two equality axioms of standard predicate calculus, called
     reflexivity of equality.  (The other one is ~ stdpc7 .)  Axiom 6 of
     [Mendelson] p. 95.  Mendelson doesn't say why he prepended the redundant
     quantifier, but it was probably to be compatible with free logic (which is
     valid in the empty domain).  (Contributed by NM, 16-Feb-2005.) $)
  stdpc6 $p |- A. x x = x $=
    ( weq equid ax-gen ) AABAACD $.

  $( Commutative law for equality.  Lemma 7 of [Tarski] p. 69.  (Contributed by
     NM, 5-Aug-1993.) $)
  equcomi $p |- ( x = y -> y = x ) $=
    ( weq equid ax-8 mpi ) ABCAACBACADABAEF $.

  ${
    $d x y $.
    $( A commuted form of ~ a9ev .  The naming reflects how axioms were
       numbered in the Metamath Proof Explorer as of 2020 (a numbering which we
       eventually plan to adopt here too, but until this happens everywhere
       only some theorems will have it).  (Contributed by BJ, 7-Dec-2020.) $)
    ax6evr $p |- E. x y = x $=
      ( weq a9ev equcomi eximii ) ABCBACAABDABEF $.
  $}

  $( Commutative law for equality.  (Contributed by NM, 20-Aug-1993.) $)
  equcom $p |- ( x = y <-> y = x ) $=
    ( weq equcomi impbii ) ABCBACABDBADE $.

  ${
    equcomd.1 $e |- ( ph -> x = y ) $.
    $( Deduction form of ~ equcom , symmetry of equality.  For the versions for
       classes, see ~ eqcom and ~ eqcomd .  (Contributed by BJ, 6-Oct-2019.) $)
    equcomd $p |- ( ph -> y = x ) $=
      ( weq equcom sylib ) ABCECBEDBCFG $.
  $}

  ${
    equcoms.1 $e |- ( x = y -> ph ) $.
    $( An inference commuting equality in antecedent.  Used to eliminate the
       need for a syllogism.  (Contributed by NM, 5-Aug-1993.) $)
    equcoms $p |- ( y = x -> ph ) $=
      ( weq equcomi syl ) CBEBCEACBFDG $.
  $}

  $( A transitive law for equality.  (Contributed by NM, 23-Aug-1993.) $)
  equtr $p |- ( x = y -> ( y = z -> x = z ) ) $=
    ( weq wi ax-8 equcoms ) BCDACDEBABACFG $.

  $( A transitive law for equality.  Lemma L17 in [Megill] p. 446 (p. 14 of the
     preprint).  (Contributed by NM, 23-Aug-1993.) $)
  equtrr $p |- ( x = y -> ( z = x -> z = y ) ) $=
    ( weq equtr com12 ) CADABDCBDCABEF $.

  $( A transitive law for equality.  (Contributed by NM, 12-Aug-1993.)  (Proof
     shortened by Andrew Salmon, 25-May-2011.) $)
  equtr2 $p |- ( ( x = z /\ y = z ) -> x = y ) $=
    ( weq wi equtrr equcoms impcom ) BCDACDZABDZIJECBCBAFGH $.

  $( An equivalence law for equality.  (Contributed by NM, 5-Aug-1993.) $)
  equequ1 $p |- ( x = y -> ( x = z <-> y = z ) ) $=
    ( weq ax-8 equtr impbid ) ABDACDBCDABCEABCFG $.

  $( An equivalence law for equality.  (Contributed by NM, 5-Aug-1993.) $)
  equequ2 $p |- ( x = y -> ( z = x <-> z = y ) ) $=
    ( weq equtrr wi equcoms impbid ) ABDCADZCBDZABCEJIFBABACEGH $.

  ${
    ax11i.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    ax11i.2 $e |- ( ps -> A. x ps ) $.
    $( Inference that has ~ ax-11 (without ` A. y ` ) as its conclusion and
       does not require ~ ax-10 , ~ ax-11 , or ~ ax12 for its proof.  The
       hypotheses may be eliminable without one or more of these axioms in
       special cases.  Proof similar to Lemma 16 of [Tarski] p. 70.
       (Contributed by NM, 20-May-2008.) $)
    ax11i $p |- ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) $=
      ( weq wi wal biimprcd alrimih biimtrdi ) CDGZABMAHZCIEBNCFMABEJKL $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Axioms ax-10 and ax-11
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Show that ~ ax-10o can be derived from ~ ax-10 .  An open problem is
     whether this theorem can be derived from ~ ax-10 and the others when
     ~ ax-11 is replaced with ~ ax-11o .  See Theorem ~ ax10 for the
     rederivation of ~ ax-10 from ~ ax10o .

     Normally, ~ ax10o should be used rather than ~ ax-10o , except by theorems
     specifically studying the latter's properties.  (Contributed by NM,
     16-May-2008.) $)
  ax10o $p |- ( A. x x = y -> ( A. x ph -> A. y ph ) ) $=
    ( weq wal wi ax-10 ax-11 equcoms sps pm2.27 al2imi sylsyld ) BCDZBECBDZCEAB
    EZOAFZCEZACEBCGNPRFZBSCBACBHIJOQACOAKLM $.

  $( Axiom ~ ax-10o ("o" for "old") was the original version of ~ ax-10 ,
     before it was discovered (in May 2008) that the shorter ~ ax-10 could
     replace it.  It appears as Axiom scheme C11' in [Megill] p. 448 (p. 16 of
     the preprint).

     This axiom is redundant, as shown by Theorem ~ ax10o .

     Normally, ~ ax10o should be used rather than ~ ax-10o , except by theorems
     specifically studying the latter's properties.  (Contributed by NM,
     5-Aug-1993.)  (New usage is discouraged.) $)
  ax-10o $a |- ( A. x x = y -> ( A. x ph -> A. y ph ) ) $.

  $( Rederivation of ~ ax-10 from original version ~ ax-10o .  See Theorem
     ~ ax10o for the derivation of ~ ax-10o from ~ ax-10 .

     This theorem should not be referenced in any proof.  Instead, use ~ ax-10
     above so that uses of ~ ax-10 can be more easily identified.  (Contributed
     by NM, 16-May-2008.)  (New usage is discouraged.) $)
  ax10 $p |- ( A. x x = y -> A. y y = x ) $=
    ( weq wal ax-10o pm2.43i equcomi alimi syl ) ABCZADZJBDZBACZBDKLJABEFJMBABG
    HI $.

  $( All variables are effectively bound in an identical variable specifier.
     (Contributed by NM, 5-Aug-1993.)  (Revised by NM, 3-Feb-2015.) $)
  hbae $p |- ( A. x x = y -> A. z A. x x = y ) $=
    ( cv wceq wal wi ax12or ax10o alequcoms pm2.43i syl5 ax-4 imim1i jaoi ax-mp
    wo sps a5i ax-7 syl ) ADZBDZEZAFZUDCFZAFUECFUDUFACDZUBECFZUGUCECFZUDUFGZCFZ
    QZQUEUFGZABCHUHUMULUMACUDACIJUIUMUKUMBCUEUDBFZUCUGEBFUFUEUNUDABIKUDBCILJUJU
    MCUEUDUFUDAMNROOPSUDACTUA $.

  $( All variables are effectively bound in an identical variable specifier.
     (Contributed by Mario Carneiro, 11-Aug-2016.) $)
  nfae $p |- F/ z A. x x = y $=
    ( weq wal hbae nfi ) ABDAECABCFG $.

  ${
    hbalequs.1 $e |- ( A. z A. x x = y -> ph ) $.
    $( Rule that applies ~ hbae to antecedent.  (Contributed by NM,
       5-Aug-1993.) $)
    hbaes $p |- ( A. x x = y -> ph ) $=
      ( weq wal hbae syl ) BCFBGZJDGABCDHEI $.
  $}

  $( All variables are effectively bound in a distinct variable specifier.
     Lemma L19 in [Megill] p. 446 (p. 14 of the preprint).  (Contributed by NM,
     5-Aug-1993.) $)
  hbnae $p |- ( -. A. x x = y -> A. z -. A. x x = y ) $=
    ( weq wal hbae hbn ) ABDAECABCFG $.

  $( All variables are effectively bound in a distinct variable specifier.
     (Contributed by Mario Carneiro, 11-Aug-2016.) $)
  nfnae $p |- F/ z -. A. x x = y $=
    ( weq wal nfae nfn ) ABDAECABCFG $.

  ${
    hbnalequs.1 $e |- ( A. z -. A. x x = y -> ph ) $.
    $( Rule that applies ~ hbnae to antecedent.  (Contributed by NM,
       5-Aug-1993.) $)
    hbnaes $p |- ( -. A. x x = y -> ph ) $=
      ( weq wal wn hbnae syl ) BCFBGHZKDGABCDIEJ $.
  $}

  ${
    naecoms.1 $e |- ( -. A. x x = y -> ph ) $.
    $( A commutation rule for distinct variable specifiers.  (Contributed by
       NM, 2-Jan-2002.) $)
    naecoms $p |- ( -. A. y y = x -> ph ) $=
      ( cv wceq wal wn ax-10 con3i syl ) CEZBEZFCGZHMLFBGZHAONBCIJDK $.
  $}

  $( Lemma used in proofs of substitution properties.  (Contributed by NM,
     5-Aug-1993.)  (Proof shortened by Mario Carneiro, 20-May-2014.) $)
  equs4 $p |- ( A. x ( x = y -> ph ) -> E. x ( x = y /\ ph ) ) $=
    ( cv wceq wi wal wa wex a9e 19.29 mpan2 ancl imp eximi syl ) BDCDEZAFZBGZRQ
    HZBIZQAHZBISQBIUABCJRQBKLTUBBRQUBQAMNOP $.

  ${
    equsalh.1 $e |- ( ps -> A. x ps ) $.
    equsalh.2 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( A useful equivalence related to substitution.  New proofs should use
       ~ equsal instead.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by
       Andrew Salmon, 12-Aug-2011.)  (New usage is discouraged.) $)
    equsalh $p |- ( A. x ( x = y -> ph ) <-> ps ) $=
      ( weq wi wal 19.3h bitr4di pm5.74i albii a1d alrimih ax9o impbii bitr4i )
      CDGZAHZCISBCIZHZCIZBTUBCSAUASABUAFBCEJKLMBUCBUBCEBUASENOBCDPQR $.
  $}

  ${
    equsal.1 $e |- F/ x ps $.
    equsal.2 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( A useful equivalence related to substitution.  (Contributed by NM,
       5-Aug-1993.)  (Proof shortened by Andrew Salmon, 12-Aug-2011.)  (Revised
       by Mario Carneiro, 3-Oct-2016.)  (Proof shortened by Wolf Lammen,
       5-Feb-2018.) $)
    equsal $p |- ( A. x ( x = y -> ph ) <-> ps ) $=
      ( weq wi wal wex 19.23 pm5.74i albii a9e a1bi 3bitr4i ) CDGZBHZCIQCJZBHQA
      HZCIBQBCEKTRCQABFLMSBCDNOP $.
  $}

  ${
    equsex.1 $e |- ( ps -> A. x ps ) $.
    equsex.2 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( A useful equivalence related to substitution.  (Contributed by NM,
       5-Aug-1993.)  (Revised by NM, 3-Feb-2015.) $)
    equsex $p |- ( E. x ( x = y /\ ph ) <-> ps ) $=
      ( cv wceq wa wex biimpa exlimih a9e idd biimprcd jcad eximdh mpi impbii )
      CGDGHZAIZCJZBUABCETABFKLBTCJUBCDMBTUACEBTTABTNTABFOPQRS $.
  $}

  ${
    $d x y $.  $d x ps $.
    equsalvw.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Version of ~ equsex with two disjoint variable conditions.  (Contributed
       by BJ, 31-May-2019.)  (Proof shortened by Wolf Lammen, 23-Oct-2023.) $)
    equsexvw $p |- ( E. x ( x = y /\ ph ) <-> ps ) $=
      ( ax-17 equsex ) ABCDBCFEG $.
  $}

  ${
    equsexd.1 $e |- ( ph -> A. x ph ) $.
    equsexd.2 $e |- ( ph -> ( ch -> A. x ch ) ) $.
    equsexd.3 $e |- ( ph -> ( x = y -> ( ps <-> ch ) ) ) $.
    $( Deduction form of ~ equsex .  (Contributed by Jim Kingdon,
       29-Dec-2017.) $)
    equsexd $p |- ( ph -> ( E. x ( x = y /\ ps ) <-> ch ) ) $=
      ( cv wceq wa wex wb wi biimp imim2i 3syl wal a1i imp pm3.31 exlimd2 19.26
      a9e jca anim12 syl imbitrrdi anabsi5 idd biimpr pm2.04 jcad eximdh mpi ex
      impbid ) ADIEIJZBKZDLZCAUSCDFGAURBCMZNZURBCNZNUSCNHVAVCURBCOPURBCUAQUBACU
      TACKZURDLUTDEUDVDURUSDACVDDRZAVDADRZCDRZKZVEAAVFNZCVGNZKVDVHNAVIVJVIAFSGU
      EAVFCVGUFUGACDUCUHUIVDURURBACURURNZCVKNACURUJSTACURBNZAVBURCBNZNCVLNHVAVM
      URBCUKPURCBULQTUMUNUOUPUQ $.
  $}

  ${
    dral1.1 $e |- ( A. x x = y -> ( ph <-> ps ) ) $.
    $( Formula-building lemma for use with the Distinctor Reduction Theorem.
       Part of Theorem 9.4 of [Megill] p. 448 (p. 16 of preprint).
       (Contributed by NM, 24-Nov-1994.) $)
    dral1 $p |- ( A. x x = y -> ( A. x ph <-> A. y ps ) ) $=
      ( weq wal hbae biimpd alimdh ax10o syld biimprd wi alequcoms impbid ) CDF
      CGZACGZBDGZQRBCGSQABCCDCHQABEIJBCDKLQSADGZRQBADCDDHQABEMJTRNDCADCKOLP $.
  $}

  ${
    dral2.1 $e |- ( A. x x = y -> ( ph <-> ps ) ) $.
    $( Formula-building lemma for use with the Distinctor Reduction Theorem.
       Part of Theorem 9.4 of [Megill] p. 448 (p. 16 of preprint).
       (Contributed by NM, 27-Feb-2005.) $)
    dral2 $p |- ( A. x x = y -> ( A. z ph <-> A. z ps ) ) $=
      ( weq wal hbae albidh ) CDGCHABECDEIFJ $.
  $}

  ${
    drex2.1 $e |- ( A. x x = y -> ( ph <-> ps ) ) $.
    $( Formula-building lemma for use with the Distinctor Reduction Theorem.
       Part of Theorem 9.4 of [Megill] p. 448 (p. 16 of preprint).
       (Contributed by NM, 27-Feb-2005.) $)
    drex2 $p |- ( A. x x = y -> ( E. z ph <-> E. z ps ) ) $=
      ( weq wal hbae exbidh ) CDGCHABECDEIFJ $.

    $( Formula-building lemma for use with the Distinctor Reduction Theorem.
       (Contributed by Mario Carneiro, 4-Oct-2016.) $)
    drnf1 $p |- ( A. x x = y -> ( F/ x ph <-> F/ y ps ) ) $=
      ( weq wal wi wnf dral1 imbi12d df-nf 3bitr4g ) CDFCGZAACGZHZCGBBDGZHZDGAC
      IBDIPRCDNABOQEABCDEJKJACLBDLM $.

    $( Formula-building lemma for use with the Distinctor Reduction Theorem.
       (Contributed by Mario Carneiro, 4-Oct-2016.) $)
    drnf2 $p |- ( A. x x = y -> ( F/ z ph <-> F/ z ps ) ) $=
      ( weq wal wi wnf dral2 imbi12d df-nf 3bitr4g ) CDGCHZAAEHZIZEHBBEHZIZEHAE
      JBEJQSCDEOABPRFABCDEFKLKAEMBEMN $.
  $}

  $( Closed theorem form of ~ spim .  (Contributed by NM, 15-Jan-2008.)
     (New usage is discouraged.) $)
  spimth $p |- ( A. x ( ( ps -> A. x ps ) /\ ( x = y -> ( ph -> ps ) ) ) ->
              ( A. x ph -> ps ) ) $=
    ( wal wi weq wa imim2 imim2d imp com23 al2imi ax9o syl6 ) BBCEZFZCDGZABFZFZ
    HZCEACERPFZCEBUAAUBCUARAPQTRAPFZFQSUCRBPAIJKLMBCDNO $.

  $( Closed theorem form of ~ spim .  (Contributed by NM, 15-Jan-2008.)
     (Revised by Mario Carneiro, 17-Oct-2016.)  (Proof shortened by Wolf
     Lammen, 24-Feb-2018.) $)
  spimt $p |- ( ( F/ x ps /\ A. x ( x = y -> ( ph -> ps ) ) ) ->
              ( A. x ph -> ps ) ) $=
    ( cv wceq wi wal wex wnf a9e exim mpi 19.35-1 syl 19.9t biimpd sylan9r ) CE
    DEFZABGZGCHZACHZBCIZBCJZBUATCIZUBUCGUASCIUECDKSTCLMABCNOUDUCBBCPQR $.

  ${
    spimh.1 $e |- ( ps -> A. x ps ) $.
    spimh.2 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( Specialization, using implicit substitition.  Compare Lemma 14 of
       [Tarski] p. 70.  The ~ spim series of theorems requires that only one
       direction of the substitution hypothesis hold.  (Contributed by NM,
       5-Aug-1993.)  (Revised by NM, 8-May-2008.)
       (New usage is discouraged.) $)
    spimh $p |- ( A. x ph -> ps ) $=
      ( wal weq wi syl6com alimi ax9o syl ) ACGCDHZBCGZIZCGBAPCNABOFEJKBCDLM $.
  $}

  ${
    spim.1 $e |- F/ x ps $.
    spim.2 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( Specialization, using implicit substitution.  Compare Lemma 14 of
       [Tarski] p. 70.  The ~ spim series of theorems requires that only one
       direction of the substitution hypothesis hold.  (Contributed by NM,
       5-Aug-1993.)  (Revised by Mario Carneiro, 3-Oct-2016.)  (Proof rewritten
       by Jim Kingdon, 10-Jun-2018.) $)
    spim $p |- ( A. x ph -> ps ) $=
      ( nfri spimh ) ABCDBCEGFH $.
  $}

  ${
    spimeh.1 $e |- ( ph -> A. x ph ) $.
    spimeh.2 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( Existential introduction, using implicit substitition.  Compare Lemma 14
       of [Tarski] p. 70.  (Contributed by NM, 7-Aug-1994.)  (Revised by NM,
       3-Feb-2015.)  (New usage is discouraged.) $)
    spimeh $p |- ( ph -> E. x ps ) $=
      ( cv wceq wex a9e com12 eximdh mpi ) ACGDGHZCIBCICDJANBCENABFKLM $.
  $}

  ${
    spimed.1 $e |- ( ch -> F/ x ph ) $.
    spimed.2 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( Deduction version of ~ spime .  (Contributed by NM, 5-Aug-1993.)
       (Revised by Mario Carneiro, 3-Oct-2016.)  (Proof shortened by Wolf
       Lammen, 19-Feb-2018.) $)
    spimed $p |- ( ch -> ( ph -> E. x ps ) ) $=
      ( wal wex nfrd weq wi a9e eximii 19.35i syl6 ) CAADHBDICADFJABDDEKABLDDEM
      GNOP $.
  $}

  ${
    spime.1 $e |- F/ x ph $.
    spime.2 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( Existential introduction, using implicit substitution.  Compare Lemma 14
       of [Tarski] p. 70.  (Contributed by NM, 7-Aug-1994.)  (Revised by Mario
       Carneiro, 3-Oct-2016.)  (Proof shortened by Wolf Lammen, 6-Mar-2018.) $)
    spime $p |- ( ph -> E. x ps ) $=
      ( wex wi wtru wnf a1i spimed mptru ) ABCGHABICDACJIEKFLM $.
  $}

  ${
    cbv3.1 $e |- F/ y ph $.
    cbv3.2 $e |- F/ x ps $.
    cbv3.3 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( Rule used to change bound variables, using implicit substitution.  Usage
       of this theorem is discouraged because proofs are encouraged to use the
       weaker ~ cbv3v if possible.  (Contributed by NM, 5-Aug-1993.)  (Proof
       shortened by Wolf Lammen, 12-May-2018.)  (New usage is discouraged.) $)
    cbv3 $p |- ( A. x ph -> A. y ps ) $=
      ( wal nfal spim alrimi ) ACHBDADCEIABCDFGJK $.
  $}

  ${
    cbv3h.1 $e |- ( ph -> A. y ph ) $.
    cbv3h.2 $e |- ( ps -> A. x ps ) $.
    cbv3h.3 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Andrew Salmon,
       25-May-2011.)  (Proof shortened by Wolf Lammen, 12-May-2018.) $)
    cbv3h $p |- ( A. x ph -> A. y ps ) $=
      ( nfi cbv3 ) ABCDADEHBCFHGI $.
  $}

  ${
    $d x y $.
    cbv3v.nf1 $e |- F/ y ph $.
    cbv3v.nf2 $e |- F/ x ps $.
    cbv3v.1 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( Rule used to change bound variables, using implicit substitution.
       Version of ~ cbv3 with a disjoint variable condition.  (Contributed by
       NM, 5-Aug-1993.)  (Revised by BJ, 31-May-2019.) $)
    cbv3v $p |- ( A. x ph -> A. y ps ) $=
      ( cbv3 ) ABCDEFGH $.
  $}

  ${
    cbv1.1 $e |- F/ x ph $.
    cbv1.2 $e |- F/ y ph $.
    cbv1.3 $e |- ( ph -> F/ y ps ) $.
    cbv1.4 $e |- ( ph -> F/ x ch ) $.
    cbv1.5 $e |- ( ph -> ( x = y -> ( ps -> ch ) ) ) $.
    $( Rule used to change bound variables, using implicit substitution.
       Revised to format hypotheses to common style.  (Contributed by NM,
       5-Aug-1993.)  (Revised by Mario Carneiro, 3-Oct-2016.)  (Revised by Wolf
       Lammen, 13-May-2018.) $)
    cbv1 $p |- ( ph -> ( A. x ps -> A. y ch ) ) $=
      ( wal wi nfim1 weq com12 a2d cbv3 19.21 3imtr3i pm2.86i ) ABDKZCEKZABLZDK
      ACLZEKAUALAUBLUCUDDEABEGHMACDFIMDENZABCAUEBCLJOPQABDFRACEGRST $.
  $}

  ${
    cbv1h.1 $e |- ( ph -> ( ps -> A. y ps ) ) $.
    cbv1h.2 $e |- ( ph -> ( ch -> A. x ch ) ) $.
    cbv1h.3 $e |- ( ph -> ( x = y -> ( ps -> ch ) ) ) $.
    $( Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen,
       13-May-2018.) $)
    cbv1h $p |- ( A. x A. y ph -> ( A. x ps -> A. y ch ) ) $=
      ( wal nfa1 nfa2 wi sp sps syl nfd weq cbv1 ) AEIZDIZBCDESDJZAEDKZTBEUBTAB
      BEILSADAEMNZFOPTCDUATACCDILUCGOPTADEQBCLLUCHOR $.
  $}

  ${
    $d x y $.
    cbv1v.1 $e |- F/ x ph $.
    cbv1v.2 $e |- F/ y ph $.
    cbv1v.3 $e |- ( ph -> F/ y ps ) $.
    cbv1v.4 $e |- ( ph -> F/ x ch ) $.
    cbv1v.5 $e |- ( ph -> ( x = y -> ( ps -> ch ) ) ) $.
    $( Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 5-Aug-1993.)  (Revised by BJ, 16-Jun-2019.) $)
    cbv1v $p |- ( ph -> ( A. x ps -> A. y ch ) ) $=
      ( wal wi nfim1 weq com12 a2d cbv3v 19.21 3imtr3i pm2.86i ) ABDKZCEKZABLZD
      KACLZEKAUALAUBLUCUDDEABEGHMACDFIMDENZABCAUEBCLJOPQABDFRACEGRST $.
  $}

  ${
    cbv2h.1 $e |- ( ph -> ( ps -> A. y ps ) ) $.
    cbv2h.2 $e |- ( ph -> ( ch -> A. x ch ) ) $.
    cbv2h.3 $e |- ( ph -> ( x = y -> ( ps <-> ch ) ) ) $.
    $( Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 5-Aug-1993.) $)
    cbv2h $p |- ( A. x A. y ph -> ( A. x ps <-> A. y ch ) ) $=
      ( wal weq wb wi biimp syl6 cbv1h equcomi biimpr syl56 a7s impbid ) AEIDIB
      DIZCEIZABCDEFGADEJZBCKZBCLHBCMNOAUBUALEDACBEDGFEDJUCAUDCBLEDPHBCQROST $.
  $}

  ${
    cbv2.1 $e |- F/ x ph $.
    cbv2.2 $e |- F/ y ph $.
    cbv2.3 $e |- ( ph -> F/ y ps ) $.
    cbv2.4 $e |- ( ph -> F/ x ch ) $.
    cbv2.5 $e |- ( ph -> ( x = y -> ( ps <-> ch ) ) ) $.
    $( Rule used to change bound variables, using implicit substitution.
       Revised to align format of hypotheses to common style.  (Contributed by
       NM, 5-Aug-1993.)  (Revised by Mario Carneiro, 3-Oct-2016.)  (Revised by
       Wolf Lammen, 13-May-2018.) $)
    cbv2 $p |- ( ph -> ( A. x ps <-> A. y ch ) ) $=
      ( wal wb nfri nfal syl nfrd cbv2h ) AAEKZDKZBDKCEKLARSAEGMRDADEFNMOABCDEA
      BEHPACDIPJQO $.
  $}

  ${
    $d x y $.
    cbv2w.1 $e |- F/ x ph $.
    cbv2w.2 $e |- F/ y ph $.
    cbv2w.3 $e |- ( ph -> F/ y ps ) $.
    cbv2w.4 $e |- ( ph -> F/ x ch ) $.
    cbv2w.5 $e |- ( ph -> ( x = y -> ( ps <-> ch ) ) ) $.
    $( Rule used to change bound variables, using implicit substitution.
       Version of ~ cbv2 with a disjoint variable condition.  (Contributed by
       NM, 5-Aug-1993.)  (Revised by GG, 10-Jan-2024.) $)
    cbv2w $p |- ( ph -> ( A. x ps <-> A. y ch ) ) $=
      ( wal weq wb wi biimp syl6 cbv1v equcomi biimpr syl56 impbid ) ABDKCEKABC
      DEFGHIADELZBCMZBCNJBCOPQACBEDGFIHEDLUBAUCCBNEDRJBCSTQUA $.
  $}

  ${
    $d x y $.
    cbvalv1.nf1 $e |- F/ y ph $.
    cbvalv1.nf2 $e |- F/ x ps $.
    cbvalv1.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Rule used to change bound variables, using implicit substitution.
       Version of ~ cbval with a disjoint variable condition.  See ~ cbvalvw
       for a version with two disjoint variable conditions, and ~ cbvalv for
       another variant.  (Contributed by NM, 13-May-1993.)  (Revised by BJ,
       31-May-2019.) $)
    cbvalv1 $p |- ( A. x ph <-> A. y ps ) $=
      ( wal weq biimpd cbv3v wi biimprd equcoms impbii ) ACHBDHABCDEFCDIZABGJKB
      ADCFEBALCDPABGMNKO $.
    $( $j usage 'cbvalv1' avoids 'ax-io' 'ax-10' 'ax-i12' 'ax-bndl'; $)

    $( Rule used to change bound variables, using implicit substitution.
       Version of ~ cbvex with a disjoint variable condition.  See ~ cbvexvw
       for a version with two disjoint variable conditions, and ~ cbvexv for
       another variant.  (Contributed by NM, 21-Jun-1993.)  (Revised by BJ,
       31-May-2019.) $)
    cbvexv1 $p |- ( E. x ph <-> E. y ps ) $=
      ( wex nfex weq wa nfri bicomd equcoms equsex exsimpr sylbir exlimi impbii
      wb ) ACHZBDHZAUBCBCDFIADCJZBKDHUBBADCADELBATCDCDJZABGMNOUCBDPQRBUADADCEIB
      UDAKCHUAABCDBCFLGOUDACPQRS $.
    $( $j usage 'cbvexv1' avoids 'ax-io' 'ax-10' 'ax-i12' 'ax-bndl'; $)
  $}

  ${
    cbvalh.1 $e |- ( ph -> A. y ph ) $.
    cbvalh.2 $e |- ( ps -> A. x ps ) $.
    cbvalh.3 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Rule used to change bound variables, using implicit substitition.
       (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Andrew Salmon,
       25-May-2011.) $)
    cbvalh $p |- ( A. x ph <-> A. y ps ) $=
      ( wal weq biimpd cbv3h wb equcoms biimprd impbii ) ACHBDHABCDEFCDIABGJKBA
      DCFEDCIABABLCDGMNKO $.
  $}

  ${
    cbval.1 $e |- F/ y ph $.
    cbval.2 $e |- F/ x ps $.
    cbval.3 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 5-Aug-1993.)  (Revised by Mario Carneiro,
       3-Oct-2016.) $)
    cbval $p |- ( A. x ph <-> A. y ps ) $=
      ( nfri cbvalh ) ABCDADEHBCFHGI $.
  $}

  ${
    cbvexh.1 $e |- ( ph -> A. y ph ) $.
    cbvexh.2 $e |- ( ps -> A. x ps ) $.
    cbvexh.3 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Rule used to change bound variables, using implicit substitition.
       (Contributed by NM, 5-Aug-1993.)  (Revised by Mario Carneiro,
       3-Feb-2015.) $)
    cbvexh $p |- ( E. x ph <-> E. y ps ) $=
      ( wex hbex cv wceq wa wb bicomd equcoms equsex simpr eximi sylbir exlimih
      impbii ) ACHZBDHZAUCCBCDFIADJZCJZKZBLZDHUCBADCEBAMCDUEUDKZABGNOPUGBDUFBQR
      STBUBDADCEIBUHALZCHUBABCDFGPUIACUHAQRSTUA $.
  $}

  ${
    cbvex.1 $e |- F/ y ph $.
    cbvex.2 $e |- F/ x ps $.
    cbvex.3 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 5-Aug-1993.) $)
    cbvex $p |- ( E. x ph <-> E. y ps ) $=
      ( nfri cbvexh ) ABCDADEHBCFHGI $.
  $}

  ${
    chvar.1 $e |- F/ x ps $.
    chvar.2 $e |- ( x = y -> ( ph <-> ps ) ) $.
    chvar.3 $e |- ph $.
    $( Implicit substitution of ` y ` for ` x ` into a theorem.  (Contributed
       by Raph Levien, 9-Jul-2003.)  (Revised by Mario Carneiro,
       3-Oct-2016.) $)
    chvar $p |- ps $=
      ( weq biimpd spim mpg ) ABCABCDECDHABFIJGK $.
  $}

  $( A variable introduction law for equality.  Lemma 15 of [Monk2] p. 109,
     however we do not require ` z ` to be distinct from ` x ` and ` y `
     (making the proof longer).  (Contributed by NM, 5-Aug-1993.)  (Proof
     shortened by Andrew Salmon, 25-May-2011.) $)
  equvini $p |- ( x = y -> E. z ( x = z /\ z = y ) ) $=
    ( cv wceq wal wi wo wex ax12or equcomi alimi a9e jctir a1d 19.29 syl6 ax-mp
    wa jaoi eximi 2a1i anc2ri 19.29r ax-8 anc2li equcoms com12 exim syl mpi sps
    imim2i ) CDZADZEZCFZUNBDZEZCFZUOUREZVACFZGZCFZHZHVAUOUNEZUSSZCIZGZABCJUQVIV
    EUQVAVFCFZUSCIZSZVHUQVLVAUQVJVKUPVFCCAKZLCBMNOVFUSCPQUTVIVDUTVAVFCIZUTSVHUT
    VAVNUTVAVNUPCIZVNCAMZUPVFCVMUARUBUCVFUSCUDQVCVICVBVHVAVBVOVHVPVBUPVGGZCFVOV
    HGVAVQCUPVAVGVAVGGACVFVAUSACBUEUFUGUHLUPVGCUIUJUKUMULTTR $.

  $( A variable elimination law for equality with no distinct variable
     requirements.  (Compare ~ equvini .)  (Contributed by NM, 1-Mar-2013.)
     (Revised by NM, 3-Feb-2015.) $)
  equveli $p |- ( A. z ( z = x <-> z = y ) -> x = y ) $=
    ( cv wceq wb wal wi wa albiim ax12or equequ1 imbi12d equid biimtrdi adantrd
    wo sps ax-4 jaoi dral2 a1bi biimpri dral1 mpi equcomi adantld hbequid hbimd
    syl hba1 a1i a5i equtr ax-8 imim12d ax-gen 19.26 spimth sylbir sylancl mpii
    ax-mp sylbi ) CDZADZEZVEBDZEZFCGVGVIHZCGZVIVGHZCGZIZVFVHEZVGVICJVGCGZVICGZV
    OVOCGHZCGZQZQVNVOHZABCKVPWAVTVPVKVOVMVPVKVFVFEZVOHZCGZVOVJWCCACVGVJWCFCVGVG
    WBVIVOCAALCABLMRUAWCVOCVOWCWBVOANZUBUCROPVQWAVSVQVMVOVKVQVMVHVHEZVHVFEZHZBG
    ZVOVLWHCBVIVLWHFCVIVIWFVGWGCBBLCBALMRUDWIWGVOWIWFWGBNWHBSUEBAUFUJOUGVSVKVOV
    MVSVKWBVOWEVSWCWDHZCGZVGVJWCHHZCGZVKWCHZVRWJCVSWBVOCVRCUKWBWBCGHVSACUHULVRC
    SUIUMWLCVGWBVGVIVOCAAUNCABUOUPUQWKWMIWJWLICGWNWJWLCURVJWCCAUSUTVAVBPTTVCVD
    $.

  ${
    nfald.1 $e |- F/ y ph $.
    nfald.2 $e |- ( ph -> F/ x ps ) $.
    $( If ` x ` is not free in ` ph ` , it is not free in ` A. y ph ` .
       (Contributed by Mario Carneiro, 24-Sep-2016.)  (Proof shortened by Wolf
       Lammen, 6-Jan-2018.) $)
    nfald $p |- ( ph -> F/ x A. y ps ) $=
      ( wnf wal nfri alrimih nfnf1 nfal hba1 sp nfrd hbald nfd syl ) ABCGZDHZBD
      HZCGASDADEIFJTUACSCDBCKLTBCDSDMTBCSDNOPQR $.

    $( If ` x ` is not free in ` ph ` , it is not free in ` E. y ph ` .
       (Contributed by Mario Carneiro, 24-Sep-2016.)  (Proof rewritten by Jim
       Kingdon, 7-Feb-2018.) $)
    nfexd $p |- ( ph -> F/ x E. y ps ) $=
      ( wex wal wnf nfri df-nf sylib alrimih alcom exim alimi syl 19.12 imim2i
      wi sylibr ) ABDGZUBCHZTZCHZUBCIAUBBCHZDGZTZCHZUEABUFTZDHZCHZUIAUJCHZDHULA
      UMDADEJABCIUMFBCKLMUJDCNLUKUHCBUFDOPQUHUDCUGUCUBBDCRSPQUBCKUA $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Substitution (without distinct variables)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c [ $. $( Left bracket $)
  $c / $. $( Division. $)
  $c ] $.  $( Right bracket $)

  $( Extend wff definition to include proper substitution (read "the wff that
     results when ` y ` is properly substituted for ` x ` in wff ` ph ` ").
     (Contributed by NM, 24-Jan-2006.) $)
  wsb $a wff [ y / x ] ph $.

  $( Define proper substitution.  Remark 9.1 in [Megill] p. 447 (p. 15 of the
     preprint).  For our notation, we use ` [ y / x ] ph ` to mean "the wff
     that results when ` y ` is properly substituted for ` x ` in the wff
     ` ph ` ".  We can also use ` [ y / x ] ph ` in place of the "free for"
     side condition used in traditional predicate calculus; see, for example,
     ~ stdpc4 .

     Our notation was introduced in Haskell B. Curry's _Foundations of
     Mathematical Logic_ (1977), p. 316 and is frequently used in textbooks of
     lambda calculus and combinatory logic.  This notation improves the common
     but ambiguous notation, " ` ph ( y ) ` is the wff that results when ` y `
     is properly substituted for ` x ` in ` ph ( x ) ` ".  For example, if the
     original ` ph ( x ) ` is ` x = y ` , then ` ph ( y ) ` is ` y = y ` , from
     which we obtain that ` ph ( x ) ` is ` x = x ` .  So what exactly does
     ` ph ( x ) ` mean?  Curry's notation solves this problem.

     In most books, proper substitution has a somewhat complicated recursive
     definition with multiple cases based on the occurrences of free and bound
     variables in the wff.  Instead, we use a single formula that is exactly
     equivalent and gives us a direct definition.  We later prove that our
     definition has the properties we expect of proper substitution (see
     Theorems ~ sbequ , ~ sbcom2 and ~ sbid2v ).

     Note that our definition is valid even when ` x ` and ` y ` are replaced
     with the same variable, as ~ sbid shows.  We achieve this by having ` x `
     free in the first conjunct and bound in the second.  We can also achieve
     this by using a dummy variable, as the alternate definition ~ dfsb7 shows
     (which some logicians may prefer because it doesn't mix free and bound
     variables).  Another alternate definition which uses a dummy variable is
     ~ dfsb7a .

     When ` x ` and ` y ` are distinct, we can express proper substitution with
     the simpler expressions of ~ sb5 and ~ sb6 .

     In classical logic, another possible definition is
     ` ( x = y /\ ph ) \/ A. x ( x = y -> ph ) ` but we do not have an
     intuitionistic proof that this is equivalent.

     There are no restrictions on any of the variables, including what
     variables may occur in wff ` ph ` .  (Contributed by NM, 5-Aug-1993.) $)
  df-sb $a |- ( [ y / x ] ph <->
              ( ( x = y -> ph ) /\ E. x ( x = y /\ ph ) ) ) $.

  ${
    sbimi.1 $e |- ( ph -> ps ) $.
    $( Infer substitution into antecedent and consequent of an implication.
       (Contributed by NM, 25-Jun-1998.) $)
    sbimi $p |- ( [ y / x ] ph -> [ y / x ] ps ) $=
      ( weq wi wa wex wsb imim2i anim2i eximi anim12i df-sb 3imtr4i ) CDFZAGZQA
      HZCIZHQBGZQBHZCIZHACDJBCDJRUATUCABQEKSUBCABQELMNACDOBCDOP $.
  $}

  ${
    sbbii.1 $e |- ( ph <-> ps ) $.
    $( Infer substitution into both sides of a logical equivalence.
       (Contributed by NM, 5-Aug-1993.) $)
    sbbii $p |- ( [ y / x ] ph <-> [ y / x ] ps ) $=
      ( wsb biimpi sbimi biimpri impbii ) ACDFBCDFABCDABEGHBACDABEIHJ $.
  $}

  $( One direction of a simplified definition of substitution.  (Contributed by
     NM, 5-Aug-1993.) $)
  sb1 $p |- ( [ y / x ] ph -> E. x ( x = y /\ ph ) ) $=
    ( wsb weq wi wa wex df-sb simprbi ) ABCDBCEZAFKAGBHABCIJ $.

  $( One direction of a simplified definition of substitution.  (Contributed by
     NM, 5-Aug-1993.) $)
  sb2 $p |- ( A. x ( x = y -> ph ) -> [ y / x ] ph ) $=
    ( weq wi wal wa wex wsb ax-4 equs4 df-sb sylanbrc ) BCDZAEZBFONAGBHABCIOBJA
    BCKABCLM $.

  $( An equality theorem for substitution.  (Contributed by NM, 5-Aug-1993.) $)
  sbequ1 $p |- ( x = y -> ( ph -> [ y / x ] ph ) ) $=
    ( weq wsb wa wi wex pm3.4 19.8a df-sb sylanbrc ex ) BCDZAABCEZNAFZNAGPBHONA
    IPBJABCKLM $.

  $( An equality theorem for substitution.  (Contributed by NM, 5-Aug-1993.) $)
  sbequ2 $p |- ( x = y -> ( [ y / x ] ph -> ph ) ) $=
    ( wsb weq wi wa wex df-sb simpl com12 biimtrid ) ABCDBCEZAFZMAGBHZGZMAABCIP
    MANOJKL $.

  $( One of the two equality axioms of standard predicate calculus, called
     substitutivity of equality.  (The other one is ~ stdpc6 .)  Translated to
     traditional notation, it can be read:  " ` x = y -> ( ph ( x ` ,
     ` x ) -> ph ( x ` , ` y ) ) ` , provided that ` y ` is free for ` x ` in
     ` ph ( x ` , ` y ) ` ".  Axiom 7 of [Mendelson] p. 95.  (Contributed by
     NM, 15-Feb-2005.) $)
  stdpc7 $p |- ( x = y -> ( [ x / y ] ph -> ph ) ) $=
    ( wsb wi sbequ2 equcoms ) ACBDAECBACBFG $.

  $( An equality theorem for substitution.  (Contributed by NM, 5-Aug-1993.) $)
  sbequ12 $p |- ( x = y -> ( ph <-> [ y / x ] ph ) ) $=
    ( weq wsb sbequ1 sbequ2 impbid ) BCDAABCEABCFABCGH $.

  $( An equality theorem for substitution.  (Contributed by NM, 6-Oct-2004.)
     (Proof shortened by Andrew Salmon, 21-Jun-2011.) $)
  sbequ12r $p |- ( x = y -> ( [ x / y ] ph <-> ph ) ) $=
    ( wsb wb weq sbequ12 bicomd equcoms ) ACBDZAECBCBFAJACBGHI $.

  $( An equality theorem for substitution.  (Contributed by NM, 5-Aug-1993.) $)
  sbequ12a $p |- ( x = y -> ( [ y / x ] ph <-> [ x / y ] ph ) ) $=
    ( weq wsb sbequ12 wb equcoms bitr3d ) BCDAABCEACBEZABCFAJGCBACBFHI $.

  $( An identity theorem for substitution.  Remark 9.1 in [Megill] p. 447 (p.
     15 of the preprint).  (Contributed by NM, 5-Aug-1993.) $)
  sbid $p |- ( [ x / x ] ph <-> ph ) $=
    ( wsb weq wb equid sbequ12 ax-mp bicomi ) AABBCZBBDAJEBFABBGHI $.

  $( The specialization axiom of standard predicate calculus.  It states that
     if a statement ` ph ` holds for all ` x ` , then it also holds for the
     specific case of ` y ` (properly) substituted for ` x ` .  Translated to
     traditional notation, it can be read:  " ` A. x ph ( x ) -> ph ( y ) ` ,
     provided that ` y ` is free for ` x ` in ` ph ( x ) ` ".  Axiom 4 of
     [Mendelson] p. 69.  (Contributed by NM, 5-Aug-1993.) $)
  stdpc4 $p |- ( A. x ph -> [ y / x ] ph ) $=
    ( wal weq wi wsb ax-1 alimi sb2 syl ) ABDBCEZAFZBDABCGAMBALHIABCJK $.

  ${
    sbh.1 $e |- ( ph -> A. x ph ) $.
    $( Substitution for a variable not free in a wff does not affect it.
       (Contributed by NM, 5-Aug-1993.)  (Revised by NM, 17-Oct-2004.) $)
    sbh $p |- ( [ y / x ] ph <-> ph ) $=
      ( wsb weq wex wa sb1 19.41h sylib simprd wal stdpc4 syl impbii ) ABCEZAQB
      CFZBGZAQRAHBGSAHABCIRABDJKLAABMQDABCNOP $.
  $}

  ${
    sbf.1 $e |- F/ x ph $.
    $( Substitution for a variable not free in a wff does not affect it.
       (Contributed by NM, 5-Aug-1993.)  (Revised by Mario Carneiro,
       4-Oct-2016.) $)
    sbf $p |- ( [ y / x ] ph <-> ph ) $=
      ( nfri sbh ) ABCABDEF $.
  $}

  $( Substitution has no effect on a bound variable.  (Contributed by NM,
     1-Jul-2005.) $)
  sbf2 $p |- ( [ y / x ] A. x ph <-> A. x ph ) $=
    ( wal nfa1 sbf ) ABDBCABEF $.

  ${
    sb6x.1 $e |- ( ph -> A. x ph ) $.
    $( Equivalence involving substitution for a variable not free.
       (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Andrew Salmon,
       12-Aug-2011.) $)
    sb6x $p |- ( [ y / x ] ph <-> A. x ( x = y -> ph ) ) $=
      ( wsb weq wi wal sbh biidd equsalh bitr4i ) ABCEABCFZAGBHABCDIAABCDMAJKL
      $.
  $}

  ${
    nfs1f.1 $e |- F/ x ph $.
    $( If ` x ` is not free in ` ph ` , it is not free in ` [ y / x ] ph ` .
       (Contributed by Mario Carneiro, 11-Aug-2016.) $)
    nfs1f $p |- F/ x [ y / x ] ph $=
      ( wsb nfri sbh nfxfr ) ABCEABABCABDFGDH $.
  $}

  ${
    hbs1f.1 $e |- ( ph -> A. x ph ) $.
    $( If ` x ` is not free in ` ph ` , it is not free in ` [ y / x ] ph ` .
       (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Andrew Salmon,
       25-May-2011.) $)
    hbs1f $p |- ( [ y / x ] ph -> A. x [ y / x ] ph ) $=
      ( wsb sbh hbxfrbi ) ABCEABABCDFDG $.
  $}

  $( Substitution does not change an identical variable specifier.
     (Contributed by NM, 5-Aug-1993.)  (Revised by NM, 21-Dec-2004.) $)
  sbequ5 $p |- ( [ w / z ] A. x x = y <-> A. x x = y ) $=
    ( weq wal nfae sbf ) ABEAFCDABCGH $.

  $( Substitution does not change a distinctor.  (Contributed by NM,
     5-Aug-1993.)  (Revised by NM, 14-May-2005.) $)
  sbequ6 $p |- ( [ w / z ] -. A. x x = y <-> -. A. x x = y ) $=
    ( weq wal wn nfnae sbf ) ABEAFGCDABCHI $.

  ${
    sbt.1 $e |- ph $.
    $( A substitution into a theorem remains true.  (See ~ chvar and ~ chvarv
       for versions using implicit substitition.)  (Contributed by NM,
       21-Jan-2004.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)
    sbt $p |- [ y / x ] ph $=
      ( wsb nfth sbf mpbir ) ABCEADABCABDFGH $.
  $}

  $( Substitution applied to an atomic wff.  (Contributed by NM,
     5-Aug-1993.) $)
  equsb1 $p |- [ y / x ] x = y $=
    ( weq wi wsb sb2 id mpg ) ABCZIDIABEAIABFIGH $.

  $( Substitution applied to an atomic wff.  (Contributed by NM,
     5-Aug-1993.) $)
  equsb2 $p |- [ y / x ] y = x $=
    ( weq wi wsb sb2 equcomi mpg ) ABCBACZDIABEAIABFABGH $.

  ${
    sbiedh.1 $e |- ( ph -> A. x ph ) $.
    sbiedh.2 $e |- ( ph -> ( ch -> A. x ch ) ) $.
    sbiedh.3 $e |- ( ph -> ( x = y -> ( ps <-> ch ) ) ) $.
    $( Conversion of implicit substitution to explicit substitution (deduction
       version of ~ sbieh ).  New proofs should use ~ sbied instead.
       (Contributed by NM, 30-Jun-1994.)  (Proof shortened by Andrew Salmon,
       25-May-2011.)  (New usage is discouraged.) $)
    sbiedh $p |- ( ph -> ( [ y / x ] ps <-> ch ) ) $=
      ( wsb wex weq wa sb1 wb wi biimp syl6 impd syld wal eximdh syl5 com23 sb2
      19.9hd biimpr alimdh impbid ) ABDEIZCAUICDJZCUIDEKZBLZDJAUJBDEMAULCDFAUKB
      CAUKBCNZBCOHBCPQRUAUBCADFGUESACCDTZUIGAUNUKBOZDTUIACUODFAUKCBAUKUMCBOHBCU
      FQUCUGBDEUDQSUH $.
  $}

  ${
    sbied.1 $e |- F/ x ph $.
    sbied.2 $e |- ( ph -> F/ x ch ) $.
    sbied.3 $e |- ( ph -> ( x = y -> ( ps <-> ch ) ) ) $.
    $( Conversion of implicit substitution to explicit substitution (deduction
       version of ~ sbie ).  (Contributed by NM, 30-Jun-1994.)  (Revised by
       Mario Carneiro, 4-Oct-2016.) $)
    sbied $p |- ( ph -> ( [ y / x ] ps <-> ch ) ) $=
      ( nfri nfrd sbiedh ) ABCDEADFIACDGJHK $.
  $}

  ${
    $d x ph $.  $d x ch $.
    sbiedv.1 $e |- ( ( ph /\ x = y ) -> ( ps <-> ch ) ) $.
    $( Conversion of implicit substitution to explicit substitution (deduction
       version of ~ sbie ).  (Contributed by NM, 7-Jan-2017.) $)
    sbiedv $p |- ( ph -> ( [ y / x ] ps <-> ch ) ) $=
      ( nfv nfvd weq wb ex sbied ) ABCDEADGACDHADEIBCJFKL $.
  $}

  ${
    sbieh.1 $e |- ( ps -> A. x ps ) $.
    sbieh.2 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Conversion of implicit substitution to explicit substitution.  New
       proofs should use ~ sbie instead.  (Contributed by NM, 30-Jun-1994.)
       (New usage is discouraged.) $)
    sbieh $p |- ( [ y / x ] ph <-> ps ) $=
      ( wi wsb wb id hbth wal a1i weq sbiedh ax-mp ) AAGZACDHBIAJZQABCDQCRKBBCL
      GQEMCDNABIGQFMOP $.
  $}

  ${
    sbie.1 $e |- F/ x ps $.
    sbie.2 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Conversion of implicit substitution to explicit substitution.
       (Contributed by NM, 30-Jun-1994.)  (Revised by Mario Carneiro,
       4-Oct-2016.)  (Revised by Wolf Lammen, 30-Apr-2018.) $)
    sbie $p |- ( [ y / x ] ph <-> ps ) $=
      ( nfri sbieh ) ABCDBCEGFH $.
  $}

  ${
    $d x y $.
    sbiev.1 $e |- F/ x ps $.
    sbiev.2 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Conversion of implicit substitution to explicit substitution.  Version
       of ~ sbie with a disjoint variable condition.  (Contributed by Wolf
       Lammen, 18-Jan-2023.) $)
    sbiev $p |- ( [ y / x ] ph <-> ps ) $=
      ( sbie ) ABCDEFG $.
  $}

  ${
    $d x y $.
    equsalv.nf $e |- F/ x ps $.
    equsalv.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( An equivalence related to implicit substitution.  Version of ~ equsal
       with a disjoint variable condition.  (Contributed by NM, 2-Jun-1993.)
       (Revised by BJ, 31-May-2019.) $)
    equsalv $p |- ( A. x ( x = y -> ph ) <-> ps ) $=
      ( weq wi wal wex 19.23 pm5.74i albii a9ev a1bi 3bitr4i ) CDGZBHZCIQCJZBHQ
      AHZCIBQBCEKTRCQABFLMSBCDNOP $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Theorems using axiom ax-11
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( A property related to substitution that unlike ~ equs5 doesn't require a
     distinctor antecedent.  (Contributed by NM, 2-Feb-2007.) $)
  equs5a $p |- ( E. x ( x = y /\ A. y ph ) -> A. x ( x = y -> ph ) ) $=
    ( weq wal wa wi hba1 ax-11 imp exlimih ) BCDZACEZFLAGZBEZBNBHLMOABCIJK $.

  $( A property related to substitution that unlike ~ equs5 doesn't require a
     distinctor antecedent.  (Contributed by NM, 2-Feb-2007.)  (Revised by NM,
     3-Feb-2015.) $)
  equs5e $p |- ( E. x ( x = y /\ ph ) -> A. x ( x = y -> E. y ph ) ) $=
    ( cv wceq wa wex wal wi 19.8a hbe1 syl anim2i eximi equs5a ) BDCDEZAFZBGPAC
    GZCHZFZBGPRIBHQTBASPARSACJACKLMNRBCOL $.

  $( Analogue to ~ ax-11 but for existential quantification.  (Contributed by
     Mario Carneiro and Jim Kingdon, 31-Dec-2017.)  (Proved by Mario Carneiro,
     9-Feb-2018.) $)
  ax11e $p |- ( x = y -> ( E. x ( x = y /\ ph ) -> E. y ph ) ) $=
    ( cv wceq wa wex wi equs5e 19.21bi com12 ) BDCDEZAFBGZLACGZMLNHBABCIJK $.

  $( Quantifier Substitution for existential quantifiers.  Analogue to ~ ax10o
     but for ` E. ` rather than ` A. ` .  (Contributed by Jim Kingdon,
     21-Dec-2017.) $)
  ax10oe $p |- ( A. x x = y -> ( E. x ps -> E. y ps ) ) $=
    ( cv wceq wal wex wa wi ax-ia3 alimi exim syl ax11e sps syld ) BDCDEZBFZABG
    ZQAHZBGZACGZRATIZBFSUAIQUCBQAJKATBLMQUAUBIBABCNOP $.

  ${
    drex1.1 $e |- ( A. x x = y -> ( ph <-> ps ) ) $.
    $( Formula-building lemma for use with the Distinctor Reduction Theorem.
       Part of Theorem 9.4 of [Megill] p. 448 (p. 16 of preprint).
       (Contributed by NM, 27-Feb-2005.)  (Revised by NM, 3-Feb-2015.) $)
    drex1 $p |- ( A. x x = y -> ( E. x ph <-> E. y ps ) ) $=
      ( cv wceq wal wex wa hbae ax-4 biantrurd bitr2d exbidh wi sylbird equcomi
      ax11e sps bitr3d alequcoms impbid ) CFZDFZGZCHZACIZBDIZUGUHUFBJZCIZUIUGUJ
      ACCDCKUGABUJEUGUFBUFCLMNOUFUKUIPCBCDSTQUGUIUEUDGZAJZDIZUHUGUMBDCDDKUGAUMB
      UGULAUFULCCDRTMEUAOUNUHPZDCULUODADCSTUBQUC $.
  $}

  $( Formula-building lemma for use with the Distinctor Reduction Theorem.
     Part of Theorem 9.4 of [Megill] p. 448 (p. 16 of preprint).  (Contributed
     by NM, 5-Aug-1993.) $)
  drsb1 $p |- ( A. x x = y -> ( [ z / x ] ph <-> [ z / y ] ph ) ) $=
    ( weq wal wi wa wex wsb wb equequ1 sps imbi1d anbi1d drex1 anbi12d 3bitr4g
    df-sb ) BCEZBFZBDEZAGZUBAHZBIZHCDEZAGZUFAHZCIZHABDJACDJUAUCUGUEUIUAUBUFATUB
    UFKBBCDLMZNUDUHBCUAUBUFAUJOPQABDSACDSR $.

  ${
    exdistrfor.1 $e |- ( A. x x = y \/ A. x F/ y ph ) $.
    $( Distribution of existential quantifiers, with a bound-variable
       hypothesis saying that ` y ` is not free in ` ph ` , but ` x ` can be
       free in ` ph ` (and there is no distinct variable condition on ` x ` and
       ` y ` ).  (Contributed by Jim Kingdon, 25-Feb-2018.) $)
    exdistrfor $p |- ( E. x E. y ( ph /\ ps ) -> E. x ( ph /\ E. y ps ) ) $=
      ( weq wal wnf wo wa wex biidd drex1 drex2 hbe1 19.9h 19.8a anim2i eximi
      wi sylbi biimtrrdi ax-ial 19.40 19.9t biimpd anim1d syl5 sps eximdh ax-mp
      jaoi ) CDFCGZADHZCGZIABJZDKZCKZABDKZJZCKZTZEUMVBUOUMURUPCKZCKZVAVCUQCDCUP
      UPCDUMUPLMNVDVCVAVCCUPCOPUPUTCBUSABDQRSUAUBUOUQUTCUNCUCUNUQUTTCUQADKZUSJU
      NUTABDUDUNVEAUSUNVEAADUEUFUGUHUIUJULUK $.
  $}

  $( A version of ~ sb4 that doesn't require a distinctor antecedent.
     (Contributed by NM, 2-Feb-2007.) $)
  sb4a $p |- ( [ y / x ] A. y ph -> A. x ( x = y -> ph ) ) $=
    ( wal wsb weq wa wex wi sb1 equs5a syl ) ACDZBCEBCFZMGBHNAIBDMBCJABCKL $.

  ${
    equs45f.1 $e |- ( ph -> A. y ph ) $.
    $( Two ways of expressing substitution when ` y ` is not free in ` ph ` .
       (Contributed by NM, 25-Apr-2008.) $)
    equs45f $p |- ( E. x ( x = y /\ ph ) <-> A. x ( x = y -> ph ) ) $=
      ( weq wa wex wi wal anim2i eximi equs5a syl equs4 impbii ) BCEZAFZBGZPAHB
      IZRPACIZFZBGSQUABATPDJKABCLMABCNO $.

    $( Equivalence for substitution when ` y ` is not free in ` ph ` .
       (Contributed by NM, 5-Aug-1993.)  (Revised by NM, 30-Apr-2008.) $)
    sb6f $p |- ( [ y / x ] ph <-> A. x ( x = y -> ph ) ) $=
      ( wsb weq wi wal sbimi sb4a syl sb2 impbii ) ABCEZBCFAGBHZNACHZBCEOAPBCDI
      ABCJKABCLM $.

    $( Equivalence for substitution when ` y ` is not free in ` ph ` .
       (Contributed by NM, 5-Aug-1993.)  (Revised by NM, 18-May-2008.) $)
    sb5f $p |- ( [ y / x ] ph <-> E. x ( x = y /\ ph ) ) $=
      ( wsb weq wi wal wa wex sb6f equs45f bitr4i ) ABCEBCFZAGBHNAIBJABCDKABCDL
      M $.
  $}

  $( One direction of a simplified definition of substitution that unlike ~ sb4
     doesn't require a distinctor antecedent.  (Contributed by NM,
     2-Feb-2007.) $)
  sb4e $p |- ( [ y / x ] ph -> A. x ( x = y -> E. y ph ) ) $=
    ( wsb weq wa wex wi wal sb1 equs5e syl ) ABCDBCEZAFBGMACGHBIABCJABCKL $.

  $( Special case of a bound-variable hypothesis builder for substitution.
     (Contributed by NM, 2-Feb-2007.) $)
  hbsb2a $p |- ( [ y / x ] A. y ph -> A. x [ y / x ] ph ) $=
    ( wal wsb weq wi sb4a sb2 a5i syl ) ACDBCEBCFAGZBDABCEZBDABCHLMBABCIJK $.

  $( Special case of a bound-variable hypothesis builder for substitution.
     (Contributed by NM, 2-Feb-2007.) $)
  hbsb2e $p |- ( [ y / x ] ph -> A. x [ y / x ] E. y ph ) $=
    ( wsb weq wex wi wal sb4e sb2 a5i syl ) ABCDBCEACFZGZBHMBCDZBHABCINOBMBCJKL
    $.

  ${
    hbsb3.1 $e |- ( ph -> A. y ph ) $.
    $( If ` y ` is not free in ` ph ` , ` x ` is not free in ` [ y / x ] ph ` .
       (Contributed by NM, 5-Aug-1993.) $)
    hbsb3 $p |- ( [ y / x ] ph -> A. x [ y / x ] ph ) $=
      ( wsb wal sbimi hbsb2a syl ) ABCEZACFZBCEJBFAKBCDGABCHI $.
  $}

  ${
    nfs1.1 $e |- F/ y ph $.
    $( If ` y ` is not free in ` ph ` , ` x ` is not free in ` [ y / x ] ph ` .
       (Contributed by Mario Carneiro, 11-Aug-2016.) $)
    nfs1 $p |- F/ x [ y / x ] ph $=
      ( wsb nfri hbsb3 nfi ) ABCEBABCACDFGH $.
  $}

  ${
    sbcof2.1 $e |- ( ph -> A. x ph ) $.
    $( Version of ~ sbco where ` x ` is not free in ` ph ` .  (Contributed by
       Jim Kingdon, 28-Dec-2017.) $)
    sbcof2 $p |- ( [ y / x ] [ x / y ] ph <-> [ y / x ] ph ) $=
      ( wsb weq wi wal hbsb3 sb6f imbi2i albii bitri alimi wex 3syl wa jca sb5f
      eximi ax-11 equcomi imim1i imim2i pm2.43d syl6 a2i sylbi ax-i9 mpi ax-ial
      exim 19.9h sylib sb2 simpl 19.8a anim1i ax11e syl5 imdistani anbi2i exbii
      sb1 sylibr impbii ) ACBEZBCEZABCEZVHBCFZVJAGZBHZGZBHZVLVIVHVJCBFZAGZCHZGZ
      BHZVNVHVJVGGZBHVSVGBCACBDIZJVTVRBVGVQVJACBDJKLMVRVMBVJVQVLVJVQVJVPGZBHVLV
      PBCUAWBVKBWBVJAVPVKVJVJVOABCUBZUCUDUENUFUGNUHVNVLBOZVLVNVJBOWDBCUIVJVLBUL
      UJVLBVKBUKUMUNABCUOPVIVJVOAQZCOZQZBOZVHVIVJAQZBOZVJWJQZBOWHABCVDWIWKBWIVJ
      WJVJAUPZWIBUQRTWKWGBVJWJWFWJVJWEQZBOVJWFWIWMBWIVJWEWLVJVOAWCURRTWEBCUSUTV
      ATPVHVJVGQZBOWHVGBCWASWNWGBVGWFVJACBDSVBVCMVEVF $.
  $}


$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Predicate calculus with distinct variables
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Derive the axiom of distinct variables ax-16
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x ps $.
    spimv.1 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( A version of ~ spim with a distinct variable requirement instead of a
       bound-variable hypothesis.  (Contributed by NM, 5-Aug-1993.) $)
    spimv $p |- ( A. x ph -> ps ) $=
      ( nfv spim ) ABCDBCFEG $.
  $}

  ${
    $v f $.
    $( Define a temporary individual variable. $)
    aev.vf $f setvar f $.
    $d f u v $.  $d f u x y $.  $d u w $.
    $( A "distinctor elimination" lemma with no restrictions on variables in
       the consequent, proved without using ~ ax-16 .  (Contributed by NM,
       8-Nov-2006.)  (Proof shortened by Andrew Salmon, 21-Jun-2011.) $)
    aev $p |- ( A. x x = y -> A. z w = v ) $=
      ( aev.vf vu weq wal hbae ax-8 alrimih equcomi syl6 alequcoms a5i alequcom
      spimv 3syl ) ABHZAIZDEHZCABCJUAFBHZFIZGEHZGIZUBUAUCFABFJTUCAFAFBKRLUDFGHZ
      FIZEGHZEIUFUCUGFUGBFBFHZUGBGBGHUJGFHUGBGFKGFMNROPUHUIEFGEJUGUIFEFEGKRLEGQ
      SUEUBGDGDEKRSL $.
  $}

  ${
    $d x y $.  $d z ph $.
    $( Theorem showing that ~ ax-16 is redundant if ~ ax-17 is included in the
       axiom system.  The important part of the proof is provided by ~ aev .

       See ~ ax16ALT for an alternate proof that does not require ~ ax-10 or
       ~ ax12 .

       This theorem should not be referenced in any proof.  Instead, use
       ~ ax-16 below so that theorems needing ~ ax-16 can be more easily
       identified.  (Contributed by NM, 8-Nov-2006.) $)
    ax16 $p |- ( A. x x = y -> ( ph -> A. x ph ) ) $=
      ( vz weq wal wi aev wsb ax-17 sbequ12 biimpcd alimdh hbsb3 stdpc7 syl6com
      cbv3h syl ) BCEBFBDEZDFZAABFZGBCDBDHATABDIZDFUAASUBDADJZSAUBABDKLMUBADBAB
      DUCNUCADBOQPR $.
  $}

  ${
    $d x y $.
    $( Axiom of Distinct Variables.  The only axiom of predicate calculus
       requiring that variables be distinct (if we consider ~ ax-17 to be a
       metatheorem and not an axiom).  Axiom scheme C16' in [Megill] p. 448 (p.
       16 of the preprint).  It apparently does not otherwise appear in the
       literature but is easily proved from textbook predicate calculus by
       cases.  It is a somewhat bizarre axiom since the antecedent is always
       false in set theory, but nonetheless it is technically necessary as you
       can see from its uses.

       This axiom is redundant if we include ~ ax-17 ; see Theorem ~ ax16 .

       This axiom is obsolete and should no longer be used.  It is proved above
       as Theorem ~ ax16 .  (Contributed by NM, 5-Aug-1993.)
       (New usage is discouraged.) $)
    ax-16 $a |- ( A. x x = y -> ( ph -> A. x ph ) ) $.
  $}

  ${
    $d z x $.
    $( Quantifier introduction when one pair of variables is distinct.
       (Contributed by NM, 2-Jan-2002.) $)
    dveeq2 $p |- ( -. A. x x = y -> ( z = y -> A. x z = y ) ) $=
      ( weq wal wn wi wo ax12or orcom orbi2i mpbi orass mpbir orel2 mpi ax16 sp
      jaoi syl ) ABDAEZFZACDAEZCBDZUDAEGZAEZHZUEUBUGUAHZUGUHUCUFUAHZHZUCUAUFHZH
      UJCBAIUKUIUCUAUFJKLUCUFUAMNUAUGOPUCUEUFUDACQUEARST $.
  $}

  ${
    $d z x $.
    $( Quantifier introduction when one pair of variables is distinct.  Like
       ~ dveeq2 but connecting ` A. x x = y ` by a disjunction rather than
       negation and implication makes the theorem stronger in intuitionistic
       logic.  (Contributed by Jim Kingdon, 1-Feb-2018.) $)
    dveeq2or $p |- ( A. x x = y \/ F/ x z = y ) $=
      ( weq wal wi wnf ax12or orass mpbir pm1.4 orim1i ax-mp mpbi ax16 a5i jaoi
      wo id orim2i df-nf biimpri ) ABDAEZCBDZUDAEFZAEZRZUCUDAGZRUCACDZAEZUFRZRZ
      UGUCUJRZUFRZULUJUCRZUFRZUNUPUJUGRCBAHUJUCUFIJUOUMUFUJUCKLMUCUJUFINUKUFUCU
      JUFUFUIUEAUDACOPUFSQTMUFUHUCUHUFUDAUAUBTM $.
  $}

  ${
    $d x z $.  $d y z $.
    dvelimfALT2.1 $e |- ( ph -> A. x ph ) $.
    dvelimfALT2.2 $e |- ( ps -> A. z ps ) $.
    dvelimfALT2.3 $e |- ( z = y -> ( ph <-> ps ) ) $.
    dvelimfALT2.4 $e |- ( -. A. x x = y -> ( z = y -> A. x z = y ) ) $.
    $( Proof of ~ dvelimf using ~ dveeq2 (shown as the last hypothesis) instead
       of ~ ax12 .  This shows that ~ ax12 could be replaced by ~ dveeq2 (the
       last hypothesis).  (Contributed by Andrew Salmon, 21-Jul-2011.) $)
    dvelimfALT2 $p |- ( -. A. x x = y -> ( ps -> A. x ps ) ) $=
      ( cv wceq wal wn wi ax-17 hbn1 a1i hbimd hbald equsalh albii 3imtr3g ) CJ
      DJZKZCLMZEJUCKZANZELZUHCLBBCLUEUGCEUEEOUEUFACUDCPIAACLNUEFQRSABEDGHTZUHBC
      UIUAUB $.
  $}

  ${
    $d z x $.
    $( A lemma for proving conditionless ZFC axioms.  (Contributed by NM,
       8-Jan-2002.) $)
    nd5 $p |- ( -. A. y y = x -> ( z = y -> A. x z = y ) ) $=
      ( cv wceq wal wi dveeq2 nalequcoms ) CDBDEZJAFGABABCHI $.
  $}

  ${
    $d x ch $.  $d x ph $.
    exlimdv.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction from Theorem 19.23 of [Margaris] p. 90.  (Contributed by NM,
       27-Apr-1994.) $)
    exlimdv $p |- ( ph -> ( E. x ps -> ch ) ) $=
      ( ax-17 exlimdh ) ABCDADFCDFEG $.
  $}

  ${
    $d x z $.  $d y z $.  $d z ph $.
    ax11v2.1 $e |- ( x = z -> ( ph -> A. x ( x = z -> ph ) ) ) $.
    $( Recovery of ~ ax11o from ~ ax11v without using ~ ax-11 .  The hypothesis
       is even weaker than ~ ax11v , with ` z ` both distinct from ` x ` _and_
       not occurring in ` ph ` .  Thus the hypothesis provides an alternate
       axiom that can be used in place of ~ ax11o .  (Contributed by NM,
       2-Feb-2007.) $)
    ax11v2 $p |- ( -. A. x x = y ->
                 ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) ) $=
      ( weq wal wn wex wi a9e wa wb equequ2 adantl dveeq2 imp hba1 imbi1d sps
      albidh syl imbi2d imbi12d mpbii ex exlimdv mpi ) BCFZBGHZDCFZDIUIAUIAJZBG
      ZJZJZDCKUJUKUODUJUKUOUJUKLZBDFZAUQAJZBGZJZJUOEUPUQUIUTUNUKUQUIMUJDCBNZOUP
      USUMAUPUKBGZUSUMMUJUKVBBCDPQVBURULBUKBRUKURULMBUKUQUIAVASTUAUBUCUDUEUFUGU
      H $.
  $}

  ${
    $d x z $.  $d y z $.  $d z ph $.
    ax11a2.1 $e |- ( x = z -> ( A. z ph -> A. x ( x = z -> ph ) ) ) $.
    $( Derive ~ ax-11o from a hypothesis in the form of ~ ax-11 .  The
       hypothesis is even weaker than ~ ax-11 , with ` z ` both distinct from
       ` x ` and not occurring in ` ph ` .  Thus the hypothesis provides an
       alternate axiom that can be used in place of ~ ax11o .  (Contributed by
       NM, 2-Feb-2007.) $)
    ax11a2 $p |- ( -. A. x x = y ->
                 ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) ) $=
      ( wal weq wi ax-17 syl5 ax11v2 ) ABCDAADFBDGZLAHBFADIEJK $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Derive the obsolete axiom of variable substitution ax-11o
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x z $.  $d y z $.  $d z ph $.
    $( Derivation of set.mm's original ~ ax-11o from the shorter ~ ax-11 that
       has replaced it.

       An open problem is whether this theorem can be proved without relying on
       ~ ax-16 or ~ ax-17 .

       Normally, ~ ax11o should be used rather than ~ ax-11o , except by
       theorems specifically studying the latter's properties.  (Contributed by
       NM, 3-Feb-2007.) $)
    ax11o $p |- ( -. A. x x = y ->
               ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) ) $=
      ( vz ax-11 ax11a2 ) ABCDABDEF $.
  $}

  $( Axiom ~ ax-11o ("o" for "old") was the original version of ~ ax-11 ,
     before it was discovered (in Jan. 2007) that the shorter ~ ax-11 could
     replace it.  It appears as Axiom scheme C15' in [Megill] p. 448 (p. 16 of
     the preprint).  It is based on Lemma 16 of [Tarski] p. 70 and Axiom C8 of
     [Monk2] p. 105, from which it can be proved by cases.  To understand this
     theorem more easily, think of " ` -. A. x x = y -> ` ..." as informally
     meaning "if ` x ` and ` y ` are distinct variables, then..."  The
     antecedent becomes false if the same variable is substituted for ` x ` and
     ` y ` , ensuring the theorem is sound whenever this is the case.  In some
     later theorems, we call an antecedent of the form ` -. A. x x = y ` a
     "distinctor."

     This axiom is redundant, as shown by Theorem ~ ax11o .

     This axiom is obsolete and should no longer be used.  It is proved above
     as Theorem ~ ax11o .  (Contributed by NM, 5-Aug-1993.)
     (New usage is discouraged.) $)
  ax-11o $a |- ( -. A. x x = y ->
             ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) ) $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  More theorems related to ax-11 and substitution
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x ph $.
    albidv.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for universal quantifier (deduction form).
       (Contributed by NM, 5-Aug-1993.) $)
    albidv $p |- ( ph -> ( A. x ps <-> A. x ch ) ) $=
      ( ax-17 albidh ) ABCDADFEG $.

    $( Formula-building rule for existential quantifier (deduction form).
       (Contributed by NM, 5-Aug-1993.) $)
    exbidv $p |- ( ph -> ( E. x ps <-> E. x ch ) ) $=
      ( ax-17 exbidh ) ABCDADFEG $.
  $}

  $( A bidirectional version of ~ ax-11o .  (Contributed by NM,
     30-Jun-2006.) $)
  ax11b $p |- ( ( -. A. x x = y /\ x = y ) ->
              ( ph <-> A. x ( x = y -> ph ) ) ) $=
    ( weq wal wn wa wi ax11o imp ax-4 com12 adantl impbid ) BCDZBEFZOGAOAHZBEZP
    OARHABCIJORAHPROAQBKLMN $.

  ${
    $d x y $.  $d x z $.  $d y z $.  $d ph z $.
    $( This is a version of ~ ax-11o when the variables are distinct.  Axiom
       (C8) of [Monk2] p. 105.  (Contributed by NM, 5-Aug-1993.)  (Revised by
       Jim Kingdon, 15-Dec-2017.) $)
    ax11v $p |- ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) $=
      ( vz cv wceq wex wi wal a9e ax-17 ax-11 syl5 equequ2 imbi1d albidv imbi2d
      imbi12d mpbii exlimiv ax-mp ) DEZCEZFZDGBEZUCFZAUFAHZBIZHZHZDCJUDUJDUDUEU
      BFZAUKAHZBIZHZHUJAADIUKUMADKABDLMUDUKUFUNUIDCBNZUDUMUHAUDULUGBUDUKUFAUOOP
      QRSTUA $.
  $}

  ${
    $d x y $.  $d x z $.  $d y z $.  $d ph z $.
    $( Analogue to ~ ax11v for existential quantification.  (Contributed by Jim
       Kingdon, 9-Jan-2018.) $)
    ax11ev $p |- ( x = y -> ( E. x ( x = y /\ ph ) -> ph ) ) $=
      ( vz cv wceq wex wa wi a9e ax11e ax-17 19.9h equequ2 anbi1d exbidv imbi1d
      imbitrdi imbi12d mpbii exlimiv ax-mp ) DEZCEZFZDGBEZUDFZUGAHZBGZAIZIZDCJU
      EUKDUEUFUCFZULAHZBGZAIZIUKULUNADGAABDKADADLMRUEULUGUOUJDCBNZUEUNUIAUEUMUH
      BUEULUGAUPOPQSTUAUB $.
  $}

  $( Lemma used in proofs of substitution properties.  (Contributed by NM,
     5-Aug-1993.) $)
  equs5 $p |- ( -. A. x x = y ->
             ( E. x ( x = y /\ ph ) -> A. x ( x = y -> ph ) ) ) $=
    ( weq wal wn wa wi hbnae hba1 ax11o impd exlimdh ) BCDZBEFZNAGNAHZBEZBBCBIP
    BJONAQABCKLM $.

  ${
    $d x z $.  $d y z $.  $d ph z $.

    $( Lemma used in proofs of substitution properties.  Like ~ equs5 but, in
       intuitionistic logic, replacing negation and implication with
       disjunction makes this a stronger result.  (Contributed by Jim Kingdon,
       2-Feb-2018.) $)
    equs5or $p |- ( A. x x = y \/
             ( E. x ( x = y /\ ph ) -> A. x ( x = y -> ph ) ) ) $=
      ( vz weq wex wal wa wi wo a9e wnf dveeq2or nfnf1 nfri ax11v equequ2 ax-mp
      wb hba1 adantl nfr imp imbi1d sps albidh syl imbi2d imbi12d mpbii alrimih
      ex imp4a 19.21t mpbid 19.23h imbitrdi orim2i pm2.76 olcs exlimiv ) DCEZDF
      BCEZBGZVCAHZBFVCAIZBGZIZJZDCKVBVIDVDVBVIVDVBVHIZJZVDVBJVIIVDVBBLZJVKBCDMV
      LVJVDVLVBVEVGIZBGZVHVLVBVMIZBGVBVNIVLVOBVLBVBBNOVLVBVCAVGVLVBVCAVGIZIZVLV
      BHZBDEZAVSAIZBGZIZIVQABDPVRVSVCWBVPVBVSVCSVLDCBQZUAVRWAVGAVRVBBGZWAVGSVLV
      BWDVBBUBUCWDVTVFBVBBTVBVTVFSBVBVSVCAWCUDUEUFUGUHUIUJULUMUKVBVMBUNUOVEVGBV
      FBTUPUQURRVDVBVHUSRUTVAR $.
  $}

  $( One direction of a simplified definition of substitution when variables
     are distinct.  (Contributed by NM, 5-Aug-1993.) $)
  sb3 $p |- ( -. A. x x = y -> ( E. x ( x = y /\ ph ) -> [ y / x ] ph ) ) $=
    ( weq wal wn wa wex wi wsb equs5 sb2 syl6 ) BCDZBEFNAGBHNAIBEABCJABCKABCLM
    $.

  $( One direction of a simplified definition of substitution when variables
     are distinct.  (Contributed by NM, 5-Aug-1993.) $)
  sb4 $p |- ( -. A. x x = y -> ( [ y / x ] ph -> A. x ( x = y -> ph ) ) ) $=
    ( wsb weq wa wex wal wn wi sb1 equs5 syl5 ) ABCDBCEZAFBGNBHINAJBHABCKABCLM
    $.

  $( One direction of a simplified definition of substitution when variables
     are distinct.  Similar to ~ sb4 but stronger in intuitionistic logic.
     (Contributed by Jim Kingdon, 2-Feb-2018.) $)
  sb4or $p |- ( A. x x = y \/
      A. x ( [ y / x ] ph -> A. x ( x = y -> ph ) ) ) $=
    ( weq wal wa wex wi wo wsb equs5or nfe1 nfa1 nfim sb1 imim1i alrimih orim2i
    nfri ax-mp ) BCDZBEZUAAFZBGZUAAHZBEZHZIUBABCJZUFHZBEZIABCKUGUJUBUGUIBUGBUDU
    FBUCBLUEBMNSUHUDUFABCOPQRT $.

  $( Simplified definition of substitution when variables are distinct.
     (Contributed by NM, 27-May-1997.) $)
  sb4b $p |- ( -. A. x x = y -> ( [ y / x ] ph <-> A. x ( x = y -> ph ) ) ) $=
    ( weq wal wn wsb wi sb4 sb2 impbid1 ) BCDZBEFABCGLAHBEABCIABCJK $.

  $( Simplified definition of substitution when variables are distinct,
     expressed via disjunction.  (Contributed by Jim Kingdon, 18-Mar-2018.) $)
  sb4bor $p |- ( A. x x = y \/
      A. x ( [ y / x ] ph <-> A. x ( x = y -> ph ) ) ) $=
    ( weq wal wsb wi wo wb sb4or sb2 wa df-bi simpri mpan2 alimi orim2i ax-mp )
    BCDZBEZABCFZSAGBEZGZBEZHTUAUBIZBEZHABCJUDUFTUCUEBUCUBUAGZUEABCKUEUCUGLZGUHU
    EGUAUBMNOPQR $.

  $( Bound-variable hypothesis builder for substitution.  (Contributed by NM,
     5-Aug-1993.) $)
  hbsb2 $p |- ( -. A. x x = y -> ( [ y / x ] ph -> A. x [ y / x ] ph ) ) $=
    ( weq wal wn wsb wi sb4 sb2 a5i syl6 ) BCDZBEFABCGZMAHZBENBEABCIONBABCJKL
    $.

  $( Bound-variable hypothesis builder for substitution.  Similar to ~ hbsb2
     but in intuitionistic logic a disjunction is stronger than an implication.
     (Contributed by Jim Kingdon, 2-Feb-2018.) $)
  nfsb2or $p |- ( A. x x = y \/ F/ x [ y / x ] ph ) $=
    ( weq wal wsb wi wnf sb4or sb2 a5i imim2i alimi df-nf sylibr orim2i ax-mp
    wo ) BCDZBEZABCFZSAGZBEZGZBEZRTUABHZRABCIUEUFTUEUAUABEZGZBEUFUDUHBUCUGUAUBU
    ABABCJKLMUABNOPQ $.

  ${
    sbequilem.1 $e |- ( ph \/ ( ps -> ( ch -> th ) ) ) $.
    sbequilem.2 $e |- ( ta \/ ( ps -> ( th -> et ) ) ) $.
    $( Propositional logic lemma used in the ~ sbequi proof.  (Contributed by
       Jim Kingdon, 1-Feb-2018.) $)
    sbequilem $p |- ( ph \/ ( ta \/ ( ps -> ( ch -> et ) ) ) ) $=
      ( wo wi wa pm3.2i andi mpbi andir orbi12i orim2i ax-mp orim1i orass simpr
      pm3.43 pm3.33 syl6 sylbir simpl mpbir orcom orbi1i ) AEIZBCFJZJZIZAEULIIE
      AIZULIZUMUOEAULIZIZEABDFJZJZKZULIZIZUQAEKBCDJZJZEKIZVAIZVBVEUTVDUSKZIZIZV
      FAVDIZEKZVJUSKZIZVIVJEUSIZKVMVJVNGHLVJEUSMNVKVEVLVHAVDEOZAVDUSOPNVHVAVEVG
      ULUTVGBVCURKUKBVCURUBCDFUCUDQQRVEEVAVEVKEVOVJEUAUESRVAUPEUTAULAUSUFSQREAU
      LTUGUNUJULEAUHUINAEULTN $.
  $}

  $( An equality theorem for substitution.  (Contributed by NM, 5-Aug-1993.)
     (Proof modified by Jim Kingdon, 1-Feb-2018.) $)
  sbequi $p |- ( x = y -> ( [ x / z ] ph -> [ y / z ] ph ) ) $=
    ( weq wal wsb wi wo wex nfsb2or wa stdpc7 sbequ1 sylan9 orim2i ax-mp biimpd
    wnf sps equvini eximi 19.35-1 3syl syl9 19.9t sbequilem sbequ2 adantr drsb1
    nfr ax-1 alequcoms sylan9r syld ex orim1i pm1.2 syl jaoi ) DBEZDFZDCEZDFZBC
    EZADBGZADCGZHZHZIZIVIVBVEVFVGDJZVDVGVBVFDSZIVBVEVFVKHHZIADBKVLVMVBVLVFVFDFZ
    VEVKVFDUKVEBDEZVCLZDJVHDJVNVKHBCDUAVPVHDVOVFAVCVGABDMADCNZOUBVFVGDUCUDUEPQV
    DVKVGHZIZVDVEVRHZIVDVGDSZIVSADCKWAVRVDWAVKVGVGDUFRPQVRVTVDVRVEULPQUGVBVIVJV
    BVEVHVBVELVFAVGVBVFAHZVEVAWBDADBUHTUIVEAABCGZVBVGABCNWCVGHBDVOBFWCVGABDCUJR
    UMUNUOUPVJVIVIIVIVDVIVIVDVEVHVDVELVFAVGVDVFACBGZVEAVDVFWDADCBUJRABCMOVDAVGH
    ZVEVCWEDVQTUIUOUPUQVIURUSUTQ $.

  $( An equality theorem for substitution.  Used in proof of Theorem 9.7 in
     [Megill] p. 449 (p. 16 of the preprint).  (Contributed by NM,
     5-Aug-1993.) $)
  sbequ $p |- ( x = y -> ( [ x / z ] ph <-> [ y / z ] ph ) ) $=
    ( weq wsb sbequi wi equcoms impbid ) BCEADBFZADCFZABCDGLKHCBACBDGIJ $.

  $( Formula-building lemma for use with the Distinctor Reduction Theorem.
     Part of Theorem 9.4 of [Megill] p. 448 (p. 16 of preprint).  (Contributed
     by NM, 27-Feb-2005.) $)
  drsb2 $p |- ( A. x x = y -> ( [ x / z ] ph <-> [ y / z ] ph ) ) $=
    ( weq wsb wb sbequ sps ) BCEADBFADCFGBABCDHI $.

  $( A specialization theorem, mostly the same as Theorem 19.8 of [Margaris]
     p. 89.  (Contributed by NM, 5-Aug-1993.)  (Proof rewritten by Jim Kingdon,
     29-Dec-2017.) $)
  spsbe $p |- ( [ y / x ] ph -> E. x ph ) $=
    ( wsb weq wa wex sb1 simpr eximi syl ) ABCDBCEZAFZBGABGABCHMABLAIJK $.

  $( Specialization of implication.  (Contributed by NM, 5-Aug-1993.)  (Proof
     rewritten by Jim Kingdon, 21-Jan-2018.) $)
  spsbim $p |- ( A. x ( ph -> ps ) -> ( [ y / x ] ph -> [ y / x ] ps ) ) $=
    ( wi wal weq wa wex wsb imim2 sps id anim2d alimi syl anim12d df-sb 3imtr4g
    exim ) ABEZCFZCDGZAEZUCAHZCIZHUCBEZUCBHZCIZHACDJBCDJUBUDUGUFUIUAUDUGECABUCK
    LUBUEUHEZCFUFUIEUAUJCUAABUCUAMNOUEUHCTPQACDRBCDRS $.

  $( Specialization of biconditional.  (Contributed by NM, 5-Aug-1993.)  (Proof
     rewritten by Jim Kingdon, 21-Jan-2018.) $)
  spsbbi $p |- ( A. x ( ph <-> ps ) -> ( [ y / x ] ph <-> [ y / x ] ps ) ) $=
    ( wi wal wa wsb wb spsbim anim12i albiim dfbi2 3imtr4i ) ABECFZBAECFZGACDHZ
    BCDHZEZRQEZGABICFQRIOSPTABCDJBACDJKABCLQRMN $.

  ${
    sbbidh.1 $e |- ( ph -> A. x ph ) $.
    sbbidh.2 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Deduction substituting both sides of a biconditional.  New proofs should
       use ~ sbbid instead.  (Contributed by NM, 5-Aug-1993.)
       (New usage is discouraged.) $)
    sbbidh $p |- ( ph -> ( [ y / x ] ps <-> [ y / x ] ch ) ) $=
      ( wb wal wsb alrimih spsbbi syl ) ABCHZDIBDEJCDEJHANDFGKBCDELM $.
  $}

  ${
    sbbid.1 $e |- F/ x ph $.
    sbbid.2 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Deduction substituting both sides of a biconditional.  (Contributed by
       NM, 30-Jun-1993.) $)
    sbbid $p |- ( ph -> ( [ y / x ] ps <-> [ y / x ] ch ) ) $=
      ( wb wal wsb alrimi spsbbi syl ) ABCHZDIBDEJCDEJHANDFGKBCDELM $.
  $}

  $( Elimination of equality from antecedent after substitution.  (Contributed
     by NM, 5-Aug-1993.)  (Proof revised by Jim Kingdon, 20-Jan-2018.) $)
  sbequ8 $p |- ( [ y / x ] ph <-> [ y / x ] ( x = y -> ph ) ) $=
    ( weq wi wa wex wsb pm5.4 simpl pm3.35 jca pm3.4 impbii exbii anbi12i df-sb
    3bitr4ri ) BCDZSAEZEZSTFZBGZFTSAFZBGZFTBCHABCHUATUCUESAIUBUDBUBUDUBSASTJSAK
    LUDSTSAJSAMLNOPTBCQABCQR $.

  $( Substitution has no effect on a nonfree variable.  (Contributed by NM,
     30-May-2009.)  (Revised by Mario Carneiro, 12-Oct-2016.)  (Proof shortened
     by Wolf Lammen, 3-May-2018.) $)
  sbft $p |- ( F/ x ph -> ( [ y / x ] ph <-> ph ) ) $=
    ( wnf wsb wex spsbe 19.9t imbitrid wal nfr stdpc4 syl6 impbid ) ABDZABCEZAP
    ABFOAABCGABHIOAABJPABKABCLMN $.

  ${
    sbid2h.1 $e |- ( ph -> A. x ph ) $.
    $( An identity law for substitution.  (Contributed by NM, 5-Aug-1993.) $)
    sbid2h $p |- ( [ y / x ] [ x / y ] ph <-> ph ) $=
      ( wsb sbcof2 sbh bitri ) ACBEBCEABCEAABCDFABCDGH $.
  $}

  ${
    sbid2.1 $e |- F/ x ph $.
    $( An identity law for substitution.  (Contributed by NM, 5-Aug-1993.)
       (Revised by Mario Carneiro, 6-Oct-2016.) $)
    sbid2 $p |- ( [ y / x ] [ x / y ] ph <-> ph ) $=
      ( nfri sbid2h ) ABCABDEF $.
  $}

  $( An idempotent law for substitution.  (Contributed by NM, 30-Jun-1994.)
     (Proof rewritten by Jim Kingdon, 21-Jan-2018.) $)
  sbidm $p |- ( [ y / x ] [ y / x ] ph <-> [ y / x ] ph ) $=
    ( wsb weq wi wa df-sb simplbi sbimi sbequ8 sylibr ax-1 pm4.24 ax-ie1 19.41h
    wex sb1 bitr4i exbii anim2i anim1i eximi sylbi anass anbi2i sylanbrc impbii
    sylib syl ) ABCDZBCDZUKULBCEZAFZBCDUKUKUNBCUKUNUMAGZBQZABCHZIJABCKLUKUMUKFU
    MUKGZBQZULUKUMMUKUPUSABCRUPUMUNUPGZGZBQZUSUPUMUNGZUPGZBQZVBUPUOUPGZBQZVEUPU
    PUPGVGUPNUOUPBUOBOPSVFVDBUOVCUPAUNUMAUMMUAUBUCUDVDVABUMUNUPUETUIURVABUKUTUM
    UQUFTLUJUKBCHUGUH $.

  ${
    sb5rf.1 $e |- ( ph -> A. y ph ) $.
    $( Reversed substitution.  (Contributed by NM, 3-Feb-2005.)  (Proof
       shortened by Andrew Salmon, 25-May-2011.) $)
    sb5rf $p |- ( ph <-> E. y ( y = x /\ [ y / x ] ph ) ) $=
      ( weq wsb wa wex sbid2h sb1 sylbir stdpc7 imp exlimih impbii ) ACBEZABCFZ
      GZCHZAQCBFSACBDIQCBJKRACDPQAACBLMNO $.

    $( Reversed substitution.  (Contributed by NM, 5-Aug-1993.)  (Proof
       shortened by Andrew Salmon, 25-May-2011.) $)
    sb6rf $p |- ( ph <-> A. y ( y = x -> [ y / x ] ph ) ) $=
      ( weq wsb wi wal sbequ1 equcoms com12 alrimih sb2 sbid2h sylib impbii ) A
      CBEZABCFZGZCHZASCDQARARGBCABCIJKLTRCBFARCBMACBDNOP $.
  $}

  ${
    sb8h.1 $e |- ( ph -> A. y ph ) $.
    $( Substitution of variable in universal quantifier.  (Contributed by NM,
       5-Aug-1993.)  (Proof shortened by Andrew Salmon, 25-May-2011.)  (Proof
       shortened by Jim Kingdon, 15-Jan-2018.) $)
    sb8h $p |- ( A. x ph <-> A. y [ y / x ] ph ) $=
      ( wsb hbsb3 sbequ12 cbvalh ) AABCEBCDABCDFABCGH $.
  $}

  ${
    sb8eh.1 $e |- ( ph -> A. y ph ) $.
    $( Substitution of variable in existential quantifier.  (Contributed by NM,
       12-Aug-1993.)  (Proof rewritten by Jim Kingdon, 15-Jan-2018.) $)
    sb8eh $p |- ( E. x ph <-> E. y [ y / x ] ph ) $=
      ( wsb hbsb3 sbequ12 cbvexh ) AABCEBCDABCDFABCGH $.
  $}

  ${
    sb8e.1 $e |- F/ y ph $.
    $( Substitution of variable in universal quantifier.  (Contributed by NM,
       5-Aug-1993.)  (Revised by Mario Carneiro, 6-Oct-2016.)  (Proof shortened
       by Jim Kingdon, 15-Jan-2018.) $)
    sb8 $p |- ( A. x ph <-> A. y [ y / x ] ph ) $=
      ( wsb nfs1 sbequ12 cbval ) AABCEBCDABCDFABCGH $.

    $( Substitution of variable in existential quantifier.  (Contributed by NM,
       12-Aug-1993.)  (Revised by Mario Carneiro, 6-Oct-2016.)  (Proof
       shortened by Jim Kingdon, 15-Jan-2018.) $)
    sb8e $p |- ( E. x ph <-> E. y [ y / x ] ph ) $=
      ( wsb nfs1 sbequ12 cbvex ) AABCEBCDABCDFABCGH $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Predicate calculus with distinct variables (cont.)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x y z $.  $d z ph $.
    ax16i.1 $e |- ( x = z -> ( ph <-> ps ) ) $.
    ax16i.2 $e |- ( ps -> A. x ps ) $.
    $( Inference with ~ ax-16 as its conclusion, that does not require
       ~ ax-10 , ~ ax-11 , or ~ ax12 for its proof.  The hypotheses may be
       eliminable without one or more of these axioms in special cases.
       (Contributed by NM, 20-May-2008.) $)
    ax16i $p |- ( A. x x = y -> ( ph -> A. x ph ) ) $=
      ( weq wal wi ax-17 ax-8 cbv3h spimv equid mpi syl syl5com alimdh mpcom
      alimi biimpcd biimprd syl6com ) CDHZCIZCEHZEIZAACIZJUFEDHZEIZUHUEUJCEUEEK
      ZUJCKCEDLMUKECHZEIZUHUEUKUNUJUEECECDLNUEUJUMEULUEDCHZUJUMUECCHUOCOCDCLPUJ
      DEHZUOUMJUJEEHZUPEOZEDELPDECLQRSTUMUGEUMUQUGURECELPZUAQQAUHBEIUIAUGBEAEKZ
      UGABFUBSBAECGUTUMUGBAJUSUGABFUCQMUDQ $.
  $}

  ${
    $d x y z $.  $d z ph $.
    $( Version of ~ ax16 that does not require ~ ax-10 or ~ ax12 for its proof.
       (Contributed by NM, 17-May-2008.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    ax16ALT $p |- ( A. x x = y -> ( ph -> A. x ph ) ) $=
      ( vz wsb sbequ12 ax-17 hbsb3 ax16i ) AABDEBCDABDFABDADGHI $.
  $}

  ${
    $d x ps $.
    spv.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Specialization, using implicit substitition.  (Contributed by NM,
       30-Aug-1993.) $)
    spv $p |- ( A. x ph -> ps ) $=
      ( weq biimpd spimv ) ABCDCDFABEGH $.
  $}

  ${
    $d x ph $.
    spimev.1 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( Distinct-variable version of ~ spime .  (Contributed by NM,
       5-Aug-1993.) $)
    spimev $p |- ( ph -> E. x ps ) $=
      ( nfv spime ) ABCDACFEG $.
  $}

  ${
    $d x ps $.
    speiv.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    speiv.2 $e |- ps $.
    $( Inference from existential specialization, using implicit substitition.
       (Contributed by NM, 19-Aug-1993.) $)
    speiv $p |- E. x ph $=
      ( wex weq biimprd spimev ax-mp ) BACGFBACDCDHABEIJK $.
  $}

  ${
    $d x z $.  $d y z $.
    $( A variable introduction law for equality.  Lemma 15 of [Monk2] p. 109.
       (Contributed by NM, 5-Aug-1993.) $)
    equvin $p |- ( x = y <-> E. z ( x = z /\ z = y ) ) $=
      ( weq wa wex equvini ax-17 equtr imp exlimih impbii ) ABDZACDZCBDZEZCFABC
      GPMCMCHNOMACBIJKL $.
  $}

  ${
    $d x y $.
    $( A generalization of Axiom ~ ax-16 .  (Contributed by NM, 5-Aug-1993.)
       (Proof shortened by Andrew Salmon, 25-May-2011.) $)
    a16g $p |- ( A. x x = y -> ( ph -> A. z ph ) ) $=
      ( weq wal aev ax16 biidd dral1 biimprd sylsyld ) BCEBFDBEDFZAABFZADFZBCDD
      BGABCHMONAADBMAIJKL $.

    $( A generalization of Axiom ~ ax-16 .  (Contributed by NM, 5-Aug-1993.) $)
    a16gb $p |- ( A. x x = y -> ( ph <-> A. z ph ) ) $=
      ( weq wal a16g ax-4 impbid1 ) BCEBFAADFABCDGADHI $.

    $( If there is only one element in the universe, then everything satisfies
       ` F/ ` .  (Contributed by Mario Carneiro, 7-Oct-2016.) $)
    a16nf $p |- ( A. x x = y -> F/ z ph ) $=
      ( weq wal nfae a16g nfd ) BCEBFADBCDGABCDHI $.
  $}

  ${
    $d x ph $.  $d y ph $.
    2albidv.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for 2 existential quantifiers (deduction form).
       (Contributed by NM, 4-Mar-1997.) $)
    2albidv $p |- ( ph -> ( A. x A. y ps <-> A. x A. y ch ) ) $=
      ( wal albidv ) ABEGCEGDABCEFHH $.

    $( Formula-building rule for 2 existential quantifiers (deduction form).
       (Contributed by NM, 1-May-1995.) $)
    2exbidv $p |- ( ph -> ( E. x E. y ps <-> E. x E. y ch ) ) $=
      ( wex exbidv ) ABEGCEGDABCEFHH $.
  $}

  ${
    $d x ph $.  $d y ph $.  $d z ph $.
    3exbidv.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for 3 existential quantifiers (deduction form).
       (Contributed by NM, 1-May-1995.) $)
    3exbidv $p |- ( ph -> ( E. x E. y E. z ps <-> E. x E. y E. z ch ) ) $=
      ( wex exbidv 2exbidv ) ABFHCFHDEABCFGIJ $.
  $}

  ${
    $d x ph $.  $d y ph $.  $d z ph $.  $d w ph $.
    4exbidv.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for 4 existential quantifiers (deduction form).
       (Contributed by NM, 3-Aug-1995.) $)
    4exbidv $p |- ( ph ->
                     ( E. x E. y E. z E. w ps <-> E. x E. y E. z E. w ch ) ) $=
      ( wex 2exbidv ) ABGIFICGIFIDEABCFGHJJ $.
  $}

  ${
    $d x ph $.
    $( Special case of Theorem 19.9 of [Margaris] p. 89.  (Contributed by NM,
       28-May-1995.)  (Revised by NM, 21-May-2007.) $)
    19.9v $p |- ( E. x ph <-> ph ) $=
      ( ax-17 19.9h ) ABABCD $.
  $}

  ${
    exlimdd.1 $e |- F/ x ph $.
    exlimdd.2 $e |- F/ x ch $.
    exlimdd.3 $e |- ( ph -> E. x ps ) $.
    exlimdd.4 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( Existential elimination rule of natural deduction.  (Contributed by
       Mario Carneiro, 9-Feb-2017.) $)
    exlimdd $p |- ( ph -> ch ) $=
      ( wex ex exlimd mpd ) ABDICGABCDEFABCHJKL $.
  $}

  ${
    $d x ph $.
    $( Special case of Theorem 19.21 of [Margaris] p. 90. _Notational
       convention_:  We sometimes suffix with "v" the label of a theorem
       eliminating a hypothesis such as ` ( ph -> A. x ph ) ` in ~ 19.21 via
       the use of distinct variable conditions combined with ~ ax-17 .
       Conversely, we sometimes suffix with "f" the label of a theorem
       introducing such a hypothesis to eliminate the need for the distinct
       variable condition; e.g., ~ euf derived from ~ df-eu .  The "f" stands
       for "not free in" which is less restrictive than "does not occur in".
       (Contributed by NM, 5-Aug-1993.) $)
    19.21v $p |- ( A. x ( ph -> ps ) <-> ( ph -> A. x ps ) ) $=
      ( ax-17 19.21h ) ABCACDE $.
  $}

  ${
    $d x ph $.
    alrimiv.1 $e |- ( ph -> ps ) $.
    $( Inference from Theorem 19.21 of [Margaris] p. 90.  (Contributed by NM,
       5-Aug-1993.) $)
    alrimiv $p |- ( ph -> A. x ps ) $=
      ( ax-17 alrimih ) ABCACEDF $.
  $}

  ${
    $d x ph $.  $d y ph $.
    alrimivv.1 $e |- ( ph -> ps ) $.
    $( Inference from Theorem 19.21 of [Margaris] p. 90.  (Contributed by NM,
       31-Jul-1995.) $)
    alrimivv $p |- ( ph -> A. x A. y ps ) $=
      ( wal alrimiv ) ABDFCABDEGG $.
  $}

  ${
    $d x ph $.  $d x ps $.
    alrimdv.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction from Theorem 19.21 of [Margaris] p. 90.  (Contributed by NM,
       10-Feb-1997.) $)
    alrimdv $p |- ( ph -> ( ps -> A. x ch ) ) $=
      ( ax-17 alrimdh ) ABCDADFBDFEG $.
  $}

  ${
    $d x ph $.
    nfdv.1 $e |- ( ph -> ( ps -> A. x ps ) ) $.
    $( Apply the definition of not-free in a context.  (Contributed by Mario
       Carneiro, 11-Aug-2016.) $)
    nfdv $p |- ( ph -> F/ x ps ) $=
      ( wal wi wnf alrimiv df-nf sylibr ) ABBCEFZCEBCGAKCDHBCIJ $.
  $}

  ${
    $d x ph $.  $d y ph $.
    $( Quantification of two variables over a formula in which they do not
       occur.  (Contributed by Alan Sare, 12-Apr-2011.) $)
    2ax17 $p |- ( ph -> A. x A. y ph ) $=
      ( id alrimivv ) AABCADE $.
  $}

  ${
    $d x ph $.
    alimdv.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction from Theorem 19.20 of [Margaris] p. 90.  (Contributed by NM,
       3-Apr-1994.) $)
    alimdv $p |- ( ph -> ( A. x ps -> A. x ch ) ) $=
      ( ax-17 alimdh ) ABCDADFEG $.

    $( Deduction from Theorem 19.22 of [Margaris] p. 90.  (Contributed by NM,
       27-Apr-1994.) $)
    eximdv $p |- ( ph -> ( E. x ps -> E. x ch ) ) $=
      ( ax-17 eximdh ) ABCDADFEG $.
  $}

  ${
    $d x ph $.  $d y ph $.
    2alimdv.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction from Theorem 19.22 of [Margaris] p. 90.  (Contributed by NM,
       27-Apr-2004.) $)
    2alimdv $p |- ( ph -> ( A. x A. y ps -> A. x A. y ch ) ) $=
      ( wal alimdv ) ABEGCEGDABCEFHH $.

    $( Deduction from Theorem 19.22 of [Margaris] p. 90.  (Contributed by NM,
       3-Aug-1995.) $)
    2eximdv $p |- ( ph -> ( E. x E. y ps -> E. x E. y ch ) ) $=
      ( wex eximdv ) ABEGCEGDABCEFHH $.
  $}

  ${
    $d x ps $.
    $( Special case of Theorem 19.23 of [Margaris] p. 90.  (Contributed by NM,
       28-Jun-1998.) $)
    19.23v $p |- ( A. x ( ph -> ps ) <-> ( E. x ph -> ps ) ) $=
      ( ax-17 19.23h ) ABCBCDE $.
  $}

  ${
    $d x ps $.  $d y ps $.
    $( Theorem 19.23 of [Margaris] p. 90 extended to two variables.
       (Contributed by NM, 10-Aug-2004.) $)
    19.23vv $p |- ( A. x A. y ( ph -> ps ) <-> ( E. x E. y ph -> ps ) ) $=
      ( wi wal wex 19.23v albii bitri ) ABEDFZCFADGZBEZCFLCGBEKMCABDHILBCHJ $.
  $}

  ${
    $d x y $.  $d x ph $.
    $( If a formula does not contain a variable ` x ` , then it is equivalent
       to the corresponding prototype of substitution with a fresh variable
       (see ~ sb6 ).  (Contributed by BJ, 23-Jul-2023.) $)
    equsv $p |- ( A. x ( x = y -> ph ) <-> ph ) $=
      ( weq wi wal wex 19.23v a9ev a1bi bitr4i ) BCDZAEBFLBGZAEALABHMABCIJK $.
  $}

  ${
    $d x ph $.
    sbbidv.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Deduction substituting both sides of a biconditional, with ` ph ` and
       ` x ` disjoint.  See also ~ sbbid .  (Contributed by Wolf Lammen,
       6-May-2023.)  (Proof shortened by Steven Nguyen, 6-Jul-2023.) $)
    sbbidv $p |- ( ph -> ( [ t / x ] ps <-> [ t / x ] ch ) ) $=
      ( wb wal wsb alrimiv spsbbi syl ) ABCGZDHBDEICDEIGAMDFJBCDEKL $.
  $}

  ${
    $d x y $.
    $( Two equivalent ways of expressing the proper substitution of ` y ` for
       ` x ` in ` ph ` , when ` x ` and ` y ` are distinct.  Theorem 6.2 of
       [Quine] p. 40.  The proof does not involve ~ df-sb .  (Contributed by
       NM, 14-Apr-2008.) $)
    sb56 $p |- ( E. x ( x = y /\ ph ) <-> A. x ( x = y -> ph ) ) $=
      ( weq wi wal hba1 ax11v ax-4 com12 impbid equsex ) ABCDZAEZBFZBCNBGMAOABC
      HOMANBIJKL $.

    $( Equivalence for substitution.  Compare Theorem 6.2 of [Quine] p. 40.
       Also proved as Lemmas 16 and 17 of [Tarski] p. 70.  (Contributed by NM,
       18-Aug-1993.)  (Revised by NM, 14-Apr-2008.) $)
    sb6 $p |- ( [ y / x ] ph <-> A. x ( x = y -> ph ) ) $=
      ( weq wi wa wex wal wsb sb56 anbi2i df-sb ax-4 pm4.71ri 3bitr4i ) BCDZAEZ
      PAFBGZFQQBHZFABCISRSQABCJKABCLSQQBMNO $.

    $( Equivalence for substitution.  Similar to Theorem 6.1 of [Quine] p. 40.
       (Contributed by NM, 18-Aug-1993.)  (Revised by NM, 14-Apr-2008.) $)
    sb5 $p |- ( [ y / x ] ph <-> E. x ( x = y /\ ph ) ) $=
      ( wsb weq wi wal wa wex sb6 sb56 bitr4i ) ABCDBCEZAFBGMAHBIABCJABCKL $.

    $( Version of ~ sbn where ` x ` and ` y ` are distinct.  (Contributed by
       Jim Kingdon, 18-Dec-2017.) $)
    sbnv $p |- ( [ y / x ] -. ph <-> -. [ y / x ] ph ) $=
      ( wn wsb weq wa wex wi wal sb6 alinexa bitri sb5 xchbinxr ) ADZBCEZBCFZAG
      BHZABCEQRPIBJSDPBCKRABLMABCNO $.

    $( Version of ~ sban where ` x ` and ` y ` are distinct.  (Contributed by
       Jim Kingdon, 24-Dec-2017.) $)
    sbanv $p |- ( [ y / x ] ( ph /\ ps ) <->
                  ( [ y / x ] ph /\ [ y / x ] ps ) ) $=
      ( wa wsb weq wi wal sb6 anbi12i 19.26 pm4.76 albii 3bitr2i bitr4i ) ABEZC
      DFCDGZQHZCIZACDFZBCDFZEZQCDJUCRAHZCIZRBHZCIZEUDUFEZCITUAUEUBUGACDJBCDJKUD
      UFCLUHSCRABMNOP $.

    $( Version of ~ sbor where ` x ` and ` y ` are distinct.  (Contributed by
       Jim Kingdon, 3-Feb-2018.) $)
    sborv $p |- ( [ y / x ] ( ph \/ ps ) <->
                  ( [ y / x ] ph \/ [ y / x ] ps ) ) $=
      ( wo wsb weq wa wex sb5 andi exbii 19.43 3bitri orbi12i bitr4i ) ABEZCDFZ
      CDGZAHZCIZSBHZCIZEZACDFZBCDFZERSQHZCITUBEZCIUDQCDJUGUHCSABKLTUBCMNUEUAUFU
      CACDJBCDJOP $.

    $( Forward direction of ~ sbimv .  (Contributed by Jim Kingdon,
       25-Dec-2017.) $)
    sbi1v $p |- ( [ y / x ] ( ph -> ps )
                      -> ( [ y / x ] ph -> [ y / x ] ps ) ) $=
      ( wsb weq wi wal sb6 ax-2 al2imi sb2 syl6 sylbi biimtrid ) ACDECDFZAGZCHZ
      ABGZCDEZBCDEZACDITPSGZCHZRUAGSCDIUCRPBGZCHUAUBQUDCPABJKBCDLMNO $.

    $( Reverse direction of ~ sbimv .  (Contributed by Jim Kingdon,
       18-Jan-2018.) $)
    sbi2v $p |- ( ( [ y / x ] ph -> [ y / x ] ps )
                      -> [ y / x ] ( ph -> ps ) ) $=
      ( weq wa wex wi wal wsb 19.38 pm3.3 pm2.04 syli alimi syl sb5 sb6 imbi12i
      3imtr4i ) CDEZAFZCGZUABHZCIZHZUAABHZHZCIZACDJZBCDJZHUGCDJUFUBUDHZCIUIUBUD
      CKULUHCUAULAUDHUGUAAUDLAUABMNOPUJUCUKUEACDQBCDRSUGCDRT $.

    $( Intuitionistic proof of ~ sbim where ` x ` and ` y ` are distinct.
       (Contributed by Jim Kingdon, 18-Jan-2018.) $)
    sbimv $p |- ( [ y / x ] ( ph -> ps )
                  <-> ( [ y / x ] ph -> [ y / x ] ps ) ) $=
      ( wi wsb sbi1v sbi2v impbii ) ABECDFACDFBCDFEABCDGABCDHI $.
  $}

  ${
    $d x ph $.
    $( Substitution for a variable not occurring in a proposition.  See ~ sbf
       for a version without disjoint variable condition on ` x , ph ` .  If
       one adds a disjoint variable condition on ` x , t ` , then ~ sbv can be
       proved directly by chaining ~ equsv with ~ sb6 .  (Contributed by BJ,
       22-Dec-2020.) $)
    sbv $p |- ( [ t / x ] ph <-> ph ) $=
      ( ax-17 sbh ) ABCABDE $.
  $}

  ${
    $d x y $.
    sblimv.1 $e |- ( ps -> A. x ps ) $.
    $( Version of ~ sblim where ` x ` and ` y ` are distinct.  (Contributed by
       Jim Kingdon, 19-Jan-2018.) $)
    sblimv $p |- ( [ y / x ] ( ph -> ps ) <-> ( [ y / x ] ph -> ps ) ) $=
      ( wi wsb sbimv sbh imbi2i bitri ) ABFCDGACDGZBCDGZFLBFABCDHMBLBCDEIJK $.
  $}

  ${
    $d ph y $.  $d ps x $.
    $( Theorem *11.53 in [WhiteheadRussell] p. 164.  (Contributed by Andrew
       Salmon, 24-May-2011.) $)
    pm11.53 $p |- ( A. x A. y ( ph -> ps ) <-> ( E. x ph -> A. y ps ) ) $=
      ( wi wal wex 19.21v albii ax-17 hbal 19.23h bitri ) ABEDFZCFABDFZEZCFACGO
      ENPCABDHIAOCBCDBCJKLM $.
  $}

  ${
    $d x ps $.  $d y ps $.
    exlimivv.1 $e |- ( ph -> ps ) $.
    $( Inference from Theorem 19.23 of [Margaris] p. 90.  (Contributed by NM,
       1-Aug-1995.) $)
    exlimivv $p |- ( E. x E. y ph -> ps ) $=
      ( wex exlimiv ) ADFBCABDEGG $.
  $}

  ${
    $d x ch $.  $d x ph $.  $d y ch $.  $d y ph $.
    exlimdvv.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction from Theorem 19.23 of [Margaris] p. 90.  (Contributed by NM,
       31-Jul-1995.) $)
    exlimdvv $p |- ( ph -> ( E. x E. y ps -> ch ) ) $=
      ( wex exlimdv ) ABEGCDABCEFHH $.
  $}

  ${
    $d x ch $.  $d x ph $.
    exlimddv.1 $e |- ( ph -> E. x ps ) $.
    exlimddv.2 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( Existential elimination rule of natural deduction.  (Contributed by
       Mario Carneiro, 15-Jun-2016.) $)
    exlimddv $p |- ( ph -> ch ) $=
      ( wex ex exlimdv mpd ) ABDGCEABCDABCFHIJ $.
  $}

  ${
    $d x ps $.
    $( Theorem 19.27 of [Margaris] p. 90.  (Contributed by NM, 3-Jun-2004.) $)
    19.27v $p |- ( A. x ( ph /\ ps ) <-> ( A. x ph /\ ps ) ) $=
      ( ax-17 19.27h ) ABCBCDE $.
  $}

  ${
    $d x ph $.
    $( Theorem 19.28 of [Margaris] p. 90.  (Contributed by NM, 25-Mar-2004.) $)
    19.28v $p |- ( A. x ( ph /\ ps ) <-> ( ph /\ A. x ps ) ) $=
      ( ax-17 19.28h ) ABCACDE $.
  $}

  ${
    $d x ps $.
    19.36aiv.1 $e |- E. x ( ph -> ps ) $.
    $( Inference from Theorem 19.36 of [Margaris] p. 90.  (Contributed by NM,
       5-Aug-1993.) $)
    19.36aiv $p |- ( A. x ph -> ps ) $=
      ( nfv 19.36i ) ABCBCEDF $.
  $}

  ${
    $d x ps $.
    $( Special case of Theorem 19.41 of [Margaris] p. 90.  (Contributed by NM,
       5-Aug-1993.) $)
    19.41v $p |- ( E. x ( ph /\ ps ) <-> ( E. x ph /\ ps ) ) $=
      ( ax-17 19.41h ) ABCBCDE $.
  $}

  ${
    $d x ps $.  $d y ps $.
    $( Theorem 19.41 of [Margaris] p. 90 with 2 quantifiers.  (Contributed by
       NM, 30-Apr-1995.) $)
    19.41vv $p |- ( E. x E. y ( ph /\ ps ) <-> ( E. x E. y ph /\ ps ) ) $=
      ( wa wex 19.41v exbii bitri ) ABEDFZCFADFZBEZCFKCFBEJLCABDGHKBCGI $.
  $}

  ${
    $d x ps $.  $d y ps $.  $d z ps $.
    $( Theorem 19.41 of [Margaris] p. 90 with 3 quantifiers.  (Contributed by
       NM, 30-Apr-1995.) $)
    19.41vvv $p |- ( E. x E. y E. z ( ph /\ ps ) <->
                     ( E. x E. y E. z ph /\ ps ) ) $=
      ( wa wex 19.41vv exbii 19.41v bitri ) ABFEGDGZCGAEGDGZBFZCGMCGBFLNCABDEHI
      MBCJK $.
  $}

  ${
    $d w ps $.  $d x ps $.  $d y ps $.  $d z ps $.
    $( Theorem 19.41 of [Margaris] p. 90 with 4 quantifiers.  (Contributed by
       FL, 14-Jul-2007.) $)
    19.41vvvv $p |- ( E. w E. x E. y E. z ( ph /\ ps ) <->
                     ( E. w E. x E. y E. z ph /\ ps ) ) $=
      ( wa wex 19.41vvv exbii 19.41v bitri ) ABGEHDHCHZFHAEHDHCHZBGZFHNFHBGMOFA
      BCDEIJNBFKL $.
  $}

  ${
    $d x ph $.
    $( Special case of Theorem 19.42 of [Margaris] p. 90.  (Contributed by NM,
       5-Aug-1993.) $)
    19.42v $p |- ( E. x ( ph /\ ps ) <-> ( ph /\ E. x ps ) ) $=
      ( ax-17 19.42h ) ABCACDE $.
  $}

  ${
    $d x y $.  $d x ps $.
    spvv.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Version of ~ spv with a disjoint variable condition.  (Contributed by
       BJ, 31-May-2019.) $)
    spvv $p |- ( A. x ph -> ps ) $=
      ( spv ) ABCDEF $.
  $}

  ${
    $d x y $.  $d x ps $.
    chvarvv.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    chvarvv.2 $e |- ph $.
    $( Version of ~ chvarv with a disjoint variable condition.  (Contributed by
       BJ, 31-May-2019.) $)
    chvarvv $p |- ps $=
      ( spvv mpg ) ABCABCDEGFH $.
  $}

  ${
    $d y ph $.
    $( Distribution of existential quantifiers.  (Contributed by NM,
       9-Mar-1995.) $)
    exdistr $p |- ( E. x E. y ( ph /\ ps ) <-> E. x ( ph /\ E. y ps ) ) $=
      ( wa wex 19.42v exbii ) ABEDFABDFECABDGH $.
  $}

  ${
    $d y ph $.  $d x ps $.  $d x y $.
    $( Distribute a pair of existential quantifiers (over disjoint variables)
       over a conjunction.  Combination of ~ 19.41v and ~ 19.42v .  For a
       version with fewer disjoint variable conditions but requiring more
       axioms, see ~ eeanv .  (Contributed by BJ, 30-Sep-2022.) $)
    exdistrv $p |- ( E. x E. y ( ph /\ ps ) <-> ( E. x ph /\ E. y ps ) ) $=
      ( wa wex exdistr 19.41v bitri ) ABEDFCFABDFZECFACFJEABCDGAJCHI $.
  $}

  ${
    $d x ph $.  $d y ph $.
    $( Theorem 19.42 of [Margaris] p. 90 with 2 quantifiers.  (Contributed by
       NM, 16-Mar-1995.) $)
    19.42vv $p |- ( E. x E. y ( ph /\ ps ) <-> ( ph /\ E. x E. y ps ) ) $=
      ( wa wex exdistr 19.42v bitri ) ABEDFCFABDFZECFAJCFEABCDGAJCHI $.
  $}

  ${
    $d x ph $.  $d y ph $.  $d z ph $.
    $( Theorem 19.42 of [Margaris] p. 90 with 3 quantifiers.  (Contributed by
       NM, 21-Sep-2011.) $)
    19.42vvv $p |- ( E. x E. y E. z ( ph /\ ps )
                       <-> ( ph /\ E. x E. y E. z ps ) ) $=
      ( wa wex 19.42vv exbii 19.42v bitri ) ABFEGDGZCGABEGDGZFZCGAMCGFLNCABDEHI
      AMCJK $.
  $}

  ${
    $d w ph $.  $d x ph $.  $d y ph $.  $d z ph $.
    $( Theorem 19.42 of [Margaris] p. 90 with 4 quantifiers.  (Contributed by
       Jim Kingdon, 23-Nov-2019.) $)
    19.42vvvv $p |- ( E. w E. x E. y E. z ( ph /\ ps ) <->
                     ( ph /\ E. w E. x E. y E. z ps ) ) $=
      ( wa wex 19.42vv 2exbii bitri ) ABGEHDHZCHFHABEHDHZGZCHFHAMCHFHGLNFCABDEI
      JAMFCIK $.
  $}

  ${
    $d y ph $.  $d z ph $.
    $( Distribution of existential quantifiers.  (Contributed by NM,
       17-Mar-1995.) $)
    exdistr2 $p |- ( E. x E. y E. z ( ph /\ ps ) <->
                   E. x ( ph /\ E. y E. z ps ) ) $=
      ( wa wex 19.42vv exbii ) ABFEGDGABEGDGFCABDEHI $.
  $}

  ${
    $d y ph $.  $d z ph $.  $d z ps $.
    $( Distribution of existential quantifiers.  (Contributed by NM,
       9-Mar-1995.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)
    3exdistr $p |- ( E. x E. y E. z ( ph /\ ps /\ ch ) <->
                E. x ( ph /\ E. y ( ps /\ E. z ch ) ) ) $=
      ( w3a wex wa 3anass 2exbii 19.42vv exdistr anbi2i 3bitri exbii ) ABCGZFHE
      HZABCFHIEHZIZDRABCIZIZFHEHAUAFHEHZITQUBEFABCJKAUAEFLUCSABCEFMNOP $.
  $}

  ${
    $d y ph $.  $d z ph $.  $d w ph $.  $d z ps $.  $d w ps $.  $d w ch $.
    $( Distribution of existential quantifiers.  (Contributed by NM,
       9-Mar-1995.) $)
    4exdistr $p |- ( E. x E. y E. z E. w ( ( ph /\ ps ) /\ ( ch /\ th ) ) <->
                E. x ( ph /\ E. y ( ps /\ E. z ( ch /\ E. w th ) ) ) ) $=
      ( wa wex anass exbii 19.42v anbi2i 3bitri bitri ) ABICDIZIZHJZGJZFJZABCDH
      JIZGJIZFJIZEUAAUCIZFJUDTUEFTABUBIZIZGJAUFGJZIUESUGGSABQIZIZHJZUGRUJHABQKL
      UKAUIHJZIABQHJZIZIUGAUIHMULUNABQHMNUNUFAUMUBBCDHMNNOPLAUFGMUHUCABUBGMNOLA
      UCFMPL $.
  $}

  ${
    $d y ph $.  $d x ps $.
    cbvalv.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Rule used to change bound variables, using implicit substitition.
       (Contributed by NM, 5-Aug-1993.) $)
    cbvalv $p |- ( A. x ph <-> A. y ps ) $=
      ( ax-17 cbvalh ) ABCDADFBCFEG $.

    $( Rule used to change bound variables, using implicit substitition.
       (Contributed by NM, 5-Aug-1993.) $)
    cbvexv $p |- ( E. x ph <-> E. y ps ) $=
      ( ax-17 cbvexh ) ABCDADFBCFEG $.
  $}

  ${
    $d x y $.  $d x ps $.  $d y ph $.
    cbvalvw.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Change bound variable.  See ~ cbvalv for a version with fewer disjoint
       variable conditions.  (Contributed by NM, 9-Apr-2017.)  Avoid ~ ax-7 .
       (Revised by GG, 25-Aug-2024.) $)
    cbvalvw $p |- ( A. x ph <-> A. y ps ) $=
      ( wal spv alrimiv weq wb equcoms biimprd spimv impbii ) ACFZBDFZOBDABCDEG
      HPACBADCDCIABABJCDEKLMHN $.
    $( $j usage 'cbvalvw' avoids 'ax-7'; $)

    $( Change bound variable.  See ~ cbvexv for a version with fewer disjoint
       variable conditions.  (Contributed by NM, 19-Apr-2017.)  Avoid ~ ax-7 .
       (Revised by GG, 25-Aug-2024.) $)
    cbvexvw $p |- ( E. x ph <-> E. y ps ) $=
      ( wex wi weq biimpd equcoms spimev exlimiv biimprd impbii ) ACFZBDFZAPCAB
      DCABGCDCDHZABEIJKLBODBACDQABEMKLN $.
    $( $j usage 'cbvexvw' avoids 'ax-7'; $)
  $}

  ${
    $d y x $.  $d y z $.  $d w x $.  $d w z $.
    cbval2.1 $e |- F/ z ph $.
    cbval2.2 $e |- F/ w ph $.
    cbval2.3 $e |- F/ x ps $.
    cbval2.4 $e |- F/ y ps $.
    cbval2.5 $e |- ( ( x = z /\ y = w ) -> ( ph <-> ps ) ) $.
    $( Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 22-Dec-2003.)  (Revised by Mario Carneiro,
       6-Oct-2016.)  (Proof shortened by Wolf Lammen, 22-Apr-2018.) $)
    cbval2 $p |- ( A. x A. y ph <-> A. z A. w ps ) $=
      ( wal nfal weq wi nfv nfim wb cbval 19.21v pm5.74d 3bitr3i pm5.74ri
      expcom ) ADLZBFLZCEAEDGMBCFIMCENZUEUFUGAOZDLUGBOZFLUGUEOUGUFOUHUIDFUGAFUG
      FPHQUGBDUGDPJQDFNZUGABUGUJABRKUDUASUGADTUGBFTUBUCS $.

    $( Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 14-Sep-2003.)  (Revised by Mario Carneiro,
       6-Oct-2016.) $)
    cbvex2 $p |- ( E. x E. y ph <-> E. z E. w ps ) $=
      ( wex nfex weq wb wa nfv nfan cbvex 19.42v wi expcom pm5.32d pm5.32 mpbir
      3bitr3i ) ADLZBFLZCEAEDGMBCFIMCENZUGUHOUAUIUGPZUIUHPZOUIAPZDLUIBPZFLUJUKU
      LUMDFUIAFUIFQHRUIBDUIDQJRDFNZUIABUIUNABOKUBUCSUIADTUIBFTUFUIUGUHUDUES $.
  $}

  ${
    $d z w ph $.  $d x y ps $.  $d x w $.  $d z y $.
    cbval2v.1 $e |- ( ( x = z /\ y = w ) -> ( ph <-> ps ) ) $.
    $( Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 4-Feb-2005.) $)
    cbval2v $p |- ( A. x A. y ph <-> A. z A. w ps ) $=
      ( nfv cbval2 ) ABCDEFAEHAFHBCHBDHGI $.

    $( Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 26-Jul-1995.) $)
    cbvex2v $p |- ( E. x E. y ph <-> E. z E. w ps ) $=
      ( nfv cbvex2 ) ABCDEFAEHAFHBCHBDHGI $.
  $}

  ${
    $d x ph $.  $d x ch $.
    cbvald.1 $e |- F/ y ph $.
    cbvald.2 $e |- ( ph -> F/ y ps ) $.
    cbvald.3 $e |- ( ph -> ( x = y -> ( ps <-> ch ) ) ) $.
    $( Deduction used to change bound variables, using implicit substitution,
       particularly useful in conjunction with ~ dvelim .  (Contributed by NM,
       2-Jan-2002.)  (Revised by Mario Carneiro, 6-Oct-2016.)  (Revised by Wolf
       Lammen, 13-May-2018.) $)
    cbvald $p |- ( ph -> ( A. x ps <-> A. y ch ) ) $=
      ( nfv wnf a1i cbv2 ) ABCDEADIFGCDJACDIKHL $.
  $}

  ${
    $d x ph $.  $d x ch $.
    cbvexdh.1 $e |- ( ph -> A. y ph ) $.
    cbvexdh.2 $e |- ( ph -> ( ps -> A. y ps ) ) $.
    cbvexdh.3 $e |- ( ph -> ( x = y -> ( ps <-> ch ) ) ) $.
    $( Deduction used to change bound variables, using implicit substitition,
       particularly useful in conjunction with ~ dvelim .  (Contributed by NM,
       2-Jan-2002.)  (Proof rewritten by Jim Kingdon, 30-Dec-2017.) $)
    cbvexdh $p |- ( ph -> ( E. x ps <-> E. y ch ) ) $=
      ( wex ax-17 cv wceq wa wb wi equsexd simpr eximi biimtrrdi wal bicom1 syl
      hbex equcomi imim12i exlimdh eximdh 19.12 syl6 a1i exlimd2 impbid ) ABDIZ
      CEIZABUNDADJZCDECDJZUCABEKZDKZLZCMZEIUNACBEDFGAURUQLZBCNZOUSCBNZOHUSVAVBV
      CEDUDBCUAUEUBPUTCEUSCQRSUFACUMEFAUMBETZDIUMETABVDDUOGUGBDEUHUIACVABMZDIUM
      ABCDEUOCCDTOAUPUJHPVEBDVABQRSUKUL $.
  $}

  ${
    $d x ph $.  $d x ch $.
    cbvexd.1 $e |- F/ y ph $.
    cbvexd.2 $e |- ( ph -> F/ y ps ) $.
    cbvexd.3 $e |- ( ph -> ( x = y -> ( ps <-> ch ) ) ) $.
    $( Deduction used to change bound variables, using implicit substitution,
       particularly useful in conjunction with ~ dvelim .  (Contributed by NM,
       2-Jan-2002.)  (Revised by Mario Carneiro, 6-Oct-2016.)  (Proof rewritten
       by Jim Kingdon, 10-Jun-2018.) $)
    cbvexd $p |- ( ph -> ( E. x ps <-> E. y ch ) ) $=
      ( nfri nfrd cbvexdh ) ABCDEAEFIABEGJHK $.
  $}

  ${
    $d ps y $.  $d ch x $.  $d ph x $.  $d ph y $.
    cbvaldva.1 $e |- ( ( ph /\ x = y ) -> ( ps <-> ch ) ) $.
    $( Rule used to change the bound variable in a universal quantifier with
       implicit substitution.  Deduction form.  (Contributed by David Moews,
       1-May-2017.) $)
    cbvaldva $p |- ( ph -> ( A. x ps <-> A. y ch ) ) $=
      ( nfv nfvd weq wb ex cbvald ) ABCDEAEGABEHADEIBCJFKL $.

    $( Rule used to change the bound variable in an existential quantifier with
       implicit substitution.  Deduction form.  (Contributed by David Moews,
       1-May-2017.) $)
    cbvexdva $p |- ( ph -> ( E. x ps <-> E. y ch ) ) $=
      ( nfv nfvd weq wb ex cbvexd ) ABCDEAEGABEHADEIBCJFKL $.
  $}

  ${
    $d ps y $.  $d ch x $.  $d ph x y $.
    cbvaldvaw.1 $e |- ( ( ph /\ x = y ) -> ( ps <-> ch ) ) $.
    $( Rule used to change the bound variable in a universal quantifier with
       implicit substitution.  Deduction form.  Version of ~ cbvaldva with a
       disjoint variable condition.  (Contributed by David Moews, 1-May-2017.)
       (Revised by GG, 10-Jan-2024.)  (Revised by Wolf Lammen, 10-Feb-2024.) $)
    cbvaldvaw $p |- ( ph -> ( A. x ps <-> A. y ch ) ) $=
      ( wal wi weq wb ancoms pm5.74da cbvalvw 19.21v 3bitr3i pm5.74ri ) ABDGZCE
      GZABHZDGACHZEGAQHARHSTDEDEIZABCAUABCJFKLMABDNACENOP $.

    $( Rule used to change the bound variable in an existential quantifier with
       implicit substitution.  Deduction form.  Version of ~ cbvexdva with a
       disjoint variable condition.  (Contributed by David Moews, 1-May-2017.)
       (Revised by GG, 10-Jan-2024.)  (Revised by Wolf Lammen, 10-Feb-2024.) $)
    cbvexdvaw $p |- ( ph -> ( E. x ps <-> E. y ch ) ) $=
      ( cbvexdva ) ABCDEFG $.
  $}

  ${
    $d w z ph $.  $d x y ps $.  $d w x y z $.
    cbval2vw.1 $e |- ( ( x = z /\ y = w ) -> ( ph <-> ps ) ) $.
    $( Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 4-Feb-2005.)  (Revised by GG, 10-Jan-2024.) $)
    cbval2vw $p |- ( A. x A. y ph <-> A. z A. w ps ) $=
      ( wal weq cbvaldvaw cbvalvw ) ADHBFHCECEIABDFGJK $.

    $( Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 26-Jul-1995.)  (Revised by GG, 10-Jan-2024.) $)
    cbvex2vw $p |- ( E. x E. y ph <-> E. z E. w ps ) $=
      ( wex weq cbvexdvaw cbvexvw ) ADHBFHCECEIABDFGJK $.
  $}

  ${
    $v f $.
    $v g $.
    $( Define temporary individual variables. $)
    cbvex4v.vf $f setvar f $.
    cbvex4v.vg $f setvar g $.
    $d w z ch $.  $d u v ph $.  $d x y ps $.  $d f g ps $.  $d f w $.
    $d g z $.  $d u v w z $.  $d u w x z $.  $d v w y z $.  $d w x y z $.
    cbvex4v.1 $e |- ( ( x = v /\ y = u ) -> ( ph <-> ps ) ) $.
    cbvex4v.2 $e |- ( ( z = f /\ w = g ) -> ( ps <-> ch ) ) $.
    $( Rule used to change bound variables, using implicit substitition.
       (Contributed by NM, 26-Jul-1995.) $)
    cbvex4v $p |- ( E. x E. y E. z E. w ph <-> E. v E. u E. f E. g ch ) $=
      ( wex weq wa 2exbidv cbvex2v 2exbii bitri ) AGNFNZENDNBGNFNZINHNCKNJNZINH
      NUAUBDEHIDHOEIOPABFGLQRUBUCHIBCFGJKMRST $.
  $}

  ${
    eean.1 $e |- F/ y ph $.
    eean.2 $e |- F/ x ps $.
    $( Rearrange existential quantifiers.  (Contributed by NM, 27-Oct-2010.)
       (Revised by Mario Carneiro, 6-Oct-2016.) $)
    eean $p |- ( E. x E. y ( ph /\ ps ) <-> ( E. x ph /\ E. y ps ) ) $=
      ( wa wex 19.42 exbii nfex 19.41 bitri ) ABGDHZCHABDHZGZCHACHOGNPCABDEIJAO
      CBCDFKLM $.
  $}

  ${
    $d y ph $.  $d x ps $.
    $( Rearrange existential quantifiers.  (Contributed by NM, 26-Jul-1995.) $)
    eeanv $p |- ( E. x E. y ( ph /\ ps ) <-> ( E. x ph /\ E. y ps ) ) $=
      ( nfv eean ) ABCDADEBCEF $.
  $}

  ${
    $d y ph $.  $d z ph $.  $d x z ps $.  $d x y ch $.
    $( Rearrange existential quantifiers.  (Contributed by NM, 26-Jul-1995.)
       (Proof shortened by Andrew Salmon, 25-May-2011.) $)
    eeeanv $p |- ( E. x E. y E. z ( ph /\ ps /\ ch ) <->
                 ( E. x ph /\ E. y ps /\ E. z ch ) ) $=
      ( w3a wex wa df-3an 3exbii eeanv exbii anbi1i 19.41v 3bitr4i 3bitri ) ABC
      GZFHEHDHABIZCIZFHEHZDHSEHZCFHZIZDHZADHZBEHZUCGZRTDEFABCJKUAUDDSCEFLMUBDHZ
      UCIUFUGIZUCIUEUHUIUJUCABDELNUBUCDOUFUGUCJPQ $.
  $}

  ${
    $d z ph $.  $d w ph $.  $d x ps $.  $d y ps $.  $d y z $.  $d w x $.
    $( Rearrange existential quantifiers.  (Contributed by NM, 31-Jul-1995.) $)
    ee4anv $p |- ( E. x E. y E. z E. w ( ph /\ ps ) <->
                  ( E. x E. y ph /\ E. z E. w ps ) ) $=
      ( wa wex excom exbii eeanv 2exbii 3bitri ) ABGFHZEHDHZCHNDHZEHZCHADHZBFHZ
      GZEHCHRCHSEHGOQCNDEIJPTCEABDFKLRSCEKM $.
  $}

  ${
    $v s $.
    $( Define a temporary individual variable. $)
    ee8anv.vs $f setvar s $.

    $d v ph $.  $d u ph $.  $d t ph $.  $d s ph $.  $d x ps $.  $d y ps $.
    $d z ps $.  $d w ps $.  $d s x $.  $d s y $.  $d s z $.  $d t w $.
    $d t x $.  $d t y $.  $d u w $.  $d u x $.  $d u z $.  $d v w $.  $d v y $.
    $d v z $.
    $( Rearrange existential quantifiers.  (Contributed by Jim Kingdon,
       23-Nov-2019.) $)
    ee8anv $p |- ( E. x E. y E. z E. w E. v E. u E. t E. s ( ph /\ ps ) <->
                  ( E. x E. y E. z E. w ph /\ E. v E. u E. t E. s ps ) ) $=
      ( wa wex exrot4 2exbii ee4anv 3bitri ) ABKJLILZHLGLFLELZDLCLQFLELZHLGLZDL
      CLAFLELZBJLILZKZHLGLZDLCLUADLCLUBHLGLKRTCDQEFGHMNTUDCDSUCGHABEFIJONNUAUBC
      DGHOP $.
  $}

  ${
    $d x ph $.
    nexdv.1 $e |- ( ph -> -. ps ) $.
    $( Deduction for generalization rule for negated wff.  (Contributed by NM,
       5-Aug-1993.) $)
    nexdv $p |- ( ph -> -. E. x ps ) $=
      ( ax-17 nexd ) ABCACEDF $.
  $}

  ${
    $d x ps $.
    chv.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    chv.2 $e |- ph $.
    $( Implicit substitution of ` y ` for ` x ` into a theorem.  (Contributed
       by NM, 20-Apr-1994.) $)
    chvarv $p |- ps $=
      ( spv mpg ) ABCABCDEGFH $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  More substitution theorems
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$( The theorems in this section make use of the $d statement. $)

  ${
    $d x y $.
    $( ` x ` is not free in ` [ y / x ] ph ` when ` x ` and ` y ` are distinct.
       (Contributed by NM, 5-Aug-1993.)  (Proof by Jim Kingdon, 16-Dec-2017.)
       (New usage is discouraged.) $)
    hbs1 $p |- ( [ y / x ] ph -> A. x [ y / x ] ph ) $=
      ( wsb weq wi wal sb6 ax-ial hbxfrbi ) ABCDBCEAFZBGBABCHKBIJ $.

    $( ` x ` is not free in ` [ y / x ] ph ` when ` x ` and ` y ` are distinct.
       (Contributed by Mario Carneiro, 11-Aug-2016.) $)
    nfs1v $p |- F/ x [ y / x ] ph $=
      ( wsb hbs1 nfi ) ABCDBABCEF $.
  $}

  ${
    $d y ph $.
    $( Two ways of expressing " ` x ` is (effectively) not free in ` ph ` ."
       (Contributed by NM, 29-May-2009.) $)
    sbhb $p |- ( ( ph -> A. x ph ) <-> A. y ( ph -> [ y / x ] ph ) ) $=
      ( wal wi wsb ax-17 sb8h imbi2i 19.21v bitr4i ) AABDZEAABCFZCDZEAMECDLNAAB
      CACGHIAMCJK $.
  $}

  ${
    $d x z $.  $d y z $.
    hbsbv.1 $e |- ( ph -> A. z ph ) $.
    $( This is a version of ~ hbsb with an extra distinct variable constraint,
       on ` z ` and ` x ` .  (Contributed by Jim Kingdon, 25-Dec-2017.) $)
    hbsbv $p |- ( [ y / x ] ph -> A. z [ y / x ] ph ) $=
      ( wsb weq wi wa wex df-sb ax-17 hbim hban hbex hbxfrbi ) ABCFBCGZAHZQAIZB
      JZIDABCKRTDQADQDLZEMSDBQADUAENONP $.
  $}

  ${
    $d x y $.  $d y z $.
    nfsbxy.1 $e |- F/ z ph $.
    $( Similar to ~ hbsb but with an extra distinct variable constraint, on
       ` x ` and ` y ` .  (Contributed by Jim Kingdon, 19-Mar-2018.) $)
    nfsbxy $p |- F/ z [ y / x ] ph $=
      ( weq wal wi wo wsb wnf ax-bndl nfs1v drsb1 drnf2 mpbii a16nf df-nf albii
      jaoi wa wex sb5 nfa1 sp a1i nfand nfexd nfxfrd sylbir ax-mp ) DBFDGZDCFDG
      ZBCFZUNDGHDGZBGZIZIABCJZDKZBCDLULUSUQULADCJZDKUSADCMUTURDBDADBCNOPUMUSUPU
      RDCDQUPUNDKZBGZUSVAUOBUNDRSURUNAUAZBUBVBDABCUCVBVCDBVABUDVBUNADVABUEADKVB
      EUFUGUHUIUJTTUK $.
  $}

  ${
    $d x y $.  $d y z $.
    $( Closed form of ~ nfsbxy .  (Contributed by Jim Kingdon, 9-May-2018.) $)
    nfsbxyt $p |- ( A. x F/ z ph -> F/ z [ y / x ] ph ) $=
      ( weq wal wi wo wnf wsb ax-bndl nfs1v drsb1 drnf2 mpbii a1d wa nfa1 jaoi
      sp a16nf df-nf albii wex sb5 nfan adantr adantl nfand nfexd nfxfrd sylbir
      ex ax-mp ) DBEDFZDCEDFZBCEZUQDFGDFZBFZHZHADIZBFZABCJZDIZGZBCDKUOVEUTUOVDV
      BUOADCJZDIVDADCLVFVCDBDADBCMNOPUPVEUSUPVDVBVCDCDUAPUSUQDIZBFZVEVGURBUQDUB
      UCVHVBVDVCUQAQZBUDVHVBQZDABCUEVJVIDBVHVBBVGBRVABRUFVJUQADVHVGVBVGBTUGVBVA
      VHVABTUHUIUJUKUMULSSUN $.
  $}

  ${
    $d x z $.  $d y z $.
    sbco2vlem.1 $e |- ( ph -> A. z ph ) $.
    $( This is a version of ~ sbco2 where ` z ` is distinct from ` x ` and from
       ` y ` .  It is a lemma on the way to proving ~ sbco2v which only
       requires that ` z ` and ` x ` be distinct.  (Contributed by Jim Kingdon,
       25-Dec-2017.)  Remove one disjoint variable condition.  (Revised by Jim
       Kingdon, 3-Feb-2018.) $)
    sbco2vlem $p |- ( [ y / z ] [ z / x ] ph <-> [ y / x ] ph ) $=
      ( wsb hbsbv sbequ sbieh ) ABDFABCFDCABCDEGADCBHI $.
  $}

  ${
    $d x z w $.  $d y w $.  $d z w $.  $d ph w $.
    sbco2vh.1 $e |- ( ph -> A. z ph ) $.
    $( This is a version of ~ sbco2 where ` z ` is distinct from ` x ` .
       (Contributed by Jim Kingdon, 12-Feb-2018.) $)
    sbco2vh $p |- ( [ y / z ] [ z / x ] ph <-> [ y / x ] ph ) $=
      ( vw wsb sbco2vlem sbbii ax-17 3bitr3i ) ABDGZDFGZFCGABFGZFCGLDCGABCGMNFC
      ABFDEHILDCFLFJHABCFAFJHK $.
  $}

  ${
    $d w y z $.  $d w ph $.  $d w x $.
    nfsb.1 $e |- F/ z ph $.
    $( If ` z ` is not free in ` ph ` , it is not free in ` [ y / x ] ph ` when
       ` y ` and ` z ` are distinct.  (Contributed by Mario Carneiro,
       11-Aug-2016.)  (Proof rewritten by Jim Kingdon, 19-Mar-2018.) $)
    nfsb $p |- F/ z [ y / x ] ph $=
      ( vw wsb wnf nfsbxy ax-17 sbco2vh nfbii mpbi ) ABFGZFCGZDHABCGZDHNFCDABFD
      EIIOPDABCFAFJKLM $.
  $}

  ${
    $d x z $.  $d y z $.
    nfsbv.nf $e |- F/ z ph $.
    $( If ` z ` is not free in ` ph ` , it is not free in ` [ y / x ] ph ` when
       ` z ` is distinct from ` x ` and ` y ` .  Version of ~ nfsb requiring
       more disjoint variables.  (Contributed by Wolf Lammen, 7-Feb-2023.)
       Remove disjoint variable condition on ` x , y ` .  (Revised by Steven
       Nguyen, 13-Aug-2023.)  Reduce axiom usage.  (Revised by GG,
       25-Aug-2024.) $)
    nfsbv $p |- F/ z [ y / x ] ph $=
      ( wsb weq wi wa wex df-sb nfv nfim nfan nfex nfxfr ) ABCFBCGZAHZQAIZBJZID
      ABCKRTDQADQDLZEMSDBQADUAENONP $.
    $( $j usage 'nfsbv' avoids 'ax-io' 'ax-8' 'ax-10' 'ax-11' 'ax-i12'
       'ax-bndl' 'ax-i9'; $)
  $}

  ${
    $d x z $.  $d y z $.
    sbco2v.1 $e |- F/ z ph $.
    $( Version of ~ sbco2 with disjoint variable conditions.  (Contributed by
       Wolf Lammen, 29-Apr-2023.) $)
    sbco2v $p |- ( [ y / z ] [ z / x ] ph <-> [ y / x ] ph ) $=
      ( wsb nfsbv sbequ sbiev ) ABDFABCFDCABCDEGADCBHI $.
  $}

  ${
    $d y z $.
    hbsb.1 $e |- ( ph -> A. z ph ) $.
    $( If ` z ` is not free in ` ph ` , it is not free in ` [ y / x ] ph ` when
       ` y ` and ` z ` are distinct.  (Contributed by NM, 12-Aug-1993.)  (Proof
       rewritten by Jim Kingdon, 22-Mar-2018.) $)
    hbsb $p |- ( [ y / x ] ph -> A. z [ y / x ] ph ) $=
      ( wsb nfi nfsb nfri ) ABCFDABCDADEGHI $.
  $}

  ${
    $d x z $.  $d x y $.
    $( Lemma for ~ equsb3 .  (Contributed by NM, 4-Dec-2005.)  (Proof shortened
       by Andrew Salmon, 14-Jun-2011.) $)
    equsb3lem $p |- ( [ y / x ] x = z <-> y = z ) $=
      ( cv wceq ax-17 equequ1 sbieh ) ADCDZEBDIEZABJAFABCGH $.
  $}

  ${
    $d w x z $.  $d w y $.
    $( Substitution applied to an atomic wff.  (Contributed by Raph Levien and
       FL, 4-Dec-2005.) $)
    equsb3 $p |- ( [ y / x ] x = z <-> y = z ) $=
      ( vw weq wsb equsb3lem sbbii ax-17 sbco2vh 3bitr3i ) ACEZADFZDBFDCEZDBFLA
      BFBCEMNDBADCGHLABDLDIJDBCGK $.
  $}

  ${
    $d z ph $.  $d z ps $.  $d z x $.  $d z y $.

    $( Negation inside and outside of substitution are equivalent.
       (Contributed by NM, 5-Aug-1993.)  (Proof rewritten by Jim Kingdon,
       3-Feb-2018.) $)
    sbn $p |- ( [ y / x ] -. ph <-> -. [ y / x ] ph ) $=
      ( vz wn wsb sbnv sbbii bitri ax-17 hbn sbco2vh notbii 3bitr3i ) AEZBDFZDC
      FZABDFZDCFZEZOBCFABCFZEQREZDCFTPUBDCABDGHRDCGIOBCDADADJZKLSUAABCDUCLMN $.

    $( Implication inside and outside of substitution are equivalent.
       (Contributed by NM, 5-Aug-1993.)  (Proof rewritten by Jim Kingdon,
       3-Feb-2018.) $)
    sbim $p |- ( [ y / x ] ( ph -> ps ) <->
        ( [ y / x ] ph -> [ y / x ] ps ) ) $=
      ( vz wi wsb sbimv sbbii bitri ax-17 sbco2vh imbi12i 3bitr3i ) ABFZCEGZEDG
      ZACEGZEDGZBCEGZEDGZFZOCDGACDGZBCDGZFQRTFZEDGUBPUEEDABCEHIRTEDHJOCDEOEKLSU
      CUAUDACDEAEKLBCDEBEKLMN $.

    $( Logical OR inside and outside of substitution are equivalent.
       (Contributed by NM, 29-Sep-2002.)  (Proof rewritten by Jim Kingdon,
       3-Feb-2018.) $)
    sbor $p |- ( [ y / x ] ( ph \/ ps ) <->
        ( [ y / x ] ph \/ [ y / x ] ps ) ) $=
      ( vz wo wsb sborv sbbii bitri ax-17 sbco2vh orbi12i 3bitr3i ) ABFZCEGZEDG
      ZACEGZEDGZBCEGZEDGZFZOCDGACDGZBCDGZFQRTFZEDGUBPUEEDABCEHIRTEDHJOCDEOEKLSU
      CUAUDACDEAEKLBCDEBEKLMN $.

    $( Conjunction inside and outside of a substitution are equivalent.
       (Contributed by NM, 5-Aug-1993.)  (Proof rewritten by Jim Kingdon,
       3-Feb-2018.) $)
    sban $p |- ( [ y / x ] ( ph /\ ps ) <->
        ( [ y / x ] ph /\ [ y / x ] ps ) ) $=
      ( vz wa wsb sbanv sbbii bitri ax-17 sbco2vh anbi12i 3bitr3i ) ABFZCEGZEDG
      ZACEGZEDGZBCEGZEDGZFZOCDGACDGZBCDGZFQRTFZEDGUBPUEEDABCEHIRTEDHJOCDEOEKLSU
      CUAUDACDEAEKLBCDEBEKLMN $.
  $}

  ${
    sbrim.1 $e |- ( ph -> A. x ph ) $.
    $( Substitution with a variable not free in antecedent affects only the
       consequent.  (Contributed by NM, 5-Aug-1993.) $)
    sbrim $p |- ( [ y / x ] ( ph -> ps ) <-> ( ph -> [ y / x ] ps ) ) $=
      ( wi wsb sbim sbh imbi1i bitri ) ABFCDGACDGZBCDGZFAMFABCDHLAMACDEIJK $.
  $}

  ${
    sblim.1 $e |- F/ x ps $.
    $( Substitution with a variable not free in consequent affects only the
       antecedent.  (Contributed by NM, 14-Nov-2013.)  (Revised by Mario
       Carneiro, 4-Oct-2016.) $)
    sblim $p |- ( [ y / x ] ( ph -> ps ) <-> ( [ y / x ] ph -> ps ) ) $=
      ( wi wsb sbim sbf imbi2i bitri ) ABFCDGACDGZBCDGZFLBFABCDHMBLBCDEIJK $.
  $}

  $( Conjunction inside and outside of a substitution are equivalent.
     (Contributed by NM, 14-Dec-2006.) $)
  sb3an $p |- ( [ y / x ] ( ph /\ ps /\ ch ) <->
              ( [ y / x ] ph /\ [ y / x ] ps /\ [ y / x ] ch ) ) $=
    ( w3a wsb wa df-3an sbbii sban anbi1i bitr4i 3bitri ) ABCFZDEGABHZCHZDEGPDE
    GZCDEGZHZADEGZBDEGZSFZOQDEABCIJPCDEKTUAUBHZSHUCRUDSABDEKLUAUBSIMN $.

  $( Equivalence inside and outside of a substitution are equivalent.
     (Contributed by NM, 5-Aug-1993.) $)
  sbbi $p |- ( [ y / x ] ( ph <-> ps )
     <-> ( [ y / x ] ph <-> [ y / x ] ps ) ) $=
    ( wb wsb wi wa dfbi2 sbbii sbim anbi12i sban 3bitr4i bitri ) ABEZCDFABGZBAG
    ZHZCDFZACDFZBCDFZEZPSCDABIJQCDFZRCDFZHUAUBGZUBUAGZHTUCUDUFUEUGABCDKBACDKLQR
    CDMUAUBINO $.

  ${
    sblbis.1 $e |- ( [ y / x ] ph <-> ps ) $.
    $( Introduce left biconditional inside of a substitution.  (Contributed by
       NM, 19-Aug-1993.) $)
    sblbis $p |- ( [ y / x ] ( ch <-> ph ) <-> ( [ y / x ] ch <-> ps ) ) $=
      ( wb wsb sbbi bibi2i bitri ) CAGDEHCDEHZADEHZGLBGCADEIMBLFJK $.
  $}

  ${
    sbrbis.1 $e |- ( [ y / x ] ph <-> ps ) $.
    $( Introduce right biconditional inside of a substitution.  (Contributed by
       NM, 18-Aug-1993.) $)
    sbrbis $p |- ( [ y / x ] ( ph <-> ch ) <-> ( ps <-> [ y / x ] ch ) ) $=
      ( wb wsb sbbi bibi1i bitri ) ACGDEHADEHZCDEHZGBMGACDEILBMFJK $.
  $}

  ${
    sbrbif.1 $e |- ( ch -> A. x ch ) $.
    sbrbif.2 $e |- ( [ y / x ] ph <-> ps ) $.
    $( Introduce right biconditional inside of a substitution.  (Contributed by
       NM, 18-Aug-1993.) $)
    sbrbif $p |- ( [ y / x ] ( ph <-> ch ) <-> ( ps <-> ch ) ) $=
      ( wb wsb sbrbis sbh bibi2i bitri ) ACHDEIBCDEIZHBCHABCDEGJNCBCDEFKLM $.
  $}

  ${
    $d y z $.
    sbco2yz.1 $e |- F/ z ph $.
    $( This is a version of ~ sbco2 where ` z ` is distinct from ` y ` .  It is
       a lemma on the way to proving ~ sbco2 which has no distinct variable
       constraints.  (Contributed by Jim Kingdon, 19-Mar-2018.) $)
    sbco2yz $p |- ( [ y / z ] [ z / x ] ph <-> [ y / x ] ph ) $=
      ( wsb nfsb nfri sbequ sbieh ) ABDFABCFZDCKDABCDEGHADCBIJ $.
  $}

  ${
    $d w z $.  $d w x $.  $d w y $.  $d ph w $.
    sbco2h.1 $e |- ( ph -> A. z ph ) $.
    $( A composition law for substitution.  (Contributed by NM, 30-Jun-1994.)
       (Proof rewritten by Jim Kingdon, 19-Mar-2018.) $)
    sbco2h $p |- ( [ y / z ] [ z / x ] ph <-> [ y / x ] ph ) $=
      ( vw wsb nfi sbco2yz sbbii nfv 3bitr3i ) ABDGZDFGZFCGABFGZFCGMDCGABCGNOFC
      ABFDADEHIJMDCFMFKIABCFAFKIL $.
  $}

  ${
    sbco2.1 $e |- F/ z ph $.
    $( A composition law for substitution.  (Contributed by NM, 30-Jun-1994.)
       (Revised by Mario Carneiro, 6-Oct-2016.) $)
    sbco2 $p |- ( [ y / z ] [ z / x ] ph <-> [ y / x ] ph ) $=
      ( nfri sbco2h ) ABCDADEFG $.
  $}

  ${
    sbco2d.1 $e |- ( ph -> A. x ph ) $.
    sbco2d.2 $e |- ( ph -> A. z ph ) $.
    sbco2d.3 $e |- ( ph -> ( ps -> A. z ps ) ) $.
    $( A composition law for substitution.  (Contributed by NM, 5-Aug-1993.) $)
    sbco2d $p |- ( ph -> ( [ y / z ] [ z / x ] ps <-> [ y / x ] ps ) ) $=
      ( wsb wi hbim1 sbco2h sbrim sbbii bitri 3bitr3i pm5.74ri ) ABCEIZEDIZBCDI
      ZABJZCEIZEDIZUACDIASJZATJUACDEABEGHKLUCARJZEDIUDUBUEEDABCEFMNAREDGMOABCDF
      MPQ $.
  $}

  ${
    $d x z $.
    sbco2vd.1 $e |- ( ph -> A. x ph ) $.
    sbco2vd.2 $e |- ( ph -> A. z ph ) $.
    sbco2vd.3 $e |- ( ph -> ( ps -> A. z ps ) ) $.
    $( Version of ~ sbco2d with a distinct variable constraint between ` x `
       and ` z ` .  (Contributed by Jim Kingdon, 19-Feb-2018.) $)
    sbco2vd $p |- ( ph -> ( [ y / z ] [ z / x ] ps <-> [ y / x ] ps ) ) $=
      ( wsb wi hbim1 sbco2vh sbrim sbbii bitri 3bitr3i pm5.74ri ) ABCEIZEDIZBCD
      IZABJZCEIZEDIZUACDIASJZATJUACDEABEGHKLUCARJZEDIUDUBUEEDABCEFMNAREDGMOABCD
      FMPQ $.
  $}

  $( A composition law for substitution.  (Contributed by NM, 5-Aug-1993.) $)
  sbco $p |- ( [ y / x ] [ x / y ] ph <-> [ y / x ] ph ) $=
    ( wsb wb weq equsb2 sbequ12 bicomd sbimi ax-mp sbbi mpbi ) ACBDZAEZBCDZNBCD
    ABCDECBFZBCDPBCGQOBCQANACBHIJKNABCLM $.

  ${
    $d x y $.
    $( Version of ~ sbco3 with a distinct variable constraint between ` x ` and
       ` y ` .  (Contributed by Jim Kingdon, 19-Feb-2018.) $)
    sbco3v $p |- ( [ z / y ] [ y / x ] ph <-> [ z / x ] [ x / y ] ph ) $=
      ( wsb nfs1v nfri sbco2vh sbco sbbii bitr3i ) ABCEZCDELCBEZBDEACBEZBDELCDB
      LBABCFGHMNBDACBIJK $.
  $}

  $( Relationship between composition and commutativity for substitution.
     (Contributed by Jim Kingdon, 28-Feb-2018.) $)
  sbcocom $p |- ( [ z / y ] [ y / x ] ph <-> [ z / y ] [ z / x ] ph ) $=
    ( wsb wb weq equsb1 sbequ sbimi ax-mp sbbi mpbi ) ABCEZABDEZFZCDEZNCDEOCDEF
    CDGZCDEQCDHRPCDACDBIJKNOCDLM $.

  ${
    $d x z $.
    $( Version of ~ sbcom with a distinct variable constraint between ` x ` and
       ` z ` .  (Contributed by Jim Kingdon, 28-Feb-2018.) $)
    sbcomv $p |- ( [ y / z ] [ y / x ] ph <-> [ y / x ] [ y / z ] ph ) $=
      ( wsb sbco3v sbcocom 3bitr3i ) ABDEDCEADBEBCEABCEDCEADCEBCEABDCFABDCGADBC
      GH $.
  $}

  ${
    $d x y $.  $d y z $.
    $( Version of ~ sbcom with distinct variable constraints between ` x ` and
       ` y ` , and ` y ` and ` z ` .  (Contributed by Jim Kingdon,
       21-Mar-2018.) $)
    sbcomxyyz $p |- ( [ y / z ] [ y / x ] ph <-> [ y / x ] [ y / z ] ph ) $=
      ( weq wal wi wo wsb ax-ial drsb1 sbbidh bitr3d sbequ12 sps wnf nfs1v nfrd
      wb a1i ax-bndl hbae df-nf albii nfsb nfr wa nfnf1 nfa1 nfan nfri sylan9bb
      ex adantl sbiedh syld bicomd sylbir jaoi ax-mp ) DBEZDFZDCEZDFZBCEZVEDFZG
      DFZBFZHZHABCIZDCIZADCIZBCIZSZBCDUAVBVNVIVBVLDCIVKVMVBVLVJDCVADJADBCKLVLDB
      CKMVDVNVHVDVJVKVMVCVJVKSDVJDCNZOVDAVLBCDCBUBVCAVLSDADCNOLMVHVEDPZBFZVNVPV
      GBVEDUCUDVQVMVKVQVLVKBCVPBJVQVKBVKBPVQVJDCBABCQUETRVPVEVLVKSZGBVPVEVFVRVE
      DUFVPVFVRVPVFUGZAVKDCVSDVPVFDVEDUHVEDUIUJUKVSVKDVKDPVSVJDCQTRVFVCAVKSZGZV
      PVEWADVEVCVTVEAVJVCVKABCNVOULUMOUNUOUMUPOUOUQURUSUSUT $.
  $}

  ${
    $d x z $.  $d y z $.
    $( Version of ~ sbco3 with distinct variable constraints between ` x ` and
       ` z ` , and ` y ` and ` z ` .  Lemma for proving ~ sbco3 .  (Contributed
       by Jim Kingdon, 22-Mar-2018.) $)
    sbco3xzyz $p |- ( [ z / y ] [ y / x ] ph <-> [ z / x ] [ x / y ] ph ) $=
      ( wsb sbcomxyyz sbcocom 3bitr4i ) ABDECDEACDEBDEABCECDEACBEBDEABDCFABCDGA
      CBDGH $.
  $}

  ${
    $d w x $.  $d w y $.  $d w ph $.
    $( A composition law for substitution.  (Contributed by NM, 5-Aug-1993.)
       (Proof rewritten by Jim Kingdon, 22-Mar-2018.) $)
    sbco3 $p |- ( [ z / y ] [ y / x ] ph <-> [ z / x ] [ x / y ] ph ) $=
      ( vw wsb sbco3xzyz sbbii ax-17 sbco2h 3bitr3i ) ABCFZCEFZEDFACBFZBEFZEDFL
      CDFNBDFMOEDABCEGHLCDELEIJNBDENEIJK $.
  $}

  $( A commutativity law for substitution.  (Contributed by NM, 27-May-1997.)
     (Proof rewritten by Jim Kingdon, 22-Mar-2018.) $)
  sbcom $p |- ( [ y / z ] [ y / x ] ph <-> [ y / x ] [ y / z ] ph ) $=
    ( wsb sbco3 sbcocom 3bitr3i ) ABDEDCEADBEBCEABCEDCEADCEBCEABDCFABDCGADBCGH
    $.

  ${
    $d w y z $.  $d w ph $.  $d w x $.
    $( Closed form of ~ nfsb .  (Contributed by Jim Kingdon, 9-May-2018.) $)
    nfsbt $p |- ( A. x F/ z ph -> F/ z [ y / x ] ph ) $=
      ( vw wnf wal wsb ax-17 nfsbxyt alimi syl nfv sbco2 nfbii sylib ) ADFBGZQE
      GZABCHZDFZQEIRABEHZECHZDFZTRUADFZEGUCQUDEABEDJKUAECDJLUBSDABCEAEMNOPL $.
  $}

  ${
    $d y z $.
    nfsbd.1 $e |- F/ x ph $.
    nfsbd.2 $e |- ( ph -> F/ z ps ) $.
    $( Deduction version of ~ nfsb .  (Contributed by NM, 15-Feb-2013.) $)
    nfsbd $p |- ( ph -> F/ z [ y / x ] ps ) $=
      ( wal wnf wsb nfri alimi nfsbt 3syl ) AACHBEIZCHBCDJEIACFKAOCGLBCDEMN $.
  $}

  ${
    $d x y $.
    $( Like ~ sb9 but with a distinct variable constraint between ` x ` and
       ` y ` .  (Contributed by Jim Kingdon, 28-Feb-2018.) $)
    sb9v $p |- ( A. x [ x / y ] ph <-> A. y [ y / x ] ph ) $=
      ( wsb hbs1 weq wb sbequ12 equcoms bitr3d cbvalh ) ACBDZABCDZBCACBEABCEBCF
      ALMALGCBACBHIABCHJK $.
  $}

  ${
    $d w x $.  $d w y $.  $d w ph $.
    $( Commutation of quantification and substitution variables.  (Contributed
       by NM, 5-Aug-1993.)  (Proof rewritten by Jim Kingdon, 23-Mar-2018.) $)
    sb9 $p |- ( A. x [ x / y ] ph <-> A. y [ y / x ] ph ) $=
      ( vw wsb wal sb9v sbcom albii 3bitri ax-17 sbco2h 3bitr3ri ) ABDEZDCEZCFZ
      ACDEZDBEZBFZABCEZCFACBEZBFPNCDEZDFQBDEZDFSNCDGUBUCDABDCHIQDBGJOTCABCDADKZ
      LIRUABACBDUDLIM $.
  $}

  $( Commutation of quantification and substitution variables.  (Contributed by
     NM, 5-Aug-1993.)  (Proof rewritten by Jim Kingdon, 23-Mar-2018.) $)
  sb9i $p |- ( A. x [ x / y ] ph -> A. y [ y / x ] ph ) $=
    ( wsb wal sb9 biimpi ) ACBDBEABCDCEABCFG $.

  ${
    $d x y z $.  $d y z ph $.
    $( Two ways of expressing " ` x ` is (effectively) not free in ` ph ` ."
       (Contributed by G&eacute;rard Lang, 14-Nov-2013.)  (Revised by Mario
       Carneiro, 6-Oct-2016.) $)
    sbnf2 $p |- ( F/ x ph
       <-> A. y A. z ( [ y / x ] ph <-> [ z / x ] ph ) ) $=
      ( wsb wb wal wi wnf 2albiim sbhb albii alcom 3bitri nfv nfs1v sblim bitri
      wa sb8 df-nf anbi12i anidm 3bitr2ri ) ABCEZABDEZFDGCGUEUFHZDGCGZUFUEHZDGZ
      CGZSABIZULSULUEUFCDJULUHULUKULAUFHZBGZDGZUGCGZDGUHULAABGHZBGZUMDGZBGUOABU
      AZUQUSBABDKLUMBDMNUNUPDUNUMBCEZCGUPUMBCUMCOTVAUGCAUFBCABDPQLRLUGDCMNULAUE
      HZBGZCGZUKULURVBCGZBGVDUTUQVEBABCKLVBBCMNVCUJCVCVBBDEZDGUJVBBDVBDOTVFUIDA
      UEBDABCPQLRLRUBULUCUD $.
  $}

  ${
    $d y z $.
    hbsbd.1 $e |- ( ph -> A. x ph ) $.
    hbsbd.2 $e |- ( ph -> A. z ph ) $.
    hbsbd.3 $e |- ( ph -> ( ps -> A. z ps ) ) $.
    $( Deduction version of ~ hbsb .  (Contributed by NM, 15-Feb-2013.)  (Proof
       rewritten by Jim Kingdon, 23-Mar-2018.) $)
    hbsbd $p |- ( ph -> ( [ y / x ] ps -> A. z [ y / x ] ps ) ) $=
      ( wsb nfi wi wnf nfdh nfim1 nfsb sbrim nfbii mpbi nfrimi nfrd ) ABCDIZEAU
      AEAEGJZABKZCDIZELAUAKZELUCCDEABEUBABEGHMNOUDUEEABCDFPQRST $.
  $}

  ${
    $d x y z $.  $d w y $.
    $( Equivalence for double substitution.  (Contributed by NM,
       3-Feb-2005.) $)
    2sb5 $p |- ( [ z / x ] [ w / y ] ph <->
               E. x E. y ( ( x = z /\ y = w ) /\ ph ) ) $=
      ( wsb weq wa wex sb5 19.42v anass exbii anbi2i 3bitr4ri bitri ) ACEFZBDFB
      DGZQHZBIRCEGZHAHZCIZBIQBDJSUBBRTAHZHZCIRUCCIZHUBSRUCCKUAUDCRTALMQUERACEJN
      OMP $.

    $( Equivalence for double substitution.  (Contributed by NM,
       3-Feb-2005.) $)
    2sb6 $p |- ( [ z / x ] [ w / y ] ph <->
               A. x A. y ( ( x = z /\ y = w ) -> ph ) ) $=
      ( wsb weq wi wal wa sb6 19.21v impexp albii imbi2i 3bitr4ri bitri ) ACEFZ
      BDFBDGZRHZBISCEGZJAHZCIZBIRBDKTUCBSUAAHZHZCISUDCIZHUCTSUDCLUBUECSUAAMNRUF
      SACEKOPNQ $.
  $}

  ${
    $d w x z $.  $d x y z $.
    $( Lemma for proving ~ sbcom2 .  It is the same as ~ sbcom2 but with
       additional distinct variable constraints on ` x ` and ` y ` , and on
       ` w ` and ` z ` .  (Contributed by Jim Kingdon, 19-Feb-2018.) $)
    sbcom2v $p |- ( [ w / z ] [ y / x ] ph <-> [ y / x ] [ w / z ] ph ) $=
      ( weq wal wsb alcom bi2.04 albii 19.21v bitri 3bitr3i sb6 imbi2i 3bitr4i
      wi ) DEFZBCFZARZBGZRZDGZTSARZDGZRZBGZABCHZDEHZADEHZBCHZTUERZBGZDGUMDGZBGU
      DUHUMDBIUNUCDUNSUARZBGUCUMUPBTSAJKSUABLMKUOUGBTUEDLKNUJSUIRZDGUDUIDEOUQUC
      DUIUBSABCOPKMULTUKRZBGUHUKBCOURUGBUKUFTADEOPKMQ $.
  $}

  ${
    $d v w x z $.  $d v y z $.  $d v ph $.
    $( Lemma for proving ~ sbcom2 .  It is the same as ~ sbcom2v but removes
       the distinct variable constraint on ` x ` and ` y ` .  (Contributed by
       Jim Kingdon, 19-Feb-2018.) $)
    sbcom2v2 $p |- ( [ w / z ] [ y / x ] ph <-> [ y / x ] [ w / z ] ph ) $=
      ( vv wsb sbcom2v sbbii bitri ax-17 sbco2vh 3bitr3i ) ABFGZFCGZDEGZADEGZBF
      GZFCGZABCGZDEGQBCGPNDEGZFCGSNFCDEHUARFCABFDEHIJOTDEABCFAFKLIQBCFQFKLM $.
  $}

  ${
    $d x z $.  $d v x w $.  $d v y z $.  $d v ph $.
    $( Commutativity law for substitution.  Used in proof of Theorem 9.7 of
       [Megill] p. 449 (p. 16 of the preprint).  (Contributed by NM,
       27-May-1997.)  (Proof modified to be intuitionistic by Jim Kingdon,
       19-Feb-2018.) $)
    sbcom2 $p |- ( [ w / z ] [ y / x ] ph <-> [ y / x ] [ w / z ] ph ) $=
      ( vv wsb sbcom2v2 sbbii bitri ax-17 sbco2vh 3bitr3i ) ABCGZDFGZFEGZADFGZF
      EGZBCGZNDEGADEGZBCGPQBCGZFEGSOUAFEABCDFHIQBCFEHJNDEFNFKLRTBCADEFAFKLIM $.
  $}

  ${
    $d x y $.
    $( Equivalence for substitution.  (Contributed by NM, 5-Aug-1993.) $)
    sb6a $p |- ( [ y / x ] ph <-> A. x ( x = y -> [ x / y ] ph ) ) $=
      ( wsb weq wi wal sb6 wb sbequ12 equcoms pm5.74i albii bitri ) ABCDBCEZAFZ
      BGOACBDZFZBGABCHPRBOAQAQICBACBJKLMN $.
  $}

  ${
    $d x y $.  $d x w $.  $d y z $.  $d z w $.
    2sb5rf.1 $e |- ( ph -> A. z ph ) $.
    2sb5rf.2 $e |- ( ph -> A. w ph ) $.
    $( Reversed double substitution.  (Contributed by NM, 3-Feb-2005.) $)
    2sb5rf $p |- ( ph <->
                E. z E. w ( ( z = x /\ w = y ) /\ [ z / x ] [ w / y ] ph ) ) $=
      ( weq wsb wex sb5rf 19.42v sbcom2 anbi2i anass bitri exbii hbsbv 3bitr4ri
      wa ) ADBHZABDIZTZDJUAECHZTZACEIBDIZTZEJZDJABDFKUCUHDUAUDUBCEIZTZTZEJUAUJE
      JZTUHUCUAUJELUGUKEUGUEUITUKUFUIUEACEBDMNUAUDUIOPQUBULUAUBCEABDEGRKNSQP $.

    $( Reversed double substitution.  (Contributed by NM, 3-Feb-2005.) $)
    2sb6rf $p |- ( ph <->
                A. z A. w ( ( z = x /\ w = y ) -> [ z / x ] [ w / y ] ph ) ) $=
      ( weq wsb wi wal wa sb6rf 19.21v sbcom2 imbi2i impexp bitri albii hbsbv
      3bitr4ri ) ADBHZABDIZJZDKUBECHZLZACEIBDIZJZEKZDKABDFMUDUIDUBUEUCCEIZJZJZE
      KUBUKEKZJUIUDUBUKENUHULEUHUFUJJULUGUJUFACEBDOPUBUEUJQRSUCUMUBUCCEABDEGTMP
      UASR $.
  $}

  ${
    $d x z $.  $d y z $.  $d z ph $.
    $( An alternate definition of proper substitution ~ df-sb .  By introducing
       a dummy variable ` z ` in the definiens, we are able to eliminate any
       distinct variable restrictions among the variables ` x ` , ` y ` , and
       ` ph ` of the definiendum.  No distinct variable conflicts arise because
       ` z ` effectively insulates ` x ` from ` y ` .  To achieve this, we use
       a chain of two substitutions in the form of ~ sb5 , first ` z ` for
       ` x ` then ` y ` for ` z ` .  Compare Definition 2.1'' of [Quine] p. 17.
       Theorem ~ sb7f provides a version where ` ph ` and ` z ` don't have to
       be distinct.  (Contributed by NM, 28-Jan-2004.) $)
    dfsb7 $p |- ( [ y / x ] ph <-> E. z ( z = y /\ E. x ( x = z /\ ph ) ) ) $=
      ( wsb weq wa wex sb5 sbbii ax-17 sbco2vh 3bitr3i ) ABDEZDCEBDFAGBHZDCEABC
      EDCFOGDHNODCABDIJABCDADKLODCIM $.
  $}

  ${
    $d x z $.  $d y z $.
    sb7f.1 $e |- ( ph -> A. z ph ) $.
    $( This version of ~ dfsb7 does not require that ` ph ` and ` z ` be
       disjoint.  This permits it to be used as a definition for substitution
       in a formalization that omits the logically redundant axiom ~ ax-17 ,
       i.e., that does not have the concept of a variable not occurring in a
       formula.  (Contributed by NM, 26-Jul-2006.)  (Proof shortened by Andrew
       Salmon, 25-May-2011.) $)
    sb7f $p |- ( [ y / x ] ph <->
               E. z ( z = y /\ E. x ( x = z /\ ph ) ) ) $=
      ( wsb weq wa wex sb5 sbbii sbco2vh 3bitr3i ) ABDFZDCFBDGAHBIZDCFABCFDCGOH
      DINODCABDJKABCDELODCJM $.
  $}

  ${
    $d x z $.  $d y z $.
    sb7af.1 $e |- F/ z ph $.
    $( An alternate definition of proper substitution ~ df-sb .  Similar to
       ~ dfsb7a but does not require that ` ph ` and ` z ` be distinct.
       Similar to ~ sb7f in that it involves a dummy variable ` z ` , but
       expressed in terms of ` A. ` rather than ` E. ` .  (Contributed by Jim
       Kingdon, 5-Feb-2018.) $)
    sb7af $p |- ( [ y / x ] ph
                      <-> A. z
                             ( z = y
                             -> A. x ( x = z -> ph ) ) ) $=
      ( wsb weq wi wal sb6 sbbii sbco2 3bitr3i ) ABDFZDCFBDGAHBIZDCFABCFDCGOHDI
      NODCABDJKABCDELODCJM $.
  $}

  ${
    $d x z $.  $d y z $.  $d z ph $.
    $( An alternate definition of proper substitution ~ df-sb .  Similar to
       ~ dfsb7 in that it involves a dummy variable ` z ` , but expressed in
       terms of ` A. ` rather than ` E. ` .  For a version which only requires
       ` F/ z ph ` rather than ` z ` and ` ph ` being distinct, see ~ sb7af .
       (Contributed by Jim Kingdon, 5-Feb-2018.) $)
    dfsb7a $p |- ( [ y / x ] ph
                      <-> A. z
                             ( z = y
                             -> A. x ( x = z -> ph ) ) ) $=
      ( nfv sb7af ) ABCDADEF $.
  $}

  ${
    $d x y $.
    sb10f.1 $e |- ( ph -> A. x ph ) $.
    $( Hao Wang's identity axiom P6 in Irving Copi, _Symbolic Logic_ (5th ed.,
       1979), p. 328.  In traditional predicate calculus, this is a sole axiom
       for identity from which the usual ones can be derived.  (Contributed by
       NM, 9-May-2005.) $)
    sb10f $p |- ( [ y / z ] ph <-> E. x ( x = y /\ [ x / z ] ph ) ) $=
      ( weq wsb wa wex hbsb sbequ equsex bicomi ) BCFADBGZHBIADCGZNOBCADCBEJABC
      DKLM $.
  $}

  ${
    $d x ph $.
    $( An identity law for substitution.  Used in proof of Theorem 9.7 of
       [Megill] p. 449 (p. 16 of the preprint).  (Contributed by NM,
       5-Aug-1993.) $)
    sbid2v $p |- ( [ y / x ] [ x / y ] ph <-> ph ) $=
      ( ax-17 sbid2h ) ABCABDE $.
  $}

  ${
    $d x y $.  $d x ph $.
    $( Elimination of substitution.  (Contributed by NM, 5-Aug-1993.) $)
    sbelx $p |- ( ph <-> E. x ( x = y /\ [ x / y ] ph ) ) $=
      ( ax-17 sb5rf ) ACBABDE $.
  $}

  ${
    $( Note:  A more general case could also be proved with
       "$d x z $.  $d y w $.  $d x ph $.  $d y ph $.", but with more
       difficulty. $)
    $d x y z $.  $d w y $.  $d x y ph $.
    $( Elimination of double substitution.  (Contributed by NM, 5-Aug-1993.) $)
    sbel2x $p |- ( ph <-> E. x E. y ( ( x = z /\ y = w ) /\
                     [ y / w ] [ x / z ] ph ) ) $=
      ( weq wsb wa wex sbelx anbi2i exbii exdistr 3bitr4i anass 2exbii bitr4i )
      ABDFZCEFZADBGZECGZHZHZCIBIZRSHUAHZCIBIRTHZBIRUBCIZHZBIAUDUFUHBTUGRTCEJKLA
      BDJRUBBCMNUEUCBCRSUAOPQ $.
  $}

  ${
    $d x y z $.
    $( Move universal quantifier in and out of substitution.  Identical to
       ~ sbal except that it has an additional distinct variable constraint on
       ` y ` and ` z ` .  (Contributed by Jim Kingdon, 29-Dec-2017.) $)
    sbalyz $p |- ( [ z / y ] A. x ph <-> A. x [ z / y ] ph ) $=
      ( wal wsb nfa1 nfsbxy ax-4 sbimi alrimi weq wi sb6 albii alcom nfv stdpc5
      bitri alimi sb2 syl sylbi impbii ) ABEZCDFZACDFZBEZUFUGBUECDBABGHUEACDABI
      JKUHCDLZAMZBEZCEZUFUHUJCEZBEULUGUMBACDNOUJBCPSULUIUEMZCEUFUKUNCUIABUIBQRT
      UECDUAUBUCUD $.
  $}

  ${
    $d x y w $.  $d x z w $.  $d w ph $.
    $( Move universal quantifier in and out of substitution.  (Contributed by
       NM, 5-Aug-1993.)  (Proof rewritten by Jim Kingdon, 12-Feb-2018.) $)
    sbal $p |- ( [ z / y ] A. x ph <-> A. x [ z / y ] ph ) $=
      ( vw wal wsb sbalyz sbbii bitri ax-17 sbco2vh albii 3bitr3i ) ABFZCEGZEDG
      ZACEGZEDGZBFZOCDGACDGZBFQRBFZEDGTPUBEDABCEHIRBEDHJOCDEOEKLSUABACDEAEKLMN
      $.
  $}

  ${
    $d x y $.  $d y z $.
    $( Lemma for proving ~ sbal1 .  Same as ~ sbal1 but with an additional
       disjoint variable condition on ` y , z ` .  (Contributed by Jim Kingdon,
       23-Feb-2018.) $)
    sbal1yz $p |- ( -. A. x x = z ->
             ( [ z / y ] A. x ph <-> A. x [ z / y ] ph ) ) $=
      ( weq wal wn wsb wi wb wo dveeq2or equcom nfbii 19.21t sylbi imbi1i albii
      wnf sb6 orim2i ax-mp ori albidv alcom bitri bitr4i bitr2i 3bitr3g bicomd
      ) BDEBFZGZACDHZBFZABFZCDHZULDCEZAIZBFZCFZUQUOIZCFZUNUPULUSVACUKUSVAJZUKCD
      EZBSZKUKVCKBDCLVEVCUKVEUQBSVCVDUQBCDMZNUQABOPUAUBUCUDUTURCFZBFUNURCBUEUMV
      GBUMVDAIZCFVGACDTVHURCVDUQAVFQRUFRUGUPVDUOIZCFVBUOCDTVIVACVDUQUOVFQRUHUIU
      J $.
  $}

  ${
    $d x y $.  $d w x $.  $d w y $.  $d w z $.  $d ph w $.

    $( A theorem used in elimination of disjoint variable conditions on
       ` x , y ` by replacing it with a distinctor ` -. A. x x = z ` .
       (Contributed by NM, 5-Aug-1993.)  (Proof rewitten by Jim Kingdon,
       24-Feb-2018.) $)
    sbal1 $p |- ( -. A. x x = z ->
             ( [ z / y ] A. x ph <-> A. x [ z / y ] ph ) ) $=
      ( vw weq wal wn wsb sbal sbbii sbal1yz bitrid ax-17 sbco2vh albii 3bitr3g
      ) BDFBGHZABGZCEIZEDIZACEIZEDIZBGZSCDIACDIZBGUAUBBGZEDIRUDTUFEDABCEJKUBBED
      LMSCDESENOUCUEBACDEAENOPQ $.
  $}

  ${
    $d x y z $.
    $( Move existential quantifier in and out of substitution.  Identical to
       ~ sbex except that it has an additional disjoint variable condition on
       ` y , z ` .  (Contributed by Jim Kingdon, 29-Dec-2017.) $)
    sbexyz $p |- ( [ z / y ] E. x ph <-> E. x [ z / y ] ph ) $=
      ( wex wsb weq wa sb5 exdistr excom 3bitr2i exbii bitr4i ) ABEZCDFZCDGZAHZ
      CEZBEZACDFZBEPQOHCERBECETOCDIQACBJRCBKLUASBACDIMN $.
  $}

  ${
    $d x y w $.  $d x z w $.  $d w ph $.
    $( Move existential quantifier in and out of substitution.  (Contributed by
       NM, 27-Sep-2003.)  (Proof rewritten by Jim Kingdon, 12-Feb-2018.) $)
    sbex $p |- ( [ z / y ] E. x ph <-> E. x [ z / y ] ph ) $=
      ( vw wex wsb sbexyz sbbii bitri ax-17 sbco2vh exbii 3bitr3i ) ABFZCEGZEDG
      ZACEGZEDGZBFZOCDGACDGZBFQRBFZEDGTPUBEDABCEHIRBEDHJOCDEOEKLSUABACDEAEKLMN
      $.
  $}

  ${
    $d x z $.  $d y z $.
    sbalv.1 $e |- ( [ y / x ] ph <-> ps ) $.
    $( Quantify with new variable inside substitution.  (Contributed by NM,
       18-Aug-1993.) $)
    sbalv $p |- ( [ y / x ] A. z ph <-> A. z ps ) $=
      ( wal wsb sbal albii bitri ) AEGCDHACDHZEGBEGAECDILBEFJK $.
  $}

  ${
    $d v w ph $.  $d v w x $.  $d v w y $.
    $( Lemma for ~ sbco4 .  It replaces the temporary variable ` v ` with
       another temporary variable ` w ` .  (Contributed by Jim Kingdon,
       26-Sep-2018.) $)
    sbco4lem $p |- ( [ x / v ] [ y / x ] [ v / y ] ph <->
        [ x / w ] [ y / x ] [ w / y ] ph ) $=
      ( wsb sbcom2 sbbii nfv sbco2 bitri sbid2 3bitr3i ) ACDFZDEFZBCFZEDFZDBFZO
      EDFZBCFZDBFACEFZBCFZEBFZNBCFZDBFQTDBOBCEDGHRUBEDFZDBFUCQUEDBPUBEDOUABCACE
      DADIJHHHUBEBDUBDIJKTUDDBSNBCNEDNEILHHM $.
  $}

  ${
    $d t u v ph $.  $d t u v x $.  $d t u v y $.  $d w ph $.  $d w x $.
    $d w y $.  $d t w $.
    $( Two ways of exchanging two variables.  Both sides of the biconditional
       exchange ` x ` and ` y ` , either via two temporary variables ` u ` and
       ` v ` , or a single temporary ` w ` .  (Contributed by Jim Kingdon,
       25-Sep-2018.) $)
    sbco4 $p |- ( [ y / u ] [ x / v ] [ u / x ] [ v / y ] ph <->
        [ x / w ] [ y / x ] [ w / y ] ph ) $=
      ( vt wsb sbcom2 nfv sbco2 sbbii bitr3i sbco4lem 3bitri ) ACEHZBFHZEBHFCHZ
      PBCHZEBHZACGHBCHGBHACDHBCHDBHRQFCHZEBHTQFCEBIUASEBPBCFPFJKLMABCGENABCDGNO
      $.
  $}

  ${
    $d x y $.  $d y ph $.
    $( An equivalent expression for existence.  (Contributed by NM,
       2-Feb-2005.) $)
    exsb $p |- ( E. x ph <-> E. y A. x ( x = y -> ph ) ) $=
      ( wex wsb weq wi wal ax-17 sb8eh sb6 exbii bitri ) ABDABCEZCDBCFAGBHZCDAB
      CACIJNOCABCKLM $.
  $}

  ${
    $d x y z $.  $d y w $.  $d z w ph $.
    $( An equivalent expression for double existence.  (Contributed by NM,
       2-Feb-2005.) $)
    2exsb $p |- ( E. x E. y ph <->
                  E. z E. w A. x A. y ( ( x = z /\ y = w ) -> ph ) ) $=
      ( wex weq wi wal exsb exbii excom bitri impexp albii 19.21v bitr2i 3bitri
      wa ) ACFZBFZCEGZAHZCIZBFZEFZBDGZUBSAHZCIZBIZDFZEFUJEFDFUAUDEFZBFUFTULBACE
      JKUDBELMUEUKEUEUGUDHZBIZDFUKUDBDJUNUJDUMUIBUIUGUCHZCIUMUHUOCUGUBANOUGUCCP
      QOKMKUJEDLR $.
  $}

  ${
    $d z ps $.  $d x z $.  $d y z $.
    dvelimALT.1 $e |- ( ph -> A. x ph ) $.
    dvelimALT.2 $e |- ( z = y -> ( ph <-> ps ) ) $.
    $( Version of ~ dvelim that doesn't use ~ ax-10 .  Because it has different
       distinct variable constraints than ~ dvelim and is used in important
       proofs, it would be better if it had a name which does not end in ALT
       (ideally more close to set.mm naming).  (Contributed by NM,
       17-May-2008.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    dvelimALT $p |- ( -. A. x x = y -> ( ps -> A. x ps ) ) $=
      ( weq wal wn wi wnf nfv wo ax12or orcom orbi2i mpbi a1i nfimd orass mpbir
      nfa1 ax16ALT nfd nfi df-nf id sylbir orim1i ax-mp ori nfald ax-17 equsalh
      jaoi nfbii sylib nfrd ) CDHCIZJZBCVAEDHZAKZEIZCLBCLVAVCCEVAEMUTVCCLZVEUTN
      ZUTVENCEHZCIZVBVBCIKCIZNZUTNZVFVKVHVIUTNZNZVHUTVINZNVMEDCOVNVLVHUTVIPQRVH
      VIUTUAUBVJVEUTVHVEVIVHVBACVHVBCVGCUCVBCEUDUEACLZVHACFUFZSTVIVBCLZVEVBCUGV
      QVBACVQUHVOVQVPSTUIUPUJUKVEUTPRULUMVDBCABEDBEUNGUOUQURUS $.
  $}

  ${
    $d x z $.
    dvelimfv.1 $e |- ( ph -> A. x ph ) $.
    dvelimfv.2 $e |- ( ps -> A. z ps ) $.
    dvelimfv.3 $e |- ( z = y -> ( ph <-> ps ) ) $.
    $( Like ~ dvelimf but with a distinct variable constraint on ` x ` and
       ` z ` .  (Contributed by Jim Kingdon, 6-Mar-2018.) $)
    dvelimfv $p |- ( -. A. x x = y -> ( ps -> A. x ps ) ) $=
      ( weq wal wn wi wnf nfnae wo ax12or orcom mpbi a1i nfimd orass mpbir nfae
      orbi2i ax16ALT nfd nfi df-nf sylbir jaoi orim1i ax-mp nfald equsalh nfbii
      id ori sylib nfrd ) CDICJZKZBCVAEDIZALZEJZCMBCMVAVCCECDENUTVCCMZVEUTOZUTV
      EOCEICJZVBVBCJLCJZOZUTOZVFVJVGVHUTOZOZVGUTVHOZOVLEDCPVMVKVGUTVHQUDRVGVHUT
      UAUBVIVEUTVGVEVHVGVBACVGVBCCECUCVBCEUEUFACMZVGACFUGZSTVHVBCMZVEVBCUHVPVBA
      CVPUPVNVPVOSTUIUJUKULVEUTQRUQUMVDBCABEDGHUNUOURUS $.
  $}

  ${
    $d w x $.  $d w y $.  $d w z $.  $d ph w $.
    hbsb4.1 $e |- ( ph -> A. z ph ) $.
    $( A variable not free remains so after substitution with a distinct
       variable.  (Contributed by NM, 5-Aug-1993.)  (Proof rewritten by Jim
       Kingdon, 23-Mar-2018.) $)
    hbsb4 $p |- ( -. A. z z = y -> ( [ y / x ] ph -> A. z [ y / x ] ph ) ) $=
      ( vw wsb hbsb sbequ dvelimALT ) ABFGABCGDCFABFDEHAFCBIJ $.
  $}

  $( A variable not free remains so after substitution with a distinct variable
     (closed form of ~ hbsb4 ).  (Contributed by NM, 7-Apr-2004.)  (Proof
     shortened by Andrew Salmon, 25-May-2011.) $)
  hbsb4t $p |- ( A. x A. z ( ph -> A. z ph ) ->
               ( -. A. z z = y -> ( [ y / x ] ph -> A. z [ y / x ] ph ) ) ) $=
    ( weq wal wn wsb wi hba1 hbsb4 spsbim sps ax-4 sbimi alimi a1i imim12d syl5
    a7s ) DCEDFGADFZBCHZUBDFZIZAUAIZDFBFABCHZUFDFZIZUABCDADJKUEUDUHIDBUEBFZDFZU
    FUBUCUGUIUFUBIDAUABCLMUCUGIUJUBUFDUAABCADNOPQRTS $.

  $( A variable not free remains so after substitution with a distinct variable
     (closed form of ~ hbsb4 ).  (Contributed by NM, 7-Apr-2004.)  (Revised by
     Mario Carneiro, 4-Oct-2016.)  (Proof rewritten by Jim Kingdon,
     9-May-2018.) $)
  nfsb4t $p |- ( A. x F/ z ph ->
                 ( -. A. z z = y -> F/ z [ y / x ] ph ) ) $=
    ( wnf wal weq wn wsb wa nfnf1 nfal nfnae nfan df-nf albii hbsb4t sylbi imp
    wi nfd ex ) ADEZBFZDCGDFHZABCIZDEUDUEJUFDUDUEDUCDBADKLDCDMNUDUEUFUFDFTZUDAA
    DFTDFZBFUEUGTUCUHBADOPABCDQRSUAUB $.

  ${
    dvelimf.1 $e |- ( ph -> A. x ph ) $.
    dvelimf.2 $e |- ( ps -> A. z ps ) $.
    dvelimf.3 $e |- ( z = y -> ( ph <-> ps ) ) $.
    $( Version of ~ dvelim without any variable restrictions.  (Contributed by
       NM, 1-Oct-2002.) $)
    dvelimf $p |- ( -. A. x x = y -> ( ps -> A. x ps ) ) $=
      ( weq wal wn wsb hbsb4 sbieh albii 3imtr3g ) CDICJKAEDLZQCJBBCJAEDCFMABED
      GHNZQBCROP $.
  $}

  ${
    dvelimdf.1 $e |- F/ x ph $.
    dvelimdf.2 $e |- F/ z ph $.
    dvelimdf.3 $e |- ( ph -> F/ x ps ) $.
    dvelimdf.4 $e |- ( ph -> F/ z ch ) $.
    dvelimdf.5 $e |- ( ph -> ( z = y -> ( ps <-> ch ) ) ) $.
    $( Deduction form of ~ dvelimf .  This version may be useful if we want to
       avoid ~ ax-17 and use ~ ax-16 instead.  (Contributed by NM, 7-Apr-2004.)
       (Revised by Mario Carneiro, 6-Oct-2016.)  (Proof shortened by Wolf
       Lammen, 11-May-2018.) $)
    dvelimdf $p |- ( ph -> ( -. A. x x = y -> F/ x ch ) ) $=
      ( weq wal wn wsb wnf wi alrimi nfsb4t syl sbied nfbidf sylibd ) ADELDMNZB
      FEOZDPZCDPABDPZFMUDUFQAUGFHIRBFEDSTAUECDGABCFEHJKUAUBUC $.
  $}

  ${
    $d z ps $.
    dvelim.1 $e |- ( ph -> A. x ph ) $.
    dvelim.2 $e |- ( z = y -> ( ph <-> ps ) ) $.
    $( This theorem can be used to eliminate a distinct variable restriction on
       ` x ` and ` z ` and replace it with the "distinctor" ` -. A. x x = y `
       as an antecedent. ` ph ` normally has ` z ` free and can be read
       ` ph ( z ) ` , and ` ps ` substitutes ` y ` for ` z ` and can be read
       ` ph ( y ) ` .  We don't require that ` x ` and ` y ` be distinct: if
       they aren't, the distinctor will become false (in multiple-element
       domains of discourse) and "protect" the consequent.

       To obtain a closed-theorem form of this inference, prefix the hypotheses
       with ` A. x A. z ` , conjoin them, and apply ~ dvelimdf .

       Other variants of this theorem are ~ dvelimf (with no distinct variable
       restrictions) and ~ dvelimALT (that avoids ~ ax-10 ).  (Contributed by
       NM, 23-Nov-1994.) $)
    dvelim $p |- ( -. A. x x = y -> ( ps -> A. x ps ) ) $=
      ( ax-17 dvelimf ) ABCDEFBEHGI $.
  $}

  ${
    $d z ps $.  $d x z $.
    dvelimor.1 $e |- F/ x ph $.
    dvelimor.2 $e |- ( z = y -> ( ph <-> ps ) ) $.
    $( Disjunctive distinct variable constraint elimination.  A user of this
       theorem starts with a formula ` ph ` (containing ` z ` ) and a distinct
       variable constraint between ` x ` and ` z ` .  The theorem makes it
       possible to replace the distinct variable constraint with the disjunct
       ` A. x x = y ` ( ` ps ` is just a version of ` ph ` with ` y `
       substituted for ` z ` ).  (Contributed by Jim Kingdon, 11-May-2018.) $)
    dvelimor $p |- ( A. x x = y \/ F/ x ps ) $=
      ( weq wal wi wnf wo ax-bndl orcom orbi2i mpbi orass mpbir nfae ax-mp jaoi
      a16nf alrimi df-nf id nfimd sylbir alimi orim1i nfalt ax-17 equsalh nfbii
      a1i sylib orim2i ) CDHCIZEDHZAJZCKZEIZLZUQBCKZLVAUQLZVBCEHCIZURURCIJCIZEI
      ZLZUQLZVDVIVEVGUQLZLZVEUQVGLZLVKEDCMVLVJVEUQVGNOPVEVGUQQRVHVAUQVEVAVGVEUT
      ECEESUSCECUBUCVFUTEVFURCKZUTURCUDVMURACVMUEACKVMFUNUFUGUHUAUITVAUQNPVAVCU
      QVAUSEIZCKVCUSCEUJVNBCABEDBEUKGULUMUOUPT $.
  $}

  ${
    $d z x $.
    $( Quantifier introduction when one pair of variables is distinct.
       (Contributed by NM, 2-Jan-2002.)  (Proof rewritten by Jim Kingdon,
       19-Feb-2018.) $)
    dveeq1 $p |- ( -. A. x x = y -> ( y = z -> A. x y = z ) ) $=
      ( weq wal wn dveeq2 equcom albii 3imtr3g ) ABDAEFCBDZKAEBCDZLAEABCGCBHZKL
      AMIJ $.
  $}

  ${
    $d z y $.  $d z x $.
    $( Move quantifier in and out of substitution.  (Contributed by NM,
       2-Jan-2002.) $)
    sbal2 $p |- ( -. A. x x = y ->
             ( [ z / y ] A. x ph <-> A. x [ z / y ] ph ) ) $=
      ( weq wal wn wi wsb hbnae wb dveeq1 alimi hbnaes 19.21ht syl albidh alcom
      bitr3di sb6 albii 3bitr4g ) BCEBFGZCDEZABFZHZCFZUDAHZCFZBFZUECDIACDIZBFUC
      UHBFZCFUGUJUCULUFCBCCJUCUDUDBFHZBFZULUFKUNBCBUCUMBBCDLMNUDABOPQUHCBRSUECD
      TUKUIBACDTUAUB $.
  $}

  ${
    $d w x $.  $d w y $.  $d w z $.  $d ph w $.
    nfsb4or.1 $e |- F/ z ph $.
    $( A variable not free remains so after substitution with a distinct
       variable.  (Contributed by Jim Kingdon, 11-May-2018.) $)
    nfsb4or $p |- ( A. z z = y \/ F/ z [ y / x ] ph ) $=
      ( vw wsb nfsb sbequ dvelimor ) ABFGABCGDCFABFDEHAFCBIJ $.
  $}

  ${
    nfd2.1 $e |- ( ph -> ( E. x ps -> A. x ps ) ) $.
    $( Deduce that ` x ` is not free in ` ps ` in a context.  (Contributed by
       Wolf Lammen, 16-Sep-2021.) $)
    nfd2 $p |- ( ph -> F/ x ps ) $=
      ( wex wal wi wnf nf2 sylibr ) ABCEBCFGBCHDBCIJ $.
  $}

  $( Dual statement of ~ hbe1 .  (Contributed by Wolf Lammen, 15-Sep-2021.) $)
  hbe1a $p |- ( E. x A. x ph -> A. x ph ) $=
    ( wal wex wi wnf nfa1 nf3 mpbi spi ) ABCZBDKEZBKBFLBCABGKBHIJ $.

  $( One direction of nf5 .  (Contributed by Wolf Lammen, 16-Sep-2021.) $)
  nf5-1 $p |- ( A. x ( ph -> A. x ph ) -> F/ x ph ) $=
    ( wal wi wex exim hbe1a syl6 nfd2 ) AABCZDBCZABKABEJBEJAJBFABGHI $.

  ${
    nf5d.1 $e |- F/ x ph $.
    nf5d.2 $e |- ( ph -> ( ps -> A. x ps ) ) $.
    $( Deduce that ` x ` is not free in ` ps ` in a context.  (Contributed by
       Mario Carneiro, 24-Sep-2016.) $)
    nf5d $p |- ( ph -> F/ x ps ) $=
      ( wal wi wnf alrimi nf5-1 syl ) ABBCFGZCFBCHALCDEIBCJK $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Existential uniqueness
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Declare new symbols needed for uniqueness notation. $)
  $c E! $.  $( Backwards E exclamation point. $)
  $c E* $.  $( Backwards E superscript *. $)

  $( Extend wff definition to include existential uniqueness ("there exists a
     unique ` x ` such that ` ph ` "). $)
  weu $a wff E! x ph $.

  $( Extend wff definition to include uniqueness ("there exists at most one
     ` x ` such that ` ph ` "). $)
  wmo $a wff E* x ph $.

  ${
    $d w x y $.  $d x z $.  $d y ph $.  $d w z ph $.
    $( A soundness justification theorem for ~ df-eu , showing that the
       definition is equivalent to itself with its dummy variable renamed.
       Note that ` y ` and ` z ` needn't be distinct variables.  (Contributed
       by NM, 11-Mar-2010.)  (Proof shortened by Andrew Salmon, 9-Jul-2011.) $)
    eujust $p |- ( E. y A. x ( ph <-> x = y )
        <-> E. z A. x ( ph <-> x = z ) ) $=
      ( vw cv wceq wb wal wex equequ2 bibi2d albidv cbvexv bitri ) ABFZCFZGZHZB
      IZCJAPEFZGZHZBIZEJAPDFZGZHZBIZDJTUDCEQUAGZSUCBUIRUBACEBKLMNUDUHEDUAUEGZUC
      UGBUJUBUFAEDBKLMNO $.
  $}

  ${
    $d x y $.  $d y ph $.
    $( Define existential uniqueness, i.e., "there exists exactly one ` x `
       such that ` ph ` ".  Definition 10.1 of [BellMachover] p. 97; also
       Definition *14.02 of [WhiteheadRussell] p. 175.  Other possible
       definitions are given by ~ eu1 , ~ eu2 , ~ eu3 , and ~ eu5 (which in
       some cases we show with a hypothesis ` ph -> A. y ph ` in place of a
       distinct variable condition on ` y ` and ` ph ` ).  Double uniqueness is
       tricky: ` E! x E! y ph ` does not mean "exactly one ` x ` and one
       ` y ` " (see ~ 2eu4 ).  (Contributed by NM, 5-Aug-1993.) $)
    df-eu $a |- ( E! x ph <-> E. y A. x ( ph <-> x = y ) ) $.
  $}

  $( Define "there exists at most one ` x ` such that ` ph ` ".  Here we define
     it in terms of existential uniqueness.  Notation of [BellMachover] p. 460,
     whose definition we show as ~ mo3 .  For another possible definition see
     ~ mo4 .  (Contributed by NM, 5-Aug-1993.) $)
  df-mo $a |- ( E* x ph <-> ( E. x ph -> E! x ph ) ) $.

  ${
    $d x y z $.  $d ph z $.
    euf.1 $e |- ( ph -> A. y ph ) $.
    $( A version of the existential uniqueness definition with a hypothesis
       instead of a distinct variable condition.  (Contributed by NM,
       12-Aug-1993.) $)
    euf $p |- ( E! x ph <-> E. y A. x ( ph <-> x = y ) ) $=
      ( vz weu weq wb wal wex df-eu ax-17 hbbi hbal equequ2 bibi2d albidv bitri
      cbvexh ) ABFABEGZHZBIZEJABCGZHZBIZCJABEKUBUEECUACBATCDTCLMNUEELECGZUAUDBU
      FTUCAECBOPQSR $.
  $}

  ${
    $d x y $.  $d y ph $.  $d y ps $.  $d y ch $.
    eubidh.1 $e |- ( ph -> A. x ph ) $.
    eubidh.2 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for unique existential quantifier (deduction
       form).  (Contributed by NM, 9-Jul-1994.) $)
    eubidh $p |- ( ph -> ( E! x ps <-> E! x ch ) ) $=
      ( vy weq wb wal wex weu bibi1d albidh exbidv df-eu 3bitr4g ) ABDGHZIZDJZG
      KCRIZDJZGKBDLCDLATUBGASUADEABCRFMNOBDGPCDGPQ $.
  $}

  ${
    $d x y $.  $d y ph $.  $d y ps $.  $d y ch $.
    eubid.1 $e |- F/ x ph $.
    eubid.2 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for unique existential quantifier (deduction
       form).  (Contributed by NM, 9-Jul-1994.) $)
    eubid $p |- ( ph -> ( E! x ps <-> E! x ch ) ) $=
      ( vy weq wb wal wex weu bibi1d albid exbidv df-eu 3bitr4g ) ABDGHZIZDJZGK
      CRIZDJZGKBDLCDLATUBGASUADEABCRFMNOBDGPCDGPQ $.
  $}

  ${
    $d x ph $.
    eubidv.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for unique existential quantifier (deduction
       form).  (Contributed by NM, 9-Jul-1994.) $)
    eubidv $p |- ( ph -> ( E! x ps <-> E! x ch ) ) $=
      ( nfv eubid ) ABCDADFEG $.
  $}

  ${
    eubii.1 $e |- ( ph <-> ps ) $.
    $( Introduce unique existential quantifier to both sides of an equivalence.
       (Contributed by NM, 9-Jul-1994.)  (Revised by Mario Carneiro,
       6-Oct-2016.) $)
    eubii $p |- ( E! x ph <-> E! x ps ) $=
      ( weu wb wtru a1i eubidv mptru ) ACEBCEFGABCABFGDHIJ $.
  $}

  ${
    $d x y $.  $d y ph $.
    $( Bound-variable hypothesis builder for uniqueness.  (Contributed by NM,
       9-Jul-1994.) $)
    hbeu1 $p |- ( E! x ph -> A. x E! x ph ) $=
      ( vy weu weq wb wal wex df-eu hba1 hbex hbxfrbi ) ABDABCEFZBGZCHBABCINBCM
      BJKL $.
  $}

  ${
    $d x y $.  $d y ph $.
    $( Bound-variable hypothesis builder for uniqueness.  (Contributed by NM,
       9-Jul-1994.)  (Revised by Mario Carneiro, 7-Oct-2016.) $)
    nfeu1 $p |- F/ x E! x ph $=
      ( vy weu weq wb wal wex df-eu nfa1 nfex nfxfr ) ABDABCEFZBGZCHBABCINBCMBJ
      KL $.
  $}

  $( Bound-variable hypothesis builder for "at most one".  (Contributed by NM,
     8-Mar-1995.)  (Revised by Mario Carneiro, 7-Oct-2016.) $)
  nfmo1 $p |- F/ x E* x ph $=
    ( wmo wex weu wi df-mo nfe1 nfeu1 nfim nfxfr ) ABCABDZABEZFBABGLMBABHABIJK
    $.

  ${
    $d w y z $.  $d ph z w $.  $d w x z $.
    sb8eu.1 $e |- F/ y ph $.
    $( Variable substitution in unique existential quantifier.  (Contributed by
       NM, 7-Aug-1994.)  (Revised by Mario Carneiro, 7-Oct-2016.) $)
    sb8eu $p |- ( E! x ph <-> E! y [ y / x ] ph ) $=
      ( vz vw weq wb wal wex wsb weu nfv sb8 sbbi nfsb equsb3 nfxfr nfbi df-eu
      sbequ cbval sblbis albii 3bitri exbii 3bitr4i ) ABEGZHZBIZEJABCKZCEGZHZCI
      ZEJABLUKCLUJUNEUJUIBFKZFIUIBCKZCIUNUIBFUIFMNUOUPFCUOABFKZUHBFKZHCAUHBFOUQ
      URCABFCDPURFEGZCBFEQUSCMRSRUPFMUIFCBUAUBUPUMCUHULABCBCEQUCUDUEUFABETUKCET
      UG $.

    $( Variable substitution for "at most one".  (Contributed by Alexander van
       der Vekens, 17-Jun-2017.) $)
    sb8mo $p |- ( E* x ph <-> E* y [ y / x ] ph ) $=
      ( wex weu wi wsb wmo sb8e sb8eu imbi12i df-mo 3bitr4i ) ABEZABFZGABCHZCEZ
      QCFZGABIQCIORPSABCDJABCDKLABMQCMN $.
  $}

  ${
    $d x y z $.  $d z ph $.  $d z ps $.
    nfeudv.1 $e |- F/ y ph $.
    nfeudv.2 $e |- ( ph -> F/ x ps ) $.
    $( Deduction version of ~ nfeu .  Similar to ~ nfeud but has the additional
       constraint that ` x ` and ` y ` must be distinct.  (Contributed by Jim
       Kingdon, 25-May-2018.) $)
    nfeudv $p |- ( ph -> F/ x E! y ps ) $=
      ( vz cv wceq wb wal wex wnf weu nfv a1i nfbid nfald nfexd df-eu sylibr
      nfbii ) ABDHGHIZJZDKZGLZCMBDNZCMAUECGAGOAUDCDEABUCCFUCCMAUCCOPQRSUGUFCBDG
      TUBUA $.
  $}

  ${
    $d x z $.  $d y z $.  $d z ph $.  $d z ps $.
    nfeud.1 $e |- F/ y ph $.
    nfeud.2 $e |- ( ph -> F/ x ps ) $.
    $( Deduction version of ~ nfeu .  (Contributed by NM, 15-Feb-2013.)
       (Revised by Mario Carneiro, 7-Oct-2016.)  (Proof rewritten by Jim
       Kingdon, 25-May-2018.) $)
    nfeud $p |- ( ph -> F/ x E! y ps ) $=
      ( vz weu wsb nfv sb8eu nfsbd nfeudv nfxfrd ) BDHBDGIZGHACBDGBGJKAOCGAGJAB
      DGCEFLMN $.

    $( Bound-variable hypothesis builder for "at most one".  (Contributed by
       Mario Carneiro, 14-Nov-2016.) $)
    nfmod $p |- ( ph -> F/ x E* y ps ) $=
      ( wmo wex weu wi df-mo nfexd nfeud nfimd nfxfrd ) BDGBDHZBDIZJACBDKAPQCAB
      CDEFLABCDEFMNO $.
  $}

  ${
    $d x y z $.  $d z ph $.
    nfeuv.1 $e |- F/ x ph $.
    $( Bound-variable hypothesis builder for existential uniqueness.  This is
       similar to ~ nfeu but has the additional condition that ` x ` and ` y `
       must be distinct.  (Contributed by Jim Kingdon, 23-May-2018.) $)
    nfeuv $p |- F/ x E! y ph $=
      ( vz weu wnf weq wb wal wex nfv nfbi nfal nfex df-eu nfbii mpbir ) ACFZBG
      ACEHZIZCJZEKZBGUBBEUABCATBDTBLMNOSUCBACEPQR $.
  $}

  ${
    $d y z $.  $d x z $.  $d z ph $.
    nfeu.1 $e |- F/ x ph $.
    $( Bound-variable hypothesis builder for existential uniqueness.  Note that
       ` x ` and ` y ` needn't be distinct.  (Contributed by NM, 8-Mar-1995.)
       (Revised by Mario Carneiro, 7-Oct-2016.)  (Proof rewritten by Jim
       Kingdon, 23-May-2018.) $)
    nfeu $p |- F/ x E! y ph $=
      ( vz weu wsb nfv sb8eu nfsb nfeuv nfxfr ) ACFACEGZEFBACEAEHIMBEACEBDJKL
      $.

    $( Bound-variable hypothesis builder for "at most one".  (Contributed by
       NM, 9-Mar-1995.) $)
    nfmo $p |- F/ x E* y ph $=
      ( wmo wnf wtru nftru a1i nfmod mptru ) ACEBFGABCCHABFGDIJK $.
  $}

  ${
    hbeu.1 $e |- ( ph -> A. x ph ) $.
    $( Bound-variable hypothesis builder for uniqueness.  Note that ` x ` and
       ` y ` needn't be distinct.  (Contributed by NM, 8-Mar-1995.)  (Proof
       rewritten by Jim Kingdon, 24-May-2018.) $)
    hbeu $p |- ( E! y ph -> A. x E! y ph ) $=
      ( weu nfi nfeu nfri ) ACEBABCABDFGH $.
  $}

  ${
    hbeud.1 $e |- ( ph -> A. x ph ) $.
    hbeud.2 $e |- ( ph -> A. y ph ) $.
    hbeud.3 $e |- ( ph -> ( ps -> A. x ps ) ) $.
    $( Deduction version of ~ hbeu .  (Contributed by NM, 15-Feb-2013.)  (Proof
       rewritten by Jim Kingdon, 25-May-2018.) $)
    hbeud $p |- ( ph -> ( E! y ps -> A. x E! y ps ) ) $=
      ( weu nfi nfd nfeud nfrd ) ABDHCABCDADFIABCACEIGJKL $.
  $}

  ${
    $d w y z $.  $d ph z w $.  $d w x z $.
    sb8euh.1 $e |- ( ph -> A. y ph ) $.
    $( Variable substitution in unique existential quantifier.  (Contributed by
       NM, 7-Aug-1994.)  (Revised by Andrew Salmon, 9-Jul-2011.) $)
    sb8euh $p |- ( E! x ph <-> E! y [ y / x ] ph ) $=
      ( vz vw weq wb wal wex wsb ax-17 sb8h sbbi hbsb equsb3 hbxfrbi hbbi df-eu
      weu sbequ cbvalh sblbis albii 3bitri exbii 3bitr4i ) ABEGZHZBIZEJABCKZCEG
      ZHZCIZEJABTUKCTUJUNEUJUIBFKZFIUIBCKZCIUNUIBFUIFLMUOUPFCUOABFKZUHBFKZHCAUH
      BFNUQURCABFCDOURFEGZCBFEPUSCLQRQUPFLUIFCBUAUBUPUMCUHULABCBCEPUCUDUEUFABES
      UKCESUG $.
  $}

  ${
    cbveu.1 $e |- F/ y ph $.
    cbveu.2 $e |- F/ x ps $.
    cbveu.3 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 25-Nov-1994.)  (Revised by Mario Carneiro,
       7-Oct-2016.) $)
    cbveu $p |- ( E! x ph <-> E! y ps ) $=
      ( weu wsb sb8eu sbie eubii bitri ) ACHACDIZDHBDHACDEJNBDABCDFGKLM $.
  $}

  ${
    $d x y $.
    eu1.1 $e |- ( ph -> A. y ph ) $.
    $( An alternate way to express uniqueness used by some authors.  Exercise
       2(b) of [Margaris] p. 110.  (Contributed by NM, 20-Aug-1993.) $)
    eu1 $p |- ( E! x ph <->
                E. x ( ph /\ A. y ( [ y / x ] ph -> x = y ) ) ) $=
      ( wsb weu weq wb wal wex wi wa hbs1 euf sb8euh equcom albii sb6rf 3bitr4i
      imbi2i anbi12i ancom albiim exbii ) ABCEZCFUECBGZHCIZBJABFAUEBCGZKZCIZLZB
      JUECBABCMNABCDOUKUGBUJALUEUFKZCIZUFUEKCIZLUKUGUJUMAUNUIULCUHUFUEBCPTQABCD
      RUAAUJUBUEUFCUCSUDS $.
  $}

  ${
    euor.1 $e |- ( ph -> A. x ph ) $.
    $( Introduce a disjunct into a unique existential quantifier.  (Contributed
       by NM, 21-Oct-2005.) $)
    euor $p |- ( ( -. ph /\ E! x ps ) -> E! x ( ph \/ ps ) ) $=
      ( wn weu wo hbn biorf eubidh biimpa ) AEZBCFABGZCFLBMCACDHABIJK $.
  $}

  ${
    $d x ph $.
    $( Introduce a disjunct into a unique existential quantifier.  (Contributed
       by NM, 23-Mar-1995.) $)
    euorv $p |- ( ( -. ph /\ E! x ps ) -> E! x ( ph \/ ps ) ) $=
      ( ax-17 euor ) ABCACDE $.
  $}

  ${
    $d x y $.
    mon.1 $e |- F/ y ph $.
    $( There is at most one of something which does not exist.  (Contributed by
       Jim Kingdon, 2-Jul-2018.) $)
    mo2n $p |- ( -. E. x ph -> E. y A. x ( ph -> x = y ) ) $=
      ( wex wsb weq wi wal sb8e wn alnex nfs1v sbequ1 equcoms con3d cbv3 pm2.21
      nfn alimi 19.8a 3syl sylbir sylnbi ) ABEABCFZCEZABCGZHZBIZCEZABCDJUFKUEKZ
      CIZUJUECLULAKZBIUIUJUKUMCBUEBABCMSACDSCBGAUEAUEHBCABCNOPQUMUHBAUGRTUICUAU
      BUCUD $.
  $}

  $( There is at most one of something which does not exist.  (Contributed by
     Jim Kingdon, 5-Jul-2018.) $)
  mon $p |- ( -. E. x ph -> E* x ph ) $=
    ( wex wn weu wi wmo ax-in2 df-mo sylibr ) ABCZDKABEZFABGKLHABIJ $.

  ${
    $d x y $.  $d ph y $.
    $( Existential uniqueness implies existence.  (Contributed by NM,
       15-Sep-1993.)  (Proof shortened by Andrew Salmon, 9-Jul-2011.) $)
    euex $p |- ( E! x ph -> E. x ph ) $=
      ( vy weu wsb weq wi wal wa wex ax-17 eu1 exsimpl sylbi ) ABDAABCEBCFGCHZI
      BJABJABCACKLAOBMN $.
  $}

  ${
    $d x y $.
    eumo0.1 $e |- ( ph -> A. y ph ) $.
    $( Existential uniqueness implies "at most one".  (Contributed by NM,
       8-Jul-1994.) $)
    eumo0 $p |- ( E! x ph -> E. y A. x ( ph -> x = y ) ) $=
      ( weu weq wb wal wex wi euf biimp alimi eximi sylbi ) ABEABCFZGZBHZCIAPJZ
      BHZCIABCDKRTCQSBAPLMNO $.
  $}

  $( Existential uniqueness implies "at most one".  (Contributed by NM,
     23-Mar-1995.)  (Proof rewritten by Jim Kingdon, 27-May-2018.) $)
  eumo $p |- ( E! x ph -> E* x ph ) $=
    ( weu wex wi wmo ax-1 df-mo sylibr ) ABCZABDZJEABFJKGABHI $.

  ${
    eumoi.1 $e |- E! x ph $.
    $( "At most one" inferred from existential uniqueness.  (Contributed by NM,
       5-Apr-1995.) $)
    eumoi $p |- E* x ph $=
      ( weu wmo eumo ax-mp ) ABDABECABFG $.
  $}

  ${
    mobidh.1 $e |- ( ph -> A. x ph ) $.
    mobidh.2 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for "at most one" quantifier (deduction form).
       (Contributed by NM, 8-Mar-1995.) $)
    mobidh $p |- ( ph -> ( E* x ps <-> E* x ch ) ) $=
      ( wex weu wi wmo exbidh eubidh imbi12d df-mo 3bitr4g ) ABDGZBDHZICDGZCDHZ
      IBDJCDJAPRQSABCDEFKABCDEFLMBDNCDNO $.
  $}

  ${
    mobid.1 $e |- F/ x ph $.
    mobid.2 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for "at most one" quantifier (deduction form).
       (Contributed by NM, 8-Mar-1995.) $)
    mobid $p |- ( ph -> ( E* x ps <-> E* x ch ) ) $=
      ( wex weu wi wmo exbid eubid imbi12d df-mo 3bitr4g ) ABDGZBDHZICDGZCDHZIB
      DJCDJAPRQSABCDEFKABCDEFLMBDNCDNO $.
  $}

  ${
    $d x ph $.
    mobidv.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for "at most one" quantifier (deduction form).
       (Contributed by Mario Carneiro, 7-Oct-2016.) $)
    mobidv $p |- ( ph -> ( E* x ps <-> E* x ch ) ) $=
      ( nfv mobid ) ABCDADFEG $.
  $}

  ${
    mobii.1 $e |- ( ps <-> ch ) $.
    $( Formula-building rule for "at most one" quantifier (inference form).
       (Contributed by NM, 9-Mar-1995.)  (Revised by Mario Carneiro,
       17-Oct-2016.) $)
    mobii $p |- ( E* x ps <-> E* x ch ) $=
      ( wmo wb wtru a1i mobidv mptru ) ACEBCEFGABCABFGDHIJ $.
  $}

  $( Bound-variable hypothesis builder for "at most one".  (Contributed by NM,
     8-Mar-1995.) $)
  hbmo1 $p |- ( E* x ph -> A. x E* x ph ) $=
    ( wmo wex weu wi df-mo hbe1 hbeu1 hbim hbxfrbi ) ABCABDZABEZFBABGLMBABHABIJ
    K $.

  ${
    hbmo.1 $e |- ( ph -> A. x ph ) $.
    $( Bound-variable hypothesis builder for "at most one".  (Contributed by
       NM, 9-Mar-1995.) $)
    hbmo $p |- ( E* y ph -> A. x E* y ph ) $=
      ( wmo wex weu wi df-mo hbex hbeu hbim hbxfrbi ) ACEACFZACGZHBACINOBABCDJA
      BCDKLM $.
  $}

  ${
    cbvmo.1 $e |- F/ y ph $.
    cbvmo.2 $e |- F/ x ps $.
    cbvmo.3 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 9-Mar-1995.)  (Revised by Andrew Salmon,
       8-Jun-2011.) $)
    cbvmo $p |- ( E* x ph <-> E* y ps ) $=
      ( wex weu wi wmo cbvex cbveu imbi12i df-mo 3bitr4i ) ACHZACIZJBDHZBDIZJAC
      KBDKQSRTABCDEFGLABCDEFGMNACOBDOP $.
  $}

  ${
    $d x y z $.  $d ph z $.  $d ps z $.
    cbvmow.1 $e |- F/ y ph $.
    cbvmow.2 $e |- F/ x ps $.
    cbvmow.3 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Rule used to change bound variables, using implicit substitution.
       Version of ~ cbvmo with a disjoint variable condition.  (Contributed by
       NM, 9-Mar-1995.)  (Revised by GG, 23-May-2024.) $)
    cbvmow $p |- ( E* x ph <-> E* y ps ) $=
      ( cbvmo ) ABCDEFGH $.
  $}

  ${
    $d x y z $.  $d ph z $.
    mo23.1 $e |- F/ y ph $.
    $( An implication between two definitions of "there exists at most one."
       (Contributed by Jim Kingdon, 25-Jun-2018.) $)
    mo23 $p |- ( E. y A. x ( ph -> x = y ) ->
               A. x A. y ( ( ph /\ [ y / x ] ph ) -> x = y ) ) $=
      ( vz weq wi wal wex wsb wa nfv nfim nfal equequ2 imbi2d albidv cbvex nfri
      nfs1v sbequ2 ax-8 imim12d cbv3 ancli sylibr anim12 equtr2 syl6 2alimi syl
      aaanh exlimiv sylbir ) ABCFZGZBHZCIABEFZGZBHZEIAABCJZKZUOGZCHBHZUTUQECUSC
      BAURCDURCLMZNUQELECFZUSUPBVFURUOAECBOPQRUTVDEUTUSVACEFZGZKZCHBHZVDUTUTVHC
      HZKVJUTVKUSVHBCVEVAVGBABCTVGBLMZUOVAAURVGABCUABCEUBUCUDUEUSVHBCUSCVESVHBV
      LSULUFVIVCBCVIVBURVGKUOAURVAVGUGBCEUHUIUJUKUMUN $.
  $}

  ${
    $d x y $.
    mor.1 $e |- F/ y ph $.
    $( Converse of ~ mo23 with an additional ` E. x ph ` condition.
       (Contributed by Jim Kingdon, 25-Jun-2018.) $)
    mor $p |- ( E. x ph ->
        ( A. x A. y ( ( ph /\ [ y / x ] ph ) -> x = y ) ->
          E. y A. x ( ph -> x = y ) ) ) $=
      ( wex wsb wa weq wi sb8e impexp bi2.04 bitri 2albii nfs1v nfri eximi alim
      wal alimi a7s exim syl syl5com biimtrid sylbi ) ABEABCFZCEZAUGGBCHZIZCSBS
      ZAUIIZBSZCEZIABCDJUKUGULIZCSBSZUHUNUJUOBCUJAUGUIIIUOAUGUIKAUGUILMNUHUGBSZ
      CEZUPUNUGUQCUGBABCOPQUPUQUMIZCSZURUNIUOUTCBUOBSUSCUGULBRTUAUQUMCUBUCUDUEU
      F $.
  $}

  ${
    $d x y $.
    modc.1 $e |- F/ y ph $.
    $( Equivalent definitions of "there exists at most one," given decidable
       existence.  (Contributed by Jim Kingdon, 1-Jul-2018.) $)
    modc $p |- ( DECID E. x ph ->
        ( E. y A. x ( ph -> x = y ) <->
          A. x A. y ( ( ph /\ [ y / x ] ph ) -> x = y ) ) ) $=
      ( wex wdc weq wi wal wsb wa mo23 wn wo exmiddc mor mo2n a1d jaoi syl
      impbid2 ) ABEZFZABCGZHBICEZAABCJKUDHCIBIZABCDLUCUBUBMZNUFUEHZUBOUBUHUGABC
      DPUGUEUFABCDQRSTUA $.
  $}

  ${
    $d x y $.
    eu2.1 $e |- F/ y ph $.
    $( An alternate way of defining existential uniqueness.  Definition 6.10 of
       [TakeutiZaring] p. 26.  (Contributed by NM, 8-Jul-1994.) $)
    eu2 $p |- ( E! x ph <->
        ( E. x ph /\ A. x A. y ( ( ph /\ [ y / x ] ph ) -> x = y ) ) ) $=
      ( weu wex wsb wa weq wal euex nfri eumo0 mo23 syl jca 19.29r impexp albii
      wi 19.21 bitri anbi2i abai bitr4i exbii sylib eu1 sylibr impbii ) ABEZABF
      ZAABCGZHBCIZTZCJZBJZHZUKULUQABKUKAUNTBJCFUQABCACDLZMABCDNOPURAUMUNTZCJZHZ
      BFZUKURAUPHZBFVCAUPBQVDVBBVDAAVATZHVBUPVEAUPAUTTZCJVEUOVFCAUMUNRSAUTCDUAU
      BUCAVAUDUEUFUGABCUSUHUIUJ $.
  $}

  ${
    $d x y $.
    eu3h.1 $e |- ( ph -> A. y ph ) $.
    $( An alternate way to express existential uniqueness.  (Contributed by NM,
       8-Jul-1994.)  (New usage is discouraged.) $)
    eu3h $p |- ( E! x ph <->
                ( E. x ph /\ E. y A. x ( ph -> x = y ) ) ) $=
      ( weu wex weq wi wal euex eumo0 jca wsb nfi mo23 anim2i eu2 sylibr impbii
      wa ) ABEZABFZABCGZHBICFZTZUAUBUDABJABCDKLUEUBAABCMTUCHCIBIZTUAUDUFUBABCAC
      DNZOPABCUGQRS $.
  $}

  ${
    $d x y $.
    eu3.1 $e |- F/ y ph $.
    $( An alternate way to express existential uniqueness.  (Contributed by NM,
       8-Jul-1994.) $)
    eu3 $p |- ( E! x ph <->
                ( E. x ph /\ E. y A. x ( ph -> x = y ) ) ) $=
      ( nfri eu3h ) ABCACDEF $.
  $}

  $( Uniqueness in terms of "at most one".  (Contributed by NM, 23-Mar-1995.)
     (Proof rewritten by Jim Kingdon, 27-May-2018.) $)
  eu5 $p |- ( E! x ph <-> ( E. x ph /\ E* x ph ) ) $=
    ( weu wex wmo wa euex eumo jca wi df-mo biimpi imp ancoms impbii ) ABCZABDZ
    ABEZFPQRABGABHIRQPRQPRQPJABKLMNO $.

  $( Existence implies "at most one" is equivalent to uniqueness.  (Contributed
     by NM, 5-Apr-2004.) $)
  exmoeu2 $p |- ( E. x ph -> ( E* x ph <-> E! x ph ) ) $=
    ( weu wex wmo eu5 baibr ) ABCABDABEABFG $.

  $( Absorption of existence condition by "at most one".  (Contributed by NM,
     4-Nov-2002.) $)
  moabs $p |- ( E* x ph <-> ( E. x ph -> E* x ph ) ) $=
    ( wex weu wi wmo pm5.4 df-mo imbi2i 3bitr4ri ) ABCZKABDZEZEMKABFZENKLGNMKAB
    HZIOJ $.

  $( If existence is decidable, something exists or at most one exists.
     (Contributed by Jim Kingdon, 30-Jun-2018.) $)
  exmodc $p |- ( DECID E. x ph -> ( E. x ph \/ E* x ph ) ) $=
    ( wex wdc wn wo wmo df-dc weu wi pm2.21 df-mo sylibr orim2i sylbi ) ABCZDPP
    EZFPABGZFPHQRPQPABIZJRPSKABLMNO $.

  $( There is at most one of something which does not exist.  Unlike ~ exmodc
     there is no decidability condition.  (Contributed by Jim Kingdon,
     22-Sep-2018.) $)
  exmonim $p |- ( -. E. x ph -> E* x ph ) $=
    ( wex wn weu wi wmo pm2.21 df-mo sylibr ) ABCZDKABEZFABGKLHABIJ $.

  ${
    $d x y $.
    mo2r.1 $e |- F/ y ph $.
    $( A condition which implies "at most one".  (Contributed by Jim Kingdon,
       2-Jul-2018.) $)
    mo2r $p |- ( E. y A. x ( ph -> x = y ) -> E* x ph ) $=
      ( weq wi wal wex weu wmo nfri eu3h simplbi2com df-mo sylibr ) ABCEFBGCHZA
      BHZABIZFABJRQPABCACDKLMABNO $.
  $}

  ${
    $d x y $.
    mo3h.1 $e |- ( ph -> A. y ph ) $.
    $( Alternate definition of "at most one".  Definition of [BellMachover]
       p. 460, except that definition has the side condition that ` y ` not
       occur in ` ph ` in place of our hypothesis.  (Contributed by NM,
       8-Mar-1995.)  (New usage is discouraged.) $)
    mo3h $p |- ( E* x ph <->
               A. x A. y ( ( ph /\ [ y / x ] ph ) -> x = y ) ) $=
      ( wmo wsb wa weq wi wal wex weu nfi eu2 imbi2i df-mo anclb 3bitr4i sylibr
      19.38 19.21 albii anabs5 pm3.31 biimtrrid 2alimi sylbi simplbi2com impbii
      syl ) ABEZAABCFZGZBCHZIZCJZBJZUKABKZUQIZUQURABLZIZURURUQGZIUKUSUTVBURABCA
      CDMZNZOABPZURUQQRUSAUOIZCJZBJZUQUSAUPIZBJVHAUPBTVGVIBAUOCVCUAUBSVFUOBCUMA
      UMGVFUNAULUCAUMUNUDUEUFUJUGUQVAUKUTURUQVDUHVESUI $.
  $}

  ${
    $d x y $.
    mo3.1 $e |- F/ y ph $.
    $( Alternate definition of "at most one".  Definition of [BellMachover]
       p. 460, except that definition has the side condition that ` y ` not
       occur in ` ph ` in place of our hypothesis.  (Contributed by NM,
       8-Mar-1995.) $)
    mo3 $p |- ( E* x ph <->
               A. x A. y ( ( ph /\ [ y / x ] ph ) -> x = y ) ) $=
      ( nfri mo3h ) ABCACDEF $.
  $}

  ${
    $d x y $.
    mo2dc.1 $e |- F/ y ph $.
    $( Alternate definition of "at most one" where existence is decidable.
       (Contributed by Jim Kingdon, 2-Jul-2018.) $)
    mo2dc $p |- ( DECID E. x ph ->
        ( E* x ph <-> E. y A. x ( ph -> x = y ) ) ) $=
      ( wex wdc wmo wsb wa weq wi wal nfri mo3h modc bitr4id ) ABEFABGAABCHIBCJ
      ZKCLBLAQKBLCEABCACDMNABCDOP $.
  $}

  ${
    euan.1 $e |- ( ph -> A. x ph ) $.
    $( Introduction of a conjunct into unique existential quantifier.
       (Contributed by NM, 19-Feb-2005.)  (Proof shortened by Andrew Salmon,
       9-Jul-2011.) $)
    euan $p |- ( E! x ( ph /\ ps ) <-> ( ph /\ E! x ps ) ) $=
      ( wa weu wex wmo simpl exlimih adantr simpr eximi hbe1 a1d impbid2 mobidh
      ancrd biimpa eu5 jca32 anbi2i 3imtr4i ibar eubidh impbii ) ABEZCFZABCFZEZ
      UGCGZUGCHZEZABCGZBCHZEZEUHUJUMAUNUOUKAULUGACDABIJZKUKUNULUGBCABLZMKUKULUO
      UKUGBCUGCNUKUGBURUKBAUKABUQORPQSUAUGCTUIUPABCTUBUCAUIUHABUGCDABUDUESUF $.
  $}

  ${
    $d x ph $.
    $( Introduction of a conjunct into unique existential quantifier.
       (Contributed by NM, 23-Mar-1995.) $)
    euanv $p |- ( E! x ( ph /\ ps ) <-> ( ph /\ E! x ps ) ) $=
      ( ax-17 euan ) ABCACDE $.
  $}

  $( Introduce or eliminate a disjunct in a unique existential quantifier.
     (Contributed by NM, 21-Oct-2005.)  (Proof shortened by Andrew Salmon,
     9-Jul-2011.) $)
  euor2 $p |- ( -. E. x ph -> ( E! x ( ph \/ ps ) <-> E! x ps ) ) $=
    ( wex wn wo hbe1 hbn wb 19.8a con3i orel1 olc impbid1 syl eubidh ) ACDZEZAB
    FZBCQCACGHRAEZSBIAQACJKTSBABLBAMNOP $.

  ${
    $d w x z $.  $d w y z $.  $d w ph $.
    $( Substitution into "at most one".  (Contributed by Jeff Madsen,
       2-Sep-2009.) $)
    sbmo $p |- ( [ y / x ] E* z ph <-> E* z [ y / x ] ph ) $=
      ( vw wsb wa cv wceq wal wmo nfv sblim sban imbi1i sbcom2 anbi2i sbalv mo3
      wi 3bitri sbbii 3bitr4i ) AADEFZGZDHEHIZTZEJZDJZBCFABCFZUJDEFZGZUFTZEJZDJ
      ADKZBCFUJDKUHUNBCDUGUMBCEUGBCFUEBCFZUFTUJUDBCFZGZUFTUMUEUFBCUFBLMUPURUFAU
      DBCNOURULUFUQUKUJADEBCPQOUARRUOUIBCADEAELSUBUJDEUJELSUC $.
  $}

  ${
    $d x y $.  $d y ph $.
    mo4f.1 $e |- F/ x ps $.
    mo4f.2 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( "At most one" expressed using implicit substitution.  (Contributed by
       NM, 10-Apr-2004.) $)
    mo4f $p |- ( E* x ph <-> A. x A. y ( ( ph /\ ps ) -> x = y ) ) $=
      ( wmo wsb wa weq wi wal ax-17 mo3h sbie anbi2i imbi1i 2albii bitri ) ACGA
      ACDHZIZCDJZKZDLCLABIZUBKZDLCLACDADMNUCUECDUAUDUBTBAABCDEFOPQRS $.
  $}

  ${
    $d x y $.  $d y ph $.  $d x ps $.
    mo4.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( "At most one" expressed using implicit substitution.  (Contributed by
       NM, 26-Jul-1995.) $)
    mo4 $p |- ( E* x ph <-> A. x A. y ( ( ph /\ ps ) -> x = y ) ) $=
      ( nfv mo4f ) ABCDBCFEG $.
  $}

  ${
    $d x y $.  $d y ph $.  $d x ps $.
    eu4.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Uniqueness using implicit substitution.  (Contributed by NM,
       26-Jul-1995.) $)
    eu4 $p |- ( E! x ph <-> ( E. x ph /\
             A. x A. y ( ( ph /\ ps ) -> x = y ) ) ) $=
      ( weu wex wmo wa weq wi wal eu5 mo4 anbi2i bitri ) ACFACGZACHZIQABICDJKDL
      CLZIACMRSQABCDENOP $.
  $}

  $( Existence in terms of "at most one" and uniqueness.  (Contributed by Jim
     Kingdon, 3-Jul-2018.) $)
  exmoeudc $p |- ( DECID E. x ph -> ( E. x ph <-> ( E* x ph -> E! x ph ) ) ) $=
    ( wex wdc wmo weu wi df-mo com12 biimpri euex imim12i peircedc syl5 impbid2
    biimpi ) ABCZDZQABEZABFZGZSQTSQTGZABHZPIUAUBQGRQUBSTQSUBUCJABKLQTMNO $.

  ${
    $d x y $.  $d y ph $.  $d y ps $.
    $( "At most one" is preserved through implication (notice wff reversal).
       (Contributed by NM, 22-Apr-1995.) $)
    moim $p |- ( A. x ( ph -> ps ) -> ( E* x ps -> E* x ph ) ) $=
      ( vy wi wal wsb wa weq nfa1 ax-4 spsbim anim12d imim1d alimdv alimd ax-17
      wmo mo3h 3imtr4g ) ABEZCFZBBCDGZHZCDIZEZDFZCFAACDGZHZUEEZDFZCFBCRACRUBUGU
      KCUACJUBUFUJDUBUIUDUEUBABUHUCUACKABCDLMNOPBCDBDQSACDADQST $.
  $}

  ${
    moimi.1 $e |- ( ph -> ps ) $.
    $( "At most one" is preserved through implication (notice wff reversal).
       (Contributed by NM, 15-Feb-2006.) $)
    moimi $p |- ( E* x ps -> E* x ph ) $=
      ( wi wmo moim mpg ) ABEBCFACFECABCGDH $.
  $}

  ${
    $d x y $.  $d x y ph $.  $d y ps $.
    $( Move antecedent outside of "at most one".  (Contributed by NM,
       28-Jul-1995.) $)
    moimv $p |- ( E* x ( ph -> ps ) -> ( ph -> E* x ps ) ) $=
      ( vy wi wmo wsb weq wal ax-1 a1i sbimi nfv sbf sbim 3imtr3i anim12d ax-17
      wa mo3h imim1d 2alimdv 3imtr4g com12 ) AABEZCFZBCFZAUEUECDGZSZCDHZEZDICIB
      BCDGZSZUJEZDICIUFUGAUKUNCDAUMUIUJABUEULUHBUEEZABAJKZACDGUOCDGAULUHEAUOCDU
      PLACDACMNBUECDOPQUAUBUECDUEDRTBCDBDRTUCUD $.
  $}

  $( Uniqueness implies "at most one" through implication.  (Contributed by NM,
     22-Apr-1995.) $)
  euimmo $p |- ( A. x ( ph -> ps ) -> ( E! x ps -> E* x ph ) ) $=
    ( weu wmo wi wal eumo moim syl5 ) BCDBCEABFCGACEBCHABCIJ $.

  $( Add existential unique existential quantifiers to an implication.  Note
     the reversed implication in the antecedent.  (Contributed by NM,
     19-Oct-2005.)  (Proof shortened by Andrew Salmon, 14-Jun-2011.) $)
  euim $p |- ( ( E. x ph /\ A. x ( ph -> ps ) ) -> ( E! x ps -> E! x ph ) ) $=
    ( wex wi wal wa weu wmo ax-1 euimmo anim12ii eu5 imbitrrdi ) ACDZABECFZGBCH
    ZOACIZGACHOQOPROQJABCKLACMN $.

  $( "At most one" is still the case when a conjunct is added.  (Contributed by
     NM, 22-Apr-1995.) $)
  moan $p |- ( E* x ph -> E* x ( ps /\ ph ) ) $=
    ( wa simpr moimi ) BADACBAEF $.

  ${
    moani.1 $e |- E* x ph $.
    $( "At most one" is still true when a conjunct is added.  (Contributed by
       NM, 9-Mar-1995.) $)
    moani $p |- E* x ( ps /\ ph ) $=
      ( wmo wa moan ax-mp ) ACEBAFCEDABCGH $.
  $}

  $( "At most one" is still the case when a disjunct is removed.  (Contributed
     by NM, 5-Apr-2004.) $)
  moor $p |- ( E* x ( ph \/ ps ) -> E* x ph ) $=
    ( wo orc moimi ) AABDCABEF $.

  $( "At most one" imports disjunction to conjunction.  (Contributed by NM,
     5-Apr-2004.)  (Proof shortened by Andrew Salmon, 9-Jul-2011.) $)
  mooran1 $p |- ( ( E* x ph \/ E* x ps ) -> E* x ( ph /\ ps ) ) $=
    ( wmo wa simpl moimi moan jaoi ) ACDABEZCDBCDJACABFGBACHI $.

  $( "At most one" exports disjunction to conjunction.  (Contributed by NM,
     5-Apr-2004.)  (Proof shortened by Andrew Salmon, 9-Jul-2011.) $)
  mooran2 $p |- ( E* x ( ph \/ ps ) -> ( E* x ph /\ E* x ps ) ) $=
    ( wo wmo moor olc moimi jca ) ABDZCEACEBCEABCFBJCBAGHI $.

  ${
    $d x y $.  $d y ph $.  $d y ps $.
    moanim.1 $e |- F/ x ph $.
    $( Introduction of a conjunct into at-most-one quantifier.  (Contributed by
       NM, 3-Dec-2001.) $)
    moanim $p |- ( E* x ( ph /\ ps ) <-> ( ph -> E* x ps ) ) $=
      ( vy wsb wa weq wi wal wmo anandi imbi1i impexp sbf anbi1i ax-17 3bitr4ri
      sban mo3h bitr2i anbi2i 3bitr3i 2albii 19.21 19.21v albii imbi2i ) ABBCEF
      ZGZCEHZIZIZEJZCJZABGZUPCEFZGZUKIZEJCJABCKZIZUPCKUMUSCEAUJGZUKIUPAUIGZGZUK
      IUMUSVBVDUKABUILMAUJUKNVDURUKVCUQUPUQACEFZUIGVCABCESVEAUIACEDOPUAUBMUCUDA
      ULEJZIZCJAVFCJZIUOVAAVFCDUEUNVGCAULEUFUGUTVHABCEBEQTUHRUPCEUPEQTR $.
  $}

  ${
    $d x ph $.
    $( Introduction of a conjunct into at-most-one quantifier.  (Contributed by
       NM, 23-Mar-1995.) $)
    moanimv $p |- ( E* x ( ph /\ ps ) <-> ( ph -> E* x ps ) ) $=
      ( nfv moanim ) ABCACDE $.
  $}

  $( Nested at-most-one and unique existential quantifiers.  (Contributed by
     NM, 25-Jan-2006.) $)
  moaneu $p |- E* x ( ph /\ E! x ph ) $=
    ( weu wa wmo wi eumo nfeu1 moanim mpbir ancom mobii ) AABCZDZBEMADZBEZPMABE
    FABGMABABHIJNOBAMKLJ $.

  $( Nested at-most-one quantifiers.  (Contributed by NM, 25-Jan-2006.) $)
  moanmo $p |- E* x ( ph /\ E* x ph ) $=
    ( wmo wa wi id nfmo1 moanim mpbir ancom mobii ) AABCZDZBCLADZBCZOLLELFLABAB
    GHIMNBALJKI $.

  ${
    $d x y $.  $d y ph $.  $d y ps $.
    $( "At most one" picks a variable value, eliminating an existential
       quantifier.  (Contributed by NM, 27-Jan-1997.) $)
    mopick $p |- ( ( E* x ph /\ E. x ( ph /\ ps ) ) -> ( ph -> ps ) ) $=
      ( vy wa wex wmo wi wsb hbs1 hban weq sbequ12 anbi12d cbvexh wal mo3h ax-4
      ax-17 sylbi sps sbequ2 imim2i expd com4t imp syl5 exlimiv impcom ) ABEZCF
      ZACGZABHZUKACDIZBCDIZEZDFULUMHZUJUPCDUJDSUNUOCACDJBCDJKCDLZAUNBUOACDMBCDM
      NOUPUQDULAUNEZURHZUPUMULUTDPZCPUTACDADSQVAUTCUTDRUATUNUOUTUMHUTAUNUOBUTAU
      NUOBHZURVBUSBCDUBUCUDUEUFUGUHTUI $.
  $}

  $( Existential uniqueness "picks" a variable value for which another wff is
     true.  If there is only one thing ` x ` such that ` ph ` is true, and
     there is also an ` x ` (actually the same one) such that ` ph ` and ` ps `
     are both true, then ` ph ` implies ` ps ` regardless of ` x ` .  This
     theorem can be useful for eliminating existential quantifiers in a
     hypothesis.  Compare Theorem *14.26 in [WhiteheadRussell] p. 192.
     (Contributed by NM, 10-Jul-1994.) $)
  eupick $p |- ( ( E! x ph /\ E. x ( ph /\ ps ) ) -> ( ph -> ps ) ) $=
    ( weu wmo wa wex wi eumo mopick sylan ) ACDACEABFCGABHACIABCJK $.

  $( Version of ~ eupick with closed formulas.  (Contributed by NM,
     6-Sep-2008.) $)
  eupicka $p |- ( ( E! x ph /\ E. x ( ph /\ ps ) ) -> A. x ( ph -> ps ) ) $=
    ( weu wa wex wi hbeu1 hbe1 hban eupick alrimih ) ACDZABEZCFZEABGCMOCACHNCIJ
    ABCKL $.

  $( Existential uniqueness "pick" showing wff equivalence.  (Contributed by
     NM, 25-Nov-1994.) $)
  eupickb $p |- ( ( E! x ph /\ E! x ps /\ E. x ( ph /\ ps ) ) ->
               ( ph <-> ps ) ) $=
    ( weu wa wex w3a wi eupick 3adant2 3simpc pm3.22 eximi anim2i 3syl impbid )
    ACDZBCDZABEZCFZGZABQTABHRABCIJUARTERBAEZCFZEBAHQRTKTUCRSUBCABLMNBACIOP $.

  $( Theorem *14.26 in [WhiteheadRussell] p. 192.  (Contributed by Andrew
     Salmon, 11-Jul-2011.) $)
  eupickbi $p |- ( E! x ph -> ( E. x ( ph /\ ps ) <-> A. x ( ph -> ps ) ) ) $=
    ( weu wa wex wi wal eupicka ex hba1 wb ancl simpl impbid1 sps euex biimtrdi
    eubidh com12 impbid ) ACDZABEZCFZABGZCHZUBUDUFABCIJUFUBUDUFUBUCCDUDUFAUCCUE
    CKUEAUCLCUEAUCABMABNOPSUCCQRTUA $.

  $( "At most one" can show the existence of a common value.  In this case we
     can infer existence of conjunction from a conjunction of existence, and it
     is one way to achieve the converse of ~ 19.40 .  (Contributed by NM,
     5-Apr-2004.)  (Proof shortened by Andrew Salmon, 9-Jul-2011.) $)
  mopick2 $p |- ( ( E* x ph /\ E. x ( ph /\ ps ) /\ E. x ( ph /\ ch ) ) ->
                E. x ( ph /\ ps /\ ch ) ) $=
    ( wmo wex w3a hbmo1 hbe1 mopick ancld anim1d df-3an imbitrrdi eximdh 3impia
    wa hban ) ADEZABQZDFZACQZDFABCGZDFSUAQZUBUCDSUADADHTDIRUDUBTCQUCUDATCUDABAB
    DJKLABCMNOP $.

  ${
    moexexdc.1 $e |- F/ y ph $.
    $( "At most one" double quantification.  (Contributed by Jim Kingdon,
       5-Jul-2018.) $)
    moexexdc $p |- ( DECID E. x ph ->
        ( ( E* x ph /\ A. x E* y ps ) -> E* y E. x ( ph /\ ps ) ) ) $=
      ( wex wdc wn wo wmo wal wa wi df-dc hbmo1 hba1 hbmo hbim exlimih a1d hbe1
      nfri mopick com3r alrimdh moim spsd syl6 hbex exsimpl con3i mon jaoi impd
      ex syl sylbi ) ACFZGURURHZIZACJZBDJZCKZLABLZCFZDJZMURNUTVAVCVFURVAVCVFMZM
      ZUSAVHCVAVGCACOVCVFCVBCPVECDVDCUAQRRAVAVEBMZDKZVGAVAVIDADEUBZADCVKQVAVEAB
      VAVEABMABCUCUOUDUEVJVBVFCVEBDUFUGUHSUSVGVAUSVFVCUSVEDFZHVFVLURVEURDADCVKU
      IABCUJSUKVEDULUPTTUMUNUQ $.
  $}

  ${
    euexex.1 $e |- F/ y ph $.
    $( Existential uniqueness and "at most one" double quantification.
       (Contributed by Jim Kingdon, 28-Dec-2018.) $)
    euexex $p |-
        ( ( E! x ph /\ A. x E* y ps ) -> E* y E. x ( ph /\ ps ) ) $=
      ( weu wmo wal wa wex wi eu5 nfmo1 nfa1 nfe1 nfmo nfim mopick ex imp com3r
      alrimd moim spsd syl6 exlimi sylbi ) ACFZBDGZCHZABIZCJZDGZUHACJZACGZIUJUM
      KZACLUNUOUPAUOUPKCUOUPCACMUJUMCUICNULCDUKCOPQQAUOULBKZDHZUPAUOUQDEADCEPUO
      ULABUOULABKABCRSUAUBURUIUMCULBDUCUDUEUFTUGT $.
  $}

  $( Double quantification with "at most one".  (Contributed by NM,
     3-Dec-2001.) $)
  2moex $p |- ( E* x E. y ph -> A. y E* x ph ) $=
    ( wex wmo hbe1 hbmo 19.8a moimi alrimih ) ACDZBEABECKCBACFGAKBACHIJ $.

  $( Double quantification with existential uniqueness.  (Contributed by NM,
     3-Dec-2001.)  (Proof shortened by Andrew Salmon, 9-Jul-2011.) $)
  2euex $p |- ( E! x E. y ph -> E. y E! x ph ) $=
    ( wex weu wmo wa excom hbe1 hbmo wi 19.8a moimi df-mo sylib eximdh biimtrid
    eu5 impcom sylbi ) ACDZBEUABDZUABFZGABEZCDZUABRUCUBUEUBABDZCDUCUEABCHUCUFUD
    CUACBACIJUCABFUFUDKAUABACLMABNOPQST $.

  $( Double quantification with existential uniqueness and "at most one."
     (Contributed by NM, 3-Dec-2001.) $)
  2eumo $p |- ( E! x E* y ph -> E* x E! y ph ) $=
    ( weu wmo wi euimmo eumo mpg ) ACDZACEZFKBDJBEFBJKBGACHI $.

  $( Double existential uniqueness.  (Contributed by NM, 3-Dec-2001.) $)
  2eu2ex $p |- ( E! x E! y ph -> E. x E. y ph ) $=
    ( weu wex euex eximi syl ) ACDZBDIBEACEZBEIBFIJBACFGH $.

  $( A condition allowing swap of "at most one" and existential quantifiers.
     (Contributed by Jim Kingdon, 6-Jul-2018.) $)
  2moswapdc $p |- ( DECID E. x E. y ph -> ( A. x E* y ph ->
      ( E* x E. y ph -> E* y E. x ph ) ) ) $=
    ( wex wdc wmo wa wi nfe1 moexexdc expcomd 19.8a pm4.71ri exbii mobii imbi2i
    wal imbitrrdi ) ACDZBDEZACFBQZSBFZSAGZBDZCFZHUBABDZCFZHTUBUAUESABCACIJKUGUE
    UBUFUDCAUCBASACLMNOPR $.

  $( A condition allowing swap of uniqueness and existential quantifiers.
     (Contributed by Jim Kingdon, 7-Jul-2018.) $)
  2euswapdc $p |- ( DECID E. x E. y ph -> ( A. x E* y ph ->
      ( E! x E. y ph -> E! y E. x ph ) ) ) $=
    ( wex wdc wmo wal weu wi wa excomim a1i 2moswapdc imp anim12d eu5 3imtr4g
    ex ) ACDZBDZEZACFBGZSBHZABDZCHZIUAUBJZTSBFZJUDCDZUDCFZJUCUEUFTUHUGUITUHIUFA
    BCKLUAUBUGUIIABCMNOSBPUDCPQR $.

  $( Double existential uniqueness implies double unique existential
     quantification.  (Contributed by NM, 3-Dec-2001.) $)
  2exeu $p |- ( ( E! x E. y ph /\ E! y E. x ph ) -> E! x E! y ph ) $=
    ( wex wmo weu excom hbe1 hbmo 19.41h 19.8a moimi anim2i eximi sylbir sylanb
    wa simpl eu5 anbi12i adantl anim12i ancoms exbii mobii bitri 3imtr4i ) ACDZ
    BDZUHBEZQZABDZCDZULCEZQZQUHACEZQZBDZUQBEZQZUHBFZULCFZQACFZBFZUOUKUTUOURUKUS
    UMUIUNURACBGUIUNQUHUNQZBDURUHUNBULBCABHIJVEUQBUNUPUHAULCABKLMNOPUJUSUIUQUHB
    UHUPRLUAUBUCVAUKVBUOUHBSULCSTVDVCBDZVCBEZQUTVCBSVFURVGUSVCUQBACSZUDVCUQBVHU
    ETUFUG $.

  ${
    $d x y z w $.  $d z w ph $.
    $( This theorem provides us with a definition of double existential
       uniqueness ("exactly one ` x ` and exactly one ` y ` ").  Naively one
       might think (incorrectly) that it could be defined by ` E! x E! y ph ` .
       See ~ 2exeu for a one-way implication.  (Contributed by NM,
       3-Dec-2001.) $)
    2eu4 $p |- ( ( E! x E. y ph /\ E! y E. x ph ) <->
      ( E. x E. y ph /\ E. z E. w A. x A. y ( ph -> ( x = z /\ y = w ) ) ) ) $=
      ( wex weu wa weq wi wal ax-17 eu3h anbi12i anbi2i bitri 19.3h 19.26 albii
      hba1 excom anidm jcab 3bitr4ri alcom bitr4i 19.23v 2albii hbe1 hbim aaanh
      an4 3bitri 2exbii eeanv bitr2i ) ACFZBGZABFZCGZHUQBFZUQBDIZJZBKZDFZHZUSCF
      ZUSCEIZJZCKZEFZHZHVAVGHZVEVKHZHVAAVBVHHJZCKZBKZEFDFZHURVFUTVLUQBDUQDLMUSC
      EUSELMNVAVEVGVKULVMVAVNVRVMVAVAHVAVGVAVAACBUAOVAUBPVRVDVJHZEFDFVNVQVSDEVQ
      AVBJZCKZAVHJZBKZHZCKZBKZVCVIHZCKBKVSVQWAWBCKZBKZHZBKZWFWABKZWIBKZHWLWIHZW
      KVQWMWIWLWIBWHBTQOWAWIBRVQWAWHHZBKWNVPWOBVPVTWBHZCKWOVOWPCAVBVHUCSVTWBCRP
      SWAWHBRPUDWEWJBWEWACKZWCCKZHWJWAWCCRWQWAWRWIWACVTCTQWBCBUENPSUFWDWGBCWAVC
      WCVIAVBCUGAVHBUGNUHVCVIBCUQVBCACUIVBCLUJUSVHBABUIVHBLUJUKUMUNVDVJDEUOUPNU
      M $.
  $}

  $( Two equivalent expressions for double existential uniqueness.
     (Contributed by NM, 19-Feb-2005.) $)
  2eu7 $p |- ( ( E! x E. y ph /\ E! y E. x ph ) <->
             E! x E! y ( E. x ph /\ E. y ph ) ) $=
    ( wex weu wa hbe1 hbeu euan ancom eubii 3bitri 3bitr4ri ) ABDZCEZACDZFZBEOP
    BEZFNPFZCEZBEROFOPBNBCABGHITQBTPNFZCEPOFQSUACNPJKPNCACGIPOJLKROJM $.

  ${
    $d x y z $.
    $( Equality has existential uniqueness.  (Contributed by Stefan Allan,
       4-Dec-2008.) $)
    euequ1 $p |- E! x x = y $=
      ( vz weq weu wex wa wi wal a9e equtr2 gen2 equequ1 eu4 mpbir2an ) ABDZAEP
      AFPCBDZGACDHZCIAIABJRACACBKLPQACACBMNO $.
  $}

  ${
    $d x y $.
    $( Two ways to express "only one thing exists".  The left-hand side
       requires only one variable to express this.  Both sides are false in set
       theory.  (Contributed by NM, 5-Apr-2004.) $)
    exists1 $p |- ( E! x x = x <-> A. x x = y ) $=
      ( weq weu wb wal wex df-eu equid tbt bicom bitri albii exbii hbae 3bitr2i
      19.9h ) AACZADRABCZEZAFZBGSAFZBGUBRABHUBUABSTASSRETRSAIJSRKLMNUBBABBOQP
      $.
  $}

  ${
    $d x y $.
    $( A condition implying that at least two things exist.  (Contributed by
       NM, 10-Apr-2004.)  (Proof shortened by Andrew Salmon, 9-Jul-2011.) $)
    exists2 $p |- ( ( E. x ph /\ E. x -. ph ) -> -. E! x x = x ) $=
      ( vy wex wn cv wceq weu wal hbeu1 hba1 wi exists1 ax16 sylbi com12 alexim
      exlimdh syl6 con2d imp ) ABDZAEBDZBFZUDGZBHZEUBUFUCUBUFABIZUCEUFUBUGUFAUG
      BUEBJABKUFUDCFGBIAUGLBCMABCNORPABQSTUA $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Aristotelian logic: Assertic syllogisms
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  Model the Aristotelian assertic syllogisms using modern notation.
  This section shows that the Aristotelian assertic syllogisms can be proven
  with our axioms of logic, and also provides generally useful theorems.

  In antiquity Aristotelian logic and Stoic logic
  (see ~ mptnan ) were the leading logical systems.
  Aristotelian logic became the leading system in medieval Europe;
  this section models this system (including later refinements to it).
  Aristotle defined syllogisms very generally
  ("a discourse in which certain (specific) things having been supposed,
  something different from the things supposed results of necessity
  because these things are so")
  Aristotle, _Prior Analytics_ 24b18-20.
  However, in _Prior Analytics_ he limits himself to
  categorical syllogisms that consist of three categorical propositions
  with specific structures.  The syllogisms are the valid subset of
  the possible combinations of these structures.
  The medieval schools used vowels to identify the types of terms
  (a=all, e=none, i=some, and o=some are not), and named the different
  syllogisms with Latin words that had the vowels in the intended order.

  "There is a surprising amount of scholarly debate
  about how best to formalize Aristotle's syllogisms..." according to
  _Aristotle's Modal Proofs: Prior Analytics A8-22 in Predicate Logic_,
  Adriane Rini, Springer, 2011, ISBN 978-94-007-0049-9, page 28.
  For example, Lukasiewicz believes it is important to note that
  "Aristotle does not introduce singular terms or premisses into his system".
  Lukasiewicz also believes that Aristotelian syllogisms are
  predicates (having a true/false value), not inference rules:
  "The characteristic sign of an inference is the word 'therefore'...
  no syllogism is formulated by Aristotle primarily as an inference,
  but they are all implications."
  Jan Lukasiewicz, _Aristotle's Syllogistic from the Standpoint of
  Modern Formal Logic_, Second edition, Oxford, 1957, page 1-2.
  Lukasiewicz devised a specialized prefix notation for representing
  Aristotelian syllogisms instead of using standard predicate logic notation.

  We instead translate each Aristotelian syllogism into an inference rule,
  and each rule is defined using standard predicate logic notation and
  predicates.  The predicates are represented by wff variables
  that may depend on the quantified variable ` x ` .
  Our translation is essentially identical to the one
  use in Rini page 18, Table 2 "Non-Modal Syllogisms in
  Lower Predicate Calculus (LPC)", which uses
  standard predicate logic with predicates.  Rini states,
  "the crucial point is that we capture the meaning Aristotle intends,
  and the method by which we represent that meaning is less important."
  There are two differences: we make the existence criteria explicit, and
  we use ` ph ` , ` ps ` , and ` ch ` in the order they appear
  (a common Metamath convention).
  Patzig also uses standard predicate logic notation and predicates
  (though he interprets them as conditional propositions, not as
  inference rules); see
  Gunther Patzig, _Aristotle's Theory of the Syllogism_ second edition, 1963,
  English translation by Jonathan Barnes, 1968, page 38.
  Terms such as "all" and "some" are translated into predicate logic
  using the aproach devised by Frege and Russell.
  "Frege (and Russell) devised an ingenious procedure for regimenting
  binary quantifiers like "every" and "some" in terms of unary quantifiers
  like "everything" and "something": they formalized sentences of the form
  "Some A is B" and "Every A is B" as
  exists x (Ax and Bx) and all x (Ax implies Bx), respectively."
  "Quantifiers and Quantification", _Stanford Encyclopedia of Philosophy_,
  ~ https://plato.stanford.edu/entries/quantification/ .
  See _Principia Mathematica_ page 22 and *10 for more information
  (especially *10.3 and *10.26).

  Expressions of the form "no ` ph ` is ` ps ` " are consistently translated as
  ` A. x ( ph -> -. ps ) ` .  These can also be expressed as
  ` -. E. x ( ph /\ ps ) ` , per ~ alinexa .
  We translate "all ` ph ` is ` ps ` " to ` A. x ( ph -> ps ) ` ,
  "some ` ph ` is ` ps ` " to ` E. x ( ph /\ ps ) ` , and
  "some ` ph ` is not ` ps ` " to ` E. x ( ph /\ -. ps ) ` .
  It is traditional to use the singular verb "is", not the plural
  verb "are", in the generic expressions.
  By convention the major premise is listed first.

  In traditional Aristotelian syllogisms the predicates
  have a restricted form ("x is a ..."); those predicates
  could be modeled in modern notation by constructs such as
  ` x = A ` , ` x e. A ` , or ` x C_ A ` .
  Here we use wff variables instead of specialized restricted forms.
  This generalization makes the syllogisms more useful
  in more circumstances.  In addition, these expressions make
  it clearer that the syllogisms of Aristolean logic are the
  forerunners of predicate calculus.  If we used restricted forms
  like ` x e. A ` instead, we would not only unnecessarily limit
  their use, but we would also need to use set and class axioms,
  making their relationship to predicate calculus less clear.

  There are some widespread misconceptions about the existential
  assumptions made by Aristotle (aka "existential import").
  Aristotle was not trying to develop something exactly corresponding
  to modern logic.  Aristotle devised "a companion-logic for science.
  He relegates fictions like fairy godmothers and mermaids and unicorns to
  the realms of poetry and literature. In his mind, they exist outside the
  ambit of science. This is why he leaves no room for such nonexistent
  entities in his logic.  This is a thoughtful choice, not an inadvertent
  omission. Technically, Aristotelian science is a search for definitions,
  where a definition is "a phrase signifying a thing's essence."
  (Topics, I.5.102a37, Pickard-Cambridge.)...
  Because nonexistent entities cannot be anything, they do not, in
  Aristotle's mind, possess an essence...  This is why he leaves
  no place for fictional entities like goat-stags (or unicorns)."
  Source: Louis F. Groarke, "Aristotle: Logic",
  section 7. (Existential Assumptions),
  _Internet Encyclopedia of Philosophy_ (A Peer-Reviewed Academic Resource),
  ~ https://iep.utm.edu/aristotle-log/ .
  Thus, some syllogisms have "extra" existence
  hypotheses that do not directly appear in Aristotle's original materials
  (since they were always assumed); they are added where they are needed.
  This affects ~ barbari , ~ celaront , ~ cesaro , ~ camestros , ~ felapton ,
  ~ darapti , ~ calemos , ~ fesapo , and ~ bamalip .

  These are only the _assertic_ syllogisms.
  Aristotle also defined modal syllogisms that deal with modal
  qualifiers such as "necessarily" and "possibly".
  Historically Aristotelian modal syllogisms were not as widely used.
  For more about modal syllogisms in a modern context, see Rini as well as
  _Aristotle's Modal Syllogistic_ by Marko Malink, Harvard
  University Press, November 2013.  We do not treat them further here.

  Aristotelian logic is essentially the forerunner of predicate calculus
  (as well as set theory since it discusses membership in groups),
  while Stoic logic is essentially the forerunner of propositional calculus.
$)

  $( Figure 1.  Aristotelian syllogisms are grouped by "figures",
     which doesn't matter for our purposes but is a reasonable way
     to order them. $)

  ${
    $( Major premise for the Aristotelian syllogism "Barbara", e.g.,
       "All men are mortal". By convention, the major premise is first. $)
    barbara.maj $e |- A. x ( ph -> ps ) $.
    $( Minor premise for Barbara, e.g., "Socrates is a man". $)
    barbara.min $e |- A. x ( ch -> ph ) $.
    $( "Barbara", one of the fundamental syllogisms of Aristotelian logic.  All
       ` ph ` is ` ps ` , and all ` ch ` is ` ph ` , therefore all ` ch ` is
       ` ps ` .  (In Aristotelian notation, AAA-1:  MaP and SaM therefore SaP.)
       For example, given "All men are mortal" and "Socrates is a man", we can
       prove "Socrates is mortal".  If H is the set of men, M is the set of
       mortal beings, and S is Socrates, these word phrases can be represented
       as ` A. x ( x e. H -> x e. M ) ` (all men are mortal) and
       ` A. x ( x = S -> x e. H ) ` (Socrates is a man) therefore
       ` A. x ( x = S -> x e. M ) ` (Socrates is mortal).  Russell and
       Whitehead note that the "syllogism in Barbara is derived..." from
       ~ syl .  (quote after Theorem *2.06 of [WhiteheadRussell] p. 101).  Most
       of the proof is in ~ alsyl .  There are a legion of sources for Barbara,
       including ~ https://www.friesian.com/aristotl.htm ,
       ~ https://plato.stanford.edu/entries/aristotle-logic/ , and
       ~ https://en.wikipedia.org/wiki/Syllogism .  (Contributed by David A.
       Wheeler, 24-Aug-2016.) $)
    barbara $p |- A. x ( ch -> ps ) $=
      ( wi wal alsyl mp2an ) CAGDHABGDHCBGDHFECABDIJ $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism "Celarent", e.g.,
       "No reptiles have fur". $)
    celarent.maj $e |- A. x ( ph -> -. ps ) $.
    $( Minor premise for Celarent, e.g., "All snakes are reptiles". $)
    celarent.min $e |- A. x ( ch -> ph ) $.
    $( "Celarent", one of the syllogisms of Aristotelian logic.  No ` ph ` is
       ` ps ` , and all ` ch ` is ` ph ` , therefore no ` ch ` is ` ps ` .  (In
       Aristotelian notation, EAE-1:  MeP and SaM therefore SeP.) For example,
       given the "No reptiles have fur" and "All snakes are reptiles",
       therefore "No snakes have fur".  Example from
       ~ https://en.wikipedia.org/wiki/Syllogism .  (Contributed by David A.
       Wheeler, 24-Aug-2016.)  (Revised by David A. Wheeler, 2-Sep-2016.) $)
    celarent $p |- A. x ( ch -> -. ps ) $=
      ( wn barbara ) ABGCDEFH $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism "Darii", e.g.,
       "All rabbits have fur". $)
    darii.maj $e |- A. x ( ph -> ps ) $.
    $( Minor premise for Darii, e.g., "Some pets are rabbits." $)
    darii.min $e |- E. x ( ch /\ ph ) $.
    $( "Darii", one of the syllogisms of Aristotelian logic.  All ` ph ` is
       ` ps ` , and some ` ch ` is ` ph ` , therefore some ` ch ` is ` ps ` .
       (In Aristotelian notation, AII-1:  MaP and SiM therefore SiP.) For
       example, given "All rabbits have fur" and "Some pets are rabbits",
       therefore "Some pets have fur".  Example from
       ~ https://en.wikipedia.org/wiki/Syllogism .  (Contributed by David A.
       Wheeler, 24-Aug-2016.) $)
    darii $p |- E. x ( ch /\ ps ) $=
      ( wa wi spi anim2i eximii ) CAGCBGDFABCABHDEIJK $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism "Ferio" ("Ferioque"),
       e.g., "No homework is fun". $)
    ferio.maj $e |- A. x ( ph -> -. ps ) $.
    $( Minor premise for Ferio, e.g., "Some reading is homework." $)
    ferio.min $e |- E. x ( ch /\ ph ) $.
    $( "Ferio" ("Ferioque"), one of the syllogisms of Aristotelian logic.  No
       ` ph ` is ` ps ` , and some ` ch ` is ` ph ` , therefore some ` ch ` is
       not ` ps ` .  (In Aristotelian notation, EIO-1:  MeP and SiM therefore
       SoP.) For example, given "No homework is fun" and "Some reading is
       homework", therefore "Some reading is not fun".  This is essentially a
       logical axiom in Aristotelian logic.  Example from
       ~ https://en.wikipedia.org/wiki/Syllogism .  (Contributed by David A.
       Wheeler, 24-Aug-2016.)  (Revised by David A. Wheeler, 2-Sep-2016.) $)
    ferio $p |- E. x ( ch /\ -. ps ) $=
      ( wn darii ) ABGCDEFH $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism "Barbari", e.g.,
       e.g., "All men are mortal". $)
    barbari.maj $e |- A. x ( ph -> ps ) $.
    $( Minor premise for Barbari, e.g., "All Greeks are men." $)
    barbari.min $e |- A. x ( ch -> ph ) $.
    $( Existence premise for Barbari, e.g., "Greeks exist." $)
    barbari.e $e |- E. x ch $.
    $( "Barbari", one of the syllogisms of Aristotelian logic.  All ` ph ` is
       ` ps ` , all ` ch ` is ` ph ` , and some ` ch ` exist, therefore some
       ` ch ` is ` ps ` .  (In Aristotelian notation, AAI-1:  MaP and SaM
       therefore SiP.) For example, given "All men are mortal", "All Greeks are
       men", and "Greeks exist", therefore "Some Greeks are mortal".  Note the
       existence hypothesis (to prove the "some" in the conclusion).  Example
       from ~ https://en.wikipedia.org/wiki/Syllogism .  (Contributed by David
       A. Wheeler, 27-Aug-2016.)  (Revised by David A. Wheeler,
       30-Aug-2016.) $)
    barbari $p |- E. x ( ch /\ ps ) $=
      ( wa wi barbara spi ancli eximii ) CCBHDGCBCBIDABCDEFJKLM $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism "Celaront", e.g.,
       e.g., "No reptiles have fur". $)
    celaront.maj $e |- A. x ( ph -> -. ps ) $.
    $( Minor premise for Celaront, e.g., "All Snakes are reptiles." $)
    celaront.min $e |- A. x ( ch -> ph ) $.
    $( Existence premise for Celaront, e.g., "Snakes exist." $)
    celaront.e $e |- E. x ch $.
    $( "Celaront", one of the syllogisms of Aristotelian logic.  No ` ph ` is
       ` ps ` , all ` ch ` is ` ph ` , and some ` ch ` exist, therefore some
       ` ch ` is not ` ps ` .  (In Aristotelian notation, EAO-1:  MeP and SaM
       therefore SoP.) For example, given "No reptiles have fur", "All snakes
       are reptiles.", and "Snakes exist.", prove "Some snakes have no fur".
       Note the existence hypothesis.  Example from
       ~ https://en.wikipedia.org/wiki/Syllogism .  (Contributed by David A.
       Wheeler, 27-Aug-2016.)  (Revised by David A. Wheeler, 2-Sep-2016.) $)
    celaront $p |- E. x ( ch /\ -. ps ) $=
      ( wn barbari ) ABHCDEFGI $.
  $}

  $( Figure 2 $)

  ${
    $( Major premise for the Aristotelian syllogism "Cesare" $)
    cesare.maj $e |- A. x ( ph -> -. ps ) $.
    $( Minor premise for Cesare $)
    cesare.min $e |- A. x ( ch -> ps ) $.
    $( "Cesare", one of the syllogisms of Aristotelian logic.  No ` ph ` is
       ` ps ` , and all ` ch ` is ` ps ` , therefore no ` ch ` is ` ph ` .  (In
       Aristotelian notation, EAE-2:  PeM and SaM therefore SeP.) Related to
       ~ celarent .  (Contributed by David A. Wheeler, 27-Aug-2016.)  (Revised
       by David A. Wheeler, 13-Nov-2016.) $)
    cesare $p |- A. x ( ch -> -. ph ) $=
      ( wn wi spi nsyl3 ax-gen ) CAGHDABCABGHDEICBHDFIJK $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism "Camestres" $)
    camestres.maj $e |- A. x ( ph -> ps ) $.
    $( Minor premise for Camestres $)
    camestres.min $e |- A. x ( ch -> -. ps ) $.
    $( "Camestres", one of the syllogisms of Aristotelian logic.  All ` ph ` is
       ` ps ` , and no ` ch ` is ` ps ` , therefore no ` ch ` is ` ph ` .  In
       Aristotelian notation, AEE-2:  PaM and SeM therefore SeP. (Contributed
       by David A. Wheeler, 28-Aug-2016.)  (Revised by David A. Wheeler,
       2-Sep-2016.) $)
    camestres $p |- A. x ( ch -> -. ph ) $=
      ( wn wi spi nsyl ax-gen ) CAGHDCBACBGHDFIABHDEIJK $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism "Festino" $)
    festino.maj $e |- A. x ( ph -> -. ps ) $.
    $( Minor premise for Festino $)
    festino.min $e |- E. x ( ch /\ ps ) $.
    $( "Festino", one of the syllogisms of Aristotelian logic.  No ` ph ` is
       ` ps ` , and some ` ch ` is ` ps ` , therefore some ` ch ` is not
       ` ph ` .  (In Aristotelian notation, EIO-2:  PeM and SiM therefore SoP.)
       (Contributed by David A. Wheeler, 25-Nov-2016.) $)
    festino $p |- E. x ( ch /\ -. ph ) $=
      ( wa wn wi spi con2i anim2i eximii ) CBGCAHZGDFBNCABABHIDEJKLM $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism "Baroco" $)
    baroco.maj $e |- A. x ( ph -> ps ) $.
    $( Minor premise for Baroco $)
    baroco.min $e |- E. x ( ch /\ -. ps ) $.
    $( "Baroco", one of the syllogisms of Aristotelian logic.  All ` ph ` is
       ` ps ` , and some ` ch ` is not ` ps ` , therefore some ` ch ` is not
       ` ph ` .  (In Aristotelian notation, AOO-2:  PaM and SoM therefore SoP.)
       For example, "All informative things are useful", "Some websites are not
       useful", therefore "Some websites are not informative".  (Contributed by
       David A. Wheeler, 28-Aug-2016.) $)
    baroco $p |- E. x ( ch /\ -. ph ) $=
      ( wn wa wi spi con3i anim2i eximii ) CBGZHCAGZHDFNOCABABIDEJKLM $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism "Cesaro" $)
    cesaro.maj $e |- A. x ( ph -> -. ps ) $.
    $( Minor premise for Cesaro $)
    cesaro.min $e |- A. x ( ch -> ps ) $.
    $( Existence premise for Cesaro $)
    cesaro.e $e |- E. x ch $.
    $( "Cesaro", one of the syllogisms of Aristotelian logic.  No ` ph ` is
       ` ps ` , all ` ch ` is ` ps ` , and ` ch ` exist, therefore some ` ch `
       is not ` ph ` .  In Aristotelian notation, EAO-2:  PeM and SaM therefore
       SoP. (Contributed by David A. Wheeler, 28-Aug-2016.)  (Revised by David
       A. Wheeler, 2-Sep-2016.) $)
    cesaro $p |- E. x ( ch /\ -. ph ) $=
      ( wn wa wi spi nsyl3 ancli eximii ) CCAHZIDGCOABCABHJDEKCBJDFKLMN $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism "Camestros" $)
    camestros.maj $e |- A. x ( ph -> ps ) $.
    $( Minor premise for  $)
    camestros.min $e |- A. x ( ch -> -. ps ) $.
    $( Existence premise for Camestros $)
    camestros.e $e |- E. x ch $.
    $( "Camestros", one of the syllogisms of Aristotelian logic.  All ` ph ` is
       ` ps ` , no ` ch ` is ` ps ` , and ` ch ` exist, therefore some ` ch `
       is not ` ph ` .  (In Aristotelian notation, AEO-2:  PaM and SeM
       therefore SoP.) For example, "All horses have hooves", "No humans have
       hooves", and humans exist, therefore "Some humans are not horses".
       (Contributed by David A. Wheeler, 28-Aug-2016.)  (Revised by David A.
       Wheeler, 2-Sep-2016.) $)
    camestros $p |- E. x ( ch /\ -. ph ) $=
      ( wn wa wi spi nsyl ancli eximii ) CCAHZIDGCOCBACBHJDFKABJDEKLMN $.
  $}

  $( Figure 3 $)

  ${
    $( Major premise for the Aristotelian syllogism "Datisi" $)
    datisi.maj $e |- A. x ( ph -> ps ) $.
    $( Minor premise for  $)
    datisi.min $e |- E. x ( ph /\ ch ) $.
    $( "Datisi", one of the syllogisms of Aristotelian logic.  All ` ph ` is
       ` ps ` , and some ` ph ` is ` ch ` , therefore some ` ch ` is ` ps ` .
       (In Aristotelian notation, AII-3:  MaP and MiS therefore SiP.)
       (Contributed by David A. Wheeler, 28-Aug-2016.) $)
    datisi $p |- E. x ( ch /\ ps ) $=
      ( wa simpr wi spi adantr jca eximii ) ACGZCBGDFNCBACHABCABIDEJKLM $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism "Disamis" $)
    disamis.maj $e |- E. x ( ph /\ ps ) $.
    $( Minor premise for  $)
    disamis.min $e |- A. x ( ph -> ch ) $.
    $( "Disamis", one of the syllogisms of Aristotelian logic.  Some ` ph ` is
       ` ps ` , and all ` ph ` is ` ch ` , therefore some ` ch ` is ` ps ` .
       (In Aristotelian notation, IAI-3:  MiP and MaS therefore SiP.)
       (Contributed by David A. Wheeler, 28-Aug-2016.) $)
    disamis $p |- E. x ( ch /\ ps ) $=
      ( wa wi spi anim1i eximii ) ABGCBGDEACBACHDFIJK $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism "Ferison" $)
    ferison.maj $e |- A. x ( ph -> -. ps ) $.
    $( Minor premise for  $)
    ferison.min $e |- E. x ( ph /\ ch ) $.
    $( "Ferison", one of the syllogisms of Aristotelian logic.  No ` ph ` is
       ` ps ` , and some ` ph ` is ` ch ` , therefore some ` ch ` is not
       ` ps ` .  (In Aristotelian notation, EIO-3:  MeP and MiS therefore SoP.)
       (Contributed by David A. Wheeler, 28-Aug-2016.)  (Revised by David A.
       Wheeler, 2-Sep-2016.) $)
    ferison $p |- E. x ( ch /\ -. ps ) $=
      ( wn datisi ) ABGCDEFH $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism "Bocardo" $)
    bocardo.maj $e |- E. x ( ph /\ -. ps ) $.
    $( Minor premise for  $)
    bocardo.min $e |- A. x ( ph -> ch ) $.
    $( "Bocardo", one of the syllogisms of Aristotelian logic.  Some ` ph ` is
       not ` ps ` , and all ` ph ` is ` ch ` , therefore some ` ch ` is not
       ` ps ` .  (In Aristotelian notation, OAO-3:  MoP and MaS therefore SoP.)
       For example, "Some cats have no tails", "All cats are mammals",
       therefore "Some mammals have no tails".  A reorder of ~ disamis ; prefer
       using that instead.  (Contributed by David A. Wheeler, 28-Aug-2016.)
       (New usage is discouraged.) $)
    bocardo $p |- E. x ( ch /\ -. ps ) $=
      ( wn disamis ) ABGCDEFH $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism "Felapton" $)
    felapton.maj $e |- A. x ( ph -> -. ps ) $.
    $( Minor premise for  $)
    felapton.min $e |- A. x ( ph -> ch ) $.
    $( Existence premise for Felapton $)
    felapton.e $e |- E. x ph $.
    $( "Felapton", one of the syllogisms of Aristotelian logic.  No ` ph ` is
       ` ps ` , all ` ph ` is ` ch ` , and some ` ph ` exist, therefore some
       ` ch ` is not ` ps ` .  (In Aristotelian notation, EAO-3:  MeP and MaS
       therefore SoP.) For example, "No flowers are animals" and "All flowers
       are plants", therefore "Some plants are not animals".  (Contributed by
       David A. Wheeler, 28-Aug-2016.)  (Revised by David A. Wheeler,
       2-Sep-2016.) $)
    felapton $p |- E. x ( ch /\ -. ps ) $=
      ( wn wa wi spi jca eximii ) ACBHZIDGACNACJDFKANJDEKLM $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism "Darapti" $)
    darapti.maj $e |- A. x ( ph -> ps ) $.
    $( Minor premise for  $)
    darapti.min $e |- A. x ( ph -> ch ) $.
    $( Existence premise for Darapti $)
    darapti.e $e |- E. x ph $.
    $( "Darapti", one of the syllogisms of Aristotelian logic.  All ` ph ` is
       ` ps ` , all ` ph ` is ` ch ` , and some ` ph ` exist, therefore some
       ` ch ` is ` ps ` .  (In Aristotelian notation, AAI-3:  MaP and MaS
       therefore SiP.) For example, "All squares are rectangles" and "All
       squares are rhombuses", therefore "Some rhombuses are rectangles".
       (Contributed by David A. Wheeler, 28-Aug-2016.) $)
    darapti $p |- E. x ( ch /\ ps ) $=
      ( wa wi spi jca eximii ) ACBHDGACBACIDFJABIDEJKL $.
  $}

  $( Figure 4 $)

  ${
    $( Major premise for the Aristotelian syllogism "Calemes" $)
    calemes.maj $e |- A. x ( ph -> ps ) $.
    $( Minor premise for  $)
    calemes.min $e |- A. x ( ps -> -. ch ) $.
    $( "Calemes", one of the syllogisms of Aristotelian logic.  All ` ph ` is
       ` ps ` , and no ` ps ` is ` ch ` , therefore no ` ch ` is ` ph ` .  In
       Aristotelian notation, AEE-4:  PaM and MeS therefore SeP. (Contributed
       by David A. Wheeler, 28-Aug-2016.)  (Revised by David A. Wheeler,
       2-Sep-2016.) $)
    calemes $p |- A. x ( ch -> -. ph ) $=
      ( wn wi spi con2i nsyl ax-gen ) CAGHDCBABCBCGHDFIJABHDEIKL $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism "Dimatis" $)
    dimatis.maj $e |- E. x ( ph /\ ps ) $.
    $( Minor premise for  $)
    dimatis.min $e |- A. x ( ps -> ch ) $.
    $( "Dimatis", one of the syllogisms of Aristotelian logic.  Some ` ph ` is
       ` ps ` , and all ` ps ` is ` ch ` , therefore some ` ch ` is ` ph ` .
       (In Aristotelian notation, IAI-4:  PiM and MaS therefore SiP.) For
       example, "Some pets are rabbits.", "All rabbits have fur", therefore
       "Some fur bearing animals are pets".  Like ~ darii with positions
       interchanged.  (Contributed by David A. Wheeler, 28-Aug-2016.) $)
    dimatis $p |- E. x ( ch /\ ph ) $=
      ( wa wi spi adantl simpl jca eximii ) ABGZCAGDENCABCABCHDFIJABKLM $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism "Fresison" $)
    fresison.maj $e |- A. x ( ph -> -. ps ) $.
    $( Minor premise for  $)
    fresison.min $e |- E. x ( ps /\ ch ) $.
    $( "Fresison", one of the syllogisms of Aristotelian logic.  No ` ph ` is
       ` ps ` (PeM), and some ` ps ` is ` ch ` (MiS), therefore some ` ch ` is
       not ` ph ` (SoP).  In Aristotelian notation, EIO-4:  PeM and MiS
       therefore SoP. (Contributed by David A. Wheeler, 28-Aug-2016.)  (Revised
       by David A. Wheeler, 2-Sep-2016.) $)
    fresison $p |- E. x ( ch /\ -. ph ) $=
      ( wa wn simpr wi spi con2i adantr jca eximii ) BCGZCAHZGDFPCQBCIBQCABABHJ
      DEKLMNO $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism "Calemos" $)
    calemos.maj $e |- A. x ( ph -> ps ) $.
    $( Minor premise for  $)
    calemos.min $e |- A. x ( ps -> -. ch ) $.
    $( Existence premise for Calemos $)
    calemos.e $e |- E. x ch $.
    $( "Calemos", one of the syllogisms of Aristotelian logic.  All ` ph ` is
       ` ps ` (PaM), no ` ps ` is ` ch ` (MeS), and ` ch ` exist, therefore
       some ` ch ` is not ` ph ` (SoP).  In Aristotelian notation, AEO-4:  PaM
       and MeS therefore SoP. (Contributed by David A. Wheeler, 28-Aug-2016.)
       (Revised by David A. Wheeler, 2-Sep-2016.) $)
    calemos $p |- E. x ( ch /\ -. ph ) $=
      ( wn wa wi spi con2i nsyl ancli eximii ) CCAHZIDGCPCBABCBCHJDFKLABJDEKMNO
      $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism "Fesapo" $)
    fesapo.maj $e |- A. x ( ph -> -. ps ) $.
    $( Minor premise for  $)
    fesapo.min $e |- A. x ( ps -> ch ) $.
    $( Existence premise for Fesapo $)
    fesapo.e $e |- E. x ps $.
    $( "Fesapo", one of the syllogisms of Aristotelian logic.  No ` ph ` is
       ` ps ` , all ` ps ` is ` ch ` , and ` ps ` exist, therefore some ` ch `
       is not ` ph ` .  In Aristotelian notation, EAO-4:  PeM and MaS therefore
       SoP. (Contributed by David A. Wheeler, 28-Aug-2016.)  (Revised by David
       A. Wheeler, 2-Sep-2016.) $)
    fesapo $p |- E. x ( ch /\ -. ph ) $=
      ( wn wa wi spi con2i jca eximii ) BCAHZIDGBCOBCJDFKABABHJDEKLMN $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism "Bamalip" $)
    bamalip.maj $e |- A. x ( ph -> ps ) $.
    $( Minor premise for  $)
    bamalip.min $e |- A. x ( ps -> ch ) $.
    $( Existence premise for Bamalip $)
    bamalip.e $e |- E. x ph $.
    $( "Bamalip", one of the syllogisms of Aristotelian logic.  All ` ph ` is
       ` ps ` , all ` ps ` is ` ch ` , and ` ph ` exist, therefore some ` ch `
       is ` ph ` .  (In Aristotelian notation, AAI-4:  PaM and MaS therefore
       SiP.) Like ~ barbari .  (Contributed by David A. Wheeler,
       28-Aug-2016.) $)
    bamalip $p |- E. x ( ch /\ ph ) $=
      ( wa wi spi syl ancri eximii ) ACAHDGACABCABIDEJBCIDFJKLM $.
  $}


$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  First-order logic with one non-logical binary predicate
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#

  This section adds one non-logical binary predicate to the first-order logic
  developed until here.  We call it "the membership predicate" since it will
  be used in the next part as the membership predicate of set theory, but in
  this section, it has no other property than being "a binary predicate".
  "Non-logical" means that it does not belong to the logic.  In our logic (and
  in most treatments), the only logical predicate is the equality predicate
  (see ~ weq ).

$)

  $( Declare the membership predicate symbol. $)
  $c e. $.  $( Stylized lowercase Greek letter epsilon. $)

  ${
    $v A $.
    $v B $.
    wcel.cA $f class A $.
    wcel.cB $f class B $.
    $( Extend wff definition to include the membership connective between
       classes.

       For a general discussion of the theory of classes, see
       ~ mmset.html#class .

       The purpose of introducing ` wff A e. B ` here is to allow us to prove
       the ~ wel of predicate calculus in terms of the ~ wceq of set theory, so
       that we do not overload the ` e. ` connective with two syntax
       definitions.  This is done to prevent ambiguity that would complicate
       some Metamath parsers.  The class variables ` A ` and ` B ` are
       introduced temporarily for the purpose of this definition but otherwise
       not used in predicate calculus.  See ~ df-clab for more information on
       the set theory usage of ~ wcel . $)
    wcel $a wff A e. B $.
  $}

  $( Extend wff definition to include atomic formulas with the membership
     predicate.  This is read either " ` x ` is an element of ` y ` ",
     or " ` x ` is a member of ` y ` ", or " ` x ` belongs to ` y ` ",
     or " ` y ` contains ` x ` ".  Note:  The phrase " ` y ` includes
     ` x ` " means " ` x ` is a subset of ` y ` "; to use it also for
     ` x e. y ` , as some authors occasionally do, is poor form and causes
     confusion, according to George Boolos (1992 lecture at MIT).

     This syntactical construction introduces a binary non-logical predicate
     symbol ` e. ` into our predicate calculus.  We will eventually use it for
     the membership predicate of set theory, but that is irrelevant at this
     point: the predicate calculus axioms for ` e. ` apply to any arbitrary
     binary predicate symbol.  "Non-logical" means that the predicate is
     presumed to have additional properties beyond the realm of predicate
     calculus, although these additional properties are not specified by
     predicate calculus itself but rather by the axioms of a theory (in our
     case set theory) added to predicate calculus.  "Binary" means that the
     predicate has two arguments.

     Instead of introducing ~ wel as an axiomatic statement, as was done in an
     older version of this database, we introduce it by "proving" a special
     case of set theory's more general ~ wcel .  This lets us avoid overloading
     the ` e. ` connective, thus preventing ambiguity that would complicate
     certain Metamath parsers.  However, logically ~ wel is considered to be a
     primitive syntax, even though here it is artificially "derived" from
     ~ wcel .  Note:  To see the proof steps of this syntax proof, type "MM>
     SHOW PROOF wel / ALL" in the Metamath program.  (Contributed by NM,
     24-Jan-2006.) $)
  wel $p wff x e. y $=
    ( cv wcel ) ACBCD $.

  $( Axiom of left equality for the binary predicate ` e. ` .  One of the
     equality and substitution axioms for a non-logical predicate in our
     predicate calculus with equality.  It substitutes equal variables into the
     left-hand side of the ` e. ` binary predicate.  Axiom scheme C12' in
     [Megill] p. 448 (p. 16 of the preprint).  It is a special case of Axiom B8
     (p. 75) of system S2 of [Tarski] p. 77.  "Non-logical" means that the
     predicate is not a primitive of predicate calculus proper but instead is
     an extension to it.  "Binary" means that the predicate has two arguments.
     In a system of predicate calculus with equality, like ours, equality is
     not usually considered to be a non-logical predicate.  In systems of
     predicate calculus without equality, it typically would be.  (Contributed
     by NM, 5-Aug-1993.) $)
  ax-13 $a |- ( x = y -> ( x e. z -> y e. z ) ) $.

  $( Axiom of right equality for the binary predicate ` e. ` .  One of the
     equality and substitution axioms for a non-logical predicate in our
     predicate calculus with equality.  It substitutes equal variables into the
     right-hand side of the ` e. ` binary predicate.  Axiom scheme C13' in
     [Megill] p. 448 (p. 16 of the preprint).  It is a special case of Axiom B8
     (p. 75) of system S2 of [Tarski] p. 77.  (Contributed by NM,
     5-Aug-1993.) $)
  ax-14 $a |- ( x = y -> ( z e. x -> z e. y ) ) $.

  $( An identity law for the non-logical predicate.  (Contributed by NM,
     5-Aug-1993.) $)
  elequ1 $p |- ( x = y -> ( x e. z <-> y e. z ) ) $=
    ( weq wel ax-13 wi equcoms impbid ) ABDACEZBCEZABCFKJGBABACFHI $.

  $( An identity law for the non-logical predicate.  (Contributed by NM,
     5-Aug-1993.) $)
  elequ2 $p |- ( x = y -> ( z e. x <-> z e. y ) ) $=
    ( weq wel ax-14 wi equcoms impbid ) ABDCAEZCBEZABCFKJGBABACFHI $.

  ${
    $d x z $.  $d y z $.
    $( When the class variables of set theory are replaced with setvar
       variables, this theorem of predicate calculus is the result.  This
       theorem provides part of the justification for the consistency of that
       definition, which "overloads" the setvar variables in ~ wel with the
       class variables in ~ wcel .  (Contributed by NM, 28-Jan-2004.) $)
    cleljust $p |- ( x e. y <-> E. z ( z = x /\ z e. y ) ) $=
      ( weq wel wa wex ax-17 elequ1 equsex bicomi ) CADCBEZFCGABEZLMCAMCHCABIJK
      $.
  $}

  ${
    $d w x z $.  $d w y $.
    $( Substitution for the first argument of the non-logical predicate in an
       atomic formula.  See ~ elsb2 for substitution for the second argument.
       (Contributed by NM, 7-Nov-2006.)  (Proof shortened by Andrew Salmon,
       14-Jun-2011.) $)
    elsb1 $p |- ( [ y / x ] x e. z <-> y e. z ) $=
      ( vw wel wsb ax-17 elequ1 sbieh sbbii sbco2h bitr3i wb equsb1 sbimi ax-mp
      weq sbbi mpbi sbh 3bitri ) ACEZABFZDCEZDBFZBCEZDBFZUFUCUDDAFZABFUEUHUBABU
      DUBDAUBDGDACHIJUDDBAUDAGKLUDUFMZDBFZUEUGMDBQZDBFUJDBNUKUIDBDBCHOPUDUFDBRS
      UFDBUFDGTUA $.
  $}

  ${
    $d w x z $.  $d w y $.
    $( Substitution for the second argument of the non-logical predicate in an
       atomic formula.  See ~ elsb1 for substitution for the first argument.
       (Contributed by Rodolfo Medina, 3-Apr-2010.)  (Proof shortened by Andrew
       Salmon, 14-Jun-2011.) $)
    elsb2 $p |- ( [ y / x ] z e. x <-> z e. y ) $=
      ( vw wel wsb ax-17 elequ2 sbieh sbbii sbco2h bitr3i wb equsb1 sbimi ax-mp
      weq sbbi mpbi sbh 3bitri ) CAEZABFZCDEZDBFZCBEZDBFZUFUCUDDAFZABFUEUHUBABU
      DUBDAUBDGDACHIJUDDBAUDAGKLUDUFMZDBFZUEUGMDBQZDBFUJDBNUKUIDBDBCHOPUDUFDBRS
      UFDBUFDGTUA $.
  $}

  ${
    $d w z x $.  $d w y $.
    $( Quantifier introduction when one pair of variables is disjoint.
       (Contributed by NM, 2-Jan-2002.) $)
    dveel1 $p |- ( -. A. x x = y -> ( y e. z -> A. x y e. z ) ) $=
      ( vw wel ax-17 elequ1 dvelimf ) DCEZBCEZABDIAFJDFDBCGH $.
  $}

  ${
    $d w z x $.  $d w y $.
    $( Quantifier introduction when one pair of variables is disjoint.
       (Contributed by NM, 2-Jan-2002.) $)
    dveel2 $p |- ( -. A. x x = y -> ( z e. y -> A. x z e. y ) ) $=
      ( vw wel ax-17 elequ2 dvelimf ) CDEZCBEZABDIAFJDFDBCGH $.
  $}

