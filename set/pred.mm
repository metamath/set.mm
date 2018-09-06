
$(
###############################################################################
            CLASSICAL FIRST ORDER LOGIC WITH EQUALITY
###############################################################################

  Logic can be defined as the "study of the principles of correct reasoning"
  (Merrilee H. Salmon's 1991 "Informal Reasoning and Informal Logic" in
  _Informal Reasoning and Education_ ) or as "a formal system using symbolic
  techniques and mathematical methods to establish truth-values" (the Oxford
  English Dictionary).

  This section formally defines the logic system we will use.  In particular,
  it defines symbols for declaring truthful statements, along with rules for
  deriving truthful statements from other truthful statements.  The system
  defined here is classical first order logic with equality (the most common
  logic system used by mathematicians).

  We begin with a few housekeeping items in pre-logic, and then introduce
  propositional calculus (both its axioms and important theorems that can be
  derived from them).  Propositional calculus deals with general truths about
  well-formed formulas (wffs) regardless of how they are constructed.  This is
  followed by proofs that other axiomatizations of classical propositional
  calculus can be derived from the axioms we have chosen to use.

  We then define predicate calculus, which adds additional symbols and rules
  useful for discussing objects (beyond simply true or false).  In particular,
  it introduces the symbols ` = ` ("equals"), ` e. ` ("is a member of"), and `
  A. ` ("for all").  The first two are called "predicates."  A predicate
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
  $c -> $. $( Right arrow (read:  "implies") $)
  $c -. $. $( Right handle (read:  "not") $)
  $c wff $. $( Well-formed formula symbol (read:  "the following symbol
               sequence is a wff") $)
  $c |- $. $( Turnstile (read:  "the following symbol sequence is provable" or
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
$)

  ${
    dummylink.1 $e |- ph $.
    dummylink.2 $e |- ps $.
    $( (_Note_:  This inference rule and the next one, ~ idi , will normally
       never appear in a completed proof.  It can be ignored if you are using
       this database to assist learning logic - please start with the statement
       ~ wn instead.)

       This is a technical inference to assist proof development.  It provides
       a temporary way to add an independent subproof to a proof under
       development, for later assignment to a normal proof step.

       The metamath program's Proof Assistant requires proofs to be developed
       backwards from the conclusion with no gaps, and it has no mechanism that
       lets the user to work on isolated subproofs.  This inference provides a
       workaround for this limitation.  It can be inserted at any point in a
       proof to allow an independent subproof to be developed on the side, for
       later use as part of the final proof.

       _Instructions_:  (1) Assign this inference to any unknown step in the
       proof.  Typically, the last unknown step is the most convenient, since
       'assign last' can be used.  This step will be replicated in hypothesis
       dummylink.1, from where the development of the main proof can continue.
       (2) Develop the independent subproof backwards from hypothesis
       dummylink.2.  If desired, use a 'let' command to pre-assign the
       conclusion of the independent subproof to dummylink.2.  (3) After the
       independent subproof is complete, use 'improve all' to assign it
       automatically to an unknown step in the main proof that matches it.  (4)
       After the entire proof is complete, use 'minimize *' to clean up
       (discard) all dummylink references automatically.

       This inference was originally designed to assist importing partially
       completed Proof Worksheets from the mmj2 Proof Assistant GUI, but it can
       also be useful on its own.  Interestingly, no axioms are required for
       its proof.  (Contributed by NM, 7-Feb-2006.) $)
    dummylink $p |- ph $=
      (  ) C $.
  $}

  ${
    idi.1 $e |- ph $.
    $( Inference form of ~ id .  This inference rule, which requires no axioms
       for its proof, is useful as a copy-paste mechanism during proof
       development in mmj2.  It is normally not referenced in the final version
       of a proof, since it is always redundant and can be removed using the
       'minimize *' command in the metamath program's Proof Assistant.
       (Contributed by Alan Sare, 31-Dec-2011.) $)
    idi $p |- ph $=
      (  ) B $.
  $}

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
                           Propositional calculus
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#

  Propositional calculus deals with general truths about well-formed formulas
  (wffs) regardless of how they are constructed.  The simplest propositional
  truth is ` ( ph -> ph ) ` , which can be read "if something is true, then it
  is true" - rather trivial and obvious, but nonetheless it must be proved from
  the axioms (see theorem ~ id ).

  Our system of propositional calculus consists of three basic axioms and
  another axiom that defines the modus-ponens inference rule.  It is attributed
  to Jan Lukasiewicz (pronounced woo-kah-SHAY-vitch) and was popularized by
  Alonzo Church, who called it system P2.  (Thanks to Ted Ulrich for this
  information.)  These axioms are ~ ax-1 , ~ ax-2 , ~ ax-3 , and (for modus
  ponens) ~ ax-mp . Some closely followed texts include [Margaris] for the
  axioms and [WhiteheadRussell] for the theorems.

  The propositional calculus used here is the classical system widely used by
  mathematicians.  In particular, this logic system accepts the "law of the
  excluded middle" as proven in ~ exmid , which says that a logical statement
  is either true or not true.  This is an essential distinction of classical
  logic and is not a theorem of intuitionistic logic.

  All 194 axioms, definitions, and theorems for propositional calculus in
  _Principia Mathematica_ (specifically *1.2 through *5.75) are axioms or
  formally proven.  See the Bibliographic Cross-References at
  ~ http://us.metamath.org/mpeuni/mmbiblio.html for a complete
  cross-reference from sources used to its formalization in the Metamath
  Proof Explorer.

$)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Recursively define primitive wffs for propositional calculus
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( If ` ph ` is a wff, so is ` -. ph ` or "not ` ph ` ."  Part of the
     recursive definition of a wff (well-formed formula).  In classical logic
     (which is our logic), a wff is interpreted as either true or false.  So if
     ` ph ` is true, then ` -. ph ` is false; if ` ph ` is false, then
     ` -. ph ` is true.  Traditionally, Greek letters are used to represent
     wffs, and we follow this convention.  In propositional calculus, we define
     only wffs built up from other wffs, i.e. there is no starting or "atomic"
     wff.  Later, in predicate calculus, we will extend the basic wff
     definition by including atomic wffs ( ~ weq and ~ wel ). $)
  wn $a wff -. ph $.

  $( If ` ph ` and ` ps ` are wff's, so is ` ( ph -> ps ) ` or " ` ph ` implies
     ` ps ` ."  Part of the recursive definition of a wff.  The resulting wff
     is (interpreted as) false when ` ph ` is true and ` ps ` is false; it is
     true otherwise.  Think of the truth table for an OR gate with input ` ph `
     connected through an inverter.  After we define the axioms of
     propositional calculus ( ~ ax-1 , ~ ax-2 , ~ ax-3 , and ~ ax-mp ), the
     biconditional ( ~ df-bi ), the constant true ` T. ` ( ~ df-tru ), and the
     constant false ` F. ` ( ~ df-fal ), we will be able to prove these truth
     table values: ` ( ( T. -> T. ) <-> T. ) ` ( ~ truimtru ),
     ` ( ( T. -> F. ) <-> F. ) ` ( ~ truimfal ), ` ( ( F. -> T. ) <-> T. ) `
     ( ~ falimtru ), and ` ( ( F. -> F. ) <-> T. ) ` ( ~ falimfal ).  These
     have straightforward meanings, for example, ` ( ( T. -> T. ) <-> T. ) `
     just means "the value of ` T. -> T. ` is ` T. ` ".

     The left-hand wff is called the antecedent, and the right-hand wff is
     called the consequent.  In the case of ` ( ph -> ( ps -> ch ) ) ` , the
     middle ` ps ` may be informally called either an antecedent or part of the
     consequent depending on context.  Contrast with ` <-> ` ( ~ df-bi ),
     ` /\ ` ( ~ df-an ), and ` \/ ` ( ~ df-or ).

     This is called "material implication" and the arrow is usually read as
     "implies."  However, material implication is not identical to the meaning
     of "implies" in natural language.  For example, the word "implies" may
     suggest a causal relationship in natural language.  Material implication
     does not require any causal relationship.  Also, note that in material
     implication, if the consequent is true then the wff is always true (even
     if the antecedent is false).  Thus, if "implies" means material
     implication, it is true that "if the moon is made of green cheese that
     implies that 5=5" (because 5=5).  Similarly, if the antecedent is false,
     the wff is always true.  Thus, it is true that, "if the moon made of green
     cheese that implies that 5=7" (because the moon is not actually made of
     green cheese).  A contradiction implies anything ( ~ pm2.21i ).  In short,
     material implication has a very specific technical definition, and
     misunderstandings of it are sometimes called "paradoxes of logical
     implication." $)
  wi $a wff ( ph -> ps ) $.

  $( Register '-.' and '->' as primitive expressions (lacking definitions). $)
  $( $j primitive 'wn' 'wi'; $)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        The axioms of propositional calculus
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  Propositional calculus (axioms ~ ax-1 through ~ ax-3 and rule ~ ax-mp ) can
  be thought of as asserting formulas that are universally "true" when their
  variables are replaced by any combination of "true" and "false."
  Propositional calculus was first formalized by Frege in 1879, using as his
  axioms (in addition to rule ~ ax-mp ) the wffs ~ ax-1 , ~ ax-2 , ~ pm2.04 ,
  ~ con3 , ~ notnot2 , and ~ notnot1 . Around 1930, Lukasiewicz simplified the
  system by eliminating the third (which follows from the first two, as you can
  see by looking at the proof of ~ pm2.04 ) and replacing the last three with
  our ~ ax-3 . (Thanks to Ted Ulrich for this information.)

  The theorems of propositional calculus are also called _tautologies_.
  Tautologies can be proved very simply using truth tables, based on the
  true/false interpretation of propositional calculus.  To do this, we assign
  all possible combinations of true and false to the wff variables and verify
  that the result (using the rules described in ~ wi and ~ wn ) always
  evaluates to true.  This is called the _semantic_ approach.  Our approach is
  called the _syntactic_ approach, in which everything is derived from axioms.
  A metatheorem called the Completeness Theorem for Propositional Calculus
  shows that the two approaches are equivalent and even provides an algorithm
  for automatically generating syntactic proofs from a truth table.  Those
  proofs, however, tend to be long, since truth tables grow exponentially with
  the number of variables, and the much shorter proofs that we show here were
  found manually.

$)

  ${
    $( Minor premise for modus ponens. $)
    min $e |- ph $.
    $( Major premise for modus ponens. $)
    maj $e |- ( ph -> ps ) $.
    $( Rule of Modus Ponens.  The postulated inference rule of propositional
       calculus.  See e.g.  Rule 1 of [Hamilton] p. 73.  The rule says, "if
       ` ph ` is true, and ` ph ` implies ` ps ` , then ` ps ` must also be
       true."  This rule is sometimes called "detachment," since it detaches
       the minor premise from the major premise.  "Modus ponens" is short for
       "modus ponendo ponens," a Latin phrase that means "the mood that by
       affirming affirms" - remark in [Sanford] p. 39.  This rule is similar to
       the rule of modus tollens ~ mto .

       Note:  In some web page displays such as the Statement List, the symbols
       "&" and "=>" informally indicate the relationship between the hypotheses
       and the assertion (conclusion), abbreviating the English words "and" and
       "implies."  They are not part of the formal language.  (Contributed by
       NM, 5-Aug-1993.) $)
    ax-mp $a |- ps $.
  $}

  $( Axiom _Simp_.  Axiom A1 of [Margaris] p. 49.  One of the 3 axioms of
     propositional calculus.  The 3 axioms are also given as Definition 2.1 of
     [Hamilton] p. 28.  This axiom is called _Simp_ or "the principle of
     simplification" in _Principia Mathematica_ (Theorem *2.02 of
     [WhiteheadRussell] p. 100) because "it enables us to pass from the joint
     assertion of ` ph ` and ` ps ` to the assertion of ` ph ` simply."
     (Contributed by NM, 5-Aug-1993.) $)
  ax-1 $a |- ( ph -> ( ps -> ph ) ) $.

  $( Axiom _Frege_.  Axiom A2 of [Margaris] p. 49.  One of the 3 axioms of
     propositional calculus.  It "distributes" an antecedent over two
     consequents.  This axiom was part of Frege's original system and is known
     as _Frege_ in the literature.  It is also proved as Theorem *2.77 of
     [WhiteheadRussell] p. 108.  The other direction of this axiom also turns
     out to be true, as demonstrated by ~ pm5.41 .  (Contributed by NM,
     5-Aug-1993.) $)
  ax-2 $a |- ( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) ) ) $.

  $( Axiom _Transp_.  Axiom A3 of [Margaris] p. 49.  One of the 3 axioms of
     propositional calculus.  It swaps or "transposes" the order of the
     consequents when negation is removed.  An informal example is that the
     statement "if there are no clouds in the sky, it is not raining" implies
     the statement "if it is raining, there are clouds in the sky."  This axiom
     is called _Transp_ or "the principle of transposition" in _Principia
     Mathematica_ (Theorem *2.17 of [WhiteheadRussell] p. 103).  We will also
     use the term "contraposition" for this principle, although the reader is
     advised that in the field of philosophical logic, "contraposition" has a
     different technical meaning.  (Contributed by NM, 5-Aug-1993.) $)
  ax-3 $a |- ( ( -. ph -> -. ps ) -> ( ps -> ph ) ) $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Logical implication
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  The results in this section are based on implication only, and avoid
  ax-3, so are intuitionistic.  In an implication, the wff before the
  arrow is called the "antecedent" and the wff after the arrow is called
  the "consequent."

  We will use the following descriptive terms very loosely:  A "closed form" or
  "tautology" has no $e hypotheses.  An "inference" has one or more $e
  hypotheses.  A "deduction" is an inference in which the hypotheses and the
  conclusion share the same antecedent.

$)

  ${
    mp2.1 $e |- ph $.
    mp2.2 $e |- ps $.
    mp2.3 $e |- ( ph -> ( ps -> ch ) ) $.
    $( A double modus ponens inference.  See ~ mp2ALT for a shorter proof using
       two more axioms.  (Contributed by NM, 5-Apr-1994.)
       (Proof modification is discouraged.) $)
    mp2 $p |- ch $=
      ( wi ax-mp ) BCEABCGDFHH $.
  $}

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
    $( Inference derived from axiom ~ ax-1 .  See ~ a1d for an explanation of
       our informal use of the terms "inference" and "deduction."  See also the
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
    $( Inference derived from axiom ~ ax-2 .  (Contributed by NM,
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
    $( A modus ponens deduction.  A translation of natural deduction rule
       ` -> ` E ( ` -> ` elimination), see ~ natded .  (Contributed by NM,
       5-Aug-1993.) $)
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
       call this law a "hypothetical syllogism."

       (A bit of trivia: this is the most commonly referenced assertion in our
       database.  In second place is ~ eqid , followed by ~ syl2anc ,
       ~ adantr , ~ syl3anc , and ~ ax-mp .  The Metamath program command 'show
       usage' shows the number of references.)  (Contributed by NM,
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
    mp2ALT.1 $e |- ph $.
    mp2ALT.2 $e |- ps $.
    mp2ALT.3 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Alternate proof of ~ mp2 (shorter but uses two more axioms).
       (Contributed by Wolf Lammen, 23-Jul-2013.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    mp2ALT $p |- ch $=
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
       "discouraged" because it causes the "minimize" command to have very long
       run times.  However, feel free to override it to use directly or in
       small "minimize" runs.  (Contributed by BJ, 14-Jul-2018.)
       (New usage is discouraged.) $)
    4syl $p |- ( ph -> ta ) $=
      ( 3syl syl ) ADEABCDFGHJIK $.
  $}

  $( Principle of identity.  Theorem *2.08 of [WhiteheadRussell] p. 101.  For
     another version of the proof directly from axioms, see ~ id1 .
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
     ~ http://www.mathsci.appstate.edu/~~hirstjl/primer/hirst.pdf .  For a
     shorter version of the proof that takes advantage of previously proved
     theorems, see ~ id .  (Contributed by NM, 5-Aug-1993.)
     (New usage is discouraged.)  (Proof modification is discouraged.) $)
  id1 $p |- ( ph -> ph ) $=
    ( wi ax-1 ax-2 ax-mp ) AAABZBZFAACAFABBGFBAFCAFADEE $.

  $( Principle of identity with antecedent.  (Contributed by NM,
     26-Nov-1995.) $)
  idd $p |- ( ph -> ( ps -> ps ) ) $=
    ( wi id a1i ) BBCABDE $.

  ${
    a1d.1 $e |- ( ph -> ps ) $.
    $( Deduction introducing an embedded antecedent.

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
       form with "g" (for "more general") as in ~ uniex vs. ~ uniexg .
       (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Stefan Allan,
       20-Mar-2006.) $)
    a1d $p |- ( ph -> ( ch -> ps ) ) $=
      ( wi ax-1 syl ) ABCBEDBCFG $.
  $}

  ${
    a2d.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    $( Deduction distributing an embedded antecedent.  (Contributed by NM,
       23-Jun-1994.) $)
    a2d $p |- ( ph -> ( ( ps -> ch ) -> ( ps -> th ) ) ) $=
      ( wi ax-2 syl ) ABCDFFBCFBDFFEBCDGH $.
  $}

  ${
    a1ii.1 $e |- ch $.
    $( Add two antecedents to a wff.  See ~ a1iiALT for a shorter proof using
       one more axiom.  (Contributed by Jeff Hankins, 4-Aug-2009.)
       (Proof modification is discouraged.) $)
    a1ii $p |- ( ph -> ( ps -> ch ) ) $=
      ( wi a1i ) BCEACBDFF $.
  $}

  ${
    a1iiALT.1 $e |- ch $.
    $( Alternate proof of ~ a1ii (shorter but uses one more axiom).
       (Contributed by Wolf Lammen, 23-Jul-2013.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    a1iiALT $p |- ( ph -> ( ps -> ch ) ) $=
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
    syl5.1 $e |- ( ph -> ps ) $.
    syl5.2 $e |- ( ch -> ( ps -> th ) ) $.
    $( A syllogism rule of inference.  The first premise is used to replace the
       second antecedent of the second premise.  (Contributed by NM,
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
    $( Syllogism deduction.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened
       by O'Cat, 19-Feb-2008.)  (Proof shortened by Wolf Lammen, 3-Aug-2012.)

       Notice that ~ syld has the same form as ~ syl with ` ph ` added in front
       of each hypothesis and conclusion.  When all theorems referenced in a
       proof are converted in this way, we can replace ` ph ` with a hypothesis
       of the proof, allowing the hypothesis to be eliminated with ~ id and
       become an antecedent.  The Deduction Theorem for propositional calculus,
       e.g.  Theorem 3 in [Margaris] p. 56, tells us that this procedure is
       always possible. $)
    syld $p |- ( ph -> ( ps -> th ) ) $=
      ( wi a1d mpdd ) ABCDEACDGBFHI $.
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
    $( Virtual deduction rule ~ e12 without virtual deduction symbols.
       (Contributed by Alan Sare, 20-Apr-2011.) $)
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
    $( A syllogism inference combined with contraction. ~ e111 without virtual
       deductions.  (Contributed by Alan Sare, 7-Jul-2011.) $)
    syl3c $p |- ( ph -> ta ) $=
      ( wi sylc mpd ) ADEHABCDEJFGIKL $.
  $}

  ${
    syl6mpi.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syl6mpi.2 $e |- th $.
    syl6mpi.3 $e |- ( ch -> ( th -> ta ) ) $.
    $( ~ e20 without virtual deductions.  (Contributed by Alan Sare,
       8-Jul-2011.)  (Proof shortened by Wolf Lammen, 13-Sep-2012.) $)
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
    $( A syllogism rule of inference.  The first premise is used to replace the
       third antecedent of the second premise.  (Contributed by NM,
       5-Aug-1993.)  (Proof shortened by Wolf Lammen, 3-Aug-2012.) $)
    syl7 $p |- ( ch -> ( th -> ( ph -> ta ) ) ) $=
      ( wi a1i syl5d ) CABDEABHCFIGJ $.
  $}

  ${
    syl6d.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    syl6d.2 $e |- ( ph -> ( th -> ta ) ) $.
    $( A nested syllogism deduction.  (Contributed by NM, 5-Aug-1993.)  (Proof
       shortened by Josh Purinton, 29-Dec-2000.)  (Proof shortened by O'Cat,
       2-Feb-2006.) $)
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
  pm2.83 $p |- ( ( ph -> ( ps -> ch ) )
      -> ( ( ph -> ( ch -> th ) ) -> ( ph -> ( ps -> th ) ) ) ) $=
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

  $( Elimination of a nested antecedent as a kind of reversal of inference
     ~ ja .  (Contributed by Wolf Lammen, 9-May-2013.) $)
  jarr $p |- ( ( ( ph -> ps ) -> ch ) -> ( ps -> ch ) ) $=
    ( wi ax-1 imim1i ) BABDCBAEF $.

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

  $( Converse of axiom ~ ax-2 .  Theorem *2.86 of [WhiteheadRussell] p. 108.
     (Contributed by NM, 25-Apr-1994.)  (Proof shortened by Wolf Lammen,
     3-Apr-2013.) $)
  pm2.86 $p |- ( ( ( ph -> ps )
       -> ( ph -> ch ) ) -> ( ph -> ( ps -> ch ) ) ) $=
    ( wi id pm2.86d ) ABDACDDZABCGEF $.

  $( The Linearity Axiom of the infinite-valued sentential logic (L-infinity)
     of Lukasiewicz.  (Contributed by O'Cat, 12-Aug-2004.)
     (Proof modification is discouraged.) $)
  loolin $p |- ( ( ( ph -> ps ) -> ( ps -> ph ) ) -> ( ps -> ph ) ) $=
    ( wi jarr pm2.43d ) ABCBACZCBAABFDE $.

  $( An alternate for the Linearity Axiom of the infinite-valued sentential
     logic (L-infinity) of Lukasiewicz, due to Barbara Wozniakowska, _Reports
     on Mathematical Logic_ 10, 129-137 (1978).  (Contributed by O'Cat,
     8-Aug-2004.) $)
  loowoz $p |- ( ( ( ph -> ps ) -> ( ph -> ch ) )
      -> ( ( ps -> ph ) -> ( ps -> ch ) ) ) $=
    ( wi jarr a2d ) ABDACDZDBACABGEF $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Logical negation
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  This section makes our first use of the third axiom of propositional
  calculus, ~ ax-3 .

$)

  ${
    con4d.1 $e |- ( ph -> ( -. ps -> -. ch ) ) $.
    $( Deduction derived from axiom ~ ax-3 .  (Contributed by NM,
       26-Mar-1995.) $)
    con4d $p |- ( ph -> ( ch -> ps ) ) $=
      ( wn wi ax-3 syl ) ABECEFCBFDBCGH $.
  $}

  ${
    pm2.21d.1 $e |- ( ph -> -. ps ) $.
    $( A contradiction implies anything.  Deduction from ~ pm2.21 .
       (Contributed by NM, 10-Feb-1996.) $)
    pm2.21d $p |- ( ph -> ( ps -> ch ) ) $=
      ( wn a1d con4d ) ACBABECEDFG $.
  $}

  ${
    pm2.21dd.1 $e |- ( ph -> ps ) $.
    pm2.21dd.2 $e |- ( ph -> -. ps ) $.
    $( A contradiction implies anything.  Deduction from ~ pm2.21 .
       (Contributed by Mario Carneiro, 9-Feb-2017.) $)
    pm2.21dd $p |- ( ph -> ch ) $=
      ( pm2.21d mpd ) ABCDABCEFG $.
  $}

  $( From a wff and its negation, anything is true.  Theorem *2.21 of
     [WhiteheadRussell] p. 104.  Also called the Duns Scotus law.  (Contributed
     by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen, 14-Sep-2012.) $)
  pm2.21 $p |- ( -. ph -> ( ph -> ps ) ) $=
    ( wn id pm2.21d ) ACZABFDE $.

  $( Theorem *2.24 of [WhiteheadRussell] p. 104.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.24 $p |- ( ph -> ( -. ph -> ps ) ) $=
    ( wn pm2.21 com12 ) ACABABDE $.

  $( Proof by contradiction.  Theorem *2.18 of [WhiteheadRussell] p. 103.  Also
     called the Law of Clavius.  (Contributed by NM, 5-Aug-1993.) $)
  pm2.18 $p |- ( ( -. ph -> ph ) -> ph ) $=
    ( wn wi pm2.21 a2i con4d pm2.43i ) ABZACZAIAIHAIBZAJDEFG $.

  ${
    pm2.18d.1 $e |- ( ph -> ( -. ps -> ps ) ) $.
    $( Deduction based on reductio ad absurdum.  (Contributed by FL,
       12-Jul-2009.)  (Proof shortened by Andrew Salmon, 7-May-2011.) $)
    pm2.18d $p |- ( ph -> ps ) $=
      ( wn wi pm2.18 syl ) ABDBEBCBFG $.
  $}

  $( Converse of double negation.  Theorem *2.14 of [WhiteheadRussell] p. 102.
     (Contributed by NM, 5-Aug-1993.)  (Proof shortened by David Harvey,
     5-Sep-1999.)  (Proof shortened by Josh Purinton, 29-Dec-2000.) $)
  notnot2 $p |- ( -. -. ph -> ph ) $=
    ( wn pm2.21 pm2.18d ) ABZBAEACD $.

  ${
    notnotrd.1 $e |- ( ph -> -. -. ps ) $.
    $( Deduction converting double-negation into the original wff, aka the
       double negation rule.  A translation of natural deduction rule ` -. -. `
       -C, ` _G |- -. -. ps ` => ` _G |- ps ` ; see ~ natded .  This is
       definition NNC in [Pfenning] p. 17.  This rule is valid in classical
       logic (which MPE uses), but not intuitionistic logic.  (Contributed by
       DAW, 8-Feb-2017.) $)
    notnotrd $p |- ( ph -> ps ) $=
      ( wn notnot2 syl ) ABDDBCBEF $.
  $}

  ${
    notnotri.1 $e |- -. -. ph $.
    $( Inference from double negation.  (Contributed by NM, 27-Feb-2008.) $)
    notnotri $p |- ph $=
      ( wn notnot2 ax-mp ) ACCABADE $.
  $}

  ${
    con2d.1 $e |- ( ph -> ( ps -> -. ch ) ) $.
    $( A contraposition deduction.  (Contributed by NM, 19-Aug-1993.) $)
    con2d $p |- ( ph -> ( ch -> -. ps ) ) $=
      ( wn notnot2 syl5 con4d ) ABEZCIEBACEBFDGH $.
  $}

  $( Contraposition.  Theorem *2.03 of [WhiteheadRussell] p. 100.  (Contributed
     by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen, 12-Feb-2013.) $)
  con2 $p |- ( ( ph -> -. ps ) -> ( ps -> -. ph ) ) $=
    ( wn wi id con2d ) ABCDZABGEF $.

  ${
    mt2d.1 $e |- ( ph -> ch ) $.
    mt2d.2 $e |- ( ph -> ( ps -> -. ch ) ) $.
    $( Modus tollens deduction.  (Contributed by NM, 4-Jul-1994.) $)
    mt2d $p |- ( ph -> -. ps ) $=
      ( wn con2d mpd ) ACBFDABCEGH $.
  $}

  ${
    mt2i.1 $e |- ch $.
    mt2i.2 $e |- ( ph -> ( ps -> -. ch ) ) $.
    $( Modus tollens inference.  (Contributed by NM, 26-Mar-1995.)  (Proof
       shortened by Wolf Lammen, 15-Sep-2012.) $)
    mt2i $p |- ( ph -> -. ps ) $=
      ( a1i mt2d ) ABCCADFEG $.
  $}

  ${
    nsyl3.1 $e |- ( ph -> -. ps ) $.
    nsyl3.2 $e |- ( ch -> ps ) $.
    $( A negated syllogism inference.  (Contributed by NM, 1-Dec-1995.) $)
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

  $( Converse of double negation.  Theorem *2.12 of [WhiteheadRussell] p. 101.
     (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen,
     2-Mar-2013.) $)
  notnot1 $p |- ( ph -> -. -. ph ) $=
    ( wn id con2i ) ABZAECD $.

  ${
    negbi.1 $e |- ph $.
    $( Infer double negation.  (Contributed by NM, 27-Feb-2008.) $)
    notnoti $p |- -. -. ph $=
      ( wn notnot1 ax-mp ) AACCBADE $.
  $}

  ${
    con1d.1 $e |- ( ph -> ( -. ps -> ch ) ) $.
    $( A contraposition deduction.  (Contributed by NM, 5-Aug-1993.) $)
    con1d $p |- ( ph -> ( -. ch -> ps ) ) $=
      ( wn notnot1 syl6 con4d ) ABCEZABECIEDCFGH $.
  $}

  ${
    mt3d.1 $e |- ( ph -> -. ch ) $.
    mt3d.2 $e |- ( ph -> ( -. ps -> ch ) ) $.
    $( Modus tollens deduction.  (Contributed by NM, 26-Mar-1995.) $)
    mt3d $p |- ( ph -> ps ) $=
      ( wn con1d mpd ) ACFBDABCEGH $.
  $}

  ${
    mt3i.1 $e |- -. ch $.
    mt3i.2 $e |- ( ph -> ( -. ps -> ch ) ) $.
    $( Modus tollens inference.  (Contributed by NM, 26-Mar-1995.)  (Proof
       shortened by Wolf Lammen, 15-Sep-2012.) $)
    mt3i $p |- ( ph -> ps ) $=
      ( wn a1i mt3d ) ABCCFADGEH $.
  $}

  ${
    nsyl2.1 $e |- ( ph -> -. ps ) $.
    nsyl2.2 $e |- ( -. ch -> ps ) $.
    $( A negated syllogism inference.  (Contributed by NM, 26-Jun-1994.) $)
    nsyl2 $p |- ( ph -> ch ) $=
      ( wn wi a1i mt3d ) ACBDCFBGAEHI $.
  $}

  $( Contraposition.  Theorem *2.15 of [WhiteheadRussell] p. 102.  (Contributed
     by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen, 12-Feb-2013.) $)
  con1 $p |- ( ( -. ph -> ps ) -> ( -. ps -> ph ) ) $=
    ( wn wi id con1d ) ACBDZABGEF $.

  ${
    con1i.a $e |- ( -. ph -> ps ) $.
    $( A contraposition inference.  (Contributed by NM, 5-Aug-1993.)  (Proof
       shortened by O'Cat, 28-Nov-2008.)  (Proof shortened by Wolf Lammen,
       19-Jun-2013.) $)
    con1i $p |- ( -. ps -> ph ) $=
      ( wn id nsyl2 ) BDZBAGECF $.
  $}

  ${
    con4i.1 $e |- ( -. ph -> -. ps ) $.
    $( Inference rule derived from axiom ~ ax-3 .  (Contributed by NM,
       5-Aug-1993.)  (Proof shortened by Wolf Lammen, 21-Jun-2013.) $)
    con4i $p |- ( ps -> ph ) $=
      ( wn notnot1 nsyl2 ) BBDABECF $.
  $}

  ${
    pm2.21i.1 $e |- -. ph $.
    $( A contradiction implies anything.  Inference from ~ pm2.21 .
       (Contributed by NM, 16-Sep-1993.) $)
    pm2.21i $p |- ( ph -> ps ) $=
      ( wn a1i con4i ) BAADBDCEF $.
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
    con3d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( A contraposition deduction.  (Contributed by NM, 5-Aug-1993.) $)
    con3d $p |- ( ph -> ( -. ch -> -. ps ) ) $=
      ( wn notnot2 syl5 con1d ) ABEZCIEBACBFDGH $.
  $}

  $( Contraposition.  Theorem *2.16 of [WhiteheadRussell] p. 103.  (Contributed
     by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen, 13-Feb-2013.) $)
  con3 $p |- ( ( ph -> ps ) -> ( -. ps -> -. ph ) ) $=
    ( wi id con3d ) ABCZABFDE $.

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

  ${
    mt4.1 $e |- ph $.
    mt4.2 $e |- ( -. ps -> -. ph ) $.
    $( The rule of modus tollens.  (Contributed by Wolf Lammen,
       12-May-2013.) $)
    mt4 $p |- ps $=
      ( con4i ax-mp ) ABCBADEF $.
  $}

  ${
    mt4d.1 $e |- ( ph -> ps ) $.
    mt4d.2 $e |- ( ph -> ( -. ch -> -. ps ) ) $.
    $( Modus tollens deduction.  (Contributed by NM, 9-Jun-2006.) $)
    mt4d $p |- ( ph -> ch ) $=
      ( con4d mpd ) ABCDACBEFG $.
  $}

  ${
    mt4i.1 $e |- ch $.
    mt4i.2 $e |- ( ph -> ( -. ps -> -. ch ) ) $.
    $( Modus tollens inference.  (Contributed by Wolf Lammen, 12-May-2013.) $)
    mt4i $p |- ( ph -> ps ) $=
      ( a1i mt4d ) ACBCADFEG $.
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
    $( A negated syllogism inference.  (Contributed by NM, 15-Feb-1996.) $)
    nsyl4 $p |- ( -. ch -> ps ) $=
      ( wn con1i syl ) CFABACEGDH $.
  $}

  ${
    pm2.24d.1 $e |- ( ph -> ps ) $.
    $( Deduction version of ~ pm2.24 .  (Contributed by NM, 30-Jan-2006.) $)
    pm2.24d $p |- ( ph -> ( -. ps -> ch ) ) $=
      ( wn a1d con1d ) ACBABCEDFG $.
  $}

  ${
    pm2.24i.1 $e |- ph $.
    $( Inference version of ~ pm2.24 .  (Contributed by NM, 20-Aug-2001.) $)
    pm2.24i $p |- ( -. ph -> ps ) $=
      ( wn a1i con1i ) BAABDCEF $.
  $}

  $( Theorem *3.2 of [WhiteheadRussell] p. 111, expressed with primitive
     connectives.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Josh
     Purinton, 29-Dec-2000.) $)
  pm3.2im $p |- ( ph -> ( ps -> -. ( ph -> -. ps ) ) ) $=
    ( wn wi pm2.27 con2d ) AABCZDBAGEF $.

  $( Theorem 8 of [Margaris] p. 60.  (Contributed by NM, 5-Aug-1993.)  (Proof
     shortened by Josh Purinton, 29-Dec-2000.) $)
  mth8 $p |- ( ph -> ( -. ps -> -. ( ph -> ps ) ) ) $=
    ( wi pm2.27 con3d ) AABCBABDE $.

  ${
    jc.1 $e |- ( ph -> ps ) $.
    jc.2 $e |- ( ph -> ch ) $.
    $( Inference joining the consequents of two premises.  (Contributed by NM,
       5-Aug-1993.) $)
    jc $p |- ( ph -> -. ( ps -> -. ch ) ) $=
      ( wn wi pm3.2im sylc ) ABCBCFGFDEBCHI $.
  $}

  ${
    impi.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( An importation inference.  (Contributed by NM, 5-Aug-1993.)  (Proof
       shortened by Wolf Lammen, 20-Jul-2013.) $)
    impi $p |- ( -. ( ph -> -. ps ) -> ch ) $=
      ( wn wi con3rr3 con1i ) CABEFABCDGH $.
  $}

  ${
    expi.1 $e |- ( -. ( ph -> -. ps ) -> ch ) $.
    $( An exportation inference.  (Contributed by NM, 5-Aug-1993.)  (Proof
       shortened by O'Cat, 28-Nov-2008.) $)
    expi $p |- ( ph -> ( ps -> ch ) ) $=
      ( wn wi pm3.2im syl6 ) ABABEFECABGDH $.
  $}

  $( Simplification.  Similar to Theorem *3.27 (Simp) of [WhiteheadRussell]
     p. 112.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf
     Lammen, 13-Nov-2012.) $)
  simprim $p |- ( -. ( ph -> -. ps ) -> ps ) $=
    ( idd impi ) ABBABCD $.

  $( Simplification.  Similar to Theorem *3.26 (Simp) of [WhiteheadRussell]
     p. 112.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf
     Lammen, 21-Jul-2012.) $)
  simplim $p |- ( -. ( ph -> ps ) -> ph ) $=
    ( wi pm2.21 con1i ) AABCABDE $.

  $( Theorem *2.5 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 9-Oct-2012.) $)
  pm2.5 $p |- ( -. ( ph -> ps ) -> ( -. ph -> ps ) ) $=
    ( wi wn simplim pm2.24d ) ABCDABABEF $.

  $( Theorem *2.51 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.51 $p |- ( -. ( ph -> ps ) -> ( ph -> -. ps ) ) $=
    ( wi wn ax-1 con3i a1d ) ABCZDBDABHBAEFG $.

  $( Theorem *2.521 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 8-Oct-2012.) $)
  pm2.521 $p |- ( -. ( ph -> ps ) -> ( ps -> ph ) ) $=
    ( wi wn simplim a1d ) ABCDABABEF $.

  $( Theorem *2.52 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 8-Oct-2012.) $)
  pm2.52 $p |- ( -. ( ph -> ps ) -> ( -. ph -> -. ps ) ) $=
    ( wi wn pm2.521 con3d ) ABCDBAABEF $.

  $( Exportation theorem expressed with primitive connectives.  (Contributed by
     NM, 5-Aug-1993.) $)
  expt $p |- ( ( -. ( ph -> -. ps ) -> ch ) -> ( ph -> ( ps -> ch ) ) ) $=
    ( wn wi pm3.2im imim1d com12 ) AABDEDZCEBCEABICABFGH $.

  $( Importation theorem expressed with primitive connectives.  (Contributed by
     NM, 25-Apr-1994.)  (Proof shortened by Wolf Lammen, 20-Jul-2013.) $)
  impt $p |- ( ( ph -> ( ps -> ch ) ) -> ( -. ( ph -> -. ps ) -> ch ) ) $=
    ( wi wn simprim simplim imim1i mpdi ) ABCDZDABEZDEZBCABFLAJAKGHI $.

  ${
    pm2.61d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    pm2.61d.2 $e |- ( ph -> ( -. ps -> ch ) ) $.
    $( Deduction eliminating an antecedent.  (Contributed by NM, 27-Apr-1994.)
       (Proof shortened by Wolf Lammen, 12-Sep-2013.) $)
    pm2.61d $p |- ( ph -> ch ) $=
      ( wn con1d syld pm2.18d ) ACACFBCABCEGDHI $.
  $}

  ${
    pm2.61d1.1 $e |- ( ph -> ( ps -> ch ) ) $.
    pm2.61d1.2 $e |- ( -. ps -> ch ) $.
    $( Inference eliminating an antecedent.  (Contributed by NM,
       15-Jul-2005.) $)
    pm2.61d1 $p |- ( ph -> ch ) $=
      ( wn wi a1i pm2.61d ) ABCDBFCGAEHI $.
  $}

  ${
    pm2.61d2.1 $e |- ( ph -> ( -. ps -> ch ) ) $.
    pm2.61d2.2 $e |- ( ps -> ch ) $.
    $( Inference eliminating an antecedent.  (Contributed by NM,
       18-Aug-1993.) $)
    pm2.61d2 $p |- ( ph -> ch ) $=
      ( wi a1i pm2.61d ) ABCBCFAEGDH $.
  $}

  ${
    ja.1 $e |- ( -. ph -> ch ) $.
    ja.2 $e |- ( ps -> ch ) $.
    $( Inference joining the antecedents of two premises.  (Contributed by NM,
       5-Aug-1993.)  (Proof shortened by O'Cat, 19-Feb-2008.) $)
    ja $p |- ( ( ph -> ps ) -> ch ) $=
      ( wi imim2i pm2.61d1 ) ABFACBCAEGDH $.
  $}

  ${
    jad.1 $e |- ( ph -> ( -. ps -> th ) ) $.
    jad.2 $e |- ( ph -> ( ch -> th ) ) $.
    $( Deduction form of ~ ja .  (Contributed by Scott Fenton, 13-Dec-2010.)
       (Proof shortened by Andrew Salmon, 17-Sep-2011.) $)
    jad $p |- ( ph -> ( ( ps -> ch ) -> th ) ) $=
      ( wi wn com12 ja ) BCGADBCADGABHDEIACDFIJI $.
  $}

  $( Elimination of a nested antecedent as a kind of reversal of inference
     ~ ja .  (Contributed by Wolf Lammen, 10-May-2013.) $)
  jarl $p |- ( ( ( ph -> ps ) -> ch ) -> ( -. ph -> ch ) ) $=
    ( wn wi pm2.21 imim1i ) ADABECABFG $.

  ${
    pm2.61i.1 $e |- ( ph -> ps ) $.
    pm2.61i.2 $e |- ( -. ph -> ps ) $.
    $( Inference eliminating an antecedent.  (Contributed by NM, 5-Apr-1994.)
       (Proof shortened by Wolf Lammen, 12-Sep-2013.) $)
    pm2.61i $p |- ps $=
      ( wi id ja ax-mp ) AAEBAFAABDCGH $.
  $}

  ${
    pm2.61ii.1 $e |- ( -. ph -> ( -. ps -> ch ) ) $.
    pm2.61ii.2 $e |- ( ph -> ch ) $.
    pm2.61ii.3 $e |- ( ps -> ch ) $.
    $( Inference eliminating two antecedents.  (Contributed by NM,
       5-Aug-1993.)  (Proof shortened by Josh Purinton, 29-Dec-2000.) $)
    pm2.61ii $p |- ch $=
      ( wn pm2.61d2 pm2.61i ) ACEAGBCDFHI $.
  $}

  ${
    pm2.61nii.1 $e |- ( ph -> ( ps -> ch ) ) $.
    pm2.61nii.2 $e |- ( -. ph -> ch ) $.
    pm2.61nii.3 $e |- ( -. ps -> ch ) $.
    $( Inference eliminating two antecedents.  (Contributed by NM,
       5-Aug-1993.)  (Proof shortened by Andrew Salmon, 25-May-2011.)  (Proof
       shortened by Wolf Lammen, 13-Nov-2012.) $)
    pm2.61nii $p |- ch $=
      ( pm2.61d1 pm2.61i ) ACABCDFGEH $.
  $}

  ${
    pm2.61iii.1 $e |- ( -. ph -> ( -. ps -> ( -. ch -> th ) ) ) $.
    pm2.61iii.2 $e |- ( ph -> th ) $.
    pm2.61iii.3 $e |- ( ps -> th ) $.
    pm2.61iii.4 $e |- ( ch -> th ) $.
    $( Inference eliminating three antecedents.  (Contributed by NM,
       2-Jan-2002.)  (Proof shortened by Wolf Lammen, 22-Sep-2013.) $)
    pm2.61iii $p |- th $=
      ( wn wi a1d pm2.61ii pm2.61i ) CDHABCIZDJEADNFKBDNGKLM $.
  $}

  $( Reductio ad absurdum.  Theorem *2.01 of [WhiteheadRussell] p. 100.
     (Contributed by NM, 18-Aug-1993.)  (Proof shortened by O'Cat,
     21-Nov-2008.)  (Proof shortened by Wolf Lammen, 31-Oct-2012.) $)
  pm2.01 $p |- ( ( ph -> -. ph ) -> -. ph ) $=
    ( wn id ja ) AABZEECZFD $.

  ${
    pm2.01d.1 $e |- ( ph -> ( ps -> -. ps ) ) $.
    $( Deduction based on reductio ad absurdum.  (Contributed by NM,
       18-Aug-1993.)  (Proof shortened by Wolf Lammen, 5-Mar-2013.) $)
    pm2.01d $p |- ( ph -> -. ps ) $=
      ( wn id pm2.61d1 ) ABBDZCGEF $.
  $}

  $( Theorem *2.6 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.6 $p |- ( ( -. ph -> ps ) -> ( ( ph -> ps ) -> ps ) ) $=
    ( wn wi id idd jad ) ACBDZABBHEHBFG $.

  $( Theorem *2.61 of [WhiteheadRussell] p. 107.  Useful for eliminating an
     antecedent.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf
     Lammen, 22-Sep-2013.) $)
  pm2.61 $p |- ( ( ph -> ps ) -> ( ( -. ph -> ps ) -> ps ) ) $=
    ( wn wi pm2.6 com12 ) ACBDABDBABEF $.

  $( Theorem *2.65 of [WhiteheadRussell] p. 107.  Proof by contradiction.
     (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen,
     8-Mar-2013.) $)
  pm2.65 $p |- ( ( ph -> ps ) -> ( ( ph -> -. ps ) -> -. ph ) ) $=
    ( wi wn idd con3 jad ) ABCZABDADZHIEABFG $.

  ${
    pm2.65i.1 $e |- ( ph -> ps ) $.
    pm2.65i.2 $e |- ( ph -> -. ps ) $.
    $( Inference rule for proof by contradiction.  (Contributed by NM,
       18-May-1994.)  (Proof shortened by Wolf Lammen, 11-Sep-2013.) $)
    pm2.65i $p |- -. ph $=
      ( wn con2i con3i pm2.61i ) BAEABDFABCGH $.
  $}

  ${
    pm2.65d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    pm2.65d.2 $e |- ( ph -> ( ps -> -. ch ) ) $.
    $( Deduction rule for proof by contradiction.  (Contributed by NM,
       26-Jun-1994.)  (Proof shortened by Wolf Lammen, 26-May-2013.) $)
    pm2.65d $p |- ( ph -> -. ps ) $=
      ( nsyld pm2.01d ) ABABCBEDFG $.
  $}

  ${
    mto.1 $e |- -. ps $.
    mto.2 $e |- ( ph -> ps ) $.
    $( The rule of modus tollens.  The rule says, "if ` ps ` is not true, and
       ` ph ` implies ` ps ` , then ` ps ` must also be not true."  Modus
       tollens is short for "modus tollendo tollens," a Latin phrase that means
       "the mood that by denying affirms" - remark in [Sanford] p. 39.  It is
       also called denying the consequent.  Modus tollens is closely related to
       modus ponens ~ ax-mp .  (Contributed by NM, 19-Aug-1993.)  (Proof
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
    mt2.1 $e |- ps $.
    mt2.2 $e |- ( ph -> -. ps ) $.
    $( A rule similar to modus tollens.  (Contributed by NM, 19-Aug-1993.)
       (Proof shortened by Wolf Lammen, 10-Sep-2013.) $)
    mt2 $p |- -. ph $=
      ( a1i pm2.65i ) ABBACEDF $.
  $}

  ${
    mt3.1 $e |- -. ps $.
    mt3.2 $e |- ( -. ph -> ps ) $.
    $( A rule similar to modus tollens.  (Contributed by NM, 18-May-1994.)
       (Proof shortened by Wolf Lammen, 11-Sep-2013.) $)
    mt3 $p |- ph $=
      ( wn mto notnotri ) AAEBCDFG $.
  $}

  $( Peirce's axiom.  This odd-looking theorem is the "difference" between an
     intuitionistic system of propositional calculus and a classical system and
     is not accepted by intuitionists.  When Peirce's axiom is added to an
     intuitionistic system, the system becomes equivalent to our classical
     system ~ ax-1 through ~ ax-3 .  A curious fact about this theorem is that
     it requires ~ ax-3 for its proof even though the result has no negation
     connectives in it.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by
     Wolf Lammen, 9-Oct-2012.) $)
  peirce $p |- ( ( ( ph -> ps ) -> ph ) -> ph ) $=
    ( wi simplim id ja ) ABCAAABDAEF $.

  $( The Inversion Axiom of the infinite-valued sentential logic (L-infinity)
     of Lukasiewicz.  Using ~ dfor2 , we can see that this essentially
     expresses "disjunction commutes."  Theorem *2.69 of [WhiteheadRussell]
     p. 108.  (Contributed by NM, 12-Aug-2004.) $)
  looinv $p |- ( ( ( ph -> ps ) -> ps ) -> ( ( ps -> ph ) -> ph ) ) $=
    ( wi imim1 peirce syl6 ) ABCZBCBACGACAGBADABEF $.

  $( Theorem used to justify definition of biconditional ~ df-bi .
     (Contributed by NM, 11-May-1999.)  (Proof shortened by Josh Purinton,
     29-Dec-2000.) $)
  bijust $p |- -. ( ( -. ( ( ph -> ps ) -> -. ( ps -> ph ) )
                      -> -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) )
               -> -. ( -. ( ( ph -> ps ) -> -. ( ps -> ph ) )
                      -> -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) ) ) $=
    ( wi wn id pm2.01 mt2 ) ABCBACDCDZHCZIDCIHEIFG $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Logical equivalence
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  The definition ~ df-bi in this section is our first definition, which
  introduces and defines the biconditional connective ` <-> ` . We define a wff
  of the form ` ( ph <-> ps ) ` as an abbreviation for
  ` -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) ` .

  Unlike most traditional developments, we have chosen not to have a separate
  symbol such as "Df." to mean "is defined as."  Instead, we will later use the
  biconditional connective for this purpose ( ~ df-or is its first use), as it
  allows us to use logic to manipulate definitions directly.  This greatly
  simplifies many proofs since it eliminates the need for a separate mechanism
  for introducing and eliminating definitions.
$)

  $( Declare the biconditional connective. $)
  $c <-> $. $( Double arrow (read:  'if and only if' or
               'is logically equivalent to') $)

  $( Extend our wff definition to include the biconditional connective. $)
  wb $a wff ( ph <-> ps ) $.

  $( Define the biconditional (logical 'iff').

     The definition ~ df-bi in this section is our first definition, which
     introduces and defines the biconditional connective ` <-> ` .  We define a
     wff of the form ` ( ph <-> ps ) ` as an abbreviation for
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
     ` ( ph <-> ps ) ` (the definiendum i.e. the thing being defined) with
     ` -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) ` (the definiens i.e. the
     defining expression) in the definition, the definition becomes the
     previously proved theorem ~ bijust .  It is impossible to use ~ df-bi to
     prove any statement expressed in the original language that can't be
     proved from the original axioms, because if we simply replace each
     instance of ~ df-bi in the proof with the corresponding ~ bijust instance,
     we will end up with a proof from the original axioms.

     Note that from Metamath's point of view, a definition is just another
     axiom - i.e. an assertion we claim to be true - but from our high level
     point of view, we are not strengthening the language.  To indicate this
     fact, we prefix definition labels with "df-" instead of "ax-".  (This
     prefixing is an informal convention that means nothing to the Metamath
     proof verifier; it is just a naming convention for human readability.)

     After we define the constant true ` T. ` ( ~ df-tru ) and the constant
     false ` F. ` ( ~ df-fal ), we will be able to prove these truth table
     values: ` ( ( T. <-> T. ) <-> T. ) ` ( ~ trubitru ),
     ` ( ( T. <-> F. ) <-> F. ) ` ( ~ trubifal ), ` ( ( F. <-> T. ) <-> F. ) `
     ( ~ falbitru ), and ` ( ( F. <-> F. ) <-> T. ) ` ( ~ falbifal ).

     See ~ dfbi1 , ~ dfbi2 , and ~ dfbi3 for theorems suggesting typical
     textbook definitions of ` <-> ` , showing that our definition has the
     properties we expect.  Theorem ~ dfbi1 is particularly useful if we want
     to eliminate ` <-> ` from an expression to convert it to primitives.
     Theorem ~ dfbi shows this definition rewritten in an abbreviated form
     after conjunction is introduced, for easier understanding.

     Contrast with ` \/ ` ( ~ df-or ), ` -> ` ( ~ wi ), ` -/\ ` ( ~ df-nan ),
     and ` \/_ ` ( ~ df-xor ) .  In some sense ` <-> ` returns true if two
     truth values are equal; ` = ` ( ~ df-cleq ) returns true if two classes
     are equal.  (Contributed by NM, 5-Aug-1993.) $)
  df-bi $a |- -. ( ( ( ph <-> ps ) -> -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) )
        -> -. ( -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) -> ( ph <-> ps ) ) ) $.

  $( $j justification 'bijust' for 'df-bi'; $)

  $( Property of the biconditional connective.  (Contributed by NM,
     11-May-1999.) $)
  bi1 $p |- ( ( ph <-> ps ) -> ( ph -> ps ) ) $=
    ( wb wi wn df-bi simplim ax-mp syl ) ABCZABDZBADEZDEZKJMDZMJDEZDENABFNOGHKL
    GI $.

  $( Property of the biconditional connective.  (Contributed by NM,
     11-May-1999.) $)
  bi3 $p |- ( ( ph -> ps ) -> ( ( ps -> ph ) -> ( ph <-> ps ) ) ) $=
    ( wi wb wn df-bi simprim ax-mp expi ) ABCZBACZABDZLJKECEZCZMLCZECEOABFNOGHI
    $.

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

  $( Relate the biconditional connective to primitive connectives.  See
     ~ dfbi1gb for an unusual version proved directly from axioms.
     (Contributed by NM, 5-Aug-1993.) $)
  dfbi1 $p |- ( ( ph <-> ps ) <-> -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) ) $=
    ( wb wi wn df-bi simplim ax-mp bi3 impi impbii ) ABCZABDZBADZEDEZLODZOLDEZD
    EPABFPQGHMNLABIJK $.

  $( This proof of ~ dfbi1 , discovered by Gregory Bush on 8-Mar-2004, has
     several curious properties.  First, it has only 17 steps directly from the
     axioms and ~ df-bi , compared to over 800 steps were the proof of ~ dfbi1
     expanded into axioms.  Second, step 2 demands only the property of "true";
     any axiom (or theorem) could be used.  It might be thought, therefore,
     that it is in some sense redundant, but in fact no proof is shorter than
     this (measured by number of steps).  Third, it illustrates how
     intermediate steps can "blow up" in size even in short proofs.  Fourth,
     the compressed proof is only 182 bytes (or 17 bytes in D-proof notation),
     but the generated web page is over 200kB with intermediate steps that are
     essentially incomprehensible to humans (other than Gregory Bush).  If
     there were an obfuscated code contest for proofs, this would be a
     contender.  This "blowing up" and incomprehensibility of the intermediate
     steps vividly demonstrate the advantages of using many layered
     intermediate theorems, since each theorem is easier to understand.
     (Contributed by Gregory Bush, 10-Mar-2004.)  (New usage is discouraged.)
     (Proof modification is discouraged.) $)
  dfbi1gb $p |- ( ( ph <-> ps ) <-> -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) ) $=
    ( wch wth wb wi wn df-bi ax-1 ax-mp ax-3 ax-2 ) ABEZABFBAFGFGZFNMFGFGZMNEZA
    BHCDCFFZOPFZCDIRGZQGZFZQRFSPOFZSFZFZUASUBISUCTFZFZUDUAFUEUFTGZUCGZFZUEUHUIM
    NHUHUGIJTUCKJUESIJSUCTLJJRQKJJJ $.

  ${
    biimpi.1 $e |- ( ph <-> ps ) $.
    $( Infer an implication from a logical equivalence.  (Contributed by NM,
       5-Aug-1993.) $)
    biimpi $p |- ( ph -> ps ) $=
      ( wb wi bi1 ax-mp ) ABDABECABFG $.
  $}

  ${
    sylbi.1 $e |- ( ph <-> ps ) $.
    sylbi.2 $e |- ( ps -> ch ) $.
    $( A mixed syllogism inference from a biconditional and an implication.
       Useful for substituting an antecedent with a definition.  (Contributed
       by NM, 5-Aug-1993.) $)
    sylbi $p |- ( ph -> ch ) $=
      ( biimpi syl ) ABCABDFEG $.
  $}

  ${
    sylib.1 $e |- ( ph -> ps ) $.
    sylib.2 $e |- ( ps <-> ch ) $.
    $( A mixed syllogism inference from an implication and a biconditional.
       (Contributed by NM, 5-Aug-1993.) $)
    sylib $p |- ( ph -> ch ) $=
      ( biimpi syl ) ABCDBCEFG $.
  $}

  $( Property of the biconditional connective.  (Contributed by NM,
     11-May-1999.)  (Proof shortened by Wolf Lammen, 11-Nov-2012.) $)
  bi2 $p |- ( ( ph <-> ps ) -> ( ps -> ph ) ) $=
    ( wb wi wn dfbi1 simprim sylbi ) ABCABDZBADZEDEJABFIJGH $.

  $( Commutative law for equivalence.  (Contributed by Wolf Lammen,
     10-Nov-2012.) $)
  bicom1 $p |- ( ( ph <-> ps ) -> ( ps <-> ph ) ) $=
    ( wb bi2 bi1 impbid ) ABCBAABDABEF $.

  $( Commutative law for equivalence.  Theorem *4.21 of [WhiteheadRussell]
     p. 117.  (Contributed by NM, 5-Aug-1993.) $)
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
    bicomi.1 $e |- ( ph <-> ps ) $.
    $( Inference from commutative law for logical equivalence.  (Contributed by
       NM, 5-Aug-1993.) $)
    bicomi $p |- ( ps <-> ph ) $=
      ( wb bicom1 ax-mp ) ABDBADCABEF $.
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
    impcon4bid.1 $e |- ( ph -> ( ps -> ch ) ) $.
    impcon4bid.2 $e |- ( ph -> ( -. ps -> -. ch ) ) $.
    $( A variation on ~ impbid with contraposition.  (Contributed by Jeff
       Hankins, 3-Jul-2009.) $)
    impcon4bid $p |- ( ph -> ( ps <-> ch ) ) $=
      ( con4d impbid ) ABCDABCEFG $.
  $}

  ${
    biimpri.1 $e |- ( ph <-> ps ) $.
    $( Infer a converse implication from a logical equivalence.  (Contributed
       by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen, 16-Sep-2013.) $)
    biimpri $p |- ( ps -> ph ) $=
      ( bicomi biimpi ) BAABCDE $.
  $}

  ${
    biimpd.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Deduce an implication from a logical equivalence.  (Contributed by NM,
       5-Aug-1993.) $)
    biimpd $p |- ( ph -> ( ps -> ch ) ) $=
      ( wb wi bi1 syl ) ABCEBCFDBCGH $.
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
    syl5bi.1 $e |- ( ph <-> ps ) $.
    syl5bi.2 $e |- ( ch -> ( ps -> th ) ) $.
    $( A mixed syllogism inference from a nested implication and a
       biconditional.  Useful for substituting an embedded antecedent with a
       definition.  (Contributed by NM, 5-Aug-1993.) $)
    syl5bi $p |- ( ch -> ( ph -> th ) ) $=
      ( biimpi syl5 ) ABCDABEGFH $.
  $}

  ${
    syl5bir.1 $e |- ( ps <-> ph ) $.
    syl5bir.2 $e |- ( ch -> ( ps -> th ) ) $.
    $( A mixed syllogism inference from a nested implication and a
       biconditional.  (Contributed by NM, 5-Aug-1993.) $)
    syl5bir $p |- ( ch -> ( ph -> th ) ) $=
      ( biimpri syl5 ) ABCDBAEGFH $.
  $}

  ${
    syl5ib.1 $e |- ( ph -> ps ) $.
    syl5ib.2 $e |- ( ch -> ( ps <-> th ) ) $.
    $( A mixed syllogism inference.  (Contributed by NM, 5-Aug-1993.) $)
    syl5ib $p |- ( ch -> ( ph -> th ) ) $=
      ( biimpd syl5 ) ABCDECBDFGH $.

    $( A mixed syllogism inference.  (Contributed by NM, 19-Jun-2007.) $)
    syl5ibcom $p |- ( ph -> ( ch -> th ) ) $=
      ( syl5ib com12 ) CADABCDEFGH $.
  $}

  ${
    syl5ibr.1 $e |- ( ph -> th ) $.
    syl5ibr.2 $e |- ( ch -> ( ps <-> th ) ) $.
    $( A mixed syllogism inference.  (Contributed by NM, 3-Apr-1994.) $)
    syl5ibr $p |- ( ch -> ( ph -> ps ) ) $=
      ( bicomd syl5ib ) ADCBECBDFGH $.

    $( A mixed syllogism inference.  (Contributed by NM, 20-Jun-2007.) $)
    syl5ibrcom $p |- ( ph -> ( ch -> ps ) ) $=
      ( syl5ibr com12 ) CABABCDEFGH $.
  $}

  ${
    biimprd.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Deduce a converse implication from a logical equivalence.  (Contributed
       by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen, 22-Sep-2013.) $)
    biimprd $p |- ( ph -> ( ch -> ps ) ) $=
      ( id syl5ibr ) CBACCEDF $.
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
    syl6ib.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syl6ib.2 $e |- ( ch <-> th ) $.
    $( A mixed syllogism inference from a nested implication and a
       biconditional.  (Contributed by NM, 5-Aug-1993.) $)
    syl6ib $p |- ( ph -> ( ps -> th ) ) $=
      ( biimpi syl6 ) ABCDECDFGH $.
  $}

  ${
    syl6ibr.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syl6ibr.2 $e |- ( th <-> ch ) $.
    $( A mixed syllogism inference from a nested implication and a
       biconditional.  Useful for substituting an embedded consequent with a
       definition.  (Contributed by NM, 5-Aug-1993.) $)
    syl6ibr $p |- ( ph -> ( ps -> th ) ) $=
      ( biimpri syl6 ) ABCDEDCFGH $.
  $}


  ${
    syl6bi.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    syl6bi.2 $e |- ( ch -> th ) $.
    $( A mixed syllogism inference.  (Contributed by NM, 2-Jan-1994.) $)
    syl6bi $p |- ( ph -> ( ps -> th ) ) $=
      ( biimpd syl6 ) ABCDABCEGFH $.
  $}

  ${
    syl6bir.1 $e |- ( ph -> ( ch <-> ps ) ) $.
    syl6bir.2 $e |- ( ch -> th ) $.
    $( A mixed syllogism inference.  (Contributed by NM, 18-May-1994.) $)
    syl6bir $p |- ( ph -> ( ps -> th ) ) $=
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
     ~ 2th .  Equivalent to a ~ bi1 -like version of the xor-connective.  This
     theorem stays true, no matter how you permute its operands.  This is
     evident from its sharper version
     ` ( ph <-> ( ps <-> ( ph <-> ps ) ) ) ` .  (Contributed by Wolf Lammen,
     12-May-2013.) $)
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
    $( Two truths are equivalent (deduction rule).  (Contributed by NM,
       3-Jun-2012.) $)
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
      ( wb bi1 syli ) BABCECDBCFG $.
  $}

  $( Distribution of implication over biconditional.  Theorem *5.74 of
     [WhiteheadRussell] p. 126.  (Contributed by NM, 1-Aug-1994.)  (Proof
     shortened by Wolf Lammen, 11-Apr-2013.) $)
  pm5.74 $p |- ( ( ph -> ( ps <-> ch ) ) <->
               ( ( ph -> ps ) <-> ( ph -> ch ) ) ) $=
    ( wb wi bi1 imim3i bi2 impbid pm2.86d impbidd impbii ) ABCDZEZABEZACEZDZNOP
    MBCABCFGMCBABCHGIQABCQABCOPFJQACBOPHJKL $.

  ${
    pm5.74i.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Distribution of implication over biconditional (inference rule).
       (Contributed by NM, 1-Aug-1994.) $)
    pm5.74i $p |- ( ( ph -> ps ) <-> ( ph -> ch ) ) $=
      ( wb wi pm5.74 mpbi ) ABCEFABFACFEDABCGH $.
  $}

  ${
    pm5.74ri.1 $e |- ( ( ph -> ps ) <-> ( ph -> ch ) ) $.
    $( Distribution of implication over biconditional (reverse inference
       rule).  (Contributed by NM, 1-Aug-1994.) $)
    pm5.74ri $p |- ( ph -> ( ps <-> ch ) ) $=
      ( wb wi pm5.74 mpbir ) ABCEFABFACFEDABCGH $.
  $}

  ${
    pm5.74d.1 $e |- ( ph -> ( ps -> ( ch <-> th ) ) ) $.
    $( Distribution of implication over biconditional (deduction rule).
       (Contributed by NM, 21-Mar-1996.) $)
    pm5.74d $p |- ( ph -> ( ( ps -> ch ) <-> ( ps -> th ) ) ) $=
      ( wb wi pm5.74 sylib ) ABCDFGBCGBDGFEBCDHI $.
  $}

  ${
    pm5.74rd.1 $e |- ( ph -> ( ( ps -> ch ) <-> ( ps -> th ) ) ) $.
    $( Distribution of implication over biconditional (deduction rule).
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

  $( Register '<->' as an equality for its type (wff). $)
  $( $j
    equality 'wb' from 'biid' 'bicomi' 'bitri';
    definition 'dfbi1' for 'wb';
  $)

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
    syl5bb.1 $e |- ( ph <-> ps ) $.
    syl5bb.2 $e |- ( ch -> ( ps <-> th ) ) $.
    $( A syllogism inference from two biconditionals.  (Contributed by NM,
       5-Aug-1993.) $)
    syl5bb $p |- ( ch -> ( ph <-> th ) ) $=
      ( wb a1i bitrd ) CABDABGCEHFI $.
  $}

  ${
    syl5rbb.1 $e |- ( ph <-> ps ) $.
    syl5rbb.2 $e |- ( ch -> ( ps <-> th ) ) $.
    $( A syllogism inference from two biconditionals.  (Contributed by NM,
       5-Aug-1993.) $)
    syl5rbb $p |- ( ch -> ( th <-> ph ) ) $=
      ( syl5bb bicomd ) CADABCDEFGH $.
  $}

  ${
    syl5bbr.1 $e |- ( ps <-> ph ) $.
    syl5bbr.2 $e |- ( ch -> ( ps <-> th ) ) $.
    $( A syllogism inference from two biconditionals.  (Contributed by NM,
       5-Aug-1993.) $)
    syl5bbr $p |- ( ch -> ( ph <-> th ) ) $=
      ( bicomi syl5bb ) ABCDBAEGFH $.
  $}

  ${
    syl5rbbr.1 $e |- ( ps <-> ph ) $.
    syl5rbbr.2 $e |- ( ch -> ( ps <-> th ) ) $.
    $( A syllogism inference from two biconditionals.  (Contributed by NM,
       25-Nov-1994.) $)
    syl5rbbr $p |- ( ch -> ( th <-> ph ) ) $=
      ( bicomi syl5rbb ) ABCDBAEGFH $.
  $}

  ${
    syl6bb.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    syl6bb.2 $e |- ( ch <-> th ) $.
    $( A syllogism inference from two biconditionals.  (Contributed by NM,
       5-Aug-1993.) $)
    syl6bb $p |- ( ph -> ( ps <-> th ) ) $=
      ( wb a1i bitrd ) ABCDECDGAFHI $.
  $}

  ${
    syl6rbb.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    syl6rbb.2 $e |- ( ch <-> th ) $.
    $( A syllogism inference from two biconditionals.  (Contributed by NM,
       5-Aug-1993.) $)
    syl6rbb $p |- ( ph -> ( th <-> ps ) ) $=
      ( syl6bb bicomd ) ABDABCDEFGH $.
  $}

  ${
    syl6bbr.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    syl6bbr.2 $e |- ( th <-> ch ) $.
    $( A syllogism inference from two biconditionals.  (Contributed by NM,
       5-Aug-1993.) $)
    syl6bbr $p |- ( ph -> ( ps <-> th ) ) $=
      ( bicomi syl6bb ) ABCDEDCFGH $.
  $}

  ${
    syl6rbbr.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    syl6rbbr.2 $e |- ( th <-> ch ) $.
    $( A syllogism inference from two biconditionals.  (Contributed by NM,
       25-Nov-1994.) $)
    syl6rbbr $p |- ( ph -> ( th <-> ps ) ) $=
      ( bicomi syl6rbb ) ABCDEDCFGH $.
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
      ( syl5bir syl6ib ) ADCEDBACGFIHJ $.
  $}

  ${
    3imtr4g.1 $e |- ( ph -> ( ps -> ch ) ) $.
    3imtr4g.2 $e |- ( th <-> ps ) $.
    3imtr4g.3 $e |- ( ta <-> ch ) $.
    $( More general version of ~ 3imtr4i .  Useful for converting definitions
       in a formula.  (Contributed by NM, 20-May-1996.)  (Proof shortened by
       Wolf Lammen, 20-Dec-2013.) $)
    3imtr4g $p |- ( ph -> ( th -> ta ) ) $=
      ( syl5bi syl6ibr ) ADCEDBACGFIHJ $.
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
      ( syl5bbr syl6bb ) ADCEDBACGFIHJ $.
  $}

  ${
    3bitr4g.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    3bitr4g.2 $e |- ( th <-> ps ) $.
    3bitr4g.3 $e |- ( ta <-> ch ) $.
    $( More general version of ~ 3bitr4i .  Useful for converting definitions
       in a formula.  (Contributed by NM, 5-Aug-1993.) $)
    3bitr4g $p |- ( ph -> ( th <-> ta ) ) $=
      ( syl5bb syl6bbr ) ADCEDBACGFIHJ $.
  $}

  ${
    bi3ant.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Construct a bi-conditional in antecedent position.  (Contributed by Wolf
       Lammen, 14-May-2013.) $)
    bi3ant $p |- ( ( ( th -> ta ) -> ph )
        -> ( ( ( ta -> th ) -> ps ) -> ( ( th <-> ta ) -> ch ) ) ) $=
      ( wi wb bi1 imim1i bi2 imim3i syl2im ) DEGZAGDEHZAGEDGZBGOBGOCGONADEIJOPB
      DEKJABCOFLM $.
  $}

  $( Express symmetries of theorems in terms of biconditionals.  (Contributed
     by Wolf Lammen, 14-May-2013.) $)
  bisym $p |- ( ( ( ph -> ps ) -> ( ch -> th ) ) -> ( ( ( ps -> ph )
      -> ( th -> ch ) ) -> ( ( ph <-> ps ) -> ( ch <-> th ) ) ) ) $=
    ( wi wb bi3 bi3ant ) CDEDCECDFABCDGH $.

  $( Double negation.  Theorem *4.13 of [WhiteheadRussell] p. 117.
     (Contributed by NM, 5-Aug-1993.) $)
  notnot $p |- ( ph <-> -. -. ph ) $=
    ( wn notnot1 notnot2 impbii ) AABBACADE $.

  $( Contraposition.  Theorem *4.1 of [WhiteheadRussell] p. 116.  (Contributed
     by NM, 5-Aug-1993.) $)
  con34b $p |- ( ( ph -> ps ) <-> ( -. ps -> -. ph ) ) $=
    ( wi wn con3 ax-3 impbii ) ABCBDADCABEBAFG $.

  ${
    con4bid.1 $e |- ( ph -> ( -. ps <-> -. ch ) ) $.
    $( A contraposition deduction.  (Contributed by NM, 21-May-1994.) $)
    con4bid $p |- ( ph -> ( ps <-> ch ) ) $=
      ( wn biimprd con4d biimpd impcon4bid ) ABCACBABEZCEZDFGAJKDHI $.
  $}

  ${
    notbid.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Deduction negating both sides of a logical equivalence.  (Contributed by
       NM, 21-May-1994.) $)
    notbid $p |- ( ph -> ( -. ps <-> -. ch ) ) $=
      ( wn notnot 3bitr3g con4bid ) ABEZCEZABCIEJEDBFCFGH $.
  $}

  $( Contraposition.  Theorem *4.11 of [WhiteheadRussell] p. 117.  (Contributed
     by NM, 21-May-1994.)  (Proof shortened by Wolf Lammen, 12-Jun-2013.) $)
  notbi $p |- ( ( ph <-> ps ) <-> ( -. ph <-> -. ps ) ) $=
    ( wb wn id notbid con4bid impbii ) ABCZADBDCZIABIEFJABJEGH $.

  ${
    notbii.1 $e |- ( ph <-> ps ) $.
    $( Negate both sides of a logical equivalence.  (Contributed by NM,
       5-Aug-1993.)  (Proof shortened by Wolf Lammen, 19-May-2013.) $)
    notbii $p |- ( -. ph <-> -. ps ) $=
      ( wb wn notbi mpbi ) ABDAEBEDCABFG $.

    $( Theorem notbii is the congruence law for negation. $)
    $( $j congruence 'notbii'; $)
  $}

  ${
    con4bii.1 $e |- ( -. ph <-> -. ps ) $.
    $( A contraposition inference.  (Contributed by NM, 21-May-1994.) $)
    con4bii $p |- ( ph <-> ps ) $=
      ( wb wn notbi mpbir ) ABDAEBEDCABFG $.
  $}

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
       Useful for substituting a consequent with a definition.  (Contributed by
       Wolf Lammen, 16-Dec-2013.) $)
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
      ( wb id syl6bb syl6bbr impbii ) CAEZCBEZJCABJFDGKCBAKFDHI $.

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

    $( Theorem imbi12i is the congruence law for implication. $)
    $( $j congruence 'imbi12i'; $)
  $}

  $( Theorem *4.86 of [WhiteheadRussell] p. 122.  (Contributed by NM,
     3-Jan-2005.) $)
  bibi1 $p |- ( ( ph <-> ps ) -> ( ( ph <-> ch ) <-> ( ps <-> ch ) ) ) $=
    ( wb id bibi1d ) ABDZABCGEF $.

  $( Contraposition.  Theorem *4.12 of [WhiteheadRussell] p. 117.  (Contributed
     by NM, 15-Apr-1995.)  (Proof shortened by Wolf Lammen, 3-Jan-2013.) $)
  con2bi $p |- ( ( ph <-> -. ps ) <-> ( ps <-> -. ph ) ) $=
    ( wn wb notbi notnot bibi2i bicom 3bitr2i ) ABCZDACZJCZDKBDBKDAJEBLKBFGKBHI
    $.

  ${
    con2bid.1 $e |- ( ph -> ( ps <-> -. ch ) ) $.
    $( A contraposition deduction.  (Contributed by NM, 15-Apr-1995.) $)
    con2bid $p |- ( ph -> ( ch <-> -. ps ) ) $=
      ( wn wb con2bi sylibr ) ABCEFCBEFDCBGH $.
  $}

  ${
    con1bid.1 $e |- ( ph -> ( -. ps <-> ch ) ) $.
    $( A contraposition deduction.  (Contributed by NM, 9-Oct-1999.) $)
    con1bid $p |- ( ph -> ( -. ch <-> ps ) ) $=
      ( wn bicomd con2bid ) ABCEACBABECDFGF $.
  $}

  ${
    con1bii.1 $e |- ( -. ph <-> ps ) $.
    $( A contraposition inference.  (Contributed by NM, 5-Aug-1993.)  (Proof
       shortened by Wolf Lammen, 13-Oct-2012.) $)
    con1bii $p |- ( -. ps <-> ph ) $=
      ( wn notnot xchbinx bicomi ) ABDAADBAECFG $.
  $}

  ${
    con2bii.1 $e |- ( ph <-> -. ps ) $.
    $( A contraposition inference.  (Contributed by NM, 5-Aug-1993.) $)
    con2bii $p |- ( ps <-> -. ph ) $=
      ( wn bicomi con1bii ) ADBBAABDCEFE $.
  $}

  $( Contraposition.  Bidirectional version of ~ con1 .  (Contributed by NM,
     5-Aug-1993.) $)
  con1b $p |- ( ( -. ph -> ps ) <-> ( -. ps -> ph ) ) $=
    ( wn wi con1 impbii ) ACBDBCADABEBAEF $.

  $( Contraposition.  Bidirectional version of ~ con2 .  (Contributed by NM,
     5-Aug-1993.) $)
  con2b $p |- ( ( ph -> -. ps ) <-> ( ps -> -. ph ) ) $=
    ( wn wi con2 impbii ) ABCDBACDABEBAEF $.

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
    $( Inference rule introducing a theorem as an antecedent.  (Contributed by
       NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen, 11-Nov-2012.) $)
    a1bi $p |- ( ps <-> ( ph -> ps ) ) $=
      ( wi wb biimt ax-mp ) ABABDECABFG $.
  $}

  ${
    mt2bi.1 $e |- ph $.
    $( A false consequent falsifies an antecedent.  (Contributed by NM,
       19-Aug-1993.)  (Proof shortened by Wolf Lammen, 12-Nov-2012.) $)
    mt2bi $p |- ( -. ps <-> ( ps -> -. ph ) ) $=
      ( wn wi a1bi con2b bitri ) BDZAIEBADEAICFABGH $.
  $}

  $( Modus-tollens-like theorem.  (Contributed by NM, 7-Apr-2001.)  (Proof
     shortened by Wolf Lammen, 12-Nov-2012.) $)
  mtt $p |- ( -. ph -> ( -. ps <-> ( ps -> ph ) ) ) $=
    ( wn wi biimt con34b syl6bbr ) ACZBCZHIDBADHIEBAFG $.

  $( Theorem *5.501 of [WhiteheadRussell] p. 125.  (Contributed by NM,
     3-Jan-2005.) $)
  pm5.501 $p |- ( ph -> ( ps <-> ( ph <-> ps ) ) ) $=
    ( wb pm5.1im bi1 com12 impbid ) ABABCZABDHABABEFG $.

  $( Implication in terms of implication and biconditional.  (Contributed by
     NM, 31-Mar-1994.)  (Proof shortened by Wolf Lammen, 24-Jan-2013.) $)
  ibib $p |- ( ( ph -> ps ) <-> ( ph -> ( ph <-> ps ) ) ) $=
    ( wb pm5.501 pm5.74i ) ABABCABDE $.

  $( Implication in terms of implication and biconditional.  (Contributed by
     NM, 29-Apr-2005.)  (Proof shortened by Wolf Lammen, 21-Dec-2013.) $)
  ibibr $p |- ( ( ph -> ps ) <-> ( ph -> ( ps <-> ph ) ) ) $=
    ( wb pm5.501 bicom syl6bb pm5.74i ) ABBACZABABCHABDABEFG $.

  ${
    tbt.1 $e |- ph $.
    $( A wff is equivalent to its equivalence with truth.  (Contributed by NM,
       18-Aug-1993.)  (Proof shortened by Andrew Salmon, 13-May-2011.) $)
    tbt $p |- ( ps <-> ( ps <-> ph ) ) $=
      ( wb ibibr pm5.74ri ax-mp ) ABBADZDCABHABEFG $.
  $}

  $( The negation of a wff is equivalent to the wff's equivalence to
     falsehood.  (Contributed by Juha Arpiainen, 19-Jan-2006.)  (Proof
     shortened by Wolf Lammen, 28-Jan-2013.) $)
  nbn2 $p |- ( -. ph -> ( -. ps <-> ( ph <-> ps ) ) ) $=
    ( wn wb pm5.501 notbi syl6bbr ) ACZBCZHIDABDHIEABFG $.

  $( Transfer negation via an equivalence.  (Contributed by NM, 3-Oct-2007.)
     (Proof shortened by Wolf Lammen, 28-Jan-2013.) $)
  bibif $p |- ( -. ps -> ( ( ph <-> ps ) <-> -. ph ) ) $=
    ( wn wb nbn2 bicom syl6rbb ) BCACBADABDBAEBAFG $.

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

  $( Two propositions are equivalent if they are both false.  Closed form of
     ~ 2false .  Equivalent to a ~ bi2 -like version of the xor-connective.
     (Contributed by Wolf Lammen, 13-May-2013.) $)
  pm5.21im $p |- ( -. ph -> ( -. ps -> ( ph <-> ps ) ) ) $=
    ( wn wb nbn2 biimpd ) ACBCABDABEF $.

  ${
    2false.1 $e |- -. ph $.
    2false.2 $e |- -. ps $.
    $( Two falsehoods are equivalent.  (Contributed by NM, 4-Apr-2005.)  (Proof
       shortened by Wolf Lammen, 19-May-2013.) $)
    2false $p |- ( ph <-> ps ) $=
      ( wn 2th con4bii ) ABAEBECDFG $.
  $}

  ${
    2falsed.1 $e |- ( ph -> -. ps ) $.
    2falsed.2 $e |- ( ph -> -. ch ) $.
    $( Two falsehoods are equivalent (deduction rule).  (Contributed by NM,
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

    ${
      pm5.21nii.3 $e |- ( ps -> ( ph <-> ch ) ) $.
      $( Eliminate an antecedent implied by each side of a biconditional.
         (Contributed by NM, 21-May-1999.) $)
      pm5.21nii $p |- ( ph <-> ch ) $=
        ( wb pm5.21ni pm2.61i ) BACGFABCDEHI $.
    $}
  $}

  ${
    pm5.21ndd.1 $e |- ( ph -> ( ch -> ps ) ) $.
    pm5.21ndd.2 $e |- ( ph -> ( th -> ps ) ) $.
    pm5.21ndd.3 $e |- ( ph -> ( ps -> ( ch <-> th ) ) ) $.
    $( Eliminate an antecedent implied by each side of a biconditional,
       deduction version.  (Contributed by Paul Chapman, 21-Nov-2012.)  (Proof
       shortened by Wolf Lammen, 6-Oct-2013.) $)
    pm5.21ndd $p |- ( ph -> ( ch <-> th ) ) $=
      ( wb wn con3d pm5.21im syl6c pm2.61d ) ABCDHZGABICIDINACBEJADBFJCDKLM $.
  $}

  ${
    bija.1 $e |- ( ph -> ( ps -> ch ) ) $.
    bija.2 $e |- ( -. ph -> ( -. ps -> ch ) ) $.
    $( Combine antecedents into a single bi-conditional.  This inference,
       reminiscent of ~ ja , is reversible:  The hypotheses can be deduced from
       the conclusion alone (see ~ pm5.1im and ~ pm5.21im ).  (Contributed by
       Wolf Lammen, 13-May-2013.) $)
    bija $p |- ( ( ph <-> ps ) -> ch ) $=
      ( wb bi2 syli wn bi1 con3d pm2.61d ) ABFZBCBMACABGDHBIMAICMABABJKEHL $.
  $}

  $( Theorem *5.18 of [WhiteheadRussell] p. 124.  This theorem says that
     logical equivalence is the same as negated "exclusive-or."  (Contributed
     by NM, 28-Jun-2002.)  (Proof shortened by Andrew Salmon, 20-Jun-2011.)
     (Proof shortened by Wolf Lammen, 15-Oct-2013.) $)
  pm5.18 $p |- ( ( ph <-> ps ) <-> -. ( ph <-> -. ps ) ) $=
    ( wb wn pm5.501 con1bid bitr2d nbn2 pm2.61i ) AABCZABDZCZDZCAMBJABLAKEFABEG
    ADZMKJNKLAKHFABHGI $.

  $( Two ways to express "exclusive or."  (Contributed by NM, 1-Jan-2006.) $)
  xor3 $p |- ( -. ( ph <-> ps ) <-> ( ph <-> -. ps ) ) $=
    ( wn wb pm5.18 con2bii bicomi ) ABCDZABDZCIHABEFG $.

  $( Move negation outside of biconditional.  Compare Theorem *5.18 of
     [WhiteheadRussell] p. 124.  (Contributed by NM, 27-Jun-2002.)  (Proof
     shortened by Wolf Lammen, 20-Sep-2013.) $)
  nbbn $p |- ( ( -. ph <-> ps ) <-> -. ( ph <-> ps ) ) $=
    ( wb wn xor3 con2bi bicom 3bitrri ) ABCDABDCBADZCIBCABEABFBIGH $.

  $( Associative law for the biconditional.  An axiom of system DS in Vladimir
     Lifschitz, "On calculational proofs", Annals of Pure and Applied Logic,
     113:207-224, 2002,
     ~ http://www.cs.utexas.edu/users/ai-lab/pub-view.php?PubID=26805 .
     Interestingly, this law was not included in _Principia Mathematica_ but
     was apparently first noted by Jan Lukasiewicz circa 1923.  (Contributed by
     NM, 8-Jan-2005.)  (Proof shortened by Juha Arpiainen, 19-Jan-2006.)
     (Proof shortened by Wolf Lammen, 21-Sep-2013.) $)
  biass $p |- ( ( ( ph <-> ps ) <-> ch ) <-> ( ph <-> ( ps <-> ch ) ) ) $=
    ( wb pm5.501 bibi1d bitr3d wn nbbn nbn2 syl5bbr pm2.61i ) AABDZCDZABCDZDZDA
    ONPABMCABEFAOEGAHZOHZNPRBHZCDQNBCIQSMCABJFKAOJGL $.

  $( Theorem *5.19 of [WhiteheadRussell] p. 124.  (Contributed by NM,
     3-Jan-2005.) $)
  pm5.19 $p |- -. ( ph <-> -. ph ) $=
    ( wb wn biid pm5.18 mpbi ) AABAACBCADAAEF $.

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

  $( Theorem *4.8 of [WhiteheadRussell] p. 122.  (Contributed by NM,
     3-Jan-2005.) $)
  pm4.8 $p |- ( ( ph -> -. ph ) <-> -. ph ) $=
    ( wn wi pm2.01 ax-1 impbii ) AABZCGADGAEF $.

  $( Theorem *4.81 of [WhiteheadRussell] p. 122.  (Contributed by NM,
     3-Jan-2005.) $)
  pm4.81 $p |- ( ( -. ph -> ph ) <-> ph ) $=
    ( wn wi pm2.18 pm2.24 impbii ) ABACAADAAEF $.

  $( Simplify an implication between two implications when the antecedent of
     the first is a consequence of the antecedent of the second.  The reverse
     form is useful in producing the successor step in induction proofs.
     (Contributed by Paul Chapman, 22-Jun-2011.)  (Proof shortened by Wolf
     Lammen, 14-Sep-2013.) $)
  imim21b $p |- ( ( ps -> ph ) -> ( ( ( ph -> ch ) -> ( ps -> th ) ) <->
                                    ( ps -> ( ch -> th ) ) ) ) $=
    ( wi bi2.04 wb pm5.5 imbi1d imim2i pm5.74d syl5bb ) ACEZBDEEBMDEZEBAEZBCDEZ
    EMBDFOBNPANPGBAMCDACHIJKL $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Logical disjunction and conjunction
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  Here we define disjunction (logical 'or') ` \/ ` ( ~ df-or ) and conjunction
  (logical 'and') ` /\ ` ( ~ df-an ). We also define various rules for
  simplifying and applying them, e.g., ~ olc , ~ orc , and ~ orcom .

$)

  $( Declare connectives for disjunction ('or') and conjunction ('and'). $)
  $c \/ $. $( Vee (read:  'or') $)
  $c /\ $. $( Wedge (read:  'and') $)

  $( Extend wff definition to include disjunction ('or'). $)
  wo $a wff ( ph \/ ps ) $.
  $( Extend wff definition to include conjunction ('and'). $)
  wa $a wff ( ph /\ ps ) $.

  $( Define disjunction (logical 'or').  Definition of [Margaris] p. 49.  When
     the left operand, right operand, or both are true, the result is true;
     when both sides are false, the result is false.  For example, it is true
     that ` ( 2 = 3 \/ 4 = 4 ) ` ( ~ ex-or ).  After we define the constant
     true ` T. ` ( ~ df-tru ) and the constant false ` F. ` ( ~ df-fal ), we
     will be able to prove these truth table values:
     ` ( ( T. \/ T. ) <-> T. ) ` ( ~ truortru ), ` ( ( T. \/ F. ) <-> T. ) `
     ( ~ truorfal ), ` ( ( F. \/ T. ) <-> T. ) ` ( ~ falortru ), and
     ` ( ( F. \/ F. ) <-> F. ) ` ( ~ falorfal ).

     This is our first use of the biconditional connective in a definition; we
     use the biconditional connective in place of the traditional "<=def=>",
     which means the same thing, except that we can manipulate the
     biconditional connective directly in proofs rather than having to rely on
     an informal definition substitution rule.  Note that if we mechanically
     substitute ` ( -. ph -> ps ) ` for ` ( ph \/ ps ) ` , we end up with an
     instance of previously proved theorem ~ biid .  This is the justification
     for the definition, along with the fact that it introduces a new symbol
     ` \/ ` .  Contrast with ` /\ ` ( ~ df-an ), ` -> ` ( ~ wi ), ` -/\ `
     ( ~ df-nan ), and ` \/_ ` ( ~ df-xor ) .  (Contributed by NM,
     5-Aug-1993.) $)
  df-or $a |- ( ( ph \/ ps ) <-> ( -. ph -> ps ) ) $.

  $( Define conjunction (logical 'and').  Definition of [Margaris] p. 49.  When
     both the left and right operand are true, the result is true; when either
     is false, the result is false.  For example, it is true that
     ` ( 2 = 2 /\ 3 = 3 ) ` .  After we define the constant true ` T. `
     ( ~ df-tru ) and the constant false ` F. ` ( ~ df-fal ), we will be able
     to prove these truth table values: ` ( ( T. /\ T. ) <-> T. ) `
     ( ~ truantru ), ` ( ( T. /\ F. ) <-> F. ) ` ( ~ truanfal ),
     ` ( ( F. /\ T. ) <-> F. ) ` ( ~ falantru ), and
     ` ( ( F. /\ F. ) <-> F. ) ` ( ~ falanfal ).

     Contrast with ` \/ ` ( ~ df-or ), ` -> ` ( ~ wi ), ` -/\ ` ( ~ df-nan ),
     and ` \/_ ` ( ~ df-xor ) .  (Contributed by NM, 5-Aug-1993.) $)
  df-an $a |- ( ( ph /\ ps ) <-> -. ( ph -> -. ps ) ) $.

  $( Theorem *4.64 of [WhiteheadRussell] p. 120.  (Contributed by NM,
     3-Jan-2005.) $)
  pm4.64 $p |- ( ( -. ph -> ps ) <-> ( ph \/ ps ) ) $=
    ( wo wn wi df-or bicomi ) ABCADBEABFG $.

  $( Theorem *2.53 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.53 $p |- ( ( ph \/ ps ) -> ( -. ph -> ps ) ) $=
    ( wo wn wi df-or biimpi ) ABCADBEABFG $.

  $( Theorem *2.54 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.54 $p |- ( ( -. ph -> ps ) -> ( ph \/ ps ) ) $=
    ( wo wn wi df-or biimpri ) ABCADBEABFG $.

  ${
    ori.1 $e |- ( ph \/ ps ) $.
    $( Infer implication from disjunction.  (Contributed by NM,
       11-Jun-1994.) $)
    ori $p |- ( -. ph -> ps ) $=
      ( wo wn wi df-or mpbi ) ABDAEBFCABGH $.
  $}

  ${
    orri.1 $e |- ( -. ph -> ps ) $.
    $( Infer implication from disjunction.  (Contributed by NM,
       11-Jun-1994.) $)
    orri $p |- ( ph \/ ps ) $=
      ( wo wn wi df-or mpbir ) ABDAEBFCABGH $.
  $}

  ${
    ord.1 $e |- ( ph -> ( ps \/ ch ) ) $.
    $( Deduce implication from disjunction.  (Contributed by NM,
       18-May-1994.) $)
    ord $p |- ( ph -> ( -. ps -> ch ) ) $=
      ( wo wn wi df-or sylib ) ABCEBFCGDBCHI $.
  $}

  ${
    orrd.1 $e |- ( ph -> ( -. ps -> ch ) ) $.
    $( Deduce implication from disjunction.  (Contributed by NM,
       27-Nov-1995.) $)
    orrd $p |- ( ph -> ( ps \/ ch ) ) $=
      ( wn wi wo pm2.54 syl ) ABECFBCGDBCHI $.
  $}

  ${
    jaoi.1 $e |- ( ph -> ps ) $.
    jaoi.2 $e |- ( ch -> ps ) $.
    $( Inference disjoining the antecedents of two implications.  (Contributed
       by NM, 5-Apr-1994.) $)
    jaoi $p |- ( ( ph \/ ch ) -> ps ) $=
      ( wo wn pm2.53 syl6 pm2.61d2 ) ACFZABKAGCBACHEIDJ $.
  $}

  ${
    jaod.1 $e |- ( ph -> ( ps -> ch ) ) $.
    jaod.2 $e |- ( ph -> ( th -> ch ) ) $.
    $( Deduction disjoining the antecedents of two implications.  (Contributed
       by NM, 18-Aug-1994.) $)
    jaod $p |- ( ph -> ( ( ps \/ th ) -> ch ) ) $=
      ( wo wi com12 jaoi ) BDGACBACHDABCEIADCFIJI $.

    jaod.3 $e |- ( ph -> ( ps \/ th ) ) $.
    $( Eliminate a disjunction in a deduction.  (Contributed by Mario Carneiro,
       29-May-2016.) $)
    mpjaod $p |- ( ph -> ch ) $=
      ( wo jaod mpd ) ABDHCGABCDEFIJ $.
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

  $( Introduction of a disjunct.  Axiom *1.3 of [WhiteheadRussell] p. 96.
     (Contributed by NM, 30-Aug-1993.) $)
  olc $p |- ( ph -> ( ps \/ ph ) ) $=
    ( wn ax-1 orrd ) ABAABCDE $.

  $( Introduction of a disjunct.  Theorem *2.2 of [WhiteheadRussell] p. 104.
     (Contributed by NM, 30-Aug-1993.) $)
  orc $p |- ( ph -> ( ph \/ ps ) ) $=
    ( pm2.24 orrd ) AABABCD $.

  $( Axiom *1.4 of [WhiteheadRussell] p. 96.  (Contributed by NM,
     3-Jan-2005.) $)
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
       (Proof shortened by Wolf Lammen, 14-Nov-2012.) $)
    orci $p |- ( ph \/ ps ) $=
      ( pm2.24i orri ) ABABCDE $.

    $( Deduction introducing a disjunct.  (Contributed by NM, 19-Jan-2008.)
       (Proof shortened by Wolf Lammen, 14-Nov-2012.) $)
    olci $p |- ( ps \/ ph ) $=
      ( wn a1i orri ) BAABDCEF $.
  $}

  ${
    orcd.1 $e |- ( ph -> ps ) $.
    $( Deduction introducing a disjunct.  A translation of natural deduction
       rule ` \/ ` IR ( ` \/ ` insertion right), see ~ natded .  (Contributed
       by NM, 20-Sep-2007.) $)
    orcd $p |- ( ph -> ( ps \/ ch ) ) $=
      ( wo orc syl ) ABBCEDBCFG $.

    $( Deduction introducing a disjunct.  A translation of natural deduction
       rule ` \/ ` IL ( ` \/ ` insertion left), see ~ natded .  (Contributed by
       NM, 11-Apr-2008.)  (Proof shortened by Wolf Lammen, 3-Oct-2013.) $)
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

  $( Slight generalization of Theorem *2.67 of [WhiteheadRussell] p. 107.
     (Contributed by NM, 3-Jan-2005.) $)
  pm2.67-2 $p |- ( ( ( ph \/ ch ) -> ps ) -> ( ph -> ps ) ) $=
    ( wo orc imim1i ) AACDBACEF $.

  $( Theorem *2.67 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.67 $p |- ( ( ( ph \/ ps ) -> ps ) -> ( ph -> ps ) ) $=
    ( pm2.67-2 ) ABBC $.

  $( Theorem *2.25 of [WhiteheadRussell] p. 104.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.25 $p |- ( ph \/ ( ( ph \/ ps ) -> ps ) ) $=
    ( wo wi orel1 orri ) AABCBDABEF $.

  $( A wff is equivalent to its disjunction with falsehood.  Theorem *4.74 of
     [WhiteheadRussell] p. 121.  (Contributed by NM, 23-Mar-1995.)  (Proof
     shortened by Wolf Lammen, 18-Nov-2012.) $)
  biorf $p |- ( -. ph -> ( ps <-> ( ph \/ ps ) ) ) $=
    ( wn wo olc orel1 impbid2 ) ACBABDBAEABFG $.

  $( A wff is equivalent to its negated disjunction with falsehood.
     (Contributed by NM, 9-Jul-2012.) $)
  biortn $p |- ( ph -> ( ps <-> ( -. ph \/ ps ) ) ) $=
    ( wn wo wb notnot1 biorf syl ) AACZCBIBDEAFIBGH $.

  ${
    biorfi.1 $e |- -. ph $.
    $( A wff is equivalent to its disjunction with falsehood.  (Contributed by
       NM, 23-Mar-1995.) $)
    biorfi $p |- ( ps <-> ( ps \/ ph ) ) $=
      ( wn wo wb orc orel2 impbid2 ax-mp ) ADZBBAEZFCKBLBAGABHIJ $.
  $}

  $( Theorem *2.621 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.621 $p |- ( ( ph -> ps ) -> ( ( ph \/ ps ) -> ps ) ) $=
    ( wi id idd jaod ) ABCZABBGDGBEF $.

  $( Theorem *2.62 of [WhiteheadRussell] p. 107.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 13-Dec-2013.) $)
  pm2.62 $p |- ( ( ph \/ ps ) -> ( ( ph -> ps ) -> ps ) ) $=
    ( wi wo pm2.621 com12 ) ABCABDBABEF $.

  $( Theorem *2.68 of [WhiteheadRussell] p. 108.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.68 $p |- ( ( ( ph -> ps ) -> ps ) -> ( ph \/ ps ) ) $=
    ( wi jarl orrd ) ABCBCABABBDE $.

  $( Logical 'or' expressed in terms of implication only.  Theorem *5.25 of
     [WhiteheadRussell] p. 124.  (Contributed by NM, 12-Aug-2004.)  (Proof
     shortened by Wolf Lammen, 20-Oct-2012.) $)
  dfor2 $p |- ( ( ph \/ ps ) <-> ( ( ph -> ps ) -> ps ) ) $=
    ( wo wi pm2.62 pm2.68 impbii ) ABCABDBDABEABFG $.

  $( Implication in terms of disjunction.  Theorem *4.6 of [WhiteheadRussell]
     p. 120.  (Contributed by NM, 5-Aug-1993.) $)
  imor $p |- ( ( ph -> ps ) <-> ( -. ph \/ ps ) ) $=
    ( wi wn wo notnot imbi1i df-or bitr4i ) ABCADZDZBCJBEAKBAFGJBHI $.

  ${
    imori.1 $e |- ( ph -> ps ) $.
    $( Infer disjunction from implication.  (Contributed by NM,
       12-Mar-2012.) $)
    imori $p |- ( -. ph \/ ps ) $=
      ( wi wn wo imor mpbi ) ABDAEBFCABGH $.
  $}

  ${
    imorri.1 $e |- ( -. ph \/ ps ) $.
    $( Infer implication from disjunction.  (Contributed by Jonathan Ben-Naim,
       3-Jun-2011.) $)
    imorri $p |- ( ph -> ps ) $=
      ( wi wn wo imor mpbir ) ABDAEBFCABGH $.
  $}

  $( Law of excluded middle, also called the principle of _tertium non datur_.
     Theorem *2.11 of [WhiteheadRussell] p. 101.  It says that something is
     either true or not true; there are no in-between values of truth.  This is
     an essential distinction of our classical logic and is not a theorem of
     intuitionistic logic.  (Contributed by NM, 5-Aug-1993.) $)
  exmid $p |- ( ph \/ -. ph ) $=
    ( wn id orri ) AABZECD $.

  $( Law of excluded middle in a context.  (Contributed by Mario Carneiro,
     9-Feb-2017.) $)
  exmidd $p |- ( ph -> ( ps \/ -. ps ) ) $=
    ( wn wo exmid a1i ) BBCDABEF $.

  $( Theorem *2.1 of [WhiteheadRussell] p. 101.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 23-Nov-2012.) $)
  pm2.1 $p |- ( -. ph \/ ph ) $=
    ( id imori ) AAABC $.

  $( Theorem *2.13 of [WhiteheadRussell] p. 101.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.13 $p |- ( ph \/ -. -. -. ph ) $=
    ( wn notnot1 orri ) AABZBBECD $.

  $( Theorem *4.62 of [WhiteheadRussell] p. 120.  (Contributed by NM,
     3-Jan-2005.) $)
  pm4.62 $p |- ( ( ph -> -. ps ) <-> ( -. ph \/ -. ps ) ) $=
    ( wn imor ) ABCD $.

  $( Theorem *4.66 of [WhiteheadRussell] p. 120.  (Contributed by NM,
     3-Jan-2005.) $)
  pm4.66 $p |- ( ( -. ph -> -. ps ) <-> ( ph \/ -. ps ) ) $=
    ( wn pm4.64 ) ABCD $.

  $( Theorem *4.63 of [WhiteheadRussell] p. 120.  (Contributed by NM,
     3-Jan-2005.) $)
  pm4.63 $p |- ( -. ( ph -> -. ps ) <-> ( ph /\ ps ) ) $=
    ( wa wn wi df-an bicomi ) ABCABDEDABFG $.

  $( Express implication in terms of conjunction.  (Contributed by NM,
     9-Apr-1994.) $)
  imnan $p |- ( ( ph -> -. ps ) <-> -. ( ph /\ ps ) ) $=
    ( wa wn wi df-an con2bii ) ABCABDEABFG $.

  ${
    imnani.1 $e |- -. ( ph /\ ps ) $.
    $( Express implication in terms of conjunction.  (Contributed by Mario
       Carneiro, 28-Sep-2015.) $)
    imnani $p |- ( ph -> -. ps ) $=
      ( wn wi wa imnan mpbir ) ABDEABFDCABGH $.
  $}

  $( Express implication in terms of conjunction.  Theorem 3.4(27) of [Stoll]
     p. 176.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf
     Lammen, 30-Oct-2012.) $)
  iman $p |- ( ( ph -> ps ) <-> -. ( ph /\ -. ps ) ) $=
    ( wi wn wa notnot imbi2i imnan bitri ) ABCABDZDZCAJEDBKABFGAJHI $.

  $( Express conjunction in terms of implication.  (Contributed by NM,
     2-Aug-1994.) $)
  annim $p |- ( ( ph /\ -. ps ) <-> -. ( ph -> ps ) ) $=
    ( wi wn wa iman con2bii ) ABCABDEABFG $.

  $( Theorem *4.61 of [WhiteheadRussell] p. 120.  (Contributed by NM,
     3-Jan-2005.) $)
  pm4.61 $p |- ( -. ( ph -> ps ) <-> ( ph /\ -. ps ) ) $=
    ( wn wa wi annim bicomi ) ABCDABECABFG $.

  $( Theorem *4.65 of [WhiteheadRussell] p. 120.  (Contributed by NM,
     3-Jan-2005.) $)
  pm4.65 $p |- ( -. ( -. ph -> ps ) <-> ( -. ph /\ -. ps ) ) $=
    ( wn pm4.61 ) ACBD $.

  $( Theorem *4.67 of [WhiteheadRussell] p. 120.  (Contributed by NM,
     3-Jan-2005.) $)
  pm4.67 $p |- ( -. ( -. ph -> -. ps ) <-> ( -. ph /\ ps ) ) $=
    ( wn pm4.63 ) ACBD $.

  ${
    imp.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Importation inference.  (Contributed by NM, 5-Aug-1993.)  (Proof
       shortened by Eric Schmidt, 22-Dec-2006.) $)
    imp $p |- ( ( ph /\ ps ) -> ch ) $=
      ( wa wn wi df-an impi sylbi ) ABEABFGFCABHABCDIJ $.

    $( Importation inference with commuted antecedents.  (Contributed by NM,
       25-May-2005.) $)
    impcom $p |- ( ( ps /\ ph ) -> ch ) $=
      ( com12 imp ) BACABCDEF $.
  $}

  ${
    imp3.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    $( Importation deduction.  (Contributed by NM, 31-Mar-1994.) $)
    imp3a $p |- ( ph -> ( ( ps /\ ch ) -> th ) ) $=
      ( wa wi com3l imp com12 ) BCFADBCADGABCDEHIJ $.

    $( An importation inference.  (Contributed by NM, 26-Apr-1994.) $)
    imp31 $p |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $=
      ( wa wi imp ) ABFCDABCDGEHH $.

    $( An importation inference.  (Contributed by NM, 26-Apr-1994.) $)
    imp32 $p |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $=
      ( wa imp3a imp ) ABCFDABCDEGH $.
  $}

  ${
    exp.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( Exportation inference.  (This theorem used to be labeled "exp" but was
       changed to "ex" so as not to conflict with the math token "exp", per the
       June 2006 Metamath spec change.)  A translation of natural deduction
       rule ` -> ` I ( ` -> ` introduction), see ~ natded .  (Contributed by
       NM, 5-Aug-1993.)  (Proof shortened by Eric Schmidt, 22-Dec-2006.) $)
    ex $p |- ( ph -> ( ps -> ch ) ) $=
      ( wn wi wa df-an sylbir expi ) ABCABEFEABGCABHDIJ $.

    $( Exportation inference with commuted antecedents.  (Contributed by NM,
       25-May-2005.) $)
    expcom $p |- ( ps -> ( ph -> ch ) ) $=
      ( ex com12 ) ABCABCDEF $.
  $}

  ${
    exp3a.1 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
    $( Exportation deduction.  (Contributed by NM, 20-Aug-1993.) $)
    exp3a $p |- ( ph -> ( ps -> ( ch -> th ) ) ) $=
      ( wi wa com12 ex com3r ) BCADBCADFABCGDEHIJ $.

    $( A deduction version of exportation, followed by importation.
       (Contributed by NM, 6-Sep-2008.) $)
    expdimp $p |- ( ( ph /\ ps ) -> ( ch -> th ) ) $=
      ( wi exp3a imp ) ABCDFABCDEGH $.
  $}

  ${
    impancom.1 $e |- ( ( ph /\ ps ) -> ( ch -> th ) ) $.
    $( Mixed importation/commutation inference.  (Contributed by NM,
       22-Jun-2013.) $)
    impancom $p |- ( ( ph /\ ch ) -> ( ps -> th ) ) $=
      ( wi ex com23 imp ) ACBDFABCDABCDFEGHI $.
  $}

  ${
    con3and.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Variant of ~ con3d with importation.  (Contributed by Jonathan Ben-Naim,
       3-Jun-2011.) $)
    con3and $p |- ( ( ph /\ -. ch ) -> -. ps ) $=
      ( wn con3d imp ) ACEBEABCDFG $.
  $}

  ${
    pm2.01da.1 $e |- ( ( ph /\ ps ) -> -. ps ) $.
    $( Deduction based on reductio ad absurdum.  (Contributed by Mario
       Carneiro, 9-Feb-2017.) $)
    pm2.01da $p |- ( ph -> -. ps ) $=
      ( wn ex pm2.01d ) ABABBDCEF $.
  $}

  ${
    pm2.18da.1 $e |- ( ( ph /\ -. ps ) -> ps ) $.
    $( Deduction based on reductio ad absurdum.  (Contributed by Mario
       Carneiro, 9-Feb-2017.) $)
    pm2.18da $p |- ( ph -> ps ) $=
      ( wn ex pm2.18d ) ABABDBCEF $.
  $}

  $( Theorem *3.3 (Exp) of [WhiteheadRussell] p. 112.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 24-Mar-2013.) $)
  pm3.3 $p |- ( ( ( ph /\ ps ) -> ch ) -> ( ph -> ( ps -> ch ) ) ) $=
    ( wa wi id exp3a ) ABDCEZABCHFG $.

  $( Theorem *3.31 (Imp) of [WhiteheadRussell] p. 112.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 24-Mar-2013.) $)
  pm3.31 $p |- ( ( ph -> ( ps -> ch ) ) -> ( ( ph /\ ps ) -> ch ) ) $=
    ( wi id imp3a ) ABCDDZABCGEF $.

  $( Import-export theorem.  Part of Theorem *4.87 of [WhiteheadRussell]
     p. 122.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf
     Lammen, 24-Mar-2013.) $)
  impexp $p |- ( ( ( ph /\ ps ) -> ch ) <-> ( ph -> ( ps -> ch ) ) ) $=
    ( wa wi pm3.3 pm3.31 impbii ) ABDCEABCEEABCFABCGH $.

  $( Join antecedents with conjunction.  Theorem *3.2 of [WhiteheadRussell]
     p. 111.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf
     Lammen, 12-Nov-2012.) $)
  pm3.2 $p |- ( ph -> ( ps -> ( ph /\ ps ) ) ) $=
    ( wa id ex ) ABABCZFDE $.

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
      ( wa ancom syl5bi ) CBFBCFADCBGEH $.
  $}

  ${
    pm3.2i.1 $e |- ph $.
    pm3.2i.2 $e |- ps $.
    $( Infer conjunction of premises.  (Contributed by NM, 5-Aug-1993.) $)
    pm3.2i $p |- ( ph /\ ps ) $=
      ( wa pm3.2 mp2 ) ABABECDABFG $.
  $}

  $( Nested conjunction of antecedents.  (Contributed by NM, 5-Aug-1993.) $)
  pm3.43i $p |- ( ( ph -> ps )
      -> ( ( ph -> ch ) -> ( ph -> ( ps /\ ch ) ) ) ) $=
    ( wa pm3.2 imim3i ) BCBCDABCEF $.

  $( Elimination of a conjunct.  Theorem *3.26 (Simp) of [WhiteheadRussell]
     p. 112.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf
     Lammen, 13-Nov-2012.) $)
  simpl $p |- ( ( ph /\ ps ) -> ph ) $=
    ( ax-1 imp ) ABAABCD $.

  ${
    simpli.1 $e |- ( ph /\ ps ) $.
    $( Inference eliminating a conjunct.  (Contributed by NM, 15-Jun-1994.) $)
    simpli $p |- ph $=
      ( wa simpl ax-mp ) ABDACABEF $.
  $}

  ${
    simpld.1 $e |- ( ph -> ( ps /\ ch ) ) $.
    $( Deduction eliminating a conjunct.  A translation of natural deduction
       rule ` /\ ` EL ( ` /\ ` elimination left), see ~ natded .  (Contributed
       by NM, 5-Aug-1993.) $)
    simpld $p |- ( ph -> ps ) $=
      ( wa simpl syl ) ABCEBDBCFG $.
  $}

  ${
    simplbi.1 $e |- ( ph <-> ( ps /\ ch ) ) $.
    $( Deduction eliminating a conjunct.  (Contributed by NM, 27-May-1998.) $)
    simplbi $p |- ( ph -> ps ) $=
      ( wa biimpi simpld ) ABCABCEDFG $.
  $}

  $( Elimination of a conjunct.  Theorem *3.27 (Simp) of [WhiteheadRussell]
     p. 112.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf
     Lammen, 13-Nov-2012.) $)
  simpr $p |- ( ( ph /\ ps ) -> ps ) $=
    ( idd imp ) ABBABCD $.

  ${
    simpri.1 $e |- ( ph /\ ps ) $.
    $( Inference eliminating a conjunct.  (Contributed by NM, 15-Jun-1994.) $)
    simpri $p |- ps $=
      ( wa simpr ax-mp ) ABDBCABEF $.
  $}

  ${
    simprd.1 $e |- ( ph -> ( ps /\ ch ) ) $.
    $( Deduction eliminating a conjunct.  (Contributed by NM, 5-Aug-1993.)  A
       translation of natural deduction rule ` /\ ` ER ( ` /\ ` elimination
       right), see ~ natded .  (Proof shortened by Wolf Lammen, 3-Oct-2013.) $)
    simprd $p |- ( ph -> ch ) $=
      ( ancomd simpld ) ACBABCDEF $.
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
    $( A syllogism deduction with conjoined antecedents.  (Contributed by NM,
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
      ( wi exp3a syld imp3a ) ABDEABCDEHFACDEGIJK $.
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

  $( Negated conjunction in terms of disjunction (De Morgan's law).  Theorem
     *4.51 of [WhiteheadRussell] p. 120.  (Contributed by NM, 5-Aug-1993.)
     (Proof shortened by Andrew Salmon, 13-May-2011.) $)
  ianor $p |- ( -. ( ph /\ ps ) <-> ( -. ph \/ -. ps ) ) $=
    ( wa wn wi wo imnan pm4.62 bitr3i ) ABCDABDZEADJFABGABHI $.

  $( Conjunction in terms of disjunction (De Morgan's law).  Theorem *4.5 of
     [WhiteheadRussell] p. 120.  (Contributed by NM, 5-Aug-1993.)  (Proof
     shortened by Wolf Lammen, 3-Nov-2012.) $)
  anor $p |- ( ( ph /\ ps ) <-> -. ( -. ph \/ -. ps ) ) $=
    ( wn wo wa ianor bicomi con2bii ) ACBCDZABEZJCIABFGH $.

  $( Negated disjunction in terms of conjunction (De Morgan's law).  Compare
     Theorem *4.56 of [WhiteheadRussell] p. 120.  (Contributed by NM,
     5-Aug-1993.)  (Proof shortened by Andrew Salmon, 7-May-2011.) $)
  ioran $p |- ( -. ( ph \/ ps ) <-> ( -. ph /\ -. ps ) ) $=
    ( wn wi wa wo pm4.65 pm4.64 xchnxbi ) ACZBDJBCEABFABGABHI $.

  $( Theorem *4.52 of [WhiteheadRussell] p. 120.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 5-Nov-2012.) $)
  pm4.52 $p |- ( ( ph /\ -. ps ) <-> -. ( -. ph \/ ps ) ) $=
    ( wn wa wi wo annim imor xchbinx ) ABCDABEACBFABGABHI $.

  $( Theorem *4.53 of [WhiteheadRussell] p. 120.  (Contributed by NM,
     3-Jan-2005.) $)
  pm4.53 $p |- ( -. ( ph /\ -. ps ) <-> ( -. ph \/ ps ) ) $=
    ( wn wo wa pm4.52 con2bii bicomi ) ACBDZABCEZCJIABFGH $.

  $( Theorem *4.54 of [WhiteheadRussell] p. 120.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 5-Nov-2012.) $)
  pm4.54 $p |- ( ( -. ph /\ ps ) <-> -. ( ph \/ -. ps ) ) $=
    ( wn wa wi wo df-an pm4.66 xchbinx ) ACZBDJBCZEAKFJBGABHI $.

  $( Theorem *4.55 of [WhiteheadRussell] p. 120.  (Contributed by NM,
     3-Jan-2005.) $)
  pm4.55 $p |- ( -. ( -. ph /\ ps ) <-> ( ph \/ -. ps ) ) $=
    ( wn wo wa pm4.54 con2bii bicomi ) ABCDZACBEZCJIABFGH $.

  $( Theorem *4.56 of [WhiteheadRussell] p. 120.  (Contributed by NM,
     3-Jan-2005.) $)
  pm4.56 $p |- ( ( -. ph /\ -. ps ) <-> -. ( ph \/ ps ) ) $=
    ( wo wn wa ioran bicomi ) ABCDADBDEABFG $.

  $( Disjunction in terms of conjunction (De Morgan's law).  Compare Theorem
     *4.57 of [WhiteheadRussell] p. 120.  (Contributed by NM, 5-Aug-1993.)
     (Proof shortened by Andrew Salmon, 7-May-2011.) $)
  oran $p |- ( ( ph \/ ps ) <-> -. ( -. ph /\ -. ps ) ) $=
    ( wn wa wo pm4.56 con2bii ) ACBCDABEABFG $.

  $( Theorem *4.57 of [WhiteheadRussell] p. 120.  (Contributed by NM,
     3-Jan-2005.) $)
  pm4.57 $p |- ( -. ( -. ph /\ -. ps ) <-> ( ph \/ ps ) ) $=
    ( wo wn wa oran bicomi ) ABCADBDEDABFG $.

  $( Theorem *3.1 of [WhiteheadRussell] p. 111.  (Contributed by NM,
     3-Jan-2005.) $)
  pm3.1 $p |- ( ( ph /\ ps ) -> -. ( -. ph \/ -. ps ) ) $=
    ( wa wn wo anor biimpi ) ABCADBDEDABFG $.

  $( Theorem *3.11 of [WhiteheadRussell] p. 111.  (Contributed by NM,
     3-Jan-2005.) $)
  pm3.11 $p |- ( -. ( -. ph \/ -. ps ) -> ( ph /\ ps ) ) $=
    ( wa wn wo anor biimpri ) ABCADBDEDABFG $.

  $( Theorem *3.12 of [WhiteheadRussell] p. 111.  (Contributed by NM,
     3-Jan-2005.) $)
  pm3.12 $p |- ( ( -. ph \/ -. ps ) \/ ( ph /\ ps ) ) $=
    ( wn wo wa pm3.11 orri ) ACBCDABEABFG $.

  $( Theorem *3.13 of [WhiteheadRussell] p. 111.  (Contributed by NM,
     3-Jan-2005.) $)
  pm3.13 $p |- ( -. ( ph /\ ps ) -> ( -. ph \/ -. ps ) ) $=
    ( wn wo wa pm3.11 con1i ) ACBCDABEABFG $.

  $( Theorem *3.14 of [WhiteheadRussell] p. 111.  (Contributed by NM,
     3-Jan-2005.) $)
  pm3.14 $p |- ( ( -. ph \/ -. ps ) -> -. ( ph /\ ps ) ) $=
    ( wa wn wo pm3.1 con2i ) ABCADBDEABFG $.

  $( Introduction of antecedent as conjunct.  Theorem *4.73 of
     [WhiteheadRussell] p. 121.  (Contributed by NM, 30-Mar-1994.) $)
  iba $p |- ( ph -> ( ps <-> ( ps /\ ph ) ) ) $=
    ( wa pm3.21 simpl impbid1 ) ABBACABDBAEF $.

  $( Introduction of antecedent as conjunct.  (Contributed by NM,
     5-Dec-1995.) $)
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
    jaao.1 $e |- ( ph -> ( ps -> ch ) ) $.
    jaao.2 $e |- ( th -> ( ta -> ch ) ) $.
    $( Inference conjoining and disjoining the antecedents of two
       implications.  (Contributed by NM, 30-Sep-1999.) $)
    jaao $p |- ( ( ph /\ th ) -> ( ( ps \/ ta ) -> ch ) ) $=
      ( wa wi adantr adantl jaod ) ADHBCEABCIDFJDECIAGKL $.

    $( Inference disjoining and conjoining the antecedents of two
       implications.  (Contributed by Stefan Allan, 1-Nov-2008.) $)
    jaoa $p |- ( ( ph \/ th ) -> ( ( ps /\ ta ) -> ch ) ) $=
      ( wa wi adantrd adantld jaoi ) ABEHCIDABCEFJDECBGKL $.
  $}

  $( Theorem *3.44 of [WhiteheadRussell] p. 113.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 3-Oct-2013.) $)
  pm3.44 $p |- ( ( ( ps -> ph ) /\ ( ch -> ph ) )
      -> ( ( ps \/ ch ) -> ph ) ) $=
    ( wi id jaao ) BADZBACADZCGEHEF $.

  $( Disjunction of antecedents.  Compare Theorem *3.44 of [WhiteheadRussell]
     p. 113.  (Contributed by NM, 5-Apr-1994.)  (Proof shortened by Wolf
     Lammen, 4-Apr-2013.) $)
  jao $p |- ( ( ph -> ps ) -> ( ( ch -> ps ) -> ( ( ph \/ ch ) -> ps ) ) ) $=
    ( wi wo pm3.44 ex ) ABDCBDACEBDBACFG $.

  $( Axiom *1.2 of [WhiteheadRussell] p. 96, which they call "Taut".
     (Contributed by NM, 3-Jan-2005.) $)
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
    $( Inference adding a left disjunct to both sides of a logical
       equivalence.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf
       Lammen, 12-Dec-2012.) $)
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

  ${
    jca.1 $e |- ( ph -> ps ) $.
    jca.2 $e |- ( ph -> ch ) $.
    $( Deduce conjunction of the consequents of two implications ("join
       consequents with 'and'").  Equivalent to the natural deduction rule
       ` /\ ` I ( ` /\ ` introduction), see ~ natded .  (Contributed by NM,
       5-Aug-1993.)  (Proof shortened by Wolf Lammen, 25-Oct-2012.) $)
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

    $( Inference conjoining a theorem to right of consequent in an
       implication.  (Contributed by NM, 31-Dec-1993.) $)
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
    $( Deduction conjoining a theorem to right of consequent in an
       implication.  (Contributed by NM, 21-Apr-2005.) $)
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

  $( Conjoin antecedents and consequents of two premises.  This is the closed
     theorem form of ~ anim12d .  Theorem *3.47 of [WhiteheadRussell] p. 113.
     It was proved by Leibniz, and it evidently pleased him enough to call it
     _praeclarum theorema_ (splendid theorem).  (Contributed by NM,
     12-Aug-1993.)  (Proof shortened by Wolf Lammen, 7-Apr-2013.) $)
  prth $p |- ( ( ( ph -> ps ) /\ ( ch -> th ) )
       -> ( ( ph /\ ch ) -> ( ps /\ th ) ) ) $=
    ( wi wa simpl simpr anim12d ) ABEZCDEZFABCDJKGJKHI $.

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

  ${
    pm2.65da.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    pm2.65da.2 $e |- ( ( ph /\ ps ) -> -. ch ) $.
    $( Deduction rule for proof by contradiction.  (Contributed by NM,
       12-Jun-2014.) $)
    pm2.65da $p |- ( ph -> -. ps ) $=
      ( ex wn pm2.65d ) ABCABCDFABCGEFH $.
  $}

  $( Theorem *4.44 of [WhiteheadRussell] p. 119.  (Contributed by NM,
     3-Jan-2005.) $)
  pm4.44 $p |- ( ph <-> ( ph \/ ( ph /\ ps ) ) ) $=
    ( wa wo orc id simpl jaoi impbii ) AAABCZDAJEAAJAFABGHI $.

  $( Theorem *4.14 of [WhiteheadRussell] p. 117.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 23-Oct-2012.) $)
  pm4.14 $p |- ( ( ( ph /\ ps ) -> ch ) <-> ( ( ph /\ -. ch ) -> -. ps ) ) $=
    ( wi wn wa con34b imbi2i impexp 3bitr4i ) ABCDZDACEZBEZDZDABFCDALFMDKNABCGH
    ABCIALMIJ $.

  $( Theorem *3.37 (Transp) of [WhiteheadRussell] p. 112.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 23-Oct-2012.) $)
  pm3.37 $p |- ( ( ( ph /\ ps ) -> ch ) -> ( ( ph /\ -. ch ) -> -. ps ) ) $=
    ( wa wi wn pm4.14 biimpi ) ABDCEACFDBFEABCGH $.

  $( Theorem to move a conjunct in and out of a negation.  (Contributed by NM,
     9-Nov-2003.) $)
  nan $p |- ( ( ph -> -. ( ps /\ ch ) ) <-> ( ( ph /\ ps ) -> -. ch ) ) $=
    ( wa wn wi impexp imnan imbi2i bitr2i ) ABDCEZFABKFZFABCDEZFABKGLMABCHIJ $.

  $( Theorem *4.15 of [WhiteheadRussell] p. 117.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 18-Nov-2012.) $)
  pm4.15 $p |- ( ( ( ph /\ ps ) -> -. ch ) <-> ( ( ps /\ ch ) -> -. ph ) ) $=
    ( wa wn wi con2b nan bitr2i ) BCDZAEFAJEFABDCEFJAGABCHI $.

  $( Implication distributes over disjunction.  Theorem *4.78 of
     [WhiteheadRussell] p. 121.  (Contributed by NM, 3-Jan-2005.)  (Proof
     shortened by Wolf Lammen, 19-Nov-2012.) $)
  pm4.78 $p |- ( ( ( ph -> ps ) \/ ( ph -> ch ) ) <->
                ( ph -> ( ps \/ ch ) ) ) $=
    ( wn wo wi orordi imor orbi12i 3bitr4ri ) ADZBCEZEKBEZKCEZEALFABFZACFZEKBCG
    ALHOMPNABHACHIJ $.

  $( Theorem *4.79 of [WhiteheadRussell] p. 121.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 27-Jun-2013.) $)
  pm4.79 $p |- ( ( ( ps -> ph ) \/ ( ch -> ph ) ) <->
                ( ( ps /\ ch ) -> ph ) ) $=
    ( wi wo wa id jaoa wn simplim pm3.3 syl5 orrd impbii ) BADZCADZEBCFADZOBAPC
    OGPGHQOPOIBQPBAJBCAKLMN $.

  $( Theorem *4.87 of [WhiteheadRussell] p. 122.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Eric Schmidt, 26-Oct-2006.) $)
  pm4.87 $p |- ( ( ( ( ( ph /\ ps ) -> ch ) <-> ( ph -> ( ps -> ch ) ) ) /\
                ( ( ph -> ( ps -> ch ) ) <-> ( ps -> ( ph -> ch ) ) ) ) /\
                ( ( ps -> ( ph -> ch ) ) <-> ( ( ps /\ ph ) -> ch ) ) ) $=
    ( wa wi wb impexp bi2.04 pm3.2i bicomi ) ABDCEABCEEZFZKBACEEZFZDMBADCEZFLNA
    BCGABCHIOMBACGJI $.

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
      ( wi wa impexp syl6ibr ) ABCDEGGCDHEGFCDEIJ $.

    $( An importation inference.  (Contributed by NM, 26-Apr-1994.) $)
    imp4b $p |- ( ( ph /\ ps ) -> ( ( ch /\ th ) -> ta ) ) $=
      ( wa wi imp4a imp ) ABCDGEHABCDEFIJ $.

    $( An importation inference.  (Contributed by NM, 26-Apr-1994.) $)
    imp4c $p |- ( ph -> ( ( ( ps /\ ch ) /\ th ) -> ta ) ) $=
      ( wa wi imp3a ) ABCGDEABCDEHFII $.

    $( An importation inference.  (Contributed by NM, 26-Apr-1994.) $)
    imp4d $p |- ( ph -> ( ( ps /\ ( ch /\ th ) ) -> ta ) ) $=
      ( wa imp4a imp3a ) ABCDGEABCDEFHI $.

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
      ( wa wi imp31 imp3a ) ABHCHDEFABCDEFIIGJK $.

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
      ( wi ex imp3a ) ABCDABCDFEGH $.
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
      ( wa ex exp3a ) ABCDABCFDEGH $.
  $}

  ${
    exp4a.1 $e |- ( ph -> ( ps -> ( ( ch /\ th ) -> ta ) ) ) $.
    $( An exportation inference.  (Contributed by NM, 26-Apr-1994.) $)
    exp4a $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $=
      ( wa wi impexp syl6ib ) ABCDGEHCDEHHFCDEIJ $.
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
      ( wi wa exp3a ) ABCDEGABCHDEFII $.
  $}

  ${
    exp4d.1 $e |- ( ph -> ( ( ps /\ ( ch /\ th ) ) -> ta ) ) $.
    $( An exportation inference.  (Contributed by NM, 26-Apr-1994.) $)
    exp4d $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $=
      ( wa exp3a exp4a ) ABCDEABCDGEFHI $.
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
      ( wi wa exp31 exp3a ) ABCDEGABCHDEFIJ $.
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
      ( wi wa exp32 exp3a ) ABCDEGABCHDEFIJ $.
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
      ( wi wa exp4a exp3a ) ABCDEFHHABCIDEFGJK $.
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
      ( exp31 imp3a ) ABCDABCDEFG $.
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
      ( exp3a imp31 ) ABCDABCDEFG $.
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
    $( Inference form of ~ exbir .  This proof is ~ exbiriVD automatically
       translated and minimized.  (Contributed by Alan Sare, 31-Dec-2011.)
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
    $( Deduction eliminating a conjunct.  Automatically derived from
       ~ simplbi2VD .  (Contributed by Alan Sare, 31-Dec-2011.) $)
    simplbi2 $p |- ( ps -> ( ch -> ph ) ) $=
      ( wa biimpri ex ) BCAABCEDFG $.
  $}

  $( A theorem similar to the standard definition of the biconditional.
     Definition of [Margaris] p. 49.  (Contributed by NM, 5-Aug-1993.) $)
  dfbi2 $p |- ( ( ph <-> ps ) <-> ( ( ph -> ps ) /\ ( ps -> ph ) ) ) $=
    ( wb wi wn wa dfbi1 df-an bitr4i ) ABCABDZBADZEDEJKFABGJKHI $.

  $( Definition ~ df-bi rewritten in an abbreviated form to help intuitive
     understanding of that definition.  Note that it is a conjunction of two
     implications; one which asserts properties that follow from the
     biconditional and one which asserts properties that imply the
     biconditional.  (Contributed by NM, 15-Aug-2008.) $)
  dfbi $p |- ( ( ( ph <-> ps ) -> ( ( ph -> ps ) /\ ( ps -> ph ) ) )
        /\ ( ( ( ph -> ps ) /\ ( ps -> ph ) ) -> ( ph <-> ps ) ) ) $=
    ( wb wi wa dfbi2 biimpi biimpri pm3.2i ) ABCZABDBADEZDKJDJKABFZGJKLHI $.

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
    $( Inference converting an implication to a biconditional with
       conjunction.  Inference from Theorem *4.71 of [WhiteheadRussell]
       p. 120.  (Contributed by NM, 4-Jan-2004.) $)
    pm4.71i $p |- ( ph <-> ( ph /\ ps ) ) $=
      ( wi wa wb pm4.71 mpbi ) ABDAABEFCABGH $.
  $}

  ${
    pm4.71ri.1 $e |- ( ph -> ps ) $.
    $( Inference converting an implication to a biconditional with
       conjunction.  Inference from Theorem *4.71 of [WhiteheadRussell] p. 120
       (with conjunct reversed).  (Contributed by NM, 1-Dec-2003.) $)
    pm4.71ri $p |- ( ph <-> ( ps /\ ph ) ) $=
      ( wi wa wb pm4.71r mpbi ) ABDABAEFCABGH $.
  $}

  ${
    pm4.71rd.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction converting an implication to a biconditional with
       conjunction.  Deduction from Theorem *4.71 of [WhiteheadRussell]
       p. 120.  (Contributed by Mario Carneiro, 25-Dec-2016.) $)
    pm4.71d $p |- ( ph -> ( ps <-> ( ps /\ ch ) ) ) $=
      ( wi wa wb pm4.71 sylib ) ABCEBBCFGDBCHI $.

    $( Deduction converting an implication to a biconditional with
       conjunction.  Deduction from Theorem *4.71 of [WhiteheadRussell]
       p. 120.  (Contributed by NM, 10-Feb-2005.) $)
    pm4.71rd $p |- ( ph -> ( ps <-> ( ch /\ ps ) ) ) $=
      ( wi wa wb pm4.71r sylib ) ABCEBCBFGDBCHI $.
  $}

  $( Distribution of implication over biconditional.  Theorem *5.32 of
     [WhiteheadRussell] p. 125.  (Contributed by NM, 1-Aug-1994.) $)
  pm5.32 $p |- ( ( ph -> ( ps <-> ch ) ) <->
               ( ( ph /\ ps ) <-> ( ph /\ ch ) ) ) $=
    ( wb wi wn wa notbi imbi2i pm5.74 3bitri df-an bibi12i bitr4i ) ABCDZEZABFZ
    EZFZACFZEZFZDZABGZACGZDPAQTDZERUADUCOUFABCHIAQTJRUAHKUDSUEUBABLACLMN $.

  ${
    pm5.32i.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Distribution of implication over biconditional (inference rule).
       (Contributed by NM, 1-Aug-1994.) $)
    pm5.32i $p |- ( ( ph /\ ps ) <-> ( ph /\ ch ) ) $=
      ( wb wi wa pm5.32 mpbi ) ABCEFABGACGEDABCHI $.

    $( Distribution of implication over biconditional (inference rule).
       (Contributed by NM, 12-Mar-1995.) $)
    pm5.32ri $p |- ( ( ps /\ ph ) <-> ( ch /\ ph ) ) $=
      ( wa pm5.32i ancom 3bitr4i ) ABEACEBAECAEABCDFBAGCAGH $.
  $}

  ${
    pm5.32d.1 $e |- ( ph -> ( ps -> ( ch <-> th ) ) ) $.
    $( Distribution of implication over biconditional (deduction rule).
       (Contributed by NM, 29-Oct-1996.) $)
    pm5.32d $p |- ( ph -> ( ( ps /\ ch ) <-> ( ps /\ th ) ) ) $=
      ( wb wi wa pm5.32 sylib ) ABCDFGBCHBDHFEBCDIJ $.

    $( Distribution of implication over biconditional (deduction rule).
       (Contributed by NM, 25-Dec-2004.) $)
    pm5.32rd $p |- ( ph -> ( ( ch /\ ps ) <-> ( th /\ ps ) ) ) $=
      ( wa pm5.32d ancom 3bitr4g ) ABCFBDFCBFDBFABCDEGCBHDBHI $.
  $}

  ${
    pm5.32da.1 $e |- ( ( ph /\ ps ) -> ( ch <-> th ) ) $.
    $( Distribution of implication over biconditional (deduction rule).
       (Contributed by NM, 9-Dec-2006.) $)
    pm5.32da $p |- ( ph -> ( ( ps /\ ch ) <-> ( ps /\ th ) ) ) $=
      ( wb ex pm5.32d ) ABCDABCDFEGH $.
  $}

  ${
    biadan2.1 $e |- ( ph -> ps ) $.
    biadan2.2 $e |- ( ps -> ( ph <-> ch ) ) $.
    $( Add a conjunction to an equivalence.  (Contributed by Jeff Madsen,
       20-Jun-2011.) $)
    biadan2 $p |- ( ph <-> ( ps /\ ch ) ) $=
      ( wa pm4.71ri pm5.32i bitri ) ABAFBCFABDGBACEHI $.
  $}

  $( Theorem *4.24 of [WhiteheadRussell] p. 117.  (Contributed by NM,
     3-Jan-2005.) $)
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
    mtand.1 $e |- ( ph -> -. ch ) $.
    mtand.2 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( A modus tollens deduction.  (Contributed by Jeff Hankins,
       19-Aug-2009.) $)
    mtand $p |- ( ph -> -. ps ) $=
      ( ex mtod ) ABCDABCEFG $.
  $}

  ${
    mtord.1 $e |- ( ph -> -. ch ) $.
    mtord.2 $e |- ( ph -> -. th ) $.
    mtord.3 $e |- ( ph -> ( ps -> ( ch \/ th ) ) ) $.
    $( A modus tollens deduction involving disjunction.  (Contributed by Jeff
       Hankins, 15-Jul-2009.) $)
    mtord $p |- ( ph -> -. ps ) $=
      ( wn wo wi df-or syl6ib mpid mtod ) ABDFABCHZDEABCDIODJGCDKLMN $.
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
    $( Syllogism inference with commutation of antecedents.  (Contributed by
       NM, 2-Jul-2008.) $)
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
       15-Jun-2010.) $)
    mp4an $p |- ta $=
      ( wa pm3.2i mp2an ) ABKCDKEABFGLCDHILJM $.
  $}

  ${
    mpan2d.1 $e |- ( ph -> ch ) $.
    mpan2d.2 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
    $( A deduction based on modus ponens.  (Contributed by NM, 12-Dec-2004.) $)
    mpan2d $p |- ( ph -> ( ps -> th ) ) $=
      ( exp3a mpid ) ABCDEABCDFGH $.
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
    pm5.74da.1 $e |- ( ( ph /\ ps ) -> ( ch <-> th ) ) $.
    $( Distribution of implication over biconditional (deduction rule).
       (Contributed by NM, 4-May-2007.) $)
    pm5.74da $p |- ( ph -> ( ( ps -> ch ) <-> ( ps -> th ) ) ) $=
      ( wb ex pm5.74d ) ABCDABCDFEGH $.
  $}

  $( Theorem *4.45 of [WhiteheadRussell] p. 119.  (Contributed by NM,
     3-Jan-2005.) $)
  pm4.45 $p |- ( ph <-> ( ph /\ ( ph \/ ps ) ) ) $=
    ( wo orc pm4.71i ) AABCABDE $.

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
    $( Distribution of implication with conjunction (deduction rule).
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
    bid.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Deduction adding a left disjunct to both sides of a logical
       equivalence.  (Contributed by NM, 5-Aug-1993.) $)
    orbi2d $p |- ( ph -> ( ( th \/ ps ) <-> ( th \/ ch ) ) ) $=
      ( wn wi wo imbi2d df-or 3bitr4g ) ADFZBGLCGDBHDCHABCLEIDBJDCJK $.

    $( Deduction adding a right disjunct to both sides of a logical
       equivalence.  (Contributed by NM, 5-Aug-1993.) $)
    orbi1d $p |- ( ph -> ( ( ps \/ th ) <-> ( ch \/ th ) ) ) $=
      ( wo orbi2d orcom 3bitr4g ) ADBFDCFBDFCDFABCDEGBDHCDHI $.

    $( Deduction adding a left conjunct to both sides of a logical
       equivalence.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf
       Lammen, 16-Nov-2013.) $)
    anbi2d $p |- ( ph -> ( ( th /\ ps ) <-> ( th /\ ch ) ) ) $=
      ( wb a1d pm5.32d ) ADBCABCFDEGH $.

    $( Deduction adding a right conjunct to both sides of a logical
       equivalence.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf
       Lammen, 16-Nov-2013.) $)
    anbi1d $p |- ( ph -> ( ( ps /\ th ) <-> ( ch /\ th ) ) ) $=
      ( wb a1d pm5.32rd ) ADBCABCFDEGH $.
  $}

  $( Theorem *4.37 of [WhiteheadRussell] p. 118.  (Contributed by NM,
     3-Jan-2005.) $)
  orbi1 $p |- ( ( ph <-> ps ) -> ( ( ph \/ ch ) <-> ( ps \/ ch ) ) ) $=
    ( wb id orbi1d ) ABDZABCGEF $.

  $( Introduce a right conjunct to both sides of a logical equivalence.
     Theorem *4.36 of [WhiteheadRussell] p. 118.  (Contributed by NM,
     3-Jan-2005.) $)
  anbi1 $p |- ( ( ph <-> ps ) -> ( ( ph /\ ch ) <-> ( ps /\ ch ) ) ) $=
    ( wb id anbi1d ) ABDZABCGEF $.

  $( Introduce a left conjunct to both sides of a logical equivalence.
     (Contributed by NM, 16-Nov-2013.) $)
  anbi2 $p |- ( ( ph <-> ps ) -> ( ( ch /\ ph ) <-> ( ch /\ ps ) ) ) $=
    ( wb id anbi2d ) ABDZABCGEF $.

  $( Theorem *4.22 of [WhiteheadRussell] p. 117.  (Contributed by NM,
     3-Jan-2005.) $)
  bitr $p |- ( ( ( ph <-> ps ) /\ ( ps <-> ch ) ) -> ( ph <-> ch ) ) $=
    ( wb bibi1 biimpar ) ABDACDBCDABCEF $.

  ${
    bi12d.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    bi12d.2 $e |- ( ph -> ( th <-> ta ) ) $.
    $( Deduction joining two equivalences to form equivalence of disjunctions.
       (Contributed by NM, 5-Aug-1993.) $)
    orbi12d $p |- ( ph -> ( ( ps \/ th ) <-> ( ch \/ ta ) ) ) $=
      ( wo orbi1d orbi2d bitrd ) ABDHCDHCEHABCDFIADECGJK $.

    $( Deduction joining two equivalences to form equivalence of conjunctions.
       (Contributed by NM, 5-Aug-1993.) $)
    anbi12d $p |- ( ph -> ( ( ps /\ th ) <-> ( ch /\ ta ) ) ) $=
      ( wa anbi1d anbi2d bitrd ) ABDHCDHCEHABCDFIADECGJK $.
  $}

  $( Theorem *5.3 of [WhiteheadRussell] p. 125.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Andrew Salmon, 7-May-2011.) $)
  pm5.3 $p |- ( ( ( ph /\ ps ) -> ch ) <->
               ( ( ph /\ ps ) -> ( ph /\ ch ) ) ) $=
    ( wa wi impexp imdistan bitri ) ABDZCEABCEEIACDEABCFABCGH $.

  $( Theorem *5.61 of [WhiteheadRussell] p. 125.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 30-Jun-2013.) $)
  pm5.61 $p |- ( ( ( ph \/ ps ) /\ -. ps ) <-> ( ph /\ -. ps ) ) $=
    ( wn wo biorf orcom syl6rbb pm5.32ri ) BCZABDZAIABADJBAEBAFGH $.

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

  $( Simplification of a conjunction.  (Contributed by NM, 18-Mar-2007.) $)
  simpll $p |- ( ( ( ph /\ ps ) /\ ch ) -> ph ) $=
    ( id ad2antrr ) AABCADE $.

  $( Simplification of a conjunction.  (Contributed by NM, 20-Mar-2007.) $)
  simplr $p |- ( ( ( ph /\ ps ) /\ ch ) -> ps ) $=
    ( id ad2antlr ) BBACBDE $.

  $( Simplification of a conjunction.  (Contributed by NM, 21-Mar-2007.) $)
  simprl $p |- ( ( ph /\ ( ps /\ ch ) ) -> ps ) $=
    ( id ad2antrl ) BBACBDE $.

  $( Simplification of a conjunction.  (Contributed by NM, 21-Mar-2007.) $)
  simprr $p |- ( ( ph /\ ( ps /\ ch ) ) -> ch ) $=
    ( id ad2antll ) CCABCDE $.

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

  $( Disjunction of antecedents.  Compare Theorem *4.77 of [WhiteheadRussell]
     p. 121.  (Contributed by NM, 30-May-1994.)  (Proof shortened by Wolf
     Lammen, 9-Dec-2012.) $)
  jaob $p |- ( ( ( ph \/ ch ) -> ps ) <-> ( ( ph -> ps ) /\ ( ch -> ps ) ) ) $=
    ( wo wi wa pm2.67-2 olc imim1i jca pm3.44 impbii ) ACDZBEZABEZCBEZFNOPABCGC
    MBCAHIJBACKL $.

  ${
    jaoian.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    jaoian.2 $e |- ( ( th /\ ps ) -> ch ) $.
    $( Inference disjoining the antecedents of two implications.  (Contributed
       by NM, 23-Oct-2005.) $)
    jaoian $p |- ( ( ( ph \/ th ) /\ ps ) -> ch ) $=
      ( wo wi ex jaoi imp ) ADGBCABCHDABCEIDBCFIJK $.
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
       deduction rule ` \/ ` E ( ` \/ ` elimination), see ~ natded .
       (Contributed by Mario Carneiro, 29-May-2016.) $)
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

  ${
    pm2.61ian.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    pm2.61ian.2 $e |- ( ( -. ph /\ ps ) -> ch ) $.
    $( Elimination of an antecedent.  (Contributed by NM, 1-Jan-2005.) $)
    pm2.61ian $p |- ( ps -> ch ) $=
      ( wi ex wn pm2.61i ) ABCFABCDGAHBCEGI $.
  $}

  ${
    pm2.61dan.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    pm2.61dan.2 $e |- ( ( ph /\ -. ps ) -> ch ) $.
    $( Elimination of an antecedent.  (Contributed by NM, 1-Jan-2005.) $)
    pm2.61dan $p |- ( ph -> ch ) $=
      ( ex wn pm2.61d ) ABCABCDFABGCEFH $.
  $}

  ${
    pm2.61ddan.1 $e |- ( ( ph /\ ps ) -> th ) $.
    pm2.61ddan.2 $e |- ( ( ph /\ ch ) -> th ) $.
    pm2.61ddan.3 $e |- ( ( ph /\ ( -. ps /\ -. ch ) ) -> th ) $.
    $( Elimination of two antecedents.  (Contributed by NM, 9-Jul-2013.) $)
    pm2.61ddan $p |- ( ph -> th ) $=
      ( wn wa adantlr anassrs pm2.61dan ) ABDEABHZICDACDMFJAMCHDGKLL $.
  $}

  ${
    pm2.61dda.1 $e |- ( ( ph /\ -. ps ) -> th ) $.
    pm2.61dda.2 $e |- ( ( ph /\ -. ch ) -> th ) $.
    pm2.61dda.3 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
    $( Elimination of two antecedents.  (Contributed by NM, 9-Jul-2013.) $)
    pm2.61dda $p |- ( ph -> th ) $=
      ( wa anassrs wn adantlr pm2.61dan ) ABDABHCDABCDGIACJDBFKLEL $.
  $}

  ${
    condan.1 $e |- ( ( ph /\ -. ps ) -> ch ) $.
    condan.2 $e |- ( ( ph /\ -. ps ) -> -. ch ) $.
    $( Proof by contradiction.  (Contributed by NM, 9-Feb-2006.)  (Proof
       shortened by Wolf Lammen, 19-Jun-2014.) $)
    condan $p |- ( ph -> ps ) $=
      ( wn pm2.65da notnotrd ) ABABFCDEGH $.
  $}

  $( Introduce one conjunct as an antecedent to the other.  "abai" stands for
     "and, biconditional, and, implication".  (Contributed by NM,
     12-Aug-1993.)  (Proof shortened by Wolf Lammen, 7-Dec-2012.) $)
  abai $p |- ( ( ph /\ ps ) <-> ( ph /\ ( ph -> ps ) ) ) $=
    ( wi biimt pm5.32i ) ABABCABDE $.

  $( Theorem *5.53 of [WhiteheadRussell] p. 125.  (Contributed by NM,
     3-Jan-2005.) $)
  pm5.53 $p |- ( ( ( ( ph \/ ps ) \/ ch ) -> th ) <->
                ( ( ( ph -> th ) /\ ( ps -> th ) ) /\ ( ch -> th ) ) ) $=
    ( wo wi wa jaob anbi1i bitri ) ABEZCEDFKDFZCDFZGADFBDFGZMGKDCHLNMADBHIJ $.

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
       24-Mar-1996.) $)
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
       10-May-2004.) $)
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
    impbida.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    impbida.2 $e |- ( ( ph /\ ch ) -> ps ) $.
    $( Deduce an equivalence from two implications.  (Contributed by NM,
       17-Feb-2007.) $)
    impbida $p |- ( ph -> ( ps <-> ch ) ) $=
      ( ex impbid ) ABCABCDFACBEFG $.
  $}

  $( Theorem *3.48 of [WhiteheadRussell] p. 114.  (Contributed by NM,
     28-Jan-1997.) $)
  pm3.48 $p |- ( ( ( ph -> ps ) /\ ( ch -> th ) )
      -> ( ( ph \/ ch ) -> ( ps \/ th ) ) ) $=
    ( wi wo orc imim2i olc jaao ) ABEABDFZCDECBKABDGHDKCDBIHJ $.

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
  pm2.73 $p |- ( ( ph -> ps )
       -> ( ( ( ph \/ ps ) \/ ch ) -> ( ps \/ ch ) ) ) $=
    ( wi wo pm2.621 orim1d ) ABDABEBCABFG $.

  $( Theorem *2.74 of [WhiteheadRussell] p. 108.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Andrew Salmon, 7-May-2011.) $)
  pm2.74 $p |- ( ( ps -> ph )
      -> ( ( ( ph \/ ps ) \/ ch ) -> ( ph \/ ch ) ) ) $=
    ( wi wo orel2 ax-1 ja orim1d ) BADABEZACBAJADBAFAJGHI $.

  $( Disjunction distributes over implication.  (Contributed by Wolf Lammen,
     5-Jan-2013.) $)
  orimdi $p |- ( ( ph \/ ( ps -> ch ) )
        <-> ( ( ph \/ ps ) -> ( ph \/ ch ) ) ) $=
    ( wn wi wo imdi df-or imbi12i 3bitr4i ) ADZBCEZEKBEZKCEZEALFABFZACFZEKBCGAL
    HOMPNABHACHIJ $.

  $( Theorem *2.76 of [WhiteheadRussell] p. 108.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.76 $p |- ( ( ph \/ ( ps -> ch ) )
      -> ( ( ph \/ ps ) -> ( ph \/ ch ) ) ) $=
    ( wi wo orimdi biimpi ) ABCDEABEACEDABCFG $.

  $( Theorem *2.75 of [WhiteheadRussell] p. 108.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 4-Jan-2013.) $)
  pm2.75 $p |- ( ( ph \/ ps )
       -> ( ( ph \/ ( ps -> ch ) ) -> ( ph \/ ch ) ) ) $=
    ( wi wo pm2.76 com12 ) ABCDEABEACEABCFG $.

  $( Theorem *2.8 of [WhiteheadRussell] p. 108.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 5-Jan-2013.) $)
  pm2.8 $p |- ( ( ph \/ ps ) -> ( ( -. ps \/ ch ) -> ( ph \/ ch ) ) ) $=
    ( wo wn pm2.53 con1d orim1d ) ABDZBEACIABABFGH $.

  $( Theorem *2.81 of [WhiteheadRussell] p. 108.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.81 $p |- ( ( ps -> ( ch -> th ) )
      -> ( ( ph \/ ps ) -> ( ( ph \/ ch ) -> ( ph \/ th ) ) ) ) $=
    ( wi wo orim2 pm2.76 syl6 ) BCDEZEABFAJFACFADFEABJGACDHI $.

  $( Theorem *2.82 of [WhiteheadRussell] p. 108.  (Contributed by NM,
     3-Jan-2005.) $)
  pm2.82 $p |- ( ( ( ph \/ ps ) \/ ch ) -> ( ( ( ph \/ -. ch ) \/ th )
      -> ( ( ph \/ ps ) \/ th ) ) ) $=
    ( wo wn wi ax-1 pm2.24 orim2d jaoi orim1d ) ABEZCEACFZEZMDMOMGCMOHCNBACBIJK
    L $.

  $( Theorem *2.85 of [WhiteheadRussell] p. 108.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 5-Jan-2013.) $)
  pm2.85 $p |- ( ( ( ph \/ ps ) -> ( ph \/ ch ) )
      -> ( ph \/ ( ps -> ch ) ) ) $=
    ( wi wo orimdi biimpri ) ABCDEABEACEDABCFG $.

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
    ( wn wo biortn orcom syl6rbb pm5.32ri ) BABCZDZABAIADJBAEIAFGH $.

  $( Two propositions are equivalent if they are both true.  Theorem *5.1 of
     [WhiteheadRussell] p. 123.  (Contributed by NM, 21-May-1994.) $)
  pm5.1 $p |- ( ( ph /\ ps ) -> ( ph <-> ps ) ) $=
    ( wb pm5.501 biimpa ) ABABCABDE $.

  $( Two propositions are equivalent if they are both false.  Theorem *5.21 of
     [WhiteheadRussell] p. 124.  (Contributed by NM, 21-May-1994.) $)
  pm5.21 $p |- ( ( -. ph /\ -. ps ) -> ( ph <-> ps ) ) $=
    ( wn wb pm5.21im imp ) ACBCABDABEF $.

  $( Theorem *3.43 (Comp) of [WhiteheadRussell] p. 113.  (Contributed by NM,
     3-Jan-2005.) $)
  pm3.43 $p |- ( ( ( ph -> ps ) /\ ( ph -> ch ) )
      -> ( ph -> ( ps /\ ch ) ) ) $=
    ( wi wa pm3.43i imp ) ABDACDABCEDABCFG $.

  $( Distributive law for implication over conjunction.  Compare Theorem *4.76
     of [WhiteheadRussell] p. 121.  (Contributed by NM, 3-Apr-1994.)  (Proof
     shortened by Wolf Lammen, 27-Nov-2013.) $)
  jcab $p |- ( ( ph -> ( ps /\ ch ) )
      <-> ( ( ph -> ps ) /\ ( ph -> ch ) ) ) $=
    ( wa wi simpl imim2i simpr jca pm3.43 impbii ) ABCDZEZABEZACEZDMNOLBABCFGLC
    ABCHGIABCJK $.

  $( Distributive law for disjunction.  Theorem *4.41 of [WhiteheadRussell]
     p. 119.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Andrew
     Salmon, 7-May-2011.)  (Proof shortened by Wolf Lammen, 28-Nov-2013.) $)
  ordi $p |- ( ( ph \/ ( ps /\ ch ) ) <-> ( ( ph \/ ps ) /\ ( ph \/ ch ) ) ) $=
    ( wn wa wi wo jcab df-or anbi12i 3bitr4i ) ADZBCEZFLBFZLCFZEAMGABGZACGZELBC
    HAMIPNQOABIACIJK $.

  $( Distributive law for disjunction.  (Contributed by NM, 12-Aug-1994.) $)
  ordir $p |- ( ( ( ph /\ ps ) \/ ch ) <->
              ( ( ph \/ ch ) /\ ( ps \/ ch ) ) ) $=
    ( wa wo ordi orcom anbi12i 3bitr4i ) CABDZECAEZCBEZDJCEACEZBCEZDCABFJCGMKNL
    ACGBCGHI $.

  $( Theorem *4.76 of [WhiteheadRussell] p. 121.  (Contributed by NM,
     3-Jan-2005.) $)
  pm4.76 $p |- ( ( ( ph -> ps ) /\ ( ph -> ch ) ) <->
                ( ph -> ( ps /\ ch ) ) ) $=
    ( wa wi jcab bicomi ) ABCDEABEACEDABCFG $.

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

  $( Implication in terms of biconditional and disjunction.  Theorem *4.72 of
     [WhiteheadRussell] p. 121.  (Contributed by NM, 30-Aug-1993.)  (Proof
     shortened by Wolf Lammen, 30-Jan-2013.) $)
  pm4.72 $p |- ( ( ph -> ps ) <-> ( ps <-> ( ph \/ ps ) ) ) $=
    ( wi wo wb olc pm2.621 impbid2 orc bi2 syl5 impbii ) ABCZBABDZEZMBNBAFABGHA
    NOBABIBNJKL $.

  $( Simplify an implication between implications.  (Contributed by Paul
     Chapman, 17-Nov-2012.)  (Proof shortened by Wolf Lammen, 3-Apr-2013.) $)
  imimorb $p |- ( ( ( ps -> ch ) -> ( ph -> ch ) ) <->
                  ( ph -> ( ps \/ ch ) ) ) $=
    ( wi wo bi2.04 dfor2 imbi2i bitr4i ) BCDZACDDAJCDZDABCEZDJACFLKABCGHI $.

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

  $( Absorption of disjunction into equivalence.  (Contributed by NM,
     6-Aug-1995.)  (Proof shortened by Wolf Lammen, 3-Nov-2013.) $)
  oibabs $p |- ( ( ( ph \/ ps ) -> ( ph <-> ps ) ) <-> ( ph <-> ps ) ) $=
    ( wo wb wi wn wa ioran pm5.21 sylbi id ja ax-1 impbii ) ABCZABDZEPOPPOFAFBF
    GPABHABIJPKLPOMN $.

  $( Law of noncontradiction.  Theorem *3.24 of [WhiteheadRussell] p. 111 (who
     call it the "law of contradiction").  (Contributed by NM, 16-Sep-1993.)
     (Proof shortened by Wolf Lammen, 24-Nov-2012.) $)
  pm3.24 $p |- -. ( ph /\ -. ph ) $=
    ( wi wn wa id iman mpbi ) AABAACDCAEAAFG $.

  $( Theorem *2.26 of [WhiteheadRussell] p. 104.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 23-Nov-2012.) $)
  pm2.26 $p |- ( -. ph \/ ( ( ph -> ps ) -> ps ) ) $=
    ( wi pm2.27 imori ) AABCBCABDE $.

  $( Theorem *5.11 of [WhiteheadRussell] p. 123.  (Contributed by NM,
     3-Jan-2005.) $)
  pm5.11 $p |- ( ( ph -> ps ) \/ ( -. ph -> ps ) ) $=
    ( wi wn pm2.5 orri ) ABCADBCABEF $.

  $( Theorem *5.12 of [WhiteheadRussell] p. 123.  (Contributed by NM,
     3-Jan-2005.) $)
  pm5.12 $p |- ( ( ph -> ps ) \/ ( ph -> -. ps ) ) $=
    ( wi wn pm2.51 orri ) ABCABDCABEF $.

  $( Theorem *5.14 of [WhiteheadRussell] p. 123.  (Contributed by NM,
     3-Jan-2005.) $)
  pm5.14 $p |- ( ( ph -> ps ) \/ ( ps -> ch ) ) $=
    ( wi wn ax-1 con3i pm2.21d orri ) ABDZBCDJEBCBJBAFGHI $.

  $( Theorem *5.13 of [WhiteheadRussell] p. 123.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 14-Nov-2012.) $)
  pm5.13 $p |- ( ( ph -> ps ) \/ ( ps -> ph ) ) $=
    ( pm5.14 ) ABAC $.

  $( Theorem *5.17 of [WhiteheadRussell] p. 124.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 3-Jan-2013.) $)
  pm5.17 $p |- ( ( ( ph \/ ps ) /\ -. ( ph /\ ps ) ) <-> ( ph <-> -. ps ) ) $=
    ( wn wb wi wa wo bicom dfbi2 orcom df-or bitr2i imnan anbi12i 3bitrri ) ABC
    ZDPADPAEZAPEZFABGZABFCZFAPHPAIQSRTSBAGQABJBAKLABMNO $.

  $( Theorem *5.15 of [WhiteheadRussell] p. 124.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 15-Oct-2013.) $)
  pm5.15 $p |- ( ( ph <-> ps ) \/ ( ph <-> -. ps ) ) $=
    ( wb wn xor3 biimpi orri ) ABCZABDCZHDIABEFG $.

  $( Theorem *5.16 of [WhiteheadRussell] p. 124.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 17-Oct-2013.) $)
  pm5.16 $p |- -. ( ( ph <-> ps ) /\ ( ph <-> -. ps ) ) $=
    ( wb wn wi wa pm5.18 biimpi imnan mpbi ) ABCZABDCZDZEKLFDKMABGHKLIJ $.

  $( Two ways to express "exclusive or."  Theorem *5.22 of [WhiteheadRussell]
     p. 124.  (Contributed by NM, 3-Jan-2005.)  (Proof shortened by Wolf
     Lammen, 22-Jan-2013.) $)
  xor $p |- ( -. ( ph <-> ps ) <->
                ( ( ph /\ -. ps ) \/ ( ps /\ -. ph ) ) ) $=
    ( wn wa wo wb wi iman anbi12i dfbi2 ioran 3bitr4ri con1bii ) ABCDZBACDZEZAB
    FZABGZBAGZDNCZOCZDQPCRTSUAABHBAHIABJNOKLM $.

  $( Two ways to express "exclusive or."  (Contributed by NM, 3-Jan-2005.)
     (Proof shortened by Wolf Lammen, 24-Jan-2013.) $)
  nbi2 $p |- ( -. ( ph <-> ps ) <-> ( ( ph \/ ps ) /\ -. ( ph /\ ps ) ) ) $=
    ( wb wn wo wa xor3 pm5.17 bitr4i ) ABCDABDCABEABFDFABGABHI $.

  $( An alternate definition of the biconditional.  Theorem *5.23 of
     [WhiteheadRussell] p. 124.  (Contributed by NM, 27-Jun-2002.)  (Proof
     shortened by Wolf Lammen, 3-Nov-2013.) $)
  dfbi3 $p |- ( ( ph <-> ps ) <-> ( ( ph /\ ps ) \/ ( -. ph /\ -. ps ) ) ) $=
    ( wn wb wa wo xor pm5.18 notnot anbi2i ancom orbi12i 3bitr4i ) ABCZDCANCZEZ
    NACZEZFABDABEZQNEZFANGABHSPTRBOABIJQNKLM $.

  $( Theorem *5.24 of [WhiteheadRussell] p. 124.  (Contributed by NM,
     3-Jan-2005.) $)
  pm5.24 $p |- ( -. ( ( ph /\ ps ) \/ ( -. ph /\ -. ps ) ) <->
                ( ( ph /\ -. ps ) \/ ( ps /\ -. ph ) ) ) $=
    ( wb wn wa wo xor dfbi3 xchnxbi ) ABCABDZEBADZEFABEKJEFABGABHI $.

  $( Conjunction distributes over exclusive-or, using ` -. ( ph <-> ps ) ` to
     express exclusive-or.  This is one way to interpret the distributive law
     of multiplication over addition in modulo 2 arithmetic.  (Contributed by
     NM, 3-Oct-2008.) $)
  xordi $p |- ( ( ph /\ -. ( ps <-> ch ) ) <->
                -. ( ( ph /\ ps ) <-> ( ph /\ ch ) ) ) $=
    ( wb wn wa wi annim pm5.32 xchbinx ) ABCDZEFAKGABFACFDAKHABCIJ $.

  $( A wff disjoined with truth is true.  (Contributed by NM, 23-May-1999.) $)
  biort $p |- ( ph -> ( ph <-> ( ph \/ ps ) ) ) $=
    ( wo orc ax-1 impbid2 ) AAABCZABDAGEF $.

  $( Theorem *5.55 of [WhiteheadRussell] p. 125.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 20-Jan-2013.) $)
  pm5.55 $p |- ( ( ( ph \/ ps ) <-> ph ) \/ ( ( ph \/ ps ) <-> ps ) ) $=
    ( wo wb biort bicomd wn biorf nsyl4 con1i orri ) ABCZADZLBDZNMAMNAALABEFAGB
    LABHFIJK $.

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

  $( Theorem *5.54 of [WhiteheadRussell] p. 125.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 7-Nov-2013.) $)
  pm5.54 $p |- ( ( ( ph /\ ps ) <-> ph ) \/ ( ( ph /\ ps ) <-> ps ) ) $=
    ( wa wb iba bicomd adantl pm5.21ni orri ) ABCZADZJBDJKBBKABAJBAEFZGLHI $.

  ${
    baib.1 $e |- ( ph <-> ( ps /\ ch ) ) $.
    $( Move conjunction outside of biconditional.  (Contributed by NM,
       13-May-1999.) $)
    baib $p |- ( ps -> ( ph <-> ch ) ) $=
      ( wa ibar syl6rbbr ) BCBCEABCFDG $.

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

  $( Conjunction in antecedent versus disjunction in consequent.  Theorem *5.6
     of [WhiteheadRussell] p. 125.  (Contributed by NM, 8-Jun-1994.) $)
  pm5.6 $p |- ( ( ( ph /\ -. ps ) -> ch ) <-> ( ph -> ( ps \/ ch ) ) ) $=
    ( wn wa wi wo impexp df-or imbi2i bitr4i ) ABDZECFALCFZFABCGZFALCHNMABCIJK
    $.

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
    mpbiran.1 $e |- ps $.
    mpbiran.2 $e |- ( ph <-> ( ps /\ ch ) ) $.
    $( Detach truth from conjunction in biconditional.  (Contributed by NM,
       27-Feb-1996.) $)
    mpbiran $p |- ( ph <-> ch ) $=
      ( wa biantrur bitr4i ) ABCFCEBCDGH $.
  $}

  ${
    mpbiran2.1 $e |- ch $.
    mpbiran2.2 $e |- ( ph <-> ( ps /\ ch ) ) $.
    $( Detach truth from conjunction in biconditional.  (Contributed by NM,
       22-Feb-1996.) $)
    mpbiran2 $p |- ( ph <-> ps ) $=
      ( wa biantru bitr4i ) ABCFBECBDGH $.
  $}

  ${
    mpbir2an.1 $e |- ps $.
    mpbir2an.2 $e |- ch $.
    mpbiran2an.1 $e |- ( ph <-> ( ps /\ ch ) ) $.
    $( Detach a conjunction of truths in a biconditional.  (Contributed by NM,
       10-May-2005.) $)
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

  $( Theorem *5.62 of [WhiteheadRussell] p. 125.  (Contributed by Roy F.
     Longton, 21-Jun-2005.) $)
  pm5.62 $p |- ( ( ( ph /\ ps ) \/ -. ps ) <-> ( ph \/ -. ps ) ) $=
    ( wa wn wo exmid ordir mpbiran2 ) ABCBDZEAIEBIEBFABIGH $.

  $( Theorem *5.63 of [WhiteheadRussell] p. 125.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 25-Dec-2012.) $)
  pm5.63 $p |- ( ( ph \/ ps ) <-> ( ph \/ ( -. ph /\ ps ) ) ) $=
    ( wn wa wo exmid ordi mpbiran bicomi ) AACZBDEZABEZKAJELAFAJBGHI $.

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

  $( Theorem *4.83 of [WhiteheadRussell] p. 122.  (Contributed by NM,
     3-Jan-2005.) $)
  pm4.83 $p |- ( ( ( ph -> ps ) /\ ( -. ph -> ps ) ) <-> ps ) $=
    ( wn wo wi wa exmid a1bi jaob bitr2i ) BAACZDZBEABEKBEFLBAGHABKIJ $.

  $( Negation inferred from embedded conjunct.  (Contributed by NM,
     20-Aug-1993.)  (Proof shortened by Wolf Lammen, 25-Nov-2012.) $)
  pclem6 $p |- ( ( ph <-> ( ps /\ -. ph ) ) -> -. ps ) $=
    ( wn wa wb ibar nbbn sylib con2i ) BABACZDZEZBJKELCBJFAKGHI $.

  $( A transitive law of equivalence.  Compare Theorem *4.22 of
     [WhiteheadRussell] p. 117.  (Contributed by NM, 18-Aug-1993.) $)
  biantr $p |- ( ( ( ph <-> ps ) /\ ( ch <-> ps ) ) -> ( ph <-> ch ) ) $=
    ( wb id bibi2d biimparc ) CBDZACDABDHCBAHEFG $.

  $( Disjunction distributes over the biconditional.  An axiom of system DS in
     Vladimir Lifschitz, "On calculational proofs" (1998),
     ~ http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.25.3384 .
     (Contributed by NM, 8-Jan-2005.)  (Proof shortened by Wolf Lammen,
     4-Feb-2013.) $)
  orbidi $p |- ( ( ph \/ ( ps <-> ch ) ) <->
                ( ( ph \/ ps ) <-> ( ph \/ ch ) ) ) $=
    ( wn wb wi wo pm5.74 df-or bibi12i 3bitr4i ) ADZBCEZFLBFZLCFZEAMGABGZACGZEL
    BCHAMIPNQOABIACIJK $.

  $( Lukasiewicz's shortest axiom for equivalential calculus.  Storrs McCall,
     ed., _Polish Logic 1920-1939_ (Oxford, 1967), p. 96.  (Contributed by NM,
     10-Jan-2005.) $)
  biluk $p |- ( ( ph <-> ps ) <-> ( ( ch <-> ps ) <-> ( ph <-> ch ) ) ) $=
    ( wb bicom bibi1i biass bitri mpbi bitr4i ) ABDZCBACDZDZDZCBDLDKCDZMDKNDOBA
    DZCDMKPCABEFBACGHKCMGICBLGJ $.

  $( Disjunction distributes over the biconditional.  Theorem *5.7 of
     [WhiteheadRussell] p. 125.  This theorem is similar to ~ orbidi .
     (Contributed by Roy F. Longton, 21-Jun-2005.) $)
  pm5.7 $p |- ( ( ( ph \/ ch ) <-> ( ps \/ ch ) ) <->
               ( ch \/ ( ph <-> ps ) ) ) $=
    ( wb wo orbidi orcom bibi12i bitr2i ) CABDECAEZCBEZDACEZBCEZDCABFJLKMCAGCBG
    HI $.

  $( Dijkstra-Scholten's Golden Rule for calculational proofs.  (Contributed by
     NM, 10-Jan-2005.) $)
  bigolden $p |- ( ( ( ph /\ ps ) <-> ph ) <-> ( ps <-> ( ph \/ ps ) ) ) $=
    ( wi wa wb wo pm4.71 pm4.72 bicom 3bitr3ri ) ABCAABDZEBABFEKAEABGABHAKIJ $.

  $( Theorem *5.71 of [WhiteheadRussell] p. 125.  (Contributed by Roy F.
     Longton, 23-Jun-2005.) $)
  pm5.71 $p |- ( ( ps -> -. ch ) -> ( ( ( ph \/ ps ) /\ ch ) <->
                ( ph /\ ch ) ) ) $=
    ( wn wo wa wb orel2 orc impbid1 anbi1d pm2.21 pm5.32rd ja ) BCDZABEZCFACFGB
    DZPACQPABAHABIJKOCPACPAGLMN $.

  $( Theorem *5.75 of [WhiteheadRussell] p. 126.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Andrew Salmon, 7-May-2011.)  (Proof
     shortened by Wolf Lammen, 23-Dec-2012.) $)
  pm5.75 $p |- ( ( ( ch -> -. ps ) /\ ( ph <-> ( ps \/ ch ) ) ) ->
                ( ( ph /\ -. ps ) <-> ch ) ) $=
    ( wo wb wn wa wi anbi1 anbi1i pm5.61 syl6bb pm4.71 biimpi bicomd sylan9bbr
    orcom bitri ) ABCDZEZABFZGZCUAGZCUAHZCTUBSUAGZUCASUAIUECBDZUAGUCSUFUABCQJCB
    KRLUDCUCUDCUCECUAMNOP $.

  $( Removal of conjunct from one side of an equivalence.  (Contributed by NM,
     5-Aug-1993.) $)
  bimsc1 $p |- ( ( ( ph -> ps ) /\ ( ch <-> ( ps /\ ph ) ) )
               -> ( ch <-> ph ) ) $=
    ( wi wa wb simpr ancr impbid2 bibi2d biimpa ) ABDZCBAEZFCAFLMACLMABAGABHIJK
    $.

  $( The disjunction of the four possible combinations of two wffs and their
     negations is always true.  (Contributed by David Abernethy,
     28-Jan-2014.) $)
  4exmid $p |- ( ( ( ph /\ ps ) \/ ( -. ph /\ -. ps ) )
              \/ ( ( ph /\ -. ps ) \/ ( ps /\ -. ph ) ) ) $=
    ( wb wn wo wa exmid dfbi3 xor orbi12i mpbi ) ABCZLDZEABFADZBDZFEZAOFBNFEZEL
    GLPMQABHABIJK $.

  ${
    ecase2d.1 $e |- ( ph -> ps ) $.
    ecase2d.2 $e |- ( ph -> -. ( ps /\ ch ) ) $.
    ecase2d.3 $e |- ( ph -> -. ( ps /\ th ) ) $.
    ecase2d.4 $e |- ( ph -> ( ta \/ ( ch \/ th ) ) ) $.
    $( Deduction for elimination by cases.  (Contributed by NM, 21-Apr-1994.)
       (Proof shortened by Wolf Lammen, 22-Dec-2012.) $)
    ecase2d $p |- ( ph -> ta ) $=
      ( wo idd wa pm2.21d mpand jaod mpjaod ) AEECDJAEKACEDABCEFABCLEGMNABDEFAB
      DLEHMNOIP $.
  $}

  ${
    ecase3.1 $e |- ( ph -> ch ) $.
    ecase3.2 $e |- ( ps -> ch ) $.
    ecase3.3 $e |- ( -. ( ph \/ ps ) -> ch ) $.
    $( Inference for elimination by cases.  (Contributed by NM, 23-Mar-1995.)
       (Proof shortened by Wolf Lammen, 26-Nov-2012.) $)
    ecase3 $p |- ch $=
      ( wo jaoi pm2.61i ) ABGCACBDEHFI $.
  $}

  ${
    ecase.1 $e |- ( -. ph -> ch ) $.
    ecase.2 $e |- ( -. ps -> ch ) $.
    ecase.3 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( Inference for elimination by cases.  (Contributed by NM,
       13-Jul-2005.) $)
    ecase $p |- ch $=
      ( ex pm2.61nii ) ABCABCFGDEH $.
  $}

  ${
    ecase3d.1 $e |- ( ph -> ( ps -> th ) ) $.
    ecase3d.2 $e |- ( ph -> ( ch -> th ) ) $.
    ecase3d.3 $e |- ( ph -> ( -. ( ps \/ ch ) -> th ) ) $.
    $( Deduction for elimination by cases.  (Contributed by NM, 2-May-1996.)
       (Proof shortened by Andrew Salmon, 7-May-2011.) $)
    ecase3d $p |- ( ph -> th ) $=
      ( wo jaod pm2.61d ) ABCHDABDCEFIGJ $.
  $}

  ${
    ecased.1 $e |- ( ph -> ( -. ps -> th ) ) $.
    ecased.2 $e |- ( ph -> ( -. ch -> th ) ) $.
    ecased.3 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
    $( Deduction for elimination by cases.  (Contributed by NM, 8-Oct-2012.) $)
    ecased $p |- ( ph -> th ) $=
      ( wn wo wa pm3.11 syl5 ecase3d ) ABHZCHZDEFNOIHBCJADBCKGLM $.
  $}

  ${
    ecase3ad.1 $e |- ( ph -> ( ps -> th ) ) $.
    ecase3ad.2 $e |- ( ph -> ( ch -> th ) ) $.
    ecase3ad.3 $e |- ( ph -> ( ( -. ps /\ -. ch ) -> th ) ) $.
    $( Deduction for elimination by cases.  (Contributed by NM,
       24-May-2013.) $)
    ecase3ad $p |- ( ph -> th ) $=
      ( wn notnot2 syl5 ecased ) ABHZCHZDLHBADBIEJMHCADCIFJGK $.
  $}

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
    4cases.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    4cases.2 $e |- ( ( ph /\ -. ps ) -> ch ) $.
    4cases.3 $e |- ( ( -. ph /\ ps ) -> ch ) $.
    4cases.4 $e |- ( ( -. ph /\ -. ps ) -> ch ) $.
    $( Inference eliminating two antecedents from the four possible cases that
       result from their true/false combinations.  (Contributed by NM,
       25-Oct-2003.) $)
    4cases $p |- ch $=
      ( pm2.61ian wn pm2.61i ) BCABCDFHABICEGHJ $.
  $}

  ${
    4casesdan.1 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
    4casesdan.2 $e |- ( ( ph /\ ( ps /\ -. ch ) ) -> th ) $.
    4casesdan.3 $e |- ( ( ph /\ ( -. ps /\ ch ) ) -> th ) $.
    4casesdan.4 $e |- ( ( ph /\ ( -. ps /\ -. ch ) ) -> th ) $.
    $( Deduction eliminating two antecedents from the four possible cases that
       result from their true/false combinations.  (Contributed by NM,
       19-Mar-2013.) $)
    4casesdan $p |- ( ph -> th ) $=
      ( wi wa expcom wn 4cases ) BCADIABCJDEKABCLZJDFKABLZCJDGKAONJDHKM $.
  $}

  ${
    niabn.1 $e |- ph $.
    $( Miscellaneous inference relating falsehoods.  (Contributed by NM,
       31-Mar-1994.) $)
    niabn $p |- ( -. ps -> ( ( ch /\ ps ) <-> -. ph ) ) $=
      ( wa wn simpr pm2.24i pm5.21ni ) CBEBAFCBGABDHI $.
  $}

  $( Lemma for an alternate version of weak deduction theorem.  (Contributed by
     NM, 2-Apr-1994.)  (Proof shortened by Andrew Salmon, 7-May-2011.)  (Proof
     shortened by Wolf Lammen, 4-Dec-2012.) $)
  dedlem0a $p |- ( ph -> ( ps <-> ( ( ch -> ph ) -> ( ps /\ ph ) ) ) ) $=
    ( wa wi iba wb ax-1 biimt syl bitrd ) ABBADZCAEZLEZABFAMLNGACHMLIJK $.

  $( Lemma for an alternate version of weak deduction theorem.  (Contributed by
     NM, 2-Apr-1994.) $)
  dedlem0b $p |- ( -. ph -> ( ps <-> ( ( ps -> ph ) -> ( ch /\ ph ) ) ) ) $=
    ( wn wi wa pm2.21 imim2d com23 simpr imim12i con1d com12 impbid ) ADZBBAEZC
    AFZEZOPBQOAQBAQGHIROBRBABDPQABAGCAJKLMN $.

  $( Lemma for weak deduction theorem.  (Contributed by NM, 26-Jun-2002.)
     (Proof shortened by Andrew Salmon, 7-May-2011.) $)
  dedlema $p |- ( ph -> ( ps <-> ( ( ps /\ ph ) \/ ( ch /\ -. ph ) ) ) ) $=
    ( wa wn wo orc expcom wi simpl a1i pm2.24 adantld jaod impbid ) ABBADZCAEZD
    ZFZBASPRGHAPBRPBIABAJKAQBCABLMNO $.

  $( Lemma for weak deduction theorem.  (Contributed by NM, 15-May-1999.)
     (Proof shortened by Andrew Salmon, 7-May-2011.) $)
  dedlemb $p |- ( -. ph -> ( ch <-> ( ( ps /\ ph ) \/ ( ch /\ -. ph ) ) ) ) $=
    ( wn wa wo olc expcom pm2.21 adantld wi simpl a1i jaod impbid ) ADZCBAEZCPE
    ZFZCPSRQGHPQCRPACBACIJRCKPCPLMNO $.

  ${
    elimh.1 $e |- ( ( ph <-> ( ( ph /\ ch ) \/ ( ps /\ -. ch ) ) )
                     -> ( ch <-> ta ) ) $.
    elimh.2 $e |- ( ( ps <-> ( ( ph /\ ch ) \/ ( ps /\ -. ch ) ) )
                     -> ( th <-> ta ) ) $.
    elimh.3 $e |- th $.
    $( Hypothesis builder for weak deduction theorem.  For more information,
       see the Deduction Theorem link on the Metamath Proof Explorer home
       page.  (Contributed by NM, 26-Jun-2002.) $)
    elimh $p |- ta $=
      ( wa wn wo wb dedlema syl ibi dedlemb mpbii pm2.61i ) CECECAACIBCJZIKZLCE
      LCABMFNOSDEHSBTLDELCABPGNQR $.
  $}

  ${
    dedt.1 $e |- ( ( ph <-> ( ( ph /\ ch ) \/ ( ps /\ -. ch ) ) )
                     -> ( th <-> ta ) ) $.
    dedt.2 $e |- ta $.
    $( The weak deduction theorem.  For more information, see the Deduction
       Theorem link on the Metamath Proof Explorer home page.  (Contributed by
       NM, 26-Jun-2002.) $)
    dedt $p |- ( ch -> th ) $=
      ( wa wn wo wb dedlema mpbiri syl ) CAACHBCIHJKZDCABLODEGFMN $.
  $}

  $( Contraposition.  Theorem *2.16 of [WhiteheadRussell] p. 103.  This version
     of ~ con3 demonstrates the use of the weak deduction theorem ~ dedt to
     derive it from ~ con3i .  (Contributed by NM, 27-Jun-2002.)
     (Proof modification is discouraged.) $)
  con3th $p |- ( ( ph -> ps ) -> ( -. ps -> -. ph ) ) $=
    ( wi wn wa wo wb id notbid imbi1d imbi2d elimh con3i dedt ) BAABCZBDZADZCBO
    EAODEFZDZQCBRGZPSQTBRTHZIJARBAOAACARCTBRAUAKARGZARAUBHKAHLMN $.

  $( The consensus theorem.  This theorem and its dual (with ` \/ ` and ` /\ `
     interchanged) are commonly used in computer logic design to eliminate
     redundant terms from Boolean expressions.  Specifically, we prove that the
     term ` ( ps /\ ch ) ` on the left-hand side is redundant.  (Contributed by
     NM, 16-May-2003.)  (Proof shortened by Andrew Salmon, 13-May-2011.)
     (Proof shortened by Wolf Lammen, 20-Jan-2013.) $)
  consensus $p |- ( ( ( ( ph /\ ps ) \/ ( -. ph /\ ch ) ) \/ ( ps /\ ch ) ) <->
                      ( ( ph /\ ps ) \/ ( -. ph /\ ch ) ) ) $=
    ( wa wn wo id orc adantrr olc adantrl pm2.61ian jaoi impbii ) ABDZAEZCDZFZB
    CDZFRRRSRGASRABRCOQHIPCRBQOJKLMRSHN $.

  $( Theorem *4.42 of [WhiteheadRussell] p. 119.  (Contributed by Roy F.
     Longton, 21-Jun-2005.) $)
  pm4.42 $p |- ( ph <-> ( ( ph /\ ps ) \/ ( ph /\ -. ps ) ) ) $=
    ( wa wn wo wb dedlema dedlemb pm2.61i ) BAABCABDCEFBAAGBAAHI $.

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
       by NM, 18-Oct-1995.)  (Proof shortened by Wolf Lammen, 8-Dec-2012.) $)
    oplem1 $p |- ( ph -> ps ) $=
      ( wn wa notbii ord syl5bir jcad biimpar syl6 pm2.18d sylibr ) ADBADADJZCE
      KDATCETBJACBDHLABCFMNADEGMOCDEIPQRHS $.
  $}

  $( Lemma used in construction of real numbers.  (Contributed by NM,
     4-Sep-1995.)  (Proof shortened by Andrew Salmon, 26-Jun-2011.) $)
  rnlem $p |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) <->
  ( ( ( ph /\ ch ) /\ ( ps /\ th ) ) /\ ( ( ph /\ th ) /\ ( ps /\ ch ) ) ) ) $=
    ( wa an4 biimpi an42 biimpri jca adantl impbii ) ABECDEEZACEBDEEZADEBCEEZEM
    NOMNABCDFGOMADBCHZIJOMNOMPGKL $.

  $( A single axiom for Boolean algebra known as DN_1.  See
     ~ http://www-unix.mcs.anl.gov/~~mccune/papers/basax/v12.pdf .
     (Contributed by Jeffrey Hankins, 3-Jul-2009.)  (Proof shortened by Andrew
     Salmon, 13-May-2011.)  (Proof shortened by Wolf Lammen, 6-Jan-2013.) $)
  dn1 $p |- ( -. ( -. ( -. ( ph \/ ps ) \/ ch ) \/
            -. ( ph \/ -. ( -. ch \/ -. ( ch \/ th ) ) ) ) <-> ch ) $=
    ( wo wn wa wi pm2.45 imnan mpbi biorfi orcom ordir bitri pm4.45 anor orbi2i
    anbi2i 3bitrri ) CABEFZCEZACEZGZUBACFCDEZFEFZEZGUBFUGFEFCCUAAGZEZUDUHCUAAFH
    UHFABIUAAJKLUIUHCEUDCUHMUAACNOOUCUGUBCUFACCUEGUFCDPCUEQORSUBUGQT $.

  ${
    jaoi2.1 $e |- ( ( ph \/ ( -. ph /\ ch ) ) -> ps ) $.
    $( Inference removing a negated conjunct in a disjunction of an antecedent
       if this conjunct is part of the disjunction.  (Contributed by Alexander
       van der Vekens, 3-Nov-2017.) $)
    jaoi2 $p |- ( ( ph \/ ch ) -> ps ) $=
      ( wo wa wn wb exmid iba ancom andir bitri syl6bb ax-mp orbi2i orass sylbi
      bicomi pm4.44 orbi1i ) ACEAACFZAGZCFZEZEZBCUEAAUCEZCUEHAIUGCCUGFZUEUGCJUH
      UGCFUECUGKAUCCLMNOPUFAUDEZBUFAUBEZUDEZUIUKUFAUBUDQSUJAUDAUJACTSUAMDRR $.
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

  $( Define disjunction ('or') of three wff's.  Definition *2.33 of
     [WhiteheadRussell] p. 105.  This abbreviation reduces the number of
     parentheses and emphasizes that the order of bracketing is not important
     by virtue of the associative law ~ orass .  (Contributed by NM,
     8-Apr-1994.) $)
  df-3or $a |- ( ( ph \/ ps \/ ch ) <-> ( ( ph \/ ps ) \/ ch ) ) $.

  $( Define conjunction ('and') of three wff's.  Definition *4.34 of
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

  $( Commutation law for triple disjunction.  (Contributed by Mario Carneiro,
     4-Sep-2016.) $)
  3orcoma $p |- ( ( ph \/ ps \/ ch ) <-> ( ps \/ ph \/ ch ) ) $=
    ( wo w3o or12 3orass 3bitr4i ) ABCDDBACDDABCEBACEABCFABCGBACGH $.

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

  $( Triple conjunction expressed in terms of triple disjunction.  (Contributed
     by Jeff Hankins, 15-Aug-2009.) $)
  3anor $p |- ( ( ph /\ ps /\ ch ) <-> -. ( -. ph \/ -. ps \/ -. ch ) ) $=
    ( w3a wa wn w3o df-3an wo anor ianor orbi1i xchbinx df-3or xchbinxr bitri )
    ABCDABEZCEZAFZBFZCFZGZFABCHRSTIZUAIZUBRQFZUAIUDQCJUEUCUAABKLMSTUANOP $.

  $( Negated triple conjunction expressed in terms of triple disjunction.
     (Contributed by Jeff Hankins, 15-Aug-2009.)  (Proof shortened by Andrew
     Salmon, 13-May-2011.) $)
  3ianor $p |- ( -. ( ph /\ ps /\ ch ) <-> ( -. ph \/ -. ps \/ -. ch ) ) $=
    ( wn w3o w3a 3anor con2bii bicomi ) ADBDCDEZABCFZDKJABCGHI $.

  $( Negated triple disjunction as triple conjunction.  (Contributed by Scott
     Fenton, 19-Apr-2011.) $)
  3ioran $p |- ( -. ( ph \/ ps \/ ch ) <-> ( -. ph /\ -. ps /\ -. ch ) ) $=
    ( wo wn wa w3o w3a ioran anbi1i df-3or xchnxbir df-3an 3bitr4i ) ABDZEZCEZF
    ZAEZBEZFZQFABCGZESTQHPUAQABIJOCDRUBOCIABCKLSTQMN $.

  $( Triple disjunction in terms of triple conjunction.  (Contributed by NM,
     8-Oct-2012.) $)
  3oran $p |- ( ( ph \/ ps \/ ch ) <-> -. ( -. ph /\ -. ps /\ -. ch ) ) $=
    ( wn w3a w3o 3ioran con1bii bicomi ) ADBDCDEZDABCFZKJABCGHI $.

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

    $( Deduction adding conjuncts to antecedent.  (Contributed by NM,
       25-Dec-2007.) $)
    3ad2antr1 $p |- ( ( ph /\ ( ch /\ ps /\ ta ) ) -> th ) $=
      ( adantrr 3adantr3 ) ACBDEACDBFGH $.

    $( Deduction adding conjuncts to antecedent.  (Contributed by NM,
       27-Dec-2007.) $)
    3ad2antr2 $p |- ( ( ph /\ ( ps /\ ch /\ ta ) ) -> th ) $=
      ( adantrl 3adantr3 ) ABCDEACDBFGH $.

    $( Deduction adding conjuncts to antecedent.  (Contributed by NM,
       30-Dec-2007.) $)
    3ad2antr3 $p |- ( ( ph /\ ( ps /\ ta /\ ch ) ) -> th ) $=
      ( adantrl 3adantr1 ) AECDBACDEFGH $.
  $}

  ${
    3anibar.1 $e |- ( ( ph /\ ps /\ ch ) -> ( th <-> ( ch /\ ta ) ) ) $.
    $( Remove a hypothesis from the second member of a biimplication.
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
    3pm3.2i.1 $e |- ph $.
    3pm3.2i.2 $e |- ps $.
    3pm3.2i.3 $e |- ch $.
    $( Infer conjunction of premises.  (Contributed by NM, 10-Feb-1995.) $)
    3pm3.2i $p |- ( ph /\ ps /\ ch ) $=
      ( w3a wa pm3.2i df-3an mpbir2an ) ABCGABHCABDEIFABCJK $.
  $}

  ${
    $( ~ pm3.2 for a triple conjunction.  (Contributed by Alan Sare,
       24-Oct-2011.) $)
    pm3.2an3 $p |- ( ph -> ( ps -> ( ch -> ( ph /\ ps /\ ch ) ) ) ) $=
      ( wa w3a wi pm3.2 ex df-3an bicomi syl8ib ) ABCABDZCDZABCEZABCMFLCGHNMABC
      IJK $.
  $}

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
       16-Sep-2011.) $)
    mpbir3an $p |- ph $=
      ( w3a 3pm3.2i mpbir ) ABCDIBCDEFGJHK $.
  $}

  ${
    mpbir3and.1 $e |- ( ph -> ch ) $.
    mpbir3and.2 $e |- ( ph -> th ) $.
    mpbir3and.3 $e |- ( ph -> ta ) $.
    mpbir3and.4 $e |- ( ph -> ( ps <-> ( ch /\ th /\ ta ) ) ) $.
    $( Detach a conjunction of truths in a biconditional.  (Contributed by
       Mario Carneiro, 11-May-2014.)  (Revised by Mario Carneiro,
       9-Jan-2015.) $)
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
      ( exp3a 3imp ) ABCDABCDEFG $.
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
      ( 3exp imp3a ) ABCDABCDEFG $.

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
      ( wi w3a exp3a 3exp ) ABCDEFHHABCIDEFGJK $.
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
    ( w3o wo wi w3a df-3or jao syl6 3imp syl5bi ) ACDEACFZDFZABGZCBGZDBGZHBACDI
    PQROBGZPQNBGRSGABCJNBDJKLM $.

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
    ( wa w3a an4 anbi1i bitri df-3an anbi12i 3bitr4i ) ABGZCGZDEGZFGZGZADGZBEGZ
    GZCFGZGZABCHZDEFHZGTUAUCHSOQGZUCGUDOCQFIUGUBUCABDEIJKUEPUFRABCLDEFLMTUAUCLN
    $.

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
       (Contributed by NM, 25-Jul-2006.) $)
    3anandirs $p |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ta ) $=
      ( w3a wa simpl1 simpr simpl2 simpl3 syl222anc ) ABCGZDHADBDCDEABCDINDJZAB
      CDKOABCDLOFM $.
  $}

  ${
    ecase23d.1 $e |- ( ph -> -. ch ) $.
    ecase23d.2 $e |- ( ph -> -. th ) $.
    ecase23d.3 $e |- ( ph -> ( ps \/ ch \/ th ) ) $.
    $( Deduction for elimination by cases.  (Contributed by NM,
       22-Apr-1994.) $)
    ecase23d $p |- ( ph -> ps ) $=
      ( wo wn ioran sylanbrc w3o 3orass sylib ord mt3d ) ABCDHZACIDIQIEFCDJKABQ
      ABCDLBQHGBCDMNOP $.
  $}

  ${
    3ecase.1 $e |- ( -. ph -> th ) $.
    3ecase.2 $e |- ( -. ps -> th ) $.
    3ecase.3 $e |- ( -. ch -> th ) $.
    3ecase.4 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
    $( Inference for elimination by cases.  (Contributed by NM,
       13-Jul-2005.) $)
    3ecase $p |- th $=
      ( wi 3exp wn a1d pm2.61i pm2.61nii ) BCDABCDIZIABCDHJAKZOBPDCELLMFGN $.
  $}

  ${
    3biorfd.1 $e |- ( ph -> -. th ) $.
    $( A disjunction is equivalent to a threefold disjunction with single
       falsehood, analogous to ~ biorf .  (Contributed by Alexander van der
       Vekens, 8-Sep-2017.) $)
    3bior1fd $p |- ( ph -> ( ( ch \/ ps ) <-> ( th \/ ch \/ ps ) ) ) $=
      ( wo w3o wn wb biorf syl 3orass syl6bbr ) ACBFZDNFZDCBGADHNOIEDNJKDCBLM
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
      ( wa w3a biantrurd 3anass syl6bbr ) ACBFZDKFDCBGADKEHDCBIJ $.
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
        Logical 'nand' (Sheffer stroke)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Declare connective for alternative denial ('nand'). $)
  $c -/\ $. $( Overlined 'wedge' (read:  'nand') $)

  $( Extend wff definition to include alternative denial ('nand'). $)
  wnan $a wff ( ph -/\ ps ) $.

  $( Define incompatibility, or alternative denial ('not-and' or 'nand').  This
     is also called the Sheffer stroke, represented by a vertical bar, but we
     use a different symbol to avoid ambiguity with other uses of the vertical
     bar.  In the second edition of Principia Mathematica (1927), Russell and
     Whitehead used the Sheffer stroke and suggested it as a replacement for
     the "or" and "not" operations of the first edition.  However, in practice,
     "or" and "not" are more widely used.  After we define the constant true
     ` T. ` ( ~ df-tru ) and the constant false ` F. ` ( ~ df-fal ), we will be
     able to prove these truth table values: ` ( ( T. -/\ T. ) <-> F. ) `
     ( ~ trunantru ), ` ( ( T. -/\ F. ) <-> T. ) ` ( ~ trunanfal ),
     ` ( ( F. -/\ T. ) <-> T. ) ` ( ~ falnantru ), and
     ` ( ( F. -/\ F. ) <-> T. ) ` ( ~ falnanfal ).  Contrast with ` /\ `
     ( ~ df-an ), ` \/ ` ( ~ df-or ), ` -> ` ( ~ wi ), and ` \/_ `
     ( ~ df-xor ) .  (Contributed by Jeff Hoffman, 19-Nov-2007.) $)
  df-nan $a |- ( ( ph -/\ ps ) <-> -. ( ph /\ ps ) ) $.

  $( Write 'and' in terms of 'nand'.  (Contributed by Mario Carneiro,
     9-May-2015.) $)
  nanan $p |- ( ( ph /\ ps ) <-> -. ( ph -/\ ps ) ) $=
    ( wnan wa df-nan con2bii ) ABCABDABEF $.

  $( The 'nand' operator commutes.  (Contributed by Mario Carneiro,
     9-May-2015.) $)
  nancom $p |- ( ( ph -/\ ps ) <-> ( ps -/\ ph ) ) $=
    ( wa wn wnan ancom notbii df-nan 3bitr4i ) ABCZDBACZDABEBAEJKABFGABHBAHI $.

  $( Lemma for handling nested 'nand's.  (Contributed by Jeff Hoffman,
     19-Nov-2007.) $)
  nannan $p |- ( ( ph -/\ ( ch -/\ ps ) ) <-> ( ph -> ( ch /\ ps ) ) ) $=
    ( wnan wa wn wi df-nan anbi2i xchbinx iman bitr4i ) ACBDZDZACBEZFZEZFAOGNAM
    EQAMHMPACBHIJAOKL $.

  $( Show equivalence between implication and the Nicod version.  To derive
     ~ nic-dfim , apply ~ nanbi .  (Contributed by Jeff Hoffman,
     19-Nov-2007.) $)
  nanim $p |- ( ( ph -> ps ) <-> ( ph -/\ ( ps -/\ ps ) ) ) $=
    ( wnan wa wi nannan anidmdbi bitr2i ) ABBCCABBDEABEABBFABGH $.

  $( Show equivalence between negation and the Nicod version.  To derive
     ~ nic-dfneg , apply ~ nanbi .  (Contributed by Jeff Hoffman,
     19-Nov-2007.) $)
  nannot $p |- ( -. ps <-> ( ps -/\ ps ) ) $=
    ( wnan wn wa df-nan anidm xchbinx bicomi ) AABZACIAADAAAEAFGH $.

  $( Show equivalence between the bidirectional and the Nicod version.
     (Contributed by Jeff Hoffman, 19-Nov-2007.) $)
  nanbi $p |- ( ( ph <-> ps ) <->
          ( ( ph -/\ ps ) -/\ ( ( ph -/\ ph ) -/\ ( ps -/\ ps ) ) ) ) $=
    ( wa wn wo wb pm4.57 df-nan nannot anbi12i xchbinxr xchbinx dfbi3 3bitr4ri
    wnan ) ABCZDZADZBDZCZDZCZDPTEABOZAAOZBBOZOZOZABFPTGUGUCUFCUBUCUFHUCQUFUAABH
    UFUDUECTUDUEHRUDSUEAIBIJKJLABMN $.

  ${
    $( Introduce a right anti-conjunct to both sides of a logical equivalence.
       (Contributed by SF, 2-Jan-2018.) $)
    nanbi1 $p |- ( ( ph <-> ps ) -> ( ( ph -/\ ch ) <-> ( ps -/\ ch ) ) ) $=
      ( wb wa wn wnan anbi1 notbid df-nan 3bitr4g ) ABDZACEZFBCEZFACGBCGLMNABCH
      IACJBCJK $.

    $( Introduce a left anti-conjunct to both sides of a logical equivalence.
       (Contributed by SF, 2-Jan-2018.) $)
    nanbi2 $p |- ( ( ph <-> ps ) -> ( ( ch -/\ ph ) <-> ( ch -/\ ps ) ) ) $=
      ( wb wnan nanbi1 nancom 3bitr4g ) ABDACEBCECAECBEABCFCAGCBGH $.

    $( Join two logical equivalences with anti-conjunction.  (Contributed by
       SF, 2-Jan-2018.) $)
    nanbi12 $p |- ( ( ( ph <-> ps ) /\ ( ch <-> th ) ) ->
       ( ( ph -/\ ch ) <-> ( ps -/\ th ) ) ) $=
      ( wb wnan nanbi1 nanbi2 sylan9bb ) ABEACFBCFCDEBDFABCGCDBHI $.

  $}

  ${
    nanbii.1 $e |- ( ph <-> ps ) $.
    $( Introduce a right anti-conjunct to both sides of a logical equivalence.
       (Contributed by SF, 2-Jan-2018.) $)
    nanbi1i $p |- ( ( ph -/\ ch ) <-> ( ps -/\ ch ) ) $=
      ( wb wnan nanbi1 ax-mp ) ABEACFBCFEDABCGH $.

    $( Introduce a left anti-conjunct to both sides of a logical equivalence.
       (Contributed by SF, 2-Jan-2018.) $)
    nanbi2i $p |- ( ( ch -/\ ph ) <-> ( ch -/\ ps ) ) $=
      ( wb wnan nanbi2 ax-mp ) ABECAFCBFEDABCGH $.

    nanbi12i.2 $e |- ( ch <-> th ) $.
    $( Join two logical equivalences with anti-conjunction.  (Contributed by
       SF, 2-Jan-2018.) $)
    nanbi12i $p |- ( ( ph -/\ ch ) <-> ( ps -/\ th ) ) $=
      ( wb wnan nanbi12 mp2an ) ABGCDGACHBDHGEFABCDIJ $.

  $}

  ${
    nanbid.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Introduce a right anti-conjunct to both sides of a logical equivalence.
       (Contributed by SF, 2-Jan-2018.) $)
    nanbi1d $p |- ( ph -> ( ( ps -/\ th ) <-> ( ch -/\ th ) ) ) $=
      ( wb wnan nanbi1 syl ) ABCFBDGCDGFEBCDHI $.

    $( Introduce a left anti-conjunct to both sides of a logical equivalence.
       (Contributed by SF, 2-Jan-2018.) $)
    nanbi2d $p |- ( ph -> ( ( th -/\ ps ) <-> ( th -/\ ch ) ) ) $=
      ( wb wnan nanbi2 syl ) ABCFDBGDCGFEBCDHI $.

    nanbi12d.2 $e |- ( ph -> ( th <-> ta ) ) $.
    $( Join two logical equivalences with anti-conjunction.  (Contributed by
       Scott Fenton, 2-Jan-2018.) $)
    nanbi12d $p |- ( ph -> ( ( ps -/\ th ) <-> ( ch -/\ ta ) ) ) $=
      ( wb wnan nanbi12 syl2anc ) ABCHDEHBDICEIHFGBCDEJK $.

  $}

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
     left or right, but not both, are true.  After we define the constant true
     ` T. ` ( ~ df-tru ) and the constant false ` F. ` ( ~ df-fal ), we will be
     able to prove these truth table values: ` ( ( T. \/_ T. ) <-> F. ) `
     ( ~ truxortru ), ` ( ( T. \/_ F. ) <-> T. ) ` ( ~ truxorfal ),
     ` ( ( F. \/_ T. ) <-> T. ) ` ( ~ falxortru ), and
     ` ( ( F. \/_ F. ) <-> F. ) ` ( ~ falxorfal ).  Contrast with ` /\ `
     ( ~ df-an ), ` \/ ` ( ~ df-or ), ` -> ` ( ~ wi ), and ` -/\ `
     ( ~ df-nan ) .  (Contributed by FL, 22-Nov-2010.) $)
  df-xor $a |- ( ( ph \/_ ps ) <-> -. ( ph <-> ps ) ) $.

  $( Two ways to write XNOR. (Contributed by Mario Carneiro, 4-Sep-2016.) $)
  xnor $p |- ( ( ph <-> ps ) <-> -. ( ph \/_ ps ) ) $=
    ( wxo wb df-xor con2bii ) ABCABDABEF $.

  $( ` \/_ ` is commutative.  (Contributed by Mario Carneiro, 4-Sep-2016.) $)
  xorcom $p |- ( ( ph \/_ ps ) <-> ( ps \/_ ph ) ) $=
    ( wb wn wxo bicom notbii df-xor 3bitr4i ) ABCZDBACZDABEBAEJKABFGABHBAHI $.

  $( ` \/_ ` is associative.  (Contributed by FL, 22-Nov-2010.)  (Proof
     shortened by Andrew Salmon, 8-Jun-2011.) $)
  xorass $p |- ( ( ( ph \/_ ps ) \/_ ch ) <-> ( ph \/_ ( ps \/_ ch ) ) ) $=
    ( wxo wb wn biass notbii nbbn pm5.18 con2bii 3bitr4i df-xor bibi1i bibi2i )
    ABDZCEZFABCDZEZFPCDARDQSABEZFZCEZABCEZFZEZQSTCEZFAUCEZFUBUEUFUGABCGHTCIUGUE
    AUCJKLPUACABMNRUDABCMOLHPCMARML $.

  $( This tautology shows that xor is really exclusive.  (Contributed by FL,
     22-Nov-2010.) $)
  excxor $p |- ( ( ph \/_ ps ) <->
       ( ( ph /\ -. ps ) \/ ( -. ph /\ ps ) ) ) $=
    ( wxo wb wn wa wo df-xor xor ancom orbi2i 3bitri ) ABCABDEABEFZBAEZFZGMNBFZ
    GABHABIOPMBNJKL $.

  $( Two ways to express "exclusive or."  (Contributed by Mario Carneiro,
     4-Sep-2016.) $)
  xor2 $p |- ( ( ph \/_ ps ) <->
       ( ( ph \/ ps ) /\ -. ( ph /\ ps ) ) ) $=
    ( wxo wb wn wo wa df-xor nbi2 bitri ) ABCABDEABFABGEGABHABIJ $.

  $( ` \/_ ` is negated under negation of one argument.  (Contributed by Mario
     Carneiro, 4-Sep-2016.) $)
  xorneg1 $p |- ( ( -. ph \/_ ps ) <-> -. ( ph \/_ ps ) ) $=
    ( wn wxo wb df-xor nbbn con2bii xnor 3bitr2i ) ACZBDKBEZCABEZABDCKBFLMABGHA
    BIJ $.

  $( ` \/_ ` is negated under negation of one argument.  (Contributed by Mario
     Carneiro, 4-Sep-2016.) $)
  xorneg2 $p |- ( ( ph \/_ -. ps ) <-> -. ( ph \/_ ps ) ) $=
    ( wn wxo xorneg1 xorcom notbii 3bitr4i ) BCZADBADZCAIDABDZCBAEAIFKJABFGH $.

  $( ` \/_ ` is unchanged under negation of both arguments.  (Contributed by
     Mario Carneiro, 4-Sep-2016.) $)
  xorneg $p |- ( ( -. ph \/_ -. ps ) <-> ( ph \/_ ps ) ) $=
    ( wn wxo xorneg1 xorneg2 con2bii bitr4i ) ACBCZDAIDZCABDZAIEJKABFGH $.

  ${
    xorbi12.1 $e |- ( ph <-> ps ) $.
    xorbi12.2 $e |- ( ch <-> th ) $.
    $( Equality property for XOR. (Contributed by Mario Carneiro,
       4-Sep-2016.) $)
    xorbi12i $p |- ( ( ph \/_ ch ) <-> ( ps \/_ th ) ) $=
      ( wb wn wxo bibi12i notbii df-xor 3bitr4i ) ACGZHBDGZHACIBDINOABCDEFJKACL
      BDLM $.
  $}

  ${
    xor12d.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    xor12d.2 $e |- ( ph -> ( th <-> ta ) ) $.
    $( Equality property for XOR. (Contributed by Mario Carneiro,
       4-Sep-2016.) $)
    xorbi12d $p |- ( ph -> ( ( ps \/_ th ) <-> ( ch \/_ ta ) ) ) $=
      ( wb wn wxo bibi12d notbid df-xor 3bitr4g ) ABDHZICEHZIBDJCEJAOPABCDEFGKL
      BDMCEMN $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                True and false constants
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c T. $.
  $c F. $.

  $( ` T. ` is a wff. $)
  wtru $a wff T. $.

  $( ` F. ` is a wff. $)
  wfal $a wff F. $.

  $( Soundness justification theorem for ~ df-tru .  (Contributed by Mario
     Carneiro, 17-Nov-2013.) $)
  trujust $p |- ( ( ph <-> ph ) <-> ( ps <-> ps ) ) $=
    ( wb biid 2th ) AACBBCADBDE $.

  $( Definition of ` T. ` , a tautology. ` T. ` is a constant true.  In this
     definition ~ biid is used as an antecedent, however, any true wff, such as
     an axiom, can be used in its place.  (Contributed by Anthony Hart,
     13-Oct-2010.) $)
  df-tru $a |- ( T. <-> ( ph <-> ph ) ) $.

  $( Definition of ` F. ` , a contradiction. ` F. ` is a constant false.
     (Contributed by Anthony Hart, 22-Oct-2010.) $)
  df-fal $a |- ( F. <-> -. T. ) $.

  $( ` T. ` is provable.  (Contributed by Anthony Hart, 13-Oct-2010.) $)
  tru $p |- T. $=
    ( wph wtru wb biid df-tru mpbir ) BAACADAEF $.

  $( ` F. ` is refutable.  (Contributed by Anthony Hart, 22-Oct-2010.)  (Proof
     shortened by Mel L. O'Cat, 11-Mar-2012.) $)
  fal $p |- -. F. $=
    ( wfal wtru wn tru notnoti df-fal mtbir ) ABCBDEFG $.

  ${
    trud.1 $e |- ( T. -> ph ) $.
    $( Eliminate ` T. ` as an antecedent.  (Contributed by Mario Carneiro,
       13-Mar-2014.) $)
    trud $p |- ph $=
      ( wtru tru ax-mp ) CADBE $.
  $}

  $( If something is true, it outputs ` T. ` .  (Contributed by Anthony Hart,
     14-Aug-2011.) $)
  tbtru $p |- ( ph <-> ( ph <-> T. ) ) $=
    ( wtru tru tbt ) BACD $.

  $( If something is not true, it outputs ` F. ` .  (Contributed by Anthony
     Hart, 14-Aug-2011.) $)
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

  $( ` F. ` implies anything.  (Contributed by FL, 20-Mar-2011.)  (Proof
     shortened by Anthony Hart, 1-Aug-2011.) $)
  falim $p |- ( F. -> ph ) $=
    ( wfal fal pm2.21i ) BACD $.

  $( ` F. ` implies anything.  (Contributed by Mario Carneiro, 9-Feb-2017.) $)
  falimd $p |- ( ( ph /\ F. ) -> ps ) $=
    ( wfal falim adantl ) CBABDE $.

  $( Anything implies ` T. ` .  (Contributed by FL, 20-Mar-2011.)  (Proof
     shortened by Anthony Hart, 1-Aug-2011.) $)
  a1tru $p |- ( ph -> T. ) $=
    ( wtru tru a1i ) BACD $.

  $( True can be removed from a conjunction.  (Contributed by FL,
     20-Mar-2011.) $)
  truan $p |- ( ( T. /\ ph ) <-> ph ) $=
    ( wtru wa simpr a1tru ancri impbii ) BACABADABAEFG $.

  $( Given falsum, we can define the negation of a wff ` ph ` as the statement
     that a contradiction follows from assuming ` ph ` .  (Contributed by Mario
     Carneiro, 9-Feb-2017.) $)
  dfnot $p |- ( -. ph <-> ( ph -> F. ) ) $=
    ( wn wfal wi pm2.21 id falim ja impbii ) ABZACDACEACJJFJGHI $.

  ${
    inegd.1 $e |- ( ( ph /\ ps ) -> F. ) $.
    $( Negation introduction rule from natural deduction.  (Contributed by
       Mario Carneiro, 9-Feb-2017.) $)
    inegd $p |- ( ph -> -. ps ) $=
      ( wfal wi wn ex dfnot sylibr ) ABDEBFABDCGBHI $.
  $}

  ${
    efald.1 $e |- ( ( ph /\ -. ps ) -> F. ) $.
    $( Deduction based on reductio ad absurdum.  (Contributed by Mario
       Carneiro, 9-Feb-2017.) $)
    efald $p |- ( ph -> ps ) $=
      ( wn inegd notnotrd ) ABABDCEF $.
  $}

  ${
    pm2.21fal.1 $e |- ( ph -> ps ) $.
    pm2.21fal.2 $e |- ( ph -> -. ps ) $.
    $( If a wff and its negation are provable, then falsum is provable.
       (Contributed by Mario Carneiro, 9-Feb-2017.) $)
    pm2.21fal $p |- ( ph -> F. ) $=
      ( wfal pm2.21dd ) ABECDF $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Truth tables
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  Some sources define operations on true/false values using truth tables.
  These tables show the results of their operations for all possible
  combinations of true ( ` T. ` ) and false ( ` F. ` ).
  Here we show that our definitions and axioms produce equivalent results for
  ` /\ ` (conjunction aka logical 'and') ~ df-an ,
  ` \/ ` (disjunction aka logical inclusive 'or') ~ df-or ,
  ` -> ` (implies) ~ wi ,
  ` -. ` (not) ~ wn ,
  ` <-> ` (logical equivalence) ~ df-bi ,
  ` -/\ ` (nand aka Sheffer stroke) ~ df-nan , and
  ` \/_ ` (exclusive or) ~ df-xor .
$)

  $( A ` /\ ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.) $)
  truantru $p |- ( ( T. /\ T. ) <-> T. ) $=
    ( wtru anidm ) AB $.

  $( A ` /\ ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.) $)
  truanfal $p |- ( ( T. /\ F. ) <-> F. ) $=
    ( wfal truan ) AB $.

  $( A ` /\ ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.) $)
  falantru $p |- ( ( F. /\ T. ) <-> F. ) $=
    ( wfal wtru wa fal intnanr bifal ) ABCABDEF $.

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

  $( A ` <-> ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.)  (Proof
     shortened by Andrew Salmon, 13-May-2011.) $)
  trubifal $p |- ( ( T. <-> F. ) <-> F. ) $=
    ( wtru wfal wb wn nottru nbbn mpbi bifal ) ABCZADBCIDEABFGH $.

  $( A ` <-> ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.)  (Proof
     shortened by Andrew Salmon, 13-May-2011.) $)
  falbitru $p |- ( ( F. <-> T. ) <-> F. ) $=
    ( wfal wtru wb bicom trubifal bitri ) ABCBACAABDEF $.

  $( A ` <-> ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.)  (Proof
     shortened by Andrew Salmon, 13-May-2011.) $)
  falbifal $p |- ( ( F. <-> F. ) <-> T. ) $=
    ( wfal wb biid bitru ) AABACD $.

  $( A ` -/\ ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.)  (Proof
     shortened by Andrew Salmon, 13-May-2011.) $)
  trunantru $p |- ( ( T. -/\ T. ) <-> F. ) $=
    ( wtru wnan wn wfal nannot nottru bitr3i ) AABACDAEFG $.

  $( A ` -/\ ` identity.  (Contributed by Anthony Hart, 23-Oct-2010.)  (Proof
     shortened by Andrew Salmon, 13-May-2011.) $)
  trunanfal $p |- ( ( T. -/\ F. ) <-> T. ) $=
    ( wtru wfal wnan wa wn df-nan truanfal notbii notfal 3bitri ) ABCABDZEBEAAB
    FKBGHIJ $.

  $( A ` -/\ ` identity.  (Contributed by Anthony Hart, 23-Oct-2010.)  (Proof
     shortened by Andrew Salmon, 13-May-2011.) $)
  falnantru $p |- ( ( F. -/\ T. ) <-> T. ) $=
    ( wfal wtru wnan nancom trunanfal bitri ) ABCBACBABDEF $.

  $( A ` -/\ ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.)  (Proof
     shortened by Andrew Salmon, 13-May-2011.) $)
  falnanfal $p |- ( ( F. -/\ F. ) <-> T. ) $=
    ( wfal wnan wn wtru nannot notfal bitr3i ) AABACDAEFG $.

  $( A ` \/_ ` identity.  (Contributed by David A. Wheeler, 8-May-2015.) $)
  truxortru $p |- ( ( T. \/_ T. ) <-> F. ) $=
    ( wtru wxo wn wfal wb df-xor trubitru xchbinx nottru bitri ) AABZACDKAAEAAA
    FGHIJ $.

  $( A ` \/_ ` identity.  (Contributed by David A. Wheeler, 8-May-2015.) $)
  truxorfal $p |- ( ( T. \/_ F. ) <-> T. ) $=
    ( wtru wfal wxo wn wb df-xor trubifal xchbinx notfal bitri ) ABCZBDAKABEBAB
    FGHIJ $.

  $( A ` \/_ ` identity.  (Contributed by David A. Wheeler, 9-May-2015.) $)
  falxortru $p |- ( ( F. \/_ T. ) <-> T. ) $=
    ( wfal wtru wxo wb wn df-xor falbitru notbii notfal 3bitri ) ABCABDZEAEBABF
    KAGHIJ $.

  $( A ` \/_ ` identity.  (Contributed by David A. Wheeler, 9-May-2015.) $)
  falxorfal $p |- ( ( F. \/_ F. ) <-> F. ) $=
    ( wfal wxo wtru wn wb df-xor falbifal xchbinx nottru bitri ) AABZCDAKAAECAA
    FGHIJ $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
       Auxiliary theorems for Alan Sare's virtual deduction tool, part 1
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    ee22.1 $e |- ( ph -> ( ps -> ch ) ) $.
    ee22.2 $e |- ( ph -> ( ps -> th ) ) $.
    ee22.3 $e |- ( ch -> ( th -> ta ) ) $.
    $( Virtual deduction rule ~ e22 without virtual deduction connectives.
       Special theorem needed for Alan Sare's virtual deduction translation
       tool.  (Contributed by Alan Sare, 2-May-2011.)
       (New usage is discouraged.)  TODO: decide if this is worth keeping. $)
    ee22 $p |- ( ph -> ( ps -> ta ) ) $=
      ( syl6c ) ABCDEFGHI $.
  $}

  ${
    ee12an.1 $e |- ( ph -> ps ) $.
    ee12an.2 $e |- ( ph -> ( ch -> th ) ) $.
    ee12an.3 $e |- ( ( ps /\ th ) -> ta ) $.
    $( ~ e12an without virtual deduction connectives.  Special theorem needed
       for Alan Sare's virtual deduction translation tool.  (Contributed by
       Alan Sare, 28-Oct-2011.)  TODO: this is frequently used; come up with
       better label. $)
    ee12an $p |- ( ph -> ( ch -> ta ) ) $=
      ( wa jctild syl6 ) ACBDIEACDBGFJHK $.
  $}

  ${
    ee23.1 $e |- ( ph -> ( ps -> ch ) ) $.
    ee23.2 $e |- ( ph -> ( ps -> ( th -> ta ) ) ) $.
    ee23.3 $e |- ( ch -> ( ta -> et ) ) $.
    $( ~ e23 without virtual deductions.  (Contributed by Alan Sare,
       17-Jul-2011.)  (New usage is discouraged.)  TODO: decide if this is
       worth keeping. $)
    ee23 $p |- ( ph -> ( ps -> ( th -> et ) ) ) $=
      ( wi syl6 syldd ) ABDEFHABCEFJGIKL $.
  $}

  $( Exportation implication also converting head from biconditional to
     conditional.  This proof is ~ exbirVD automatically translated and
     minimized.  (Contributed by Alan Sare, 31-Dec-2011.)
     (New usage is discouraged.)  TODO: decide if this is worth keeping. $)
  exbir $p |- ( ( ( ph /\ ps ) -> ( ch <-> th ) ) ->
              ( ph -> ( ps -> ( th -> ch ) ) ) ) $=
    ( wa wb wi bi2 imim2i exp3a ) ABEZCDFZGABDCGZLMKCDHIJ $.

  $( ~ impexp with a 3-conjunct antecedent.  (Contributed by Alan Sare,
     31-Dec-2011.) $)
  3impexp $p |- ( ( ( ph /\ ps /\ ch ) -> th ) <->
                ( ph -> ( ps -> ( ch -> th ) ) ) ) $=
    ( w3a wi id 3expd 3impd impbii ) ABCEDFZABCDFFFZKABCDKGHLABCDLGIJ $.

  $( ~ 3impexp with biconditional consequent of antecedent that is commuted in
     consequent.  Derived automatically from ~ 3impexpVD .  (Contributed by
     Alan Sare, 31-Dec-2011.)  (New usage is discouraged.)  TODO: decide if
     this is worth keeping. $)
  3impexpbicom $p |- ( ( ( ph /\ ps /\ ch ) -> ( th <-> ta ) ) <->
                     ( ph -> ( ps -> ( ch -> ( ta <-> th ) ) ) ) ) $=
    ( w3a wb wi bicom imbi2 biimpcd mpi 3expd 3impexp biimpri syl6ibr impbii )
    ABCFZDEGZHZABCEDGZHHHZTABCUATSUAGZRUAHZDEIZUCTUDSUARJKLMUBRUASUDUBABCUANOUE
    PQ $.

  ${
    3impexpbicomi.1 $e |- ( ( ph /\ ps /\ ch ) -> ( th <-> ta ) ) $.
    $( Deduction form of ~ 3impexpbicom .  Derived automatically from
       ~ 3impexpbicomiVD .  (Contributed by Alan Sare, 31-Dec-2011.)
       (New usage is discouraged.)  TODO: decide if this is worth keeping. $)
    3impexpbicomi $p |- ( ph -> ( ps -> ( ch -> ( ta <-> th ) ) ) ) $=
      ( wb w3a bicomd 3exp ) ABCEDGABCHDEFIJ $.
  $}

  $( Closed form of ~ ancoms .  Derived automatically from ~ ancomsimpVD .
     (Contributed by Alan Sare, 31-Dec-2011.) $)
  ancomsimp $p |- ( ( ( ph /\ ps ) -> ch ) <-> ( ( ps /\ ph ) -> ch ) ) $=
    ( wa ancom imbi1i ) ABDBADCABEF $.

  ${
    exp3acom3r.1 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
    $( Export and commute antecedents.  (Contributed by Alan Sare,
       18-Mar-2012.) $)
    exp3acom3r $p |- ( ps -> ( ch -> ( ph -> th ) ) ) $=
      ( exp3a com3l ) ABCDABCDEFG $.
  $}

  $( Implication form of ~ exp3acom23 .  (Contributed by Alan Sare,
     22-Jul-2012.)  (New usage is discouraged.)  TODO: decide if this is worth
     keeping. $)
  exp3acom23g $p |- ( ( ph -> ( ( ps /\ ch ) -> th ) ) <->
                        ( ph -> ( ch -> ( ps -> th ) ) ) ) $=
    ( wa wi ancomsimp impexp bitri imbi2i ) BCEDFZCBDFFZAKCBEDFLBCDGCBDHIJ $.

  ${
    exp3acom23.1 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
    $( The exportation deduction ~ exp3a with commutation of the conjoined
       wwfs.  (Contributed by Alan Sare, 22-Jul-2012.) $)
    exp3acom23 $p |- ( ph -> ( ch -> ( ps -> th ) ) ) $=
      ( exp3a com23 ) ABCDABCDEFG $.
  $}

  $( Implication form of ~ simplbi2com .  (Contributed by Alan Sare,
     22-Jul-2012.)  (New usage is discouraged.)  TODO: decide if this is worth
     keeping. $)
  simplbi2comg $p |- ( ( ph <-> ( ps /\ ch ) ) -> ( ch -> ( ps -> ph ) ) ) $=
    ( wa wb bi2 exp3acom23 ) ABCDZEBCAAHFG $.

  ${
    simplbi2com.1 $e |- ( ph <-> ( ps /\ ch ) ) $.
    $( A deduction eliminating a conjunct, similar to ~ simplbi2 .
       (Contributed by Alan Sare, 22-Jul-2012.)  (Proof shortened by Wolf
       Lammen, 10-Nov-2012.) $)
    simplbi2com $p |- ( ch -> ( ps -> ph ) ) $=
      ( simplbi2 com12 ) BCAABCDEF $.
  $}

  ${
    ee21.1 $e |- ( ph -> ( ps -> ch ) ) $.
    ee21.2 $e |- ( ph -> th ) $.
    ee21.3 $e |- ( ch -> ( th -> ta ) ) $.
    $( ~ e21 without virtual deductions.  (Contributed by Alan Sare,
       18-Mar-2012.)  (New usage is discouraged.)  TODO: decide if this is
       worth keeping. $)
    ee21 $p |- ( ph -> ( ps -> ta ) ) $=
      ( a1d ee22 ) ABCDEFADBGIHJ $.
  $}

  ${
    ee10.1 $e |- ( ph -> ps ) $.
    ee10.2 $e |- ch $.
    ee10.3 $e |- ( ps -> ( ch -> th ) ) $.
    $( ~ e10 without virtual deductions.  (Contributed by Alan Sare,
       25-Jul-2011.)  TODO: this is frequently used; come up with better
       label. $)
    ee10 $p |- ( ph -> th ) $=
      ( mpi syl ) ABDEBCDFGHI $.
  $}

  ${
    ee02.1 $e |- ph $.
    ee02.2 $e |- ( ps -> ( ch -> th ) ) $.
    ee02.3 $e |- ( ph -> ( th -> ta ) ) $.
    $( ~ e02 without virtual deductions.  (Contributed by Alan Sare,
       22-Jul-2012.)  (New usage is discouraged.)  TODO: decide if this is
       worth keeping. $)
    ee02 $p |- ( ps -> ( ch -> ta ) ) $=
      ( a1i sylsyld ) BACDEABFIGHJ $.
  $}

$( End of auxiliary theorems for Alan Sare's virtual deduction tool, part 1 $)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
       Half-adders and full adders in propositional calculus
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  Propositional calculus deals with truth values, which can be interpreted as
  bits. Using this, we can define the half-adder in pure propositional
  calculus, and show its basic properties.

$)

  $c hadd cadd $.
  $c , $.  $( Comma (also used for unordered pair notation later) $)

  $( Define the half adder (triple XOR).  (Contributed by Mario Carneiro,
     4-Sep-2016.) $)
  whad $a wff hadd ( ph , ps , ch ) $.

  $( Define the half adder carry.  (Contributed by Mario Carneiro,
     4-Sep-2016.) $)
  wcad $a wff cadd ( ph , ps , ch ) $.

  $( Define the half adder (triple XOR).  (Contributed by Mario Carneiro,
     4-Sep-2016.) $)
  df-had $a |- ( hadd ( ph , ps , ch ) <-> ( ( ph \/_ ps ) \/_ ch ) ) $.

  $( Define the half adder carry, which is true when at least two arguments are
     true.  (Contributed by Mario Carneiro, 4-Sep-2016.) $)
  df-cad $a |- ( cadd ( ph , ps , ch ) <->
    ( ( ph /\ ps ) \/ ( ch /\ ( ph \/_ ps ) ) ) ) $.

  ${
    hadbid.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    hadbid.2 $e |- ( ph -> ( th <-> ta ) ) $.
    hadbid.3 $e |- ( ph -> ( et <-> ze ) ) $.
    $( Equality theorem for half adder.  (Contributed by Mario Carneiro,
       4-Sep-2016.) $)
    hadbi123d $p |- ( ph ->
      ( hadd ( ps , th , et ) <-> hadd ( ch , ta , ze ) ) ) $=
      ( wxo whad xorbi12d df-had 3bitr4g ) ABDKZFKCEKZGKBDFLCEGLAPQFGABCDEHIMJM
      BDFNCEGNO $.

    $( Equality theorem for adder carry.  (Contributed by Mario Carneiro,
       4-Sep-2016.) $)
    cadbi123d $p |- ( ph ->
      ( cadd ( ps , th , et ) <-> cadd ( ch , ta , ze ) ) ) $=
      ( wa wxo wo wcad anbi12d xorbi12d orbi12d df-cad 3bitr4g ) ABDKZFBDLZKZMC
      EKZGCELZKZMBDFNCEGNATUCUBUEABCDEHIOAFGUAUDJABCDEHIPOQBDFRCEGRS $.
  $}

  ${
    hadbii.1 $e |- ( ph <-> ps ) $.
    hadbii.2 $e |- ( ch <-> th ) $.
    hadbii.3 $e |- ( ta <-> et ) $.
    $( Equality theorem for half adder.  (Contributed by Mario Carneiro,
       4-Sep-2016.) $)
    hadbi123i $p |- ( hadd ( ph , ch , ta ) <-> hadd ( ps , th , et ) ) $=
      ( whad wb wtru a1i hadbi123d trud ) ACEJBDFJKLABCDEFABKLGMCDKLHMEFKLIMNO
      $.

    $( Equality theorem for adder carry.  (Contributed by Mario Carneiro,
       4-Sep-2016.) $)
    cadbi123i $p |- ( cadd ( ph , ch , ta ) <-> cadd ( ps , th , et ) ) $=
      ( wcad wb wtru a1i cadbi123d trud ) ACEJBDFJKLABCDEFABKLGMCDKLHMEFKLIMNO
      $.
  $}

  $( Associative law for triple XOR. (Contributed by Mario Carneiro,
     4-Sep-2016.) $)
  hadass $p |- ( hadd ( ph , ps , ch ) <-> ( ph \/_ ( ps \/_ ch ) ) ) $=
    ( whad wxo df-had xorass bitri ) ABCDABECEABCEEABCFABCGH $.

  $( The half adder is the same as the triple biconditional.  (Contributed by
     Mario Carneiro, 4-Sep-2016.) $)
  hadbi $p |- ( hadd ( ph , ps , ch ) <-> ( ( ph <-> ps ) <-> ch ) ) $=
    ( wxo wb wn whad df-xor df-had xnor bibi1i nbbn bitri 3bitr4i ) ABDZCDOCEFZ
    ABCGABEZCEZOCHABCIROFZCEPQSCABJKOCLMN $.

  $( Commutative law for triple XOR. (Contributed by Mario Carneiro,
     4-Sep-2016.) $)
  hadcoma $p |- ( hadd ( ph , ps , ch ) <-> hadd ( ps , ph , ch ) ) $=
    ( wxo whad xorcom biid xorbi12i df-had 3bitr4i ) ABDZCDBADZCDABCEBACEKLCCAB
    FCGHABCIBACIJ $.

  $( Commutative law for triple XOR. (Contributed by Mario Carneiro,
     4-Sep-2016.) $)
  hadcomb $p |- ( hadd ( ph , ps , ch ) <-> hadd ( ph , ch , ps ) ) $=
    ( wxo whad biid xorcom xorbi12i hadass 3bitr4i ) ABCDZDACBDZDABCEACBEAAKLAF
    BCGHABCIACBIJ $.

  $( Rotation law for triple XOR. (Contributed by Mario Carneiro,
     4-Sep-2016.) $)
  hadrot $p |- ( hadd ( ph , ps , ch ) <-> hadd ( ps , ch , ph ) ) $=
    ( whad hadcoma hadcomb bitri ) ABCDBACDBCADABCEBACFG $.

  $( Write the adder carry in disjunctive normal form.  (Contributed by Mario
     Carneiro, 4-Sep-2016.) $)
  cador $p |- ( cadd ( ph , ps , ch ) <->
    ( ( ph /\ ps ) \/ ( ph /\ ch ) \/ ( ps /\ ch ) ) ) $=
    ( wcad wa wxo wo df-cad wn wi xor2 rbaib anbi1d ancom andir 3bitr3g pm5.74i
    w3o df-or bitri 3orass 3bitr4i ) ABCDABEZCABFZEZGZUCACEZBCEZRZABCHUCIZUEJUJ
    UGUHGZJZUFUIUJUEUKUJUDCEABGZCEUEUKUJUDUMCUDUMUJABKLMUDCNABCOPQUCUESUIUCUKGU
    LUCUGUHUAUCUKSTUBT $.

  $( Write the adder carry in conjunctive normal form.  (Contributed by Mario
     Carneiro, 4-Sep-2016.) $)
  cadan $p |- ( cadd ( ph , ps , ch ) <->
    ( ( ph \/ ps ) /\ ( ph \/ ch ) /\ ( ps \/ ch ) ) ) $=
    ( wa w3o wo wcad w3a ordir wn wi wb simpr con3i biorf pm5.74i df-or 3bitr4i
    syl orcom anbi2i 3bitr3i syl6bb bitr3i anbi12i bitri df-3or anandir df-3an
    ordi cador ) ABDZACDZBCDZEZABFZACFZDBCFZDZABCGUPUQURHULUMFZUNFZUPURDZUQURDZ
    DZUOUSVAUTBFZUTCFZDVDUTBCUJVEVBVFVCUMBFZUPCBFZDVEVBACBIBUMFZBUTFZVGVEBJZUMK
    VKUTKVIVJVKUMUTVKULJUMUTLULBABMNULUMOSPBUMQBUTQRUMBTUTBTRVHURUPCBTUAUBVFULC
    FZVCCULFZCUTFZVLVFCJZULKVOUTKVMVNVOULUTVOUMJZULUTLUMCACMNVPULUMULFUTUMULOUM
    ULTUCSPCULQCUTQRULCTUTCTRABCIUDUEUFULUMUNUGUPUQURUHRABCUKUPUQURUIR $.

  $( The half adder distributes over negation.  (Contributed by Mario Carneiro,
     4-Sep-2016.) $)
  hadnot $p |- ( -. hadd ( ph , ps , ch ) <->
    hadd ( -. ph , -. ps , -. ch ) ) $=
    ( wxo wn whad xorneg biid xorbi12i xorneg2 bitr2i df-had notbii 3bitr4i ) A
    BDZCDZEZAEZBEZDZCEZDZABCFZERSUAFUBOUADQTOUAUAABGUAHIOCJKUCPABCLMRSUALN $.

  $( The adder carry distributes over negation.  (Contributed by Mario
     Carneiro, 4-Sep-2016.) $)
  cadnot $p |- ( -. cadd ( ph , ps , ch ) <->
    cadd ( -. ph , -. ps , -. ch ) ) $=
    ( wa w3o wn wo wcad 3ioran ianor 3anbi123i bitri cador notbii cadan 3bitr4i
    w3a ) ABDZACDZBCDZEZFZAFZBFZGZUCCFZGZUDUFGZQZABCHZFUCUDUFHUBRFZSFZTFZQUIRST
    IUKUEULUGUMUHABJACJBCJKLUJUAABCMNUCUDUFOP $.

  $( Commutative law for adder carry.  (Contributed by Mario Carneiro,
     4-Sep-2016.) $)
  cadcoma $p |- ( cadd ( ph , ps , ch ) <-> cadd ( ps , ph , ch ) ) $=
    ( wa wxo wo wcad ancom xorcom anbi2i orbi12i df-cad 3bitr4i ) ABDZCABEZDZFB
    ADZCBAEZDZFABCGBACGNQPSABHORCABIJKABCLBACLM $.

  $( Commutative law for adder carry.  (Contributed by Mario Carneiro,
     4-Sep-2016.) $)
  cadcomb $p |- ( cadd ( ph , ps , ch ) <-> cadd ( ph , ch , ps ) ) $=
    ( wa w3o wcad 3orcoma biid ancom 3orbi123i bitri cador 3bitr4i ) ABDZACDZBC
    DZEZONCBDZEZABCFACBFQONPESNOPGOONNPROHNHBCIJKABCLACBLM $.

  $( Rotation law for adder carry.  (Contributed by Mario Carneiro,
     4-Sep-2016.) $)
  cadrot $p |- ( cadd ( ph , ps , ch ) <-> cadd ( ps , ch , ph ) ) $=
    ( wcad cadcoma cadcomb bitri ) ABCDBACDBCADABCEBACFG $.

  $( If one parameter is true, the adder carry is true exactly when at least
     one of the other parameters is true.  (Contributed by Mario Carneiro,
     8-Sep-2016.) $)
  cad1 $p |- ( ch -> ( cadd ( ph , ps , ch ) <-> ( ph \/ ps ) ) ) $=
    ( wa wxo wo wcad ibar bicomd orbi2d df-cad wn pm5.63 olc orc adantr id jaoi
    impbii xor2 ancom bitri orbi2i 3bitr4i 3bitr4g ) CABDZCABEZDZFUFUGFZABCGABF
    ZCUHUGUFCUGUHCUGHIJABCKUFUJFZUFUFLZUJDZFUJUIUFUJMUJUKUJUFNUFUJUJAUJBABOPUJQ
    RSUGUMUFUGUJULDUMABTUJULUAUBUCUDUE $.

  $( If two parameters are true, the adder carry is true.  (Contributed by
     Mario Carneiro, 4-Sep-2016.) $)
  cad11 $p |- ( ( ph /\ ps ) -> cadd ( ph , ps , ch ) ) $=
    ( wa wxo wo wcad orc df-cad sylibr ) ABDZKCABEDZFABCGKLHABCIJ $.

  $( If one parameter is false, the adder carry is true exactly when both of
     the other two parameters are true.  (Contributed by Mario Carneiro,
     8-Sep-2016.) $)
  cad0 $p |- ( -. ch -> ( cadd ( ph , ps , ch ) <-> ( ph /\ ps ) ) ) $=
    ( wcad wa wxo wo wn df-cad idd pm2.21 adantrd jaod orc impbid1 syl5bb ) ABC
    DABEZCABFZEZGZCHZQABCIUATQUAQQSUAQJUACQRCQKLMQSNOP $.

  $( Rotation law for adder carry.  (Contributed by Mario Carneiro,
     4-Sep-2016.) $)
  cadtru $p |- cadd ( T. , T. , ph ) $=
    ( wtru wcad tru cad11 mp2an ) BBBBACDDBBAEF $.

  $( If the first parameter is true, the half adder is equivalent to the
     equality of the other two inputs.  (Contributed by Mario Carneiro,
     4-Sep-2016.) $)
  had1 $p |- ( ph -> ( hadd ( ph , ps , ch ) <-> ( ps <-> ch ) ) ) $=
    ( whad wb hadbi biass bitri id biidd 2thd sylibr syl5bb ) ABCDZABCEZEZAONAB
    ECEPABCFABCGHAAOOEZEPOEAAQAIAOJKAOOGLM $.

  $( If the first parameter is false, the half adder is equivalent to the XOR
     of the other two inputs.  (Contributed by Mario Carneiro, 4-Sep-2016.) $)
  had0 $p |- ( -. ph -> ( hadd ( ph , ps , ch ) <-> ( ps \/_ ch ) ) ) $=
    ( wn whad wxo wb had1 hadnot df-xor xorneg bitr3i con1bii 3bitr4g con4bid )
    ADZABCEZBCFZPPBDZCDZESTGZQDRDPSTHABCIUARUADSTFRSTJBCKLMNO $.

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
     axioms as ~ ax1 , ~ ax2 , and ~ ax3 , thus proving the equivalence of all
     three systems.  C. A. Meredith, "Single Axioms for the Systems (C,N),
     (C,O) and (A,N) of the Two-Valued Propositional Calculus," _The Journal of
     Computing Systems_ vol. 1 (1953), pp. 155-164.  Meredith claimed to be
     close to a proof that this axiom is the shortest possible, but the proof
     was apparently never completed.

     An obscure Irish lecturer, Meredith (1904-1976) became enamored with logic
     somewhat late in life after attending talks by Lukasiewicz and produced
     many remarkable results such as this axiom.  From his obituary:  "He did
     logic whenever time and opportunity presented themselves, and he did it on
     whatever materials came to hand: in a pub, his favored pint of porter
     within reach, he would use the inside of cigarette packs to write proofs
     for logical colleagues."  (Contributed by NM, 14-Dec-2002.)  (Proof
     shortened by Andrew Salmon, 25-Jul-2011.)  (Proof shortened by Wolf
     Lammen, 28-May-2013.) $)
  meredith $p |- ( ( ( ( ( ph -> ps ) -> ( -. ch -> -. th ) ) -> ch ) ->
       ta ) -> ( ( ta -> ph ) -> ( th -> ph ) ) ) $=
    ( wi wn pm2.21 ax-3 imim12i com13 con1d com12 a1d ax-1 imim1d ja ) ABFZCGDG
    FZFZCFZEEAFZDAFZFUAGZUCUBDUDADAUATAGZDCUERSDCFABHCDIJKLMNEDEAEDOPQ $.

  $( Alias for ~ meredith which "verify markup *" will match to
     ~ ax-meredith .  (Contributed by NM, 21-Aug-2017.)
     (New usage is discouraged.) $)
  axmeredith $p |- ( ( ( ( ( ph -> ps ) -> ( -. ch -> -. th ) ) -> ch ) ->
       ta ) -> ( ( ta -> ph ) -> ( th -> ph ) ) ) $=
    ( meredith ) ABCDEF $.

  $( Theorem ~ meredith restated as an axiom.  This will allow us to ensure
     that the rederivation of ~ ax1 , ~ ax2 , and ~ ax3 below depend only on
     Meredith's sole axiom and not accidentally on a previous theorem above.
     Outside of this section, we will not make use of this axiom.  (Contributed
     by NM, 14-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  ax-meredith $a |- ( ( ( ( ( ph -> ps ) -> ( -. ch -> -. th ) ) -> ch ) ->
       ta ) -> ( ( ta -> ph ) -> ( th -> ph ) ) ) $.

  $( Step 3 of Meredith's proof of Lukasiewicz axioms from his sole axiom.
     (The step numbers refer to Meredith's original paper.)  (Contributed by
     NM, 14-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  merlem1 $p |- ( ( ( ch -> ( -. ph -> ps ) ) -> ta ) -> ( ph -> ta ) ) $=
    ( wn wi ax-meredith ax-mp ) DAEZFIBFZEZIFFZJFCJFZFZMDFADFFJDECEFZEKEFZFOFDF
    LFNIBOKDGJPDCLGHDIJAMGH $.

  $( Step 4 of Meredith's proof of Lukasiewicz axioms from his sole axiom.
     (Contributed by NM, 14-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  merlem2 $p |- ( ( ( ph -> ph ) -> ch ) -> ( th -> ch ) ) $=
    ( wi wn merlem1 ax-meredith ax-mp ) BBDZAECEZDDADAADZDKBDCBDDAJIAFBBACKGH
    $.

  $( Step 7 of Meredith's proof of Lukasiewicz axioms from his sole axiom.
     (Contributed by NM, 14-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  merlem3 $p |- ( ( ( ps -> ch ) -> ph ) -> ( ch -> ph ) ) $=
    ( wi wn merlem2 ax-mp ax-meredith ) AADZCEZJDZDZCDBCDZDZMADCADZDOBEZPDDBDZL
    DZNKKDLDRJKIFKLQFGCABBLHGAACCMHG $.

  $( Step 8 of Meredith's proof of Lukasiewicz axioms from his sole axiom.
     (Contributed by NM, 14-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  merlem4 $p |- ( ta -> ( ( ta -> ph ) -> ( th -> ph ) ) ) $=
    ( wi wn ax-meredith merlem3 ax-mp ) AADBEZIDDBDZCDCADBADDZDCKDAABBCFKJCGH
    $.

  $( Step 11 of Meredith's proof of Lukasiewicz axioms from his sole axiom.
     (Contributed by NM, 14-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  merlem5 $p |- ( ( ph -> ps ) -> ( -. -. ph -> ps ) ) $=
    ( wi wn ax-meredith merlem1 merlem4 ax-mp ) BBCZBDZJCCBCBCIICCZABCZADZDZBCC
    ZBBBBBEIJNDCCBCZACZOCZKOCZBBBNAEOKDZCMTCCZACQCZRSCUAUBMBLTFAPUAGHOTAKQEHHH
    $.

  $( Step 12 of Meredith's proof of Lukasiewicz axioms from his sole axiom.
     (Contributed by NM, 14-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  merlem6 $p |- ( ch -> ( ( ( ps -> ch ) -> ph ) -> ( th -> ph ) ) ) $=
    ( wi merlem4 merlem3 ax-mp ) BCEZIAEDAEEZECJEADIFJBCGH $.

  $( Between steps 14 and 15 of Meredith's proof of Lukasiewicz axioms from his
     sole axiom.  (Contributed by NM, 22-Dec-2002.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  merlem7 $p |- ( ph -> ( ( ( ps -> ch ) -> th ) -> ( ( ( ch -> ta ) ->
                  ( -. th -> -. ps ) ) -> th ) ) ) $=
    ( wi wn merlem4 merlem6 ax-meredith ax-mp ) BCFZLDFZCEFDGBGFFZDFZFZFZAPFZDN
    LHPAGZFCGZSFFZCFLFZQRFOUAFUBSMOTICEDBUAJKPSCALJKK $.

  $( Step 15 of Meredith's proof of Lukasiewicz axioms from his sole axiom.
     (Contributed by NM, 22-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  merlem8 $p |- ( ( ( ps -> ch ) -> th ) -> ( ( ( ch -> ta ) ->
                  ( -. th -> -. ps ) ) -> th ) ) $=
    ( wph wi wn ax-meredith merlem7 ax-mp ) EEFZEGZLFFEFEFKKFFZABFCFBDFCGAGFFCF
    FEEEEEHMABCDIJ $.

  $( Step 18 of Meredith's proof of Lukasiewicz axioms from his sole axiom.
     (Contributed by NM, 22-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  merlem9 $p |- ( ( ( ph -> ps ) -> ( ch -> ( th -> ( ps -> ta ) ) ) ) ->
                    ( et -> ( ch -> ( th -> ( ps -> ta ) ) ) ) ) $=
    ( wi wn merlem6 merlem8 ax-mp ax-meredith ) CDBEGZGZGZFHZGBHZPGGZBGABGZGZSO
    GFOGGMRHDHGZHAHGZGUAGRGZTNRGUCPCNQIDMRUBJKBEUAARLKOPBFSLK $.

  $( Step 19 of Meredith's proof of Lukasiewicz axioms from his sole axiom.
     (Contributed by NM, 14-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  merlem10 $p |- ( ( ph -> ( ph -> ps ) ) -> ( th -> ( ph -> ps ) ) ) $=
    ( wi wn ax-meredith merlem9 ax-mp ) AADZAEZJDDADADIIDDZAABDZDZCLDDZAAAAAFLA
    DJCEDDADZADNDKNDLAACAFOAMCBKGHH $.

  $( Step 20 of Meredith's proof of Lukasiewicz axioms from his sole axiom.
     (Contributed by NM, 14-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  merlem11 $p |- ( ( ph -> ( ph -> ps ) ) -> ( ph -> ps ) ) $=
    ( wi wn ax-meredith merlem10 ax-mp ) AACZADZICCACACHHCCZAABCZCZKCZAAAAAELMC
    JMCABLFLKJFGG $.

  $( Step 28 of Meredith's proof of Lukasiewicz axioms from his sole axiom.
     (Contributed by NM, 14-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  merlem12 $p |- ( ( ( th -> ( -. -. ch -> ch ) ) -> ph ) -> ph ) $=
    ( wn wi merlem5 merlem2 ax-mp merlem4 merlem11 ) CBDDBEZEZAEZMAEZEZNLOBBEKE
    LBBFBKCGHAMLIHMAJH $.

  $( Step 35 of Meredith's proof of Lukasiewicz axioms from his sole axiom.
     (Contributed by NM, 14-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  merlem13 $p |- ( ( ph -> ps ) ->
              ( ( ( th -> ( -. -. ch -> ch ) ) -> -. -. ph ) -> ps ) ) $=
    ( wi wn merlem12 merlem5 ax-mp merlem6 ax-meredith merlem11 ) BBEZAFZDCFFCE
    EZNFZEZFZEZEAEZAEZABEQBEETUAEZUASUBOREZREZSRCDGRBEZRFPEZEREUCEZUDSEUFUGQPEU
    FPCDGQPHIRUEUFOJIRBRNUCKIIAMSTJITALIBBAQAKI $.

  $( 1 of 3 axioms for propositional calculus due to Lukasiewicz, derived from
     Meredith's sole axiom.  (Contributed by NM, 14-Dec-2002.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  luk-1 $p |- ( ( ph -> ps ) -> ( ( ps -> ch ) -> ( ph -> ch ) ) ) $=
    ( wi wn ax-meredith merlem13 ax-mp ) CCDZAEZEZEJDDKDBDZBCDACDDZDZABDZMDZCCK
    ABFMADZOEZEZERDDSDLDZNPDOLDTABJIGOLRQGHMASOLFHH $.

  $( 2 of 3 axioms for propositional calculus due to Lukasiewicz, derived from
     Meredith's sole axiom.  (Contributed by NM, 14-Dec-2002.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  luk-2 $p |- ( ( -. ph -> ph ) -> ph ) $=
    ( wn wi merlem5 merlem4 ax-mp merlem11 ax-meredith ) ABZACZJACZCZKAJBZCIBMC
    CZICZICZLOPCZPNQAMDIONEFOIGFAMIJIHFJAGF $.

  $( 3 of 3 axioms for propositional calculus due to Lukasiewicz, derived from
     Meredith's sole axiom.  (Contributed by NM, 14-Dec-2002.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  luk-3 $p |- ( ph -> ( -. ph -> ps ) ) $=
    ( wn wi merlem11 merlem1 ax-mp ) ACZHBDZDIDAIDHBEABHIFG $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
      Derive the standard axioms from the Lukasiewicz axioms
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    luklem1.1 $e |- ( ph -> ps ) $.
    luklem1.2 $e |- ( ps -> ch ) $.
    $( Used to rederive standard propositional axioms from Lukasiewicz'.
       (Contributed by NM, 23-Dec-2002.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    luklem1 $p |- ( ph -> ch ) $=
      ( wi luk-1 ax-mp ) BCFZACFZEABFIJFDABCGHH $.
  $}

  $( Used to rederive standard propositional axioms from Lukasiewicz'.
     (Contributed by NM, 22-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  luklem2 $p |- ( ( ph -> -. ps ) ->
                ( ( ( ph -> ch ) -> th ) -> ( ps -> th ) ) ) $=
    ( wn wi luk-1 luk-3 ax-mp luklem1 ) ABEZFZBACFZFZMDFBDFFLKCFZMFZNAKCGBOFPNF
    BCHBOMGIJBMDGJ $.

  $( Used to rederive standard propositional axioms from Lukasiewicz'.
     (Contributed by NM, 22-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  luklem3 $p |- ( ph -> ( ( ( -. ph -> ps ) -> ch ) -> ( th -> ch ) ) ) $=
    ( wn wi luk-3 luklem2 luklem1 ) AAEZDEZFJBFCFDCFFAKGJDBCHI $.

  $( Used to rederive standard propositional axioms from Lukasiewicz'.
     (Contributed by NM, 22-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  luklem4 $p |- ( ( ( ( -. ph -> ph ) -> ph ) -> ps ) -> ps ) $=
    ( wn wi luk-2 luklem3 ax-mp luk-1 luklem1 ) ACADADZBDZBCZBDZBLJDZKMDJCJDJDZ
    NJEJONDAEJJJLFGGLJBHGBEI $.

  $( Used to rederive standard propositional axioms from Lukasiewicz'.
     (Contributed by NM, 22-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  luklem5 $p |- ( ph -> ( ps -> ph ) ) $=
    ( wn wi luklem3 luklem4 luklem1 ) AACADADBADZDHAAABEAHFG $.

  $( Used to rederive standard propositional axioms from Lukasiewicz'.
     (Contributed by NM, 22-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  luklem6 $p |- ( ( ph -> ( ph -> ps ) ) -> ( ph -> ps ) ) $=
    ( wi luk-1 wn luklem5 luklem2 luklem4 luklem1 ax-mp ) AABCZCKBCZKCZKAKBDKEZ
    KCZKCMKCZCZPMOCZQNLCRNBEZNCZLNSFTSBCBCLCLSKBBGBLHIINLKDJMOKDJKPHJI $.

  $( Used to rederive standard propositional axioms from Lukasiewicz'.
     (Contributed by NM, 22-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  luklem7 $p |- ( ( ph -> ( ps -> ch ) ) -> ( ps -> ( ph -> ch ) ) ) $=
    ( wi luk-1 luklem5 luklem1 luklem6 ax-mp ) ABCDZDJCDZACDZDZBLDZAJCEBKDMNDBJ
    KDZKBJBDOBJFJBCEGJCHGBKLEIG $.

  $( Used to rederive standard propositional axioms from Lukasiewicz'.
     (Contributed by NM, 22-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  luklem8 $p |- ( ( ph -> ps ) -> ( ( ch -> ph ) -> ( ch -> ps ) ) ) $=
    ( wi luk-1 luklem7 ax-mp ) CADZABDZCBDZDDIHJDDCABEHIJFG $.

  $( Standard propositional axiom derived from Lukasiewicz axioms.
     (Contributed by NM, 22-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  ax1 $p |- ( ph -> ( ps -> ph ) ) $=
    ( luklem5 ) ABC $.

  $( Standard propositional axiom derived from Lukasiewicz axioms.
     (Contributed by NM, 22-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  ax2 $p |- ( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) ) ) $=
    ( wi luklem7 luklem8 luklem6 ax-mp luklem1 ) ABCDDBACDZDZABDZJDZABCEKLAJDZD
    ZMBJAFNJDOMDACGNJLFHII $.

  $( Standard propositional axiom derived from Lukasiewicz axioms.
     (Contributed by NM, 22-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  ax3 $p |- ( ( -. ph -> -. ps ) -> ( ps -> ph ) ) $=
    ( wn wi luklem2 luklem4 luklem1 ) ACZBCDHADADBADZDIHBAAEAIFG $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
           Derive Nicod's axiom from the standard axioms
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

Prove Nicod's axiom and implication and negation definitions.

$)

  $( Define implication in terms of 'nand'.  Analogous to
     ` ( ( ph -/\ ( ps -/\ ps ) ) <-> ( ph -> ps ) ) ` .  In a pure
     (standalone) treatment of Nicod's axiom, this theorem would be changed to
     a definition ($a statement).  (Contributed by NM, 11-Dec-2008.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  nic-dfim $p |- ( ( ( ph -/\ ( ps -/\ ps ) ) -/\ ( ph -> ps ) ) -/\
                   ( ( ( ph -/\ ( ps -/\ ps ) ) -/\ ( ph -/\ ( ps -/\ ps ) ) )
                          -/\
                     ( ( ph -> ps ) -/\ ( ph -> ps ) ) ) ) $=
    ( wnan wi wb nanim bicomi nanbi mpbi ) ABBCCZABDZEJKCJJCKKCCCKJABFGJKHI $.

  $( Define negation in terms of 'nand'.  Analogous to
     ` ( ( ph -/\ ph ) <-> -. ph ) ` .  In a pure (standalone) treatment of
     Nicod's axiom, this theorem would be changed to a definition ($a
     statement).  (Contributed by NM, 11-Dec-2008.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  nic-dfneg $p |- ( ( ( ph -/\ ph ) -/\ -. ph ) -/\
                    ( ( ( ph -/\ ph ) -/\ ( ph -/\ ph ) ) -/\
                      ( -. ph -/\ -. ph ) ) ) $=
    ( wnan wn wb nannot bicomi nanbi mpbi ) AABZACZDIJBIIBJJBBBJIAEFIJGH $.

  ${
    $( Minor premise. $)
    nic-jmin $e |- ph $.
    $( Major premise. $)
    nic-jmaj $e |- ( ph -/\ ( ch -/\ ps ) ) $.
    $( Derive Nicod's rule of modus ponens using 'nand', from the standard
       one.  Although the major and minor premise together also imply ` ch ` ,
       this form is necessary for useful derivations from ~ nic-ax .  In a pure
       (standalone) treatment of Nicod's axiom, this theorem would be changed
       to an axiom ($a statement).  (Contributed by Jeff Hoffman,
       19-Nov-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    nic-mp $p |- ps $=
      ( wnan wa wi nannan mpbi simprd ax-mp ) ABDACBACBFFACBGHEABCIJKL $.

    $( A direct proof of ~ nic-mp .  (Contributed by NM, 30-Dec-2008.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    nic-mpALT $p |- ps $=
      ( wa wi wn wnan df-nan anbi2i xchbinx mpbi iman mpbir simprd ax-mp ) ABDA
      CBACBFZGARHZFZHZACBIZIZUAEUCAUBFTAUBJUBSACBJKLMARNOPQ $.
  $}

  $( Nicod's axiom derived from the standard ones.  See _Intro. to Math.
     Phil._ by B. Russell, p. 152.  Like ~ meredith , the usual axioms can be
     derived from this and vice versa.  Unlike ~ meredith , Nicod uses a
     different connective ('nand'), so another form of modus ponens must be
     used in proofs, e.g. ` { ` ~ nic-ax , ~ nic-mp ` } ` is equivalent to
     ` { ` ~ luk-1 , ~ luk-2 , ~ luk-3 , ~ ax-mp ` } ` .  In a pure
     (standalone) treatment of Nicod's axiom, this theorem would be changed to
     an axiom ($a statement).  (Contributed by Jeff Hoffman, 19-Nov-2007.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  nic-ax $p |- ( ( ph -/\ ( ch -/\ ps ) ) -/\
                   ( ( ta -/\ ( ta -/\ ta ) ) -/\
                     ( ( th -/\ ch ) -/\
                       ( ( ph -/\ th ) -/\ ( ph -/\ th ) ) ) ) ) $=
    ( wnan wa wi nannan biimpi simpl imim2i wn imnan df-nan bitr4i imim2d con2b
    con3 mpbir 3bitr4ri syl6ibr syl5bir nanim sylib 3syl pm4.24 jctil ) ACBFFZE
    EEFFZDCFZADFZULFFZFFUIUJUMGHUIUMUJUIACBGZHZACHZUMUIUOABCIJUNCACBKLUPUKULHUM
    UKDCMZHZUPULURDCGMUKDCNDCOPUPURDAMZHZULUPUQUSDACSQADMHADGMUTULADNDARADOUAUB
    UCUKULUDUEUFUJEEEGZHEVAEUGJEEEITUHUIUMUJIT $.

  $( A direct proof of ~ nic-ax .  (Contributed by NM, 11-Dec-2008.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  nic-axALT $p |- ( ( ph -/\ ( ch -/\ ps ) ) -/\ ( ( ta -/\ ( ta -/\ ta ) )
          -/\ ( ( th -/\ ch ) -/\ ( ( ph -/\ th ) -/\ ( ph -/\ th ) ) ) ) ) $=
    ( wnan wa wn anidm df-nan anbi2i notbii iman 3bitr4i bitr4i xchbinx anbi12i
    wi imnan mpbir simpl imim2i con3 imim2d biimpri jctil con2b bitr3i 3bitri
    syl ) ACBFZFZEEEFZFZDCFZADFZUPFZFZFZFULUSGZHZVAACBGZRZEEEGZRZDCHZRZDAHZRZRZ
    GZRZVCVJVEVCACRZVJVBCACBUAUBVMVFVHDACUCUDUJVDEEIUEUFVAVCVKHZGZHVLUTVOULVCUS
    VNAUKGZHAVBHZGZHULVCVPVRUKVQACBJKLAUKJAVBMNUSUNURGVKUNURJUNVEURVJEUMGZHEVDH
    ZGZHUNVEVSWAUMVTEEEJKLEUMJEVDMNUOUQGZHVGVIHZGZHURVJWBWDUOVGUQWCUODCGHVGDCJD
    CSOUQUPUPGZVIUPUPJWEUPADGHZVIUPIADJWFADHRVIADSADUGUHUIPQLUOUQJVGVIMNQPQLVCV
    KMOTULUSJT $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
          Derive the Lukasiewicz axioms from Nicod's axiom
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $( Minor premise. $)
    nic-imp.1 $e |- ( ph -/\ ( ch -/\ ps ) ) $.
    $( Inference for ~ nic-mp using ~ nic-ax as major premise.  (Contributed by
       Jeff Hoffman, 17-Nov-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    nic-imp $p |- ( ( th -/\ ch ) -/\ ( ( ph -/\ th ) -/\ ( ph -/\ th ) ) ) $=
      ( wta wnan nic-ax nic-mp ) ACBGGDCGADGZJGGFFFGGEABCDFHI $.
  $}

  $( Lemma for ~ nic-id .  (Contributed by Jeff Hoffman, 17-Nov-2007.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  nic-idlem1 $p |- ( ( th -/\ ( ta -/\ ( ta -/\ ta ) ) ) -/\
                 ( ( ( ph -/\ ( ch -/\ ps ) ) -/\ th ) -/\
                   ( ( ph -/\ ( ch -/\ ps ) ) -/\ th ) ) ) $=
    ( wnan nic-ax nic-imp ) ACBFFACFAAFZIFFEEEFFDABCAEGH $.

  ${
    nic-idlem2.1 $e |- ( et -/\ ( ( ph -/\ ( ch -/\ ps ) ) -/\ th ) ) $.
    $( Lemma for ~ nic-id .  Inference used by ~ nic-id .  (Contributed by Jeff
       Hoffman, 17-Nov-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    nic-idlem2 $p |- ( ( th -/\ ( ta -/\ ( ta -/\ ta ) ) ) -/\ et ) $=
      ( wnan nic-ax nic-imp nic-mp ) FACBHHZDHZHDEEEHHZHZFHZPGOMMFLACHAAHZQHHND
      ABCAEIJJK $.
  $}

  $( Theorem ~ id expressed with ` -/\ ` .  (Contributed by Jeff Hoffman,
     17-Nov-2007.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  nic-id $p |- ( ta -/\ ( ta -/\ ta ) ) $=
    ( wph wps wch wth wnan nic-ax nic-idlem2 nic-idlem1 nic-mp ) BCFZCBFZLFFZDD
    DFZFZFZCCCFFZFAAAFFZOEEEMDQCCCBEGHMNDPCORFKLLOAIHJ $.

  $( ` -/\ ` is symmetric.  (Contributed by Jeff Hoffman, 17-Nov-2007.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  nic-swap $p |- ( ( th -/\ ph ) -/\ ( ( ph -/\ th ) -/\ ( ph -/\ th ) ) ) $=
    ( wta wnan nic-id nic-ax nic-mp ) AAADDBADABDZHDDCCCDDAEAAABCFG $.

  ${
    nic-isw1.1 $e |- ( th -/\ ph ) $.
    $( Inference version of ~ nic-swap .  (Contributed by Jeff Hoffman,
       17-Nov-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    nic-isw1 $p |- ( ph -/\ th ) $=
      ( wnan nic-swap nic-mp ) BADABDZGCABEF $.
  $}

  ${
    nic-isw2.1 $e |- ( ps -/\ ( th -/\ ph ) ) $.
    $( Inference for swapping nested terms.  (Contributed by Jeff Hoffman,
       17-Nov-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    nic-isw2 $p |- ( ps -/\ ( ph -/\ th ) ) $=
      ( wnan nic-swap nic-imp nic-mp nic-isw1 ) BACEZBCAEZEJBEZLDJKKBCAFGHI $.
  $}

  ${
    nic-iimp1.1 $e |- ( ph -/\ ( ch -/\ ps ) ) $.
    nic-iimp1.2 $e |- ( th -/\ ch ) $.
    $( Inference version of ~ nic-imp using right-handed term.  (Contributed by
       Jeff Hoffman, 17-Nov-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    nic-iimp1 $p |- ( th -/\ ph ) $=
      ( wnan nic-imp nic-mp nic-isw1 ) DADCGADGZKFABCDEHIJ $.
  $}

  ${
    nic-iimp2.1 $e |- ( ( ph -/\ ps ) -/\ ( ch -/\ ch ) ) $.
    nic-iimp2.2 $e |- ( th -/\ ph ) $.
    $( Inference version of ~ nic-imp using left-handed term.  (Contributed by
       Jeff Hoffman, 17-Nov-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    nic-iimp2 $p |- ( th -/\ ( ch -/\ ch ) ) $=
      ( wnan nic-isw1 nic-iimp1 ) CCGZBADJABGEHFI $.
  $}

  ${
    nic-idel.1 $e |- ( ph -/\ ( ch -/\ ps ) ) $.
    $( Inference to remove the trailing term.  (Contributed by Jeff Hoffman,
       17-Nov-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    nic-idel $p |- ( ph -/\ ( ch -/\ ch ) ) $=
      ( wnan nic-id nic-isw1 nic-imp nic-mp ) CCEZCEAJEZKJCCFGABCJDHI $.
  $}

  ${
    nic-ich.1 $e |- ( ph -/\ ( ps -/\ ps ) ) $.
    nic-ich.2 $e |- ( ps -/\ ( ch -/\ ch ) ) $.
    $( Chained inference.  (Contributed by Jeff Hoffman, 17-Nov-2007.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    nic-ich $p |- ( ph -/\ ( ch -/\ ch ) ) $=
      ( wnan nic-isw1 nic-imp nic-mp ) CCFZBFAJFZKJBEGABBJDHI $.
  $}

  ${
    nic-idbl.1 $e |- ( ph -/\ ( ps -/\ ps ) ) $.
    $( Double the terms.  Since doubling is the same as negation, this can be
       viewed as a contraposition inference.  (Contributed by Jeff Hoffman,
       17-Nov-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    nic-idbl $p |- ( ( ps -/\ ps ) -/\ ( ( ph -/\ ph ) -/\ ( ph -/\ ph ) ) ) $=
      ( wnan nic-imp nic-ich ) BBDABDAADABBBCEABBACEF $.
  $}

$( (not in Table of Contents)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Biconditional justification from Nicod's axiom
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( For nic-* definitions, the biconditional connective is not used.  Instead,
     definitions are made based on this form. ~ nic-bi1 and ~ nic-bi2 are used
     to convert the definitions into usable theorems about one side of the
     implication.  (Contributed by Jeff Hoffman, 18-Nov-2007.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  nic-bijust $p |- ( ( ta -/\ ta ) -/\ ( ( ta -/\ ta ) -/\ ( ta -/\ ta ) ) ) $=
    ( nic-swap ) AAB $.

  ${
    $( 'Biconditional' premise. $)
    nic-bi1.1 $e |- ( ( ph -/\ ps ) -/\ ( ( ph -/\ ph )
         -/\ ( ps -/\ ps ) ) ) $.
    $( Inference to extract one side of an implication from a definition.
       (Contributed by Jeff Hoffman, 18-Nov-2007.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    nic-bi1 $p |- ( ph -/\ ( ps -/\ ps ) ) $=
      ( wnan nic-id nic-iimp1 nic-isw2 nic-idel ) AABBAAABDBBDAADACAEFGH $.
  $}

  ${
    $( 'Biconditional' premise.  $)
    nic-bi2.1 $e |- ( ( ph -/\ ps ) -/\ ( ( ph -/\ ph )
         -/\ ( ps -/\ ps ) ) ) $.
    $( Inference to extract the other side of an implication from a
       'biconditional' definition.  (Contributed by Jeff Hoffman,
       18-Nov-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    nic-bi2 $p |- ( ps -/\ ( ph -/\ ph ) ) $=
      ( wnan nic-isw2 nic-id nic-iimp1 nic-idel ) BBAABDZAADZBBDZBKIJCEBFGH $.
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
       Hoffman, 18-Nov-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    nic-stdmp $p |- ps $=
      ( wi wnan nic-dfim nic-bi2 nic-mp ) ABBCABEZABBFFZKDKJABGHII $.
  $}

  $( Proof of ~ luk-1 from ~ nic-ax and ~ nic-mp (and definitions ~ nic-dfim
     and ~ nic-dfneg ).  Note that the standard axioms ~ ax-1 , ~ ax-2 , and
     ~ ax-3 are proved from the Lukasiewicz axioms by theorems ~ ax1 , ~ ax2 ,
     and ~ ax3 .  (Contributed by Jeff Hoffman, 18-Nov-2007.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  nic-luk1 $p |- ( ( ph -> ps ) -> ( ( ps -> ch ) -> ( ph -> ch ) ) ) $=
    ( wta wi nic-dfim nic-bi2 nic-ax nic-isw2 nic-idel nic-bi1 nic-idbl nic-imp
    wnan nic-swap nic-ich nic-mp ) ABEZBCEZACEZEZUANNZRUAEZUCRABBNNZUAUDRABFGUD
    STTNZNZUAUDCCNZBNZAUGNZUINZNZUFUDDDDNNZUKUKUDULABBUGDHIJUKUEUHNUFUEUJUJUHUI
    TUITACFKLMSUHUHUESBUGNZUHUMSBCFGUGBOPMPPUFUASTFKPPUBUCRUAFKQ $.

  $( Proof of ~ luk-2 from ~ nic-ax and ~ nic-mp .  (Contributed by Jeff
     Hoffman, 18-Nov-2007.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  nic-luk2 $p |- ( ( -. ph -> ph ) -> ph ) $=
    ( wn wi wnan nic-dfim nic-bi2 nic-dfneg nic-iimp1 nic-isw2 nic-isw1 nic-bi1
    nic-id nic-mp ) ABZACZAADZDZOACZROPONPDZSPSONAEFNPPPNDNNDPPDPAGPLHIHJQROAEK
    M $.

  $( Proof of ~ luk-3 from ~ nic-ax and ~ nic-mp .  (Contributed by Jeff
     Hoffman, 18-Nov-2007.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  nic-luk3 $p |- ( ph -> ( -. ph -> ps ) ) $=
    ( wnan nic-dfim nic-bi1 nic-dfneg nic-bi2 nic-id nic-iimp1 nic-iimp2 nic-mp
    wn wi ) AALZBMZOCCZAOMZQNBBCZOANRCONBDENAACZSASNAFGAHIJPQAODEK $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Derive Nicod's Axiom from Lukasiewicz's First Sheffer Stroke Axiom
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( This alternative axiom for propositional calculus using the Sheffer Stroke
     was offered by Lukasiewicz in his Selected Works.  It improves on Nicod's
     axiom by reducing its number of variables by one.

     This axiom also uses ~ nic-mp for its constructions.

     Here, the axiom is proved as a substitution instance of ~ nic-ax .
     (Contributed by Anthony Hart, 31-Jul-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  lukshef-ax1 $p |- ( ( ph -/\ ( ch -/\ ps ) ) -/\ ( ( th -/\ ( th -/\ th ) )
          -/\ ( ( th -/\ ch ) -/\ ( ( ph -/\ th ) -/\ ( ph -/\ th ) ) ) ) ) $=
    ( nic-ax ) ABCDDE $.

  $( Lemma for ~ renicax .  (Contributed by NM, 31-Jul-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  lukshefth1 $p |- ( ( ( ( ta -/\ ps ) -/\ ( ( ph -/\ ta ) -/\ ( ph
          -/\ ta ) ) ) -/\ ( th -/\ ( th -/\ th ) ) ) -/\ ( ph -/\ ( ps
          -/\ ch ) ) ) $=
    ( wnan lukshef-ax1 nic-mp ) ABCFFZEEEFFZEBFAEFZKFFZFZFZLDDDFFZFZIFZQACBEGPM
    MFFZNQQFFIIIFFJODEFEDFZSFFZFFRLLLFFEEEDGJTOLGHPMMIGHH $.

  $( Lemma for ~ renicax .  (Contributed by NM, 31-Jul-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  lukshefth2 $p |- ( ( ta -/\ th ) -/\ ( ( th -/\ ta ) -/\ ( th
          -/\ ta ) ) ) $=
    ( wps wch wph wnan lukshef-ax1 nic-mp lukshefth1 ) AAAFFZBAFABFZKFFBBBFFAJF
    ZCDEFFZAFZNFFZJBEFEBFZPFFZMJADFCAFZRFFZFFOJCEDAGMSJAGHQJFZEEEFFZFZOTFZUCEEE
    ABIOUAENFLEFZUDFFZFFUBUCUCFFTTTFFLNNEGOUEUATGHHHAAABGH $.

  $( A rederivation of ~ nic-ax from ~ lukshef-ax1 , proving that ~ lukshef-ax1
     with ~ nic-mp can be used as a complete axiomatization of propositional
     calculus.  (Contributed by Anthony Hart, 31-Jul-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  renicax $p |- ( ( ph -/\ ( ch -/\ ps ) ) -/\ ( ( ta -/\ ( ta -/\ ta ) )
          -/\ ( ( th -/\ ch ) -/\ ( ( ph -/\ th ) -/\ ( ph -/\ th ) ) ) ) ) $=
    ( wnan lukshefth1 lukshefth2 nic-mp lukshef-ax1 ) EEEFFZDCFADFZLFFZFZACBFFZ
    FZONFZQOMKFZFZPPROFSSACBEDGORHINRRFFSPPFFOOOFFMKHNRROJIIONHI $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
      Derive the Lukasiewicz Axioms from the Tarski-Bernays-Wajsberg Axioms
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Justification for ~ tbw-negdf .  (Contributed by Anthony Hart,
     15-Aug-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  tbw-bijust $p |- ( ( ph <-> ps ) <-> ( ( ( ph -> ps )
    -> ( ( ps -> ph ) -> F. ) ) -> F. ) ) $=
    ( wb wi wn wfal dfbi1 pm2.21 imim2i falim impbii notbii ax-1 pm2.43i 3bitri
    id ja ) ABCABDZBADZEZDZERSFDZDZEZUCFDZABGUAUCUAUCTUBRSFHIUBTRSFTTPTJQIKLUDU
    EUCFHUEUDUCFUEUDDZUDUEMUFJQNKO $.

  $( The definition of negation, in terms of ` -> ` and ` F. ` .  (Contributed
     by Anthony Hart, 15-Aug-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  tbw-negdf $p |- ( ( ( -. ph -> ( ph -> F. ) )
    -> ( ( ( ph -> F. ) -> -. ph ) -> F. ) ) -> F. ) $=
    ( wn wfal wi wb pm2.21 ax-1 falim ja pm2.43i impbii tbw-bijust mpbi ) ABZAC
    DZENODONDZCDDCDNOACFONACPNOGPHIJKNOLM $.

  $( The first of four axioms in the Tarski-Bernays-Wajsberg system.
     (Contributed by Anthony Hart, 13-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  tbw-ax1 $p |- ( ( ph -> ps ) -> ( ( ps -> ch ) -> ( ph -> ch ) ) ) $=
    ( imim1 ) ABCD $.

  $( The second of four axioms in the Tarski-Bernays-Wajsberg system.
     (Contributed by Anthony Hart, 13-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  tbw-ax2 $p |- ( ph -> ( ps -> ph ) ) $=
    ( ax-1 ) ABC $.

  $( The third of four axioms in the Tarski-Bernays-Wajsberg system.
     (Contributed by Anthony Hart, 13-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  tbw-ax3 $p |- ( ( ( ph -> ps ) -> ph ) -> ph ) $=
    ( peirce ) ABC $.

  $( The fourth of four axioms in the Tarski-Bernays-Wajsberg system.

     This axiom was added to the Tarski-Bernays axiom system ( see ~ tb-ax1 ,
     ~ tb-ax2 , and ~ tb-ax3 ) by Wajsberg for completeness.  (Contributed by
     Anthony Hart, 13-Aug-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  tbw-ax4 $p |- ( F. -> ph ) $=
    ( falim ) AB $.

  ${
    tbwsyl.1 $e |- ( ph -> ps ) $.
    tbwsyl.2 $e |- ( ps -> ch ) $.
    $( Used to rederive the Lukasiewicz axioms from Tarski-Bernays-Wajsberg'.
       (Contributed by Anthony Hart, 16-Aug-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    tbwsyl $p |- ( ph -> ch ) $=
      ( wi tbw-ax1 ax-mp ) BCFZACFZEABFIJFDABCGHH $.
  $}

  $( Used to rederive the Lukasiewicz axioms from Tarski-Bernays-Wajsberg'.
     (Contributed by Anthony Hart, 16-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  tbwlem1 $p |- ( ( ph -> ( ps -> ch ) ) -> ( ps -> ( ph -> ch ) ) ) $=
    ( wi tbw-ax2 tbw-ax1 tbwsyl tbw-ax3 mpsyl ) BBCDZCDZDAJDKACDZDBLDBJKDZKBJBD
    MBJEJBCFGMKCDKDKJKCFKCHGGAJCFBKLFI $.

  $( Used to rederive the Lukasiewicz axioms from Tarski-Bernays-Wajsberg'.
     (Contributed by Anthony Hart, 16-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  tbwlem2 $p |- ( ( ph -> ( ps -> F. ) ) -> ( ( ( ph -> ch ) -> th )
    -> ( ps -> th ) ) ) $=
    ( wfal wi tbw-ax4 tbw-ax1 tbwlem1 ax-mp mpsyl tbwsyl ) ABEFZFZBACFZFZODFBDF
    FBMCFZFZNQOFPMBCFZFZRECFZTCGMUASFFUATFBECHMUASIJJMBCIJAMCHBQOHKBODHL $.

  $( Used to rederive the Lukasiewicz axioms from Tarski-Bernays-Wajsberg'.
     (Contributed by Anthony Hart, 16-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  tbwlem3 $p |- ( ( ( ( ( ph -> F. ) -> ph ) -> ph ) -> ps ) -> ps ) $=
    ( wfal wi tbw-ax3 tbw-ax2 tbw-ax1 tbwsyl ax-mp ) ACDADADZBDZKBDZDZLJMACEJKJ
    DMJKFKJBGHIMLBDLDLKLBGLBEHI $.

  $( Used to rederive the Lukasiewicz axioms from Tarski-Bernays-Wajsberg'.
     (Contributed by Anthony Hart, 16-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  tbwlem4 $p |- ( ( ( ph -> F. ) -> ps ) -> ( ( ps -> F. ) -> ph ) ) $=
    ( wfal wi tbw-ax4 tbw-ax1 tbwlem1 ax-mp tbwlem2 tbwlem3 tbwsyl ) ACDZBDZLBC
    DZCDZDZNADZBODZMPDZNNDZRCCDZTCENUANDDUATDBCCFNUANGHHNBCGHMRPDDRSDLBOFMRPGHH
    PLADADQDQLNAAIAQJKK $.

  $( Used to rederive the Lukasiewicz axioms from Tarski-Bernays-Wajsberg'.
     (Contributed by Anthony Hart, 16-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  tbwlem5 $p |- ( ( ( ph -> ( ps -> F. ) ) -> F. ) -> ph ) $=
    ( wfal wi tbw-ax2 tbw-ax1 tbwsyl tbwlem1 ax-mp tbwlem4 ) ACDZABCDZDZDZMCDAD
    AKLDZDNABADOABEBACFGAKLHIAMJI $.

  $( ~ luk-1 derived from the Tarski-Bernays-Wajsberg axioms.  (Contributed by
     Anthony Hart, 16-Aug-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  re1luk1 $p |- ( ( ph -> ps ) -> ( ( ps -> ch ) -> ( ph -> ch ) ) ) $=
    ( tbw-ax1 ) ABCD $.

  $( ~ luk-2 derived from the Tarski-Bernays-Wajsberg axioms.  (Contributed by
     Anthony Hart, 16-Aug-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  re1luk2 $p |- ( ( -. ph -> ph ) -> ph ) $=
    ( wn wi wfal tbw-negdf tbw-ax2 tbwlem4 ax-mp tbw-ax1 tbw-ax3 tbwsyl ) ABZAC
    ZADCZACZANLCZMOCLNCZPDCZCZDCZPAERSCTPCRQFPSGHHNLAIHADJK $.

  $( ~ luk-3 derived from the Tarski-Bernays-Wajsberg axioms.

     This theorem, along with ~ re1luk1 and ~ re1luk2 proves that ~ tbw-ax1 ,
     ~ tbw-ax2 , ~ tbw-ax3 , and ~ tbw-ax4 , with ~ ax-mp can be used as a
     complete axiom system for all of propositional calculus.  (Contributed by
     Anthony Hart, 16-Aug-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  re1luk3 $p |- ( ph -> ( -. ph -> ps ) ) $=
    ( wn wfal wi tbw-negdf tbwlem5 ax-mp tbw-ax4 tbw-ax1 tbwlem1 mpsyl ) ACZADE
    ZEZANBEZMBEONMEZDEEDEOAFOQGHNABEZEZAPEDBEZSBINTREETSEADBJNTRKHHNABKHMNBJL
    $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Derive the Tarski-Bernays-Wajsberg axioms from Meredith's First CO Axiom
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( A single axiom for propositional calculus offered by Meredith.

     This axiom is worthy of note, due to it having only 19 symbols, not
     counting parentheses.  The more well-known ~ meredith has 21 symbols, sans
     parentheses.

     See ~ merco2 for another axiom of equal length.  (Contributed by Anthony
     Hart, 13-Aug-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  merco1 $p |- ( ( ( ( ( ph -> ps ) -> ( ch -> F. ) ) -> th ) -> ta )
         -> ( ( ta -> ph ) -> ( ch -> ph ) ) ) $=
    ( wi wfal wn ax-1 falim ja imim2i imim1i meredith syl ) ABFZCGFZFZDFZEFPDHZ
    CHZFZFZDFZEFEAFCAFFUDSERUCDQUBPCGUBUATIUBJKLMMABDCENO $.

  $( Used to rederive the Tarski-Bernays-Wajsberg axioms from ~ merco1 .
     (Contributed by Anthony Hart, 17-Sep-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  merco1lem1 $p |- ( ph -> ( F. -> ch ) ) $=
    ( wfal wi merco1 ax-mp ) AACADZDZDZACBDZDZHGDZHDZIGCDACDZDZGDHDZMGNDZNDZGDO
    DPCAANGEGNAGOEFGCAGHEFHCDZNDZGDLDZMIDQSDHDTDUACAASHEGNHHTEFHCAGLEFFHJDZKDZI
    KDZJCDNDZGDHDZUCRJDUEDUFCAANJEGNAJUEEFJCAGHEFKCDICDZDZJDUBDZUCUDDJUGDSDKDUH
    DUICBISKEJUGHKUHEFKCIJUBEFFF $.

  $( ~ tbw-ax4 rederived from ~ merco1 .  (Contributed by Anthony Hart,
     17-Sep-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  retbwax4 $p |- ( F. -> ph ) $=
    ( wfal wi merco1lem1 ax-mp ) ABACZCZFAADGADE $.

  $( ~ tbw-ax2 rederived from ~ merco1 .  (Contributed by Anthony Hart,
     17-Sep-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  retbwax2 $p |- ( ph -> ( ps -> ph ) ) $=
    ( wi wfal merco1lem1 merco1 ax-mp ) AAAACZCZCZABACZCZDACZHCZICZJHACADCZCACZ
    MCOQAEHAAAMFGIPCPCDCNCOJCAHAPDFIPADNFGGMKCZLCZJLCZKACPCACZMCSUAAEKAAAMFGLBD
    CZCJDCZCDCRCSTCAKBUCDFLUBJDRFGGG $.

  $( Used to rederive the Tarski-Bernays-Wajsberg axioms from ~ merco1 .
     (Contributed by Anthony Hart, 17-Sep-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  merco1lem2 $p |- ( ( ( ph -> ps ) -> ch ) -> ( ( ( ps -> ta ) -> ( ph ->
    F. ) ) -> ch ) ) $=
    ( wi wfal retbwax2 merco1 ax-mp ) CAEZBDEAFEEZFEZEZBEABEZEZNCEKCEELMEOLJGBD
    AFMHICAKBNHI $.

  $( Used to rederive the Tarski-Bernays-Wajsberg axioms from ~ merco1 .
     (Contributed by Anthony Hart, 17-Sep-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  merco1lem3 $p |- ( ( ( ph -> ps ) -> ( ch -> F. ) ) -> ( ch -> ph ) ) $=
    ( wi wfal merco1lem2 retbwax2 ax-mp ) AAADZAEDDZIDZDZABDCEDDZCADZDZIEDJEDDZ
    LAAEAFKLDPLDKAGJILEFHHNEDMEDDZLODZCAEBFORDQRDOLGMNREFHHH $.

  $( Used to rederive the Tarski-Bernays-Wajsberg axioms from ~ merco1 .
     (Contributed by Anthony Hart, 17-Sep-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  merco1lem4 $p |- ( ( ( ph -> ps ) -> ch ) -> ( ps -> ch ) ) $=
    ( wi wfal merco1lem3 merco1 ax-mp ) CADZBEDZDZBDABDZDZLCDBCDDJAEDZDIEDZDKDM
    JNIFBEAOKGHCABBLGH $.

  $( Used to rederive the Tarski-Bernays-Wajsberg axioms from ~ merco1 .
     (Contributed by Anthony Hart, 17-Sep-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  merco1lem5 $p |- ( ( ( ( ph -> F. ) -> ch ) -> ta ) -> ( ph -> ta ) ) $=
    ( wi wfal merco1lem4 merco1 ax-mp ) CADZAEDZDBDJBDZDKCDACDDIJBFCAABKGH $.

  $( Used to rederive the Tarski-Bernays-Wajsberg axioms from ~ merco1 .
     (Contributed by Anthony Hart, 17-Sep-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  merco1lem6 $p |- ( ( ph -> ( ph -> ps ) ) -> ( ch -> ( ph -> ps ) ) ) $=
    ( wi wfal merco1lem5 merco1lem3 ax-mp merco1 ) ABDZEDCEDZDZEDZADZAJDCJDDJME
    DZDZNLODZPOEDMDQLEEFOELGHJKOFHABMGHJECEAIH $.

  $( Used to rederive the Tarski-Bernays-Wajsberg axioms from ~ merco1 .
     (Contributed by Anthony Hart, 17-Sep-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  merco1lem7 $p |- ( ph -> ( ( ( ps -> ch ) -> ps ) -> ps ) ) $=
    ( wi wfal merco1lem5 merco1 ax-mp merco1lem6 ) BCDZBDZKBDZDZALDBEDKEDZDCDJD
    MBNCFBEKCJGHKBAIH $.

  $( ~ tbw-ax3 rederived from ~ merco1 .  (Contributed by Anthony Hart,
     17-Sep-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  retbwax3 $p |- ( ( ( ph -> ps ) -> ph ) -> ph ) $=
    ( wi retbwax2 merco1lem7 ax-mp ) AAACCZABCACACAADGABEF $.

  $( Used to rederive the Tarski-Bernays-Wajsberg axioms from ~ merco1 .
     (Contributed by Anthony Hart, 17-Sep-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  merco1lem8 $p |- ( ph -> ( ( ps -> ( ps -> ch ) ) -> ( ps -> ch ) ) ) $=
    ( wi merco1lem6 ax-mp ) BBCDZDZHGDZDAIDBCHEHGAEF $.

  $( Used to rederive the Tarski-Bernays-Wajsberg axioms from ~ merco1 .
     (Contributed by Anthony Hart, 18-Sep-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  merco1lem9 $p |- ( ( ph -> ( ph -> ps ) ) -> ( ph -> ps ) ) $=
    ( wfal wi merco1lem8 ax-mp ) CADZAABDZDHDZDZIGABEJABEF $.

  $( Used to rederive the Tarski-Bernays-Wajsberg axioms from ~ merco1 .
     (Contributed by Anthony Hart, 18-Sep-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  merco1lem10 $p |- ( ( ( ( ( ph -> ps ) -> ch ) -> ( ta -> ch ) ) -> ph ) ->
    ( th -> ph ) ) $=
    ( wi wfal merco1 merco1lem2 ax-mp ) ABFZDGFZFCAFEGFFAFZGFZFKCFECFFZFZOAFDAF
    FMKFOFPCAEAKHMKOLIJABDNOHJ $.

  $( Used to rederive the Tarski-Bernays-Wajsberg axioms from ~ merco1 .
     (Contributed by Anthony Hart, 18-Sep-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  merco1lem11 $p |- ( ( ph -> ps ) -> ( ( ( ch -> ( ph -> ta ) ) -> F. ) -> ps
    ) ) $=
    ( wi wfal merco1lem5 merco1lem3 ax-mp merco1lem4 merco1 merco1lem2 ) ADEZBA
    EZCMEZFEZFEZEZFEZFEZEZABEPBEEZOTEZUAQTEZUCRTEZUDTFESEUERFFGTFRHINQTJIOFTGIC
    MTJISAEUBEUAUBEBAPFAKSAUBDLII $.

  $( Used to rederive the Tarski-Bernays-Wajsberg axioms from ~ merco1 .
     (Contributed by Anthony Hart, 18-Sep-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  merco1lem12 $p |- ( ( ph -> ps ) -> ( ( ( ch -> ( ph -> ta ) ) -> ph ) -> ps
    ) ) $=
    ( wi wfal merco1lem3 merco1 ax-mp merco1lem9 merco1lem11 ) BAEZCADEZEZAEZFE
    ZEFEAEZABEOBEEOAEZQOREZRMPECFEZENESMPCGADOTNHIOAJIOALFKIBAOFAHI $.

  $( Used to rederive the Tarski-Bernays-Wajsberg axioms from ~ merco1 .
     (Contributed by Anthony Hart, 18-Sep-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  merco1lem13 $p |- ( ( ( ( ph -> ps ) -> ( ch -> ps ) ) -> ta ) -> ( ph ->
    ta ) ) $=
    ( wi wfal merco1 merco1lem4 ax-mp merco1lem12 ) DAEZAFEEAEABECBEEZEZLDEADEE
    ALEZMBAECFEEAEZAELENBACAAGOALHIALKFJIDAAALGI $.

  $( Used to rederive the Tarski-Bernays-Wajsberg axioms from ~ merco1 .
     (Contributed by Anthony Hart, 18-Sep-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  merco1lem14 $p |- ( ( ( ( ph -> ps ) -> ps ) -> ch ) -> ( ph -> ch ) ) $=
    ( wi wfal merco1lem13 merco1lem8 merco1 ax-mp merco1lem9 merco1lem12 ) CADZ
    AEDDADABDZBDZDZNCDACDDANDZOMNDNDZPDZPABMNFRRPDZDZSPADREDDADZQDTUAMBGPARAQHI
    RPJIIANLEKICAAANHI $.

  $( Used to rederive the Tarski-Bernays-Wajsberg axioms from ~ merco1 .
     (Contributed by Anthony Hart, 18-Sep-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  merco1lem15 $p |- ( ( ph -> ps ) -> ( ph -> ( ch -> ps ) ) ) $=
    ( wi merco1lem14 merco1lem13 ax-mp ) ABDZBDCBDZDAIDZDHJDABIEHBCJFG $.

  $( Used to rederive the Tarski-Bernays-Wajsberg axioms from ~ merco1 .
     (Contributed by Anthony Hart, 18-Sep-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  merco1lem16 $p |- ( ( ( ph -> ( ps -> ch ) ) -> ta ) -> ( ( ph -> ch ) -> ta
    ) ) $=
    ( wi wfal merco1lem15 merco1lem11 ax-mp merco1 ) DAEZACEZFEEFEABCEEZEZMDELD
    EELMENACBGLMKFHIDALFMJI $.

  $( Used to rederive the Tarski-Bernays-Wajsberg axioms from ~ merco1 .
     (Contributed by Anthony Hart, 18-Sep-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  merco1lem17 $p |- ( ( ( ( ( ph -> ps ) -> ph ) -> ch ) -> ta ) -> ( ( ph ->
    ch ) -> ta ) ) $=
    ( wfal merco1lem11 merco1lem7 ax-mp merco1lem9 merco1lem4 merco1lem16 mpsyl
    wi merco1 ) DAMZACMZEMZMCMZABMAMZCMZMTDMPDMMQPMZTMZRQCMTPTMZUBCAMZSEMMEMAMZ
    UCSAMZUEMZUESAUDEFUGUGUEMZMZUHUEAMUGEMMAMZUFMUIUJABGUEAUGAUFNHUGUEIHHCASEAN
    HTAMZUAEMMEMPMZUCUBMUAPMZULMZULUAPUKEFUNUNULMZMZUOULAMUNEMMAMZUMMUPUQPEGULA
    UNAUMNHUNULIHHTAUAEPNHHOQCJQACTKLDAPCTNH $.

  $( Used to rederive the Tarski-Bernays-Wajsberg axioms from ~ merco1 .
     (Contributed by Anthony Hart, 18-Sep-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  merco1lem18 $p |- ( ( ph -> ( ps -> ch ) ) -> ( ( ps -> ph ) -> ( ps ->
    ch ) ) ) $=
    ( wfal merco1 merco1lem17 ax-mp merco1lem5 merco1lem3 merco1lem4 merco1lem2
    wi merco1lem9 ) BALZABCLZLZNOLZLZLZROBLZALRLZSTNDLZLTLALRLUAOBNTAETUBARFGBC
    ARFGSSRLZLZUCQRDLSDLZLZDLZDLZLZUDRUHLZUIUFUHLZUJUHDLUGLUKUFDDHUHDUFIGRUEUHH
    GPQUHJGUGNLUDLUIUDLRDSDNEUGNUDOKGGSRMGG $.

  $( ~ tbw-ax1 rederived from ~ merco1 .

     This theorem, along with ~ retbwax2 , ~ retbwax3 , and ~ retbwax4 , shows
     that ~ merco1 with ~ ax-mp can be used as a complete axiomatization of
     propositional calculus.  (Contributed by Anthony Hart, 18-Sep-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  retbwax1 $p |- ( ( ph -> ps ) -> ( ( ps -> ch ) -> ( ph -> ch ) ) ) $=
    ( wi merco1lem18 merco1lem16 ax-mp merco1lem15 merco1lem14 wfal merco1lem10
    merco1 merco1lem9 merco1lem13 ) BCDZABDZACDZDZDZPOQDZDZBQDRDSBACEBACRFGOSUA
    DZDZUBSRDUBDZUCRUBDZUDRUADUEPQOHRUASHGRSUAEGORUBIGUCUBDZJDZUADZUFUGTDZUHUFQ
    DZTDZUIOUBQITADZUGJDZDZQDUJDZUKUIDQADZUGDZUMDUNDZUOUMJDULJDDUGDUQDURUGJJUPU
    LKUMJULUGUQLGQAUFUMUNLGTAUGQUJLGGUGTPHGUHUBDUFDZUFDZUHUFDUSUTDUTUFJUAUSSKUS
    UFMGUHUBUCUFNGGGG $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Derive the Tarski-Bernays-Wajsberg axioms from Meredith's Second CO Axiom
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( A single axiom for propositional calculus offered by Meredith.

     This axiom has 19 symbols, sans auxiliaries.  See notes in ~ merco1 .
     (Contributed by Anthony Hart, 7-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  merco2 $p |- ( ( ( ph -> ps ) -> ( ( F. -> ch ) -> th ) ) -> ( ( th
         -> ph ) -> ( ta -> ( et -> ph ) ) ) ) $=
    ( wi wfal falim pm2.04 mpi jarl idd jad looinv 3syl a1dd a1i com4l ) FABGZH
    CGZDGGZDAGZEAUBUCEAGGGFUBUCAEUBTDGZADGDGUCAGUBUAUDCITUADJKUDADDABDLUDDMNADO
    PQRS $.

  $( Used to rederive the Tarski-Bernays-Wajsberg axioms from ~ merco2 .
     (Contributed by Anthony Hart, 16-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  mercolem1 $p |- ( ( ( ph -> ps ) -> ch ) -> ( ps -> ( th -> ch ) ) ) $=
    ( wi wfal merco2 ax-mp ) AAEZFAEZAEEIAIEEEZABEZCEZBDCEZEZEZAAAAAAGZKKPEZQCA
    EZJLEZEZPEZKREZCAALBDGPTEJUAEEZUBUCETOEJPEEZUDOJFEZEFBETEEUEBNAFJAGOUFBTJMG
    HTOAPJSGHPTAUAKKGHHHH $.

  $( Used to rederive the Tarski-Bernays-Wajsberg axioms from ~ merco2 .
     (Contributed by Anthony Hart, 16-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  mercolem2 $p |- ( ( ( ph -> ps ) -> ph ) -> ( ch -> ( th -> ph ) ) ) $=
    ( wi wfal merco2 ax-mp ) AAEZFAEZAEEIAIEEEZABEZAEZCDAEEZEZAAAAAAGZKKOEZPIJL
    EZEZOEZKQEZAAALCDGOREJSEEZTUAERNEJOEEZUBNLEJREEZUCLJFEZEJNEEUDABAFCDGLUEANJ
    JGHNLARJMGHRNAOJIGHORASKKGHHHH $.

  $( Used to rederive the Tarski-Bernays-Wajsberg axioms from ~ merco2 .
     (Contributed by Anthony Hart, 16-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  mercolem3 $p |- ( ( ps -> ch ) -> ( ps -> ( ph -> ch ) ) ) $=
    ( wi wfal merco2 mercolem2 ax-mp ) AADZEADZADDIAIDDDZBCDZBACDZDZDZAAAAAAFZK
    KODZPCADZJBDZDZODZKQDZCAABBAFOSDJTDDZUAUBDSNDJODDZUCNBDJSDDUDBMJJGNBASJLFHS
    NAOJRFHOSATKKFHHHH $.

  $( Used to rederive the Tarski-Bernays-Wajsberg axioms from ~ merco2 .
     (Contributed by Anthony Hart, 16-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  mercolem4 $p |- ( ( th -> ( et -> ph ) ) -> ( ( ( th -> ch )
  -> ph ) -> ( ta -> ( et -> ph ) ) ) ) $=
    ( wi wfal merco2 mercolem1 ax-mp mercolem3 ) AAFZGAFZAFFLALFFFZCEAFZFZCBFZA
    FZDOFFZFZAAAAAAHZNNTFZUAOAFZMCFFZTFZNUBFZOAACRDHTCFZMUDFFZUEUFFUGUDFZUHQMTF
    FZUIMQFZTFZUJLUKFSFULAAAQDEHLUKSPIJMQTMIJCBATUCMHJMUGUDKJTCAUDNNHJJJJ $.

  $( Used to rederive the Tarski-Bernays-Wajsberg axioms from ~ merco2 .
     (Contributed by Anthony Hart, 16-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  mercolem5 $p |- ( th -> ( ( th -> ph ) -> ( ta -> ( ch -> ph ) ) ) ) $=
    ( wi wfal merco2 mercolem1 ax-mp mercolem2 ) AAEZFAEZAEEKAKEEEZCCAEDBAEEEZE
    ZAAAAAAGZMMOEZPLCEZOEZMQEZKRENESAAACDBGKRNCHIOCELREESTECNLLJOCARMMGIIII $.

  $( Used to rederive the Tarski-Bernays-Wajsberg axioms from ~ merco2 .
     (Contributed by Anthony Hart, 16-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  mercolem6 $p |- ( ( ph -> ( ps -> ( ph -> ch ) ) )
  -> ( ps -> ( ph -> ch ) ) ) $=
    ( wi wfal merco2 mercolem1 ax-mp mercolem5 mercolem4 ) AADZEADADDKAKDDDZABA
    CDZDZDZNDZAAAAAAFZLLPDZQLLRDZQORDZLSDZLTQMRDZLTDZAODZMDPDUBAOMBGUDMPLGHATDU
    BUCDNOALIRCALOJHHHLTUADZQPUADZLUEDZALDZPDSDUFALPLGUHPSLGHOUEDUFUGDRLOLIUANO
    LTJHHHHHHH $.

  $( Used to rederive the Tarski-Bernays-Wajsberg axioms from ~ merco2 .
     (Contributed by Anthony Hart, 16-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  mercolem7 $p |- ( ( ph -> ps ) -> ( ( ( ph -> ch )
  -> ( th -> ps ) ) -> ( th -> ps ) ) ) $=
    ( wi wfal merco2 mercolem3 mercolem6 ax-mp mercolem5 mercolem4 ) AAEZFAEAEE
    MAMEEEZABEZACEZDBEZEZQEZEZAAAAAAGPSEZNTEZRUAEUARPQHRPQIJATEUAUBEBDARKSCANOL
    JJJ $.

  $( Used to rederive the Tarski-Bernays-Wajsberg axioms from ~ merco2 .
     (Contributed by Anthony Hart, 16-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  mercolem8 $p |- ( ( ph -> ps ) -> ( ( ps -> ( ph -> ch ) )
  -> ( ta -> ( th -> ( ph -> ch ) ) ) ) ) $=
    ( wi wfal merco2 mercolem3 ax-mp mercolem7 ) AAFZGAFZAFFLALFFFZABFZBACFZFED
    PFFFZFZAAAAAAHZNNRFZSPMBFZFUAFZRFZNTFZUBQFUCPUAABEDHOUBQIJRMUBFZFUEFZUCUDFO
    UBFUFABCMKOUBQMKJRUEAUBNNHJJJJ $.

  $( ~ tbw-ax1 rederived from ~ merco2 .  (Contributed by Anthony Hart,
     16-Aug-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  re1tbw1 $p |- ( ( ph -> ps ) -> ( ( ps -> ch ) -> ( ph -> ch ) ) ) $=
    ( wi mercolem8 mercolem3 mercolem6 mpsyl ax-mp ) BCDZABDZJACDZDZDZDNKBLDZND
    DJONABCJKEABCFKOMGHJKLGI $.

  $( ~ tbw-ax2 rederived from ~ merco2 .  (Contributed by Anthony Hart,
     16-Aug-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  re1tbw2 $p |- ( ph -> ( ps -> ph ) ) $=
    ( wi mercolem1 ax-mp mercolem6 ) BABACZCZCZHAICZIAACZACHCJAAABDKAHBDEABGFEB
    AAFE $.

  $( ~ tbw-ax3 rederived from ~ merco2 .  (Contributed by Anthony Hart,
     16-Aug-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  re1tbw3 $p |- ( ( ( ph -> ps ) -> ph ) -> ph ) $=
    ( wi mercolem2 mercolem6 ax-mp ) AACZACAGCCZABCACZACZAAAADIHJCZCKABHIDIHAEF
    F $.

  $( ~ tbw-ax4 rederived from ~ merco2 .

     This theorem, along with ~ re1tbw1 , ~ re1tbw2 , and ~ re1tbw3 , shows
     that ~ merco2 , along with ~ ax-mp , can be used as a complete
     axiomatization of propositional calculus.  (Contributed by Anthony Hart,
     16-Aug-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  re1tbw4 $p |- ( F. -> ph ) $=
    ( wi wfal re1tbw3 re1tbw2 re1tbw1 ax-mp mercolem3 merco2 ) AABZCABZJABZABZJ
    AADALBMJBAJEALAFGGZJJKBZNKKBZJOBZKABZKBZKBZPKADKSBTPBKREKSKFGGRPBPQBCKAHKAA
    KJJIGGGG $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
       Derive the Lukasiewicz axioms from the The Russell-Bernays Axioms
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Justification for ~ rb-imdf .  (Contributed by Anthony Hart,
     17-Aug-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  rb-bijust $p |- ( ( ph <-> ps ) <-> -. ( -. ( -. ph \/ ps )
    \/ -. ( -. ps \/ ph ) ) ) $=
    ( wb wi wn wo dfbi1 imor notbii imbi12i pm4.62 3bitri ) ABCABDZBADZEZDZEAEB
    FZBEAFZEZDZEQESFZEABGPTMQOSABHNRBAHIJITUAQRKIL $.

  $( The definition of implication, in terms of ` \/ ` and ` -. ` .
     (Contributed by Anthony Hart, 17-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  rb-imdf $p |- -. ( -. ( -. ( ph -> ps ) \/ ( -. ph \/ ps ) )
    \/ -. ( -. ( -. ph \/ ps ) \/ ( ph -> ps ) ) ) $=
    ( wi wn wo wb imor rb-bijust mpbi ) ABCZADBEZFJDKEDKDJEDEDABGJKHI $.

  ${
    anmp.min $e |- ph $.
    anmp.maj $e |- ( -. ph \/ ps ) $.
    $( Modus ponens for ` \/ ` ` -. ` axiom systems.  (Contributed by Anthony
       Hart, 12-Aug-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    anmp $p |- ps $=
      ( imorri ax-mp ) ABCABDEF $.
  $}

  $( The first of four axioms in the Russell-Bernays axiom system.
     (Contributed by Anthony Hart, 13-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  rb-ax1 $p |- ( -. ( -. ps \/ ch ) \/ ( -. ( ph \/ ps ) \/ ( ph \/ ch ) ) ) $=
    ( wn wo wi orim2 imor 3imtr3i imori ) BDCEZABEZDACEZEZBCFLMFKNABCGBCHLMHIJ
    $.

  $( The second of four axioms in the Russell-Bernays axiom system.
     (Contributed by Anthony Hart, 13-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  rb-ax2 $p |- ( -. ( ph \/ ps ) \/ ( ps \/ ph ) ) $=
    ( wo wn pm1.4 con3i con1i orri ) ABCZDZBACZKJIKABEFGH $.

  $( The third of four axioms in the Russell-Bernays axiom system.
     (Contributed by Anthony Hart, 13-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  rb-ax3 $p |- ( -. ph \/ ( ps \/ ph ) ) $=
    ( wn wo pm2.46 con1i orri ) ACZBADZIHBAEFG $.

  $( The fourth of four axioms in the Russell-Bernays axiom system.
     (Contributed by Anthony Hart, 13-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  rb-ax4 $p |- ( -. ( ph \/ ph ) \/ ph ) $=
    ( wo wn pm1.2 con3i con1i orri ) AABZCZAAIHAADEFG $.

  ${
    rbsyl.1 $e |- ( -. ps \/ ch ) $.
    rbsyl.2 $e |- ( ph \/ ps ) $.
    $( Used to rederive the Lukasiewicz axioms from Russell-Bernays'.
       (Contributed by Anthony Hart, 18-Aug-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    rbsyl $p |- ( ph \/ ch ) $=
      ( wo wn rb-ax1 anmp ) ABFZACFZEBGCFJGKFDABCHII $.
  $}

  ${
    rblem1.1 $e |- ( -. ph \/ ps ) $.
    rblem1.2 $e |- ( -. ch \/ th ) $.
    $( Used to rederive the Lukasiewicz axioms from Russell-Bernays'.
       (Contributed by Anthony Hart, 18-Aug-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    rblem1 $p |- ( -. ( ph \/ ch ) \/ ( ps \/ th ) ) $=
      ( wo wn rb-ax1 anmp rb-ax2 rbsyl ) ACGHZBCGZBDGZCHDGNHOGFBCDIJMCBGZNCBKMC
      AGZPAHBGQHPGECABIJACKLLL $.
  $}

  $( Used to rederive the Lukasiewicz axioms from Russell-Bernays'.
     (Contributed by Anthony Hart, 18-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  rblem2 $p |- ( -. ( ch \/ ph ) \/ ( ch \/ ( ph \/ ps ) ) ) $=
    ( wn wo rb-ax2 rb-ax3 rbsyl rb-ax1 anmp ) ADZABEZECAEDCLEEKBAELBAFABGHCALIJ
    $.

  $( Used to rederive the Lukasiewicz axioms from Russell-Bernays'.
     (Contributed by Anthony Hart, 18-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  rblem3 $p |- ( -. ( ch \/ ph ) \/ ( ( ch \/ ps ) \/ ph ) ) $=
    ( wo wn rb-ax2 rblem2 rbsyl ) CADEZACBDZDZJADAJFIACDKCBAGCAFHH $.

  ${
    rblem4.1 $e |- ( -. ph \/ th ) $.
    rblem4.2 $e |- ( -. ps \/ ta ) $.
    rblem4.3 $e |- ( -. ch \/ et ) $.
    $( Used to rederive the Lukasiewicz axioms from Russell-Bernays'.
       (Contributed by Anthony Hart, 18-Aug-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    rblem4 $p |- ( -. ( ( ph \/ ps ) \/ ch ) \/ ( ( et \/ ta ) \/ th ) ) $=
      ( wo wn rblem1 rb-ax2 rb-ax1 anmp rbsyl rb-ax4 rblem2 rb-ax3 ) ABJZCJKZCB
      JZAJZFEJZDJUBUDADCFBEIHLGLUABCJZAJZUCUFKZAUBJZUCAUBMUGAUEJZUHUEKUBJUIKUHJ
      BCMAUEUBNOUEAMPPUAUFUFJUFUFQTUFCUFTKUIUFAUEMBCARPCKZUEJUJUFJCBSUEAUJROLPP
      P $.
  $}

  $( Used to rederive the Lukasiewicz axioms from Russell-Bernays'.
     (Contributed by Anthony Hart, 19-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  rblem5 $p |- ( -. ( -. -. ph \/ ps ) \/ ( -. -. ps \/ ph ) ) $=
    ( wn wo rb-ax2 rb-ax4 rb-ax3 rbsyl anmp rblem1 ) ACZCZBDCABCZCZDNADANELABNK
    ADLCZADKAADAAFAAGHZKOAAOLDLODOLLDLLFLLGHOLEIPJINMDMNDNMMDMMFMMGHNMEIJH $.

  ${
    rblem6.1 $e |- -. ( -. ( -. ph \/ ps ) \/ -. ( -. ps \/ ph ) ) $.
    $( Used to rederive the Lukasiewicz axioms from Russell-Bernays'.
       (Contributed by Anthony Hart, 19-Aug-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    rblem6 $p |- ( -. ph \/ ps ) $=
      ( wn wo rb-ax4 rb-ax3 rbsyl rb-ax2 anmp rblem3 rblem5 ) ADBEZDZBDAEDZEZDZ
      MCNDZPEZQDMEPREZSNREZTRNEUARNNENNFNNGHRNIJRONKJPRIJMPLJJ $.
  $}

  ${
    rblem7.1 $e |- -. ( -. ( -. ph \/ ps ) \/ -. ( -. ps \/ ph ) ) $.
    $( Used to rederive the Lukasiewicz axioms from Russell-Bernays'.
       (Contributed by Anthony Hart, 19-Aug-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    rblem7 $p |- ( -. ps \/ ph ) $=
      ( wn wo rb-ax3 rblem5 anmp ) ADBEDZBDAEZDZEZDZJCKDLEMDJEKIFJLGHH $.
  $}

  ${
    re1axmp.min $e |- ph $.
    re1axmp.maj $e |- ( ph -> ps ) $.
    $( ~ ax-mp derived from Russell-Bernays'.  (Contributed by Anthony Hart,
       19-Aug-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    re1axmp $p |- ps $=
      ( wi wn wo rb-imdf rblem6 anmp ) ABCABEZAFBGZDKLABHIJJ $.
  $}

  $( ~ luk-1 derived from Russell-Bernays'.  (Contributed by Anthony Hart,
     19-Aug-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  re2luk1 $p |- ( ( ph -> ps ) -> ( ( ps -> ch ) -> ( ph -> ch ) ) ) $=
    ( wi wn rb-imdf rblem7 rblem6 rb-ax2 rb-ax4 rb-ax3 rbsyl anmp rblem1 rb-ax1
    wo rblem4 ) ABDZEZBCDZACDZDZPZRUBDZSTEZUAPZUBUBUFTUAFGSAEZBPZUFUHEZBECPZEZU
    GCPZPZUFUKUEULUAUEUJPZUKEZUEPZTUJBCFHUNEUEUOPUPUEUOIUEUEUJUOUEEUEUEPUEUEJUE
    UEKLUOUKPUKUOPUOUKUKPUKUKJUKUKKLZUOUKIMNLMUAULACFGNUKUIULPZPZUIUMPZUGBCOUSE
    ZUMUIPZUTUMUIIVAURUKPVBUIULUKUIULUKUIEUIUIPUIUIJUIUIKLULEULULPULULJULULKLUQ
    QUKURILLMLRUHABFHLLUDUCRUBFGM $.

  $( ~ luk-2 derived from Russell-Bernays'.  (Contributed by Anthony Hart,
     19-Aug-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  re2luk2 $p |- ( ( -. ph -> ph ) -> ph ) $=
    ( wn wi wo rb-ax4 rb-ax3 rbsyl rb-ax2 anmp rblem1 rb-imdf rblem6 rblem7 ) A
    BZACZBZADZOACZPNBZADZATBAADZAAEZSAAANADSBZADNUAAUBAAFGZNUCAAUCSDSUCDUCSSDSS
    ESSFGUCSHIUDJIUDJGOTNAKLGRQOAKMI $.

  $( ~ luk-3 derived from Russell-Bernays'.

     This theorem, along with ~ re1axmp , ~ re2luk1 , and ~ re2luk2 shows that
     ~ rb-ax1 , ~ rb-ax2 , ~ rb-ax3 , and ~ rb-ax4 , along with ~ anmp , can be
     used as a complete axiomatization of propositional calculus.  (Contributed
     by Anthony Hart, 19-Aug-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  re2luk3 $p |- ( ph -> ( -. ph -> ps ) ) $=
    ( wn wi wo rb-imdf rblem7 rb-ax4 rb-ax3 rbsyl rb-ax2 anmp rblem2 ) ACZNBDZE
    ZAODZNNCZBEZOOSNBFGNREZNSERNETRNNENNHNNIJRNKLRBNMLJQPAOFGL $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                Stoic logic indemonstrables (Chrysippus of Soli)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  The Greek Stoics developed a system of logic.
  The Stoic Chrysippus, in particular, was often considered one of the greatest
  logicians of antiquity.
  Stoic logic is different from Aristotle's system, since it focuses
  on propositional logic,
  though later thinkers did combine the systems of the Stoics with Aristotle.
  Jan Lukasiewicz reports,
  "For anybody familiar with mathematical logic it is self-evident
  that the Stoic dialectic is the ancient form of modern propositional logic"
  ( _On the history of the logic of proposition_ by Jan Lukasiewicz (1934),
  translated in: _Selected Works_ - Edited by Ludwik Borkowski -
  Amsterdam, North-Holland, 1970 pp. 197-217,
  referenced in "History of Logic"
  ~ https://www.historyoflogic.com/logic-stoics.htm ).
  For more about Aristotle's system, see ~ barbara and related theorems.

  A key part of the Stoic logic system is a set of five "indemonstrables"
  assigned to Chrysippus of Soli by Diogenes Laertius, though in
  general it is difficult to assign specific
  ideas to specific thinkers.
  The indemonstrables are described in, for example,
  [Lopez-Astorga] p. 11 , [Sanford] p. 39, and [Hitchcock] p. 5.
  These indemonstrables are
  modus ponendo ponens (modus ponens) ~ ax-mp ,
  modus tollendo tollens (modus tollens) ~ mto ,
  modus ponendo tollens I ~ mpto1 ,
  modus ponendo tollens II ~ mpto2 , and
  modus tollendo ponens (exclusive-or version) ~ mtp-xor .
  The first is an axiom, the second is already proved; in this section
  we prove the other three.
  Since we assume or prove all of indemonstrables, the system of logic we use
  here is as at least as strong as the set of Stoic indemonstrables.
  Note that modus tollendo ponens ~ mtp-xor originally used exclusive-or,
  but over time the name modus tollendo ponens has increasingly referred
  to an inclusive-or variation, which is proved in ~ mtp-or .
  This set of indemonstrables is not the entire system of Stoic logic.

$)

  ${
    $( Minor premise for modus ponendo tollens 1. $)
    mpto1.1 $e |- ph $.
    $( Major premise for modus ponendo tollens 1. $)
    mpto1.2 $e |- -. ( ph /\ ps ) $.
    $( Modus ponendo tollens 1, one of the "indemonstrables" in Stoic logic.
       See rule 1 on [Lopez-Astorga] p. 12 , rule 1 on [Sanford] p. 40, and
       rule A3 in [Hitchcock] p. 5.  Sanford describes this rule second (after
       ~ mpto2 ) as a "safer, and these days much more common" version of modus
       ponendo tollens because it avoids confusion between inclusive-or and
       exclusive-or.  (Contributed by David A. Wheeler, 3-Jul-2016.) $)
    mpto1 $p |- -. ps $=
      ( wn imnani ax-mp ) ABECABDFG $.
  $}

  ${
    $( Minor premise for modus ponendo tollens 2. $)
    mpto2.1 $e |- ph $.
    $( Major premise for modus ponendo tollens 2. $)
    mpto2.2 $e |- ( ph \/_ ps ) $.
    $( Modus ponendo tollens 2, one of the "indemonstrables" in Stoic logic.
       Note that this uses exclusive-or ` \/_ ` .  See rule 2 on
       [Lopez-Astorga] p. 12 , rule 4 on [Sanford] p. 39 and rule A4 in
       [Hitchcock] p. 5 .  (Contributed by David A. Wheeler, 3-Jul-2016.)
       (Proof shortened by Wolf Lammen, 12-Nov-2017.) $)
    mpto2 $p |- -. ps $=
      ( wn wb wxo df-xor mpbi xor3 ) ABEZCABFEZAKFABGLDABHIABJII $.
  $}

  ${
    $( Minor premise for modus ponendo tollens 2. $)
    mpto2OLD.1 $e |- ph $.
    $( Major premise for modus ponendo tollens 2. $)
    mpto2OLD.2 $e |- ( ph \/_ ps ) $.
    $( Obsolete version of ~ mpto2 as of 12-Nov-2017.  (Contributed by David A.
       Wheeler, 3-Jul-2016.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    mpto2OLD $p |- -. ps $=
      ( wn wb wxo df-xor mpbi nbbn mpbir con1bii ) BEACABAEBFABFEZABGMDABHIABJK
      LK $.
  $}


  ${
    $( Minor premise for modus tollendo ponens (original exclusive-or version).
    $)
    mtp-xor.1 $e |- -. ph $.
    $( Major premise for modus tollendo ponens (original exclusive-or version).
    $)
    mtp-xor.2 $e |- ( ph \/_ ps ) $.
    $( Modus tollendo ponens (original exclusive-or version), aka disjunctive
       syllogism, one of the five "indemonstrables" in Stoic logic.  The rule
       says, "if ` ph ` is not true, and either ` ph ` or ` ps ` (exclusively)
       are true, then ` ps ` must be true."  Today the name "modus tollendo
       ponens" often refers to a variant, the inclusive-or version as defined
       in ~ mtp-or .  See rule 3 on [Lopez-Astorga] p. 12 (note that the "or"
       is the same as ~ mpto2 , that is, it is exclusive-or ~ df-xor ), rule 3
       of [Sanford] p. 39 (where it is not as clearly stated which kind of "or"
       is used but it appears to be in the same sense as ~ mpto2 ), and rule A5
       in [Hitchcock] p. 5 (exclusive-or is expressly used).  (Contributed by
       David A. Wheeler, 4-Jul-2016.)  (Proof shortened by Wolf Lammen,
       11-Nov-2017.) $)
    mtp-xor $p |- ps $=
      ( wn wxo xorneg mpbir mpto2 notnotri ) BAEZBEZCKLFABFDABGHIJ $.

    $( Obsolete version of ~ mtp-xor as of 11-Nov-2017.  (Contributed by David
       A. Wheeler, 4-Jul-2016.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    mtp-xorOLD $p |- ps $=
      ( wn wb wxo df-xor mpbi bicom mtbi xor3 mpbir ) BAEZCBAFZEBNFABFZOABGPEDA
      BHIABJKBALIM $.
  $}

  ${
    $( Minor premise for modus tollendo ponens (inclusive-or version). $)
    mtp-or.1 $e |- -. ph $.
    $( Major premise for modus tollendo ponens (inclusive-or version). $)
    mtp-or.2 $e |- ( ph \/ ps ) $.
    $( Modus tollendo ponens (inclusive-or version), aka disjunctive
       syllogism.  This is similar to ~ mtp-xor , one of the five original
       "indemonstrables" in Stoic logic.  However, in Stoic logic this rule
       used exclusive-or, while the name modus tollendo ponens often refers to
       a variant of the rule that uses inclusive-or instead.  The rule says,
       "if ` ph ` is not true, and ` ph ` or ` ps ` (or both) are true, then
       ` ps ` must be true."  An alternative phrasing is, "Once you eliminate
       the impossible, whatever remains, no matter how improbable, must be the
       truth." -- Sherlock Holmes (Sir Arthur Conan Doyle, 1890:  The Sign of
       the Four, ch. 6).  (Contributed by David A. Wheeler, 3-Jul-2016.)
       (Proof shortened by Wolf Lammen, 11-Nov-2017.) $)
    mtp-or $p |- ps $=
      ( wn ori ax-mp ) AEBCABDFG $.

    $( Obsolete version of ~ mtp-or as of 11-Nov-2017.  (Contributed by David
       A. Wheeler, 3-Jul-2016.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    mtp-orOLD $p |- ps $=
      ( wn wo wi pm2.53 ax-mp ) AEZBCABFJBGDABHII $.
  $}


$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
    Predicate calculus with equality:  Tarski's system S2 (1 rule, 6 schemes)
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#

  Here we extend the language of wffs with predicate calculus, which allows us
  to talk about individual objects in a domain of discussion (which for us will
  be the universe of all sets, so we call them "set variables") and make
  true/false statements about predicates, which are relationships between
  objects, such as whether or not two objects are equal.  In addition, we
  introduce universal quantification ("for all") in order to make statements
  about whether a wff holds for every object in the domain of discussion.
  Later we introduce existential quantification ("there exists", ~ df-ex )
  which is defined in terms of universal quantification.

  Our axioms are really axiom _schemes_, and our wff and set variables are
  metavariables ranging over expressions in an underlying "object language."
  This is explained here:  ~ http://us.metamath.org/mpeuni/mmset.html#axiomnote

  Our axiom system starts with the predicate calculus axiom schemes system S2
  of Tarski defined in his 1965 paper, "A Simplified Formalization of Predicate
  Logic with Identity" [Tarski].  System S2 is defined in the last paragraph on
  p. 77, and repeated on p. 81 of [KalishMontague].  We do not include scheme
  B5 (our ~ sp ) since [KalishMontague] shows it to be logically redundant
  (Lemma 9, p. 87, which we prove as theorem ~ spw below).

  Theorem ~ spw can be used to prove any instance of ~ sp having no wff
  metavariables and mutually distinct set variables.  However, it seems that
  ~ sp in its general form cannot be derived from only Tarski's schemes.  We
  do not include B5 i.e.  ~ sp as part of what we call "Tarski's system"
  because we want it to be the smallest set of axioms that is logically
  complete with no redundancies.  We later prove ~ sp as theorem ~ ax4
  using the auxiliary axioms that make our system metalogically complete.

  Our version of Tarski's system S2 consists of propositional calculus plus
  ~ ax-gen , ~ ax-5 , ~ ax-17 , ~ ax-9 , ~ ax-8 , ~ ax-13 , and ~ ax-14 . The
  last 3 are equality axioms that represent 3 sub-schemes of Tarski's scheme
  B8.  Due to its side-condition ("where ` ph ` is an atomic formula and ` ps `
  is obtained by replacing an occurrence of the variable ` x ` by the variable
  ` y ` "), we cannot represent his B8 directly without greatly complicating
  our scheme language, but the simpler schemes ~ ax-8 , ~ ax-13 , and ~ ax-14
  are sufficient for set theory.

  Tarski's system is exactly equivalent to the traditional axiom system in most
  logic textbooks but has the advantage of being easy to manipulate with a
  computer program, and its simpler metalogic (with no built-in notions of free
  variable and proper substitution) is arguably easier for a non-logician human
  to follow step by step in a proof.

  However, in our system that derives schemes (rather than object language
  theorems) from other schemes, Tarski's S2 is not complete.  For example, we
  cannot derive scheme ~ sp , even though (using ~ spw ) we can derive all
  instances of it that don't involve wff metavariables or bundled set
  metavariables.  (Two set metavariables are "bundled" if they can be
  substituted with the same set metavariable i.e. do not have a $d distinct
  variable proviso.)  Later we will introduce auxiliary axiom schemes ~ ax-6 ,
  ~ ax-7 , ~ ax-12 , and ~ ax-11 that are metatheorems of Tarski's system (i.e.
  are logically redundant) but which give our system the property of
  "metalogical completeness," allowing us to prove directly (instead of, say,
  by induction on formula length) all possible schemes that can be expressed in
  our language.

$)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
    Universal quantifier; define "exists" and "not free"
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Declare new symbols needed for predicate calculus. $)
  $c A. $. $( "inverted A" universal quantifier (read:  "for all") $)
  $c set $. $( Individual variable type (read:  "the following is an
             individual (set) variable" $)

  $( Add 'set' as a typecode. $)
  $( $j syntax 'set'; $)

  $( Declare some names for individual variables. $)
  $v x $.
  $v y $.
  $v z $.
  $v w $.
  $v v $.
  $v u $.
  $v t $.
  $( Let ` x ` be an individual variable. $)
  vx $f set x $.
  $( Let ` y ` be an individual variable. $)
  vy $f set y $.
  $( Let ` z ` be an individual variable. $)
  vz $f set z $.
  $( Let ` w ` be an individual variable. $)
  vw $f set w $.
  $( Let ` v ` be an individual variable. $)
  vv $f set v $.
  $( Let ` u ` be an individual variable. $)
  vu $f set u $.
  $( Let ` t ` be an individual variable. $)
  vt $f set t $.

  $( Extend wff definition to include the universal quantifier ('for all').
     ` A. x ph ` is read " ` ph ` (phi) is true for all ` x ` ."  Typically, in
     its final application ` ph ` would be replaced with a wff containing a
     (free) occurrence of the variable ` x ` , for example ` x = y ` .  In a
     universe with a finite number of objects, "for all" is equivalent to a big
     conjunction (AND) with one wff for each possible case of ` x ` .  When the
     universe is infinite (as with set theory), such a propositional-calculus
     equivalent is not possible because an infinitely long formula has no
     meaning, but conceptually the idea is the same. $)
  wal $a wff A. x ph $.

  $( Register 'A.' as a primitive expression (lacking a definition). $)
  $( $j primitive 'wal'; $)

  $( Declare the existential quantifier symbol. $)
  $c E. $.   $( Backwards E (read:  "there exists") $)

  $( Extend wff definition to include the existential quantifier ("there
     exists"). $)
  wex $a wff E. x ph $.

  $( Define existential quantification. ` E. x ph ` means "there exists at
     least one set ` x ` such that ` ph ` is true."  Definition of [Margaris]
     p. 49.  (Contributed by NM, 5-Aug-1993.) $)
  df-ex $a |- ( E. x ph <-> -. A. x -. ph ) $.

  $( Theorem 19.7 of [Margaris] p. 89.  (Contributed by NM, 5-Aug-1993.) $)
  alnex $p |- ( A. x -. ph <-> -. E. x ph ) $=
    ( wex wn wal df-ex con2bii ) ABCADBEABFG $.

  $c F/ $.  $( The not-free symbol. $)

  $( Extend wff definition to include the not-free predicate. $)
  wnf $a wff F/ x ph $.

  $( Define the not-free predicate for wffs.  This is read " ` x ` is not free
     in ` ph ` ".  Not-free means that the value of ` x ` cannot affect the
     value of ` ph ` , e.g., any occurrence of ` x ` in ` ph ` is effectively
     bound by a "for all" or something that expands to one (such as "there
     exists").  In particular, substitution for a variable not free in a wff
     does not affect its value ( ~ sbf ).  An example of where this is used is
     ~ stdpc5 .  See ~ nf2 for an alternative definition which does not involve
     nested quantifiers on the same variable.

     Not-free is a commonly used constraint, so it is useful to have a notation
     for it.  Surprisingly, there is no common formal notation for it, so here
     we devise one.  Our definition lets us work with the not-free notion
     within the logic itself rather than as a metalogical side condition.

     To be precise, our definition really means "effectively not free," because
     it is slightly less restrictive than the usual textbook definition for
     not-free (which only considers syntactic freedom).  For example, ` x ` is
     effectively not free in the bare expression ` x = x ` (see ~ nfequid ),
     even though ` x ` would be considered free in the usual textbook
     definition, because the value of ` x ` in the expression ` x = x ` cannot
     affect the truth of the expression (and thus substitution will not change
     the result).

     This predicate only applies to wffs.  See ~ df-nfc for a not-free
     predicate for class variables.  (Contributed by Mario Carneiro,
     11-Aug-2016.) $)
  df-nf $a |- ( F/ x ph <-> A. x ( ph -> A. x ph ) ) $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
       Rule scheme ax-gen (Generalization)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    ax-g.1 $e |- ph $.
    $( Rule of Generalization.  The postulated inference rule of predicate
       calculus.  See e.g.  Rule 2 of [Hamilton] p. 74.  This rule says that if
       something is unconditionally true, then it is true for all values of a
       variable.  For example, if we have proved ` x = x ` , we can conclude
       ` A. x x = x ` or even ` A. y x = x ` .  Theorem ~ allt shows the
       special case ` A. x T. ` .  Theorem ~ spi shows we can go the other way
       also: in other words we can add or remove universal quantifiers from the
       beginning of any theorem as required.  (Contributed by NM,
       5-Aug-1993.) $)
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
       not free in ` ph ` ."  (Contributed by NM, 5-Aug-1993.) $)
    hbth $p |- ( ph -> A. x ph ) $=
      ( wal ax-gen a1i ) ABDAABCEF $.

    $( No variable is (effectively) free in a theorem.  (Contributed by Mario
       Carneiro, 11-Aug-2016.) $)
    nfth $p |- F/ x ph $=
      ( hbth nfi ) ABABCDE $.
  $}

  $( The true constant has no free variables.  (This can also be proven in one
     step with ~ nfv , but this proof does not use ~ ax-17 .)  (Contributed by
     Mario Carneiro, 6-Oct-2016.) $)
  nftru $p |- F/ x T. $=
    ( wtru tru nfth ) BACD $.

  ${
    nex.1 $e |- -. ph $.
    $( Generalization rule for negated wff.  (Contributed by NM,
       18-May-1994.) $)
    nex $p |- -. E. x ph $=
      ( wn wex alnex mpgbi ) ADABEDBABFCG $.
  $}

  ${
    nfnth.1 $e |- -. ph $.
    $( No variable is (effectively) free in a non-theorem.  (Contributed by
       Mario Carneiro, 6-Dec-2016.) $)
    nfnth $p |- F/ x ph $=
      ( wal pm2.21i nfi ) ABAABDCEF $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
         Axiom scheme ax-5 (Quantified Implication)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Axiom of Quantified Implication.  Axiom C4 of [Monk2] p. 105.
     (Contributed by NM, 5-Aug-1993.) $)
  ax-5 $a |- ( A. x ( ph -> ps ) -> ( A. x ph -> A. x ps ) ) $.

  $( Theorem 19.20 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.)
     (Proof shortened by O'Cat, 30-Mar-2008.) $)
  alim $p |- ( A. x ( ph -> ps ) -> ( A. x ph -> A. x ps ) ) $=
    ( ax-5 ) ABCD $.

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
    ( wb wal bi1 al2imi bi2 impbid ) ABDZCEACEBCEJABCABFGJBACABHGI $.

  ${
    alrimih.1 $e |- ( ph -> A. x ph ) $.
    alrimih.2 $e |- ( ph -> ps ) $.
    $( Inference from Theorem 19.21 of [Margaris] p. 90.  (Contributed by NM,
       5-Aug-1993.) $)
    alrimih $p |- ( ph -> A. x ps ) $=
      ( wal alimi syl ) AACFBCFDABCEGH $.
  $}

  ${
    albii.1 $e |- ( ph <-> ps ) $.
    $( Inference adding universal quantifier to both sides of an equivalence.
       (Contributed by NM, 7-Aug-1994.) $)
    albii $p |- ( A. x ph <-> A. x ps ) $=
      ( wb wal albi mpg ) ABEACFBCFECABCGDH $.

    $( Theorem albii is the congruence law for universal quantification. $)
    $( $j congruence 'albii'; $)

    $( Inference adding two universal quantifiers to both sides of an
       equivalence.  (Contributed by NM, 9-Mar-1997.) $)
    2albii $p |- ( A. x A. y ph <-> A. x A. y ps ) $=
      ( wal albii ) ADFBDFCABDEGG $.
  $}

  ${
    hbxfrbi.1 $e |- ( ph <-> ps ) $.
    hbxfrbi.2 $e |- ( ps -> A. x ps ) $.
    $( A utility lemma to transfer a bound-variable hypothesis builder into a
       definition.  See ~ hbxfreq for equality version.  (Contributed by
       Jonathan Ben-Naim, 3-Jun-2011.) $)
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

  $( Theorem 19.6 of [Margaris] p. 89.  (Contributed by NM, 5-Aug-1993.) $)
  alex $p |- ( A. x ph <-> -. E. x -. ph ) $=
    ( wal wn wex notnot albii alnex bitri ) ABCADZDZBCJBEDAKBAFGJBHI $.

  $( Part of theorem *11.5 in [WhiteheadRussell] p. 164.  (Contributed by
     Andrew Salmon, 24-May-2011.) $)
  2nalexn $p |- ( -. A. x A. y ph <-> E. x E. y -. ph ) $=
    ( wn wex wal df-ex alex albii xchbinxr bicomi ) ADCEZBEZACFZBFZDMLDZBFOLBGN
    PBACHIJK $.

  $( Theorem 19.14 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)
  exnal $p |- ( E. x -. ph <-> -. A. x ph ) $=
    ( wal wn wex alex con2bii ) ABCADBEABFG $.

  $( Theorem 19.22 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.)
     (Proof shortened by Wolf Lammen, 4-Jul-2014.) $)
  exim $p |- ( A. x ( ph -> ps ) -> ( E. x ph -> E. x ps ) ) $=
    ( wi wal wex wn con3 al2imi alnex 3imtr3g con4d ) ABDZCEZBCFZACFZNBGZCEAGZC
    EOGPGMQRCABHIBCJACJKL $.

  ${
    eximi.1 $e |- ( ph -> ps ) $.
    $( Inference adding existential quantifier to antecedent and consequent.
       (Contributed by NM, 5-Aug-1993.) $)
    eximi $p |- ( E. x ph -> E. x ps ) $=
      ( wi wex exim mpg ) ABEACFBCFECABCGDH $.

    $( Inference adding two existential quantifiers to antecedent and
       consequent.  (Contributed by NM, 3-Feb-2005.) $)
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

  $( A relationship between two quantifiers and negation.  (Contributed by NM,
     18-Aug-1993.) $)
  alexn $p |- ( A. x E. y -. ph <-> -. E. x A. y ph ) $=
    ( wn wex wal exnal albii alnex bitri ) ADCEZBFACFZDZBFLBEDKMBACGHLBIJ $.

  $( Theorem *11.51 in [WhiteheadRussell] p. 164.  (Contributed by Andrew
     Salmon, 24-May-2011.)  (Proof shortened by Wolf Lammen, 25-Sep-2014.) $)
  2exnexn $p |- ( E. x A. y ph <-> -. A. x E. y -. ph ) $=
    ( wn wex wal alexn con2bii ) ADCEBFACFBEABCGH $.

  $( Theorem 19.18 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)
  exbi $p |- ( A. x ( ph <-> ps ) -> ( E. x ph <-> E. x ps ) ) $=
    ( wb wal wex wi bi1 alimi exim syl bi2 impbid ) ABDZCEZACFZBCFZOABGZCEPQGNR
    CABHIABCJKOBAGZCEQPGNSCABLIBACJKM $.

  ${
    exbii.1 $e |- ( ph <-> ps ) $.
    $( Inference adding existential quantifier to both sides of an
       equivalence.  (Contributed by NM, 24-May-1994.) $)
    exbii $p |- ( E. x ph <-> E. x ps ) $=
      ( wb wex exbi mpg ) ABEACFBCFECABCGDH $.
  $}

  ${
    2exbii.1 $e |- ( ph <-> ps ) $.
    $( Inference adding two existential quantifiers to both sides of an
       equivalence.  (Contributed by NM, 16-Mar-1995.) $)
    2exbii $p |- ( E. x E. y ph <-> E. x E. y ps ) $=
      ( wex exbii ) ADFBDFCABDEGG $.
  $}

  ${
    3exbii.1 $e |- ( ph <-> ps ) $.
    $( Inference adding 3 existential quantifiers to both sides of an
       equivalence.  (Contributed by NM, 2-May-1995.) $)
    3exbii $p |- ( E. x E. y E. z ph <-> E. x E. y E. z ps ) $=
      ( wex exbii 2exbii ) AEGBEGCDABEFHI $.
  $}

  $( A transformation of quantifiers and logical connectives.  (Contributed by
     NM, 25-Mar-1996.)  (Proof shortened by Wolf Lammen, 4-Sep-2014.) $)
  exanali $p |- ( E. x ( ph /\ -. ps ) <-> -. A. x ( ph -> ps ) ) $=
    ( wn wa wex wi wal annim exbii exnal bitri ) ABDEZCFABGZDZCFNCHDMOCABIJNCKL
    $.

  $( Commutation of conjunction inside an existential quantifier.  (Contributed
     by NM, 18-Aug-1993.) $)
  exancom $p |- ( E. x ( ph /\ ps ) <-> E. x ( ps /\ ph ) ) $=
    ( wa ancom exbii ) ABDBADCABEF $.

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
    eximdh.1 $e |- ( ph -> A. x ph ) $.
    eximdh.2 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction from Theorem 19.22 of [Margaris] p. 90.  (Contributed by NM,
       20-May-1996.) $)
    eximdh $p |- ( ph -> ( E. x ps -> E. x ch ) ) $=
      ( wi wal wex alrimih exim syl ) ABCGZDHBDICDIGAMDEFJBCDKL $.
  $}

  ${
    nexdh.1 $e |- ( ph -> A. x ph ) $.
    nexdh.2 $e |- ( ph -> -. ps ) $.
    $( Deduction for generalization rule for negated wff.  (Contributed by NM,
       2-Jan-2002.) $)
    nexdh $p |- ( ph -> -. E. x ps ) $=
      ( wn wal wex alrimih alnex sylib ) ABFZCGBCHFALCDEIBCJK $.
  $}

  ${
    albidh.1 $e |- ( ph -> A. x ph ) $.
    albidh.2 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for universal quantifier (deduction rule).
       (Contributed by NM, 5-Aug-1993.) $)
    albidh $p |- ( ph -> ( A. x ps <-> A. x ch ) ) $=
      ( wb wal alrimih albi syl ) ABCGZDHBDHCDHGALDEFIBCDJK $.
  $}

  ${
    exbidh.1 $e |- ( ph -> A. x ph ) $.
    exbidh.2 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for existential quantifier (deduction rule).
       (Contributed by NM, 5-Aug-1993.) $)
    exbidh $p |- ( ph -> ( E. x ps <-> E. x ch ) ) $=
      ( wb wal wex alrimih exbi syl ) ABCGZDHBDICDIGAMDEFJBCDKL $.
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

  $( Theorem 19.26 of [Margaris] p. 90.  Also Theorem *10.22 of
     [WhiteheadRussell] p. 147.  (Contributed by NM, 5-Aug-1993.)  (Proof
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

  $( Theorem 19.29 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.)
     (Proof shortened by Andrew Salmon, 13-May-2011.) $)
  19.29 $p |- ( ( A. x ph /\ E. x ps ) -> E. x ( ph /\ ps ) ) $=
    ( wal wex wa wi pm3.2 alimi exim syl imp ) ACDZBCEZABFZCEZMBOGZCDNPGAQCABHI
    BOCJKL $.

  $( Variation of Theorem 19.29 of [Margaris] p. 90.  (Contributed by NM,
     18-Aug-1993.) $)
  19.29r $p |- ( ( E. x ph /\ A. x ps ) -> E. x ( ph /\ ps ) ) $=
    ( wex wal wa 19.29 ancoms exancom sylibr ) ACDZBCEZFBAFCDZABFCDLKMBACGHABCI
    J $.

  $( Variation of Theorem 19.29 of [Margaris] p. 90 with double
     quantification.  (Contributed by NM, 3-Feb-2005.) $)
  19.29r2 $p |- ( ( E. x E. y ph /\ A. x A. y ps ) ->
             E. x E. y ( ph /\ ps ) ) $=
    ( wex wal wa 19.29r eximi syl ) ADEZCEBDFZCFGKLGZCEABGDEZCEKLCHMNCABDHIJ $.

  $( Variation of Theorem 19.29 of [Margaris] p. 90 with mixed quantification.
     (Contributed by NM, 11-Feb-2005.) $)
  19.29x $p |- ( ( E. x A. y ph /\ A. x E. y ps ) ->
             E. x E. y ( ph /\ ps ) ) $=
    ( wal wex wa 19.29r 19.29 eximi syl ) ADEZCFBDFZCEGLMGZCFABGDFZCFLMCHNOCABD
    IJK $.

  $( Theorem 19.35 of [Margaris] p. 90.  This theorem is useful for moving an
     implication (in the form of the right-hand side) into the scope of a
     single existential quantifier.  (Contributed by NM, 5-Aug-1993.)  (Proof
     shortened by Wolf Lammen, 27-Jun-2014.) $)
  19.35 $p |- ( E. x ( ph -> ps ) <-> ( A. x ph -> E. x ps ) ) $=
    ( wi wex wal wn wa 19.26 annim albii alnex anbi2i 3bitr3i con4bii ) ABDZCEZ
    ACFZBCEZDZPGZCFZRSGZHZQGTGABGZHZCFRUECFZHUBUDAUECIUFUACABJKUGUCRBCLMNPCLRSJ
    NO $.

  ${
    19.35i.1 $e |- E. x ( ph -> ps ) $.
    $( Inference from Theorem 19.35 of [Margaris] p. 90.  (Contributed by NM,
       5-Aug-1993.) $)
    19.35i $p |- ( A. x ph -> E. x ps ) $=
      ( wi wex wal 19.35 mpbi ) ABECFACGBCFEDABCHI $.
  $}

  ${
    19.35ri.1 $e |- ( A. x ph -> E. x ps ) $.
    $( Inference from Theorem 19.35 of [Margaris] p. 90.  (Contributed by NM,
       5-Aug-1993.) $)
    19.35ri $p |- E. x ( ph -> ps ) $=
      ( wi wex wal 19.35 mpbir ) ABECFACGBCFEDABCHI $.
  $}

  $( Theorem 19.25 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)
  19.25 $p |- ( A. y E. x ( ph -> ps ) ->
              ( E. y A. x ph -> E. y E. x ps ) ) $=
    ( wi wex wal 19.35 biimpi alimi exim syl ) ABECFZDGACGZBCFZEZDGNDFODFEMPDMP
    ABCHIJNODKL $.

  $( Theorem 19.30 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.)
     (Proof shortened by Andrew Salmon, 25-May-2011.) $)
  19.30 $p |- ( A. x ( ph \/ ps ) -> ( A. x ph \/ E. x ps ) ) $=
    ( wn wi wal wex wo exnal exim syl5bir df-or albii 3imtr4i ) ADZBEZCFZACFZDZ
    BCGZEABHZCFRTHSOCGQTACIOBCJKUAPCABLMRTLN $.

  $( Theorem 19.43 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.)
     (Proof shortened by Wolf Lammen, 27-Jun-2014.) $)
  19.43 $p |- ( E. x ( ph \/ ps ) <-> ( E. x ph \/ E. x ps ) ) $=
    ( wo wex wn wi wal df-or exbii 19.35 alnex imbi1i 3bitri bitr4i ) ABDZCEZAC
    EZFZBCEZGZRTDQAFZBGZCEUBCHZTGUAPUCCABIJUBBCKUDSTACLMNRTIO $.

  $( Obsolete proof of ~ 19.43 as of 3-May-2017.  Leave this in for the example
     on the mmrecent.html page.  (Contributed by NM, 5-Aug-1993.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  19.43OLD $p |- ( E. x ( ph \/ ps ) <-> ( E. x ph \/ E. x ps ) ) $=
    ( wo wn wal wex wa ioran albii 19.26 alnex anbi12i 3bitri notbii df-ex oran
    3bitr4i ) ABDZEZCFZEACGZEZBCGZEZHZESCGUBUDDUAUFUAAEZBEZHZCFUGCFZUHCFZHUFTUI
    CABIJUGUHCKUJUCUKUEACLBCLMNOSCPUBUDQR $.

  $( Theorem 19.33 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)
  19.33 $p |- ( ( A. x ph \/ A. x ps ) -> A. x ( ph \/ ps ) ) $=
    ( wal wo orc alimi olc jaoi ) ACDABEZCDBCDAJCABFGBJCBAHGI $.

  $( The antecedent provides a condition implying the converse of ~ 19.33 .
     Compare Theorem 19.33 of [Margaris] p. 90.  (Contributed by NM,
     27-Mar-2004.)  (Proof shortened by Andrew Salmon, 25-May-2011.)  (Proof
     shortened by Wolf Lammen, 5-Jul-2014.) $)
  19.33b $p |- ( -. ( E. x ph /\ E. x ps ) ->
               ( A. x ( ph \/ ps ) <-> ( A. x ph \/ A. x ps ) ) ) $=
    ( wex wa wn wo wal ianor alnex pm2.53 al2imi syl5bir olc syl6com orcomd ord
    wi 19.30 orc jaoi sylbi 19.33 impbid1 ) ACDZBCDZEFZABGZCHZACHZBCHZGZUGUEFZU
    FFZGUIULRZUEUFIUMUOUNUIUMUKULUMAFZCHUIUKACJUHUPBCABKLMUKUJNOUIUNUJULUIUFUJU
    IUJUFABCSPQUJUKTOUAUBABCUCUD $.

  $( Theorem 19.40 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)
  19.40 $p |- ( E. x ( ph /\ ps ) -> ( E. x ph /\ E. x ps ) ) $=
    ( wa wex exsimpl exsimpr jca ) ABDCEACEBCEABCFABCGH $.

  $( Theorem *11.42 in [WhiteheadRussell] p. 163.  Theorem 19.40 of [Margaris]
     p. 90 with 2 quantifiers.  (Contributed by Andrew Salmon, 24-May-2011.) $)
  19.40-2 $p |- ( E. x E. y ( ph /\ ps ) ->
        ( E. x E. y ph /\ E. x E. y ps ) ) $=
    ( wa wex 19.40 eximi syl ) ABEDFZCFADFZBDFZEZCFKCFLCFEJMCABDGHKLCGI $.

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

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Axiom scheme ax-17 (Distinctness) - first use of $d
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x ph $.
    $( Axiom of Distinctness.  This axiom quantifies a variable over a formula
       in which it does not occur.  Axiom C5 in [Megill] p. 444 (p. 11 of the
       preprint).  Also appears as Axiom B6 (p. 75) of system S2 of [Tarski]
       p. 77 and Axiom C5-1 of [Monk2] p. 113.

       (See comments in ~ ax17o about the logical redundancy of ~ ax-17 in the
       presence of our obsolete axioms.)

       This axiom essentially says that if ` x ` does not occur in ` ph ` ,
       i.e. ` ph ` does not depend on ` x ` in any way, then we can add the
       quantifier ` A. x ` to ` ph ` with no further assumptions.  By ~ sp , we
       can also remove the quantifier (unconditionally).  (Contributed by NM,
       5-Aug-1993.) $)
    ax-17 $a |- ( ph -> A. x ph ) $.
  $}

  ${
    $d x ps $.
    $( ~ ax-17 with antecedent.  Useful in proofs of deduction versions of
       bound-variable hypothesis builders.  (Contributed by NM, 1-Mar-2013.) $)
    a17d $p |- ( ph -> ( ps -> A. x ps ) ) $=
      ( wal wi ax-17 a1i ) BBCDEABCFG $.
  $}

  ${
    $d x ph $.
    $( A rephrasing of ~ ax-17 using the existential quantifier.  (Contributed
       by Wolf Lammen, 4-Dec-2017.) $)
    ax17e $p |- ( E. x ph -> ph ) $=
      ( wex wn wal df-ex ax-17 con1i sylbi ) ABCADZBEZDAABFAKJBGHI $.
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
    $d x ph $.
    albidv.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for universal quantifier (deduction rule).
       (Contributed by NM, 5-Aug-1993.) $)
    albidv $p |- ( ph -> ( A. x ps <-> A. x ch ) ) $=
      ( ax-17 albidh ) ABCDADFEG $.

    $( Formula-building rule for existential quantifier (deduction rule).
       (Contributed by NM, 5-Aug-1993.) $)
    exbidv $p |- ( ph -> ( E. x ps <-> E. x ch ) ) $=
      ( ax-17 exbidh ) ABCDADFEG $.
  $}

  ${
    $d x ph $.  $d y ph $.
    2albidv.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for 2 universal quantifiers (deduction rule).
       (Contributed by NM, 4-Mar-1997.) $)
    2albidv $p |- ( ph -> ( A. x A. y ps <-> A. x A. y ch ) ) $=
      ( wal albidv ) ABEGCEGDABCEFHH $.

    $( Formula-building rule for 2 existential quantifiers (deduction rule).
       (Contributed by NM, 1-May-1995.) $)
    2exbidv $p |- ( ph -> ( E. x E. y ps <-> E. x E. y ch ) ) $=
      ( wex exbidv ) ABEGCEGDABCEFHH $.
  $}

  ${
    $d x ph $.  $d y ph $.  $d z ph $.
    3exbidv.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for 3 existential quantifiers (deduction rule).
       (Contributed by NM, 1-May-1995.) $)
    3exbidv $p |- ( ph -> ( E. x E. y E. z ps <-> E. x E. y E. z ch ) ) $=
      ( wex exbidv 2exbidv ) ABFHCFHDEABCFGIJ $.
  $}

  ${
    $d x ph $.  $d y ph $.  $d z ph $.  $d w ph $.
    4exbidv.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for 4 existential quantifiers (deduction rule).
       (Contributed by NM, 3-Aug-1995.) $)
    4exbidv $p |- ( ph ->
                     ( E. x E. y E. z E. w ps <-> E. x E. y E. z E. w ch ) ) $=
      ( wex 2exbidv ) ABGIFICGIFIDEABCFGHJJ $.
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
    $d x ps $.
    exlimiv.1 $e |- ( ph -> ps ) $.
    $( Inference from Theorem 19.23 of [Margaris] p. 90.

       This inference, along with our many variants such as ~ rexlimdv , is
       used to implement a metatheorem called "Rule C" that is given in many
       logic textbooks.  See, for example, Rule C in [Mendelson] p. 81, Rule C
       in [Margaris] p. 40, or Rule C in Hirst and Hirst's _A Primer for Logic
       and Proof_ p. 59 (PDF p. 65) at
       ~ http://www.mathsci.appstate.edu/~~hirstjl/primer/hirst.pdf .

       In informal proofs, the statement "Let ` C ` be an element such that..."
       almost always means an implicit application of Rule C.

       In essence, Rule C states that if we can prove that some element ` x `
       exists satisfying a wff, i.e. ` E. x ph ( x ) ` where ` ph ( x ) ` has
       ` x ` free, then we can use ` ph ( C ) ` as a hypothesis for the proof
       where ` C ` is a new (ficticious) constant not appearing previously in
       the proof, nor in any axioms used, nor in the theorem to be proved.  The
       purpose of Rule C is to get rid of the existential quantifier.

       We cannot do this in Metamath directly.  Instead, we use the original
       ` ph ` (containing ` x ` ) as an antecedent for the main part of the
       proof.  We eventually arrive at ` ( ph -> ps ) ` where ` ps ` is the
       theorem to be proved and does not contain ` x ` .  Then we apply
       ~ exlimiv to arrive at ` ( E. x ph -> ps ) ` .  Finally, we separately
       prove ` E. x ph ` and detach it with modus ponens ~ ax-mp to arrive at
       the final theorem ` ps ` .  (Contributed by NM, 5-Aug-1993.)  (Revised
       by Wolf Lammen to remove dependency on ax-9 and ax-8, 4-Dec-2017.) $)
    exlimiv $p |- ( E. x ph -> ps ) $=
      ( wex eximi ax17e syl ) ACEBCEBABCDFBCGH $.
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
    $d x ch $.  $d x ph $.
    exlimdv.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction from Theorem 19.23 of [Margaris] p. 90.  Revised to remove
       dependency on ~ ax-9 and ~ ax-8 .  (Contributed by NM, 27-Apr-1994.)
       (Revised by Wolf Lammen, 4-Dec-2017.) $)
    exlimdv $p |- ( ph -> ( E. x ps -> ch ) ) $=
      ( wex eximdv ax17e syl6 ) ABDFCDFCABCDEGCDHI $.
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

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Equality predicate; define substitution
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( --- Start of patch to prevent connective overloading $)
  $c class $.

  $( Add 'class' as a typecode. $)
  $( $j syntax 'class'; $)

  $( This syntax construction states that a variable ` x ` , which has been
     declared to be a set variable by $f statement vx, is also a class
     expression.  This can be justified informally as follows.  We know that
     the class builder ` { y | y e. x } ` is a class by ~ cab .  Since (when
     ` y ` is distinct from ` x ` ) we have ` x = { y | y e. x } ` by
     ~ cvjust , we can argue that the syntax " ` class x ` " can be viewed as
     an abbreviation for " ` class { y | y e. x } ` ".  See the discussion
     under the definition of class in [Jech] p. 4 showing that "Every set can
     be considered to be a class."

     While it is tempting and perhaps occasionally useful to view ~ cv as a
     "type conversion" from a set variable to a class variable, keep in mind
     that ~ cv is intrinsically no different from any other class-building
     syntax such as ~ cab , ~ cun , or ~ c0 .

     For a general discussion of the theory of classes and the role of ~ cv ,
     see ~ http://us.metamath.org/mpeuni/mmset.html#class .

     (The description above applies to set theory, not predicate calculus.  The
     purpose of introducing ` class x ` here, and not in set theory where it
     belongs, is to allow us to express i.e.  "prove" the ~ weq of predicate
     calculus from the ~ wceq of set theory, so that we don't "overload" the
     ` = ` connective with two syntax definitions.  This is done to prevent
     ambiguity that would complicate some Metamath parsers.) $)
  cv $a class x $.
  $( --- End of patch to prevent connective overloading $)

  $( --- Start of old code before overloading prevention patch. $)
  $(          (None - the above patch had no old code.) $)
  $( --- End of old code before overloading prevention patch. $)

  $( Declare the equality predicate symbol. $)
  $c = $.  $( Equal sign (read:  'is equal to') $)

  $( --- Start of patch to prevent connective overloading $)
  ${
    $v A $.
    $v B $.
    wceq.cA $f class A $.
    wceq.cB $f class B $.
    $( Extend wff definition to include class equality.

       For a general discussion of the theory of classes, see
       ~ http://us.metamath.org/mpeuni/mmset.html#class .

       (The purpose of introducing ` wff A = B ` here, and not in set theory
       where it belongs, is to allow us to express i.e.  "prove" the ~ weq of
       predicate calculus in terms of the ~ wceq of set theory, so that we
       don't "overload" the ` = ` connective with two syntax definitions.  This
       is done to prevent ambiguity that would complicate some Metamath
       parsers.  For example, some parsers - although not the Metamath program
       - stumble on the fact that the ` = ` in ` x = y ` could be the ` = ` of
       either ~ weq or ~ wceq , although mathematically it makes no
       difference.  The class variables ` A ` and ` B ` are introduced
       temporarily for the purpose of this definition but otherwise not used in
       predicate calculus.  See ~ df-cleq for more information on the set
       theory usage of ~ wceq .) $)
    wceq $a wff A = B $.
  $}

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
  $( --- End of patch to prevent connective overloading $)

  $( --- Start of old code before overloading prevention patch. $)
  $(
  @( Extend wff definition to include atomic formulas using the equality
     predicate.

     After we introduce ~ cv and ~ wceq in set theory, this syntax construction
     becomes redundant, since it can be derived with the proof
     "vx cv vy cv wceq". @)
  weq @a wff x = y @.
  $)
  $( --- End of old code before overloading prevention patch. $)

  $( Lemma used in proofs of substitution properties.  (Contributed by NM,
     5-Aug-1993.) $)
  equs3 $p |- ( E. x ( x = y /\ ph ) <-> -. A. x ( x = y -> -. ph ) ) $=
    ( weq wn wi wal wa wex alinexa con2bii ) BCDZAEFBGLAHBILABJK $.

  ${
    speimfw.2 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( Specialization, with additional weakening to allow bundling of ` x ` and
       ` y ` .  Uses only Tarski's FOL axiom schemes.  (Contributed by NM,
       23-Apr-2017.)  (Proof shortened by Wolf Lammen, 5-Aug-2017.) $)
    speimfw $p |- ( -. A. x -. x = y -> ( A. x ph -> E. x ps ) ) $=
      ( weq wex wi wn wal eximi df-ex 19.35 3imtr3i ) CDFZCGABHZCGOICJIACJBCGHO
      PCEKOCLABCMN $.
  $}

  ${
    spimfw.1 $e |- ( -. ps -> A. x -. ps ) $.
    spimfw.2 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( Specialization, with additional weakening to allow bundling of ` x ` and
       ` y ` .  Uses only Tarski's FOL axiom schemes.  (Contributed by NM,
       23-Apr-1017.)  (Proof shortened by Wolf Lammen, 7-Aug-2017.) $)
    spimfw $p |- ( -. A. x -. x = y -> ( A. x ph -> ps ) ) $=
      ( weq wn wal wex speimfw df-ex con1i sylbi syl6 ) CDGHCIHACIBCJZBABCDFKPB
      HCIZHBBCLBQEMNO $.
  $}

  ${
    ax11i.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    ax11i.2 $e |- ( ps -> A. x ps ) $.
    $( Inference that has ~ ax-11 (without ` A. y ` ) as its conclusion.  Uses
       only Tarski's FOL axiom schemes.  The hypotheses may be eliminable
       without one or more of these axioms in special cases.  Proof similar to
       Lemma 16 of [Tarski] p. 70.  (Contributed by NM, 20-May-2008.) $)
    ax11i $p |- ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) $=
      ( weq wi wal biimprcd alrimih syl6bi ) CDGZABMAHZCIEBNCFMABEJKL $.
  $}

  $c [ $. $( Left bracket $)
  $c / $. $( Slash. $)
  $c ] $.  $( Right bracket $)

  $( Extend wff definition to include proper substitution (read "the wff that
     results when ` y ` is properly substituted for ` x ` in wff ` ph ` ").
     (Contributed by NM, 24-Jan-2006.) $)
  wsb $a wff [ y / x ] ph $.

  $( Define proper substitution.  Remark 9.1 in [Megill] p. 447 (p. 15 of the
     preprint).  For our notation, we use ` [ y / x ] ph ` to mean "the wff
     that results from the proper substitution of ` y ` for ` x ` in the wff
     ` ph ` ."  We can also use ` [ y / x ] ph ` in place of the "free for"
     side condition used in traditional predicate calculus; see, for example,
     ~ stdpc4 .

     Our notation was introduced in Haskell B. Curry's _Foundations of
     Mathematical Logic_ (1977), p. 316 and is frequently used in textbooks of
     lambda calculus and combinatory logic.  This notation improves the common
     but ambiguous notation, " ` ph ( y ) ` is the wff that results when ` y `
     is properly substituted for ` x ` in ` ph ( x ) ` ."  For example, if the
     original ` ph ( x ) ` is ` x = y ` , then ` ph ( y ) ` is ` y = y ` , from
     which we obtain that ` ph ( x ) ` is ` x = x ` .  So what exactly does
     ` ph ( x ) ` mean?  Curry's notation solves this problem.

     In most books, proper substitution has a somewhat complicated recursive
     definition with multiple cases based on the occurrences of free and bound
     variables in the wff.  Instead, we use a single formula that is exactly
     equivalent and gives us a direct definition.  We later prove that our
     definition has the properties we expect of proper substitution (see
     theorems ~ sbequ , ~ sbcom2 and ~ sbid2v ).

     Note that our definition is valid even when ` x ` and ` y ` are replaced
     with the same variable, as ~ sbid shows.  We achieve this by having ` x `
     free in the first conjunct and bound in the second.  We can also achieve
     this by using a dummy variable, as the alternate definition ~ dfsb7 shows
     (which some logicians may prefer because it doesn't mix free and bound
     variables).  Another version that mixes free and bound variables is
     ~ dfsb3 .  When ` x ` and ` y ` are distinct, we can express proper
     substitution with the simpler expressions of ~ sb5 and ~ sb6 .

     There are no restrictions on any of the variables, including what
     variables may occur in wff ` ph ` .  (Contributed by NM, 5-Aug-1993.) $)
  df-sb $a |- ( [ y / x ] ph <->
              ( ( x = y -> ph ) /\ E. x ( x = y /\ ph ) ) ) $.

  $( An equality theorem for substitution.  (Contributed by NM, 5-Aug-1993.)
     (Proof shortened by Wolf Lammen, 25-Feb-2018.) $)
  sbequ2 $p |- ( x = y -> ( [ y / x ] ph -> ph ) ) $=
    ( wsb weq wi wa wex df-sb simplbi com12 ) ABCDZBCEZALMAFMAGBHABCIJK $.

  $( Obsolete proof of ~ sbequ2 as of 25-Feb-2018.  (Contributed by NM,
     5-Aug-1993.)  (New usage is discouraged.)
     (Proof modification is discouraged.) $)
  sbequ2OLD $p |- ( x = y -> ( [ y / x ] ph -> ph ) ) $=
    ( wsb weq wi wa wex df-sb simpl com12 syl5bi ) ABCDBCEZAFZMAGBHZGZMAABCIPMA
    NOJKL $.

  $( One direction of a simplified definition of substitution.  (Contributed by
     NM, 5-Aug-1993.) $)
  sb1 $p |- ( [ y / x ] ph -> E. x ( x = y /\ ph ) ) $=
    ( wsb weq wi wa wex df-sb simprbi ) ABCDBCEZAFKAGBHABCIJ $.

  $( A specialization theorem.  (Contributed by NM, 5-Aug-1993.)  (Proof
     shortened by Wolf Lammen, 3-May-2018.) $)
  spsbe $p |- ( [ y / x ] ph -> E. x ph ) $=
    ( wsb weq wa wex sb1 exsimpr syl ) ABCDBCEZAFBGABGABCHKABIJ $.

  $( Elimination of equality from antecedent after substitution.  Revised to
     minimize dependencies.  (Contributed by NM, 5-Aug-1993.)  (Revised by Wolf
     Lammen, 28-Jul-2018.) $)
  sbequ8 $p |- ( [ y / x ] ph <-> [ y / x ] ( x = y -> ph ) ) $=
    ( weq wi wa wex wsb pm5.4 bicomi abai exbii anbi12i df-sb 3bitr4i ) BCDZAEZ
    PAFZBGZFPQEZPQFZBGZFABCHQBCHQTSUBTQPAIJRUABPAKLMABCNQBCNO $.

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

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                Axiom scheme ax-9 (Existence)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Axiom of Existence.  One of the equality and substitution axioms of
     predicate calculus with equality.  This axiom tells us is that at least
     one thing exists.  In this form (not requiring that ` x ` and ` y ` be
     distinct) it was used in an axiom system of Tarski (see Axiom B7' in
     footnote 1 of [KalishMontague] p. 81.)  It is equivalent to axiom scheme
     C10' in [Megill] p. 448 (p. 16 of the preprint); the equivalence is
     established by ~ ax9o and ~ ax9from9o .  A more convenient form of this
     axiom is ~ a9e , which has additional remarks.

     Raph Levien proved the independence of this axiom from the other logical
     axioms on 12-Apr-2005.  See item 16 at
     ~ http://us.metamath.org/award2003.html .

     ~ ax-9 can be proved from the weaker version ~ ax9v requiring that the
     variables be distinct; see theorem ~ ax9 .

     ~ ax-9 can also be proved from the Axiom of Separation (in the form that
     we use that axiom, where free variables are not universally quantified).
     See theorem ~ ax9vsep .

     Except by ~ ax9v , this axiom should not be referenced directly.  Instead,
     use theorem ~ ax9 .  (Contributed by NM, 5-Aug-1993.)
     (New usage is discouraged.) $)
  ax-9 $a |- -. A. x -. x = y $.

  ${
    $d x y $.
    $( Axiom B7 of [Tarski] p. 75, which requires that ` x ` and ` y ` be
       distinct.  This trivial proof is intended merely to weaken axiom ~ ax-9
       by adding a distinct variable restriction.  From here on, ~ ax-9 should
       not be referenced directly by any other proof, so that theorem ~ ax9
       will show that we can recover ~ ax-9 from this weaker version if it were
       an axiom (as it is in the case of Tarski).

       Note:  Introducing ` x , y ` as a distinct variable group "out of the
       blue" with no apparent justification has puzzled some people, but it is
       perfectly sound.  All we are doing is adding an additional redundant
       requirement, no different from adding a redundant logical hypothesis,
       that results in a weakening of the theorem.  This means that any
       _future_ theorem that references ~ ax9v must have a $d specified for the
       two variables that get substituted for ` x ` and ` y ` .  The $d does
       not propagate "backwards" i.e. it does not impose a requirement on
       ~ ax-9 .

       When possible, use of this theorem rather than ~ ax9 is preferred since
       its derivation from axioms is much shorter.  (Contributed by NM,
       7-Aug-2015.) $)
    ax9v $p |- -. A. x -. x = y $=
      ( ax-9 ) ABC $.
  $}

  ${
    $d x y $.
    $( At least one individual exists.  Weaker version of ~ a9e .  When
       possible, use of this theorem rather than ~ a9e is preferred since its
       derivation from axioms is much shorter.  (Contributed by NM,
       3-Aug-2017.) $)
    a9ev $p |- E. x x = y $=
      ( weq wex wn wal ax9v df-ex mpbir ) ABCZADJEAFEABGJAHI $.
  $}

  ${
    $d x y $.
    exiftru.1 $e |- ph $.
    $( A companion rule to ax-gen, valid only if an individual exists.  Unlike
       ~ ax-9 , it does not require equality on its interface.  Some
       fundamental theorems of predicate logic can be proven from ~ ax-gen ,
       ~ ax-5 and this theorem alone, not requiring ~ ax-8 or excessive
       distinct variable conditions.  (Contributed by Wolf Lammen,
       12-Nov-2017.)  (Proof shortened by Wolf Lammen, 9-Dec-2017.) $)
    exiftru $p |- E. x ph $=
      ( vy weq a9ev a1i eximii ) BDEZABBDFAICGH $.
  $}

  ${
    $d x y $.
    exiftruOLD.1 $e |- ph $.
    $( Obsolete proof of ~ exiftru as of 9-Dec-2017.  (Contributed by Wolf
       Lammen, 12-Nov-2017.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    exiftruOLD $p |- E. x ph $=
      ( vy wex weq wi wal a9ev a1i 19.35ri id 2th exbii mpbir ) ABEBDFZPGZBEPPB
      PBEPBHBDIJKAQBAQCPLMNO $.
  $}

  $( Theorem 19.2 of [Margaris] p. 89.  Note:  This proof is very different
     from Margaris' because we only have Tarski's FOL axiom schemes available
     at this point.  See the later ~ 19.2g for a more conventional proof.
     Revised to remove dependency on ~ ax-8 .  (Contributed by NM,
     2-Aug-2017.)  (Revised by Wolf Lammen, 4-Dec-2017.) $)
  19.2 $p |- ( A. x ph -> E. x ph ) $=
    ( wi id exiftru 19.35i ) AABAACBADEF $.

  ${
    19.8w.1 $e |- ( ph -> A. x ph ) $.
    $( Weak version of ~ 19.8a .  Uses only Tarski's FOL axiom schemes.
       (Contributed by NM, 1-Aug-2017.)  (Proof shortened by Wolf Lammen,
       4-Dec-2017.) $)
    19.8w $p |- ( ph -> E. x ph ) $=
      ( wal wex 19.2 syl ) AABDABECABFG $.
  $}

  $( Theorem 19.39 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)
  19.39 $p |- ( ( E. x ph -> E. x ps ) -> E. x ( ph -> ps ) ) $=
    ( wex wi wal 19.2 imim1i 19.35 sylibr ) ACDZBCDZEACFZLEABECDMKLACGHABCIJ $.

  $( Theorem 19.24 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)
  19.24 $p |- ( ( A. x ph -> A. x ps ) -> E. x ( ph -> ps ) ) $=
    ( wal wi wex 19.2 imim2i 19.35 sylibr ) ACDZBCDZEKBCFZEABECFLMKBCGHABCIJ $.

  $( Theorem 19.34 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)
  19.34 $p |- ( ( A. x ph \/ E. x ps ) -> E. x ( ph \/ ps ) ) $=
    ( wal wex wo 19.2 orim1i 19.43 sylibr ) ACDZBCEZFACEZLFABFCEKMLACGHABCIJ $.

  ${
    $d x ph $.
    $( Special case of Theorem 19.9 of [Margaris] p. 89.  Revised to remove
       dependency on ~ ax-8 .  (Contributed by NM, 28-May-1995.)  (Revised by
       NM, 1-Aug-2017.)  (Revised by Wolf Lammen, 4-Dec-2017.) $)
    19.9v $p |- ( E. x ph <-> ph ) $=
      ( wex ax17e ax-17 19.8w impbii ) ABCAABDABABEFG $.

    $( Special case of Theorem 19.3 of [Margaris] p. 89.  Revised to remove
       dependency on ~ ax-8 .  (Contributed by NM, 1-Aug-2017.)  (Revised by
       Wolf Lammen, 4-Dec-2017.) $)
    19.3v $p |- ( A. x ph <-> ph ) $=
      ( wal wn wex alex 19.9v con2bii bitr4i ) ABCADZBEZDAABFKAJBGHI $.

    $( Version of ~ sp when ` x ` does not occur in ` ph ` .  This provides the
       other direction of ~ ax-17 .  Uses only Tarski's FOL axiom schemes.
       (Contributed by NM, 10-Apr-2017.)  (Proof shortened by Wolf Lammen,
       4-Dec-2017.) $)
    spvw $p |- ( A. x ph -> ph ) $=
      ( wal 19.3v biimpi ) ABCAABDE $.
  $}

  ${
    $d x z $.
    spimeh.1 $e |- ( ph -> A. x ph ) $.
    spimeh.2 $e |- ( x = z -> ( ph -> ps ) ) $.
    $( Existential introduction, using implicit substitution.  Compare Lemma 14
       of [Tarski] p. 70.  (Contributed by NM, 7-Aug-1994.)  (Proof shortened
       by Wolf Lammen, 10-Dec-2017.) $)
    spimeh $p |- ( ph -> E. x ps ) $=
      ( wal wex weq wi a9ev eximii 19.35i syl ) AACGBCHEABCCDIABJCCDKFLMN $.
  $}

  ${
    $d x y $.
    spimw.1 $e |- ( -. ps -> A. x -. ps ) $.
    spimw.2 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( Specialization.  Lemma 8 of [KalishMontague] p. 87.  Uses only Tarski's
       FOL axiom schemes.  (Contributed by NM, 19-Apr-2017.)  (Proof shortened
       by Wolf Lammen, 7-Aug-2017.) $)
    spimw $p |- ( A. x ph -> ps ) $=
      ( weq wn wal wi ax9v spimfw ax-mp ) CDGHCIHACIBJCDKABCDEFLM $.
  $}

  ${
    $d x y $.  $d x ps $.
    spimvw.1 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( Specialization.  Lemma 8 of [KalishMontague] p. 87.  Uses only Tarski's
       FOL axiom schemes.  (Contributed by NM, 9-Apr-2017.) $)
    spimvw $p |- ( A. x ph -> ps ) $=
      ( wn ax-17 spimw ) ABCDBFCGEH $.
  $}

  ${
    $d x y $.  $d y ph $.
    spnfw.1 $e |- ( -. ph -> A. x -. ph ) $.
    $( Weak version of ~ sp .  Uses only Tarski's FOL axiom schemes.
       (Contributed by NM, 1-Aug-2017.)  (Proof shortened by Wolf Lammen,
       13-Aug-2017.) $)
    spnfw $p |- ( A. x ph -> ph ) $=
      ( vy weq idd spimw ) AABDCBDEAFG $.
  $}

  ${
    sptruw.1 $e |- ph $.
    $( Version of ~ sp when ` ph ` is true.  Uses only Tarski's FOL axiom
       schemes.  (Contributed by NM, 23-Apr-1017.) $)
    sptruw $p |- ( A. x ph -> ph ) $=
      ( wal a1i ) AABDCE $.
  $}

  ${
    spfalw.1 $e |- -. ph $.
    $( Version of ~ sp when ` ph ` is false.  Uses only Tarski's FOL axiom
       schemes.  (Contributed by NM, 23-Apr-1017.)  (Proof shortened by Wolf
       Lammen, 25-Dec-2017.) $)
    spfalw $p |- ( A. x ph -> ph ) $=
      ( wn hbth spnfw ) ABADBCEF $.
  $}

  ${
    $d x y $.
    cbvaliw.1 $e |- ( A. x ph -> A. y A. x ph ) $.
    cbvaliw.2 $e |- ( -. ps -> A. x -. ps ) $.
    cbvaliw.3 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( Change bound variable.  Uses only Tarski's FOL axiom schemes.  Part of
       Lemma 7 of [KalishMontague] p. 86.  (Contributed by NM, 19-Apr-2017.) $)
    cbvaliw $p |- ( A. x ph -> A. y ps ) $=
      ( wal spimw alrimih ) ACHBDEABCDFGIJ $.
  $}

  ${
    $d x y $.  $d x ps $.  $d y ph $.
    cbvalivw.1 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( Change bound variable.  Uses only Tarski's FOL axiom schemes.  Part of
       Lemma 7 of [KalishMontague] p. 86.  (Contributed by NM, 9-Apr-2017.) $)
    cbvalivw $p |- ( A. x ph -> A. y ps ) $=
      ( wal spimvw alrimiv ) ACFBDABCDEGH $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                   Axiom scheme ax-8 (Equality)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Axiom of Equality.  One of the equality and substitution axioms of
     predicate calculus with equality.  This is similar to, but not quite, a
     transitive law for equality (proved later as ~ equtr ).  This axiom scheme
     is a sub-scheme of Axiom Scheme B8 of system S2 of [Tarski], p. 75, whose
     general form cannot be represented with our notation.  Also appears as
     Axiom C7 of [Monk2] p. 105 and Axiom Scheme C8' in [Megill] p. 448 (p. 16
     of the preprint).

     The equality symbol was invented in 1527 by Robert Recorde.  He chose a
     pair of parallel lines of the same length because "noe .2. thynges, can be
     moare equalle."

     Note that this axiom is still valid even when any two or all three of
     ` x ` , ` y ` , and ` z ` are replaced with the same variable since they
     do not have any distinct variable (Metamath's $d) restrictions.  Because
     of this, we say that these three variables are "bundled" (a term coined by
     Raph Levien).  (Contributed by NM, 5-Aug-1993.) $)
  ax-8 $a |- ( x = y -> ( x = z -> y = z ) ) $.

  ${
    $d x y $.
    $( Identity law for equality.  Lemma 2 of [KalishMontague] p. 85.  See also
       Lemma 6 of [Tarski] p. 68.  (Contributed by NM, 1-Apr-2005.)  (Revised
       by NM, 9-Apr-2017.)  (Proof shortened by Wolf Lammen, 5-Feb-2018.) $)
    equid $p |- x = x $=
      ( vy weq wex a9ev ax-8 pm2.43i eximii ax17e ax-mp ) AACZBDKBACZKBBAELKBAA
      FGHKBIJ $.
  $}

  ${
    $d x y $.
    $( Obsolete proof of ~ equid as of 9-Dec-2017.  (Contributed by NM,
       1-Apr-2005.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    equidOLD $p |- x = x $=
      ( vy weq wn wal ax9v ax-8 pm2.43i con3i alimi mto ax-17 mt3 ) AACZNDZBEZP
      BACZDZBEBAFORBQNQNBAAGHIJKOBLM $.
  $}

  $( Bound-variable hypothesis builder for ` x = x ` .  This theorem tells us
     that any variable, including ` x ` , is effectively not free in
     ` x = x ` , even though ` x ` is technically free according to the
     traditional definition of free variable.  (Contributed by NM,
     13-Jan-2011.)  (Revised by NM, 21-Aug-2017.) $)
  nfequid $p |- F/ y x = x $=
    ( weq equid nfth ) AACBADE $.

  ${
    $d x w $.
    $( Commutative law for equality.  Lemma 3 of [KalishMontague] p. 85.  See
       also Lemma 7 of [Tarski] p. 69.  (Contributed by NM, 5-Aug-1993.)
       (Revised by NM, 9-Apr-2017.) $)
    equcomi $p |- ( x = y -> y = x ) $=
      ( weq equid ax-8 mpi ) ABCAACBACADABAEF $.
  $}

  $( Commutative law for equality.  (Contributed by NM, 20-Aug-1993.) $)
  equcom $p |- ( x = y <-> y = x ) $=
    ( weq equcomi impbii ) ABCBACABDBADE $.

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

  $( An equivalence law for equality.  (Contributed by NM, 5-Aug-1993.)  (Proof
     shortened by Wolf Lammen, 10-Dec-2017.) $)
  equequ1 $p |- ( x = y -> ( x = z <-> y = z ) ) $=
    ( weq ax-8 equtr impbid ) ABDACDBCDABCEABCFG $.

  $( Obsolete version of ~ equequ1 as of 12-Nov-2017.  (Contributed by NM,
     5-Aug-1993.)  (New usage is discouraged.)
     (Proof modification is discouraged.) $)
  equequ1OLD $p |- ( x = y -> ( x = z <-> y = z ) ) $=
    ( weq ax-8 wi equcomi syl impbid ) ABDZACDZBCDZABCEJBADLKFABGBACEHI $.

  $( An equivalence law for equality.  (Contributed by NM, 5-Aug-1993.)  (Proof
     shortened by Wolf Lammen, 4-Aug-2017.) $)
  equequ2 $p |- ( x = y -> ( z = x <-> z = y ) ) $=
    ( weq equequ1 equcom 3bitr3g ) ABDACDBCDCADCBDABCEACFBCFG $.

  $( One of the two equality axioms of standard predicate calculus, called
     reflexivity of equality.  (The other one is ~ stdpc7 .)  Axiom 6 of
     [Mendelson] p. 95.  Mendelson doesn't say why he prepended the redundant
     quantifier, but it was probably to be compatible with free logic (which is
     valid in the empty domain).  (Contributed by NM, 16-Feb-2005.) $)
  stdpc6 $p |- A. x x = x $=
    ( weq equid ax-gen ) AABAACD $.

  $( A transitive law for equality.  (Contributed by NM, 12-Aug-1993.)  (Proof
     shortened by Andrew Salmon, 25-May-2011.) $)
  equtr2 $p |- ( ( x = z /\ y = z ) -> x = y ) $=
    ( weq wi equtrr equcoms impcom ) BCDACDZABDZIJECBCBAFGH $.

  $( Two equivalent ways of expressing ~ ax-12 .  See the comment for
     ~ ax-12 .  (Contributed by NM, 2-May-2017.)  (Proof shortened by Wolf
     Lammen, 26-Feb-2018.) $)
  ax12b $p |- ( ( -. x = y -> ( y = z -> A. x y = z ) )
     <-> ( -. x = y -> ( -. x = z -> ( y = z -> A. x y = z ) ) ) ) $=
    ( weq wn wal ax-1 equtrr equcoms con3rr3 imim1d pm2.43 syl6 impbid2 pm5.74i
    wi ) ABDZEZBCDZSAFZPZACDZEZUAPZRUAUDUAUCGRUDSUAPUARSUCUASUBQUBQPCBCBAHIJKST
    LMNO $.

  $( Obsolete version of ~ ax12b as of 12-Aug-2017.  (Contributed by NM,
     2-May-2017.)  (New usage is discouraged.)
     (Proof modification is discouraged.) $)
  ax12bOLD $p |- ( ( -. x = y -> ( y = z -> A. x y = z ) )
     <-> ( -. x = y -> ( -. x = z -> ( y = z -> A. x y = z ) ) ) ) $=
    ( weq wn wal wi wa bi2.04 equtrr equcoms con3d pm4.71d imbi1d pm5.74i bitri
    impexp ) ABDZEZBCDZTAFZGZGZSACDZEZHZUBGZSUEUBGGUCTUFUAGZGZUGUCTSUAGZGUISTUA
    ITUJUHTSUFUATSUETUDRUDRGCBCBAJKLMNOPTUFUAIPSUEUBQP $.

  ${
    $d x y $.
    spfw.1 $e |- ( -. ps -> A. x -. ps ) $.
    spfw.2 $e |- ( A. x ph -> A. y A. x ph ) $.
    spfw.3 $e |- ( -. ph -> A. y -. ph ) $.
    spfw.4 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Weak version of ~ sp .  Uses only Tarski's FOL axiom schemes.  Lemma 9
       of [KalishMontague] p. 87.  This may be the best we can do with minimal
       distinct variable conditions.  TO DO:  Do we need this theorem?  If not,
       maybe it should be deleted.  (Contributed by NM, 19-Apr-2017.) $)
    spfw $p |- ( A. x ph -> ph ) $=
      ( wal wi ax-5 weq biimprd equcoms spimw syl56 biimpd mpg ) ACIZBJZSAJDSSD
      ITDIBDIAFSBDKBADCGBAJCDCDLZABHMNOPABCDEUAABHQOR $.
  $}

  ${
    $d x y $.  $d y ph $.
    spnfw.3 $e |- ( -. ph -> A. x -. ph ) $.
    $( Weak version of ~ sp .  Uses only Tarski's FOL axiom schemes.  Obsolete
       version of ~ spnfw as of 13-Aug-2017.  (Contributed by NM, 1-Aug-2017.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    spnfwOLD $p |- ( A. x ph -> ph ) $=
      ( vy wal ax-17 wn weq biidd spfw ) AABDCABEDFAGDFBDHAIJ $.
  $}

  ${
    19.8wOLD.1 $e |- ( ph -> A. x ph ) $.
    $( Obsolete version of ~ 19.8w as of 4-Dec-2017.  (Contributed by NM,
       1-Aug-2017.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    19.8wOLD $p |- ( ph -> E. x ph ) $=
      ( wn wal wex notnot albii 3imtr3i spnfw con2i df-ex sylibr ) AADZBEZDABFO
      ANBAABENDZPBECAGZAPBQHIJKABLM $.
  $}

  ${
    $d x y $.  $d x ps $.  $d y ph $.
    spw.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Weak version of specialization scheme ~ sp .  Lemma 9 of
       [KalishMontague] p. 87.  While it appears that ~ sp in its general form
       does not follow from Tarski's FOL axiom schemes, from this theorem we
       can prove any instance of ~ sp having no wff metavariables and mutually
       distinct set variables (see ~ ax11wdemo for an example of the procedure
       to eliminate the hypothesis).  Other approximations of ~ sp are ~ spfw
       (minimal distinct variable requirements), ~ spnfw (when ` x ` is not
       free in ` -. ph ` ), ~ spvw (when ` x ` does not appear in ` ph ` ),
       ~ sptruw (when ` ph ` is true), and ~ spfalw (when ` ph ` is false).
       (Contributed by NM, 9-Apr-2017.)  (Proof shortened by Wolf Lammen,
       27-Feb-2018.) $)
    spw $p |- ( A. x ph -> ph ) $=
      ( wn ax-17 wal spfw ) ABCDBFCGACHDGAFDGEI $.
    $( Obsolete proof of ~ spw as of 27-Feb-2018.  (Contributed by NM,
       9-Apr-2017.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    spwOLD $p |- ( A. x ph -> ph ) $=
      ( wal wi ax-17 ax-5 weq biimprd equcoms spimvw syl56 biimpd mpg ) ACFZBGZ
      QAGDQQDFRDFBDFAQDHQBDIBADCBAGCDCDJZABEKLMNABCDSABEOMP $.
  $}

  ${
    $d x y ph $.
    $( Obsolete version of ~ spvw as of 4-Dec-2017.  (Contributed by NM,
       10-Apr-2017.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    spvwOLD $p |- ( A. x ph -> ph ) $=
      ( vy weq biidd spw ) AABCBCDAEF $.

    $( Obsolete version of ~ 19.3v as of 4-Dec-2017.  (Contributed by NM,
       1-Aug-2017.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    19.3vOLD $p |- ( A. x ph <-> ph ) $=
      ( wal spvw ax-17 impbii ) ABCAABDABEF $.

    $( Obsolete version of ~ 19.9v as of 4-Dec-2017.  (Contributed by NM,
       28-May-1995.)  (Revised by NM, 1-Aug-2017.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    19.9vOLD $p |- ( E. x ph <-> ph ) $=
      ( wex wn wal df-ex 19.3v con2bii bitr4i ) ABCADZBEZDAABFKAJBGHI $.
  $}

  ${
    $d x ps $.
    exlimivOLD.1 $e |- ( ph -> ps ) $.
    $( Obsolete version of ~ exlimiv as of 4-Dec-2017.  (Contributed by NM,
       5-Aug-1993.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    exlimivOLD $p |- ( E. x ph -> ps ) $=
      ( wex eximi 19.9v sylib ) ACEBCEBABCDFBCGH $.
  $}

  ${
    $d x y $.  $d y ph $.
    spfalwOLD.1 $e |- -. ph $.
    $( Obsolete proof of ~ spfalw as of 25-Dec-2017.  (Contributed by NM,
       23-Apr-1017.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    spfalwOLD $p |- ( A. x ph -> ph ) $=
      ( vy wfal wb weq bifal a1i spw ) AEBDAEFBDGACHIJ $.
  $}

  $( Obsolete version of ~ 19.2 as of 4-Dec-2017.  (Contributed by NM,
     2-Aug-2017.)  (New usage is discouraged.)
     (Proof modification is discouraged.) $)
  19.2OLD $p |- ( A. x ph -> E. x ph ) $=
    ( weq wn wal wex wi equid notnoti spfalw mt2 idd speimfw ax-mp ) BBCZDZBEZD
    ABEABFGQOBHZPBORIJKAABBOALMN $.

  ${
    $d x y $.
    cbvalw.1 $e |- ( A. x ph -> A. y A. x ph ) $.
    cbvalw.2 $e |- ( -. ps -> A. x -. ps ) $.
    cbvalw.3 $e |- ( A. y ps -> A. x A. y ps ) $.
    cbvalw.4 $e |- ( -. ph -> A. y -. ph ) $.
    cbvalw.5 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Change bound variable.  Uses only Tarski's FOL axiom schemes.
       (Contributed by NM, 9-Apr-2017.) $)
    cbvalw $p |- ( A. x ph <-> A. y ps ) $=
      ( wal weq biimpd cbvaliw wi biimprd equcoms impbii ) ACJBDJABCDEFCDKZABIL
      MBADCGHBANCDRABIOPMQ $.
  $}

  ${
    $d x y $.  $d x ps $.  $d y ph $.
    cbvalvw.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Change bound variable.  Uses only Tarski's FOL axiom schemes.
       (Contributed by NM, 9-Apr-2017.)  (Proof shortened by Wolf Lammen,
       28-Feb-2018.) $)
    cbvalvw $p |- ( A. x ph <-> A. y ps ) $=
      ( wal ax-17 wn cbvalw ) ABCDACFDGBHCGBDFCGAHDGEI $.

    $( Change bound variable.  Uses only Tarski's FOL axiom schemes.
       (Contributed by NM, 9-Apr-2017.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    cbvalvwOLD $p |- ( A. x ph <-> A. y ps ) $=
      ( wal weq biimpd cbvalivw wi biimprd equcoms impbii ) ACFBDFABCDCDGZABEHI
      BADCBAJCDNABEKLIM $.

    $( Change bound variable.  Uses only Tarski's FOL axiom schemes.
       (Contributed by NM, 19-Apr-2017.) $)
    cbvexvw $p |- ( E. x ph <-> E. y ps ) $=
      ( wn wal wex weq notbid cbvalvw notbii df-ex 3bitr4i ) AFZCGZFBFZDGZFACHB
      DHPROQCDCDIABEJKLACMBDMN $.
  $}

  ${
    $d y z $.  $d x y $.  $d z ph $.  $d y ps $.
    alcomiw.1 $e |- ( y = z -> ( ph <-> ps ) ) $.
    $( Weak version of ~ alcom .  Uses only Tarski's FOL axiom schemes.
       (Contributed by NM, 10-Apr-2017.) $)
    alcomiw $p |- ( A. x A. y ph -> A. y A. x ph ) $=
      ( wal weq biimpd cbvalivw alimi ax-17 wi biimprd equcoms spimvw 3syl ) AD
      GZCGBEGZCGZTDGACGZDGRSCABDEDEHZABFIJKTDLTUADSACBAEDBAMDEUBABFNOPKKQ $.
  $}

  ${
    $d x y $.
    hbn1fw.1 $e |- ( A. x ph -> A. y A. x ph ) $.
    hbn1fw.2 $e |- ( -. ps -> A. x -. ps ) $.
    hbn1fw.3 $e |- ( A. y ps -> A. x A. y ps ) $.
    hbn1fw.4 $e |- ( -. ph -> A. y -. ph ) $.
    hbn1fw.5 $e |- ( -. A. y ps -> A. x -. A. y ps ) $.
    hbn1fw.6 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Weak version of ~ ax-6 from which we can prove any ~ ax-6 instance not
       involving wff variables or bundling.  Uses only Tarski's FOL axiom
       schemes.  (Contributed by NM, 19-Apr-2017.)  (Proof shortened by Wolf
       Lammen, 28-Feb-2018.) $)
    hbn1fw $p |- ( -. A. x ph -> A. x -. A. x ph ) $=
      ( wal wn cbvalw notbii biimpi biimpri alimi 3syl ) ACKZLZBDKZLZUBCKTCKTUB
      SUAABCDEFGHJMNZOIUBTCTUBUCPQR $.

    $( Obsolete proof of ~ hbn1fw as of 28-Feb-2018.  (Contributed by NM,
       19-Apr-2017.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    hbn1fwOLD $p |- ( -. A. x ph -> A. x -. A. x ph ) $=
      ( wal wn cbvalw biimpri con3i biimpi alimi 3syl ) ACKZLZBDKZLZUBCKTCKUASS
      UAABCDEFGHJMZNOIUBTCSUASUAUCPOQR $.
  $}

  ${
    $d y ph $.  $d x ps $.  $d x y $.
    hbn1w.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Weak version of ~ hbn1 .  Uses only Tarski's FOL axiom schemes.
       (Contributed by NM, 9-Apr-2017.) $)
    hbn1w $p |- ( -. A. x ph -> A. x -. A. x ph ) $=
      ( wal ax-17 wn hbn1fw ) ABCDACFDGBHCGBDFZCGAHDGJHCGEI $.

    $( Weak version of ~ hba1 .  See comments for ~ ax6w .  Uses only Tarski's
       FOL axiom schemes.  (Contributed by NM, 9-Apr-2017.) $)
    hba1w $p |- ( A. x ph -> A. x A. x ph ) $=
      ( wal wn weq wb cbvalvw a1i notbid spw con2i hbn1w con1i alimi 3syl ) ACF
      ZSGZCFZGZUBCFSCFUASTBDFZGZCDCDHZSUCSUCIUEABCDEJKLZMNTUDCDUFOUBSCSUAABCDEO
      PQR $.

    $( Weak version of ~ hbe1 .  See comments for ~ ax6w .  Uses only Tarski's
       FOL axiom schemes.  (Contributed by NM, 19-Apr-2017.) $)
    hbe1w $p |- ( E. x ph -> A. x E. x ph ) $=
      ( wex wn wal df-ex weq notbid hbn1w hbxfrbi ) ACFAGZCHGCACINBGCDCDJABEKLM
      $.
  $}

  ${
    $d x z $.  $d x y $.  $d z ph $.  $d x ps $.
    hbalw.1 $e |- ( x = z -> ( ph <-> ps ) ) $.
    hbalw.2 $e |- ( ph -> A. x ph ) $.
    $( Weak version of ~ hbal .  Uses only Tarski's FOL axiom schemes.  Unlike
       ~ hbal , this theorem requires that ` x ` and ` y ` be distinct i.e. are
       not bundled.  (Contributed by NM, 19-Apr-2017.) $)
    hbalw $p |- ( A. y ph -> A. x A. y ph ) $=
      ( wal alimi alcomiw syl ) ADHZACHZDHLCHAMDGIABDCEFJK $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                  Membership predicate
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Declare the membership predicate symbol. $)
  $c e. $. $( Stylized epsilon $)

  $( --- Start of patch to prevent connective overloading $)
  ${
    $v A $.
    $v B $.
    wcel.cA $f class A $.
    wcel.cB $f class B $.
    $( Extend wff definition to include the membership connective between
       classes.

       For a general discussion of the theory of classes, see
       ~ http://us.metamath.org/mpeuni/mmset.html#class .

       (The purpose of introducing ` wff A e. B ` here is to allow us to
       express i.e.  "prove" the ~ wel of predicate calculus in terms of the
       ~ wceq of set theory, so that we don't "overload" the ` e. ` connective
       with two syntax definitions.  This is done to prevent ambiguity that
       would complicate some Metamath parsers.  The class variables ` A ` and
       ` B ` are introduced temporarily for the purpose of this definition but
       otherwise not used in predicate calculus.  See ~ df-clab for more
       information on the set theory usage of ~ wcel .) $)
    wcel $a wff A e. B $.
  $}

  $( Extend wff definition to include atomic formulas with the epsilon
     (membership) predicate.  This is read " ` x ` is an element of
     ` y ` ," " ` x ` is a member of ` y ` ," " ` x ` belongs to ` y ` ,"
     or " ` y ` contains ` x ` ."  Note:  The phrase " ` y ` includes
     ` x ` " means " ` x ` is a subset of ` y ` ;" to use it also for
     ` x e. y ` , as some authors occasionally do, is poor form and causes
     confusion, according to George Boolos (1992 lecture at MIT).

     This syntactical construction introduces a binary non-logical predicate
     symbol ` e. ` (epsilon) into our predicate calculus.  We will eventually
     use it for the membership predicate of set theory, but that is irrelevant
     at this point: the predicate calculus axioms for ` e. ` apply to any
     arbitrary binary predicate symbol.  "Non-logical" means that the predicate
     is presumed to have additional properties beyond the realm of predicate
     calculus, although these additional properties are not specified by
     predicate calculus itself but rather by the axioms of a theory (in our
     case set theory) added to predicate calculus.  "Binary" means that the
     predicate has two arguments.

     (Instead of introducing ~ wel as an axiomatic statement, as was done in an
     older version of this database, we introduce it by "proving" a special
     case of set theory's more general ~ wcel .  This lets us avoid overloading
     the ` e. ` connective, thus preventing ambiguity that would complicate
     certain Metamath parsers.  However, logically ~ wel is considered to be a
     primitive syntax, even though here it is artificially "derived" from
     ~ wcel .  Note:  To see the proof steps of this syntax proof, type "show
     proof wel /all" in the Metamath program.)  (Contributed by NM,
     24-Jan-2006.) $)
  wel $p wff x e. y $=
    ( cv wcel ) ACBCD $.
  $( --- End of patch to prevent connective overloading $)

  $( --- Start of old code before overloading prevention patch. $)
  $(
  @( Extend wff definition to include atomic formulas with the epsilon
     (membership) predicate.  This is read " ` x ` is an element of ` y ` ,"
     " ` x ` is a member of ` y ` ," " ` x ` belongs to ` y ` ," or " ` y `
     contains ` x ` ."  Note:  The phrase " ` y ` includes ` x ` " means
     " ` x ` is a subset of ` y ` "; to use it also for ` x e. y ` (as some
     authors occasionally do) is poor form and causes confusion.

     After we introduce ~ cv and ~ wcel in set theory, this syntax construction
     becomes redundant, since it can be derived with the proof
     "vx cv vy cv wcel". @)
  wel @a wff x e. y @.
  $)
  $( --- End of old code before overloading prevention patch. $)

  $( Register class-to-set promotion and class equality and membership as
     primitive expressions. Although these are actually definitions, the above
     ambiguity prevention necessitates our taking class equality as the
     primitive, instead of set equality. $)
  $( $j primitive 'weq' 'wel'; $)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Axiom scheme ax-13 (Left Equality for Binary Predicate)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Axiom of Left Equality for Binary Predicate.  One of the equality and
     substitution axioms for a non-logical predicate in our predicate calculus
     with equality.  It substitutes equal variables into the left-hand side of
     an arbitrary binary predicate ` e. ` , which we will use for the set
     membership relation when set theory is introduced.  This axiom scheme is a
     sub-scheme of Axiom Scheme B8 of system S2 of [Tarski], p. 75, whose
     general form cannot be represented with our notation.  Also appears as
     Axiom scheme C12' in [Megill] p. 448 (p. 16 of the preprint).
     "Non-logical" means that the predicate is not a primitive of predicate
     calculus proper but instead is an extension to it.  "Binary" means that
     the predicate has two arguments.  In a system of predicate calculus with
     equality, like ours, equality is not usually considered to be a
     non-logical predicate.  In systems of predicate calculus without equality,
     it typically would be.  (Contributed by NM, 5-Aug-1993.) $)
  ax-13 $a |- ( x = y -> ( x e. z -> y e. z ) ) $.

  $( An identity law for the non-logical predicate.  (Contributed by NM,
     5-Aug-1993.) $)
  elequ1 $p |- ( x = y -> ( x e. z <-> y e. z ) ) $=
    ( weq wel ax-13 wi equcoms impbid ) ABDACEZBCEZABCFKJGBABACFHI $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Axiom scheme ax-14 (Right Equality for Binary Predicate)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Axiom of Right Equality for Binary Predicate.  One of the equality and
     substitution axioms for a non-logical predicate in our predicate calculus
     with equality.  It substitutes equal variables into the right-hand side of
     an arbitrary binary predicate ` e. ` , which we will use for the set
     membership relation when set theory is introduced.  This axiom scheme is a
     sub-scheme of Axiom Scheme B8 of system S2 of [Tarski], p. 75, whose
     general form cannot be represented with our notation.  Also appears as
     Axiom scheme C13' in [Megill] p. 448 (p. 16 of the preprint).
     (Contributed by NM, 5-Aug-1993.) $)
  ax-14 $a |- ( x = y -> ( z e. x -> z e. y ) ) $.

  $( An identity law for the non-logical predicate.  (Contributed by NM,
     5-Aug-1993.) $)
  elequ2 $p |- ( x = y -> ( z e. x <-> z e. y ) ) $=
    ( weq wel ax-14 wi equcoms impbid ) ABDCAEZCBEZABCFKJGBABACFHI $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
      Logical redundancy of ax-6 , ax-7 , ax-11 , ax-12
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  The orginal axiom schemes of Tarski's predicate calculus are ~ ax-5 ,
  ~ ax-17 , ~ ax9v , ~ ax-8 , ~ ax-13 , and ~ ax-14 , together with rule
  ~ ax-gen .  See ~ http://us.metamath.org/mpeuni/mmset.html#compare .  They
  are given as axiom schemes B4 through B8 in [KalishMontague] p. 81.  These
  are shown to be logically complete by Theorem 1 of [KalishMontague] p. 85.

  The axiom system of set.mm includes the auxiliary axiom schemes ~ ax-6 ,
  ~ ax-7 , ~ ax-12 , and ~ ax-11 , which are not part of Tarski's axiom
  schemes.  Each object language instance of them is provable from Tarski's
  axioms, so they are logically redundant.  However, they are conjectured not
  to be provable directly _as schemes_ from Tarski's axiom schemes using only
  Metamath's direct substitution rule.  They are used to make our system
  "metalogically complete" i.e. able to prove directly all possible schemes
  with wff and set metavariables, bundled or not, whose object-language
  instances are valid.  ( ~ ax-11 has been proved to be required; see
  ~ http://us.metamath.org/award2003.html#9a .  Metalogical independence of the
  other three are open problems.)

  (There are additional predicate calculus axiom schemes included in set.mm
  such as ~ ax-4 , but they can all be proved as theorems from the above.)

  Terminology:  Two set (individual) metavariables are "bundled" in an axiom or
  theorem scheme when there is no distinct variable constraint ($d) imposed on
  them.  (The term "bundled" is due to Raph Levien.)  For example, the ` x `
  and ` y ` in ~ ax-9 are bundled, but they are not in ~ ax9v . We also say
  that a scheme is bundled when it has at least one pair of bundled set
  metavariables.  If distinct variable conditions are added to all set
  metavariable pairs in a bundled scheme, we call that the "principal" instance
  of the bundled scheme.  For example, ~ ax9v is the principal instance of
  ~ ax-9 . Whenever a common variable is substituted for two or more bundled
  variables in an axiom or theorem scheme, we call the substitution instance
  "degenerate".  For example, the instance ` -. A. x -. x = x ` of ~ ax-9 is
  degenerate.  An advantage of bundling is ease of use since there are fewer
  distinct variable restrictions ($d) to be concerned with.  There is also a
  small economy in being able to state principal and degenerate instances
  simultaneously.  A disadvantage is that bundling may present difficulties in
  translations to other proof languages, which typically lack the concept (in
  part because their variables often represent the variables of the object
  language rather than metavariables ranging over them).

  Because Tarski's axiom schemes are logically complete, they can be used to
  prove any object-language instance of ~ ax-6 , ~ ax-7 , ~ ax-11 , and ~ ax-12
  . "Translating" this to Metamath, it means that Tarski's axioms can prove any
  substitution instance of ~ ax-6 , ~ ax-7 , ~ ax-11 , or ~ ax-12 in which (1)
  there are no wff metavariables and (2) all set metavariables are mutually
  distinct i.e. are not bundled.  In effect this is mimicking the object
  language by pretending that each set metavariable is an object-language
  variable.  (There may also be specific instances with wff metavariables
  and/or bundling that are directly provable from Tarski's axiom schemes, but
  it isn't guaranteed.  Whether all of them are possible is part of the still
  open metalogical independence problem for our additional axiom schemes.)

  It can be useful to see how this can be done, both to show that our
  additional schemes are valid metatheorems of Tarski's system and to be able
  to translate object language instances of our proofs into proofs that would
  work with a system using only Tarski's original schemes.  In addition, it may
  (or may not) provide insight into the conjectured metalogical independence of
  our additional schemes.

  The theorem schemes ~ ax6w , ~ ax7w , ~ ax11w , and ~ ax12w are derived using
  only Tarski's axiom schemes, showing that Tarski's schemes can be used to
  derive all substitution instances of ~ ax-6 , ~ ax-7 , ~ ax-11 , and ~ ax-12
  meeting conditions (1) and (2).  (The "w" suffix stands for "weak version".)
  Each hypothesis of ~ ax6w , ~ ax7w , and ~ ax11w is of the form
  ` ( x = y -> ( ph <-> ps ) ) ` where ` ps ` is an auxiliary or "dummy" wff
  metavariable in which ` x ` doesn't occur.  We can show by induction on
  formula length that the hypotheses can be eliminated in all cases meeting
  conditions (1) and (2).  The example ~ ax11wdemo illustrates the techniques
  (equality theorems and bound variable renaming) used to achieve this.

  We also show the degenerate instances for axioms with bundled variables in
  ~ ax7dgen , ~ ax11dgen , ~ ax12dgen1 , ~ ax12dgen2 , ~ ax12dgen3 , and
  ~ ax12dgen4 . (Their proofs are trivial, but we include them to be thorough.)
  Combining the principal and degenerate cases _outside_ of Metamath, we show
  that the bundled schemes ~ ax-6 , ~ ax-7 , ~ ax-11 , and ~ ax-12 are schemes
  of Tarski's system, meaning that all object language instances they generate
  are theorems of Tarski's system.

  It is interesting that Tarski used the bundled scheme ~ ax-9 in an older
  system, so it seems the main purpose of his later ~ ax9v was just to show
  that the weaker unbundled form is sufficient rather than an aesthetic
  objection to bundled free and bound variables.  Since we adopt the
  bundled ~ ax-9 as our official axiom, we  show that the degenerate
  instance holds in ~ ax9dgen .

  The case of ~ sp is curious:  originally an axiom of Tarski's system, it was
  proved logically redundant by Lemma 9 of [KalishMontague] p. 86.  However,
  the proof is by induction on formula length, and the scheme form
  ` A. x ph -> ph ` apparently cannot be proved directly from Tarski's other
  axiom schemes.  The best we can do seems to be ~ spw , again requiring
  substitution instances of ` ph ` that meet conditions (1) and (2) above.
  Note that our direct proof ~ sp requires ~ ax-11 , which is not part of
  Tarski's system.

$)

  ${
    $( Tarski's system uses the weaker ~ ax9v instead of the bundled ~ ax-9 ,
       so here we show that the degenerate case of ~ ax-9 can be derived.
       (Contributed by NM, 23-Apr-2017.) $)
    ax9dgen $p |- -. A. x -. x = x $=
      ( weq wn wal equid notnoti spfalw mt2 ) AABZCZADIAEZJAIKFGH $.
  $}

  ${
    $d y ph $.  $d x ps $.  $d x y $.
    ax6w.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Weak version of ~ ax-6 from which we can prove any ~ ax-6 instance not
       involving wff variables or bundling.  Uses only Tarski's FOL axiom
       schemes.  (Contributed by NM, 9-Apr-2017.) $)
    ax6w $p |- ( -. A. x ph -> A. x -. A. x ph ) $=
      ( hbn1w ) ABCDEF $.
  $}

  ${
    $d y z $.  $d x y $.  $d z ph $.  $d y ps $.
    ax7w.1 $e |- ( y = z -> ( ph <-> ps ) ) $.
    $( Weak version of ~ ax-7 from which we can prove any ~ ax-7 instance not
       involving wff variables or bundling.  Uses only Tarski's FOL axiom
       schemes.  Unlike ~ ax-7 , this theorem requires that ` x ` and ` y ` be
       distinct i.e. are not bundled.  (Contributed by NM, 10-Apr-2017.) $)
    ax7w $p |- ( A. x A. y ph -> A. y A. x ph ) $=
      ( alcomiw ) ABCDEFG $.
  $}

  $( Degenerate instance of ~ ax-7 where bundled variables ` x ` and ` y ` have
     a common substitution.  Uses only Tarski's FOL axiom schemes.
     (Contributed by NM, 13-Apr-2017.) $)
  ax7dgen $p |- ( A. x A. x ph -> A. x A. x ph ) $=
    ( wal id ) ABCBCD $.

  ${
    $d x ps $.
    ax11wlemw.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Lemma for weak version of ~ ax-11 .  Uses only Tarski's FOL axiom
       schemes.  In some cases, this lemma may lead to shorter proofs than
       ~ ax11w .  (Contributed by NM, 10-Apr-2017.) $)
    ax11wlem $p |- ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) $=
      ( ax-17 ax11i ) ABCDEBCFG $.
  $}

  ${
    $d y z $.  $d x ps $.  $d z ph $.  $d y ch $.
    ax11w.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    ax11w.2 $e |- ( y = z -> ( ph <-> ch ) ) $.
    $( Weak version of ~ ax-11 from which we can prove any ~ ax-11 instance not
       involving wff variables or bundling.  Uses only Tarski's FOL axiom
       schemes.  An instance of the first hypothesis will normally require that
       ` x ` and ` y ` be distinct (unless ` x ` does not occur in ` ph ` ).
       For an example of how the hypotheses can be eliminated when we
       substitute an expression without wff variables for ` ph ` , see
       ~ ax11wdemo .  (Contributed by NM, 10-Apr-2017.) $)
    ax11w $p |- ( x = y -> ( A. y ph -> A. x ( x = y -> ph ) ) ) $=
      ( wal weq wi spw ax11wlem syl5 ) AEIADEJZOAKDIACEFHLABDEGMN $.
  $}

  $( Degenerate instance of ~ ax-11 where bundled variables ` x ` and ` y `
     have a common substitution.  Uses only Tarski's FOL axiom schemes.
     (Contributed by NM, 13-Apr-2017.) $)
  ax11dgen $p |- ( x = x -> ( A. x ph -> A. x ( x = x -> ph ) ) ) $=
    ( wal weq wi ax-1 alimi a1i ) ABCBBDZAEZBCEIAJBAIFGH $.

  ${
    $d x y z w v $.
    $( Example of an application of ~ ax11w that results in an instance of
       ~ ax-11 for a contrived formula with mixed free and bound variables,
       ` ( x e. y /\ A. x z e. x /\ A. y A. z y e. x ) ` , in place of
       ` ph ` .  The proof illustrates bound variable renaming with ~ cbvalvw
       to obtain fresh variables to avoid distinct variable clashes.  Uses only
       Tarski's FOL axiom schemes.  (Contributed by NM, 14-Apr-2017.) $)
    ax11wdemo $p |- ( x = y
              -> ( A. y ( x e. y /\ A. x z e. x /\ A. y A. z y e. x )
     -> A. x ( x = y -> ( x e. y /\ A. x z e. x /\ A. y A. z y e. x ) ) ) ) $=
      ( vw vv wel wal w3a weq elequ1 elequ2 cbvalvw a1i albidv syl5bb 3anbi123d
      wb 3anbi13d ax11w ) ABFZCAFZAGZBAFZCGZBGZHBBFZCDFZDGZEBFZCGZEGZHAEFZUBEAF
      ZCGZEGZHABEABIZTUFUBUHUEUKABBJUBUHQUPUAUGADADCKLMUEUOUPUKUDUNBEBEIZUCUMCB
      EAJNLZUPUNUJEUPUMUICABEKNNOPUQTULUEUOUBBEAKUEUOQUQURMRS $.
  $}

  ${
    $d x y $.  $d x z $.
    $( Weak version (principal instance) of ~ ax-12 .  (Because ` y ` and ` z `
       don't need to be distinct, this actually bundles the principal instance
       and the degenerate instance
       ` ( -. x = y -> ( y = y -> A. x y = y ) ) ` .)  Uses only Tarski's FOL
       axiom schemes.  The proof is trivial but is included to complete the set
       ~ ax6w , ~ ax7w , and ~ ax11w .  (Contributed by NM, 10-Apr-2017.) $)
    ax12w $p |- ( -. x = y -> ( y = z -> A. x y = z ) ) $=
      ( weq wn a17d ) ABDEBCDAF $.
  $}

  $( Degenerate instance of ~ ax-12 where bundled variables ` x ` and ` y `
     have a common substitution.  Uses only Tarski's FOL axiom schemes.
     (Contributed by NM, 13-Apr-2017.) $)
  ax12dgen1 $p |- ( -. x = x -> ( x = z -> A. x x = z ) ) $=
    ( weq wal wi equid pm2.24i ) AACABCZHADEAFG $.

  $( Degenerate instance of ~ ax-12 where bundled variables ` x ` and ` z `
     have a common substitution.  Uses only Tarski's FOL axiom schemes.
     (Contributed by NM, 13-Apr-2017.) $)
  ax12dgen2 $p |- ( -. x = y -> ( y = x -> A. x y = x ) ) $=
    ( weq wn wal equcomi pm2.21 syl5 ) BACZABCZJDIAEZBAFJKGH $.

  $( Degenerate instance of ~ ax-12 where bundled variables ` y ` and ` z `
     have a common substitution.  Uses only Tarski's FOL axiom schemes.
     (Contributed by NM, 13-Apr-2017.) $)
  ax12dgen3 $p |- ( -. x = y -> ( y = y -> A. x y = y ) ) $=
    ( weq wn wal equid ax-gen a1ii ) ABCDBBCZIAEIABFGH $.

  $( Degenerate instance of ~ ax-12 where bundled variables ` x ` , ` y ` , and
     ` z ` have a common substitution.  Uses only Tarski's FOL axiom schemes .
     (Contributed by NM, 13-Apr-2017.) $)
  ax12dgen4 $p |- ( -. x = x -> ( x = x -> A. x x = x ) ) $=
    ( ax12dgen1 ) AAB $.


$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
   Predicate calculus with equality:  Auxiliary axiom schemes (4 schemes)
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#

  In this section we introduce four additional schemes ~ ax-6 , ~ ax-7 ,
  ~ ax-11 , and ~ ax-12 that are not part of Tarski's system but can be proved
  (outside of Metamath) as theorem schemes of Tarski's system.  These are
  needed to give our system the property of "metalogical completeness," which
  means that we can prove (with Metamath) all possible schemes expressible in
  our language of wff metavariables ranging over object-language wffs and set
  metavariables ranging over object-language individual variables.

  To show that these schemes are valid metatheorems of Tarski's system S2,
  above we proved from Tarski's system theorems ~ ax6w , ~ ax7w , ~ ax12w ,
  and ~ ax11w , which show that any object-language instance of these schemes
  (emulated by having no wff metavariables and requiring all set
  metavariables to be mutually distinct) can be proved using only the schemes
  in Tarski's system S2.

  An open problem is to show that these four additional schemes are mutually
  _metalogically_ independent and metalogically independent from Tarski's.  So
  far, independence of ~ ax-11 from all others has been shown, and
  independence of Tarski's ~ ax-9 from all others has been shown; see
  items 9a and 11 on ~ http://us.metamath.org/award2003.html .

$)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
              Axiom scheme ax-6 (Quantified Negation)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Axiom of Quantified Negation.  Axiom C5-2 of [Monk2] p. 113.  This axiom
     scheme is logically redundant (see ~ ax6w ) but is used as an auxiliary
     axiom to achieve metalogical completeness.  (Contributed by NM,
     5-Aug-1993.) $)
  ax-6 $a |- ( -. A. x ph -> A. x -. A. x ph ) $.

  $( ` x ` is not free in ` -. A. x ph ` .  (Contributed by NM, 5-Aug-1993.)
     (Proof shortened by Wolf Lammen, 18-Aug-2014.) $)
  hbn1 $p |- ( -. A. x ph -> A. x -. A. x ph ) $=
    ( ax-6 ) ABC $.

  $( ` x ` is not free in ` E. x ph ` .  (Contributed by NM, 5-Aug-1993.) $)
  hbe1 $p |- ( E. x ph -> A. x E. x ph ) $=
    ( wex wn wal df-ex hbn1 hbxfrbi ) ABCADZBEDBABFIBGH $.

  $( ` x ` is not free in ` E. x ph ` .  (Contributed by Mario Carneiro,
     11-Aug-2016.) $)
  nfe1 $p |- F/ x E. x ph $=
    ( wex hbe1 nfi ) ABCBABDE $.

  $( The analog in our predicate calculus of axiom 5 of modal logic S5.
     (Contributed by NM, 5-Oct-2005.) $)
  modal-5 $p |- ( -. A. x -. ph -> A. x -. A. x -. ph ) $=
    ( wn hbn1 ) ACBD $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
            Axiom scheme ax-7 (Quantifier Commutation)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Axiom of Quantifier Commutation.  This axiom says universal quantifiers
     can be swapped.  Axiom scheme C6' in [Megill] p. 448 (p. 16 of the
     preprint).  Also appears as Lemma 12 of [Monk2] p. 109 and Axiom C5-3 of
     [Monk2] p. 113.  This axiom scheme is logically redundant (see ~ ax7w )
     but is used as an auxiliary axiom to achieve metalogical completeness.
     (Contributed by NM, 5-Aug-1993.) $)
  ax-7 $a |- ( A. x A. y ph -> A. y A. x ph ) $.

  ${
    a7s.1 $e |- ( A. x A. y ph -> ps ) $.
    $( Swap quantifiers in an antecedent.  (Contributed by NM, 5-Aug-1993.) $)
    a7s $p |- ( A. y A. x ph -> ps ) $=
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

  $( Theorem *11.21 in [WhiteheadRussell] p. 160.  (Contributed by Andrew
     Salmon, 24-May-2011.) $)
  alrot3 $p |- ( A. x A. y A. z ph <-> A. y A. z A. x ph ) $=
    ( wal alcom albii bitri ) ADEZCEBEIBEZCEABEDEZCEIBCFJKCABDFGH $.

  $( Rotate 4 universal quantifiers twice.  (Contributed by NM, 2-Feb-2005.)
     (Proof shortened by Fan Zheng, 6-Jun-2016.) $)
  alrot4 $p |- ( A. x A. y A. z A. w ph <-> A. z A. w A. x A. y ph ) $=
    ( wal alrot3 albii bitri ) AEFDFCFZBFACFZEFDFZBFKBFEFDFJLBACDEGHKBDEGI $.

  ${
    hbald.1 $e |- ( ph -> A. y ph ) $.
    hbald.2 $e |- ( ph -> ( ps -> A. x ps ) ) $.
    $( Deduction form of bound-variable hypothesis builder ~ hbal .
       (Contributed by NM, 2-Jan-2002.) $)
    hbald $p |- ( ph -> ( A. y ps -> A. x A. y ps ) ) $=
      ( wal alimdh ax-7 syl6 ) ABDGZBCGZDGKCGABLDEFHBDCIJ $.
  $}

  $( Theorem 19.11 of [Margaris] p. 89.  Revised to remove dependency on
     ~ ax-11 , ~ ax-6 , ~ ax-9 , ~ ax-8 and ~ ax-17 .  (Contributed by NM,
     5-Aug-1993.)  (Revised by Wolf Lammen, 8-Jan-2018.) $)
  excom $p |- ( E. x E. y ph <-> E. y E. x ph ) $=
    ( wn wal wex alcom notbii exnal 3bitr4i df-ex exbii ) ADZCEZDZBFZMBEZDZCFZA
    CFZBFABFZCFNBEZDQCEZDPSUBUCMBCGHNBIQCIJTOBACKLUARCABKLJ $.

  $( One direction of Theorem 19.11 of [Margaris] p. 89.  Revised to remove
     dependency on ~ ax-11 , ~ ax-6 , ~ ax-9 , ~ ax-8 and ~ ax-17 .
     (Contributed by NM, 5-Aug-1993.)  (Revised by Mario Carneiro,
     24-Sep-2016.)  (Revised by Wolf Lammen, 8-Jan-2018.) $)
  excomim $p |- ( E. x E. y ph -> E. y E. x ph ) $=
    ( wex excom biimpi ) ACDBDABDCDABCEF $.

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

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
           Axiom scheme ax-11 (Substitution)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Axiom of Substitution.  One of the 5 equality axioms of predicate
     calculus.  The final consequent ` A. x ( x = y -> ph ) ` is a way of
     expressing " ` y ` substituted for ` x ` in wff ` ph ` " (cf. ~ sb6 ).  It
     is based on Lemma 16 of [Tarski] p. 70 and Axiom C8 of [Monk2] p. 105,
     from which it can be proved by cases.

     The original version of this axiom was ~ ax-11o ("o" for "old") and was
     replaced with this shorter ~ ax-11 in Jan. 2007.  The old axiom is proved
     from this one as theorem ~ ax11o .  Conversely, this axiom is proved from
     ~ ax-11o as theorem ~ ax11 .

     Juha Arpiainen proved the metalogical independence of this axiom (in the
     form of the older axiom ~ ax-11o ) from the others on 19-Jan-2006.  See
     item 9a at ~ http://us.metamath.org/award2003.html .

     See ~ ax11v and ~ ax11v2 for other equivalents of this axiom that (unlike
     this axiom) have distinct variable restrictions.

     This axiom scheme is logically redundant (see ~ ax11w ) but is used as an
     auxiliary axiom to achieve metalogical completeness.  (Contributed by NM,
     22-Jan-2007.) $)
  ax-11 $a |- ( x = y -> ( A. y ph -> A. x ( x = y -> ph ) ) ) $.

  ${
    $d x w $.  $d w ph $.
    $( If a wff is true, it is true for at least one instance.  Special case of
       Theorem 19.8 of [Margaris] p. 89.  (Contributed by NM, 5-Aug-1993.)
       (Revised by Wolf Lammen, 13-Jan-2018.) $)
    19.8a $p |- ( ph -> E. x ph ) $=
      ( vw weq wex wi a9ev wal ax-17 ax-11 exim mpi syl56 equcoms exlimiv ax-mp
      ) CBDZCEAABEZFZCBGQSCSBCAACHBCDZTAFBHZRACIABCJUATBERBCGTABKLMNOP $.
  $}

  ${
    $( Specialization.  A universally quantified wff implies the wff without a
       quantifier Axiom scheme B5 of [Tarski] p. 67 (under his system S2,
       defined in the last paragraph on p. 77).  Also appears as Axiom scheme
       C5' in [Megill] p. 448 (p. 16 of the preprint).

       For the axiom of specialization presented in many logic textbooks, see
       theorem ~ stdpc4 .

       This theorem shows that our obsolete axiom ~ ax-4 can be derived from
       the others.  The proof uses ideas from the proof of Lemma 21 of [Monk2]
       p. 114.

       It appears that this scheme cannot be derived directly from Tarski's
       axioms without auxilliary axiom scheme ~ ax-11 .  It is thought the best
       we can do using only Tarski's axioms is ~ spw .  (Contributed by NM,
       21-May-2008.)  (Proof shortened by Scott Fenton, 24-Jan-2011.)  (Proof
       shortened by Wolf Lammen, 13-Jan-2018.) $)
    sp $p |- ( A. x ph -> ph ) $=
      ( wal wn wex alex 19.8a con1i sylbi ) ABCADZBEZDAABFAKJBGHI $.
  $}

  ${
    $d x w $.  $d w ph $.
    $( Obsolete proof of ~ sp as of 23-Dec-2017.  (Contributed by NM,
       21-May-2008.)  (Proof shortened by Scott Fenton, 24-Jan-2011.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    spOLD $p |- ( A. x ph -> ph ) $=
      ( vw wal wi weq wn ax9v equcomi ax-17 ax-11 syl2im con2 al2imi mtoi con4d
      syl6 con3i alrimiv mt3 ) ABDZAEZCBFZGZCDCBHUBGUDCUCUBUCAUAUCAGZBCFZUEEZBD
      ZUAGUCUFUEUECDUHCBIUECJUEBCKLUHUAUFGZBDBCHUGAUIBUFAMNOQPRST $.
  $}

  $( Show that the original axiom ~ ax-5o can be derived from ~ ax-5 and
     others.  See ~ ax5 for the rederivation of ~ ax-5 from ~ ax-5o .

     Part of the proof is based on the proof of Lemma 22 of [Monk2] p. 114.
     (Contributed by NM, 21-May-2008.)  (Proof modification is discouraged.) $)
  ax5o $p |- ( A. x ( A. x ph -> ps ) -> ( A. x ph -> A. x ps ) ) $=
    ( wal wi wn sp con2i hbn1 con1i alimi 3syl ax-5 syl5 ) ACDZOCDZOBECDBCDOOFZ
    CDZFZSCDPROQCGHQCISOCORACIJKLOBCMN $.

  $( Show that the original axiom ~ ax-6o can be derived from ~ ax-6 and
     others.  See ~ ax6 for the rederivation of ~ ax-6 from ~ ax-6o .

     Normally, ~ ax6o should be used rather than ~ ax-6o , except by theorems
     specifically studying the latter's properties.  (Contributed by NM,
     21-May-2008.) $)
  ax6o $p |- ( -. A. x -. A. x ph -> ph ) $=
    ( wal wn sp ax-6 nsyl4 ) ABCZAHDBCABEABFG $.

  $( Abbreviated version of ~ ax6o .  (Contributed by NM, 5-Aug-1993.) $)
  a6e $p |- ( E. x A. x ph -> ph ) $=
    ( wal wex wn df-ex ax6o sylbi ) ABCZBDIEBCEAIBFABGH $.

  $( The analog in our predicate calculus of the Brouwer axiom (B) of modal
     logic S5.  (Contributed by NM, 5-Oct-2005.) $)
  modal-b $p |- ( ph -> A. x -. A. x -. ph ) $=
    ( wn wal ax6o con4i ) ACZBDCBDAGBEF $.

  ${
    spi.1 $e |- A. x ph $.
    $( Inference rule reversing generalization.  (Contributed by NM,
       5-Aug-1993.) $)
    spi $p |- ph $=
      ( wal sp ax-mp ) ABDACABEF $.
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

  $( If a wff is true, it is true for at least one instance.  Special case of
     Theorem 19.8 of [Margaris] p. 89.  (Contributed by NM, 5-Aug-1993.)
     (New usage is discouraged.)  (Proof modification is discouraged.) $)
  19.8aOLD $p |- ( ph -> E. x ph ) $=
    ( wn wal wex sp con2i df-ex sylibr ) AACZBDZCABEKAJBFGABHI $.

  $( Theorem 19.2 of [Margaris] p. 89, generalized to use two set variables.
     (Contributed by O'Cat, 31-Mar-2008.) $)
  19.2g $p |- ( A. x ph -> E. y ph ) $=
    ( wex 19.8a sps ) AACDBACEF $.

  ${
    19.21bi.1 $e |- ( ph -> A. x ps ) $.
    $( Inference from Theorem 19.21 of [Margaris] p. 90.  (Contributed by NM,
       5-Aug-1993.) $)
    19.21bi $p |- ( ph -> ps ) $=
      ( wal sp syl ) ABCEBDBCFG $.
  $}

  ${
    19.23bi.1 $e |- ( E. x ph -> ps ) $.
    $( Inference from Theorem 19.23 of [Margaris] p. 90.  (Contributed by NM,
       5-Aug-1993.) $)
    19.23bi $p |- ( ph -> ps ) $=
      ( wex 19.8a syl ) AACEBACFDG $.
  $}

  ${
    nexr.1 $e |- -. E. x ph $.
    $( Inference from ~ 19.8a .  (Contributed by Jeff Hankins, 26-Jul-2009.) $)
    nexr $p |- -. ph $=
      ( wex 19.8a mto ) AABDCABEF $.
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
      ( wal wi wnf alrimi df-nf sylibr ) ABBCFGZCFBCHALCDEIBCJK $.
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
    eximd.1 $e |- F/ x ph $.
    eximd.2 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction from Theorem 19.22 of [Margaris] p. 90.  (Contributed by Mario
       Carneiro, 24-Sep-2016.) $)
    eximd $p |- ( ph -> ( E. x ps -> E. x ch ) ) $=
      ( nfri eximdh ) ABCDADEGFH $.
  $}

  ${
    nexd.1 $e |- F/ x ph $.
    nexd.2 $e |- ( ph -> -. ps ) $.
    $( Deduction for generalization rule for negated wff.  (Contributed by
       Mario Carneiro, 24-Sep-2016.) $)
    nexd $p |- ( ph -> -. E. x ps ) $=
      ( nfri nexdh ) ABCACDFEG $.
  $}

  ${
    albid.1 $e |- F/ x ph $.
    albid.2 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for universal quantifier (deduction rule).
       (Contributed by Mario Carneiro, 24-Sep-2016.) $)
    albid $p |- ( ph -> ( A. x ps <-> A. x ch ) ) $=
      ( nfri albidh ) ABCDADEGFH $.
  $}

  ${
    exbid.1 $e |- F/ x ph $.
    exbid.2 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for existential quantifier (deduction rule).
       (Contributed by Mario Carneiro, 24-Sep-2016.) $)
    exbid $p |- ( ph -> ( E. x ps <-> E. x ch ) ) $=
      ( nfri exbidh ) ABCDADEGFH $.
  $}

  ${
    nfbidf.1 $e |- F/ x ph $.
    nfbidf.2 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( An equality theorem for effectively not free.  (Contributed by Mario
       Carneiro, 4-Oct-2016.) $)
    nfbidf $p |- ( ph -> ( F/ x ps <-> F/ x ch ) ) $=
      ( wal wi wnf albid imbi12d df-nf 3bitr4g ) ABBDGZHZDGCCDGZHZDGBDICDIAOQDE
      ABCNPFABCDEFJKJBDLCDLM $.
  $}

  ${
    19.3.1 $e |- F/ x ph $.
    $( A wff may be quantified with a variable not free in it.  Theorem 19.3 of
       [Margaris] p. 89.  (Contributed by NM, 5-Aug-1993.)  (Revised by Mario
       Carneiro, 24-Sep-2016.) $)
    19.3 $p |- ( A. x ph <-> ph ) $=
      ( wal sp nfri impbii ) ABDAABEABCFG $.
  $}

  $( A closed version of ~ 19.9 .  (Contributed by NM, 5-Aug-1993.)  (Proof
     shortened by Wolf Lammen, 3-Mar-2018.) $)
  19.9ht $p |- ( A. x ( ph -> A. x ph ) -> ( E. x ph -> ph ) ) $=
    ( wal wi wex exim a6e syl6 ) AABCZDBCABEIBEAAIBFABGH $.

  $( A closed version of ~ 19.9 .  (Contributed by NM, 5-Aug-1993.)  (Revised
     by Mario Carneiro, 24-Sep-2016.)  (Proof shortended by Wolf Lammen,
     30-Dec-2017.) $)
  19.9t $p |- ( F/ x ph -> ( E. x ph <-> ph ) ) $=
    ( wnf wex wal wi df-nf 19.9ht sylbi 19.8a impbid1 ) ABCZABDZALAABEFBEMAFABG
    ABHIABJK $.

  ${
    19.9h.1 $e |- ( ph -> A. x ph ) $.
    $( A wff may be existentially quantified with a variable not free in it.
       Theorem 19.9 of [Margaris] p. 89.  (Contributed by FL, 24-Mar-2007.)
       (Proof shortened by Wolf Lammen, 5-Jan-2018.) $)
    19.9h $p |- ( E. x ph <-> ph ) $=
      ( wnf wex wb nfi 19.9t ax-mp ) ABDABEAFABCGABHI $.

    $( Obsolete proof of ~ 19.9h as of 5-Jan-2018.  (Contributed by FL,
       24-Mar-2007.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    19.9hOLD $p |- ( E. x ph <-> ph ) $=
      ( wex wal wi 19.9ht mpg 19.8a impbii ) ABDZAAABEFKAFBABGCHABIJ $.
  $}

  ${
    19.9d.1 $e |- ( ps -> F/ x ph ) $.
    $( A deduction version of one direction of ~ 19.9 .  (Contributed by NM,
       5-Aug-1993.)  (Revised by Mario Carneiro, 24-Sep-2016.) $)
    19.9d $p |- ( ps -> ( E. x ph -> ph ) ) $=
      ( wex wnf wb 19.9t syl biimpd ) BACEZABACFKAGDACHIJ $.
  $}

  ${
    19.9.1 $e |- F/ x ph $.
    $( A wff may be existentially quantified with a variable not free in it.
       Theorem 19.9 of [Margaris] p. 89.  (Contributed by FL, 24-Mar-2007.)
       (Revised by Mario Carneiro, 24-Sep-2016.)  (Proof shortened by Wolf
       Lammen, 30-Dec-2017.) $)
    19.9 $p |- ( E. x ph <-> ph ) $=
      ( nfri 19.9h ) ABABCDE $.

    $( Obsolete proof of ~ 19.9 as of 30-Dec-2017.  (Contributed by FL,
       24-Mar-2007.)  (Revised by Mario Carneiro, 24-Sep-2016.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    19.9OLD $p |- ( E. x ph <-> ph ) $=
      ( wnf wex wb 19.9t ax-mp ) ABDABEAFCABGH $.
  $}

  $( Closed theorem version of bound-variable hypothesis builder ~ hbn .
     (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen,
     3-Mar-2018.) $)
  hbnt $p |- ( A. x ( ph -> A. x ph ) -> ( -. ph -> A. x -. ph ) ) $=
    ( wal wi wn wex df-ex 19.9ht syl5bir con1d ) AABCDBCZAEBCZALEABFKAABGABHIJ
    $.

  $( Obsolete proof of ~ hbnt as of 3-Mar-2018.  (Contributed by NM,
     5-Aug-1993.)  (New usage is discouraged.)
     (Proof modification is discouraged.) $)
  hbntOLD $p |- ( A. x ( ph -> A. x ph ) -> ( -. ph -> A. x -. ph ) ) $=
    ( wn wal wi ax6o con1i con3 al2imi syl5 ) ACZABDZCZBDZALEZBDKBDNAABFGOMKBAL
    HIJ $.

  ${
    hbn.1 $e |- ( ph -> A. x ph ) $.
    $( If ` x ` is not free in ` ph ` , it is not free in ` -. ph ` .
       (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen,
       17-Dec-2017.) $)
    hbn $p |- ( -. ph -> A. x -. ph ) $=
      ( wal wi wn hbnt mpg ) AABDEAFZIBDEBABGCH $.

    $( Obsolete proof of ~ hbn as of 16-Dec-2017.  (Contributed by NM,
       5-Aug-1993.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    hbnOLD $p |- ( -. ph -> A. x -. ph ) $=
      ( wn wal sp con3i hbn1 alrimih syl ) ADZABEZDZKBELAABFGMKBABHALCGIJ $.
  $}

  $( Obsolete proof of ~ 19.9ht as of 3-Mar-2018.  (Contributed by NM,
     5-Aug-1993.)  (New usage is discouraged.)
     (Proof modification is discouraged.) $)
  19.9htOLD $p |- ( A. x ( ph -> A. x ph ) -> ( E. x ph -> ph ) ) $=
    ( wex wn wal wi df-ex hbnt con1d syl5bi ) ABCADBEZDAABEFBEZAABGLAKABHIJ $.

  $( ` x ` is not free in ` A. x ph ` .  Example in Appendix in [Megill] p. 450
     (p. 19 of the preprint).  Also Lemma 22 of [Monk2] p. 114.  (Contributed
     by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen, 15-Dec-2017.) $)
  hba1 $p |- ( A. x ph -> A. x A. x ph ) $=
    ( wal wn wex alex hbe1 hbn hbxfrbi ) ABCADZBEZDBABFKBJBGHI $.

  $( Obsolete proof of ~ hba1 as of 15-Dec-2017 (Contributed by NM,
     5-Aug-1993.)  (New usage is discouraged.)
     (Proof modification is discouraged.) $)
  hba1OLD $p |- ( A. x ph -> A. x A. x ph ) $=
    ( wal wn sp con2i hbn1 con1i alimi 3syl ) ABCZKDZBCZDZNBCKBCMKLBEFLBGNKBKMA
    BGHIJ $.

  $( ` x ` is not free in ` A. x ph ` .  (Contributed by Mario Carneiro,
     11-Aug-2016.) $)
  nfa1 $p |- F/ x A. x ph $=
    ( wal hba1 nfi ) ABCBABDE $.

  ${
    a5i.1 $e |- ( A. x ph -> ps ) $.
    $( Inference version of ~ ax5o .  (Contributed by NM, 5-Aug-1993.) $)
    a5i $p |- ( A. x ph -> A. x ps ) $=
      ( wal nfa1 alrimi ) ACEBCACFDG $.
  $}

  $( ` x ` is not free in ` F/ x ph ` .  (Contributed by Mario Carneiro,
     11-Aug-2016.) $)
  nfnf1 $p |- F/ x F/ x ph $=
    ( wnf wal wi df-nf nfa1 nfxfr ) ABCAABDEZBDBABFIBGH $.

  ${
    nfnd.1 $e |- ( ph -> F/ x ps ) $.
    $( If in a context ` x ` is not free in ` ps ` , it is not free in
       ` -. ps ` .  (Contributed by Mario Carneiro, 24-Sep-2016.)  (Proof
       shortened by Wolf Lammen, 28-Dec-2017.) $)
    nfnd $p |- ( ph -> F/ x -. ps ) $=
      ( wnf wn nfnf1 wal wi df-nf hbnt sylbi nfd syl ) ABCEZBFZCEDOPCBCGOBBCHIC
      HPPCHIBCJBCKLMN $.

    $( Obsolete proof of ~ nfnd as of 28-Dec-2017.  (Contributed by Mario
       Carneiro, 24-Sep-2016.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    nfndOLD $p |- ( ph -> F/ x -. ps ) $=
      ( wnf wn nfnf1 wal ax6o con1i wi df-nf con3 al2imi sylbi syl5 nfd syl ) A
      BCEZBFZCEDSTCBCGTBCHZFZCHZSTCHZUCBBCIJSBUAKZCHUCUDKBCLUEUBTCBUAMNOPQR $.

  $}

  ${
    nfn.1 $e |- F/ x ph $.
    $( If ` x ` is not free in ` ph ` , it is not free in ` -. ph ` .
       (Contributed by Mario Carneiro, 11-Aug-2016.) $)
    nfn $p |- F/ x -. ph $=
      ( wn wnf wtru a1i nfnd trud ) ADBEFABABEFCGHI $.
  $}

  $( A convenience theorem particularly designed to remove dependencies on
     ~ ax-7 in conjunction with disjunctors.  (Contributed by Wolf Lammen,
     2-Sep-2018.) $)
  nfna1 $p |- F/ x -. A. x ph $=
    ( wal nfa1 nfn ) ABCBABDE $.

  $( Theorem 19.38 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.)
     (Revised by Wolf Lammen, 2-Jan-2018.) $)
  19.38 $p |- ( ( E. x ph -> A. x ps ) -> A. x ( ph -> ps ) ) $=
    ( wex wal wi wn alnex pm2.21 alimi sylbir ax-1 ja ) ACDZBCEABFZCEZNGAGZCEPA
    CHQOCABIJKBOCBALJM $.

  $( Closed form of Theorem 19.21 of [Margaris] p. 90.  (Contributed by NM,
     27-May-1997.)  (Revised by Mario Carneiro, 24-Sep-2016.)  (Proof shortened
     by Wolf Lammen, 3-Jan-2018.) $)
  19.21t $p |- ( F/ x ph -> ( A. x ( ph -> ps ) <-> ( ph -> A. x ps ) ) ) $=
    ( wnf wi wal nfr ax-5 syl9 wex 19.9t imbi1d 19.38 syl6bir impbid ) ACDZABEC
    FZABCFZEZPAACFQRACGABCHIPSACJZREQPTARACKLABCMNO $.

  ${
    19.21.1 $e |- F/ x ph $.
    $( Theorem 19.21 of [Margaris] p. 90.  The hypothesis can be thought of
       as " ` x ` is not free in ` ph ` ."  (Contributed by NM, 5-Aug-1993.)
       (Revised by Mario Carneiro, 24-Sep-2016.) $)
    19.21 $p |- ( A. x ( ph -> ps ) <-> ( ph -> A. x ps ) ) $=
      ( wnf wi wal wb 19.21t ax-mp ) ACEABFCGABCGFHDABCIJ $.
  $}

  ${
    19.21h.1 $e |- ( ph -> A. x ph ) $.
    $( Theorem 19.21 of [Margaris] p. 90.  The hypothesis can be thought of
       as " ` x ` is not free in ` ph ` ."  (Contributed by NM, 1-Aug-2017.)
       (Proof shortened by Wolf Lammen, 1-Jan-2018.) $)
    19.21h $p |- ( A. x ( ph -> ps ) <-> ( ph -> A. x ps ) ) $=
      ( nfi 19.21 ) ABCACDEF $.
  $}

  ${
    stdpc5.1 $e |- F/ x ph $.
    $( An axiom scheme of standard predicate calculus that emulates Axiom 5 of
       [Mendelson] p. 69.  The hypothesis ` F/ x ph ` can be thought of as
       emulating " ` x ` is not free in ` ph ` ."  With this definition, the
       meaning of "not free" is less restrictive than the usual textbook
       definition; for example ` x ` would not (for us) be free in ` x = x ` by
       ~ nfequid .  This theorem scheme can be proved as a metatheorem of
       Mendelson's axiom system, even though it is slightly stronger than his
       Axiom 5.  (Contributed by NM, 22-Sep-1993.)  (Revised by Mario Carneiro,
       12-Oct-2016.)  (Proof shortened by Wolf Lammen, 1-Jan-2018.) $)
    stdpc5 $p |- ( A. x ( ph -> ps ) -> ( ph -> A. x ps ) ) $=
      ( wi wal 19.21 biimpi ) ABECFABCFEABCDGH $.

    $( Obsolete proof of ~ stdpc5 as of 1-Jan-2018.  (Contributed by NM,
       22-Sep-1993.)  (Revised by Mario Carneiro, 12-Oct-2016.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    stdpc5OLD $p |- ( A. x ( ph -> ps ) -> ( ph -> A. x ps ) ) $=
      ( wal wi nfri alim syl5 ) AACEABFCEBCEACDGABCHI $.
  $}

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
    19.23h.1 $e |- ( ps -> A. x ps ) $.
    $( Theorem 19.23 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.)
       (Revised by Mario Carneiro, 24-Sep-2016.)  (Proof shortened by Wolf
       Lammen, 1-Jan-2018.) $)
    19.23h $p |- ( A. x ( ph -> ps ) <-> ( E. x ph -> ps ) ) $=
      ( nfi 19.23 ) ABCBCDEF $.
  $}

  ${
    exlimi.1 $e |- F/ x ps $.
    exlimi.2 $e |- ( ph -> ps ) $.
    $( Inference from Theorem 19.23 of [Margaris] p. 90.  (Contributed by Mario
       Carneiro, 24-Sep-2016.) $)
    exlimi $p |- ( E. x ph -> ps ) $=
      ( wi wex 19.23 mpgbi ) ABFACGBFCABCDHEI $.
  $}

  ${
    exlimih.1 $e |- ( ps -> A. x ps ) $.
    exlimih.2 $e |- ( ph -> ps ) $.
    $( Inference from Theorem 19.23 of [Margaris] p. 90.  (Contributed by NM,
       5-Aug-1993.)  (Proof shortened by Andrew Salmon, 13-May-2011.)  (Proof
       shortened by Wolf Lammen, 1-Jan-2018.) $)
    exlimih $p |- ( E. x ph -> ps ) $=
      ( nfi exlimi ) ABCBCDFEG $.

    $( Obsolete proof of ~ exlimih as of 1-Jan-2018.  (Contributed by NM,
       5-Aug-1993.)  (Proof shortened by Andrew Salmon, 13-May-2011.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    exlimihOLD $p |- ( E. x ph -> ps ) $=
      ( wi wex 19.23h mpgbi ) ABFACGBFCABCDHEI $.
  $}

  ${
    exlimd.1 $e |- F/ x ph $.
    exlimd.2 $e |- F/ x ch $.
    exlimd.3 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction from Theorem 19.9 of [Margaris] p. 89.  (Contributed by Mario
       Carneiro, 24-Sep-2016.)  (Proof shortened by Wolf Lammen,
       12-Jan-2018.) $)
    exlimd $p |- ( ph -> ( E. x ps -> ch ) ) $=
      ( wex eximd 19.9 syl6ib ) ABDHCDHCABCDEGICDFJK $.
    $( Obsolete proof of ~ exlimd as of 12-Jan-2018.  (Contributed by Mario
       Carneiro, 24-Sep-2016.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    exlimdOLD $p |- ( ph -> ( E. x ps -> ch ) ) $=
      ( wi wal wex alrimi 19.23 sylib ) ABCHZDIBDJCHANDEGKBCDFLM $.
  $}

  ${
    exlimdh.1 $e |- ( ph -> A. x ph ) $.
    exlimdh.2 $e |- ( ch -> A. x ch ) $.
    exlimdh.3 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction from Theorem 19.9 of [Margaris] p. 89.  (Contributed by NM,
       28-Jan-1997.) $)
    exlimdh $p |- ( ph -> ( E. x ps -> ch ) ) $=
      ( nfi exlimd ) ABCDADEHCDFHGI $.
  $}

  ${
    nfimd.1 $e |- ( ph -> F/ x ps ) $.
    nfimd.2 $e |- ( ph -> F/ x ch ) $.
    $( If in a context ` x ` is not free in ` ps ` and ` ch ` , it is not free
       in ` ( ps -> ch ) ` .  (Contributed by Mario Carneiro, 24-Sep-2016.)
       (Proof shortened by Wolf Lammen, 30-Dec-2017.) $)
    nfimd $p |- ( ph -> F/ x ( ps -> ch ) ) $=
      ( wnf wal nfnf1 nfr imim2d 19.21t biimprd syl9r alrimd df-nf syl6ibr sylc
      wi ) ABDGZCDGZBCSZDGZEFTUAUBUBDHZSZDHUCTUAUEDBDICDIUAUBBCDHZSZTUDUACUFBCD
      JKTUDUGBCDLMNOUBDPQR $.

    $( Obsolete proof of ~ nfimd as of 29-Dec-2017.  (Contributed by Mario
       Carneiro, 24-Sep-2016.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    nfimdOLD $p |- ( ph -> F/ x ( ps -> ch ) ) $=
      ( wnf wi wal wa nfa1 wn hbnt pm2.21 alimi imim2i adantr ax-1 adantl df-nf
      jad ex syl alimd imp anbi12i 3imtr4i syl2anc ) ABDGZCDGZBCHZDGZEFBBDIHZDI
      ZCCDIZHZDIZJUKUKDIZHZDIZUIUJJULUNUQUTUNUPUSDUMDKUNBLZVADIZHZUPUSHBDMVCUPU
      SVCUPJBCURVCVAURHUPVBURVAVAUKDBCNOPQUPCURHVCUOURCCUKDCBROPSUAUBUCUDUEUIUN
      UJUQBDTCDTUFUKDTUGUH $.
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

    $( A closed form of ~ nfim .  (Contributed by NM, 5-Aug-1993.)  (Revised by
       Mario Carneiro, 24-Sep-2016.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    nfim1OLD $p |- F/ x ( ph -> ps ) $=
      ( wi wal nfrd a2i 19.21 sylibr nfi ) ABFZCMABCGZFMCGABNABCEHIABCDJKL $.
  $}

  ${
    nfim.1 $e |- F/ x ph $.
    nfim.2 $e |- F/ x ps $.
    $( If ` x ` is not free in ` ph ` and ` ps ` , it is not free in
       ` ( ph -> ps ) ` .  (Contributed by Mario Carneiro, 11-Aug-2016.)
       (Proof shortened by Wolf Lammen, 2-Jan-2018.) $)
    nfim $p |- F/ x ( ph -> ps ) $=
      ( wnf a1i nfim1 ) ABCDBCFAEGH $.

    $( If ` x ` is not free in ` ph ` and ` ps ` , it is not free in
       ` ( ph -> ps ) ` .  (Contributed by Mario Carneiro, 11-Aug-2016.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    nfimOLD $p |- F/ x ( ph -> ps ) $=
      ( wi wnf wtru a1i nfimd trud ) ABFCGHABCACGHDIBCGHEIJK $.
  $}

  ${
    hbimd.1 $e |- ( ph -> A. x ph ) $.
    hbimd.2 $e |- ( ph -> ( ps -> A. x ps ) ) $.
    hbimd.3 $e |- ( ph -> ( ch -> A. x ch ) ) $.
    $( Deduction form of bound-variable hypothesis builder ~ hbim .
       (Contributed by NM, 1-Jan-2002.)  (Proof shortened by Wolf Lammen,
       3-Jan-2018.) $)
    hbimd $p |- ( ph -> ( ( ps -> ch ) -> A. x ( ps -> ch ) ) ) $=
      ( wi nfdh nfimd nfrd ) ABCHDABCDABDEFIACDEGIJK $.

    $( Obsolete proof of ~ hbimd as of 16-Dec-2017.  (Contributed by NM,
       1-Jan-2002.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    hbimdOLD $p |- ( ph -> ( ( ps -> ch ) -> A. x ( ps -> ch ) ) ) $=
      ( wi wal wn alrimih sp hbn1 nsyl4 con1i con3 al2imi syl2im alimi syl6 jad
      pm2.21 ax-1 ) ABCBCHZDIZABJZUFDIZUEABBDIZHZDIUFUHJZDIZUGAUIDEFKUKBUHBUKBD
      LBDMNOUIUJUFDBUHPQRUFUDDBCUBSTACCDIUEGCUDDCBUCSTUA $.
  $}

  ${
    hbim.1 $e |- ( ph -> A. x ph ) $.
    hbim.2 $e |- ( ps -> A. x ps ) $.
    $( If ` x ` is not free in ` ph ` and ` ps ` , it is not free in
       ` ( ph -> ps ) ` .  (Contributed by NM, 5-Aug-1993.)  (Proof shortened
       by O'Cat, 3-Mar-2008.)  (Proof shortened by Wolf Lammen, 1-Jan-2018.) $)
    hbim $p |- ( ( ph -> ps ) -> A. x ( ph -> ps ) ) $=
      ( wal wi a1i hbim1 ) ABCDBBCFGAEHI $.

    $( Obsolete proof of ~ hbim as of 1-Jan-2018.  (Contributed by NM,
       5-Aug-1993.)  (Proof shortened by O'Cat, 3-Mar-2008.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    hbimOLD $p |- ( ( ph -> ps ) -> A. x ( ph -> ps ) ) $=
      ( wi wal wn hbn pm2.21 alrimih ax-1 ja ) ABABFZCGAHNCACDIABJKBNCEBALKM $.
  $}

  $( Obsolete proof of ~ 19.23t as of 1-Jan-2018.  (Contributed by NM,
     7-Nov-2005.)  (New usage is discouraged.)
     (Proof modification is discouraged.) $)
  19.23tOLD $p |- ( F/ x ps -> ( A. x ( ph -> ps ) <-> ( E. x ph -> ps ) ) ) $=
    ( wnf wi wal wex exim 19.9t imbi2d syl5ib nfnf1 nfe1 a1i nfimd 19.8a imim1d
    id alrimdd impbid ) BCDZABEZCFZACGZBEZUCUDBCGZEUAUEABCHUAUFBUDBCIJKUAUEUBCB
    CLUAUDBCUDCDUAACMNUAROUAAUDBAUDEUAACPNQST $.

  ${
    19.23hOLD.1 $e |- ( ps -> A. x ps ) $.
    $( Obsolete proof of ~ 19.23h as of 1-Jan-2018.  (Contributed by NM,
       5-Aug-1993.)  (Revised by Mario Carneiro, 24-Sep-2016.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    19.23hOLD $p |- ( A. x ( ph -> ps ) <-> ( E. x ph -> ps ) ) $=
      ( wi wal wex exim 19.9h syl6ib hbe1 hbim 19.8a imim1i alrimih impbii ) AB
      EZCFZACGZBEZRSBCGBABCHBCDIJTQCSBCACKDLASBACMNOP $.
  $}


  ${
    $d x z $.  $d w ph $.
    spimehOLD.1 $e |- ( ph -> A. x ph ) $.
    spimehOLD.2 $e |- ( x = z -> ( ph -> ps ) ) $.
    $( Obsolete proof of ~ spimeh as of 10-Dec-2017.  (Contributed by NM,
       7-Aug-1994.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    spimehOLD $p |- ( ph -> E. x ps ) $=
      ( wn wal wex wi weq ax9v id hbth hba1 a1i hbn hbimd ax-mp sp nsyli sylibr
      con3i alrimih mt3 con2i df-ex ) ABGZCHZGBCIUIAUIAGZJZCDKZGZCHCDLUKGUMCUKC
      AAJZUKUKCHJAMZUNUIUJCUNCUONUIUICHJUNUHCOPUJUJCHJUNACEQPRSQULUKULABUIFUHCT
      UAUCUDUEUFBCUGUB $.
  $}

  ${
    19.27.1 $e |- F/ x ps $.
    $( Theorem 19.27 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)
    19.27 $p |- ( A. x ( ph /\ ps ) <-> ( A. x ph /\ ps ) ) $=
      ( wa wal 19.26 19.3 anbi2i bitri ) ABECFACFZBCFZEKBEABCGLBKBCDHIJ $.
  $}

  ${
    19.28.1 $e |- F/ x ph $.
    $( Theorem 19.28 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)
    19.28 $p |- ( A. x ( ph /\ ps ) <-> ( ph /\ A. x ps ) ) $=
      ( wa wal 19.26 19.3 anbi1i bitri ) ABECFACFZBCFZEALEABCGKALACDHIJ $.
  $}

  ${
    nfand.1 $e |- ( ph -> F/ x ps ) $.
    nfand.2 $e |- ( ph -> F/ x ch ) $.
    $( If in a context ` x ` is not free in ` ps ` and ` ch ` , it is not free
       in ` ( ps /\ ch ) ` .  (Contributed by Mario Carneiro, 7-Oct-2016.) $)
    nfand $p |- ( ph -> F/ x ( ps /\ ch ) ) $=
      ( wa wn wi df-an nfnd nfimd nfxfrd ) BCGBCHZIZHADBCJAODABNDEACDFKLKM $.

    nfand.3 $e |- ( ph -> F/ x th ) $.
    $( Deduction form of bound-variable hypothesis builder ~ nf3an .
       (Contributed by NM, 17-Feb-2013.)  (Revised by Mario Carneiro,
       16-Oct-2016.) $)
    nf3and $p |- ( ph -> F/ x ( ps /\ ch /\ th ) ) $=
      ( w3a wa df-3an nfand nfxfrd ) BCDIBCJZDJAEBCDKANDEABCEFGLHLM $.
  $}


  ${
    nfan1.1 $e |- F/ x ph $.
    nfan1.2 $e |- ( ph -> F/ x ps ) $.
    $( A closed form of ~ nfan .  (Contributed by Mario Carneiro,
       3-Oct-2016.) $)
    nfan1 $p |- F/ x ( ph /\ ps ) $=
      ( wa wal nfrd imdistani 19.28 sylibr nfi ) ABFZCMABCGZFMCGABNABCEHIABCDJK
      L $.
  $}

  ${
    nfan.1 $e |- F/ x ph $.
    nfan.2 $e |- F/ x ps $.
    $( If ` x ` is not free in ` ph ` and ` ps ` , it is not free in
       ` ( ph /\ ps ) ` .  (Contributed by Mario Carneiro, 11-Aug-2016.)
       (Proof shortened by Wolf Lammen, 13-Jan-2018.) $)
    nfan $p |- F/ x ( ph /\ ps ) $=
      ( wnf a1i nfan1 ) ABCDBCFAEGH $.

    $( If ` x ` is not free in ` ph ` and ` ps ` , then it is not free in
       ` ( ph -/\ ps ) ` .  (Contributed by Scott Fenton, 2-Jan-2018.) $)
    nfnan $p |- F/ x ( ph -/\ ps ) $=
      ( wnan wa wn df-nan nfan nfn nfxfr ) ABFABGZHCABIMCABCDEJKL $.

    $( Obsolete proof of ~ nfan as of 2-Jan-2018.  (Contributed by Mario
       Carneiro, 11-Aug-2016.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    nfanOLD $p |- F/ x ( ph /\ ps ) $=
      ( wa wn wi df-an nfn nfim nfxfr ) ABFABGZHZGCABINCAMCDBCEJKJL $.

    nfan.3 $e |- F/ x ch $.
    $( If ` x ` is not free in ` ph ` , ` ps ` , and ` ch ` , it is not free in
       ` ( ph /\ ps /\ ch ) ` .  (Contributed by Mario Carneiro,
       11-Aug-2016.) $)
    nf3an $p |- F/ x ( ph /\ ps /\ ch ) $=
      ( w3a wa df-3an nfan nfxfr ) ABCHABIZCIDABCJMCDABDEFKGKL $.
  $}

  ${
    hb.1 $e |- ( ph -> A. x ph ) $.
    hb.2 $e |- ( ps -> A. x ps ) $.
    $( If ` x ` is not free in ` ph ` and ` ps ` , it is not free in
       ` ( ph /\ ps ) ` .  (Contributed by NM, 5-Aug-1993.)  (Proof shortened
       by Wolf Lammen, 2-Jan-2018.) $)
    hban $p |- ( ( ph /\ ps ) -> A. x ( ph /\ ps ) ) $=
      ( wa nfi nfan nfri ) ABFCABCACDGBCEGHI $.
    $( Obsolete proof of ~ hban as of 2-Jan-2018.  (Contributed by NM,
       5-Aug-1993.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    hbanOLD $p |- ( ( ph /\ ps ) -> A. x ( ph /\ ps ) ) $=
      ( wa wn wi df-an hbn hbim hbxfrbi ) ABFABGZHZGCABINCAMCDBCEJKJL $.

    hb.3 $e |- ( ch -> A. x ch ) $.
    $( If ` x ` is not free in ` ph ` , ` ps ` , and ` ch ` , it is not free in
       ` ( ph /\ ps /\ ch ) ` .  (Contributed by NM, 14-Sep-2003.)  (Proof
       shortened by Wolf Lammen, 2-Jan-2018.) $)
    hb3an $p |- ( ( ph /\ ps /\ ch ) -> A. x ( ph /\ ps /\ ch ) ) $=
      ( w3a nfi nf3an nfri ) ABCHDABCDADEIBDFICDGIJK $.

    $( Obsolete proof of ~ hb3an as of 2-Jan-2018.  (Contributed by NM,
       14-Sep-2003.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    hb3anOLD $p |- ( ( ph /\ ps /\ ch ) -> A. x ( ph /\ ps /\ ch ) ) $=
      ( w3a wa df-3an hban hbxfrbi ) ABCHABIZCIDABCJMCDABDEFKGKL $.
  $}

  ${
    nfbid.1 $e |- ( ph -> F/ x ps ) $.
    nfbid.2 $e |- ( ph -> F/ x ch ) $.
    $( If in a context ` x ` is not free in ` ps ` and ` ch ` , it is not free
       in ` ( ps <-> ch ) ` .  (Contributed by Mario Carneiro, 24-Sep-2016.)
       (Proof shortened by Wolf Lammen, 29-Dec-2017.) $)
    nfbid $p |- ( ph -> F/ x ( ps <-> ch ) ) $=
      ( wb wi wa dfbi2 nfimd nfand nfxfrd ) BCGBCHZCBHZIADBCJANODABCDEFKACBDFEK
      LM $.

    $( Obsolete proof of ~ nfbid as of 29-Dec-2017.  (Contributed by Mario
       Carneiro, 24-Sep-2016.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    nfbidOLD $p |- ( ph -> F/ x ( ps <-> ch ) ) $=
      ( wb wi wn dfbi1 nfimd nfnd nfxfrd ) BCGBCHZCBHZIZHZIADBCJAQDANPDABCDEFKA
      ODACBDFEKLKLM $.
  $}

  ${
    nf.1 $e |- F/ x ph $.
    nf.2 $e |- F/ x ps $.
    $( If ` x ` is not free in ` ph ` and ` ps ` , it is not free in
       ` ( ph <-> ps ) ` .  (Contributed by Mario Carneiro, 11-Aug-2016.)
       (Proof shortened by Wolf Lammen, 2-Jan-2018.) $)
    nfbi $p |- F/ x ( ph <-> ps ) $=
      ( wb wnf wtru a1i nfbid trud ) ABFCGHABCACGHDIBCGHEIJK $.

    $( If ` x ` is not free in ` ph ` and ` ps ` , it is not free in
       ` ( ph <-> ps ) ` .  (Contributed by Mario Carneiro, 11-Aug-2016.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    nfbiOLD $p |- F/ x ( ph <-> ps ) $=
      ( wb wi wa dfbi2 nfim nfan nfxfr ) ABFABGZBAGZHCABIMNCABCDEJBACEDJKL $.

    $( If ` x ` is not free in ` ph ` and ` ps ` , it is not free in
       ` ( ph \/ ps ) ` .  (Contributed by Mario Carneiro, 11-Aug-2016.) $)
    nfor $p |- F/ x ( ph \/ ps ) $=
      ( wo wn wi df-or nfn nfim nfxfr ) ABFAGZBHCABIMBCACDJEKL $.

    nf.3 $e |- F/ x ch $.
    $( If ` x ` is not free in ` ph ` , ` ps ` , and ` ch ` , it is not free in
       ` ( ph \/ ps \/ ch ) ` .  (Contributed by Mario Carneiro,
       11-Aug-2016.) $)
    nf3or $p |- F/ x ( ph \/ ps \/ ch ) $=
      ( w3o wo df-3or nfor nfxfr ) ABCHABIZCIDABCJMCDABDEFKGKL $.
  $}

  ${
    $d x y $.
    equsalhw.1 $e |- ( ps -> A. x ps ) $.
    equsalhw.2 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Weaker version of ~ equsalh (requiring distinct variables) without using
       ~ ax-12 .  (Contributed by NM, 29-Nov-2015.)  (Proof shortened by Wolf
       Lammen, 28-Dec-2017.) $)
    equsalhw $p |- ( A. x ( x = y -> ph ) <-> ps ) $=
      ( weq wi wal wex 19.23h pm5.74i albii a9ev a1bi 3bitr4i ) CDGZBHZCIQCJZBH
      QAHZCIBQBCEKTRCQABFLMSBCDNOP $.
  $}

  ${
    $d x y $.
    equsalhwOLD.1 $e |- ( ps -> A. x ps ) $.
    equsalhwOLD.2 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Obsolete proof of ~ equsalhw as of 28-Dec-2017.  (Contributed by NM,
       29-Nov-2015.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    equsalhwOLD $p |- ( A. x ( x = y -> ph ) <-> ps ) $=
      ( weq wi wal sp impbii syl6bbr pm5.74i albii a1d alrimih ax9v con3 al2imi
      wn mtoi ax6o syl bitr4i ) CDGZAHZCIUEBCIZHZCIZBUFUHCUEAUGUEABUGFUGBBCJEKL
      MNBUIBUHCEBUGUEEOPUIUGTZCIZTBUIUKUETZCICDQUHUJULCUEUGRSUABCUBUCKUD $.
  $}

  ${
    19.21hOLD.1 $e |- ( ph -> A. x ph ) $.
    $( Obsolete proof of ~ 19.21h as of 1-Jan-2018.  (Contributed by NM,
       1-Aug-2017.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    19.21hOLD $p |- ( A. x ( ph -> ps ) <-> ( ph -> A. x ps ) ) $=
      ( wi wal alim syl5 hba1 hbim sp imim2i alrimih impbii ) ABEZCFZABCFZEZAAC
      FPQDABCGHROCAQCDBCIJQBABCKLMN $.
  $}

  ${
    hbex.1 $e |- ( ph -> A. x ph ) $.
    $( If ` x ` is not free in ` ph ` , it is not free in ` E. y ph ` .
       (Contributed by NM, 5-Aug-1993.) $)
    hbex $p |- ( E. y ph -> A. x E. y ph ) $=
      ( wex wn wal df-ex hbn hbal hbxfrbi ) ACEAFZCGZFBACHMBLBCABDIJIK $.
  $}

  ${
    nfal.1 $e |- F/ x ph $.
    $( If ` x ` is not free in ` ph ` , it is not free in ` A. y ph ` .
       (Contributed by Mario Carneiro, 11-Aug-2016.) $)
    nfal $p |- F/ x A. y ph $=
      ( wal nfri hbal nfi ) ACEBABCABDFGH $.

    $( If ` x ` is not free in ` ph ` , it is not free in ` E. y ph ` .
       (Contributed by Mario Carneiro, 11-Aug-2016.)  (Proof shortened by Wolf
       Lammen, 30-Dec-2017.) $)
    nfex $p |- F/ x E. y ph $=
      ( wex nfri hbex nfi ) ACEBABCABDFGH $.

    $( Obsolete proof of ~ nfex as of 30-Dec-2017.  (Contributed by Mario
       Carneiro, 11-Aug-2016.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    nfexOLD $p |- F/ x E. y ph $=
      ( wex wn wal df-ex nfn nfal nfxfr ) ACEAFZCGZFBACHMBLBCABDIJIK $.

    $( If ` x ` is not free in ` ph ` , it is not free in ` F/ y ph ` .
       (Contributed by Mario Carneiro, 11-Aug-2016.)  (Proof shortened by Wolf
       Lammen, 30-Dec-2017.) $)
    nfnf $p |- F/ x F/ y ph $=
      ( wnf wal wi df-nf nfal nfim nfxfr ) ACEAACFZGZCFBACHMBCALBDABCDIJIK $.

    $( Obsolete proof of ~ nfnf as of 30-Dec-2017.  (Contributed by Mario
       Carneiro, 11-Aug-2016.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    nfnfOLD $p |- F/ x F/ y ph $=
      ( wnf wal wi df-nf wtru a1i nfal nfimd trud nfxfr ) ACEAACFZGZCFBACHPBCPB
      EIAOBABEIDJOBEIABCDKJLMKN $.
  $}

  $( Theorem 19.12 of [Margaris] p. 89.  Assuming the converse is a mistake
     sometimes made by beginners!  But sometimes the converse does hold, as in
     ~ 19.12vv and ~ r19.12sn .  (Contributed by NM, 5-Aug-1993.)  (Proof
     shortened by Wolf Lammen, 3-Jan-2018.) $)
  19.12 $p |- ( E. x A. y ph -> A. y E. x ph ) $=
    ( wal wex nfa1 nfex sp eximi alrimi ) ACDZBEABECKCBACFGKABACHIJ $.

  $( Obsolete proof of ~ 19.12 as of 3-Jan-2018.  (Contributed by NM,
     5-Aug-1993.)  (New usage is discouraged.)
     (Proof modification is discouraged.) $)
  19.12OLD $p |- ( E. x A. y ph -> A. y E. x ph ) $=
    ( wal wex hba1 hbex sp eximi alrimih ) ACDZBEABECKCBACFGKABACHIJ $.

  ${
    nfald.1 $e |- F/ y ph $.
    nfald.2 $e |- ( ph -> F/ x ps ) $.
    $( If ` x ` is not free in ` ph ` , it is not free in ` A. y ph ` .
       (Contributed by Mario Carneiro, 24-Sep-2016.)  (Proof shortened by Wolf
       Lammen, 6-Jan-2018.) $)
    nfald $p |- ( ph -> F/ x A. y ps ) $=
      ( wnf wal alrimi nfnf1 nfal hba1 sp nfrd hbald nfd syl ) ABCGZDHZBDHZCGAR
      DEFISTCRCDBCJKSBCDRDLSBCRDMNOPQ $.

    $( Obsolete proof of ~ nfald as of 6-Jan-2018.  (Contributed by Mario
       Carneiro, 24-Sep-2016.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    nfaldOLD $p |- ( ph -> F/ x A. y ps ) $=
      ( wnf wal alrimi nfnf1 nfal nfr al2imi ax-7 syl6 nfd syl ) ABCGZDHZBDHZCG
      ARDEFISTCRCDBCJKSTBCHZDHTCHRBUADBCLMBDCNOPQ $.

    $( If ` x ` is not free in ` ph ` , it is not free in ` E. y ph ` .
       (Contributed by Mario Carneiro, 24-Sep-2016.) $)
    nfexd $p |- ( ph -> F/ x E. y ps ) $=
      ( wex wn wal df-ex nfnd nfald nfxfrd ) BDGBHZDIZHACBDJAOCANCDEABCFKLKM $.
  $}

  $( Lemma 24 of [Monk2] p. 114.  (Contributed by Mario Carneiro,
     24-Sep-2016.) $)
  nfa2 $p |- F/ x A. y A. x ph $=
    ( wal nfa1 nfal ) ABDBCABEF $.

  $( Lemma 23 of [Monk2] p. 114.  (Contributed by Mario Carneiro,
     24-Sep-2016.) $)
  nfia1 $p |- F/ x ( A. x ph -> A. x ps ) $=
    ( wal nfa1 nfim ) ACDBCDCACEBCEF $.

  ${
    $d x z $.  $d y z $.
    dvelimhw.1 $e |- ( ph -> A. x ph ) $.
    dvelimhw.2 $e |- ( ps -> A. z ps ) $.
    dvelimhw.3 $e |- ( z = y -> ( ph <-> ps ) ) $.
    $(  dvelimhw.4 $e |- ( -. A. x x = y -> ( z = y -> A. x z = y ) ) $. $)
    dvelimhw.4 $e |- ( -. A. x x = y -> ( y = z -> A. x y = z ) ) $.
    $( Proof of ~ dvelimh without using ~ ax-12 but with additional distinct
       variable conditions.  (Contributed by Andrew Salmon, 21-Jul-2011.)
       (Revised by NM, 1-Aug-2017.)  (Proof shortened by Wolf Lammen,
       3-Mar-2018.) $)
    dvelimhw $p |- ( -. A. x x = y -> ( ps -> A. x ps ) ) $=
      ( weq wal wn wi wnf nfv equcom nfa1 nfn nfd nfxfrd nfi a1i nfimd equsalhw
      nfald nfbii sylib nfrd ) CDJZCKZLZBCUKEDJZAMZEKZCNBCNUKUMCEUKEOUKULACULDE
      JZUKCEDPUKUOCUJCUICQRISTACNUKACFUAUBUCUEUNBCABEDGHUDUFUGUH $.

    $( Proof of ~ dvelimh without using ~ ax-12 but with additional distinct
       variable conditions.  (Contributed by Andrew Salmon, 21-Jul-2011.)
       (Revised by NM, 1-Aug-2017.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    dvelimhwOLD $p |- ( -. A. x x = y -> ( ps -> A. x ps ) ) $=
      ( weq wal wn wi ax-17 hbn1 equcomi alimi syl56 a1i hbimd equsalhw 3imtr3g
      hbald albii ) CDJZCKLZEDJZAMZEKZUICKBBCKUFUHCEUFENUFUGACUECOUGDEJZUFUJCKU
      GCKEDPIUJUGCDEPQRAACKMUFFSTUCABEDGHUAZUIBCUKUDUB $.
  $}

  ${
    $d x y $.
    cbv3hv.1 $e |- ( ph -> A. y ph ) $.
    cbv3hv.2 $e |- ( ps -> A. x ps ) $.
    cbv3hv.3 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( Lemma for ~ ax10 .  Similar to ~ cbv3h .  Requires distinct variables
       but avoids ~ ax-12 .  (Contributed by NM, 25-Jul-2015.)  (Proof
       shortened by Wolf Lammen, 29-Dec-2017.) $)
    cbv3hv $p |- ( A. x ph -> A. y ps ) $=
      ( wal alimi wex weq wi a9ev eximii 19.35i 19.9h sylib a7s syl ) ACHZADHZC
      HBDHZAUACEIAUBDCTBDTBCJBABCCDKABLCCDMGNOBCFPQIRS $.

    $( Obsolete proof of ~ cbv3hv as of 29-Dec-2017.  (Contributed by NM,
       25-Jul-2015.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    cbv3hvOLD $p |- ( A. x ph -> A. y ps ) $=
      ( wal alimi wi weq wn ax9v hba1 hbim hbn sp syl5 con3i alrimih mt3 a7s
      syl ) ACHZADHZCHBDHZAUECEIAUFDCUDBDUDBJZCDKZLZCHCDMUGLUICUGCUDBCACNFOPUHU
      GUDAUHBACQGRSTUAIUBUC $.
  $}

  $( Obsolete proof of ~ 19.9t as of 30-Dec-2017.  (Contributed by NM,
     5-Aug-1993.)  (Revised by Mario Carneiro, 24-Sep-2016.)
     (New usage is discouraged.)  (Proof modification is discouraged.) $)
  19.9tOLD $p |- ( F/ x ph -> ( E. x ph <-> ph ) ) $=
    ( wnf wex wn wal df-ex id nfnd nfrd con1d syl5bi 19.8a impbid1 ) ABCZABDZAP
    AEZBFZEOAABGOAROQBOABOHIJKLABMN $.

  $( Obsolete proof of ~ excomim as of 8-Jan-2018.  (Contributed by NM,
     5-Aug-1993.)  (Revised by Mario Carneiro, 24-Sep-2016.)
     (New usage is discouraged.)  (Proof modification is discouraged.) $)
  excomimOLD $p |- ( E. x E. y ph -> E. y E. x ph ) $=
    ( wex 19.8a 2eximi nfe1 nfex 19.9 sylib ) ACDBDABDZCDZBDLAKBCABEFLBKBCABGHI
    J $.

  $( Obsolete proof of ~ excom as of 8-Jan-2018.  (Contributed by NM,
     5-Aug-1993.)  (New usage is discouraged.)
     (Proof modification is discouraged.) $)
  excomOLD $p |- ( E. x E. y ph <-> E. y E. x ph ) $=
    ( wex excomim impbii ) ACDBDABDCDABCEACBEF $.

  ${
    19.16.1 $e |- F/ x ph $.
    $( Theorem 19.16 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)
    19.16 $p |- ( A. x ( ph <-> ps ) -> ( ph <-> A. x ps ) ) $=
      ( wal wb 19.3 albi syl5bbr ) AACEABFCEBCEACDGABCHI $.
  $}

  ${
    19.17.1 $e |- F/ x ps $.
    $( Theorem 19.17 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)
    19.17 $p |- ( A. x ( ph <-> ps ) -> ( A. x ph <-> ps ) ) $=
      ( wb wal albi 19.3 syl6bb ) ABECFACFBCFBABCGBCDHI $.
  $}

  ${
    19.19.1 $e |- F/ x ph $.
    $( Theorem 19.19 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)
    19.19 $p |- ( A. x ( ph <-> ps ) -> ( ph <-> E. x ps ) ) $=
      ( wex wb wal 19.9 exbi syl5bbr ) AACEABFCGBCEACDHABCIJ $.
  $}

  $( Obsolete proof of ~ 19.21t as of 30-Dec-2017.  (Contributed by NM,
     27-May-1997.)  (Revised by Mario Carneiro, 24-Sep-2016.)
     (New usage is discouraged.)  (Proof modification is discouraged.) $)
  19.21tOLD $p |- ( F/ x ph -> ( A. x ( ph -> ps ) <-> ( ph -> A. x ps ) ) ) $=
    ( wnf wi wal id nfrd alim syl9 nfa1 a1i nfimd sp imim2i alimi syl6 impbid )
    ACDZABEZCFZABCFZEZSAACFUAUBSACSGZHABCIJSUCUCCFUASUCCSAUBCUDUBCDSBCKLMHUCTCU
    BBABCNOPQR $.

  ${
    19.21-2.1 $e |- F/ x ph $.
    19.21-2.2 $e |- F/ y ph $.
    $( Theorem 19.21 of [Margaris] p. 90 but with 2 quantifiers.  (Contributed
       by NM, 4-Feb-2005.) $)
    19.21-2 $p |- ( A. x A. y ( ph -> ps ) <-> ( ph -> A. x A. y ps ) ) $=
      ( wi wal 19.21 albii bitri ) ABGDHZCHABDHZGZCHAMCHGLNCABDFIJAMCEIK $.
  $}

  ${
    19.21bbi.1 $e |- ( ph -> A. x A. y ps ) $.
    $( Inference removing double quantifier.  (Contributed by NM,
       20-Apr-1994.) $)
    19.21bbi $p |- ( ph -> ps ) $=
      ( wal 19.21bi ) ABDABDFCEGG $.
  $}

  $( An alternative definition of ~ df-nf , which does not involve nested
     quantifiers on the same variable.  (Contributed by Mario Carneiro,
     24-Sep-2016.) $)
  nf2 $p |- ( F/ x ph <-> ( E. x ph -> A. x ph ) ) $=
    ( wnf wal wi wex df-nf nfa1 19.23 bitri ) ABCAABDZEBDABFKEABGAKBABHIJ $.

  $( An alternative definition of ~ df-nf .  (Contributed by Mario Carneiro,
     24-Sep-2016.) $)
  nf3 $p |- ( F/ x ph <-> A. x ( E. x ph -> ph ) ) $=
    ( wnf wex wal wi nf2 nfe1 19.21 bitr4i ) ABCABDZABEFKAFBEABGKABABHIJ $.

  $( Variable ` x ` is effectively not free in ` ph ` iff ` ph ` is always true
     or always false.  (Contributed by Mario Carneiro, 24-Sep-2016.) $)
  nf4 $p |- ( F/ x ph <-> ( A. x ph \/ A. x -. ph ) ) $=
    ( wnf wex wal wi wn wo nf2 imor orcom alnex orbi2i bitr4i 3bitri ) ABCABDZA
    BEZFPGZQHZQAGBEZHZABIPQJSQRHUARQKTRQABLMNO $.

  ${
    nfdi.1 $e |- ( ph -> F/ x ph ) $.
    $( Since the converse holds by ~ a1i , this inference shows that we can
       represent a not-free hypothesis with either ` F/ x ph ` (inference form)
       or ` ( ph -> F/ x ph ) ` (deduction form).  (Contributed by NM,
       17-Aug-2018.) $)
    nfdi $p |- F/ x ph $=
      ( wex wal 19.8a wnf wi nf2 sylib mpd nfi ) ABAABDZABEZABFAABGMNHCABIJKL
      $.
  $}

  ${
    19.36.1 $e |- F/ x ps $.
    $( Theorem 19.36 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)
    19.36 $p |- ( E. x ( ph -> ps ) <-> ( A. x ph -> ps ) ) $=
      ( wi wex wal 19.35 19.9 imbi2i bitri ) ABECFACGZBCFZELBEABCHMBLBCDIJK $.

    19.36i.2 $e |- E. x ( ph -> ps ) $.
    $( Inference from Theorem 19.36 of [Margaris] p. 90.  (Contributed by NM,
       5-Aug-1993.) $)
    19.36i $p |- ( A. x ph -> ps ) $=
      ( wi wex wal 19.36 mpbi ) ABFCGACHBFEABCDIJ $.
  $}

  ${
    19.37.1 $e |- F/ x ph $.
    $( Theorem 19.37 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)
    19.37 $p |- ( E. x ( ph -> ps ) <-> ( ph -> E. x ps ) ) $=
      ( wi wex wal 19.35 19.3 imbi1i bitri ) ABECFACGZBCFZEAMEABCHLAMACDIJK $.
  $}

  $( Obsolete proof of ~ 19.38 as of 2-Jan-2018.  (Contributed by NM,
     5-Aug-1993.)  (New usage is discouraged.)
     (Proof modification is discouraged.) $)
  19.38OLD $p |- ( ( E. x ph -> A. x ps ) -> A. x ( ph -> ps ) ) $=
    ( wex wal wi nfe1 nfa1 nfim 19.8a sp imim12i alrimi ) ACDZBCEZFABFCNOCACGBC
    HIANOBACJBCKLM $.

  ${
    19.32.1 $e |- F/ x ph $.
    $( Theorem 19.32 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.)
       (Revised by Mario Carneiro, 24-Sep-2016.) $)
    19.32 $p |- ( A. x ( ph \/ ps ) <-> ( ph \/ A. x ps ) ) $=
      ( wn wi wal wo nfn 19.21 df-or albii 3bitr4i ) AEZBFZCGNBCGZFABHZCGAPHNBC
      ACDIJQOCABKLAPKM $.
  $}

  ${
    19.31.1 $e |- F/ x ps $.
    $( Theorem 19.31 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)
    19.31 $p |- ( A. x ( ph \/ ps ) <-> ( A. x ph \/ ps ) ) $=
      ( wo wal 19.32 orcom albii 3bitr4i ) BAEZCFBACFZEABEZCFLBEBACDGMKCABHILBH
      J $.
  $}

  ${
    19.44.1 $e |- F/ x ps $.
    $( Theorem 19.44 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)
    19.44 $p |- ( E. x ( ph \/ ps ) <-> ( E. x ph \/ ps ) ) $=
      ( wo wex 19.43 19.9 orbi2i bitri ) ABECFACFZBCFZEKBEABCGLBKBCDHIJ $.
  $}

  ${
    19.45.1 $e |- F/ x ph $.
    $( Theorem 19.45 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)
    19.45 $p |- ( E. x ( ph \/ ps ) <-> ( ph \/ E. x ps ) ) $=
      ( wo wex 19.43 19.9 orbi1i bitri ) ABECFACFZBCFZEALEABCGKALACDHIJ $.
  $}

  ${
    19.41.1 $e |- F/ x ps $.
    $( Theorem 19.41 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.)
       (Proof shortened by Andrew Salmon, 25-May-2011.)  (Proof shortened by
       Wolf Lammen, 12-Jan-2018.) $)
    19.41 $p |- ( E. x ( ph /\ ps ) <-> ( E. x ph /\ ps ) ) $=
      ( wa wex 19.40 19.9 anbi2i sylib pm3.21 eximd impcom impbii ) ABEZCFZACFZ
      BEZPQBCFZERABCGSBQBCDHIJBQPBAOCDBAKLMN $.

    $( Obsolete proof of ~ 19.41 as of 12-Jan-2018.  (Contributed by NM,
       5-Aug-1993.)  (Proof shortened by Andrew Salmon, 25-May-2011.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    19.41OLD $p |- ( E. x ( ph /\ ps ) <-> ( E. x ph /\ ps ) ) $=
      ( wa wex 19.40 id exlimi anim2i syl pm3.21 eximd impcom impbii ) ABEZCFZA
      CFZBEZQRBCFZESABCGTBRBBCDBHIJKBRQBAPCDBALMNO $.
  $}

  ${
    19.42.1 $e |- F/ x ph $.
    $( Theorem 19.42 of [Margaris] p. 90.  (Contributed by NM, 18-Aug-1993.) $)
    19.42 $p |- ( E. x ( ph /\ ps ) <-> ( ph /\ E. x ps ) ) $=
      ( wa wex 19.41 exancom ancom 3bitr4i ) BAECFBCFZAEABECFAKEBACDGABCHAKIJ
      $.
  $}

  ${
    exan.1 $e |- ( E. x ph /\ ps ) $.
    $( Place a conjunct in the scope of an existential quantifier.
       (Contributed by NM, 18-Aug-1993.)  (Proof shortened by Andrew Salmon,
       25-May-2011.)  (Proof shortened by Wolf Lammen, 13-Jan-2018.) $)
    exan $p |- E. x ( ph /\ ps ) $=
      ( wa wex simpri nfth 19.41 mpbir ) ABECFACFZBEDABCBCKBDGHIJ $.

    $( Obsolete proof of ~ exan as of 13-Jan-2018.  (Contributed by NM,
       18-Aug-1993.)  (Proof shortened by Andrew Salmon, 25-May-2011.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    exanOLD $p |- E. x ( ph /\ ps ) $=
      ( wex wal wa nfe1 19.28 mpgbi 19.29r ax-mp ) ACEZBCFGZABGCEMBGNCMBCACHIDJ
      ABCKL $.
  $}

  ${
    hbnd.1 $e |- ( ph -> A. x ph ) $.
    hbnd.2 $e |- ( ph -> ( ps -> A. x ps ) ) $.
    $( Deduction form of bound-variable hypothesis builder ~ hbn .
       (Contributed by NM, 3-Jan-2002.) $)
    hbnd $p |- ( ph -> ( -. ps -> A. x -. ps ) ) $=
      ( wal wi wn alrimih hbnt syl ) ABBCFGZCFBHZMCFGALCDEIBCJK $.
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
    eeor.1 $e |- F/ y ph $.
    eeor.2 $e |- F/ x ps $.
    $( Rearrange existential quantifiers.  (Contributed by NM, 8-Aug-1994.) $)
    eeor $p |- ( E. x E. y ( ph \/ ps ) <-> ( E. x ph \/ E. y ps ) ) $=
      ( wo wex 19.45 exbii nfex 19.44 bitri ) ABGDHZCHABDHZGZCHACHOGNPCABDEIJAO
      CBCDFKLM $.
  $}

  $( Quantified "excluded middle."  Exercise 9.2a of Boolos, p. 111,
     _Computability and Logic_.  (Contributed by NM, 10-Dec-2000.) $)
  qexmid $p |- E. x ( ph -> A. x ph ) $=
    ( wal 19.8a 19.35ri ) AABCZBFBDE $.

  $( A property related to substitution that unlike ~ equs5 doesn't require a
     distinctor antecedent.  (Contributed by NM, 2-Feb-2007.) $)
  equs5a $p |- ( E. x ( x = y /\ A. y ph ) -> A. x ( x = y -> ph ) ) $=
    ( weq wal wa wi nfa1 ax-11 imp exlimi ) BCDZACEZFLAGZBEZBNBHLMOABCIJK $.

  $( A property related to substitution that unlike ~ equs5 doesn't require a
     distinctor antecedent.  (Contributed by NM, 2-Feb-2007.)  (Proof shortened
     by Wolf Lammen, 15-Jan-2018.) $)
  equs5e $p |- ( E. x ( x = y /\ ph ) -> A. x ( x = y -> E. y ph ) ) $=
    ( weq wa wex wi wal nfa1 hbe1 19.23bi ax-11 syl5 imp exlimi ) BCDZAEPACFZGZ
    BHZBRBIPASAQCHZPSATCACJKQBCLMNO $.

  $( Obsolete proof of ~ equs5e as of 15-Jan-2018.  (Contributed by NM,
     2-Feb-2007.)  (New usage is discouraged.)
     (Proof modification is discouraged.) $)
  equs5eOLD $p |- ( E. x ( x = y /\ ph ) -> A. x ( x = y -> E. y ph ) ) $=
    ( weq wa wex wi nfe1 wn wal equs3 ax-11 con3rr3 df-ex syl6ibr sylbi alrimi
    ) BCDZAEZBFZRACFZGZBSBHTRAIZGBJZIZUBABCKUERUCCJZIUARUFUDUCBCLMACNOPQ $.

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
       eliminating a hypothesis such as ` F/ x ph ` in ~ 19.21 via the use of
       distinct variable conditions combined with ~ nfv .  Conversely, we
       sometimes suffix with "f" the label of a theorem introducing such a
       hypothesis to eliminate the need for the distinct variable condition;
       e.g. ~ euf derived from ~ df-eu .  The "f" stands for "not free in"
       which is less restrictive than "does not occur in."  (Contributed by NM,
       5-Aug-1993.) $)
    19.21v $p |- ( A. x ( ph -> ps ) <-> ( ph -> A. x ps ) ) $=
      ( nfv 19.21 ) ABCACDE $.
  $}

  ${
    $d x ps $.
    $( Special case of Theorem 19.23 of [Margaris] p. 90.  (Contributed by NM,
       28-Jun-1998.) $)
    19.23v $p |- ( A. x ( ph -> ps ) <-> ( E. x ph -> ps ) ) $=
      ( nfv 19.23 ) ABCBCDE $.
  $}

  ${
    $d x ps $.  $d y ps $.
    $( Theorem 19.23 of [Margaris] p. 90 extended to two variables.
       (Contributed by NM, 10-Aug-2004.) $)
    19.23vv $p |- ( A. x A. y ( ph -> ps ) <-> ( E. x E. y ph -> ps ) ) $=
      ( wi wal wex 19.23v albii bitri ) ABEDFZCFADGZBEZCFLCGBEKMCABDHILBCHJ $.
  $}

  ${
    $d ph y $.  $d ps x $.
    $( Theorem *11.53 in [WhiteheadRussell] p. 164.  (Contributed by Andrew
       Salmon, 24-May-2011.) $)
    pm11.53 $p |- ( A. x A. y ( ph -> ps ) <-> ( E. x ph -> A. y ps ) ) $=
      ( wi wal wex 19.21v albii nfv nfal 19.23 bitri ) ABEDFZCFABDFZEZCFACGOENP
      CABDHIAOCBCDBCJKLM $.
  $}

  ${
    $d x ps $.
    $( Theorem 19.27 of [Margaris] p. 90.  (Contributed by NM, 3-Jun-2004.) $)
    19.27v $p |- ( A. x ( ph /\ ps ) <-> ( A. x ph /\ ps ) ) $=
      ( nfv 19.27 ) ABCBCDE $.
  $}

  ${
    $d x ph $.
    $( Theorem 19.28 of [Margaris] p. 90.  (Contributed by NM, 25-Mar-2004.) $)
    19.28v $p |- ( A. x ( ph /\ ps ) <-> ( ph /\ A. x ps ) ) $=
      ( nfv 19.28 ) ABCACDE $.
  $}

  ${
    $d x ps $.
    $( Special case of Theorem 19.36 of [Margaris] p. 90.  (Contributed by NM,
       18-Aug-1993.) $)
    19.36v $p |- ( E. x ( ph -> ps ) <-> ( A. x ph -> ps ) ) $=
      ( nfv 19.36 ) ABCBCDE $.
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
    $d x ps $.  $d y ph $.
    $( Special case of ~ 19.12 where its converse holds.  (Contributed by NM,
       18-Jul-2001.)  (Revised by Andrew Salmon, 11-Jul-2011.) $)
    19.12vv $p |- ( E. x A. y ( ph -> ps ) <-> A. y E. x ( ph -> ps ) ) $=
      ( wi wal wex 19.21v exbii nfv nfal 19.36 19.36v albii 19.21 bitr2i 3bitri
      ) ABEZDFZCGABDFZEZCGACFZTEZRCGZDFZSUACABDHIATCBCDBCJKLUEUBBEZDFUCUDUFDABC
      MNUBBDADCADJKOPQ $.
  $}

  ${
    $d x ph $.
    $( Special case of Theorem 19.37 of [Margaris] p. 90.  (Contributed by NM,
       5-Aug-1993.) $)
    19.37v $p |- ( E. x ( ph -> ps ) <-> ( ph -> E. x ps ) ) $=
      ( nfv 19.37 ) ABCACDE $.
  $}

  ${
    $d x ph $.
    19.37aiv.1 $e |- E. x ( ph -> ps ) $.
    $( Inference from Theorem 19.37 of [Margaris] p. 90.  (Contributed by NM,
       5-Aug-1993.) $)
    19.37aiv $p |- ( ph -> E. x ps ) $=
      ( wi wex 19.37v mpbi ) ABECFABCFEDABCGH $.
  $}

  ${
    $d x ps $.
    $( Special case of Theorem 19.41 of [Margaris] p. 90.  (Contributed by NM,
       5-Aug-1993.) $)
    19.41v $p |- ( E. x ( ph /\ ps ) <-> ( E. x ph /\ ps ) ) $=
      ( nfv 19.41 ) ABCBCDE $.
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
      ( nfv 19.42 ) ABCACDE $.
  $}

  ${
    $d y ph $.
    $( Distribution of existential quantifiers.  (Contributed by NM,
       9-Mar-1995.) $)
    exdistr $p |- ( E. x E. y ( ph /\ ps ) <-> E. x ( ph /\ E. y ps ) ) $=
      ( wa wex 19.42v exbii ) ABEDFABDFECABDGH $.
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
       9-Mar-1995.)  (Proof shortened by Wolf Lammen, 20-Jan-2018.) $)
    4exdistr $p |- ( E. x E. y E. z E. w ( ( ph /\ ps ) /\ ( ch /\ th ) ) <->
                E. x ( ph /\ E. y ( ps /\ E. z ( ch /\ E. w th ) ) ) ) $=
      ( wa wex w3a 19.42v anbi2i df-3an 3bitr4i 3exbii 3exdistr bitri ) ABIZCDI
      ZIHJZGJFJEJABCDHJIZKZGJFJEJABUBGJIFJIEJUAUCEFGSTHJZISUBIUAUCUDUBSCDHLMSTH
      LABUBNOPABUBEFGQR $.
  $}

  ${
    $d y ph $.  $d z ph $.  $d w ph $.  $d z ps $.  $d w ps $.  $d w ch $.
    $( Obsolete proof of ~ 4exdistr as of 20-Jan-2018.  (Contributed by NM,
       9-Mar-1995.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    4exdistrOLD $p |- ( E. x E. y E. z E. w ( ( ph /\ ps ) /\ ( ch /\ th ) )
                <-> E. x ( ph /\ E. y ( ps /\ E. z ( ch /\ E. w th ) ) ) ) $=
      ( wa wex anass exbii 19.42v anbi2i 3bitri bitri ) ABICDIZIZHJZGJZFJZABCDH
      JIZGJIZFJIZEUAAUCIZFJUDTUEFTABUBIZIZGJAUFGJZIUESUGGSABQIZIZHJZUGRUJHABQKL
      UKAUIHJZIABQHJZIZIUGAUIHMULUNABQHMNUNUFAUMUBBCDHMNNOPLAUFGMUHUCABUBGMNOLA
      UCFMPL $.
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
    $d y ph $.  $d z ph $.  $d x ps $.  $d z ps $.  $d x ch $.  $d y ch $.
    $( Rearrange existential quantifiers.  Revised to loosen distinct variable
       restrictions.  (Contributed by NM, 26-Jul-1995.)  (Proof shortened by
       Andrew Salmon, 25-May-2011.)  (Revised by Wolf Lammen, 20-Jan-2018.) $)
    eeeanv $p |- ( E. x E. y E. z ( ph /\ ps /\ ch ) <->
                 ( E. x ph /\ E. y ps /\ E. z ch ) ) $=
      ( wa wex w3a eeanv anbi1i df-3an exbii 19.42v bitri 2exbii nfv nfex 19.41
      3bitri 3bitr4i ) ABGZEHZDHZCFHZGZADHZBEHZGZUEGABCIZFHZEHDHZUGUHUEIUDUIUEA
      BDEJKULUBUEGZEHZDHUCUEGZDHUFUKUMDEUKUBCGZFHUMUJUPFABCLMUBCFNOPUNUODUBUEEC
      EFCEQRSMUCUEDCDFCDQRSTUGUHUELUA $.
  $}

  ${
    $d y ph $.  $d z ph $.  $d x z ps $.  $d x y ch $.
    $( Obsolete proof of ~ eeeanv as of 20-Jan-2018.  (Contributed by NM,
       26-Jul-1995.)  (Proof shortened by Andrew Salmon, 25-May-2011.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    eeeanvOLD $p |- ( E. x E. y E. z ( ph /\ ps /\ ch ) <->
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
    $d x ph $.
    nexdv.1 $e |- ( ph -> -. ps ) $.
    $( Deduction for generalization rule for negated wff.  (Contributed by NM,
       5-Aug-1993.) $)
    nexdv $p |- ( ph -> -. E. x ps ) $=
      ( nfv nexd ) ABCACEDF $.
  $}

  $( One of the two equality axioms of standard predicate calculus, called
     substitutivity of equality.  (The other one is ~ stdpc6 .)  Translated to
     traditional notation, it can be
     read:  " ` x = y -> ( ph ( x , x ) -> ph ( x , y ) ) ` , provided that
     ` y ` is free for ` x ` in ` ph ( x , x ) ` ."  Axiom 7 of [Mendelson]
     p. 95.  (Contributed by NM, 15-Feb-2005.) $)
  stdpc7 $p |- ( x = y -> ( [ x / y ] ph -> ph ) ) $=
    ( wsb wi sbequ2 equcoms ) ACBDAECBACBFG $.

  $( An equality theorem for substitution.  (Contributed by NM, 5-Aug-1993.) $)
  sbequ1 $p |- ( x = y -> ( ph -> [ y / x ] ph ) ) $=
    ( weq wsb wa wi wex pm3.4 19.8a df-sb sylanbrc ex ) BCDZAABCEZNAFZNAGPBHONA
    IPBJABCKLM $.

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

  $( A version of ~ sb4 that doesn't require a distinctor antecedent.
     (Contributed by NM, 2-Feb-2007.) $)
  sb4a $p |- ( [ y / x ] A. y ph -> A. x ( x = y -> ph ) ) $=
    ( wal wsb weq wa wex wi sb1 equs5a syl ) ACDZBCEBCFZMGBHNAIBDMBCJABCKL $.

  $( One direction of a simplified definition of substitution that unlike ~ sb4
     doesn't require a distinctor antecedent.  (Contributed by NM,
     2-Feb-2007.) $)
  sb4e $p |- ( [ y / x ] ph -> A. x ( x = y -> E. y ph ) ) $=
    ( wsb weq wa wex wi wal sb1 equs5e syl ) ABCDBCEZAFBGMACGHBIABCJABCKL $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
          Axiom scheme ax-12 (Quantified Equality)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Axiom of Quantified Equality.  One of the equality and substitution axioms
     of predicate calculus with equality.

     An equivalent way to express this axiom that may be easier to understand
     is ` ( -. x = y -> ( -. x = z -> ( y = z -> A. x y = z ) ) ) ` (see
     ~ ax12b ).  Recall that in the intended interpretation, our variables are
     metavariables ranging over the variables of predicate calculus (the object
     language).  In order for the first antecedent ` -. x = y ` to hold, ` x `
     and ` y ` must have different values and thus cannot be the same
     object-language variable.  Similarly, ` x ` and ` z ` cannot be the same
     object-language variable.  Therefore, ` x ` will not occur in the wff
     ` y = z ` when the first two antecedents hold, so analogous to ~ ax-17 ,
     the conclusion ` ( y = z -> A. x y = z ) ` follows.

     The original version of this axiom was ~ ax-12o and was replaced with this
     shorter ~ ax-12 in December 2015.  The old axiom is proved from this one
     as theorem ~ ax12o .  Conversely, this axiom is proved from ~ ax-12o as
     theorem ~ ax12 .

     The primary purpose of this axiom is to provide a way to introduce the
     quantifier ` A. x ` on ` y = z ` even when ` x ` and ` y ` are substituted
     with the same variable.  In this case, the first antecedent becomes
     ` -. x = x ` and the axiom still holds.

     Although this version is shorter, the original version ~ ax12o may be more
     practical to work with because of the "distinctor" form of its
     antecedents.  A typical application of ~ ax12o is in ~ dvelimh which
     converts a distinct variable pair to the distinctor antecendent
     ` -. A. x x = y ` .

     This axiom can be weakened if desired by adding distinct variable
     restrictions on pairs ` x , z ` and ` y , z ` .  To show that, we add
     these restrictions to theorem ~ ax12v and use only ~ ax12v for further
     derivations.  Thus, ~ ax12v should be the only theorem referencing this
     axiom.  Other theorems can reference either ~ ax12v or ~ ax12o .

     This axiom scheme is logically redundant (see ~ ax12w ) but is used as an
     auxiliary axiom to achieve metalogical completeness.  (Contributed by NM,
     21-Dec-2015.)  (New usage is discouraged.) $)
  ax-12 $a |- ( -. x = y -> ( y = z -> A. x y = z ) ) $.

  ${
    $d x z $.  $d y z $.
    $( A weaker version of ~ ax-12 with distinct variable restrictions on pairs
       ` x , z ` and ` y , z ` .  In order to show that this weakening is
       adequate, this should be the only theorem referencing ~ ax-12 directly.
       (Contributed by NM, 30-Jun-2016.) $)
    ax12v $p |- ( -. x = y -> ( y = z -> A. x y = z ) ) $=
      ( ax-12 ) ABCD $.
  $}

  ${
    $d y v z $.  $d x v z $.
    $( At least one individual exists.  This is not a theorem of free logic,
       which is sound in empty domains.  For such a logic, we would add this
       theorem as an axiom of set theory (Axiom 0 of [Kunen] p. 10).  In the
       system consisting of ~ ax-5 through ~ ax-14 and ~ ax-17 , all axioms
       other than ~ ax-9 are believed to be theorems of free logic, although
       the system without ~ ax-9 is probably not complete in free logic.
       (Contributed by NM, 5-Aug-1993.)  (Revised by Wolf Lammen,
       25-Feb-2018.) $)
    a9e $p |- E. x x = y $=
      ( vv weq wex 19.8a wn wi wal ax12v equequ2 biimprcd eximii 19.35i syl6com
      a9ev equcoms exlimiv ax-mp pm2.61i ) ABDZUAAEZUAAFCBDZCEUAGZUBHZCBPUCUECU
      EBCUDBCDZUFAIUBABCJUFUAAACDZUFUAHAACPUFUAUGBCAKLMNOQRST $.
  $}

  ${
    $d x v z $.  $d y v z $.
    $( Theorem showing that ~ ax-9 follows from the weaker version ~ ax9v .
       (Even though this theorem depends on ~ ax-9 , all references of ~ ax-9
       are made via ~ ax9v .  An earlier version stated ~ ax9v as a separate
       axiom, but having two axioms caused some confusion.)

       This theorem should be referenced in place of ~ ax-9 so that all proofs
       can be traced back to ~ ax9v .  (Contributed by NM, 12-Nov-2013.)
       (Revised by NM, 25-Jul-2015.)  (Proof shortened by Wolf Lammen,
       4-Feb-2018.) $)
    ax9 $p |- -. A. x -. x = y $=
      ( weq wex wn wal a9e df-ex mpbi ) ABCZADJEAFEABGJAHI $.
  $}

  $( Show that the original axiom ~ ax-9o can be derived from ~ ax9 and
     others.  See ~ ax9from9o for the rederivation of ~ ax9 from ~ ax-9o .

     Normally, ~ ax9o should be used rather than ~ ax-9o , except by theorems
     specifically studying the latter's properties.  (Contributed by NM,
     5-Aug-1993.)  (Proof modification is discouraged.) $)
  ax9o $p |- ( A. x ( x = y -> A. x ph ) -> ph ) $=
    ( weq wal wi wn ax9 con3 al2imi mtoi ax6o syl ) BCDZABEZFZBEZOGZBEZGAQSNGZB
    EBCHPRTBNOIJKABLM $.

  $( Closed theorem form of ~ spim .  (Contributed by NM, 15-Jan-2008.)
     (Revised by Mario Carneiro, 17-Oct-2016.)  (Proof shortened by Wolf
     Lammen, 24-Feb-2018.) $)
  spimt $p |- ( ( F/ x ps /\ A. x ( x = y -> ( ph -> ps ) ) ) ->
              ( A. x ph -> ps ) ) $=
    ( weq wi wal wex wnf a9e exim mpi 19.35 sylib 19.9t biimpd sylan9r ) CDEZAB
    FZFCGZACGZBCHZBCIZBTSCHZUAUBFTRCHUDCDJRSCKLABCMNUCUBBBCOPQ $.

  $( Obsolete proof of ~ spimt as of 17-Feb-2018.  (Contributed by NM,
     15-Jan-2008.)  (Revised by Mario Carneiro, 17-Oct-2016.)
     (New usage is discouraged.)  (Proof modification is discouraged.) $)
  spimtOLD $p |- ( ( F/ x ps /\ A. x ( x = y -> ( ph -> ps ) ) ) ->
              ( A. x ph -> ps ) ) $=
    ( wnf weq wi wal wa nfnf1 nfa1 sp adantl nfr adantr embantd imim2d impancom
    nfan alimd ax9o syl6 ) BCEZCDFZABGZGZCHZIACHZUDBCHZGZCHZBUCUHUGUKUCUHIZUFUJ
    CUCUHCBCJACKSULUEUIUDULABUIUHAUCACLMUCBUIGUHBCNOPQTRBCDUAUB $.

  ${
    spim.1 $e |- F/ x ps $.
    spim.2 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( Specialization, using implicit substitution.  Compare Lemma 14 of
       [Tarski] p. 70.  The ~ spim series of theorems requires that only one
       direction of the substitution hypothesis hold.  (Contributed by NM,
       5-Aug-1993.)  (Revised by Mario Carneiro, 3-Oct-2016.)  (Proof shortened
       by Wolf Lammen, 18-Feb-2018.) $)
    spim $p |- ( A. x ph -> ps ) $=
      ( weq wi a9e eximii 19.36i ) ABCECDGABHCCDIFJK $.
    $( Obsolete proof of ~ spim as of 18-Feb-2018.  (Contributed by NM,
       5-Aug-1993.)  (Revised by Mario Carneiro, 3-Oct-2016.)
       (New usage is discouraged.)  (Proof modofication is discouraged.) $)
    spimOLD $p |- ( A. x ph -> ps ) $=
      ( wnf weq wi wal ax-gen spimt mp2an ) BCGCDHABIIZCJACJBIENCFKABCDLM $.
  $}

  ${
    spimeOLD.1 $e |- F/ x ph $.
    spimeOLD.2 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( Obsolete proof of ~ spime as of 17-Feb-2018.  (Contributed by NM,
       7-Aug-1994.)  (Revised by Mario Carneiro, 3-Oct-2016.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    spimeOLD $p |- ( ph -> E. x ps ) $=
      ( wn wal wex nfn weq con3d spim con2i df-ex sylibr ) ABGZCHZGBCIRAQAGCDAC
      EJCDKABFLMNBCOP $.
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

    $( Obsolete proof of ~ spimed as of 19-Feb-2018.  (Contributed by NM,
       5-Aug-1993.)  (Revised by Mario Carneiro, 3-Oct-2016.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    spimedOLD $p |- ( ch -> ( ph -> E. x ps ) ) $=
      ( wnf wex wi wa nfnf1 id nfan1 weq adantld spimeOLD ex syl ) CADHZABDIZJF
      TAUATAKBDETADADLTMNDEOABTGPQRS $.
  $}

  ${
    spime.1 $e |- F/ x ph $.
    spime.2 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( Existential introduction, using implicit substitution.  Compare Lemma 14
       of [Tarski] p. 70.  (Contributed by NM, 7-Aug-1994.)  (Revised by Mario
       Carneiro, 3-Oct-2016.)  (Proof shortened by Wolf Lammen, 6-Mar-2018.) $)
    spime $p |- ( ph -> E. x ps ) $=
      ( wex wi wtru wnf a1i spimed trud ) ABCGHABICDACJIEKFLM $.
  $}

  ${
    $d x ps $.
    spimv.1 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( A version of ~ spim with a distinct variable requirement instead of a
       bound variable hypothesis.  (Contributed by NM, 5-Aug-1993.) $)
    spimv $p |- ( A. x ph -> ps ) $=
      ( nfv spim ) ABCDBCFEG $.
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
    spv.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Specialization, using implicit substitution.  (Contributed by NM,
       30-Aug-1993.) $)
    spv $p |- ( A. x ph -> ps ) $=
      ( weq biimpd spimv ) ABCDCDFABEGH $.
  $}

  ${
    spei.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    spei.2 $e |- ps $.
    $( Inference from existential specialization, using implicit substitution.
       Revised to remove a distinct variable constraint.  (Contributed by NM,
       19-Aug-1993.)  (Proof shortened by Wolf Lammen, 12-May-2018.) $)
    spei $p |- E. x ph $=
      ( weq a9e mpbiri eximii ) CDGZACCDHKABFEIJ $.
  $}

  ${
    $d x ps $.
    speivOLD.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    speivOLD.2 $e |- ps $.
    $( Obsolete proof of ~ spei as of 23-Feb-2018.  (Contributed by NM,
       19-Aug-1993.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    speivOLD $p |- E. x ph $=
      ( wex weq biimprd spimev ax-mp ) BACGFBACDCDHABEIJK $.
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

  ${
    $d x ps $.
    chv.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    chv.2 $e |- ph $.
    $( Implicit substitution of ` y ` for ` x ` into a theorem.  (Contributed
       by NM, 20-Apr-1994.)  (Proof shortened by Wolf Lammen, 22-Apr-2018.) $)
    chvarv $p |- ps $=
      ( nfv chvar ) ABCDBCGEFH $.
    $( Obsolete proof of ~ chvarv as of 22-Apr-2018.  (Contributed by NM,
       20-Apr-1994.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    chvarvOLD $p |- ps $=
      ( spv mpg ) ABCABCDEGFH $.
  $}

  ${
    cbv3.1 $e |- F/ y ph $.
    cbv3.2 $e |- F/ x ps $.
    cbv3.3 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( Rule used to change bound variables, using implicit substitution, that
       does not use ~ ax-12o .  (Contributed by NM, 5-Aug-1993.)  (Proof
       shortened by Wolf Lammen, 12-May-2018.) $)
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

    $( Obsolete proof of ~ cbv1h as of 13-May-2018.  (Contributed by NM,
       5-Aug-1993.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    cbv1hOLD $p |- ( A. x A. y ph -> ( A. x ps -> A. y ch ) ) $=
      ( wal wi sps al2imi ax-7 syl6 weq com23 syl6d ax9o a7s syld ) AEIZDIZBDIZ
      UCEIZCEIZUBUCBEIZDIUDUABUFDABUFJEFKLBDEMNAUDUEJEDADIZUCCEUGUCDEOZCDIZJZDI
      CABUJDABUHCUIAUHBCHPGQLCDERNLST $.
  $}

  ${
    cbv1OLD.1 $e |- ( ph -> F/ y ps ) $.
    cbv1OLD.2 $e |- ( ph -> F/ x ch ) $.
    cbv1OLD.3 $e |- ( ph -> ( x = y -> ( ps -> ch ) ) ) $.
    $( Obsolete version of ~ cbv1 as of 13-May-2018.  (Contributed by NM,
       5-Aug-1993.)  (Revised by Mario Carneiro, 3-Oct-2016.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    cbv1OLD $p |- ( A. x A. y ph -> ( A. x ps -> A. y ch ) ) $=
      ( nfrd cbv1hOLD ) ABCDEABEFIACDGIHJ $.
  $}

  ${
    cbv3hOLD.1 $e |- ( ph -> A. y ph ) $.
    cbv3hOLD.2 $e |- ( ps -> A. x ps ) $.
    cbv3hOLD.3 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( Obsolete proof of ~ cbv3h as of 12-May-2018.  (Contributed by NM,
       5-Aug-1993.)  (Proof shortened by Andrew Salmon, 25-May-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    cbv3hOLD $p |- ( A. x ph -> A. y ps ) $=
      ( weq wal wi a1i cbv1h stdpc6 mpg ) DDHZDIACIBDIJCOABCDAADIJOEKBBCIJOFKCD
      HABJJOGKLDMN $.
  $}

  ${
    cbv3OLD.1 $e |- F/ y ph $.
    cbv3OLD.2 $e |- F/ x ps $.
    cbv3OLD.3 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( Obsolete proof of ~ cbv3 as of 22-Apr-2018.  (Contributed by NM,
       5-Aug-1993.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    cbv3OLD $p |- ( A. x ph -> A. y ps ) $=
      ( wtru wal wi wnf a1i weq cbv1OLD tru ax-gen mpg ) HDIACIBDIJCHABCDADKHEL
      BCKHFLCDMABJJHGLNHDOPQ $.
  $}

  ${
    cbv2h.1 $e |- ( ph -> ( ps -> A. y ps ) ) $.
    cbv2h.2 $e |- ( ph -> ( ch -> A. x ch ) ) $.
    cbv2h.3 $e |- ( ph -> ( x = y -> ( ps <-> ch ) ) ) $.
    $( Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 5-Aug-1993.) $)
    cbv2h $p |- ( A. x A. y ph -> ( A. x ps <-> A. y ch ) ) $=
      ( wal weq wb wi bi1 syl6 cbv1h equcomi bi2 syl56 a7s impbid ) AEIDIBDIZCE
      IZABCDEFGADEJZBCKZBCLHBCMNOAUBUALEDACBEDGFEDJUCAUDCBLEDPHBCQROST $.
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
    cbv2OLD.1 $e |- ( ph -> F/ y ps ) $.
    cbv2OLD.2 $e |- ( ph -> F/ x ch ) $.
    cbv2OLD.3 $e |- ( ph -> ( x = y -> ( ps <-> ch ) ) ) $.
    $( Obsolete version of ~ cbv2 as of 13-May-2018.  (Contributed by NM,
       5-Aug-1993.)  (Revised by Mario Carneiro, 3-Oct-2016.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    cbv2OLD $p |- ( A. x A. y ph -> ( A. x ps <-> A. y ch ) ) $=
      ( nfrd cbv2h ) ABCDEABEFIACDGIHJ $.
  $}

  ${
    cbval.1 $e |- F/ y ph $.
    cbval.2 $e |- F/ x ps $.
    cbval.3 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 5-Aug-1993.)  (Revised by Mario Carneiro,
       3-Oct-2016.) $)
    cbval $p |- ( A. x ph <-> A. y ps ) $=
      ( wal weq biimpd cbv3 wi biimprd equcoms impbii ) ACHBDHABCDEFCDIZABGJKBA
      DCFEBALCDPABGMNKO $.

    $( Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 5-Aug-1993.) $)
    cbvex $p |- ( E. x ph <-> E. y ps ) $=
      ( wn wal wex nfn weq notbid cbval notbii df-ex 3bitr4i ) AHZCIZHBHZDIZHAC
      JBDJSUARTCDADEKBCFKCDLABGMNOACPBDPQ $.
  $}

  ${
    $d y ph $.  $d x ps $.
    cbvalv.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 5-Aug-1993.) $)
    cbvalv $p |- ( A. x ph <-> A. y ps ) $=
      ( nfv cbval ) ABCDADFBCFEG $.

    $( Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 5-Aug-1993.) $)
    cbvexv $p |- ( E. x ph <-> E. y ps ) $=
      ( nfv cbvex ) ABCDADFBCFEG $.
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

    $( Obsolete proof of ~ cbvald as of 13-May-2018.  (Contributed by NM,
       2-Jan-2002.)  (Revised by Mario Carneiro, 6-Oct-2016.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    cbvaldOLD $p |- ( ph -> ( A. x ps <-> A. y ch ) ) $=
      ( wal wb nfri alrimiv nfvd cbv2OLD syl ) AAEIZDIBDICEIJAPDAEFKLABCDEGACDM
      HNO $.

    $( Deduction used to change bound variables, using implicit substitution,
       particularly useful in conjunction with ~ dvelim .  (Contributed by NM,
       2-Jan-2002.)  (Revised by Mario Carneiro, 6-Oct-2016.) $)
    cbvexd $p |- ( ph -> ( E. x ps <-> E. y ch ) ) $=
      ( wn wal wex nfnd weq wb notbi syl6ib cbvald notbid df-ex 3bitr4g ) ABIZD
      JZICIZEJZIBDKCEKAUBUDAUAUCDEFABEGLADEMBCNUAUCNHBCOPQRBDSCEST $.
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
    $( Obsolete proof of ~ cbval2 as of 22-Apr-2018.  (Contributed by NM,
       22-Dec-2003.)  (Revised by Mario Carneiro, 6-Oct-2016.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    cbval2OLD $p |- ( A. x A. y ph <-> A. z A. w ps ) $=
      ( wal nfal weq wb wa nfv nfan cbval 19.28v wi expcom pm5.32d pm5.32 mpbir
      3bitr3i ) ADLZBFLZCEAEDGMBCFIMCENZUGUHOUAUIUGPZUIUHPZOUIAPZDLUIBPZFLUJUKU
      LUMDFUIAFUIFQHRUIBDUIDQJRDFNZUIABUIUNABOKUBUCSUIADTUIBFTUFUIUGUHUDUES $.

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
    $v f $.
    $v g $.
    $( Define temporary individual variables. $)
    cbvex4v.vf $f set f $.
    cbvex4v.vg $f set g $.
    $d w z ch $.  $d u v ph $.  $d x y ps $.  $d f g ps $.  $d f w $.
    $d g z $.  $d u v w x y z $.
    cbvex4v.1 $e |- ( ( x = v /\ y = u ) -> ( ph <-> ps ) ) $.
    cbvex4v.2 $e |- ( ( z = f /\ w = g ) -> ( ps <-> ch ) ) $.
    $( Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 26-Jul-1995.) $)
    cbvex4v $p |- ( E. x E. y E. z E. w ph <-> E. v E. u E. f E. g ch ) $=
      ( wex weq wa 2exbidv cbvex2v 2exbii bitri ) AGNFNZENDNBGNFNZINHNCKNJNZINH
      NUAUBDEHIDHOEIOPABFGLQRUBUCHIBCFGJKMRST $.
  $}

  $( Lemma used in proofs of substitution properties.  (Contributed by NM,
     5-Aug-1993.)  (Proof shortened by Mario Carneiro, 20-May-2014.)  (Proof
     shortened by Wolf Lammen, 5-Feb-2018.) $)
  equs4 $p |- ( A. x ( x = y -> ph ) -> E. x ( x = y /\ ph ) ) $=
    ( weq wi wal wex wa a9e exintr mpi ) BCDZAEBFLBGLAHBGBCILABJK $.

  $( Obsolete proof of ~ equs4 as of 5-Feb-2018.  (Contributed by NM,
     5-Aug-1993.)  (Proof shortened by Mario Carneiro, 20-May-2014.)
     (New usage is discouraged.)  (Proof modification is discouraged.) $)
  equs4OLD $p |- ( A. x ( x = y -> ph ) -> E. x ( x = y /\ ph ) ) $=
    ( weq wi wal wa wex a9e 19.29 mpan2 ancl imp eximi syl ) BCDZAEZBFZQPGZBHZP
    AGZBHRPBHTBCIQPBJKSUABQPUAPALMNO $.

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
    $( Obsolete proof of ~ equsal as of 5-Feb-2018.  (Contributed by NM,
       5-Aug-1993.)  (Proof shortened by Andrew Salmon, 12-Aug-2011.)  (Revised
       by Mario Carneiro, 3-Oct-2016.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    equsalOLD $p |- ( A. x ( x = y -> ph ) <-> ps ) $=
      ( weq wal 19.3 syl6bbr pm5.74i albii nfri a1d alrimi ax9o impbii bitr4i
      wi ) CDGZASZCHTBCHZSZCHZBUAUCCTAUBTABUBFBCEIJKLBUDBUCCEBUBTBCEMNOBCDPQR
      $.
  $}

  ${
    equsalh.1 $e |- ( ps -> A. x ps ) $.
    equsalh.2 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( A useful equivalence related to substitution.  (Contributed by NM,
       5-Aug-1993.) $)
    equsalh $p |- ( A. x ( x = y -> ph ) <-> ps ) $=
      ( nfi equsal ) ABCDBCEGFH $.
  $}

  ${
    equsex.1 $e |- F/ x ps $.
    equsex.2 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( A useful equivalence related to substitution.  (Contributed by NM,
       5-Aug-1993.)  (Revised by Mario Carneiro, 3-Oct-2016.)  (Proof shortened
       by Wolf Lammen, 6-Feb-2018.) $)
    equsex $p |- ( E. x ( x = y /\ ph ) <-> ps ) $=
      ( weq wa wex biimpa exlimi wi wal equsal equs4 sylbir impbii ) CDGZAHZCIZ
      BSBCERABFJKBRALCMTABCDEFNACDOPQ $.
    $( Obsolete proof of ~ equsex as of 6-Feb-2018.  (Contributed by NM,
       5-Aug-1993.)  (Revised by Mario Carneiro, 3-Oct-2016.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    equsexOLD $p |- ( E. x ( x = y /\ ph ) <-> ps ) $=
      ( weq wn wi wex wal exnal df-an exbii nfn notbid equsal con2bii 3bitr4i
      wa ) CDGZAHZIZHZCJUCCKZHUAATZCJBUCCLUFUDCUAAMNUEBUBBHCDBCEOUAABFPQRS $.
  $}

  ${
    equsexh.1 $e |- ( ps -> A. x ps ) $.
    equsexh.2 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( A useful equivalence related to substitution.  (Contributed by NM,
       5-Aug-1993.) $)
    equsexh $p |- ( E. x ( x = y /\ ph ) <-> ps ) $=
      ( nfi equsex ) ABCDBCEGFH $.
  $}

  ${
    $d w y $.  $d w z $.
    $( Lemma for ~ nfeqf and ~ dveeq1 .  Used to eliminate distinct variable
       constraints.  The proof of ~ ax12o bases on ideas from NM, 24-Dec-2015.
       (Contributed by Wolf Lammen, 8-Feb-2018.) $)
    ax12olem1 $p |- ( y = z <-> A. w ( y = w -> z = w ) ) $=
      ( weq wi wal ax-8 alrimiv equcomi syl5 embantd spimvw impbii ) ABDZACDZBC
      DZEZCFNQCABCGHQNCACADZOPNCAIPCBDRNBCICABGJKLM $.
  $}

  ${
    $d w x z $.  $d w y $.
    $( Lemma for ~ nfeqf and ~ dveeq1 .  This lemma is equivalent to ~ ax12v
       with one distinct variable constraint removed.  (Contributed by Wolf
       Lammen, 29-Apr-2018.) $)
    ax12olem2 $p |- ( -. x = y -> ( E. x y = z -> y = z ) ) $=
      ( vw weq wn wex wi wal ax12v ax-8 eximi 19.36v sylib syl9 alrimdv syl6ibr
      ax12olem1 ) ABEFZBCEZAGZBDEZCDEZHZDITSUAUDDSUBUBAIZUAUCABDJUAUDAGUEUCHTUD
      ABCDKLUBUCAMNOPBCDRQ $.
  $}

  ${
    $d x z $.
    ax12olem3.1 $e |- ( -. x = y -> ( y = z -> A. x y = z ) ) $.
    $( Lemma for ~ nfeqf and ~ dveeq1 .  Convert ~ ax12olem2 into a more
       general form.  (Contributed by Wolf Lammen, 29-Apr-2018.) $)
    ax12olem3 $p |- ( -. A. x x = y -> F/ x y = z ) $=
      ( weq wal wn wex wnf exnal nfnf1 ax12olem2 syld nf2 sylibr exlimi sylbir
      wi ) ABEZAFGSGZAHBCEZAIZSAJTUBAUAAKTUAAHZUAAFZRUBTUCUAUDABCLDMUAANOPQ $.
  $}

  ${
    $d w y $.  $d w z $.  $d ph w $.  $d ps w $.
    ax12olem4.1 $e |- ( ph -> F/ x y = w ) $.
    ax12olem4.2 $e |- ( ps -> F/ x z = w ) $.
    $( Lemma for ~ nfeqf .  A technical step to remove a distinct variable
       constraint from ~ ax12v .  (Contributed by Wolf Lammen, 29-Apr-2018.) $)
    ax12olem4 $p |- ( ( ph /\ ps ) -> F/ x y = z ) $=
      ( weq wi wal wa ax12olem1 nfv wnf adantr adantl nfimd nfald nfxfrd ) DEID
      FIZEFIZJZFKABLZCDEFMUDUCCFUDFNUDUAUBCAUACOBGPBUBCOAHQRST $.
  $}

  ${
    $d x w $.  $d y w $.  $d z w $.
    $( A variable is effectively not free in an equality if it is not either of
       the involved variables. ` F/ ` version of ~ ax-12o .  (Contributed by
       Mario Carneiro, 6-Oct-2016.)  (Proof shortened by Wolf Lammen,
       29-Apr-2018.) $)
    nfeqf $p |- ( ( -. A. z z = x /\ -. A. z z = y ) -> F/ z x = y ) $=
      ( vw weq wal wn ax12v ax12olem3 ax12olem4 ) CAECFGCBECFGCABDCADCADHICBDCB
      DHIJ $.
  $}

  $( Derive set.mm's original ~ ax-12o from the shorter ~ ax-12 .  (Contributed
     by NM, 29-Nov-2015.)  (Revised by NM, 24-Dec-2015.)  (Proof shortened by
     Wolf Lammen, 29-Apr-2018.) $)
  ax12o $p |- ( -. A. z z = x -> ( -. A. z z = y
              -> ( x = y -> A. z x = y ) ) ) $=
    ( weq wal wn wi wa nfeqf nfrd ex ) CADCEFZCBDCEFZABDZNCEGLMHNCABCIJK $.

  ${
    $d w y $.  $d w z $.
    $( Obsolete proof of ~ ax12oOLD as of 30-Jan-2018.  Lemma for ~ ax12oOLD .
       Similar to ~ equvin but with a negated equality.  (Contributed by NM,
       24-Dec-2015.)  (Proof shortened by Wolf Lammen, 20-Jan-2018.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    ax12olem1OLD $p |- ( E. w ( y = w /\ -. z = w ) <-> -. y = z ) $=
      ( weq wn wa wex ax-8 equcomi syl6 con3and exlimiv ax-17 syl5 con3d jctild
      spimeh impbii ) ACDZBCDZEZFZCGABDZEZUBUDCSUCTSUCCBDZTACBHCBIJKLUDUBCAUDCM
      CADZUDUASUFTUCTUEUFUCBCICABHNOCAIPQR $.
  $}

  ${
    $d w x z $.  $d w y $.
    ax12olem2OLD.1 $e |- ( -. x = y -> ( y = w -> A. x y = w ) ) $.
    $( Obsolete proof of ~ ax12oOLD as of 30-Jan-2018.  Lemma for ~ ax12oOLD .
       Negate the equalities in ~ ax-12 , shown as the hypothesis.
       (Contributed by NM, 24-Dec-2015.)  (Proof shortened by Wolf Lammen,
       23-Jan-2018.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    ax12olem2OLD $p |- ( -. x = y -> ( -. y = z -> A. x -. y = z ) ) $=
      ( weq wn wa wex wal anim1d 19.27v syl6ibr eximdv 19.12 ax12olem1OLD albii
      syl6 3imtr3g ) ABFGZBDFZCDFGZHZDIZUDAJZBCFGZUFAJTUDUCAJZDIUETUCUGDTUCUAAJ
      ZUBHUGTUAUHUBEKUAUBALMNUCDAORBCDPZUDUFAUIQS $.
  $}

  $( Obsolete proof of ~ ax12oOLD as of 30-Jan-2018.  Lemma for ~ ax12oOLD .
     Show the equivalence of an intermediate equivalent to ~ ax12o with the
     conjunction of ~ ax-12 and a variant with negated equalities.
     (Contributed by NM, 24-Dec-2015.)  (New usage is discouraged.)
     (Proof modification is discouraged.) $)
  ax12olem3OLD $p |- ( ( -. x = y -> ( -. A. x -. y = z -> A. x y = z ) )
         <-> ( ( -. x = y -> ( y = z -> A. x y = z ) )
            /\ ( -. x = y -> ( -. y = z -> A. x -. y = z ) ) ) ) $=
    ( weq wn wal wi wa sp con2i imim1i imim2i con1d jca imim1d com12 imim3i imp
    con1 impbii ) ABDEZBCDZEZAFZEZUBAFZGZGZUAUBUFGZGZUAUCUDGZGZHUHUJULUGUIUAUBU
    EUFUDUBUCAIJKLUGUKUAUGUDUBUFUBUEUBAILMLNUJULUHUIUKUGUAUKUIUGUKUEUBUFUBUDSOP
    QRT $.

  ${
    $d w x z $.  $d w y z $.
    ax12olem4OLD.1 $e |- ( -. x = y -> ( y = z -> A. x y = z ) ) $.
    ax12olem4OLD.2 $e |- ( -. x = y -> ( y = w -> A. x y = w ) ) $.
    $( Obsolete proof of ~ ax12oOLD as of 30-Jan-2018.  Lemma for ~ ax12oOLD .
       Construct an intermediate equivalent to ~ ax-12 from two instances of
       ~ ax-12 .  (Contributed by NM, 24-Dec-2015.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    ax12olem4OLD $p |- ( -. x = y -> ( -. A. x -. y = z -> A. x y = z ) ) $=
      ( weq wn wal wi ax12olem2OLD ax12olem3OLD mpbir2an ) ABGHZBCGZHZAIZHOAIZJ
      JNORJJNPQJJEABCDFKABCLM $.
  $}

  ${
    ax12olem5OLD.1 $e |- ( -. x = y -> ( -. A. x -. y = z -> A. x y = z ) ) $.
    $( Obsolete proof of ~ ax12oOLD as of 30-Jan-2018.  Lemma for ~ ax12oOLD .
       See ~ ax12olem6OLD for derivation of ~ ax12oOLD from the conclusion.
       (Contributed by NM, 24-Dec-2015.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    ax12olem5OLD $p |- ( -. A. x x = y -> ( y = z -> A. x y = z ) ) $=
      ( weq wal wn wex wi exnal 19.8a hbe1 hba1 hbim syl5bi exlimih syl5 sylbir
      df-ex ) ABEZAFGTGZAHZBCEZUCAFZITAJUCUCAHZUBUDUCAKUAUEUDIAUEUDAUCALUCAMNUE
      UCGAFGUAUDUCASDOPQR $.
  $}

  ${
    $d w x $.  $d w y $.  $d w z $.
    ax12olem6OLD.1 $e |- ( -. A. x x = z -> ( z = w -> A. x z = w ) ) $.
    ax12olem6OLD.2 $e |- ( -. A. x x = y -> ( y = w -> A. x y = w ) ) $.
    $( Obsolete proof of ~ ax12oOLD as of 30-Jan-2018.  Lemma for ~ ax12oOLD .
       Derivation of ~ ax12oOLD from the hypotheses, without using
       ~ ax12oOLD .  (Contributed by Andrew Salmon, 21-Jul-2011.)  (Revised by
       NM, 24-Dec-2015.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    ax12olem6OLD $p |- ( -. A. x x = y
      -> ( -. A. x x = z -> ( y = z -> A. x y = z ) ) ) $=
      ( weq wn wi hbn1 hbim1 ax-17 equcom equequ1 syl5bb imbi2d dvelimhw 19.21h
      wal syl6ib pm2.86d ) ABGASHZACGZASHZBCGZUEASZUBUDUEIZUGASUDUFIUDCDGZIUGAB
      DUDUHAUCAJZEKUGDLDBGZUHUEUDUHDCGUJUECDMDBCNOPFQUDUEAUIRTUA $.
  $}

  ${
    $d w x $.  $d w y $.  $d w z $.
    ax12olem7OLD.1 $e |- ( -. x = z -> ( -. A. x -. z = w -> A. x z = w ) ) $.
    ax12olem7OLD.2 $e |- ( -. x = y -> ( -. A. x -. y = w -> A. x y = w ) ) $.
    $( Obsolete proof of ~ ax12oOLD as of 30-Jan-2018.  Lemma for ~ ax12oOLD .
       Derivation of ~ ax12oOLD from the hypotheses, without using
       ~ ax12oOLD .  (Contributed by NM, 24-Dec-2015.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    ax12olem7OLD $p |- ( -. A. x x = y
              -> ( -. A. x x = z -> ( y = z -> A. x y = z ) ) ) $=
      ( ax12olem5OLD ax12olem6OLD ) ABCDACDEGABDFGH $.
  $}

  ${
    $d x w v $.  $d y w v $.  $d z w v $.
    $( Obsolete proof of ~ ax12oOLD as of 30-Jan-2018.  (Contributed by NM,
       29-Nov-2015.)  (Revised by NM, 24-Dec-2015.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    ax12oOLD $p |- ( -. A. z z = x -> ( -. A. z z = y
              -> ( x = y -> A. z x = y ) ) ) $=
      ( vw vv ax12v ax12olem4OLD ax12olem7OLD ) CABDCBDECBDFCBEFGCADECADFCAEFGH
      $.
  $}

  $( Derive ~ ax-12 from ~ ax12v via ~ ax12o .  This shows that the weakening
     in ~ ax12v is still sufficient for a complete system.  (Contributed by NM,
     21-Dec-2015.)  (Proof shortened by Wolf Lammen, 31-Jan-2018.) $)
  ax12 $p |- ( -. x = y -> ( y = z -> A. x y = z ) ) $=
    ( weq wn wal wi sp con3i ax12o syl2im ax12b mpbir ) ABDZEZBCDZPAFGZGOACDZEZ
    QGGONAFZESRAFZEQTNNAHIUARRAHIBCAJKABCLM $.

  $( Obsolete proof of ~ ax12 as of 31-Jan-2018.  (Contributed by NM,
     21-Dec-2015.)  (New usage is discouraged.)
     (Proof modification is discouraged.) $)
  ax12OLD $p |- ( -. x = y -> ( y = z -> A. x y = z ) ) $=
    ( weq wn wal wi wa sp con3i adantr equtrr equcoms con3rr3 imp nsyl ax12o ex
    sylc pm2.43d ) ABDZEZBCDZUCAFZUBUCUCUDGZUBUCHZUAAFZEZACDZAFZEUEUBUHUCUGUAUA
    AIJKUFUIUJUBUCUIEUCUIUAUIUAGCBCBALMNOUIAIPBCAQSRT $.

  ${
    $d w x z $.  $d w y $.
    $( Quantifier introduction when one pair of variables is distinct.  Revised
       to be independent of ~ ax-7 .
       (Contributed by NM, 2-Jan-2002.)  (Revised by Wolf Lammen, 5-Sep-2018.)
       $)
    dveeq1 $p |- ( -. A. x x = y -> ( y = z -> A. x y = z ) ) $=
      ( vw weq wal wn wa wex wi equtrr equcoms anc2li spimev ax12v alimdv imp3a
      syl9 exlimdv syl5 ax12olem3 nfrd ) ABEZAFGBCEZAABCUDDCEZBDEZHZDIUCGZUDAFZ
      UDUGDCUEUDUFUDUFJCDCDBKLMNUHUGUIDUHUEUFUIUHUFUFAFUEUIABDOUEUFUDADCBKPRQST
      UAUB $.

    $( Quantifier introduction when one pair of variables is distinct.  Revised
       to be independent of ~ dvelimv .
       (Contributed by NM, 2-Jan-2002.)  (Revised by Wolf Lammen,
       29-Apr-2018.)  (New usage is discouraged.) $)
    dveeq1ALT $p |- ( -. A. x x = y -> ( y = z -> A. x y = z ) ) $=
      ( weq wal wn ax12 ax12olem3 nfrd ) ABDAEFBCDAABCABCGHI $.
  $}

  ${
    $d x z $.
    $( Quantifier introduction when one pair of variables is distinct. Revised
       to remove dependency on ~ ax-7 .  (Contributed by NM, 2-Jan-2002.)
       (Revised by NM, 20-Jul-2015.)  (Revised by Wolf Lammen, 5-Sep-2018.) $)
    dveeq2 $p |- ( -. A. x x = y -> ( z = y -> A. x z = y ) ) $=
      ( weq wal wn dveeq1 equcom albii 3imtr3g ) ABDAEFBCDZKAECBDZLAEABCGBCHZKL
      AMIJ $.
  $}

  ${
    $d x v w $.  $d y v w $.
    $( Lemma for ~ ax10 .  Change bound variable.  (Contributed by NM,
       22-Jul-2015.) $)
    ax10lem1 $p |- ( A. x x = w -> A. y y = w ) $=
      ( vv weq wal ax-8 cbvalivw syl ) ACEZAFDCEZDFBCEZBFJKADADCGHKLDBDBCGHI $.
  $}

  ${
    $d w z x $.  $d w z y $.
    $( Lemma for ~ ax10 .  Change bound variable.  (Contributed by NM,
       8-Jul-2016.)  (Proof shortened by Wolf Lammen, 17-Feb-2018.) $)
    ax10lem2 $p |- ( A. x x = w -> A. y y = x ) $=
      ( weq wal ax10lem1 equequ2 biimprd al2imi syl5com dveeq1 spsd com12 con1d
      wn pm2.61d ) ACDZAEZQBEZBADZBEZRBCDZBESUAABCFQUBTBQTUBACBGHIJRUASUAOZRSUC
      QSABACKLMNP $.
  $}

  $( Same as ~ ax10o but with reversed antecedent.  (Contributed by NM,
     25-Jul-2015.) $)
  ax10o2 $p |- ( A. y y = x -> ( A. x ph -> A. y ph ) ) $=
    ( weq wal wi ax-11 sps pm2.27 al2imi syld ) CBDZCEABEZLAFZCEZACELMOFCACBGHL
    NACLAIJK $.

  ${
    $d x z $.  $d y z $.
    $( Derive set.mm's original ~ ax-10 from others.  (Contributed by NM,
       25-Jul-2015.)  (Revised by NM, 7-Nov-2015.)  (Proof shortened by Wolf
       Lammen, 6-Mar-2018.) $)
    ax10 $p |- ( A. x x = y -> A. y y = x ) $=
      ( vz weq wal wex wn a9ev equcomi dveeq1 syl5com ax10o2 ax10lem2 syl6 syl9
      wi exlimiv ax-mp pm2.18d ) ABDAEZBADBEZCADZCFTUAGZUAPPZCAHUBUDCUBUCACDZBE
      ZTUAUBUEUCUFCAIBACJKTUFUEAEUAUEBALABCMNOQRS $.
  $}

  ${
    $d x y $.  $d x z $.
    $( Obsolete proof of a lemma for ~ ax10 as of 17-Feb-2018.  Change free
       variable.  (Contributed by NM, 25-Jul-2015.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    ax10lem2OLD $p |- ( A. x x = y -> A. x x = z ) $=
      ( weq wal wn hbe1 equequ2 biimprd con3rr3 19.8a syl6 ax-17 equequ1 notbid
      wex spimeh pm2.61d1 exlimih exnal 3imtr3i con4i ) ACDZAEZABDZAEZUCFZAPUEF
      ZAPZUDFUFFUGUIAUHAGUGCBDZUIUGUJUHUIUJUEUCUJUCUECBAHIJUHAKLUJFZUHACUKAMUCU
      HUKUCUEUJACBNOIQRSUCATUEATUAUB $.
  $}

  ${
    $d w x y $.  $d w x z $.
    $( Obsolete proof of a lemma for ~ ax10 as of 17-Feb-2018.  Similar to
       ~ ax-10 but with distinct variables.  (Contributed by NM, 25-Jul-2015.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    ax10lem3OLD $p |- ( A. x x = y -> A. y y = x ) $=
      ( vz vw weq wal ax10lem2OLD ax10lem1 syl ) ABEAFACEAFZBAEBFZABCGJDAEDFZKJ
      DCEDFLADCHDCAGIDBAHII $.
  $}

  ${
    $d x z $.  $d y z $.  $d z ps $.  $d x ph $.
    dvelimvOLD.1 $e |- ( z = y -> ( ph <-> ps ) ) $.
    $( Obsolete proof of ~ dvelimv as of 17-Feb-2018.  (Contributed by NM,
       25-Jul-2015.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    dvelimvOLD $p |- ( -. A. x x = y -> ( ps -> A. x ps ) ) $=
      ( weq wal wn wi ax-17 alrimih a2i alimi syl ax10lem3OLD con3i hbn1 hban
      sp wa a1d syl5ibr ax12o imp a17d hbimd hbald biimpd ax9v con3 al2imi mtoi
      nsyl2 syl56 expcom ax-11 syl2im pm2.27 syld pm2.61d2 ) CDGZCHIZCEGZCHZBBC
      HZJZVEIZVCVGBEDGZAJZEHZVHVCUAZVKCHVFBVIBEHZJZEHVKBVNEBEKZBVMVIVOUBLVNVJEV
      IVMAVMAVIBBETFUCMNOVLVJCEVHVCEVHECGZEHZIZVHEHVQVEECPQVRVHEVPERVEVQCEPQLOV
      CEKSVLVIACVHVCCVDCRVBCRSVHVCVIVICHJEDCUDUEVLACUFUGUHVKBCVKBIZEHZBVKVIBJZE
      HZVTIVJWAEVIABVIABFUIMNWBVTVIIZEHEDUJWAVSWCEVIBUKULUMOVSEKUNNUOUPVEBVDBJZ
      CHZVFVEVDBVMWEVDCTVOBCEUQURVDWDBCVDBUSULUTVA $.
  $}

  ${
    $d w x z $.  $d w y $.
    $( Obsolete proof of ~ dveeq2 as of 25-Feb-2018.  (Contributed by NM,
       2-Jan-2002.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    dveeq2OLD $p |- ( -. A. x x = y -> ( z = y -> A. x z = y ) ) $=
      ( vw weq equequ2 dvelimvOLD ) CDECBEABDDBCFG $.
  $}

  ${
    $d w z x $.  $d w z y $.
    $( Obsolete proof of ~ ax10lem2 as of 17-Feb-2018.  (Contributed by NM,
       8-Jul-2016.)  (New usage is discouraged.)  (Proof modification is
       discouraged. ) $)
    ax10lem4OLD $p |- ( A. x x = w -> A. y y = x ) $=
      ( vz weq wal wn wi ax10lem1 equequ1 dvelimvOLD hba1 wb equequ2 sps albidh
      biimprd syl6 syl7 spsd pm2.43d com12 pm2.18d ) ACEZAFZBAEZBFZUGGZUEUGUHUE
      UGUHUDUEUGHAUEBCEZBFZUHUDUGABCIUHUDUDBFZUJUGHDCEUDBADDACJKUKUGUJUKUFUIBUD
      BLUDUFUIMBACBNOPQRSTUAUBUC $.
  $}

  ${
    $d w z $.  $d u v w $.  $d v x $.  $d v y $.
    $( Obsolete proof of ~ ax10o2 as of 17-Feb-2018.  (Contributed by NM,
       22-Jul-2015.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    ax10lem5OLD $p |- ( A. z z = w -> A. y y = x ) $=
      ( vv vu weq wal ax10lem1 ax10lem4OLD syl ) CDGCHZAEGAHZBAGBHLFEGFHZMLEDGE
      HNCEDIEFDJKFAEIKABEJK $.
  $}

  ${
    $d x z $.  $d y z $.
    $( Obsolete proof of ~ ax10 as of 17-Feb-2018.  (Contributed by NM,
       25-Jul-2015.)  (Revised by NM, 7-Nov-2015.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    ax10OLD $p |- ( A. x x = y -> A. y y = x ) $=
      ( vz weq wal wn ax9v wex df-ex wi dveeq2OLD imp ax10o2 equcomi alimi syl6
      wa ax10lem5OLD syl56 exp3acom23 pm2.18 exlimdv syl5bir mpi ) ABDAEZCADZFC
      EFZBADBEZCAGUGUFCHUEUHUFCIUEUFUHCUEUFUHFZUHJUHUEUIUFUHUIUFQUFBEZUEACDZAEZ
      UHUIUFUJBACKLUEUJUFAEULUFBAMUFUKACANOPABACRSTUHUAPUBUCUD $.
  $}

  ${
    $d x v z $.  $d y v z $.
    $( Obsolete proof of ~ ax9 as of 4-Feb-2018.  (Contributed by NM,
       12-Nov-2013.)  (Revised by NM, 25-Jul-2015.)
       (New usage is discouraged.)  (Proof modfication is discouraged.) $)
    ax9OLD $p |- -. A. x -. x = y $=
      ( vv weq wal wn sp nsyl3 wi ax9v dveeq2OLD hba1 equequ2 sps notbid albidh
      wb mtbii syl6com con3i alrimiv mt3 pm2.61i ) ABDZAEZUDFZAEZFZUGUDUEUFAGUD
      AGHUEFZUHIZCBDZFZCECBJUJFULCUKUJUIUKUKAEZUHABCKUMACDZFZAEUGACJUMUOUFAUKAL
      UMUNUDUKUNUDQACBAMNOPRSTUAUBUC $.
  $}

  $( Obsolete proof of ~ a9e as of 4-Feb-2018.  (Contributed by NM,
     5-Aug-1993.)  (New usage is discouraged.)  (Proof modfication is
     discouraged.) $)
  a9eOLD $p |- E. x x = y $=
    ( weq wex wn wal ax9 df-ex mpbir ) ABCZADJEAFEABGJAHI $.

  $( Commutation law for identical variable specifiers.  The antecedent and
     consequent are true when ` x ` and ` y ` are substituted with the same
     variable.  Lemma L12 in [Megill] p. 445 (p. 12 of the preprint).
     (Contributed by NM, 5-Aug-1993.) $)
  aecom $p |- ( A. x x = y -> A. y y = x ) $=
    ( ax10 ) ABC $.

  ${
    aecoms.1 $e |- ( A. x x = y -> ph ) $.
    $( A commutation rule for identical variable specifiers.  (Contributed by
       NM, 5-Aug-1993.) $)
    aecoms $p |- ( A. y y = x -> ph ) $=
      ( weq wal ax10 syl ) CBECFBCEBFACBGDH $.
  $}

  ${
    naecoms.1 $e |- ( -. A. x x = y -> ph ) $.
    $( A commutation rule for distinct variable specifiers.  (Contributed by
       NM, 2-Jan-2002.) $)
    naecoms $p |- ( -. A. y y = x -> ph ) $=
      ( weq wal ax10 nsyl4 con1i ) ACBECFZBCEBFJABCGDHI $.
  $}

  $( Show that ~ ax-10o can be derived from ~ ax-10 in the form of ~ ax10 .
     Normally, ~ ax10o should be used rather than ~ ax-10o , except by theorems
     specifically studying the latter's properties.  (Contributed by NM,
     16-May-2008.)  (Proof shortened by Wolf Lammen, 21-Apr-2018.) $)
  ax10o $p |- ( A. x x = y -> ( A. x ph -> A. y ph ) ) $=
    ( wal wi ax10o2 aecoms ) ABDACDECBABCFG $.

  $( Obsolete proof of ~ ax10o as of 21-Apr-2018.  (Contributed by NM,
     16-May-2008.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  ax10oOLD $p |- ( A. x x = y -> ( A. x ph -> A. y ph ) ) $=
    ( weq wal wi ax10 ax-11 equcoms sps pm2.27 al2imi sylsyld ) BCDZBECBDZCEABE
    ZOAFZCEZACEBCGNPRFZBSCBACBHIJOQACOAKLM $.

  $( All variables are effectively bound in an identical variable specifier.
     (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen,
     21-Apr-2018.) $)
  hbae $p |- ( A. x x = y -> A. z A. x x = y ) $=
    ( weq wal wi wn ax12o syl7 ax10o2 ax10o pm2.43i syl5 pm2.61ii a5i ax-7 syl
    sp ) ABDZAEZSCEZAETCESUAACADCEZCBDCEZTUAFTSUBGUCGUASARABCHISACJTSBEZUCUATUD
    SABKLSBCJMNOSACPQ $.

  $( Obsolete proof of ~ hbae as of 21-Apr-2018.  (Contributed by NM,
     5-Aug-1993.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  hbaeOLD $p |- ( A. x x = y -> A. z A. x x = y ) $=
    ( weq wal wi wn ax12o syl7 ax10o aecoms pm2.43i syl5 pm2.61ii a5i ax-7 syl
    sp ) ABDZAEZSCEZAETCESUAACADCEZCBDCEZTUAFZTSUBGUCGUASARABCHIUDACSACJKUDBCTS
    BEZBCDBEUATUESABJLSBCJMKNOSACPQ $.

  $( All variables are effectively bound in an identical variable specifier.
     (Contributed by Mario Carneiro, 11-Aug-2016.) $)
  nfae $p |- F/ z A. x x = y $=
    ( weq wal hbae nfi ) ABDAECABCFG $.

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
    $d w z $.  $d u v w $.  $d v x $.  $d v y $.
    $( Lemma for ~ aev and ~ a16g .  Change free and bound variables.
       (Contributed by NM, 22-Jul-2015.)  (Proof shortened by Wolf Lammen,
       17-Feb-2018.) $)
    aevlem1 $p |- ( A. z z = w -> A. y y = x ) $=
      ( vv vu weq wal ax10lem1 ax10lem2 4syl ) CDGCHEDGEHFEGFHAEGAHBAGBHCEDIEFD
      JFAEIABEJK $.
  $}

  ${
    $d u v $.  $d u x y $.  $d u w $.
    $( A "distinctor elimination" lemma with no restrictions on variables in
       the consequent.  (Contributed by NM, 8-Nov-2006.) $)
    aev $p |- ( A. x x = y -> A. z w = v ) $=
      ( vu weq wal hbae aevlem1 ax-8 spimv syl alrimih ) ABGAHZDEGZCABCIOFEGZFH
      PEFABJQPFDFDEKLMN $.
  $}

  ${
    $d x y $.  $d w ph $.
    $( Generalization of ~ ax16 .  (Contributed by NM, 25-Jul-2015.)  (Proof
       shortened by Wolf Lammen, 18-Feb-2018.) $)
    a16g $p |- ( A. x x = y -> ( ph -> A. z ph ) ) $=
      ( vw weq wal aevlem1 ax-17 ax10o syl2im ) BCFBGEDFEGAAEGADGDEBCHAEIAEDJK
      $.
  $}

  ${
    $d x y $.  $d w ph $.  $d w z $.
    $( Obsolete proof of ~ a16g as of 18-Feb-2018.  (Contributed by NM,
       25-Jul-2015.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    a16gOLD $p |- ( A. x x = y -> ( ph -> A. z ph ) ) $=
      ( vw weq wex wi a9ev aevlem1 wn hbn1 pm2.21 alrimih ax-17 ax-1 ja equcomi
      wal ax-11 syl2im ax-5 syl6 com23 syl5 exlimih mpsyl ) EDFZEGBCFBSUHESZAAD
      SZHZEDIDEBCJUHUIUKHZEUIUKULESUIKULEUHELUIUKMNUKULEUKEOUKUIPNQUIDEFZDSZUHU
      KEDEDJUHAUNUJUHAUMAHDSZUNUJHUHUMAAESUOEDRAEOADETUAUMADUBUCUDUEUFUG $.
  $}

  ${
    $d x y z $.  $d z ph $.
    $( Proof of older axiom ~ ax-16 .  (Contributed by NM, 8-Nov-2006.)
       (Revised by NM, 22-Sep-2017.) $)
    ax16 $p |- ( A. x x = y -> ( ph -> A. x ph ) ) $=
      ( a16g ) ABCBD $.
  $}

  ${
    $d x y z $.  $d z ph $.
    ax16i.1 $e |- ( x = z -> ( ph <-> ps ) ) $.
    ax16i.2 $e |- ( ps -> A. x ps ) $.
    $( Inference with ~ ax16 as its conclusion.  (Contributed by NM,
       20-May-2008.)  (Proof modification is discouraged.) $)
    ax16i $p |- ( A. x x = y -> ( ph -> A. x ph ) ) $=
      ( weq wal wi nfv ax-8 cbv3 spimv equcomi syl syl5com alimdv mpcom alimi
      biimpcd nfi biimprd syl6com 3syl ) CDHZCIEDHZEIZCEHZEIZAACIZJUFUGCEUFEKUG
      CKCEDLMUHECHZEIZUJUFUHUMUGUFECECDLNUFUGULEUFDCHZUGULCDOUGDEHUNULJEDODECLP
      QRSULUIEECOZTPAUJBEIUKAUIBEUIABFUARBAECBCGUBAEKULUIBAJUOUIABFUCPMUDUE $.
  $}

  ${
    $d x y $.
    $( A generalization of axiom ~ ax-16 .  (Contributed by NM, 5-Aug-1993.) $)
    a16gb $p |- ( A. x x = y -> ( ph <-> A. z ph ) ) $=
      ( weq wal a16g sp impbid1 ) BCEBFAADFABCDGADHI $.

    $( If ~ dtru is false, then there is only one element in the universe, so
       everything satisfies ` F/ ` .  (Contributed by Mario Carneiro,
       7-Oct-2016.) $)
    a16nf $p |- ( A. x x = y -> F/ z ph ) $=
      ( weq wal nfae a16g nfd ) BCEBFADBCDGABCDHI $.
  $}

  $( Obsolete proof of ~ nfeqf as of 29-Apr-2018.  (Contributed by Mario
     Carneiro, 6-Oct-2016.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  nfeqfOLD $p |- ( ( -. A. z z = x /\ -. A. z z = y ) -> F/ z x = y ) $=
    ( weq wal wn wa nfnae nfan wi ax12o imp nfd ) CADCEFZCBDCEFZGABDZCNOCCACHCB
    CHINOPPCEJABCKLM $.

  ${
    dral1.1 $e |- ( A. x x = y -> ( ph <-> ps ) ) $.
    $( Formula-building lemma for use with the Distinctor Reduction Theorem.
       Part of Theorem 9.4 of [Megill] p. 448 (p. 16 of preprint).
       (Contributed by NM, 27-Feb-2005.)  (Revised by Wolf Lammen,
       4-Mar-2018.) $)
    dral2 $p |- ( A. x x = y -> ( A. z ph <-> A. z ps ) ) $=
      ( weq wal nfae albid ) CDGCHABECDEIFJ $.

    $( Obsolete proof of ~ dral2 as of 4-Mar-2018.  (Contributed by NM,
       27-Feb-2005.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    dral2OLD $p |- ( A. x x = y -> ( A. z ph <-> A. z ps ) ) $=
      ( weq wal hbae albidh ) CDGCHABECDEIFJ $.

    $( Formula-building lemma for use with the Distinctor Reduction Theorem.
       Part of Theorem 9.4 of [Megill] p. 448 (p. 16 of preprint).
       (Contributed by NM, 24-Nov-1994.)  (Proof shortened by Wolf Lammen,
       22-Apr-2018.) $)
    dral1 $p |- ( A. x x = y -> ( A. x ph <-> A. y ps ) ) $=
      ( weq wal dral2 ax10o ax10o2 impbid bitrd ) CDFCGZACGBCGZBDGZABCDCEHMNOBC
      DIBDCJKL $.

    $( Obsolete proof of ~ dral1 as of 4-Mar-2018.  (Contributed by NM,
       24-Nov-1994.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    dral1OLD $p |- ( A. x x = y -> ( A. x ph <-> A. y ps ) ) $=
      ( weq wal hbae biimpd alimdh ax10o syld biimprd wi aecoms impbid ) CDFCGZ
      ACGZBDGZQRBCGSQABCCDCHQABEIJBCDKLQSADGZRQBADCDDHQABEMJTRNDCADCKOLP $.

    $( Formula-building lemma for use with the Distinctor Reduction Theorem.
       Part of Theorem 9.4 of [Megill] p. 448 (p. 16 of preprint).
       (Contributed by NM, 27-Feb-2005.) $)
    drex1 $p |- ( A. x x = y -> ( E. x ph <-> E. y ps ) ) $=
      ( weq wal wn wex notbid dral1 df-ex 3bitr4g ) CDFCGZAHZCGZHBHZDGZHACIBDIN
      PROQCDNABEJKJACLBDLM $.

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
       (Contributed by Mario Carneiro, 4-Oct-2016.)  (Proof shortened by Wolf
       Lammen, 5-May-2018.) $)
    drnf2 $p |- ( A. x x = y -> ( F/ z ph <-> F/ z ps ) ) $=
      ( weq wal nfae nfbidf ) CDGCHABECDEIFJ $.

    $( Obsolete proof of ~ drnf2 as of 5-May-2018.  (Contributed by Mario
       Carneiro, 4-Oct-2016.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    drnf2OLD $p |- ( A. x x = y -> ( F/ z ph <-> F/ z ps ) ) $=
      ( weq wal wi wnf dral2 imbi12d df-nf 3bitr4g ) CDGCHZAAEHZIZEHBBEHZIZEHAE
      JBEJQSCDEOABPRFABCDEFKLKAEMBEMN $.
  $}

  ${
    nfald2.1 $e |- F/ y ph $.
    nfald2.2 $e |- ( ( ph /\ -. A. x x = y ) -> F/ x ps ) $.
    $( Variation on ~ nfald which adds the hypothesis that ` x ` and ` y ` are
       distinct in the inner subproof.  (Contributed by Mario Carneiro,
       8-Oct-2016.) $)
    nfald2 $p |- ( ph -> F/ x A. y ps ) $=
      ( weq wal wnf wn wa nfnae nfan nfald ex nfa1 biidd drnf1 mpbiri pm2.61d2
      ) ACDGCHZBDHZCIZAUAJZUCAUDKBCDAUDDECDDLMFNOUAUCUBDIBDPUBUBCDUAUBQRST $.

    $( Variation on ~ nfexd which adds the hypothesis that ` x ` and ` y ` are
       distinct in the inner subproof.  (Contributed by Mario Carneiro,
       8-Oct-2016.) $)
    nfexd2 $p |- ( ph -> F/ x E. y ps ) $=
      ( wex wn wal df-ex weq wa nfnd nfald2 nfxfrd ) BDGBHZDIZHACBDJAQCAPCDEACD
      KCIHLBCFMNMO $.
  $}

  ${
    exdistrf.1 $e |- ( -. A. x x = y -> F/ y ph ) $.
    $( Distribution of existential quantifiers, with a bound-variable
       hypothesis saying that ` y ` is not free in ` ph ` , but ` x ` can be
       free in ` ph ` (and there is no distinct variable condition on ` x ` and
       ` y ` ).  (Contributed by Mario Carneiro, 20-Mar-2013.)  (Proof
       shortened by Wolf Lammen, 14-May-2018.) $)
    exdistrf $p |- ( E. x E. y ( ph /\ ps ) -> E. x ( ph /\ E. y ps ) ) $=
      ( wa wex weq wal wi 19.8a anim2i eximi biidd drex1 syl5ibr wn 19.40 19.9d
      nfe1 anim1d syl56 pm2.61i exlimi ) ABFZDGZABDGZFZCGZCUHCTCDHCIZUFUIJUFUIU
      JUHDGUEUHDBUGABDKLMUHUHCDUJUHNOPUFADGZUGFUJQZUHUIABDRULUKAUGAULDESUAUHCKU
      BUCUD $.
    $( Obsolete proof of ~ exdistrf as of 14-May-2018.  (Contributed by Mario
       Carneiro, 20-Mar-2013.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    exdistrfOLD $p |- ( E. x E. y ( ph /\ ps ) -> E. x ( ph /\ E. y ps ) ) $=
      ( weq wal wa wex wi biidd drex1 drex2 nfe1 19.9 19.8a eximi sylbi syl6bir
      anim2i wn nfnae 19.40 19.9d anim1d syl5 eximd pm2.61i ) CDFCGZABHZDIZCIZA
      BDIZHZCIZJUIULUJCIZCIZUOUPUKCDCUJUJCDUIUJKLMUQUPUOUPCUJCNOUJUNCBUMABDPTQR
      SUIUAZUKUNCCDCUBUKADIZUMHURUNABDUCURUSAUMAURDEUDUEUFUGUH $.
  $}

  ${
    dvelimf.1 $e |- F/ x ph $.
    dvelimf.2 $e |- F/ z ps $.
    dvelimf.3 $e |- ( z = y -> ( ph <-> ps ) ) $.
    $( Version of ~ dvelimv without any variable restrictions.  (Contributed by
       NM, 1-Oct-2002.)  (Revised by Mario Carneiro, 6-Oct-2016.)  (Proof
       shortened by Wolf Lammen, 11-May-2018.) $)
    dvelimf $p |- ( -. A. x x = y -> F/ x ps ) $=
      ( weq wi wal wn equsal bicomi nfnae wa wnf nfeqf ancoms a1i nfald2 nfxfrd
      nfimd ) BEDIZAJZEKZCDICKLZCUFBABEDGHMNUGUECECDEOUGCEICKLZPZUDACUHUGUDCQED
      CRSACQUIFTUCUAUB $.

    $( Obsolete proof of ~ dvelimf as of 21-Apr-2018.  (Contributed by NM,
       1-Oct-2002.)  (Revised by Mario Carneiro, 6-Oct-2016.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    dvelimfOLD $p |- ( -. A. x x = y -> F/ x ps ) $=
      ( weq wi wal wn equsal bicomi nfnae wa nfan ax12o impcom nfd nfimd nfald2
      wnf a1i nfxfrd ) BEDIZAJZEKZCDICKLZCUHBABEDGHMNUIUGCECDEOUICEICKLZPZUFACU
      KUFCUIUJCCDCOCECOQUJUIUFUFCKJEDCRSTACUCUKFUDUAUBUE $.
  $}

  ${
    dvelimdf.1 $e |- F/ x ph $.
    dvelimdf.2 $e |- F/ z ph $.
    dvelimdf.3 $e |- ( ph -> F/ x ps ) $.
    dvelimdf.4 $e |- ( ph -> F/ z ch ) $.
    dvelimdf.5 $e |- ( ph -> ( z = y -> ( ps <-> ch ) ) ) $.
    $( Deduction form of ~ dvelimf .  This version may be useful if we want to
       avoid ~ ax-17 and use ~ ax-16 instead.  (Contributed by NM,
       7-Apr-2004.)  (Revised by Mario Carneiro, 6-Oct-2016.)  (Proof shortened
       by Wolf Lammen, 11-May-2018.) $)
    dvelimdf $p |- ( ph -> ( -. A. x x = y -> F/ x ch ) ) $=
      ( weq wal wn wi wnf nfim1 wb com12 pm5.74d dvelimf pm5.5 nfbidf syl5ib )
      DELDMNACOZDPACDPABOUEDEFABDGIQACFHJQFELZABCAUFBCRKSTUAAUECDGACUBUCUD $.
  $}

  ${
    dvelimh.1 $e |- ( ph -> A. x ph ) $.
    dvelimh.2 $e |- ( ps -> A. z ps ) $.
    dvelimh.3 $e |- ( z = y -> ( ph <-> ps ) ) $.
    $( Version of ~ dvelim without any variable restrictions.  (Contributed by
       NM, 1-Oct-2002.)  (Proof shortened by Wolf Lammen, 11-May-2018.) $)
    dvelimh $p |- ( -. A. x x = y -> ( ps -> A. x ps ) ) $=
      ( weq wal wn nfi dvelimf nfrd ) CDICJKBCABCDEACFLBEGLHMN $.


    $( Obsolete proof of ~ dvelimh as of 4-Mar-2018.  (Contributed by NM,
       1-Oct-2002.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    dvelimhOLD $p |- ( -. A. x x = y -> ( ps -> A. x ps ) ) $=
      ( weq wal wn wi hba1 ax10o aecoms syl5 a1d wa hbnae hban ax12o imp a1i ex
      hbimd hbald pm2.61i equsalh albii 3imtr3g ) CDICJKZEDIZALZEJZUNCJZBBCJCEI
      CJZUKUNUOLZLUPUQUKUNUNEJZUPUOUMEMURUOLECUNECNOPQUPKZUKUQUSUKRZUMCEUSUKECE
      ESCDESTUTULACUSUKCCECSCDCSTUSUKULULCJLEDCUAUBAACJLUTFUCUEUFUDUGABEDGHUHZU
      NBCVAUIUJ $.
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

       Other variants of this theorem are ~ dvelimh (with no distinct variable
       restrictions), ~ dvelimhw (that avoids ~ ax-12 ), and ~ dvelimALT (that
       avoids ~ ax-10 ).  (Contributed by NM, 23-Nov-1994.) $)
    dvelim $p |- ( -. A. x x = y -> ( ps -> A. x ps ) ) $=
      ( ax-17 dvelimh ) ABCDEFBEHGI $.
  $}

  ${
    $d x ph $.  $d z ps $.
    dvelimv.1 $e |- ( z = y -> ( ph <-> ps ) ) $.
    $( Similar to ~ dvelim with first hypothesis replaced by distinct variable
       condition.  (Contributed by NM, 25-Jul-2015.)  (Proof shortened by Wolf
       Lammen, 30-Apr-2018.) $)
    dvelimv $p |- ( -. A. x x = y -> ( ps -> A. x ps ) ) $=
      ( ax-17 dvelim ) ABCDEACGFH $.
  $}

  ${
    $d z ps $.
    dvelimnf.1 $e |- F/ x ph $.
    dvelimnf.2 $e |- ( z = y -> ( ph <-> ps ) ) $.
    $( Version of ~ dvelim using "not free" notation.  (Contributed by Mario
       Carneiro, 9-Oct-2016.) $)
    dvelimnf $p |- ( -. A. x x = y -> F/ x ps ) $=
      ( nfv dvelimf ) ABCDEFBEHGI $.
  $}

  ${
    $d w x z $.  $d w y $.
    $( Obsolete proof of ~ dveeq1 as of 25-Feb-2018.  (Contributed by NM,
       2-Jan-2002.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    dveeq1OLD $p |- ( -. A. x x = y -> ( y = z -> A. x y = z ) ) $=
      ( vw weq equequ1 dvelimv ) DCEBCEABDDBCFG $.

    $( Quantifier introduction when one pair of variables is distinct.
       (Contributed by NM, 2-Jan-2002.)  (Revised by NM, 20-Jul-2015.)
       (New usage is discouraged.) $)
    dveeq2ALT $p |- ( -. A. x x = y -> ( z = y -> A. x z = y ) ) $=
      ( vw weq equequ2 dvelimv ) CDECBEABDDBCFG $.
  $}

  ${
    $d x z $.  $d y z $.  $d z ph $.
    ax11v2.1 $e |- ( x = z -> ( ph -> A. x ( x = z -> ph ) ) ) $.
    $( Recovery of ~ ax-11o from ~ ax11v .  This proof uses ~ ax-10 and
       ~ ax-11 .  TODO: figure out if this is useful, or if it should be
       simplified or eliminated.  (Contributed by NM, 2-Feb-2007.)  (Proof
       shortened by Wolf Lammen, 21-Apr-2018.) $)
    ax11v2 $p |- ( -. A. x x = y ->
                 ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) ) $=
      ( weq wal wn wex wi a9ev dveeq2 wb equequ2 sps nfa1 imbi1d imbi2d imbi12d
      albid mpbii syl6 exlimdv mpi ) BCFZBGHZDCFZDIUEAUEAJZBGZJZJZDCKUFUGUKDUFU
      GUGBGZUKBCDLULBDFZAUMAJZBGZJZJUKEULUMUEUPUJUGUMUEMBDCBNOZULUOUIAULUNUHBUG
      BPULUMUEAUQQTRSUAUBUCUD $.

    $( Obsolete proof of ~ ax11v2 as of 21-Apr-2018.  (Contributed by NM,
       2-Feb-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    ax11v2OLD $p |- ( -. A. x x = y ->
                 ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) ) $=
      ( weq wal wn wex wi a9ev wa wb equequ2 adantl dveeq2 imp nfa1 imbi1d sps
      albid syl imbi2d imbi12d mpbii ex exlimdv mpi ) BCFZBGHZDCFZDIUIAUIAJZBGZ
      JZJZDCKUJUKUODUJUKUOUJUKLZBDFZAUQAJZBGZJZJUOEUPUQUIUTUNUKUQUIMUJDCBNZOUPU
      SUMAUPUKBGZUSUMMUJUKVBBCDPQVBURULBUKBRUKURULMBUKUQUIAVASTUAUBUCUDUEUFUGUH
      $.
  $}

  ${
    $d x z $.  $d y z $.  $d z ph $.
    ax11a2.1 $e |- ( x = z -> ( A. z ph -> A. x ( x = z -> ph ) ) ) $.
    $( Derive ~ ax-11o from a hypothesis in the form of ~ ax-11 . ~ ax-10 and
       ~ ax-11 are used by the proof, but not ~ ax-10o or ~ ax-11o .  TODO:
       figure out if this is useful, or if it should be simplified or
       eliminated.  (Contributed by NM, 2-Feb-2007.) $)
    ax11a2 $p |- ( -. A. x x = y ->
                 ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) ) $=
      ( wal weq wi ax-17 syl5 ax11v2 ) ABCDAADFBDGZLAHBFADIEJK $.
  $}

  ${
    $d x z $.  $d y z $.  $d z ph $.
    $( Derivation of set.mm's original ~ ax-11o from ~ ax-10 and the shorter
       ~ ax-11 that has replaced it.

       Theorem ~ ax11 shows the reverse derivation of ~ ax-11 from ~ ax-11o .

       Normally, ~ ax11o should be used rather than ~ ax-11o , except by
       theorems specifically studying the latter's properties.  (Contributed by
       NM, 3-Feb-2007.) $)
    ax11o $p |- ( -. A. x x = y ->
               ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) ) $=
      ( vz ax-11 ax11a2 ) ABCDABDEF $.
  $}

  $( A bidirectional version of ~ ax11o .  (Contributed by NM, 30-Jun-2006.) $)
  ax11b $p |- ( ( -. A. x x = y /\ x = y ) ->
              ( ph <-> A. x ( x = y -> ph ) ) ) $=
    ( weq wal wn wa wi ax11o imp sp com12 adantl impbid ) BCDZBEFZOGAOAHZBEZPOA
    RHABCIJORAHPROAQBKLMN $.

  $( A variable introduction law for equality.  Lemma 15 of [Monk2] p. 109,
     however we do not require ` z ` to be distinct from ` x ` and ` y `
     (making the proof longer).  (Contributed by NM, 5-Aug-1993.)  (Proof
     shortened by Andrew Salmon, 25-May-2011.)  (Proof shortened by Wolf
     Lammen, 7-Apr-2018.) $)
  equvini $p |- ( x = y -> E. z ( x = z /\ z = y ) ) $=
    ( weq wal wa wex equcomi alimi a9e jctir 19.29 adantl eximii jctl 19.29r wn
    syl nfeqf wi ax-8 anc2li equcoms spimed impcom pm2.61ddan ) ABDZCADZCEZCBDZ
    CEZACDZUJFZCGZUIUNUGUIULCEZUJCGZFUNUIUOUPUHULCCAHZICBJKULUJCLRMUKUNUGUKULCG
    ZUKFUNUKURUHULCCAJUQNOULUJCPRMUIQUKQFZUGUNUGUMUSCAABCSUGUMTACULUGUJACBUAUBU
    CUDUEUF $.

  $( Obsolete proof of ~ equvini as of 7-Apr-2018.  (Contributed by NM,
     5-Aug-1993.)  (Proof shortened by Andrew Salmon, 25-May-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  equviniOLD $p |- ( x = y -> E. z ( x = z /\ z = y ) ) $=
    ( weq wal wa wex wi equcomi alimi a9e jctir 19.29 syl6 eximii anc2ri 19.29r
    a1d a1ii wn wo ioran nfeqf ax-8 anc2li equcoms spimed sylbi ecase3 ) CADZCE
    ZCBDZCEZABDZACDZULFZCGZHZUKUNUOCEZULCGZFZUQUKVAUNUKUSUTUJUOCCAIZJCBKLRUOULC
    MNUMUNUOCGZUMFUQUMUNVCUMUNVCUJUOCCAKVBOSPUOULCQNUKUMUATUKTUMTFZURUKUMUBUNUP
    VDCAABCUCUNUPHACUOUNULACBUDUEUFUGUHUI $.

  $( A variable elimination law for equality with no distinct variable
     requirements.  (Compare ~ equvini .)  (Contributed by NM, 1-Mar-2013.)
     (Proof shortened by Mario Carneiro, 17-Oct-2016.)  (Proof shortened by
     Wolf Lammen, 15-Apr-2018.) $)
  equveli $p |- ( A. z ( z = x <-> z = y ) -> x = y ) $=
    ( weq wb wal wi wn wnf wex nfeqf a9e bi2 ax-8 syl6com pm2.43a eximii 19.35i
    wa al2imi nf2 biimpi syl2im ex bi1 com12 pm2.61ii 19.21bi ) CADZCBDZEZCFZAB
    DZCUICFZUJCFZULUMCFZGZUNHZUOHZUQURUSSUMCIZULUMCJZUPABCKUKUMCUJUKUMGCCBLUKUJ
    UMUKUJUIUJUMGUIUJMCABNZOPZQRUTVAUPGUMCUAUBUCUDUIUKUMCUKUIUMUKUIUJUIUMGUIUJU
    EUIUJUMVBUFOPTUJUKUMCVCTUGUH $.

  $( Obsolete proof of ~ equveli as of 15-Apr-2018.  (Contributed by NM,
     1-Mar-2013.)  (Proof shortened by Mario Carneiro, 17-Oct-2016.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  equveliOLD $p |- ( A. z ( z = x <-> z = y ) -> x = y ) $=
    ( weq wb wal wi wa albiim equequ1 imbi12d sps dral1 equid sp equcomi syl6bi
    mpi wn pm2.61i syl adantld dral2 a1bi biimpri a1d wnf nfeqf equtr ax-8 mpii
    imim12d ax-gen spimt sylancl ex adantrd sylbi ) CADZCBDZECFUSUTGZCFZUTUSGZC
    FZHZABDZUSUTCIUTCFZVEVFGVGVDVFVBVGVDBBDZBADZGZBFZVFVCVJCBUTVCVJECUTUTVHUSVI
    CBBJCBAJKLMVKVIVFVKVHVIBNVJBORBAPUAQUBVGSZVBVFVDUSCFZVLVBVFGZGVMVNVLVMVBAAD
    ZVFGZCFVFVAVPCACUSVAVPECUSUSVOUTVFCAAJCABJKLUCVPVFCVFVPVOVFANZUDUELQUFVMSZV
    LVNVRVLHVFCUGUSVAVFGGZCFVNABCUHVSCUSVAVOVFVQUSVOUSUTVFCAAUICABUJULUKUMVAVFC
    AUNUOUPTUQTUR $.

  ${
    $d x z $.  $d y z $.
    $( A variable introduction law for equality.  Lemma 15 of [Monk2] p. 109.
       (Contributed by NM, 5-Aug-1993.) $)
    equvin $p |- ( x = y <-> E. z ( x = z /\ z = y ) ) $=
      ( weq wa wex equvini equtr imp exlimiv impbii ) ABDZACDZCBDZEZCFABCGOLCMN
      LACBHIJK $.
  $}

  ${
    equs45f.1 $e |- F/ y ph $.
    $( Two ways of expressing substitution when ` y ` is not free in ` ph ` .
       (Contributed by NM, 25-Apr-2008.)  (Revised by Mario Carneiro,
       4-Oct-2016.) $)
    equs45f $p |- ( E. x ( x = y /\ ph ) <-> A. x ( x = y -> ph ) ) $=
      ( weq wa wex wi wal nfri anim2i eximi equs5a syl equs4 impbii ) BCEZAFZBG
      ZQAHBIZSQACIZFZBGTRUBBAUAQACDJKLABCMNABCOP $.
  $}

  $( Lemma used in proofs of substitution properties.  (Contributed by NM,
     5-Aug-1993.) $)
  equs5 $p |- ( -. A. x x = y ->
             ( E. x ( x = y /\ ph ) -> A. x ( x = y -> ph ) ) ) $=
    ( weq wal wn wa wi nfna1 nfa1 ax11o imp3a exlimd ) BCDZBEFZNAGNAHZBEZBNBIPB
    JONAQABCKLM $.

  $( One direction of a simplified definition of substitution.  (Contributed by
     NM, 5-Aug-1993.) $)
  sb2 $p |- ( A. x ( x = y -> ph ) -> [ y / x ] ph ) $=
    ( weq wi wal wa wex wsb sp equs4 df-sb sylanbrc ) BCDZAEZBFONAGBHABCIOBJABC
    KABCLM $.

  $( The specialization axiom of standard predicate calculus.  It states that
     if a statement ` ph ` holds for all ` x ` , then it also holds for the
     specific case of ` y ` (properly) substituted for ` x ` .  Translated to
     traditional notation, it can be read:  " ` A. x ph ( x ) -> ph ( y ) ` ,
     provided that ` y ` is free for ` x ` in ` ph ( x ) ` ."  Axiom 4 of
     [Mendelson] p. 69.  See also ~ spsbc and ~ rspsbc .  (Contributed by NM,
     5-Aug-1993.) $)
  stdpc4 $p |- ( A. x ph -> [ y / x ] ph ) $=
    ( wal weq wi wsb ax-1 alimi sb2 syl ) ABDBCEZAFZBDABCGAMBALHIABCJK $.

  ${
    sbt.1 $e |- ph $.
    $( A substitution into a theorem remains true.  (See ~ chvar and ~ chvarv
       for versions using implicit substitution.)  (Contributed by NM,
       21-Jan-2004.)  (Proof shortened by Andrew Salmon, 25-May-2011.)  (Proof
       shortened by Wolf Lammen, 20-Jul-2018.) $)
    sbt $p |- [ y / x ] ph $=
      ( wsb stdpc4 mpg ) AABCEBABCFDG $.
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

  $( Simplified definition of substitution when variables are distinct.
     (Contributed by NM, 27-May-1997.) $)
  sb4b $p |- ( -. A. x x = y -> ( [ y / x ] ph <-> A. x ( x = y -> ph ) ) ) $=
    ( weq wal wn wsb wi sb4 sb2 impbid1 ) BCDZBEFABCGLAHBEABCIABCJK $.

  $( Bound-variable hypothesis builder for substitution.  (Contributed by NM,
     5-Aug-1993.) $)
  hbsb2 $p |- ( -. A. x x = y -> ( [ y / x ] ph -> A. x [ y / x ] ph ) ) $=
    ( weq wal wn wsb wi sb4 sb2 a5i syl6 ) BCDZBEFABCGZMAHZBENBEABCIONBABCJKL
    $.

  $( Bound-variable hypothesis builder for substitution.  (Contributed by Mario
     Carneiro, 4-Oct-2016.) $)
  nfsb2 $p |- ( -. A. x x = y -> F/ x [ y / x ] ph ) $=
    ( weq wal wn wsb nfna1 hbsb2 nfd ) BCDZBEFABCGBKBHABCIJ $.

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
    $( If ` y ` is not free in ` ph ` , ` x ` is not free in
       ` [ y / x ] ph ` .  (Contributed by NM, 5-Aug-1993.) $)
    hbsb3 $p |- ( [ y / x ] ph -> A. x [ y / x ] ph ) $=
      ( wsb wal sbimi hbsb2a syl ) ABCEZACFZBCEJBFAKBCDGABCHI $.
  $}

  ${
    nfs1.1 $e |- F/ y ph $.
    $( If ` y ` is not free in ` ph ` , ` x ` is not free in
       ` [ y / x ] ph ` .  (Contributed by Mario Carneiro, 11-Aug-2016.) $)
    nfs1 $p |- F/ x [ y / x ] ph $=
      ( wsb nfri hbsb3 nfi ) ABCEBABCACDFGH $.
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
    $d x z $.  $d y z $.
    $( When the class variables in definition ~ df-clel are replaced with set
       variables, this theorem of predicate calculus is the result.  This
       theorem provides part of the justification for the consistency of that
       definition, which "overloads" the set variables in ~ wel with the class
       variables in ~ wcel .  Note:  This proof is referenced on the Metamath
       Proof Explorer Home Page and shouldn't be changed.  (Contributed by NM,
       28-Jan-2004.)  (Proof modification is discouraged.) $)
    cleljust $p |- ( x e. y <-> E. z ( z = x /\ z e. y ) ) $=
      ( weq wel wa wex ax-17 elequ1 equsexh bicomi ) CADCBEZFCGABEZLMCAMCHCABIJ
      K $.
  $}

  ${
    $d x z $.  $d y z $.
    $( When the class variables in definition ~ df-clel are replaced with set
       variables, this theorem of predicate calculus is the result.  This
       theorem provides part of the justification for the consistency of that
       definition, which "overloads" the set variables in ~ wel with the class
       variables in ~ wcel .  (Contributed by NM, 28-Jan-2004.)  (Revised by
       Mario Carneiro, 21-Dec-2016.)  (Proof modification is discouraged.) $)
    cleljustALT $p |- ( x e. y <-> E. z ( z = x /\ z e. y ) ) $=
      ( weq wel wa wex nfv elequ1 equsex bicomi ) CADCBEZFCGABEZLMCAMCHCABIJK
      $.
  $}

  ${
    $d w z x $.  $d w y $.
    $( Quantifier introduction when one pair of variables is distinct.
       (Contributed by NM, 2-Jan-2002.) $)
    dveel1 $p |- ( -. A. x x = y -> ( y e. z -> A. x y e. z ) ) $=
      ( vw wel elequ1 dvelimv ) DCEBCEABDDBCFG $.

    $( Quantifier introduction when one pair of variables is distinct.
       (Contributed by NM, 2-Jan-2002.) $)
    dveel2 $p |- ( -. A. x x = y -> ( z e. y -> A. x z e. y ) ) $=
      ( vw wel elequ2 dvelimv ) CDECBEABDDBCFG $.
  $}

  ${
    $d w y $.  $d w z $.  $d w x $.  $( ` w ` is dummy. $)
    $( Axiom ~ ax-15 is redundant if we assume ~ ax-17 .  Remark 9.6 in
       [Megill] p. 448 (p. 16 of the preprint), regarding axiom scheme C14'.

       Note that ` w ` is a dummy variable introduced in the proof.  On the web
       page, it is implicitly assumed to be distinct from all other variables.
       (This is made explicit in the database file set.mm).  Its purpose is to
       satisfy the distinct variable requirements of ~ dveel2 and ~ ax-17 .  By
       the end of the proof it has vanished, and the final theorem has no
       distinct variable requirements.  (Contributed by NM, 29-Jun-1995.)
       (Proof modification is discouraged.) $)
    ax15 $p |- ( -. A. z z = x -> ( -. A. z z = y ->
              ( x e. y -> A. z x e. y ) ) ) $=
      ( vw weq wal wn wel hbn1 dveel2 hbim1 elequ1 imbi2d dvelim nfa1 nfn 19.21
      wi syl6ib pm2.86d ) CAECFGZCBEZCFZGZABHZUECFZUAUDUERZUGCFUDUFRUDDBHZRUGCA
      DUDUHCUBCICBDJKDAEUHUEUDDABLMNUDUECUCCUBCOPQST $.
  $}

  $( An alternate definition of proper substitution that, like ~ df-sb , mixes
     free and bound variables to avoid distinct variable requirements.
     (Contributed by NM, 17-Feb-2005.) $)
  dfsb2 $p |- ( [ y / x ] ph <->
              ( ( x = y /\ ph ) \/ A. x ( x = y -> ph ) ) ) $=
    ( wsb weq wa wi wal wo sp sbequ2 sps orc ee12an sb4 olc syl6 pm2.61i sbequ1
    wn imp sb2 jaoi impbii ) ABCDZBCEZAFZUFAGBHZIZUFBHZUEUIGUJUFUEAUIUFBJUFUEAG
    BABCKLUGUHMNUJTUEUHUIABCOUHUGPQRUGUEUHUFAUEABCSUAABCUBUCUD $.

  $( An alternate definition of proper substitution ~ df-sb that uses only
     primitive connectives (no defined terms) on the right-hand side.
     (Contributed by NM, 6-Mar-2007.) $)
  dfsb3 $p |- ( [ y / x ] ph <->
              ( ( x = y -> -. ph ) -> A. x ( x = y -> ph ) ) ) $=
    ( weq wa wi wal wo wn wsb df-or dfsb2 imnan imbi1i 3bitr4i ) BCDZAEZPAFBGZH
    QIZRFABCJPAIFZRFQRKABCLTSRPAMNO $.

  $( An equality theorem for substitution.  (Contributed by NM, 5-Aug-1993.)
     (Proof shortened by Wolf Lammen, 14-Jul-2018.) $)
  sbequi $p |- ( x = y -> ( [ x / z ] ph -> [ y / z ] ph ) ) $=
    ( weq wal wsb wi wn wex wa equvini sbequ2 sbequ1 syl9 equcoms imp wnf nfsb2
    sps eximi adantr adantl nfimd 19.9d syl5 ex equtr syld equequ2 biimprd syli
    syl com12 pm2.61ii ) DBEZDFZDCEZDFZBCEZADBGZADCGZHZHZUQIZUSIZVDUTVCDJZVEVFK
    ZVCUTBDEZURKZDJVGBCDLVJVCDVIURVCURVCHDBUPVAAURVBADBMADCNOZPQUAUMVCVHDVHVAVB
    DVEVADRVFADBSUBVFVBDRVEADCSUCUDUEUFUGUPVDDUPUTURVCDBCUHVKUITURVDDUTURVCURUT
    UPVCUTUPURBCDUJUKVKULUNTUO $.

  $( An equality theorem for substitution.  Used in proof of Theorem 9.7 in
     [Megill] p. 449 (p. 16 of the preprint).  (Contributed by NM,
     5-Aug-1993.) $)
  sbequ $p |- ( x = y -> ( [ x / z ] ph <-> [ y / z ] ph ) ) $=
    ( weq wsb sbequi wi equcoms impbid ) BCEADBFZADCFZABCDGLKHCBACBDGIJ $.

  $( Formula-building lemma for use with the Distinctor Reduction Theorem.
     Part of Theorem 9.4 of [Megill] p. 448 (p. 16 of preprint).  (Contributed
     by NM, 5-Aug-1993.) $)
  drsb1 $p |- ( A. x x = y -> ( [ z / x ] ph <-> [ z / y ] ph ) ) $=
    ( weq wal wi wa wex wsb wb equequ1 sps imbi1d anbi1d drex1 anbi12d 3bitr4g
    df-sb ) BCEZBFZBDEZAGZUBAHZBIZHCDEZAGZUFAHZCIZHABDJACDJUAUCUGUEUIUAUBUFATUB
    UFKBBCDLMZNUDUHBCUAUBUFAUJOPQABDSACDSR $.

  $( Formula-building lemma for use with the Distinctor Reduction Theorem.
     Part of Theorem 9.4 of [Megill] p. 448 (p. 16 of preprint).  (Contributed
     by NM, 27-Feb-2005.) $)
  drsb2 $p |- ( A. x x = y -> ( [ x / z ] ph <-> [ y / z ] ph ) ) $=
    ( weq wsb wb sbequ sps ) BCEADBFADCFGBABCDHI $.

  $( Obsolete proof of ~ sbequi as of 2-May-2018.  (Contributed by NM,
     5-Aug-1993.)  (Proof modification is discoraged.)
     (New usage is discouraged.) $)
  sbequiOLD $p |- ( x = y -> ( [ x / z ] ph -> [ y / z ] ph ) ) $=
    ( weq wal wsb wi wn wa wex hbsb2 stdpc7 sbequ1 sylan9 sps adantr drsb1 syld
    ex equvini eximi 19.35 sylib nfsb2 19.9d syl9 sbequ2 biimprd sylan9r biimpd
    syl com23 pm2.61ii ) DBEZDFZDCEZDFZBCEZADBGZADCGZHZHUPIZUSURIZVBVCUSVDVBHVC
    USJUTVADKZVDVAVCUTUTDFZUSVEADBLUSVBDKZVFVEHUSBDEZUQJZDKVGBCDUAVIVBDVHUTAUQV
    AABDMADCNZOUBULUTVADUCUDOVAVDDADCUEUFUGTUMUPUSVBUPUSJUTAVAUPUTAHZUSUOVKDADB
    UHPQUSAABCGZUPVAABCNUPVAVLADBCRUIUJSTURUSVBURUSJUTAVAURUTACBGZUSAURUTVMADCB
    RUKABCMOURAVAHZUSUQVNDVJPQSTUN $.

  $( Substitution has no effect on a non-free variable.  (Contributed by NM,
     30-May-2009.)  (Revised by Mario Carneiro, 12-Oct-2016.)  (Proof shortened
     by Wolf Lammen, 3-May-2018.) $)
  sbft $p |- ( F/ x ph -> ( [ y / x ] ph <-> ph ) ) $=
    ( wnf wsb wex spsbe 19.9t syl5ib wal nfr stdpc4 syl6 impbid ) ABDZABCEZAPAB
    FOAABCGABHIOAABJPABKABCLMN $.

  $( Obsolete proof of ~ sbft as of 22-Apr-2018.  (Contributed by NM,
     30-May-2009.)  (Revised by Mario Carneiro, 12-Oct-2016.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  sbftOLD $p |- ( F/ x ph -> ( [ y / x ] ph <-> ph ) ) $=
    ( wnf wsb weq wa wex sb1 wal simpr ax-gen 19.23t mpbii syl5 nfr stdpc4 syl6
    wi impbid ) ABDZABCEZAUBBCFZAGZBHZUAAABCIUAUDASZBJUEASUFBUCAKLUDABMNOUAAABJ
    UBABPABCQRT $.

  ${
    sbf.1 $e |- F/ x ph $.
    $( Substitution for a variable not free in a wff does not affect it.
       (Contributed by NM, 5-Aug-1993.)  (Revised by Mario Carneiro,
       4-Oct-2016.) $)
    sbf $p |- ( [ y / x ] ph <-> ph ) $=
      ( wnf wsb wb sbft ax-mp ) ABEABCFAGDABCHI $.
  $}

  ${
    sbh.1 $e |- ( ph -> A. x ph ) $.
    $( Substitution for a variable not free in a wff does not affect it.
       (Contributed by NM, 5-Aug-1993.) $)
    sbh $p |- ( [ y / x ] ph <-> ph ) $=
      ( nfi sbf ) ABCABDEF $.
  $}

  $( Substitution has no effect on a bound variable.  (Contributed by NM,
     1-Jul-2005.) $)
  sbf2 $p |- ( [ y / x ] A. x ph <-> A. x ph ) $=
    ( wal nfa1 sbf ) ABDBCABEF $.

  ${
    nfs1f.1 $e |- F/ x ph $.
    $( If ` x ` is not free in ` ph ` , it is not free in ` [ y / x ] ph ` .
       (Contributed by Mario Carneiro, 11-Aug-2016.) $)
    nfs1f $p |- F/ x [ y / x ] ph $=
      ( wsb sbf nfxfr ) ABCEABABCDFDG $.
  $}

  ${
    sb6x.1 $e |- F/ x ph $.
    $( Equivalence involving substitution for a variable not free.
       (Contributed by NM, 5-Aug-1993.)  (Revised by Mario Carneiro,
       4-Oct-2016.) $)
    sb6x $p |- ( [ y / x ] ph <-> A. x ( x = y -> ph ) ) $=
      ( wsb weq wi wal sbf biidd equsal bitr4i ) ABCEABCFZAGBHABCDIAABCDMAJKL
      $.
  $}

  ${
    sb6f.1 $e |- F/ y ph $.
    $( Equivalence for substitution when ` y ` is not free in ` ph ` .
       (Contributed by NM, 5-Aug-1993.)  (Revised by Mario Carneiro,
       4-Oct-2016.) $)
    sb6f $p |- ( [ y / x ] ph <-> A. x ( x = y -> ph ) ) $=
      ( wsb weq wi wal nfri sbimi sb4a syl sb2 impbii ) ABCEZBCFAGBHZOACHZBCEPA
      QBCACDIJABCKLABCMN $.

    $( Equivalence for substitution when ` y ` is not free in ` ph ` .
       (Contributed by NM, 5-Aug-1993.)  (Revised by Mario Carneiro,
       4-Oct-2016.) $)
    sb5f $p |- ( [ y / x ] ph <-> E. x ( x = y /\ ph ) ) $=
      ( wsb weq wi wal wa wex sb6f equs45f bitr4i ) ABCEBCFZAGBHNAIBJABCDKABCDL
      M $.
  $}

  $( Substitution does not change an identical variable specifier.
     (Contributed by NM, 5-Aug-1993.) $)
  sbequ5 $p |- ( [ w / z ] A. x x = y <-> A. x x = y ) $=
    ( weq wal nfae sbf ) ABEAFCDABCGH $.

  $( Substitution does not change a distinctor.  (Contributed by NM,
     5-Aug-1993.) $)
  sbequ6 $p |- ( [ w / z ] -. A. x x = y <-> -. A. x x = y ) $=
    ( weq wal wn nfnae sbf ) ABEAFGCDABCHI $.

  ${
    sbtOLD.1 $e |- ph $.
    $( Obsolete proof of ~ sbt as of 20-Jul-2018.)  (Contributed by NM,
       21-Jan-2004.)  (Proof shortened by Andrew Salmon, 25-May-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    sbtOLD $p |- [ y / x ] ph $=
      ( wsb nfth sbf mpbir ) ABCEADABCABDFGH $.
  $}

  $( A variable not free remains so after substitution with a distinct variable
     (closed form of ~ nfsb4 ).  (Contributed by NM, 7-Apr-2004.)  (Revised by
     Mario Carneiro, 4-Oct-2016.)  (Proof shortened by Wolf Lammen,
     11-May-2018.) $)
  nfsb4t $p |- ( A. x F/ z ph ->
                 ( -. A. z z = y -> F/ z [ y / x ] ph ) ) $=
    ( wnf wal weq wn wsb wi wa sbequ12 sps drnf2 biimpd spsd impcom nfnae nfan
    wb a1d nfnf1 nfal nfa1 sp adantr nfsb2 adantl a1i dvelimdf pm2.61dan ) ADEZ
    BFZBCGZBFZDCGDFHZABCIZDEZJUMUOKURUPUOUMURUOULURBUOULURAUQBCDUNAUQTZBABCLZMN
    OPQUAUMUOHZKZAUQDCBUMVADULDBADUBUCBCDRSUMVABULBUDBCBRSUMULVAULBUEUFVAUQBEUM
    ABCUGUHUNUSJVBUTUIUJUK $.

  $( Obsolete proof of ~ nfsb4t as of 6-May-2018.  (Contributed by NM,
     7-Apr-2004.)  (Revised by Mario Carneiro, 4-Oct-2016.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  nfsb4tOLD $p |- ( A. x F/ z ph ->
                 ( -. A. z z = y -> F/ z [ y / x ] ph ) ) $=
    ( wnf wal weq wn wsb wi wa sbequ12 sps drnf2 biimpcd a1dd nfa1 nfnae nfan
    wb nfeqf adantl sp adantr nfimd nfald sb4b nfbidf imbi2d syl5ibrcom pm2.61d
    ex exp3a nfsb2 drsb1 syl5ib pm2.61d2 ) ADEZBFZDBGDFZDCGDFHZABCIZDEZJUSUTHZV
    AVCUSBCGZBFZVDVAKZVCJZUSVFVCVGURVFVCJBVFURVCAVBBCDVEAVBTBABCLMNOMPUSVHVFHZV
    GVEAJZBFZDEZJUSVGVLUSVGKZVJDBUSVGBURBQVDVABDBBRDCBRSSVMVEADVGVEDEUSBCDUAUBU
    SURVGURBUCUDUEUFULVIVCVLVGVIVBVKDBCDRABCUGUHUIUJUKUMVAADCIZDEUTVCADCUNVNVBD
    BDADBCUONUPUQ $.

  ${
    nfsb4.1 $e |- F/ z ph $.
    $( A variable not free remains so after substitution with a distinct
       variable.  (Contributed by NM, 5-Aug-1993.)  (Revised by Mario Carneiro,
       4-Oct-2016.) $)
    nfsb4 $p |- ( -. A. z z = y -> F/ z [ y / x ] ph ) $=
      ( wnf weq wal wn wsb wi nfsb4t mpg ) ADFDCGDHIABCJDFKBABCDLEM $.
  $}

  $( Negation inside and outside of substitution are equivalent.  (Contributed
     by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen, 30-Apr-2018.) $)
  sbn $p |- ( [ y / x ] -. ph <-> -. [ y / x ] ph ) $=
    ( wn wsb weq wi wal wa wex df-sb exanali anbi2i annim 3bitri dfsb3 xchbinxr
    ) ADZBCEZBCFZRGZTAGBHZGZABCESUATRIBJZIUAUBDZIUCDRBCKUDUEUATABLMUAUBNOABCPQ
    $.

  $( Obsolete proof of ~ sbn as of 30-Apr-2018.  (Contributed by NM,
     5-Aug-1993.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  sbnOLD $p |- ( [ y / x ] -. ph <-> -. [ y / x ] ph ) $=
    ( wn wsb weq wal wi sbequ2 nsyld sps sb4 wa wex sb1 equs3 sylib syl6 sylibr
    con2i pm2.61i sbequ1 con3rr3 sb2 notnot sbbii con3i df-sb sylanbrc impbii )
    ADZBCEZABCEZDZBCFZBGZULUNHZUOUQBUOULAUMUKBCIABCIJKUPDULUOUKHZBGZUNUKBCLUMUS
    UMUOAMBNUSDABCOABCPQTRUAUNURUOUKMBNZULUOAUMABCUBUCUNUOUKDZHBGZDUTVBUMVBVABC
    EUMVABCUDAVABCAUEUFSUGUKBCPSUKBCUHUIUJ $.

  $( Removal of implication from substitution.  (Contributed by NM,
     5-Aug-1993.) $)
  sbi1 $p |- ( [ y / x ] ( ph -> ps ) -> ( [ y / x ] ph -> [ y / x ] ps ) ) $=
    ( weq wal wi wsb sbequ2 syl5d sbequ1 syl6d sps sb4 ax-2 al2imi syl6 pm2.61i
    wn sb2 ) CDEZCFZABGZCDHZACDHZBCDHZGGZUAUGCUAUDUEBUFUAUEAUDBACDIUCCDIJBCDKLM
    UBSZUEUAAGZCFZUDUFACDNUHUDUAUCGZCFZUJUFGUCCDNULUJUABGZCFUFUKUIUMCUAABOPBCDT
    QQJR $.

  $( Introduction of implication into substitution.  (Contributed by NM,
     5-Aug-1993.) $)
  sbi2 $p |- ( ( [ y / x ] ph -> [ y / x ] ps ) -> [ y / x ] ( ph -> ps ) ) $=
    ( wsb wi wn sbn pm2.21 sbimi sylbir ax-1 ja ) ACDEZBCDEABFZCDEZNGAGZCDEPACD
    HQOCDABIJKBOCDBALJM $.

  $( Specialization of implication.  (Contributed by NM, 5-Aug-1993.)  (Proof
     shortened by Andrew Salmon, 25-May-2011.) $)
  spsbim $p |- ( A. x ( ph -> ps ) -> ( [ y / x ] ph -> [ y / x ] ps ) ) $=
    ( wi wal wsb stdpc4 sbi1 syl ) ABEZCFKCDGACDGBCDGEKCDHABCDIJ $.

  $( Implication inside and outside of substitution are equivalent.
     (Contributed by NM, 5-Aug-1993.) $)
  sbim $p |- ( [ y / x ] ( ph -> ps ) <-> ( [ y / x ] ph -> [ y / x ] ps ) ) $=
    ( wi wsb sbi1 sbi2 impbii ) ABECDFACDFBCDFEABCDGABCDHI $.

  ${
    sbrim.1 $e |- F/ x ph $.
    $( Substitution with a variable not free in antecedent affects only the
       consequent.  (Contributed by NM, 5-Aug-1993.)  (Revised by Mario
       Carneiro, 4-Oct-2016.) $)
    sbrim $p |- ( [ y / x ] ( ph -> ps ) <-> ( ph -> [ y / x ] ps ) ) $=
      ( wi wsb sbim sbf imbi1i bitri ) ABFCDGACDGZBCDGZFAMFABCDHLAMACDEIJK $.
  $}

  ${
    sblim.1 $e |- F/ x ps $.
    $( Substitution with a variable not free in consequent affects only the
       antecedent.  (Contributed by NM, 14-Nov-2013.)  (Revised by Mario
       Carneiro, 4-Oct-2016.) $)
    sblim $p |- ( [ y / x ] ( ph -> ps ) <-> ( [ y / x ] ph -> ps ) ) $=
      ( wi wsb sbim sbf imbi2i bitri ) ABFCDGACDGZBCDGZFLBFABCDHMBLBCDEIJK $.
  $}

  $( Logical OR inside and outside of substitution are equivalent.
     (Contributed by NM, 29-Sep-2002.) $)
  sbor $p |- ( [ y / x ] ( ph \/ ps ) <-> ( [ y / x ] ph \/ [ y / x ] ps ) ) $=
    ( wn wi wsb wo sbim sbn imbi1i bitri df-or sbbii 3bitr4i ) AEZBFZCDGZACDGZE
    ZBCDGZFZABHZCDGSUAHRPCDGZUAFUBPBCDIUDTUAACDJKLUCQCDABMNSUAMO $.

  $( Conjunction inside and outside of a substitution are equivalent.
     (Contributed by NM, 5-Aug-1993.) $)
  sban $p |- ( [ y / x ] ( ph /\ ps ) <-> ( [ y / x ] ph /\ [ y / x ] ps ) ) $=
    ( wn wi wsb wa sbn sbim imbi2i bitri xchbinx df-an sbbii 3bitr4i ) ABEZFZEZ
    CDGZACDGZBCDGZEZFZEABHZCDGUAUBHTRCDGZUDRCDIUFUAQCDGZFUDAQCDJUGUCUABCDIKLMUE
    SCDABNOUAUBNP $.

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

  $( Specialization of biconditional.  (Contributed by NM, 5-Aug-1993.) $)
  spsbbi $p |- ( A. x ( ph <-> ps ) -> ( [ y / x ] ph <-> [ y / x ] ps ) ) $=
    ( wb wal wsb stdpc4 sbbi sylib ) ABEZCFKCDGACDGBCDGEKCDHABCDIJ $.

  ${
    sbbid.1 $e |- F/ x ph $.
    sbbid.2 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Deduction substituting both sides of a biconditional.  (Contributed by
       NM, 5-Aug-1993.) $)
    sbbid $p |- ( ph -> ( [ y / x ] ps <-> [ y / x ] ch ) ) $=
      ( wb wal wsb alrimi spsbbi syl ) ABCHZDIBDEJCDEJHANDFGKBCDELM $.
  $}

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
    sbrbif.1 $e |- F/ x ch $.
    sbrbif.2 $e |- ( [ y / x ] ph <-> ps ) $.
    $( Introduce right biconditional inside of a substitution.  (Contributed by
       NM, 18-Aug-1993.)  (Revised by Mario Carneiro, 4-Oct-2016.) $)
    sbrbif $p |- ( [ y / x ] ( ph <-> ch ) <-> ( ps <-> ch ) ) $=
      ( wb wsb sbrbis sbf bibi2i bitri ) ACHDEIBCDEIZHBCHABCDEGJNCBCDEFKLM $.
  $}

  $( Obsolete proof of ~ spsbe as of 3-May-2018.  (Contributed by NM,
     5-Aug-1993.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  spsbeOLD $p |- ( [ y / x ] ph -> E. x ph ) $=
    ( wsb wn wal wex stdpc4 sbn sylib con2i df-ex sylibr ) ABCDZAEZBFZEABGPNPOB
    CDNEOBCHABCIJKABLM $.

  $( Elimination of equality from antecedent after substitution.  (Contributed
     by NM, 5-Aug-1993.)  (New usage is discouraged.) $)
  sbequ8ALT $p |- ( [ y / x ] ph <-> [ y / x ] ( x = y -> ph ) ) $=
    ( wsb weq wi equsb1 a1bi sbim bitr4i ) ABCDZBCEZBCDZKFLAFBCDMKBCGHLABCIJ $.

  ${
    sbie.1 $e |- F/ x ps $.
    sbie.2 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Conversion of implicit substitution to explicit substitution.
       (Contributed by NM, 30-Jun-1994.)  (Revised by Mario Carneiro,
       4-Oct-2016.)  (Revised by Wolf Lammen, 14-Jul-2018.) $)
    sbie $p |- ( [ y / x ] ph <-> ps ) $=
      ( wsb wb weq wi sbt sbequ8 mpbir sbbi mpbi sbf bitri ) ACDGZBCDGZBABHZCDG
      ZRSHUACDITJZCDGUBCDFKTCDLMABCDNOBCDEPQ $.
  $}

  ${
    sbied.1 $e |- F/ x ph $.
    sbied.2 $e |- ( ph -> F/ x ch ) $.
    sbied.3 $e |- ( ph -> ( x = y -> ( ps <-> ch ) ) ) $.
    $( Conversion of implicit substitution to explicit substitution (deduction
       version of ~ sbie ).  (Contributed by NM, 30-Jun-1994.)  (Revised by
       Mario Carneiro, 4-Oct-2016.)  (Proof shortened by Wolf Lammen,
       24-Jun-2018.) $)
    sbied $p |- ( ph -> ( [ y / x ] ps <-> ch ) ) $=
      ( wsb wi sbrim nfim1 weq wb com12 pm5.74d sbie bitr3i pm5.74ri ) ABDEIZCA
      TJABJZDEIACJZABDEFKUAUBDEACDFGLDEMZABCAUCBCNHOPQRS $.

    $( Obsolete proof of ~ sbied as of 30-Apr-2018.  (Contributed by NM,
       30-Jun-1994.)  (Revised by Mario Carneiro, 4-Oct-2016.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    sbiedOLD $p |- ( ph -> ( [ y / x ] ps <-> ch ) ) $=
      ( wsb wex weq wa sb1 wb wi bi1 syl6 imp3a syld wal eximd syl5 19.9d com23
      nfrd bi2 alimd sb2 impbid ) ABDEIZCAUJCDJZCUJDEKZBLZDJAUKBDEMAUMCDFAULBCA
      ULBCNZBCOHBCPQRUAUBCADGUCSACCDTZUJACDGUEAUOULBOZDTUJACUPDFAULCBAULUNCBOHB
      CUFQUDUGBDEUHQSUI $.
  $}

  ${
    sbieOLD.1 $e |- F/ x ps $.
    sbieOLD.2 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Obsolete proof of ~ sbie as of 30-Apr-2018.  (Contributed by NM,
       30-Jun-1994.)  (Revised by Mario Carneiro, 4-Oct-2016.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    sbieOLD $p |- ( [ y / x ] ph <-> ps ) $=
      ( wsb wb wtru nftru wnf a1i weq wi sbied trud ) ACDGBHIABCDCJBCKIELCDMABH
      NIFLOP $.
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
    $d x y z $.  $d z ph $.
    $( Alternate proof of ~ ax16 .  (Contributed by NM, 17-May-2008.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    ax16ALT $p |- ( A. x x = y -> ( ph -> A. x ph ) ) $=
      ( vz wsb sbequ12 ax-17 hbsb3 ax16i ) AABDEBCDABDFABDADGHI $.
  $}

  ${
    $d x y $.  $d z ph $.
    $( Alternate proof of ~ ax16 .  (Contributed by NM, 8-Nov-2006.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    ax16ALT2 $p |- ( A. x x = y -> ( ph -> A. x ph ) ) $=
      ( weq wal aev wsb sbequ12 biimpcd alimdv nfv nfs1 stdpc7 cbv3 syl6com syl
      vz wi ) BCDBEBQDZQEZAABEZRBCQBQFATABQGZQEUAASUBQSAUBABQHIJUBAQBABQAQKZLUC
      AQBMNOP $.
  $}

  ${
    $d x y $.
    $( A generalization of axiom ~ ax-16 .  Alternate proof of ~ a16g that uses
       ~ df-sb .  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Andrew
       Salmon, 25-May-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    a16gALT $p |- ( A. x x = y -> ( ph -> A. z ph ) ) $=
      ( weq wal aev ax16ALT2 biidd dral1 biimprd sylsyld ) BCEBFDBEDFZAABFZADFZ
      BCDDBGABCHMONAADBMAIJKL $.
  $}

  ${
    dvelimdfOLD.1 $e |- F/ x ph $.
    dvelimdfOLD.2 $e |- F/ z ph $.
    dvelimdfOLD.3 $e |- ( ph -> F/ x ps ) $.
    dvelimdfOLD.4 $e |- ( ph -> F/ z ch ) $.
    dvelimdfOLD.5 $e |- ( ph -> ( z = y -> ( ps <-> ch ) ) ) $.
    $( Obsolete proof of ~ dvelimdf as of 6-May-2018.  (Contributed by NM,
       7-Apr-2004.)  (Revised by Mario Carneiro, 6-Oct-2016.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    dvelimdfOLD $p |- ( ph -> ( -. A. x x = y -> F/ x ch ) ) $=
      ( weq wal wn wnf wa wsb wi alrimi nfsb4t syl imp nfnae nfan adantr nfbidf
      wb sbied mpbid ex ) ADELDMNZCDOZAUKPZBFEQZDOZULAUKUOABDOZFMUKUORAUPFHISBF
      EDTUAUBUMUNCDAUKDGDEDUCUDAUNCUGUKABCFEHJKUHUEUFUIUJ $.
  $}

  $( A composition law for substitution.  (Contributed by NM, 5-Aug-1993.) $)
  sbco $p |- ( [ y / x ] [ x / y ] ph <-> [ y / x ] ph ) $=
    ( wsb wb weq equsb2 sbequ12 bicomd sbimi ax-mp sbbi mpbi ) ACBDZAEZBCDZNBCD
    ABCDECBFZBCDPBCGQOBCQANACBHIJKNABCLM $.

  ${
    sbid2.1 $e |- F/ x ph $.
    $( An identity law for substitution.  (Contributed by NM, 5-Aug-1993.)
       (Revised by Mario Carneiro, 6-Oct-2016.) $)
    sbid2 $p |- ( [ y / x ] [ x / y ] ph <-> ph ) $=
      ( wsb sbco sbf bitri ) ACBEBCEABCEAABCFABCDGH $.
  $}

  $( An idempotent law for substitution.  (Contributed by NM, 30-Jun-1994.)
     (Proof shortened by Andrew Salmon, 25-May-2011.) $)
  sbidm $p |- ( [ y / x ] [ y / x ] ph <-> [ y / x ] ph ) $=
    ( wsb wb weq equsb2 sbequ12r sbimi ax-mp sbbi mpbi ) ABCDZAEZBCDZMBCDMECBFZ
    BCDOBCGPNBCACBHIJMABCKL $.

  ${
    sbco2.1 $e |- F/ z ph $.
    $( A composition law for substitution.  (Contributed by NM, 30-Jun-1994.)
       (Revised by Mario Carneiro, 6-Oct-2016.) $)
    sbco2 $p |- ( [ y / z ] [ z / x ] ph <-> [ y / x ] ph ) $=
      ( weq wal wsb wb sbid2 sbequ syl5bbr sbequ12 bitr3d sps wn nfnae nfsb4 wi
      nfs1 a1i sbied bicomd pm2.61i ) BCFZBGZABDHZDCHZABCHZIZUEUJBUEAUHUIAUGDBH
      UEUHADBEJUGBCDKLZABCMNOUFPZUIUHULAUHBCBCBQUGDCBABDETRUEAUHISULUKUAUBUCUD
      $.
  $}

  ${
    sbco2d.1 $e |- F/ x ph $.
    sbco2d.2 $e |- F/ z ph $.
    sbco2d.3 $e |- ( ph -> F/ z ps ) $.
    $( A composition law for substitution.  (Contributed by NM, 5-Aug-1993.)
       (Revised by Mario Carneiro, 6-Oct-2016.) $)
    sbco2d $p |- ( ph -> ( [ y / z ] [ z / x ] ps <-> [ y / x ] ps ) ) $=
      ( wsb wi nfim1 sbco2 sbrim sbbii bitri 3bitr3i pm5.74ri ) ABCEIZEDIZBCDIZ
      ABJZCEIZEDIZUACDIASJZATJUACDEABEGHKLUCARJZEDIUDUBUEEDABCEFMNAREDGMOABCDFM
      PQ $.
  $}

  $( A composition law for substitution.  (Contributed by NM, 5-Aug-1993.) $)
  sbco3 $p |- ( [ z / y ] [ y / x ] ph <-> [ z / x ] [ x / y ] ph ) $=
    ( weq wal wsb wb drsb1 sbequ12a alimi spsbbi syl bitr3d wn sbco sbbii nfnae
    nfsb2 sbco2d syl5rbbr pm2.61i ) BCEZBFZABCGZCDGZACBGZBDGZHUDUEBDGZUFUHUEBCD
    IUDUEUGHZBFUIUHHUCUJBABCJKUEUGBDLMNUHUECBGZBDGUDOZUFUKUGBDACBPQULUECDBBCCRB
    CBRABCSTUAUB $.

  $( A commutativity law for substitution.  (Contributed by NM, 27-May-1997.)
     (Proof shortened by Wolf Lammen, 24-Jun-2018.) $)
  sbcom $p |- ( [ y / z ] [ y / x ] ph <-> [ y / x ] [ y / z ] ph ) $=
    ( weq wal wsb wb wn wa drsb1 nfae sbbid bitr3d nfnae nfan sb4b sbequ12 sps
    wi adantr alcom bi2.04 2albii bitri nfeqf 19.21t adantl imbi2d bitr4d albid
    wnf syl syl5bb adantrr ax10 con3i sylan adantrl ad2antll ad2antrl pm2.61ian
    3bitr4d ex pm2.61ii ) BCEZBFZDCEZDFZABCGZDCGZADCGZBCGZHZVGIZVIIZVNBDEBFZVOV
    PJZVNVQVNVRVQVJBCGVKVMVJBDCKVQVJVLBCBDBLABDCKMNUAVQIZVRJZVHVJTZDFZVFVLTZBFZ
    VKVMVTVFVHATZTZDFZBFZWBWDVSVOWHWBHVPWHVHVFATZTZBFZDFZVSVOJZWBWHWFBFDFWLWFBD
    UBWFWJDBVFVHAUCUDUEWMWKWADVSVODBDDOBCDOPWMWKVHWIBFZTZWAWMVHBULWKWOHDCBUFVHW
    IBUGUMWMVJWNVHVOVJWNHVSABCQUHUIUJUKUNUOVSVPWHWDHVOVSVPJZWGWCBVSVPBBDBODCBOP
    WPWGVFWEDFZTZWCWPVFDULZWGWRHVSDBEDFZIVPWSWTVQDBUPUQBCDUFURVFWEDUGUMVPWCWRHV
    SVPVLWQVFADCQUIUHUJUKUSNVPVKWBHVSVOVJDCQUTVOVMWDHVSVPVLBCQVAVCVBVDVGVLVKVMV
    GAVJDCBCDLVFAVJHBABCRSMVFVLVMHBVLBCRSNVIVJVKVMVHVJVKHDVJDCRSVIAVLBCDCBLVHAV
    LHDADCRSMNVE $.

  $( Obsolete proof of ~ sbcom as of 24-Jun-2018.  (Contributed by NM,
     27-May-1997.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  sbcomOLD $p |- ( [ y / z ] [ y / x ] ph <-> [ y / x ] [ y / z ] ph ) $=
    ( weq wal wsb wb wn wa drsb1 nfae sbbid bitr3d nfnae albid sb4b sbequ12 sps
    wi adantr wnf nfeqf 19.21t syl adantrr alcom bi2.04 albii aecom con3i sylan
    nfan syl5bb adantrl imbi2d sylan9bbr sylan9bb 3bitr4d pm2.61ian ex pm2.61ii
    adantl ) BCEZBFZDCEZDFZABCGZDCGZADCGZBCGZHZVEIZVGIZVLBDEBFZVMVNJZVLVOVLVPVO
    VHBCGVIVKVHBDCKVOVHVJBCBDBLABDCKMNUAVOIZVPJZVFVDATZBFZTZDFZVDVFATZDFZTZBFZV
    IVKVRVFVSTZBFZDFZWBWFVQVMWIWBHVNVQVMJZWHWADVQVMDBDDOBCDOZUMWJVFBUBWHWAHDCBU
    CVFVSBUDUEPUFVQVNWIWFHVMWIWGDFZBFVQVNJZWFWGDBUGWMWLWEBVQVNBBDBODCBOZUMWLVDW
    CTZDFZWMWEWGWODVFVDAUHUIWMVDDUBZWPWEHVQDBEDFZIVNWQWRVODBUJUKBCDUCULVDWCDUDU
    EUNPUNUONVPVIWBHVQVNVIVFVHTZDFVMWBVHDCQVMWSWADWKVMVHVTVFABCQUPPUQVCVPVKWFHV
    QVMVKVDVJTZBFVNWFVJBCQVNWTWEBWNVNVJWDVDADCQUPPURVCUSUTVAVEVJVIVKVEAVHDCBCDL
    VDAVHHBABCRSMVDVJVKHBVJBCRSNVGVHVIVKVFVHVIHDVHDCRSVGAVJBCDCBLVFAVJHDADCRSMN
    VB $.

  ${
    sb5rf.1 $e |- F/ y ph $.
    $( Reversed substitution.  (Contributed by NM, 3-Feb-2005.)  (Revised by
       Mario Carneiro, 6-Oct-2016.) $)
    sb5rf $p |- ( ph <-> E. y ( y = x /\ [ y / x ] ph ) ) $=
      ( weq wsb wa wex sbid2 sb1 sylbir stdpc7 imp exlimi impbii ) ACBEZABCFZGZ
      CHZAQCBFSACBDIQCBJKRACDPQAACBLMNO $.

    $( Reversed substitution.  (Contributed by NM, 5-Aug-1993.)  (Revised by
       Mario Carneiro, 6-Oct-2016.) $)
    sb6rf $p |- ( ph <-> A. y ( y = x -> [ y / x ] ph ) ) $=
      ( weq wsb wi wal sbequ1 equcoms com12 alrimi sb2 sbid2 sylib impbii ) ACB
      EZABCFZGZCHZASCDQARARGBCABCIJKLTRCBFARCBMACBDNOP $.

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

  $( Commutation of quantification and substitution variables.  (Contributed by
     NM, 5-Aug-1993.) $)
  sb9i $p |- ( A. x [ x / y ] ph -> A. y [ y / x ] ph ) $=
    ( weq wal wsb wi drsb1 drsb2 bitr3d dral1 biimprd wn nfnae hbsb2 alimd sbco
    stdpc4 sylib alimi a7s syl6 pm2.61i ) CBDCEZACBFZBEZABCFZCEZGUDUHUFUGUECBUD
    ACCFUGUEACBCHACBCIJKLUDMZUFUECEZBEUHUIUEUJBCBBNACBOPUEUHCBUFUGCUFUEBCFUGUEB
    CRABCQSTUAUBUC $.

  $( Commutation of quantification and substitution variables.  (Contributed by
     NM, 5-Aug-1993.) $)
  sb9 $p |- ( A. x [ x / y ] ph <-> A. y [ y / x ] ph ) $=
    ( wsb wal sb9i impbii ) ACBDBEABCDCEABCFACBFG $.

  ${
    $d x y $.  $d x z $.  $d y z $.  $d ph z $.
    $( This is a version of ~ ax-11o when the variables are distinct.  Axiom
       (C8) of [Monk2] p. 105.  See theorem ~ ax11v2 for the rederivation of
       ~ ax-11o from this theorem.  (Contributed by NM, 5-Aug-1993.) $)
    ax11v $p |- ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) $=
      ( weq wal wi ax-1 ax16 syl5 a1d ax11o pm2.61i ) BCDZBEZMAMAFZBEZFZFNQMAON
      PAMGOBCHIJABCKL $.

    $( Alternate proof of ~ ax11v that avoids theorem ~ ax16 and is proved
       directly from ~ ax-11 rather than via ~ ax11o .  (Contributed by Jim
       Kingdon, 15-Dec-2017.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    ax11vALT $p |- ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) $=
      ( vz cv wceq wex wi wal a9e ax-17 ax-11 syl5 equequ2 imbi1d albidv imbi2d
      imbi12d mpbii exlimiv ax-mp ) DEZCEZFZDGBEZUCFZAUFAHZBIZHZHZDCJUDUJDUDUEU
      BFZAUKAHZBIZHZHUJAADIUKUMADKABDLMUDUKUFUNUIDCBNZUDUMUHAUDULUGBUDUKUFAUOOP
      QRSTUA $.

    $( Two equivalent ways of expressing the proper substitution of ` y ` for
       ` x ` in ` ph ` , when ` x ` and ` y ` are distinct.  Theorem 6.2 of
       [Quine] p. 40.  The proof does not involve ~ df-sb .  (Contributed by
       NM, 14-Apr-2008.) $)
    sb56 $p |- ( E. x ( x = y /\ ph ) <-> A. x ( x = y -> ph ) ) $=
      ( weq wi wal nfa1 ax11v sp com12 impbid equsex ) ABCDZAEZBFZBCNBGMAOABCHO
      MANBIJKL $.

    $( Equivalence for substitution.  Compare Theorem 6.2 of [Quine] p. 40.
       Also proved as Lemmas 16 and 17 of [Tarski] p. 70.  (Contributed by NM,
       18-Aug-1993.) $)
    sb6 $p |- ( [ y / x ] ph <-> A. x ( x = y -> ph ) ) $=
      ( weq wi wa wex wal wsb sb56 anbi2i df-sb sp pm4.71ri 3bitr4i ) BCDZAEZPA
      FBGZFQQBHZFABCISRSQABCJKABCLSQQBMNO $.

    $( Equivalence for substitution.  Similar to Theorem 6.1 of [Quine] p. 40.
       (Contributed by NM, 18-Aug-1993.) $)
    sb5 $p |- ( [ y / x ] ph <-> E. x ( x = y /\ ph ) ) $=
      ( wsb weq wi wal wa wex sb6 sb56 bitr4i ) ABCDBCEZAFBGMAHBIABCJABCKL $.
  $}

  ${
    $d y z $.  $d x y $.
    $( Lemma for ~ equsb3 .  (Contributed by Raph Levien and FL, 4-Dec-2005.)
       (Proof shortened by Andrew Salmon, 14-Jun-2011.) $)
    equsb3lem $p |- ( [ x / y ] y = z <-> x = z ) $=
      ( weq nfv equequ1 sbie ) BCDACDZBAHBEBACFG $.
  $}

  ${
    $d w y z $.  $d w x $.
    $( Substitution applied to an atomic wff.  (Contributed by Raph Levien and
       FL, 4-Dec-2005.) $)
    equsb3 $p |- ( [ x / y ] y = z <-> x = z ) $=
      ( vw weq wsb equsb3lem sbbii nfv sbco2 3bitr3i ) BCEZBDFZDAFDCEZDAFLBAFAC
      EMNDADBCGHLBADLDIJADCGK $.
  $}

  ${
    $d w y z $.  $d w x $.
    $( Substitution applied to an atomic membership wff.  (Contributed by NM,
       7-Nov-2006.)  (Proof shortened by Andrew Salmon, 14-Jun-2011.) $)
    elsb3 $p |- ( [ x / y ] y e. z <-> x e. z ) $=
      ( vw wel wsb nfv sbco2 elequ1 sbie sbbii 3bitr3i ) DCEZDBFZBAFMDAFBCEZBAF
      ACEZMDABMBGHNOBAMODBODGDBCIJKMPDAPDGDACIJL $.
  $}

  ${
    $d w y z $.  $d w x $.
    $( Substitution applied to an atomic membership wff.  (Contributed by
       Rodolfo Medina, 3-Apr-2010.)  (Proof shortened by Andrew Salmon,
       14-Jun-2011.) $)
    elsb4 $p |- ( [ x / y ] z e. y <-> z e. x ) $=
      ( vw wel wsb nfv sbco2 elequ2 sbie sbbii 3bitr3i ) CDEZDBFZBAFMDAFCBEZBAF
      CAEZMDABMBGHNOBAMODBODGDBCIJKMPDAPDGDACIJL $.
  $}

  ${
    $d x y $.
    $( ` x ` is not free in ` [ y / x ] ph ` when ` x ` and ` y ` are
       distinct.  (Contributed by NM, 5-Aug-1993.) $)
    hbs1 $p |- ( [ y / x ] ph -> A. x [ y / x ] ph ) $=
      ( weq wal wsb wi ax16 hbsb2 pm2.61i ) BCDBEABCFZKBEGKBCHABCIJ $.

    $( ` x ` is not free in ` [ y / x ] ph ` when ` x ` and ` y ` are
       distinct.  (Contributed by Mario Carneiro, 11-Aug-2016.) $)
    nfs1v $p |- F/ x [ y / x ] ph $=
      ( wsb hbs1 nfi ) ABCDBABCEF $.
  $}

  ${
    $d y ph $.
    $( Two ways of expressing " ` x ` is (effectively) not free in ` ph ` ."
       (Contributed by NM, 29-May-2009.) $)
    sbhb $p |- ( ( ph -> A. x ph ) <-> A. y ( ph -> [ y / x ] ph ) ) $=
      ( wal wi wsb nfv sb8 imbi2i 19.21v bitr4i ) AABDZEAABCFZCDZEAMECDLNAABCAC
      GHIAMCJK $.
  $}

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
    nfsb.1 $e |- F/ z ph $.
    $( If ` z ` is not free in ` ph ` , it is not free in ` [ y / x ] ph ` when
       ` y ` and ` z ` are distinct.  (Contributed by Mario Carneiro,
       11-Aug-2016.) $)
    nfsb $p |- F/ z [ y / x ] ph $=
      ( weq wal wsb wnf a16nf nfsb4 pm2.61i ) DCFDGABCHZDIMDCDJABCDEKL $.
  $}

  ${
    $d y z $.
    hbsb.1 $e |- ( ph -> A. z ph ) $.
    $( If ` z ` is not free in ` ph ` , it is not free in ` [ y / x ] ph ` when
       ` y ` and ` z ` are distinct.  (Contributed by NM, 12-Aug-1993.) $)
    hbsb $p |- ( [ y / x ] ph -> A. z [ y / x ] ph ) $=
      ( wsb nfi nfsb nfri ) ABCFDABCDADEGHI $.
  $}

  ${
    $d y z $.
    nfsbd.1 $e |- F/ x ph $.
    nfsbd.2 $e |- ( ph -> F/ z ps ) $.
    $( Deduction version of ~ nfsb .  (Contributed by NM, 15-Feb-2013.) $)
    nfsbd $p |- ( ph -> F/ z [ y / x ] ps ) $=
      ( weq wal wsb wnf wn wi alrimi nfsb4t syl a16nf pm2.61d2 ) AEDHEIZBCDJZEK
      ZABEKZCISLUAMAUBCFGNBCDEOPTEDEQR $.
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
    $d x z $.  $d x w $.  $d y z $.
    $( Commutativity law for substitution.  Used in proof of Theorem 9.7 of
       [Megill] p. 449 (p. 16 of the preprint).  (Contributed by NM,
       27-May-1997.) $)
    sbcom2 $p |- ( [ w / z ] [ y / x ] ph <-> [ y / x ] [ w / z ] ph ) $=
      ( weq wal wsb wb wn wi albii 19.21v sb4b imbi2d albidv nfae sbequ12 sbbid
      sps wa alcom bi2.04 bitri 3bitr3i a1i sylan9bbr sylan9bb 3bitr4d pm2.61ii
      ex bitr3d ) BCFZBGZDEFZDGZABCHZDEHZADEHZBCHZIZUNJZUPJZVAVBVCUAZUOUMAKZBGZ
      KZDGZUMUOAKZDGZKZBGZURUTVHVLIVDUMVIKZBGZDGVMDGZBGVHVLVMDBUBVNVGDVNUOVEKZB
      GVGVMVPBUMUOAUCLUOVEBMUDLVOVKBUMVIDMLUEUFVCURUOUQKZDGVBVHUQDENVBVQVGDVBUQ
      VFUOABCNOPUGVBUTUMUSKZBGVCVLUSBCNVCVRVKBVCUSVJUMADENOPUHUIUKUNUSURUTUNAUQ
      DEBCDQUMAUQIBABCRTSUMUSUTIBUSBCRTULUPUQURUTUOUQURIDUQDERTUPAUSBCDEBQUOAUS
      IDADERTSULUJ $.
  $}

  ${
    $d ph x y z $.  $d w x z $.
    $( (Probably not) Axiom *11.07 in [WhiteheadRussell] p. 159.  The original
       confusingly reads: *11.07 "Whatever possible argument ` x ` may be,
       ` ph ( x , y ) ` is true whatever possible argument ` y ` may be"
       implies the corresponding statement with ` x ` and ` y ` interchanged
       except in " ` ph ( x , y ) ` ".  This theorem will be deleted after
       22-Feb-2018 if no one is able to determine the correct interpretation.
       See
       ~ https://groups.google.com/d/msg/metamath/iS0fOvSemC8/YzrRyX70AgAJ .
       (Contributed by Andrew Salmon, 17-Jun-2011.)  (Proof shortened by Jim
       Kingdon, 22-Jan-2018.)  (New usage is discouraged.) $)
    pm11.07 $p |- ( [ w / x ] [ y / z ] ph <-> [ y / x ] [ w / z ] ph ) $=
      ( wsb nfv sbf sbbii bitri bitr4i ) ADCFZBEFZAADEFZBCFZMABEFALABEADCADGZHI
      ABEABGZHJOABCFANABCADEPHIABCQHJK $.
  $}

  ${
    $d ph x y z $.  $d w x z $.
    $( Obsolete proof of ~ pm11.07 as of 22-Jan-2018.  (Contributed by Andrew
       Salmon, 17-Jun-2011.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    pm11.07OLD $p |- ( [ w / x ] [ y / z ] ph <-> [ y / x ] [ w / z ] ph ) $=
      ( weq wa wex wsb a9ev pm3.2i 2th eeanv 3bitr4i anbi1i 19.41vv 2sb5 ) BEFZ
      DCFZGZAGDHBHZBCFZDEFZGZAGDHBHZADCIBEIADEIBCITDHBHZAGUDDHBHZAGUAUEUFUGARBH
      ZSDHZGZUBBHZUCDHZGZUFUGUJUMUHUIBEJDCJKUKULBCJDEJKLRSBDMUBUCBDMNOTABDPUDAB
      DPNABDECQABDCEQN $.
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
    2sb5rf.1 $e |- F/ z ph $.
    2sb5rf.2 $e |- F/ w ph $.
    $( Reversed double substitution.  (Contributed by NM, 3-Feb-2005.)
       (Revised by Mario Carneiro, 6-Oct-2016.) $)
    2sb5rf $p |- ( ph <->
                E. z E. w ( ( z = x /\ w = y ) /\ [ z / x ] [ w / y ] ph ) ) $=
      ( weq wsb wex sb5rf 19.42v sbcom2 anbi2i anass bitri exbii nfsb 3bitr4ri
      wa ) ADBHZABDIZTZDJUAECHZTZACEIBDIZTZEJZDJABDFKUCUHDUAUDUBCEIZTZTZEJUAUJE
      JZTUHUCUAUJELUGUKEUGUEUITUKUFUIUEACEBDMNUAUDUIOPQUBULUAUBCEABDEGRKNSQP $.

    $( Reversed double substitution.  (Contributed by NM, 3-Feb-2005.)
       (Revised by Mario Carneiro, 6-Oct-2016.) $)
    2sb6rf $p |- ( ph <->
                A. z A. w ( ( z = x /\ w = y ) -> [ z / x ] [ w / y ] ph ) ) $=
      ( weq wsb wi wal wa sb6rf 19.21v sbcom2 imbi2i impexp bitri albii nfsb
      3bitr4ri ) ADBHZABDIZJZDKUBECHZLZACEIBDIZJZEKZDKABDFMUDUIDUBUEUCCEIZJZJZE
      KUBUKEKZJUIUDUBUKENUHULEUHUFUJJULUGUJUFACEBDOPUBUEUJQRSUCUMUBUCCEABDEGTMP
      UASR $.
  $}

  ${
    $d y z $.
    sb7f.1 $e |- F/ z ph $.
    $( This version of ~ dfsb7 does not require that ` ph ` and ` z ` be
       distinct.  This permits it to be used as a definition for substitution
       in a formalization that omits the logically redundant axiom ~ ax-17 i.e.
       that doesn't have the concept of a variable not occurring in a wff.
       ( ~ df-sb is also suitable, but its mixing of free and bound variables
       is distasteful to some logicians.)  (Contributed by NM, 26-Jul-2006.)
       (Revised by Mario Carneiro, 6-Oct-2016.) $)
    sb7f $p |- ( [ y / x ] ph <->
               E. z ( z = y /\ E. x ( x = z /\ ph ) ) ) $=
      ( wsb cv wceq wa wex sb5f sbbii sbco2 sb5 3bitr3i ) ABDFZDCFBGDGZHAIBJZDC
      FABCFQCGHRIDJPRDCABDEKLABCDEMRDCNO $.
  $}

  ${
    $d y z $.
    sb7h.1 $e |- ( ph -> A. z ph ) $.
    $( This version of ~ dfsb7 does not require that ` ph ` and ` z ` be
       distinct.  This permits it to be used as a definition for substitution
       in a formalization that omits the logically redundant axiom ~ ax-17 i.e.
       that doesn't have the concept of a variable not occurring in a wff.
       ( ~ df-sb is also suitable, but its mixing of free and bound variables
       is distasteful to some logicians.)  (Contributed by NM, 26-Jul-2006.)
       (Proof shortened by Andrew Salmon, 25-May-2011.) $)
    sb7h $p |- ( [ y / x ] ph <->
               E. z ( z = y /\ E. x ( x = z /\ ph ) ) ) $=
      ( nfi sb7f ) ABCDADEFG $.
  $}

  ${
    $d y z $.  $d z ph $.
    $( An alternate definition of proper substitution ~ df-sb .  By introducing
       a dummy variable ` z ` in the definiens, we are able to eliminate any
       distinct variable restrictions among the variables ` x ` , ` y ` , and
       ` ph ` of the definiendum.  No distinct variable conflicts arise because
       ` z ` effectively insulates ` x ` from ` y ` .  To achieve this, we use
       a chain of two substitutions in the form of ~ sb5 , first ` z ` for
       ` x ` then ` y ` for ` z ` .  Compare Definition 2.1'' of [Quine] p. 17,
       which is obtained from this theorem by applying ~ df-clab .  Theorem
       ~ sb7h provides a version where ` ph ` and ` z ` don't have to be
       distinct.  (Contributed by NM, 28-Jan-2004.) $)
    dfsb7 $p |- ( [ y / x ] ph <-> E. z ( z = y /\ E. x ( x = z /\ ph ) ) ) $=
      ( nfv sb7f ) ABCDADEF $.
  $}

  ${
    $d x y $.
    sb10f.1 $e |- F/ x ph $.
    $( Hao Wang's identity axiom P6 in Irving Copi, _Symbolic Logic_ (5th ed.,
       1979), p. 328.  In traditional predicate calculus, this is a sole axiom
       for identity from which the usual ones can be derived.  (Contributed by
       NM, 9-May-2005.)  (Revised by Mario Carneiro, 6-Oct-2016.) $)
    sb10f $p |- ( [ y / z ] ph <-> E. x ( x = y /\ [ x / z ] ph ) ) $=
      ( weq wsb wa wex nfsb sbequ equsex bicomi ) BCFADBGZHBIADCGZNOBCADCBEJABC
      DKLM $.
  $}

  ${
    $d x ph $.
    $( An identity law for substitution.  Used in proof of Theorem 9.7 of
       [Megill] p. 449 (p. 16 of the preprint).  (Contributed by NM,
       5-Aug-1993.) $)
    sbid2v $p |- ( [ y / x ] [ x / y ] ph <-> ph ) $=
      ( nfv sbid2 ) ABCABDE $.
  $}

  ${
    $d x y $.  $d x ph $.
    $( Elimination of substitution.  (Contributed by NM, 5-Aug-1993.) $)
    sbelx $p |- ( ph <-> E. x ( x = y /\ [ x / y ] ph ) ) $=
      ( wsb weq wa wex sbid2v sb5 bitr3i ) AACBDZBCDBCEKFBGABCHKBCIJ $.
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
    $d x y $.
    $( A theorem used in elimination of disjoint variable restriction on ` x `
       and ` y ` by replacing it with a distinctor ` -. A. x x = z ` .
       (Contributed by NM, 5-Aug-1993.) $)
    sbal1 $p |- ( -. A. x x = z ->
             ( [ z / y ] A. x ph <-> A. x [ z / y ] ph ) ) $=
      ( weq wal wn wsb wb wi sbequ12 sps dral2 bitr3d a1d wa nfa1 al2imi hbnaes
      syl6 nfsb4 nfrd sp sbimi alimi adantl ax-7 dveeq2 alim syl9 sylan9 impbid
      sb4 sb2 ex pm2.61i ) CDEZCFZBDEBFGZABFZCDHZACDHZBFZIZJURVDUSURUTVAVCUQUTV
      AICUTCDKLAVBCDBUQAVBICACDKLMNOURGZUSVDVEUSPVAVCUSVAVCJVEUSVAVABFVCUSVABUT
      CDBABQUAUBVAVBBUTACDABUCUDUETUFVEVCUQAJZBFZCFZUSVAVEVCVFCFZBFZVHVCVJJCDBV
      EVBVIBACDUMRSVFBCUGTVHVAJBDCUSCFVHUQUTJZCFVAUSVGVKCUSUQUQBFVGUTBDCUHUQABU
      IUJRUTCDUNTSUKULUOUP $.
  $}

  ${
    $d x y $.  $d x z $.
    $( Move universal quantifier in and out of substitution.  (Contributed by
       NM, 5-Aug-1993.) $)
    sbal $p |- ( [ z / y ] A. x ph <-> A. x [ z / y ] ph ) $=
      ( weq wal wsb wb a16gb sbimi sbequ5 sbbi 3imtr3i bitr3d sbal1 pm2.61i ) B
      DEBFZABFZCDGZACDGZBFZHQTSUAQCDGARHZCDGQTSHQUBCDABDBIJBDCDKARCDLMTBDBINABC
      DOP $.
  $}

  ${
    $d x y $.  $d x z $.
    $( Move existential quantifier in and out of substitution.  (Contributed by
       NM, 27-Sep-2003.) $)
    sbex $p |- ( [ z / y ] E. x ph <-> E. x [ z / y ] ph ) $=
      ( wn wal wsb wex sbn sbal albii bitri xchbinx df-ex sbbii 3bitr4i ) AEZBF
      ZEZCDGZACDGZEZBFZEABHZCDGUABHTRCDGZUCRCDIUEQCDGZBFUCQBCDJUFUBBACDIKLMUDSC
      DABNOUABNP $.
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
    $d x y $.  $d y ph $.
    $( An equivalent expression for existence.  (Contributed by NM,
       2-Feb-2005.) $)
    exsb $p |- ( E. x ph <-> E. y A. x ( x = y -> ph ) ) $=
      ( weq wi wal nfv nfa1 ax11v sp com12 impbid cbvex ) ABCDZAEZBFZBCACGOBHNA
      PABCIPNAOBJKLM $.

    $( An equivalent expression for existence.  Obsolete as of 19-Jun-2017.
       (Contributed by NM, 2-Feb-2005.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    exsbOLD $p |- ( E. x ph <-> E. y A. x ( x = y -> ph ) ) $=
      ( wex wsb cv wceq wi wal nfv sb8e sb6 exbii bitri ) ABDABCEZCDBFCFGAHBIZC
      DABCACJKOPCABCLMN $.
  $}

  ${
    $d x y z $.  $d y w $.  $d z w ph $.
    $( An equivalent expression for double existence.  (Contributed by NM,
       2-Feb-2005.) $)
    2exsb $p |- ( E. x E. y ph <->
                  E. z E. w A. x A. y ( ( x = z /\ y = w ) -> ph ) ) $=
      ( wex weq wi wal wa exsb exbii excom bitri impexp albii 19.21v bitr2i ) A
      CFZBFZCEGZAHZCIZBFZEFZBDGZUAJAHZCIZBIZEFDFZTUCEFZBFUESUKBACEKLUCBEMNUEUID
      FZEFUJUDULEUDUFUCHZBIZDFULUCBDKUNUIDUMUHBUHUFUBHZCIUMUGUOCUFUAAOPUFUBCQRP
      LNLUIEDMNN $.
  $}

  ${
    $d z ps $.  $d x z $.  $d y z $.
    dvelimALT.1 $e |- ( ph -> A. x ph ) $.
    dvelimALT.2 $e |- ( z = y -> ( ph <-> ps ) ) $.
    $( Version of ~ dvelim that doesn't use ~ ax-10 .  (See ~ dvelimh for a
       version that doesn't use ~ ax-11 .)  (Contributed by NM, 17-May-2008.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    dvelimALT $p |- ( -. A. x x = y -> ( ps -> A. x ps ) ) $=
      ( weq wal wn wi ax-17 ax16ALT a1d wa hbn1 hban ax12o imp a1i hbimd hbald
      ex pm2.61i equsalh albii 3imtr3g ) CDHZCIJZEDHZAKZEIZULCIBBCIUIUKCEUIELCE
      HZCIZUIUKUKCIKZKUNUOUIUKCEMNUNJZUIUOUPUIOZUJACUPUICUMCPUHCPQUPUIUJUJCIKED
      CRSAACIKUQFTUAUCUDUBABEDBELGUEZULBCURUFUG $.
  $}

  ${
    $d z y $.  $d z x $.
    $( Move quantifier in and out of substitution.  (Contributed by NM,
       2-Jan-2002.) $)
    sbal2 $p |- ( -. A. x x = y ->
             ( [ z / y ] A. x ph <-> A. x [ z / y ] ph ) ) $=
      ( weq wal wn wi wsb alcom nfnae wnf wb dveeq1 nfd 19.21t syl syl5rbbr sb6
      albid albii 3bitr4g ) BCEBFGZCDEZABFZHZCFZUDAHZCFZBFZUECDIACDIZBFUJUHBFZC
      FUCUGUHCBJUCULUFCBCCKUCUDBLULUFMUCUDBBCBKBCDNOUDABPQTRUECDSUKUIBACDSUAUB
      $.
  $}


$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Predicate calculus with equality:  Older axiomatization (1 rule, 14 schemes)
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#

  The "metalogical completeness theorem", Theorem 9.7 of [Megill] p. 448, uses
  a different but (logically and metalogically) equivalent set of axiom schemes
  for its proof.  In order to show that our axiomatization is also
  metalogically complete, we derive the axiom schemes of that paper in this
  section (or mention where they are derived, if they have already been derived
  as therorems above).  Additionally, we re-derive our axiomatization from the
  one in the paper, showing that the two systems are equivalent.

  The 14 predicate calculus axioms used by the paper are ~ ax-5o , ~ ax-4 ,
  ~ ax-7 , ~ ax-6o , ~ ax-8 , ~ ax-12o , ~ ax-9o , ~ ax-10o , ~ ax-13 ,
  ~ ax-14 , ~ ax-15 , ~ ax-11o , ~ ax-16 , and ~ ax-17 .  Like ours, it
  includes the rule of generalization ( ~ ax-gen ).

  The ones we need to prove from our axioms are ~ ax-5o , ~ ax-4 ,
  ~ ax-6o , ~ ax-12o , ~ ax-9o , ~ ax-10o , ~ ax-15 , ~ ax-11o ,
  and ~ ax-16 . The theorems showing the derivations of those axioms,
  which have all been proved earlier, are ~ ax5o , ~ ax4 (also called
  ~ sp ), ~ ax6o , ~ ax12o , ~ ax9o , ~ ax10o , ~ ax15 , ~ ax11o ,
  ~ ax16 , and ~ ax10 . In addition, ~ ax-10 was an intermediate axiom we
  adopted at one time, and we show its proof in this section as
  ~ ax10from10o .

  This section also includes a few miscellaneous legacy theorems such as
  ~ hbequid use the older axioms.

  Note:  The axioms and theorems in this section should not be used outside of
  this section.  Inside this section, we may use the external axioms ~ ax-gen ,
  ~ ax-17 , ~ ax-8 , ~ ax-9 , ~ ax-13 , and ~ ax-14 since they are common to
  both our current and the older axiomatizations.  (These are the ones that
  were never revised.)

  The following newer axioms may NOT be used in this section until we
  have proved them from the older axioms:  ~ ax-5 , ~ ax-6 , ~ ax-9 ,
  ~ ax-11 , and ~ ax-12 .  However, once we have rederived an axiom
  (e.g. theorem ~ ax5 for axiom ~ ax-5 ), we may make use of theorems
  outside of this section that make use of the rederived axiom (e.g. we
  may use theorem ~ alimi , which uses ~ ax-5 , after proving ~ ax5 ).

$)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
 Obsolete schemes ax-5o ax-4 ax-6o ax-9o ax-10o ax-10 ax-11o ax-12o ax-15 ax-16
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  These older axiom schemes are obsolete and should not be used outside of this
  section.  They are proved above as theorems ax5o , ~ sp , ~ ax6o , ~ ax9o ,
  ~ ax10o , ~ ax10 , ~ ax11o , ~ ax12o , ~ ax15 , and ~ ax16 .

$)

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
     ~ ax-gen .  Conditional forms of the converse are given by ~ ax-12 ,
     ~ ax-15 , ~ ax-16 , and ~ ax-17 .

     Unlike the more general textbook Axiom of Specialization, we cannot choose
     a variable different from ` x ` for the special case.  For use, that
     requires the assistance of equality axioms, and we deal with it later
     after we introduce the definition of proper substitution - see ~ stdpc4 .

     An interesting alternate axiomatization uses ~ ax467 and ~ ax-5o in place
     of ~ ax-4 , ~ ax-5 , ~ ax-6 , and ~ ax-7 .

     This axiom is obsolete and should no longer be used.  It is proved above
     as theorem ~ sp .  (Contributed by NM, 5-Aug-1993.)
     (New usage is discouraged.) $)
  ax-4 $a |- ( A. x ph -> ph ) $.

  $( Axiom of Quantified Implication.  This axiom moves a quantifier from
     outside to inside an implication, quantifying ` ps ` .  Notice that ` x `
     must not be a free variable in the antecedent of the quantified
     implication, and we express this by binding ` ph ` to "protect" the axiom
     from a ` ph ` containing a free ` x ` .  Axiom scheme C4' in [Megill]
     p. 448 (p. 16 of the preprint).  It is a special case of Lemma 5 of
     [Monk2] p. 108 and Axiom 5 of [Mendelson] p. 69.

     This axiom is obsolete and should no longer be used.  It is proved above
     as theorem ~ ax5o .  (Contributed by NM, 5-Aug-1993.)
     (New usage is discouraged.) $)
  ax-5o $a |- ( A. x ( A. x ph -> ps ) -> ( A. x ph -> A. x ps ) ) $.

  $( Axiom of Quantified Negation.  This axiom is used to manipulate negated
     quantifiers.  Equivalent to axiom scheme C7' in [Megill] p. 448 (p. 16 of
     the preprint).  An alternate axiomatization could use ~ ax467 in place of
     ~ ax-4 , ~ ax-6o , and ~ ax-7 .

     This axiom is obsolete and should no longer be used.  It is proved above
     as theorem ~ ax6o .  (Contributed by NM, 5-Aug-1993.)
     (New usage is discouraged.) $)
  ax-6o $a |- ( -. A. x -. A. x ph -> ph ) $.

  $( A variant of ~ ax9 .  Axiom scheme C10' in [Megill] p. 448 (p. 16 of the
     preprint).

     This axiom is obsolete and should no longer be used.  It is proved above
     as theorem ~ ax9o .  (Contributed by NM, 5-Aug-1993.)
     (New usage is discouraged.) $)
  ax-9o $a |- ( A. x ( x = y -> A. x ph ) -> ph ) $.

  $( Axiom ~ ax-10o ("o" for "old") was the original version of ~ ax-10 ,
     before it was discovered (in May 2008) that the shorter ~ ax-10 could
     replace it.  It appears as Axiom scheme C11' in [Megill] p. 448 (p. 16 of
     the preprint).

     This axiom is obsolete and should no longer be used.  It is proved above
     as theorem ~ ax10o .  (Contributed by NM, 5-Aug-1993.)
     (New usage is discouraged.) $)
  ax-10o $a |- ( A. x x = y -> ( A. x ph -> A. y ph ) ) $.

  $( Axiom of Quantifier Substitution.  One of the equality and substitution
     axioms of predicate calculus with equality.  Appears as Lemma L12 in
     [Megill] p. 445 (p. 12 of the preprint).

     The original version of this axiom was ~ ax-10o ("o" for "old") and was
     replaced with this shorter ~ ax-10 in May 2008.  The old axiom is proved
     from this one as theorem ~ ax10o .  Conversely, this axiom is proved from
     ~ ax-10o as theorem ~ ax10from10o .

     This axiom was proved redundant in July 2015.  See theorem ~ ax10 .

     This axiom is obsolete and should no longer be used.  It is proved above
     as theorem ~ ax10 .  (Contributed by NM, 16-May-2008.)
     (New usage is discouraged.) $)
  ax-10 $a |- ( A. x x = y -> A. y y = x ) $.

  $( Axiom ~ ax-11o ("o" for "old") was the original version of ~ ax-11 ,
     before it was discovered (in Jan. 2007) that the shorter ~ ax-11 could
     replace it.  It appears as Axiom scheme C15' in [Megill] p. 448 (p. 16 of
     the preprint).  It is based on Lemma 16 of [Tarski] p. 70 and Axiom C8 of
     [Monk2] p. 105, from which it can be proved by cases.  To understand this
     theorem more easily, think of " ` -. A. x x = y -> ` ..." as informally
     meaning "if ` x ` and ` y ` are distinct variables then..."  The
     antecedent becomes false if the same variable is substituted for ` x ` and
     ` y ` , ensuring the theorem is sound whenever this is the case.  In some
     later theorems, we call an antecedent of the form ` -. A. x x = y ` a
     "distinctor."

     Interestingly, if the wff expression substituted for ` ph ` contains no
     wff variables, the resulting statement _can_ be proved without invoking
     this axiom.  This means that even though this axiom is _metalogically_
     independent from the others, it is not _logically_ independent.
     Specifically, we can prove any wff-variable-free instance of axiom
     ~ ax-11o (from which the ~ ax-11 instance follows by theorem ~ ax11 .)
     The proof is by induction on formula length, using ~ ax11eq and ~ ax11el
     for the basis steps and ~ ax11indn , ~ ax11indi , and ~ ax11inda for the
     induction steps.  (This paragraph is true provided we use ~ ax-10o in
     place of ~ ax-10 .)

     This axiom is obsolete and should no longer be used.  It is proved above
     as theorem ~ ax11o .  (Contributed by NM, 5-Aug-1993.)
     (New usage is discouraged.) $)
  ax-11o $a |- ( -. A. x x = y ->
             ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) ) $.

  $( Axiom of Quantifier Introduction.  One of the equality and substitution
     axioms of predicate calculus with equality.  Informally, it says that
     whenever ` z ` is distinct from ` x ` and ` y ` , and ` x = y ` is true,
     then ` x = y ` quantified with ` z ` is also true.  In other words, ` z `
     is irrelevant to the truth of ` x = y ` .  Axiom scheme C9' in [Megill]
     p. 448 (p. 16 of the preprint).  It apparently does not otherwise appear
     in the literature but is easily proved from textbook predicate calculus by
     cases.

     This axiom is obsolete and should no longer be used.  It is proved above
     as theorem ~ ax12o .  (Contributed by NM, 5-Aug-1993.)
     (New usage is discouraged.) $)
  ax-12o $a |- ( -. A. z z = x -> ( -. A. z z = y ->
              ( x = y -> A. z x = y ) ) ) $.

  $( Axiom of Quantifier Introduction.  One of the equality and substitution
     axioms for a non-logical predicate in our predicate calculus with
     equality.  Axiom scheme C14' in [Megill] p. 448 (p. 16 of the preprint).
     It is redundant if we include ~ ax-17 ; see theorem ~ ax15 .  Alternately,
     ~ ax-17 becomes unnecessary in principle with this axiom, but we lose the
     more powerful metalogic afforded by ~ ax-17 .  We retain ~ ax-15 here to
     provide completeness for systems with the simpler metalogic that results
     from omitting ~ ax-17 , which might be easier to study for some
     theoretical purposes.

     This axiom is obsolete and should no longer be used.  It is proved above
     as theorem ~ ax15 .  (Contributed by NM, 5-Aug-1993.)
     (New usage is discouraged.) $)
  ax-15 $a |- ( -. A. z z = x -> ( -. A. z z = y ->
              ( x e. y -> A. z x e. y ) ) ) $.

  ${
    $d x y $.
    $( Axiom of Distinct Variables.  The only axiom of predicate calculus
       requiring that variables be distinct (if we consider ~ ax-17 to be a
       metatheorem and not an axiom).  Axiom scheme C16' in [Megill] p. 448 (p.
       16 of the preprint).  It apparently does not otherwise appear in the
       literature but is easily proved from textbook predicate calculus by
       cases.  It is a somewhat bizarre axiom since the antecedent is always
       false in set theory (see ~ dtru ), but nonetheless it is technically
       necessary as you can see from its uses.

       This axiom is redundant if we include ~ ax-17 ; see theorem ~ ax16 .
       Alternately, ~ ax-17 becomes logically redundant in the presence of this
       axiom, but without ~ ax-17 we lose the more powerful metalogic that
       results from being able to express the concept of a set variable not
       occurring in a wff (as opposed to just two set variables being
       distinct).  We retain ~ ax-16 here to provide logical completeness for
       systems with the simpler metalogic that results from omitting ~ ax-17 ,
       which might be easier to study for some theoretical purposes.

       This axiom is obsolete and should no longer be used.  It is proved above
       as theorem ~ ax16 .  (Contributed by NM, 5-Aug-1993.)
       (New usage is discouraged.) $)
    ax-16 $a |- ( A. x x = y -> ( ph -> A. x ph ) ) $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Rederive new axioms from old:  ax5 , ax6 , ax9from9o , ax11 , ax12from12o
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  Theorems ~ ax11 and ~ ax12from12o require some intermediate theorems that are
  included in this section.

$)

  $( This theorem repeats ~ sp under the name ~ ax4 , so that the metamath
     program's "verify markup" command will check that it matches axiom scheme
     ~ ax-4 .  It is preferred that references to this theorem use the name
     ~ sp .  (Contributed by NM, 18-Aug-2017.)  (New usage is discouraged.)
     (Proof modification is discouraged.) $)
  ax4 $p |- ( A. x ph -> ph ) $=
    ( sp ) ABC $.

  $( Rederivation of axiom ~ ax-5 from ~ ax-5o and other older axioms.  See
     ~ ax5o for the derivation of ~ ax-5o from ~ ax-5 .  (Contributed by NM,
     23-May-2008.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  ax5 $p |- ( A. x ( ph -> ps ) -> ( A. x ph -> A. x ps ) ) $=
    ( wi wal ax-5o ax-4 syl5 mpg syl ) ABDZCEZACEZBDZCEZMBCEDLNDLODCKNCFMALBACG
    KCGHIABCFJ $.

  $( Rederivation of axiom ~ ax-6 from ~ ax-6o and other older axioms.  See
     ~ ax6o for the derivation of ~ ax-6o from ~ ax-6 .  (Contributed by NM,
     23-May-2008.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  ax6 $p |- ( -. A. x ph -> A. x -. A. x ph ) $=
    ( wal wn wi ax-5o ax-4 id mpg nsyl ax-6o nsyl4 ) ABCZBCZDZBCZMDZBCZMPQEPREB
    OQBFPNMOBGMMEMNEBAMBFMHIJIMBKL $.

  $( Rederivation of axiom ~ ax-9 from ~ ax-9o and other older axioms.  See
     ~ ax9o for the derivation of ~ ax-9o from ~ ax-9 .  Lemma L18 in [Megill]
     p. 446 (p. 14 of the preprint).  (Contributed by NM, 5-Aug-1993.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  ax9from9o $p |- -. A. x -. x = y $=
    ( weq wn wal wi ax-9o ax-6o con4i mpg ) ABCZKDZAEDZAEZFMAMABGNKLAHIJ $.

  $( ` x ` is not free in ` A. x ph ` .  Example in Appendix in [Megill] p. 450
     (p. 19 of the preprint).  Also Lemma 22 of [Monk2] p. 114.  (Contributed
     by NM, 5-Aug-1993.)  (New usage is discouraged.) $)
  hba1-o $p |- ( A. x ph -> A. x A. x ph ) $=
    ( wal wn ax-4 con2i ax6 con1i alimi 3syl ) ABCZKDZBCZDZNBCKBCMKLBEFLBGNKBKM
    ABGHIJ $.

  ${
    a5i-o.1 $e |- ( A. x ph -> ps ) $.
    $( Inference version of ~ ax-5o .  (Contributed by NM, 5-Aug-1993.)
       (New usage is discouraged.) $)
    a5i-o $p |- ( A. x ph -> A. x ps ) $=
      ( wal hba1-o alrimih ) ACEBCACFDG $.
  $}

  $( Commutation law for identical variable specifiers.  The antecedent and
     consequent are true when ` x ` and ` y ` are substituted with the same
     variable.  Lemma L12 in [Megill] p. 445 (p. 12 of the preprint).  Version
     of ~ aecom using ~ ax-10o .  Unlike ~ ax10from10o , this version does not
     require ~ ax-17 .  (Contributed by NM, 5-Aug-1993.)
     (New usage is discouraged.) $)
  aecom-o $p |- ( A. x x = y -> A. y y = x ) $=
    ( weq wal ax-10o pm2.43i equcomi alimi syl ) ABCZADZJBDZBACZBDKLJABEFJMBABG
    HI $.

  ${
    alequcoms-o.1 $e |- ( A. x x = y -> ph ) $.
    $( A commutation rule for identical variable specifiers.  Version of
       ~ aecoms using ax-10o .  (Contributed by NM, 5-Aug-1993.)
       (New usage is discouraged.) $)
    aecoms-o $p |- ( A. y y = x -> ph ) $=
      ( weq wal aecom-o syl ) CBECFBCEBFACBGDH $.
  $}

  $( All variables are effectively bound in an identical variable specifier.
     Version of ~ hbae using ~ ax-10o .  (Contributed by NM, 5-Aug-1993.)
     (Proof modification is disccouraged.)  (New usage is discouraged.) $)
  hbae-o $p |- ( A. x x = y -> A. z A. x x = y ) $=
    ( weq wal wi wn ax-4 ax-12o syl7 ax-10o aecoms-o pm2.43i syl5 pm2.61ii ax-7
    a5i-o syl ) ABDZAEZSCEZAETCESUAACADCEZCBDCEZTUAFZTSUBGUCGUASAHABCIJUDACSACK
    LUDBCTSBEZBCDBEUATUESABKMSBCKNLOQSACPR $.

  ${
    dral1-o.1 $e |- ( A. x x = y -> ( ph <-> ps ) ) $.
    $( Formula-building lemma for use with the Distinctor Reduction Theorem.
       Part of Theorem 9.4 of [Megill] p. 448 (p. 16 of preprint).  Version of
       ~ dral1 using ~ ax-10o .  (Contributed by NM, 24-Nov-1994.)
       (New usage is discouraged.) $)
    dral1-o $p |- ( A. x x = y -> ( A. x ph <-> A. y ps ) ) $=
      ( weq wal hbae-o biimpd alimdh ax-10o syld biimprd wi aecoms-o impbid ) C
      DFCGZACGZBDGZQRBCGSQABCCDCHQABEIJBCDKLQSADGZRQBADCDDHQABEMJTRNDCADCKOLP
      $.
  $}

  $( Rederivation of axiom ~ ax-11 from ~ ax-11o , ~ ax-10o , and other older
     axioms.  The proof does not require ~ ax-16 or ~ ax-17 .  See theorem
     ~ ax11o for the derivation of ~ ax-11o from ~ ax-11 .

     An open problem is whether we can prove this using ~ ax-10 instead of
     ~ ax-10o .

     This proof uses newer axioms ~ ax-5 and ~ ax-9 , but since these are
     proved from the older axioms above, this is acceptable and lets us avoid
     having to reprove several earlier theorems to use ~ ax-5o and ~ ax-9o .
     (Contributed by NM, 22-Jan-2007.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  ax11 $p |- ( x = y -> ( A. y ph -> A. x ( x = y -> ph ) ) ) $=
    ( weq wal wi biidd dral1-o ax-1 alimi syl6bir a1d ax-4 ax-11o syl7 pm2.61i
    wn ) BCDZBEZRACEZRAFZBEZFZFSUCRSTABEUBAABCSAGHAUABARIJKLTASQRUBACMABCNOP $.

  $( Derive ~ ax-12 from ~ ax-12o and other older axioms.

     This proof uses newer axioms ~ ax-5 and ~ ax-9 , but since these are
     proved from the older axioms above, this is acceptable and lets us avoid
     having to reprove several earlier theorems to use ~ ax-5o and ~ ax-9o .
     (Contributed by NM, 21-Dec-2015.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  ax12from12o $p |- ( -. x = y -> ( y = z -> A. x y = z ) ) $=
    ( weq wn wal wi wa ax-4 con3i adantr equtrr equcoms con3rr3 imp nsyl ax-12o
    sylc ex pm2.43d ) ABDZEZBCDZUCAFZUBUCUCUDGZUBUCHZUAAFZEZACDZAFZEUEUBUHUCUGU
    AUAAIJKUFUIUJUBUCUIEUCUIUAUIUAGCBCBALMNOUIAIPBCAQRST $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
               Legacy theorems using obsolete axioms
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  These theorems were mostly intended to study properties of the older axiom
  schemes and are not useful outside of this section.  They should not be
  used outside of this section.  They may be deleted when they are deemed to no
  longer be of interest.

$)


  ${
    $d x ph $.
    $( Axiom to quantify a variable over a formula in which it does not occur.
       Axiom C5 in [Megill] p. 444 (p. 11 of the preprint).  Also appears as
       Axiom B6 (p. 75) of system S2 of [Tarski] p. 77 and Axiom C5-1 of
       [Monk2] p. 113.

       (This theorem simply repeats ~ ax-17 so that we can include the
       following note, which applies only to the obsolete axiomatization.)

       This axiom is _logically_ redundant in the (logically complete)
       predicate calculus axiom system consisting of ~ ax-gen , ~ ax-5o ,
       ~ ax-4 , ~ ax-7 , ~ ax-6o , ~ ax-8 , ~ ax-12o , ~ ax-9o , ~ ax-10o ,
       ~ ax-13 , ~ ax-14 , ~ ax-15 , ~ ax-11o , and ~ ax-16 : in that system,
       we can derive any instance of ~ ax-17 not containing wff variables by
       induction on formula length, using ~ ax17eq and ~ ax17el for the basis
       together ~ hbn , ~ hbal , and ~ hbim .  However, if we omit this axiom,
       our development would be quite inconvenient since we could work only
       with specific instances of wffs containing no wff variables - this axiom
       introduces the concept of a set variable not occurring in a wff (as
       opposed to just two set variables being distinct).  (Contributed by NM,
       19-Aug-2017.)  (New usage is discouraged.)  (Proof modification
       discouraged.) $)
    ax17o $p |- ( ph -> A. x ph ) $=
      ( ax-17 ) ABC $.
  $}

  $( Identity law for equality (reflexivity).  Lemma 6 of [Tarski] p. 68.  This
     is often an axiom of equality in textbook systems, but we don't need it as
     an axiom since it can be proved from our other axioms (although the proof,
     as you can see below, is not as obvious as you might think).  This proof
     uses only axioms without distinct variable conditions and thus requires no
     dummy variables.  A simpler proof, similar to Tarki's, is possible if we
     make use of ~ ax-17 ; see the proof of ~ equid .  See ~ equid1ALT for an
     alternate proof.  (Contributed by NM, 5-Aug-1993.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  equid1 $p |- x = x $=
    ( weq wal wn wi ax-5o ax-4 ax-12o sylc mpg ax-9o syl ax-6o pm2.61i ) AABZAC
    ZDZACZOROPEZACZORSERTEAQSAFRQQSQAGZUAAAAHIJOAAKLOAMN $.

  ${
    sps-o.1 $e |- ( ph -> ps ) $.
    $( Generalization of antecedent.  (Contributed by NM, 5-Aug-1993.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    sps-o $p |- ( A. x ph -> ps ) $=
      ( wal ax-4 syl ) ACEABACFDG $.
  $}

  $( Bound-variable hypothesis builder for ` x = x ` .  This theorem tells us
     that any variable, including ` x ` , is effectively not free in
     ` x = x ` , even though ` x ` is technically free according to the
     traditional definition of free variable.  (The proof does not use
     ~ ax-9o .)  (Contributed by NM, 13-Jan-2011.)  (Proof shortened by Wolf
     Lammen, 23-Mar-2014.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  hbequid $p |- ( x = x -> A. y x = x ) $=
    ( weq wal wi ax-12o ax-8 pm2.43i alimi a1d pm2.61ii ) BACZBDZMAACZNBDZEAABF
    MONLNBLNBAAGHIJZPK $.

  $( Bound-variable hypothesis builder for ` x = x ` .  This theorem tells us
     that any variable, including ` x ` , is effectively not free in
     ` x = x ` , even though ` x ` is technically free according to the
     traditional definition of free variable.  (The proof uses only ~ ax-5 ,
     ~ ax-8 , ~ ax-12o , and ~ ax-gen .  This shows that this can be proved
     without ~ ax9 , even though the theorem ~ equid cannot be.  A shorter
     proof using ~ ax9 is obtainable from ~ equid and ~ hbth .)  Remark added
     2-Dec-2015 NM:  This proof does implicitly use ~ ax9v , which is used for
     the derivation of ~ ax12o , unless we consider ~ ax-12o the starting axiom
     rather than ~ ax-12 .  (Contributed by NM, 13-Jan-2011.)  (Revised by
     Mario Carneiro, 12-Oct-2016.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  nfequid-o $p |- F/ y x = x $=
    ( weq hbequid nfi ) AACBABDE $.

  $( Proof of a single axiom that can replace ~ ax-4 and ~ ax-6o .  See
     ~ ax46to4 and ~ ax46to6 for the re-derivation of those axioms.
     (Contributed by Scott Fenton, 12-Sep-2005.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  ax46 $p |- ( ( A. x -. A. x ph -> A. x ph ) -> ph ) $=
    ( wal wn ax-6o ax-4 ja ) ABCZDBCHAABEABFG $.

  $( Re-derivation of ~ ax-4 from ~ ax46 .  Only propositional calculus is used
     for the re-derivation.  (Contributed by Scott Fenton, 12-Sep-2005.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  ax46to4 $p |- ( A. x ph -> ph ) $=
    ( wal wn wi ax-1 ax46 syl ) ABCZIDBCZIEAIJFABGH $.

  $( Re-derivation of ~ ax-6o from ~ ax46 .  Only propositional calculus is
     used for the re-derivation.  (Contributed by Scott Fenton, 12-Sep-2005.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  ax46to6 $p |- ( -. A. x -. A. x ph -> ph ) $=
    ( wal wn wi pm2.21 ax46 syl ) ABCZDBCZDJIEAJIFABGH $.

  $( Proof of a single axiom that can replace both ~ ax-6o and ~ ax-7 .  See
     ~ ax67to6 and ~ ax67to7 for the re-derivation of those axioms.
     (Contributed by NM, 18-Nov-2006.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  ax67 $p |- ( -. A. x -. A. y A. x ph -> A. y ph ) $=
    ( wal wn ax-7 con3i alimi ax-6o syl ) ABDCDZEZBDZEACDZBDZEZBDZENQMPLBKOACBF
    GHGNBIJ $.

  $( ` x ` is not free in ` A. x ph ` .  (Contributed by Mario Carneiro,
     11-Aug-2016.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  nfa1-o $p |- F/ x A. x ph $=
    ( wal hba1-o nfi ) ABCBABDE $.

  $( Re-derivation of ~ ax-6o from ~ ax67 .  Note that ~ ax-6o and ~ ax-7 are
     not used by the re-derivation.  (Contributed by NM, 18-Nov-2006.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  ax67to6 $p |- ( -. A. x -. A. x ph -> ph ) $=
    ( wal wn hba1-o con3i alimi ax67 ax-4 3syl ) ABCZDZBCZDKBCZDZBCZDKAPMOLBKNA
    BEFGFABBHABIJ $.

  $( Re-derivation of ~ ax-7 from ~ ax67 .  Note that ~ ax-6o and ~ ax-7 are
     not used by the re-derivation.  (Contributed by NM, 18-Nov-2006.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  ax67to7 $p |- ( A. x A. y ph -> A. y A. x ph ) $=
    ( wal wn ax67to6 con4i ax67 alimi syl ) ACDBDZKEZCDEZCDZABDZCDNKLCFGMOCACBH
    IJ $.

  $( Proof of a single axiom that can replace ~ ax-4 , ~ ax-6o , and ~ ax-7 in
     a subsystem that includes these axioms plus ~ ax-5o and ~ ax-gen (and
     propositional calculus).  See ~ ax467to4 , ~ ax467to6 , and ~ ax467to7 for
     the re-derivation of those axioms.  This theorem extends the idea in Scott
     Fenton's ~ ax46 .  (Contributed by NM, 18-Nov-2006.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  ax467 $p |- ( ( A. x A. y -. A. x A. y ph -> A. x ph ) -> ph ) $=
    ( wal wn ax-4 ax6 ax-6o con1i alimi ax-7 3syl nsyl4 ja ) ACDZBDEZCDBDZABDAO
    AQACFOEZRCDPBDZCDQACGRSCSOOBHIJPCBKLMABFN $.

  $( Re-derivation of ~ ax-4 from ~ ax467 .  Only propositional calculus is
     used by the re-derivation.  (Contributed by NM, 19-Nov-2006.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  ax467to4 $p |- ( A. x ph -> ph ) $=
    ( wal wn wi ax-1 ax467 syl ) ABCZIBCDBCBCZIEAIJFABBGH $.

  $( Re-derivation of ~ ax-6o from ~ ax467 .  Note that ~ ax-6o and ~ ax-7 are
     not used by the re-derivation.  The use of ~ alimi (which uses ~ ax-4 ) is
     allowed since we have already proved ~ ax467to4 .  (Contributed by NM,
     19-Nov-2006.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  ax467to6 $p |- ( -. A. x -. A. x ph -> ph ) $=
    ( wal wn wi hba1-o con3i alimi sps-o pm2.21 ax467 3syl ) ABCZDZBCZDMBCZDZBC
    ZBCZDSMEASOROBQNBMPABFGHIGSMJABBKL $.

  $( Re-derivation of ~ ax-7 from ~ ax467 .  Note that ~ ax-6o and ~ ax-7 are
     not used by the re-derivation.  The use of ~ alimi (which uses ~ ax-4 ) is
     allowed since we have already proved ~ ax467to4 .  (Contributed by NM,
     19-Nov-2006.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  ax467to7 $p |- ( A. x A. y ph -> A. y A. x ph ) $=
    ( wal wn ax467to6 con4i wi pm2.21 ax467 syl alimi nsyl4 ) ACDBDZNEZCDZEZCDZ
    ABDZCDRNOCFGQSCPBDZEZBDSPUAABUATSHATSIABCJKLPBFMLK $.

  $( ~ equid with existential quantifier without using ~ ax-4 or ~ ax-17 .
     (Contributed by NM, 13-Jan-2011.)  (Proof shortened by Wolf Lammen,
     27-Feb-2014.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  equidqe $p |- -. A. y -. x = x $=
    ( weq wn wal ax9from9o ax-8 pm2.43i con3i alimi mto ) AACZDZBEBACZDZBEBAFMO
    BNLNLBAAGHIJK $.

  $( A special case of ~ ax-4 without using ~ ax-4 or ~ ax-17 .  (Contributed
     by NM, 13-Jan-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  ax4sp1 $p |- ( A. y -. x = x -> -. x = x ) $=
    ( weq wn wal equidqe pm2.21i ) AACDZBEHABFG $.

  $( ~ equid with universal quantifier without using ~ ax-4 or ~ ax-17 .
     (Contributed by NM, 13-Jan-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  equidq $p |- A. y x = x $=
    ( weq wal wn equidqe ax6 hbequid con3i alrimih mt3 ) AACZBDZLEZBDABFMENBLBG
    LMABHIJK $.

  $( Identity law for equality (reflexivity).  Lemma 6 of [Tarski] p. 68.
     Alternate proof of ~ equid1 from older axioms ~ ax-6o and ~ ax-9o .
     (Contributed by NM, 5-Aug-1993.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  equid1ALT $p |- x = x $=
    ( weq wal wn wi ax-12o pm2.43i alimi ax-9o syl ax-6o pm2.61i ) AABZACZDZACZ
    MPMNEZACMOQAOQAAAFGHMAAIJMAKL $.

  $( Rederivation of ~ ax-10 from original version ~ ax-10o .  See theorem
     ~ ax10o for the derivation of ~ ax-10o from ~ ax-10 .

     This theorem should not be referenced in any proof.  Instead, use ~ ax-10
     above so that uses of ~ ax-10 can be more easily identified, or use
     ~ aecom-o when this form is needed for studies involving ~ ax-10o and
     omitting ~ ax-17 .  (Contributed by NM, 16-May-2008.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  ax10from10o $p |- ( A. x x = y -> A. y y = x ) $=
    ( weq wal ax-10o pm2.43i equcomi alimi syl ) ABCZADZJBDZBACZBDKLJABEFJMBABG
    HI $.

  ${
    nalequcoms-o.1 $e |- ( -. A. x x = y -> ph ) $.
    $( A commutation rule for distinct variable specifiers.  Version of
       ~ naecoms using ~ ax-10o .  (Contributed by NM, 2-Jan-2002.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    naecoms-o $p |- ( -. A. y y = x -> ph ) $=
      ( weq wal aecom-o nsyl4 con1i ) ACBECFZBCEBFJABCGDHI $.
  $}

  $( All variables are effectively bound in a distinct variable specifier.
     Lemma L19 in [Megill] p. 446 (p. 14 of the preprint).  Version of ~ hbnae
     using ~ ax-10o .  (Contributed by NM, 5-Aug-1993.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  hbnae-o $p |- ( -. A. x x = y -> A. z -. A. x x = y ) $=
    ( weq wal hbae-o hbn ) ABDAECABCFG $.

  ${
    dvelimf-o.1 $e |- ( ph -> A. x ph ) $.
    dvelimf-o.2 $e |- ( ps -> A. z ps ) $.
    dvelimf-o.3 $e |- ( z = y -> ( ph <-> ps ) ) $.
    $( Proof of ~ dvelimh that uses ~ ax-10o but not ~ ax-11o , ~ ax-10 , or
       ~ ax-11 .  Version of ~ dvelimh using ~ ax-10o instead of ~ ax10o .
       (Contributed by NM, 12-Nov-2002.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    dvelimf-o $p |- ( -. A. x x = y -> ( ps -> A. x ps ) ) $=
      ( weq wal wn wi hba1-o ax-10o aecoms-o syl5 a1d wa hbnae-o hban imp hbimd
      ax-12o a1i hbald ex pm2.61i equsalh albii 3imtr3g ) CDICJKZEDIZALZEJZUNCJ
      ZBBCJCEICJZUKUNUOLZLUPUQUKUNUNEJZUPUOUMEMURUOLECUNECNOPQUPKZUKUQUSUKRZUMC
      EUSUKECEESCDESTUTULACUSUKCCECSCDCSTUSUKULULCJLEDCUCUAAACJLUTFUDUBUEUFUGAB
      EDGHUHZUNBCVAUIUJ $.
  $}

  ${
    dral2-o.1 $e |- ( A. x x = y -> ( ph <-> ps ) ) $.
    $( Formula-building lemma for use with the Distinctor Reduction Theorem.
       Part of Theorem 9.4 of [Megill] p. 448 (p. 16 of preprint).  Version of
       ~ dral2 using ~ ax-10o .  (Contributed by NM, 27-Feb-2005.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    dral2-o $p |- ( A. x x = y -> ( A. z ph <-> A. z ps ) ) $=
      ( weq wal hbae-o albidh ) CDGCHABECDEIFJ $.
  $}

  ${
    $d t u v $.  $d t u x y $.  $d u w $.
    $( A "distinctor elimination" lemma with no restrictions on variables in
       the consequent, proved without using ~ ax-16 .  Version of ~ aev using
       ~ ax-10o .  (Contributed by NM, 8-Nov-2006.)  (Proof shortened by Andrew
       Salmon, 21-Jun-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    aev-o $p |- ( A. x x = y -> A. z w = v ) $=
      ( vt vu weq hbae-o ax-8 spimv alrimih equcomi syl6 aecoms-o a5i-o aecom-o
      wal 3syl ) ABHZARZDEHZCABCIUAFBHZFRZGEHZGRZUBUAUCFABFITUCAFAFBJKLUDFGHZFR
      ZEGHZERUFUCUGFUGBFBFHZUGBGBGHUJGFHUGBGFJGFMNKOPUHUIEFGEIUGUIFEFEGJKLEGQSU
      EUBGDGDEJKSL $.
  $}

  ${
    $d x z $.  $d y z $.
    $( Theorem to add distinct quantifier to atomic formula.  (This theorem
       demonstrates the induction basis for ~ ax-17 considered as a
       metatheorem.  Do not use it for later proofs - use ~ ax-17 instead, to
       avoid reference to the redundant axiom ~ ax-16 .)  (Contributed by NM,
       5-Aug-1993.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    ax17eq $p |- ( x = y -> A. z x = y ) $=
      ( weq wal wi ax-12o ax-16 pm2.61ii ) CADCECBDCEABDZJCEFABCGJCAHJCBHI $.
  $}

  ${
    $d w z x $.  $d w y $.
    $( Quantifier introduction when one pair of variables is distinct.  Version
       of ~ dveeq2 using ~ ax-11o .  (Contributed by NM, 2-Jan-2002.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    dveeq2-o $p |- ( -. A. x x = y -> ( z = y -> A. x z = y ) ) $=
      ( vw weq ax-17 equequ2 dvelimf-o ) CDEZCBEZABDIAFJDFDBCGH $.

    $( Version of ~ dveeq2 using ~ ax-16 instead of ~ ax-17 .  TO DO:  Recover
       proof from older set.mm to remove use of ~ ax-17 .  (Contributed by NM,
       29-Apr-2008.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    dveeq2-o16 $p |- ( -. A. x x = y -> ( z = y -> A. x z = y ) ) $=
      ( vw weq ax17eq equequ2 dvelimALT ) CDECBEABDCDAFDBCGH $.
  $}

  ${
    $d x y $.
    $( A generalization of axiom ~ ax-16 .  Version of ~ a16g using ~ ax-10o .
       (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Andrew Salmon,
       25-May-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    a16g-o $p |- ( A. x x = y -> ( ph -> A. z ph ) ) $=
      ( weq wal aev-o ax-16 biidd dral1-o biimprd sylsyld ) BCEBFDBEDFZAABFZADF
      ZBCDDBGABCHMONAADBMAIJKL $.
  $}

  ${
    $d w z x $.  $d w y $.
    $( Quantifier introduction when one pair of variables is distinct.  Version
       of ~ dveeq1 using ax-10o .  (Contributed by NM, 2-Jan-2002.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    dveeq1-o $p |- ( -. A. x x = y -> ( y = z -> A. x y = z ) ) $=
      ( vw weq ax-17 equequ1 dvelimf-o ) DCEZBCEZABDIAFJDFDBCGH $.

    $( Version of ~ dveeq1 using ~ ax-16 instead of ~ ax-17 .  (Contributed by
       NM, 29-Apr-2008.)  TO DO:  Recover proof from older set.mm to remove use
       of ~ ax-17 .  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    dveeq1-o16 $p |- ( -. A. x x = y -> ( y = z -> A. x y = z ) ) $=
      ( vw weq ax17eq equequ1 dvelimh ) DCEBCEABDDCAFBCDFDBCGH $.
  $}

  ${
    $d x z $.  $d y z $.
    $( Theorem to add distinct quantifier to atomic formula.  This theorem
       demonstrates the induction basis for ~ ax-17 considered as a
       metatheorem.)  (Contributed by NM, 5-Aug-1993.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    ax17el $p |- ( x e. y -> A. z x e. y ) $=
      ( weq wal wel wi ax-15 ax-16 pm2.61ii ) CADCECBDCEABFZKCEGABCHKCAIKCBIJ
      $.
  $}

  ${
    $d x z w $.
    $( This theorem shows that, given ~ ax-16 , we can derive a version of
       ~ ax-10 .  However, it is weaker than ~ ax-10 because it has a distinct
       variable requirement.  (Contributed by Andrew Salmon, 27-Jul-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    ax10-16 $p |- ( A. x x = z -> A. z z = x ) $=
      ( vw weq wal ax-16 alrimiv a5i-o equequ1 cbvalv a1i imbi12d albidv biimpi
      wi wb wex nfa1-o 19.23 a7s albii pm2.27 ax-mp alimi equequ2 spv sps-o syl
      a9ev sylbi 3syl ) ABDZAEZACDZUNAEZOZCEZAEZBCDZUSBEZOZCEZBEZBADZBEULUQAUMU
      PCUNABFGHURVCUQVBABULUPVACULUNUSUOUTABCIZUOUTPULUNUSABVEJKLMJNVBVDBVAVDCB
      VABEZCEUSBQZUTOZCEZVDVFVHCUSUTBUSBRSUAVIUTCEVDVHUTCVGVHUTOBCUIVGUTUBUCUDU
      SVDBCUSCEVDBUSVDCACABUEUFUGTUHUJTHUK $.
  $}

  ${
    $d w z x $.  $d w y $.
    $( Version of ~ dveel2 using ~ ax-16 instead of ~ ax-17 .  (Contributed by
       NM, 10-May-2008.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    dveel2ALT $p |- ( -. A. x x = y -> ( z e. y -> A. x z e. y ) ) $=
      ( vw wel ax17el elequ2 dvelimh ) CDECBEABDCDAFCBDFDBCGH $.
  $}

  ${
    ax11f.1 $e |- ( ph -> A. x ph ) $.
    $( Basis step for constructing a substitution instance of ~ ax-11o without
       using ~ ax-11o .  We can start with any formula ` ph ` in which ` x ` is
       not free.  (Contributed by NM, 21-Jan-2007.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    ax11f $p |- ( -. A. x x = y ->
               ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) ) $=
      ( weq wal wn wi ax-1 alrimih a1ii ) BCEZBFGLALAHZBFHAMBDALIJK $.
  $}

  ${
    $d x u v $.  $d y u v $.  $d z u v $.  $d w u v $.
    $( Basis step for constructing a substitution instance of ~ ax-11o without
       using ~ ax-11o .  Atomic formula for equality predicate.  (Contributed
       by NM, 22-Jan-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    ax11eq $p |- ( -. A. x x = y ->
               ( x = y -> ( z = w -> A. x ( x = y -> z = w ) ) ) ) $=
      ( vu vv weq wal wn wi wa 19.26 a1i wb equequ1 equequ2 sps-o imbi12d exp32
      imbi2d equid ax-gen sylan9bb nfa1-o adantr sylbir ad2antll impcom adantrr
      albid mpbii ax12o equtrr alimi syl6 sylbid adantll dral2-o ad2antrr mpbid
      imp biimprcd adantlr ad2antlr wex alrimiv adantl dveeq2-o im2anan9 sylibr
      a9ev ax-1 syl exlimdv mpi a1d 4cases ) ACGZAHZADGZAHZABGZAHIZWBCDGZWBWDJZ
      AHZJZJZJZVSWAKVRVTKZAHZWIVRVTALWKWCWBWGWKWCWBKZKAAGZWBWMJZAHZJZWGWOWMWNAW
      MWBAUAMUBMWKWPWGNWLWKWMWDWOWFWJWMWDNAVRWMCAGZVTWDACAOADCPZUCQZWKWNWEAWJAU
      DWKWMWDWBWSTUJRUEUKSUFVSWAIZKZWCWBWGXAWLKVTWBVTJZAHZJZWGWTWLXDVSWTWLKZVTB
      DGZXCWBVTXFNWTWCABDOUGXEXFXFAHZXCWTWCXFXGJZWBWCWTXHBDAULUHUIXFXBABDAUMUNU
      OUPUQVSXDWGNWTWLVSVTWDXCWFVRVTWDNAACDOQZXBWEACAVSVTWDWBXITURRUSUTSVSIZWAK
      ZWCWBWGXKWLKWQWBWQJZAHZJZWGXJWLXNWAXJWLKZWQCBGZXMWBWQXPNXJWCABCPZUGXOXPXP
      AHZXMXJWCXPXRJZWBXJWCXSCBAULVAUIXPXLAWBWQXPXQVBUNUOUPVCWAXNWGNXJWLWAWQWDX
      MWFVTWQWDNAWRQZXLWEADAWAWQWDWBXTTURRVDUTSXJWTKZWHWCYAWGWBYAEDGZEVEWGEDVKY
      AYBWGEYAFCGZFVEYBWGJZFCVKYAYCYDFYAYCYBWGYAYCYBKZKZFEGZWBYGJZAHZJWGYGYHAYG
      WBVLVFYFYGWDYIWFYEYGWDNZYAYCYGCEGYBWDFCEOEDCPUCZVGYFYEAHZYIWFNYFYCAHZYBAH
      ZKZYLYAYEYOXJYCYMWTYBYNACFVHADEVHVIVAYCYBALVJYLYHWEAYEAUDYLYGWDWBYEYJAYKQ
      TUJVMRUKSVNVOVNVOVPVPVQ $.
  $}

  ${
    $d x u v $.  $d y u v $.  $d z u v $.  $d w u v $.
    $( Basis step for constructing a substitution instance of ~ ax-11o without
       using ~ ax-11o .  Atomic formula for membership predicate.  (Contributed
       by NM, 22-Jan-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    ax11el $p |- ( -. A. x x = y ->
               ( x = y -> ( z e. w -> A. x ( x = y -> z e. w ) ) ) ) $=
      ( vv vu weq wal wn wel wi wa wb elequ1 elequ2 adantl sps-o imbi2d imbi12d
      exp32 19.26 bitrd ax-17 biimprcd alimi syl6 adantr sylbid sylan9bb nfa1-o
      albid mpbid sylbir ad2antll ax-15 impcom adantrr adantll dral2-o ad2antrr
      dvelimf-o imp adantlr ad2antlr a9ev ax-1 alrimiv dveeq2-o im2anan9 sylibr
      wex syl mpbii exlimdv mpi a1d 4cases ) ACGZAHZADGZAHZABGZAHIZWBCDJZWBWDKZ
      AHZKZKZKZVSWALVRVTLZAHZWIVRVTAUAWKWCWBWGWKWCWBLZLAAJZWBWMKZAHZKZWGWLWPWKW
      LWMBBJZWOWBWMWQMWCWBWMBAJWQABANABBOUBZPWCWQWOKWBWCWQWQAHWOEEJZWQABEWSAUCW
      QEUCEBGWSBEJWQEBENEBBOUBVAWQWNAWBWMWQWRUDUEUFUGUHPWKWPWGMWLWKWMWDWOWFWJWM
      WDMAVRWMCAJZVTWDACANADCOZUIQZWKWNWEAWJAUJWKWMWDWBXBRUKSUGULTUMVSWAIZLZWCW
      BWGXDWLLADJZWBXEKZAHZKZWGXCWLXHVSXCWLLZXEBDJZXGWBXEXJMXCWCABDNZUNXIXJXJAH
      ZXGXCWCXJXLKZWBWCXCXMBDAUOUPUQXJXFAWBXEXJXKUDUEUFUHURVSXHWGMXCWLVSXEWDXGW
      FVRXEWDMAACDNQZXFWEACAVSXEWDWBXNRUSSUTULTVSIZWALZWCWBWGXPWLLWTWBWTKZAHZKZ
      WGXOWLXSWAXOWLLZWTCBJZXRWBWTYAMXOWCABCOZUNXTYAYAAHZXRXOWCYAYCKZWBXOWCYDCB
      AUOVBUQYAXQAWBWTYAYBUDUEUFUHVCWAXSWGMXOWLWAWTWDXRWFVTWTWDMAXAQZXQWEADAWAW
      TWDWBYERUSSVDULTXOXCLZWHWCYFWGWBYFFDGZFVKWGFDVEYFYGWGFYFECGZEVKYGWGKZECVE
      YFYHYIEYFYHYGWGYFYHYGLZLZEFJZWBYLKZAHZKWGYLYMAYLWBVFVGYKYLWDYNWFYJYLWDMZY
      FYHYLCFJYGWDECFNFDCOUIZPYKYJAHZYNWFMYKYHAHZYGAHZLZYQYFYJYTXOYHYRXCYGYSACE
      VHADFVHVIVBYHYGAUAVJYQYMWEAYJAUJYQYLWDWBYJYOAYPQRUKVLSVMTVNVOVNVOVPVPVQ
      $.
  $}

  ${
    ax11indn.1 $e |- ( -. A. x x = y ->
               ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) ) $.
    $( Induction step for constructing a substitution instance of ~ ax-11o
       without using ~ ax-11o .  Negation case.  (Contributed by NM,
       21-Jan-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    ax11indn $p |- ( -. A. x x = y ->
               ( x = y -> ( -. ph -> A. x ( x = y -> -. ph ) ) ) ) $=
      ( weq wal wn wi wa 19.8a exanali hbn1 con3 syl6 com23 alrimdh syl5bi syl5
      wex exp3a ) BCEZBFGZUAAGZUAUCHZBFZUAUCIZUFBSZUBUEUFBJUGUAAHZBFZGZUBUEUAAB
      KUBUJUDBUABLUHBLUBUAUJUCUBUAAUIHUJUCHDAUIMNOPQRT $.

    ${
      ax11indi.2 $e |- ( -. A. x x = y ->
                 ( x = y -> ( ps -> A. x ( x = y -> ps ) ) ) ) $.
      $( Induction step for constructing a substitution instance of ~ ax-11o
         without using ~ ax-11o .  Implication case.  (Contributed by NM,
         21-Jan-2007.)  (Proof modification is discouraged.)
         (New usage is discouraged.) $)
      ax11indi $p |- ( -. A. x x = y ->
           ( x = y -> ( ( ph -> ps ) -> A. x ( x = y -> ( ph -> ps ) ) ) ) ) $=
        ( weq wal wn wi wa ax11indn imp pm2.21 imim2i alimi syl6 ax-1 jad ex )
        CDGZCHIZUAABJZUAUCJZCHZJUBUAKZABUEUFAIZUAUGJZCHZUEUBUAUGUIJACDELMUHUDCU
        GUCUAABNOPQUFBUABJZCHZUEUBUABUKJFMUJUDCBUCUABAROPQST $.
    $}
  $}

  ${
    ax11indalem.1 $e |- ( -. A. x x = y ->
               ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) ) $.
    $( Lemma for ~ ax11inda2 and ~ ax11inda .  (Contributed by NM,
       24-Jan-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    ax11indalem $p |- ( -. A. y y = z -> ( -. A. x x = y ->
               ( x = y -> ( A. z ph -> A. x ( x = y -> A. z ph ) ) ) ) ) $=
      ( weq wal wn wi ax-1 a5i-o a1i biidd a1d aecom-o con3i imp hbnae-o hban
      wa dral1-o imbi2d dral2-o 3imtr4d adantr simplr ax12o syl2an adantlr ax-4
      aecoms-o hba1-o sylan2 alimdh syl2anc ax-7 wb nfdh 19.21t albidh ad2antrr
      wnf syl syl5ib syld exp31 pm2.61ian ) BDFBGZCDFCGZHZBCFZBGHZVKADGZVKVMIZB
      GZIZIZIZVHVRVJVHVQVLVHVPVKVPDBDBFDGZABGZVKVTIZBGZVMVOVTWBIVSAWABVTVKJKLAA
      DBVSAMUAZVNWADBBVSVMVTVKWCUBUCUDUKNNUEVHHZVJTZVLVKVPWEVLTVKTZVMVKAIZBGZDG
      ZVOWFVLVKDGZVMWIIWEVLVKUFWEVKWJVLWEVKWJWDVSHZDCFDGZHZVKWJIZVJVSVHDBOPWLVI
      DCOPWKWMWNBCDUGQUHZQUIVLWJTAWHDVLWJDBCDRVKDULSWJVLVKAWHIZVKDUJVLVKWPEQUMU
      NUOWEWIVOIVLVKWIWGDGZBGWEVOWGDBUPWEWQVNBWDVJBBDBRCDBRSWEVKDVBWQVNUQWEVKDW
      DVJDBDDRCDDRSWOURVKADUSVCUTVDVAVEVFVG $.
  $}

  ${
    $d z y $.
    ax11inda2.1 $e |- ( -. A. x x = y ->
               ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) ) $.
    $( A proof of ~ ax11inda2 that is slightly more direct.  (Contributed by
       NM, 4-May-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    ax11inda2ALT $p |- ( -. A. x x = y ->
               ( x = y -> ( A. z ph -> A. x ( x = y -> A. z ph ) ) ) ) $=
      ( weq wal wn wi a5i-o a1i biidd dral1-o imbi2d dral2-o a1d wa imp hbnae-o
      ax-1 3imtr4d aecoms-o simplr dveeq1-o naecoms-o hba1-o hban sylan2 alimdh
      adantlr ax-4 syl2anc ax-7 wnf nfdh 19.21t syl albidh syl5ib ad2antrr syld
      wb exp31 pm2.61i ) BDFBGZBCFZBGHZVFADGZVFVHIZBGZIZIZIVEVLVGVEVKVFVKDBDBFD
      GZABGZVFVNIZBGZVHVJVNVPIVMAVOBVNVFTJKAADBVMALMZVIVODBBVMVHVNVFVQNOUAUBPPV
      EHZVGVFVKVRVGQVFQZVHVFAIZBGZDGZVJVSVGVFDGZVHWBIVRVGVFUCVRVFWCVGVRVFWCVFWC
      IDBDBCUDUEZRUJVGWCQAWADVGWCDBCDSVFDUFUGWCVGVFAWAIZVFDUKVGVFWEERUHUIULVRWB
      VJIVGVFWBVTDGZBGVRVJVTDBUMVRWFVIBBDBSVRVFDUNWFVIVBVRVFDBDDSWDUOVFADUPUQUR
      USUTVAVCVD $.

    $( Induction step for constructing a substitution instance of ~ ax-11o
       without using ~ ax-11o .  Quantification case.  When ` z ` and ` y ` are
       distinct, this theorem avoids the dummy variables needed by the more
       general ~ ax11inda .  (Contributed by NM, 24-Jan-2007.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    ax11inda2 $p |- ( -. A. x x = y ->
               ( x = y -> ( A. z ph -> A. x ( x = y -> A. z ph ) ) ) ) $=
      ( weq wal wn wi ax-1 a16g-o syl5 a1d ax11indalem pm2.61i ) CDFCGZBCFZBGHZ
      QADGZQSIZBGZIZIZIPUCRPUBQSTPUASQJTCDBKLMMABCDENO $.
  $}

  ${
    $d w ph $.  $d w x $.  $d w y $.  $d w z $.
    ax11inda.1 $e |- ( -. A. x x = w ->
               ( x = w -> ( ph -> A. x ( x = w -> ph ) ) ) ) $.
    $( Induction step for constructing a substitution instance of ~ ax-11o
       without using ~ ax-11o .  Quantification case.  (When ` z ` and ` y `
       are distinct, ~ ax11inda2 may be used instead to avoid the dummy
       variable ` w ` in the proof.)  (Contributed by NM, 24-Jan-2007.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    ax11inda $p |- ( -. A. x x = y ->
               ( x = y -> ( A. z ph -> A. x ( x = y -> A. z ph ) ) ) ) $=
      ( weq wal wn wi wex a9ev wa ax11inda2 wb dveeq2-o imp albidh syl imbi12d
      hba1-o equequ2 sps-o notbid adantl imbi1d imbi2d mpbii ex exlimdv pm2.43i
      mpi ) BCGZBHZIZUMADHZUMUPJZBHZJZJZUOECGZEKUOUTJZECLUOVAVBEUOVAVBUOVAMZBEG
      ZBHZIZVDUPVDUPJZBHZJZJZJVBABEDFNVCVFUOVJUTVCVABHZVFUOOUOVAVKBCEPQZVKVEUNV
      KVDUMBVABUAZVAVDUMOZBECBUBZUCZRUDSVCVDUMVIUSVAVNUOVOUEVCVHURUPVCVKVHUROVL
      VKVGUQBVMVKVDUMUPVPUFRSUGTTUHUIUJULUK $.
  $}

  ${
    $d x z $.  $d y z $.  $d z ph $.
    ax11v2-o.1 $e |- ( x = z -> ( ph -> A. x ( x = z -> ph ) ) ) $.
    $( Recovery of ~ ax-11o from ~ ax11v without using ~ ax-11o .  The
       hypothesis is even weaker than ~ ax11v , with ` z ` both distinct from
       ` x ` _and_ not occurring in ` ph ` .  Thus, the hypothesis provides an
       alternate axiom that can be used in place of ~ ax-11o .  (Contributed by
       NM, 2-Feb-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    ax11v2-o $p |- ( -. A. x x = y ->
                 ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) ) $=
      ( weq wal wn wex wi wa wb equequ2 adantl dveeq2-o imp nfa1-o imbi1d sps-o
      a9ev albid syl imbi2d imbi12d mpbii ex exlimdv mpi ) BCFZBGHZDCFZDIUIAUIA
      JZBGZJZJZDCTUJUKUODUJUKUOUJUKKZBDFZAUQAJZBGZJZJUOEUPUQUIUTUNUKUQUILUJDCBM
      ZNUPUSUMAUPUKBGZUSUMLUJUKVBBCDOPVBURULBUKBQUKURULLBUKUQUIAVARSUAUBUCUDUEU
      FUGUH $.
  $}

  ${
    $d x z $.  $d y z $.  $d z ph $.
    ax11a2-o.1 $e |- ( x = z -> ( A. z ph -> A. x ( x = z -> ph ) ) ) $.
    $( Derive ~ ax-11o from a hypothesis in the form of ~ ax-11 , without using
       ~ ax-11 or ~ ax-11o .  The hypothesis is even weaker than ~ ax-11 , with
       ` z ` both distinct from ` x ` and not occurring in ` ph ` .  Thus, the
       hypothesis provides an alternate axiom that can be used in place of
       ~ ax-11 , if we also hvae ~ ax-10o which this proof uses .  As theorem
       ~ ax11 shows, the distinct variable conditions are optional.  An open
       problem is whether we can derive this with ~ ax-10 instead of
       ~ ax-10o .  (Contributed by NM, 2-Feb-2007.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    ax11a2-o $p |- ( -. A. x x = y ->
                 ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) ) $=
      ( wal weq wi ax-17 syl5 ax11v2-o ) ABCDAADFBDGZLAHBFADIEJK $.
  $}

  $( Show that ~ ax-10o can be derived from ~ ax-10 .  An open problem is
     whether this theorem can be derived from ~ ax-10 and the others when
     ~ ax-11 is replaced with ~ ax-11o .  See theorem ~ ax10from10o for the
     rederivation of ~ ax-10 from ~ ax10o .

     Normally, ~ ax10o should be used rather than ~ ax-10o or ~ ax10o-o ,
     except by theorems specifically studying the latter's properties.
     (Contributed by NM, 16-May-2008.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  ax10o-o $p |- ( A. x x = y -> ( A. x ph -> A. y ph ) ) $=
    ( weq wal wi ax-10 ax11 equcoms sps-o pm2.27 al2imi sylsyld ) BCDZBECBDZCEA
    BEZOAFZCEZACEBCGNPRFZBSCBACBHIJOQACOAKLM $.

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
               Existential uniqueness
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
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
       Note that ` y ` and ` z ` needn't be distinct variables.  See
       ~ eujustALT for a proof that provides an example of how it can be
       achieved through the use of ~ dvelim .  (Contributed by NM,
       11-Mar-2010.)  (Proof shortened by Andrew Salmon, 9-Jul-2011.) $)
    eujust $p |- ( E. y A. x ( ph <-> x = y )
        <-> E. z A. x ( ph <-> x = z ) ) $=
      ( vw weq wb wal wex equequ2 bibi2d albidv cbvexv bitri ) ABCFZGZBHZCIABEF
      ZGZBHZEIABDFZGZBHZDIQTCECEFZPSBUDORACEBJKLMTUCEDEDFZSUBBUERUAAEDBJKLMN $.

    $( A soundness justification theorem for ~ df-eu , showing that the
       definition is equivalent to itself with its dummy variable renamed.
       Note that ` y ` and ` z ` needn't be distinct variables.  While this
       isn't strictly necessary for soundness, the proof provides an example of
       how it can be achieved through the use of ~ dvelim .  (Contributed by
       NM, 11-Mar-2010.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    eujustALT $p |- ( E. y A. x ( ph <-> x = y )
        <-> E. z A. x ( ph <-> x = z ) ) $=
      ( vw weq wal wb wex equequ2 bibi2d albidv wn hbnae wi ax-17 notbid dvelim
      sps df-ex drex1 alrimih naecoms a1i cbv2h syl 3bitr4g pm2.61i ) CDFZCGZAB
      CFZHZBGZCIZABDFZHZBGZDIZHUMUQCDUIUMUQHCUIULUPBUIUKUOACDBJKLZSUAUJMZUMMZCG
      ZMUQMZDGZMUNURUTVBVDUTUTDGZCGVBVDHUTVECCDCNCDDNUBUTVAVCCDVAVADGODCABEFZHZ
      BGZMZVADCEVIDPECFZVHUMVJVGULBVJVFUKAECBJKLQRUCVIVCCDEVICPEDFZVHUQVKVGUPBV
      KVFUOAEDBJKLQRUIVAVCHOUTUIUMUQUSQUDUEUFQUMCTUQDTUGUH $.
  $}

  ${
    $d x y $.  $d y ph $.
    $( Define existential uniqueness, i.e.  "there exists exactly one ` x `
       such that ` ph ` ."  Definition 10.1 of [BellMachover] p. 97; also
       Definition *14.02 of [WhiteheadRussell] p. 175.  Other possible
       definitions are given by ~ eu1 , ~ eu2 , ~ eu3 , and ~ eu5 (which in
       some cases we show with a hypothesis ` ph -> A. y ph ` in place of a
       distinct variable condition on ` y ` and ` ph ` ).  Double uniqueness is
       tricky: ` E! x E! y ph ` does not mean "exactly one ` x ` and one
       ` y ` " (see ~ 2eu4 ).  (Contributed by NM, 12-Aug-1993.) $)
    df-eu $a |- ( E! x ph <-> E. y A. x ( ph <-> x = y ) ) $.
  $}

  $( Define "there exists at most one ` x ` such that ` ph ` ."  Here we define
     it in terms of existential uniqueness.  Notation of [BellMachover] p. 460,
     whose definition we show as ~ mo3 .  For other possible definitions see
     ~ mo2 and ~ mo4 .  (Contributed by NM, 8-Mar-1995.) $)
  df-mo $a |- ( E* x ph <-> ( E. x ph -> E! x ph ) ) $.

  ${
    $d x y z $.  $d ph z $.
    euf.1 $e |- F/ y ph $.
    $( A version of the existential uniqueness definition with a hypothesis
       instead of a distinct variable condition.  (Contributed by NM,
       12-Aug-1993.) $)
    euf $p |- ( E! x ph <-> E. y A. x ( ph <-> x = y ) ) $=
      ( vz weu weq wb wal wex df-eu nfbi nfal equequ2 bibi2d albidv cbvex bitri
      nfv ) ABFABEGZHZBIZEJABCGZHZBIZCJABEKUBUEECUACBATCDTCSLMUDEBAUCEAESUCESLM
      ECGZUAUDBUFTUCAECBNOPQR $.
  $}

  ${
    $d x y $.  $d y ph $.  $d y ps $.  $d y ch $.
    eubid.1 $e |- F/ x ph $.
    eubid.2 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for uniqueness quantifier (deduction rule).
       (Contributed by NM, 9-Jul-1994.) $)
    eubid $p |- ( ph -> ( E! x ps <-> E! x ch ) ) $=
      ( vy weq wb wal wex weu bibi1d albid exbidv df-eu 3bitr4g ) ABDGHZIZDJZGK
      CRIZDJZGKBDLCDLATUBGASUADEABCRFMNOBDGPCDGPQ $.
  $}

  ${
    $d x ph $.
    eubidv.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for uniqueness quantifier (deduction rule).
       (Contributed by NM, 9-Jul-1994.) $)
    eubidv $p |- ( ph -> ( E! x ps <-> E! x ch ) ) $=
      ( nfv eubid ) ABCDADFEG $.
  $}

  ${
    eubii.1 $e |- ( ph <-> ps ) $.
    $( Introduce uniqueness quantifier to both sides of an equivalence.
       (Contributed by NM, 9-Jul-1994.)  (Revised by Mario Carneiro,
       6-Oct-2016.) $)
    eubii $p |- ( E! x ph <-> E! x ps ) $=
      ( weu wb wtru a1i eubidv trud ) ACEBCEFGABCABFGDHIJ $.
  $}

  ${
    $d x y $.  $d y ph $.
    $( Bound-variable hypothesis builder for uniqueness.  (Contributed by NM,
       9-Jul-1994.)  (Revised by Mario Carneiro, 7-Oct-2016.) $)
    nfeu1 $p |- F/ x E! x ph $=
      ( vy weu weq wb wal wex df-eu nfa1 nfex nfxfr ) ABDABCEFZBGZCHBABCINBCMBJ
      KL $.
  $}

  $( Bound-variable hypothesis builder for "at most one."  (Contributed by NM,
     8-Mar-1995.)  (Revised by Mario Carneiro, 7-Oct-2016.) $)
  nfmo1 $p |- F/ x E* x ph $=
    ( wmo wex weu wi df-mo nfe1 nfeu1 nfim nfxfr ) ABCABDZABEZFBABGLMBABHABIJK
    $.

  ${
    $d y z $.  $d z ph $.  $d z ps $.
    nfeud2.1 $e |- F/ y ph $.
    nfeud2.2 $e |- ( ( ph /\ -. A. x x = y ) -> F/ x ps ) $.
    $( Bound-variable hypothesis builder for uniqueness.  (Contributed by Mario
       Carneiro, 14-Nov-2016.) $)
    nfeud2 $p |- ( ph -> F/ x E! y ps ) $=
      ( vz weu weq wb wal wex df-eu nfv wn wa nfnae nfan wnf adantlr adantll
      nfeqf ancoms nfbid nfald2 nfexd2 nfxfrd ) BDHBDGIZJZDKZGLACBDGMAUJCGAGNAC
      GICKOZPZUICDAUKDECGDQRULCDICKOZPBUHCAUMBCSUKFTUKUMUHCSZAUMUKUNDGCUBUCUAUD
      UEUFUG $.

    $( Bound-variable hypothesis builder for "at most one."  (Contributed by
       Mario Carneiro, 14-Nov-2016.) $)
    nfmod2 $p |- ( ph -> F/ x E* y ps ) $=
      ( wmo wex weu wi df-mo nfexd2 nfeud2 nfimd nfxfrd ) BDGBDHZBDIZJACBDKAPQC
      ABCDEFLABCDEFMNO $.
  $}

  ${
    nfeud.1 $e |- F/ y ph $.
    nfeud.2 $e |- ( ph -> F/ x ps ) $.
    $( Deduction version of ~ nfeu .  (Contributed by NM, 15-Feb-2013.)
       (Revised by Mario Carneiro, 7-Oct-2016.) $)
    nfeud $p |- ( ph -> F/ x E! y ps ) $=
      ( wnf weq wal wn adantr nfeud2 ) ABCDEABCGCDHCIJFKL $.

    $( Bound-variable hypothesis builder for "at most one."  (Contributed by
       Mario Carneiro, 14-Nov-2016.) $)
    nfmod $p |- ( ph -> F/ x E* y ps ) $=
      ( wnf weq wal wn adantr nfmod2 ) ABCDEABCGCDHCIJFKL $.
  $}

  ${
    $d y z $.  $d x z $.  $d z ph $.
    nfeu.1 $e |- F/ x ph $.
    $( Bound-variable hypothesis builder for uniqueness.  Note that ` x ` and
       ` y ` needn't be distinct (this makes the proof more difficult).
       (Contributed by NM, 8-Mar-1995.)  (Revised by Mario Carneiro,
       7-Oct-2016.) $)
    nfeu $p |- F/ x E! y ph $=
      ( weu wnf wtru nftru a1i nfeud trud ) ACEBFGABCCHABFGDIJK $.

    $( Bound-variable hypothesis builder for "at most one."  (Contributed by
       NM, 9-Mar-1995.) $)
    nfmo $p |- F/ x E* y ph $=
      ( wmo wnf wtru nftru a1i nfmod trud ) ACEBFGABCCHABFGDIJK $.
  $}

  ${
    $d w y z $.  $d ph z w $.  $d w x z $.
    sb8eu.1 $e |- F/ y ph $.
    $( Variable substitution in uniqueness quantifier.  (Contributed by NM,
       7-Aug-1994.)  (Revised by Mario Carneiro, 7-Oct-2016.) $)
    sb8eu $p |- ( E! x ph <-> E! y [ y / x ] ph ) $=
      ( vz vw weq wb wal wex wsb weu nfv sb8 sbbi nfsb equsb3 nfxfr nfbi df-eu
      sbequ cbval sblbis albii 3bitri exbii 3bitr4i ) ABEGZHZBIZEJABCKZCEGZHZCI
      ZEJABLUKCLUJUNEUJUIBFKZFIUIBCKZCIUNUIBFUIFMNUOUPFCUOABFKZUHBFKZHCAUHBFOUQ
      URCABFCDPURFEGZCFBEQUSCMRSRUPFMUIFCBUAUBUPUMCUHULABCCBEQUCUDUEUFABETUKCET
      UG $.

    $( Variable substitution for "at most one."  (Contributed by Alexander van
       der Vekens, 17-Jun-2017.) $)
    sb8mo $p |- ( E* x ph <-> E* y [ y / x ] ph ) $=
      ( wex weu wi wsb wmo sb8e sb8eu imbi12i df-mo 3bitr4i ) ABEZABFZGABCHZCEZ
      QCFZGABIQCIORPSABCDJABCDKLABMQCMN $.
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
    eu1.1 $e |- F/ y ph $.
    $( An alternate way to express uniqueness used by some authors.  Exercise
       2(b) of [Margaris] p. 110.  (Contributed by NM, 20-Aug-1993.)  (Revised
       by Mario Carneiro, 7-Oct-2016.) $)
    eu1 $p |- ( E! x ph <->
                E. x ( ph /\ A. y ( [ y / x ] ph -> x = y ) ) ) $=
      ( wsb weu weq wb wal wex wi wa nfs1v euf sb8eu equcom albii sb6rf 3bitr4i
      imbi2i anbi12i ancom albiim exbii ) ABCEZCFUECBGZHCIZBJABFAUEBCGZKZCIZLZB
      JUECBABCMNABCDOUKUGBUJALUEUFKZCIZUFUEKCIZLUKUGUJUMAUNUIULCUHUFUEBCPTQABCD
      RUAAUJUBUEUFCUCSUDS $.
  $}

  ${
    $d x y z $.  $d ph z $.
    mo.1 $e |- F/ y ph $.
    $( Equivalent definitions of "there exists at most one."  (Contributed by
       NM, 7-Aug-1994.)  (Revised by Mario Carneiro, 7-Oct-2016.) $)
    mo $p |- ( E. y A. x ( ph -> x = y ) <->
               A. x A. y ( ( ph /\ [ y / x ] ph ) -> x = y ) ) $=
      ( vz weq wi wal wex wsb wa nfv nfim nfal equequ2 imbi2d cbv3 sylbir nfn
      wn albidv cbvex nfs1v sbequ2 ax-8 imim12d ancli aaan sylibr equtr2 2alimi
      prth syl6 syl exlimiv nfa2 sp exp3a com3r alimd com12 eximd alnex equcoms
      sbequ1 con3d pm2.21 alimi 19.8a 3syl pm2.61d1 impbii ) ABCFZGZBHZCIZAABCJ
      ZKZVMGZCHZBHZVPABEFZGZBHZEIWAWDVOECWCCBAWBCDWBCLMZNVOELECFZWCVNBWFWBVMAEC
      BOPUAUBWDWAEWDWCVQCEFZGZKZCHBHZWAWDWDWHCHZKWJWDWKWCWHBCWEVQWGBABCUCZWGBLM
      ZVMVQAWBWGABCUDBCEUEUFQUGWCWHBCWEWMUHUIWIVSBCWIVRWBWGKVMAWBVQWGULBCEUJUMU
      KUNUORWAVQCIZVPWAVQVOCVSCBUPVQWAVOVQVTVNBWLVTAVQVMVTAVQVMVSCUQURUSUTVAVBW
      NTVQTZCHZVPVQCVCWPATZBHVOVPWOWQCBVQBWLSACDSCBFAVQAVQGBCABCVEVDVFQWQVNBAVM
      VGVHVOCVIVJRVKVL $.
  $}

  ${
    $d x y $.  $d ph y $.
    $( Existential uniqueness implies existence.  (Contributed by NM,
       15-Sep-1993.)  (Proof shortened by Andrew Salmon, 9-Jul-2011.) $)
    euex $p |- ( E! x ph -> E. x ph ) $=
      ( vy weu wsb weq wi wal wa wex nfv eu1 exsimpl sylbi ) ABDAABCEBCFGCHZIBJ
      ABJABCACKLAOBMN $.
  $}

  ${
    $d x y $.
    eumo0.1 $e |- F/ y ph $.
    $( Existential uniqueness implies "at most one."  (Contributed by NM,
       8-Jul-1994.) $)
    eumo0 $p |- ( E! x ph -> E. y A. x ( ph -> x = y ) ) $=
      ( weu weq wb wal wex wi euf bi1 alimi eximi sylbi ) ABEABCFZGZBHZCIAPJZBH
      ZCIABCDKRTCQSBAPLMNO $.
  $}

  ${
    $d x y $.
    eu2.1 $e |- F/ y ph $.
    $( An alternate way of defining existential uniqueness.  Definition 6.10 of
       [TakeutiZaring] p. 26.  (Contributed by NM, 8-Jul-1994.) $)
    eu2 $p |- ( E! x ph <->
    ( E. x ph /\ A. x A. y ( ( ph /\ [ y / x ] ph ) -> x = y ) ) ) $=
      ( weu wex wsb wa weq wi wal euex eumo0 mo sylib 19.29r impexp albii 19.21
      jca bitri anbi2i abai bitr4i exbii eu1 sylibr impbii ) ABEZABFZAABCGZHBCI
      ZJZCKZBKZHZUIUJUOABLUIAULJBKCFUOABCDMABCDNOTUPAUKULJZCKZHZBFZUIUPAUNHZBFU
      TAUNBPVAUSBVAAAURJZHUSUNVBAUNAUQJZCKVBUMVCCAUKULQRAUQCDSUAUBAURUCUDUEOABC
      DUFUGUH $.
  $}

  ${
    $d x y $.
    eu3.1 $e |- F/ y ph $.
    $( An alternate way to express existential uniqueness.  (Contributed by NM,
       8-Jul-1994.) $)
    eu3 $p |- ( E! x ph <->
                ( E. x ph /\ E. y A. x ( ph -> x = y ) ) ) $=
      ( weu wex wsb wa weq wi wal eu2 mo anbi2i bitr4i ) ABEABFZAABCGHBCIZJCKBK
      ZHPAQJBKCFZHABCDLSRPABCDMNO $.
  $}

  ${
    euor.1 $e |- F/ x ph $.
    $( Introduce a disjunct into a uniqueness quantifier.  (Contributed by NM,
       21-Oct-2005.) $)
    euor $p |- ( ( -. ph /\ E! x ps ) -> E! x ( ph \/ ps ) ) $=
      ( wn weu wo nfn biorf eubid biimpa ) AEZBCFABGZCFLBMCACDHABIJK $.
  $}

  ${
    $d x ph $.
    $( Introduce a disjunct into a uniqueness quantifier.  (Contributed by NM,
       23-Mar-1995.) $)
    euorv $p |- ( ( -. ph /\ E! x ps ) -> E! x ( ph \/ ps ) ) $=
      ( nfv euor ) ABCACDE $.
  $}

  ${
    $d x y $.
    mo2.1 $e |- F/ y ph $.
    $( Alternate definition of "at most one."  (Contributed by NM,
       8-Mar-1995.) $)
    mo2 $p |- ( E* x ph <-> E. y A. x ( ph -> x = y ) ) $=
      ( wmo wex weu wi weq wal df-mo alnex pm2.21 alimi 19.8a syl sylbir eumo0
      wn ja eu3 simplbi2com impbii bitri ) ABEABFZABGZHZABCIZHZBJZCFZABKUGUKUEU
      FUKUESASZBJZUKABLUMUJUKULUIBAUHMNUJCOPQABCDRTUFUEUKABCDUAUBUCUD $.
  $}

  ${
    $d w x z $.  $d w y z $.  $d w ph $.
    $( Substitution into "at most one".  (Contributed by Jeff Madsen,
       2-Sep-2009.) $)
    sbmo $p |- ( [ y / x ] E* z ph <-> E* z [ y / x ] ph ) $=
      ( vw weq wi wal wex wsb wmo nfv sblim sbalv exbii bitri mo2 sbbii 3bitr4i
      sbex ) ADEFZGZDHZEIZBCJZABCJZUAGZDHZEIZADKZBCJUFDKUEUCBCJZEIUIUCEBCTUKUHE
      UBUGBCDAUABCUABLMNOPUJUDBCADEAELQRUFDEUFELQS $.
  $}

  ${
    $d x y $.
    mo3.1 $e |- F/ y ph $.
    $( Alternate definition of "at most one."  Definition of [BellMachover]
       p. 460, except that definition has the side condition that ` y ` not
       occur in ` ph ` in place of our hypothesis.  (Contributed by NM,
       8-Mar-1995.) $)
    mo3 $p |- ( E* x ph <->
               A. x A. y ( ( ph /\ [ y / x ] ph ) -> x = y ) ) $=
      ( wmo weq wi wal wex wsb wa mo2 mo bitri ) ABEABCFZGBHCIAABCJKOGCHBHABCDL
      ABCDMN $.
  $}

  ${
    $d x y $.  $d y ph $.
    mo4f.1 $e |- F/ x ps $.
    mo4f.2 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( "At most one" expressed using implicit substitution.  (Contributed by
       NM, 10-Apr-2004.) $)
    mo4f $p |- ( E* x ph <-> A. x A. y ( ( ph /\ ps ) -> x = y ) ) $=
      ( wmo wsb wa weq wi wal nfv mo3 sbie anbi2i imbi1i 2albii bitri ) ACGAACD
      HZIZCDJZKZDLCLABIZUBKZDLCLACDADMNUCUECDUAUDUBTBAABCDEFOPQRS $.
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
    mobid.1 $e |- F/ x ph $.
    mobid.2 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for "at most one" quantifier (deduction rule).
       (Contributed by NM, 8-Mar-1995.) $)
    mobid $p |- ( ph -> ( E* x ps <-> E* x ch ) ) $=
      ( wex weu wi wmo exbid eubid imbi12d df-mo 3bitr4g ) ABDGZBDHZICDGZCDHZIB
      DJCDJAPRQSABCDEFKABCDEFLMBDNCDNO $.
  $}

  ${
    $d x ph $.
    mobidv.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for "at most one" quantifier (deduction rule).
       (Contributed by Mario Carneiro, 7-Oct-2016.) $)
    mobidv $p |- ( ph -> ( E* x ps <-> E* x ch ) ) $=
      ( nfv mobid ) ABCDADFEG $.
  $}

  ${
    mobii.1 $e |- ( ps <-> ch ) $.
    $( Formula-building rule for "at most one" quantifier (inference rule).
       (Contributed by NM, 9-Mar-1995.)  (Revised by Mario Carneiro,
       17-Oct-2016.) $)
    mobii $p |- ( E* x ps <-> E* x ch ) $=
      ( wmo wb wtru a1i mobidv trud ) ACEBCEFGABCABFGDHIJ $.
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
    $d x y $.  $d y ph $.
    $( Uniqueness in terms of "at most one."  (Contributed by NM,
       23-Mar-1995.) $)
    eu5 $p |- ( E! x ph <-> ( E. x ph /\ E* x ph ) ) $=
      ( vy weu wex weq wi wal wa wmo nfv eu3 mo2 anbi2i bitr4i ) ABDABEZABCFGBH
      CEZIPABJZIABCACKZLRQPABCSMNO $.
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

  $( Existential uniqueness implies "at most one."  (Contributed by NM,
     23-Mar-1995.) $)
  eumo $p |- ( E! x ph -> E* x ph ) $=
    ( weu wex wmo eu5 simprbi ) ABCABDABEABFG $.

  ${
    eumoi.1 $e |- E! x ph $.
    $( "At most one" inferred from existential uniqueness.  (Contributed by NM,
       5-Apr-1995.) $)
    eumoi $p |- E* x ph $=
      ( weu wmo eumo ax-mp ) ABDABECABFG $.
  $}

  $( Existence in terms of "at most one" and uniqueness.  (Contributed by NM,
     5-Apr-2004.) $)
  exmoeu $p |- ( E. x ph <-> ( E* x ph -> E! x ph ) ) $=
    ( wex wmo weu wi df-mo biimpi com12 biimpri euex imim12i peirce syl impbii
    ) ABCZABDZABEZFZQPRQPRFZABGZHISTPFPTQRPQTUAJABKLPRMNO $.

  $( Existence implies "at most one" is equivalent to uniqueness.  (Contributed
     by NM, 5-Apr-2004.) $)
  exmoeu2 $p |- ( E. x ph -> ( E* x ph <-> E! x ph ) ) $=
    ( weu wex wmo eu5 baibr ) ABCABDABEABFG $.

  $( Absorption of existence condition by "at most one."  (Contributed by NM,
     4-Nov-2002.) $)
  moabs $p |- ( E* x ph <-> ( E. x ph -> E* x ph ) ) $=
    ( wex weu wi wmo pm5.4 df-mo imbi2i 3bitr4ri ) ABCZKABDZEZEMKABFZENKLGNMKAB
    HZIOJ $.

  $( Something exists or at most one exists.  (Contributed by NM,
     8-Mar-1995.) $)
  exmo $p |- ( E. x ph \/ E* x ph ) $=
    ( wex wmo wn weu wi pm2.21 df-mo sylibr orri ) ABCZABDZLELABFZGMLNHABIJK $.

  ${
    $d x y $.  $d y ph $.  $d y ps $.
    $( "At most one" is preserved through implication (notice wff reversal).
       (Contributed by NM, 22-Apr-1995.) $)
    moim $p |- ( A. x ( ph -> ps ) -> ( E* x ps -> E* x ph ) ) $=
      ( vy wi wal weq wex wmo imim1 al2imi eximdv nfv mo2 3imtr4g ) ABEZCFZBCDG
      ZEZCFZDHAREZCFZDHBCIACIQTUBDPSUACABRJKLBCDBDMNACDADMNO $.
  $}

  ${
    immoi.1 $e |- ( ph -> ps ) $.
    $( "At most one" is preserved through implication (notice wff reversal).
       (Contributed by NM, 15-Feb-2006.) $)
    moimi $p |- ( E* x ps -> E* x ph ) $=
      ( wi wmo moim mpg ) ABEBCFACFECABCGDH $.
  $}

  ${
    $d x y $.  $d x y ph $.  $d y ps $.
    $( Move antecedent outside of "at most one."  (Contributed by NM,
       28-Jul-1995.) $)
    morimv $p |- ( E* x ( ph -> ps ) -> ( ph -> E* x ps ) ) $=
      ( vy wmo weq wal wex ax-1 a1i imim1d alimdv eximdv nfv mo2 3imtr4g com12
      wi ) AABRZCEZBCEZASCDFZRZCGZDHBUBRZCGZDHTUAAUDUFDAUCUECABSUBBSRABAIJKLMSC
      DSDNOBCDBDNOPQ $.
  $}

  $( Uniqueness implies "at most one" through implication.  (Contributed by NM,
     22-Apr-1995.) $)
  euimmo $p |- ( A. x ( ph -> ps ) -> ( E! x ps -> E* x ph ) ) $=
    ( weu wmo wi wal eumo moim syl5 ) BCDBCEABFCGACEBCHABCIJ $.

  $( Add existential uniqueness quantifiers to an implication.  Note the
     reversed implication in the antecedent.  (Contributed by NM,
     19-Oct-2005.)  (Proof shortened by Andrew Salmon, 14-Jun-2011.) $)
  euim $p |- ( ( E. x ph /\ A. x ( ph -> ps ) ) -> ( E! x ps -> E! x ph ) ) $=
    ( wex wi wal wa weu wmo ax-1 euimmo anim12ii eu5 syl6ibr ) ACDZABECFZGBCHZO
    ACIZGACHOQOPROQJABCKLACMN $.

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
    $( Introduction of a conjunct into "at most one" quantifier.  (Contributed
       by NM, 3-Dec-2001.) $)
    moanim $p |- ( E* x ( ph /\ ps ) <-> ( ph -> E* x ps ) ) $=
      ( vy wa weq wi wal wex wmo impexp albii 19.21 bitri nfv mo2 imbi2i 19.37v
      exbii bitr4i 3bitr4i ) ABFZCEGZHZCIZEJABUDHZCIZHZEJZUCCKABCKZHZUFUIEUFAUG
      HZCIUIUEUMCABUDLMAUGCDNOTUCCEUCEPQULAUHEJZHUJUKUNABCEBEPQRAUHESUAUB $.

    $( Introduction of a conjunct into uniqueness quantifier.  (Contributed by
       NM, 19-Feb-2005.)  (Proof shortened by Andrew Salmon, 9-Jul-2011.) $)
    euan $p |- ( E! x ( ph /\ ps ) <-> ( ph /\ E! x ps ) ) $=
      ( wa weu wex wmo simpl exlimi adantr exsimpr nfe1 simpr a1d ancrd impbid2
      mobid biimpa eu5 jca32 anbi2i 3imtr4i ibar eubid impbii ) ABEZCFZABCFZEZU
      GCGZUGCHZEZABCGZBCHZEZEUHUJUMAUNUOUKAULUGACDABIJZKUKUNULABCLKUKULUOUKUGBC
      UGCMUKUGBABNUKBAUKABUQOPQRSUAUGCTUIUPABCTUBUCAUIUHABUGCDABUDUESUF $.
  $}

  ${
    $d x y ph $.  $d y ps $.
    $( Introduction of a conjunct into "at most one" quantifier.  (Contributed
       by NM, 23-Mar-1995.) $)
    moanimv $p |- ( E* x ( ph /\ ps ) <-> ( ph -> E* x ps ) ) $=
      ( nfv moanim ) ABCACDE $.
  $}

  $( Nested "at most one" and uniqueness quantifiers.  (Contributed by NM,
     25-Jan-2006.) $)
  moaneu $p |- E* x ( ph /\ E! x ph ) $=
    ( weu wa wmo wi eumo nfeu1 moanim mpbir ancom mobii ) AABCZDZBEMADZBEZPMABE
    FABGMABABHIJNOBAMKLJ $.

  $( Nested "at most one" quantifiers.  (Contributed by NM, 25-Jan-2006.) $)
  moanmo $p |- E* x ( ph /\ E* x ph ) $=
    ( wmo wa wi id nfmo1 moanim mpbir ancom mobii ) AABCZDZBCLADZBCZOLLELFLABAB
    GHIMNBALJKI $.

  ${
    $d x ph $.
    $( Introduction of a conjunct into uniqueness quantifier.  (Contributed by
       NM, 23-Mar-1995.) $)
    euanv $p |- ( E! x ( ph /\ ps ) <-> ( ph /\ E! x ps ) ) $=
      ( nfv euan ) ABCACDE $.
  $}

  ${
    $d x y $.  $d y ph $.  $d y ps $.
    $( "At most one" picks a variable value, eliminating an existential
       quantifier.  (Contributed by NM, 27-Jan-1997.) $)
    mopick $p |- ( ( E* x ph /\ E. x ( ph /\ ps ) ) -> ( ph -> ps ) ) $=
      ( vy wa wex wmo wi wsb nfv nfs1v nfan weq sbequ12 anbi12d cbvex wal sylbi
      mo3 sp sps sbequ2 imim2i exp3a com4t imp syl5 exlimiv impcom ) ABEZCFZACG
      ZABHZUKACDIZBCDIZEZDFULUMHZUJUPCDUJDJUNUOCACDKBCDKLCDMZAUNBUOACDNBCDNOPUP
      UQDULAUNEZURHZUPUMULUTDQZCQUTACDADJSVAUTCUTDTUARUNUOUTUMHUTAUNUOBUTAUNUOB
      HZURVBUSBCDUBUCUDUEUFUGUHRUI $.
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
    ( weu wa wex wi nfeu1 nfe1 nfan eupick alrimi ) ACDZABEZCFZEABGCMOCACHNCIJA
    BCKL $.

  $( Existential uniqueness "pick" showing wff equivalence.  (Contributed by
     NM, 25-Nov-1994.) $)
  eupickb $p |- ( ( E! x ph /\ E! x ps /\ E. x ( ph /\ ps ) ) ->
               ( ph <-> ps ) ) $=
    ( weu wa wex w3a wi eupick 3adant2 3simpc pm3.22 eximi anim2i 3syl impbid )
    ACDZBCDZABEZCFZGZABQTABHRABCIJUARTERBAEZCFZEBAHQRTKTUCRSUBCABLMNBACIOP $.

  $( Theorem *14.26 in [WhiteheadRussell] p. 192.  (Contributed by Andrew
     Salmon, 11-Jul-2011.) $)
  eupickbi $p |- ( E! x ph -> ( E. x ( ph /\ ps ) <-> A. x ( ph -> ps ) ) ) $=
    ( weu wa wex wi wal eupicka ex nfa1 wb ancl simpl impbid1 eubid euex syl6bi
    sps com12 impbid ) ACDZABEZCFZABGZCHZUBUDUFABCIJUFUBUDUFUBUCCDUDUFAUCCUECKU
    EAUCLCUEAUCABMABNOSPUCCQRTUA $.

  $( "At most one" can show the existence of a common value.  In this case we
     can infer existence of conjunction from a conjunction of existence, and it
     is one way to achieve the converse of ~ 19.40 .  (Contributed by NM,
     5-Apr-2004.)  (Proof shortened by Andrew Salmon, 9-Jul-2011.) $)
  mopick2 $p |- ( ( E* x ph /\ E. x ( ph /\ ps ) /\ E. x ( ph /\ ch ) ) ->
                E. x ( ph /\ ps /\ ch ) ) $=
    ( wmo wa wex w3a nfmo1 nfe1 mopick ancld anim1d df-3an syl6ibr eximd 3impia
    nfan ) ADEZABFZDGZACFZDGABCHZDGSUAFZUBUCDSUADADITDJRUDUBTCFUCUDATCUDABABDKL
    MABCNOPQ $.

  $( Introduce or eliminate a disjunct in a uniqueness quantifier.
     (Contributed by NM, 21-Oct-2005.)  (Proof shortened by Andrew Salmon,
     9-Jul-2011.) $)
  euor2 $p |- ( -. E. x ph -> ( E! x ( ph \/ ps ) <-> E! x ps ) ) $=
    ( wex wn wo nfe1 nfn wb 19.8a con3i orel1 olc impbid1 syl eubid ) ACDZEZABF
    ZBCQCACGHRAEZSBIAQACJKTSBABLBAMNOP $.

  ${
    moexex.1 $e |- F/ y ph $.
    $( "At most one" double quantification.  (Contributed by NM,
       3-Dec-2001.) $)
    moexex $p |- ( ( E* x ph /\ A. x E* y ps ) -> E* y E. x ( ph /\ ps ) ) $=
      ( wmo wal wa wex wi nfmo1 nfa1 nfe1 nfmo nfim mopick ex exlimi wn a1d ori
      com3r alrimd moim spsd syl6 nfex exsimpl con3i exmo syl pm2.61i imp ) ACF
      ZBDFZCGZABHZCIZDFZACIZUNUPUSJZJZAVBCUNVACACKUPUSCUOCLURCDUQCMNOOAUNURBJZD
      GZVAAUNVCDEADCENUNURABUNURABJABCPQUBUCVDUOUSCURBDUDUEUFRUTSZVAUNVEUSUPVEU
      RDIZSUSVFUTURUTDADCEUGABCUHRUIVFUSURDUJUAUKTTULUM $.
  $}

  ${
    $d y ph $.
    $( "At most one" double quantification.  (Contributed by NM,
       26-Jan-1997.) $)
    moexexv $p |- ( ( E* x ph /\ A. x E* y ps ) -> E* y E. x ( ph /\ ps ) ) $=
      ( nfv moexex ) ABCDADEF $.
  $}

  $( Double quantification with "at most one."  (Contributed by NM,
     3-Dec-2001.) $)
  2moex $p |- ( E* x E. y ph -> A. y E* x ph ) $=
    ( wex wmo nfe1 nfmo 19.8a moimi alrimi ) ACDZBEABECKCBACFGAKBACHIJ $.

  $( Double quantification with existential uniqueness.  (Contributed by NM,
     3-Dec-2001.)  (Proof shortened by Andrew Salmon, 9-Jul-2011.) $)
  2euex $p |- ( E! x E. y ph -> E. y E! x ph ) $=
    ( wex weu wmo wa eu5 excom nfe1 19.8a moimi df-mo sylib eximd syl5bi impcom
    nfmo wi sylbi ) ACDZBEUABDZUABFZGABEZCDZUABHUCUBUEUBABDZCDUCUEABCIUCUFUDCUA
    CBACJRUCABFUFUDSAUABACKLABMNOPQT $.

  $( Double quantification with existential uniqueness and "at most one."
     (Contributed by NM, 3-Dec-2001.) $)
  2eumo $p |- ( E! x E* y ph -> E* x E! y ph ) $=
    ( weu wmo wi euimmo eumo mpg ) ACDZACEZFKBDJBEFBJKBGACHI $.

  $( Double existential uniqueness.  (Contributed by NM, 3-Dec-2001.) $)
  2eu2ex $p |- ( E! x E! y ph -> E. x E. y ph ) $=
    ( weu wex euex eximi syl ) ACDZBDIBEACEZBEIBFIJBACFGH $.

  $( A condition allowing swap of "at most one" and existential quantifiers.
     (Contributed by NM, 10-Apr-2004.) $)
  2moswap $p |- ( A. x E* y ph -> ( E* x E. y ph -> E* y E. x ph ) ) $=
    ( wmo wal wex wa nfe1 moexex expcom 19.8a pm4.71ri exbii mobii syl6ibr ) AC
    DBEZACFZBDZQAGZBFZCDZABFZCDRPUAQABCACHIJUBTCASBAQACKLMNO $.

  $( A condition allowing swap of uniqueness and existential quantifiers.
     (Contributed by NM, 10-Apr-2004.) $)
  2euswap $p |- ( A. x E* y ph -> ( E! x E. y ph -> E! y E. x ph ) ) $=
    ( wmo wal wex wa weu wi excomim a1i 2moswap anim12d eu5 3imtr4g ) ACDBEZACF
    ZBFZQBDZGABFZCFZTCDZGQBHTCHPRUASUBRUAIPABCJKABCLMQBNTCNO $.

  $( Double existential uniqueness implies double uniqueness quantification.
     (Contributed by NM, 3-Dec-2001.)  (Proof shortened by Mario Carneiro,
     22-Dec-2016.) $)
  2exeu $p |- ( ( E! x E. y ph /\ E! y E. x ph ) -> E! x E! y ph ) $=
    ( wex weu wa wmo eumo euex moimi syl 2euex anim12ci eu5 sylibr ) ACDZBEZABD
    CEZFACEZBDZSBGZFSBEQUARTQPBGUAPBHSPBACIJKACBLMSBNO $.

  ${
    $d x y z w v u $.  $d z w v u ph $.
    $( Two equivalent expressions for double "at most one."  (Contributed by
       NM, 2-Feb-2005.)  (Revised by Mario Carneiro, 17-Oct-2016.) $)
    2mo $p |- ( E. z E. w A. x A. y ( ph -> ( x = z /\ y = w ) ) <->
              A. x A. y A. z A. w ( ( ph /\ [ z / x ] [ w / y ] ph ) ->
                   ( x = z /\ y = w ) ) ) $=
      ( vv vu weq wa wi wal wex wsb nfv albii bitri 2alimi syl sylbir wn imbi2d
      equequ2 2albidv cbvex2v nfs1v nfim nfsb sbequ12 sylan9bbr equequ1 imbi12d
      bi2anan9 cbval2 biimpi ancli alcom aaan nfal sylibr prth equtr2 an4s syl6
      anim12i exlimivv alrot4 pm3.21 imim1d alimd com12 alimi exim sylbi notbid
      alnex nfn pm2.21 19.8a 19.23bi pm2.61d1 impbii ) ABDHZCEHZIZJZCKZBKZELZDL
      ZAACEMZBDMZIZWDJZEKDKZCKBKZWIABFHZCGHZIZJZCKZBKZGLFLWOXAWGFGDEFDHZGEHZIZW
      SWEBCXDWRWDAXBWPWBXCWQWCFDBUBGECUBULUAUCUDXAWOFGXAWSWKDFHZEGHZIZJZIZEKZDK
      ZCKZBKZWOXAXAXHEKZDKZIZXMXAXOXAXOWSXHBCDEWSDNWSENZWKXGBWJBDUEZXGBNUFZWKXG
      CWJBDCACEUEUGZXGCNUFZWDAWKWRXGWCAWJWBWKACEUHWJBDUHUIZWBWPXEWCWQXFBDFUJCEG
      UJULUKUMUNUOXMWTXNIZDKZBKXPXLYDBXLXJCKZDKYDXJCDUPYEYCDWSXHCEXQYAUQOPOWTXN
      BDWTDNXHBEXSURUQPUSXKWNBCXIWMDEXIWLWRXGIWDAWRWKXGUTWPXEWQXFWDWPXEIWBWQXFI
      WCBDFVACEGVAVDVBVCQQRVESWOWKELZDLZWIWOYFWHJZDKZYGWIJWOWMCKZBKZEKZDKYIWMBC
      DEVFYLYHDYLWKWGJZEKYHYKYMEWKYKWGWKYJWFBXRWKWMWECXTWKAWLWDWKAVGVHVIVIVJVKW
      KWGEVLRVKVMYFWHDVLRYGTZWKTZEKZDKZWIYQYFTZDKYNYPYRDWKEVOOYFDVOPYQWGWIYQATZ
      CKBKWGYSYOBCDEYSDNYSENWKBXRVPWKCXTVPWDAWKYBVNUMYSWEBCAWDVQQSWGWIEWHDVRVSR
      SVTWA $.
  $}

  ${
    $d z w ph $.  $d x y ps $.  $d x y z w $.
    2mos.1 $e |- ( ( x = z /\ y = w ) -> ( ph <-> ps ) ) $.
    $( Double "exists at most one", using implicit substitution.  (Contributed
       by NM, 10-Feb-2005.) $)
    2mos $p |- ( E. z E. w A. x A. y ( ph -> ( x = z /\ y = w ) ) <->
             A. x A. y A. z A. w ( ( ph /\ ps ) -> ( x = z /\ y = w ) ) ) $=
      ( weq wa wi wal wex wsb 2mo nfv sbiedv sbie anbi2i imbi1i 2albii bitri )
      ACEHZDFHIZJDKCKFLELAADFMZCEMZIZUCJZFKEKZDKCKABIZUCJZFKEKZDKCKACDEFNUHUKCD
      UGUJEFUFUIUCUEBAUDBCEBCOUBABDFGPQRSTTUA $.
  $}

  $( Double existential uniqueness.  This theorem shows a condition under which
     a "naive" definition matches the correct one.  (Contributed by NM,
     3-Dec-2001.) $)
  2eu1 $p |- ( A. x E* y ph ->
        ( E! x E! y ph <-> ( E! x E. y ph /\ E! y E. x ph ) ) ) $=
    ( wmo wal weu wex wa wi eu5 exbii mobii anbi12i bitri simprbi anim2i ancoms
    sp sylib com12 moimi nfa1 moanim ancrd 2moswap imdistani syl6 syl excom jca
    2eu2ex jctild an4 syl6ibr 2exeu impbid1 ) ACDZBEZACFZBFZACGZBFZABGZCFZHZUTU
    RVEUTURVABGZVCCGZHZVABDZVCCDZHZHZVEUTURVKVHUTVAUQHZBDZURVKIUTVMBGZVNUTUSBGZ
    USBDZHVOVNHUSBJVPVOVQVNUSVMBACJZKUSVMBVRLMNOVNURVIURHVKVNURVIVNURVAHZBDURVI
    IVSVMBVAURVMURUQVAUQBRPQUAURVABUQBUBUCSUDVIURVJURVIVJABCUETUFUGUHUTVFVGABCU
    KZUTVFVGVTABCUISUJULVEVFVIHZVGVJHZHVLVBWAVDWBVABJVCCJMVFVIVGVJUMNUNTABCUOUP
    $.

  $( Double existential uniqueness.  (Contributed by NM, 3-Dec-2001.) $)
  2eu2 $p |- ( E! y E. x ph -> ( E! x E! y ph <-> E! x E. y ph ) ) $=
    ( wex weu wmo wal wi eumo 2moex 2eu1 simpl syl6bi 3syl 2exeu expcom impbid
    wa ) ABDZCEZACEBEZACDBEZTSCFACFBGZUAUBHSCIACBJUCUAUBTRUBABCKUBTLMNUBTUAABCO
    PQ $.


  $( Double existential uniqueness.  (Contributed by NM, 3-Dec-2001.) $)
  2eu3 $p |- ( A. x A. y ( E* x ph \/ E* y ph ) ->
 ( ( E! x E! y ph /\ E! y E! x ph ) <-> ( E! x E. y ph /\ E! y E. x ph ) ) ) $=
    ( wmo wo wal weu wa wex wb nfmo1 19.31 albii nfal 19.32 bitri wi 2eu1 2exeu
    biimpd ancom syl6ib adantld adantrd jaoi ancoms jca impbid1 sylbi ) ABDZACD
    ZECFZBFZUJCFZUKBFZEZACGBGZABGCGZHZACIBGZABICGZHZJUMUNUKEZBFUPULVCBUJUKCACKL
    MUNUKBUJBCABKNOPUPUSVBUNUSVBQUOUNURVBUQUNURVAUTHZVBUNURVDACBRTVAUTUAUBUCUOU
    QVBURUOUQVBABCRTUDUEVBUQURABCSVAUTURACBSUFUGUHUI $.

  ${
    $d x y z w $.  $d z w ph $.
    $( This theorem provides us with a definition of double existential
       uniqueness ("exactly one ` x ` and exactly one ` y ` ").  Naively one
       might think (incorrectly) that it could be defined by
       ` E! x E! y ph ` .  See ~ 2eu1 for a condition under which the naive
       definition holds and ~ 2exeu for a one-way implication.  See ~ 2eu5 and
       ~ 2eu8 for alternate definitions.  (Contributed by NM, 3-Dec-2001.) $)
    2eu4 $p |- ( ( E! x E. y ph /\ E! y E. x ph ) <->
      ( E. x E. y ph /\ E. z E. w A. x A. y ( ph -> ( x = z /\ y = w ) ) ) ) $=
      ( wex weu wa weq wal nfv eu3 anbi12i anbi2i bitri 19.26 nfa1 19.3 albii
      wi an4 excom anidm jcab bitr4i bitr2i 19.23v 2albii nfe1 nfim aaan 3bitri
      alcom 2exbii eeanv ) ACFZBGZABFZCGZHUPBFZUPBDIZTZBJZDFZHZURCFZURCEIZTZCJZ
      EFZHZHUTVFHZVDVJHZHUTAVAVGHTZCJZBJZEFDFZHUQVEUSVKUPBDUPDKLURCEUREKLMUTVDV
      FVJUAVLUTVMVQVLUTUTHUTVFUTUTACBUBNUTUCOVQVCVIHZEFDFVMVPVRDEVPAVATZCJZAVGT
      ZBJZHZCJZBJZVBVHHZCJBJVRVPVTWACJZBJZHZBJZWEWJVTBJZWHBJZHZVPVTWHBPWMWKWHHZ
      VPWLWHWKWHBWGBQRNVPVTWGHZBJWNVOWOBVOVSWAHZCJWOVNWPCAVAVGUDSVSWACPOSVTWGBP
      OUEUFWDWIBWDVTCJZWBCJZHWIVTWBCPWQVTWRWHVTCVSCQRWACBUMMOSUEWCWFBCVTVBWBVHA
      VACUGAVGBUGMUHVBVHBCUPVACACUIVACKUJURVGBABUIVGBKUJUKULUNVCVIDEUOUFMUL $.

    $( An alternate definition of double existential uniqueness (see ~ 2eu4 ).
       A mistake sometimes made in the literature is to use ` E! x E! y ` to
       mean "exactly one ` x ` and exactly one ` y ` ."  (For example, see
       Proposition 7.53 of [TakeutiZaring] p. 53.)  It turns out that this is
       actually a weaker assertion, as can be seen by expanding out the formal
       definitions.  This theorem shows that the erroneous definition can be
       repaired by conjoining ` A. x E* y ph ` as an additional condition.  The
       correct definition apparently has never been published.  ( ` E* ` means
       "exists at most one.") (Contributed by NM, 26-Oct-2003.) $)
    2eu5 $p |- ( ( E! x E! y ph /\ A. x E* y ph ) <->
      ( E. x E. y ph /\ E. z E. w A. x A. y ( ph -> ( x = z /\ y = w ) ) ) ) $=
      ( weu wmo wal wa wex weq 2eu1 pm5.32ri eumo adantl 2moex syl pm4.71i 2eu4
      wi 3bitr2i ) ACFBFZACGBHZIACJZBFZABJZCFZIZUCIUHUDBJABDKCEKITCHBHEJDJIUCUB
      UHABCLMUHUCUHUFCGZUCUGUIUEUFCNOACBPQRABCDESUA $.
  $}

  ${
    $d x y z w v u $.  $d z w v u ph $.
    $( Two equivalent expressions for double existential uniqueness.
       (Contributed by NM, 2-Feb-2005.)  (Revised by Mario Carneiro,
       17-Oct-2016.) $)
    2eu6 $p |- ( ( E! x E. y ph /\ E! y E. x ph ) <->
               E. z E. w A. x A. y ( ph <-> ( x = z /\ y = w ) ) ) $=
      ( vu vv wex wa weq wal wsb nfv nfsb sbequ12 equequ2 bi2anan9 nfim bitri
      wi weu 2eu4 nfs1v sylan9bbr cbvex2 imbi2d 2albidv cbvex2v equequ1 imbi12d
      cbval2 2exbii 2mo 19.29r2 syl2anb 2albiim ancom sbco2 sbbii sbcom2 bitr3i
      nfan syl6bb anbi2d equcom anbi12i imbi2i impexp 2albii anbi2i abai bitr4i
      wb 19.21-2 2sb6 anbi1i sylibr bi2 2alimi 2eximi 2exsb bi1 jca impbii ) AC
      HZBUAABHCUAIWEBHZABDJZCEJZIZTZCKBKZEHDHZIZAWIVMZCKBKZEHDHZABCDEUBWMWPWMAC
      ELZBDLZWRWREFLZDGLZIZDGJZEFJZIZTZFKGKZIZEHDHZWPWFWREHDHXFEKDKZXHWLAWRBCDE
      ADMAEMZWQBDUCZWQBDCACEUCNZWHAWQWGWRACEOWQBDOUDZUEWLABGJZCFJZIZTZCKBKZFHGH
      ZXIWKXRDEGFXDWJXQBCXDWIXPAXBWGXNXCWHXODGBPEFCPQUFUGUHXSWRXDTZEKDKZFHGHXIX
      RYAGFXQXTBCDEXQDMXQEMWRXDBXKXDBMZRWRXDCXLXDCMZRWIAWRXPXDXMWGXNXBWHXOXCBDG
      UICEFUIQUJUKULWRDEGFUMSSWRXFDEUNUOWPWIATZCKBKZWKIZEHDHXHWOYFDEWOWKYEIYFAW
      IBCUPWKYEUQSULXGYFDEXGWRWKIZYFXGWRWRWKTZIYGXFYHWRXFWRWJTZCKBKZYHXFWRAIZDB
      JZECJZIZTZCKBKYJYOXEBCGFYOGMYOFMXAXDBWRWTBXKWSDGBWREFBXKNNVBYBRXAXDCWRWTC
      XLWSDGCWREFCXLNNVBYCRXPYKXAYNXDXPAWTWRXPAACFLZBGLZWTXOAYPXNYQACFOYPBGOUDY
      QWQEFLZBGLZWTYRYPBGACFEXJURUSYSYRBDLZDGLWTYRBGDYRDMURYTWSDGWQEFBDUTUSVAVA
      VCVDXNYLXBXOYMXCBGDPCFEPQUJUKYOYIBCYOYKWITYIYNWIYKYLWGYMWHDBVEECVEVFVGWRA
      WIVHSVIVAWRWJBCXKXLVNSVJWRWKVKVLWRYEWKABCDEVOVPSULVLVQWPWFWLWPYEEHDHWFWOY
      EDEWNYDBCAWIVRVSVTABCDEWAVQWOWKDEWNWJBCAWIWBVSVTWCWDS $.
  $}

  $( Two equivalent expressions for double existential uniqueness.
     (Contributed by NM, 19-Feb-2005.) $)
  2eu7 $p |- ( ( E! x E. y ph /\ E! y E. x ph ) <->
             E! x E! y ( E. x ph /\ E. y ph ) ) $=
    ( wex weu wa nfe1 nfeu euan ancom eubii 3bitri 3bitr4ri ) ABDZCEZACDZFZBEOP
    BEZFNPFZCEZBEROFOPBNBCABGHITQBTPNFZCEPOFQSUACNPJKPNCACGIPOJLKROJM $.

  $( Two equivalent expressions for double existential uniqueness.  Curiously,
     we can put ` E! ` on either of the internal conjuncts but not both.  We
     can also commute ` E! x E! y ` using ~ 2eu7 .  (Contributed by NM,
     20-Feb-2005.) $)
  2eu8 $p |- ( E! x E! y ( E. x ph /\ E. y ph ) <->
                E! x E! y ( E! x ph /\ E. y ph ) ) $=
    ( wex wa 2eu2 pm5.32i nfeu1 nfeu euan ancom eubii nfe1 3bitri 3bitr4ri 2eu7
    weu 3bitr3ri ) ACDZBQZABQZCQZEZTABDZCQZEUASEZCQZBQZUDSECQBQTUBUEACBFGUBSEZB
    QUBTEUHUCUBSBUABCABHIJUGUIBUGSUAEZCQSUBEUIUFUJCUASKLSUACACMJSUBKNLTUBKOABCP
    R $.

  ${
    $d x y z $.
    $( Equality has existential uniqueness.  Special case of ~ eueq1 proved
       using only predicate calculus.  (Contributed by Stefan Allan,
       4-Dec-2008.) $)
    euequ1 $p |- E! x x = y $=
      ( vz weq weu wex wa wi wal a9ev equtr2 gen2 equequ1 eu4 mpbir2an ) ABDZAE
      PAFPCBDZGACDHZCIAIABJRACACBKLPQACACBMNO $.
  $}

  ${
    $d x y $.
    $( Two ways to express "only one thing exists."  The left-hand side
       requires only one variable to express this.  Both sides are false in set
       theory; see theorem ~ dtru .  (Contributed by NM, 5-Apr-2004.) $)
    exists1 $p |- ( E! x x = x <-> A. x x = y ) $=
      ( weq weu wb wal wex df-eu equid tbt bicom bitri albii exbii nfae 3bitr2i
      19.9 ) AACZADRABCZEZAFZBGSAFZBGUBRABHUBUABSTASSRETRSAIJSRKLMNUBBABBOQP $.

    $( A condition implying that at least two things exist.  (Contributed by
       NM, 10-Apr-2004.)  (Proof shortened by Andrew Salmon, 9-Jul-2011.) $)
    exists2 $p |- ( ( E. x ph /\ E. x -. ph ) -> -. E! x x = x ) $=
      ( vy wex wn weq weu wal nfeu1 nfa1 exists1 ax16 sylbi exlimd com12 syl6ib
      wi alex con2d imp ) ABDZAEBDZBBFZBGZEUAUDUBUAUDABHZUBEUDUAUEUDAUEBUCBIABJ
      UDBCFBHAUEQBCKABCLMNOABRPST $.
  $}

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
             Other axiomatizations related to classical predicate calculus
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Predicate calculus with all distinct variables
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x y z $.
    $( Distinct variable version of ~ ax-7 .  (Contributed by Mario Carneiro,
       14-Aug-2015.) $)
    ax-7d $a |- ( A. x A. y ph -> A. y A. x ph ) $.

    $( Distinct variable version of ~ ax-8 .  (Contributed by Mario Carneiro,
       14-Aug-2015.) $)
    ax-8d $a |- ( x = y -> ( x = z -> y = z ) ) $.

    $( Distinct variable version of ~ ax-9 , equal variables case.
       (Contributed by Mario Carneiro, 14-Aug-2015.) $)
    ax-9d1 $a |- -. A. x -. x = x $.

    $( Distinct variable version of ~ ax-9 , distinct variables case.
       (Contributed by Mario Carneiro, 14-Aug-2015.) $)
    ax-9d2 $a |- -. A. x -. x = y $.

    $( Distinct variable version of ~ ax10 .  (Contributed by Mario Carneiro,
       14-Aug-2015.) $)
    ax-10d $a |- ( A. x x = y -> A. y y = x ) $.

    $( Distinct variable version of ~ ax-11 .  (Contributed by Mario Carneiro,
       14-Aug-2015.) $)
    ax-11d $a |- ( x = y -> ( A. y ph -> A. x ( x = y -> ph ) ) ) $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
               Aristotelian logic: Assertic syllogisms
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  Model the Aristotelian assertic syllogisms using modern notation.
  This section shows that the Aristotelian assertic syllogisms can be proven
  with our axioms of logic, and also provides generally useful theorems.

  In antiquity Aristotelian logic and Stoic logic
  (see ~ mpto1 ) were the leading logical systems.
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
  ~ http://plato.stanford.edu/entries/quantification/ .
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
  ambit of science. This is why he leaves no room for such non-existent
  entities in his logic.  This is a thoughtful choice, not an inadvertent
  omission. Technically, Aristotelian science is a search for definitions,
  where a definition is "a phrase signifying a thing's essence."
  (Topics, I.5.102a37, Pickard-Cambridge.)...
  Because non-existent entities cannot be anything, they do not, in
  Aristotle's mind, possess an essence...  This is why he leaves
  no place for fictional entities like goat-stags (or unicorns)."
  Source: Louis F. Groarke, "Aristotle: Logic",
  section 7. (Existential Assumptions),
  _Internet Encyclopedia of Philosophy_ (A Peer-Reviewed Academic Resource),
  ~ http://www.iep.utm.edu/aris-log/ .
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

  Aristotelean logic is essentially the forerunner of predicate calculus
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
       including ~ http://www.friesian.com/aristotl.htm ,
       ~ http://plato.stanford.edu/entries/aristotle-logic/ , and
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
       ` ps ` , and no ` ch ` is ` ps ` , therefore no ` ch ` is ` ph ` .  (In
       Aristotelian notation, AEE-2:  PaM and SeM therefore SeP.) (Contributed
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
       useful", therefore "Some websites are not informative."  (Contributed by
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
       is not ` ph ` .  (In Aristotelian notation, EAO-2:  PeM and SaM
       therefore SoP.) (Contributed by David A. Wheeler, 28-Aug-2016.)
       (Revised by David A. Wheeler, 2-Sep-2016.) $)
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
       ` ps ` , and no ` ps ` is ` ch ` , therefore no ` ch ` is ` ph ` .  (In
       Aristotelian notation, AEE-4:  PaM and MeS therefore SeP.) (Contributed
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
       not ` ph ` (SoP).  (In Aristotelian notation, EIO-4:  PeM and MiS
       therefore SoP.) (Contributed by David A. Wheeler, 28-Aug-2016.)
       (Revised by David A. Wheeler, 2-Sep-2016.) $)
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
       some ` ch ` is not ` ph ` (SoP).  (In Aristotelian notation, AEO-4:  PaM
       and MeS therefore SoP.) (Contributed by David A. Wheeler, 28-Aug-2016.)
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
       is not ` ph ` .  (In Aristotelian notation, EAO-4:  PeM and MaS
       therefore SoP.) (Contributed by David A. Wheeler, 28-Aug-2016.)
       (Revised by David A. Wheeler, 2-Sep-2016.) $)
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
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
               Intuitionistic logic
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

Intuitionistic (constructive) logic is similar to classical logic
with the notable omission of ~ ax-3 and theorems such as ~ exmid or
~ peirce . We mostly treat intuitionistic logic in a separate file, iset.mm,
which is known as the Intuitionistic Logic Explorer on the web site. However,
iset.mm has a number of additional axioms (mainly to replace definitions like
~ df-or and ~ df-ex which are not valid in intitionistic logic) and we want
to prove those axioms here to demonstrate that adding those axioms in iset.mm
does not make iset.mm any less consistent than set.mm.

The following axioms are unchanged between set.mm and iset.mm: ~ ax-1 ,
~ ax-2 , ~ ax-mp , ~ ax-5 , ~ ax-7 , ~ ax-gen , ~ ax-8 , ~ ax-11 ,
~ ax-13 , ~ ax-14 , and ~ ax-17 .

$)

  $( Left 'and' elimination (intuitionistic logic axiom ax-ia1).  (Contributed
     by Jim Kingdon, 21-May-2018.) $)
  axia1 $p |- ( ( ph /\ ps ) -> ph ) $=
    ( simpl ) ABC $.

  $( Right 'and' elimination (intuitionistic logic axiom ax-ia2).  (Contributed
     by Jim Kingdon, 21-May-2018.) $)
  axia2 $p |- ( ( ph /\ ps ) -> ps ) $=
    ( simpr ) ABC $.

  $( 'And' introduction (intuitionistic logic axiom ax-ia3).  (Contributed by
     Jim Kingdon, 21-May-2018.) $)
  axia3 $p |- ( ph -> ( ps -> ( ph /\ ps ) ) ) $=
    ( pm3.2 ) ABC $.

  $( 'Not' introduction (intuitionistic logic axiom ax-in1).  (Contributed by
     Jim Kingdon, 21-May-2018.) $)
  axin1 $p |- ( ( ph -> -. ph ) -> -. ph ) $=
    ( pm2.01 ) AB $.

  $( 'Not' elimination (intuitionistic logic axiom ax-in2).  (Contributed by
     Jim Kingdon, 21-May-2018.) $)
  axin2 $p |- ( -. ph -> ( ph -> ps ) ) $=
    ( pm2.21 ) ABC $.

  $( Definition of 'or' (intuitionistic logic axiom ax-io).  (Contributed by
     Jim Kingdon, 21-May-2018.) $)
  axio $p |- ( ( ( ph \/ ch ) -> ps ) <->
      ( ( ph -> ps ) /\ ( ch -> ps ) ) ) $=
    ( jaob ) ABCD $.

  $( Specialization (intuitionistic logic axiom ax-4).  This is just ~ sp by
     another name.  (Contributed by Jim Kingdon, 31-Dec-2017.) $)
  axi4 $p |- ( A. x ph -> ph ) $=
    ( sp ) ABC $.

  $( Converse of ax-5o (intuitionistic logic axiom ax-i5r).  (Contributed by
     Jim Kingdon, 31-Dec-2017.) $)
  axi5r $p |- ( ( A. x ph -> A. x ps ) -> A. x ( A. x ph -> ps ) ) $=
    ( wal wi hba1 hbim sp imim2i alrimih ) ACDZBCDZEKBECKLCACFBCFGLBKBCHIJ $.

  $( ` x ` is not free in ` A. x ph ` (intuitionistic logic axiom ax-ial).
     (Contributed by Jim Kingdon, 31-Dec-2017.) $)
  axial $p |- ( A. x ph -> A. x A. x ph ) $=
    ( hba1 ) ABC $.

  $( ` x ` is bound in ` E. x ph ` (intuitionistic logic axiom ax-ie1).
     (Contributed by Jim Kingdon, 31-Dec-2017.) $)
  axie1 $p |- ( E. x ph -> A. x E. x ph ) $=
    ( hbe1 ) ABC $.

  $( A key property of existential quantification (intuitionistic logic axiom
     ax-ie2).  (Contributed by Jim Kingdon, 31-Dec-2017.) $)
  axie2 $p |- ( A. x ( ps -> A. x ps ) ->
              ( A. x ( ph -> ps ) <-> ( E. x ph -> ps ) ) ) $=
    ( wal wi wnf wex wb df-nf 19.23t sylbir ) BBCDECDBCFABECDACGBEHBCIABCJK $.

  $( Axiom of existence (intuitionistic logic axiom ax-i9).  In classical
     logic, this is equivalent to ~ ax-9 but in intuitionistic logic it needs
     to be stated using the existential quantifier.  (Contributed by Jim
     Kingdon, 31-Dec-2017.) $)
  axi9 $p |- E. x x = y $=
    ( a9e ) ABC $.

  $( Axiom of Quantifier Substitution (intuitionistic logic axiom ax-10).  This
     is just ~ ax10 by another name.  (Contributed by Jim Kingdon,
     31-Dec-2017.) $)
  axi10 $p |- ( A. x x = y -> A. y y = x ) $=
    ( ax10 ) ABC $.

  $( Axiom of Quantifier Introduction (intuitionistic logic axiom ax-i12).

     In classical logic, this is mostly a restatement of ~ ax12o (with one
     additional quantifier).  But in intuitionistic logic, changing the
     negations and implications to disjunctions makes it stronger.

     (Contributed by Jim Kingdon, 31-Dec-2017.) $)
  axi12 $p |- ( A. z z = x \/ ( A. z z = y \/
                A. z ( x = y -> A. z x = y ) ) ) $=
    ( weq wal wo wi nfae nfor 19.32 wn ax12o orrd orri orass mpbir mpgbi mpbi )
    CADCEZCBDCEZFZABDZUBCEGZCEZFZSTUDFFUAUCFZUECUAUCCSTCCACHCBCHIJUFSTUCFZFSUGS
    KTUCABCLMNSTUCOPQSTUDOR $.

  $( Axiom of Bundling (intuitionistic logic axiom ax-bnd).

     In classical logic, this and ~ axi12 are fairly straightforward
     consequences of ~ ax12o .  But in intuitionistic logic, it is not easy to
     add the extra ` A. x ` to ~ axi12 and so we treat the two as separate
     axioms.

     (Contributed by Jim Kingdon, 22-Mar-2018.) $)
  axbnd $p |- ( A. z z = x \/ ( A. z z = y \/
                 A. x A. z ( x = y -> A. z x = y ) ) ) $=
    ( weq wal wi wo wn wa nfnae nfan ax12o imp alrimi ex orrd orri ) CADCEZCBDC
    EZABDZTCEFZCEZAEZGRHZSUCUDSHZUCUDUEIZUBAUDUEACAAJCBAJKUFUACUDUECCACJCBCJKUD
    UEUAABCLMNNOPQ $.

