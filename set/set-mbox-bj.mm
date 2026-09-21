$[ set-main.mm $]
$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Mathbox for BJ
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#

  In this mathbox, we try to respect the ordering of the sections of the main
  part.  There are strengthenings of theorems of the main part, as well as work
  on reducing axiom dependencies.

$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Propositional calculus
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  Miscellaneous utility theorems of propositional calculus.

$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Derived rules of inference
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  In this section, we prove a few rules of inference derived from _modus
  ponens_ ~ ax-mp , and which do not depend on any other axioms.

$)

  ${
    bj-mp2c.majm $e |- ( ph -> ( ps -> ch ) ) $.
    bj-mp2c.maj $e |- ( ph -> ps ) $.
    bj-mp2c.min $e |- ph $.
    $( A double _modus ponens_ inference.  Inference associated with ~ mpd .
       (Contributed by BJ, 24-Sep-2019.) $)
    bj-mp2c $p |- ch $=
      ( ax-mp mp2 ) ABCFABFEGDH $.
  $}

  ${
    bj-mp2d.majm $e |- ( ps -> ( ph -> ch ) ) $.
    bj-mp2d.maj $e |- ( ph -> ps ) $.
    bj-mp2d.min $e |- ph $.
    $( A double _modus ponens_ inference.  Inference associated with ~ mpcom .
       (Contributed by BJ, 24-Sep-2019.) $)
    bj-mp2d $p |- ch $=
      ( ax-mp mp2 ) BACABFEGFDH $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  A syntactic theorem
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  In this section, we prove a syntactic theorem ( ~ bj-0 ) asserting that some
  formula is well-formed.  Then, we use this syntactic theorem to shorten the
  proof of a "usual" theorem ( ~ bj-1 ) and explain in the comment of that
  theorem why this phenomenon is unusual.

$)

  $( A syntactic theorem.  See the section comment and the comment of ~ bj-1 .
     The full proof (that is, with the syntactic, non-essential steps) does not
     appear on this webpage.  It has five steps and reads $= wph wps wi wch wi
     $.  The only other syntactic theorems in the main part of set.mm are ~ wel
     and ~ weq .  (Contributed by BJ, 24-Sep-2019.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  bj-0 $p wff ( ( ph -> ps ) -> ch ) $=
    ( wi ) ABDCD $.

  $( In this proof, the use of the syntactic theorem ~ bj-0 allows to reduce
     the total length by one (non-essential) step.  See also the section
     comment and the comment of ~ bj-0 .  Since ~ bj-0 is used in a
     non-essential step, this use does not appear on this webpage (but the
     present theorem appears on the webpage for ~ bj-0 as a theorem referencing
     it).  The full proof reads $= wph wps wch bj-0 id $.  (while, without
     using ~ bj-0 , it would read $= wph wps wi wch wi id $.).

     Now we explain why syntactic theorems are not useful in set.mm.  Suppose
     that the syntactic theorem thm-0 proves that PHI is a well-formed formula,
     and that thm-0 is used to shorten the proof of thm-1.  Assume that PHI
     does have proper non-atomic subformulas (which is not the case of the
     formula proved by ~ weq or ~ wel ).  Then, the proof of thm-1 does not
     construct all the proper non-atomic subformulas of PHI (if it did, then
     using thm-0 would not shorten it).  Therefore, thm-1 is a special instance
     of a more general theorem with essentially the same proof.  In the present
     case, ~ bj-1 is a special instance of ~ id .  (Contributed by BJ,
     24-Sep-2019.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  bj-1 $p |- ( ( ( ph -> ps ) -> ch ) -> ( ( ph -> ps ) -> ch ) ) $=
    ( bj-0 id ) ABCDE $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Minimal implicational calculus
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  Minimal implicational calculus, or intuitionistic implicational calculus, is
  the logical calculus with axioms ~ ax-mp , ~ ax-1 , ~ ax-2 .

$)

  ${
    bj-poni.1 $e |- ph $.
    $( Inference associated with "pon", ~ pm2.27 .  Its associated inference is
       ~ ax-mp .  (Contributed by BJ, 30-Jul-2024.) $)
    bj-poni $p |- ( ( ph -> ps ) -> ps ) $=
      ( wi pm2.27 ax-mp ) AABDBDCABEF $.
  $}

  $( When ` F. ` is substituted for ` ps ` , this formula is the Clavius law
     with a doubly negated consequent, which is therefore a minimalistic
     tautology.  Notice the non-intuitionistic proof from ~ peirce and ~ pm2.27
     chained using ~ syl .  (Contributed by BJ, 4-Dec-2023.) $)
  bj-nnclav $p |- ( ( ( ph -> ps ) -> ph ) -> ( ( ph -> ps ) -> ps ) ) $=
    ( wi id a2i ) ABCZABFDE $.

  ${
    bj-nnclavi.1 $e |- ( ( ph -> ps ) -> ph ) $.
    $( Inference associated with ~ bj-nnclav .  Its associated inference is an
       instance of ~ syl .  Notice the non-intuitionistic proof from
       ~ bj-peircei and ~ bj-poni .  (Contributed by BJ, 30-Jul-2024.) $)
    bj-nnclavi $p |- ( ( ph -> ps ) -> ps ) $=
      ( wi bj-nnclav ax-mp ) ABDZADGBDCABEF $.
  $}

  $( Commuted form of ~ bj-nnclav .  Notice the non-intuitionistic proof from
     ~ bj-peircei and ~ imim1i .  (Contributed by BJ, 30-Jul-2024.)  A proof
     which is shorter when compressed uses ~ embantd .
     (Proof modification is discouraged.) $)
  bj-nnclavc $p |- ( ( ph -> ps ) -> ( ( ( ph -> ps ) -> ph ) -> ps ) ) $=
    ( wi bj-nnclav com12 ) ABCZACFBABDE $.

  ${
    bj-nnclavci.1 $e |- ( ph -> ps ) $.
    $( Inference associated with ~ bj-nnclavc .  Its associated inference is an
       instance of ~ syl .  Notice the non-intuitionistic proof from ~ peirce
       and ~ syl .  (Contributed by BJ, 30-Jul-2024.) $)
    bj-nnclavci $p |- ( ( ( ph -> ps ) -> ph ) -> ps ) $=
      ( wi bj-nnclavc ax-mp ) ABDZGADBDCABEF $.
  $}

  ${
    bj-jarrii.1 $e |- ( ( ph -> ps ) -> ch ) $.
    bj-jarrii.2 $e |- ps $.
    $( Inference associated with ~ jarri .  Contrary to it, it does not require
       ~ ax-2 , but only ~ ax-mp and ~ ax-1 .  (Contributed by BJ,
       29-Mar-2020.)  (Proof modification is discouraged.) $)
    bj-jarrii $p |- ch $=
      ( wi a1i ax-mp ) ABFCBAEGDH $.
      $( $j usage 'bj-jarrii' avoids 'ax-2' 'ax-3'; $)
  $}

  $( The propositional function ` ( ph -> ( . -> ps ) ) ` is decreasing.
     (Contributed by BJ, 19-Jul-2019.) $)
  bj-imim21 $p |- ( ( ph -> ps ) ->
                      ( ( ch -> ( ps -> th ) ) -> ( ch -> ( ph -> th ) ) ) ) $=
    ( wi imim1 imim2d ) ABEBDEADECABDFG $.

  ${
    bj-imim21i.1 $e |- ( ph -> ps ) $.
    $( The propositional function ` ( ph -> ( . -> ps ) ) ` is decreasing.  Its
       associated inference is ~ syl5 .  (Contributed by BJ, 19-Jul-2019.) $)
    bj-imim21i $p |- ( ( ch -> ( ps -> th ) ) -> ( ch -> ( ph -> th ) ) ) $=
      ( wi bj-imim21 ax-mp ) ABFCBDFFCADFFFEABCDGH $.
  $}

  $( The propositional function ` ( ( . -> ph ) -> ps ) ` is increasing.
     (Contributed by BJ, 3-Apr-2026.) $)
  bj-imim11 $p |- ( ( ph -> ps ) ->
                      ( ( ( ph -> ch ) -> th ) -> ( ( ps -> ch ) -> th ) ) ) $=
    ( wi imim1 imim1d ) ABEBCEACEDABCFG $.

  ${
    bj-imim11i.1 $e |- ( ph -> ps ) $.
    $( The propositional function ` ( ( . -> ph ) -> ps ) ` is increasing.  Its
       associated inference is ~ wl-syls2 .  (Contributed by BJ,
       3-Apr-2026.) $)
    bj-imim11i $p |- ( ( ( ph -> ch ) -> th ) -> ( ( ps -> ch ) -> th ) ) $=
      ( wi bj-imim11 ax-mp ) ABFACFDFBCFDFFEABCDGH $.
  $}

  $( Over minimal implicational calculus, Peirce's law implies the double
     negation of the stability of any formula (that is the interpretation when
     ` F. ` is substituted for ` ps ` and for ` ch ` ).  Therefore, the double
     negation of the stability of any formula is provable in classical
     refutability calculus.  It is also provable in intuitionistic calculus
     (see iset.mm/bj-nnst) but it is not provable in minimal calculus (see
     ~ bj-stabpeirce ).  (Contributed by BJ, 30-Nov-2023.)  Axiom ~ ax-3 is
     only used through Peirce's law ~ peirce .
     (Proof modification is discouraged.) $)
  bj-peircestab $p |- ( ( ( ( ( ph -> ps ) -> ch ) -> ph ) -> ch ) -> ch ) $=
    ( wi bj-nnclav ax-1 imim2i peirce syl imim2 syl56 a1dd syl11 ) ABDZCDZADZCD
    ZCADZCDCQPDQCRPCERQAOQORNADAQPODOCOPCNFGOAHICANJABHKLMCAHI $.

  $( This minimal implicational calculus tautology is used in the following
     argument:  When ` ph , ps , ch , th , ta ` are replaced respectively by
     ` ( ph -> F. ) , F. , ph , F. , F. ` , the antecedent becomes
     ` -. -. ( -. -. ph -> ph ) ` , that is, the double negation of the
     stability of ` ph ` .  If that statement were provable in minimal
     calculus, then, since ` F. ` plays no particular role in minimal calculus,
     also the statement with ` ps ` in place of ` F. ` would be provable.  The
     corresponding consequent is ` ( ( ( ps -> ph ) -> ps ) -> ps ) ` , that
     is, the non-intuitionistic Peirce law.  Therefore, the double negation of
     the stability of any formula is not provable in minimal calculus.
     However, it is provable both in intuitionistic calculus (see
     iset.mm/bj-nnst) and in classical refutability calculus (see
     ~ bj-peircestab ).  (Contributed by BJ, 30-Nov-2023.)  (Revised by BJ,
     30-Jul-2024.)  (Proof modification is discouraged.) $)
  bj-stabpeirce $p |- ( ( ( ( ( ph -> ps ) -> ch ) -> th ) -> ta ) ->
                                          ( ( ( ps -> ch ) -> th ) -> ta ) ) $=
    ( wi jarr imim1i ) BCFZDFABFCFZDFEJIDABCGHH $.
    $( $j usage 'bj-stabpeirce' avoids 'ax-3'; $)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Positive calculus
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  Positive calculus is understood to be intuitionistic. Its primitive
  connectives are implication, equivalence, conjunction, and disjunction.
  Due to the current axiomatization of set.mm, axiom ~ ax-3 , which does not
  belong to positive calculus, may appear as a dependency of some theorems in
  this section.

$)

  $( Implication from equivalence with a conjunct.  Its associated inference is
     ~ simplbi .  (Contributed by BJ, 20-Mar-2026.) $)
  bj-bisimpl $p |- ( ( ph <-> ( ps /\ ch ) ) -> ( ph -> ps ) ) $=
    ( wa wb biimp simpl syl6 ) ABCDZEAIBAIFBCGH $.

  $( Implication from equivalence with a conjunct.  Its associated inference is
     ~ simprbi .  (Contributed by BJ, 20-Mar-2026.) $)
  bj-bisimpr $p |- ( ( ph <-> ( ps /\ ch ) ) -> ( ph -> ch ) ) $=
    ( wa wb biimp simpr syl6 ) ABCDZEAICAIFBCGH $.

  ${
    bj-syl66ib.1 $e |- ( ph -> ( ps -> th ) ) $.
    bj-syl66ib.2 $e |- ( th -> ta ) $.
    bj-syl66ib.3 $e |- ( ta <-> ch ) $.
    $( A mixed syllogism inference derived from ~ imbitrdi .  Shortens
       ~ bj-dvelimdv1 , ~ alexsubALTlem4 (4821>4812), ~ supsrlem (2868>2863).
       (Contributed by BJ, 20-Oct-2021.) $)
    bj-syl66ib $p |- ( ph -> ( ps -> ch ) ) $=
      ( syl6 imbitrdi ) ABECABDEFGIHJ $.
  $}

  $( Proof of ~ orim2 from the axiomatic definition of disjunction ( ~ olc ,
     ~ orc , ~ jao ) and minimal implicational calculus.  (Contributed by BJ,
     4-Apr-2021.)  (Proof modification is discouraged.) $)
  bj-orim2 $p |- ( ( ph -> ps ) -> ( ( ch \/ ph ) -> ( ch \/ ps ) ) ) $=
    ( wo wi orc olc imim2i jao mpsyl ) CCBDZEABEAKECADKECBFBKABCGHCKAIJ $.

  $( Curry's axiom ~ curryax (a non-intuitionistic positive statement sometimes
     called a paradox of material implication) implies Peirce's axiom ~ peirce
     over minimal implicational calculus and the axiomatic definition of
     disjunction (actually, only the elimination axiom ~ jao via its inference
     form ~ jaoi ; the introduction axioms ~ olc and ~ orc are not needed).
     Note that this theorem shows that actually, the standard instance of
     ~ curryax implies the standard instance of ~ peirce , which is not the
     case for the converse ~ bj-peircecurry .  (Contributed by BJ,
     15-Jun-2021.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  bj-currypeirce $p |-
              ( ( ph \/ ( ph -> ps ) ) -> ( ( ( ph -> ps ) -> ph ) -> ph ) ) $=
    ( wi ax-1 pm2.27 jaoi ) AABCZACZACGAHDGAEF $.

  $( Peirce's axiom ~ peirce implies Curry's axiom ~ curryax over minimal
     implicational calculus and the axiomatic definition of disjunction
     (actually, only the introduction axioms ~ olc and ~ orc ; the elimination
     axiom ~ jao is not needed).  See ~ bj-currypeirce for the converse.
     (Contributed by BJ, 15-Jun-2021.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  bj-peircecurry $p |- ( ph \/ ( ph -> ps ) ) $=
    ( wi wo orc olc peirce peirceroll ax-mp mpsyl ) AAABCZDZCZLAKEKLCZMLCZKAFLA
    CZLCLCNPACZOLAGKACACNQCABGABLHILAAHJII $.

  $( Conjunction in terms of implication and biconditional.  Note that the
     proof is intuitionistic (use of ~ ax-3 comes from the unusual definition
     of the biconditional in set.mm).  (Contributed by BJ, 23-Sep-2023.) $)
  bj-animbi $p |- ( ( ph /\ ps ) <-> ( ph <-> ( ph -> ps ) ) ) $=
    ( wa wi wb simpl pm3.4 2thd biimp pm2.43d biimpr mpd jcai impbii ) ABCZAABD
    ZEZOAPABFABGHQABQPAQABAPIJZAPKLRMN $.

  $( Curry's paradox.  Note that the proof is intuitionistic (use of ~ ax-3
     comes from the unusual definition of the biconditional in set.mm).  The
     paradox comes from the case where ` ph ` is the self-referential sentence
     "If this sentence is true, then ` ps ` ", so that one can prove
     everything.  Therefore, a consistent system cannot allow the formation of
     such self-referential sentences.  This has lead to the study of logics
     rejecting contraction ~ pm2.43 , such as affine logic and linear logic.
     (Contributed by BJ, 23-Sep-2023.)  (Proof modification is discouraged.) $)
  bj-currypara $p |- ( ( ph <-> ( ph -> ps ) ) -> ps ) $=
    ( wi wb wa bj-animbi simpr sylbir ) AABCDABEBABFABGH $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Implication and negation
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  Some theorems of propositional calculus in the language of implication and
  negation.

$)

  $( A commuted form of the contrapositive, true in minimal calculus.
     (Contributed by BJ, 19-Mar-2020.) $)
  bj-con2com $p |- ( ph -> ( ( ps -> -. ph ) -> -. ps ) ) $=
    ( wn wi con2 com12 ) BACDABCBAEF $.

  ${
    bj-con2comi.1 $e |- ph $.
    $( Inference associated with ~ bj-con2com .  Its associated inference is
       ~ mt2 .  TODO: when in the main part, add to ~ mt2 that it is the
       inference associated with ~ bj-con2comi .  (Contributed by BJ,
       19-Mar-2020.) $)
    bj-con2comi $p |- ( ( ps -> -. ph ) -> -. ps ) $=
      ( wn wi bj-con2com ax-mp ) ABADEBDECABFG $.
  $}

  $( If a formula is true, then it does not imply its negation.  (Contributed
     by BJ, 19-Mar-2020.)  A shorter proof is possible using ~ id and ~ jc ,
     however, the present proof uses theorems that are more basic than ~ jc .
     (Proof modification is discouraged.) $)
  bj-nimn $p |- ( ph -> -. ( ph -> -. ph ) ) $=
    ( wn wi pm2.01 con2i ) AABCAADE $.

  ${
    bj-nimni.1 $e |- ph $.
    $( Inference associated with ~ bj-nimn .  (Contributed by BJ,
       19-Mar-2020.) $)
    bj-nimni $p |- -. ( ph -> -. ph ) $=
      ( wn wi bj-nimn ax-mp ) AAACDCBAEF $.
  $}

  ${
    bj-peircei.1 $e |- ( ( ph -> ps ) -> ph ) $.
    $( Inference associated with ~ peirce .  (Contributed by BJ,
       30-Mar-2020.) $)
    bj-peircei $p |- ph $=
      ( wi peirce ax-mp ) ABDADACABEF $.
  $}

  ${
    bj-looinvi.1 $e |- ( ( ph -> ps ) -> ps ) $.
    $( Inference associated with ~ looinv .  Its associated inference is
       ~ bj-looinvii .  (Contributed by BJ, 30-Mar-2020.) $)
    bj-looinvi $p |- ( ( ps -> ph ) -> ph ) $=
      ( wi looinv ax-mp ) ABDBDBADADCABEF $.
  $}

  ${
    bj-looinvii.1 $e |- ( ( ph -> ps ) -> ps ) $.
    bj-looinvii.2 $e |- ( ps -> ph ) $.
    $( Inference associated with ~ bj-looinvi .  (Contributed by BJ,
       30-Mar-2020.) $)
    bj-looinvii $p |- ph $=
      ( wi bj-looinvi ax-mp ) BAEADABCFG $.
  $}

  ${
    bj-mt2bi.maj $e |- ( ps <-> -. ph ) $.
    bj-mt2bi.min $e |- ph $.
    $( Version of ~ mt2 where the major premise is a biconditional.  Shortens
       ~ fal (see ~ bj-fal ) .  Another proof is also possible via ~ con2bii
       and ~ mpbi .  The current ~ mt2bi should be relabeled, maybe to imfal.
       (Contributed by BJ, 5-Oct-2024.) $)
    bj-mt2bi $p |- -. ps $=
      ( wn biimpi mt2 ) BADBAECFG $.
  $}

  $( Shortening of ~ fal using ~ bj-mt2bi .  (Contributed by Anthony Hart,
     22-Oct-2010.)  (Proof shortened by Mel L. O'Cat, 11-Mar-2012.)
     (Proof modification is discouraged.) $)
  bj-fal $p |- -. F. $=
    ( wtru wfal df-fal tru bj-mt2bi ) ABCDE $.

  ${
    bj-ntrufal.1 $e |- ph $.
    $( The negation of a theorem is equivalent to false.  Shortens ~ dfnul2
       (see ~ bj-dfnul2 ).  (Contributed by BJ, 5-Oct-2024.) $)
    bj-ntrufal $p |- ( -. ph <-> F. ) $=
      ( wn notnoti bifal ) ACABDE $.
  $}

  $( Alternate definition of the empty set.  Definition 5.14 of [TakeutiZaring]
     p. 20.  (Contributed by NM, 26-Dec-1996.)  Remove dependency on ~ ax-10 ,
     ~ ax-11 , and ~ ax-12 .  (Revised by Steven Nguyen, 3-May-2023.)  (Proof
     shortened by BJ, 23-Sep-2024.)  (Proof modification is discouraged.) $)
  bj-dfnul2 $p |- (/) = { x | -. x = x } $=
    ( c0 wfal cab weq wn dfnul4 equid bj-ntrufal abbii eqtr4i ) BCADAAEZFZADAGM
    CALAHIJK $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Disjunction
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  A few lemmas about disjunction.  The fundamental theorems in this family are
  the dual statements ~ pm4.71 and ~ pm4.72 .
  See also ~ biort and ~ biorf .

$)

  ${
    bj-jaoi1.1 $e |- ( ph -> ps ) $.
    $( Shortens ~ orfa2 (58>53), ~ pm1.2 (20>18), ~ pm1.2 (20>18), ~ pm2.4
       (31>25), ~ pm2.41 (31>25), ~ pm2.42 (38>32), ~ pm3.2ni (43>39), ~ pm4.44
       (55>51).  (Contributed by BJ, 30-Sep-2019.) $)
    bj-jaoi1 $p |- ( ( ph \/ ps ) -> ps ) $=
      ( id jaoi ) ABBCBDE $.

    $( Shortens ~ consensus (110>106), ~ elnn0z (336>329), ~ pm1.2 (20>19),
       ~ pm3.2ni (43>39), ~ pm4.44 (55>51).  (Contributed by BJ,
       30-Sep-2019.) $)
    bj-jaoi2 $p |- ( ( ps \/ ph ) -> ps ) $=
      ( id jaoi ) BBABDCE $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Logical equivalence
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  A few other characterizations of the biconditional.  The inter-definability
  of logical connectives offers many ways to express a given statement.  Some
  useful theorems in this regard are ~ df-or , ~ df-an , ~ pm4.64 , ~ imor ,
  ~ pm4.62 through ~ pm4.67 , and, for the De Morgan laws, ~ ianor through
  ~ pm4.57 .

$)

  $( Alternate definition of the biconditional.  (Contributed by BJ,
     4-Oct-2019.) $)
  bj-dfbi4 $p |- ( ( ph <-> ps ) <-> ( ( ph /\ ps ) \/ -. ( ph \/ ps ) ) ) $=
    ( wb wa wn wo dfbi3 pm4.56 orbi2i bitri ) ABCABDZAEBEDZFKABFEZFABGLMKABHIJ
    $.

  $( Alternate definition of the biconditional.  (Contributed by BJ,
     4-Oct-2019.) $)
  bj-dfbi5 $p |- ( ( ph <-> ps ) <-> ( ( ph \/ ps ) -> ( ph /\ ps ) ) ) $=
    ( wa wo wn wb wi orcom bj-dfbi4 imor 3bitr4i ) ABCZABDZEZDNLDABFMLGLNHABIML
    JK $.

  $( Alternate definition of the biconditional.  (Contributed by BJ,
     4-Oct-2019.) $)
  bj-dfbi6 $p |- ( ( ph <-> ps ) <-> ( ( ph \/ ps ) <-> ( ph /\ ps ) ) ) $=
    ( wb wo wa wi bj-dfbi5 id animorr impbid1 biimp impbii bitri ) ABCABDZABEZF
    ZNOCZABGPQPNOPHABAIJNOKLM $.

  $( Alternate proof of ~ bijust0 ; shorter but using additional intermediate
     results.  (Contributed by NM, 11-May-1999.)  (Proof shortened by Josh
     Purinton, 29-Dec-2000.)  (Revised by BJ, 19-Mar-2020.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  bj-bijust0ALT $p |- -. ( ( ph -> ph ) -> -. ( ph -> ph ) ) $=
    ( wi id bj-nimni ) AABACD $.

  $( A self-implication does not imply the negation of a self-implication.
     Most general theorem of which ~ bijust is an instance ( ~ bijust0 and
     ~ bj-bijust0ALT are therefore also instances of it).  (Contributed by BJ,
     7-Sep-2022.) $)
  bj-bijust00 $p |- -. ( ( ph -> ph ) -> -. ( ps -> ps ) ) $=
    ( wi wn id pm3.2im mp2 ) AACZBBCZHIDCDAEBEHIFG $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  The conditional operator for propositions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( Version of ~ consensus expressed using the conditional operator.  (Remark:
     it may be better to express it as ~ consensus , using only binary
     connectives, and hinting at the fact that it is a Boolean algebra
     identity, like the absorption identities.)  (Contributed by BJ,
     30-Sep-2019.) $)
  bj-consensus $p |- ( ( if- ( ph , ps , ch ) \/ ( ps /\ ch ) ) <->
                                                      if- ( ph , ps , ch ) ) $=
    ( wif wa wo anifp bj-jaoi2 orc impbii ) ABCDZBCEZFKLKABCGHKLIJ $.

  $( Alternate proof of ~ bj-consensus .  (Contributed by BJ, 30-Sep-2019.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  bj-consensusALT $p |- ( ( if- ( ph , ps , ch ) \/ ( ps /\ ch ) ) <->
                                                      if- ( ph , ps , ch ) ) $=
    ( wif wa wo orcom wi wb anifp pm4.72 mpbi bitr4i ) ABCDZBCEZFONFZNNOGONHNPI
    ABCJONKLM $.

  ${
    $d x ph $.  $d x A $.  $d x B $.
    $( Candidate definition for the conditional operator for classes.  This is
       in line with the definition of a class as the extension of a predicate
       in ~ df-clab .  We reprove the current ~ df-if from it in ~ bj-dfif .
       (Contributed by BJ, 20-Sep-2019.)
       (Proof modification is discouraged.) $)
    bj-df-ifc $p |- if ( ph , A , B ) = { x | if- ( ph , x e. A , x e. B ) } $=
      ( cif cv wcel wa wn cab wif df-if ancom orbi12i df-ifp bitr4i abbii eqtri
      wo ) ACDEBFZCGZAHZTDGZAIZHZSZBJAUAUCKZBJABCDLUFUGBUFAUAHZUDUCHZSUGUBUHUEU
      IUAAMUCUDMNAUAUCOPQR $.
  $}

  ${
    $d x ph $.  $d x A $.  $d x B $.
    $( Alternate definition of the conditional operator for classes, which used
       to be the main definition.  (Contributed by BJ, 26-Dec-2023.)
       (Proof modification is discouraged.) $)
    bj-dfif $p |-
     if ( ph , A , B ) = { x | ( ( ph /\ x e. A ) \/ ( -. ph /\ x e. B ) ) } $=
      ( cif cv wcel wif cab wa wn wo bj-df-ifc df-ifp abbii eqtri ) ACDEABFZCGZ
      QDGZHZBIARJAKSJLZBIABCDMTUABARSNOP $.
  $}

  ${
    $d x ph $.  $d x A $.  $d x B $.  $d x X $.
    $( A biconditional connecting the conditional operator for propositions and
       the conditional operator for classes.  Note that there is no sethood
       hypothesis on ` X ` : it is implied by either side.  (Contributed by BJ,
       24-Sep-2019.)  Generalize statement from setvar ` x ` to class ` X ` .
       (Revised by BJ, 26-Dec-2023.) $)
    bj-ififc $p |-
                 ( X e. if ( ph , A , B ) <-> if- ( ph , X e. A , X e. B ) ) $=
      ( vx cif wcel cv wif cab bj-df-ifc eleq2i cvv wa wn wo df-ifp elex adantl
      eleq1 jaoi sylbi wceq ifpbi23d elab3 bitri ) DABCFZGDAEHZBGZUHCGZIZEJZGAD
      BGZDCGZIZUGULDAEBCKLUKUOEDMUOAUMNZAOZUNNZPDMGZAUMUNQUPUSURUMUSADBRSUNUSUQ
      DCRSUAUBUHDUCAUIUJUMUNUHDBTUHDCTUDUEUF $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Propositional calculus: miscellaneous
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  Miscellaneous theorems of propositional calculus.

$)

  $( Uncurried (imported) form of ~ imbi12 .  (Contributed by BJ,
     6-May-2019.) $)
  bj-imbi12 $p |- ( ( ( ph <-> ps ) /\ ( ch <-> th ) ) ->
                                         ( ( ph -> ch ) <-> ( ps -> th ) ) ) $=
    ( wb wi imbi12 imp ) ABECDEACFBDFEABCDGH $.

  $( Dual of ~ truan (which has biconditional reversed).  (Contributed by BJ,
     26-Oct-2019.)  (Proof modification is discouraged.) $)
  bj-falor $p |- ( ph <-> ( F. \/ ph ) ) $=
    ( wfal fal biorfi ) BACD $.

  $( Dual of ~ truan .  (Contributed by BJ, 26-Oct-2019.)
     (Proof modification is discouraged.) $)
  bj-falor2 $p |- ( ( F. \/ ph ) <-> ph ) $=
    ( wfal wo falim bj-jaoi1 olc impbii ) BACABAADEABFG $.

  $( A property of the biconditional.  (Contributed by BJ, 26-Oct-2019.)
     (Proof modification is discouraged.) $)
  bj-bibibi $p |- ( ph <-> ( ps <-> ( ph <-> ps ) ) ) $=
    ( wb pm5.501 bianir ex wn bibif con2bid biimprd bija impbii ) ABABCZCABDBMA
    BMABAEFBGZAMGNMAABHIJKL $.

  ${
    bj-imn3ani.1 $e |- -. ( ph /\ ps /\ ch ) $.
    $( Duplication of ~ bnj1224 .  Three-fold version of ~ imnani .
       (Contributed by Jonathan Ben-Naim, 3-Jun-2011.)  (Revised by BJ,
       22-Oct-2019.)  (Proof modification is discouraged.) $)
    bj-imn3ani $p |- ( ( ph /\ ps ) -> -. ch ) $=
      ( wa w3a df-3an mtbi imnani ) ABEZCABCFJCEDABCGHI $.
  $}

  $( Two ways of expressing a certain ternary connective.  Note the respective
     positions of the three formulas on each side of the biconditional.
     (Contributed by BJ, 6-Oct-2018.) $)
  bj-andnotim $p |- ( ( ( ph /\ -. ps ) -> ch ) <-> ( ( ph -> ps ) \/ ch ) ) $=
    ( wn wa wi wo imor iman biimpri orim1i sylbi pm2.24 imim2i impd ax-1 impbii
    jaoi ) ABDZEZCFZABFZCGZUATDZCGUCTCHUDUBCUBUDABIJKLUBUACUBASCBSCFABCMNOCTPRQ
    $.

  ${
    bj-bi3ant.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( This used to be in the main part.  (Contributed by Wolf Lammen,
       14-May-2013.)  (Revised by BJ, 14-Jun-2019.) $)
    bj-bi3ant $p |- ( ( ( th -> ta ) -> ph )
          -> ( ( ( ta -> th ) -> ps ) -> ( ( th <-> ta ) -> ch ) ) ) $=
      ( wi wb biimp imim1i biimpr imim3i syl2im ) DEGZAGDEHZAGEDGZBGOBGOCGONADE
      IJOPBDEKJABCOFLM $.
  $}

  $( This used to be in the main part.  (Contributed by Wolf Lammen,
     14-May-2013.)  (Revised by BJ, 14-Jun-2019.) $)
  bj-bisym $p |- ( ( ( ph -> ps ) -> ( ch -> th ) ) -> ( ( ( ps -> ph )
        -> ( th -> ch ) ) -> ( ( ph <-> ps ) -> ( ch <-> th ) ) ) ) $=
    ( wi wb impbi bj-bi3ant ) CDEDCECDFABCDGH $.

  $( Equivalence of two ternary operations.  Note the identical order and
     parenthesizing of the three arguments in both expressions.  (Contributed
     by BJ, 31-Dec-2023.) $)
  bj-bixor $p |- ( ( ph <-> ( ps \/_ ch ) ) <-> ( ph \/_ ( ps <-> ch ) ) ) $=
    ( wb wn wxo pm5.18 con2bii df-xor bibi2i 3bitr4i ) ABCDZEZDZALDZEABCFZDALFO
    NALGHPMABCIJALIK $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Modal logic
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  In this section, we prove some theorems related to modal logic.  For modal
  logic, we refer to ~ https://en.wikipedia.org/wiki/Kripke_semantics ,
  ~ https://en.wikipedia.org/wiki/Modal_logic and
  ~ https://plato.stanford.edu/entries/logic-modal/ .

  Monadic first-order logic (i.e., with quantification over only one variable)
  is bi-interpretable with modal logic, by mapping ` A. x ` to "necessity"
  (generally denoted by a box) and ` E. x ` to "possibility" (generally denoted
  by a diamond).  Therefore, we use these quantifiers so as not to introduce
  new symbols.  (To be strictly within modal logic, we should add disjoint
  variable conditions between ` x ` and any other metavariables appearing in
  the statements.)

  For instance, ~ ax-gen corresponds to the necessitation rule of modal logic,
  and ~ ax-4 corresponds to the distributivity axiom (K) of modal logic, also
  called the Kripke scheme.  Modal logics satisfying these rule and axiom are
  called "normal modal logics", of which the most important modal logics are.

  The minimal normal modal logic is also denoted by (K).
  Here are a few normal modal logics with their axiomatizations (on top of
  (K)):
  (K) axiomatized by no supplementary axioms;
  (T) axiomatized by the axiom T;
  (K4) axiomatized by the axiom 4;
  (S4) axiomatized by the axioms T,4;
  (S5) axiomatized by the axioms T,5 or D,B,4;
  (GL) axiomatized by the axiom GL.

  The last one, called G&ouml;del&ndash;L&ouml;b logic or provability logic, is
  important because it describes exactly the properties of provability in Peano
  arithmetic, as proved by Robert Solovay.  See for instance
  ~ https://plato.stanford.edu/entries/logic-provability/ .
  A basic result in this logic is ~ bj-gl4 .

$)

  $( This implication, proved using only ~ ax-gen and ~ ax-4 on top of
     propositional calculus (hence holding, up to the standard interpretation,
     in any normal modal logic), shows that the axiom scheme ` |- E. x T. `
     implies the axiom scheme ` |- ( A. x ph -> E. x ph ) ` .  These correspond
     to the modal axiom (D), and in predicate calculus, they assert that the
     universe of discourse is nonempty.  For the converse, see ~ bj-axd2d .
     (Contributed by BJ, 16-May-2019.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  bj-axdd2 $p |- ( E. x ph -> ( A. x ps -> E. x ps ) ) $=
    ( wal wex wi ala1 exim syl com12 ) BCDZACEZBCEZKABFCDLMFBACGABCHIJ $.

  $( This implication, proved using only ~ ax-gen on top of propositional
     calculus (hence holding, up to the standard interpretation, in any modal
     logic), shows that the axiom scheme ` |- ( A. x ph -> E. x ph ) ` implies
     the axiom scheme ` |- E. x T. ` (substitute ` T. ` for ` ph ` ).  These
     correspond to the modal axiom (D), and in predicate calculus, they assert
     that the universe of discourse is nonempty.  For the converse, see
     ~ bj-axdd2 .  (Contributed by BJ, 16-May-2019.)  Generalize from its
     instance with ` T. ` substituted for ` ph ` .  (Revised by BJ,
     20-Mar-2022.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  bj-axd2d $p |- ( ( A. x T. -> E. x ph ) -> E. x ph ) $=
    ( wtru wal wex wi pm2.27 tru mpg ) CCBDZABEZFKFBJKGHI $.

  $( This implication, proved from propositional calculus only (hence holding,
     up to the standard interpretation, in any modal logic), shows that the
     axiom scheme ` |- ( A. x ph -> ph ) ` (modal T) implies the axiom scheme
     ` |- ( A. x ph -> E. x ph ) ` (modal D).  See also ~ bj-axdd2 and
     ~ bj-axd2d .  (Contributed by BJ, 16-May-2019.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  bj-axtd $p |- ( ( A. x -. ph -> -. ph ) ->
                           ( ( A. x ph -> ph ) -> ( A. x ph -> E. x ph ) ) ) $=
    ( wn wal wi wex con2 df-ex imbitrrdi imim2d ) ACZBDZKEZAABFZABDMALCNLAGABHI
    J $.

  $( In a normal modal logic, the modal axiom GL implies the modal axiom (4).
     Translated to first-order logic, Axiom GL reads
     ` |- ( A. x ( A. x ph -> ph ) -> A. x ph ) ` .  Note that the antecedent
     of ~ bj-gl4 is an instance of the axiom GL, with ` ph ` replaced by
     ` ( A. x ph /\ ph ) ` , which is a modality sometimes called the "strong
     necessity" of ` ph ` .  (Contributed by BJ, 12-Dec-2019.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  bj-gl4 $p |- ( ( A. x ( A. x ( A. x ph /\ ph ) -> ( A. x ph /\ ph ) ) ->
                   A. x ( A. x ph /\ ph ) ) -> ( A. x ph -> A. x A. x ph ) ) $=
    ( wal wa wi 19.26 simpr a1i anc2ri biimtrid alimi biimpi imim12i simpl syl6
    ) ABCZADZBCZQEZBCZREPPBCZPDZUAPTRUBASBRUBAQPABFZAUBPUBPEAUAPGHIJKRUBUCLMUAP
    NO $.

  $( Over minimal calculus, the modal axiom (4) ( ~ hba1 ) and the modal axiom
     (K) ( ~ ax-4 ) together imply ~ axc4 .  (Contributed by BJ, 29-Nov-2020.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  bj-axc4 $p |- ( ( A. x ph -> A. x A. x ph ) ->
                ( ( A. x ( A. x ph -> ps ) -> ( A. x A. x ph -> A. x ps ) ) ->
                    ( A. x ( A. x ph -> ps ) -> ( A. x ph -> A. x ps ) ) ) ) $=
    ( wal wi bj-imim21 ) ACDZGCDGBECDBCDF $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Provability logic
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  In this section, we assume that, on top of propositional calculus, there is
  given a provability predicate ` Prv ` satisfying the three axioms ~ ax-prv1
  and ~ ax-prv2 and ~ ax-prv3 .  Note the similarity with ~ ax-gen , ~ ax-4 and
  ~ hba1 respectively.  These three properties of ` Prv ` are often called the
  Hilbert&ndash;Bernays&ndash;L&ouml;b derivability conditions, or the
  Hilbert&ndash;Bernays provability conditions.

  This corresponds to the modal logic (K4) (see previous section for modal
  logic).  The interpretation of provability logic is the following: we are
  given a background first-order theory T, the wff ` Prv ph ` means " ` ph ` is
  provable in T", and the turnstile ` |- ` indicates provability in T.

  Beware that "provability logic" often means (K) augmented with the
  G&ouml;del&ndash;L&ouml;b axiom GL, which we do not assume here (at least for
  the moment).  See for instance
  ~ https://plato.stanford.edu/entries/logic-provability/ .

  Provability logic is worth studying because whenever T is a first-order
  theory containing Robinson arithmetic (a fragment of Peano arithmetic), one
  can prove (using G&ouml;del numbering, and in the much weaker primitive
  recursive arithmetic) that there exists in T a provability predicate ` Prv `
  satisfying the above three axioms.  (We do not construct this predicate in
  this section; this is still a project.)

  The main theorems of this section are the "easy parts" of the proofs of
  G&ouml;del's second incompleteness theorem ( ~ bj-babygodel ) and L&ouml;b's
  theorem ( ~ bj-babylob ).  See the comments of these theorems for details.

$)

  $c Prv $.

  $( Syntax for the provability predicate. $)
  cprvb $a wff Prv ph $.

  $( Register the provability predicate as a primitive expression (lacking a
     definition). $)
  $( $j primitive 'cprvb'; $)

  ${
    ax-prv1.1 $e |- ph $.
    $( First property of three of the provability predicate.  (Contributed by
       BJ, 3-Apr-2019.) $)
    ax-prv1 $a |- Prv ph $.
  $}

  $( Second property of three of the provability predicate.  (Contributed by
     BJ, 3-Apr-2019.) $)
  ax-prv2 $a |- ( Prv ( ph -> ps ) -> ( Prv ph -> Prv ps ) ) $.

  $( Third property of three of the provability predicate.  (Contributed by BJ,
     3-Apr-2019.) $)
  ax-prv3 $a |- ( Prv ph -> Prv Prv ph ) $.

  ${
    prvlem1.1 $e |- ( ph -> ps ) $.
    $( An elementary property of the provability predicate.  (Contributed by
       BJ, 3-Apr-2019.) $)
    prvlem1 $p |- ( Prv ph -> Prv ps ) $=
      ( wi cprvb ax-prv1 ax-prv2 ax-mp ) ABDZEAEBEDICFABGH $.
  $}

  ${
    prvlem2.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( An elementary property of the provability predicate.  (Contributed by
       BJ, 3-Apr-2019.) $)
    prvlem2 $p |- ( Prv ph -> ( Prv ps -> Prv ch ) ) $=
      ( cprvb wi prvlem1 ax-prv2 syl ) AEBCFZEBECEFAJDGBCHI $.
  $}

  ${
    bj-babygodel.s $e |- ( ph <-> -. Prv ph ) $.
    bj-babygodel.1 $e |- -. Prv F. $.
    $( See the section header comments for the context.

       The first hypothesis reads " ` ph ` is true if and only if it is not
       provable in T" (and having this first hypothesis means that we can prove
       this fact in T).  The wff ` ph ` is a formal version of the sentence
       "This sentence is not provable".  The hard part of the proof of
       G&ouml;del's theorem is to construct such a ` ph ` , called a
       "G&ouml;del&ndash;Rosser sentence", for a first-order theory T which is
       effectively axiomatizable and contains Robinson arithmetic, through
       G&ouml;del diagonalization (this can be done in primitive recursive
       arithmetic).  The second hypothesis means that ` F. ` is not provable in
       T, that is, that the theory T is consistent (and having this second
       hypothesis means that we can prove in T that the theory T is
       consistent).  The conclusion is the falsity, so having the conclusion
       means that T can prove the falsity, that is, T is inconsistent.

       Therefore, taking the contrapositive, this theorem expresses that if a
       first-order theory is consistent (and one can prove in it that some
       formula is true if and only if it is not provable in it), then this
       theory does not prove its own consistency.

       This proof is due to George Boolos, _G&ouml;del's Second Incompleteness
       Theorem Explained in Words of One Syllable_, Mind, New Series, Vol. 103,
       No. 409 (January 1994), pp. 1--3.

       (Contributed by BJ, 3-Apr-2019.) $)
    bj-babygodel $p |- F. $=
      ( wfal cprvb wn ax-prv1 biimpi prvlem1 ax-prv3 pm2.21 prvlem2 sylc sylibr
      con3i mp2b pm2.24ii ) DEZDRFZEAEZRSCGSASTFZATRTUAETERAUAAUABHIAJUATDTDKLM
      ZOBNIUBPCQ $.
  $}

  ${
    bj-babylob.s $e |- ( ps <-> ( Prv ps -> ph ) ) $.
    bj-babylob.1 $e |- ( Prv ph -> ph ) $.
    $( See the section header comments for the context, as well as the comments
       for ~ bj-babygodel .

       L&ouml;b's theorem when the L&ouml;b sentence is given as a hypothesis
       (the hard part of the proof of L&ouml;b's theorem is to construct this
       L&ouml;b sentence; this can be done, using G&ouml;del diagonalization,
       for any first-order effectively axiomatizable theory containing Robinson
       arithmetic).  More precisely, the present theorem states that if a
       first-order theory proves that the provability of a given sentence
       entails its truth (and if one can construct in this theory a provability
       predicate and a L&ouml;b sentence, given here as the first hypothesis),
       then the theory actually proves that sentence.

       See for instance, Eliezer Yudkowsky, _The Cartoon Guide to L&ouml;b's
       Theorem_ (available at ~ http://yudkowsky.net/rational/lobs-theorem/ ).

       (Contributed by BJ, 20-Apr-2019.) $)
    bj-babylob $p |- ph $=
      ( cprvb wi ax-prv3 biimpi prvlem2 mpd syl mpbir ax-prv1 ax-mp ) BEZABBOAF
      ZOAEZAOOEQBGBOABPCHIJDKZCLMRN $.
  $}

  ${
    bj-godellob.s $e |- ( ph <-> -. Prv ph ) $.
    bj-godellob.1 $e |- -. Prv F. $.
    $( Proof of G&ouml;del's theorem from L&ouml;b's theorem (see comments at
       ~ bj-babygodel and ~ bj-babylob for details).  (Contributed by BJ,
       20-Apr-2019.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    bj-godellob $p |- F. $=
      ( wfal cprvb wn wi dfnot bitri pm2.21i bj-babylob ) DAAAEZFLDGBLHIDEDCJK
      $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  First-order logic
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  Utility lemmas or strengthenings of theorems in the main part (biconditional
  or closed forms, or fewer disjoint variable conditions, or disjoint variable
  conditions replaced with nonfreeness hypotheses...).  Sorted in the same
  order as in the main part.

$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Universal and existential quantifiers, nonfreeness predicate
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( A lemma for changing bound variables.  Only the forward implication is
     intuitionistic.  (Contributed by BJ, 14-Mar-2026.) $)
  bj-exexalal $p |-
                 ( ( E. x ph -> E. y ps ) <-> ( A. y -. ps -> A. x -. ph ) ) $=
    ( wex wi wn wal con34b alnex imbi12i bitr4i ) ACEZBDEZFNGZMGZFBGDHZAGCHZFMN
    IQORPBDJACJKL $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Adding ax-gen
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    bj-genr.1 $e |- ( ph /\ ps ) $.
    $( Generalization rule on the right conjunct.  See ~ 19.28 .  (Contributed
       by BJ, 7-Jul-2021.) $)
    bj-genr $p |- ( ph /\ A. x ps ) $=
      ( wal simpli simpri ax-gen pm3.2i ) ABCEABDFBCABDGHI $.

    $( Generalization rule on the left conjunct.  See ~ 19.27 .  (Contributed
       by BJ, 7-Jul-2021.) $)
    bj-genl $p |- ( A. x ph /\ ps ) $=
      ( wal simpli ax-gen simpri pm3.2i ) ACEBACABDFGABDHI $.

    $( Generalization rule on a conjunction.  Forward inference associated with
       ~ 19.26 .  (Contributed by BJ, 7-Jul-2021.) $)
    bj-genan $p |- ( A. x ph /\ A. x ps ) $=
      ( wal simpli ax-gen simpri pm3.2i ) ACEBCEACABDFGBCABDHGI $.
  $}

  ${
    bj-mpgs.maj $e |- ( ( ph /\ A. x ph ) -> ps ) $.
    bj-mpgs.min $e |- ph $.
    $( From a closed form theorem (the major premise) with an antecedent in the
       "strong necessity" modality (in the language of modal logic), deduce the
       associated inference.  Strong necessity is stronger than necessity, and
       equivalent to it when ~ sp (modal T) is available.  Therefore, this
       theorem is stronger than ~ mpg , and strictly stronger when ~ sp is not
       available.  (Contributed by BJ, 1-Nov-2023.) $)
    bj-mpgs $p |- ps $=
      ( wal ax-gen mp2an ) AACFBEACEGDH $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Adding ax-4
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

$( *** ax-gen not required *** $)

  ${
    bj-almp.maj $e |- A. x ( ps -> ph ) $.
    bj-almp.min $e |- A. x ps $.
    $( A quantified form of ~ ax-mp .  See also ~ barbara , ~ bj-ala1i ,
       ~ bj-almpi .  (Contributed by BJ, 19-Mar-2026.) $)
    bj-almp $p |- A. x ph $=
      ( wi wal alim mp2 ) BAFCGBCGACGDEBACHI $.
  $}

  $( Stronger form of ~ sylgt , closer to ~ ax-2 .  (Contributed by BJ,
     30-Jul-2025.) $)
  bj-sylggt $p |- ( ( ph -> A. x ( ps -> ch ) ) -> ( ( ph -> A. x ps ) ->
                                                       ( ph -> A. x ch ) ) ) $=
    ( wi wal alim imim3i ) BCEDFBDFCDFABCDGH $.

  $( The general form of the *alrim* family of theorems: if ` ph ` is
     substituted for ` ps ` , then the antecedent expresses a form of
     nonfreeness of ` x ` in ` ph ` , so the theorem means that under a
     nonfreeness condition in an antecedent, one can deduce from the
     universally quantified implication an implication where the consequent is
     universally quantified.  Dual of ~ bj-exlimg .  (Contributed by BJ,
     9-Dec-2023.) $)
  bj-alrimg $p |-
         ( ( ph -> A. x ps ) -> ( A. x ( ps -> ch ) -> ( ph -> A. x ch ) ) ) $=
    ( wi wal sylgt com12 ) BCEDFABDFEACDFEABCDGH $.

  $( Uncurried (imported) form of ~ sylgt .  (Contributed by BJ,
     2-May-2019.) $)
  bj-sylgt2 $p |- ( ( A. x ( ps -> ch ) /\ ( ph -> A. x ps ) ) ->
                                                         ( ph -> A. x ch ) ) $=
    ( wi wal sylgt imp ) BCEDFABDFEACDFEABCDGH $.

  $( Closed form of ~ nexdh (actually, its general instance).  (Contributed by
     BJ, 6-May-2019.) $)
  bj-nexdh $p |- ( A. x ( ph -> -. ps ) ->
                             ( ( ch -> A. x ph ) -> ( ch -> -. E. x ps ) ) ) $=
    ( wn wi wal wex sylgt alnex syl8ib ) ABEZFDGCADGFCLDGBDHECALDIBDJK $.

  $( Uncurried (imported) form of ~ bj-nexdh .  (Contributed by BJ,
     6-May-2019.) $)
  bj-nexdh2 $p |- ( ( A. x ( ph -> -. ps ) /\ ( ch -> A. x ph ) ) ->
                                                      ( ch -> -. E. x ps ) ) $=
    ( wn wi wal wex bj-nexdh imp ) ABEFDGCADGFCBDHEFABCDIJ $.

$( *** ax-gen required *** $)

  ${
    bj-alimii.maj $e |- ( ps -> ph ) $.
    bj-alimii.min $e |- A. x ps $.
    $( Inference associated with ~ alimi .  Double inference associated with
       ~ alim .  The usual proof of an associated inference (here from ~ alimi
       and ~ ax-mp ) has the same size and same number of steps.  (Contributed
       by BJ, 19-Mar-2026.) $)
    bj-alimii $p |- A. x ph $=
      ( wi ax-gen bj-almp ) ABCBAFCDGEH $.
  $}

  ${
    bj-ala1i.1 $e |- A. x ph $.
    $( Add an antecedent in a universally quantified formula.  Inference
       associated with ~ ala1 .  (Contributed by BJ, 6-Oct-2018.) $)
    bj-ala1i $p |- A. x ( ps -> ph ) $=
      ( wal wi ala1 ax-mp ) ACEBAFCEDABCGH $.
  $}

  ${
    bj-almpi.maj $e |- A. x ( ph -> ( ch -> ps ) ) $.
    bj-almpi.min $e |- A. x ch $.
    $( A quantified form of ~ mpi .  See also ~ barbara , ~ bj-ala1i ,
       ~ bj-almp .  (Contributed by BJ, 19-Mar-2026.) $)
    bj-almpi $p |- A. x ( ph -> ps ) $=
      ( wi wal pm2.04 alimi ax-mp bj-almp ) ABGZCDACBGGZDHCMGZDHENODACBIJKFL $.
  $}

  ${
    bj-almpig.maj $e |- ( ph -> ( ch -> ps ) ) $.
    bj-almpig.min $e |- A. x ch $.
    $( A partially quantified form of ~ mpi similar to ~ bj-almpi .
       (Contributed by BJ, 19-Mar-2026.) $)
    bj-almpig $p |- A. x ( ph -> ps ) $=
      ( wi ax-gen bj-almpi ) ABCDACBGGDEHFI $.
  $}

  $( Syllogism under the universal quantifier, in the curried form appearing as
     Theorem *10.3 of [WhiteheadRussell] p. 145.  See ~ alsyl for the uncurried
     form.  (Contributed by BJ, 28-Mar-2026.) $)
  bj-alsyl $p |- ( A. x ( ph -> ps ) ->
                                ( A. x ( ps -> ch ) -> A. x ( ph -> ch ) ) ) $=
    ( wi imim1 al2imi ) ABEBCEACEDABCFG $.

  $( Closed form of ~ 2alimi .  (Contributed by BJ, 6-May-2019.) $)
  bj-2alim $p |- ( A. x A. y ( ph -> ps ) ->
                                          ( A. x A. y ph -> A. x A. y ps ) ) $=
    ( wi wal alim al2imi ) ABEDFADFBDFCABDGH $.

  ${
    bj-alimdh.nf $e |- ( ph -> A. x ps ) $.
    bj-alimdh.maj $e |- ( ps -> ( ch -> th ) ) $.
    $( General instance of ~ alimdh .  (Contributed by NM, 4-Jan-2002.)  State
       the most general derivable instance.  (Revised by BJ, 5-Apr-2026.) $)
    bj-alimdh $p |- ( ph -> ( A. x ch -> A. x th ) ) $=
      ( wal wi al2imi syl ) ABEHCEHDEHIFBCDEGJK $.
  $}

  ${
    bj-alrimdh.nf1 $e |- ( ph -> A. x ps ) $.
    bj-alrimdh.nf2 $e |- ( ch -> A. x th ) $.
    bj-alrimdh.maj $e |- ( ps -> ( th -> ta ) ) $.
    $( Deduction form of Theorem 19.21 of [Margaris] p. 90, see ~ 19.21 and
       ~ 19.21h .  (Contributed by NM, 10-Feb-1997.)  (Proof shortened by
       Andrew Salmon, 13-May-2011.)  State the most general derivable instance.
       (Revised by BJ, 5-Apr-2026.) $)
    bj-alrimdh $p |- ( ph -> ( ch -> A. x ta ) ) $=
      ( wal bj-alimdh syl5 ) CDFJAEFJHABDEFGIKL $.
  $}

  ${
    bj-alrimd.ph $e |- ( ph -> A. x ps ) $.
    bj-alrimd.th $e |- ( ph -> ( ch -> A. x th ) ) $.
    bj-alrimd.maj $e |- ( ps -> ( th -> ta ) ) $.
    $( A slightly more general ~ alrimd .  A common usage will have ` ph `
       substituted for ` ps ` and ` ch ` substituted for ` th ` , giving a form
       closer to ~ alrimd .  (Contributed by BJ, 25-Dec-2023.) $)
    bj-alrimd $p |- ( ph -> ( ch -> A. x ta ) ) $=
      ( wal wi sylg bj-alrimg sylc ) ACDFJKDEKZFJCEFJKHABOFGILCDEFMN $.
  $}

  ${
    bj-exa1i.1 $e |- E. x ph $.
    $( Add an antecedent in an existentially quantified formula.  Inference
       associated with ~ exa1 .  (Contributed by BJ, 6-Oct-2018.) $)
    bj-exa1i $p |- E. x ( ps -> ph ) $=
      ( wex wi exa1 ax-mp ) ACEBAFCEDABCGH $.
  $}

  $( Closed form of ~ alanimi .  (Contributed by BJ, 6-May-2019.) $)
  bj-alanim $p |- ( A. x ( ( ph /\ ps ) -> ch ) ->
                                     ( ( A. x ph /\ A. x ps ) -> A. x ch ) ) $=
    ( wa wi wal pm3.3 alimi al2im syl impd ) ABECFZDGZADGZBDGZCDGZNABCFFZDGOPQF
    FMRDABCHIABCDJKL $.

  $( Closed form of ~ 2albii .  (Contributed by BJ, 6-May-2019.) $)
  bj-2albi $p |- ( A. x A. y ( ph <-> ps ) ->
                                         ( A. x A. y ph <-> A. x A. y ps ) ) $=
    ( wb wal albi alimi syl ) ABEDFZCFADFZBDFZEZCFKCFLCFEJMCABDGHKLCGI $.

  ${
    bj-notalbii.1 $e |- ( ph <-> ps ) $.
    $( Equivalence of universal quantification of negation of equivalent
       formulas.  Shortens ~ ab0 (103>94), ~ ballotlem2 (2655>2648), ~ bnj1143
       (522>519), ~ hausdiag (2119>2104).  (Contributed by BJ, 17-Jul-2021.) $)
    bj-notalbii $p |- ( A. x -. ph <-> A. x -. ps ) $=
      ( wn notbii albii ) AEBECABDFG $.
  $}

  $( Closed form of ~ 2eximi .  (Contributed by BJ, 6-May-2019.) $)
  bj-2exim $p |- ( A. x A. y ( ph -> ps ) ->
                                          ( E. x E. y ph -> E. x E. y ps ) ) $=
    ( wi wal wex exim aleximi ) ABEDFADGBDGCABDHI $.

  $( Closed form of ~ 2exbii .  (Contributed by BJ, 6-May-2019.) $)
  bj-2exbi $p |- ( A. x A. y ( ph <-> ps ) ->
                                         ( E. x E. y ph <-> E. x E. y ps ) ) $=
    ( wb wal wex exbi alexbii ) ABEDFADGBDGCABDHI $.

  $( Closed form of ~ 3exbii .  (Contributed by BJ, 6-May-2019.) $)
  bj-3exbi $p |- ( A. x A. y A. z ( ph <-> ps ) ->
                               ( E. x E. y E. z ph <-> E. x E. y E. z ps ) ) $=
    ( wb wal wex exbi 2alimi bj-2exbi syl ) ABFEGZDGCGAEHZBEHZFZDGCGNDHCHODHCHF
    MPCDABEIJNOCDKL $.

  $( Dual statement of ~ sylgt .  Closed form of ~ bj-sylge .  (Contributed by
     BJ, 2-May-2019.) $)
  bj-sylget $p |-
         ( A. x ( ch -> ph ) -> ( ( E. x ph -> ps ) -> ( E. x ch -> ps ) ) ) $=
    ( wi wal wex exim imim1d ) CAEDFCDGADGBCADHI $.

  $( Uncurried (imported) form of ~ bj-sylget .  (Contributed by BJ,
     2-May-2019.) $)
  bj-sylget2 $p |- ( ( A. x ( ph -> ps ) /\ ( E. x ps -> ch ) ) ->
                                                         ( E. x ph -> ch ) ) $=
    ( wi wal wex bj-sylget imp ) ABEDFBDGCEADGCEBCADHI $.

  $( The general form of the *exlim* family of theorems: if ` ph ` is
     substituted for ` ps ` , then the antecedent expresses a form of
     nonfreeness of ` x ` in ` ph ` , so the theorem means that under a
     nonfreeness condition in a consequent, one can deduce from the universally
     quantified implication an implication where the antecedent is
     existentially quantified.  Dual of ~ bj-alrimg .  (Contributed by BJ,
     9-Dec-2023.) $)
  bj-exlimg $p |-
         ( ( E. x ph -> ps ) -> ( A. x ( ch -> ph ) -> ( E. x ch -> ps ) ) ) $=
    ( wi wal wex bj-sylget com12 ) CAEDFADGBECDGBEABCDHI $.

  ${
    bj-sylge.nf $e |- ( E. x ph -> ps ) $.
    bj-sylge.maj $e |- ( ch -> ph ) $.
    $( Dual statement of ~ sylg (the final "e" in the label stands for
       "existential (version of ~ sylg )".  Variant of ~ exlimih .
       (Contributed by BJ, 25-Dec-2023.) $)
    bj-sylge $p |- ( E. x ch -> ps ) $=
      ( wex eximi syl ) CDGADGBCADFHEI $.
  $}

  ${
    bj-exlimd.ph $e |- ( ph -> A. x ps ) $.
    bj-exlimd.th $e |- ( ph -> ( E. x th -> ta ) ) $.
    bj-exlimd.maj $e |- ( ps -> ( ch -> th ) ) $.
    $( A slightly more general ~ exlimd .  A common usage will have ` ph `
       substituted for ` ps ` and ` th ` substituted for ` ta ` , giving a form
       closer to ~ exlimd .  (Contributed by BJ, 25-Dec-2023.) $)
    bj-exlimd $p |- ( ph -> ( E. x ch -> ta ) ) $=
      ( wex wi wal sylg bj-exlimg sylc ) ADFJEKCDKZFLCFJEKHABPFGIMDECFNO $.
  $}

  $( A weak from of nonfreeness in either an antecedent or a consequent implies
     that a universally quantified implication is equivalent to the associated
     implication where the antecedent is existentially quantified and the
     consequent is universally quantified.  The forward implication always
     holds (this is ~ 19.38 ) and the converse implication is the join of
     instances of ~ bj-alrimg and ~ bj-exlimg (see ~ 19.38a and ~ 19.38b ).
     TODO: prove a version where the antecedents use the nonfreeness
     quantifier.  (Contributed by BJ, 9-Dec-2023.) $)
  bj-nfimexal $p |- ( ( ( E. x ph -> A. x ph ) \/ ( E. x ps -> A. x ps ) ) ->
                          ( ( E. x ph -> A. x ps ) <-> A. x ( ph -> ps ) ) ) $=
    ( wex wal wi wo 19.38 bj-alrimg bj-exlimg jaoi impbid2 ) ACDZACEFZBCDBCEZFZ
    GMOFZABFCEZABCHNRQFPMABCIBOACJKL $.

  $( Theorem 19.22 of [Margaris] p. 90.  (Contributed by NM, 10-Jan-1993.)
     (Proof shortened by Wolf Lammen, 4-Jul-2014.)  Prove it directly from
     ~ alim to allow use in ~ bj-alexim .  (Revised by BJ, 9-Dec-2023.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  bj-exim $p |- ( A. x ( ph -> ps ) -> ( E. x ph -> E. x ps ) ) $=
    ( wi wal wn wex con3 alimi alim 3syl df-ex 3imtr4g ) ABDZCEZAFZCEZFZBFZCEZF
    ZACGBCGOSPDZCETQDRUADNUBCABHISPCJTQHKACLBCLM $.

  $( Closed form of ~ aleximi .  Note: this proof is shorter, so ~ aleximi
     could be deduced from it ( ~ exim would have to be proved first, see
     ~ bj-exim ).  (Contributed by BJ, 8-Nov-2021.) $)
  bj-alexim $p |-
    ( A. x ( ph -> ( ps -> ch ) ) -> ( A. x ph -> ( E. x ps -> E. x ch ) ) ) $=
    ( wi wal wex alim exim syl6 ) ABCEZEDFADFKDFBDGCDGEAKDHBCDIJ $.

  ${
    bj-aleximiALT.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Alternate proof of ~ aleximi from ~ exim , which is sometimes used as an
       axiom in instuitionistic modal logic.  (Contributed by BJ, 9-Dec-2023.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    bj-aleximiALT $p |- ( A. x ph -> ( E. x ps -> E. x ch ) ) $=
      ( wal wi wex alimi exim syl ) ADFBCGZDFBDHCDHGALDEIBCDJK $.
  $}

  $( Closed form of ~ hbxfrbi .  Note: it is less important than ~ nfbiit .
     The antecedent is in the "strong necessity" modality of modal logic (see
     also ~ bj-nnftht ) in order not to require ~ sp (modal T).  See
     ~ bj-hbyfrbi for its version with existential quantifiers.  (Contributed
     by BJ, 6-May-2019.) $)
  bj-hbxfrbi $p |- ( ( ( ph <-> ps ) /\ A. x ( ph <-> ps ) ) ->
                               ( ( ph -> A. x ph ) <-> ( ps -> A. x ps ) ) ) $=
    ( wb wal wa simpl albi adantl imbi12d ) ABDZKCEZFABACEZBCEZKLGLMNDKABCHIJ
    $.

  $( Version of ~ bj-hbxfrbi with existential quantifiers.  (Contributed by BJ,
     23-Aug-2023.) $)
  bj-hbyfrbi $p |- ( ( ( ph <-> ps ) /\ A. x ( ph <-> ps ) ) ->
                               ( ( E. x ph -> ph ) <-> ( E. x ps -> ps ) ) ) $=
    ( wb wal wa wex exbi adantl simpl imbi12d ) ABDZLCEZFACGZBCGZABMNODLABCHILM
    JK $.

  $( Distribute quantifiers over a nested implication.

     This and the following theorems are the general instances of already
     proved theorems.  They could be moved to the main part, before ~ ax-5 .  I
     propose to move to the main part: ~ bj-exalim , ~ bj-exalimi ,
     ~ bj-eximcom ~ bj-exalims , ~ bj-exalimsi , ~ bj-ax12i , ~ bj-ax12wlem ,
     ~ bj-ax12w .  A new label is needed for ~ bj-ax12i and label suggestions
     are welcome for the others.  I also propose to change ` -. A. x -. ` to
     ` E. x ` in ~ speimfw and ~ spimfw (other spim* theorems use ` E. x ` and
     very few theorems in set.mm use ` -. A. x -. ` ).  (Contributed by BJ,
     8-Nov-2021.) $)
  bj-exalim $p |- ( A. x ( ph -> ( ps -> ch ) ) ->
                                   ( E. x ph -> ( A. x ps -> E. x ch ) ) ) $=
    ( wi wal wex pm2.04 alimi bj-alexim 3syl ) ABCEEZDFBACEEZDFBDFZADGZCDGZEEON
    PEELMDABCHIBACDJNOPHK $.

  ${
    bj-exalimi.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( An inference for distributing quantifiers over a nested implication.
       The canonical derivation from its closed form ~ bj-exalim (using ~ mpg )
       has fewer essential steps, but more steps in total (yielding a longer
       compressed proof).  (Almost) the general statement that ~ speimfw
       proves.  (Contributed by BJ, 29-Sep-2019.) $)
    bj-exalimi $p |- ( E. x ph -> ( A. x ps -> E. x ch ) ) $=
      ( wal wex com12 aleximi ) BDFADGCDGBACDABCEHIH $.
  $}

  $( A commuted form of ~ exim which is sometimes posited as an axiom in
     instuitionistic modal logic.  Forward implication of ~ 19.35 .  Its
     converse is not intuitionistic.  (Contributed by BJ, 9-Dec-2023.) $)
  bj-eximcom $p |- ( E. x ( ph -> ps ) -> ( A. x ph -> E. x ps ) ) $=
    ( wal wi wex pm2.27 aleximi com12 ) ACDABEZCFBCFAJBCABGHI $.

  ${
    bj-exalims.1 $e |- ( E. x ph -> ( -. ch -> A. x -. ch ) ) $.
    $( Distributing quantifiers over a nested implication.  (Almost) the
       general statement that ~ spimfw proves.  (Contributed by BJ,
       29-Sep-2019.) $)
    bj-exalims $p |-
         ( A. x ( ph -> ( ps -> ch ) ) -> ( E. x ph -> ( A. x ps -> ch ) ) ) $=
      ( wi wal wex bj-exalim wn eximal sylibr a1i syldd ) ABCFFDGZADHZBDGCDHZCA
      BCDIPQCFZFOPCJZSDGFRECCDKLMN $.
  $}

  ${
    bj-exalimsi.1 $e |- ( ph -> ( ps -> ch ) ) $.
    bj-exalimsi.2 $e |- ( E. x ph -> ( -. ch -> A. x -. ch ) ) $.
    $( An inference for distributing quantifiers over a nested implication.
       (Almost) the general statement that ~ spimfw proves.  (Contributed by
       BJ, 29-Sep-2019.) $)
    bj-exalimsi $p |- ( E. x ph -> ( A. x ps -> ch ) ) $=
      ( wi wex wal bj-exalims mpg ) ABCGGADHBDICGGDABCDFJEK $.
  $}

  $( Alternate proof of ~ bj-axdd2 (this should replace ~ bj-axdd2 when
     ~ bj-exalimi is moved to the main section).  (Contributed by BJ,
     8-Mar-2026.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  bj-axdd2ALT $p |- ( E. x ph -> ( A. x ps -> E. x ps ) ) $=
    ( idd bj-exalimi ) ABBCABDE $.

  ${
    bj-ax12ig.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    bj-ax12ig.2 $e |- ( ph -> ( ch -> A. x ch ) ) $.
    $( A lemma used to prove a weak form of the axiom of substitution.  A
       generalization of ~ bj-ax12i .  (Contributed by BJ, 19-Dec-2020.) $)
    bj-ax12ig $p |- ( ph -> ( ps -> A. x ( ph -> ps ) ) ) $=
      ( wi wal wa pm5.32i imp biimprcd sylg sylbi ex ) ABABGZDHZABIACIZQABCEJRC
      PDACCDHFKABCELMNO $.
  $}

  ${
    bj-ax12i.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    bj-ax12i.2 $e |- ( ch -> A. x ch ) $.
    $( A weakening of ~ bj-ax12ig that is sufficient to prove a weak form of
       the axiom of substitution ~ ax-12 .  The general statement of which
       ~ ax12i is an instance.  (Contributed by BJ, 29-Sep-2019.) $)
    bj-ax12i $p |- ( ph -> ( ps -> A. x ( ph -> ps ) ) ) $=
      ( wal wi a1i bj-ax12ig ) ABCDECCDGHAFIJ $.
  $}

  $( Closed form of ~ nfim and curried (exported) form of ~ nfimt .
     (Contributed by BJ, 20-Oct-2021.)  Proof should not use ~ 19.35 .
     (Proof modification is discouraged.) $)
  bj-nfimt $p |- ( F/ x ph -> ( F/ x ps -> F/ x ( ph -> ps ) ) ) $=
    ( wnf wi wex wal id nfrd bj-eximcom syl9 imim2d 19.38 syl6 df-nf imbitrrdi
    ) ACDZBCDZABEZCFZSCGZESCDQTACFZBCFZEZRUAQUBACGTUCQACQHIABCJKRUDUBBCGZEUARUC
    UEUBRBCRHILABCMNKSCOP $.

  $( A universal specification result: if ` ph ` is true for all values of
     ` x ` and implies ` ps ` for at least one value, and if furthermore ` x `
     is ` E. ` -weakly nonfree in ` ps ` , then ` ps ` follows.  An
     intermediate result on the way to prove ~ 19.36i , ~ bj-19.36im ,
     ~ 19.36imv , ~ spimfw ...  (Contributed by BJ, 3-Apr-2026.)  Proof should
     not use ~ 19.35 .  (Proof modification is discouraged.) $)
  bj-spimnfe $p |- ( ( E. x ps -> ps ) ->
                                ( E. x ( ph -> ps ) -> ( A. x ph -> ps ) ) ) $=
    ( wi wex wal bj-eximcom imim2 syl5 ) ABDCEACFZBCEZDKBDJBDABCGKBJHI $.

  $( An existential generalization result: if ` ph ` holds and implies ` ps `
     for at least one value of ` x ` , and if furthermore ` x ` is ` A. `
     -weakly nonfree in ` ph ` , then ` ps ` holds for at least one value of
     ` x ` .  (Contributed by BJ, 3-Apr-2026.)  Proof should not use ~ 19.35 .
     (Proof modification is discouraged.) $)
  bj-spimenfa $p |- ( ( ph -> A. x ph ) ->
                                ( E. x ( ph -> ps ) -> ( ph -> E. x ps ) ) ) $=
    ( wi wex wal bj-eximcom imim1 syl5 ) ABDCEACFZBCEZDAJDAKDABCGAJKHI $.

  ${
    bj-spim.nf0 $e |- ( ph -> A. x ph ) $.
    bj-spim.nf $e |- ( ph -> ( E. x th -> th ) ) $.
    bj-spim.denote $e |- ( ph -> E. x ps ) $.
    bj-spim.maj $e |- ( ( ph /\ ps ) -> ( ch -> th ) ) $.
    $( A lemma for universal specification.  In applications, ` x = y ` will be
       substituted for ` ps ` and ~ ax6ev will prove Hypothesis bj-spim.denote.
       (Contributed by BJ, 4-Apr-2026.) $)
    bj-spim $p |- ( ph -> ( A. x ch -> th ) ) $=
      ( wex wi wal ex eximdh mpd bj-spimnfe sylc ) ADEJDKCDKZEJZCELDKGABEJSHABR
      EFABRIMNOCDEPQ $.
  $}

  ${
    bj-spime.nf0 $e |- ( ph -> A. x ph ) $.
    bj-spime.nf $e |- ( ph -> ( ch -> A. x ch ) ) $.
    bj-spime.denote $e |- ( ph -> E. x ps ) $.
    bj-spime.maj $e |- ( ( ph /\ ps ) -> ( ch -> th ) ) $.
    $( A lemma for existential generalization.  In applications, ` x = y ` will
       be substituted for ` ps ` and ~ ax6ev will prove Hypothesis
       bj-spime.denote.  (Contributed by BJ, 4-Apr-2026.) $)
    bj-spime $p |- ( ph -> ( ch -> E. x th ) ) $=
      ( wal wi wex ex eximdh mpd bj-spimenfa sylc ) ACCEJKCDKZELZCDELKGABELSHAB
      REFABRIMNOCDEPQ $.
  $}

  ${
    bj-cbvalimd0.nf0 $e |- ( ph -> A. x ph ) $.
    bj-cbvalimd0.nf1 $e |- ( ph -> A. y ph ) $.
    bj-cbvalimd0.nfch $e |- ( ph -> ( ch -> A. y ch ) ) $.
    bj-cbvalimd0.nfth $e |- ( ph -> ( E. x th -> th ) ) $.
    bj-cbvalimd0.denote $e |- ( ph -> E. x ps ) $.
    bj-cbvalimd0.maj $e |- ( ( ph /\ ps ) -> ( ch -> th ) ) $.
    $( A lemma for alpha-renaming of variables bound by a universal quantifier.
       In applications, ` x = y ` will be substituted for ` ps ` and ~ ax6ev
       will prove Hypothesis bj-cbvalimd0.denote.  When ~ ax6ev is not
       available but only its universal closure is, then ~ bj-cbvalimd or
       ~ bj-cbvalimdv should be used (see ~ bj-cbvalimdlem , ~ bj-cbval ).
       (Contributed by BJ, 4-Apr-2026.) $)
    bj-cbvalimd0 $p |- ( ph -> ( A. x ch -> A. y th ) ) $=
      ( wal hbald bj-spim bj-alrimd ) AACEMZQDFHACFEGINABCDEGJKLOP $.
  $}

  ${
    bj-cbvalimdlem.nf0 $e |- ( ph -> A. x ph ) $.
    bj-cbvalimdlem.nf1 $e |- ( ph -> A. y ph ) $.
    bj-cbvalimdlem.nfch $e |- ( ph -> ( A. x ch -> A. y A. x ch ) ) $.
    bj-cbvalimdlem.nfth $e |- ( ph -> ( E. x th -> th ) ) $.
    bj-cbvalimdlem.denote $e |- ( ph -> A. y E. x ps ) $.
    bj-cbvalimdlem.maj $e |- ( ( ph /\ ps ) -> ( ch -> th ) ) $.
    $( A lemma for alpha-renaming of variables bound by a universal quantifier.
       Hypothesis bj-cbvalimdlem.nfch can be proved either from DV conditions
       as in ~ bj-cbvalimdv or from a nonfreeness condition and ~ alcom as in
       ~ bj-cbvalimd .  Hypothesis bj-cbvalimdlem.denote is weaker than the
       corresponding hypothesis of ~ bj-cbvalimd0 , and this proof is therefore
       a bit longer, not using ~ bj-spim but ~ bj-eximcom .  (Contributed by
       BJ, 12-Mar-2023.)  Proof should not use ~ 19.35 .
       (Proof modification is discouraged.) $)
    bj-cbvalimdlem $p |- ( ph -> ( A. x ch -> A. y th ) ) $=
      ( wal wex wi ex eximdh alimdh mpd bj-alrimd bj-eximcom ) AACEMZDENZDFHACD
      OZENZUBUBUCFABENZFMUEFMKAUFUEFHABUDEGABUDLPQRSICDEUATJT $.
  $}

  ${
    bj-cbveximdlem.nf0 $e |- ( ph -> A. x ph ) $.
    bj-cbveximdlem.nf1 $e |- ( ph -> A. y ph ) $.
    bj-cbveximdlem.nfch $e |- ( ph -> ( ch -> A. y ch ) ) $.
    bj-cbveximdlem.nfth $e |- ( ph -> ( E. x E. y th -> E. y th ) ) $.
    bj-cbveximdlem.denote $e |- ( ph -> A. x E. y ps ) $.
    bj-cbveximdlem.maj $e |- ( ( ph /\ ps ) -> ( ch -> th ) ) $.
    $( A lemma for alpha-renaming of variables bound by an existential
       quantifier.  Hypothesis bj-cbveximdlem.nfth can be proved either from DV
       conditions as in ~ bj-cbveximdv or from a nonfreeness condition and
       ~ excom as in ~ bj-cbveximd .  Hypothesis bj-cbveximdlem.denote is
       weaker than the corresponding hypothesis of ~~ bj-cbveximd0 , and this
       proof is therefore a bit longer, not using ~ bj-spime but ~ bj-eximcom .
       (Contributed by BJ, 12-Mar-2023.)  Proof should not use ~ 19.35 .
       (Proof modification is discouraged.) $)
    bj-cbveximdlem $p |- ( ph -> ( E. x ch -> E. y th ) ) $=
      ( wal wex wi ex eximdh alimdh mpd bj-exlimd bj-eximcom ) AACCFMZDFNZEGACD
      OZFNZUBUCUCEABFNZEMUEEMKAUFUEEGABUDFHABUDLPQRSJCDFUATIT $.
  $}

  ${
    bj-cbvalimd.nf0 $e |- ( ph -> A. x ph ) $.
    bj-cbvalimd.nf1 $e |- ( ph -> A. y ph ) $.
    bj-cbvalimd.nfch $e |- ( ph -> ( ch -> A. y ch ) ) $.
    bj-cbvalimd.nfth $e |- ( ph -> ( E. x th -> th ) ) $.
    bj-cbvalimd.denote $e |- ( ph -> A. y E. x ps ) $.
    bj-cbvalimd.maj $e |- ( ( ph /\ ps ) -> ( ch -> th ) ) $.
    $( A lemma for alpha-renaming of variables bound by a universal quantifier.
       (Contributed by BJ, 4-Apr-2026.)
       (Proof modification is discouraged.) $)
    bj-cbvalimd $p |- ( ph -> ( A. x ch -> A. y th ) ) $=
      ( hbald bj-cbvalimdlem ) ABCDEFGHACFEGIMJKLN $.
  $}

  ${
    bj-cbveximd.nf0 $e |- ( ph -> A. x ph ) $.
    bj-cbveximd.nf1 $e |- ( ph -> A. y ph ) $.
    bj-cbveximd.nfch $e |- ( ph -> ( ch -> A. y ch ) ) $.
    bj-cbveximd.nfth $e |- ( ph -> ( E. x th -> th ) ) $.
    bj-cbveximd.denote $e |- ( ph -> A. x E. y ps ) $.
    bj-cbveximd.maj $e |- ( ( ph /\ ps ) -> ( ch -> th ) ) $.
    $( A lemma for alpha-renaming of variables bound by an existential
       quantifier.  (Contributed by BJ, 4-Apr-2026.)
       (Proof modification is discouraged.) $)
    bj-cbveximd $p |- ( ph -> ( E. x ch -> E. y th ) ) $=
      ( wex excomim eximdh syl5 bj-cbveximdlem ) ABCDEFGHIDFMZEMDEMZFMARDEFNASD
      FHJOPKLQ $.
  $}

  ${
    $d y x $.  $d y ch $.
    bj-cbvalimdv.nf0 $e |- ( ph -> A. x ph ) $.
    bj-cbvalimdv.nf1 $e |- ( ph -> A. y ph ) $.
    bj-cbvalimdv.nfth $e |- ( ph -> ( E. x th -> th ) ) $.
    bj-cbvalimdv.denote $e |- ( ph -> A. y E. x ps ) $.
    bj-cbvalimdv.maj $e |- ( ( ph /\ ps ) -> ( ch -> th ) ) $.
    $( A lemma for alpha-renaming of variables bound by a universal quantifier.
       (Contributed by BJ, 4-Apr-2026.)
       (Proof modification is discouraged.) $)
    bj-cbvalimdv $p |- ( ph -> ( A. x ch -> A. y th ) ) $=
      ( wal ax5d bj-cbvalimdlem ) ABCDEFGHACELFMIJKN $.
  $}

  ${
    $d y x $.  $d x th $.
    bj-cbveximdv.nf0 $e |- ( ph -> A. x ph ) $.
    bj-cbveximdv.nf1 $e |- ( ph -> A. y ph ) $.
    bj-cbveximdv.nfth $e |- ( ph -> ( ch -> A. y ch ) ) $.
    bj-cbveximdv.denote $e |- ( ph -> A. x E. y ps ) $.
    bj-cbveximdv.maj $e |- ( ( ph /\ ps ) -> ( ch -> th ) ) $.
    $( A lemma for alpha-renaming of variables bound by an existential
       quantifier.  (Contributed by BJ, 4-Apr-2026.)
       (Proof modification is discouraged.) $)
    bj-cbveximdv $p |- ( ph -> ( E. x ch -> E. y th ) ) $=
      ( wex wi ax5e a1i bj-cbveximdlem ) ABCDEFGHIDFLZELQMAQENOJKP $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Adding ax-5
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d x ps $.
    $( Version of ~ spvw and ~ 19.3v proved from ~ ax-1 -- ~ ax-5 .  The
       antecedent can for instance be proved with the existence axiom ~ extru .
       (Contributed by BJ, 8-Mar-2026.)
       (Proof modification is discouraged.) $)
    bj-spvw $p |- ( E. x ph -> ( ps <-> A. x ps ) ) $=
      ( wex wal ax-5 bj-axdd2 ax5e syl6 impbid2 ) ACDZBBCEZBCFKLBCDBABCGBCHIJ
      $.

    $( Version of ~ 19.8v and ~ 19.9v proved from ~ ax-1 -- ~ ax-5 .  The
       antecedent can for instance be proved with the existence axiom ~ extru .
       (Contributed by BJ, 8-Mar-2026.)  This could also be proved from
       ~ bj-spvw using duality, but that proof would not be intuitionistic,
       contrary to the present one.  (Proof modification is discouraged.) $)
    bj-spvew $p |- ( E. x ph -> ( ps <-> E. x ps ) ) $=
      ( wex wal ax-5 bj-axdd2 syl5 ax5e impbid1 ) ACDZBBCDZBBCEKLBCFABCGHBCIJ
      $.
  $}

  ${
    $d x ph $.
    $( An equivalent expression for universal quantification over a
       non-occurring variable proved over ~ ax-1 -- ~ ax-5 .  The forward
       implication can be strengthened when ~ ax-6 is posited (which implies
       that models are non-empty), see ~ spvw .  The reverse implication can be
       seen as a strengthening of ~ ax-5 (since the antecedent of the
       implication is weakened).  See ~ bj-exextruan for a dual statement.

       An approximate meaning is: the universal quantification of a proposition
       over a non-occurring variable holds if and only if the proposition holds
       in nonempty universes.  (Contributed by BJ, 14-Mar-2026.)
       (Proof modification is discouraged.) $)
    bj-alextruim $p |- ( A. x ph <-> ( E. x T. -> ph ) ) $=
      ( wal wtru wi bj-spvw biimprcd ax-5 imim2i 19.38 pm2.27 mptru sylg impbii
      wex syl ) ABCZDBOZAEZRAQDABFGSRQEZQAQRABHITDAEZABDABJUAAEDAKLMPN $.

    $( An equivalent expression for existential quantification over a
       non-occurring variable proved over ~ ax-1 -- ~ ax-5 .  The forward
       implication can be seen as a strengthening of ~ ax-5 (a conjunct is
       added to the consequent of the implication).  The reverse implication
       can be strengthened when ~ ax-6 is posited (which implies that models
       are non-empty), see ~ 19.8v .  See ~ bj-alextruim for a dual statement.

       An approximate meaning is: the existential quantification of a
       proposition over a non-occurring variable holds if and only if the
       proposition holds and the universe is nonempty.  (Contributed by BJ,
       14-Mar-2026.)  (Proof modification is discouraged.) $)
    bj-exextruan $p |- ( E. x ph <-> ( E. x T. /\ ph ) ) $=
      ( wex wtru wa trud eximi ax5e jca bj-spvew biimpa impbii ) ABCZDBCZAEMNAA
      DBAFGABHINAMDABJKL $.
  $}

  ${
    $d x ps $.  $d y ps $.
    $( Universally quantifying over a non-occurring variable is independent of
       that variable, over ~ ax-1 -- ~ ax-5 and the existence axiom ~ extru .
       See ~ bj-cbvaw for a strengthening.  (Contributed by BJ, 8-Mar-2026.)
       (Proof modification is discouraged.) $)
    bj-cbvalvv $p |- ( E. x ph -> ( A. x ps -> A. y ps ) ) $=
      ( wex wal bj-spvw biimprd ax-5 syl6 ) ACEZBCFZBBDFKBLABCGHBDIJ $.

    $( Existentially quantifying over a non-occurring variable is independent
       of that variable, over ~ ax-1 -- ~ ax-5 and the existence axiom
       ~ extru .  See ~ bj-cbvew for a strengthening.  (Contributed by BJ,
       8-Mar-2026.)  (Proof modification is discouraged.) $)
    bj-cbvexvv $p |- ( E. x ph -> ( E. y ps -> E. x ps ) ) $=
      ( wex ax5e bj-spvew biimpd syl5 ) BDEBACEZBCEZBDFJBKABCGHI $.
  $}

  ${
    $d x ps $.  $d y ps $.
    $( Universally quantifying over a non-occurring variable is independent
       from the variable, under a weaker condition than in ~ bj-cbvalvv .  If
       ` F. ` is substituted for ` ph ` , then the statement reads:
       "universally quantifying over a non-occurring variable is independent
       from the variable as soon as that result is true for the False truth
       constant".  The label "cbvaw" means "'change bound variable' theorem,
       'all' quantifier, weak version".  (Contributed by BJ, 14-Mar-2026.)
       This proof is not intuitionistic (it uses ~ ja ); an intuitionistically
       valid statement is obtained by expressing the antecedent as a
       disjunction (classically equivalent through ~ imor ).
       (Proof modification is discouraged.) $)
    bj-cbvaw $p |- ( ( A. x ph -> A. y F. ) -> ( A. x ps -> A. y ps ) ) $=
      ( wal wfal wi wn wex exnal bj-cbvalvv sylbir falim alimi a1d ja ) ACEZFDE
      ZBCEZBDEZGZQHAHZCIUAACJUBBCDKLRTSFBDBMNOP $.

    $( Existentially quantifying over a non-occurring variable is independent
       from the variable, under a weaker condition than in ~ bj-cbvexvv .  If
       ` T. ` is substituted for ` ph ` , then the statement reads:
       "existentially quantifying over a non-occurring variable is independent
       from the variable as soon as that result is true for the True truth
       constant.  The label "cbvew" means "'change bound variable' theorem,
       'exists' quantifier, weak version".  (Contributed by BJ, 14-Mar-2026.)
       This proof is intuitionistic.  (Proof modification is discouraged.) $)
    bj-cbvew $p |- ( ( E. x T. -> E. y ph ) -> ( E. x ps -> E. y ps ) ) $=
      ( wex wtru wi trud eximi pm3.35 sylan bj-cbvexvv impcom syldan expcom ) B
      CEZFCEZADEZGZBDEZPSRTPQSRBFCBHIQRJKRPTABDCLMNO $.

    $( Universally quantifying over a non-occurring variable is independent
       from the variable, under a weaker condition than in ~ bj-cbvalvv .
       (Contributed by BJ, 14-Mar-2026.)
       (Proof modification is discouraged.) $)
    bj-cbveaw $p |- ( ( E. x T. -> E. y ph ) -> ( A. y ps -> A. x ps ) ) $=
      ( wtru wex wal wi wn wfal empty falim alimi a1d sylbi bj-cbvalvv ja ) ECF
      ZADFBDGZBCGZHZRIJCGZUACKUBTSJBCBLMNOABDCPQ $.

    $( Exixtentially quantifying over a non-occurring variable is independent
       from the variable, under a weaker condition than in ~ bj-cbvexvv .
       (Contributed by BJ, 14-Mar-2026.)
       (Proof modification is discouraged.) $)
    bj-cbvaew $p |- ( ( A. x ph -> A. y F. ) -> ( E. y ps -> E. x ps ) ) $=
      ( wal wfal wi wtru wex wn notnotb albii df-fal imbi12i bj-exexalal bitr4i
      bj-cbvew sylbi ) ACEZFDEZGZHDIAJZCIGZBDIBCIGUAUBJZCEZHJZDEZGUCSUETUGAUDCA
      KLFUFDMLNHUBDCOPUBBDCQR $.
  $}

  ${
    $d x ch $.
    bj-ax12wlem.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( A lemma used to prove a weak version of the axiom of substitution
       ~ ax-12 .  (Temporary comment:  The general statement that ~ ax12wlem
       proves.)  (Contributed by BJ, 20-Mar-2020.) $)
    bj-ax12wlem $p |- ( ph -> ( ps -> A. x ( ph -> ps ) ) ) $=
      ( ax-5 bj-ax12i ) ABCDECDFG $.
  $}

  ${
    $d x y $.  $d x ch $.  $d y ps $.
    bj-cbval.denote $e |- A. y E. x x = y $.
    bj-cbval.denote2 $e |- A. x E. y y = x $.
    bj-cbval.equcomiv $e |- ( y = x -> x = y ) $.
    bj-cbval.nf0 $e |- ( ph -> A. x ph ) $.
    bj-cbval.nf1 $e |- ( ph -> A. y ph ) $.
    bj-cbval.is $e |- ( ( ph /\ x = y ) -> ( ps <-> ch ) ) $.
    $( Changing a bound variable (universal quantification case) in a weak
       axiomatization that assumes that all variables denote (which is valid in
       inclusive free logic) and that equality is symmetric.  (Contributed by
       BJ, 12-Mar-2023.)  Proved from ~ ax-1 -- ~ ax-5 .
       (Proof modification is discouraged.) $)
    bj-cbval $p |- ( ph -> ( A. x ps <-> A. y ch ) ) $=
      ( wal weq wex wi ax5e a1i wa biimpd bj-cbvalimdv biimprd sylan2 impbid )
      ABDLCELADEMZBCDEIJCDNCOACDPQUDDNELAFQAUDRZBCKSTAEDMZCBEDJIBENBOABEPQUFEND
      LAGQUFAUDCBOHUEBCKUAUBTUC $.

    $( Changing a bound variable (existential quantification case) in a weak
       axiomatization that assumes that all variables denote (which is valid in
       inclusive free logic) and that equality is symmetric.  (Contributed by
       BJ, 12-Mar-2023.)  Proved from ~ ax-1 -- ~ ax-5 .
       (Proof modification is discouraged.) $)
    bj-cbvex $p |- ( ph -> ( E. x ps <-> E. y ch ) ) $=
      ( wex weq ax5d wal a1i wa wb sylan2 bj-cbveximdv biimpd biimprd impbid )
      ABDLCELAEDMZBCDEIJABENUDELDOAGPAUDQBCUDADEMZBCRHKSUATAUECBEDJIACDNUEDLEOA
      FPAUEQBCKUBTUC $.
  $}

  $( Symbol for BJ's version of the uniqueness quantifier. $)
  $c E** $.

  $( Syntax for BJ's version of the uniqueness quantifier. $)
  wmoo $a wff E** x ph $.

  ${
    $d x y z $.  $d ph y z $.
    $( Definition of the uniqueness quantifier which is correct on the empty
       domain.  Instead of the fresh variable ` z ` , one could save a dummy
       variable by using ` x ` or ` y ` at the cost of having nested
       quantifiers on the same variable.  (Contributed by BJ, 12-Mar-2023.) $)
    df-bj-mo $a |- ( E** x ph <-> A. z E. y A. x ( ph -> x = y ) ) $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Equality and substitution
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d y x $.  $d y A $.  $d y ph $.
    $( Proposed definition to replace ~ df-sb and ~ df-sbc .  Proof is
       therefore unimportant.  Contrary to ~ df-sb , this definition makes a
       substituted formula false when one substitutes a non-existent object for
       a variable: this is better suited to the "Levy-style" treatment of
       classes as virtual objects adopted by set.mm.  That difference is
       unimportant since as soon as ~ ax6ev is posited, all variables "exist".
       (Contributed by BJ, 19-Feb-2026.) $)
    bj-df-sb $p
            |- ( [. A / x ]. ph <-> E. y ( y = A /\ A. x ( x = y -> ph ) ) ) $=
  ( wsbc cv wceq wa wex weq wi wal sbc7 wsb sbsbc sb6 bitr3i anbi2i exbii bitri
  ) ABDECFZDGZABUAEZHZCIUBBCJAKBLZHZCIABCDMUDUFCUCUEUBUCABCNUEABCOABCPQRST $.
  $}

  ${
    $d y x $.  $d y A $.  $d y ph $.
    $( Proof of ~ sbcex when taking ~ bj-df-sb as definition.  (Contributed by
       BJ, 19-Feb-2026.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    bj-sbcex $p |- ( [. A / x ]. ph -> A e. _V ) $=
      ( vy cv wceq weq wi wal wex wsbc cvv wcel exsimpl bj-df-sb isset 3imtr4i
      wa ) DECFZBDGAHBIZRDJSDJABCKCLMSTDNABDCODCPQ $.
  $}

  ${
    $d y x $.  $d y A $.  $d y ph $.
    $( Proof of ~ df-sbc when taking ~ bj-df-sb as definition.  (Contributed by
       BJ, 19-Feb-2026.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    bj-dfsbc $p |- ( A e. { x | ph } <-> [. A / x ]. ph ) $=
      ( vy cv wceq cab wcel wa wex weq wi wal wsbc wsb df-clab sb6 bitri anbi2i
      exbii dfclel bj-df-sb 3bitr4i ) DEZCFZUDABGZHZIZDJUEBDKALBMZIZDJCUFHABCNU
      HUJDUGUIUEUGABDOUIADBPABDQRSTDCUFUAABDCUBUC $.
  $}

  ${
    $d y x u $.  $d z x u $.  $d u t $.
    $( Substitution in an equality, disjoint variables case.  Uses only ~ ax-1
       through ~ ax-6 .  It might be shorter to prove the result about
       composition of two substitutions and prove ~ bj-ssbeq first with a DV
       condition on ` x , t ` , and then in the general case.  (Contributed by
       BJ, 22-Dec-2020.)  (Proof modification is discouraged.) $)
    bj-ssbeq $p |- ( [ t / x ] y = z <-> y = z ) $=
      ( vu weq wsb wi wal dfsb wex 19.23v ax6ev pm2.27 ax-mp ax-1 impbii imbi2i
      bitri albii ) BCFZADGEDFZAEFZUAHAIZHZEIZUAUAAEDJUFUBUAHZEIZUAUEUGEUDUAUBU
      DUCAKZUAHZUAUCUAALUJUAUIUJUAHAEMUIUANOUAUIPQSRTUHUBEKZUAHZUAUBUAELULUAUKU
      LUAHEDMUKUANOUAUKPQSSS $.
  $}

  ${
    $d y z x $.  $d y z t $.  $d y z ph $.
    $( A lemma for the definiens of ~ df-sb .  An instance of ~ sp proved
       without it.  Note: it has a common subproof with ~ sbjust .
       (Contributed by BJ, 22-Dec-2020.)
       (Proof modification is discouraged.) $)
    bj-ssblem1 $p |- ( A. y ( y = t -> A. x ( x = y -> ph ) ) ->
                                         ( y = t -> A. x ( x = y -> ph ) ) ) $=
      ( vz weq wi wal equequ1 equequ2 imbi1d albidv imbi12d spw ) CDFZBCFZAGZBH
      ZGEDFZBEFZAGZBHZGCECEFZOSRUBCEDIUCQUABUCPTACEBJKLMN $.
  $}

  ${
    $d x y z t $.  $d y z ph $.
    $( An instance of ~ ax-11 proved without it.  The converse may not be
       provable without ~ ax-11 (since using ~ alcomimw would require a DV on
       ` ph , x ` , which defeats the purpose).  (Contributed by BJ,
       22-Dec-2020.)  (Proof modification is discouraged.) $)
    bj-ssblem2 $p |- ( A. x A. y ( y = t -> ( x = y -> ph ) ) ->
                                   A. y A. x ( y = t -> ( x = y -> ph ) ) ) $=
      ( vz weq wi equequ1 equequ2 imbi1d imbi12d alcomimw ) CDFZBCFZAGZGEDFZBEF
      ZAGZGBCECEFZMPORCEDHSNQACEBIJKL $.
  $}

  ${
    $d x t $.  $d t ph $.
    $( A weaker form of ~ ax-12 and ~ ax12v , namely the generalization over
       ` x ` of the latter.  In this statement, all occurrences of ` x ` are
       bound.  (Contributed by BJ, 26-Dec-2020.)
       (Proof modification is discouraged.) $)
    bj-ax12v $p |- A. x ( x = t -> ( ph -> A. x ( x = t -> ph ) ) ) $=
      ( weq wi wal ax12v ax-gen ) BCDZAIAEBFEEBABCGH $.
  $}

  ${
    $d y x t $.  $d y ph $.
    $( Remove a DV condition from ~ bj-ax12v (using core axioms only).
       (Contributed by BJ, 26-Dec-2020.)
       (Proof modification is discouraged.) $)
    bj-ax12 $p |- A. x ( x = t -> ( ph -> A. x ( x = t -> ph ) ) ) $=
      ( vy weq wi wal bj-ax12v equequ2 imbi1d albidv imbi2d imbi12d mpbii ax6ev
      exlimiiv ) DCEZBCEZARAFZBGZFZFZBGZDQBDEZAUDAFZBGZFZFZBGUCABDHQUHUBBQUDRUG
      UADCBIZQUFTAQUESBQUDRAUIJKLMKNDCOP $.
  $}

  ${
    $d x t $.
    $( Axiom ~ bj-ax12 expressed using substitution.  (Contributed by BJ,
       26-Dec-2020.)  (Proof modification is discouraged.) $)
    bj-ax12ssb $p |- [ t / x ] ( ph -> [ t / x ] ph ) $=
      ( wsb wi weq wal bj-ax12 sb6 imbi2i albii mpbir ) AABCDZEZBCDBCFZNEZBGZQO
      AOAEBGZEZEZBGABCHPTBNSOMRAABCIJJKLNBCIL $.
  $}

  $( Special case of ~ 19.41 proved from core axioms, ~ ax-10 (modal5), and
     ~ hba1 (modal4).  (Contributed by BJ, 29-Dec-2020.)
     (Proof modification is discouraged.) $)
  bj-19.41al $p |- ( E. x ( ph /\ A. x ps ) <-> ( E. x ph /\ A. x ps ) ) $=
    ( wal wa wex 19.40 hbe1a anim2i syl hba1 19.29r impbii ) ABCDZECFZACFZNEZOP
    NCFZEQANCGRNPBCHIJQPNCDZEONSPBCKIANCLJM $.

  ${
    $d x y $.
    bj-equsexval.1 $e |- ( x = y -> ( ph <-> A. x ps ) ) $.
    $( Special case of ~ equsexv proved from core axioms, ~ ax-10 (modal5), and
       ~ hba1 (modal4).  (Contributed by BJ, 29-Dec-2020.)
       (Proof modification is discouraged.) $)
    bj-equsexval $p |- ( E. x ( x = y /\ ph ) <-> A. x ps ) $=
      ( weq wa wex wal pm5.32i exbii ax6ev bj-19.41al mpbiran bitri ) CDFZAGZCH
      PBCIZGZCHZRQSCPAREJKTPCHRCDLPBCMNO $.
  $}

  ${
    $d x y $.
    $( Proof of ~ sbalex from core axioms, ~ ax-10 (modal5), and ~ bj-ax12 .
       (Contributed by BJ, 29-Dec-2020.)
       (Proof modification is discouraged.) $)
    bj-subst $p |- ( E. x ( x = y /\ ph ) <-> A. x ( x = y -> ph ) ) $=
      ( weq wa wex wi wal bj-ax12 pm3.31 aleximi ax-mp hbe1a syl equs4v impbii
      ) BCDZAEZBFZQAGZBHZSUABFZUAQAUAGGZBHSUBGABCIUCRUABQAUAJKLTBMNABCOP $.
  $}

  ${
    $d y x $.  $d y ph $.
    $( A special case of ~ sbequ2 .  (Contributed by BJ, 22-Dec-2020.) $)
    bj-ssbid2 $p |- ( [ x / x ] ph -> ph ) $=
      ( weq wsb wi equid sbequ2 ax-mp ) BBCABBDAEBFABBGH $.

    $( Alternate proof of ~ bj-ssbid2 , not using ~ sbequ2 .  (Contributed by
       BJ, 22-Dec-2020.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    bj-ssbid2ALT $p |- ( [ x / x ] ph -> ph ) $=
      ( vy wsb weq wi wal dfsb sp imim2i alimi wex pm2.21 equcomi imim1i 19.23v
      ja ax6ev biimpi mpisyl syl sylbi ) ABBDCBEZBCEZAFZBGZFZCGZAABCBHUHUCUEFZC
      GZAUGUICUFUEUCUEBIJKUJUCAFZCGZUCCLZAUIUKCUCUEUKUCAMUCUDACBNOQKCBRULUMAFUC
      ACPSTUAUB $.
  $}

  ${
    $d y x $.  $d y ph $.
    $( A special case of ~ sbequ1 .  (Contributed by BJ, 22-Dec-2020.) $)
    bj-ssbid1 $p |- ( ph -> [ x / x ] ph ) $=
      ( weq wsb wi equid sbequ1 ax-mp ) BBCAABBDEBFABBGH $.

    $( Alternate proof of ~ bj-ssbid1 , not using ~ sbequ1 .  (Contributed by
       BJ, 22-Dec-2020.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    bj-ssbid1ALT $p |- ( ph -> [ x / x ] ph ) $=
      ( vy weq wi wal wsb ax12v equcoms com12 alrimiv dfsb sylibr ) ACBDZBCDAEB
      FZEZCFABBGAPCNAOAOEBCABCHIJKABCBLM $.
  $}

  ${
    $d x z $.
    $( Lemma for ~ bj-ax6e .  (Contributed by BJ, 22-Dec-2020.)
       (Proof modification is discouraged.) $)
    bj-ax6elem1 $p |- ( -. A. x x = y -> ( y = z -> A. x y = z ) ) $=
      ( weq wal wn wi axc9 axc16 pm2.61d2 ) ABDAEFACDAEBCDZKAEGBCAHKACIJ $.
  $}

  ${
    $d x z $.
    $( Lemma for ~ bj-ax6e .  (Contributed by BJ, 22-Dec-2020.)
       (Proof modification is discouraged.) $)
    bj-ax6elem2 $p |- ( A. x y = z -> E. x x = y ) $=
      ( weq wi ax6ev equeucl eximii 19.35i ) BCDZABDZAACDJKEAACFABCGHI $.
  $}

  ${
    $d x z $.  $d y z $.
    $( Proof of ~ ax6e (hence ~ ax6 ) from Tarski's system, ~ ax-c9 ,
       ~ ax-c16 .  Remark: ~ ax-6 is used only via its principal (unbundled)
       instance ~ ax6v .  (Contributed by BJ, 22-Dec-2020.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    bj-ax6e $p |- E. x x = y $=
      ( vz weq wex wal wi 19.2 wn bj-ax6elem1 bj-ax6elem2 syl6 pm2.61i exlimiiv
      a1d ax6evr ) BCDZABDZAEZCRAFZQSGTSQRAHOTIQQAFSABCJABCKLMCBPN $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Adding ax-6
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d x y $.
    bj-spim0.nf0 $e |- ( ph -> A. x ph ) $.
    bj-spim0.nf $e |- ( ph -> ( E. x ch -> ch ) ) $.
    bj-spim0.is $e |- ( ( ph /\ x = y ) -> ( ps -> ch ) ) $.
    $( A universal specialization result in deduction form, proved from ~ ax-1
       -- ~ ax-6 , where the only DV condition is on ` x , y ` and where ` x `
       should be nonfree in the new proposition ` ch ` (and in the context
       ` ph ` ).  (Contributed by BJ, 4-Apr-2026.) $)
    bj-spim0 $p |- ( ph -> ( A. x ps -> ch ) ) $=
      ( weq wex ax6ev a1i bj-spim ) ADEIZBCDFGNDJADEKLHM $.
  $}

  ${
    $d x y $.  $d x ps $.
    $( Closed form of ~ spimvw .  See also ~ spimt .  (Contributed by BJ,
       8-Nov-2021.) $)
    bj-spimvwt $p |- ( A. x ( x = y -> ( ph -> ps ) ) -> ( A. x ph -> ps ) ) $=
      ( weq wi wal wex alequexv 19.36v sylib ) CDEABFZFCGLCHACGBFLCDIABCJK $.
  $}

  $( Theorem close to a closed form of ~ spnfw .  (Contributed by BJ,
     12-May-2019.) $)
  bj-spnfw $p |- ( ( E. x ph -> ps ) -> ( A. x ph -> ps ) ) $=
    ( wal wex 19.2 imim1i ) ACDACEBACFG $.

  ${
    $d x y $.
    bj-cbvexiw.1 $e |- ( E. x E. y ps -> E. y ps ) $.
    bj-cbvexiw.2 $e |- ( ph -> A. y ph ) $.
    bj-cbvexiw.3 $e |- ( y = x -> ( ph -> ps ) ) $.
    $( Change bound variable.  This is to ~ cbvexvw what ~ cbvaliw is to
       ~ cbvalvw .  TODO: move after ~ cbvalivw .  (Contributed by BJ,
       17-Mar-2020.) $)
    bj-cbvexiw $p |- ( E. x ph -> E. y ps ) $=
      ( wex spimew bj-sylge ) BDHZKACEABDCFGIJ $.
  $}

  ${
    $d x y $.  $d x ps $.  $d y ph $.
    bj-cbvexivw.1 $e |- ( y = x -> ( ph -> ps ) ) $.
    $( Change bound variable.  This is to ~ cbvexvw what ~ cbvalivw is to
       ~ cbvalvw .  TODO: move after ~ cbvalivw .  (Contributed by BJ,
       17-Mar-2020.) $)
    bj-cbvexivw $p |- ( E. x ph -> E. y ps ) $=
      ( wex ax5e ax-5 bj-cbvexiw ) ABCDBDFCGADHEI $.
  $}

  $( A short form of the axiom D of modal logic.  (Contributed by BJ,
     4-Apr-2021.) $)
  bj-modald $p |- ( A. x -. ph -> -. A. x ph ) $=
    ( wal wn wex 19.2 df-ex sylib con2i ) ABCZADBCZJABEKDABFABGHI $.

  ${
    $d x y $.
    $( A weakening of ~ ax-6 and ~ ax6v .  (Contributed by BJ, 4-Apr-2021.)
       (New usage is discouraged.) $)
    bj-denot $p |- ( x = x -> -. A. y -. y = x ) $=
      ( weq wn wal ax6v a1i ) BACDBEDAACBAFG $.
  $}

  ${
    $d x y $.  $d x ph $.
    $( A lemma for substitutions, proved from Tarski's FOL. The version without
       DV ` ( x , y ) ` is true but requires ~ ax-13 .  The disjoint variable
       condition DV ` ( x , ph ) ` is necessary for both directions: consider
       substituting ` x = z ` for ` ph ` .  (Contributed by BJ,
       25-May-2021.) $)
    bj-eqs $p |- ( ph <-> A. x ( x = y -> ph ) ) $=
      ( weq wi wal ax-1 alrimiv wex exim ax6ev pm2.27 ax-mp ax5e 3syl impbii )
      ABCDZAEZBFZARBAQGHSQBIZABIZEZUAAQABJTUBUAEBCKTUALMABNOP $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Adding ax-7
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d x y $.
    bj-cbvexw.1 $e |- ( E. x E. y ps -> E. y ps ) $.
    bj-cbvexw.2 $e |- ( ph -> A. y ph ) $.
    bj-cbvexw.3 $e |- ( E. y E. x ph -> E. x ph ) $.
    bj-cbvexw.4 $e |- ( ps -> A. x ps ) $.
    bj-cbvexw.5 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Change bound variable.  This is to ~ cbvexvw what ~ cbvalw is to
       ~ cbvalvw .  (Contributed by BJ, 17-Mar-2020.) $)
    bj-cbvexw $p |- ( E. x ph <-> E. y ps ) $=
      ( wex weq wb equcoms biimpd bj-cbvexiw biimprd impbii ) ACJBDJABCDEFDCKAB
      ABLCDIMNOBADCGHCDKABIPOQ $.
  $}

  ${
    $d x ch $.  $d y th $.  $d z ps $.  $d y z $.
    bj-ax12w.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    bj-ax12w.2 $e |- ( y = z -> ( ps <-> th ) ) $.
    $( The general statement that ~ ax12w proves.  (Contributed by BJ,
       20-Mar-2020.) $)
    bj-ax12w $p |- ( ph -> ( A. y ps -> A. x ( ph -> ps ) ) ) $=
      ( wal wi spw bj-ax12wlem syl5 ) BFJBAABKEJBDFGILABCEHMN $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Membership predicate, ax-8 and ax-9
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( A theorem which could be used as sole axiom for the non-logical predicate
     instead of ~ ax-8 and ~ ax-9 .  Indeed, it is implied over propositional
     calculus by the conjunction of ~ ax-8 and ~ ax-9 , as proved here.  In the
     other direction, one can prove ~ ax-8 (respectively ~ ax-9 ) from
     ~ bj-ax89 by using ~ mpan2 (respectively ~ mpan ) and ~ equid .  TODO:
     move to main part.  (Contributed by BJ, 3-Oct-2019.) $)
  bj-ax89 $p |- ( ( x = y /\ z = t ) -> ( x e. z -> y e. t ) ) $=
    ( weq wel ax8 ax9 sylan9 ) ABEACFBCFCDEBDFABCGCDBHI $.

  ${
    $d x z $.  $d y z $.
    $( One direction of ~ cleljust , requiring only ~ ax-1 -- ~ ax-5 and
       ~ ax8v1 .  (Contributed by BJ, 31-Dec-2020.)
       (Proof modification is discouraged.) $)
    bj-cleljusti $p |- ( E. z ( z = x /\ z e. y ) -> x e. y ) $=
      ( weq wel wa ax8v1 imp exlimiv ) CADZCBEZFABEZCJKLCABGHI $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Logical redundancy of ax-10--13
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Adding ax-10
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Adding ax-11
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( Commutation of two existential quantifiers on a formula is equivalent to
     commutation of two universal quantifiers over the same variables on the
     negation of that formula.  Can be placed in the ~ ax-4 section, soon after
     ~ 2nexaln , and used to prove ~ excom .  (Contributed by BJ, 29-Nov-2020.)
     (Proof modification is discouraged.) $)
  bj-alcomexcom $p |- ( ( A. x A. y -. ph -> A. y A. x -. ph ) <->
                                          ( E. y E. x ph -> E. x E. y ph ) ) $=
    ( wex wi wn wal con34b 2nexaln imbi12i bitr2i ) ABDCDZACDBDZEMFZLFZEAFZCGBG
    ZPBGCGZELMHNQORABCIACBIJK $.

  ${
    bj-hbald.1 $e |- ( ph -> A. y ps ) $.
    bj-hbald.2 $e |- ( ps -> ( ch -> A. x th ) ) $.
    $( General statement that ~ hbald proves .  (Contributed by BJ,
       4-Apr-2026.) $)
    bj-hbald $p |- ( ph -> ( A. y ch -> A. x A. y th ) ) $=
      ( wal wi al2imi syl ax-11 syl6 ) ACFIZDEIZFIZDFIEIABFIOQJGBCPFHKLDFEMN $.
  $}

  $( Closed form of (general instance of) ~ hbal .  (Contributed by BJ,
     2-May-2019.) $)
  bj-hbalt $p |- ( A. y ( ph -> A. x ps ) -> ( A. y ph -> A. x A. y ps ) ) $=
    ( wal wi id bj-hbald ) ABCEFZDEZIABCDJGIGH $.

  ${
    bj-hbal.1 $e |- ( ph -> A. x ps ) $.
    $( More general instance of ~ hbal .  (Contributed by BJ, 4-Apr-2026.) $)
    bj-hbal $p |- ( A. y ph -> A. x A. y ps ) $=
      ( wal wi bj-hbalt mpg ) ABCFGADFBDFCFGDABCDHEI $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Adding ax-12
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( Proof of ~ axc11n from { ~ ax-1 -- ~ ax-7 , ~ axc11 } .  Almost identical
     to ~ axc11nfromc11 .  (Contributed by NM, 6-Jul-2021.)
     (Proof modification is discouraged.) $)
  axc11n11 $p |- ( A. x x = y -> A. y y = x ) $=
    ( weq wal axc11 pm2.43i equcomi sylg ) ABCZADZIBACBJIBDIABEFABGH $.

  ${
    $d x z $.  $d y z $.
    $( Proof of ~ axc11n from { ~ ax-1 -- ~ ax-7 , ~ axc9 , ~ axc11r } (note
       that ~ axc16 is provable from { ~ ax-1 -- ~ ax-7 , ~ axc11r }).

       Note that ~ axc11n proves (over minimal calculus) that ~ axc11 and
       ~ axc11r are equivalent.  Therefore, ~ axc11n11 and ~ axc11n11r prove
       that one can use one or the other as an axiom, provided one assumes the
       axioms listed above ( ~ axc11 appears slightly stronger since
       ~ axc11n11r requires ~ axc9 while ~ axc11n11 does not).

       (Contributed by BJ, 6-Jul-2021.)
       (Proof modification is discouraged.) $)
    axc11n11r $p |- ( A. x x = y -> A. y y = x ) $=
      ( vz weq wal wex wi equcomi axc16 syl5 spsd exlimiv wn alnex ax6evr 19.29
      wa mpan2 axc9 impcom axc11r syl9 aev syl8 ex com24 imp pm2.18 syl6 sylbir
      syl pm2.61i ) BCDBEZCFZABDZAEZBADZBEZGZUMUSCUMUOURAUOUQUMURABHUQBCIJKLUNM
      UMMZCEZUSUMCNVAUTACDZQZCFZUSVAVBCFVDCAOUTVBCPRVCUSCVCUPURMZURGZURUTVBUPVF
      GUTVEUPVBURUTVEUPVBURGGUTVEQZUPVBVBAEZURVGVBVBBEZUPVHVEUTVBVIGACBSTVBBAUA
      UBACBABUCUDUEUFUGURUHUILUKUJUL $.
  $}

  ${
    $d x y $.  $d z t $.
    $( Proof of ~ axc16g from { ~ ax-1 -- ~ ax-7 , ~ axc16 }.  (Contributed by
       BJ, 6-Jul-2021.)  (Proof modification is discouraged.) $)
    bj-axc16g16 $p |- ( A. x x = y -> ( ph -> A. z ph ) ) $=
      ( vt weq wal wi aevlem axc16 syl ) BCFBGDEFDGAADGHBCDEIADEJK $.
  $}

  ${
    $d y ph $.
    $( A weak version of ~ ax-12 which is stronger than ~ ax12v .  Note that if
       one assumes reflexivity of equality ` |- x = x ` ( ~ equid ), then
       ~ bj-ax12v3 implies ~ ax-5 over modal logic K (substitute ` x ` for
       ` y ` ).  See also ~ bj-ax12v3ALT .  (Contributed by BJ, 6-Jul-2021.)
       (Proof modification is discouraged.) $)
    bj-ax12v3 $p |- ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) $=
      ( wal weq wi ax-5 ax12 syl5 ) AACDBCEZJAFBDACGABCHI $.

    $( Alternate proof of ~ bj-ax12v3 .  Uses ~ axc11r and ~ axc15 instead of
       ~ ax-12 .  (Contributed by BJ, 6-Jul-2021.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    bj-ax12v3ALT $p |- ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) $=
      ( weq wal wi ax-5 axc11r ala1 syl56 a1d axc15 pm2.61i ) BCDZBEZNANAFBEZFZ
      FOQNAACEOABEPACGACBHANBIJKABCLM $.
  $}

  ${
    $d x y $.  $d y ph $.
    $( A weak variant of ~ sbid2 not requiring ~ ax-13 nor ~ ax-10 .  On top of
       Tarski's FOL, one implication requires only ~ ax12v , and the other
       requires only ~ sp .  (Contributed by BJ, 25-May-2021.) $)
    bj-sb $p |- ( ph <-> A. y ( y = x -> A. x ( x = y -> ph ) ) ) $=
      ( weq wi wal ax12v equcoms com12 alrimiv a2i alimi bj-eqs sylibr impbii
      sp ) ACBDZBCDZAEZBFZEZCFZAUACQATATEBCABCGHIJUBQAEZCFAUAUCCQTATAEBCTRASBPI
      HKLACBMNO $.
  $}

  $( The predicate-calculus version of the axiom (B) of modal logic.  See also
     ~ modal-b .  (Contributed by BJ, 20-Oct-2019.) $)
  bj-modalbe $p |- ( ph -> A. x E. x ph ) $=
    ( wn wal wex modal-b df-ex biimpri sylg ) AACBDCZABEZBABFKJABGHI $.

  $( Closed form of ~ sps .  Once in main part, prove ~ sps and ~ spsd from it.
     (Contributed by BJ, 20-Oct-2019.) $)
  bj-spst $p |- ( ( ph -> ps ) -> ( A. x ph -> ps ) ) $=
    ( wal sp imim1i ) ACDABACEF $.

  $( Closed form of ~ 19.21bi .  (Contributed by BJ, 20-Oct-2019.) $)
  bj-19.21bit $p |- ( ( ph -> A. x ps ) -> ( ph -> ps ) ) $=
    ( wal sp imim2i ) BCDBABCEF $.

  $( Closed form of ~ 19.23bi .  (Contributed by BJ, 20-Oct-2019.) $)
  bj-19.23bit $p |- ( ( E. x ph -> ps ) -> ( ph -> ps ) ) $=
    ( wex 19.8a imim1i ) AACDBACEF $.

  $( Closed form of ~ nexr .  Contrapositive of ~ 19.8a .  (Contributed by BJ,
     20-Oct-2019.) $)
  bj-nexrt $p |- ( -. E. x ph -> -. ph ) $=
    ( wex 19.8a con3i ) AABCABDE $.

  $( Closed form of ~ alrimi .  (Contributed by BJ, 2-May-2019.) $)
  bj-alrim $p |- ( F/ x ph -> ( A. x ( ph -> ps ) -> ( ph -> A. x ps ) ) ) $=
    ( wnf wal wi nf5r sylgt syl5com ) ACDAACEFABFCEABCEFACGAABCHI $.

  $( Uncurried (imported) form of ~ bj-alrim .  (Contributed by BJ,
     2-May-2019.) $)
  bj-alrim2 $p |- ( ( F/ x ph /\ A. x ( ph -> ps ) ) -> ( ph -> A. x ps ) ) $=
    ( wnf wi wal bj-alrim imp ) ACDABECFABCFEABCGH $.

  $( A theorem close to a closed form of ~ nf5d and ~ nf5dh .  (Contributed by
     BJ, 2-May-2019.) $)
  bj-nfdt0 $p |- ( A. x ( ph -> ( ps -> A. x ps ) ) ->
                                ( A. x ph -> F/ x ps ) ) $=
    ( wal wi wnf alim nf5 imbitrrdi ) ABBCDEZECDACDJCDBCFAJCGBCHI $.

  $( Closed form of ~ nf5d and ~ nf5dh .  (Contributed by BJ, 2-May-2019.) $)
  bj-nfdt $p |- ( A. x ( ph -> ( ps -> A. x ps ) ) ->
                                ( ( ph -> A. x ph ) -> ( ph -> F/ x ps ) ) ) $=
    ( wal wi wnf bj-nfdt0 imim2d ) ABBCDEECDACDBCFAABCGH $.

  $( Closed form of ~ nexd .  (Contributed by BJ, 20-Oct-2019.) $)
  bj-nexdt $p |- ( F/ x ph ->
                          ( A. x ( ph -> -. ps ) -> ( ph -> -. E. x ps ) ) ) $=
    ( wnf wal wi wn wex nf5r bj-nexdh syl5com ) ACDAACEFABGFCEABCHGFACIABACJK
    $.

  ${
    $d x ph $.
    $( Closed form of ~ nexdv .  (Contributed by BJ, 20-Oct-2019.) $)
    bj-nexdvt $p |- ( A. x ( ph -> -. ps ) -> ( ph -> -. E. x ps ) ) $=
      ( wnf wn wi wal wex nfv bj-nexdt ax-mp ) ACDABEFCGABCHEFFACIABCJK $.
  $}

  $( Adding a second quantifier over the same variable is a transparent
     operation, ( ` A. E. ` case).  (Contributed by BJ, 20-Oct-2019.) $)
  bj-alexbiex $p |- ( A. x E. x ph <-> E. x ph ) $=
    ( wex nfe1 19.3 ) ABCBABDE $.

  $( Adding a second quantifier over the same variable is a transparent
     operation, ( ` E. E. ` case).  (Contributed by BJ, 20-Oct-2019.) $)
  bj-exexbiex $p |- ( E. x E. x ph <-> E. x ph ) $=
    ( wex nfe1 19.9 ) ABCBABDE $.

  $( Adding a second quantifier over the same variable is a transparent
     operation, ( ` A. A. ` case).  (Contributed by BJ, 20-Oct-2019.) $)
  bj-alalbial $p |- ( A. x A. x ph <-> A. x ph ) $=
    ( wal nfa1 19.3 ) ABCBABDE $.

  $( Adding a second quantifier over the same variable is a transparent
     operation, ( ` E. A. ` case).  (Contributed by BJ, 20-Oct-2019.) $)
  bj-exalbial $p |- ( E. x A. x ph <-> A. x ph ) $=
    ( wal nfa1 19.9 ) ABCBABDE $.

  $( Strengthening ~ 19.9ht by replacing its consequent with a biconditional
     ( ~ 19.9t does have a biconditional consequent).  This propagates.
     (Contributed by BJ, 20-Oct-2019.) $)
  bj-19.9htbi $p |- ( A. x ( ph -> A. x ph ) -> ( E. x ph <-> ph ) ) $=
    ( wal wi wex 19.9ht 19.8a impbid1 ) AABCDBCABEAABFABGH $.

  $( Strengthening ~ hbnt by replacing its consequent with a biconditional.
     See also ~ hbntg and ~ hbntal .  (Contributed by BJ, 20-Oct-2019.)  Proved
     from ~ bj-19.9htbi .  (Proof modification is discouraged.) $)
  bj-hbntbi $p |- ( A. x ( ph -> A. x ph ) -> ( -. ph <-> A. x -. ph ) ) $=
    ( wal wi wn wex bj-19.9htbi bicomd notbid alnex bitr4di ) AABCDBCZAEZABFZEM
    BCLANLNAABGHIABJK $.

  $( A general FOL biconditional that generalizes ~ 19.9ht among others.  For
     this and the following theorems, see also ~ 19.35 , ~ 19.21 , ~ 19.23 .
     When ` ph ` is substituted for ` ps ` , both sides express a form of
     nonfreeness.  (Contributed by BJ, 20-Oct-2019.) $)
  bj-biexal1 $p |- ( A. x ( ph -> A. x ps ) <-> ( E. x ph -> A. x ps ) ) $=
    ( wal nfa1 19.23 ) ABCDCBCEF $.

  $( When ` ph ` is substituted for ` ps ` , both sides express a form of
     nonfreeness.  (Contributed by BJ, 20-Oct-2019.) $)
  bj-biexal2 $p |- ( A. x ( E. x ph -> ps ) <-> ( E. x ph -> A. x ps ) ) $=
    ( wex nfe1 19.21 ) ACDBCACEF $.

  $( When ` ph ` is substituted for ` ps ` , both sides express a form of
     nonfreeness.  (Contributed by BJ, 20-Oct-2019.) $)
  bj-biexal3 $p |- ( A. x ( ph -> A. x ps ) <-> A. x ( E. x ph -> ps ) ) $=
    ( wal wi wex bj-biexal1 bj-biexal2 bitr4i ) ABCDZECDACFZJEKBECDABCGABCHI $.

  $( When ` ph ` is substituted for ` ps ` , both sides express a form of
     nonfreeness.  (Contributed by BJ, 20-Oct-2019.) $)
  bj-bialal $p |- ( A. x ( A. x ph -> ps ) <-> ( A. x ph -> A. x ps ) ) $=
    ( wal nfa1 19.21 ) ACDBCACEF $.

  $( When ` ph ` is substituted for ` ps ` , both sides express a form of
     nonfreeness.  (Contributed by BJ, 20-Oct-2019.) $)
  bj-biexex $p |- ( A. x ( ph -> E. x ps ) <-> ( E. x ph -> E. x ps ) ) $=
    ( wex nfe1 19.23 ) ABCDCBCEF $.

  ${
    bj-hbexd.nf $e |- ( ph -> A. y ps ) $.
    bj-hbexd.maj $e |- ( ps -> ( ch -> A. x th ) ) $.
    $( A more general instance of the deduction form of ~ hbex .  (Contributed
       by BJ, 4-Apr-2026.) $)
    bj-hbexd $p |- ( ph -> ( E. y ch -> A. x E. y th ) ) $=
      ( wal wex wi 19.12 a1i bj-exlimd ) ABCDEIZDFJEIZFGOFJPKADFELMHN $.
  $}

  $( Closed form of ~ bj-hbex and ~ hbex .  (Contributed by BJ,
     10-Oct-2019.) $)
  bj-hbext $p |-
              ( A. y A. x ( ph -> A. x ps ) -> ( E. y ph -> A. x E. y ps ) ) $=
    ( wal wi id sp bj-hbexd ) ABCEFZCEZDEZKABCDLGJCHI $.

  ${
    bj-hbex.1 $e |- ( ph -> A. x ps ) $.
    $( A more general instance of ~ hbex .  (Contributed by BJ, 4-Apr-2026.) $)
    bj-hbex $p |- ( E. y ph -> A. x E. y ps ) $=
      ( wal wex 19.12 bj-sylge ) BCFBDGCFADBDCHEI $.
  $}

  $( Closed form of ~ nfal .  (Contributed by BJ, 2-May-2019.) $)
  bj-nfalt $p |- ( A. x F/ y ph -> F/ y A. x ph ) $=
    ( wal wi wnf bj-hbalt alimi alcoms nf5 albii 3imtr4i ) AACDEZCDZBDABDZOCDEZ
    CDZACFZBDOCFMQCBMBDPCAACBGHIRNBACJKOCJL $.

  $( Closed form of ~ nfex .  (Contributed by BJ, 10-Oct-2019.) $)
  bj-nfext $p |- ( A. x F/ y ph -> F/ y E. x ph ) $=
    ( wnf wal wex wi nf5 biimpi alimi nfa2 bj-hbext alrimi syl sylibr ) ACDZBEZ
    ABFZRCEGZCEZRCDQAACEGZCEZBEZTPUBBPUBACHIJUCSCUACBKAACBLMNRCHO $.

  ${
    $d y ph $.  $d x ps $.  $d x y $.
    $( Version of ~ exdistrv with a disjoint variable condition on ` x , y `
       not requiring ~ ax-11 .  (The same can be done with ~ eeeanv and
       ~ ee4anv .)  (Contributed by BJ, 29-Sep-2019.)
       (Proof modification is discouraged.) $)
    bj-eeanvw $p |- ( E. x E. y ( ph /\ ps ) <-> ( E. x ph /\ E. y ps ) ) $=
      ( wa wex 19.42v exbii 19.41v bitri ) ABEDFZCFABDFZEZCFACFLEKMCABDGHALCIJ
      $.
  $}

  $( First-order logic form of the modal axiom (4).  See ~ hba1 .  This is the
     standard proof of the implication in modal logic (B5 ` => ` 4).  Its dual
     statement is ~ bj-modal4e .  (Contributed by BJ, 12-Aug-2023.)
     (Proof modification is discouraged.) $)
  bj-modal4 $p |- ( A. x ph -> A. x A. x ph ) $=
    ( wal wex bj-modalbe hbe1a sylg ) ABCZHBDHBHBEABFG $.

  $( First-order logic form of the modal axiom (4) using existential
     quantifiers.  Dual statement of ~ bj-modal4 ( ~ hba1 ).  (Contributed by
     BJ, 21-Dec-2020.)  (Proof modification is discouraged.) $)
  bj-modal4e $p |- ( E. x E. x ph -> E. x ph ) $=
    ( wex wn wal bj-modal4 alnex 2exnaln con2bii 3imtr3i con4i ) ABCZLBCZADZBEZ
    OBEZLDMDNBFABGMPABBHIJK $.

  $( A short form of the axiom B of modal logic using only primitive symbols
     ( ` -> , -. , A. ` ).  (Contributed by BJ, 4-Apr-2021.)
     (Proof modification is discouraged.) $)
  bj-modalb $p |- ( -. ph -> A. x -. A. x ph ) $=
    ( wal wn axc7 con1i ) ABCDBCAABEF $.

  $( When ` ph ` is substituted for ` ps ` , this is the first half of
     nonfreness ` ( . -> A. ) ` of the weak form of nonfreeness
     ` ( E. -> A. ) ` .  (Contributed by BJ, 9-Dec-2023.) $)
  bj-wnf1 $p |- ( ( E. x ph -> A. x ps ) -> A. x ( E. x ph -> A. x ps ) ) $=
    ( wex wal wi bj-modal4e hba1 imim12i 19.38 syl ) ACDZBCEZFZLCDZMCEZFNCEOLMP
    ACGBCHILMCJK $.

  $( When ` ph ` is substituted for ` ps ` , this is the first half of
     nonfreness ` ( . -> A. ) ` of the weak form of nonfreeness
     ` ( E. -> A. ) ` .  (Contributed by BJ, 9-Dec-2023.) $)
  bj-wnf2 $p |- ( E. x ( E. x ph -> A. x ps ) -> ( E. x ph -> A. x ps ) ) $=
    ( wex wal wi hbe1 bj-eximcom hbe1a syl56 ) ACDZKCEKBCEZFCDLCDLACGKLCHBCIJ
    $.

  $( When ` ph ` is substituted for ` ps ` , this statement expresses that weak
     nonfreeness implies the universal form of nonfreeness.  (Contributed by
     BJ, 9-Dec-2023.) $)
  bj-wnfanf $p |- ( ( E. x ph -> A. x ps ) -> A. x ( ph -> A. x ps ) ) $=
    ( wex wal wi bj-wnf1 bj-19.23bit sylg ) ACDBCEZFZKAJFCABCGAJCHI $.

  $( When ` ph ` is substituted for ` ps ` , this statement expresses that weak
     nonfreeness implies the existential form of nonfreeness.  (Contributed by
     BJ, 9-Dec-2023.) $)
  bj-wnfenf $p |- ( ( E. x ph -> A. x ps ) -> A. x ( E. x ph -> ps ) ) $=
    ( wex wal wi bj-wnf1 bj-19.21bit sylg ) ACDZBCEFZKJBFCABCGJBCHI $.

  $( See ~ 19.12 .  Could be labeled "exalimalex" for "'there exists for all'
     implies 'for all there exists'".  This proof is from ~ excom and modal (B)
     on top of modalK logic.  (Contributed by BJ, 12-Aug-2023.)  The proof
     should not rely on ~ df-nf or ~ df-bj-nnf , directly or indirectly.
     (Proof modification is discouraged.) $)
  bj-19.12 $p |- ( E. x A. y ph -> A. y E. x ph ) $=
    ( wal wex bj-modalbe excom axc7e eximi sylbi sylg ) ACDZBEZMCEZABEZCMCFNLCE
    ZBEOLCBGPABACHIJK $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Really adding ax-12
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  The results in the previous section, as actually many theorems of the main
  part using ~ ax-12 , actually only require ~ sp (which is proved using
  ~ ax-12 ).

$)

  $( Equivalent form of the axiom of substitution ~ bj-ax12 .  Although both
     sides need a DV condition on ` x , t ` (or as in ~ bj-ax12v3 on
     ` t , ph ` ) to hold, their equivalence holds without DV conditions.  The
     forward implication is proved in modal (K4) while the reverse implication
     is proved in modal (T5).  The LHS has the advantage of not involving
     nested quantifiers on the same variable.  Its metaweakening is proved from
     the core axiom schemes in ~ bj-substw .  Note that in the LHS, the reverse
     implication holds by ~ equs4 (or ~ equs4v if a DV condition is added on
     ` x , t ` as in ~ bj-ax12 ), and the forward implication is ~ sbalex .

     The LHS can be read as saying that if there exists a variable equal to a
     given term witnessing a given formula, then all variables equal to that
     term also witness that formula.  The equivalent form of the LHS using only
     primitive symbols is
     ` ( A. x ( x = t -> ph ) \/ A. x ( x = t -> -. ph ) ) ` , which expresses
     that a given formula is true at all variables equal to a given term, or
     false at all these variables.  An equivalent form of the LHS using only
     the existential quantifier is
     ` -. ( E. x ( x = t /\ ph ) /\ E. x ( x = t /\ -. ph ) ) ` , which
     expresses that there can be no two variables both equal to a given term,
     one witnessing a formula and the other witnessing its negation.  These
     equivalences do not hold in intuitionistic logic.  The LHS should be the
     preferred form, and has the advantage of having no negation nor nested
     quantifiers.  (Contributed by BJ, 21-May-2024.)
     (Proof modification is discouraged.) $)
  bj-substax12 $p |- ( ( E. x ( x = t /\ ph ) -> A. x ( x = t -> ph ) ) <->
                          A. x ( x = t -> ( ph -> A. x ( x = t -> ph ) ) ) ) $=
    ( weq wa wex wi wal bj-modal4 imim2i 19.38 syl hbe1a bj-exlimg ax-mp impbii
    sp impexp albii bitri ) BCDZAEZBFZUAAGZBHZGZUBUEGZBHZUAAUEGGZBHUFUHUFUCUEBH
    ZGZUHUEUJUCUDBIZJUBUEBKLUHUKUFUEBFZUJGUHUKGUMUEUJUDBMULLUEUJUBBNOUJUEUCUEBQ
    JLPUGUIBUAAUERST $.

  ${
    $d x ps $.
    bj-substw.is $e |- ( x = t -> ( ph <-> ps ) ) $.
    $( Weak form of the LHS of ~ bj-substax12 proved from the core axiom
       schemes.  Compare ~ ax12w .  (Contributed by BJ, 26-May-2024.)
       (Proof modification is discouraged.) $)
    bj-substw $p |- ( E. x ( x = t /\ ph ) -> A. x ( x = t -> ph ) ) $=
      ( weq wa wex wi wal pm5.32i exbii 19.41v bitri biimprcd alrimiv simplbiim
      ) CDFZAGZCHZRCHZBRAIZCJTRBGZCHUABGSUCCRABEKLRBCMNBUBCRABEOPQ $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Nonfreeness
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( Token for the nonfreeness quantifier. $)
  $c F// $.

  $( Syntax for the nonfreeness quantifier. $)
  wnnf $a wff F// x ph $.

  $( Definition of the nonfreeness quantifier.  The formula ` F// x ph ` has
     the intended meaning that the variable ` x ` is semantically nonfree in
     the formula ` ph ` .  The motivation for this quantifier is to have a
     condition expressible in the logic which is as close as possible to the
     non-occurrence condition DV ` ( x , ph ) ` (in Metamath files, "$d x ph
     $."), which belongs to the metalogic.

     The standard syntactic nonfreeness condition, also expressed in the
     metalogic, is intermediate between these two notions: semantic nonfreeness
     implies syntactic nonfreeness, which implies non-occurrence.  Both
     implications are strict; for the first, note that ` |- F// x x = x ` ,
     that is, ` x ` is semantically (but not syntactically) nonfree in the
     formula ` x = x ` ; for the second, note that ` x ` is syntactically
     nonfree in the formula ` A. x x = x ` although it occurs in it.

     We now prove two metatheorems which make precise the above fact that, as
     far as proving power is concerned, the nonfreeness condition ` F// x ph `
     is very close to the non-occurrence condition DV ` ( x , ph ) ` .

     Let S be a Metamath system with the FOL-syntax of (i)set.mm, containing
     intuitionistic positive propositional calculus and ~ ax-5 and ~ ax5e .

     Theorem 1.  If the scheme

     ` ( F// x ph & ` PHI_1 ` & ... & ` PHI_n ` => ` PHI_0, DV)

     is provable in S, then so is the scheme

     (PHI_1 ` & ... & ` PHI_n ` => ` PHI_0, DV ` u. { { x , ph } } ) ` .

     Proof:  By ~ bj-nnfv , we can prove ` ( F// x ph , { { x , ph } } ) ` ,
     from which the theorem follows.  QED

     Theorem 2.  Suppose that S also contains (the FOL version of) modal logic
     KB and commutation of quantifiers ~ alcom and ~ excom (possibly weakened
     by a DV condition on the quantifying variables), and that S can be
     axiomatized such that the only axioms with a DV condition involving a
     formula variable are among ~ ax-5 , ~ ax5e , ~ ax5ea .  If the scheme

     (PHI_1 ` & ... & ` PHI_n ` => ` PHI_0, DV)

     is provable in S, then so is the scheme

     ` ( F// x ph & ` PHI_1 ` & ... & ` PHI_n ` => ` PHI_0, DV
     ` \ { { x , ph } } ) ` .

     More precisely, if S contains modal 45 and if the variables quantified
     over in PHI_0, ..., PHI_n are among ` x `_1, ..., ` x `_m, then the scheme

     (PHI_1 ` & ... & ` PHI_n ` => ` (antecedent ` -> ` PHI_0), DV
     ` \ { { x , ph } } ) `

     is provable in S, where the antecedent is a finite conjunction of formulas
     of the form ` A. x `_i1 ` ... A. x `_ip ` F// x ph ` where the ` x `_ij's
     are among the ` x `_i's.

     Lemma:  If ` x e/ ` OC(PHI), then S proves the scheme

     ` ( F// x ph => F// x ` PHI, ` { { x , a } | a e. ` OC(PHI)
     ` \ { ph } } ) ` .

     More precisely, if the variables quantified over in PHI are among
     ` x `_1, ..., ` x `_m, then

     ((antecedent ` -> F// x ` PHI), ` { { x , a } | a e. ` OC(PHI)
     ` \ { ph } } ) `

     is provable in S, with the same form of antecedent as above.

     Proof:  By induction on the height of PHI. We first note that by
     ~ bj-nnfbi we can assume that PHI contains only primitive (as opposed to
     defined) symbols.  For the base case, atomic formulas are either ` ph ` ,
     in which case the scheme to prove is an instance of ~ id , or have
     variables all in OC(PHI) ` \ { ph } ` , so ` ( F// x ` PHI,
     ` { { x , a } | a e. ` OC(PHI) ` \ { ph } } ) ` by ~ bj-nnfv , hence
     ` ( ( F// x ph -> F// x ` PHI), ` { { x , a } | a e. ` OC(PHI)
     ` \ { ph } } ) ` by ~ a1i .  For the induction step, PHI is either an
     implication, a negation, a conjunction, a disjunction, a biconditional, a
     universal or an existential quantification of formulas where ` x ` does
     not occur.  We use respectively ~ bj-nnfim , ~ bj-nnfnt , ~ bj-nnfan ,
     ~ bj-nnfor , ~ bj-nnfbit , ~ bj-nnfalt , ~ bj-nnfext .  For instance, in
     the implication case, if we have by induction hypothesis

     ` ( ( A. x `_1 ` ... A. x `_m ` F// x ph -> F// x ` PHI),
     ` { { x , a } | a e. ` OC(PHI) ` \ { ph } } ) ` and ` ( ( A. y `_1
     ` ... A. y `_n ` F// x ph -> F// x ` PSI), ` { { x , a } | a e. ` OC(PSI)
     ` \ { ph } } ) ` ,

     then ~ bj-nnfim yields

     ` ( ( ( A. x `_1 ` ... A. x `_m ` F// x ph /\ A. y `_1 ` ... A. y `_n
     ` F// x ph ) -> F// x ` (PHI ` -> ` PSI)), ` { { x , a } | a e. ` OC(PHI
     ` -> ` PSI) ` \ { ph } } ) `

     and similarly for antecedents which are conjunctions as in the statement
     of the lemma.

     In the universal quantification case, say quantification over ` y ` , if
     we have by induction hypothesis

     ` ( ( A. x `_1 ` ... A. x `_m ` F// x ph -> F// x ` PHI),
     ` { { x , a } | a e. ` OC(PHI) ` \ { ph } } ) ` ,

     then ~ bj-nnfalt yields

     ` ( ( A. y A. x `_1 ` ... A. x `_m ` F// x ph -> F// x A. y ` PHI),
     ` { { x , a } | a e. ` OC( ` A. y ` PHI) ` \ { ph } } ) `

     and similarly for antecedents which are conjunctions as in the statement
     of the lemma.

     Note ~ bj-nnfalt and ~ bj-nnfext are proved from positive propositional
     calculus with ~ alcom and ~ excom (possibly weakened by a DV condition on
     the quantifying variables), and modalB (via ~ bj-19.12 ).  QED

     Proof of the theorem:  Consider a proof of that scheme directly from the
     axioms.  Consider a step where a DV condition involving ` ph ` is used.
     By hypothesis, that step is an instance of ~ ax-5 or ~ ax5e or ~ ax5ea .
     It has the form (PSI ` -> A. x ` PSI) where PSI has the form of the lemma
     and the DV conditions of the proof contain ` { { x , a } | a e. ` OC(PSI)
     ` } ` .  Therefore, one has

     ` ( ( A. x `_1 ` ... A. x `_m ` F// x ph -> F// x ` PSI),
     ` { { x , a } | a e. ` OC(PSI) ` \ { ph } } ) `

     for appropriate ` x `_i's, and by ~ bj-nnfa we obtain

     ` ( ( A. x `_1 ` ... A. x `_m ` F// x ph -> ` (PSI ` -> A. x ` PSI)),
     ` { { x , a } | a e. ` OC(PSI) ` \ { ph } } ) `

     and similarly for antecedents which are conjunctions as in the statement
     of the theorem.  Similarly if the step is using ~ ax5e or ~ ax5ea , we
     would use ~ bj-nnfe or ~ bj-nnfea respectively.

     Therefore, taking as antecedent of the theorem to prove the conjunction of
     all the antecedents at each of these steps, we obtain a proof by "carrying
     the context over", which is possible, as in the deduction theorem when the
     step uses ~ ax-mp , and when the step uses ~ ax-gen , by ~ bj-nnf-alrim
     and ~ bj-nnfa1 (which requires modal 45).  The condition DV ` ( x , ph ) `
     is not required by the resulting proof.

     Finally, there may be in the global antecedent thus constructed some dummy
     variables, which can be removed by ~ spvw .  QED

     Compared with ~ df-nf , the present definition is stricter on positive
     propositional calculus ( ~ bj-nnfnfTEMP ) and equivalent on core FOL plus
     ~ sp ( ~ bj-nfnnfTEMP ).  While being stricter, it still holds for
     non-occurring variables ( ~ bj-nnfv ), which is the basic requirement for
     this quantifier.  In particular, it translates more closely the associated
     variable disjointness condition.  Since the nonfreeness quantifier is a
     means to translate a variable disjointness condition from the metalogic to
     the logic, it seems preferable.  Also, since nonfreeness is mainly used as
     a hypothesis, this definition would allow more theorems, notably the 19.xx
     theorems, to be proved from the core axioms, without needing a 19.xxv
     variant.

     One can devise infinitely many definitions increasingly close to the
     non-occurring condition, like
     ` ( ( E. x ph -> ph ) /\ ( ph -> A. x ph ) ) /\ `
     ` A. x ( ( E. x ph -> ph ) /\ ( ph -> A. x ph ) ) /\ A. x A. x ` ... and
     each stronger definition would permit more theorems to be proved from the
     core axioms.  A reasonable rule seems to be to stop before nested
     quantifiers appear (since they typically require ~ ax-10 to work with),
     and also not to have redundant conjuncts when full metacomplete FOL= is
     developed.

     (Contributed by BJ, 28-Jul-2023.) $)
  df-bj-nnf $a |-
                 ( F// x ph <-> ( ( E. x ph -> ph ) /\ ( ph -> A. x ph ) ) ) $.

  $( Nonfreeness implies the equivalent of ~ ax-5 .  See ~ nf5r .  (Contributed
     by BJ, 28-Jul-2023.) $)
  bj-nnfa $p |- ( F// x ph -> ( ph -> A. x ph ) ) $=
    ( wnnf wex wi wal df-bj-nnf simprbi ) ABCABDAEAABFEABGH $.

  ${
    bj-nnfad.1 $e |- ( ph -> F// x ps ) $.
    $( Nonfreeness implies the equivalent of ~ ax-5 , deduction form.  See
       ~ nf5rd .  (Contributed by BJ, 2-Dec-2023.) $)
    bj-nnfad $p |- ( ph -> ( ps -> A. x ps ) ) $=
      ( wnnf wal wi bj-nnfa syl ) ABCEBBCFGDBCHI $.
  $}

  ${
    bj-nnfai.1 $e |- F// x ph $.
    $( Nonfreeness implies the equivalent of ~ ax-5 , inference form.  See
       ~ nf5ri .  (Contributed by BJ, 22-Sep-2024.) $)
    bj-nnfai $p |- ( ph -> A. x ph ) $=
      ( wnnf wal wi bj-nnfa ax-mp ) ABDAABEFCABGH $.
  $}

  $( Nonfreeness implies the equivalent of ~ ax5e .  (Contributed by BJ,
     28-Jul-2023.) $)
  bj-nnfe $p |- ( F// x ph -> ( E. x ph -> ph ) ) $=
    ( wnnf wex wi wal df-bj-nnf simplbi ) ABCABDAEAABFEABGH $.

  ${
    bj-nnfed.1 $e |- ( ph -> F// x ps ) $.
    $( Nonfreeness implies the equivalent of ~ ax5e , deduction form.
       (Contributed by BJ, 2-Dec-2023.) $)
    bj-nnfed $p |- ( ph -> ( E. x ps -> ps ) ) $=
      ( wnnf wex wi bj-nnfe syl ) ABCEBCFBGDBCHI $.
  $}

  ${
    bj-nnfei.1 $e |- F// x ph $.
    $( Nonfreeness implies the equivalent of ~ ax5e , inference form.
       (Contributed by BJ, 22-Sep-2024.) $)
    bj-nnfei $p |- ( E. x ph -> ph ) $=
      ( wnnf wex wi bj-nnfe ax-mp ) ABDABEAFCABGH $.
  $}

  $( Nonfreeness implies the equivalent of ~ ax5ea .  (Contributed by BJ,
     28-Jul-2023.) $)
  bj-nnfea $p |- ( F// x ph -> ( E. x ph -> A. x ph ) ) $=
    ( wnnf wex wal bj-nnfe bj-nnfa syld ) ABCABDAABEABFABGH $.

  ${
    bj-nnfead.1 $e |- ( ph -> F// x ps ) $.
    $( Nonfreeness implies the equivalent of ~ ax5ea , deduction form.
       (Contributed by BJ, 2-Dec-2023.) $)
    bj-nnfead $p |- ( ph -> ( E. x ps -> A. x ps ) ) $=
      ( wnnf wex wal wi bj-nnfea syl ) ABCEBCFBCGHDBCIJ $.
  $}

  ${
    bj-nnfeai.1 $e |- F// x ph $.
    $( Nonfreeness implies the equivalent of ~ ax5ea , inference form.
       (Contributed by BJ, 22-Sep-2024.) $)
    bj-nnfeai $p |- ( E. x ph -> A. x ph ) $=
      ( wnnf wex wal wi bj-nnfea ax-mp ) ABDABEABFGCABHI $.
  $}

  $( In deduction-style proofs, it is equivalent to assert that the context
     holds for all values of a variable, or that is does not depend on that
     variable.  (Contributed by BJ, 28-Mar-2026.) $)
  bj-alnnf $p |- ( ( ph -> A. x ph ) <-> ( ph -> F// x ph ) ) $=
    ( wal wi wa wnnf ax-1 biantrur pm5.4 pm4.76 3bitr3i df-bj-nnf imbi2i bitr4i
    wex ) AABCZDZAABOZADZQEZDZAABFZDAQDZASDZUCEQUAUDUCARGHAPIASQJKUBTAABLMN $.

  $( If a proposition holds, then it holds for all values of a given variable
     if and only if it does not depend on that variable.  (Contributed by BJ,
     28-Mar-2026.) $)
  bj-alnnf2 $p |- ( ph -> ( A. x ph <-> F// x ph ) ) $=
    ( wal wnnf bj-alnnf pm5.74ri ) AABCABDABEF $.

  $( Alternate definition of ~ df-bj-nnf using only primitive symbols
     ( ` -> ` , ` -. ` , ` A. ` ) in each conjunct.  (Contributed by BJ,
     20-Aug-2023.) $)
  bj-dfnnf2 $p |- ( F// x ph <->
                          ( ( ph -> A. x ph ) /\ ( -. ph -> A. x -. ph ) ) ) $=
    ( wnnf wex wi wal wa wn df-bj-nnf eximal anbi2ci bitri ) ABCABDAEZAABFEZGNA
    HZOBFEZGABIMPNAABJKL $.

  $( New nonfreeness implies old nonfreeness on minimal implicational calculus
     (the proof indicates it uses ~ ax-3 because of set.mm's definition of the
     biconditional, but the proof actually holds in minimal implicational
     calculus).  (Contributed by BJ, 28-Jul-2023.)  The proof should not rely
     on ~ df-nf except via ~ df-nf directly.
     (Proof modification is discouraged.) $)
  bj-nnfnfTEMP $p |- ( F// x ph -> F/ x ph ) $=
    ( wnnf wex wal wi wnf bj-nnfea df-nf sylibr ) ABCABDABEFABGABHABIJ $.

  $( A consequence of nonfreeness in the antecedent and the consequent of an
     implication.  (Contributed by BJ, 27-Aug-2023.) $)
  bj-nnfim1 $p |- ( ( F// x ph /\ F// x ps ) ->
                                ( ( ph -> ps ) -> ( E. x ph -> A. x ps ) ) ) $=
    ( wnnf wex wi wal bj-nnfe bj-nnfa imim12 imp syl2an ) ACDACEZAFZBBCGZFZABFM
    OFFZBCDACHBCINPQMABOJKL $.

  $( A consequence of nonfreeness in the antecedent and the consequent of an
     implication.  (Contributed by BJ, 27-Aug-2023.) $)
  bj-nnfim2 $p |- ( ( F// x ph /\ F// x ps ) ->
                                ( ( A. x ph -> E. x ps ) -> ( ph -> ps ) ) ) $=
    ( wnnf wal wi wex bj-nnfa bj-nnfe imim12 imp syl2an ) ACDAACEZFZBCGZBFZMOFA
    BFFZBCDACHBCINPQAMOBJKL $.

  $( A variable is nonfree in a theorem.  The antecedent is in the "strong
     necessity" modality of modal logic in order not to require ~ sp (modal T),
     as in ~ bj-nnfbi .  (Contributed by BJ, 28-Jul-2023.) $)
  bj-nnftht $p |- ( ( ph /\ A. x ph ) -> F// x ph ) $=
    ( wal wnnf bj-alnnf2 biimpa ) AABCABDABEF $.

  ${
    bj-nnfth.1 $e |- ph $.
    $( A variable is nonfree in a theorem, inference form.  (Contributed by BJ,
       28-Jul-2023.) $)
    bj-nnfth $p |- F// x ph $=
      ( wnnf bj-nnftht bj-mpgs ) AABDBABECF $.
  $}

  $( Proof of the closed form of ~ alrimi from modalK (compare ~ alrimiv ).
     See also ~ bj-alrim .  Actually, most proofs between ~ 19.3t and ~ 2sbbid
     could be proved without ~ ax-12 .  (Contributed by BJ, 20-Aug-2023.) $)
  bj-nnf-alrim $p |-
                  ( F// x ph -> ( A. x ( ph -> ps ) -> ( ph -> A. x ps ) ) ) $=
    ( wnnf wal wi bj-nnfa alim syl9 ) ACDAACEABFCEBCEACGABCHI $.

  $( Alias of ~ bj-nnf-alrim for labeling consistency (a standard predicate
     calculus axiom).  Closed form of ~ stdpc5 proved from modalK (obsoleting
     ~ stdpc5v ).  (Contributed by BJ, 2-Dec-2023.)  Use ~ bj-nnf-alrim
     instead.  (New usaged is discouraged.) $)
  bj-stdpc5t $p |-
                  ( F// x ph -> ( A. x ( ph -> ps ) -> ( ph -> A. x ps ) ) ) $=
    ( bj-nnf-alrim ) ABCD $.

  $( If two formulas are equivalent, then nonfreeness of a variable in one of
     them is equivalent to nonfreeness in the other.  Compare ~ nfbiit .  From
     this and ~ bj-nnfim and ~ bj-nnfnt , one can prove analogous nonfreeness
     conservation results for other propositional operators.  The antecedent is
     in the "strong necessity" modality of modal logic (see also ~ bj-nnftht )
     in order not to require ~ sp (modal T).  (Contributed by BJ,
     27-Aug-2023.) $)
  bj-nnfbi $p |- ( ( ( ph <-> ps ) /\ A. x ( ph <-> ps ) ) ->
                                                 ( F// x ph <-> F// x ps ) ) $=
    ( wb wal wa wex wi wnnf bj-hbyfrbi bj-hbxfrbi anbi12d df-bj-nnf 3bitr4g ) A
    BDZOCEFZACGAHZAACEHZFBCGBHZBBCEHZFACIBCIPQSRTABCJABCKLACMBCMN $.

  ${
    bj-nnfbd0.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( If two formulas are equivalent, then nonfreeness of a variable in one of
       them is equivalent to nonfreeness in the other, deduction form.  The
       antecedent of the conclusion is in the "strong necessity" modality of
       modal logic (see also ~ bj-nnftht ) in order not to require ~ sp (modal
       T).  See ~ bj-nnfbi .  (Contributed by BJ, 21-Mar-2026.) $)
    bj-nnfbd0 $p |- ( ( ph /\ A. x ph ) -> ( F// x ps <-> F// x ch ) ) $=
      ( wb wal wnnf alimi bj-nnfbi syl2an ) ABCFZLDGBDHCDHFADGEALDEIBCDJK $.
  $}

  ${
    bj-nnfbii.1 $e |- ( ph <-> ps ) $.
    $( If two formulas are equivalent, then nonfreeness of a variable in one of
       them is equivalent to nonfreeness in the other, inference form.  See
       ~ bj-nnfbi .  (Contributed by BJ, 18-Nov-2023.) $)
    bj-nnfbii $p |- ( F// x ph <-> F// x ps ) $=
      ( wb wnnf bj-nnfbi bj-mpgs ) ABEACFBCFECABCGDH $.
  $}

  $( A variable is nonfree in a formula if and only if it is nonfree in its
     negation.  The foward implication is intuitionistically valid (and that
     direction is sufficient for the purpose of recursively proving that some
     formulas have a given variable not free in them, like ~ bj-nnfim ).
     Intuitionistically, ` |- ( F// x -. ph <-> F// x -. -. ph ) ` .  See
     ~ nfnt .  (Contributed by BJ, 28-Jul-2023.) $)
  bj-nnfnt $p |- ( F// x ph <-> F// x -. ph ) $=
    ( wex wi wal wa wn wnnf eximal alimex anbi12ci df-bj-nnf 3bitr4i ) ABCADZAA
    BEDZFAGZBCPDZPPBEDZFABHPBHNROQAABIAABJKABLPBLM $.

  ${
    bj-nnfnth.1 $e |- -. ph $.
    $( A variable is nonfree in the negation of a theorem, inference form.
       (Contributed by BJ, 27-Aug-2023.) $)
    bj-nnfnth $p |- F// x ph $=
      ( wnnf wn bj-nnfth bj-nnfnt mpbir ) ABDAEZBDIBCFABGH $.
  $}

  $( Nonfreeness in the antecedent and the consequent of an implication implies
     nonfreeness in the implication.  (Contributed by BJ, 27-Aug-2023.) $)
  bj-nnfim $p |- ( ( F// x ph /\ F// x ps ) -> F// x ( ph -> ps ) ) $=
    ( wnnf wa wi wex wal 19.35 bj-nnfim2 biimtrid bj-nnfim1 19.38 syl6 sylanbrc
    df-bj-nnf ) ACDBCDEZABFZCGZRFRRCHZFRCDSACHBCGFQRABCIABCJKQRACGBCHFTABCLABCM
    NRCPO $.

  ${
    bj-nnfimd.1 $e |- ( ph -> F// x ps ) $.
    bj-nnfimd.2 $e |- ( ph -> F// x ch ) $.
    $( Nonfreeness in the antecedent and the consequent of an implication
       implies nonfreeness in the implication, deduction form.  (Contributed by
       BJ, 2-Dec-2023.) $)
    bj-nnfimd $p |- ( ph -> F// x ( ps -> ch ) ) $=
      ( wnnf wi bj-nnfim syl2anc ) ABDGCDGBCHDGEFBCDIJ $.
  $}

  $( Nonfreeness in both conjuncts implies nonfreeness in the conjunction.
     (Contributed by BJ, 19-Nov-2023.)  In classical logic, there is a proof
     using the definition of conjunction in terms of implication and negation,
     so using ~ bj-nnfim , ~ bj-nnfnt and ~ bj-nnfbi , but we want a proof
     valid in intuitionistic logic.  (Proof modification is discouraged.) $)
  bj-nnfan $p |- ( ( F// x ph /\ F// x ps ) -> F// x ( ph /\ ps ) ) $=
    ( wnnf wa wex wi wal df-bj-nnf 19.40 anim12 syl5 id alanimi anim12i syl2anb
    syl6 an4s sylibr ) ACDZBCDZEABEZCFZUBGZUBUBCHZGZEZUBCDTACFZAGZAACHZGZEBCFZB
    GZBBCHZGZEUGUAACIBCIUIUMUKUOUGUIUMEZUDUKUOEZUFUCUHULEUPUBABCJUHAULBKLUQUBUJ
    UNEUEAUJBUNKABUBCUBMNQORPUBCIS $.

  ${
    bj-nnfand.1 $e |- ( ph -> F// x ps ) $.
    bj-nnfand.2 $e |- ( ph -> F// x ch ) $.
    $( Nonfreeness in both conjuncts implies nonfreeness in the conjunction,
       deduction form.  Note: compared with the proof of ~ bj-nnfan , it has
       two more essential steps but fewer total steps (since there are fewer
       intermediate formulas to build) and is easier to follow and understand.
       This statement is of intermediate complexity: for simpler statements,
       closed-style proofs like that of ~ bj-nnfan will generally be shorter
       than deduction-style proofs while still easy to follow, while for more
       complex statements, the opposite will be true (and deduction-style
       proofs like that of ~ bj-nnfand will generally be easier to understand).
       (Contributed by BJ, 19-Nov-2023.)
       (Proof modification is discouraged.) $)
    bj-nnfand $p |- ( ph -> F// x ( ps /\ ch ) ) $=
      ( wa wex wi wal wnnf 19.40 bj-nnfed anim12d syl5 bj-nnfad 19.26 imbitrrdi
      df-bj-nnf sylanbrc ) ABCGZDHZUAIUAUADJZIUADKUBBDHZCDHZGAUABCDLAUDBUECABDE
      MACDFMNOAUABDJZCDJZGUCABUFCUGABDEPACDFPNBCDQRUADST $.
  $}

  $( Nonfreeness in both disjuncts implies nonfreeness in the disjunction.
     (Contributed by BJ, 19-Nov-2023.)  In classical logic, there is a proof
     using the definition of disjunction in terms of implication and negation,
     so using ~ bj-nnfim , ~ bj-nnfnt and ~ bj-nnfbi , but we want a proof
     valid in intuitionistic logic.  (Proof modification is discouraged.) $)
  bj-nnfor $p |- ( ( F// x ph /\ F// x ps ) -> F// x ( ph \/ ps ) ) $=
    ( wnnf wa wo wex wi df-bj-nnf 19.43 pm3.48 biimtrid 19.33 syl6 anim12i an4s
    wal syl2anb sylibr ) ACDZBCDZEABFZCGZUBHZUBUBCQZHZEZUBCDTACGZAHZAACQZHZEBCG
    ZBHZBBCQZHZEUGUAACIBCIUIUMUKUOUGUIUMEZUDUKUOEZUFUCUHULFUPUBABCJUHAULBKLUQUB
    UJUNFUEAUJBUNKABCMNOPRUBCIS $.

  ${
    bj-nnford.1 $e |- ( ph -> F// x ps ) $.
    bj-nnford.2 $e |- ( ph -> F// x ch ) $.
    $( Nonfreeness in both disjuncts implies nonfreeness in the disjunction,
       deduction form.  See comments for ~ bj-nnfor and ~ bj-nnfand .
       (Contributed by BJ, 2-Dec-2023.)
       (Proof modification is discouraged.) $)
    bj-nnford $p |- ( ph -> F// x ( ps \/ ch ) ) $=
      ( wo wex wi wnnf 19.43 bj-nnfed orim12d biimtrid bj-nnfad 19.33 df-bj-nnf
      wal syl6 sylanbrc ) ABCGZDHZUAIUAUADRZIUADJUBBDHZCDHZGAUABCDKAUDBUECABDEL
      ACDFLMNAUABDRZCDRZGUCABUFCUGABDEOACDFOMBCDPSUADQT $.
  $}

  $( Nonfreeness in both sides implies nonfreeness in the biconditional.
     (Contributed by BJ, 2-Dec-2023.)  (Proof modification is discouraged.) $)
  bj-nnfbit $p |- ( ( F// x ph /\ F// x ps ) -> F// x ( ph <-> ps ) ) $=
    ( wnnf wa wi bj-nnfim ancoms bj-nnfan syl2anc dfbi2 bicomi bj-nnfbii sylib
    wb ) ACDZBCDZEZABFZBAFZEZCDZABOZCDRSCDTCDZUBABCGQPUDBACGHSTCIJUAUCCUCUAABKL
    MN $.

  ${
    bj-nnfbid.1 $e |- ( ph -> F// x ps ) $.
    bj-nnfbid.2 $e |- ( ph -> F// x ch ) $.
    $( Nonfreeness in both sides implies nonfreeness in the biconditional,
       deduction form.  (Contributed by BJ, 2-Dec-2023.)
       (Proof modification is discouraged.) $)
    bj-nnfbid $p |- ( ph -> F// x ( ps <-> ch ) ) $=
      ( wi wa wnnf wb bj-nnfim syl2anc bj-nnfand dfbi2 bj-nnfbii sylibr ) ABCGZ
      CBGZHZDIBCJZDIAQRDABDIZCDIZQDIEFBCDKLAUBUARDIFECBDKLMTSDBCNOP $.
  $}

  $( Proof of the closed form of ~ exlimi from modalK (compare ~ exlimiv ).
     See also ~ bj-sylget2 .  (Contributed by BJ, 2-Dec-2023.) $)
  bj-nnf-exlim $p |-
                  ( F// x ps -> ( A. x ( ph -> ps ) -> ( E. x ph -> ps ) ) ) $=
    ( wi wal wex wnnf exim bj-nnfe syl9r ) ABDCEACFBCFBCGBABCHBCIJ $.

  $( Statement ~ 19.21t proved from modalK (obsoleting ~ 19.21v ).
     (Contributed by BJ, 2-Dec-2023.) $)
  bj-19.21t $p |-
                 ( F// x ph -> ( A. x ( ph -> ps ) <-> ( ph -> A. x ps ) ) ) $=
    ( wnnf wi wal bj-nnf-alrim wex bj-nnfe imim1d 19.38 syl6 impbid ) ACDZABECF
    ZABCFZEZABCGNQACHZPEONRAPACIJABCKLM $.

  $( Statement ~ 19.23t proved from modalK (obsoleting ~ 19.23v ).
     (Contributed by BJ, 2-Dec-2023.) $)
  bj-19.23t $p |-
                 ( F// x ps -> ( A. x ( ph -> ps ) <-> ( E. x ph -> ps ) ) ) $=
    ( wnnf wi wal wex bj-nnf-exlim bj-nnfa imim2d 19.38 syl6 impbid ) BCDZABECF
    ZACGZBEZABCHNQPBCFZEONBRPBCIJABCKLM $.

  $( One direction of ~ 19.36 from the same axioms as ~ 19.36imv .
     (Contributed by BJ, 2-Dec-2023.) $)
  bj-19.36im $p |-
                 ( F// x ps -> ( E. x ( ph -> ps ) -> ( A. x ph -> ps ) ) ) $=
    ( wnnf wex wi wal bj-nnfe bj-spimnfe syl ) BCDBCEBFABFCEACGBFFBCHABCIJ $.

  $( One direction of ~ 19.37 from the same axioms as ~ 19.37imv .
     (Contributed by BJ, 2-Dec-2023.) $)
  bj-19.37im $p |-
                 ( F// x ph -> ( E. x ( ph -> ps ) -> ( ph -> E. x ps ) ) ) $=
    ( wnnf wal wi wex bj-nnfa bj-spimenfa syl ) ACDAACEFABFCGABCGFFACHABCIJ $.

  $( Closed form of ~ 19.42 from the same axioms as ~ 19.42v .  (Contributed by
     BJ, 2-Dec-2023.) $)
  bj-19.42t $p |-
                 ( F// x ph -> ( E. x ( ph /\ ps ) <-> ( ph /\ E. x ps ) ) ) $=
    ( wnnf wa wex 19.40 bj-nnfe anim1d syl5 wal bj-nnfa 19.29 syl6 impbid ) ACD
    ZABECFZABCFZEZQACFZREPSABCGPTARACHIJPSACKZREQPAUARACLIABCMNO $.

  $( Closed form of ~ 19.41 from the same axioms as ~ 19.41v .  The same is
     doable with ~ 19.27 , ~ 19.28 , ~ 19.31 , ~ 19.32 , ~ 19.44 , ~ 19.45 .
     (Contributed by BJ, 2-Dec-2023.) $)
  bj-19.41t $p |-
                 ( F// x ps -> ( E. x ( ph /\ ps ) <-> ( E. x ph /\ ps ) ) ) $=
    ( wnnf wa wex exancom bj-19.42t bitrid biancomd ) BCDZABECFZACFZBLBAECFKBME
    ABCGBACHIJ $.

  $( Version of ~ pm11.53v with nonfreeness antecedents.  One can also prove
     the theorem with antecedent ` ( F// y A. x ph /\ A. y F// x ps ) ` .
     (Contributed by BJ, 7-Oct-2024.) $)
  bj-pm11.53vw $p |- ( ( A. x F// y ph /\ F// x A. y ps ) ->
                     ( A. x A. y ( ph -> ps ) <-> ( E. x ph -> A. y ps ) ) ) $=
    ( wnnf wal wa wi wex simpl bj-19.21t sylg albi syl bj-19.23t adantl bitrd
    wb ) ADEZCFZBDFZCEZGZABHDFZCFZAUAHZCFZACIUAHZUCUDUFRZCFUEUGRUCSUICTUBJABDKL
    UDUFCMNUBUGUHRTAUACOPQ $.

  ${
    $d x ph $.
    $( A non-occurring variable is nonfree in a formula.  (Contributed by BJ,
       28-Jul-2023.) $)
    bj-nnfv $p |- F// x ph $=
      ( wnnf wex wi wal ax5e ax-5 df-bj-nnf mpbir2an ) ABCABDAEAABFEABGABHABIJ
      $.
  $}

  ${
    $d x ph $.
    bj-nnfbd.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( If two formulas are equivalent, then nonfreeness of a variable in one of
       them is equivalent to nonfreeness in the other, deduction form.  See
       ~ bj-nnfbi .  (Contributed by BJ, 27-Aug-2023.) $)
    bj-nnfbd $p |- ( ph -> ( F// x ps <-> F// x ch ) ) $=
      ( wal wnnf wb ax-5 bj-nnfbd0 mpdan ) AADFBDGCDGHADIABCDEJK $.
  $}

  ${
    $d x ps $.  $d x y $.
    $( A variant of ~ pm11.53v .  One can similarly prove a variant with DV
       ` ( y , ph ) ` and ` A. y F// x ps ` instead of DV ` ( x , ps ) ` and
       ` A. x F// y ph ` .  (Contributed by BJ, 7-Oct-2024.) $)
    bj-pm11.53a $p |- ( A. x F// y ph ->
                     ( A. x A. y ( ph -> ps ) <-> ( E. x ph -> A. y ps ) ) ) $=
      ( wnnf wal wi wex wb bj-nnfv bj-pm11.53vw mpan2 ) ADECFBDFZCEABGDFCFACHMG
      IMCJABCDKL $.
  $}

  ${
    $d x y $.
    $( A variant of ~ equsv .  (Contributed by BJ, 7-Oct-2024.) $)
    bj-equsvt $p |- ( F// x ph -> ( A. x ( x = y -> ph ) <-> ph ) ) $=
      ( wnnf weq wi wal wex bj-19.23t ax6ev a1bi bitr4di ) ABDBCEZAFBGMBHZAFAMA
      BINABCJKL $.
  $}

  ${
    $d x y $.
    bj-equsalvwd.nf0 $e |- ( ph -> A. x ph ) $.
    bj-equsalvwd.nf $e |- ( ph -> F// x ch ) $.
    bj-equsalvwd.is $e |- ( ( ph /\ x = y ) -> ( ps <-> ch ) ) $.
    $( Variant of ~ equsalvw .  (Contributed by BJ, 7-Oct-2024.) $)
    bj-equsalvwd $p |- ( ph -> ( A. x ( x = y -> ps ) <-> ch ) ) $=
      ( weq wi wal pm5.74da albidh wnnf wb bj-equsvt syl bitrd ) ADEIZBJZDKSCJZ
      DKZCATUADFASBCHLMACDNUBCOGCDEPQR $.
  $}

  ${
    $d x y $.
    bj-equsexvwd.nf0 $e |- ( ph -> A. x ph ) $.
    bj-equsexvwd.nf $e |- ( ph -> F// x ch ) $.
    bj-equsexvwd.is $e |- ( ( ph /\ x = y ) -> ( ps <-> ch ) ) $.
    $( Variant of ~ equsexvw .  (Contributed by BJ, 7-Oct-2024.) $)
    bj-equsexvwd $p |- ( ph -> ( E. x ( x = y /\ ps ) <-> ch ) ) $=
      ( weq wa wex wn wi wal alinexa wnnf bj-nnfnt sylib notbid bj-equsalvwd
      bitr3id con4bid ) ADEIZBJDKZCUDLUCBLZMDNACLZUCBDOAUEUFDEFACDPUFDPGCDQRAUC
      JBCHSTUAUB $.
  $}

  ${
    $d x y $.
    bj-nnf-spim.nf0 $e |- ( ph -> A. x ph ) $.
    bj-nnf-spim.nf $e |- ( ph -> F// x ch ) $.
    bj-nnf-spim.is $e |- ( ( ph /\ x = y ) -> ( ps -> ch ) ) $.
    $( A universal specialization result in deduction form, proved from ~ ax-1
       -- ~ ax-6 , where the only DV condition is on ` x , y ` and where ` x `
       should be nonfree in the new proposition ` ch ` (and in the context
       ` ph ` ).  (Contributed by BJ, 4-Apr-2026.) $)
    bj-nnf-spim $p |- ( ph -> ( A. x ps -> ch ) ) $=
      ( bj-nnfed bj-spim0 ) ABCDEFACDGIHJ $.
  $}

  ${
    $d x y $.
    bj-nnf-spime.nf0 $e |- ( ph -> A. x ph ) $.
    bj-nnf-spime.nf $e |- ( ph -> F// x ps ) $.
    bj-nnf-spime.is $e |- ( ( ph /\ x = y ) -> ( ps -> ch ) ) $.
    $( An existential generalization result in deduction form, from ~ ax-1 --
       ~ ax-6 , where the only DV condition is on ` x , y ` , and where ` x `
       should be nonfree in the new proposition ` ch ` (and in the context
       ` ph ` ).  (Contributed by BJ, 4-Apr-2026.) $)
    bj-nnf-spime $p |- ( ph -> ( ps -> E. x ch ) ) $=
      ( wnnf wi wex weq ax6ev ex eximdh mpi bj-19.37im sylc ) ABDIBCJZDKZBCDKJG
      ADELZDKTDEMAUASDFAUASHNOPBCDQR $.
  $}

  ${
    $d y ph $.  $d y ps $.  $d y x $.
    bj-nnf-cbvaliv.nf0 $e |- ( ph -> A. x ph ) $.
    bj-nnf-cbvaliv.nf $e |- ( ph -> F// x ch ) $.
    bj-nnf-cbvaliv.is $e |- ( ( ph /\ x = y ) -> ( ps -> ch ) ) $.
    $( The only DV conditions are those saying that ` y ` is a fresh variable
       used to construct ` ch ` .  (Contributed by BJ, 4-Apr-2026.) $)
    bj-nnf-cbvaliv $p |- ( ph -> ( A. x ps -> A. y ch ) ) $=
      ( wal ax-5 bj-nnf-spim alrimdh ) ABDIZCEAEJMEJABCDEFGHKL $.
  $}

  ${
    $d x y $.
    bj-sbievwd.nf0 $e |- ( ph -> A. x ph ) $.
    bj-sbievwd.nf $e |- ( ph -> F// x ch ) $.
    bj-sbievwd.is $e |- ( ( ph /\ x = y ) -> ( ps <-> ch ) ) $.
    $( Variant of ~ sbievw .  (Contributed by BJ, 7-Oct-2024.) $)
    bj-sbievwd $p |- ( ph -> ( [ y / x ] ps <-> ch ) ) $=
      ( wsb weq wi wal sb6 bj-equsalvwd bitrid ) BDEIDEJBKDLACBDEMABCDEFGHNO $.
  $}

  $( Version of ~ sbft using ` F// ` , proved from core axioms.  (Contributed
     by BJ, 19-Nov-2023.) $)
  bj-sbft $p |- ( F// x ph -> ( [ t / x ] ph <-> ph ) ) $=
    ( wnnf wsb wex spsbe bj-nnfe syl5 wal bj-nnfa stdpc4 syl6 impbid ) ABDZABCE
    ZAPABFOAABCGABHIOAABJPABKABCLMN $.

  ${
    $d y x $.
    bj-nnf-cbvali.nf0 $e |- ( ph -> A. x ph ) $.
    bj-nnf-cbvali.nf1 $e |- ( ph -> A. y ph ) $.
    bj-nnf-cbvali.ps $e |- ( ph -> F// y ps ) $.
    bj-nnf-cbvali.ch $e |- ( ph -> F// x ch ) $.
    bj-nnf-cbvali.is $e |- ( ( ph /\ x = y ) -> ( ps -> ch ) ) $.
    $( Compared with ~ bj-nnf-cbvaliv , replacing the DV condition on
       ` y , ps ` with the nonfreeness condition requires ~ ax-11 .
       (Contributed by BJ, 4-Apr-2026.) $)
    bj-nnf-cbvali $p |- ( ph -> ( A. x ps -> A. y ch ) ) $=
      ( wal bj-nnfad hbald bj-nnf-spim bj-alrimd ) AABDKZPCEGABEDFABEHLMABCDEFI
      JNO $.
  $}

  ${
    $d y x $.
    bj-nnf-cbval.nf0 $e |- ( ph -> A. x ph ) $.
    bj-nnf-cbval.nf1 $e |- ( ph -> A. y ph ) $.
    bj-nnf-cbval.ps $e |- ( ph -> F// y ps ) $.
    bj-nnf-cbval.ch $e |- ( ph -> F// x ch ) $.
    bj-nnf-cbval.is $e |- ( ( ph /\ x = y ) -> ( ps <-> ch ) ) $.
    $( Compared with ~ cbvalv1 , this saves ~ ax-12 .  (Contributed by BJ,
       4-Apr-2026.) $)
    bj-nnf-cbval $p |- ( ph -> ( A. x ps <-> A. y ch ) ) $=
      ( wal weq wa biimpd bj-nnf-cbvali wb equcomi sylan2 biimprd impbid ) ABDK
      CEKABCDEFGHIADELZMBCJNOACBEDGFIHAEDLZMBCUBAUABCPEDQJRSOT $.
  $}

  $( Alternate definition of nonfreeness when ~ sp is available.  (Contributed
     by BJ, 28-Jul-2023.)  The proof should not rely on ~ df-nf .
     (Proof modification is discouraged.) $)
  bj-dfnnf3 $p |- ( F// x ph <-> ( E. x ph -> A. x ph ) ) $=
    ( wnnf wex wal bj-nnfea bj-19.21bit bj-19.23bit df-bj-nnf sylanbrc impbii
    wi ) ABCZABDZABEZLZABFPNALAOLMNABGAOBHABIJK $.

  $( New nonfreeness is equivalent to old nonfreeness on core FOL axioms plus
     ~ sp .  (Contributed by BJ, 28-Jul-2023.)  The proof should not rely on
     ~ df-nf except via ~ df-nf directly.
     (Proof modification is discouraged.) $)
  bj-nfnnfTEMP $p |- ( F// x ph <-> F/ x ph ) $=
    ( wnnf wex wal wi wnf bj-dfnnf3 df-nf bitr4i ) ABCABDABEFABGABHABIJ $.

  $( When ` ph ` is substituted for ` ps ` , this statement expresses
     nonfreeness in the weak form of nonfreeness ` ( E. -> A. ) ` .  Note that
     this could also be proved from ~ bj-nnfim , ~ bj-nnfe1 and ~ bj-nnfa1 .
     (Contributed by BJ, 9-Dec-2023.) $)
  bj-wnfnf $p |- F// x ( E. x ph -> A. x ps ) $=
    ( wex wal wi wnnf bj-wnf2 bj-wnf1 df-bj-nnf mpbir2an ) ACDBCEFZCGLCDLFLLCEF
    ABCHABCILCJK $.

  $( See ~ nfa1 .  (Contributed by BJ, 12-Aug-2023.)
     (Proof modification is discouraged.) $)
  bj-nnfa1 $p |- F// x A. x ph $=
    ( wal wnnf wex wi hbe1a bj-modal4 df-bj-nnf mpbir2an ) ABCZBDKBEKFKKBCFABGA
    BHKBIJ $.

  $( See ~ nfe1 .  (Contributed by BJ, 12-Aug-2023.)
     (Proof modification is discouraged.) $)
  bj-nnfe1 $p |- F// x E. x ph $=
    ( wex wnnf wi wal bj-modal4e hbe1 df-bj-nnf mpbir2an ) ABCZBDKBCKEKKBFEABGA
    BHKBIJ $.

  $( One of four lemmas for nonfreeness: antecedent and consequent both
     expressed using universal quantifier.  Note: this is ~ bj-hbalt .
     (Contributed by BJ, 12-Aug-2023.)  (Proof modification is discouraged.) $)
  bj-nnflemaa $p |-
                   ( A. x ( ph -> A. y ps ) -> ( A. x ph -> A. y A. x ps ) ) $=
    ( wal wi alim ax-11 syl6 ) ABDEZFCEACEJCEBCEDEAJCGBCDHI $.

  $( One of four lemmas for nonfreeness: antecedent and consequent both
     expressed using existential quantifier.  (Contributed by BJ, 12-Aug-2023.)
     (Proof modification is discouraged.) $)
  bj-nnflemee $p |-
                   ( A. x ( E. y ph -> ps ) -> ( E. y E. x ph -> E. x ps ) ) $=
    ( wex wi wal excom exim biimtrid ) ACEDEADEZCEKBFCGBCEADCHKBCIJ $.

  $( One of four lemmas for nonfreeness: antecedent expressed with universal
     quantifier and consequent expressed with existential quantifier.
     (Contributed by BJ, 12-Aug-2023.)  (Proof modification is discouraged.) $)
  bj-nnflemae $p |-
                   ( A. x ( ph -> A. y ps ) -> ( E. x ph -> A. y E. x ps ) ) $=
    ( wal wi wex exim bj-19.12 syl6 ) ABDEZFCEACGKCGBCGDEAKCHBCDIJ $.

  $( One of four lemmas for nonfreeness: antecedent expressed with existential
     quantifier and consequent expressed with universal quantifier.
     (Contributed by BJ, 12-Aug-2023.)  (Proof modification is discouraged.) $)
  bj-nnflemea $p |-
                   ( A. x ( E. y ph -> ps ) -> ( E. y A. x ph -> A. x ps ) ) $=
    ( wal wex wi bj-19.12 alim syl5 ) ACEDFADFZCEKBGCEBCEADCHKBCIJ $.

  $( See ~ nfal and ~ bj-nfalt .  (Contributed by BJ, 12-Aug-2023.)
     (Proof modification is discouraged.) $)
  bj-nnfalt $p |- ( A. x F// y ph -> F// y A. x ph ) $=
    ( wnnf wal wex wi df-bj-nnf albii simpl alimi bj-nnflemea sylbi bj-nnflemaa
    wa syl simpr sylanbrc ) ACDZBEZABEZCFUAGZUAUACEGZUACDTACFAGZAACEGZOZBEZUBSU
    FBACHIZUGUDBEUBUFUDBUDUEJKAABCLPMTUGUCUHUGUEBEUCUFUEBUDUEQKAABCNPMUACHR $.

  $( See ~ nfex and ~ bj-nfext .  (Contributed by BJ, 12-Aug-2023.)
     (Proof modification is discouraged.) $)
  bj-nnfext $p |- ( A. x F// y ph -> F// y E. x ph ) $=
    ( wnnf wal wex wi df-bj-nnf albii simpl alimi bj-nnflemee sylbi bj-nnflemae
    wa syl simpr sylanbrc ) ACDZBEZABFZCFUAGZUAUACEGZUACDTACFAGZAACEGZOZBEZUBSU
    FBACHIZUGUDBEUBUFUDBUDUEJKAABCLPMTUGUCUHUGUEBEUCUFUEBUDUEQKAABCNPMUACHR $.

  $( Version of ~ pm11.53v with nonfreeness antecedents.  (Contributed by BJ,
     7-Oct-2024.) $)
  bj-pm11.53v $p |- ( ( A. x F// y ph /\ A. y F// x ps ) ->
                     ( A. x A. y ( ph -> ps ) <-> ( E. x ph -> A. y ps ) ) ) $=
    ( wnnf wal wi wex wb bj-nnfalt bj-pm11.53vw sylan2 ) BCEDFADECFBDFZCEABGDFC
    FACHMGIBDCJABCDKL $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Adding ax-13
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( Alternate proof of ~ axc10 .  Shorter.  One can prove a version with DV
     ` ( x , y ) ` without ~ ax-13 , by using ~ ax6ev instead of ~ ax6e .
     (Contributed by BJ, 31-Mar-2021.)  (Proof modification is discouraged.) $)
  bj-axc10 $p |- ( A. x ( x = y -> A. x ph ) -> ph ) $=
    ( weq wal wi wex ax6e exim mpi axc7e syl ) BCDZABEZFBEZNBGZAOMBGPBCHMNBIJAB
    KL $.

  $( A fol lemma.  See ~ alequexv for a version with a disjoint variable
     condition requiring fewer axioms.  Can be used to reduce the proof of
     ~ spimt from 133 to 112 bytes.  (Contributed by BJ, 6-Oct-2018.) $)
  bj-alequex $p |- ( A. x ( x = y -> ph ) -> E. x ph ) $=
    ( weq wi wal wex ax6e exim mpi ) BCDZAEBFKBGABGBCHKABIJ $.

  $( A step in the proof of ~ spimt .  (Contributed by BJ, 2-May-2019.) $)
  bj-spimt2 $p |- ( A. x ( x = y -> ( ph -> ps ) ) ->
                                ( ( E. x ps -> ps ) -> ( A. x ph -> ps ) ) ) $=
    ( weq wi wal wex bj-alequex 19.35 sylib imim1d ) CDEABFZFCGZACGZBCHZBNMCHOP
    FMCDIABCJKL $.

  $( Closed form of ~ cbv3 .  (Contributed by BJ, 2-May-2019.) $)
  bj-cbv3ta $p |- ( A. x A. y ( x = y -> ( ph -> ps ) ) ->
                    ( ( A. y ( E. x ps -> ps ) /\ A. x ( ph -> A. y ph ) ) ->
                                                  ( A. x ph -> A. y ps ) ) ) $=
    ( weq wi wex wal bj-spimt2 imp alanimi bj-hbalt sylgt syl2im expimpd alcoms
    wa ) CDEABFFZBCGBFZDHZAADHFCHZQACHZBDHFZFDCRCHZDHZTUAUCUETQUBBFZDHUAUBUBDHF
    UCUDSUFDUDSUFABCDIJKAADCLUBUBBDMNOP $.

  $( Closed form of ~ cbv3 .  (Contributed by BJ, 2-May-2019.) $)
  bj-cbv3tb $p |- ( A. x A. y ( x = y -> ( ph -> ps ) ) ->
      ( ( A. y F/ x ps /\ A. x F/ y ph ) -> ( A. x ph -> A. y ps ) ) ) $=
    ( wnf wal weq wi wex 19.9t biimpd alimi nf5r bj-cbv3ta syl2ani ) BCEZDFCDGA
    BHHDFCFBCIZBHZDFAADFHZCFACFBDFHADEZCFPRDPQBBCJKLTSCADMLABCDNO $.

  $( A theorem close to a closed form of ~ hbsb3 .  (Contributed by BJ,
     2-May-2019.) $)
  bj-hbsb3t $p |- ( A. x ( ph -> A. y ph ) ->
                                     ( [ y / x ] ph -> A. x [ y / x ] ph ) ) $=
    ( wal wi wsb spsbim hbsb2a syl6 ) AACDZEBDABCFZJBCFKBDAJBCGABCHI $.

  ${
    bj-hbsb3.1 $e |- ( ph -> A. y ph ) $.
    $( Shorter proof of ~ hbsb3 .  (Contributed by BJ, 2-May-2019.)
       (Proof modification is discouraged.) $)
    bj-hbsb3 $p |- ( [ y / x ] ph -> A. x [ y / x ] ph ) $=
      ( wal wi wsb bj-hbsb3t mpg ) AACEFABCGZJBEFBABCHDI $.
  $}

  $( A theorem close to a closed form of ~ nfs1 .  (Contributed by BJ,
     2-May-2019.) $)
  bj-nfs1t $p |- ( A. x ( ph -> A. y ph ) -> F/ x [ y / x ] ph ) $=
    ( wal wi wsb wnf bj-hbsb3t axc4i nf5 sylibr ) AACDEZBDABCFZMBDEZBDMBGLNBABC
    HIMBJK $.

  $( A theorem close to a closed form of ~ nfs1 .  (Contributed by BJ,
     2-May-2019.) $)
  bj-nfs1t2 $p |- ( A. x F/ y ph -> F/ x [ y / x ] ph ) $=
    ( wnf wal wi wsb nf5r alimi bj-nfs1t syl ) ACDZBEAACEFZBEABCGBDLMBACHIABCJK
    $.

  ${
    bj-nfs1.nf $e |- F/ y ph $.
    $( Shorter proof of ~ nfs1 (three essential steps instead of four).
       (Contributed by BJ, 2-May-2019.)
       (Proof modification is discouraged.) $)
    bj-nfs1 $p |- F/ x [ y / x ] ph $=
      ( wnf wsb bj-nfs1t2 mpg ) ACEABCFBEBABCGDH $.
  $}

  $( Goal: closed form of sb8, but first need closed form of cbval.
     Remark: The equality may be a hypothesis.
     TODO: prove sb8f with fewer axioms than ~ sb8 ; use it for ~ abtrubi . $)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Removing dependencies on ax-13 (and ax-11)
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  It is known that ~ ax-13 is logically redundant (see ~ ax13w and the head
  comment of the section "Logical redundancy of ax-10--13").  More precisely,
  one can remove dependency on ~ ax-13 from every theorem in set.mm which is
  totally unbundled (i.e., has disjoint variable conditions on all setvar
  variables).  Indeed, start with the existing proof, and replace any
  occurrence of ~ ax-13 with ~ ax13w .

  This section is an experiment to see in practice if (partially) unbundled
  versions of existing theorems can be proved more efficiently without ~ ax-13
  (and using ~ ax6v / ~ ax6ev instead of ~ ax-6 / ~ ax6e , as is currently
  done).

  One reason to be optimistic is that the first few utility theorems using
  ~ ax-13 (roughly 200 of them) are then used mainly with dummy variables,
  which one can assume distinct from any other, so that the unbundled versions
  of the utility theorems suffice.

  In this section, we prove versions of theorems in the main part with dv
  conditions and not requiring ~ ax-13 , labeled bj-xxxv (we follow the proof
  of xxx but use ~ ax6v and ~ ax6ev instead of ~ ax-6 and ~ ax6e , and ~ ax-5
  instead of ~ ax13v ; shorter proofs may be possible).  When no additional dv
  condition is required, we label it bj-xxx.

  It is important to keep all the bundled theorems already in set.mm, but one
  may also add the (partially) unbundled versions which dispense with ~ ax-13 ,
  so as to remove dependencies on ~ ax-13 from many existing theorems.

  UPDATE: it turns out that several theorems of the form bj-xxxv, or minor
  variations, are already in set.mm with label xxxw.

  It is also possible to remove dependencies on ~ ax-11 , typically by
  replacing a nonfree hypothesis with a disjoint variable condition (see
  ~ cbv3v2 and following theorems).

$)

  ${
    $d x y $.
    $( Version of ~ axc10 with a disjoint variable condition, which does not
       require ~ ax-13 .  (Contributed by BJ, 14-Jun-2019.)
       (Proof modification is discouraged.) $)
    bj-axc10v $p |- ( A. x ( x = y -> A. x ph ) -> ph ) $=
      ( weq wal wi wn ax6v con3 al2imi mtoi axc7 syl ) BCDZABEZFZBEZOGZBEZGAQSN
      GZBEBCHPRTBNOIJKABLM $.
  $}

  ${
    $d x y $.
    $( Version of ~ spimt with a disjoint variable condition, which does not
       require ~ ax-13 .  (Contributed by BJ, 14-Jun-2019.)
       (Proof modification is discouraged.) $)
    bj-spimtv $p |- ( ( F/ x ps /\ A. x ( x = y -> ( ph -> ps ) ) ) ->
                                                         ( A. x ph -> ps ) ) $=
      ( weq wi wal wex wnf ax6ev exim mpi 19.35 sylib 19.9t biimpd sylan9r ) CD
      EZABFZFCGZACGZBCHZBCIZBTSCHZUAUBFTRCHUDCDJRSCKLABCMNUCUBBBCOPQ $.
  $}

  ${
    $d x y $.  $d y ph $.
    bj-cbv3hv2.nf $e |- ( ps -> A. x ps ) $.
    bj-cbv3hv2.1 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( Version of ~ cbv3h with two disjoint variable conditions, which does not
       require ~ ax-11 nor ~ ax-13 .  (Contributed by BJ, 24-Jun-2019.)
       (Proof modification is discouraged.) $)
    bj-cbv3hv2 $p |- ( A. x ph -> A. y ps ) $=
      ( nf5i cbv3v2 ) ABCDBCEGFH $.
  $}

  ${
    $d x y $.
    bj-cbv1hv.1 $e |- ( ph -> ( ps -> A. y ps ) ) $.
    bj-cbv1hv.2 $e |- ( ph -> ( ch -> A. x ch ) ) $.
    bj-cbv1hv.3 $e |- ( ph -> ( x = y -> ( ps -> ch ) ) ) $.
    $( Version of ~ cbv1h with a disjoint variable condition, which does not
       require ~ ax-13 .  (Contributed by BJ, 16-Jun-2019.)
       (Proof modification is discouraged.) $)
    bj-cbv1hv $p |- ( A. x A. y ph -> ( A. x ps -> A. y ch ) ) $=
      ( wal nfa1 nfa2 wi 2sp syl nf5d weq cbv1v ) AEIZDIZBCDERDJZAEDKZSBEUASABB
      EILADEMZFNOSCDTSACCDILUBGNOSADEPBCLLUBHNQ $.
  $}

  ${
    $d x y $.
    bj-cbv2hv.1 $e |- ( ph -> ( ps -> A. y ps ) ) $.
    bj-cbv2hv.2 $e |- ( ph -> ( ch -> A. x ch ) ) $.
    bj-cbv2hv.3 $e |- ( ph -> ( x = y -> ( ps <-> ch ) ) ) $.
    $( Version of ~ cbv2h with a disjoint variable condition, which does not
       require ~ ax-13 .  (Contributed by BJ, 16-Jun-2019.)
       (Proof modification is discouraged.) $)
    bj-cbv2hv $p |- ( A. x A. y ph -> ( A. x ps <-> A. y ch ) ) $=
      ( wal weq wb wi biimp syl6 bj-cbv1hv equcomi biimpr syl56 alcoms impbid )
      AEIDIBDIZCEIZABCDEFGADEJZBCKZBCLHBCMNOAUBUALEDACBEDGFEDJUCAUDCBLEDPHBCQRO
      ST $.
  $}

  ${
    $d x y $.
    bj-cbv2v.1 $e |- F/ x ph $.
    bj-cbv2v.2 $e |- F/ y ph $.
    bj-cbv2v.3 $e |- ( ph -> F/ y ps ) $.
    bj-cbv2v.4 $e |- ( ph -> F/ x ch ) $.
    bj-cbv2v.5 $e |- ( ph -> ( x = y -> ( ps <-> ch ) ) ) $.
    $( Version of ~ cbv2 with a disjoint variable condition, which does not
       require ~ ax-13 .  (Contributed by BJ, 16-Jun-2019.)
       (Proof modification is discouraged.) $)
    bj-cbv2v $p |- ( ph -> ( A. x ps <-> A. y ch ) ) $=
      ( wal wb nf5ri nfal syl nf5rd bj-cbv2hv ) AAEKZDKZBDKCEKLARSAEGMRDADEFNMO
      ABCDEABEHPACDIPJQO $.
  $}

  ${
    $d x y $.  $d x ph $.  $d x ch $.
    bj-cbvaldv.1 $e |- F/ y ph $.
    bj-cbvaldv.2 $e |- ( ph -> F/ y ps ) $.
    bj-cbvaldv.3 $e |- ( ph -> ( x = y -> ( ps <-> ch ) ) ) $.
    $( Version of ~ cbvald with a disjoint variable condition, which does not
       require ~ ax-13 .  (Contributed by BJ, 16-Jun-2019.)
       (Proof modification is discouraged.) $)
    bj-cbvaldv $p |- ( ph -> ( A. x ps <-> A. y ch ) ) $=
      ( nfv wnf a1i bj-cbv2v ) ABCDEADIFGCDJACDIKHL $.

    $( Version of ~ cbvexd with a disjoint variable condition, which does not
       require ~ ax-13 .  (Contributed by BJ, 16-Jun-2019.)
       (Proof modification is discouraged.) $)
    bj-cbvexdv $p |- ( ph -> ( E. x ps <-> E. y ch ) ) $=
      ( wn wal wex nfnd weq wb notbi imbitrdi bj-cbvaldv notbid df-ex 3bitr4g )
      ABIZDJZICIZEJZIBDKCEKAUBUDAUAUCDEFABEGLADEMBCNUAUCNHBCOPQRBDSCEST $.
  $}

  ${
    $d z w ph $.  $d x y ps $.  $d x y z w $.
    bj-cbval2vv.1 $e |- ( ( x = z /\ y = w ) -> ( ph <-> ps ) ) $.
    $( Version of ~ cbval2vv with a disjoint variable condition, which does not
       require ~ ax-13 .  (Contributed by BJ, 16-Jun-2019.)
       (Proof modification is discouraged.) $)
    bj-cbval2vv $p |- ( A. x A. y ph <-> A. z A. w ps ) $=
      ( nfv cbval2v ) ABCDEFAEHAFHBCHBDHGI $.

    $( Version of ~ cbvex2vv with a disjoint variable condition, which does not
       require ~ ax-13 .  (Contributed by BJ, 16-Jun-2019.)
       (Proof modification is discouraged.) $)
    bj-cbvex2vv $p |- ( E. x E. y ph <-> E. z E. w ps ) $=
      ( nfv cbvex2v ) ABCDEFAEHAFHBCHBDHGI $.
  $}

  ${
    $d ps y $.  $d ch x $.  $d ph x y $.
    bj-cbvaldvav.1 $e |- ( ( ph /\ x = y ) -> ( ps <-> ch ) ) $.
    $( Version of ~ cbvaldva with a disjoint variable condition, which does not
       require ~ ax-13 .  (Contributed by BJ, 16-Jun-2019.)
       (Proof modification is discouraged.) $)
    bj-cbvaldvav $p |- ( ph -> ( A. x ps <-> A. y ch ) ) $=
      ( nfv nfvd weq wb ex bj-cbvaldv ) ABCDEAEGABEHADEIBCJFKL $.

    $( Version of ~ cbvexdva with a disjoint variable condition, which does not
       require ~ ax-13 .  (Contributed by BJ, 16-Jun-2019.)
       (Proof modification is discouraged.) $)
    bj-cbvexdvav $p |- ( ph -> ( E. x ps <-> E. y ch ) ) $=
      ( nfv nfvd weq wb ex bj-cbvexdv ) ABCDEAEGABEHADEIBCJFKL $.
  $}

  ${
    $d w z ch $.  $d u v ph $.  $d x y ps $.  $d f g ps $.  $d z w f g $.
    $d u v w x y z $.
    bj-cbvex4vv.1 $e |- ( ( x = v /\ y = u ) -> ( ph <-> ps ) ) $.
    bj-cbvex4vv.2 $e |- ( ( z = f /\ w = g ) -> ( ps <-> ch ) ) $.
    $( Version of ~ cbvex4v with a disjoint variable condition, which does not
       require ~ ax-13 .  (Contributed by BJ, 16-Jun-2019.)
       (Proof modification is discouraged.) $)
    bj-cbvex4vv $p |- ( E. x E. y E. z E. w ph <-> E. v E. u E. f E. g ch ) $=
      ( wex weq wa 2exbidv cbvex2vw 2exbii bitri ) AGNFNZENDNBGNFNZINHNCKNJNZIN
      HNUAUBDEHIDHOEIOPABFGLQRUBUCHIBCFGJKMRST $.
  $}

  ${
    $d x y $.
    bj-equsalhv.nf $e |- ( ps -> A. x ps ) $.
    bj-equsalhv.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Version of ~ equsalh with a disjoint variable condition, which does not
       require ~ ax-13 .  Remark: this is the same as ~ equsalhw .  TODO:
       delete after moving the following paragraph somewhere.

       Remarks: ~ equsexvw has been moved to Main; Theorem ~ ax13lem2 has a DV
       version which is a simple consequence of ~ ax5e ; Theorems ~ nfeqf2 ,
       ~ dveeq2 , ~ nfeqf1 , ~ dveeq1 , ~ nfeqf , ~ axc9 , ~ ax13 , have dv
       versions which are simple consequences of ~ ax-5 .  (Contributed by BJ,
       14-Jun-2019.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    bj-equsalhv $p |- ( A. x ( x = y -> ph ) <-> ps ) $=
      ( nf5i equsalv ) ABCDBCEGFH $.
  $}

  ${
    $d x y $.
    $( Version of ~ axc11n with a disjoint variable condition; instance of
       ~ aevlem .  TODO: delete after checking surrounding theorems.
       (Contributed by BJ, 31-May-2019.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    bj-axc11nv $p |- ( A. x x = y -> A. y y = x ) $=
      ( aevlem ) ABBAC $.
  $}

  ${
    $d x y $.
    bj-aecomsv.1 $e |- ( A. x x = y -> ph ) $.
    $( Version of ~ aecoms with a disjoint variable condition, provable from
       Tarski's FOL. The corresponding version of ~ naecoms should not be very
       useful since ` -. A. x x = y ` , DV ` ( x , y ) ` is true when the
       universe has at least two objects (see ~ dtru ).  (Contributed by BJ,
       31-May-2019.)  (Proof modification is discouraged.) $)
    bj-aecomsv $p |- ( A. y y = x -> ph ) $=
      ( weq wal aevlem syl ) CBECFBCEBFACBBCGDH $.
  $}

  ${
    $d x y $.
    $( Version of ~ axc11 with a disjoint variable condition, which does not
       require ~ ax-13 nor ~ ax-10 .  Remark: the following theorems ( ~ hbae ,
       ~ nfae , ~ hbnae , ~ nfnae , ~ hbnaes ) would need to be totally
       unbundled to be proved without ~ ax-13 , hence would be simple
       consequences of ~ ax-5 or ~ nfv .  (Contributed by BJ, 31-May-2019.)
       (Proof modification is discouraged.) $)
    bj-axc11v $p |- ( A. x x = y -> ( A. x ph -> A. y ph ) ) $=
      ( wal wi axc11rv bj-aecomsv ) ABDACDECBACBFG $.
  $}

  ${
    $d x y z $.
    bj-drnf2v.1 $e |- ( A. x x = y -> ( ph <-> ps ) ) $.
    $( Version of ~ drnf2 with a disjoint variable condition, which does not
       require ~ ax-10 , ~ ax-11 , ~ ax-12 , ~ ax-13 .  Instance of ~ nfbidv .
       Note that the version of ~ axc15 with a disjoint variable condition is
       actually ~ ax12v2 (up to adding a superfluous antecedent).  (Contributed
       by BJ, 17-Jun-2019.)  (Proof modification is discouraged.) $)
    bj-drnf2v $p |- ( A. x x = y -> ( F/ z ph <-> F/ z ps ) ) $=
      ( weq wal nfbidv ) CDGCHABEFI $.
  $}

  ${
    $d x y $.
    bj-equs45fv.1 $e |- F/ y ph $.
    $( Version of ~ equs45f with a disjoint variable condition, which does not
       require ~ ax-13 .  Note that the version of ~ equs5 with a disjoint
       variable condition is actually ~ sbalex (up to adding a superfluous
       antecedent).  (Contributed by BJ, 11-Sep-2019.)
       (Proof modification is discouraged.) $)
    bj-equs45fv $p |- ( E. x ( x = y /\ ph ) <-> A. x ( x = y -> ph ) ) $=
      ( weq wa wex wi wal nf5ri anim2i eximi equs5av syl equs4v impbii ) BCEZAF
      ZBGZQAHBIZSQACIZFZBGTRUBBAUAQACDJKLABCMNABCOP $.
  $}

  ${
    $d x y $.
    $( Version of ~ hbsb2 with a disjoint variable condition, which does not
       require ~ ax-13 , and removal of ~ ax-13 from ~ hbs1 .  (Contributed by
       BJ, 23-Jun-2019.)  (Proof modification is discouraged.) $)
    bj-hbs1 $p |- ( [ y / x ] ph -> A. x [ y / x ] ph ) $=
      ( wsb weq wi wal sb6 biimpri axc4i sylbi ) ABCDZBCEAFZBGZLBGABCHZMLBLNOIJ
      K $.
  $}

  ${
    $d x y $.
    $( Version of ~ nfsb2 with a disjoint variable condition, which does not
       require ~ ax-13 , and removal of ~ ax-13 from ~ nfs1v .  (Contributed by
       BJ, 24-Jun-2019.)  (Proof modification is discouraged.) $)
    bj-nfs1v $p |- F/ x [ y / x ] ph $=
      ( wsb bj-hbs1 nf5i ) ABCDBABCEF $.
  $}

  ${
    $d x y $.
    $( Version of ~ hbsb2a with a disjoint variable condition, which does not
       require ~ ax-13 .  (Contributed by BJ, 11-Sep-2019.)
       (Proof modification is discouraged.) $)
    bj-hbsb2av $p |- ( [ y / x ] A. y ph -> A. x [ y / x ] ph ) $=
      ( wal wsb weq wi sb4av sb6 biimpri axc4i syl ) ACDBCEBCFAGZBDZABCEZBDABCH
      MOBONABCIJKL $.
  $}

  ${
    $d x y $.
    bj-hbsb3v.1 $e |- ( ph -> A. y ph ) $.
    $( Version of ~ hbsb3 with a disjoint variable condition, which does not
       require ~ ax-13 .  (Remark: the unbundled version of ~ nfs1 is given by
       ~ bj-nfs1v .)  (Contributed by BJ, 11-Sep-2019.)
       (Proof modification is discouraged.) $)
    bj-hbsb3v $p |- ( [ y / x ] ph -> A. x [ y / x ] ph ) $=
      ( wsb wal sbimi bj-hbsb2av syl ) ABCEZACFZBCEJBFAKBCDGABCHI $.
  $}

  ${
    $d x y $.
    $( Remove dependency on ~ ax-13 from ~ nfsab1 .  UPDATE / TODO: ~ nfsab1
       does not use ~ ax-13 either anymore; ~ bj-nfsab1 is shorter than
       ~ nfsab1 but uses ~ ax-12 .  (Contributed by BJ, 23-Jun-2019.)
       (Proof modification is discouraged.) $)
    bj-nfsab1 $p |- F/ x y e. { x | ph } $=
      ( cv cab wcel hbab1 nf5i ) CDABEFBABCGH $.
  $}

  ${
    $d x y $.
    bj-dtrucor2v.1 $e |- ( x = y -> x =/= y ) $.
    $( Version of ~ dtrucor2 with a disjoint variable condition, which does not
       require ~ ax-13 (nor ~ ax-4 , ~ ax-5 , ~ ax-7 , ~ ax-12 ).  (Contributed
       by BJ, 16-Jul-2019.)  (Proof modification is discouraged.) $)
    bj-dtrucor2v $p |- ( ph /\ -. ph ) $=
      ( weq wex wn wa ax6ev wi cv necon2bi pm2.01 ax-mp nex pm2.24ii ) BCEZBFAA
      GHBCIQBQQGZJRQBKCKDLQMNOP $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Strengthenings of theorems of the main part
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  Typically, these are biconditional versions of theorems in the main part
  which are formulated as implications.  They could be added after said
  implication, or sometimes replace it (by "inlining" it).

  This section contained ~ sb3b , now moved to Main.  This could also be done
  for ~ hba1 , ~ hbe1 , ~ hbe1a , ~ hbn1 , ~ modal5 .

$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Distinct var metavariables
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  The closed formula ` A. x A. y x = y ` approximately means that the var
  metavariables ` x ` and ` y ` represent the same variable v_i.  In a domain
  with at most one object, however, this formula is always true, hence the
  "approximately" in the previous sentence.

$)

  $( Biconditional version of a form of ~ hbae with commuted quantifiers, not
     requiring ~ ax-11 .  (Contributed by BJ, 12-Dec-2019.)
     (Proof modification is discouraged.) $)
  bj-hbaeb2 $p |- ( A. x x = y <-> A. x A. z x = y ) $=
    ( weq wal wi wn sp axc9 syl7 axc11r axc11 pm2.43i syl5 pm2.61ii axc4i alimi
    impbii ) ABDZAEZSCEZAESUAACADCEZCBDCEZTUAFTSUBGUCGUASAHABCIJSACKTSBEZUCUATU
    DSABLMSBCKNOPUASASCHQR $.

  $( Biconditional version of ~ hbae .  (Contributed by BJ, 6-Oct-2018.)
     (Proof modification is discouraged.) $)
  bj-hbaeb $p |- ( A. x x = y <-> A. z A. x x = y ) $=
    ( weq wal bj-hbaeb2 alcom bitri ) ABDZAEZICEAEJCEABCFIACGH $.

  $( Biconditional version of ~ hbnae (to replace it?).  (Contributed by BJ,
     6-Oct-2018.) $)
  bj-hbnaeb $p |- ( -. A. x x = y <-> A. z -. A. x x = y ) $=
    ( weq wal wn hbnae sp impbii ) ABDAEFZJCEABCGJCHI $.

  $( A special instance of ~ bj-hbaeb2 .  A lemma for distinct var
     metavariables.  Note that the right-hand side is a closed formula (a
     sentence).  (Contributed by BJ, 6-Oct-2018.) $)
  bj-dvv $p |- ( A. x x = y <-> A. x A. y x = y ) $=
    ( bj-hbaeb2 ) ABBC $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Around ~ equsal
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  As a rule of thumb, if a theorem of the form
  ` |- ( ph <-> ps ) => |- ( ch <-> th ) ` is in the database, and the "more
  precise" theorems ` |- ( ph -> ps ) => |- ( ch -> th ) ` and
  ` |- ( ps -> ph ) => |- ( th -> ch ) ` also hold (see ~ bj-bisym ), then they
  should be added to the database.  The present case is similar.  Similar
  additions can be done regarding ~ equsex (and ~ equsalh and ~ equsexh ).
  Even if only one of these two theorems holds, it should be added to the
  database.

$)

  $( Duplication of ~ wl-equsal1t , with shorter proof.  If one imposes a
     disjoint variable condition on ` x , y ` , then one can use ~ alequexv and
     reduce axiom dependencies, and similarly for the following theorems.
     Note: ~ wl-equsalcom is also interesting.  (Contributed by BJ,
     6-Oct-2018.) $)
  bj-equsal1t $p |- ( F/ x ph -> ( A. x ( x = y -> ph ) <-> ph ) ) $=
    ( wnf weq wi wal wex bj-alequex 19.9t imbitrid nf5r ala1 syl6 impbid ) ABDZ
    BCEZAFBGZARABHPAABCIABJKPAABGRABLAQBMNO $.

  ${
    bj-equsal1ti.1 $e |- F/ x ph $.
    $( Inference associated with ~ bj-equsal1t .  (Contributed by BJ,
       30-Sep-2018.) $)
    bj-equsal1ti $p |- ( A. x ( x = y -> ph ) <-> ph ) $=
      ( wnf weq wi wal wb bj-equsal1t ax-mp ) ABEBCFAGBHAIDABCJK $.
  $}

  ${
    bj-equsal1.1 $e |- F/ x ps $.
    bj-equsal1.2 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( One direction of ~ equsal .  (Contributed by BJ, 30-Sep-2018.) $)
    bj-equsal1 $p |- ( A. x ( x = y -> ph ) -> ps ) $=
      ( weq wi wal a2i alimi bj-equsal1ti sylib ) CDGZAHZCINBHZCIBOPCNABFJKBCDE
      LM $.
  $}

  ${
    bj-equsal2.1 $e |- F/ x ph $.
    bj-equsal2.2 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( One direction of ~ equsal .  (Contributed by BJ, 30-Sep-2018.) $)
    bj-equsal2 $p |- ( ph -> A. x ( x = y -> ps ) ) $=
      ( weq wi wal bj-equsal1ti a2i alimi sylbir ) ACDGZAHZCINBHZCIACDEJOPCNABF
      KLM $.
  $}

  ${
    bj-equsal.1 $e |- F/ x ps $.
    bj-equsal.2 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Shorter proof of ~ equsal .  (Contributed by BJ, 30-Sep-2018.)  Proof
       modification is discouraged to avoid using ~ equsal , but "min */exc
       equsal" is ok.  (Proof modification is discouraged.) $)
    bj-equsal $p |- ( A. x ( x = y -> ph ) <-> ps ) $=
      ( weq wi wal biimpd bj-equsal1 biimprd bj-equsal2 impbii ) CDGZAHCIBABCDE
      OABFJKBACDEOABFLMN $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Some Principia Mathematica proofs
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  References are made to the second edition (1927, reprinted 1963) of
  _Principia Mathematica_, Vol. 1.  Theorems are referred to in the form
  "PM*xx.xx".

$)

  $( Closed form of ~ stdpc5 .  (Possible to place it before ~ 19.21t and use
     it to prove ~ 19.21t ).  (Contributed by BJ, 15-Sep-2018.)
     (Proof modification is discouraged.) $)
  stdpc5t $p |- ( F/ x ph -> ( A. x ( ph -> ps ) -> ( ph -> A. x ps ) ) ) $=
    ( wnf wal wi nf5r alim syl9 ) ACDAACEABFCEBCEACGABCHI $.

  ${
    bj-stdpc5.1 $e |- F/ x ph $.
    $( More direct proof of ~ stdpc5 .  (Contributed by BJ, 15-Sep-2018.)
       (Proof modification is discouraged.) $)
    bj-stdpc5 $p |- ( A. x ( ph -> ps ) -> ( ph -> A. x ps ) ) $=
      ( wnf wi wal stdpc5t ax-mp ) ACEABFCGABCGFFDABCHI $.
  $}

  ${
    2stdpc5.1 $e |- F/ x ph $.
    2stdpc5.2 $e |- F/ y ph $.
    $( A double ~ stdpc5 (one direction of PM*11.3).  See also ~ 2stdpc4 and
       ~ 19.21vv .  (Contributed by BJ, 15-Sep-2018.)
       (Proof modification is discouraged.) $)
    2stdpc5 $p |- ( A. x A. y ( ph -> ps ) -> ( ph -> A. x A. y ps ) ) $=
      ( wi wal stdpc5 alimi syl ) ABGDHZCHABDHZGZCHAMCHGLNCABDFIJAMCEIK $.
  $}

  $( Proof of ~ 19.21t from ~ stdpc5t .  (Contributed by BJ, 15-Sep-2018.)
     (Proof modification is discouraged.) $)
  bj-19.21t0 $p |-
                  ( F/ x ph -> ( A. x ( ph -> ps ) <-> ( ph -> A. x ps ) ) ) $=
    ( wnf wi wal stdpc5t wex 19.9t imbi1d 19.38 biimtrrdi impbid ) ACDZABECFZAB
    CFZEZABCGNQACHZPEONRAPACIJABCKLM $.

  ${
    exlimii.1 $e |- F/ x ps $.
    exlimii.2 $e |- ( ph -> ps ) $.
    exlimii.3 $e |- E. x ph $.
    $( Inference associated with ~ exlimi .  Inferring a theorem when it is
       implied by an antecedent which may be true.  (Contributed by BJ,
       15-Sep-2018.) $)
    exlimii $p |- ps $=
      ( wex exlimi ax-mp ) ACGBFABCDEHI $.
  $}

  $( Proof of ~ ax-11 similar to PM's proof of ~ alcom (PM*11.2).  For a proof
     closer to PM's proof, see ~ ax11-pm2 .  Axiom ~ ax-11 is used in the proof
     only through ~ nfa2 .  (Contributed by BJ, 15-Sep-2018.)
     (Proof modification is discouraged.) $)
  ax11-pm $p |- ( A. x A. y ph -> A. y A. x ph ) $=
    ( wal wi 2sp gen2 nfa2 nfa1 2stdpc5 ax-mp ) ACDZBDZAEZBDCDMABDCDENCBABCFGMA
    CBACBHLBIJK $.

  $( Commuted form of ~ ax6e .  (Could be placed right after ~ ax6e ).
     (Contributed by BJ, 15-Sep-2018.) $)
  ax6er $p |- E. x y = x $=
    ( weq ax6e equcomi eximii ) ABCBACAABDABEF $.

  ${
    exlimiieq1.1 $e |- F/ x ph $.
    exlimiieq1.2 $e |- ( x = y -> ph ) $.
    $( Inferring a theorem when it is implied by an equality which may be true.
       (Contributed by BJ, 30-Sep-2018.) $)
    exlimiieq1 $p |- ph $=
      ( weq ax6e exlimii ) BCFABDEBCGH $.
  $}

  ${
    exlimiieq2.1 $e |- F/ y ph $.
    exlimiieq2.2 $e |- ( x = y -> ph ) $.
    $( Inferring a theorem when it is implied by an equality which may be true.
       (Contributed by BJ, 15-Sep-2018.)  (Revised by BJ, 30-Sep-2018.) $)
    exlimiieq2 $p |- ph $=
      ( weq ax6er exlimii ) BCFACDECBGH $.
  $}

  ${
    $d x y z t $.  $d z t ph $.
    $( Proof of ~ ax-11 from the standard axioms of predicate calculus, similar
       to PM's proof of ~ alcom (PM*11.2).  This proof requires that ` x ` and
       ` y ` be distinct.  Axiom ~ ax-11 is used in the proof only through
       ~ nfal , ~ nfsb , ~ sbal , ~ sb8 .  See also ~ ax11-pm .  (Contributed
       by BJ, 15-Sep-2018.)  (Proof modification is discouraged.) $)
    ax11-pm2 $p |- ( A. x A. y ph -> A. y A. x ph ) $=
      ( vt vz wal wsb wi 2stdpc4 gen2 nfv nfal 2stdpc5 ax-mp nfsbv albii sylibr
      sb8f sbal ) ACFZBFZABFZCDGZDFZUBCFUAACDGZBFZDFZUDUAUEBEGZEFZDFZUGUAUHHZEF
      DFUAUJHUKDEABCEDIJUAUHDETDBADCADKZLLTEBAECAEKZLLMNUFUIDUEBEACDEUMORPQUCUF
      DABCDSPQUBCDADBULLRQ $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Alternate definition of substitution
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( Biconditional showing two possible (dual) definitions of substitution
     ~ df-sb not using dummy variables.  (Contributed by BJ, 19-Mar-2021.) $)
  bj-sbsb $p |- ( ( ( x = y -> ph ) /\ E. x ( x = y /\ ph ) ) <->
                               ( A. x ( x = y -> ph ) \/ ( x = y /\ ph ) ) ) $=
    ( weq wi wa wex wal wo simpl pm2.27 anc2li sps olc syl56 simpr equs5 biimpd
    wn jaoi orc pm2.61i sp pm3.4 equs4 19.8a jca impbii ) BCDZAEZUIAFZBGZFZUJBH
    ZUKIZUIBHZUMUOEUMUJUPUKUOUJULJUIUJUKEBUIUJAUIAKLMUKUNNOUMULUPSZUNUOUJULPUQU
    LUNABCQRUNUKUAOUBUOUJULUNUJUKUJBUCUIAUDTUNULUKABCUEUKBUFTUGUH $.

  $( Alternate (dual) definition of substitution ~ df-sb not using dummy
     variables.  (Contributed by BJ, 19-Mar-2021.) $)
  bj-dfsb2 $p |- ( [ y / x ] ph <->
                               ( A. x ( x = y -> ph ) \/ ( x = y /\ ph ) ) ) $=
    ( wsb weq wi wa wex wal wo dfsb1 bj-sbsb bitri ) ABCDBCEZAFZNAGZBHGOBIPJABC
    KABCLM $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Lemmas for substitution
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( Substitution has no effect on a bound variable (existential quantifier
     case); see ~ sbf2 .  (Contributed by BJ, 2-May-2019.) $)
  bj-sbf3 $p |- ( [ y / x ] E. x ph <-> E. x ph ) $=
    ( wex nfe1 sbf ) ABDBCABEF $.

  $( Substitution has no effect on a bound variable (nonfreeness case); see
     ~ sbf2 .  (Contributed by BJ, 2-May-2019.) $)
  bj-sbf4 $p |- ( [ y / x ] F/ x ph <-> F/ x ph ) $=
    ( wnf nfnf1 sbf ) ABDBCABEF $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Existential uniqueness
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d x y $.
    bj-eu3f.1 $e |- F/ y ph $.
    $( Version of ~ eu3v where the disjoint variable condition is replaced with
       a nonfreeness hypothesis.  This is a "backup" of a theorem that used to
       be in the main part with label "eu3" and was deprecated in favor of
       ~ eu3v .  (Contributed by NM, 8-Jul-1994.)  (Proof shortened by BJ,
       31-May-2019.) $)
    bj-eu3f $p |- ( E! x ph <-> ( E. x ph /\ E. y A. x ( ph -> x = y ) ) ) $=
      ( weu wex wmo wa weq wi wal df-eu mof anbi2i bitri ) ABEABFZABGZHPABCIJBK
      CFZHABLQRPABCDMNO $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  First-order logic: miscellaneous
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  Miscellaneous theorems of first-order logic.

$)

  ${
    $d x ch $.
    $( Lemma for substitution.  (Contributed by BJ, 23-Jul-2023.) $)
    bj-sblem1 $p |- ( A. x ( ph -> ( ps -> ch ) ) ->
                                ( A. x ( ph -> ps ) -> ( E. x ph -> ch ) ) ) $=
      ( wi wal wex ax-2 al2imi 19.23v imbitrdi ) ABCEEZDFABEZDFACEZDFADGCELMNDA
      BCHIACDJK $.
    $( Lemma for substitution.  (Contributed by BJ, 23-Jul-2023.) $)
    bj-sblem2 $p |- ( A. x ( ph -> ( ch -> ps ) ) ->
                                ( ( E. x ph -> ch ) -> A. x ( ph -> ps ) ) ) $=
      ( wex wi wal 19.23v ax-2 al2imi biimtrrid ) ADECFACFZDGACBFFZDGABFZDGACDH
      MLNDACBIJK $.
    $( Lemma for substitution.  (Contributed by BJ, 23-Jul-2023.) $)
    bj-sblem $p |- ( A. x ( ph -> ( ps <-> ch ) ) ->
                               ( A. x ( ph -> ps ) <-> ( E. x ph -> ch ) ) ) $=
      ( wb wi wal wex pm5.74 albii albi sylbi 19.23v bitrdi ) ABCEFZDGZABFZDGZA
      CFZDGZADHCFPQSEZDGRTEOUADABCIJQSDKLACDMN $.
  $}

  ${
    $d x ps $.  $d x y $.
    $( Lemma for substitution.  (Contributed by BJ, 23-Jul-2023.) $)
    bj-sbievw1 $p |- ( [ y / x ] ( ph -> ps ) -> ( [ y / x ] ph -> ps ) ) $=
      ( wi wsb weq wal sb6 wex bj-sblem1 ax6ev a1bi 3imtr4g sylbi ) ABEZCDFCDGZ
      PECHZACDFZBEPCDIRQAECHQCJZBESBQABCKACDITBCDLMNO $.
    $( Lemma for substitution.  (Contributed by BJ, 23-Jul-2023.) $)
    bj-sbievw2 $p |- ( [ y / x ] ( ps -> ph ) -> ( ps -> [ y / x ] ph ) ) $=
      ( wi wsb weq wal sb6 wex bj-sblem2 jarr imbitrrdi syl sylbi ) BAEZCDFCDGZ
      PECHZBACDFZEZPCDIRQCJZBEQAECHZEZTQABCKUCBUBSUABUBLACDIMNO $.
    $( Lemma for substitution.  Closed form of ~ equsalvw and ~ sbievw .
       (Contributed by BJ, 23-Jul-2023.) $)
    bj-sbievw $p |- ( [ y / x ] ( ph <-> ps ) -> ( [ y / x ] ph <-> ps ) ) $=
      ( wb wsb weq wi wal sb6 wex bj-sblem ax6ev a1bi 3bitr4g sylbi ) ABEZCDFCD
      GZQHCIZACDFZBEQCDJSRAHCIRCKZBHTBRABCLACDJUABCDMNOP $.
  $}

  ${
    bj-sbievv.nfx $e |- F/ x ps $.
    bj-sbievv.nfy $e |- F/ y ph $.
    bj-sbievv.is $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Version of ~ sbie with a second nonfreeness hypothesis and shorter
       proof.  (Contributed by BJ, 18-Jul-2023.)
       (Proof modification is discouraged.) $)
    bj-sbievv $p |- ( [ y / x ] ph <-> ps ) $=
      ( wsb weq wi wal sb6f equsal bitri ) ACDHCDIAJCKBACDFLABCDEGMN $.
  $}

  $( Uniqueness is equivalent to existence being equivalent to unique
     existence.  (Contributed by BJ, 14-Oct-2022.) $)
  bj-moeub $p |- ( E* x ph <-> ( E. x ph <-> E! x ph ) ) $=
    ( wmo wex weu wi wb moeu euex impbi mpi biimp impbii bitri ) ABCABDZABEZFZO
    PGZABHQRQPOFRABIOPJKOPLMN $.

  $( Obsolete proof of ~ sbidm temporarily kept here to check it gives no
     additional insight.  (Contributed by NM, 8-Mar-1995.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  bj-sbidmOLD $p |- ( [ y / x ] [ y / x ] ph <-> [ y / x ] ph ) $=
    ( wsb wb weq equsb2 sbequ12r sbimi ax-mp sbbi mpbi ) ABCDZAEZBCDZMBCDMECBFZ
    BCDOBCGPNBCACBHIJMABCKL $.

$(
  ${
    $d ph ps $.
    @( An unprovable true scheme.

       It is true since the disjoint variable condition implies that ` x ` does
       not occur in at least one of ` ph ` and ` ps ` , so at least one of the
       two disjuncts is true.

       It is not provable from any consistent axiom system containing no
       disjoint variable condition of that form.  Indeed, such a disjoint
       variable condition cannot be produced from disjoint variable conditions
       of one of the other two forms, DV ` ( x , y ) ` or DV ` ( x , ph ) ` .
       Therefore, if it were provable, then so would the same scheme without
       this disjoint variable condition be, but that scheme is obviously false
       (take ` ph ` and ` ps ` to be ` x = y ` for instance).

       See also ~ ax-bj-00 .

       Megill's completeness theorem concerns schemes with disjoint variable
       conditions of the form DV ` ( x , y ) ` or DV ` ( x , ph ) ` .  The
       present scheme shows that it does not generalize to include schemes that
       contain disjoint variable conditions of the form DV ` ( ph , ps ) ` .

       (Contributed by BJ, 19-Mar-2021.)  (New usage is discouraged.) @)
    ax-bj-0 $a |- ( ( ph -> A. x ph ) \/ ( ps -> A. x ps ) ) $.

    @( A stronger variant of ~ ax-bj-0 with the advantage of binding
       every possible occurrence of ` x ` in any of its instances (see
       ~ df-nf ).

       (Contributed by BJ, 19-Mar-2021.)  (New usage is discouraged.) @)
    ax-bj-00 $a |- ( ( E. x ph -> A. x ph ) \/ ( E. x ps -> A. x ps ) ) $.
  $}

  ${
    $d ph x y $.
    @( Proof of ~ ax-5 from ~ ax-bj-00 (note that the use of ~ ax-5 is via
       ~ 19.8v , which is a form of ~ sp , and ~ ax-5 and the auxiliary axioms
       are used via the axiom of twoness ~ dtru ).  (Contributed by BJ,
       19-Mar-2021.)  (Proof modification is discouraged.)
       (New usage is discouraged.) @)
    bj-ax5 $p |- ( ph -> A. x ph ) $=
      ( vy wex wal 19.8v weq wi wn wa ax6ev dtru pm3.2i annim mpbi ax-bj-00 syl
      mtpor ) AABDZABEZABFBCGZBDZUABEZHZSTHUBUCIZJUDIUBUEBCKBCLMUBUCNOUAABPRQ
      $.
  $}
$)

  ${
    $d x z $.  $d y z $.  $d ph z $.  $d ps z $.
    bj-dvelimdv.nf $e |- ( ph -> F/ x ch ) $.
    bj-dvelimdv.is $e |- ( z = y -> ( ch <-> ps ) ) $.
    $( Deduction form of ~ dvelim with disjoint variable conditions.  Uncurried
       (imported) form of ~ bj-dvelimdv1 .  Typically, ` z ` is a fresh
       variable used for the implicit substitution hypothesis that results in
       ` ch ` (namely, ` ps ` can be thought as ` ps ( x , y ) ` and ` ch ` as
       ` ps ( x , z ) ` ).  So the theorem says that if x is effectively free
       in ` ps ( x , z ) ` , then if x and y are not the same variable, then
       ` x ` is also effectively free in ` ps ( x , y ) ` , in a context
       ` ph ` .

       One can weaken the implicit substitution hypothesis by adding the
       antecedent ` ph ` but this typically does not make the theorem much more
       useful.  Similarly, one could use nonfreeness hypotheses instead of
       disjoint variable conditions but since this result is typically used
       when ` z ` is a dummy variable, this would not be of much benefit.  One
       could also remove DV ` ( x , z ) ` since in the proof ~ nfv can be
       replaced with ~ nfal followed by ~ nfn .

       Remark: ~ nfald uses ~ ax-11 ; it might be possible to inline and use
       ~ ax11w instead, but there is still a use via ~ 19.12 anyway.
       (Contributed by BJ, 20-Oct-2021.)
       (Proof modification is discouraged.) $)
    bj-dvelimdv $p |- ( ( ph /\ -. A. x x = y ) -> F/ x ps ) $=
      ( weq wi wal wn wa equsalvw bicomi nfv nfan wnf nfeqf2 adantl nfimd nfald
      adantr nfxfrd ) BFEIZCJZFKZADEIDKLZMZDUGBCBFEHNOUIUFDFAUHFAFPUHFPQUIUECDU
      HUEDRADEFSTACDRUHGUCUAUBUD $.

    $( Curried (exported) form of ~ bj-dvelimdv (of course, one is directly
       provable from the other, but we keep this proof for illustration
       purposes).  (Contributed by BJ, 20-Oct-2021.)
       (Proof modification is discouraged.) $)
    bj-dvelimdv1 $p |- ( ph -> ( -. A. x x = y -> F/ x ps ) ) $=
      ( weq wal wn wnf nfeqf2 bj-nfimt syl2imc alrimdv bj-nfalt equsalvw nfbii
      wi bj-syl66ib ) ADEIDJKZBDLFEIZCTZDLZFJUDFJZDLAUBUEFUBUCDLACDLUEDEFMGUCCD
      NOPUDFDQUFBDCBFEHRSUA $.
  $}

  ${
    $d x z $.  $d y z $.  $d ph z $.
    bj-dvelimv.nf $e |- F/ x ps $.
    bj-dvelimv.is $e |- ( z = y -> ( ps <-> ph ) ) $.
    $( A version of ~ dvelim using the "nonfree" idiom.  (Contributed by BJ,
       20-Oct-2021.)  (Proof modification is discouraged.) $)
    bj-dvelimv $p |- ( -. A. x x = y -> F/ x ph ) $=
      ( weq wal wn wnf wi wtru a1i bj-dvelimdv1 mptru ) CDHCIJACKLMABCDEBCKMFNG
      OP $.
  $}

  ${
    $d t x z $.  $d t y $.
    $( Nonfreeness in a membership statement.  (Contributed by BJ,
       20-Oct-2021.)  (Proof modification is discouraged.) $)
    bj-nfeel2 $p |- ( -. A. x x = y -> F/ x y e. z ) $=
      ( vt wel nfv elequ1 bj-dvelimv ) BCEDCEZABDIAFDBCGH $.
  $}

  ${
    $d t x $.  $d t y $.  $d t z $.
    $( Proof of a version of ~ axc14 using the "nonfree" idiom.  (Contributed
       by BJ, 20-Oct-2021.)  (Proof modification is discouraged.) $)
    bj-axc14nf $p |-
         ( -. A. z z = x -> ( -. A. z z = y -> F/ z x e. y ) ) $=
      ( vt weq wal wn wel bj-nfeel2 elequ2 bj-dvelimdv1 ) CAECFGABHADHCBDCADIDB
      AJK $.
  $}

  $( Alternate proof of ~ axc14 (even when inlining the above results, this
     gives a shorter proof).  (Contributed by BJ, 20-Oct-2021.)
     (Proof modification is discouraged.) $)
  bj-axc14 $p |-
         ( -. A. z z = x -> ( -. A. z z = y -> ( x e. y -> A. z x e. y ) ) ) $=
    ( weq wal wn wel wnf wi bj-axc14nf nf5r a1i syld ) CADCEFZCBDCEFABGZCHZOOCE
    IZABCJPQINOCKLM $.

  ${
    mobidvALT.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $d x y ph $.  $d y ps $.  $d y ch $.
    $( Alternate proof of ~ mobidv directly from its analogues ~ albidv and
       ~ exbidv , using deduction style.  Note the proof structure, similar to
       ~ mobi .  (Contributed by Mario Carneiro, 7-Oct-2016.)  Reduce axiom
       dependencies and shorten proof.  Remove dependency on ~ ax-12 by
       adapting proof of ~ mobid .  (Revised by BJ, 26-Sep-2022.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    mobidvALT $p |- ( ph -> ( E* x ps <-> E* x ch ) ) $=
      ( vy weq wi wal wex wmo imbi1d albidv exbidv dfmo 3bitr4g ) ABDFGZHZDIZFJ
      CQHZDIZFJBDKCDKASUAFARTDABCQELMNBDFOCDFOP $.
  $}

  $( Alternate proof of ~ sbn1 , not using the false constant.  (Contributed by
     BJ, 18-Sep-2024.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  sbn1ALT $p |- ( [ t / x ] -. ph -> -. [ t / x ] ph ) $=
    ( wn wsb wa nsb pm3.24 mpg sban mtbi pm3.21 mtoi ) ADZBCEZABCEZPOFZANFZBCEZ
    QRDSDBRBCGAHIANBCJKOPLM $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Set theory
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Eliminability of class terms
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  In this section, we give a sketch of the proof of the Eliminability Theorem
  for class terms in an extensional set theory where quantification occurs only
  over set variables.

  Eliminability of class variables using the $a-statements ~ ax-ext ,
  ~ df-clab , ~ df-cleq , ~ df-clel is an easy result, proved for instance in
  Appendix X of Azriel Levy, _Basic Set Theory_, Dover Publications, 2002.
  Note that viewed from the set.mm axiomatization, it is a metatheorem not
  formalizable in set.mm.  It states: every formula in the language of
  FOL + ` e. ` + class terms, but without class variables, is provably
  equivalent (over {FOL, ~ ax-ext , ~ df-clab , ~ df-cleq , ~ df-clel }) to a
  formula in the language of FOL + ` e. ` (that is, without class terms).

  The proof goes by induction on the complexity of the formula (see op. cit.
  for details).  The base case is that of atomic formulas.  The atomic formulas
  containing class terms are of one of the six following forms:
  for equality,
  ` x = { y | ph } ` , ` { x | ph } = y ` , ` { x | ph } = { y | ps } ` ,
  and for membership,
  ` y e. { x | ph } ` , ` { x | ph } e. y ` , ` { x | ph } e. { y | ps } ` .
  These cases are dealt with by ~ eliminable-veqab ,  ~ eliminable-abeqv ,
  ~ eliminable-abeqab ,  ~ eliminable-velab ,  ~ eliminable-abelv ,
  ~ eliminable-abelab respectively, which are all proved from {FOL, ~ ax-ext ,
  ~ df-clab , ~ df-cleq , ~ df-clel }.

  (Details on the proof of the above six theorems.  To understand how they
  were systematically proved, look at the theorems "eliminablei" below, which
  are special instances of ~ df-clab , ~ dfcleq (proved from {FOL, ~ ax-ext ,
  ~ df-cleq }), and ~ dfclel (proved from {FOL, ~ df-clel }).  Indeed, denote
  by (i) the formula proved by "eliminablei".  One sees that the RHS of (1) has
  no class terms, the RHS's of (2x) have only class terms of the form dealt
  with by (1), and the RHS's of (3x) have only class terms of the forms dealt
  with by (1) and (2a).  Note that in order to prove ~ eliminable2a ,
  ~ eliminable2b and ~ eliminable3a , we need to substitute a class variable
  for a setvar variable.  This is possible because setvars are class terms:
  this is the content of the syntactic theorem ~ cv , which is used in these
  proofs (this does not appear in the html pages but it is in the set.mm file
  and you can check it using the Metamath program).)

  The induction step relies on the fact that any formula is a FOL-combination
  of atomic formulas, so if one found equivalents for all atomic formulas
  constituting the formula, then the same FOL-combination of these equivalents
  will be equivalent to the original formula.

  Note that one has a slightly more precise result: if the original formula has
  only class terms appearing in atomic formulas of the form
   ` y e. { x | ph } ` , then ~ df-clab is sufficient (over FOL) to eliminate
  class terms, and if the original formula has only class terms appearing in
  atomic formulas of the form ` y e. { x | ph } ` and equalities, then
  ~ df-clab , ~ ax-ext and ~ df-cleq are sufficient (over FOL) to eliminate
  class terms.

  To prove that { ~ df-clab , ~ df-cleq , ~ df-clel } provides a definitional
  extension of {FOL, ~ ax-ext }, one needs to prove both the above
  Eliminability Theorem, which compares the expressive powers of the languages
  with and without class terms, and the Conservativity Theorem, which compares
  the deductive powers when one adds { ~ df-clab , ~ df-cleq , ~ df-clel }.  It
  states that a formula without class terms is provable in one axiom system if
  and only if it is provable in the other, and that this remains true when one
  adds further definitions to {FOL, ~ ax-ext }.  It is also proved in op. cit.
  The proof is more difficult, since one has to construct for each proof of a
  statement without class terms, an associated proof not using { ~ df-clab ,
  ~ df-cleq , ~ df-clel }.  It involves a careful case study on the structure
  of the proof tree.

$)

  $( A theorem used to prove the base case of the Eliminability Theorem (see
     section comment).  (Contributed by BJ, 19-Oct-2019.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  eliminable1 $p |- ( y e. { x | ph } <-> [ y / x ] ph ) $=
    ( df-clab ) ACBD $.

  ${
    $d x z $.  $d y z $.  $d ph z $.  $d ps z $.
    $( A theorem used to prove the base case of the Eliminability Theorem (see
       section comment).  (Contributed by BJ, 19-Oct-2019.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    eliminable2a $p |-
                  ( x = { y | ph } <-> A. z ( z e. x <-> z e. { y | ph } ) ) $=
      ( cv cab dfcleq ) DBEACFG $.

    $( A theorem used to prove the base case of the Eliminability Theorem (see
       section comment).  (Contributed by BJ, 19-Oct-2019.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    eliminable2b $p |-
                  ( { x | ph } = y <-> A. z ( z e. { x | ph } <-> z e. y ) ) $=
      ( cab cv dfcleq ) DABECFG $.

    $( A theorem used to prove the base case of the Eliminability Theorem (see
       section comment).  (Contributed by BJ, 19-Oct-2019.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    eliminable2c $p |- ( { x | ph } = { y | ps } <->
                              A. z ( z e. { x | ph } <-> z e. { y | ps } ) ) $=
      ( cab dfcleq ) EACFBDFG $.

    $( A theorem used to prove the base case of the Eliminability Theorem (see
       section comment).  (Contributed by BJ, 19-Oct-2019.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    eliminable3a $p |-
                   ( { x | ph } e. y <-> E. z ( z = { x | ph } /\ z e. y ) ) $=
      ( cab cv dfclel ) DABECFG $.

    $( A theorem used to prove the base case of the Eliminability Theorem (see
       section comment).  (Contributed by BJ, 19-Oct-2019.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    eliminable3b $p |- ( { x | ph } e. { y | ps } <->
                                E. z ( z = { x | ph } /\ z e. { y | ps } ) ) $=
      ( cab dfclel ) EACFBDFG $.
  $}

  $( A theorem used to prove the base case of the Eliminability Theorem (see
     section comment): variable belongs to abstraction.  (Contributed by BJ,
     30-Apr-2024.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  eliminable-velab $p |- ( y e. { x | ph } <-> [ y / x ] ph ) $=
    ( df-clab ) ACBD $.

  ${  $d x z $.  $d y z $.  $d ph z $.
    $( A theorem used to prove the base case of the Eliminability Theorem (see
       section comment): variable equals abstraction.  (Contributed by BJ,
       30-Apr-2024.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    eliminable-veqab $p |-
                     ( x = { y | ph } <-> A. z ( z e. x <-> [ z / y ] ph ) ) $=
      ( cv cab wceq wel wcel wal wsb dfcleq eliminable-velab bibi2i albii bitri
      wb ) BEZACFZGDBHZDESIZQZDJTACDKZQZDJDRSLUBUDDUAUCTACDMNOP $.
  $}

  ${  $d x z $.  $d y z $.  $d ph z $.
    $( A theorem used to prove the base case of the Eliminability Theorem (see
       section comment): abstraction equals variable.  (Contributed by BJ,
       30-Apr-2024.)  Beware not to use symmetry of class equality.
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    eliminable-abeqv $p |-
                     ( { x | ph } = y <-> A. z ( [ z / x ] ph <-> z e. y ) ) $=
      ( cab cv wceq wcel wel wal wsb dfcleq eliminable-velab bibi1i albii bitri
      wb ) ABEZCFZGDFRHZDCIZQZDJABDKZUAQZDJDRSLUBUDDTUCUAABDMNOP $.
  $}

  ${  $d x z $.  $d y z $.  $d ph z $.  $d ps z $.
    $( A theorem used to prove the base case of the Eliminability Theorem (see
       section comment): abstraction equals abstraction.  (Contributed by BJ,
       30-Apr-2024.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    eliminable-abeqab $p |- ( { x | ph } = { y | ps } <->
                                    A. z ( [ z / x ] ph <-> [ z / y ] ps ) ) $=
      ( cab wceq cv wcel wb wal wsb dfcleq eliminable-velab bibi12i albii bitri
      ) ACFZBDFZGEHZRIZTSIZJZEKACELZBDELZJZEKERSMUCUFEUAUDUBUEACENBDENOPQ $.
  $}

  ${  $d t x z $.  $d y z $.  $d ph z $.  $d ph t $.
    $( A theorem used to prove the base case of the Eliminability Theorem (see
       section comment): abstraction belongs to variable.  (Contributed by BJ,
       30-Apr-2024.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    eliminable-abelv $p |- ( { x | ph } e. y <->
                       E. z ( A. t ( t e. z <-> [ t / x ] ph ) /\ z e. y ) ) $=
      ( cab cv wcel wceq wel wa wex wsb wb dfclel eliminable-veqab anbi1i exbii
      wal bitri ) ABFZCGZHDGUAIZDCJZKZDLEDJABEMNESZUDKZDLDUAUBOUEUGDUCUFUDADBEP
      QRT $.
  $}

  ${  $d t x z $.  $d y z $.  $d ph z $.  $d ph t $.  $d ps z $.
    $( A theorem used to prove the base case of the Eliminability Theorem (see
       section comment): abstraction belongs to abstraction.  (Contributed by
       BJ, 30-Apr-2024.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    eliminable-abelab $p |- ( { x | ph } e. { y | ps } <->
                 E. z ( A. t ( t e. z <-> [ t / x ] ph ) /\ [ z / y ] ps ) ) $=
      ( cab wcel cv wceq wa wex wel wb dfclel eliminable-veqab eliminable-velab
      wsb wal anbi12i exbii bitri ) ACGZBDGZHEIZUCJZUEUDHZKZELFEMACFRNFSZBDERZK
      ZELEUCUDOUHUKEUFUIUGUJAECFPBDEQTUAUB $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Classes without the axiom of extensionality
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  A few results about classes can be proved without using ~ ax-ext .  One could
  move all theorems from ~ cab to ~ df-clel (except for ~ dfcleq and ~ cvjust )
  in a subsection "Classes" before the subsection on the axiom of
  extensionality, together with the theorems below.  In that subsection, the
  last statement should be ~ df-cleq .

  Note that without ~ ax-ext , the $a-statements ~ df-clab , ~ df-cleq , and
  ~ df-clel are no longer eliminable (see previous section) (but PROBABLY
  ~ df-clab is still conservative , while ~ df-cleq and ~ df-clel are not).
  This is not a reason not to study what is provable
  with them but without ~ ax-ext , in order to gauge their strengths more
  precisely.

  Before that subsection, a subsection "The membership predicate" could group
  the statements with ` e. ` that are currently in the FOL part (including
  ~ wcel , ~ wel , ~ ax-8 , ~ ax-9 ).

  Remark: the weakening of ~ eleq1 / ~ eleq2 to ~ eleq1w / ~ eleq2w can also
  be done with ~ eleq1i , ~ eqeltri , ~ eqeltrri , ~ eleq1a , ~ eleq1d ,
  ~ eqeltrd , ~ eqeltrrd , ~ eqneltrd , ~ eqneltrrd , ~ nelneq .

  Remark: possibility to remove dependency on ~ ax-10 , ~ ax-11 , ~ ax-13 from
  ~ nfcri and theorems using it if one adds a disjoint variable condition (that
  theorem is typically used with dummy variables, so the disjoint variable
  condition addition is not very restrictive), and then shorten ~ nfnfc .

$)

  ${
    $d A x $.  $d x y $.
    $( Duplicate of ~ issettru and ~ bj-issettruALTV .

       Lemma for ~ bj-denotesALTV .  (Contributed by BJ, 24-Apr-2024.)
       (Proof modification is discouraged.) $)
    bj-denoteslem $p |- ( E. x x = A <-> A e. { y | T. } ) $=
      ( cv wceq wex wtru cab wcel wa vextru biantru exbii dfclel bitr4i ) ADZCE
      ZAFQPGBHZIZJZAFCRIQTASQBAKLMACRNO $.
  $}

  ${
    $d x A $.  $d y A $.  $d x z $.  $d y z $.
    $( Moved to main as ~ iseqsetv-clel and kept for the comments.

       This would be the justification theorem for the definition of the unary
       predicate "E!" by ` |- ( ` E! ` A <-> E. x x = A ) ` which could be
       interpreted as " ` A ` exists" (as a set) or " ` A ` denotes" (in the
       sense of free logic).

       A shorter proof using ~ bitri (to add an intermediate proposition
       ` E. z z = A ` with a fresh ` z ` ), ~ cbvexvw , and ~ eqeq1 , requires
       the core axioms and { ~ ax-9 , ~ ax-ext , ~ df-cleq } whereas this proof
       requires the core axioms and { ~ ax-8 , ~ df-clab , ~ df-clel }.

       Theorem ~ bj-issetwt proves that "existing" is equivalent to being a
       member of a class abstraction.  It also requires, with the present
       proof, { ~ ax-8 , ~ df-clab , ~ df-clel } (whereas with the shorter
       proof from ~ cbvexvw and ~ eqeq1 it would require { ~ ax-8 , ~ ax-9 ,
       ~ ax-ext , ~ df-clab , ~ df-cleq , ~ df-clel }).  That every class is
       equal to a class abstraction is proved by ~ abid1 , which requires {
       ~ ax-8 , ~ ax-9 , ~ ax-ext , ~ df-clab , ~ df-cleq , ~ df-clel }.

       Note that there is no disjoint variable condition on ` x , y ` but the
       theorem does not depend on ~ ax-13 .  Actually, the proof depends only
       on the logical axioms ~ ax-1 through ~ ax-7 and ~ sp .

       The symbol "E!" was chosen to be reminiscent of the analogous predicate
       in (inclusive or non-inclusive) free logic, which deals with the
       possibility of nonexistent objects.  This analogy should not be taken
       too far, since here there are no equality axioms for classes: these are
       derived from ~ ax-ext and ~ df-cleq (e.g., ~ eqid and ~ eqeq1 ).  In
       particular, one cannot even prove ` |- E. x x = A => |- A = A ` without
       ~ ax-ext and ~ df-cleq .

       (Contributed by BJ, 29-Apr-2019.)
       (Proof modification is discouraged.) $)
    bj-denotesALTV $p |- ( E. x x = A <-> E. y y = A ) $=
      ( vz cv wceq wex wtru cab wcel bj-denoteslem bitr4i ) AECFAGCHDIJBECFBGAD
      CKBDCKL $.
    $( $j usage 'bj-denotesALTV' avoids 'ax-9' 'ax-10' 'ax-11' 'ax-12' 'ax-13'
       'ax-ext' 'df-cleq'; $)
  $}

  ${
    $d A x $.  $d A z $.  $d y z $.
    $( Moved to main as ~ issettru and kept for the comments.

       Weak version of ~ isset without ~ ax-ext .  (Contributed by BJ,
       24-Apr-2024.)  (Proof modification is discouraged.) $)
    bj-issettruALTV $p |- ( E. x x = A <-> A e. { y | T. } ) $=
      ( vz cv wceq wex wtru cab wcel iseqsetv-clel issettru bitri ) AECFAGDECFD
      GCHBIJADCKDBCLM $.
    $( $j usage 'bj-issettruALTV' avoids 'ax-9' 'ax-10' 'ax-11' 'ax-12' 'ax-13'
       'ax-ext' 'df-cleq'; $)
  $}

  ${
    $d A z $.  $d x z $.  $d y z $.
    $( This is as close as we can get to proving extensionality for "the"
       "universal" class without ~ ax-ext .  (Contributed by BJ, 24-Apr-2024.)
       (Proof modification is discouraged.) $)
    bj-elabtru $p |- ( A e. { x | T. } <-> A e. { y | T. } ) $=
      ( vz wtru cab wcel cv wceq wex issettru bitr3i ) CEAFGDHCIDJCEBFGDACKDBCK
      L $.
    $( $j usage 'bj-elabtru' avoids 'ax-9' 'ax-10' 'ax-11' 'ax-12' 'ax-13'
       'ax-ext' 'df-cleq'; $)
  $}

  ${
    $d y A $.  $d z x $.  $d z A $.  $d z ph $.
    $( Closed form of ~ bj-issetw .  (Contributed by BJ, 29-Apr-2019.)
       (Proof modification is discouraged.) $)
    bj-issetwt $p |- ( A. x ph -> ( A e. { x | ph } <-> E. y y = A ) ) $=
      ( vz wal cab wcel cv wceq wa wex wb dfclel a1i vexwt bicomd iseqsetv-clel
      biantrud exbidv 3bitrd ) ABFZDABGZHZEIZDJZUEUCHZKZELZUFELZCIDJCLZUDUIMUBE
      DUCNOUBUHUFEUBUFUHUBUGUFABEPSQTUJUKMUBECDROUA $.
    $( $j usage 'bj-issetwt' avoids 'ax-9' 'ax-10' 'ax-11' 'ax-12' 'ax-13'
       'ax-ext' 'df-cleq'; $)
  $}

  ${
    $d y A $.
    bj-issetw.1 $e |- ph $.
    $( The closest one can get to ~ isset without using ~ ax-ext .  See also
       ~ vexw .  Note that the only disjoint variable condition is between
       ` y ` and ` A ` .  From there, one can prove ~ isset using ~ eleq2i
       (which requires ~ ax-ext and ~ df-cleq ).  (Contributed by BJ,
       29-Apr-2019.)  (Proof modification is discouraged.) $)
    bj-issetw $p |- ( A e. { x | ph } <-> E. y y = A ) $=
      ( cab wcel cv wceq wex wb bj-issetwt mpg ) ADABFGCHDICJKBABCDLEM $.
    $( $j usage 'bj-issetw' avoids 'ax-9' 'ax-10' 'ax-11' 'ax-12' 'ax-13'
       'ax-ext' 'df-cleq'; $)
  $}

  ${
    $d x A $.  $d x V $.
    bj-issetiv.1 $e |- A e. V $.
    $( Version of ~ bj-isseti with a disjoint variable condition on ` x , V ` .
       The hypothesis uses ` V ` instead of ` _V ` for extra generality.  This
       is indeed more general than ~ isseti as long as ~ elex is not available
       (and the non-dependence of ~ bj-issetiv on special properties of the
       universal class ` _V ` is obvious).  Prefer its use over ~ bj-isseti
       when sufficient (in particular when ` V ` is substituted for ` _V ` ).
       (Contributed by BJ, 14-Sep-2019.)
       (Proof modification is discouraged.) $)
    bj-issetiv $p |- E. x x = A $=
      ( wcel cv wceq wex elissetv ax-mp ) BCEAFBGAHDABCIJ $.
      $( $j usage 'bj-issetiv' avoids 'ax-9' 'ax-10' 'ax-11' 'ax-12' 'ax-13'
       'ax-ext' 'df-clab' 'df-cleq' 'cvv'; $)
  $}

  ${
    $d x A $.
    bj-isseti.1 $e |- A e. V $.
    $( Version of ~ isseti with a class variable ` V ` in the hypothesis
       instead of ` _V ` for extra generality.  This is indeed more general
       than ~ isseti as long as ~ elex is not available (and the non-dependence
       of ~ bj-isseti on special properties of the universal class ` _V ` is
       obvious).  Use ~ bj-issetiv instead when sufficient (in particular when
       ` V ` is substituted for ` _V ` ).  (Contributed by BJ, 13-Jun-2019.)
       (Proof modification is discouraged.) $)
    bj-isseti $p |- E. x x = A $=
      ( wcel cv wceq wex elisset ax-mp ) BCEAFBGAHDABCIJ $.
      $( $j usage 'bj-isseti' avoids 'ax-9' 'ax-10' 'ax-11' 'ax-12' 'ax-13'
       'ax-ext' 'df-cleq' 'cvv'; $)
  $}

  ${
    bj-ralvw.1 $e |- ps $.
    $( A weak version of ~ ralv not using ~ ax-ext (nor ~ df-cleq , ~ df-clel ,
       ~ df-v ), and only core FOL axioms.  See also ~ bj-rexvw .  The
       analogues for ~ reuv and ~ rmov are not proved.  (Contributed by BJ,
       16-Jun-2019.)  (Proof modification is discouraged.) $)
    bj-ralvw $p |- ( A. x e. { y | ps } ph <-> A. x ph ) $=
      ( cab wral cv wcel wi wal df-ral vexw a1bi albii bitr4i ) ACBDFZGCHQIZAJZ
      CKACKACQLASCRABDCEMNOP $.
  $}

  ${
    bj-rexvw.1 $e |- ps $.
    $( A weak version of ~ rexv not using ~ ax-ext (nor ~ df-cleq , ~ df-clel ,
       ~ df-v ), and only core FOL axioms.  See also ~ bj-ralvw .  (Contributed
       by BJ, 16-Jun-2019.)  (Proof modification is discouraged.) $)
    bj-rexvw $p |- ( E. x e. { y | ps } ph <-> E. x ph ) $=
      ( cab wrex cv wcel wa wex df-rex vexw biantrur exbii bitr4i ) ACBDFZGCHQI
      ZAJZCKACKACQLASCRABDCEMNOP $.
  $}

  ${
    bj-rababw.1 $e |- ps $.
    $( A weak version of ~ rabab not using ~ df-clel nor ~ df-v (but requiring
       ~ ax-ext ) nor ~ ax-12 .  (Contributed by BJ, 16-Jun-2019.)
       (Proof modification is discouraged.) $)
    bj-rababw $p |- { x e. { y | ps } | ph } = { x | ph } $=
      ( cab crab cv wcel wa df-rab vexw biantrur abbii eqtr4i ) ACBDFZGCHPIZAJZ
      CFACFACPKARCQABDCELMNO $.
  $}

  ${
    $d x A $.  $d x B $.  $d x V $.  $d x y $.  $d x ph $.
    bj-rexcom4bv.1 $e |- B e. V $.
    $( Version of ~ rexcom4b and ~ bj-rexcom4b with a disjoint variable
       condition on ` x , V ` , hence removing dependency on ~ df-sb and
       ~ df-clab (so that it depends on ~ df-clel and ~ df-rex only on top of
       first-order logic).  Prefer its use over ~ bj-rexcom4b when sufficient
       (in particular when ` V ` is substituted for ` _V ` ).  Note the ` V `
       in the hypothesis instead of ` _V ` .  (Contributed by BJ, 14-Sep-2019.)
       (Proof modification is discouraged.) $)
    bj-rexcom4bv $p |- ( E. x E. y e. A ( ph /\ x = B ) <-> E. y e. A ph ) $=
      ( cv wceq wa wrex wex rexcom4a bj-issetiv biantru rexbii bitr4i ) ABHEIZJ
      CDKBLARBLZJZCDKACDKARBCDMATCDSABEFGNOPQ $.
  $}

  ${
    $d x A $.  $d x B $.  $d x y $.  $d x ph $.
    bj-rexcom4b.1 $e |- B e. V $.
    $( Remove from ~ rexcom4b dependency on ~ ax-ext and ~ ax-13 (and on
       ~ df-or , ~ df-cleq , ~ df-nfc , ~ df-v ).  The hypothesis uses ` V `
       instead of ` _V ` (see ~ bj-isseti for the motivation).  Use
       ~ bj-rexcom4bv instead when sufficient (in particular when ` V ` is
       substituted for ` _V ` ).  (Contributed by BJ, 16-Jun-2019.)
       (Proof modification is discouraged.) $)
    bj-rexcom4b $p |- ( E. x E. y e. A ( ph /\ x = B ) <-> E. y e. A ph ) $=
      ( cv wceq wa wrex wex rexcom4a bj-isseti biantru rexbii bitr4i ) ABHEIZJC
      DKBLARBLZJZCDKACDKARBCDMATCDSABEFGNOPQ $.
  $}

  $( The FOL content of ~ ceqsalt .  Lemma for ~ bj-ceqsalt and ~ bj-ceqsaltv .
     (Contributed by BJ, 26-Sep-2019.)  (Proof modification is discouraged.) $)
  bj-ceqsalt0 $p |- ( ( F/ x ps /\ A. x ( th -> ( ph <-> ps ) ) /\ E. x th )
                                           -> ( A. x ( th -> ph ) <-> ps ) ) $=
    ( wnf wb wi wal wex w3a simp3 imim3i al2imi 3ad2ant2 19.23t 3ad2ant1 sylibd
    biimp mpid biimpr imim2i com23 alimi 19.21t mpbid impbid ) BDEZCABFZGZDHZCD
    IZJZCAGZDHZBULUNUKBUGUJUKKULUNCBGZDHZUKBGZUJUGUNUPGUKUIUMUODUHABCABRLMNUGUJ
    UPUQFUKCBDOPQSULBUMGZDHZBUNGZUJUGUSUKUIURDUICBAUHBAGCABTUAUBUCNUGUJUSUTFUKB
    UMDUDPUEUF $.

  ${
    bj-ceqsalt1.1 $e |- ( th -> E. x ch ) $.
    $( The FOL content of ~ ceqsalt .  Lemma for ~ bj-ceqsalt and
       ~ bj-ceqsaltv .  TODO: consider removing if it does not add anything to
       ~ bj-ceqsalt0 .  (Contributed by BJ, 26-Sep-2019.)
       (Proof modification is discouraged.) $)
    bj-ceqsalt1 $p |- ( ( F/ x ps /\ A. x ( ch -> ( ph <-> ps ) ) /\ th )
                                           -> ( A. x ( ch -> ph ) <-> ps ) ) $=
      ( wnf wb wi wal w3a 3ad2ant3 biimp imim3i al2imi 3ad2ant2 19.23t 3ad2ant1
      wex sylibd mpid biimpr imim2i com23 alimi 19.21t mpbid impbid ) BEGZCABHZ
      IZEJZDKZCAIZEJZBUMUOCESZBDUIUPULFLUMUOCBIZEJZUPBIZULUIUOURIDUKUNUQEUJABCA
      BMNOPUIULURUSHDCBEQRTUAUMBUNIZEJZBUOIZULUIVADUKUTEUKCBAUJBAICABUBUCUDUEPU
      IULVAVBHDBUNEUFRUGUH $.
  $}

  ${
    $d x A $.
    $( Remove from ~ ceqsalt dependency on ~ ax-ext (and on ~ df-cleq and
       ~ df-v ).  Note: this is not doable with ~ ceqsralt (or ~ ceqsralv ),
       which uses ~ eleq1 , but the same dependence removal is possible for
       ~ ceqsalg , ~ ceqsal , ~ ceqsalv , ~ cgsexg , ~ cgsex2g , ~ cgsex4g ,
       ~ ceqsex , ~ ceqsexv , ~ ceqsex2 , ~ ceqsex2v , ~ ceqsex3v ,
       ~ ceqsex4v , ~ ceqsex6v , ~ ceqsex8v , ~ gencbvex (after changing
       ` A = y ` to ` y = A ` ), ~ gencbvex2 , ~ gencbval , ~ vtoclgft (it uses
       ` F/_ ` , whose justification ~ nfcjust does not use ~ ax-ext ) and
       several other vtocl* theorems (see for instance ~ bj-vtoclg1f ).  See
       also ~ bj-ceqsaltv .  (Contributed by BJ, 16-Jun-2019.)
       (Proof modification is discouraged.) $)
    bj-ceqsalt $p |- ( ( F/ x ps /\ A. x ( x = A -> ( ph <-> ps ) ) /\ A e. V )
                                        -> ( A. x ( x = A -> ph ) <-> ps ) ) $=
      ( wnf cv wceq wb wi wal wcel w3a wex elisset 3anim3i bj-ceqsalt0 syl ) BC
      FZCGDHZABIJCKZDELZMSUATCNZMTAJCKBIUBUCSUACDEOPABTCQR $.
  $}

  ${
    $d x A $.  $d x V $.
    $( Version of ~ bj-ceqsalt with a disjoint variable condition on
       ` x , V ` , removing dependency on ~ df-sb and ~ df-clab .  Prefer its
       use over ~ bj-ceqsalt when sufficient (in particular when ` V ` is
       substituted for ` _V ` ).  (Contributed by BJ, 16-Jun-2019.)
       (Proof modification is discouraged.) $)
    bj-ceqsaltv $p |-
                ( ( F/ x ps /\ A. x ( x = A -> ( ph <-> ps ) ) /\ A e. V )
                                        -> ( A. x ( x = A -> ph ) <-> ps ) ) $=
      ( wnf cv wceq wb wi wal wcel w3a wex elissetv 3anim3i bj-ceqsalt0 syl ) B
      CFZCGDHZABIJCKZDELZMSUATCNZMTAJCKBIUBUCSUACDEOPABTCQR $.
  $}

  ${
    bj-ceqsalg0.1 $e |- F/ x ps $.
    bj-ceqsalg0.2 $e |- ( ch -> ( ph <-> ps ) ) $.
    $( The FOL content of ~ ceqsalg .  (Contributed by BJ, 12-Oct-2019.)
       (Proof modification is discouraged.) $)
    bj-ceqsalg0 $p |- ( E. x ch -> ( A. x ( ch -> ph ) <-> ps ) ) $=
      ( wnf wb wi wal wex ax-gen bj-ceqsalt0 mp3an12 ) BDGCABHIZDJCDKCAIDJBHEOD
      FLABCDMN $.
  $}

  ${
    $d x A $.
    bj-ceqsalg.1 $e |- F/ x ps $.
    bj-ceqsalg.2 $e |- ( x = A -> ( ph <-> ps ) ) $.
    $( Remove from ~ ceqsalg dependency on ~ ax-ext (and on ~ df-cleq and
       ~ df-v ).  See also ~ bj-ceqsalgv .  (Contributed by BJ, 12-Oct-2019.)
       (Proof modification is discouraged.) $)
    bj-ceqsalg $p |- ( A e. V -> ( A. x ( x = A -> ph ) <-> ps ) ) $=
      ( wcel cv wceq wex wi wal wb elisset bj-ceqsalg0 syl ) DEHCIDJZCKRALCMBNC
      DEOABRCFGPQ $.

    $( Alternate proof of ~ bj-ceqsalg .  (Contributed by BJ, 12-Oct-2019.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    bj-ceqsalgALT $p |- ( A e. V -> ( A. x ( x = A -> ph ) <-> ps ) ) $=
      ( wnf cv wceq wb wi wal wcel ax-gen bj-ceqsalt mp3an12 ) BCHCIDJZABKLZCMD
      ENRALCMBKFSCGOABCDEPQ $.
  $}

  ${
    $d x A $.  $d x V $.
    bj-ceqsalgv.1 $e |- F/ x ps $.
    bj-ceqsalgv.2 $e |- ( x = A -> ( ph <-> ps ) ) $.
    $( Version of ~ bj-ceqsalg with a disjoint variable condition on
       ` x , V ` , removing dependency on ~ df-sb and ~ df-clab .  Prefer its
       use over ~ bj-ceqsalg when sufficient (in particular when ` V ` is
       substituted for ` _V ` ).  (Contributed by BJ, 12-Oct-2019.)
       (Proof modification is discouraged.) $)
    bj-ceqsalgv $p |- ( A e. V -> ( A. x ( x = A -> ph ) <-> ps ) ) $=
      ( wcel cv wceq wex wi wal wb elissetv bj-ceqsalg0 syl ) DEHCIDJZCKRALCMBN
      CDEOABRCFGPQ $.

    $( Alternate proof of ~ bj-ceqsalgv .  (Contributed by BJ, 12-Oct-2019.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    bj-ceqsalgvALT $p |- ( A e. V -> ( A. x ( x = A -> ph ) <-> ps ) ) $=
      ( wnf cv wceq wb wi wal wcel ax-gen bj-ceqsaltv mp3an12 ) BCHCIDJZABKLZCM
      DENRALCMBKFSCGOABCDEPQ $.
  $}

  ${
    $d x A $.
    bj-ceqsal.1 $e |- F/ x ps $.
    bj-ceqsal.2 $e |- A e. _V $.
    bj-ceqsal.3 $e |- ( x = A -> ( ph <-> ps ) ) $.
    $( Remove from ~ ceqsal dependency on ~ ax-ext (and on ~ df-cleq , ~ df-v ,
       ~ df-clab , ~ df-sb ).  (Contributed by BJ, 12-Oct-2019.)
       (Proof modification is discouraged.) $)
    bj-ceqsal $p |- ( A. x ( x = A -> ph ) <-> ps ) $=
      ( cvv wcel cv wceq wi wal wb bj-ceqsalgv ax-mp ) DHICJDKALCMBNFABCDHEGOP
      $.
  $}

  ${
    $d x A $.  $d x ps $.
    bj-ceqsalv.1 $e |- A e. _V $.
    bj-ceqsalv.2 $e |- ( x = A -> ( ph <-> ps ) ) $.
    $( Remove from ~ ceqsalv dependency on ~ ax-ext (and on ~ df-cleq ,
       ~ df-v , ~ df-clab , ~ df-sb ).  (Contributed by BJ, 12-Oct-2019.)
       (Proof modification is discouraged.) $)
    bj-ceqsalv $p |- ( A. x ( x = A -> ph ) <-> ps ) $=
      ( nfv bj-ceqsal ) ABCDBCGEFH $.
  $}

  ${
    $d x A $.  $d x ph $.  $d x ch $.
    bj-spcimdv.1 $e |- ( ph -> A e. B ) $.
    bj-spcimdv.2 $e |- ( ( ph /\ x = A ) -> ( ps -> ch ) ) $.
    $( Remove from ~ spcimdv dependency on ~ ax-9 , ~ ax-10 , ~ ax-11 ,
       ~ ax-13 , ~ ax-ext , ~ df-cleq (and ~ df-nfc , ~ df-v , ~ df-or ,
       ~ df-tru , ~ df-nf ).  For an even more economical version, see
       ~ bj-spcimdvv .  (Contributed by BJ, 30-Nov-2020.)
       (Proof modification is discouraged.) $)
    bj-spcimdv $p |- ( ph -> ( A. x ps -> ch ) ) $=
      ( cv wceq wi wal wcel ex alrimiv wex elisset exim syl5 19.36v imbitrdi
      sylc ) ADIEJZBCKZKZDLZEFMZBDLCKZAUEDAUCUDHNOGUFUGUDDPZUHUGUCDPUFUIDEFQUCU
      DDRSBCDTUAUB $.
  $}

  ${
    $d x A $.  $d x B $.  $d x ph $.  $d x ch $.
    bj-spcimdvv.1 $e |- ( ph -> A e. B ) $.
    bj-spcimdvv.2 $e |- ( ( ph /\ x = A ) -> ( ps -> ch ) ) $.
    $( Remove from ~ spcimdv dependency on ~ ax-7 , ~ ax-8 , ~ ax-10 ,
       ~ ax-11 , ~ ax-12 ~ ax-13 , ~ ax-ext , ~ df-cleq , ~ df-clab (and
       ~ df-nfc , ~ df-v , ~ df-or , ~ df-tru , ~ df-nf ) at the price of
       adding a disjoint variable condition on ` x , B ` (but in usages, ` x `
       is typically a dummy, hence fresh, variable).  For the version without
       this disjoint variable condition, see ~ bj-spcimdv .  (Contributed by
       BJ, 3-Nov-2021.)  (Proof modification is discouraged.) $)
    bj-spcimdvv $p |- ( ph -> ( A. x ps -> ch ) ) $=
      ( cv wceq wi wal wcel ex alrimiv wex elissetv exim syl5 19.36v imbitrdi
      sylc ) ADIEJZBCKZKZDLZEFMZBDLCKZAUEDAUCUDHNOGUFUGUDDPZUHUGUCDPUFUIDEFQUCU
      DDRSBCDTUAUB $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Characterization among sets versus among classes
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( Equivalence between two common ways to characterize elements of a class
     ` B ` : the LHS says that sets are elements of ` B ` if and only if they
     satisfy ` ph ` while the RHS says that classes are elements of ` B ` if
     and only if they are sets and satisfy ` ph ` .  Therefore, the LHS is a
     characterization among sets while the RHS is a characterization among
     classes.  Note that the LHS is often formulated using a class variable
     instead of the universe ` _V ` while this is not possible for the RHS
     (apart from using ` B ` itself, which would not be very useful).
     (Contributed by BJ, 26-Feb-2023.) $)
  elelb $p |- ( ( A e. _V -> ( A e. B <-> ph ) ) <->
                ( A e. B <-> ( A e. _V /\ ph ) ) ) $=
    ( wcel cvv elex biadani ) BCDBEDABCFG $.

  $( Characterization of the elements of the powerclass of the cartesian square
     of the universal class: they are exactly the sets which are binary
     relations.  (Contributed by BJ, 16-Dec-2023.) $)
  bj-pwvrelb $p |- ( A e. ~P ( _V X. _V ) <-> ( A e. _V /\ Rel A ) ) $=
    ( cvv cxp cpw wcel wrel elex pwvrel biadanii ) ABBCDZEABEAFAJGABHI $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  The nonfreeness quantifier for classes
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  In this section, we prove the symmetry of the nonfreeness quantifier for
  classes.

$)

  $( The nonfreeness quantifier for classes defines a symmetric binary relation
     on var metavariables (irreflexivity is proved by ~ nfnid with additional
     axioms; see also ~ nfcv ).  This could be proved from ~ aecom and ~ nfcvb
     but the latter requires a domain with at least two objects (hence uses
     extra axioms).  (Contributed by BJ, 30-Sep-2018.)  Proof modification is
     discouraged to avoid use of ~ eqcomd instead of ~ equcomd ; removing
     dependency on ~ ax-ext is possible: prove weak versions (i.e. replace
     classes with setvars) of ~ drnfc1 , ~ eleq2d (using ~ elequ2 ), ~ nfcvf ,
     ~ dvelimc , ~ dvelimdc , ~ nfcvf2 .
     (Proof modification is discouraged.) $)
  bj-nfcsym $p |- ( F/_ x y <-> F/_ y x ) $=
    ( weq wal cv wnfc wb sp equcomd drnfc1 wn nfcvf nfcvf2 2thd pm2.61i ) ABCZA
    DZABEZFZBAEZFZGABRTQABPAHIJQKSUAABLABMNO $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Lemmas for class substitution
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  Some useful theorems for dealing with substitutions: ~ sbbi , ~ sbcbig ,
  ~ sbcel1g , ~ sbcel2 , ~ sbcel12 , ~ sbceqg , ~ csbvarg .

$)

  ${
    $d x y $.
    $( Substitution in an equality (use the more general version ~ bj-sbeq
       instead, without disjoint variable condition).  (Contributed by BJ,
       6-Oct-2018.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    bj-sbeqALT $p |- ( [ y / x ] A = B <-> [_ y / x ]_ A = [_ y / x ]_ B ) $=
      ( wceq cv csb nfcsb1v nfeq weq csbeq1a eqeq12d sbiev ) CDEABFZCGZANDGZEAB
      AOPANCHANDHIABJCODPANCKANDKLM $.
  $}

  ${
    $d z x $.  $d z y $.  $d z A $.  $d z B $.
    $( Distribute proper substitution through an equality relation.  (See
       ~ sbceqg ).  (Contributed by BJ, 6-Oct-2018.) $)
    bj-sbeq $p |- ( [ y / x ] A = B <-> [_ y / x ]_ A = [_ y / x ]_ B ) $=
      ( vz wceq wsb cv csb wcel wal wsbc dfcleq sbbii sbsbc sbcal 3bitri sbcel2
      wb albii cvv sbcbig elv bibi12i bitr4i ) CDFZABGZEHZABHZCIZJZUHAUIDIZJZSZ
      EKZUJULFUGUHCJZUHDJZSZAUILZEKZUPAUILZUQAUILZSZEKUOUGUREKZABGVDAUILUTUFVDA
      BECDMNVDABOUREAUIPQUSVCEUSVCSBUPUQAUIUAUBUCTVCUNEVAUKVBUMAUIUHCRAUIUHDRUD
      TQEUJULMUE $.
  $}

  ${
    $d y A $.  $d y B $.  $d y C $.  $d y x $.  $d y V $.
    $( Distribute proper substitution through an equality relation.  Alternate
       proof of ~ sbceqg .  (Contributed by BJ, 6-Oct-2018.)  Proof
       modification is discouraged to avoid using ~ sbceqg , but the Metamath
       program "MM-PA> MINIMIZE__WITH * / EXCEPT sbceqg" command is ok.
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    bj-sbceqgALT $p |- ( A e. V -> ( [. A / x ]. B = C <->
      [_ A / x ]_ B = [_ A / x ]_ C ) ) $=
      ( vy wcel wceq wsbc cv csb wb wal dfcleq sbcth sbcbig mpbid albidv sbcel2
      a1i sbcal bitrdi bibi12d 3bitrd bitr4di ) BEGZCDHZABIZFJZABCKZGZUIABDKZGZ
      LZFMZUJULHUFUHUICGZUIDGZLZABIZFMZUPABIZUQABIZLZFMUOUFUHURFMZABIZUTUFUGVDL
      ZABIUHVELVFABEFCDNOUGVDABEPQURFABUAUBUFUSVCFUPUQABEPRUFVCUNFUFVAUKVBUMVAU
      KLUFABUICSTVBUMLUFABUIDSTUCRUDFUJULNUE $.
  $}

  ${
    $d y x A $.
    $( Lemma for ~ bj-csbsn (in this lemma, ` x ` cannot occur in ` A ` ).
       (Contributed by BJ, 6-Oct-2018.)  (New usage is discouraged.) $)
    bj-csbsnlem $p |- [_ A / x ]_ { x } = { A } $=
      ( vy cv csn csb wcel wsbc cab wceq abid df-sbc wex weq clelab velsn exbii
      wa cvv 3bitri anbi2i eqeq2 pm5.32i 19.41v simpr eqvisset syl ancri impbii
      elisset df-csb eleq2i 3bitr4i eqriv ) CABADZEZFZBEZCDZUSUPGZABHZCIZGZUSBJ
      ZUSUQGUSURGVCVABUTAIGZVDVACKUTABLVEUOBJZUTRZAMVFCANZRZAMZVDUTABOVGVIAUTVH
      VFCUOPUAQVJVFVDRZAMVFAMZVDRZVDVIVKAVFVHVDUOBUSUBUCQVFVDAUDVMVDVLVDUEVDVLV
      DBSGVLCBUFABSUJUGUHUITTTUQVBUSACBUPUKULCBPUMUN $.
  $}

  ${
    $d y x $.  $d y A $.
    $( Substitution in a singleton.  (Contributed by BJ, 6-Oct-2018.) $)
    bj-csbsn $p |- [_ A / x ]_ { x } = { A } $=
      ( vy cv csn csb bj-csbsnlem csbeq2i csbcow 3eqtr3i ) CBACDZADEZFZFCBKEZFA
      BLFBECBMNAKGHACBLICBGJ $.
  $}

  ${
    $d x B $.
    $( Version of ~ sbcel1g when substituting a set.  (Note: one could have a
       corresponding version of ~ sbcel12 when substituting a set, but the
       point here is that the antecedent of ~ sbcel1g is not needed when
       substituting a set.)  (Contributed by BJ, 6-Oct-2018.) $)
    bj-sbel1 $p |- ( [ y / x ] A e. B <-> [_ y / x ]_ A e. B ) $=
      ( wcel wsb cv wsbc csb sbsbc wb cvv sbcel1g elv bitri ) CDEZABFPABGZHZAQC
      IDEZPABJRSKBAQCDLMNO $.
  $}

  $( The class of sets verifying a tautology is the universal class.
     (Contributed by BJ, 24-Jul-2019.)  (Proof modification is discouraged.) $)
  bj-abv $p |- ( A. x ph -> { x | ph } = _V ) $=
    ( wal cab wtru cvv wb wceq trud simpl impbida alimi abbi syl dfv2 eqtr4di
    wa ) ABCZABDZEBDZFRAEGZBCSTHAUABAAEAAQIAEJKLAEBMNBOP $.

  ${
    $d y x $.  $d y ph $.
    $( Alternate version of ~ bj-abv ; shorter but uses ~ ax-8 .  (Contributed
       by BJ, 24-Jul-2019.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    bj-abvALT $p |- ( A. x ph -> { x | ph } = _V ) $=
      ( vy wal cv cab wcel cvv wceq ax-5 vexwt alrimih eqv sylibr ) ABDZCEABFZG
      ZCDPHIOQCOCJABCKLCPMN $.
  $}

  ${
    $d y x $.  $d y ph $.
    $( The class of sets verifying a falsity is the empty set (closed form of
       ~ abf ).  (Contributed by BJ, 24-Jul-2019.)
       (Proof modification is discouraged.) $)
    bj-ab0 $p |- ( A. x -. ph -> { x | ph } = (/) ) $=
      ( vy wn wal cab wsb cv wcel stdpc4 sbn1 syl df-clab sylnibr eq0rdv ) ADZB
      EZCABFZQABCGZCHRIQPBCGSDPBCJABCKLACBMNO $.
  $}

  ${
    bj-abf.1 $e |- -. ph $.
    $( Shorter proof of ~ abf (which should be kept as abfALT).  (Contributed
       by BJ, 24-Jul-2019.)  (Proof modification is discouraged.) $)
    bj-abf $p |- { x | ph } = (/) $=
      ( wn cab c0 wceq bj-ab0 mpg ) ADABEFGBABHCI $.
  $}

  ${
    $d y x $.  $d y A $.  $d y B $.
    $( More direct proof of ~ csbprc (fewer essential steps).  (Contributed by
       BJ, 24-Jul-2019.)  (Proof modification is discouraged.) $)
    bj-csbprc $p |- ( -. A e. _V -> [_ A / x ]_ B = (/) ) $=
      ( vy cvv wcel wn csb cv wsbc cab c0 df-csb wal sbcex con3i alrimiv bj-ab0
      wceq syl eqtrid ) BEFZGZABCHDICFZABJZDKZLADBCMUCUEGZDNUFLSUCUGDUEUBUDABOP
      QUEDRTUA $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Removing some axiom requirements and disjoint variable conditions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d ps x $.
    bj-exlimvmpi.maj $e |- ( ch -> ( ph -> ps ) ) $.
    bj-exlimvmpi.min $e |- ph $.
    $( A Fol lemma ( ~ exlimiv followed by ~ mpi ).  (Contributed by BJ,
       2-Jul-2022.)  (Proof modification is discouraged.) $)
    bj-exlimvmpi $p |- ( E. x ch -> ps ) $=
      ( mpi exlimiv ) CBDCABFEGH $.
  $}

  ${
    bj-exlimmpi.nf $e |- F/ x ps $.
    bj-exlimmpi.maj $e |- ( ch -> ( ph -> ps ) ) $.
    bj-exlimmpi.min $e |- ph $.
    $( Lemma for ~ bj-vtoclg1f1 (an instance of this lemma is a version of
       ~ bj-vtoclg1f1 where ` x ` and ` y ` are identified).  (Contributed by
       BJ, 30-Apr-2019.)  (Proof modification is discouraged.) $)
    bj-exlimmpi $p |- ( E. x ch -> ps ) $=
      ( mpi exlimi ) CBDECABGFHI $.
  $}

  ${
    bj-exlimmpbi.nf $e |- F/ x ps $.
    bj-exlimmpbi.maj $e |- ( ch -> ( ph <-> ps ) ) $.
    bj-exlimmpbi.min $e |- ph $.
    $( Lemma for theorems of the ~ vtoclg family.  (Contributed by BJ,
       3-Oct-2019.)  (Proof modification is discouraged.) $)
    bj-exlimmpbi $p |- ( E. x ch -> ps ) $=
      ( mpbii exlimi ) CBDECABGFHI $.
  $}

  ${
    bj-exlimmpbir.nf $e |- F/ x ph $.
    bj-exlimmpbir.maj $e |- ( ch -> ( ph <-> ps ) ) $.
    bj-exlimmpbir.min $e |- ps $.
    $( Lemma for theorems of the ~ vtoclg family.  (Contributed by BJ,
       3-Oct-2019.)  (Proof modification is discouraged.) $)
    bj-exlimmpbir $p |- ( E. x ch -> ph ) $=
      ( mpbiri exlimi ) CADECABGFHI $.
  $}

  ${
    $d x A $.  $d x V $.
    bj-vtoclf.nf $e |- F/ x ps $.
    bj-vtoclf.s $e |- A e. V $.
    bj-vtoclf.maj $e |- ( x = A -> ( ph <-> ps ) ) $.
    bj-vtoclf.min $e |- ph $.
    $( Remove dependency on ~ ax-ext , ~ df-clab and ~ df-cleq (and ~ df-sb and
       ~ df-v ) from ~ vtoclf .  (Contributed by BJ, 6-Oct-2019.)
       (Proof modification is discouraged.) $)
    bj-vtoclf $p |- ps $=
      ( cv wceq wi bj-issetiv biimpd eximii 19.36i mpg ) ABCABCFCJDKZABLCCDEGMR
      ABHNOPIQ $.
  $}

  ${
    $d x A $.  $d x ps $.  $d x V $.
    bj-vtocl.s $e |- A e. V $.
    bj-vtocl.maj $e |- ( x = A -> ( ph <-> ps ) ) $.
    bj-vtocl.min $e |- ph $.
    $( Remove dependency on ~ ax-ext , ~ df-clab and ~ df-cleq (and ~ df-sb and
       ~ df-v ) from ~ vtocl .  (Contributed by BJ, 6-Oct-2019.)
       (Proof modification is discouraged.) $)
    bj-vtocl $p |- ps $=
      ( nfv bj-vtoclf ) ABCDEBCIFGHJ $.
  $}

  ${
    $d x A $.  $d y A $.
    bj-vtoclg1f1.nf $e |- F/ x ps $.
    bj-vtoclg1f1.maj $e |- ( x = A -> ( ph -> ps ) ) $.
    bj-vtoclg1f1.min $e |- ph $.
    $( The FOL content of ~ vtoclg1f (hence not using ~ ax-ext , ~ df-cleq ,
       ~ df-nfc , ~ df-v ).  Note the weakened "major" hypothesis and the
       disjoint variable condition between ` x ` and ` A ` (needed since the
       nonfreeness quantifier for classes is not available without ~ ax-ext ;
       as a byproduct, this dispenses with ~ ax-11 and ~ ax-13 ).  (Contributed
       by BJ, 30-Apr-2019.)  (Proof modification is discouraged.) $)
    bj-vtoclg1f1 $p |- ( E. y y = A -> ps ) $=
      ( cv wceq wex iseqsetv-clel bj-exlimmpi sylbi ) DIEJDKCIEJZCKBDCELABOCFGH
      MN $.
  $}

  ${
    $d x A $.
    bj-vtoclg1f.nf $e |- F/ x ps $.
    bj-vtoclg1f.maj $e |- ( x = A -> ( ph -> ps ) ) $.
    bj-vtoclg1f.min $e |- ph $.
    $( Reprove ~ vtoclg1f from ~ bj-vtoclg1f1 .  This removes dependency on
       ~ ax-ext , ~ df-cleq and ~ df-v .  Use ~ bj-vtoclg1fv instead when
       sufficient (in particular when ` V ` is substituted for ` _V ` ).
       (Contributed by BJ, 14-Sep-2019.)
       (Proof modification is discouraged.) $)
    bj-vtoclg1f $p |- ( A e. V -> ps ) $=
      ( wcel cv wceq wex elisset bj-exlimmpi syl ) DEICJDKZCLBCDEMABPCFGHNO $.
  $}

  ${
    $d x A $.  $d x V $.
    bj-vtoclg1fv.nf $e |- F/ x ps $.
    bj-vtoclg1fv.maj $e |- ( x = A -> ( ph -> ps ) ) $.
    bj-vtoclg1fv.min $e |- ph $.
    $( Version of ~ bj-vtoclg1f with a disjoint variable condition on
       ` x , V ` .  This removes dependency on ~ df-sb and ~ df-clab .  Prefer
       its use over ~ bj-vtoclg1f when sufficient (in particular when ` V ` is
       substituted for ` _V ` ).  (Contributed by BJ, 14-Sep-2019.)
       (Proof modification is discouraged.) $)
    bj-vtoclg1fv $p |- ( A e. V -> ps ) $=
      ( wcel cv wceq wex elissetv bj-exlimmpi syl ) DEICJDKZCLBCDEMABPCFGHNO $.
  $}

  ${
    $d x A $.  $d x V $.  $d ps x $.
    bj-vtoclg.maj $e |- ( x = A -> ( ph -> ps ) ) $.
    bj-vtoclg.min $e |- ph $.
    $( A version of ~ vtoclg with an additional disjoint variable condition
       (which is removable if we allow use of ~ df-clab , see ~ bj-vtoclg1f ),
       which requires fewer axioms (i.e., removes dependency on ~ ax-6 ,
       ~ ax-7 , ~ ax-9 , ~ ax-12 , ~ ax-ext , ~ df-clab , ~ df-cleq , ~ df-v ).
       (Contributed by BJ, 2-Jul-2022.)
       (Proof modification is discouraged.) $)
    bj-vtoclg $p |- ( A e. V -> ps ) $=
      ( wcel cv wceq wex elissetv bj-exlimvmpi syl ) DEHCIDJZCKBCDELABOCFGMN $.
  $}

  ${
    bj-rabeqbid.nf $e |- F/ x ph $.
    bj-rabeqbid.1 $e |- ( ph -> A = B ) $.
    bj-rabeqbid.2 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Version of ~ rabeqbidv with two disjoint variable conditions removed and
       the third replaced by a nonfreeness hypothesis.  (Contributed by BJ,
       27-Apr-2019.) $)
    bj-rabeqbid $p |- ( ph -> { x e. A | ps } = { x e. B | ch } ) $=
      ( crab rabeqd rabbid eqtrd ) ABDEJBDFJCDFJABDEFGHKABCDFGILM $.
  $}

  ${
    $d x y A $.  $d y B $.  $d x y R $.
    bj-seex.nf $e |- F/_ x B $.
    $( Version of ~ seex with a disjoint variable condition replaced by a
       nonfreeness hypothesis (for the sake of illustration).  (Contributed by
       BJ, 27-Apr-2019.) $)
    bj-seex $p |- ( ( R Se A /\ B e. A ) -> { x e. A | x R B } e. _V ) $=
      ( vy wse cv wbr crab cvv wcel wral df-se wceq nfeq2 rabbid eleq1d rspccva
      breq2 sylanb ) BDGAHZFHZDIZABJZKLZFBMCBLUBCDIZABJZKLZFABDNUFUIFCBUCCOZUEU
      HKUJUDUGABAUCCEPUCCUBDTQRSUA $.
  $}

  ${
    $d x y z $.  $d A z $.
    bj-nfcf.nf $e |- F/_ y A $.
    $( Version of ~ df-nfc with a disjoint variable condition replaced with a
       nonfreeness hypothesis.  (Contributed by BJ, 2-May-2019.) $)
    bj-nfcf $p |- ( F/_ x A <-> A. y F/ x y e. A ) $=
      ( vz wnfc cv wcel wnf wal df-nfc nfcri nfnf sb8f sbnf clelsb1 nfbii bitri
      wsb albii ) ACFEGCHZAIZEJZBGCHZAIZBJZAECKUCUBEBSZBJUFUBEBUABABECDLMNUGUEB
      UGUAEBSZAIUEUAAEBOUHUDAEBCPQRTRR $.
  $}

  ${
    $d A x y z $.  $d ph y z $.  $d V z $.
    $( Version of ~ sepg which does not require ~ df-clab , thanks to the use
       of ~ bj-vtoclg (and ultimately, to the use of ~ elissetv instead of
       ~ elisset ).  This axiom save is not very important, since this theorem
       uses ~ df-cleq and ~ df-clel .  This theorem is a remnant of a previous
       state of set.mm where the axiom saving was larger.  (Contributed by BJ,
       2-Jul-2022.)  (Proof modification is discouraged.) $)
    bj-sepg $p |- ( A e. V -> E. y A. x ( x e. y <-> ( x e. A /\ ph ) ) ) $=
      ( vz wel wa wb wal wex wcel wceq eleq2 anbi1d bibi2d biimpd alimdv eximdv
      cv ax-sep bj-vtoclg ) BCGZBFGZAHZIZBJZCKUCBTZDLZAHZIZBJZCKFDEFTZDMZUGULCU
      NUFUKBUNUFUKUNUEUJUCUNUDUIAUMDUHNOPQRSABCFUAUB $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d V x y $.
    $( Proof of ~ inex1g from ~ sepg to then allow proving ~ inex1 from it.
       That does not reduce the combined proof size of ~ inex1 and ~ inex1g .
       (Contributed by BJ, 14-Jul-2026.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    bj-inex1gALT $p |- ( A e. V -> ( A i^i B ) e. _V ) $=
      ( vx vy wcel cv cin wceq wex cvv wel wa wal sepg dfcleq elin a1i bibi2d
      wb albidv bitrid exbidv mpbird isset sylibr ) ACFZDGZABHZIZDJZUIKFUGUKEDL
      ZEGZAFUMBFZMZTZENZDJUNEDACOUGUJUQDUJULUMUIFZTZENUGUQEUHUIPUGUSUPEUGURUOUL
      URUOTUGUMABQRSUAUBUCUDDUIUEUF $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Class abstractions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  A few additional theorems on class abstractions and restricted class
  abstractions.

$)

  ${
    $d x y ph $.  $d x y ch $.  $d x y A $.  $d B y $.
    bj-elabd2ALT.ex $e |- ( ph -> A e. V ) $.
    bj-elabd2ALT.eq $e |- ( ph -> B = { x | ps } ) $.
    bj-elabd2ALT.is $e |- ( ( ph /\ x = A ) -> ( ps <-> ch ) ) $.
    $( Alternate proof of ~ elabd2 bypassing ~ elab6g (and using ~ sbiedvw
       instead of the ` A. x ( x = y -> ps ) ` idiom).  (Contributed by BJ,
       16-Oct-2024.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    bj-elabd2ALT $p |- ( ph -> ( A e. B <-> ch ) ) $=
      ( vy cv cab wcel wsb wb wceq wa simpr eqcomd adantr eqeq1 biimparc anim2i
      eleq12d weq anassrs syl sbiedvw bibi12d df-clab a1i vtocld ) AKLZBDMZNZBD
      KOZPZEFNZCPKEGHAUNEQZRZUPUSUQCVAUNEUOFAUTSAUOFQUTAFUOITUAUEVABCDKVADKUFZR
      ADLZEQZRZBCPAUTVBVEUTVBRVDAVBVDUTVCUNEUBUCUDUGJUHUIUJURABKDUKULUM $.
  $}

  ${
    $d x A $.  $d x B $.
    $( Generalization of ~ unrab .  Equality need not hold.  (Contributed by
       BJ, 21-Apr-2019.) $)
    bj-unrab $p |- ( { x e. A | ph } u. { x e. B | ps } ) C_
                 { x e. ( A u. B ) | ( ph \/ ps ) } $=
      ( crab wo cun wss ssun1 rabss2 ax-mp wi wcel orc a1i ss2rabi sstri ssun2
      cv olc unssi ) ACDFZBCEFZABGZCDEHZFZUCACUFFZUGDUFIUCUHIDEJACDUFKLAUECUFAU
      EMCTUFNZABOPQRUDBCUFFZUGEUFIUDUJIEDSBCEUFKLBUECUFBUEMUIBAUAPQRUB $.
  $}

  $( Generalization of ~ inrab .  (Contributed by BJ, 21-Apr-2019.) $)
  bj-inrab $p |- ( { x e. A | ph } i^i { x e. B | ps } ) =
                 { x e. ( A i^i B ) | ( ph /\ ps ) } $=
    ( cv wcel wa cab cin crab an4 elin anbi1i bitr4i abbii df-rab ineq12i eqtri
    inab 3eqtr4i ) CFZDGZAHZUBEGZBHZHZCIZUBDEJZGZABHZHZCIACDKZBCEKZJZUKCUIKUGUL
    CUGUCUEHZUKHULUCAUEBLUJUPUKUBDEMNOPUOUDCIZUFCIZJUHUMUQUNURACDQBCEQRUDUFCTSU
    KCUIQUA $.

  $( Shorter proof of ~ inrab .  (Contributed by BJ, 21-Apr-2019.)
     (Proof modification is discouraged.) $)
  bj-inrab2 $p |- ( { x e. A | ph } i^i { x e. A | ps } ) =
                                                   { x e. A | ( ph /\ ps ) } $=
    ( crab cin wa bj-inrab wceq wtru nfv inidm a1i rabeqd mptru eqtri ) ACDEBCD
    EFABGZCDDFZEZQCDEZABCDDHSTIJQCRDJCKRDIJDLMNOP $.

  ${
    $d A x $.  $d B x $.
    $( Generalization of ~ dfrab3ss .  Shortens ~ dfrab3ss .  (Contributed by
       BJ, 21-Apr-2019.)  (Revised by OpenAI, 7-Jul-2020.) $)
    bj-inrab3 $p |- ( A i^i { x e. B | ph } ) = ( { x e. A | ph } i^i B ) $=
      ( crab cin cab dfrab3 ineq2i incom in12 3eqtr4i eqtr4i ) CABDEZFCDABGZFZF
      ZABCEZDFZNPCABDHIDRFDCOFZFSQRTDABCHIRDJCDOKLM $.
  $}

  ${
    $d x A $.
    $( Restricted class abstraction with true formula.  (Contributed by BJ,
       22-Apr-2019.) $)
    bj-rabtr $p |- { x e. A | T. } = A $=
      ( wtru crab ssrab2 wss wral ssid tru rgenw ssrab mpbir2an eqssi ) CABDZBC
      ABEBNFBBFCABGBHCABIJCABBKLM $.

    $( Alternate proof of ~ bj-rabtr .  (Contributed by BJ, 22-Apr-2019.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    bj-rabtrALT $p |- { x e. A | T. } = A $=
      ( wtru crab wceq cv wcel wb nfrab1 nfcv cleqf tru rabid mpbiran2 mpgbir )
      CABDZBEAFZPGZQBGZHAAPBCABIABJKRSCLCABMNO $.

    $( Proof of ~ bj-rabtr found automatically by the Metamath program "MM-PA>
       IMPROVE ALL / DEPTH 3 / 3" command followed by "MM-PA> MINIMIZE__WITH
       *".  (Contributed by BJ, 22-Apr-2019.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    bj-rabtrAUTO $p |- { x e. A | T. } = A $=
      ( wtru crab ssrab2 wss ssid a1i cv wcel simpl ssrabdv mptru eqssi ) CABDZ
      BCABEBOFCCABBBBFCBGHCAIBJKLMN $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Generalized class abstractions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( Braces for generalized class abstractions.  Needed to ease parsing. $)
  $c {{ }} $.

  $( Syntax for generalized class abstractions. $)
  bj-cgab $a class {{ A | x | ph }} $.

  ${
    $d x y $.  $d A y $.  $d ph y $.
    $( Definition of generalized class abstractions: typically, ` x ` is a
       bound variable in ` A ` and ` ph ` and ` { A | x | ph } ` denotes "the
       class of ` A ( x ) ` 's such that ` ph ( x ) ` ".  (Contributed by BJ,
       4-Oct-2024.) $)
    df-bj-gab $a |- {{ A | x | ph }} = { y | E. x ( A = y /\ ph ) } $.
  $}

  ${
    $d x y $.  $d ph y $.  $d ps y $.  $d A y $.  $d B y $.
    $( Inclusion of generalized class abstractions.  (Contributed by BJ,
       4-Oct-2024.) $)
    bj-gabss $p |- ( A. x ( A = B /\ ( ph -> ps ) ) ->
                                      {{ A | x | ph }} C_ {{ B | x | ps }} ) $=
      ( vy wi wa wal cv wex cab bj-cgab wss eqeq1 biimpd adantr simpr df-bj-gab
      wceq anim12d aleximi alrimiv ss2ab sylibr 3sstr4g ) DETZABGZHZCIZDFJZTZAH
      ZCKZFLZEUKTZBHZCKZFLZACDMBCEMUJUNURGZFIUOUSNUJUTFUIUMUQCUIULUPABUGULUPGUH
      UGULUPDEUKOPQUGUHRUAUBUCUNURFUDUEACFDSBCFESUF $.
  $}

  ${
    bj-gabssd.nf $e |- ( ph -> A. x ph ) $.
    bj-gabssd.c $e |- ( ph -> A = B ) $.
    bj-gabssd.f $e |- ( ph -> ( ps -> ch ) ) $.
    $( Inclusion of generalized class abstractions.  Deduction form.
       (Contributed by BJ, 4-Oct-2024.) $)
    bj-gabssd $p |- ( ph -> {{ A | x | ps }} C_ {{ B | x | ch }} ) $=
      ( wceq wi wa wal bj-cgab wss jca alrimih bj-gabss syl ) AEFJZBCKZLZDMBDEN
      CDFNOAUBDGATUAHIPQBCDEFRS $.
  $}

  ${
    bj-gabeqd.nf $e |- ( ph -> A. x ph ) $.
    bj-gabeqd.c $e |- ( ph -> A = B ) $.
    bj-gabeqd.f $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Equality of generalized class abstractions.  Deduction form.
       (Contributed by BJ, 4-Oct-2024.) $)
    bj-gabeqd $p |- ( ph -> {{ A | x | ps }} = {{ B | x | ch }} ) $=
      ( bj-cgab biimpd bj-gabssd eqcomd biimprd eqssd ) ABDEJCDFJABCDEFGHABCIKL
      ACBDFEGAEFHMABCINLO $.
  $}

  ${
    $d A y u v $.  $d ph y u v $.  $d B x v u $.  $d ps x u v $.  $d u v x y $.
    bj-gabeqis.c $e |- ( x = y -> A = B ) $.
    bj-gabeqis.f $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Equality of generalized class abstractions, with implicit substitution.
       (Contributed by BJ, 4-Oct-2024.) $)
    bj-gabeqis $p |- {{ A | x | ph }} = {{ B | y | ps }} $=
      ( vu vv cv wceq wa wex cab bj-cgab weq adantl simpl df-bj-gab eqeq12d wb
      anbi12d cbvexdvaw cbvabv 3eqtr4i ) EIKZLZAMZCNZIOFJKZLZBMZDNZJOACEPBDFPUJ
      UNIJIJQZUIUMCDUOCDQZMZUHULABUQEFUGUKUPEFLUOGRUOUPSUAUPABUBUOHRUCUDUEACIET
      BDJFTUF $.
  $}

  ${
    $d x y $.  $d ph y $.  $d ps y $.  $d A y $.  $d B y $.
    bj-elgab.nf $e |- ( ph -> A. x ph ) $.
    bj-elgab.nfa $e |- ( ph -> F/_ x A ) $.
    bj-elgab.ex $e |- ( ph -> A e. V ) $.
    bj-elgab.is $e |- ( ph -> ( E. x ( A = B /\ ps ) <-> ch ) ) $.
    $( Elements of a generalized class abstraction.  (Contributed by BJ,
       4-Oct-2024.) $)
    bj-elgab $p |- ( ph -> ( A e. {{ B | x | ps }} <-> ch ) ) $=
      ( vy bj-cgab wcel wceq wa wex wb wi wal cab df-bj-gab eleq2i adantr nfcvd
      cv id nfeqd nf5rd syl imp 19.26 sylanbrc eqeq2 eqcom bitrdi anbi1d adantl
      wnfc exbidh ex alrimiv elabgt syl2anc bitrd bitrid ) EBDFMZNEFLUFZOZBPZDQ
      ZLUAZNZACVGVLEBDLFUBUCAVMEFOZBPZDQZCAEGNVHEOZVKVPRZSZLTVMVPRJAVSLAVQVRAVQ
      PZVJVODVTADTZVQDTZVTDTAWAVQHUDAVQWBADEUSZVQWBSIWCVQDWCDVHEWCDVHUEWCUGUHUI
      UJUKAVQDULUMVQVJVORAVQVIVNBVQVIFEOVNVHEFUNFEUOUPUQURUTVAVBVKVPLEGVCVDKVEV
      F $.
  $}

  ${
    $d x y z $.  $d ph y z $.  $d F y z $.  $d ps y z $.
    bj-gabima.nf $e |- ( ph -> A. x ph ) $.
    bj-gabima.nff $e |- ( ph -> F/_ x F ) $.
    bj-gabima.fun $e |- ( ph -> Fun F ) $.
    bj-gabima.dm $e |- ( ph -> { x | ps } C_ dom F ) $.
    $( Generalized class abstraction as a direct image.

       TODO: improve the support lemmas ~ elimag and ~ fvelima to nonfreeness
       hypothesis (and for the latter, biconditional).  (Contributed by BJ,
       4-Oct-2024.) $)
    bj-gabima $p |- ( ph -> {{ ( F ` x ) | x | ps }} = ( F " { x | ps } ) ) $=
      ( vy vz cv cfv wcel wceq cvv a1i wa wex wb wnfc bj-cgab cab cima wrex vex
      nfcvd wsb df-rex eqcom df-clab bicomi anbi12ci exbii nf5i nffvd nfeqd wnf
      nfcv nfs1v nfand weq wi eqeq2d sbequ12r anbi12d cbvexdw 3bitr2rd bj-elgab
      fveq2 cdm funfnd fvelimabd bitr4d eqrdv ) AIBCCKZDLZUAZDBCUBZUCZAIKZVQMJK
      ZDLZVTNZJVRUDZVTVSMABWDCVTVPOEACVTUFVTOMAIUEPAWDWAVRMZWCQZJRZVTWBNZBCJUGZ
      QZJRZVTVPNZBQZCRWDWGSAWCJVRUHPWKWGSAWJWFJWHWCWIWEVTWBUIWEWIBJCUJUKULUMPAW
      JWMJCACEUNAWHWICACVTWBCVTTACVTURPACWADFCWATACWAURPUOUPWICUQABCJUSPUTJCVAZ
      WJWMSVBAWNWHWLWIBWNWBVPVTWAVODVIVCBJCVDVEPVFVGVHAJDVJVRVTDADGVKHVLVMVN $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Restricted nonfreeness
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  In this subsection, we define restricted nonfreeness (or relative
  nonfreeness).

$)

  $( Syntax for restricted nonfreeness. $)
  wrnf $a wff F/ x e. A ph $.

  $( Definition of restricted nonfreeness.  Informally, the proposition
     ` F/ x e. A ph ` means that ` ph ( x ) ` does not vary on ` A ` .
     (Contributed by BJ, 19-Mar-2021.) $)
  df-bj-rnf $a |- ( F/ x e. A ph <-> ( E. x e. A ph -> A. x e. A ph ) ) $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Russell's paradox
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  A few results around Russell's paradox.  For clarity, we prove separately a
  FOL statement (now in the main part as ~ ru0 ) and then two versions
  ( ~ bj-ru1 and ~ bj-ru ).  Special attention is put on minimizing axiom
  depencencies.

$)

  ${
    $d x y z $.
    $( A version of Russell's paradox ~ ru not mentioning the universal class.
       (see also ~ bj-ru ).  (Contributed by BJ, 12-Oct-2019.)  Remove usage of
       ~ ax-10 , ~ ax-11 , ~ ax-12 by using ~ eqabbw following BTernaryTau's
       similar revision of ~ ru .  (Revised by BJ, 28-Jun-2025.)
       (Proof modification is discouraged.) $)
    bj-ru1 $p |- -. E. y y = { x | -. x e. x } $=
      ( vz cv wel wn cab wceq wb wal ru0 weq id eleq12d notbid eqabbw mtbir nex
      ) BDZAAEZFZAGHZBUBCBECCEZFZICJCBKUAUDACSACLZTUCUEADZCDZUFUGUEMZUHNOPQR $.
  $}

  ${
    $d x y $.  $d y V $.
    $( Remove dependency on ~ ax-13 (and ~ df-v ) from Russell's paradox ~ ru
       expressed with primitive symbols and with a class variable ` V ` .  Note
       the more economical use of ~ elissetv instead of ~ isset to avoid use of
       ~ df-v .  (Contributed by BJ, 12-Oct-2019.)
       (Proof modification is discouraged.) $)
    bj-ru $p |- -. { x | -. x e. x } e. V $=
      ( vy wel wn cab wcel cv wceq wex bj-ru1 elissetv mto ) AADEAFZBGCHNICJACK
      CNBLM $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Curry's paradox in set theory
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d x ph $.
    $( Lemma for ~ currysetlem , where it is used with ` ( x e. x -> ph ) `
       substituted for ` ps ` .  (Contributed by BJ, 23-Sep-2023.)  This proof
       is intuitionistically valid.  (Proof modification is discouraged.) $)
    currysetlem $p |- ( { x | ps } e. V ->
                        ( { x | ps } e. { x | ( x e. x -> ph ) } <->
                                      ( { x | ps } e. { x | ps } -> ph ) ) ) $=
      ( wel wi cab wcel nfab1 nfel nfv nfim cv wceq id eleq12d imbi1d elabgf )
      CCEZAFBCGZTHZAFCTDBCIZUAACCTTUBUBJACKLCMZTNZSUAAUDUCTUCTUDOZUEPQR $.

    $( Curry's paradox in set theory.  This can be seen as a generalization of
       Russell's paradox, which corresponds to the case where ` ph ` is
       ` F. ` .  See alternate exposal of basically the same proof
       ~ currysetALT .  (Contributed by BJ, 23-Sep-2023.)  This proof is
       intuitionistically valid.  (Proof modification is discouraged.) $)
    curryset $p |- -. { x | ( x e. x -> ph ) } e. V $=
      ( wel wi cab wcel cvv wceq wn currysetlem ibi pm2.43i mpbiri ax-1 alrimiv
      wal bj-abv syl nvel eleq1 mtbiri 4syl pm2.01i ) BBDZAEZBFZCGZUHUGUGGZAUGH
      IZUHJUHUIUIAEZUIAUIUKAUFBUGKLMZAUFBCKNULAUFBQUJAUFBAUEOPUFBRSUJUHHCGCTUGH
      CUAUBUCUD $.
  $}

  ${
    $d x ph $.
    currysetlem2.def $e |- X = { x | ( x e. x -> ph ) } $.
    $( Lemma for ~ currysetALT .  (Contributed by BJ, 23-Sep-2023.)  This proof
       is intuitionistically valid.  (Proof modification is discouraged.) $)
    currysetlem1 $p |- ( X e. V -> ( X e. X <-> ( X e. X -> ph ) ) ) $=
      ( wcel wel wi cab eqcomi eleq2i nfab1 nfcxfr nfel nfim cv wceq id eleq12d
      nfv imbi1d elabgf bitr3id ) DDFZDBBGZAHZBIZFDCFUDAHZUGDDDUGEJKUFUHBDCBDUG
      EUFBLMZUDABBDDUIUINABTOBPZDQZUEUDAUKUJDUJDUKRZULSUAUBUC $.

    $( Lemma for ~ currysetALT .  (Contributed by BJ, 23-Sep-2023.)  This proof
       is intuitionistically valid.  (Proof modification is discouraged.) $)
    currysetlem2 $p |- ( X e. V -> ( X e. X -> ph ) ) $=
      ( wcel wi currysetlem1 biimpd pm2.43d ) DCFZDDFZAKLLAGABCDEHIJ $.

    $( Lemma for ~ currysetALT .  (Contributed by BJ, 23-Sep-2023.)  This proof
       is intuitionistically valid.  (Proof modification is discouraged.) $)
    currysetlem3 $p |- -. X e. V $=
      ( wcel cvv wn wi currysetlem2 currysetlem1 mpbird pm2.43i wel wal alrimiv
      wceq ax-1 cab bj-abv eqtrid syl nvel eleq1 mtbiri 4syl pm2.01i ) DCFZUHDD
      FZADGQZUHHUHUIUIAIABCDEJABCDEKLUIAABDDEJMABBNZAIZBOZUJAULBAUKRPUMDULBSGEU
      LBTUAUBUJUHGCFCUCDGCUDUEUFUG $.
  $}

  ${
    $d x ph $.
    $( Alternate proof of ~ curryset , or more precisely alternate exposal of
       the same proof.  (Contributed by BJ, 23-Sep-2023.)  This proof is
       intuitionistically valid.  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    currysetALT $p |- -. { x | ( x e. x -> ph ) } e. V $=
      ( wel wi cab eqid currysetlem3 ) ABCBBDAEBFZIGH $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Some disjointness results
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  A few utility theorems on disjointness of classes.

$)

  ${
    $d x A $.
    bj-n0i.1 $e |- A =/= (/) $.
    $( Inference associated with ~ n0 .  Shortens ~ 2ndcdisj (2888>2878),
       ~ notsep (264>253).  (Contributed by BJ, 22-Apr-2019.) $)
    bj-n0i $p |- E. x x e. A $=
      ( c0 wne cv wcel wex n0 mpbi ) BDEAFBGAHCABIJ $.
  $}

  $( Disjointness of the singletons containing 0 and 1.  This is a consequence
     of ~ disjcsn but the present proof does not use regularity.  (Contributed
     by BJ, 4-Apr-2019.)  (Proof modification is discouraged.) $)
  bj-disjsn01 $p |- ( { (/) } i^i { 1o } ) = (/) $=
    ( c0 c1o wne csn cin wceq 1n0 necomi disjsn2 ax-mp ) ABCADBDEAFBAGHABIJ $.

  $( The empty set does not belong to ` { 1o } ` .  (Contributed by BJ,
     6-Apr-2019.) $)
  bj-0nel1 $p |- (/) e/ { 1o } $=
    ( c0 c1o csn wcel wceq 1n0 nesymi 0ex elsn mtbir nelir ) ABCZALDABEBAFGABHI
    JK $.

  $( ` 1o ` does not belong to ` { (/) } ` .  (Contributed by BJ,
     6-Apr-2019.) $)
  bj-1nel0 $p |- 1o e/ { (/) } $=
    ( c1o c0 csn wcel wceq 1n0 neii elsni mto nelir ) ABCZAKDABEABFGABHIJ $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Complements on direct products
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  A few utility theorems on direct products.

$)

  $( The image of a singleton, general case.  [Change and relabel ~ xpimasn
     accordingly, maybe to xpima2sn.] (Contributed by BJ, 6-Apr-2019.) $)
  bj-xpimasn $p |- ( ( A X. B ) " { X } ) = if ( X e. A , B , (/) ) $=
    ( cxp csn cima cin c0 wceq cif wcel xpima disjsn eqid ifbieq2i ifnot 3eqtri
    wn ) ABDCEZFASGHIZHBJCAKZRZHBJUABHJABSLTUBBBHACMBNOUAHBPQ $.

  $( The image of a singleton by a direct product, empty case.  [Change and
     relabel ~ xpimasn accordingly, maybe to xpima2sn.] (Contributed by BJ,
     6-Apr-2019.) $)
  bj-xpima1sn $p |- ( -. X e. A -> ( ( A X. B ) " { X } ) = (/) ) $=
    ( wcel wn cxp csn cima c0 cif bj-xpimasn iffalse eqtrid ) CADZEABFCGHNBIJIA
    BCKNBILM $.

  $( Alternate proof of ~ bj-xpima1sn .  (Contributed by BJ, 6-Apr-2019.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  bj-xpima1snALT $p |- ( -. X e. A -> ( ( A X. B ) " { X } ) = (/) ) $=
    ( wcel wn csn cin c0 wceq cxp cima disjsn xpima1 sylbir ) CADEACFZGHIABJOKH
    IACLABOMN $.

  $( The image of a singleton by a direct product, nonempty case.  [To replace
     ~ xpimasn .] (Contributed by BJ, 6-Apr-2019.)
     (Proof modification is discouraged.) $)
  bj-xpima2sn $p |- ( X e. A -> ( ( A X. B ) " { X } ) = B ) $=
    ( wcel cxp csn cima c0 cif bj-xpimasn iftrue eqtrid ) CADZABECFGMBHIBABCJMB
    HKL $.

  $( If the first factor of a product is nonempty, and the product is a set,
     then the second factor is a set.  UPDATE: this is actually the curried
     (exported) form of ~ xpexcnv (up to commutation in the product).
     (Contributed by BJ, 6-Oct-2018.)  (Proof modification is discouraged.) $)
  bj-xpnzex $p |- ( A =/= (/) -> ( ( A X. B ) e. V -> B e. _V ) ) $=
    ( c0 wne cxp wcel cvv wi wceq 0ex eleq1a ax-mp wa xpnz xpexr2 simprd expcom
    a1d sylbi pm2.61ine ) ADEZABFZCGZBHGZIZIBDBDJZUFUBUGUEUDDHGUGUEIKDHBLMSSUBB
    DEZUFUBUHNUCDEZUFABOUDUIUEUDUINAHGUEABCPQRTRUA $.

  $( Curried (exported) form of ~ xpexg .  (Contributed by BJ, 2-Apr-2019.) $)
  bj-xpexg2 $p |- ( A e. V -> ( B e. W -> ( A X. B ) e. _V ) ) $=
    ( wcel cxp cvv xpexg ex ) ACEBDEABFGEABCDHI $.

  $( If the first factor of a product is a nonempty set, then the product is a
     set if and only if the second factor is a set.  (Contributed by BJ,
     2-Apr-2019.) $)
  bj-xpnzexb $p |- ( A e. ( V \ { (/) } ) ->
                     ( B e. _V <-> ( A X. B ) e. _V ) ) $=
    ( c0 csn cdif wcel cvv cxp bj-xpexg2 wne wi eldifsni bj-xpnzex syl impbid )
    ACDEFZGZBHGZABIHGZABQHJRADKTSLACDMABHNOP $.

  ${
    $d x A $.  $d x B $.  $d x C $.
    $( Substitution property for certain classes.  (Contributed by BJ,
       2-Apr-2019.) $)
    bj-cleq $p |- ( A = B -> { x | { x } e. ( A " C ) } =
                             { x | { x } e. ( B " C ) } ) $=
      ( wceq cima cv csn wcel wb wal cab imaeq1 eleq2 alrimiv abbi 3syl ) BCEBD
      FZCDFZEZAGHZRIZUASIZJZAKUBALUCALEBCDMTUDARSUANOUBUCAPQ $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  "Singletonization" and tagging
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  This subsection introduces the "singletonization" and the "tagging" of a
  class.  The singletonization of a class is the class of singletons of
  elements of that class.  It is useful since all nonsingletons are disjoint
  from it, so one can easily adjoin to it disjoint elements, which is what the
  tagging does: it adjoins the empty set.  This can be used for instance to
  define the one-point compactification of a topological space.  It will be
  used in the next section to define tuples which work for proper classes.

$)

  ${
    $d x y z t u A $.
    $( The class of sets "whose singletons" belong to a set is a set.  Nice
       application of ~ ax-rep .  (Contributed by BJ, 6-Oct-2018.) $)
    bj-snsetex $p |- ( A e. V -> { x | { x } e. A } e. _V ) $=
      ( vy vz vt vu wcel cv wceq wex csn cvv wi wal wb wa wsb bitri exbii eleq2
      cab elisset abbidv eleq1 biimpd eximi bj-eximcom com12 ax-rep 19.3v sbbii
      syl csb sbsbc sbceq2g elv bj-csbsn eqeq2i eqtr2 vex sneqr sylan2b syl2anb
      wsbc gen2 nfa1 mpbir mpg bj-sbel1 eleq1i df-clab anbi2i eleq1a imdistanri
      mo eqcoms impac impbii vsnex isseti 19.42v mpbiran2 3bitr4ri bibi2i albii
      mpbi dfcleq issetri ax5e 4syl ) BCHDIZBJZDKAILZWLHZAUBZMHZWNBHZAUBZMHZNZD
      KZWTDKZWTDBCUCWMXADWMWPWSJZXAWMWOWRAWLBWNUAUDXDWQWTWPWSMUEUFUMUGWQXBXCNDX
      BWQDOXCWQWTDUHUIEWPEIZWPJZEKFIZXEHZXGWPHZPZFOZEKZXHGIZWLHZXMXGLZJZEOZQZGK
      ZPZFOZEKZXLXQXGXEJZNFOEKZYBGXPDEFGUJYDXQXQFERZQYCNZEOFOYFFEXQXPXPFERZYCYE
      XPEUKZXQXPFEYHULYGXPXMXELZJZYCYGXMFXEXOUNZJZYJYGXPFXEVEZYLXPFEUOYMYLPEFXE
      XMXOMUPUQSYKYIXMFXEURUSSXPYJQXOYIJYCXMXOYIUTXGXEFVAVBUMVCVDVFXQFEXPEVGVPV
      HVIYAXKEXTXJFXSXIXHWOAFRZXOWLHZXIXSYNAXGWNUNZWLHYOAFWNWLVJYPXOWLAXGURVKSW
      OFAVLXSYOXPQZGKZYOXRYQGXRXNXPQZYQXQXPXNYHVMYSYQXPXNYOXNYONXOXMXNXOXMJYOXM
      WLXOVNUIVQVOYOXPXNXOWLXMVNVRVSSTYRYOXPGKGXOFVTWAYOXPGWBWCSWDWEWFTWGXFXKEF
      XEWPWHTVHWIVIWTDWJWK $.
  $}

  ${
    $d x A $.  $d x B $.
    $( Sethood of certain classes.  (Contributed by BJ, 2-Apr-2019.) $)
    bj-clexab $p |- ( A e. V -> { x | { x } e. ( A " B ) } e. _V ) $=
      ( wcel cima cvv cv csn cab imaexg bj-snsetex syl ) BDEBCFZGEAHINEAJGEBCDK
      ANGLM $.
  $}

  $( Symbol for singletonization. $)
  $c sngl $.

  $( Syntax for singletonization.  (Contributed by BJ, 6-Oct-2018.) $)
  bj-csngl $a class sngl A $.

  ${
    $d x y A $.
    $( Definition of "singletonization".  The class ` sngl A ` is isomorphic to
       ` A ` and since it contains only singletons, it can be easily be
       adjoined disjoint elements, which can be useful in various
       constructions.  (Contributed by BJ, 6-Oct-2018.) $)
    df-bj-sngl $a |- sngl A = { x | E. y e. A x = { y } } $.
  $}

  ${
    $d x y A $.  $d x y B $.
    $( Substitution property for ` sngl ` .  (Contributed by BJ,
       6-Oct-2018.) $)
    bj-sngleq $p |- ( A = B -> sngl A = sngl B ) $=
      ( vx vy wceq cv csn wrex cab bj-csngl rexeq abbidv df-bj-sngl 3eqtr4g ) A
      BEZCFDFGEZDAHZCIPDBHZCIAJBJOQRCPDABKLCDAMCDBMN $.
  $}

  ${
    $d x y A $.  $d x y B $.
    $( Characterization of the elements of the singletonization of a class.
       (Contributed by BJ, 6-Oct-2018.) $)
    bj-elsngl $p |- ( A e. sngl B <-> E. x e. B A = { x } ) $=
      ( vy bj-csngl wcel cv wceq wa wex csn wrex dfclel df-bj-sngl eqabri exbii
      anbi2i r19.42v bicomi 3bitri rexcom4 eqcom vsnex eqvinc exancom rexbii )
      BCEZFDGZBHZUHUGFZIZDJUIUHAGKZHZACLZIZDJZBULHZACLZDBUGMUKUODUJUNUIUNDUGDAC
      NOQPUPUIUMIZACLZDJZUSDJZACLZURUOUTDUTUOUIUMACRSPVCVAUSADCUASVBUQACUQVBUQU
      LBHUMUIIDJVBBULUBDULBAUCUDUMUIDUETSUFTT $.
  $}

  ${
    $d x A $.  $d x B $.
    $( Characterization of the elements of ` A ` in terms of elements of its
       singletonization.  (Contributed by BJ, 6-Oct-2018.) $)
    bj-snglc $p |- ( A e. B <-> { A } e. sngl B ) $=
      ( vx csn cv wceq wrex wcel wa wex df-rex bj-elsngl elisset pm4.71i 19.42v
      bj-csngl wb eleq1 eqcoms exbii 3bitr2i cvv sneqbg elv eqcom bitr3i anbi2i
      pm5.32ri bitri 3bitr4ri ) ADZCEZDZFZCBGULBHZUNIZCJZUKBPHABHZUNCBKCUKBLURU
      OULAFZIZCJZUQURURUSCJZIURUSIZCJVAURVBCABMNURUSCOVCUTCUSURUOURUOQAULAULBRS
      UHTUAUTUPCUSUNUOUSUMUKFZUNVDUSQCULAUBUCUDUMUKUEUFUGTUIUJ $.
  $}

  ${
    $d x y A $.
    $( The singletonization of a class is included in its powerclass.
       (Contributed by BJ, 6-Oct-2018.) $)
    bj-snglss $p |- sngl A C_ ~P A $=
      ( vx vy bj-csngl cpw cv wcel wss wex csn wceq wrex bj-elsngl df-rex snssi
      wa sseq1 biimparc sylan sylbi eximi ax5e syl velpw sylibr ssriv ) BADZAEZ
      BFZUGGZUIAHZUIUHGUJUKCIZUKUJUICFZJZKZCALZULCUIAMUPUMAGZUOPZCIULUOCANURUKC
      UQUNAHZUOUKUMAOUOUKUSUIUNAQRSUATTUKCUBUCBAUDUEUF $.
  $}

  ${
    $d x A $.
    $( The empty set is not a member of a singletonization (neither is any
       nonsingleton, in particular any von Neuman ordinal except possibly
       ~ df-1o ).  (Contributed by BJ, 6-Oct-2018.) $)
    bj-0nelsngl $p |- (/) e/ sngl A $=
      ( vx c0 bj-csngl wcel cv csn wceq wex vex snnz nesymi nex bj-elsngl rexex
      wrex sylbi mto nelir ) CADZCTEZCBFZGZHZBIZUDBUCCUBBJKLMUAUDBAPUEBCANUDBAO
      QRS $.
  $}

  ${
    $d x A $.
    $( Inverse of singletonization.  (Contributed by BJ, 6-Oct-2018.) $)
    bj-snglinv $p |- A = { x | { x } e. sngl A } $=
      ( cv csn bj-csngl wcel bj-snglc eqabi ) ACZDBEFABIBGH $.
  $}

  ${
    $d x y A $.
    $( A class is a set if and only if its singletonization is a set.
       (Contributed by BJ, 6-Oct-2018.) $)
    bj-snglex $p |- ( A e. _V <-> sngl A e. _V ) $=
      ( vx vy cvv wcel bj-csngl cv wceq wex isset cpw wss eximi bj-snglss sseq2
      pweq mpbiri vpwex ssex exlimiv sylbi csn cab bj-snglinv bj-snsetex impbii
      3syl eqeltrid ) ADEZAFZDEZUIBGZAHZBIZUKBAJUNULKZAKZHZBIUJUOLZBIUKUMUQBULA
      PMUQURBUQURUJUPLANUOUPUJOQMURUKBUJUOBRSTUGUAUKACGUBUJECUCDCAUDCUJDUEUHUF
      $.
  $}

  $( Symbol for the tagged copy of a class. $)
  $c tag $.

  $( Syntax for the tagged copy of a class.  (Contributed by BJ,
     6-Oct-2018.) $)
  bj-ctag $a class tag A $.

  $( Definition of the tagged copy of a class, that is, the adjunction to (an
     isomorph of) ` A ` of a disjoint element (here, the empty set).  Remark:
     this could be used for the one-point compactification of a topological
     space.  (Contributed by BJ, 6-Oct-2018.) $)
  df-bj-tag $a |- tag A = ( sngl A u. { (/) } ) $.

  $( Substitution property for ` tag ` .  (Contributed by BJ, 6-Oct-2018.) $)
  bj-tageq $p |- ( A = B -> tag A = tag B ) $=
    ( wceq bj-csngl c0 csn cun bj-ctag bj-sngleq uneq1d df-bj-tag 3eqtr4g ) ABC
    ZADZEFZGBDZOGAHBHMNPOABIJAKBKL $.

  ${
    $d x A $.  $d x B $.
    $( Characterization of the elements of the tagging of a class.
       (Contributed by BJ, 6-Oct-2018.) $)
    bj-eltag $p |- ( A e. tag B <-> ( E. x e. B A = { x } \/ A = (/) ) ) $=
      ( bj-ctag wcel bj-csngl c0 csn wo cv wceq wrex df-bj-tag eleq2i bj-elsngl
      cun elun 0ex elsn2 orbi12i 3bitri ) BCDZEBCFZGHZPZEBUCEZBUDEZIBAJHKACLZBG
      KZIUBUEBCMNBUCUDQUFUHUGUIABCOBGRSTUA $.
  $}

  $( The empty set belongs to the tagging of a class.  (Contributed by BJ,
     6-Apr-2019.) $)
  bj-0eltag $p |- (/) e. tag A $=
    ( c0 bj-csngl csn cun bj-ctag wcel wo 0ex snid olci elun df-bj-tag eleqtrri
    mpbir ) BACZBDZEZAFBRGBPGZBQGZHTSBIJKBPQLOAMN $.

  $( The tagging of a class is nonempty.  (Contributed by BJ, 6-Apr-2019.) $)
  bj-tagn0 $p |- tag A =/= (/) $=
    ( c0 bj-ctag bj-0eltag ne0ii ) BACADE $.

  $( The tagging of a class is included in its powerclass.  (Contributed by BJ,
     6-Oct-2018.) $)
  bj-tagss $p |- tag A C_ ~P A $=
    ( bj-ctag bj-csngl csn cun cpw df-bj-tag bj-snglss wcel wss 0elpw snss mpbi
    c0 0ex unssi eqsstri ) ABACZNDZEAFZAGRSTAHNTISTJAKNTOLMPQ $.

  $( The singletonization is included in the tagging.  (Contributed by BJ,
     6-Oct-2018.) $)
  bj-snglsstag $p |- sngl A C_ tag A $=
    ( bj-csngl c0 csn cun bj-ctag ssun1 df-bj-tag sseqtrri ) ABZJCDZEAFJKGAHI
    $.

  $( The singletonization is included in the tagging.  (Contributed by BJ,
     6-Oct-2018.) $)
  bj-sngltagi $p |- ( A e. sngl B -> A e. tag B ) $=
    ( bj-csngl bj-ctag bj-snglsstag sseli ) BCBDABEF $.

  $( The singletonization and the tagging of a set contain the same singletons.
     (Contributed by BJ, 6-Oct-2018.) $)
  bj-sngltag $p |- ( A e. V -> ( { A } e. sngl B <-> { A } e. tag B ) ) $=
    ( wcel csn bj-csngl bj-ctag bj-sngltagi c0 cun df-bj-tag eleq2i wo elun idd
    wceq elsni cvv wn biimtrid snprc elex pm2.24d biimtrrid syl5 jaod impbid2 )
    ACDZAEZBFZDZUIBGZDZUIBHUMUIUJIEZJZDZUHUKULUOUIBKLUPUKUIUNDZMUHUKUIUJUNNUHUK
    UKUQUHUKOUQUIIPZUHUKUIIQURARDZSUHUKAUAUHUSUKACUBUCUDUEUFTTUG $.

  $( Characterization of the elements of ` B ` in terms of elements of its
     tagged version.  (Contributed by BJ, 6-Oct-2018.) $)
  bj-tagci $p |- ( A e. B -> { A } e. tag B ) $=
    ( wcel csn bj-csngl bj-ctag bj-snglc bj-sngltagi sylbi ) ABCADZBECJBFCABGJB
    HI $.

  $( Characterization of the elements of ` B ` in terms of elements of its
     tagged version.  (Contributed by BJ, 6-Oct-2018.) $)
  bj-tagcg $p |- ( A e. V -> ( A e. B <-> { A } e. tag B ) ) $=
    ( wcel csn bj-csngl bj-ctag bj-snglc bj-sngltag bitrid ) ABDAEZBFDACDKBGDAB
    HABCIJ $.

  ${
    $d x A $.
    $( Inverse of tagging.  (Contributed by BJ, 6-Oct-2018.) $)
    bj-taginv $p |- A = { x | { x } e. tag A } $=
      ( cv csn bj-csngl wcel cab bj-ctag bj-snglinv wb cvv bj-sngltag elv abbii
      eqtri ) BACZDZBEFZAGQBHFZAGABIRSARSJAPBKLMNO $.
  $}

  $( A class is a set if and only if its tagging is a set.  (Contributed by BJ,
     6-Oct-2018.) $)
  bj-tagex $p |- ( A e. _V <-> tag A e. _V ) $=
    ( cvv wcel bj-csngl c0 csn wa cun bj-ctag bj-snglex biantru bitri df-bj-tag
    p0ex unexb eqcomi eleq1i 3bitri ) ABCZADZBCZEFZBCZGZTUBHZBCAIZBCSUAUDAJUCUA
    NKLTUBOUEUFBUFUEAMPQR $.

  $( The products of a given class and the tagging of either of two equal
     classes are equal.  (Contributed by BJ, 6-Apr-2019.) $)
  bj-xtageq $p |- ( A = B -> ( C X. tag A ) = ( C X. tag B ) ) $=
    ( wceq bj-ctag bj-tageq xpeq2d ) ABDAEBECABFG $.

  $( The product of a set and the tagging of a set is a set.  (Contributed by
     BJ, 2-Apr-2019.) $)
  bj-xtagex $p |- ( A e. V -> ( B e. W -> ( A X. tag B ) e. _V ) ) $=
    ( wcel bj-ctag cvv cxp elex bj-tagex sylib bj-xpexg2 syl5 ) BDEZBFZGEZACEAO
    HGENBGEPBDIBJKAOCGLM $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Tuples of classes
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  This subsection gives a definition of an ordered pair, or couple (2-tuple),
  that "works" for proper classes, as evidenced by Theorems ~ bj-2uplth and
  ~ bj-2uplex , and more importantly, ~ bj-pr21val and ~ bj-pr22val .  In
  particular, one can define well-behaved tuples of classes.  Classes in ZF(C)
  are only virtual, and in particular they cannot be quantified over.  Theorem
  ~ bj-2uplex has advantages: in view of ~ df-br , several sethood antecedents
  could be removed from existing theorems.  For instance, ~ relsnopg (resp.
  ~ relsnop ) would hold without antecedents (resp. hypotheses) thanks to
  ~ relsnb ).  Also, the antecedent ` Rel R ` could be removed from ~ brrelex12
  and related theorems brrelex*, and, as a consequence, of multiple later
  theorems.  Similarly, ~ df-struct could be simplified by removing the
  exception currently made for the empty set.

  The projections are denoted by ` pr1 ` and ` pr2 ` and the couple with
  projections (or coordinates) ` A ` and ` B ` is denoted by ` (| A ,, B |) ` .

  Note that this definition uses the Kuratowski definition ( ~ df-op ) as a
  preliminary definition, and then "redefines" a couple.  It could also use the
  "short" version of the Kuratowski pair (see ~ opthreg ) without needing the
  axiom of regularity; it could even bypass this definition by "inlining" it.

  This definition is due to Anthony Morse and is expounded (with idiosyncratic
  notation) in

  Anthony P. Morse,
  _A Theory of Sets_,
  Academic Press, 1965
  (second edition 1986).

  Note that this extends in a natural way to tuples.

  A variation of this definition is justified in ~ opthprc , but here we use
  "tagged versions" of the factors (see ~ df-bj-tag ) so that an m-tuple can
  equal an n-tuple only when m = n (and the projections are the same).

  A comparison of the different definitions of tuples (strangely not mentioning
  Morse's), is given in

  Dominic McCarty and Dana Scott,
  _Reconsidering ordered pairs_,
  Bull. Symbolic Logic,
  Volume 14, Issue 3 (Sept. 2008), 379--397.

  where a recursive definition of tuples is given that avoids the two-step
  definition of tuples and that can be adapted to various set theories.

  Finally, another survey is

  Akihiro Kanamori,
  _The empty set, the singleton, and the ordered pair_,
  Bull. Symbolic Logic,
  Volume 9, Number 3 (Sept. 2003), 273--298.
  (available at ~ http://math.bu.edu/people/aki/8.pdf )

$)

  $( Symbol the class projection. $)
  $c Proj $.

  $( Syntax for the class projection.  (Contributed by BJ, 6-Apr-2019.) $)
  bj-cproj $a class ( A Proj B ) $.

  ${
    $d x A $.  $d x B $.
    $( Definition of the class projection corresponding to tagged tuples.  The
       expression ` ( A Proj B ) ` denotes the projection on the A^th
       component.  (Contributed by BJ, 6-Apr-2019.)
       (New usage is discouraged.) $)
    df-bj-proj $a |- ( A Proj B ) = { x | { x } e. ( B " { A } ) } $.
  $}

  ${
    $d x A $.  $d x B $.  $d x C $.  $d x D $.
    $( Substitution property for ` Proj ` .  (Contributed by BJ,
       6-Apr-2019.) $)
    bj-projeq $p |- ( A = C -> ( B = D -> ( A Proj B ) = ( C Proj D ) ) ) $=
      ( vx wceq bj-cproj wa csn cima wcel cab simpr simpl sneqd imaeq12d eleq2d
      cv abbidv df-bj-proj 3eqtr4g ex ) ACFZBDFZABGZCDGZFUCUDHZERIZBAIZJZKZELUH
      DCIZJZKZELUEUFUGUKUNEUGUJUMUHUGBDUIULUCUDMUGACUCUDNOPQSEABTECDTUAUB $.
  $}

  $( Substitution property for ` Proj ` .  (Contributed by BJ, 6-Apr-2019.) $)
  bj-projeq2 $p |- ( B = C -> ( A Proj B ) = ( A Proj C ) ) $=
    ( wceq bj-cproj wi eqid bj-projeq ax-mp ) AADBCDABEACEDFAGABACHI $.

  ${
    $d x A $.  $d x B $.  $d x C $.
    $( The class projection on a given component preserves unions.
       (Contributed by BJ, 6-Apr-2019.) $)
    bj-projun $p |- ( A Proj ( B u. C ) ) = ( ( A Proj B ) u. ( A Proj C ) ) $=
      ( vx cun bj-cproj cv wcel wo cima df-bj-proj eqabri orbi12i elun imaundir
      csn eleq2i 3bitri 3bitr4ri eqriv ) DABCEZFZABFZACFZEZDGZUCHZUFUDHZIUFPZBA
      PZJZHZUICUJJZHZIZUFUEHUFUBHZUGULUHUNULDUCDABKLUNDUDDACKLMUFUCUDNUPUIUAUJJ
      ZHZUIUKUMEZHUOURDUBDAUAKLUQUSUIBCUJOQUIUKUMNRST $.
  $}

  ${
    $d x A $.  $d x B $.
    $( Sethood of the class projection.  (Contributed by BJ, 6-Apr-2019.) $)
    bj-projex $p |- ( B e. V -> ( A Proj B ) e. _V ) $=
      ( vx wcel bj-cproj cv csn cima cab cvv df-bj-proj bj-clexab eqeltrid ) BC
      EABFDGHBAHZIEDJKDABLDBOCMN $.
  $}

  ${
    $d x A $.  $d x B $.  $d x C $.  $d x V $.
    $( Value of the class projection.  (Contributed by BJ, 6-Apr-2019.) $)
    bj-projval $p |- ( A e. V ->
                  ( A Proj ( { B } X. tag C ) ) = if ( B = A , C , (/) ) ) $=
      ( vx wcel csn bj-ctag cxp bj-cproj wceq c0 cif wi wn wa cima cab eleq2d
      cv elsng bj-xpima2sn biimtrrdi imp abbidv df-bj-proj bj-taginv 3eqtr4g ex
      eqabri elsni bj-xpima1sn nsyl5 bitrid mtbiri eq0rdv ifval sylanblrc eqcom
      noel wb ifbi ax-mp eqtrdi ) ADFZABGZCHZIZJZABKZCLMZBAKZCLMZVEVJVICKZNVJOZ
      VILKNVIVKKVEVJVNVEVJPZETZGZVHAGQZFZERVRVGFZERVICVPVTWAEVPVSVGVRVEVJVSVGKZ
      VEVJAVFFZWBABDUAVFVGAUBUCUDSUEEAVHUFZECUGUHUIVOEVIVOVQVIFZVRLFZVRUTWEVTVO
      WFVTEVIWDUJVOVSLVRWCVJVSLKABUKVFVGAULUMSUNUOUPVJVICLUQURVJVLVAVKVMKABUSVJ
      VLCLVBVCVD $.
  $}

  $( Symbols for Morse tuples. $)
  $c (| ,, |) $.

  $( Symbols for class tuple projections. $)
  $c pr1 pr2 $.

  $( Syntax for Morse monuple.  (Contributed by BJ, 6-Apr-2019.) $)
  bj-c1upl $a class (| A |) $.

  $( Definition of the Morse monuple (1-tuple).  This is not useful per se, but
     is used as a step towards the definition of couples (2-tuples, or ordered
     pairs).  The reason for "tagging" the set is so that an m-tuple and an
     n-tuple be equal only when m = n.  Note that with this definition, the
     0-tuple is the empty set.  New usage is discouraged because the precise
     definition is generally unimportant compared to the characteristic
     properties ~ bj-2upleq , ~ bj-2uplth , ~ bj-2uplex , and the properties of
     the projections (see ~ df-bj-pr1 and ~ df-bj-pr2 ).  (Contributed by BJ,
     6-Apr-2019.)  (New usage is discouraged.) $)
  df-bj-1upl $a |- (| A |) = ( { (/) } X. tag A ) $.

  $( Substitution property for ` (| - |) ` .  (Contributed by BJ,
     6-Apr-2019.) $)
  bj-1upleq $p |- ( A = B -> (| A |) = (| B |) ) $=
    ( wceq c0 csn bj-ctag cxp bj-c1upl bj-xtageq df-bj-1upl 3eqtr4g ) ABCDEZAFG
    LBFGAHBHABLIAJBJK $.

  $( Syntax for the first class tuple projection.  (Contributed by BJ,
     6-Apr-2019.) $)
  bj-cpr1 $a class pr1 A $.

  $( Definition of the first projection of a class tuple.  New usage is
     discouraged because the precise definition is generally unimportant
     compared to the characteristic properties ~ bj-pr1eq , ~ bj-pr11val ,
     ~ bj-pr21val , ~ bj-pr1ex .  (Contributed by BJ, 6-Apr-2019.)
     (New usage is discouraged.) $)
  df-bj-pr1 $a |- pr1 A = ( (/) Proj A ) $.

  $( Substitution property for ` pr1 ` .  (Contributed by BJ, 6-Apr-2019.) $)
  bj-pr1eq $p |- ( A = B -> pr1 A = pr1 B ) $=
    ( wceq c0 bj-cproj bj-cpr1 bj-projeq2 df-bj-pr1 3eqtr4g ) ABCDAEDBEAFBFDABG
    AHBHI $.

  $( The first projection preserves unions.  (Contributed by BJ,
     6-Apr-2019.) $)
  bj-pr1un $p |- pr1 ( A u. B ) = ( pr1 A u. pr1 B ) $=
    ( c0 cun bj-cproj bj-cpr1 bj-projun df-bj-pr1 uneq12i 3eqtr4i ) CABDZECAEZC
    BEZDKFAFZBFZDCABGKHNLOMAHBHIJ $.

  $( Value of the first projection.  (Contributed by BJ, 6-Apr-2019.) $)
  bj-pr1val $p |- pr1 ( { A } X. tag B ) = if ( A = (/) , B , (/) ) $=
    ( csn bj-ctag cxp bj-cpr1 c0 bj-cproj wceq cif df-bj-pr1 cvv 0ex bj-projval
    wcel ax-mp eqtri ) ACBDEZFGRHZAGIBGJZRKGLOSTIMGABLNPQ $.

  $( Value of the first projection of a monuple.  (Contributed by BJ,
     6-Apr-2019.) $)
  bj-pr11val $p |- pr1 (| A |) = A $=
    ( bj-c1upl bj-cpr1 csn bj-ctag cxp wceq df-bj-1upl bj-pr1eq ax-mp bj-pr1val
    c0 cif eqid iftruei 3eqtri ) ABZCZLDAEFZCZLLGZALMAQSGRTGAHQSIJLAKUAALLNOP
    $.

  $( Sethood of the first projection.  (Contributed by BJ, 6-Oct-2018.) $)
  bj-pr1ex $p |- ( A e. V -> pr1 A e. _V ) $=
    ( wcel bj-cpr1 c0 bj-cproj cvv df-bj-pr1 bj-projex eqeltrid ) ABCADEAFGAHEA
    BIJ $.

  $( The characteristic property of monuples.  Note that this holds without
     sethood hypotheses.  (Contributed by BJ, 6-Apr-2019.) $)
  bj-1uplth $p |- ( (| A |) = (| B |) <-> A = B ) $=
    ( bj-c1upl wceq bj-cpr1 bj-pr1eq bj-pr11val 3eqtr3g bj-1upleq impbii ) ACZB
    CZDZABDMKELEABKLFAGBGHABIJ $.

  $( A monuple is a set if and only if its coordinates are sets.  (Contributed
     by BJ, 6-Apr-2019.) $)
  bj-1uplex $p |- ( (| A |) e. _V <-> A e. _V ) $=
    ( bj-c1upl cvv wcel bj-cpr1 bj-pr11val bj-pr1ex eqeltrrid c0 csn df-bj-1upl
    bj-ctag cxp wi p0ex bj-xtagex ax-mp eqeltrid impbii ) ABZCDZACDZUAATECAFTCG
    HUBTIJZALMZCAKUCCDUBUDCDNOUCACCPQRS $.

  $( A monuple is nonempty.  (Contributed by BJ, 6-Apr-2019.) $)
  bj-1upln0 $p |- (| A |) =/= (/) $=
    ( bj-c1upl csn bj-ctag cxp df-bj-1upl wne 0nep0 necomi bj-tagn0 xpnz biimpi
    c0 wa mp2an eqnetri ) ABMCZADZEZMAFQMGZRMGZSMGZMQHIAJTUANUBQRKLOP $.

  $( Syntax for Morse couple.  (Contributed by BJ, 6-Oct-2018.) $)
  bj-c2uple $a class (| A ,, B |) $.

  $( Definition of the Morse couple.  See ~ df-bj-1upl .  New usage is
     discouraged because the precise definition is generally unimportant
     compared to the characteristic properties ~ bj-2upleq , ~ bj-2uplth ,
     ~ bj-2uplex , and the properties of the projections (see ~ df-bj-pr1 and
     ~ df-bj-pr2 ).  (Contributed by BJ, 6-Oct-2018.)
     (New usage is discouraged.) $)
  df-bj-2upl $a |- (| A ,, B |) = ( (| A |) u. ( { 1o } X. tag B ) ) $.

  $( Substitution property for ` (| - ,, - |) ` .  (Contributed by BJ,
     6-Oct-2018.) $)
  bj-2upleq $p |- ( A = B -> ( C = D -> (| A ,, C |) = (| B ,, D |) ) ) $=
    ( wceq bj-c1upl c1o csn bj-ctag cxp bj-c2uple bj-1upleq bj-xtageq uneq12 ex
    cun syl2im df-bj-2upl eqeq12i imbitrrdi ) ABEZCDEZAFZGHZCIJZPZBFZUDDIJZPZEZ
    ACKZBDKZEUAUCUGEZUBUEUHEZUJABLCDUDMUMUNUJUCUGUEUHNOQUKUFULUIACRBDRST $.

  $( Value of the first projection of a couple.  (Contributed by BJ,
     6-Oct-2018.) $)
  bj-pr21val $p |- pr1 (| A ,, B |) = A $=
    ( bj-c2uple bj-cpr1 bj-c1upl c1o csn bj-ctag wceq df-bj-2upl bj-pr1eq ax-mp
    cxp cun bj-pr1un c0 bj-pr11val cif bj-pr1val eqtri 1n0 iffalsei uneq12i un0
    neii 3eqtri ) ABCZDZAEZFGBHMZNZDZUIDZUJDZNZAUGUKIUHULIABJUGUKKLUIUJOUOAPNAU
    MAUNPAQUNFPIZBPRPFBSUPBPFPUAUEUBTUCAUDTUF $.

  $( Syntax for the second class tuple projection.  (Contributed by BJ,
     6-Oct-2018.) $)
  bj-cpr2 $a class pr2 A $.

  $( Definition of the second projection of a class tuple.  New usage is
     discouraged because the precise definition is generally unimportant
     compared to the characteristic properties ~ bj-pr2eq , ~ bj-pr22val ,
     ~ bj-pr2ex .  (Contributed by BJ, 6-Oct-2018.)
     (New usage is discouraged.) $)
  df-bj-pr2 $a |- pr2 A = ( 1o Proj A ) $.

  $( Substitution property for ` pr2 ` .  (Contributed by BJ, 6-Oct-2018.) $)
  bj-pr2eq $p |- ( A = B -> pr2 A = pr2 B ) $=
    ( wceq c1o bj-cproj bj-cpr2 bj-projeq2 df-bj-pr2 3eqtr4g ) ABCDAEDBEAFBFDAB
    GAHBHI $.

  $( The second projection preserves unions.  (Contributed by BJ,
     6-Apr-2019.) $)
  bj-pr2un $p |- pr2 ( A u. B ) = ( pr2 A u. pr2 B ) $=
    ( c1o cun bj-cproj bj-cpr2 bj-projun df-bj-pr2 uneq12i 3eqtr4i ) CABDZECAEZ
    CBEZDKFAFZBFZDCABGKHNLOMAHBHIJ $.

  $( Value of the second projection.  (Contributed by BJ, 6-Apr-2019.) $)
  bj-pr2val $p |- pr2 ( { A } X. tag B ) = if ( A = 1o , B , (/) ) $=
    ( csn bj-ctag cxp bj-cpr2 c1o bj-cproj wceq c0 cif df-bj-pr2 cvv bj-projval
    wcel 1oex ax-mp eqtri ) ACBDEZFGSHZAGIBJKZSLGMOTUAIPGABMNQR $.

  $( Value of the second projection of a couple.  (Contributed by BJ,
     6-Oct-2018.) $)
  bj-pr22val $p |- pr2 (| A ,, B |) = B $=
    ( bj-c2uple bj-cpr2 bj-c1upl c1o csn bj-ctag cxp cun c0 df-bj-2upl bj-pr2eq
    wceq ax-mp bj-pr2un eqtri cif bj-pr2val 3eqtri df-bj-1upl 1n0 iffalsei eqid
    nesymi iftruei uneq12i 0un ) ABCZDZAEZDZFGBHIZDZJZKBJBUJUKUMJZDZUOUIUPNUJUQ
    NABLUIUPMOUKUMPQULKUNBULKGAHIZDZKFNZAKRKUKURNULUSNAUAUKURMOKASUTAKFKUBUEUCT
    UNFFNZBKRBFBSVABKFUDUFQUGBUHT $.

  $( Sethood of the second projection.  (Contributed by BJ, 6-Oct-2018.) $)
  bj-pr2ex $p |- ( A e. V -> pr2 A e. _V ) $=
    ( wcel bj-cpr2 c1o bj-cproj cvv df-bj-pr2 bj-projex eqeltrid ) ABCADEAFGAHE
    ABIJ $.

  $( The characteristic property of couples.  Note that this holds without
     sethood hypotheses (compare ~ opth ).  (Contributed by BJ, 6-Oct-2018.) $)
  bj-2uplth $p |- ( (| A ,, B |) = (| C ,, D |) <-> ( A = C /\ B = D ) ) $=
    ( bj-c2uple wceq wa bj-cpr1 bj-pr1eq bj-pr21val 3eqtr3g bj-pr2eq bj-pr22val
    bj-cpr2 jca bj-2upleq imp impbii ) ABEZCDEZFZACFZBDFZGUAUBUCUASHTHACSTIABJC
    DJKUASNTNBDSTLABMCDMKOUBUCUAACBDPQR $.

  $( A couple is a set if and only if its coordinates are sets.  For the
     advantages offered by the reverse closure property, see the section head
     comment.  (Contributed by BJ, 6-Oct-2018.) $)
  bj-2uplex $p |- ( (| A ,, B |) e. _V <-> ( A e. _V /\ B e. _V ) ) $=
    ( bj-c2uple cvv wa bj-cpr1 bj-pr21val bj-pr1ex eqeltrrid bj-cpr2 bj-pr22val
    wcel bj-pr2ex jca bj-c1upl c1o csn bj-ctag cxp cun bj-1uplex snex bj-xtagex
    df-bj-2upl biimpri wi ax-mp unexg syl2an eqeltrid impbii ) ABCZDLZADLZBDLZE
    ZUMUNUOUMAULFDABGULDHIUMBULJDABKULDMINUPULAOZPQZBRSZTZDABUDUNUQDLZUSDLZUTDL
    UOVAUNAUAUEURDLUOVBUFPUBURBDDUCUGUQUSDDUHUIUJUK $.

  $( A couple is nonempty.  (Contributed by BJ, 21-Apr-2019.) $)
  bj-2upln0 $p |- (| A ,, B |) =/= (/) $=
    ( bj-c2uple bj-c1upl c1o csn bj-ctag cxp cun df-bj-2upl wpss bj-1upln0 0pss
    c0 wne wss mpbir ssun1 psssstr mp2an mpbi eqnetri ) ABCADZEFBGHZIZNABJNUEKZ
    UENONUCKZUCUEPUFUGUCNOALUCMQUCUDRNUCUESTUEMUAUB $.

  $( A couple is never equal to a monuple.  It is in order to have this
     "non-clashing" result that tagging was used.  Without tagging, we would
     have ` (| A , (/) |) = (| A |) ` .  Note that in the context of Morse
     tuples, it is natural to define the 0-tuple as the empty set.  Therefore,
     the present theorem together with ~ bj-1upln0 and ~ bj-2upln0 tell us that
     an m-tuple may equal an n-tuple only when m = n, at least for m, n <= 2,
     but this result would extend as soon as we define n-tuples for higher
     values of n.  (Contributed by BJ, 21-Apr-2019.) $)
  bj-2upln1upl $p |- (| A ,, B |) =/= (| C |) $=
    ( bj-c1upl cdif wne wpss c1o csn bj-ctag cxp cun wss difeq2i cin wceq ax-mp
    c0 mpbi 0pss bj-c2uple xpundi incom xp01disjl eqtr3i disjdif2 1oex bj-tagn0
    wa snnz xpnz eqnetri eqnetrri mpbir ssun2 sscon ssdif df-bj-2upl df-bj-1upl
    pm3.2i sstri uneq1i eqtri difeq1i sseqtrri psssstr mp2an difn0 ) ABUAZCDZEZ
    RFZVIVJFRVKGZVLRHIZBJZKZRIZAJZKZVQCJZKZLZEZGZWCVKMVMWDWCRFVPVQVRVTLZKZEZWCR
    WFWBVPVQVRVTUBNWGVPRVPWFOZRPWGVPPWFVPOWHRWFVPUCWEVOUDUEVPWFUFQVNRFZVORFZUIV
    PRFWIWJHUGUJBUHUTVNVOUKSULUMWCTUNWCVIWAEZVKWCVSVPLZWAEZWKWCVPWAEZWMWAWBMWCW
    NMWAVSUOWAWBVPUPQVPWLMWNWMMVPVSUOVPWLWAUQQVAVIWLWAVIADZVPLWLABURWOVSVPAUSVB
    VCVDVEVJWAVICUSNVERWCVKVFVGVKTSVIVJVHQ $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Set theory: elementary operations relative to a universe
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  Some elementary set-theoretic operations "relative to a universe" (by which
  is merely meant some given class considered as a universe).

$)

  ${
    bj-rcleqf.a $e |- F/_ x A $.
    bj-rcleqf.b $e |- F/_ x B $.
    bj-rcleqf.v $e |- F/_ x V $.
    $( Relative version of ~ cleqf .  (Contributed by BJ, 27-Dec-2023.) $)
    bj-rcleqf $p |- ( ( V i^i A ) = ( V i^i B ) <->
                                           A. x e. V ( x e. A <-> x e. B ) ) $=
      ( cv cin wcel wb wal wi wceq wral wa elin bibi12i pm5.32 nfin albii cleqf
      bitr4i df-ral 3bitr4i ) AHZDBIZJZUFDCIZJZKZALUFDJZUFBJZUFCJZKZMZALUGUINUO
      ADOUKUPAUKULUMPZULUNPZKUPUHUQUJURUFDBQUFDCQRULUMUNSUCUAAUGUIADBGETADCGFTU
      BUOADUDUE $.
  $}

  ${
    $d A x $.  $d B x $.  $d V x $.
    $( Relative version of ~ dfcleq .  (Contributed by BJ, 27-Dec-2023.) $)
    bj-rcleq $p |- ( ( V i^i A ) = ( V i^i B ) <->
                                           A. x e. V ( x e. A <-> x e. B ) ) $=
      ( nfcv bj-rcleqf ) ABCDABEACEADEF $.
  $}

  ${
    $d A x $.  $d V x $.
    $( Relative form of ~ eqabb .  (Contributed by BJ, 27-Dec-2023.) $)
    bj-reabeq $p |- ( ( V i^i A ) = { x e. V | ph } <->
                                               A. x e. V ( x e. A <-> ph ) ) $=
      ( cin crab wceq cv wcel wb wral dfrab3 eqeq2i nfcv nfab1 bj-rcleqf bibi2i
      cab abid ralbii 3bitri ) DCEZABDFZGUBDABRZEZGBHZCIZUFUDIZJZBDKUGAJZBDKUCU
      EUBABDLMBCUDDBCNABOBDNPUIUJBDUHAUGABSQTUA $.
  $}

  $( Relative version of ~ ssdifin0 , allowing a biconditional, and of
     ~ disj2 .  (Contributed by BJ, 11-Nov-2021.)  This proof does not rely,
     even indirectly, on ~ ssdifin0 nor ~ disj2 .
     (Proof modification is discouraged.) $)
  bj-disj2r $p |-
                ( ( A i^i V ) C_ ( V \ B ) <-> ( ( A i^i B ) i^i V ) = (/) ) $=
    ( cin cdif wss wceq dfss2 indif2 inss1 ssid inss2 ssini eqssi difeq1i eqtri
    c0 eqeq1i eqcom 3bitri disj3 in32 3bitr2i ) ACDZCBEZFZUDUDBEZGZUDBDZQGABDCD
    ZQGUFUDUEDZUDGUGUDGUHUDUEHUKUGUDUKUDCDZBEUGUDCBIULUDBULUDUDCJUDUDCUDKACLMNO
    PRUGUDSTUDBUAUIUJQACBUBRUC $.

  $( Contraposition law for relative subclasses.  Relative and generalized
     version of ~ ssconb .  Shortens ~ ssconb , ~ conss2 .  (Contributed by BJ,
     11-Nov-2021.)  This proof does not rely, even indirectly, on ~ ssconb nor
     ~ conss2 .  (Proof modification is discouraged.) $)
  bj-sscon $p |- ( ( A i^i V ) C_ ( V \ B ) <-> ( B i^i V ) C_ ( V \ A ) ) $=
    ( cin c0 wceq cdif wss incom ineq1i eqeq1i bj-disj2r 3bitr4i ) ABDZCDZEFBAD
    ZCDZEFACDCBGHBCDCAGHOQENPCABIJKABCLBACLM $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Axioms for finite unions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  In this section, we introduce the axiom of singleton ~ ax-bj-sn and the axiom
  of binary union ~ ax-bj-bun .  Both axioms are implied by the standard
  axioms of unordered pair ~ ax-pr and of union ~ ax-un (see ~ snex and
  ~ unex ).  Conversely, the axiom of unordered pair ~ ax-pr is implied by the
  axioms of singleton and of binary union, as proved in ~ bj-prexg and
  ~ bj-prex .

  The axioms of union ~ ax-un and of powerset ~ ax-pow are independent of these
  axioms: consider respectively the class of pseudo-hereditarily sets
  of cardinality less than a given singular strong limit cardinal, see

  Greg Oman, _On the axiom of union_, Arch. Math. Logic (2010) 49:283--289

  (that model does have finite unions), and the class of well-founded
  hereditarily countable sets (or hereditarily less than a given uncountable
  regular cardinal).  See also ~ https://mathoverflow.net/questions/81815 and
  ~ https://mathoverflow.net/questions/48365 .

  A proof by finite induction shows that the existence of finite unions is
  equivalent to the existence of binary unions and of nullary unions (the
  latter being the axiom of the empty set ~ ax-nul ).

  The axiom of binary union is useful in theories without the axioms of union
  ~ ax-un and of powerset ~ ax-pow .  For instance, the class of well-founded
  sets hereditarily of cardinality at most ` n e. NN0 ` with ordinary
  membership relation is a model of
  { ~ ax-ext , ~ ax-rep , ~ ax-sep , ~ ax-nul , ~ ax-reg } and the axioms of
  existence of unordered ` m ` -tuples for all ` m <_ n ` , and in most cases
  one would like to rule out such models, hence the need for extra axioms,
  typically variants of powersets or unions.

  The axiom of adjunction ~ ax-bj-adj is more widely used, and is an axiom of
  General Set Theory.  We prove how to retrieve it from binary union and
  singleton in ~ bj-adjfrombun and conversely how to prove from adjunction
  singleton ( ~ bj-snfromadj ) and unordered pair ( ~ bj-prfromadj ).

$)

  ${
    $d x y $.  $d ph y $.
    $( Two ways of stating that the extension of a formula is a set.
       (Contributed by BJ, 18-Jan-2025.)
       (Proof modification is discouraged.) $)
    bj-abex $p |- ( { x | ph } e. _V <-> E. y A. x ( x e. y <-> ph ) ) $=
      ( cab cvv wcel cv wceq wex wel wb wal isset eqabb exbii bitri ) ABDZEFCGZ
      QHZCIBCJAKBLZCICQMSTCABRNOP $.
  $}

  ${
    $d A x y $.
    bj-clex.1 $e |- ( x e. A <-> ph ) $.
    $( Two ways of stating that a class is a set.  (Contributed by BJ,
       18-Jan-2025.)  (Proof modification is discouraged.) $)
    bj-clex $p |- ( A e. _V <-> E. y A. x ( x e. y <-> ph ) ) $=
      ( cvv wcel cv wceq wex wel wb wal isset dfcleq bibi2i albii bitri exbii )
      DFGCHZDIZCJBCKZALZBMZCJCDNUAUDCUAUBBHDGZLZBMUDBTDOUFUCBUEAUBEPQRSR $.
  $}

  ${
    $d x y z $.
    $( Two ways of stating the axiom of singleton (which is the universal
       closure of either side, see ~ ax-bj-sn ).  (Contributed by BJ,
       12-Jan-2025.)  (Proof modification is discouraged.) $)
    bj-axsn $p |- ( { x } e. _V <-> E. y A. z ( z e. y <-> z = x ) ) $=
      ( weq cv csn velsn bj-clex ) CADCBAEZFCIGH $.
    $( $j usage 'bj-axsn' avoids 'ax-sep' 'ax-nul' 'ax-pr' 'ax-pow'; $)
  $}

  ${
    $d x y z $.
    $( Axiom of singleton.  (Contributed by BJ, 12-Jan-2025.) $)
    ax-bj-sn $a |- A. x E. y A. z ( z e. y <-> z = x ) $.
  $}

  ${
    $d x y z $.  $d x A $.
    $( A singleton built on a set is a set.  Contrary to ~ bj-snex , this proof
       is intuitionistically valid and does not require ~ ax-nul .
       (Contributed by NM, 7-Aug-1994.)  Extract it from ~ snex and prove it
       from ~ ax-bj-sn .  (Revised by BJ, 12-Jan-2025.)
       (Proof modification is discouraged.) $)
    bj-snexg $p |- ( A e. V -> { A } e. _V ) $=
      ( vx vz vy csn cvv wcel cv wceq sneq wel weq wal wex ax-bj-sn spi bj-axsn
      wb mpbir eqeltrrdi vtocleg ) AFZGHCABCIZAJUCUDFZGUDAKUEGHDELDCMSDNEOZUFCC
      EDPQCEDRTUAUB $.
    $( $j usage 'bj-snexg' avoids 'ax-sep' 'ax-nul' 'ax-pr' 'ax-pow'; $)
  $}

  ${
    $( A singleton is a set.  See also ~ snex , ~ snexALT .  (Contributed by
       NM, 7-Aug-1994.)  Prove it from ~ ax-bj-sn .  (Revised by BJ,
       12-Jan-2025.)  (Proof modification is discouraged.) $)
    bj-snex $p |- { A } e. _V $=
      ( cvv wcel csn bj-snexg wn c0 wceq snprc biimpi 0ex eqeltrdi pm2.61i ) AB
      CZADZBCABENFZOGBPOGHAIJKLM $.
    $( $j usage 'bj-snex' avoids 'ax-sep' 'ax-pr' 'ax-pow'; $)
  $}

  ${
    $d x z t $.  $d y z t $.
    $( Two ways of stating the axiom of binary union (which is the universal
       closure of either side, see ~ ax-bj-bun ).  (Contributed by BJ,
       12-Jan-2025.)  (Proof modification is discouraged.) $)
    bj-axbun $p |- ( ( x u. y ) e. _V <->
                             E. z A. t ( t e. z <-> ( t e. x \/ t e. y ) ) ) $=
      ( wel wo cv cun elun bj-clex ) DAEDBEFDCAGZBGZHDGKLIJ $.
    $( $j usage 'bj-axbun' avoids 'ax-sep' 'ax-nul' 'ax-pr' 'ax-pow'; $)
  $}

  ${
    $d x y z t $.
    $( Axiom of binary union.  (Contributed by BJ, 12-Jan-2025.) $)
    ax-bj-bun $a |- A. x A. y E. z A. t ( t e. z <-> ( t e. x \/ t e. y ) ) $.
  $}

  ${
    $d A x y $.  $d B x y $.  $d V x $.  $d W y $.  $d x y z t $.
    $( Existence of binary unions of sets, proved from ~ ax-bj-bun .
       (Contributed by BJ, 12-Jan-2025.)
       (Proof modification is discouraged.) $)
    bj-unexg $p |- ( ( A e. V /\ B e. W ) -> ( A u. B ) e. _V ) $=
      ( vx vy vt vz wcel cv wceq wex cun cvv elissetv wa wel wal spi exlimiv wo
      exdistrv uneq12 wb ax-bj-bun bj-axbun mpbir eqeltrrdi sylbir syl2an ) ACI
      EJZAKZELZFJZBKZFLZABMZNIZBDIEACOFBDOUMUPPULUOPZFLZELURULUOEFUBUTUREUSURFU
      SUQUKUNMZNUKAUNBUCVANIGHQGEQGFQUAUDGRHLZVBFVBFREEFHGUESSEFHGUFUGUHTTUIUJ
      $.
    $( $j usage 'bj-unexg' avoids 'ax-sep' 'ax-nul' 'ax-pr' 'ax-pow'; $)
  $}

  ${
    $( Existence of unordered pairs formed on sets, proved from ~ ax-bj-sn and
       ~ ax-bj-bun .  Contrary to ~ bj-prex , this proof is intuitionistically
       valid and does not require ~ ax-nul .  (Contributed by BJ, 12-Jan-2025.)
       (Proof modification is discouraged.) $)
    bj-prexg $p |- ( ( A e. V /\ B e. W ) -> { A , B } e. _V ) $=
      ( wcel wa cpr csn cun cvv df-pr bj-snexg bj-unexg syl2an eqeltrid ) ACEZB
      DEZFABGAHZBHZIZJABKPRJESJETJEQACLBDLRSJJMNO $.
      $( $j usage 'bj-prexg' avoids 'ax-sep' 'ax-nul' 'ax-pr' 'ax-pow'; $)
  $}

  ${
    $( Existence of unordered pairs proved from ~ ax-bj-sn and ~ ax-bj-bun .
       (Contributed by BJ, 12-Jan-2025.)
       (Proof modification is discouraged.) $)
    bj-prex $p |- { A , B } e. _V $=
      ( cpr csn cun cvv df-pr wcel bj-snex bj-unexg mp2an eqeltri ) ABCADZBDZEZ
      FABGMFHNFHOFHAIBIMNFFJKL $.
      $( $j usage 'bj-prex' avoids 'ax-sep' 'ax-pr' 'ax-pow'; $)
  $}

  ${
    $d x z t $.  $d y z t $.
    $( Two ways of stating the axiom of adjunction (which is the universal
       closure of either side, see ~ ax-bj-adj ).  (Contributed by BJ,
       12-Jan-2025.)  (Proof modification is discouraged.) $)
    bj-axadj $p |- ( ( x u. { y } ) e. _V <->
                              E. z A. t ( t e. z <-> ( t e. x \/ t = y ) ) ) $=
      ( wel weq wo cv csn cun wcel elun velsn orbi2i bitri bj-clex ) DAEZDBFZGZ
      DCAHZBHZIZJZDHZUCKQUDUBKZGSUDTUBLUERQDUAMNOP $.
    $( $j usage 'bj-axadj' avoids 'ax-sep' 'ax-nul' 'ax-pr' 'ax-pow'; $)
  $}

  ${
    $d x y z t $.
    $( Axiom of adjunction.  (Contributed by BJ, 19-Jan-2025.) $)
    ax-bj-adj $a |- A. x A. y E. z A. t ( t e. z <-> ( t e. x \/ t = y ) ) $.
  $}

  ${
    $d x y z t $.  $d A y $.
    $( Existence of the result of the adjunction (generalized only in the first
       term since this suffices for current applications).  (Contributed by BJ,
       19-Jan-2025.)  (Proof modification is discouraged.) $)
    bj-adjg1 $p |- ( A e. V -> ( A u. { x } ) e. _V ) $=
      ( vy vt vz cv csn cun cvv wcel wceq uneq1 eleq1d wel weq wo wb wal spi
      wex ax-bj-adj bj-axadj mpbir vtoclg ) DGZAGHZIZJKZBUGIZJKDBCUFBLUHUJJUFBU
      GMNUIEFOEDOEAPQRESFUAZUKAUKASDDAFEUBTTDAFEUCUDUE $.
  $}

  ${
    $( Singleton from adjunction and empty set.  (Contributed by BJ,
       19-Jan-2025.)  (Proof modification is discouraged.) $)
    bj-snfromadj $p |- { x } e. _V $=
      ( c0 cv csn cun cvv 0un wcel 0ex bj-adjg1 ax-mp eqeltrri ) BACDZEZMFMGBFH
      NFHIABFJKL $.
  $}

  ${
    $( Unordered pair from adjunction.  (Contributed by BJ, 19-Jan-2025.)
       (Proof modification is discouraged.) $)
    bj-prfromadj $p |- { x , y } e. _V $=
      ( cv cpr csn cun cvv df-pr wcel bj-snfromadj bj-adjg1 ax-mp eqeltri ) ACZ
      BCZDNEZOEFZGNOHPGIQGIAJBPGKLM $.
  $}

  ${
    $( Adjunction from singleton and binary union.  (Contributed by BJ,
       19-Jan-2025.)  (Proof modification is discouraged.) $)
    bj-adjfrombun $p |- ( x u. { y } ) e. _V $=
      ( cv cvv wcel csn cun vex bj-snexg elv bj-unexg mp2an ) ACZDEBCZFZDEZMOGD
      EAHPBNDIJMODDKL $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Set theory: miscellaneous
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  Miscellaneous theorems of set theory.

$)

  ${
    $d y A $.  $d y B $.  $d x y $.
    $( Alternate proof of ~ eleq2w2 and special instance of ~ eleq2 .
       (Contributed by BJ, 22-Sep-2024.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    eleq2w2ALT $p |- ( A = B -> ( x e. A <-> x e. B ) ) $=
      ( vy wceq cv wcel wb wal dfcleq biimpi weq eleq1w bibi12d spvv syl ) BCEZ
      DFZBGZRCGZHZDIZAFZBGZUCCGZHZQUBDBCJKUAUFDADALSUDTUEDABMDACMNOP $.
  $}

  ${
    $d x A $.  $d x B $.
    $( Alternate proof of ~ clel3g .  (Contributed by BJ, 1-Sep-2024.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    bj-clel3gALT $p |- ( B e. V -> ( A e. B <-> E. x ( x = B /\ A e. x ) ) ) $=
      ( wcel cv wceq wa wex elisset biantrurd 19.41v bitr4di eleq2 bicomd exbii
      pm5.32i bitrdi ) CDEZBCEZAFZCGZTHZAIZUBBUAEZHZAISTUBAIZTHUDSUGTACDJKUBTAL
      MUCUFAUBTUEUBUETUACBNOQPR $.
  $}

  $( Alternate proof of ~ pw0 .  The proofs have a similar structure: ~ pw0
     uses the definitions of powerclass and singleton as class abstractions,
     whereas ~ bj-pw0ALT uses characterizations of their elements.  Both proofs
     then use transitivity of a congruence relation (equality for ~ pw0 and
     biconditional for ~ bj-pw0ALT ) to translate the property ~ ss0b into the
     wanted result.  To translate a biconditional into a class equality, ~ pw0
     uses ~ abbii (which yields an equality of class abstractions), while
     ~ bj-pw0ALT uses ~ eqriv (which requires a biconditional of membership of
     a given setvar variable).  Note that ~ abbii , through its closed form
     ~ abbi , is proved from ~ eqrdv , which is the deduction form of ~ eqriv .
     In the other direction, ~ velpw and ~ velsn are proved from the
     definitions of powerclass and singleton using ~ elabg , which is a version
     of ~ abbii suited for membership characterizations.  (Contributed by BJ,
     14-Apr-2024.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  bj-pw0ALT $p |- ~P (/) = { (/) } $=
    ( vx c0 cpw csn cv wss wceq wcel ss0b velpw velsn 3bitr4i eqriv ) ABCZBDZAE
    ZBFPBGPNHPOHPIABJABKLM $.

  $( Quantitative version of ~ ssexg : a subset of an element of a class is an
     element of the powerclass of the union of that class.  (Contributed by BJ,
     6-Apr-2024.) $)
  bj-sselpwuni $p |- ( ( A C_ B /\ B e. V ) -> A e. ~P U. V ) $=
    ( wss wcel wa cuni cvv ssexg ssuni elpwd ) ABDBCEFACGHABCIABCJK $.

  $( Quantitative version of ~ uniexr : if the union of a class is an element
     of a class, then that class is an element of the double powerclass of the
     union of this class.  (Contributed by BJ, 6-Apr-2024.) $)
  bj-unirel $p |- ( U. A e. V -> A e. ~P ~P U. V ) $=
    ( cuni wcel cpw wss pwuni pwel bj-sselpwuni sylancr unipw pweqi eleqtrdi )
    ACZBDZABCEZEZCZEZQOANEZFTQDASDAGNBHATQIJRPPKLM $.

  $( If the intersection of two classes is a set, then inclusion among these
     classes is equivalent to membership in the powerclass.  Common
     generalization of ~ elpwg and ~ elpw2g (the latter of which could be
     proved from it).  (Contributed by BJ, 31-Dec-2023.) $)
  bj-elpwg $p |- ( ( A i^i B ) e. V -> ( A e. ~P B <-> A C_ B ) ) $=
    ( cin wcel cpw wss elpwi cvv ssidd id ssind ssexg sylan elpwg syldan expcom
    biimparc impbid2 ) ABDZCEZABFEZABGZABHUCUAUBUCUAAIEZUBUCATGUAUDUCAABUCAJUCK
    LATCMNUDUBUCABIORPQS $.

  ${
    $d x A $.
    $( This theorem ~ bj-velpwALT and the next theorem ~ bj-elpwgALT are
       alternate proofs of ~ velpw and ~ elpwg respectively, where one proves
       first the setvar case and then generalizes using ~ vtoclbg instead of
       proving first the general case using ~ elab2g and then specifying.
       Here, this results in needing an extra DV condition, a longer combined
       proof and use of ~ ax-12 .  In other cases, that order is better (e.g.,
       ~ vsnex proved before ~ snexg ).  (Contributed by BJ, 17-Jan-2025.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    bj-velpwALT $p |- ( x e. ~P A <-> x C_ A ) $=
      ( cv cpw wcel wss cab df-pw eleq2i abid bitri ) ACZBDZELLBFZAGZENMOLABHIN
      AJK $.
  $}

  ${
    $d A x $.  $d B x $.
    $( Alternate proof of ~ elpwg .  See comment for ~ bj-velpwALT .
       (Contributed by BJ, 17-Jan-2025.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    bj-elpwgALT $p |- ( A e. V -> ( A e. ~P B <-> A C_ B ) ) $=
      ( vx cv cpw wcel wss eleq1 sseq1 bj-velpwALT vtoclbg ) DEZBFZGMBHANGABHDA
      CMANIMABJDBKL $.
  $}

  ${
    $d z x $.  $d z y $.
    $( Justification theorem for ~ dfv2 if it were the definition.  See also
       ~ vjust .  (Contributed by BJ, 30-Nov-2019.)
       (Proof modification is discouraged.) $)
    bj-vjust $p |- { x | T. } = { y | T. } $=
      ( vz wtru cab cv wcel vextru 2th eqriv ) CDAEZDBEZCFZKGMLGACHBCHIJ $.
  $}

  ${
    $d x y $.
    $( Two formulations of the axiom of the empty set ~ ax-nul .  Proposal:
       place it right before ~ ax-nul .  (Contributed by BJ, 30-Nov-2019.)
       (Proof modification is discouraged.) $)
    bj-nul $p |- ( (/) e. _V <-> E. x A. y -. y e. x ) $=
      ( c0 cvv wcel cv wceq wex wel wn wal isset eq0 exbii bitri ) CDEAFZCGZAHB
      AIJBKZAHACLQRABPMNO $.
  $}

  ${
    $d x y $.
    $( Definition of the empty set using the definite description binder.  See
       also ~ bj-nuliotaALT .  (Contributed by BJ, 30-Nov-2019.)
       (Proof modification is discouraged.) $)
    bj-nuliota $p |- (/) = ( iota x A. y -. y e. x ) $=
      ( wel wn wal cio c0 cv wcel wceq cvv weu 0ex eueqi eq0 eubii eleq2 notbid
      wb mpbi albidv iota2 mp2an noel mpgbi eqcomi ) BACZDZBEZAFZGBHZGIZDZUJGJZ
      BGKIUIALZUMBEZUNSMAHZGJZALUOAGMNURUIABUQOPTUIUPAGKURUHUMBURUGULUQGUKQRUAU
      BUCUKUDUEUF $.
  $}

  ${
    $d x y $.
    $( Alternate proof of ~ bj-nuliota .  Note that this alternate proof uses
       the fact that ` iota x ph ` evaluates to ` (/) ` when there is no ` x `
       satisfying ` ph ` ( ~ iotanul ).  This is an implementation detail of
       the encoding currently used in set.mm and should be avoided.
       (Contributed by BJ, 30-Nov-2019.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    bj-nuliotaALT $p |- (/) = ( iota x A. y -. y e. x ) $=
      ( c0 wel wn wal cio 0ss cab cuni iotassuni cv csn eq0 bicomi abbii unieqi
      wceq df-sn eqcomi 0ex unisn 3eqtri sseqtri eqssi ) CBADEBFZAGZUGHUGUFAIZJ
      ZCUFAKUIALZCRZAIZJCMZJCUHULUFUKAUKUFBUJNOPQULUMUMULACSTQCUAUBUCUDUE $.
  $}

  ${
    bj-vtoclgfALT.1 $e |- F/_ x A $.
    bj-vtoclgfALT.2 $e |- F/ x ps $.
    bj-vtoclgfALT.3 $e |- ( x = A -> ( ph <-> ps ) ) $.
    bj-vtoclgfALT.4 $e |- ph $.
    $( Alternate proof of ~ vtoclgf .  Proof from ~ vtoclgft .  (This may have
       been the original proof before shortening.)  (Contributed by BJ,
       30-Sep-2019.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    bj-vtoclgfALT $p |- ( A e. V -> ps ) $=
      ( wnfc wnf wa cv wceq wb wi wal wcel pm3.2i ax-gen vtoclgft mp3an12 ) CDJ
      ZBCKZLCMDNABOPZCQZACQZLDERBUCUDFGSUFUGUECHTACITSABCDEUAUB $.
  $}

  $( Join of ~ elsng and ~ elsn2g .  (Contributed by BJ, 18-Nov-2023.) $)
  bj-elsn12g $p |- ( ( A e. V \/ B e. W ) -> ( A e. { B } <-> A = B ) ) $=
    ( wcel csn wceq wb elsng elsn2g jaoi ) ACEABFEABGHBDEABCIABDJK $.

  $( Biconditional version of ~ elsng .  (Contributed by BJ, 18-Nov-2023.) $)
  bj-elsnb $p |- ( A e. { B } <-> ( A e. _V /\ A = B ) ) $=
    ( csn wcel cvv wceq elex elsng biadanii ) ABCZDAEDABFAJGABEHI $.

  ${
    $d y f A $.
    $( Remove hypothesis from ~ pwcfsdom .  Illustration of how to remove a
       "proof-facilitating hypothesis".  Shortens theorems using ~ pwcfsdom .
       (Contributed by BJ, 14-Sep-2019.) $)
    bj-pwcfsdom $p
             |- ( aleph ` A ) ~< ( ( aleph ` A ) ^m ( cf ` ( aleph ` A ) ) ) $=
  ( vy vf cale cfv ccf cv char cmpt eqid pwcfsdom ) BACBADEFEBGCGEHEIZLJK $.
  $}

  $( Remove hypothesis from ~ grur1 .  Illustration of how to remove a
     "definitional hypothesis".  This makes its uses longer, but the theorem
     feels more self-contained.  It looks preferable when the defined term
     appears only once in the conclusion.  (Contributed by BJ, 14-Sep-2019.) $)
  bj-grur1 $p |- ( ( U e. Univ /\ U e. U. ( R1 " On ) ) ->
                                                 U = ( R1 ` ( U i^i On ) ) ) $=
    ( con0 cin eqid grur1 ) ABCZAFDE $.

  ${
    $d t x z $.  $d t y z $.  $d ph x $.  $d ph y $.  $d ph t $.
    $( The extension of a predicate ( ` ph ( z ) ` ) is included in a set
       ( ` x ` ) if and only if it is a set ( ` y ` ).  Sufficiency is obvious,
       and necessity is the content of the axiom of separation ~ ax-sep .
       Similar to Theorem 1.3(ii) of [BellMachover] p. 463.  (Contributed by
       NM, 21-Jun-1993.)  Generalized to a closed form biconditional with
       existential quantifications using two different setvars ` x , y ` (which
       need not be disjoint).  (Revised by BJ, 8-Aug-2022.)

       TODO: move after ~ sepexi .  Relabel ("sepbi"?). $)
    bj-bm1.3ii $p |- ( E. x A. z ( ph -> z e. x ) <->
                                               E. y A. z ( z e. y <-> ph ) ) $=
      ( vt wel wi wal wex weq elequ2 imbi2d albidv cbvexvw ax-sep 19.42v bimsc1
      wb wa eximi alanimi sylbir mpan2 exlimiv bibi1d biimpr alimi sylbi impbii
      bitri ) ADBFZGZDHZBIADEFZGZDHZEIZDCFZARZDHZCIZUMUPBEBEJZULUODVBUKUNABEDKL
      MNUQVAUPVAEUPURUNASRZDHZCIZVAADCEOUPVESUPVDSZCIVAUPVDCPVFUTCUOVCUSDAUNURQ
      UATUBUCUDVAUNARZDHZEIUQUTVHCECEJZUSVGDVIURUNACEDKUEMNVHUPEVGUODUNAUFUGTUH
      UIUJ $.
  $}

  ${
    $d x y z u $.
    $( Alternate version of ~ dfid2 .  (Contributed by BJ, 9-Nov-2024.)
       (Proof modification is discouraged.)  Use ~ df-id instead to make the
       semantics of the construction ~ df-opab clearer.
       (New usage is discouraged.) $)
    bj-dfid2ALT $p |- _I = { <. x , x >. | T. } $=
      ( vy vz vu cid weq copab wtru df-id cv cop wceq wa wex cab equcomi eqeq2d
      exbii bitri df-opab opeq2d pm5.32ri ax6evr 19.42v mpbiran2 id opeq12d tru
      exexw biantru abbii 3eqtr4i eqtri ) EABFZABGZHAAGZABICJZAJZBJZKZLZUNMZBNZ
      ANZCOUQURURKZLZHMZANZANZCOUOUPVDVICVDVFANZANZVIVDVJVKVCVFAVCVFUNMZBNZVFVB
      VLBUNVAVFUNUTVEUQUNUSURURABPUAQUBRVMVFUNBNBAUCVFUNBUDUESRVFUQDJZVNKZLADAD
      FZVEVOUQVPURVNURVNVPUFZVQUGQUISVJVHAVFVGAHVFUHUJRRSUKUNABCTHAACTULUM $.
  $}

  $( The empty set is never an element in an ordered-pair class abstraction.
     (Contributed by Alexander van der Vekens, 5-Nov-2017.)  (Proof shortened
     by BJ, 22-Jul-2023.)

     TODO: move to the main section when one can reorder sections so that we
     can use ~ relopab (this is a very limited reordering). $)
  bj-0nelopab $p |- -. (/) e. { <. x , y >. | ph } $=
    ( copab wrel c0 wcel wn relopab 0nelrel0 ax-mp ) ABCDZEFLGHABCILJK $.

  $( Two classes related by a binary relation are both sets.  Alternate proof
     of ~ brrelex12 .  (Contributed by BJ, 14-Jul-2023.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  bj-brrelex12ALT $p |- ( ( Rel R /\ A R B ) -> ( A e. _V /\ B e. _V ) ) $=
    ( wrel c0 wcel wn wbr cvv wa 0nelrel0 wi jcn impcom wceq opprc df-br biimpi
    cop eleq1 imbitrid syl nsyl2 sylan ) CDECFZGZABCHZAIFBIFJZCKUFUGJUGUELZUHUG
    UFUIGUGUEMNUHGABSZEOZUIABPUGUJCFZUKUEUGULABCQRUJECTUAUBUCUD $.

  ${
    $d A x y $.  $d B x y $.
    $( The membership relation and the membership predicate agree when the
       "containing" class is a set.  General version of ~ epel and closed form
       of ~ epeli .  (Contributed by Scott Fenton, 27-Mar-2011.)  (Revised by
       Mario Carneiro, 28-Apr-2015.)  TODO: move it to the main section after
       reordering to have ~ brrelex1i available.  (Proof shortened by BJ,
       14-Jul-2023.)  (Proof modification is discouraged.) $)
    bj-epelg $p |- ( B e. V -> ( A _E B <-> A e. B ) ) $=
      ( vx vy wcel cvv cep wbr wi rele brrelex1i a1i elex wb cv eleq12 df-eprel
      wel brabga expcom pm5.21ndd ) BCFZAGFZABHIZABFZUEUDJUCABHKLMUFUDJUCABNMUD
      UCUEUFODESUFDEABHGCDPAEPBQDERTUAUB $.
  $}

  $( Two classes are related by the membership relation if and only if they are
     related by the membership relation (i.e., the first is an element of the
     second) and the second is a set (hence so is the first).  TODO: move to
     Main after reordering to have ~ brrelex2i available.  Check if it is
     shorter to prove ~ bj-epelg first or ~ bj-epelb first.  (Contributed by
     BJ, 14-Jul-2023.) $)
  bj-epelb $p |- ( A _E B <-> ( A e. B /\ B e. _V ) ) $=
    ( cep wbr cvv wcel wa rele brrelex2i pm4.71i epelg pm5.32ri bitri ) ABCDZNB
    EFZGABFZOGNOABCHIJONPABEKLM $.

  $( A set does not contain the singleton formed on it.  More precisely, one
     can prove that a class contains the singleton formed on it if and only if
     it is proper and contains the empty set (since it is "the singleton formed
     on" any proper class, see ~ snprc ):
     ` |- -. ( { A } e. A <-> ( (/) e. A -> A e. _V ) ) ` .  (Contributed by
     BJ, 4-Feb-2023.) $)
  bj-nsnid $p |- ( A e. V -> -. { A } e. A ) $=
    ( wcel csn wa en2lp snidg anim1i ex mtoi ) ABCZADZACZALCZMEZALFKMOKNMABGHIJ
    $.

  ${
    $d x A $.  $d x F $.  $d x V $.
    $( Alternate proof of ~ rdg0g .  More direct since it bypasses ~ tz7.44-1
       and ~ rdg0 (and ~ vtoclg , ~ vtoclga ).  (Contributed by NM,
       25-Apr-1995.)  More direct proof.  (Revised by BJ, 17-Nov-2024.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    bj-rdg0gALT $p |- ( A e. V -> ( rec ( F , A ) ` (/) ) = A ) $=
      ( vx wcel c0 crdg cfv cres cvv cv wceq cdm wlim crn cuni cif ax-mp eqtrid
      com cmpt rdgdmlim limomss peano1 sselii rdgvalg res0 fveq2i eqid wa simpr
      wss iftrued 0ex a1i id fvmptd2 ) ACEZFBAGZHZUSFIZDJDKZFLZAVBMZNVBOPVDPVBH
      BHQZQZUAZHZAFUSMZEUTVHLTVIFVINTVIULABUBVIUCRUDUEAFDBUFRURVHFVGHAVAFVGUSUG
      UHURDFVFAJVGCVGUIURVCUJVCAVEURVCUKUMFJEURUNUOURUPUQSS $.
  $}

  ${
    $d x y $.  $d x z $.
    $( Alternate proof of ~ vn0 which does not use ~ eqabbw (and is shorter
       than ~ vn0 when ~ eqabbw is inlined).  (Contributed by BJ, 12-Jul-2026.)
       Using the same dummy variable for ` y ` and ` z ` slightly reduces the
       proof size.  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    bj-vn0ALT $p |- _V =/= (/) $=
      ( vy vz vx cvv c0 wceq wfal fal wtru cab dfv2 dfnul4 eqeq12i wcel df-clab
      wb wsb sbv bitri sylbi cv wal dfcleq bibi12i trubifal sylbb spsv mto neir
      ) DEDEFZGHUJIAJZGBJZFZGDUKEULAKBLMUMCUAZUKNZUNULNZPZCUBGCUKULUCUQGCUQIGPG
      UOIUPGUOIACQIICAOIACRSUPGBCQGGCBOGBCRSUDUEUFUGTTUHUI $.
    $( $j usage 'bj-vn0ALT' avoids 'df-clel' 'ax-8'; $)
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Axioms of separation and replacement
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  This section proves basic relations among some standard axioms of set theory,
  in particular the axiom of separation (the universal closure of ~ ax-sep )
  and the version of the axiom of replacement requiring the functional relation
  in the axiom to be a (total) function, ~ bj-rep . These axioms often appear
  (as specific instances) in the hypotheses of the theorems in this section.

$)

  ${
    $d x y $.  $d x z $.
    bj-axnul.axsep $e |- A. x E. y A. z ( z e. y <-> ( z e. x /\ F. ) ) $.
    $( Over the base theory ~ ax-1 -- ~ ax-5 , the axiom of separation implies
       the weak emptyset axiom.

       By "weak emptyset axiom", we mean the axiom asserting existence of an
       empty set (which can be called "the" empty set when the axiom of
       extensionality ~ ax-ext is posited) provided existence of a set (the
       True truth constant existentially quantified over a fresh variable,
       ~ extru ).  This is the conclusion of ~ bj-axnul .

       Note that the weak emptyset axiom implies ` |- ( E. x T. -> E. y T. ) `
       without DV conditions hence also the same statement as the weak emptyset
       axiom without DV conditions on ` x ` , but only on ` y , z ` .

       By "axiom of separation", we mean the universal closure of ~ ax-sep ,
       simulated here by its instance with ` F. ` substituted for ` ph ` (and
       with the variable used to assert existence in the weak emptyset axiom
       substituted for the containing set) as the hypothesis of ~ bj-axnul .

       In particular, the axiom of existence ~ extru and the axiom of
       separation together imply the emptyset axiom (and conversely, the
       emptyset axiom implies the axiom of existence).

       Note: this theorem does not require a disjointness condition on
       ` y , z ` , although both axioms should be stated with all variables
       disjoint.

       This proof only uses an instance of the axiom of separation with a
       bounded formula, so is valid in a constructive setting (see the CZF
       section in the "Intuitionistic Logic Explorer" iset.mm).  (Contributed
       by BJ, 8-Mar-2026.)  (Proof modification is discouraged.) $)
    bj-axnul $p |- ( E. x T. -> E. y A. z e. y F. ) $=
      ( wtru wex wfal cv wral wal wel wa wb wi bj-bisimpr alimi eximi bj-alimii
      ralrid bj-spvw mpbiri ) EAFGCBHZIZBFZUDAJUDCBKZCAKZGLMZCJZBFAUHUCBUHGCUBU
      GUEGNCUEUFGOPSQDREUDATUA $.
    $( $j usage 'bj-axnul' avoids 'ax-6' 'ax-ext' 'ax-rep' 'ax-sep'
       'ax-nul'; $)
  $}

  ${
    $d x y z t $.  $d x t ph $.
    $( Version of the axiom of replacement requiring the functional relation in
       the axiom to be a (total) function from ~ ax-rep (in the form of
       ~ axrep6 ).  (Contributed by BJ, 14-Mar-2026.)  The proof proves the
       statement without the DV condition on ` x , ph ` , but the DV condition
       is added to this statement to show that this weaker version is
       sufficient.  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    bj-rep $p |- A. x ( A. y e. x E! z ph ->
                                     E. t A. z ( z e. t <-> E. y e. x ph ) ) $=
      ( weu cv wral wel wrex wb wal wex wi wa wmo df-ral eumo imim2i moanimv
      sylibr alimi sylbi axrep6 rexanid bibi2i albii exbii sylib syl ax-gen ) A
      DFZCBGZHZDEIZACUMJZKZDLZEMZNBUNCBIZAOZDPZCLZUSUNUTULNZCLVCULCUMQVDVBCVDUT
      ADPZNVBULVEUTADRSUTADTUAUBUCVCUOVACUMJZKZDLZEMUSVABEDCUDVHUREVGUQDVFUPUOA
      CUMUEUFUGUHUIUJUK $.
  $}

  ${
    $d a t x y z $.  $d a t x y ph $.
    bj-axseprep.axnulw $e |- ( E. x T. -> E. y A. z e. y F. ) $.
    bj-axseprep.axrep $e
      |- A. x ( A. z e. x E! t ps -> E. y A. t ( t e. y <-> E. z e. x ps ) ) $.
    bj-axseprep.ps $e
                     |- ( ps <-> ( ( ph /\ t = z ) \/ ( -. ph /\ t = a ) ) ) $.
    $( Axiom of separation (universal closure of ~ ax-sep ) from a weak form of
       the axiom of replacement requiring that the functional relation in it be
       a (total) function and the weak emptyset axiom (existence of an empty
       set provided existence of a set), as written in the theorem's
       hypotheses.

       This result shows that the weak emptyset axiom is not only the result of
       a cheap way to avoid an axiom redundancy (in this case, the existence
       axiom ~ extru ) by adding it as an antecedent, but also permits to prove
       nontrivial results that hold in nonnecessarily nonempty universes.

       This proof is by cases so is not intuitionistic.  The statement does not
       require a nonempty universe; most of the proof does not either, and the
       parts that do (e.g., near ~ sb8ef and ~ sbequ12r and ~ eueq2 ) could be
       reworked to avoid it.  Proof modifications should not introduce steps
       relying on a nonempty universe, like ~ alrimiv .  (Contributed by BJ,
       14-Mar-2026.)  (Proof modification is discouraged.) $)
    bj-axseprep $p |- A. x E. y A. z ( z e. y <-> ( z e. x /\ ph ) ) $=
      ( cv wrex wa wb wal wex wi wn ax-gen wral wcel ax5e wceq bj-eximcom eubii
      weu ralbii rexbii bibi2i albii exbii imbi12i mpbi vex eueq2 rgenw bj-almp
      alcom bj-almpig wsb df-rex nfv sb8ef bitri weq 19.43 3bitri equcom anbi1i
      wo andi ancom anass biimpri a1i simprr exlimiv sbequ biimpd equcoms com12
      sb5 imbitrdi syl5 jaod orc sylbi impbid1 bitrid bibi2d alimdv nfe1 elequ1
      nfbi bicomi bibi12d cbvalv1 eximdv eximi barbara wfal ralnex df-ral dfnot
      sbequ12r pm5.21 syl2anb expcom al2imi biimtrid sylbir bj-alextruim pm2.61
      imnan wtru mpbir mp2 ) AECKZLZEKZDKZUAZXTXRUAZAMZNZEOZDPZQZCOXSRZYGQZCOYG
      COYGGPZYGXSCYKYGQCYGGUBSFKZYAUAZAYLXTUCZMZARZYLGKZUCZMZVJZEXRLZNZFOZDPZYG
      QZGPZYKXSCUUFYKUUDGOZCUUDYGGUDUUDCOZGOUUGCOUUHGUUDYTFUFZEXRTZCBFUFZEXRTZY
      MBEXRLZNZFOZDPZQZCOUUJUUDQZCOIUUQUURCUULUUJUUPUUDUUKUUIEXRBYTFJUEUGUUOUUC
      DUUNUUBFUUMUUAYMBYTEXRJUHUIUJUKULUJUMUUJCUUIEXRAFXTYQEUNGUNUOUPSUQSUUDGCU
      RUMUSXSUUFQCXSYDEGUTZGPZUUFXSYDEPUUTAEXRVAYDEGYDGVBVCVDUUSUUEGUUSUUCYFDUU
      SUUCYMEFVEZYDMZEPZNZFOYFUUSUUBUVDFUUSUUBUVDUUSUUAUVCYMUUAYCYOMZEPZYCYSMZE
      PZVJZUUSUVCUUAYCYTMZEPUVEUVGVJZEPUVIYTEXRVAUVJUVKEYCYOYSVKUKUVEUVGEVFVGUU
      SUVIUVCUUSUVFUVCUVHUVFUVCQUUSUVCUVFUVBUVEEUVBYNYDMYDYNMUVEUVAYNYDEFVHVIYN
      YDVLYCAYNVMVGUKZVNVOUVHYRUUSUVCUVGYREYCYPYRVPVQUUSYRYDEFUTZUVCYRUUSUVMUUS
      UVMQGFGFVEUUSUVMYDGFEVRVSVTWAYDEFWBZWCWDWEUVCUVFUVIUVLUVFUVHWFWGWHWIWJVSW
      KUVDYEFEYMUVCEYMEVBUVBEWLWNYEFVBYNYMYBUVCYDFEDWMUVCUVMYNYDUVMUVCUVNWOYDFE
      XEWIWPWQWCWRWSWGSWTWTYIYGXAEYATZDPZCYIUVOYFDYIYPEXRTZUVOYFQZAEXRXBUVQYCYP
      QZEOZUVRYPEXRXCUVOYBXAQZEOUVTYFXAEYAXCUVSUWAYEEUWAUVSYEUWAYBRZYDRYEUVSUWB
      UWAYBXDWOYCAXNYBYDXFXGXHXIXJWGXKWRUVPCOXOCPUVPQHUVPCXLXPUSYHYJYGCXSYGXMXI
      XQ $.
    $( $j usage 'bj-axseprep' avoids 'ax-rep' 'ax-sep' 'ax-nul'; $)
  $}

  ${
    $d s t x y z $.  $d s t x y ph $.
    bj-axreprepsep.axsep $e
                      |- A. x E. s A. y ( y e. s <-> ( y e. x /\ E. z ph ) ) $.
    bj-axreprepsep.axrep $e
      |- A. s ( A. y e. s E! z ph -> E. t A. z ( z e. t <-> E. y e. s ph ) ) $.
    $( Strong axiom of replacement (universal closure of ~ ax-rep ) from the
       axioms of separation and replacement as written in the theorem's
       hypotheses.

       The statement does not require a nonempty universe; most of the proof
       does not either, except for the use of ~ 19.8a , which could be removed
       by reworking the proof, since it is applied in a subexpression bound by
       the variable it introduces.  Proof modifications should not introduce
       steps relying on a nonempty universe, like ~ alrimiv .  (Contributed by
       BJ, 14-Mar-2026.)  (Proof modification is discouraged.) $)
    bj-axreprepsep $p |- A. x ( A. y e. x E* z ph ->
                                     E. t A. z ( z e. t <-> E. y e. x ph ) ) $=
      ( cv wral wel wrex wb wal wex wa wi ax-gen impd com12 wmo 19.42v biimprcd
      bianir pm3.43 df-ral bicom1 simplbi2com imim2i syl6 ancoms alanimi sylanb
      weu df-eu ralrid barbara nfv nfe1 nfan nfbi nfal 19.8a sylan2i simpr jca2
      biimpr bj-bisimpl anim1d impbid alexbii df-rex bibi2d albid exbidv adantl
      3bitr4g 19.26 mpbir2an bj-alimii exim ax-mp sylbir ex ax5e bj-almpig ) AD
      UAZCBIZJZDEKZACWHLZMZDNZEOZCFKZCBKZADOZPZMZCNZFOZBWIXAWNFOZWNWIXAXBWIXAPW
      IWTPZFOZXBWIWTFUBXCWNQFNXDXBQWJACFIZLZMZDNZEOZWNXIMZPZWNXCFXKWNQFXIWNUDRX
      CXKQXCXIQZXCXJQZPZFXCXIXJUEXNFNXLFNXMFNADUNZCXEJZXIXCFHXCXPQFXCXOCXEWIWPW
      GQZCNWTWOXOQZCNWGCWHUFXQWSXRCWSXQXRWOWSXQPXOWOWSXQXOWOWSWRXQXOQWSWRWOWOWR
      UGUCXQWRXOXQWPWQXOWGWQXOQWPXOWQWGADUOUHUISTUJSTUKULUMUPRUQXMFWTXJWIWTWMXH
      EWTWLXGDWSDCWOWRDWODURWPWQDWPDURADUSUTVAVBWTWKXFWJWTWPAPZCOWOAPZCOWKXFWSX
      SXTCWSXSXTWSXSWOAAWSWPWQWOADVCWOWRVGVDWPAVEVFWSWOWPAWOWPWQVHVIVJVKACWHVLA
      CXEVLVQVMVNVOVPRXLXMFVRVSVTUQXCWNFWAWBWCWDWNFWEUJGWF $.
    $( $j usage 'bj-axreprepsep' avoids 'ax-ext' 'ax-rep' 'ax-sep' 'ax-nul'; $)
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Evaluation at a class
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  This section treats the existing predicate ` Slot ` ( ~ df-slot ) as
  "evaluation at a class" and for the moment does not introduce new syntax for
  it.

$)

  ${
    $d A f $.  $d B f $.
    $( Equality theorem for the ` Slot ` construction.  This is currently a
       duplicate of ~ sloteq but may diverge from it if/when a token Eval is
       introduced for evaluation in order to separate it from Slot and any of
       its possible modifications.  (Contributed by BJ, 27-Dec-2021.)
       (Proof modification is discouraged.) $)
    bj-evaleq $p |- ( A = B -> Slot A = Slot B ) $=
      ( vf wceq cvv cv cfv cmpt cslot fveq2 mpteq2dv df-slot 3eqtr4g ) ABDZCEAC
      FZGZHCEBOGZHAIBINCEPQABOJKCALCBLM $.
  $}

  ${
    $d A f $.
    $( The evaluation at a class is a function.  (Contributed by BJ,
       27-Dec-2021.) $)
    bj-evalfun $p |- Fun Slot A $=
      ( vf cvv cv cfv cslot df-slot funmpt2 ) BCABDEAFBAGH $.

    $( The evaluation at a class is a function on the universal class.
       (General form of ~ slotfn ).  (Contributed by Mario Carneiro,
       22-Sep-2015.)  (Revised by BJ, 27-Dec-2021.) $)
    bj-evalfn $p |- Slot A Fn _V $=
      ( vf cvv cv cfv cslot fvex df-slot fnmpti ) BCABDZEAFAJGBAHI $.

    $( The evaluation at a class is a function from the universal class into
       the universal class.  (Contributed by BJ, 17-Mar-2026.) $)
    bj-evalf $p |- Slot A : _V --> _V $=
      ( vf cvv cv cfv cslot df-slot wcel fvexd fmpti ) BCCABDZEAFBAGKCHAKIJ $.
  $}

  ${
    $d A f $.  $d F f $.
    $( Value of the evaluation at a class.  Closed form of ~ strfvnd and
       ~ strfvn .  (Contributed by NM, 9-Sep-2011.)  (Revised by Mario
       Carneiro, 15-Nov-2014.)  (Revised by BJ, 27-Dec-2021.) $)
    bj-evalval $p |- ( F e. V -> ( Slot A ` F ) = ( F ` A ) ) $=
      ( vf wcel cvv cslot cfv wceq elex cv fveq1 df-slot fvex fvmpt syl ) BCEBF
      EBAGZHABHZIBCJDBADKZHRFQASBLDAMABNOP $.
  $}

  $( The evaluation at a set of the identity function is that set.  General
     form of ~ ndxarg .  The restriction to a set ` V ` is necessary since the
     argument of the function ` Slot A ` (like that of any function) has to be
     a set for the evaluation to be meaningful.  (Contributed by BJ,
     27-Dec-2021.) $)
  bj-evalid $p |- ( ( V e. W /\ A e. V ) -> ( Slot A ` ( _I |` V ) ) = A ) $=
    ( wcel cid cres cslot cfv cvv wceq resiexg bj-evalval syl fvresi sylan9eq )
    BCDZABDEBFZAGHZAQHZAPQIDRSJBCKAQILMBANO $.

  ${
    bj-ndxarg.1 $e |- E = Slot N $.
    bj-ndxarg.2 $e |- N e. NN $.
    $( Proof of ~ ndxarg from ~ bj-evalid .  (Contributed by BJ, 27-Dec-2021.)
       (Proof modification is discouraged.) $)
    bj-ndxarg $p |- ( E ` ndx ) = N $=
      ( cn cvv wcel cnx cfv wceq nnex wa cid cres cslot df-ndx bj-evalid eqtrid
      fveq12i mp2an ) EFGZBEGZHAIZBJKDUAUBLUCMENZBOZIBHUDAUECPSBEFQRT $.
  $}

  $( Closed general form of ~ strndxid .  Both sides are equal to
     ` ( F `` A ) ` by ~ bj-evalid and ~ bj-evalval respectively, but
     ~ bj-evalidval adds something to ~ bj-evalid and ~ bj-evalval in that
     ` Slot A ` appears on both sides.  (Contributed by BJ, 27-Dec-2021.) $)
  bj-evalidval $p |- ( ( V e. W /\ A e. V /\ F e. U ) ->
                        ( F ` ( Slot A ` ( _I |` V ) ) ) = ( Slot A ` F ) ) $=
    ( wcel w3a cid cres cslot cfv wa bj-evalid fveq2d 3adant3 bj-evalval eqcomd
    wceq 3ad2ant3 eqtrd ) DEFZADFZCBFZGHDIAJZKZCKZACKZCUDKZUAUBUFUGRUCUAUBLUEAC
    ADEMNOUCUAUGUHRUBUCUHUGACBPQST $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Elementwise operations
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( Token for elementwise operations. $)
  $c elwise $.

  $( Syntax for elementwise operations. $)
  celwise $a class elwise $.

  ${
    $d o x y z u v $.
    $( Define the elementwise operation associated with a given operation.  For
       instance, ` + ` is the addition of complex numbers ( ~ axaddf ), so if
       ` A ` and ` B ` are sets of complex numbers, then
       ` ( A ( elwise `` + ) B ) ` is the set of numbers of the form
       ` ( x + y ) ` with ` x e. A ` and ` y e. B ` .  The set of odd natural
       numbers is
       ` ( ( { 2 } ( elwise `` x. ) NN0 ) ( elwise `` + ) { 1 } ) ` , or less
       formally ` 2 NN0 + 1 ` .  (Contributed by BJ, 22-Dec-2021.) $)
    df-elwise $a |- elwise = ( o e. _V |->
       ( x e. _V , y e. _V |-> { z | E. u e. x E. v e. y z = ( u o v ) } ) ) $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Elementwise intersection (families of sets induced on a subset)
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  Many kinds of structures are given by families of subsets of a given set:
  Moore collections ( ~ df-mre ), topologies ( ~ df-top ), pi-systems, rings of
  sets, delta-rings, lambda-systems/Dynkin systems, algebras/fields of sets,
  sigma-algebras/sigma-fields/tribes ( ~ df-siga ), sigma rings, monotone
  classes, matroids/independent sets, bornologies, filters.

  There is a natural notion of structure induced on a subset.  It is often
  given by an elementwise intersection, namely, the
  family of intersections of sets in the original family with the given subset.
  In this subsection, we define this notion and prove its main properties.
  Classical conditions on families of subsets include being nonempty,
  containing the whole set, containing the empty set, being stable under
  unions, intersections, subsets, supersets, (relative) complements. Therefore,
  we prove related properties for the elementwise intersection.

  We will call ` ( X |``t A ) ` the elementwise intersection on the family
  ` X ` by the class ` A ` .

  REMARK: many theorems are already in set.mm: "MM> SEARCH *rest* / JOIN".

$)

  $( An elementwise intersection on the empty family is the empty set.  TODO:
     this is ~ 0rest .  (Contributed by BJ, 27-Apr-2021.) $)
  bj-rest00 $p |- ( (/) |`t A ) = (/) $=
    ( 0rest ) AB $.

  ${
    $d A x y $.  $d V x $.  $d W x $.  $d Y x y $.
    $( An elementwise intersection on the singleton on a set is the singleton
       on the intersection by that set.  Generalization of ~ bj-restsn0 and
       ~ bj-restsnid .  (Contributed by BJ, 27-Apr-2021.) $)
    bj-restsn $p |-
               ( ( Y e. V /\ A e. W ) -> ( { Y } |`t A ) = { ( Y i^i A ) } ) $=
      ( vx vy wcel wa csn crest co cin cv wceq wrex cvv wb snex elrest mpan
      velsn ineq1 sneqd eleq2d bitr3id rexsng sylan9bbr eqrdv ) DBGZACGZHEDIZAJ
      KZDALZIZUJEMZULGZUOFMZALZNZFUKOZUIUOUNGZUKPGUJUPUTQDRFUOAUKPCSTUSVAFDBUSU
      OURIZGUQDNZVAEURUAVCVBUNUOVCURUMUQDAUBUCUDUEUFUGUH $.
  $}

  $( Special case of ~ bj-restsn .  (Contributed by BJ, 27-Apr-2021.) $)
  bj-restsnss $p |-
               ( ( Y e. V /\ A C_ Y ) -> ( { Y } |`t A ) = { A } ) $=
    ( wss cin csn wceq wcel crest sseqin2 sneq sylbi cvv ssexg ancoms bj-restsn
    co syldan eqeq2 biimpa syl2an2 ) ACDZCAEZFZAFZGZCBHZCFAIQZUDGZUHUEGZUBUCAGU
    FACJUCAKLUGUBAMHZUIUBUGUKACBNOABMCPRUFUIUJUDUEUHSTUA $.

  $( Special case of ~ bj-restsn .  (Contributed by BJ, 27-Apr-2021.) $)
  bj-restsnss2 $p |-
               ( ( A e. V /\ Y C_ A ) -> ( { Y } |`t A ) = { Y } ) $=
    ( wss cin wceq wcel crest co dfss2 sneq sylbi ssexg ancoms bj-restsn syldan
    csn cvv eqeq2 biimpa syl2an2 ) CADZCAEZQZCQZFZABGZUEAHIZUDFZUHUEFZUBUCCFUFC
    AJUCCKLUGUBCRGZUIUBUGUKCABMNUKUGUIARBCONPUFUIUJUDUEUHSTUA $.

  $( An elementwise intersection on the singleton on the empty set is the
     singleton on the empty set.  Special case of ~ bj-restsn and
     ~ bj-restsnss2 .  TODO: this is ~ restsn .  (Contributed by BJ,
     27-Apr-2021.) $)
  bj-restsn0 $p |- ( A e. V -> ( { (/) } |`t A ) = { (/) } ) $=
    ( wcel c0 wss csn crest co wceq 0ss bj-restsnss2 mpan2 ) ABCDAEDFZAGHMIAJAB
    DKL $.

  $( Special case of ~ bj-restsn , ~ bj-restsnss , and ~ bj-rest10 .
     (Contributed by BJ, 27-Apr-2021.) $)
  bj-restsn10 $p |- ( X e. V -> ( { X } |`t (/) ) = { (/) } ) $=
    ( wcel c0 wss csn crest co wceq 0ss bj-restsnss mpan2 ) BACDBEBFDGHDFIBJDAB
    KL $.

  ${
    $d x y z $.
    $( The elementwise intersection on the singleton on a class by that class
       is the singleton on that class.  Special case of ~ bj-restsn and
       ~ bj-restsnss .  (Contributed by BJ, 27-Apr-2021.) $)
    bj-restsnid $p |- ( { A } |`t A ) = { A } $=
      ( vx vy vz cvv wcel csn crest co wceq wss ssid bj-restsnss mpan2 wn c0 cv
      cin cmpt crn df-rest reldmmpo ovprc2 snprc biimpi eqtr4d pm2.61i ) AEFZAG
      ZAHIZUIJZUHAAKUKALAEAMNUHOZUJPUIUIAHBCEEDBQDQCQRSTHCDBUAUBUCULUIPJAUDUEUF
      UG $.
  $}

  ${
    $d V x $.  $d X x y $.
    $( An elementwise intersection on a nonempty family by the empty set is the
       singleton on the empty set.  TODO: this generalizes ~ rest0 and could
       replace it.  (Contributed by BJ, 27-Apr-2021.) $)
    bj-rest10 $p |- ( X e. V -> ( X =/= (/) -> ( X |`t (/) ) = { (/) } ) ) $=
      ( vx vy wcel c0 wne crest co csn wceq wa cv cin wrex cvv wb 0ex wex bitri
      elrest mpan2 in0 eqeq2i rexbii df-rex 19.41v bicomi anbi1i sylan9bb velsn
      n0 baib bitr4di eqrdv ex ) BAEZBFGZBFHIZFJZKUQURLZCUSUTVACMZUSEZVBFKZVBUT
      EUQVCVBDMZFNZKZDBOZURVDUQFPEVCVHQRDVBFBAPUAUBVHURVDVHVDDBOZURVDLZVGVDDBVF
      FVBVEUCUDUEVIVEBEZVDLDSZVJVDDBUFVLVKDSZVDLVJVKVDDUGVMURVDURVMDBULUHUITTTU
      MUJCFUKUNUOUP $.
  $}

  $( Alternate version of ~ bj-rest10 .  (Contributed by BJ, 27-Apr-2021.) $)
  bj-rest10b $p |- ( X e. ( V \ { (/) } ) -> ( X |`t (/) ) = { (/) } ) $=
    ( c0 csn cdif wcel wne wa crest co wceq eldif 0ex elsn2 neqne sylnbi anim2i
    wn sylbi bj-rest10 imp syl ) BACDZEFZBAFZBCGZHZBCIJUCKZUDUEBUCFZRZHUGBAUCLU
    JUFUEUIBCKUFBCMNBCOPQSUEUFUHABTUAUB $.

  ${
    $d A x y $.  $d V x $.  $d W x $.  $d X x y $.
    $( An elementwise intersection on a nonempty family is nonempty.
       (Contributed by BJ, 27-Apr-2021.) $)
    bj-restn0 $p |-
            ( ( X e. V /\ A e. W ) -> ( X =/= (/) -> ( X |`t A ) =/= (/) ) ) $=
      ( vx vy wcel wa c0 wne cv crest co wex cin wceq wrex n0 wi vex inex1 jctr
      isseti eximi df-rex sylibr rexcom4 sylib a1i biimtrid elrest biimprd syld
      eximdv imbitrrdi ) DBGACGHZDIJZEKZDALMZGZENZUSIJUPUQURFKZAOZPZFDQZENZVAUQ
      VBDGZFNZUPVFFDRVHVFSUPVHVDENZFDQZVFVHVGVIHZFNVJVGVKFVGVIEVCVBAFTUAUCUBUDV
      IFDUEUFVDFEDUGUHUIUJUPVEUTEUPUTVEFURADBCUKULUNUMEUSRUO $.
  $}

  $( Alternate version of ~ bj-restn0 .  (Contributed by BJ, 27-Apr-2021.) $)
  bj-restn0b $p |-
               ( ( X e. ( V \ { (/) } ) /\ A e. W ) -> ( X |`t A ) =/= (/) ) $=
    ( c0 csn cdif wcel wa wne crest co eldifi eldifsni jca an32 sylib bj-restn0
    anim1i imp syl ) DBEFZGHZACHZIZDBHZUDIZDEJZIZDAKLEJZUEUFUHIZUDIUIUCUKUDUCUF
    UHDBUBMDBENOSUFUHUDPQUGUHUJABCDRTUA $.

  ${
    $d A x y $.  $d V x $.  $d W x $.  $d Y x y $.
    $( The elementwise intersection on a powerset is the powerset of the
       intersection.  This allows to prove for instance that the topology
       induced on a subset by the discrete topology is the discrete topology on
       that subset.  See also ~ restdis (which uses ~ distop and ~ restopn2 ).
       (Contributed by BJ, 27-Apr-2021.) $)
    bj-restpw $p |-
                 ( ( Y e. V /\ A e. W ) -> ( ~P Y |`t A ) = ~P ( Y i^i A ) ) $=
      ( vx vy wcel wa cpw cin wceq cvv wex wss velpw sstr2 inss1 sseq1 mpbiri
      cv crest co wrex pwexg elrest sylan anbi1i exbii com12 impel inss2 adantl
      wb ssind exlimiv mpi ssidd id a1i eqssd ineq1 eqeq2d anbi12d spcev sylan2
      vex syl2anc impbii bitri df-rex 3bitr4i bitrdi eqrdv ) DBGZACGZHZEDIZAUAU
      BZDAJZIZVPETZVRGZWAFTZAJZKZFVQUCZWAVTGZVNVQLGVOWBWFUMDBUDFWAAVQLCUEUFWCVQ
      GZWEHZFMZWAVSNZWFWGWJWCDNZWEHZFMZWKWIWMFWHWLWEFDOUGUHWNWKWMWKFWMWADAWLWAW
      CNZWADNZWEWOWLWPWAWCDPUIWEWOWDWCNWCAQWAWDWCRSUJWEWAANZWLWEWQWDANWCAUKWAWD
      ARSULUNUOWKWPWQWNWKVSDNWPDAQWAVSDPUPWKVSANWQDAUKWAVSAPUPWQWPWAWAAJZKZWNWQ
      WAWRWQWAWAAWQWAUQWQURUNWRWANWQWAAQUSUTWMWPWSHFWAEVFWCWAKZWLWPWEWSWCWADRWT
      WDWRWAWCWAAVAVBVCVDVEVGVHVIWEFVQVJEVSOVKVLVM $.
  $}

  ${
    $d A x $.  $d X x $.
    $( An elementwise intersection on a family containing the empty set
       contains the empty set.  (Contributed by BJ, 27-Apr-2021.) $)
    bj-rest0 $p |-
              ( ( X e. V /\ A e. W ) -> ( (/) e. X -> (/) e. ( X |`t A ) ) ) $=
      ( vx c0 wcel crest co wa cv cin wceq wrex wex in0 incom eqtr3i 0ex eleq1
      ineq1 eqeq2d anbi12d spcev mpan2 df-rex sylibr elrest imbitrrid ) FDGZFDA
      HIGDBGACGJFEKZALZMZEDNZUJUKDGZUMJZEOZUNUJFFALZMZUQAFLFURAPAFQRUPUJUSJEFSU
      KFMZUOUJUMUSUKFDTUTULURFUKFAUAUBUCUDUEUMEDUFUGEFADBCUHUI $.
  $}

  ${
    $d A y $.  $d B y $.  $d X y $.
    $( An elementwise intersection by a set on a family containing a superset
       of that set contains that set.  (Contributed by BJ, 27-Apr-2021.) $)
    bj-restb $p |-
                  ( X e. V -> ( ( A C_ B /\ B e. X ) -> A e. ( X |`t A ) ) ) $=
      ( vy wcel wss wa crest co cv cin wceq wrex wex id ssidd ssind inss2 cvv
      a1i eqssd wi eleq1 ineq1 eqeq2d anbi12d spcegv expd pm2.43i df-rex sylibr
      mpan9 adantl wb ssexg elrest sylan2 mpbird ex ) DCFZABGZBDFZHZADAIJFZVAVD
      HVEAEKZALZMZEDNZVDVIVAVDVFDFZVHHZEOZVIVBABALZMZVCVLVBAVMVBABAVBPVBAQRVMAG
      VBBASUAUBVCVNVLUCVCVCVNVLVKVCVNHEBDVFBMZVJVCVHVNVFBDUDVOVGVMAVFBAUEUFUGUH
      UIUJUMVHEDUKULUNVDVAATFVEVIUOABDUPEAADCTUQURUSUT $.
  $}

  $( An elementwise intersection by a subset on a family containing the whole
     set contains the whole subset.  (Contributed by BJ, 27-Apr-2021.) $)
  bj-restv $p |- ( ( A C_ U. X /\ U. X e. X ) -> A e. ( X |`t A ) ) $=
    ( cvv wcel cuni wss wa crest co uniexr adantl bj-restb mpcom ) BCDZABEZFZOB
    DZGABAHIDQNPBBJKAOCBLM $.

  $( An elementwise intersection by a set on a family containing that set
     contains that set.  (Contributed by BJ, 27-Apr-2021.) $)
  bj-resta $p |- ( X e. V -> ( A e. X -> A e. ( X |`t A ) ) ) $=
    ( wcel wss crest co ssid bj-restb mpani ) CBDAAEACDACAFGDAHAABCIJ $.

  ${
    $d A x y z $.  $d V x y $.  $d W x y $.  $d X x y z $.
    $( The union of an elementwise intersection by a set is equal to the
       intersection with that set of the union of the family.  See also
       ~ restuni and ~ restuni2 .  (Contributed by BJ, 27-Apr-2021.) $)
    bj-restuni $p |-
             ( ( X e. V /\ A e. W ) -> U. ( X |`t A ) = ( U. X i^i A ) ) $=
      ( vx vy vz wcel wa cuni cin cv wex eluni bicomi 19.42v bitri exbii 3bitri
      sseld crest co wceq wrex elrest anbi2d exbidv wb anbi1i a1i df-rex anbi2i
      excom an12 eqimss imdistanri eqimss2 impbii vex inex1 isseti biantru elin
      bianassc 19.41v 3bitr4g bitrd bitrid eqrdv ) DBHACHIZEDAUAUBZJZDJZAKZELZV
      LHVOFLZHZVPVKHZIZFMZVJVOVNHZFVOVKNVJVTVQVPGLZAKZUCZGDUDZIZFMZWAVJVSWFFVJV
      RWEVQGVPADBCUEUFUGVJVOWBHZWBDHZIZGMZVOAHZIZVOVMHZWLIZWGWAWMWOUHVJWKWNWLWN
      WKGVODNOUIUJWGVQWIWDIZIZGMZFMWQFMZGMZWMWFWRFWFVQWPGMZIZWRWEXAVQWDGDUKULWR
      XBVQWPGPOQRWQFGUMWTWJWLIZGMWMWSXCGWSWIVQWDIZIZFMWIXDFMZIXCWQXEFVQWIWDUNRW
      IXDFPXFWHWLWIXFVOWCHZWDIZFMXGWDFMZIZWHWLIZXDXHFXDXHWDVQXGWDVPWCVOVPWCUOTU
      PWDXGVQWDWCVPVOWCVPUQTUPURRXGWDFPXJXGXKXGXJXIXGFWCWBAGUSUTVAVBOVOWBAVCQSV
      DSRWJWLGVEQSVOVMAVCVFVGVHVI $.
  $}

  $( The union of an elementwise intersection on a family of sets by a subset
     is equal to that subset.  See also ~ restuni and ~ restuni2 .
     (Contributed by BJ, 27-Apr-2021.) $)
  bj-restuni2 $p |- ( ( X e. V /\ A C_ U. X ) -> U. ( X |`t A ) = A ) $=
    ( wcel cuni wss wa crest cin cvv wceq uniexg ssexg sylan2 ancoms bj-restuni
    co syldan inss2 a1i id ssidd ssind eqssd adantl eqtrd ) CBDZACEZFZGCAHQEZUH
    AIZAUGUIAJDZUJUKKUIUGULUGUIUHJDULCBLAUHJMNOABJCPRUIUKAKUGUIUKAUKAFUIUHASTUI
    AUHAUIUAUIAUBUCUDUEUF $.

  ${
    $d A x $.
    $( A reformulation of the axiom of regularity using elementwise
       intersection.  (RK: might have to be placed later since theorems in this
       section are to be moved early (in the section related to the algebra of
       sets).)  (Contributed by BJ, 27-Apr-2021.) $)
    bj-restreg $p |- ( ( A e. V /\ A =/= (/) ) -> (/) e. ( A |`t A ) ) $=
      ( vx wcel c0 wne wa crest co cv cin wceq wrex zfreg eqcom rexbii sylib wb
      simpl elrest syldan mpbird ) ABDZAEFZGZEAAHIDZECJAKZLZCAMZUEUGELZCAMUICAB
      NUJUHCAUGEOPQUCUDUCUFUIRUCUDSCEAABBTUAUB $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Moore collections (complements)
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d A x $.  $d B x $.  $d ps x $.
    bj-raldifsn.is $e |- ( x = B -> ( ph <-> ps ) ) $.
    $( All elements in a set satisfy a given property if and only if all but
       one satisfy that property and that one also does.  Typically, this can
       be used for characterizations that are proved using different methods
       for a given element and for all others, for instance zero and nonzero
       numbers, or the empty set and nonempty sets.  (Contributed by BJ,
       7-Dec-2021.) $)
    bj-raldifsn $p |-
       ( B e. A -> ( A. x e. A ph <-> ( A. x e. ( A \ { B } ) ph /\ ps ) ) ) $=
      ( wcel wral csn cun wa difsnid eqcomd raleqdv wb ralunb a1i ralsng anbi2d
      cdif 3bitrd ) EDGZACDHACDEIZTZUCJZHZACUDHZACUCHZKZUGBKUBACDUEUBUEDDELMNUF
      UIOUBACUDUCPQUBUHBUGABCEDFRSUA $.
  $}

  ${
    $d x A $.  $d x B $.  $d x X $.
    $( If ` A ` is a collection of subsets of ` X ` , like a Moore collection
       or a topology, two equivalent ways to say that arbitrary intersections
       of elements of ` A ` relative to ` X ` belong to some class ` B ` : the
       LHS singles out the empty intersection (the empty intersection relative
       to ` X ` is ` X ` and the intersection of a nonempty family of subsets
       of ` X ` is included in ` X ` , so there is no need to intersect it with
       ` X ` ).  In typical applications, ` B ` is ` A ` itself.  (Contributed
       by BJ, 7-Dec-2021.) $)
    bj-0int $p |- ( A C_ ~P X -> (
                     ( X e. B /\ A. x e. ( ~P A \ { (/) } ) |^| x e. B ) <->
                                       A. x e. ~P A ( X i^i |^| x ) e. B ) ) $=
      ( cpw wss wcel cv cint c0 csn wral wa cin wb wceq dfss2 a1i wi eleq1 cdif
      cvv ssv int0 sseqtrri mpbi eqcomi eleq1i eldifsn sstr2 intss2 elpwi syl11
      wne syl6 impd biimtrid incom eqeq1i eqcom sylbb sylbi syl5 ralrimiv ralbi
      syld anbi12d biancomd 0elpw inteq ineq2 3syl bj-raldifsn ax-mp bitr4di
      syl ) BDEZFZDCGZAHZIZCGZABEZJKUAZLZMZDWANZCGZAWDLZDJIZNZCGZMZWHAWCLZVRWFW
      IWLVRVSWLWEWIVSWLOVRDWKCWKDDWJFWKDPDUBWJDUCUDUEDWJQUFUGUHRVRWBWHOZAWDLWEW
      IOVRWOAWDVRVTWDGZWADFZWOWPVTWCGZVTJUNZMVRWQVTWCJUIVRWRWSWQVTBFZVRWSWQSZWR
      WTVRVTVQFXAVTBVQUJVTDUKUOVTBULUMUPUQWQWAWGPZVRWOWQWADNZWAPZXBWADQXDWGWAPX
      BXCWGWAWADURUSWGWAUTVAVBXBWOSVRWAWGCTRVCVFVDWBWHAWDVEVPVGVHJWCGWNWMOBVIWH
      WLAWCJVTJPWAWJPWGWKPWHWLOVTJVJWAWJDVKWGWKCTVLVMVNVO $.
  $}

  ${
    $d A x $.
    $( A Moore collection is a set.  Therefore, the class ` Moore_ ` of all
       Moore sets defined in ~ df-bj-moore is actually the class of all Moore
       collections.  This is also illustrated by the lack of sethood condition
       in ~ bj-ismoore .

       Note that the closed sets of a topology form a Moore collection, so a
       topology is a set, and this remark also applies to many other families
       of sets (namely, as soon as the whole set is required to be a set of the
       family, then the associated kind of family has no proper classes: that
       this condition suffices to impose sethood can be seen in this proof,
       which relies crucially on ~ uniexr ).

       Note: if, in the above predicate, we substitute ` ~P X ` for ` A ` ,
       then the last ` e. ~P X ` could be weakened to ` C_ X ` , and then the
       predicate would be obviously satisfied since ` |- U. ~P X = X `
       ( ~ unipw ), making ` ~P X ` a Moore collection in this weaker sense,
       for any class ` X ` , even proper, but the addition of this single case
       does not add anything interesting.  Instead, we have the biconditional
       ~ bj-discrmoore .  (Contributed by BJ, 8-Dec-2021.) $)
    bj-mooreset $p |- ( A. x e. ~P A ( U. A i^i |^| x ) e. A -> A e. _V ) $=
      ( cuni cv cint cin wcel cpw wral cvv c0 wi 0elpw rint0 eleq1d rspcv ax-mp
      wceq uniexr syl ) BCZADZEFZBGZABHZIZUABGZBJGKUEGUFUGLBMUDUGAKUEUBKRUCUABU
      AUBNOPQBBST $.
  $}

  $( Token for the class of Moore collections. $)
  $c Moore_ $.

  $( Syntax for the class of Moore collections. $)
  cmoore $a class Moore_ $.

  ${
    $d x y $.
    $( Define the class of Moore collections.  This is indeed the class of all
       Moore collections since these all are sets, as proved in ~ bj-mooreset ,
       and as illustrated by the lack of sethood condition in ~ bj-ismoore .

       This is to ~ df-mre (defining ` Moore ` ) what ~ df-top (defining
       ` Top ` ) is to ~ df-topon (defining ` TopOn ` ).

       For the sake of consistency, the function defined at ~ df-mre should be
       denoted by "MooreOn".

       Note: ~ df-mre singles out the empty intersection.  This is not
       necessary.  It could be written instead ` |- Moore = `
       ` ( x e. _V |-> { y e. ~P ~P x | A. z e. ~P y ( x i^i |^| z ) e. y } ) `
       and the equivalence of both definitions is proved by ~ bj-0int .

       There is no added generality in defining a "Moore predicate" for
       arbitrary classes, since a Moore class satisfying such a predicate is
       automatically a set (see ~ bj-mooreset ).

       TODO: move to the main section.  For many families of sets, one can
       define both the function associating to each set the set of families of
       that kind on it (like ~ df-mre and ~ df-topon ) or the class of all
       families of that kind, independent of a base set (like ~ df-bj-moore or
       ~ df-top ).  In general, the former will be more useful and the extra
       generality of the latter is not necessary.  Moore collections, however,
       are particular in that they are more ubiquitous and are used in a wide
       variety of applications (for many families of sets, the family of
       families of a given kind is often a Moore collection, for instance).
       Therefore, in the case of Moore families, having both definitions is
       useful.

       (Contributed by BJ, 27-Apr-2021.) $)
    df-bj-moore $a |- Moore_ = { x | A. y e. ~P x ( U. x i^i |^| y ) e. x } $.
  $}

  ${
    $d x y A $.
    $( Characterization of Moore collections.  Note that there is no sethood
       hypothesis on ` A ` : it is implied by either side (this is obvious for
       the LHS, and is the content of ~ bj-mooreset for the RHS).  (Contributed
       by BJ, 9-Dec-2021.) $)
    bj-ismoore $p |-
                    ( A e. Moore_ <-> A. x e. ~P A ( U. A i^i |^| x ) e. A ) $=
      ( vy cmoore wcel cvv cuni cv cint cin cpw wral elex bj-mooreset wceq pweq
      unieq ineq1d id eleq12d raleqbidv df-bj-moore elab2g pm5.21nii ) BDEBFEBG
      ZAHIZJZBEZABKZLZBDMABNCHZGZUFJZUKEZAUKKZLUJCBDFUKBOZUNUHAUOUIUKBPUPUMUGUK
      BUPULUEUFUKBQRUPSTUACAUBUCUD $.
  $}

  ${
    $d x A $.
    $( Necessary condition to be a Moore collection.  (Contributed by BJ,
       9-Dec-2021.) $)
    bj-ismoored0 $p |- ( A e. Moore_ -> U. A e. A ) $=
      ( vx cmoore wcel cuni cv cint cin cpw wral bj-ismoore c0 0elpw wceq rint0
      wi eleq1d rspcv ax-mp sylbi ) ACDAEZBFZGHZADZBAIZJZUAADZBAKLUEDUFUGPAMUDU
      GBLUEUBLNUCUAAUAUBOQRST $.
  $}

  ${
    $d x A $.  $d x B $.
    bj-ismoored.1 $e |- ( ph -> A e. Moore_ ) $.
    bj-ismoored.2 $e |- ( ph -> B C_ A ) $.
    $( Necessary condition to be a Moore collection.  (Contributed by BJ,
       9-Dec-2021.) $)
    bj-ismoored $p |- ( ph -> ( U. A i^i |^| B ) e. A ) $=
      ( vx cuni cv cint cin wcel cpw wceq inteq ineq2d eleq1d cmoore bj-ismoore
      wral sylib sselpwd rspcdva ) ABGZFHZIZJZBKZUCCIZJZBKFBLZCUDCMZUFUIBUKUEUH
      UCUDCNOPABQKUGFUJSDFBRTACBQDEUAUB $.

    bj-ismoored2.3 $e |- ( ph -> B =/= (/) ) $.
    $( Necessary condition to be a Moore collection.  (Contributed by BJ,
       9-Dec-2021.) $)
    bj-ismoored2 $p |- ( ph -> |^| B e. A ) $=
      ( cuni cint cin wss c0 wne intssuni2 syl2anc sseqin2 bj-ismoored eqeltrrd
      wceq sylib ) ABGZCHZIZUABAUATJZUBUARACBJCKLUCEFCBMNUATOSABCDEPQ $.
  $}

  ${
    $d ph x $.  $d A x $.
    bj-ismooredr.1 $e |- ( ( ph /\ x C_ A ) -> ( U. A i^i |^| x ) e. A ) $.
    $( Sufficient condition to be a Moore collection.  Note that there is no
       sethood hypothesis on ` A ` : it is a consequence of the only
       hypothesis.  (Contributed by BJ, 9-Dec-2021.) $)
    bj-ismooredr $p |- ( ph -> A e. Moore_ ) $=
      ( cuni cv cint cin wcel cpw wral cmoore elpwi ex syl5 ralrimiv bj-ismoore
      wss sylibr ) ACEBFZGHCIZBCJZKCLIAUABUBTUBITCRZAUATCMAUCUADNOPBCQS $.
  $}

  ${
    $d ph x $.  $d A x $.
    bj-ismooredr2.1 $e |- ( ph -> U. A e. A ) $.
    bj-ismooredr2.2 $e |-
                         ( ( ph /\ ( x C_ A /\ x =/= (/) ) ) -> |^| x e. A ) $.
    $( Sufficient condition to be a Moore collection (variant of ~ bj-ismooredr
       singling out the empty intersection).  Note that there is no sethood
       hypothesis on ` A ` : it is a consequence of the first hypothesis.
       (Contributed by BJ, 9-Dec-2021.) $)
    bj-ismooredr2 $p |- ( ph -> A e. Moore_ ) $=
      ( cv wss wa c0 wne cuni cint cin wcel anassrs intssuni2 wceq dfss sylbi
      wi wb incom eqeq2i eleq1 biimpd syl adantll mpd ex wn rint0 eleq1a syl2im
      nne biimtrid adantr pm2.61d bj-ismooredr ) ABCABFZCGZHZUSIJZCKZUSLZMZCNZV
      AVBVFVAVBHVDCNZVFAUTVBVGEOUTVBVGVFTZAUTVBHVDVCGZVHUSCPVIVDVDVCMZQZVHVDVCR
      VKVGVFVKVDVEQVGVFUAVJVEVDVDVCUBUCVDVECUDSUESUFUGUHUIAVBUJZVFTUTVLUSIQZAVF
      USIUNAVCCNVMVEVCQVFDVCUSUKVCCVEULUMUOUPUQUR $.
  $}

  ${
    $d x A $.
    $( The powerclass ` ~P A ` is a Moore collection if and only if ` A ` is a
       set.  It is then called the discrete Moore collection.  (Contributed by
       BJ, 9-Dec-2021.) $)
    bj-discrmoore $p |- ( A e. _V <-> ~P A e. Moore_ ) $=
      ( vx cvv wcel cpw cmoore cuni cv cint cin unipw ineq1i inex1g inss1 elpwd
      wss a1i eqeltrid adantr bj-ismooredr pwexr impbii ) ACDZAEZFDUCBUDUCUDGZB
      HZIZJZUDDUFUDPUCUHAUGJZUDUEAUGAKLUCUIACAUGCMUIAPUCAUGNQORSTAFUAUB $.
  $}

  $( The empty set is not a Moore collection.  (Contributed by BJ,
     9-Dec-2021.) $)
  bj-0nmoore $p |- -. (/) e. Moore_ $=
    ( c0 cmoore wcel cuni noel bj-ismoored0 mto ) ABCADZACHEAFG $.

  ${
    $d x A $.  $d x V $.
    $( A singleton is a Moore collection.  See ~ bj-snmooreb for a
       biconditional version.  (Contributed by BJ, 10-Apr-2024.) $)
    bj-snmoore $p |- ( A e. V -> { A } e. Moore_ ) $=
      ( vx wcel csn cuni unisng snidg eqeltrd cv wss c0 wne wa cint wi wceq cvv
      wn wo df-ne sssn biorf biimpar syl2anb inteq intsng ex syl2im intex elsng
      eqtr wb sylbi biimprd sylan9r syldan ancoms impcom bj-ismooredr2 ) ABDZCA
      EZVAVBFAVBABGABHICJZVBKZVCLMZNVAVCOZVBDZVEVDVAVGPZVEVDVCVBQZVHVEVCLQZSZVJ
      VITZVIVDVCLUAVCAUBVKVIVLVJVIUCUDUEVIVAVFAQZVEVGVIVFVBOZQZVAVNAQZVMVCVBUFA
      BUGVOVPVMVFVNAULUHUIVEVGVMVEVFRDVGVMUMVCUJVFARUKUNUOUPUQURUSUT $.
  $}

  $( A singleton is a Moore collection, biconditional version.  (Contributed by
     BJ, 9-Dec-2021.)  (Proof shortened by BJ, 10-Apr-2024.) $)
  bj-snmooreb $p |- ( A e. _V <-> { A } e. Moore_ ) $=
    ( cvv wcel csn cmoore bj-snmoore wn c0 snprc biimpi bj-0nmoore a1i eqneltrd
    wceq con4i impbii ) ABCZADZECZABFQSQGZRHETRHNAIJHECGTKLMOP $.

  ${
    $d A x $.  $d B x $.  $d V x $.
    $( A pair formed of two nested sets is a Moore collection.  (Note that in
       the statement, if ` B ` is a proper class, we are in the case of
       ~ bj-snmoore ).  A direct consequence is ` |- { (/) , A } e. Moore_ ` .

       More generally, any nonempty well-ordered chain of sets that is a set is
       a Moore collection.

       We also have the biconditional ` |- ( ( A i^i B ) e. V -> `
       ` ( { A , B } e. Moore_ <-> ( A C_ B \/ B C_ A ) ) ) ` .  (Contributed
       by BJ, 11-Apr-2024.) $)
    bj-prmoore $p |- ( ( A e. V /\ A C_ B ) -> { A , B } e. Moore_ ) $=
      ( vx cvv wcel wss wa cmoore wceq syl adantr eqeltrd c0 wo inteq adantl ex
      cint wfal cpr cun pm3.22 adantrr uniprg simprr ssequn1 sylib eqtrd prid2g
      cuni cv wne biid bianass wi intsng sylan9eqr prid1g ad2antrr intprg dfss2
      csn cin bilani 3eqtrd ad3antlr jaod sspr andir eqneqall imp simpl orim12i
      falim bj-jaoi1 sylbi sylanb impel bj-ismooredr2 wn prprc2 eqcomd ad2antrl
      bj-snmoore eqeltrrd pm2.61ian ) BEFZACFZABGZHZABUAZIFWHWKHZDWLWMWLUKZBWLW
      MWNABUBZBWMWIWHHZWNWOJWHWIWPWJWHWIUCZUDABCEUEKWMWJWOBJWHWIWJUFABUGUHUIWHB
      WLFZWKABEUJZLMWMWHWIHZWJHZDULZWLGZXBNUMZHZXBSZWLFZWKWIWJWHWKUNUOXAXBAVCZJ
      ZXBBVCZJZXBWLJZOZOZXGXEXAXIXGXMWTXIXGUPWJWTXIXGWTXIHXFAWLXIWTXFXHSZAXBXHP
      WIXOAJWHACUQQURWTAWLFZXIWIXPWHABCUSZQLMRLXAXKXGXLWTXKXGUPWJWTXKXGWTXKHXFB
      WLXKWTXFXJSZBXBXJPWHXRBJWIBEUQLURWHWRWIXKWSUTMRLXAXLXGXAXLHZXFAWLXSXFWLSZ
      ABVDZAXLXFXTJXAXBWLPQXSWPXTYAJWTWPWJXLWQUTABCEVAKXAYAAJZXLWJYBWTABVBVELVF
      WIXPWHWJXLXQVGMRVHVHXCXBNJZXIOZXMOZXDXNXBABVIYEXDHYDXDHZXMXDHZOXNYDXMXDVJ
      YFXIYGXMYFYCXDHZXIXDHZOZXIYCXIXDVJYJTXIOXIYHTYIXIYCXDTTXBNVKVLXIXDVMVNTXI
      XIVOVPKVQXMXDVMVNVQVRVSVRVTWHWAZWKHZXHWLIYLWIYKHZXHWLJYKWIYMWJYKWIUCUDYMW
      LXHYKWLXHJWIABWBQWCKWIXHIFYKWJACWEWDWFWG $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Maps-to notation for functions with three arguments
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d y x $.  $d y A $.  $d y B $.
    $( The empty set is not an element of a function (given in maps-to
       notation).  (Contributed by BJ, 30-Dec-2020.) $)
    bj-0nelmpt $p |- -. (/) e. ( x e. A |-> B ) $=
      ( vy c0 cv wcel wceq wa copab cmpt 0nelopab df-mpt eqcomi eleq2i mtbi ) E
      AFBGDFCHIZADJZGEABCKZGQADLRSESRADBCMNOP $.
  $}

  ${
    bj-mptval.nf $e |- F/_ x A $.
    $( Value of a function given in maps-to notation.  (Contributed by BJ,
       30-Dec-2020.) $)
    bj-mptval $p |- ( A. x e. A B e. V -> ( X e. A ->
               ( ( ( x e. A |-> B ) ` X ) = Y <-> X ( x e. A |-> B ) Y ) ) ) $=
      ( wcel wral cmpt wfn cfv wceq wbr wb wi fnmptf fnbrfvb ex syl ) CDHABIABC
      JZBKZEBHZEUALFMEFUANOZPABCDGQUBUCUDBEFUARST $.
  $}

$(
${
  bj-mptval2.1 $e |- ( ph -> ( x = <. X , Y >. -> B = C ) ) $.
  @( Value of a function given in maps-to notation.  (Contributed by BJ,
     30-Dec-2020.) @)
    bj-mptval2 $p |- ( ph -> ( X ( x e. A |-> B ) Y ) = C ) $=
     ? $.
$}
$)

  ${
    $d x y s t $.  $d s t A $.  $d s t B $.  $d s t C $.  $d y A $.
    $( An equivalent definition of ~ df-mpo .  (Contributed by BJ,
       30-Dec-2020.) $)
    bj-dfmpoa $p |- ( x e. A , y e. B |-> C ) = { <. s , t >. |
                          E. x e. A E. y e. B ( s = <. x , y >. /\ t = C ) } $=
      ( cmpo cv wcel wa wceq coprab cop wex copab wrex 3bitr2i exbii df-rex
      df-mpo dfoprab2 ancom anbi2i anass an13 r19.42v bitr4i opabbii 3eqtri ) A
      BDEFHAIZDJZBIZEJZKZCIFLZKZABCMGIUKUMNLZUQKZBOZAOZGCPURUPKZBEQZADQZGCPABCD
      EFUAUQABCGUBVAVDGCVAULVCKZAOVDUTVEAUTUNULVBKZKZBOVFBEQVEUSVGBUSURUPUOKZKV
      BUOKVGUQVHURUOUPUCUDURUPUOUEVBULUNUFRSVFBETULVBBEUGRSVCADTUHUIUJ $.
  $}

  ${
    $d x y z t A $.  $d x y z t B $.  $d x y t C $.  $d z t D $.
    bj-mpomptALT.1 $e |- ( z = <. x , y >. -> C = D ) $.
    $( Alternate proof of ~ mpompt .  (Contributed by BJ, 30-Dec-2020.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    bj-mpomptALT $p |- ( z e. ( A X. B ) |-> C ) = ( x e. A , y e. B |-> D ) $=
      ( vt cv cxp wcel wceq wa copab cop wrex cmpt r19.41v rexbii anbi1i eqeq2d
      cmpo elxp2 pm5.32i bitr3i 3bitr2i opabbii df-mpt bj-dfmpoa 3eqtr4i ) CJZD
      EKZLZIJZFMZNZCIOULAJBJPMZUOGMZNZBEQZADQZCIOCUMFRABDEGUCUQVBCIUQURBEQZADQZ
      UPNVCUPNZADQVBUNVDUPABULDEUDUAVCUPADSVEVAADVEURUPNZBEQVAURUPBESVFUTBEURUP
      USURFGUOHUBUETUFTUGUHCIUMFUIABIDEGCUJUK $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Currying
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  Currying and uncurrying.  See also ~ df-cur and ~ df-unc .  Contrary to
  these, the definitions in this section are parameterized.

$)

  $( Token for the set of set morphisms. $)
  $c -Set-> $.

  $( Syntax for the set of set morphisms. $)
  csethom $a class -Set-> $.

  ${
    $d f x y $.
    $( Define the set of functions (morphisms of sets) between two sets.  Same
       as ~ df-map with arguments swapped.  TODO: prove the same staple lemmas
       as for ` ^m ` .

       Remark: one may define
       ` -Set-> = ( x e. dom Struct , y e. dom Struct |-> `
       ` { f | f : ( Base `` x ) --> ( Base `` y ) } ) ` so that for morphisms
       between other structures, one could write
       ` ... = { f e. ( x -Set-> y ) | ... } ` .

       (Contributed by BJ, 11-Apr-2020.) $)
    df-bj-sethom $a |-
                      -Set-> = ( x e. _V , y e. _V |-> { f | f : x --> y } ) $.
  $}

  $( Token for the set of topological morphisms. $)
  $c -Top-> $.

  $( Syntax for the set of topological morphisms. $)
  ctophom $a class -Top-> $.

  ${
    $d f x y u $.
    $( Define the set of continuous functions (morphisms of topological spaces)
       between two topological spaces.  Similar to ~ df-cn (which is in terms
       of topologies instead of topological spaces).  (Contributed by BJ,
       10-Feb-2022.) $)
    df-bj-tophom $a |- -Top-> = ( x e. TopSp , y e. TopSp |->
                     { f e. ( ( Base ` x ) -Set-> ( Base ` y ) ) |
                 A. u e. ( TopOpen ` y ) ( `' f " u ) e. ( TopOpen ` x ) } ) $.
  $}

  $( Token for the set of magma morphisms. $)
  $c -Mgm-> $.

  $( Syntax for the set of magma morphisms. $)
  cmgmhom $a class -Mgm-> $.

  ${
    $d f x y u v $.
    $( Define the set of magma morphisms between two magmas.  If domain and
       codomain are semigroups, monoids, or groups, then one obtains the set of
       morphisms of these structures.  (Contributed by BJ, 10-Feb-2022.) $)
    df-bj-mgmhom $a |- -Mgm-> = ( x e. Mgm , y e. Mgm |->
                     { f e. ( ( Base ` x ) -Set-> ( Base ` y ) ) |
                       A. u e. ( Base ` x ) A. v e. ( Base ` x )
         ( f ` ( u ( +g ` x ) v ) ) = ( ( f ` u ) ( +g ` y ) ( f ` v ) ) } ) $.
  $}

  $( Token for the set of topological magma morphisms. $)
  $c -TopMgm-> $.

  $( Syntax for the set of topological magma morphisms. $)
  ctopmgmhom $a class -TopMgm-> $.

  ${
    $d x y $.
    $( Define the set of topological magma morphisms (continuous magma
       morphisms) between two topological magmas.  If domain and codomain are
       topological semigroups, monoids, or groups, then one obtains the set of
       morphisms of these structures.  This definition is currently stated with
       topological monoid domain and codomain, since topological magmas are
       currently not defined in set.mm.  (Contributed by BJ, 10-Feb-2022.) $)
    df-bj-topmgmhom $a |- -TopMgm-> =
     ( x e. TopMnd , y e. TopMnd |-> ( ( x -Top-> y ) i^i ( x -Mgm-> y ) ) ) $.
  $}

  $( Token for the parameterized currying function. $)
  $c curry_ $.

  $( Syntax for the parameterized currying function. $)
  ccur- $a class curry_ $.

  ${
    $d x y z a b f $.
    $( Define currying.  See also ~ df-cur .  (Contributed by BJ,
       11-Apr-2020.) $)
    df-bj-cur $a |- curry_ = ( x e. _V , y e. _V , z e. _V |->
                     ( f e. ( ( x X. y ) -Set-> z ) |->
                       ( a e. x |-> ( b e. y |-> ( f ` <. a , b >. ) ) ) ) ) $.
  $}

  $( Token for the parameterized uncurrying function. $)
  $c uncurry_ $.

  $( Notation for the parameterized uncurrying function. $)
  cunc- $a class uncurry_ $.

  ${
    $d x y z a b f $.
    $( Define uncurrying.  See also ~ df-unc .  (Contributed by BJ,
       11-Apr-2020.) $)
    df-bj-unc $a |- uncurry_ = ( x e. _V , y e. _V , z e. _V |->
                             ( f e. ( x -Set-> ( y -Set-> z ) ) |->
                               ( a e. x , b e. y |-> ( ( f ` a ) ` b ) ) ) ) $.
  $}

$(
  ${
    bj-curval.x $e |- ( ph -> X e. U ) $.
    bj-curval.y $e |- ( ph -> Y e. V ) $.
    bj-curval.z $e |- ( ph -> Z e. W ) $.
    @( Value of the currying function.  (Contributed by BJ, 30-Dec-2020.) @)
    bj-curval $p |- ( ph -> ( curry_ ` <. X , Y , Z >. ) =
                   ( f e. ( ( X X. Y ) -Set-> Z ) |->
                     ( a e. X |-> ( b e. Y |-> ( f ` <. a , b >. ) ) ) ) ) $=
      (  ) ? $.

    @( Property of currying.  (Contributed by BJ, 30-Dec-2020.) @)
    bj-cur $p |- ( ph -> ( curry_ ` <. X , Y , Z >. ) e.
            ( ( ( X X. Y ) -Set-> Z ) -Set-> ( X -Set-> ( Y -Set-> Z ) ) ) ) $=
      (  ) ? $.
$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Setting components of extensible structures
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  Groundwork for changing the definition, syntax and token for
  component-setting in extensible structures.  See
  ~ https://github.com/metamath/set.mm/issues/2401

$)

  $( Tokens for component-setting in extensible structures $)
  $c [s ]s $.

  $( Syntax for component-setting in extensible structures. $)
  cstrset $a class [s B / A ]s S $.

  $( Component-setting in extensible structures.  Define the extensible
     structure ` [s B / A ]s S ` , which is like the extensible structure ` S `
     except that the value ` B ` has been put in the slot ` A ` (replacing the
     current value if there was already one).  In such expressions, ` A ` is
     generally substituted for slot mnemonics like ` Base ` or ` +g ` or
     ` dist ` .  The ` _V ` in this definition was chosen to be closer to
     ~ df-sets , but since extensible structures are functions on ` NN ` , it
     will be more natural to replace it with ` NN ` when ~ df-strset becomes
     the main definition.  (Contributed by BJ, 13-Feb-2022.) $)
  df-strset $a |- [s B / A ]s S =
          ( ( S |` ( _V \ { ( A ` ndx ) } ) ) u. { <. ( A ` ndx ) , B >. } ) $.

  $( Relation between ~ df-sets and ~ df-strset .  Temporary theorem kept
     during the transition from the former to the latter.  (Contributed by BJ,
     13-Feb-2022.) $)
  setsstrset $p |- ( ( S e. V /\ B e. W ) ->
                          [s B / A ]s S = ( S sSet <. ( A ` ndx ) , B >. ) ) $=
    ( wcel wa cstrset cvv cnx cfv csn cdif cres cop cun csts df-strset setsval
    co eqtr4id ) CDFBEFGABCHCIJAKZLMNUBBOZLPCUCQTABCRUBBCDESUA $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Extended real and complex numbers, real and complex projective lines
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  In this section, we indroduce several supersets of the set ` RR ` of real
  numbers and the set ` CC ` of complex numbers.

  Once they are given their usual topologies, which are locally compact, both
  topological spaces have a one-point compactification.  They are denoted by
  ` RRhat ` and ` CChat ` respectively, defined in ~ df-bj-cchat and
  ~ df-bj-rrhat , and the point at infinity is denoted by ` infty ` , defined
  in ~ df-bj-infty .

  Both  ` RR ` and ` CC ` also have "directional compactifications", denoted
  respectively by ` RRbar ` , defined in ~ df-bj-rrbar (already defined as
  ` RR* ` , see ~ df-xr ) and ` CCbar ` , defined in ~ df-bj-ccbar .

  Since ` CCbar ` does not seem to be standard, we describe it in some detail.
  It is obtained by adding to ` CC ` a "point at infinity at the end of each
  ray with origin at 0".  Although ` CCbar ` is not an important object in
  itself, the motivation for introducing it is to provide a common superset to
  both ` RRbar ` and ` CC ` and to define algebraic operations (addition,
  opposite, multiplication, inverse) as widely as reasonably possible.

  Mathematically, ` CCbar ` is the quotient of
  ` ( ( CC X. RR>=0 ) \ { <. 0 , 0 >. } ) `
  by the diagonal multiplicative action of ` RR>0 ` (think of the closed
  "northern hemisphere" in ` RR `^3 identified with ` ( CC X. RR ) ` , that
  each open ray from 0 included in the closed northern half-space intersects
  exactly once).

  Since in set.mm, we want to have a genuine inclusion ` CC C_ CCbar ` , we
  instead define ` CCbar ` as the (disjoint) union of ` CC ` with a circle at
  infinity denoted by ` CCinfty ` .  To have a genuine inclusion
  ` RRbar C_ CCbar ` , we define ` pinfty ` and ` minfty ` as certain points in
  ` CCinfty ` .

  Thanks to this framework, one has the genuine inclusions
  ` RR C_ RRbar ` and ` RR C_ RRhat ` and similarly
  ` CC C_ CCbar ` and ` CC C_ CChat `.
  Furthermore, one has ` RR C_ CC ` as well as ` RRbar C_ CCbar ` and
  ` RRhat C_ CChat `.

  Furthermore, we define the main algebraic operations on
  ` ( CCbar u. CChat ) ` , which is not very mathematical, but "overloads" the
  operations, so that one can use the same notation in all cases.

$)

  $( Token for the nonnegative reals (currently only for comment
     typesetting). $)
  $c RR>=0 $.

  $( Token for the (strictly) positive reals (currently only for comment
     typesetting). $)
  $c RR>0 $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Complements on class abstractions of ordered pairs and binary relations
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    bj-nfald.1 $e |- ( ph -> A. y ph ) $.
    bj-nfald.2 $e |- ( ph -> F/ x ps ) $.
    $( Variant of ~ nfald .  (Contributed by BJ, 25-Dec-2023.) $)
    bj-nfald $p |- ( ph -> F/ x A. y ps ) $=
      ( wal wex 19.12 nfrd alimdh ax-11 syl56 nfd ) ABDGZCOCHBCHZDGABCGZDGOCGBC
      DIAPQDEABCFJKBDCLMN $.

    $( Variant of ~ nfexd .  (Contributed by BJ, 25-Dec-2023.) $)
    bj-nfexd $p |- ( ph -> F/ x E. y ps ) $=
      ( wex wn wal df-ex nfnd bj-nfald nfxfrd ) BDGBHZDIZHACBDJAOCANCDEABCFKLKM
      $.
  $}

  ${
    $d ph x y $.  $d th x y $.  $d A x y $.  $d B x y $.
    cgsex2gd.is $e |- ( ( ph /\ ( x = A /\ y = B ) ) -> ps ) $.
    cgsex2gd.maj $e |- ( ( ph /\ ps ) -> ( ch <-> th ) ) $.
    $( Implicit substitution inference for general classes.  (Contributed by
       NM, 26-Jul-1995.)  Adapt ~ cgsex2g to deduction form.  (Revised by BJ,
       28-Mar-2026.)  Do not use ~ cgsex2g .
       (Proof modification is discouraged.) $)
    cgsex2gd $p |- ( ( ph /\ ( A e. V /\ B e. W ) ) ->
                                         ( E. x E. y ( ps /\ ch ) <-> th ) ) $=
      ( wcel wa wex wi adantr cv wceq 2eximdv biimp3a 3expib ex elisset anim12i
      exlimdvv exdistrv sylibr impel biimprd impancom expimpd mpan2d impbid
      ancld ) AGIMZHJMZNZNZBCNZFOEOZDAVADPURAUTDEFABCDABCDLUAUBUFQUSDBFOEOZVAAE
      RGSZFRHSZNZFOEOZVBURAVEBEFAVEBKUCTURVCEOZVDFOZNVFUPVGUQVHEGIUDFHJUDUEVCVD
      EFUGUHUIADVBNVAPURADVBVAADNZBUTEFVIBCABDCABNCDLUJUKUOTULQUMUN $.
  $}

  ${
    $d x y ph $.  $d x y ch $.  $d x y A $.  $d x y B $.
    copsex2gd.is $e |- ( ( ph /\ ( x = A /\ y = B ) ) -> ( ps <-> ch ) ) $.
    $( Implicit substitution inference for ordered pairs.  (Contributed by NM,
       28-May-1995.)  Use a similar proof to ~ copsex4g to reduce axiom usage.
       (Revised by SN, 1-Sep-2024.)  Adapt ~ copsex2g $p to deduction form.
       (Revised by BJ, 28-Mar-2026.)  Do not use ~ copsex2g .
       (Proof modification is discouraged.) $)
    copsex2gd $p |- ( ( ph /\ ( A e. V /\ B e. W ) ) ->
                  ( E. x E. y ( <. A , B >. = <. x , y >. /\ ps ) <-> ch ) ) $=
      ( cop cv wceq wa wex wcel eqcom vex opth bitri anbi1i 2exbii simpr bitrid
      cgsex2gd ) FGKZDLZELZKZMZBNZEODOUGFMUHGMNZBNZEODOAFHPGIPNNCUKUMDEUJULBUJU
      IUFMULUFUIQUGUHFGDRERSTUAUBAULBCDEFGHIAULUCJUEUD $.
  $}

  ${
    $d A x y $.  $d B x y $.
    copsex2d.xph $e |- ( ph -> A. x ph ) $.
    copsex2d.yph $e |- ( ph -> A. y ph ) $.
    copsex2d.xch $e |- ( ph -> F/ x ch ) $.
    copsex2d.ych $e |- ( ph -> F/ y ch ) $.
    copsex2d.exa $e |- ( ph -> A e. U ) $.
    copsex2d.exb $e |- ( ph -> B e. V ) $.
    copsex2d.is $e |- ( ( ph /\ ( x = A /\ y = B ) ) -> ( ps <-> ch ) ) $.
    $( Implicit substitution deduction for ordered pairs.  (Contributed by BJ,
       25-Dec-2023.) $)
    copsex2d $p |- ( ph ->
                  ( E. x E. y ( <. A , B >. = <. x , y >. /\ ps ) <-> ch ) ) $=
      ( wceq wex wa syl cv cop wb wcel elisset exdistrv wnf nfe1 nfbid bj-nfexd
      a1i 19.9d opeq12 copsexgw bicomd eqcoms adantl bj-exlimd biimtrrid mp2and
      bitrd ex ) ADUAZFQZDRZEUAZGQZERZFGUBZVCVFUBZQZBSZERZDRZCUCZAFHUDVENDFHUET
      AGIUDVHOEGIUETVEVHSVDVGSZERZDRAVOVDVGDEUFAAVQVOVODJVOADAVNCDVNDUGAVMDUHUK
      LUIULAAVPVOVOEKVOAEAVNCEAVMEDJVMEUGAVLEUHUKUJMUIULAVPVOAVPSVNBCVPVNBUCZAV
      PVJVIQVRVCVFFGUMVRVIVJVKBVNBDEVIUNUOUPTUQPVAVBURURUSUT $.
  $}

  ${
    $d A x y $.  $d B x y $.
    copsex2b.xph $e |- ( ph -> A. x ph ) $.
    copsex2b.yph $e |- ( ph -> A. y ph ) $.
    copsex2b.xch $e |- ( ph -> F/ x ch ) $.
    copsex2b.ych $e |- ( ph -> F/ y ch ) $.
    copsex2b.is $e |- ( ( ph /\ ( x = A /\ y = B ) ) -> ( ps <-> ch ) ) $.
    $( Biconditional form of ~ copsex2d .  TODO: prove a relative version, that
       is, with ` E. x e. V E. y e. W ... ( A e. V /\ B e. W ) ` .
       (Contributed by BJ, 27-Dec-2023.) $)
    copsex2b $p |- ( ph -> ( E. x E. y ( <. A , B >. = <. x , y >. /\ ps ) <->
                                        ( ( A e. _V /\ B e. _V ) /\ ch ) ) ) $=
      ( cop cv wceq wa wex cvv wcel adantr eqcom opth eqvisset anim12i exlimivv
      vex bitri sylbi anim2i simpl ax-5 hban wnf simprl simprr adantlr copsex2d
      wb ibar adantl bitrd pm5.21nd ) AFGMZDNZENZMZOZBPZEQDQZFRSZGRSZPZCPZAVLPZ
      VIVLAVHVLDEVGVLBVGVDFOZVEGOZPZVLVGVFVCOVQVCVFUAVDVEFGDUFEUFUBUGVOVJVPVKDF
      UCEGUCUDUHTUEUIVMVLAVLCUJUIVNVICVMVNBCDEFGRRAVLDHVLDUKULAVLEIVLEUKULACDUM
      VLJTACEUMVLKTAVJVKUNAVJVKUOAVQBCURVLLUPUQVLCVMURAVLCUSUTVAVB $.
  $}

  ${
    $d A x y $.  $d B x y $.
    opelopabd.xph $e |- ( ph -> A. x ph ) $.
    opelopabd.yph $e |- ( ph -> A. y ph ) $.
    opelopabd.xch $e |- ( ph -> F/ x ch ) $.
    opelopabd.ych $e |- ( ph -> F/ y ch ) $.
    opelopabd.exa $e |- ( ph -> A e. U ) $.
    opelopabd.exb $e |- ( ph -> B e. V ) $.
    opelopabd.is $e |- ( ( ph /\ ( x = A /\ y = B ) ) -> ( ps <-> ch ) ) $.
    $( Membership of an ordered pair in a class abstraction of ordered pairs.
       (Contributed by BJ, 17-Dec-2023.) $)
    opelopabd $p |- ( ph -> ( <. A , B >. e. { <. x , y >. | ps } <-> ch ) ) $=
      ( cop copab cv wex wcel wceq wa elopab copsex2d bitrid ) FGQZBDERUAUGDSES
      QUBBUCETDTACBDEUGUDABCDEFGHIJKLMNOPUEUF $.
  $}

  ${
    $d A x y $.  $d B x y $.
    opelopabb.xph $e |- ( ph -> A. x ph ) $.
    opelopabb.yph $e |- ( ph -> A. y ph ) $.
    opelopabb.xch $e |- ( ph -> F/ x ch ) $.
    opelopabb.ych $e |- ( ph -> F/ y ch ) $.
    opelopabb.is $e |- ( ( ph /\ ( x = A /\ y = B ) ) -> ( ps <-> ch ) ) $.
    $( Membership of an ordered pair in a class abstraction of ordered pairs,
       biconditional form.  (Contributed by BJ, 17-Dec-2023.) $)
    opelopabb $p |- ( ph -> ( <. A , B >. e. { <. x , y >. | ps } <->
                                        ( ( A e. _V /\ B e. _V ) /\ ch ) ) ) $=
      ( cop copab wcel cv wceq wa wex cvv elopab copsex2b bitrid ) FGMZBDENOUDD
      PEPMQBRESDSAFTOGTORCRBDEUDUAABCDEFGHIJKLUBUC $.
  $}

  ${
    $d A x y $.  $d B x y $.  $d ph x y $.  $d ch x y $.
    opelopabbv.def $e |- ( ph -> R = { <. x , y >. | ps } ) $.
    opelopabbv.is $e |- ( ( ph /\ ( x = A /\ y = B ) ) -> ( ps <-> ch ) ) $.
    $( Membership of an ordered pair in a class abstraction of ordered pairs,
       biconditional form.  (Contributed by BJ, 17-Dec-2023.) $)
    opelopabbv $p |- ( ph -> ( <. A , B >. e. R <->
                                        ( ( A e. _V /\ B e. _V ) /\ ch ) ) ) $=
      ( cop wcel copab cvv wa eleq2d ax-5 nfvd opelopabb bitrd ) AFGKZHLUABDEMZ
      LFNLGNLOCOAHUBUAIPABCDEFGADQAEQACDRACERJST $.
  $}

  $( The coordinates of an ordered pair that belongs to a relation are sets.
     TODO:  Slightly shorter than ~ brrelex12 , which could be proved from it.
     (Contributed by BJ, 27-Dec-2023.) $)
  bj-opelrelex $p |-
                 ( ( Rel R /\ <. A , B >. e. R ) -> ( A e. _V /\ B e. _V ) ) $=
    ( wrel cop wcel wa cvv cxp wss df-rel biimpi sselda opelxp sylib ) CDZABEZC
    FGQHHIZFAHFBHFGPCRQPCRJCKLMABHHNO $.

  $( If an ordered pair is in a restricted binary relation, then its first
     component is an element of the restricting class.  See also ~ opelres .
     (Contributed by BJ, 25-Dec-2023.) $)
  bj-opelresdm $p |- ( <. A , B >. e. ( R |` X ) -> A e. X ) $=
    ( wcel cop cvv cxp cin cres elin opelxp1 simplbiim df-res eleq2s ) ADEZABFZ
    CDGHZIZCDJQSEQCEQREPQCRKABDGLMCDNO $.

  $( If two classes are related by a restricted binary relation, then the first
     class is an element of the restricting class.  See also ~ brres and
     ~ brrelex1 .

     Remark: there are many pairs like ~ bj-opelresdm / ~ bj-brresdm , where
     one uses membership of ordered pairs and the other, related classes (for
     instance, ~ bj-opelresdm / ~ brrelex12 or the ~ opelopabg / ~ brabg
     family).  They are straightforwardly equivalent by ~ df-br .  The latter
     is indeed a very direct definition, introducing a "shorthand", and barely
     necessary, were it not for the frequency of the expression ` A R B ` .
     Therefore, in the spirit of "definitions are here to be used", most
     theorems, apart from the most elementary ones, should only have the "br"
     version, not the "opel" one.  (Contributed by BJ, 25-Dec-2023.) $)
  bj-brresdm $p |- ( A ( R |` X ) B -> A e. X ) $=
    ( cres wbr cop wcel df-br bj-opelresdm sylbi ) ABCDEZFABGLHADHABLIABCDJK $.

  ${
    $d A x y $.  $d B x y $.
    brabd0.x $e |- ( ph -> A. x ph ) $.
    brabd0.y $e |- ( ph -> A. y ph ) $.
    brabd0.xch $e |- ( ph -> F/ x ch ) $.
    brabd0.ych $e |- ( ph -> F/ y ch ) $.
    brabd0.exa $e |- ( ph -> A e. U ) $.
    brabd0.exb $e |- ( ph -> B e. V ) $.
    brabd0.def $e |- ( ph -> R = { <. x , y >. | ps } ) $.
    brabd0.is $e |- ( ( ph /\ ( x = A /\ y = B ) ) -> ( ps <-> ch ) ) $.
    $( Expressing that two sets are related by a binary relation which is
       expressed as a class abstraction of ordered pairs.  (Contributed by BJ,
       17-Dec-2023.) $)
    brabd0 $p |- ( ph -> ( A R B <-> ch ) ) $=
      ( wbr wcel cop copab df-br eleq2d bitrid opelopabd bitrd ) AFGHSZFGUAZBDE
      UBZTZCUHUIHTAUKFGHUCAHUJUIQUDUEABCDEFGIJKLMNOPRUFUG $.
  $}

  ${
    $d A x y $.  $d B x y $.  $d ph x y $.  $d ch x y $.
    brabd.exa $e |- ( ph -> A e. U ) $.
    brabd.exb $e |- ( ph -> B e. V ) $.
    brabd.def $e |- ( ph -> R = { <. x , y >. | ps } ) $.
    brabd.is $e |- ( ( ph /\ ( x = A /\ y = B ) ) -> ( ps <-> ch ) ) $.
    $( Expressing that two sets are related by a binary relation which is
       expressed as a class abstraction of ordered pairs.  (Contributed by BJ,
       17-Dec-2023.) $)
    brabd $p |- ( ph -> ( A R B <-> ch ) ) $=
      ( ax-5 nfvd brabd0 ) ABCDEFGHIJADOAEOACDPACEPKLMNQ $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x y ps $.
    bj-brab2a1.1 $e |- ( ( x = A /\ y = B ) -> ( ph <-> ps ) ) $.
    bj-brab2a1.2 $e |- R = { <. x , y >. | ph } $.
    $( "Unbounded" version of ~ brab2a .  (Contributed by BJ, 25-Dec-2023.) $)
    bj-brab2a1 $p |- ( A R B <-> ( ( A e. _V /\ B e. _V ) /\ ps ) ) $=
      ( cvv copab cv wcel wa vex pm3.2i biantrur opabbii eqtri brab2a ) ABCDEFJ
      JGHGACDKCLJMZDLJMZNZANZCDKIAUDCDUCAUAUBCODOPQRST $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Identity relation (complements)
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  Complements on the identity relation.

$)

  ${
    $d x y $.
    $( A variant of ~ relopabiv (which could be proved from it, similarly to
       ~ relxp from ~ xpss ).  (Contributed by BJ, 28-Dec-2023.) $)
    bj-opabssvv $p |- { <. x , y >. | ph } C_ ( _V X. _V ) $=
      ( copab cv cvv wcel wa cxp vex pm3.2i a1i ssopab2i df-xp sseqtrri ) ABCDB
      EFGZCEFGZHZBCDFFIARBCRAPQBJCJKLMBCFFNO $.
  $}

  $( The restricted identity relation is a function.  (Contributed by BJ,
     27-Dec-2023.)

     TODO: relabel ~ funi to funid. $)
  bj-funidres $p |- Fun ( _I |` V ) $=
    ( cid wfun cres funi funres ax-mp ) BCBADCEABFG $.

  ${
    $d A x y $.  $d B x y $.
    $( Characterization of the ordered pair elements of the identity relation.

       Remark: in deduction-style proofs, one could save a few syntactic steps
       by using another antecedent than ` T. ` which already appears in the
       proof.  Here for instance this could be the definition
       ` _I = { <. x , y >. | x = y } ` but this would make the proof less easy
       to read.  (Contributed by BJ, 27-Dec-2023.) $)
    bj-opelidb $p |-
               ( <. A , B >. e. _I <-> ( ( A e. _V /\ B e. _V ) /\ A = B ) ) $=
      ( vx vy cop cid wcel cvv wa wceq wb wtru weq copab df-id cv eqeq12 adantl
      a1i opelopabbv mptru ) ABEFGAHGBHGIABJZIKLCDMZUBCDABFFUCCDNJLCDOSCPZAJDPZ
      BJIUCUBKLUDAUEBQRTUA $.
  $}

  $( Characterization of the ordered pair elements of the identity relation.
     Variant of ~ bj-opelidb where only the sethood of the first component is
     expressed.  (Contributed by BJ, 27-Dec-2023.) $)
  bj-opelidb1 $p |- ( <. A , B >. e. _I <-> ( A e. _V /\ A = B ) ) $=
    ( cvv wcel wa wceq cop cid an32 bj-opelidb eleq1 biimpac pm4.71i 3bitr4i )
    ACDZBCDZEABFZEOQEZPEABGHDROPQIABJRPQOPABCKLMN $.

  $( Lemma for ~ bj-opelid (but not specific to the identity relation): if the
     intersection of two classes is a set and the two classes are equal, then
     both are sets (all three classes are equal, so they all belong to ` V ` ,
     but it is more convenient to have ` _V ` in the consequent for theorems
     using it).  (Contributed by BJ, 27-Dec-2023.) $)
  bj-inexeqex $p |-
                 ( ( ( A i^i B ) e. V /\ A = B ) -> ( A e. _V /\ B e. _V ) ) $=
    ( cin wcel wa cvv wss eqimss dfss2 sylib eleq1 biimpac sylan2 elexd eqimss2
    wceq sseqin2 jca ) ABDZCEZABQZFZAGEBGEUCACUBUATAQZACEZUBABHUDABIABJKUDUAUET
    ACLMNOUCBCUBUATBQZBCEZUBBAHUFBAPBARKUFUAUGTBCLMNOS $.

  $( If the intersection of two classes is a set, then these classes are equal
     if and only if one is an element of the singleton formed on the other.
     Stronger form of ~ elsng and ~ elsn2g (which could be proved from it).
     (Contributed by BJ, 20-Jan-2024.) $)
  bj-elsn0 $p |- ( ( A i^i B ) e. V -> ( A e. { B } <-> A = B ) ) $=
    ( cin wcel csn wceq elsni wi wa cvv bj-inexeqex simpl elsng biimprd 3syl ex
    pm2.43d impbid2 ) ABDCEZABFEZABGZABHTUBUATUBUBUAIZTUBJAKEZBKEZJUDUCABCLUDUE
    MUDUAUBABKNOPQRS $.

  $( Characterization of the ordered pair elements of the identity relation
     when the intersection of their components are sets.  Note that the
     antecedent is more general than either component being a set.
     (Contributed by BJ, 29-Mar-2020.) $)
  bj-opelid $p |- ( ( A i^i B ) e. V -> ( <. A , B >. e. _I <-> A = B ) ) $=
    ( cin wcel wceq cvv wa wi cop cid wb bj-inexeqex ex bj-opelidb ancr impbid2
    simpr bitrid syl ) ABDCEZABFZAGEBGEHZIZABJKEZUBLUAUBUCABCMNUEUCUBHZUDUBABOU
    DUFUBUCUBRUBUCPQST $.

  $( Characterization of the classes related by the identity relation when
     their intersection is a set.  Note that the antecedent is more general
     than either class being a set.  (Contributed by NM, 30-Apr-2004.)  Weaken
     the antecedent to sethood of the intersection.  (Revised by BJ,
     24-Dec-2023.)

     TODO: replace ~ ideqg , or at least prove ~ ideqg from it. $)
  bj-ideqg $p |- ( ( A i^i B ) e. V -> ( A _I B <-> A = B ) ) $=
    ( cid wbr cop wcel cin wceq df-br bj-opelid bitrid ) ABDEABFDGABHCGABIABDJA
    BCKL $.

  ${
    $d x y A $.  $d x y B $.
    $( Alternate proof of ~ bj-ideqg from ~ brabga instead of ~ bj-opelid
       itself proved from ~ bj-opelidb .  (Contributed by BJ, 27-Dec-2023.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    bj-ideqgALT $p |- ( ( A i^i B ) e. V -> ( A _I B <-> A = B ) ) $=
      ( vx vy cin wcel cid wbr wceq cvv wa brrelex12i adantl bj-inexeqex weq cv
      reli eqeq12 df-id brabga pm5.21nd ) ABFCGZABHIZABJZAKGBKGLZUDUFUCABHRMNAB
      CODEPUEDEABHKKDQAEQBSDETUAUB $.
  $}

  $( Characterization of classes related by the identity relation.
     (Contributed by BJ, 24-Dec-2023.) $)
  bj-ideqb $p |- ( A _I B <-> ( A e. _V /\ A = B ) ) $=
    ( cid wbr cvv wcel wceq reli brrelex1i cin wb inex1g bj-ideqg syl biadanii
    ) ABCDZAEFZABGZABCHIQABJEFPRKABELABEMNO $.

  ${
    $d A x y $.
    $( Alternate expression for the restricted identity relation.  The
       advantage of that expression is to expose it as a "bounded" class, being
       included in the Cartesian square of the restricting class.  (Contributed
       by BJ, 27-Dec-2023.)

       This is an alternate of ~ idinxpresid (see ~ idinxpres ).  See also
       ~ elrid and ~ elidinxp .  (Proof modification is discouraged.) $)
    bj-idres $p |- ( _I |` A ) = ( _I i^i ( A X. A ) ) $=
      ( vx vy cid cres cvv cxp cin df-res inss1 relinxp cv cop wcel wa elin weq
      bj-opelidb1 simprbi wss opelxp1 simpr eleq1w biimpa jca sylbi opelxpi syl
      syl2an relssi ssini ssv xpss2 sslin mp2b eqssi eqtri ) DAEDAFGZHZDAAGZHZD
      AIUSVAUSDUTDURJBCUSUTAFDKBLZCLZMZUSNZVBANZVCANZOZVDUTNVEVDDNZVDURNZOVHVDD
      URPVIBCQZVFVHVJVIVBFNVKVBVCRSVBVCAFUAVKVFOVFVGVKVFUBVKVFVGBCAUCUDUEUIUFVB
      VCAAUGUHUJUKAFTUTURTVAUSTAULAFAUMUTURDUNUOUPUQ $.
  $}

  $( Characterization of the ordered pairs in the restricted identity relation
     when the intersection of their component belongs to the restricting class.
     TODO: prove ~ bj-idreseq from it.  (Contributed by BJ, 29-Mar-2020.) $)
  bj-opelidres $p |- ( A e. V -> ( <. A , B >. e. ( _I |` V ) <-> A = B ) ) $=
    ( cop cid cres wcel cxp cin wceq bj-idres eleq2i wa cvv wb inex1g bj-opelid
    elin syl bitrid opelxp a1i anbi12d simpl eleq1 biimpcd anc2li ancld impbid2
    bitrd ) ABDZECFZGUKECCHZIZGZACGZABJZULUNUKCKLUOUKEGZUKUMGZMZUPUQUKEUMRUPUTU
    QUPBCGZMZMZUQUPURUQUSVBUPABINGURUQOABCPABNQSUSVBOUPABCCUAUBUCUPVCUQUQVBUDUP
    UQVBUPUQVAUQUPVAABCUEUFUGUHUIUJTT $.

  ${
    $d x y A $.  $d x y B $.
    $( Sufficient condition for the restricted identity relation to agree with
       equality.  Note that the instance of ~ bj-ideqg with ` _V ` substituted
       for ` V ` is a direct consequence of ~ bj-idreseq .  This is a
       strengthening of ~ resieq which should be proved from it (note that
       currently, ~ resieq relies on ~ ideq ).  Note that the intersection in
       the antecedent is not very meaningful, but is a device to prove versions
       with either class assumed to be a set.  It could be enough to prove the
       version with a disjunctive antecedent:
       ` |- ( ( A e. C \/ B e. C ) -> ... ) ` .  (Contributed by BJ,
       25-Dec-2023.) $)
    bj-idreseq $p |- ( ( A i^i B ) e. C -> ( A ( _I |` C ) B <-> A = B ) ) $=
      ( vx vy cin wcel cid cres wbr wceq cvv wa bj-brresdm jca adantl wss sylib
      eqeltrrd cv relres brrelex2i eqimss dfss2 simpl eqimss2 sseqin2 elexd weq
      brres eqeq12 df-id brabga anbi2d simp3 3expib 3simpb 3expia impbid 3bitrd
      wb pm5.21nd ) ABFZCGZABHCIZJZABKZACGZBLGZMZVFVJVDVFVHVIABHCNABVEHCUAUBOPV
      DVGMZVHVIVKVCACVGVCAKZVDVGABQVLABUCABUDRPVDVGUEZSVKBCVKVCBCVGVCBKZVDVGBAQ
      VNBAUFBAUGRPVMSUHOVJVFVHABHJZMZVHVGMZVGVIVFVPVAVHCABHLUJPVJVOVGVHDEUIVGDE
      ABHCLDTAETBUKDEULUMUNVJVQVGVJVHVGVGVJVHVGUOUPVHVIVGVQVHVIVGUQURUSUTVB $.
  $}

  ${
    $d x y A $.  $d x y B $.
    $( Characterization for two classes to be related under the restricted
       identity relation.  (Contributed by BJ, 24-Dec-2023.) $)
    bj-idreseqb $p |- ( A ( _I |` C ) B <-> ( A e. C /\ A = B ) ) $=
      ( vx vy cid cres wbr cvv wcel wa wceq relres brrelex12i simpl elexd eleq1
      biimpac jca cv wb brres adantl eqeq12 df-id brabga anbi2d bitrd pm5.21nii
      weq ) ABFCGZHZAIJZBIJZKZACJZABLZKZABUKFCMNURUMUNURACUPUQOPURBCUQUPBCJABCQ
      RPSUOULUPABFHZKZURUNULUTUAUMCABFIUBUCUOUSUQUPDEUJUQDEABFIIDTAETBUDDEUEUFU
      GUHUI $.
  $}

  ${
    $d x y A $.  $d x y B $.
    $( For sets, the identity relation is the same thing as equality.
       (Contributed by NM, 30-Apr-2004.)  (Proof shortened by Andrew Salmon,
       27-Aug-2011.)  Generalize to a disjunctive antecedent.  (Revised by BJ,
       24-Dec-2023.)

       TODO: delete once ~ bj-ideqg is in the main section. $)
    bj-ideqg1 $p |- ( ( A e. V \/ B e. W ) -> ( A _I B <-> A = B ) ) $=
      ( vx vy cid wbr cvv wcel wa wceq wo weq cv eqeq12 wi elex a1d jaoi eleq1a
      df-id bj-brab2a1 simpr syl eleq1 syl5ibcom jcad ancrd impbid2 bitrid ) AB
      GHAIJZBIJZKZABLZKZACJZBDJZMZUOEFNUOEFABGEOAFOBPEFUBUCUSUPUOUNUOUDUSUOUNUS
      UOULUMUQUOULQZURUQULUOACRZSURUMUTBDRZBIAUAUETUQUOUMQURUQULUOUMVAABIUFUGUR
      UMUOVBSTUHUIUJUK $.

    $( Alternate proof of bj-ideqg1 using ~ brabga instead of the "unbounded"
       version ~ bj-brab2a1 or ~ brab2a .  (Contributed by BJ, 25-Dec-2023.)
       (Proof modification is discouraged.)  (New usage is discouraged.)

       TODO: delete once ~ bj-ideqg is in the main section. $)
    bj-ideqg1ALT $p |- ( ( A e. V \/ B e. W ) -> ( A _I B <-> A = B ) ) $=
      ( vx vy wcel wo cid wbr wceq cvv wa reli elex adantr eleq1 elexd jaoian
      cv brrelex12i adantl biimparc biimpac jca eqeq12 df-id brabga pm5.21nd
      weq ) ACGZBDGZHZABIJZABKZALGZBLGZMZUNURUMABINUAUBUMUOMUPUQUKUOUPULUKUPUOA
      COPULUOMADUOADGULABDQUCRSUKUOUQULUKUOMBCUOUKBCGABCQUDRULUQUOBDOPSUEEFUJUO
      EFABILLETAFTBUFEFUGUHUI $.
  $}

  $( Characterization of the couples in ` _I ` .  (Contributed by BJ,
     29-Mar-2020.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  bj-opelidb1ALT $p |- ( <. A , B >. e. _I <-> ( A e. _V /\ A = B ) ) $=
    ( cop cid wcel cvv wceq wbr df-br reli brrelex1i sylbir wb inex1g bj-opelid
    cin syl biadanii ) ABCDEZAFEZABGZSABDHTABDIABDJKLTABPFESUAMABFNABFOQR $.

  $( Characterization of the couples in ` _I ` whose first component is a
     setvar.  (Contributed by BJ, 29-Mar-2020.) $)
  bj-elid3 $p |- ( <. x , A >. e. _I <-> x = A ) $=
    ( cv cop cid wcel cvv wceq vex bj-opelidb1 mpbiran ) ACZBDEFLGFLBHAILBJK $.

  $( Characterization of the elements of ` _I ` .  (Contributed by BJ,
     22-Jun-2019.) $)
  bj-elid4 $p |-
            ( A e. ( V X. W ) -> ( A e. _I <-> ( 1st ` A ) = ( 2nd ` A ) ) ) $=
    ( cxp wcel c1st cfv c2nd cop wceq cid wb 1st2nd2 eleq1 adantl cin cvv inex2
    wa fvex bj-opelid mp1i bitrd mpdan ) ABCDEZAAFGZAHGZIZJZAKEZUFUGJZLABCMUEUI
    SZUJUHKEZUKUIUJUMLUEAUHKNOUFUGPQEUMUKLULUGUFAHTRUFUGQUAUBUCUD $.

  $( Characterization of the elements of ` _I ` .  (Contributed by BJ,
     22-Jun-2019.) $)
  bj-elid5 $p |-
          ( A e. _I <-> ( A e. ( _V X. _V ) /\ ( 1st ` A ) = ( 2nd ` A ) ) ) $=
    ( cid wcel cvv cxp c1st cfv c2nd wceq wrel wss reli sseli bj-elid4 biadanii
    df-rel mpbi ) ABCADDEZCAFGAHGIBRABJBRKLBPQMADDNO $.

  $( Characterization of the elements of the diagonal of a Cartesian square.
     (Contributed by BJ, 22-Jun-2019.) $)
  bj-elid6 $p |- ( B e. ( _I |` A ) <->
                          ( B e. ( A X. A ) /\ ( 1st ` B ) = ( 2nd ` B ) ) ) $=
    ( cid cres wcel cvv cxp wa c1st cfv c2nd wceq df-res elin2 biancomi 1st2nd2
    wb eleq1 adantl opelxp bj-elid4 pm5.32i cop pm4.71ri wi simpl imbitrid jcad
    a1i anim2i impbid1 adantr 3bitr4g bicomd 3bitrd pm5.32da simpr ancri impbii
    elex bitrdi bitrid pm5.32ri 3bitri ) BCADZEZBAFGZEZBCEZHVHBIJZBKJZLZHBAAGZE
    ZVLHVFVHVIBCVGVECAMNOVHVIVLBAFUAUBVLVHVNVHBVJVKUCZLZVHHZVLVNVHVPBAFPUDVLVQV
    PVNHZVNVLVPVHVNVLVPHZVHVOVGEZVOVMEZVNVPVHVTQVLBVOVGRSVSVJAEZVKFEZHZWBVKAEZH
    ZVTWAVLWDWFQVPVLWDWFVLWDWBWEWDWBUEVLWBWCUFZUIWDWBVLWEWGVJVKARUGUHWEWCWBVKAU
    TUJUKULVJVKAFTVJVKAATUMVPWAVNQVLVPVNWABVOVMRUNSUOUPVRVNVPVNUQVNVPBAAPURUSVA
    VBVCVD $.

  $( Characterization of the elements of the diagonal of a Cartesian square.
     (Contributed by BJ, 22-Jun-2019.) $)
  bj-elid7 $p |- ( <. B , C >. e. ( _I |` A ) <-> ( B e. A /\ B = C ) ) $=
    ( cop cid cres wcel wbr wceq wa df-br bj-idreseqb bitr3i ) BCDEAFZGBCNHBAGB
    CIJBCNKBCALM $.

$(
more general elid6:
    |- ( A e. ( _I |` ( V i^i W ) ) <->
          ( A e. ( V X. W ) /\ ( 1st ` A ) = ( 2nd ` A ) ) ) $=

"stronger" elid4:
    |- ( A e. ( V X. W ) ->
              ( A e. ( _I |` ( V i^i W ) ) <-> ( 1st ` A ) = ( 2nd ` A ) ) ) $=
$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Functionalized identity (diagonal in a Cartesian square)
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  This subsection defines a functionalized version of the identity relation,
  that can also be seen as the diagonal in a Cartesian square.

  As explained in ~ df-bj-diag , it will probably be deleted.

$)

  $( Token for the diagonal of the Cartesian square of a set. $)
  $c _Id $.

  $( Syntax for the diagonal of the Cartesian square of a set. $)
  cdiag2 $a class _Id $.

  $( Define the functionalized identity, which can also be seen as the diagonal
     function.  Its value is given in ~ bj-diagval when it is viewed as the
     functionalized identity, and in ~ bj-diagval2 when it is viewed as the
     diagonal function.

     Indeed, Definition ~ df-br identifies a binary relation with the class of
     couples that are related by that binary relation (see ~ eqrel2 for the
     extensionality property of binary relations).  As a consequence, the
     identity relation, or identity function (see ~ funi ), on any class, can
     alternatively be seen as the diagonal of the cartesian square of that
     class.

     The identity relation on the universal class, ` _I ` , is an "identity
     relation generator", since its restriction to any class is the identity
     relation on that class.  It may be useful to consider a functionalized
     version of that fact, and that is the purpose of ~ df-bj-diag .

     Note: most proofs will only use its values ` ( _Id `` A ) ` , in which
     case it may be enough to use ` ( _I |`` A ) ` everywhere and dispense with
     this definition.  (Contributed by BJ, 22-Jun-2019.) $)
  df-bj-diag $a |- _Id = ( x e. _V |-> ( _I |` x ) ) $.

  ${
    $d x A $.
    $( Value of the functionalized identity, or equivalently of the diagonal
       function.  This expression views it as the functionalized identity,
       whereas ~ bj-diagval2 views it as the diagonal function.  See
       ~ df-bj-diag for the terminology.  (Contributed by BJ, 22-Jun-2019.) $)
    bj-diagval $p |- ( A e. V -> ( _Id ` A ) = ( _I |` A ) ) $=
      ( vx wcel cid cv cres cvv cdiag2 df-bj-diag reseq2 elex resiexg fvmptd3 )
      ABDCAECFZGEAGHIHCJOAEKABLABMN $.
  $}

  $( Value of the functionalized identity, or equivalently of the diagonal
     function.  This expression views it as the diagonal function, whereas
     ~ bj-diagval views it as the functionalized identity.  See ~ df-bj-diag
     for the terminology.  (Contributed by BJ, 22-Jun-2019.) $)
  bj-diagval2 $p |- ( A e. V -> ( _Id ` A ) = ( _I i^i ( A X. A ) ) ) $=
    ( wcel cdiag2 cfv cid cres cxp cin bj-diagval idinxpresid eqtr4di ) ABCADEF
    AGFAAHIABJAKL $.

  $( Characterization of the elements of the diagonal of a Cartesian square.
     Subsumed by ~ bj-elid6 .  (Contributed by BJ, 22-Jun-2019.) $)
  bj-eldiag $p |- ( A e. V -> ( B e. ( _Id ` A ) <->
                        ( B e. ( A X. A ) /\ ( 1st ` B ) = ( 2nd ` B ) ) ) ) $=
    ( wcel cdiag2 cfv cid cxp cin c1st c2nd wceq wa bj-diagval2 eleq2d bj-elid4
    elin ancom pm5.32i 3bitri bitrdi ) ACDZBAEFZDBGAAHZIZDZBUDDZBJFBKFLZMZUBUCU
    EBACNOUFBGDZUGMUGUJMUIBGUDQUJUGRUGUJUHBAAPSTUA $.

  $( Characterization of the elements of the diagonal of a Cartesian square.
     Subsumed by ~ bj-elid7 .  (Contributed by BJ, 22-Jun-2019.) $)
  bj-eldiag2 $p |- ( A e. V ->
                    ( <. B , C >. e. ( _Id ` A ) <-> ( B e. A /\ B = C ) ) ) $=
    ( wcel cop cdiag2 cfv cid cxp wceq wa bj-diagval2 eleq2d bj-opelidb1 opelxp
    cin cvv elin jca anbi12i simprl simplr elex anim1i biimpcd imdistani impbii
    eleq1 3bitri bitrdi ) ADEZBCFZAGHZEUMIAAJZQZEZBAEZBCKZLZULUNUPUMADMNUQUMIEZ
    UMUOEZLBREZUSLZURCAEZLZLZUTUMIUOSVAVDVBVFBCOBCAAPUAVGUTVGURUSVDURVEUBVCUSVF
    UCTUTVDVFURVCUSBAUDUEURUSVEUSURVEBCAUIUFUGTUHUJUK $.

$(
  @( The modulo of a number is equal to itself when the number is in the right
     interval.  Not proved from ~ modid because we want to use intervals more
     consistently.  (Contributed by BJ, 29-Jun-2019.)
     (Proof modification is discouraged.) @)
  bj-modid $p |- ( B e. RR+ -> ( A e. ( 0 [,) B ) -> ( A mod B ) = A ) ) $=
    (  ) ? $.

  @( Translation of an open interval.  Remark: in ~ icoshft, ` A , B ` may be
     in ` RR* ` .  (Contributed by BJ, 29-Jun-2019.) @)
  bj-iooshft $p |- ( ( A e. RR* /\ B e. RR* ) -> ( C e. RR ->
        ( X e. ( A (,) B ) -> ( X + C ) e. ( ( A + C ) (,) ( B + C ) ) ) ) ) $=
    (  ) ? $.
$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Direct image and inverse image
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  Definitions of the functionalized direct image and inverse image.

  The functionalized direct (resp. inverse) image is the morphism component of
  the covariant (resp. contravariant) powerset endofunctor of the category of
  sets and relations (and, up to restriction, of its subcategory of sets and
  functions).  Its object component is the powerset operation ` ~P ` defined in
  ~ df-pw .

$)

  $( Token for the functionalized direct image. $)
  $c ~P_* $.

  $( Syntax for the functionalized direct image. $)
  cimdir $a class ~P_* $.

  ${
    $d a b r x y $.
    $( Definition of the functionalized direct image, which maps a binary
       relation between two given sets to its associated direct image relation.
       (Contributed by BJ, 16-Dec-2023.) $)
    df-imdir $a |- ~P_* = ( a e. _V , b e. _V |-> ( r e. ~P ( a X. b ) |->
             { <. x , y >. | ( ( x C_ a /\ y C_ b ) /\ ( r " x ) = y ) } ) ) $.
  $}

  ${
    $d A a b r x y $.  $d B a b r x y $.  $d ph a b r $.  $d ps a b $.
    bj-imdirvallem.1 $e |- ( ph -> A e. U ) $.
    bj-imdirvallem.2 $e |- ( ph -> B e. V ) $.
    bj-imdirvallem.df $e |- C = ( a e. _V , b e. _V |-> ( r e. ~P ( a X. b )
                    |-> { <. x , y >. | ( ( x C_ a /\ y C_ b ) /\ ps ) } ) ) $.
    $( Lemma for ~ bj-imdirval and ~ bj-iminvval .  (Contributed by BJ,
       23-May-2024.) $)
    bj-imdirvallem $p |- ( ph -> ( A C B ) = ( r e. ~P ( A X. B ) |->
                        { <. x , y >. | ( ( x C_ A /\ y C_ B ) /\ ps ) } ) ) $=
      ( cvv cv wss wa wceq cxp cpw copab cmpt cmpo xpeq12 pweqd adantl bi2anan9
      a1i sseq2 anbi1d opabbidv mpteq12dv elexd xpexd pwexd mptexd ovmpod ) AKL
      EFPPJKQZLQZUAZUBZCQZUTRZDQZVARZSZBSZCDUCZUDZJEFUAZUBZVDERZVFFRZSZBSZCDUCZ
      UDGPGKLPPVKUETAOUJAUTETZVAFTZSZSJVCVJVMVRWAVCVMTAWAVBVLUTEVAFUFUGUHWAVJVR
      TAWAVIVQCDWAVHVPBVSVEVNVTVGVOUTEVDUKVAFVFUKUIULUMUHUNAEHMUOAFINUOAJVMVRPA
      VLPAEFHIMNUPUQURUS $.
  $}

  ${
    $d A a b r x y $.  $d B a b r x y $.  $d ph a b r $.
    bj-imdirval.1 $e |- ( ph -> A e. U ) $.
    bj-imdirval.2 $e |- ( ph -> B e. V ) $.
    $( Value of the functionalized direct image.  (Contributed by BJ,
       16-Dec-2023.) $)
    bj-imdirval $p |- ( ph -> ( A ~P_* B ) = ( r e. ~P ( A X. B ) |->
             { <. x , y >. | ( ( x C_ A /\ y C_ B ) /\ ( r " x ) = y ) } ) ) $=
      ( va vb cv cima wceq cimdir df-imdir bj-imdirvallem ) AHMBMNCMOBCDEPFGHKL
      IJBCHKLQR $.
  $}

  ${
    $d A x y $.  $d B x y $.  $d ph x y $.
    bj-imdirval2lem.exa $e |- ( ph -> A e. U ) $.
    bj-imdirval2lem.exb $e |- ( ph -> B e. V ) $.
    $( Lemma for ~ bj-imdirval2 and ~ bj-iminvval2 .  (Contributed by BJ,
       23-May-2024.) $)
    bj-imdirval2lem $p |- ( ph ->
                    { <. x , y >. | ( ( x C_ A /\ y C_ B ) /\ ps ) } e. _V ) $=
      ( cv wss wa copab cvv cpw pwexd wcel velpw sylibr simprl opabex2 ssopab2i
      simprr simpl a1i ssexd ) ACKZELZDKZFLZMZBMZCDNZULCDNZOAULCDEPZFPZOOAEGIQA
      FHJQAULMZUIUHUPRAUIUKUACESTURUKUJUQRAUIUKUDDFSTUBUNUOLAUMULCDULBUEUCUFUG
      $.
  $}

  ${
    $d A r x y $.  $d B r x y $.  $d R r x y $.  $d ph r x y $.
    bj-imdirval2.exa $e |- ( ph -> A e. U ) $.
    bj-imdirval2.exb $e |- ( ph -> B e. V ) $.
    bj-imdirval2.arg $e |- ( ph -> R C_ ( A X. B ) ) $.
    $( Value of the functionalized direct image.  (Contributed by BJ,
       16-Dec-2023.) $)
    bj-imdirval2 $p |- ( ph -> ( ( A ~P_* B ) ` R ) =
               { <. x , y >. | ( ( x C_ A /\ y C_ B ) /\ ( R " x ) = y ) } ) $=
      ( vr cv wss wa cima wceq copab cxp cvv cimdir co bj-imdirval simpr eqeq1d
      cpw imaeq1d anbi2d opabbidv xpexd sselpwd bj-imdirval2lem fvmptd ) ALFBMZ
      DNCMZENOZLMZUNPZUOQZOZBCRUPFUNPZUOQZOZBCRDESZUFDEUAUBTABCDEGHLIJUCAUQFQZO
      ZUTVCBCVFUSVBUPVFURVAUOVFUQFUNAVEUDUGUEUHUIAFVDTADEGHIJUJKUKAVBBCDEGHIJUL
      UM $.
  $}

  ${
    $d A x y $.  $d B x y $.  $d R x y $.  $d X x y $.  $d Y x y $.
    $d ph x y $.
    bj-imdirval3.exa $e |- ( ph -> A e. U ) $.
    bj-imdirval3.exb $e |- ( ph -> B e. V ) $.
    bj-imdirval3.arg $e |- ( ph -> R C_ ( A X. B ) ) $.
    $( Value of the functionalized direct image.  (Contributed by BJ,
       16-Dec-2023.) $)
    bj-imdirval3 $p |- ( ph -> ( X ( ( A ~P_* B ) ` R ) Y <->
                               ( ( X C_ A /\ Y C_ B ) /\ ( R " X ) = Y ) ) ) $=
      ( vx vy cvv wcel wa wss wceq adantl simpr cimdir co cfv wbr cima cv copab
      bj-imdirval2 breqd brabv biimtrdi pm4.71rd simpl adantr wb sseq1d anbi12d
      imaeq2 id eqeqan12d brabd pm5.32da ssexd ex anim12d adantrd ancrd impbid2
      3bitrd ) AGHDBCUAUBUCZUDZGNOZHNOZPZVKPVNGBQZHCQZPZDGUEZHRZPZPZVTAVKVNAVKG
      HLUFZBQZMUFZCQZPZDWBUEZWDRZPZLMUGZUDVNAVJWJGHALMBCDEFIJKUHZUIWILMGHUJUKUL
      AVNVKVTAVNPZWIVTLMGHVJNNVNVLAVLVMUMSVNVMAVLVMTSAVJWJRVNWKUNWBGRZWDHRZPZWI
      VTUOWLWOWFVQWHVSWOWCVOWEVPWOWBGBWMWNUMUPWOWDHCWMWNTUPUQWMWNWGVRWDHWBGDURW
      NUSUTUQSVAVBAWAVTVNVTTAVTVNAVQVNVSAVOVLVPVMAVOVLAVOPGBEABEOVOIUNAVOTVCVDA
      VPVMAVPPHCFACFOVPJUNAVPTVCVDVEVFVGVHVI $.
  $}

  ${
    $d A x y $.
    bj-imdiridlem.1 $e |- ( ( x C_ A /\ y C_ A ) -> ( ph <-> x = y ) ) $.
    $( Lemma for ~ bj-imdirid and ~ bj-iminvid .  (Contributed by BJ,
       26-May-2024.) $)
    bj-imdiridlem $p |-
           { <. x , y >. | ( ( x C_ A /\ y C_ A ) /\ ph ) } = ( _I |` ~P A ) $=
      ( cv wss wa copab cpw wcel cid wbr cres weq biimp3a 3expib equcomi sseq1d
      biimparc simpr biimpar an32s jca mpdan ex impbid pm5.32i anass velpw ideq
      vex anbi12i 3bitr4i opabbii dfres2 eqtr4i ) BFZDGZCFZDGZHZAHZBCIURDJZKZUR
      UTLMZHZBCILVDNVCVGBCUSVAAHZHUSBCOZHZVCVGUSVHVIUSVHVIUSVAAVIUSVAAVIEPQUSVI
      VHVJVAVHVIVAUSVIUTURDBCRSTVJVAHVAAVJVAUAUSVAVIAVBAVIEUBUCUDUEUFUGUHUSVAAU
      IVEUSVFVIBDUJURUTCULUKUMUNUOBCVDLUPUQ $.
  $}

  ${
    $d A x y $.  $d ph x y $.
    bj-imdirid.ex $e |- ( ph -> A e. U ) $.
    $( Functorial property of the direct image: the direct image by the
       identity on a set is the identity on the powerset.  (Contributed by BJ,
       24-Dec-2023.) $)
    bj-imdirid $p |-
                   ( ph -> ( ( A ~P_* A ) ` ( _I |` A ) ) = ( _I |` ~P A ) ) $=
      ( vx vy cid cres cimdir co cfv cv wss wa cima wceq copab cpw cxp idssxp
      a1i bj-imdirval2 resiima adantr eqeq1d bj-imdiridlem eqtrdi ) AGBHZBBIJKE
      LZBMZFLZBMZNZUHUIOZUKPZNEFQGBRHAEFBBUHCCDDUHBBSMABTUAUBUOEFBUMUNUIUKUJUNU
      IPULBUIUCUDUEUFUG $.
  $}

  ${
    $d x y $.
    $( Membership in an ordered-pair class abstraction.  One can remove the DV
       condition on ` x , y ` by using ~ opabid in place of ~ opabidw .
       (Contributed by BJ, 22-May-2024.) $)
    bj-opelopabid $p |- ( x { <. x , y >. | ph } y <-> ph ) $=
      ( cv copab wbr cop wcel df-br opabidw bitri ) BDZCDZABCEZFLMGNHALMNIABCJK
      $.
  $}

  ${
    $d x y z a b c $.  $d x a b c ps $.  $d z a b c ph $.
    $( Composition of ordered-pair class abstractions.  (Contributed by BJ,
       22-May-2024.) $)
    bj-opabco $p |- ( { <. y , z >. | ps } o. { <. x , y >. | ph } ) =
                                         { <. x , z >. | E. y ( ph /\ ps ) } $=
      ( va vc vb copab cv wbr wa wex nfcv nfopab1 nfbr nfv nfan nfex weq wnf wb
      ccom df-co nfopab2 simpll simpr breq12d simplr anbi12d ex cbvexdw cbvopab
      a1i bj-opelopabid anbi12i exbii opabbii 3eqtri ) BDEIZACDIZUCFJZGJZVAKZVC
      HJZUTKZLZGMZFHICJZDJZVAKZVJEJZUTKZLZDMZCEIABLZDMZCEIFHGUTVAUDVHVOFHCEVGCG
      VDVFCCVBVCVACVBNACDOCVCNPVFCQRSVGEGVDVFEVDEQEVCVEUTEVCNBDEUEEVENPRSVOFQVO
      HQFCTZHETZLZVGVNGDVTDQVGDUAVTVDVFDDVBVCVADVBNACDUEDVCNZPDVCVEUTWABDEODVEN
      PRUNVTGDTZVGVNUBVTWBLZVDVKVFVMWCVBVIVCVJVAVRVSWBUFVTWBUGZUHWCVCVJVEVLUTWD
      VRVSWBUIUHUJUKULUMVOVQCEVNVPDVKAVMBACDUOBDEUOUPUQURUS $.
  $}

  ${  $d A x y t $.  $d B x y t $.  $d C x y t $.  $d D x y t $.
    $( The composition of two Cartesian products is included in the expected
       Cartesian product.  There is equality if ` ( B i^i C ) =/= (/) ` , see
       ~ xpcogend .  (Contributed by BJ, 22-May-2024.) $)
    bj-xpcossxp $p |- ( ( C X. D ) o. ( A X. B ) ) C_ ( A X. D ) $=
      ( vx vy vt cv cxp wbr wex copab wcel ccom brxp anbi12i an43 bitri exbii
      wa 19.42v simplbi sylbi ssopab2i df-co df-xp 3sstr4i ) EHZFHZABIZJZUIGHZC
      DIZJZTZFKZEGLUHAMZULDMZTZEGLUMUJNADIUPUSEGUPUSUIBMZUICMZTZTZFKZUSUOVCFUOU
      QUTTZVAURTZTVCUKVEUNVFUHUIABOUIULCDOPUQUTVAURQRSVDUSVBFKUSVBFUAUBUCUDEGFU
      MUJUEEGADUFUG $.
  $}

  ${
    $d ph x y z u $.  $d A x y z u $.  $d B x y z u $.  $d C x y z u $.
    $d R x y z u $.  $d S x y z u $.
    bj-imdirco.exa $e |- ( ph -> A e. U ) $.
    bj-imdirco.exb $e |- ( ph -> B e. V ) $.
    bj-imdirco.exc $e |- ( ph -> C e. W ) $.
    bj-imdirco.arg1 $e |- ( ph -> R C_ ( A X. B ) ) $.
    bj-imdirco.arg2 $e |- ( ph -> S C_ ( B X. C ) ) $.
    $( Functorial property of the direct image: the direct image by a
       composition is the composition of the direct images.  (Contributed by
       BJ, 23-May-2024.) $)
    bj-imdirco $p |- ( ph -> ( ( A ~P_* C ) ` ( S o. R ) ) =
                          ( ( ( B ~P_* C ) ` S ) o. ( ( A ~P_* B ) ` R ) ) ) $=
      ( vx vz vy wa wceq wex vu cv wss ccom copab cimdir co cfv wb imaco eqeq1i
      cima anbi2i a1i cvv wcel cxp xpexd ssexd imaexg syl imass1 cin c0 cif cun
      xpima wn wo simpr orim12i elif elun 3imtr4i ssriv 0ss unssi sstri eqsstri
      ssid sstrdi eqidd sseq1 eqeq2 anbi12d spcedv biantrurd 19.41v anass exbii
      jca bitr3i bitrdi imaeq2 eqeq1d pm5.32i biancomi pm4.24 anbi1i bitri an12
      bianass 3bitrd anbi2d 19.42v ancom biid bitr4i 3bitr4i opabbidv bj-opabco
      eqtr4di coss12d bj-xpcossxp bj-imdirval2 coeq12d 3eqtr4d ) AOUBZBUCZPUBZD
      UCZRZFEUDZXRULZXTSZRZOPUEZQUBZCUCZYARZFYHULZXTSZRZQPUEZXSYIRZEXRULZYHSZRZ
      OQUEZUDZYCBDUFUGUHFCDUFUGUHZEBCUFUGUHZUDAYGYRYMRZQTZOPUEYTAYFUUDOPAYFYBFY
      PULZXTSZRZYBYIYLYIYQRZRZRZQTZRZUUDYFUUGUIAYEUUFYBYDUUEXTFEXRUJUKUMUNAUUFU
      UKYBAUUFYIYQUUFRZRZQTZUUIQTZUUKAUUFUUHQTZUUFRZUUOAUUQUUFAUUHYPCUCZYPYPSZR
      QUOYPAEUOUPYPUOUPAEBCUQZUOABCGHJKURMUSEXRUOUTVAAUUSUUTAEUVAUCZUUSMUVBYPUV
      AXRULZCEUVAXRVBUVCBXRVCVDSZVDCVEZCBCXRVGUVEVDCVFZCUAUVEUVFUVDUAUBZVDUPZRZ
      UVDVHZUVGCUPZRZVIUVHUVKVIUVGUVEUPUVGUVFUPUVIUVHUVLUVKUVDUVHVJUVJUVKVJVKUV
      DUVGVDCVLUVGVDCVMVNVOVDCCCVPCVTVQVRVSWAVAAYPWBWKYHYPSYIUUSYQUUTYHYPCWCYHY
      PYPWDWEWFWGUURUUHUUFRZQTUUOUUHUUFQWHUVMUUNQYIYQUUFWIWJWLWMUUOUUPUIAUUNUUI
      QUUNYLUUHUUMYQYLYIYQUUFYLYQUUEYKXTYPYHFWNWOWPXBWQWJUNUUPUUKUIAUUIUUJQUUIY
      LYIUUHRZRUUJUUHUVNYLUUHYIYIRZYQRUVNYIUVOYQYIWRWSYIYIYQWIWTUMYLYIUUHXAWTWJ
      UNXCXDUULUUDUIAUULYBUUJRZQTUUDYBUUJQXEUVPUUCQUVPXSYAUUJRZRZUUCXSYAUUJWIXS
      YQYMRZYIRZRYOUVSRUVRUUCUVTYIUVSXSUVSYIXFXBUVQUVTXSYMYIRZYQRZYQUWARUVQUVTU
      WAYQXFYAYIRZYLRZUUHRZYMUUHRUVQUWBUWDYMUUHUWCYJYLYAYIXFWSWSUVQUWCUUIRUWEUU
      JYIUUIYAUUJXGXBUWCYLUUHWIXHYMYIYQWIXIYQYMYIWIXIUMYOYQYMWIXIWTWJWLUNXCXJYR
      YMOQPXKXLAOPBDYCGIJLAYCCDUQZUVAUDBDUQAFUWFEUVANMXMBCCDXNWAXOAUUAYNUUBYSAQ
      PCDFHIKLNXOAOQBCEGHJKMXOXPXQ $.
  $}

  $( Token for the functionalized inverse image. $)
  $c ~P^* $.

  $( Syntax for the functionalized inverse image. $)
  ciminv $a class ~P^* $.

  ${
    $d a b r x y $.
    $( Definition of the functionalized inverse image, which maps a binary
       relation between two given sets to its associated inverse image
       relation.  (Contributed by BJ, 23-Dec-2023.) $)
    df-iminv $a |- ~P^* = ( a e. _V , b e. _V |-> ( r e. ~P ( a X. b ) |->
          { <. x , y >. | ( ( x C_ a /\ y C_ b ) /\ x = ( `' r " y ) ) } ) ) $.
  $}

  ${
    $d A a b r x y $.  $d B a b r x y $.  $d ph a b r $.
    bj-iminvval.1 $e |- ( ph -> A e. U ) $.
    bj-iminvval.2 $e |- ( ph -> B e. V ) $.
    $( Value of the functionalized inverse image.  (Contributed by BJ,
       23-May-2024.) $)
    bj-iminvval $p |- ( ph -> ( A ~P^* B ) = ( r e. ~P ( A X. B ) |->
          { <. x , y >. | ( ( x C_ A /\ y C_ B ) /\ x = ( `' r " y ) ) } ) ) $=
      ( va vb cv ccnv cima wceq ciminv df-iminv bj-imdirvallem ) ABMHMNCMOPBCDE
      QFGHKLIJBCHKLRS $.
  $}

  ${
    $d A r x y $.  $d B r x y $.  $d R r x y $.  $d ph r x y $.
    bj-iminvval2.exa $e |- ( ph -> A e. U ) $.
    bj-iminvval2.exb $e |- ( ph -> B e. V ) $.
    bj-iminvval2.arg $e |- ( ph -> R C_ ( A X. B ) ) $.
    $( Value of the functionalized inverse image.  (Contributed by BJ,
       23-May-2024.) $)
    bj-iminvval2 $p |- ( ph -> ( ( A ~P^* B ) ` R ) =
            { <. x , y >. | ( ( x C_ A /\ y C_ B ) /\ x = ( `' R " y ) ) } ) $=
      ( vr cv wss wa ccnv cima wceq copab cvv cxp cpw ciminv bj-iminvval cnveqd
      simpr imaeq1d eqeq2d anbi2d opabbidv xpexd sselpwd bj-imdirval2lem fvmptd
      co ) ALFBMZDNCMZENOZUPLMZPZUQQZRZOZBCSURUPFPZUQQZRZOZBCSDEUAZUBDEUCUOTABC
      DEGHLIJUDAUSFRZOZVCVGBCVJVBVFURVJVAVEUPVJUTVDUQVJUSFAVIUFUEUGUHUIUJAFVHTA
      DEGHIJUKKULAVFBCDEGHIJUMUN $.
  $}

  ${
    $d A x y $.  $d ph x y $.
    bj-iminvid.ex $e |- ( ph -> A e. U ) $.
    $( Functorial property of the inverse image: the inverse image by the
       identity on a set is the identity on the powerset.  (Contributed by BJ,
       26-May-2024.) $)
    bj-iminvid $p |-
                   ( ph -> ( ( A ~P^* A ) ` ( _I |` A ) ) = ( _I |` ~P A ) ) $=
      ( vx vy cid cres ciminv co cfv cv wss wa ccnv cima wceq copab cpw cxp a1i
      idssxp cnvresid imaeq1i resiima eqtrid adantl eqeq2d bj-imdiridlem eqtrdi
      bj-iminvval2 ) AGBHZBBIJKELZBMZFLZBMZNZUMULOZUOPZQZNEFRGBSHAEFBBULCCDDULB
      BTMABUBUAUKUTEFBUQUSUOUMUPUSUOQUNUPUSULUOPUOURULUOBUCUDBUOUEUFUGUHUIUJ $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Extended numbers and projective lines as sets
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  We parameterize the set of infinite extended complex numbers ` CCinfty `
  ( ~ df-bj-ccinfty ) using the real numbers ` RR ` ( ~ df-r ) via the function
  ` inftyexpitau ` .  Since at that point, we have only defined the set of
  real numbers but no operations on it, we define a temporary "fractional part"
  function, which is more convenient to define on the temporary reals ` R. `
  ( ~ df-nr ) since we can use operations on the latter.  We also define the
  temporary real "one-half" in order to define minus infinity
  ( ~ df-bj-minfty ) and then we can define the sets of extended real numbers
  and of extended complex numbers, and the projective real and complex lines,
  as well as addition and negation on these, and also the order relation on the
  extended reals (which bypasses the intermediate definition of a temporary
  order on the real numbers and then a superseding one on the extended real
  numbers).

$)

  $( Token for the fractional part of a temporary real. $)
  $c {R $.

  $( Syntax for the fractional part of a temporary real. $)
  cfractemp $a class {R $.

  ${
    $d x y z n $.
    $( Temporary definition: fractional part of a temporary real.

       To understand this definition, recall the canonical injection
       ` _om --> R. ` ,
       ` n |-> [ { x e. Q. | x <Q <. suc n , 1o >. } , 1P ] ~R ` where we
       successively take the successor of ` n ` to land in positive integers,
       then take the couple with ` 1o ` as second component to land in positive
       rationals, then take the Dedekind cut that positive rational forms, and
       finally take the equivalence class of the couple with ` 1P ` as second
       component.  Adding one at the beginning and subtracting it at the end is
       necessary since the constructions used in set.mm use the positive
       integers, positive rationals, and positive reals as intermediate number
       systems.  (Contributed by BJ, 22-Jan-2023.)  The precise definition is
       irrelevant and should generally not be used.  One could even inline it.
       The definitive fractional part of an extended or projective complex
       number will be defined later.  (New usage is discouraged.) $)
    df-bj-fractemp $a |- {R = ( x e. R. |-> ( iota_ y e. R.
        ( ( y = 0R \/ ( 0R <R y /\ y <R 1R ) ) /\ E. n e. _om
    ( [ <. { z e. Q. | z <Q <. suc n , 1o >. } , 1P >. ] ~R +R y ) = x ) ) ) $.
  $}

  $( Token for the function inftyexpitau parameterizing CCinfty. $)
  $c inftyexpitau $.

  $( Syntax for the function ` inftyexpitau ` parameterizing ` CCinfty ` . $)
  cinftyexpitau $a class inftyexpitau $.

  $( Definition of the auxiliary function ` inftyexpitau ` parameterizing the
     circle at infinity ` CCinfty ` in ` CCbar ` .  We use coupling with
     ` { R. } ` to simplify the proof of ~ bj-inftyexpitaudisj .  (Contributed
     by BJ, 22-Jan-2023.)  The precise definition is irrelevant and should
     generally not be used.  TODO: prove only the necessary lemmas to prove
     ` |- ( A e. RR /\ B e. RR ) -> ( ( inftyexpitau `` A ) = `
     ` ( inftyexpitau `` B ) <-> ( A - B ) e. ZZ ) ) ` .
     (New usage is discouraged.) $)
  df-bj-inftyexpitau $a |- inftyexpitau =
                         ( x e. RR |-> <. ( {R ` ( 1st ` x ) ) , { R. } >. ) $.

  $( Token for the circle at infinity. $)
  $c CCinftyN $.

  $( Syntax for the circle at infinity ` CCinftyN ` . $)
  cccinftyN $a class CCinftyN $.

  $( Definition of the circle at infinity ` CCinftyN ` .  (Contributed by BJ,
     22-Jun-2019.)  The precise definition is irrelevant and should generally
     not be used.  (New usage is discouraged.) $)
  df-bj-ccinftyN $a |- CCinftyN = ran inftyexpitau $.

  $( The function ` inftyexpitau ` written as a surjection with domain and
     range.  (Contributed by BJ, 4-Feb-2023.) $)
  bj-inftyexpitaufo $p |- inftyexpitau : RR -onto-> CCinftyN $=
    ( vx cr cinftyexpitau crn wfo cccinftyN wfn c1st cfv cfractemp cnr csn opex
    cv cop df-bj-inftyexpitau fnmpti dffn4 mpbi wceq df-bj-ccinftyN foeq3 ax-mp
    wb eqcomi ) BCDZCEZBFCEZCBGUGABANHIJIZKLZOCUIUJMAPQBCRSUFFTUGUHUDFUFUAUEUFF
    BCUBUCS $.

  $( Token for the temporary one-half. $)
  $c 1/2 $.

  $( Syntax for the temporary one-half. $)
  chalf $a class 1/2 $.

  $( Define the temporary real "one-half".  Once the machinery is developed,
     the real number "one-half" is commonly denoted by ` ( 1 / 2 ) ` .
     (Contributed by BJ, 4-Feb-2023.)  (New usage is discouraged.)

     TODO:

     $p |- 1/2 e.  R. $= ? $.  ( ~ riotacl )

     $p |- -. 0R = 1/2 $= ? $.  (since -.  ( 0R +R 0R ) = 1R )

     $p |- 0R <R 1/2 $= ? $.

     $p |- 1/2 <R 1R $= ? $.

     $p |- ( {R `` 0R ) = 0R $= ? $.

     $p |- ( {R `` 1/2 ) = 1/2 $= ? $.

     df-minfty $a |- minfty = ( inftyexpitau `` <. 1/2 , 0R >. ) $. $)
  df-bj-onehalf $a |- 1/2 = ( iota_ x e. R. ( x +R x ) = 1R ) $.

  ${
    $d A x $.
    $( An element of the circle at infinity is not a complex number.
       (Contributed by BJ, 4-Feb-2023.) $)
    bj-inftyexpitaudisj $p |- -. ( inftyexpitau ` A ) e. CC $=
      ( vx vy cinftyexpitau wcel cfv cc wn cfractemp cnr cop df-bj-inftyexpitau
      c1st wceq cr cv opex cvv mtbir eleq1d cdm csn 2fveq3 opeq1d dmmpti eleq2s
      fvmpt cxp wa nrex1 bj-nsnid ax-mp intnan opelxp eleq2i eqcom biimpi mtbii
      df-c syl c0 0ncn ndmfv mtbiri pm2.61i ) ADUAZEZADFZGEZHZVGVHAMFIFZJUBZKZN
      ZVJVNAOVFBABPZMFIFZVLKVMODVOANVPVKVLVOAIMUCUDBLVKVLQUGCOCPMFIFZVLKDVQVLQC
      LUEUFVNVMGEZVIVRVMJJUHZEZVTVKJEZVLJEZUIWBWAJREWBHUJJRUKULUMVKVLJJUNSGVSVM
      USUOSVNVMVHGVNVMVHNVHVMUPUQTURUTVGHZVIVAGEVBWCVHVAGADVCTVDVE $.
  $}

  $( Token for the function inftyexpi parameterizing CCinfty. $)
  $c inftyexpi $.

  $( Syntax for the function ` inftyexpi ` parameterizing ` CCinfty ` . $)
  cinftyexpi $a class inftyexpi $.

  $( Definition of the auxiliary function ` inftyexpi ` parameterizing the
     circle at infinity ` CCinfty ` in ` CCbar ` .  We use coupling with ` CC `
     to simplify the proof of ~ bj-ccinftydisj .  It could seem more natural to
     define ` inftyexpi ` on all of ` RR ` , but we want to use only basic
     functions in the definition of ` CCbar ` .  TODO: transition to
     ~ df-bj-inftyexpitau instead.  (Contributed by BJ, 22-Jun-2019.)  The
     precise definition is irrelevant and should generally not be used.
     (New usage is discouraged.) $)
  df-bj-inftyexpi $a |-
                    inftyexpi = ( x e. ( -u _pi (,] _pi ) |-> <. x , CC >. ) $.

  ${
    $d x A $.
    $( Utility theorem for the inverse of ` inftyexpi ` .  (Contributed by BJ,
       22-Jun-2019.)  This utility theorem is irrelevant and should generally
       not be used.  (New usage is discouraged.) $)
    bj-inftyexpiinv $p |- ( A e. ( -u _pi (,] _pi ) ->
                                           ( 1st ` ( inftyexpi ` A ) ) = A ) $=
      ( vx cpi cneg cioc co wcel cinftyexpi cfv cc cop cv opeq1 df-bj-inftyexpi
      c1st opex fvmpt fveq2d cvv wceq cnex op1stg mpan2 eqtrd ) ACDCEFZGZAHIZOI
      AJKZOIZAUFUGUHOBABLZJKUHUEHUJAJMBNAJPQRUFJSGUIATUAAJUESUBUCUD $.
  $}

  $( Injectivity of the parameterization ` inftyexpi ` .  Remark: a more
     conceptual proof would use ~ bj-inftyexpiinv and the fact that a function
     with a retraction is injective.  (Contributed by BJ, 22-Jun-2019.) $)
  bj-inftyexpiinj $p |- ( ( A e. ( -u _pi (,] _pi ) /\
                            B e. ( -u _pi (,] _pi ) ) ->
                       ( A = B <-> ( inftyexpi ` A ) = ( inftyexpi ` B ) ) ) $=
    ( cpi cneg cioc co wcel wa wceq cinftyexpi cfv fveq2 bj-inftyexpiinv adantr
    c1st eqeq1d biimpd adantl eqeq2d sylibd syl5 impbid2 ) ACDCEFZGZBUCGZHZABIZ
    AJKZBJKZIZABJLUJUHOKZUIOKZIZUFUGUHUIOLUFUMAULIZUGUFUMUNUFUKAULUDUKAIUEAMNPQ
    UFULBAUEULBIUDBMRSTUAUB $.

  ${
    $d A x $.
    $( An element of the circle at infinity is not a complex number.
       (Contributed by BJ, 22-Jun-2019.)  This utility theorem is irrelevant
       and should generally not be used.  (New usage is discouraged.) $)
    bj-inftyexpidisj $p |- -. ( inftyexpi ` A ) e. CC $=
      ( vx cinftyexpi cdm wcel cfv cc wn cop wceq cpi opex cvv cnex 0ncn mtbiri
      c0 syl pm2.61i eleq1d cneg cioc co cv opeq1 df-bj-inftyexpi dmmpti eleq2s
      fvmpt cpr prid2 csn wo eqid olci wb elopg mpan2 mpbiri bj-imn3ani sylancr
      en3lp opprc1 eleq1 eqcom biimpi mtbii ndmfv ) ACDZEZACFZGEZHZVJVKAGIZJZVM
      VOAKUAKUBUCZVIBABUDZGIZVNVPCVQAGUEBUFZAGLUIBVPVRCVQGLVSUGUHVOVNGEZVLAMEZV
      THZWAGAGUJZEZWCVNEZWBAGNUKWAWEWCAULJZWCWCJZUMZWGWFWCUNUOWAGMEWEWHUPNAGWCM
      MUQURUSWDWEVTGWCVNVBUTVAWAHVNQJZWBAGVCWIVTQGEZOVNQGVDPRSVOVNVKGVOVNVKJVKV
      NVEVFTVGRVJHZVLWJOWKVKQGACVHTPS $.
  $}

  $( Token for the circle at infinity. $)
  $c CCinfty $.

  $( Syntax for the circle at infinity ` CCinfty ` . $)
  cccinfty $a class CCinfty $.

  $( Definition of the circle at infinity ` CCinfty ` .  (Contributed by BJ,
     22-Jun-2019.)  The precise definition is irrelevant and should generally
     not be used.  (New usage is discouraged.) $)
  df-bj-ccinfty $a |- CCinfty = ran inftyexpi $.

  ${
    $d x y $.
    $( The circle at infinity is disjoint from the set of complex numbers.
       (Contributed by BJ, 22-Jun-2019.) $)
    bj-ccinftydisj $p |- ( CC i^i CCinfty ) = (/) $=
      ( vx vy vz cccinfty cin wcel cinftyexpi cfv wex bj-inftyexpidisj nex wceq
      cc cv wa elin crn cdm cpi syl wrex wfun cneg cioc df-bj-inftyexpi funmpt2
      wi co cop elrnrexdm ax-mp rexex df-bj-ccinfty eleq2s anim2i sylbi exancom
      ancom 19.41v bitri sylbb2 eleq1 biimpac eximi mto nel0 ) AMDEZANZVGFZBNZG
      HZMFZBIZVLBVJJKVIVHMFZVHVKLZOZBIZVMVIVNVOBIZOZVQVIVNVHDFZOVSVHMDPVTVRVNVR
      VHGQZDVHWAFZVOBGRZUAZVRGUBWBWDUGCSUCSUDUHCNMUIGCUEUFBGVHUJUKVOBWCULTUMUNU
      OUPVSVRVNOZVQVNVRURVQVOVNOBIWEVNVOBUQVOVNBUSUTVATVPVLBVOVNVLVHVKMVBVCVDTV
      EVF $.
  $}

  $( A lemma for infinite extended complex numbers.  (Contributed by BJ,
     27-Jun-2019.) $)
  bj-elccinfty $p |- ( A e. ( -u _pi (,] _pi ) ->
                                              ( inftyexpi ` A ) e. CCinfty ) $=
    ( vx cpi cneg cioc co wcel cinftyexpi wfun cdm cfv cccinfty df-bj-inftyexpi
    wa crn cv cc cop funmpt2 eqcomi jctl opex dmmpti eleq2s df-bj-ccinfty 3syl
    fvelrn eleq2i biimpi ) ACDCEFZGHIZAHJZGZNZAHKZHOZGZUOLGZUNAULUJUMUKBUJBPZQR
    ZHBMZSUAULUJBUJUTHUSQUBVAUCTUDAHUGUQURUPLUOLUPUETUHUIUF $.

  $( Token for the set of extended complex numbers. $)
  $c CCbar $.

  $( Syntax for the set of extended complex numbers ` CCbar ` . $)
  cccbar $a class CCbar $.

  $( Definition of the set of extended complex numbers ` CCbar ` .
     (Contributed by BJ, 22-Jun-2019.) $)
  df-bj-ccbar $a |- CCbar = ( CC u. CCinfty ) $.

  $( Complex numbers are extended complex numbers.  (Contributed by BJ,
     27-Jun-2019.) $)
  bj-ccssccbar $p |- CC C_ CCbar $=
    ( cc cccinfty cun cccbar ssun1 df-bj-ccbar sseqtrri ) AABCDABEFG $.

  $( Infinite extended complex numbers are extended complex numbers.
     (Contributed by BJ, 27-Jun-2019.) $)
  bj-ccinftyssccbar $p |- CCinfty C_ CCbar $=
    ( cccinfty cc cun cccbar ssun2 df-bj-ccbar sseqtrri ) ABACDABEFG $.

  $( Token for "plus infinity". $)
  $c pinfty $.

  $( Syntax for "plus infinity". $)
  cpinfty $a class pinfty $.

  $( Definition of "plus infinity".  (Contributed by BJ, 27-Jun-2019.) $)
  df-bj-pinfty $a |- pinfty = ( inftyexpi ` 0 ) $.

  $( The class ` pinfty ` is an extended complex number.  (Contributed by BJ,
     27-Jun-2019.) $)
  bj-pinftyccb $p |- pinfty e. CCbar $=
    ( cpinfty cc0 cinftyexpi cfv cccbar df-bj-pinfty cccinfty bj-ccinftyssccbar
    cpi cneg cioc co wcel cr clt wbr cle 0re pipos pire ltnegi mpbi neg0 ltleii
    breqtri cxr w3a wb renegcli rexri elioc2 mp2an mpbir3an bj-elccinfty sselii
    ax-mp eqeltri ) ABCDZEFGEURHBIJZIKLMZURGMUTBNMZUSBOPZBIQPZRUSBJZBOBIOPUSVDO
    PSBIRTUAUBUCUEBIRTSUDUSUFMINMUTVAVBVCUGUHUSITUIUJTUSIBUKULUMBUNUPUOUQ $.

  $( The extended complex number ` pinfty ` is not a complex number.
     (Contributed by BJ, 27-Jun-2019.) $)
  bj-pinftynrr $p |- -. pinfty e. CC $=
    ( cpinfty cc0 cinftyexpi cfv cc df-bj-pinfty bj-inftyexpidisj eqneltri ) AB
    CDEFBGH $.

  $( Token for "minus infinity". $)
  $c minfty $.

  $( Syntax for "minus infinity". $)
  cminfty $a class minfty $.

  $( Definition of "minus infinity".  (Contributed by BJ, 27-Jun-2019.) $)
  df-bj-minfty $a |- minfty = ( inftyexpi ` _pi ) $.

  $( The class ` minfty ` is an extended complex number.  (Contributed by BJ,
     27-Jun-2019.) $)
  bj-minftyccb $p |- minfty e. CCbar $=
    ( vx cccinfty cccbar cminfty bj-ccinftyssccbar cpi cinftyexpi cfv wcel cneg
    cc cxr clt wbr pire rexri cc0 pipos 0re mp2an crn wfun cioc df-bj-inftyexpi
    cdm co cv funmpt2 renegcli ltnegi mpbi neg0 breqtri lttri ubioc1 mp3an opex
    cop dmmpti eleqtrri fvelrn df-bj-minfty df-bj-ccinfty 3eltr4i sselii ) BCDE
    FGHZGUAZDBGUBFGUEZIVFVGIAFJZFUCUFZAUGZKURZGAUDZUHFVJVHVILIFLIVIFMNZFVJIVIFO
    UIZPFOPVIQMNQFMNZVNVIQJZQMVPVIVQMNRQFSOUJUKULUMRVIQFVOSOUNTVIFUOUPAVJVLGVKK
    UQVMUSUTFGVATVBVCVDVE $.

  $( The extended complex number ` minfty ` is not a complex number.
     (Contributed by BJ, 27-Jun-2019.) $)
  bj-minftynrr $p |- -. minfty e. CC $=
    ( cminfty cpi cinftyexpi cfv cc df-bj-minfty bj-inftyexpidisj eqneltri ) AB
    CDEFBGH $.

  $( The extended complex numbers ` pinfty ` and ` minfty ` are different.
     (Contributed by BJ, 27-Jun-2019.) $)
  bj-pinftynminfty $p |- pinfty =/= minfty $=
    ( cpinfty cminfty wceq cc0 cinftyexpi cfv cpi pire pipos wcel wb cr clt wbr
    cle a1i 0re elioc2 mpbir3and mp2an gt0ne0ii nesymi cneg cioc renegcli rexri
    co wa 0red lt0neg2 ax-mp mpbi ltleii simpr lttri leidi bj-inftyexpiinj mtbi
    cxr df-bj-minfty eqeq2i mtbir df-bj-pinfty eqeq1i neir ) ABABCDEFZBCZVGVFGE
    FZCZDGCZVIGDGHIUAUBDGUCZGUDUGZJZGVLJZVJVIKVKUSJZGLJZVMVKGHUEZUFZHVOVPUHZVMD
    LJVKDMNZDGONZVSUIVTVSDGMNZVTIVPWBVTKHGUJUKULZPWAVSDGQHIUMPVKGDRSTVOVPVNVRHV
    SVNVPVKGMNZGGONZVOVPUNWDVSVTWBWDWCIVKDGVQQHUOTPWEVSGHUPPVKGGRSTDGUQTURBVHVF
    UTVAVBAVFBVCVDVBVE $.

  $( Token for the set of extended real numbers. $)
  $c RRbar $.

  $( Syntax for the set of extended real numbers. $)
  crrbar $a class RRbar $.

  $( Definition of the set of extended real numbers.  This aims to replace
     ~ df-xr .  (Contributed by BJ, 29-Jun-2019.) $)
  df-bj-rrbar $a |- RRbar = ( RR u. { minfty , pinfty } ) $.

  $c infty $.

  $( Syntax for ` infty ` . $)
  cinfty $a class infty $.

  $( Definition of ` infty ` , the point at infinity of the real or complex
     projective line.  (Contributed by BJ, 27-Jun-2019.)  The precise
     definition is irrelevant and should generally not be used.
     (New usage is discouraged.) $)
  df-bj-infty $a |- infty = ~P U. CC $.

  $c CChat $.

  $( Syntax for ` CChat ` . $)
  ccchat $a class CChat $.

  $( Define the complex projective line, or Riemann sphere.  (Contributed by
     BJ, 27-Jun-2019.) $)
  df-bj-cchat $a |- CChat = ( CC u. { infty } ) $.

  $c RRhat $.

  $( Syntax for ` RRhat ` . $)
  crrhat $a class RRhat $.

  $( Define the real projective line.  (Contributed by BJ, 27-Jun-2019.) $)
  df-bj-rrhat $a |- RRhat = ( RR u. { infty } ) $.

  $( The real projective line is included in the complex projective line.
     (Contributed by BJ, 27-Jun-2019.) $)
  bj-rrhatsscchat $p |- RRhat C_ CChat $=
    ( cr cinfty csn cun cc crrhat ccchat axresscn unss1 df-bj-rrhat df-bj-cchat
    wss ax-mp 3sstr4i ) ABCZDZEODZFGAELPQLHAEOIMJKN $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Addition and opposite
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  We define the operations of addition and opposite on the extended complex
  numbers and on the complex projective line (Riemann sphere) simultaneously,
  thus "overloading" the operations.

$)

  $( Token for the addition on extended complex numbers. $)
  $c +cc $.

  $( Syntax for the addition on extended complex numbers. $)
  caddcc $a class +cc $.

  $( Define the additions on the extended complex numbers (on the subset of
     ` ( CCbar X. CCbar ) ` where it makes sense) and on the complex projective
     line (Riemann sphere).  We use the plural in "additions" since these are
     two different operations, even though ` +cc ` is overloaded.  (Contributed
     by BJ, 22-Jun-2019.) $)
  df-bj-addc $a |- +cc =
    ( x e. ( ( ( CC X. CCbar ) u. ( CCbar X. CC ) ) u.
          ( ( CChat X. CChat ) u. ( _I |` CCinfty ) ) ) |->
      if ( ( ( 1st ` x ) = infty \/ ( 2nd ` x ) = infty ) , infty ,
      if ( ( 1st ` x ) e. CC , if ( ( 2nd ` x ) e. CC ,
           <. ( ( 1st ` ( 1st ` x ) ) +R ( 1st ` ( 2nd ` x ) ) ) ,
              ( ( 2nd ` ( 1st ` x ) ) +R ( 2nd ` ( 2nd ` x ) ) ) >. ,
           ( 2nd ` x ) ) , ( 1st ` x ) ) ) ) $.

  $( Token for negation on the set of extended complex numbers and the complex
     projective line (Riemann sphere). $)
  $c -cc $.

  $( Syntax for negation on the set of extended complex numbers and the complex
     projective line (Riemann sphere). $)
  coppcc $a class -cc $.

  ${
    $d x y $.
    $( Define the negation (operation giving the opposite) on the set of
       extended complex numbers and the complex projective line (Riemann
       sphere).  (Contributed by BJ, 22-Jun-2019.) $)
    df-bj-oppc $a |- -cc = ( x e. ( CCbar u. CChat ) |-> if ( x = infty ,
                  infty , if ( x e. CC , ( iota_ y e. CC ( x +cc y ) = 0 ) ,
                           ( inftyexpitau ` ( x +cc <. 1/2 , 0R >. ) ) ) ) ) $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Order relation on the extended reals
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  In this section, we redefine ~ df-ltxr without the intermediate step of
  ~ df-lt .

$)

  $( Token for the standard (strict) order on the extended reals. $)
  $c <rr $.

  $( Syntax for the standard (strict) order on the extended reals. $)
  cltxr $a class <rr $.

  ${
    $d x y z $.
    $( Define the standard (strict) order on the extended reals.  (Contributed
       by BJ, 4-Feb-2023.) $)
    df-bj-lt $a |- <rr = ( { x e. ( RRbar X. RRbar ) | E. y E. z ( (
       ( 1st ` x ) = <. y , 0R >. /\ ( 2nd ` x ) = <. z , 0R >. ) /\ y <R z ) }
          u. ( ( ( { minfty } X. RR ) u. ( RR X. { pinfty } ) )
               u. ( { minfty } X. { pinfty } ) ) ) $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Argument, multiplication and inverse
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  Since one needs arguments in order to define multiplication in ` CCbar ` ,
  and one needs complex multiplication in order to define arguments, it would
  be contrived to construct a whole theory for a temporary multiplication
  (and temporary powers, then temporary logarithm, and finally temporary
  argument) before redefining the extended complex multiplication.  Therefore,
  we adopt a two-step process, see ~ df-bj-mulc .

$)

  $( Token for the argument of a nonzero extended complex number. $)
  $c Arg $.

  $( Syntax for the argument of a nonzero extended complex number. $)
  carg $a class Arg $.

  $( Define the argument of a nonzero extended complex number.  By convention,
     it has values in ` ( -u _pi , _pi ] ` .  Another convention chooses values
     in ` [ 0 , 2 _pi ) ` but the present convention simplifies formulas giving
     the argument as an arctangent.  (Contributed by BJ, 22-Jun-2019.)  The
     "else" case of the second conditional operator, corresponding to infinite
     extended complex numbers other than ` minfty ` , gives a definition
     depending on the specific definition chosen for these numbers
     ( ~ df-bj-inftyexpitau ), and therefore should not be relied upon.
     (New usage is discouraged.) $)
  df-bj-arg $a |- Arg = ( x e. ( CCbar \ { 0 } ) |->
         if ( x e. CC , ( Im ` ( log ` x ) ) ,
         if ( x <rr 0 , _pi , ( ( ( 1st ` x ) / ( 2 x. _pi ) ) - _pi ) ) ) ) $.

  $( Token for the multiplication of extended complex numbers. $)
  $c .cc $.

  $( Syntax for the multiplication of extended complex numbers. $)
  cmulc $a class .cc $.

  $( Define the multiplication of extended complex numbers and of the complex
     projective line (Riemann sphere).  In our convention, a product with 0 is
     0, even when the other factor is infinite.  An alternate convention leaves
     products of 0 with an infinite number undefined since the multiplication
     is not continuous at these points.  Note that our convention entails
     ` ( 0 / 0 ) = 0 ` (given ~ df-bj-invc ).

     Note that this definition uses ` x. ` and ` Arg ` and ` / ` .  Indeed, it
     would be contrived to bypass ordinary complex multiplication, and the
     present two-step definition looks like a good compromise.  (Contributed by
     BJ, 22-Jun-2019.) $)
  df-bj-mulc $a |- .cc = ( x e. ( ( CCbar X. CCbar ) u. ( CChat X. CChat ) )
   |-> if ( ( ( 1st ` x ) = 0 \/ ( 2nd ` x ) = 0 ) , 0 ,
       if ( ( ( 1st ` x ) = infty \/ ( 2nd ` x ) = infty ) , infty ,
       if ( x e. ( CC X. CC ) , ( ( 1st ` x ) x. ( 2nd ` x ) ) ,
       ( inftyexpitau `
    ( ( ( Arg ` ( 1st ` x ) ) +cc ( Arg ` ( 2nd ` x ) ) ) / _tau ) ) ) ) ) ) $.

  $( Token for the inverse of nonzero extended complex numbers. $)
  $c invc $.

  $( Syntax for the inverse of nonzero extended complex numbers. $)
  cinvc $a class invc $.

  ${
    $d x y $.
    $( Define inversion, which maps a nonzero extended complex number or
       element of the complex projective line (Riemann sphere) to its inverse.
       Beware of the overloading: the equality ` ( invc `` 0 ) = infty ` is to
       be understood in the complex projective line, but 0 as an extended
       complex number does not have an inverse, which we can state as
       ` ( invc `` 0 ) e/ CCbar ` .  Note that this definition relies on
       ~ df-bj-mulc , which does not bypass ordinary complex multiplication,
       but defines extended complex multiplication on top of it.  Therefore, we
       could have used directly ` / ` instead of ` ( iota_ ... .cc ... ) ` .
       (Contributed by BJ, 22-Jun-2019.) $)
    df-bj-invc $a |- invc = ( x e. ( CCbar u. CChat ) |->
                  if ( x = 0 , infty ,
                  if ( x e. CC , ( iota_ y e. CC ( x .cc y ) = 1 ) , 0 ) ) ) $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  The canonical bijection from the finite ordinals
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( Token for the canonical bijection from ` ( _om u. { _om } ) ` onto
     ` ( NN0 u. { pinfty } ) ` . $)
  $c iomnn $.

  $( Syntax for the canonical bijection from ` ( _om u. { _om } ) ` onto
     ` ( NN0 u. { pinfty } ) ` . $)
  ciomnn $a class iomnn $.

  ${
    $d n r $.
    $( Definition of the canonical bijection from ` ( _om u. { _om } ) ` onto
       ` ( NN0 u. { pinfty } ) ` .

       To understand this definition, recall that set.mm constructs reals as
       couples whose first component is a prereal and second component is the
       zero prereal (in order that one have ` RR C_ CC ` ), that prereals are
       equivalence classes of couples of positive reals, the latter are
       Dedekind cuts of positive rationals, which are equivalence classes of
       positive ordinals.  In partiular, we take the successor ordinal at the
       beginning and subtract 1 at the end since the intermediate systems
       contain only (strictly) positive numbers.

       Note the similarity with ~ df-bj-fractemp but we did not use the present
       definition there since we wanted to have defined ` pinfty ` first.

       See ~ bj-iomnnom for its value at ` pinfty ` .

       TODO:

       Prove ` |- ( iomnn `` (/) ) = 0 ` .

       Define ` |- NN0 = ( iomnn " _om ) ` and ` |- NN = ( NN0 \ { 0 } ) ` .

       Prove
       ` |- iomnn : ( _om u. { _om } ) -1-1-onto-> ( NN0 u. { pinfty } ) ` and
       ` |- ( iomnn |`` _om ) : _om -1-1-onto-> NN0 ` .

       Prove that these bijections are respectively an isomorphism of ordered
       "extended rigs" and of ordered rigs.

       Prove ` |- ( iomnn |`` _om ) = rec ( ( x e. RR |-> ( x + 1 ) ) , 0 ) ` .

       (Contributed by BJ, 18-Feb-2023.)  The precise definition is irrelevant
       and should generally not be used.  (New usage is discouraged.) $)
    df-bj-iomnn $a |- iomnn = ( ( n e. _om |->
        <. [ <. { r e. Q. | r <Q <. suc n , 1o >. } , 1P >. ] ~R , 0R >. ) u.
                                                    { <. _om , pinfty >. } ) $.
  $}

  ${
    $d x A $.  $d x F $.  $d x G $.
    $( If the direct image of a singleton under any of two functions is the
       same, then the values of these functions at the corresponding point
       agree.  (Contributed by BJ, 18-Mar-2023.) $)
    bj-imafv $p |-
                  ( ( F " { A } ) = ( G " { A } ) -> ( F ` A ) = ( G ` A ) ) $=
      ( vx csn cima wceq cv cab cuni cfv eqeq1 abbidv unieqd dffv4 3eqtr4g ) BA
      EZFZCQFZGZRDHEZGZDIZJSUAGZDIZJABKACKTUCUETUBUDDRSUALMNDABODACOP $.
  $}

  ${
    bj-funun.un $e |- ( ph -> F = ( G u. H ) ) $.
    bj-funun.neldm $e |- ( ph -> -. A e. dom H ) $.
    $( Value of a function expressed as a union of two functions at a point not
       in the domain of one of them.  (Contributed by BJ, 18-Mar-2023.) $)
    bj-funun $p |- ( ph -> ( F ` A ) = ( G ` A ) ) $=
      ( csn cima wceq cfv cun imaeq1 imaundir eqtrdi syl c0 cdm wcel wn ndmima
      uneq2 un0 eqtrd bj-imafv ) ACBHZIZDUFIZJBCKBDKJAUGUHEUFIZLZUHACDELZJZUGUJ
      JFULUGUKUFIUJCUKUFMDEUFNOPAUIQJZUJUHJABERSTUMGBEUAPUMUJUHQLUHUIQUHUBUHUCO
      PUDBCDUEP $.
  $}

  ${
    bj-fununsn.un $e |- ( ph -> F = ( G u. { <. B , C >. } ) ) $.
    ${
      bj-fununsn1.neq $e |- ( ph -> -. A = B ) $.
      $( Value of a function expressed as a union of a function and a singleton
         on a couple (with disjoint domain) at a point not equal to the first
         component of that couple.  (Contributed by BJ, 18-Mar-2023.)
         (Proof modification is discouraged.) $)
      bj-fununsn1 $p |- ( ph -> ( F ` A ) = ( G ` A ) ) $=
        ( cop csn cdm wss dmsnopss a1i wceq wcel elsni nsyl ssneldd bj-funun )
        ABEFCDIJZGAUAKZCJZBUBUCLACDMNABCOBUCPHBCQRST $.
    $}

    ${
      bj-fununsn2.neldm $e |- ( ph -> -. B e. dom G ) $.
      bj-fununsn2.ex1 $e |- ( ph -> B e. V ) $.
      bj-fununsn2.ex2 $e |- ( ph -> C e. W ) $.
      $( Value of a function expressed as a union of a function and a singleton
         on a couple (with disjoint domain) at the first component of that
         couple.  (Contributed by BJ, 18-Mar-2023.)
         (Proof modification is discouraged.) $)
      bj-fununsn2 $p |- ( ph -> ( F ` B ) = C ) $=
        ( cfv cop csn cun uncom eqtrdi bj-funun wcel wceq fvsng syl2anc eqtrd )
        ABDLBBCMNZLZCABDUDEADEUDOUDEOHEUDPQIRABFSCGSUECTJKBCFGUAUBUC $.
    $}
  $}

  ${
    bj-fvsnun.un $e |-
                 ( ph -> G = ( ( F |` ( C \ { A } ) ) u. { <. A , B >. } ) ) $.
    ${
      bj-fvsnun1.eldif $e |- ( ph -> D e. ( C \ { A } ) ) $.
      $( The value of a function with one of its ordered pairs replaced, at
         arguments other than the replaced one.  (Contributed by NM,
         23-Sep-2007.)  Put in deduction form and remove two sethood
         hypotheses.  (Revised by BJ, 18-Mar-2023.) $)
      bj-fvsnun1 $p |- ( ph -> ( G ` D ) = ( F ` D ) ) $=
        ( cfv csn cdif cres wcel wceq wn eldifsnneq syl bj-fununsn1 fvresd
        eqtrd ) AEGJEFDBKLZMZJEFJAEBCGUCHAEUBNEBOPIEDBQRSAEUBFITUA $.
    $}

    ${
      bj-fvsnun2.ex1 $e |- ( ph -> A e. V ) $.
      bj-fvsnun2.ex2 $e |- ( ph -> B e. W ) $.
      $( The value of a function with one of its ordered pairs replaced, at the
         replaced ordered pair.  See also ~ fvsnun2 .  (Contributed by NM,
         23-Sep-2007.)  Put in deduction form.  (Revised by BJ, 18-Mar-2023.)
         (Proof modification is discouraged.) $)
      bj-fvsnun2 $p |- ( ph -> ( G ` A ) = B ) $=
        ( csn cdif cres cdm wss cin dmres inss1 eqsstri a1i ssneldd bj-fununsn2
        neldifsnd ) ABCFEDBLMZNZGHIAUFOZUEBUGUEPAUGUEEOZQUEEUERUEUHSTUAABDUDUBJ
        KUC $.
    $}
  $}

  ${
    $d A x $.
    bj-fvmptunsn.un $e |-
                       ( ph -> F = ( ( x e. A |-> B ) u. { <. C , D >. } ) ) $.
    bj-fvmptunsn.nel $e |- ( ph -> -. C e. A ) $.
    ${
      bj-fvmptunsn1.ex1 $e |- ( ph -> C e. V ) $.
      bj-fvmptunsn1.ex2 $e |- ( ph -> D e. W ) $.
      $( Value of a function expressed as a union of a mapsto expression and a
         singleton on a couple (with disjoint domain) at the first component of
         that couple.  (Contributed by BJ, 18-Mar-2023.)
         (Proof modification is discouraged.) $)
      bj-fvmptunsn1 $p |- ( ph -> ( F ` C ) = D ) $=
        ( cmpt wcel cdm eqid dmmptss sseli nsyl bj-fununsn2 ) AEFGBCDNZHIJAECOE
        UBPZOKUCCEBCDUBUBQRSTLMUA $.
    $}

    ${
      $d ph x $.  $d E x $.  $d G x $.
      bj-fvmptunsn2.el $e |- ( ph -> E e. A ) $.
      bj-fvmptunsn2.ex $e |- ( ph -> G e. V ) $.
      bj-fvmptunsn2.is $e |- ( ( ph /\ x = E ) -> B = G ) $.
      $( Value of a function expressed as a union of a mapsto expression and a
         singleton on a couple (with disjoint domain) at a point in the domain
         of the mapsto construction.  (Contributed by BJ, 18-Mar-2023.)
         (Proof modification is discouraged.) $)
      bj-fvmptunsn2 $p |- ( ph -> ( F ` E ) = G ) $=
        ( cfv cmpt wcel wn wceq nelneq syl2anc bj-fununsn1 eqidd fvmptd eqtrd )
        AGHPGBCDQZPIAGEFHUGKAGCRECRSGETSMLGECUAUBUCABGDICUGJAUGUDOMNUEUF $.
    $}
  $}

  ${
    $d n r $.
    $( The canonical bijection from ` ( _om u. { _om } ) ` onto
       ` ( NN0 u. { pinfty } ) ` maps ` _om ` to ` pinfty ` .  (Contributed by
       BJ, 18-Feb-2023.) $)
    bj-iomnnom $p |- ( iomnn ` _om ) = pinfty $=
      ( vn vr com ciomnn cfv cpinfty wceq wtru cv csuc c1o cop cltq wbr cnq cvv
      crab cccbar a1i wcel c1p cer cec c0r cmpt csn cun df-bj-iomnn word ordirr
      wn ordom ax-mp omex bj-pinftyccb bj-fvmptunsn1 mptru ) CDEFGHACBIAIJKLMNB
      OQUALUBUCUDLZCFDPRDACURUECFLUFUGGHABUHSCCTUKZHCUIUSULCUJUMSCPTHUNSFRTHUOS
      UPUQ $.
    $( $j usage 'bj-iomnnom' avoids 'ax-reg'; $)
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Divisibility
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( Token for the extended natural numbers. $)
  $c NNbar $.

  $( Syntax for the extended natural numbers. $)
  cnnbar $a class NNbar $.

  $( Definition of the extended natural numbers.  (Contributed by BJ,
     28-Jul-2023.) $)
  df-bj-nnbar $a |- NNbar = ( NN0 u. { pinfty } ) $.

  $( Token for the extended integers. $)
  $c ZZbar $.

  $( Syntax for the extended integers. $)
  czzbar $a class ZZbar $.

  $( Definition of the extended integers.  (Contributed by BJ, 28-Jul-2023.) $)
  df-bj-zzbar $a |- ZZbar = ( ZZ u. { minfty , pinfty } ) $.

  $( Token for the one-point-compactified integers. $)
  $c ZZhat $.

  $( Syntax for the one-point-compactified integers. $)
  czzhat $a class ZZhat $.

  $( Definition of the one-point-compactified.  (Contributed by BJ,
     28-Jul-2023.) $)
  df-bj-zzhat $a |- ZZhat = ( ZZ u. { infty } ) $.

  $( Token for the divisibility relation. $)
  $c ||C $.

  $( Syntax for the divisibility relation. $)
  cdivc $a class ||C $.

  ${
    $d n x y $.
    $( Definition of the divisibility relation (compare ~ df-dvds ).

       Since 0 is absorbing, ` |- ( A e. ( CCbar u. CChat ) -> ( A ||C 0 ) ) `
       and ` |- ( ( 0 ||C A ) <-> A = 0 ) ` .

       (Contributed by BJ, 28-Jul-2023.) $)
    df-bj-divc $a |- ||C = { <. x , y >. |
         ( <. x , y >. e. ( ( CCbar X. CCbar ) u. ( CChat X. CChat ) ) /\
                              E. n e. ( ZZbar u. ZZhat ) ( n .cc x ) = y ) } $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Monoids
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  See ~ ccmn and subsequents. The first few statements of this subsection can
  be put very early after ~ ccmn .
  Proposal: in the main part, make separate subsections of commutative monoids
  and abelian groups.

  Relabel ~ cabl to "cabl" or, preferably, other labels containing "abl" to
  "abel", for consistency.

$)

  ${
    $d g b p x y z $.
    $( Semigroups are magmas.  (Contributed by BJ, 12-Apr-2024.)
       (Proof modification is discouraged.) $)
    bj-smgrpssmgm $p |- Smgrp C_ Mgm $=
      ( vx vy vp vz vb vg cv co wceq wral cplusg cfv wsbc cbs cmgm csgrp ssrab3
      df-sgrp ) AGZBGZCGZHDGZUAHSTUBUAHUAHIDEGZJBUCJAUCJCFGZKLMEUDNLMFOPABDFCER
      Q $.
  $}

  $( Semigroups are magmas (elemental version).  (Contributed by BJ,
     12-Apr-2024.)  (Proof modification is discouraged.) $)
  bj-smgrpssmgmel $p |- ( G e. Smgrp -> G e. Mgm ) $=
    ( csgrp cmgm bj-smgrpssmgm sseli ) BCADE $.

  ${
    $d g b p e x $.
    $( Monoids are semigroups.  (Contributed by BJ, 11-Apr-2024.)
       (Proof modification is discouraged.) $)
    bj-mndsssmgrp $p |- Mnd C_ Smgrp $=
      ( ve vx vp vb vg cv co wceq wa wral wrex cplusg cfv wsbc cbs csgrp df-mnd
      cmnd ssrab3 ) AFZBFZCFZGUAHUATUBGUAHIBDFZJAUCKCEFZLMNDUDOMNEPRBAECDQS $.
  $}

  $( Monoids are semigroups (elemental version).  (Contributed by BJ,
     11-Apr-2024.)  (Proof modification is discouraged.) $)
  bj-mndsssmgrpel $p |- ( G e. Mnd -> G e. Smgrp ) $=
    ( cmnd csgrp bj-mndsssmgrp sseli ) BCADE $.

  ${
    $d x y z $.
    $( Commutative monoids are monoids.  (Contributed by BJ, 9-Jun-2019.)
       (Proof modification is discouraged.) $)
    bj-cmnssmnd $p |- CMnd C_ Mnd $=
      ( vy vz vx cv cplusg cfv co wceq cbs wral cmnd ccmn df-cmn ssrab3 ) ADZBD
      ZCDZEFZGPORGHBQIFZJASJCKLCABMN $.
  $}

  $( Commutative monoids are monoids (elemental version).  This is a more
     direct proof of ~ cmnmnd , which relies on ~ iscmn .  (Contributed by BJ,
     9-Jun-2019.)  (Proof modification is discouraged.) $)
  bj-cmnssmndel $p |- ( A e. CMnd -> A e. Mnd ) $=
    ( ccmn cmnd bj-cmnssmnd sseli ) BCADE $.

  ${
    $d x y z $.
    $( Groups are monoids.  (Contributed by BJ, 5-Jan-2024.)
       (Proof modification is discouraged.) $)
    bj-grpssmnd $p |- Grp C_ Mnd $=
      ( vz vy vx cv cplusg cfv c0g wceq cbs wrex wral cmnd cgrp df-grp ssrab3
      co ) ADBDCDZEFPQGFHAQIFZJBRKCLMCABNO $.
  $}

  $( Groups are monoids (elemental version).  Shorter proof of ~ grpmnd .
     (Contributed by BJ, 5-Jan-2024.)  (Proof modification is discouraged.) $)
  bj-grpssmndel $p |- ( A e. Grp -> A e. Mnd ) $=
    ( cgrp cmnd bj-grpssmnd sseli ) BCADE $.

  $( Abelian groups are groups.  (Contributed by BJ, 9-Jun-2019.)
     (Proof modification is discouraged.) $)
  bj-ablssgrp $p |- Abel C_ Grp $=
    ( cabl cgrp ccmn cin df-abl inss1 eqsstri ) ABCDBEBCFG $.

  $( Abelian groups are groups (elemental version).  This is a shorter proof of
     ~ ablgrp .  (Contributed by BJ, 9-Jun-2019.)
     (Proof modification is discouraged.) $)
  bj-ablssgrpel $p |- ( A e. Abel -> A e. Grp ) $=
    ( cabl cgrp bj-ablssgrp sseli ) BCADE $.

  $( Abelian groups are commutative monoids.  (Contributed by BJ, 9-Jun-2019.)
     (Proof modification is discouraged.) $)
  bj-ablsscmn $p |- Abel C_ CMnd $=
    ( cabl cgrp ccmn cin df-abl inss2 eqsstri ) ABCDCEBCFG $.

  $( Abelian groups are commutative monoids (elemental version).  This is a
     shorter proof of ~ ablcmn .  (Contributed by BJ, 9-Jun-2019.)
     (Proof modification is discouraged.) $)
  bj-ablsscmnel $p |- ( A e. Abel -> A e. CMnd ) $=
    ( cabl ccmn bj-ablsscmn sseli ) BCADE $.

  $( (The additive groups of) modules are abelian groups.  (The elemental
     version is ~ lmodabl ; see also ~ lmodgrp and ~ lmodcmn .)  (Contributed
     by BJ, 9-Jun-2019.) $)
  bj-modssabl $p |- LMod C_ Abel $=
    ( vx clmod cabl cv lmodabl ssriv ) ABCADEF $.

  $( Vector spaces are modules.  (Contributed by BJ, 9-Jun-2019.)
     (Proof modification is discouraged.) $)
  bj-vecssmod $p |- LVec C_ LMod $=
    ( vx clvec cv csca cfv cdr wcel clmod crab df-lvec ssrab2 eqsstri ) BACDEFG
    ZAHIHAJMAHKL $.

  $( Vector spaces are modules (elemental version).  This is a shorter proof of
     ~ lveclmod .  (Contributed by BJ, 9-Jun-2019.)
     (Proof modification is discouraged.) $)
  bj-vecssmodel $p |- ( A e. LVec -> A e. LMod ) $=
    ( clvec clmod bj-vecssmod sseli ) BCADE $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Finite sums in monoids
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  UPDATE: a similar summation is already defined as ~ df-gsum (although it
  mixes finite and infinite sums, which makes it harder to understand).

$)

  $( Symbol for the class "finite summation in monoids". $)
  $c FinSum $.

  $( Syntax for the class "finite summation in monoids". $)
  cfinsum $a class FinSum $.

  ${
    $d x y z t s f m n $.
    $( Finite summation in commutative monoids.  This finite summation function
       can be extended to pairs ` <. y , z >. ` where ` y ` is a left-unital
       magma and ` z ` is defined on a totally ordered set (choosing
       left-associative composition), or dropping unitality and requiring
       nonempty families, or on any monoids for families of permutable
       elements, etc.  We use the term "summation", even though the definition
       stands for any unital, commutative and associative composition law.
       (Contributed by BJ, 9-Jun-2019.) $)
    df-bj-finsum $a |- FinSum = (
     x e. { <. y , z >. | ( y e. CMnd /\ E. t e. Fin z : t --> ( Base ` y ) ) }
     |->
     ( iota s E. m e. NN0 E. f ( f : ( 1 ... m ) -1-1-onto-> dom ( 2nd ` x ) /\
              s = ( seq 1 ( ( +g ` ( 1st ` x ) ) , ( n e. NN |->
                                 ( ( 2nd ` x ) ` ( f ` n ) ) ) ) ` m ) ) ) ) $.
  $}

  ${
    $d A s t x y z f m n $.  $d B f m n x y z s t $.  $d I f n t x $.
    $d ph f m s x $.
    bj-finsumval0.1 $e |- ( ph -> A e. CMnd ) $.
    bj-finsumval0.2 $e |- ( ph -> I e. Fin ) $.
    bj-finsumval0.3 $e |- ( ph -> B : I --> ( Base ` A ) ) $.
    $( Value of a finite sum.  (Contributed by BJ, 9-Jun-2019.)  (Proof
       shortened by AV, 5-May-2021.) $)
    bj-finsumval0 $p |- ( ph -> ( A FinSum B ) =
     ( iota s E. m e. NN0 E. f ( f : ( 1 ... m ) -1-1-onto-> I /\ s =
       ( seq 1 ( ( +g ` A ) , ( n e. NN |->
                                   ( B ` ( f ` n ) ) ) ) ` ( # ` I ) ) ) ) ) $=
      ( vt cfv c1 cv wceq wa wcel cfn adantr vx vy vz cfinsum co cop wf1o chash
      cfz cplusg cn cmpt cseq wex cn0 wrex cio df-ov c2nd cdm c1st cbs wf copab
      ccmn cvv df-bj-finsum wb wi simpr fveq2d fexd op1stg syl2anc eqtrd op2ndg
      dmeqd fdmd f1oeq3 biimpd ad2antll adantrd eqidd adantrr simprrl mpteq2dva
      simprl fveq1d seqeq123d simprr anim1ci hashfz1 eqcomd ad2antrl hasheqf1oi
      fzfid 19.8a sylc 3eqtrd sylan2 fveq12d eqeq2d impancom com12 jcad biimprd
      wtru simpl tru syl adantlrr impcom syl12anc impbid ex imp exbidv rexbidva
      jctir iotabidv eleq1 feq2 anbi12d ceqsexgv mpbir2and exsimpr df-rex fveq2
      sylibr feq3d rexbidv feq1 anbi2d opelopabg iotaex a1i fvmptd2 eqtrid ) AB
      CUDUEBCUFZUDMNEOZUIUEZGDOZUGZHOZGUHMZBUJMZFUKFOZUUBMZCMZULZNUMZMZPZQZDUNZ
      EUOUPZHUQZBCUDURAUAYSUUAUAOZUSMZUTZUUBUGZUUDYTUURVAMZUJMZFUKUUHUUSMZULZNU
      MZMZPZQZDUNZEUOUPZHUQUUQUBOZVERZLOZUVLVBMZUCOZVCZLSUPZQZUBUCVDZUDVFUAUBUC
      LDEFHVGAUURYSPZQZUVKUUPHUWBUVJUUOEUOUWBYTUORZQUVIUUNDUWBUWCUVIUUNVHZUWBUV
      BBPZUUSCPZUUTGPZUWCUWDVIUWBUVBYSVAMZBUWBUURYSVAAUWAVJZVKUWBBVERZCVFRZUWHB
      PAUWJUWAITZAUWKUWAAGBVBMZSCKJVLZTZBCVEVFVMVNVOUWBUUSYSUSMZCUWBUURYSUSUWIV
      KUWBUWJUWKUWPCPUWLUWOBCVEVFVPVNVOZUWBUUTCUTZGUWBUUSCUWQVQAUWRGPUWAAGUWMCK
      VRTVOUWEUWFUWGQZQZUWCUWDUWTUWCQZUVIUUNUXAUVIUUCUUMUWTUVIUUCVIUWCUWTUVAUUC
      UVHUWGUVAUUCVIUWEUWFUWGUVAUUCUUTGUUAUUBVSZVTWAWBTUVIUXAUUMUVAUXAUVHUUMUVA
      UXAQZUVHUUMUXCUVGUULUUDUXCYTUUEUVFUUKUXCUVCUUFUVEUUJNNUXCNWCUVAUWTUVCUUFP
      UWCUVAUWTQZUVBBUJUVAUWEUWSWGVKWDUVAUWTUVEUUJPUWCUXDFUKUVDUUIUXDUUGUKRZQUU
      HUUSCUXDUWFUXEUVAUWEUWFUWGWETWHWFWDWIUXAUVAUWCUWGQZYTUUEPZUWTUWGUWCUWEUWF
      UWGWJZWKUVAUXFQZYTUUAUHMZUUTUHMZUUEUWCYTUXJPUVAUWGUWCUXJYTYTWLWMWNUXIUUAS
      RUVADUNZUXJUXKPUXINYTWPUVAUXLUXFUVADWQTUUAUUTDSWOWRUXIUUTGUHUVAUWCUWGWJVK
      WSZWTXAXBVTXCXDXEUXAUUNUVAUVHUXAUUCUVAUUMUWTUUCUVAVIZUWCUWGUXNUWEUWFUWGUV
      AUUCUXBXFWATZWBUUNUXAUVHUUCUXAUUMUVHUUCUXAQZUUMUVHUXPUULUVGUUDUXPUUEYTUUK
      UVFUXPUUFUVCUUJUVENNUXPNWCUXPBUVBUJUXPUWEXGQZBUVBPUWTUXQUUCUWCUWTUWEXGUWE
      UWSXHXIXSWNUXQUVBBUWEXGXHWMXJVKUXPFUKUUIUVDUUCUWTUXEUUIUVDPUWCUUCUWTQZUXE
      QUUHCUUSUXRCUUSPZUXEUWSUXSUUCUWEUWSUUSCUWFUWGXHWMWATWHXKWFWIUXPYTUUEUXPUV
      AUWCUWGUXGUXAUUCUVAUXOXLUUCUWTUWCWJUWTUWGUUCUWCUXHWNUXMXMWMXAXBVTXCXDXEXN
      XOXMXPXQXRXTAYSUVTRZUWJUVNUWMCVCZLSUPZIAUVNSRZUYAQZLUNZUYBAUVNGPZUYDQLUNZ
      UYEAUYGGSRZGUWMCVCZJKAUYHUYGUYHUYIQZVHJUYDUYJLGSUYFUYCUYHUYAUYIUVNGSYAUVN
      GUWMCYBYCYDXJYEUYFUYDLYFXJUYALSYGYIAUWJUWKUXTUWJUYBQZVHIUWNUVSUWJUVNUWMUV
      PVCZLSUPZQUYKUBUCBCVEVFUVLBPZUVMUWJUVRUYMUVLBVEYAUYNUVQUYLLSUYNUVOUWMUVPU
      VNUVLBVBYHYJYKYCUVPCPZUYMUYBUWJUYOUYLUYALSUVNUWMUVPCYLYKYMYNVNYEUUQVFRAUU
      PHYOYPYQYR $.

$(
  @( Value of a finite sum.  (Contributed by BJ, 9-Jun-2019.) @)
  bj-finsumval1 $p |- ( ph ->
   ( A FinSum B ) = ( iota s E. f ( f : ( 1 ... ( # ` I ) ) -1-1-onto-> I /\
   s = ( seq 1 ( ( +g ` A ) , ( n e. NN |->
                                   ( B ` ( f ` n ) ) ) ) ` ( # ` I ) ) ) ) ) $=
    (  ) ? $.
$)
  $}

$(
  @( Value of a finite sum.  (Contributed by BJ, 9-Jun-2019.) @)
  bj-finsumval2 $p |- ( A e. CMnd ->
    ( ( m e. NN0 /\ B : ( 1 ... m ) --> ( Base ` A ) ) -> ( A FinSum B ) =
                ( seq 1 ( ( +g ` A ) , ( n e. NN |-> ( B ` n ) ) ) ` m ) ) ) $=
    (  ) ? $.

  @( The sum of the empty set is the identity.  (Contributed by BJ,
     9-Jun-2019.) @)
  bj-finsum0 $p |- ( A e. CMnd -> ( A FinSum (/) ) = ( 0g ` A ) ) $=
    (  ) ? $.

  @( The sum of a singleton is the element of that singleton.  (Contributed by
     BJ, 9-Jun-2019.) @)
  bj-finsum1 $p |- ( A e. CMnd -> ( B e. V ->
               ( x e. ( Base ` A ) -> ( A FinSum { <. B , x >. } ) = x ) ) ) $=
    (  ) ? $.
$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Affine, Euclidean, and Cartesian geometry
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  A few basic theorems to start affine, Euclidean, and Cartesian geometry.

  The first step is to define real vector spaces, then barycentric coordinates
  and convex hulls.

$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Real vector spaces
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  In this section, we introduce real vector spaces.

$)

  $( Variant of ~ fvimacnv where membership of ` A ` in the domain is not
     needed provided the containing class ` B ` does not contain the empty set.
     Note that this antecedent would not be needed with Definition ~ df-afv .
     (Contributed by BJ, 7-Jan-2024.) $)
  bj-fvimacnv0 $p |- ( ( Fun F /\ -. (/) e. B ) ->
                                  ( ( F ` A ) e. B <-> A e. ( `' F " B ) ) ) $=
    ( wfun c0 wcel wn wa cfv ccnv cima cdm wceq eleq1 biimpcd con3rr3 imp ndmfv
    wi ex nsyl2 simpr fvimacnv biimpd com3l sylc com3r fvimacnvi adantr impbid
    ) CDZEBFZGZHACIZBFZACJBKFZUKUMUOUPSZUMUOUKUPUMUOUKUPSZUMUOHZACLFZUOURUSUNEM
    ZUTUMUOVAGUOVAULVAUOULUNEBNOPQACRUAUMUOUBUKUTUOUPUKUTUQUKUTHUOUPABCUCUDTUEU
    FTUGQUKUPUOSUMUKUPUOABCUHTUIUJ $.

  ${
    bj-isvec.scal $e |- ( ph -> K = ( Scalar ` V ) ) $.
    $( The predicate "is a vector space".  (Contributed by BJ, 6-Jan-2024.) $)
    bj-isvec $p |- ( ph -> ( V e. LVec <-> ( V e. LMod /\ K e. DivRing ) ) ) $=
      ( clvec wcel clmod csca cfv cdr eqid islvec eqcomd eleq1d anbi2d bitrid
      wa ) CEFCGFZCHIZJFZQARBJFZQSCSKLATUARASBJABSDMNOP $.
  $}

  $( Fields are division rings.  (Contributed by BJ, 6-Jan-2024.) $)
  bj-fldssdrng $p |- Field C_ DivRing $=
    ( cfield cdr ccrg cin df-field inss1 eqsstri ) ABCDBEBCFG $.

  $( Fields are division rings (elemental version).  (Contributed by BJ,
     9-Nov-2024.) $)
  bj-flddrng $p |- ( F e. Field -> F e. DivRing ) $=
    ( cfield cdr bj-fldssdrng sseli ) BCADE $.

  $( The field of real numbers is a division ring.  (Contributed by BJ,
     6-Jan-2024.) $)
  bj-rrdrg $p |- RRfld e. DivRing $=
    ( cfield cdr crefld bj-fldssdrng refld sselii ) ABCDEF $.

  ${
    bj-isclm.scal $e |- ( ph -> F = ( Scalar ` W ) ) $.
    bj-isclm.base $e |- ( ph -> K = ( Base ` F ) ) $.
    $( The predicate "is a subcomplex module".  (Contributed by BJ,
       6-Jan-2024.) $)
    bj-isclm $p |- ( ph -> ( W e. CMod <->
        ( W e. LMod /\ F = ( CCfld |`s K ) /\ K e. ( SubRing ` CCfld ) ) ) ) $=
      ( cclm wcel clmod csca cfv ccnfld cbs cress wceq csubrg w3a eqid eqcomd
      co isclm fveq2 wa eqtr syl2im mpd oveq2d eqeq12d eleq1d 3anbi23d bitrid
      ex ) DGHDIHZDJKZLUNMKZNTZOZUOLPKZHZQAUMBLCNTZOZCURHZQUNUODUNRUORUAAUQVAUS
      VBUMAUNBUPUTABUNESAUOCLNABUNOZUOCOZEACBMKZOZVCVEUOOZVDFBUNMUBVFVGVDVFVGUC
      CUOCVEUOUDSULUEUFZUGUHAUOCURVHUIUJUK $.
  $}

  $( Symbol for the class of real vector spaces. $)
  $c RRVec $.

  $( Syntax for the class of real vector spaces. $)
  crrvec $a class RRVec $.

  $( Definition of the class of real vector spaces.  The previous definition,
     ` |- RRVec = { x e. LMod | ( Scalar `` x ) = RRfld } ` , can be recovered
     using ~ bj-isrvec .  The present one is preferred since it does not use
     any dummy variable.  That ` RRVec ` could be defined with ` LVec ` in
     place of ` LMod ` is a consequence of ~ bj-isrvec2 .  (Contributed by BJ,
     9-Jun-2019.) $)
  df-bj-rvec $a |- RRVec = ( LMod i^i ( `' Scalar " { RRfld } ) ) $.

  $( The predicate "is a real vector space".  Using ~ df-sca instead of ~ scaid
     shortens the proof by two syntactic steps, but it is preferable not to
     rely on the precise definition ~ df-sca .  (Contributed by BJ,
     6-Jan-2024.) $)
  bj-isrvec $p |- ( V e. RRVec <-> ( V e. LMod /\ ( Scalar ` V ) = RRfld ) ) $=
    ( crrvec wcel clmod csca ccnv crefld csn cima wa wceq df-bj-rvec elin2 wfun
    cfv cdm wb cvv wfn cnx scaid slotfn df-fn mpbi elex eleq2 syl5ibrcom anim2d
    mpi fvimacnv syl fvex elsn bitr3di pm5.32i bitri ) ABCADCZAEFGHZIZCZJUQAEOZ
    GKZJADUSBLMUQUTVBUQVAURCZUTVBUQENZAEPZCZJZVCUTQUQVDVERKZJZVGERSVIETEOUAUBER
    UCUDUQVHVFVDUQVFVHARCADUEVERAUFUGUHUIAUREUJUKVAGAEULUMUNUOUP $.

  $( Real vector spaces are modules (elemental version).  (Contributed by BJ,
     6-Jan-2024.) $)
  bj-rvecmod $p |- ( V e. RRVec -> V e. LMod ) $=
    ( crrvec wcel clmod csca cfv crefld wceq bj-isrvec simplbi ) ABCADCAEFGHAIJ
    $.

  $( Real vector spaces are modules.  (Contributed by BJ, 6-Jan-2024.) $)
  bj-rvecssmod $p |- RRVec C_ LMod $=
    ( vx crrvec clmod cv bj-rvecmod ssriv ) ABCADEF $.

  $( The field of scalars of a real vector space is the field of real numbers.
     (Contributed by BJ, 6-Jan-2024.) $)
  bj-rvecrr $p |- ( V e. RRVec -> ( Scalar ` V ) = RRfld ) $=
    ( crrvec wcel clmod csca cfv crefld wceq bj-isrvec simprbi ) ABCADCAEFGHAIJ
    $.

  ${
    bj-isrvecd.scal $e |- ( ph -> ( Scalar ` V ) = K ) $.
    $( The predicate "is a real vector space".  (Contributed by BJ,
       6-Jan-2024.) $)
    bj-isrvecd $p |- ( ph -> ( V e. RRVec <-> ( V e. LMod /\ K = RRfld ) ) ) $=
      ( crrvec wcel clmod csca cfv crefld wceq bj-isrvec eqeq1d anbi2d bitrid
      wa ) CEFCGFZCHIZJKZPAQBJKZPCLASTQARBJDMNO $.
  $}

  $( Real vector spaces are vector spaces (elemental version).  (Contributed by
     BJ, 6-Jan-2024.) $)
  bj-rvecvec $p |- ( V e. RRVec -> V e. LVec ) $=
    ( crrvec wcel clvec clmod crefld cdr bj-rvecmod bj-rrdrg a1i csca bj-rvecrr
    cfv eqcomd bj-isvec mpbir2and ) ABCZADCAECFGCZAHRQIJQFAQAKMFALNOP $.

  ${
    bj-isrvec2.scal $e |- ( ph -> ( Scalar ` V ) = K ) $.
    $( The predicate "is a real vector space".  (Contributed by BJ,
       6-Jan-2024.) $)
    bj-isrvec2 $p |- ( ph -> ( V e. RRVec <-> ( V e. LVec /\ K = RRfld ) ) ) $=
      ( crrvec wcel clvec crefld wceq wa wi bj-rvecvec a1i cfv bj-rvecrr eqeq1d
      csca imbitrid jcad clmod bj-vecssmodel anim1i bj-isrvecd imbitrrid impbid
      ) ACEFZCGFZBHIZJZAUFUGUHUFUGKACLMUFCQNZHIAUHCOAUJBHDPRSUIUFACTFZUHJUGUKUH
      CUAUBABCDUCUDUE $.
  $}

  $( Real vector spaces are vector spaces.  (Contributed by BJ, 6-Jan-2024.) $)
  bj-rvecssvec $p |- RRVec C_ LVec $=
    ( vx crrvec clvec cv bj-rvecvec ssriv ) ABCADEF $.

  $( Real vector spaces are subcomplex modules (elemental version).
     (Contributed by BJ, 6-Jan-2024.) $)
  bj-rveccmod $p |- ( V e. RRVec -> V e. CMod ) $=
    ( crrvec wcel cclm clmod crefld ccnfld cr cress co wceq csubrg cfv df-refld
    bj-rvecmod a1i cdr resubdrg simpli csca bj-rvecrr eqcomd bj-isclm mpbir3and
    cbs rebase ) ABCZADCAECFGHIJKZHGLMCZAOUHUGNPUIUGUIFQCRSPUGFHAUGATMFAUAUBHFU
    EMKUGUFPUCUD $.

  $( Real vector spaces are subcomplex modules.  (Contributed by BJ,
     6-Jan-2024.) $)
  bj-rvecsscmod $p |- RRVec C_ CMod $=
    ( vx crrvec cclm cv bj-rveccmod ssriv ) ABCADEF $.

  $( Real vector spaces are subcomplex vector spaces.  (Contributed by BJ,
     6-Jan-2024.) $)
  bj-rvecsscvec $p |- RRVec C_ CVec $=
    ( crrvec cclm clvec ccvs bj-rvecsscmod bj-rvecssvec ssini df-cvs sseqtrri
    cin ) ABCJDABCEFGHI $.

  $( Real vector spaces are subcomplex vector spaces (elemental version).
     (Contributed by BJ, 6-Jan-2024.) $)
  bj-rveccvec $p |- ( V e. RRVec -> V e. CVec ) $=
    ( crrvec ccvs bj-rvecsscvec sseli ) BCADE $.

  $( (The additive groups of) real vector spaces are commutative groups.
     (Contributed by BJ, 9-Jun-2019.) $)
  bj-rvecssabl $p |- RRVec C_ Abel $=
    ( crrvec clmod cabl bj-rvecssmod bj-modssabl sstri ) ABCDEF $.

  $( (The additive groups of) real vector spaces are commutative groups
     (elemental version).  (Contributed by BJ, 9-Jun-2019.) $)
  bj-rvecabl $p |- ( A e. RRVec -> A e. Abel ) $=
    ( crrvec cabl bj-rvecssabl sseli ) BCADE $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Complex numbers (supplements)
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  Some lemmas to ease algebraic manipulations.

$)

  ${
    bj-subcom.a $e |- ( ph -> A e. CC ) $.
    bj-subcom.b $e |- ( ph -> B e. CC ) $.
    $( A consequence of commutativity of multiplication.  (Contributed by BJ,
       6-Jun-2019.) $)
    bj-subcom $p |- ( ph -> ( ( A x. B ) - ( B x. A ) ) = 0 ) $=
      ( cmul co mulcld mulcomd subeq0bd ) ABCFGCBFGABCDEHABCDEIJ $.
  $}

  ${
    bj-lineqi.a $e |- ( ph -> A e. CC ) $.
    bj-lineqi.b $e |- ( ph -> B e. CC ) $.
    bj-lineqi.x $e |- ( ph -> X e. CC ) $.
    bj-lineqi.y $e |- ( ph -> Y e. CC ) $.
    bj-lineqi.n0 $e |- ( ph -> A =/= 0 ) $.
    bj-lineqi.1 $e |- ( ph -> ( ( A x. X ) + B ) = Y ) $.
    $( Solution of a (scalar) linear equation.  (Contributed by BJ,
       6-Jun-2019.) $)
    bj-lineqi $p |- ( ph -> X = ( ( Y - B ) / A ) ) $=
      ( cmul co caddc wceq cmin cdiv lineq mpbid ) ABDLMCNMEODECPMBQMOKABCDEFGH
      IJRS $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Barycentric coordinates
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  Lemmas about barycentric coordinates.  For the moment, this is limited to the
  one-dimensional case (complex line), where existence and uniqueness of
  barycentric coordinates are proved by ~ bj-bary1 (which computes them).  It
  would be nice to prove the two-dimensional case (is it easier to use ad hoc
  computations, or Cramer formulas?), in order to do some planar geometry.

$)

  ${
    bj-bary1.a $e |- ( ph -> A e. CC ) $.
    bj-bary1.b $e |- ( ph -> B e. CC ) $.
    bj-bary1.x $e |- ( ph -> X e. CC ) $.
    bj-bary1.neq $e |- ( ph -> A =/= B ) $.
    $( Lemma for ~ bj-bary1 : expression for a barycenter of two points in one
       dimension (complex line).  (Contributed by BJ, 6-Jun-2019.) $)
    bj-bary1lem $p |- ( ph -> X = ( ( ( ( B - X ) / ( B - A ) ) x. A ) +
                                      ( ( ( X - A ) / ( B - A ) ) x. B ) ) ) $=
      ( cmin co cmul cdiv caddc cc0 mulcld subcld oveq1d eqtrd subdird oveq12d
      addsub12d sub32d bj-subcom oveq2d 0cnd addsubassd addridd subdid 3eqtr4rd
      3eqtr2d necomd subne0d divdird divcan4d div23d 3eqtr3d ) ADCBIJZKJZUQLJZC
      DIJZBKJZUQLJZDBIJZCKJZUQLJZMJZDUTUQLJBKJZVCUQLJCKJZMJAUSVAVDMJZUQLJVFAURV
      IUQLACBKJZDBKJZIJZDCKJZBCKJZIJZMJZVMVKIJZVIURAVPVMNVKIJZMJZVMNMJZVKIJVQAV
      PVMVLVNIJZMJVSAVLVMVNAVJVKACBFEOZADBGEOZPADCGFOZABCEFOZUAAWAVRVMMAWAVJVNI
      JZVKIJVRAVJVKVNWBWCWEUBAWFNVKIACBFEUCQRUDRAVMNVKWDAUEWCUFAVTVMVKIAVMWDUGQ
      UJAVAVLVDVOMACDBFGESADBCGEFSTADCBGFEUHUIQAVAVDUQAUTBACDFGPZEOAVCCADBGEPZF
      OACBFEPZACBFEABCHUKULZUMRADUQGWIWJUNAVBVGVEVHMAUTBUQWGEWIWJUOAVCCUQWHFWIW
      JUOTUP $.

    bj-bary1.s $e |- ( ph -> S e. CC ) $.
    bj-bary1.t $e |- ( ph -> T e. CC ) $.
    $( Lemma for ~ bj-bary1 : computation of one of the two barycentric
       coordinates of a barycenter of two points in one dimension (complex
       line).  (Contributed by BJ, 6-Jun-2019.) $)
    bj-bary1lem1 $p |- ( ph ->
                ( ( X = ( ( S x. A ) + ( T x. B ) ) /\ ( S + T ) = 1 ) ->
                                           T = ( ( X - A ) / ( B - A ) ) ) ) $=
      ( cmul co caddc wceq c1 wa cmin oveq1 cdiv wi pncand pm5.31 sylancl eqtr2
      eqcomd syl6 oveq1d eqtr sylan2 subdird mullidd eqtrd sylan9eqr ex sylan2d
      1cnd mulcld subadd23d subdid oveq2d eqeq2d sylibd subcld pncan2d imbitrid
      eqcom mulcomd eqeq1d necomd subne0d rdiv biimpd sylbid biimtrid 3syld ) A
      FDBMNZECMNZONZPZDEONZQPZRZFBECBSNZMNZONZPZFBSNZWFPZEWIWEUANPZAWDFBEBMNZSN
      ZVSONZPZWHAWCDQESNZPZWAWOAWCWBESNZWPPZWRDPZRZWQAWTWCWSUBWCXAUBADEKLUCWBQE
      STWCWSWTUDUEXAWPDWRWPDUFUGUHAWAWQRZWOXBAFWPBMNZVSONZWNWQWAVTXDPFXDPWQVRXC
      VSODWPBMTUIFVTXDUJUKAXCWMVSOAXCQBMNZWLSNWMAQEBAURLGULAXEBWLSABGUMUIUNUIUO
      UPUQAWNWGFAWNBVSWLSNZONWGABWLVSGAEBLGUSAECLHUSUTAXFWFBOAWFXFAECBLHGVAUGVB
      UNVCVDWHWIWGBSNZPAWJFWGBSTAXGWFWIABWFGAEWELACBHGVEZUSVFVCVGWJWFWIPZAWKWIW
      FVHAXIWEEMNZWIPZWKAWFXJWIAEWELXHVIVJAXKWKAWEEWIXHLAFBIGVEACBHGABCJVKVLVMV
      NVOVPVQ $.

    $( Barycentric coordinates in one dimension (complex line).  In the
       statement, ` X ` is the barycenter of the two points ` A , B ` with
       respective normalized coefficients ` S , T ` .  (Contributed by BJ,
       6-Jun-2019.) $)
    bj-bary1 $p |- ( ph ->
            ( ( X = ( ( S x. A ) + ( T x. B ) ) /\ ( S + T ) = 1 ) <->
      ( S = ( ( B - X ) / ( B - A ) ) /\ T = ( ( X - A ) / ( B - A ) ) ) ) ) $=
      ( cmul co caddc wceq c1 cmin cdiv eqeq2d wa mulcld addcomd biimpd syl2and
      eqeq1d necomd bj-bary1lem1 div2subd sylibd bj-bary1lem wi oveq1 oveqan12d
      jcad eqtr3 syl6an oveq12 subcld subne0d divdird npncand diveq1bd imbitrid
      a1i eqtr3d impbid ) AFDBMNZECMNZONZPZDEONZQPZUAZDCFRNZCBRNZSNZPZEFBRNZVPS
      NZPZUAZAVNVRWAAVNDFCRNBCRNSNZPZVRAVKFVIVHONZPZVMEDONZQPZWDAVKWFAVJWEFAVHV
      IADBKGUBAECLHUBUCTUDAVMWHAVLWGQADEKLUCUFUDACBEDFHGIABCJUGZLKUHUEAWCVQDAFC
      BCIHGHJUITUJABCDEFGHIJKLUHUOAWBVKVMAFVQBMNZVTCMNZONZPWBVJWLPZVKABCFGHIJUK
      WBWMULAVRWAVHWJVIWKODVQBMUMEVTCMUMUNVEFVJWLUPUQWBVLVQVTONZPAVMDVQEVTOURAW
      NQVLAVOVSONZVPSNWNQAVOVSVPACFHIUSAFBIGUSACBHGUSZACBHGWIUTZVAAWOVPWPWQACFB
      HIGVBVCVFTVDUOVG $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Monoid of endomorphisms
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c End $.
  $( Token for the monoid of endomorphisms. $)
  cend $a class End $. $( Syntax for the monoid of endomorphisms. $)

  ${
    $d c x $.
    $( The monoid of endomorphisms on an object of a category.  (Contributed by
       BJ, 4-Apr-2024.) $)
    df-bj-end $a |- End = ( c e. Cat |-> ( x e. ( Base ` c ) |->
                 { <. ( Base ` ndx ) , ( x ( Hom ` c ) x ) >. ,
                   <. ( +g ` ndx ) , ( <. x , x >. ( comp ` c ) x ) >. } ) ) $.
  $}

  ${
    $d C c x $.  $d X c x $.  $d ph c x $.
    bj-endval.c $e |- ( ph -> C e. Cat ) $.
    bj-endval.x $e |- ( ph -> X e. ( Base ` C ) ) $.
    $( Value of the monoid of endomorphisms on an object of a category.
       (Contributed by BJ, 5-Apr-2024.)
       (Proof modification is discouraged.) $)
    bj-endval $p |- ( ph -> ( ( End ` C ) ` X ) =
                   { <. ( Base ` ndx ) , ( X ( Hom ` C ) X ) >. ,
                     <. ( +g ` ndx ) , ( <. X , X >. ( comp ` C ) X ) >. } ) $=
      ( vx vc cnx cbs cfv cv chom co cop cco cpr cvv wceq fveq2 opeq2d cend a1i
      cplusg cmpt ccat df-bj-end preq12d mpteq12dv wcel fvex fvmptd3 id oveq12d
      oveqd mptex opeq12d adantl prex fvmptd ) AFCHIJZFKZVABLJZMZNZHUCJZVAVANZV
      ABOJZMZNZPZUTCCVBMZNZVECCNZCVGMZNZPZBIJZBUAJQAGBFGKZIJZUTVAVAVRLJZMZNZVEV
      FVAVROJZMZNZPZUDFVQVJUDZUEUAQFGUFVRBRZFVSWFVQVJVRBISWHWBVDWEVIWHWAVCUTWHV
      TVBVAVAVRBLSUNTWHWDVHVEWHWCVGVFVAVRBOSUNTUGUHDWGQUIAFVQVJBIUJUOUBUKVACRZV
      JVPRAWIVDVLVIVOWIVCVKUTWIVACVACVBWIULZWJUMTWIVHVNVEWIVFVMVACVGWIVACVACWJW
      JUPWJUMTUGUQEVPQUIAVLVOURUBUS $.

    $( Base set of the monoid of endomorphisms on an object of a category.
       (Contributed by BJ, 5-Apr-2024.)
       (Proof modification is discouraged.) $)
    bj-endbase $p |- ( ph ->
                      ( Base ` ( ( End ` C ) ` X ) ) = ( X ( Hom ` C ) X ) ) $=
      ( cend cfv cbs cnx chom co cop cplusg cco cpr cvv fvexd strfvnd bj-endval
      baseid fveq1d wne wceq basendxnplusgndx fvex ovex fvpr1 mp1i 3eqtrd ) ACB
      FGZGZHGIHGZUKGULULCCBJGZKZLIMGZCCLCBNGKZLOZGZUNAUKHULPTACUJQRAULUKUQABCDE
      SUAULUOUBURUNUCAUDULUOUNUPIHUECCUMUFUGUHUI $.

    $( Composition law of the monoid of endomorphisms on an object of a
       category.  (Contributed by BJ, 5-Apr-2024.)
       (Proof modification is discouraged.) $)
    bj-endcomp $p |- ( ph ->
             ( +g ` ( ( End ` C ) ` X ) ) = ( <. X , X >. ( comp ` C ) X ) ) $=
      ( cend cfv cplusg cnx cbs chom co cop cco cpr cvv plusgid fvexd bj-endval
      strfvnd fveq1d wne wceq basendxnplusgndx fvex ovex fvpr2 mp1i 3eqtrd ) AC
      BFGZGZHGIHGZUKGULIJGZCCBKGLZMULCCMZCBNGZLZMOZGZUQAUKHULPQACUJRTAULUKURABC
      DESUAUMULUBUSUQUCAUDUMULUNUQIHUEUOCUPUFUGUHUI $.

    $d C x y z $.  $d X x y z $.  $d ph x y z $.
    $( The monoid of endomorphisms on an object of a category is a monoid.
       (Contributed by BJ, 5-Apr-2024.)
       (Proof modification is discouraged.) $)
    bj-endmnd $p |- ( ph -> ( ( End ` C ) ` X ) e. Mnd ) $=
      ( vx vy vz cfv co cbs eqcomd cv wcel w3a eqid 3ad2ant1 simp3 adantr syl
      chom cop cco cend ccid bj-endbase cplusg bj-endcomp ccat simp2 catcocl wa
      simpr simp1 catass catidcl catlid catrid ismndd ) AFGHCCBUAIZJZCCUBCBUCIZ
      JZCBUDIIZCBUEIZIAVDKIVAABCDEUFLAVDUGIVCABCDEUHLAFMZVANZGMZVANZOBKIZBVBVHV
      FUTCCCVJPZUTPZVBPZAVGBUINZVIDQAVGCVJNZVIEQZVPVPAVGVIRAVGVIUJUKAVGVIHMZVAN
      ZOZULZVJBVBVQVHUTVFCCCCVKVLVMAVNVSDSAVOVSESZWAWAVTVSVRAVSUMZVGVIVRRTVTVSV
      IWBVGVIVRUJTWAVTVSVGWBVGVIVRUNTUOAVJBVEUTCVKVLVEPZDEUPAVGULZVJBVBVEVFUTCC
      VKVLWCAVNVGDSZAVOVGESZVMWFAVGUMZUQWDVJBVBVEVFUTCCVKVLWCWEWFVMWFWGURUS $.
  $}

$( (End of BJ's mathbox.) $)
