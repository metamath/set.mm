$[ set-main.mm $]
$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Mathbox for Jarvin Udandy
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

  $( Table of Contents [ Search Code: pyY6vpz5mecT2rh9 ]
   Table of Contents for MathBox

   Note: All search codes are randomly generated strings.

   0| Table of Contents [ Search Code: pyY6vpz5mecT2rh9 ]
   1| Preface for Mathbox [ Search Code: gmFp93ENa4XAkymc ]
   2| Main Section [ Search Code: MnBcpxXHRCLsx9Bj ]
    -Propositional Calculus
   3| Experimental Section [ Search Code: 6hFY3NX45ggpE7Hx ]
        -Propositional Calculus
    - ?
  $)

  $( PREFACE FOR MATHBOX [ Search Code: gmFp93ENa4XAkymc ]

    Aim: Prove interesting results, personally meaningful results, or
    supplement set.mm as much as possible.

    The order of declaring things:
    variables, wffs, constants, definitions, followed by
    broad-use-formulas, and lastly more subject-specific results.

    Occasionally grouping like-formulas when sensible.
  $)

  $( BEGIN MAIN SECTION [ Search Code: MnBcpxXHRCLsx9Bj ]
   This section of the mathbox is for official results.
  $)

  $v jph $.  $( jarvin Greek phi $)
  $v jps $.  $( jarvin Greek psi $)
  $v jch $.  $( jarvin Greek chi $)
  $v jth $.  $( jarvin Greek theta $)
  $v jta $.  $( jarvin Greek tau $)
  $v jet $.  $( jarvin Greek eta $)
  $v jze $.  $( jarvin Greek zeta $)
  $v jsi $.  $( jarvin Greek sigma $)
  $v jrh $.  $( jarvin Greek rho $)
  $v jmu $.  $( jarvin Greek mu $)
  $v jla $.  $( jarvin Greek lambda $)

  $( Let variable ` jph ` be a wff. $)
  wjph $f wff jph $.
  $( Let variable ` jps ` be a wff. $)
  wjps $f wff jps $.
  $( Let variable ` jch ` be a wff. $)
  wjch $f wff jch $.
  $( Let variable ` jth ` be a wff. $)
  wjth $f wff jth $.
  $( Let variable ` jta ` be a wff. $)
  wjta $f wff jta $.
  $( Let variable ` jet ` be a wff. $)
  wjet $f wff jet $.
  $( Let variable ` jze ` be a wff. $)
  wjze $f wff jze $.
  $( Let variable ` jsi ` be a wff. $)
  wjsi $f wff jsi $.
  $( Let variable ` jrh ` be a wff. $)
  wjrh $f wff jrh $.
  $( Let variable ` jmu ` be a wff. $)
  wjmu $f wff jmu $.
  $( Let variable ` jla ` be a wff. $)
  wjla $f wff jla $.

  $( The third axiom of a system called "L" but proven to be a theorem since
     set.mm uses a different third axiom.  This is named hirst after Holly P.
     Hirst and Jeffry L. Hirst.  Axiom A3 of [Mendelson] p. 35.  (Contributed
     by Jarvin Udandy, 7-Feb-2015.)  (Proof modification is discouraged.) $)
  hirstL-ax3 $p |- ( ( -. ph -> -. ps ) -> ( ( -. ph -> ps ) -> ph ) ) $=
    ( wn wi wo pm4.64 pm4.66 pm2.64 com12 sylbi biimtrid ) ACZBDABEZLBCZDZAABFO
    ANEZMADABGMPAABHIJK $.

  $( Recover ~ ax-3 from ~ hirstL-ax3 .  (Contributed by Jarvin Udandy,
     3-Jul-2015.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  ax3h $p |- ( ( -. ph -> -. ps ) -> ( ps -> ph ) ) $=
    ( wn wi hirstL-ax3 jarr syl ) ACZBCDHBDADBADABEHBAFG $.

  $( A closed form showing (a implies b and b implies a) same-as (a same-as b).
     (Contributed by Jarvin Udandy, 3-Sep-2016.) $)
  aibandbiaiffaiffb $p |- ( ( ( ph -> ps ) /\ ( ps -> ph ) ) <->
( ph <-> ps ) ) $=
    ( wb wi wa dfbi2 bicomi ) ABCABDBADEABFG $.

  $( A closed form showing (a implies b and b implies a) implies (a same-as b).
     (Contributed by Jarvin Udandy, 3-Sep-2016.) $)
  aibandbiaiaiffb $p |- ( ( ( ph -> ps ) /\ ( ps -> ph ) ) ->
( ph <-> ps ) ) $=
    ( wb wi wa dfbi2 biimpri ) ABCABDBADEABFG $.

  ${
    notatnand.1 $e |- -. ph $.
    $( Do not use.  Use intnanr instead.  Given not a, there exists a proof for
       not (a and b).  (Contributed by Jarvin Udandy, 31-Aug-2016.) $)
    notatnand $p |- -. ( ph /\ ps ) $=
      ( intnanr ) ABCD $.
  $}

  ${
    aistia.1 $e |- ( ph <-> T. ) $.
    $( Given a is equivalent to ` T. ` , there exists a proof for a.
       (Contributed by Jarvin Udandy, 30-Aug-2016.) $)
    aistia $p |- ph $=
      ( wtru wb tbtru mpbir ) AACDBAEF $.
  $}

  ${
    aisfina.1 $e |- ( ph <-> F. ) $.
    $( Given a is equivalent to ` F. ` , there exists a proof for not a.
       (Contributed by Jarvin Udandy, 30-Aug-2016.) $)
    aisfina $p |- -. ph $=
      ( wn wfal wb nbfal mpbir ) ACADEBAFG $.
  $}

  ${
    bothtbothsame.1 $e |- ( ph <-> T. ) $.
    bothtbothsame.2 $e |- ( ps <-> T. ) $.
    $( Given both a, b are equivalent to ` T. ` , there exists a proof for a is
       the same as b.  (Contributed by Jarvin Udandy, 31-Aug-2016.) $)
    bothtbothsame $p |- ( ph <-> ps ) $=
      ( wtru bitr4i ) AEBCDF $.
  $}

  ${
    bothfbothsame.1 $e |- ( ph <-> F. ) $.
    bothfbothsame.2 $e |- ( ps <-> F. ) $.
    $( Given both a, b are equivalent to ` F. ` , there exists a proof for a is
       the same as b.  (Contributed by Jarvin Udandy, 31-Aug-2016.) $)
    bothfbothsame $p |- ( ph <-> ps ) $=
      ( wfal bitr4i ) AEBCDF $.
  $}

  ${
    aiffbbtat.1 $e |- ( ph <-> ps ) $.
    aiffbbtat.2 $e |- ( ps <-> T. ) $.
    $( Given a is equivalent to b, b is equivalent to ` T. ` there exists a
       proof for a is equivalent to T. (Contributed by Jarvin Udandy,
       29-Aug-2016.) $)
    aiffbbtat $p |- ( ph <-> T. ) $=
      ( wtru bitri ) ABECDF $.
  $}

  ${
    aisbbisfaisf.1 $e |- ( ph <-> ps ) $.
    aisbbisfaisf.2 $e |- ( ps <-> F. ) $.
    $( Given a is equivalent to b, b is equivalent to ` F. ` there exists a
       proof for a is equivalent to F. (Contributed by Jarvin Udandy,
       30-Aug-2016.) $)
    aisbbisfaisf $p |- ( ph <-> F. ) $=
      ( wfal bitri ) ABECDF $.
  $}

  ${
    axorbtnotaiffb.1 $e |- ( ph \/_ ps ) $.
    $( Given a is exclusive to b, there exists a proof for (not (a
       if-and-only-if b)); ~ df-xor is a closed form of this.  (Contributed by
       Jarvin Udandy, 7-Sep-2016.) $)
    axorbtnotaiffb $p |- -. ( ph <-> ps ) $=
      ( wxo wb wn df-xor mpbi ) ABDABEFCABGH $.
  $}

  ${
    aiffnbandciffatnotciffb.1 $e |- ( ph <-> -. ps ) $.
    aiffnbandciffatnotciffb.2 $e |- ( ch <-> ph ) $.
    $( Given a is equivalent to (not b), c is equivalent to a, there exists a
       proof for ( not ( c iff b ) ).  (Contributed by Jarvin Udandy,
       7-Sep-2016.) $)
    aiffnbandciffatnotciffb $p |- -. ( ch <-> ps ) $=
      ( wb wn bitri xor3 mpbir ) CBFGCBGZFCAKEDHCBIJ $.
  $}

  ${
    axorbciffatcxorb.1 $e |- ( ph \/_ ps ) $.
    axorbciffatcxorb.2 $e |- ( ch <-> ph ) $.
    $( Given a is equivalent to (not b), c is equivalent to a. there exists a
       proof for ( c xor b ).  (Contributed by Jarvin Udandy, 7-Sep-2016.) $)
    axorbciffatcxorb $p |- ( ch \/_ ps ) $=
      ( wxo wb wn axorbtnotaiffb xor3 mpbi aiffnbandciffatnotciffb df-xor mpbir
      ) CBFCBGHABCABGHABHGABDIABJKELCBMN $.
  $}

  ${
    aibnbna.1 $e |- ( ph -> ps ) $.
    aibnbna.2 $e |- -. ps $.
    $( Given a implies b, (not b), there exists a proof for (not a).
       (Contributed by Jarvin Udandy, 1-Sep-2016.) $)
    aibnbna $p |- -. ph $=
      ( mto ) ABDCE $.
  $}

  ${
    aibnbaif.1 $e |- ( ph -> ps ) $.
    aibnbaif.2 $e |- -. ps $.
    $( Given a implies b, not b, there exists a proof for a is F. (Contributed
       by Jarvin Udandy, 1-Sep-2016.) $)
    aibnbaif $p |- ( ph <-> F. ) $=
      ( aibnbna bifal ) AABCDEF $.
  $}

  ${
    aiffbtbat.1 $e |- ( ph <-> ps ) $.
    aiffbtbat.2 $e |- ( T. <-> ps ) $.
    $( Given a is equivalent to b, T. is equivalent to b. there exists a proof
       for a is equivalent to T. (Contributed by Jarvin Udandy,
       29-Aug-2016.) $)
    aiffbtbat $p |- ( ph <-> T. ) $=
      ( wtru bitr4i ) ABECDF $.
  $}

  ${
    astbstanbst.1 $e |- ( ph <-> T. ) $.
    astbstanbst.2 $e |- ( ps <-> T. ) $.
    $( Given a is equivalent to T., also given that b is equivalent to T, there
       exists a proof for a and b is equivalent to T. (Contributed by Jarvin
       Udandy, 29-Aug-2016.) $)
    astbstanbst $p |- ( ( ph /\ ps ) <-> T. ) $=
      ( wa aistia pm3.2i bitru ) ABEABACFBDFGH $.
  $}

  ${
    aistbistaandb.1 $e |- ( ph <-> T. ) $.
    aistbistaandb.2 $e |- ( ps <-> T. ) $.
    $( Given a is equivalent to T., also given that b is equivalent to T, there
       exists a proof for (a and b).  (Contributed by Jarvin Udandy,
       9-Sep-2016.) $)
    aistbistaandb $p |- ( ph /\ ps ) $=
      ( aistia pm3.2i ) ABACEBDEF $.
  $}

  ${
    aisbnaxb.1 $e |- ( ph <-> ps ) $.
    $( Given a is equivalent to b, there exists a proof for (not (a xor b)).
       (Contributed by Jarvin Udandy, 28-Aug-2016.) $)
    aisbnaxb $p |- -. ( ph \/_ ps ) $=
      ( wxo wb wn notnoti df-xor mtbir ) ABDABEZFJCGABHI $.
  $}

  $( If a implies b, then a implies not not b.  (Contributed by Jarvin Udandy,
     28-Aug-2016.) $)
  atbiffatnnb $p |- ( ( ph -> ps ) -> ( ph -> -. -. ps ) ) $=
    ( wn idd notnotb imbitrdi a2i ) ABBCCZABBHABDBEFG $.

  $( Application of bicom1 with a, b swapped.  (Contributed by Jarvin Udandy,
     31-Aug-2016.) $)
  bisaiaisb $p |- ( ( ps <-> ph ) -> ( ph <-> ps ) ) $=
    ( bicom1 ) BAC $.

  $( If a implies b, then a implies not not b.  (Contributed by Jarvin Udandy,
     29-Aug-2016.) $)
  atbiffatnnbalt $p |- ( ( ph -> ps ) -> ( ph -> -. -. ps ) ) $=
    ( atbiffatnnb ) ABC $.

  ${
    abnotbtaxb.1 $e |- ph $.
    abnotbtaxb.2 $e |- -. ps $.
    $( Assuming a, not b, there exists a proof a-xor-b.)  (Contributed by
       Jarvin Udandy, 31-Aug-2016.) $)
    abnotbtaxb $p |- ( ph \/_ ps ) $=
      ( wxo wb wn wa xor3 wi pm5.1 ibibr mpbi mp2an bitri mpbir2an df-xor mpbir
      ) ABEABFGZSABGZCDSATFZATHZABIATUAUBFZCDUBUAJUBUCJATKUBUALMNOPABQR $.
  $}

  ${
    abnotataxb.1 $e |- -. ph $.
    abnotataxb.2 $e |- ps $.
    $( Assuming not a, b, there exists a proof a-xor-b.)  (Contributed by
       Jarvin Udandy, 31-Aug-2016.) $)
    abnotataxb $p |- ( ph \/_ ps ) $=
      ( wxo wb wn wa wo pm3.2i olci xor mpbir df-xor ) ABEABFGZOABGHZBAGZHZIRPB
      QDCJKABLMABNM $.
  $}

  ${
    conimpf.1 $e |- ph $.
    conimpf.2 $e |- -. ps $.
    conimpf.3 $e |- ( ph -> ps ) $.
    $( Assuming a, not b, and a implies b, there exists a proof that a is
       false.)  (Contributed by Jarvin Udandy, 28-Aug-2016.) $)
    conimpf $p |- ( ph <-> F. ) $=
      ( aibnbaif ) ABEDF $.
  $}

  ${
    conimpfalt.1 $e |- ph $.
    conimpfalt.2 $e |- -. ps $.
    conimpfalt.3 $e |- ( ph -> ps ) $.
    $( Assuming a, not b, and a implies b, there exists a proof that a is
       false.)  (Contributed by Jarvin Udandy, 29-Aug-2016.) $)
    conimpfalt $p |- ( ph <-> F. ) $=
      ( aibnbaif ) ABEDF $.
  $}

  ${
    aistbisfiaxb.1 $e |- ( ph <-> T. ) $.
    aistbisfiaxb.2 $e |- ( ps <-> F. ) $.
    $( Given a is equivalent to T., Given b is equivalent to F. there exists a
       proof for a-xor-b.  (Contributed by Jarvin Udandy, 31-Aug-2016.) $)
    aistbisfiaxb $p |- ( ph \/_ ps ) $=
      ( aistia aisfina abnotbtaxb ) ABACEBDFG $.
  $}

  ${
    aisfbistiaxb.1 $e |- ( ph <-> F. ) $.
    aisfbistiaxb.2 $e |- ( ps <-> T. ) $.
    $( Given a is equivalent to F., Given b is equivalent to T., there exists a
       proof for a-xor-b.  (Contributed by Jarvin Udandy, 31-Aug-2016.) $)
    aisfbistiaxb $p |- ( ph \/_ ps ) $=
      ( aisfina aistia abnotataxb ) ABACEBDFG $.
  $}

  ${
    aifftbifffaibif.1 $e |- ( ph <-> T. ) $.
    aifftbifffaibif.2 $e |- ( ps <-> F. ) $.
    $( Given a is equivalent to T., Given b is equivalent to F., there exists a
       proof for that a implies b is false.  (Contributed by Jarvin Udandy,
       7-Sep-2020.) $)
    aifftbifffaibif $p |- ( ( ph -> ps ) <-> F. ) $=
      ( wi wn wa aistia aisfina pm3.2i annim biimpi ax-mp bifal ) ABEZABFZGZOFZ
      APACHBDIJQRABKLMN $.
  $}

  ${
    aifftbifffaibifff.1 $e |- ( ph <-> T. ) $.
    aifftbifffaibifff.2 $e |- ( ps <-> F. ) $.
    $( Given a is equivalent to T., Given b is equivalent to F., there exists a
       proof for that a iff b is false.  (Contributed by Jarvin Udandy,
       7-Sep-2020.) $)
    aifftbifffaibifff $p |- ( ( ph <-> ps ) <-> F. ) $=
      ( wb wn wfal aistia aisfina abnotbtaxb axorbtnotaiffb nbfal biimpi ax-mp
      ) ABEZFZOGEZABABACHBDIJKPQOLMN $.
  $}

  ${
    atnaiana.1 $e |- ph $.
    $( Given a, it is not the case a implies a self contradiction.
       (Contributed by Jarvin Udandy, 7-Sep-2020.) $)
    atnaiana $p |- -. ( ph -> ( ph /\ -. ph ) ) $=
      ( wn wa wi bitru pm3.24 bifal aifftbifffaibif aisfina ) AAACDZEAKABFKAGHI
      J $.
  $}

  ${
    ainaiaandna.1 $e |- ph $.
    $( Given a, a implies it is not the case a implies a self contradiction.
       (Contributed by Jarvin Udandy, 7-Sep-2020.) $)
    ainaiaandna $p |- ( ph -> -. ( ph -> ( ph /\ -. ph ) ) ) $=
      ( wn wa wi atnaiana a1i ) AAACDECAABFG $.
  $}

  ${
    abcdta.1 $e |- ( ( ( ph /\ ps ) /\ ch ) /\ th ) $.
    $( Given (((a and b) and c) and d), there exists a proof for a.
       (Contributed by Jarvin Udandy, 3-Sep-2016.) $)
    abcdta $p |- ph $=
      ( wa simpli ) ABABFZCHCFDEGGG $.
  $}

  ${
    abcdtb.1 $e |- ( ( ( ph /\ ps ) /\ ch ) /\ th ) $.
    $( Given (((a and b) and c) and d), there exists a proof for b.
       (Contributed by Jarvin Udandy, 3-Sep-2016.) $)
    abcdtb $p |- ps $=
      ( wa simpli simpri ) ABABFZCICFDEGGH $.
  $}

  ${
    abcdtc.1 $e |- ( ( ( ph /\ ps ) /\ ch ) /\ th ) $.
    $( Given (((a and b) and c) and d), there exists a proof for c.
       (Contributed by Jarvin Udandy, 3-Sep-2016.) $)
    abcdtc $p |- ch $=
      ( wa simpli simpri ) ABFZCICFDEGH $.
  $}

  ${
    abcdtd.1 $e |- ( ( ( ph /\ ps ) /\ ch ) /\ th ) $.
    $( Given (((a and b) and c) and d), there exists a proof for d.
       (Contributed by Jarvin Udandy, 3-Sep-2016.) $)
    abcdtd $p |- th $=
      ( wa simpri ) ABFCFDEG $.
  $}

  $( Operands in a biconditional expression converted negated.  Additionally
     biconditional converted to show antecedent implies sequent.  Closed form.
     (Contributed by Jarvin Udandy, 7-Sep-2020.) $)
  abciffcbatnabciffncba $p |- ( -. ( ( ph /\ ps ) /\ ch ) -> -. ( ( ch /\
ps ) /\ ph ) ) $=
    ( wa wn wb an31 notbi biimpi ax-mp ) ABDCDZEZCBDADZEZKMFZLNFZABCGOPKMHIJI
    $.

  ${
    abciffcbatnabciffncbai.1 $e |- ( ( ( ph /\ ps ) /\ ch ) <-> ( ( ch /\ ps )
/\ ph ) ) $.
    $( Operands in a biconditional expression converted negated.  Additionally
       biconditional converted to show antecedent implies sequent.
       (Contributed by Jarvin Udandy, 7-Sep-2020.) $)
    abciffcbatnabciffncbai $p |- ( -. ( ( ph /\ ps ) /\ ch ) -> -. ( ( ch /\ ps
 ) /\ ph ) ) $=
      ( wa wn wb notbi biimpi ax-mp ) ABECEZFZCBEAEZFZKMGZLNGZDOPKMHIJI $.
  $}

  ${
    nabctnabc.1 $e |- -. ( ph -> ( ps /\ ch ) ) $.
    $( not ( a -> ( b /\ c ) ) we can show: not a implies ( b /\ c ).
       (Contributed by Jarvin Udandy, 7-Sep-2020.) $)
    nabctnabc $p |- ( -. ph -> ( ps /\ ch ) ) $=
      ( wn wa wb wi pm4.61 biimpi ax-mp simpli simpri 2th bicom con3i notnotrd
      ) AEBCFZREZASAASGZSAGZASASARHEZASFZDUBUCARIJKZLASUDMNTUAASOJKJPQ $.
  $}

  ${
    jabtaib.1 $e |- ( ph /\ ps ) $.
    $( For when pm3.4 lacks a pm3.4i.  (Contributed by Jarvin Udandy,
       9-Sep-2020.) $)
    jabtaib $p |- ( ph -> ps ) $=
      ( wa wi pm3.4 ax-mp ) ABDABECABFG $.
  $}

  ${
    onenotinotbothi.1 $e |- -. ( ph -> ps ) $.
    $( From one negated implication it is not the case its nonnegated form and
       a random others are both true.  (Contributed by Jarvin Udandy,
       11-Sep-2020.) $)
    onenotinotbothi $p |- -. ( ( ph -> ps ) /\ ( ch -> th ) ) $=
      ( wi wn wo wa orci pm3.14 ax-mp ) ABFZGZCDFZGZHMOIGNPEJMOKL $.
  $}

  ${
    twonotinotbothi.1 $e |- -. ( ph -> ps ) $.
    twonotinotbothi.2 $e |- -. ( ch -> th ) $.
    $( From these two negated implications it is not the case their nonnegated
       forms are both true.  (Contributed by Jarvin Udandy, 11-Sep-2020.) $)
    twonotinotbothi $p |- -. ( ( ph -> ps ) /\ ( ch -> th ) ) $=
      ( wi wn wo wa orci pm3.14 ax-mp ) ABGZHZCDGZHZINPJHOQEKNPLM $.
  $}

  ${
    clifte.1 $e |- ( ph /\ -. ch ) $.
    clifte.2 $e |- th $.
    $( show d is the same as an if-else involving a,b.  (Contributed by Jarvin
       Udandy, 20-Sep-2020.) $)
    clifte $p |- ( th <-> ( ( ph /\ -. ch ) \/ ( ps /\ ch ) ) ) $=
      ( wn wa wo orci 2th ) DACGHZBCHZIFLMEJK $.
  $}

  ${
    cliftet.1 $e |- ( ph /\ ch ) $.
    cliftet.2 $e |- th $.
    $( show d is the same as an if-else involving a,b.  (Contributed by Jarvin
       Udandy, 20-Sep-2020.) $)
    cliftet $p |- ( th <-> ( ( ph /\ ch ) \/ ( ps /\ -. ch ) ) ) $=
      ( wa wn wo orci 2th ) DACGZBCHGZIFLMEJK $.
  $}

  ${
    clifteta.1 $e |- ( ( ph /\ -. ch ) \/ ( ps /\ ch ) ) $.
    clifteta.2 $e |- th $.
    $( show d is the same as an if-else involving a,b.  (Contributed by Jarvin
       Udandy, 20-Sep-2020.) $)
    clifteta $p |- ( th <-> ( ( ph /\ -. ch ) \/ ( ps /\ ch ) ) ) $=
      ( wn wa wo 2th ) DACGHBCHIFEJ $.
  $}

  ${
    cliftetb.1 $e |- ( ( ph /\ ch ) \/ ( ps /\ -. ch ) ) $.
    cliftetb.2 $e |- th $.
    $( show d is the same as an if-else involving a,b.  (Contributed by Jarvin
       Udandy, 20-Sep-2020.) $)
    cliftetb $p |- ( th <-> ( ( ph /\ ch ) \/ ( ps /\ -. ch ) ) ) $=
      ( wa wn wo 2th ) DACGBCHGIFEJ $.
  $}

  ${
    confun.1 $e |- ph $.
    confun.2 $e |- ( ch -> ps ) $.
    confun.3 $e |- ( ch -> th ) $.
    confun.4 $e |- ( ph -> ( ph -> ps ) ) $.
    $( Given the hypotheses there exists a proof for (c implies ( d iff a ) ).
       (Contributed by Jarvin Udandy, 6-Sep-2020.) $)
    confun $p |- ( ch -> ( th <-> ph ) ) $=
      ( ax-1 wi a1i impbid ax-mp impbii sylibr bitrd ) CDCACDCCDICDJCGKLCCACAJC
      CBAFABAABJEHMABAJEABIMNOKCAILP $.
  $}

  ${
    confun2.1 $e |- ( ps -> ph ) $.
    confun2.2 $e |- ( ps -> -. ( ps -> ( ps /\ -. ps ) ) ) $.
    confun2.3 $e |- ( ( ps -> ph ) -> ( ( ps -> ph ) -> ph ) ) $.
    $( Confun simplified to two propositions.  (Contributed by Jarvin Udandy,
       6-Sep-2020.) $)
    confun2 $p |- ( ps -> ( -. ( ps -> ( ps /\ -. ps ) ) <-> ( ps -> ph ) ) )
$=
      ( wi wn wa confun ) BAFABBBBGHFGCCDEI $.
  $}

  ${
    confun3.1 $e |- ( ph <-> ( ch -> ps ) ) $.
    confun3.2 $e |- ( th <-> -. ( ch -> ( ch /\ -. ch ) ) ) $.
    confun3.3 $e |- ( ch -> ps ) $.
    confun3.4 $e |- ( ch -> -. ( ch -> ( ch /\ -. ch ) ) ) $.
    confun3.5 $e |- ( ( ch -> ps ) -> ( ( ch -> ps ) -> ps ) ) $.
    $( Confun's more complex form where both a,d have been "defined".
       (Contributed by Jarvin Udandy, 6-Sep-2020.) $)
    confun3 $p |- ( ch -> ( -. ( ch -> ( ch /\ -. ch ) ) <-> ( ch -> ps ) ) )
$=
      ( wi wn wa confun ) CBJBCCCCKLJKGGHIM $.
  $}

  ${
    confun4.1 $e |- ph $.
    confun4.2 $e |- ( ( ph -> ps ) -> ps ) $.
    confun4.3 $e |- ( ps -> ( ph -> ch ) ) $.
    confun4.4 $e |- ( ( ch -> th ) -> ( ( ph -> th ) <-> ps ) ) $.
    confun4.5 $e |- ( ta <-> ( ch -> th ) ) $.
    confun4.6 $e |- ( et <-> -. ( ch -> ( ch /\ -. ch ) ) ) $.
    confun4.7 $e |- ps $.
    confun4.8 $e |- ( ch -> th ) $.
    $( An attempt at derivative.  Resisted simplest path to a proof.
       (Contributed by Jarvin Udandy, 6-Sep-2020.) $)
    confun4 $p |- ( ch -> ( ps -> ta ) ) $=
      ( wi wa ax-mp wb pm3.2i pm3.4 bicom1 biimpi ) CBEOZPCUCOCUCACGBACOMIQQBEP
      UCBEMCDOZENUDEEUDRUDERKEUDUAQUBQSBETQSCUCTQ $.
  $}

  ${
    confun5.1 $e |- ph $.
    confun5.2 $e |- ( ( ph -> ps ) -> ps ) $.
    confun5.3 $e |- ( ps -> ( ph -> ch ) ) $.
    confun5.4 $e |- ( ( ch -> th ) -> ( ( ph -> th ) <-> ps ) ) $.
    confun5.5 $e |- ( ta <-> ( ch -> th ) ) $.
    confun5.6 $e |- ( et <-> -. ( ch -> ( ch /\ -. ch ) ) ) $.
    confun5.7 $e |- ps $.
    confun5.8 $e |- ( ch -> th ) $.
    $( An attempt at derivative.  Resisted simplest path to a proof.
       Interesting that ch, th, ta, et were all provable.  (Contributed by
       Jarvin Udandy, 7-Sep-2020.) $)
    confun5 $p |- ( ch -> ( et <-> ta ) ) $=
      ( wb wi wn ax-mp bicom1 biimpi wa atnaiana 2th ax-1 ) FEOZCUEPFECCCQUAPQZ
      FCACGBACPMIRRUBUFFFUFOUFFOLFUFSRTRCDPZENUGEEUGOUGEOKEUGSRTRUCUECUDR $.
  $}

  ${
    plcofph.1 $e |- ( ch <-> ( ( ( ( ph /\ ps ) <-> ph ) -> ( ph /\ -. ( ph /\
-. ph ) ) ) /\ ( ph /\ -. ( ph /\ -. ph ) ) ) ) $.
    plcofph.2 $e |- ph $.
    plcofph.3 $e |- ps $.
    $( Given, a,b and a "definition" for c, c is demonstrated.  (Contributed by
       Jarvin Udandy, 8-Sep-2020.) $)
    plcofph $p |- ch $=
      ( wa wb wn wi pm3.24 pm3.2i a1i bicomi biimpi ax-mp ) ABGAHZAAAIGIZGZJZSG
      ZCTSSQAREAKLZMUBLUACCUADNOP $.
  $}

  ${
    pldofph.1 $e |- ( ta <-> ( ( ch -> th ) /\ ( ph <-> ch ) /\ ( ( ph -> ps )
-> ( ps <-> th ) ) ) ) $.
    pldofph.2 $e |- ph $.
    pldofph.3 $e |- ps $.
    pldofph.4 $e |- ch $.
    pldofph.5 $e |- th $.
    $( Given, a,b c, d, "definition" for e, e is demonstrated.  (Contributed by
       Jarvin Udandy, 8-Sep-2020.) $)
    pldofph $p |- ta $=
      ( wi wb w3a a1i 2th 3pm3.2i bicomi biimpi ax-mp ) CDKZACLZABKZBDLZKZMZETU
      AUDDCJNACGIOUCUBBDHJONPUEEEUEFQRS $.
  $}

  ${
    plvcofph.1 $e |- ( ch <-> ( ( ( ( ph /\ ps ) <-> ph ) -> ( ph /\ -. ( ph /\
 -. ph ) ) ) /\ ( ph /\ -. ( ph /\ -. ph ) ) ) ) $.
    plvcofph.2 $e |- ( ta <-> ( ( ch -> th ) /\ ( ph <-> ch ) /\ ( ( ph -> ps )
 -> ( ps <-> th ) ) ) ) $.
    plvcofph.3 $e |- ( et <-> ( ch /\ ta ) ) $.
    plvcofph.4 $e |- ph $.
    plvcofph.5 $e |- ps $.
    plvcofph.6 $e |- th $.
    $( Given, a,b,d, and "definitions" for c, e, f: f is demonstrated.
       (Contributed by Jarvin Udandy, 8-Sep-2020.) $)
    plvcofph $p |- et $=
      ( wa plcofph pldofph pm3.2i bicomi biimpi ax-mp ) CEMZFCEABCGJKNZABCDEHJK
      UALOPTFFTIQRS $.
  $}

  ${
    plvcofphax.1 $e |- ( ch <-> ( ( ( ( ph /\ ps ) <-> ph ) -> ( ph /\ -. ( ph
/\ -. ph ) ) ) /\ ( ph /\ -. ( ph /\ -. ph ) ) ) ) $.
    plvcofphax.2 $e |- ( ta <-> ( ( ch -> th ) /\ ( ph <-> ch ) /\ ( ( ph -> ps
 ) -> ( ps <-> th ) ) ) ) $.
    plvcofphax.3 $e |- ( et <-> ( ch /\ ta ) ) $.
    plvcofphax.4 $e |- ph $.
    plvcofphax.5 $e |- ps $.
    plvcofphax.6 $e |- th $.
    plvcofphax.7 $e |- ( ze <-> -. ( ps /\ -. ta ) ) $.
    $( Given, a,b,d, and "definitions" for c, e, f, g: g is demonstrated.
       (Contributed by Jarvin Udandy, 8-Sep-2020.) $)
    plvcofphax $p |- ze $=
      ( wn wa wi plcofph ax-mp biimpi pldofph pm3.2i pm3.4 iman bicomi ) BEOPOZ
      GBEQZUFBEPUGBELABCDEIKLABCHKLRMUAUBBEUCSUGUFBEUDTSUFGGUFNUETS $.
  $}

  ${
    plvofpos.1 $e |- ( ch <-> ( -. ph /\ -. ps ) ) $.
    plvofpos.2 $e |- ( th <-> ( -. ph /\ ps ) ) $.
    plvofpos.3 $e |- ( ta <-> ( ph /\ -. ps ) ) $.
    plvofpos.4 $e |- ( et <-> ( ph /\ ps ) ) $.
    plvofpos.5 $e |- ( ze <-> ( ( ( ( ( -. ( ( mu -> ch ) /\ ( mu -> th ) ) /\
 -. ( ( mu -> ch ) /\ ( mu -> ta ) ) ) /\
 -. ( ( mu -> ch ) /\ ( ch -> et ) ) ) /\
 -. ( ( mu -> th ) /\ ( mu -> ta ) ) ) /\
 -. ( ( mu -> th ) /\ ( mu -> et ) ) ) /\
 -. ( ( mu -> ta ) /\ ( mu -> et ) ) ) ) $.
    plvofpos.6 $e |- ( si <-> ( ( ( mu -> ch ) \/ ( mu -> th ) ) \/
( ( mu -> ta ) \/ ( mu -> et ) ) ) ) $.
    plvofpos.7 $e |- ( rh <-> ( ze /\ si ) ) $.
    plvofpos.8 $e |- ze $.
    plvofpos.9 $e |- si $.
    $( rh is derivable because ONLY one of ch, th, ta, et is implied by mu.
       (Contributed by Jarvin Udandy, 11-Sep-2020.) $)
    plvofpos $p |- rh $=
      ( wa pm3.2i bicomi biimpi ax-mp ) GHTZIGHRSUAUEIIUEQUBUCUD $.
  $}

  $(
    The dandysum binary to decimal equivalence table.
    Please note the differences! In binary 0100 would normally be the value of
    '4' in Decimal.
        Here it is '2' in Decimal.

        1111 = is 15 in Decimal
        0111 = is 14 in Decimal
        1011 = is 13 in Decimal
        0011 = is 12 in Decimal
        1101 = is 11 in Decimal
        0101 = is 10 in Decimal
        1001 = is 9 in Decimal
        0001 = is 8 in Decimal
        1110 = is 7 in Decimal
        0110 = is 6 in Decimal
        1010 = is 5 in Decimal
        0010 = is 4 in Decimal
        1100 = is 3 in Decimal
        0100 = is 2 in Decimal
        1000 = is 1 in Decimal
        0000 = is 0 in Decimal
  $)

  ${
    mdandyv0.1 $e |- ( ph <-> F. ) $.
    mdandyv0.2 $e |- ( ps <-> T. ) $.
    mdandyv0.3 $e |- ( ch <-> F. ) $.
    mdandyv0.4 $e |- ( th <-> F. ) $.
    mdandyv0.5 $e |- ( ta <-> F. ) $.
    mdandyv0.6 $e |- ( et <-> F. ) $.
    $( Given the equivalences set in the hypotheses, there exist a proof where
       ch, th, ta, et match ph, ps accordingly.  (Contributed by Jarvin Udandy,
       6-Sep-2016.) $)
    mdandyv0 $p |- ( ( ( ( ch <-> ph ) /\ ( th <-> ph ) ) /\ ( ta <-> ph ) ) /\
                     ( et <-> ph ) ) $=
      ( wb wa bothfbothsame pm3.2i ) CAMZDAMZNZEAMZNFAMSTQRCAIGODAJGOPEAKGOPFAL
      GOP $.
  $}

  ${
    mdandyv1.1 $e |- ( ph <-> F. ) $.
    mdandyv1.2 $e |- ( ps <-> T. ) $.
    mdandyv1.3 $e |- ( ch <-> T. ) $.
    mdandyv1.4 $e |- ( th <-> F. ) $.
    mdandyv1.5 $e |- ( ta <-> F. ) $.
    mdandyv1.6 $e |- ( et <-> F. ) $.
    $( Given the equivalences set in the hypotheses, there exist a proof where
       ch, th, ta, et match ph, ps accordingly.  (Contributed by Jarvin Udandy,
       6-Sep-2016.) $)
    mdandyv1 $p |- ( ( ( ( ch <-> ps ) /\ ( th <-> ph ) ) /\ ( ta <-> ph ) ) /\
                     ( et <-> ph ) ) $=
      ( wb wa bothtbothsame bothfbothsame pm3.2i ) CBMZDAMZNZEAMZNFAMTUARSCBIHO
      DAJGPQEAKGPQFALGPQ $.
  $}

  ${
    mdandyv2.1 $e |- ( ph <-> F. ) $.
    mdandyv2.2 $e |- ( ps <-> T. ) $.
    mdandyv2.3 $e |- ( ch <-> F. ) $.
    mdandyv2.4 $e |- ( th <-> T. ) $.
    mdandyv2.5 $e |- ( ta <-> F. ) $.
    mdandyv2.6 $e |- ( et <-> F. ) $.
    $( Given the equivalences set in the hypotheses, there exist a proof where
       ch, th, ta, et match ph, ps accordingly.  (Contributed by Jarvin Udandy,
       6-Sep-2016.) $)
    mdandyv2 $p |- ( ( ( ( ch <-> ph ) /\ ( th <-> ps ) ) /\ ( ta <-> ph ) ) /\
                     ( et <-> ph ) ) $=
      ( wb wa bothfbothsame bothtbothsame pm3.2i ) CAMZDBMZNZEAMZNFAMTUARSCAIGO
      DBJHPQEAKGOQFALGOQ $.
  $}

  ${
    mdandyv3.1 $e |- ( ph <-> F. ) $.
    mdandyv3.2 $e |- ( ps <-> T. ) $.
    mdandyv3.3 $e |- ( ch <-> T. ) $.
    mdandyv3.4 $e |- ( th <-> T. ) $.
    mdandyv3.5 $e |- ( ta <-> F. ) $.
    mdandyv3.6 $e |- ( et <-> F. ) $.
    $( Given the equivalences set in the hypotheses, there exist a proof where
       ch, th, ta, et match ph, ps accordingly.  (Contributed by Jarvin Udandy,
       6-Sep-2016.) $)
    mdandyv3 $p |- ( ( ( ( ch <-> ps ) /\ ( th <-> ps ) ) /\ ( ta <-> ph ) ) /\
                     ( et <-> ph ) ) $=
      ( wb wa bothtbothsame pm3.2i bothfbothsame ) CBMZDBMZNZEAMZNFAMTUARSCBIHO
      DBJHOPEAKGQPFALGQP $.
  $}

  ${
    mdandyv4.1 $e |- ( ph <-> F. ) $.
    mdandyv4.2 $e |- ( ps <-> T. ) $.
    mdandyv4.3 $e |- ( ch <-> F. ) $.
    mdandyv4.4 $e |- ( th <-> F. ) $.
    mdandyv4.5 $e |- ( ta <-> T. ) $.
    mdandyv4.6 $e |- ( et <-> F. ) $.
    $( Given the equivalences set in the hypotheses, there exist a proof where
       ch, th, ta, et match ph, ps accordingly.  (Contributed by Jarvin Udandy,
       6-Sep-2016.) $)
    mdandyv4 $p |- ( ( ( ( ch <-> ph ) /\ ( th <-> ph ) ) /\
( ta <-> ps ) ) /\
( et <-> ph ) )
$=
      ( wb wa bothfbothsame pm3.2i bothtbothsame ) CAMZDAMZNZEBMZNFAMTUARSCAIGO
      DAJGOPEBKHQPFALGOP $.
  $}

  ${
    mdandyv5.1 $e |- ( ph <-> F. ) $.
    mdandyv5.2 $e |- ( ps <-> T. ) $.
    mdandyv5.3 $e |- ( ch <-> T. ) $.
    mdandyv5.4 $e |- ( th <-> F. ) $.
    mdandyv5.5 $e |- ( ta <-> T. ) $.
    mdandyv5.6 $e |- ( et <-> F. ) $.
    $( Given the equivalences set in the hypotheses, there exist a proof where
       ch, th, ta, et match ph, ps accordingly.  (Contributed by Jarvin Udandy,
       6-Sep-2016.) $)
    mdandyv5 $p |- ( ( ( ( ch <-> ps ) /\ ( th <-> ph ) ) /\
( ta <-> ps ) ) /\
( et <-> ph ) )
$=
      ( wb wa bothtbothsame bothfbothsame pm3.2i ) CBMZDAMZNZEBMZNFAMTUARSCBIHO
      DAJGPQEBKHOQFALGPQ $.
  $}

  ${
    mdandyv6.1 $e |- ( ph <-> F. ) $.
    mdandyv6.2 $e |- ( ps <-> T. ) $.
    mdandyv6.3 $e |- ( ch <-> F. ) $.
    mdandyv6.4 $e |- ( th <-> T. ) $.
    mdandyv6.5 $e |- ( ta <-> T. ) $.
    mdandyv6.6 $e |- ( et <-> F. ) $.
    $( Given the equivalences set in the hypotheses, there exist a proof where
       ch, th, ta, et match ph, ps accordingly.  (Contributed by Jarvin Udandy,
       6-Sep-2016.) $)
    mdandyv6 $p |- ( ( ( ( ch <-> ph ) /\ ( th <-> ps ) ) /\
( ta <-> ps ) ) /\
( et <-> ph ) )
$=
      ( wb wa bothfbothsame bothtbothsame pm3.2i ) CAMZDBMZNZEBMZNFAMTUARSCAIGO
      DBJHPQEBKHPQFALGOQ $.
  $}

  ${
    mdandyv7.1 $e |- ( ph <-> F. ) $.
    mdandyv7.2 $e |- ( ps <-> T. ) $.
    mdandyv7.3 $e |- ( ch <-> T. ) $.
    mdandyv7.4 $e |- ( th <-> T. ) $.
    mdandyv7.5 $e |- ( ta <-> T. ) $.
    mdandyv7.6 $e |- ( et <-> F. ) $.
    $( Given the equivalences set in the hypotheses, there exist a proof where
       ch, th, ta, et match ph, ps accordingly.  (Contributed by Jarvin Udandy,
       6-Sep-2016.) $)
    mdandyv7 $p |- ( ( ( ( ch <-> ps ) /\ ( th <-> ps ) ) /\
( ta <-> ps ) ) /\
( et <-> ph ) )
$=
      ( wb wa bothtbothsame pm3.2i bothfbothsame ) CBMZDBMZNZEBMZNFAMTUARSCBIHO
      DBJHOPEBKHOPFALGQP $.
  $}

  ${
    mdandyv8.1 $e |- ( ph <-> F. ) $.
    mdandyv8.2 $e |- ( ps <-> T. ) $.
    mdandyv8.3 $e |- ( ch <-> F. ) $.
    mdandyv8.4 $e |- ( th <-> F. ) $.
    mdandyv8.5 $e |- ( ta <-> F. ) $.
    mdandyv8.6 $e |- ( et <-> T. ) $.
    $( Given the equivalences set in the hypotheses, there exist a proof where
       ch, th, ta, et match ph, ps accordingly.  (Contributed by Jarvin Udandy,
       6-Sep-2016.) $)
    mdandyv8 $p |- ( ( ( ( ch <-> ph ) /\ ( th <-> ph ) ) /\
( ta <-> ph ) ) /\
( et <-> ps ) )
$=
      ( wb wa bothfbothsame pm3.2i bothtbothsame ) CAMZDAMZNZEAMZNFBMTUARSCAIGO
      DAJGOPEAKGOPFBLHQP $.
  $}

  ${
    mdandyv9.1 $e |- ( ph <-> F. ) $.
    mdandyv9.2 $e |- ( ps <-> T. ) $.
    mdandyv9.3 $e |- ( ch <-> T. ) $.
    mdandyv9.4 $e |- ( th <-> F. ) $.
    mdandyv9.5 $e |- ( ta <-> F. ) $.
    mdandyv9.6 $e |- ( et <-> T. ) $.
    $( Given the equivalences set in the hypotheses, there exist a proof where
       ch, th, ta, et match ph, ps accordingly.  (Contributed by Jarvin Udandy,
       6-Sep-2016.) $)
    mdandyv9 $p |- ( ( ( ( ch <-> ps ) /\ ( th <-> ph ) ) /\
( ta <-> ph ) ) /\
( et <-> ps ) )
$=
      ( wb wa bothtbothsame bothfbothsame pm3.2i ) CBMZDAMZNZEAMZNFBMTUARSCBIHO
      DAJGPQEAKGPQFBLHOQ $.
  $}

  ${
    mdandyv10.1 $e |- ( ph <-> F. ) $.
    mdandyv10.2 $e |- ( ps <-> T. ) $.
    mdandyv10.3 $e |- ( ch <-> F. ) $.
    mdandyv10.4 $e |- ( th <-> T. ) $.
    mdandyv10.5 $e |- ( ta <-> F. ) $.
    mdandyv10.6 $e |- ( et <-> T. ) $.
    $( Given the equivalences set in the hypotheses, there exist a proof where
       ch, th, ta, et match ph, ps accordingly.  (Contributed by Jarvin Udandy,
       6-Sep-2016.) $)
    mdandyv10 $p |- ( ( ( ( ch <-> ph ) /\ ( th <-> ps ) ) /\
( ta <-> ph ) ) /\
( et <-> ps ) )
$=
      ( wb wa bothfbothsame bothtbothsame pm3.2i ) CAMZDBMZNZEAMZNFBMTUARSCAIGO
      DBJHPQEAKGOQFBLHPQ $.
  $}

  ${
    mdandyv11.1 $e |- ( ph <-> F. ) $.
    mdandyv11.2 $e |- ( ps <-> T. ) $.
    mdandyv11.3 $e |- ( ch <-> T. ) $.
    mdandyv11.4 $e |- ( th <-> T. ) $.
    mdandyv11.5 $e |- ( ta <-> F. ) $.
    mdandyv11.6 $e |- ( et <-> T. ) $.
    $( Given the equivalences set in the hypotheses, there exist a proof where
       ch, th, ta, et match ph, ps accordingly.  (Contributed by Jarvin Udandy,
       6-Sep-2016.) $)
    mdandyv11 $p |- ( ( ( ( ch <-> ps ) /\ ( th <-> ps ) ) /\
( ta <-> ph ) ) /\
( et <-> ps ) )
$=
      ( wb wa bothtbothsame pm3.2i bothfbothsame ) CBMZDBMZNZEAMZNFBMTUARSCBIHO
      DBJHOPEAKGQPFBLHOP $.
  $}

  ${
    mdandyv12.1 $e |- ( ph <-> F. ) $.
    mdandyv12.2 $e |- ( ps <-> T. ) $.
    mdandyv12.3 $e |- ( ch <-> F. ) $.
    mdandyv12.4 $e |- ( th <-> F. ) $.
    mdandyv12.5 $e |- ( ta <-> T. ) $.
    mdandyv12.6 $e |- ( et <-> T. ) $.
    $( Given the equivalences set in the hypotheses, there exist a proof where
       ch, th, ta, et match ph, ps accordingly.  (Contributed by Jarvin Udandy,
       6-Sep-2016.) $)
    mdandyv12 $p |- ( ( ( ( ch <-> ph ) /\ ( th <-> ph ) ) /\
( ta <-> ps ) ) /\
( et <-> ps ) )
$=
      ( wb wa bothfbothsame pm3.2i bothtbothsame ) CAMZDAMZNZEBMZNFBMTUARSCAIGO
      DAJGOPEBKHQPFBLHQP $.
  $}

  ${
    mdandyv13.1 $e |- ( ph <-> F. ) $.
    mdandyv13.2 $e |- ( ps <-> T. ) $.
    mdandyv13.3 $e |- ( ch <-> T. ) $.
    mdandyv13.4 $e |- ( th <-> F. ) $.
    mdandyv13.5 $e |- ( ta <-> T. ) $.
    mdandyv13.6 $e |- ( et <-> T. ) $.
    $( Given the equivalences set in the hypotheses, there exist a proof where
       ch, th, ta, et match ph, ps accordingly.  (Contributed by Jarvin Udandy,
       6-Sep-2016.) $)
    mdandyv13 $p |- ( ( ( ( ch <-> ps ) /\ ( th <-> ph ) ) /\
( ta <-> ps ) ) /\
( et <-> ps ) )
$=
      ( wb wa bothtbothsame bothfbothsame pm3.2i ) CBMZDAMZNZEBMZNFBMTUARSCBIHO
      DAJGPQEBKHOQFBLHOQ $.
  $}

  ${
    mdandyv14.1 $e |- ( ph <-> F. ) $.
    mdandyv14.2 $e |- ( ps <-> T. ) $.
    mdandyv14.3 $e |- ( ch <-> F. ) $.
    mdandyv14.4 $e |- ( th <-> T. ) $.
    mdandyv14.5 $e |- ( ta <-> T. ) $.
    mdandyv14.6 $e |- ( et <-> T. ) $.
    $( Given the equivalences set in the hypotheses, there exist a proof where
       ch, th, ta, et match ph, ps accordingly.  (Contributed by Jarvin Udandy,
       6-Sep-2016.) $)
    mdandyv14 $p |- ( ( ( ( ch <-> ph ) /\ ( th <-> ps ) ) /\
( ta <-> ps ) ) /\
( et <-> ps ) )
$=
      ( wb wa bothfbothsame bothtbothsame pm3.2i ) CAMZDBMZNZEBMZNFBMTUARSCAIGO
      DBJHPQEBKHPQFBLHPQ $.
  $}

  ${
    mdandyv15.1 $e |- ( ph <-> F. ) $.
    mdandyv15.2 $e |- ( ps <-> T. ) $.
    mdandyv15.3 $e |- ( ch <-> T. ) $.
    mdandyv15.4 $e |- ( th <-> T. ) $.
    mdandyv15.5 $e |- ( ta <-> T. ) $.
    mdandyv15.6 $e |- ( et <-> T. ) $.
    $( Given the equivalences set in the hypotheses, there exist a proof where
       ch, th, ta, et match ph, ps accordingly.  (Contributed by Jarvin Udandy,
       6-Sep-2016.) $)
    mdandyv15 $p |- ( ( ( ( ch <-> ps ) /\ ( th <-> ps ) ) /\
( ta <-> ps ) ) /\
( et <-> ps ) )
$=
      ( wb wa bothtbothsame pm3.2i ) CBMZDBMZNZEBMZNFBMSTQRCBIHODBJHOPEBKHOPFBL
      HOP $.
  $}

  ${
    mdandyvr0.1 $e |- ( ph <-> ze ) $.
    mdandyvr0.2 $e |- ( ps <-> si ) $.
    mdandyvr0.3 $e |- ( ch <-> ph ) $.
    mdandyvr0.4 $e |- ( th <-> ph ) $.
    mdandyvr0.5 $e |- ( ta <-> ph ) $.
    mdandyvr0.6 $e |- ( et <-> ph ) $.
    $( Given the equivalences set in the hypotheses, there exist a proof where
       ch, th, ta, et match ze, si accordingly.  (Contributed by Jarvin Udandy,
       7-Sep-2016.) $)
    mdandyvr0 $p |- ( ( ( ( ch <-> ze ) /\ ( th <-> ze ) ) /\
( ta <-> ze ) ) /\
( et <-> ze ) )
$=
      ( wb wa bitri pm3.2i ) CGOZDGOZPZEGOZPFGOUAUBSTCAGKIQDAGLIQREAGMIQRFAGNIQ
      R $.
  $}

  ${
    mdandyvr1.1 $e |- ( ph <-> ze ) $.
    mdandyvr1.2 $e |- ( ps <-> si ) $.
    mdandyvr1.3 $e |- ( ch <-> ps ) $.
    mdandyvr1.4 $e |- ( th <-> ph ) $.
    mdandyvr1.5 $e |- ( ta <-> ph ) $.
    mdandyvr1.6 $e |- ( et <-> ph ) $.
    $( Given the equivalences set in the hypotheses, there exist a proof where
       ch, th, ta, et match ze, si accordingly.  (Contributed by Jarvin Udandy,
       7-Sep-2016.) $)
    mdandyvr1 $p |- ( ( ( ( ch <-> si ) /\ ( th <-> ze ) ) /\
( ta <-> ze ) ) /\
( et <-> ze ) )
$=
      ( wb wa bitri pm3.2i ) CHOZDGOZPZEGOZPFGOUAUBSTCBHKJQDAGLIQREAGMIQRFAGNIQ
      R $.
  $}

  ${
    mdandyvr2.1 $e |- ( ph <-> ze ) $.
    mdandyvr2.2 $e |- ( ps <-> si ) $.
    mdandyvr2.3 $e |- ( ch <-> ph ) $.
    mdandyvr2.4 $e |- ( th <-> ps ) $.
    mdandyvr2.5 $e |- ( ta <-> ph ) $.
    mdandyvr2.6 $e |- ( et <-> ph ) $.
    $( Given the equivalences set in the hypotheses, there exist a proof where
       ch, th, ta, et match ze, si accordingly.  (Contributed by Jarvin Udandy,
       7-Sep-2016.) $)
    mdandyvr2 $p |- ( ( ( ( ch <-> ze ) /\ ( th <-> si ) ) /\
( ta <-> ze ) ) /\
( et <-> ze ) )
$=
      ( wb wa bitri pm3.2i ) CGOZDHOZPZEGOZPFGOUAUBSTCAGKIQDBHLJQREAGMIQRFAGNIQ
      R $.
  $}

  ${
    mdandyvr3.1 $e |- ( ph <-> ze ) $.
    mdandyvr3.2 $e |- ( ps <-> si ) $.
    mdandyvr3.3 $e |- ( ch <-> ps ) $.
    mdandyvr3.4 $e |- ( th <-> ps ) $.
    mdandyvr3.5 $e |- ( ta <-> ph ) $.
    mdandyvr3.6 $e |- ( et <-> ph ) $.
    $( Given the equivalences set in the hypotheses, there exist a proof where
       ch, th, ta, et match ze, si accordingly.  (Contributed by Jarvin Udandy,
       7-Sep-2016.) $)
    mdandyvr3 $p |- ( ( ( ( ch <-> si ) /\ ( th <-> si ) ) /\
( ta <-> ze ) ) /\
( et <-> ze ) )
$=
      ( wb wa bitri pm3.2i ) CHOZDHOZPZEGOZPFGOUAUBSTCBHKJQDBHLJQREAGMIQRFAGNIQ
      R $.
  $}

  ${
    mdandyvr4.1 $e |- ( ph <-> ze ) $.
    mdandyvr4.2 $e |- ( ps <-> si ) $.
    mdandyvr4.3 $e |- ( ch <-> ph ) $.
    mdandyvr4.4 $e |- ( th <-> ph ) $.
    mdandyvr4.5 $e |- ( ta <-> ps ) $.
    mdandyvr4.6 $e |- ( et <-> ph ) $.
    $( Given the equivalences set in the hypotheses, there exist a proof where
       ch, th, ta, et match ze, si accordingly.  (Contributed by Jarvin Udandy,
       7-Sep-2016.) $)
    mdandyvr4 $p |- ( ( ( ( ch <-> ze ) /\ ( th <-> ze ) ) /\
( ta <-> si ) ) /\
( et <-> ze ) )
$=
      ( wb wa bitri pm3.2i ) CGOZDGOZPZEHOZPFGOUAUBSTCAGKIQDAGLIQREBHMJQRFAGNIQ
      R $.
  $}

  ${
    mdandyvr5.1 $e |- ( ph <-> ze ) $.
    mdandyvr5.2 $e |- ( ps <-> si ) $.
    mdandyvr5.3 $e |- ( ch <-> ps ) $.
    mdandyvr5.4 $e |- ( th <-> ph ) $.
    mdandyvr5.5 $e |- ( ta <-> ps ) $.
    mdandyvr5.6 $e |- ( et <-> ph ) $.
    $( Given the equivalences set in the hypotheses, there exist a proof where
       ch, th, ta, et match ze, si accordingly.  (Contributed by Jarvin Udandy,
       7-Sep-2016.) $)
    mdandyvr5 $p |- ( ( ( ( ch <-> si ) /\ ( th <-> ze ) ) /\
( ta <-> si ) ) /\
( et <-> ze ) )
$=
      ( wb wa bitri pm3.2i ) CHOZDGOZPZEHOZPFGOUAUBSTCBHKJQDAGLIQREBHMJQRFAGNIQ
      R $.
  $}

  ${
    mdandyvr6.1 $e |- ( ph <-> ze ) $.
    mdandyvr6.2 $e |- ( ps <-> si ) $.
    mdandyvr6.3 $e |- ( ch <-> ph ) $.
    mdandyvr6.4 $e |- ( th <-> ps ) $.
    mdandyvr6.5 $e |- ( ta <-> ps ) $.
    mdandyvr6.6 $e |- ( et <-> ph ) $.
    $( Given the equivalences set in the hypotheses, there exist a proof where
       ch, th, ta, et match ze, si accordingly.  (Contributed by Jarvin Udandy,
       7-Sep-2016.) $)
    mdandyvr6 $p |- ( ( ( ( ch <-> ze ) /\ ( th <-> si ) ) /\
( ta <-> si ) ) /\
( et <-> ze ) )
$=
      ( wb wa bitri pm3.2i ) CGOZDHOZPZEHOZPFGOUAUBSTCAGKIQDBHLJQREBHMJQRFAGNIQ
      R $.
  $}

  ${
    mdandyvr7.1 $e |- ( ph <-> ze ) $.
    mdandyvr7.2 $e |- ( ps <-> si ) $.
    mdandyvr7.3 $e |- ( ch <-> ps ) $.
    mdandyvr7.4 $e |- ( th <-> ps ) $.
    mdandyvr7.5 $e |- ( ta <-> ps ) $.
    mdandyvr7.6 $e |- ( et <-> ph ) $.
    $( Given the equivalences set in the hypotheses, there exist a proof where
       ch, th, ta, et match ze, si accordingly.  (Contributed by Jarvin Udandy,
       7-Sep-2016.) $)
    mdandyvr7 $p |- ( ( ( ( ch <-> si ) /\ ( th <-> si ) ) /\
( ta <-> si ) ) /\
( et <-> ze ) )
$=
      ( wb wa bitri pm3.2i ) CHOZDHOZPZEHOZPFGOUAUBSTCBHKJQDBHLJQREBHMJQRFAGNIQ
      R $.
  $}

  ${
    mdandyvr8.1 $e |- ( ph <-> ze ) $.
    mdandyvr8.2 $e |- ( ps <-> si ) $.
    mdandyvr8.3 $e |- ( ch <-> ph ) $.
    mdandyvr8.4 $e |- ( th <-> ph ) $.
    mdandyvr8.5 $e |- ( ta <-> ph ) $.
    mdandyvr8.6 $e |- ( et <-> ps ) $.
    $( Given the equivalences set in the hypotheses, there exist a proof where
       ch, th, ta, et match ze, si accordingly.  (Contributed by Jarvin Udandy,
       7-Sep-2016.) $)
    mdandyvr8 $p |- ( ( ( ( ch <-> ze ) /\ ( th <-> ze ) ) /\
( ta <-> ze ) ) /\
( et <-> si ) )
$=
      ( mdandyvr7 ) BACDEFHGJIKLMNO $.
  $}

  ${
    mdandyvr9.1 $e |- ( ph <-> ze ) $.
    mdandyvr9.2 $e |- ( ps <-> si ) $.
    mdandyvr9.3 $e |- ( ch <-> ps ) $.
    mdandyvr9.4 $e |- ( th <-> ph ) $.
    mdandyvr9.5 $e |- ( ta <-> ph ) $.
    mdandyvr9.6 $e |- ( et <-> ps ) $.
    $( Given the equivalences set in the hypotheses, there exist a proof where
       ch, th, ta, et match ze, si accordingly.  (Contributed by Jarvin Udandy,
       7-Sep-2016.) $)
    mdandyvr9 $p |- ( ( ( ( ch <-> si ) /\ ( th <-> ze ) ) /\
( ta <-> ze ) ) /\
( et <-> si ) )
$=
      ( mdandyvr6 ) BACDEFHGJIKLMNO $.
  $}

  ${
    mdandyvr10.1 $e |- ( ph <-> ze ) $.
    mdandyvr10.2 $e |- ( ps <-> si ) $.
    mdandyvr10.3 $e |- ( ch <-> ph ) $.
    mdandyvr10.4 $e |- ( th <-> ps ) $.
    mdandyvr10.5 $e |- ( ta <-> ph ) $.
    mdandyvr10.6 $e |- ( et <-> ps ) $.
    $( Given the equivalences set in the hypotheses, there exist a proof where
       ch, th, ta, et match ze, si accordingly.  (Contributed by Jarvin Udandy,
       7-Sep-2016.) $)
    mdandyvr10 $p |- ( ( ( ( ch <-> ze ) /\ ( th <-> si ) ) /\
( ta <-> ze ) ) /\
( et <-> si ) )
$=
      ( mdandyvr5 ) BACDEFHGJIKLMNO $.
  $}

  ${
    mdandyvr11.1 $e |- ( ph <-> ze ) $.
    mdandyvr11.2 $e |- ( ps <-> si ) $.
    mdandyvr11.3 $e |- ( ch <-> ps ) $.
    mdandyvr11.4 $e |- ( th <-> ps ) $.
    mdandyvr11.5 $e |- ( ta <-> ph ) $.
    mdandyvr11.6 $e |- ( et <-> ps ) $.
    $( Given the equivalences set in the hypotheses, there exist a proof where
       ch, th, ta, et match ze, si accordingly.  (Contributed by Jarvin Udandy,
       7-Sep-2016.) $)
    mdandyvr11 $p |- ( ( ( ( ch <-> si ) /\ ( th <-> si ) ) /\
( ta <-> ze ) ) /\
( et <-> si ) )
$=
      ( mdandyvr4 ) BACDEFHGJIKLMNO $.
  $}

  ${
    mdandyvr12.1 $e |- ( ph <-> ze ) $.
    mdandyvr12.2 $e |- ( ps <-> si ) $.
    mdandyvr12.3 $e |- ( ch <-> ph ) $.
    mdandyvr12.4 $e |- ( th <-> ph ) $.
    mdandyvr12.5 $e |- ( ta <-> ps ) $.
    mdandyvr12.6 $e |- ( et <-> ps ) $.
    $( Given the equivalences set in the hypotheses, there exist a proof where
       ch, th, ta, et match ze, si accordingly.  (Contributed by Jarvin Udandy,
       7-Sep-2016.) $)
    mdandyvr12 $p |- ( ( ( ( ch <-> ze ) /\ ( th <-> ze ) ) /\
( ta <-> si ) ) /\
( et <-> si ) )
$=
      ( mdandyvr3 ) BACDEFHGJIKLMNO $.
  $}

  ${
    mdandyvr13.1 $e |- ( ph <-> ze ) $.
    mdandyvr13.2 $e |- ( ps <-> si ) $.
    mdandyvr13.3 $e |- ( ch <-> ps ) $.
    mdandyvr13.4 $e |- ( th <-> ph ) $.
    mdandyvr13.5 $e |- ( ta <-> ps ) $.
    mdandyvr13.6 $e |- ( et <-> ps ) $.
    $( Given the equivalences set in the hypotheses, there exist a proof where
       ch, th, ta, et match ze, si accordingly.  (Contributed by Jarvin Udandy,
       7-Sep-2016.) $)
    mdandyvr13 $p |- ( ( ( ( ch <-> si ) /\ ( th <-> ze ) ) /\
( ta <-> si ) ) /\
( et <-> si ) )
$=
      ( mdandyvr2 ) BACDEFHGJIKLMNO $.
  $}

  ${
    mdandyvr14.1 $e |- ( ph <-> ze ) $.
    mdandyvr14.2 $e |- ( ps <-> si ) $.
    mdandyvr14.3 $e |- ( ch <-> ph ) $.
    mdandyvr14.4 $e |- ( th <-> ps ) $.
    mdandyvr14.5 $e |- ( ta <-> ps ) $.
    mdandyvr14.6 $e |- ( et <-> ps ) $.
    $( Given the equivalences set in the hypotheses, there exist a proof where
       ch, th, ta, et match ze, si accordingly.  (Contributed by Jarvin Udandy,
       7-Sep-2016.) $)
    mdandyvr14 $p |- ( ( ( ( ch <-> ze ) /\ ( th <-> si ) ) /\
( ta <-> si ) ) /\
( et <-> si ) )
$=
      ( mdandyvr1 ) BACDEFHGJIKLMNO $.
  $}

  ${
    mdandyvr15.1 $e |- ( ph <-> ze ) $.
    mdandyvr15.2 $e |- ( ps <-> si ) $.
    mdandyvr15.3 $e |- ( ch <-> ps ) $.
    mdandyvr15.4 $e |- ( th <-> ps ) $.
    mdandyvr15.5 $e |- ( ta <-> ps ) $.
    mdandyvr15.6 $e |- ( et <-> ps ) $.
    $( Given the equivalences set in the hypotheses, there exist a proof where
       ch, th, ta, et match ze, si accordingly.  (Contributed by Jarvin Udandy,
       7-Sep-2016.) $)
    mdandyvr15 $p |- ( ( ( ( ch <-> si ) /\ ( th <-> si ) ) /\
( ta <-> si ) ) /\
( et <-> si ) )
$=
      ( mdandyvr0 ) BACDEFHGJIKLMNO $.
  $}

  ${
    mdandyvrx0.1 $e |- ( ph \/_ ze ) $.
    mdandyvrx0.2 $e |- ( ps \/_ si ) $.
    mdandyvrx0.3 $e |- ( ch <-> ph ) $.
    mdandyvrx0.4 $e |- ( th <-> ph ) $.
    mdandyvrx0.5 $e |- ( ta <-> ph ) $.
    mdandyvrx0.6 $e |- ( et <-> ph ) $.
    $( Given the exclusivities set in the hypotheses, there exist a proof where
       ch, th, ta, et exclude ze, si accordingly.  (Contributed by Jarvin
       Udandy, 7-Sep-2016.) $)
    mdandyvrx0 $p |- ( ( ( ( ch \/_ ze ) /\ ( th \/_ ze ) ) /\
( ta \/_ ze ) ) /\
( et \/_ ze ) )
$=
      ( wxo wa axorbciffatcxorb pm3.2i ) CGOZDGOZPZEGOZPFGOUAUBSTAGCIKQAGDILQRA
      GEIMQRAGFINQR $.
  $}

  ${
    mdandyvrx1.1 $e |- ( ph \/_ ze ) $.
    mdandyvrx1.2 $e |- ( ps \/_ si ) $.
    mdandyvrx1.3 $e |- ( ch <-> ps ) $.
    mdandyvrx1.4 $e |- ( th <-> ph ) $.
    mdandyvrx1.5 $e |- ( ta <-> ph ) $.
    mdandyvrx1.6 $e |- ( et <-> ph ) $.
    $( Given the exclusivities set in the hypotheses, there exist a proof where
       ch, th, ta, et exclude ze, si accordingly.  (Contributed by Jarvin
       Udandy, 7-Sep-2016.) $)
    mdandyvrx1 $p |- ( ( ( ( ch \/_ si ) /\ ( th \/_ ze ) ) /\
( ta \/_ ze ) ) /\
( et \/_ ze ) )
$=
      ( wxo wa axorbciffatcxorb pm3.2i ) CHOZDGOZPZEGOZPFGOUAUBSTBHCJKQAGDILQRA
      GEIMQRAGFINQR $.
  $}

  ${
    mdandyvrx2.1 $e |- ( ph \/_ ze ) $.
    mdandyvrx2.2 $e |- ( ps \/_ si ) $.
    mdandyvrx2.3 $e |- ( ch <-> ph ) $.
    mdandyvrx2.4 $e |- ( th <-> ps ) $.
    mdandyvrx2.5 $e |- ( ta <-> ph ) $.
    mdandyvrx2.6 $e |- ( et <-> ph ) $.
    $( Given the exclusivities set in the hypotheses, there exist a proof where
       ch, th, ta, et exclude ze, si accordingly.  (Contributed by Jarvin
       Udandy, 7-Sep-2016.) $)
    mdandyvrx2 $p |- ( ( ( ( ch \/_ ze ) /\ ( th \/_ si ) ) /\
( ta \/_ ze ) ) /\
( et \/_ ze ) )
$=
      ( wxo wa axorbciffatcxorb pm3.2i ) CGOZDHOZPZEGOZPFGOUAUBSTAGCIKQBHDJLQRA
      GEIMQRAGFINQR $.
  $}

  ${
    mdandyvrx3.1 $e |- ( ph \/_ ze ) $.
    mdandyvrx3.2 $e |- ( ps \/_ si ) $.
    mdandyvrx3.3 $e |- ( ch <-> ps ) $.
    mdandyvrx3.4 $e |- ( th <-> ps ) $.
    mdandyvrx3.5 $e |- ( ta <-> ph ) $.
    mdandyvrx3.6 $e |- ( et <-> ph ) $.
    $( Given the exclusivities set in the hypotheses, there exist a proof where
       ch, th, ta, et exclude ze, si accordingly.  (Contributed by Jarvin
       Udandy, 7-Sep-2016.) $)
    mdandyvrx3 $p |- ( ( ( ( ch \/_ si ) /\ ( th \/_ si ) ) /\
( ta \/_ ze ) ) /\
( et \/_ ze ) )
$=
      ( wxo wa axorbciffatcxorb pm3.2i ) CHOZDHOZPZEGOZPFGOUAUBSTBHCJKQBHDJLQRA
      GEIMQRAGFINQR $.
  $}

  ${
    mdandyvrx4.1 $e |- ( ph \/_ ze ) $.
    mdandyvrx4.2 $e |- ( ps \/_ si ) $.
    mdandyvrx4.3 $e |- ( ch <-> ph ) $.
    mdandyvrx4.4 $e |- ( th <-> ph ) $.
    mdandyvrx4.5 $e |- ( ta <-> ps ) $.
    mdandyvrx4.6 $e |- ( et <-> ph ) $.
    $( Given the exclusivities set in the hypotheses, there exist a proof where
       ch, th, ta, et exclude ze, si accordingly.  (Contributed by Jarvin
       Udandy, 7-Sep-2016.) $)
    mdandyvrx4 $p |- ( ( ( ( ch \/_ ze ) /\ ( th \/_ ze ) ) /\
( ta \/_ si ) ) /\
( et \/_ ze ) )
$=
      ( wxo wa axorbciffatcxorb pm3.2i ) CGOZDGOZPZEHOZPFGOUAUBSTAGCIKQAGDILQRB
      HEJMQRAGFINQR $.
  $}

  ${
    mdandyvrx5.1 $e |- ( ph \/_ ze ) $.
    mdandyvrx5.2 $e |- ( ps \/_ si ) $.
    mdandyvrx5.3 $e |- ( ch <-> ps ) $.
    mdandyvrx5.4 $e |- ( th <-> ph ) $.
    mdandyvrx5.5 $e |- ( ta <-> ps ) $.
    mdandyvrx5.6 $e |- ( et <-> ph ) $.
    $( Given the exclusivities set in the hypotheses, there exist a proof where
       ch, th, ta, et exclude ze, si accordingly.  (Contributed by Jarvin
       Udandy, 7-Sep-2016.) $)
    mdandyvrx5 $p |- ( ( ( ( ch \/_ si ) /\ ( th \/_ ze ) ) /\
( ta \/_ si ) ) /\
( et \/_ ze ) )
$=
      ( wxo wa axorbciffatcxorb pm3.2i ) CHOZDGOZPZEHOZPFGOUAUBSTBHCJKQAGDILQRB
      HEJMQRAGFINQR $.
  $}

  ${
    mdandyvrx6.1 $e |- ( ph \/_ ze ) $.
    mdandyvrx6.2 $e |- ( ps \/_ si ) $.
    mdandyvrx6.3 $e |- ( ch <-> ph ) $.
    mdandyvrx6.4 $e |- ( th <-> ps ) $.
    mdandyvrx6.5 $e |- ( ta <-> ps ) $.
    mdandyvrx6.6 $e |- ( et <-> ph ) $.
    $( Given the exclusivities set in the hypotheses, there exist a proof where
       ch, th, ta, et exclude ze, si accordingly.  (Contributed by Jarvin
       Udandy, 7-Sep-2016.) $)
    mdandyvrx6 $p |- ( ( ( ( ch \/_ ze ) /\ ( th \/_ si ) ) /\
( ta \/_ si ) ) /\
( et \/_ ze ) )
$=
      ( wxo wa axorbciffatcxorb pm3.2i ) CGOZDHOZPZEHOZPFGOUAUBSTAGCIKQBHDJLQRB
      HEJMQRAGFINQR $.
  $}

  ${
    mdandyvrx7.1 $e |- ( ph \/_ ze ) $.
    mdandyvrx7.2 $e |- ( ps \/_ si ) $.
    mdandyvrx7.3 $e |- ( ch <-> ps ) $.
    mdandyvrx7.4 $e |- ( th <-> ps ) $.
    mdandyvrx7.5 $e |- ( ta <-> ps ) $.
    mdandyvrx7.6 $e |- ( et <-> ph ) $.
    $( Given the exclusivities set in the hypotheses, there exist a proof where
       ch, th, ta, et exclude ze, si accordingly.  (Contributed by Jarvin
       Udandy, 7-Sep-2016.) $)
    mdandyvrx7 $p |- ( ( ( ( ch \/_ si ) /\ ( th \/_ si ) ) /\
( ta \/_ si ) ) /\
( et \/_ ze ) )
$=
      ( wxo wa axorbciffatcxorb pm3.2i ) CHOZDHOZPZEHOZPFGOUAUBSTBHCJKQBHDJLQRB
      HEJMQRAGFINQR $.
  $}

  ${
    mdandyvrx8.1 $e |- ( ph \/_ ze ) $.
    mdandyvrx8.2 $e |- ( ps \/_ si ) $.
    mdandyvrx8.3 $e |- ( ch <-> ph ) $.
    mdandyvrx8.4 $e |- ( th <-> ph ) $.
    mdandyvrx8.5 $e |- ( ta <-> ph ) $.
    mdandyvrx8.6 $e |- ( et <-> ps ) $.
    $( Given the exclusivities set in the hypotheses, there exist a proof where
       ch, th, ta, et exclude ze, si accordingly.  (Contributed by Jarvin
       Udandy, 7-Sep-2016.) $)
    mdandyvrx8 $p |- ( ( ( ( ch \/_ ze ) /\ ( th \/_ ze ) ) /\
( ta \/_ ze ) ) /\
( et \/_ si ) )
$=
      ( mdandyvrx7 ) BACDEFHGJIKLMNO $.
  $}

  ${
    mdandyvrx9.1 $e |- ( ph \/_ ze ) $.
    mdandyvrx9.2 $e |- ( ps \/_ si ) $.
    mdandyvrx9.3 $e |- ( ch <-> ps ) $.
    mdandyvrx9.4 $e |- ( th <-> ph ) $.
    mdandyvrx9.5 $e |- ( ta <-> ph ) $.
    mdandyvrx9.6 $e |- ( et <-> ps ) $.
    $( Given the exclusivities set in the hypotheses, there exist a proof where
       ch, th, ta, et exclude ze, si accordingly.  (Contributed by Jarvin
       Udandy, 7-Sep-2016.) $)
    mdandyvrx9 $p |- ( ( ( ( ch \/_ si ) /\ ( th \/_ ze ) ) /\
( ta \/_ ze ) ) /\
( et \/_ si ) )
$=
      ( mdandyvrx6 ) BACDEFHGJIKLMNO $.
  $}

  ${
    mdandyvrx10.1 $e |- ( ph \/_ ze ) $.
    mdandyvrx10.2 $e |- ( ps \/_ si ) $.
    mdandyvrx10.3 $e |- ( ch <-> ph ) $.
    mdandyvrx10.4 $e |- ( th <-> ps ) $.
    mdandyvrx10.5 $e |- ( ta <-> ph ) $.
    mdandyvrx10.6 $e |- ( et <-> ps ) $.
    $( Given the exclusivities set in the hypotheses, there exist a proof where
       ch, th, ta, et exclude ze, si accordingly.  (Contributed by Jarvin
       Udandy, 7-Sep-2016.) $)
    mdandyvrx10 $p |- ( ( ( ( ch \/_ ze ) /\ ( th \/_ si ) ) /\
( ta \/_ ze ) ) /\
( et \/_ si ) )
$=
      ( mdandyvrx5 ) BACDEFHGJIKLMNO $.
  $}

  ${
    mdandyvrx11.1 $e |- ( ph \/_ ze ) $.
    mdandyvrx11.2 $e |- ( ps \/_ si ) $.
    mdandyvrx11.3 $e |- ( ch <-> ps ) $.
    mdandyvrx11.4 $e |- ( th <-> ps ) $.
    mdandyvrx11.5 $e |- ( ta <-> ph ) $.
    mdandyvrx11.6 $e |- ( et <-> ps ) $.
    $( Given the exclusivities set in the hypotheses, there exist a proof where
       ch, th, ta, et exclude ze, si accordingly.  (Contributed by Jarvin
       Udandy, 7-Sep-2016.) $)
    mdandyvrx11 $p |- ( ( ( ( ch \/_ si ) /\ ( th \/_ si ) ) /\
( ta \/_ ze ) ) /\
( et \/_ si ) )
$=
      ( mdandyvrx4 ) BACDEFHGJIKLMNO $.
  $}

  ${
    mdandyvrx12.1 $e |- ( ph \/_ ze ) $.
    mdandyvrx12.2 $e |- ( ps \/_ si ) $.
    mdandyvrx12.3 $e |- ( ch <-> ph ) $.
    mdandyvrx12.4 $e |- ( th <-> ph ) $.
    mdandyvrx12.5 $e |- ( ta <-> ps ) $.
    mdandyvrx12.6 $e |- ( et <-> ps ) $.
    $( Given the exclusivities set in the hypotheses, there exist a proof where
       ch, th, ta, et exclude ze, si accordingly.  (Contributed by Jarvin
       Udandy, 7-Sep-2016.) $)
    mdandyvrx12 $p |- ( ( ( ( ch \/_ ze ) /\ ( th \/_ ze ) ) /\
( ta \/_ si ) ) /\
( et \/_ si ) )
$=
      ( mdandyvrx3 ) BACDEFHGJIKLMNO $.
  $}

  ${
    mdandyvrx13.1 $e |- ( ph \/_ ze ) $.
    mdandyvrx13.2 $e |- ( ps \/_ si ) $.
    mdandyvrx13.3 $e |- ( ch <-> ps ) $.
    mdandyvrx13.4 $e |- ( th <-> ph ) $.
    mdandyvrx13.5 $e |- ( ta <-> ps ) $.
    mdandyvrx13.6 $e |- ( et <-> ps ) $.
    $( Given the exclusivities set in the hypotheses, there exist a proof where
       ch, th, ta, et exclude ze, si accordingly.  (Contributed by Jarvin
       Udandy, 7-Sep-2016.) $)
    mdandyvrx13 $p |- ( ( ( ( ch \/_ si ) /\ ( th \/_ ze ) ) /\
( ta \/_ si ) ) /\
( et \/_ si ) )
$=
      ( mdandyvrx2 ) BACDEFHGJIKLMNO $.
  $}

  ${
    mdandyvrx14.1 $e |- ( ph \/_ ze ) $.
    mdandyvrx14.2 $e |- ( ps \/_ si ) $.
    mdandyvrx14.3 $e |- ( ch <-> ph ) $.
    mdandyvrx14.4 $e |- ( th <-> ps ) $.
    mdandyvrx14.5 $e |- ( ta <-> ps ) $.
    mdandyvrx14.6 $e |- ( et <-> ps ) $.
    $( Given the exclusivities set in the hypotheses, there exist a proof where
       ch, th, ta, et exclude ze, si accordingly.  (Contributed by Jarvin
       Udandy, 7-Sep-2016.) $)
    mdandyvrx14 $p |- ( ( ( ( ch \/_ ze ) /\ ( th \/_ si ) ) /\
( ta \/_ si ) ) /\
( et \/_ si ) )
$=
      ( mdandyvrx1 ) BACDEFHGJIKLMNO $.
  $}

  ${
    mdandyvrx15.1 $e |- ( ph \/_ ze ) $.
    mdandyvrx15.2 $e |- ( ps \/_ si ) $.
    mdandyvrx15.3 $e |- ( ch <-> ps ) $.
    mdandyvrx15.4 $e |- ( th <-> ps ) $.
    mdandyvrx15.5 $e |- ( ta <-> ps ) $.
    mdandyvrx15.6 $e |- ( et <-> ps ) $.
    $( Given the exclusivities set in the hypotheses, there exist a proof where
       ch, th, ta, et exclude ze, si accordingly.  (Contributed by Jarvin
       Udandy, 7-Sep-2016.) $)
    mdandyvrx15 $p |- ( ( ( ( ch \/_ si ) /\ ( th \/_ si ) ) /\ ( ta \/_ si ) )
                     /\ ( et \/_ si ) ) $=
      ( mdandyvrx0 ) BACDEFHGJIKLMNO $.
  $}

  ${
    H15NH16TH15IH16.1 $e |- ph $.
    H15NH16TH15IH16.2 $e |- ps $.
    H15NH16TH15IH16.3 $e |- ch $.
    H15NH16TH15IH16.4 $e |- th $.
    H15NH16TH15IH16.5 $e |- ta $.
    H15NH16TH15IH16.6 $e |- et $.
    H15NH16TH15IH16.7 $e |- ze $.
    H15NH16TH15IH16.8 $e |- si $.
    H15NH16TH15IH16.9 $e |- rh $.
    H15NH16TH15IH16.10 $e |- mu $.
    H15NH16TH15IH16.11 $e |- la $.
    H15NH16TH15IH16.12 $e |- ka $.
    H15NH16TH15IH16.13 $e |- jph $.
    H15NH16TH15IH16.14 $e |- jps $.
    H15NH16TH15IH16.15 $e |- jch $.
    H15NH16TH15IH16.16 $e |- jth $.
    $( Given 15 hypotheses and a 16th hypothesis, there exists a proof the 15
       imply the 16th.  (Contributed by Jarvin Udandy, 8-Sep-2016.) $)
    H15NH16TH15IH16 $p |- ( ( ( ( ( ( ( ( ( ( ( ( ( ( ( ph /\ ps ) /\ ch )
        /\ th ) /\ ta ) /\ et ) /\ ze ) /\ si ) /\ rh ) /\ mu ) /\ la ) /\ ka )
        /\ jph ) /\ jps ) /\ jch ) -> jth ) $=
      ( wa a1i ) PABUMCUMDUMEUMFUMGUMHUMIUMJUMKUMLUMMUMNUMOUMULUN $.
  $}

  $( END MAIN SECTION
   This is the end-of the main section.
  $)

  $( BEGIN EXPERIMENTS [ Search Code: 6hFY3NX45ggpE7Hx ]
   This section of the mathbox is for experiments/works-in-progress that aren't
   officially ready, are suggested to me to try, or have a high chance of being
   removed later on.

   Self-Rule: Every theorem must have in its description that it is subject to
   modification by the author and at increased risk of being abandoned
   or removed.

   Like so:
   (Experimental! Has increased risk of ..
   abandonment/removal/modification by author.)

   This section should be at the very end of the mathbox to make full use of
   available theorems elsewhere in the mathbox.

    The order of declaring things:
    variables, wffs, constants, definitions, followed by
    broad-use-formulas, and lastly more subject-specific results.

    Occasionally grouping like-formulas
    when sensible.

    But now keep the experimental versions of all that beyond this point.
  $)

  ${
    dandysum2p2e4.a $e |- ( ph <-> ( th /\ ta ) ) $.
    dandysum2p2e4.b $e |- ( ps <-> ( et /\ ze ) ) $.
    dandysum2p2e4.c $e |- ( ch <-> ( si /\ rh ) ) $.
    dandysum2p2e4.d $e |- ( th <-> F. ) $.
    dandysum2p2e4.e $e |- ( ta <-> F. ) $.
    dandysum2p2e4.f $e |- ( et <-> T. ) $.
    dandysum2p2e4.g $e |- ( ze <-> T. ) $.
    dandysum2p2e4.h $e |- ( si <-> F. ) $.
    dandysum2p2e4.i $e |- ( rh <-> F. ) $.
    dandysum2p2e4.j $e |- ( mu <-> F. ) $.
    dandysum2p2e4.k $e |- ( la <-> F. ) $.
    dandysum2p2e4.l $e |- ( ka <-> ( ( th \/_ ta ) \/_ ( th /\ ta ) ) ) $.
    dandysum2p2e4.m $e |- ( jph <-> ( ( et \/_ ze ) \/ ph ) ) $.
    dandysum2p2e4.n $e |- ( jps <-> ( ( si \/_ rh ) \/ ps ) ) $.
    dandysum2p2e4.o $e |- ( jch <-> ( ( mu \/_ la ) \/ ch ) ) $.
    $( CONTRADICTION PROVED AT 1 + 1 = 2 .

       Given the right hypotheses we can prove a dandysum of 2+2=4.  The qed
       step is the value '4' in Decimal BEING IMPLIED by the hypotheses.

       Note:  Values that when added would exceed a 4bit value are not
       supported.

       Note:  Digits begin from left (least) to right (greatest).  E.g., 1000
       would be '1', 0100 would be '2', 0010 would be '4'.

       How to perceive the hypotheses' bits in order:  ( th <-> F. ), ( ta <->
       F. ) Would be input value X's first bit, and input value Y's first bit.

       ( et <-> F ), ( ze <-> F. ) would be input value X's second bit, and
       input value Y's second bit.  (Contributed by Jarvin Udandy,
       6-Sep-2016.) $)
    dandysum2p2e4 $p |- ( ( ( ( ( ( ( ( ( ( ( ( ( ( ( ( ph <-> ( th /\ ta ) )
    /\ ( ps <-> ( et /\ ze ) ) ) /\ ( ch <-> ( si /\ rh ) ) )
    /\ ( th <-> F. ) ) /\ ( ta <-> F. ) ) /\ ( et <-> T. ) ) /\ ( ze <-> T. ) )
    /\ ( si <-> F. ) ) /\ ( rh <-> F. ) ) /\ ( mu <-> F. ) ) /\ ( la <-> F. ) )
    /\ ( ka <-> ( ( th \/_ ta ) \/_ ( th /\ ta ) ) ) )
    /\ ( jph <-> ( ( et \/_ ze ) \/ ph ) ) )
    /\ ( jps <-> ( ( si \/_ rh ) \/ ps ) ) )
    /\ ( jch <-> ( ( mu \/_ la ) \/ ch ) ) )
    -> ( ( ( ( ka <-> F. ) /\ ( jph <-> F. ) ) /\ ( jps <-> T. ) )
    /\ ( jch <-> F. ) ) ) $=
      ( wfal wb wtru wxo biimpi bothfbothsame aisbnaxb aisfina notatnand 2false
      wa aibnbaif bothtbothsame mtbir pm3.2ni pm3.2i astbstanbst aiffbbtat olci
      wo aistia bitru a1i ) LUKULZMUKULZVAZNUMULZVAZOUKULZVAADEVAZULBFGVAZULVAC
      HIVAZULVADUKULVAEUKULVAFUMULVAGUMULVAHUKULVAIUKULVAJUKULVAKUKULVALDEUNZVT
      UNZULVAMFGUNZAVJZULVANHIUNZBVJZULVAOJKUNZCVJZULVAVRVSVPVQVNVOLWDLWDUGUOWC
      VTWCVTDEDESTUPUQDEDSURUSZUTUQVBMWFMWFUHUOWEAFGFGUAUBVCUQAVTWKPVDVEVBVFNWH
      UIWHBWGBBWAQFGUAUBVGVHVKVIVLVHVFOWJOWJUJUOWICJKJKUEUFUPUQCWBHIHUCURUSRVDV
      EVBVFVM $.
  $}

  ${
    mdandysum2p2e4.1 $e |- ( jth <-> F. ) $.
    mdandysum2p2e4.2 $e |- ( jta <-> T. ) $.
    mdandysum2p2e4.a $e |- ( ph <-> ( th /\ ta ) ) $.
    mdandysum2p2e4.b $e |- ( ps <-> ( et /\ ze ) ) $.
    mdandysum2p2e4.c $e |- ( ch <-> ( si /\ rh ) ) $.
    mdandysum2p2e4.d $e |- ( th <-> jth ) $.
    mdandysum2p2e4.e $e |- ( ta <-> jth ) $.
    mdandysum2p2e4.f $e |- ( et <-> jta ) $.
    mdandysum2p2e4.g $e |- ( ze <-> jta ) $.
    mdandysum2p2e4.h $e |- ( si <-> jth ) $.
    mdandysum2p2e4.i $e |- ( rh <-> jth ) $.
    mdandysum2p2e4.j $e |- ( mu <-> jth ) $.
    mdandysum2p2e4.k $e |- ( la <-> jth ) $.
    mdandysum2p2e4.l $e |- ( ka <-> ( ( th \/_ ta ) \/_ ( th /\ ta ) ) ) $.
    mdandysum2p2e4.m $e |- ( jph <-> ( ( et \/_ ze ) \/ ph ) ) $.
    mdandysum2p2e4.n $e |- ( jps <-> ( ( si \/_ rh ) \/ ps ) ) $.
    mdandysum2p2e4.o $e |- ( jch <-> ( ( mu \/_ la ) \/ ch ) ) $.
    $( CONTRADICTION PROVED AT 1 + 1 = 2 .  Luckily Mario Carneiro did a
       successful version of his own.

       See Mario's Relevant Work:  Half adder and full adder in propositional
       calculus.

       Given the right hypotheses we can prove a dandysum of 2+2=4.  The qed
       step is the value '4' in Decimal BEING IMPLIED by the hypotheses.

       Note:  Values that when added would exceed a 4bit value are not
       supported.

       Note:  Digits begin from left (least) to right (greatest).  E.g., 1000
       would be '1', 0100 would be '2'. 0010 would be '4'.

       How to perceive the hypotheses' bits in order:  ( th <-> F. ), ( ta <->
       F. ) Would be input value X's first bit, and input value Y's first bit.

       ( et <-> F. ), ( ze <-> F. ) would be input value X's second bit, and
       input value Y's second bit.

       In mdandysum2p2e4, one might imagine what jth or jta could be then do
       the math with their truths.  Also limited to the restriction jth, jta
       are having opposite truths equivalent to the stated truth constants.
       (Contributed by Jarvin Udandy, 6-Sep-2016.) $)
    mdandysum2p2e4 $p |- ( ( ( ( ( ( ( ( ( ( ( ( ( ( ( ( ph <-> ( th /\ ta ) )
    /\ ( ps <-> ( et /\ ze ) ) ) /\ ( ch <-> ( si /\ rh ) ) )
    /\ ( th <-> F. ) ) /\ ( ta <-> F. ) ) /\ ( et <-> T. ) ) /\ ( ze <-> T. ) )
    /\ ( si <-> F. ) ) /\ ( rh <-> F. ) ) /\ ( mu <-> F. ) ) /\ ( la <-> F. ) )
    /\ ( ka <-> ( ( th \/_ ta ) \/_ ( th /\ ta ) ) ) )
    /\ ( jph <-> ( ( et \/_ ze ) \/ ph ) ) )
    /\ ( jps <-> ( ( si \/_ rh ) \/ ps ) ) )
    /\ ( jch <-> ( ( mu \/_ la ) \/ ch ) ) )
    -> ( ( ( ( ka <-> F. ) /\ ( jph <-> F. ) ) /\ ( jps <-> T. ) )
    /\ ( jch <-> F. ) ) ) $=
      ( aisbbisfaisf aiffbbtat dandysum2p2e4 ) ABCDEFGHIJKLMNOTUAUBDPUCRUOEPUDR
      UOFQUESUPGQUFSUPHPUGRUOIPUHRUOJPUIRUOKPUJRUOUKULUMUNUQ $.
  $}

  $( END EXPERIMENTS
   This is the end-of the experiment section of the mathbox.
   Which should be at the end of the mathbox too.
  $)

$( (End of Jarvin Udandy's mathbox.) $)
