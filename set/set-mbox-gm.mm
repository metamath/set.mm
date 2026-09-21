$[ set-main.mm $]
$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Mathbox for Giovanni Mascellani
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Tools for automatic proof building
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  The results in this section are mostly meant for being used by automatic
  proof building programs.  As a result, they might appear less useful or
  meaningful than others to human beings.

$)

  ${
    efald2.1 $e |- ( -. ph -> F. ) $.
    $( A proof by contradiction.  (Contributed by Giovanni Mascellani,
       15-Sep-2017.) $)
    efald2 $p |- ph $=
      ( wtru wn wfal adantl efald mptru ) ACAADECBFGH $.
  $}

  $( Simplification rule of negation across a biconditional.  (Contributed by
     Giovanni Mascellani, 15-Sep-2017.) $)
  notbinot1 $p |- ( -. ( -. ph <-> ps ) <-> ( ph <-> ps ) ) $=
    ( wb wn nbbn bicomi con1bii ) ABCZADBCZIHDABEFG $.

  $( Biconditional of its own negation is a contradiction.  (Contributed by
     Giovanni Mascellani, 15-Sep-2017.) $)
  bicontr $p |- ( ( -. ph <-> ph ) <-> F. ) $=
    ( wn wb biid notbinot1 mpbir bifal ) ABACZHBAACADAAEFG $.

  $( An equivalent formula for implying a disjunction.  (Contributed by
     Giovanni Mascellani, 15-Sep-2017.) $)
  impor $p |- ( ( ph -> ( ps \/ ch ) ) <-> ( ( -. ph \/ ps ) \/ ch ) ) $=
    ( wo wi wn imor orass bitr4i ) ABCDZEAFZJDKBDCDAJGKBCHI $.

  $( The falsum ` F. ` can be removed from a disjunction.  (Contributed by
     Giovanni Mascellani, 15-Sep-2017.) $)
  orfa $p |- ( ( ph \/ F. ) <-> ph ) $=
    ( wfal wo wn wi orcom df-or bitri fal pm2.27 ax-mp sylbi orc impbii ) ABCZA
    OBDZAEZAOBACQABFBAGHPQAEIPAJKLABMN $.

  $( Commutation rule between negation and biconditional.  (Contributed by
     Giovanni Mascellani, 15-Sep-2017.) $)
  notbinot2 $p |- ( -. ( ph <-> ps ) <-> ( -. ph <-> ps ) ) $=
    ( wn wb nbbn bicomi ) ACBDABDCABEF $.

  $( A rewriting rule for biconditional.  (Contributed by Giovanni Mascellani,
     15-Sep-2017.) $)
  biimpor $p |- ( ( ( ph <-> ps ) -> ch ) <-> ( ( -. ph <-> ps ) \/ ch ) ) $=
    ( wb wi wn wo imor notbinot2 orbi1i bitri ) ABDZCELFZCGAFBDZCGLCHMNCABIJK
    $.

  ${
    orfa1.1 $e |- ( ph -> ps ) $.
    $( Add a contradicting disjunct to an antecedent.  (Contributed by Giovanni
       Mascellani, 15-Sep-2017.) $)
    orfa1 $p |- ( ( ph \/ F. ) -> ps ) $=
      ( wfal falim jaoi ) ABDCBEF $.
  $}

  ${
    orfa2.1 $e |- ( ph -> F. ) $.
    $( Remove a contradicting disjunct from an antecedent.  (Contributed by
       Giovanni Mascellani, 15-Sep-2017.) $)
    orfa2 $p |- ( ( ph \/ ps ) -> ps ) $=
      ( wo wfal orim1i falim id jaoi syl ) ABDEBDBAEBCFEBBBGBHIJ $.
  $}

  ${
    bifald.1 $e |- ( ph -> -. ps ) $.
    $( Infer the equivalence to a contradiction from a negation, in deduction
       form.  (Contributed by Giovanni Mascellani, 15-Sep-2017.) $)
    bifald $p |- ( ph -> ( ps <-> F. ) ) $=
      ( wn wfal wb id falim pm5.21ni syl ) ABDBEFCBBEBGBHIJ $.
  $}

  ${
    cnf1dd.1 $e |- ( ph -> ( ps -> -. ch ) ) $.
    cnf1dd.2 $e |- ( ph -> ( ps -> ( ch \/ th ) ) ) $.
    $( A lemma for Conjunctive Normal Form unit propagation, in double
       deduction form.  (Contributed by Giovanni Mascellani, 19-Mar-2018.) $)
    cnf1dd $p |- ( ph -> ( ps -> th ) ) $=
      ( wn wo wa jcad wi df-or pm3.35 sylan2b syl6 ) ABCGZCDHZIDABPQEFJQPPDKDCD
      LPDMNO $.
  $}

  ${
    cnf2dd.1 $e |- ( ph -> ( ps -> -. th ) ) $.
    cnf2dd.2 $e |- ( ph -> ( ps -> ( ch \/ th ) ) ) $.
    $( A lemma for Conjunctive Normal Form unit propagation, in double
       deduction form.  (Contributed by Giovanni Mascellani, 19-Mar-2018.) $)
    cnf2dd $p |- ( ph -> ( ps -> ch ) ) $=
      ( wo pm1.4 syl6 cnf1dd ) ABDCEABCDGDCGFCDHIJ $.
  $}

  ${
    cnfn1dd.1 $e |- ( ph -> ( ps -> ch ) ) $.
    cnfn1dd.2 $e |- ( ph -> ( ps -> ( -. ch \/ th ) ) ) $.
    $( A lemma for Conjunctive Normal Form unit propagation, in double
       deduction form.  (Contributed by Giovanni Mascellani, 19-Mar-2018.) $)
    cnfn1dd $p |- ( ph -> ( ps -> th ) ) $=
      ( wn notnot syl6 cnf1dd ) ABCGZDABCKGECHIFJ $.
  $}

  ${
    cnfn2dd.1 $e |- ( ph -> ( ps -> th ) ) $.
    cnfn2dd.2 $e |- ( ph -> ( ps -> ( ch \/ -. th ) ) ) $.
    $( A lemma for Conjunctive Normal Form unit propagation, in double
       deduction form.  (Contributed by Giovanni Mascellani, 19-Mar-2018.) $)
    cnfn2dd $p |- ( ph -> ( ps -> ch ) ) $=
      ( wn notnot syl6 cnf2dd ) ABCDGZABDKGEDHIFJ $.
  $}

  ${
    or32dd.1 $e |- ( ph -> ( ps -> ( ( ch \/ th ) \/ ta ) ) ) $.
    $( A rearrangement of disjuncts, in double deduction form.  (Contributed by
       Giovanni Mascellani, 19-Mar-2018.) $)
    or32dd $p |- ( ph -> ( ps -> ( ( ch \/ ta ) \/ th ) ) ) $=
      ( wo or32 imbitrrdi ) ABCDGEGCEGDGFCEDHI $.
  $}

  ${
    notornotel1.1 $e |- ( ph -> -. ( -. ps \/ ch ) ) $.
    $( A lemma for not-or-not elimination, in deduction form.  (Contributed by
       Giovanni Mascellani, 19-Mar-2018.) $)
    notornotel1 $p |- ( ph -> ps ) $=
      ( wn wo wa ioran biimpi simpl notnotr 4syl ) ABEZCFEZMEZCEZGZOBDNQMCHIOPJ
      BKL $.
  $}

  ${
    notornotel2.1 $e |- ( ph -> -. ( ps \/ -. ch ) ) $.
    $( A lemma for not-or-not elimination, in deduction form.  (Contributed by
       Giovanni Mascellani, 19-Mar-2018.) $)
    notornotel2 $p |- ( ph -> ch ) $=
      ( wn wo orcom sylnibr notornotel1 ) ACBABCEZFJBFDJBGHI $.
  $}

  ${
    contrd.1 $e |- ( ph -> ( -. ps -> ch ) ) $.
    contrd.2 $e |- ( ph -> ( -. ps -> -. ch ) ) $.
    $( A proof by contradiction, in deduction form.  (Contributed by Giovanni
       Mascellani, 19-Mar-2018.) $)
    contrd $p |- ( ph -> ps ) $=
      ( wn wa wi jcad pm2.24 imp imim2i pm2.18d syl ) ABFZCCFZGZHZBAOCPDEIRBQBO
      CPBCBJKLMN $.
  $}

  ${
    an12i.1 $e |- ( ph /\ ( ps /\ ch ) ) $.
    $( An inference from commuting operands in a chain of conjunctions.
       (Contributed by Giovanni Mascellani, 22-May-2019.) $)
    an12i $p |- ( ps /\ ( ph /\ ch ) ) $=
      ( wa an12 mpbir ) BACEEABCEEDBACFG $.
  $}

  ${
    exmid2.1 $e |- ( ( ps /\ ph ) -> ch ) $.
    exmid2.2 $e |- ( ( -. ps /\ et ) -> ch ) $.
    $( An excluded middle law.  (Contributed by Giovanni Mascellani,
       23-May-2019.) $)
    exmid2 $p |- ( ( ph /\ et ) -> ch ) $=
      ( wa simpl anim2i ancoms syl wn simpr pm2.61dan ) ADGZBCOBGBAGZCBOPOABADH
      IJEKOBLZGQDGZCQORODQADMIJFKN $.
  $}

  ${
    selconj.1 $e |- ( ph <-> ( ps /\ ch ) ) $.
    $( An inference for selecting one of a list of conjuncts.  (Contributed by
       Giovanni Mascellani, 23-May-2019.) $)
    selconj $p |- ( ( et /\ ph ) <-> ( ps /\ ( et /\ ch ) ) ) $=
      ( wa anbi2i an12 bitr4i ) DAFDBCFZFBDCFFAJDEGBDCHI $.
  $}

  $( Add true as a conjunct.  (Contributed by Giovanni Mascellani,
     23-May-2019.) $)
  truconj $p |- ( ph <-> ( T. /\ ph ) ) $=
    ( wtru wa truan bicomi ) BACAADE $.

  ${
    orel.1 $e |- ( ( ps /\ et ) -> th ) $.
    orel.2 $e |- ( ( ch /\ rh ) -> th ) $.
    orel.3 $e |- ( ph -> ( ps \/ ch ) ) $.
    $( An inference for disjunction elimination.  (Contributed by Giovanni
       Mascellani, 24-May-2019.) $)
    orel $p |- ( ( ph /\ ( et /\ rh ) ) -> th ) $=
      ( wa simprl ancoms sylan simprr wo adantr mpjaodan ) AEFJZJZBDCSEBDAEFKBE
      DGLMSFCDAEFNCFDHLMABCORIPQ $.
  $}

  ${
    negel.1 $e |- ( ps -> ch ) $.
    negel.2 $e |- ( ph -> -. ch ) $.
    $( An inference for negation elimination.  (Contributed by Giovanni
       Mascellani, 24-May-2019.) $)
    negel $p |- ( ( ph /\ ps ) -> F. ) $=
      ( wa adantl wn adantr pm2.21fal ) ABFCBCADGACHBEIJ $.
  $}

  ${
    botel.1 $e |- ( ph -> F. ) $.
    $( An inference for bottom elimination.  (Contributed by Giovanni
       Mascellani, 24-May-2019.) $)
    botel $p |- ( ph -> ps ) $=
      ( wfal falim syl ) ADBCBEF $.
  $}

  ${
    tradd.1 $e |- ( ph <-> ps ) $.
    $( Add top ad a conjunct.  (Contributed by Giovanni Mascellani,
       24-May-2019.) $)
    tradd $p |- ( ph <-> ( T. /\ ps ) ) $=
      ( wtru wa truan bitr4i ) ABDBECBFG $.
  $}

  ${
    gm-sbtru.1 $e |- A e. _V $.
    $( Substitution does not change truth.  (Contributed by Giovanni
       Mascellani, 24-May-2019.) $)
    gm-sbtru $p |- ( [. A / x ]. T. <-> T. ) $=
      ( cvv wcel wtru wsbc wb sbcg ax-mp ) BDEFABGFHCFABDIJ $.
  $}

  ${
    sbfal.1 $e |- A e. _V $.
    $( Substitution does not change falsity.  (Contributed by Giovanni
       Mascellani, 24-May-2019.) $)
    sbfal $p |- ( [. A / x ]. F. <-> F. ) $=
      ( cvv wcel wfal wsbc wb sbcg ax-mp ) BDEFABGFHCFABDIJ $.
  $}

  ${
    sbcani.1 $e |- ( [. A / x ]. ph <-> ch ) $.
    sbcani.2 $e |- ( [. A / x ]. ps <-> et ) $.
    $( Distribution of class substitution over conjunction, in inference form.
       (Contributed by Giovanni Mascellani, 27-May-2019.) $)
    sbcani $p |- ( [. A / x ]. ( ph /\ ps ) <-> ( ch /\ et ) ) $=
      ( wa wsbc sbcan anbi12i bitri ) ABIEFJAEFJZBEFJZICDIABEFKNCODGHLM $.
  $}

  ${
    sbcori.1 $e |- ( [. A / x ]. ph <-> ch ) $.
    sbcori.2 $e |- ( [. A / x ]. ps <-> et ) $.
    $( Distribution of class substitution over disjunction, in inference form.
       (Contributed by Giovanni Mascellani, 27-May-2019.) $)
    sbcori $p |- ( [. A / x ]. ( ph \/ ps ) <-> ( ch \/ et ) ) $=
      ( wo wsbc sbcor orbi12i bitri ) ABIEFJAEFJZBEFJZICDIABEFKNCODGHLM $.
  $}

  ${
    sbcimi.1 $e |- A e. _V $.
    sbcimi.2 $e |- ( [. A / x ]. ph <-> ch ) $.
    sbcimi.3 $e |- ( [. A / x ]. ps <-> et ) $.
    $( Distribution of class substitution over implication, in inference form.
       (Contributed by Giovanni Mascellani, 27-May-2019.) $)
    sbcimi $p |- ( [. A / x ]. ( ph -> ps ) <-> ( ch -> et ) ) $=
      ( wi wsbc cvv wcel wb sbcimg ax-mp imbi12i bitri ) ABJEFKZAEFKZBEFKZJZCDJ
      FLMSUBNGABEFLOPTCUADHIQR $.
  $}

  ${
    sbcni.1 $e |- A e. _V $.
    sbcni.2 $e |- ( [. A / x ]. ph <-> ps ) $.
    $( Move class substitution inside a negation, in inference form.
       (Contributed by Giovanni Mascellani, 27-May-2019.) $)
    sbcni $p |- ( [. A / x ]. -. ph <-> -. ps ) $=
      ( wn wsbc cvv wcel wb sbcng ax-mp xchbinx ) AGCDHZACDHZBDIJOPGKEACDILMFN
      $.
  $}

  ${
    sbali.1 $e |- A e. _V $.
    $( Discard class substitution in a universal quantification when
       substituting the quantified variable, in inference form.  (Contributed
       by Giovanni Mascellani, 27-May-2019.) $)
    sbali $p |- ( [. A / x ]. A. x ph <-> A. x ph ) $=
      ( wal nfa1 sbcgfi ) ABEBCDABFG $.
  $}

  ${
    sbexi.1 $e |- A e. _V $.
    $( Discard class substitution in an existential quantification when
       substituting the quantified variable, in inference form.  (Contributed
       by Giovanni Mascellani, 27-May-2019.) $)
    sbexi $p |- ( [. A / x ]. E. x ph <-> E. x ph ) $=
      ( wex nfe1 sbcgfi ) ABEBCDABFG $.
  $}

  ${
    $d ph z $.  $d x y $.  $d x z $.  $d y z $.  $d z A $.
    sbcalf.1 $e |- F/_ y A $.
    $( Move universal quantifier in and out of class substitution, with an
       explicit nonfree variable condition.  (Contributed by Giovanni
       Mascellani, 29-May-2019.) $)
    sbcalf $p |- ( [. A / x ]. A. y ph <-> A. y [. A / x ]. ph ) $=
      ( vz wal wsbc wsb sb8v sbcbii sbcal nfs1v nfsbcw nfv weq sbequ12r sbcbidv
      cbvalv1 3bitri ) ACGZBDHACFIZFGZBDHUBBDHZFGABDHZCGUAUCBDACFJKUBFBDLUDUEFC
      UBCBDEACFMNUEFOFCPUBABDAFCQRST $.
  $}

  ${
    $d ph z $.  $d x y $.  $d x z $.  $d y z $.  $d z A $.
    sbcexf.1 $e |- F/_ y A $.
    $( Move existential quantifier in and out of class substitution, with an
       explicit nonfree variable condition.  (Contributed by Giovanni
       Mascellani, 29-May-2019.) $)
    sbcexf $p |- ( [. A / x ]. E. y ph <-> E. y [. A / x ]. ph ) $=
      ( vz wex wsbc wsb nfv sb8ef sbcbii sbcex2 nfsbcw sbequ12r sbcbidv cbvexv1
      nfs1v weq 3bitri ) ACGZBDHACFIZFGZBDHUBBDHZFGABDHZCGUAUCBDACFAFJKLUBFBDMU
      DUEFCUBCBDEACFRNUEFJFCSUBABDAFCOPQT $.
  $}

  ${
    $d x y $.
    sbcalfi.1 $e |- F/_ y A $.
    sbcalfi.2 $e |- ( [. A / x ]. ph <-> ps ) $.
    $( Move universal quantifier in and out of class substitution, with an
       explicit nonfree variable condition and in inference form.  (Contributed
       by Giovanni Mascellani, 30-May-2019.) $)
    sbcalfi $p |- ( [. A / x ]. A. y ph <-> A. y ps ) $=
      ( wal wsbc sbcalf albii bitri ) ADHCEIACEIZDHBDHACDEFJMBDGKL $.
  $}

  ${
    $d x y $.
    sbcexfi.1 $e |- F/_ y A $.
    sbcexfi.2 $e |- ( [. A / x ]. ph <-> ps ) $.
    $( Move existential quantifier in and out of class substitution, with an
       explicit nonfree variable condition and in inference form.  (Contributed
       by Giovanni Mascellani, 30-May-2019.) $)
    sbcexfi $p |- ( [. A / x ]. E. y ph <-> E. y ps ) $=
      ( wex wsbc sbcexf exbii bitri ) ADHCEIACEIZDHBDHACDEFJMBDGKL $.
  $}

  ${
    spsbcdi.1 $e |- A e. _V $.
    spsbcdi.2 $e |- ( ph -> A. x ch ) $.
    spsbcdi.3 $e |- ( [. A / x ]. ch <-> ps ) $.
    $( A lemma for eliminating a universal quantifier, in inference form.
       (Contributed by Giovanni Mascellani, 30-May-2019.) $)
    spsbcdi $p |- ( ph -> ps ) $=
      ( wsbc cvv wcel a1i spsbcd sylib ) ACDEIBACDEJEJKAFLGMHN $.
  $}

  ${
    $d x y $.
    alrimii.1 $e |- F/ y ph $.
    alrimii.2 $e |- ( ph -> ps ) $.
    alrimii.3 $e |- ( [. y / x ]. ch <-> ps ) $.
    alrimii.4 $e |- F/ y ch $.
    $( A lemma for introducing a universal quantifier, in inference form.
       (Contributed by Giovanni Mascellani, 30-May-2019.) $)
    alrimii $p |- ( ph -> A. x ch ) $=
      ( cv wsbc wal sylibr alrimi nfsbc1v sbceq2a cbvalv1 sylib ) ACDEJZKZELCDL
      ATEFABTGHMNTCEDCDSOICDSPQR $.
  $}

  ${
    spesbcdi.1 $e |- ( ph -> ps ) $.
    spesbcdi.2 $e |- ( [. A / x ]. ch <-> ps ) $.
    $( A lemma for introducing an existential quantifier, in inference form.
       (Contributed by Giovanni Mascellani, 30-May-2019.) $)
    spesbcdi $p |- ( ph -> E. x ch ) $=
      ( wsbc sylibr spesbcd ) ACDEABCDEHFGIJ $.
  $}

  ${
    exlimddvf.1 $e |- ( ph -> E. x th ) $.
    exlimddvf.2 $e |- F/ x ps $.
    exlimddvf.3 $e |- ( ( th /\ ps ) -> ch ) $.
    exlimddvf.4 $e |- F/ x ch $.
    $( A lemma for eliminating an existential quantifier.  (Contributed by
       Giovanni Mascellani, 30-May-2019.) $)
    exlimddvf $p |- ( ( ph /\ ps ) -> ch ) $=
      ( wex expcom exlimd mpan9 ) ADEJBCFBDCEGIDBCHKLM $.
  $}

  ${
    exlimddvfi.1 $e |- ( ph -> E. x th ) $.
    exlimddvfi.2 $e |- F/ y th $.
    exlimddvfi.3 $e |- F/ y ps $.
    exlimddvfi.4 $e |- ( [. y / x ]. th <-> et ) $.
    exlimddvfi.5 $e |- ( ( et /\ ps ) -> ch ) $.
    exlimddvfi.6 $e |- F/ y ch $.
    $( A lemma for eliminating an existential quantifier, in inference form.
       (Contributed by Giovanni Mascellani, 31-May-2019.) $)
    exlimddvfi $p |- ( ( ph /\ ps ) -> ch ) $=
      ( wsb wex sb8e sylib cv wsbc sbsbc bitri sylanb exlimddvf ) ABCDFGNZGADFO
      UDGOHDFGIPQJUDEBCUDDFGRSEDFGTKUALUBMUC $.
  $}

  ${
    sbceq1ddi.1 $e |- ( ph -> A = B ) $.
    sbceq1ddi.2 $e |- ( ps -> th ) $.
    sbceq1ddi.3 $e |- ( [. A / x ]. ch <-> th ) $.
    sbceq1ddi.4 $e |- ( [. B / x ]. ch <-> et ) $.
    $( A lemma for eliminating inequality, in inference form.  (Contributed by
       Giovanni Mascellani, 31-May-2019.) $)
    sbceq1ddi $p |- ( ( ph /\ ps ) -> et ) $=
      ( wa wsbc wceq adantr sylibr adantl sbceq1dd sylib ) ABMZCFHNEUACFGHAGHOB
      IPBCFGNZABDUBJKQRSLT $.
  $}

  ${
    $d x y $.  $d x A $.  $d y A $.  $d y B $.
    sbccom2lem.1 $e |- A e. _V $.
    $( Lemma for ~ sbccom2 .  (Contributed by Giovanni Mascellani,
       31-May-2019.) $)
    sbccom2lem $p |- ( [. A / x ]. [. B / y ]. ph
        <-> [. [_ A / x ]_ B / y ]. [. A / x ]. ph ) $=
      ( cv wceq wa wex csb wsbc sbcan sbc5 csbconstgi sbceqi anbi1i exbii bitri
      eqid 3bitr3i sbcbii 19.42v bicomi excom 3bitr4i ) BGDHZCGZEHZAIZIZBJZCJZU
      HBDEKZHZABDLZIZCJACELZBDLZUPCUNLULUQCUJBDLUIBDLZUPIULUQUIABDMUJBDNUTUOUPB
      DUHEUHUNFBCDFOUNTPQUARUSUGUJCJZIZBJZUMUSVABDLVCURVABDACENUBVABDNSVCUKCJZB
      JUMVBVDBVDVBUGUJCUCUDRUKBCUESSUPCUNNUF $.
  $}

  ${
    $d ph z $.  $d ph w $.  $d x y $.  $d x z $.  $d x w $.  $d y z $.
    $d y A $.  $d z w $.  $d z A $.  $d z B $.  $d w A $.  $d w B $.  $d w y $.
    sbccom2.1 $e |- A e. _V $.
    $( Commutative law for double class substitution.  (Contributed by Giovanni
       Mascellani, 31-May-2019.) $)
    sbccom2 $p |- ( [. A / x ]. [. B / y ]. ph
        <-> [. [_ A / x ]_ B / y ]. [. A / x ]. ph ) $=
      ( vw vz wsbc cv csb sbccow bicomi sbcbii sbccom2lem 3bitri wceq wb csbcow
      vex dfsbcq ax-mp bitri sbccom ) ACEIZBDIZACGJZIZBDIZGBDEKZIZABDIZCUGIZGUJ
      IULCUJIUFUIGHDBHJZEKZKZIZUKUFUHBUNIZGUOIZHDIZURHDIZGUPIUQUFUHGEIZBDIZVBBU
      NIZHDIZUTUEVBBDVBUEACGELMNVEVCVBBHDLMVDUSHDUHBGUNEHTONPURHGDUOFOVAUIGUPUH
      BHDLNPUPUJQUQUKRBHDESUIGUPUJUAUBUCUIUMGUJABCDUGUDNULCGUJLP $.
  $}

  ${
    $d ph z $.  $d x y $.  $d x z $.  $d y z $.  $d z A $.
    sbccom2f.1 $e |- A e. _V $.
    sbccom2f.2 $e |- F/_ y A $.
    $( Commutative law for double class substitution, with nonfree variable
       condition.  (Contributed by Giovanni Mascellani, 31-May-2019.) $)
    sbccom2f $p |- ( [. A / x ]. [. B / y ]. ph
        <-> [. [_ A / x ]_ B / y ]. [. A / x ]. ph ) $=
      ( vz wsbc cv csb sbccow bicomi sbcbii sbccom2 vex wceq wb csbgfi bitri
      dfsbcq ax-mp 3bitri ) ACEIZBDIACHJZIZHEIZBDIUFBDIZHBDEKZIZABDIZCUIIZUDUGB
      DUGUDACHELMNUFBHDEFOUJUKCUEIZHUIIULUHUMHUIUMUHUMUFBCUEDKZIZUHACBUEDHPZOUN
      DQUOUHRCUEDUPGSUFBUNDUAUBTMNUKCHUILTUC $.
  $}

  ${
    $d x y $.
    sbccom2fi.1 $e |- A e. _V $.
    sbccom2fi.2 $e |- F/_ y A $.
    sbccom2fi.3 $e |- [_ A / x ]_ B = C $.
    sbccom2fi.4 $e |- ( [. A / x ]. ph <-> ps ) $.
    $( Commutative law for double class substitution, with nonfree variable
       condition and in inference form.  (Contributed by Giovanni Mascellani,
       1-Jun-2019.) $)
    sbccom2fi $p |- ( [. A / x ]. [. B / y ]. ph <-> [. C / y ]. ps ) $=
      ( wsbc csb sbccom2f wceq wb dfsbcq ax-mp sbcbii 3bitri ) ADFLCELACELZDCEF
      MZLZUADGLZBDGLACDEFHINUBGOUCUDPJUADUBGQRUABDGKST $.
  $}

  ${
    $d x y $.  $d x z $.  $d y z $.  $d z A $.  $d z B $.  $d z C $.  $d z D $.
    $d z E $.
    csbcom2fi.1 $e |- A e. _V $.
    csbcom2fi.2 $e |- F/_ y A $.
    csbcom2fi.3 $e |- [_ A / x ]_ B = C $.
    csbcom2fi.4 $e |- [_ A / x ]_ D = E $.
    $( Commutative law for double class substitution in a class, with nonfree
       variable condition and in inference form.  (Contributed by Giovanni
       Mascellani, 4-Jun-2019.) $)
    csbcom2fi $p |- [_ A / x ]_ [_ B / y ]_ D = [_ C / y ]_ E $=
      ( vz csb cv wcel wsbc df-csb eqabri sbcbii bitri eleq2i bitr3i sbccom2fi
      sbcel2 3bitri eqriv ) LACBDFMZMZBEGMZLNZUHOZUJFOZBDPZACPZUJGOZBEPUJUIOUKU
      JUGOZACPZUNUQLUHALCUGQRUPUMACUMLUGBLDFQRSTULUOABCDEHIJULACPZUJACFMZOUOURL
      USALCFQRUSGUJKUAUBUCBEUJGUDUEUF $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Tseitin axioms
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  A collection of Tseitin axioms used to convert a wff to Conjunctive
  Normal Form.

$)

  $( Refutation of falsity, in deduction form.  (Contributed by Giovanni
     Mascellani, 24-Mar-2018.) $)
  fald $p |- ( th -> -. F. ) $=
    ( wfal wn fal a1i ) BCADE $.

  $( A Tseitin axiom for logical implication, in deduction form.  (Contributed
     by Giovanni Mascellani, 24-Mar-2018.) $)
  tsim1 $p |- ( th -> ( ( -. ph \/ ps ) \/ -. ( ph -> ps ) ) ) $=
    ( wn wo wi exmid df-or notnotb bicomi imbi1i bitri orbi1i mpbir a1i ) ADZBE
    ZABFZDZEZCTRSERGQRSQPDZBFRPBHUAABAUAAIJKLMNO $.

  $( A Tseitin axiom for logical implication, in deduction form.  (Contributed
     by Giovanni Mascellani, 24-Mar-2018.) $)
  tsim2 $p |- ( th -> ( ph \/ ( ph -> ps ) ) ) $=
    ( wi wo curryax a1i ) AABDECABFG $.

  $( A Tseitin axiom for logical implication, in deduction form.  (Contributed
     by Giovanni Mascellani, 24-Mar-2018.) $)
  tsim3 $p |- ( th -> ( -. ps \/ ( ph -> ps ) ) ) $=
    ( wn wi wo ax-1 imori a1i ) BDABEZFCBJBAGHI $.

  $( A Tseitin axiom for logical biconditional, in deduction form.
     (Contributed by Giovanni Mascellani, 24-Mar-2018.) $)
  tsbi1 $p |- ( th -> ( ( -. ph \/ -. ps ) \/ ( ph <-> ps ) ) ) $=
    ( wn wo wb wa pm5.1 olcd pm3.13 orcd pm2.61i a1i ) ADBDEZABFZEZCABGZPQONABH
    IQDNOABJKLM $.

  $( A Tseitin axiom for logical biconditional, in deduction form.
     (Contributed by Giovanni Mascellani, 24-Mar-2018.) $)
  tsbi2 $p |- ( th -> ( ( ph \/ ps ) \/ ( ph <-> ps ) ) ) $=
    ( wo wb wn wa pm5.21 olcd pm4.57 biimpi orcd pm2.61i a1i ) ABDZABEZDZCAFBFG
    ZQRPOABHIRFZOPSOABJKLMN $.

  $( A Tseitin axiom for logical biconditional, in deduction form.
     (Contributed by Giovanni Mascellani, 24-Mar-2018.) $)
  tsbi3 $p |- ( th -> ( ( ph \/ -. ps ) \/ -. ( ph <-> ps ) ) ) $=
    ( wn wo wb wi biimpr con34b pm2.54 sylbi syl con3i orri a1i ) ABDZEZABFZDZE
    CQSRQRBAGZQABHTADPGQBAIAPJKLMNO $.

  $( A Tseitin axiom for logical biconditional, in deduction form.
     (Contributed by Giovanni Mascellani, 24-Mar-2018.) $)
  tsbi4 $p |- ( th -> ( ( -. ph \/ ps ) \/ -. ( ph <-> ps ) ) ) $=
    ( wn wo wb tsbi3 orcom bicom notbii orbi12i sylib ) CBADZEZBAFZDZEMBEZABFZD
    ZEBACGNQPSBMHORBAIJKL $.

  $( A Tseitin axiom for logical exclusive disjunction, in deduction form.
     (Contributed by Giovanni Mascellani, 24-Mar-2018.) $)
  tsxo1 $p |- ( th -> ( ( -. ph \/ -. ps ) \/ -. ( ph \/_ ps ) ) ) $=
    ( wn wo wb wxo tsbi1 xnor orbi2i sylib ) CADBDEZABFZELABGDZEABCHMNLABIJK $.

  $( A Tseitin axiom for logical exclusive disjunction, in deduction form.
     (Contributed by Giovanni Mascellani, 24-Mar-2018.) $)
  tsxo2 $p |- ( th -> ( ( ph \/ ps ) \/ -. ( ph \/_ ps ) ) ) $=
    ( wo wb wxo wn tsbi2 xnor orbi2i sylib ) CABDZABEZDLABFGZDABCHMNLABIJK $.

  $( A Tseitin axiom for logical exclusive disjunction, in deduction form.
     (Contributed by Giovanni Mascellani, 24-Mar-2018.) $)
  tsxo3 $p |- ( th -> ( ( ph \/ -. ps ) \/ ( ph \/_ ps ) ) ) $=
    ( wn wo wb wxo tsbi3 df-xor bicomi orbi2i sylib ) CABDEZABFDZEMABGZEABCHNOM
    ONABIJKL $.

  $( A Tseitin axiom for logical exclusive disjunction, in deduction form.
     (Contributed by Giovanni Mascellani, 24-Mar-2018.) $)
  tsxo4 $p |- ( th -> ( ( -. ph \/ ps ) \/ ( ph \/_ ps ) ) ) $=
    ( wn wo wb wxo tsbi4 df-xor bicomi orbi2i sylib ) CADBEZABFDZEMABGZEABCHNOM
    ONABIJKL $.

  $( A Tseitin axiom for logical conjunction, in deduction form.  (Contributed
     by Giovanni Mascellani, 24-Mar-2018.) $)
  tsan1 $p |- ( th -> ( ( -. ph \/ -. ps ) \/ ( ph /\ ps ) ) ) $=
    ( wn wo wa pm3.12 a1i ) ADBDEABFECABGH $.

  $( A Tseitin axiom for logical conjunction, in deduction form.  (Contributed
     by Giovanni Mascellani, 24-Mar-2018.) $)
  tsan2 $p |- ( th -> ( ph \/ -. ( ph /\ ps ) ) ) $=
    ( wa wn wo pm3.14 orcs orri a1i ) AABDEZFCAKAEBEKABGHIJ $.

  $( A Tseitin axiom for logical conjunction, in deduction form.  (Contributed
     by Giovanni Mascellani, 24-Mar-2018.) $)
  tsan3 $p |- ( th -> ( ps \/ -. ( ph /\ ps ) ) ) $=
    ( wa wn wo pm3.14 olcs orri a1i ) BABDEZFCBKAEBEKABGHIJ $.

  $( A Tseitin axiom for logical incompatibility, in deduction form.
     (Contributed by Giovanni Mascellani, 24-Mar-2018.) $)
  tsna1 $p |- ( th -> ( ( -. ph \/ -. ps ) \/ -. ( ph -/\ ps ) ) ) $=
    ( wn wo wa wnan tsan1 notnotb df-nan bitr3i con4bii orbi2i sylibr ) CADBDEZ
    ABFZEOABGZDZEABCHRPORPRDQPDQIABJKLMN $.

  $( A Tseitin axiom for logical incompatibility, in deduction form.
     (Contributed by Giovanni Mascellani, 24-Mar-2018.) $)
  tsna2 $p |- ( th -> ( ph \/ ( ph -/\ ps ) ) ) $=
    ( wa wn wo wnan tsan2 df-nan orbi2i sylibr ) CAABDEZFAABGZFABCHMLAABIJK $.

  $( A Tseitin axiom for logical incompatibility, in deduction form.
     (Contributed by Giovanni Mascellani, 24-Mar-2018.) $)
  tsna3 $p |- ( th -> ( ps \/ ( ph -/\ ps ) ) ) $=
    ( wa wn wo wnan tsan3 df-nan orbi2i sylibr ) CBABDEZFBABGZFABCHMLBABIJK $.

  $( A Tseitin axiom for logical disjunction, in deduction form.  (Contributed
     by Giovanni Mascellani, 25-Mar-2018.) $)
  tsor1 $p |- ( th -> ( ( ph \/ ps ) \/ -. ( ph \/ ps ) ) ) $=
    ( wo exmidd ) CABDE $.

  $( A Tseitin axiom for logical disjunction, in deduction form.  (Contributed
     by Giovanni Mascellani, 25-Mar-2018.) $)
  tsor2 $p |- ( th -> ( -. ph \/ ( ph \/ ps ) ) ) $=
    ( wn wo orc imori a1i ) ADABEZECAIABFGH $.

  $( A Tseitin axiom for logical disjunction, in deduction form.  (Contributed
     by Giovanni Mascellani, 25-Mar-2018.) $)
  tsor3 $p |- ( th -> ( -. ps \/ ( ph \/ ps ) ) ) $=
    ( wn wo olc imori a1i ) BDABEZECBIBAFGH $.

  $( A Tseitin axiom for triple logical conjunction, in deduction form.
     (Contributed by Giovanni Mascellani, 25-Mar-2018.) $)
  ts3an1 $p |- ( th ->
       ( ( -. ( ph /\ ps ) \/ -. ch ) \/ ( ph /\ ps /\ ch ) ) ) $=
    ( wa wn wo w3a tsan1 df-3an orbi2i sylibr ) DABEZFCFGZMCEZGNABCHZGMCDIPONAB
    CJKL $.

  $( A Tseitin axiom for triple logical conjunction, in deduction form.
     (Contributed by Giovanni Mascellani, 25-Mar-2018.) $)
  ts3an2 $p |- ( th -> ( ( ph /\ ps ) \/ -. ( ph /\ ps /\ ch ) ) ) $=
    ( wa wn wo w3a tsan2 df-3an notbii orbi2i sylibr ) DABEZNCEZFZGNABCHZFZGNCD
    IRPNQOABCJKLM $.

  $( A Tseitin axiom for triple logical conjunction, in deduction form.
     (Contributed by Giovanni Mascellani, 25-Mar-2018.) $)
  ts3an3 $p |- ( th -> ( ch \/ -. ( ph /\ ps /\ ch ) ) ) $=
    ( wa wn wo w3a tsan3 df-3an notbii orbi2i sylibr ) DCABEZCEZFZGCABCHZFZGNCD
    IRPCQOABCJKLM $.

  $( A Tseitin axiom for triple logical disjunction, in deduction form.
     (Contributed by Giovanni Mascellani, 25-Mar-2018.) $)
  ts3or1 $p |- ( th -> ( ( ( ph \/ ps ) \/ ch ) \/ -. ( ph \/ ps \/ ch ) ) ) $=
    ( wo wn w3o exmidd df-3or notbii orbi2i sylibr ) DABECEZMFZEMABCGZFZEDMHPNM
    OMABCIJKL $.

  $( A Tseitin axiom for triple logical disjunction, in deduction form.
     (Contributed by Giovanni Mascellani, 25-Mar-2018.) $)
  ts3or2 $p |- ( th -> ( -. ( ph \/ ps ) \/ ( ph \/ ps \/ ch ) ) ) $=
    ( wo wn w3o tsor2 df-3or orbi2i sylibr ) DABEZFZLCEZEMABCGZELCDHONMABCIJK
    $.

  $( A Tseitin axiom for triple logical disjunction, in deduction form.
     (Contributed by Giovanni Mascellani, 25-Mar-2018.) $)
  ts3or3 $p |- ( th -> ( -. ch \/ ( ph \/ ps \/ ch ) ) ) $=
    ( wn wo w3o tsor3 df-3or orbi2i sylibr ) DCEZABFZCFZFLABCGZFMCDHONLABCIJK
    $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Equality deductions
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  A collection of theorems for commuting equalities (or
  biconditionals) with other constructs.

$)

  ${
    iuneq2f.1 $e |- F/_ x A $.
    iuneq2f.2 $e |- F/_ x B $.
    $( Equality deduction for indexed union.  (Contributed by Giovanni
       Mascellani, 9-Apr-2018.) $)
    iuneq2f $p |- ( A = B -> U_ x e. A C = U_ x e. B C ) $=
      ( wceq nfeq id eqidd iuneq12df ) BCGZABCDDABCEFHEFLILDJK $.
  $}

  ${
    rabeq12f.1 $e |- F/_ x A $.
    rabeq12f.2 $e |- F/_ x B $.
    $( Equality deduction for restricted class abstraction.  (Contributed by
       Giovanni Mascellani, 10-Apr-2018.) $)
    rabeq12f $p |- ( ( A = B /\ A. x e. A ( ph <-> ps ) ) ->
         { x e. A | ph } = { x e. B | ps } ) $=
      ( wb wral wceq crab rabbi biimpi rabeqf sylan9eqr ) ABHCDIZDEJACDKZBCDKZB
      CEKPQRJABCDLMBCDEFGNO $.
  $}

  $( Equality deduction for substitution in class.  (Contributed by Giovanni
     Mascellani, 10-Apr-2018.) $)
  csbeq12 $p |- ( ( A = B /\ A. x C = D ) ->
       [_ A / x ]_ C = [_ B / x ]_ D ) $=
    ( wceq wal csb csbeq2 csbeq1 sylan9eqr ) DEFAGBCFABDHABEHACEHABDEIABCEJK $.

  $( Equality deduction for substitution.  (Contributed by Giovanni Mascellani,
     10-Apr-2018.) $)
  sbeqi $p |- ( ( x = y /\ A. z ( ph <-> ps ) ) ->
       ( [ x / z ] ph <-> [ y / z ] ps ) ) $=
    ( wb wal wsb cv wceq spsbbi sbequ sylan9bbr ) ABFEGAECHBECHCIDIJBEDHABECKBC
    DELM $.

  ${
    ralbi12f.1 $e |- F/_ x A $.
    ralbi12f.2 $e |- F/_ x B $.
    $( Equality deduction for restricted universal quantification.
       (Contributed by Giovanni Mascellani, 10-Apr-2018.) $)
    ralbi12f $p |- ( ( A = B /\ A. x e. A ( ph <-> ps ) ) ->
         ( A. x e. A ph <-> A. x e. B ps ) ) $=
      ( wb wral wceq ralbi raleqf sylan9bbr ) ABHCDIACDIBCDIDEJBCEIABCDKBCDEFGL
      M $.
  $}

  $( Equality deduction for class abstraction of nested ordered pairs.
     (Contributed by Giovanni Mascellani, 10-Apr-2018.) $)
  oprabbi $p |- ( A. x A. y A. z ( ph <-> ps ) ->
       { <. <. x , y >. , z >. | ph } = { <. <. x , y >. , z >. | ps } ) $=
    ( coprab wceq wb wal eqoprab2b biimpri ) ACDEFBCDEFGABHEIDICIABCDEJK $.

  ${
    $d x y $.  $d x z $.  $d y z $.  $d z A $.  $d z B $.  $d z C $.  $d z D $.
    $d z E $.  $d z F $.
    mpobi123f.1 $e |- F/_ x A $.
    mpobi123f.2 $e |- F/_ x B $.
    mpobi123f.3 $e |- F/_ y A $.
    mpobi123f.4 $e |- F/_ y B $.
    mpobi123f.5 $e |- F/_ y C $.
    mpobi123f.6 $e |- F/_ y D $.
    mpobi123f.7 $e |- F/_ x C $.
    mpobi123f.8 $e |- F/_ x D $.
    $( Equality deduction for maps-to notations with two arguments.
       (Contributed by Giovanni Mascellani, 10-Apr-2018.) $)
    mpobi123f $p |- ( ( ( A = B /\ C = D ) /\ A. x e. A A. y e. C E = F )
         -> ( x e. A , y e. C |-> E ) = ( x e. B , y e. D |-> F ) ) $=
      ( vz wal wo a1d wceq wa wral cv wcel coprab cmpo wb wi eleq2 alrimi nfcri
      nfeq nfbi ax-5 sylg alimi nfal nf5ri 3syl id alanimi syl2an eqeq2 alrimiv
      2ralimi hbra1 alrimih 19.21v albii sylibr ralimi 2albii 19.21 sylbbr 4syl
      rsp wfal tsan2 ord cnf1dd tsbi2 a1dd ax-1 contrd idd tsim2 cnfn2dd cnf2dd
      wn tsbi3 tsan3 mpdd notnotr sylibrd jcad tsim3 tsbi1 tsan1 cnfn1dd or32dd
      a1i sylibd tsbi4 tsim1 efald2 2alimi oprabbi df-mpo 3eqtr4g ) CDUAZEFUAZU
      BZGHUAZBEUCACUCZUBZAUDZCUEZBUDZEUEZUBZQUDZGUAZUBZABQUFZXQDUEZXSFUEZUBZYBH
      UAZUBZABQUFZABCEGUGABDFHUGXPXRYFUHZXTYGUHZUBZXRXTYCYIUHZUIZUIZUBZQRZBRZAR
      ZYDYJUHZQRZBRARYEYKUAXMYNQRZBRZARZYQQRZBRZARZUUAXOXKYLQRZBRZARYMQRZBRZARZ
      UUFXLXKYLUUKAXKYLAACDIJUMCDXQUJUKYLUUJBXRYFBBACKULZBADLULUNYLQUOUKUPXLYMB
      RUUMUUNXLYMBBEFMNUMEFXSUJUKYMUULBYMQUOUQUUMAUULABYMAQXTYGAABEOULABFPULUNU
      RURUSUTUUKUUMUUEAUUJUULUUDBYLYMYNQYNVAVBVBVBVCXOYOQRZBEUCZACUCYPQRZBRZACU
      CZXRUUSUIZARZUUIXNUUPABCEXNYOQGHYBVDVEVFUUQUUSACUUQXTUUPUIZBRUUSUUQUVCBUU
      PBEVGUUPBEVQVHUURUVCBXTYOQVIVJVKVLUUTUVAAUUSACVGUUSACVQVHUUIXRUURUIZBRZAR
      UVBUUGUVDABXRYPQVIVMUVEUVAAXRUURBUUOVNVJVOVPUUEUUHYTAUUDUUGYSBYNYQYRQYRVA
      VBVBVBVCYSUUCABYRUUBQYRUUBUIZUVFWJZVRYPUVGVRWJZXRYPUVGXRUVHUVGXRYJUVGXRWJ
      ZYDYJUVGUVIYAYDWJZUVGXRYAWJZXRXTUVGVSVTUVGYAUVJSZUVIYAYCUVGVSZTWAUVGYDYJS
      ZUVIUVGUVNUVFUVGUVNWJZUUBYRUVGUVNUUBYDYJUVGWBZVTWCUVGUVOWDWETWAUVGUVIYHYJ
      WJZUVGUVIYFYHWJZUVGUVIXRYFWJZUVGUVIWFUVGUVIXRUVSSZYLUVGYLUVIUVGYLUVFUVGYL
      WJZYRUVFUVGUWAYNYRWJZUVGYLYNWJZYLYMUVGVSVTUVGYNUWBSZUWAYNYQUVGVSZTWAUVGYR
      UVFSZUWAYRUUBUVGWGZTWAUVGUWAWDWEZTUVGUVTUWASUVIXRYFUVGWKTWHWAUVGYFUVRSUVI
      YFYGUVGVSTWAUVGYHUVQSZUVIYHYIUVGVSZTWAWEZTZUVGUVHYQYRUVGUVHYRUVFUVGUVHWDZ
      UVGUWFUVHUWGTWIUVGYQUWBSZUVHYNYQUVGWLZTWHWMUVGUVHXTYPWJZUVGUVHXTYAUVGUVHY
      AYDUVGUVHYDYJUVGUVQUVHUVGUVQYOUVGUVQWJZXTYOUVGUWQYGXTUVGUWQYGYHUVGUWQYHYJ
      UWQYJUIUVGYJWNXBZUVGUWIUWQUWJTWHUVGYGUVRSUWQYFYGUVGWLTWHUVGYMUVFUVGYMWJZY
      RUVFUVGUWSYNUWBUVGYMUWCYLYMUVGWLVTUVGUWDUWSUWETWAUVGUWFUWSUWGTWAUVGUWSWDW
      EZWOZUVGUWQXRYPUVGXRUWQUWKTZUVGUWQYQYRUVGUWQYRUVFUVGUWQWDZUVGUWFUWQUWGTWI
      UVGUWNUWQUWOTWHWMWMUVGUWQYCYOWJZUVGUWQYAYCWJZUVGUWQXRXTUXBUXAWPUVGUWQUVKU
      XESZYDUVGUWQUVJYJUWRUVGUWQUVJUVQSZUUBUVGUWQUUBWJZUVFUXCUVGUXHUVFSZUWQYRUU
      BUVGWQZTWIUVGUXGUUBSUWQYDYJUVGWRTWIWHUVGUXFYDSUWQYAYCUVGWSTWIWTUVGUWQYCUX
      DSYIUVGUWQYIYJUWRUVGYIUVQSUWQYHYIUVGWLTWHUVGUWQYCYIWJZUXDUVGYCUXKSUXDSUWQ
      YCYIUVGWKTXAWHWAWETZUVGUVHUVNUUBUVGUVHUXHUVFUWMUVGUXIUVHUXJTWIUVGUVNUUBSU
      VHUVPTWIWIZUVGUVLUVHUVMTWHUVGXTUVKSUVHXRXTUVGWLTWHZUVGUVHXTWJZUWPSYOUVGUV
      HYCUXDUVGUVHYCYDUXMUVGYCUVJSUVHYAYCUVGWLTWHUVGUVHUXEUXDSYIUVGUVHYHUXKUVGU
      VHYFYGUVGUVHXRYFUWLUWHXCUVGUVHXTYGUXNUWTXCWPUVGUVHUVRUXKSZYJUXLUVGUXPYJSU
      VHYHYIUVGWSTWIWTUVGUVHUXEYIUXDUVGUXEYISUXDSUVHYCYIUVGXDTXAWIWTUVGUVHUXOYO
      UWPUVGUXOYOSUWPSUVHXTYOUVGXETXAWIWTWEXFUQXGYDYJABQXHUTABQCEGXIABQDFHXIXJ
      $.
  $}

  ${
    iuneq12f.1 $e |- F/_ x A $.
    iuneq12f.2 $e |- F/_ x B $.
    $( Equality deduction for indexed unions.  (Contributed by Giovanni
       Mascellani, 10-Apr-2018.) $)
    iuneq12f $p |- ( ( A = B /\ A. x e. A C = D )
         -> U_ x e. A C = U_ x e. B D ) $=
      ( wceq wral ciun iuneq2 iuneq2f sylan9eqr ) DEHABIBCHABDJABEJACEJABDEKABC
      EFGLM $.
  $}

  ${
    $d x y $.  $d y A $.  $d y B $.  $d y C $.  $d y D $.
    iineq12f.1 $e |- F/_ x A $.
    iineq12f.2 $e |- F/_ x B $.
    $( Equality deduction for indexed intersections.  (Contributed by Giovanni
       Mascellani, 10-Apr-2018.) $)
    iineq12f $p |- ( ( A = B /\ A. x e. A C = D ) ->
         |^|_ x e. A C = |^|_ x e. B D ) $=
      ( vy wceq wral wa cv wcel cab ciin wb eleq2 ralimi ralbi df-iin sylan9bbr
      syl raleqf abbidv 3eqtr4g ) BCIZDEIZABJZKZHLZDMZABJZHNUJEMZACJZHNABDOACEO
      UIULUNHUHULUMABJZUFUNUHUKUMPZABJULUOPUGUPABDEUJQRUKUMABSUBUMABCFGUCUAUDAH
      BDTAHCETUE $.
  $}

  $( Equality deduction for class abstraction of ordered pairs.  (Contributed
     by Giovanni Mascellani, 10-Apr-2018.) $)
  opabbi $p |- ( A. x A. y ( ph <-> ps ) ->
       { <. x , y >. | ph } = { <. x , y >. | ps } ) $=
    ( copab wceq wb wal eqopab2b biimpri ) ACDEBCDEFABGDHCHABCDIJ $.

  ${
    $d x y $.  $d y A $.  $d y B $.  $d y D $.  $d y E $.
    mptbi12f.1 $e |- F/_ x A $.
    mptbi12f.2 $e |- F/_ x B $.
    $( Equality deduction for maps-to notations.  (Contributed by Giovanni
       Mascellani, 10-Apr-2018.) $)
    mptbi12f $p |- ( ( A = B /\ A. x e. A D = E ) ->
         ( x e. A |-> D ) = ( x e. B |-> E ) ) $=
      ( vy wceq wa wb wal wi wn ord wo contrd a1d cnfn2dd cnf2dd wral wcel cmpt
      copab nfeq eleq2 alrimi ax-5 sylg eqeq2 alrimiv ralimi df-ral sylib albii
      cv 19.21v sylibr alanimi syl2an wfal tsan2 tsbi2 a1dd ax-1 cnf1dd simplim
      tsbi3 tsan3 mpdd notnotr a1i jcad tsim3 tsbi1 tsbi4 cnfn1dd or32dd efald2
      id tsan1 2alimi syl eqopab2bw df-mpt 3eqtr4g ) BCIZDEIZABUAZJZAUPZBUBZHUP
      ZDIZJZAHUDZWKCUBZWMEIZJZAHUDZABDUCACEUCWJWOWSKZHLALZWPWTIWJWLWQKZWLWNWRKZ
      MZJZHLZALZXBWGXCHLZALXEHLZALZXHWIWGXCXIAWGXCAABCFGUEBCWKUFUGXCHUHUIWIWLXD
      HLZMZALZXKWIXLABUAXNWHXLABWHXDHDEWMUJUKULXLABUMUNXJXMAWLXDHUQUOURXIXJXGAX
      CXEXFHXFVTUSUSUTXFXAAHXFXAMZXONZVAXDXPVANZWLXDXPWLXQXPWLWSXPWLNZWOWSXPWLW
      ONZWLWNXPVBOXPWOWSPZXRXPXTXOXPXTNZXAXFXPXTXAWOWSXPVCOVDXPYAVEQZRVFXPXRWQW
      SNZXPWLWQNZXPWLYDPZXFXPXFYENZXFXAVGZRXPYFXCXFNZXPYEXCNZWLWQXPVHOXPXCYHPZY
      FXCXEXPVBZRVFQZOXPWQYCPZXRWQWRXPVBZRVFQRZXPXQXEXFXPXFXQYGRZXPXEYHPZXQXCXE
      XPVIZRSVJXPXQWNXDNZXPXQWNWOXPXQWOWSXPYCXQXPYCWOXPYCNZWLWNXPYTWLWQXPYTWQWS
      YTWSMXPWSVKVLZXPYMYTYNRSXPYEYTYLRSZXPYTWNWRXPYTWRWSUUAXPWRYCPYTWQWRXPVIRS
      XPYTWNWRNZPZXDXPYTWLXDUUBXPYTXEXFXPXFYTYGRXPYQYTYRRSVJXPUUDYSPYTWNWRXPVHR
      SSVMXPYTXSWSUUAXPYTXSYCPZXAXPYTXANZXOXPYTVEXPUUFXOPYTXFXAXPVNRTXPUUEXAPYT
      WOWSXPVORTSQRZXPXTXQYBRTXPWNXSPXQWLWNXPVIRSXPXQWNNZYSPWRXPXQWQUUCXPXQWLWQ
      YOXPXQXRWQPZXCXPXQXCXFYPXPYJXQYKRSXPUUIYIPXQWLWQXPVPRSVQXPXQYDUUCPZWSUUGX
      PUUJWSPXQWQWRXPWARTVQXPXQUUHWRYSXPUUHWRPYSPXQWNWRXPVPRVRTVQQVSWBWCWOWSAHW
      DURAHBDWEAHCEWEWF $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Miscellanea
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  Work in progress or things that do not belong anywhere else.

$)

  ${
    orcomdd.1 $e |- ( ph -> ( ps -> ( ch \/ th ) ) ) $.
    $( Commutativity of logic disjunction, in double deduction form.  Should
       not be moved to main, see PR #3034 in Github.  Use ~ orcomd instead.
       (Contributed by Giovanni Mascellani, 19-Mar-2018.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    orcomdd $p |- ( ph -> ( ps -> ( th \/ ch ) ) ) $=
      ( wo pm1.4 syl6 ) ABCDFDCFECDGH $.
  $}

  ${
    $( $d x y $.  $d x z $. $)
    $( Substituting ` y ` for ` x ` and then ` z ` for ` y ` is equivalent to
       substituting ` z ` for both ` x ` and ` y ` .  (Contributed by Giovanni
       Mascellani, 8-Apr-2018.)  Obsolete version of ~ sbcom3 as of
       16-Sep-2018.  (New usage is discouraged.)
       (Proof modification is discouraged.)  Note: this proof requires many
       hours to "MM> PROVE sbcom3OLD" and "MM-PA> MINIMIZE__WITH *" and
       "MM-PA> SAVE NEW_PROOF".  The discouragements will prevent accidental
       minimization attempts and other operations that would interfere with
       scripts.  For the time being, we are keeping this proof as a test case,
       but it will be deleted eventually. -NM $)
    $(
    [Commented out by NM 28-Aug-2019 to avoid slowdown in proof format
    conversions.  Uncomment it if needed for testing.]
    sbcom3OLD $p |- ( [ z / y ] [ y / x ] ph <-> [ z / x ] [ z / y ] ph ) $=
      ( wi wa wn id a1i wo a1d orcomdd cnf2dd or32dd tsim3 cnfn2dd contrd tsan3
      tsan1 tsim2 wsb cv wceq wex wb equtr impcom equtr2 eqcomd imbi2d pm5.74rd
      eqeq2 pm5.32rd exbidv pm5.74i imbi1d pm5.32i wfal tsan2 tsbi2 tsbi3 tsbi4
      exmidd tsbi1 efald2 ax-mp exbii orsild orsird notnotrd tsim1 dfsb imbi2i
      anbi2i anbi12i bitri bicomi bitr4i 3bitr4i sbcom ) ABCUAZCDUAZABDUAZCDUAZ
      ACDUABDUACUBZDUBZUCZBUBZWEUCZAEZWIAFZBUDZFZEZWGWMFZCUDZFZWGWHWFUCZAEZWRAF
      ZBUDZFZEZWGXBFZCUDZFZWBWDWGWIFZWREZWQXFUEZWIWGWRBCDUFUGWGWRFZWIEZXHXIEZXJ
      WEWHCBDUHUIWGWLEZWGXAEZUEZXKXLEZWGWLXAWGWKWTBWGAWIWRWGAWIWRWGWIWRAWEWFWHU
      LZUJUKUMUNZUOWPXEUEZXOXPEZWOXDCWGWJFZWGWSFZUEZWOXDUEZWGWJWSWGWIWRAXQUPUQW
      GWLFZWGXAFZUEZYCYDEZWGWLXAXRUQYGYHEZYIGZURXBYJURGZXBWSYJYKWSYBYJYKYBYAYJY
      KYAWGYJWGYKYJWGYHYJWGGZYHYDYJYLYDWOYJYLWOGZWGYLYLEYJYLHIZYJYLWGYMYJWGYMJY
      LWGWMYJUSKLMYJYLWOYDYJYLWOYDJXDYJYLXDGZWGYNYJYLWGYOYJWGYOJYLWGXBYJUSKLMYJ
      YLWOXDYDYJWOXDJZYDJZYLWOXDYJUTZKNMLMYJYLYDGZYHYJYSYHJZYLYCYDYJOZKLPYJYLYH
      GZYIYJYLYJYJYJYJYLYJHZKYJYJYJGJZYLYJYJVCZKPYJUUBYIJZYLYGYHYJOZKMQZKZYJYKY
      LYAYJYKYLYAJWJYJYKWJWMYJYKWMWOYJWOYKYJWOWMYJYMWMWJYJYMWJYAYJYMYAYBYJYMYBW
      GYJWGYMUUHKZYJYMYLYBYJYMYLYBJWSYJYMWSXBYJYMXBXDYJYMXDWOYMYMEYJYMHIZYJYMWO
      XDYJYMYPYDYJYMYSYHYJYMUUBYIYJYMYJYJYJYJYMUUCKZYJUUDYMUUEKPYJUUFYMUUGKMZYJ
      YTYMUUAKMYJYQYMYRKMLMYJXBYOJYMWGXBYJRKPZYJWSXBGZJZYMWSXAYJUSKPYJYMYLWSGZY
      BYJYLUUQJYBJYMWGWSYJSKNPLPYJYMYAYBGZJZYCYJYMYCYHUUMYJYCYHJZYMYCYDYJTZKMYJ
      UUSYCGZJYMYAYBYJVAKPPYJWJYAGZJYMWGWJYJRKPYJYMWJGZWMYJYMUVDWMJWLYJYMWLYEYJ
      YMYEYFYJYMYFWGUUJYJYMYLYFYJYMYLYFJXAYJYMXAXBUUNYJXAUUOJZYMWSXAYJRKPYJYMYL
      XAGZYFYJYLUVFJYFJYMWGXAYJSKNPLPYJYMYEYFGZJZYGYJYMYGYIUULYJYGYIJZYMYGYHYJT
      ZKMYJUVHYGGZJYMYEYFYJVAKPPYJWLYEGZJYMWGWLYJRKPYJYMUVDWLGZWMYJUVDUVMJZWMJZ
      YMWJWLYJSKNPLPYJYMWMGZWGUUJYJYMYLUVPYJYMYLUVPJZWOUUKYJUVQWOJYMWGWMYJSKMLP
      QKZYJWMYMJYKWGWMYJRKPZYJWJUVPJZYKWJWLYJUSKPYJYKYLUVDYAYJYLUVDJYAJYKWGWJYJ
      SKNPLPYJYKUVCYBYJYKUVCYBJZYCYJYKYCYHYJYKUUBYIYJYKYJYJYJYJYKUUCKZYJUUDYKUU
      EKPYJUUFYKUUGKMZYJUUTYKUVAKMYJUWAUVBJYKYAYBYJVBKPLPYJWSUURJYKWGWSYJRKPYJY
      KUUQXBYJYKUUQXBJXAYJYKXAYFYJYKYFYEYJYKYEWGUUIYJYKYLYEYJYKYLYEJWLYJYKWLWMU
      VSYJWLUVPJZYKWJWLYJRKPYJYKYLUVMYEYJYLUVMJYEJYKWGWLYJSKNPLPYJYKUVLYFYJYKUV
      LYFJZYGYJYKYGYIUWBYJUVIYKUVJKMYJUWEUVKJYKYEYFYJVBKPLPYJXAUVGJYKWGXAYJRKPY
      JYKUUQUVFXBYJUUQUVFJZXBJZYKWSXAYJSKNPLPYJYKUUOWGUUIYJYKYLUUOYJYKYLUUOJZXD
      YJYKYOWOUVRYJYKYMYOYJYKYMYOJZYDYJYKYSYHUWCYJYTYKUUAKMYJUWIYDJYKWOXDYJVDKM
      LPYJUWHXDJYKWGXBYJSKMLPQVEVFVFVGXSXTEZUWJGZURXHUWKXHYKUWKXHXTUWKXHGZXTXPU
      WKUWLXPXLUWKUWLXLXHUWLUWLEUWKUWLHIUWKUWLXHXLUWKXHXLJUWLXHXIUWKTKLMUWKUWLX
      LGZXPUWKUWMXPJZUWLXKXLUWKOZKLPUWKUWLXPGZXTUWKUWPXTJZUWLXOXPUWKOZKLPUWKUWL
      XTGZUWJUWKUWLUWKUWKUWKUWKUWLUWKHZKUWKUWKUWKGZJZUWLUWKUWKVCZKPUWKUWSUWJJZU
      WLXSXTUWKOZKMQKUWKYKUWLXGUWKYKXGWGUWKYKWGWNUWKYKWNGZWPUWKYKWPXEUWKXEYKUWK
      XEWQUWKXEGZWQXFUWKUXGXFGZXEUXGUXGEUWKUXGHIZUWKUXGXEUXHUWKXEUXHJUXGXCXEUWK
      RKLMUWKWQXFJZUXGUWKUXJXTUWKUXJGZXTXPUWKUXKXPXLUWKUXKXLXIUWKUXKXIWQUXKWQGZ
      EUWKUXKWQXFUXKHZVHIUWKUXKWQXIUWKUXKWQXIJXFUXKUXHEUWKUXKWQXFUXMVIIUWKUXKWQ
      XFXIUWKUXJXIJUXKWQXFUWKUTKNMLMUWKUXKXIGZXLUWKUXNXLJZUXKXHXIUWKOZKLPUWKUXK
      UWMXPUWKUWNUXKUWOKLPUWKUXKUWPXTUWKUWQUXKUWRKLPUWKUXKUWSUWJUWKUXKUWKUWKUWK
      UWKUXKUWTKUWKUXBUXKUXCKPUWKUXDUXKUXEKMQZKMUWKUXGUXLWPUWKUXGWPGZXEUXIUWKUX
      GUXRXEJZXSUWKXSUXGUWKXSUWKUWKUWKXSGZUWTKUWKUXTUXAUWJUWKUXTUWJXSUXTUXTEUWK
      UXTHIUWKUXTXSUWJUWKXSUWJJUXTXSXTUWKTKLMUWKUXTUWKUXAUWKUXBUXTUXCKLPQZKUWKU
      XSUXTJUXGWPXEUWKVBKPMUWKUXGWPUXLUWKWPUXLJUXGWNWPUWKRKLMQZKUWKYKWPUXGJZXSU
      WKXSYKUYAKUWKUYCUXTJYKWPXEUWKVAKPPUWKYKUXFUXRJZWQUWKUXLYKUWKUXLWJUWKUXLGZ
      WJWMUWKUYEWMWGUWKUYEWGXCUWKUYEXCGZXEUWKXEUYEUYBKUWKUYEUYFUXGJZXFUWKUYEUXH
      WQUYEWQEUWKUYEWQUYEHVJIZUWKUYEUXLUXHUWKUYEUXLUXHJZXIUWKUYEUXNXLUWKUYEUWMX
      PUWKUYEUWPXTUWKUYEUWSUWJUWKUYEUWKUWKUWKUWKUYEUWTKUWKUXBUYEUXCKPUWKUXDUYEU
      XEKMUWKUWQUYEUWRKMUWKUWNUYEUWOKMUWKUXOUYEUXPKMUWKUYIXIJUYEWQXFUWKVDKMLPUW
      KUYGXFJUYEXCXEUWKSKMPZUWKWGXCJUYEWGXBUWKTKMZUWKUYEYLWMUWKUYEYLWMJZWNUWKUY
      EWNWQUYHUWKWNUXLJUYEWNWPUWKUSKPUWKUYLUXFJUYEWGWMUWKVKKPLPZUWKUVTUYEWJWLUW
      KUSKPUWKUYEUVDWIUWKUYEWIXJUWKUYEXJWGUYKUWKUYEYLXJUWKUYEYLXJJWRUWKUYEWRWSU
      WKUYEUUQXAUWKUYEXAWGUYKUWKUYEYLXAUWKUYEYLXAJZXNUWKUYEXNXMUWKUYEXMWLUWKUYE
      WLWMUYMUWKUWDUYEWJWLUWKRKPUWKUYEUVMXMUWKUVMXMJUYEWGWLUWKOKLPUWKUYEXMGZXNU
      WKUYEUYOXNJZXOUWKXOUYEUWKXOUWJUWKXOGZUWJXTUWKUYQXTXOUYQUYQEUWKUYQHIUWKUYQ
      XOXTUWKXOXTJUYQXOXPUWKTKLMUWKUYQUWSUWJUWKUXDUYQUXEKLPUWKUYQUWKUWKUWKUWKUY
      QUWTKUWKUXBUYQUXCKPQZKUWKUYPUYQJUYEXMXNUWKVBKPLPUWKUYNXNGZJUYEWGXAUWKVKKP
      LPUWKUYEUWFXBUWKUYEUUOXCUYJUWKUUOXCJUYEWGXBUWKOKMUWKUWGUYEWSXAUWKSKMPZUWK
      WRWSJUYEWRAUWKTKMUWKUYEYLWRGZXJUWKYLVUAJXJJUYEWGWRUWKSKNPLPUWKUYEXJGZWIUW
      KUYEVUBWIJZXKUWKXKUYEUWKXKUWJUWKXKGZUWJXTUWKVUDXTXPUWKVUDXPXKVUDVUDEUWKVU
      DHIUWKVUDXKXPUWKXKXPJVUDXKXLUWKTKLMUWKVUDUWPXTUWKUWQVUDUWRKLPUWKVUDUWSUWJ
      UWKUXDVUDUXEKLPUWKVUDUWKUWKUWKUWKVUDUWTKUWKUXBVUDUXCKPQKUWKVUCVUDJUYEXJWI
      UWKVKKPLPUWKUYEWIGZUVDUWKUYEVUEUVDJAUWKUYEAGZWSUYTUWKVUFWSJUYEWRAUWKOKMUW
      KUYEVUEAUVDUWKVUEAJUVDJUYEWIAUWKVKKNMLPQKZUWKUYDWQJYKWNWPUWKSKMPZUWKWGWNJ
      YKWGWMUWKTKMZUWKYKYLXGUWKYKYLXGJWIUWKYKWIWJUWKYKUVDWLUWKYKWLWGVUIUWKYKYLW
      LUWKYKYLWLJZXMUWKYKXMXNUWKYKXNXAUWKYKXAXBUWKYKXBWGVUIUWKYKYLXBUWKYKYLXBJZ
      XCUWKYKXCXFUWKYKXFWQVUGUWKYKWQXFUWKUXJYKUXQKLMUWKXCUXHJYKXCXEUWKUSKPUWKVU
      KUYFJYKWGXBUWKVKKPLPZUWKUVEYKWSXAUWKRKPUWKYKUVFXNUWKUVFXNJYKWGXAUWKOKLPUW
      KYKXMUYSJZXOUWKXOYKUYRKUWKVUMUYQJYKXMXNUWKVAKPPUWKVUJUYOJYKWGWLUWKVKKPLPU
      WKYKUVNWMUWKYKUVPWNVUHUWKUVPWNJYKWGWMUWKOKMUWKUVOYKWJWLUWKSKMPZUWKWIWJJYK
      WIAUWKTKMUWKYKYLVUEXGUWKYLVUEJXGJYKWGWIUWKSKNPLPUWKYKXGGZUWLUWKYKVUOUWLJW
      RUWKYKVUAAUWKYKVUFWJVUNUWKVUFWJJYKWIAUWKOKMUWKYKVUAAJZWSUWKYKWSXBVULUWKUU
      PYKWSXAUWKUSKPUWKVUPUUQJYKWRAUWKVKKPMUWKYKVUOWRUWLUWKVUOWRJUWLJYKXGWRUWKV
      KKNMLPQVEVFVFVFVFWBWGWAEZWGWAFZCUDZFWQWACDVLVUQWNVUSWPWAWMWGABCVLZVMVURWO
      CWAWMWGVUTVNVGVOVPWDWGWCEZWGWCFZCUDZFXFWCCDVLXCVVAXEVVCXBWCWGWCXBABDVLZVQ
      VMVVCXEVVBXDCWCXBWGVVDVNVGVQVOVRVSACDBVTVR $.
    $)
  $}

  ${
    $d x y $.  $d x z $.  $d x w $.  $d y z $.  $d z w $.  $d z A $.  $d w A $.
    scottexf.1 $e |- F/_ y A $.
    scottexf.2 $e |- F/_ x A $.
    $( A version of ~ scottex with nonfree variables instead of distinct
       variables.  (Contributed by Giovanni Mascellani, 19-Aug-2018.) $)
    scottexf $p |- { x e. A | A. y e. A ( rank ` x ) C_ ( rank ` y ) } e. _V $=
      ( vw vz cv crnk cfv wss wral crab cvv nfcv nfv weq fveq2 sseq2d cbvralfw
      rabbii nfralw sseq1d ralbidv cbvrabw df-scott scottex eqeltrri eqeltri
      eqtr4i cscott ) AHZIJZBHZIJZKZBCLZACMZFHZIJZGHZIJZKZGCLZFCMZNURUMVBKZGCLZ
      ACMVEUQVGACUPVFBGCDGCOUPGPVFBPBGQUOVBUMUNVAIRSTUAVDVGFACFCOEVCAGCEVCAPUBV
      GFPFAQZVCVFGCVHUTUMVBUSULIRUCUDUEUJCUKVENFGCUFCUGUHUI $.
  $}

  ${
    $d x y $.  $d x z $.  $d x w $.  $d y z $.  $d z w $.  $d z A $.  $d w A $.
    scott0f.1 $e |- F/_ y A $.
    scott0f.2 $e |- F/_ x A $.
    $( A version of ~ scott0b with nonfree variables instead of distinct
       variables.  (Contributed by Giovanni Mascellani, 19-Aug-2018.) $)
    scott0f $p |- ( A = (/) <-> { x e. A | A. y e. A ( rank ` x )
         C_ ( rank ` y ) } = (/) ) $=
      ( vw vz cscott c0 wceq cv crnk cfv wss wral crab eqeq1i nfcv nfv fveq2
      df-scott scott0b sseq2d cbvralfw rabbii nfralw ralbidv cbvrabw 3bitr4i
      sseq1d eqtr4i ) CHZIJFKZLMZGKZLMZNZGCOZFCPZIJCIJAKZLMZBKZLMZNZBCOZACPZIJU
      LUSIFGCUAQCUBVFUSIVFVAUPNZGCOZACPUSVEVHACVDVGBGCDGCRVDGSVGBSVBUOJVCUPVAVB
      UOLTUCUDUEURVHFACFCREUQAGCEUQASUFVHFSUMUTJZUQVGGCVIUNVAUPUMUTLTUJUGUHUKQU
      I $.
  $}

  ${
    $d x y $.
    scottn0f.1 $e |- F/_ y A $.
    scottn0f.2 $e |- F/_ x A $.
    $( A version of ~ scott0f with inequalities instead of equalities.
       (Contributed by Giovanni Mascellani, 19-Aug-2018.) $)
    scottn0f $p |- ( A =/= (/) <-> { x e. A | A. y e. A ( rank ` x )
         C_ ( rank ` y ) } =/= (/) ) $=
      ( c0 cv crnk cfv wss wral crab scott0f necon3bii ) CFAGHIBGHIJBCKACLFABCD
      EMN $.
  $}

  ${
    $d ph f $.  $d x y $.  $d x A $.  $d x f $.  $d y f $.  $d A f $.
    ac6s3f.1 $e |- F/ y ps $.
    ac6s3f.2 $e |- A e. _V $.
    ac6s3f.3 $e |- ( y = ( f ` x ) -> ( ph <-> ps ) ) $.
    $( Generalization of the Axiom of Choice to classes, with bound-variable
       hypothesis.  (Contributed by Giovanni Mascellani, 19-Aug-2018.) $)
    ac6s3f $p |- ( A. x e. A E. y ph -> E. f A. x e. A ps ) $=
      ( wex wral cvv wrex cv wf wa rexv ralbii biimpri ac6sf exsimpr 3syl ) ADJ
      ZCEKZADLMZCEKZELFNOZBCEKZPFJUHFJUFUDUEUCCEADQRSABCDELFGHITUGUHFUAUB $.
  $}

  ${
    $d ph f $.  $d x y $.  $d x A $.  $d x f $.  $d y f $.  $d A f $.
    ac6s6.1 $e |- F/ y ps $.
    ac6s6.2 $e |- A e. _V $.
    ac6s6.3 $e |- ( y = ( f ` x ) -> ( ph <-> ps ) ) $.
    $( Generalization of the Axiom of Choice to classes, moving the existence
       condition in the consequent.  (Contributed by Giovanni Mascellani,
       19-Aug-2018.) $)
    ac6s6 $p |- E. f A. x e. A ( E. y ph -> ps ) $=
      ( wi wn wo tsim3 a1d cnf2dd tsim2 cnfn2dd cnfn1dd a1dd wtru wex wcel wral
      cv cab cvv cif hbe1 iftrue eqabrd exbidh ibir vex exgen hbn eleq2d mpbiri
      iffalse pm2.61i rgenw nfe1 nfim cfv wceq wb wfal id ax-1 mpdd tsbi4 tsbi2
      a1i cnf1dd simplim syld tsbi3 tsim1 or32dd contrd tsbi1 efald2 ax-mp mt3d
      ord notornotel2 notornotel1 trud ac6s3f ) DUDZADUAZADUEZUFUGZUBZDUAZCEUCW
      JBJZCEUCFUAWNCEWJWNWJWNWJWMADADUHZWJADWLWJWKUFUIUJZUKULWJKZWNWIUFUBZDUAWS
      DDUMZUNWRWMWSDWJDWPUOWRWLUFWIWJWKUFURUPZUKUQUSUTWMWOCDEFWJBDADVAGVBHWJWIC
      UDFUDVCVDZWMWOVEZJZWJWMAVEZJZWJXDJZWQXBABVEZJZXFXGJZIXIXJJZXKKZVFXCXLVFKZ
      WMXCXLXMWMAXLAXMXLAWOXLAKZWMWOXLXNWMKZAXNXNJXLXNVGVLZXLXNXOALZXEXLXNWJXEX
      LXNWJXGXLXNXGKZXJXLXNXJKZXKXLXNVHXLXSXKLZXNXIXJXLMZNOZXLXRXJLZXNXFXGXLMZN
      OZXLWJXGLZXNWJXDXLPZNOZXLXNXFXJYBXLXFXJLZXNXFXGXLPZNOVIXLXQXEKZLXNWMAXLVJ
      NQOXLXNWMWOLZXCXLXNXCKZXDXLXNXDKZXGYEXLYNXGLZXNWJXDXLMZNOZXLYMXDLZXNXBXCX
      LMZNOXLYLXCLXNWMWOXLVKNOVMXLXNWJWOKZYHXLXNWRYTLBXLXNABKZXPXLXNAUUALZXHXLX
      NXBXHXLXNXBXDYQXLXBXDLZXNXBXCXLPZNOXIXJVNZVOXLUUBXHKZLXNABXLVPNQVMXLXNWRB
      YTXLWRBLYTLXNWJBXLVQNVRORVSNZXLXMWMXNLZXEXLXMWJXEXLXMWJXGXLXMXRXJXLXMXSXK
      XLXMVHXLXTXMYANOZXLYCXMYDNOZXLYFXMYGNOXLXMXFXJUUIXLYIXMYJNOVIXLUUHYKLXMWM
      AXLVPNQQXLXMXOXCLWOXLXMBWJXLXMABUUGXLXMXNBLZXHXLXMXBXHXLXMXBXDXLXMYNXGUUJ
      XLYOXMYPNOZXLUUCXMUUDNOUUEVOXLUUKUUFLXMABXLVJNQRSXLXMXOYTXCXLXOYTLZXCLZXM
      WMWOXLVTNVRQRXLXMYMXDUULXLYRXMYSNOVSWAWBWBWRWMTVEZJZWRXDJZWRWMWSVEZJZUUPX
      AWRWSJZUUSUUPJZWSWRWTVLUUTUVAJZUVBKZVFWSUVCXMWRWSUVCWRXMUVCWRUVBUVCVGZUVC
      WRKZUVAUUTUVCUVEUUPUUSUVCWRUUPWRUUOUVCPWDSSWCNZUUTUVAVNVOUVCXMUURWSKZUVCX
      MWRUURUVFUVCUUSUVBUVDUVCUUSKUVAUUTUVCUUSUVAUUSUUPUVCPWDSWCVOUVCUURKZUVGLZ
      XMUVCUVIUVAUVCUVIKZUUPUUSUVCUVJUUOWRUVCUVJWMUUOUVCUVJWMWSUVJWSJUVCUVJUVHW
      SUVJVGZWEVLUVCUVJWMUVGLZUURUVJUURJUVCUVJUURUVGUVKWFVLUVCUVLUVHLUVJWMWSUVC
      VPNQQUVCUVJXOUUOLTUVCTUVJUVCWGNUVCUVJXOTKZUUOUVCXOUVMLUUOLUVJWMTUVCVTNVRQ
      RSSUVCUVJUVAKZUVBUVCUVJVHUVCUVNUVBLUVJUUTUVAUVCMNOVSNRVSWAWBWBUUPUUQJZUVO
      KZVFUUOUVPXMWRUUOUVPXMWRUUQUVPXMUUQKZUVOUVPXMVHZUVPUVQUVOLXMUUPUUQUVPMNOZ
      UVPWRUUQLZXMWRXDUVPPZNOUVPXMUUPUVOUVRUVPUUPUVOLXMUUPUUQUVPPNOVIUVPXMWMUUO
      KZUVPXMXOWOUVPWOXMUVPWOUVOUVPVGUVPYTUUQUUPUVPYTWJUUQUVPYTWJWOYTYTJUVPYTVG
      VLUVPWJWOLYTWJBUVPPNOUVPUVTYTUWANRSWCNUVPXMUUMXCUVPXMYMXDUVPXMYNUUQUVSUVP
      YNUUQLXMWRXDUVPMNOUVPYRXMXBXCUVPMNOUVPUUNXMWMWOUVPVTNOQUVPXMWMUWBLTUVPTXM
      UVPWGNUVPXMWMUVMUWBUVPWMUVMLUWBLXMWMTUVPVPNVRQVMVSWAWBUSWHWB $.
  $}

  ${
    $d ph z $.  $d ph f $.  $d ps z $.  $d x y $.  $d x z $.  $d x f $.
    $d y z $.  $d y f $.  $d z A $.  $d z f $.  $d A f $.
    ac6s6f.1 $e |- A e. _V $.
    ac6s6f.2 $e |- F/ y ps $.
    ac6s6f.3 $e |- ( y = ( f ` x ) -> ( ph <-> ps ) ) $.
    ac6s6f.4 $e |- F/_ x A $.
    $( Generalization of the Axiom of Choice to classes, moving the existence
       condition in the consequent.  (Contributed by Giovanni Mascellani,
       20-Aug-2018.) $)
    ac6s6f $p |- E. f A. x e. A ( E. y ph -> ps ) $=
      ( vz cv wceq wex wi wral wa isseti vex ac6s6 exdistr raleqf biimpa 2eximi
      exan mpbir nfcv ax5e mp2b ) KLZEMZADNBOZCUJPZQZFNKNZULCEPZFNZKNUQUOUKUMFN
      ZQKNUKURKKEGRABCDUJFHKSITUEUKUMKFUAUFUNUPKFUKUMUPULCUJECUJUGJUBUCUDUQKUHU
      I $.
  $}

$( (End of Giovanni Mascellani's mathbox.) $)
