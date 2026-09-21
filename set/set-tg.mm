$(
###############################################################################
  TG (TARSKI-GROTHENDIECK) SET THEORY
###############################################################################

  Here we introduce Tarski-Grothendieck (TG) set theory, named after
  mathematicians Alfred Tarski and Alexander Grothendieck.  TG theory extends
  ZFC with the TG Axiom ~ ax-groth , which states that for every set ` x `
  there is an inaccessible cardinal ` y ` such that ` y ` is not in ` x ` .
  The addition of this axiom to ZFC set theory provides a framework for
  category theory, thus for all practical purposes giving us a complete
  foundation for "all of mathematics".

  We first introduce the concept of inaccessibles, including weakly and
  strongly inaccessible cardinals ( ~ df-wina and ~ df-ina respectively ),
  Tarski classes ( ~ df-tsk ), and Grothendieck universes ( ~ df-gru ).  We
  then introduce the Tarski's axiom ~ ax-groth and prove various properties
  from that.

$)


$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Inaccessibles
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Weakly and strongly inaccessible cardinals
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c InaccW $. $( Weakly inaccessible $)
  $c Inacc $. $( Strongly inaccessible $)

  $( The class of weak inaccessibles. $)
  cwina $a class InaccW $.

  $( The class of strong inaccessibles. $)
  cina $a class Inacc $.

  ${
    $d x y z $.
    $( An ordinal is weakly inaccessible iff it is a regular limit cardinal.
       Note that our definition allows ` _om ` as a weakly inaccessible
       cardinal.  (Contributed by Mario Carneiro, 22-Jun-2013.) $)
    df-wina $a |- InaccW = { x | ( x =/= (/) /\ ( cf ` x ) = x /\
      A. y e. x E. z e. x y ~< z ) } $.

    $( An ordinal is strongly inaccessible iff it is a regular strong limit
       cardinal, which is to say that it dominates the powersets of every
       smaller ordinal.  (Contributed by Mario Carneiro, 22-Jun-2013.) $)
    df-ina $a |- Inacc = { x | ( x =/= (/) /\ ( cf ` x ) = x /\
      A. y e. x ~P y ~< x ) } $.
  $}

  ${
    $d A x y z $.
    $( Conditions of weak inaccessibility.  (Contributed by Mario Carneiro,
       22-Jun-2013.) $)
    elwina $p |- ( A e. InaccW <-> ( A =/= (/) /\ ( cf ` A ) = A /\
        A. x e. A E. y e. A x ~< y ) ) $=
      ( vz cwina wcel cvv c0 wne ccf cfv wceq csdm wbr wrex wral w3a elex fvex
      cv eleq1 mpbii 3ad2ant2 neeq1 wb fveq2 mpancom rexeq raleqbi1dv 3anbi123d
      eqeq12 df-wina elab2g pm5.21nii ) CEFCGFZCHIZCJKZCLZATBTMNZBCOZACPZQZCERU
      RUPUOVAURUQGFUOCJSUQCGUAUBUCDTZHIZVCJKZVCLZUSBVCOZAVCPZQVBDCEGVCCLZVDUPVF
      URVHVAVCCHUDVEUQLVIVFURUEVCCJUFVEUQVCCUKUGVGUTAVCCUSBVCCUHUIUJDABULUMUN
      $.

    $( Conditions of strong inaccessibility.  (Contributed by Mario Carneiro,
       22-Jun-2013.) $)
    elina $p |- ( A e. Inacc <-> ( A =/= (/) /\ ( cf ` A ) = A /\
      A. x e. A ~P x ~< A ) ) $=
      ( vy cina wcel cvv c0 wne ccf cfv wceq cv cpw csdm wbr wral w3a elex fvex
      eleq1 mpbii 3ad2ant2 neeq1 wb fveq2 eqeq12 mpancom breq2 3anbi123d df-ina
      raleqbi1dv elab2g pm5.21nii ) BDEBFEZBGHZBIJZBKZALMZBNOZABPZQZBDRUQUOUNUT
      UQUPFEUNBISUPBFTUAUBCLZGHZVBIJZVBKZURVBNOZAVBPZQVACBDFVBBKZVCUOVEUQVGUTVB
      BGUCVDUPKVHVEUQUDVBBIUEVDUPVBBUFUGVFUSAVBBVBBURNUHUKUICAUJULUM $.
  $}

  ${
    $d A x y $.
    $( A weakly inaccessible cardinal is an ordinal.  (Contributed by Mario
       Carneiro, 29-May-2014.) $)
    winaon $p |- ( A e. InaccW -> A e. On ) $=
      ( vx vy cwina wcel c0 wne ccf cfv wceq csdm wbr wrex wral w3a con0 elwina
      cv cfon eleq1 mpbii 3ad2ant2 sylbi ) ADEAFGZAHIZAJZBRCRKLCAMBANZOAPEZBCAQ
      UFUDUHUGUFUEPEUHASUEAPTUAUBUC $.

    $( Lemma for ~ inawina .  (Contributed by Mario Carneiro, 8-Jun-2014.) $)
    inawinalem $p |- ( A e. On ->
        ( A. x e. A ~P x ~< A -> A. x e. A E. y e. A x ~< y ) ) $=
      ( con0 wcel cv cpw csdm wbr wrex cen cdom sdomdom ccrd cdm ondomen isnum2
      wa sylib mpd sylan2 ensdomtr ad2ant2l wi sdomel ad2ant2r vex canth2 ensym
      sdomentr sylancr ad2antlr jca expcom reximdv2 ex ralimdv ) CDEZAFZGZCHIZU
      SBFZHIZBCJZACURVAVDURVARZVBUTKIZBDJZVDVAURUTCLIZVGUTCMURVHRUTNOEVGCUTPBUT
      QSUAVEVFVCBDCVBDEZVFRZVEVBCEZVCRVJVERZVKVCVLVBCHIZVKVFVAVMVIURVBUTCUBUCVI
      URVMVKUDVFVAVBCUEUFTVFVCVIVEVFUSUTHIUTVBKIVCUSAUGUHVBUTUIUSUTVBUJUKULUMUN
      UOTUPUQ $.

    $( Every strongly inaccessible cardinal is weakly inaccessible.
       (Contributed by Mario Carneiro, 29-May-2014.) $)
    inawina $p |- ( A e. Inacc -> A e. InaccW ) $=
      ( vx vy c0 wne ccf cfv wceq cv cpw csdm wbr wral w3a wrex cina wcel cwina
      con0 idd cfon eleq1 mpbii inawinalem 3anim123d mpcom elina elwina 3imtr4i
      3ad2ant2 ) ADEZAFGZAHZBIZJAKLBAMZNZUKUMUNCIKLCAOBAMZNZAPQARQASQZUPURUMUKU
      SUOUMULSQUSAUAULASUBUCUJUSUKUKUMUMUOUQUSUKTUSUMTBCAUDUEUFBAUGBCAUHUI $.
  $}

  $( ` _om ` is a strongly inaccessible cardinal.  (Many definitions of
     "inaccessible" explicitly disallow ` _om ` as an inaccessible cardinal,
     but this choice allows to reuse our results for inaccessibles for
     ` _om ` .)  (Contributed by Mario Carneiro, 29-May-2014.) $)
  omina $p |- _om e. Inacc $=
    ( vx com cina wcel c0 wne ccf cfv wceq cv cpw csdm wbr wral peano1 cfom cfn
    ne0ii nnfi sylib pwfi isfinite rgen elina mpbir3an ) BCDBEFBGHBIAJZKZBLMZAB
    NEBORPUHABUFBDZUGQDZUHUIUFQDUJUFSUFUATUGUBTUCABUDUE $.

  ${
    $d A x y $.
    $( A weakly inaccessible cardinal is a cardinal.  (Contributed by Mario
       Carneiro, 29-May-2014.) $)
    winacard $p |- ( A e. InaccW -> ( card ` A ) = A ) $=
      ( vx vy cwina wcel c0 wne ccf cfv wceq csdm wbr wrex wral w3a ccrd elwina
      cv cardcf fveq2 id 3eqtr3a 3ad2ant2 sylbi ) ADEAFGZAHIZAJZBRCRKLCAMBANZOA
      PIZAJZBCAQUGUEUJUHUGUFPIUFUIAASUFAPTUGUAUBUCUD $.
  $}

  ${
    $d A w x y z $.
    $( A weakly inaccessible cardinal is infinite.  (Contributed by Mario
       Carneiro, 29-May-2014.) $)
    winainflem $p |- ( ( A =/= (/) /\ A e. On /\
        A. x e. A E. y e. A x ~< y ) -> _om C_ A ) $=
      ( vz vw c0 con0 wcel cv csdm wbr wrex w3a com wss wn wceq wa eleq2 syl wo
      wne wral csuc nn0suc simp1 necon2bi vex sucid mpbiri adantl breq1 rexbidv
      wi breq2 cbvrexvw bitrdi rspcv cdom cvv biimpa 3ad2antl2 nnon onsuc eleq1
      biimparc sylan 3adant3 onelon simpl1 onsssuc syl2anc mpbird mpsyl domnsym
      wb ssdomg nrexdv 3expia pm2.65d intn3an3d rexlimiva jaoi con2i word ordom
      eloni 3ad2ant2 ordtri1 sylancr ) CFUBZCGHZAIZBIZJKZBCLZACUCZMZNCOZCNHZPZW
      TWRWTCFQZCDIZUDZQZDNLZUAWRPZDCUEXBXGXFWRCFWKWLWQUFUGXEXGDNXCNHZXERZWQWKWL
      XIWQXCEIZJKZECLZXIXCCHZWQXLUNXEXMXHXEXMXCXDHXCDUHZUICXDXCSUJUKWPXLAXCCWMX
      CQZWPXCWNJKZBCLXLXOWOXPBCWMXCWNJULUMXPXKBECWNXJXCJUOUPUQURTXHXEWQXLPXHXEW
      QMZXKECXQXJCHZRZXJXCUSKZXKPXCUTHXSXJXCOZXTXNXSYAXJXDHZXEXHXRYBWQXEXRYBCXD
      XJSVAVBXSXJGHZXCGHZYAYBVPXQWLXRYCXHXEWLWQXHXDGHZXEWLXHYDYEXCVCZXCVDTXEWLY
      ECXDGVEVFVGVHCXJVIVGXSXHYDXHXEWQXRVJYFTXJXCVKVLVMXJXCUTVQVNXJXCVOTVRVSVTW
      AWBWCTWDWRNWECWEZWSXAVPWFWLWKYGWQCWGWHNCWIWJVM $.

    $( A weakly inaccessible cardinal is infinite.  (Contributed by Mario
       Carneiro, 29-May-2014.) $)
    winainf $p |- ( A e. InaccW -> _om C_ A ) $=
      ( vx vy cwina wcel wne ccf cfv wceq csdm wbr wrex wral w3a com wss elwina
      c0 cv con0 cfon eleq1 mpbii winainflem syl3an2 sylbi ) ADEARFZAGHZAIZBSCS
      JKCALBAMZNOAPZBCAQUIUGATEZUJUKUIUHTEULAUAUHATUBUCBCAUDUEUF $.

    $( A weakly inaccessible cardinal is a limit ordinal.  (Contributed by
       Mario Carneiro, 29-May-2014.) $)
    winalim $p |- ( A e. InaccW -> Lim A ) $=
      ( cwina wcel com wss wlim winainf ccrd cfv wceq wb winacard cardlim sseq2
      limeq bibi12d mpbii syl mpbid ) ABCZDAEZAFZAGTAHIZAJZUAUBKZALUDDUCEZUCFZK
      UEAMUDUFUAUGUBUCADNUCAOPQRS $.

    $( A nontrivial weakly inaccessible cardinal is a limit aleph.
       (Contributed by Mario Carneiro, 29-May-2014.) $)
    winalim2 $p |- ( ( A e. InaccW /\ A =/= _om ) ->
      E. x ( ( aleph ` x ) = A /\ Lim x ) ) $=
      ( vy vw vz wcel com wne wa cv cale cfv wceq con0 wrex wex c0 wn csdm wbr
      cwina wlim ccrd winacard wss winainf cardalephex syl adantr df-rex simprr
      wb mpbid eqcomd csuc cvv w3o simprl onzsl sylib simplr aleph0 eqtrdi eqtr
      fveq2 sylan2 ex necon3ad sylc pm2.21d breq1 rexbidv wral elwina ad3antrrr
      ccf simp3bi onsuc sucid alephord2i mpisyl ad2antrl simplrr ad2antll eqtrd
      vex eleqtrrd rspcdva expr wi iscard simprbi rsp breq2d sylibd alephnbtwn2
      3syl pm3.21 mtoi syl6 imp nrexdv pm2.65d simpr a1i 3jaod mpd jca biimtrid
      eximdv ) BUAFZBGHZIZBAJZKLZMZANOZXOBMZXNUBZIZAPZXKXQXLXKBUCLBMZXQBUDZXKGB
      UEYBXQULBUFABUGUHUMUIXQXNNFZXPIZAPXMYAXPANUJXMYEXTAXMYEXTXMYEIZXRXSYFBXOX
      MYDXPUKZUNYFXNQMZXNCJZUOZMZCNOZXNUPFZXSIZUQZXSYFYDYOXMYDXPURCXNUSUTYFYHXS
      YLYNYFYHXSYFXPXLYHRYGXKXLYEVAXPYHBGXPYHBGMZYHXPXOGMYPYHXOQKLGXNQKVEVBVCBX
      OGVDVFVGVHVIVJYFYLXSYFYKCNYFYINFZIYKYIKLZDJZSTZDBOZYFYQYKUUAYFYQYKIZIZEJZ
      YSSTZDBOZUUAEBYRUUDYRMUUEYTDBUUDYRYSSVKVLXKUUFEBVMZXLYEUUBXKBQHBVPLBMUUGE
      DBVNVQVOUUCYRYJKLZBYQYRUUHFZYFYKYQYJNFYIYJFUUIYIVRYICWFVSYIYJVTWAWBUUCBXO
      UUHXMYDXPUUBWCYKXOUUHMYFYQXNYJKVEWDWEZWGWHWIYFYQYKUUARUUCYTDBUUCYSBFZYTRZ
      UUCUUKYSUUHSTZUULUUCUUKYSBSTZUUMXKUUKUUNWJZXLYEUUBXKYBUUNDBVMZUUOYCYBBNFU
      UPDBWKWLUUNDBWMWQVOUUCBUUHYSSUUJWNWOUUMYTYTUUMIYIYSWPUUMYTWRWSWTXAXBWIXCX
      BVJYNXSWJYFYMXSXDXEXFXGXHVGXJXIXG $.
  $}

  ${
    $d A x $.  $d A y z $.
    $( A nontrivial weakly inaccessible cardinal is a fixed point of the aleph
       function.  (Contributed by Mario Carneiro, 29-May-2014.) $)
    winafp $p |- ( ( A e. InaccW /\ A =/= _om ) -> ( aleph ` A ) = A ) $=
      ( vx vy vz cwina wcel com wne wa cale cfv wceq wlim winalim2 cvv ad2antll
      cv ccf fveq2d eqtr3d wss con0 vex limelon mpan alephle syl simprl sseqtrd
      alephsing csdm wbr wrex wral elwina simp2bi ad2antrr cfle eqsstrrdi eqssd
      c0 exlimddv ) AEFZAGHZIZBQZJKZALZVFMZIZAJKZALBBANVEVJIZVGVKAVLVFAJVLVFAVL
      VFVGAVIVFVGUAZVEVHVIVFUBFZVMVFOFVIVNBUCVFOUDUEVFUFUGPVEVHVIUHZUIVLAVFRKZV
      FVLARKZVPAVLVGRKZVQVPVLVGARVOSVIVRVPLVEVHVFUJPTVCVQALZVDVJVCAVAHVSCQDQUKU
      LDAUMCAUNCDAUOUPUQTVFURUSUTSVOTVB $.
  $}

  ${
    winafp.1 $e |- A e. InaccW $.
    winafp.2 $e |- A =/= _om $.
    $( This theorem, which states that a nontrivial inaccessible cardinal is
       its own aleph number, is stated here in inference form, where the
       assumptions are in the hypotheses rather than an antecedent.  Often, we
       use ~ dedth to turn this type of statement into the closed form
       statement ~ winafp , but in this case, since it is consistent with ZFC
       that there are no nontrivial inaccessible cardinals, it is not possible
       to prove ~ winafp using this theorem and ~ dedth , in ZFC. (You can
       prove this if you use ~ ax-groth , though.)  (Contributed by Mario
       Carneiro, 28-May-2014.) $)
    winafpi $p |- ( aleph ` A ) = A $=
      ( cwina wcel com wne cale cfv wceq winafp mp2an ) ADEAFGAHIAJBCAKL $.
  $}

  ${
    $d x y z $.
    $( Assuming the GCH, weakly and strongly inaccessible cardinals coincide.
       Theorem 11.20 of [TakeutiZaring] p. 106.  (Contributed by Mario
       Carneiro, 5-Jun-2015.) $)
    gchina $p |- ( GCH = _V -> InaccW = Inacc ) $=
      ( vx vy vz cgch cvv wceq cwina cina cv wcel wa cfv csdm wbr wral w3a cdom
      wi com syl simpr c0 wne ccf wrex cpw idd cfn pwfi isfinite winainf ssdomg
      wss mpd sdomdomtr expcom biimtrid ad3antlr wn wb simplll eleqtrrid simprr
      a1dd vex gchinf syl2anc gchpwdom syl3anc winacard iscard simprbi ad2antlr
      ccrd con0 r19.21bi domsdomtr adantrr pm2.61d rexlimdva ralimdva 3anim123d
      sylbid expr elwina elina 3imtr4g ex inawina impbid1 eqrdv ) DEFZAGHWLAIZG
      JZWMHJZWLWNWOWLWNKZWNWOWLWNUAWPWMUBUCZWMUDLWMFZBIZCIZMNZCWMUEZBWMOZPWQWRW
      SUFZWMMNZBWMOZPWNWOWPWQWQWRWRXCXFWPWQUGWPWRUGWPXBXEBWMWPWSWMJZKZXAXECWMXH
      WTWMJZKZWSUHJZXAXERZXJXKXEXAWNXKXERWLXGXIXKXDUHJZWNXEWSUIXMXDSMNZWNXEXDUJ
      WNSWMQNZXNXERWNSWMUMXOWMUKSWMGULUNXNXOXEXDSWMUOUPTUQUQURVDXHXIXKUSZXLXHXI
      XPKZKZXAXDWTQNZXEXRSWSQNZWSDJZWTDJXAXSUTXRYAXPXTXRWSEDBVEWLWNXGXQVAZVBZXH
      XIXPVCWSVFVGYCXRWTEDCVEYBVBWSWTVHVIXHXIXSXERZXPXJWTWMMNZYDXHYECWMWNYECWMO
      ZWLXGWNWMVNLWMFZYFWMVJYGWMVOJYFCWMVKVLTVMVPXSYEXEXDWTWMVQUPTVRWCWDVSVTWAW
      BBCWMWEBWMWFWGUNWHWMWIWJWK $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Weak universes
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c WUni $. $( The class of weak universes. $)
  $c wUniCl $. $( The function of "weak universe closure". $)

  $( Extend class definition to include the class of all weak universes. $)
  cwun $a class WUni $.

  $( Extend class definition to include the map whose value is the smallest
     weak universe of which the given set is a subset. $)
  cwunm $a class wUniCl $.

  ${
    $d x y A $.  $d y B $.  $d u x y U $.
    $( The class of all weak universes.  A weak universe is a nonempty
       transitive class closed under union, pairing, and powerset.  The
       advantage of weak universes over Grothendieck universes is that one can
       prove that every set is contained in a weak universe in ZF (see
       ~ uniwun ) whereas the analogue for Grothendieck universes requires
       ~ ax-groth (see ~ grothtsk ).  (Contributed by Mario Carneiro,
       2-Jan-2017.) $)
    df-wun $a |- WUni = { u | ( Tr u /\ u =/= (/) /\
      A. x e. u ( U. x e. u /\ ~P x e. u /\ A. y e. u { x , y } e. u ) ) } $.

    $( A function that maps a set ` x ` to the smallest weak universe that
       contains the elements of the set.  (Contributed by Mario Carneiro,
       2-Jan-2017.) $)
    df-wunc $a |- wUniCl = ( x e. _V |-> |^| { u e. WUni | x C_ u } ) $.

    $( Properties of a weak universe.  (Contributed by Mario Carneiro,
       2-Jan-2017.) $)
    iswun $p |- ( U e. V -> ( U e. WUni <-> ( Tr U /\ U =/= (/) /\
      A. x e. U ( U. x e. U /\ ~P x e. U /\ A. y e. U { x , y } e. U ) ) ) ) $=
      ( vu cv wtr wne cuni wcel cpw cpr wral w3a cwun wceq raleqbi1dv 3anbi123d
      c0 eleq2 treq neeq1 df-wun elab2g ) EFZGZUESHZAFZIZUEJZUHKZUEJZUHBFLZUEJZ
      BUEMZNZAUEMZNCGZCSHZUICJZUKCJZUMCJZBCMZNZACMZNECODUECPZUFURUGUSUQVEUECUAU
      ECSUBUPVDAUECVFUJUTULVAUOVCUECUITUECUKTUNVBBUECUECUMTQRQRABEUCUD $.

    $( A weak universe is transitive.  (Contributed by Mario Carneiro,
       2-Jan-2017.) $)
    wuntr $p |- ( U e. WUni -> Tr U ) $=
      ( vx vy cwun wcel wtr c0 wne cv cuni cpw cpr wral w3a iswun ibi simp1d )
      ADEZAFZAGHZBIZJAEUAKAEUACILAECAMNBAMZRSTUBNBCADOPQ $.

    wununi.1 $e |- ( ph -> U e. WUni ) $.
    wununi.2 $e |- ( ph -> A e. U ) $.
    $( A weak universe is closed under union.  (Contributed by Mario Carneiro,
       2-Jan-2017.) $)
    wununi $p |- ( ph -> U. A e. U ) $=
      ( vx vy cv cuni wcel wceq unieq eleq1d cwun cpw cpr wral w3a wtr c0 iswun
      wne ibi simp3d simp1 ralimi 3syl rspcdva ) AFHZIZCJZBIZCJFCBUIBKUJULCUIBL
      MACNJZUKUIOCJZUIGHPCJGCQZRZFCQZUKFCQDUMCSZCTUBZUQUMURUSUQRFGCNUAUCUDUPUKF
      CUKUNUOUEUFUGEUH $.

    $( A weak universe is closed under powerset.  (Contributed by Mario
       Carneiro, 2-Jan-2017.) $)
    wunpw $p |- ( ph -> ~P A e. U ) $=
      ( vx vy cv cpw wcel wceq pweq eleq1d cwun cuni cpr wral w3a wtr c0 simp3d
      wne iswun ibi simp2 ralimi 3syl rspcdva ) AFHZIZCJZBIZCJFCBUIBKUJULCUIBLM
      ACNJZUIOCJZUKUIGHPCJGCQZRZFCQZUKFCQDUMCSZCTUBZUQUMURUSUQRFGCNUCUDUAUPUKFC
      UNUKUOUEUFUGEUH $.

    $( The elements of a weak universe are also subsets of it.  (Contributed by
       Mario Carneiro, 2-Jan-2017.) $)
    wunelss $p |- ( ph -> A C_ U ) $=
      ( wtr wcel wss cwun wuntr syl trss sylc ) ACFZBCGBCHACIGNDCJKECBLM $.

    ${
      wunpr.3 $e |- ( ph -> B e. U ) $.
      $( A weak universe is closed under pairing.  (Contributed by Mario
         Carneiro, 2-Jan-2017.) $)
      wunpr $p |- ( ph -> { A , B } e. U ) $=
        ( vx vy wcel cv cpr wral cwun cuni cpw w3a wtr wceq eleq1d c0 wne iswun
        ibi simp3d simp3 ralimi 3syl preq1 preq2 rspc2va syl21anc ) ABDJCDJHKZI
        KZLZDJZIDMZHDMZBCLZDJZFGADNJZUMODJZUMPDJZUQQZHDMZUREVADRZDUAUBZVEVAVFVG
        VEQHIDNUCUDUEVDUQHDVBVCUQUFUGUHUPUTBUNLZDJHIBCDDUMBSUOVHDUMBUNUITUNCSVH
        USDUNCBUJTUKUL $.

      $( A weak universe is closed under binary union.  (Contributed by Mario
         Carneiro, 2-Jan-2017.) $)
      wunun $p |- ( ph -> ( A u. B ) e. U ) $=
        ( cpr cuni cun wcel wceq uniprg syl2anc wunpr wununi eqeltrrd ) ABCHZIZ
        BCJZDABDKCDKSTLFGBCDDMNARDEABCDEFGOPQ $.

      wuntp.3 $e |- ( ph -> C e. U ) $.
      $( A weak universe is closed under unordered triple.  (Contributed by
         Mario Carneiro, 2-Jan-2017.) $)
      wuntp $p |- ( ph -> { A , B , C } e. U ) $=
        ( ctp csn cpr cun tpass dfsn2 wunpr eqeltrid wunun ) ABCDJBKZCDLZMEBCDN
        ASTEFASBBLEBOABBEFGGPQACDEFHIPRQ $.
    $}

    ${
      wunss.3 $e |- ( ph -> B C_ A ) $.
      $( A weak universe is closed under subsets.  (Contributed by Mario
         Carneiro, 2-Jan-2017.) $)
      wunss $p |- ( ph -> B e. U ) $=
        ( cpw wunpw wunelss sselpwd sseldd ) ABHZDCAMDEABDEFIJACBDFGKL $.
    $}

    $( A weak universe is closed under binary intersections.  (Contributed by
       Mario Carneiro, 2-Jan-2017.) $)
    wunin $p |- ( ph -> ( A i^i B ) e. U ) $=
      ( cin wss inss1 a1i wunss ) ABBCGZDEFLBHABCIJK $.

    $( A weak universe is closed under class difference.  (Contributed by Mario
       Carneiro, 2-Jan-2017.) $)
    wundif $p |- ( ph -> ( A \ B ) e. U ) $=
      ( cdif difssd wunss ) ABBCGDEFABCHI $.

    $( A weak universe is closed under nonempty intersections.  (Contributed by
       Mario Carneiro, 2-Jan-2017.) $)
    wunint $p |- ( ( ph /\ A =/= (/) ) -> |^| A e. U ) $=
      ( c0 wne wa cuni cint cwun wcel adantr wununi wss intssuni adantl wunss )
      ABFGZHBIZBJZCACKLSDMATCLSABCDENMSUATOABPQR $.

    $( A weak universe is closed under singletons.  (Contributed by Mario
       Carneiro, 2-Jan-2017.) $)
    wunsn $p |- ( ph -> { A } e. U ) $=
      ( csn cpr dfsn2 wunpr eqeltrid ) ABFBBGCBHABBCDEEIJ $.

    $( A weak universe is closed under successors.  (Contributed by Mario
       Carneiro, 2-Jan-2017.) $)
    wunsuc $p |- ( ph -> suc A e. U ) $=
      ( csuc csn cun df-suc wunsn wunun eqeltrid ) ABFBBGZHCBIABMCDEABCDEJKL $.
  $}

  ${
    $d x y z A $.  $d x y z ph $.  $d x y z U $.
    wun0.1 $e |- ( ph -> U e. WUni ) $.
    $( A weak universe contains the empty set.  (Contributed by Mario Carneiro,
       2-Jan-2017.) $)
    wun0 $p |- ( ph -> (/) e. U ) $=
      ( vx vy cv wcel wne wex cwun wtr cuni cpw cpr wral w3a iswun ibi simp2d
      c0 syl n0 sylib wa adantr simpr wss 0ss a1i wunss exlimddv ) ADFZBGZTBGDA
      BTHZUMDIABJGZUNCUOBKZUNULLBGULMBGULEFNBGEBOPDBOZUOUPUNUQPDEBJQRSUADBUBUCA
      UMUDZULTBAUOUMCUEAUMUFTULUGURULUHUIUJUK $.

    $( A weak universe is infinite, because it contains all the finite levels
       of the cumulative hierarchy.  (Contributed by Mario Carneiro,
       2-Jan-2017.) $)
    wunr1om $p |- ( ph -> ( R1 " _om ) C_ U ) $=
      ( vy vx cr1 com cima cv cfv wceq wrex wcel wi csuc fveq2 eleq1d r10 con0
      c0 wun0 eqeltrid wa cpw cwun adantr simpr wunpw nnon r1suc imbitrrid expd
      syl finds2 eleq1 imbi2d syl5ibcom rexlimiv wfn r1fnon fnfun ax-mp fvelima
      wfun mpan syl11 ssrdv ) ADFGHZBEIZFJZDIZKZEGLZAVKBMZVKVHMZVLAVNNZEGVIGMAV
      JBMZNVLVPVQTFJZBMVKFJZBMZVKOZFJZBMZAEDVITKVJVRBVITFPQVIVKKVJVSBVIVKFPQVIW
      AKVJWBBVIWAFPQAVRTBRABCUAUBVKGMZAVTWCAVTUCZWCWDVSUDZBMWEVSBABUEMVTCUFAVTU
      GUHWDWBWFBWDVKSMWBWFKVKUIVKUJUMQUKULUNVLVQVNAVJVKBUOUPUQURFVDZVOVMFSUSWGU
      TSFVAVBEVKGFVCVEVFVG $.

    $( A weak universe contains all the finite ordinals, and hence is infinite.
       (Contributed by Mario Carneiro, 2-Jan-2017.) $)
    wunom $p |- ( ph -> _om C_ U ) $=
      ( vx com cv wcel wa cr1 cfv cwun adantr cima wss wral wunr1om wfun cdm wb
      r1funlim simpli simpri limomss ax-mp funimass4 mp2an sylib r19.21bi simpr
      wlim sselid onssr1 syl wunss ex ssrdv ) ADEBADFZEGZUQBGAURHZUQIJZUQBABKGU
      RCLAUTBGZDEAIEMBNZVADEOZABCPIQZEIRZNZVBVCSVDVEUJZTUAVGVFVDVGTUBVEUCUDZDEB
      IUEUFUGUHUSUQVEGUQUTNUSEVEUQVHAURUIUKUQULUMUNUOUP $.

    ${
      wunfi.2 $e |- ( ph -> A C_ U ) $.
      wunfi.3 $e |- ( ph -> A e. Fin ) $.
      $( A weak universe contains all finite sets with elements drawn from the
         universe.  (Contributed by Mario Carneiro, 2-Jan-2017.) $)
      wunfi $p |- ( ph -> A e. U ) $=
        ( vx vy vz wss wcel cfn wi cv c0 wceq sseq1 eleq1 imbi12d imbi2d imim1i
        csn cun wun0 a1d sstr mpan wa cwun adantr simprr simprl unssbd vex snss
        ssun1 sylibr wunsn wunun exp32 a2d syl5 a2i a1i findcard2 mpcom mpd ) A
        BCJZBCKZEBLKAVHVIMZFAGNZCJZVKCKZMZMAOCJZOCKZMZMAHNZCJZVRCKZMZMZAVRINZUB
        ZUCZCJZWECKZMZMZAVJMGHIBVKOPZVNVQAWJVLVOVMVPVKOCQVKOCRSTVKVRPZVNWAAWKVL
        VSVMVTVKVRCQVKVRCRSTVKWEPZVNWHAWLVLWFVMWGVKWECQVKWECRSTVKBPZVNVJAWMVLVH
        VMVIVKBCQVKBCRSTAVPVOACDUDUEWBWIMVRLKAWAWHWAWFVTMAWHWFVSVTVRWEJWFVSVRWD
        UPVRWECUFUGUAAWFVTWGAWFVTWGAWFVTUHZUHZVRWDCACUIKWNDUJZAWFVTUKWOWCCWPWOW
        DCJWCCKWOVRWDCAWFVTULUMWCCIUNUOUQURUSUTVAVBVCVDVEVFVG $.
    $}

    wunop.2 $e |- ( ph -> A e. U ) $.
    ${
      wunop.3 $e |- ( ph -> B e. U ) $.
      $( A weak universe is closed under ordered pairs.  (Contributed by Mario
         Carneiro, 2-Jan-2017.) $)
      wunop $p |- ( ph -> <. A , B >. e. U ) $=
        ( cop csn cpr wcel wceq dfopg syl2anc wunsn wunpr eqeltrd ) ABCHZBIZBCJ
        ZJZDABDKCDKRUALFGBCDDMNASTDEABDEFOABCDEFGPPQ $.

      ${
        wunot.3 $e |- ( ph -> C e. U ) $.
        $( A weak universe is closed under ordered triples.  (Contributed by
           Mario Carneiro, 2-Jan-2017.) $)
        wunot $p |- ( ph -> <. A , B , C >. e. U ) $=
          ( cotp cop df-ot wunop eqeltrid ) ABCDJBCKZDKEBCDLAODEFABCEFGHMIMN $.
      $}

      $( A weak universe is closed under cartesian products.  (Contributed by
         Mario Carneiro, 2-Jan-2017.) $)
      wunxp $p |- ( ph -> ( A X. B ) e. U ) $=
        ( cun cpw cxp wunun wunpw wss xpsspw a1i wunss ) ABCHZIZIZBCJZDEARDEAQD
        EABCDEFGKLLTSMABCNOP $.

      $( A weak universe is closed under partial mappings.  (Contributed by
         Mario Carneiro, 2-Jan-2017.) $)
      wunpm $p |- ( ph -> ( A ^pm B ) e. U ) $=
        ( cxp cpw cpm co wunxp wunpw wss pmsspw a1i wunss ) ACBHZIZBCJKZDEARDEA
        CBDEGFLMTSNABCOPQ $.

      $( A weak universe is closed under mappings.  (Contributed by Mario
         Carneiro, 2-Jan-2017.) $)
      wunmap $p |- ( ph -> ( A ^m B ) e. U ) $=
        ( cpm co cmap wunpm wss mapsspm a1i wunss ) ABCHIZBCJIZDEABCDEFGKQPLABC
        MNO $.

      wunf.3 $e |- ( ph -> F : A --> B ) $.
      $( A weak universe is closed under functions with known domain and
         codomain.  (Contributed by Mario Carneiro, 2-Jan-2017.) $)
      wunf $p |- ( ph -> F e. U ) $=
        ( cmap co wunmap wunelss wcel wf elmapd mpbird sseldd ) ACBJKZDEASDFACB
        DFHGLMAESNBCEOIACBEDDHGPQR $.
    $}

    $( A weak universe is closed under the domain operator.  (Contributed by
       Mario Carneiro, 2-Jan-2017.) $)
    wundm $p |- ( ph -> dom A e. U ) $=
      ( cuni cdm wununi wss crn cun ssun1 dmrnssfld sstri a1i wunss ) ABFZFZBGZ
      CDAQCDABCDEHHSRIASSBJZKRSTLBMNOP $.

    $( A weak universe is closed under the range operator.  (Contributed by
       Mario Carneiro, 2-Jan-2017.) $)
    wunrn $p |- ( ph -> ran A e. U ) $=
      ( cuni crn wununi wss cdm cun ssun2 dmrnssfld sstri a1i wunss ) ABFZFZBGZ
      CDAQCDABCDEHHSRIASBJZSKRSTLBMNOP $.

    $( A weak universe is closed under the converse operator.  (Contributed by
       Mario Carneiro, 2-Jan-2017.) $)
    wuncnv $p |- ( ph -> `' A e. U ) $=
      ( crn cdm cxp ccnv wunrn wundm wunxp wss cnvssrndm a1i wunss ) ABFZBGZHZB
      IZCDAQRCDABCDEJABCDEKLTSMABNOP $.

    $( A weak universe is closed under restrictions.  (Contributed by Mario
       Carneiro, 12-Jan-2017.) $)
    wunres $p |- ( ph -> ( A |` B ) e. U ) $=
      ( cres wss resss a1i wunss ) ABBCGZDEFLBHABCIJK $.

    $( A weak universe is closed under the function value operator.
       (Contributed by Mario Carneiro, 3-Jan-2017.) $)
    wunfv $p |- ( ph -> ( A ` B ) e. U ) $=
      ( crn cuni cfv wunrn wununi wss fvssunirn a1i wunss ) ABGZHZCBIZDEAPDEABD
      EFJKRQLABCMNO $.

    ${
      wunco.3 $e |- ( ph -> B e. U ) $.
      $( A weak universe is closed under composition.  (Contributed by Mario
         Carneiro, 12-Jan-2017.) $)
      wunco $p |- ( ph -> ( A o. B ) e. U ) $=
        ( ccom cdm crn cxp wundm wss dmcoss a1i wunss wunrn rncoss wunxp wrel
        relco relssdmrn mp1i ) ABCHZIZUDJZKZUDDEAUEUFDEACIZUEDEACDEGLUEUHMABCNO
        PABJZUFDEABDEFQUFUIMABCROPSUDTUDUGMABCUAUDUBUCP $.
    $}

    $( A weak universe is closed under transposition.  (Contributed by Mario
       Carneiro, 12-Jan-2017.) $)
    wuntpos $p |- ( ph -> tpos A e. U ) $=
      ( cdm ccnv c0 csn cun crn ctpos wundm wuncnv wun0 wunsn wunun wunrn wunxp
      cxp wss tposssxp a1i wunss ) ABFZGZHIZJZBKZTZBLZCDAUHUICDAUFUGCDAUECDABCD
      EMNAHCDACDOPQABCDERSUKUJUAABUBUCUD $.
  $}

  ${
    $d u x y A $.
    $( The intersection of a collection of weak universes is a weak universe.
       (Contributed by Mario Carneiro, 2-Jan-2017.) $)
    intwun $p |- ( ( A C_ WUni /\ A =/= (/) ) -> |^| A e. WUni ) $=
      ( vx vy vu cwun wss c0 wne wa wcel wtr cv w3a sselda syl ralrimiva elint2
      wral sylibr adantlr cint cuni cpw cpr simpl wuntr trint 0ex intss1 adantl
      wun0 ne0d an32s wununi vuniex wunpw vpwex wunpr prex 3jca wb intex bilani
      cvv iswun mpbir3and ) AEFZAGHZIZAUAZEJZVJKZVJGHZBLZUBZVJJZVNUCZVJJZVNCLZU
      DZVJJZCVJRZMZBVJRZVIDLZKZDARVLVIWFDAVIWEAJZIZWEEJZWFVIAEWEVGVHUENZWEUFOPD
      AUGOVIVJGVIGWEJZDARGVJJVIWKDAWHWEWJUKPDGAUHQSULVIWCBVJVIVNVJJZIZVPVRWBWMV
      OWEJZDARVPWMWNDAWMWGIZVNWEVIWGWIWLWJTZVIWGWLVNWEJZWHVJWEVNWGVJWEFZVIWEAUI
      ZUJNUMZUNPDVOABUOQSWMVQWEJZDARVRWMXADAWOVNWEWPWTUPPDVQABUQQSWMWACVJWMVSVJ
      JZIZVTWEJZDARWAXCXDDAXCWGIVNVSWEWMWGWIXBWPTWMWGWQXBWTTWMWGXBVSWEJWOVJWEVS
      WGWRWMWSUJNUMURPDVTAVNVSUSQSPUTPVIVJVDJZVKVLVMWDMVAVHXEVGAVBVCBCVJVDVEOVF
      $.
  $}

  ${
    $d x y A $.  $d x y V $.
    $( Each limit stage in the cumulative hierarchy is a weak universe.
       (Contributed by Mario Carneiro, 2-Jan-2017.) $)
    r1limwun $p |- ( ( A e. V /\ Lim A ) -> ( R1 ` A ) e. WUni ) $=
      ( vx vy wcel wa cr1 cfv cuni wral w3a a1i con0 adantl crnk adantr syl2anc
      c0 cv wb wlim wtr wne cpw cpr cwun cdm wss limelon r1fnon fndmi eleqtrrdi
      r1tr onssr1 syl 0ellim sseldd ne0d rankuni rankon eloni orduniss rankr1ai
      word mp2b wi onuni ax-mp ontr2 sylancr mp2and eqeltrid r1elwf uniwf sylib
      cima rankr1ag mpbird r1pwcl biimpa cun csuc wceq ad2antlr limord ad3antlr
      rankprb ordunel syl3anc limsuc mpbid eqeltrd prwf ralrimiva 3jca cvv fvex
      iswun syl3anbrc ) ABEZAUAZFZAGHZUBZXCRUCZCSZIZXCEZXFUDXCEZXFDSZUEZXCEZDXC
      JZKZCXCJZXCUFEZXDXBAUMLXBXCRXBAXCRXBAGUGZEZAXCUHXBAMXQABUIZMGUJUKULZAUNUO
      XARAEWTAUPNUQURXBXNCXCXBXFXCEZFZXHXIXMYBXHXGOHZAEZYBYCXFOHZIZAXFUSYBYFYEU
      HZYEAEZYFAEZYGYBYEMEZYEVDYGXFUTZYEVAYEVBVELYAYHXBXFAVCNZYBYFMEZAMEZYGYHFY
      IVFYJYMYKYEVGVHXBYNYAXSPYFYEAVIVJVKVLYBXGGMVPIZEZXRXHYDTYBXFYOEZYPYAYQXBX
      FAVMZNXFVNVOXBXRYAXTPZXGAVQQVRXBYAXIXAYAXITWTXFAVSNVTYBXLDXCYBXJXCEZFZXLX
      KOHZAEZUUAUUBYEXJOHZWAZWBZAUUAYQXJYOEZUUBUUFWCYAYQXBYTYRWDZYTUUGYBXJAVMNZ
      XFXJWGQUUAUUEAEZUUFAEZUUAAVDZYHUUDAEZUUJXAUULWTYAYTAWEWFYBYHYTYLPYTUUMYBX
      JAVCNAYEUUDWHWIXAUUJUUKTWTYAYTAUUEWJWFWKWLUUAXKYOEZXRXLUUCTUUAYQUUGUUNUUH
      UUIXFXJWMQYBXRYTYSPXKAVQQVRWNWOWNXCWPEXPXDXEXOKTAGWQCDXCWPWRVHWS $.

    $( The weak universes in the cumulative hierarchy are exactly the limit
       ordinals.  (Contributed by Mario Carneiro, 2-Jan-2017.) $)
    r1wunlim $p |- ( A e. V -> ( ( R1 ` A ) e. WUni <-> Lim A ) ) $=
      ( vx wcel cr1 cfv cwun wlim wa c0 wceq csuc con0 wn syl sucidg r1ord sylc
      ad2antrl sylanbrc word cv wrex wo simpr wun0 elfvdm r1fnon fndmi eleqtrdi
      cdm eloni n0i fveq2 r10 eqtrdi nsyl cima cuni onsuc r1elwf wfelirr simprr
      3syl cpw fveq2d r1suc eqtrd simplr eleqtrrd wunpw eqeltrd rexlimdvaa mtod
      adantr ioran dflim3 r1limwun impbida ) ABDZAEFZGDZAHZVTWBIZAUAZAJKZACUBZL
      ZKZCMUCZUDNZWCWDAMDZWEWDAEUKZMWDJWADZAWMDWDWAVTWBUEUFZJAEUGOMEUHUIUJZAULO
      WDWFNWJNWKWDWAJKZWFWDWNWQNWOWAJUMOWFWAJEFJAJEUNUOUPUQWDWJWAWADZWDWAALZEFD
      ZWAEMURUSDWRNWDWSMDZAWSDZWTWDWLXAWPAUTOWDWLXBWPAMPOAWSQRWAWSVAWAVBVDWDWIW
      RCMWDWGMDZWIIZIZWAWGEFZVEZWAXEWAWHEFZXGXEAWHEWDXCWIVCZVFXCXHXGKWDWIWGVGSV
      HXEXFWAVTWBXDVIXEWLWGADXFWADWDWLXDWPVOXEWGWHAXCWGWHDWDWIWGMPSXIVJWGAQRVKV
      LVMVNWFWJVPTCAVQTABVRVS $.
  $}

  ${
    $d a u v w x y z $.  $d a b m n w A $.  $d a b m n U $.  $d a b m n V $.
    $d b i k m n u v w F $.
    wunex2.f $e |- F = ( rec ( ( z e. _V |-> ( ( z u. U. z ) u.
      U_ x e. z ( { ~P x , U. x } u.
        ran ( y e. z |-> { x , y } ) ) ) ) , ( A u. 1o ) ) |` _om ) $.
    wunex2.u $e |- U = U. ran F $.
    $( Construct a weak universe from a given set.  (Contributed by Mario
       Carneiro, 2-Jan-2017.) $)
    wunex2 $p |- ( A e. V -> ( U e. WUni /\ A C_ U ) ) $=
      ( va vm vu vv wcel wss cv com cvv cun wa vb vw vn vk vi cwun wtr wne cuni
      c0 cpw cpr wral w3a cfv wrex crn eleq2i wfn wb cmpt ciun crdg cres frfnom
      fneq1i mpbir fnunirn ax-mp bitri csuc elssuni ad2antll ssun2 ssun1 sstrdi
      c1o sstri wceq simprl fvex uniex unex prex mptex rnex iunex unieq uneq12d
      weq pweq preq12d preq2 cbvmptv preq1 mpteq2dv eqtrid rneqd cbviunv mpteq1
      id uneq2d iuneq12d frsucmpt2 sylancl sseqtrrd fvssunirn sseqtrri biimtrid
      rexlimdvaa ralrimiv dftr3 sylibr con0 1on unexg fveq1i fr0g syl eqsstrrdi
      mpan2 unssbd ssn0 ssiun2s sseqtrrid sstrd unssad vpwex vuniex prss simprd
      1n0 fveq2 sseq2d vtoclga findsg sseldd wi imbi12d eqeltri simplrl ordunel
      simpld ordom mp3an2i ssidd suceq sseq12d ad2antrr syl5com syl2anc simplrr
      word fveq2d sstr2 biantrud bicomd eleq1w anbi2d sseq1 anbi12d sseq1d expl
      chvarvv sylc simprr eqid elrnmpt1s 3jca wfun rdgfun resfunexg mp2an iswun
      omex syl3anbrc jca ) DGNZEUFNZDEOUVREUGZEUJUHZJPZUIZENZUWBUKZENZUWBUAPZUL
      ZENZUAEUMZUNZJEUMZUVSUVRUWBEOZJEUMUVTUVRUWMJEUWBENZUWBKPZFUOZNZKQUPZUVRUW
      MUWNUWBFUQZUIZNZUWREUWTUWBIURFQUSZUXAUWRUTUXBCRCPZUXCUIZSZAUXCAPZUKZUXFUI
      ZULZBUXCUXFBPZULZVAZUQZSZVBZSZVAZDVQSZVCZQVDZQUSUXRUXQVEQFUXTHVFVGZKUWBFQ
      VHVIVJZUVRUWQUWMKQUVRUWOQNZUWQTTZUWBUWOVKZFUOZEUYDUWBUWPUWPUIZSZLUWPLPZUK
      ZUYIUIZULZMUWPUYIMPZULZVAZUQZSZVBZSZUYFUYDUWBUYGUYSUWQUWBUYGOUVRUYCUWBUWP
      VLVMUYGUYHUYSUYGUWPVNUYHUYRVOZVRVPUYDUYCUYSRNZUYFUYSVSZUVRUYCUWQVTUYHUYRU
      WPUYGUWOFWAZUWPVUCWBWCLUWPUYQVUCUYLUYPUYJUYKWDZUYOMUWPUYNVUCWEWFWCWGWCZCU
      BUXRUWOUXPUYSUBPZVUFUIZSZLVUFUYLMVUFUYNVAZUQZSZVBZSZFRHUBCWJZVUHUXEVULUXO
      VUNVUFUXCVUGUXDVUNXAZVUFUXCWHWIVUNVULAVUFUXIBVUFUXKVAZUQZSZVBUXOLAVUFVUKV
      URLAWJZUYLUXIVUJVUQVUSUYJUXGUYKUXHUYIUXFWKUYIUXFWHWLVUSVUIVUPVUSVUIBVUFUY
      IUXJULZVAVUPMBVUFUYNVUTUYMUXJUYIWMWNVUSBVUFVUTUXKUYIUXFUXJWOWPWQWRWIWSVUN
      AVUFUXCVURUXNVUOVUNVUQUXMUXIVUNVUPUXLBVUFUXCUXKWTWRXBXCWQWIZVUFUWPVSZVUHU
      YHVULUYRVVBVUFUWPVUGUYGVVBXAZVUFUWPWHWIVVBLVUFUWPVUKUYQVVCVVBVUJUYPUYLVVB
      VUIUYOMVUFUWPUYNWTWRXBXCWIXDZXEZXFUYFUWTEFUYEXGIXHZVPXJXIXKJEXLXMUVRVQEOV
      QUJUHUWAUVRDVQEUVRUXRUJFUOZEUVRUXRRNZVVGUXRVSUVRVQXNNVVHXODVQGXNXPYAVVHVV
      GUJUXTUOUXRUJFUXTHXQUXRRUXQXRWQXSVVGUWTEFUJXGIXHXTZYBYLVQEYCXEUVRUWKJEUWN
      UWRUVRUWKUYBUVRUWQUWKKQUYDUWDUWFUWJUYDUWFUWDUYDUWEUWCULZEOUWFUWDTUYDVVJMU
      WPUWBUYMULZVAZUQZEUYDVVJVVMSZUYREUWQVVNUYROUVRUYCLUWPUYQUWBVVNLJWJZUYLVVJ
      UYPVVMVVOUYJUWEUYKUWCUYIUWBWKUYIUWBWHWLZVVOUYOVVLVVOMUWPUYNVVKUYIUWBUYMWO
      ZWPWRWIYDVMUYDUYRUYFEUYDUYSUYRUYFUYRUYHVNVVEYEVVFVPYFYGUWEUWCEJYHJYIYJXMZ
      YKUYDUWFUWDVVRUUCUYDUWIUAEUWGENZUWGUCPZFUOZNZUCQUPZUYDUWIVVSUWGUWTNZVWCEU
      WTUWGIURUXBVWDVWCUTUYAUCUWGFQVHVIVJUYDVWBUWIUCQUYDVVTQNZVWBTZTZMUWOVVTSZF
      UOZVVKVAZUQZEUWHVWGVVJVWKEVWGVVJVWKSZLVWIUYLMVWIUYNVAZUQZSZVBZEVWGUWBVWIN
      VWLVWPOVWGUWPVWIUWBVWGVWHQNZUYCUWPVWIOZQUUMVWGUYCVWEVWQUUDUVRUYCUWQVWFUUA
      ZUYDVWEVWBVTZQUWOVVTUUBUUEZVWSVWQUYCTUWOVWHOVWRUWOVVTVOUWPUDPZFUOZOZUWPUW
      POZUWPUEPZFUOZOZUWPVXFVKZFUOZOZVWRUDUEVWHUWOUDKWJVXCUWPUWPVXBUWOFYMYNZUDU
      EWJVXCVXGUWPVXBVXFFYMYNZVXBVXIVSVXCVXJUWPVXBVXIFYMYNZVXBVWHVSVXCVWIUWPVXB
      VWHFYMYNUYCUWPUUFZVXFQNZUYCTZUWOVXFOZTZVXGVXJOZVXHVXKVXPVXTUYCVXRUWPUYFOV
      XTKVXFQKUEWJZUWPVXGUYFVXJUWOVXFFYMVYAUYEVXIFUWOVXFUUGUUNUUHUYCUYSUWPUYFUW
      PUYHUYSUWPUYGVOUYTVRUYCVUAVUBVUEVVDYAYEYOUUIUWPVXGVXJUUOUUJZYPYAUUKUVRUYC
      UWQVWFUULYQLVWIVWOUWBVWLVVOUYLVVJVWNVWKVVPVVOVWMVWJVVOMVWIUYNVVKVVQWPWRWI
      YDXSVWGVWPVWHVKZFUOZEVWGVWIVWIUIZSZVWPSZVWPVYDVWPVYFVNVWGVWQVYGRNVYDVYGVS
      VXAVYFVWPVWIVYEVWHFWAZVWIVYHWBWCLVWIVWOVYHUYLVWNVUDVWMMVWIUYNVYHWEWFWCWGW
      CCUBUXRVWHUXPVYGVUMFRHVVAVUFVWIVSZVUHVYFVULVWPVYIVUFVWIVUGVYEVYIXAZVUFVWI
      WHWIVYILVUFVWIVUKVWOVYJVYIVUJVWNUYLVYIVUIVWMMVUFVWIUYNWTWRXBXCWIXDXEYEVYD
      UWTEFVYCXGIXHVPYFYBVWGUWGVWINUWHRNUWHVWKNVWGVWAVWIUWGVWGVWQVWEVWAVWIOZVXA
      VWTVWEVVTVXFOZTZVWAVXGOZYRVWEVYKYRUEVWHQVXFVWHVSZVYMVWEVYNVYKVYOVWEVYMVYO
      VYLVWEVYOVWHVVTVXFVVTUWOVNVYOXAYEUUPUUQVYOVXGVWIVWAVXFVWHFYMYNYSVXPVWEVYL
      VYNVXSVXHYRVXPVWETZVYLTZVYNYRKUCKUCWJZVXSVYQVXHVYNVYRVXQVYPVXRVYLVYRUYCVW
      EVXPKUCQUURUUSUWOVVTVXFUUTUVAVYRUWPVWAVXGUWOVVTFYMUVBYSVXDVXEVXHVXKVXHUDU
      EVXFUWOVXLVXMVXNVXMVXOVYBYPUVDUVCYOUVEUYDVWEVWBUVFYQUWBUWGWDMVWIVVKUWHUWG
      VWJRVWJUVGUYMUWGUWBWMUVHXEYQXJXIXKUVIXJXIXKERNUVSUVTUWAUWLUNUTEUWTRIUWSFF
      UXTRHUXSUVJQRNUXTRNUXRUXQUVKUVOUXSQRUVLUVMYTWFWBYTJUAERUVNVIUVPUVRDVQEVVI
      YGUVQ $.
  $}

  ${
    $d u x y z $.  $d u A $.
    $( Construct a weak universe from a given set.  See also ~ wunex2 .
       (Contributed by Mario Carneiro, 2-Jan-2017.) $)
    wunex $p |- ( A e. V -> E. u e. WUni A C_ u ) $=
      ( vz vx vy wcel cvv cv cuni cun cpw cpr cmpt crn ciun c1o cwun wss eqid
      crdg com cres wa wrex wunex2 sseq2 rspcev syl ) BCGDHDIZUJJKEUJEIZLUKJMFU
      JUKFIMNOKPKNBQKUAUBUCZOJZRGBUMSZUDBAIZSZARUEEFDBUMULCULTUMTUFUPUNAUMRUOUM
      BUGUHUI $.

    $( Every set is contained in a weak universe.  This is the analogue of
       ~ grothtsk for weak universes, but it is provable in ZF without the
       Tarski-Grothendieck axiom, contrary to ~ grothtsk .  (Contributed by
       Mario Carneiro, 2-Jan-2017.) $)
    uniwun $p |- U. WUni = _V $=
      ( vx vu cwun cuni cvv wceq wcel eqv csn wss wrex vsnex wunex ax-mp eluni2
      cv vex snss rexbii bitri mpbir mpgbir ) CDZEFAPZUCGZAAUCHUEUDIZBPZJZBCKZU
      FEGUIALBUFEMNUEUDUGGZBCKUIBUDCOUJUHBCUDUGAQRSTUAUB $.

    wunex3.u $e |- U = ( R1 ` ( ( rank ` A ) +o _om ) ) $.
    $( Construct a weak universe from a given set.  This version of ~ wunex has
       a simpler proof, but requires the axiom of regularity.  (Contributed by
       Mario Carneiro, 2-Jan-2017.) $)
    wunex3 $p |- ( A e. V -> ( U e. WUni /\ A C_ U ) ) $=
      ( wcel wss cwun crnk cfv cr1 r1rankid com coa co con0 rankon omelon mp2an
      oacl wlim c0 peano1 wb oaord1 mpbi r1ord2 sseqtrri sstrdi wa limom pm3.2i
      mp2 oalimcl r1limwun eqeltri jctil ) ACEZABFBGEUQAAHIZJIZBACKUSURLMNZJIZB
      UTOEZURUTEZUSVAFUROEZLOEZVBAPZQURLSRZUALEZVCUBVDVEVHVCUCVFQURLUDRUEURUTUF
      ULDUGUHBVAGDVBUTTZVAGEVGVDVELTZUIVIVFVEVJQUJUKURLOUMRUTOUNRUOUP $.
  $}

  ${
    $d u v w x y z $.  $d m n u v w x y A $.  $d u U $.  $d m n u v x y V $.
    $d m n u v w F $.
    $( Value of the weak universe closure operator.  (Contributed by Mario
       Carneiro, 2-Jan-2017.) $)
    wuncval $p |- ( A e. V -> ( wUniCl ` A ) = |^| { u e. WUni | A C_ u } ) $=
      ( vx wcel cv wss cwun crab cint cvv cwunm df-wunc wceq sseq1 rabbidv elex
      inteqd c0 wne wrex wunex rabn0 sylibr intex sylib fvmptd3 ) BCEZDBDFZAFZG
      ZAHIZJBUJGZAHIZJZKLKDAMUIBNZULUNUPUKUMAHUIBUJOPRBCQUHUNSTZUOKEUHUMAHUAUQA
      BCUBUMAHUCUDUNUEUFUG $.

    $( The weak universe closure of a set contains the set.  (Contributed by
       Mario Carneiro, 2-Jan-2017.) $)
    wuncid $p |- ( A e. V -> A C_ ( wUniCl ` A ) ) $=
      ( vu wcel cv wss cwun crab cint cwunm cfv ssintub wuncval sseqtrrid ) ABD
      ACEFCGHIAAJKCAGLCABMN $.

    $( The weak universe closure of a set is a weak universe.  (Contributed by
       Mario Carneiro, 2-Jan-2017.) $)
    wunccl $p |- ( A e. V -> ( wUniCl ` A ) e. WUni ) $=
      ( vu wcel cwunm cfv cv wss cwun crab cint wuncval c0 wne wrex wunex rabn0
      ssrab2 sylibr intwun sylancr eqeltrd ) ABDZAEFACGHZCIJZKZICABLUCUEIHUEMNZ
      UFIDUDCIRUCUDCIOUGCABPUDCIQSUETUAUB $.

    $( The weak universe closure is a subset of any other weak universe
       containing the set.  (Contributed by Mario Carneiro, 2-Jan-2017.) $)
    wuncss $p |- ( ( U e. WUni /\ A C_ U ) -> ( wUniCl ` A ) C_ U ) $=
      ( vu cwun wcel wss wa cwunm cfv cv crab cint cvv ssexg ancoms wuncval syl
      wceq sseq2 intminss eqsstrd ) BDEZABFZGZAHIZACJZFZCDKLZBUDAMEZUEUHRUCUBUI
      ABDNOCAMPQUGUCCBDUFBASTUA $.

    $( The weak universe closure is idempotent.  (Contributed by Mario
       Carneiro, 2-Jan-2017.) $)
    wuncidm $p |- ( A e. V -> ( wUniCl ` ( wUniCl ` A ) ) = ( wUniCl ` A ) ) $=
      ( wcel cwunm cfv cwun wss wunccl ssid wuncss sylancl wuncid syl eqssd ) A
      BCZADEZDEZPOPFCZPPGQPGABHZPIPPJKORPQGSPFLMN $.

    wuncval2.f $e |- F = ( rec ( ( z e. _V |-> ( ( z u. U. z ) u.
      U_ x e. z ( { ~P x , U. x } u.
        ran ( y e. z |-> { x , y } ) ) ) ) , ( A u. 1o ) ) |` _om ) $.
    wuncval2.u $e |- U = U. ran F $.
    $( Our earlier expression for a containing weak universe is in fact the
       weak universe closure.  (Contributed by Mario Carneiro, 2-Jan-2017.) $)
    wuncval2 $p |- ( A e. V -> ( wUniCl ` A ) = U ) $=
      ( vm vu vv wcel cfv wss com cv cuni cun c0 vn vw cwunm cwun wunex2 wuncss
      wa syl ciun crn wfn wceq cvv cpw cpr cmpt crdg cres frfnom fneq1i fniunfv
      c1o mpbir ax-mp eqtr4i wral csuc fveq2 sseq1d weq con0 unexg mpan2 fveq1i
      1on fr0g eqtrid wuncid csn df1o2 wunccl wun0 snssd eqsstrid unssd eqsstrd
      wi simplr fvex uniex unex prex mptex iunex id unieq uneq12d preq12d preq1
      rnex pweq mpteq2dv rneqd cbviunv cbvmptv mpteq1 uneq2d iuneq12d frsucmpt2
      preq2 sylancl simpr ad3antrrr sselda ralrimiva unissb sylibr wunpw wununi
      wunelss prssd adantr wunpr fmpttd frnd iunss expcom finds2 com12 ralrimiv
      ex eqssd ) DGMZDUCNZEYMEUDMDEOUGYNEOABCDEFGHIUEDEUFUHYMEJPJQZFNZUIZYNEFUJ
      RZYQIFPUKZYQYRULYSCUMCQZYTRZSZAYTAQZUNZUUCRZUOZBYTUUCBQZUOZUPZUJZSZUIZSZU
      PZDVBSZUQPURZPUKUUOUUNUSPFUUPHUTVCJPFVAVDVEYMYPYNOZJPVFYQYNOYMUUQJPYOPMYM
      UUQUUQTFNZYNOUAQZFNZYNOZUUSVGZFNZYNOZYMJUAYOTULYPUURYNYOTFVHVIJUAVJYPUUTY
      NYOUUSFVHVIYOUVBULYPUVCYNYOUVBFVHVIYMUURUUOYNYMUUOUMMZUURUUOULYMVBVKMUVEV
      ODVBGVKVLVMUVEUURTUUPNUUOTFUUPHVNUUOUMUUNVPVQUHYMDVBYNDGVRYMVBTVSYNVTYMTY
      NYMYNDGWAZWBWCWDWEWFYMUUSPMZUVAUVDWGYMUVGUGZUVAUVDUVHUVAUGZUVCUUTUUTRZSZK
      UUTKQZUNZUVLRZUOZLUUTUVLLQZUOZUPZUJZSZUIZSZYNUVIUVGUWBUMMUVCUWBULYMUVGUVA
      WHUVKUWAUUTUVJUUSFWIZUUTUWCWJWKKUUTUVTUWCUVOUVSUVMUVNWLUVRLUUTUVQUWCWMWTW
      KWNWKCUBUUOUUSUUMUWBUBQZUWDRZSZKUWDUVOLUWDUVQUPZUJZSZUIZSFUMHUBCVJZUWFUUB
      UWJUULUWKUWDYTUWEUUAUWKWOZUWDYTWPWQUWKUWJAUWDUUFLUWDUUCUVPUOZUPZUJZSZUIUU
      LKAUWDUWIUWPKAVJZUVOUUFUWHUWOUWQUVMUUDUVNUUEUVLUUCXAUVLUUCWPWRUWQUWGUWNUW
      QLUWDUVQUWMUVLUUCUVPWSXBXCWQXDUWKAUWDYTUWPUUKUWLUWKUWOUUJUUFUWKUWNUUIUWKU
      WNBUWDUUHUPUUILBUWDUWMUUHUVPUUGUUCXJXEBUWDYTUUHXFVQXCXGXHVQWQUWDUUTULZUWF
      UVKUWJUWAUWRUWDUUTUWEUVJUWRWOZUWDUUTWPWQUWRKUWDUUTUWIUVTUWSUWRUWHUVSUVOUW
      RUWGUVRLUWDUUTUVQXFXCXGXHWQXIXKUVIUVKUWAYNUVIUUTUVJYNUVHUVAXLZUVIUVLYNOZK
      UUTVFUVJYNOUVIUXAKUUTUVIUVLUUTMZUGZUVLYNYMYNUDMZUVGUVAUXBUVFXMZUVIUUTYNUV
      LUWTXNZXTXOKUUTYNXPXQWEUVIUVTYNOZKUUTVFUWAYNOUVIUXGKUUTUXCUVOUVSYNUXCUVMU
      VNYNUXCUVLYNUXEUXFXRUXCUVLYNUXEUXFXSYAUXCUUTYNUVRUXCLUUTUVQYNUXCUVPUUTMZU
      GUVLUVPYNUXCUXDUXHUXEYBUXCUVLYNMUXHUXFYBUXCUUTYNUVPUVHUVAUXBWHXNYCYDYEWEX
      OKUUTUVTYNYFXQWEWFYKYGYHYIYJJPYPYNYFXQWDYL $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Tarski classes
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c Tarski $. $( The class of Tarski classes. $)

  $( Extend class definition to include the class of all Tarski classes. $)
  ctsk $a class Tarski $.

  ${
    $d y z w $.
    $( The class of all Tarski classes.  Tarski classes is a phrase coined by
       Grzegorz Bancerek in his article _Tarski's Classes and Ranks_, Journal
       of Formalized Mathematics, Vol 1, No 3, May-August 1990.  A Tarski class
       is a set whose existence is ensured by Tarski's Axiom A (see ~ ax-groth
       and the equivalent axioms).  Axiom A was first presented in Tarski's
       article _Ueber unerreichbare Kardinalzahlen_.  Tarski introduced Axiom A
       to allow reasoning with inaccessible cardinals in ZFC. Later,
       Grothendieck introduced the concept of (Grothendieck) universes and
       showed they were exactly transitive Tarski classes.  (Contributed by FL,
       30-Dec-2010.) $)
    df-tsk $a |- Tarski = { y | ( A. z e. y ( ~P z C_ y
      /\ E. w e. y ~P z C_ w ) /\ A. z e. ~P y ( z ~~ y \/ z e. y ) ) } $.
  $}

  ${
    $d A x $.  $d T w x y z $.
    $( Properties of a Tarski class.  (Contributed by FL, 30-Dec-2010.) $)
    eltskg $p |- ( T e. V -> ( T e. Tarski <-> ( A. z e. T ( ~P z C_ T
      /\ E. w e. T ~P z C_ w ) /\ A. z e. ~P T ( z ~~ T \/ z e. T ) ) ) ) $=
      ( vy cv cpw wss wrex wa wral cen wbr wcel ctsk wceq sseq2 rexeq anbi12d
      wo raleqbi1dv pweq breq2 eleq2 orbi12d raleqbidv df-tsk elab2g ) AFZGZEFZ
      HZUJBFHZBUKIZJZAUKKZUIUKLMZUIUKNZTZAUKGZKZJUJCHZUMBCIZJZACKZUICLMZUICNZTZ
      ACGZKZJECODUKCPZUPVEVAVJUOVDAUKCVKULVBUNVCUKCUJQUMBUKCRSUAVKUSVHAUTVIUKCU
      BVKUQVFURVGUKCUILUCUKCUIUDUEUFSEABUGUH $.

    $( Properties of a Tarski class.  (Contributed by FL, 30-Dec-2010.)
       (Revised by Mario Carneiro, 20-Sep-2014.) $)
    eltsk2g $p |- ( T e. V -> ( T e. Tarski <-> ( A. z e. T ( ~P z C_ T
      /\ ~P z e. T ) /\ A. z e. ~P T ( z ~~ T \/ z e. T ) ) ) ) $=
      ( vw wcel ctsk cv cpw wss wrex wa wral cen wbr wo eltskg nfra1 weq r19.26
      wi pweq sseq1d rspccva adantlr elpw ssel biimtrrid syl rexlimdva ralimdaa
      vpwex 3imtr4i ssid sseq2 rspcev mpan2 anim2i ralimi impbii anbi1i bitrdi
      imdistani ) BCEBFEAGZHZBIZVDDGZIZDBJZKZABLZVCBMNVCBEZOABHLZKVEVDBEZKZABLZ
      VLKADBCPVJVOVLVJVOVEABLZVHABLZKVPVMABLZKVJVOVPVQVRVPVHVMABVEABQVPVKKZVGVM
      DBVSVFBEZKVFHZBIZVGVMTVPVTWBVKVEWBAVFBADRVDWABVCVFUAUBUCUDVGVDWAEWBVMVDVF
      AUKUEWABVDUFUGUHUIUJVBVEVHABSVEVMABSULVNVIABVMVHVEVMVDVDIZVHVDUMVGWCDVDBV
      FVDVDUNUOUPUQURUSUTVA $.

    $( First axiom of a Tarski class.  The subsets of an element of a Tarski
       class belong to the class.  (Contributed by FL, 30-Dec-2010.)  (Proof
       shortened by Mario Carneiro, 20-Sep-2014.) $)
    tskpwss $p |- ( ( T e. Tarski /\ A e. T ) -> ~P A C_ T ) $=
      ( vx vy ctsk wcel cv cpw wss wral wrex wa cen wbr eltskg ibi simpld simpl
      wo ralimi syl wceq pweq sseq1d rspccva sylan ) BEFZCGZHZBIZCBJZABFAHZBIZU
      GUJUIDGIDBKZLZCBJZUKUGUPUHBMNUHBFSCBHJZUGUPUQLCDBEOPQUOUJCBUJUNRTUAUJUMCA
      BUHAUBUIULBUHAUCUDUEUF $.

    $( Second axiom of a Tarski class.  The powerset of an element of a Tarski
       class belongs to the class.  (Contributed by FL, 30-Dec-2010.)  (Proof
       shortened by Mario Carneiro, 20-Sep-2014.) $)
    tskpw $p |- ( ( T e. Tarski /\ A e. T ) -> ~P A e. T ) $=
      ( vx ctsk wcel cv cpw wral wss wa cen wbr eltsk2g ibi simpld simpr ralimi
      wo syl wceq pweq eleq1d rspccva sylan ) BDEZCFZGZBEZCBHZABEAGZBEZUEUGBIZU
      HJZCBHZUIUEUNUFBKLUFBERCBGHZUEUNUOJCBDMNOUMUHCBULUHPQSUHUKCABUFATUGUJBUFA
      UAUBUCUD $.

    $( Third axiom of a Tarski class.  A subset of a Tarski class is either
       equipotent to the class or an element of the class.  (Contributed by FL,
       30-Dec-2010.)  (Revised by Mario Carneiro, 20-Sep-2014.) $)
    tsken $p |- ( ( T e. Tarski /\ A C_ T ) -> ( A ~~ T \/ A e. T ) ) $=
      ( vx vy ctsk wcel cv cen wbr wo cpw wral wss wrex wa eltskg simprd elpw2g
      ibi biimpar wceq breq1 eleq1 orbi12d rspccva syl2an2r ) BEFZCGZBHIZUHBFZJ
      ZCBKZLZABMZAULFZABHIZABFZJZUGUHKZBMUSDGMDBNOCBLZUMUGUTUMOCDBEPSQUGUOUNABE
      RTUKURCAULUHAUAUIUPUJUQUHABHUBUHABUCUDUEUF $.
  $}

  $( The empty set is a (transitive) Tarski class.  (Contributed by FL,
     30-Dec-2010.) $)
  0tsk $p |- (/) e. Tarski $=
    ( vx c0 ctsk wcel cv cpw wss wa wral cen wbr wo ral0 wceq elsni enref breq1
    csn 0ex cvv mpbiri orcd syl pw0 eleq2s rgen wb eltsk2g ax-mp mpbir2an ) BCD
    ZAEZFZBGUMBDHZABIZULBJKZULBDZLZABFZIZUNAMURAUSURULBRZUSULVADULBNZURULBOVBUP
    UQVBUPBBJKBSPULBBJQUAUBUCUDUEUFBTDUKUOUTHUGSABTUHUIUJ $.

  $( An element of a Tarski class is strictly dominated by the class.  JFM
     CLASSES2 th. 1.  (Contributed by FL, 22-Feb-2011.)  (Revised by Mario
     Carneiro, 18-Jun-2013.) $)
  tsksdom $p |- ( ( T e. Tarski /\ A e. T ) -> A ~< T ) $=
    ( wcel cpw csdm wbr ctsk cdom canth2g wa wss simpl tskpwss ssdomg sdomdomtr
    sylc syl2an2 ) ABCZAADZEFBGCZSBHFZABEFABITRJTSBKUATRLABMSBGNPASBOQ $.

  $( A part of a Tarski class strictly dominated by the class is an element of
     the class.  JFM CLASSES2 th. 2.  (Contributed by FL, 22-Feb-2011.)  (Proof
     shortened by Mario Carneiro, 20-Sep-2014.) $)
  tskssel $p |- ( ( T e. Tarski /\ A C_ T /\ A ~< T ) -> A e. T ) $=
    ( ctsk wcel wss csdm wbr w3a cen wn sdomnen 3ad2ant3 tsken 3adant3 ord mpd
    wo ) BCDZABEZABFGZHZABIGZJZABDZTRUCSABKLUAUBUDRSUBUDQTABMNOP $.

  $( The subsets of an element of a Tarski class belong to the class.
     (Contributed by FL, 30-Dec-2010.)  (Revised by Mario Carneiro,
     18-Jun-2013.) $)
  tskss $p |- ( ( T e. Tarski /\ A e. T /\ B C_ A ) -> B e. T ) $=
    ( ctsk wcel wss wa cpw wb elpw2g adantl tskpwss sseld sylbird 3impia ) CDEZ
    ACEZBAFZBCEZPQGZRBAHZEZSQUBRIPBACJKTUACBACLMNO $.

  $( The intersection of two elements of a Tarski class belongs to the class.
     (Contributed by FL, 30-Dec-2010.)  (Proof shortened by Mario Carneiro,
     20-Sep-2014.) $)
  tskin $p |- ( ( T e. Tarski /\ A e. T ) -> ( A i^i B ) e. T ) $=
    ( ctsk wcel cin wss inss1 tskss mp3an3 ) CDEACEABFZAGKCEABHAKCIJ $.

  $( A singleton of an element of a Tarski class belongs to the class.  JFM
     CLASSES2 th. 2 (partly).  (Contributed by FL, 22-Feb-2011.)  (Revised by
     Mario Carneiro, 18-Jun-2013.) $)
  tsksn $p |- ( ( T e. Tarski /\ A e. T ) -> { A } e. T ) $=
    ( ctsk wcel cpw csn tskpw wss snsspw tskss mp3an3 syldan ) BCDZABDAEZBDZAFZ
    BDZABGMOPNHQAINPBJKL $.

  $( A transitive element of a Tarski class is a part of the class.  JFM
     CLASSES2 th. 8.  (Contributed by FL, 22-Feb-2011.)  (Revised by Mario
     Carneiro, 20-Sep-2014.) $)
  tsktrss $p |- ( ( T e. Tarski /\ Tr A /\ A e. T ) -> A C_ T ) $=
    ( ctsk wcel wtr w3a cpw wss simp2 dftr4 sylib tskpwss 3adant2 sstrd ) BCDZA
    EZABDZFZAAGZBRPASHOPQIAJKOQSBHPABLMN $.

  $( If an element of a Tarski class is an ordinal number, its successor is an
     element of the class.  JFM CLASSES2 th. 6 (partly).  (Contributed by FL,
     22-Feb-2011.)  (Proof shortened by Mario Carneiro, 20-Sep-2014.) $)
  tsksuc $p |- ( ( T e. Tarski /\ A e. On /\ A e. T ) -> suc A e. T ) $=
    ( ctsk wcel con0 w3a cpw csuc wss simp1 tskpw cuni word wceq eloni 3ad2ant2
    3adant2 ordunisuc eqimss 3syl sspwuni sylibr tskss syl3anc ) BCDZAEDZABDZFZ
    UEAGZBDZAHZUIIZUKBDUEUFUGJUEUGUJUFABKQUHUKLZAIZULUHAMZUMANUNUFUEUOUGAOPARUM
    ASTUKAUAUBUIUKBUCUD $.

  ${
    $d T x $.
    $( A nonempty Tarski class contains the empty set.  (Contributed by FL,
       30-Dec-2010.)  (Revised by Mario Carneiro, 18-Jun-2013.) $)
    tsk0 $p |- ( ( T e. Tarski /\ T =/= (/) ) -> (/) e. T ) $=
      ( vx c0 wne ctsk wcel cv wex wi wss 0ss tskss mp3an3 expcom exlimiv sylbi
      n0 impcom ) ACDZAEFZCAFZSBGZAFZBHTUAIZBAQUCUDBTUCUATUCCUBJUAUBKUBCALMNOPR
      $.
  $}

  $( One is an element of a nonempty Tarski class.  (Contributed by FL,
     22-Feb-2011.) $)
  tsk1 $p |- ( ( T e. Tarski /\ T =/= (/) ) -> 1o e. T ) $=
    ( ctsk wcel c0 wne wa c1o csn df1o2 tsk0 tsksn syldan eqeltrid ) ABCZADEZFG
    DHZAINODACPACAJDAKLM $.

  $( Two is an element of a nonempty Tarski class.  (Contributed by FL,
     22-Feb-2011.)  (Proof shortened by Mario Carneiro, 20-Sep-2014.) $)
  tsk2 $p |- ( ( T e. Tarski /\ T =/= (/) ) -> 2o e. T ) $=
    ( ctsk wcel c0 wne c1o c2o tsk1 wa csuc df-2o con0 1on tsksuc mp3an2 syldan
    eqeltrid ) ABCZADEFACZGACAHRSIGFJZAKRFLCSTACMFANOQP $.

  $( If a Tarski class is not empty, it has more than two elements.
     (Contributed by FL, 22-Feb-2011.) $)
  2domtsk $p |- ( ( T e. Tarski /\ T =/= (/) ) -> 2o ~< T ) $=
    ( ctsk wcel c0 wne c2o csdm wbr tsk2 tsksdom syldan ) ABCADEFACFAGHAIFAJK
    $.

  ${
    $d T x y $.
    $( A nonempty Tarski class is infinite, because it contains all the finite
       levels of the cumulative hierarchy.  (This proof does not use
       ~ ax-inf .)  (Contributed by Mario Carneiro, 24-Jun-2013.) $)
    tskr1om $p |- ( ( T e. Tarski /\ T =/= (/) ) -> ( R1 " _om ) C_ T ) $=
      ( vy vx ctsk wcel c0 wne wa cr1 com cima cv cfv wceq wrex wi fveq2 eleq1d
      csuc con0 r10 tsk0 eqeltrid cpw tskpw nnon r1suc imbitrrid adantrd finds2
      syl expd eleq1 imbi2d syl5ibcom rexlimiv wfun wfn r1fnon fnfun ax-mp mpan
      fvelima syl11 ssrdv ) ADEZAFGZHZBIJKZACLZIMZBLZNZCJOZVHVLAEZVLVIEZVMVHVOP
      ZCJVJJEVHVKAEZPVMVQVRFIMZAEVLIMZAEZVLSZIMZAEZVHCBVJFNVKVSAVJFIQRVJVLNVKVT
      AVJVLIQRVJWBNVKWCAVJWBIQRVHVSFAUAAUBUCVLJEZVFWAWDPVGWEVFWAWDVFWAHWDWEVTUD
      ZAEVTAUEWEWCWFAWEVLTEWCWFNVLUFVLUGUKRUHULUIUJVMVRVOVHVKVLAUMUNUOUPIUQZVPV
      NITURWGUSTIUTVACVLJIVCVBVDVE $.

    $( A nonempty Tarski class contains the whole finite cumulative hierarchy.
       (This proof does not use ~ ax-inf .)  (Contributed by NM,
       22-Feb-2011.) $)
    tskr1om2 $p |- ( ( T e. Tarski /\ T =/= (/) ) -> U. ( R1 " _om ) C_ T ) $=
      ( vy vx ctsk wcel c0 wne wa cr1 com cima cuni cv wrex eluni2 wss wtr con0
      wi syld cfv wceq wfun wfn r1fnon fnfun ax-mp fvelima mpan r1tr treq mpbii
      rexlimivw trss 3syl adantl sseld tskss 3exp adantr imp rexlimdva biimtrid
      tskr1om ssrdv ) ADEZAFGZHZBIJKZLZABMZVJEVKCMZEZCVINVHVKAEZCVKVIOVHVMVNCVI
      VHVLVIEZHVMVKVLPZVNVOVMVPSZVHVOVKIUAZVLUBZBJNZVLQZVQIUCZVOVTIRUDWBUERIUFU
      GBVLJIUHUIVSWABJVSVRQWAVKUJVRVLUKULUMVLVKUNUOUPVHVOVPVNSZVHVOVLAEZWCVHVIA
      VLAVDUQVFWDWCSVGVFWDVPVNVLVKAURUSUTTVATVBVCVE $.
  $}

  $( A nonempty Tarski class is infinite.  (Contributed by FL, 22-Feb-2011.) $)
  tskinf $p |- ( ( T e. Tarski /\ T =/= (/) ) -> _om ~<_ T ) $=
    ( ctsk wcel wne com cr1 cima cen wbr cdom con0 cvv wf1 wss r111 omsson omex
    c0 wa f1imaen mp2an ensymi simpl tskr1om ssdomg sylc endomtr sylancr ) ABCZ
    ARDZSZEFEGZHIULAJIZEAJIULEKLFMEKNULEHIOPKLEFQTUAUBUKUIULANUMUIUJUCAUDULABUE
    UFEULAUGUH $.

  $( If ` A ` and ` B ` are members of a Tarski class, their unordered pair is
     also an element of the class.  JFM CLASSES2 th. 3 (partly).  (Contributed
     by FL, 22-Feb-2011.)  (Proof shortened by Mario Carneiro, 20-Jun-2013.) $)
  tskpr $p |- ( ( T e. Tarski /\ A e. T /\ B e. T )
    -> { A , B } e. T ) $=
    ( ctsk wcel w3a cpr wss csdm wbr simp1 prssi 3adant1 com cdom prfi isfinite
    wa cfn mpbi c0 ne0i tskinf sylan2 sdomdomtr sylancr 3adant3 tskssel syl3anc
    wne ) CDEZACEZBCEZFUKABGZCHZUNCIJZUNCEUKULUMKULUMUOUKABCLMUKULUPUMUKULRUNNI
    JZNCOJZUPUNSEUQABPUNQTULUKCUAUJURCAUBCUCUDUNNCUEUFUGUNCUHUI $.

  $( If ` A ` and ` B ` are members of a Tarski class, their ordered pair is
     also an element of the class.  JFM CLASSES2 th. 4.  (Contributed by FL,
     22-Feb-2011.) $)
  tskop $p |- ( ( T e. Tarski /\ A e. T /\ B e. T )
    -> <. A , B >. e. T ) $=
    ( ctsk wcel w3a cop csn cpr dfopg 3adant1 simp1 tsksn 3adant3 tskpr syl3anc
    wceq eqeltrd ) CDEZACEZBCEZFZABGZAHZABIZIZCTUAUCUFQSABCCJKUBSUDCEZUECEUFCES
    TUALSTUGUAACMNABCOUDUECOPR $.

  ${
    $d A x y z $.  $d B x y z $.  $d T x y z $.
    $( A Cartesian product of two parts of a Tarski class is a part of the
       class.  (Contributed by FL, 22-Feb-2011.)  (Proof shortened by Mario
       Carneiro, 20-Jun-2013.) $)
    tskxpss $p |- ( ( T e. Tarski /\ A C_ T /\ B C_ T )
    -> ( A X. B ) C_ T ) $=
      ( vz vx vy ctsk wcel wss cxp wa cv cop wceq wrex elxp2 w3a tskop eleq1a
      wi syl 3expib rexlimdvv biimtrid ssrdv xpss12 sstr expcom syl2im 3impib )
      CGHZACIZBCIZABJZCIZUKCCJZCIZULUMKUNUPIZUOUKDUPCDLZUPHUSELZFLZMZNZFCOECOUK
      USCHZEFUSCCPUKVCVDEFCCUKUTCHZVACHZVCVDTZUKVEVFQVBCHVGUTVACRVBCUSSUAUBUCUD
      UEACBCUFURUQUOUNUPCUGUHUIUJ $.
  $}

  ${
    $d T y $.
    $( A Tarski class is well-orderable.  (Contributed by Mario Carneiro,
       20-Jun-2013.) $)
    tskwe2 $p |- ( T e. Tarski -> T e. dom card ) $=
      ( vy ctsk wcel cv csdm wbr cpw crab wss ccrd wral elpwi tskssel 3exp syl5
      cdm wi ralrimiv rabss sylibr tskwe mpdan ) ACDZBEZAFGZBAHZIAJZAKQDUDUFUEA
      DZRZBUGLUHUDUJBUGUEUGDUEAJZUDUJUEAMUDUKUFUIUEANOPSUFBUGATUABACUBUC $.
  $}

  ${
    $d A t z $.
    $( The intersection of a collection of Tarski classes is a Tarski class.
       (Contributed by FL, 17-Apr-2011.)  (Proof shortened by Mario Carneiro,
       20-Sep-2014.) $)
    inttsk $p |- ( ( A C_ Tarski /\ A =/= (/) ) -> |^| A e. Tarski ) $=
      ( vz vt ctsk wss wa wcel cpw wral cen wbr syl2anc ralrimiva sylibr elint2
      cv wo wn cdom cvv wne cint simpll sselda elinti imp adantll tskpwss ssint
      c0 tskpw vpwex elpwi wrex rexnal intex bilani ad2antrr simplr ssdomg sylc
      jca vex intss1 ad2antrl mpsyl simprr simplll simprl sseldd sstrd ord mt3d
      tsken ensymd domentr sbth rexlimdvaa biimtrrid con1d imbitrrdi wb eltsk2g
      orrd sylan2 syl mpbir2and ) ADEZAUJUAZFZAUBZDGZBPZHZWKEZWNWKGZFZBWKIZWMWK
      JKZWMWKGZQZBWKHZIZWJWQBWKWJWTFZWOWPXDWNCPZEZCAIWOXDXFCAXDXEAGZFZXEDGZWMXE
      GZXFXDADXEWHWIWTUCUDZWTXGXJWJWTXGXJWMAXEUEUFUGZWMXEUHLMCWNAUINXDWNXEGZCAI
      WPXDXMCAXHXIXJXMXKXLWMXEUKLMCWNABULONVBMWJXABXBWMXBGWJWMWKEZXAWMWKUMWJXNF
      ZWSWTXOWSRXJCAIZWTXOXPWSXPRXJRZCAUNXOWSXJCAUOXOXQWSCAXOXGXQFZFZWMWKSKZWKW
      MSKZWSXSWKTGZXNXTWJYBXNXRWIYBWHAUPUQZURWJXNXRUSZWMWKTUTVAXSWKXESKZXEWMJKY
      AXETGXSWKXEEZYECVCXGYFXOXQXEAVDVEZWKXETUTVFXSWMXEXSWMXEJKZXJXOXGXQVGXSYHX
      JXSXIWMXEEYHXJQXSADXEWHWIXNXRVHXOXGXQVIVJXSWMWKXEYDYGVKWMXEVNLVLVMVOWKXEW
      MVPLWMWKVQLVRVSVTCWMABVCOWAWDWEMWJYBWLWRXCFWBYCBWKTWCWFWG $.
  $}

  ${
    $d A w x y z $.
    $( ` ( R1 `` A ) ` for ` A ` a strongly inaccessible cardinal is equipotent
       to ` A ` .  (Contributed by Mario Carneiro, 6-Jun-2013.) $)
    inar1 $p |- ( A e. Inacc -> ( R1 ` A ) ~~ A ) $=
      ( vx vy vz wcel cr1 cfv cdom wbr con0 wceq syl syl2anc wral wa csdm wi c0
      cvv wss vw cina cen cxp cv ciun cwina inawina winaon winalim r1lim onelon
      wlim sylan csuc eleq1 breq1d imbi12d weq wne ne0i 0sdomg imbitrrid breq1i
      fveq2 r10 imbitrrdi 3syl wtr word eloni ordtr trsuc adantl ccrd cpw r1suc
      ex fvex cardid ensymi pwen ax-mp eqbrtrdi winacard eleq2d cardsdom bitr3d
      wb sylancr ccf elina simp3bi pweq rspccv sylbird imp ensdomtr syl2an expr
      imim12d cun vex mpan nfcv nfiu1 nfbr iunex ssiun2 ssdomg endomtr vtoclgaf
      wel mpsyl iundom mp2an mp2 domtr com domentr eqbrtrd ad2antlr wn wrex wfn
      wf sylibr eleq1d ralimdva impr sseq2d biimtrid ad2antrl sylibd iunon mprg
      wo a1i onelss mpd rgen ssun2 xpdom2 xpdom1 limomss sstrdi infxpidm eleq1a
      unex ssun1 ordirr nsyli ad2ant2r simpll wex ccom cres limord cardf r1fnon
      elon dffn2 mpbi fco onss fssres ffn simpr simplll syl12anc biimpd embantd
      ontr1 fvres fvco3 eqtrd sylibrd ffnfv sylanbrc eleq2 biimpa eliun onelssi
      cardon reximdva syl5 expdimp ralrimiv wfun ffun resfunexg rexbidv ralbidv
      feq1 fveq1 anbi12d spcev syl6an cfflb simp2bi sseq1d ontri1 eqcom ordequn
      syld mt2d sylancl mtord sylc sylsyld iunss unssd cif iuneq1 uneq12d 0elon
      elimel elexi onun2i dedth adantr onsseleq mpbid orcomd ord iscard simprbi
      id breq1 domsdomtr exp43 com4l tfinds2 impd mpcom sdomdom winainf infxpen
      ralrimiva cdm fdmi eleqtrrdi onssr1 sbth ) AUBEZAFGZAHIZAVUFHIZVUFAUCIVUE
      VUFAAUDZHIVUIAUCIZVUGVUEVUFBABUEZFGZUFZVUIHVUEAJEZAUMZVUFVUMKVUEAUGEZVUNA
      UHZAUIZLZVUEVUPVUOVUQAUJLBAJUKMVUEVUNVULAHIZBANVUMVUIHIVUSVUEVUTBAVUEVUKA
      EZOZVULAPIZVUTVUKJEZVVBVVCVUEVUNVVAVVDVUSAVUKULUNVVDVUEVVAVVCVVAVVCQRAEZR
      FGZAPIZQZCUEZAEZVVIFGZAPIZQZVVIUOZAEZVVNFGZAPIZQZVUEBCVUKRKZVVAVVEVVCVVGV
      UKRAUPVVSVULVVFAPVUKRFVEUQURBCUSZVVAVVJVVCVVLVUKVVIAUPVVTVULVVKAPVUKVVIFV
      EUQURVUKVVNKZVVAVVOVVCVVQVUKVVNAUPVWAVULVVPAPVUKVVNFVEUQURVUEVUPVUNVVHVUQ
      VURVUNVVERAPIZVVGVVEVWBVUNARUTZARVAAJVBVCVVFRAPVFVDVGVHVVIJEZVUEVVMVVRQVW
      DVUEOVVOVVJVVLVVQVUEVVOVVJQZVWDVUEVUNAVIZVWEVUSVUNAVJZVWFAVKZAVLLVWFVVOVV
      JAVVIVMVRVHVNVWDVUEVVLVVQVWDVVPVVKVOGZVPZUCIVWJAPIZVVQVUEVVLOVWDVVPVVKVPZ
      VWJUCVVIVQVVKVWIUCIZVWLVWJUCIVWIVVKVVKVVIFVSZVTWAZVVKVWIWBWCWDVUEVVLVWKVU
      EVVLVWIAEZVWKVUEVUPVWPVVLWIVUQVUPVWIAVOGZEZVWPVVLVUPVWQAVWIAWEZWFVUPVVKSE
      ZVUNVWRVVLWIZVWNVURVVKASJWGZWJWHLVUEDUEZVPZAPIZDANZVWPVWKQVUEVWCAWKGZAKZV
      XFDAWLZWMVXEVWKDVWIAVXCVWIKVXDVWJAPVXCVWIWNUQWOLWPWQVVPVWJAWRWSWTXAVRVVAV
      UKUMZVUEVVMCVUKNZVVCVVAVXJVUEVXKVVCVVAVXJOZVUEVXKOZOZVULVUKCVUKVWIUFZXBZH
      IZVXPAPIZVVCVXJVXQVVAVXMVXJVULDVUKVXCFGZUFZVXPHVUKSEZVXJVULVXTKBXCZDVUKSU
      KXDVXJVXTVUKVXOUDZHIZVYCVXPHIZVXTVXPHIVYAVXSVXOHIZDVUKNVYDVYBVYFDVUKVVKVX
      OHIZVYFCVXCVUKCVXCXECVXSVXOHCVXSXECHXECVUKVWIXFXGCDUSVVKVXSVXOHVVIVXCFVEU
      QCBXMZVWMVWIVXOHIZVYGVWOVXOSEVYHVWIVXOTVYICVUKVWIVYBVVKVOVSXHZCVUKVWIXIVW
      IVXOSXJXNVVKVWIVXOXKWJXLUUADVUKVXOVXSSXOXPVXJVYCVXPVXPUDZHIZVYKVXPUCIZVYE
      VYCVUKVXPUDZHIZVYNVYKHIZVYLVXOVXPHIZVYOVXPSEZVXOVXPTVYQVUKVXOVYBVYJUUIZVX
      OVUKUUBVXOVXPSXJXQVXOVXPVUKVYBUUCWCVUKVXPHIZVYPVYRVUKVXPTVYTVYSVUKVXOUUJZ
      VUKVXPSXJXQVUKVXPVXPVYSUUDWCVYCVYNVYKXRXPVXJXSVXPHIZVYMVYRVXJXSVXPTWUBVYS
      VXJXSVUKVXPVUKUUEWUAUUFXSVXPSXJXNVXPUUGLVYCVYKVXPXTWJVXTVYCVXPXRWJYAYBVXN
      VXPAEZVXRVXNVXPAKZYCWUCVXNWUDAVUKKZAVXOKZVVAVUEWUEYCZVXJVXKVVAVUEWUGVVAWU
      EAAEZVUEVUKAAUUHVUEVUNVWGWUHYCVUSVWHAUUKVHUULWQUUMVXNWUFVVAVVAVXJVXMUUNZV
      XNWUFAVUKTZVVAYCZVXNWUFVXGVUKTZWUJVXNWUFVUKAUAUEZYFZVXCVVIWUMGZTZCVUKYDZD
      ANZOZUAUUOZWULVXNVUKAVOFUUPZVUKUUQZYFZWUFVXCVVIWVBGZTZCVUKYDZDANZWUTVXNWV
      BVUKYEZWVDAEZCVUKNZWVCVXNVVDVUKJWVBYFZWVHVXJVVDVVAVXMVXJVUKVJZVVDVUKUURVU
      KVYBUVAYGZYBZVVDJJWVAYFZVUKJTWVKSJVOYFJSFYFZWVOUUSFJYEWVPUUTJFUVBUVCZJSJV
      OFUVDXPZVUKUVEJJVUKWVAUVFWJVUKJWVBUVGVHVXLVUEVXKWVJVXLVUEOZVVMWVICVUKWVSV
      YHOZVVMVWPWVIWVTVVJVVLVWPWVTVUNVYHVVAVVJVUEVUNVXLVYHVUSYBZWVSVYHUVHVVAVXJ
      VUEVYHUVIVUNVYHVVAOVVJVVIVUKAUVMWQUVJWVTVVLVWPWVTVWRVVLVWPWVTVWTVUNVXAVWN
      WWAVXBWJWVTVWQAVWIVUEVWQAKZVXLVYHVUEVUPWWBVUQVWSLZYBWFWHUVKUVLZWVTWVDVWIA
      WVSVVDVYHWVDVWIKVXJVVDVVAVUEWVMYBVVDVYHOZWVDVVIWVAGZVWIVYHWVDWWFKVVDVVIVU
      KWVAUVNVNWWEWVPVWDWWFVWIKWVQVUKVVIULJSVVIVOFUVOWJUVPZUNYHUVQYIYJCVUKAWVBU
      VRUVSVXNVVDWUFWVGQWVNVVDWUFWVGVVDWUFOWVFDAVVDWUFVXCAEZWVFWUFWWHOVXCVXOEZV
      VDWVFWUFWWHWWIAVXOVXCUVTUWAWWIVXCVWIEZCVUKYDVVDWVFCVXCVUKVWIUWBVVDWWJWVEC
      VUKWWJWVEWWEVXCVWITVWIVXCVVKUWDZUWCWWEWVDVWIVXCWWGYKVCUWEYLUWFUWGUWHVRLWU
      SWVCWVGOUAWVBWVAUWIZVYAWVBSEWVOWWLWVRJJWVAUWJWCVYBWVAVUKSUWKXPWUMWVBKZWUN
      WVCWURWVGVUKAWUMWVBUWNWWMWUQWVFDAWWMWUPWVECVUKWWMWUOWVDVXCVVIWUMWVBUWOYKU
      WLUWMUWPUWQUWRVXNVUNVVDWUTWULQVUEVUNVXLVXKVUSYMZWVNDCAVUKUAUWSMUXEVUEWULW
      UJWIVXLVXKVUEVXGAVUKVUEVWCVXHVXFVXIUWTUXAYMYNVXNVUNVVDWUJWUKWIWWNWVNAVUKU
      XBMYNUXFVXNVVDVXOJEZWUDWUEWUFYQZQWVNVWIJEZWWOCVUKVYAWWQCVUKNWWOVYBCVUKVWI
      SYOXDWWQVYHWWKYRYPWUDAVXPKZVVDWWOOWWPVXPAUXCVVDWVLVXOVJWWRWWPQWWOVUKVKVXO
      VKAVUKVXOUXDWSYLUXGUXHVXNWUDWUCVXNWUCWUDVXNVXPATZWUCWUDYQZVXNVUKVXOAVXNVU
      NVVAVUKATWWNWUIAVUKYSUXIVXNVWIATZCVUKNZVXOATVXLVUEVXKWXBWVSVVMWXACVUKWVTV
      UNVVMVWPWXAWWAWWDAVWIYSUXJYIYJCVUKVWIAUXKYGUXLVXLVXPJEZVUNWWSWWTWIVXMVXJW
      XCVVAVXJVVDWXCWVMVVDWXCVVDVUKRUXMZCWXDVWIUFZXBZJEVUKRVUKWXDKZVXPWXFJWXGVU
      KWXDVXOWXEWXGUYHCVUKWXDVWIUXNUXOYHWXDWXEVUKRJUXPUXQZWWQWXEJEZCWXDWXDSEWWQ
      CWXDNWXIWXDJWXHUXRCWXDVWISYOXDWWQVVIWXDEWWKYRYPUXSUXTLVNVUEVUNVXKVUSUYAVX
      PAUYBWSUYCUYDUYEYTVXNWWBVXCAPIZDANZWUCVXRQVUEWWBVXLVXKWWCYMWWBVUNWXKDAUYF
      UYGWXJVXRDVXPAVXCVXPAPUYIWOVHYTVULVXPAUYJMUYKUYLUYMUYNUYOVULAUYPLUYSBAAVU
      LJXOMYAVUEVUNXSATZVUJVUSVUEVUPWXLVUQAUYQLAUYRMVUFVUIAXTMVUFSEVUEAVUFTZVUH
      AFVSVUEVUPAFUYTZEWXMVUQVUPAJWXNVURJSFWVQVUAVUBAVUCVHAVUFSXJXNVUFAVUDM $.
  $}

  $( Alternate proof of ~ r1om , shorter as a consequence of ~ inar1 , but
     requiring AC. (Contributed by Mario Carneiro, 27-May-2013.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  r1omALT $p |- ( R1 ` _om ) ~~ _om $=
    ( com cina wcel cr1 cfv cen wbr omina inar1 ax-mp ) ABCADEAFGHAIJ $.

  ${
    $d A w x y z $.
    $( Any set must be at least as large as the cofinality of its rank, because
       the ranks of the elements of ` A ` form a cofinal map into
       ` ( rank `` A ) ` .  (Contributed by Mario Carneiro, 27-May-2013.) $)
    rankcf $p |- -. A ~< ( cf ` ( rank ` A ) ) $=
      ( vx vy vw vz crnk cfv c0 wceq con0 wrex wcel wa ccf csdm wbr cdom c1o wi
      syl cv csuc cvv wlim w3o wn rankon onzsl sdom0 fveq2 eqtrdi breq2d mtbiri
      mpbi cf0 cfsuc sylan9eqr wne nsuceq0 neeq1 mpbiri cr1 cdm r1fnon eleqtrri
      0elon fndmi rankonid necon3i cima cuni wb rankvaln necon1ai 0sdom1dom vex
      breq2 0sdom bitr3i vtoclbg mpbird eqbrtrd rexlimiva domnsym csn cab nlim0
      adantl wss limeq r1elssi sselda ranksnb rankelb limsuc sylibd imp eqeltrd
      con4i eleq1a rexlimdva abssdv ciun vsnex dfiun2 eqtr3i snwf 3syl abrexexg
      iunid fveq2i eleq1 sseq1 r1elss eqtr3id fvex abrexco unieqi eqtri eqtr2di
      rankuni2b cfslb mpd3an23 2fveq3 breq12 mpdan rexeq abbidv mpancom imbi12d
      cmpt crn eqid rnmpt ccrd wfo cfon sdomdom ondomen sylancr fnmpti fodomnum
      wfn dffn4 mpisyl eqbrtrrid vtoclg domtr syl6an pm2.01d 3jaoi ax-mp ) AFGZ
      HIZUUMBUAZUBZIZBJKZUUMUCLZUUMUDZMZUEZAUUMNGZOPZUFZUUMJLUVBAUGBUUMUHUNUUNU
      VEUURUVAUUNUVDAHOPAUIUUNUVCHAOUUNUVCHNGHUUMHNUJUOUKULUMUURUVCAQPZUVEUUQUV
      FBJUUOJLZUUQMUVCRAQUUQUVGUVCUUPNGRUUMUUPNUJUUOUPUQUUQRAQPZUVGUUQUUMHURZUV
      HUUQUVIUUPHURUUOUSUUMUUPHUTVAUVIUVHAHURZAHUUMHAHIUUMHFGZHAHFUJHVBVCZLUVKH
      IHJUVLVFJVBVDVGVEHVHUNUKVIUVIAVBJVJVKZLZUVHUVJVLUVNUUMHAVMZVNRCUAZQPZUVPH
      URZUVHUVJCAUVMUVPARQVQUVPAHUTUVQHUVPOPUVRUVPVOUVPCVPVRVSVTTWATWHWBWCUVCAW
      DZTUUTUVEUUSUUTUVDUUTUVCDUAZUUOWEZFGZIZBAKZDWFZQPZUVDUWEAQPZUVEUUTUWEUUMW
      IUWEVKZUUMIZUWFUUTUWDDUUMUUTUWCUVTUUMLZBAUUTUUOALZMZUWBUUMLUWCUWJSUWLUWBU
      UOFGZUBZUUMUWLUUOUVMLZUWBUWNIUUTAUVMUUOUUTUVNAUVMWIUVNUUTUVNUFUUNUUTUFUVO
      UUNUUTHUDWGUUMHWJUMTWSZAWKZTWLUUOWMTUUTUWKUWNUUMLZUUTUWKUWMUUMLZUWRUUTUVN
      UWKUWSSUWPUUOAWNTUUMUWMWOWPWQWRUWBUUMUVTWTTXAXBUUTUVNUWIUWPUVNUUMEUVPUWAI
      ZBAKZCWFZEUAZFGZXCZUWHUVNUUMUXBVKZFGZUXEUXFAFBAUWAXCUXFABCAUWABXDZXEBAXJX
      FXKUVNUXBUVMLZUXGUXEIUVNUXIUXBUVMWIZUVNUXACUVMUVNUWTUVPUVMLZBAUVNUWKMUWOU
      WAUVMLUWTUXKSUVNAUVMUUOUWQWLUUOXGUWAUVMUVPWTXHXAXBUVNUXBUCLUXIUXJVLBCAUWA
      UVMXIUXCUVMLUXCUVMWIUXIUXJEUXBUCUXCUXBUVMXLUXCUXBUVMXMUXCEVPXNVTTWAEUXBYA
      TXOUXEUVTUXDIEUXBKDWFZVKUWHEDUXBUXDUXCFXPXEUXLUWEDECBAUWAUXDUWBUXHUXCUWAF
      UJXQXRXSXTTUUMUWEAFXPYBYCUUTUVNUVDUWGSZUWPUVPUVPFGZNGZOPZUWCBUVPKZDWFZUVP
      QPZSUXMCAUVMUVPAIZUXPUVDUXSUWGUXTUXOUVCIUXPUVDVLUVPANFYDUVPAUXOUVCOYEYFUX
      RUWEIUXTUXSUWGVLUXTUXQUWDDUWCBUVPAYGYHUXRUWEUVPAQYEYIYJUXPUXRBUVPUWBYKZYL
      ZUVPQBDUVPUWBUYAUYAYMZYNUXPUVPYOVCLZUVPUYBUYAYPZUYBUVPQPUXPUXOJLUVPUXOQPU
      YDUXNYQUVPUXOYRUXOUVPYSYTUYAUVPUUCUYEBUVPUWBUYAUWAFXPUYCUUAUVPUYAUUDUNUVP
      UYBUYAUUBUUEUUFUUGTUWFUWGMUVFUVEUVCUWEAUUHUVSTUUIUUJWHUUKUUL $.
  $}

  ${
    $d A x y $.
    $( ` ( R1 `` A ) ` for ` A ` a strongly inaccessible cardinal is a Tarski
       class.  (Contributed by Mario Carneiro, 8-Jun-2013.) $)
    inatsk $p |- ( A e. Inacc -> ( R1 ` A ) e. Tarski ) $=
      ( vx vy wcel cr1 cfv wss wa wral wbr wo con0 wceq syl sylbid imp csdm cvv
      wi wb cina cpw cen ctsk cwina inawina wrex ciun wlim winaon winalim r1lim
      cv syl2anc eleq2d eliun bitrdi csuc onelon sylan r1pw limsuc r1ord2 sseld
      rexlimdva cuni r1tr2 sstrdi jccil ralrimiva crnk r1suc rankr1ai biimtrrdi
      elssuni fvex elsuc sylib orcomd wn elpwi ad2antlr ssdomg mpsyl ccf rankcf
      cdom fveq2 wne elina simp2bi sylan9eqr breq2d mtbii inar1 sdomentr expcom
      c0 adantr mtod adantlr bren2 sylanbrc ex cima cdm r1elwf r1fnon eleqtrrdi
      fndmi rankr1ag biimprd orim12d mpd eltsk2g ax-mp ) AUADZBUMZUBZAEFZGZXSXT
      DZHZBXTIZXRXTUCJZXRXTDZKZBXTUBZIZXTUDDZXQYCBXTXQYFHYBYAXQYFYBXQAUEDZYFYBS
      AUFZYKYFXRCUMZEFZDZCAUGZYBYKYFXRCAYNUHZDYPYKXTYQXRYKALDZAUIZXTYQMAUJZAUKZ
      CALULUNUOCXRAYNUPUQYKYOYBCAYKYMADZHZYOXSYMURZEFZDZYBUUCYMLDZYOUUFTYKYRUUB
      UUGYTAYMUSUTXRYMVANUUCUUEXTXSYKUUBUUEXTGZYKUUBUUDADZUUHYKYSUUBUUITUUAAYMV
      BNYKYRUUIUUHSYTUUDAVCNOPVDOVEONPYBXSXTVFXTXSXTVOAVGVHVIVJXQYGBYHXQXRYHDZH
      ZXRVKFZAMZUULADZKYGUUKUUNUUMUUKUULAURZDZUUNUUMKXQUUJUUPXQUUJXRUUOEFZDZUUP
      XQYRUURUUJTXQYKYRYLYTNZYRUUQYHXRAVLUONZXRUUOVMVNPUULAXRVKVPVQVRVSUUKUUMYE
      UUNYFUUKUUMYEUUKUUMHZXRXTWGJZXRXTQJZVTZYEXTRDZUVAXRXTGZUVBAEVPZUUJUVFXQUU
      MXRXTWAWBXRXTRWCWDXQUUMUVDUUJXQUUMHZUVCXRAQJZUVHXRUULWEFZQJUVIXRWFUVHUVJA
      XRQUUMXQUVJAWEFZAUULAWEWHXQAWRWIUVKAMXSAQJBAIBAWJWKWLWMWNXQUVCUVISZUUMXQX
      TAUCJZUVLAWOUVCUVMUVIXRXTAWPWQNWSWTXAXRXTXBXCXDUUKYFUUNUUKXRELXEVFDZAEXFZ
      DZYFUUNTXQUUJUVNXQUUJUURUVNUUTXRUUOXGVNPXQUVPUUJXQALUVOUUSLEXHXJXIWSXRAXK
      UNXLXMXNVJUVEYJYDYIHTUVGBXTRXOXPXC $.
  $}

  $( The set of hereditarily finite sets is a Tarski class.  (The
     Tarski-Grothendieck Axiom is not needed for this theorem.)  (Contributed
     by Mario Carneiro, 28-May-2013.) $)
  r1omtsk $p |- ( R1 ` _om ) e. Tarski $=
    ( com cina wcel cr1 cfv ctsk omina inatsk ax-mp ) ABCADEFCGAHI $.

  ${
    $d T x y $.  $d A x $.
    $( A Tarski class contains all ordinals smaller than it.  (Contributed by
       Mario Carneiro, 8-Jun-2013.) $)
    tskord $p |- ( ( T e. Tarski /\ A e. On /\ A ~< T ) -> A e. T ) $=
      ( vx vy con0 wcel csdm wbr cv wa wceq breq1 anbi2d eleq1 imbi12d wral wss
      wi syld imp ctsk simplrl onelss ssdomg adantlr simplrr domsdomtr ralimdva
      cdom syl2anc pm2.27 dfss3 tskssel biimtrrid com23 adantl ex 3impib 3com12
      3exp tfis3 ) AEFZBUAFZABGHZABFZVBVCVDVEVCCIZBGHZJZVFBFZRVCDIZBGHZJZVJBFZR
      ZVCVDJZVERCDAVFVJKZVHVLVIVMVPVGVKVCVFVJBGLMVFVJBNOVFAKZVHVOVIVEVQVGVDVCVF
      ABGLMVFABNOVFEFZVHVNDVFPZVIVRVHVSVIRVRVHJZVSVMDVFPZVIVTVNVMDVFVTVJVFFZJZV
      CVKVNVMRVRVCVGWBUBWCVJVFUIHZVGVKVRWBWDVHVRWBWDVRWBVJVFQWDVFVJUCVJVFEUDSTU
      EVRVCVGWBUFVJVFBUGUJVLVMUKUJUHVHWAVIRZVRVCVGWEVCWAVGVIWAVFBQZVCVGVIRDVFBU
      LVCWFVGVIVFBUMUTUNUOTUPSUQUOVAURUS $.
  $}

  ${
    $d T w x y z $.
    $( An even more direct relationship than ~ r1tskina to get an inaccessible
       cardinal out of a Tarski class: the size of any nonempty Tarski class is
       an inaccessible cardinal.  (Contributed by Mario Carneiro,
       9-Jun-2013.) $)
    tskcard $p |- ( ( T e. Tarski /\ T =/= (/) ) -> ( card ` T ) e. Inacc ) $=
      ( vx vz vy ctsk wcel c0 wa ccrd cfv ccf wceq cv csdm wbr cmap cdom adantr
      wss syl2anc vw wne cpw wral cina cardeq0 necon3bid biimpar cale con0 crab
      wn co cint char cmpt eqid pwcfsdom vpwex canth2 simpl cardon oneli adantl
      com cardsdomelir tskord syl3anc tskpwss syldan ssdomg sylc cardidg ensymd
      cen tskpw domentr sdomdomtr sylancr ralrimiva inawinalem ax-mp winainflem
      wrex wi mp3an2 sylan2 cardidm cardaleph sylancl fveq2d oveq12d mpbiri w3a
      breq12d simp1 simp3 cxp wf fvex elmap fssxp sylbi ex ssrdv cfle sstr mpan
      tskxpss 3exp com23 mpdi mpd sstr2 syl2im simp2 wfn cvv ffn fndmeng syl2an
      ensdomtr tskssel 3expia imp domnsym syl mt2d cfon onsseli elina syl3anbrc
      wo mpbi ori ) AEFZAGUBZHZAIJZGUBZYSKJZYSLZBMZUCZYSNOZBYSUDZYSUEFYPYTYQYPY
      SGAGAEUFUGUHZYRUUAYSFZULUUBYRUUHYSYSUUAPUMZNOZYRUUJYSUUCUIJSBUJUKUNZUIJZU
      ULUULKJZPUMZNOCUUKUACUUMCMUAMJUOJUPZUUOUQURYRYSUULUUIUUNNYRVEYSSZYSIJYSLY
      SUULLYRYTUUFUUPUUGYPUUFYQYPUUEBYSYPUUCYSFZHZUUDUUDUCZNOUUSYSQOZUUEUUDBUSU
      TUURUUSAQOZAYSVOOZUUTUURYPUUSASZUVAYPUUQVAZYPUUQUUCAFZUVCUURYPUUCUJFZUUCA
      NOZUVEUVDUUQUVFYPYSUUCAVBZVCVDUUQUVGYPUUCAVFVDUUCAVGVHZYPUVEUUDAFUVCUUCAV
      PUUDAVIVJVJUUSAEVKVLYPUVBUUQYPYSAAEVMVNZRUUSAYSVQTUUDUUSYSVRVSVTRZUUFYTUU
      CDMNODYSWDBYSUDZUUPYSUJFZUUFUVLWEUVHBDYSWAWBYTUVMUVLUUPUVHBDYSWCWFWGTAWHB
      YSWIWJZYRYSUULUUAUUMPUVNYRYSUULKUVNWKWLWOWMYPUUHUUJULZWEYQYPUUHUVOYPUUHHZ
      UUIYSQOZUVOUVPUUIAQOZUVBUVQYPUUHUUIASZUVRUVPBUUIAYPUUHUUCUUIFZUVEYPUUHUVT
      WNZYPUUCASZUVGUVEYPUUHUVTWPZUWAUVTYPUWBYPUUHUVTWQZUWCUVTUUCUUAYSWRZSZYPUW
      EASZUWBUVTUUAYSUUCWSZUWFYSUUAUUCAIWTYSKWTZXAZUUAYSUUCXBXCYPYSASZUWGYPBYSA
      YPUUQUVEUVIXDXEYPUWKUUAASZUWGUUAYSSZUWKUWLYSXFZUUAYSAXGXHYPUWLUWKUWGYPUWL
      UWKUWGUUAYSAXIXJXKXLXMUUCUWEAXNXOVLUWAUVTUUHUVGUWDYPUUHUVTXPUVTUUCUUAVOOU
      UAANOUVGUUHUVTUUAUUCUVTUWHUUAUUCVOOZUWJUWHUUCUUAXQUUAXRFUWOUUAYSUUCXSUWIU
      UAXRUUCXTWJXCVNUUAAVFUUCUUAAYBYATUUCAYCVHYDXEYPUVSUVRUUIAEVKYEVJYPUVBUUHU
      VJRUUIAYSVQTUUIYSYFYGXDRYHUUHUUBUWMUUHUUBYMUWNUUAYSYSYIUVHYJYNYOYGUVKBYSY
      KYL $.
  $}

  ${
    $d A x $.
    $( There is a direct relationship between transitive Tarski classes and
       inaccessible cardinals: the Tarski classes that occur in the cumulative
       hierarchy are exactly at the strongly inaccessible cardinals.
       (Contributed by Mario Carneiro, 8-Jun-2013.) $)
    r1tskina $p |- ( A e. On ->
        ( ( R1 ` A ) e. Tarski <-> ( A = (/) \/ A e. Inacc ) ) ) $=
      ( vx con0 wcel cr1 cfv ctsk c0 wceq cina wo wa wn wne ccrd cen wbr simplr
      syl2anc csdm df-ne simpll crnk csuc cima cuni onwf sseli eqid rankr1c syl
      mpbii simpld cdm r1fnon fndmi eleq2i rankonid bitr3i fveq2 sylbi neleqtrd
      adantl wss onssr1 sylbir tsken sylan2 ord mt3d carden2b wral simpl adantr
      cv sselda tsksdom ensymd sdomentr ralrimiva iscard eqtr3d on0eln0 biimpar
      sylanbrc r10 r1sdom syldan eqbrtrrid 0sdom sylib adantlr tskcard eqeltrrd
      fvex ex biimtrrid orrd eqtrdi 0tsk eqeltrdi inatsk jaoi impbid1 ) ACDZAEF
      ZGDZAHIZAJDZKZXEXGXJXEXGLZXHXIXHMAHNZXKXIAHUAXKXLXIXKXLLZXFOFZAJXMAOFZXNA
      XMAXFPQZXOXNIXMXGXEXPXEXGXLRZXEXGXLUBXGXELZXPAXFDZXEXSMXGXEAUCFZEFZXFAXEA
      YADMZAXTUDEFDZXEAECUEUFZDZYBYCLZCYDAUGUHYEXTXTIYFXTUIAXTUJULUKUMXEXTAIZYA
      XFIXEAEUNZDZYGYHCACEUOUPUQZAURUSXTAEUTVAVBVCXRXPXSXEXGAXFVDZXPXSKXEYIYKYJ
      AVEVFZAXFVGVHVIVJZSAXFVKUKXKXOAIZXLXKXEBVOZATQZBAVLYNXEXGVMXKYPBAXKYOADZL
      ZYOXFTQZXFAPQZYPYRXGYOXFDYSXEXGYQRZXKAXFYOXEYKXGYLVNVPYOXFVQSYRXGXEYTUUAX
      EXGYQUBXRAXFYMVRSYOXFAVSSVTBAWAWEVNWBXMXGXFHNZXNJDXQXEXLUUBXGXEXLLZHXFTQU
      UBUUCHHEFZXFTWFXEXLHADZUUDXFTQXEUUEXLAWCWDAHWGWHWIXFAEWOWJWKWLXFWMSWNWPWQ
      WRWPXHXGXIXHXFHGXHXFUUDHAHEUTWFWSWTXAAXBXCXD $.
  $}

  ${
    $d A f x y z $.  $d T f x y z $.
    $( The union of an element of a transitive Tarski class is in the set.
       (Contributed by Mario Carneiro, 22-Jun-2013.) $)
    tskuni $p |- ( ( T e. Tarski /\ Tr T /\ A e. T ) -> U. A e. T ) $=
      ( vf vz vx vy wcel cen wbr cv wa wceq wrex csdm adantr syl2anc syl wss wi
      cdom ctsk wtr w3a cuni ccrd cfv wf1o wex cima cab wne ccf tsksdom cardidg
      wn ensymd sdomentr cmpt crn eqid rnmpt cdm cardon sdomdom ondomen sylancr
      wfo con0 adantl wfn vex imaex fnmpti dffn4 mpbi fodomnum mpisyl eqbrtrrid
      domsdomtr sylancom adantll mpdan cina c0 ne0i tskcard sylan2 wral simp2bi
      elina breqtrrd 3adant2 wlim cwina inawina winalim 3syl eqeq1 rexbidv elab
      cpw imassrn f1ofo forn sseqtrid ad2antlr wf1 f1of1 elssuni f1imaen syl2an
      simpl1 trss 3adant1 sselda adantlr ensdomtr sseq1 breq1 anbi12d rexlimdva
      imp biimprcd biimtrid ralrimiv fvex cfslb2n dfiun2 ralrimivw iunss sylibr
      mpd ciun wf fof foelrn ex 3ad2ant2 3ad2ant1 expcom eluni2 nfv nfiu1 nfel2
      ssiun2 ffn simp3 fnfvima syl3anc sseldd 3exp rexlimd eleq1a syl6 rexlimdv
      sylsyld ssrdv eqssd eqtr3id necon3ai pm2.01da nexdv entr bren sylib uniss
      mtod wo df-tr biimpi sylan9ss syld tsken 3impb ord ) BUAGZBUBZABGZUCZAUDZ
      BHIZUOUVTBGZUVSUWAUVTBUEUFZCJZUGZCUHZUVSUWECUVSUWEUVSUWEKZDJZUWDEJZUIZLZE
      AMZDUJZUDZUWCUKZUWEUOUWGUWMUWCULUFZNIZUWOUVSUWQUWEUVPUVRUWQUVQUVPUVRKZUWM
      UWCUWPNUWRAUWCNIZUWMUWCNIZUWRABNIBUWCHIZUWSABUMUVPUXAUVRUVPUWCBBUAUNUPZOA
      BUWCUQPUVRUWSUWTUVPUVRUWSUWMATIUWTUVRUWSKZUWMEAUWJURZUSZATEDAUWJUXDUXDUTZ
      VAUXCAUEVBGZAUXEUXDVGZUXEATIUWSUXGUVRUWSUWCVHGAUWCTIUXGBVCAUWCVDUWCAVEVFV
      IUXDAVJUXHEAUWJUXDUWDUWICVKVLZUXFVMAUXDVNVOAUXEUXDVPVQVRUWMAUWCVSVTWAWBUW
      RUWCWCGZUWPUWCLZUVRUVPBWDUKUXJBAWEBWFWGZUXJUWCWDUKUXKUWIXAUWCNIEUWCWHEUWC
      WJWIZQWKWLOUWGUWCWMZFJZUWCRZUXOUWPNIZKZFUWMWHUWQUWOSUWGUXJUWCWNGUXNUVSUXJ
      UWEUVPUVRUXJUVQUXLWLOZUWCWOUWCWPWQUWGUXRFUWMUXOUWMGUXOUWJLZEAMZUWGUXRUWLU
      YADUXOFVKUWHUXOLUWKUXTEAUWHUXOUWJWRWSWTUWGUXTUXREAUWGUWIAGZKZUWJUWCRZUWJU
      WPNIZUXTUXRSUWEUYDUVSUYBUWEUWDUSZUWJUWCUWDUWIXBUWEUVTUWCUWDVGZUYFUWCLUVTU
      WCUWDXCZUVTUWCUWDXDQXEZXFUYCUWJUWCUWPNUYCUWJUWIHIZUWIUWCNIZUWJUWCNIUWEUYB
      UYJUVSUWEUVTUWCUWDXGUWIUVTRZUYJUYBUVTUWCUWDXHUWIAXIZUVTUWCUWIUWDEVKXJXKWA
      UVSUYBUYKUWEUVSUYBKZUWIBNIZUXAUYKUYNUVPUWIBGUYOUVPUVQUVRUYBXLZUVSABUWIUVQ
      UVRABRZUVPUVQUVRUYQBAXMZYBXNXOUWIBUMPUYNUVPUXAUYPUXBQUWIBUWCUQPXPUWJUWIUW
      CXQPUWGUXKUYBUWGUXJUXKUXSUXMQOWKUXTUXRUYDUYEKUXTUXPUYDUXQUYEUXOUWJUWCXRUX
      OUWJUWPNXSXTYCPYAYDYEFUWCUWMBUEYFYGPYLUWEUWNUWCUWEUWNEAUWJYMZUWCEDAUWJUXI
      YHUWEUYSUWCUWEUYDEAWHUYSUWCRUWEUYDEAUYIYIEAUWJUWCYJYKUWEFUWCUYSUWEUYGUXOU
      WCGZUXOUYSGZSUYHUYGUVTUWCUWDYNZUYTUXOUWHUWDUFZLZDUVTMZVUAUVTUWCUWDYOUYGUY
      TVUEDUVTUWCUXOUWDYPYQVUBVUDVUADUVTVUBUWHUVTGZVUCUYSGZVUDVUASVUFUWHUWIGZEA
      MVUBVUGEUWHAUUAVUBVUHVUGEAVUBEUUBEVUCUYSEAUWJUUCUUDVUBUYBVUHVUGVUBUYBVUHU
      CZUWJUYSVUCUYBVUBUWJUYSRVUHEAUWJUUEYRVUIUWDUVTVJZUYLVUHVUCUWJGVUBUYBVUJVU
      HUVTUWCUWDUUFYSUYBVUBUYLVUHUYMYRVUBUYBVUHUUGUVTUWIUWDUWHUUHUUIUUJUUKUULYD
      VUCUYSUXOUUMUUNUUOUUPQUUQUURUUSUUTQUVAUVBUVPUVQUWAUWFSUVRUWAUVPUWFUWAUVPK
      UVTUWCHIZUWFUVPUWAUXAVUKUXBUVTBUWCUVCWGUVTUWCCUVDUVEYTYSUVGUVSUWAUWBUVPUV
      QUVRUWAUWBUVHZUVQUVRKUVPUVTBRZVULUVQUVRVUMUVQUVRUYQVUMUYRUYQUVQVUMUYQUVQU
      VTBUDZBABUVFUVQVUNBRBUVIUVJUVKYTUVLYBUVTBUVMWGUVNUVOYL $.

    $( A nonempty transitive Tarski class is a weak universe.  (Contributed by
       Mario Carneiro, 2-Jan-2017.) $)
    tskwun $p |- ( ( T e. Tarski /\ Tr T /\ T =/= (/) ) -> T e. WUni ) $=
      ( vx vy ctsk wcel wtr c0 wne w3a cwun cv cuni cpw cpr wral simp2 simp3 wi
      3ad2ant1 ralrimiva tskuni 3expa 3adantl3 tskpw 3ad2antl1 tskpr 3exp imp31
      wa 3jca wb iswun mpbir3and ) ADEZAFZAGHZIZAJEZUOUPBKZLAEZUSMAEZUSCKZNAEZC
      AOZIZBAOZUNUOUPPUNUOUPQUQVEBAUQUSAEZUIZUTVAVDUNUOVGUTUPUNUOVGUTUSAUAUBUCU
      NUOVGVAUPUSAUDUEVHVCCAUQVGVBAEZVCUNUOVGVIVCRRUPUNVGVIVCUSVBAUFUGSUHTUJTUN
      UOURUOUPVFIUKUPBCADULSUM $.
  $}

  $( The intersection of an element of a transitive Tarski class is an element
     of the class.  (Contributed by FL, 17-Apr-2011.)  (Revised by Mario
     Carneiro, 20-Sep-2014.) $)
  tskint $p |- ( ( ( T e. Tarski /\ Tr T ) /\ A e. T /\ A =/= (/) ) ->
    |^| A e. T ) $=
    ( ctsk wcel wtr wa c0 wne w3a cuni wss simp1l tskuni 3expa 3adant3 intssuni
    cint 3ad2ant3 tskss syl3anc ) BCDZBEZFZABDZAGHZIUAAJZBDZAQZUFKZUHBDUAUBUDUE
    LUCUDUGUEUAUBUDUGABMNOUEUCUIUDAPRUFUHBST $.

  $( The union of two elements of a transitive Tarski class is in the set.
     (Contributed by Mario Carneiro, 20-Sep-2014.) $)
  tskun $p |- ( ( ( T e. Tarski /\ Tr T ) /\ A e. T /\ B e. T ) ->
    ( A u. B ) e. T ) $=
    ( ctsk wcel wtr wa w3a cpr cuni cun wceq uniprg 3adant1 simp1l simp1r tskpr
    3adant1r tskuni syl3anc eqeltrrd ) CDEZCFZGZACEZBCEZHZABIZJZABKZCUEUFUIUJLU
    DABCCMNUGUBUCUHCEZUICEUBUCUEUFOUBUCUEUFPUBUEUFUKUCABCQRUHCSTUA $.

  $( The Cartesian product of two elements of a transitive Tarski class is an
     element of the class.  JFM CLASSES2 th. 67 (partly).  (Contributed by FL,
     15-Apr-2011.)  (Proof shortened by Mario Carneiro, 20-Sep-2014.) $)
  tskxp $p |- ( ( ( T e. Tarski /\ Tr T ) /\ A e. T /\ B e. T )
  -> ( A X. B ) e. T ) $=
    ( ctsk wcel wtr wa w3a cwun c0 ne0i tskwun 3expa sylan2 3adant3 simp2 simp3
    wne wunxp ) CDEZCFZGZACEZBCEZHABCUBUCCIEZUDUCUBCJRZUECAKTUAUFUECLMNOUBUCUDP
    UBUCUDQS $.

  $( Set exponentiation is an element of a transitive Tarski class.  JFM
     CLASSES2 th. 67 (partly).  (Contributed by FL, 15-Apr-2011.)  (Proof
     shortened by Mario Carneiro, 20-Sep-2014.) $)
  tskmap $p |- ( ( ( T e. Tarski /\ Tr T ) /\ A e. T /\ B e. T )
  -> ( A ^m B ) e. T ) $=
    ( ctsk wcel wtr wa w3a cwun c0 ne0i tskwun 3expa sylan2 3adant3 simp2 simp3
    wne wunmap ) CDEZCFZGZACEZBCEZHABCUBUCCIEZUDUCUBCJRZUECAKTUAUFUECLMNOUBUCUD
    PUBUCUDQS $.

  $( A transitive Tarski class is closed under small unions.  (Contributed by
     Mario Carneiro, 22-Jun-2013.) $)
  tskurn $p |- ( ( ( T e. Tarski /\ Tr T ) /\ A e. T /\ F : A --> T )
  -> U. ran F e. T ) $=
    ( ctsk wcel wtr wa wf w3a crn cuni simp1l simp1r wss csdm wbr 3ad2ant3 sylc
    syl2anc syl3anc frn cdom ccrd cdm wfo tskwe2 syl simp2 trss ssnum wfn dffn4
    ffn sylib fodomnum tsksdom domsdomtr tskssel tskuni ) BDEZBFZGZABEZABCHZIZU
    TVACJZBEZVFKBEUTVAVCVDLZUTVAVCVDMZVEUTVFBNZVFBOPZVGVHVDVBVJVCABCUAQVEVFAUBP
    ZABOPZVKVEAUCUDZEZAVFCUEZVLVEBVNEZABNZVOVEUTVQVHBUFUGVEVAVCVRVIVBVCVDUHZBAU
    IRBAUJSVDVBVPVCVDCAUKVPABCUMACULUNQAVFCUORVEUTVCVMVHVSABUPSVFABUQSVFBURTVFB
    UST $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Grothendieck universes
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c Univ $. $( The class of all Grothendieck universes. $)

  $( Extend class notation to include the class of all Grothendieck
     universes. $)
  cgru $a class Univ $.

  ${
    $d u x y $.
    $( A Grothendieck universe is a set that is closed with respect to all the
       operations that are common in set theory: pairs, powersets, unions,
       intersections, Cartesian products etc.  Grothendieck and alii,
       S&eacute;minaire de G&eacute;om&eacute;trie Alg&eacute;brique 4,
       Expos&eacute; I, p. 185.  It was designed to give a precise meaning to
       the concepts of categories of sets, groups...  (Contributed by Mario
       Carneiro, 9-Jun-2013.) $)
    df-gru $a |- Univ = { u | ( Tr u /\ A. x e. u ( ~P x e. u /\
      A. y e. u { x , y } e. u /\ A. y e. ( u ^m x ) U. ran y e. u ) ) } $.
  $}

  ${
    $d U u x y $.
    $( Properties of a Grothendieck universe.  (Contributed by Mario Carneiro,
       9-Jun-2013.) $)
    elgrug $p |- ( U e. V ->
      ( U e. Univ <-> ( Tr U /\ A. x e. U ( ~P x e. U /\
        A. y e. U { x , y } e. U /\ A. y e. ( U ^m x ) U. ran y e. U ) ) ) ) $=
      ( vu cv wtr cpw wcel cpr wral crn cuni cmap co w3a cgru eleq2 raleqbi1dv
      wa wceq treq oveq1 raleqbidv 3anbi123d anbi12d df-gru elab2g ) EFZGZAFZHZ
      UIIZUKBFZJZUIIZBUIKZUNLMZUIIZBUIUKNOZKZPZAUIKZTCGZULCIZUOCIZBCKZURCIZBCUK
      NOZKZPZACKZTECQDUICUAZUJVDVCVLUICUBVBVKAUICVMUMVEUQVGVAVJUICULRUPVFBUICUI
      CUORSVMUSVHBUTVIUICUKNUCUICURRUDUESUFABEUGUH $.
  $}

  ${
    $d U x y $.  $d A x y $.  $d B y $.  $d F x y $.
    $( A Grothendieck universe is transitive.  (Contributed by Mario Carneiro,
       2-Jan-2017.) $)
    grutr $p |- ( U e. Univ -> Tr U ) $=
      ( vx vy cgru wcel wtr cv cpw cpr wral crn cuni cmap w3a elgrug ibi simpld
      co wa ) ADEZAFZBGZHAEUBCGZIAECAJUCKLAECAUBMRJNBAJZTUAUDSBCADOPQ $.

    $( A Grothendieck universe is transitive, so each element is a subset of
       the universe.  (Contributed by Mario Carneiro, 9-Jun-2013.) $)
    gruelss $p |- ( ( U e. Univ /\ A e. U ) -> A C_ U ) $=
      ( cgru wcel wtr wss grutr trss imp sylan ) BCDBEZABDZABFZBGKLMBAHIJ $.

    $( A Grothendieck universe contains the powerset of each of its members.
       (Contributed by Mario Carneiro, 9-Jun-2013.) $)
    grupw $p |- ( ( U e. Univ /\ A e. U ) -> ~P A e. U ) $=
      ( vy vx cgru wcel cpw cv cpr wral crn cuni cmap co w3a wi wtr elgrug ibi
      wa simprd simp1 ralimi wceq pweq eleq1d rspccv 3syl imp ) BEFZABFZAGZBFZU
      JCHZGZBFZUNDHZIBFDBJZUQKLBFDBUNMNJZOZCBJZUPCBJUKUMPUJBQZVAUJVBVATCDBERSUA
      UTUPCBUPURUSUBUCUPUMCABUNAUDUOULBUNAUEUFUGUHUI $.

    $( Any subset of an element of a Grothendieck universe is also an element.
       (Contributed by Mario Carneiro, 9-Jun-2013.) $)
    gruss $p |- ( ( U e. Univ /\ A e. U /\ B C_ A ) -> B e. U ) $=
      ( cgru wcel wss wa cpw wb elpw2g adantl grupw gruelss syldan sseld 3impia
      sylbird ) CDEZACEZBAFZBCEZRSGZTBAHZEZUASUDTIRBACJKUBUCCBRSUCCEUCCFACLUCCM
      NOQP $.

    ${
      $d B x $.
      $( A Grothendieck universe contains pairs derived from its elements.
         (Contributed by Mario Carneiro, 9-Jun-2013.) $)
      grupr $p |- ( ( U e. Univ /\ A e. U /\ B e. U ) -> { A , B } e. U ) $=
        ( vx vy cgru wcel cpr cv wral wi cpw crn cuni cmap co w3a eleq1d rspccv
        wceq wtr wa elgrug ibi simprd preq2 3ad2ant2 com12 ralimdv syl5com syl6
        preq1 com23 3imp ) CFGZACGZBCGZABHZCGZUOUQUPUSUOUQDIZBHZCGZDCJZUPUSKUOU
        TLCGZUTEIZHZCGZECJZVEMNCGECUTOPJZQZDCJZUQVCUOCUAZVKUOVLVKUBDECFUCUDUEUQ
        VJVBDCVJUQVBVHVDUQVBKVIVGVBEBCVEBTVFVACVEBUTUFRSUGUHUIUJVBUSDACUTATVAUR
        CUTABULRSUKUMUN $.
    $}

    $( A Grothendieck universe contains the range of any function which takes
       values in the universe (see ~ gruiun for a more intuitive version).
       (Contributed by Mario Carneiro, 9-Jun-2013.) $)
    gruurn $p |- ( ( U e. Univ /\ A e. U /\ F : A --> U ) -> U. ran F e. U ) $=
      ( vx vy cgru wcel wf crn cuni wa cmap co elmapg wi cpw wral wceq rspccv
      cv cpr w3a wtr elgrug ibi simprd rneq unieqd eleq1d 3ad2ant3 ralimi oveq2
      eleq2d imbi1d 3syl imp sylbird 3impia ) BFGZABGZABCHZCIZJZBGZUSUTKVACBALM
      ZGZVDBACFBNUSUTVFVDOZUSDTZPBGZVHETZUABGEBQZVJIZJZBGZEBVHLMZQZUBZDBQZCVOGZ
      VDOZDBQUTVGOUSBUCZVRUSWAVRKDEBFUDUEUFVQVTDBVPVIVTVKVNVDECVOVJCRZVMVCBWBVL
      VBVJCUGUHUISUJUKVTVGDABVHARZVSVFVDWCVOVECVHABLULUMUNSUOUPUQUR $.

    $( If ` B ( x ) ` is a family of elements of ` U ` and the index set ` A `
       is an element of ` U ` , then the indexed union ` U_ x e. A B ` is also
       an element of ` U ` , where ` U ` is a Grothendieck universe.
       (Contributed by Mario Carneiro, 9-Jun-2013.) $)
    gruiun $p |- ( ( U e. Univ /\ A e. U /\ A. x e. A B e. U )
        -> U_ x e. A B e. U ) $=
      ( cgru wcel wral ciun wa cmpt crn cuni wf wfn wss eqid fnmpt rnmptss df-f
      sylanbrc gruurn 3expia syl5com dfiun3g eleq1d sylibrd com12 3impia ) DEFZ
      BDFZCDFABGZABCHZDFZUKUIUJIZUMUKUNABCJZKZLZDFZUMUKBDUOMZUNURUKUOBNUPDOUSAB
      CUODUOPZQABCDUOUTRBDUOSTUIUJUSURBDUOUAUBUCUKULUQDABCDUDUEUFUGUH $.

    $( A Grothendieck universe contains unions of its elements.  (Contributed
       by Mario Carneiro, 17-Jun-2013.) $)
    gruuni $p |- ( ( U e. Univ /\ A e. U ) -> U. A e. U ) $=
      ( vx cgru wcel wa cuni cv ciun uniiun wral wss gruelss dfss3 sylib gruiun
      mpd3an3 eqeltrid ) BDEZABEZFZAGCACHZIZBCAJSTUBBECAKZUCBEUAABLUDABMCABNOCA
      UBBPQR $.

    $( A Grothendieck universe contains the range of any function which takes
       values in the universe (see ~ gruiun for a more intuitive version).
       (Contributed by Mario Carneiro, 9-Jun-2013.) $)
    grurn $p |- ( ( U e. Univ /\ A e. U /\ F : A --> U ) -> ran F e. U ) $=
      ( cgru wcel wf w3a crn cpw wss simp1 gruurn grupw syl2anc pwuni a1i gruss
      cuni syl3anc ) BDEZABEZABCFZGZTCHZRZIZBEZUDUFJZUDBETUAUBKZUCTUEBEUGUIABCL
      UEBMNUHUCUDOPUFUDBQS $.

    $( A Grothendieck universe contains image sets drawn from its members.
       (Contributed by Mario Carneiro, 9-Jun-2013.) $)
    gruima $p |- ( ( U e. Univ /\ Fun F /\ ( F " A ) C_ U ) ->
        ( A e. U -> ( F " A ) e. U ) ) $=
      ( cgru wcel wfun cima wss w3a wa cdm cin cres wrel wceq simpl2 wf syl3anc
      crn 3syl funrel df-ima resres resdm reseq1d eqtr3id rneqd simpr inss2 a1i
      eqtr4id simpl1 gruss wfn wfo funforn fof sylbi inss1 sylancl ffn eqsstrrd
      fssres simpl3 df-f sylanbrc grurn eqeltrd ex ) BDEZCFZCAGZBHZIZABEZVLBEVN
      VOJZVLCCKZALZMZSZBVPVKCNZVLVTOVJVKVMVOPZCUAWAVLCAMZSVTCAUBWAVSWCWAVSCVQMZ
      AMWCCVQAUCWAWDCACUDUEUFUGUKTZVPVJVRBEZVRBVSQZVTBEVJVKVMVOULZVPVJVOVRAHZWF
      WHVNVOUHWIVPVQAUIUJAVRBUMRVPVSVRUNZVTBHWGVPVKVRCSZVSQZWJWBVKVQWKCQZVRVQHW
      LVKVQWKCUOWMCUPVQWKCUQURVQAUSVQWKVRCVCUTVRWKVSVATVPVTVLBWEVJVKVMVOVDVBVRB
      VSVEVFVRBVSVGRVHVI $.

    $( Any element of an element of a Grothendieck universe is also an element
       of the universe.  (Contributed by Mario Carneiro, 9-Jun-2013.) $)
    gruel $p |- ( ( U e. Univ /\ A e. U /\ B e. A ) -> B e. U ) $=
      ( cgru wcel wa gruelss sseld 3impia ) CDEZACEZBAEBCEJKFACBACGHI $.

    $( A Grothendieck universe contains the singletons of its elements.
       (Contributed by Mario Carneiro, 9-Jun-2013.) $)
    grusn $p |- ( ( U e. Univ /\ A e. U ) -> { A } e. U ) $=
      ( cgru wcel wa csn cpr dfsn2 grupr 3anidm23 eqeltrid ) BCDZABDZEAFAAGZBAH
      LMNBDAABIJK $.

    $( A Grothendieck universe contains ordered pairs of its elements.
       (Contributed by Mario Carneiro, 10-Jun-2013.) $)
    gruop $p |- ( ( U e. Univ /\ A e. U /\ B e. U ) -> <. A , B >. e. U ) $=
      ( cgru wcel w3a cop csn dfopg 3adant1 simp1 grusn 3adant3 syl3anc eqeltrd
      cpr wceq grupr ) CDEZACEZBCEZFZABGZAHZABPZPZCTUAUCUFQSABCCIJUBSUDCEZUECEU
      FCESTUAKSTUGUAACLMABCRUDUECRNO $.

    ${
      $d B x $.
      $( A Grothendieck universe contains binary unions of its elements.
         (Contributed by Mario Carneiro, 9-Jun-2013.) $)
      gruun $p |- ( ( U e. Univ /\ A e. U /\ B e. U ) -> ( A u. B ) e. U ) $=
        ( vx cgru wcel w3a cun cpr ciun cuni wceq uniprg 3adant1 uniiun eqtr3di
        cv wral simp1 eleq1a grupr wa wo vex elpr jaao biimtrid ralrimiv gruiun
        syl3anc eqeltrd ) CEFZACFZBCFZGZABHZDABIZDQZJZCUOUQKZUPUSUMUNUTUPLULABC
        CMNDUQOPUOULUQCFURCFZDUQRZUSCFULUMUNSABCUAUMUNVBULUMUNUBZVADUQURUQFURAL
        ZURBLZUCVCVAURABDUDUEUMVDVAUNVEACURTBCURTUFUGUHNDUQURCUIUJUK $.
    $}

    $( A Grothendieck universe contains binary cartesian products of its
       elements.  (Contributed by Mario Carneiro, 9-Jun-2013.) $)
    gruxp $p |- ( ( U e. Univ /\ A e. U /\ B e. U ) -> ( A X. B ) e. U ) $=
      ( cgru wcel w3a cun cxp gruun cpw grupw wss xpsspw gruss mp3an3 3ad2antl1
      syldan mpdan ) CDEZACEZBCEZFABGZCEZABHZCEZABCISTUCUEUASUCUBJZCEZUEUBCKSUG
      UFJZCEZUEUFCKSUIUDUHLUEABMUHUDCNOQQPR $.

    $( A Grothendieck universe contains all powers of its elements.
       (Contributed by Mario Carneiro, 9-Jun-2013.) $)
    grumap $p |- ( ( U e. Univ /\ A e. U /\ B e. U ) -> ( A ^m B ) e. U ) $=
      ( cgru wcel w3a cxp cpw cmap wss simp1 gruxp 3com23 grupw syl2anc mapsspw
      co a1i gruss syl3anc ) CDEZACEZBCEZFZUABAGZHZCEZABIQZUFJZUHCEUAUBUCKZUDUA
      UECEZUGUJUAUCUBUKBACLMUECNOUIUDABPRUFUHCST $.

    $( A Grothendieck universe contains indexed cartesian products of its
       elements.  (Contributed by Mario Carneiro, 9-Jun-2013.) $)
    gruixp $p |- ( ( U e. Univ /\ A e. U /\ A. x e. A B e. U )
        -> X_ x e. A B e. U ) $=
      ( cgru wcel wral w3a ciun cmap cixp wss simp1 gruiun simp2 grumap syl3anc
      co ixpssmapg 3ad2ant3 gruss ) DEFZBDFZCDFABGZHZUBABCIZBJRZDFZABCKZUGLZUID
      FUBUCUDMZUEUBUFDFUCUHUKABCDNUBUCUDOUFBDPQUDUBUJUCABCDSTUGUIDUAQ $.

    $( A Grothendieck universe contains indexed intersections of its elements.
       (Contributed by Mario Carneiro, 9-Jun-2013.) $)
    gruiin $p |- ( ( U e. Univ /\ E. x e. A B e. U ) -> |^|_ x e. A B e. U ) $=
      ( cgru wcel wrex ciin nfv nfii1 nfel1 wss iinss2 gruss syl3an3 3exp com23
      cv rexlimd imp ) DEFZCDFZABGABCHZDFZUAUBUDABUAAIAUCDABCJKUAUBARBFZUDUAUBU
      EUDUEUAUBUCCLUDABCMCUCDNOPQST $.

    $( A Grothendieck universe contains all functions on its elements.
       (Contributed by Mario Carneiro, 10-Jun-2013.) $)
    gruf $p |- ( ( U e. Univ /\ A e. U /\ F : A --> U ) -> F e. U ) $=
      ( vx cgru wcel wf w3a cv cfv cop cmpt simp3 feqmptd fvex fnasrn eqtrdi wa
      crn simpl1 gruel 3expa 3adantl3 ffvelcdm 3ad2antl3 gruop syl3anc syld3an3
      fmpttd grurn eqeltrd ) BEFZABFZABCGZHZCDADIZUPCJZKZLZSZBUOCDAUQLUTUODABCU
      LUMUNMNDAUQUPCOPQULUMUNABUSGUTBFUODAURBUOUPAFZRULUPBFZUQBFZURBFULUMUNVATU
      LUMVAVBUNULUMVAVBAUPBUAUBUCUNULVAVCUMABUPCUDUEUPUQBUFUGUIABUSUJUHUK $.

    $( A Grothendieck universe contains all subsets of itself that are
       equipotent to an element of the universe.  (Contributed by Mario
       Carneiro, 9-Jun-2013.) $)
    gruen $p |- ( ( U e. Univ /\ A C_ U /\ ( B e. U /\ B ~~ A ) )
        -> A e. U ) $=
      ( vy cgru wcel wss cen wbr wa wi cv wf1o wex bren wfo f1ofo w3a crn wf
      wceq simp3l forn syl fof sylan grurn syl3an3 eqeltrrd 3expia expd exlimdv
      fss syl5 com3r expdimp syl7bi impd ancoms 3impia ) CEFZACGZBCFZBAHIZJZACF
      ZVBVAVEVFKVBVAJZVCVDVFVDBADLZMZDNZVGVCVFBADOVBVAVCVJVFKVAVCJZVJVBVFVKVIVB
      VFKZDVIBAVHPZVKVLBAVHQVKVMVBVFVAVCVMVBJZVFVAVCVNRZVHSZACVOVMVPAUAVAVCVMVB
      UBBAVHUCUDVNVAVCBCVHTZVPCFVMBAVHTVBVQBAVHUEBACVHUMUFBCVHUGUHUIUJUKUNULUOU
      PUQURUSUT $.

    $( A nonempty Grothendieck universe is a weak universe.  (Contributed by
       Mario Carneiro, 2-Jan-2017.) $)
    gruwun $p |- ( ( U e. Univ /\ U =/= (/) ) -> U e. WUni ) $=
      ( vx vy cgru wcel c0 wne wa cwun wtr cuni cpw cpr wral w3a adantr adantlr
      cv grutr ralrimiva simpr gruuni grupw grupr ad4ant134 wb iswun mpbir3and
      3jca ) ADEZAFGZHZAIEZAJZUKBRZKAEZUOLAEZUOCRZMAEZCANZOZBANZUJUNUKASPUJUKUA
      ULVABAULUOAEZHZUPUQUTUJVCUPUKUOAUBQUJVCUQUKUOAUCQVDUSCAUJVCURAEUSUKUOURAU
      DUETUITUJUMUNUKVBOUFUKBCADUGPUH $.
  $}

  ${
    $d u x y A $.
    $( The intersection of a family of universes is a universe.  (Contributed
       by Mario Carneiro, 9-Jun-2013.) $)
    intgru $p |- ( ( A C_ Univ /\ A =/= (/) ) -> |^| A e. Univ ) $=
      ( vx vy vu cgru wss wa cvv wcel wtr wral sylbi ral2imi vex elint2 3imtr4g
      cv adantlr wi 3expia c0 wne cint cpw cpr crn cuni cmap co w3a intex dfss3
      bilani grutr ralimi trint syl adantr grupw ex vpwex imp r19.26 grupr prex
      sylbir sylan2b ralrimiv wf wb elmapg ad2antlr intss1 fss sylan2 ralrimiva
      elvd gruurn syl5 rnex uniex imbitrrdi sylbid 3jca sylanb biimpar syl12anc
      elgrug ) AEFZAUAUBZGAUCZHIZWKJZBQZUDZWKIZWNCQZUEZWKIZCWKKZWQUFZUGZWKIZCWK
      WNUHUIZKZUJZBWKKZWKEIZWJWLWIAUKZUMWIWMWJWIDQZJZDAKZWMWIXJEIZDAKZXLDAEULZX
      MXKDAXJUNUOLDAUPUQURWIXNWJXGXOXNWJGZXFBWKXPWNWKIZGZWPWTXEXNXQWPWJXNXQWPXN
      WNXJIZDAKZWOXJIZDAKXQWPXMXSYADAXMXSYAWNXJUSUTMDWNABNOZDWOABVAOPVBRXNXQWTW
      JXNXQGZWSCWKXQXNXTWQWKIZWSSYBXNXTGZWQXJIZDAKZWRXJIZDAKZYDWSYEXMXSGZDAKZYG
      YISXMXSDAVCZYJYFYHDAXMXSYFYHWNWQXJVDTMVFDWQACNZODWRAWNWQVEOPVGVHRXRXCCXDX
      RWQXDIZWNWKWQVIZXCWJYNYOVJZXNXQWJWLYPXIWLYPBWKWNWQHHVKVQLVLXNXQYOXCSWJYCY
      OXBXJIZDAKZXCYOWNXJWQVIZDAKZYCYRYOYSDAXJAIYOWKXJFYSXJAVMWNWKXJWQVNVOVPXQX
      NXTYTYRSZYBYEYKUUAYLYJYSYQDAXMXSYSYQWNXJWQVRTMVFVGVSDXBAXAWQYMVTWAOWBRWCV
      HWDVPWEWLXHWMXGGBCWKHWHWFWG $.

    $d u U $.
    $( The intersection of a universe with a class that acts like a universe is
       another universe.  (Contributed by Mario Carneiro, 10-Jun-2013.) $)
    ingru $p |- ( ( Tr A /\ A. x e. A ( ~P x e. A /\
          A. y e. A { x , y } e. A /\ A. y ( y : x --> A -> U. ran y e. A ) ) )
        -> ( U e. Univ -> ( U i^i A ) e. Univ ) ) $=
      ( vu cgru wcel wtr cv wral wi w3a wa wss ssralv elin simplbi2 ral2imi cvv
      ax-mp cpw cpr wf crn cuni wal cin wceq ineq1 eleq1d imbi2d cmap co elgrug
      ibi trin ex inss1 inss2 syl2im im2anan9 vex mapss mp2an inex1 elmap mpan2
      fss sylbi imim1i alimi ralrid 3impa df-3an 3imtr4g syl wb imbitrrdi com12
      vtoclga ) DFGCHZAIZUAZCGZWBBIZUBZCGZBCJZWBCWEUCZWEUDUEZCGZKZBUFZLZACJZMZD
      CUGZFGZWPEIZCUGZFGZKWPWRKEDFWSDUHZXAWRWPXBWTWQFWSDCUIUJUKWSFGZWPWTHZWCWTG
      ZWFWTGZBWTJZWJWTGZBWTWBULUMZJZLZAWTJZMZXAXCWSHZWCWSGZWFWSGZBWSJZWJWSGZBWS
      WBULUMZJZLZAWSJZMZWPXMKXCYCABWSFUNUOXNWAXDYBWOXLXNWAXDWSCUPUQYBYAAWTJZWOW
      NAWTJZXLWTWSNZYBYDKWSCURZYAAWTWSOTWTCNZWOYEKWSCUSZWNAWTCOTYAWNXKAWTYAWDWH
      MZWMMZXEXGMZXJMZWNXKXOXQXTYKYMKXOXQMYJYLXTWMXJXOWDXEXQWHXGXEXOWDWCWSCPQXQ
      XPBWTJZWHWGBWTJZXGYFXQYNKYGXPBWTWSOTYHWHYOKYIWGBWTCOTXPWGXFBWTXFXPWGWFWSC
      PQRUTVAXTXRBXIJZWMWKBXIJXJXIXSNZXTYPKWSSGYFYQEVBZYGWTWSWBSVCVDXRBXIXSOTWM
      WKBXIWLWEXIGZWKKBYSWIWKYSWBWTWEUCZWIWTWBWEWSCYRVEZAVBVFYTYHWIYIWBWTCWEVHV
      GVIVJVKVLXRWKXHBXIXHXRWKWJWSCPQRUTVAVMWDWHWMVNXEXGXJVNVORUTVAVPWTSGXAXMVQ
      UUAABWTSUNTVRVTVS $.

    $( The wellfounded part of a universe is another universe.  (Contributed by
       Mario Carneiro, 17-Jun-2013.) $)
    wfgru $p |- ( U e. Univ -> ( U i^i U. ( R1 " On ) ) e. Univ ) $=
      ( vx vy cr1 con0 cima cuni wtr cv cpw wcel cpr wral wf crn wi wal w3a wss
      cgru cin dftr3 r1elssi mprgbir pwwf biimpi prwf ralrimiva frn rnex r1elss
      vex uniwf bitr3i sylib ax-gen a1i 3jca rgen ingru mp2an ) DEFGZHZBIZJVBKZ
      VDCIZLVBKZCVBMZVDVBVFNZVFOZGVBKZPZCQZRZBVBMATKAVBUATKPVCVDVBSBVBBVBUBVDUC
      UDVNBVBVDVBKZVEVHVMVOVEVDUEUFVOVGCVBVDVFUGUHVMVOVLCVIVJVBSZVKVDVBVFUIVPVJ
      VBKVKVJVFCULUJUKVJUMUNUOUPUQURUSBCVBAUTVA $.

    $d B x y $.  $d U x y $.
    $( Each ordinal that is comparable with an element of the universe is in
       the universe.  (Contributed by Mario Carneiro, 10-Jun-2013.) $)
    grudomon $p |- ( ( U e. Univ /\ A e. On /\ ( B e. U /\ A ~<_ B ) ) ->
        A e. U ) $=
      ( vx vy wcel cdom wbr wa con0 wi wceq breq1 eleq1 imbi12d imbi2d wral cvv
      cv wss cgru r19.21v w3a simpl1 vex onelss ssdomg mpsyl sylan simplr domtr
      imp syl2anc pm2.27 syl ralimdva dfss3 cen wb domeng 3ad2ant3 biimpa gruss
      wex simpl2 3expia 3adant1 adantr ensym anim12d1 ancomsd eximdv gruen 3exp
      3com23 exlimdv sylsyld mpd biimtrrid syld com23 3expib a2d biimtrid tfis3
      ex com3l impr 3impia ) CUAFZBCFZABGHZIZAJFZACFZWJWMWNWOWJWKWLWNWOKWNWJWKI
      ZWLWOWPDSZBGHZWQCFZKZKZWPESZBGHZXBCFZKZKZWPWLWOKZKDEAWQXBLZWTXEWPXHWRXCWS
      XDWQXBBGMWQXBCNOPWQALZWTXGWPXIWRWLWSWOWQABGMWQACNOPXFEWQQWPXEEWQQZKWQJFZX
      AWPXEEWQUBXKWPXJWTXKWJWKXJWTKXKWJWKUCZWRXJWSXLWRXJWSKXLWRIZXJXDEWQQZWSXMX
      EXDEWQXMXBWQFZIZXCXEXDKXPXBWQGHZWRXCXMXKXOXQXKWJWKWRUDWQRFXKXOIXBWQTZXQDU
      EXKXOXRWQXBUFULXBWQRUGUHUIXLWRXOUJXBWQBUKUMXCXDUNUOUPXNWQCTZXMWSEWQCUQXMW
      QXBURHZXBBTZIZEVDZXSWSKZXLWRYCWKXKWRYCUSWJEWQBCUTVAVBXMWJYCXDXBWQURHZIZEV
      DYDXKWJWKWRVEXMYBYFEXMYAXTYFXMYAXDXTYEXLYAXDKZWRWJWKYGXKWJWKYAXDBXBCVCVFV
      GVHWQXBVIVJVKVLWJYFYDEWJYFXSWSWJXSYFWSWQXBCVMVOVNVPVQVRVSVTWFWAWBWCWDWEWG
      WHWIVO $.
  $}

  ${
    $d A x y $.  $d U x y $.
    gruina.1 $e |- A = ( U i^i On ) $.
    $( If a Grothendieck universe ` U ` is nonempty, then the height of the
       ordinals in ` U ` is a strongly inaccessible cardinal.  (Contributed by
       Mario Carneiro, 17-Jun-2013.) $)
    gruina $p |- ( ( U e. Univ /\ U =/= (/) ) -> A e. Inacc ) $=
      ( vx vy wcel c0 wne wa cfv wceq csdm wbr wral con0 wss adantr cen sylancr
      sylc cgru ccf cv cpw cina wex wi n0 cin gruss mp3an3 0elon elin sylanblrc
      0ss eleqtrrdi ne0d expcom exlimiv sylbi impcom word cvv wtr cep wwe grutr
      wn tron trin sylancl inss2 epweon wess mp2 df-ord elon2 sylanbrc eqeltrid
      inex1g eloni ordirr syl biimpri mtod ccrd cuni cab cint wlim wrex eqsstri
      inss1 sseli cdom vpwex canth2 pwex cardid ensymi grupw syldan endom ax-mp
      com cardon mp3an2 mpanr2 onelss ssdomg endomtr sdomdomtr sylan2 ralrimiva
      grudomon inawinalem winainflem syl3anc wb vex sdomtr iscard cardlim sseq2
      limeq bibi12d mpbii mpbid cflm syl2anc eleq1 mpbiri abssi eqeltrrdi intex
      fvex sylibr onint eqeltrd eqeq1 anbi1d exbidv elab simp2rr simp1l simp2rl
      sylib sstrdi 3ad2ant3 simp2l eqbrtrdi gruen syl112anc gruuni 3exp exlimdv
      w3a mpd wo cfon cfle onsseleq mpan ord elina syl3anbrc ) BUAFZBGHZIZAGHZA
      UBJZAKZDUCZUDZALMZDANZAUEFUVHUVGUVJUVHUVMBFZDUFUVGUVJUGZDBUHUVQUVRDUVGUVQ
      UVJUVGUVQIZAGUVSGBOUIZAUVSGBFZGOFGUVTFUVGUVQGUVMPUWAUVMUOUVMGBUJUKULGBOUM
      UNCUPUQURUSUTVAZUVIAOFZUVKAFZVHUVLUVGUWCUVHUVGAUVTOCUVGUVTVBZUVTVCFUVTOFU
      VGUVTVDZUVTVEVFZUWEUVGBVDOVDUWFBVGVIBOVJVKUVTOPOVEVFUWGBOVLVMUVTOVEVNVOUV
      TVPUNBOUAVTUVTVQVRVSZQZUVIUWDABFZUVIUWCUWJVHUWIUWCUWJAAFZUWCAVBUWKVHAWAAW
      BWCUWJUWCUWKUWJUWCIZAUVTAAUVTFUWLABOUMWDCUPURWEWCUVIUVKEUCZWFJZKZUWMAPZAU
      WMWGZKZIZIZEUFZUWDUWJUGZUVIUVKUVMUWNKZUWSIZEUFZDWHZFUXAUVIUVKUXFWIZUXFUVI
      UWCAWJZUVKUXGKUWIUVIXEAPZUXHUVIUVJUWCUVMUWMLMEAWKDANZUXIUWBUWIUVGUXJUVHUV
      GUWCUVPUXJUWHUVGUVODAUVMAFZUVGUVQUVOABUVMAUVTBCBOWMWLZWNUVSUVNUVNUDZLMUXM
      AWOMZUVOUVNDWPZWQUVSUXMUXMWFJZRMUXPAWOMZUXNUXPUXMUXMUVNUXOWRWSZWTUVSUWCUX
      PAPZUXQUVGUWCUVQUWHQUVGUVQUXMBFZUXSUVGUVQUVNBFUXTUVMBXAUVNBXAXBUVGUXTIZUW
      CUXPAFZUXSUVGUWCUXTUWHQUYAUXPBFZUXPOFZUYBUVGUXTUXPUXMWOMZUYCUXPUXMRMUYEUX
      RUXPUXMXCXDUVGUYDUXTUYEIUYCUXMXFZUXPUXMBXOXGXHUYFUYCUYDIZUXPUVTAUXPUVTFUY
      GUXPBOUMWDCUPVKAUXPXITXBUXPAOXJTUXMUXPAXKSUVNUXMAXLSXMZXNZDEAXPTQDEAXQXRU
      VGUXIUXHXSZUVHUVGAWFJZAKZUYJUVGUWCUVMALMZDANUYLUWHUVGUYMDAUVGUXKIUVMUVNLM
      UVOUYMUVMDXTWQUYHUVMUVNAYASXNDAYBVRUYLXEUYKPZUYKWJZXSUYJAYCUYLUYNUXIUYOUX
      HUYKAXEYDUYKAYEYFYGWCQYHDEAOYIYJZUVIUXFOPUXFGHZUXGUXFFUXEDOUXDUVMOFZEUXCU
      YRUWSUXCUYRUWNOFUWMXFUVMUWNOYKYLQUSYMUVIUXGVCFUYQUVIUXGUVKVCUYPAUBYPZYNUX
      FYOYQUXFYRSYSUXEUXADUVKUYSUVMUVKKZUXDUWTEUYTUXCUWOUWSUVMUVKUWNYTUUAUUBUUC
      UUGUVIUWTUXBEUVIUWTUWDUWJUVIUWTUWDUUQZAUWQBUWPUWRUWOUVIUWDUUDVUAUVGUWMBFZ
      UWQBFUVGUVHUWTUWDUUEZVUAUVGUWMBPUVKBFZUVKUWMRMVUBVUCVUAUWMABUWPUWRUWOUVIU
      WDUUFUXLUUHUWDUVIVUDUWTABUVKUXLWNUUIVUAUVKUWNUWMRUVIUWOUWSUWDUUJUWMEXTWSU
      UKUWMUVKBUULUUMUWMBUUNYJYSUUOUUPUURWEUWCUWDUVLUVKOFZUWCUWDUVLUUSZAUUTVUEU
      WCIUVKAPVUFAUVAUVKAUVBYGUVCUVDTUVGUVPUVHUYIQDAUVEUVF $.

    $( A characterization of Grothendieck universes, part 1.  (Contributed by
       Mario Carneiro, 23-Jun-2013.) $)
    grur1a $p |- ( U e. Univ -> ( R1 ` A ) C_ U ) $=
      ( vx vy wcel cr1 cfv wss c0 wceq wi con0 fveq2 3syl wa sseli eleq1 eleq1d
      wral cin inss1 eqsstri sseq2 mpbii ss0 r10 eqtrdi 0ss eqsstrdi a1i wne cv
      cgru ciun cina cwina gruina inawina wlim winalim r1lim syl2anc inss2 csuc
      winaon imbi12d simpr elelsuc word ne0d sylan2 eloni ordsucelsuc imbitrrid
      wb mpd cpw grupw ex adantr r1suc biimprcd syl6 embantd com23 com4r pm2.27
      ontr1 expd com3r sylc imp ralimdva gruiun 3expia syld cvv biimprd sylan9r
      vex mpan exp32 com34 tfinds2 impcom gruelss syldan ralrimiva iunss sylibr
      eqsstrd pm2.61dne ) BUNFZAGHZBIZBJBJKZXPLXNXQAJIZAJKZXPXQABIXRABMUAZBCBMU
      BUCZBJAUDUEAUFXSXOJBXSXOJGHZJAJGNUGUHBUIUJOUKXNBJULZXPXNYCPZXODADUMZGHZUO
      ZBYDAUPFZAUQFZXOYGKZABCURZAUSZYIAMFZAUTYJAVFZAVADAMVBVCOXNYGBIZYCXNYFBIZD
      ATYOXNYPDAXNYEAFZYFBFZYPYQXNYRYQYEMFZXNYRLAMYEAXTMCBMVDUCQYSXNYQYRYQYRLJA
      FZJBFZLZEUMZAFZUUCGHZBFZLZUUCVEZAFZUUHGHZBFZLXNDEYEJKZYQYTYRUUAYEJARUULYF
      JBUULYFYBJYEJGNUGUHSVGYEUUCKZYQUUDYRUUFYEUUCARUUMYFUUEBYEUUCGNSVGYEUUHKZY
      QUUIYRUUKYEUUHARUUNYFUUJBYEUUHGNSVGUUBXNABJYAQUKXNUUGUUIUUCMFZUUKXNUUIUUG
      UUOUUKLZXNUUIUUGUUPLXNUUIPZUUDUUFUUPUUQUUIUUDXNUUIVHUUIUUDUUQUUHAVEFZUUHA
      VIUUQYMAVJUUDUURVPUUIXNYCYMUUIBUUHABUUHYAQVKYDYHYIYMYKYLYNOZVLAVMUUCAVNOV
      OVQUUQUUFUUEVRZBFZUUPXNUUFUVALUUIXNUUFUVAUUEBVSVTWAUUOUUKUVAUUOUUJUUTBUUC
      WBSWCWDWEVTWFWGYEUTZXNYQUUGEYETZYRUVBXNYQUVCYRLXNYQPZUVCEYEUUEUOZBFZUVBYR
      UVDUVCUUFEYETZUVFUVDUUGUUFEYEUVDUUCYEFZUUGUUFLZUVDYQYMUVHUVILXNYQVHYQXNYC
      YMYQBYEABYEYAQZVKUUSVLYMUVHYQUVIYMUVHYQUVIYMUVHYQPUUDUVIUUCYEAWIUUDUUFWHW
      DWJWKWLWMWNYQXNYEBFZUVGUVFLUVJXNUVKUVGUVFEYEUUEBWOWPVLWQUVBYRUVFUVBYFUVEB
      YEWRFUVBYFUVEKDXAEYEWRVBXBSWSWTXCXDXEWKVQXFYFBXGXHXIDAYFBXJXKWAXLVTXM $.

    $( A characterization of Grothendieck universes, part 2.  (Contributed by
       Mario Carneiro, 24-Jun-2013.) $)
    grur1 $p |- ( ( U e. Univ /\ U e. U. ( R1 " On ) ) -> U = ( R1 ` A ) ) $=
      ( vy vx wcel cr1 con0 wa cfv wss wn crnk wceq wi syl cvv ad2ant2r wbr ccf
      cgru cima cuni cv wrex wex nss fveqeq2 rspcev ad2antrl ctc simplr r1elssi
      ex simprl sseld sylc tcrank eleq2d wtr gruelss grutr adantr tcmin syl2anc
      vex ax-mp wfun wf rankf ffun fvelima mpan ssrexv syl2im sylbid simprr cdm
      wo wb cina cwina c0 wne ne0i gruina sylan2 inawina winaon 3syl wfn r1fnon
      fndm eleqtrrdi rankr1ag mtbid w3o rankon word eloni syl2an sylancr 3orass
      ordtri3or sylib ord mpd mpjaod exlimdv biimtrid simpll fveq2 ad2antll cpw
      cdom csdm wral elina simp2bi eqtrd rankcf domtri mp2an eqbrtrrdi grudomon
      fvex syl112anc cin elin biimpri ordirr adantl pm2.21dd rexlimdvaa pm2.18d
      mpbir syld grur1a eqssd ) BUAFZBGHUBUCZFZIZBAGJZUUCBUUDKZUUCUUELZDUDZMJZA
      NZDBUEZUUEUUFEUDZBFZUUKUUDFZLZIZEUFUUCUUJEBUUDUGUUCUUOUUJEUUCUUOUUJUUCUUO
      IZUUKMJZANZUUJAUUQFZUULUURUUJOUUCUUNUULUURUUJUUIUURDUUKBUUGUUKAMUHUIUNUJU
      UPUUSAMUUKUKJZUBZFZUUJUUPUUQUVAAUUPUUKUUAFZUUQUVANUUPUUBUULUVCYTUUBUUOULU
      UCUULUUNUOUUBBUUAUUKBUMUPUQZUUKURPUSYTUULUVBUUJOUUBUUNYTUULIZUUTBKZUVBUUI
      DUUTUEZUUJUVEUUKBKZBUTZUVFUUKBVAYTUVIUULBVBVCUUKQFUVHUVIIUVFOEVFUUKBQVDVG
      VEMVHZUVBUVGUUAHMVIUVJVJUUAHMVKVGDAUUTMVLVMUUIDUUTBVNVORVPUUPUUQAFZLZUURU
      USVSZUUPUUMUVKUUCUULUUNVQUUPUVCAGVRZFZUUMUVKVTUVDYTUULUVOUUBUUNUVEAHUVNUV
      EAWAFZAWBFZAHFZUULYTBWCWDZUVPBUUKWEABCWFZWGAWHZAWIZWJZGHWKUVNHNWLHGWMVGWN
      RUUKAWOVEWPYTUULUVLUVMOUUBUUNUVEUVKUVMUVEUVKUURUUSWQZUVKUVMVSUVEUUQHFZUVR
      UWDUUKWRUWCUWEUUQWSAWSZUWDUVRUUQWTAWTZUUQAXDXAXBUVKUURUUSXCXEXFRXGXHUNXIX
      JUUCUUIUUEDBUUCUUGBFZUUIIZIZABFZUVRUUEUWJYTUVRUWHAUUGXOSUWKYTUUBUWIXKUWJU
      VPUVQUVRYTUWHUVPUUBUUIUWHYTUVSUVPBUUGWEUVTWGRZUWAUWBWJZUUCUWHUUIUOUWJAUUH
      TJZUUGXOUWJUWNATJZAUUIUWNUWONUUCUWHUUHATXLXMUWJUVPUWOANZUWLUVPAWCWDUWPUUK
      XNAXPSEAXQEAXRXSPXTUWNUUGXOSZUUGUWNXPSLZUUGYAUWNQFUUGQFUWQUWRVTUUHTYFDVFU
      WNUUGQQYBYCYPYDAUUGBYEYGUWMUWKUVRIZAAFZUUEUWSABHYHZAAUXAFUWSABHYIYJCWNUVR
      UWTLZUWKUVRUWFUXBUWGAYKPYLYMVEYNYQYOYTUUDBKUUBABCYRVCYS $.
  $}

  ${
    $d T x y $.
    $( Grothendieck universes are the same as transitive Tarski classes, part
       one: a transitive Tarski class is a universe.  (The hard work is in
       ~ tskuni .)  (Contributed by Mario Carneiro, 17-Jun-2013.) $)
    grutsk1 $p |- ( ( T e. Tarski /\ Tr T ) -> T e. Univ ) $=
      ( vx vy ctsk wcel wtr wa cgru cv cpw cpr wral crn cuni cmap w3a ralrimiva
      co adantlr wb simpr tskpw tskpr 3expa wf elmapg tskurn 3expia sylbid 3jca
      ralrimiv elgrug adantr mpbir2and ) ADEZAFZGZAHEZUPBIZJAEZUSCIZKAEZCALZVAM
      NAEZCAUSORZLZPZBALZUOUPUAUQVGBAUQUSAEZGZUTVCVFUOVIUTUPUSAUBSUOVIVCUPUOVIG
      VBCAUOVIVAAEVBUSVAAUCUDQSVJVDCVEVJVAVEEZUSAVAUEZVDUOVIVKVLTUPAUSVADAUFSUQ
      VIVLVDUSAVAUGUHUIUKUJQUOURUPVHGTUPBCADULUMUN $.
  $}

  ${
    $d x y $.
    $( Grothendieck universes are the same as transitive Tarski classes.  (The
       proof in the forward direction requires Foundation.)  (Contributed by
       Mario Carneiro, 24-Jun-2013.) $)
    grutsk $p |- Univ = { x e. Tarski | Tr x } $=
      ( vy cgru cv wtr ctsk crab wcel wa c0 wceq 0tsk eleq1 mpbiri a1i wne con0
      wi cin cr1 cfv cima cuni cvv vex unir1 eleqtrri grur1 mpan2 adantr gruina
      eqid cina inatsk syl eqeltrd ex pm2.61dne grutr grutsk1 impbii treq elrab
      jca bitr4i eqriv ) BCADZEZAFGZBDZCHZVJFHZVJEZIZVJVIHVKVNVKVLVMVKVLVJJVJJK
      ZVLRVKVOVLJFHLVJJFMNOVKVJJPZVLVKVPIZVJVJQSZTUAZFVKVJVSKZVPVKVJTQUBUCZHVTV
      JUDWABUEUFUGVRVJVRULZUHUIUJVQVRUMHVSFHVRVJWBUKVRUNUOUPUQURVJUSVDVJUTVAVHV
      MAVJFVGVJVBVCVEVF $.
  $}


$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  ZFC Set Theory plus the Tarski-Grothendieck Axiom
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Introduce the Tarski-Grothendieck Axiom
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x y z w v u $.
    $( The Tarski-Grothendieck Axiom.  For every set ` x ` there is an
       inaccessible cardinal ` y ` such that ` y ` is not in ` x ` .  The
       addition of this axiom to ZFC set theory provides a framework for
       category theory, thus for all practical purposes giving us a complete
       foundation for "all of mathematics".  This version of the axiom is used
       by the Mizar project
       ( ~ http://www.mizar.org/JFM/Axiomatics/tarski.html ).  Unlike the ZFC
       axioms, this axiom is very long when expressed in terms of primitive
       symbols (see ~ grothprim ).  An open problem is finding a shorter
       equivalent.  (Contributed by NM, 18-Mar-2007.) $)
    ax-groth $a |- E. y ( x e. y /\ A. z e. y ( A. w ( w C_ z -> w e. y ) /\
                       E. w e. y A. v ( v C_ z -> v e. w ) ) /\
                     A. z ( z C_ y -> ( z ~~ y \/ z e. y ) ) ) $.

    $( The Tarski-Grothendieck axiom using abbreviations.  (Contributed by NM,
       22-Jun-2009.) $)
    axgroth5 $p |- E. y ( x e. y /\ A. z e. y ( ~P z C_ y
             /\ E. w e. y ~P z C_ w ) /\ A. z e. ~P y ( z ~~ y \/ z e. y ) ) $=
      ( vv wel cv cpw wss wrex wa wral cen wbr wo w3a wex wi wal pwss biid wcel
      ax-groth rexbii anbi12i ralbii df-ral velpw imbi1i albii bitri 3anbi123i
      exbii mpbir ) ABFZCGZHZBGZIZUQDGZIZDURJZKZCURLZUPURMNCBFOZCURHZLZPZBQUOUT
      UPIDBFRDSZEGUPIEDFRESZDURJZKZCURLZUPURIZVERZCSZPZBQABCDEUCVHVQBUOUOVDVMVG
      VPUOUAVCVLCURUSVIVBVKDUPURTVAVJDUREUPUTTUDUEUFVGUPVFUBZVERZCSVPVECVFUGVSV
      OCVRVNVECURUHUIUJUKULUMUN $.

    $( Alternate version of the Tarski-Grothendieck Axiom.  (Contributed by NM,
       18-Mar-2007.) $)
    axgroth2 $p |- E. y ( x e. y /\ A. z e. y ( A. w ( w C_ z -> w e. y ) /\
                       E. w e. y A. v ( v C_ z -> v e. w ) ) /\
                     A. z ( z C_ y -> ( y ~<_ z \/ z e. y ) ) ) $=
      ( wel cv wss wi wal wrex wa wral cdom wbr wo w3a wex cen ax-groth cvv elv
      ssdomg biantrurd sbthb bitrdi orbi1d pm5.74i albii 3anbi3i exbii mpbir )
      ABFZDGCGZHDBFIDJEGUNHEDFIEJDBGZKLCUOMZUNUOHZUOUNNOZCBFZPZIZCJZQZBRUMUPUQU
      NUOSOZUSPZIZCJZQZBRABCDETVCVHBVBVGUMUPVAVFCUQUTVEUQURVDUSUQURUNUONOZURLVD
      UQVIURUQVIIBUNUOUAUCUBUDUNUOUEUFUGUHUIUJUKUL $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Derive the Power Set, Infinity and Choice Axioms
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

    $( Derive the Axiom of Power Sets ~ ax-pow from the Tarski-Grothendieck
       axiom ~ ax-groth .  That it follows is mentioned by Bob Solovay at
       ~ https://fomarchive.ugent.be/2008-March/012783.html .  Note that
       ~ ax-pow is not used by the proof.  (Contributed by G&eacute;rard Lang,
       22-Jun-2009.)  (New usage is discouraged.) $)
    grothpw $p |- E. y A. z ( A. w ( w e. z -> w e. x ) -> z e. y ) $=
      ( cv cpw cvv wcel wel wi wal wex wss wrex wa wral cen wbr wo w3a weq pweq
      ralimi sseq1d rspccv syl anim2i 3adant3 pm3.35 vex ssex axgroth5 exlimiiv
      simpl 3syl axpweq mpbi ) AEZFZGHZDCIDAIJDKCBIZJCKBLABIZCEZFZBEZMZVDDEMDVE
      NZOZCVEPZVCVEQRVASCVEFPZTZUTBVKVBVBUSVEMZJZOZVLUTVBVIVNVJVIVMVBVIVFCVEPVM
      VHVFCVEVFVGUNUCVFVLCURVECAUAVDUSVEVCURUBUDUEUFUGUHVBVLUIUSVEBUJUKUOABCDUL
      UMBCDURUPUQ $.

    $( Derive the Axiom of Power Sets from the Tarski-Grothendieck axiom
       ~ ax-groth .  Note that ~ ax-pow is not used by the proof.  Use ~ axpweq
       to obtain ~ ax-pow .  Use ~ pwex or ~ pwexg instead.  (Contributed by
       G&eacute;rard Lang, 22-Jun-2009.)  (New usage is discouraged.) $)
    grothpwex $p |- ~P x e. _V $=
      ( vy vz vw cv wcel cpw wss wrex wa cen wbr wo w3a cvv wi simpl ralimi weq
      wral pweq sseq1d rspccv anim2i 3adant3 pm3.35 ssex 3syl axgroth5 exlimiiv
      syl vex ) AEZBEZFZCEZGZUNHZUQDEHDUNIZJZCUNTZUPUNKLUPUNFMCUNGTZNZUMGZOFZBV
      CUOUOVDUNHZPZJZVFVEUOVAVHVBVAVGUOVAURCUNTVGUTURCUNURUSQRURVFCUMUNCASUQVDU
      NUPUMUAUBUCUKUDUEUOVFUFVDUNBULUGUHABCDUIUJ $.

    $( The Tarski-Grothendieck axiom using abbreviations.  This version is
       called Tarski's axiom: given a set ` x ` , there exists a set ` y `
       containing ` x ` , the subsets of the members of ` y ` , the power sets
       of the members of ` y ` , and the subsets of ` y ` of cardinality less
       than that of ` y ` .  (Contributed by NM, 21-Jun-2009.) $)
    axgroth6 $p |- E. y ( x e. y /\ A. z e. y ( ~P z C_ y /\ ~P z e. y )
                   /\ A. z e. ~P y ( z ~< y -> z e. y ) ) $=
      ( vw vv wel cv cpw wss wcel wa wral wbr wi w3a wex wb wceq pweq sylbi cen
      csdm wrex wo axgroth5 biid sseq1d cbvralvw ssid sseq2 rspcev mpan2 rspccv
      pwss vpwex sseq1 eleq1 imbi12d spcv syl6 rexlimdv impbid2 ralbidv pm5.32i
      wal r19.26 3bitr4i velpw cdom impexp cvv ssdomg elv pm4.71i imbi1i brsdom
      wn bitri imbi2i 3bitr4ri pm5.74ri pm4.64 bitrdi ralbiia 3anbi123i exbii
      mpbir ) ABFZCGZHZBGZIZWJWKJZKCWKLZWIWKUBMZCBFZNZCWKHZLZOZBPWHWLWJDGZIZDWK
      UCZKCWKLZWIWKUAMZWPUDZCWRLZOZBPABCDUEWTXHBWHWHWNXDWSXGWHUFWLCWKLZWMCWKLZK
      XIXCCWKLZKWNXDXIXJXKXIEGZHZWKIZEWKLZXJXKQWLXNCEWKWIXLRWJXMWKWIXLSUGUHXOWM
      XCCWKXOWMXCWMWJWJIZXCWJUIXBXPDWJWKXAWJWJUJUKULXOXBWMDWKXODBFXAHZWKIZXBWMN
      ZXNXREXAWKXLXARXMXQWKXLXASUGUMXRXLXAIZEBFZNZEVEXSEXAWKUNYBXSEWJCUOXLWJRXT
      XBYAWMXLWJXAUPXLWJWKUQURUSTUTVAVBVCTVDWLWMCWKVFWLXCCWKVFVGWQXFCWRWIWRJWIW
      KIZWQXFQCWKVHYCWQXEVQZWPNZXFYCWQYEYCWIWKVIMZKZYENYCYFYENZNYCYENYCWQNYCYFY
      EVJYCYGYEYCYFYCYFNBWIWKVKVLVMVNVOWQYHYCWQYFYDKZWPNYHWOYIWPWIWKVPVOYFYDWPV
      JVRVSVTWAXEWPWBWCTWDWEWFWG $.

    $( The Tarski-Grothendieck Axiom implies the Axiom of Infinity (in the form
       of ~ omex ).  Note that our proof depends on neither the Axiom of
       Infinity nor Regularity.  (Contributed by Mario Carneiro, 19-Apr-2013.)
       (New usage is discouraged.) $)
    grothomex $p |- _om e. _V $=
      ( vy vz vw vx com cr1 cvv wcel con0 wss mp2an c0 cpw wral cfv wceq eleq1d
      cv wa wi cima cres wf1 wf1o r111 omsson f1ores f1of1 ax-mp wel wfn r1fnon
      wrex wb fvelimab csuc fveq2 weq r10 eleq1i biranri pweq rspccv nnon r1suc
      biimprcd syl6 com3r adantld finds2 eleq1 biimpd syl9 rexlimiv sylbi com12
      syl ssrdv vex ssex wex 0ex anbi1d exbidv csdm wbr w3a simpr ralimi anim2i
      axgroth6 3adant3 eximii vtocl exlimiiv f1dmex ) EFEUAZFEUBZUCZWQGHZEGHEWQ
      WRUDZWSIGFUCEIJZXAUEUFIGEFUGKEWQWRUHUILARZHZBRZMZXCHZBXCNZSZWTAXIWQXCJWTX
      ICWQXCCRZWQHZXICAUJZXKDRZFOZXJPZDEUMZXIXLTZFIUKXBXKXPUNULUFDIEXJFUOKXOXQD
      EXMEHXIXNXCHZXOXLXRLFOZXCHZXJFOZXCHZXJUPZFOZXCHZXIDCXMLPZXNXSXCXMLFUQQDCU
      RXNYAXCXMXJFUQQXMYCPXNYDXCXMYCFUQQXTXDXHXSLXCUSUTVAXJEHZXHYBYETXDXHYBYGYE
      XHYBYAMZXCHZYGYETXGYIBYAXCXEYAPXFYHXCXEYAVBQVCYGYEYIYGYDYHXCYGXJIHYDYHPXJ
      VDXJVEVQQVFVGVHVIVJXOXRXLXNXJXCVKVLVMVNVOVPVRWQXCAVSVTVQDAUJZXHSZAWAXIAWA
      DLWBYFYKXIAYFYJXDXHXMLXCVKWCWDYJXFXCJZXGSZBXCNZXEXCWEWFBAUJTBXCMNZWGYKADA
      BWKYJYNYKYOYNXHYJYMXGBXCYLXGWHWIWJWLWMWNWOEWQGWRWPK $.

    $( The Tarski-Grothendieck Axiom implies the Axiom of Choice (in the form
       of ~ cardeqv ).  This can be put in a more conventional form via ~ ween
       and ~ dfac8 .  Note that the mere existence of strongly inaccessible
       cardinals doesn't imply AC, but rather the particular form of the
       Tarski-Grothendieck axiom (see
       ~ https://fomarchive.ugent.be/2008-March/012783.html ).  (Contributed by
       Mario Carneiro, 19-Apr-2013.)  (New usage is discouraged.) $)
    grothac $p |- dom card = _V $=
      ( vy vu vx ccrd cdm cvv cv wcel cpw wss wa wral csdm wbr wi w3a crab cdom
      vex syl2im pweq sseq1d eleq1d anbi12d rspcva simpld rabss biimpri sdomdom
      weq canth2 ax-mp ssdomg elv domtr sylancr tskwe mpan numdom expcom 3impia
      axgroth6 exlimiiv 2th eqriv ) ADEZFAGZVFHZVGFHVGBGZHZCGZIZVIJZVLVIHZKZCVI
      LZVKVIMNZVKVIHOCVIIZLZPVHBVJVPVSVHVJVPKZVGIZVIJZVSVQCVRQVIJZVHVTWBWAVIHZV
      OWBWDKCVGVICAUJZVMWBVNWDWEVLWAVIVKVGUAZUBWEVLWAVIWFUCUDUEUFWCVSVQCVRVIUGU
      HWBVGVIRNZWCVIVFHZVHWBVGWARNZWAVIRNZWGVGWAMNWIVGASZUKVGWAUIULWBWJOBWAVIFU
      MUNVGWAVIUOUPVIFHWCWHBSCVIFUQURWHWGVHVIVGUSUTTTVAABCVBVCWKVDVE $.

    $( Alternate version of the Tarski-Grothendieck Axiom. ~ ax-cc is used to
       derive this version.  (Contributed by NM, 26-Mar-2007.) $)
    axgroth3 $p |- E. y ( x e. y /\ A. z e. y ( A. w ( w C_ z -> w e. y ) /\
                       E. w e. y A. v ( v C_ z -> v e. w ) ) /\
                     A. z ( z C_ y -> ( ( y \ z ) ~<_ z \/ z e. y ) ) ) $=
      ( wel cv wss wi wal wrex wa wral cdom wbr wo w3a wex wb wcel axgroth2 weq
      cdif cuni ssid elequ1 imbi12d spvv mpi reximi eluni2 sylibr adantl ralimi
      sseq1 dfss3 ccrd cdm com cvv vex grothac eleqtrri wne ne0i dominf infdif2
      c0 sylan mp3an12i orbi1d imbi2d albidv sylan2 pm5.32i 3bitr4i exbii mpbir
      df-3an ) ABFZDGCGZHDBFIDJZEGZWAHZEDFZIZEJZDBGZKZLZCWHMZWAWHHZWHWAUCWANOZC
      BFZPZIZCJZQZBRVTWKWLWHWANOZWNPZIZCJZQZBRABCDEUAWRXCBVTWKLZWQLXDXBLWRXCXDW
      QXBWKVTWHWHUDZHZWQXBSWKWAXETZCWHMXFWJXGCWHWIXGWBWICDFZDWHKXGWGXHDWHWGWAWA
      HZXHWAUEWFXIXHIECECUBWDXIWEXHWCWAWAUOECDUFUGUHUIUJDWAWHUKULUMUNCWHXEUPULV
      TXFLZWPXACXJWOWTWLXJWMWSWNWHUQURZTWAXKTXJUSWHNOZWMWSSWHUTXKBVAZVBVCWAUTXK
      CVAVBVCVTWHVHVDXFXLWHAGVEWHXMVFVIWHWAVGVJVKVLVMVNVOVTWKWQVSVTWKXBVSVPVQVR
      $.

    $( Alternate version of the Tarski-Grothendieck Axiom. ~ ax-ac is used to
       derive this version.  (Contributed by NM, 16-Apr-2007.) $)
    axgroth4 $p |- E. y ( x e. y /\ A. z e. y E. v e. y A. w ( w C_ z ->
    w e. ( y i^i v ) ) /\ A. z ( z C_ y -> ( ( y \ z ) ~<_ z \/ z e. y ) ) ) $=
      ( vu wel cv wss wi wal wrex wa wral cdif w3a wex weq anbi2i 3bitr2i sseq1
      cdom wbr wo cin wcel axgroth3 elequ2 imbi2d albidv r19.42v elequ1 imbi12d
      cbvalvw 19.26 pm4.76 elin imbi2i bitr4i albii rexbii ralbii 3anbi2i exbii
      cbvrexvw mpbi ) ABGZDHZCHZIZDBGZJZDKZFHZVIIZFDGZJZFKZDBHZLZMZCVSNZVIVSIVS
      VIOVIUBUCCBGUDJCKZPZBQVGVJVHVSEHZUEUFZJZDKZEVSLZCVSNZWCPZBQABCDFUGWDWKBWB
      WJVGWCWAWICVSWAVMVOFEGZJZFKZEVSLZMVMWNMZEVSLWIVTWOVMVRWNDEVSDERZVQWMFWQVP
      WLVODEFUHUIUJVESVMWNEVSUKWPWHEVSWPVMVJDEGZJZDKZMVLWSMZDKWHWNWTVMWMWSFDFDR
      VOVJWLWRVNVHVIUAFDEULUMUNSVLWSDUOXAWGDXAVJVKWRMZJWGVJVKWRUPWFXBVJVHVSWEUQ
      URUSUTTVATVBVCVDVF $.
  $}

  ${
    $d x y z w v u t h g $.
    $( Lemma for ~ grothprim .  Expand the membership of an unordered pair into
       primitives.  (Contributed by NM, 29-Mar-2007.) $)
    grothprimlem $p |- ( { u , v } e. w <-> E. g ( g e. w /\ A. h
      ( h e. g <-> ( h = u \/ h = v ) ) ) ) $=
      ( cv cpr wcel weq wo cab wel wb wal wa wex dfpr2 eleq1i clabel bitri ) CF
      ZBFZGZAFZHECIEBIJZEKZUDHDALEDLUEMENODPUCUFUDEUAUBQRUEEDUDST $.

    $( The Tarski-Grothendieck Axiom ~ ax-groth expanded into set theory
       primitives using 163 symbols (allowing the defined symbols ` /\ ` ,
       ` \/ ` , ` <-> ` , and ` E. ` ).  An open problem is whether a shorter
       equivalent exists (when expanded to primitives).  (Contributed by NM,
       16-Apr-2007.) $)
    grothprim $p |- E. y ( x e. y /\ A. z ( ( z e. y -> E. v ( v e. y /\
       A. w ( A. u ( u e. w -> u e. z ) -> ( w e. y /\ w e. v ) ) ) ) /\ E. w
      ( ( w e. z -> w e. y ) -> ( A. v ( ( v e. z -> E. t A. u ( E. g ( g e. w
      /\ A. h ( h e. g <-> ( h = v \/ h = u ) ) ) -> u = t ) ) /\ ( v e. y ->
      ( v e. z \/ E. u ( u e. z /\ E. g ( g e. w /\ A. h ( h e. g <-> ( h = u
      \/ h = v ) ) ) ) ) ) ) \/ z e. y ) ) ) ) $=
      ( wel cv wcel wi wal wrex wral wo wex wa bitri wss cin cdif cdom axgroth4
      wbr w3a weq wb 3anass df-ss imbi12i albii rexbii df-rex ralbii df-ral cpr
      elin wmo vex difexi disjdifr brdom6disj orbi1i 19.44v bitr4i grothprimlem
      19.35 mobii dfmo wn eldif pm5.6 anbi12i 19.26 imbi2i exbii anbi2i mpbi )
      ABJZDKZCKZUAZWBBKZEKZUBLZMZDNZEWEOZCWEPZWCWEUAZWEWCUCZWCUDUFZCBJZQZMZCNZU
      GZBRWAWOEBJZFDJFCJZMFNZDBJZDEJSZMZDNZSERZMZDCJXCMZECJZHDJZIHJZIEUHZIFUHZQ
      UIINSHRZFGUHMFNGRZMZWTXJXAXKXLXNXMQUIINSHRZSFRZQMZSENZWOQZMZDRZSCNZSZBRAB
      CDEUEWSYFBWSWAWKWRSZSYFWAWKWRUJYGYEWAYGXHCNZYDCNZSYEWKYHWRYIWKXGCWEPYHWJX
      GCWEWJXFEWEOXGWIXFEWEWHXEDWDXBWGXDFWBWCUKWBWEWFUSULUMUNXFEWEUOTUPXGCWEUQT
      WQYDCWQXIWFFKZURWBLZFUTZEWCPZYJWFURWBLZFWCOZEWMPZSZWOQZMZDRZYDWQXIDNZYRDR
      ZMYTWLUUAWPUUBDWCWEUKWPYQDRZWOQUUBWNUUCWOEFWMWCDWEWCBVAVBCVAWCWEVCVDVEYQW
      ODVFVGULXIYRDVIVGYSYCDYRYBXIYQYAWOYQXQENZXTENZSYAYMUUDYPUUEYMXPEWCPUUDYLX
      PEWCYLXOFUTXPYKXOFDFEHIVHVJXOFGVKTUPXPEWCUQTYPWFWMLZYOMZENUUEYOEWMUQUUGXT
      EUUGWTXJVLSZXSMXTUUFUUHYOXSWFWEWCVMYOXRFWCOXSYNXRFWCDEFHIVHUNXRFWCUOTULWT
      XJXSVNTUMTVOXQXTEVPVGVEVQVRTUMVOXHYDCVPVGVSTVRVT $.
  $}

  ${
    $d w x y z $.
    $( The Tarski-Grothendieck Axiom, using abbreviations.  (Contributed by
       Mario Carneiro, 28-May-2013.) $)
    grothtsk $p |- U. Tarski = _V $=
      ( vw vx vy vz ctsk cuni cvv cv wcel wa wex cpw wss wrex wral cen wo mpbir
      wbr w3a axgroth5 wb eltskg elv anbi2i 3anass bitr4i exbii eluni vex eqriv
      2th ) AEFZGAHZUMIZUNGIUOUNBHZIZUPEIZJZBKZUTUQCHZLZUPMVBDHMDUPNJCUPOZVAUPP
      SVAUPIQCUPLOZTZBKABCDUAUSVEBUSUQVCVDJZJVEURVFUQURVFUBBCDUPGUCUDUEUQVCVDUF
      UGUHRBUNEUIRAUJULUK $.
  $}

  ${
    $d w x y z $.
    $( An equivalent to the Tarski-Grothendieck Axiom: there is a proper class
       of inaccessible cardinals.  (Contributed by Mario Carneiro,
       9-Jun-2013.) $)
    inaprc $p |- Inacc e/ _V $=
      ( vx vy vz vw cina cvv cuni con0 wss wcel ssriv wel wrex ctsk eluni2 ccrd
      cv wa sylan2 wb wnel wceq word cwina inawina winaon ssorduni ordsson mp2b
      syl vex grothtsk eleqtrri mpbi cfv c0 wne ne0i tskcard wbr tsksdom adantl
      cdm tskwe2 adantr cardsdomel mpbid eleq2 rspcev syl2an2 rexlimdvaa sylibr
      csdm mpi eqssi ssonprc ax-mp mpbir ) EFUAZEGZHUBZVTHEHIZVTUCVTHIAEHAQZEJW
      CUDJWCHJWCUEWCUFUJKZEUGVTUHUIBHVTBQZHJZBCLZCEMZWEVTJWFBDLZDNMZWHWENGZJWJW
      EFWKBUKULUMDWENOUNWFWIWHDNDQZNJZWIRZWLPUOZEJZWFWEWOJZWHWIWMWLUPUQWPWLWEUR
      WLUSSWFWNRWEWLVMUTZWQWNWRWFWEWLVAVBWNWFWLPVCJZWRWQTWMWSWIWLVDVEWEWLVFSVGW
      GWQCWOECQWOWEVHVIVJVKVNCWEEOVLKVOWBVSWATWDEVPVQVR $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Tarski map function
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c tarskiMap $.
  $( A function whose value is the smallest Tarski class
     containing a particular set. $)

  $( Extend class definition to include the map whose value is the smallest
     Tarski class. $)
  ctskm $a class tarskiMap $.

  ${
    $d x y $.
    $( A function that maps a set ` x ` to the smallest Tarski class that
       contains the set.  (Contributed by FL, 30-Dec-2010.) $)
    df-tskm $a |- tarskiMap = ( x e. _V |-> |^| { y e. Tarski | x e. y } ) $.
  $}

  ${
    $d A x y $.
    $( Value of our tarski map.  (Contributed by FL, 30-Dec-2010.)  (Revised by
       Mario Carneiro, 20-Sep-2014.) $)
    tskmval $p |- ( A e. V ->
      ( tarskiMap ` A ) = |^| { x e. Tarski | A e. x } ) $=
      ( vy wcel cvv ctsk crab cint ctskm wceq elex wrex cuni grothtsk eleqtrrdi
      cv cfv eluni2 sylib intexrab eleq1 rabbidv inteqd df-tskm fvmptg syl2anc
      ) BCEZBFEBAQZEZAGHZIZFEZBJRULKBCLZUHUJAGMZUMUHBGNZEUOUHBFUPUNOPABGSTUJAGU
      ATDBDQZUIEZAGHZIULFFJUQBKZUSUKUTURUJAGUQBUIUBUCUDDAUEUFUG $.

    $( The set ` A ` is an element of the smallest Tarski class that contains
       ` A ` .  CLASSES1 th. 5.  (Contributed by FL, 30-Dec-2010.)  (Proof
       shortened by Mario Carneiro, 21-Sep-2014.) $)
    tskmid $p |- ( A e. V -> A e. ( tarskiMap ` A ) ) $=
      ( vx wcel cv ctsk crab cint ctskm cfv wi wral id elintrabg mpbiri tskmval
      rgenw eleqtrrd ) ABDZAACEDZCFGHZAIJSAUADTTKZCFLUBCFTMQTCAFBNOCABPR $.

    $( A Tarski class that contains ` A ` is a Tarski class.  (Contributed by
       FL, 17-Apr-2011.)  (Proof shortened by Mario Carneiro, 21-Sep-2014.) $)
    tskmcl $p |- ( tarskiMap ` A ) e. Tarski $=
      ( vx cvv wcel ctskm cfv ctsk cv crab cint tskmval wss c0 ssrab2 wrex cuni
      wne id grothtsk eleqtrrdi eluni2 sylib rabn0 sylibr sylancr eqeltrd fvprc
      inttsk wn 0tsk eqeltrdi pm2.61i ) ACDZAEFZGDUMUNABHDZBGIZJZGBACKUMUPGLUPM
      QZUQGDUOBGNUMUOBGOZURUMAGPZDUSUMACUTUMRSTBAGUAUBUOBGUCUDUPUHUEUFUMUIUNMGA
      EUGUJUKUL $.
  $}

  ${
    $d A x $.  $d B x $.
    $( Being a part of ` ( tarskiMap `` A ) ` .  (Contributed by FL,
       17-Apr-2011.)  (Proof shortened by Mario Carneiro, 20-Sep-2014.) $)
    sstskm $p |- ( A e. V -> ( B C_ ( tarskiMap ` A ) <->
      A. x e. Tarski ( A e. x -> B C_ x ) ) ) $=
      ( wcel ctskm cfv wss cv ctsk cab cint wral crab tskmval df-rab inteqi wal
      wa wi eqtrdi sseq2d impexp albii ssintab df-ral 3bitr4i bitrdi ) BDEZCBFG
      ZHCAIZJEZBUKEZSZAKZLZHZUMCUKHZTZAJMZUIUJUPCUIUJUMAJNZLUPABDOVAUOUMAJPQUAU
      BUNURTZARULUSTZARUQUTVBVCAULUMURUCUDUNACUEUSAJUFUGUH $.
  $}

  ${
    $d A x $.  $d B x $.
    $( Belonging to ` ( tarskiMap `` A ) ` .  (Contributed by FL, 17-Apr-2011.)
       (Proof shortened by Mario Carneiro, 21-Sep-2014.) $)
    eltskm $p |- ( A e. V -> ( B e. ( tarskiMap ` A ) <->
      A. x e. Tarski ( A e. x -> B e. x ) ) ) $=
      ( wcel ctskm cfv cv ctsk crab cint wi wral tskmval eleq2d cvv elex tskmid
      a1i eleq2 tskmcl wceq imbi12d rspcv ax-mp syl5com syl6 wb elintrabg bitrd
      pm5.21ndd ) BDEZCBFGZEZCBAHZEZAIJKZEZUPCUOEZLZAIMZULUMUQCABDNOULCPEZURVAU
      RVBLULCUQQSULVAUNVBULBUMEZVAUNBDRUMIEVAVCUNLZLBUAUTVDAUMIUOUMUBUPVCUSUNUO
      UMBTUOUMCTUCUDUEUFCUMQUGVBURVAUHLULUPACIPUISUKUJ $.
  $}

