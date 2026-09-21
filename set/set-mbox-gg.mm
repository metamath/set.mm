$[ set-main.mm $]
$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Mathbox for Gino Giotto
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Equality theorems
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Inference versions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    rmoeqi.1 $e |- A = B $.
    $( Equality inference for restricted at-most-one quantifier.  (Contributed
       by GG, 1-Sep-2025.) $)
    rmoeqi $p |- ( E* x e. A ps <-> E* x e. B ps ) $=
      ( cv wcel wa wmo wrmo eleq2i anbi1i mobii df-rmo 3bitr4i ) BFZCGZAHZBIPDG
      ZAHZBIABCJABDJRTBQSACDPEKLMABCNABDNO $.
    $( $j usage 'rmoeqi' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    rmoeqbii.1 $e |- A = B $.
    rmoeqbii.2 $e |- ( ps <-> ch ) $.
    $( Equality inference for restricted at-most-one quantifier.  (Contributed
       by GG, 1-Sep-2025.) $)
    rmoeqbii $p |- ( E* x e. A ps <-> E* x e. B ch ) $=
      ( cv wcel wa wmo wrmo eleq2i anbi12i mobii df-rmo 3bitr4i ) CHZDIZAJZCKRE
      IZBJZCKACDLBCELTUBCSUAABDERFMGNOACDPBCEPQ $.
    $( $j usage 'rmoeqbii' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    reueqi.1 $e |- A = B $.
    $( Equality inference for restricted existential uniqueness quantifier.
       (Contributed by GG, 1-Sep-2025.) $)
    reueqi $p |- ( E! x e. A ps <-> E! x e. B ps ) $=
      ( cv wcel wa weu wreu eleq2i anbi1i eubii df-reu 3bitr4i ) BFZCGZAHZBIPDG
      ZAHZBIABCJABDJRTBQSACDPEKLMABCNABDNO $.
    $( $j usage 'reueqi' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    reueqbii.1 $e |- A = B $.
    reueqbii.2 $e |- ( ps <-> ch ) $.
    $( Equality inference for restricted existential uniqueness quantifier.
       (Contributed by GG, 1-Sep-2025.) $)
    reueqbii $p |- ( E! x e. A ps <-> E! x e. B ch ) $=
      ( cv wcel wa weu wreu eleq2i anbi12i eubii df-reu 3bitr4i ) CHZDIZAJZCKRE
      IZBJZCKACDLBCELTUBCSUAABDERFMGNOACDPBCEPQ $.
    $( $j usage 'reueqbii' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    sbceqbii.1 $e |- A = B $.
    sbceqbii.2 $e |- ( ph <-> ps ) $.
    $( Formula-building inference for class substitution.  General version of
       ~ sbcbii .  (Contributed by GG, 1-Sep-2025.) $)
    sbceqbii $p |- ( [. A / x ]. ph <-> [. B / x ]. ps ) $=
      ( cab wcel wsbc abbii eleq12i df-sbc 3bitr4i ) DACHZIEBCHZIACDJBCEJDEOPFA
      BCGKLACDMBCEMN $.
    $( $j usage 'sbceqbii' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d t x $.  $d A t $.  $d B t $.  $d C t $.
    disjeq1i.1 $e |- A = B $.
    $( Equality theorem for disjoint collection.  Inference version.
       (Contributed by GG, 1-Sep-2025.) $)
    disjeq1i $p |- ( Disj_ x e. A C <-> Disj_ x e. B C ) $=
      ( vt cv wcel wrmo wal wdisj rmoeqi albii df-disj 3bitr4i ) FGDHZABIZFJPAC
      IZFJABDKACDKQRFPABCELMAFBDNAFCDNO $.
    $( $j usage 'disjeq1i' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    disjeq12i.1 $e |- A = B $.
    disjeq12i.2 $e |- C = D $.
    $( Equality theorem for disjoint collection.  Inference version.
       (Contributed by GG, 1-Sep-2025.) $)
    disjeq12i $p |- ( Disj_ x e. A C <-> Disj_ x e. B D ) $=
      ( wdisj wceq wb disjeq2 cv wcel a1i mprg disjeq1i bitri ) ABDHZABEHZACEHD
      EIZRSJABABDEKTALBMGNOABCEFPQ $.
    $( $j usage 'disjeq12i' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    rabeqbii.1 $e |- A = B $.
    rabeqbii.2 $e |- ( ph <-> ps ) $.
    $( Equality theorem for restricted class abstractions.  Inference version.
       (Contributed by GG, 1-Sep-2025.) $)
    rabeqbii $p |- { x e. A | ph } = { x e. B | ps } $=
      ( cv wcel wa cab crab eleq2i anbi12i abbii df-rab 3eqtr4i ) CHZDIZAJZCKRE
      IZBJZCKACDLBCELTUBCSUAABDERFMGNOACDPBCEPQ $.
    $( $j usage 'rabeqbii' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d A t $.  $d B t $.  $d C t $.  $d D t $.  $d x t $.
    iuneq12i.1 $e |- A = B $.
    iuneq12i.2 $e |- C = D $.
    $( Equality theorem for indexed union.  Inference version.  (Contributed by
       GG, 1-Sep-2025.) $)
    iuneq12i $p |- U_ x e. A C = U_ x e. B D $=
      ( vt cv wcel wrex cab ciun eleq2i rexeqbii abbii df-iun 3eqtr4i ) HIZDJZA
      BKZHLSEJZACKZHLABDMACEMUAUCHTUBABCFDESGNOPAHBDQAHCEQR $.
    $( $j usage 'iuneq12i' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d A t $.  $d B t $.  $d C t $.  $d x t $.
    iineq1i.1 $e |- A = B $.
    $( Equality theorem for indexed intersection.  Inference version.
       (Contributed by GG, 1-Sep-2025.) $)
    iineq1i $p |- |^|_ x e. A C = |^|_ x e. B C $=
      ( vt cv wcel wral cab ciin eleq2i imbi1i ralbii2 abbii df-iin 3eqtr4i ) F
      GDHZABIZFJRACIZFJABDKACDKSTFRRABCAGZBHUACHRBCUAELMNOAFBDPAFCDPQ $.
    $( $j usage 'iineq1i' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d A t $.  $d B t $.  $d C t $.  $d D t $.  $d x t $.
    iineq12i.1 $e |- A = B $.
    iineq12i.2 $e |- C = D $.
    $( Equality theorem for indexed intersection.  Inference version.  General
       version of ~ iineq1i .  (Contributed by GG, 1-Sep-2025.) $)
    iineq12i $p |- |^|_ x e. A C = |^|_ x e. B D $=
      ( vt cv wcel wral cab ciin eleq2i raleqbii abbii df-iin 3eqtr4i ) HIZDJZA
      BKZHLSEJZACKZHLABDMACEMUAUCHTUBABCFDESGNOPAHBDQAHCEQR $.
    $( $j usage 'iineq12i' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    riotaeqbii.1 $e |- A = B $.
    riotaeqbii.2 $e |- ( ph <-> ps ) $.
    $( Equivalent wff's and equal domains yield equal restricted iotas.
       Inference version.  (Contributed by GG, 1-Sep-2025.) $)
    riotaeqbii $p |- ( iota_ x e. A ph ) = ( iota_ x e. B ps ) $=
      ( cv wcel wa cio crio eleq2i anbi12i iotabii df-riota 3eqtr4i ) CHZDIZAJZ
      CKREIZBJZCKACDLBCELTUBCSUAABDERFMGNOACDPBCEPQ $.
    $( $j usage 'riotaeqbii' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    riotaeqi.1 $e |- A = B $.
    $( Equal domains yield equal restricted iotas.  Inference version.
       (Contributed by GG, 1-Sep-2025.) $)
    riotaeqi $p |- ( iota_ x e. A ph ) = ( iota_ x e. B ph ) $=
      ( biid riotaeqbii ) AABCDEAFG $.
    $( $j usage 'riotaeqi' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d A f $.  $d B f $.  $d C f $.  $d x f $.
    ixpeq1i.1 $e |- A = B $.
    $( Equality inference for infinite Cartesian product.  (Contributed by GG,
       1-Sep-2025.) $)
    ixpeq1i $p |- X_ x e. A C = X_ x e. B C $=
      ( vf cv wcel cab wfn cfv wral wa cixp eleq2i fneq2i imbi1i ralbii2 df-ixp
      abbii anbi12i 3eqtr4i ) FGZAGZBHZAIZJZUDUCKDHZABLZMZFIUCUDCHZAIZJZUHACLZM
      ZFIABDNACDNUJUOFUGUMUIUNUFULUCUEUKABCUDEOZTPUHUHABCUEUKUHUPQRUATABDFSACDF
      SUB $.
    $( $j usage 'ixpeq1i' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    ixpeq12i.1 $e |- A = B $.
    ixpeq12i.2 $e |- C = D $.
    $( Equality inference for infinite Cartesian product.  (Contributed by GG,
       1-Sep-2025.) $)
    ixpeq12i $p |- X_ x e. A C = X_ x e. B D $=
      ( cixp wceq wral rgenw ixpeq2 ax-mp ixpeq1i eqtri ) ABDHZABEHZACEHDEIZABJ
      PQIRABGKABDELMABCEFNO $.
    $( $j usage 'ixpeq12i' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d A x m n f $.  $d B x m n f $.  $d C x m n f $.  $d k x m n f $.
    sumeq2si.1 $e |- B = C $.
    $( Equality inference for sum.  (Contributed by GG, 1-Sep-2025.) $)
    sumeq2si $p |- sum_ k e. A B = sum_ k e. A C $=
      ( vm vn vx vf cv cfv caddc cz csb cmpt cseq wa wrex cn wceq cuz wss c1 co
      wcel cc0 cif cli wbr cfz wf1o wex wo cio csu csbeq2i ifeq1 mpteq2i seqeq3
      ax-mp breq1i anbi2i rexbii fveq1i eqeq2i orbi12i iotabii df-sum 3eqtr4i
      exbii ) AFJZUAKUBZLGMGJZAUEZDVMBNZUFUGZOZVKPZHJZUHUIZQZFMRZUCVKUJUDAIJZUK
      ZVSVKLGSDVMWCKZBNZOZUCPZKZTZQZIULZFSRZUMZHUNVLLGMVNDVMCNZUFUGZOZVKPZVSUHU
      IZQZFMRZWDVSVKLGSDWECNZOZUCPZKZTZQZIULZFSRZUMZHUNABDUOACDUOWNXJHWBXAWMXIW
      AWTFMVTWSVLVRWRVSUHVQWQTVRWRTGMVPWPVOWOTVPWPTDVMBCEUPVNVOWOUFUQUTURLVQWQV
      KUSUTVAVBVCWLXHFSWKXGIWJXFWDWIXEVSVKWHXDWGXCTWHXDTGSWFXBDWEBCEUPURLWGXCUC
      USUTVDVEVBVJVCVFVGHABIDFGVHHACIDFGVHVI $.
    $( $j usage 'sumeq2si' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    sumeq12si.1 $e |- A = B $.
    sumeq12si.2 $e |- C = D $.
    $( Equality inference for sum.  General version of ~ sumeq2si .
       (Contributed by GG, 1-Sep-2025.) $)
    sumeq12si $p |- sum_ x e. A C = sum_ x e. B D $=
      ( csu sumeq1i sumeq2si eqtri ) BDAHCDAHCEAHBCDAFICDEAGJK $.
    $( $j usage 'sumeq12si' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d A x m n y f $.  $d B x m n y f $.  $d C x m n y f $.  $d k x m n y f $.
    prodeq2si.1 $e |- B = C $.
    $( Equality inference for product.  (Contributed by GG, 1-Sep-2025.) $)
    prodeq2si $p |- prod_ k e. A B = prod_ k e. A C $=
      ( vm vy vn vx vf cv cfv cmul cz c1 cseq cli wrex cn wceq cuz wss cc0 wcel
      wne cif cmpt wbr wa wex w3a cfz co wf1o csb wo cio cprod biid ifeq1 ax-mp
      mpteq2i seqeq3 breq1i anbi2i exbii rexbii 3anbi123i csbeq2i fveq1i eqeq2i
      orbi12i iotabii df-prod 3eqtr4i ) AFKZUALZUBZGKZUCUEZMDNDKAUDZBOUFZUGZHKZ
      PZVSQUHZUIZGUJZHVQRZMWCVPPZIKZQUHZUKZFNRZOVPULUMAJKZUNZWKVPMHSDWDWOLZBUOZ
      UGZOPZLZTZUIZJUJZFSRZUPZIUQVRVTMDNWACOUFZUGZWDPZVSQUHZUIZGUJZHVQRZMXHVPPZ
      WKQUHZUKZFNRZWPWKVPMHSDWQCUOZUGZOPZLZTZUIZJUJZFSRZUPZIUQABDURACDURXFYFIWN
      XQXEYEWMXPFNVRVRWIXMWLXOVRUSWHXLHVQWGXKGWFXJVTWEXIVSQWCXHTZWEXITDNWBXGBCT
      WBXGTEWABCOUTVAVBZMWCXHWDVCVAVDVEVFVGWJXNWKQYGWJXNTYHMWCXHVPVCVAVDVHVGXDY
      DFSXCYCJXBYBWPXAYAWKVPWTXTWSXSTWTXTTHSWRXRDWQBCEVIVBMWSXSOVCVAVJVKVEVFVGV
      LVMIGABJDFHVNIGACJDFHVNVO $.
    $( $j usage 'prodeq2si' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    prodeq12si.1 $e |- A = B $.
    prodeq12si.2 $e |- C = D $.
    $( Equality inference for product.  General version of ~ prodeq2si .
       (Contributed by GG, 1-Sep-2025.) $)
    prodeq12si $p |- prod_ x e. A C = prod_ x e. B D $=
      ( cprod prodeq1i prodeq2si eqtri ) BDAHCDAHCEAHBCDAFICDEAGJK $.
    $( $j usage 'prodeq12si' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d A k y $.  $d B k y $.  $d C k y $.  $d D k y $.  $d x k y $.
    itgeq12i.1 $e |- A = B $.
    itgeq12i.2 $e |- C = D $.
    $( Equality inference for an integral.  General version of ~ itgeq1i and
       ~ itgeq2i .  (Contributed by GG, 1-Sep-2025.) $)
    itgeq12i $p |- S. A C _d x = S. B D _d x $=
      ( vk vy cc0 co cv cr cdiv cre cfv wa csb citg2 cmul cfz cexp wcel cle wbr
      c3 ci cif cmpt csu citg wceq wal oveq1i fveq2i eleq2i anbi1i ax-mp ax-gen
      wb pm3.2i csbeq2 csbeq1 sylan9eqr mpteq2i oveq2i sumeq2si df-itg 3eqtr4i
      ifbi ) JUFUAKZUGHLUBKZAMIDVLNKZOPZALZBUCZJILZUDUEZQZVQJUHZRZUIZSPZTKZHUJV
      KVLAMIEVLNKZOPZVOCUCZVRQZVQJUHZRZUIZSPZTKZHUJABDUKACEUKVKWDWMHWCWLVLTWBWK
      SAMWAWJVNWFULZVTWIULZIUMZQWAWJULWNWPVMWEODEVLNGUNUOWOIVSWHUTWOVPWGVRBCVOF
      UPUQVSWHVQJVJURUSVAWPWNWAIVNWIRWJIVNVTWIVBIVNWFWIVCVDURVEUOVFVGAIBDHVHAIC
      EHVHVI $.
    $( $j usage 'itgeq12i' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    itgeq1i.1 $e |- A = B $.
    $( Equality inference for an integral.  (Contributed by GG, 1-Sep-2025.) $)
    itgeq1i $p |- S. A C _d x = S. B C _d x $=
      ( eqid itgeq12i ) ABCDDEDFG $.
    $( $j usage 'itgeq1i' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    itgeq2i.1 $e |- B = C $.
    $( Equality inference for an integral.  (Contributed by GG, 1-Sep-2025.) $)
    itgeq2i $p |- S. A B _d x = S. A C _d x $=
      ( eqid itgeq12i ) ABBCDBFEG $.
    $( $j usage 'itgeq2i' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    ditgeq123i.1 $e |- A = B $.
    ditgeq123i.2 $e |- C = D $.
    ditgeq123i.3 $e |- E = F $.
    $( Equality inference for the directed integral.  General version of
       ~ ditgeq12i and ~ ditgeq3i .  (Contributed by GG, 1-Sep-2025.) $)
    ditgeq123i $p |- S_ [ A -> C ] E _d x = S_ [ B -> D ] F _d x $=
      ( cle wbr cioo co citg cneg cif cdit oveq12i itgeq12i breq12i ifbieq12i
      negeqi df-ditg 3eqtr4i ) BDKLZABDMNZFOZADBMNZFOZPZQCEKLZACEMNZGOZAECMNZGO
      ZPZQABDFRACEGRUFULUHUKUNUQBCDEKHIUAAUGUMFGBCDEMHISJTUJUPAUIUOFGDEBCMIHSJT
      UCUBABDFUDACEGUDUE $.
   $( $j usage 'ditgeq123i' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    ditgeq12i.1 $e |- A = B $.
    ditgeq12i.2 $e |- C = D $.
    $( Equality inference for the directed integral.  (Contributed by GG,
       1-Sep-2025.) $)
    ditgeq12i $p |- S_ [ A -> C ] E _d x = S_ [ B -> D ] E _d x $=
      ( eqid ditgeq123i ) ABCDEFFGHFIJ $.
    $( $j usage 'ditgeq12i' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    ditgeq3i.1 $e |- C = D $.
    $( Equality inference for the directed integral.  (Contributed by GG,
       1-Sep-2025.) $)
    ditgeq3i $p |- S_ [ A -> B ] C _d x = S_ [ A -> B ] D _d x $=
      ( eqid ditgeq123i ) ABBCCDEBGCGFH $.
    $( $j usage 'ditgeq3i' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Deduction versions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d A x $.  $d B x $.
    rmoeqdv.1 $e |- ( ph -> A = B ) $.
    $( Formula-building rule for restricted at-most-one quantifier.  Deduction
       form.  (Contributed by GG, 1-Sep-2025.) $)
    rmoeqdv $p |- ( ph -> ( E* x e. A ps <-> E* x e. B ps ) ) $=
      ( wceq wrmo wb rmoeq1 syl ) ADEGBCDHBCEHIFBCDEJK $.
    $( $j usage 'rmoeqdv' avoids 'ax-8' 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d ph x $.
    rmoeqbidv.1 $e |- ( ph -> A = B ) $.
    rmoeqbidv.2 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for restricted at-most-one quantifier.  Deduction
       form.  General version of ~ rmobidv .  (Contributed by GG,
       1-Sep-2025.) $)
    rmoeqbidv $p |- ( ph -> ( E* x e. A ps <-> E* x e. B ch ) ) $=
      ( cv wcel wa wmo wrmo eleq2d anbi12d mobidv df-rmo 3bitr4g ) ADIZEJZBKZDL
      SFJZCKZDLBDEMCDFMAUAUCDATUBBCAEFSGNHOPBDEQCDFQR $.
    $( $j usage 'rmoeqbidv' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d ph x t $.  $d ps t $.  $d ch t $.  $d t u $.  $d t v $.
    sbequbidv.1 $e |- ( ph -> u = v ) $.
    sbequbidv.2 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Deduction substituting both sides of a biconditional.  (Contributed by
       GG, 1-Sep-2025.) $)
    sbequbidv $p |- ( ph -> ( [ u / x ] ps <-> [ v / x ] ch ) ) $=
      ( vt weq wi wal wsb wb equequ2 syl imbi2d albidv imbi12d dfsb 3bitr4g ) A
      IFJZDIJZBKZDLZKZILIEJZUCCKZDLZKZILBDFMCDEMAUFUJIAUBUGUEUIAFEJUBUGNGFEIOPA
      UDUHDABCUCHQRSRBDIFTCDIETUA $.
    $( $j usage 'sbequbidv' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d ph x t $.  $d A t $.  $d B t $.  $d C t $.
    disjeq12dv.1 $e |- ( ph -> A = B ) $.
    disjeq12dv.2 $e |- ( ph -> C = D ) $.
    $( Equality theorem for disjoint collection.  Deduction version.
       (Contributed by GG, 1-Sep-2025.) $)
    disjeq12dv $p |- ( ph -> ( Disj_ x e. A C <-> Disj_ x e. B D ) ) $=
      ( vt wdisj cv wcel wrmo wal wa wmo eleq2d df-rmo 3bitr4g df-disj anbi1d
      mobidv albidv wceq adantr disjeq2dv bitrd ) ABCEJZBDEJZBDFJAIKELZBCMZINUJ
      BDMZINUHUIAUKULIABKZCLZUJOZBPUMDLZUJOZBPUKULAUOUQBAUNUPUJACDUMGQUAUBUJBCR
      UJBDRSUCBICETBIDETSABDEFAEFUDUPHUEUFUG $.
    $( $j usage 'disjeq12dv' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d ph x t $.  $d A t $.  $d B t $.  $d C t $.
    ixpeq12dv.1 $e |- ( ph -> A = B ) $.
    ixpeq12dv.2 $e |- ( ph -> C = D ) $.
    $( Equality theorem for infinite Cartesian product.  Deduction version.
       (Contributed by GG, 1-Sep-2025.) $)
    ixpeq12dv $p |- ( ph -> X_ x e. A C = X_ x e. B D ) $=
      ( vt cixp cv wcel cab wfn wral wa abbidv wi wal df-ral cfv eleq2d 3bitr4g
      fneq2d imbi1d albidv anbi12d df-ixp 3eqtr4g ixpeq2dv eqtrd ) ABCEJZBDEJZB
      DFJAIKZBKZCLZBMZNZUOUNUAELZBCOZPZIMUNUODLZBMZNZUSBDOZPZIMULUMAVAVFIAURVDU
      TVEAUQVCUNAUPVBBACDUOGUBZQUDAUPUSRZBSVBUSRZBSUTVEAVHVIBAUPVBUSVGUEUFUSBCT
      USBDTUCUGQBCEIUHBDEIUHUIABDEFHUJUK $.
    $( $j usage 'ixpeq12dv' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d ph k $.
    sumeq12sdv.1 $e |- ( ph -> A = B ) $.
    sumeq12sdv.2 $e |- ( ph -> C = D ) $.
    $( Equality deduction for sum.  General version of ~ sumeq2sdv .
       (Contributed by GG, 1-Sep-2025.) $)
    sumeq12sdv $p |- ( ph -> sum_ k e. A C = sum_ k e. B D ) $=
      ( csu sumeq1d sumeq2sdv eqtrd ) ABDFICDFICEFIABCDFGJACDEFHKL $.
    $( $j usage 'sumeq12sdv' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d A x m n y f $.  $d B x m n y f $.  $d C x m n y f $.
    $d ph k x m n y f $.
    prodeq12sdv.1 $e |- ( ph -> A = B ) $.
    prodeq12sdv.2 $e |- ( ph -> C = D ) $.
    $( Equality deduction for product.  General version of ~ prodeq2sdv .
       (Contributed by GG, 1-Sep-2025.) $)
    prodeq12sdv $p |- ( ph -> prod_ k e. A C = prod_ k e. B D ) $=
      ( vm vy vn vx vf cv cmul cz c1 cseq cli wrex cuz cfv wss cc0 wne wcel cif
      cprod cmpt wbr wa wex w3a cfz co wf1o cn csb wceq cio sseq1d eleq2d ifbid
      wo mpteq2dv seqeq3d breq1d anbi2d exbidv rexbidv 3anbi123d f1oeq3d anbi1d
      orbi12d iotabidv df-prod 3eqtr4g prodeq2sdv eqtrd ) ABDFUHZCDFUHZCEFUHABI
      NZUAUBZUCZJNZUDUEZOFPFNZBUFZDQUGZUIZKNZRZWESUJZUKZJULZKWCTZOWJWBRZLNZSUJZ
      UMZIPTZQWBUNUOZBMNZUPZWRWBOKUQFWKXCUBDURUIQRUBUSZUKZMULZIUQTZVDZLUTCWCUCZ
      WFOFPWGCUFZDQUGZUIZWKRZWESUJZUKZJULZKWCTZOXMWBRZWRSUJZUMZIPTZXBCXCUPZXEUK
      ZMULZIUQTZVDZLUTVTWAAXIYGLAXAYBXHYFAWTYAIPAWDXJWPXRWSXTABCWCGVAAWOXQKWCAW
      NXPJAWMXOWFAWLXNWESAWJXMOWKAFPWIXLAWHXKDQABCWGGVBVCVEZVFVGVHVIVJAWQXSWRSA
      WJXMOWBYHVFVGVKVJAXGYEIUQAXFYDMAXDYCXEABCXBXCGVLVMVIVJVNVOLJBDMFIKVPLJCDM
      FIKVPVQACDEFHVRVS $.
    $( $j usage 'prodeq12sdv' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d ph x k y $.  $d A k y $.  $d B k y $.  $d C k y $.  $d D k y $.
    itgeq12sdv.1 $e |- ( ph -> A = B ) $.
    itgeq12sdv.2 $e |- ( ph -> C = D ) $.
    $( Equality theorem for an integral.  Deduction form.  General version of
       ~ itgeq1d and ~ itgeq2sdv .  (Contributed by GG, 1-Sep-2025.) $)
    itgeq12sdv $p |- ( ph -> S. A C _d x = S. B D _d x ) $=
      ( vk vy cc0 co cv cr cdiv cre cfv wcel citg2 cmul c3 cfz cexp cle wbr cif
      ci csb cmpt csu citg oveq1d fveq2d eleq2d anbi1d ifbid csbeq12dv mpteq2dv
      wa oveq2d sumeq2sdv df-itg 3eqtr4g ) AKUAUBLZUGIMUCLZBNJEVEOLZPQZBMZCRZKJ
      MZUDUEZUSZVJKUFZUHZUIZSQZTLZIUJVDVEBNJFVEOLZPQZVHDRZVKUSZVJKUFZUHZUIZSQZT
      LZIUJBCEUKBDFUKAVDVQWFIAVPWEVETAVOWDSABNVNWCAJVGVMVSWBAVFVRPAEFVEOHULUMAV
      LWAVJKAVIVTVKACDVHGUNUOUPUQURUMUTVABJCEIVBBJDFIVBVC $.
    $( $j usage 'itgeq12sdv' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d ph x $.
    itgeq2sdv.1 $e |- ( ph -> B = C ) $.
    $( Equality theorem for an integral.  Deduction form.  (Contributed by GG,
       1-Sep-2025.) $)
    itgeq2sdv $p |- ( ph -> S. A B _d x = S. A C _d x ) $=
      ( eqidd itgeq12sdv ) ABCCDEACGFH $.
    $( $j usage 'itgeq2sdv' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d ph x $.
    ditgeq123dv.1 $e |- ( ph -> A = B ) $.
    ditgeq123dv.2 $e |- ( ph -> C = D ) $.
    ditgeq123dv.3 $e |- ( ph -> E = F ) $.
    $( Equality theorem for the directed integral.  Deduction form.  General
       version of ~ ditgeq3sdv .  (Contributed by GG, 1-Sep-2025.) $)
    ditgeq123dv $p |- ( ph -> S_ [ A -> C ] E _d x = S_ [ B -> D ] F _d x ) $=
      ( cle wbr cioo co citg cneg cif cdit oveq12d breq12d itgeq12sdv ifbieq12d
      negeqd df-ditg 3eqtr4g ) ACELMZBCENOZGPZBECNOZGPZQZRDFLMZBDFNOZHPZBFDNOZH
      PZQZRBCEGSBDFHSAUGUMUIULUOURACDEFLIJUAABUHUNGHACDEFNIJTKUBAUKUQABUJUPGHAE
      FCDNJITKUBUDUCBCEGUEBDFHUEUF $.
    $( $j usage 'ditgeq123dv' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d A x $.  $d B x $.  $d C x $.  $d D x $.
    ditgeq12d.1 $e |- ( ph -> A = B ) $.
    ditgeq12d.2 $e |- ( ph -> C = D ) $.
    $( Equality theorem for the directed integral.  Deduction form.
       (Contributed by GG, 1-Sep-2025.) $)
    ditgeq12d $p |- ( ph -> S_ [ A -> C ] E _d x = S_ [ B -> D ] E _d x ) $=
      ( wceq cdit ditgeq1 ditgeq2 sylan9eq syl2anc ) ACDJZEFJZBCEGKZBDFGKZJHIPQ
      RBDEGKSBCDEGLBEFDGMNO $.
    $( $j usage 'ditgeq12d' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d ph x $.
    ditgeq3sdv.1 $e |- ( ph -> C = D ) $.
    $( Equality theorem for the directed integral.  Deduction form.
       (Contributed by GG, 1-Sep-2025.) $)
    ditgeq3sdv $p |- ( ph -> S_ [ A -> B ] C _d x = S_ [ A -> B ] D _d x ) $=
      ( eqidd ditgeq123dv ) ABCCDDEFACHADHGI $.
    $( $j usage 'ditgeq3sdv' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Change bound variables
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x t w $.  $d y t w $.  $d z t w $.
    $( A proof of ~ ax-8 that does not rely on ~ ax-8 .  It employs ~ df-in to
       perform alpha-renaming and eliminates disjoint variable conditions using
       ~ ax-9 .  Since the nature of this result is unclear, usage of this
       theorem is discouraged, and this method should not be applied to
       eliminate axiom dependencies.  (Contributed by GG, 1-Aug-2025.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    in-ax8 $p |- ( x = y -> ( x e. z -> y e. z ) ) $=
      ( vt vw weq wel wi wa wal wsb sb6 cv cab wcel df-in df-clab equcoms ax6ev
      exlimiiv ax7 ax12v2 imp wb wceq cin eqtr3i dfcleq mpbi spi 3bitr3i bitr3i
      sylbb sp 3syl ex com23 sylcom com12 pm4.24 3imtr4g ax9 imim12d syl5 ) DCF
      ZABFZACGZBCGZHZHDVFADGZBDGZHVEVIVFVJVJIZVKVKIZVJVKEAFVFVLVMHZHZEVOAEVFAEF
      ZVNVFVPBEFZVNABEUAVPVLVQVMVPVLVQVMHZVPVLIVPVLHAJZVRBJZVRVPVLVSVLAEUBUCVSV
      MBEKZVTVSVLAEKZWAVLAELEMZVLANZOZWCVMBNZOZWBWAWEWGUDZEWDWFUEWHEJDMZWIUFWDW
      FAWIWIPBWIWIPUGEWDWFUHUIUJVLEAQVMEBQUKULVMBELUMVRBUNUOUPUQURUSREASTVJUTVK
      UTVAVEVGVJVKVHVGVJHCDCDAVBRDCBVBVCVDDCST $.
    $( $j usage 'in-ax8' avoids 'ax-8' 'df-clel'; $)
  $}

  ${
    $d x t w v $.  $d y t w v $.  $d z t w v $.
    $( A proof of ~ ax-8 that does not rely on ~ ax-8 .  It employs ~ df-ss to
       perform alpha-renaming and eliminates disjoint variable conditions using
       ~ ax-9 .  Contrary to ~ in-ax8 , this proof does not rely on ~ df-cleq ,
       therefore using fewer axioms .  This method should not be applied to
       eliminate axiom dependencies.  (Contributed by GG, 30-Aug-2025.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    ss-ax8 $p |- ( x = y -> ( x e. z -> y e. z ) ) $=
      ( vt vw vv weq wel wi wal wsb equsb3 bicomi imbi1i albii cv df-clab df-ss
      wcel 3bitri ax7 wa ax12v2 imp cab wss bitr3i biimpi sp com23 sylcom com12
      3syl ex equcoms ax6ev exlimiiv ax9 imim12d syl5 ) DCGZABGZACHZBCHZIZIDVBA
      DHZBDHZIZVAVEEAGVBVHIZEVIAEVBAEGZVHVBVJBEGZVHABEUAVJVFVKVGVJVFVKVGIZVJVFU
      BVJVFIZAJZVLBJZVLVJVFVNVFAEUCUDVNVOVNFEGZFAKZVFIZAJZVPFBKZVGIZBJZVOVMVRAV
      JVQVFVQVJFAELMNOVSAPZVPFUEZSZVFIZAJBPZWDSZVGIZBJWBVRWFAVQWEVFWEVQVPAFQMNO
      WEWCDPZSIAJWDWJUFWHWGWJSIBJAWDWJRBWDWJRUGWIWABWHVTVGVPBFQNOTWAVLBVTVKVGFB
      ELNOTUHVLBUIUMUNUJUKULUOEAUPUQVAVCVFVGVDVCVFICDCDAURUODCBURUSUTDCUPUQ $.
    $( $j usage 'ss-ax8' avoids 'ax-8' 'ax-ext' 'df-clel' 'df-cleq'; $)
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Change bound variables and domains
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d x y $.  $d ph y $.  $d ps x $.  $d A y $.  $d B x $.
    cbvralvw2.1 $e |- ( x = y -> A = B ) $.
    cbvralvw2.2 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Change bound variable and domain in the restricted universal quantifier,
       using implicit substitution.  (Contributed by GG, 14-Aug-2025.) $)
    cbvralvw2 $p |- ( A. x e. A ph <-> A. y e. B ps ) $=
      ( cv wcel wi wal wral weq eleq1w eleq2d bitrd imbi12d cbvalvw df-ral
      3bitr4i ) CIEJZAKZCLDIZFJZBKZDLACEMBDFMUCUFCDCDNZUBUEABUGUBUDEJUECDEOUGEF
      UDGPQHRSACETBDFTUA $.
    $( $j usage 'cbvralvw2' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d x y $.  $d ph y $.  $d ps x $.  $d A y $.  $d B x $.
    cbvrexvw2.1 $e |- ( x = y -> A = B ) $.
    cbvrexvw2.2 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Change bound variable and domain in the restricted existential
       quantifier, using implicit substitution.  (Contributed by GG,
       14-Aug-2025.) $)
    cbvrexvw2 $p |- ( E. x e. A ph <-> E. y e. B ps ) $=
      ( cv wcel wa wex wrex weq eleq1w eleq2d bitrd anbi12d cbvexvw df-rex
      3bitr4i ) CIEJZAKZCLDIZFJZBKZDLACEMBDFMUCUFCDCDNZUBUEABUGUBUDEJUECDEOUGEF
      UDGPQHRSACETBDFTUA $.
    $( $j usage 'cbvrexvw2' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d x y $.  $d ph y $.  $d ps x $.  $d A y $.  $d B x $.
    cbvrmovw2.1 $e |- ( x = y -> A = B ) $.
    cbvrmovw2.2 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Change bound variable and domain in the restricted at-most-one
       quantifier, using implicit substitution.  (Contributed by GG,
       14-Aug-2025.) $)
    cbvrmovw2 $p |- ( E* x e. A ph <-> E* y e. B ps ) $=
      ( cv wcel wa wmo wrmo weq eleq1w eleq2d bitrd anbi12d cbvmovw df-rmo
      3bitr4i ) CIEJZAKZCLDIZFJZBKZDLACEMBDFMUCUFCDCDNZUBUEABUGUBUDEJUECDEOUGEF
      UDGPQHRSACETBDFTUA $.
    $( $j usage 'cbvrmovw2' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d x y $.  $d ph y $.  $d ps x $.  $d A y $.  $d B x $.
    cbvreuvw2.1 $e |- ( x = y -> A = B ) $.
    cbvreuvw2.2 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Change bound variable and domain in the restricted existential
       uniqueness quantifier, using implicit substitution.  (Contributed by GG,
       14-Aug-2025.) $)
    cbvreuvw2 $p |- ( E! x e. A ph <-> E! y e. B ps ) $=
      ( cv wcel wa weu wreu weq eleq1w eleq2d bitrd anbi12d cbveuvw df-reu
      3bitr4i ) CIEJZAKZCLDIZFJZBKZDLACEMBDFMUCUFCDCDNZUBUEABUGUBUDEJUECDEOUGEF
      UDGPQHRSACETBDFTUA $.
    $( $j usage 'cbvreuvw2' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d x y $.  $d ph y $.  $d ps x $.
    cbvsbcvw2.1 $e |- A = B $.
    cbvsbcvw2.2 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Change bound variable of a class substitution using implicit
       substitution.  General version of ~ cbvsbcvw .  (Contributed by GG,
       1-Sep-2025.) $)
    cbvsbcvw2 $p |- ( [. A / x ]. ph <-> [. B / y ]. ps ) $=
      ( cab wcel wsbc cbvabv eleq12i df-sbc 3bitr4i ) EACIZJFBDIZJACEKBDFKEFPQG
      ABCDHLMACENBDFNO $.
    $( $j usage 'cbvsbcvw2' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d x y $.  $d A t $.  $d B t $.  $d C y t $.  $d D x t $.
    cbvcsbvw2.1 $e |- A = B $.
    cbvcsbvw2.2 $e |- ( x = y -> C = D ) $.
    $( Change bound variable of a proper substitution into a class using
       implicit substitution.  General version of ~ cbvcsbv .  (Contributed by
       GG, 1-Sep-2025.) $)
    cbvcsbvw2 $p |- [_ A / x ]_ C = [_ B / y ]_ D $=
      ( vt cv wcel wsbc cab csb weq eleq2d cbvsbcvw2 abbii df-csb 3eqtr4i ) IJZ
      EKZACLZIMUAFKZBDLZIMACENBDFNUCUEIUBUDABCDGABOEFUAHPQRAICESBIDFST $.
    $( $j usage 'cbvcsbvw2' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d x y $.  $d A y t $.  $d B x t $.  $d C y t $.  $d D x t $.
    cbviunvw2.1 $e |- ( x = y -> C = D ) $.
    cbviunvw2.2 $e |- ( x = y -> A = B ) $.
    $( Change bound variable and domain in indexed unions, using implicit
       substitution.  (Contributed by GG, 14-Aug-2025.) $)
    cbviunvw2 $p |- U_ x e. A C = U_ y e. B D $=
      ( vt cv wcel wrex cab ciun weq eleq2d cbvrexvw2 abbii df-iun 3eqtr4i ) IJ
      ZEKZACLZIMUAFKZBDLZIMACENBDFNUCUEIUBUDABCDHABOEFUAGPQRAICESBIDFST $.
    $( $j usage 'cbviunvw2' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d x y $.  $d A y t $.  $d B x t $.  $d C y t $.  $d D x t $.
    cbviinvw2.1 $e |- ( x = y -> C = D ) $.
    cbviinvw2.2 $e |- ( x = y -> A = B ) $.
    $( Change bound variable and domain in an indexed intersection, using
       implicit substitution.  (Contributed by GG, 14-Aug-2025.) $)
    cbviinvw2 $p |- |^|_ x e. A C = |^|_ y e. B D $=
      ( vt cv wcel wral cab ciin weq eleq2d cbvralvw2 abbii df-iin 3eqtr4i ) IJ
      ZEKZACLZIMUAFKZBDLZIMACENBDFNUCUEIUBUDABCDHABOEFUAGPQRAICESBIDFST $.
    $( $j usage 'cbviinvw2' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d x y $.  $d A y t $.  $d B x t $.  $d C y t $.  $d D x t $.
    cbvmptvw2.1 $e |- ( x = y -> C = D ) $.
    cbvmptvw2.2 $e |- ( x = y -> A = B ) $.
    $( Change bound variable and domain in a maps-to function, using implicit
       substitution.  (Contributed by GG, 14-Aug-2025.) $)
    cbvmptvw2 $p |- ( x e. A |-> C ) = ( y e. B |-> D ) $=
      ( vt cv wcel wceq wa copab cmpt weq eleq1w eleq2d bitrd df-mpt cbvopab1v
      eqeq2d anbi12d 3eqtr4i ) AJCKZIJZELZMZAINBJZDKZUFFLZMZBINACEOBDFOUHULAIBA
      BPZUEUJUGUKUMUEUICKUJABCQUMCDUIHRSUMEFUFGUBUCUAAICETBIDFTUD $.
    $( $j usage 'cbvmptvw2' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d x y $.  $d A y t $.  $d B x t $.  $d C y t $.  $d D x t $.
    cbvdisjvw2.1 $e |- ( x = y -> C = D ) $.
    cbvdisjvw2.2 $e |- ( x = y -> A = B ) $.
    $( Change bound variable and domain in a disjoint collection, using
       implicit substitution.  (Contributed by GG, 14-Aug-2025.) $)
    cbvdisjvw2 $p |- ( Disj_ x e. A C <-> Disj_ y e. B D ) $=
      ( vt cv wcel wrmo wal wdisj weq eleq2d cbvrmovw2 albii df-disj 3bitr4i )
      IJZEKZACLZIMUAFKZBDLZIMACENBDFNUCUEIUBUDABCDHABOEFUAGPQRAICESBIDFST $.
    $( $j usage 'cbvdisjvw2' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d x y $.  $d ph y $.  $d ps x $.  $d A y $.  $d B x $.
    cbvriotavw2.1 $e |- ( x = y -> A = B ) $.
    cbvriotavw2.2 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Change bound variable and domain in a restricted description binder,
       using implicit substitution.  (Contributed by GG, 14-Aug-2025.) $)
    cbvriotavw2 $p |- ( iota_ x e. A ph ) = ( iota_ y e. B ps ) $=
      ( cv wcel wa cio crio weq id eleq12d anbi12d cbviotavw df-riota 3eqtr4i )
      CIZEJZAKZCLDIZFJZBKZDLACEMBDFMUCUFCDCDNZUBUEABUGUAUDEFUGOGPHQRACESBDFST
      $.
    $( $j usage 'cbvriotavw2' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d x y w t $.  $d x z w t $.  $d ps w t $.  $d ch x t $.
    cbvoprab1vw.1 $e |- ( x = w -> ( ps <-> ch ) ) $.
    $( Change the first bound variable in an operation abstraction, using
       implicit substitution.  (Contributed by GG, 14-Aug-2025.) $)
    cbvoprab1vw $p |- { <. <. x , y >. , z >. | ps } =
                      { <. <. w , y >. , z >. | ch } $=
      ( vt cv cop wceq wa wex cab coprab weq opeq1 opeq1d eqeq2d df-oprab abbii
      anbi12d 2exbidv cbvexvw 3eqtr4i ) HIZCIZDIZJZEIZJZKZALZEMDMZCMZHNUFFIZUHJ
      ZUJJZKZBLZEMDMZFMZHNACDEOBFDEOUOVBHUNVACFCFPZUMUTDEVCULUSABVCUKURUFVCUIUQ
      UJUGUPUHQRSGUBUCUDUAACDEHTBFDEHTUE $.
    $( $j usage 'cbvoprab1vw' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d x y w t $.  $d y z w t $.  $d ps w t $.  $d ch y t $.
    cbvoprab2vw.1 $e |- ( y = w -> ( ps <-> ch ) ) $.
    $( Change the second bound variable in an operation abstraction, using
       implicit substitution.  (Contributed by GG, 14-Aug-2025.) $)
    cbvoprab2vw $p |- { <. <. x , y >. , z >. | ps } =
                      { <. <. x , w >. , z >. | ch } $=
      ( vt cv cop wceq wa wex cab coprab weq opeq2 opeq1d eqeq2d df-oprab exbii
      anbi12d exbidv cbvexvw abbii 3eqtr4i ) HIZCIZDIZJZEIZJZKZALZEMZDMZCMZHNUG
      UHFIZJZUKJZKZBLZEMZFMZCMZHNACDEOBCFEOUQVEHUPVDCUOVCDFDFPZUNVBEVFUMVAABVFU
      LUTUGVFUJUSUKUIURUHQRSGUBUCUDUAUEACDEHTBCFEHTUF $.
    $( $j usage 'cbvoprab2vw' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d x y z w u v t $.  $d ps w u v t $.  $d ch x y z t $.
    cbvoprab123vw.1 $e |- ( ( ( x = w /\ y = u ) /\ z = v ) ->
                                                             ( ps <-> ch ) ) $.
    $( Change all bound variables in an operation abstraction, using implicit
       substitution.  (Contributed by GG, 14-Aug-2025.) $)
    cbvoprab123vw $p |- { <. <. x , y >. , z >. | ps } =
                        { <. <. w , u >. , v >. | ch } $=
      ( vt cv cop wceq wa wex cab coprab weq opeq12d df-oprab anbi12d cbvexdvaw
      simpll simplr simpr eqeq2d cbvex2vw abbii 3eqtr4i ) JKZCKZDKZLZEKZLZMZANZ
      EOZDOCOZJPUJFKZHKZLZGKZLZMZBNZGOZHOFOZJPACDEQBFHGQUSVHJURVGCDFHCFRZDHRZNZ
      UQVFEGVKEGRZNZUPVEABVMUOVDUJVMUMVBUNVCVMUKUTULVAVIVJVLUCVIVJVLUDSVKVLUESU
      FIUAUBUGUHACDEJTBFHGJTUI $.
    $( $j usage 'cbvoprab123vw' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d x y z w v t $.  $d ps w v t $.  $d ch y z t $.
    cbvoprab23vw.1 $e |- ( ( y = w /\ z = v ) -> ( ps <-> ch ) ) $.
    $( Change the second and third bound variables in an operation abstraction,
       using implicit substitution.  (Contributed by GG, 14-Aug-2025.) $)
    cbvoprab23vw $p |- { <. <. x , y >. , z >. | ps } =
                       { <. <. x , w >. , v >. | ch } $=
      ( vt cv cop wceq wa wex cab coprab weq opeq2 adantr df-oprab simpr eqeq2d
      opeq12d anbi12d cbvex2vw exbii abbii 3eqtr4i ) IJZCJZDJZKZEJZKZLZAMZENDNZ
      CNZIOUIUJFJZKZGJZKZLZBMZGNFNZCNZIOACDEPBCFGPURVFIUQVECUPVDDEFGDFQZEGQZMZU
      OVCABVIUNVBUIVIULUTUMVAVGULUTLVHUKUSUJRSVGVHUAUCUBHUDUEUFUGACDEITBCFGITUH
      $.
    $( $j usage 'cbvoprab23vw' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d x y z w v t $.  $d ps w v t $.  $d ch x z t $.
    cbvoprab13vw.1 $e |- ( ( x = w /\ z = v ) -> ( ps <-> ch ) ) $.
    $( Change the first and third bound variables in an operation abstraction,
       using implicit substitution.  (Contributed by GG, 14-Aug-2025.) $)
    cbvoprab13vw $p |- { <. <. x , y >. , z >. | ps } =
                       { <. <. w , y >. , v >. | ch } $=
      ( vt cv cop wceq wa wex cab coprab weq opeq1 adantr df-oprab simpr eqeq2d
      opeq12d anbi12d cbvexdvaw exbidv cbvexvw abbii 3eqtr4i ) IJZCJZDJZKZEJZKZ
      LZAMZENZDNZCNZIOUJFJZULKZGJZKZLZBMZGNZDNZFNZIOACDEPBFDGPUTVIIUSVHCFCFQZUR
      VGDVJUQVFEGVJEGQZMZUPVEABVLUOVDUJVLUMVBUNVCVJUMVBLVKUKVAULRSVJVKUAUCUBHUD
      UEUFUGUHACDEITBFDGITUI $.
    $( $j usage 'cbvoprab13vw' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d x y z w $.  $d z w A t $.  $d x y B t $.  $d z w C t $.  $d x y D t $.
    $d z w E t $.  $d x y F t $.
    cbvmpovw2.1 $e |- ( ( x = z /\ y = w ) -> E = F ) $.
    cbvmpovw2.2 $e |- ( ( x = z /\ y = w ) -> C = D ) $.
    cbvmpovw2.3 $e |- ( ( x = z /\ y = w ) -> A = B ) $.
    $( Change bound variables and domains in a maps-to function, using implicit
       substitution.  (Contributed by GG, 14-Aug-2025.) $)
    cbvmpovw2 $p |- ( x e. A , y e. C |-> E ) = ( z e. B , w e. D |-> F ) $=
      ( vt cv wcel wa wceq coprab cmpo simpl eleq12d anbi12d eqeq2d cbvoprab12v
      weq simpr df-mpo 3eqtr4i ) AOZEPZBOZGPZQZNOZIRZQZABNSCOZFPZDOZHPZQZUOJRZQ
      ZCDNSABEGITCDFHJTUQVDABNCDACUFZBDUFZQZUNVBUPVCVGUKUSUMVAVGUJUREFVEVFUAMUB
      VGULUTGHVEVFUGLUBUCVGIJUOKUDUCUEABNEGIUHCDNFHJUHUI $.
    $( $j usage 'cbvmpovw2' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d x y z t $.  $d z A t $.  $d x B t $.  $d z C t $.  $d x D t $.
    $d z E t $.  $d x F t $.
    cbvmpo1vw2.1 $e |- ( x = z -> E = F ) $.
    cbvmpo1vw2.2 $e |- ( x = z -> C = D ) $.
    cbvmpo1vw2.3 $e |- ( x = z -> A = B ) $.
    $( Change domains and the first bound variable in a maps-to function, using
       implicit substitution.  (Contributed by GG, 14-Aug-2025.) $)
    cbvmpo1vw2 $p |- ( x e. A , y e. C |-> E ) = ( z e. B , y e. D |-> F ) $=
      ( vt cv wcel wa wceq coprab cmpo anbi12d weq id eleq2d eqeq2d cbvoprab1vw
      eleq12d df-mpo 3eqtr4i ) ANZDOZBNZFOZPZMNZHQZPZABMRCNZEOZUKGOZPZUNIQZPZCB
      MRABDFHSCBEGISUPVBABMCACUAZUMUTUOVAVCUJURULUSVCUIUQDEVCUBLUFVCFGUKKUCTVCH
      IUNJUDTUEABMDFHUGCBMEGIUGUH $.
    $( $j usage 'cbvmpo1vw2' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d x y z t $.  $d z A t $.  $d y B t $.  $d z C t $.  $d y D t $.
    $d z E t $.  $d y F t $.
    cbvmpo2vw2.1 $e |- ( y = z -> E = F ) $.
    cbvmpo2vw2.2 $e |- ( y = z -> C = D ) $.
    cbvmpo2vw2.3 $e |- ( y = z -> A = B ) $.
    $( Change domains and the second bound variable in a maps-to function,
       using implicit substitution.  (Contributed by GG, 14-Aug-2025.) $)
    cbvmpo2vw2 $p |- ( x e. A , y e. C |-> E ) = ( x e. B , z e. D |-> F ) $=
      ( vt cv wcel wa wceq coprab cmpo anbi12d weq eleq2d id eqeq2d cbvoprab2vw
      eleq12d df-mpo 3eqtr4i ) ANZDOZBNZFOZPZMNZHQZPZABMRUIEOZCNZGOZPZUNIQZPZAC
      MRABDFHSACEGISUPVBABMCBCUAZUMUTUOVAVCUJUQULUSVCDEUILUBVCUKURFGVCUCKUFTVCH
      IUNJUDTUEABMDFHUGACMEGIUGUH $.
    $( $j usage 'cbvmpo2vw2' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d x y $.  $d A y t $.  $d B x t $.  $d C y t $.  $d D x t $.
    cbvixpvw2.1 $e |- ( x = y -> C = D ) $.
    cbvixpvw2.2 $e |- ( x = y -> A = B ) $.
    $( Change bound variable and domain in an indexed Cartesian product, using
       implicit substitution.  (Contributed by GG, 14-Aug-2025.) $)
    cbvixpvw2 $p |- X_ x e. A C = X_ y e. B D $=
      ( vt cv wcel cab wfn cfv wral wa cixp weq eleq12d df-ixp id cbvabv fneq2i
      fveq2 cbvralvw2 anbi12i abbii 3eqtr4i ) IJZAJZCKZALZMZUJUINZEKZACOZPZILUI
      BJZDKZBLZMZURUINZFKZBDOZPZILACEQBDFQUQVEIUMVAUPVDULUTUIUKUSABABRZUJURCDVF
      UAHSUBUCUOVCABCDHVFUNVBEFUJURUIUDGSUEUFUGACEITBDFITUH $.
    $( $j usage 'cbvixpvw2' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d j k $.  $d D j $.  $d C k $.
    cbvsumvw2.1 $e |- A = B $.
    cbvsumvw2.2 $e |- ( j = k -> C = D ) $.
    $( Change bound variable and the set of integers in a sum, using implicit
       substitution.  (Contributed by GG, 1-Sep-2025.) $)
    cbvsumvw2 $p |- sum_ j e. A C = sum_ k e. B D $=
      ( csu cbvsumv sumeq1i eqtri ) ACEIADFIBDFIACDEFHJABDFGKL $.
    $( $j usage 'cbvsumvw2' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d j k x y m n f $.  $d D j x y m n f $.  $d C k x y m n f $.
    $d A k x y m n f $.  $d B j x y m n f $.
    cbvprodvw2.1 $e |- A = B $.
    cbvprodvw2.2 $e |- ( j = k -> C = D ) $.
    $( Change bound variable and the set of integers in a product, using
       implicit substitution.  (Contributed by GG, 1-Sep-2025.) $)
    cbvprodvw2 $p |- prod_ j e. A C = prod_ k e. B D $=
      ( vm vy vn vx vf cv cmul cz c1 cseq cli wceq cuz cfv wss cc0 wne wcel cif
      cmpt wbr wa wex wrex w3a cfz co wf1o cn csb wo cprod sseq1i eleq2i eleq1w
      cio weq bitrid ifbieq1d seqeq3 ax-mp breq1i anbi2i exbii rexbii 3anbi123i
      cbvmptv wb f1oeq3 cbvcsbv mpteq2i anbi12i orbi12i iotabii df-prod 3eqtr4i
      fveq1i eqeq2i ) AINZUAUBZUCZJNZUDUEZOEPENZAUFZCQUGZUHZKNZRZWJSUIZUJZJUKZK
      WHULZOWOWGRZLNZSUIZUMZIPULZQWGUNUOZAMNZUPZXCWGOKUQEWPXHUBZCURZUHZQRZUBZTZ
      UJZMUKZIUQULZUSZLVDBWHUCZWKOFPFNBUFZDQUGZUHZWPRZWJSUIZUJZJUKZKWHULZOYCWGR
      ZXCSUIZUMZIPULZXGBXHUPZXCWGOKUQFXJDURZUHZQRZUBZTZUJZMUKZIUQULZUSZLVDACEUT
      BDFUTXSUUBLXFYLXRUUAXEYKIPWIXTXAYHXDYJABWHGVAWTYGKWHWSYFJWRYEWKWQYDWJSWOY
      CTZWQYDTEFPWNYBEFVEZWMYACDQWMWLBUFUUDYAABWLGVBEFBVCVFHVGVOZOWOYCWPVHVIVJV
      KVLVMXBYIXCSUUCXBYITUUEOWOYCWGVHVIVJVNVMXQYTIUQXPYSMXIYMXOYRABTXIYMVPGABX
      GXHVQVIXNYQXCWGXMYPXLYOTXMYPTKUQXKYNEFXJCDHVRVSOXLYOQVHVIWEWFVTVLVMWAWBLJ
      ACMEIKWCLJBDMFIKWCWD $.
    $( $j usage 'cbvprodvw2' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d x y $.  $d A y t v $.  $d B x t v $.  $d C y t v $.  $d D x t v $.
    cbvitgvw2.1 $e |- ( x = y -> C = D ) $.
    cbvitgvw2.2 $e |- ( x = y -> A = B ) $.
    $( Change bound variable and domain in an integral, using implicit
       substitution.  (Contributed by GG, 14-Aug-2025.) $)
    cbvitgvw2 $p |- S. A C _d x = S. B D _d y $=
      ( vt vv cc0 co cv cr cdiv cre cfv wcel citg2 cmul c3 cfz cexp cle wbr cif
      ci wa csb cmpt csu weq fvoveq1d id eleq12d anbi1d ifbid csbeq12dv cbvmptv
      citg fveq2i oveq2i sumeq2si df-itg 3eqtr4i ) KUAUBLZUGIMUCLZANJEVGOLPQZAM
      ZCRZKJMZUDUEZUHZVKKUFZUIZUJZSQZTLZIUKVFVGBNJFVGOLPQZBMZDRZVLUHZVKKUFZUIZU
      JZSQZTLZIUKACEUTBDFUTVFVRWGIVQWFVGTVPWESABNVOWDABULZJVHVNVSWCWHEFVGPOGUMW
      HVMWBVKKWHVJWAVLWHVIVTCDWHUNHUOUPUQURUSVAVBVCAJCEIVDBJDFIVDVE $.
    $( $j usage 'cbvitgvw2' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d x y $.  $d A y $.  $d B x $.  $d C y $.  $d D x $.  $d E y $.  $d F x $.
    cbvditgvw2.1 $e |- A = B $.
    cbvditgvw2.2 $e |- C = D $.
    cbvditgvw2.3 $e |- ( x = y -> E = F ) $.
    $( Change bound variable and domain in a directed integral, using implicit
       substitution.  (Contributed by GG, 1-Sep-2025.) $)
    cbvditgvw2 $p |- S_ [ A -> C ] E _d x = S_ [ B -> D ] F _d y $=
      ( cle wbr cioo co citg cneg cif wceq a1i cdit breq12i weq oveq12i oveq12d
      cbvitgvw2 negeqi ifbieq12i df-ditg 3eqtr4i ) CELMZACENOZGPZAECNOZGPZQZRDF
      LMZBDFNOZHPZBFDNOZHPZQZRACEGUABDFHUAUKUQUMUPUSVBCDEFLIJUBABULURGHKULURSAB
      UCZCDEFNIJUDTUFUOVAABUNUTGHKVCEFCDNEFSVCJTCDSVCITUEUFUGUHACEGUIBDFHUIUJ
      $.
    $( $j usage 'cbvditgvw2' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Change bound variables, deduction versions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d ph x y z $.  $d ps y z $.  $d ch x z $.
    cbvmodavw.1 $e |- ( ( ph /\ x = y ) -> ( ps <-> ch ) ) $.
    $( Change bound variable in the at-most-one quantifier.  Deduction form.
       (Contributed by GG, 14-Aug-2025.) $)
    cbvmodavw $p |- ( ph -> ( E* x ps <-> E* y ch ) ) $=
      ( vz weq wi wal wex wmo wa equequ1 adantl imbi12d cbvaldvaw exbidv dfmo
      wb 3bitr4g ) ABDGHZIZDJZGKCEGHZIZEJZGKBDLCELAUDUGGAUCUFDEADEHZMBCUBUEFUHU
      BUETADEGNOPQRBDGSCEGSUA $.
    $( $j usage 'cbvmodavw' avoids 'ax-8' 'ax-9' 'ax-10' 'ax-11' 'ax-12'
       'ax-13' 'ax-ext'; $)
  $}

  ${
    $d ph x y $.  $d ps y $.  $d ch x $.
    cbveudavw.1 $e |- ( ( ph /\ x = y ) -> ( ps <-> ch ) ) $.
    $( Change bound variable in the existential uniqueness quantifier.
       Deduction form.  (Contributed by GG, 14-Aug-2025.) $)
    cbveudavw $p |- ( ph -> ( E! x ps <-> E! y ch ) ) $=
      ( wex wmo wa weu cbvexdvaw cbvmodavw anbi12d df-eu 3bitr4g ) ABDGZBDHZICE
      GZCEHZIBDJCEJAPRQSABCDEFKABCDEFLMBDNCENO $.
    $( $j usage 'cbveudavw' avoids 'ax-8' 'ax-9' 'ax-10' 'ax-11' 'ax-12'
       'ax-13' 'ax-ext'; $)
  $}

  ${
    $d ph x y $.  $d ps y $.  $d ch x $.  $d A x y $.
    cbvrmodavw.1 $e |- ( ( ph /\ x = y ) -> ( ps <-> ch ) ) $.
    $( Change bound variable in the restricted at-most-one quantifier.
       Deduction form.  (Contributed by GG, 14-Aug-2025.) $)
    cbvrmodavw $p |- ( ph -> ( E* x e. A ps <-> E* y e. A ch ) ) $=
      ( cv wcel wa wmo wrmo weq eleq1w adantl anbi12d cbvmodavw df-rmo 3bitr4g
      wb ) ADHFIZBJZDKEHFIZCJZEKBDFLCEFLAUBUDDEADEMZJUAUCBCUEUAUCTADEFNOGPQBDFR
      CEFRS $.
    $( $j usage 'cbvrmodavw' avoids 'ax-9' 'ax-10' 'ax-11' 'ax-12' 'ax-13'
       'ax-ext'; $)
  $}

  ${
    $d ph x y $.  $d ps y $.  $d ch x $.  $d A x y $.
    cbvreudavw.1 $e |- ( ( ph /\ x = y ) -> ( ps <-> ch ) ) $.
    $( Change bound variable in the restricted existential uniqueness
       quantifier.  Deduction form.  (Contributed by GG, 14-Aug-2025.) $)
    cbvreudavw $p |- ( ph -> ( E! x e. A ps <-> E! y e. A ch ) ) $=
      ( cv wcel wa weu wreu weq eleq1w adantl anbi12d cbveudavw df-reu 3bitr4g
      wb ) ADHFIZBJZDKEHFIZCJZEKBDFLCEFLAUBUDDEADEMZJUAUCBCUEUAUCTADEFNOGPQBDFR
      CEFRS $.
    $( $j usage 'cbvreudavw' avoids 'ax-9' 'ax-10' 'ax-11' 'ax-12' 'ax-13'
       'ax-ext'; $)
  $}

  ${
    $d ph x y t $.  $d ps y t $.  $d ch x t $.  $d t z $.
    cbvsbdavw.1 $e |- ( ( ph /\ x = y ) -> ( ps <-> ch ) ) $.
    $( Change bound variable in proper substitution.  Deduction form.
       (Contributed by GG, 14-Aug-2025.) $)
    cbvsbdavw $p |- ( ph -> ( [ z / x ] ps <-> [ z / y ] ch ) ) $=
      ( vt weq wi wal wsb wa wb equequ1 adantl imbi12d cbvaldvaw imbi2d dfsb
      albidv 3bitr4g ) AHFIZDHIZBJZDKZJZHKUCEHIZCJZEKZJZHKBDFLCEFLAUGUKHAUFUJUC
      AUEUIDEADEIZMUDUHBCULUDUHNADEHOPGQRSUABDHFTCEHFTUB $.
    $( $j usage 'cbvsbdavw' avoids 'ax-8' 'ax-9' 'ax-10' 'ax-11' 'ax-12'
       'ax-13' 'ax-ext'; $)
  $}

  ${
    $d ph x y t $.  $d ps y t $.  $d ch x t $.  $d t z $.  $d t w $.
    cbvsbdavw2.1 $e |- ( ph -> z = w ) $.
    cbvsbdavw2.2 $e |- ( ( ph /\ x = y ) -> ( ps <-> ch ) ) $.
    $( Change bound variable in proper substitution.  General version of
       ~ cbvsbdavw .  Deduction form.  (Contributed by GG, 14-Aug-2025.) $)
    cbvsbdavw2 $p |- ( ph -> ( [ z / x ] ps <-> [ w / y ] ch ) ) $=
      ( vt weq wi wal wsb wb equequ2 syl wa imbi12d dfsb equequ1 adantl 3bitr4g
      cbvaldvaw albidv ) AJFKZDJKZBLZDMZLZJMJGKZEJKZCLZEMZLZJMBDFNCEGNAUJUOJAUF
      UKUIUNAFGKUFUKOHFGJPQAUHUMDEADEKZRUGULBCUPUGULOADEJUAUBISUDSUEBDJFTCEJGTU
      C $.
    $( $j usage 'cbvsbdavw2' avoids 'ax-8' 'ax-9' 'ax-10' 'ax-11' 'ax-12'
       'ax-13' 'ax-ext'; $)
  $}

  ${
    $d ph x y t $.  $d ps y t $.  $d ch x t $.
    cbvabdavw.1 $e |- ( ( ph /\ x = y ) -> ( ps <-> ch ) ) $.
    $( Change bound variable in class abstractions.  Deduction form.
       (Contributed by GG, 14-Aug-2025.) $)
    cbvabdavw $p |- ( ph -> { x | ps } = { y | ch } ) $=
      ( vt cab wsb cv wcel cbvsbdavw df-clab 3bitr4g eqrdv ) AGBDHZCEHZABDGICEG
      IGJZPKRQKABCDEGFLBGDMCGEMNO $.
    $( $j usage 'cbvabdavw' avoids 'ax-8' 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d ph x y $.  $d ps y $.  $d ch x $.
    cbvsbcdavw.1 $e |- ( ( ph /\ x = y ) -> ( ps <-> ch ) ) $.
    $( Change bound variable of a class substitution.  Deduction form.
       (Contributed by GG, 14-Aug-2025.) $)
    cbvsbcdavw $p |- ( ph -> ( [. A / x ]. ps <-> [. A / y ]. ch ) ) $=
      ( cab wcel wsbc cbvabdavw eleq2d df-sbc 3bitr4g ) AFBDHZIFCEHZIBDFJCEFJAO
      PFABCDEGKLBDFMCEFMN $.
    $( $j usage 'cbvsbcdavw' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d ph x y $.  $d ps y $.  $d ch x $.
    cbvsbcdavw2.1 $e |- ( ph -> A = B ) $.
    cbvsbcdavw2.2 $e |- ( ( ph /\ x = y ) -> ( ps <-> ch ) ) $.
    $( Change bound variable of a class substitution.  General version of
       ~ cbvsbcdavw .  Deduction form.  (Contributed by GG, 14-Aug-2025.) $)
    cbvsbcdavw2 $p |- ( ph -> ( [. A / x ]. ps <-> [. B / y ]. ch ) ) $=
      ( cab wcel wsbc cbvabdavw eleq12d df-sbc 3bitr4g ) AFBDJZKGCEJZKBDFLCEGLA
      FGQRHABCDEIMNBDFOCEGOP $.
    $( $j usage 'cbvsbcdavw2' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d ph x y t $.  $d A t $.  $d B y t $.  $d C x t $.
    cbvcsbdavw.1 $e |- ( ( ph /\ x = y ) -> B = C ) $.
    $( Change bound variable of a proper substitution into a class.  Deduction
       form.  (Contributed by GG, 14-Aug-2025.) $)
    cbvcsbdavw $p |- ( ph -> [_ A / x ]_ B = [_ A / y ]_ C ) $=
      ( vt cv wcel wsbc cab csb weq wa eleq2d cbvsbcdavw abbidv df-csb 3eqtr4g
      ) AHIZEJZBDKZHLUAFJZCDKZHLBDEMCDFMAUCUEHAUBUDBCDABCNOEFUAGPQRBHDESCHDFST
      $.
    $( $j usage 'cbvcsbdavw' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d ph x y t $.  $d A t $.  $d B t $.  $d C y t $.  $d D x t $.
    cbvcsbdavw2.1 $e |- ( ph -> A = B ) $.
    cbvcsbdavw2.2 $e |- ( ( ph /\ x = y ) -> C = D ) $.
    $( Change bound variable of a proper substitution into a class.  General
       version of ~ cbvcsbdavw .  Deduction form.  (Contributed by GG,
       14-Aug-2025.) $)
    cbvcsbdavw2 $p |- ( ph -> [_ A / x ]_ C = [_ B / y ]_ D ) $=
      ( vt cv wcel wsbc cab csb weq wa eleq2d cbvsbcdavw2 df-csb abbidv 3eqtr4g
      ) AJKZFLZBDMZJNUCGLZCEMZJNBDFOCEGOAUEUGJAUDUFBCDEHABCPQFGUCIRSUABJDFTCJEG
      TUB $.
    $( $j usage 'cbvcsbdavw2' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d ph x y $.  $d ps y $.  $d ch x $.  $d A x y $.
    cbvrabdavw.1 $e |- ( ( ph /\ x = y ) -> ( ps <-> ch ) ) $.
    $( Change bound variable in restricted class abstractions.  Deduction form.
       (Contributed by GG, 14-Aug-2025.) $)
    cbvrabdavw $p |- ( ph -> { x e. A | ps } = { y e. A | ch } ) $=
      ( cv wcel wa cab crab weq eleq1w adantl anbi12d cbvabdavw df-rab 3eqtr4g
      wb ) ADHFIZBJZDKEHFIZCJZEKBDFLCEFLAUBUDDEADEMZJUAUCBCUEUAUCTADEFNOGPQBDFR
      CEFRS $.
    $( $j usage 'cbvrabdavw' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d ph x y t $.  $d A x y t $.  $d B y t $.  $d C x t $.
    cbviundavw.1 $e |- ( ( ph /\ x = y ) -> B = C ) $.
    $( Change bound variable in indexed unions.  Deduction form.  (Contributed
       by GG, 14-Aug-2025.) $)
    cbviundavw $p |- ( ph -> U_ x e. A B = U_ y e. A C ) $=
      ( vt cv wcel wrex cab ciun weq wa eleq2d cbvrexdva abbidv df-iun 3eqtr4g
      ) AHIZEJZBDKZHLUAFJZCDKZHLBDEMCDFMAUCUEHAUBUDBCDABCNOEFUAGPQRBHDESCHDFST
      $.
    $( $j usage 'cbviundavw' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d ph x y t $.  $d A x y t $.  $d B y t $.  $d C x t $.
    cbviindavw.1 $e |- ( ( ph /\ x = y ) -> B = C ) $.
    $( Change bound variable in indexed intersections.  Deduction form.
       (Contributed by GG, 14-Aug-2025.) $)
    cbviindavw $p |- ( ph -> |^|_ x e. A B = |^|_ y e. A C ) $=
      ( vt cv wcel wral cab ciin weq wa eleq2d cbvraldva abbidv df-iin 3eqtr4g
      ) AHIZEJZBDKZHLUAFJZCDKZHLBDEMCDFMAUCUEHAUBUDBCDABCNOEFUAGPQRBHDESCHDFST
      $.
    $( $j usage 'cbviindavw' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d ph x y z t $.  $d x y z t $.  $d ps z t $.  $d ch x t $.
    cbvopab1davw.1 $e |- ( ( ph /\ x = z ) -> ( ps <-> ch ) ) $.
    $( Change the first bound variable in an ordered-pair class abstraction.
       Deduction form.  (Contributed by GG, 14-Aug-2025.) $)
    cbvopab1davw $p |- ( ph -> { <. x , y >. | ps } = { <. z , y >. | ch } ) $=
      ( vt cv cop wceq wa wex cab copab weq opeq1 adantl eqeq2d df-opab anbi12d
      exbidv cbvexdvaw abbidv 3eqtr4g ) AHIZDIZEIZJZKZBLZEMZDMZHNUFFIZUHJZKZCLZ
      EMZFMZHNBDEOCFEOAUMUSHAULURDFADFPZLZUKUQEVAUJUPBCVAUIUOUFUTUIUOKAUGUNUHQR
      SGUAUBUCUDBDEHTCFEHTUE $.
    $( $j usage 'cbvopab1davw' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d ph x y z t $.  $d x y z t $.  $d ps z t $.  $d ch y t $.
    cbvopab2davw.1 $e |- ( ( ph /\ y = z ) -> ( ps <-> ch ) ) $.
    $( Change the second bound variable in an ordered-pair class abstraction.
       Deduction form.  (Contributed by GG, 14-Aug-2025.) $)
    cbvopab2davw $p |- ( ph -> { <. x , y >. | ps } = { <. x , z >. | ch } ) $=
      ( vt cv cop wceq wa wex cab copab weq wb opeq2 eqeq2d df-opab cbvexdvaw
      adantl anbi12d exbidv abbidv 3eqtr4g ) AHIZDIZEIZJZKZBLZEMZDMZHNUGUHFIZJZ
      KZCLZFMZDMZHNBDEOCDFOAUNUTHAUMUSDAULUREFAEFPZLUKUQBCVAUKUQQAVAUJUPUGUIUOU
      HRSUBGUCUAUDUEBDEHTCDFHTUF $.
    $( $j usage 'cbvopab2davw' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d ph x y z w t $.  $d ps z w t $.  $d ch x y t $.
    cbvopabdavw.1 $e |- ( ( ( ph /\ x = z ) /\ y = w ) -> ( ps <-> ch ) ) $.
    $( Change bound variables in an ordered-pair class abstraction.  Deduction
       form.  (Contributed by GG, 14-Aug-2025.) $)
    cbvopabdavw $p |- ( ph -> { <. x , y >. | ps } = { <. z , w >. | ch } ) $=
      ( vt cv cop wceq wa wex cab copab weq simplr cbvexdvaw df-opab opeq12d
      simpr eqeq2d anbi12d abbidv 3eqtr4g ) AIJZDJZEJZKZLZBMZENZDNZIOUGFJZGJZKZ
      LZCMZGNZFNZIOBDEPCFGPAUNVAIAUMUTDFADFQZMZULUSEGVCEGQZMZUKURBCVEUJUQUGVEUH
      UOUIUPAVBVDRVCVDUBUAUCHUDSSUEBDEITCFGITUF $.
    $( $j usage 'cbvopabdavw' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d ph x y t $.  $d x y t A $.  $d y t B $.  $d x t C $.
    cbvmptdavw.1 $e |- ( ( ph /\ x = y ) -> B = C ) $.
    $( Change bound variable in a maps-to function.  Deduction form.
       (Contributed by GG, 14-Aug-2025.) $)
    cbvmptdavw $p |- ( ph -> ( x e. A |-> B ) = ( y e. A |-> C ) ) $=
      ( vt cv wcel wceq wa copab cmpt weq wb eleq1w adantl eqeq2d df-mpt
      anbi12d cbvopab1davw 3eqtr4g ) ABIDJZHIZEKZLZBHMCIDJZUEFKZLZCHMBDENCDFNAU
      GUJBHCABCOZLZUDUHUFUIUKUDUHPABCDQRULEFUEGSUAUBBHDETCHDFTUC $.
    $( $j usage 'cbvmptdavw' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d ph x y t $.  $d x y t A $.  $d y t B $.  $d x t C $.
    cbvdisjdavw.1 $e |- ( ( ph /\ x = y ) -> B = C ) $.
    $( Change bound variable in a disjoint collection.  Deduction form.
       (Contributed by GG, 14-Aug-2025.) $)
    cbvdisjdavw $p |- ( ph -> ( Disj_ x e. A B <-> Disj_ y e. A C ) ) $=
      ( vt cv wcel wrmo wal wdisj weq eleq2d cbvrmodavw albidv df-disj 3bitr4g
      wa ) AHIZEJZBDKZHLUAFJZCDKZHLBDEMCDFMAUCUEHAUBUDBCDABCNTEFUAGOPQBHDERCHDF
      RS $.
    $( $j usage 'cbvdisjdavw' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d ph x y t $.  $d ps y t $.  $d ch x t $.
    cbviotadavw.1 $e |- ( ( ph /\ x = y ) -> ( ps <-> ch ) ) $.
    $( Change bound variable in a description binder.  Deduction form.
       (Contributed by GG, 14-Aug-2025.) $)
    cbviotadavw $p |- ( ph -> ( iota x ps ) = ( iota y ch ) ) $=
      ( vt cab csn wceq cuni cio cbvabdavw eqeq1d abbidv unieqd df-iota 3eqtr4g
      cv ) ABDHZGSIZJZGHZKCEHZUAJZGHZKBDLCELAUCUFAUBUEGATUDUAABCDEFMNOPBDGQCEGQ
      R $.
    $( $j usage 'cbviotadavw' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d ph x y $.  $d ps y $.  $d ch x $.  $d x y A $.
    cbvriotadavw.1 $e |- ( ( ph /\ x = y ) -> ( ps <-> ch ) ) $.
    $( Change bound variable in a restricted description binder.  Deduction
       form.  (Contributed by GG, 14-Aug-2025.) $)
    cbvriotadavw $p |- ( ph -> ( iota_ x e. A ps ) = ( iota_ y e. A ch ) ) $=
      ( cv wcel cio crio weq eleq1w adantl anbi12d cbviotadavw df-riota 3eqtr4g
      wa wb ) ADHFIZBSZDJEHFIZCSZEJBDFKCEFKAUBUDDEADELZSUAUCBCUEUAUCTADEFMNGOPB
      DFQCEFQR $.
    $( $j usage 'cbvriotadavw' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d ph x z w t $.  $d ph x y w t $.  $d ps w t $.  $d ch x t $.
    cbvoprab1davw.1 $e |- ( ( ph /\ x = w ) -> ( ps <-> ch ) ) $.
    $( Change the first bound variable in an operation abstraction.  Deduction
       form.  (Contributed by GG, 14-Aug-2025.) $)
    cbvoprab1davw $p |- ( ph -> { <. <. x , y >. , z >. | ps } =
                                { <. <. w , y >. , z >. | ch } ) $=
      ( vt cv cop wceq wa wex cab coprab weq opeq1 adantl df-oprab cbvexdvaw
      opeq1d eqeq2d anbi12d 2exbidv abbidv 3eqtr4g ) AIJZDJZEJZKZFJZKZLZBMZFNEN
      ZDNZIOUHGJZUJKZULKZLZCMZFNENZGNZIOBDEFPCGEFPAUQVDIAUPVCDGADGQZMZUOVBEFVFU
      NVABCVFUMUTUHVFUKUSULVEUKUSLAUIURUJRSUBUCHUDUEUAUFBDEFITCGEFITUG $.
    $( $j usage 'cbvoprab1davw' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d ph x y w t $.  $d ph y z w t $.  $d ps w t $.  $d ch y t $.
    cbvoprab2davw.1 $e |- ( ( ph /\ y = w ) -> ( ps <-> ch ) ) $.
    $( Change the second bound variable in an operation abstraction.  Deduction
       form.  (Contributed by GG, 14-Aug-2025.) $)
    cbvoprab2davw $p |- ( ph -> { <. <. x , y >. , z >. | ps } =
                                { <. <. x , w >. , z >. | ch } ) $=
      ( vt cv cop wceq wa wex cab coprab weq opeq2 exbidv df-oprab cbvexdvaw
      adantl opeq1d eqeq2d anbi12d abbidv 3eqtr4g ) AIJZDJZEJZKZFJZKZLZBMZFNZEN
      ZDNZIOUHUIGJZKZULKZLZCMZFNZGNZDNZIOBDEFPCDGFPAURVFIAUQVEDAUPVDEGAEGQZMZUO
      VCFVHUNVBBCVHUMVAUHVHUKUTULVGUKUTLAUJUSUIRUBUCUDHUESUASUFBDEFITCDGFITUG
      $.
    $( $j usage 'cbvoprab2davw' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d ph x z w t $.  $d ph y z w t $.  $d ps w t $.  $d ch z t $.
    cbvoprab3davw.1 $e |- ( ( ph /\ z = w ) -> ( ps <-> ch ) ) $.
    $( Change the third bound variable in an operation abstraction.  Deduction
       form.  (Contributed by GG, 14-Aug-2025.) $)
    cbvoprab3davw $p |- ( ph -> { <. <. x , y >. , z >. | ps } =
                                { <. <. x , y >. , w >. | ch } ) $=
      ( vt cv cop wceq wa wex cab coprab weq simpr opeq2d df-oprab cbvexdvaw
      eqeq2d anbi12d 2exbidv abbidv 3eqtr4g ) AIJZDJEJKZFJZKZLZBMZFNZENDNZIOUGU
      HGJZKZLZCMZGNZENDNZIOBDEFPCDEGPAUNUTIAUMUSDEAULURFGAFGQZMZUKUQBCVBUJUPUGV
      BUIUOUHAVARSUBHUCUAUDUEBDEFITCDEGITUF $.
    $( $j usage 'cbvoprab3davw' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d ph x y z w u v t $.  $d ps w u v t $.  $d ch x y z t $.
    cbvoprab123davw.1 $e |- ( ( ( ( ph /\ x = w ) /\ y = u ) /\ z = v ) ->
                                                             ( ps <-> ch ) ) $.
    $( Change all bound variables in an operation abstraction.  Deduction form.
       (Contributed by GG, 14-Aug-2025.) $)
    cbvoprab123davw $p |- ( ph -> { <. <. x , y >. , z >. | ps } =
                                  { <. <. w , u >. , v >. | ch } ) $=
      ( vt cv cop wceq wa wex cab coprab weq cbvexdvaw opeq12d anbi12d df-oprab
      simplr simpr adantr eqeq2d abbidv 3eqtr4g ) AKLZDLZELZMZFLZMZNZBOZFPZEPZD
      PZKQUJGLZILZMZHLZMZNZCOZHPZIPZGPZKQBDEFRCGIHRAUTVJKAUSVIDGADGSZOZURVHEIVL
      EISZOZUQVGFHVNFHSZOZUPVFBCVPUOVEUJVPUMVCUNVDVNUMVCNVOVNUKVAULVBAVKVMUDVLV
      MUEUAUFVNVOUEUAUGJUBTTTUHBDEFKUCCGIHKUCUI $.
    $( $j usage 'cbvoprab123davw' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d ph x y z w v t $.  $d ps w v t $.  $d ch x y t $.
    cbvoprab12davw.1 $e |- ( ( ( ph /\ x = w ) /\ y = v ) -> ( ps <-> ch ) ) $.
    $( Change the first and second bound variables in an operation abstraction.
       Deduction form.  (Contributed by GG, 14-Aug-2025.) $)
    cbvoprab12davw $p |- ( ph -> { <. <. x , y >. , z >. | ps } =
                                 { <. <. w , v >. , z >. | ch } ) $=
      ( vt cv cop wceq wa wex cab coprab weq cbvexdvaw df-oprab opeq12d anbi12d
      simplr simpr opeq1d eqeq2d exbidv abbidv 3eqtr4g ) AJKZDKZEKZLZFKZLZMZBNZ
      FOZEOZDOZJPUJGKZHKZLZUNLZMZCNZFOZHOZGOZJPBDEFQCGHFQAUTVIJAUSVHDGADGRZNZUR
      VGEHVKEHRZNZUQVFFVMUPVEBCVMUOVDUJVMUMVCUNVMUKVAULVBAVJVLUCVKVLUDUAUEUFIUB
      UGSSUHBDEFJTCGHFJTUI $.
    $( $j usage 'cbvoprab12davw' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d ph x y z w v t $.  $d ps w v t $.  $d ch y z t $.
    cbvoprab23davw.1 $e |- ( ( ( ph /\ y = w ) /\ z = v ) -> ( ps <-> ch ) ) $.
    $( Change the second and third bound variables in an operation abstraction.
       Deduction form.  (Contributed by GG, 14-Aug-2025.) $)
    cbvoprab23davw $p |- ( ph -> { <. <. x , y >. , z >. | ps } =
                                 { <. <. x , w >. , v >. | ch } ) $=
      ( vt cv cop wceq wa wex cab coprab weq opeq12d cbvexdvaw anbi12d df-oprab
      eqidd simplr simpr eqeq2d exbidv abbidv 3eqtr4g ) AJKZDKZEKZLZFKZLZMZBNZF
      OZEOZDOZJPUJUKGKZLZHKZLZMZCNZHOZGOZDOZJPBDEFQCDGHQAUTVIJAUSVHDAURVGEGAEGR
      ZNZUQVFFHVKFHRZNZUPVEBCVMUOVDUJVMUMVBUNVCVMUKUKULVAVMUKUCAVJVLUDSVKVLUESU
      FIUATTUGUHBDEFJUBCDGHJUBUI $.
    $( $j usage 'cbvoprab23davw' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d ph x y z w v t $.  $d ps w v t $.  $d ch x z t $.
    cbvoprab13davw.1 $e |- ( ( ( ph /\ x = w ) /\ z = v ) -> ( ps <-> ch ) ) $.
    $( Change the first and third bound variables in an operation abstraction.
       Deduction form.  (Contributed by GG, 14-Aug-2025.) $)
    cbvoprab13davw $p |- ( ph -> { <. <. x , y >. , z >. | ps } =
                                 { <. <. w , y >. , v >. | ch } ) $=
      ( vt cv cop wceq wa wex cab coprab weq opeq12d cbvexdvaw anbi12d df-oprab
      simplr eqidd simpr eqeq2d exbidv abbidv 3eqtr4g ) AJKZDKZEKZLZFKZLZMZBNZF
      OZEOZDOZJPUJGKZULLZHKZLZMZCNZHOZEOZGOZJPBDEFQCGEHQAUTVIJAUSVHDGADGRZNZURV
      GEVKUQVFFHVKFHRZNZUPVEBCVMUOVDUJVMUMVBUNVCVMUKVAULULAVJVLUCVMULUDSVKVLUES
      UFIUATUGTUHBDEFJUBCGEHJUBUI $.
    $( $j usage 'cbvoprab13davw' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d ph x y t $.  $d x y A t $.  $d y B t $.  $d x C t $.
    cbvixpdavw.1 $e |- ( ( ph /\ x = y ) -> B = C ) $.
    $( Change bound variable in an indexed Cartesian product.  Deduction form.
       (Contributed by GG, 14-Aug-2025.) $)
    cbvixpdavw $p |- ( ph -> X_ x e. A B = X_ y e. A C ) $=
      ( vt cv wcel cab wfn cfv wral wa cixp weq wb eleq1w df-ixp adantl eleq12d
      cbvabdavw fneq2d simpr fveq2d cbvraldva anbi12d abbidv 3eqtr4g ) AHIZBIZD
      JZBKZLZULUKMZEJZBDNZOZHKUKCIZDJZCKZLZUTUKMZFJZCDNZOZHKBDEPCDFPAUSVGHAUOVC
      URVFAUNVBUKAUMVABCBCQZUMVARABCDSUAUCUDAUQVEBCDAVHOZUPVDEFVIULUTUKAVHUEUFG
      UBUGUHUIBDEHTCDFHTUJ $.
    $( $j usage 'cbvixpdavw' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d ph k j x m n f $.  $d A x m n f $.  $d j B x m n f $.  $d k C x n m f $.
    cbvsumdavw.1 $e |- ( ( ph /\ k = j ) -> B = C ) $.
    $( Change bound variable in a sum.  Deduction form.  (Contributed by GG,
       14-Aug-2025.) $)
    cbvsumdavw $p |- ( ph -> sum_ k e. A B = sum_ j e. A C ) $=
      ( vm vn vx vf cv cfv caddc cz csb cmpt cseq wa cn cuz wss cc0 cif cli wbr
      wcel wrex c1 cfz wf1o wceq wex cio csu cbvcsbdavw ifeq1d mpteq2dv seqeq3d
      co wo breq1d anbi2d rexbidv fveq1d eqeq2d exbidv orbi12d iotabidv 3eqtr4g
      df-sum ) ABHLZUAMUBZNIOILZBUGZFVNCPZUCUDZQZVLRZJLZUEUFZSZHOUHZUIVLUJUTBKL
      ZUKZVTVLNITFVNWDMZCPZQZUIRZMZULZSZKUMZHTUHZVAZJUNVMNIOVOEVNDPZUCUDZQZVLRZ
      VTUEUFZSZHOUHZWEVTVLNITEWFDPZQZUIRZMZULZSZKUMZHTUHZVAZJUNBCFUOBDEUOAWOXKJ
      AWCXBWNXJAWBXAHOAWAWTVMAVSWSVTUEAVRWRNVLAIOVQWQAVOVPWPUCAFEVNCDGUPUQURUSV
      BVCVDAWMXIHTAWLXHKAWKXGWEAWJXFVTAVLWIXEAWHXDNUIAITWGXCAFEWFCDGUPURUSVEVFV
      CVGVDVHVIJBCKFHIVKJBDKEHIVKVJ $.
    $( $j usage 'cbvsumdavw' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d ph j k x y m n f $.  $d j k A x y m n f $.  $d k B x y m n f $.
    $d j C x y m n f $.
    cbvproddavw.1 $e |- ( ( ph /\ j = k ) -> B = C ) $.
    $( Change bound variable in a product.  Deduction form.  (Contributed by
       GG, 14-Aug-2025.) $)
    cbvproddavw $p |- ( ph -> prod_ j e. A B = prod_ k e. A C ) $=
      ( vm vy vn vx vf cv cmul cz c1 cseq cli wrex cn cuz cfv wss cc0 wcel cmpt
      wne cif wbr wa wex w3a cfz co wf1o csb wceq wo cio cprod wb eleq1w adantl
      weq ifbieq1d cbvmptdavw seqeq3d breq1d anbi2d rexbidv 3anbi23d cbvcsbdavw
      exbidv mpteq2dv fveq1d eqeq2d orbi12d iotabidv df-prod 3eqtr4g ) ABHMZUAU
      BZUCZIMZUDUGZNEOEMBUEZCPUHZUFZJMZQZWDRUIZUJZIUKZJWBSZNWHWAQZKMZRUIZULZHOS
      ZPWAUMUNBLMZUOZWPWANJTEWIWTUBZCUPZUFZPQZUBZUQZUJZLUKZHTSZURZKUSWCWENFOFMB
      UEZDPUHZUFZWIQZWDRUIZUJZIUKZJWBSZNXNWAQZWPRUIZULZHOSZXAWPWANJTFXBDUPZUFZP
      QZUBZUQZUJZLUKZHTSZURZKUSBCEUTBDFUTAXKYLKAWSYCXJYKAWRYBHOAWNXSWQYAWCAWMXR
      JWBAWLXQIAWKXPWEAWJXOWDRAWHXNNWIAEFOWGXMAEFVDZUJWFXLCDPYMWFXLVAAEFBVBVCGV
      EVFZVGVHVIVMVJAWOXTWPRAWHXNNWAYNVGVHVKVJAXIYJHTAXHYILAXGYHXAAXFYGWPAWAXEY
      FAXDYENPAJTXCYDAEFXBCDGVLVNVGVOVPVIVMVJVQVRKIBCLEHJVSKIBDLFHJVSVT $.
    $( $j usage 'cbvproddavw' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d ph x y t v $.  $d x y A t v $.  $d y B t v $.  $d x C t v $.
    cbvitgdavw.1 $e |- ( ( ph /\ x = y ) -> B = C ) $.
    $( Change bound variable in an integral.  Deduction form.  (Contributed by
       GG, 14-Aug-2025.) $)
    cbvitgdavw $p |- ( ph -> S. A B _d x = S. A C _d y ) $=
      ( vt vv cc0 co cv cr cdiv cre cfv wcel wa citg2 cmul cfz cexp cle wbr cif
      c3 ci csb cmpt csu citg weq fvoveq1d eleq1w adantl anbi1d ifbid csbeq12dv
      wb cbvmptdavw fveq2d oveq2d sumeq2sdv df-itg 3eqtr4g ) AJUFUAKZUGHLUBKZBM
      IEVGNKOPZBLDQZJILZUCUDZRZVJJUEZUHZUIZSPZTKZHUJVFVGCMIFVGNKOPZCLDQZVKRZVJJ
      UEZUHZUIZSPZTKZHUJBDEUKCDFUKAVFVQWEHAVPWDVGTAVOWCSABCMVNWBABCULZRZIVHVMVR
      WAWGEFVGONGUMWGVLVTVJJWGVIVSVKWFVIVSUSABCDUNUOUPUQURUTVAVBVCBIDEHVDCIDFHV
      DVE $.
    $( $j usage 'cbvitgdavw' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d ph x y $.  $d x A y $.  $d x B y $.  $d y C $.  $d x D $.
    cbvditgdavw.1 $e |- ( ( ph /\ x = y ) -> C = D ) $.
    $( Change bound variable in a directed integral.  Deduction form.
       (Contributed by GG, 14-Aug-2025.) $)
    cbvditgdavw $p |- ( ph -> S_ [ A -> B ] C _d x = S_ [ A -> B ] D _d y ) $=
      ( cle wbr cioo co citg cneg cif cdit cbvitgdavw negeqd ifeq12d df-ditg
      3eqtr4g ) ADEIJZBDEKLZFMZBEDKLZFMZNZOUBCUCGMZCUEGMZNZOBDEFPCDEGPAUBUDUHUG
      UJABCUCFGHQAUFUIABCUEFGHQRSBDEFTCDEGTUA $.
    $( $j usage 'cbvditgdavw' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Change bound variables and domains, deduction versions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d ph x y $.  $d ps y $.  $d ch x $.  $d A y $.  $d B x $.
    cbvrmodavw2.1 $e |- ( ( ph /\ x = y ) -> ( ps <-> ch ) ) $.
    cbvrmodavw2.2 $e |- ( ( ph /\ x = y ) -> A = B ) $.
    $( Change bound variable and quantifier domain in the restricted
       at-most-one quantifier.  Deduction form.  (Contributed by GG,
       14-Aug-2025.) $)
    cbvrmodavw2 $p |- ( ph -> ( E* x e. A ps <-> E* y e. B ch ) ) $=
      ( cv wcel wa wmo wrmo weq simpr eleq12d anbi12d cbvmodavw df-rmo 3bitr4g
      ) ADJZFKZBLZDMEJZGKZCLZEMBDFNCEGNAUDUGDEADEOZLZUCUFBCUIUBUEFGAUHPIQHRSBDF
      TCEGTUA $.
    $( $j usage 'cbvrmodavw2' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d ph x y $.  $d ps y $.  $d ch x $.  $d A y $.  $d B x $.
    cbvreudavw2.1 $e |- ( ( ph /\ x = y ) -> ( ps <-> ch ) ) $.
    cbvreudavw2.2 $e |- ( ( ph /\ x = y ) -> A = B ) $.
    $( Change bound variable and quantifier domain in the restricted
       existential uniqueness quantifier.  Deduction form.  (Contributed by GG,
       14-Aug-2025.) $)
    cbvreudavw2 $p |- ( ph -> ( E! x e. A ps <-> E! y e. B ch ) ) $=
      ( cv wcel wa weu wreu weq simpr eleq12d anbi12d cbveudavw df-reu 3bitr4g
      ) ADJZFKZBLZDMEJZGKZCLZEMBDFNCEGNAUDUGDEADEOZLZUCUFBCUIUBUEFGAUHPIQHRSBDF
      TCEGTUA $.
    $( $j usage 'cbvreudavw2' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d ph x y $.  $d ps y $.  $d ch x $.  $d y A $.  $d x B $.
    cbvrabdavw2.1 $e |- ( ( ph /\ x = y ) -> ( ps <-> ch ) ) $.
    cbvrabdavw2.2 $e |- ( ( ph /\ x = y ) -> A = B ) $.
    $( Change bound variable and domain in restricted class abstractions.
       Deduction form.  (Contributed by GG, 14-Aug-2025.) $)
    cbvrabdavw2 $p |- ( ph -> { x e. A | ps } = { y e. B | ch } ) $=
      ( cv wcel wa cab crab weq wb eleq1w adantl eleq2d df-rab bitrd cbvabdavw
      anbi12d 3eqtr4g ) ADJFKZBLZDMEJZGKZCLZEMBDFNCEGNAUFUIDEADEOZLZUEUHBCUKUEU
      GFKZUHUJUEULPADEFQRUKFGUGISUAHUCUBBDFTCEGTUD $.
    $( $j usage 'cbvrabdavw2' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d ph x y t $.  $d A y t $.  $d B x t $.  $d C y t $.  $d D x t $.
    cbviundavw2.1 $e |- ( ( ph /\ x = y ) -> C = D ) $.
    cbviundavw2.2 $e |- ( ( ph /\ x = y ) -> A = B ) $.
    $( Change bound variable and domain in indexed unions.  Deduction form.
       (Contributed by GG, 14-Aug-2025.) $)
    cbviundavw2 $p |- ( ph -> U_ x e. A C = U_ y e. B D ) $=
      ( vt cv wcel wrex cab ciun weq wa eleq2d cbvrexdva2 df-iun abbidv 3eqtr4g
      ) AJKZFLZBDMZJNUCGLZCEMZJNBDFOCEGOAUEUGJAUDUFBCDEABCPQFGUCHRISUABJDFTCJEG
      TUB $.
    $( $j usage 'cbviundavw2' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d ph x y t $.  $d A y t $.  $d B x t $.  $d C y t $.  $d D x t $.
    cbviindavw2.1 $e |- ( ( ph /\ x = y ) -> C = D ) $.
    cbviindavw2.2 $e |- ( ( ph /\ x = y ) -> A = B ) $.
    $( Change bound variable and domain in indexed intersections.  Deduction
       form.  (Contributed by GG, 14-Aug-2025.) $)
    cbviindavw2 $p |- ( ph -> |^|_ x e. A C = |^|_ y e. B D ) $=
      ( vt cv wcel wral cab ciin weq wa eleq2d cbvraldva2 df-iin abbidv 3eqtr4g
      ) AJKZFLZBDMZJNUCGLZCEMZJNBDFOCEGOAUEUGJAUDUFBCDEABCPQFGUCHRISUABJDFTCJEG
      TUB $.
    $( $j usage 'cbviindavw2' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d ph x y t $.  $d y t A $.  $d x t B $.  $d y t C $.  $d x t D $.
    cbvmptdavw2.1 $e |- ( ( ph /\ x = y ) -> C = D ) $.
    cbvmptdavw2.2 $e |- ( ( ph /\ x = y ) -> A = B ) $.
    $( Change bound variable and domain in a maps-to function.  Deduction form.
       (Contributed by GG, 14-Aug-2025.) $)
    cbvmptdavw2 $p |- ( ph -> ( x e. A |-> C ) = ( y e. B |-> D ) ) $=
      ( vt cv wcel wceq wa copab cmpt weq wb eleq1w df-mpt adantl eleq2d eqeq2d
      bitrd anbi12d cbvopab1davw 3eqtr4g ) ABKDLZJKZFMZNZBJOCKZELZUIGMZNZCJOBDF
      PCEGPAUKUOBJCABCQZNZUHUMUJUNUQUHULDLZUMUPUHURRABCDSUAUQDEULIUBUDUQFGUIHUC
      UEUFBJDFTCJEGTUG $.
    $( $j usage 'cbvmptdavw2' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d ph x y t $.  $d y t A $.  $d x t B $.  $d y t C $.  $d x t D $.
    cbvdisjdavw2.1 $e |- ( ( ph /\ x = y ) -> C = D ) $.
    cbvdisjdavw2.2 $e |- ( ( ph /\ x = y ) -> A = B ) $.
    $( Change bound variable and domain in a disjoint collection.  Deduction
       form.  (Contributed by GG, 14-Aug-2025.) $)
    cbvdisjdavw2 $p |- ( ph -> ( Disj_ x e. A C <-> Disj_ y e. B D ) ) $=
      ( vt cv wcel wrmo wal wdisj weq wa eleq2d cbvrmodavw2 df-disj 3bitr4g
      albidv ) AJKZFLZBDMZJNUCGLZCEMZJNBDFOCEGOAUEUGJAUDUFBCDEABCPQFGUCHRISUBBJ
      DFTCJEGTUA $.
    $( $j usage 'cbvdisjdavw2' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d ph x y $.  $d ps y $.  $d ch x $.  $d y A $.  $d x B $.
    cbvriotadavw2.1 $e |- ( ( ph /\ x = y ) -> ( ps <-> ch ) ) $.
    cbvriotadavw2.2 $e |- ( ( ph /\ x = y ) -> A = B ) $.
    $( Change bound variable and domain in a restricted description binder.
       Deduction form.  (Contributed by GG, 14-Aug-2025.) $)
    cbvriotadavw2 $p |- ( ph -> ( iota_ x e. A ps ) = ( iota_ y e. B ch ) ) $=
      ( cv wcel wa cio crio weq wb eleq1w adantl eleq2d df-riota bitrd anbi12d
      cbviotadavw 3eqtr4g ) ADJFKZBLZDMEJZGKZCLZEMBDFNCEGNAUFUIDEADEOZLZUEUHBCU
      KUEUGFKZUHUJUEULPADEFQRUKFGUGISUAHUBUCBDFTCEGTUD $.
    $( $j usage 'cbvriotadavw2' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d ph x y z w t $.  $d z w A t $.  $d x y B t $.  $d z w C t $.
    $d x y D t $.  $d z w E t $.  $d x y F t $.
    cbvmpodavw2.1 $e |- ( ( ( ph /\ x = z ) /\ y = w ) -> E = F ) $.
    cbvmpodavw2.2 $e |- ( ( ( ph /\ x = z ) /\ y = w ) -> C = D ) $.
    cbvmpodavw2.3 $e |- ( ( ( ph /\ x = z ) /\ y = w ) -> A = B ) $.
    $( Change bound variable and domains in a maps-to function.  Deduction
       form.  (Contributed by GG, 14-Aug-2025.) $)
    cbvmpodavw2 $p |- ( ph -> ( x e. A , y e. C |-> E ) =
                              ( z e. B , w e. D |-> F ) ) $=
      ( vt cv wcel wa wceq coprab cmpo weq eleq12d simpr anbi12d cbvoprab12davw
      simplr eqeq2d df-mpo 3eqtr4g ) ABPZFQZCPZHQZRZOPZJSZRZBCOTDPZGQZEPZIQZRZU
      PKSZRZDEOTBCFHJUADEGIKUAAURVEBCODEABDUBZRZCEUBZRZUOVCUQVDVIULUTUNVBVIUKUS
      FGAVFVHUGNUCVIUMVAHIVGVHUDMUCUEVIJKUPLUHUEUFBCOFHJUIDEOGIKUIUJ $.
    $( $j usage 'cbvmpodavw2' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d ph x y z t $.  $d z A t $.  $d x B t $.  $d z C t $.  $d x D t $.
    $d z E t $.  $d x F t $.
    cbvmpo1davw2.1 $e |- ( ( ph /\ x = z ) -> E = F ) $.
    cbvmpo1davw2.2 $e |- ( ( ph /\ x = z ) -> C = D ) $.
    cbvmpo1davw2.3 $e |- ( ( ph /\ x = z ) -> A = B ) $.
    $( Change first bound variable and domains in a maps-to function.
       Deduction form.  (Contributed by GG, 14-Aug-2025.) $)
    cbvmpo1davw2 $p |- ( ph -> ( x e. A , y e. C |-> E ) =
                               ( z e. B , y e. D |-> F ) ) $=
      ( vt cv wcel wa wceq coprab cmpo weq eleq12d eleq2d anbi12d cbvoprab1davw
      simpr eqeq2d df-mpo 3eqtr4g ) ABOZEPZCOZGPZQZNOZIRZQZBCNSDOZFPZULHPZQZUOJ
      RZQZDCNSBCEGITDCFHJTAUQVCBCNDABDUAZQZUNVAUPVBVEUKUSUMUTVEUJUREFAVDUFMUBVE
      GHULLUCUDVEIJUOKUGUDUEBCNEGIUHDCNFHJUHUI $.
    $( $j usage 'cbvmpo1davw2' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d ph x y z t $.  $d z A t $.  $d y B t $.  $d z C t $.  $d y D t $.
    $d z E t $.  $d y F t $.
    cbvmpo2davw2.1 $e |- ( ( ph /\ y = z ) -> E = F ) $.
    cbvmpo2davw2.2 $e |- ( ( ph /\ y = z ) -> C = D ) $.
    cbvmpo2davw2.3 $e |- ( ( ph /\ y = z ) -> A = B ) $.
    $( Change second bound variable and domains in a maps-to function.
       Deduction form.  (Contributed by GG, 14-Aug-2025.) $)
    cbvmpo2davw2 $p |- ( ph -> ( x e. A , y e. C |-> E ) =
                               ( x e. B , z e. D |-> F ) ) $=
      ( vt cv wcel wa wceq coprab cmpo weq eleq2d eleq12d anbi12d cbvoprab2davw
      simpr eqeq2d df-mpo 3eqtr4g ) ABOZEPZCOZGPZQZNOZIRZQZBCNSUJFPZDOZHPZQZUOJ
      RZQZBDNSBCEGITBDFHJTAUQVCBCNDACDUAZQZUNVAUPVBVEUKURUMUTVEEFUJMUBVEULUSGHA
      VDUFLUCUDVEIJUOKUGUDUEBCNEGIUHBDNFHJUHUI $.
    $( $j usage 'cbvmpo2davw2' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d ph x y t $.  $d A y t $.  $d B x t $.  $d C y t $.  $d D x t $.
    cbvixpdavw2.1 $e |- ( ( ph /\ x = y ) -> C = D ) $.
    cbvixpdavw2.2 $e |- ( ( ph /\ x = y ) -> A = B ) $.
    $( Change bound variable and domain in an indexed Cartesian product.
       Deduction form.  (Contributed by GG, 14-Aug-2025.) $)
    cbvixpdavw2 $p |- ( ph -> X_ x e. A C = X_ y e. B D ) $=
      ( vt cv wcel cab wfn cfv wral wa cixp eleq12d df-ixp weq cbvabdavw fneq2d
      simpr wceq fveq2 adantl cbvraldva2 anbi12d abbidv 3eqtr4g ) AJKZBKZDLZBMZ
      NZUMULOZFLZBDPZQZJMULCKZELZCMZNZVAULOZGLZCEPZQZJMBDFRCEGRAUTVHJAUPVDUSVGA
      UOVCULAUNVBBCABCUAZQZUMVADEAVIUDISUBUCAURVFBCDEVJUQVEFGVIUQVEUEAUMVAULUFU
      GHSIUHUIUJBDFJTCEGJTUK $.
    $( $j usage 'cbvixpdavw2' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d ph j k x m n f $.  $d A x m n f $.  $d B x m n f $.  $d C k x m n f $.
    $d D j x m n f $.
    cbvsumdavw2.1 $e |- ( ph -> A = B ) $.
    cbvsumdavw2.2 $e |- ( ( ph /\ j = k ) -> C = D ) $.
    $( Change bound variable and the set of integers in a sum.  Deduction form.
       (Contributed by GG, 14-Aug-2025.) $)
    cbvsumdavw2 $p |- ( ph -> sum_ j e. A C = sum_ k e. B D ) $=
      ( vm vn vx vf cv cfv caddc cz csb cmpt cn cuz wss wcel cc0 cif cli wbr wa
      cseq wrex c1 cfz co wf1o wex wo cio csu sseq1d eleq2d cbvcsbdavw ifbieq1d
      wceq mpteq2dv seqeq3d breq1d anbi12d rexbidv f1oeq3d fveq1d eqeq2d exbidv
      orbi12d iotabidv df-sum 3eqtr4g ) ABJNZUAOZUBZPKQKNZBUCZFVTDRZUDUEZSZVQUI
      ZLNZUFUGZUHZJQUJZUKVQULUMZBMNZUNZWFVQPKTFVTWKOZDRZSZUKUIZOZVCZUHZMUOZJTUJ
      ZUPZLUQCVRUBZPKQVTCUCZGVTERZUDUEZSZVQUIZWFUFUGZUHZJQUJZWJCWKUNZWFVQPKTGWM
      ERZSZUKUIZOZVCZUHZMUOZJTUJZUPZLUQBDFURCEGURAXBYALAWIXKXAXTAWHXJJQAVSXCWGX
      IABCVRHUSAWEXHWFUFAWDXGPVQAKQWCXFAWAXDWBXEUDABCVTHUTAFGVTDEIVAVBVDVEVFVGV
      HAWTXSJTAWSXRMAWLXLWRXQABCWJWKHVIAWQXPWFAVQWPXOAWOXNPUKAKTWNXMAFGWMDEIVAV
      DVEVJVKVGVLVHVMVNLBDMFJKVOLCEMGJKVOVP $.
    $( $j usage 'cbvsumdavw2' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d ph j k x y m n f $.  $d A k x y m n f $.  $d B j x y m n f $.
    $d C k x y m n f $.  $d D j x y m n f $.
    cbvproddavw2.1 $e |- ( ph -> A = B ) $.
    cbvproddavw2.2 $e |- ( ( ph /\ j = k ) -> C = D ) $.
    $( Change bound variable and the set of integers in a product.  Deduction
       form.  (Contributed by GG, 14-Aug-2025.) $)
    cbvproddavw2 $p |- ( ph -> prod_ j e. A C = prod_ k e. B D ) $=
      ( vm vy vn vx vf cv cmul cz c1 cseq cli cuz cfv wss cc0 wne wcel cif cmpt
      wbr wa wex wrex w3a cfz co wf1o cn csb wceq wo cio cprod sseq1d weq simpr
      adantr eleq12d ifbieq1d cbvmptdavw seqeq3d breq1d anbi2d exbidv 3anbi123d
      rexbidv f1oeq3d cbvcsbdavw mpteq2dv fveq1d eqeq2d anbi12d orbi12d df-prod
      iotabidv 3eqtr4g ) ABJOZUAUBZUCZKOZUDUEZPFQFOZBUFZDRUGZUHZLOZSZWITUIZUJZK
      UKZLWGULZPWNWFSZMOZTUIZUMZJQULZRWFUNUOZBNOZUPZXBWFPLUQFWOXGUBZDURZUHZRSZU
      BZUSZUJZNUKZJUQULZUTZMVACWGUCZWJPGQGOZCUFZERUGZUHZWOSZWITUIZUJZKUKZLWGULZ
      PYCWFSZXBTUIZUMZJQULZXFCXGUPZXBWFPLUQGXIEURZUHZRSZUBZUSZUJZNUKZJUQULZUTZM
      VABDFVBCEGVBAXRUUBMAXEYLXQUUAAXDYKJQAWHXSWTYHXCYJABCWGHVCAWSYGLWGAWRYFKAW
      QYEWJAWPYDWITAWNYCPWOAFGQWMYBAFGVDZUJZWLYADERUUDWKXTBCAUUCVEABCUSUUCHVFVG
      IVHVIZVJVKVLVMVOAXAYIXBTAWNYCPWFUUEVJVKVNVOAXPYTJUQAXOYSNAXHYMXNYRABCXFXG
      HVPAXMYQXBAWFXLYPAXKYOPRALUQXJYNAFGXIDEIVQVRVJVSVTWAVMVOWBWDMKBDNFJLWCMKC
      ENGJLWCWE $.
    $( $j usage 'cbvproddavw2' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d ph x y t v $.  $d A y t v $.  $d B x t v $.  $d C y t v $.
    $d D x t v $.
    cbvitgdavw2.1 $e |- ( ( ph /\ x = y ) -> C = D ) $.
    cbvitgdavw2.2 $e |- ( ( ph /\ x = y ) -> A = B ) $.
    $( Change bound variable and domain in an integral.  Deduction form.
       (Contributed by GG, 14-Aug-2025.) $)
    cbvitgdavw2 $p |- ( ph -> S. A C _d x = S. B D _d y ) $=
      ( vt vv cc0 co cv cr cdiv cre cfv wa citg2 c3 cfz ci cexp cle wbr cif csb
      wcel cmpt cmul csu citg weq fvoveq1d simpr eleq12d anbi1d ifbid csbeq12dv
      cbvmptdavw fveq2d oveq2d sumeq2sdv df-itg 3eqtr4g ) ALUAUBMZUCJNUDMZBOKFV
      HPMQRZBNZDUIZLKNZUEUFZSZVLLUGZUHZUJZTRZUKMZJULVGVHCOKGVHPMQRZCNZEUIZVMSZV
      LLUGZUHZUJZTRZUKMZJULBDFUMCEGUMAVGVSWHJAVRWGVHUKAVQWFTABCOVPWEABCUNZSZKVI
      VOVTWDWJFGVHQPHUOWJVNWCVLLWJVKWBVMWJVJWADEAWIUPIUQURUSUTVAVBVCVDBKDFJVECK
      EGJVEVF $.
    $( $j usage 'cbvitgdavw2' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d ph x y $.  $d A y $.  $d B x $.  $d C y $.  $d D x $.  $d E y $.
    $d F x $.
    cbvditgdavw2.1 $e |- ( ph -> A = B ) $.
    cbvditgdavw2.2 $e |- ( ph -> C = D ) $.
    cbvditgdavw2.3 $e |- ( ( ph /\ x = y ) -> E = F ) $.
    $( Change bound variable and limits in a directed integral.  Deduction
       form.  (Contributed by GG, 14-Aug-2025.) $)
    cbvditgdavw2 $p |- ( ph -> S_ [ A -> C ] E _d x = S_ [ B -> D ] F _d y ) $=
      ( cle wbr cioo co citg cneg cif cdit breq12d weq wceq oveq12d cbvitgdavw2
      wa adantr negeqd ifbieq12d df-ditg 3eqtr4g ) ADFMNZBDFOPZHQZBFDOPZHQZRZSE
      GMNZCEGOPZIQZCGEOPZIQZRZSBDFHTCEGITAULURUNUQUTVCADEFGMJKUAABCUMUSHILABCUB
      ZUFZDEFGOADEUCVDJUGZAFGUCVDKUGZUDUEAUPVBABCUOVAHILVEFGDEOVGVFUDUEUHUIBDFH
      UJCEGIUJUK $.
    $( $j usage 'cbvditgdavw2' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Study of ax-mulf usage
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x y u v $.
    $( Multiplication maps nonzero complex numbers to nonzero complex numbers.
       Version of ~ mulnzcnf using maps-to notation, which does not require
       ~ ax-mulf .  (Contributed by GG, 18-Apr-2025.) $)
    mpomulnzcnf $p |-
      ( x e. ( CC \ { 0 } ) , y e. ( CC \ { 0 } ) |-> ( x x. y ) )
                   : ( ( CC \ { 0 } ) X. ( CC \ { 0 } ) ) --> ( CC \ { 0 } ) $=
      ( vu vv cc cc0 csn cdif cxp cv cmul co cmpo wf wcel wral ovex wne eldifsn
      wa wfn eqid fnmpoi oveq12 ovmpoa mulcl ad2ant2r mulne0 jca syl2anb sylibr
      eqeltrd rgen2 ffnov mpbir2an ) EFGHZUPIZUPABUPUPAJZBJZKLZMZNVAUQUACJZDJZV
      ALZUPOZDUPPCUPPABUPUPUTVAVAUBZURUSKQUCVECDUPUPVBUPOZVCUPOZTZVDVBVCKLZUPAB
      VBVCUPUPUTVJVAURVBUSVCKUDVFVBVCKQUEVIVJEOZVJFRZTZVJUPOVGVBEOZVBFRZTZVCEOZ
      VCFRZTZVMVHVBEFSVCEFSVPVSTVKVLVNVQVKVOVRVBVCUFUGVBVCUHUIUJVJEFSUKULUMCDUP
      UPUPVAUNUO $.
    $( $j usage 'mpomulnzcnf' avoids 'ax-mulf'; $)
  $}

$( (End of Gino Giotto's mathbox.) $)
