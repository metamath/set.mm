$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Topology and algebraic structures
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  The norm on the ring of the integer numbers
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( The norm (function) for a ring of integers is the absolute value function
     (restricted to the integers).  (Contributed by AV, 13-Jun-2019.) $)
  zringnm $p |- ( norm ` ZZring ) = ( abs |` ZZ ) $=
    ( ccnfld cmnd wcel cc0 wss czring cnm cfv cabs cres wceq crg cnring ringmnd
    cz cc ax-mp 0z zsscn w3a df-zring cnfldbas cnfld0 cnfldnm ressnm eqcomd
    mp3an ) ABCZDOCZOPEZFGHZIOJZKALCUHMANQRSUHUIUJTULUKOPAFIDUAUBUCUDUEUFUG $.

  $( The norm of the ring of the integers.  (Contributed by Thierry Arnoux,
     8-Nov-2017.)  (Revised by AV, 13-Jun-2019.) $)
  zzsnm $p |- ( M e. ZZ -> ( abs ` M ) = ( ( norm ` ZZring ) ` M ) ) $=
    ( cz wcel cabs cres cfv czring cnm fvres zringnm eqcomi fveq1i eqtr3di ) AB
    CADBEZFADFAGHFZFABDIANOONJKLM $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Topological ` ZZ ` -modules
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    zlmlem2.1 $e |- W = ( ZMod ` G ) $.

    ${
      $d x y G $.  $d x y W $.
      zlm0.1 $e |- .0. = ( 0g ` G ) $.
      $( Zero of a ` ZZ ` -module.  (Contributed by Thierry Arnoux,
         8-Nov-2017.) $)
      zlm0 $p |- .0. = ( 0g ` W ) $=
        ( vx vy c0g cfv wceq wtru cbs eqid a1i zlmbas cv wcel cplusg zlmplusg
        wa oveqd grpidpropd mptru eqtri ) CAHIZBHIZEUEUFJKFGALIZABUGUGJKUGMZNUG
        BLIJKUGABDUHONKFPZUGQGPZUGQTTZARIZBRIZUIUJULUMJUKULABDULMSNUAUBUCUD $.
    $}

    ${
      $d x y G $.  $d x y W $.
      zlm1.1 $e |- .1. = ( 1r ` G ) $.
      $( Unity element of a ` ZZ ` -module (if present).  (Contributed by
         Thierry Arnoux, 8-Nov-2017.) $)
      zlm1 $p |- .1. = ( 1r ` W ) $=
        ( vx vy cur cfv wceq wtru cbs eqid a1i zlmbas cv wcel wa cmulr zlmmulr
        oveqd rngidpropd mptru eqtri ) ABHIZCHIZEUEUFJKFGBLIZBCUGUGJKUGMZNUGCLI
        JKUGBCDUHONKFPZUGQGPZUGQRRZBSIZCSIZUIUJULUMJUKULBCDULMTNUAUBUCUD $.
    $}

    ${
      zlmds.1 $e |- D = ( dist ` G ) $.
      $( Distance in a ` ZZ ` -module (if present).  (Contributed by Thierry
         Arnoux, 8-Nov-2017.)  (Proof shortened by AV, 11-Nov-2024.) $)
      zlmds $p |- ( G e. V -> D = ( dist ` W ) ) $=
        ( wcel cds cfv cnx csca czring cop csts co dsid wne slotsdnscsi setsnid
        cvsca cmg eqid zlmval fveq2d cip simp1i simp2i eqtri eqtr4di eqtr4id )
        BCGZABHIZDHIZFUKUMBJKIZLMNOZJTIZBUAIZMNOZHIZULUKDURHUQBCDEUQUBUCUDULUOH
        IUSLUNHBPJHIZUNQZUTUPQZUTJUEIQZRUFSUQUPHUOPVAVBVCRUGSUHUIUJ $.
    $}

    ${
      zlmtset.1 $e |- J = ( TopSet ` G ) $.
      $( Topology in a ` ZZ ` -module (if present).  (Contributed by Thierry
         Arnoux, 8-Nov-2017.)  (Proof shortened by AV, 12-Nov-2024.) $)
      zlmtset $p |- ( G e. V -> J = ( TopSet ` W ) ) $=
        ( wcel cnx csca cfv czring cop csts co cvsca cts tsetid wne slotstnscsi
        setsnid cmg cip simp1i simp2i 3eqtri eqid zlmval fveq2d eqtr4id ) ACGZB
        AHIJZKLMNZHOJZAUAJZLMNZPJZDPJBAPJULPJUPFKUKPAQHPJZUKRZUQUMRZUQHUBJRZSUC
        TUNUMPULQURUSUTSUDTUEUJDUOPUNACDEUNUFUGUHUI $.
    $}

    ${
      zlmnm.1 $e |- N = ( norm ` G ) $.
      $( Norm of a ` ZZ ` -module (if present).  (Contributed by Thierry
         Arnoux, 8-Nov-2017.) $)
      zlmnm $p |- ( G e. V -> N = ( norm ` W ) ) $=
        ( wcel cnm cfv cbs wceq zlmbas a1i cplusg zlmplusg zlmds nmpropd eqtrid
        eqid cds ) ACGZBAHIDHIFUAADAJIZDJIKUAUBADEUBSLMANIZDNIKUAUCADEUCSOMATIZ
        ACDEUDSPQR $.
    $}

    ${
      $d x y G $.  $d x y W $.
      $( The ` ZZ ` -module built from a normed ring is also a normed ring.
         (Contributed by Thierry Arnoux, 8-Nov-2017.) $)
      zhmnrg $p |- ( G e. NrmRing -> W e. NrmRing ) $=
        ( vx vy cnrg wcel cngp cnm cfv cabv cgrp cms csg ccom cds wceq eqid a1i
        wa wss w3a cbs zlmbas cplusg zlmplusg oveqdr grppropd cxp zlmds reseq1d
        cts zlmtset topnpropd mspropd zlmnm grpsubpropd coeq12d 3anbi123d isngp
        cv sseq12d 3bitr4g cmulr zlmmulr abvpropd2 eleq12d anbi12d isnrg ibi )
        AFGZBFGZVKAHGZAIJZAKJZGZTBHGZBIJZBKJZGZTVKVLVKVMVQVPVTVKALGZAMGZVNANJZO
        ZAPJZUAZUBBLGZBMGZVRBNJZOZBPJZUAZUBVMVQVKWAWGWBWHWFWLVKDEAUCJZABWMWMQVK
        WMRZSZWMBUCJQVKWMABCWNUDSZVKDVAWMGEVAWMGTDEAUEJZBUEJZWQWRQVKWQABCWQRUFS
        ZUGUHVKWMABWOWPVKWEWKWMWMUIWEAFBCWERZUJZUKVKABWPAAULJZFBCXBRUMUNUOVKWDW
        JWEWKVKVNVRWCWIAVNFBCVNRZUPZVKABWPWSUQURXAVBUSWEAWCVNXCWCRWTUTWKBWIVRVR
        RZWIRWKRUTVCVKVNVRVOVSXDVKABWPWSAVDJZBVDJQVKXFABCXFRVESVFVGVHVOAVNXCVOR
        VIVSBVRXEVSRVIVCVJ $.
    $}
  $}

  ${
    nmmulg.x $e |- B = ( Base ` R ) $.
    nmmulg.n $e |- N = ( norm ` R ) $.
    nmmulg.z $e |- Z = ( ZMod ` R ) $.
    ${
      nmmulg.t $e |- .x. = ( .g ` R ) $.
      $( The norm of a group product, provided the ` ZZ ` -module is normed.
         (Contributed by Thierry Arnoux, 8-Nov-2017.) $)
      nmmulg $p |- ( ( Z e. NrmMod /\ M e. ZZ /\ X e. B ) ->
        ( N ` ( M .x. X ) ) = ( ( abs ` M ) x. ( N ` X ) ) ) $=
        ( wcel cz co cnm cfv cmul wceq czring eqid cnlm w3a csca cabs cbs simp2
        zringbas clmod nlmlmod zlmlmod sylibr 3ad2ant1 zlmsca syl fveq2d eqtrid
        cabl eleqtrd zlmbas zlmvsca nmvs syld3an2 zlmnm fveq1d 3ad2ant2 oveq12d
        zzsnm eqtrd 3eqtr4d ) GUALZDMLZFALZUBZDFCNZGOPZPZDGUCPZOPZPZFVOPZQNZVNE
        PDUDPZFEPZQNVJDVQUEPZLVKVLVPWARVMDMWDVJVKVLUFVMMSUEPWDUGVMSVQUEVMBUQLZS
        VQRVJVKWEVLVJGUHLWEGUIBGJUJUKULZBUQGJUMUNZUOUPURVRCVQWDVOAGDFABGJHUSVOT
        CBGJKUTVQTWDTVRTVAVBVMVNEVOVMWEEVORWFBEUQGJIVCUNZVDVMWBVSWCVTQVMWBDSOPZ
        PZVSVKVJWBWJRVLDVGVEVMDWIVRVMSVQOWGUOVDVHVMFEVOWHVDVFVI $.
    $}

    ${
      zrhnm.1 $e |- L = ( ZRHom ` R ) $.
      $( The norm of the image by ` ZRHom ` of an integer in a normed ring.
         (Contributed by Thierry Arnoux, 8-Nov-2017.) $)
      zrhnm $p |- ( ( ( Z e. NrmMod /\ Z e. NrmRing /\ R e. NzRing )
                           /\ M e. ZZ ) -> ( N ` ( L ` M ) ) = ( abs ` M ) ) $=
        ( wcel cnzr wa cfv c1 cmul co wceq syl eqid cnlm cnrg w3a cz cur simpl3
        cabs cmg crg nzrring simpr zrhmulg fveq2d syl2anc simpl1 nmmulg syl3anc
        ringidcl cnm zlmnm fveq1d simpl2 c0g wne nzrnz zlm1 zlm0 isnzr sylanbrc
        nrgring nm1 eqtrd oveq2d 3eqtrd cc zcnd abscl recnd mulrid 3syl ) FUAKZ
        FUBKZBLKZUCZDUDKZMZDCNZENZDUGNZOPQZWIWFWHDBUENZBUHNZQZENZWIWKENZPQZWJWF
        BUIKZWEWHWNRWFWCWQWAWBWCWEUFZBUJSZWDWEUKZWQWEMWGWMEBWLWKCDJWLTZWKTZULUM
        UNWFWAWEWKAKZWNWPRWAWBWCWEUOWTWFWQXCWSABWKGXBURSABWLDEWKFGHIXAUPUQWFWOO
        WIPWFWOWKFUSNZNZOWFWKEXDWFWCEXDRWRBELFIHUTSVAWFWBFLKZXEORWAWBWCWEVBZWFF
        UIKZWKBVCNZVDZXFWFWBXHXGFVJSWFWCXJWRBWKXIXBXITZVESFWKXIWKBFIXBVFZBFXIIX
        KVGVHVIFWKXDXDTXLVKUNVLVMVNWFDVOKZWIVOKWJWIRWFDWTVPXMWIDVQVRWIVSVTVL $.
    $}
  $}

  ${
    $d x z $.
    $( The ` ZZ ` -module of ` CC ` is a normed module.  (Contributed by
       Thierry Arnoux, 25-Feb-2018.) $)
    cnzh $p |- ( ZMod ` CCfld ) e. NrmMod $=
      ( vz vx ccnfld cfv wcel czring cnrg cv co cabs cz cmul wceq cc wral cnnrg
      eqid mp2b cvv cnm czlm cnlm cngp clmod w3a cmg cres zhmnrg nrgngp nrgring
      cabl crg ringabl zlmlmod mpbi zringnrg 3pm3.2i simpl zcnd simpr cnfldmulg
      absmuld fveq2d fvres adantr oveq1d 3eqtr4d rgen2 cnfldbas cnfldex cnfldnm
      wa zlmbas zlmnm ax-mp zlmvsca csca zlmsca zringbas zringnm isnlm mpbir2an
      eqcomi ) CUADZUBEWDUCEZWDUDEZFGEZUEAHZBHZCUFDZIZJDZWHJKUGZDZWIJDZLIZMZBNO
      AKOWEWFWGCGEZWDGEWEPCWDWDQZUHWDUIRCUKEZWFWRCULEWTPCUJCUMRCWDWSUNUOUPUQWQA
      BKNWHKEZWINEZVLZWHWILIZJDWHJDZWOLIWLWPXCWHWIXCWHXAXBURUSXAXBUTVBXCWKXDJWH
      WIVAVCXCWNXEWOLXAWNXEMXBWHKJVDVEVFVGVHABWMWJFKJNWDNCWDWSVIVMCSEZJWDTDMVJC
      JSWDWSVKVNVOWJCWDWSWJQVPXFFWDVQDMVJCSWDWSVRVOVSFTDWMVTWCWAWB $.

    $( The ` ZZ ` -module of ` RR ` is a normed module.  (Contributed by
       Thierry Arnoux, 14-Feb-2018.) $)
    rezh $p |- ( ZMod ` RRfld ) e. NrmMod $=
      ( vz vx crefld cfv wcel czring cnrg co cabs cr cz cmul wceq df-refld eqid
      ccnfld ax-mp cc fvres cvv czlm cnlm cngp clmod w3a cvsca cres wral csubrg
      cv cnnrg cdr resubdrg simpli subrgnrg zhmnrg nrgngp mp2b cabl crg nrgring
      mp2an ringabl zlmlmod mpbi zringnrg 3pm3.2i wa simpl zcnd simpr recnd cmg
      absmuld csubg subrgsubg zlmvsca eqcomi mp3an1 cnfldmulg syldan eqtr3d zre
      subgmulg fveq2d remulcl sylan eqtrd oveqan12d 3eqtr4d rgen2 rebase zlmbas
      syl cnm ccusp recusp elexi cmnd cc0 wss cnring ringmnd ax-resscn cnfldbas
      0re cnfld0 cnfldnm ressnm mp3an zlmnm csca zlmsca zringbas isnlm mpbir2an
      zringnm ) CUADZUBEXRUCEZXRUDEZFGEZUEAUJZBUJZXRUFDZHZIJUGZDZYBIKUGZDZYCYFD
      ZLHZMZBJUHAKUHXSXTYACGEZXRGEXSPGEJPUIDEZYMUKYNCULEUMUNZJPCNUOVBZCXRXROZUP
      XRUQURCUSEZXTYMCUTEYRYPCVACVCURCXRYQVDVEVFVGYLABKJYBKEZYCJEZVHZYBYCLHZIDZ
      YBIDZYCIDZLHYGYKUUAYBYCUUAYBYSYTVIVJUUAYCYSYTVKVLZVNUUAYGUUBYFDZUUCUUAYEU
      UBYFUUAYBYCPVMDZHZYEUUBJPVODEZYSYTUUIYEMYNUUJYOJPVPQJYDUUHPCYBYCUUHONCVMD
      ZYDUUKCXRYQUUKOVQVRWDVSYSYTYCREUUIUUBMUUFYBYCVTWAWBWEYSYBJEZYTUUGUUCMZYBW
      CUULYTVHUUBJEUUMYBYCWFUUBJISWNWGWHYSYTYIUUDYJUUELYBKISYCJISWIWJWKABYHYDFK
      YFJXRJCXRYQWLWMCTEZYFXRWODMCWPWQWRZCYFTXRYQPWSEZWTJEJRXAYFCWODMPUTEUUPXBP
      XCQXFXDJRPCIWTNXEXGXHXIXJXKQYDOUUNFXRXLDMUUOCTXRYQXMQXNFWODYHXQVRXOXP $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Canonical embedding of the field of the rational numbers into a division ring
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $c QQHom $.

  $( Map the rationals into a field. $)
  cqqh $a class QQHom $.

  ${
    $d r x y $.
    $( Define the canonical homomorphism from the rationals into any field.
       (Contributed by Mario Carneiro, 22-Oct-2017.)  (Revised by Thierry
       Arnoux, 23-Oct-2017.) $)
    df-qqh $a |- QQHom = ( r e. _V |-> ran ( x e. ZZ , y e.
      ( `' ( ZRHom ` r ) " ( Unit ` r ) ) |-> <. ( x / y ) ,
      ( ( ( ZRHom ` r ) ` x ) ( /r ` r ) ( ( ZRHom ` r ) ` y ) ) >. ) ) $.
  $}

  ${
    $d f x y R $.  $d f ./ $.  $d f y L $.
    qqhval.1 $e |- ./ = ( /r ` R ) $.
    qqhval.2 $e |- .1. = ( 1r ` R ) $.
    qqhval.3 $e |- L = ( ZRHom ` R ) $.
    $( Value of the canonical homormorphism from the rational number to a
       field.  (Contributed by Thierry Arnoux, 22-Oct-2017.) $)
    qqhval $p |- ( R e. _V -> ( QQHom ` R ) =
      ran ( x e. ZZ , y e. ( `' L " ( Unit ` R ) ) |->
        <. ( x / y ) , ( ( L ` x ) ./ ( L ` y ) ) >. ) ) $=
      ( vf cz cv czrh cfv ccnv cui co cdvr cvv fveq2 cima cdiv cop cmpo eqtr4di
      crn cqqh wceq eqidd cnveqd imaeq12d fveq1d opeq2d mpoeq123dv rneqd df-qqh
      oveq123d zex wcel fvexi cnvex imaexg ax-mp mpoex rnex fvmpt ) JDABKJLZMNZ
      OZVGPNZUAZALZBLZUBQZVLVHNZVMVHNZVGRNZQZUCZUDZUFABKFOZDPNZUAZVNVLFNZVMFNZC
      QZUCZUDZUFSUGVGDUHZVTWHWIABKVKVSKWCWGWIKUIWIVIWAVJWBWIVHFWIVHDMNFVGDMTIUE
      ZUJVGDPTUKWIVRWFVNWIVOWDVPWEVQCWIVQDRNCVGDRTGUEWIVLVHFWJULWIVMVHFWJULUQUM
      UNUOABJUPWHABKWCWGURWASUSWCSUSFFDMIUTVAWAWBSVBVCVDVEVF $.
  $}

  ${
    zrhker.0 $e |- B = ( Base ` R ) $.
    zrhker.1 $e |- L = ( ZRHom ` R ) $.
    zrhker.2 $e |- .0. = ( 0g ` R ) $.
    $( The kernel of the homomorphism from the integers to a ring, if it is
       injective.  (Contributed by Thierry Arnoux, 26-Oct-2017.)  (Revised by
       Thierry Arnoux, 23-May-2023.) $)
    zrhf1ker $p |- ( R e. Ring ->
       ( L : ZZ -1-1-> B <-> ( `' L " { .0. } ) = { 0 } ) ) $=
      ( crg wcel czring crh co cghm cz wf1 ccnv csn cima cc0 wceq zrhrhm rhmghm
      wb zringbas zring0 kerf1ghm 3syl ) BHICJBKLICJBMLINACOCPDQRSQTUCBCFUAJBCU
      BNAJBCSDUDEUEGUFUG $.

    $d x B $.  $d x R $.
    $( The kernel of the homomorphism from the integers to a ring is injective
       if and only if the ring has characteristic 0 .  (Contributed by Thierry
       Arnoux, 8-Nov-2017.) $)
    zrhchr $p |- ( R e. Ring -> ( ( chr ` R ) = 0 <-> L : ZZ -1-1-> B ) ) $=
      ( vx crg wcel cz wf1 cv cur cfv cmg cc0 wceq wb eqid co cmpt cchr zrhval2
      cod f1eq1 syl cgrp ringgrp ringidcl odf1 syl2anc chrval eqeq1i 3bitr2rd
      a1i ) BIJZKACLZKAHKHMBNOZBPOZUAUBZLZUSBUEOZOZQRZBUCOZQRZUQCVARURVBSBUTUSH
      CFUTTZUSTZUDKACVAUFUGUQBUHJUSAJVEVBSBUIABUSEVIUJHUSUTVABVCAEVCTZVHVATUKUL
      VEVGSUQVDVFQVFBUSVCVJVIVFTUMUNUPUO $.

    $( The kernel of the homomorphism from the integers to a ring with
       characteristic 0.  (Contributed by Thierry Arnoux, 8-Nov-2017.) $)
    zrhker $p |- ( R e. Ring ->
       ( ( chr ` R ) = 0 <-> ( `' L " { .0. } ) = { 0 } ) ) $=
      ( crg wcel cchr cfv cc0 wceq cz wf1 ccnv csn cima zrhchr zrhf1ker bitrd )
      BHIBJKLMNACOCPDQRLQMABCDEFGSABCDEFGTUA $.

    $( The preimage by ` ZRHom ` of the units of a division ring is
       ` ( ZZ \ { 0 } ) ` .  (Contributed by Thierry Arnoux, 22-Oct-2017.) $)
    zrhunitpreima $p |- ( ( R e. DivRing /\ ( chr ` R ) = 0 )
      -> ( `' L " ( Unit ` R ) ) = ( ZZ \ { 0 } ) ) $=
      ( cdr wcel cfv cc0 wceq cima csn cdif cz eqid adantr czring 3syl cchr cui
      wa ccnv c0g crg isdrng simprbi imaeq2d drngring crh co wf zrhrhm zringbas
      wfun rhmf ffun difpreima fimacnv 4syl zrhker biimpa sylan difeq12d 3eqtrd
      ) BHIZBUAJKLZUCZCUDZBUBJZMZVJABUEJZNZOZMZVJAMZVJVNMZOZPKNZOVGVLVPLVHVGVKV
      OVJVGBUFIZVKVOLABVKVMEVKQVMQZUGUHUIRVGVPVSLZVHVGWACUPZWCBUJZWACSBUKULIZPA
      CUMZWDBCFUNZPASBCUOEUQZPACURTAVNCUSTRVIVQPVRVTVGVQPLZVHVGWAWFWGWJWEWHWIPA
      CUTVARVGWAVHVRVTLZWEWAVHWKABCVMEFWBVBVCVDVEVF $.

    $( Condition for the image by ` ZRHom ` to be a unit.  (Contributed by
       Thierry Arnoux, 30-Oct-2017.) $)
    elzrhunit $p |- ( ( ( R e. DivRing /\ ( chr ` R ) = 0 )
      /\ ( M e. ZZ /\ M =/= 0 ) ) -> ( L ` M ) e. ( Unit ` R ) ) $=
      ( cdr wcel cchr cfv cc0 wceq wa cz wne wfn czring 3syl ccnv cima drngring
      cui crg simpll crh co zrhrhm zringbas rhmf ffn csn cdif simprl necon3bbid
      wf wn elsng adantl eldifd zrhunitpreima adantr eleqtrrd elpreima simplbda
      biimpar syl2anc ) BIJZBKLMNZOZDPJZDMQZOZOZCPRZDCUABUDLZUBZJZDCLVQJZVOVIBU
      EJZVPVIVJVNUFBUCWACSBUGUHJPACUQVPBCGUIPASBCUJFUKPACULTTVODPMUMZUNZVRVODPW
      BVKVLVMUOVNDWBJZURZVKVLWEVMVLWDDMDMPUSUPVGUTVAVKVRWCNVNABCEFGHVBVCVDVPVSV
      LVTPDVQCVEVFVH $.
  $}

  ${
    zrhneg.1 $e |- L = ( ZRHom ` R ) $.
    zrhneg.2 $e |- I = ( invg ` R ) $.
    zrhneg.3 $e |- ( ph -> R e. Ring ) $.
    zrhneg.4 $e |- ( ph -> N e. ZZ ) $.
    $( The canonical homomorphism from the integers to a ring ` R ` maps
       additive inverses to additive inverses.  (Contributed by Thierry Arnoux,
       5-Oct-2025.) $)
    zrhneg $p |- ( ph -> ( L ` -u N ) = ( I ` ( L ` N ) ) ) $=
      ( cneg cfv czring cminusg cz wcel wceq zringinvg syl fveq2d co crg zrhrhm
      cghm crh rhmghm 3syl zringbas eqid ghminv syl2anc eqtrd ) AEJZDKELMKZKZDK
      ZEDKCKZAULUNDAENOZULUNPIEQRSADLBUCTOZUQUOUPPABUAODLBUDTOURHBDFUBLBDUEUFIN
      LBDUMCEUGUMUHGUIUJUK $.
  $}

  ${
    $d C i m $.  $d C i n $.  $d C n x $.  $d L i n $.  $d L m $.  $d L x $.
    $d M x $.  $d N i $.  $d N m $.  $d N x $.  $d R x $.  $d i n ph $.
    $d m ph $.  $d ph x $.
    zrhcntr.1 $e |- M = ( mulGrp ` R ) $.
    zrhcntr.2 $e |- C = ( Cntr ` M ) $.
    zrhcntr.3 $e |- L = ( ZRHom ` R ) $.
    zrhcntr.4 $e |- ( ph -> R e. Ring ) $.
    zrhcntr.5 $e |- ( ph -> N e. ZZ ) $.
    $( The canonical representation of an integer ` N ` in a ring ` R ` is in
       the centralizer of the ring's multiplicative monoid.  (Contributed by
       Thierry Arnoux, 5-Oct-2025.) $)
    zrhcntr $p |- ( ph -> ( L ` N ) e. C ) $=
      ( vx wcel cfv wa wceq co adantr cz ad2antrr vm vi vn cneg cv fveq2 eleq1d
      cn0 wral cc0 c1 caddc cbs cmulr c0g crg eqid zrh0 ring0cl eqeltrd ringlzd
      syl ringrzd eqtr4d oveq1d oveq2d 3eqtr4d ralrimiva mgpbas mgpplusg elcntr
      simpr sylanbrc cur cplusg czring cghm crh zrhrhm rhmghm 3syl simplr nn0zd
      1zzd zringbas zringplusg ghmlin zrh1 eqtrd cgrp ringgrpd wss ccntr cntrss
      syl3anc eqsstri a1i sselda ringidcl adantll ad3antrrr ringlidmd ringridmd
      grpcld oveq12d ringdird ringdid nn0indd rspcdva wf rhmf ffvelcdmd cminusg
      cntri sylib simpld ringmneg1 zcnd negnegd znegcld zringinvg eqtr3d fveq2d
      cc ghminv syl2anc ringmneg2 simprd r19.21bi cr wo elznn0 mpjaodan ) AFUHM
      ZFDNZBMZFUDZUHMZAYNOUAUEZDNZBMZYPUAUHFYSFPYTYOBYSFDUFUGAUUAUAUHUIZYNAUUAU
      AUHAUBUEZDNZBMUJDNZBMZUCUEZDNZBMZUUGUKULQZDNZBMUUAUBUCYSUUCUJPUUDUUEBUUCU
      JDUFUGUUCUUGPUUDUUHBUUCUUGDUFUGUUCUUJPUUDUUKBUUCUUJDUFUGUUCYSPUUDYTBUUCYS
      DUFUGAUUECUMNZMUUELUEZCUNNZQZUUMUUEUUNQZPZLUULUIUUFAUUECUONZUULACUPMZUUEU
      URPJCDUURIUURUQZURVBZAUUSUURUULMJUULCUURUULUQZUUTUSVBUTAUUQLUULAUUMUULMZO
      ZUURUUMUUNQZUUMUURUUNQZUUOUUPUVDUVEUURUVFUVDUULCUUNUUMUURUVBUUNUQZUUTAUUS
      UVCJRZAUVCVLZVAUVDUULCUUNUUMUURUVBUVGUUTUVHUVIVCVDAUUOUVEPUVCAUUEUURUUMUU
      NUVAVERAUUPUVFPUVCAUUEUURUUMUUNUVAVFRVGVHLUUEUULUUNEBUULCEGUVBVIZCUUNEGUV
      GVJZHVKVMAUUGUHMZOZUUIOZUUKUUHCVNNZCVONZQZBUVNUUKUUHUKDNZUVPQZUVQUVNDVPCV
      QQMZUUGSMUKSMUUKUVSPAUVTUVLUUIAUUSDVPCVRQMZUVTJCDIVSZVPCDVTZWATUVNUUGAUVL
      UUIWBWCUVNWDULUVPVPCUUGDUKSWEWFUVPUQZWGWOUVNUVRUVOUUHUVPAUVRUVOPZUVLUUIAU
      USUWEJCUVODIUVOUQZWHVBTVFWIUVNUVQUULMUVQUUMUUNQZUUMUVQUUNQZPZLUULUIUVQBMU
      VNUULUVPCUUHUVOUVBUWDACWJMUVLUUIACJWKTUVMBUULUUHBUULWLUVMBEWMNUULHUULEUVJ
      WNWPWQWRZAUVOUULMZUVLUUIAUUSUWKJUULCUVOUVBUWFWSZVBTXDUVNUWILUULUVNUVCOZUU
      HUUMUUNQZUVOUUMUUNQZUVPQUUMUUHUUNQZUUMUVOUUNQZUVPQUWGUWHUWMUWNUWPUWOUWQUV
      PUUIUVCUWNUWPPUVMUULUUNEUUHUUMBUVJUVKHXNWTUWMUWOUUMUWQUWMUULCUUNUVOUUMUVB
      UVGUWFAUUSUVLUUIUVCJXAZUVNUVCVLZXBUWMUULCUUNUVOUUMUVBUVGUWFUWRUWSXCVDXEUW
      MUULUVPCUUNUUHUVOUUMUVBUWDUVGUWRUVNUUHUULMUVCUWJRZUWMUUSUWKUWRUWLVBZUWSXF
      UWMUULUVPCUUNUUMUUHUVOUVBUWDUVGUWRUWSUWTUXAXGVGVHLUVQUULUUNEBUVJUVKHVKVMU
      TXHVHZRAYNVLXIAYROZYOUULMYOUUMUUNQZUUMYOUUNQZPZLUULUIYPUXCSUULFDASUULDXJZ
      YRAUUSUWAUXGJUWBSUULVPCDWEUVBXKWARAFSMZYRKRXLUXCUXFLUULUXCUVCOZYQDNZCXMNZ
      NZUUMUUNQUXJUUMUUNQZUXKNZUXDUXEUXIUULCUUNUXKUXJUUMUVBUVGUXKUQZAUUSYRUVCJT
      ZUXCUXJUULMZUVCUXCUXQUXMUUMUXJUUNQZPZLUULUIZUXCUXJBMZUXQUXTOUXCUUAUYAUAUH
      YQYSYQPYTUXJBYSYQDUFUGAUUBYRUXBRAYRVLXILUXJUULUUNEBUVJUVKHVKXOZXPRZUXCUVC
      VLZXQUXIYOUXLUUMUUNUXIYOYQVPXMNZNZDNZUXLUXIFUYFDUXIYQUDZFUYFUXIFAFYDMYRUV
      CAFKXRTXSAUYHUYFPZYRUVCAYQSMZUYIAFKXTZYQYAVBTYBYCUXIUVTUYJUYGUXLPUXIUUSUW
      AUVTUXPUWBUWCWAAUYJYRUVCUYKTSVPCDUYEUXKYQWEUYEUQUXOYEYFWIZVEUXIUUMUXLUUNQ
      UXRUXKNUXEUXNUXIUULCUUNUXKUUMUXJUVBUVGUXOUXPUYDUYCYGUXIYOUXLUUMUUNUYLVFUX
      IUXMUXRUXKUXCUXSLUULUXCUXQUXTUYBYHYIYCVGVGVHLYOUULUUNEBUVJUVKHVKVMAFYJMZY
      NYRYKZAUXHUYMUYNOKFYLXOYHYM $.
  $}

  $( Lemma for ~ qqhval2 .  (Contributed by Thierry Arnoux, 29-Oct-2017.) $)
  elzdif0 $p |- ( M e. ( ZZ \ { 0 } ) -> ( M e. NN \/ -u M e. NN ) ) $=
    ( cz cc0 csn cdif wcel wceq wn cn cneg wo eldifsnneq w3o cr wa eldifi sylib
    elz simprd 3orass orel1 sylc ) ABCDZEFZACGZHUEAIFZAJIFZKZKZUHABCLUDUEUFUGMZ
    UIUDANFZUJUDABFUKUJOABUCPARQSUEUFUGTQUEUHUAUB $.

  ${
    qqhval2.0 $e |- B = ( Base ` R ) $.
    qqhval2.1 $e |- ./ = ( /r ` R ) $.
    qqhval2.2 $e |- L = ( ZRHom ` R ) $.
    $( Lemma for ~ qqhval2 .  (Contributed by Thierry Arnoux, 29-Oct-2017.) $)
    qqhval2lem $p |- ( ( ( R e. DivRing /\ ( chr ` R ) = 0 )
      /\ ( X e. ZZ /\ Y e. ZZ /\ Y =/= 0 ) )
         -> ( ( L ` ( numer ` ( X / Y ) ) ) ./ ( L ` ( denom ` ( X / Y ) ) ) )
         = ( ( L ` X ) ./ ( L ` Y ) ) ) $=
      ( wcel cfv cc0 wceq wa cz co cmul czring wn fveq2d cdr cchr wne cgcd cdiv
      w3a cnumer cdenom crh cui crg drngring zrhrhm syl cdvds wbr simpr1 simpr2
      ad2antrr gcdcld nn0zd simpr3 gcdeq0 simplbda necon3d imp syl21anc gcddvds
      ex syl2anc simpld dvdsval2 biimpa syl31anc simprd zringbas rhmf ffvelcdmd
      c0g wf wfn ccnv cima ffnd zcnd divne0d ovex elsn necon3bbii sylibr simplr
      eqid zrhker neleqtrrd elpreima baibd biimprd con3dimp fvex sylib drngunit
      csn wb mpbir2and zringmulr rhmdvd syl132anc cneg divnumden eqcomd oveq12d
      cn sylan c1 adantr mulm1d cc neg1cn a1i mulcomd eqtr3d divnumden2 syl3anc
      simpr 1zzd znegcld cabs neg1z ax-1cn absnegi zringunit mpbir2an elrhmunit
      abs1 eqtri 3eqtr4rd wo simp3 neneqd divcan1d w3o cr simp2 elz 3orass sylc
      orel1 adantl mpjaodan 3eqtr3d ) CUAJZCUBKLMZNZEOJZFOJZFLUCZUFZNZEEFUDPZUE
      PZDKZFUUSUEPZDKZBPZUUTUUSQPZDKZUVBUUSQPZDKZBPZEFUEPZUGKZDKZUVJUHKZDKZBPZE
      DKZFDKZBPUURDRCUIPJZUUTOJZUVBOJZUUSOJZUVCCUJKZJZUUSDKZUWBJZUVDUVIMUUKUVRU
      ULUUQUUKCUKJZUVRCULZCDIUMUNUSZUURUWAUUSLUCZUUNUUSEUOUPZUVSUURUUSUUREFUUMU
      UNUUOUUPUQZUUMUUNUUOUUPURZUTVAZUURUUNUUOUUPUWIUWKUWLUUMUUNUUOUUPVBZUUNUUO
      NZUUPUWIUWOUUSLFLUWOUUSLMZFLMZUWOUWPELMUWQEFVCVDVIVEVFVGZUWKUURUWJUUSFUOU
      PZUURUUNUUOUWJUWSNUWKUWLEFVHVJZVKUWAUWIUUNUFUWJUVSUUSEVLVMVNZUURUWAUWIUUO
      UWSUVTUWMUWRUWLUURUWJUWSUWTVOUWAUWIUUOUFUWSUVTUUSFVLVMVNZUWMUURUWCUVCAJZU
      VCCVSKZUCZUUROAUVBDUURUVROADVTUWHOARCDVPGVQUNZUXBVRUURDOWAZUVTUVBDWBUXDXB
      ZWCZJZSZUXEUUROADUXFWDZUXBUURUXILXBZUVBUURUVBLUCUVBUXMJZSUURFUUSUURFUWLWE
      ZUURUUSUWMWEZUWNUWRWFUXNUVBLUVBLFUUSUEWGWHWIWJUURUWFUULUXIUXMMZUUKUWFUULU
      UQUWGUSUUKUULUUQWKUWFUULUXQACDUXDGIUXDWLZWMVMVJZWNUXGUVTNZUXKNUVCUXHJZSUX
      EUXTUYAUXJUXTUXJUYAUXGUXJUVTUYAOUVBUXHDWOWPWQWRUYAUVCUXDUVCUXDUVBDWSWHWIW
      TVGUUKUWCUXCUXENXCUULUUQACUWBUVCUXDGUWBWLZUXRXAUSXDZUURUWEUWDAJZUWDUXDUCZ
      UUROAUUSDUXFUWMVRUURUXGUWAUUSUXIJZSZUYEUXLUWMUURUXIUXMUUSUURUWIUUSUXMJZSU
      WRUYHUUSLUUSLEFUDWGWHWIWJUXSWNUXGUWANZUYGNUWDUXHJZSUYEUYIUYJUYFUYIUYFUYJU
      XGUYFUWAUYJOUUSUXHDWOWPWQWRUYJUWDUXDUWDUXDUUSDWSWHWIWTVGUUKUWEUYDUYENXCUU
      LUUQACUWBUWDUXDGUYBUXRXAUSXDUUTUVBUUSBRCQUWBDOUYBVPHXEXFXGUURFXLJZUVDUVOM
      FXHXLJZUURUYKNZUVAUVLUVCUVNBUYMUUTUVKDUYMUVKUUTUYMUVKUUTMZUVMUVBMZUURUUNU
      YKUYNUYONUWKEFXIXMZVKXJTUYMUVBUVMDUYMUVMUVBUYMUYNUYOUYPVOXJTXKUURUYLNZUUT
      XHZDKZUVBXHZDKZBPUUTXNXHZQPZDKZUVBVUBQPZDKZBPZUVOUVDUYQUYSVUDVUAVUFBUYQUY
      RVUCDUYQVUBUUTQPUYRVUCUYQUUTUYQUUTUURUVSUYLUXAXOZWEZXPUYQVUBUUTVUBXQJUYQX
      RXSZVUIXTYATUYQUYTVUEDUYQVUBUVBQPUYTVUEUYQUVBUYQUVBUURUVTUYLUXBXOZWEZXPUY
      QVUBUVBVUJVULXTYATXKUYQUVLUYSUVNVUABUYQUVKUYRDUYQUVKUYRMZUVMUYTMZUYQUUNUU
      OUYLVUMVUNNUURUUNUYLUWKXOUURUUOUYLUWLXOUURUYLYDEFYBYCZVKTUYQUVMUYTDUYQVUM
      VUNVUOVOTXKUYQUVRUVSUVTVUBOJZUWCVUBDKUWBJZUVDVUGMUURUVRUYLUWHXOZVUHVUKUYQ
      XNUYQYEYFUURUWCUYLUYCXOUYQUVRVUBRUJKJZVUQVURVUSUYQVUSVUPVUBYGKZXNMYHVUTXN
      YGKXNXNYIYJYNYOVUBYKYLXSVUBRCDYMVJUUTUVBVUBBRCQUWBDOUYBVPHXEXFXGYPUUQUYKU
      YLYQZUUMUUQUWQSUWQVVAYQZVVAUUQFLUUNUUOUUPYRYSUUQUWQUYKUYLUUAZVVBUUQFUUBJZ
      VVCUUQUUOVVDVVCNUUNUUOUUPUUCFUUDWTVOUWQUYKUYLUUEWTUWQVVAUUGUUFUUHUUIUURUV
      FUVPUVHUVQBUURUVEEDUUREUUSUUREUWKWEUXPUWRYTTUURUVGFDUURFUUSUXOUXPUWRYTTXK
      UUJ $.

    $d e q s x y ./ $.  $d e q s x y B $.  $d e q s x y L $.  $d e q s x y R $.
    $( Value of the canonical homormorphism from the rational number when the
       target ring is a division ring.  (Contributed by Thierry Arnoux,
       26-Oct-2017.) $)
    qqhval2 $p |- ( ( R e. DivRing /\ ( chr ` R ) = 0 ) -> ( QQHom ` R ) =
      ( q e. QQ |-> ( ( L ` ( numer ` q ) ) ./ ( L ` ( denom ` q ) ) ) ) ) $=
      ( vx vy ve vs wcel cfv cc0 wceq wa cz co cq cdr cchr cqqh ccnv cui cv cop
      cima cdiv cmpo crn csn cdif cnumer cdenom cmpt cvv elex adantr cur qqhval
      eqid syl c0g zrhunitpreima mpoeq12 sylancr rneqd wrex cab copab nfv nfab1
      nfcv wex simpr wne zssq simplrl sselid simplrr eldifad eldifbd necon3bbii
      velsn sylib qdivcl syl3anc simplll simpllr w3a qqhval2lem eqcomd syl23anc
      wn ovex opeq12 eqeq2d simpl eleq1d fveq2d oveq12d eqeq12d spc2ev syl12anc
      anbi12d ex rexlimdvva imp 19.42vv simprrl qnumcl cn nnzd nnne0 nelsn 3syl
      qdencl eldifd simprl qeqnumdivden simprrr opeq12d eqtrd oveq1 fveq2 oveq2
      oveq1d oveq2d rspc2ev exlimivv sylbir impbida elopab 3bitr4g rnmpo df-mpt
      abid eqrd 3eqtr4g 3eqtrd ) CUAMZCUBNOPZQZCUCNZIJRDUDCUENUHZIUFZJUFZUISZUU
      GDNZUUHDNZBSZUGZUJZUKZIJRROULZUMZUUMUJZUKZETEUFZUNNZDNZUUTUONZDNZBSZUPZUU
      DCUQMZUUEUUOPUUBUVGUUCCUAURUSIJBCCUTNZDGUVHVBHVAVCUUDUUNUURUUDRRPUUFUUQPU
      UNUURPRVBACDCVDNZFHUVIVBVEIJRUUFRUUQUUMVFVGVHUUDKUFZUUMPZJUUQVIIRVIZKVJZU
      UTTMZLUFZUVEPZQZELVKZUUSUVFUUDKUVMUVRUUDKVLUVLKVMKUVRVNUUDUVLUVJUUTUVOUGZ
      PZUVQQZLVOEVOZUVJUVMMUVJUVRMUUDUVLUWBUUDUVLUWBUUDUVKUWBIJRUUQUUDUUGRMZUUH
      UUQMZQZQZUVKUWBUWFUVKQZUVKUUITMZUULUUIUNNZDNZUUIUONZDNZBSZPZUWBUWFUVKVPUW
      GUUGTMUUHTMUUHOVQZUWHUWGRTUUGVRUUDUWCUWDUVKVSZVTUWGRTUUHVRUWGUUHRUUPUUDUW
      CUWDUVKWAZWBZVTUWGUUHUUPMZWOUWOUWGUUHRUUPUWQWCUWSUUHOJOWEWDWFZUUGUUHWGWHU
      WGUUBUUCUWCUUHRMZUWOUWNUUBUUCUWEUVKWIUUBUUCUWEUVKWJUWPUWRUWTUUDUWCUXAUWOW
      KQUWMUULABCDUUGUUHFGHWLWMWNUWAUVKUWHUWNQZQELUUIUULUUGUUHUIWPUUJUUKBWPUUTU
      UIPZUVOUULPZQZUVTUVKUVQUXBUXEUVSUUMUVJUUTUVOUUIUULWQWRUXEUVNUWHUVPUWNUXEU
      UTUUITUXCUXDWSZWTUXEUVOUULUVEUWMUXCUXDVPUXEUVBUWJUVDUWLBUXEUVAUWIDUXEUUTU
      UIUNUXFXAXAUXEUVCUWKDUXEUUTUUIUOUXFXAXAXBXCXFXFXDXEXGXHXIUUDUWBQUUDUWAQZL
      VOEVOUVLUUDUWAELXJUXGUVLELUXGUVARMZUVCUUQMUVJUVAUVCUISZUVEUGZPZUVLUXGUVNU
      XHUUDUVTUVNUVPXKZUUTXLVCUXGUVCRUUPUXGUVCUXGUVNUVCXMMZUXLUUTXRVCZXNUXGUXMU
      VCOVQUVCUUPMWOUXNUVCXOUVCOXPXQXSUXGUVJUVSUXJUUDUVTUVQXTUXGUUTUXIUVOUVEUXG
      UVNUUTUXIPUXLUUTYAVCUUDUVTUVNUVPYBYCYDUVKUXKUVJUVAUUHUISZUVBUUKBSZUGZPIJU
      VAUVCRUUQUUGUVAPZUUMUXQUVJUXRUUIUXOUULUXPUUGUVAUUHUIYEUXRUUJUVBUUKBUUGUVA
      DYFYHYCWRUUHUVCPZUXQUXJUVJUXSUXOUXIUXPUVEUUHUVCUVAUIYGUXSUUKUVDUVBBUUHUVC
      DYFYIYCWRYJWHYKYLYMUVLKYRUVQELUVJYNYOYSIJKRUUQUUMUURUURVBYPELTUVEYQYTUUA
      $.

    $d q Q $.
    $( Value of the canonical homormorphism from the rational number when the
       target ring is a division ring.  (Contributed by Thierry Arnoux,
       30-Oct-2017.) $)
    qqhvval $p |- ( ( ( R e. DivRing /\ ( chr ` R ) = 0 ) /\ Q e. QQ ) ->
      ( ( QQHom ` R ) ` Q )
          = ( ( L ` ( numer ` Q ) ) ./ ( L ` ( denom ` Q ) ) ) ) $=
      ( vq cdr wcel cfv wceq wa cq cnumer cdenom co simpr fveq2d cchr cqqh cmpt
      cc0 cv cvv qqhval2 adantr oveq12d ovexd fvmptd ) DJKDUALUDMNZCOKZNZICIUEZ
      PLZELZUOQLZELZBRZCPLZELZCQLZELZBRODUBLZUFULVEIOUTUCMUMABDEIFGHUGUHUNUOCMZ
      NZUQVBUSVDBVGUPVAEVGUOCPUNVFSZTTVGURVCEVGUOCQVHTTUIULUMSUNVBVDBUJUK $.

    $( The image of ` 0 ` by the ` QQHom ` homomorphism is the ring's zero.
       (Contributed by Thierry Arnoux, 22-Oct-2017.) $)
    qqh0 $p |- ( ( R e. DivRing /\ ( chr ` R ) = 0 )
                                     -> ( ( QQHom ` R ) ` 0 ) = ( 0g ` R ) ) $=
      ( wcel cfv cc0 wceq wa co cq cz 0z c1 fveq2i eqid syl cdr cchr cnumer c0g
      cqqh cdenom zssq sselii qqhvval mpan2 cgcd cdiv cabs 1z gcd0id ax-mp abs1
      eqtri 0cn div1i eqcomi pm3.2i cn wb qnumdenbi mp3an simpli simpri oveq12i
      1nn mpbi cur drngring zrh0 zrh1 oveq12d cgrp drnggrp grpidcl dvr1 syl2anc
      crg eqtrd eqtrid adantr ) CUAHZCUBIJKZLZJCUEIIZJUCIZDIZJUFIZDIZBMZCUDIZWH
      JNHZWIWNKONJUGPUHZABJCDEFGUIUJWFWNWOKWGWFWNJDIZQDIZBMZWOWKWRWMWSBWJJDWJJK
      ZWLQKZJQUKMZQKZJJQULMZKZLZXAXBLZXDXFXCQUMIZQQOHXCXIKUNQUOUPUQURXEJJUSUTVA
      VBWPJOHQVCHXGXHVDWQPVJJJQVEVFVKZVGRWLQDXAXBXJVHRVIWFWTWOCVLIZBMZWOWFCWBHZ
      WTXLKCVMZXMWRWOWSXKBCDWOGWOSZVNCXKDGXKSZVOVPTWFXMWOAHZXLWOKXNWFCVQHXQCVRA
      CWOEXOVSTABCXKWOEFXPVTWAWCWDWEWC $.

    $( The image of ` 1 ` by the ` QQHom ` homomorphism is the ring unity.
       (Contributed by Thierry Arnoux, 22-Oct-2017.) $)
    qqh1 $p |- ( ( R e. DivRing /\ ( chr ` R ) = 0 )
                                     -> ( ( QQHom ` R ) ` 1 ) = ( 1r ` R ) ) $=
      ( cdr wcel cchr cfv wceq wa c1 co cq cz 1z fveq2i eqtrd cc0 cnumer cdenom
      cqqh zssq sselii qqhvval mpan2 cgcd cdiv gcd1 ax-mp 1div1e1 eqcomi pm3.2i
      cur cn wb 1nn qnumdenbi mpbi simpli simpri oveq12i crg drngring eqid zrh1
      mp3an oveq12d syl ringidcl dvr1 syl2anc2 eqtrid adantr ) CHIZCJKUALZMZNCU
      DKKZNUBKZDKZNUCKZDKZBOZCUPKZVSNPIZVTWELQPNUERUFZABNCDEFGUGUHVQWEWFLVRVQWE
      NDKZWIBOZWFWBWIWDWIBWANDWANLZWCNLZNNUIONLZNNNUJOZLZMZWKWLMZWMWONQIZWMRNUK
      ULWNNUMUNUOWGWRNUQIWPWQURWHRUSNNNUTVIVAZVBSWCNDWKWLWSVCSVDVQWJWFWFBOZWFVQ
      CVEIZWJWTLCVFZXAWIWFWIWFBCWFDGWFVGZVHZXDVJVKVQXAWFAIWTWFLXBACWFEXCVLABCWF
      WFEFXCVMVNTVOVPT $.

    $( TODO simplify this & others using properties of ` ( CClfd |`s ZZ )` $)
    $( ` QQHom ` as a function.  (Contributed by Thierry Arnoux,
       28-Oct-2017.) $)
    qqhf $p |- ( ( R e. DivRing /\ ( chr ` R ) = 0 )
      -> ( QQHom ` R ) : QQ --> B ) $=
      ( vq wcel cfv cc0 wceq wa cq cdenom co adantr cz czring 3syl cchr cv cqqh
      cdr cnumer qqhval2 crg cui drngring wf zrhrhm zringbas rhmf qnumcl adantl
      crh ffvelcdmd c0g wne simpll qdencl nnzd csn ccnv cima nnne0d neneqd fvex
      cn wn elsn sylnibr eqid zrhker biimpa sylan neleqtrrd wfn wb ffn elpreima
      biimpar con3dimp syl21anc sylnib neqned drngunit syl12anc syl3anc fmpt3d
      expr dvrcl ) CUDIZCUAJKLZMZHNHUBZUEJZDJZWPOJZDJZBPZACUCJABCDHEFGUFWOWPNIZ
      MZCUGIZWRAIWTCUHJZIZXAAIWOXDXBWMXDWNCUIZQQZXCRAWQDXCXDDSCUPPIZRADUJZXHCDG
      UKZRASCDULEUMZTZXBWQRIWOWPUNUOUQXCWMWTAIZWTCURJZUSZXFWMWNXBUTZXCRAWSDXMXC
      WSXBWSVIIWOWPVAUOZVBZUQXCWTXOXCWTXOVCZIZWTXOLXCWMWSRIZWSDVDXTVEZIZVJYAVJX
      QXSXCYCKVCZWSXCWSKLWSYEIXCWSKXCWSXRVFVGWSKWPOVHVKVLWOYCYELZXBWMXDWNYFXGXD
      WNYFACDXOEGXOVMZVNVOVPQVQWMYBMYAYDWMYBYAYDWMYDYBYAMZWMXDDRVRZYDYHVSXGXDXI
      XJYIXKXLRADVTTRWSXTDWATWBWKWCWDWTXOWSDVHVKWEWFWMXFXNXPMACXEWTXOEXEVMZYGWG
      WBWHABCXEWRWTEYJFWLWIWJ $.

    $( The image of a quotient by the ` QQHom ` homomorphism.  (Contributed by
       Thierry Arnoux, 28-Oct-2017.) $)
    qqhvq $p |- ( ( ( R e. DivRing /\ ( chr ` R ) = 0 )
      /\ ( X e. ZZ /\ Y e. ZZ /\ Y =/= 0 ) )
             -> ( ( QQHom ` R ) ` ( X / Y ) ) = ( ( L ` X ) ./ ( L ` Y ) ) ) $=
      ( cdr wcel cfv cc0 wceq wa cz co cq zssq sselid cchr wne cdiv cqqh cnumer
      w3a cdenom simpr1 simpr2 simpr3 qdivcl syl3anc qqhvval syldan qqhval2lem
      eqtrd ) CJKCUALMNOZEPKZFPKZFMUBZUFZOZEFUCQZCUDLLZVCUELDLVCUGLDLBQZEDLFDLB
      QUQVAVCRKZVDVENVBERKFRKUTVFVBPRESUQURUSUTUHTVBPRFSUQURUSUTUITUQURUSUTUJEF
      UKULABVCCDGHIUMUNABCDEFGHIUOUP $.

    $d x y Q $.
    qqhrhm.1 $e |- Q = ( CCfld |`s QQ ) $.
    $( The ` QQHom ` homomorphism is a group homomorphism if the target
       structure is a division ring.  (Contributed by Thierry Arnoux,
       9-Nov-2017.) $)
    qqhghm $p |- ( ( R e. DivRing /\ ( chr ` R ) = 0 )
                                       -> ( QQHom ` R ) e. ( Q GrpHom R ) ) $=
      ( wcel cfv cc0 wceq caddc cq cmul co cz czring zringbas vx vy cdr cchr wa
      cplusg cqqh qrngbas cvv ccnfld cnfldadd ressplusg ax-mp eqid cgrp drnggrp
      qex qdrng mp1i adantr qqhf cv cnumer cdenom crg cui drngring ad2antrr crh
      wf zrhrhm rhmf 3syl qnumcl ad2antrl cn qdencl ad2antll nnzd zmulcld cmulr
      ffvelcdmd syl zringmulr rhmmul syl3anc wne nnne0d c0g elzrhunit unitmulcl
      simpl syl12anc eqeltrd syl13anc cdiv qeqnumdivden oveq12d zcnd divadddivd
      dvrdir eqtrd fveq2d zaddcld mulne0d qqhvq rhmghm zringplusg ghmlin oveq1d
      cghm w3a 3eqtrd rhmdvd syl132anc mulcomd oveq2d 3eqtr4d isghmd ) DUCJZDUD
      KLMZUEZUAUBNDUFKZCDDUGKZOACIUHFOUIJNCUFKMUQONUJCUIIUKULUMYCUNZCUCJCUOJYBC
      IURCUPUSXTDUOJYADUPUTABDEFGHVAYBUAVBZOJZUBVBZOJZUEZUEZYFVCKZYHVDKZPQZEKZY
      HVCKZYFVDKZPQZEKZYCQZYQYMPQZEKZBQZYOUUBBQZYSUUBBQZYCQZYFYHNQZYDKZYFYDKZYH
      YDKZYCQYKDVEJZYOAJYSAJUUBDVFKZJUUCUUFMXTUUKYAYJDVGZVHZYKRAYNEYBRAEVJZYJYB
      UUKESDVIQJZUUOXTUUKYAUUMUTDEHVKZRASDETFVLVMUTZYKYLYMYGYLRJZYBYIYFVNVOZYKY
      MYIYMVPJYBYGYHVQVRZVSZVTZWBYKRAYREUURYKYPYQYIYPRJZYBYGYHVNVRZYKYQYGYQVPJY
      BYIYFVQVOZVSZVTZWBYKUUBYQEKZYMEKZDWAKZQZUULYKUUPYQRJZYMRJZUUBUVLMYKUUKUUP
      UUNUUQWCZUVGUVBYQYMSDPUVKERTWDUVKUNZWEWFYKUUKUVIUULJZUVJUULJZUVLUULJUUNYK
      YBUVMYQLWGZUVQYBYJWLZUVGYKYQUVFWHZADEYQDWIKZFHUWBUNZWJWMZYKYBUVNYMLWGZUVR
      UVTUVBYKYMUVAWHZADEYMUWBFHUWCWJWMZDUVKUULUVIUVJUULUNZUVPWKWFWNABYCDUULYOY
      SUUBFUWHYEGXAWOYKUUHYNYRNQZUUAWPQZYDKZUWIEKZUUBBQZUUCYKUUGUWJYDYKUUGYLYQW
      PQZYPYMWPQZNQUWJYKYFUWNYHUWONYGYFUWNMYBYIYFWQZVOYIYHUWOMYBYGYHWQZVRWRYKYL
      YQYPYMYKYLUUTWSYKYQUVGWSZYKYPUVEWSYKYMUVBWSZUWAUWFWTXBXCYKYBUWIRJUUARJUUA
      LWGUWKUWMMUVTYKYNYRUVCUVHXDYKYQYMUVGUVBVTYKYQYMUWRUWSUWAUWFXEABDEUWIUUAFG
      HXFWOYKESDXKQJZYNRJZYRRJZUWMUUCMYKUUPUWTUVOSDEXGWCUVCUVHUWTUXAUXBXLUWLYTU
      UBBNYCSDYNEYRRTXHYEXIXJWFXMYKUUIUUDUUJUUEYCYKUUIUWNYDKZYLEKUVIBQZUUDYGUUI
      UXCMYBYIYGYFUWNYDUWPXCVOYKYBUUSUVMUVSUXCUXDMUVTUUTUVGUWAABDEYLYQFGHXFWOYK
      UUPUUSUVMUVNUVQUVRUXDUUDMUVOUUTUVGUVBUWDUWGYLYQYMBSDPUULERUWHTGWDXNXOXMYK
      UUJUWOYDKZUUEYIUUJUXEMYBYGYIYHUWOYDUWQXCVRYKYPEKUVJBQZYSYMYQPQZEKZBQZUXEU
      UEYKUUPUVDUVNUVMUVRUVQUXFUXIMUVOUVEUVBUVGUWGUWDYPYMYQBSDPUULERUWHTGWDXNXO
      YKYBUVDUVNUWEUXEUXFMUVTUVEUVBUWFABDEYPYMFGHXFWOYKUUBUXHYSBYKUUAUXGEYKYQYM
      UWRUWSXPXCXQXRXBWRXRXS $.

    $( TODO - Shorten using ~ qqhghm ! $)
    $( The ` QQHom ` homomorphism is a ring homomorphism if the target
       structure is a field.  If the target structure is a division ring, it is
       a group homomorphism, but not a ring homomorphism, because it does not
       preserve the ring multiplication operation.  (Contributed by Thierry
       Arnoux, 29-Oct-2017.) $)
    qqhrhm $p |- ( ( R e. Field /\ ( chr ` R ) = 0 )
                                       -> ( QQHom ` R ) e. ( Q RingHom R ) ) $=
      ( wcel cfv wceq cq caddc cmul eqid co cz czring zringbas vx vy cfield cc0
      cchr wa cplusg cmulr c1 cqqh cur qrngbas cvv qex ccnfld cnfldmul ressmulr
      qrng1 ax-mp cdr crg qdrng drngring mp1i ccrg isfld simplbi syl qqh1 sylan
      adantr cv cnumer cdenom cui simprbi ad2antrr wf zrhrhm rhmf 3syl ad2antrl
      crh qnumcl ffvelcdmd wne simplr jca qdencl nnzd nnne0d elzrhunit syl12anc
      cn c0g ad2antll rdivmuldivd cdiv qeqnumdivden fveq2d qqhvq syl13anc eqtrd
      oveq12d zcnd divmuldivd zmulcld mulne0d zringmulr rhmmul syl3anc 3eqtr4rd
      3eqtrd cnfldadd ressplusg qqhf unitmulcl eqeltrd dvrdir divadddivd rhmghm
      zaddcld cghm w3a zringplusg ghmlin oveq1d rhmdvd syl132anc mulcomd oveq2d
      3eqtr4d isrhmd ) DUCJZDUEKUDLZUFZUAUBMANDUGKZCDODUHKZUIDUJKZDUKKZCIULCIUR
      YTPMUMJZOCUHKLUNMUOCOUMIUPUQUSYRPZCUTJCVAJYPCIVBCVCVDYPDUTJZDVAJZYNUUCYOY
      NUUCDVEJZDVFZVGZVKDVCZVHZYNUUCYOUIYSKYTLUUGABDEFGHVIVJYPUAVLZMJZUBVLZMJZU
      FZUFZUUJVMKZEKZUUJVNKZEKZBQZUULVMKZEKZUULVNKZEKZBQZYRQUUQUVBYRQZUUSUVDYRQ
      ZBQZUUJYSKZUULYSKZYRQUUJUULOQZYSKZUUOABYQDYRDVOKZUVDUUQUUSUVBFUVMPZYQPZGU
      UBYNUUEYOUUNYNUUCUUEUUFVPVQUUORAUUPEYPRAEVRZUUNYPUUDESDWCQJZUVPUUIDEHVSZR
      ASDETFVTWAVKZUUKUUPRJZYPUUMUUJWDWBZWEUUOUUCYOUFZUURRJZUURUDWFZUUSUVMJZUUO
      UUCYOYNUUCYOUUNUUGVQZYNYOUUNWGWHZUUOUURUUKUURWNJYPUUMUUJWIWBZWJZUUOUURUWH
      WKZADEUURDWOKZFHUWKPZWLWMZUUORAUVAEUVSUUMUVARJZYPUUKUULWDWPZWEUUOUWBUVCRJ
      ZUVCUDWFZUVDUVMJZUWGUUOUVCUUMUVCWNJYPUUKUULWIWPZWJZUUOUVCUWSWKZADEUVCUWKF
      HUWLWLWMZWQUUOUVIUUTUVJUVEYRUUOUVIUUPUURWRQZYSKZUUTUUKUVIUXDLYPUUMUUKUUJU
      XCYSUUJWSZWTWBZUUOUWBUVTUWCUWDUXDUUTLUWGUWAUWIUWJABDEUUPUURFGHXAXBZXCUUOU
      VJUVAUVCWRQZYSKZUVEUUMUVJUXILYPUUKUUMUULUXHYSUULWSZWTWPZUUOUWBUWNUWPUWQUX
      IUVELUWGUWOUWTUXAABDEUVAUVCFGHXAXBZXCXDUUOUVLUUPUVAOQZUURUVCOQZWRQZYSKZUX
      MEKZUXNEKZBQZUVHUUOUVKUXOYSUUOUVKUXCUXHOQUXOUUOUUJUXCUULUXHOUUKUUJUXCLYPU
      UMUXEWBZUUMUULUXHLYPUUKUXJWPZXDUUOUUPUURUVAUVCUUOUUPUWAXEZUUOUURUWIXEZUUO
      UVAUWOXEZUUOUVCUWTXEZUWJUXAXFXCWTUUOUWBUXMRJUXNRJZUXNUDWFZUXPUXSLUWGUUOUU
      PUVAUWAUWOXGUUOUURUVCUWIUWTXGZUUOUURUVCUYCUYEUWJUXAXHZABDEUXMUXNFGHXAXBUU
      OUXQUVFUXRUVGBUUOUVQUVTUWNUXQUVFLUUOUUDUVQUUOUUCUUDUWFUUHVHZUVRVHZUWAUWOU
      UPUVASDOYRERTXIUUBXJXKUUOUVQUWCUWPUXRUVGLUYKUWIUWTUURUVCSDOYRERTXIUUBXJXK
      ZXDXMXLFUUANCUGKLUNMNUOCUMIXNXOUSUVOYNUUCYOMAYSVRUUGABDEFGHXPVJUUOUUPUVCO
      QZEKZUVAUUROQZEKZYQQZUXRBQZUYNUXRBQZUYPUXRBQZYQQZUUJUULNQZYSKZUVIUVJYQQUU
      OUUDUYNAJUYPAJUXRUVMJUYRVUALUYJUUORAUYMEUVSUUOUUPUVCUWAUWTXGZWEUUORAUYOEU
      VSUUOUVAUURUWOUWIXGZWEUUOUXRUVGUVMUYLUUOUUDUWEUWRUVGUVMJUYJUWMUXBDYRUVMUU
      SUVDUVNUUBXQXKXRABYQDUVMUYNUYPUXRFUVNUVOGXSXBUUOVUCUYMUYONQZUXNWRQZYSKZVU
      FEKZUXRBQZUYRUUOVUBVUGYSUUOVUBUXCUXHNQVUGUUOUUJUXCUULUXHNUXTUYAXDUUOUUPUU
      RUVAUVCUYBUYCUYDUYEUWJUXAXTXCWTUUOUWBVUFRJUYFUYGVUHVUJLUWGUUOUYMUYOVUDVUE
      YBUYHUYIABDEVUFUXNFGHXAXBUUOESDYCQJZUYMRJZUYORJZVUJUYRLUUOUVQVUKUYKSDEYAV
      HVUDVUEVUKVULVUMYDVUIUYQUXRBNYQSDUYMEUYORTYEUVOYFYGXKXMUUOUVIUYSUVJUYTYQU
      UOUVIUXDUUTUYSUXFUXGUUOUVQUVTUWCUWPUWEUWRUUTUYSLUYKUWAUWIUWTUWMUXBUUPUURU
      VCBSDOUVMERUVNTGXIYHYIXMUUOUVJUXIUYTUXKUUOUVEUYPUVCUUROQZEKZBQZUXIUYTUUOU
      VQUWNUWPUWCUWRUWEUVEVUPLUYKUWOUWTUWIUXBUWMUVAUVCUURBSDOUVMERUVNTGXIYHYIUX
      LUUOUXRVUOUYPBUUOUXNVUNEUUOUURUVCUYCUYEYJWTYKYLXCXDYLYM $.
  $}

  ${
    qqhnm.n $e |- N = ( norm ` R ) $.
    qqhnm.z $e |- Z = ( ZMod ` R ) $.
    $( The norm of the image by ` QQHom ` of a rational number in a topological
       division ring.  (Contributed by Thierry Arnoux, 8-Nov-2017.) $)
    qqhnm $p |- ( ( ( R e. ( NrmRing i^i DivRing ) /\ Z e. NrmMod
      /\ ( chr ` R ) = 0 ) /\ Q e. QQ )
      -> ( N ` ( ( QQHom ` R ) ` Q ) ) = ( abs ` Q ) ) $=
      ( cnrg cdr wcel cfv cc0 wceq wa cabs cdiv co fveq2d syl cz eqid cnlm cchr
      cin w3a cq cnumer cdenom cqqh simpr qeqnumdivden qnumcl zcnd qdencl nncnd
      cn wne nnne0 3syl absdivd czrh cdvr simpl1 sselid simpl3 qqhvval syl21anc
      inss2 cbs cnzr cui inss1 drngnzr crg czring crh wf drngring zringbas rhmf
      zrhrhm 4syl ffvelcdmd c0g elzrhunit syl22anc nmdvr simpl2 zhmnrg syl31anc
      nnzd zrhnm oveq12d 3eqtrrd ) BGHUCZIZDUAIZBUBJKLZUDZAUEIZMZANJZAUFJZAUGJZ
      OPZNJZXBNJZXCNJZOPZABUHJJZCJZWTWSXAXELWRWSUIZWSAXDNAUJQRWTXBXCWTXBWTWSXBS
      IZXKAUKRZULWTXCWTWSXCUOIZXKAUMZRZUNWTWSXNXCKUPZXKXOXCUQURZUSWTXJXBBUTJZJZ
      XCXSJZBVAJZPZCJZXTCJZYACJZOPZXHWTBHIZWQWSXJYDLWTWNHBGHVGWOWPWQWSVBZVCZWOW
      PWQWSVDZXKYHWQMWSMXIYCCBVHJZYBABXSYLTZYBTZXSTZVEQVFWTBGIZBVIIZXTYLIYABVJJ
      ZIZYDYGLWTWNGBGHVKYIVCZWTYHYQYJBVLRZWTSYLXBXSWTYHBVMIXSVNBVOPISYLXSVPYJBV
      QBXSYOVTSYLVNBXSVRYMVSWAXMWBWTYHWQXCSIZXQYSYJYKWTXCXPWJZXRYLBXSXCBWCJZYMY
      OUUDTWDWEXTYAYBBYRCYLYMEYRTYNWFWEWTYEXFYFXGOWTWPDGIZYQXLYEXFLWOWPWQWSWGZW
      TYPUUEYTBDFWHRZUUAXMYLBXSXBCDYMEFYOWKWIWTWPUUEYQUUBYFXGLUUFUUGUUAUUCYLBXS
      XCCDYMEFYOWKWIWLWMWM $.
  $}

  ${
    $d d e q J $.  $d d e q R $.  $d e q Z $.
    qqhcn.q $e |- Q = ( CCfld |`s QQ ) $.
    qqhcn.j $e |- J = ( TopOpen ` Q ) $.
    qqhcn.z $e |- Z = ( ZMod ` R ) $.
    qqhcn.k $e |- K = ( TopOpen ` R ) $.
    $( The ` QQHom ` homomorphism is a continuous function.  (Contributed by
       Thierry Arnoux, 9-Nov-2017.) $)
    qqhcn $p |- ( ( R e. ( NrmRing i^i DivRing ) /\ Z e. NrmMod
                       /\ ( chr ` R ) = 0 ) -> ( QQHom ` R ) e. ( J Cn K ) ) $=
      ( vq cnrg cdr wcel cfv cc0 wceq cq co eqid ccnfld vd ve cin cnlm cchr w3a
      cqqh ccn ccnp wa cds cbs cxp cres cmopn wf cv cabs cmin ccom clt wbr wral
      wi crp wrex inss2 sseli 3ad2ant1 simp3 cdvr czrh qqhf syl2anc simpr qsscn
      cnm cc sselid cneg 0cn cnmetdval mpan df-neg fveq2i a1i absneg 3eqtr2d cz
      syl zssq sselii ovresd qqhnm adantlr 3eqtr4d csg ad2antrr ffvelcdmd inss1
      0z cngp nrgngp ngpdsr syl3anc c0g qqh0 oveq2d cgrp ngpgrp grpsubid1 eqtrd
      fveq2d 3eqtrd eqtr4d breq1d ralrimiva breq2 rspceaimv cxmet wb cxms cress
      biimpd cvv cnfldxms ressxms mp2an eqeltri qrngbas cnfldds ressds xmsxmet2
      qex ax-mp mp1i 3syl xmstopn ctmd ctgp ngpxms metcnp mpbir2and fveq1d cghm
      reseq1i eleqtrrd csubg cnfldtgp csubrg qsubdrg simpli subgtgp tgptmd ctrg
      subrgsubg nrgtrg trgtmd2 qqhghm ghmcnp mpbid simprd ) BKLUCZMZEUDMZBUENOP
      ZUFZOQMZBUGNZCDUHRMZUVGUVIOCDUIRZNZMZUVHUVJUJZUVGUVIOCBUKNZBULNZUVPUMUNZU
      ONZUIRZNZUVLUVGUVIUVTMZQUVPUVIUPZOJUQZURUSUTZQQUMZUNZRZUAUQZVAVBZOUVINZUW
      CUVINZUVQRZUBUQZVAVBZVDJQVCUAVEVFZUBVEVCZUVGBLMZUVFUWBUVDUVEUWQUVFUVCLBKL
      VGVHVIZUVDUVEUVFVJZUVPBVKNZBBVLNZUVPSZUWTSZUXASZVMVNZUVGUWOUBVEUVGUWMVEMZ
      UJZUXFUWGUWMVAVBZUWNVDZJQVCUWOUVGUXFVOUXGUXIJQUXGUWCQMZUJZUXHUWNUXKUWGUWL
      UWMVAUXKUWGUWKBVQNZNZUWLUXKOUWCUWDRZUWCURNZUWGUXMUXKUWCVRMZUXNUXOPUXKQVRU
      WCVPUXGUXJVOZVSUXPUXNOUWCUSRZURNZUWCVTZURNZUXOOVRMUXPUXNUXSPWAOUWCUWDUWDS
      WBWCUYAUXSPUXPUXTUXRURUWCWDWEWFUWCWGWHWJUXKOUWCUWDQUVHUXKWIQOWKXAWLZWFZUX
      QWMUVGUXJUXMUXOPUXFUWCBUXLEUXLSZHWNWOWPUXKUWLUWJUWKUVORZUWKUWJBWQNZRZUXLN
      ZUXMUXKUWJUWKUVOUVPUXKQUVPOUVIUVGUWBUXFUXJUXEWRZUYCWSZUXKQUVPUWCUVIUYIUXQ
      WSZWMUXKBXBMZUWJUVPMUWKUVPMZUYEUYHPUXKBKMZUYLUVGUYNUXFUXJUVDUVEUYNUVFUVCK
      BKLWTVHZVIZWRBXCZWJZUYJUYKUWJUWKUVOBUYFUXLUVPUYDUXBUYFSZUVOSZXDXEUXKUYGUW
      KUXLUXKUYGUWKBXFNZUYFRZUWKUXKUWJVUAUWKUYFUXKUWQUVFUWJVUAPUVGUWQUXFUXJUWRW
      RUVGUVFUXFUXJUWSWRUVPUWTBUXAUXBUXCUXDXGVNXHUXKBXIMZUYMVUBUWKPUXKUYLVUCUYR
      BXJWJUYKUVPBUYFUWKVUAUXBVUASUYSXKVNXLXMXNXOXPYDXQUWIUXHUWNUAJUWMVEQUWHUWM
      UWGVAXRXSVNXQUVGUWFQXTNMZUVQUVPXTNMZUVHUWAUWBUWPUJYAAYBMZVUDUVGATQYCRZYBF
      TYBMQYEMZVUGYBMYFYNQTYEYGYHYIZUWDAQAFYJZVUHUWDAUKNZPYNQUWDTAYEFYKYLYOZYMY
      PUVGBYBMZVUEUVDUVEVUMUVFUVDUYNUYLVUMUYOUYQBUUAYQVIZUVOBUVPUXBUYTYMWJUVHUV
      GUYBWFUBUAJUWFUVQOUVICUVRQUVPVUFCUWFUONPVUIUWFCAQGVUJUWDVUKUWEVULUUFYRYOU
      VRSUUBXEUUCUVGOUVKUVSUVGDUVRCUIUVGVUMDUVRPVUNUVQDBUVPIUXBUVQSYRWJXHUUDUUG
      UVGAYSMZBYSMZUVIABUUERMZUVMUVNYAAYTMZVUOUVGTYTMQTUUHNMZVURUUIQTUUJNMZVUSV
      UTVUGLMUUKUULQTUUPYOQTAFUUMYHAUUNYPUVGUYNBUUOMVUPUYPBUUQBUURYQUVGUWQUVFVU
      QUWRUWSUVPUWTABUXAUXBUXCUXDFUUSVNOUVIABCDQVUJGIUUTXEUVAUVB $.
  $}

  ${
    $d d e p q B $.  $d d e p q R $.  $d p V $.  $d d e p q ph $.
    qqhucn.b $e |- B = ( Base ` R ) $.
    qqhucn.q $e |- Q = ( CCfld |`s QQ ) $.
    qqhucn.u $e |- U = ( UnifSt ` Q ) $.
    qqhucn.v $e |- V = ( metUnif ` ( ( dist ` R ) |` ( B X. B ) ) ) $.
    qqhucn.z $e |- Z = ( ZMod ` R ) $.
    qqhucn.1 $e |- ( ph -> R e. NrmRing ) $.
    qqhucn.2 $e |- ( ph -> R e. DivRing ) $.
    qqhucn.3 $e |- ( ph -> Z e. NrmMod ) $.
    qqhucn.4 $e |- ( ph -> ( chr ` R ) = 0 ) $.
    $( The ` QQHom ` homomorphism is uniformly continuous.  (Contributed by
       Thierry Arnoux, 28-Jan-2018.) $)
    qqhucn $p |- ( ph -> ( QQHom ` R ) e. ( U uCn V ) ) $=
      ( cfv cq co wcel vp vq vd ve cqqh cabs cmin ccom cxp cres cmetu wf cv clt
      cucn wbr cds wi wral crp wrex cdr cchr cc0 wceq cdvr czrh eqid syl2anc wa
      qqhf simpr csg cnm cngp cnrg nrgngp syl ad2antrr ffvelcdmda adantr ngpdsr
      syl3anc simplr ccnfld csubg csubrg cress qsubdrg subrgsubg ax-mp cnfldsub
      simpli subgsub mp3an1 fveq2d cghm qqhghm qrngbas ghmsub eqtr2d cnlm elind
      cin qsubcl qqhnm syl31anc 3eqtrd ovresd cc qsscn sselid cnmetdval abssubd
      3eqtr4d 3eqtr4rd breq1d biimpd ralrimiva breq2 imbi1d 2ralbidv rspcev wne
      c0 cz 0z ne0i a1i 4syl cxmet cpsmet cxms cvv qex xmsxmet2 xmetpsmet crest
      cuss 3eqtri mp2b crg cur drngring ringidcl cnfldxms ressxms mp2an eqeltri
      zq cnfldds ressds mp1i ngpxms metucn mpbir2and fveq2i cnflduss oveq1i wss
      ressuss cnxmet restmetu mp3an oveq1d eleqtrrd ) ADUEQZUFUGUHZRRUIZUJZUKQZ
      FUOSZEFUOSAUVGUVLTRBUVGULZUAUMZUBUMZUVJSZUCUMZUNUPZUVNUVGQZUVOUVGQZDUQQZB
      BUIUJZSZUDUMZUNUPZURZUBRUSUARUSZUCUTVAZUDUTUSADVBTZDVCQVDVEZUVMNPBDVFQZDD
      VGQZHUWKVHZUWLVHZVKVIZAUWHUDUTAUWDUTTZVJUWPUVPUWDUNUPZUWEURZUBRUSZUARUSZU
      WHAUWPVLAUWTUWPAUWSUARAUVNRTZVJZUWRUBRUXBUVORTZVJZUWQUWEUXDUVPUWCUWDUNUXD
      UVSUVTUWASZUVOUVNUGSZUFQZUWCUVPUXDUXEUVTUVSDVMQZSZDVNQZQZUXFUVGQZUXJQZUXG
      UXDDVOTZUVSBTZUVTBTUXEUXKVEAUXNUXAUXCADVPTZUXNMDVQZVRVSUXBUXOUXCARBUVNUVG
      UWOVTWAZUXBRBUVOUVGAUVMUXAUWOWAVTZUVSUVTUWADUXHUXJBUXJVHZHUXHVHZUWAVHZWBW
      CUXDUXIUXLUXJUXDUXLUVOUVNCVMQZSZUVGQZUXIUXDUXFUYDUVGUXDUXCUXAUXFUYDVEZUXB
      UXCVLZAUXAUXCWDZRWEWFQTZUXCUXAUYFRWEWGQTZUYIUYJWERWHSZVBTWIWMRWEWJWKRWECU
      GUYCUVOUVNWLIUYCVHZWNWOVIWPUXDUVGCDWQSTZUXCUXAUYEUXIVEAUYMUXAUXCAUWIUWJUY
      MNPBUWKCDUWLHUWMUWNIWRVIVSUYGUYHRCDUVOUVGUYCUXHUVNCIWSZUYLUYAWTWCXAWPUXDD
      VPVBXDTZGXBTZUWJUXFRTZUXMUXGVEAUYOUXAUXCAVPVBDMNXCVSAUYPUXAUXCOVSAUWJUXAU
      XCPVSUXDUXCUXAUYQUYGUYHUVOUVNXEVIUXFDUXJGUXTLXFXGXHUXDUVSUVTUWABUXRUXSXIU
      XDUVNUVOUVHSZUVNUVOUGSUFQZUVPUXGUXDUVNXJTUVOXJTUYRUYSVEUXDRXJUVNXKUYHXLZU
      XDRXJUVOXKUYGXLZUVNUVOUVHUVHVHXMVIUXDUVNUVOUVHRUYHUYGXIUXDUVOUVNVUAUYTXNX
      OXPXQXRXSXSWAUWGUWTUCUWDUTUVQUWDVEZUWFUWRUAUBRRVUBUVRUWQUWEUVQUWDUVPUNXTY
      AYBYCVIXSAUAUBUVJUWBUVKUVGFRBUCUDUVKVHKRYEYDZAVDYFTVDRTVUCYGVDUUJRVDYHUUA
      ZYIAUWIDUUBTDUUCQZBTBYEYDNDUUDBDVUEHVUEVHUUEBVUEYHYJAUVJRYKQTZUVJRYLQTCYM
      TVUFACUYKYMIWEYMTRYNTZUYKYMTUUFYORWEYNUUGUUHUUIUVHCRUYNVUGUVHCUQQVEYORUVH
      WECYNIUUKUULWKYPUUMUVJRYQVRAUWBBYKQTZUWBBYLQTAUXPUXNDYMTVUHMUXQDUUNUWADBH
      UYBYPYJUWBBYQVRUUOUUPAEUVKFUOEUVKVEAEWEYSQZUVIYRSZUVHUKQZUVIYRSZUVKECYSQU
      YKYSQZVUJJCUYKYSIUUQVUGVUMVUJVEYORYNWEUVAWKYTVUIVUKUVIYRVUIVUIVHUURUUSVUC
      UVHXJYLQTZRXJUUTVULUVKVEVUDUVHXJYKQTVUNUVBUVHXJYQWKXKRUVHXJUVCUVDYTYIUVEU
      VF $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Canonical embedding of the real numbers into a complete ordered field
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $c RRHom $.
  $c RRExt $.

  $( Map the real numbers into a complete field. $)
  crrh $a class RRHom $.

  $( Extend class notation with the class of extension fields of ` RR ` . $)
  crrext $a class RRExt $.

  $( Define the canonical homomorphism from the real numbers to any complete
     field, as the extension by continuity of the canonical homomorphism from
     the rational numbers.  (Contributed by Mario Carneiro, 22-Oct-2017.)
     (Revised by Thierry Arnoux, 23-Oct-2017.) $)
  df-rrh $a |- RRHom = ( r e. _V |->
    ( ( ( topGen ` ran (,) ) CnExt ( TopOpen ` r ) ) ` ( QQHom ` r ) ) ) $.

  ${
    $d r J $.  $d r K $.  $d r R $.
    rrhval.1 $e |- J = ( topGen ` ran (,) ) $.
    rrhval.2 $e |- K = ( TopOpen ` R ) $.
    $( Value of the canonical homormorphism from the real numbers to a complete
       space.  (Contributed by Thierry Arnoux, 2-Nov-2017.) $)
    rrhval $p |- ( R e. V
      -> ( RRHom ` R ) = ( ( J CnExt K ) ` ( QQHom ` R ) ) ) $=
      ( vr wcel cvv crrh cfv cqqh ccnext co wceq elex cv cioo ctopn fveq2 fvmpt
      crn ctg eqcomi a1i eqtr4di oveq12d fveq12d df-rrh fvex syl ) ADHAIHAJKALK
      ZBCMNZKZOADPGAGQZLKZRUBUCKZUOSKZMNZKUNIJUOAOZUPULUSUMUTUQBURCMUQBOUTBUQEU
      DUEUTURASKCUOASTFUFUGUOALTUHGUIULUMUJUAUK $.
  $}

  ${
    rrhf.d $e |- D = ( ( dist ` R ) |` ( B X. B ) ) $.
    rrhf.j $e |- J = ( topGen ` ran (,) ) $.
    rrhf.b $e |- B = ( Base ` R ) $.
    rrhf.k $e |- K = ( TopOpen ` R ) $.
    rrhf.z $e |- Z = ( ZMod ` R ) $.
    rrhf.1 $e |- ( ph -> R e. DivRing ) $.
    rrhf.2 $e |- ( ph -> R e. NrmRing ) $.
    rrhf.3 $e |- ( ph -> Z e. NrmMod ) $.
    rrhf.4 $e |- ( ph -> ( chr ` R ) = 0 ) $.
    rrhf.5 $e |- ( ph -> R e. CUnifSp ) $.
    rrhf.6 $e |- ( ph -> ( UnifSt ` R ) = ( metUnif ` D ) ) $.
    $( If the topology of ` R ` is Hausdorff, and ` R ` is a complete uniform
       space, then the canonical homomorphism from the real numbers to ` R ` is
       continuous.  (Contributed by Thierry Arnoux, 17-Jan-2018.) $)
    rrhcn $p |- ( ph -> ( RRHom ` R ) e. ( J Cn K ) ) $=
      ( cfv crefld crrh cqqh ccnext co ccn ctps wcel wceq cxms cnrg cngp nrgngp
      ngpxms 3syl xmstps syl rrhval cq cuss ccnfld cress cr rebase cioo crn ctg
      ctopn retopn eqtri eqid df-refld oveq1i cvv wss reex qssre ressabs eqtr2i
      mp2an fveq2i ccms cms recms cmsms mstps mp2b a1i cusp recusp cuspusp mp1i
      ccusp cmopn cha xmstopn cxmet xmsxmet methaus eqeltrd cmetu cucn cds cres
      cxp qqhucn eqcomd oveq2d eleqtrd ccl fveq1i qdensere ucnextcn ) ADUASZDUB
      SZEFUCUDSZEFUEUDADUFUGZXMXOUHADUIUGZXPADUJUGDUKUGXQNDULDUMUNZDUOUPZDEFUFI
      KUQUPAURTUSSZUTURVAUDZUSSZDUSSZXNEFTDVBBVCJEVDVEVFSZTVGSIVHVIKXTVJYATURVA
      UDZUSYEUTVBVAUDZURVAUDZYATYFURVAVKVLVBVMUGURVBVNZYGYAUHVOVPVBURUTVMVQVSVR
      VTYCVJTUFUGZATWAUGTWBUGYIWCTWDTWEWFWGTWLUGTWHUGAWITWJWKXSQAFCWMSZWNAXQFYJ
      UHXRCFDBKJHWOUPAXQCBWPSUGYJWNUGXRCDBJHWQCYJBYJVJWRUNWSYHAVPWGAXNYBCWTSZXA
      UDYBYCXAUDABYADYBYKGJYAVJYBVJCDXBSBBXDXCWTHVTLNMOPXEAYKYCYBXAAYCYKRXFXGXH
      UREXISZSZVBUHAYMURYDXISZSVBURYLYNEYDXIIVTXJXKVIWGXLWS $.

    $( If the topology of ` R ` is Hausdorff, Cauchy sequences have at most one
       limit, i.e. the canonical homomorphism of ` RR ` into ` R ` is a
       function.  (Contributed by Thierry Arnoux, 2-Nov-2017.) $)
    rrhf $p |- ( ph -> ( RRHom ` R ) : RR --> B ) $=
      ( cr wcel crrh cfv wf cuni cioo crn ctg ccn co eqid uniretop cnf syl cxms
      rrhcn ctps wceq cnrg cngp nrgngp ngpxms 3syl xmstps tpsuni feq3d mpbird )
      ASBDUAUBZUCSFUDZVGUCZAVGUEUFUGUBZFUHUITVIABCDVJFGHVJUJJKLMNOPQRUOVGVJFSVH
      UKVHUJULUMABVHVGSADUNTZDUPTBVHUQADURTDUSTVKNDUTDVAVBDVCBFDJKVDVBVEVF $.
  $}

  $( Define the class of extensions of ` RR ` .  This is a shorthand for
     listing the necessary conditions for a structure to admit a canonical
     embedding of ` RR ` into it.  Interestingly, this is not coming from a
     mathematical reference, but was from the necessary conditions to build the
     embedding at each step ( ` ZZ ` , ` QQ ` and ` RR ` ).  It would be
     interesting see if this is formally treated in the literature.  See
     ~ isrrext for a better readable version.  (Contributed by Thierry Arnoux,
     2-May-2018.) $)
  df-rrext $a |- RRExt = { r e. ( NrmRing i^i DivRing ) |
     ( ( ( ZMod ` r ) e. NrmMod /\ ( chr ` r ) = 0 ) /\ ( r e. CUnifSp
     /\ ( UnifSt ` r ) = ( metUnif ` ( ( dist ` r )
     |` ( ( Base ` r ) X. ( Base ` r ) ) ) ) ) ) } $.

  ${
    $d r D $.  $d r R $.  $d r Z $.
    isrrext.b $e |- B = ( Base ` R ) $.
    isrrext.v $e |- D = ( ( dist ` R ) |` ( B X. B ) ) $.
    isrrext.z $e |- Z = ( ZMod ` R ) $.
    $( Express the property " ` R ` is an extension of ` RR ` ".  (Contributed
       by Thierry Arnoux, 2-May-2018.) $)
    isrrext $p |- ( R e. RRExt <-> ( ( R e. NrmRing /\ R e. DivRing ) /\
      ( Z e. NrmMod /\ ( chr ` R ) = 0 ) /\ ( R e. CUnifSp
      /\ ( UnifSt ` R ) = ( metUnif ` D ) ) ) ) $=
      ( vr cnrg cdr wcel cnlm cchr cfv cc0 wceq wa ccusp cuss fveq2 crrext elin
      cin cmetu w3a anbi1i czlm cds cbs cxp cres eleq1d bitr4di fveqeq2 anbi12d
      cv eleq1i eqtr4di sqxpeqd reseq12d fveq2d eqeq12d df-rrext elrab2 3bitr4i
      eleq1 3anass ) CIJUCZKZDLKZCMNOPZQZCRKZCSNZBUDNZPZQZQZQCIKCJKQZVRQCUAKVSV
      LVQUEVIVSVRCIJUBUFHUPZUGNZLKZVTMNOPZQZVTRKZVTSNZVTUHNZVTUINZWHUJZUKZUDNZP
      ZQZQVRHCVHUAVTCPZWDVLWMVQWNWBVJWCVKWNWBCUGNZLKVJWNWAWOLVTCUGTULDWOLGUQUMV
      TCOMUNUOWNWEVMWLVPVTCRVFWNWFVNWKVOVTCSTWNWJBUDWNWJCUHNZAAUJZUKBWNWGWPWIWQ
      VTCUHTWNWHAWNWHCUINAVTCUITEURUSUTFURVAVBUOUOHVCVDVSVLVQVGVE $.
  $}

  $( An extension of ` RR ` is a normed ring.  (Contributed by Thierry Arnoux,
     2-May-2018.) $)
  rrextnrg $p |- ( R e. RRExt -> R e. NrmRing ) $=
    ( crrext wcel cnrg cdr wa czlm cfv cnlm cchr cc0 wceq cuss cds cbs cxp cres
    ccusp cmetu eqid isrrext simp1bi simpld ) ABCZADCZAECZUDUEUFFAGHZICAJHKLFAR
    CAMHANHAOHZUHPQZSHLFUHUIAUGUHTUITUGTUAUBUC $.

  $( An extension of ` RR ` is a division ring.  (Contributed by Thierry
     Arnoux, 2-May-2018.) $)
  rrextdrg $p |- ( R e. RRExt -> R e. DivRing ) $=
    ( crrext wcel cnrg cdr wa czlm cfv cnlm cchr cc0 wceq cuss cds cbs cxp cres
    ccusp cmetu eqid isrrext simp1bi simprd ) ABCZADCZAECZUDUEUFFAGHZICAJHKLFAR
    CAMHANHAOHZUHPQZSHLFUHUIAUGUHTUITUGTUAUBUC $.

  ${
    rrextnlm.z $e |- Z = ( ZMod ` R ) $.
    $( The norm of an extension of ` RR ` is absolutely homogeneous.
       (Contributed by Thierry Arnoux, 2-May-2018.) $)
    rrextnlm $p |- ( R e. RRExt -> Z e. NrmMod ) $=
      ( crrext wcel cnlm cchr cfv cc0 wceq cnrg cdr ccusp cuss cds cbs cxp cres
      wa eqid cmetu isrrext simp2bi simpld ) ADEZBFEZAGHIJZUEAKEALESUFUGSAMEANH
      AOHAPHZUHQRZUAHJSUHUIABUHTUITCUBUCUD $.
  $}

  $( The ring characteristic of an extension of ` RR ` is zero.  (Contributed
     by Thierry Arnoux, 2-May-2018.) $)
  rrextchr $p |- ( R e. RRExt -> ( chr ` R ) = 0 ) $=
    ( crrext wcel czlm cfv cnlm cchr cc0 wceq cnrg cdr wa cuss cds cbs cxp cres
    ccusp cmetu eqid isrrext simp2bi simprd ) ABCZADEZFCZAGEHIZUDAJCAKCLUFUGLAR
    CAMEANEAOEZUHPQZSEILUHUIAUEUHTUITUETUAUBUC $.

  $( An extension of ` RR ` is a complete uniform space.  (Contributed by
     Thierry Arnoux, 2-May-2018.) $)
  rrextcusp $p |- ( R e. RRExt -> R e. CUnifSp ) $=
    ( crrext wcel ccusp cuss cfv cds cbs cxp cres cmetu wceq cnrg cdr czlm cnlm
    wa cchr cc0 eqid isrrext simp3bi simpld ) ABCZADCZAEFAGFAHFZUFIJZKFLZUDAMCA
    NCQAOFZPCARFSLQUEUHQUFUGAUIUFTUGTUITUAUBUC $.

  $( An extension of ` RR ` is a topological space.  (Contributed by Thierry
     Arnoux, 7-Sep-2018.) $)
  rrexttps $p |- ( R e. RRExt -> R e. TopSp ) $=
    ( crrext wcel cnrg cngp cxms ctps rrextnrg nrgngp ngpxms xmstps 4syl ) ABCA
    DCAECAFCAGCAHAIAJAKL $.

  ${
    rrexthaus.1 $e |- K = ( TopOpen ` R ) $.
    $( The topology of an extension of ` RR ` is Hausdorff.  (Contributed by
       Thierry Arnoux, 7-Sep-2018.) $)
    rrexthaus $p |- ( R e. RRExt -> K e. Haus ) $=
      ( crrext wcel cds cfv cbs cxp cres cmopn cha cxms wceq cnrg cngp rrextnrg
      nrgngp 3syl eqid ngpxms xmstopn syl cxmet xmsxmet methaus eqeltrd ) ADEZB
      AFGAHGZUIIJZKGZLUHAMEZBUKNUHAOEAPEULAQARAUASZUJBAUICUITZUJTZUBUCUHULUJUIU
      DGEUKLEUMUJAUIUNUOUEUJUKUIUKTUFSUG $.
  $}

  ${
    rrextust.b $e |- B = ( Base ` R ) $.
    rrextust.d $e |- D = ( ( dist ` R ) |` ( B X. B ) ) $.
    $( The uniformity of an extension of ` RR ` is the uniformity generated by
       its distance.  (Contributed by Thierry Arnoux, 2-May-2018.) $)
    rrextust $p |- ( R e. RRExt -> ( UnifSt ` R ) = ( metUnif ` D ) ) $=
      ( crrext wcel ccusp cuss cfv cmetu wceq cnrg cdr czlm cnlm cchr cc0 eqid
      wa isrrext simp3bi simprd ) CFGZCHGZCIJBKJLZUDCMGCNGTCOJZPGCQJRLTUEUFTABC
      UGDEUGSUAUBUC $.
  $}

  $( The field of the real numbers is an extension of the real numbers.
     (Contributed by Thierry Arnoux, 2-May-2018.) $)
  rerrext $p |- RRfld e. RRExt $=
    ( crefld crrext wcel cnrg cdr wa czlm cfv cnlm cchr cc0 wceq ccusp cuss cds
    cr ccnfld resubdrg pm3.2i eqid cxp cmetu csubrg cnnrg simpli df-refld mp2an
    cres subrgnrg simpri cofld reofld ofldchr ax-mp recusp reust rebase isrrext
    rezh mpbir3an ) ABCADCZAECZFAGHZICZAJHKLZFAMCZANHAOHPPUAUHZUBHLZFVAVBQDCPQU
    CHCZVAUDVIVBRUEPQAUFUIUGVIVBRUJSVDVEUSAUKCVEULAUMUNSVFVHUOUPSPVGAVCUQVGTVCT
    URUT $.

  $( The field of the complex numbers is an extension of the real numbers.
     (Contributed by Thierry Arnoux, 2-May-2018.) $)
  cnrrext $p |- CCfld e. RRExt $=
    ( ccnfld crrext wcel cnrg cdr wa czlm cfv cnlm cchr cc0 ccusp pm3.2i crefld
    wceq cr ax-mp eqid cc cres cuss cabs cmin cmetu cnnrg cndrng cress df-refld
    ccom cnzh co fveq2i reofld ofldchr csubrg resubdrg simpli subrgchr 3eqtr3ri
    cofld cnfldcusp cnflduss cnfldbas cxp cds wfn cmet wf metf ffn mp2b fnresdm
    cnmet cnfldds reseq1i eqtr3i isrrext mpbir3an ) ABCADCZAECZFAGHZICZAJHZKOZF
    ALCZAUAHZUBUCUIZUDHOZFVSVTUEUFMWBWDUJNJHZAPUGUKZJHZKWCNWJJUHULNUTCWIKOUMNUN
    QPAUOHCZWKWCOWLNECUPUQPAURQUSMWEWHVAWFWFRVBMSWGAWAVCWGSSVDZTZWGAVEHZWMTWGWM
    VFZWNWGOWGSVGHCWMPWGVHWPVMWGSVIWMPWGVJVKWMWGVLQWGWOWMVNVOVPWARVQVR $.

  $( The topology of the field of the rational numbers.  (Contributed by
     Thierry Arnoux, 29-Aug-2020.) $)
  qqtopn $p |- ( ( TopOpen ` RRfld ) |`t QQ ) = ( TopOpen ` ( CCfld |`s QQ ) )
    $=
    ( cioo crn ctg cq crest co crefld ctopn ccnfld cress retopn oveq1i df-refld
    cfv cr cvv wcel wss wceq reex qssre ressabs mp2an eqtr2i resstopn eqtr3i )
    ABCNZDEFGHNZDEFIDJFZHNUGUHDEKLDUIUGGGDJFIOJFZDJFZUIGUJDJMLOPQDORUKUISTUAODI
    PUBUCUDKUEUF $.

  ${
    rrhfe.b $e |- B = ( Base ` R ) $.
    $( If ` R ` is an extension of ` RR ` , then the canonical homomorphism of
       ` RR ` into ` R ` is a function.  (Contributed by Thierry Arnoux,
       2-May-2018.) $)
    rrhfe $p |- ( R e. RRExt -> ( RRHom ` R ) : RR --> B ) $=
      ( crrext wcel cds cfv cxp cres cioo crn ctopn czlm eqid rrextdrg rrextnrg
      ctg rrextnlm rrextchr rrextcusp rrextust rrhf ) BDEABFGAAHIZBJKQGZBLGZBMG
      ZUCNZUDNCUENUFNZBOBPBUFUHRBSBTAUCBCUGUAUB $.
  $}

  ${
    rrhcne.j $e |- J = ( topGen ` ran (,) ) $.
    rrhcne.k $e |- K = ( TopOpen ` R ) $.
    $( If ` R ` is an extension of ` RR ` , then the canonical homomorphism of
       ` RR ` into ` R ` is continuous.  (Contributed by Thierry Arnoux,
       2-May-2018.) $)
    rrhcne $p |- ( R e. RRExt -> ( RRHom ` R ) e. ( J Cn K ) ) $=
      ( wcel cbs cfv cds cxp cres czlm eqid rrextdrg rrextnrg rrextnlm rrextchr
      crrext rrextcusp rrextust rrhcn ) ARFAGHZAIHUBUBJKZABCALHZUCMZDUBMZEUDMZA
      NAOAUDUGPAQASUBUCAUFUETUA $.
  $}

  ${
    rrhfvale.j $e |- J = ( topGen ` ran (,) ) $.
    rrhfvale.k $e |- K = ( TopOpen ` R ) $.
$(
    @( Necessary condition for the ` RRHom ` homomorphism to have values.
       @)
    rrhlim @p |- ( ( R e. RRExt /\ X e. RR ) -> ( ( K fLimf
      ( ( ( nei ` J ) ` { X } ) |`t QQ ) ) ` ( QQHom ` R ) ) =/= (/) ) @=
      ? @.
    @d A x @.  @d J x @.  @d K x @.  @d R x @.
    rrhfvale.h @e |- H = ( RRHom ` R ) @.
    @( Value of the canonical embedding of ` RR ` into ` R ` at a given point
       ` A ` .  (Contributed by Thierry Arnoux, 8-Sep-2018.) @)
    rrhfvale @p |- ( ( R e. RRExt /\ A e. RR ) -> ( H ` A ) =
     U. ( ( K fLimf ( ( ( nei ` J ) ` { A } ) |`t QQ ) ) ` ( QQHom ` R ) ) ) @=
      ( vx crrext wcel cr cfv co cq cuni wceq eqid a1i ccl cqqh ccnext csn cnei
      wa crest cflf crrh rrhval adantr eqtrid fveq1d cioo crn ctg unieqi eqtr4i
      uniretop ctop retop eqeltri rrexthaus cbs cdr cchr rrextdrg rrextchr cdvr
      wf czrh qqhf syl2anc ctps wb rrexttps tpsuni feq3 3syl mpbid qssre fveq2i
      cc0 wss fveq1i qdensere eqtri cv rrhlim cnextfvval eqtrd ) BJKZALKZUEZACM
      ABUAMZDEUBNMZMWNEAUCDUDMMOUFNUGNMPWMACWOWMCBUHMZWOHWKWPWOQWLBDEJFGUIUJUKU
      LWKIOEPZLWNDEALUMUNUOMZPDPURDWRFUPUQWQRDUSKWKDWRUSFUTVASBEGVBWKOBVCMZWNVI
      ZOWQWNVIZWKBVDKBVEMWBQWTBVFBVGWSBVHMZBBVJMZWSRZXBRXCRVKVLWKBVMKWSWQQWTXAV
      NBVOWSEBXDGVPWSWQOWNVQVRVSOLWCWKVTSODTMZMZLQWKXFOWRTMZMLOXEXGDWRTFWAWDWEW
      FSBDEIWGFGWHWIWJ @.
$)
  $}

  $( The ` RRHom ` homomorphism leaves rational numbers unchanged.
     (Contributed by Thierry Arnoux, 27-Mar-2018.) $)
  rrhqima $p |- ( ( R e. RRExt /\ Q e. QQ ) ->
    ( ( RRHom ` R ) ` Q ) = ( ( QQHom ` R ) ` Q ) ) $=
    ( crrext wcel cq wa crrh cfv ctopn co wceq eqid adantr cr a1i crest ccn cdr
    cnrg oveq1i cqqh cioo crn ctg ccnext rrhval fveq1d cuni uniretop ctop retop
    cha rrexthaus wss qssre crefld cin czlm cnlm cc0 rrextnrg rrextdrg rrextnlm
    cchr elind rrextchr ccnfld cress qqtopn qqhcn syl3anc retopn eleqtrdi simpr
    eqcomi cnextfres eqtrd ) BCDZAEDZFZABGHZHZABUAHZUBUCUDHZBIHZUEJHZHZAWCHVRWB
    WGKVSVRAWAWFBWDWECWDLWELZUFUGMVTEWEUHZNWCWDWEAUIWILWDUJDVTUKOVRWEULDVSBWEWH
    UMMENUNVTUOOVRWCWDEPJZWEQJZDVSVRWCUPIHZEPJZWEQJZWKVRBSRUQDBURHZUSDBVDHUTKWC
    WNDVRSRBBVABVBVEBWOWOLZVCBVFVGEVHJZBWMWEWOWQLVIWPWHVJVKWMWJWEQWLWDEPWDWLVLV
    OTTVMMVRVSVNVPVQ $.

$(
  @( The canonical homomorphism from the real numbers to any complete field is
     a monoid homomorphism. @)
  rrhmhm @p |- ( R e. RRExt
    -> ( RRHom ` R ) e. ( ( CCfld |`s RR ) MndHom R ) ) @=
    ? @.
$)

  $( The image of ` 0 ` by the ` RRHom ` homomorphism is the ring's zero.
     (Contributed by Thierry Arnoux, 22-Oct-2017.) $)
  rrh0 $p |- ( R e. RRExt -> ( ( RRHom ` R ) ` 0 ) = ( 0g ` R ) ) $=
    ( crrext wcel cc0 crrh cfv cqqh c0g cq wceq cz zssq 0z sselii simpl rrhqima
    wa simpr syl2anc eqid mpan2 cdr cchr rrextdrg rrextchr cdvr czrh qqh0 eqtrd
    cbs ) ABCZDAEFFZDAGFFZAHFZUKDICZULUMJZKIDLMNUKUOQUKUOUPUKUOOUKUORDAPSUAUKAU
    BCAUCFDJUMUNJAUDAUEAUJFZAUFFZAAUGFZUQTURTUSTUHSUI $.

$(
      rrhrhm.3 @e |- ( ph -> R e. CUnifSp ) @.
      rrhrhm.1 @e |- W = ( CCfld |`s RR ) @.
      @( The ` RRHom ` homomorphism is a ring homomorphism if the target
         structure is a complete field.  @)
      rrhrhm @p |- ( ph -> ( RRHom ` R ) e. ( W RingHom R ) ) @=
        ? @.
$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Embedding from the extended real numbers into a complete lattice
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $c RR*Hom $.

  $( Map the extended real numbers into a complete lattice. $)
  cxrh $a class RR*Hom $.

  ${
    $d r x $.
    $( Define an embedding from the extended real number into a complete
       lattice.  (Contributed by Thierry Arnoux, 19-Feb-2018.) $)
    df-xrh $a |- RR*Hom = ( r e. _V |->
      ( x e. RR* |-> if ( x e. RR , ( ( RRHom ` r ) ` x ) ,
        if ( x = +oo , ( ( lub ` r ) ` ( ( RRHom ` r ) " RR ) ) ,
                       ( ( glb ` r ) ` ( ( RRHom ` r ) " RR ) ) ) ) ) ) $.
  $}

  ${
    $d r x R $.  $d r B $.  $d r L $.  $d r U $.
    xrhval.b $e |- B = ( ( RRHom ` R ) " RR ) $.
    xrhval.l $e |- L = ( glb ` R ) $.
    xrhval.u $e |- U = ( lub ` R ) $.
    $( The value of the embedding from the extended real numbers into a
       complete lattice.  (Contributed by Thierry Arnoux, 19-Feb-2018.) $)
    xrhval $p |- ( R e. V -> ( RR*Hom ` R ) = ( x e. RR* |->
      if ( x e. RR , ( ( RRHom ` R ) ` x ) ,
         if ( x = +oo , ( U ` B ) , ( L ` B ) ) ) ) ) $=
      ( vr wcel cfv cxr cr crrh wceq cif club cglb fveq2 cxrh cv cpnf cmpt elex
      cvv cima fveq1d eqtr4di imaeq1d fveq12d ifeq12d mpteq2dv xrex mptex fvmpt
      df-xrh syl ) CFKCUFKCUALAMAUBZNKZUSCOLZLZUSUCPZBDLZBELZQZQZUDZPCFUEJCAMUT
      USJUBZOLZLZVCVJNUGZVIRLZLZVLVISLZLZQZQZUDVHUFUAVICPZAMVRVGVSUTVKVBVQVFVSU
      SVJVAVICOTZUHVSVCVNVDVPVEVSVLBVMDVSVMCRLDVICRTIUIVSVLVANUGBVSVJVANVTUJGUI
      ZUKVSVLBVOEVSVOCSLEVICSTHUIWAUKULULUMAJUQAMVGUNUOUPUR $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Canonical embeddings into the ordered field of the real numbers
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( The ` ZRHom ` homomorphism for the real number structure is the identity.
     (Contributed by Thierry Arnoux, 31-Oct-2017.) $)
  zrhre $p |- ( ZRHom ` RRfld ) = ( _I |` ZZ ) $=
    ( vn cz cv c1 crefld cmg cfv co cmpt czrh cid cres wcel cmul cr wceq remulg
    1re mpan2 eqid zre ax-1rid syl eqtrd mpteq2ia ccnfld csubrg resubdrg simpri
    cdr crg drngring re1r zrhval2 mp2b mptresid 3eqtr4i ) ABACZDEFGZHZIZABURIEJ
    GZKBLABUTURURBMZUTURDNHZURVCDOMUTVDPRDURQSVCUROMVDURPURUAURUBUCUDUEEUJMZEUK
    MVBVAPOUFUGGMVEUHUIEULEUSDAVBVBTUSTUMUNUOABUPUQ $.

  $( The ` QQHom ` homomorphism for the real number structure is the identity.
     (Contributed by Thierry Arnoux, 31-Oct-2017.) $)
  qqhre $p |- ( QQHom ` RRfld ) = ( _I |` QQ ) $=
    ( vq cq crefld cfv cmpt cid cres wcel co cdiv cc0 wceq cr cz ax-mp wb zrhre
    wf1 rebase mp2b cv cqqh cnumer czrh cdenom cdvr cchr ccnfld csubrg resubdrg
    cdr crg drngring wss wf1o f1oi f1of1 zssre f1ss mp2an f1eq1 mpbir eqid re0g
    simpri zrhchr mpbiri qqhvval mpanl12 wne wf f1f a1i qnumcl ffvelcdmd qdencl
    nnzd wa anim1i ccnv csn cima zrhf1ker mpbi eleq2i wfn ffn fniniseg 3bitr3ri
    fvex elsn sylibr nnne0d adantr neneqd pm2.65da neqned syl3anc fveq1i fvresi
    redvr eqtrid oveq12d qeqnumdivden eqtr4d 3eqtrd mpteq2ia wtru feqmptd mptru
    syl qqhf mptresid 3eqtr4i ) ABAUAZCUBDZDZEZABXOEXPFBGABXQXOXOBHZXQXOUCDZCUD
    DZDZXOUEDZYADZCUFDZIZYBYDJIZXOCUKHZCUGDKLZXSXQYFLMUHUIDHYHUJVEZYHCULHZYIYJC
    UMZYKYINMYARZYMNMFNGZRZNNYNRZNMUNYONNYNUOYPNUPNNYNUQOURNNMYNUSUTYAYNLYMYOPQ
    NMYAYNVAOVBZMCYAKSYAVCZVDVFVGTZMYEXOCYASYEVCZYRVHVIXSYBMHYDMHYDKVJYFYGLXSNM
    XTYANMYAVKZXSYMUUAYQNMYAVLOZVMZXOVNZVOXSNMYCYAUUCXSYCXOVPZVQZVOXSYDKXSYDKLZ
    YCKLZXSUUGVRZYCNHZUUGVRZUUHXSUUJUUGUUFVSYCYAVTKWAZWBZHZYCUULHUUKUUHUUMUULYC
    YMUUMUULLZYQYHYKYMUUOPYJYLMCYAKSYRVDWCTWDWEUUAYANWFUUNUUKPUUBNMYAWGNKYCYAWH
    TYCKXOUEWJWKWIWLUUIYCKXSYCKVJUUGXSYCUUEWMWNWOWPWQYBYDXAWRXSYGXTYCJIXOXSYBXT
    YDYCJXSXTNHZYBXTLUUDUUPYBXTYNDXTXTYAYNQWSNXTWTXBXKXSUUJYDYCLUUFUUJYDYCYNDYC
    YCYAYNQWSNYCWTXBXKXCXOXDXEXFXGXPXRLXHABMXPBMXPVKZXHYHYIUUQYJYSMYECYASYTYRXL
    UTVMXIXJABXMXN $.

  ${
    $d a b x $.
    $( The ` RRHom ` homomorphism for the real numbers structure is the
       identity.  (Contributed by Thierry Arnoux, 22-Oct-2017.) $)
    rrhre $p |- ( RRHom ` RRfld ) = ( _I |` RR ) $=
      ( va vb crefld cfv cid cr cres wceq wtru cq uniretop wcel co retopn retop
      a1i ax-mp wss qssre cvv vx crrh cioo crn ctg cha rehaus crrext ccn rrhcne
      rerrext eqid mp1i ctopon ctop toptopon mpbi idcn ccnext wf wf1o f1oi f1of
      fss mp2an ccl qdensere cv csn cnei crest cflf c0 wne cima wrex wi wral wa
      cin simplr simpr opnneip syl3anc fvex qex elrestr mp3an12 syl inss2 inss1
      resiima eqsstri imaeq2 sseq1d rspcev syl2anc ex ralrimiva ancli wb eleq2i
      cfil biimpri trnei mpbid isflf mp3an13 mpbird ne0d adantl creg cusp ccusp
      recusp cuspusp uspreg resabs1 cnrest eqeltrri cnextfres1 mptru cqqh recms
      ccms elexi rrhval qqhre fveq2i eqtri reseq1i 3eqtr4i hauseqcn ) CUBDZEFGZ
      HIJYNYOUCUDUEDZYPFKYPUFLZIUGPZCUHLYNYPYPUIMZLIUKCYPYPYPULZNUJUMYOYSLZIYPF
      UNDLZUUAYPUOLZUUBOYPFKUPUQZYPFURQZPYNJGZYOJGZHIEJGZYPYPUSMZDZJGZUUHUUFUUG
      UUKUUHHIUAJFFUUHYPYPKKUUCIOPYRJFUUHUTZIJJUUHUTZJFRZUULJJUUHVAUUMJVBJJUUHV
      CQSJJFUUHVDVEZPUUNISPZJYPVFDDZFHIVGPZUAVHZFLZUUHYPUUSVIZYPVJDZDZJVKMZVLMD
      ZVMVNIUUTUVEUUSUUTUUSUVELZUUTUUSAVHZLZUUHBVHZVOZUVGRZBUVDVPZVQZAYPVRZVSZU
      UTUVNUUTUVMAYPUUTUVGYPLZVSZUVHUVLUVQUVHVSZUVGJVTZUVDLZUUHUVSVOZUVGRZUVLUV
      RUVGUVCLZUVTUVRUUCUVPUVHUWCUUCUVROPUUTUVPUVHWAUVQUVHWBUUSYPUVGWCWDUVCTLJT
      LUWCUVTUVAUVBWEWFUVGJUVCTTWGWHWIUWBUVRUWAUVSUVGUVSJRUWAUVSHUVGJWJJUVSWLQU
      VGJWKWMPUVKUWBBUVSUVDUVIUVSHUVJUWAUVGUVIUVSUUHWNWOWPWQWRWSWTUUTUVDJXCDLZU
      VFUVOXAZUUTUUSUUQLZUWDUWFUUTUUQFUUSVGXBXDUUBUUNUUTUWFUWDXAUUDSJUUSYPFXEWH
      XFUUBUWDUULUWEUUDUUOUUSAUUHYPUVDFJBXGXHWIXIXJXKYPXLLZICXMLZYQUWGCXNLUWHXO
      CXPQUGYPCNXQVEPUUHYPJVKMYPUIMZLIUUGUUHUWIUUNUUGUUHHSEJFXRQZUUAUUNUUGUWILU
      UESJYOYPYPFKXSVEXTPYAYBYNUUJJYNCYCDZUUIDZUUJCTLYNUWLHCYEYDYFCYPYPTYTNYGQU
      WKUUHUUIYHYIYJYKUWJYLPUUPUURYMYB $.
  $}

