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

  ${
    zzsnm.1 $e |- Z = ( CCfld |`s ZZ ) $.
    $( The norm of the ring of the integers (Contributed by Thierry Arnoux,
       8-Nov-2017.) $)
    zzsnm $p |- ( M e. ZZ -> ( abs ` M ) = ( ( norm ` Z ) ` M ) ) $=
      ( cz wcel cnm cfv cabs cres ccnfld cmnd cc0 cc wss crg cnrng rngmnd ax-mp
      wceq 0z zsscn cnfldbas cnfld0 cnfldnm ressnm mp3an fveq1i fvres syl5reqr
      ) ADEABFGZGAHDIZGAHGAUKUJJKEZLDEDMNUKUJSJOEULPJQRTUADMJBHLCUBUCUDUEUFUGAD
      HUHUI $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
             The complete ordered field of the real numbers
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    recms.1 $e |- R = ( CCfld |`s RR ) $.
    $( The real numbers form a complete metric space.  (Contributed by Thierry
       Arnoux, 1-Nov-2017.) $)
    recms $p |- R e. CMetSp $=
      ( ccms wcel cr ccnfld ctopn cfv ccld eqid recld2 cc wss wb cncms cnfldbas
      ax-resscn cmsss mp2an mpbir ) ACDZEFGHZIHDZUBUBJZKFCDELMUAUCNOQEUBAFLBPUD
      RST $.

    $( The Uniform structure of the real numbers.  (Contributed by Thierry
       Arnoux, 14-Feb-2018.) $)
    reust $p |- ( UnifSt ` R )
                  = ( metUnif ` ( ( dist ` R ) |` ( RR X. RR ) ) ) $=
      ( cuss cfv cabs cmetu cr crest co cres ccnfld fveq2i wcel wceq reex ax-mp
      cvv 3eqtri cc cc0 cmin ccom cxp cds cress ressuss eqid cnflduss oveq1i c0
      wne cpsmet wss 0re ne0i cnxmet xmetpsmet ax-resscn restmetu mp3an cnfldds
      cxmt ressds reseq1i ) ACDZEUAUBZFDZGGUCZHIZVFVHJZFDZAUDDZVHJZFDVEKGUEIZCD
      ZKCDZVHHIZVIAVNCBLGQMZVOVQNOGQKUFPVPVGVHHVPVPUGUHUIRGUJUKZVFSULDMZGSUMVIV
      KNTGMVSUNGTUOPVFSVBDMVTUPVFSUQPURGVFSUSUTVJVMFVFVLVHVRVFVLNOGVFKAQBVAVCPV
      DLR $.

    $( The real numbers form a complete uniform space.  (Contributed by Thierry
       Arnoux, 17-Dec-2017.) $)
    recusp $p |- R e. CUnifSp $=
      ( cr c0 wne ccms wcel cuss cfv cds cxp cres cmetu wceq ccusp cc0 0re ne0i
      ax-mp eqid recms reust rebase cmetcusp1 mp3an ) CDEZAFGAHIZAJICCKLZMINAOG
      PCGUFQCPRSABUAABUBUHUGACABUCUHTUGTUDUE $.
  $}

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
        wa oveqd grpidpropd trud eqtri ) CAHIZBHIZEUEUFJKFGALIZABUGUGJKUGMZNUGB
        LIJKUGABDUHONKFPZUGQGPZUGQTTZARIZBRIZUIUJULUMJUKULABDULMSNUAUBUCUD $.
    $}

    ${
      $d x y G $.  $d x y W $.
      zlm1.1 $e |- .1. = ( 1r ` G ) $.
      $( Unit of a ` ZZ ` -module (if present).  (Contributed by Thierry
         Arnoux, 8-Nov-2017.) $)
      zlm1 $p |- .1. = ( 1r ` W ) $=
        ( vx vy cur cfv wceq wtru cbs eqid a1i zlmbas cv wcel wa cmulr zlmmulr
        oveqd rngidpropd trud eqtri ) ABHIZCHIZEUEUFJKFGBLIZBCUGUGJKUGMZNUGCLIJ
        KUGBCDUHONKFPZUGQGPZUGQRRZBSIZCSIZUIUJULUMJUKULBCDULMTNUAUBUCUD $.
    $}

    ${
      zlmds.1 $e |- D = ( dist ` G ) $.
      $( Distance in a ` ZZ ` -module (if present).  (Contributed by Thierry
         Arnoux, 8-Nov-2017.) $)
      zlmds $p |- ( G e. V -> D = ( dist ` W ) ) $=
        ( cds cfv cnx co cop csts eqid dsid wne c1 c2 c5 1nn c6 wcel csca cress
        ccnfld cz cvsca cmg zlmval fveq2d cdc 5re 2nn0 5nn0 5lt10 declti gtneii
        dsndx scandx neeq12i mpbir setsnid 6re 6nn0 6lt10 vscandx eqtri syl6eqr
        syl6reqr ) BCUAZDGHZBGHZAVIVJBIUBHZUDUEUCJZKLJZIUFHZBUGHZKLJZGHZVKVIDVQ
        GVPBCDVMEVMMVPMUHUIVKVNGHVRVMVLGBNIGHZVLOPQUJZRORVTUKPQRSULUMUNUOUPVSVT
        VLRUQURUSUTVAVPVOGVNNVSVOOVTTOTVTVBPQTSULVCVDUOUPVSVTVOTUQVEUSUTVAVFVGF
        VH $.
    $}

    ${
      zlmtset.1 $e |- J = ( TopSet ` G ) $.
      $( Topology in a ` ZZ ` -module (if present).  (Contributed by Thierry
         Arnoux, 8-Nov-2017.) $)
      zlmtset $p |- ( G e. V -> J = ( TopSet ` W ) ) $=
        ( cts cfv cnx co cop csts eqid tsetid wne c9 c5 gtneii tsetndx c6 cress
        wcel csca ccnfld cz cvsca cmg zlmval fveq2d 5lt9 scandx neeq12i setsnid
        5re mpbir 6re 6lt9 vscandx 3eqtri syl6reqr ) ACUBZDGHAIUCHZUDUEUAJZKLJZ
        IUFHZAUGHZKLJZGHZBVADVGGVFACDVCEVCMVFMUHUIBAGHVDGHVHFVCVBGANIGHZVBOPQOQ
        PUNUJRVIPVBQSUKULUOUMVFVEGVDNVIVEOPTOTPUPUQRVIPVETSURULUOUMUSUT $.
    $}

    ${
      zlmnm.1 $e |- N = ( norm ` G ) $.
      $( Norm of a ` ZZ ` -module (if present).  (Contributed by Thierry
         Arnoux, 8-Nov-2017.) $)
      zlmnm $p |- ( G e. V -> N = ( norm ` W ) ) $=
        ( wcel cnm cfv cbs wceq zlmbas a1i cplusg zlmplusg zlmds nmpropd syl5eq
        eqid cds ) ACGZBAHIDHIFUAADAJIZDJIKUAUBADEUBSLMANIZDNIKUAUCADEUCSOMATIZ
        ACDEUDSPQR $.
    $}

    ${
      $d x y G $.  $d x y W $.
      $( The ` ZZ ` -module built from a normed ring is also a normed ring.
         (Contributed by Thierry Arnoux, 8-Nov-2017.) $)
      zhmnrg $p |- ( G e. NrmRing -> W e. NrmRing ) $=
        ( vx vy cnrg wcel cngp cnm cfv cabv cgrp cmt csg ccom cds wceq eqid a1i
        wa wss w3a cbs zlmbas cplusg zlmplusg proplem3 grppropd cxp reseq1d cts
        zlmds zlmtset topnpropd mspropd zlmnm grpsubpropd coeq12d sseq12d isngp
        cv 3anbi123d 3bitr4g cmulr zlmmulr abvpropd2 eleq12d anbi12d isnrg ibi
        ) AFGZBFGZVKAHGZAIJZAKJZGZTBHGZBIJZBKJZGZTVKVLVKVMVQVPVTVKALGZAMGZVNANJ
        ZOZAPJZUAZUBBLGZBMGZVRBNJZOZBPJZUAZUBVMVQVKWAWGWBWHWFWLVKDEAUCJZABWMWMQ
        VKWMRZSZWMBUCJQVKWMABCWNUDSZVKDVAWMGEVAWMGTDEAUEJZBUEJZWQWRQVKWQABCWQRU
        FSZUGUHVKWMABWOWPVKWEWKWMWMUIWEAFBCWERZULZUJVKABWPAAUKJZFBCXBRUMUNUOVKW
        DWJWEWKVKVNVRWCWIAVNFBCVNRZUPZVKABWPWSUQURXAUSVBWEAWCVNXCWCRWTUTWKBWIVR
        VRRZWIRWKRUTVCVKVNVRVOVSXDVKABWPWSAVDJZBVDJQVKXFABCXFRVESVFVGVHVOAVNXCV
        ORVIVSBVRXEVSRVIVCVJ $.
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
        ( wcel cz co cnm cfv cmul cbs wceq eqid cnlm w3a csca cabs simp2 ccnfld
        cress zzsbase cabel clmod nlmlmod zlmlmod sylibr 3ad2ant1 zlmsca fveq2d
        syl5eq eleqtrd zlmbas zlmvsca nmvs syld3an2 zlmnm fveq1d zzsnm 3ad2ant2
        syl eqtrd oveq12d 3eqtr4d ) GUALZDMLZFALZUBZDFCNZGOPZPZDGUCPZOPZPZFVPPZ
        QNZVOEPDUDPZFEPZQNVKDVRRPZLVLVMVQWBSVNDMWEVKVLVMUEVNMUFMUGNZRPWEWFWFTZU
        HVNWFVRRVNBUILZWFVRSVKVLWHVMVKGUJLWHGUKBGJULUMUNZBUIGWFJWGUOVGZUPUQURVS
        CVRWEVPAGDFABGJHUSVPTCBGJKUTVRTWETVSTVAVBVNVOEVPVNWHEVPSWIBEUIGJIVCVGZV
        DVNWCVTWDWAQVNWCDWFOPZPZVTVLVKWCWMSVMDWFWGVEVFVNDWLVSVNWFVROWJUPVDVHVNF
        EVPWKVDVIVJ $.
    $}

    ${
      zrhnm.1 $e |- L = ( ZRHom ` R ) $.
      $( The norm of the image by ` ZRHom ` of an integer in a normed ring.
         (Contributed by Thierry Arnoux, 8-Nov-2017.) $)
      zrhnm $p |- ( ( ( Z e. NrmMod /\ Z e. NrmRing /\ R e. NzRing )
                           /\ M e. ZZ ) -> ( N ` ( L ` M ) ) = ( abs ` M ) ) $=
        ( wcel cnzr cz cfv c1 cmul co wceq syl eqid cnlm cnrg w3a wa cur simpl3
        cmg crg nzrrng simpr ccnfld cress zrhmulg fveq2d syl2anc simpl1 rngidcl
        cabs nmmulg syl3anc cnm zlmnm fveq1d simpl2 c0g nrgrng nzrnz zlm1 isnzr
        wne zlm0 sylanbrc nm1 eqtrd oveq2d 3eqtrd zcnd abscl recnd mulid1 3syl
        cc ) FUAKZFUBKZBLKZUCZDMKZUDZDCNZENZDURNZOPQZWKWHWJDBUENZBUGNZQZENZWKWM
        ENZPQZWLWHBUHKZWGWJWPRWHWEWSWCWDWEWGUFZBUISZWFWGUJZWSWGUDWIWOEBWNWMCDUK
        MULQZXCTJWNTZWMTZUMUNUOWHWCWGWMAKZWPWRRWCWDWEWGUPXBWHWSXFXAABWMGXEUQSAB
        WNDEWMFGHIXDUSUTWHWQOWKPWHWQWMFVANZNZOWHWMEXGWHWEEXGRWTBELFIHVBSVCWHWDF
        LKZXHORWCWDWEWGVDZWHFUHKZWMBVENZVJZXIWHWDXKXJFVFSWHWEXMWTBWMXLXEXLTZVGS
        FWMXLWMBFIXEVHZBFXLIXNVKVIVLFWMXGXGTXOVMUOVNVOVPWHDWBKZWKWBKWLWKRWHDXBV
        QXPWKDVRVSWKVTWAVN $.
    $}
  $}

  ${
    $d a b x $.  $d x y R $.  $d x z R $.
    $( The ` ZZ ` -module of ` CC ` is a normed module.  (Contributed by
       Thierry Arnoux, 25-Feb-2018.) $)
    cnzh $p |- ( ZMod ` CCfld ) e. NrmMod $=
      ( vz vx ccnfld cfv wcel cz co cnrg cv cabs cmul wceq cc wral wa eqid mp2b
      cnnrg cvv ax-mp czlm cnlm cngp clmod cress w3a cmg cres zhmnrg nrgngp crg
      cabel nrgrng rngabl zlmlmod mpbi csubrg zsubrg subrgnrg mp2an zsscn simpl
      3pm3.2i sseldi simpr absmul syl2anc cnfldmulg fveq2d fvres adantr 3eqtr4d
      oveq1d ralrimiva pm3.2i cnfldbas zlmbas cnm cnfldex cnfldnm zlmnm zlmvsca
      rgen csca zlmsca zzsbase cmnd cc0 wss cnrng rngmnd 0z cnfld0 ressnm mp3an
      isnlm mpbir ) CUADZUBEWRUCEZWRUDEZCFUEGZHEZUFZAIZBIZCUGDZGZJDZXDJFUHZDZXE
      JDZKGZLZBMNZAFNZOXCXOWSWTXBCHEZWRHEWSRCWRWRPZUIWRUJQCULEZWTXPCUKEZXRRCUMC
      UNQCWRXQUOUPXPFCUQDEXBRURFCXAXAPZUSUTVCXNAFXDFEZXMBMYAXEMEZOZXDXEKGZJDZXD
      JDZXKKGZXHXLYCXDMEYBYEYGLYCFMXDVAYAYBVBVDYAYBVEXDXEVFVGYCXGYDJXDXEVHVIYCX
      JYFXKKYAXJYFLYBXDFJVJVKVMVLVNWCVOABXIXFXAFJMWRMCWRXQVPVQCSEZJWRVRDLVSCJSW
      RXQVTWATXFCWRXQXFPWBYHXAWRWDDLVSCSWRXAXQXTWETXAXTWFCWGEZWHFEFMWIXIXAVRDLX
      SYIWJCWKTWLVAFMCXAJWHXTVPWMVTWNWOWPWQ $.

    rezh.1 $e |- R = ( CCfld |`s RR ) $.
    $( The ` ZZ ` -module of ` RR ` is a normed module.  (Contributed by
       Thierry Arnoux, 14-Feb-2018.) $)
    rezh $p |- ( ZMod ` R ) e. NrmMod $=
      ( vz vx cfv wcel ccnfld cz co cnrg cabs cr cmul wceq wa eqid cc ax-mp cc0
      fvres czlm cnlm cngp clmod cress cv cvsca cres wral csubrg cnnrg resubdrg
      w3a cdr simpli subrgnrg mp2an zhmnrg nrgngp mp2b cabel crg nrgrng zlmlmod
      rngabl mpbi zsubrg 3pm3.2i zsscn simpl sseldi ax-resscn simpr syl2anc cmg
      absmul csubg subrgsubg eqcomi subgmulg mp3an1 cnfldmulg syldan eqtr3d zre
      zlmvsca fveq2d remulcl syl sylan eqtrd oveqan12d 3eqtr4d ralrimiva pm3.2i
      rgen rebase zlmbas cvv cnm ccusp recusp elexi cmnd wss cnrng 0re cnfldbas
      rngmnd cnfld0 cnfldnm ressnm mp3an zlmnm csca zlmsca zzsbase isnlm mpbir
      0z ) AUAEZUBFYAUCFZYAUDFZGHUEIZJFZUMZCUFZDUFZYAUGEZIZKLUHZEZYGKHUHZEZYHYK
      EZMIZNZDLUIZCHUIZOYFYSYBYCYEAJFZYAJFYBGJFZLGUJEZFZYTUKUUCGLUEIUNFULUOZLGA
      BUPUQZAYAYAPZURYAUSUTAVAFZYCYTAVBFUUGUUEAVCAVEUTAYAUUFVDVFUUAHUUBFYEUKVGH
      GYDYDPZUPUQVHYRCHYGHFZYQDLUUIYHLFZOZYGYHMIZKEZYGKEZYHKEZMIZYLYPUUKYGQFYHQ
      FZUUMUUPNUUKHQYGVIUUIUUJVJVKUUKLQYHVLUUIUUJVMVKZYGYHVPVNUUKYLUULYKEZUUMUU
      KYJUULYKUUKYGYHGVOEZIZYJUULLGVQEFZUUIUUJUVAYJNUUCUVBUUDLGVRRLYIUUTGAYGYHU
      UTPBAVOEZYIUVCAYAUUFUVCPWFVSVTWAUUIUUJUUQUVAUULNUURYGYHWBWCWDWGUUIYGLFZUU
      JUUSUUMNZYGWEUVDUUJOUULLFUVEYGYHWHUULLKTWIWJWKUUIUUJYNUUNYOUUOMYGHKTYHLKT
      WLWMWNWPWOCDYMYIYDHYKLYALAYAUUFABWQWRAWSFZYKYAWTENAXAABXBXCZAYKWSYAUUFGXD
      FZSLFLQXEYKAWTENGVBFUVHXFGXIRZXGVLLQGAKSBXHXJXKXLXMXNRYIPUVFYDYAXOENUVGAW
      SYAYDUUFUUHXPRYDUUHXQUVHSHFHQXEYMYDWTENUVIXTVIHQGYDKSUUHXHXJXKXLXMXRXS $.
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
      ( vf cz cv czrh cfv ccnv cui co cdvr cvv fveq2 cima cdiv cmpt2 cqqh eqidd
      cop wceq syl6eqr cnveqd imaeq12d fveq1d oveq123d opeq2d mpt2eq123dv rneqd
      crn df-qqh zex wcel fvex eqeltri cnvex imaexg ax-mp mpt2ex rnex fvmpt ) J
      DABKJLZMNZOZVHPNZUAZALZBLZUBQZVMVINZVNVINZVHRNZQZUFZUCZUPABKFOZDPNZUAZVOV
      MFNZVNFNZCQZUFZUCZUPSUDVHDUGZWAWIWJABKVLVTKWDWHWJKUEWJVJWBVKWCWJVIFWJVIDM
      NZFVHDMTIUHZUIVHDPTUJWJVSWGVOWJVPWEVQWFVRCWJVRDRNCVHDRTGUHWJVMVIFWLUKWJVN
      VIFWLUKULUMUNUOABJUQWIABKWDWHURWBSUSWDSUSFFWKSIDMUTVAVBWBWCSVCVDVEVFVG $.
  $}

  ${
    zrhker.0 $e |- B = ( Base ` R ) $.
    zrhker.1 $e |- L = ( ZRHom ` R ) $.
    zrhker.2 $e |- .0. = ( 0g ` R ) $.
    $( The kernel of the homomorphism from the integers to a ring, if it is
       injective.  (Contributed by Thierry Arnoux, 26-Oct-2017.) $)
    zrhf1ker $p |- ( R e. Ring ->
       ( L : ZZ -1-1-> B <-> ( `' L " { .0. } ) = { 0 } ) ) $=
      ( crg wcel ccnfld cz cress co crh wf1 ccnv csn cima cc0 wceq eqid zzsbase
      wb zrhrhm zzs0 kerf1hrm syl ) BHICJKLMZBNMIKACOCPDQRSQTUCBCUHUHUAZFUDKAUH
      BCSDUHUIUBEUHUIUEGUFUG $.

    $d x B $.  $d x R $.
    $( The kernel of the homomorphism from the integers to a ring is injective
       if and only if the ring has characteristic 0 .  (Contributed by Thierry
       Arnoux, 8-Nov-2017.) $)
    zrhchr $p |- ( R e. Ring -> ( ( chr ` R ) = 0 <-> L : ZZ -1-1-> B ) ) $=
      ( vx crg wcel cz wf1 cv cur cfv co cc0 wceq wb eqid cmg cmpt ccnfld cress
      cod cchr zrhval2 f1eq1 syl cgrp rnggrp rngidcl odf1 syl2anc chrval eqeq1i
      a1i 3bitr2rd ) BIJZKACLZKAHKHMBNOZBUAOZPUBZLZVABUEOZOZQRZBUFOZQRZUSCVCRUT
      VDSBVBVAHCUCKUDPZVJTFVBTZVATZUGKACVCUHUIUSBUJJVAAJVGVDSBUKABVAEVLULHVAVBV
      CBVEAEVETZVKVCTUMUNVGVISUSVFVHQVHBVAVEVMVLVHTUOUPUQUR $.

    $( The kernel of the homomorphism from the integers to a ring with
       characteristic 0.  (Contributed by Thierry Arnoux, 8-Nov-2017.) $)
    zrhker $p |- ( R e. Ring ->
       ( ( chr ` R ) = 0 <-> ( `' L " { .0. } ) = { 0 } ) ) $=
      ( crg wcel cchr cfv cc0 wceq cz wf1 ccnv csn cima zrhchr zrhf1ker bitrd )
      BHIBJKLMNACOCPDQRLQMABCDEFGSABCDEFGTUA $.

    $( The preimage by ` ZRHom ` of the unit of a division ring is
       ` ( ZZ \ { 0 } ) ` .  (Contributed by Thierry Arnoux, 22-Oct-2017.) $)
    zrhunitpreima $p |- ( ( R e. DivRing /\ ( chr ` R ) = 0 )
      -> ( `' L " ( Unit ` R ) ) = ( ZZ \ { 0 } ) ) $=
      ( cdr wcel cfv cc0 wceq cima csn cdif cz eqid adantr co 3syl cchr wa ccnv
      cui c0g crg isdrng simprbi imaeq2d wfun drngrng ccnfld crh zrhrhm zzsbase
      cress wf rhmf ffun difpreima fimacnv zrhker biimpa sylan difeq12d 3eqtrd
      4syl ) BHIZBUAJKLZUBZCUCZBUDJZMZVKABUEJZNZOZMZVKAMZVKVOMZOZPKNZOVHVMVQLVI
      VHVLVPVKVHBUFIZVLVPLABVLVNEVLQVNQZUGUHUIRVHVQVTLZVIVHWBCUJZWDBUKZWBCULPUP
      SZBUMSIZPACUQZWEBCWGWGQZFUNZPAWGBCWGWJUOEURZPACUSTAVOCUTTRVJVRPVSWAVHVRPL
      ZVIVHWBWHWIWMWFWKWLPACVAVGRVHWBVIVSWALZWFWBVIWNABCVNEFWCVBVCVDVEVF $.

    $( Condition for the image by ` ZRHom ` to be a unit.  (Contributed by
       Thierry Arnoux, 30-Oct-2017.) $)
    elzrhunit $p |- ( ( ( R e. DivRing /\ ( chr ` R ) = 0 )
      /\ ( M e. ZZ /\ M =/= 0 ) ) -> ( L ` M ) e. ( Unit ` R ) ) $=
      ( cdr wcel cchr cfv cc0 wceq wa cz wne wfn co 3syl cui crg simpll drngrng
      ccnv cima ccnfld cress crh wf eqid zrhrhm zzsbase rhmf ffn cdif simprl wn
      csn elsncg necon3bbid biimpar adantl eldifd zrhunitpreima adantr eleqtrrd
      elpreima simplbda syl2anc ) BIJZBKLMNZOZDPJZDMQZOZOZCPRZDCUEBUALZUFZJZDCL
      VSJZVQVKBUBJZVRVKVLVPUCBUDWCCUGPUHSZBUISJPACUJVRBCWDWDUKZGULPAWDBCWDWEUMF
      UNPACUOTTVQDPMUSZUPZVTVQDPWFVMVNVOUQVPDWFJZURZVMVNWIVOVNWHDMDMPUTVAVBVCVD
      VMVTWGNVPABCEFGHVEVFVGVRWAVNWBPDVSCVHVIVJ $.
  $}

  $( Lemma for ~ qqhval2 (Contributed by Thierry Arnoux, 29-Oct-2017.) $)
  elzdif0 $p |- ( M e. ( ZZ \ { 0 } ) -> ( M e. NN \/ -u M e. NN ) ) $=
    ( cz cc0 csn cdif wcel wceq cneg eldifi eldifn elsncg notbid biimpa syl2anc
    wn cn wo w3o cr sylib wa elz simprd 3orass orel1 sylc ) ABCDZEFZACGZOZUIAPF
    ZAHPFZQZQZUMUHABFZAUGFZOZUJABUGIZABUGJUOUQUJUOUPUIACBKLMNUHUIUKULRZUNUHASFZ
    USUHUOUTUSUAURAUBTUCUIUKULUDTUIUMUEUF $.

  ${
    $d z X $.  $d z Y $.
    qqhval2.0 $e |- B = ( Base ` R ) $.
    qqhval2.1 $e |- ./ = ( /r ` R ) $.
    qqhval2.2 $e |- L = ( ZRHom ` R ) $.
    $( Lemma for ~ qqhval2 (Contributed by Thierry Arnoux, 29-Oct-2017.) $)
    qqhval2lem $p |- ( ( ( R e. DivRing /\ ( chr ` R ) = 0 )
      /\ ( X e. ZZ /\ Y e. ZZ /\ Y =/= 0 ) )
         -> ( ( L ` ( numer ` ( X / Y ) ) ) ./ ( L ` ( denom ` ( X / Y ) ) ) )
         = ( ( L ` X ) ./ ( L ` Y ) ) ) $=
      ( wcel cfv cc0 wceq wa cz co cmul wn fveq2d c1 cdr cchr wne w3a cgcd cdiv
      cnumer cdenom ccnfld cress crh cui crg drngrng eqid syl ad2antrr cdivides
      zrhrhm simpr1 simpr2 gcdcld nn0zd simpr3 gcdeq0 simplbda necon3d syl21anc
      wbr ex imp gcddvds syl2anc simpld dvdsval2 biimpa syl31anc simprd zzsbase
      c0g wf rhmf ffvelrnd wfn ccnv csn cima zcnd divne0d ovex elsnc necon3bbii
      ffn sylibr simplr zrhker neleqtrrd elpreima baibd biimprd con3and fvex wb
      sylib drngunit mpbir2and zzsmulr rhmdvd syl132anc cn cneg divnumden sylan
      eqcomd oveq12d adantr mulm1d neg1cn a1i mulcomd eqtr3d divnumden2 syl3anc
      cc simpr znegcld cabs znegcl ax-mp ax-1cn absnegi eqtri zrngunit mpbir2an
      1z abs1 elrhmunit 3eqtr4rd wo divcan1d simp3 neneqd cr simp2 3orass orel1
      w3o elz sylc adantl mpjaodan 3eqtr3d ) CUAJZCUBKLMZNZEOJZFOJZFLUCZUDZNZEE
      FUEPZUFPZDKZFUVAUFPZDKZBPZUVBUVAQPZDKZUVDUVAQPZDKZBPZEFUFPZUGKZDKZUVLUHKZ
      DKZBPZEDKZFDKZBPUUTDUIOUJPZCUKPJZUVBOJZUVDOJZUVAOJZUVECULKZJZUVADKZUWEJZU
      VFUVKMUUMUWAUUNUUSUUMCUMJZUWACUNZCDUVTUVTUOZIUSUPUQZUUTUWDUVALUCZUUPUVAEU
      RVIZUWBUUTUVAUUTEFUUOUUPUUQUURUTZUUOUUPUUQUURVAZVBVCZUUTUUPUUQUURUWMUWOUW
      PUUOUUPUUQUURVDZUUPUUQNZUURUWMUWSUVALFLUWSUVALMZFLMZUWSUWTELMUXAEFVEVFVJV
      GVKVHZUWOUUTUWNUVAFURVIZUUTUUPUUQUWNUXCNUWOUWPEFVLVMZVNUWDUWMUUPUDUWNUWBU
      VAEVOVPVQZUUTUWDUWMUUQUXCUWCUWQUXBUWPUUTUWNUXCUXDVRUWDUWMUUQUDUXCUWCUVAFV
      OVPVQZUWQUUTUWFUVEAJZUVECVTKZUCZUUTOAUVDDUUTUWAOADWAZUWLOAUVTCDUVTUWKVSZG
      WBUPZUXFWCUUTDOWDZUWCUVDDWEUXHWFZWGZJZRZUXIUUTUXJUXMUXLOADWMUPZUXFUUTUXOL
      WFZUVDUUTUVDLUCUVDUXSJZRUUTFUVAUUTFUWPWHZUUTUVAUWQWHZUWRUXBWIUXTUVDLUVDLF
      UVAUFWJWKWLWNUUTUWIUUNUXOUXSMZUUMUWIUUNUUSUWJUQUUMUUNUUSWOUWIUUNUYCACDUXH
      GIUXHUOZWPVPVMZWQUXMUWCNZUXQNUVEUXNJZRUXIUYFUYGUXPUYFUXPUYGUXMUXPUWCUYGOU
      VDUXNDWRWSWTXAUYGUVEUXHUVEUXHUVDDXBWKWLXDVHUUMUWFUXGUXINXCUUNUUSACUWEUVEU
      XHGUWEUOZUYDXEUQXFZUUTUWHUWGAJZUWGUXHUCZUUTOAUVADUXLUWQWCUUTUXMUWDUVAUXOJ
      ZRZUYKUXRUWQUUTUXOUXSUVAUUTUWMUVAUXSJZRUXBUYNUVALUVALEFUEWJWKWLWNUYEWQUXM
      UWDNZUYMNUWGUXNJZRUYKUYOUYPUYLUYOUYLUYPUXMUYLUWDUYPOUVAUXNDWRWSWTXAUYPUWG
      UXHUWGUXHUVADXBWKWLXDVHUUMUWHUYJUYKNXCUUNUUSACUWEUWGUXHGUYHUYDXEUQXFUVBUV
      DUVABUVTCQUWEDOUYHUXKHUVTUWKXGZXHXIUUTFXJJZUVFUVQMFXKXJJZUUTUYRNZUVCUVNUV
      EUVPBUYTUVBUVMDUYTUVMUVBUYTUVMUVBMZUVOUVDMZUUTUUPUYRVUAVUBNUWOEFXLXMZVNXN
      SUYTUVDUVODUYTUVOUVDUYTVUAVUBVUCVRXNSXOUUTUYSNZUVBXKZDKZUVDXKZDKZBPUVBTXK
      ZQPZDKZUVDVUIQPZDKZBPZUVQUVFVUDVUFVUKVUHVUMBVUDVUEVUJDVUDVUIUVBQPVUEVUJVU
      DUVBVUDUVBUUTUWBUYSUXEXPZWHZXQVUDVUIUVBVUIYDJVUDXRXSZVUPXTYASVUDVUGVULDVU
      DVUIUVDQPVUGVULVUDUVDVUDUVDUUTUWCUYSUXFXPZWHZXQVUDVUIUVDVUQVUSXTYASXOVUDU
      VNVUFUVPVUHBVUDUVMVUEDVUDUVMVUEMZUVOVUGMZVUDUUPUUQUYSVUTVVANUUTUUPUYSUWOX
      PUUTUUQUYSUWPXPUUTUYSYEEFYBYCZVNSVUDUVOVUGDVUDVUTVVAVVBVRSXOVUDUWAUWBUWCV
      UIOJZUWFVUIDKUWEJZUVFVUNMUUTUWAUYSUWLXPZVUOVURVUDTTOJZVUDYOXSYFUUTUWFUYSU
      YIXPVUDUWAVUIUVTULKJZVVDVVEVVGVUDVVGVVCVUIYGKZTMVVFVVCYOTYHYIVVHTYGKTTYJY
      KYPYLVUIUVTUWKYMYNXSVUIUVTCDYQVMUVBUVDVUIBUVTCQUWEDOUYHUXKHUYQXHXIYRUUSUY
      RUYSYSZUUOUUSUXARUXAVVIYSZVVIUUSFLUUPUUQUURUUAUUBUUSUXAUYRUYSUUGZVVJUUSFU
      UCJZVVKUUSUUQVVLVVKNUUPUUQUURUUDFUUHXDVRUXAUYRUYSUUEXDUXAVVIUUFUUIUUJUUKU
      UTUVHUVRUVJUVSBUUTUVGEDUUTEUVAUUTEUWOWHUYBUXBYTSUUTUVIFDUUTFUVAUYAUYBUXBY
      TSXOUUL $.

    $d x y z $.  $d e q s x y ./ $.  $d e q s x y B $.  $d e q s x y L $.
    $d e q s x y R $.
    $( Value of the canonical homormorphism from the rational number when the
       target ring is a division ring.  (Contributed by Thierry Arnoux,
       26-Oct-2017.) $)
    qqhval2 $p |- ( ( R e. DivRing /\ ( chr ` R ) = 0 ) -> ( QQHom ` R ) =
      ( q e. QQ |-> ( ( L ` ( numer ` q ) ) ./ ( L ` ( denom ` q ) ) ) ) ) $=
      ( vx vy ve vs wcel cfv cc0 wceq wa cz co cq cdr cchr cqqh ccnv cui cv cop
      cima cdiv crn csn cdif cnumer cdenom cmpt cvv elex adantr cur eqid qqhval
      cmpt2 syl eqidd c0g zrhunitpreima mpt2eq12 syl2anc rneqd wrex copab nfab1
      cab nfv nfcv wex simpr wne zssq simplrl sseldi simplrr eldifad wn eldifbd
      elsn necon3bbii qdivcl syl3anc simplll simpllr qqhval2lem eqcomd syl23anc
      sylib w3a ovex opeq12 eqeq2d eleq1d fveq2d oveq12d eqeq12d anbi12d spc2ev
      simpl syl12anc ex rexlimdvva imp 19.42vv simprrl qnumcl qdencl nnzd nnne0
      elsni necon3ai 3syl eldifd qeqnumdivden simprrr opeq12d eqtrd oveq1 fveq2
      cn simprl oveq1d oveq2 oveq2d rspc2ev exlimivv sylbir impbida abid elopab
      3bitr4g eqrd rnmpt2 df-mpt 3eqtr4g 3eqtrd ) CUAMZCUBNOPZQZCUCNZIJRDUDCUEN
      UHZIUFZJUFZUISZUUIDNZUUJDNZBSZUGZVBZUJZIJRROUKZULZUUOVBZUJZETEUFZUMNZDNZU
      VBUNNZDNZBSZUOZUUFCUPMZUUGUUQPUUDUVIUUECUAUQURIJBCCUSNZDGUVJUTHVAVCUUFUUP
      UUTUUFRRPUUHUUSPUUPUUTPUUFRVDACDCVENZFHUVKUTVFIJRUUHRUUSUUOVGVHVIUUFKUFZU
      UOPZJUUSVJIRVJZKVMZUVBTMZLUFZUVGPZQZELVKZUVAUVHUUFKUVOUVTUUFKVNUVNKVLKUVT
      VOUUFUVNUVLUVBUVQUGZPZUVSQZLVPEVPZUVLUVOMUVLUVTMUUFUVNUWDUUFUVNUWDUUFUVMU
      WDIJRUUSUUFUUIRMZUUJUUSMZQZQZUVMUWDUWHUVMQZUVMUUKTMZUUNUUKUMNZDNZUUKUNNZD
      NZBSZPZUWDUWHUVMVQUWIUUITMUUJTMUUJOVRZUWJUWIRTUUIVSUUFUWEUWFUVMVTZWAUWIRT
      UUJVSUWIUUJRUURUUFUWEUWFUVMWBZWCZWAUWIUUJUURMZWDUWQUWIUUJRUURUWSWEUXAUUJO
      JOWFWGWOZUUIUUJWHWIUWIUUDUUEUWEUUJRMZUWQUWPUUDUUEUWGUVMWJUUDUUEUWGUVMWKUW
      RUWTUXBUUFUWEUXCUWQWPQUWOUUNABCDUUIUUJFGHWLWMWNUWCUVMUWJUWPQZQELUUKUUNUUI
      UUJUIWQUULUUMBWQUVBUUKPZUVQUUNPZQZUWBUVMUVSUXDUXGUWAUUOUVLUVBUVQUUKUUNWRW
      SUXGUVPUWJUVRUWPUXGUVBUUKTUXEUXFXFZWTUXGUVQUUNUVGUWOUXEUXFVQUXGUVDUWLUVFU
      WNBUXGUVCUWKDUXGUVBUUKUMUXHXAXAUXGUVEUWMDUXGUVBUUKUNUXHXAXAXBXCXDXDXEXGXH
      XIXJUUFUWDQUUFUWCQZLVPEVPUVNUUFUWCELXKUXIUVNELUXIUVCRMZUVEUUSMUVLUVCUVEUI
      SZUVGUGZPZUVNUXIUVPUXJUUFUWBUVPUVRXLZUVBXMVCUXIUVERUURUXIUVEUXIUVPUVEYGMZ
      UXNUVBXNVCZXOUXIUXOUVEOVRUVEUURMZWDUXPUVEXPUXQUVEOUVEOXQXRXSXTUXIUVLUWAUX
      LUUFUWBUVSYHUXIUVBUXKUVQUVGUXIUVPUVBUXKPUXNUVBYAVCUUFUWBUVPUVRYBYCYDUVMUX
      MUVLUVCUUJUISZUVDUUMBSZUGZPIJUVCUVERUUSUUIUVCPZUUOUXTUVLUYAUUKUXRUUNUXSUU
      IUVCUUJUIYEUYAUULUVDUUMBUUIUVCDYFYIYCWSUUJUVEPZUXTUXLUVLUYBUXRUXKUXSUVGUU
      JUVEUVCUIYJUYBUUMUVFUVDBUUJUVEDYFYKYCWSYLWIYMYNYOUVNKYPUVSELUVLYQYRYSIJKR
      UUSUUOUUTUUTUTYTELTUVGUUAUUBUUC $.

    $d q Q $.
    $( Value of the canonical homormorphism from the rational number when the
       target ring is a division ring.  (Contributed by Thierry Arnoux,
       30-Oct-2017.) $)
    qqhvval $p |- ( ( ( R e. DivRing /\ ( chr ` R ) = 0 ) /\ Q e. QQ ) ->
      ( ( QQHom ` R ) ` Q )
          = ( ( L ` ( numer ` Q ) ) ./ ( L ` ( denom ` Q ) ) ) ) $=
      ( vq wcel cfv wceq wa cq cnumer cdenom co cvv simpr fveq2d cchr cqqh cmpt
      cdr cc0 cv qqhval2 adantr oveq12d ovex a1i fvmptd ) DUDJDUAKUELMZCNJZMZIC
      IUFZOKZEKZUPPKZEKZBQZCOKZEKZCPKZEKZBQZNDUBKZRUMVGINVAUCLUNABDEIFGHUGUHUOU
      PCLZMZURVCUTVEBVIUQVBEVIUPCOUOVHSZTTVIUSVDEVIUPCPVJTTUIUMUNSVFRJUOVCVEBUJ
      UKUL $.

    $( The image of ` 0 ` by the ` QQHom ` homomorphism is the ring's zero.
       (Contributed by Thierry Arnoux, 22-Oct-2017.) $)
    qqh0 $p |- ( ( R e. DivRing /\ ( chr ` R ) = 0 )
                                     -> ( ( QQHom ` R ) ` 0 ) = ( 0g ` R ) ) $=
      ( wcel cfv cc0 wceq wa co cq cz 0z c1 fveq2i eqid syl cdr cchr cnumer c0g
      cqqh cdenom zssq sselii qqhvval mpan2 cgcd cdiv cabs 1z gcd0id ax-mp abs1
      eqtri 0cn div1i eqcomi pm3.2i cn wb qnumdenbi mp3an simpli simpri oveq12i
      1nn mpbi cur drngrng zrh0 zrh1 oveq12d cgrp drnggrp grpidcl syl2anc eqtrd
      crg dvr1 syl5eq adantr ) CUAHZCUBIJKZLZJCUEIIZJUCIZDIZJUFIZDIZBMZCUDIZWHJ
      NHZWIWNKONJUGPUHZABJCDEFGUIUJWFWNWOKWGWFWNJDIZQDIZBMZWOWKWRWMWSBWJJDWJJKZ
      WLQKZJQUKMZQKZJJQULMZKZLZXAXBLZXDXFXCQUMIZQQOHXCXIKUNQUOUPUQURXEJJUSUTVAV
      BWPJOHQVCHXGXHVDWQPVJJJQVEVFVKZVGRWLQDXAXBXJVHRVIWFWTWOCVLIZBMZWOWFCWBHZW
      TXLKCVMZXMWRWOWSXKBCDWOGWOSZVNCXKDGXKSZVOVPTWFXMWOAHZXLWOKXNWFCVQHXQCVRAC
      WOEXOVSTABCXKWOEFXPWCVTWAWDWEWA $.

    $( The image of ` 1 ` by the ` QQHom ` homomorphism is the ring's unit.
       (Contributed by Thierry Arnoux, 22-Oct-2017.) $)
    qqh1 $p |- ( ( R e. DivRing /\ ( chr ` R ) = 0 )
                                     -> ( ( QQHom ` R ) ` 1 ) = ( 1r ` R ) ) $=
      ( cdr wcel cfv wceq wa c1 co cq cz 1z fveq2i syl eqtrd cchr cnumer cdenom
      cc0 cqqh cur zssq sselii qqhvval mpan2 cgcd cdiv gcd1 ax-mp ax-1cn eqcomi
      div1i pm3.2i cn wb 1nn qnumdenbi mp3an mpbi simpli simpri oveq12i drngrng
      crg eqid zrh1 oveq12d rngidcl dvr1 syl2anc syl5eq adantr ) CHIZCUAJUDKZLZ
      MCUEJJZMUBJZDJZMUCJZDJZBNZCUFJZVTMOIZWAWFKPOMUGQUHZABMCDEFGUIUJVRWFWGKVSV
      RWFMDJZWJBNZWGWCWJWEWJBWBMDWBMKZWDMKZMMUKNMKZMMMULNZKZLZWLWMLZWNWPMPIZWNQ
      MUMUNWOMMUOUQUPURWHWSMUSIWQWRUTWIQVAMMMVBVCVDZVERWDMDWLWMWTVFRVGVRWKWGWGB
      NZWGVRCVIIZWKXAKCVHZXBWJWGWJWGBCWGDGWGVJZVKZXEVLSVRXBWGAIZXAWGKXCVRXBXFXC
      ACWGEXDVMSABCWGWGEFXDVNVOTVPVQT $.

    $( TODO simplify this & others using properties of ` ( CClfd |`s ZZ )` $)
    $( ` QQHom ` as a function.  (Contributed by Thierry Arnoux,
       28-Oct-2017.) $)
    qqhf $p |- ( ( R e. DivRing /\ ( chr ` R ) = 0 )
      -> ( QQHom ` R ) : QQ --> B ) $=
      ( vq wcel cfv cc0 wceq wa cq cdenom co adantr cz eqid 3syl cchr cv cnumer
      cdr cqqh qqhval2 crg cui drngrng ccnfld crh wf zrhrhm zzsbase rhmf qnumcl
      adantl ffvelrnd c0g wne simpll cn qdencl nnzd csn ccnv cima nnne0d neneqd
      cress wn fvex elsnc sylnibr zrhker biimpa sylan neleqtrrd wfn wb elpreima
      ffn biimpar expr con3and syl21anc neneqad drngunit syl12anc dvrcl syl3anc
      sylnib fmpt3d ) CUDIZCUAJKLZMZHNHUBZUCJZDJZWQOJZDJZBPZACUEJABCDHEFGUFWPWQ
      NIZMZCUGIZWSAIXACUHJZIZXBAIWPXEXCWNXEWOCUIZQQZXDRAWRDXDXEDUJRVJPZCUKPIZRA
      DULZXICDXJXJSZGUMZRAXJCDXJXMUNEUOZTZXCWRRIWPWQUPUQURXDWNXAAIZXACUSJZUTZXG
      WNWOXCVAZXDRAWTDXPXDWTXCWTVBIWPWQVCUQZVDZURXDXAXRXDXAXRVEZIZXAXRLXDWNWTRI
      ZWTDVFYCVGZIZVKYDVKXTYBXDYFKVEZWTXDWTKLWTYHIXDWTKXDWTYAVHVIWTKWQOVLVMVNWP
      YFYHLZXCWNXEWOYIXHXEWOYIACDXREGXRSZVOVPVQQVRWNYEMYDYGWNYEYDYGWNYGYEYDMZWN
      XEDRVSZYGYKVTXHXEXKXLYLXNXORADWBTRWTYCDWATWCWDWEWFXAXRWTDVLVMWLWGWNXGXQXS
      MACXFXAXREXFSZYJWHWCWIABCXFWSXAEYMFWJWKWM $.

    $( The image of a quotient by the ` QQHom ` homomorphism.  (Contributed by
       Thierry Arnoux, 28-Oct-2017.) $)
    qqhvq $p |- ( ( ( R e. DivRing /\ ( chr ` R ) = 0 )
      /\ ( X e. ZZ /\ Y e. ZZ /\ Y =/= 0 ) )
             -> ( ( QQHom ` R ) ` ( X / Y ) ) = ( ( L ` X ) ./ ( L ` Y ) ) ) $=
      ( cdr wcel cfv cc0 wceq wa cz co cq zssq sseldi cchr wne cdiv cqqh cnumer
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
      ( wcel cfv cc0 wceq caddc cq eqid cmul co cz ad2antrl vx vy cdr wa cplusg
      cchr cqqh qrngbas cvv qex ccnfld cnfldadd ressplusg ax-mp cgrp qdrng mp1i
      drnggrp adantr qqhf cv cnumer cdenom crg drngrng ad2antrr wf cress zrhrhm
      cui crh zzsbase rhmf 3syl qnumcl cn qdencl ad2antll nnzd zmulcld ffvelrnd
      cmulr syl zzsmulr rhmmul syl3anc wne simpl nnne0d c0g elzrhunit unitmulcl
      syl12anc eqeltrd syl13anc cdiv qeqnumdivden oveq12d zcnd divadddivd eqtrd
      dvrdir fveq2d zaddcld qqhvq cghm rhmghm w3a zzsplusg ghmlin oveq1d 3eqtrd
      mulne0d rhmdvd syl132anc mulcomd oveq2d 3eqtr4d isghmd ) DUCJZDUFKLMZUDZU
      AUBNDUEKZCDDUGKZOACIUHFOUIJNCUEKMUJONUKCUIIULUMUNYCPZCUCJCUOJYBCIUPCURUQX
      TDUOJYADURUSABDEFGHUTYBUAVAZOJZUBVAZOJZUDZUDZYFVBKZYHVCKZQRZEKZYHVBKZYFVC
      KZQRZEKZYCRZYQYMQRZEKZBRZYOUUBBRZYSUUBBRZYCRZYFYHNRZYDKZYFYDKZYHYDKZYCRYK
      DVDJZYOAJYSAJUUBDVJKZJUUCUUFMXTUUKYAYJDVEZVFZYKSAYNEYBSAEVGZYJYBUUKEUKSVH
      RZDVKRJZUUOXTUUKYAUUMUSDEUUPUUPPZHVIZSAUUPDEUUPUURVLZFVMVNUSZYKYLYMYGYLSJ
      ZYBYIYFVOTZYKYMYIYMVPJYBYGYHVQVRZVSZVTZWAYKSAYREUVAYKYPYQYIYPSJZYBYGYHVOV
      RZYKYQYGYQVPJYBYIYFVQTZVSZVTZWAYKUUBYQEKZYMEKZDWBKZRZUULYKUUQYQSJZYMSJZUU
      BUVOMYKUUKUUQUUNUUSWCZUVJUVEYQYMUUPDQUVNESUUTUUPUURWDZUVNPZWEWFYKUUKUVLUU
      LJZUVMUULJZUVOUULJUUNYKYBUVPYQLWGZUWAYBYJWHZUVJYKYQUVIWIZADEYQDWJKZFHUWFP
      ZWKWMZYKYBUVQYMLWGZUWBUWDUVEYKYMUVDWIZADEYMUWFFHUWGWKWMZDUVNUULUVLUVMUULP
      ZUVTWLWFWNABYCDUULYOYSUUBFUWLYEGXBWOYKUUHYNYRNRZUUAWPRZYDKZUWMEKZUUBBRZUU
      CYKUUGUWNYDYKUUGYLYQWPRZYPYMWPRZNRUWNYKYFUWRYHUWSNYGYFUWRMYBYIYFWQZTYIYHU
      WSMYBYGYHWQZVRWRYKYLYQYPYMYKYLUVCWSYKYQUVJWSZYKYPUVHWSYKYMUVEWSZUWEUWJWTX
      AXCYKYBUWMSJUUASJUUALWGUWOUWQMUWDYKYNYRUVFUVKXDYKYQYMUVJUVEVTYKYQYMUXBUXC
      UWEUWJXMABDEUWMUUAFGHXEWOYKEUUPDXFRJZYNSJZYRSJZUWQUUCMYKUUQUXDUVRUUPDEXGW
      CUVFUVKUXDUXEUXFXHUWPYTUUBBNYCUUPDYNEYRSUUTUUPUURXIYEXJXKWFXLYKUUIUUDUUJU
      UEYCYKUUIUWRYDKZYLEKUVLBRZUUDYGUUIUXGMYBYIYGYFUWRYDUWTXCTYKYBUVBUVPUWCUXG
      UXHMUWDUVCUVJUWEABDEYLYQFGHXEWOYKUUQUVBUVPUVQUWAUWBUXHUUDMUVRUVCUVJUVEUWH
      UWKYLYQYMBUUPDQUULESUWLUUTGUVSXNXOXLYKUUJUWSYDKZUUEYIUUJUXIMYBYGYIYHUWSYD
      UXAXCVRYKYPEKUVMBRZYSYMYQQRZEKZBRZUXIUUEYKUUQUVGUVQUVPUWBUWAUXJUXMMUVRUVH
      UVEUVJUWKUWHYPYMYQBUUPDQUULESUWLUUTGUVSXNXOYKYBUVGUVQUWIUXIUXJMUWDUVHUVEU
      WJABDEYPYMFGHXEWOYKUUBUXLYSBYKUUAUXKEYKYQYMUXBUXCXPXCXQXRXAWRXRXS $.

    $( TODO - Shorten using ~ qqhghm ! $)
    $( The ` QQHom ` homomorphism is a ring homomorphism if the target
       structure is a field.  If the target structure is a division ring, it is
       a group homomorphism, but not a ring homomorphism, because it does not
       preserve the ring multiplication operation.  (Contributed by Thierry
       Arnoux, 29-Oct-2017.) $)
    qqhrhm $p |- ( ( R e. Field /\ ( chr ` R ) = 0 )
                                       -> ( QQHom ` R ) e. ( Q RingHom R ) ) $=
      ( wcel cfv wceq cq caddc cmul eqid co cz fveq2d syl13anc vx vy cfield cc0
      cchr wa cplusg cmulr c1 cqqh cur qrngbas cvv qex ccnfld cnfldmul ressmulr
      qrng1 ax-mp cdr crg qdrng drngrng mp1i ccrg isfld simplbi adantr syl qqh1
      sylan cv cnumer cdenom cui simprbi ad2antrr cress crh zrhrhm zzsbase rhmf
      wf 3syl qnumcl ad2antrl ffvelrnd wne simplr jca cn qdencl nnzd nnne0d c0g
      elzrhunit syl12anc rdivmuldivd cdiv qeqnumdivden qqhvq eqtrd oveq12d zcnd
      ad2antll zmulcld mulne0d zzsmulr rhmmul syl3anc 3eqtrd 3eqtr4rd ressplusg
      divmuldivd cnfldadd qqhf unitmulcl eqeltrd dvrdir divadddivd zaddcld cghm
      rhmghm w3a zzsplusg ghmlin oveq1d rhmdvd syl132anc mulcomd oveq2d 3eqtr4d
      isrhmd ) DUCJZDUEKUDLZUFZUAUBMANDUGKZCDODUHKZUIDUJKZDUKKZCIULCIURYTPMUMJZ
      OCUHKLUNMUOCOUMIUPUQUSYRPZCUTJCVAJYPCIVBCVCVDYPDUTJZDVAJZYNUUCYOYNUUCDVEJ
      ZDVFZVGZVHDVCZVIZYNUUCYOUIYSKYTLUUGABDEFGHVJVKYPUAVLZMJZUBVLZMJZUFZUFZUUJ
      VMKZEKZUUJVNKZEKZBQZUULVMKZEKZUULVNKZEKZBQZYRQUUQUVBYRQZUUSUVDYRQZBQZUUJY
      SKZUULYSKZYRQUUJUULOQZYSKZUUOABYQDYRDVOKZUVDUUQUUSUVBFUVMPZYQPZGUUBYNUUEY
      OUUNYNUUCUUEUUFVPVQUUORAUUPEYPRAEWCZUUNYPUUDEUORVRQZDVSQJZUVPUUIDEUVQUVQP
      ZHVTZRAUVQDEUVQUVSWAZFWBWDVHZUUKUUPRJZYPUUMUUJWEWFZWGUUOUUCYOUFZUURRJZUUR
      UDWHZUUSUVMJZUUOUUCYOYNUUCYOUUNUUGVQZYNYOUUNWIWJZUUOUURUUKUURWKJYPUUMUUJW
      LWFZWMZUUOUURUWKWNZADEUURDWOKZFHUWNPZWPWQZUUORAUVAEUWBUUMUVARJZYPUUKUULWE
      XEZWGUUOUWEUVCRJZUVCUDWHZUVDUVMJZUWJUUOUVCUUMUVCWKJYPUUKUULWLXEZWMZUUOUVC
      UXBWNZADEUVCUWNFHUWOWPWQZWRUUOUVIUUTUVJUVEYRUUOUVIUUPUURWSQZYSKZUUTUUKUVI
      UXGLYPUUMUUKUUJUXFYSUUJWTZSWFZUUOUWEUWCUWFUWGUXGUUTLUWJUWDUWLUWMABDEUUPUU
      RFGHXATZXBUUOUVJUVAUVCWSQZYSKZUVEUUMUVJUXLLYPUUKUUMUULUXKYSUULWTZSXEZUUOU
      WEUWQUWSUWTUXLUVELUWJUWRUXCUXDABDEUVAUVCFGHXATZXBXCUUOUVLUUPUVAOQZUURUVCO
      QZWSQZYSKZUXPEKZUXQEKZBQZUVHUUOUVKUXRYSUUOUVKUXFUXKOQUXRUUOUUJUXFUULUXKOU
      UKUUJUXFLYPUUMUXHWFZUUMUULUXKLYPUUKUXMXEZXCUUOUUPUURUVAUVCUUOUUPUWDXDZUUO
      UURUWLXDZUUOUVAUWRXDZUUOUVCUXCXDZUWMUXDXNXBSUUOUWEUXPRJUXQRJZUXQUDWHZUXSU
      YBLUWJUUOUUPUVAUWDUWRXFUUOUURUVCUWLUXCXFZUUOUURUVCUYFUYHUWMUXDXGZABDEUXPU
      XQFGHXATUUOUXTUVFUYAUVGBUUOUVRUWCUWQUXTUVFLUUOUUDUVRUUOUUCUUDUWIUUHVIZUVT
      VIZUWDUWRUUPUVAUVQDOYRERUWAUVQUVSXHZUUBXIXJUUOUVRUWFUWSUYAUVGLUYNUWLUXCUU
      RUVCUVQDOYRERUWAUYOUUBXIXJZXCXKXLFUUANCUGKLUNMNUOCUMIXOXMUSUVOYNUUCYOMAYS
      WCUUGABDEFGHXPVKUUOUUPUVCOQZEKZUVAUUROQZEKZYQQZUYABQZUYRUYABQZUYTUYABQZYQ
      QZUUJUULNQZYSKZUVIUVJYQQUUOUUDUYRAJUYTAJUYAUVMJVUBVUELUYMUUORAUYQEUWBUUOU
      UPUVCUWDUXCXFZWGUUORAUYSEUWBUUOUVAUURUWRUWLXFZWGUUOUYAUVGUVMUYPUUOUUDUWHU
      XAUVGUVMJUYMUWPUXEDYRUVMUUSUVDUVNUUBXQXJXRABYQDUVMUYRUYTUYAFUVNUVOGXSTUUO
      VUGUYQUYSNQZUXQWSQZYSKZVUJEKZUYABQZVUBUUOVUFVUKYSUUOVUFUXFUXKNQVUKUUOUUJU
      XFUULUXKNUYCUYDXCUUOUUPUURUVAUVCUYEUYFUYGUYHUWMUXDXTXBSUUOUWEVUJRJUYIUYJV
      ULVUNLUWJUUOUYQUYSVUHVUIYAUYKUYLABDEVUJUXQFGHXATUUOEUVQDYBQJZUYQRJZUYSRJZ
      VUNVUBLUUOUVRVUOUYNUVQDEYCVIVUHVUIVUOVUPVUQYDVUMVUAUYABNYQUVQDUYQEUYSRUWA
      UVQUVSYEUVOYFYGXJXKUUOUVIVUCUVJVUDYQUUOUVIUXGUUTVUCUXIUXJUUOUVRUWCUWFUWSU
      WHUXAUUTVUCLUYNUWDUWLUXCUWPUXEUUPUURUVCBUVQDOUVMERUVNUWAGUYOYHYIXKUUOUVJU
      XLVUDUXNUUOUVEUYTUVCUUROQZEKZBQZUXLVUDUUOUVRUWQUWSUWFUXAUWHUVEVUTLUYNUWRU
      XCUWLUXEUWPUVAUVCUURBUVQDOUVMERUVNUWAGUYOYHYIUXOUUOUYAVUSUYTBUUOUXQVUREUU
      OUURUVCUYFUYHYJSYKYLXBXCYLYM $.
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
      cn wne nnne0 3syl absdivd czrh cdvr simpl1 sseldi simpl3 qqhvval syl21anc
      inss2 cbs cnzr cui inss1 drngnzr crg ccnfld crh wf drngrng zrhrhm zzsbase
      cress rhmf 4syl ffvelrnd c0g elzrhunit syl22anc nmdvr simpl2 zhmnrg zrhnm
      nnzd syl31anc oveq12d 3eqtrrd ) BGHUCZIZDUAIZBUBJKLZUDZAUEIZMZANJZAUFJZAU
      GJZOPZNJZXCNJZXDNJZOPZABUHJJZCJZXAWTXBXFLWSWTUIZWTAXENAUJQRXAXCXDXAXCXAWT
      XCSIZXLAUKRZULXAXDXAWTXDUOIZXLAUMZRZUNXAWTXOXDKUPZXLXPXDUQURZUSXAXKXCBUTJ
      ZJZXDXTJZBVAJZPZCJZYACJZYBCJZOPZXIXABHIZWRWTXKYELXAWOHBGHVGWPWQWRWTVBZVCZ
      WPWQWRWTVDZXLYIWRMWTMXJYDCBVHJZYCABXTYMTZYCTZXTTZVEQVFXABGIZBVIIZYAYMIYBB
      VJJZIZYEYHLXAWOGBGHVKYJVCZXAYIYRYKBVLRZXASYMXCXTXAYIBVMIXTVNSVTPZBVOPISYM
      XTVPYKBVQBXTUUCUUCTZYPVRSYMUUCBXTUUCUUDVSYNWAWBXNWCXAYIWRXDSIZXRYTYKYLXAX
      DXQWKZXSYMBXTXDBWDJZYNYPUUGTWEWFYAYBYCBYSCYMYNEYSTYOWGWFXAYFXGYGXHOXAWQDG
      IZYRXMYFXGLWPWQWRWTWHZXAYQUUHUUABDFWIRZUUBXNYMBXTXCCDYNEFYPWJWLXAWQUUHYRU
      UEYGXHLUUIUUJUUBUUFYMBXTXDCDYNEFYPWJWLWMWNWN $.
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
      cnm cc sseldi cneg 0cn cnmetdval mpan df-neg fveq2i a1i absneg 3eqtr2d cz
      syl zssq sselii ovresd qqhnm adantlr 3eqtr4d ad2antrr ffvelrnd cngp inss1
      0z csg nrgngp ngpdsr syl3anc c0g qqh0 oveq2d cgrp ngpgrp grpsubid1 fveq2d
      eqtrd 3eqtrd eqtr4d breq1d biimpd ralrimiva imbi1d ralbidv rspcev cxmt wb
      breq2 cress cvv cnfldxms qex ressxms mp2an eqeltri qrngbas ax-mp xmsxmet2
      cxme mp1i 3syl xmstopn ctmd ctgp cnfldds ressds ngpxms mpbir2and eleqtrrd
      reseq1i metcnp fveq1d cghm csubg cnfldtgp csubrg qsubdrg simpli subrgsubg
      subgtgp tgptmd ctrg nrgtrg trgtmd2 qqhghm ghmcnp mpbid simprd ) BKLUCZMZE
      UDMZBUENOPZUFZOQMZBUGNZCDUHRMZUVIUVKOCDUIRZNZMZUVJUVLUJZUVIUVKOCBUKNZBULN
      ZUVRUMUNZUONZUIRZNZUVNUVIUVKUWBMZQUVRUVKUPZOJUQZURUSUTZQQUMZUNZRZUAUQZVAV
      BZOUVKNZUWEUVKNZUVSRZUBUQZVAVBZVDZJQVCZUAVEVFZUBVEVCZUVIBLMZUVHUWDUVFUVGU
      XAUVHUVELBKLVGVHVIZUVFUVGUVHVJZUVRBVKNZBBVLNZUVRSZUXDSZUXESZVMVNZUVIUWSUB
      VEUVIUWOVEMZUJZUXJUWIUWOVAVBZUWPVDZJQVCZUWSUVIUXJVOUXKUXMJQUXKUWEQMZUJZUX
      LUWPUXPUWIUWNUWOVAUXPUWIUWMBVQNZNZUWNUXPOUWEUWFRZUWEURNZUWIUXRUXPUWEVRMZU
      XSUXTPUXPQVRUWEVPUXKUXOVOZVSUYAUXSOUWEUSRZURNZUWEVTZURNZUXTOVRMUYAUXSUYDP
      WAOUWEUWFUWFSWBWCUYFUYDPUYAUYEUYCURUWEWDWEWFUWEWGWHWJUXPOUWEUWFQUVJUXPWIQ
      OWKXAWLZWFZUYBWMUVIUXOUXRUXTPUXJUWEBUXQEUXQSZHWNWOWPUXPUWNUWLUWMUVQRZUWMU
      WLBXBNZRZUXQNZUXRUXPUWLUWMUVQUVRUXPQUVROUVKUVIUWDUXJUXOUXIWQZUYHWRZUXPQUV
      RUWEUVKUYNUYBWRZWMUXPBWSMZUWLUVRMUWMUVRMZUYJUYMPUXPBKMZUYQUVIUYSUXJUXOUVF
      UVGUYSUVHUVEKBKLWTVHZVIZWQBXCZWJZUYOUYPUWLUWMUVQBUYKUXQUVRUYIUXFUYKSZUVQS
      ZXDXEUXPUYLUWMUXQUXPUYLUWMBXFNZUYKRZUWMUXPUWLVUFUWMUYKUXPUXAUVHUWLVUFPUVI
      UXAUXJUXOUXBWQUVIUVHUXJUXOUXCWQUVRUXDBUXEUXFUXGUXHXGVNXHUXPBXIMZUYRVUGUWM
      PUXPUYQVUHVUCBXJWJUYPUVRBUYKUWMVUFUXFVUFSVUDXKVNXMXLXNXOXPXQXRUWRUXNUAUWO
      VEUWJUWOPZUWQUXMJQVUIUWKUXLUWPUWJUWOUWIVAYDXSXTYAVNXRUVIUWHQYBNMZUVSUVRYB
      NMZUVJUWCUWDUWTUJYCAYOMZVUJUVIATQYERZYOFTYOMQYFMZVUMYOMYGYHQTYFYIYJYKZUWF
      AQAFYLZVUNUWFAUKNZPYHQUWFTAYFFUUAUUBYMZYNYPUVIBYOMZVUKUVFUVGVUSUVHUVFUYSU
      YQVUSUYTVUBBUUCYQVIZUVQBUVRUXFVUEYNWJUVJUVIUYGWFUBUAJUWHUVSOUVKCUVTQUVRVU
      LCUWHUONPVUOUWHCAQGVUPUWFVUQUWGVURUUFYRYMUVTSUUGXEUUDUVIOUVMUWAUVIDUVTCUI
      UVIVUSDUVTPVUTUVSDBUVRIUXFUVSSYRWJXHUUHUUEUVIAYSMZBYSMZUVKABUUIRMZUVOUVPY
      CAYTMZVVAUVITYTMQTUUJNMZVVDUUKQTUULNMZVVEVVFVUMLMUUMUUNQTUUOYMQTAFUUPYJAU
      UQYPUVIUYSBUURMVVBVUABUUSBUUTYQUVIUXAUVHVVCUXBUXCUVRUXDABUXEUXFUXGUXHFUVA
      VNOUVKABCDQVUPGIUVBXEUVCUVD $.
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
      cucn wbr cds wi wral crp wrex wa cdr cchr cc0 wceq cdvr czrh eqid syl2anc
      qqhf simpr simplr ovresd cc qsscn sseldi cnmetdval eqtrd abssub ffvelrnda
      eqtr4d adantr csg cnm cngp cnrg nrgngp syl ad2antrr ngpdsr syl3anc ccnfld
      csubg csubrg cress qsubdrg simpli subrgsubg ax-mp cnfldsub subgsub mp3an1
      fveq2d cghm simpll qqhghm qrngbas ghmsub eqtr2d cnlm elin sylanbrc qsubcl
      jca cin qqhnm syl31anc 3eqtrd breq1d biimpd ralrimiva imbi1d 2ralbidv wne
      breq2 c0 ne0i a1i 4syl cxmt cpsmet cxme cvv xmsxmet2 xmetpsmet cuss crest
      qex 3eqtri rspcev cz 0z zq crg cur drngrng rngidcl cnfldxms ressxms mp2an
      eqeltri cnfldds ressds ngpxms metucn mpbird fveq2i cnflduss oveq1i cnxmet
      mp1i ressuss wss restmetu mp3an oveq1d eleqtrrd ) ADUEQZUFUGUHZRRUIZUJZUK
      QZFUOSZEFUOSAUVIUVNTRBUVIULZUAUMZUBUMZUVLSZUCUMZUNUPZUVPUVIQZUVQUVIQZDUQQ
      ZBBUIUJZSZUDUMZUNUPZURZUBRUSUARUSZUCUTVAZUDUTUSZVBAUVOUWKADVCTZDVDQVEVFZU
      VONPBDVGQZDDVHQZHUWNVIZUWOVIZVKVJZAUWJUDUTAUWFUTTZVBUWSUVRUWFUNUPZUWGURZU
      BRUSZUARUSZUWJAUWSVLAUXCUWSAUXBUARAUVPRTZVBZUXAUBRUXEUVQRTZVBZUWTUWGUXGUV
      RUWEUWFUNUXGUVRUVQUVPUGSZUFQZUWEUXGUVRUVPUVQUGSUFQZUXIUXGUVRUVPUVQUVJSZUX
      JUXGUVPUVQUVJRAUXDUXFVMZUXEUXFVLZVNUXGUVPVOTZUVQVOTZUXKUXJVFUXGRVOUVPVPUX
      LVQZUXGRVOUVQVPUXMVQZUVPUVQUVJUVJVIVRVJVSUXGUXOUXNUXIUXJVFUXQUXPUVQUVPVTV
      JWBUXGUWEUWAUWBUWCSZUXIUXGUWAUWBUWCBUXEUWABTZUXFARBUVPUVIUWRWAWCZUXERBUVQ
      UVIAUVOUXDUWRWCWAZVNUXGUXRUWBUWADWDQZSZDWEQZQZUXHUVIQZUYDQZUXIUXGDWFTZUXS
      UWBBTUXRUYEVFAUYHUXDUXFADWGTZUYHMDWHZWIWJUXTUYAUWAUWBUWCDUYBUYDBUYDVIZHUY
      BVIZUWCVIZWKWLUXGUYCUYFUYDUXGUYFUVQUVPCWDQZSZUVIQZUYCUXGUXHUYOUVIUXGUXFUX
      DVBZUXHUYOVFZUXGUXFUXDUXMUXLXOZRWMWNQTZUXFUXDUYRRWMWOQTZUYTVUAWMRWPSZVCTW
      QWRRWMWSWTRWMCUGUYNUVQUVPXAIUYNVIZXBXCWIXDUXGUVICDXESTZUXFUXDUYPUYCVFUXGA
      VUDAUXDUXFXFAUWLUWMVUDNPBUWNCDUWOHUWPUWQIXGVJWIUXMUXLRCDUVQUVIUYNUYBUVPCI
      XHZVUCUYLXIWLXJXDUXGDWGVCXPTZGXKTZUWMUXHRTZUYGUXIVFAVUFUXDUXFAUYIUWLVUFMN
      DWGVCXLXMWJAVUGUXDUXFOWJAUWMUXDUXFPWJUXGUYQVUHUYSUVQUVPXNWIUXHDUYDGUYKLXQ
      XRXSVSWBXTYAYBYBWCUWIUXCUCUWFUTUVSUWFVFZUWHUXAUAUBRRVUIUVTUWTUWGUVSUWFUVR
      UNYFYCYDUUAVJYBXOAUAUBUVLUWDUVMUVIFRBUCUDUVMVIKRYGYEZAVERTZVUJVEUUBTVUKUU
      CVEUUDWTRVEYHWTZYIAUWLDUUETDUUFQZBTBYGYENDUUGBDVUMHVUMVIUUHBVUMYHYJAUVLRY
      KQTZUVLRYLQTCYMTVUNACVUBYMIWMYMTRYNTZVUBYMTUUIYSRWMYNUUJUUKUULUVJCRVUEVUO
      UVJCUQQVFYSRUVJWMCYNIUUMUUNWTYOUVBUVLRYPWIAUWDBYKQTZUWDBYLQTAUYIUYHDYMTVU
      PMUYJDUUOUWCDBHUYMYOYJUWDBYPWIUUPUUQAEUVMFUOEUVMVFAEWMYQQZUVKYRSZUVJUKQZU
      VKYRSZUVMECYQQVUBYQQZVURJCVUBYQIUURVUOVVAVURVFYSRYNWMUVCWTYTVUQVUSUVKYRVU
      QVUQVIUUSUUTVUJUVJVOYLQTZRVOUVDVUTUVMVFVULUVJVOYKQTVVBUVAUVJVOYPWTVPRUVJV
      OUVEUVFYTYIUVGUVH $.
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
      crn ctg eqcomi a1i syl6eqr oveq12d fveq12d df-rrh fvex syl ) ADHAIHAJKALK
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
      ( cfv wcel crrh cqqh ccnext co ccn ctps wceq cxme cnrg cngp nrgngp ngpxms
      3syl xmstps syl rrhval cq ccnfld cr cress cuss eqid rebase cioo crn ctopn
      ctg tgioo3 3eqtri cvv wss reex qssre ressabs mp2an eqcomi fveq2i cnfldtps
      resstps a1i cusp ccusp recusp cuspusp ax-mp cmopn xmstopn xmsxmet methaus
      cha cxmt eqeltrd cmetu cucn czlm cres cnlm syl5eqelr qqhucn eqcomd oveq2d
      cds cxp eleqtrd ccl fveq1i qdensere eqtri ucnextcn ) ADUASZDUBSZEFUCUDSZE
      FUEUDADUFTZXJXLUGADUHTZXMADUITDUJTXNNDUKDULUMZDUNUOZDEFUFIKUPUOAUQURUSUTU
      DZVASZURUQUTUDZVASZDVASZXKEFXQDUSBXQXQVBZVCJEVDVEVGSZXQVFSZYDIYDYDVBZVHYE
      VIKXRVBXSXQUQUTUDZVAYFXSUSVJTZUQUSVKZYFXSUGVLVMUSUQURVJVNVOVPVQYAVBXQUFTZ
      AURUFTYGYIVRVLUSURVJVSVOVTXQWATZAXQWBTYJXQYBWCXQWDWEVTXPQAFCWFSZWJAXNFYKU
      GXOCFDBKJHWGUOAXNCBWKSTYKWJTXOCDBJHWHCYKBYKVBWIUMWLYHAVMVTAXKXTCWMSZWNUDX
      TYAWNUDABXSDXTYLDWOSZJXSVBXTVBCDXBSBBXCWPWMHVQYMVBNMAYMGWQLOWRPWSAYLYAXTW
      NAYAYLRWTXAXDUQEXESZSZUSUGAYOUQYCXESZSUSUQYNYPEYCXEIVQXFXGXHVTXIWL $.

    $( If the topology of ` R ` is Hausdorff, Cauchy sequences have at most one
       limit, i.e. the canonical homomorphism of ` RR ` into ` R ` is a
       function.  (Contributed by Thierry Arnoux, 2-Nov-2017.) $)
    rrhf $p |- ( ph -> ( RRHom ` R ) : RR --> B ) $=
      ( cr wcel crrh cfv wf cuni cioo crn ctg ccn eqid rrhcn uniretop cnf eqidd
      co syl ctps wceq cxme cnrg cngp nrgngp ngpxms xmstps tpsuni feq23d mpbird
      3syl ) ASBDUAUBZUCSFUDZVHUCZAVHUEUFUGUBZFUHUNTVJABCDVKFGHVKUIJKLMNOPQRUJV
      HVKFSVIUKVIUIULUOASBSVIVHASUMADUPTZBVIUQADURTZVLADUSTDUTTVMNDVADVBVGDVCUO
      BFDJKVDUOVEVF $.
  $}

  $( Define the class of extensions of ` RR ` . This is a shorthand.  
     (Contributed by Thierry Arnoux, 2-May-2018.) $)
  df-rrext $a |- RRExt = { r e. ( NrmRing i^i DivRing ) | 
     ( ( ( ZMod ` r ) e. NrmMod /\ ( chr ` r ) = 0 ) /\ ( r e. CUnifSp
     /\ ( UnifSt ` r ) = ( metUnif ` ( ( dist ` r ) 
     |` ( ( Base ` r ) X. ( Base ` r ) ) ) ) ) ) } $.
     
  ${
    $d r D $.  $d r R $.  $d r Z $. 
    isrrext.b $e |- B = ( Base ` R ) $.
    isrrext.v $e |- D = ( ( dist ` R ) |` ( B X. B ) ) $.
    isrrext.z $e |- Z = ( ZMod ` R ) $.
    $( Express the property " ` R ` is an extension of ` RR ` ". (Contributed
       by Thierry Arnoux, 2-May-2018.) $) 
    isrrext $p |- ( R e. RRExt <-> ( ( R e. NrmRing /\ R e. DivRing ) /\ 
      ( Z e. NrmMod /\ ( chr ` R ) = 0 ) /\ ( R e. CUnifSp
      /\ ( UnifSt ` R ) = ( metUnif ` D ) ) ) ) $=
      ( vr cnrg cdr wcel cnlm cchr cfv cc0 wceq wa ccusp cuss fveq2 crrext elin
      cin cmetu w3a anbi1i cv czlm cds cbs eleq1d eleq1i syl6bbr eqeq1d anbi12d
      cres eleq1 syl6eqr xpeq12d reseq12d fveq2d eqeq12d df-rrext elrab2 3anass
      cxp 3bitr4i ) CIJUCZKZDLKZCMNZOPZQZCRKZCSNZBUDNZPZQZQZQCIKCJKQZVSQCUAKVTV
      MVRUEVIVTVSCIJUBUFHUGZUHNZLKZWAMNZOPZQZWARKZWASNZWAUINZWAUJNZWJVFZUPZUDNZ
      PZQZQVSHCVHUAWACPZWFVMWOVRWPWCVJWEVLWPWCCUHNZLKVJWPWBWQLWACUHTUKDWQLGULUM
      WPWDVKOWACMTUNUOWPWGVNWNVQWACRUQWPWHVOWMVPWACSTWPWLBUDWPWLCUINZAAVFZUPBWP
      WIWRWKWSWACUITWPWJAWJAWPWJCUJNAWACUJTEURZWTUSUTFURVAVBUOUOHVCVDVTVMVRVEVG
      $.
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

  ${
    $( The field of the real numbers is an extension of the real numbers. 
       (Contributed by Thierry Arnoux, 2-May-2018.) $)
    rerrext $p |- ( CCfld |`s RR ) e. RRExt $=
      ( ccnfld cr cress co crrext wcel cnrg cdr wa czlm cfv cnlm cchr cc0 ccusp
      wceq cuss resubdrg eqid pm3.2i cds cxp cmetu csubrg cnnrg simpli subrgnrg
      cres mp2an simpri cofld reofld ofldchr ax-mp recusp reust rebase mpbir3an
      rezh isrrext ) ABCDZEFVAGFZVAHFZIVAJKZLFZVAMKNPZIVAOFZVAQKVAUAKBBUBUHZUCK
      PZIVBVCAGFBAUDKFZVBUEVJVCRUFBAVAVASZUGUIVJVCRUJTVEVFVAVKUSVAUKFVFVAVKULVA
      UMUNTVGVIVAVKUOVAVKUPTBVHVAVDVAVKUQVHSVDSUTUR $.
  $}

  ${
    $( The field of the complex numbers is an extension of the real numbers.
       (Contributed by Thierry Arnoux, 2-May-2018.) $)
    cnrrext $p |- CCfld e. RRExt $=
      ( ccnfld crrext wcel cnrg cdr wa czlm cfv cnlm cchr cc0 wceq ccusp pm3.2i
      cr ax-mp eqid eqtr3i cc cres cuss cabs cmin ccom cmetu cnnrg cndrng cress
      cnzh co csubrg resubdrg simpli subrgchr reofld ofldchr cnfldcusp cnflduss
      cofld cnfldbas cxp cds wfn cme wf cnmet metf mp2b fnresdm cnfldds reseq1i
      ffn isrrext mpbir3an ) ABCADCZAECZFAGHZICZAJHZKLZFAMCZAUAHZUBUCUDZUEHLZFV
      OVPUFUGNVRVTUIAOUHUJZJHZVSKOAUKHCZWFVSLWGWEECULUMOAUNPWEUSCWFKLWEWEQUOWEU
      PPRNWAWDUQWBWBQURNSWCAVQUTWCSSVAZTZWCAVBHZWHTWCWHVCZWIWCLWCSVDHCWHOWCVEWK
      VFWCSVGWHOWCVLVHWHWCVIPWCWJWHVJVKRVQQVMVN $.
  $}

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

$(
  @{
    @( The ` RRHom ` homomorphism leaves rational numbers unchanged.
       (Contributed by Thierry Arnoux, 27-Mar-2018.) @)
    rrhqima @p |- ( ( R e. RRExt /\ Q e. QQ ) -> 
      ( ( RRHom ` R ) ` Q ) = ( ( QQHom ` R ) ` Q ) ) @=
      ? @.

    @( The canonical homomorphism from the real numbers to any complete
       field is a monoid homomorphism. @)
    rrhmhm @p |- ( R e. RRExt
      -> ( RRHom ` R ) e. ( ( CCfld |`s RR ) MndHom R ) ) @=
      ? @.
  @}
$)
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
      cvv cima eqidd fveq12d syl6eqr imaeq1d ifeq12d mpteq12dv xrex mptex fvmpt
      df-xrh syl ) CFKCUFKCUALAMAUBZNKZUSCOLZLZUSUCPZBDLZBELZQZQZUDZPCFUEJCAMUT
      USJUBZOLZLZVCVJNUGZVIRLZLZVLVISLZLZQZQZUDVHUFUAVICPZAMVRMVGVSMUHVSUTVKVBV
      QVFVSUSUSVJVAVICOTZVSUSUHUIVSVCVNVDVPVEVSVLBVMDVSVMCRLDVICRTIUJVSVLVANUGB
      VSVJVANVTUKGUJZUIVSVLBVOEVSVOCSLEVICSTHUJWAUIULULUMAJUQAMVGUNUOUPUR $.
  $}

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
             Canonical embeddings into the ordered field of the real numbers
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $( The ` ZRHom ` homomorphism for the real number structure is the
       identity.  (Contributed by Thierry Arnoux, 31-Oct-2017.) $)
    zrhre $p |- ( ZRHom ` ( CCfld |`s RR ) ) = ( _I |` ZZ ) $=
      ( vn ccnfld cr cress co czrh cfv cz cv c1 cmg cmpt cid cres cdr wcel wceq
      crg csubrg eqid resubdrg simpri drngrng re1r zrhval2 mp2b cmul 1re remulg
      mpan2 zre ax-1rid syl eqtrd mpteq2ia mptresid 3eqtri ) BCDEZFGZAHAIZJURKG
      ZEZLZAHUTLMHNUROPZURRPUSVCQCBSGPVDUAUBURUCURVAJAUSBHDEZVETUSTVATURURTZUDU
      EUFAHVBUTUTHPZVBUTJUGEZUTVGJCPVBVHQUHJURUTVFUIUJVGUTCPVHUTQUTUKUTULUMUNUO
      AHUPUQ $.
  $}

  ${
    $( The ` QQHom ` homomorphism for the real number structure is the
       identity.  (Contributed by Thierry Arnoux, 31-Oct-2017.) $)
    qqhre $p |- ( QQHom ` ( CCfld |`s RR ) ) = ( _I |` QQ ) $=
      ( vq ccnfld cr co cfv cq cmpt cid cres wceq wcel cc0 cz wf1 ax-mp wb eqid
      zrhre mp2b cdiv cress cqqh cv wtru wf cdr cchr csubrg resubdrg simpri crg
      drngrng czrh wss wf1o f1oi f1of1 zssre f1ss mp2an f1eq1 mpbir rebase re0g
      zrhchr mpbiri cdvr qqhf a1i feqmptd cnumer cdenom qqhvval mpanl12 wne f1f
      trud qnumcl ffvelrnd qdencl nnzd wa anim1i ccnv cima zrhf1ker mpbi eleq2i
      csn wfn fniniseg fvex elsnc 3bitr3ri sylibr nnne0d adantr neneqd pm2.65da
      ffn neneqad redvr syl3anc fveq1i fvresi syl5eq qeqnumdivden eqtr4d 3eqtrd
      syl oveq12d mpteq2ia mptresid 3eqtri ) BCUADZUBEZAFAUCZXPEZGZAFXQGHFIXPXS
      JUDAFCXPFCXPUEZUDXOUFKZXOUGELJZXTCBUHEKYAUIUJZYAXOUKKZYBYCXOULZYDYBMCXOUM
      EZNZYGMCHMIZNZMMYHNZMCUNYIMMYHUOYJMUPMMYHUQOURMMCYHUSUTYFYHJYGYIPRMCYFYHV
      AOVBZCXOYFLXOXOQZVCZYFQZXOYLVDZVEVFSZCXOVGEZXOYFYMYQQZYNVHUTVIVJVQAFXRXQX
      QFKZXRXQVKEZYFEZXQVLEZYFEZYQDZUUAUUCTDZXQYAYBYSXRUUDJYCYPCYQXQXOYFYMYRYNV
      MVNYSUUACKUUCCKUUCLVOUUDUUEJYSMCYTYFMCYFUEZYSYGUUFYKMCYFVPOZVIZXQVRZVSYSM
      CUUBYFUUHYSUUBXQVTZWAZVSYSUUCLYSUUCLJZUUBLJZYSUULWBZUUBMKZUULWBZUUMYSUUOU
      ULUUKWCUUBYFWDLWIZWEZKZUUBUUQKUUPUUMUURUUQUUBYGUURUUQJZYKYAYDYGUUTPYCYECX
      OYFLYMYNYOWFSWGWHUUFYFMWJUUSUUPPUUGMCYFWTMLUUBYFWKSUUBLXQVLWLWMWNWOUUNUUB
      LYSUUBLVOUULYSUUBUUJWPWQWRWSXAUUAUUCXOYLXBXCYSUUEYTUUBTDXQYSUUAYTUUCUUBTY
      SYTMKZUUAYTJUUIUVAUUAYTYHEYTYTYFYHRXDMYTXEXFXJYSUUOUUCUUBJUUKUUOUUCUUBYHE
      UUBUUBYFYHRXDMUUBXEXFXJXKXQXGXHXIXLAFXMXN $.
  $}

  ${
    $d a b x $.  $d x y $.  $d x z $.
    $( The ` RRHom ` homomorphism for the real numbers structure is the
       identity.  (Contributed by Thierry Arnoux, 22-Oct-2017.) $)
    rrhre $p |- ( RRHom ` ( CCfld |`s RR ) ) = ( _I |` RR ) $=
      ( va vb cr co cfv cid cres wceq wtru cq uniretop wcel a1i retop ax-mp wss
      eqid qssre mp2an cvv ccnfld cress crrh cioo crn ctg cha rehaus crrext ccn
      vx rerrext ctopn tgioo3 rrhcne mp1i ctopon ctop toptopon mpbi idcn ccnext
      wf wf1o f1oi f1of fss ccl qdensere cv csn cnei crest cflf c0 cima wrex wi
      wne wral wa cin simplr simpr opnneip syl3anc fvex qex elrestr mp3an12 syl
      inss2 resiima inss1 eqsstri imaeq2 sseq1d syl2anc ex ralrimiva ancli cfil
      rspcev wb eleq2i biimpri trnei mpbid mp3an13 mpbird ne0i adantl creg cusp
      isflf ccusp recusp cuspusp uspreg resabs1 cnrest cnextfres trud cqqh ccms
      eqeltrri recms elexi rrhval qqhre fveq2i eqtri reseq1i 3eqtr4i hauseqcn )
      UACUBDZUCEZFCGZHIJYQYRUDUEUFEZYSCKYSUGLZIUHMZYPUILYQYSYSUJDZLIULYPYSYSYSQ
      ZYPUMEZUUDQUNZUOUPYRUUBLZIYSCUQELZUUFYSURLZUUGNYSCKUSUTZYSCVAOZMYQJGZYRJG
      ZHIFJGZYSYSVBDZEZJGZUUMUUKUULUUPUUMHIUKJCCUUMYSYSKKUUHINMUUAJCUUMVCZIJJUU
      MVCZJCPZUUQJJUUMVDUURJVEJJUUMVFORJJCUUMVGSZMUUSIRMZJYSVHEEZCHIVIMZUKVJZCL
      ZUUMYSUVDVKZYSVLEZEZJVMDZVNDEZVOVSZIUVEUVDUVJLZUVKUVEUVLUVEUVDAVJZLZUUMBV
      JZVPZUVMPZBUVIVQZVRZAYSVTZWAZUVEUVTUVEUVSAYSUVEUVMYSLZWAZUVNUVRUWCUVNWAZU
      VMJWBZUVILZUUMUWEVPZUVMPZUVRUWDUVMUVHLZUWFUWDUUHUWBUVNUWIUUHUWDNMUVEUWBUV
      NWCUWCUVNWDUVDYSUVMWEWFUVHTLJTLUWIUWFUVFUVGWGWHUVMJUVHTTWIWJWKUWHUWDUWGUW
      EUVMUWEJPUWGUWEHUVMJWLJUWEWMOUVMJWNWOMUVQUWHBUWEUVIUVOUWEHUVPUWGUVMUVOUWE
      UUMWPWQXCWRWSWTXAUVEUVIJXBELZUVLUWAXDZUVEUVDUVBLZUWJUWLUVEUVBCUVDVIXEXFUU
      GUUSUVEUWLUWJXDUUIRJUVDYSCXGWJXHUUGUWJUUQUWKUUIUUTUVDAUUMYSUVICJBXOXIWKXJ
      UVJUVDXKWKXLYSXMLZIYPXNLZYTUWMYPXPLUWNYPYPQZXQYPXROUHYSYPUUEXSSMUUMYSJVMD
      YSUJDZLIUULUUMUWPUUSUULUUMHRFJCXTOZUUFUUSUULUWPLUUJRJYRYSYSCKYASYFMYBYCYQ
      UUOJYQYPYDEZUUNEZUUOYPTLYQUWSHYPYEYPUWOYGYHYPYSYSTUUCUUEYIOUWRUUMUUNYJYKY
      LYMUWQYNMUVAUVCYOYC $.
  $}
