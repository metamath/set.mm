$[ set-main.mm $]
$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Mathbox for ML
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Miscellaneous
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Move class substitution in and out of ` recs ` .  (Contributed by ML,
     25-Oct-2020.) $)
  csbrecsg $p |- ( A e. V -> [_ A / x ]_ recs ( F ) =
                                         recs ( [_ A / x ]_ F ) ) $=
    ( wcel con0 cep cwrecs csb crecs csbwrecsg wceq csbconstg wrecseq1 wrecseq2
    syl 3eqtrd df-recs csbeq2i 3eqtr4g ) BDEZABFGCHZIZFGABCIZHZABCJZIUDJUAUCABF
    IZABGIZUDHZUGGUDHZUEABFGCDKUAUHGLUIUJLABGDMUGUHGUDNPUAUGFLUJUELABFDMUGFGUDO
    PQABUFUBCRSUDRT $.

  ${
    $d A g $.  $d F g $.  $d I g $.  $d V g $.  $d g x $.
    $( Move class substitution in and out of the recursive function generator.
       (Contributed by ML, 25-Oct-2020.) $)
    csbrdgg $p |- ( A e. V -> [_ A / x ]_ rec ( F , I ) =
                   rec ( [_ A / x ]_ F , [_ A / x ]_ I ) ) $=
      ( vg cvv wceq cuni cfv cif cmpt crecs csb crdg wsbc sbcg csbconstg eqtrid
      csbif wcel cv c0 cdm wlim crn csbrecsg csbmpt2 csbfv12 ifbieq12d ifbieq2d
      fveq2d mpteq2dv eqtrd recseq syl df-rdg csbeq2i 3eqtr4g ) BEUAZABFGFUBZUC
      HZDVAUDZUEZVAUFIZVCIVAJZCJZKZKZLZMZNZFGVBABDNZVDVEVFABCNZJZKZKZLZMZABCDOZ
      NVNVMOUTVLABVJNZMZVSABVJEUGUTWAVRHWBVSHUTWAFGABVINZLVRAFBEGVIUHUTFGWCVQUT
      WCVBABPZVMABVHNZKVQVBABDVHTUTWDVBWEVPVMVBABEQUTWEVDABPZABVENZABVGNZKVPVDA
      BVEVGTUTWFVDWGWHVEVOVDABEQABVEERUTWHABVFNZVNJVOABVFCUIUTWIVFVNABVFERULSUJ
      SUKSUMUNWAVRUOUPUNABVTVKFCDUQURFVNVMUQUS $.
  $}

  ${
    $d A c d $.  $d A c y $.  $d A c z $.  $d V c d $.  $d V c y $.
    $d V c z $.  $d c ph $.  $d c d x $.  $d x y $.  $d x z $.
    $( Move class substitution in and out of class abstractions of nested
       ordered pairs.  (Contributed by ML, 25-Oct-2020.) $)
    csboprabg $p |- ( A e. V -> [_ A / x ]_ { <. <. y , z >. , d >. | ph }
                             = { <. <. y , z >. , d >. | [. A / x ]. ph } ) $=
      ( vc cv cop wa wex cab csb wsbc coprab sbcex2 bitrid exbidv df-oprab wcel
      wceq csbab sbcan sbcg anbi1d abbidv eqtrid csbeq2i 3eqtr4g ) EFUAZBEHICID
      IJGIJUBZAKZGLZDLZCLZHMZNZULABEOZKZGLZDLZCLZHMZBEACDGPZNUSCDGPUKURUPBEOZHM
      VDUPBHEUCUKVFVCHVFUOBEOZCLUKVCUOCBEQUKVGVBCVGUNBEOZDLUKVBUNDBEQUKVHVADVHU
      MBEOZGLUKVAUMGBEQUKVIUTGVIULBEOZUSKUKUTULABEUDUKVJULUSULBEFUEUFRSRSRSRUGU
      HBEVEUQACDGHTUIUSCDGHTUJ $.
  $}

  ${
    $d A d y $.  $d A d z $.  $d D d $.  $d V d y $.  $d V d z $.  $d Y d $.
    $d Z d $.  $d d x y $.  $d x z $.
    $( Move class substitution in and out of maps-to notation for operations.
       (Contributed by ML, 25-Oct-2020.) $)
    csbmpo123 $p |- ( A e. V -> [_ A / x ]_ ( y e. Y , z e. Z |-> D )
           = ( y e. [_ A / x ]_ Y , z e. [_ A / x ]_ Z |-> [_ A / x ]_ D ) ) $=
      ( vd wcel cv wa wceq coprab csb cmpo wsbc sbcan sbcel12 bitrid csboprabg
      csbconstg eleq1d anbi12d sbceq2g oprabbidv eqtrd df-mpo csbeq2i 3eqtr4g )
      DFJZADBKZGJZCKZHJZLZIKZEMZLZBCINZOZULADGOZJZUNADHOZJZLZUQADEOZMZLZBCINZAD
      BCGHEPZOBCVBVDVGPUKVAUSADQZBCINVJUSABCDFIUAUKVLVIBCIVLUPADQZURADQZLUKVIUP
      URADRUKVMVFVNVHVMUMADQZUOADQZLUKVFUMUOADRUKVOVCVPVEVOADULOZVBJUKVCADULGSU
      KVQULVBADULFUBUCTVPADUNOZVDJUKVEADUNHSUKVRUNVDADUNFUBUCTUDTADUQEFUEUDTUFU
      GADVKUTBCIGHEUHUIBCIVBVDVGUHUJ $.
  $}

  ${
    con1bii2.1 $e |- ( -. ph <-> ps ) $.
    $( A contraposition inference.  (Contributed by ML, 18-Oct-2020.) $)
    con1bii2 $p |- ( ph <-> -. ps ) $=
      ( wn con1bii bicomi ) BDAABCEF $.
  $}

  ${
    con2bii2.1 $e |- ( ph <-> -. ps ) $.
    $( A contraposition inference.  (Contributed by ML, 18-Oct-2020.) $)
    con2bii2 $p |- ( -. ph <-> ps ) $=
      ( wn con2bii bicomi ) BADABCEF $.
  $}

  ${
    $d A x $.
    vtoclefex.1 $e |- F/ x ph $.
    vtoclefex.3 $e |- ( x = A -> ph ) $.
    $( Implicit substitution of a class for a setvar variable.  (Contributed by
       ML, 17-Oct-2020.) $)
    vtoclefex $p |- ( A e. V -> ph ) $=
      ( wcel wnf cv wceq wi wal ax-gen vtoclegft mp3an23 ) CDGABHBICJAKZBLAEPBF
      MABCDNO $.
  $}

  ${
    $d A u $.  $d u x $.
    $( The range of a function mapping to singletons.  (Contributed by ML,
       15-Jul-2020.) $)
    rnmptsn $p |- ran ( x e. A |-> { x } ) = { u | E. x e. A u = { x } } $=
      ( cv wcel csn wceq copab crn wex cab cmpt wrex rnopab df-mpt rneqi df-rex
      wa abbii 3eqtr4i ) ADZCEBDUAFZGZRZABHZIUDAJZBKACUBLZIUCACMZBKUDABNUGUEABC
      UBOPUHUFBUCACQST $.
  $}

  ${
    f1omptsn.f $e |- F = ( x e. A |-> { x } ) $.
    f1omptsn.r $e |- R = { u | E. x e. A u = { x } } $.
    ${
      $d A x u $.  $d A x y $.  $d F x y $.  $d R u x $.
      $( This is the core of the proof of ~ f1omptsn , but to avoid the
         distinct variables on the definitions, we split this proof into two.
         (Contributed by ML, 15-Jul-2020.) $)
      f1omptsnlem $p |- F : A -1-1-onto-> R $=
        ( vy crn wf1o cv cfv wceq wi wcel wsbc cvv wb ax-mp wa wf1 wf wral eqid
        csn vsnex eqsbc1 mpbir sbcel2 csbconstg eleq2i bitri wrex eqabri df-rex
        csb wex sylbbr 19.23bi sbcth sbcimg sbcan sbcel1v 3imtr3i sylanbr mpan2
        mpbi fmpti fvmpt2 mpdan sneq fvmpt3i eqeqan12d vex sneqbg bitrdi biimpd
        rgen2 dff13 mpbir2an f1f1orn cmpt cab rnmptsn rneqi 3eqtr4i f1oeq3 ) CE
        IZEJZCDEJZCDEUAZWIWKCDEUBAKZELZHKZELZMZWLWNMZNZHCUCACUCACDWLUEZEFWLCOZB
        KZWSMZBWSPZWSDOZXCWSWSMZWSUDWSQOZXCXERAUFZBWSWSQUGSUHWTWTBWSPZXCXDXHWLB
        WSCUPZOWTBWSWLCUIXICWLXFXICMXGBWSCQUJSUKULWTXBTZBWSPZXADOZBWSPZXHXCTXDX
        JXLNZBWSPZXKXMNZXFXOXGXNBWSQXJXLAXLXBACUMZXJAUQXQBDGUNXBACUOURUSUTSXFXO
        XPRXGXJXLBWSQVASVGWTXBBWSVBBWSDVCVDVEVFZVHWRAHCCWTWNCOZTZWPWQXTWPWSWNUE
        ZMZWQWTXSWMWSWOYAWTXDWMWSMXRACWSDEFVIVJAWNWSYACEWLWNVKFXGVLVMWLQOYBWQRA
        VNWLWNQVOSVPVQVRAHCDEVSVTCDEWASWHDMWIWJRACWSWBZIXQBWCWHDABCWDEYCFWEGWFW
        HDCEWGSVG $.
    $}

    $d A a u x z $.
    $( A function mapping to singletons is bijective onto a set of singletons.
       (Contributed by ML, 16-Jul-2020.) $)
    f1omptsn $p |- F : A -1-1-onto-> R $=
      ( va vz wf1o cv csn cmpt wceq wrex cab eqcomi wb eqtri ax-mp sneq cbvmptv
      id eqeqan12d cbvrexdva cbvabv f1omptsnlem f1oeq3 mpbir f1oeq1 ) CDEJZCDHC
      HKZLZMZJZUOCIKZUMNZHCOZIPZUNJZABCUSUNACAKZLZMZUNAHCVBUMVAULUAZUBZQBKZVBNZ
      ACOZBPZUSVHURBIVFUPNZVGUQAHCVJVAULNVFUPVBUMVJUCVDUDUEUFZQUGDUSNUOUTRDVIUS
      GVKSDUSCUNUHTUIEUNNUKUOREVCUNFVESCDEUNUJTUI $.
  $}

  ${
    mptsnun.f $e |- F = ( x e. A |-> { x } ) $.
    mptsnun.r $e |- R = { u | E. x e. A u = { x } } $.
    ${
      $d A u x $.  $d B u x z $.  $d F x $.
      $( This is the core of the proof of ~ mptsnun , but to avoid the distinct
         variables on the definitions, we split this proof into two.
         (Contributed by ML, 16-Jul-2020.) $)
      mptsnunlem $p |- ( B C_ A -> B = U. ( F " B ) ) $=
        ( vz cv wcel wceq wa wex wb sylbi wi wsbc cvv ax-mp cima cuni wrex cres
        wss csn cab crn df-ima cmpt reseq1i resmpt eqtrid rnmptsn eqtrdi unieqd
        rneqd eleq2d eleq1w eluniab r19.41v df-rex 3bitr2i anbi2d adantr anim2i
        ancom eleq2 ibi eximi an12 exbii exsimpr syl exlimiv velsn anbi2i sylib
        biimparc vtoclga equid wsb eqid vsnex sbcg eqsbc1 adantl biimpri expcom
        19.23bi sylbir sylbird sbcth sbcimg mpbi sbcan nfab1 nfuni nfcri sbcgfi
        nfv nfim 3imtr3i syl2anbr mpan2 biimtrrid mpbidi com12 sbimi equsb3 sbv
        impbii bitrdi eqrdv eqcomd ) DCUEZFDUAZUBZDXPAXRDXPAJZXRKXSBJZXSUFZLZAD
        UCZBUGZUBZKZXSDKZXPXRYEXSXPXQYDXPXQFDUDZUHZYDFDUIXPYIADYAUJZUHYDXPYHYJX
        PYHACYAUJZDUDYJFYKDGUKACDYAULUMUQABDUNUOUMUPURYFYGIJZDKZYGIXSYEIADUSZYL
        YEKZYGYLXSLZMZANZYMYOYGYLYAKZMZANZYRYOYLXTKZYCMZBNZUUAYCBYLUTZUUCUUABUU
        CYGYBYSMZMZANZUUAUUCYGYBUUBMZMZANZUUHUUCYCUUBMUUIADUCUUKUUBYCVGYBUUBADV
        AUUIADVBVCUUJUUGAUUIUUFYGUUIUUFYBUUIUUFOUUBYBUUBYSYBXTYAYLVHZVDVEVIVFVJ
        PUUHYBYTMZANUUAUUGUUMAYGYBYSVKVLYBYTAVMPVNVOPYTYQAYSYPYGIXSVPZVQVLVRYQY
        MAYPYMYGYNVSVOVNVTXSXSLZYGYFQZAWAYPIAWBUUPIAWBUUOUUPYPUUPIAYGYPYFYPYOYF
        YGYPYSYGYOUUNYGYAYALZYSYOQZYAWCYGYGBYARZYBBYARZUURUUQYASKZUUSYGOAWDZYGB
        YASWETUVAUUTUUQOUVBBYAYASWFTYGYBMZBYARZUURBYARZUUSUUTMUURUVCUURQZBYARZU
        VDUVEQZUVAUVGUVBUVFBYASUVCYSUUBYOYBUUBYSOYGUULWGUVCUUBYOQZAUVCANYCUVIYB
        ADVBUUBYCYOUUCYOBYOUUDUUEWHWJWIWKWJWLWMTUVAUVGUVHOUVBUVCUURBYASWNTWOYGY
        BBYAWPUURBYAUVBYSYOBYSBXABIYEBYDYCBWQWRWSXBWTXCXDXEXFIAYEUSXGXHXIIAAXJU
        UPIAXKXCTXLXMXNXO $.
    $}

    $d A u x $.  $d A x y $.  $d B u x $.
    $( A class ` B ` is equal to the union of the class of all singletons of
       elements of ` B ` .  (Contributed by ML, 16-Jul-2020.) $)
    mptsnun $p |- ( B C_ A -> B = U. ( F " B ) ) $=
      ( vy wss cv csn cmpt cima cuni sneq cbvmptv eqcomi mptsnunlem eqtri
      imaeq1i unieqi eqtr4di ) DCJDICIKZLZMZDNZOFDNZOABCDEUFACAKZLZMZUFAICUJUEU
      IUDPQZRHSUHUGFUFDFUKUFGULTUAUBUC $.
  $}

  ${
    dissneq.c $e |- C = { u | E. x e. A u = { x } } $.
    ${
      $d A u x y z $.  $d B x y $.  $d C x y $.
      $( This is the core of the proof of ~ dissneq , but to avoid the distinct
         variables on the definitions, we split this proof into two.
         (Contributed by ML, 16-Jul-2020.) $)
      dissneqlem $p |- ( ( C C_ B /\ B e. ( TopOn ` A ) ) -> B = ~P A ) $=
        ( vy vz wss cfv wcel wa adantl cv cuni wceq wex wrex cab crn ctopon cpw
        cpr topgele simprd velpw w3a csn cvv simp3 cmpt cima cres df-ima resmpt
        c0 rneqd eqtrid rnmptsn eqtrdi imassrn eqsstrrdi sseqtrdi sneq cbvrexvw
        eqeq2d abbii eqtri sseqtrrdi sstr expcom adantr mpd 3adant3 ssexd isset
        wi sylib mptsnun unieqd eqtrd jca sseq1 unieq anbi12d syl5ibrcom eximdv
        eqid syl3an2b 3com23 3expia wb ctg ctop topontop tgtop syl eleq2d eltg3
        bitr3d sylibrd ssrdv eqssd ) EDIZDCUAJZKZLZDCUBZXGUPCUCDIZDXHIZXFXIXJLX
        DDCUDMUEXGAXHDXGANZXHKZGNZDIZXKXMOZPZLZGQZXKDKZXDXFXLXRXDXLXFXRXLXDXKCI
        ZXFXRACUFXDXTXFUGZXMBNZHNZUHZPZHXKRBSZPZGQZXRYAYFUIKYHYAYFDXEXDXTXFUJXD
        XTYFDIZXFXDXTLZYFEIZYIXTYKXDXTYFYEHCRZBSZEXTYFHCYDUKZTZYMXTYFYNXKULZYOX
        TYPHXKYDUKZTZYFXTYPYNXKUMZTYRYNXKUNXTYSYQHCXKYDUOUQURHBXKUSUTZYNXKVAVBH
        BCUSVCEYBXKUHZPZACRZBSYMFUUCYLBUUBYEAHCXKYCPUUAYDYBXKYCVDVFVEVGVHVIMXDY
        KYIVQXTYKXDYIYFEDVJVKVLVMZVNVOGYFVPVRXDXTYHXRVQXFYJYGXQGYJXQYGYIXKYFOZP
        ZLYJYIUUFUUDXTUUFXDXTXKYPOUUEHBCXKYMYNYNWHYMWHVSXTYPYFYTVTWAMWBYGXNYIXP
        UUFXMYFDWCYGXOUUEXKXMYFWDVFWEWFWGVNVMWIWJWKXFXSXRWLXDXFXKDWMJZKXSXRXFUU
        GDXKXFDWNKUUGDPCDWODWPWQWRGXKDXEWSWTMXAXBXC $.
    $}
    $d A u x z $.  $d B z $.  $d C z $.
    $( Any topology that contains every single-point set is the discrete
       topology.  (Contributed by ML, 16-Jul-2020.) $)
    dissneq $p |- ( ( C C_ B /\ B e. ( TopOn ` A ) ) -> B = ~P A ) $=
      ( vz cv csn wceq wrex cab sneq eqeq2d cbvrexvw abbii eqtr4i dissneqlem )
      GBCDEEBHZAHZIZJZACKZBLSGHZIZJZGCKZBLFUGUCBUFUBGACUDTJUEUASUDTMNOPQR $.
  $}

  ${
    $d x ps $.
    $( Closed form of ~ exlimimd .  (Contributed by ML, 17-Jul-2020.) $)
    exlimim $p |- ( ( E. x ph /\ A. x ( ph -> ps ) ) -> ps ) $=
      ( wi wal wex nfa1 nfv sp exlimd impcom ) ABDZCEZACFBMABCLCGBCHLCIJK $.
  $}

  ${
    $d x ph $.  $d x ch $.
    exlimimd.1 $e |- ( ph -> E. x ps ) $.
    exlimimd.2 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Existential elimination rule of natural deduction.  (Contributed by ML,
       17-Jul-2020.) $)
    exlimimd $p |- ( ph -> ch ) $=
      ( imp exlimddv ) ABCDEABCFGH $.
  $}

  ${
    $d x ph $.
    $( Closed form of ~ exellimddv .  See also ~ exlimim for a more general
       theorem.  (Contributed by ML, 17-Jul-2020.) $)
    exellim $p |- ( ( E. x x e. A /\ A. x ( x e. A -> ph ) ) -> ph ) $=
      ( cv wcel wi wal wex nfa1 nfv sp exlimd impcom ) BDCEZAFZBGZNBHAPNABOBIAB
      JOBKLM $.
  $}

  ${
    $d x ph $.  $d x ps $.
    exellimddv.1 $e |- ( ph -> E. x x e. A ) $.
    exellimddv.2 $e |- ( ph -> ( x e. A -> ps ) ) $.
    $( Eliminate an antecedent when the antecedent is elementhood, deduction
       version.  See ~ exellim for the closed form, which requires the use of a
       universal quantifier.  (Contributed by ML, 17-Jul-2020.) $)
    exellimddv $p |- ( ph -> ps ) $=
      ( cv wcel wex wi wal alrimiv exellim syl2anc ) ACGDHZCIOBJZCKBEAPCFLBCDMN
      $.
  $}

  ${
    topdifinf.t $e |- T = { x e. ~P A | ( -. ( A \ x ) e. Fin \/
                                          ( x = (/) \/ x = A ) ) } $.
    $d A x $.
    $( Part of Exercise 3 of [Munkres] p. 83.  The topology of all subsets
       ` x ` of ` A ` such that the complement of ` x ` in ` A ` is infinite,
       or ` x ` is the empty set, or ` x ` is all of ` A ` , is the trivial
       topology when ` A ` is finite.  (Contributed by ML, 14-Jul-2020.) $)
    topdifinfindis $p |- ( A e. Fin -> T = { (/) , A } ) $=
      ( cfn wcel c0 cpr nfv cv cdif wn wceq wo cpw wa wi eleq1a syl wb pm4.71rd
      crab nfrab1 nfcxfr nfcv 0elpw mp1i pwidg jaod vex a1i reqabi diffi biortn
      elpr anbi2d bitr4id 3bitr4rd eqrd ) BEFZACGBHZUTAIACBAJZKEFZLVBGMZVBBMZNZ
      NZABOZUBDVGAVHUCUDAVAUEUTVFVBVHFZVFPZVBVAFZVBCFZUTVFVIUTVDVIVEGVHFVDVIQUT
      BUFGVHVBRUGUTBVHFVEVIQBEUHBVHVBRSUIUAVKVFTUTVBGBAUJUOUKUTVLVIVGPVJVGACVHD
      ULUTVFVGVIUTVCVFVGTBVBUMVCVFUNSUPUQURUS $.

    ${
      $d A u y $.  $d A x y $.  $d T u y $.  $d T x y $.
      $( This is the core of the proof of ~ topdifinffin , but to avoid the
         distinct variables on the definition, we need to split this proof into
         two.  (Contributed by ML, 17-Jul-2020.) $)
      topdifinffinlem $p |- ( T e. ( TopOn ` A ) -> A e. Fin ) $=
        ( vu vy cfn wcel wn wceq wex wa w3a wsbc cvv c0 wo eleq1 wb ax-mp nfab1
        ctopon cfv cpw cv csn wrex cab wss nfcv abid df-rex bitri eqid wi vsnex
        cdif snelpwi imbitrrid imdistani anim2i 3impb 3anass sylibr snfi mpbiri
        difinf sylan2 orcd ancoms 3impa reqabi 3ad2ant2 mpbid sbcth sbcimg mpbi
        nfv sbc3an sbcg 3anbi1i eqsbc1 3anbi2i 3bitri 3anbi3i 3imtr3i mp3an2 ex
        pm4.71d anbi1d exbidv bitrid anass exbii exsimpr sylbi biimtrdi pm5.32i
        ancom bitr4i imbitrdi syl6 ax5e ssrd dissneq sylan nfielex adantr difss
        syl elfvex difexg elpwg 3syl mpan2 0fi nsyl ad2antrl wne cin wpss vsnid
        adantl inelcm disj4 necon2abii pssned neneqd pm4.56 sylib difeq2 eleq1d
        jca notbid eqeq1 orbi12d elrab2 biantrurd bitr4id dfin4 eqeltrri biortn
        inss2 mp2an bitr4di ad2antll mtbird expcom nelneq2 eqcom sylnibr syl6an
        ssfi exellimddv pm2.65da con4i ) BGHZCBUBUCHZUUQIZUURCBUDZJZUUSEUEZFUEZ
        UFZJZFBUGZEUHZCUIUURUVAUUSEUVGCUUSEVRUVFEUAECUJUUSUVBUVGHZUVBCHZFKZUVIU
        USUVHUVEUVILZFKZUVJUUSUVHUVDCHZUVELZFKZUVLUUSUVHUVCBHZUVMLZUVELZFKZUVOU
        VHUVPUVELZFKZUUSUVSUVHUVFUWAUVFEUKUVEFBULUMUUSUVTUVRFUUSUVPUVQUVEUUSUVP
        UVMUUSUVPUVMUUSUVDUVDJZUVPUVMUVDUNUUSAUEZUVDJZUVPMZAUVDNZUVMAUVDNZUUSUW
        BUVPMZUVMUWEUVMUOZAUVDNZUWFUWGUOZUVDOHZUWJFUPZUWIAUVDOUWEUWCCHZUVMUWEUW
        CUUTHZBUWCUQZGHZIZUWCPJZUWCBJZQZQZLZUWNUWEUUSUWDUWOMZUXCUWEUUSUWDUWOLZL
        ZUXDUUSUWDUVPUXFUWDUVPLUXEUUSUWDUVPUWOUVPUWOUWDUVDUUTHUVCBURUWCUVDUUTRU
        SUTVAVBUUSUWDUWOVCVDUUSUWDUWOUXCUWOUUSUWDLZUXCUXGUXBUWOUXGUWRUXAUWDUUSU
        WCGHZUWRUWDUXHUVDGHZUVCVEZUWCUVDGRVFBUWCVGVHVIVAVJVKXJUXBACUUTDVLVDUWDU
        USUWNUVMSUVPUWCUVDCRVMVNVOTUWLUWJUWKSUWMUWEUVMAUVDOVPTVQUWFUUSUWBUVPAUV
        DNZMZUWHUWFUUSAUVDNZUWDAUVDNZUXKMUUSUXNUXKMUXLUUSUWDUVPAUVDVSUXMUUSUXNU
        XKUWLUXMUUSSUWMUUSAUVDOVTTWAUXNUWBUUSUXKUWLUXNUWBSUWMAUVDUVDOWBTWCWDUXK
        UVPUUSUWBUWLUXKUVPSUWMUVPAUVDOVTTWEUMUWLUWGUVMSUWMUVMAUVDOVTTWFWGWHWIWJ
        WKWLUVSUVPUVNLZFKUVOUVRUXOFUVPUVMUVEWMWNUVPUVNFWOWPWQUVNUVKFUVNUVEUVMLU
        VKUVMUVEWSUVEUVIUVMUVBUVDCRWRWTWNXAUVEUVIFWOXBUVIFXCXBXDFEBCUVGUVGUNXEX
        FUUSUURLZUVAIZFBUUSUVPFKUURFBXGXHUXPBUVDUQZUUTHZUVPUXRCHZIZUXQUURUXSUUS
        UURUXSUXRBUIZBUVDXIUURBOHUXROHUXSUYBSCBUBXKBUVDOXLUXRBOXMXNVFZYCUVPUXPU
        YAUVPUXPLZUXTUXRPJZUXRBJZQZUYDUYEIZUYFIZLUYGIUYDUYHUYIUUSUYHUVPUURUUSUX
        RGHZUYEUUSUXIUYJIUXJBUVDVGXOUYEUYJPGHXPUXRPGRVFXQXRUYDUXRBUVPUXRBXSUXPU
        VPUXRBUVPBUVDXTZPXSZUXRBYAZUVPUVCUVDHUYLFYBUVCBUVDYDXOUYMUYKPBUVDYEYFVD
        YGXHYHYMUYEUYFYIYJUURUXTUYGSUVPUUSUURUXTBUXRUQZGHZIZUYGQZUYGUURUXTUXSUY
        QLUYQUXBUYQAUXRUUTCUWCUXRJZUWRUYPUXAUYGUYRUWQUYOUYRUWPUYNGUWCUXRBYKYLYN
        UYRUWSUYEUWTUYFUWCUXRPYOUWCUXRBYOYPYPDYQUURUXSUYQUYCYRYSUYOUYGUYQSUYKUY
        NGBUVDYTUXIUYKUVDUIUYKGHUXJBUVDUUCUVDUYKUUMUUDUUAUYOUYGUUBTUUEUUFUUGUUH
        UXSUYALUUTCJUVAUXRUUTCUUICUUTUUJUUKUULUUNUUOUUP $.
    $}

    $d A x y $.  $d T y $.
    $( Part of Exercise 3 of [Munkres] p. 83.  The topology of all subsets
       ` x ` of ` A ` such that the complement of ` x ` in ` A ` is infinite,
       or ` x ` is the empty set, or ` x ` is all of ` A ` , is a topology only
       if ` A ` is finite.  (Contributed by ML, 17-Jul-2020.) $)
    topdifinffin $p |- ( T e. ( TopOn ` A ) -> A e. Fin ) $=
      ( vy cv cdif cfn wcel wn c0 wceq wo cpw crab difeq2 eleq1d notbid orbi12d
      eqeq1 cbvrabv eqtri topdifinffinlem ) EBCCBAFZGZHIZJZUDKLZUDBLZMZMZABNZOB
      EFZGZHIZJZUMKLZUMBLZMZMZEULODUKUTAEULUDUMLZUGUPUJUSVAUFUOVAUEUNHUDUMBPQRV
      AUHUQUIURUDUMKTUDUMBTSSUAUBUC $.

    $d A x $.
    $( Part of Exercise 3 of [Munkres] p. 83.  The topology of all subsets
       ` x ` of ` A ` such that the complement of ` x ` in ` A ` is infinite,
       or ` x ` is the empty set, or ` x ` is all of ` A ` , is a topology if
       and only if ` A ` is finite, in which case it is the trivial topology.
       (Contributed by ML, 17-Jul-2020.) $)
    topdifinf $p |- ( ( T e. ( TopOn ` A ) <-> A e. Fin ) /\
                      ( T e. ( TopOn ` A ) -> T = { (/) , A } ) ) $=
      ( ctopon cfv wcel cfn wb c0 cpr wi topdifinffin topdifinfindis indistopon
      wceq eqeltrd impbii syl pm3.2i ) CBEFZGZBHGZIUBCJBKZPZLUBUCABCDMZUCCUDUAA
      BCDNZBHOQRUBUCUEUFUGST $.
  $}

  ${
    $d A x $.
    $( Two different ways of defining the collection from Exercise 3 of
       [Munkres] p. 83.  (Contributed by ML, 18-Jul-2020.) $)
    topdifinfeq $p |- { x e. ~P A | ( -. ( A \ x ) e. Fin \/
                                ( ( A \ x ) = (/) \/ ( A \ x ) = A ) ) } =
                      { x e. ~P A | ( -. ( A \ x ) e. Fin \/
                                ( x = (/) \/ x = A ) ) } $=
      ( cv cdif cfn wcel wn c0 wceq wo cpw cin wb wss velpw sseqin2 bitri eqeq1
      sylbi wa disj3 eqcom bitr3di eqss ssdif0 bicomi anbi12i bitr4i baib orcom
      orbi12d bitrdi orbi2d bicomd rabbiia ) BACZDZEFGZUQHIZUQBIZJZJZURUPHIZUPB
      IZJZJZABKZUPVGFZVFVBVHVEVAURVHVEUTUSJVAVHVCUTVDUSVHBUPLZHIZVCUTVHVIUPIZVJ
      VCMVHUPBNZVKABOZUPBPQVIUPHRSVJBUQIUTBUPUABUQUBQUCVDVHUSVDVLBUPNZTVHUSTUPB
      UDVHVLUSVNVMVNUSBUPUEUFUGUHUIUKUTUSUJULUMUNUO $.
  $}

  ${
    $d x y z $.
    icorempo.1 $e |- F = ( [,) |` ( RR X. RR ) ) $.
    $( Closed-below, open-above intervals of reals.  (Contributed by ML,
       26-Jul-2020.) $)
    icorempo $p |- F = ( x e. RR , y e. RR |->
                         { z e. RR | ( x <_ z /\ z < y ) } ) $=
      ( cico cr cv cle wbr clt wa cxr cmpo wceq ressxr wcel cmnf wn cpnf df-ico
      cxp cres crab reseq1i wss resmpo mp2an eqtri nfv nfrab1 rabid rexr nltmnf
      wo syl renemnf neneqd jca pm4.56 sylib mnfxr xrleloe sylancl mtbird breq2
      wb notbid syl5ibrcom con2d wi pnfnlt breq1 anim2d renepnf pm4.71i xrnemnf
      im2anan9 wne anbi1i df-ne anbi2i 3bitr3i anass 3bitr2ri imbitrdi biimtrid
      pm5.61 simprbi a1i jcad imbitrrdi rabss2 ax-mp sseli eqrd mpoeq3ia 3eqtri
      impbid1 ) DFGGUBZUCZABGGAHZCHZIJZXCBHZKJZLZCMUDZNZABGGXGCGUDZNEXAABMMXHNZ
      WTUCZXIFXKWTABCUAUEGMUFZXMXLXIOPPABMMGGXHUGUHUIABGGXHXJXBGQZXEGQZLZCXHXJX
      PCUJXGCMUKXGCGUKXPXCXHQZXCXJQZXPXQXCGQZXGLXRXPXQXSXGXQXCMQZXGLZXPXSXGCMUL
      ZXPYAXTXCROZSZXCTOZSZLZLZXSXPXGYGXTXNXDYDXOXFYFXNYCXDXNXDSYCXBRIJZSXNYIXB
      RKJZXBROZUOZXNYJSZYKSZLYLSXNYMYNXNXBMQZYMXBUMZXBUNUPXNXBRXBUQURUSYJYKUTVA
      XNYORMQYIYLVGYPVBXBRVCVDVEYCXDYIXCRXBIVFVHVIVJXOXEMQZXFYFVKXEUMYQYEXFYQXF
      SYETXEKJZSXEVLYEXFYRXCTXEKVMVHVIVJUPVRVNXSXSYFLZXTYDLZYFLZYHXSYFXSXCTXCVO
      URVPXTXCRVSZLZYFLXSYEUOZYFLUUAYSUUCUUDYFXCVQVTUUCYTYFUUBYDXTXCRWAWBVTXSYE
      WHWCXTYDYFWDWEWFWGXQXGVKXPXQXTXGYBWIWJWKXGCGULWLXJXHXCXMXJXHUFPXGCGMWMWNW
      OWSWPWQWR $.
  $}

  ${
    $d x y z l $.
    $( Closed-below, open-above intervals of reals map to subsets of reals.
       (Contributed by ML, 25-Jul-2020.) $)
    icoreresf $p |- ( [,) |` ( RR X. RR ) ) : ( RR X. RR ) --> ~P RR $=
      ( vx vy vz vl cr cxp cpw cico wf wfn crn wss cxr cle clt mpbir cv wa wcel
      wrex cres rexpssxrxp df-ico ixxf ffn fnssresb mp2b wbr crab cmpo icorempo
      wb eqid rneqi wral ssrab2 reex elpw2 rgen2w wceq rnmpo eqabri simpl simpr
      r19.29d2r wi eleq1 biimparc a1i rexlimivv ex biimtrid ssrdv ax-mp eqsstri
      syl df-f mpbir2an ) EEFZEGZHVSUAZIWAVSJZWAKZVTLWBVSMMFZLZUBWDMGZHIHWDJWBW
      EULABCNOHABCUCUDWDWFHUEWDVSHUFUGPWCABEEAQZCQZNUHWHBQZOUHRZCEUIZUJZKZVTWAW
      LABCWAWAUMUKUNWKVTSZBEUOAEUOZWMVTLWNABEEWNWKELWJCEUPWKEUQURPUSWODWMVTDQZW
      MSWPWKUTZBETAETZWOWPVTSZWRDWMABDEEWKWLWLUMVAVBWOWRWSWOWRRZWNWQRZBETAETWSW
      TWNWQABEEWOWRVCWOWRVDVEXAWSABEEXAWSVFWGESWIESRWQWSWNWPWKVTVGVHVIVJVPVKVLV
      MVNVOVSVTWAVQVR $.
  $}

  ${
    $d A x y z $.  $d B x y z $.
    $( Value of the closed-below, open-above interval function on reals.
       (Contributed by ML, 26-Jul-2020.) $)
    icoreval $p |- ( ( A e. RR /\ B e. RR ) -> ( A [,) B ) =
                 { z e. RR | ( A <_ z /\ z < B ) } ) $=
      ( vx vy cr wcel wa cico cxp cres co cle wbr clt crab ovres wceq rabbidv
      cv breq1 anbi1d breq2 anbi2d eqid icorempo reex rabex ovmpo eqtr3d ) BFGC
      FGHBCIFFJKZLBCILBATZMNZULCONZHZAFPZBCFFIQDEBCFFDTZULMNZULETZONZHZAFPUPUKU
      MUTHZAFPUQBRZVAVBAFVCURUMUTUQBULMUAUBSUSCRZVBUOAFVDUTUNUMUSCULOUCUDSDEAUK
      UKUEUFUOAFUGUHUIUJ $.
  $}

  ${
    $d X a b $.  $d a b z $.
    icoreelrnab.1 $e |- I = ( [,) " ( RR X. RR ) ) $.
    $( Elementhood in the set of closed-below, open-above intervals of reals.
       (Contributed by ML, 27-Jul-2020.) $)
    icoreelrnab $p |- ( X e. I <-> E. a e. RR E. b e. RR
                       X = { z e. RR | ( a <_ z /\ z < b ) } ) $=
      ( wcel cv cico co wceq cr wrex cle wbr clt wa bitri eqeq2d 2rexbiia eqtri
      crab cxp cres crn cima df-ima eleq2i cpw wf wfn icoreresf ffn ovelrn mp2b
      wb ovres icoreval ) CBGZCDHZEHZIJZKZELMDLMZCUTAHZNOVEVAPOQALUBZKZELMDLMUS
      CUTVAILLUCZUDZJZKZELMDLMZVDUSCVIUEZGZVLBVMCBIVHUFVMFIVHUGUAUHVHLUIZVIUJVI
      VHUKVNVLUPULVHVOVIUMDELLCVIUNUORVKVCDELLUTLGVALGQZVJVBCUTVALLIUQSTRVCVGDE
      LLVPVBVFCAUTVAURSTR $.
  $}

  ${
    isbasisrelowl.1 $e |- I = ( [,) " ( RR X. RR ) ) $.
    ${
      $d I x y z $.  $d a b x z $.  $d b c x y z $.  $d c d y z $.
      $( Lemma for ~ isbasisrelowl .  (Contributed by ML, 27-Jul-2020.) $)
      isbasisrelowllem1 $p |-
       ( ( ( ( a e. RR /\ b e. RR /\
                 x = { z e. RR | ( a <_ z /\ z < b ) } ) /\
             ( c e. RR /\ d e. RR /\
                 y = { z e. RR | ( c <_ z /\ z < d ) } ) ) /\
          ( a <_ c /\ b <_ d ) ) -> ( x i^i y ) e. I ) $=
        ( cv cr wcel cle wbr wa crab wceq w3a nfv wi clt cin wex simplr1 nfrab1
        wrex simpll2 nfeq2 nf3an nfan nfcv simp3 elin eleq2 rabid bitrdi anbi1d
        wb bitrid anbi2d sylan9bb an4 anidm anbi1i bitri syl2an simprrl simprlr
        adantr simpl jca32 biimtrdi 3simpa anim12i 3expia exp4a ad2ant2r ltletr
        letr 3coml expcomd ad2ant2l jcad anim12 syl6 com23 imp31 ancrd imbitrdi
        syl8 an42 simpr jctild sylanl1 an32s mpbird expl ancomsd impbid bitr4di
        imp eqrd jca 19.8ad df-rex sylibr icoreelrnab ) EJZKLZFJZKLZAJZXHCJZMNZ
        XMXJUANZOZCKPZQZRZGJZKLZHJZKLZBJZXTXMMNZXMYBUANZOZCKPZQZRZOZXHXTMNZXJYB
        MNZOZOZXLYDUBZYEXOOZCKPZQZFKUFZGKUFZYPDLYOYAYTOZGUCUUAYOUUBGYOYAYTYAYCY
        IXSYNUDYOXKYSOZFUCYTYOUUCFYOXKYSXIXKXRYJYNUGYOCYPYRYKYNCXSYJCXIXKXRCXIC
        SXKCSCXLXQXPCKUEUHUIYAYCYICYACSYCCSCYDYHYGCKUEUHUIUJYNCSUJCYPUKYQCKUEYO
        XMYPLZXMKLZYQOZXMYRLYOUUDUUFYOUUDUUEXPYGOZOZUUFYKUUDUUHURZYNXSXRYIUUIYJ
        XIXKXRULYAYCYIULXRYIOUUDUUEXPOZUUEYGOZOZUUHXRUUDUUJXMYDLZOZYIUULUUDXMXL
        LZUUMOXRUUNXMXLYDUMXRUUOUUJUUMXRUUOXMXQLUUJXLXQXMUNXPCKUOUPUQUSYIUUMUUK
        UUJYIUUMXMYHLUUKYDYHXMUNYGCKUOUPUTVAUULUUEUUEOZUUGOUUHUUEXPUUEYGVBUUPUU
        EUUGUUEVCVDVEUPVFVIZUUHUUEYEXOUUEUUGVJUUEXPYEYFVGUUEXNXOYGVHVKVLYOYQUUE
        UUDYOYQUUEUUDYOYQOZUUEOUUDUUHYOUUEYQUUHYOUUEOYQUUHYKXIXKOZYAYCOZOZYNUUE
        YQUUHTXSUUSYJUUTXIXKXRVMYAYCYIVMVNUVAYNOZUUEOZYQUUGUUEUVCYQXNYFOZYQOZUU
        GUVCYQUVDUVAYNUUEYQUVDTZUVAYNUUEYEXNTZXOYFTZOZUVFUVAUUEYNUVIUVAUUEYLUVG
        TZYMUVHTZOYNUVITUVAUUEUVJUVKXIYAUUEUVJTXKYCXIYAOUUEYLYEXNXIYAUUEYLYEOXN
        TXHXTXMVSVOVPVQXKYCUUEUVKTXIYAXKYCUUEUVKXKYCUUERXOYMYFUUEXKYCXOYMOYFTXM
        XJYBVRVTWAVOWBWCYLUVGYMUVHWDWEWFYEXNXOYFWDWJWGWHUVEXNYEOXOYFOOUUGXNYFYE
        XOWKXNYEXOYFVBVEWIUVBUUEWLWMWNXAWOUURUUIUUEYOUUIYQUUQVIVIWPWQWRWSYQCKUO
        WTXBXCXDYSFKXEXFXCXDYTGKXEXFCDYPGFIXGXF $.
    $}

    ${
      $d a z $.  $d b z $.  $d c d x z $.  $d c d y z $.
      $( Lemma for ~ isbasisrelowl .  (Contributed by ML, 27-Jul-2020.) $)
      isbasisrelowllem2 $p |-
       ( ( ( ( a e. RR /\ b e. RR /\
                 x = { z e. RR | ( a <_ z /\ z < b ) } ) /\
             ( c e. RR /\ d e. RR /\
                 y = { z e. RR | ( c <_ z /\ z < d ) } ) ) /\
          ( a <_ c /\ d <_ b ) ) -> ( x i^i y ) e. I ) $=
        ( cv cr wcel cle wbr wa wceq w3a nfv bitri wi clt crab cin wrex simplr1
        wex simplr2 nfrab1 nfeq2 nf3an nfan nfcv simp3 elin eleq2 bitrdi anbi1d
        rabid bitrid anbi2d sylan9bb an4 anidm anbi1i an42 bicomi anbi2i syl2an
        adantr simpl simprrl simprlr jca32 biimtrdi 3simpa anim12i 3expia exp4a
        wb letr ad2ant2r ltletr 3com13 expcomd ad2ant2l jcad anim12 com23 imp31
        syl6 syl8 ancrd imbitrrdi simpr jctild sylanl1 imp an32s mpbird ancomsd
        expl impbid bitr4di eqrd jca 19.8ad df-rex sylibr icoreelrnab ) EJZKLZF
        JZKLZAJZXJCJZMNZXOXLUANZOZCKUBZPZQZGJZKLZHJZKLZBJZYBXOMNZXOYDUANZOZCKUB
        ZPZQZOZXJYBMNZYDXLMNZOZOZXNYFUCZYJPZHKUDZGKUDZYRDLYQYCYTOZGUFUUAYQUUBGY
        QYCYTYCYEYKYAYPUEYQYEYSOZHUFYTYQUUCHYQYEYSYCYEYKYAYPUGYQCYRYJYMYPCYAYLC
        XKXMXTCXKCRXMCRCXNXSXRCKUHUIUJYCYEYKCYCCRYECRCYFYJYICKUHZUIUJUKYPCRUKCY
        RULUUDYQXOYRLZXOKLZYIOZXOYJLZYQUUEUUGYQUUEUUFXPYHOZYGXQOZOZOZUUGYMUUEUU
        LVSZYPYAXTYKUUMYLXKXMXTUMYCYEYKUMXTYKOUUEUUFXROZUUGOZUULXTUUEUUNXOYFLZO
        ZYKUUOUUEXOXNLZUUPOXTUUQXOXNYFUNXTUURUUNUUPXTUURXOXSLUUNXNXSXOUOXRCKURU
        PUQUSYKUUPUUGUUNYKUUPUUHUUGYFYJXOUOYICKURZUPUTVAUUOUUFXRYIOZOZUULUUOUUF
        UUFOZUUTOUVAUUFXRUUFYIVBUVBUUFUUTUUFVCVDSUUTUUKUUFUUKUUTUUKXPYGOZYHXQOO
        ZUUTXPYHYGXQVBUUTUVDXPXQYGYHVEVFSVFVGSUPVHVIZUULUUFYGYHUUFUUKVJUUFUUIYG
        XQVKUUFXPYHUUJVLVMVNYQYIUUFUUEYQYIUUFUUEYQYIOZUUFOUUEUULYQUUFYIUULYQUUF
        OYIUULYMXKXMOZYCYEOZOZYPUUFYIUULTYAUVGYLUVHXKXMXTVOYCYEYKVOVPUVIYPOZUUF
        OZYIUUKUUFUVKYIUUTUUKUVKYIXRUVIYPUUFYIXRTZUVIYPUUFYGXPTZYHXQTZOZUVLUVIU
        UFYPUVOUVIUUFYNUVMTZYOUVNTZOYPUVOTUVIUUFUVPUVQXKYCUUFUVPTXMYEXKYCOUUFYN
        YGXPXKYCUUFYNYGOXPTXJYBXOVTVQVRWAXMYEUUFUVQTXKYCXMYEUUFUVQXMYEUUFQYHYOX
        QUUFYEXMYHYOOXQTXOYDXLWBWCWDVQWEWFYNUVMYOUVNWGWJWHYGXPYHXQWGWKWIWLUUKUV
        CXQYHOOUUTXPYHYGXQVEXPYGXQYHVBSWMUVJUUFWNWOWPWQWRUVFUUMUUFYQUUMYIUVEVIV
        IWSXAWTXBUUSXCXDXEXFYSHKXGXHXEXFYTGKXGXHCDYRGHIXIXH $.
    $}

    $d I x y z $.
    ${
      $d I a b c d x y z $.
      $( The set of closed-below, open-above intervals of reals is closed under
         finite intersection.  (Contributed by ML, 27-Jul-2020.) $)
      icoreclin $p |- ( ( x e. I /\ y e. I ) -> ( x i^i y ) e. I ) $=
        ( vc vz vd va vb cv wcel cin cle wbr clt wa cr wrex wo ex crab wceq w3a
        wi icoreelrnab isbasisrelowllem1 isbasisrelowllem2 jaod incom eqeltrrid
        ancom1s 3simpa letric anim12i anddi an4s syl2an mpjaod 3expia rexlimivv
        sylib sylbi com12 impcom ) BJZCKZAJZCKZVGVELZCKZVFVEEJZFJZMNVLGJZONPFQU
        AUBZGQREQRVHVJUDZFCVEEGDUEVNVOEGQQVKQKZVMQKZVNVOVHVPVQVNUCZVJVHVGHJZVLM
        NVLIJZONPFQUAUBZIQRHQRVRVJUDZFCVGHIDUEWAWBHIQQVSQKZVTQKZWAWBWCWDWAUCZVR
        VJWEVRPZVSVKMNZVTVMMNZPZWGVMVTMNZPZSZVJVKVSMNZWHPZWMWJPZSZWFWIVJWKWFWIV
        JABFCHIEGDUFTWFWKVJABFCHIEGDUGTUHWFWNVJWOWFWNVJVRWEWNVJVRWEPZWNPVIVEVGL
        ZCVEVGUIZBAFCEGHIDUGUJUKTWFWOVJVRWEWOVJWQWOPVIWRCWSBAFCEGHIDUFUJUKTUHWE
        WCWDPVPVQPWLWPSZVRWCWDWAULVPVQVNULWCVPWDVQWTWCVPPZWDVQPZPWGWMSZWHWJSZPW
        TXAXCXBXDVSVKUMVTVMUMUNWGWMWHWJUOVAUPUQURTUSUTVBVCUSUTVBVD $.
    $}

    $( The set of all closed-below, open-above intervals of reals form a basis.
       (Contributed by ML, 27-Jul-2020.) $)
    isbasisrelowl $p |- I e. TopBases $=
      ( vx vy vz cvv wcel cv cin wral ctb cico cr cxp cima cle clt df-ico ixxex
      imaexg ax-mp eqeltri icoreclin rgen2 fiinbas mp2an ) AFGCHDHIAGZDAJCAJAKG
      ALMMNZOZFBLFGUIFGCDEPQLCDERSLUHFTUAUBUGCDAACDABUCUDCDAFUEUF $.
  $}

  ${
    $d I x $.
    icoreunrn.1 $e |- I = ( [,) " ( RR X. RR ) ) $.
    $( The union of all closed-below, open-above intervals of reals is the set
       of reals.  (Contributed by ML, 27-Jul-2020.) $)
    icoreunrn $p |- RR = U. I $=
      ( vx cr cuni cv wcel c1 caddc cico cfv cxr rexr mpdan icoreresf eleqtrrdi
      co syl ax-mp wss cop cxp cres clt wbr peano2re ltp1 lbico1 df-ov eleqtrdi
      syl3anc wceq opelxpi fvres eleqtrrd cdm wa cpw fdmi crn wfun wf ffun mpan
      fvelrn df-ima eqtri elunii syl2anc ssriv frn eqsstri uniss unipw sseqtrdi
      cima eqssi ) DAEZCDVRCFZDGZVSVSVSHIQZUAZJDDUBZUCZKZGWEAGZVSVRGVTVSWBJKZWE
      VTVSVSWAJQZWGVTVSLGWALGZVSWAUDUEVSWHGVSMVTWADGZWIVSUFZWAMRVSUGVSWAUHUKVSW
      AJUIUJVTWBWCGZWEWGULVTWJWLWKVSWADDUMZNWBWCJUNRUOVTWBWDUPZGZWFVTWJWOWKVTWJ
      UQWBWCWNWMWCDURZWDOUSPNWOWEWDUTZAWDVAZWOWEWQGWCWPWDVBZWROWCWPWDVCSWBWDVEV
      DAJWCVPWQBJWCVFVGZPRVSWEAVHVIVJAWPTZVRDTAWQWPWTWSWQWPTOWCWPWDVKSVLXAVRWPE
      DAWPVMDVNVOSVQ $.
  $}

  ${
    istoprelowl.1 $e |- I = ( [,) " ( RR X. RR ) ) $.
    $( The set of all closed-below, open-above intervals of reals generate a
       topology on the reals.  (Contributed by ML, 27-Jul-2020.) $)
    istoprelowl $p |- ( topGen ` I ) e. ( TopOn ` RR ) $=
      ( ctb wcel ctg cfv cr ctopon isbasisrelowl cuni icoreunrn eqcomi eleqtrdi
      tgtopon fveq2i ax-mp ) ACDZAEFZGHFZDABIQRAJZHFSANTGHGTABKLOMP $.
  $}

  ${
    $d A z $.  $d B z $.  $d a b z $.
    icoreelrn.1 $e |- I = ( [,) " ( RR X. RR ) ) $.
    $( A class abstraction which is an element of the set of closed-below,
       open-above intervals of reals.  (Contributed by ML, 1-Aug-2020.) $)
    icoreelrn $p |- ( ( A e. RR /\ B e. RR ) ->
                       { z e. RR | ( A <_ z /\ z < B ) } e. I ) $=
      ( va vb cr wcel wa cico co cv cle wbr clt crab icoreval cxp cxr simpl cpw
      cima simpr wf wfun df-ico ixxf ffun mp1i cdm wss rexpssxrxp fdmi sseqtrri
      a1i elovimad eleqtrrdi eqeltrrd ) BHIZCHIZJZBCKLZBAMZNOVDCPOJAHQDABCRVBVC
      KHHSZUCDVBBCHHKUTVAUAUTVAUDTTSZTUBZKUEKUFVBFGANPKFGAUGUHZVFVGKUIUJVEKUKZU
      LVBVEVFVIUMVFVGKVHUNUOUPUQEURUS $.
  $}

  ${
    $d A y $.  $d B y $.  $d X y $.
    $( An element of an open interval is not its smallest element.
       (Contributed by ML, 2-Aug-2020.) $)
    iooelexlt $p |- ( X e. ( A (,) B ) -> E. y e. ( A (,) B ) y < X ) $=
      ( cxr wcel cioo co clt wbr cr cpnf wceq cmnf wi wa cvv adantr wb syl wrex
      cv eliooxr simpld w3o elxr wal 19.3v caddc cdiv ovex nfcv elioore readdcl
      nfre1 rehalfcld sylan2 ancoms rexrd eliooord avglt1 simprd avglt2 xrlttrd
      c2 mpbid w3a elioo1 mpbir3and jca eleq1 breq1 anbi12d imbitrrid rspe syl6
      spcimgf ax-mp sylbir expcom simpl oveq1 eleq2d adantl pnfxr elioo2 biimpd
      wn mpan rexr pnfnlt intn3an2d a1i pm2.65d pm2.21d sylbid mpd c1 peano2rem
      cmin mnflt ltm1d mnfxr mpbird 3jaoi sylbi mpcom ) BEFZDBCGHZFZAUBZDIJZAXI
      UAZXJXHCEFZDBCUCZUDXHBKFZBLMZBNMZUEXJXMOZBUFXPXSXQXRXJXPXMXJXPPZXTAUGZXMX
      TAUHBDUIHZVEUJHZQFYAXMOYBVEUJUKXTXMAYCQAYCULXLAXIUOZXKYCMZXTXKXIFZXLPZXMX
      TYGYEYCXIFZYCDIJZPXTYHYIXTYHYCEFZBYCIJZYCCIJZXTYCXPXJYCKFZXJXPDKFZYMDBCUM
      ZXPYNPYBBDUNUPUQURUSZXTBDIJZYKXJYQXPXJYQDCIJZDBCUTZUDRZXPXJYQYKSZXJXPYNUU
      AYOBDVAUQURVFXTYCDCYPXJDEFZXPXJDYOUSZRXJXNXPXJXHXNXOVBZRXTYQYIYTXPXJYQYIS
      ZXJXPYNUUEYOBDVCUQURVFZXJYRXPXJYQYRYSVBZRVDXJYHYJYKYLVGSZXPXJXHXNPUUHXOBC
      YCVHTRVIUUFVJYEYFYHXLYIXKYCXIVKXKYCDIVLVMVNXLAXIVOZVPVQVRVSVTXJXQXMXJXQPZ
      XJXMXJXQWAUUJXJDLCGHZFZXMXQXJUULSXJXQXIUUKDBLCGWBWCWDXJUULXMOXQXJUULXMXJX
      NUULWHUUDXNUULYNLDIJZYRVGZXNUULUUNLEFXNUULUUNSWELCDWFWIWGUULUUNWHZOXNUULY
      NUUODLCUMYNUUMYNYRYNUUBUUMWHDWJDWKTWLTWMWNTWORWPWQVTXJXRXMXJXRPZUUPAUGZXM
      UUPAUHDWRWTHZQFUUQXMODWRWTUKUUPXMAUURQAUURULYDUUPXKUURMZXMUUPUUSPZYGXMUUT
      YGUURXIFZUURDIJZPZUUPUVCUUSUUPUVAUVBUUPUVAUURNCGHZFZXJUVEXRXJUVEUURKFZNUU
      RIJZUURCIJZXJYNUVFYODWSTZXJUVFUVGUVIUURXATXJUURDCXJUURUVIUSUUCUUDXJDYOXBZ
      UUGVDXJXNUVEUVFUVGUVHVGSZUUDNEFXNUVKXCNCUURWFWITVIRXRUVAUVESXJXRXIUVDUURB
      NCGWBWCWDXDXJUVBXRUVJRVJRUUSYGUVCSUUPUUSYFUVAXLUVBXKUURXIVKXKUURDIVLVMWDX
      DUUITVTVQVRVSVTXEXFXG $.
  $}

  ${
    $d I a b i o x $.  $d a b x z $.  $d i x z $.
    relowlssretop.1 $e |- I = ( [,) " ( RR X. RR ) ) $.
    $( The lower limit topology on the reals is finer than the standard
       topology.  (Contributed by ML, 1-Aug-2020.) $)
    relowlssretop $p |- ( topGen ` ran (,) ) C_ ( topGen ` I ) $=
      ( vx vi vz cioo wss cv wcel wa wi cr co wceq cxr wb cmnf wbr clt adantl
      vo va vb crn ctg cfv wrex wral cxp cpw wfn ioof ffn ovelrn mp2b cpnf elxr
      w3o cle crab simpr elioore anim12ci icoreelrn syl leidd w3a elioo1 syldan
      wf rexrd biimpa simp3d cico 3anim1i elico1 syl2an biimprd syl2im icoreval
      rexr eleq2d sylibd mp3and nfrab1 nfcv iooval anbi1d pm5.32i rabid anbi12i
      nfv ad2antll anim12i anim2i 3anass sylibr simprl xrltletr sylc simprr jca
      simpl sylanbrc adantlr adantr sylan2b sylbi expr ssrd sylanl2 eleq2 sseq1
      eleqtrrd anbi12d rspcev syl12anc ancom1s c1 caddc peano2re syl2anc2 ltp1d
      expl jca32 breq2 breq1 simpll elioopnf simplbda xrltletrd mp2and biimtrid
      elrab oveq2 anbi2d imbi12d cuni cvv unirnioo ex sseq2d mpbiri impl nltmnf
      syl2anc intnand eliooord pm2.21d ancomsd mpcom 3jaoi expdimp ancoms sseq2
      nsyl impd rexbidv syl5ibrcom rexlimivv rgen rgenw iooex rnex eqtr3i tgss2
      icoreunrn mp2an raleqi bitr4i mpbir ) FUDZUEUFAUEUFGZCHZUAHZIZUVNDHZIZUVQ
      UVOGZJZDAUGZKZUAUVLUHZCLUHZUWCCLUWBUAUVLUVOUVLIZUVOUBHZUCHZFMZNZUCOUGUBOU
      GZUWBOOUIZLUJZFVJFUWKUKUWEUWJPULUWKUWLFUMUBUCOOUVOFUNUOUWIUWBUBUCOOUWFOIZ
      UWGOIZJZUWBUWIUVNUWHIZUVRUVQUWHGZJZDAUGZKZUWNUWMUWTUWNUWMUWPUWSUWNUWGLIZU
      WGUPNZUWGQNZURUWMUWPJZUWSKZUWGUQUXAUXEUXBUXCUXAUWMUWPUWSUWMUXAUWPUWSUWMUX
      AJZUWPJZUVNEHZUSRZUXHUWGSRZJZELUTZAIZUVNUXLIZUXLUWHGZUWSUXGUVNLIZUXAJZUXM
      UXFUXAUWPUXPUWMUXAVAZUVNUWFUWGVBZVCZEUVNUWGABVDVEUXGUXPUVNUVNUSRZUVNUWGSR
      ZUXNUWPUXPUXFUXSTUWPUYAUXFUWPUVNUXSVFTUXGUVNOIZUWFUVNSRZUYBUXFUWPUYCUYDUY
      BVGZUWMUXAUWNUWPUYEPUXFUWGUXRVKUWFUWGUVNVHVIVLVMUXGUXPUYAUYBVGZUVNUVNUWGV
      NMZIZUXNUXGUXQUYFUYCUYAUYBVGZUYHUXTUXPUYCUYAUYBUVNWAZVOUXQUYHUYIUXPUYCUWN
      UYHUYIPUXAUYJUWGWAZUVNUWGUVNVPVQVRVSUXGUYGUXLUVNUXGUXQUYGUXLNUXTEUVNUWGVT
      VEWBWCWDUXAUWMUWNUWPUXOUYKUWOUWPJZEUXLUWHUYLEWLUXKELWEEUWHWFUWOUWPUXHUXLI
      ZUXHUWHIZUWOUWPUYMJZJUWOUVNUYDUYBJZCOUTZIZUYMJZJUYNUWOUYOUYSUWOUWPUYRUYMU
      WOUWHUYQUVNCUWFUWGWGWBWHWIUYSUWOUYCUYPJZUXHLIZUXKJZJZUYNUYRUYTUYMVUBUYPCO
      WJUXKELWJWKUWOVUCJUXHUWFUXHSRZUXJJZEOUTZUWHUWMVUCUXHVUFIZUWNUWMVUCJZUXHOI
      ZVUEVUGVUBVUIUWMUYTVUBUXHVUAUXKXCVKZWMVUHVUDUXJVUHUWMUYCVUIVGZUYDUXIJZVUD
      VUHUWMUYCVUIJZJVUKVUCVUMUWMUYTUYCVUBVUIUYCUYPXCVUJWNWOUWMUYCVUIWPWQVUCVUL
      UWMUYTUYDVUBUXIUYCUYDUYBWRVUAUXIUXJWRWNTUWFUVNUXHWSWTVUBUXJUWMUYTVUAUXIUX
      JXAWMXBVUEEOWJXDXEUWOUWHVUFNVUCEUWFUWGWGXFXNXGXHXIXJXKUWRUXNUXOJDUXLAUVQU
      XLNUVRUXNUWQUXOUVQUXLUVNXLUVQUXLUWHXMXOXPXQXRYDUXBUWMUWPUWSUWMUXBUWPUWSUW
      MUXBJZUWPJZUXIUXHUVNXSXTMZSRZJZELUTZAIZUVNVUSIZVUSUWHGZJZUWSVUOUXPVUPLIVU
      TUWPUXPVUNUXSTUVNYAEUVNVUPABVDYBUXBUWMUWPVVCUXBUWMUWPVVCUXBUXDVVCKUWMUVNU
      WFUPFMZIZJZVVAVUSVVDGZJZKVVFVVAVVGVVFUXPUYAUVNVUPSRZJZJVVAVVFUXPUYAVVIVVE
      UXPUWMUVNUWFUPVBTZVVFUVNVVKVFVVFUVNVVKYCYEVURVVJEUVNLUXHUVNNUXIUYAVUQVVIU
      XHUVNUVNUSYFUXHUVNVUPSYGXOYNWQVVFEVUSVVDVVFEWLVURELWEEVVDWFUXHVUSIVUAVURJ
      ZVVFUXHVVDIZVURELWJVVFVVLVVMVVFVVLJZVUAVUDVVMVVFVUAVURWRZVVNUWFUVNUXHUWMV
      VEVVLYHVVNUVNVVFUXPVVLVVKXFVKVVNUXHVVOVKVVFUYDVVLUWMVVEUXPUYDUWFUVNYIYJXF
      VVLUXIVVFVUAUXIVUQWRTYKVVFVUAVUDJZVVMKZVVLUWMVVQVVEUWMVVMVVPUWFUXHYIVRXFX
      FYLUUAYMXJXBUXBUXDVVFVVCVVHUXBUWPVVEUWMUXBUWHVVDUVNUWGUPUWFFYOZWBYPUXBVVB
      VVGVVAUXBUWHVVDVUSVVRUUBYPYQUUCUUDXRUWRVVCDVUSAUVQVUSNUVRVVAUWQVVBUVQVUSU
      VNXLUVQVUSUWHXMXOXPUUFXRYDUXCUWMUWPUWSUWMUXCUWPUWSUXPUWMUXCJZUWPJZUWSUWPU
      XPVVSUXSTUXPUYCVVTUWSKUYJVVTVVSUVNUWFQFMZIZJUYCUWSVVSUWPVWBUXCUWPVWBPUWMU
      XCUWHVWAUVNUWGQUWFFYOWBTWIUYCVWBVVSUWSUYCVWBVVSUWSUYCVWBVVSUWSKUYCUYDUVNQ
      SRZJVWBUYCVWCUYDUVNUUEUUGUVNUWFQUUHUUPUUIUUQUUJYMVEUUKXRYDUULXHUUMUUNUWIU
      VPUWPUWAUWSUVOUWHUVNXLUWIUVTUWRDAUWIUVSUWQUVRUVOUWHUVQUUOYPUURYQUUSUUTXHU
      VAUVBUVMUWCCUVLYRZUHZUWDUVLYSIVWDAYRZNUVMVWEPFUVCUVDLVWDVWFYTABUVGUVECUAD
      UVLAYSUVFUVHUWCCLVWDYTUVIUVJUVK $.
  $}

  ${
    $d I a b c i o x $.  $d a b m n x z $.  $d a b c x y $.  $d c i x z $.
    relowlpssretop.1 $e |- I = ( [,) " ( RR X. RR ) ) $.
    $( The lower limit topology on the reals is strictly finer than the
       standard topology.  (Contributed by ML, 2-Aug-2020.) $)
    relowlpssretop $p |- ( topGen ` ran (,) ) C. ( topGen ` I ) $=
      ( vc vi vx wceq c2 cr wcel c1 clt wbr wn wa wsbc wi cico wb ax-mp cxr crn
      vo vz va vb vy vm vn cioo ctg cfv wpss wss wne relowlssretop 2re 1lt2 cvv
      cv co ovex sbcan 1re sbcg sbcbr123 csbvarg csbconstg breq12i breqi 3bitri
      csb anbi12i bitri sbceqg csbov123 oveq123i eqtri eqeq12i wrex simpr simpl
      wral cle leid jccir rexr elico2 sylan2 df-3an bitrdi baibd biimpar adantr
      w3a mpdan adantl mpbird cop cxp cima rexpssxrxp opelxpi sselid cdm df-ico
      cpw ixxf fdmi eleq2i wfun crab mpofun funfvima mpan sylbir syl5ibrcom imp
      eleq2 wex sylib a1i sylan rexrd con2d syl2anc annim sylnibr mpbi jca rspe
      ex rexnal cuni mp2an sbcth sbcimg sbcel1v mpbir mpbiran2 3imtr3i sylc wfn
      df-ov 3eltr4g eleq1 ioof ffn ovelrn wal iooelexlt df-rex elmpocl2 elioore
      wf simp2 biimtrdi com23 mpdi elicore xrlenlt biimpd mt2d intnand imbitrdi
      jcad eximdv exnal df-ss imnan sseq1 anbi12d mtbiri sseq2 anbi2d rexlimivv
      mpd notbid sylbi com12 ralrimiv ralnex adantlr an12 syl exp41 com4l imp41
      anbi2i ixxex imaexg eqeltri icoreunrn unirnioo eqtr3i tgss2 raleqi bitr4i
      syl2anbr eqid eqsbc1 anbi1i eqimss mto nesymir df-pss mpbir2an ) UIUAZUJU
      KZAUJUKZULUXHUXIUMUXHUXIUNABUOUXIUXHUXIUXHFUXIUXHUMZGHIZJGKLZUXJMZUPUQCUS
      ZHIZJUXNKLZNZCGOZUXMCGOZUXKUXLNZUXMUXQUXMPZCGOZUXRUXSPZUXKUYBUPUYACGHUXQD
      USZJUXNQUTZFZNZDUYEOZUXMDUYEOZUXQUXMUYGUXMPZDUYEOZUYHUYIPZUYEURIZUYKJUXNQ
      VAZUYJDUYEURUXQUXOEUSZUXNKLZNZEJOZUYDUYOUXNQUTZFZEJOZUXMUYFUYRUXOEJOZUYPE
      JOZNUXQUXOUYPEJVBVUBUXOVUCUXPJHIZVUBUXORVCUXOEJHVDSVUCEJUYOVKZEJUXNVKZEJK
      VKZLJUXNVUGLUXPEJUYOUXNKVEVUEJVUFUXNVUGVUDVUEJFVCEJHVFSZVUDVUFUXNFVCEJUXN
      HVGSZVHJUXNVUGKVUDVUGKFVCEJKHVGSVIVJVLVMVUAEJUYDVKZEJUYSVKZFZUYFVUDVUAVUL
      RVCEJUYDUYSHVNSVUJUYDVUKUYEVUDVUJUYDFVCEJUYDHVGSVUKVUEVUFEJQVKZUTUYEEJUYO
      UXNQVOVUEVUFJUXNVUMQVUHVUIVUDVUMQFVCEJQHVGSVPVQVRVMUYRVUANUYQUYTNZEJOZUXM
      UYQUYTEJVBVUNUYOHIZNZEJOZUXMEJOZVUOUXMVUQUXMPZEJOZVURVUSPZVUDVVAVCVUTEJHV
      UQUYOUYDIZUYOUBUSZIZVVDUYDUMZNZUBUXGVSZPZDAWBZEHWBZUXJVUQVVJMZEHVSZVVKMVU
      QVUPVVLVVMVUNVUPVTUXOUYPUYTVUPVVLVUPUXOUYPUYTVVLVUPUXOUYPUYTVVLVUPUXONZUY
      PNZUYTNZVVIMZDAVSZVVLVVPUYDAIZVVQNZVVRVVPVVCVVSVVHMZNZNZVVTVVPVVCVWBVVPVV
      CUYOUYSIZVVOVWDUYTVVNVWDUYPVVNVUPUYOUYOWCLZNZVWDUYPRVVNVUPVWEVUPUXOWAUYOW
      DWEVVNVWDVWFUYPVVNVWDVUPVWEUYPWNZVWFUYPNUXOVUPUXNTIZVWDVWGRUXNWFUYOUXNUYO
      WGWHVUPVWEUYPWIWJWKWOWLWMUYTVVCVWDRVVOUYDUYSUYOXRWPWQVVNUYTVWBUYPVVNUYTNV
      VSVWAVVNUYTVVSVVNVVSUYTUYSAIVVNUYOUXNWRZQUKZQHHWSZWTZUYSAVVNVWITTWSZIZVWI
      VWKIZVWJVWLIZVVNVWKVWMVWIXAUYOUXNHHXBZXCVWQVWNVWIQXDZIZVWOVWPPZVWRVWMVWIV
      WMTXFQECUCWCKQECUCXEZXGXHXIQXJVWSVWTECTTUYOUCUSZWCLVXBUXNKLNUCTXKZQVXAXLV
      WKVWIQXMXNXOUUAUYOUXNQUUCBUUDUYDUYSAUUEXPXQUYTVWAVVNUYTVVGMZUBUXGWBVWAUYT
      VXDUBUXGVVDUXGIZUYTVXDVXEVVDUDUSZUEUSZUIUTZFZUETVSUDTVSZUYTVXDPZUIVWMUUBZ
      VXEVXJRVWMHXFZUIUUNVXLUUFVWMVXMUIUUGSUDUETTVVDUIUUHSVXIVXKUDUETTVXIVXKPVX
      FTIVXGTINVXIVXDUYTVVEVVDUYSUMZNZMVXIVXOUYOVXHIZVXHUYSUMZNZVXPVXQMPVXRMVXP
      UFUSZVXHIZVXSUYSIZPZUFUUIZVXQVXPVYBMZUFXSZVYCMVXPVXTVXSUYOKLZNZUFXSZVYEVX
      PVYFUFVXHVSVYHUFVXFVXGUYOUUJVYFUFVXHUUKXTVXPVYGVYDUFVXPVYGVXTVYAMZNVYDVXP
      VYGVXTVYIVYGVXTPVXPVXTVYFWAYAVXPVYAVYGVXPVYAVYGMVXPVYANZVYFVXTVYJVYFUYOVX
      SWCLZVXPVYAVYKVXPVYAVWHVYKECTTVXCUYOUXNQVXSVXAUULVXPVWHVYAVYKVXPVWHVYAVYK
      PVXPVWHNVYAVXSHIZVYKVXSUXNKLZWNZVYKVXPVUPVWHVYAVYNRUYOVXFVXGUUMZUYOUXNVXS
      WGYBVYLVYKVYMUUOUUPYKUUQUURXQVYJUYOTIZVXSTIZVYFVYKMPVXPVYPVYAVXPUYOVYOYCW
      MVYJVXSVXPVUPVYAVYLVYOUYOUXNVXSUUSYBYCVYPVYQNZVYKVYFVYRVYKVYFMUYOVXSUUTUV
      AYDYEUVBUVCYKYDUVEVXTVYAYFUVDUVFUVPVYBUFUVGXTUFVXHUYSUVHYGVXPVXQUVIYHVXIV
      VEVXPVXNVXQVVDVXHUYOXRVVDVXHUYSUVJUVKUVLUYTVVGVXOUYTVVFVXNVVEUYDUYSVVDUVM
      UVNUVQXPYAUVOUVRUVSUVTVVGUBUXGUWAXTWPYIUWBYIVWCVVSVVCVWANZNVVTVVCVVSVWAUW
      CVYSVVQVVSVVCVVHYFUWHVMXTVVQDAYJUWDVVIDAYLXTUWEUWFUWGVVLEHYJYEVVJEHYLXTUX
      JVVJEAYMZWBZVVKAURIVYTUXGYMZFUXJWUARAVWLURBQURIVWLURIUGUHUCWCKQUGUHUCXEUW
      IQVWKURUWJSUWKHVYTWUBABUWLZUWMUWNEDUBAUXGURUWOYNVVJEHVYTWUCUWPUWQYGYOSVUD
      VVAVVBRVCVUQUXMEJHYPSYHVURVUOVUPEJOZWUDVUDVCEJHYQYRVUNVUPEJVBYSVUDVUSUXMR
      VCUXMEJHVDSYTXOUWRYOSUYMUYKUYLRUYNUYGUXMDUYEURYPSYHUYHUXQDUYEOZUYFDUYEOZN
      ZUXQUXQUYFDUYEVBWUGUXQWUFWUFUYEUYEFZUYEUWSUYMWUFWUHRUYNDUYEUYEURUWTSYRWUE
      UXQWUFUYMWUEUXQRUYNUXQDUYEURVDSUXAYSVMUYMUYIUXMRUYNUXMDUYEURVDSYTYOSUXKUY
      BUYCRUPUXQUXMCGHYPSYHUXRUXOCGOZUXPCGOZNUXTUXOUXPCGVBWUIUXKWUJUXLCGHYQWUJC
      GJVKZCGUXNVKZCGKVKZLJGWUMLUXLCGJUXNKVEWUKJWULGWUMUXKWUKJFUPCGJHVGSUXKWULG
      FUPCGHVFSVHJGWUMKUXKWUMKFUPCGKHVGSVIVJVLVMUXKUXSUXMRUPUXMCGHVDSYTYNUXIUXH
      UXBUXCUXDUXHUXIUXEUXF $.
  $}

  ${
    sucneqond.1 $e |- ( ph -> X = suc Y ) $.
    sucneqond.2 $e |- ( ph -> Y e. On ) $.
    $( Inequality of an ordinal set with its successor.  Does not use the axiom
       of regularity.  (Contributed by ML, 18-Oct-2020.) $)
    sucneqond $p |- ( ph -> X =/= Y ) $=
      ( wceq wcel csuc con0 sucidg syl eleqtrrd word onsuc eqeltrd eloni ordirr
      wn eleq1 biimprd con3d syl5com mt2d neqned ) ABCABCFZCBGZACCHZBACIGZCUGGE
      CIJKDLABBGZRZUEUFRABMZUJABIGUKABUGIDAUHUGIGECNKOBPKBQKUEUFUIUEUIUFBCBSTUA
      UBUCUD $.
  $}

  ${
    sucneqoni.1 $e |- X = suc Y $.
    sucneqoni.2 $e |- Y e. On $.
    $( Inequality of an ordinal set with its successor.  Does not use the axiom
       of regularity.  (Contributed by ML, 18-Oct-2020.) $)
    sucneqoni $p |- X =/= Y $=
      ( wne wtru csuc wceq a1i con0 wcel sucneqond mptru ) ABEFABABGHFCIBJKFDIL
      M $.
  $}

  $( If an ordinal number has a predecessor, then it is successor of that
     predecessor.  (Contributed by ML, 17-Oct-2020.) $)
  onsucuni3 $p |- ( ( B e. On /\ B =/= (/) /\ -. Lim B ) ->
                    B = suc U. B ) $=
    ( con0 wcel c0 wne wlim wn w3a cuni csuc wceq wo eloni 3ad2ant1 orduniorsuc
    word syl orcomd wa mpnanrd simp2 df-lim 3expb con3i 3ad2ant3 wi orcom df-or
    biimpri sylbb sylc ) ABCZADEZAFZGZHZAAIZJKZAUQKZLZUSGZURUPUSURUPAPZUSURLZUL
    UMVBUOAMNZAOQRUPUMUSULUMUOUAUPVBUMUSSZVDUOULVBVESZGUMVFUNVBUMUSUNUNVBUMUSHA
    UBUIUCUDUETTUTVCVAURUFURUSUGUSURUHUJUK $.

  $( The ordinal number ` 1o ` is the predecessor of the ordinal number
     ` 2o ` .  (Contributed by ML, 19-Oct-2020.) $)
  1oequni2o $p |- 1o = U. 2o $=
    ( c1o csuc c2o cuni wceq df-2o con0 wcel c0 wne wlim wn 2on 2on0 2onn nnlim
    com ax-mp onsucuni3 mp3an eqtr3i wb 1on onuni suc11 mp2an mpbi ) ABZCDZBZEZ
    AUIEZCUHUJFCGHZCIJCKLZCUJEMNCQHUNOCPRCSTUAAGHUIGHZUKULUBUCUMUOMCUDRAUIUEUFU
    G $.

  $( If an ordinal number has a predecessor, the value of the recursive
     definition generator at that number in terms of its predecessor.
     (Contributed by ML, 17-Oct-2020.) $)
  rdgsucuni $p |- ( ( B e. On /\ B =/= (/) /\ -. Lim B ) ->
         ( rec ( F , I ) ` B ) = ( F ` ( rec ( F , I ) ` U. B ) ) ) $=
    ( con0 wcel c0 wne wlim wn w3a crdg cfv cuni csuc onsucuni3 fveq2d 3ad2ant1
    wceq onuni rdgsuc syl eqtrd ) ADEZAFGZAHIZJZABCKZLAMZNZUGLZUHUGLBLZUFAUIUGA
    OPUFUHDEZUJUKRUCUDULUEASQCUHBTUAUB $.

  ${
    $d A x $.  $d B x $.  $d F x $.  $d M x $.  $d N x $.  $d X x $.
    $( If a recursive function with an initial value ` A ` at step ` N ` is
       equal to itself with an initial value ` B ` at step ` M ` , then every
       finite number of successor steps will also be equal.  (Contributed by
       ML, 21-Oct-2020.) $)
    rdgeqoa $p |- ( ( N e. On /\ M e. On /\ X e. _om ) ->
         ( ( rec ( F , A ) ` N ) = ( rec ( F , B ) ` M ) ->
             ( rec ( F , A ) ` ( N +o X ) )
           = ( rec ( F , B ) ` ( M +o X ) ) ) ) $=
      ( vx com wcel w3a cfv wceq coa co wi fveq2d c0 wsbc wa csb simp3 cv eleq1
      con0 3anbi3d oveq2 eqeq12d imbi2d imbi12d peano1 wal oa0 eqcomd eqeqan12d
      crdg biimpd biantru anbi2i 3anass bitr4i bitr4di mpbiri ax-gen sbc6g csuc
      peano2b 3anbi3i imbi1i nnon oacl anim12i 3impdir rdgsuc sylan9eqr adantrr
      ax-mp fveq2 ad2antll eqtr4d sylan2 ancoms syl3anl3 onasuc 3adant2 3adant1
      adantr 3eqtr4d ex imim2d sylbir a2i sylbi sbcimg sbc3an sbcg wb 3anbi123d
      sbcel1v bitrid sbceqg csbfv12 csbconstg csbov123 csbvarg oveq123d fveq12d
      a1i eqtrid bitrd imbitrrid findes vtoclga mpcom ) FHIZEUDIZDUDIZXNJZECAUO
      ZKZDCBUOZKZLZEFMNZXRKZDFMNZXTKZLZOZXOXPXNUAXOXPGUBZHIZJZYBEYIMNZXRKZDYIMN
      ZXTKZLZOZOZXQYHOGFHYIFLZYKXQYQYHYSYJXNXOXPYIFHUCUEYSYPYGYBYSYMYDYOYFYSYLY
      CXRYIFEMUFPYSYNYEXTYIFDMUFPUGUHUIYRGQHIZYRGQRZUJYTUUAYIQLZYROZGUKUUCGUUBY
      RXOXPSZYBEQMNZXRKZDQMNZXTKZLZOZOUUDYBUUIXOXPXSUUFYAUUHXOUUFXSXOUUEEXREULP
      UMXPUUHYAXPUUGDXTDULPUMUNUPUUBYKUUDYQUUJUUBYKXOXPYTJZUUDUUBYJYTXOXPYIQHUC
      UEUUDXOXPYTSZSUUKXPUULXOYTXPUJUQURXOXPYTUSUTVAUUBYPUUIYBUUBYMUUFYOUUHUUBY
      LUUEXRYIQEMUFPUUBYNUUGXTYIQDMUFPUGUHUIVBVCYRGQHVDVBVPYJYIVEZHIZYRYRGUUMRZ
      OYIVFZYRUUOUUNXOXPUUNJZYBEUUMMNZXRKZDUUMMNZXTKZLZOZOZYRUUQYQOUVDYKUUQYQYJ
      UUNXOXPUUPVGZVHUUQYQUVCUUQYKYQUVCOUVEYKYPUVBYBYKYPUVBYKYPSYLVEZXRKZYNVEZX
      TKZUUSUVAYJXOXPYIUDIZYPUVGUVILZYIVIYPXOXPUVJJZUVKUVLYPYLUDIZYNUDIZSZUVKXO
      UVJXPUVOXOUVJSUVMXPUVJSUVNEYIVJDYIVJVKVLYPUVOSUVGYOCKZUVIYPUVMUVGUVPLUVNU
      VMYPUVGYMCKUVPAYLCVMYMYOCVQVNVOUVNUVIUVPLYPUVMBYNCVMVRVSVTWAWBYKUUSUVGLZY
      PXOYJUVQXPXOYJSUURUVFXREYIWCPWDWFYKUVAUVILZYPXPYJUVRXOXPYJSUUTUVHXTDYIWCP
      WEWFWGWHWIWJWKWLUUNUUOYKGUUMRZYQGUUMRZOUVDYKYQGUUMHWMUUNUVSUUQUVTUVCUVSXO
      GUUMRZXPGUUMRZYJGUUMRZJUUNUUQXOXPYJGUUMWNUUNUWAXOUWBXPUWCUUNXOGUUMHWOXPGU
      UMHWOUWCUUNWPUUNGUUMHWRXGWQWSUUNUVTYBGUUMRZYPGUUMRZOUVCYBYPGUUMHWMUUNUWDY
      BUWEUVBYBGUUMHWOUUNUWEGUUMYMTZGUUMYOTZLUVBGUUMYMYOHWTUUNUWFUUSUWGUVAUUNUW
      FGUUMYLTZGUUMXRTZKUUSGUUMYLXRXAUUNUWHUURUWIXRGUUMXRHXBUUNUWHGUUMETZGUUMYI
      TZGUUMMTZNUURGUUMEYIMXCUUNUWJEUWKUUMUWLMGUUMMHXBZGUUMEHXBGUUMHXDZXEXHXFXH
      UUNUWGGUUMYNTZGUUMXTTZKUVAGUUMYNXTXAUUNUWOUUTUWPXTGUUMXTHXBUUNUWOGUUMDTZU
      WKUWLNUUTGUUMDYIMXCUUNUWQDUWKUUMUWLMUWMGUUMDHXBUWNXEXHXFXHUGXIUIXIUIXIXJW
      LXKXLXM $.
  $}

  $( Membership in a Cartesian product.  This version requires no quantifiers
     or dummy variables.  See also ~ elxp7 .  (Contributed by ML,
     19-Oct-2020.) $)
  elxp8 $p |- ( A e. ( B X. C )
                <-> ( ( 1st ` A ) e. B /\ A e. ( _V X. C ) ) ) $=
    ( cxp wcel c1st cfv cvv xp1st wss ssv ssid xpss12 mp2an sseli jca c2nd xpss
    wa adantl xp2nd anim2i elxp7 sylanbrc impbii ) ABCDZEZAFGBEZAHCDZEZSZUGUHUJ
    ABCIUFUIABHJCCJUFUIJBKCLBHCCMNOPUKAHHDZEZUHAQGCEZSUGUJUMUHUIULAHCROTUJUNUHA
    HCUAUBABCUCUDUE $.

  ${
    $d ch z $.  $d ph z $.  $d ps z $.  $d x y z $.
    cbveud.1 $e |- F/ x ph $.
    cbveud.2 $e |- F/ y ph $.
    cbveud.3 $e |- ( ph -> F/ y ps ) $.
    cbveud.4 $e |- ( ph -> F/ x ch ) $.
    cbveud.5 $e |- ( ph -> ( x = y -> ( ps <-> ch ) ) ) $.
    $( Deduction used to change bound variables in an existential uniqueness
       quantifier, using implicit substitution.  (Contributed by ML,
       27-Mar-2021.) $)
    cbveud $p |- ( ph -> ( E! x ps <-> E! y ch ) ) $=
      ( vz weq wb wal wex weu nfvd nfbid wa eu6 simpr equequ1 adantr bibi12d ex
      sylcom cbv2w exbidv 3bitr4g ) ABDKLZMZDNZKOCEKLZMZENZKOBDPCEPAULUOKAUKUND
      EFGABUJEHAUJEQRACUMDIAUMDQRADELZBCMZUKUNMZJUPUQURUPUQSBCUJUMUPUQUAUPUJUMM
      UQDEKUBUCUDUEUFUGUHBDKTCEKTUI $.
  $}

  ${
    $d A x y $.
    cbvreud.1 $e |- F/ x ph $.
    cbvreud.2 $e |- F/ y ph $.
    cbvreud.3 $e |- ( ph -> F/ y ps ) $.
    cbvreud.4 $e |- ( ph -> F/ x ch ) $.
    cbvreud.5 $e |- ( ph -> ( x = y -> ( ps <-> ch ) ) ) $.
    $( Deduction used to change bound variables in a restricted existential
       uniqueness quantifier.  (Contributed by ML, 27-Mar-2021.) $)
    cbvreud $p |- ( ph -> ( E! x e. A ps <-> E! y e. A ch ) ) $=
      ( cv wcel wa weu wreu nfvd nfand wb df-reu wceq adantl imp anbi12d cbveud
      eleq1 ex 3bitr4g ) ADLZFMZBNZDOELZFMZCNZEOBDFPCEFPAUKUNDEGHAUJBEAUJEQIRAU
      MCDAUMDQJRAUIULUAZUKUNSAUONUJUMBCUOUJUMSAUIULFUFUBAUOBCSKUCUDUGUEBDFTCEFT
      UH $.
  $}

  ${
    $d A x y $.  $d B x y $.
    $( The difference of unions is a subset of the union of the difference.
       (Contributed by ML, 29-Mar-2021.) $)
    difunieq $p |- ( U. A \ U. B ) C_ U. ( A \ B ) $=
      ( vx vy cuni cdif cv wcel wn wa wex eluni notbii wal alinexa nfa1 adantrd
      wi sp eldif ancld anass imbitrdi eximd sylbir impcom syl2anb anbi2i exbii
      bitri 3imtr4i ssriv ) CAEZBEZFZABFZEZCGZUMHZURUNHZIZJURDGZHZVBAHZVBBHZIZJ
      ZJZDKZURUOHURUQHZUSVCVDJZDKZVCVEJDKZIZVIVADURALUTVMDURBLMVNVLVIVNVCVFRZDN
      ZVLVIRVCVEDOVPVKVHDVODPVPVKVKVFJVHVPVKVFVPVCVFVDVODSQUAVCVDVFUBUCUDUEUFUG
      URUMUNTVJVCVBUPHZJZDKVIDURUPLVRVHDVQVGVCVBABTUHUIUJUKUL $.
  $}

  ${
    $( Theorem about subsets of the difference of unions.  (Contributed by ML,
       29-Mar-2021.) $)
    inunissunidif $p |- ( ( A i^i U. C ) = (/) ->
                         ( A C_ U. B <-> A C_ U. ( B \ C ) ) ) $=
      ( cuni cin wceq wss cdif reldisj difunieq sstr mpan2 biimtrdi com12 difss
      c0 unissi impbid1 ) ACDZEPFZABDZGZABCHZDZGZUBTUEUBTAUASHZGZUEASUAIUGUFUDG
      UEBCJAUFUDKLMNUEUDUAGUBUCBBCOQAUDUAKLR $.
  $}

  ${
    $d A y $.  $d B y $.  $d C y $.  $d F y $.  $d X y $.
    $( Elementhood in a recursive definition at a limit ordinal.  (Contributed
       by ML, 30-Mar-2022.) $)
    rdgellim $p |- ( ( ( B e. On /\ Lim B ) /\ C e. B ) ->
           ( X e. ( rec ( F , A ) ` C ) -> X e. ( rec ( F , A ) ` B ) ) ) $=
      ( vy con0 wcel wlim wa crdg cfv cv ciun wi wrex wceq fveq2 eleq2d rspcev
      ex eliun imbitrrdi adantl wb rdglim2a adantr sylibrd ) BGHBIJZCBHZJECDAKZ
      LZHZEFBFMZUKLZNZHZEBUKLZHZUJUMUQOUIUJUMEUOHZFBPZUQUJUMVAUTUMFCBUNCQUOULEU
      NCUKRSTUAFEBUOUBUCUDUIUSUQUEUJUIURUPEFABGDUFSUGUH $.
  $}

  ${
    $d A x $.  $d B x $.  $d C x $.  $d F x $.
    $( A recursive definition at a limit ordinal is a superset of itself at any
       smaller ordinal.  (Contributed by ML, 30-Mar-2022.) $)
    rdglimss $p |- ( ( ( B e. On /\ Lim B ) /\ C e. B ) ->
         ( rec ( F , A ) ` C ) C_ ( rec ( F , A ) ` B ) ) $=
      ( vx con0 wcel wlim wa crdg cfv cv rdgellim ssrdv ) BFGBHICBGIECDAJZKBOKA
      BCDELMN $.
  $}

  ${
    $d A w x $.  $d A x y z $.  $d F x y z $.  $d X x y $.  $d Y w x $.
    $d Y x y $.
    rdgssun.1 $e |- F = ( w e. _V |-> ( w u. B ) ) $.
    rdgssun.2 $e |- B e. _V $.
    $( In a recursive definition where each step expands on the previous one
       using a union, every previous step is a subset of every later step.
       (Contributed by ML, 1-Apr-2022.) $)
    rdgssun $p |- ( ( X e. On /\ Y e. X ) ->
                 ( rec ( F , A ) ` Y ) C_ ( rec ( F , A ) ` X ) ) $=
      ( vx vy vz con0 wcel cfv wss wi wceq c0 cvv fveq2 crdg cv wa wral nfsbc1v
      wsbc 0ex rzal sbceq1a mpbid vtoclef csuc wo vex elsuc csb cun ssun1 csbex
      fvex unex nfcv cmpt nfmpt1 nfcxfr nfrdg nffv nfcsb1 nfun ax-mp id csbeq1a
      rdgeq1 uneq12d rdgsucmptf mpan2 sseqtrrid sstr2 syl5com imim2d imp sseq1d
      syl5ibrcom adantr biimtrid ex ralimdv2 cab df-sbc sucex sseq2d raleqbi1dv
      jaod cbvabv elab2 bitri imbitrrdi wlim ciun ssiun2 rdglim2a mpan sseqtrrd
      adantl ralrimiva eleq2i abid sylibr a1d tfindes rsp syl wb eleq12 sseq12d
      eleq1 imbi12d mpbii vtocleg com12 pm2.43b ) ELMZFEMZFDBUAZNZEYDNZOZYBYCYG
      YCYBYCYGPZYCYBYHPZPIELYCIUBZEQZYIYKYIPJFEJUBZFQZYKYIYMYKUCZYJLMZYLYJMZYLY
      DNZYJYDNZOZPZPYIYOYSJYJUDZYTUUAIKUUAIRUFZIRUUAIRUEUGYJRQUUAUUBYSJYJUHUUAI
      RUIUJUKYOUUAYQYJULZYDNZOZJUUCUDZUUAIUUCUFZYOYSUUEJYJUUCYOYTYLUUCMZUUEPUUH
      YPYLYJQZUMYOYTUCZUUEYLYJJUNUOUUJYPUUEUUIYOYTYPUUEPYOYSUUEYPYOYRUUDOZYSUUE
      YOYRAYRCUPZUQZYRUUDYRUULURYOUUMSMUUDUUMQYRUULYJYDUTAYRCHUSVAABYJAUBZCUQZU
      UMYDSABVBZAYJVBZAYRUULAYJYDABDADASUUOVCZGASUUOVDVEUUPVFUUQVGZAYRCUUSVHVID
      UURQYDUURBUAQGBDUURVMVJUUNYRQZUUNYRCUULUUTVKAYRCVLVNVOVPVQZYQYRUUDVRVSVTW
      AYOUUIUUEPYTYOUUEUUIUUKUVAUUIYQYRUUDYLYJYDTWBWCWDWMWEWFWGUUGUUCUUAIWHZMUU
      FUUAIUUCWIYQKUBZYDNZOZJUVCUDZUUFKUUCUVBYJIUNWJUVEUUEJUVCUUCUVCUUCQUVDUUDY
      QUVCUUCYDTWKWLUUAUVFIKYSUVEJYJUVCYJUVCQYRUVDYQYJUVCYDTWKWLWNZWOWPWQUVCWRZ
      UUAIUVCUFZUUAIUVCUDUVHUVFUVIUVHUVEJUVCUVHYLUVCMZUCYQJUVCYQWSZUVDUVJYQUVKO
      UVHJUVCYQWTXDUVHUVDUVKQZUVJUVCSMUVHUVLKUNJBUVCSDXAXBWDXCXEUVIUVCUVFKWHZMZ
      UVFUVIUVCUVBMUVNUUAIUVCWIUVBUVMUVCUVGXFWPUVFKXGWPXHXIXJYSJYJXKXLYNYOYBYTY
      HYKYOYBXMYMYJELXPXDYNYPYCYSYGYLFYJEXNYNYQYEYRYFYMYQYEQYKYLFYDTWDYKYRYFQYM
      YJEYDTXDXOXQXQXRWFXSXTXSYAYAWA $.
  $}

  ${
    $d A u y z $.  $d A x y $.  $d B u x z $.  $d F u x $.  $d W u y $.
    exrecfnlem.1 $e |- F = ( z e. _V |-> ( z u. ran ( y e. z |-> B ) ) ) $.
    $( Lemma for ~ exrecfn .  (Contributed by ML, 30-Mar-2022.) $)
    exrecfnlem $p |- ( ( A e. V /\ A. y B e. W ) ->
                   E. x ( A C_ x /\ A. y e. x B e. x ) ) $=
      ( vu wcel com cfv wss cv wa wi wceq cvv nfcv crdg wex wal c0 rdg0g peano1
      wral con0 wlim omelon limom rdglimss mpanl12 eqsstrrdi wrex ciun rdglim2a
      ax-mp mp2an eleq2i eliun bitri csuc nnon cmpt crn cun eqid elrnmpt1 elun2
      peano2 syl fvex nfmpt1 nfrn nfun nfmpt nfcxfr nfrdg nffv rnex unex rdgeq1
      mptexgf id nfeq2 eqidd mpteq12df rneqd uneq12d rdgsucmptf mpan2 imbitrrid
      eleq2d rdgellim sylsyld expd com3r rexlimdv biimtrid alimi ralrid imbi12d
      sseq2 eleq2 albid df-ral 3bitr4g anbi12d spcev syl2an ) DGKZDLFDUAZMZNZEX
      NKZBXNUGZDAOZNZEXRKZBXRUGZPZAUBEHKZBUCZXLDUDXMMZXNDGFUEUDLKZYEXNNZUFLUHKZ
      LUIZYFYGUJUKDLUDFULUMURUNYDXPBXNYCBOZXNKZXPQZBYKYJJOZXMMZKZJLUOZYCXPYKYJJ
      LYNUPZKYPXNYQYJYHYIXNYQRUJUKJDLUHFUQUSUTJYJLYNVAVBYCYOXPJLYMLKZYOYCXPYRYO
      YCXPYRYMVCZLKZYOYCPZEYSXMMZKZXPYMVKYRYMUHKZUUAUUCQYMVDUUAUUCUUDEYNBYNEVEZ
      VFZVGZKZUUAEUUFKUUHBYNEUUEHUUEVHVIEUUFYNVJVLUUDUUBUUGEUUDUUGSKUUBUUGRYNUU
      FYMXMVMZUUEYNSKUUESKUUIBYNESBYMXMBDFBFCSCOZBUUJEVEZVFZVGZVEZIBCSUUMBSTBUU
      JUULBUUJTBUUKBUUJEVNVOVPVQVRBDTVSZBYMTVTZWDURWAWBCDYMUUMUUGXMSCDTZCYMTZCY
      NUUFCYMXMCDFCFUUNICSUUMVNVRUUQVSUURVTZCUUECBYNEUUSCETVQVOVPFUUNRXMUUNDUAR
      IDFUUNWCURUUJYNRZUUJYNUULUUFUUTWEZUUTUUKUUEUUTBUUJEYNEBUUJYNUUPWFUVAUUTEW
      GWHWIWJWKWLWNWMVLYHYIYTUUCXPQUJUKDLYSFEWOUMWPWQWRWSWTXAXBYBXOXQPAXNLXMVMX
      RXNRZXSXOYAXQXRXNDXDUVBYJXRKZXTQZBUCYLBUCYAXQUVBUVDYLBBXRXNBLXMUUOBLTVTWF
      UVBUVCYKXTXPXRXNYJXEXRXNEXEXCXFXTBXRXGXPBXNXGXHXIXJXK $.
  $}

  ${
    $d A x y z $.  $d B x z $.  $d W y $.
    $( Theorem about the existence of infinite recursive sets. ` y ` should
       usually be free in ` B ` .  (Contributed by ML, 30-Mar-2022.) $)
    exrecfn $p |- ( ( A e. V /\ A. y B e. W ) ->
                   E. x ( A C_ x /\ A. y e. x B e. x ) ) $=
      ( vz cvv cv cmpt crn cun eqid exrecfnlem ) ABGCDGHGIZBODJKLJZEFPMN $.
  $}

  ${
    $d A x y $.
    $( For any base set, a set which contains the powerset of all of its own
       elements exists.  (Contributed by ML, 30-Mar-2022.) $)
    exrecfnpw $p |- ( A e. V -> E. x ( A C_ x /\ A. y e. x ~P y e. x ) ) $=
      ( wcel cv cpw cvv wal wss wral wa wex vpwex ax-gen exrecfn mpan2 ) CDEBFG
      ZHEZBICAFZJRTEBTKLAMSBBNOABCRDHPQ $.
  $}

  ${
    $d .< x y z $.  $d A x y z $.
    $( If the Axiom of Infinity is denied, every total order is a well-order.
       The notion of a well-order cannot be usefully expressed without the
       Axiom of Infinity due to the inability to quantify over proper classes.
       (Contributed by ML, 5-Oct-2023.) $)
    finorwe $p |- ( -. _om e. _V -> ( .< Or A -> .< We A ) ) $=
      ( vx vz vy com cvv wcel wn wor wwe wa wfr cv wss c0 wne wi cfn ex wbr wal
      wral wrex simpl soss com12 adantl vex wceq fineqv biimpi eleqtrrid ancoms
      wofi sylan syl6an ssid w3a wreu wereu reurex syl mp3anr1 mpanr1 syl6 impd
      alrimiv df-fr sylibr simpr df-we sylanbrc ) FGHIZABJZABKZVNVOLZABMZVOVPVQ
      CNZAOZVSPQZLDNENBUAIDVSUCZEVSUDZRZCUBVRVQWDCVQVTWAWCVQVTVSBKZWAWCRVQVNVTV
      SBJZWEVNVOUEVOVTWFRVNVTVOWFVSABUFUGUHVNVSSHZWFWEVNVSGSCUIZVNSGUJUKULUMWFW
      GWEVSBUOUNUPUQWEWAWCWEVSVSOZWAWCVSURWEVSGHZWIWAWCWHWEWJWIWAUSLWBEVSUTWCED
      VSVSBGVAWBEVSVBVCVDVETVFVGVHCEDABVIVJVNVOVKABVLVMT $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Cartesian exponentiation
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c ^^ $.

  $( Extend the definition of a class to include Cartesian exponentiation. $)
  cfinxp $a class ( U ^^ N ) $.

  ${
    $d U n x y $.  $d N n x y $.
    $( Define Cartesian exponentiation on a class.

       Note that this definition is limited to finite exponents, since it is
       defined using nested ordered pairs.  If tuples of infinite length are
       needed, or if they might be needed in the future, use ~ df-ixp or
       ~ df-map instead.  The main advantage of this definition is that it
       integrates better with functions and relations.  For example if ` R ` is
       a subset of ` ( A ^^ 2o ) ` , then ~ df-br can be used on it, and
       ~ df-fv can also be used, and so on.

       It's also worth keeping in mind that ` ( ( U ^^ M ) X. ( U ^^ N ) ) ` is
       generally not equal to ` ( U ^^ ( M +o N ) ) ` .

       This definition is technical.  Use ~ finxp1o and ~ finxpsuc for a more
       standard recursive experience.  (Contributed by ML, 16-Oct-2020.) $)
    df-finxp $a |- ( U ^^ N ) =
                     { y | ( N e. _om /\ (/) =
                       ( rec ( ( n e. _om , x e. _V |->
                                 if ( ( n = 1o /\ x e. U ) ,
                                   (/) ,
                                   if ( x e. ( _V X. U ) ,
                                       <. U. n , ( 1st ` x ) >. ,
                                       <. n , x >. ) ) )
                         , <. N , y >. ) ` N ) ) } $.

    dffinxpf.1 $e |- F = ( n e. _om , x e. _V |->
                                 if ( ( n = 1o /\ x e. U ) ,
                                   (/) ,
                                   if ( x e. ( _V X. U ) ,
                                       <. U. n , ( 1st ` x ) >. ,
                                       <. n , x >. ) ) ) $.
    $( This theorem is the same as Definition ~ df-finxp , except that the
       large function is replaced by a class variable for brevity.
       (Contributed by ML, 24-Oct-2020.) $)
    dffinxpf $p |- ( U ^^ N ) =
                     { y | ( N e. _om /\ (/) =
                       ( rec ( F , <. N , y >. ) ` N ) ) } $=
      ( cfinxp com wcel c0 cvv cv wceq wa cfv cop cif crdg cab c1o cxp df-finxp
      cuni c1st cmpo rdgeq1 ax-mp fveq1i eqeq2i anbi2i abbii eqtr4i ) CFHFIJZKF
      DAILDMZUANAMZCJOKUPLCUBJUOUDUPUEPQUOUPQRRUFZFBMQZSZPZNZOZBTUNKFEURSZPZNZO
      ZBTABCDFUCVFVBBVEVAUNVDUTKFVCUSEUQNVCUSNGUREUQUGUHUIUJUKULUM $.
  $}

  ${
    $d U n x y $.  $d V n x y $.  $d N n x y $.  $d U n x $.
    $( Equality theorem for Cartesian exponentiation.  (Contributed by ML,
       19-Oct-2020.) $)
    finxpeq1 $p |- ( U = V -> ( U ^^ N ) = ( V ^^ N ) ) $=
      ( vn vx vy wceq com wcel c0 cvv cv wa cxp cfv cop cif cmpo crdg cab eleq2
      c1o cuni cfinxp anbi2d xpeq2 eleq2d ifbid ifbieq2d mpoeq3dv rdgeq1 fveq1d
      c1st syl eqeq2d abbidv df-finxp 3eqtr4g ) ACGZBHIZJBDEHKDLZUBGZELZAIZMZJV
      CKANZIZVAUCVCUMOPZVAVCPZQZQZRZBFLPZSZOZGZMZFTUTJBDEHKVBVCCIZMZJVCKCNZIZVH
      VIQZQZRZVMSZOZGZMZFTABUDCBUDUSVQWHFUSVPWGUTUSVOWFJUSBVNWEUSVLWDGVNWEGUSDE
      HKVKWCUSVEVSVJWBJUSVDVRVBACVCUAUEUSVGWAVHVIUSVFVTVCACKUFUGUHUIUJVMVLWDUKU
      NULUOUEUPEFADBUQEFCDBUQUR $.
  $}

  ${
    $d U n x y $.  $d M n x y $.  $d N n x y $.
    $( Equality theorem for Cartesian exponentiation.  (Contributed by ML,
       19-Oct-2020.) $)
    finxpeq2 $p |- ( M = N -> ( U ^^ M ) = ( U ^^ N ) ) $=
      ( vn vx vy wceq com wcel c0 cvv cv cfv cop cif crdg cab cfinxp df-finxp
      wa c1o cxp cuni c1st cmpo eleq1 opeq1 rdgeq2 syl id fveq12d eqeq2d abbidv
      anbi12d 3eqtr4g ) BCGZBHIZJBDEHKDLZUAGELZAITJUSKAUBIURUCUSUDMNURUSNOOUEZB
      FLZNZPZMZGZTZFQCHIZJCUTCVANZPZMZGZTZFQABRACRUPVFVLFUPUQVGVEVKBCHUFUPVDVJJ
      UPBCVCVIUPVBVHGVCVIGBCVAUGVBVHUTUHUIUPUJUKULUNUMEFADBSEFADCSUO $.
  $}

  ${
    $d A n y z $.  $d N n x y z $.  $d U n y z $.  $d V n y z $.  $d n x y z $.
    $( Distribute proper substitution through Cartesian exponentiation.
       (Contributed by ML, 25-Oct-2020.) $)
    csbfinxpg $p |- ( A e. V -> [_ A / x ]_ ( U ^^ N )
                            = ( [_ A / x ]_ U ^^ [_ A / x ]_ N ) ) $=
      ( vn vz vy wcel csb com c0 cvv wceq wa cop cif wsbc csbconstg eqtrid cuni
      cfinxp cv c1o cxp c1st cfv cmpo crdg cab df-finxp csbeq2i sbcel1g sbceq2g
      sbcan csbfv12 csbrdgg csbmpo123 csbif sbcel12 eleq1d bitrid anbi12d csbxp
      sbcg xpeq1d eleq12d mpoeq123dv eqtrd csbopg opeq2d rdgeq12 syl2anc fveq1d
      ifbieq12d eqeq2d bitrd abbidv csbab 3eqtr4g ) BEIZABCDUBZJABDKIZLDFGKMFUC
      ZUDNZGUCZCIZOZLWFMCUEZIZWDUAWFUFUGPZWDWFPZQZQZUHZDHUCZPZUIZUGZNZOZHUJZJZA
      BCJZABDJZUBZABWBXBGHCFDUKULWAXAABRZHUJXEKIZLXEFGKMWEWFXDIZOZLWFMXDUEZIZWK
      WLQZQZUHZXEWPPZUIZUGZNZOZHUJXCXFWAXGXTHXGWCABRZWTABRZOWAXTWCWTABUOWAYAXHY
      BXSABDKEUMWAYBLABWSJZNXSABLWSEUNWAYCXRLWAYCXEABWRJZUGXRABDWRUPWAXEYDXQWAY
      DABWOJZABWQJZUIZXQABWOWQEUQWAYEXONYFXPNYGXQNWAYEFGABKJZABMJZABWNJZUHXOAFG
      BWNEKMURWAFGYHYIYJKMXNABKESABMESZWAYJWHABRZABLJZABWMJZQXNWHABLWMUSWAYLXJY
      MYNLXMYLWEABRZWGABRZOWAXJWEWGABUOWAYOWEYPXIWEABEVEYPABWFJZXDIWAXIABWFCUTW
      AYQWFXDABWFESZVAVBVCVBABLESWAYNWJABRZABWKJZABWLJZQXMWJABWKWLUSWAYSXLYTUUA
      WKWLYSYQABWIJZIWAXLABWFWIUTWAYQWFUUBXKYRWAUUBYIXDUEXKABMCVDWAYIMXDYKVFTVG
      VBABWKESABWLESVOTVOTVHVIWAYFXEABWPJZPXPABDWPEVJWAUUCWPXEABWPESVKVIYFXPYEX
      OVLVMVIVNTVPVQVCVBVRXAAHBVSGHXDFXEUKVTT $.
  $}

  ${
    $d U n x $.  $d X n x $.
    $( Lemma for ` ^^ ` recursion theorems.  (Contributed by ML,
       17-Oct-2020.) $)
    finxpreclem1 $p |- ( X e. U -> (/) =
              ( ( n e. _om , x e. _V |->
                    if ( ( n = 1o /\ x e. U ) ,
                      (/) ,
                      if ( x e. ( _V X. U ) ,
                          <. U. n , ( 1st ` x ) >. ,
                          <. n , x >. ) ) )
                ` <. 1o , X >. ) ) $=
      ( wcel c1o com cvv cv wceq wa c0 cxp cuni c1st cfv cop cif cmpo a1i eqidd
      co eleq1a anim2d iftrue syl6 imp 1onn elex 0ex ovmpod df-ov eqtr3di ) DBE
      ZFDCAGHCIZFJZAIZBEZKZLUQHBMEUONUQOPQUOUQQRZRZSZUBLFDQVBPUNCAFDGHVALVBHUNV
      BUAUNUPUQDJZKZVALJZUNVDUSVEUNVCURUPDBUQUCUDUSLUTUEUFUGFGEUNUHTDBUILHEUNUJ
      TUKFDVBULUM $.
  $}

  ${
    $d U n x $.  $d X n x $.
    $( Lemma for ` ^^ ` recursion theorems.  (Contributed by ML,
       17-Oct-2020.) $)
    finxpreclem2 $p |- ( ( X e. _V /\ -. X e. U ) -> -. (/) =
              ( ( n e. _om , x e. _V |->
                    if ( ( n = 1o /\ x e. U ) ,
                      (/) ,
                      if ( x e. ( _V X. U ) ,
                          <. U. n , ( 1st ` x ) >. ,
                          <. n , x >. ) ) )
                ` <. 1o , X >. ) ) $=
      ( cvv wcel wn wa c0 c1o cop com cv wceq c1st cfv wne nfv nfcv nfim cxp wi
      cuni cif cmpo nfmpo2 nffv nfne nfmpo1 1onn elexi df-ov csb 0ex opex csbex
      co ifex eqid ovmpos mp3an13 adantr sylan9eqr adantl eleq1 notbid biimprcd
      csbeq1a pm3.14 olcs syl6 iffalse imp ifeqor vuniex fvex opnzi neii mtbiri
      wo eqeq1 vex jaoi neqned eqnetrd adantrl eqnetrrd eqnetrrid ancom2s an12s
      mp1i exp31 vtoclef vtoclefex anabsi5 necomd neneqd ) DEFZDBFZGZHZIJDKZCAL
      ECMZJNZAMZBFZHZIXEEBUAFZXCUCZXEOPZKZXCXEKZUDZUDZUEZPZXAXPIWRWTXPIQZXAXQUB
      ZADEXAXQAXAARAXPIAXBXOCALEXNUFAXBSUGAISUHTXEDNZXRUBCJXSXRCXSCRXAXQCXACRCX
      PICXBXOCALEXNUICXBSUGCISUHTTJLUJUKXDXSXAXQWRXDXSHZWTXQWRWTXTXQWRWTXTHZHZX
      PJDXOUQZIJDXOULYBYCCJADXNUMZUMZIWRYCYENZYAJLFWRYEEFYFUJCJYDADXNXGIXMUNXHX
      KXLXIXJUOXCXEUOURURUPUPCAJDLEXNXOEXOUSUTVAVBYAYEIQWRYAXNYEIXTXNYENWTXSXDX
      NYDYEADXNVHCJYDVHVCVDWTXSXNIQXDWTXSHZXNXMIWTXSXNXMNZWTXSXGGZYHWTXSXFGZYIX
      SYJWTXSXFWSXEDBVEVFVGXDGYJYIXDXFVIVJVKXGIXMVLVKVMYGXMIXMXKNZXMXLNZVTXMINZ
      GZYGXHXKXLVNYKYNYLYKYMXKINXKIXIXJCVOXEOVPVQVRXMXKIWAVSYLYMXLINXLIXCXECWBA
      WBVQVRXMXLIWAVSWCWKWDWEWFWGVDWEWHWIWJWLWMWNWOWPWQ $.
  $}

  ${
    $d U n x y $.
    $( The value of Cartesian exponentiation at zero.  (Contributed by ML,
       24-Oct-2020.) $)
    finxp0 $p |- ( U ^^ (/) ) = (/) $=
      ( vy vn vx c0 cfinxp cv wcel cop wceq 0ex vex opnzi nesymi com cvv c1o wa
      cfv cif cxp cuni c1st cmpo crdg peano1 df-finxp eqabri mpbiran opex bitri
      rdg0 eqeq2i mtbir nel0 ) BAEFZBGZUPHZEEUQIZJZUSEEUQKBLMNUREECDOPCGZQJDGZA
      HREVBPAUAHVAUBVBUCSIVAVBITTUDZUSUESZJZUTUREOHZVEUFVFVERBUPDBACEUGUHUIVDUS
      EUSVCEUQUJULUMUKUNUO $.
  $}

  ${
    $d U n x y $.
    $( The value of Cartesian exponentiation at one.  (Contributed by ML,
       17-Oct-2020.) $)
    finxp1o $p |- ( U ^^ 1o ) = U $=
      ( vy vn vx c1o cv wcel com c0 cvv wceq wa cuni cfv cop cif 1onn wn fveq2i
      eqtri cfinxp cxp c1st cmpo crdg a1i finxpreclem1 con0 wne 1on nnlim ax-mp
      wlim rdgsucuni mp3an csuc df-1o unieqi 0elon onunisuci opex rdg0 df-finxp
      1n0 eqtr4di eqabri sylanbrc mpbiran vex eqcomi finxpreclem2 neqned necomd
      eqnetrrid neneqd mpan con4i sylbi impbii eqriv ) AAEUAZBAWABFZAGZWBWAGZWC
      EHGZIECDHJCFZEKDFZAGLIWGJAUBGWFMWGUCNOWFWGOPPUDZEWBOZUEZNZKZWDWEWCQUFWCIW
      IWHNZWKDACWBUGWKEMZWJNZWHNZWMEUHGEIUIEUMRZWKWPKUJVDWEWQQEUKULEWHWIUNUOWOW
      IWHWOIWJNWIWNIWJWNIUPZMIEWRUQURIUSUTTSWIWHEWBVAVBTSTZVEWEWLLBWADBACEVCVFZ
      VGWDWLWCWDWEWLQWTVHWCWLWBJGZWCRZWLRBVIXAXBLZIWKXCWKIXCWKWMIWKWMWSVJXCIWMX
      CIWMDACWBVKVLVMVNVMVOVPVQVRVSVTVJ $.
  $}

  ${
    $d N n x $.  $d U n x $.  $d X n x $.
    finxpreclem3.1 $e |- F =
        ( n e. _om , x e. _V |-> if ( ( n = 1o /\ x e. U ) , (/) ,
        if ( x e. ( _V X. U ) , <. U. n , ( 1st ` x ) >. , <. n , x >. ) ) ) $.
    $( Lemma for ` ^^ ` recursion theorems.  (Contributed by ML,
       20-Oct-2020.) $)
    finxpreclem3 $p |- ( ( ( N e. _om /\ 2o C_ N ) /\ X e. ( _V X. U ) ) ->
                        <. U. N , ( 1st ` X ) >. =
                        ( F ` <. N , X >. ) ) $=
      ( com wcel c2o wss wa cvv c1st cfv cop c1o wceq c0 cif cxp co cuni cv a1i
      cmpo eqeq1 eleq1 bi2anan9 wb adantl unieq adantr opeq12d opeq12 ifbieq12d
      fveq2 ifbieq2d wpss wne csuc sssucid sseqtrri 1on sucneqoni necomi df-pss
      df-2o mpbir2an ssnpss mt2 sseq2 mtbiri intnanrd iffalsed iftrue sylan9eqr
      con2i sylan9eq adantlll simpll elex opex ovmpod df-ov eqtr3di ) EHIZJEKZL
      ZFMBUAZIZLZEFDUBEUCZFNOZPZEFPZDOWLCAEFHMCUDZQRZAUDZBIZLZSWSWJIZWQUCZWSNOZ
      PZWQWSPZTZTZWODMDCAHMXHUFRWLGUEWHWKWQERZWSFRZLZXHWORWGXKWHWKLXHEQRZFBIZLZ
      SWKWOWPTZTZWOXKXAXNXGXOSXIWRXLXJWTXMWQEQUGWSFBUHUIXKXBWKXEXFWOWPXJXBWKUJX
      IWSFWJUHUKXKXCWMXDWNXIXCWMRXJWQEULUMXJXDWNRXIWSFNUQUKUNWQWSEFUOUPURWHWKXP
      XOWOWHXNSXOWHXLXMXLWHXLWHJQKZXQQJUSZXRQJKQJUTQQVAJQVBVHVCJQJQVHVDVEVFQJVG
      VIJQVJVKEQJVLVMVRVNVOWKWOWPVPVSVQVTWGWHWKWAWKFMIWIFWJWBUKWOMIWLWMWNWCUEWD
      EFDWEWF $.
  $}

  ${
    $d N n x $.  $d N o $.  $d U n x $.  $d n x y $.
    finxpreclem4.1 $e |- F =
        ( n e. _om , x e. _V |-> if ( ( n = 1o /\ x e. U ) , (/) ,
        if ( x e. ( _V X. U ) , <. U. n , ( 1st ` x ) >. , <. n , x >. ) ) ) $.
    $( Lemma for ` ^^ ` recursion theorems.  (Contributed by ML,
       23-Oct-2020.) $)
    finxpreclem4 $p |- ( ( ( N e. _om /\ 2o C_ N ) /\ y e. ( _V X. U ) ) ->
                ( rec ( F , <. N , y >. ) ` N ) =
                 ( rec ( F , <. U. N , ( 1st ` y ) >. ) ` U. N ) ) $=
      ( vo com wcel c2o cfv c1o coa co wceq con0 ax-mp c0 adantr wss wa cvv cxp
      cv cuni c1st cop crdg crio csuc 2onn nnon wsbc wreu 2on oawordeu riotasbc
      mpanl1 syl csb riotaex sbceq1g csbov2g csbvargi oveq2i eqtri eqeq1i bitri
      wb sylib sylan simpl eqeltrd riotacl riotaund 0elon eqeltrdi pm2.61i mpan
      nnarcl biantrur bitr4di nnacom sylancr 1onn nnasuc sylancl eqtrid 3eqtr3d
      wn df-2o wne wlim sucidg eleqtrri ssel mpi adantl nnlim onsucuni3 syl3anc
      ne0d suceq cfn word ordom ordelss nnfi nnunifi syl2anc nnacl peano4 mpbid
      fveq2d fveq2i rdgsuc opex rdg0 3eqtri finxpreclem3 eqtr4id 2on0 rdgsucuni
      df-1o mp3an 1oequni2o eqtr4i 3eqtr4g wi 1on rdgeqoa mp3an12 sylc 3eqtr2rd
      ) FIJZKFUAZUBZBUEZUCCUDJZUBZFUFZEUUBYSUGLZUHZUIZLZMKHUEZNOZFPZHQUJZNOZUUE
      LZKUUJNOZEFYSUHZUIZLZFUUOLZYRUUFUULPYTYRUUBUUKUUEYRUUBUKZUUKUKZPZUUBUUKPZ
      YRFUUJMNOZUKZUURUUSYRUUMUUJKNOZFUVCYRKIJZUUJIJZUUMUVDPULYRUUMIJZUVFYRUUMF
      IYPFQJZYQUUMFPZFUMZUVHYQUBZUUIHUUJUNZUVIUVKUUIHQUOZUVLKQJZUVHYQUVMUPHKFUQ
      USUUIHQURUTUVLHUUJUUHVAZFPZUVIUUJUCJZUVLUVPVJUUIHQVBZHUUJUUHFUCVCRUVOUUMF
      UVOKHUUJUUGVAZNOZUUMUVQUVOUVTPUVRHUUJKUUGNUCVDRUVSUUJKNHUUJUVRVEVFVGVHVIV
      KVLZYPYQVMVNUUJQJZUVGUVFVJUVMUWBUUIHQVOUVMWKUUJSQUUIHQVPVQVRVSUWBUVGUVEUV
      FUBZUVFUVNUWBUVGUWCVJUPKUUJWAVTUVEUVFULWBWCRVKZKUUJWDWEUWAYRUVDUUJMUKZNOZ
      UVCKUWEUUJNWLVFYRUVFMIJZUWFUVCPUWDWFUUJMWGWHWIWJYRUVHFSWMZFWNWKZFUURPYPUV
      HYQUVJTYQUWHYPYQFMYQMKJMFJMUWEKUWGMUWEJWFMIWORWLWPKFMWQWRXCWSYPUWIYQFWTTF
      XAXBYRUVBUUKPZUVCUUSPYRUVFUWGUWJUWDWFUUJMWDWHUVBUUKXDUTWJYRUUBIJZUUKIJZUU
      TUVAVJYPUWKYQYPFIUAZFXEJUWKIXFYPUWMXGIFXHVTFXIFXJXKTYRUWGUVFUWLWFUWDMUUJX
      LWEUUBUUKXMXKXNXOTUUAUVFKUUOLZMUUELZPZUUPUULPZYRUVFYTUWDTUUAMUUOLZELZUUDE
      LZUWNUWOUUAUWRUUDEUUAUWRUUNELZUUDUWRSUKZUUOLZSUUOLZELZUXAMUXBUUOYEXPSQJZU
      XCUXEPVQUUNSEXQRUXDUUNEUUNEFYSXRXSXPXTACDEFYSGYAYBXOUWNKUFZUUOLZELZUWSUVN
      KSWMKWNWKZUWNUXIPUPYCUVEUXJULKWTRKEUUNYDYFUWRUXHEMUXGUUOYGXPXPYHUWOUXBUUE
      LZSUUELZELZUWTMUXBUUEYEXPUXFUXKUXMPVQUUDSEXQRUXLUUDEUUDEUUBUUCXRXSXPXTYIU
      VNMQJUVFUWPUWQYJUPYKUUNUUDEMKUUJYLYMYNYRUUPUUQPYTYRUUMFUUOUWAXOTYO $.
  $}

  ${
    $d n x $.
    finxpreclem5.1 $e |- F =
        ( n e. _om , x e. _V |-> if ( ( n = 1o /\ x e. U ) , (/) ,
        if ( x e. ( _V X. U ) , <. U. n , ( 1st ` x ) >. , <. n , x >. ) ) ) $.
    $( Lemma for ` ^^ ` recursion theorems.  (Contributed by ML,
       24-Oct-2020.) $)
    finxpreclem5 $p |- ( ( n e. _om /\ 1o e. n ) ->
             ( -. x e. ( _V X. U ) -> ( F ` <. n , x >. ) = <. n , x >. ) ) $=
      ( cv com wcel c1o wa cvv cxp wn cop cfv wceq c0 cif opex ifex co cuni vex
      df-ov 0ex ovmpt4g mp3an23 ad2antrr 1on onirri eleq2 mtbiri con2i intnanrd
      c1st iffalsed adantl iffalse sylan9eq eqtrd eqtr3id ex ) CFZGHZIVCHZJZAFZ
      KBLHZMZVCVGNZDOZVJPVFVIJZVKVCVGDUAZVJVCVGDUDVLVMVCIPZVGBHZJZQVHVCUBZVGUOO
      ZNZVJRZRZVJVDVMWAPZVEVIVDVGKHWAKHWBAUCVPQVTUEVHVSVJVQVRSVCVGSTTCAGKWADKEU
      FUGUHVFVIWAVTVJVEWAVTPVDVEVPQVTVEVNVOVNVEVNVEIIHIUIUJVCIIUKULUMUNUPUQVHVS
      VJURUSUTVAVB $.

    $d F m o $.  $d N x n y $.  $d U m n o x $.  $d U n x y $.
    $( Lemma for ` ^^ ` recursion theorems.  (Contributed by ML,
       24-Oct-2020.) $)
    finxpreclem6 $p |- ( ( N e. _om /\ 1o e. N ) ->
                           ( U ^^ N ) C_ ( _V X. U ) ) $=
      ( vy vm com wcel c1o wa wi cv wceq wn c0 cop cfv fveqeq2 cfinxp cvv eleq1
      vo cxp wss eleq2 anbi12d anass crdg nfv cuni c1st cmpo nfmpo2 nfcxfr nfcv
      cif nfrdg nffv nfeq2 nfn notbid anbi2d opeq2 rdgeq2 fveq1d eqeq2d imbi12d
      nfim syl vex csuc opex rdg0 a1i con0 nnon fveq2 sylan9eq finxpreclem5 imp
      rdgsuc expl expcomd finds2 imbi2d mpbiri equcoms vtocle biimtrrid anabsi5
      wne opnzi eqnetrd necomd neneqd chvarfv intnand adantl wb opeq1 id abbidv
      cab fveq12d dffinxpf eqtr4di eleq2d abid bitr3di adantr mtbird ex expdimp
      biimtrid con4d ssrdv sylbird vtocleg ) EIJZKEJZBEUAZUBBUEZUFZYAYBLZYEMCEI
      CNZEOZYFYGIJZKYGJZLZYEYHYIYAYJYBYGEIUCZYGEKUGUHYHYKYEYHYKLZGYCYDYMGNZYDJZ
      YNYCJZYHYKYOPZYPPZYKYQLYIYJYQLZLZYHYRYIYJYQUIYHYTYRYHYTLYPYIQYGDYGYNRZUJZ
      SZOZLZYTUUEPYHYTUUDYIYIYJANZYDJZPZLZLZQYGDYGUUFRZUJZSZOZPZMYTUUDPZMAGYTUU
      PAYTAUKUUDAAQUUCAYGUUBAUUADADCAIUBYGKOUUFBJLQUUGYGULUUFUMSRUUKURURZUNFCAI
      UBUUQUOUPAUUAUQUSAYGUQUTVAVBVJUUFYNOZUUJYTUUOUUPUURUUIYSYIUURUUHYQYJUURUU
      GYOUUFYNYDUCVCVDVDUURUUNUUDUURUUMUUCQUURYGUULUUBUURUUKUUAOUULUUBOUUFYNYGV
      EUUKUUADVFVKVGVHVCVIUUJQUUMUUJUUMQUUJUUMUUKQYIUUIUUMUUKOZUUJYKUUHLZYIUUSY
      IYJUUHUIYIUUTUUSMZMZHYGCVLZUVBCHYGHNZOZUVBUVDIJZUUTUVDUULSUUKOZMZMUVGQUUL
      SUUKOZUDNZUULSZUUKOZUVJVMZUULSZUUKOZUUTHUDUVDQUUKUULTUVDUVJUUKUULTUVDUVMU
      UKUULTUVIUUTUUKDYGUUFVNVOVPUVJIJZUVLUUTUVOUVPUVLUUTUVOUVPUVLLUUTUVNUUKDSZ
      UUKUVPUVLUVNUVKDSZUVQUVPUVJVQJUVNUVROUVJVRUUKUVJDWCVKUVKUUKDVSVTYKUUHUVQU
      UKOABCDFWAWBVTWDWEWFUVEYIUVFUVAUVHYGUVDIUCUVEUUSUVGUUTYGUVDUUKUULTWGVIWHW
      IWJWKWLUUKQWMUUJYGUUFUVCAVLWNVPWOWPWQWRWSWTYHYPUUEXAYTYHYNUUEGXEZJYPUUEYH
      UVSYCYNYHUVSYAQEDEYNRZUJZSZOZLZGXEYCYHUUEUWDGYHYIYAUUDUWCYLYHUUCUWBQYHYGE
      UUBUWAYHUUAUVTOUUBUWAOYGEYNXBUUAUVTDVFVKYHXCXFVHUHXDAGBCDEFXGXHXIUUEGXJXK
      XLXMXNXPXOXQXRXNXSXTWL $.
  $}

  ${
    $d F z $.  $d N n x y z $.  $d U n x y z $.
    finxpsuclem.1 $e |- F =
        ( n e. _om , x e. _V |-> if ( ( n = 1o /\ x e. U ) , (/) ,
        if ( x e. ( _V X. U ) , <. U. n , ( 1st ` x ) >. , <. n , x >. ) ) ) $.
    $( Lemma for ~ finxpsuc .  (Contributed by ML, 24-Oct-2020.) $)
    finxpsuclem $p |- ( ( N e. _om /\ 1o C_ N ) ->
                            ( U ^^ suc N ) = ( ( U ^^ N ) X. U ) ) $=
      ( vy vz wcel c1o wss wa cfv wceq wb c0 cop crdg ad2antrr syl com csuc cxp
      cfinxp cv c1st cvv peano2 adantr word 1on onordi ordsseleq sylancr biimpa
      wo nnord wi elelsuc a1i sucidg eleq1 syl5ibrcom jaod finxpreclem6 syl2anc
      mpd sselda c2o df-2o ordsucsssuc eqsstrid finxpreclem4 syl21anc ordunisuc
      simpr opeq1 rdgeq2 fveq12d eqtrd eqeq2d dffinxpf eqabri biantrurd bitr4id
      cuni fvex opeq2 fveq1d anbi2d baib 3bitr4d biimpd impancom ex jcad exbiri
      elab2 impd ancomsd impbid elxp8 bitr4di eqrdv ) EUAIZJEKZLZGBEUBZUDZBEUDZ
      BUCZXGGUEZXIIZXLUFMZXJIZXLUGBUCZIZLZXLXKIXGXMXRXGXMXOXQXGXMXOXGXMLXQXOXGX
      IXPXLXGXHUAIZJXHIZXIXPKXEXSXFEUHZUIXGJEIZJENZUPZXTXEXFYDXEJUJZEUJZXFYDOJU
      KULZEUQZJEUMUNUOXEYDXTURXFXEYBXTYCYBXTURXEJEUSUTXEXTYCEXHIEUAVAJEXHVBVCVD
      UIVGABCDXHFVEVFVHZXGXQXMXOXGXQLZXMXOYJPXHDXHXLQRMZNZPEDEXNQZRZMZNZXMXOYJY
      KYOPYJYKXHWFZDYQXNQZRZMZYOYJXSVIXHKZXQYKYTNXEXSXFXQYASXGUUAXQXGVIJUBZXHVJ
      XEXFUUBXHKZXEYEYFXFUUCOYGYHJEVKUNUOVLUIXGXQVPAGBCDXHFVMVNXEYTYONXFXQXEYQE
      YSYNXEYQENZYSYNNZXEYFUUDYHEVOTZUUDYRYMNUUEYQEXNVQYRYMDVRTTUUFVSSVTWAXEXMY
      LOXFXQXEXMXSYLLZYLUUGGXIAGBCDXHFWBWCXEXSYLYAWDWESXEXOYPOXFXQXOXEYPXEPEDEH
      UEZQZRZMZNZLXEYPLHXNXJXLUFWGUUHXNNZUULYPXEUUMUUKYOPUUMEUUJYNUUMUUIYMNUUJY
      NNUUHXNEWHUUIYMDVRTWIWAWJAHBCDEFWBWRWKSWLZWMWNVGWOXGXMXQYIWOWPXGXQXOXMXGX
      QXOXMXGXQXMXOUUNWQWSWTXAXLXJBXBXCXD $.
  $}

  ${
    $d N x y $.  $d U x y $.
    $( The value of Cartesian exponentiation at a successor.  (Contributed by
       ML, 24-Oct-2020.) $)
    finxpsuc $p |- ( ( N e. _om /\ N =/= (/) ) ->
                            ( U ^^ suc N ) = ( ( U ^^ N ) X. U ) ) $=
      ( vx vy com wcel c0 wne wa c1o wss csuc cfinxp cxp wceq syl cvv cop cif
      cv word wb ordge1n0 biimprd imdistani cuni c1st cfv cmpo eqid finxpsuclem
      nnord ) BEFZBGHZIUMJBKZIABLMABMANOUMUNUOUMUOUNUMBUAUOUNUBBULBUCPUDUECADDC
      EQDTZJOCTZAFIGUQQANFUPUFUQUGUHRUPUQRSSUIZBURUJUKP $.
  $}

  $( The value of Cartesian exponentiation at two.  (Contributed by ML,
     19-Oct-2020.) $)
  finxp2o $p |- ( U ^^ 2o ) = ( U X. U ) $=
    ( c2o cfinxp c1o csuc cxp wceq df-2o finxpeq2 com wcel c0 wne 1onn finxpsuc
    ax-mp 1n0 mp2an finxp1o xpeq1i 3eqtri ) ABCZADEZCZADCZAFZAAFBUCGUBUDGHABUCI
    PDJKDLMUDUFGNQADORUEAAASTUA $.

  $( The value of Cartesian exponentiation at three.  (Contributed by ML,
     24-Oct-2020.) $)
  finxp3o $p |- ( U ^^ 3o ) = ( ( U X. U ) X. U ) $=
    ( c3o cfinxp c2o csuc cxp wceq df-3o finxpeq2 com wcel c0 wne 2onn finxpsuc
    ax-mp 2on0 mp2an finxp2o xpeq1i 3eqtri ) ABCZADEZCZADCZAFZAAFZAFBUCGUBUDGHA
    BUCIPDJKDLMUDUFGNQADORUEUGAASTUA $.

  ${
    $d N n x y $.  $d U n x y $.
    $( Cartesian exponentiation when the exponent is not a natural number
       defaults to the empty set.  (Contributed by ML, 24-Oct-2020.) $)
    finxpnom $p |- ( -. N e. _om -> ( U ^^ N ) = (/) ) $=
      ( vy vn vx com wcel wn cfinxp cv c0 cvv c1o wceq cxp cfv cop cif sylnibr
      wa cuni c1st cmpo crdg cab simpl con3i abid df-finxp eleq2i eq0rdv ) BFGZ
      HZCABIZUMCJZULKBDEFLDJZMNEJZAGTKUQLAOGUPUAUQUBPQUPUQQRRUCBUOQUDPNZTZCUEZG
      ZUOUNGUMUSVAUSULULURUFUGUSCUHSUNUTUOECADBUIUJSUK $.
  $}

  ${
    $d N n $.  $d m n $.
    $( Cartesian exponentiation of the empty set to any power is the empty set.
       (Contributed by ML, 24-Oct-2020.) $)
    finxp00 $p |- ( (/) ^^ N ) = (/) $=
      ( vn vm com wcel c0 cfinxp wceq cv finxpeq2 eqeq1d finxp0 c1o suceq df-1o
      csuc eqtr4di syl finxp1o eqtrdi adantl wne wa cxp finxpsuc xp0 pm2.61dane
      a1d finds finxpnom pm2.61i ) ADEFAGZFHZFBIZGZFHFFGZFHFCIZGZFHZFUQPZGZFHZU
      MBCAUNFHUOUPFFUNFJKUNUQHUOURFFUNUQJKUNUTHUOVAFFUNUTJKUNAHUOULFFUNAJKFLUQD
      EZVBUSVCVBUQFUQFHZVBVCVDVAFMGZFVDUTMHVAVEHVDUTFPMUQFNOQFUTMJRFSTUAVCUQFUB
      UCVAURFUDFFUQUEURUFTUGUHUIFAUJUK $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Topology
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Using the axiom of countable choice ~ ax-cc , the countable union of
     countable sets is countable.  See ~ iunctb for a somewhat more general
     theorem.  (Contributed by ML, 10-Dec-2020.) $)
  iunctb2 $p |- ( A. x e. _om B ~<_ _om -> U_ x e. _om B ~<_ _om ) $=
    ( com cdom wbr wral ciun cvv wcel omex domrefg ax-mp iunctb mpan ) CCDEZBCD
    EACFACBGCDECHIOJCHKLACBMN $.

  ${
    $d A n $.  $d A n y z $.
    $( A class which dominates every natural number is not finite.
       (Contributed by ML, 14-Dec-2020.) $)
    domalom $p |- ( A. n e. _om n ~<_ A -> -. A e. Fin ) $=
      ( vy vz cv cdom wbr com wral cen wn wcel csdm wi breq1 csuc c1o 1onn syl
      c0 cfn nfra1 wceq imbi2d wne 1n0 wb 0sdomg ax-mp mpbir rspccv mpi sylancr
      sdomdomtr wa peano2 impel syl2an2 a1d expcom finds2 vtoclga com12 ralrimi
      php4 sdomnen ensym nsyl ralimi wrex isfi notbii ralnex bitr4i sylibr ) BE
      ZAFGZBHIZAVPJGZKZBHIZAUALZKZVRVPAMGZBHIWAVRWDBHVQBHUBVPHLVRWDVRCEZAMGZNVR
      WDNCVPHWEVPUCWFWDVRWEVPAMOUDWFTAMGZDEZAMGZWHPZAMGZVRCDWETAMOWEWHAMOWEWJAM
      OVRTQMGZQAFGZWGWLQTUEZUFQHLZWLWNUGRQHUHUIUJVRWOWMRVQWMBQHVPQAFOUKULTQAUNU
      MVRWHHLZWIWKNVRWPUOWKWIWPWJWJPZMGZVRWQAFGZWKWPWJHLZWRWHUPZWJVESVRWQHLZWSW
      PVQWSBWQHVPWQAFOUKWPWTXBXAWJUPSUQWJWQAUNURUSUTVAVBVCVDWDVTBHWDVPAJGVSVPAV
      FAVPVGVHVISWCVSBHVJZKWAWBXCBAVKVLVSBHVMVNVO $.
  $}

  ${
    $d A n x $.  $d A n $.
    $( The converse of ~ isinf .  Any set that is not finite is literally
       infinite, in the sense that it contains subsets of arbitrarily large
       finite cardinality.  (It cannot be proven that the set has _countably
       infinite_ subsets unless AC is invoked.)  The proof does not require the
       Axiom of Infinity.  (Contributed by ML, 14-Dec-2020.) $)
    isinf2 $p |- ( A. n e. _om E. x ( x C_ A /\ x ~~ n ) -> -. A e. Fin ) $=
      ( cvv wcel cv wss cen wbr wa wex com wral cfn wn wi cdom ssdomg adantr wb
      domen1 adantl sylibd expimpd ancomsd exlimdv ralimdv domalom syl6 pm2.61i
      prcnel a1d ) BDEZAFZBGZUNCFZHIZJZAKZCLMZBNEOZPUMUTUPBQIZCLMVAUMUSVBCLUMUR
      VBAUMUQUOVBUMUQUOVBUMUQJUOUNBQIZVBUMUOVCPUQUNBDRSUQVCVBTUMUNUPBUAUBUCUDUE
      UFUGBCUHUIUMOVAUTBNUKULUJ $.
  $}

  ${
    $d A f n x $.
    $( Using the axiom of choice, any infinite class has a countable subset.
       (Contributed by ML, 14-Dec-2020.) $)
    ctbssinf $p |- ( -. A e. Fin -> E. x ( x C_ A /\ x ~~ _om ) ) $=
      ( vn vf wcel cv wss cen wbr wa wex com wral wceq sseq1 anbi12d ralimi syl
      cuni cdom cfn wn wfn cfv isinf omex breq1 ac6s2 crn simpl cpw fvex ralbii
      elpw fnfvrnss uniss unipw sseqtrdi sylan2br sylan2 ciun cmpt dffn5 biimpi
      rneqd unieqd dfiun3 eqtr4di adantr simpr nnsdom domsdomtr sdomdom syl2anr
      csdm endom ralimiaa iunctb2 3syl adantl eqbrtrd fvssunirn jctl isinf2 cvv
      spcev wb vex rnex uniex infinf ax-mp sylib sbth syl2anc exlimiv ) BUAEUBA
      FZBGZWQCFZHIZJZAKCLMDFZLUCZWSXBUDZBGZXDWSHIZJZCLMZJZDKWRWQLHIZJZAKZABCUEX
      AXGCALDUFWQXDNZWRXEWTXFWQXDBOWQXDWSHUGZPUHXIXLDXIXBUIZSZBGZXPLHIZXLXHXCXE
      CLMZXQXGXECLXEXFUJQXSXCXDBUKZEZCLMZXQYAXECLXDBWSXBULZUNUMXCYBJXOXTGZXQCLX
      TXBUOYDXPXTSBXOXTUPBUQURRUSUTXIXPLTILXPTIZXRXIXPCLXDVAZLTXCXPYFNXHXCXPCLX
      DVBZUIZSYFXCXOYHXCXBYGXCXBYGNCLXBVCVDVEVFCLXDYCVGVHVIXHYFLTIZXCXHXFCLMXDL
      TIZCLMYIXGXFCLXEXFVJQXFYJCLXFXDWSTIZWSLVOIZYJWSLEXDWSVPWSVKYKYLJXDLVOIYJX
      DWSLVLXDLVMRVNVQCXDVRVSVTWAXHYEXCXHXDXPGZXFJZCLMZYEXGYNCLXFYNXEXFYMXBWSWB
      WCVTQYOXPUAEUBZYEYOWQXPGZWTJZAKZCLMYPYNYSCLYRYNAXDYCXMYQYMWTXFWQXDXPOXNPW
      FQAXPCWDRXPWEEYPYEWGXOXBDWHWIWJZXPWEWKWLWMRVTXPLWNWOXKXQXRJAXPYTWQXPNWRXQ
      XJXRWQXPBOWQXPLHUGPWFWOWPVS $.
  $}

  ${
    $d A x y $.  $d B y $.
    $( The index set of an indexed union is a subset of the union when each
       ` B ` contains its index.  (Contributed by ML, 16-Dec-2020.) $)
    ralssiun $p |- ( A. x e. A x e. B -> A C_ U_ x e. A B ) $=
      ( vy cv wcel wral ciun nfra1 nfcv nfiu1 wa wi wceq cab simpr rsp wb eleq1
      wrex adantl imbi2d adantr mpbid imp syl2anc sylibr ad2antrr mpbird df-iun
      rspe abid eleqtrrdi expl equcoms vtocleg anabsi7 ex ssrd ) AEZCFZABGZABAB
      CHZVAABIABJABCKVBUTBFZUTVCFZVBVDVEVBVDLVEMZDUTBVFADUTDEZNZVBVDVEVHVBLZVDL
      ZUTVGCFZABTZDOZVCVJUTVMFZVGVMFZVJVLVOVJVDVKVLVIVDPVIVDVKVIVDVAMZVDVKMZVBV
      PVHVAABQUAVHVPVQRVBVHVAVKVDUTVGCSUBUCUDUEVKABUKUFVLDULUGVHVNVORVBVDUTVGVM
      SUHUIADBCUJUMUNUOUPUQURUS $.
  $}

  ${
    $d A n p $.  $d J n p $.  $d X n p $.
    nlpineqsn.x $e |- X = U. J $.
    $( For every point ` p ` of a subset ` A ` of ` X ` with no limit points,
       there exists an open set ` n ` that intersects ` A ` only at ` p ` .
       (Contributed by ML, 23-Mar-2021.) $)
    nlpineqsn $p |- ( ( J e. Top /\ A C_ X /\ ( ( limPt ` J ) ` A ) = (/) )
              -> A. p e. A E. n e. J ( p e. n /\ ( n i^i A ) = { p } ) ) $=
      ( wcel wss cfv c0 wceq w3a cv cin wa wrex cdif wn wb adantr clp csn simp1
      ctop simp2 ssel2 3adant1 3jca wne wi wral eleq2 mtbiri adantl islp3 mtbid
      anbi2i annim bitr3i rexbii rexnal bitri sylibr sylan indif2 eqeq1i ssdif0
      noel nne bitr4i elin wo sssn n0i biorf syl bitr4id sylbir bitrid pm5.32da
      ancoms rexbidv 3ad2ant3 mpbid 3an1rs ralrimiva ) CUDGZADHZACUAIIZJKZLEMZB
      MZGZWLANZWKUBZKZOZBCPZEAWGWHWKAGZWJWRWGWHWSLZWJOWMWLAWOQNZJKZOZBCPZWRWTWG
      WHWKDGZLZWJXDWTWGWHXEWGWHWSUCWGWHWSUEWHWSXEWGADWKUFUGUHXFWJOZWMXAJUIZUJZB
      CUKZRZXDXGWKWIGZXJWJXLRXFWJXLWKJGWKVHWIJWKULUMUNXFXLXJSWJBWKACDFUOTUPXDXI
      RZBCPXKXCXMBCXCWMXHRZOXMXNXBWMXAJVIUQWMXHURUSUTXIBCVAVBVCVDWTXDWRSZWJWSWG
      XOWHWSXCWQBCWSWMXBWPWMWSXBWPSXBWNWOHZWMWSOZWPXBWNWOQZJKXPXAXRJWLAWOVEVFWN
      WOVGVJXQWKWNGZXPWPSWKWLAVKXSXPWNJKZWPVLZWPWNWKVMXSXTRWPYASWNWKVNXTWPVOVPV
      QVRVSWAVTWBWCTWDWEWF $.

    $d A f n p $.  $d J f n p $.  $d X n p $.
    $( Given a subset ` A ` of ` X ` with no limit points, there exists a
       function from each point ` p ` of ` A ` to an open set intersecting
       ` A ` only at ` p ` .  This proof uses the axiom of choice.
       (Contributed by ML, 23-Mar-2021.) $)
    nlpfvineqsn $p |- ( A e. V ->
        ( ( J e. Top /\ A C_ X /\ ( ( limPt ` J ) ` A ) = (/) )
        -> E. f ( f : A --> J /\ A. p e. A ( ( f ` p ) i^i A ) = { p } ) ) ) $=
      ( vn ctop wcel wss clp cfv c0 wceq cv cin wrex wral wa wf nlpineqsn simpr
      w3a csn wex reximi ralimi syl ineq1 eqeq1d ac6sg syl5 ) CIJAEKACLMMNOUDZH
      PZAQZFPZUEZOZHCRZFASZADJACBPZUAUQVBMZAQZUROZFASTBUFUNUQUOJZUSTZHCRZFASVAA
      HCEFGUBVHUTFAVGUSHCVFUSUCUGUHUIUSVEFHACBDUOVCOUPVDURUOVCAUJUKULUM $.
  $}

  ${
    $d A p q $.  $d F p q $.
    $( A theorem about functions where the image of every point intersects the
       domain only at that point.  If ` J ` is a topology and ` A ` is a set
       with no limit points, then there exists an ` F ` such that this
       antecedent is true.  See ~ nlpfvineqsn for a proof of this fact.
       (Contributed by ML, 23-Mar-2021.) $)
    fvineqsnf1 $p |- ( ( F : A --> J /\ A. p e. A ( ( F ` p ) i^i A ) = { p } )
                      -> F : A -1-1-> J ) $=
      ( vq cv cfv cin csn wceq wral wa biimpi wal ax-5 alral sylibr eqeq1 eqcom
      syl wf wi fveq2 ineq1d sneq eqeq12d cbvralvw ralcom 3syl anim12i r19.26-2
      wf1 mpdan ineq1 bitrdi cvv wcel wb vex sneqbg ax-mp bitri sylan9bb ralimi
      imbitrid anim2i dff13 ) ACBUAZDFZBGZAHZVIIZJZDAKZLVHVJEFZBGZJZVIVOJZUBZEA
      KZDAKZLACBULVNWAVHVNVMVPAHZVOIZJZLZEAKZDAKZWAVNVMEAKDAKZWDEAKZDAKZLZWGVNW
      IWKVNWIVMWDDEAVRVKWBVLWCVRVJVPAVIVOBUCUDVIVOUEUFUGMVNWHWIWJVNVNENVNEAKZWH
      VNEOVNEAPWLWHVMEDAAUHMUIWIWIDNWJWIDOWIDAPTUJUMVMWDDEAAUKQWFVTDAWEVSEAVQVK
      WBJZWEVRVJVPAUNVMWMWBVLJZWDVRVMWMVLWBJWNVKVLWBRVLWBSUOWDWNWCVLJZVRWBWCVLR
      WOVLWCJZVRWCVLSVIUPUQWPVRURDUSVIVOUPUTVAVBUOVCVEVDVDTVFDEACBVGQ $.
  $}

  ${
    $d A q x o y $.  $d F q x o y $.  $d A p $.  $d F p $.  $d p o y $.
    $( A theorem about functions where the image of every point intersects the
       domain only at that point.  (Contributed by ML, 27-Mar-2021.) $)
    fvineqsneu $p |- ( ( F Fn A /\ A. p e. A ( ( F ` p ) i^i A ) = { p } )
                       -> A. q e. A E! x e. ran F q e. x ) $=
      ( vo vy cv cfv wceq wral wa wcel wreu wb wi ex nfv rsp syl6 fnfvelrn wrex
      wfn cin csn crn adantr fnrnfv eqabrd nfra1 nfan elin rbaib ad2antll velsn
      eleq2w2 equcom bitri bitrdi adantl adantrd bitr3d sylan9bbr anass1rs impr
      imp an32s eqeq1 wf wf1 dffn3 fvineqsnf1 sylanb dff13 sylib simpl2im imp32
      fveq2 impbid1 bitr4d ralrimiv exp32 rexlimd sylbid com23 reu6i syl6c nfvd
      ralrimdv elequ12 cbvreud cbvralvw sylibr ) CBUCZEHZCIZBUDZWOUEZJZEBKZLZFH
      ZGHZMZGCUFZNZFBKDHZAHZMZAXENZDBKXAXFFBXAXBBMZXBCIZXEMZXDXCXLJZOZGXEKZXFWN
      XKXMPWTWNXKXMBXBCUAQUGXAXKXOGXEXAXCXEMZXKXOXAXQXOFBKZXKXOPXAXQXCWPJZEBUBZ
      XRWNXQXTOWTWNXTGXEEGBCUHUIUGXAXSXREBWNWTEWNERWSEBUJUKXRERXAWOBMZXSXRXAYAX
      SLZLZXOFBYCXKXOYCXKLXDWOXBJZXNXAXKYBXDYDOZXAXKLZYAXSYEXAYAXKXSYEPXAYAXKLZ
      LZXSYEXSXDXBWPMZYHYDFXCWPUPYHXBWQMZYIYDXKYJYIOXAYAYJYIXKXBWPBULUMUNXAYGYJ
      YDOZXAYAYKXKWTYAYKPWNWTYAWSYKWSEBSWSYJXBWRMZYDFWQWRUPYLXBWOJYDFWOUOFEUQUR
      USTUTVAVFVBVCQVDVEVGXAXKYBXNYDOZYFYAXSYMXAYAXKXSYMPYHXSYMXSXNWPXLJZYHYDXC
      WPXLVHYHYNYDXAYAXKYNYDPZXAYAYOFBKZXKYOPXABXECVIZYPEBKZYAYPPXABXECVJZYQYRL
      WNYQWTYSBCVKBCXEEVLVMEFBXECVNVOYPEBSVPYOFBSTVQWOXBCVRVSVCQVDVEVGVTQWAWBWC
      WDXOFBSTWEWIXMXPXFXDGXEXLWFQWGWAXJXFDFBXGXBJZXIXDAGXEYTARYTGRYTXIGWHYTXDA
      WHYTXHXCJXIXDODFAGWJQWKWLWM $.
  $}

  ${
    $d A p x $.  $d F p x $.  $d Z p x $.
    $( A theorem about functions where the image of every point intersects the
       domain only at that point.  (Contributed by ML, 28-Mar-2021.) $)
    fvineqsneq $p |- ( ( ( F Fn A /\ A. p e. A ( ( F ` p ) i^i A ) = { p } )
                       /\ ( Z C_ ran F /\ A C_ U. Z ) ) -> Z = ran F ) $=
      ( vx wceq wral wa wn wi wcel wrex wal adantl sylibr adantr rsp ex syl nfv
      wfn cv cfv cin csn crn wss cuni wpss pssnel df-rex fnrnfv eqabrd ralrimiv
      biimpd r19.29r syl2anc nfra1 vsnid eleq2 mpbiri elin1d syl6 sylibrd com23
      wex wb reximdai anim2d reximdv mpd ancom bitr4i rexbii sylib rexcom nfre1
      r19.41v 19.3 alral sylbir nfan wreu fvineqsneu adantrd imp reupick3 3expa
      reximi expcom mpand ralrimi ralim impcom con2b ralbii df-ral bi2.04 albii
      expr 3bitri a1i rexbid mpbid nfa1 pssss bilanri mpdd ralnex eluni2 notbii
      df-ss a1d dfss3 dfral2 bitri con2bii2 con2d npss imbitrdi imp32 ) BAUAZDU
      BZBUCZAUDZYCUEZFZDAGZHZCBUFZUGZACUHZUGZCYJFZYIYMYKYNYIYMCYJUIZIYKYNJYIYOY
      MYIYOYMIZYIYOHZYCYLKZIZDALZYPYQYCEUBZKZECLZIZDALZYTYQUUBIZECGZDALZUUEYQUU
      ACKZUUAYJKZUUFJZJZEMZDALZUUHYQUUBUUIIZJZEYJGZDALZUUNYQUUBUUOHZEYJLZEYJGZU
      UTUUPJZEYJGZHZDALZUURYQUVADALZUVCDAGUVEYQUUTDALZUVFYQUUSDALZEYJLZUVGYQUUO
      UUBDALZHZEYJLZUVIYQUUOUUAYDFZDALZHZEYJLZUVLYQUUOEYJLZUVNEYJGZUVPYQUUJUUOH
      EVFZUVQYOUVSYIECYJUJNUUOEYJUKOYIUVRYOYBUVRYHYBUVNEYJYBUUJUVNYBUVNEYJDEABU
      LUMUOUNPPUUOUVNEYJUPUQYQUVOUVKEYJYQUVNUVJUUOYIUVNUVJJZYOYHUVTYBYHUVMUUBDA
      YGDAURZYHUVMYCAKZUUBYHUVMUWBUUBJYHUVMHUWBYCYDKZUUBYHUWBUWCJUVMYHUWBYGUWCY
      GDAQYGYDAYCYGYCYEKYCYFKDUSYEYFYCUTVAVBVCPUVMUUBUWCVGYHUUAYDYCUTNVDRVEVHNP
      VIVJVKUVKUVHEYJUVKUVJUUOHUVHUUOUVJVLUUBUUODAVRVMVNVOUUSDEAYJVPOUUTUVADAUU
      TUUTEMUVAUUTEUUSEYJVQVSUUTEYJVTWAWISYQUVCDAYIYODYBYHDYBDTUWAWBYODTWBZYQUW
      BUVCYQUWBHZUVBEYJUWEETYQUWBUUJUVBYQUWBUUJHZHUUBEYJWCZUUTUUPYQUWFUWGYQUWBU
      WGUUJYQUWGDAGZUWBUWGJYIUWHYOEABDDWDPUWGDAQSWEWFUWFUWGUUTHZUUPJZYQUUJUWJUW
      BUWIUUJUUPUWGUUTUUJUUPUUBUUOEYJWGWHWJNNWKWTWLRWLUVAUVCDAUPUQUVDUUQDAUVCUV
      AUUQUUTUUPEYJWMWNWISYQUUQUUMDAUWDUUQUUMVGYQUUQUUIUUFJZEYJGUUJUWKJZEMUUMUU
      PUWKEYJUUBUUIWOWPUWKEYJWQUWLUULEUUJUUIUUFWRWSXAXBXCXDYQUUMUUGDAUWDYQUUMUU
      GJUWBYQUUMUUGYQUUMHZUUFECYQUUMEYQETUULEXEWBUWMUUIUUJUUFUWMUUJECGZUUIUUJJZ
      YQUWNUUMYQUWOEMZUWNYOUWPYIYOYKUWPCYJXFECYJXLVONUUJECWQOPUUJECQSUWMUUKECGZ
      UULUWQUUMYQUUKECWQXGUUKECQSXHWLRXMVHVKUUGUUDDAUUBECXIVNVOYSUUDDAYRUUCEYCC
      XJXKVNOYMYTYMYRDAGYTIDAYLXNYRDAXOXPXQORXRCYJXSXTVEYA $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Pi-base theorems
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  This section contains a few proofs of theorems found in the pi-base database.
  The pi-base site can be found at ~ https://topology.pi-base.org .

  Definitions of topological properties are theorems labeled pibpN, where N is
  the property number in pi-base.  For example, ~ pibp19 defines countably
  compact topologies.  Proofs of theorems are similarly labeled pibtN, for
  example ~ pibt2 .

$)

  ${
    $d J y z $.
    pibp16.x $e |- X = U. J $.
    $( Property P000016 of pi-base.  The class of compact topologies.  A space
       ` X ` is compact if every open cover of ` X ` has a finite subcover.
       This theorem is just a relabeled copy of ~ iscmp .  (Contributed by ML,
       8-Dec-2020.) $)
    pibp16 $p |- ( J e. Comp <-> ( J e. Top /\ A. y e. ~P J
      ( X = U. y -> E. z e. ( ~P y i^i Fin ) X = U. z ) ) ) $=
      ( iscmp ) ABCDEF $.
  $}

  ${
    $d J x y $.  $d J x z $.  $d X x $.
    pibp19.x $e |- X = U. J $.
    pibp19.19 $e |- C = { x e. Top | A. y e. ~P x
                         ( ( U. x = U. y /\ y ~<_ _om )
                         -> E. z e. ( ~P y i^i Fin ) U. x = U. z ) } $.
    $( Property P000019 of pi-base.  The class of countably compact topologies.
       A space ` X ` is countably compact if every countable open cover of
       ` X ` has a finite subcover.  (Contributed by ML, 8-Dec-2020.) $)
    pibp19 $p |- ( J e. C <-> ( J e. Top /\ A. y e. ~P J
      ( ( X = U. y /\ y ~<_ _om ) -> E. z e. ( ~P y i^i Fin ) X = U. z ) ) ) $=
      ( cv cuni wceq com cdom wbr wa cpw wrex wi wral eqeq1d cfn cin ctop unieq
      pweq eqtr4di anbi1d rexbidv imbi12d raleqbidv elrab2 ) AIZJZBIZJZKZUNLMNZ
      OZUMCIJZKZCUNPUAUBZQZRZBULPZSFUOKZUQOZFUSKZCVAQZRZBEPZSAEUCDULEKZVCVIBVDV
      JULEUEVKURVFVBVHVKUPVEUQVKUMFUOVKUMEJFULEUDGUFZTUGVKUTVGCVAVKUMFUSVLTUHUI
      UJHUK $.
  $}

  ${
    $d J x y $.  $d J x z $.  $d X x y $.  $d X x z $.
    pibp21.x $e |- X = U. J $.
    pibp21.21 $e |- W = { x e. Top | A. y e. ( ~P U. x \ Fin )
                          E. z e. U. x z e. ( ( limPt ` x ) ` y ) } $.
    $( Property P000021 of pi-base.  The class of weakly countably compact
       topologies, or limit point compact topologies.  A space ` X ` is weakly
       countably compact if every infinite subset of ` X ` has a limit point.
       (Contributed by ML, 9-Dec-2020.) $)
    pibp21 $p |- ( J e. W <-> ( J e. Top /\ A. y e. ( ~P X \ Fin )
                   E. z e. X z e. ( ( limPt ` J ) ` y ) ) ) $=
      ( cv clp cfv wcel cuni wrex cpw cfn cdif wral ctop wceq unieq pweqd fveq2
      eqtr4di difeq1d fveq1d eleq2d rexeqbidv raleqbidv elrab2 ) CIZBIZAIZJKZKZ
      LZCUMMZNZBUQOZPQZRUKULDJKZKZLZCFNZBFOZPQZRADSEUMDTZURVDBUTVFVGUSVEPVGUQFV
      GUQDMFUMDUAGUDZUBUEVGUPVCCUQFVHVGUOVBUKVGULUNVAUMDJUCUFUGUHUIHUJ $.
  $}

  ${
    $d J x y z $.
    pibt1.19 $e |- C = { x e. Top | A. y e. ~P x
                         ( ( U. x = U. y /\ y ~<_ _om )
                         -> E. z e. ( ~P y i^i Fin ) U. x = U. z ) } $.
    $( Theorem T000001 of pi-base.  A compact topology is also countably
       compact.  See ~ pibp16 and ~ pibp19 for the definitions of the relevant
       properties.  (Contributed by ML, 8-Dec-2020.) $)
    pibt1 $p |- ( J e. Comp -> J e. C ) $=
      ( ctop wcel cuni cv wceq cpw cfn cin wrex wi wral wa com cdom ccmp pm3.41
      wbr ralimi anim2i eqid pibp16 pibp19 3imtr4i ) EGHZEIZBJZIKZUKCJIKCULLMNO
      ZPZBELZQZRUJUMULSTUCZRUNPZBUPQZREUAHEDHUQUTUJUOUSBUPUMURUNUBUDUEBCEUKUKUF
      ZUGABCDEUKVAFUHUI $.
  $}

  ${
    $d C a b s $.  $d C a f s $.  $d J a b s y $.  $d J a f n p $.
    $d J x y z $.  $d X a b s y $.  $d X a n p $.  $d X a p s $.  $d X x y z $.
    $d a f p $.  $d b s y z $.  $d f s y $.
    pibt2.x $e |- X = U. J $.
    pibt2.19 $e |- C = { x e. Top | A. y e. ~P x
                         ( ( U. x = U. y /\ y ~<_ _om )
                         -> E. z e. ( ~P y i^i Fin ) U. x = U. z ) } $.
    pibt2.21 $e |- W = { x e. Top | A. y e. ( ~P U. x \ Fin )
                          E. z e. U. x z e. ( ( limPt ` x ) ` y ) } $.
    $( Theorem T000002 of pi-base, a countably compact topology is also weakly
       countably compact.  See ~ pibp19 and ~ pibp21 for the definitions of the
       relevant properties.  This proof uses the axiom of choice.  (Contributed
       by ML, 30-Mar-2021.) $)
    pibt2 $p |- ( J e. C -> J e. W ) $=
      ( vs vp wcel wceq com wbr wa wi wss cvv vb va vf vn ctop clp cfv wrex cpw
      cv cfn cdif wral cuni cin pibp19 simplbi wn eldif velpw anbi1i cen wex wb
      cdom infinf ax-mp infcntss sylbi ad2antll sstr ancoms c0 simplr csdm ccld
      vex simpll sseq1 mpbiri adantl cldlp adantr mpbird sylanl1 adantllr simpr
      0ss w3a wf1 cldss wf nlpineqsn reximi ralimi ineq1 eqeq1d ac6s fvineqsnf1
      csn jca eximi 4syl syl3an2 syl3an1 3adant1r crn cun ciun vsnid elin1d syl
      eleq2 anim1i unisng 3syl unss12 unidm sseqtrdi sylan syl2an syldan sylan2
      sseqtrrdi adantlrr isfinite adantrr ad2antrr mpd eqeq2d sylibr df-rex a1i
      ex unieq eximdv exlimdv sylan2b adantlr sseld ralssiun wfn fniunfv cldopn
      sseqtrd ancomd eqcomd eqimss ssun4 uniun ssun3 uncom undif1 eqtri ssequn2
      f1fn biimpi eqtrid eqsstrrd sylanr1 sylanr2 f1f topopn difopn snssd uniss
      frn eqssd ancom1s mpand impr wf1o f1f1orn f1oen3g sylancr enen1 snfi mpbi
      sdomdom sylancl biimtrdi impcom adantll ad2ant2lr elpw2g biimprd cbvrexvw
      endom unctb simprbi imbi2i ralbii breq1 anbi12d pweq ineq1d rspccv mp2and
      rexeqdv imbi12d elinel1 ssdif difun2 difss2d sseq2 uniexg eqeltrid difexg
      ineq2d disjdif eqtrdi inunissunidif sylan9bbr impancom anim12d fvineqsneq
      biimpd anim2d difss ssdomg eqbrtrrdi endomtr syl2anc syl6 expdimp elinel2
      jcad biimtrid anass1rs 3adant3 syl3anc domsdomtr exlimiv sdomnen pm2.65da
      mp2 anasss imnan imp neq0 sylib ancrd imbitrrdi lpss3 3expb reximdv an42s
      lpss ralrimiva fveq2 eleq12d cbvrexdva cbvralvw pibp21 sylanbrc ) EDMZEUE
      MZCUJZBUJZEUFUGZUGZMZCGUHZBGUIZUKULZUMZEFMVUPVUQGVUSUNZNZVUSOVEPZQZGVURUN
      ZNZCVUSUIZUKUOZUHZRZBEUIZUMZABCDEGHIUPZUQZVUPKUJZUAUJZVUTUGZMZKGUHZUAVVEU
      MVVFVUPVWEUAVVEVWBVVEMVUPVWBVVDMZVWBUKMURZQZVWEVWBVVDUKUSVWHVUPVWBGSZVWGQ
      ZVWEVWFVWIVWGUAGUTVAVUPVWJQUBUJZVWBSZVWKOVBPZQZUBVCZVWEVWGVWOVUPVWIVWGOVW
      BVEPZVWOVWBTMVWGVWPVDUAVQZVWBTVFVGUBVWBVWQVHVIVJVUPVWIVWOVWERVWGVUPVWIQZV
      WNVWEUBVWRVWNVWEVUPVWMVWIVWLVWEVUPVWMQZVWIVWLQZQZVWAVWKVUTUGZMZKGUHZVWEVW
      TVWSVWKGSZVXDVWLVWIVXEVWKVWBGVKVLVWSVXEQZVXCKVCZVXDVXFVXBVMNZURZVXGVWSVXE
      VXIVWSVXEVXHQZURVXEVXIRVWSVXJVWMVUPVWMVXJVNVWSVXJQVWKVWAVEPZVWAUKMZQZKVCZ
      VWKOVOPZVWMURVWSVXEVXHVXNVXFVXHQVWSVWKEVPUGMZVXHVXNVWSVXEVXHVRVUPVXEVXHVX
      PVWMVUPVUQVXEVXHVXPVVTVUQVXEQZVXHQVXPVXBVWKSZVXHVXRVXQVXHVXRVMVWKSVWKWHVX
      BVMVWKVSVTWAVXQVXPVXRVDVXHVWKEGHWBWCWDWEWFVXFVXHWGVWSVXPVXHWIVWKEUCUJZWJZ
      LUJZVXSUGZVWKUOZVYAWTZNZLVWKUMZQZUCVCZVXNVUPVXPVXHVYHVWMVUPVUQVXPVXHVYHVV
      TVXPVUQVXEVXHVYHVWKEGHWKZVUQVXEVXHWIVYAUDUJZMZVYJVWKUOZVYDNZQZUDEUHZLVWKU
      MVYMUDEUHZLVWKUMVWKEVXSWLZVYFQZUCVCVYHVWKUDEGLHWMVYOVYPLVWKVYNVYMUDEVYKVY
      MWGWNWOVYMVYELUDVWKEUCUBVQVYJVYBNVYLVYCVYDVYJVYBVWKWPWQWRVYRVYGUCVYRVXTVY
      FVWKVXSELWSVYQVYFWGXAXBXCXDXEXFVWSVXPVYHVXNRZVXHVUPVXPVWMVYSVUPVXPVWMQZQZ
      VYGVXNUCWUAVYGVXNWUAVYGQZGVWAUNZNZKVXSXGZGVWKULZWTZXHZUIZUKUOZUHZVXNWUBGW
      UHUNZNZWUHOVEPZWUKVUPVUQVYTVYGWUMVVTVUQVXPVYGWUMVWMVUQVXPQZVXTVYFWUMWUOVX
      TQZVXTVYFWUMWUOVXTWGWUPVYGWUMVXTWUOVYGWUMVYGVXTWUOQZVWKWUEUNZSZWUMVYGVWKL
      VWKVYBXIZWURVYFVWKWUTSZVXTVYFVYAVYBMZLVWKUMWVAVYEWVBLVWKVYEVYBVWKVYAVYEVY
      AVYCMVYAVYDMLXJVYCVYDVYAXMVTXKWOLVWKVYBUUAXLWAVXTWUTWURNZVYFVXTVXSVWKUUBZ
      WVCVWKEVXSUUPZLVWKVXSUUCXLWCUUEWUQWUSWUSWUFEMZQZWUMWUQWUSQWVFWUSWUQWVFWUS
      VXPWVFVXTVUQVWKEGHUUDVJXNUUFWUQWVGVXEWVGQZWUMWUQVXEWVGVXPVXEVXTVUQVYIVJXN
      WUQWVHQGWULWVHGWULSZWUQWVFVXEWUSWUFWULSZWVIWVFWUFWUGUNZNWUFWVKSZWVJWVFWVK
      WUFWUFEXOUUGWUFWVKUUHWVLWUFWURWVKXHZWULWUFWVKWURUUIWUEWUGUUJZYDXPWUSVXEVW
      KWULSZWVJWVIWUSVWKWVMWULVWKWURWVKUUKWVNYDVXEWVOWVJQZQGVWKWUFXHZWULVXEWVQG
      NWVPVXEWVQGVWKXHZGWVQWUFVWKXHWVRVWKWUFUULGVWKUUMUUNVXEWVRGNVWKGUUOUUQUURW
      CWVPWVQWULSVXEWVPWVQWULWULXHWULVWKWULWUFWULXQWULXRXSWAUUSUUTUVAWAWUQWULGS
      ZWVHWUQWUHESZWVSVXTWUEESZWUGESZWVTWUOVXTVYQWWAVWKEVXSUVBVWKEVXSUVGXLWUOWU
      FEVUQGEMVXPWVFEGHUVCGVWKEGHUVDXTUVEWWAWWBQWUHEEXHEWUEEWUGEXQEXRXSYAZWVTWU
      LEUNZGWUHEUVFHYDXLWCUVHYBYBYCUVIYNUVJUVKYEWEVYTVXTWUNVUPVYFVWMVXTWUNVXPVX
      TVWMWUNVXTVWKWUEVBPZVWMWUNRVXTVXSTMVWKWUEVXSUVLWWEUCVQVWKEVXSUVMVWKWUEVXS
      TUVNUVOZWWEVWMWUEOVBPZWUNVWKWUEOUVPWWGWUEOVEPWUGOVEPZWUNWUEOUWHWUGOVOPZWW
      HWUGUKMWWIWUFUVQWUGYFUVRWUGOUVSVGWUEWUGUWIUVTUWAXLUWBUWCUWDWUBWUHVVQMZWUM
      WUNQZWUKRZWUBWVTWWJVUPVUQVYTVYGWVTVVTVUQVXPVYGWVTVWMWUOVXTWVTVYFVXTWUOWVT
      WWCVLYGYEWEVUPWVTWWJRVYTVYGVUPWWJWVTWUHEDUWEUWFYHYIVUPWWJWWLRZVYTVYGVUPVV
      JWUDKVVNUHZRZBVVQUMZWWMVUPVVRWWPVUPVUQVVRVVSUWJWWOVVPBVVQWWNVVOVVJWUDVVLK
      CVVNVWAVURNWUCVVKGVWAVURYOYJUWGUWKUWLYKWWOWWLBWUHVVQVUSWUHNZVVJWWKWWNWUKW
      WQVVHWUMVVIWUNWWQVVGWULGVUSWUHYOYJVUSWUHOVEUWMUWNWWQWUDKVVNWUJWWQVVMWUIUK
      VUSWUHUWOUWPUWSUWTUWQXLYHYIUWRWUKVWAWUJMZWUDQZKVCWUBVXNWUDKWUJYLWUBWWSVXM
      KWUBWWSVXKVXLWUAVYGWWSVXKWUAVYGWWSQVYGVWAWUGULZWUESZVWKWWTUNSZQZQZVXKWUAW
      WSWXCVYGVUPVXPWWSWXCRZVWMVUPVUQVXEWXEVXPVVTVYIVXQWWRWXAWUDWXBWWRWXARVXQWW
      RVWAWUIMZWXAVWAWUIUKUXAWXFVWAWUHSZWXAKWUHUTWXGWWTWUEWUGWXGWWTWUHWUGULWUEW
      UGULVWAWUHWUGUXBWUEWUGUXCXSUXDVIXLYMVUQWUDVXEWXBVUQWUDQVXEWXBWUDVXEVWKWUC
      SZVUQWXBGWUCVWKUXEVUQVWKWVKUOZVMNWXHWXBVDVUQWXIVWKWUFUOVMVUQWVKWUFVWKVUQG
      TMWUFTMWVKWUFNVUQGWWDTHEUEUXFUXGGVWKTUXHWUFTXOXPUXIVWKGUXJUXKVWKVWAWUGUXL
      XLUXMUXQUXNUXOYAYGUXRWXDWWEWUEVWAVEPVXKVXTWWEVYFWXCWWFYHWXDWUEWWTVWAVEVXT
      WVDVYFWXCWWTWUENWVEVWKVXSWWTLUXPWEVWATMWWTVWASWWTVWAVEPKVQVWAWUGUXSWWTVWA
      TUXTUYPUYAVWKWUEVWAUYBUYCUYDUYEWWSVXLRWUBWWRVXLWUDVWAWUIUKUYFWCYMUYGYPUYH
      YIYNYQUYIUYJYIUYKUYQVXMVXOKVXLVXKVWAOVOPVXOVWAYFVWKVWAOUYLYRUYMVWKOUYNXPU
      YOVXEVXHUYRYKUYSKVXBUYTVUAVXFVXGVWAGMZVXCQZKVCVXDVXFVXCWXKKVXFVXCWXJVXFVX
      BGVWAVUPVXEVXBGSZVWMVUPVUQVXEWXLVVTVWKEGHVUHXTYSYTVUBYPVXCKGYLVUCYIYCVXAV
      XCVWDKGVXAVXBVWCVWAVUPVWTVXBVWCSZVWMVUPVUQVWTWXMVVTVUQVWIVWLWXMVWBVWKEGHV
      UDVUEXTYSYTVUFYIVUGYNYQYGYIYRYRVUIVVCVWEBUAVVEVUSVWBNZVVBVWDCKGWXNVURVWAN
      ZQVURVWAVVAVWCWXNWXOWGWXNVVAVWCNWXOVUSVWBVUTVUJWCVUKVULVUMYKABCEFGHJVUNVU
      O $.
  $}

$( (End of ML's mathbox.) $)
