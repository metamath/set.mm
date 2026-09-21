$[ set-main.mm $]
$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Mathbox for Stanislas Polu
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

  ${
    $d N k $.  $d k n $.
    $( Simple induction example.  (Contributed by Stanislas Polu,
       9-Mar-2020.) $)
    inductionexd $p |- ( N e. NN -> 3 || ( ( 4 ^ N ) + 5 ) ) $=
      ( c3 c4 cexp co c5 caddc cdvds wbr wceq oveq2 oveq1d breq2d wcel cmul 5cn
      c1 cz cmin a1i vk vn cv w3a 3z cn0 4z 1nn0 zexpcl 5nn nnzi zaddcl 3pm3.2i
      mp2an c9 3t3e9 numexp1 oveq1i 4cn 5p4e9 addcomli eqtri eqtr4i dvds0lem cn
      4nn0 wa 4nn nnnn0 nnexpcld nnzd adantr zaddcld simpr dvdsmultr1d dvdsmul1
      zmulcld dvds2subd cdc cc adddird 3cn 5t3e15 mulcomli oveq2d expp1d ax-1cn
      nncnd 3p1e4 eqcomi pncan3oi oveq2i subdii mulridi 3eqtr3ri oveq12d mulcld
      5nn0 deccl nn0cni addsubassd eqtr4d 3eqtr4rd breqtrrd ex nnind ) BCUAUCZD
      EZFGEZHIBCQDEZFGEZHIZBCUBUCZDEZFGEZHIZBCXMQGEZDEZFGEZHIZBCADEZFGEZHIUAUBA
      XGQJZXIXKBHYCXHXJFGXGQCDKLMXGXMJZXIXOBHYDXHXNFGXGXMCDKLMXGXQJZXIXSBHYEXHX
      RFGXGXQCDKLMXGAJZXIYBBHYFXHYAFGXGACDKLMBRNZYGXKRNZUDBBOEZXKJXLYGYGYHUEUEX
      JRNZFRNZYHCRNZQUFNYJUGUHCQUIUNFUJUKZXJFULUNUMYIUOXKUPXKCFGEUOXJCFGCVFUQUR
      FCUOPUSUTVAVBVCBBXKVDUNXMVENZXPXTYNXPVGZBXOCOEZBFOEZSEZXSHYOBYPYQYGYOUETZ
      YOXOCYOXNFYNXNRNXPYNXNYNCXMCVENYNVHTXMVIZVJZVKVLYKYOYMTZVMZYLYOUGTZVQYOBF
      YSUUBVQYOBXOCYSUUCUUDYNXPVNVOBYQHIZYOYGYKUUEUEYMBFVPUNTVRYNXSYRJXPYNYPQFV
      SZSEXNCOEZFCOEZGEZUUFSEZYRXSYNYPUUIUUFSYNXNFCYNXNUUAWHZFVTNYNPTZCVTNYNUST
      ZWALYNYQUUFYPSYQUUFJYNFBUUFPWBWCWDTWEYNXSUUGUUHUUFSEZGEUUJYNXRUUGFUUNGYNC
      XMUUMYTWFFUUNJYNFUUHFBOEZSEZUUNFCBSEZOEFQOEUUPFUUQQFOUUQQBGEZBSEQCUURBSUU
      RCBQCWBWGWIVAWJURQBWGWBWKVBWLFCBPUSWBWMFPWNWOUUFUUOUUHSUUOUUFWCWJWLVCTWPY
      NUUGUUHUUFYNXNCUUKUUMWQYNFCUULUUMWQUUFVTNYNUUFQFUHWRWSWTTXAXBXCVLXDXEXF
      $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  IMO Problems
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  IMO 1972 B2
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    wwlemuld.1 $e |- ( ph -> A e. RR ) $.
    wwlemuld.2 $e |- ( ph -> B e. RR ) $.
    wwlemuld.3 $e |- ( ph -> C e. RR ) $.
    wwlemuld.4 $e |- ( ph -> ( C x. A ) <_ ( C x. B ) ) $.
    wwlemuld.5 $e |- ( ph -> 0 < C ) $.
    $( Natural deduction form of ~ lemul2d .  (Contributed by Stanislas Polu,
       9-Mar-2020.) $)
    wwlemuld $p |- ( ph -> A <_ B ) $=
      ( cle wbr cmul co elrpd lemul2d mpbird ) ABCJKDBLMDCLMJKHABCDEFADGINOP $.
  $}

  ${
    leeq1d.1 $e |- ( ph -> A <_ C ) $.
    leeq1d.2 $e |- ( ph -> A = B ) $.
    leeq1d.3 $e |- ( ph -> A e. RR ) $.
    leeq1d.4 $e |- ( ph -> C e. RR ) $.
    $( Specialization of ~ breq1d to reals and less than.  (Contributed by
       Stanislas Polu, 9-Mar-2020.) $)
    leeq1d $p |- ( ph -> B <_ C ) $=
      ( cle eqbrtrrd ) ABCDIFEJ $.
  $}

  ${
    leeq2d.1 $e |- ( ph -> A <_ C ) $.
    leeq2d.2 $e |- ( ph -> C = D ) $.
    leeq2d.3 $e |- ( ph -> A e. RR ) $.
    leeq2d.4 $e |- ( ph -> C e. RR ) $.
    $( Specialization of ~ breq2d to reals and less than.  (Contributed by
       Stanislas Polu, 9-Mar-2020.) $)
    leeq2d $p |- ( ph -> A <_ D ) $=
      ( cle breqtrd ) ABCDIEFJ $.
  $}

  ${
    absmulrposd.1 $e |- ( ph -> 0 <_ A ) $.
    absmulrposd.2 $e |- ( ph -> A e. RR ) $.
    absmulrposd.3 $e |- ( ph -> B e. RR ) $.
    $( Specialization of absmuld with ~ absidd .  (Contributed by Stanislas
       Polu, 9-Mar-2020.) $)
    absmulrposd $p |- ( ph -> ( abs ` ( A x. B ) ) = ( A x. ( abs ` B ) ) ) $=
      ( cmul co cabs cfv recnd absmuld absidd oveq1d eqtrd ) ABCGHIJBIJZCIJZGHB
      QGHABCABEKACFKLAPBQGABEDMNO $.
  $}

  ${
    imadisjld.1 $e |- ( ph -> ( dom A i^i B ) = (/) ) $.
    $( Natural dduction form of one side of ~ imadisj .  (Contributed by
       Stanislas Polu, 9-Mar-2020.) $)
    imadisjld $p |- ( ph -> ( A " B ) = (/) ) $=
      ( cdm cin c0 wceq cima imadisj sylibr ) ABECFGHBCIGHDBCJK $.
  $}

  ${
    wnefimgd.1 $e |- ( ph -> A =/= (/) ) $.
    wnefimgd.2 $e |- ( ph -> F : A --> B ) $.
    $( The image of a mapping from A is nonempty if A is nonempty.
       (Contributed by Stanislas Polu, 9-Mar-2020.) $)
    wnefimgd $p |- ( ph -> ( F " A ) =/= (/) ) $=
      ( cdm cin wss wceq ssid fdmd sseqtrrid sseqin2 sylib eqnetrd imadisjlnd
      c0 ) ADBADGZBHZBRABSITBJABBSBKABCDFLMBSNOEPQ $.
  $}

  ${
    fco2d.1 $e |- ( ph -> G : A --> B ) $.
    fco2d.2 $e |- ( ph -> ( F |` B ) : B --> C ) $.
    $( Natural deduction form of ~ fco2 .  (Contributed by Stanislas Polu,
       9-Mar-2020.) $)
    fco2d $p |- ( ph -> ( F o. G ) : A --> C ) $=
      ( cres wf ccom fco2 syl2anc ) ACDECIJBCFJBDEFKJHGBCDEFLM $.
  $}

  ${
    wfximgfd.1 $e |- ( ph -> C e. A ) $.
    wfximgfd.2 $e |- ( ph -> F : A --> B ) $.
    $( The value of a function on its domain is in the image of the function.
       (Contributed by Stanislas Polu, 9-Mar-2020.) $)
    wfximgfd $p |- ( ph -> ( F ` C ) e. ( F " A ) ) $=
      ( ffnd fnfvimad ) ABDBEABCEGHFFI $.
  $}

  ${
    $d C x y $.  $d F x y $.  $d ph x y $.
    extoimad.1 $e |- ( ph -> F : RR --> RR ) $.
    extoimad.2 $e |- ( ph -> A. y e. RR ( abs ` ( F ` y ) ) <_ C ) $.
    $( If |f(x)| <= C for all x then it applies to all x in the image of |f(x)|
       (Contributed by Stanislas Polu, 9-Mar-2020.) $)
    extoimad $p |- ( ph -> A. x e. ( abs " ( F " RR ) ) x <_ C ) $=
      ( cv cle wbr cabs cr cima wral cfv wcel wceq wrex a1i cc ffvelcdmda recnd
      wa abscld ccom imaco eleq2d wf absf wss ax-resscn fssresd fco2d fvelimabd
      ffnd ssidd eqcom rexbidv bitrd adantr simpr fvco3d eqcomd eqeq2d rexbidva
      wb bitr4d bitr3d breq1d ralxfr2d mpbird ) ABHZDIJZBKELMMZNCHZEOZKOZDIJZCL
      NGAVMVRBCVQVNLLAVOLPZUCZVPVTVPALLVOEFUAUBUDAVLKEUEZLMZPZVLVNPVLVQQZCLRZAW
      BVNVLWBVNQAKELUFSUGAWCVLVOWAOZQZCLRZWEAWCWFVLQZCLRWHACLLVLWAALLWAALLLKEFA
      TLLKTLKUHAUISLTUJAUKSULUMUOALUPUNAWIWGCLWIWGVFAWFVLUQSURUSAWDWGCLVTVQWFVL
      VTWFVQVTLLVOKEALLEUHVSFUTAVSVAVBVCVDVEVGVHAWDUCVLVQDIAWDVAVIVJVK $.
  $}

  ${
    $d F c x $.  $d F x y $.  $d c ph x $.  $d ph x y $.
    imo72b2lem0.1 $e |- ( ph -> F : RR --> RR ) $.
    imo72b2lem0.2 $e |- ( ph -> G : RR --> RR ) $.
    imo72b2lem0.3 $e |- ( ph -> A e. RR ) $.
    imo72b2lem0.4 $e |- ( ph -> B e. RR ) $.
    imo72b2lem0.5 $e |- ( ph -> ( ( F ` ( A + B ) ) + ( F ` ( A - B ) ) )
                        = ( 2 x. ( ( F ` A ) x. ( G ` B ) ) ) ) $.
    imo72b2lem0.6 $e |- ( ph -> A. y e. RR ( abs ` ( F ` y ) ) <_ 1 ) $.
    $( Lemma for ~ imo72b2 .  (Contributed by Stanislas Polu, 9-Mar-2020.) $)
    imo72b2lem0 $p |- ( ph -> ( ( abs ` ( F ` A ) ) x. ( abs ` ( G ` B ) ) )
                       <_ sup ( ( abs " ( F " RR ) ) , RR , < ) ) $=
      ( vc vx cfv co cabs cr cle c2 cmul cima clt csup ffvelcdmd absmuld mulcld
      recnd abscld cc wf absf a1i fimassd ccom imaco ne0d wss ax-resscn fssresd
      c0 fco2d wnefimgd eqnetrrid cv wbr wral c1 1red wceq simpr breq2d ralbidv
      wa extoimad rspcedvd suprcld wcel 2re cc0 0le2 remulcld absmulrposd caddc
      fveq2d eqeltrd readdcld resubcld abstrid fvco3d wfximgfd eleqtrdi suprubd
      cmin 2cnd eqeltrrd le2addd 2timesd breqtrrd letrd eqbrtrrd 2pos wwlemuld
      ) ACEOZDFOZUAPZQOZXDQOXEQOUAPQERUBZUBZRUCUDZSAXDXEAXDARRCEGIUEZUHZAXEARRD
      FHJUEZUHZUFAXGXJTAXFAXDXEXLXNUGZUIAMNXIAUJRQXHUJRQUKAULUMZUNZAXIQEUOZRUBZ
      VAQERUPZARRXRARCIUQARRRQEGAUJRRQXPRUJURAUSUMUTVBZVCVDZANVEZMVEZSVFZNXIVGY
      CVHSVFZNXIVGMVHRAVIAYDVHVJZVNZYEYFNXIYHYDVHYCSAYGVKVLVMANBVHEGLVOVPZVQZTR
      VRAVSUMZATXFUAPZQOZTXGUAPTXJUAPZSATXFVTTSVFAWAUMYKAXDXEXKXMWBWCACDWDPZEOZ
      CDWNPZEOZWDPZQOZYMYNSAYSYLQKWEZAYTYPQOZYRQOZWDPZYNAYTYMRUUAAYLATXFAWOXOUG
      UIWFAUUBUUCAYPAYPARRYOEGACDIJWGZUEUHZUIZAYRAYRARRYQEGACDIJWHZUEUHZUIZWGAT
      XJYKYJWBAYPYRUUFUUIWIAUUDXJXJWDPYNSAUUBUUCXJXJUUGUUJYJYJAMNXIUUBXQYBYIAYO
      XROZUUBXIARRYOQEGUUEWJAUUKXSXIARRYOXRUUEYAWKXTWLWPWMAMNXIUUCXQYBYIAYQXROZ
      UUCXIARRYQQEGUUHWJAUULXSXIARRYQXRUUHYAWKXTWLWPWMWQAXJAXJYJUHWRWSWTXAXAVTT
      UCVFAXBUMXCXA $.
  $}

  ${
    $d A x y $.  $d A z $.  $d B z $.
    suprleubrd.1 $e |- ( ph -> A C_ RR ) $.
    suprleubrd.2 $e |- ( ph -> A =/= (/) ) $.
    suprleubrd.3 $e |- ( ph -> E. x e. RR A. y e. A y <_ x ) $.
    suprleubrd.4 $e |- ( ph -> B e. RR ) $.
    suprleubrd.5 $e |- ( ph -> A. z e. A z <_ B ) $.
    $( Natural deduction form of specialized ~ suprleub .  (Contributed by
       Stanislas Polu, 9-Mar-2020.) $)
    suprleubrd $p |- ( ph -> sup ( A , RR , < ) <_ B ) $=
      ( cv cle wbr wral cr clt csup wss c0 wne wrex wb suprleub syl31anc bicomd
      wcel biimpd imp mpdan ) ADLFMNDEOZEPQRFMNZKAUKULAUKULAULUKAEPSETUACLBLMNC
      EOBPUBFPUGULUKUCGHIJBCDEFUDUEUFUHUIUJ $.
  $}

  ${
    $d C c v z $.  $d C t z $.  $d F c v z $.  $d F t z $.  $d c ph v z $.
    $d ph t z $.
    imo72b2lem2.1 $e |- ( ph -> F : RR --> RR ) $.
    imo72b2lem2.2 $e |- ( ph -> C e. RR ) $.
    imo72b2lem2.3 $e |- ( ph -> A. z e. RR ( abs ` ( F ` z ) ) <_ C ) $.
    $( Lemma for ~ imo72b2 .  (Contributed by Stanislas Polu, 9-Mar-2020.) $)
    imo72b2lem2 $p |- ( ph -> sup ( ( abs " ( F " RR ) ) , RR , < ) <_ C ) $=
      ( vc vv vt cabs cr cima wss a1i cc c0 necomd wceq cle ccom eqcomi imassrn
      imaco crn wf absf ax-resscn fssresd fco2d frnd sstrd eqsstrid wne cc0 0re
      ne0ii wnefimgd neeqtrrd cv wral wa simpr breq2d ralbidv extoimad rspcedvd
      wbr suprleubrd ) AHIJKDLMMZCAVJKDUAZLMZLVLVJKDLUDUBZAVLVKUEZLVLVNNAVKLUCO
      ALLVKALLLKDEAPLLKPLKUFAUGOLPNAUHOUIUJZUKULUMAQVJAQVLVJAVLQALLVKLQUNAUOLUP
      UQOVOURRVJVLSAVMOUSRAIUTZHUTZTVHZIVJVAVPCTVHZIVJVAHCLFAVQCSZVBZVRVSIVJWAV
      QCVPTAVTVCVDVEAIBCDEGVFVGFAJBCDEGVFVI $.
  $}

  ${
    $d A x y $.  $d A z $.  $d B z $.
    suprlubrd.1 $e |- ( ph -> A C_ RR ) $.
    suprlubrd.2 $e |- ( ph -> A =/= (/) ) $.
    suprlubrd.3 $e |- ( ph -> E. x e. RR A. y e. A y <_ x ) $.
    suprlubrd.4 $e |- ( ph -> B e. RR ) $.
    suprlubrd.5 $e |- ( ph -> E. z e. A B < z ) $.
    $( Natural deduction form of specialized ~ suprlub .  (Contributed by
       Stanislas Polu, 9-Mar-2020.) $)
    suprlubrd $p |- ( ph -> B < sup ( A , RR , < ) ) $=
      ( cv clt wbr wrex cr csup wss c0 wne wral wcel wb suprlub syl31anc bicomd
      cle biimpd imp mpdan ) AFDLMNDEOZFEPMQMNZKAUKULAUKULAULUKAEPRESTCLBLUGNCE
      UABPOFPUBULUKUCGHIJBCDEFUDUEUFUHUIUJ $.
  $}

  ${
    $d F c t $.  $d F x z $.  $d F t y $.  $d c ph t $.  $d ph x z $.
    $d ph t y $.
    imo72b2lem1.1 $e |- ( ph -> F : RR --> RR ) $.
    imo72b2lem1.7 $e |- ( ph -> E. x e. RR ( F ` x ) =/= 0 ) $.
    imo72b2lem1.6 $e |- ( ph -> A. y e. RR ( abs ` ( F ` y ) ) <_ 1 ) $.
    $( Lemma for ~ imo72b2 .  (Contributed by Stanislas Polu, 9-Mar-2020.) $)
    imo72b2lem1 $p |- ( ph -> 0 < sup ( ( abs " ( F " RR ) ) , RR , < ) ) $=
      ( vc vt vz cabs cr cima cc0 cc a1i cv wbr c1 wa ccom imaco crn imassrn wf
      absf wss ax-resscn fssresd fco2d frnd sstrid eqsstrrid wne ne0ii wnefimgd
      c0 0re eqnetrrid cle wral 1red wceq breq2d ralbidv extoimad rspcedvd 0red
      simpr cfv clt wrex wcel adantr simprl fvco3d funfvima2d eleqtrdi eqeltrrd
      adantrr ffvelcdmda recnd simprr absrpcld rpgt0d rexlimddv suprlubrd ) AHI
      JKDLMMZNAWHKDUAZLMZLKDLUBZAWJWIUCLWILUDALLWIALLLKDEAOLLKOLKUEAUFPLOUGAUHP
      UIUJZUKULUMAWHWJUQWKALLWILUQUNANLURUOPWLUPUSAIQZHQZUTRZIWHVAWMSUTRZIWHVAH
      SLAVBAWNSVCZTZWOWPIWHWRWNSWMUTAWQVIVDVEAICSDEGVFVGAVHABQZDVJZNUNZNJQZVKRZ
      JWHVLBLFAWSLVMZXATZTZXCNWTKVJZVKRJXGWHXFWSWIVJZXGWHXFLLWSKDALLDUEXEEVNAXD
      XAVOVPXFXHWJWHAXDXHWJVMXAALLWIWSWLVQVTWKVRVSXFXBXGVCZTXBXGNVKXFXIVIVDXFXG
      XFWTXFWTAXDWTLVMXAALLWSDEWAVTWBAXDXAWCWDWEVGWFWG $.
  $}

  ${
    lemuldiv3d.1 $e |- ( ph -> ( B x. A ) <_ C ) $.
    lemuldiv3d.2 $e |- ( ph -> 0 < A ) $.
    lemuldiv3d.3 $e |- ( ph -> A e. RR ) $.
    lemuldiv3d.4 $e |- ( ph -> B e. RR ) $.
    lemuldiv3d.5 $e |- ( ph -> C e. RR ) $.
    $( 'Less than or equal to' relationship between division and
       multiplication.  (Contributed by Stanislas Polu, 9-Mar-2020.) $)
    lemuldiv3d $p |- ( ph -> B <_ ( C / A ) ) $=
      ( cmul co cle wbr cdiv cr wcel cc0 clt wb lemuldiv syl112anc mpbid ) ACBJ
      KDLMZCDBNKLMZEACOPDOPBOPQBRMUCUDSHIGFCDBTUAUB $.
  $}

  ${
    lemuldiv4d.1 $e |- ( ph -> B <_ ( C / A ) ) $.
    lemuldiv4d.2 $e |- ( ph -> 0 < A ) $.
    lemuldiv4d.3 $e |- ( ph -> A e. RR ) $.
    lemuldiv4d.4 $e |- ( ph -> B e. RR ) $.
    lemuldiv4d.5 $e |- ( ph -> C e. RR ) $.
    $( 'Less than or equal to' relationship between division and
       multiplication.  (Contributed by Stanislas Polu, 9-Mar-2020.) $)
    lemuldiv4d $p |- ( ph -> ( B x. A ) <_ C ) $=
      ( cdiv co cle wbr cmul cr wcel cc0 clt wb lemuldiv syl112anc bicomd mpbid
      ) ACDBJKLMZCBNKDLMZEAUEUDACOPDOPBOPQBRMUEUDSHIGFCDBTUAUBUC $.
  $}

  ${
    $d B c t $.  $d B u v $.  $d B x $.  $d B t y $.  $d F c t $.  $d F u v $.
    $d F x $.  $d F t y $.  $d G c t $.  $d G u v $.  $d G x $.  $d G t y $.
    $d c ph t $.  $d ph u v $.  $d ph x $.  $d ph t y $.  $d u y $.
    imo72b2.1 $e |- ( ph -> F : RR --> RR ) $.
    imo72b2.2 $e |- ( ph -> G : RR --> RR ) $.
    imo72b2.4 $e |- ( ph -> B e. RR ) $.
    imo72b2.5 $e |- ( ph -> A. u e. RR A. v e. RR ( ( F ` ( u + v ) ) + ( F ` (
                    u - v ) ) ) = ( 2 x. ( ( F ` u ) x. ( G ` v ) ) ) ) $.
    imo72b2.6 $e |- ( ph -> A. y e. RR ( abs ` ( F ` y ) ) <_ 1 ) $.
    imo72b2.7 $e |- ( ph -> E. x e. RR ( F ` x ) =/= 0 ) $.
    $( IMO 1972 B2.  (14th International Mathematical Olympiad in Poland,
       problem B2).  (Contributed by Stanislas Polu, 9-Mar-2020.) $)
    imo72b2 $p |- ( ph -> ( abs ` ( G ` B ) ) <_ 1 ) $=
      ( cfv c1 cr adantr co a1i vc vt cabs ffvelcdmd recnd abscld clt wbr simpr
      1red wa wf wcel cima csup cdiv cle cmul cc ax-resscn imaco eqcomi crn wss
      ccom imassrn absf fssresd fco2d frnd sstrd eqsstrid c0 wne ne0ii wnefimgd
      cc0 necomd wceq neeqtrrd cv wral breq2d ralbidv extoimad rspcedvd suprcld
      0re sselid mulcomd 0lt1 lttrd gt0ne0d redivcld cmin oveq2d fveq2d oveq12d
      caddc c2 eqeq12d ralcom bilani mpdan rspcdv2 r19.21bi adantlr imo72b2lem0
      ad2antrr cxr 0xr 1xr rexrd simplr xrlttrd ffvelcdmda lemuldiv3d ralrimiva
      imo72b2lem2 lemuldiv4d eqbrtrrd imo72b2lem1 sseldd dividd eqcomd breqtrrd
      wrex lensymd pm2.65da nltled ) AFHOZUCOZPAYKAYKAQQFHJKUDUEUFAUJZAPYLUGUHZ
      YNAYNUIZAYNUKZYLPYPYKYPYKYPQQFHAQQHULZYNJRZAFQUMZYNKRZUDUEUFZAPQUMYNYMRZY
      PYLUCGQUNUNZQUGUOZUUDUPSZPUQYPUUDYLUUDYPUUDYLURSYLUUDURSUUDUQYPUUDYLYPQUS
      UUDUTYPUAUBUUCYPUUCUCGVEZQUNZQUUGUUCUCGQVAVBZYPUUGUUFVCZQUUGUUIVDYPUUFQVF
      TYPQQUUFYPQQQUCGAQQGULZYNIRZYPUSQQUCUSQUCULYPVGTQUSVDYPUTTZVHVIZVJVKVLYPV
      MUUCYPVMUUGUUCYPUUGVMYPQQUUFQVMVNYPVQQWHVOTUUMVPVRUUCUUGVSYPUUHTVTVRYPUBW
      AZUAWAZUQUHZUBUUCWBUUNPUQUHZUBUUCWBZUAPQUUBYPUUOPVSZUKZUUPUUQUBUUCUUTUUOP
      UUNUQYPUUSUIWCWDAUURYNAUBCPGIMWERWFWGZWIYPQUSYLUTUUAWIWJYPYLUUDUUDYPEUUDY
      LUPSZGUUKYPUUDYLUVAUUAYPYLYPVQPYLVQQUMYPWHTUUBUUAVQPUGUHZYPWKTYOWLZWMWNYP
      EWAZGOZUCOZUVBUQUHEQYPUVEQUMZUKZYLUVGUUDUVICUVEFGHYPUUJUVHUUKRYPYQUVHYRRY
      PUVHUIYPYSUVHYTRAUVHUVEFWSSZGOZUVEFWOSZGOZWSSZWTUVFYKURSZURSZVSZYNAUVQEQA
      UVEDWAZWSSZGOZUVEUVRWOSZGOZWSSZWTUVFUVRHOZURSZURSZVSZEQWBZUVQEQWBDFQAUVRF
      VSZUKZUWGUVQEQUWJUWCUVNUWFUVPUWJUVTUVKUWBUVMWSUWJUVSUVJGUWJUVRFUVEWSAUWIU
      IZWPWQUWJUWAUVLGUWJUVRFUVEWOUWKWPWQWRUWJUWEUVOWTURUWJUWDYKUVFURUWJUVRFHUW
      KWQWPWPXAWDKAUWGDQWBEQWBZUWHDQWBZLUWLUWMAUWGEDQQXBXCXDXEXFXGACWAGOUCOPUQU
      HCQWBZYNUVHMXIXHUVIVQPYLVQXJUMUVIXKTPXJUMUVIXLTUVIYLYPYLQUMUVHUUARZXMUVCU
      VIWKTAYNUVHXNXOUWOUVIUVFUVIUVFYPQQUVEGUUKXPUEUFYPUUDQUMUVHUVARXQXRXSUVDUU
      AUVAUVAXTYAYPBCGUUKABWAGOVQVNBQYGYNNRAUWNYNMRYBZUVAUUAUVAXQYPUUEPYPUUDYPQ
      USUUDUULUVAYCYPUUDUWPWMYDYEYFYHYIYJ $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  INT Inequalities Proof Generator
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  This section formalizes theorems necessary to reproduce the equality and
  inequality generator described in "Neural Theorem Proving on Inequality
  Problems" ~ http://aitp-conference.org/2020/abstract/paper_18.pdf .

  Other theorems required: ~ 0red ~ 1red ~ readdcld ~ remulcld ~ eqcomd .

$)

  ${
    int-addcomd.1 $e |- ( ph -> B e. RR ) $.
    int-addcomd.2 $e |- ( ph -> C e. RR ) $.
    int-addcomd.3 $e |- ( ph -> A = B ) $.
    $( AdditionCommutativity generator rule.  (Contributed by Stanislas Polu,
       7-Apr-2020.) $)
    int-addcomd $p |- ( ph -> ( B + C ) = ( C + A ) ) $=
      ( caddc co recnd addcomd eqcomd oveq2d eqtrd ) ACDHIDCHIDBHIACDACEJADFJKA
      CBDHABCGLMN $.
  $}

  ${
    int-addassocd.1 $e |- ( ph -> A e. RR ) $.
    int-addassocd.2 $e |- ( ph -> C e. RR ) $.
    int-addassocd.3 $e |- ( ph -> D e. RR ) $.
    int-addassocd.4 $e |- ( ph -> A = B ) $.
    $( AdditionAssociativity generator rule.  (Contributed by Stanislas Polu,
       7-Apr-2020.) $)
    int-addassocd $p |- ( ph -> ( B + ( C + D ) ) = ( ( A + C ) + D ) ) $=
      ( caddc co recnd addassd oveq1d eqtr2d ) ABDJKEJKBDEJKZJKCPJKABDEABFLADGL
      AEHLMABCPJINO $.
  $}

  ${
    int-addsimpd.1 $e |- ( ph -> A e. RR ) $.
    int-addsimpd.2 $e |- ( ph -> A = B ) $.
    $( AdditionSimplification generator rule.  (Contributed by Stanislas Polu,
       7-Apr-2020.) $)
    int-addsimpd $p |- ( ph -> 0 = ( A - B ) ) $=
      ( cmin co cc0 recnd subeq0bd eqcomd ) ABCFGHABCABDIEJK $.
  $}

  ${
    int-mulcomd.1 $e |- ( ph -> B e. RR ) $.
    int-mulcomd.2 $e |- ( ph -> C e. RR ) $.
    int-mulcomd.3 $e |- ( ph -> A = B ) $.
    $( MultiplicationCommutativity generator rule.  (Contributed by Stanislas
       Polu, 7-Apr-2020.) $)
    int-mulcomd $p |- ( ph -> ( B x. C ) = ( C x. A ) ) $=
      ( cmul co recnd mulcomd eqcomd oveq2d eqtrd ) ACDHIDCHIDBHIACDACEJADFJKAC
      BDHABCGLMN $.
  $}

  ${
    int-mulassocd.1 $e |- ( ph -> B e. RR ) $.
    int-mulassocd.2 $e |- ( ph -> C e. RR ) $.
    int-mulassocd.3 $e |- ( ph -> D e. RR ) $.
    int-mulassocd.4 $e |- ( ph -> A = B ) $.
    $( MultiplicationAssociativity generator rule.  (Contributed by Stanislas
       Polu, 7-Apr-2020.) $)
    int-mulassocd $p |- ( ph -> ( B x. ( C x. D ) ) = ( ( A x. C ) x. D ) ) $=
      ( cmul co recnd mulassd eqcomd oveq1d eqtr3d ) ACDJKZEJKCDEJKJKBDJKZEJKAC
      DEACFLADGLAEHLMAQREJACBDJABCINOOP $.
  $}

  ${
    int-mulsimpd.1 $e |- ( ph -> B e. RR ) $.
    int-mulsimpd.2 $e |- ( ph -> A = B ) $.
    int-mulsimpd.3 $e |- ( ph -> B =/= 0 ) $.
    $( MultiplicationSimplification generator rule.  (Contributed by Stanislas
       Polu, 7-Apr-2020.) $)
    int-mulsimpd $p |- ( ph -> 1 = ( A / B ) ) $=
      ( cdiv co c1 recnd diveq1bd eqcomd ) ABCGHIABCACDJFEKL $.
  $}

  ${
    int-leftdistd.1 $e |- ( ph -> B e. RR ) $.
    int-leftdistd.2 $e |- ( ph -> C e. RR ) $.
    int-leftdistd.3 $e |- ( ph -> D e. RR ) $.
    int-leftdistd.4 $e |- ( ph -> A = B ) $.
    $( AdditionMultiplicationLeftDistribution generator rule.  (Contributed by
       Stanislas Polu, 7-Apr-2020.) $)
    int-leftdistd $p |- ( ph -> ( ( C + D ) x. B ) =
                        ( ( C x. A ) + ( D x. A ) ) ) $=
      ( caddc co cmul recnd adddird mulcld addcomd eqcomd oveq2d oveq12d eqtrd
      3eqtrd ) ADEJKCLKDCLKZECLKZJKZUCUBJKZDBLKZEBLKZJKZADECADGMZAEHMZACFMZNAUB
      UCADCUIUKOZAECUJUKOZPAUEUDUHAUCUBUMULPAUBUFUCUGJACBDLABCIQZRACBELUNRSTUA
      $.
  $}

  ${
    int-rightdistd.1 $e |- ( ph -> B e. RR ) $.
    int-rightdistd.2 $e |- ( ph -> C e. RR ) $.
    int-rightdistd.3 $e |- ( ph -> D e. RR ) $.
    int-rightdistd.4 $e |- ( ph -> A = B ) $.
    $( AdditionMultiplicationRightDistribution generator rule.  (Contributed by
       Stanislas Polu, 7-Apr-2020.) $)
    int-rightdistd $p |- ( ph -> ( B x. ( C + D ) ) =
                         ( ( A x. C ) + ( A x. D ) ) ) $=
      ( caddc co cmul recnd addcld mulcomd eqcomd eqtrd oveq12d joinlmuladdmuld
      oveq1d ) ACDEJKZLKUACLKBDLKZBELKZJKZACUAACFMZADEADGMZAEHMZNOADCEUDUFUEUGA
      DCLKZUBECLKZUCJAUHCDLKUBADCUFUEOACBDLABCIPZTQAUICELKUCAECUGUEOACBELUJTQRS
      Q $.
  $}

  ${
    int-sqdefd.1 $e |- ( ph -> B e. RR ) $.
    int-sqdefd.2 $e |- ( ph -> A = B ) $.
    $( SquareDefinition generator rule.  (Contributed by Stanislas Polu,
       7-Apr-2020.) $)
    int-sqdefd $p |- ( ph -> ( A x. B ) = ( A ^ 2 ) ) $=
      ( c2 cexp co cmul oveq1d recnd sqvald wceq eqcom imbi2i mpbi eqtrd eqcomd
      wi ) ABFGHZBCIHZATCFGHZUAABCFGEJAUBCCIHUAACACDKLACBCIABCMZSACBMZSEUCUDABC
      NOPJQQR $.
  $}

  ${
    int-mul11d.1 $e |- ( ph -> A e. RR ) $.
    int-mul11d.2 $e |- ( ph -> A = B ) $.
    $( First MultiplicationOne generator rule.  (Contributed by Stanislas Polu,
       7-Apr-2020.) $)
    int-mul11d $p |- ( ph -> ( A x. 1 ) = B ) $=
      ( c1 cmul co recnd mulridd eqtrd ) ABFGHBCABABDIJEK $.
  $}

  ${
    int-mul12d.1 $e |- ( ph -> A e. RR ) $.
    int-mul12d.2 $e |- ( ph -> A = B ) $.
    $( Second MultiplicationOne generator rule.  (Contributed by Stanislas
       Polu, 7-Apr-2020.) $)
    int-mul12d $p |- ( ph -> ( 1 x. A ) = B ) $=
      ( c1 cmul co recnd mullidd eqtrd ) AFBGHBCABABDIJEK $.
  $}

  ${
    int-add01d.1 $e |- ( ph -> A e. RR ) $.
    int-add01d.2 $e |- ( ph -> A = B ) $.
    $( First AdditionZero generator rule.  (Contributed by Stanislas Polu,
       7-Apr-2020.) $)
    int-add01d $p |- ( ph -> ( A + 0 ) = B ) $=
      ( cc0 caddc co recnd addridd eqtrd ) ABFGHBCABABDIJEK $.
  $}

  ${
    int-add02d.1 $e |- ( ph -> A e. RR ) $.
    int-add02d.2 $e |- ( ph -> A = B ) $.
    $( Second AdditionZero generator rule.  (Contributed by Stanislas Polu,
       7-Apr-2020.) $)
    int-add02d $p |- ( ph -> ( 0 + A ) = B ) $=
      ( cc0 caddc co recnd addlidd eqtrd ) AFBGHBCABABDIJEK $.
  $}

  ${
    int-sqgeq0d.1 $e |- ( ph -> A e. RR ) $.
    int-sqgeq0d.2 $e |- ( ph -> B e. RR ) $.
    int-sqgeq0d.3 $e |- ( ph -> A = B ) $.
    $( SquareGEQZero generator rule.  (Contributed by Stanislas Polu,
       7-Apr-2020.) $)
    int-sqgeq0d $p |- ( ph -> 0 <_ ( A x. B ) ) $=
      ( cc0 c2 cexp co cmul cle sqge0d oveq1d recnd sqvald wceq wi eqcom eqtrd
      imbi2i mpbi breqtrd ) AGBHIJZBCKJZLABDMAUDCHIJZUEABCHIFNAUFCCKJUEACACEOPA
      CBCKABCQZRACBQZRFUGUHABCSUAUBNTTUC $.
  $}

  ${
    int-eqprincd.1 $e |- ( ph -> A = B ) $.
    int-eqprincd.2 $e |- ( ph -> C = D ) $.
    $( PrincipleOfEquality generator rule.  (Contributed by Stanislas Polu,
       7-Apr-2020.) $)
    int-eqprincd $p |- ( ph -> ( A + C ) = ( B + D ) ) $=
      ( caddc oveq12d ) ABCDEHFGI $.
  $}

  ${
    int-eqtransd.1 $e |- ( ph -> A = B ) $.
    int-eqtransd.2 $e |- ( ph -> B = C ) $.
    $( EqualityTransitivity generator rule.  (Contributed by Stanislas Polu,
       7-Apr-2020.) $)
    int-eqtransd $p |- ( ph -> A = C ) $=
      ( eqtrd ) ABCDEFG $.
  $}

  ${
    int-eqmvtd.1 $e |- ( ph -> C e. RR ) $.
    int-eqmvtd.2 $e |- ( ph -> D e. RR ) $.
    int-eqmvtd.3 $e |- ( ph -> A = B ) $.
    int-eqmvtd.4 $e |- ( ph -> A = ( C + D ) ) $.
    $( EquMoveTerm generator rule.  (Contributed by Stanislas Polu,
       7-Apr-2020.) $)
    int-eqmvtd $p |- ( ph -> C = ( B - D ) ) $=
      ( cmin co caddc eqtr3d oveq1d recnd pncand eqtrd eqcomd ) ACEJKZDASDELKZE
      JKDACTEJABCTHIMNADEADFOAEGOPQR $.
  $}

  ${
    int-eqineqd.1 $e |- ( ph -> B e. RR ) $.
    int-eqineqd.2 $e |- ( ph -> A = B ) $.
    $( EquivalenceImpliesDoubleInequality generator rule.  (Contributed by
       Stanislas Polu, 7-Apr-2020.) $)
    int-eqineqd $p |- ( ph -> B <_ A ) $=
      ( eqcomd eqled ) ACBDABCEFG $.
  $}

  ${
    int-ineqmvtd.1 $e |- ( ph -> B e. RR ) $.
    int-ineqmvtd.2 $e |- ( ph -> C e. RR ) $.
    int-ineqmvtd.3 $e |- ( ph -> D e. RR ) $.
    int-ineqmvtd.4 $e |- ( ph -> B <_ A ) $.
    int-ineqmvtd.5 $e |- ( ph -> A = ( C + D ) ) $.
    $( IneqMoveTerm generator rule.  (Contributed by Stanislas Polu,
       7-Apr-2020.) $)
    int-ineqmvtd $p |- ( ph -> ( B - D ) <_ C ) $=
      ( cmin co cle wbr caddc breqtrd lesubaddd mpbird ) ACEKLDMNCDEOLZMNACBSMI
      JPACEDFHGQR $.
  $}

  ${
    int-ineq1stprincd.1 $e |- ( ph -> A e. RR ) $.
    int-ineq1stprincd.2 $e |- ( ph -> B e. RR ) $.
    int-ineq1stprincd.3 $e |- ( ph -> C e. RR ) $.
    int-ineq1stprincd.4 $e |- ( ph -> D e. RR ) $.
    int-ineq1stprincd.5 $e |- ( ph -> B <_ A ) $.
    int-ineq1stprincd.6 $e |- ( ph -> D <_ C ) $.
    $( FirstPrincipleOfInequality generator rule.  (Contributed by Stanislas
       Polu, 7-Apr-2020.) $)
    int-ineq1stprincd $p |- ( ph -> ( B + D ) <_ ( A + C ) ) $=
      ( le2addd ) ACEBDGIFHJKL $.
  $}

  ${
    int-ineq2ndprincd.1 $e |- ( ph -> A e. RR ) $.
    int-ineq2ndprincd.2 $e |- ( ph -> B e. RR ) $.
    int-ineq2ndprincd.3 $e |- ( ph -> C e. RR ) $.
    int-ineq2ndprincd.4 $e |- ( ph -> B <_ A ) $.
    int-ineq2ndprincd.5 $e |- ( ph -> 0 <_ C ) $.
    $( SecondPrincipleOfInequality generator rule.  (Contributed by Stanislas
       Polu, 7-Apr-2020.) $)
    int-ineq2ndprincd $p |- ( ph -> ( B x. C ) <_ ( A x. C ) ) $=
      ( lemul1ad ) ACBDFEGIHJ $.
  $}

  ${
    int-ineqtransd.1 $e |- ( ph -> A e. RR ) $.
    int-ineqtransd.2 $e |- ( ph -> B e. RR ) $.
    int-ineqtransd.3 $e |- ( ph -> C e. RR ) $.
    int-ineqtransd.4 $e |- ( ph -> B <_ A ) $.
    int-ineqtransd.5 $e |- ( ph -> C <_ B ) $.
    $( InequalityTransitivity generator rule.  (Contributed by Stanislas Polu,
       7-Apr-2020.) $)
    int-ineqtransd $p |- ( ph -> C <_ A ) $=
      ( letrd ) ADCBGFEIHJ $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  N-Digit Addition Proof Generator
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  This section formalizes theorems used in an n-digit addition proof generator.

  Other theorems required: ~ deccl ~ addcomli ~ 00id ~ addridi ~ addlidi ~ eqid
  ~ dec0h ~ decadd ~ decaddc .

$)

  ${
    unitadd.1 $e |- ( A + B ) = F $.
    unitadd.2 $e |- ( C + 1 ) = B $.
    unitadd.3 $e |- A e. NN0 $.
    unitadd.4 $e |- C e. NN0 $.
    $( Theorem used in conjunction with ~ decaddc to absorb carry when
       generating n-digit addition synthetic proofs.  (Contributed by Stanislas
       Polu, 7-Apr-2020.) $)
    unitadd $p |- ( ( A + C ) + 1 ) = F $=
      ( caddc co c1 nn0cni ax-1cn addassi eqcomi oveq2i eqtr3i eqtri ) ACIJKIJA
      CKIJZIJZDACKAGLCHLMNABIJTDBSAISBFOPEQR $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  AM-GM (for k = 2,3,4)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    gsumws3.0 $e |- B = ( Base ` G ) $.
    gsumws3.1 $e |- .+ = ( +g ` G ) $.
    $( Valuation of a length 3 word in a monoid.  (Contributed by Stanislas
       Polu, 9-Sep-2020.) $)
    gsumws3 $p |- ( ( G e. Mnd /\ ( S e. B /\ ( T e. B /\ U e. B ) ) ) ->
                  ( G gsum <" S T U "> ) = ( S .+ ( T .+ U ) ) ) $=
      ( cmnd wcel wa cs3 cgsu co cs1 cs2 cconcat wceq s1s2 a1i simprrl gsumccat
      oveq2d cword simpl s1cld simprrr syl3anc gsumws1 ad2antrl gsumws2 adantrl
      simprl s2cld 3expb oveq12d 3eqtrd ) FIJZCAJZDAJZEAJZKZKZKZFCDELZMNFCOZDEP
      ZQNZMNZFVFMNZFVGMNZBNZCDEBNZBNVDVEVHFMVEVHRVDCDESTUCVDURVFAUDZJVGVNJVIVLR
      URVCUEVDCAURUSVBUMUFVDDEAURUSUTVAUAURUSUTVAUGUNABFVFVGGHUBUHVDVJCVKVMBUSV
      JCRURVBACFGUIUJURVBVKVMRZUSURUTVAVOABDEFGHUKUOULUPUQ $.
  $}

  ${
    gsumws4.0 $e |- B = ( Base ` G ) $.
    gsumws4.1 $e |- .+ = ( +g ` G ) $.
    $( Valuation of a length 4 word in a monoid.  (Contributed by Stanislas
       Polu, 10-Sep-2020.) $)
    gsumws4 $p |- ( ( G e. Mnd /\ ( S e. B /\ ( T e. B /\
                  ( U e. B /\ V e. B ) ) ) ) ->
                  ( G gsum <" S T U V "> ) = ( S .+ ( T .+ ( U .+ V ) ) ) ) $=
      ( cmnd wcel wa cs4 cgsu co cs1 cs3 wceq simprrl adantl cconcat a1i oveq2d
      s1s3 cword simpl simprl simprrr gsumccat syl3anc gsumws1 ad2antrl gsumws3
      s1cld s3cld adantrl oveq12d 3eqtrd ) FJKZCAKZDAKZEAKZGAKZLZLZLZLZFCDEGMZN
      OFCPZDEGQZUAOZNOZFVINOZFVJNOZBOZCDEGBOBOZBOVGVHVKFNVHVKRVGCDEGUDUBUCVGUSV
      IAUEZKVJVQKVLVORUSVFUFVGCAUSUTVEUGUNVGDEGAUSUTVAVDSVFVBUSUTVAVBVCSTVFVCUS
      UTVAVBVCUHTUOABFVIVJHIUIUJVGVMCVNVPBUTVMCRUSVEACFHUKULUSVEVNVPRUTABDEGFHI
      UMUPUQUR $.
  $}

  ${
    amgm2d.0 $e |- ( ph -> A e. RR+ ) $.
    amgm2d.1 $e |- ( ph -> B e. RR+ ) $.
    $( Arithmetic-geometric mean inequality for ` n = 2 ` , derived from
       ~ amgmlem .  (Contributed by Stanislas Polu, 8-Sep-2020.) $)
    amgm2d $p |- ( ph -> ( ( A x. B ) ^c ( 1 / 2 ) ) <_ ( ( A + B ) / 2 ) ) $=
      ( ccnfld cfv co c1 cc0 c2 cfzo cdiv ccxp cmul wcel crp cc wceq mp1i chash
      cmgp cs2 cgsu caddc cle eqid cfn fzofi a1i c0 cn lbfzo0 mpbir ne0ii cword
      wne 2nn wf s2cld wrdf s2len eqcomi oveq2i feq2i sylibr syl amgmlem cnring
      cmnd ringmgp rpcnd cnfldbas mgpbas cnfldmul mgpplusg gsumws2 syl3anc 2nn0
      crg cn0 hashfzo0 oveq2d oveq12d ringmnd cnfldadd 3brtr3d ) AFUBGZBCUCZUDH
      ZIJKLHZUAGZMHZNHFWIUDHZWLMHBCOHZIKMHZNHBCUEHZKMHUFAWKWIWHWHUGZWKUHPAJKUIU
      JWKUKUQAJWKJWKPKULPURKUMUNUOUJAWIQUPPZWKQWIUSZABCQDEUTWSJWIUAGZLHZQWIUSWT
      QWIVAWKXBQWIKXAJLXAKBCVBVCVDVEVFVGVHAWJWOWMWPNAWHVJPZBRPZCRPZWJWOSFVTPZXC
      AVIFWHWRVKTABDVLZACEVLZROBCWHRFWHWRVMVNFOWHWRVOVPVQVRAWLKIMKWAPWLKSAVSKWB
      TZWCWDAWNWQWLKMAFVJPZXDXEWNWQSXFXJAVIFWETXGXHRUEBCFVMWFVQVRXIWDWG $.
  $}

  ${
    amgm3d.0 $e |- ( ph -> A e. RR+ ) $.
    amgm3d.1 $e |- ( ph -> B e. RR+ ) $.
    amgm3d.2 $e |- ( ph -> C e. RR+ ) $.
    $( Arithmetic-geometric mean inequality for ` n = 3 ` .  (Contributed by
       Stanislas Polu, 11-Sep-2020.) $)
    amgm3d $p |- ( ph -> ( ( A x. ( B x. C ) ) ^c ( 1 / 3 ) ) <_
                 ( ( A + ( B + C ) ) / 3 ) ) $=
      ( ccnfld co c1 cc0 c3 cfzo cdiv cmul caddc wcel mp1i crp cc cmgp cfv cgsu
      cs3 chash ccxp cle eqid cfn fzofi a1i c0 wne cn 3nn lbfzo0 mpbir cword wf
      ne0i s3cld c2 wrdf s3len df-3 eqtri oveq2i feq2i sylib sylibr syl amgmlem
      cmnd wa wceq cnring ringmgp rpcnd jca32 cnfldbas mgpbas cnfldmul mgpplusg
      crg gsumws3 syl2anc 3nn0 hashfzo0 oveq2d oveq12d ringmnd cnfldadd 3brtr3d
      cn0 ) AHUAUBZBCDUDZUCIZJKLMIZUEUBZNIZUFIHWPUCIZWSNIBCDOIOIZJLNIZUFIBCDPIP
      IZLNIUGAWRWPWOWOUHZWRUIQAKLUJUKKWRQZWRULUMAXFLUNQUOLUPUQWRKUTRAWPSURQZWRS
      WPUSZABCDSEFGVAXGKVBJPIZMIZSWPUSZXHXGKWPUEUBZMIZSWPUSXKSWPVCXMXJSWPXLXIKM
      XLLXIBCDVDVEVFVGVHVIWRXJSWPLXIKMVEVGVHVJVKVLAWQXBWTXCUFAWOVMQZBTQZCTQZDTQ
      ZVNVNZWQXBVOHWDQZXNAVPHWOXEVQRAXOXPXQABEVRACFVRADGVRVSZTOBCDWOTHWOXEVTWAH
      OWOXEWBWCWEWFAWSLJNLWNQWSLVOAWGLWHRZWIWJAXAXDWSLNAHVMQZXRXAXDVOXSYBAVPHWK
      RXTTPBCDHVTWLWEWFYAWJWM $.
  $}

  ${
    amgm4d.0 $e |- ( ph -> A e. RR+ ) $.
    amgm4d.1 $e |- ( ph -> B e. RR+ ) $.
    amgm4d.2 $e |- ( ph -> C e. RR+ ) $.
    amgm4d.3 $e |- ( ph -> D e. RR+ ) $.
    $( Arithmetic-geometric mean inequality for ` n = 4 ` .  (Contributed by
       Stanislas Polu, 11-Sep-2020.) $)
    amgm4d $p |- ( ph -> ( ( A x. ( B x. ( C x. D ) ) ) ^c ( 1 / 4 ) ) <_
                 ( ( A + ( B + ( C + D ) ) ) / 4 ) ) $=
      ( ccnfld co cc0 c4 cdiv cmul caddc wcel mp1i crp cc cmgp cfv cgsu c1 cfzo
      cs4 chash ccxp cle eqid cfn fzofi a1i c0 wne cn 4nn lbfzo0 mpbir wf cword
      ne0i s4cld wrdf syl wceq s4len oveq2d feq2d mpbid amgmlem cmnd crg cnring
      ringmgp rpcnd jca jca32 cnfldbas mgpbas cnfldmul mgpplusg gsumws4 syl2anc
      wa cn0 4nn0 hashfzo0 oveq12d ringmnd cnfldadd 3brtr3d ) AJUAUBZBCDEUFZUCK
      ZUDLMUEKZUGUBZNKZUHKJWNUCKZWQNKBCDEOKOKOKZUDMNKZUHKBCDEPKPKPKZMNKUIAWPWNW
      MWMUJZWPUKQALMULUMLWPQZWPUNUOAXDMUPQUQMURUSWPLVBRALWNUGUBZUEKZSWNUTZWPSWN
      UTAWNSVAQXGABCDESFGHIVCSWNVDVEAXFWPSWNAXEMLUEXEMVFABCDEVGUMVHVIVJVKAWOWTW
      RXAUHAWMVLQZBTQZCTQZDTQZETQZWEZWEWEZWOWTVFJVMQZXHAVNJWMXCVORAXIXJXMABFVPA
      CGVPAXKXLADHVPAEIVPVQVRZTOBCDWMETJWMXCVSVTJOWMXCWAWBWCWDAWQMUDNMWFQWQMVFA
      WGMWHRZVHWIAWSXBWQMNAJVLQZXNWSXBVFXOXRAVNJWJRXPTPBCDJEVSWKWCWDXQWIWL $.
  $}

$( (End of Stanislas Polu's mathbox.) $)
