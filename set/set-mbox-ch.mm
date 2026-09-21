$[ set-main.mm $]
$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Mathbox for Chen-Pang He
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Ordinal topology
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d B x y $.
    $( An ordinal number is a topological basis.  (Contributed by Chen-Pang He,
       8-Oct-2015.) $)
    ontopbas $p |- ( B e. On -> B e. TopBases ) $=
      ( vx vy con0 wcel cv cin wral ctb wa onelon anim12dan ex onin syl6 anc2ri
      wss wi inss1 jctl adantr a1i ontr2 syl6c ralrimivv fiinbas mpdan ) ADEZBF
      ZCFZGZAEZCAHBAHAIEUHULBCAAUHUIAEZUJAEZJZUKDEZUHJUKUIQZUMJZULUHUOUPUHUOUID
      EZUJDEZJZUPUHUOVAUHUMUSUNUTAUIKAUJKLMUIUJNOPUOURRUHUMURUNUMUQUIUJSTUAUBUK
      UIAUCUDUEBCADUFUG $.
  $}

  $( The class of ordinal numbers is a subclass of the class of topological
     bases.  (Contributed by Chen-Pang He, 8-Oct-2015.) $)
  onsstopbas $p |- On C_ TopBases $=
    ( vx con0 ctb cv ontopbas ssriv ) ABCADEF $.

  $( The class of ordinal numbers is a proper subclass of the class of
     topological bases.  (Contributed by Chen-Pang He, 9-Oct-2015.) $)
  onpsstopbas $p |- On C. TopBases $=
    ( con0 ctb wss c0 csn wcel wn wa wpss onsstopbas ctop indistop topbas ax-mp
    cpr wi snex prid2 snsn0non mp2 jcn onelon ex mto pm3.2i ssnelpss ) ABCDDEZE
    ZOZBFZUIAFZGZHABIJUJULUIKFUJUHLUIMNUKUHUIFZUHAFZPZUMUNGUOGDUHUGQRSUMUNUATUK
    UMUNUIUHUBUCUDUEABUIUFT $.

  ${
    $d B x $.
    $( The topology generated from an ordinal number ` B ` is ` suc U. B ` .
       (Contributed by Chen-Pang He, 10-Oct-2015.) $)
    ontgval $p |- ( B e. On -> ( topGen ` B ) = suc U. B ) $=
      ( vx con0 wcel ctg cfv cuni csuc cv wa wss cpw cin wceq eltg4i cvv inex1g
      syl jctird wi onss ssinss1 ssonuni sylc eleq1 biimprd syl2imc onuni onsuc
      tg1 a1i sucidg ontr2 syl6c wo elsuci word eloni orduniss bastg sstrd ssid
      sseld eltg3i mpan2 eleq1a jaod syl5 impbid eqrdv ) ACDZBAEFZAGZHZVKBIZVLD
      ZVOVNDZVKVPVOCDZVNCDZJVOVMKZVMVNDZJVQVKVPVRVSVPVOAVOLZMZGZNZVKWDCDZVRVOAO
      VKWCPDWCCKZWFAWBCQVKACKWGAUAAWBCUBRWCPUCUDWEVRWFVOWDCUEUFUGVKVMCDZVSAUHZV
      MUIRSVKVPVTWAVPVTTVKVOAUJUKVKWHWAWIVMCULRSVOVMVNUMUNVQVOVMDZVOVMNZUOVKVPV
      OVMUPVKWJVPWKVKVMVLVOVKVMAVLVKAUQVMAKAURAUSRACUTVAVCVKVMVLDZWKVPTVKAAKWLA
      VBAACVDVEVMVLVOVFRVGVHVIVJ $.
  $}

  $( The topology generated from a successor ordinal number is itself.
     (Contributed by Chen-Pang He, 11-Oct-2015.) $)
  ontgsucval $p |- ( A e. On -> ( topGen ` suc A ) = suc A ) $=
    ( con0 wcel csuc ctg cfv cuni wceq onsuc ontgval word eloni ordunisuc suceq
    syl eqtrd ) ABCZADZEFZRGZDZRQRBCSUAHAIRJOQTAHZUARHQAKUBALAMOTANOP $.

  $( A successor ordinal number is a topology.  (Contributed by Chen-Pang He,
     11-Oct-2015.) $)
  onsuctop $p |- ( A e. On -> suc A e. Top ) $=
    ( con0 wcel csuc ctg cfv ctop ontgsucval onsuc ontopbas tgcl 3syl eqeltrrd
    ctb ) ABCZADZEFZPGAHOPBCPNCQGCAIPJPKLM $.

  $( One of the topologies on an ordinal number is its successor.  (Contributed
     by Chen-Pang He, 7-Nov-2015.) $)
  onsuctopon $p |- ( A e. On -> suc A e. ( TopOn ` A ) ) $=
    ( con0 wcel csuc ctop cuni wceq ctopon onsuctop word eloni ordunisuc eqcomd
    cfv syl istopon sylanbrc ) ABCZADZECASFZGZSAHNCAIRAJZUAAKUBTAALMOASPQ $.

  ${
    ordtoplem.1 $e |- ( U. A e. On -> suc U. A e. S ) $.
    $( Membership of the class of successor ordinals.  (Contributed by
       Chen-Pang He, 1-Nov-2015.) $)
    ordtoplem $p |- ( Ord A -> ( A =/= U. A -> A e. S ) ) $=
      ( cuni wne wceq wn word wcel df-ne con0 csuc wo ordeleqon eqcomi id unieq
      unon 3eqtr4a ord orim2i sylbi orcomd orduniorsuc wi onuni eleq1a biimtrid
      3syl syl6c ) AADZEAUKFZGZAHZABIZAUKJUNUMAKIZAUKLZFZUOUNULUPUNUPULUNUPAKFZ
      MUPULMANUSULUPUSKKDZAUKUTKROUSPAKQSUAUBUCTUNULURAUDTUPUKKIUQBIURUOUEAUFCU
      QBAUGUIUJUH $.
  $}

  $( An ordinal is a topology iff it is not its supremum (union), proven
     without the Axiom of Regularity.  (Contributed by Chen-Pang He,
     1-Nov-2015.) $)
  ordtop $p |- ( Ord J -> ( J e. Top <-> J =/= U. J ) ) $=
    ( word ctop wcel cuni wne eqid topopn nordeq syl5 onsuctop ordtoplem impbid
    ex ) ABZACDZAAEZFZPQADZORAQQGHOSRAQINJACQKLM $.

  ${
    $d A x $.
    onsucconni.1 $e |- A e. On $.
    $( A successor ordinal number is a connected topology.  (Contributed by
       Chen-Pang He, 16-Oct-2015.) $)
    onsucconni $p |- suc A e. Conn $=
      ( vx csuc cconn wcel c0 wss con0 wa wceq wo wi oneli wne on0eln0 necon1bd
      wn biimprd syl ctop ccld cfv cin cpr onsuctop ax-mp elin cdif elsuci cuni
      onunisuci eqcomi cldopn onsuci elndif ssdif0 onssneli sylbir syl56 sylcom
      con2d orim1d impcom vex elpr sylibr syl2an sylbi ssriv isconn2 mpbir2an
      cv ) ADZEFVNUAFZVNVNUBUCZUDZGAUEZHAIFVOBAUFUGCVQVRCVMZVQFVSVNFZVSVPFZJVSV
      RFZVSVNVPUHVTVSAFZVSAKZLZAVSUIZVNFZWBWAVSAUJVSVNAVNUKAABULUMZUNWEWGJVSGKZ
      WDLZWBWGWEWJWGWCWIWDWGWFIFZWCWIMVNWFABUONWKWCGVSFZRWIWKWLWCWLGWFFZRWKWFGK
      ZWCRZGVSAUPWKWMWFGWKWMWFGOWFPSQWNAVSHWOAVSUQAVSBURUSUTVBWCWLVSGWCVSIFZVSG
      OZWLMAVSBNWPWLWQVSPSTQVATVCVDVSGACVEVFVGVHVIVJVNAWHVKVL $.
  $}

  $( A successor ordinal number is a connected topology.  (Contributed by
     Chen-Pang He, 16-Oct-2015.) $)
  onsucconn $p |- ( A e. On -> suc A e. Conn ) $=
    ( con0 wcel csuc cconn cif wceq suceq eleq1d 0elon elimel onsucconni dedth
    c0 ) ABCZADZECOANFZDZECANAQGPREAQHIQANBJKLM $.

  $( An ordinal topology is connected.  (Contributed by Chen-Pang He,
     1-Nov-2015.) $)
  ordtopconn $p |- ( Ord J -> ( J e. Top <-> J e. Conn ) ) $=
    ( word ctop wcel cuni wne ordtop onsucconn ordtoplem sylbid conntop impbid1
    cconn ) ABZACDZAMDZNOAAEZFPAGAMQHIJAKL $.

  $( An ordinal topology is connected, expressed in constants.  (Contributed by
     Chen-Pang He, 16-Oct-2015.) $)
  onintopssconn $p |- ( On i^i Top ) C_ Conn $=
    ( vx con0 ctop cin cconn cv wcel wa elin word wb eloni ordtopconn syl sylbi
    biimpa ssriv ) ABCDZEAFZRGSBGZSCGZHSEGZSBCITUAUBTSJUAUBKSLSMNPOQ $.

  ${
    $d A o x y $.
    $( A successor ordinal number is a T_0 space.  (Contributed by Chen-Pang
       He, 8-Nov-2015.) $)
    onsuct0 $p |- ( A e. On -> suc A e. Kol2 ) $=
      ( vx vo vy con0 wcel csuc wel wb wral wi word cv wa wal ordelon wn ancoms
      wss syl ct0 weq eloni df-ral anim12dan ordsuc sylbi adantr ontri1 onsssuc
      ex notbi bitr3d adantrr adantrl bibi12d bitrid biimpd syl6an a2d ordelord
      ordelss ordsucsssuc syldan mpbid ssneld jcad pm5.21 syl6 idd jad biimtrid
      syld alimdv wceq dfcleq suc11 bitr3id sylibd ralrimivva ctopon onsuctopon
      cfv ist0-2 mpbird ) AEFZAGZUAFZBCHZDCHZIZCWGJZBDUBZKZDAJBAJZWFALZWOAUCWPW
      NBDAAWPBMZAFZDMZAFZNZNZWLCMZWQGZFZXCWSGZFZIZCOZWMWLXCWGFZWKKZCOXBXIWKCWGU
      DXBXKXHCXBXKXJXHKXHXBXJWKXHXBWQEFZWSEFZNZXJXCEFZWKXHKWPWRXLWTXMAWQPAWSPUE
      ZWPXJXOKZXAWPWGLZXQAUFXRXJXOWGXCPUKUGUHXNXONZWKXHWKWIQZWJQZIZXSXHWIWJULXO
      XNYBXHIXOXNNXTXEYAXGXOXLXTXEIXMXOXLNXCWQSXTXEXCWQUIXCWQUJUMUNXOXMYAXGIXLX
      OXMNXCWSSYAXGXCWSUIXCWSUJUMUOUPRUQURUSUTXBXJXHXHXBXJQZXEQZXGQZNXHXBYCYDYE
      WPWRYCYDKWTWPWRNZXDWGXCYFWQASZXDWGSZAWQVBWPWRWQLZYGYHIZAWQVAYIWPYJWQAVCRV
      DVEVFUNWPWTYCYEKWRWPWTNZXFWGXCYKWSASZXFWGSZAWSVBWPWTWSLZYLYMIZAWSVAYNWPYO
      WSAVCRVDVEVFUOVGXEXGVHVIXBXHVJVKVMVNVLXBXNXIWMIXPXIXDXFVOXNWMCXDXFVPWQWSV
      QVRTVSVTTWFWGAWAWCFWHWOIAWBBDCWGAWDTWE $.
  $}

  $( An ordinal topology is T_0.  (Contributed by Chen-Pang He, 8-Nov-2015.) $)
  ordtopt0 $p |- ( Ord J -> ( J e. Top <-> J e. Kol2 ) ) $=
    ( word ctop wcel ct0 cuni wne ordtop onsuct0 ordtoplem sylbid t0top impbid1
    ) ABZACDZAEDZNOAAFZGPAHAEQIJKALM $.

  ${
    $d A y z $.
    onsucsuccmpi.1 $e |- A e. On $.
    $( The successor of a successor ordinal number is a compact topology,
       proven without the Axiom of Regularity.  (Contributed by Chen-Pang He,
       18-Oct-2015.) $)
    onsucsuccmpi $p |- suc suc A e. Comp $=
      ( vy vz csuc ccmp wcel ctop cv cuni wceq cpw cfn cin wi con0 onunisuci wa
      wss eqcomi wrex wral onsuci onsuctop ax-mp wn onirri onsucssi sseq1 mtbii
      mtbi elpwi unissd sseqtrdi nsyl csn cun cdif eldif elpwunsn sylbir df-suc
      ex pweqi eleq2s snelpwi snfi jctr elin elexi unisn unieq rspceeqv sylancl
      sylibr syl syl56 rgen iscmp mpbir2an ) AEZEZFGWBHGZWACIZJZKZWADIZJZKDWDLZ
      MNZUAZOZCWBLZUBWAPGWCABUCZWAUDUEWLCWMWFWDWALZGZUFZWDWMGWAWDGZWKWFWEASZWPW
      FWAASZWSAAGWTABUGAABBUHUKWAWEAUIUJWPWEWAJAWPWDWAWDWAULUMABQUNUOWQWROWDWAW
      AUPZUQZLZWMWDXCGZWQWRXDWQRWDXCWOURGWRWDXCWOUSWDWAWAUTVAVCWBXBWAVBVDVEWRXA
      WIGZWKWAWDVFXEXAWJGZWAXAJZKWKXEXEXAMGZRXFXEXHWAVGVHXAWIMVIVOXGWAWAWAPWNVJ
      VKTDXAWJWHXGWAWGXAVLVMVNVPVQVRCDWBWAWBJWAWAWNQTVSVT $.
  $}

  $( The successor of a successor ordinal number is a compact topology.
     (Contributed by Chen-Pang He, 18-Oct-2015.) $)
  onsucsuccmp $p |- ( A e. On -> suc suc A e. Comp ) $=
    ( con0 wcel csuc ccmp c0 cif wceq suceq syl eleq1d 0elon onsucsuccmpi dedth
    elimel ) ABCZADZDZECPAFGZDZDZECAFASHZRUAEUBQTHRUAHASIQTIJKSAFBLOMN $.

  ${
    $d A y z $.
    limsucncmpi.1 $e |- Lim A $.
    $( The successor of a limit ordinal is not compact.  (Contributed by
       Chen-Pang He, 20-Oct-2015.) $)
    limsucncmpi $p |- -. suc A e. Comp $=
      ( vy vz wcel ctop cuni wceq cpw cfn wrex wi wa wn cvv wss ax-mp wne con0
      c0 csuc ccmp cin wral elex sucexb sylibr sssucid elpwg mpbiri wlim limuni
      cv elin elpwi anim1i sylbi wb nlim0 2th xor3 mpbir necon3bi uni0 neeqtrri
      limeq unieq neeq2d a1i word limord ordsson mp2b sstr2 mpi ordunifi 3expia
      sylan ssel nordeq mpan syl6 adantr syld pm2.61dne neneqd nrex eqeq2d pweq
      syl ineq1d rexeqdv notbid anbi12d rspcev mpanr12 rexanali sylib 3syl mpbi
      imnan ordunisuc eqcomi iscmp mtbir ) AUAZUBEXFFEZACUMZGZHZADUMZGZHZDXHIZJ
      UCZKZLCXFIZUDZMZXGXRNZLXSNXGAOEZAXQEZXTXGXFOEYAXFFUEAUFUGYAYBAXFPAUHAXFOU
      IUJYBXJXPNZMZCXQKZXTYBAAGZHZXMDAIZJUCZKZNZYEAUKZYGBAULQXMDYIXKYIEZAXLYMXK
      APZXKJEZMZAXLRZYMXKYHEZYOMYPXKYHJUNYRYNYOXKAUOUPUQYPYQXKTXKTHZYQLYPYSYQAT
      GZRATYTYLTUKZURZNZATRUUCYLUUANZURYLUUDBUSUTYLUUAVAVBUUBATATVFVCQVDVEYSXLY
      TAXKTVGVHUJVIYPXKTRZXLXKEZYQYNXKSPZYOUUEUUFLYNASPZUUGYLAVJZUUHBAVKZAVLVMX
      KASVNVOUUGYOUUEUUFXKVPVQVRYNUUFYQLYOYNUUFXLAEZYQXKAXLVSUUIUUKYQYLUUIBUUJQ
      AXLVTWAWBWCWDWEWJWFWGYDYGYKMCAXQXHAHZXJYGYCYKUULXIYFAXHAVGWHUULXPYJUULXMD
      XOYIUULXNYHJXHAWIWKWLWMWNWOWPXJXPCXQWQWRWSXGXRXAWTCDXFAXFGZAYLUUIUUMAHBUU
      JAXBVMXCXDXE $.
  $}

  $( The successor of a limit ordinal is not compact.  (Contributed by
     Chen-Pang He, 20-Oct-2015.) $)
  limsucncmp $p |- ( Lim A -> -. suc A e. Comp ) $=
    ( wlim csuc ccmp wcel con0 cif wceq suceq eleq1d notbid limeq limon elimhyp
    wn limsucncmpi dedth ) ABZACZDEZORAFGZCZDEZOAFAUAHZTUCUDSUBDAUAIJKUARUABFBA
    FAUALFUALMNPQ $.

  $( An ordinal topology is compact iff the underlying set is its supremum
     (union) only when the ordinal is ` 1o ` .  (Contributed by Chen-Pang He,
     1-Nov-2015.) $)
  ordcmp $p |- ( Ord A -> ( A e. Comp <-> ( U. A = U. U. A -> A = 1o ) ) ) $=
    ( word ccmp wcel cuni wceq c1o wi c0 wo biimpd syl ctop cmptop wn csuc syl6
    a1i con0 ord csn wss wlim orduni unizlim uni0b orbi1i bitrdi sssn 0ntop mto
    eleq1 mtbiri pm2.21d df1o2 eqtr4di a1d jaoi sylbi wne ordtop necon2bd con3i
    a1dd limsucncmp notbid imbitrrid orduniorsuc mpjaod pm2.21 jaod com23 syl5d
    id ordeleqon unon eqcomi unieqi unieq unieqd 3eqtr4a orim2i syl5 suceq eqtr
    orcomd syl6c onuni onsucsuccmp eleq1a 4syl eqtrdi 0cmp eqeltrdi jad impbid
    ex ) ABZACDZAEZWTEZFZAGFZHWRXBAIUAZUBZWTUCZJZWSXCWRWTBZXBXGHAUDZXHXBXGXHXBW
    TIFZXFJXGWTUEXJXEXFAUFUGUHKLWRXGWSXCWRXEWSXCHZXFXEXKHWRXEAIFZAXDFZJXKAIUIXL
    XKXMXLWSXCXLWSICDZXNIMDUJINUKAICULUMUNXMXCWSXMAXDGXMVNUOUPUQURUSRWRXFWSOZXK
    WRAWTFZXFXOHZAWTPZFZWRXPXOXFWRXPAMDZOXOWRXTAWTWRXTAWTUTAVAKVBWSXTANVCQVDXSX
    QHWRXFXOXSXRCDZOWTVEXSWSYAAXRCULVFVGRAVHZVIWSXCVJQVKVLVMWRXBXCWSWRXBOZASDZA
    XAPZPZFZWSWRXBYDWRYDXBWRYDASFZJYDXBJAVOYHXBYDYHSEZYIEWTXASYIYISVPVQVRASVSZY
    HWTYIYJVTWAWBUSWFTWRYCXSXRYFFZYGYCXPOWRXSXPXBAWTVSVCWRXPXSYBTWCWRYCWTYEFZYK
    WRXBYLWRXHXBYLJXIWTVHLTWTYEWDQXSYKYGAXRYFWEWQWGYDWTSDXASDYFCDYGWSHAWHWTWHXA
    WIYFCAWJWKWGXCWSHWRXCAXDCXCAGXDXCVNUOWLWMWNRWOWP $.

  $( The ordinal topologies ` 1o ` and ` 2o ` are Hausdorff.  (Contributed by
     Chen-Pang He, 10-Nov-2015.) $)
  ssoninhaus $p |- { 1o , 2o } C_ ( On i^i Haus ) $=
    ( c1o c2o cpr con0 cha wcel wss 1on 2on prssi mp2an c0 cpw csn df1o2 eqtr4i
    cvv dishaus ax-mp eqeltri pw0 0ex df2o2 pwpw0 p0ex ssini ) ABCZDEADFBDFUGDG
    HIABDJKAEFBEFUGEGALMZEALNZUHOUAPLQFUHEFUBLQRSTBUIMZEBLUICUJUCUDPUIQFUJEFUEU
    IQRSTABEJKUF $.

  ${
    $d j a $.
    $( The ordinal T_1 spaces are ` 1o ` and ` 2o ` , proven without the Axiom
       of Regularity.  (Contributed by Chen-Pang He, 9-Nov-2015.) $)
    onint1 $p |- ( On i^i Fre ) = { 1o , 2o } $=
      ( vj va con0 ct1 cin c1o c2o cpr c0 csn cdif wcel wa wne wceq wss cun cha
      wn wb csuc cv elin ccld cuni wral ctop eqid ist1 simprbi onelon neldifsnd
      cfv ex p0ex prid2 df2o2 eleqtrri elunii mpan df1o2 eqeltrri onirri eldifd
      1on a1i ne0d 2thd nbbn sylib on0eln0 nsyl nsyli imp 0ex prid1 simpr sneqd
      adantl eleq1d rspcdv cldopn syl6 mtod con2d syl5 2on ontri1 onsssuc mpan2
      bitr3d sylibd 0ntop t1top nelneq elsni sylbi ssriv difeq1i difundir eqtri
      mto df-suc df-pr df2o3 difid 1n0 disjsn2 ax-mp difeq2i difin dif0 3eqtr3i
      uneq12i uncom un0 3eqtri 2on0 eqtr4i sseqtri ssoninhaus sslin sstri eqssi
      haust1 ) CDEZFGHZYFGUAZIJZKZYGAYFYJAUBZYFLYKCLZYKDLZMZYKYJLYKCDUCYNYKYHYI
      YLYMYKYHLZYLYMGYKLZSZYOYMBUBZJZYKUDUMZLZBYKUEZUFZYLYQYMYKUGLUUCYKUUBBUUBU
      HZUIUJYLYPUUCYLYPUUCSYLYPMZUUCUUBYIKZYKLZYLYPUUGSYLUUGUUFCLZYPYLUUGUUHYKU
      UFUKUNYPIUUFLZUUFINZTZUUHYPUUISZUUJTUUKSYPUULUUJYPIUUBULYPUUFYIYPYIUUBYIY
      IGLYPYIUUBLYIIYIHZGIYIUOUPUQURYIGYKUSUTYIYILSYPYIFYICVAVEVBVCVFVDVGVHUUIU
      UJVIVJUUFVKVLVMVNUUEUUCYIYTLZUUGUUEUUAUUNBIUUBYPIUUBLZYLIGLYPUUOIUUMGIYIV
      OVPUQURIGYKUSUTVSUUEYRIOZMZYSYIYTUUQYRIUUEUUPVQVRVTWAYIYKUUBUUDWBWCWDUNWE
      WFYLGCLZYQYOTWGYLUURMYKGPYQYOYKGWHYKGWIWKWJWLVNYMYKYILZSYLYMYKIOZUUSYMIDL
      ZSUUTSUVAIUGLWMIWNXBYKIDWOWJYKIWPVLVSVDWQWRYJGYIKZGJZYIKZQZYGYJGUVCQZYIKU
      VEYHUVFYIGXCWSGUVCYIWTXAYGFJZUVCQUVEFGXDUVBUVGUVDUVCUVBYIUVGQZYIKYIYIKZUV
      GYIKZQZUVGGUVHYIGIFHUVHXEIFXDXAWSYIUVGYIWTUVKIUVGQUVGIQUVGUVIIUVJUVGYIXFU
      VGUVGYIEZKUVGIKUVJUVGUVLIUVGFINUVLIOXGFIXHXIXJUVGYIXKUVGXLXMXNIUVGXOUVGXP
      XQXQUVCUVCYIEZKUVCIKUVDUVCUVMIUVCGINUVMIOXRGIXHXIXJUVCYIXKUVCXLXMXNXSXSXT
      YGCREZYFYARDPUVNYFPARDYKYEWRRDCYBXIYCYD $.
  $}

  $( The ordinal Hausdorff spaces are ` 1o ` and ` 2o ` .  (Contributed by
     Chen-Pang He, 10-Nov-2015.) $)
  oninhaus $p |- ( On i^i Haus ) = { 1o , 2o } $=
    ( vx cha cin c1o c2o cpr ct1 wss cv haust1 ssriv sslin ax-mp onint1 sseqtri
    con0 ssoninhaus eqssi ) PBCZDEFZSPGCZTBGHSUAHABGAIJKBGPLMNOQR $.

$( (End of Chen-Pang He's mathbox.) $)
