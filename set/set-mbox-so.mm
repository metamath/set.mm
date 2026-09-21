$[ set-main.mm $]
$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Mathbox for Stefan O'Rear
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Additional elementary logic and set theory
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d ps x $.  $d ph y $.  $d x A $.  $d x y $.
    moxfr.a $e |- A e. _V $.
    moxfr.b $e |- E! y x = A $.
    moxfr.c $e |- ( x = A -> ( ph <-> ps ) ) $.
    $( Transfer at-most-one between related expressions.  (Contributed by
       Stefan O'Rear, 12-Feb-2015.) $)
    moxfr $p |- ( E* x ph <-> E* y ps ) $=
      ( wex weu wi wmo cvv wrex wcel cv a1i wceq rexv moeu ax-mp rexxfr 3bitr3i
      euex mpbir euxfrw imbi12i 3bitr4i ) ACIZACJZKBDIZBDJZKACLBDLUIUKUJULACMNB
      DMNUIUKABCDEMMEMODPMOFQCPZERZDMNZUMMOUOUNDIZUNDJUPGUNDUDUAUNDSUEQHUBACSBD
      SUCABCDEFGHUFUGACTBDTUH $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Additional theory of functions
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d B x $.  $d F x $.
    $( Indexed intersection of an image.  (Contributed by Stefan O'Rear,
       22-Feb-2015.) $)
    imaiinfv $p |- ( ( F Fn A /\ B C_ A ) ->
        |^|_ x e. B ( F ` x ) = |^| ( F " B ) ) $=
      ( wfn wss wa cres cfv ciin crn cint cima wceq fnssres fniinfv syl iineq2i
      cv fvres eqcomi df-ima inteqi 3eqtr4g ) DBECBFGZACASZDCHZIZJZUGKZLZACUFDI
      ZJZDCMZLUEUGCEUIUKNBCDOACUGPQUIUMACUHULUFCDTRUAUNUJDCUBUCUD $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Additional topology
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d A v w $.  $d B v w $.  $d C v w $.  $d V v w $.
    $( Elementhood in a set of relative finite intersections.  (Contributed by
       Stefan O'Rear, 22-Feb-2015.) $)
    elrfi $p |- ( ( B e. V /\ C C_ ~P B ) -> ( A e. ( fi ` ( { B } u. C ) ) <->
          E. v e. ( ~P C i^i Fin ) A = ( B i^i |^| v ) ) ) $=
      ( vw wcel cpw wss wa cvv cun cint cin wceq cfn wrex syl2anc sseli sylib
      csn cfi cfv cv wi elex a1i inex1g eleq1 syl5ibrcom rexlimdvw adantr simpr
      wb snex pwexg ad2antrr simplr ssexd unexg sylancr elfi cdif inss1 sseqtri
      uncom pweqi elpwun ad2antrl inss2 diffi syl elind simprr cuni c0 eqeltrrd
      incom intex sylibr intssuni pwidg snssd unssd sstrd sspwuni eqsstrd dfss2
      wne elpwid eqtr2id ineq2 ad2antll eqtrd intun intsng ineq1d undif2 inteqi
      ad3antrrr eqtr4di eqtrid inteq rspceeqv rexlimdvaa ssun1 elpwi ssun4 3syl
      ineq2d adantl vex unex elpw snfi unfi eqcomd eqeq1 rexlimdva impbid bitrd
      rexbidv ex pm5.21ndd ) CEGZDCHZIZJZBKGZBCUAZDLZUBUCZGZBCAUDZMZNZOZADHZPNZ
      QZYMYIUEYHBYLUFUGYEYTYIUEYGYEYQYIAYSYEYIYQYPKGCYOEUHBYPKUIUJUKULYHYIYMYTU
      NYHYIJZYMBFUDZMZOZFYKHZPNZQZYTUUAYIYKKGZYMUUGUNYHYIUMUUAYJKGDKGUUHCUOZUUA
      DYFKYEYFKGYGYICEUPUQYEYGYIURUSYJDKKUTVAFBYKKKVBRUUAUUGYTUUAUUDYTFUUFUUAUU
      BUUFGZUUDJZJZUUBYJVCZYSGBCUUMMZNZOYTUULYRPUUMUUJUUMYRGZUUAUUDUUJUUBDYJLZH
      ZGUUPUUFUURUUBUUFUUEUURUUEPVDZYKUUQYJDVFVGVESUUBDYJUUIVHTVIUUJUUMPGZUUAUU
      DUUJUUBPGUUTUUFPUUBUUEPVJSUUBYJVKVLVIVMUULBYJUUMLZMZUUOUULBYJUUBLZMZUVBUU
      LBCUUCNZUVDUULBCBNZUVEUULUVFBCNZBCBVRUULBCIUVGBOUULBUUCCUUAUUJUUDVNZUULUU
      CUUBVOZCUULUUBVPWIZUUCUVIIUULUUCKGUVJUULBUUCKUVHYHYIUUKURVQUUBVSVTUUBWAVL
      UULUUBYFIUVICIUULUUBYKYFUUJUUBYKIUUAUUDUUJUUBYKUUFUUEUUBUUSSWJVIYHYKYFIYI
      UUKYHYJDYFYEYJYFIYGYECYFCEWBWCULYEYGUMWDUQWEUUBCWFTWEWGBCWHTWKUUDUVFUVEOU
      UAUUJBUUCCWLWMWNYEUVEUVDOYGYIUUKYEUVDYJMZUUCNUVEYJUUBWOYEUVKCUUCCEWPZWQWK
      WTWNUVAUVCYJUUBWRWSXAYEUVBUUOOYGYIUUKYEUVBUVKUUNNUUOYJUUMWOYEUVKCUUNUVLWQ
      XBWTWNAUUMYSYPUUOBYNUUMOYOUUNCYNUUMXCXJXDRXEUUAYQUUGAYSUUAYNYSGZJZUUGYQYP
      UUCOZFUUFQZUVNYJYNLZUUFGYPUVQMZOZUVPUVNUUEPUVQUVNUVQYKIUVQUUEGUVNYJYNYKYJ
      YKIUVNYJDXFUGUVMYNYKIZUUAUVMYNYRGYNDIUVTYSYRYNYRPVDSYNDXGYNDYJXHXIXKWDUVQ
      YKYJYNUUIAXLXMXNVTUVNYJPGYNPGZUVQPGCXOUVMUWAUUAYSPYNYRPVJSXKYJYNXPVAVMYEU
      VSYGYIUVMYEYPUVKYONUVRYECUVKYOYEUVKCUVLXQWQYJYNWOXAWTFUVQUUFUUCUVRYPUUBUV
      QXCXDRYQUUDUVOFUUFBYPUUCXRYBUJXSXTYAYCYD $.
  $}

  ${
    $d A v w $.  $d B v w $.  $d F v w $.  $d F y $.  $d I v w $.  $d V v w $.
    $d v y $.
    $( Elementhood in a set of relative finite intersections of an indexed
       family of sets.  (Contributed by Stefan O'Rear, 22-Feb-2015.) $)
    elrfirn $p |- ( ( B e. V /\ F : I --> ~P B ) ->
        ( A e. ( fi ` ( { B } u. ran F ) ) <->
          E. v e. ( ~P I i^i Fin ) A = ( B i^i |^|_ y e. v ( F ` y ) ) ) ) $=
      ( vw wcel cpw wa cv cin wceq cfn wrex wss cvv sseli adantl wf csn crn cun
      cfi cfv cint cima ciin wb elrfi sylan2 imassrn pwexg ssexg syl2anr elpw2g
      frn syl mpbiri wfun ffun ad2antlr inss2 imafi syl2anc elind wfn ffn inss1
      adantr elpwid fipreima syl3anc eqcom rexbii sylib ineq2d rexxfrd imaiinfv
      inteq eqeq2d eqcomd rexbidva 3bitrd ) DGIZFDJZEUAZKZCDUBEUCZUDUEUFIZCDHLZ
      UGZMZNZHWJJZOMZPZCDEBLZUHZUGZMZNZBFJZOMZPCDAWSALEUFUIZMZNZBXEPWHWFWJWGQZW
      KWRUJFWGEURZHCDWJGUKULWIWOXCHBWTWQXEWIWSXEIZKZWPOWTWIWTWPIZXKWIXMWTWJQZEW
      SUMWIWJRIZXMXNUJWHXIWGRIXOWFXJDGUNWJWGRUOUPWTWJRUQUSUTVKXLEVAZWSOIZWTOIWH
      XPWFXKFWGEVBVCXKXQWIXEOWSXDOVDSTEWSVEVFVGWIWLWQIZKZWTWLNZBXEPZWLWTNZBXEPX
      SEFVHZWLWJQZWLOIZYAWHYCWFXRFWGEVIZVCXRYDWIXRWLWJWQWPWLWPOVJSVLTXRYEWIWQOW
      LWPOVDSTWLFEBVMVNXTYBBXEWTWLVOVPVQYBWOXCUJWIYBWNXBCYBWMXADWLWTWAVRWBTVSWI
      XCXHBXEXLXBXGCXLXAXFDXLXFXAXLYCWSFQZXFXANWHYCWFXKYFVCXKYGWIXKWSFXEXDWSXDO
      VJSVLTAFWSEVTVFWCVRWBWDWE $.
  $}

  ${
    $d A v $.  $d B v y $.  $d C v z $.  $d I v y z $.  $d V v y $.

    $( Elementhood in a set of relative finite intersections of an indexed
       family of sets (implicit).  (Contributed by Stefan O'Rear,
       22-Feb-2015.) $)
    elrfirn2 $p |- ( ( B e. V /\ A. y e. I C C_ B ) ->
        ( A e. ( fi ` ( { B } u. ran ( y e. I |-> C ) ) ) <->
          E. v e. ( ~P I i^i Fin ) A = ( B i^i |^|_ y e. v C ) ) ) $=
      ( vz wcel wss wral wa cfv cv ciin cin wceq cpw cfn wrex csn crn cun wf wb
      cmpt cfi elpw2g biimprd ralimdv imp eqid sylib elrfirn syldan inss1 sseli
      fmpt elpwid nffvmpt1 nfcv fveq2 cbviin simplr simpll simpr fvmpt2 syl2anc
      cvv ssexd ex ralimdva ssralv mpan9 iineq2 syl eqtrid ineq2d eqeq2d sylan2
      rexbidva bitrd ) DGIZEDJZAFKZLZCDUAAFEUFZUBUCUGMIZCDHBNZHNZWGMZOZPZQZBFRZ
      SPZTZCDAWIEOZPZQZBWPTWCWEFDRZWGUDZWHWQUEWFEXAIZAFKZXBWCWEXDWCWDXCAFWCXCWD
      EDGUHUIUJUKAFXAEWGWGULZURUMHBCDWGFGUNUOWFWNWTBWPWIWPIZWFWIFJZWNWTUEXFWIFW
      PWOWIWOSUPUQUSWFXGLZWMWSCXHWLWRDXHWLAWIANZWGMZOZWRHAWIWKXJAFEWJUTHXJVAWJX
      IWGVBVCXHXJEQZAWIKZXKWRQWFXLAFKZXGXMWCWEXNWCWDXLAFWCXIFIZLZWDXLXPWDLZXOEV
      IIXLWCXOWDVDXQEDGWCXOWDVEXPWDVFVJAFEVIWGXEVGVHVKVLUKXLAWIFVMVNAWIXJEVOVPV
      QVRVSVTWAWB $.
  $}

  ${
    $d ph k l $.  $d I k l $.  $d J k l $.  $d S l $.  $d X k l $.
    cmpfiiin.x $e |- X = U. J $.
    cmpfiiin.j $e |- ( ph -> J e. Comp ) $.
    cmpfiiin.s $e |- ( ( ph /\ k e. I ) -> S e. ( Clsd ` J ) ) $.
    cmpfiiin.z $e |- ( ( ph /\ ( l C_ I /\ l e. Fin ) ) ->
        ( X i^i |^|_ k e. l S ) =/= (/) ) $.
    $( In a compact topology, a system of closed sets with nonempty finite
       intersections has a nonempty intersection.  (Contributed by Stefan
       O'Rear, 22-Feb-2015.) $)
    cmpfiiin $p |- ( ph -> ( X i^i |^|_ k e. I S ) =/= (/) ) $=
      ( ciin cin c0 cfv wcel wss syl wa cfn csn cmpt cint ccld wral wceq cmptop
      crn cun ctop ccmp topcld cv cldss ralrimiva riinint syl2anc cfi wne snssd
      wn fmpttd frnd unssd cpw wrex elin elpwi anim1i sylbi nesym sylan2 nrexdv
      sylib wb elrfirn2 mtbird cmpfii syl3anc eqnetrd ) AFCDBLMZFUAZCDBUBZUHZUI
      ZUCZNAFEUDOZPZBFQZCDUEZWAWFUFAEUJPZWHAEUKPZWKIEUGREFHULRZAWICDACUMDPSBWGP
      WIJBEFHUNRUOZBCDWGFUPUQAWLWEWGQNWEUROPZVAWFNUSIAWBWDWGAFWGWMUTADWGWCACDBW
      GJVBVCVDAWONFCGUMZBLMZUFZGDVEZTMZVFZAWRGWTWPWTPZAWPDQZWPTPZSZWRVAZXBWPWSP
      ZXDSXEWPWSTVGXGXCXDWPDVHVIVJAXESWQNUSXFKWQNVKVNVLVMAWHWJWOXAVOWMWNCGNFBDW
      GVPUQVQEWEVRVSVT $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Characterization of closure operators.  Kuratowski closure axioms
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d ph x y z $.  $d B x y z $.  $d F x y z $.  $d V x y z $.
    ismrcd.b $e |- ( ph -> B e. V ) $.
    ismrcd.f $e |- ( ph -> F : ~P B --> ~P B ) $.
    ismrcd.e $e |- ( ( ph /\ x C_ B ) -> x C_ ( F ` x ) ) $.
    ismrcd.m $e |- ( ( ph /\ x C_ B /\ y C_ x ) -> ( F ` y ) C_ ( F ` x ) ) $.
    ismrcd.i $e |- ( ( ph /\ x C_ B ) -> ( F ` ( F ` x ) ) = ( F ` x ) ) $.
    $( Any function from the subsets of a set to itself, which is extensive
       (satisfies ~ mrcssid ), isotone (satisfies ~ mrcss ), and idempotent
       (satisfies ~ mrcidm ) has a collection of fixed points which is a Moore
       collection, and itself is the closure operator for that collection.
       This can be taken as an alternate definition for the closure operators.
       This is the first half, ~ ismrcd2 is the second.  (Contributed by Stefan
       O'Rear, 1-Feb-2015.) $)
    ismrcd1 $p |- ( ph -> dom ( F i^i _I ) e. ( Moore ` B ) ) $=
      ( vz wss wcel cfv wceq wb cv syl2anc 3ad2ant1 cid cin cdm cpw inss1 ax-mp
      dmss fssdm ssid elpwg syl mpbiri ffvelcdmd elpwid velpw sylan2b ralrimiva
      wral id fveq2 sseq12d rspcva eqssd wfn ffnd fnelfp mpbird c0 wne w3a cint
      wel wa wi wal cuni simp2 sstrd simp3 intssuni2 unipw sseqtrdi intex sylbi
      cvv 3ad2ant3 adantr 3expib alrimiv sselda intss1 adantl jca anbi2d sseq1d
      sseq1 imbi12d spcgv syl3c mpbid sseqtrd ssint sylibr ismred ) AEUAUBZUCZD
      LADUDZXGXFEXEEMXFEUCMEUAUEXEEUGUFHUHZADXFNZDEOZDPZAXJDAXJDAXGXGDEHADXGNZD
      DMZDUIADFNXLXMQGDDFUJUKULZUMUNAXLBRZXOEOZMZBXGURZDXJMZXNAXQBXGXOXGNZAXODM
      ZXQBDUOIUPUQZXQXSBDXGXODPZXODXPXJYCUSXODEUTVAVBSVCAEXGVDZXLXIXKQAXGXGEHVE
      ZXNXGEDVFSVGALRZXFMZYFVHVIZVJZYFVKZXFNZYJEOZYJPZYIYLYJYIYLXOMZBYFURYLYJMY
      IYNBYFYIBLVLZVMZYLXPXOYPYJXGNZYACRZXOMZVMZYREOZXPMZVNZCVOZYAYJXOMZVMZYLXP
      MZYIYQYOYIYQYJDMZYIYJXGVPZDYIYFXGMYHYJUUIMYIYFXFXGAYGYHVQZAYGXFXGMYHXHTVR
      ZAYGYHVSYFXGVTSDWAWBYHAYQUUHQZYGYHYJWENUULYFWCYJDWEUJWDWFVGZWGYIUUDYOAYGU
      UDYHAUUCCAYAYSUUBJWHWITWGYPYAUUEYPXODYIYFXGXOUUKWJZUNYOUUEYIXOYFWKWLWMUUC
      UUFUUGVNCYJXGYRYJPZYTUUFUUBUUGUUOYSUUEYAYRYJXOWPWNUUOUUAYLXPYRYJEUTWOWQWR
      WSYPXOXFNZXPXOPZYIYFXFXOUUJWJYPYDXTUUPUUQQYIYDYOAYGYDYHYETZWGUUNXGEXOVFSW
      TXAUQBYLYFXBXCYIYQXRYJYLMZUUMAYGXRYHYBTXQUUSBYJXGXOYJPZXOYJXPYLUUTUSXOYJE
      UTVAVBSVCYIYDYQYKYMQUURUUMXGEYJVFSVGXD $.

    $( Second half of ~ ismrcd1 .  (Contributed by Stefan O'Rear,
       1-Feb-2015.) $)
    ismrcd2 $p |- ( ph -> F = ( mrCls ` dom ( F i^i _I ) ) ) $=
      ( vz cfv wcel wa wss adantr wi cvv wceq cpw cid cin cdm cmrc ffnd cmre wf
      wfn ismrcd1 eqid mrcf ffn 3syl cv mrcssvd elpwi mrcssid syl2an wal 3expib
      alrimivv vex fvex weq wb sseq1 adantl sseq12 anbi12d fveq2 imbi12d spc2gv
      mp2an syl mp2and mrccl elpw sylibr fnelfp syl2anc mpbid sseqtrd anbi2d id
      sseq12d chvarvv sylan2 2fveq3 eqeq12d ffvelcdmda mrcsscl syl3anc eqfnfvd
      mpbird eqssd ) ALDUAZEEUBUCUDZUEMZAWQWQEHUFZAWRDUGMNZWQWRWSUHWSWQUIABCDEF
      GHIJKUJZWRWSDWSUKZULWQWRWSUMUNALUOZWQNZOZXDEMZXDWSMZXFXGXHEMZXHXFXHDPZXDX
      HPZXGXIPZAXJXEAWRXDWSDXBXCUPZQAXAXDDPZXKXEXBXDDUQZWRXDWSDXCURUSAXJXKOZXLR
      ZXEABUOZDPZCUOZXRPZOZXTEMZXREMZPZRZBUTCUTZXQAYFCBAXSYAYEJVAVBXDSNXHSNYGXQ
      RLVCXDWSVDZYFXQCBXDXHSSCLVEZXRXHTZOZYBXPYEXLYKXSXJYAXKYJXSXJVFYIXRXHDVGVH
      XTXDXRXHVIVJYIYCXGTYDXITYEXLVFYJXTXDEVKXRXHEVKYCXGYDXIVIUSVLVMVNVOQVPXFXH
      WRNZXIXHTZAXAXNYLXEXBXOWRXDWSDXCVQUSXFEWQUIZXHWQNZYLYMVFAYNXEWTQZAYOXEAXJ
      YOXMXHDYHVRVSQWQEXHVTWAWBWCXFXAXDXGPZXGWRNZXHXGPAXAXEXBQXEAXNYQXOAXSOZXRY
      DPZRAXNOZYQRBLBLVEZYSUUAYTYQUUBXSXNAXRXDDVGWDZUUBXRXDYDXGUUBWEXRXDEVKZWFV
      LIWGWHXFYRXGEMZXGTZXEAXNUUFXOYSYDEMZYDTZRUUAUUFRBLUUBYSUUAUUHUUFUUCUUBUUG
      UUEYDXGXRXDEEWIUUDWJVLKWGWHXFYNXGWQNYRUUFVFYPAWQWQXDEHWKWQEXGVTWAWOWRXDWS
      XGDXCWLWMWPWN $.
  $}

  ${
    $d B x y z $.  $d ph x y z $.  $d F x y z $.  $d J x y $.  $d V x y z $.
    istopclsd.b $e |- ( ph -> B e. V ) $.
    istopclsd.f $e |- ( ph -> F : ~P B --> ~P B ) $.
    istopclsd.e $e |- ( ( ph /\ x C_ B ) -> x C_ ( F ` x ) ) $.
    istopclsd.i $e |- ( ( ph /\ x C_ B ) -> ( F ` ( F ` x ) ) = ( F ` x ) ) $.
    istopclsd.z $e |- ( ph -> ( F ` (/) ) = (/) ) $.
    istopclsd.u $e |- ( ( ph /\ x C_ B /\ y C_ B ) -> ( F ` ( x u. y ) ) =
          ( ( F ` x ) u. ( F ` y ) ) ) $.
    istopclsd.j $e |- J = { z e. ~P B | ( F ` ( B \ z ) ) = ( B \ z ) } $.
    $( A closure function which satisfies ~ sscls , ~ clsidm , ~ cls0 , and
       ~ clsun defines a (unique) topology which it is the closure function on.
       (Contributed by Stefan O'Rear, 1-Feb-2015.) $)
    istopclsd $p |- ( ph -> ( J e. ( TopOn ` B ) /\ ( cls ` J ) = F ) ) $=
      ( cfv wcel wceq wb wss ctopon ccl cv cdif cid cin cdm cpw crab wfn adantr
      wa ffnd difss elpw2g syl mpbiri fnelfp syl2anc bicomd rabbidva eqtrid w3a
      cun simp1 simp2 simp3 sstrd syl3anc ssequn2 biimpi 3ad2ant3 fveq2d eqtr3d
      ccld sylibr ismrcd1 c0 0elpw sylancl mpbird inss1 dmss ax-mp fssdm sseldd
      3ad2ant1 elpwid mpbid uneq12d eqtrd unssd vex unex mretopd simpld eqeltrd
      elpw eqid cmrc ctop topontop mrccls simprd eqtr4d ismrcd2 jca ) AGEUAPZQZ
      GUBPZFRAGEDUCZUDZFUEUFZUGZQZDEUHZUIZXHAGXLFPXLRZDXPUIXQOAXRXODXPAXKXPQZUL
      ZXOXRXTFXPUJZXLXPQZXOXRSAYAXSAXPXPFJUMZUKAYBXSAYBXLETZEXKUNAEHQYBYDSIXLEH
      UOUPUQUKXPFXLURUSUTVAVBZAXQXHQZXNXQVOPZRZABCDEXQXNABCEFHIJKABUCZETZCUCZYI
      TZVCZYIFPZYKFPZVDZYNRYOYNTYMYIYKVDZFPZYPYNYMAYJYKETZYRYPRZAYJYLVEAYJYLVFZ
      YMYKYIEAYJYLVGUUAVHNVIYMYQYIFYLAYQYIRZYJYLUUBYKYIVJVKVLVMVNYOYNVJVPZLVQAV
      RXNQZVRFPVRRZMAYAVRXPQUUDUUESYCEVSXPFVRURVTWAAYIXNQZYKXNQZVCZYQXNQZYRYQRZ
      UUHYRYPYQUUHAYJYSYTAUUFUUGVEUUHYIEUUHXNXPYIAUUFXNXPTUUGAXPXPXNFXMFTXNFUGT
      FUEWBXMFWCWDJWEWGZAUUFUUGVFZWFZWHZUUHYKEUUHXNXPYKUUKAUUFUUGVGZWFZWHZNVIUU
      HYNYIYOYKUUHUUFYNYIRZUULUUHYAYIXPQUUFUURSAUUFYAUUGYCWGZUUMXPFYIURUSWIUUHU
      UGYOYKRZUUOUUHYAYKXPQUUGUUTSUUSUUPXPFYKURUSWIWJWKUUHYAYQXPQZUUIUUJSUUSUUH
      YQETUVAUUHYIYKEUUNUUQWLYQEYIYKBWMCWMWNWRVPXPFYQURUSWAXQWSWOZWPWQZAXJXNWTP
      ZFAXJGVOPZWTPZUVDAGXAQZXJUVFRAXIUVGUVCEGXBUPUVFGUVFWSXCUPAXNUVEWTAXNYGUVE
      AYFYHUVBXDAGXQVOYEVMXEVMXEABCEFHIJKUUCLXFXEXG $.
  $}

  ${
    $d F x y z w $.  $d B x y z w $.
    $( A function is a Moore closure operator iff it satisfies ~ mrcssid ,
       ~ mrcss , and ~ mrcidm .  (Contributed by Stefan O'Rear, 1-Feb-2015.) $)
    ismrc $p |- ( F e. ( mrCls " ( Moore ` B ) ) <-> ( B e. _V /\
          F : ~P B --> ~P B /\ A. x A. y ( ( x C_ B /\ y C_ x ) ->
              ( x C_ ( F ` x ) /\ ( F ` y ) C_ ( F ` x ) /\
                ( F ` ( F ` x ) ) = ( F ` x ) ) ) ) ) $=
      ( vz vw cmrc cmre cfv wcel cvv cv wss wa wceq w3a wi wal syl wb cima wrex
      cpw wf wfun crn cuni wfn fnmrc fnfun ax-mp fvelima mpan eqid mrcf mresspw
      elfvex fssd mrcssid adantrr mrcss 3expb ancom2s mrcidm 3jca alrimivv feq1
      ex fveq1 sseq2d sseq12d fveq12d eqeq12d 3anbi123d imbi2d 2albidv 3anbi23d
      id syl5ibcom rexlimiv cid cin simp1 simp2 ssid 3simpb imim2i 2alimi sseq1
      cdm weq adantr sseq12 ancoms anbi12d fveq2 2fveq3 imbi12d spc2gv 3ad2ant3
      el2v mpan2i simpld syl2anr 3impib simprd ismrcd2 fvssunirn fndmi sseqtrri
      imp ismrcd1 funfvima2 mp2an eqeltrd impbii ) DGCHIZUAZJZCKJZCUCZYADUDZALZ
      CMZBLZYCMZNZYCYCDIZMZYEDIZYHMZYHDIZYHOZPZQZBRARZPZXSELZGIZDOZEXQUBZYQGUEZ
      XSUUAGHUFUGZUHUUBUIUUCGUJUKZEDXQGULUMYTYQEXQYRXQJZXTYAYAYSUDZYGYCYCYSIZMZ
      YEYSIZUUGMZUUGYSIZUUGOZPZQZBRARZPYTYQUUEXTUUFUUOYRCHUQUUEYAYRYAYSYRYSCYSU
      NZUOYRCUPURUUEUUNABUUEYGUUMUUEYGNUUHUUJUULUUEYDUUHYFYRYCYSCUUPUSUTUUEYFYD
      UUJUUEYFYDUUJYRYEYSYCCUUPVAVBVCUUEYDUULYFYRYCYSCUUPVDUTVEVHVFVEYTUUFYBUUO
      YPXTYAYAYSDVGYTUUNYOABYTUUMYNYGYTUUHYIUUJYKUULYMYTUUGYHYCYCYSDVIZVJYTUUIY
      JUUGYHYEYSDVIUUQVKYTUUKYLUUGYHYTUUGYHYSDYTVRUUQVLUUQVMVNVOVPVQVSVTSYQDDWA
      WBWJZGIZXRYQEFCDKXTYBYPWCZXTYBYPWDZYQYRCMZNZYRYRDIZMZUVDDIZUVDOZYQUVBUVEU
      VGNZYQUVBYRYRMZUVHYRWEYPXTUVBUVINZUVHQZYBYPYGYIYMNZQZBRARZUVKYOUVMABYNUVL
      YGYIYKYMWFWGWHUVNUVKQEEUVMUVKABYRYRKKAEWKZBEWKZNZYGUVJUVLUVHUVQYDUVBYFUVI
      UVOYDUVBTZUVPYCYRCWIZWLUVPUVOYFUVITYEYRYCYRWMWNWOUVQYIUVEYMUVGUVOYIUVETUV
      PUVOYCYRYHUVDUVOVRYCYRDWPZVKWLUVOYMUVGTUVPUVOYLUVFYHUVDYCYRDDWQUVTVMWLWOW
      RWSXASWTXBXKZXCZYQUVBFLZYRMZUWCDIZUVDMZYQYGYKQZBRARZUVBUWDNZUWFQZYPXTUWHY
      BYOUWGABYNYKYGYIYKYMWDWGWHWTUWHUWJQEFUWGUWJABYRUWCKKUVOBFWKZNZYGUWIYKUWFU
      WLYDUVBYFUWDUVOUVRUWKUVSWLUWKUVOYFUWDTYEUWCYCYRWMWNWOUWKYJUWEOYHUVDOYKUWF
      TUVOYEUWCDWPUVTYJUWEYHUVDWMXDWRWSXASXEZUVCUVEUVGUWAXFZXGYQUURXQJZUUSXRJZY
      QEFCDKUUTUVAUWBUWMUWNXLUUBXQGWJZMUWOUWPQUUDXQUUCUWQHCXHUUCGUIXIXJXQUURGXM
      XNSXOXP $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Algebraic closure systems
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c NoeACS $.

  $( Class of Noetherian closure systems. $)
  cnacs $a class NoeACS $.

  ${
    $d x c s g $.
    $( Define a closure system of _Noetherian type_ (not standard terminology)
       as an algebraic system where all closed sets are finitely generated.
       (Contributed by Stefan O'Rear, 4-Apr-2015.) $)
    df-nacs $a |- NoeACS = ( x e. _V |-> { c e. ( ACS ` x ) | A. s e. c
              E. g e. ( ~P x i^i Fin ) s = ( ( mrCls ` c ) ` g ) } ) $.
  $}

  ${
    $d C c g s $.  $d F c g s $.  $d S g s $.  $d X c g s x $.
    isnacs.f $e |- F = ( mrCls ` C ) $.
    $( Expand definition of Noetherian-type closure system.  (Contributed by
       Stefan O'Rear, 4-Apr-2015.) $)
    isnacs $p |- ( C e. ( NoeACS ` X ) <-> ( C e. ( ACS ` X ) /\
          A. s e. C E. g e. ( ~P X i^i Fin ) s = ( F ` g ) ) ) $=
      ( vc vx cnacs cfv wcel cvv cacs cv wceq cpw cfn wrex wral cmrc cin elfvex
      wa adantr crab fveq2 ineq1d rexeqdv ralbidv rabeqbidv df-nacs rabex fvmpt
      pweq fvex eleq2d eqtr4di fveq1d eqeq2d rexbidv raleqbi1dv elrab pm5.21nii
      bitrdi ) ADIJZKZDLKZADMJZKZENZBNZCJZOZBDPZQUAZRZEASZUCZADIUBVIVGVQADMUBUD
      VGVFAVJVKGNZTJZJZOZBVORZEVSSZGVHUEZKVRVGVEWEAHDWBBHNZPZQUAZRZEVSSZGWFMJZU
      EWELIWFDOZWJWDGWKVHWFDMUFWLWIWCEVSWLWBBWHVOWLWGVNQWFDUNUGUHUIUJHBEGUKWDGV
      HDMUOULUMUPWDVQGAVHWCVPEVSAVSAOZWBVMBVOWMWAVLVJWMVKVTCWMVTATJCVSATUFFUQUR
      USUTVAVBVDVC $.

    $( In a Noetherian-type closure system, all closed sets are finitely
       generated.  (Contributed by Stefan O'Rear, 4-Apr-2015.) $)
    nacsfg $p |- ( ( C e. ( NoeACS ` X ) /\ S e. C ) ->
        E. g e. ( ~P X i^i Fin ) S = ( F ` g ) ) $=
      ( vs wcel cnacs cfv cv wceq cpw cfn cin wrex wral cacs isnacs simprbi
      eqeq1 rexbidv rspcva sylan2 ancoms ) BAHZAEIJHZBCKDJZLZCEMNOZPZUGUFGKZUHL
      ZCUJPZGAQZUKUGAERJHUOACDEGFSTUNUKGBAULBLUMUICUJULBUHUAUBUCUDUE $.

    $( Express Noetherian-type closure system with fewer quantifiers.
       (Contributed by Stefan O'Rear, 4-Apr-2015.) $)
    isnacs2 $p |- ( C e. ( NoeACS ` X ) <-> ( C e. ( ACS ` X ) /\
          ( F " ( ~P X i^i Fin ) ) = C ) ) $=
      ( vs vg cnacs cfv wcel cacs cv wceq cpw cfn wrex wral wa wss 3syl bitr4di
      cin cima isnacs eqcom rexbii wfn wb cmre wf acsmre mrcf ffn inss1 sylancl
      fvelimab bitr4id ralbidv dfss3 crn imassrn sstrid biantrurd bitrd pm5.32i
      frn eqss bitri ) ACGHIACJHIZEKZFKBHZLZFCMZNUAZOZEAPZQVHBVMUBZALZQAFBCEDUC
      VHVOVQVHVOAVPRZVQVHVOVIVPIZEAPVRVHVNVSEAVHVNVJVILZFVMOZVSVKVTFVMVIVJUDUEV
      HBVLUFZVMVLRVSWAUGVHACUHHIZVLABUIZWBACUJZABCDUKZVLABULSVLNUMFVLVMVIBUOUNU
      PUQEAVPURTVHVRVPARZVRQVQVHWGVRVHVPBUSZABVMUTVHWCWDWHARWEWFVLABVESVAVBVPAV
      FTVCVDVG $.

    $( Slight variation on finite generation for closure systems.  (Contributed
       by Stefan O'Rear, 4-Apr-2015.) $)
    mrefg2 $p |- ( C e. ( Moore ` X ) ->
        ( E. g e. ( ~P X i^i Fin ) S = ( F ` g ) <->
          E. g e. ( ~P S i^i Fin ) S = ( F ` g ) ) ) $=
      ( cmre cfv wcel cv wceq cpw cfn cin wb wa wss elpw 3bitr4g elin simpr vex
      mrcssid mrcssv adantr impbida anbi1d pweq ineq1d eleq2d bibi2d syl5ibrcom
      sstrd pm5.32rd rexbidv2 ) AEGHIZBCJZDHZKZUSCELZMNZBLZMNZUPUSUQVAIZUQVCIZU
      PVDVEOUSVDUQURLZMNZIZOUPUQUTIZUQMIZPUQVFIZVJPVDVHUPVIVKVJUPUQEQZUQURQZVIV
      KUPVLVMAUQDEFUCUPVMPUQUREUPVMUAUPUREQVMAUQDEFUDUEUMUFUQECUBZRUQURVNRSUGUQ
      UTMTUQVFMTSUSVEVHVDUSVCVGUQUSVBVFMBURUHUIUJUKULUNUO $.

    $( Slight variation on finite generation for closure systems.  (Contributed
       by Stefan O'Rear, 4-Apr-2015.) $)
    mrefg3 $p |- ( ( C e. ( Moore ` X ) /\ S e. C ) ->
        ( E. g e. ( ~P X i^i Fin ) S = ( F ` g ) <->
          E. g e. ( ~P S i^i Fin ) S C_ ( F ` g ) ) ) $=
      ( cmre cfv wcel wa cv wceq cpw cfn cin wrex wss wb mrefg2 adantr biantrud
      simpll inss1 sseli elpwid adantl simplr mrcsscl syl3anc bitr4id rexbidva
      eqss bitrd ) AEGHIZBAIZJZBCKZDHZLZCEMNOPZUSCBMZNOZPZBURQZCVBPUNUTVCRUOABC
      DEFSTUPUSVDCVBUPUQVBIZJZUSVDURBQZJVDBURULVFVGVDVFUNUQBQZUOVGUNUOVEUBVEVHU
      PVEUQBVBVAUQVANUCUDUEUFUNUOVEUGAUQDBEFUHUIUAUJUKUM $.
  $}

  ${
    $d C g h i s $.  $d C t $.  $d X g h i s $.  $d X t $.  $d g t $.
    $d h t $.  $d s t $.
    $( A closure system of Noetherian type is algebraic.  (Contributed by
       Stefan O'Rear, 4-Apr-2015.) $)
    nacsacs $p |- ( C e. ( NoeACS ` X ) -> C e. ( ACS ` X ) ) $=
      ( cnacs cfv wcel cacs cmrc cpw cfn cin cima wceq eqid isnacs2 simplbi ) A
      BCDEABFDEAGDZBHIJKALAPBPMNO $.

    $( A choice-free order equivalent to the Noetherian condition on a closure
       system.  (Contributed by Stefan O'Rear, 4-Apr-2015.) $)
    isnacs3 $p |- ( C e. ( NoeACS ` X ) <-> ( C e. ( Moore ` X ) /\
          A. s e. ~P C ( ( toInc ` s ) e. Dirset -> U. s e. s ) ) ) $=
      ( vg vh vi vt cfv wcel cv cipo wi cpw wa wceq cfn wrex wss adantlr cvv wb
      cnacs cmre cdrs cuni wral nacsacs acsmred cmrc simpll cacs ad2antrr elpwi
      cin ad2antlr simpr acsdrsel syl3anc nacsfg syl2anc mrefg2 syl mpbid elfpw
      eqid fissuni sylbi 3expb sylan2b sstr ancoms simprr simprl sseldd mrcsscl
      ipodrsfi adantr eqsstrd simplrl elssuni eqssd eqeltrd expr syl5 rexlimdva
      ex expd expdimp rexlimdv mpd ralrimiva simpl adantl sseld imim2d ralimdva
      jca imp isacs3 sylanbrc cima mrcid mress acsficld wfn mrcf ffnd mrcss vex
      eqtr3d fpwipodrs mp1i inss1 sspwd sstrid fvex ax-mp a1i ipodrsima imassrn
      imaexg crn frnd elpw sylibr simplr fveq2 eleq1d id eleq12d imbi12d rspcva
      unieq fvelimab eqcom rexbii mpbird isnacs impbii ) ABUBHIZABUCHIZCJZKHZUD
      IZUUBUEZUUBIZLZCAMZUFZNZYTUUAUUIYTABABUGZUHZYTUUGCUUHYTUUBUUHIZNZUUDUUFUU
      NUUDNZUUEDJZAUIHZHZOZDUUEMPUNZQZUUFUUOUUSDBMZPUNZQZUVAUUOYTUUEAIZUVDYTUUM
      UUDUJUUOABUKHIZUUBARZUUDUVEYTUVFUUMUUDUUKULUUMUVGYTUUDUUBAUMZUOUUNUUDUPAB
      UUBUQURAUUEDUUQBUUQVEZUSUTYTUVDUVAUAZUUMUUDYTUUAUVJUULAUUEDUUQBUVIVAVBULV
      CUUOUUSUUFDUUTUUPUUTIZUUPEJZUEZRZEUUBMPUNZQZUUOUUSUUFLZUVKUUPUUERUUPPINUV
      PUUPUUEVDUUPUUBEVFVGUUOUVNUVQEUVOUUNUUDUVLUVOIZUVNUVQLZUUDUVRNUVMFJZRZFUU
      BQZUUNUVSUVRUUDUVLUUBRZUVLPIZNUWBUVLUUBVDUUDUWCUWDUWBFUUBUVLVPVHVIUUNUWAU
      VSFUUBUUNUVTUUBIZNZUWAUVNUVQUWAUVNNUUPUVTRZUWFUVQUVNUWAUWGUUPUVMUVTVJVKUU
      NUWEUWGUVQUUNUWEUWGNZNZUUSUUFUWIUUSNZUUEUVTUUBUWJUUEUVTUWJUUEUURUVTUWIUUS
      UPUWIUURUVTRZUUSUWIUUAUWGUVTAIUWKYTUUAUUMUWHUULULUUNUWEUWGVLUWIUUBAUVTUUM
      UVGYTUWHUVHUOUUNUWEUWGVMVNAUUPUUQUVTBUVIVOURVQVRUWJUWEUVTUUERUUNUWEUWGUUS
      VSZUVTUUBVTVBWAUWLWBWFWCWDWGWEWDWHWIWDWIWJWFWKWQUUJUVFGJZUUROZDUVCQZGAUFY
      TUUJUUAUUDUVELZCUUHUFZUVFUUAUUIWLUUAUUIUWQUUAUUGUWPCUUHUUAUUMNZUUFUVEUUDU
      WRUUBAUUEUUMUVGUUAUVHWMWNWOWPWRABCWSWTZUUJUWOGAUUJUWMAIZNZUWOUWNDUWMMZPUN
      ZQZUXAUURUWMOZDUXCQZUXDUXAUWMUUQUXCXAZIZUXFUXAUWMUXGUEZUXGUXAUWMUUQHZUWMU
      XIUUAUWTUXJUWMOUUIAUWMUUQBUVIXBSUXAAUWMUUQBUUJUVFUWTUWSVQUVIUUAUWTUWMBRUU
      IAUWMBXCZSXDXJUXAUXGKHZUDIZUXIUXGIZUUAUWTUXMUUIUUAUWTNZEDBUXCUUQTUUAUUQUV
      BXEZUWTUUAUVBAUUQAUUQBUVIXFZXGVQZUUAUUPUVLRZUVLBRZNUURUVLUUQHRZUWTUUAUXSU
      XTUYAAUUPUUQUVLBUVIXHVHSUWMTIUXCKHUDIUXOGXIUWMTXKXLUXOUXCUXBUVBUXBPXMUXOU
      WMBUXKXNXOZUXGTIZUXOUUQTIUYCAUIXPUUQUXCTYAXQZXRXSSUXAUXGUUHIZUUIUXMUXNLZU
      UAUWTUYEUUIUXOUXGARZUYEUUAUYGUWTUUAUXGUUQYBAUUQUXCXTUUAUVBAUUQUXQYCXOVQUX
      GAUYDYDYESUUAUUIUWTYFUUGUYFCUXGUUHUUBUXGOZUUDUXMUUFUXNUYHUUCUXLUDUUBUXGKY
      GYHUYHUUEUXIUUBUXGUUBUXGYMUYHYIYJYKYLUTWJWBUUAUWTUXHUXFUAZUUIUXOUXPUXCUVB
      RUYIUXRUYBDUVBUXCUWMUUQYNUTSVCUWNUXEDUXCUWMUURYOYPYEUUAUWOUXDUAUUIUWTAUWM
      DUUQBUVIVAULYQWKADUUQBGUVIYRWTYS $.
  $}

  ${
    $d A a b $.  $d B a $.  $d F a b x $.
    $( Transitivity induction of subsets, lemma for ~ nacsfix .  (Contributed
       by Stefan O'Rear, 4-Apr-2015.) $)
    incssnn0 $p |- ( ( A. x e. NN0 ( F ` x ) C_ ( F ` ( x + 1 ) ) /\
        A e. NN0 /\ B e. ( ZZ>= ` A ) ) -> ( F ` A ) C_ ( F ` B ) ) $=
      ( va vb cv cfv c1 caddc co wss cn0 wcel wa wi wceq fveq2 sseq2d imbi2d cz
      wral cuz weq ssid 2a1i eluznn0 ancoms fvoveq1 sseq12d syl expimpd ancomsd
      rspcv sstr2 com12 syl6 a2d uzind4 3impia ) AGZDHZVAIJKDHZLZAMUBZBMNZCBUCH
      ZNZBDHZCDHZLZVHVEVFOZVKVLVIEGZDHZLZPVLVIVILZPVLVIFGZDHZLZPVLVIVQIJKZDHZLZ
      PVLVKPEFBCVMBQZVOVPVLWCVNVIVIVMBDRSTEFUDZVOVSVLWDVNVRVIVMVQDRSTVMVTQZVOWB
      VLWEVNWAVIVMVTDRSTVMCQZVOVKVLWFVNVJVIVMCDRSTVPBUANVLVIUEUFVQVGNZVLVSWBWGV
      LVRWALZVSWBPWGVFVEWHWGVFVEWHWGVFOVQMNZVEWHPVFWGWIVQBUGUHVDWHAVQMAFUDVBVRV
      CWAVAVQDRVAVQIDJUIUJUNUKULUMVSWHWBVIVRWAUOUPUQURUSUPUT $.
  $}

  ${
    $d C a b z $.  $d C y $.  $d F a b c w $.  $d F y z $.  $d X a b z $.
    $d X y $.  $d a x y $.  $d b x $.  $d w y z $.  $d x z $.  $d F x $.
    $( An increasing sequence of closed sets in a Noetherian-type closure
       system eventually fixates.  (Contributed by Stefan O'Rear,
       4-Apr-2015.) $)
    nacsfix $p |- ( ( C e. ( NoeACS ` X ) /\ F : NN0 --> C /\
          A. x e. NN0 ( F ` x ) C_ ( F ` ( x + 1 ) ) ) ->
        E. y e. NN0 A. z e. ( ZZ>= ` y ) ( F ` z ) = ( F ` y ) ) $=
      ( vw va vb vc cfv wcel cn0 cv wss wral wceq wa wrex wb cnacs wf caddc w3a
      c1 co crn cuni fvssunirn simplrr sseqtrrid simpll3 simplrl simpr incssnn0
      cuz syl3anc eqssd ralrimiva cipo cdrs cvv wne cun cpw frn 3ad2ant2 elpw2g
      c0 3ad2ant1 mpbird elex syl cc0 wfn ffn 0nn0 fnfvelrn sylancl cr ad2antrl
      ne0d nn0re ad2antll cle cz nn0z eluz syl2an biimpar adantll ssequn1 sylib
      wbr eqimss fveq2 sseq2d rspcev syl2anc syl2anr ssequn2 lecasei ralrimivva
      weq uneq1 sseq1d rexbidv ralrn uneq2 sseq2 rexrn bitrd isipodrs syl3anbrc
      ralbidv wi isnacs3 simprbi eleq1d unieq id eleq12d imbi12d rspcva fvelrnb
      cmre mpd mpbid reximddv ) DFUAKZLZMDEUBZANZEKYMUEUCUFEKOAMPZUDZBNZEKZEUGZ
      UHZQZCNZEKZYQQZCYPUPKZPBMYOYPMLZYTRZRZUUCCUUDUUGUUAUUDLZRZUUBYQUUIYSUUBYQ
      EUUAUIYOUUEYTUUHUJUKUUIYNUUEUUHYQUUBOYKYLYNUUFUUHULYOUUEYTUUHUMUUGUUHUNAY
      PUUAEUOUQURUSYOYSYRLZYTBMSZYOYRUTKZVALZUUJYOYRVBLZYRVIVCYPUUAVDZGNZOZGYRS
      ZCYRPZBYRPZUUMYOYRDVEZLZUUNYOUVBYRDOZYLYKUVCYNMDEVFVGYKYLUVBUVCTYNYRDYJVH
      VJVKZYRUVAVLVMYOYRVNEKZYOEMVOZVNMLUVEYRLYLYKUVFYNMDEVPVGZVQMVNEVRVSWBYOUU
      THNZEKZINZEKZVDZJNZEKZOZJMSZIMPZHMPZYOUVPHIMMYOUVHMLZUVJMLZRZRZUVPUVHUVJU
      VSUVHVTLYOUVTUVHWCWAUVTUVJVTLYOUVSUVJWCWDUWBUVHUVJWEWNZRZUVTUVLUVKOZUVPYO
      UVSUVTUWCUJUWDUVLUVKQZUWEUWDUVIUVKOZUWFUWDYNUVSUVJUVHUPKLZUWGYKYLYNUWAUWC
      ULYOUVSUVTUWCUMUWAUWCUWHYOUWAUWHUWCUVSUVHWFLZUVJWFLZUWHUWCTUVTUVHWGZUVJWG
      ZUVHUVJWHWIWJWKAUVHUVJEUOUQUVIUVKWLWMUVLUVKWOVMUVOUWEJUVJMJIXDUVNUVKUVLUV
      MUVJEWPWQWRWSUWBUVJUVHWEWNZRZUVSUVLUVIOZUVPYOUVSUVTUWMUMUWNUVLUVIQZUWOUWN
      UVKUVIOZUWPUWNYNUVTUVHUVJUPKLZUWQYKYLYNUWAUWMULYOUVSUVTUWMUJUWAUWMUWRYOUW
      AUWRUWMUVTUWJUWIUWRUWMTUVSUWLUWKUVJUVHWHWTWJWKAUVJUVHEUOUQUVKUVIXAWMUVLUV
      IWOVMUVOUWOJUVHMJHXDUVNUVIUVLUVMUVHEWPWQWRWSXBXCYOUVFUUTUVRTUVGUVFUUTUVIU
      UAVDZUUPOZGYRSZCYRPZHMPUVRUUSUXBBHMEYPUVIQZUURUXACYRUXCUUQUWTGYRUXCUUOUWS
      UUPYPUVIUUAXEXFXGXOXHUVFUXBUVQHMUVFUXBUVLUUPOZGYRSZIMPUVQUXAUXECIMEUUAUVK
      QZUWTUXDGYRUXFUWSUVLUUPUUAUVKUVIXIXFXGXHUVFUXEUVPIMUXDUVOGJMEUUPUVNUVLXJX
      KXOXLXOXLVMVKBCGYRXMXNYOUVBYPUTKZVALZYPUHZYPLZXPZBUVAPZUUMUUJXPZUVDYKYLUX
      LYNYKDFYFKLUXLDFBXQXRVJUXKUXMBYRUVAYPYRQZUXHUUMUXJUUJUXNUXGUULVAYPYRUTWPX
      SUXNUXIYSYPYRYPYRXTUXNYAYBYCYDWSYGYOUVFUUJUUKTUVGBMYSEYEVMYHYI $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Miscellanea 1. Map utilities
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    constmap.1 $e |- A e. _V $.
    constmap.3 $e |- C e. _V $.
    $( A constant (represented without dummy variables) is an element of a
       function set.

       _Note:  In the following development, we will be quite often quantifying
       over functions and points in N-dimensional space (which are equivalent
       to functions from an "index set").  Many of the following theorems exist
       to transfer standard facts about functions to elements of function
       sets_.  (Contributed by Stefan O'Rear, 30-Aug-2014.)  (Revised by Stefan
       O'Rear, 5-May-2015.) $)
    constmap $p |- ( B e. C -> ( A X. { B } ) e. ( C ^m A ) ) $=
      ( wcel csn cxp wf cmap co fconst6g elmap sylibr ) BCFACABGHZIOCAJKFABCLCA
      OEDMN $.
  $}

  $( Renaming indices in a tuple, with sethood as antecedents.  (Contributed by
     Stefan O'Rear, 9-Oct-2014.)  (Revised by Mario Carneiro, 5-May-2015.) $)
  mapco2g $p |- ( ( E e. _V /\ A e. ( B ^m C ) /\ D : E --> C ) ->
    ( A o. D ) e. ( B ^m E ) ) $=
    ( cvv wcel cmap co wf w3a ccom elmapi fco sylan 3adant1 wceq n0i reldmmap
    c0 ovprc1 nsyl2 3ad2ant2 simp1 elmapd mpbird ) EFGZABCHIZGZECDJZKZADLZBEHIG
    EBULJZUIUJUMUGUICBAJUJUMABCMECBADNOPUKBEULFFUIUGBFGZUJUIUHTQUNUHARBCHSUAUBU
    CUGUIUJUDUEUF $.

  ${
    mapco2.3 $e |- E e. _V $.
    $( Post-composition (renaming indices) of a mapping viewed as a point.
       (Contributed by Stefan O'Rear, 5-Oct-2014.)  (Revised by Stefan O'Rear,
       5-May-2015.) $)
    mapco2 $p |- ( ( A e. ( B ^m C ) /\ D : E --> C ) ->
        ( A o. D ) e. ( B ^m E ) ) $=
      ( cvv wcel cmap co wf ccom mapco2g mp3an1 ) EGHABCIJHECDKADLBEIJHFABCDEMN
      $.
  $}

  ${
    mapfzcons.1 $e |- M = ( N + 1 ) $.
    $( Extending a one-based mapping by adding a tuple at the end results in
       another mapping.  (Contributed by Stefan O'Rear, 10-Oct-2014.)  (Revised
       by Stefan O'Rear, 5-May-2015.) $)
    mapfzcons $p |- ( ( N e. NN0 /\ A e. ( B ^m ( 1 ... N ) ) /\ C e. B ) -> (
        A u. { <. M , C >. } ) e. ( B ^m ( 1 ... M ) ) ) $=
      ( cn0 wcel c1 cfz co cmap caddc csn cun wf wceq cvv ovex cuz w3a c0 simp2
      cop cin wb elmapex simpld 3ad2ant2 elmapg sylancl mpbid wf1o simp3 f1osng
      sylancr f1of syl wss snssi 3ad2ant3 fssd fzp1disj a1i fun syl21anc cz cfv
      cmin 1z simp1 cc0 nn0uz 1m1e0 fveq2i eqtr4i eleqtrdi fzsuc2 eqcomd feq23d
      unidm mpbird opeq1i sneqi uneq2i oveq2i 3eltr4g ) EGHZABIEJKZLKHZCBHZUAZA
      EIMKZCUDZNZOZBIWMJKZLKZADCUDZNZOBIDJKZLKWLWPWRHZWQBWPPZWLWIWMNZOZBBOZWPPZ
      XCWLWIBAPZXDBWOPWIXDUEUBQZXGWLWJXHWHWJWKUCWLBRHZWIRHZWJXHUFWJWHXJWKWJXJXK
      ABWIUGUHUIZIEJSBWIARRUJUKULWLXDCNZBWOWLXDXMWOUMZXDXMWOPWLWMRHWKXNEIMSWHWJ
      WKUNWMCRBUOUPXDXMWOUQURWKWHXMBUSWJCBUTVAVBXIWLIEVCVDWIXDBBAWOVEVFWLXEXFWQ
      BWPWLWQXEWLIVGHEIIVIKZTVHZHWQXEQVJWLEGXPWHWJWKVKGVLTVHXPVMXOVLTVNVOVPVQIE
      VRUPVSXFBQWLBWAVDVTULWLXJWQRHXBXCUFXLIWMJSBWQWPRRUJUKWBWTWOAWSWNDWMCFWCWD
      WEXAWQBLDWMIJFWFWFWG $.

    $( Recover prefix mapping from an extended mapping.  (Contributed by Stefan
       O'Rear, 10-Oct-2014.)  (Revised by Stefan O'Rear, 5-May-2015.) $)
    mapfzcons1 $p |- ( A e. ( B ^m ( 1 ... N ) ) ->
      ( ( A u. { <. M , C >. } ) |` ( 1 ... N ) ) = A ) $=
      ( c1 cfz co cmap wcel cres csn cun wceq c0 cdm cin wss ax-mp cop wfn 3syl
      wf elmapi ffn fnresdm uneq1d resundir dmres caddc dmsnopss sneqi fzp1disj
      sseqtri sslin sseq0 mp2an eqtri wrel wb relres reldm0 mpbir uneq2i eqtr2i
      un0 3eqtr4g ) ABGEHIZJIKZAVILZDCUAMZVILZNAVMNZAVLNVILAVJVKAVMVJVIBAUDAVIU
      BVKAOABVIUEVIBAUFVIAUGUCUHAVLVIUIVNAPNAVMPAVMPOZVMQZPOZVPVIVLQZRZPVLVIUJV
      SVIEGUKIZMZRZSZWBPOVSPOVRWASWCVRDMWADCULDVTFUMUOVRWAVIUPTGEUNVSWBUQURUSVM
      UTVOVQVAVLVIVBVMVCTVDVEAVGVFVH $.

    $( A nonempty mapping has a prefix.  (Contributed by Stefan O'Rear,
       10-Oct-2014.)  (Revised by Stefan O'Rear, 5-May-2015.) $)
    mapfzcons1cl $p |- ( A e. ( B ^m ( 1 ... M ) ) ->
        ( A |` ( 1 ... N ) ) e. ( B ^m ( 1 ... N ) ) ) $=
      ( c1 cfz cmap wcel wss cres caddc fzssp1 oveq2i sseqtrri elmapssres mpan2
      co ) ABFCGRZHRIFDGRZSJATKBTHRITFDFLRZGRSFDMCUAFGENOABSTPQ $.

    $( Recover added element from an extended mapping.  (Contributed by Stefan
       O'Rear, 10-Oct-2014.)  (Revised by Stefan O'Rear, 5-May-2015.) $)
    mapfzcons2 $p |- ( ( A e. ( B ^m ( 1 ... N ) ) /\ C e. B ) ->
        ( ( A u. { <. M , C >. } ) ` M ) = C ) $=
      ( c1 cfz co cmap wcel wa cvv cdm wn csn wceq caddc cin c0 cop cun eqeltri
      cfv ovex a1i elex adantl elmapi adantr ineq1d sneqi ineq2i fzp1disj eqtri
      fdmd eqtrdi disjsn sylib fsnunfv syl3anc ) ABGEHIZJIKZCBKZLZDMKZCMKZDANZK
      OZDADCUAPUBUDCQVFVEDEGRIZMFEGRUEUCUFVDVGVCCBUGUHVEVHDPZSZTQVIVEVLVBVKSZTV
      EVHVBVKVCVHVBQVDVCVBBAABVBUIUPUJUKVMVBVJPZSTVKVNVBDVJFULUMGEUNUOUQVHDURUS
      AMMDCUTVA $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Miscellanea for polynomials
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d A t $.  $d C t $.
    $( Interpret range of a maps-to notation as a constraint on the definition.
       (Contributed by Stefan O'Rear, 10-Oct-2014.) $)
    mptfcl $p |- ( ( t e. A |-> B ) : A --> C -> ( t e. A -> B e. C ) ) $=
      ( cmpt wf wcel wral cv wi eqid fmpt rsp sylbir ) BDABCEZFCDGZABHAIBGPJABD
      COOKLPABMN $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Multivariate polynomials over the integers
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c mzPolyCld $.
  $c mzPoly $.
  $( Extend class notation to include pre-polynomial rings. $)
  cmzpcl $a class mzPolyCld $.
  $( Extend class notation to include polynomial rings. $)
  cmzp $a class mzPoly $.

  ${
    $d f g i j p v x $.
    $( Define the polynomially closed function rings over an arbitrary index
       set ` v ` .  The set ` ( mzPolyCld `` v ) ` contains all sets of
       functions from ` ( ZZ ^m v ) ` to ` ZZ ` which include all constants and
       projections and are closed under addition and multiplication.  This is a
       "temporary" set used to define the polynomial function ring itself
       ` ( mzPoly `` v ) ` ; see ~ df-mzp .  (Contributed by Stefan O'Rear,
       4-Oct-2014.) $)
    df-mzpcl $a |- mzPolyCld = ( v e. _V |-> { p e. ~P ( ZZ ^m ( ZZ ^m v ) ) |
        ( ( A. i e. ZZ ( ( ZZ ^m v ) X. { i } ) e. p
           /\ A. j e. v ( x e. ( ZZ ^m v ) |-> ( x ` j ) ) e. p )
    /\ A. f e. p A. g e. p ( ( f oF + g ) e. p /\ ( f oF x. g ) e. p ) ) } ) $.

    $( Polynomials over ` ZZ ` with an arbitrary index set, that is, the
       smallest ring of functions containing all constant functions and all
       projections.  This is almost the most general reasonable definition; to
       reach full generality, we would need to be able to replace ZZ with an
       arbitrary (semi)ring (and a coordinate subring), but rings have not been
       defined yet.  (Contributed by Stefan O'Rear, 4-Oct-2014.) $)
    df-mzp $a |- mzPoly = ( v e. _V |-> |^| ( mzPolyCld ` v ) ) $.
  $}

  ${
    $d V v p f g a b c $.  $d V v p i a b c $.  $d V v p j x a b c $.
    $( Substitution lemma for ` mzPolyCld ` .  (Contributed by Stefan O'Rear,
       4-Oct-2014.) $)
    mzpclval $p |- ( V e. _V -> ( mzPolyCld ` V ) =
      { p e. ~P ( ZZ ^m ( ZZ ^m V ) ) |
        ( ( A. i e. ZZ ( ( ZZ ^m V ) X. { i } ) e. p
           /\ A. j e. V ( x e. ( ZZ ^m V ) |-> ( x ` j ) ) e. p )
    /\ A. f e. p A. g e. p ( ( f oF + g ) e. p /\ ( f oF x. g ) e. p ) ) } ) $=
      ( vv va vc vb cz cv cmap co wcel wral cmpt wa eleq1d csn cxp cfv cof cmul
      caddc cpw crab cvv cmzpcl wceq oveq2 oveq2d pweqd xpeq1d ralbidv weq sneq
      xpeq2d cbvralvw bitrdi mpteq1d raleqbi1dv mpteq2dv cbvmptv eleq1i anbi12d
      fveq2 fveq1 anbi1d rabeqbidv df-mzpcl ovex pwex rabex fvmpt ) HFLHMZNOZIM
      ZUAZUBZGMZPZILQZJVRKMZJMZUCZRZWBPZKVQQZSZBMZCMZUFUDOWBPWLWMUEUDOWBPSCWBQB
      WBQZSZGLVRNOZUGZUHLFNOZDMZUAZUBZWBPZDLQZAWREMZAMZUCZRZWBPZEFQZSZWNSZGLWRN
      OZUGZUHUIUJVQFUKZWOXKGWQXMXNWPXLXNVRWRLNVQFLNULZUMUNXNWKXJWNXNWDXCWJXIXNW
      DWRVTUBZWBPZILQXCXNWCXQILXNWAXPWBXNVRWRVTXOUOTUPXQXBIDLIDUQZXPXAWBXRVTWTW
      RVSWSURUSTUTVAXNWJJWRWGRZWBPZKFQXIWIXTKVQFXNWHXSWBXNJVRWRWGXOVBTVCXTXHKEF
      KEUQZXTJWRXDWFUCZRZWBPXHYAXSYCWBYAJWRWGYBWEXDWFVHVDTYCXGWBJAWRYBXFXDWFXEV
      IVEVFVAUTVAVGVJVKJHBCIKGVLXKGXMXLLWRNVMVNVOVP $.
  $}

  ${
    $d V p f g $.  $d V p i $.  $d V p j x $.  $d P p f g $.  $d P p i $.
    $d P p j x $.
    $( Double substitution lemma for ` mzPolyCld ` .  (Contributed by Stefan
       O'Rear, 4-Oct-2014.) $)
    elmzpcl $p |- ( V e. _V -> ( P e. ( mzPolyCld ` V ) <->
        ( P C_ ( ZZ ^m ( ZZ ^m V ) )
       /\ ( ( A. i e. ZZ ( ( ZZ ^m V ) X. { i } ) e. P
           /\ A. j e. V ( x e. ( ZZ ^m V ) |-> ( x ` j ) ) e. P )
        /\ A. f e. P A. g e. P ( ( f oF + g ) e. P /\ ( f oF x. g ) e. P ) ) )
        ) ) $=
      ( vp wcel cfv cz cmap co cv wral wa cof eleq2 ralbidv anbi12d cvv csn cxp
      cmzpcl cmpt caddc cmul cpw crab wss mzpclval eleq2d wceq raleqbi1dv elrab
      ovex elpw2 anbi1i bitri bitrdi ) GUAIZBGUDJZIBKGLMZENUBUCZHNZIZEKOZAVCFNA
      NJUEZVEIZFGOZPZCNZDNZUFQMZVEIZVLVMUGQMZVEIZPZDVEOZCVEOZPZHKVCLMZUHZUIZIZB
      WBUJZVDBIZEKOZVHBIZFGOZPZVNBIZVPBIZPZDBOZCBOZPZPZVAVBWDBACDEFGHUKULWEBWCI
      ZWQPWRWAWQHBWCVEBUMZVKWKVTWPWTVGWHVJWJWTVFWGEKVEBVDRSWTVIWIFGVEBVHRSTVSWO
      CVEBVRWNDVEBWTVOWLVQWMVEBVNRVEBVPRTUNUNTUOWSWFWQBWBKVCLUPUQURUSUT $.
  $}

  ${
    $d V v f g a b $.  $d P v f g a b $.  $d F v f g a b $.  $d G v f g a b $.
    $( The set of all functions with the signature of a polynomial is a
       polynomially closed set.  This is a lemma to show that the intersection
       in ~ df-mzp is well-defined.  (Contributed by Stefan O'Rear,
       4-Oct-2014.) $)
    mzpclall $p |- ( V e. _V -> ( ZZ ^m ( ZZ ^m V ) ) e. ( mzPolyCld ` V ) ) $=
      ( vv vf vg va vb cz cv cmap co cmzpcl cfv wcel cvv wral wa caddc wf elmap
      zex wceq oveq2 fveq2 eleq12d wss csn cxp cmpt cof cmul ssid ovex constmap
      oveq2d rgen vex ffvelcdm sylanb ancoms fmpttd sylibr pm3.2i zaddcl adantl
      simpl simpr ovexd inidm off zmulcl anbi12i 3imtr4i rgen2 wb elmzpcl ax-mp
      jca mpbir2an vtoclg ) GGBHZIJZIJZVTKLZMZGGAIJZIJZAKLZMBANVTAUAZWBWFWCWGWH
      WAWEGIVTAGIUBUNVTAKUCUDWDWBWBUEZWACHZUFUGWBMZCGOZDWAWJDHZLZUHZWBMZCVTOZPZ
      WJWMQUIJZWBMZWJWMUJUIJZWBMZPZDWBOCWBOZPZWBUKWRXDWLWQWKCGWAWJGGVTIULZTUMUO
      WPCVTWJVTMZWAGWORWPXGDWAWNGWMWAMZXGWNGMZXHVTGWMRXGXIGVTWMTBUPZSVTGWJWMUQU
      RUSUTGWAWOTXFSVAUOVBXCCDWBWBWAGWJRZWAGWMRZPZWAGWSRZWAGXARZPWJWBMZWMWBMZPX
      CXMXNXOXMEFWAWAWAQGGGWJWMNNEHZGMFHZGMPZXRXSQJGMXMXRXSVCVDXKXLVEZXKXLVFZXM
      GVTIVGZYCWAVHZVIXMEFWAWAWAUJGGGWJWMNNXTXRXSUJJGMXMXRXSVJVDYAYBYCYCYDVIVQX
      PXKXQXLGWAWJTXFSGWAWMTXFSVKWTXNXBXOGWAWSTXFSGWAXATXFSVKVLVMVBVTNMWDWIXEPV
      NXJDWBCDCCVTVOVPVRVS $.

    $( Corollary of ~ mzpclall : polynomially closed function sets are not
       empty.  (Contributed by Stefan O'Rear, 4-Oct-2014.) $)
    mzpcln0 $p |- ( V e. _V -> ( mzPolyCld ` V ) =/= (/) ) $=
      ( cvv wcel cmzpcl cfv cz cmap co mzpclall ne0d ) ABCADEFFAGHGHAIJ $.

    $( Defining property 1 of a polynomially closed function set ` P ` : it
       contains all constant functions.  (Contributed by Stefan O'Rear,
       4-Oct-2014.) $)
    mzpcl1 $p |- ( ( P e. ( mzPolyCld ` V ) /\ F e. ZZ ) ->
      ( ( ZZ ^m V ) X. { F } ) e. P ) $=
      ( vf vg cmzpcl cfv wcel cz wa cmap co cv csn cxp wral simpr wss cof syl
      cmpt caddc cmul simpl cvv elfvex adantr elmzpcl mpbid simprll wceq xpeq2d
      wb sneq eleq1d rspcva syl2anc ) ACFGHZBIHZJZUSICKLZDMZNZOZAHZDIPZVABNZOZA
      HZURUSQUTAIVAKLRZVFEVAVBEMZGUAAHDCPZJVBVKUBSLAHVBVKUCSLAHJEAPDAPZJJZVFUTU
      RVNURUSUDUTCUEHZURVNUMURVOUSACFUFUGEADEDDCUHTUIVJVFVLVMUJTVEVIDBIVBBUKZVD
      VHAVPVCVGVAVBBUNULUOUPUQ $.

    $( Defining property 2 of a polynomially closed function set ` P ` : it
       contains all projections.  (Contributed by Stefan O'Rear,
       4-Oct-2014.) $)
    mzpcl2 $p |- ( ( P e. ( mzPolyCld ` V ) /\ F e. V ) ->
      ( g e. ( ZZ ^m V ) |-> ( g ` F ) ) e. P ) $=
      ( vf cmzpcl cfv wcel wa cz cmap co cv cmpt wral simpr wss csn cof syl cxp
      caddc cmul simpl cvv wb elfvex adantr elmzpcl mpbid simprlr wceq mpteq2dv
      fveq2 eleq1d rspcva syl2anc ) ADFGHZCDHZIZUSBJDKLZEMZBMZGZNZAHZEDOZBVACVC
      GZNZAHZURUSPUTAJVAKLQZVAVBRUAAHEJOZVGIVBVCUBSLAHVBVCUCSLAHIBAOEAOZIIZVGUT
      URVNURUSUDUTDUEHZURVNUFURVOUSADFUGUHBAEBEEDUITUJVKVLVGVMUKTVFVJECDVBCULZV
      EVIAVPBVAVDVHVBCVCUNUMUOUPUQ $.

    $( Defining properties 3 and 4 of a polynomially closed function set
       ` P ` : it is closed under pointwise addition and multiplication.
       (Contributed by Stefan O'Rear, 4-Oct-2014.) $)
    mzpcl34 $p |- ( ( P e. ( mzPolyCld ` V ) /\ F e. P /\ G e. P ) ->
      ( ( F oF + G ) e. P /\ ( F oF x. G ) e. P ) ) $=
      ( vf vg cmzpcl cfv wcel cv cof co wa wral cmap wceq oveq1 eleq1d anbi12d
      cz w3a caddc cmul simp2 simp3 wss csn cxp cmpt cvv wb elfvexd elmzpcl syl
      simp1 mpbid simprrd oveq2 rspc2va syl21anc ) ADGHIZBAIZCAIZUAZVBVCEJZFJZU
      BKZLZAIZVEVFUCKZLZAIZMZFANEANZBCVGLZAIZBCVJLZAIZMZVAVBVCUDVAVBVCUEVDATTDO
      LZOLUFZVTVEUGUHAIETNFVTVEVFHUIAIEDNMZVNVDVAWAWBVNMMZVAVBVCUOZVDDUJIVAWCUK
      VDAGDWDULFAEFEEDUMUNUPUQVMVSBVFVGLZAIZBVFVJLZAIZMEFBCAAVEBPZVIWFVLWHWIVHW
      EAVEBVFVGQRWIVKWGAVEBVFVJQRSVFCPZWFVPWHVRWJWEVOAVFCBVGURRWJWGVQAVFCBVJURR
      SUSUT $.
  $}

  ${
    $d V v f g a $.
    $( Value of the ` mzPoly ` function.  (Contributed by Stefan O'Rear,
       4-Oct-2014.) $)
    mzpval $p |- ( V e. _V -> ( mzPoly ` V ) = |^| ( mzPolyCld ` V ) ) $=
      ( vv cvv wcel cmzpcl cfv cint cmzp wceq c0 wne mzpcln0 intex sylib inteqd
      cv fveq2 df-mzp fvmptg mpdan ) ACDZAEFZGZCDZAHFUCIUAUBJKUDALUBMNBABPZEFZG
      UCCCHUEAIUFUBUEAEQOBRST $.

    $( ` mzPoly ` is defined for all index sets which are sets.  This is used
       with ~ elfvdm to eliminate sethood antecedents.  (Contributed by Stefan
       O'Rear, 4-Oct-2014.) $)
    dmmzp $p |- dom mzPoly = _V $=
      ( vv cmzp cdm cvv cv cmzpcl cfv cint cmpt df-mzp dmeqi wcel dmmptg c0 wne
      wceq mzpcln0 intex sylib mprg eqtri ) BCADAEZFGZHZIZCZDBUEAJKUDDLZUFDPADA
      DUDDMUBDLUCNOUGUBQUCRSTUA $.

    $( Polynomial closedness is a universal first-order property and passes to
       intersections.  This is where the closure properties of the polynomial
       ring itself are proved.  (Contributed by Stefan O'Rear, 4-Oct-2014.) $)
    mzpincl $p |- ( V e. _V -> ( mzPoly ` V ) e. ( mzPolyCld ` V ) ) $=
      ( vf vg va wcel cfv cz cmap co cv wral cof simpr simplr syl2anc ralrimiva
      wa ovex elint2 sylibr cvv cmzp cmzpcl cint mzpval wss csn cmpt caddc cmul
      cxp mzpclall intss1 syl mzpcl1 vsnex xpex mzpcl2 mptex jca wi vex mzpcl34
      3expib ralimia r19.26 3imtr3i syl2anb anbi12i a1i ralrimivv jca32 elmzpcl
      mpbird eqeltrd ) AUAEZAUBFAUCFZUDZVQAUEVPVRVQEVRGGAHIZHIZUFZVSBJZUGZUKZVR
      EZBGKZCVSWBCJZFZUHZVREZBAKZQZWBWGUILZIZVREZWBWGUJLZIZVREZQZCVRKBVRKZQQVPW
      AWLWTVPVTVQEWAAULVTVQUMUNVPWFWKVPWEBGVPWBGEZQZWDDJZEZDVQKWEXBXDDVQXBXCVQE
      ZQXEXAXDXBXEMVPXAXENXCWBAUOOPDWDVQVSWCGAHRZBUPUQSTPVPWJBAVPWBAEZQZWIXCEZD
      VQKWJXHXIDVQXHXEQXEXGXIXHXEMVPXGXENXCCWBAUROPDWIVQCVSWHXFUSSTPUTVPWSBCVRV
      RWBVREZWGVREZQZWSVAVPXLWNXCEZDVQKZWQXCEZDVQKZQZWSXJWBXCEZDVQKZWGXCEZDVQKZ
      XQXKDWBVQBVBSDWGVQCVBSXRXTQZDVQKXMXOQZDVQKXSYAQXQYBYCDVQXEXRXTYCXCWBWGAVC
      VDVEXRXTDVQVFXMXODVQVFVGVHWOXNWRXPDWNVQWBWGWMRSDWQVQWBWGWPRSVITVJVKVLCVRB
      CBBAVMVNVO $.
  $}

  $( Constant functions are polynomial.  See also ~ mzpconstmpt .  (Contributed
     by Stefan O'Rear, 4-Oct-2014.) $)
  mzpconst $p |- ( ( V e. _V /\ C e. ZZ ) ->
    ( ( ZZ ^m V ) X. { C } ) e. ( mzPoly ` V ) ) $=
    ( cvv wcel cmzp cfv cmzpcl cz cmap co csn cxp mzpincl mzpcl1 sylan ) BCDBEF
    ZBGFDAHDHBIJAKLPDBMPABNO $.

  $( A polynomial function is a function from the coordinate space to the
     integers.  (Contributed by Stefan O'Rear, 5-Oct-2014.) $)
  mzpf $p |- ( F e. ( mzPoly ` V ) -> F : ( ZZ ^m V ) --> ZZ ) $=
    ( cmzp cfv wcel cz cmap co wf cvv elfvex cmzpcl cint mzpval mzpclall intss1
    wss syl eqsstrd sselda anidms zex ovex elmap sylib ) ABCDZEZAFFBGHZGHZEZUHF
    AIUGUJUGUFUIAUGBJEZUFUIQABCKUKUFBLDZMZUIBNUKUIULEUMUIQBOUIULPRSRTUAFUHAUBFB
    GUCUDUE $.

  ${
    $d X g $.  $d V g $.
    $( A projection function is polynomial.  (Contributed by Stefan O'Rear,
       4-Oct-2014.) $)
    mzpproj $p |- ( ( V e. _V /\ X e. V ) -> ( g e. ( ZZ ^m V ) |-> ( g ` X ) )
        e. ( mzPoly ` V ) ) $=
      ( cvv wcel cmzp cfv cmzpcl cz cmap co cv cmpt mzpincl mzpcl2 sylan ) BDEB
      FGZBHGECBEAIBJKCALGMQEBNQACBOP $.
  $}

  $( The pointwise sum of two polynomial functions is a polynomial function.
     See also ~ mzpaddmpt .  (Contributed by Stefan O'Rear, 4-Oct-2014.) $)
  mzpadd $p |- ( ( A e. ( mzPoly ` V ) /\ B e. ( mzPoly ` V ) ) ->
    ( A oF + B ) e. ( mzPoly ` V ) ) $=
    ( cmzp cfv wcel caddc cof cmul cmzpcl cvv elfvex adantr mzpincl syl mzpcl34
    wa co 3expib mpcom simpld ) ACDEZFZBUBFZQZABGHRUBFZABIHRUBFZUBCJEFZUEUFUGQZ
    UECKFZUHUCUJUDACDLMCNOUHUCUDUIUBABCPSTUA $.

  $( The pointwise product of two polynomial functions is a polynomial
     function.  See also ~ mzpmulmpt .  (Contributed by Stefan O'Rear,
     4-Oct-2014.) $)
  mzpmul $p |- ( ( A e. ( mzPoly ` V ) /\ B e. ( mzPoly ` V ) ) ->
    ( A oF x. B ) e. ( mzPoly ` V ) ) $=
    ( cmzp cfv wcel caddc cof cmul cmzpcl cvv elfvex adantr mzpincl syl mzpcl34
    wa co 3expib mpcom simprd ) ACDEZFZBUBFZQZABGHRUBFZABIHRUBFZUBCJEFZUEUFUGQZ
    UECKFZUHUCUJUDACDLMCNOUHUCUDUIUBABCPSTUA $.

  ${
    $d V x a b $.  $d C x $.  $d D x a b $.  $d A a b $.

    $( A constant function expressed in maps-to notation is polynomial.  This
       theorem and the several that follow ( ~ mzpaddmpt , ~ mzpmulmpt ,
       ~ mzpnegmpt , ~ mzpsubmpt , ~ mzpexpmpt ) can be used to build proofs
       that functions which are "manifestly polynomial", in the sense of being
       a maps-to containing constants, projections, and simple arithmetic
       operations, are actually polynomial functions.  There is no mzpprojmpt
       because ~ mzpproj is already expressed using maps-to notation.
       (Contributed by Stefan O'Rear, 5-Oct-2014.) $)
    mzpconstmpt $p |- ( ( V e. _V /\ C e. ZZ ) ->
      ( x e. ( ZZ ^m V ) |-> C ) e. ( mzPoly ` V ) ) $=
      ( cvv wcel cz wa cmap cmpt csn cxp cmzp cfv fconstmpt mzpconst eqeltrrid
      co ) CDEBFEGAFCHQZBIRBJKCLMARBNBCOP $.

    $( Sum of polynomial functions is polynomial.  Maps-to version of
       ~ mzpadd .  (Contributed by Stefan O'Rear, 5-Oct-2014.) $)
    mzpaddmpt $p |- ( ( ( x e. ( ZZ ^m V ) |-> A ) e. ( mzPoly ` V ) /\ ( x e.
        ( ZZ ^m V ) |-> B ) e. ( mzPoly ` V ) ) ->
        ( x e. ( ZZ ^m V ) |-> ( A + B ) ) e. ( mzPoly ` V ) ) $=
      ( cz cmap co cmpt cmzp cfv wcel wa caddc cof wfn wceq mzpf ffnd cvv ovex
      ofmpteq mp3an1 syl2an mzpadd eqeltrrd ) AEDFGZBHZDIJZKZAUFCHZUHKZLUGUJMNG
      ZAUFBCMGHZUHUIUGUFOZUJUFOZULUMPZUKUIUFEUGUGDQRUKUFEUJUJDQRUFSKUNUOUPEDFTA
      UFBCMSUAUBUCUGUJDUDUE $.

    $( Product of polynomial functions is polynomial.  Maps-to version of
       ~ mzpmulmpt .  (Contributed by Stefan O'Rear, 5-Oct-2014.) $)
    mzpmulmpt $p |- ( ( ( x e. ( ZZ ^m V ) |-> A ) e. ( mzPoly ` V ) /\
      ( x e. ( ZZ ^m V ) |-> B ) e. ( mzPoly ` V ) ) ->
        ( x e. ( ZZ ^m V ) |-> ( A x. B ) ) e. ( mzPoly ` V ) ) $=
      ( cz cmap co cmpt cmzp cfv wcel wa cmul cof wfn wceq mzpf ffnd cvv ovex
      ofmpteq mp3an1 syl2an mzpmul eqeltrrd ) AEDFGZBHZDIJZKZAUFCHZUHKZLUGUJMNG
      ZAUFBCMGHZUHUIUGUFOZUJUFOZULUMPZUKUIUFEUGUGDQRUKUFEUJUJDQRUFSKUNUOUPEDFTA
      UFBCMSUAUBUCUGUJDUDUE $.

    $( The difference of two polynomial functions is polynomial.  (Contributed
       by Stefan O'Rear, 10-Oct-2014.) $)
    mzpsubmpt $p |- ( ( ( x e. ( ZZ ^m V ) |-> A ) e. ( mzPoly ` V ) /\
      ( x e. ( ZZ ^m V ) |-> B ) e. ( mzPoly ` V ) ) ->
        ( x e. ( ZZ ^m V ) |-> ( A - B ) ) e. ( mzPoly ` V ) ) $=
      ( cz cmap co cmpt cmzp wcel cneg caddc nfmpt1 nfel1 mzpf mptfcl sylc zcnd
      wa wf cfv cmin c1 cmul nfan ad2antlr simpr mulm1d oveq2d ad2antrr negsubd
      cv eqtr2d mpteq2da cvv elfvex neg1z mzpconstmpt sylancl mzpmulmpt mpancom
      mzpaddmpt sylan2 eqeltrd ) AEDFGZBHZDIUAZJZAVECHZVGJZSZAVEBCUBGZHAVEBUCKZ
      CUDGZLGZHZVGVKAVEVLVOVHVJAAVFVGAVEBMNAVIVGAVECMNUEVKAULVEJZSZVOBCKZLGVLVR
      VNVSBLVRCVRCVRVEEVITZVQCEJVJVTVHVQVIDOUFVKVQUGZAVECEPQRZUHUIVRBCVRBVRVEEV
      FTZVQBEJVHWCVJVQVFDOUJWAAVEBEPQRWBUKUMUNVJVHAVEVNHVGJZVPVGJAVEVMHVGJZVJWD
      VJDUOJVMEJWEVIDIUPUQAVMDURUSAVMCDUTVAABVNDVBVCVD $.

    $( Negation of a polynomial function.  (Contributed by Stefan O'Rear,
       11-Oct-2014.) $)
    mzpnegmpt $p |- ( ( x e. ( ZZ ^m V ) |-> A ) e. ( mzPoly ` V ) ->
        ( x e. ( ZZ ^m V ) |-> -u A ) e. ( mzPoly ` V ) ) $=
      ( cz cmap cmpt cmzp cfv wcel cneg cc0 cmin df-neg mpteq2i cvv mzpconstmpt
      co elfvex 0z sylancl mzpsubmpt mpancom eqeltrid ) ADCEQZBFZCGHZIZAUDBJZFA
      UDKBLQZFZUFAUDUHUIBMNAUDKFUFIZUGUJUFIUGCOIKDIUKUECGRSAKCPTAKBCUAUBUC $.

    $( Raise a polynomial function to a (fixed) exponent.  (Contributed by
       Stefan O'Rear, 5-Oct-2014.) $)
    mzpexpmpt $p |- ( ( ( x e. ( ZZ ^m V ) |-> A ) e. ( mzPoly ` V ) /\
        D e. NN0 ) -> ( x e. ( ZZ ^m V ) |-> ( A ^ D ) ) e. ( mzPoly ` V ) ) $=
      ( wcel cz co cmpt cexp cv wi cc0 c1 wceq oveq2 mpteq2dv eleq1d imbi2d cc
      wa va vb cn0 cmap cmzp cfv caddc wral wf wss mzpf zsscn sylancl eqid fmpt
      fss sylibr nfra1 exp0d mpteq2da syl cvv elfvex 1z mzpconstmpt eqeltrd w3a
      rspa cmul 3ad2ant2 simp1 nfv nfan adantlr simplr expp1d syl2anc mzpmulmpt
      simp3 simp2 3exp a2d nn0ind impcom ) CUCEAFDUDGZBHZDUEUFZEZAWEBCIGZHZWGEZ
      WHAWEBUAJZIGZHZWGEZKWHAWEBLIGZHZWGEZKWHAWEBUBJZIGZHZWGEZKWHAWEBWSMUGGZIGZ
      HZWGEZKWHWKKUAUBCWLLNZWOWRWHXGWNWQWGXGAWEWMWPWLLBIOPQRWLWSNZWOXBWHXHWNXAW
      GXHAWEWMWTWLWSBIOPQRWLXCNZWOXFWHXIWNXEWGXIAWEWMXDWLXCBIOPQRWLCNZWOWKWHXJW
      NWJWGXJAWEWMWIWLCBIOPQRWHWQAWEMHZWGWHBSEZAWEUHZWQXKNWHWESWFUIZXMWHWEFWFUI
      FSUJXNWFDUKULWEFSWFUPUMAWESBWFWFUNUOUQZXMAWEWPMXLAWEURZXMAJWEEZTBXLAWEVHZ
      USUTVAWHDVBEMFEXKWGEWFDUEVCVDAMDVEUMVFWSUCEZWHXBXFXSWHXBXFXSWHXBVGZXEAWEW
      TBVIGZHZWGXTXMXSXEYBNWHXSXMXBXOVJXSWHXBVKXMXSTZAWEXDYAXMXSAXPXSAVLVMYCXQT
      BWSXMXQXLXSXRVNXMXSXQVOVPUTVQXTXBWHYBWGEXSWHXBVSXSWHXBVTAWTBDVRVQVFWAWBWC
      WD $.
  $}

  ${
    $d ph x f g $.  $d ps f g $.  $d ch x $.  $d th x $.  $d ta x $.
    $d et x $.  $d ze x $.  $d si x $.  $d rh x $.  $d V x f g a b $.
    $d A x $.
    mzpindd.co $e |- ( ( ph /\ f e. ZZ ) -> ch ) $.
    mzpindd.pr $e |- ( ( ph /\ f e. V ) -> th ) $.
    mzpindd.ad $e |- ( ( ph /\ ( f : ( ZZ ^m V ) --> ZZ /\ ta ) /\ ( g : ( ZZ
        ^m V ) --> ZZ /\ et ) ) -> ze ) $.
    mzpindd.mu $e |- ( ( ph /\ ( f : ( ZZ ^m V ) --> ZZ /\ ta ) /\ ( g : ( ZZ
        ^m V ) --> ZZ /\ et ) ) -> si ) $.
    mzpindd.1 $e |- ( x = ( ( ZZ ^m V ) X. { f } ) -> ( ps <-> ch ) ) $.
    mzpindd.2 $e |- ( x = ( g e. ( ZZ ^m V ) |-> ( g ` f ) ) -> ( ps <-> th ) )
        $.
    mzpindd.3 $e |- ( x = f -> ( ps <-> ta ) ) $.
    mzpindd.4 $e |- ( x = g -> ( ps <-> et ) ) $.
    mzpindd.5 $e |- ( x = ( f oF + g ) -> ( ps <-> ze ) ) $.
    mzpindd.6 $e |- ( x = ( f oF x. g ) -> ( ps <-> si ) ) $.
    mzpindd.7 $e |- ( x = A -> ( ps <-> rh ) ) $.
    $( "Structural" induction to prove properties of all polynomial functions.
       (Contributed by Stefan O'Rear, 4-Oct-2014.) $)
    mzpindd $p |- ( ( ph /\ A e. ( mzPoly ` V ) ) -> rh ) $=
      ( va vb cmzp cfv wcel wa cz cmap co crab elfvex adantl cmzpcl cint mzpval
      cvv wceq wss cv csn cxp wral cmpt caddc cof cmul ssrab2 a1i ovex constmap
      zex elrab sylanbrc ralrimiva adantr wf simpllr simpr elmapg biimpa simplr
      syl21anc ffvelcdmd fmpttd elmap sylibr adantlr jca zaddcl simpl inidm off
      ad2ant2r 3expb zmulcl jca32 ex anbi1i anbi12i 3imtr4g ralrimivv wb mpbird
      elmzpcl intss1 syl eqsstrd sselda an32s mpdan simprbi ) AKNUHUIZUJZUKZKBJ
      ULULNUMUNZUMUNZUOZUJZIXSNVAUJZYCXRYDAKNUHUPUQAYDXRYCAYDUKZXQYBKYEXQNURUIZ
      USZYBYDXQYGVBANUTUQYEYBYFUJZYGYBVCYEYHYBYAVCZXTLVDZVEVFZYBUJZLULVGZMXTYJM
      VDZUIZVHZYBUJZLNVGZUKZYJYNVIVJUNZYBUJZYJYNVKVJUNZYBUJZUKZMYBVGLYBVGZUKUKZ
      YEYIYSUUEYIYEBJYAVLVMYEYMYRAYMYDAYLLULAYJULUJZUKYKYAUJZCYLUUGUUHAXTYJULUL
      NUMVNZVPVOUQOBCJYKYASVQVRVSVTYEYQLNYEYJNUJZUKZYPYAUJZDYQUUKXTULYPWAUULUUK
      MXTYOULUUKYNXTUJZUKZNULYJYNUUNULVAUJZYDUUMNULYNWAZUUOUUNVPVMAYDUUJUUMWBUU
      KUUMWCUUOYDUKUUMUUPULNYNVAVAWDWEWGYEUUJUUMWFWHWIULXTYPVPUUIWJWKAUUJDYDPWL
      BDJYPYATVQVRVSWMAUUEYDAUUDLMYBYBAYJYAUJZEUKZYNYAUJZFUKZUKZYTYAUJZGUKZUUBY
      AUJZHUKZUKZYJYBUJZYNYBUJZUKUUDAXTULYJWAZEUKZXTULYNWAZFUKZUKZXTULYTWAZGUKZ
      XTULUUBWAZHUKZUKZUVAUVFAUVMUVRAUVMUKZUVOUVPHUVSUVNGUVMUVNAUVIUVKUVNEFUVIU
      VKUKZUFUGXTXTXTVIULULULYJYNVAVAUFVDZULUJUGVDZULUJUKZUWAUWBVIUNULUJUVTUWAU
      WBWNUQUVIUVKWOZUVIUVKWCZXTVAUJUVTUUIVMZUWFXTWPZWQWRUQAUVJUVLGQWSWMUVMUVPA
      UVIUVKUVPEFUVTUFUGXTXTXTVKULULULYJYNVAVAUWCUWAUWBVKUNULUJUVTUWAUWBWTUQUWD
      UWEUWFUWFUWGWQWRUQAUVJUVLHRWSXAXBUURUVJUUTUVLUUQUVIEULXTYJVPUUIWJXCUUSUVK
      FULXTYNVPUUIWJXCXDUVCUVOUVEUVQUVBUVNGULXTYTVPUUIWJXCUVDUVPHULXTUUBVPUUIWJ
      XCXDXEUVGUURUVHUUTBEJYJYAUAVQBFJYNYAUBVQXDUUAUVCUUCUVEBGJYTYAUCVQBHJUUBYA
      UDVQXDXEXFVTXAYDYHUUFXGAMYBLMLLNXIUQXHYBYFXJXKXLXMXNXOYCKYAUJIBIJKYAUEVQX
      PXK $.
  $}

  ${
    $d I a b x y $.  $d I f g $.  $d b f g $.
    $( Relationship between multivariate Z-polynomials and general multivariate
       polynomial functions.  (Contributed by Stefan O'Rear, 20-Mar-2015.)
       (Revised by AV, 13-Jun-2019.) $)
    mzpmfp $p |- ( mzPoly ` I ) = ran ( I eval ZZring ) $=
      ( va vb vg vy cvv wcel cfv czring cevl co cv cz caddc wa zringbas syl2anc
      a1i eleq1 c0 vf cmzp crn wceq cmap csn cxp cmpt cof cmul ces evlval rneqi
      vx eqid simpl zringcrng csubrg crg zringring subrgid ax-mp simpr mpfconst
      ccrg mpfproj wf w3a simp2r zringplusg mpfaddcl zringmulr mpfmulcl mzpindd
      simp3r simprlr simprrr mzpadd mzpmul adantlr mzpproj mpfind impbida eqrdv
      mzpconst fvprc cbs df-evl reldmmpo ovprc1 rneqd rn0 eqtrdi eqtr4d pm2.61i
      wn ) AFGZAUBHZAIJKZUCZUDWQBWRWTWQBLZWRGZXAWTGZWQCLZWTGMAUEKZUALZUFUGZWTGD
      XEXFDLZHUHZWTGXFWTGZXHWTGZXFXHNUIZKZWTGZXFXHUJUIZKZWTGZXCCXAUADAWQXFMGZOZ
      MWTMIAFXFPWSMAIUKKHMWSIAWSUOPULUMZWQXRUPIVEGZXSUQRMIURHGZXSIUSGYBUTMIPVAV
      BZRWQXRVCVDWQXFAGZOZMWTMIDAXFFPXTWQYDUPYAYEUQRYBYEYCRWQYDVCVFWQXEMXFVGZXJ
      OZXEMXHVGZXKOZVHZXJXKXNWQYFXJYIVIZWQYGYHXKVOZNWTMIXFXHAXTVJVKQYJXJXKXQYKY
      LWTMIUJXFXHAXTVLVMQXDXGWTSXDXIWTSXDXFWTSXDXHWTSXDXMWTSXDXPWTSXDXAWTSVNWQX
      COZXDWRGXEUNLZUFUGZWRGZEXEYNELZHUHZWRGZYNWRGZYQWRGZYNYQXLKZWRGZYNYQXOKZWR
      GZXBCXAMNWTMIUJUNEAPVJVLXTYMYNWTGZYTOZYQWTGZUUAOZOOZYTUUAUUCYMUUFYTUUIVPZ
      YMUUGUUHUUAVQZYNYQAVRQUUJYTUUAUUEUUKUULYNYQAVSQXDYOWRSXDYRWRSXDYNWRSXDYQW
      RSXDUUBWRSXDUUDWRSXDXAWRSWQYNMGYPXCYNAWEVTWQYNAGYSXCEAYNWAVTWQXCVCWBWCWDW
      QWPZWRTWTAUBWFUUMWTTUCTUUMWSTAIJBCFFXDWGHXAXDUKKHJBCWHWIWJWKWLWMWNWO $.
  $}

  ${
    $d W a b c x y $.  $d F a b c x $.  $d V a b c x y $.  $d G a b c x $.

    $( Substituting polynomials for the variables of a polynomial results in a
       polynomial. ` G ` is expected to depend on ` y ` and provide the
       polynomials which are being substituted.  (Contributed by Stefan O'Rear,
       5-Oct-2014.) $)
    mzpsubst $p |- ( ( W e. _V /\ F e. ( mzPoly ` V ) /\ A. y e. V G e. (
        mzPoly ` W ) ) ->
        ( x e. ( ZZ ^m W ) |-> ( F ` ( y e. V |-> ( G ` x ) ) ) ) e. ( mzPoly `
        W ) ) $=
      ( va cvv wcel cfv cz co cv cmpt wa wceq simpr fveq1 eleq1d mpteq2dv vb vc
      cmzp wral w3a simp1 elfvex 3ad2ant2 simp3 simp2 csn cxp caddc cof simpll3
      cmap cmul simpll2 wf mzpf ffvelcdmda expcom ralimdv imp eqid sylib adantr
      fmpt wb zex elmapg sylancr mpbird syl21anc fvconst2 mpteq2dva mzpconstmpt
      vex syl 3ad2antl1 eqeltrd csb fvex simplr csbeq1 fveq1d nfcv nfcsb1v nffv
      fvmpt csbeq1a cbvmpt fvmptg sylancl eqtrd simpl3 rspc sylc feqmptd eqtr4d
      nfel1 wfn simp2l ffnd simp3l simp13 simplll simpllr ovexd simplrl simplrr
      simp12 fnfvof syl22anc simp2r simp3r mzpaddmpt syl2anc mzpmulmpt syl31anc
      mzpindd ) FHIZCEUCJIZDFUCJZIZBEUDZUEYBEHIZYFYCAKFUPLZBEAMZDJZNZCJZNZYDIZY
      BYCYFUFYCYBYGYFCEUCUGUHYBYCYFUIYBYCYFUJYBYGYFUEZAYHYKGMZJZNZYDIAYHYKKEUPL
      ZUAMZUKULZJZNZYDIAYHYKUBYSYTUBMZJZNZJZNZYDIAYHYKYTJZNZYDIZAYHYKUUDJZNZYDI
      ZAYHYKYTUUDUMUNLZJZNZYDIAYHYKYTUUDUQUNLZJZNZYDIYNGCUAUBEYOYTKIZOZUUCAYHYT
      NZYDUVBAYHUUBYTUVBYIYHIZOZYKYSIZUUBYTPUVEUVDYFYGUVFUVBUVDQYBYGYFUVAUVDUOY
      BYGYFUVAUVDURUVDYFOZYGOZUVFEKYKUSZUVGUVIYGUVGYJKIZBEUDZUVIUVDYFUVKUVDYEUV
      JBEYEUVDUVJYEYHKYIDDFUTVAVBVCZVDBEKYJYKYKVEVHZVFVGUVHKHIZYGUVFUVIVIZVJUVG
      YGQKEYKHHVKZVLVMZVNYSYTYKUAVRVOVSVPYBYGUVAUVCYDIYFAYTFVQVTWAYOYTEIZOZUUHB
      YTDWBZYDUVSUUHAYHYIUVTJZNUVTUVSAYHUUGUWAUVSUVDOZUUGYTYKJZUWAUWBUVFUUGUWCP
      UWBUVDYFYGUVFUVSUVDQYBYGYFUVRUVDUOYBYGYFUVRUVDURUVQVNUBYKUUEUWCYSUUFYTUUD
      YKRUUFVEYTYKWCWJVSUWBUVRUWAHIUWCUWAPYOUVRUVDWDYIUVTWCGYTYIBYPDWBZJZUWAEHY
      KYPYTPZYIUWDUVTBYPYTDWEWFBGEYJUWEGYJWGBYIUWDBYPDWHBYIWGWIBMZYPPYIDUWDBYPD
      WKWFWLWMWNWOVPUVSAYHKUVTUVSUVTYDIZYHKUVTUSUVSUVRYFUWHYOUVRQYBYGYFUVRWPYEU
      WHBYTEBUVTYDBYTDWHXAUWGYTPDUVTYDBYTDWKSWQWRZUVTFUTVSWSWTUWIWAYOYSKYTUSZUU
      KOZYSKUUDUSZUUNOZUEZUUQAYHUUIUULUMLZNZYDUWNYTYSXBZUUDYSXBZYFYGUUQUWPPUWNY
      SKYTYOUWJUUKUWMXCXDZUWNYSKUUDYOUWKUWLUUNXEXDZYBYGYFUWKUWMXFZYBYGYFUWKUWMX
      LZUWQUWROZYFYGOZOZAYHUUPUWOUXEUVDOZUWQUWRYSHIZUVFUUPUWOPUWQUWRUXDUVDXGZUW
      QUWRUXDUVDXHZUXFKEUPXIZUXFUVFUVIUXFUVKUVIUXFUVDYFUVKUXEUVDQUXCYFYGUVDXJUV
      LWRUVMVFUXFUVNYGUVOVJUXCYFYGUVDXKUVPVLVMZYSUMYTUUDHYKXMXNVPXNUWNUUKUUNUWP
      YDIYOUWJUUKUWMXOZYOUWKUWLUUNXPZAUUIUULFXQXRWAUWNUUTAYHUUIUULUQLZNZYDUWNUW
      QUWRYFYGUUTUXOPUWSUWTUXAUXBUXEAYHUUSUXNUXFUWQUWRUXGUVFUUSUXNPUXHUXIUXJUXK
      YSUQYTUUDHYKXMXNVPXNUWNUUKUUNUXOYDIUXLUXMAUUIUULFXSXRWAYPUUAPZYRUUCYDUXPA
      YHYQUUBYKYPUUARTSYPUUFPZYRUUHYDUXQAYHYQUUGYKYPUUFRTSUWFYRUUJYDUWFAYHYQUUI
      YKYPYTRTSYPUUDPZYRUUMYDUXRAYHYQUULYKYPUUDRTSYPUUOPZYRUUQYDUXSAYHYQUUPYKYP
      UUORTSYPUURPZYRUUTYDUXTAYHYQUUSYKYPUURRTSYPCPZYRYMYDUYAAYHYQYLYKYPCRTSYAX
      T $.
  $}

  ${
    $d W x a b $.  $d F x a b $.  $d R x a b $.  $d V a x $.
    $( Simplified version of ~ mzpsubst to simply relabel variables in a
       polynomial.  (Contributed by Stefan O'Rear, 5-Oct-2014.) $)
    mzprename $p |- ( ( W e. _V /\ F e. ( mzPoly ` V ) /\ R : V --> W ) ->
        ( x e. ( ZZ ^m W ) |-> ( F ` ( x o. R ) ) ) e. ( mzPoly ` W ) ) $=
      ( va vb cvv wcel cmzp cfv wf w3a cz cv cmpt wceq wa syl2anc mpteq2dva zex
      cmap co ccom simpr wb simpll elmapg sylancr mpbid simplr fcompt eqid fvex
      fveq1 fvmpt ad2antlr eqcomd fveq2d 3adant2 wral simpl1 ffvelcdm 3ad2antl3
      eqtrd mzpproj ralrimiva mzpsubst syld3an3 eqeltrd ) EHIZCDJKIZDEBLZMZANEU
      BUCZAOZBUDZCKZPZAVOFDVPGVOFOZBKZGOZKZPZKZPZCKZPZEJKZVKVMVSWHQVLVKVMRZAVOV
      RWGWJVPVOIZRZVQWFCWLVQFDWAVPKZPZWFWLENVPLZVMVQWNQWLWKWOWJWKUEWLNHIVKWKWOU
      FUAVKVMWKUGNEVPHHUHUIUJVKVMWKUKFVPBDENULSWLFDWMWEWLVTDIZRWEWMWKWEWMQWJWPG
      VPWCWMVOWDWAWBVPUOWDUMWAVPUNUPUQURTVEUSTUTVKVLVMWDWIIZFDVAWHWIIVNWQFDVNWP
      RVKWAEIZWQVKVLVMWPVBVMVKWPWRVLDEVTBVCVDGEWAVFSVGAFCWDDEVHVIVJ $.
  $}

  ${
    $d W x $.  $d F x $.  $d V x $.
    $( A polynomial is a polynomial over all larger index sets.  (Contributed
       by Stefan O'Rear, 5-Oct-2014.)  (Revised by Stefan O'Rear,
       5-Jun-2015.) $)
    mzpresrename $p |- ( ( W e. _V /\ V C_ W /\ F e. ( mzPoly ` V ) ) -> ( x e.
        ( ZZ ^m W ) |-> ( F ` ( x |` V ) ) ) e. ( mzPoly ` W ) ) $=
      ( cvv wcel wss cmzp cfv w3a cz cmap co cv cres cmpt cid ccom coires1 wf
      fveq2i mpteq2i simp1 simp3 wf1o f1oi f1of ax-mp fss mpan 3ad2ant2 syl3anc
      mzprename eqeltrrid ) DEFZCDGZBCHIFZJZAKDLMZANZCOZBIZPAUSUTQCOZRZBIZPZDHI
      ZAUSVEVBVDVABUTCSUAUBURUOUQCDVCTZVFVGFUOUPUQUCUOUPUQUDUPUOVHUQCCVCTZUPVHC
      CVCUEVICUFCCVCUGUHCCDVCUIUJUKAVCBCDUMULUN $.
  $}

  ${
    $d A a b d e f g h i j k l $.  $d B a b c d e f g h i j k l $.
    mzpcompact2lem.i $e |- B e. _V $.
    $( Lemma for ~ mzpcompact2 .  (Contributed by Stefan O'Rear,
       9-Oct-2014.) $)
    mzpcompact2lem $p |- ( A e. ( mzPoly ` B )
        -> E. a e. Fin E. b e. ( mzPoly ` a ) ( a C_ B
          /\ A = ( c e. ( ZZ ^m B ) |-> ( b ` ( c |` a ) ) ) ) ) $=
      ( vd cmzp cfv wcel cv cz co cmpt wceq wa wrex cfn c0 anbi2d ve vf vg cmap
      vh vi vj vk wss cres wtru tru csn cxp caddc cof cmul 0fi cvv 0ex mzpconst
      vl mpan 0ss a1i fconstmpt simpr elmapssres sylancl vex fvconst2 mpteq2dva
      eqtr4id fveq1 mpteq2dv eqeq2d rspcev syl12anc fveq2 reseq2 fveq2d anbi12d
      syl sseq1 rexeqbidv sylancr adantl snfi vsnex vsnid mzpproj mp2an cbvmptv
      snssi simpl snssd syl2anc eqid fvmpt fvres ax-mp eqtr2di eqtrid wf w3a wi
      fvex simplll simprll unfi unex ssun1 simpllr mzpresrename syl3anc simprlr
      cun mzpaddmpt simplr simprr wfn ovex mzpf ffn 3syl ofmpteq reseq1 oveq12d
      ssun2 resabs1 fveq2i oveq12i eqtrd eqeq1d rexbidv eqeq1 2rexbidv cbvrexvw
      weq bitrdi unssd elmapi fssres syl2anr zex elmap sylibr adantlrr adantrrr
      mzpmulmpt simplrr mpbird r19.40 exp32 rexlimdvv ex rexlimivv imp ad2ant2l
      simprrr 3adant1 simpld simprd mzpindd eqeq2i anbi2i 2rexbii sylib ) ABHIZ
      JZCKZBUIZAGLBUDMZGKZUVKUJZDKZIZNZOZPZDUVKHIZQCRQZUVLAEUVMEKZUVKUJZUVPIZNZ
      OZPZDUWAQCRQUKUVJUWBULUKUVLUAKZUVROZPZDUWAQCRQZUVLUVMUBKZUMZUNZUVROZPZDUW
      AQZCRQZUVLUCUVMUWMUCKZIZNZUVROZPZDUWAQZCRQZUEKZBUIZUWMGUVMUVNUXGUJZUFKZIZ
      NZOZPZUFUXGHIZQZUERQZUGKZBUIZUWTGUVMUVNUXRUJZUHKZIZNZOZPZUHUXRHIZQZUGRQZU
      VLUWMUWTUOUPZMZUVROZPZDUWAQZCRQZUVLUWMUWTUQUPZMZUVROZPZDUWAQZCRQZUWBUAAUB
      UCBUWMLJZUWSUKVUASRJSBUIZUWOGUVMUVNSUJZUVPIZNZOZPZDSHIZQZUWSURVUALSUDMZUW
      NUNZVUHJZVUBUWOGUVMVUCVUKIZNZOZVUISUSJVUAVULUTUWMSVAVCVUBVUABVDZVEVUAUWOG
      UVMUWMNVUNGUVMUWMVFVUAGUVMVUMUWMVUAUVNUVMJZPZVUCVUJJZVUMUWMOVURVUQVUBVUSV
      UAVUQVGVUPUVNLBSVHVIVUJUWMVUCUBVJVKWCVLVMVUGVUBVUOPDVUKVUHUVPVUKOZVUFVUOV
      UBVUTVUEVUNUWOVUTGUVMVUDVUMVUCUVPVUKVNVOVPTVQVRUWRVUICSRUVKSOZUWQVUGDUWAV
      UHUVKSHVSVVAUVLVUBUWPVUFUVKSBWDVVAUVRVUEUWOVVAGUVMUVQVUDVVAUVOVUCUVPUVKSU
      VNVTWAVOVPWBWEVQWFWGUWMBJZUXFUKVVBUWNRJUWNBUIZUXBGUVMUVNUWNUJZUVPIZNZOZPZ
      DUWNHIZQZUXFUWMWHVVBUCLUWNUDMZUXANZVVIJZVVCUXBGUVMVVDVVLIZNZOZVVJVVMVVBUW
      NUSJUWMUWNJZVVMUBWIUBWJZUCUWNUWMWKWLVEUWMBWNVVBUXBGUVMUWMUVNIZNVVOUCGUVMU
      XAVVSUWMUWTUVNVNWMVVBGUVMVVSVVNVVBVUQPZVVNUWMVVDIZVVSVVTVVDVVKJZVVNVWAOVV
      TVUQVVCVWBVVBVUQVGVVTUWMBVVBVUQWOWPUVNLBUWNVHWQUCVVDUXAVWAVVKVVLUWMUWTVVD
      VNVVLWRUWMVVDXGWSWCVVQVWAVVSOVVRUWMUWNUVNWTXAXBVLXCVVHVVCVVPPDVVLVVIUVPVV
      LOZVVGVVPVVCVWCVVFVVOUXBVWCGUVMVVEVVNVVDUVPVVLVNVOVPTVQVRUXEVVJCUWNRUVKUW
      NOZUXDVVHDUWAVVIUVKUWNHVSVWDUVLVVCUXCVVGUVKUWNBWDVWDUVRVVFUXBVWDGUVMUVQVV
      EVWDUVOVVDUVPUVKUWNUVNVTWAVOVPWBWEVQWFWGUKUVMLUWMXDZUXQPZUVMLUWTXDZUYHPZX
      EZUYNUYTVWFVWHUYNUYTPZUKUXQUYHVWJVWEVWGUXQUYHVWJUXNUYHVWJXFZUEUFRUXOUXGRJ
      ZUXJUXOJZPZUXNVWKVWNUXNPZUYEVWJUGUHRUYFVWOUXRRJZUYAUYFJZPZUYEVWJVWOVWRUYE
      PZPZUYMUYSPZCRQZVWJVWTVXBUVLUXLUYCUYIMZUVROZPZDUWAQZUVLUXLUYCUYOMZUVROZPZ
      DUWAQZPZCRQZVWOVWRUXSVXLUYDVWNUXHVWRUXSPZVXLUXMVWNUXHPZVXMPZUXGUXRXQZRJZV
      XPBUIZVXCGUVMUVNVXPUJZUVPIZNZOZPZDVXPHIZQZVXRVXGVYAOZPZDVYDQZVXLVXOVWLVWP
      VXQVWLVWMUXHVXMXHVXNVWPVWQUXSXIUXGUXRXJWQVXOVBLVXPUDMZVBKZUXGUJZUXJIZVYJU
      XRUJZUYAIZUOMZNZVYDJZVXRVXCGUVMVXSVYPIZNZOZVYEVXOVBVYIVYLNVYDJZVBVYIVYNNV
      YDJZVYQVXOVXPUSJZUXGVXPUIZVWMWUAWUCVXOUXGUXRUEVJUGVJXKZVEZWUDVXOUXGUXRXLZ
      VEVWLVWMUXHVXMXMZVBUXJUXGVXPXNXOZVXOWUCUXRVXPUIZVWQWUBWUFWUJVXOUXRUXGYIZV
      EVXNVWPVWQUXSXPZVBUYAUXRVXPXNXOZVBVYLVYNVXPXRWQVXOUXGUXRBVWNUXHVXMXSZVXNV
      WRUXSXTZUUAZVXOVXCGUVMUXKUYBUOMZNZVYSVXOUVMUSJZUXLUVMYAZUYCUVMYAZVXCWUROW
      USVXOLBUDYBVEZVXOUXLUVIJZUVMLUXLXDWUTVXOBUSJZUXHVWMWVCWVDVXOFVEZWUNWUHGUX
      JUXGBXNXOUXLBYCUVMLUXLYDYEZVXOUYCUVIJZUVMLUYCXDWVAVXOWVDUXSVWQWVGWVEWUOWU
      LGUYAUXRBXNXOUYCBYCUVMLUYCYDYEZGUVMUXKUYBUOUSYFXOVXOGUVMWUQVYRVXOVUQPZVYR
      VXSUXGUJZUXJIZVXSUXRUJZUYAIZUOMZWUQWVIVXSVYIJZVYRWVNOWVIVXPLVXSXDZWVOVUQB
      LUVNXDVXRWVPVXOUVNLBUUBWUPBLVXPUVNUUCUUDLVXPVXSUUEWUEUUFUUGZVBVXSVYOWVNVY
      IVYPVYJVXSOZVYLWVKVYNWVMUOWVRVYKWVJUXJVYJVXSUXGYGWAZWVRVYMWVLUYAVYJVXSUXR
      YGWAZYHVYPWRWVKWVMUOYBWSWCWVKUXKWVMUYBUOWVJUXIUXJWUDWVJUXIOWUGUVNUXGVXPYJ
      XAYKZWVLUXTUYAWUJWVLUXTOWUKUVNUXRVXPYJXAYKZYLXBVLYMVYCVXRVYTPDVYPVYDUVPVY
      POZVYBVYTVXRWWCVYAVYSVXCWWCGUVMVXTVYRVXSUVPVYPVNVOVPTVQVRVXOVBVYIVYLVYNUQ
      MZNZVYDJZVXRVXGGUVMVXSWWEIZNZOZVYHVXOWUAWUBWWFWUIWUMVBVYLVYNVXPUUJWQWUPVX
      OVXGGUVMUXKUYBUQMZNZWWHVXOWUSWUTWVAVXGWWKOWVBWVFWVHGUVMUXKUYBUQUSYFXOVXOG
      UVMWWJWWGWVIWWGWVKWVMUQMZWWJWVIWVOWWGWWLOWVQVBVXSWWDWWLVYIWWEWVRVYLWVKVYN
      WVMUQWVSWVTYHWWEWRWVKWVMUQYBWSWCWVKUXKWVMUYBUQWWAWWBYLXBVLYMVYGVXRWWIPDWW
      EVYDUVPWWEOZVYFWWIVXRWWMVYAWWHVXGWWMGUVMVXTWWGVXSUVPWWEVNVOVPTVQVRVXKVYEV
      YHPCVXPRUVKVXPOZVXFVYEVXJVYHWWNVXEVYCDUWAVYDUVKVXPHVSZWWNUVLVXRVXDVYBUVKV
      XPBWDZWWNUVRVYAVXCWWNGUVMUVQVXTWWNUVOVXSUVPUVKVXPUVNVTWAVOZVPWBWEWWNVXIVY
      GDUWAVYDWWOWWNUVLVXRVXHVYFWWPWWNUVRVYAVXGWWQVPWBWEWBVQVRUUHUUIVWTVXAVXKCR
      VWTUYMVXFUYSVXJVWTUYLVXEDUWAVWTUYKVXDUVLVWTUYJVXCUVRVWTUWMUXLUWTUYCUYIVWN
      UXHUXMVWSUUKZVWOVWRUXSUYDUUTZYHYNTYOVWTUYRVXIDUWAVWTUYQVXHUVLVWTUYPVXGUVR
      VWTUWMUXLUWTUYCUYOWWRWWSYHYNTYOWBYOUULUYMUYSCRUUMWCUUNUUOUUPUUQUURUUSUVAZ
      UVBVWIUYNUYTWWTUVCUWIUWOOZUWKUWQCDRUWAWXAUWJUWPUVLUWIUWOUVRYPTYQUWIUXBOZU
      WKUXDCDRUWAWXBUWJUXCUVLUWIUXBUVRYPTYQUAUBYSZUWLUVLUWMUVROZPZDUWAQZCRQUXQW
      XCUWKWXECDRUWAWXCUWJWXDUVLUWIUWMUVRYPTYQWXFUXPCUERCUEYSZWXFUXHUWMGUVMUXIU
      VPIZNZOZPZDUXOQUXPWXGWXEWXKDUWAUXOUVKUXGHVSWXGUVLUXHWXDWXJUVKUXGBWDWXGUVR
      WXIUWMWXGGUVMUVQWXHWXGUVOUXIUVPUVKUXGUVNVTWAVOVPWBWEWXKUXNDUFUXODUFYSZWXJ
      UXMUXHWXLWXIUXLUWMWXLGUVMWXHUXKUXIUVPUXJVNVOVPTYRYTYRYTUAUCYSZUWLUVLUWTUV
      ROZPZDUWAQZCRQUYHWXMUWKWXOCDRUWAWXMUWJWXNUVLUWIUWTUVRYPTYQWXPUYGCUGRCUGYS
      ZWXPUXSUWTGUVMUXTUVPIZNZOZPZDUYFQUYGWXQWXOWYADUWAUYFUVKUXRHVSWXQUVLUXSWXN
      WXTUVKUXRBWDWXQUVRWXSUWTWXQGUVMUVQWXRWXQUVOUXTUVPUVKUXRUVNVTWAVOVPWBWEWYA
      UYEDUHUYFDUHYSZWXTUYDUXSWYBWXSUYCUWTWYBGUVMWXRUYBUXTUVPUYAVNVOVPTYRYTYRYT
      UWIUYJOZUWKUYLCDRUWAWYCUWJUYKUVLUWIUYJUVRYPTYQUWIUYPOZUWKUYRCDRUWAWYDUWJU
      YQUVLUWIUYPUVRYPTYQUWIAOZUWKUVTCDRUWAWYEUWJUVSUVLUWIAUVRYPTYQUVDVCUVTUWHC
      DRUWAUVSUWGUVLUVRUWFAGEUVMUVQUWEGEYSUVOUWDUVPUVNUWCUVKYGWAWMUVEUVFUVGUVH
      $.
  $}

  ${
    $d A a b d $.  $d B a b c d $.
    $( Polynomials are finitary objects and can only reference a finite number
       of variables, even if the index set is infinite.  Thus, every polynomial
       can be expressed as a (uniquely minimal, although we do not prove that)
       polynomial on a finite number of variables, which is then extended by
       adding an arbitrary set of ignored variables.  (Contributed by Stefan
       O'Rear, 9-Oct-2014.) $)
    mzpcompact2 $p |- ( A e. ( mzPoly ` B ) -> E. a e. Fin E. b e. ( mzPoly ` a
        ) ( a C_ B /\ A = ( c e. ( ZZ ^m B ) |-> ( b ` ( c |` a ) ) ) ) ) $=
      ( vd cvv wcel cmzp cfv cv wss cz cmap co cmpt wceq wa wrex cfn cres fveq2
      elfvex eleq2d sseq2 oveq2 mpteq1d anbi12d 2rexbidv imbi12d mzpcompact2lem
      wi eqeq2d vex vtoclg mpcom ) BGHABIJZHZCKZBLZAEMBNOZEKUSUADKJZPZQZRZDUSIJ
      ZSCTSZABIUCAFKZIJZHZUSVHLZAEMVHNOZVBPZQZRZDVFSCTSZULURVGULFBGVHBQZVJURVPV
      GVQVIUQAVHBIUBUDVQVOVECDTVFVQVKUTVNVDVHBUSUEVQVMVCAVQEVLVAVBVHBMNUFUGUMUH
      UIUJAVHCDEFUNUKUOUP $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Miscellanea for Diophantine sets 1
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( ~ coeq0 but without explicitly introducing domain and range symbols.
     (Contributed by Stefan O'Rear, 16-Oct-2014.) $)
  coeq0i $p |- ( ( A : C --> D /\ B : E --> F /\ ( C i^i F ) = (/) ) ->
      ( A o. B ) = (/) ) $=
    ( wf cin c0 wceq w3a cdm crn wss frn 3ad2ant2 sslin syl fdm 3ad2ant1 ineq1d
    simp3 eqtrd sseqtrd ss0 coemptyd ) CDAGZEFBGZCFHZIJZKZABUKALZBMZHZINUNIJUKU
    NULFHZIUKUMFNZUNUONUHUGUPUJEFBOPUMFULQRUKUOUIIUKULCFUGUHULCJUJCDASTUAUGUHUJ
    UBUCUDUNUERUF $.

  $( Split a finite 1-based set of integers in the middle, allowing either end
     to be empty ( ` ( 1 ... 0 ) ` ).  (Contributed by Stefan O'Rear,
     8-Oct-2014.) $)
  fzsplit1nn0 $p |- ( ( A e. NN0 /\ B e. NN0 /\ A <_ B ) -> ( 1 ... B ) = ( ( 1
      ... A ) u. ( ( A + 1 ) ... B ) ) ) $=
    ( cn0 wcel cle wbr c1 cfz co caddc cun wceq cn cc0 wo wa cz adantr eqtrdi
    c0 wi elnn0 1zzd nn0z ad2antrl nnge1 simprr elfzd fzsplit uncom oveq1 0p1e1
    nnz syl oveq1d oveq2 fz10 uneq12d un0 eqtr2id jaoian ex sylbi 3impib ) ACDZ
    BCDZABEFZGBHIZGAHIZAGJIZBHIZKZLZVEAMDZANLZOZVFVGPZVMUAAUBVPVQVMVNVQVMVOVNVQ
    PZAVHDVMVRAGBVRUCVFBQDVNVGBUDUEVNAQDVQAUMRVNGAEFVQAUFRVNVFVGUGUHAGBUIUNVOVQ
    PZVLVKVIKZVHVIVKUJVSVTVHTKVHVSVKVHVITVSVJGBHVSVJNGJIZGVOVJWALVQANGJUKRULSUO
    VSVIGNHIZTVOVIWBLVQANGHUPRUQSURVHUSSUTVAVBVCVD $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Diophantine sets 1: definitions
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c Dioph $.
  $( Extend class notation to include the family of Diophantine sets. $)
  cdioph $a class Dioph $.

  ${
    $d n k p t u $.
    $( A Diophantine set is a set of positive integers which is a projection of
       the zero set of some polynomial.  This definition somewhat awkwardly
       mixes ` ZZ ` (via ` mzPoly ` ) and ` NN0 ` (to define the zero sets);
       the former could be avoided by considering coincidence sets of ` NN0 `
       polynomials at the cost of requiring two, and the second is driven by
       consistency with our mu-recursive functions and the requirements of the
       Davis-Putnam-Robinson-Matiyasevich proof.  Both are avoidable at a
       complexity cost.  In particular, it is a consequence of ~ 4sq that
       implicitly restricting variables to ` NN0 ` adds no expressive power
       over allowing them to range over ` ZZ ` .  While this definition
       stipulates a specific index set for the polynomials, there is actually
       flexibility here, see ~ eldioph2b .  (Contributed by Stefan O'Rear,
       5-Oct-2014.) $)
    df-dioph $a |- Dioph = ( n e. NN0 |-> ran ( k e. ( ZZ>= ` n ) , p e. (
        mzPoly ` ( 1 ... k ) ) |-> { t | E. u e. ( NN0 ^m ( 1 ... k ) ) ( t =
        ( u |` ( 1 ... n ) ) /\ ( p ` u ) = 0 ) } ) ) $.
  $}

  ${
    $d D n d k p $.  $d N n d k p t u $.
    $( Initial expression of Diophantine property of a set.  (Contributed by
       Stefan O'Rear, 5-Oct-2014.)  (Revised by Mario Carneiro,
       22-Sep-2015.) $)
    eldiophb $p |- ( D e. ( Dioph ` N ) <-> ( N e. NN0 /\ E. k e. ( ZZ>= ` N )
        E. p e. (
        mzPoly ` ( 1 ... k ) ) D = { t | E. u e. ( NN0 ^m ( 1 ... k ) ) ( t =
        ( u |` ( 1 ... N ) ) /\ ( p ` u ) = 0 ) } ) ) $=
      ( vn vd cdioph cfv wcel cn0 cv c1 cfz co wceq cmap wrex cab cres cc0 cmzp
      cuz cdm cmpo crn df-dioph dmmptss elfvdm sselid fveq2 eqidd oveq2 reseq2d
      wa eqeq2d anbi1d rexbidv abbidv mpoeq123dv rneqd cpw ovex pwex eqid rnmpo
      wss wf elmapi fzss2 fssres syl2anr nn0ex elmap sylibr wb eleq1 syl5ibrcom
      adantr rexlimdva abssdv elpw2 rexlimdvw rexlimiv abssi ssexi fvmpt eleq2d
      eqsstri abrexex simpl reximi ss2abi elrnmpo bitrdi biadanii ) CEIJZKZELKZ
      CBMZAMZNEOPZUAZQZXBFMJUBQZUPZALNDMZOPZRPZSZBTZQFXIUCJZSDEUDJZSZWSIUELEGLD
      FGMZUDJZXMXAXBNXPOPZUAZQZXFUPZAXJSZBTZUFZUGZIABDGFUHZUICEIUJUKWTWSCDFXNXM
      XLUFZUGZKXOWTWRYHCGEYEYHLIXPEQZYDYGYIDFXQXMYCXNXMXLXPEUDULYIXMUMYIYBXKBYI
      YAXGAXJYIXTXEXFYIXSXDXAYIXRXCXBXPENOUNUOUQURUSUTVAVBYFYHLXCRPZVCZYJLXCRVD
      ZVEYHHMZXLQZFXMSZDXNSZHTYKDFHXNXMXLYGYGVFZVGYPHYKYOYMYKKZDXNXHXNKZYNYRFXM
      YSYRYNXLYKKZYSXLYJVHYTYSXKBYJYSXGXAYJKZAXJYSXBXJKZUPZUUAXGXDYJKZUUCXCLXDV
      IZUUDUUBXILXBVIXCXIVHUUEYSXBLXIVJENXHVKXILXCXBVLVMLXCXDVNNEOVDVOVPXEUUAUU
      DVQXFXAXDYJVRVTVSWAWBXLYJYLWCVPYMXLYKVRVSWDWEWFWJWGWHWIDFXNXMXLCYGYQXLXEA
      XJSZBTABXJXDLXIRVDWKXKUUFBXGXEAXJXEXFWLWMWNWGWOWPWQ $.
  $}

  ${
    $d N k p t u $.  $d K k p t u $.  $d P k p t u $.
    $( Condition for a set to be Diophantine (unpacking existential
       quantifier).  (Contributed by Stefan O'Rear, 5-Oct-2014.) $)
    eldioph $p |- ( ( N e. NN0 /\ K e. ( ZZ>= ` N ) /\ P e. ( mzPoly ` ( 1 ...
        K ) ) ) ->
        { t | E. u e. ( NN0 ^m ( 1 ... K ) ) ( t = ( u |` ( 1 ... N ) ) /\ ( P
        ` u ) = 0 ) } e. ( Dioph ` N ) ) $=
      ( vp vk cn0 wcel cfv c1 cfz co cmzp cv wceq cc0 cmap wrex cab cuz cres wa
      cdioph simp1 simp2 simp3 eqidd fveq1 eqeq1d anbi2d rexbidv abbidv syl2anc
      w3a rspceeqv oveq2 fveq2d oveq2d rexeqdv eqeq2d rexeqbidv rspcev eldiophb
      sylanbrc ) EHIZDEUAJZIZCKDLMZNJZIZUOZVFBOAOZKELMUBPZVMCJZQPZUCZAHVIRMZSZB
      TZVNVMFOZJZQPZUCZAHKGOZLMZRMZSZBTZPZFWFNJZSZGVGSZVTEUDJIVFVHVKUEVLVHVTWDA
      VRSZBTZPZFVJSZWMVFVHVKUFVLVKVTVTPWQVFVHVKUGVLVTUHFCVJWOVTVTWACPZWNVSBWRWD
      VQAVRWRWCVPVNWRWBVOQVMWACUIUJUKULUMUPUNWLWQGDVGWEDPZWJWPFWKVJWSWFVINWEDKL
      UQZURWSWIWOVTWSWHWNBWSWDAWGVRWSWFVIHRWTUSUTUMVAVBVCUNABVTGEFVDVE $.
  $}

  ${
    $d S a b c d $.  $d T a b c d $.  $d M a b c d $.  $d O a b c d $.
    $d P b c d $.
    $( Renaming and adding unused witness variables does not change the
       Diophantine set coded by a polynomial.  (Contributed by Stefan O'Rear,
       7-Oct-2014.) $)
    diophrw $p |- ( ( S e. _V /\ M : T -1-1-> S /\ ( M |` O ) = ( _I |` O ) )
        -> { a | E. b e. ( NN0 ^m S ) ( a = ( b |` O ) /\ ( ( d e. ( ZZ ^m S )
        |-> ( P ` ( d o. M ) ) ) ` b ) = 0 ) } = { a | E. c e. ( NN0 ^m T ) ( a
        = ( c |` O ) /\ ( P ` c ) = 0 ) } ) $=
      ( cvv wcel cres wceq cz ccom cc0 cn0 wf eqtrid c0 wf1 cid w3a cv cmap cfv
      co cmpt wa simpr wb nn0ex simp1 adantr elmapg sylancr mpbid simp2 f1f syl
      ad2antrr syl2anc f1dmex mpbird simprl resco simpll3 coeq2d coires1 eqtrdi
      fco eqtr4d wss simpll1 oveq2 sseq12d zex nn0ssz mapss mp2an vtoclg simplr
      wrex sseldd coeq1 fveq2d eqid simprr eqtr3d reseq1 eqeq2d fveqeq2 anbi12d
      fvex fvmpt rspcev syl12anc rexlimdva2 ccnv crn cdif csn cxp cun cin f1cnv
      wf1o f1of 3syl c0ex fconst a1i disjdif fun syl21anc frn undif sylib snssi
      0nn0 ax-mp ssequn2 mpbi feq23d resundir cima wfun df-f1 simprbi funcnvres
      simpl2 simpl3 cnveqd df-ima rneqd cdm eqtr2di uneq12d un0 eqtrd dmres wne
      rnresi reseq2d 3eqtr3d cnvresid eqtr3di snnz dmxp ineq2i inss1 resss rnss
      mp1i eqsstrd sstrid inssdif0 wrel relres reldm0 sylibr sylancl 0z coundir
      coass f1cocnv1 ineq1i incom 3eqtri coeq0 mpbir fcoi1 3eqtrd impbid abbidv
      fss ) BJKZCBDUAZDELZUBELZMZUCZFUDZGUDZELZMZUWDINBUEUGZIUDZDOZAUFZUHZUFZPM
      ZUIZGQBUEUGZWCZUWCHUDZELZMZUWQAUFZPMZUIZHQCUEUGZWCZFUWBUWPUXDUWBUWNUXDGUW
      OUWBUWDUWOKZUIZUWNUIZUWDDOZUXCKZUWCUXHELZMZUXHAUFZPMZUXDUXGUXICQUXHRZUXGB
      QUWDRZCBDRZUXNUXFUXOUWNUXFUXEUXOUWBUXEUJUXFQJKZUVQUXEUXOUKULUWBUVQUXEUVQU
      VRUWAUMZUNQBUWDJJUOUPUQUNUWBUXPUXEUWNUWBUVRUXPUVQUVRUWAURZCBDUSZUTVACBQUW
      DDVKVBUXGUXQCJKZUXIUXNUKULUWBUYAUXEUWNUWBUVRUVQUYAUXSUXRCBJDVCVBZVAQCUXHJ
      JUOUPVDUXGUWCUWEUXJUXFUWFUWMVEUXGUXJUWDUVSOZUWEUWDDEVFUXGUYCUWDUVTOUWEUXG
      UVSUVTUWDUVQUVRUWAUXEUWNVGVHUWDEVIVJSVLUXGUWLUXLPUXGUWDUWGKUWLUXLMUXGUWOU
      WGUWDUXGUVQUWOUWGVMZUVQUVRUWAUXEUWNVNQUWCUEUGZNUWCUEUGZVMZUYDFBJUWCBMUYEU
      WOUYFUWGUWCBQUEVOUWCBNUEVOVPNJKZQNVMZUYGVQVRQNUWCJVSVTWAUTUWBUXEUWNWBWDIU
      WDUWJUXLUWGUWKUWHUWDMUWIUXHAUWHUWDDWEWFUWKWGZUXHAWNWOUTUXFUWFUWMWHWIUXBUX
      KUXMUIHUXHUXCUWQUXHMZUWSUXKUXAUXMUYKUWRUXJUWCUWQUXHEWJWKUWQUXHPAWLWMWPWQW
      RUWBUXBUWPHUXCUWBUWQUXCKZUIZUXBUIZUWQDWSZOZBDWTZXAZPXBZXCZXDZUWOKZUWCVUAE
      LZMZVUAUWKUFZPMZUWPUYNVUBBQVUARZUYNUYQUYRXDZQUYSXDZVUARZVUGUYNUYQQUYPRZUY
      RUYSUYTRZUYQUYRXEZTMZVUJUYNCQUWQRZUYQCUYORZVUKUYMVUOUXBUYMUYLVUOUWBUYLUJU
      YMUXQUYAUYLVUOUKULUWBUYAUYLUYBUNQCUWQJJUOUPUQZUNZUYNUVRUYQCUYOXGVUPUWBUVR
      UYLUXBUXSVAZCBDXFUYQCUYOXHXIZUYQCQUWQUYOVKVBVULUYNUYRPXJXKXLZVUNUYNUYQBXM
      ZXLZUYQUYRQUYSUYPUYTXNXOUYNVUHVUIBQVUAUYNUYQBVMZVUHBMUWBVVDUYLUXBUWBUVRUX
      PVVDUXSUXTCBDXPXIVAUYQBXQXRZVUIQMZUYNUYSQVMZVVFPQKVVGXTPQXSYAUYSQYBYCXLYD
      UQUWBVUBVUGUKZUYLUXBUWBUXQUVQVVHULUXRQBVUAJJUOUPVAVDUYNUWCUWRVUCUYMUWSUXA
      VEUYMUWRVUCMUXBUYMVUCUWRTXDZUWRUYMVUCUYPELZUYTELZXDVVIUYPUYTEYEUYMVVJUWRV
      VKTUYMVVJUWQUYOELZOZUWRUWQUYOEVFUYMVVMUWQUVTOUWRUYMVVLUVTUWQUYMUVTWSZVVLU
      VTUYMUVSWSZUYODEYFZLZVVNVVLUYMUVRUYOYGZVVOVVQMUVQUVRUWAUYLYKUVRUXPVVRCBDY
      HYIEDYJXIUYMUVSUVTUVQUVRUWAUYLYLZYMUYMVVPEUYOUYMVVPUVSWTZEDEYNUYMVVTUVTWT
      ZEUYMUVSUVTVVSYOZEUUCZVJSUUDUUEEUUFUUGVHUWQEVIVJSUYMVVKYPZTMZVVKTMZUYMVWD
      EUYTYPZXEZTUYTEUUAUYMVWHEUYRXEZTVWGUYREUYSTUUBVWGUYRMPXJUUHUYRUYSUUIYAZUU
      JUYMEBXEZUYQVMVWITMUYMVWKEUYQEBUUKUYMEVVTUYQUYMVVTVWAEVWBVWCYQUVSDVMVVTUY
      QVMUYMDEUULUVSDUUMUUNUUOUUPEBUYQUUQXRSSVVKUURVWFVWEUKUYTEUUSVVKUUTYAUVAYR
      SUWRYSYQUNYTUYNVUEVUADOZAUFZUWTPUYNVUAUWGKZVUEVWMMUYNVWNBNVUARZUYNVUHNUYS
      XDZVUARZVWOUYNUYQNUYPRZVULVUNVWQUYNCNUWQRZVUPVWRUYMVWSUXBUYMVUOUYIVWSVUQV
      RCQNUWQUVPUVBUNVUTUYQCNUWQUYOVKVBVVAVVCUYQUYRNUYSUYPUYTXNXOUYNVUHVWPBNVUA
      VVEVWPNMZUYNUYSNVMZVWTPNKVXAUVCPNXSYAUYSNYBYCXLYDUQUWBVWNVWOUKZUYLUXBUWBU
      YHUVQVXBVQUXRNBVUAJJUOUPVAVDIVUAUWJVWMUWGUWKUWHVUAMUWIVWLAUWHVUADWEWFUYJV
      WLAWNWOUTUYNVWLUWQAUYNVWLUYPDOZUYTDOZXDZUWQUYPUYTDUVDUYNVXEUWQUBCLZOZTXDZ
      UWQUYNVXCVXGVXDTUYNVXCUWQUYODOZOZVXGUWQUYODUVEUYNUVRVXJVXGMVUSUVRVXIVXFUW
      QCBDUVFVHUTSVXDTMZUYNVXKVWGUYQXEZTMVXLUYRUYQXEVUMTVWGUYRUYQVWJUVGUYRUYQUV
      HVVBUVIUYTDUVJUVKXLYRUYNVXHVXGUWQVXGYSUYNVUOVXGUWQMVURCQUWQUVLUTSYTSWFUYM
      UWSUXAWHUVMUWNVUDVUFUIGVUAUWOUWDVUAMZUWFVUDUWMVUFVXMUWEVUCUWCUWDVUAEWJWKU
      WDVUAPUWKWLWMWPWQWRUVNUVO $.
  $}

  ${
    $d A a d e $.  $d N a d e $.
    $( Lemma for ~ eldioph2 .  Construct necessary renaming function for one
       direction.  (Contributed by Stefan O'Rear, 8-Oct-2014.) $)
    eldioph2lem1 $p |- ( ( N e. NN0 /\ A e. Fin /\ ( 1 ... N ) C_ A ) -> E. d
        e. ( ZZ>= ` N ) E. e e. _V ( e : ( 1 ... d ) -1-1-onto-> A /\ ( e |` (
        1 ... N ) ) = ( _I |` ( 1 ... N ) ) ) ) $=
      ( va wcel cfn c1 cfz co caddc chash cfv wf1o cres wceq cvv wbr cun c0 cn0
      wss w3a cdif cv cid wa wrex cuz cen wex cc cr nn0re 3ad2ant1 recnd ax-1cn
      addcom sylancl cin diffi 3ad2ant2 fzfid disjdifr a1i hashun syl3anc uncom
      simp3 undif sylib eqtrid fveq2d hashfz1 oveq2d 3eqtr3d oveq12d hashcl syl
      cz 1zzd nn0zd nn0z fzen ensymd wb fzfi hashen mp2an sylibr 3eqtrd sylancr
      mpbid cle simpl1 simpl2 nn0addge2 syl2anc breqtrrd adantr eluz2 syl3anbrc
      bren vex ovex resiexg ax-mp unex simpr f1oi incom clt nn0red ltp1d fzdisj
      f1oun syl22anc fzsplit1nn0 eqtr4id simpl3 resundir cdm dmres f1odm adantl
      f1oeq23 ineq2d eqtrd wrel relres reldm0 residm uneq12d eqtri eqtrdi oveq2
      un0 f1oeq2d anbi1d f1oeq1 reseq1 anbi12d rspc2ev syl112anc exlimddv
      eqeq1d ) CUAFZAGFZHCIJZAUBZUCZCHKJZALMZIJZAUUIUDZEUEZNZHDUEZIJZABUEZNZUUT
      UUIOZUFUUIOZPZUGZBQUHDCUIMZUHZEUUKUUNUUOUJRZUUQEUKUUKUUNLMZUUOLMZPZUVHUUK
      UVIHCKJZUVJCKJZIJZLMZHUVJIJZLMZUVJUUKUUNUVNLUUKUULUVLUUMUVMIUUKCULFHULFUU
      LUVLPUUKCUUGUUHCUMFZUUJCUNUOZUPUQCHURUSUUKUUOUUISZLMZUVJUUILMZKJZUUMUVMUU
      KUUOGFZUUIGFUUOUUIUTTPZUWAUWCPUUHUUGUWDUUJAUUIVAVBZUUKHCVCUWEUUKUUIAVDZVE
      UUOUUIVFVGUUKUVTALUUKUVTUUIUUOSZAUUOUUIVHZUUKUUJUWHAPZUUGUUHUUJVIUUIAVJZV
      KVLVMUUKUWBCUVJKUUGUUHUWBCPUUJCVNUOVOVPZVQVMUUKUVNUVPUJRZUVOUVQPZUUKUVPUV
      NUUKHVTFUVJVTFCVTFZUVPUVNUJRUUKWAUUKUVJUUKUWDUVJUAFZUWFUUOVRVSZWBUUGUUHUW
      OUUJCWCUOCHUVJWDVGWEUVNGFUVPGFUWNUWMWFUVLUVMWGHUVJWGUVNUVPWHWIWJUUKUWPUVQ
      UVJPUWQUVJVNVSWKUUKUUNGFUWDUVKUVHWFUULUUMWGUWFUUNUUOWHWLWMUUNUUOEXCVKUUKU
      UQUGZUUMUVFFZUUPUVCSZQFZHUUMIJZAUWTNZUWTUUIOZUVCPZUVGUWRUWOUUMVTFCUUMWNRZ
      UWSUWRCUUGUUHUUJUUQWOZWBUWRUUMUWRUUHUUMUAFZUUGUUHUUJUUQWPAVRVSZWBUUKUXFUU
      QUUKCUVMUUMWNUUKUVRUWPCUVMWNRUVSUWQCUVJWQWRUWLWSWTZCUUMXAXBUXAUWRUUPUVCEX
      DUUIQFUVCQFHCIXEUUIQXFXGXHVEUWRUUNUUISZUVTUWTNZUXCUWRUUQUUIUUIUVCNZUUNUUI
      UTZTPUWEUXLUUKUUQXIUXMUWRUUIXJVEUWRUXNUUIUUNUTZTUUNUUIXKUWRCUULXLRUXOTPUW
      RCUWRCUXGXMXNHCUULUUMXOVSZVLUWEUWRUWGVEUUNUUOUUIUUIUUPUVCXPXQUWRUXKUXBPUV
      TAPUXLUXCWFUWRUXKUUIUUNSZUXBUUNUUIVHUWRUUGUXHUXFUXBUXQPUXGUXIUXJCUUMXRVGX
      SUWRUVTUWHAUWIUWRUUJUWJUUGUUHUUJUUQXTUWKVKVLUXKUXBUVTAUWTYFWRWMUWRUXDUUPU
      UIOZUVCUUIOZSZUVCUUPUVCUUIYAUWRUXTTUVCSZUVCUWRUXRTUXSUVCUWRUXRYBZTPZUXRTP
      ZUWRUYBUUIUUPYBZUTZTUUPUUIYCUWRUYFUXOTUWRUYEUUNUUIUUQUYEUUNPUUKUUNUUOUUPY
      DYEYGUXPYHVLUXRYIUYDUYCWFUUPUUIYJUXRYKXGWJUXSUVCPUWRUFUUIYLVEYMUYAUVCTSUV
      CTUVCVHUVCYQYNYOVLUVEUXCUXEUGUXBAUUTNZUVDUGDBUUMUWTUVFQUURUUMPZUVAUYGUVDU
      YHUUSUXBAUUTUURUUMHIYPYRYSUUTUWTPZUYGUXCUVDUXEUXBAUUTUWTYTUYIUVBUXDUVCUUT
      UWTUUIUUAUUFUUBUUCUUDUUE $.
  $}

  ${
    $d N a c $.  $d S a c $.  $d A a c $.
    $( Lemma for ~ eldioph2 .  Construct necessary renaming function for one
       direction.  (Contributed by Stefan O'Rear, 8-Oct-2014.) $)
    eldioph2lem2 $p |- ( ( ( N e. NN0 /\ -. S e. Fin ) /\ ( ( 1 ... N ) C_ S /\
        A e. ( ZZ>= ` N ) ) ) -> E. c ( c : ( 1 ... A ) -1-1-> S /\ ( c |` ( 1
        ... N ) ) = ( _I |` ( 1 ... N ) ) ) ) $=
      ( va wcel cfn wa c1 cfz wss wf1 cres wceq cun cin c0 adantl syl eqtrid wn
      cn0 co cuz cfv cdif cv cid simplr fzfi difinf sylancl diffi ax-mp isinffi
      wex crn wf1o f1f1orn f1oi a1i disjdifr f1f frnd ssrind sseqtrdi ss0 f1oun
      syl22anc f1of1 uncom simplrr fzss2 undif sylib f1eq2 difss2d simplrl f1ss
      wb mpbid unssd syl2anc resundir cdm dmres incom f1dm ineq1d eqtrdi relres
      wrel reldm0 sylibr residm uneq12d un0 eqtri vex ovex resiexg f1eq1 reseq1
      cvv unex eqeq1d anbi12d spcev exlimddv ) CUBFZBGFUAZHZICJUCZBKZACUDUEFZHZ
      HZIAJUCZXMUFZBXMUFZEUGZLZXRBDUGZLZYCXMMZUHXMMZNZHZDUPZEXQXTGFUAZXSGFZYBEU
      PXQXKXMGFYJXJXKXPUIICUJBXMUKULXRGFYKIAUJXRXMUMUNXTXSEUOULXQYBHZXRBYAYFOZL
      ZYMXMMZYFNZYIYLXRYAUQZXMOZYMLZYRBKYNYLXSXMOZYRYMLZYSYLYTYRYMURZUUAYLXSYQY
      AURZXMXMYFURZXSXMPZQNZYQXMPZQNZUUBYBUUCXQXSXTYAUSRUUDYLXMUTVAUUFYLXMXRVBZ
      VAYLUUGQKUUHYLUUGXTXMPQYLYQXTXMYBYQXTKXQYBXSXTYAXSXTYAVCVDZRVEXMBVBVFUUGV
      GSXSYQXMXMYAYFVHVIYTYRYMVJSYLYTXRNUUAYSVTYLYTXMXSOZXRXSXMVKYLXMXRKZUUKXRN
      YLXOUULXLXNXOYBVLCIAVMSXMXRVNVOTYTXRYRYMVPSWAYLYQXMBYBYQBKXQYBYQBXMUUJVQR
      XLXNXOYBVRWBXRYRBYMVSWCYLYOYAXMMZYFXMMZOZYFYAYFXMWDYLUUOQYFOZYFYLUUMQUUNY
      FYLUUMWEZQNZUUMQNZYLUUQXMYAWEZPZQYAXMWFYLUVAUUTXMPZQXMUUTWGYLUVBUUEQYLUUT
      XSXMYBUUTXSNXQXSXTYAWHRWIUUIWJTTUUMWLUUSUURVTYAXMWKUUMWMUNWNUUNYFNYLUHXMW
      OVAWPUUPYFQOYFQYFVKYFWQWRWJTYHYNYPHDYMYAYFEWSXMXDFYFXDFICJWTXMXDXAUNXEYCY
      MNZYDYNYGYPXRBYCYMXBUVCYEYOYFYCYMXMXCXFXGXHWCXI $.
  $}

  ${
    $d P a b c e t u g h $.  $d S a b c d e t u g h $.
    $d N a b c d e t u g h $.
    $( Construct a Diophantine set from a polynomial with witness variables
       drawn from any set whatsoever, via ~ mzpcompact2 .  (Contributed by
       Stefan O'Rear, 8-Oct-2014.)  (Revised by Stefan O'Rear, 5-Jun-2015.) $)
    eldioph2 $p |- ( ( N e. NN0 /\ ( S e. _V /\ ( 1 ... N ) C_ S ) /\ P e. (
        mzPoly ` S ) ) ->
        { t | E. u e. ( NN0 ^m S ) ( t = ( u |` ( 1 ... N ) ) /\ ( P ` u ) = 0
        ) } e. ( Dioph ` N ) ) $=
      ( ve wcel cvv c1 co wss wa cfv cv cres wceq wrex cfn cc0 ccom va vb vc vd
      vg vh cn0 cfz cmzp w3a cz cmap cmpt cab cdioph mzpcompact2 3ad2ant3 fveq1
      eqeq1d anbi2d rexbidv abbidv ad2antll wi cun wf1o cid cuz simplll simplrl
      fzfi unfi sylancl ssun2 a1i eldioph2lem1 syl3anc f1ococnv2 ad2antrl ssun1
      reseq1d resabs1 ax-mp eqtr2di eqtrdi adantr coeq2d coires1 eqcomi 3eqtr3g
      resco coass fveq2d wf ovexd simpr wf1 f1of1 simprr ad2antrr unssd syl2anc
      ccnv f1ss f1f syl coeq1 eqid fvex fvmpt eqtr4d mpteq2dva fveq1d ad3antrrr
      mapco2g diophrw eqtrd simp-5l simplrr f1ocnv mzprename eldioph eqeltrd ex
      f1of fssres rexlimdvva mpd exp31 3adant3 imp31 adantrr ) EUGGZDHGZIEUHJZD
      KZLZCDUIMGZUJZUANZDKZCFUKDULJZFNZYTOZUBNZMZUMZPZLZUBYTUIMZQUARQZBNZANZYOO
      PZUUMCMZSPZLZAUGDULJZQZBUNZEUOMZGZYRYMUUKYQCDUAUBFUPUQYSUUIUVBUAUBRUUJYSY
      TRGZUUEUUJGZLZLZUUIUVBUVFUUILUUTUUNUUMUUGMZSPZLZAUURQZBUNZUVAUUHUUTUVKPUV
      FUUAUUHUUSUVJBUUHUUQUVIAUURUUHUUPUVHUUNUUHUUOUVGSUUMCUUGURUSUTVAVBVCUVFUU
      AUVKUVAGZUUHYSUVEUUAUVLYMYQUVEUUAUVLVDVDYRYMYQLZUVEUUAUVLUVMUVELZUUALZIUC
      NZUHJZYTYOVEZUDNZVFZUVSYOOVGYOOPZLZUDHQUCEVHMZQZUVLUVOYMUVRRGZYOUVRKZUWDY
      MYQUVEUUAVIUVOUVCYORGUWEUVMUVCUVDUUAVJIEVKYTYOVLVMUWFUVOYOYTVNVOUVRUDEUCV
      PVQUVOUWBUVLUCUDUWCHUVOUVPUWCGZUVSHGZLZLZUWBUVLUWJUWBLZUVKUULUENZYOOPUWLU
      FUKUVQULJZUFNZUVSXCZYTOZTZUUEMZUMZMSPLUEUGUVQULJQBUNZUVAUWKUVKUUNUUMFUUBU
      UCUVSTZUWSMZUMZMZSPZLZAUURQZBUNZUWTUWKUVJUXGBUWKUVIUXFAUURUWKUVHUXEUUNUWK
      UVGUXDSUWKUUMUUGUXCUWKFUUBUUFUXBUWKUUCUUBGZLZUUFUXAUWPTZUUEMZUXBUXJUUDUXK
      UUEUXJUUCVGYTOZTUUCUVSUWPTZTZUUDUXKUXJUXMUXNUUCUWKUXMUXNPUXIUWKUXMUVSUWOT
      ZYTOZUXNUWKUXQVGUVROZYTOZUXMUWKUXPUXRYTUVTUXPUXRPUWJUWAUVQUVRUVSVRVSWAYTU
      VRKZUXSUXMPYTYOVTZVGYTUVRWBWCWDUVSUWOYTWKWEWFWGUUCYTWHUXKUXOUUCUVSUWPWLWI
      WJWMUXJUXAUWMGZUXBUXLPUXJUVQHGZUXIUVQDUVSWNZUYBUXJIUVPUHWOUWKUXIWPUWKUYDU
      XIUWKUVQDUVSWQZUYDUWKUVQUVRUVSWQZUVRDKZUYEUVTUYFUWJUWAUVQUVRUVSWRVSUVOUYG
      UWIUWBUVOYTYODUVNUUAWPUVMYPUVEUUAYMYNYPWSWTXAWTUVQUVRDUVSXDXBZUVQDUVSXEXF
      WFUUCUKDUVSUVQXOVQUFUXAUWRUXLUWMUWSUWNUXAPUWQUXKUUEUWNUXAUWPXGWMUWSXHUXKU
      UEXIXJXFXKXLXMUSUTVAVBUWKYNUYEUWAUXHUWTPUVNYNUUAUWIUWBYMYNYPUVEVJXNUYHUWJ
      UVTUWAWSUWSDUVQUVSYOBAUEFXPVQXQUWKYMUWGUWSUVQUIMGZUWTUVAGYMYQUVEUUAUWIUWB
      XRUVOUWGUWHUWBVJUWKUYCUVDYTUVQUWPWNZUYIUWKIUVPUHWOUVOUVDUWIUWBUVMUVCUVDUU
      AXSWTUVTUYJUWJUWAUVTUVRUVQUWOWNZUXTUYJUVTUVRUVQUWOVFUYKUVQUVRUVSXTUVRUVQU
      WOYEXFUYAUVRUVQYTUWOYFVMVSUFUWPUUEYTUVQYAVQUEBUWSUVPEYBVQYCYDYGYHYIYJYKYL
      YCYDYGYH $.
  $}

  ${
    $d A a b p $.  $d N a b c d e u t p $.  $d S a b c d e u t p $.
    $( While Diophantine sets were defined to have a finite number of witness
       variables consequtively following the observable variables, this is not
       necessary; they can equivalently be taken to use any witness set
       ` ( S \ ( 1 ... N ) ) ` .  For instance, in ~ diophin we use this to
       take the two input sets to have disjoint witness sets.  (Contributed by
       Stefan O'Rear, 8-Oct-2014.) $)
    eldioph2b $p |- ( ( ( N e. NN0 /\ S e. _V ) /\ ( -. S e. Fin /\ ( 1 ... N )
        C_ S ) ) -> ( A e. ( Dioph ` N ) <->
        E. p e. ( mzPoly ` S ) A = { t | E. u e. ( NN0 ^m S ) ( t = ( u |` ( 1
        ... N ) ) /\ ( p ` u ) = 0 ) } ) ) $=
      ( vd vb va vc ve wcel cvv wa co cfv cv cres wceq wrex cn0 cfn cfz wss cc0
      wn c1 cdioph cmap cab cmzp cuz eldiophb wf1 cid cz ccom wf simp-5r simprr
      ad2antrr simprl f1f syl mzprename syl3anc w3a diophrw eqcomd fveq1 eqeq1d
      cmpt anbi2d rexbidv rspceeqv syl2anc simplll simplrl simplrr eldioph2lem2
      abbidv wex syl22anc rexv sylibr r19.29a eqeq1 syl5ibrcom adantld biimtrid
      rexlimdvva simpllr eldioph2 syl121anc adantr eqeltrd rexlimdva2 impbid
      simpr ) EUALZDMLZNZDUBLUFZUGEUCOZDUDZNZNZCEUHPZLZCBQZAQZXDRSZXKFQZPZUESZN
      ZAUADUIOZTZBUJZSZFDUKPZTZXIWTCXJGQZXDRSYCHQZPUESNGUAUGIQZUCOZUIOTBUJZSZHY
      FUKPZTIEULPZTZNXGYBGBCIEHUMXGYKYBWTXGYHYBIHYJYIXGYEYJLZYDYILZNZNZYBYHYGXS
      SZFYATZYOYFDJQZUNZYRXDRUOXDRSZNZYQJMYOYRMLZNZUUANZKUPDUIOKQYRUQYDPVLZYALZ
      YGXLXKUUEPZUESZNZAXQTZBUJZSZYQUUDXAYMYFDYRURZUUFWTXAXFYNUUBUUAUSZYOYMUUBU
      UAXGYLYMUTVAUUDYSUUMUUCYSYTVBZYFDYRVCVDKYRYDYFDVEVFUUDXAYSYTUULUUNUUOUUCY
      SYTUTXAYSYTVGUUKYGYDDYFYRXDBAGKVHVIVFFUUEYAXSUUKYGXMUUESZXRUUJBUUPXPUUIAX
      QUUPXOUUHXLUUPXNUUGUEXKXMUUEVJVKVMVNWAVOVPYOUUAJWBZUUAJMTYOWTXCXEYLUUQWTX
      AXFYNVQXBXCXEYNVRXBXCXEYNVSXGYLYMVBYEDEJVTWCUUAJWDWEWFYHXTYPFYACYGXSWGVNW
      HWKWIWJXGXTXIFYAXGXMYALZNZXTNCXSXHUUSXTWSUUSXSXHLZXTUUSWTXAXEUURUUTWTXAXF
      UURVQWTXAXFUURWLXBXCXEUURVSXGUURWSABXMDEWMWNWOWPWQWR $.
  $}

  ${
    $d A a b c d $.  $d B a b c d $.
    $( Remove antecedent on ` B ` from Diophantine set constructors.
       (Contributed by Stefan O'Rear, 10-Oct-2014.) $)
    eldiophelnn0 $p |- ( A e. ( Dioph ` B ) -> B e. NN0 ) $=
      ( vc vd va vb cdioph cfv wcel cn0 cv c1 cfz co cres wceq cc0 wa cmap wrex
      cab cmzp cuz eldiophb simplbi ) ABGHIBJIACKDKZLBMNOPUFEKHQPRDJLFKMNZSNTCU
      APEUGUBHTFBUCHTDCAFBEUDUE $.
  $}

  ${
    $d A p t u $.  $d N p t u $.
    $( Define Diophantine sets in terms of polynomials with variables indexed
       by ` NN ` .  This avoids a quantifier over the number of witness
       variables and will be easier to use than ~ eldiophb in most cases.
       (Contributed by Stefan O'Rear, 10-Oct-2014.) $)
    eldioph3b $p |- ( A e. ( Dioph ` N ) <-> ( N e. NN0 /\
        E. p e. ( mzPoly ` NN ) A = { t | E. u e. ( NN0 ^m NN ) ( t = ( u |` (
        1 ... N ) ) /\ ( p ` u ) = 0 ) } ) ) $=
      ( cdioph cfv wcel cn0 cv c1 cfz co cres wceq cc0 wa cn cmap wrex cab cmzp
      eldiophelnn0 cvv wb nnex cfn wn wss cz uzinf ax-mp elfznn ssriv eldioph2b
      1z nnuz mpanr12 mpan2 biadanii ) CDFGHZDIHZCBJAJZKDLMZNOVCEJZGPOQAIRSMTBU
      AOERUBGTZCDUCVBRUDHZVAVFUEZUFVBVGQRUGHUHZVDRUIVHKUJHVIUPKRUQUKULEVDRVEDUM
      UNABCRDEUOURUSUT $.
  $}

  $( TODO: could maybe shorten a LOT of these with a canned substitution. $)
  ${
    $d N a b p t u $.  $d P a b p t u $.
    $( Inference version of ~ eldioph3b with quantifier expanded.  (Contributed
       by Stefan O'Rear, 10-Oct-2014.) $)
    eldioph3 $p |- ( ( N e. NN0 /\ P e. ( mzPoly ` NN ) ) -> { t | E. u e. (
        NN0 ^m NN ) ( t = ( u |` ( 1 ... N ) ) /\ ( P ` u ) = 0 ) } e. ( Dioph
        ` N ) ) $=
      ( va vb vp cn0 wcel cn cfv wa cv co cres wceq cc0 wrex cab rexbidv c1 cfz
      cmzp cdioph simpl simpr eqidd fveq1 eqeq1d anbi2d abbidv weq eqeq1 anbi1d
      cmap reseq1 eqeq2d fveqeq2 anbi12d cbvrexvw bitrdi cbvabv eqtrdi rspceeqv
      syl2anc eldioph3b sylanbrc ) DHIZCJUCKZIZLZVHBMZAMZUADUBNZOZPZVMCKQPZLZAH
      JUONZRZBSZEMZFMZVNOZPZWCGMZKZQPZLZFVSRZESZPGVIRZWADUDKIVHVJUEVKVJWAWAPWLV
      HVJUFVKWAUGGCVIWKWAWAWFCPZWKWEWCCKZQPZLZFVSRZESWAWMWJWQEWMWIWPFVSWMWHWOWE
      WMWGWNQWCWFCUHUIUJTUKWQVTEBEBULZWQVLWDPZWOLZFVSRVTWRWPWTFVSWRWEWSWOWBVLWD
      UMUNTWTVRFAVSFAULZWSVPWOVQXAWDVOVLWCVMVNUPUQWCVMQCURUSUTVAVBVCVDVEFEWADGV
      FVG $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Diophantine sets 2 miscellanea
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d N a $.  $d A a $.  $d B a $.
    $( Membership in a lower set of integers.  (Contributed by Stefan O'Rear,
       9-Oct-2014.) $)
    ellz1 $p |- ( B e. ZZ -> ( A e. ( ZZ \ ( ZZ>= ` ( B + 1 ) ) ) <-> ( A e. ZZ
        /\ A <_ B ) ) ) $=
      ( cz c1 caddc co cuz cfv cdif wcel wn wa cle wbr eldif clt notbid cr zre
      wb zltp1le lenlt syl2anr peano2z eluz sylan 3bitr4rd pm5.32da bitrid ) AC
      BDEFZGHZIJACJZAUKJZKZLBCJZULABMNZLACUKOUOULUNUPUOULLZBAPNZKZUJAMNZKUPUNUQ
      URUTBAUAQULARJBRJUPUSTUOASBSABUBUCUQUMUTUOUJCJULUMUTTBUDUJAUEUFQUGUHUI $.

    $( The union of a lower set of integers and an upper set of integers which
       abut or overlap is all of the integers.  (Contributed by Stefan O'Rear,
       9-Oct-2014.) $)
    lzunuz $p |- ( ( A e. ZZ /\ B e. ZZ /\ B <_ ( A + 1 ) ) -> ( ( ZZ \ ( ZZ>=
        ` ( A + 1 ) ) ) u. ( ZZ>= ` B ) ) = ZZ ) $=
      ( va cz wcel c1 caddc co cle wbr w3a cuz cfv cdif wo wa wb cr zred ex cun
      elun ellz1 3ad2ant1 eluz1 3ad2ant2 orbi12d clt zre adantl simpl1 lelttric
      syl2anc simpll2 simpll1 peano2zd ad2antlr simpll3 zltp1le 3ad2antl1 letrd
      cv biimpa orim2d mpd pm4.71d andi bitr2di bitrd bitrid eqrdv ) ADEZBDEZBA
      FGHZIJZKZCDVNLMNZBLMZUAZDCVBZVSEVTVQEZVTVREZOZVPVTDEZVTVQVRUBVPWCWDVTAIJZ
      PZWDBVTIJZPZOZWDVPWAWFWBWHVLVMWAWFQVOVTAUCUDVMVLWBWHQVOBVTUEUFUGVPWDWDWEW
      GOZPWIVPWDWJVPWDWJVPWDPZWEAVTUHJZOZWJWKVTREZAREWMWDWNVPVTUIZUJWKAVLVMVOWD
      UKSVTAULUMWKWLWGWEWKWLWGWKWLPZBVNVTWPBVLVMVOWDWLUNSWPVNWPAVLVMVOWDWLUOUPS
      WDWNVPWLWOUQVLVMVOWDWLURWKWLVNVTIJZVLVMWDWLWQQVOAVTUSUTVCVATVDVETVFWDWEWG
      VGVHVIVJVK $.

    $( Express a one-based finite range as the intersection of lower integers
       with ` NN ` .  (Contributed by Stefan O'Rear, 9-Oct-2014.) $)
    fz1eqin $p |- ( N e. NN0 -> ( 1 ... N ) = ( ( ZZ \ ( ZZ>= ` ( N + 1 ) ) )
        i^i NN ) ) $=
      ( va cn0 wcel c1 cfz co cz caddc cuz cfv cdif cn cin cv cle wbr wa w3a wb
      1z nn0z elfz1 sylancr 3anass ancom anbi2i anandi 3bitri bitrdi elin ellz1
      syl elnnz1 a1i anbi12d bitrid bitr4d eqrdv ) ACDZBEAFGZHAEIGJKLZMNZUTBOZV
      ADZVDHDZVDAPQZRZVFEVDPQZRZRZVDVCDZUTVEVFVIVGSZVKUTEHDAHDZVEVMTUAAUBZVDEAU
      CUDVMVFVIVGRZRVFVGVIRZRVKVFVIVGUEVPVQVFVIVGUFUGVFVGVIUHUIUJVLVDVBDZVDMDZR
      UTVKVDVBMUKUTVRVHVSVJUTVNVRVHTVOVDAULUMVSVJTUTVDUNUOUPUQURUS $.
  $}

  ${
    $d N a b $.
    $( Lower integers are countably infinite.  (Contributed by Stefan O'Rear,
       10-Oct-2014.) $)
    lzenom $p |- ( N e. ZZ -> ( ZZ \ ( ZZ>= ` ( N + 1 ) ) ) ~~ _om ) $=
      ( cz wcel c1 co cn cen wbr com cmin cvv cle wa cr zre ad2antrl cc anbi12d
      wceq zcn va vb caddc cuz cfv cdif cv zex difexg mp1i nnex ovex 2a1i simpl
      a1i peano2zd simprl zsubcld zred 1red simprr adantr ax-1cn pncan breqtrrd
      sylancl lesubd nncand eqcomd jca31 adantrr wb eleq1 breq2 eqeq2d ad2antll
      zcnd oveq2 mpbird recnd pncan2 eqbrtrd subled breq1 impbida anbi1d elnnz1
      ellz1 3bitr4d en2d nnenom entr ) ABCZBADUCEZUDUEZUFZFGHFIGHWPIGHWMUAUBWPF
      WNUAUGZJEZWNUBUGZJEZKKKKBKCWPKCWMUHBWOKUIUJFKCWMUKUOWRKCWMWQWPCZWNWQJULUM
      WTKCWMWSFCZWNWSJULUMWMWQBCZWQALHZMZWSWRSZMZWSBCZDWSLHZMZWQWTSZMZXAXFMXBXK
      MWMXGXLWMXGMXLWRBCZDWRLHZMZWQWNWRJEZSZMZWMXEXRXFWMXEMZXMXNXQXSWNWQXSAWMXE
      UNUPZWMXCXDUQURXSWQWNDXCWQNCWMXDWQOPXSWNXTUSXSUTXSWQAWNDJEZLWMXCXDVAXSAQC
      ZDQCZYAASWMYBXEATVBVCADVDVFVEVGXSXPWQXSWNWQXSWNXTVQXCWQQCWMXDWQTPVHVIVJVK
      XFXLXRVLWMXEXFXJXOXKXQXFXHXMXIXNWSWRBVMWSWRDLVNRXFWTXPWQWSWRWNJVRVORVPVSW
      MXLMXGWTBCZWTALHZMZWSWNWTJEZSZMZWMXJYIXKWMXJMZYDYEYHYJWNWSYJAWMXJUNUPZWMX
      HXIUQURYJWNAWSYJWNYKUSWMANCXJAOVBZXHWSNCWMXIWSOPYJWNAJEZDWSLYJYBYCYMDSYJA
      YLVTVCADWAVFWMXHXIVAWBWCYJYGWSYJWNWSYJWNYKVQXHWSQCWMXIWSTPVHVIVJVKXKXGYIV
      LWMXJXKXEYFXFYHXKXCYDXDYEWQWTBVMWQWTALWDRXKWRYGWSWQWTWNJVRVORVPVSWEWMXAXE
      XFWQAWHWFWMXBXJXKXBXJVLWMWSWGUOWFWIWJWKWPFIWLVF $.
  $}

  $( ~ fresaunres2 transposed to mappings.  (Contributed by Stefan O'Rear,
     9-Oct-2014.) $)
  elmapresaunres2 $p |- ( ( F e. ( C ^m A ) /\ G e. ( C ^m B ) /\
  ( F |` ( A i^i B ) ) = ( G |` ( A i^i B ) ) ) -> ( ( F u. G ) |` B ) = G ) $=
    ( cmap co wcel wf cin cres wceq cun elmapi id fresaunres2 syl3an ) DCAFGHAC
    DIECBFGHBCEIDABJZKERKLZSDEMBKELDCANECBNSOABCDEPQ $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Diophantine sets 2: union and intersection.  Monotone Boolean algebra
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d A a b c d e f g $.  $d B a b c d e f g $.  $d N a b c d e f g $.
    $( If two sets are Diophantine, so is their intersection.  (Contributed by
       Stefan O'Rear, 9-Oct-2014.)  (Revised by Stefan O'Rear, 6-May-2015.) $)
    diophin $p |- ( ( A e. ( Dioph ` N ) /\ B e. ( Dioph ` N ) ) -> ( A i^i B )
        e. ( Dioph ` N ) ) $=
      ( vc vg cfv wcel cn0 wa c1 co cres wceq cc0 cz cmap wrex cn c2 syl3anc vd
      va ve vb vf cdioph cin wi eldiophelnn0 cv cfz caddc cuz cdif cab cmzp cvv
      cfn wn wss wb id zex difexg mp1i com cen wbr nn0z lzenom enfi 3syl mtbiri
      ominf fz1eqin inss1 eqsstrdi eldioph2b syl22anc nnex 1z nnuz uzinf elfznn
      a1i ssriv anbi12d reeanv cexp cmpt inab simplrl simplrr reseq2d ad3antrrr
      cun eqcomd simprrl simprll eqtr4d elmapresaun uneq2i nnge1d lzunuz eqtrid
      3eqtr2d nn0p1nn oveq2d eleqtrd unidm uneq12d elmapresaunres2 fveq2d eqtrd
      simprrr jca32 reseq1 eqeq2d fveqeq2d syl2anc rexlimdvva elmapssres adantr
      cle sylancl nnssz simprl fveqeq2 anbi2d cr mzpf syl adantl ffvelcdmd zred
      wf oveq1d mzpresrename 2nn0 mzpexpmpt eqtr3id eqtr4di uncom reseq1i incom
      resundir simprlr rspcev ex simpr difss resabs1d resabs1 anbi1d rexlimdva2
      rspc2ev impbid nn0ssz mapss mp2an sseli sumsqeq0 oveq12d eqid ovex eqeq1d
      jca fvmpt bitr4d rexbidva bitrd bitr3id abbidv simpl fzssuz pm3.2i simprr
      uzssz sstri mzpaddmpt eldioph2 eqeltrd ineq12 eleq1d syl5ibrcom biimtrrid
      sylbid anabsi5 ) ACUFFZGZBUWIGZABUGZUWIGZUWJCHGZUWJUWKIZUWMUHACUIUWNUWOAD
      UJZUAUJZJCUKKZLZMZUWQUBUJZFZNMZIZUAHOCJULKZUMFZUNZPKZQZDUOZMZUBUXGUPFZQZB
      UWPUCUJZUWRLZMZUXNUDUJZFZNMZIZUCHRPKZQZDUOZMZUDRUPFZQZIZUWMUWNUWJUXMUWKUY
      FUWNUWNUXGUQGZUXGURGZUSUWRUXGUTZUWJUXMVAUWNVBZOUQGZUYHUWNVCOUXFUQVDVEUWNU
      YIVFURGZVNUWNCOGZUXGVFVGVHUYIUYMVACVIZCVJUXGVFVKVLVMUWNUWRUXGRUGZUXGCVOZU
      XGRVPVQZUADAUXGCUBVRVSUWNUWNRUQGZRURGUSZUWRRUTZUWKUYFVAUYKUYSUWNVTWEJOGZU
      YTUWNWAJRWBWCVEVUAUWNUBUWRRUXACWDWFZWEUCDBRCUDVRVSWGUYGUXKUYDIZUDUYEQUBUX
      LQUWNUWMUXKUYDUBUDUXLUYEWHUWNVUDUWMUBUDUXLUYEUWNUXAUXLGZUXQUYEGZIZIZUWMVU
      DUXJUYCUGZUWIGVUHVUIUWPUEUJZUWRLZMZVUJEOOPKZEUJZUXGLZUXAFZSWIKZVUNRLZUXQF
      ZSWIKZULKZWJZFZNMZIZUEHOPKZQZDUOZUWIVUHVUIUXIUYBIZDUOVVHUXIUYBDWKVUHVVIVV
      GDVVIUXDUXTIZUCUYAQUAUXHQZVUHVVGUXDUXTUAUCUXHUYAWHVUHVVKVULVUJUXGLZUXAFZN
      MZVUJRLZUXQFZNMZIZIZUEVVFQZVVGVUHVVKVVTVUHVVJVVTUAUCUXHUYAVUHUWQUXHGZUXNU
      YAGZIZIZVVJVVTVWDVVJIZUWQUXNWPZVVFGUWPVWFUWRLZMZVWFUXGLZUXAFZNMZVWFRLZUXQ
      FZNMZIZIZVVTVWEVWFHUXGRWPZPKZVVFVWEVWAVWBUWQUYPLZUXNUYPLZMZVWFVWRGVUHVWAV
      WBVVJWLZVUHVWAVWBVVJWMZVWEVWSUWSVWTUWNVWSUWSMVUGVWCVVJUWNUYPUWRUWQUWNUWRU
      YPUYQWQZWNWOVWEVWTUXOUWPUWSUWNVWTUXOMVUGVWCVVJUWNUYPUWRUXNVXDWNWOVWDUXDUX
      PUXSWRZVWDUWTUXCUXTWSZXFWTZUXGRHUWQUXNXATUWNVWRVVFMVUGVWCVVJUWNVWQOHPUWNV
      WQUXGJUMFZWPZORVXHUXGWBXBUWNUYNVUBJUXEYDVHVXIOMUYOVUBUWNWAWEUWNUXECXGXCCJ
      XDTXEXHWOXIVWEVWHVWKVWNVWEUWPUWSUXOWPZVWGVWEUWPUWPUWPWPVXJUWPXJVWEUWPUWSU
      WPUXOVXFVXEXKUUAUWQUXNUWRUUFUUBVWEVWJUXBNVWEVWIUWQUXAVWEVWIUXNUWQWPZUXGLZ
      UWQVWFVXKUXGUWQUXNUUCUUDVWEVWBVWAUXNRUXGUGZLZUWQVXMLZMVXLUWQMVXCVXBVWEVXN
      UXOVXOUWNVXNUXOMVUGVWCVVJUWNVXMUWRUXNUWNVXMUYPUWRRUXGUUEVXDXEZWNWOVWEVXOU
      WSUWPUXOUWNVXOUWSMVUGVWCVVJUWNVXMUWRUWQVXPWNWOVXFVXEXFWTRUXGHUXNUWQXLTXEX
      MVWDUWTUXCUXTUUGXNVWEVWMUXRNVWEVWLUXNUXQVWEVWAVWBVXAVWLUXNMVXBVXCVXGUXGRH
      UWQUXNXLTXMVWDUXDUXPUXSXOXNXPVVSVWPUEVWFVVFVUJVWFMZVULVWHVVRVWOVXQVUKVWGU
      WPVUJVWFUWRXQXRVXQVVNVWKVVQVWNVXQVVLVWINUXAVUJVWFUXGXQXSVXQVVOVWLNUXQVUJV
      WFRXQXSWGWGUUHXTUUIYAVUHVVSVVKUEVVFVUHVUJVVFGZIZVVSIZVVLUXHGZVVOUYAGZUWPV
      VLUWRLZMZVVNIZUWPVVOUWRLZMZVVQIZIZVVKVXSVYAVVSVXSVXRUXGOUTZVYAVUHVXRUUJZO
      UXFUUKZVUJHOUXGYBYEYCVXSVYBVVSVXSVXRROUTZVYBVYKYFVUJHORYBYEYCVXTVYEVYGVVQ
      VXTVYDVVNVXTUWPVUKVYCVXSVULVVRYGZVXTVUJUWRUXGUWNUYJVUGVXRVVSUYRWOUULWTVXS
      VULVVNVVQWRUVGVXTUWPVUKVYFVYNVUAVYFVUKMVXTVUCVUJUWRRUUMVEWTVXSVULVVNVVQXO
      XPVVJVYIVYEUXTIUAUCVVLVVOUXHUYAUWQVVLMZUXDVYEUXTVYOUWTVYDUXCVVNVYOUWSVYCU
      WPUWQVVLUWRXQXRUWQVVLNUXAYHWGUUNUXNVVOMZUXTVYHVYEVYPUXPVYGUXSVVQVYPUXOVYF
      UWPUXNVVOUWRXQXRUXNVVONUXQYHWGYIUUPTUUOUUQVUHVVSVVEUEVVFVXSVVRVVDVULVXSVV
      RVVMSWIKZVVPSWIKZULKZNMZVVDVXSVVMYJGVVPYJGVVRVYTVAVXSVVMVXSOUXGPKZOVVLUXA
      VXSVUEWUAOUXAYPUWNVUEVUFVXRWLUXAUXGYKYLVXRVVLWUAGZVUHVXRVUJVUMGZVYJWUBVVF
      VUMVUJUYLHOUTVVFVUMUTVCUURHOOUQUUSUUTUVAZVYLVUJOOUXGYBYEYMYNYOVXSVVPVXSOR
      PKZOVVOUXQVXSVUFWUEOUXQYPUWNVUEVUFVXRWMUXQRYKYLVXRVVOWUEGZVUHVXRWUCVYMWUF
      WUDYFVUJOORYBYEYMYNYOVVMVVPUVBXTVXSVVCVYSNVXSWUCVVCVYSMVXRWUCVUHWUDYMEVUJ
      VVAVYSVUMVVBVUNVUJMZVUQVYQVUTVYRULWUGVUPVVMSWIWUGVUOVVLUXAVUNVUJUXGXQXMYQ
      WUGVUSVVPSWIWUGVURVVOUXQVUNVUJRXQXMYQUVCVVBUVDVYQVYRULUVEUVHYLUVFUVIYIUVJ
      UVKUVLUVMXEVUHUWNUYLUWROUTZIZVVBOUPFZGZVVHUWIGUWNVUGUVNWUIVUHUYLWUHVCUWRV
      XHOJCUVOJUVRUVSUVPWEVUHEVUMVUQWJWUJGZEVUMVUTWJWUJGZWUKVUHEVUMVUPWJWUJGZSH
      GZWULVUHUYLVYJVUEWUNUYLVUHVCWEZVYJVUHVYLWEUWNVUEVUFYGEUXAUXGOYRTYSEVUPSOY
      TYEVUHEVUMVUSWJWUJGZWUOWUMVUHUYLVYMVUFWUQWUPVYMVUHYFWEUWNVUEVUFUVQEUXQROY
      RTYSEVUSSOYTYEEVUQVUTOUVTXTUEDVVBOCUWATUWBVUDUWLVUIUWIAUXJBUYCUWCUWDUWEYA
      UWFUWGYLUWH $.
  $}

  ${
    $d A a b c d e $.  $d B a b c d e $.  $d N a b c d e $.

    $( If two sets are Diophantine, so is their union.  (Contributed by Stefan
       O'Rear, 9-Oct-2014.)  (Revised by Stefan O'Rear, 6-May-2015.) $)
    diophun $p |- ( ( A e. ( Dioph ` N ) /\ B e. ( Dioph ` N ) ) -> ( A u. B )
        e. ( Dioph ` N ) ) $=
      ( vb vd va vc ve cfv wcel cn0 wa cv co wceq cc0 cn wrex cz syl cdioph cun
      wi eldiophelnn0 c1 cfz cres cmap cab cmzp cvv cfn wn wb nnex jctr 1z nnuz
      wss uzinf ax-mp elfznn ssriv pm3.2i eldioph2b anbi12d sylancl reeanv cmul
      cmpt wo unab r19.43 andi zex nn0ssz mapss mp2an sseli adantl oveq12d eqid
      fveq2 ovex fvmpt eqeq1d simplrl mzpf ffvelcdmd zcnd simplrr bitr2d anbi2d
      wf mul0ord bitr3id rexbidva abbidv eqtrid simpl a1i simprl feqmptd simprr
      eqeltrrd mzpmulmpt syl2anc eldioph2 syl3anc eqeltrd syl5ibrcom rexlimdvva
      uneq12 eleq1d biimtrrid sylbid anabsi5 ) ACUAIZJZBXRJZABUBZXRJZXSCKJZXSXT
      LZYBUCACUDYCYDADMEMZUECUFNZUGOZYEFMZIZPOZLZEKQUHNZRZDUIZOZFQUJIZRZBYGYEGM
      ZIZPOZLZEYLRZDUIZOZGYPRZLZYBYCYCQUKJZLZQULJUMZYFQUSZLZYDUUFUNYCUUGUOUPUUI
      UUJUESJUUIUQUEQURUTVAFYFQYHCVBVCZVDUUHUUKLXSYQXTUUEEDAQCFVEEDBQCGVEVFVGUU
      FYOUUDLZGYPRFYPRYCYBYOUUDFGYPYPVHYCUUMYBFGYPYPYCYHYPJZYRYPJZLZLZYBUUMYNUU
      CUBZXRJUUQUURYGYEHSQUHNZHMZYHIZUUTYRIZVINZVJZIZPOZLZEYLRZDUIZXRUUQUURYMUU
      BVKZDUIUVIYMUUBDVLUUQUVJUVHDUVJYKUUAVKZEYLRUUQUVHYKUUAEYLVMUUQUVKUVGEYLUV
      KYGYJYTVKZLUUQYEYLJZLZUVGYGYJYTVNUVNUVLUVFYGUVNUVFYIYSVINZPOUVLUVNUVEUVOP
      UVNYEUUSJZUVEUVOOUVMUVPUUQYLUUSYESUKJKSUSYLUUSUSVOVPKSQUKVQVRVSVTZHYEUVCU
      VOUUSUVDUUTYEOUVAYIUVBYSVIUUTYEYHWCUUTYEYRWCWAUVDWBYIYSVIWDWETWFUVNYIYSUV
      NYIUVNUUSSYEYHUVNUUNUUSSYHWNZYCUUNUUOUVMWGYHQWHZTUVQWIWJUVNYSUVNUUSSYEYRU
      VNUUOUUSSYRWNZYCUUNUUOUVMWKYRQWHZTUVQWIWJWOWLWMWPWQWPWRWSUUQYCUUGUUJLZUVD
      YPJZUVIXRJYCUUPWTUWBUUQUUGUUJUOUULVDXAUUQHUUSUVAVJZYPJHUUSUVBVJZYPJUWCUUQ
      YHUWDYPUUQHUUSSYHUUQUUNUVRYCUUNUUOXBZUVSTXCUWFXEUUQYRUWEYPUUQHUUSSYRUUQUU
      OUVTYCUUNUUOXDZUWATXCUWGXEHUVAUVBQXFXGEDUVDQCXHXIXJUUMYAUURXRAYNBUUCXMXNX
      KXLXOXPTXQ $.
  $}

  ${
    $d A a b c d $.  $d B a b c d $.
    $( Diophantine sets are sets of tuples of nonnegative integers.
       (Contributed by Stefan O'Rear, 10-Oct-2014.)  (Revised by Stefan O'Rear,
       6-May-2015.) $)
    eldiophss $p |- ( A e. ( Dioph ` B ) -> A C_ ( NN0 ^m ( 1 ... B ) ) ) $=
      ( vb vc va vd cdioph cfv wcel cn0 cv c1 co wceq wa cn cmap wrex wss simpr
      cfz cres cc0 cab cmzp eldioph3b vex anbi1d rexbidv elab elfznn elmapssres
      eqeq1 ssriv ad2antlr eqeltrd ex adantrd rexlimdva biimtrid adantr eqsstrd
      mpan2 ssrdv r19.29an sylbi ) ABGHIBJIZACKZDKZLBUAMZUBZNZVIEKZHUCNZOZDJPQM
      ZRZCUDZNZEPUEHZROAJVJQMZSZDCABEUFVGVSWBEVTVGVMVTIOZVSOAVRWAWCVSTWCVRWASVS
      WCFVRWAFKZVRIWDVKNZVNOZDVPRZWCWDWAIZVQWGCWDFUGVHWDNZVOWFDVPWIVLWEVNVHWDVK
      UMUHUIUJWCWFWHDVPWCVIVPIZOZWEWHVNWKWEWHWKWEOWDVKWAWKWETWJVKWAIZWCWEWJVJPS
      WLEVJPVMBUKUNVIJPVJULVCUOUPUQURUSUTVDVAVBVEVF $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Diophantine sets 3: construction
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d N t u a b c d e $.  $d M a b c d e $.  $d S t u a b c d e $.
    $( Projecting a Diophantine set by removing a coordinate results in a
       Diophantine set.  (Contributed by Stefan O'Rear, 10-Oct-2014.) $)
    diophrex $p |- ( ( N e. NN0 /\ M e. ( ZZ>= ` N ) /\ S e. ( Dioph ` M ) ) ->
        { t | E. u e. S t = ( u |` ( 1 ... N ) ) } e. ( Dioph ` N ) ) $=
      ( va vb vd ve vc cn0 wcel cfv cv cres wceq wrex cab wa wex cuz cdioph w3a
      c1 cfz co eqeq1 rexbidv reseq1 eqeq2d cbvrexvw bitrdi cbvabv cn cmap cmzp
      rexeq abbidv adantl anbi1d rexab r19.41v exbii rexcom4 anass resex anbi2d
      cc0 vex ceqsexv bitri ancom wss simpl2 fzss2 resabs1 3syl bitrid eldioph3
      bitr3id 3ad2antl1 eqeltrd eldioph3b simprbi 3ad2ant3 r19.29a eqeltrrid
      adantr ) EKLZDEUAMLZCDUBMLZUCZBNZANZUDEUEUFZOZPZACQZBRFNZGNZWOOZPZGCQZFRZ
      EUBMZXCWRFBWSWMPZXCWMXAPZGCQWRXFXBXGGCWSWMXAUGUHXGWQGACWTWNPXAWPWMWTWNWOU
      IUJUKULUMWLCHNZINZUDDUEUFZOZPZXIJNZMVHPZSZIKUNUOUFZQZHRZPZXDXELJUNUPMZWLX
      MXTLZSZXSSXDXBGXRQZFRZXEXSXDYDPYBXSXCYCFXBGCXRUQURUSYBYDXELXSYBYDWSXIWOOZ
      PZXNSZIXPQZFRZXEYBYCYHFYCWTXKPZXNSZIXPQZXBSZGTZYBYHXQYLXBGHXHWTPZXOYKIXPY
      OXLYJXNXHWTXKUGUTUHVAYNYKXBSZIXPQZGTZYBYHYQYMGYKXBIXPVBVCYRYPGTZIXPQYBYHY
      PIGXPVDYBYSYGIXPYSXNWSXKWOOZPZSZYBYGYSYJXNXBSZSZGTUUBYPUUDGYJXNXBVEVCUUCU
      UBGXKXIXJIVIVFYJXBUUAXNYJXAYTWSWTXKWOUIUJVGVJVKUUBUUAXNSYBYGXNUUAVLYBUUAY
      FXNYBYTYEWSYBWJWOXJVMYTYEPWIWJWKYAVNEUDDVOXIWOXJVPVQUJUTVRVRUHVTVTVRURWIW
      JYAYIXELWKIFXMEVSWAWBWHWBWKWIXSJXTQZWJWKDKLUUEIHCDJWCWDWEWFWG $.
  $}

  ${
    $d N t a b $.  $d A a b $.  $d B a b $.

    $( This is the first of a number of theorems which allow sets to be proven
       Diophantine by syntactic induction, and models the correspondence
       between Diophantine sets and monotone existential first-order logic.
       This first theorem shows that the zero set of an implicit polynomial is
       Diophantine.  (Contributed by Stefan O'Rear, 10-Oct-2014.) $)
    eq0rabdioph $p |- ( ( N e. NN0 /\ ( t e. ( ZZ ^m ( 1 ... N ) ) |-> A ) e. (
        mzPoly ` ( 1 ... N ) ) ) -> { t e. ( NN0 ^m ( 1 ... N ) ) | A = 0 } e.
        ( Dioph ` N ) ) $=
      ( va vb cn0 wcel cz co cmap cfv wa cc0 wceq crab cv wrex cab nfv eqtrdi
      c1 cfz cmpt cmzp cres cdioph wb wral nfmpt1 nfel1 nfan cvv wss zex nn0ssz
      mapss mp2an sseli adantl wf mzpf mptfcl imp syl2an adantll fvmpt2 syl2anc
      eqid eqcomd eqeq1d ralrimi rabbi sylib nfcv nffvmpt1 nfeq1 fveqeq2 df-rab
      cbvrabw wfn elmapi ffn fnresdm 3syl eqeq2d equcom bitrdi anbi1d ceqsrexbv
      rexbiia bitr2i abbii cuz simpl nn0z uzid syl adantr simpr eldioph syl3anc
      ex eqeltrd ) CFGZAHUACUBIZJIZBUCZXEUDKZGZLZBMNZAFXEJIZOZDPZEPZXEUEZNZXOXG
      KMNZLZEXLQZDRZCUFKZXJXMXNXLGXNXGKZMNZLZDRZYAXJXMYDDXLOZYFXJXMAPZXGKZMNZAX
      LOZYGXJXKYJUGZAXLUHXMYKNXJYLAXLXDXIAXDASAXGXHAXFBUIUJUKXJYHXLGZYLXJYMLZBY
      IMYNYIBYNYHXFGZBHGZYIBNYMYOXJXLXFYHHULGFHUMXLXFUMUNUOFHXEULUPUQURZUSXIYMY
      PXDXIXFHXGUTZYOYPYMXGXEVAYQYRYOYPAXFBHVBVCVDVEAXFBHXGXGVHVFVGVIVJXBVKXKYJ
      AXLVLVMYJYDADXLAXLVNDXLVNYJDSAYCMAXFBXNVOVPYHXNMXGVQVSTYDDXLVRTYEXTDXTXOX
      NNZXRLZEXLQYEXSYTEXLXOXLGZXQYSXRUUAXQXNXONYSUUAXPXOXNUUAXEFXOUTXOXEVTXPXO
      NXOFXEWAXEFXOWBXEXOWCWDWEDEWFWGWHWJXRYDEXNXLXOXNMXGVQWIWKWLTXJXDCCWMKGZXI
      YAYBGXDXIWNXDUUBXIXDCHGUUBCWOCWPWQWRXDXIWSEDXGCCWTXAXC $.

    $( Diophantine set builder for equality of polynomial expressions.  Note
       that the two expressions need not be nonnegative; only variables are so
       constrained.  (Contributed by Stefan O'Rear, 10-Oct-2014.) $)
    eqrabdioph $p |- ( ( N e. NN0 /\ ( t e. ( ZZ ^m ( 1 ... N ) ) |-> A ) e. (
        mzPoly ` ( 1 ... N ) ) /\ ( t e. ( ZZ ^m ( 1 ... N ) ) |-> B ) e. (
        mzPoly ` ( 1 ... N ) ) ) -> { t e. ( NN0 ^m ( 1 ... N ) ) | A = B } e.
        ( Dioph ` N ) ) $=
      ( cn0 wcel cz co cmap cmpt cfv wceq crab wa nfmpt1 nfel1 wf mzpf cvv wss
      c1 cfz cmzp w3a cmin cc0 cdioph wb wral nfan cv ad2antrr zex nn0ssz mapss
      mp2an sseli adantl mptfcl sylc zcnd ad2antlr subeq0ad ralrimi rabbi sylib
      bicomd ex 3adant1 simp1 mzpsubmpt eq0rabdioph syl2anc eqeltrd ) DEFZAGUAD
      UBHZIHZBJZVPUCKZFZAVQCJZVSFZUDZBCLZAEVPIHZMZBCUEHZUFLZAWEMZDUGKZVTWBWFWIL
      ZVOVTWBNZWDWHUHZAWEUIWKWLWMAWEVTWBAAVRVSAVQBOPAWAVSAVQCOPUJWLAUKZWEFZWMWL
      WONZWHWDWPBCWPBWPVQGVRQZWNVQFZBGFVTWQWBWOVRVPRULWOWRWLWEVQWNGSFEGTWEVQTUM
      UNEGVPSUOUPUQURZAVQBGUSUTVAWPCWPVQGWAQZWRCGFWBWTVTWOWAVPRVBWSAVQCGUSUTVAV
      CVGVHVDWDWHAWEVEVFVIWCVOAVQWGJVSFZWIWJFVOVTWBVJVTWBXAVOABCVPVKVIAWGDVLVMV
      N $.

    $( The empty set is Diophantine.  (Contributed by Stefan O'Rear,
       10-Oct-2014.) $)
    0dioph $p |- ( A e. NN0 -> (/) e. ( Dioph ` A ) ) $=
      ( va cn0 wcel c0 c1 cc0 wceq cfz co cmap crab cdioph wn wral ax-1ne0 neii
      cfv rgenw cz rabeq0 mpbir cmpt cmzp ovex 1z mzpconstmpt mp2an eq0rabdioph
      cvv mpan2 eqeltrrid ) ACDZEFGHZBCFAIJZKJZLZAMRZUQEHUNNZBUPOUSBUPFGPQSUNBU
      PUAUBUMBTUOKJFUCUOUDRDZUQURDUOUJDFTDUTFAIUEUFBFUOUGUHBFAUIUKUL $.

    $( The "universal" set (as large as possible given ~ eldiophss ) is
       Diophantine.  (Contributed by Stefan O'Rear, 10-Oct-2014.) $)
    vdioph $p |- ( A e. NN0 -> ( NN0 ^m ( 1 ... A ) ) e. ( Dioph ` A ) ) $=
      ( va cn0 wcel c1 cfz cmap cc0 wceq crab cdioph cfv wral eqid rgenw rabid2
      co mpbir cz cmpt cmzp cvv 0z mzpconstmpt mp2an eq0rabdioph mpan2 eqeltrid
      ovex ) ACDZCEAFQZGQZHHIZBULJZAKLZULUNIUMBULMUMBULHNOUMBULPRUJBSUKGQHTUKUA
      LDZUNUODUKUBDHSDUPEAFUIUCBHUKUDUEBHAUFUGUH $.

    $( Diophantine set builder for conjunctions.  (Contributed by Stefan
       O'Rear, 10-Oct-2014.) $)
    anrabdioph $p |- ( ( { t e. ( NN0 ^m ( 1 ... N ) ) | ph } e. ( Dioph ` N )
        /\ { t e. ( NN0 ^m ( 1 ... N ) ) | ps } e. ( Dioph ` N ) ) -> { t e. (
        NN0 ^m ( 1 ... N ) ) | ( ph /\ ps ) } e. ( Dioph ` N ) ) $=
      ( cn0 c1 cfz co cmap crab cdioph cfv wcel wa cin inrab diophin eqeltrrid
      ) ACEFDGHIHZJZDKLZMBCSJZUAMNABNCSJTUBOUAABCSPTUBDQR $.

    $( Diophantine set builder for disjunctions.  (Contributed by Stefan
       O'Rear, 10-Oct-2014.) $)
    orrabdioph $p |- ( ( { t e. ( NN0 ^m ( 1 ... N ) ) | ph } e. ( Dioph ` N )
        /\ { t e. ( NN0 ^m ( 1 ... N ) ) | ps } e. ( Dioph ` N ) ) -> { t e. (
        NN0 ^m ( 1 ... N ) ) | ( ph \/ ps ) } e. ( Dioph ` N ) ) $=
      ( cn0 c1 cfz co cmap crab cdioph cfv wcel wa cun unrab diophun eqeltrrid
      wo ) ACEFDGHIHZJZDKLZMBCTJZUBMNABSCTJUAUCOUBABCTPUAUCDQR $.

    $( Diophantine set builder for ternary conjunctions.  (Contributed by
       Stefan O'Rear, 10-Oct-2014.) $)
    3anrabdioph $p |- ( ( { t e. ( NN0 ^m ( 1 ... N ) ) | ph } e. ( Dioph ` N )
        /\ { t e. ( NN0 ^m ( 1 ... N ) ) | ps } e. ( Dioph ` N ) /\ { t e. (
        NN0 ^m ( 1 ... N ) ) | ch } e. ( Dioph ` N ) ) -> { t e. ( NN0 ^m ( 1
        ... N ) ) | ( ph /\ ps /\ ch ) } e. ( Dioph ` N ) ) $=
      ( cn0 c1 cfz co cmap crab cdioph cfv wcel w3a wa df-3an rabbii anrabdioph
      sylan eqeltrid 3impa ) ADFGEHIJIZKELMZNZBDUCKUDNZCDUCKUDNZABCOZDUCKZUDNUE
      UFPZUGPUIABPZCPZDUCKZUDUHULDUCABCQRUJUKDUCKUDNUGUMUDNABDESUKCDESTUAUB $.

    $( Diophantine set builder for ternary disjunctions.  (Contributed by
       Stefan O'Rear, 10-Oct-2014.) $)
    3orrabdioph $p |- ( ( { t e. ( NN0 ^m ( 1 ... N ) ) | ph } e. ( Dioph ` N )
        /\ { t e. ( NN0 ^m ( 1 ... N ) ) | ps } e. ( Dioph ` N ) /\ { t e. (
        NN0 ^m ( 1 ... N ) ) | ch } e. ( Dioph ` N ) ) -> { t e. ( NN0 ^m ( 1
        ... N ) ) | ( ph \/ ps \/ ch ) } e. ( Dioph ` N ) ) $=
      ( cn0 c1 cfz co cmap crab cdioph cfv wcel w3o wa df-3or rabbii orrabdioph
      wo sylan eqeltrid 3impa ) ADFGEHIJIZKELMZNZBDUDKUENZCDUDKUENZABCOZDUDKZUE
      NUFUGPZUHPUJABTZCTZDUDKZUEUIUMDUDABCQRUKULDUDKUENUHUNUENABDESULCDESUAUBUC
      $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Diophantine sets 4 miscellanea
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d A c $.  $d B c $.  $d C b $.  $d a c $.  $d b c $.  $d C a $.
    $( Exchange an existential quantifier with two substitutions.  (Contributed
       by Stefan O'Rear, 11-Oct-2014.)  (Revised by NM, 24-Aug-2018.) $)
    2sbcrex $p |- ( [. A / a ]. [. B / b ]. E. c e. C ph
       <-> E. c e. C [. A / a ]. [. B / b ]. ph ) $=
      ( wrex wsbc sbcrex sbcbii bitri ) AGDHFCIZEBIAFCIZGDHZEBINEBIGDHMOEBAFGCD
      JKNEGBDJL $.
  $}

  ${
    $d A b $.  $d A c $.  $d B a $.  $d C a $.  $d a b $.  $d a c $.
    $( Exchange a substitution with two existentials.  (Contributed by Stefan
       O'Rear, 11-Oct-2014.)  (Revised by NM, 24-Aug-2018.) $)
    sbc2rex $p |- ( [. A / a ]. E. b e. B E. c e. C ph
       <-> E. b e. B E. c e. C [. A / a ]. ph ) $=
      ( wrex wsbc sbcrex rexbii bitri ) AGDHZFCHEBIMEBIZFCHAEBIGDHZFCHMEFBCJNOF
      CAEGBDJKL $.

    $d A d $.  $d A e $.  $d D a $.  $d E a $.  $d a d $.  $d a e $.
    $( Exchange a substitution with four existentials.  (Contributed by Stefan
       O'Rear, 11-Oct-2014.)  (Revised by NM, 24-Aug-2018.) $)
    sbc4rex $p |- ( [. A / a ]. E. b e. B E. c e. C E. d e. D E. e e. E ph
           <-> E. b e. B E. c e. C E. d e. D E. e e. E [. A / a ]. ph ) $=
      ( wrex wsbc sbc2rex 2rexbii bitri ) AFGLKELZJDLICLHBMQHBMZJDLICLAHBMFGLKE
      LZJDLICLQBCDHIJNRSIJCDABEGHKFNOP $.
  $}

  ${
    $d A b $.  $d A c $.  $d B a $.  $d C a $.  $d a c $.  $d a b $.
    $( also my first direct use of sp $)
    $( Rotate a sequence of three explicit substitutions.  (Contributed by
       Stefan O'Rear, 11-Oct-2014.)  (Revised by Mario Carneiro,
       11-Dec-2016.) $)
    sbcrot3 $p |- ( [. A / a ]. [. B / b ]. [. C / c ]. ph <->
      [. B / b ]. [. C / c ]. [. A / a ]. ph ) $=
      ( wsbc sbccom sbcbii bitri ) AGDHZFCHEBHLEBHZFCHAEBHGDHZFCHLEFBCIMNFCAEGB
      DIJK $.

    $d A d $.  $d A e $.  $d D a $.  $d E a $.  $d a e $.  $d a d $.
    $( Rotate a sequence of five explicit substitutions.  (Contributed by
       Stefan O'Rear, 11-Oct-2014.)  (Revised by Mario Carneiro,
       11-Dec-2016.) $)
    sbcrot5 $p |- ( [. A / a ]. [. B / b ]. [. C / c ]. [. D / d ].
        [. E / e ]. ph
      <-> [. B / b ]. [. C / c ]. [. D / d ]. [. E / e ]. [. A / a ]. ph ) $=
      ( wsbc sbcrot3 sbcbii bitri ) AFGLKELZJDLICLHBLPHBLZJDLZICLAHBLFGLKELZJDL
      ZICLPBCDHIJMRTICQSJDABEGHKFMNNO $.
  $}

  ${
    $d A a b $.  $d C a $.
    sbccomieg.1 $e |- ( a = A -> B = C ) $.
    $( Commute two explicit substitutions, using an implicit substitution to
       rewrite the exiting substitution.  (Contributed by Stefan O'Rear,
       11-Oct-2014.)  (Revised by Mario Carneiro, 11-Dec-2016.) $)
    sbccomieg $p |- ( [. A / a ]. [. B / b ]. ph
         <-> [. C / b ]. [. A / a ]. ph ) $=
      ( wsbc cvv wcel sbcex wex spesbc exlimiv syl nfcv nfsbc1v nfsbcw cv wceq
      sbceq1a sbceqbid sbciegf pm5.21nii ) AFCHZEBHBIJZAEBHZFDHZUEEBKUHUGFLUFUG
      FDMUGUFFAEBKNOUEUHEBIUGEFDEDPAEBQRESBTAUGFCDGAEBUAUBUCUD $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Diophantine sets 4: Quantification
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d N t u v a b c $.  $d M t u v a b c $.  $d ph u v a b c $.
    $d ps t a b c $.  $d ch v a b c $.
    rexrabdioph.1 $e |- M = ( N + 1 ) $.
    rexrabdioph.2 $e |- ( v = ( t ` M ) -> ( ps <-> ch ) ) $.
    rexrabdioph.3 $e |- ( u = ( t |` ( 1 ... N ) ) -> ( ch <-> ph ) ) $.
    $( Diophantine set builder for existential quantification.  (Contributed by
       Stefan O'Rear, 10-Oct-2014.) $)
    rexrabdioph $p |- ( ( N e. NN0 /\ { t e. ( NN0 ^m ( 1 ... M ) ) | ph } e. (
        Dioph ` M ) ) -> { u e. ( NN0 ^m ( 1 ... N ) ) | E. v e. NN0 ps } e. (
        Dioph ` N ) ) $=
      ( va vb vc cn0 wcel wa wrex wceq wsbc c1 cfz co cmap crab cdioph cfv cres
      cab df-rab dfsbcq cbvrexvw anbi2i r19.42v bitr4i cop csn cun simpll simpr
      cv simplr mapfzcons syl3anc adantrr mapfzcons2 syl2anc mapfzcons1 sbceq1d
      eqcomd adantl sbceqbid biimpd fveq1 reseq1 eqeq2d anbi12d rspcev syl12anc
      impr rexlimdva2 wf caddc nn0p1nn eqeltrid elfz1end sylib ffvelcdm syl2anr
      elmapi cn adantr simprr mapfzcons1cl ad2antlr eqeltrd wb sbcbidv ad2antll
      simprl mpbird anbi2d impbid bitrid abbidv eqtrid nfcv nfv nfsbc1v sbceq1a
      nfsbcw nfrexw weq rexbidv cbvrexw bitrdi cbvrabw rexrab abbii 3eqtr4g vex
      fvex resex sylan9bb sbc2ie rabbii rexeqi eqtrdi cuz cz nn0z uzid peano2uz
      simpl 3syl diophrex ) HOPZAFOUAGUBUCZUDUCZUEZGUFUGPZQZBDORZEOUAHUBUCZUDUC
      ZUEZLVAZMVAZUUDUHZSZMYTRZLUIZHUFUGZYQUUFUULSUUAYQUUFUUJMBEFVAZUUDUHZTZDGU
      UNUGZTZFYSUEZRZLUIZUULYQBEUUGTZDUUHTZMORZLUUEUEZBEUUITZDGUUHUGZTZUUJQZMYS
      RZLUIZUUFUVAYQUVEUUGUUEPZUVDQZLUIUVKUVDLUUEUJYQUVMUVJLUVMUVLUVBDNVAZTZQZN
      ORZYQUVJUVMUVLUVONORZQUVQUVDUVRUVLUVCUVOMNOUVBDUUHUVNUKULUMUVLUVONOUNUOYQ
      UVQUVJYQUVPUVJNOYQUVNOPZQZUVPQUUGGUVNUPUQURZYSPZBEUWAUUDUHZTZDGUWAUGZTZUU
      GUWCSZUVJUVTUVLUWBUVOUVTUVLQZYQUVLUVSUWBYQUVSUVLUSUVTUVLUTZYQUVSUVLVBZUUG
      OUVNGHIVCVDVEUVTUVLUVOUWFUWHUVOUWFUWHUVBUWDDUVNUWEUWHUWEUVNUWHUVLUVSUWEUV
      NSUWIUWJUUGOUVNGHIVFVGVJUWHBEUUGUWCUWHUWCUUGUVLUWCUUGSUVTUUGOUVNGHIVHVKVJ
      ZVIVLVMVTUVTUVLUWGUVOUWKVEUVIUWFUWGQMUWAYSUUHUWASZUVHUWFUUJUWGUWLUVFUWDDU
      VGUWEGUUHUWAVNUWLBEUUIUWCUUHUWAUUDVOZVIVLUWLUUIUWCUUGUWMVPVQVRVSWAYQUVIUV
      QMYSYQUUHYSPZQZUVIQZUVGOPZUVLUVBDUVGTZUVQUWOUWQUVIUWNYROUUHWBGYRPZUWQYQUU
      HOYRWJYQGWKPUWSYQGHUAWCUCZWKIHWDWEGWFWGYROGUUHWHWIWLUWPUUGUUIUUEUWOUVHUUJ
      WMUWNUUIUUEPYQUVIUUHOGHIWNWOWPUWPUWRUVHUWOUVHUUJWTUUJUWRUVHWQUWOUVHUUJUVB
      UVFDUVGBEUUGUUIUKWRWSXAUVPUVLUWRQNUVGOUVNUVGSUVOUWRUVLUVBDUVNUVGUKXBVRVSW
      AXCXDXEXFUUCUVDELUUEEUUEXGLUUEXGUUCLXHUVCEMOEOXGUVBEDUUHEUUHXGBEUUGXIXKXL
      ELXMZUUCUVBDORUVDUXABUVBDOBEUUGXJXNUVBUVCDMOUVBMXHUVBDUUHXIUVBDUUHXJXOXPX
      QUUTUVJLUURUVHUUJMFYSFMXMZUUPUVFDUUQUVGGUUNUUHVNUXBBEUUOUUIUUNUUHUUDVOVIV
      LXRXSXTUUTUUKLUUJMUUSYTUURAFYSBADEUUQUUOGUUNYBUUNUUDFYAYCDVAUUQSBCEVAUUOS
      AJKYDYEYFYGXSYHWLUUBYQGHYIUGZPZUUAUULUUMPYQUUAYNYQUXDUUAYQGUWTUXCIYQHYJPH
      UXCPUWTUXCPHYKHYLHHYMYOWEWLYQUUAUTMLYTGHYPVDWP $.
  $}

  ${
    $d G a b t u v w x y z p q $.  $d H a b t u v w x y z p q $.
    $d I a b t u v w x y z p q $.  $d J a b t u v w x y z p q $.
    $d K a b t u v w x y z p q $.  $d L a b t u v w x y z p q $.
    $d M a b t u v w x y z p q $.  $d N a b t u v w x y z p q $.
    $d ph a b t $.
    rexfrabdioph.1 $e |- M = ( N + 1 ) $.
    $( Diophantine set builder for existential quantifier, explicit
       substitution.  (Contributed by Stefan O'Rear, 11-Oct-2014.)  (Revised by
       Stefan O'Rear, 6-May-2015.) $)
    rexfrabdioph $p |- ( ( N e. NN0 /\ { t e. ( NN0 ^m ( 1 ... M ) )
   | [. ( t |` ( 1 ... N ) ) / u ]. [. ( t ` M ) / v ]. ph } e. ( Dioph ` M ) )
      -> { u e. ( NN0 ^m ( 1 ... N ) ) | E. v e. NN0 ph } e. ( Dioph ` N ) ) $=
      ( vb va cn0 wcel cv cfv wsbc c1 cfz co crab wrex nfcv cres cmap cdioph wa
      nfsbc1v nfrexw wceq sbceq1a cbvrexw rexbidv bitrid cbvrabw dfsbcq sbcbidv
      nfv rexrabdioph eqeltrid ) FJKABEDLZMZNZCUROFPQZUAZNZDJOEPQUBQREUCMKUDABJ
      SZCJVAUBQZRABHLZNZCILZNZHJSZIVERFUCMVDVJCIVECVETIVETVDIUOVICHJCJTVGCVHUEU
      FVDVGHJSCLVHUGZVJAVGBHJAHUOABVFUEABVFUHUIVKVGVIHJVGCVHUHUJUKULVCVIUTCVHNH
      IDEFGVFUSUGVGUTCVHABVFUSUMUNUTCVHVBUMUPUQ $.

    rexfrabdioph.2 $e |- L = ( M + 1 ) $.
    $( Diophantine set builder for existential quantifier, explicit
       substitution, two variables.  (Contributed by Stefan O'Rear,
       11-Oct-2014.)  (Revised by Stefan O'Rear, 6-May-2015.) $)
    2rexfrabdioph $p |- ( ( N e. NN0 /\ { t e. ( NN0 ^m ( 1 ... L ) )
 | [. ( t |` ( 1 ... N ) ) / u ]. [. ( t ` M ) / v ]. [. ( t ` L ) / w ]. ph }
  e. ( Dioph ` L ) ) -> { u e. ( NN0 ^m ( 1 ... N ) ) | E. v e. NN0 E. w e.
        NN0 ph } e. ( Dioph ` N ) ) $=
      ( va cn0 wcel cfv wsbc c1 cfz co cres crab cv cmap cdioph wrex wa 2sbcrex
      rabbii peano2nn0 eqeltrid adantr sbcrot3 sbcbii reseq1 sbccomieg wss wceq
      caddc fzssp1 oveq2i sseqtrri resabs1 dfsbcq mp2b cvv resex fveq1 sbcco3gw
      wb vex ax-mp cn nn0p1nn elfz1end sylib fvres 3syl sbcbidv bitr2id rabbidv
      bitrid eleq1d biimpa rexfrabdioph syl2anc syldan ) HLMZABFEUAZNZOZCGWGNZO
      ZDWGPHQRZSZOZELPFQRUBRZTZFUCNZMZABLUDZCGKUAZNZODWTWLSZOZKLPGQRZUBRZTZGUCN
      ZMWSCLUDDLWLUBRTHUCNMWFWRUEZXFACXAODXBOZBLUDZKXETZXGXCXJKXEAXBXALDCBUFUGX
      HGLMZXIBWHOZKWGXDSZOZEWOTZWQMZXKXGMWFXLWRWFGHPUQRZLIHUHUIUJWFWRXQWFWPXPWQ
      WFWNXOEWOXOWICXAOZDXBOZKXNOZWFWNXMXTKXNAWHXBXABDCUKULYAXSKXNOZDXNWLSZOZWF
      WNXSXNXBYCKDWTXNWLUMUNYDYBDWMOZWFWNWLXDUOYCWMUPYDYEVHWLPXRQRXDPHURGXRPQIU
      SUTWGWLXDVAYBDYCWMVBVCWFYBWKDWMYBWICGXNNZOZWFWKXNVDMYBYGVHWGXDEVIVEWIKCXN
      XAYFVDGWTXNVFVGVJWFGXDMZYFWJUPYGWKVHWFGVKMYHWFGXRVKIHVLUIGVMVNGXDWGVOWICY
      FWJVBVPVTVQVTVTVRVSWAWBXIBKEFGJWCWDUIWSCDKGHIWCWE $.

    rexfrabdioph.3 $e |- K = ( L + 1 ) $.
    $( Diophantine set builder for existential quantifier, explicit
       substitution, two variables.  (Contributed by Stefan O'Rear,
       17-Oct-2014.)  (Revised by Stefan O'Rear, 6-May-2015.) $)
    3rexfrabdioph $p |- ( ( N e. NN0
          /\ { t e. ( NN0 ^m ( 1 ... K ) )
      | [. ( t |` ( 1 ... N ) ) / u ]. [. ( t ` M ) / v ]. [. ( t ` L ) / w ].
      [. ( t ` K ) / x ]. ph } e. ( Dioph ` K ) )
   -> { u e. ( NN0 ^m ( 1 ... N ) )
        | E. v e. NN0 E. w e. NN0 E. x e. NN0 ph } e. ( Dioph ` N ) ) $=
      ( va cn0 wcel cfv wsbc c1 co cv cfz cres cmap crab cdioph wrex wa sbc2rex
      sbcbii bitri rabbii caddc nn0p1nn eqeltrid nnnn0d adantr reseq1 sbccomieg
      cn sbcrot3 wss wceq wb fzssp1 oveq2i sseqtrri resabs1 dfsbcq mp2b cvv vex
      resex fveq1 sbcco3gw ax-mp sylib fvres 3syl bitrid sbcbidv bitr3id eleq1d
      elfz1end rabbidv biimpar 2rexfrabdioph syl2anc rexfrabdioph syldan ) JOPZ
      ABGFUAZQZRCHWLQZRZDIWLQZRZEWLSJUBTZUCZRZFOSGUBTUDTZUEZGUFQZPZABOUGCOUGZDI
      NUAZQZRZEXFWRUCZRZNOSIUBTZUDTZUEZIUFQZPXEDOUGEOWRUDTUEJUFQPWKXDUHZXMADXGR
      ZEXIRZBOUGCOUGZNXLUEZXNXJXRNXLXJXPBOUGCOUGZEXIRXRXHXTEXIAXGOODCBUIUJXPXIO
      OECBUIUKULXOIOPZXQBWMRCWNRZNWLXKUCZRZFXAUEZXCPZXSXNPWKYAXDWKIWKIJSUMTZUTK
      JUNUOZUPUQWKYFXDWKYEXBXCWKYDWTFXAYDWODXGRZEXIRZNYCRZWKWTYJYBNYCYJXPBWMRCW
      NRZEXIRYBYIYLEXIAXGWNWMDCBVAUJXPXIWNWMECBVAUKUJYKYINYCRZEYCWRUCZRZWKWTYIY
      CXIYNNEXFYCWRURUSYOYMEWSRZWKWTWRXKVBYNWSVCYOYPVDWRSYGUBTXKSJVEIYGSUBKVFVG
      WLWRXKVHYMEYNWSVIVJWKYMWQEWSYMWODIYCQZRZWKWQYCVKPYMYRVDWLXKFVLVMWONDYCXGY
      QVKIXFYCVNVOVPWKIXKPZYQWPVCYRWQVDWKIUTPYSYHIWDVQIXKWLVRWODYQWPVIVSVTWAVTV
      TWBWEWCWFXQBCNFGHILMWGWHUOXEDENIJKWIWJ $.

    rexfrabdioph.4 $e |- J = ( K + 1 ) $.
    $( Diophantine set builder for existential quantifier, explicit
       substitution, four variables.  (Contributed by Stefan O'Rear,
       11-Oct-2014.)  (Revised by Stefan O'Rear, 6-May-2015.) $)
    4rexfrabdioph $p |- ( ( N e. NN0 /\ { t e. ( NN0 ^m ( 1 ... J ) )
       | [. ( t |` ( 1 ... N ) ) / u ]. [. ( t ` M ) / v ]. [. ( t ` L ) / w ].
       [. ( t ` K ) / x ]. [. ( t ` J ) / y ]. ph } e. ( Dioph ` J ) )
   -> { u e. ( NN0 ^m ( 1 ... N ) ) | E. v e. NN0 E. w e. NN0 E. x e. NN0
        E. y e. NN0 ph } e. ( Dioph ` N ) ) $=
      ( va cn0 wcel wsbc cv cfv c1 cfz co cres cmap crab cdioph wrex wa 2sbcrex
      rexbii bitri sbcbii sbc2rex rabbii caddc eqeltrid peano2nnd nnnn0d adantr
      cn nn0p1nn sbcrot3 bitr3i reseq1 sbccomieg wceq wb fzssp1 oveq2i sseqtrri
      wss sstri resabs1 dfsbcq mp2b fveq1 elfz1end sylib sselid fvres cvv resex
      3syl vex sbcco3gw ax-mp bitrid sbcbidv bitrd rabbidv eleq1d 2rexfrabdioph
      biimpar syl2anc syldan ) LRSZACHGUAZUBZTZBIWTUBZTZDJWTUBZTZEKWTUBZTZFWTUC
      LUDUEZUFZTZGRUCHUDUEUGUEZUHZHUIUBZSZACRUJZBRUJZDJQUAZUBZTEKXRUBZTZFXRXIUF
      ZTZQRUCJUDUEZUGUEZUHZJUIUBZSXQDRUJERUJFRXIUGUEUHLUIUBSWSXOUKZYFADXSTEXTTZ
      FYBTZCRUJBRUJZQYEUHZYGYCYKQYEYCYICRUJZBRUJZFYBTYKYAYNFYBYAXPDXSTEXTTZBRUJ
      YNXPXTXSREDBULYOYMBRAXTXSREDCULUMUNUOYIYBRRFBCUPUNUQYHJRSZYJCXATBXCTZQWTY
      DUFZTZGXLUHZXNSZYLYGSWSYPXOWSJWSJKUCURUEZVCNWSKWSKLUCURUEZVCMLVDUSZUTUSZV
      AVBWSUUAXOWSYTXMXNWSYSXKGXLYSXDDXSTZEXTTZFYBTZQYRTZWSXKYQUUHQYRYQYICXATZB
      XCTZFYBTUUHYIYBXCXAFBCVEUUKUUGFYBUUKXBDXSTEXTTZBXCTUUGUUJUULBXCAXAXTXSCED
      VEUOXBXCXTXSBEDVEUNUOVFUOUUIUUGQYRTZFYRXIUFZTZWSXKUUGYRYBUUNQFXRYRXIVGVHU
      UOUUMFXJTZWSXKXIYDVNUUNXJVIUUOUUPVJXIUCKUDUEZYDXIUCUUCUDUEUUQUCLVKKUUCUCU
      DMVLVMUUQUCUUBUDUEYDUCKVKJUUBUCUDNVLVMZVOWTXIYDVPUUMFUUNXJVQVRWSUUMXHFXJU
      UMUUFQYRTZEKYRUBZTZWSXHUUFYRXTUUTQEKXRYRVSVHWSUVAUUSEXGTZXHWSKYDSUUTXGVIU
      VAUVBVJWSUUQYDKUURWSKVCSKUUQSUUDKVTWAWBKYDWTWCUUSEUUTXGVQWFWSUUSXFEXGUUSX
      DDJYRUBZTZWSXFYRWDSUUSUVDVJWTYDGWGWEXDQDYRXSUVCWDJXRYRVSWHWIWSJYDSZUVCXEV
      IUVDXFVJWSJVCSUVEUUEJVTWAJYDWTWCXDDUVCXEVQWFWJWKWLWJWKWJWJWJWMWNWPYJCBQGH
      IJOPWOWQUSXQDEFQJKLMNWOWR $.

    rexfrabdioph.5 $e |- I = ( J + 1 ) $.
    rexfrabdioph.6 $e |- H = ( I + 1 ) $.
    $( Diophantine set builder for existential quantifier, explicit
       substitution, six variables.  (Contributed by Stefan O'Rear,
       11-Oct-2014.)  (Revised by Stefan O'Rear, 6-May-2015.) $)
    6rexfrabdioph $p |- ( ( N e. NN0 /\ { t e. ( NN0 ^m ( 1 ... H ) )
       | [. ( t |` ( 1 ... N ) ) / u ]. [. ( t ` M ) / v ]. [. ( t ` L ) / w ].
       [. ( t ` K ) / x ]. [. ( t ` J ) / y ]. [. ( t ` I ) / z ].
       [. ( t ` H ) / p ]. ph } e. ( Dioph ` H ) )
  -> { u e. ( NN0 ^m ( 1 ... N ) ) | E. v e. NN0 E. w e. NN0 E. x e. NN0
       E. y e. NN0 E. z e. NN0 E. p e. NN0 ph } e. ( Dioph ` N ) ) $=
      ( va cn0 wcel cv cfv wsbc c1 cfz co cres cmap crab cdioph wrex wa sbc4rex
      sbcbii bitri rabbii caddc nn0p1nn eqeltrid peano2nnd nnnn0d adantr reseq1
      cn sbcrot5 sbccomieg wss wceq fzssp1 oveq2i sseqtrri sstri resabs1 dfsbcq
      mp2b fveq1 elfz1end sylib sselid fvres 3syl cvv vex resex sbcco3gw bitrid
      wb ax-mp sbcbidv bitrd bitr3id rabbidv eleq1d 4rexfrabdioph 2rexfrabdioph
      biimpar syl2anc syldan ) OUDUEZAPIHUFZUGZUHDJXEUGZUHCKXEUGZUHBLXEUGZUHZEM
      XEUGZUHZFNXEUGZUHZGXEUIOUJUKZULZUHZHUDUIIUJUKUMUKZUNZIUOUGZUEZAPUDUPDUDUP
      CUDUPBUDUPZEMUCUFZUGZUHZFNYCUGZUHZGYCXOULZUHZUCUDUIMUJUKZUMUKZUNZMUOUGZUE
      YBEUDUPFUDUPGUDXOUMUKUNOUOUGUEXDYAUQZYLAEYDUHZFYFUHZGYHUHZPUDUPDUDUPCUDUP
      BUDUPZUCYKUNZYMYIYRUCYKYIYPPUDUPDUDUPCUDUPBUDUPZGYHUHYRYGYTGYHYGYOPUDUPDU
      DUPCUDUPBUDUPZFYFUHYTYEUUAFYFAYDUDUDUDPUDEBCDURUSYOYFUDUDUDPUDFBCDURUTUSY
      PYHUDUDUDPUDGBCDURUTVAYNMUDUEZYQPXFUHDXGUHCXHUHBXIUHZUCXEYJULZUHZHXRUNZXT
      UEZYSYMUEXDUUBYAXDMXDMNUIVBUKZVIRXDNXDNOUIVBUKZVIQOVCVDZVEVDZVFVGXDUUGYAX
      DUUFXSXTXDUUEXQHXRUUEXJEYDUHZFYFUHZGYHUHZUCUUDUHZXDXQUUNUUCUCUUDUUNYPPXFU
      HDXGUHCXHUHBXIUHZGYHUHUUCUUMUUPGYHUUMYOPXFUHDXGUHCXHUHBXIUHZFYFUHUUPUULUU
      QFYFAYDXIXHXGPXFEBCDVJUSYOYFXIXHXGPXFFBCDVJUTUSYPYHXIXHXGPXFGBCDVJUTUSUUO
      UUMUCUUDUHZGUUDXOULZUHZXDXQUUMUUDYHUUSUCGYCUUDXOVHVKUUTUURGXPUHZXDXQXOYJV
      LUUSXPVMUUTUVAWLXOUINUJUKZYJXOUIUUIUJUKUVBUIOVNNUUIUIUJQVOVPUVBUIUUHUJUKY
      JUINVNMUUHUIUJRVOVPZVQXEXOYJVRUURGUUSXPVSVTXDUURXNGXPUURUULUCUUDUHZFNUUDU
      GZUHZXDXNUULUUDYFUVEUCFNYCUUDWAVKXDUVFUVDFXMUHZXNXDNYJUEUVEXMVMUVFUVGWLXD
      UVBYJNUVCXDNVIUENUVBUEUUJNWBWCWDNYJXEWEUVDFUVEXMVSWFXDUVDXLFXMUVDXJEMUUDU
      GZUHZXDXLUUDWGUEUVDUVIWLXEYJHWHWIXJUCEUUDYDUVHWGMYCUUDWAWJWMXDMYJUEZUVHXK
      VMUVIXLWLXDMVIUEUVJUUKMWBWCMYJXEWEXJEUVHXKVSWFWKWNWOWKWNWKWKWPWQWRXAYQDPC
      BUCHIJKLMSTUAUBWSXBVDYBEFGUCMNOQRWTXC $.

    rexfrabdioph.7 $e |- G = ( H + 1 ) $.
    $( Diophantine set builder for existential quantifier, explicit
       substitution, seven variables.  (Contributed by Stefan O'Rear,
       11-Oct-2014.)  (Revised by Stefan O'Rear, 6-May-2015.) $)
    7rexfrabdioph $p |- ( ( N e. NN0 /\ { t e. ( NN0 ^m ( 1 ... G ) )
       | [. ( t |` ( 1 ... N ) ) / u ]. [. ( t ` M ) / v ]. [. ( t ` L ) / w ].
       [. ( t ` K ) / x ]. [. ( t ` J ) / y ]. [. ( t ` I ) / z ].
       [. ( t ` H ) / p ]. [. ( t ` G ) / q ]. ph } e. ( Dioph ` G ) )
  -> { u e. ( NN0 ^m ( 1 ... N ) ) | E. v e. NN0 E. w e. NN0 E. x e. NN0
     E. y e. NN0 E. z e. NN0 E. p e. NN0 E. q e. NN0 ph } e. ( Dioph ` N ) ) $=
      ( va cn0 wcel cv cfv wsbc c1 cfz co cres cmap crab cdioph wrex wa sbc2rex
      sbc4rex 2rexbii bitri sbcbii 3bitri rabbii caddc cn nn0p1nn nnnn0d adantr
      eqeltrid sbcrot3 sbcrot5 reseq1 sbccomieg wss wceq fzssp1 oveq2i sseqtrri
      wb resabs1 dfsbcq cvv vex resex fveq1 sbcco3gw ax-mp elfz1end sylib fvres
      bitrid sbcbidv bitr3id rabbidv biimpar 6rexfrabdioph syl2anc rexfrabdioph
      mp2b 3syl eleq1d syldan ) PUGUHZAQIHUIZUJZUKRJXHUJZUKDKXHUJZUKCLXHUJZUKZB
      MXHUJZUKENXHUJZUKZFOXHUJZUKZGXHULPUMUNZUOZUKZHUGULIUMUNUPUNZUQZIURUJZUHZA
      QUGUSRUGUSDUGUSCUGUSZBUGUSEUGUSZFOUFUIZUJZUKZGYHXSUOZUKZUFUGULOUMUNZUPUNZ
      UQZOURUJZUHYGFUGUSGUGXSUPUNUQPURUJUHXGYEUTZYOAFYIUKZGYKUKZQUGUSRUGUSDUGUS
      CUGUSZBUGUSEUGUSZUFYNUQZYPYLUUAUFYNYLYRQUGUSRUGUSDUGUSCUGUSZBUGUSEUGUSZGY
      KUKUUCGYKUKZBUGUSEUGUSUUAYJUUDGYKYJYFFYIUKZBUGUSEUGUSUUDYFYIUGUGFEBVAUUFU
      UCEBUGUGAYIUGUGUGQUGFCDRVBVCVDVEUUCYKUGUGGEBVAUUEYTEBUGUGYRYKUGUGUGQUGGCD
      RVBVCVFVGYQOUGUHZYSQXIUKRXJUKDXKUKCXLUKZBXNUKZEXOUKZUFXHYMUOZUKZHYBUQZYDU
      HZUUBYPUHXGUUGYEXGOXGOPULVHUNZVISPVJVMZVKVLXGUUNYEXGUUMYCYDXGUULYAHYBUULX
      PFYIUKZGYKUKZUFUUKUKZXGYAUURUUJUFUUKUURXMFYIUKZBXNUKEXOUKZGYKUKUUTGYKUKZB
      XNUKZEXOUKUUJUUQUVAGYKXMYIXOXNFEBVNVEUUTYKXOXNGEBVNUVCUUIEXOUVBUUHBXNUVBY
      RQXIUKRXJUKDXKUKCXLUKZGYKUKUUHUUTUVDGYKAYIXLXKXJQXIFCDRVOVEYRYKXLXKXJQXIG
      CDRVOVDVEVEVFVEUUSUUQUFUUKUKZGUUKXSUOZUKZXGYAUUQUUKYKUVFUFGYHUUKXSVPVQUVG
      UVEGXTUKZXGYAXSYMVRUVFXTVSUVGUVHWCXSULUUOUMUNYMULPVTOUUOULUMSWAWBXHXSYMWD
      UVEGUVFXTWEXCXGUVEXRGXTUVEXPFOUUKUJZUKZXGXRUUKWFUHUVEUVJWCXHYMHWGWHXPUFFU
      UKYIUVIWFOYHUUKWIWJWKXGOYMUHZUVIXQVSUVJXRWCXGOVIUHUVKUUPOWLWMOYMXHWNXPFUV
      IXQWEXDWOWPWOWOWQWRXEWSYSCDRBEUFHIJKLMNOQTUAUBUCUDUEWTXAVMYGFGUFOPSXBXF
      $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Diophantine sets 5: Arithmetic sets
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d N t $.
    $( Lemma for arithmetic diophantine sets.  Convert polynomial-ness of an
       expression into a constraint suitable for ~ ralimi .  (Contributed by
       Stefan O'Rear, 10-Oct-2014.) $)
    rabdiophlem1 $p |- ( ( t e. ( ZZ ^m ( 1 ... N ) ) |-> A ) e. ( mzPoly ` ( 1
        ... N ) ) -> A. t e. ( NN0 ^m ( 1 ... N ) ) A e. ZZ ) $=
      ( cn0 c1 cfz co cmap cz wss cmpt cmzp cfv wcel cvv zex nn0ssz mapss mp2an
      wral wf mzpf eqid fmpt sylibr ssralv mpsyl ) DECFGZHGZIUHHGZJZAUJBKZUHLMN
      ZBINZAUJTZUNAUITIONDIJUKPQDIUHORSUMUJIULUAUOULUHUBAUJIBULULUCUDUEUNAUIUJU
      FUG $.
  $}

  ${
    $d N a u t $.  $d M a u t $.  $d A a t $.
    rabdiophlem2.1 $e |- M = ( N + 1 ) $.
    $( Lemma for arithmetic diophantine sets.  Reuse a polynomial expression
       under a new quantifier.  (Contributed by Stefan O'Rear, 10-Oct-2014.) $)
    rabdiophlem2 $p |- ( ( N e. NN0 /\ ( u e. ( ZZ ^m ( 1 ... N ) ) |-> A ) e.
        ( mzPoly ` ( 1 ... N ) ) ) -> ( t e. ( ZZ ^m ( 1 ... M ) ) |-> [_ ( t
        |` ( 1 ... N ) ) / u ]_ A ) e. ( mzPoly ` ( 1 ... M ) ) ) $=
      ( va wcel cz c1 cfz co cmap cmpt cmzp cfv wa cv csb nfcsb1v cn0 cres nfcv
      csbeq1a cbvmpt fveq1i eqid csbeq1 mapfzcons1cl adantl wral wf mzpf sylibr
      fmpt ad2antlr nfel1 wceq eleq1d rspc sylc fvmptd3 eqtr2id mpteq2dva ovexd
      cvv wss caddc fzssp1 oveq2i sseqtrri simpr mzpresrename syl3anc eqeltrd
      a1i ) EUAHZAIJEKLZMLZCNZVROPHZQZBIJDKLZMLZABRZVRUBZCSZNBWDWFVTPZNZWCOPZWB
      BWDWGWHWBWEWDHZQZWHWFGVSAGRZCSZNZPWGWFVTWOAGVSCWNGCUCAWMCTAWMCUDUEUFWLGWF
      WNWGVSWOIWOUGAWMWFCUHWKWFVSHZWBWEIDEFUIUJZWLWPCIHZAVSUKZWGIHZWQWAWSVQWKWA
      VSIVTULWSVTVRUMAVSICVTVTUGUOUNUPWRWTAWFVSAWGIAWFCTUQARWFURCWGIAWFCUDUSUTV
      AVBVCVDWBWCVFHVRWCVGZWAWIWJHWBJDKVEXAWBVRJEJVHLZKLWCJEVIDXBJKFVJVKVPVQWAV
      LBVTVRWCVMVNVO $.
  $}

  ${
    $d A a b c $.  $d N a b c t $.
    $( Diophantine set builder for nonnegativity constraints.  The first
       builder which uses a witness variable internally; an expression is
       nonnegative if there is a nonnegative integer equal to it.  (Contributed
       by Stefan O'Rear, 11-Oct-2014.) $)
    elnn0rabdioph $p |- ( ( N e. NN0 /\ ( t e. ( ZZ ^m ( 1 ... N ) ) |-> A ) e.
        ( mzPoly ` ( 1 ... N ) ) ) -> { t e. ( NN0 ^m ( 1 ... N ) ) | A e. NN0
        } e. ( Dioph ` N ) ) $=
      ( vb va vc cn0 wcel cz c1 cfz co cmap cmpt cmzp cfv crab cv wceq nfcv csb
      wa wrex cdioph risset rabbii a1i nfv nfcsb1v nfeq2 nfrexw csbeq1a rexbidv
      eqeq2d cbvrabw eqtrdi caddc cres peano2nn0 adantr cvv cn nn0p1nn elfz1end
      ovex sylib mzpproj sylancr eqid rabdiophlem2 eqrabdioph eqeq1 rexrabdioph
      syl3anc csbeq1 syldan eqeltrd ) CGHZAIJCKLZMLBNVSOPHZUBZBGHZAGVSMLZQZDRZA
      ERZBUAZSZDGUCZEWCQZCUDPZWAWDWEBSZDGUCZAWCQZWJWDWNSWAWBWMAWCDBGUEUFUGWMWIA
      EWCAWCTEWCTWMEUHWHADGAGTAWEWGAWFBUIUJUKARWFSZWLWHDGWOBWGWEAWFBULUNUMUOUPV
      RVTCJUQLZFRZPZAWQVSURZBUAZSZFGJWPKLZMLQWPUDPHZWJWKHWAWPGHZFIXBMLZWRNXBOPZ
      HZFXEWTNXFHXCVRXDVTCUSUTWAXBVAHWPXBHZXGJWPKVEVRXHVTVRWPVBHXHCVCWPVDVFUTFX
      BWPVGVHAFBWPCWPVIZVJFWRWTWPVKVNXAWHWRWGSDEFWPCXIWEWRWGVLWFWSSWGWTWRAWFWSB
      VOUNVMVPVQ $.
  $}

  ${
    $d ph y $.  $d ps x $.  $d ch x $.  $d x y $.
    rexzrexnn0.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    rexzrexnn0.2 $e |- ( x = -u y -> ( ph <-> ch ) ) $.
    $( Rewrite an existential quantification restricted to integers into an
       existential quantification restricted to naturals.  (Contributed by
       Stefan O'Rear, 11-Oct-2014.) $)
    rexzrexnn0 $p |- ( E. x e. ZZ ph <-> E. y e. NN0 ( ps \/ ch ) ) $=
      ( cz wrex wo cn0 cv wcel wa cneg simpr wceq wb bicomd rspcev cr elznn0 ex
      simprbi adantr simplr equcoms syl2anc zcn negnegd eqcomd negeq syl5ibrcom
      eqeq2d imp syl adantlr rspcedv impancom orim12d mpd r19.43 rexlimiva nn0z
      sylibr sylan nn0negz jaodan impbii ) ADHIZBCJZEKIZAVLDHDLZHMZANZBEKIZCEKI
      ZJZVLVOVMKMZVMOZKMZJZVRVNWBAVNVMUAMWBVMUBUDUEVOVSVPWAVQVOVSVPVOVSNVSAVPVO
      VSPVNAVSUFBAEVMKELZVMQABABRDEFUGSTUHUCVNWAAVQVNWANCAEVTKVNWAPVNWCVTQZCARW
      AVNWDNZACWEVMWCOZQZACRVNWDWGVNWGWDVMVTOZQVNWHVMVNVMVMUIUJUKWDWFWHVMWCVTUL
      UNUMUOGUPSUQURUSUTVABCEKVBVEVCVKVJEKWCKMZBVJCWIWCHMBVJWCVDABDWCHFTVFWIWFH
      MCVJWCVGACDWFHGTVFVHVCVI $.
  $}

  ${
    $d N t $.  $d M t $.
    $( Diophantine set builder for the "less than or equal to" relation.
       (Contributed by Stefan O'Rear, 11-Oct-2014.) $)
    lerabdioph $p |- ( ( N e. NN0 /\ ( t e. ( ZZ ^m ( 1 ... N ) ) |-> A ) e. (
        mzPoly ` ( 1 ... N ) ) /\ ( t e. ( ZZ ^m ( 1 ... N ) ) |-> B ) e. (
        mzPoly ` ( 1 ... N ) ) ) -> { t e. ( NN0 ^m ( 1 ... N ) ) | A <_ B } e.
        ( Dioph ` N ) ) $=
      ( cn0 wcel cz c1 cfz co cmap cmpt cmzp cfv crab wral rabdiophlem1 3adant1
      w3a wa cle cmin cdioph wceq wb znn0sub ralimi r19.26 rabbi 3imtr3i syl2an
      wbr simp1 mzpsubmpt ancoms elnn0rabdioph syl2anc eqeltrd ) DEFZAGHDIJZKJZ
      BLUTMNZFZAVACLVBFZSZBCUAULZAEUTKJZOZCBUBJZEFZAVGOZDUCNZVCVDVHVKUDZUSVCBGF
      ZAVGPZCGFZAVGPZVMVDABDQACDQVNVPTZAVGPVFVJUEZAVGPVOVQTVMVRVSAVGBCUFUGVNVPA
      VGUHVFVJAVGUIUJUKRVEUSAVAVILVBFZVKVLFUSVCVDUMVCVDVTUSVDVCVTACBUTUNUORAVID
      UPUQUR $.

    $( Diophantine set builder for membership in a fixed upper set of integers.
       (Contributed by Stefan O'Rear, 11-Oct-2014.) $)
    eluzrabdioph $p |- ( ( N e. NN0 /\ M e. ZZ /\ ( t e. ( ZZ ^m ( 1 ... N ) )
        |-> A ) e. ( mzPoly ` ( 1 ... N ) ) ) -> { t e. ( NN0 ^m ( 1 ... N ) )
        | A e. ( ZZ>= ` M ) } e. ( Dioph ` N ) ) $=
      ( cn0 wcel cz c1 cfz co cmap cmpt cmzp cfv w3a cuz crab cle wbr wral wceq
      cdioph wa wb rabdiophlem1 eluz ralimdv imp sylan2 rabbi sylib 3adant1 cvv
      ex ovex mzpconstmpt mpan lerabdioph syl3an2 eqeltrd ) DEFZCGFZAGHDIJZKJZB
      LVCMNZFZOBCPNFZAEVCKJZQZCBRSZAVHQZDUBNZVBVFVIVKUAZVAVBVFUCVGVJUDZAVHTZVMV
      FVBBGFZAVHTZVOABDUEVBVQVOVBVPVNAVHVBVPVNCBUFUNUGUHUIVGVJAVHUJUKULVBVAAVDC
      LVEFZVFVKVLFVCUMFVBVRHDIUOACVCUPUQACBDURUSUT $.

    $( Diophantine set builder for positivity.  (Contributed by Stefan O'Rear,
       11-Oct-2014.) $)
    elnnrabdioph $p |- ( ( N e. NN0 /\ ( t e. ( ZZ ^m ( 1 ... N ) ) |-> A ) e.
        ( mzPoly ` ( 1 ... N ) ) ) -> { t e. ( NN0 ^m ( 1 ... N ) ) | A e. NN }
        e. ( Dioph ` N ) ) $=
      ( cn0 wcel cz c1 cfz co cmap cmpt cmzp cfv wa cn cuz cdioph elnnuz rabbii
      crab 1z eluzrabdioph mp3an2 eqeltrid ) CDEZAFGCHIZJIBKUFLMEZNBOEZADUFJIZT
      BGPMEZAUITZCQMZUHUJAUIBRSUEGFEUGUKULEUAABGCUBUCUD $.

    $( Diophantine set builder for the strict less than relation.  (Contributed
       by Stefan O'Rear, 11-Oct-2014.) $)
    ltrabdioph $p |- ( ( N e. NN0 /\ ( t e. ( ZZ ^m ( 1 ... N ) ) |-> A ) e. (
        mzPoly ` ( 1 ... N ) ) /\ ( t e. ( ZZ ^m ( 1 ... N ) ) |-> B ) e. (
        mzPoly ` ( 1 ... N ) ) ) -> { t e. ( NN0 ^m ( 1 ... N ) ) | A < B } e.
        ( Dioph ` N ) ) $=
      ( cn0 wcel cz c1 cfz co cmap cmpt cmzp cfv crab wral rabdiophlem1 3adant1
      w3a wa clt wbr cmin cn cdioph wceq wb znnsub ralimi r19.26 3imtr3i syl2an
      rabbi simp1 mzpsubmpt ancoms elnnrabdioph syl2anc eqeltrd ) DEFZAGHDIJZKJ
      ZBLVAMNZFZAVBCLVCFZSZBCUAUBZAEVAKJZOZCBUCJZUDFZAVHOZDUENZVDVEVIVLUFZUTVDB
      GFZAVHPZCGFZAVHPZVNVEABDQACDQVOVQTZAVHPVGVKUGZAVHPVPVRTVNVSVTAVHBCUHUIVOV
      QAVHUJVGVKAVHUMUKULRVFUTAVBVJLVCFZVLVMFUTVDVEUNVDVEWAUTVEVDWAACBVAUOUPRAV
      JDUQURUS $.

    $( Diophantine set builder for inequality.  This not quite trivial theorem
       touches on something important; Diophantine sets are not closed under
       negation, but they contain an important subclass that is, namely the
       recursive sets.  With this theorem and De Morgan's laws, all
       quantifier-free formulas can be negated.  (Contributed by Stefan O'Rear,
       11-Oct-2014.) $)
    nerabdioph $p |- ( ( N e. NN0 /\ ( t e. ( ZZ ^m ( 1 ... N ) ) |-> A ) e. (
        mzPoly ` ( 1 ... N ) ) /\ ( t e. ( ZZ ^m ( 1 ... N ) ) |-> B ) e. (
        mzPoly ` ( 1 ... N ) ) ) -> { t e. ( NN0 ^m ( 1 ... N ) ) | A =/= B }
        e. ( Dioph ` N ) ) $=
      ( cn0 wcel cz co cmap cmpt cfv crab clt wbr rabdiophlem1 wa cr zre syl2an
      wral c1 cfz cmzp w3a wo cdioph wceq wb lttri2 ralimi r19.26 rabbi 3imtr3i
      wne 3adant1 ltrabdioph 3com23 orrabdioph syl2anc eqeltrd ) DEFZAGUADUBHZI
      HZBJVBUCKZFZAVCCJVDFZUDZBCUNZAEVBIHZLZBCMNZCBMNZUEZAVILZDUFKZVEVFVJVNUGZV
      AVEBGFZAVITZCGFZAVITZVPVFABDOACDOVQVSPZAVITVHVMUHZAVITVRVTPVPWAWBAVIVQBQF
      CQFWBVSBRCRBCUISUJVQVSAVIUKVHVMAVIULUMSUOVGVKAVILVOFVLAVILVOFZVNVOFABCDUP
      VAVFVEWCACBDUPUQVKVLADURUSUT $.
  $}

  ${
    $d N a b c t $.  $d A a b c $.  $d B a b c $.

    $( Divisibility is a Diophantine relation.  (Contributed by Stefan O'Rear,
       11-Oct-2014.) $)
    dvdsrabdioph $p |- ( ( N e. NN0 /\ ( t e. ( ZZ ^m ( 1 ... N ) ) |-> A ) e.
        ( mzPoly ` ( 1 ... N ) ) /\ ( t e. ( ZZ ^m ( 1 ... N ) ) |-> B ) e. (
        mzPoly ` ( 1 ... N ) ) ) -> { t e. ( NN0 ^m ( 1 ... N ) ) | A || B } e.
        ( Dioph ` N ) ) $=
      ( vb va vc cn0 wcel cz c1 co cmap cmpt cfv crab cv cmul wceq nfcv cfz w3a
      cmzp cdvds wbr cneg wo wrex cdioph wral rabdiophlem1 wa wb divides eqeq1d
      oveq1 rexzrexnn0 bitrdi ralimi r19.26 3imtr3i syl2an 3adant1 csb nfv nfov
      rabbi nfcsb1v nfrexw csbeq1a oveq2d eqeq12d orbi12d rexbidv cbvrabw caddc
      nfeq nfor cres simp1 peano2nn0 3ad2ant1 cvv ovex nn0p1nn elfz1end mzpproj
      cn sylib sylancr adantr rabdiophlem2 mzpmulmpt syl2anc 3adant3 eqrabdioph
      eqid 3adant2 syl3anc mzpnegmpt orrabdioph negeq oveq1d csbeq1 rexrabdioph
      syl eqeltrid eqeltrd ) DHIZAJKDUALZMLZBNXJUCOZIZAXKCNXLIZUBZBCUDUEZAHXJML
      ZPZEQZBRLZCSZXSUFZBRLZCSZUGZEHUHZAXQPZDUIOZXMXNXRYGSZXIXMBJIZAXQUJZCJIZAX
      QUJZYIXNABDUKACDUKYJYLULZAXQUJXPYFUMZAXQUJYKYMULYIYNYOAXQYNXPFQZBRLZCSZFJ
      UHYFFBCUNYRYAYDFEYPXSSYQXTCYPXSBRUPUOYPYBSYQYCCYPYBBRUPUOUQURUSYJYLAXQUTX
      PYFAXQVGVAVBVCXOYGXSAYPBVDZRLZAYPCVDZSZYBYSRLZUUASZUGZEHUHZFXQPZYHYFUUFAF
      XQAXQTFXQTYFFVEUUEAEHAHTUUBUUDAAYTUUAAXSYSRAXSTARTZAYPBVHZVFAYPCVHZVQAUUC
      UUAAYBYSRAYBTUUHUUIVFUUJVQVRVIAQYPSZYEUUEEHUUKYAUUBYDUUDUUKXTYTCUUAUUKBYS
      XSRAYPBVJZVKAYPCVJZVLUUKYCUUCCUUAUUKBYSYBRUULVKUUMVLVMVNVOXOXIDKVPLZGQZOZ
      AUUOXJVSZBVDZRLZAUUQCVDZSZUUPUFZUURRLZUUTSZUGZGHKUUNUALZMLZPUUNUIOZIZUUGY
      HIXIXMXNVTXOUVAGUVGPUVHIZUVDGUVGPUVHIZUVIXOUUNHIZGJUVFMLZUUSNUVFUCOZIZGUV
      MUUTNUVNIZUVJXIXMUVLXNDWAWBZXIXMUVOXNXIXMULZGUVMUUPNUVNIZGUVMUURNUVNIZUVO
      XIUVSXMXIUVFWCIUUNUVFIZUVSKUUNUAWDXIUUNWHIUWADWEUUNWFWIGUVFUUNWGWJWKZAGBU
      UNDUUNWQZWLZGUUPUURUVFWMWNWOXIXNUVPXMAGCUUNDUWCWLWRZGUUSUUTUUNWPWSXOUVLGU
      VMUVCNUVNIZUVPUVKUVQXIXMUWFXNUVRGUVMUVBNUVNIZUVTUWFUVRUVSUWGUWBGUUPUVFWTX
      FUWDGUVBUURUVFWMWNWOUWEGUVCUUTUUNWPWSUVAUVDGUUNXAWNUVEUUEUUPYSRLZUUASZUVB
      YSRLZUUASZUGEFGUUNDUWCXSUUPSZUUBUWIUUDUWKUWLYTUWHUUAXSUUPYSRUPUOUWLUUCUWJ
      UUAUWLYBUVBYSRXSUUPXBXCUOVMYPUUQSZUWIUVAUWKUVDUWMUWHUUSUUAUUTUWMYSUURUUPR
      AYPUUQBXDZVKAYPUUQCXDZVLUWMUWJUVCUUAUUTUWMYSUURUVBRUWNVKUWOVLVMXEWNXGXH
      $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Diophantine sets 6: reusability.  renumbering of variables
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d W a b p u t w $.  $d S a b p u t w $.  $d N a b p u t w $.
    $d P a b p u t w $.
    eldioph4b.a $e |- W e. _V $.
    eldioph4b.b $e |- -. W e. Fin $.
    eldioph4b.c $e |- ( W i^i NN ) = (/) $.
    $( Membership in ` Dioph ` expressed using a quantified union to add
       witness variables instead of a restriction to remove them.  (Contributed
       by Stefan O'Rear, 16-Oct-2014.) $)
    eldioph4b $p |- ( S e. ( Dioph ` N ) <-> ( N e. NN0 /\ E. p e. ( mzPoly ` (
        W u. ( 1 ... N ) ) ) S = { t e. ( NN0 ^m ( 1 ... N ) ) | E. w e. ( NN0
        ^m W ) ( p ` ( t u. w ) ) = 0 } ) ) $=
      ( vu cfv wcel cn0 cun cc0 wceq wrex cres wa c0 cdioph cv cmap co cfz crab
      c1 cmzp eldiophelnn0 cab cvv cfn wn wb ovex unex jctr intnanr unfir ssun2
      wss pm3.2i eldioph2b sylancl elmapssres mpan2 adantr ssun1 resundi eqtr4i
      mto uncom wf wfn elmapi fnresdm 3syl eqtrid fveqeq2d biimpar uneq2 rspcev
      ffn syl2anc jca eleq1 rexbidv anbi12d syl5ibrcom expimpd ancomsd rexlimiv
      uneq1 cin fz1ssnn sslin ax-mp sseqtri ss0 reseq2i res0 elmapresaun mp3an3
      eqtri ancoms eqeltrid reseq1i elmapresaunres2 eqtr2id simpr reseq1 eqeq2d
      cn fveqeq2 syl12anc r19.29an impbii df-rab eqeq2i rexbii bitrdi biadanii
      abbii ) CDUAKLZDMLZCBUBZAUBZNZFUBZKOPZAMEUCUDZQZBMUGDUEUDZUCUDZUFZPZFEYMN
      ZUHKZQZCDUIYEYDCYFJUBZYMRZPZYTYIKOPZSZJMYQUCUDZQZBUJZPZFYRQZYSYEYEYQUKLZS
      YQULLZUMZYMYQVAZSYDUUIUNYEUUJEYMGUGDUEUOUPUQUULUUMUUKEULLZYMULLZSUUNUUOHU
      REYMUSVKYMEUTZVBJBCYQDFVCVDUUHYPFYRUUGYOCUUGYFYNLZYLSZBUJYOUUFUURBUUFUURU
      UDUURJUUEYTUUELZUUCUUBUURUUSUUCUUBUURUUSUUCSZUURUUBUUAYNLZUUAYGNZYIKOPZAY
      KQZSUUTUVAUVDUUSUVAUUCUUSUUMUVAUUPYTMYQYMVEVFVGUUTYTERZYKLZUUAUVENZYIKOPZ
      UVDUUSUVFUUCUUSEYQVAUVFEYMVHYTMYQEVEVFVGUUSUVHUUCUUSUVGYTOYIUUSUVGYTYQRZY
      TUVGUVEUUANUVIUUAUVEVLYTEYMVIVJUUSYQMYTVMYTYQVNUVIYTPYTMYQVOYQMYTWCYQYTVP
      VQVRVSVTUVCUVHAUVEYKYGUVEPUVBUVGOYIYGUVEUUAWAVSWBWDWEUUBUUQUVAYLUVDYFUUAY
      NWFUUBYJUVCAYKUUBYHUVBOYIYFUUAYGWMVSWGWHWIWJWKWLUUQYJUUFAYKUUQYGYKLZSZYJS
      YHUUELZYFYHYMRZPZYJUUFUVKUVLYJUVKYHYGYFNZUUEYFYGVLZUVJUUQUVOUUELZUVJUUQYG
      EYMWNZRZYFUVRRZPZUVQUVSTUVTUVSYGTRTUVRTYGUVRTVAUVRTPUVREXMWNZTYMXMVAUVRUW
      BVADWOYMXMEWPWQIWRUVRWSWQZWTYGXAXDUVTYFTRTUVRTYFUWCWTYFXAXDVJZEYMMYGYFXBX
      CXEXFVGUVKUVNYJUVKUVMUVOYMRZYFYHUVOYMUVPXGUVJUUQUWEYFPZUVJUUQUWAUWFUWDEYM
      MYGYFXHXCXEXIVGUVKYJXJUUDUVNYJSJYHUUEYTYHPZUUBUVNUUCYJUWGUUAUVMYFYTYHYMXK
      XLYTYHOYIXNWHWBXOXPXQYCYLBYNXRVJXSXTYAYB $.

    $( Forward-only version of ~ eldioph4b .  (Contributed by Stefan O'Rear,
       16-Oct-2014.) $)
    eldioph4i $p |- ( ( N e. NN0 /\ P e. ( mzPoly ` ( W u. ( 1 ... N ) ) ) ) ->
        { t e. ( NN0 ^m ( 1 ... N ) ) | E. w e. ( NN0 ^m W ) ( P ` ( t u. w ) )
        = 0 } e. ( Dioph ` N ) ) $=
      ( va vb vp cn0 wcel co cun cfv cv cc0 wceq wrex cfz cmzp cmap crab cdioph
      c1 weq uneq1 fveqeq2d rexbidv uneq2 cbvrexvw bitrdi cbvrabv fveq1 rabbidv
      wa eqeq1d rspceeqv mpan2 anim2i eldioph4b sylibr ) DLMZCEUFDUANZOUBPZMZUQ
      VDBQZAQZOZCPRSZALEUCNZTZBLVEUCNZUDZIQZJQZOZKQZPZRSZJVLTZIVNUDZSKVFTZUQVOD
      UEPMVGWDVDVGVOVRCPZRSZJVLTZIVNUDZSWDVMWGBIVNBIUGZVMVPVIOZCPRSZAVLTWGWIVKW
      KAVLWIVJWJRCVHVPVIUHUIUJWKWFAJVLAJUGWJVRRCVIVQVPUKUIULUMUNKCVFWCWHVOVSCSZ
      WBWGIVNWLWAWFJVLWLVTWERVRVSCUOURUJUPUSUTVAJIVODEKFGHVBVC $.
  $}

  ${
    $d S a b c d e $.  $d M a b c d e $.  $d N a b c d e $.  $d F a b c d e $.
    $( Change variables in a Diophantine set, using class notation.  This
       allows already proved Diophantine sets to be reused in contexts with
       more variables.  (Contributed by Stefan O'Rear, 16-Oct-2014.)  (Revised
       by Stefan O'Rear, 5-Jun-2015.) $)
    diophren $p |- ( ( S e. ( Dioph ` N ) /\ M e. NN0 /\
          F : ( 1 ... N ) --> ( 1 ... M ) ) ->
        { a e. ( NN0 ^m ( 1 ... M ) ) | ( a o. F ) e. S } e. ( Dioph ` M ) ) $=
      ( vd cfv wcel cn0 c1 co ccom cmap wa cun cc0 wceq cz cn c0 vc vb ve wf cv
      cdioph cfz crab cdif wrex cmzp cvv zex difexg ax-mp cfn com ominf cen wbr
      wb caddc nnuz 0p1e1 fveq2i eqtr4i difeq2i 0z lzenom eqbrtri enfi disjdifr
      cuz mtbir eldioph4b cid cres cmpt simpr simp-4r ovex mapco2 syl2anc uneq1
      fveqeq2d rexbidv elrab3 syl simp-5r simplr coundi coundir elmapi 3ad2ant3
      w3a cin simp1 incom wss fz1ssnn disjdif ssdisj mp2an eqtri coeq0i syl3anc
      a1i uneq2d eqtrid un0 3ad2ant2 wf1o f1oi f1of mp3an23 coires1 wfn fnresdm
      eqtrdi 3syl uneq12d uncom eqtr2id fveq2d nn0ssz mapss reseq2i elmapresaun
      res0 oveq2i eleqtrdi mp3an3 sselid adantll coeq1 eqid fvex fvmpt eqtr4d
      ffn eqeq1d rexbidva bitrd rabbidva simplll id fun syl21anc feq1i ad3antlr
      unex sylib mzprename eldioph4i eqeltrd eleq2 rabbidv syl5ibrcom rexlimdva
      eleq1d expimpd biimtrid impcom 3impb ) ADUFGHZCIHZJDUGKZJCUGKZBUDZEUEZBLZ
      AHZEIUVHMKZUHZCUFGZHZUVFUVINZUVEUVPUVEDIHZAUAUEZFUEZOZUBUEZGPQZFIRSUIZMKZ
      UJZUAIUVGMKZUHZQZUBUWDUVGOZUKGZUJZNUVQUVPFUAADUWDUBRULHZUWDULHUMRSULUNUOZ
      UWDUPHZUQUPHZURUWDUQUSUTUWOUWPVAUWDRPJVBKZVMGZUIZUQUSSUWRRSJVMGUWRVCUWQJV
      MVDVEVFVGPRHUWSUQUSUTVHPVIUOVJUWDUQVKUOVNZSRVLZVOUVQUVRUWLUVPUVQUVRNZUWIU
      VPUBUWKUXBUWBUWKHZNZUVPUWIUVKUWHHZEUVMUHZUVOHUXDUXFUVJUVTOZUCRUWDUVHOZMKZ
      UCUEZBVPUWDVQZOZLZUWBGZVRZGZPQZFUWEUJZEUVMUHZUVOUXDUXEUXREUVMUXDUVJUVMHZN
      ZUXEUVKUVTOZUWBGZPQZFUWEUJZUXRUYAUVKUWGHZUXEUYEVAUYAUXTUVIUYFUXDUXTVSUVFU
      VIUVRUXCUXTVTUVJIUVHBUVGJDUGWAWBWCUWFUYEUAUVKUWGUVSUVKQZUWCUYDFUWEUYGUWAU
      YBPUWBUVSUVKUVTWDWEWFWGWHUYAUYDUXQFUWEUYAUVTUWEHZNZUYCUXPPUYIUYCUXGUXLLZU
      WBGZUXPUYIUYBUYJUWBUYIUVIUXTUYHUYBUYJQUVFUVIUVRUXCUXTUYHWIUXDUXTUYHWJUYAU
      YHVSUVIUXTUYHWOZUYJUXGBLZUXGUXKLZOUYBUXGBUXKWKUYLUYMUVKUYNUVTUYLUYMUVKTOZ
      UVKUYLUYMUVKUVTBLZOUYOUVJUVTBWLUYLUYPTUVKUYLUWDIUVTUDZUVIUWDUVHWPZTQZUYPT
      QUYHUVIUYQUXTUVTIUWDWMZWNUVIUXTUYHWQUYSUYLUYRUVHUWDWPZTUWDUVHWRUVHSWSSUWD
      WPTQZVUATQZCWTSRXAZUVHSUWDXBXCZXDXGUVTBUWDIUVGUVHXEXFXHXIUVKXJXSUYLUYNTUV
      TOZUVTUYLUYNUVJUXKLZUVTUXKLZOVUFUVJUVTUXKWLUYLVUGTVUHUVTUYLUVHIUVJUDZVUGT
      QZUXTUVIVUIUYHUVJIUVHWMXKVUIUWDUWDUXKUDZVUCVUJUWDUWDUXKXLVUKUWDXMUWDUWDUX
      KXNUOZVUEUVJUXKUVHIUWDUWDXEXOWHUYHUVIVUHUVTQUXTUYHVUHUVTUWDVQZUVTUVTUWDXP
      UYHUYQUVTUWDXQVUMUVTQUYTUWDIUVTYTUWDUVTXRXTXIWNYAXIVUFUVTTOUVTTUVTYBUVTXJ
      XDXSYAYCXFYDUYIUXGUXIHZUXPUYKQUXTUYHVUNUXDUXTUYHNIUXHMKZUXIUXGUWMIRWSVUOU
      XIWSUMYEIRUXHULYFXCUXTUYHUVJVUAVQZUVTVUAVQZQZUXGVUOHVUPTVUQVUPUVJTVQTVUAT
      UVJVUEYGUVJYIXDVUQUVTTVQTVUATUVTVUEYGUVTYIXDVFUXTUYHVURWOUXGIUVHUWDOZMKVU
      OUVHUWDIUVJUVTYHVUSUXHIMUVHUWDYBYJYKYLYMYNUCUXGUXNUYKUXIUXOUXJUXGQUXMUYJU
      WBUXJUXGUXLYOYDUXOYPUYJUWBYQYRWHYSUUAUUBUUCUUDUXDUVFUXOUXHUKGHZUXSUVOHUVF
      UVIUVRUXCUUEUXDUXHULHZUXCUWJUXHUXLUDZVUTVVAUXDUWDUVHUWNJCUGWAUUKXGUXBUXCV
      SUVIVVBUVFUVRUXCUVIUWJUXHUXKBOZUDZVVBUVIVUKUVIUWDUVGWPZTQZVVDVUKUVIVULXGU
      VIUUFVVFUVIVVEUVGUWDWPZTUWDUVGWRUVGSWSVUBVVGTQDWTVUDUVGSUWDXBXCXDXGUWDUVG
      UWDUVHUXKBUUGUUHUWJUXHVVCUXLUXKBYBUUIUULUUJUCUXLUWBUWJUXHUUMXFFEUXOCUWDUW
      NUWTUXAUUNWCUUOUWIUVNUXFUVOUWIUVLUXEEUVMAUWHUVKUUPUUQUUTUURUUSUVAUVBUVCUV
      D $.
  $}

  ${
    $d ph b $.  $d A a b $.  $d B a b $.  $d F a b $.
    $( Change variable numbers in a Diophantine class abstraction using
       explicit substitution.  (Contributed by Stefan O'Rear, 17-Oct-2014.) $)
    rabrenfdioph $p |- ( ( B e. NN0 /\ F : ( 1 ... A ) --> ( 1 ... B ) /\
          { a e. ( NN0 ^m ( 1 ... A ) ) | ph } e. ( Dioph ` A ) ) ->
        { b e. ( NN0 ^m ( 1 ... B ) ) | [. ( b o. F ) / a ]. ph } e.
          ( Dioph ` B ) ) $=
      ( cn0 wcel c1 cfz co wf cmap crab cdioph cfv w3a cv ccom wa simplr mapco2
      wsbc wceq simpr ovex syl2anc biantrurd nfcv elrabsf bitr4di 3adant3 3coml
      rabbidva diophren eqeltrd ) CGHZIBJKZICJKZDLZAEGURMKZNZBOPHZQAEFRZDSZUCZF
      GUSMKZNZVEVBHZFVGNZCOPZUQUTVHVJUDVCUQUTTZVFVIFVGVLVDVGHZTZVFVEVAHZVFTVIVN
      VOVFVNVMUTVOVLVMUEUQUTVMUAVDGUSDURIBJUFUBUGUHAEVEVAEVAUIUJUKUNULVCUQUTVJV
      KHVBDCBFUOUMUP $.
  $}

  ${
    $d ps a $.  $d ph b $.  $d X a b $.  $d Y a b $.  $d Z a b $.  $d N a b $.
    rabren3dioph.a $e |- ( ( ( a ` 1 ) = ( b ` X ) /\ ( a ` 2 ) = ( b ` Y ) /\
      ( a ` 3 ) = ( b ` Z ) ) -> ( ph <-> ps ) ) $.
    rabren3dioph.b $e |- X e. ( 1 ... N ) $.
    rabren3dioph.c $e |- Y e. ( 1 ... N ) $.
    rabren3dioph.d $e |- Z e. ( 1 ... N ) $.
    $( Change variable numbers in a 3-variable Diophantine class abstraction.
       (Contributed by Stefan O'Rear, 17-Oct-2014.) $)
    rabren3dioph $p |- ( ( N e. NN0 /\ { a e. ( NN0 ^m ( 1 ... 3 ) ) | ph } e.
        ( Dioph ` 3 ) ) -> { b e. ( NN0 ^m ( 1 ... N ) ) | ps } e.
        ( Dioph ` N ) ) $=
      ( wcel c1 c3 co cfv c2 wceq mp2an cn0 cfz cmap crab cdioph wa cv cop ccom
      ctp wsbc vex tpex coex w3a wb wfn wne 1ne2 1re 1lt3 ltneii 2re 2lt3 elexi
      1ex 2ex fntp mp3an tpid1 fvco2 fvtp1 fveq2i eqtri tpid2 fvtp2 tpid3 fvtp3
      3ex 3pm3.2i fveq1 eqeq1d 3anbi123d mpbiri syl sbcie rabbii wf caddc cz 1z
      wss ftp fztp ax-mp 1p2e3 oveq2i eqidd 1p1e2 a1i tpeq123d feq2i mpbir tpss
      3eqtr3i mpbi fss rabrenfdioph mp3an2 eqeltrrid ) CUAMZAGUANOUBPZUCPUDOUEQ
      MZUFBHUANCUBPZUCPZUDAGHUGZNDUHZREUHZOFUHZUJZUIZUKZHXOUDZCUEQZYBBHXOABGYAX
      PXTHULXQXRXSUMUNGUGZYASZNYEQZDXPQZSZRYEQZEXPQZSZOYEQZFXPQZSZUOZABUPYFYPNY
      AQZYHSZRYAQZYKSZOYAQZYNSZUOYRYTUUBYQNXTQZXPQZYHXTNROUJZUQZNUUEMYQUUDSNRUR
      ZNOURZROURZUUFUSNOUTVAVBZROVCVDVBZNRODEFVFVGVSDXNJVEZEXNKVEZFXNLVEZVHVIZN
      ROVFVJUUEXPXTNVKTUUCDXPUUGUUHUUCDSUSUUJNRODEFVFUULVLTVMVNYSRXTQZXPQZYKUUF
      RUUEMYSUUQSUUONROVGVOUUEXPXTRVKTUUPEXPUUGUUIUUPESUSUUKNRODEFVGUUMVPTVMVNU
      UAOXTQZXPQZYNUUFOUUEMUUAUUSSUUONROVSVQUUEXPXTOVKTUURFXPUUHUUIUURFSUUJUUKN
      RODEFVSUUNVRTVMVNVTYFYIYRYLYTYOUUBYFYGYQYHNYEYAWAWBYFYJYSYKRYEYAWAWBYFYMU
      UAYNOYEYAWAWBWCWDIWEWFWGXKXLXNXTWHZXMYCYDMXLDEFUJZXTWHZUVAXNWLZUUTUVBUUEU
      VAXTWHNRODEFVFVGVSUULUUMUUNUSUUJUUKWMXLUUEUVAXTNNRWIPZUBPZNNNWIPZUVDUJZXL
      UUENWJMZUVEUVGSWKNWNWOUVDONUBWPWQUVHUVGUUESWKUVHNNUVFRUVDOUVHNWRUVFRSUVHW
      SWTUVDOSUVHWPWTXAWOXEXBXCDXNMZEXNMZFXNMZUOUVCUVIUVJUVKJKLVTDEFXNUULUUMUUN
      XDXFXLUVAXNXTXGTAOCXTGHXHXIXJ $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Pigeonhole Principle and cardinality helpers
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d A x y a b $.  $d B x y a b $.  $d C y a b $.  $d D x a b $.
    $d ph x y a b $.
    fphpd.a $e |- ( ph -> B ~< A ) $.
    fphpd.b $e |- ( ( ph /\ x e. A ) -> C e. B ) $.
    fphpd.c $e |- ( x = y -> C = D ) $.
    $( Pigeonhole principle expressed with implicit substitution.  If the range
       is smaller than the domain, two inputs must be mapped to the same
       output.  (Contributed by Stefan O'Rear, 19-Oct-2014.)  (Revised by
       Stefan O'Rear, 6-May-2015.) $)
    fphpd $p |- ( ph -> E. x e. A E. y e. A ( x =/= y /\ C = D ) ) $=
      ( va wceq cv wi wral wn wa wrex wcel csb vb wne cdom wbr csdm domnsym cvv
      nsyl3 relsdom brrelex1i syl adantr nfv nfcsb1v nfim eleq1w anbi2d csbeq1a
      nfel1 eleq1d imbi12d chvarfv ex wb csbid vex csbie eqeq12i imbi1i 2ralbii
      nfeq csbeq1 eqeq1d equequ1 eqeq2d equequ2 rspc2 com12 sylbir impbid1 syl6
      id adantl dom2d mpd mtand ancom df-ne anbi1i pm4.61 3bitr4i rexbii rexnal
      bitri sylibr ) AFGLZBMZCMZLZNZCDOZBDOZPZWQWRUBZWPQZCDRZBDRZAXBDEUCUDZXHED
      UEUDZADEUFHUHAXBQZEUGSZXHAXKXBAXIXKHEDUEUIUJUKULXJKUADEBKMZFTZBUAMZFTZUGA
      XLDSZXMESZNXBAXPXQAWQDSZQZFESZNAXPQZXQNBKYAXQBYABUMBXMEBXLFUNZUSUOWQXLLZX
      SYAXTXQYCXRXPABKDUPUQYCFXMEBXLFURUTVAIVBVCULXBXPXNDSQZXMXOLZXLXNLZVDZNAXB
      YDYEYFNZYGXBBWQFTZBWRFTZLZWSNZCDOBDOZYDYHNYLWTBCDDYKWPWSYIFYJGBFVEBWRFGCV
      FJVGVHVIVJYDYMYHYLYHXMYJLZXLWRLZNBCXLXNDDYNYOBBXMYJYBBWRFUNVKYOBUMUOYHCUM
      YCYKYNWSYOYCYIXMYJBWQXLFVLVMBKCVNVAWRXNLZYNYEYOYFYPYJXOXMBWRXNFVLVOCUAKVP
      VAVQVRVSYHYEYFYHWBBXLXNFVLVTWAWCWDWEWFXGXAPZBDRXCXFYQBDXFWTPZCDRYQXEYRCDW
      SPZWPQWPYSQXEYRYSWPWGXDYSWPWQWRWHWIWPWSWJWKWLWTCDWMWNWLXABDWMWNWO $.
  $}

  ${
    $d ph x y z b c $.  $d A x y z b c $.  $d B z b c $.  $d C x y b c $.
    $d D y z b c $.  $d E x z b c $.
    fphpdo.1 $e |- ( ph -> A C_ RR ) $.
    fphpdo.2 $e |- ( ph -> B e. _V ) $.
    fphpdo.3 $e |- ( ph -> B ~< A ) $.
    fphpdo.4 $e |- ( ( ph /\ z e. A ) -> C e. B ) $.
    fphpdo.5 $e |- ( z = x -> C = D ) $.
    fphpdo.6 $e |- ( z = y -> C = E ) $.
    $( Pigeonhole principle for sets of real numbers with implicit output
       reordering.  (Contributed by Stefan O'Rear, 12-Sep-2014.) $)
    fphpdo $p |- ( ph -> E. x e. A E. y e. A ( x < y /\ D = E ) ) $=
      ( vb vc wa clt wcel cv wne cmpt cfv wceq wrex wbr fmpttd ffvelcdmda fveq2
      fphpd sselda adantrr adantr adantrl lttri2d simprl ad2antrr simprr simplr
      wo cr simpr weq breq1 fveqeq2 anbi12d breq2 eqeq2d rspc2ev syl112anc jaod
      ex eqcomd wi eleq1w anbi2d eleq1d imbi12d chvarvv fvmptd3 adantlr eqeq12d
      eqid biimpd anim2d reximdva syld sylbid expimpd ancomsd rexlimdvva mpd )
      APUAZQUAZUBZWNDEGUCZUDZWOWQUDZUEZRZQEUFPEUFBUAZCUAZSUGZHIUEZRZCEUFZBEUFZA
      PQEFWRWSLAEFWNWQADEGFMUHUIWNWOWQUJUKAXAXHPQEEAWNETZWOETZRZRZWTWPXHXLWTWPX
      HXLWTRZWPWNWOSUGZWOWNSUGZVAZXHXMWNWOXLWNVBTZWTAXIXQXJAEVBWNJULUMUNXLWOVBT
      ZWTAXJXRXIAEVBWOJULUOUNUPXMXPXDXBWQUDZXCWQUDZUEZRZCEUFZBEUFZXHXMXNYDXOXMX
      NYDXMXNRXIXJXNWTYDXLXIWTXNAXIXJUQZURXLXJWTXNAXIXJUSZURXMXNVCXLWTXNUTYBXNW
      TRWNXCSUGZWRXTUEZRBCWNWOEEBPVDXDYGYAYHXBWNXCSVEXBWNXTWQVFVGCQVDZYGXNYHWTX
      CWOWNSVHYIXTWSWRXCWOWQUJVIVGVJVKVMXMXOYDXMXORZXJXIXOWSWRUEZYDXLXJWTXOYFUR
      XLXIWTXOYEURXMXOVCYJWRWSXLWTXOUTVNYBXOYKRWOXCSUGZWSXTUEZRBCWOWNEEBQVDXDYL
      YAYMXBWOXCSVEXBWOXTWQVFVGCPVDZYLXOYMYKXCWNWOSVHYNXTWRWSXCWNWQUJVIVGVJVKVM
      VLAYDXHVOXKWTAYCXGBEAXBETZRZYBXFCEYPXCETZRZYAXEXDYRYAXEYRXSHXTIYRDXBGHEWQ
      FWQWDZNAYOYQUTYPHFTZYQADUAETZRZGFTZVOZYPYTVODBDBVDZUUBYPUUCYTUUEUUAYOADBE
      VPVQUUEGHFNVRVSMVTUNWAYRDXCGIEWQFYSOYPYQVCAYQIFTZYOUUDAYQRZUUFVODCDCVDZUU
      BUUGUUCUUFUUHUUAYQADCEVPVQUUHGIFOVRVSMVTWBWAWCWEWFWGWGURWHWIWJWKWLWM $.
  $}

  $( An infinite subset of a countable set is countable, without using choice.
     (Contributed by Stefan O'Rear, 19-Oct-2014.)  (Revised by Stefan O'Rear,
     6-May-2015.) $)
  ctbnfien $p |- ( ( ( X ~~ _om /\ Y ~~ _om ) /\
        ( A C_ X /\ -. A e. Fin ) ) -> A ~~ Y ) $=
    ( com cen wbr wa wss cfn wcel wn csdm isfinite notbii wo cdom cvv brrelex1i
    wi relen ssdomg syl domen2 sylibd imp brdom2 sylib adantlr biimtrid impr wb
    ord enen2 ad2antlr mpbird ) BDEFZCDEFZGZABHZAIJZKZGZGACEFZADEFZURUSVAVDVAAD
    LFZKURUSGZVDUTVEAMNVFVEVDUPUSVEVDOZUQUPUSGADPFZVGUPUSVHUPUSABPFZVHUPBQJUSVI
    SBDETRABQUAUBBDAUCUDUEADUFUGUHULUIUJUQVCVDUKUPVBCDAUMUNUO $.

  ${
    $d A x y $.  $d ph x y $.  $d B x y $.  $d D y $.
    fiphp3d.a $e |- ( ph -> A ~~ NN ) $.
    fiphp3d.b $e |- ( ph -> B e. Fin ) $.
    fiphp3d.c $e |- ( ( ph /\ x e. A ) -> D e. B ) $.
    $( Infinite pigeonhole principle for partitioning an infinite set between
       finitely many buckets.  (Contributed by Stefan O'Rear, 18-Oct-2014.) $)
    fiphp3d $p |- ( ph -> E. y e. B { x e. A | D = y } ~~ NN ) $=
      ( cv wceq crab cfn wcel wrex cn cen wbr com wa wn wral ciun iunrab risset
      ominf eqcom rexbii bitri ralrimiva rabid2 sylibr eqtr4id eleq1d wb nnenom
      sylib entr sylancl syl bitrd mtbiri iunfi sylan mtand rexnal jctir ssrab2
      enfi wss jctl ctbnfien syl2an ex reximdv mpd ) AFCJZKZBDLZMNZUAZCEOZVSPQR
      ZCEOAVTCEUBZUAWBAWDCEVSUCZMNZAWFSMNZUFAWFDMNZWGAWEDMAWEVRCEOZBDLZDVRCBEDU
      DAWIBDUBDWJKAWIBDABJDNTFENZWIIWKVQFKZCEOWICFEUEWLVRCEVQFUGUHUIUQUJWIBDUKU
      LUMUNADSQRZWHWGUOADPQRPSQRZWMGUPDPSURUSZDSVIUTVAVBAEMNWDWFHCEVSVCVDVEVTCE
      VFULAWAWCCEAWAWCAWMWNTVSDVJZWATWCWAAWMWNWOUPVGWAWPVRBDVHVKVSDPVLVMVNVOVP
      $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  A non-closed set of reals is infinite
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d A a b c d x y $.  $d B a b c d x y $.
    $( Lemma for ~ rencldnfi .  (Contributed by Stefan O'Rear, 18-Oct-2014.) $)
    rencldnfilem $p |- ( ( ( A C_ RR /\ B e. RR /\ ( A =/= (/) /\ -. B e. A ) )
        /\ A. x e. RR+ E. y e. A ( abs ` ( y - B ) ) < x ) -> -. A e. Fin ) $=
      ( va vb vc vd cr wss wcel wn wa cv clt wbr wrex crp wral wceq c0 wne cmin
      w3a co cabs cfv cfn wi crab ccnv eqeq1 rexbidv elrab simp-4l simpr sseldd
      csup recnd simp-4r subcld cc0 simprr ad2antrr nelneq syl2anc cc wb subeq0
      necon3abid mpbird absrpcld eleq1 syl5ibrcom expimpd biimtrid ssrdv adantr
      rexlimdva cab abrexfi rabssab ssfi sylancl adantl simplrl n0 sylib abscld
      wex eqid fvoveq1 rspceeqv mpan2 sylanbrc ne0d exlimddv ssrab2 a1i fisupcl
      wor gtso mpan syl3anc cle cinf mp2 fisupg elrabi vex brcnv notbii biimprd
      soss lenlt adantll sylan2 ralimdva adantrd reximdva lbinfle df-inf eqcomi
      mpd breq1i sylibr sselid lenltd mpbid notbid ralbidv rspcev ralnex rexbii
      ralrimiva breq2 rexnal bitri ex 3impa con2d imp ) CIJZDIKZCUAUBZDCKLZMZUD
      ZBNZDUCUEZUFUGZANZOPZBCQZARSZCUHKZLUUHUUPUUOUUCUUDUUGUUPUUOLZUIUUCUUDMZUU
      GMZUUPUUQUUSUUPMZUUMLZBCSZARQZUUQUUTENZFNZDUCUEZUFUGZTZFCQZEIUJZIOUKZURZR
      KUUKUVLOPZLZBCSZUVCUUTUVJRUVLUUSUVJRJUUPUUSGUVJRGNZUVJKZUVPIKZUVPUVGTZFCQ
      ZMUUSUVPRKZUVIUVTEUVPIUVDUVPTUVHUVSFCUVDUVPUVGULUMUNUUSUVRUVTUWAUUSUVRMZU
      VSUWAFCUWBUVECKZMZUWAUVSUVGRKUWDUVFUWDUVEDUWDUVEUWDCIUVEUUCUUDUUGUVRUWCUO
      UWBUWCUPZUQUSZUWDDUUCUUDUUGUVRUWCUTUSZVAUWDUVFVBUBZUVEDTZLZUWDUWCUUFUWJUW
      EUUSUUFUVRUWCUURUUEUUFVCVDUVEDCVEVFUWDUVEVGKZDVGKZUWHUWJVHUWFUWGUWKUWLMUW
      IUVFVBUVEDVIVJVFVKVLUVPUVGRVMVNVSVOVPVQVRUUTUVJUHKZUVJUAUBZUVJIJZUVLUVJKZ
      UUPUWMUUSUUPUVIEVTZUHKUVJUWQJUWMFECUVGWAUVIEIWBUWQUVJWCWDWEZUUTUUICKZUWNB
      UUTUUEUWSBWJUURUUEUUFUUPWFBCWGWHUUTUWSMZUVJUUKUWTUUKIKUUKUVGTZFCQZUUKUVJK
      ZUWTUUJUWTUUIDUWTUUIUWTCIUUIUUCUUDUUGUUPUWSUOUUTUWSUPUQUSUWTDUUCUUDUUGUUP
      UWSUTUSVAWIZUWSUXBUUTUWSUUKUUKTUXBUUKWKFUUICUVGUUKUUKUVEUUIDUFUCWLWMWNWEU
      VIUXBEUUKIUVDUUKTUVHUXAFCUVDUUKUVGULUMUNWOZWPWQZUWOUUTUVIEIWRZWSIUVKXAZUW
      MUWNUWOUDUWPXBIUVJUVKWTXCXDZUQUUTUVNBCUWTUVLUUKXEPZUVNUWTUVJIOXFZUUKXEPZU
      XJUWTUWOUVPHNZXEPZHUVJSZGUVJQZUXCUXLUWOUWTUXGWSUUTUXPUWSUUTUVPUXMUVKPZLZH
      UVJSZUXMUVPUVKPUXMUULUVKPAUVJQUIHUVJSZMZGUVJQZUXPUUTUVJUVKXAZUWMUWNUYBUYC
      UUTUWOUXHUYCUXGXBUVJIUVKXNXGWSUWRUXFGHAUVJUVKXHXDUUTUYAUXOGUVJUVQUUTUVRUY
      AUXOUIUVIEUVPIXIUUTUVRMZUXSUXOUXTUYDUXRUXNHUVJUXMUVJKUYDUXMIKZUXRUXNUIZUV
      IEUXMIXIUVRUYEUYFUUTUXRUXMUVPOPZLZUVRUYEMZUXNUXQUYGUVPUXMOGXJHXJXKXLUYIUX
      NUYHUVPUXMXOXMVPXPXQXRXSXQXTYDVRUXEGHUUKUVJYAXDUVLUXKUUKXEUXKUVLUVJIOYBYC
      YEYFUWTUVLUUKUUTUVLIKUWSUUTUVJIUVLUXGUXIYGVRUXDYHYIYOUVBUVOAUVLRUULUVLTZU
      VAUVNBCUYJUUMUVMUULUVLUUKOYPYJYKYLVFUVCUUNLZARQUUQUVBUYKARUUMBCYMYNUUNARY
      QYRWHYSYTUUAUUB $.

    $( A set of real numbers which comes arbitrarily close to some target yet
       excludes it is infinite.  The work is done in ~ rencldnfilem using
       infima; this theorem removes the requirement that A be nonempty.
       (Contributed by Stefan O'Rear, 19-Oct-2014.) $)
    rencldnfi $p |- ( ( ( A C_ RR /\ B e. RR /\ -. B e. A ) /\ A. x e. RR+ E. y
        e. A ( abs ` ( y - B ) ) < x ) -> -. A e. Fin ) $=
      ( cr wss wcel wn w3a cv cmin co cabs cfv crp wral wa c0 wne c1 clt simpl1
      wbr wrex cfn simpl2 ralimi wb 1rp ne0i r19.3rzv mp2b sylibr adantl simpl3
      rexn0 jca simpr rencldnfilem syl31anc ) CEFZDEGZDCGHZIZBJDKLMNAJUAUCZBCUD
      ZAOPZQZVAVBCRSZVCQVGCUEGHVAVBVCVGUBVAVBVCVGUFVHVIVCVGVIVDVGVIAOPZVIVFVIAO
      VEBCUPUGTOGORSVIVJUHUIOTUJVIAOUKULUMUNVAVBVCVGUOUQVDVGURABCDUSUT $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Lagrange's rational approximation theorem
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x a b $.  $d A a b x y $.  $d B a b x y $.
    $( Lemma for ~ irrapx1 .  Divides the unit interval into ` B ` half-open
       sections and using the pigeonhole principle ~ fphpdo finds two multiples
       of ` A ` in the same section mod 1.  (Contributed by Stefan O'Rear,
       12-Sep-2014.) $)
    irrapxlem1 $p |- ( ( A e. RR+ /\ B e. NN ) -> E. x e. ( 0 ... B ) E. y e. (
        0 ... B ) ( x < y /\ ( |_ ` ( B x. ( ( A x. x ) mod 1 ) ) ) = ( |_ ` (
        B x. ( ( A x. y ) mod 1 ) ) ) ) ) $=
      ( wcel cc0 co c1 cmul cmo cfl cfv cr clt wbr adantl cle ad2antlr sylancl
      cz va crp cn wa cfz cmin cv wss cuz fzssuz uzssz zssre sstri a1i csdm cn0
      ovexd nnm1nn0 nn0uz eleqtrdi nnz nnre ltm1d fzsdom2 syl21anc rpre elfzelz
      ad2antrr zred remulcld 1rp modcl flcld wn recnd mul01d modge0 0red lemul2
      wb nngt0 syl112anc mpbid eqbrtrrd lenltd fllt mtbid mpbird sylanbrc caddc
      0z elnn0z flle syl modlt 1red ltmul2 mulridd breqtrd lelttrd wceq cc nncn
      ax-1cn npcan breqtrrd 1z zsubcl zleltp1 syl2anc elfz2nn0 syl3anbrc oveq1d
      oveq2 oveq2d fveq2d fphpdo ) CUBEZDUCEZUDZABUAFDUEGZFDHUFGZUEGZDCUAUGZIGZ
      HJGZIGZKLZDCAUGZIGZHJGZIGZKLDCBUGZIGZHJGZIGZKLYAMUHXTYAFUILZMFDUJYQTMFUKU
      LUMUMUNXTFYBUEUQXTYBYQEDTEZYBDNOYCYAUOOXTYBUPYQXSYBUPEZXRDURZPUSUTXSYRXRD
      VAZPXTDXSDMEZXRDVBZPVCFYBDVDVEXTYDYAEZUDZYHUPEZYSYHYBQOZYHYCEUUEYHTEZFYHQ
      OZUUFUUEYGUUEDYFXSUUBXRUUDUUCRZUUEYEMEZHUBEZYFMEZUUECYDXRCMEXSUUDCVFVHUUD
      YDMEXTUUDYDYDFDVGVIPVJZVKYEHVLSZVJZVMZUUEUUIYHFNOZVNUUEYGFNOZUURUUEFYGQOU
      USVNUUEDFIGZFYGQUUEDUUEDUUJVOZVPUUEFYFQOZUUTYGQOZUUEUUKUULUVBUUNVKYEHVQSU
      UEFMEUUMUUBFDNOZUVBUVCVTUUEVRZUUOUUJXSUVDXRUUDDWARZFYFDVSWBWCWDUUEFYGUVEU
      UPWEWCUUEYGMEZFTEUUSUURVTUUPWKYGFWFSWGUUEFYHUVEUUEYHUUQVIZWEWHYHWLWIXSYSX
      RUUDYTRUUEUUGYHYBHWJGZNOZUUEYHDUVINUUEYHYGDUVHUUPUUJUUEUVGYHYGQOUUPYGWMWN
      UUEYGDHIGZDNUUEYFHNOZYGUVKNOZUUEUUKUULUVLUUNVKYEHWOSUUEUUMHMEUUBUVDUVLUVM
      VTUUOUUEWPUUJUVFYFHDWQWBWCUUEDUVAWRWSWTXSUVIDXAZXRUUDXSDXBEHXBEUVNDXCXDDH
      XESRXFUUEUUHYBTEZUUGUVJVTUUQUUEYRHTEUVOXSYRXRUUDUUARXGDHXHSYHYBXIXJWHYHYB
      XKXLYDYIXAZYGYLKUVPYFYKDIUVPYEYJHJYDYICIXNXMXOXPYDYMXAZYGYPKUVQYFYODIUVQY
      EYNHJYDYMCIXNXMXOXPXQ $.

    $( Lemma for ~ irrapx1 .  Two multiples in the same bucket means they are
       very close mod 1.  (Contributed by Stefan O'Rear, 12-Sep-2014.) $)
    irrapxlem2 $p |- ( ( A e. RR+ /\ B e. NN ) -> E. x e. ( 0 ... B ) E. y e. (
        0 ... B ) ( x < y /\ ( abs ` ( ( ( A x. x ) mod 1 ) - ( ( A x. y ) mod
        1 ) ) ) < ( 1 / B ) ) ) $=
      ( wcel wa clt wbr cmul co c1 cmo cfv wceq cc0 wrex cmin cabs cr recnd crp
      cn cv cfl cdiv irrapxlem1 caddc nnre ad3antlr rpre ad3antrrr elfzelz zred
      cfz ad2antlr remulcld 1rp a1i modcld intfrac adantl oveq12d fveq2d adantr
      simpr oveq1d flcld zcnd pnpcand cico 0red 1red modelico sylancl icodiamlt
      syl syl22anc 1m0e1 breqtrdi eqbrtrd ex wb resubcld nngt0 gt0ne0d rereccld
      abscld ltmul2 syl112anc nnnn0 nn0ge0d absidd eqcomd absmuld subdid recidd
      cle 3eqtr2d breq12d bitrd sylibrd anim2d reximdva mpd ) CUAEZDUBEZFZAUCZB
      UCZGHZDCXHIJZKLJZIJZUDMZDCXIIJZKLJZIJZUDMZNZFZBODUNJZPZAYAPXJXLXPQJZRMZKD
      UEJZGHZFZBYAPZAYAPABCDUFXGYBYHAYAXGXHYAEZFZXTYGBYAYJXIYAEZFZXSYFXJYLXSXMX
      QQJZRMZKGHZYFYLXSYOYLXSFZYNXNXMKLJZUGJZXRXQKLJZUGJZQJZRMZKGYLYNUUBNXSYLYM
      UUARYLXMYRXQYTQYLXMSEZXMYRNYLDXLXFDSEZXEYIYKDUHUIZYLXKKYLCXHXECSEXFYIYKCU
      JUKZYIXHSEXGYKYIXHXHODULUMUOUPKUAEZYLUQURZUSZUPZXMUTVPYLXQSEZXQYTNYLDXPUU
      EYLXOKYLCXIUUFYKXISEYJYKXIXIODULUMVAUPUUHUSZUPZXQUTVPVBVCVDYPUUBXRYQUGJZY
      TQJZRMZKGYPUUAUUORYPYRUUNYTQYPXNXRYQUGYLXSVEVFVFVCYLUUPKGHXSYLUUPYQYSQJZR
      MZKGYLUUOUUQRYLXRYQYSYLXRYLXQUUMVGVHYLYQYLXMKUUJUUHUSTYLYSYLXQKUUMUUHUSTV
      IVCYLUURKOQJZKGYLOSEKSEYQOKVJJZEZYSUUTEZUURUUSGHYLVKYLVLYLUUCUUGUVAUUJUQX
      MKVMVNYLUUKUUGUVBUUMUQXQKVMVNOKYQYSVOVQVRVSVTVDVTVTWAYLYFDYDIJZDYEIJZGHZY
      OYLYDSEYESEUUDODGHZYFUVEWBYLYCYLYCYLXLXPUUIUULWCTZWGYLDUUEYLDXFUVFXEYIYKD
      WDUIZWEZWFUUEUVHYDYEDWHWIYLUVCYNUVDKGYLUVCDRMZYDIJDYCIJZRMYNYLDUVJYDIYLUV
      JDYLDUUEXFODWQHXEYIYKXFDDWJWKUIWLWMVFYLDYCYLDUUETZUVGWNYLUVKYMRYLDXLXPUVL
      YLXLUUITYLXPUULTWOVCWRYLDUVLUVIWPWSWTXAXBXCXCXD $.

    $( Lemma for ~ irrapx1 .  By subtraction, there is a multiple very close to
       an integer.  (Contributed by Stefan O'Rear, 13-Sep-2014.) $)
    irrapxlem3 $p |- ( ( A e. RR+ /\ B e. NN ) -> E. x e. ( 1 ... B ) E. y e.
        NN0 ( abs ` ( ( A x. x ) - y ) ) < ( 1 / B ) ) $=
      ( va wcel wa clt wbr cmul co c1 cmin cabs cfv cc0 cle syl recnd cr vb crp
      cn cv cmo cdiv cfz wrex cn0 irrapxlem2 cfl cz 1z a1i simpllr nnzd simplrr
      elfzelzd simplrl zsubcld 1m1e0 elfzelz ad2antrl ad2antll posdifd eqbrtrid
      zred biimpa wb zlem1lt sylancr mpbird resubcld 0red nnred elfzle1 subid1d
      lesub2dd elfzle2 eqbrtrd letrd elfzd adantrr cuz ad3antrrr remulcld simpr
      ltled rpgt0 lemul2 syl112anc mpbid flword2 syl3anc uznn0sub subdid oveq1d
      rpre flcld zcnd sub4d modfrac eqcomd oveq12d 3eqtrd fveq2d modcld abssubd
      wceq 1rp eqtr2d breq1d biimpd impr oveq2 fvoveq1d rspc2ev rexlimdvva mpd
      ex ) CUBFZDUCFZGZEUDZUAUDZHIZCYDJKZLUEKZCYEJKZLUEKZMKNOZLDUFKZHIZGZUAPDUG
      KZUHEYOUHCAUDZJKZBUDZMKNOZYLHIZBUIUHALDUGKZUHZEUACDUJYCYNUUBEUAYOYOYCYDYO
      FZYEYOFZGZGZYNUUBUUFYNGYEYDMKZUUAFZYIUKOZYGUKOZMKZUIFZCUUGJKZUUKMKZNOZYLH
      IZUUBUUFYFUUHYMUUFYFGZUUGLDLULFZUUQUMUNUUQDYAYBUUEYFUOZUPUUQYEYDUUQYEPDYC
      UUCUUDYFUQZURZUUQYDPDYCUUCUUDYFUSZURZUTZUUQLUUGQIZLLMKZUUGHIZUUQUVFPUUGHV
      AUUFYFPUUGHIUUFYDYEUUFYDUUCYDULFYCUUDYDPDVBVCVGUUFYEUUDYEULFYCUUCYEPDVBVD
      VGVEVHVFUUQUURUUGULFUVEUVGVIUMUVDLUUGVJVKVLUUQUUGYEPMKZDUUQYEYDUUQYEUVAVG
      ZUUQYDUVCVGZVMUUQYEPUVIUUQVNZVMUUQDUUSVOUUQPYDYEUVKUVJUVIUUQUUCPYDQIUVBYD
      PDVPRVRUUQUVHYEDQUUQYEUUQYEUVISZVQUUQUUDYEDQIUUTYEPDVSRVTWAWBWCUUFYFUULYM
      UUQUUIUUJWDOFZUULUUQYGTFZYITFZYGYIQIZUVMUUQCYDYACTFZYBUUEYFCWRWEZUVJWFZUU
      QCYEUVRUVIWFZUUQYDYEQIZUVPUUQYDYEUVJUVIUUFYFWGWHUUQYDTFYETFUVQPCHIZUWAUVP
      VIUVJUVIUVRYAUWBYBUUEYFCWIWEYDYECWJWKWLYGYIWMWNUUJUUIWORWCUUFYFYMUUPUUQYM
      UUPUUQYKUUOYLHUUQUUOYJYHMKZNOYKUUQUUNUWCNUUQUUNYIYGMKZUUKMKYIUUIMKZYGUUJM
      KZMKUWCUUQUUMUWDUUKMUUQCYEYDUUQCUVRSUVLUUQYDUVJSWPWQUUQYIYGUUIUUJUUQYIUVT
      SUUQYGUVSSUUQUUIUUQYIUVTWSWTUUQUUJUUQYGUVSWSWTXAUUQUWEYJUWFYHMUUQYJUWEUUQ
      UVOYJUWEXIUVTYIXBRXCUUQYHUWFUUQUVNYHUWFXIUVSYGXBRXCXDXEXFUUQYJYHUUQYJUUQY
      ILUVTLUBFUUQXJUNZXGSUUQYHUUQYGLUVSUWGXGSXHXKXLXMXNYTUUPUUMYRMKZNOZYLHIABU
      UGUUKUUAUIYPUUGXIZYSUWIYLHUWJYQUUMYRNMYPUUGCJXOXPXLYRUUKXIZUWIUUOYLHUWKUW
      HUUNNYRUUKUUMMXOXFXLXQWNXTXRXS $.

    $( Lemma for ~ irrapx1 .  Eliminate ranges, use positivity of the input to
       force positivity of the output by increasing ` B ` as needed.
       (Contributed by Stefan O'Rear, 13-Sep-2014.) $)
    irrapxlem4 $p |- ( ( A e. RR+ /\ B e. NN ) -> E. x e. NN E. y e. NN ( abs `
        ( ( A x. x ) - y ) ) < ( 1 / if ( x <_ B , B , x ) ) ) $=
      ( va vb wcel cn wa cv co cmin cabs c1 cdiv cle wbr clt cc0 cr crp cfv cfl
      cmul caddc cif wrex cfz cn0 elfznn ad3antlr nn0z ad2antlr simpl ad3antrrr
      cneg rpred nnred remulcld nn0re resubcld recnd rpreccld rprege0d flge0nn0
      abscld nn0p1nn 3syl simpr ifcld nnrecred 0red rprecred flcld peano2re syl
      cz zred max2 syl2anc wb nngt0d lerec syl22anc mpbid fllep1 nnne0d recrecd
      nncnd breqtrrd recgt0d rpgt0d mpbird mulridd nnge1d 1red lemul2d eqbrtrrd
      letrd subid1d ltletrd absltd simprd ltsub2d sylanbrc elfzle2 max1 syl3anc
      elnnz maxle mpbir2and weq oveq2 fvoveq1d breq1 id ifbieq2d oveq2d breq12d
      fveq2d breq1d rspc2ev irrapxlem3 r19.29vva ) CUAGZDHGZIZCEJZUDKZFJZLKZMUB
      ZNDNCOKZUCUBZNUEKZPQZYODUFZOKZRQZCAJZUDKZBJZLKMUBZNYTDPQZDYTUFZOKZRQZBHUG
      AHUGZEFNYQUHKZUIYGYHUUIGZIZYJUIGZIZYSIZYHHGZYJHGZYLNYHDPQZDYHUFZOKZRQZUUH
      UUJUUOYGUULYSYHYQUJUKZUUNYJVQGZSYJRQZUUPUULUVBUUKYSYJULUMUUNUVCYKYISLKZRQ
      ZUUNUVDUPYKRQZUVEUUNYLUVDRQUVFUVEIUUNYLYRUVDUUNYKUUNYKUUNYIYJUUNCYHUUNCYG
      YEUUJUULYSYEYFUNZUOZUQZUUNYHUVAURZUSZUULYJTGUUKYSYJUTUMZVAZVBVFZUUNYQUUNY
      PYODHYGYOHGZUUJUULYSYGYMTGZSYMPQIYNUIGUVOYGYMYGCUVGVCVDYMVEYNVGVHZUOZYGYF
      UUJUULYSYEYFVIZUOZVJZVKZUUNYISUVKUUNVLZVAZUUMYSVIZUUNYRCUVDUWBUVIUWDUUNYR
      NYOOKZCUWBUUNYOUVRVKZUVIUUNYOYQPQZYRUWFPQZUUNDTGZYOTGZUWHUUNDUVTURZUUNYNT
      GUWKUUNYNUUNYMUUNCUVHVMZVNVRYNVOVPZDYOVSVTUUNUWKSYORQYQTGZSYQRQZUWHUWIWAU
      WNUUNYOUVRWBZUUNYQUWAURZUUNYQUWAWBZYOYQWCWDWEUUNUWFCPQZYMNUWFOKZPQZUUNYMY
      OUXAPUUNUVPYMYOPQUWMYMWFVPUUNYOUUNYOUVRWIUUNYOUVRWGWHWJUUNUWFTGSUWFRQCTGS
      CRQUWTUXBWAUWGUUNYOUWNUWQWKUVIUUNCUVHWLUWFCWCWDWMWSUUNCYIUVDPUUNCNUDKZCYI
      PUUNCUUNCUVIVBWNUUNNYHPQUXCYIPQUUNYHUVAWOUUNNYHCUUNWPUVJUVHWQWEWRUUNYIUUN
      YIUVKVBWTWJWSXAUUNYKUVDUVMUWDXBWEXCUUNSYJYIUWCUVLUVKXDWMYJXIXEUUNYLYRUUSU
      VNUWBUUNUURUUNUUQDYHHUVTUVAVJVKUWEUUNUURYQPQZYRUUSPQZUUNUXDYHYQPQZDYQPQZU
      UJUXFYGUULYSYHNYQXFUKUUNUWJUWKUXGUWLUWNDYOXGVTUUNYHTGZUWJUWOUXDUXFUXGIWAU
      VJUWLUWRYHDYQXJXHXKUUNUURTGSUURRQUWOUWPUXDUXEWAUUNUUQDYHTUWLUVJVJZUUNSDUU
      RUWCUWLUXIUUNDUVTWBUUNUXHUWJDUURPQUVJUWLYHDVSVTXAUWRUWSUURYQWCWDWEXAUUGUU
      TYIUUBLKZMUBZUUSRQABYHYJHHAEXLZUUCUXKUUFUUSRUXLUUAYIUUBMLYTYHCUDXMXNUXLUU
      EUURNOUXLUUDUUQYTYHDYTYHDPXOUXLXPXQXRXSBFXLZUXKYLUUSRUXMUXJYKMUUBYJYILXMX
      TYAYBXHYGYEYQHGYSFUIUGEUUIUGUVGYGYPYODHUVQUVSVJEFCYQYCVTYD $.

    $( Lemma for ~ irrapx1 .  Switching to real intervals and fraction syntax.
       (Contributed by Stefan O'Rear, 13-Sep-2014.) $)
    irrapxlem5 $p |- ( ( A e. RR+ /\ B e. RR+ )
        -> E. x e. QQ ( 0 < x /\ ( abs ` ( x - A ) ) < B
          /\ ( abs ` ( x - A ) ) < ( ( denom ` x ) ^ -u 2 ) ) ) $=
      ( wcel wa cmul co cmin cabs cfv c1 cdiv cle wbr clt cn cc0 cq cr syl wrex
      va vb crp cv cfl caddc cif cdenom c2 cneg w3a cn0 simpr rpreccld rprege0d
      cexp flge0nn0 nn0p1nn irrapxlem4 syldan wne simplrr simplrl nnne0d qdivcl
      3syl nnq syl3anc nnrpd rpdivcld rpgt0d nnred nnnn0d nn0ge0d absidd eqcomd
      oveq1d nncnd qre rpre ad3antrrr resubcld recnd absmuld eqtr4d cc qcn rpcn
      subdid divcan2d mulcomd oveq12d eqtrd fveq2d abssubd 3eqtrd abscld rpge0d
      remulcld simpllr rprecred syl2anc ifcld rpred fllep1 letrd lerecd recrecd
      max2 mpbid rpne0d mullidd nnge1d lemul1d eqbrtrd ltletrd wb nngt0d ltmul2
      1red syl112anc mpbird msqgt0d gt0ne0d rereccld qdencl max1 dividd divrecd
      divdiv1d 3eqtr3rd 3brtr4d cz nnzd divdenle le2msq syl22anc lerec wceq mpd
      2nn0 expneg sylancl sqvald oveq2d breqtrrd breq2 fvoveq1 breq1d 3anbi123d
      fveq2 breq12d rspcev syl13anc ex rexlimdvva ) BUDDZCUDDZEZBUBUEZFGZUCUEZH
      GZIJZKUVAKCLGZUFJZKUGGZMNZUVHUVAUHZLGZONZUCPUAUBPUAZQAUEZONZUVNBHGIJZCONZ
      UVPUVNUIJZUJUKZUQGZONZULZARUAZUURUUSUVHPDZUVMUUTUVFSDZQUVFMNZEUVGUMDZUWDU
      UTUVFUUTCUURUUSUNUOUPUVFURZUVGUSZVGUBUCBUVHUTVAUUTUVLUWCUBUCPPUUTUVAPDZUV
      CPDZEZEZUVLUWCUWMUVLEZUVCUVALGZRDZQUWOONZUWOBHGZIJZCONZUWSUWOUIJZUVSUQGZO
      NZUWCUWNUVCRDZUVARDZUVAQVBUWPUWNUWKUXDUUTUWJUWKUVLVCZUVCVHTUWNUWJUXEUUTUW
      JUWKUVLVDZUVAVHTUWNUVAUXGVEZUVCUVAVFVIZUWNUWOUWNUVCUVAUWNUVCUXFVJUWNUVAUX
      GVJZVKVLUWNUWTUVAUWSFGZUVACFGZONZUWNUXKUVEUXLOUWNUXKUVAUWRFGZIJZUVCUVBHGZ
      IJUVEUWNUXKUVAIJZUWSFGUXOUWNUVAUXQUWSFUWNUXQUVAUWNUVAUWNUVAUXGVMZUWNUVAUW
      NUVAUXGVNVOZVPVQVRUWNUVAUWRUWNUVAUXGVSZUWNUWRUWNUWOBUWNUWPUWOSDUXIUWOVTTU
      URBSDUUSUWLUVLBWAWBZWCWDZWEWFUWNUXNUXPIUWNUXNUVAUWOFGZUVABFGZHGUXPUWNUVAU
      WOBUXTUWNUWPUWOWGDUXIUWOWHTUURBWGDUUSUWLUVLBWIWBZWJUWNUYCUVCUYDUVBHUWNUVC
      UVAUWNUVCUXFVSZUXTUXHWKUWNUVABUXTUYEWLWMWNWOUWNUVCUVBUYFUWNUVBUWNBUVAUYAU
      XRWTZWDWPWQZUWNUVEUVKUXLUWNUVDUWNUVDUWNUVBUVCUYGUWNUVCUXFVMWCWDWRZUWNUVJU
      WNUVIUVHUVAUDUWNUVHUWNUWGUWDUWNUWEUWFUWGUWNCUURUUSUWLUVLXAZXBZUWNUVFUWNCU
      YJUOZWSUWHXCUWITZVJUXJXDZXBZUWNUVACUXRUWNCUYJXEZWTZUWMUVLUNZUWNUVKKUVFLGZ
      UXLUYOUWNUVFUYLXBUYQUWNUVFUVJMNUVKUYSMNUWNUVFUVHUVJUYKUWNUVHUYMVMZUWNUVIU
      VHUVASUYTUXRXDUWNUWEUVFUVHMNUYKUVFXFTUWNUVASDZUVHSDZUVHUVJMNUXRUYTUVAUVHX
      JXCXGUWNUVFUVJUYLUYNXHXKUWNUYSKCFGZUXLMUWNUYSCVUCUWNCUWNCUYPWDZUWNCUYJXLX
      IUWNCVUDXMWFUWNKUVAMNVUCUXLMNUWNUVAUXGXNUWNKUVACUWNYAUXRUYJXOXKXPXGXQXPUW
      NUWSSDZCSDVUAQUVAONZUWTUXMXRUWNUWRUYBWRZUYPUXRUWNUVAUXGXSZUWSCUVAXTYBYCUW
      NUWSKUXAUXAFGZLGZUXBOUWNUWSKUVAUVAFGZLGZVUJVUGUWNVUKUWNUVAUVAUXRUXRWTZUWN
      VUKUWNUVAUXRUXHYDZYEZYFZUWNVUIUWNUXAUXAUWNUXAUWNUWPUXAPDUXIUWOYGTZVMZVURW
      TZUWNVUIUWNUXAVURUWNUXAVUQVEYDZYEYFUWNUWSVULONZUXKUVAVULFGZONZUWNUVEKUVAL
      GZUXKVVBOUWNUVEUVKVVDUYIUYOUWNUVAUXRUXHYFUYRUWNUVAUVJMNZUVKVVDMNUWNVUAVUB
      VVEUXRUYTUVAUVHYHXCUWNUVAUVJUXJUYNXHXKXQUYHUWNUVAUVALGZUVALGUVAVUKLGVVDVV
      BUWNUVAUVAUVAUXTUXTUXTUXHUXHYKUWNVVFKUVALUWNUVAUXTUXHYIVRUWNUVAVUKUXTUWNV
      UKVUMWDVUOYJYLYMUWNVUEVULSDVUAVUFVVAVVCXRVUGVUPUXRVUHUWSVULUVAXTYBYCUWNVU
      IVUKMNZVULVUJMNZUWNUXAUVAMNZVVGUWNUVCYNDUWJVVIUWNUVCUXFYOUXGUVCUVAYPXCUWN
      UXASDQUXAMNVUAQUVAMNVVIVVGXRVURUWNUXAUWNUXAVUQVNVOUXRUXSUXAUVAYQYRXKUWNVU
      ISDQVUIONVUKSDQVUKONVVGVVHXRVUSVUTVUMVUNVUIVUKYSYRXKXQUWNUXBKUXAUJUQGZLGZ
      VUJUWNUXAWGDUJUMDUXBVVKYTUWNUXAVUQVSZUUBUXAUJUUCUUDUWNVVJVUIKLUWNUXAVVLUU
      EUUFWNUUGUWBUWQUWTUXCULAUWORUVNUWOYTZUVOUWQUVQUWTUWAUXCUVNUWOQOUUHVVMUVPU
      WSCOUVNUWOBIHUUIZUUJVVMUVPUWSUVTUXBOVVNVVMUVRUXAUVSUQUVNUWOUIUULVRUUMUUKU
      UNUUOUUPUUQUUA $.

    $( Lemma for ~ irrapx1 .  Explicit description of a non-closed set.
       (Contributed by Stefan O'Rear, 13-Sep-2014.) $)
    irrapxlem6 $p |- ( ( A e. RR+ /\ B e. RR+ ) -> E. x e. { y e. QQ | ( 0 < y
        /\ ( abs ` ( y - A ) ) < ( ( denom ` y ) ^ -u 2 ) ) } ( abs ` ( x - A )
        ) < B ) $=
      ( va crp wcel wa cc0 cv clt wbr cmin co cabs cfv cdenom cexp cq weq breq2
      cneg w3a crab wrex simplr simpr1 simpr3 jca fvoveq1 fveq2 breq12d anbi12d
      c2 oveq1d elrab sylanbrc simpr2 breq1d rspcev syl2anc irrapxlem5 r19.29a
      ) CFGDFGHZIEJZKLZVECMNOPZDKLZVGVEQPZUNUBZRNZKLZUCZAJZCMNOPZDKLZAIBJZKLZVQ
      CMNOPZVQQPZVJRNZKLZHZBSUDZUEZESVDVESGZHZVMHZVEWDGZVHWEWHWFVFVLHZWIVDWFVMU
      FWHVFVLWGVFVHVLUGWGVFVHVLUHUIWCWJBVESBETZVRVFWBVLVQVEIKUAWKVSVGWAVKKVQVEC
      OMUJWKVTVIVJRVQVEQUKUOULUMUPUQWGVFVHVLURVPVHAVEWDAETVOVGDKVNVECOMUJUSUTVA
      ECDVBVC $.

    $( Dirichlet's approximation theorem.  Every positive irrational number has
       infinitely many rational approximations which are closer than the
       inverse squares of their reduced denominators.  Lemma 61 in
       [vandenDries] p. 42.  (Contributed by Stefan O'Rear, 14-Sep-2014.) $)
    irrapx1 $p |- ( A e. ( RR+ \ QQ ) -> { y e. QQ | ( 0 < y /\ ( abs ` ( y - A
        ) ) < ( ( denom ` y ) ^ -u 2 ) ) } ~~ NN ) $=
      ( vb va crp cq wcel com cen wbr cn wa cv clt cmin co cabs cfv wss cr cdif
      cc0 cdenom c2 cneg cexp crab cfn wn qnnen nnenom entri pm3.2i wrex ssrab2
      wral qssre sstri a1i eldifi rpred eldifn elrabi nsyl irrapxlem6 ralrimiva
      sylan rencldnfi syl31anc jctil ctbnfien sylancr ) BEFUAGZFHIJZKHIJZLUBAMZ
      NJVPBOPQRVPUCRUDUEUFPNJLZAFUGZFSZVRUHGUIZLVRKIJVNVOFKHUJUKULUKUMVMVTVSVMV
      RTSZBTGBVRGZUICMBOPQRDMZNJCVRUNZDEUPVTWAVMVRFTVQAFUOZUQURUSVMBBEFUTZVAVMB
      FGWBBEFVBVQABFVCVDVMWDDEVMBEGWCEGWDWFCABWCVEVGVFDCVRBVHVIWEVJVRFKVKVL $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Pell equations 1: A nontrivial solution always exists
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d a b c d e f g A $.  $d a b c d e f g B $.  $d a b c d e f g C $.
    $d a b c d e f g D $.  $d a b c d e f g E $.  $d a b c d e f g F $.
    $d a b c d e f g x $.  $d a b c d e f g y $.  $d a b c d e f g z $.
    $d a b c d e f g ph $.

    $( a bit of terminology - Pell field = Q[sqr d], Pell ring = Z[sqr d]
       (algebraic integers in Pell field), Pell group = right branch of the
       group of units in Pell ring - isomorphic to ZZ, Pell semigroup = Pell
       group elements >= 1, resembles NN0 $)

    $( Lemma for ~ pellex .  Arithmetical core of pellexlem3, norm lower bound.
       This begins Dirichlet's proof of the Pell equation solution existence;
       the proof here follows theorem 62 of [vandenDries] p. 43.  (Contributed
       by Stefan O'Rear, 14-Sep-2014.) $)
    pellexlem1 $p |- ( ( ( D e. NN /\ A e. NN /\ B e. NN ) /\ -. ( sqrt ` D )
        e. QQ ) -> ( ( A ^ 2 ) - ( D x. ( B ^ 2 ) ) ) =/= 0 ) $=
      ( cn wcel w3a csqrt cfv cq c2 cexp co cc0 wne wceq nncn 3ad2ant2 3ad2ant3
      cc wbr wn cmul cmin sqcld 3ad2ant1 mulcld subeq0ad nnne0 sqne0 syl mpbird
      cdiv wb divmul3d sqdiv fveq2d syl3anc nnre redivcld cle clt nnnn0 nn0ge0d
      cr nngt0 divge0 syl22anc sqrtsqd eqtr3d nnq qdivcl fveq2 eleq1d syl5ibcom
      eqeltrd sylbird sylbid necon3bd imp ) CDEZADEZBDEZFZCGHZIEZUAAJKLZCBJKLZU
      BLZUCLZMNWCWEWIMWCWIMOWFWHOZWEWCWFWHWCAWAVTASEZWBAPQZUDZWCCWGVTWACSEWBCPU
      EZWCBWBVTBSEZWABPRZUDZUFUGWCWJWFWGULLZCOZWEWCWFCWGWMWNWQWCWGMNZBMNZWBVTXA
      WABUHRZWCWOWTXAUMWPBUIUJUKUNWCWRGHZIEWSWEWCXCABULLZIWCXDJKLZGHZXCXDWCWKWO
      XAXFXCOWLWPXBWKWOXAFXEWRGABUOUPUQWCXDWCABWAVTAVDEZWBAURQZWBVTBVDEZWABURRZ
      XBUSWCXGMAUTTZXIMBVATZMXDUTTXHWAVTXKWBWAAAVBVCQXJWBVTXLWABVERABVFVGVHVIWC
      AIEZBIEZXAXDIEWAVTXMWBAVJQWBVTXNWABVJRXBABVKUQVOWSXCWDIWRCGVLVMVNVPVQVRVS
      $.

    $( Lemma for ~ pellex .  Arithmetical core of pellexlem3, norm upper bound.
       (Contributed by Stefan O'Rear, 14-Sep-2014.) $)
    pellexlem2 $p |- ( ( ( D e. NN /\ A e. NN /\ B e. NN ) /\ ( abs ` ( ( A / B
        ) - ( sqrt ` D ) ) ) < ( B ^ -u 2 ) ) -> ( abs ` ( ( A ^ 2 ) - ( D x. (
        B ^ 2 ) ) ) ) < ( 1 + ( 2 x. ( sqrt ` D ) ) ) ) $=
      ( wcel cdiv co cfv cabs c2 clt wbr cmul caddc c1 oveq2d cc cc0 recnd cle
      cr cn w3a csqrt cmin cneg cexp simpl3 resqcld sqge0d absidd eqcomd simpl2
      nnred nncnd sqcld simpl1 mulcld subcld wne nnne0d biimpar syl2anc absdivd
      wa eqtr4d abscld divcan2d divsubdird sqdivd wceq nnnn0d nn0ge0d remsqsqrt
      sqne0 resqrtcld sqvald divcan4d 3eqtr4rd oveq12d divcld nndivred resubcld
      subsq addcld mulcomd eqtrd 3eqtrd fveq2d 3eqtr3d absmuld remulcld cz 2nn0
      nn0negzi a1i reexpclzd 1red 2re readdcld simpr wb divgt0d sqrtgt0 addgt0d
      nngt0d gt0ne0d absgt0 biimpa ltmul1 syl112anc mpbid sqgt0d ltmul2 expclzd
      mulass syl3anc expneg sylancl recidd oveq1d mullidd addcomd ppncan 2times
      cn0 syl abstrid 0le2 sqrtge0d mulge0d nnsqcld 0lt1 lerec syl22anc 1div1e1
      nnge1d breqtrdi eqbrtrd ltletrd ltled leadd1dd letrd ) CUADZAUADZBUADZUBZ
      ABEFZCUCGZUDFZHGZBIUEZUFFZJKZVDZAIUFFZCBIUFFZLFZUDFZHGZUUPUUIUUGUUHMFZLFZ
      HGZLFZNIUUHLFZMFZJUUNUUPUUSUUPEFZLFUUPUURUUPEFZHGZLFUUSUVCUUNUVFUVHUUPLUU
      NUVFUUSUUPHGZEFUVHUUNUUPUVIUUSEUUNUVIUUPUUNUUPUUNBUUNBUUCUUDUUEUUMUGZUMZU
      HZUUNBUVKUIUJUKOUUNUURUUPUUNUUOUUQUUNAUUNAUUCUUDUUEUUMULZUNZUOZUUNCUUPUUN
      CUUCUUDUUEUUMUPZUNZUUNBUUNBUVJUNZUOZUQZURZUVSUUNBPDZBQUSZUUPQUSZUVRUUNBUV
      JUTZUWBUWDUWCBVNVAVBZVCVEOUUNUUSUUPUUNUUSUUNUURUWAVFRUVSUWFVGUUNUVHUVBUUP
      LUUNUVGUVAHUUNUVGUUOUUPEFZUUQUUPEFZUDFUUGIUFFZUUHIUFFZUDFZUVAUUNUUOUUQUUP
      UVOUVTUVSUWFVHUUNUWGUWIUWHUWJUDUUNUWIUWGUUNABUVNUVRUWEVIUKUUNUUHUUHLFZCUW
      JUWHUUNCTDZQCSKUWLCVJUUNCUVPUMZUUNCUUNCUVPVKVLZCVMVBUUNUUHUUNUUHUUNCUWNUW
      OVOZRZVPUUNCUUPUVQUVSUWFVQVRVSUUNUWKUUTUUILFZUVAUUNUUGPDZUUHPDZUWKUWRVJUU
      NABUVNUVRUWEVTZUWQUUGUUHWCVBUUNUUTUUIUUNUUGUUHUXAUWQWDZUUNUUIUUNUUGUUHUUN
      ABUUNAUVMUMZUVJWAZUWPWBZRZWEWFWGWHOWIUUNUVCUUPUUJUUTHGZLFZLFZUVEJUUNUVBUX
      HUUPLUUNUUIUUTUXFUXBWJOUUNUXIUUPUULUXGLFZLFZUVEUUNUUPUXHUVLUUNUUJUXGUUNUU
      IUXFVFZUUNUUTUXBVFZWKZWKUUNUUPUXJUVLUUNUULUXGUUNBUUKUVKUWEUUKWLDUUNIWMWNW
      OZWPZUXMWKZWKUUNNUVDUUNWQZUUNIUUHITDUUNWRWOZUWPWKZWSZUUNUXHUXJJKZUXIUXKJK
      ZUUNUUMUYBUUFUUMWTZUUNUUJTDUULTDUXGTDQUXGJKZUUMUYBXAUXLUXPUXMUUNUUTPDZUUT
      QUSZUYEUXBUUNUUTUUNUUGUUHUXDUWPUUNABUXCUVKUUNAUVMXEUUNBUVJXEXBUUNUWMQCJKQ
      UUHJKUWNUUNCUVPXECXCVBXDXFUYFUYGUYEUUTXGXHVBUUJUULUXGXIXJXKUUNUXHTDUXJTDU
      UPTDZQUUPJKZUYBUYCXAUXNUXQUVLUUNBUVKUWEXLZUXHUXJUUPXMXJXKUUNUXKUXGUVESUUN
      UXKUUPUULLFZUXGLFZNUXGLFUXGUUNUUPPDZUULPDZUXGPDZUXKUYLVJUVSUUNBUUKUVRUWEU
      XOXNUUNUXGUXMRZUYMUYNUYOUBUYLUXKUUPUULUXGXOUKXPUUNUYKNUXGLUUNUYKUUPNUUPEF
      ZLFNUUNUULUYQUUPLUUNUWBIYEDUULUYQVJUVRWMBIXQXRZOUUNUUPUVSUWFXSWFXTUUNUXGU
      YPYAWGUUNUXGUUIUVDMFZHGZUVESUUNUUTUYSHUUNUUTUUHUUGMFZUUHUUHMFZUUIMFZUYSUU
      NUUGUUHUXAUWQYBUUNUWTUWTUWSVUAVUCVJUWQUWQUXAUWTUWTUWSUBVUCVUAUUHUUHUUGYCU
      KXPUUNVUCUUIVUBMFUYSUUNVUBUUIUUNUUHUUHUWQUWQWDUXFYBUUNVUBUVDUUIMUUNUWTVUB
      UVDVJUWQUWTUVDVUBUUHYDUKYFOWFWGWHUUNUYTUUJUVDHGZMFZUVEUUNUYSUUNUYSUUNUUIU
      VDUXEUXTWSRVFUUNUUJVUDUXLUUNUVDUUNUVDUXTRZVFWSUYAUUNUUIUVDUXFVUFYGUUNVUEU
      UJUVDMFUVESUUNVUDUVDUUJMUUNUVDUXTUUNIUUHUXSUWPQISKUUNYHWOUUNCUWNUWOYIYJUJ
      OUUNUUJNUVDUXLUXRUXTUUNUUJNUXLUXRUUNUUJUULNUXLUXPUXRUYDUUNUULUYQNSUYRUUNU
      YQNNEFZNSUUNNUUPSKZUYQVUGSKZUUNUUPUUNBUVJYKYPUUNNTDQNJKZUYHUYIVUHVUIXAUXR
      VUJUUNYLWOUVLUYJNUUPYMYNXKYOYQYRYSYTUUAYRUUBYRYRYSYRYR $.

    ${
      $d D x y z $.
      $( Lemma for ~ pellex .  To each good rational approximation of
         ` ( sqrt `` D ) ` , there exists a near-solution.  (Contributed by
         Stefan O'Rear, 14-Sep-2014.) $)
      pellexlem3 $p |- ( ( D e. NN /\ -. ( sqrt ` D ) e. QQ ) -> { x e. QQ |
       ( 0 < x /\ ( abs ` ( x - ( sqrt ` D ) ) ) < ( ( denom ` x ) ^ -u 2 ) ) }
          ~<_ { <. y , z >. | ( ( y e. NN /\ z e. NN ) /\ ( ( ( y ^ 2 ) - ( D
          x. ( z ^ 2 ) ) ) =/= 0 /\ ( abs ` ( ( y ^ 2 ) - ( D x. ( z ^ 2 ) ) )
          ) < ( 1 + ( 2 x. ( sqrt ` D ) ) ) ) ) } ) $=
        ( cn wcel cfv cq wa cv c2 cexp co cmin cc0 cabs clt wbr cdenom wceq wne
        va vb csqrt wn cmul c1 caddc copab cvv cneg crab cdom cxp nnex opabssxp
        ssexi cnumer cop simprl simprrl qgt0numnn syl2anc qdencl syl jca simpll
        xpex simplr pellexlem1 syl31anc cdiv simprrr qeqnumdivden oveq1d fveq2d
        wb breq1d mpbid pellexlem2 jca32 ex breq2 fvoveq1 fveq2 breq12d anbi12d
        elrab fvex eleq1 anbi1d oveq1 neeq1d anbi2d oveq2d ssrab2 sselid simprr
        opelopab 3imtr4g opth oveq12d 3eqtr4d biimtrid opeq12d impbid1 dom2d
        mpi ) DEFZDUDGZHFUEZIZBJZEFZCJZEFZIZXMKLMZDXOKLMZUFMZNMZOUAZYAPGZUGKXJU
        FMUHMZQRZIZIZBCUIZUJFOAJZQRZYIXJNMPGZYISGZKUKZLMZQRZIZAHULZYHUMRYHEEUNE
        EUOUOVHYFBCEEUPUQXLUBUCYQYHUBJZURGZYRSGZUSZUCJZURGZUUBSGZUSZUJXLYRHFZOY
        RQRZYRXJNMZPGZYTYMLMZQRZIZIZYSEFZYTEFZIZYSKLMZDYTKLMZUFMZNMZOUAZUUTPGZY
        DQRZIZIZYRYQFZUUAYHFXLUUMUVEXLUUMIZUUPUVAUVCUVGUUNUUOUVGUUFUUGUUNXLUUFU
        ULUTZXLUUFUUGUUKVAYRVBVCZUVGUUFUUOUVHYRVDVEZVFUVGXIUUNUUOXKUVAXIXKUUMVG
        ZUVIUVJXIXKUUMVIYSYTDVJVKUVGXIUUNUUOYSYTVLMZXJNMZPGZUUJQRZUVCUVKUVIUVJU
        VGUUKUVOXLUUFUUGUUKVMUVGUUFUUKUVOVQUVHUUFUUIUVNUUJQUUFUUHUVMPUUFYRUVLXJ
        NYRVNZVOVPVRVEVSYSYTDVTVKWAWBYPUULAYRHYIYRTZYJUUGYOUUKYIYROQWCUVQYKUUIY
        NUUJQYIYRXJPNWDUVQYLYTYMLYIYRSWEVOWFWGWHYGUUNXPIZUUQXTNMZOUAZUVSPGZYDQR
        ZIZIUVEBCYSYTYRURWIZYRSWIZXMYSTZXQUVRYFUWCUWFXNUUNXPXMYSEWJWKUWFYBUVTYE
        UWBUWFYAUVSOUWFXRUUQXTNXMYSKLWLVOZWMUWFYCUWAYDQUWFYAUVSPUWGVPVRWGWGXOYT
        TZUVRUUPUWCUVDUWHXPUUOUUNXOYTEWJWNUWHUVTUVAUWBUVCUWHUVSUUTOUWHXTUUSUUQN
        UWHXSUURDUFXOYTKLWLWOWOZWMUWHUWAUVBYDQUWHUVSUUTPUWIVPVRWGWGWSWTXLUVFUUB
        YQFZIZUUAUUETZYRUUBTZVQZXLUWKIZUUFUUBHFZUWNUWOYQHYRYPAHWPZXLUVFUWJUTWQU
        WOYQHUUBUWQXLUVFUWJWRWQUUFUWPIZUWLUWMUWLYSUUCTZYTUUDTZIZUWRUWMYSYTUUCUU
        DUWDUWEXAUWRUXAUWMUWRUXAIZUVLUUCUUDVLMZYRUUBUXBYSUUCYTUUDVLUWRUWSUWTUTU
        WRUWSUWTWRXBUXBUUFYRUVLTUUFUWPUXAVGUVPVEUXBUWPUUBUXCTUUFUWPUXAVIUUBVNVE
        XCWBXDUWMYSUUCYTUUDYRUUBURWEYRUUBSWEXEXFVCWBXGXH $.
    $}

    ${
      $d D y z $.
      $( Lemma for ~ pellex .  Invoking ~ irrapx1 , we have infinitely many
         near-solutions.  (Contributed by Stefan O'Rear, 14-Sep-2014.) $)
      pellexlem4 $p |- ( ( D e. NN /\ -. ( sqrt ` D ) e. QQ ) -> { <. y , z >.
       | ( ( y e. NN /\ z e. NN ) /\ ( ( ( y ^ 2 ) - ( D x. ( z ^ 2 ) ) ) =/= 0
         /\ ( abs ` ( ( y ^ 2 ) - ( D x. ( z ^ 2 ) ) ) )
          < ( 1 + ( 2 x. ( sqrt ` D ) ) ) ) ) } ~~ NN ) $=
        ( vb cn wcel cfv cq wa cv c2 cexp co cmul cmin clt wbr cdom cen crp cc0
        csqrt wn wne cabs caddc copab cxp cvv wss nnex xpex opabssxp ssdomg mp2
        xpnnen domentr mp2an cdenom cneg crab cdif nnrp rpsqrtcld anim1i sylibr
        c1 eldif irrapx1 ensym 3syl pellexlem3 endomtr syl2anc sbth sylancr ) C
        EFZCUBGZHFUCZIZAJZEFBJZEFIWAKLMCWBKLMNMOMZUAUDWCUEGVGKVRNMUFMPQIZIABUGZ
        ERQZEWERQZWEESQWEEEUHZRQZWHESQWFWHUIFWEWHUJWIEEUKUKULWDABEEUMWEWHUIUNUO
        UPWEWHEUQURVTEUADJZPQWJVROMUEGWJUSGKUTLMPQIDHVAZSQZWKWERQWGVTVRTHVBFZWK
        ESQWLVTVRTFZVSIWMVQWNVSVQCCVCVDVEVRTHVHVFDVRVIWKEVJVKDABCVLEWKWEVMVNWEE
        VOVP $.
    $}

    ${
      $d D x y z $.
      $( Lemma for ~ pellex .  Invoking ~ fiphp3d , we have infinitely many
         near-solutions for some specific norm.  (Contributed by Stefan O'Rear,
         19-Oct-2014.) $)
      pellexlem5 $p |- ( ( D e. NN /\ -. ( sqrt ` D ) e. QQ ) -> E. x e. ZZ ( x
          =/= 0 /\ { <. y , z >. | ( ( y e. NN /\ z e. NN ) /\ ( ( y ^ 2 ) - (
          D x. ( z ^ 2 ) ) ) = x ) } ~~ NN ) ) $=
        ( cn wcel cfv wa c1st c2 cexp co c2nd cmul cmin wceq cc0 wbr cz cr cabs
        va vb csqrt cq wn cv wne caddc clt copab crab cen cfl cneg cfz csn cdif
        wrex pellexlem4 cfn fzfi diffi mp1i cop wex elopab fveq2 oveq1d oveq12d
        c1 oveq2d vex op1st oveq1i op2nd oveq2i oveq12i eqtrdi ad2antrl simprrl
        simpl simprr ad2antll cle nnz ad2antrr zsqcl syl simplr zmulcld zsubcld
        nnzd 1re 2re nnre nnnn0 nn0ge0d resqrtcld remulcl sylancr readdcl flcld
        cn0 znegcld zred nn0abscl nn0zd peano2re flltp1 lttrd wb zleltp1 mpbird
        syl2anc absle biimpa syl21anc w3a elfz biimpar syl31anc syl12anc simprl
        adantlr eldifsn sylanbrc eqeltrd ex biimtrid wi 3ad2ant3 3exp impd cdom
        cvv wss nnex ssdomg jca32 imp fiphp3d eldif elfzelz simp2 velsn biimpri
        exlimdvv necon3bi jca syl5 simp2l simp2r cxp xpex opabssxp xpnnen mp2an
        domentr ensym ssexi elrab eqtr2di eqtrd 2eximdv 3imtr4g expimpd ancomsd
        mp2 eqeq1d ssrdv 3adant3 mpsyl endomtr sbth syld reximdv2 mpd ) DEFZDUD
        GZUEFUFZHZUBUGZIGZJKLZDUWCMGZJKLZNLZOLZAUGZPZUBBUGZEFZCUGZEFZHZUWLJKLZD
        UWNJKLZNLZOLZQUHZUWTUAGZVKJUVTNLZUILZUJRZHZHZBCUKZULZEUMRZAUXDUNGZUOZUX
        KUPLZQUQZURZUSUWJQUHZUWPUWTUWJPZHZBCUKZEUMRZHZASUSUWBUBAUXHUXOUWIBCDUTU
        XMVAFUXOVAFUWBUXLUXKVBUXMUXNVCVDUWBUWCUXHFZUWIUXOFZUYBUWCUWLUWNVEZPZUXG
        HZCVFBVFUWBUYCUXGBCUWCVGUWBUYFUYCBCUWBUYFUYCUWBUYFHZUWIUWTUXOUYEUWIUWTP
        UWBUXGUYEUWIUYDIGZJKLZDUYDMGZJKLZNLZOLZUWTUYEUWEUYIUWHUYLOUYEUWDUYHJKUW
        CUYDIVHVIUYEUWGUYKDNUYEUWFUYJJKUWCUYDMVHVIVLVJUYIUWQUYLUWSOUYHUWLJKUWLU
        WNBVMZCVMZVNVOUYKUWRDNUYJUWNJKUWLUWNUYNUYOVPVOVQVRZVSVTUYGUWTUXMFZUXAUW
        TUXOFUVSUYFUYQUWAUVSUYFHUWPUVSUXEUYQUVSUYEUWPUXFWAUVSUYFWBUXGUXEUVSUYEU
        WPUXAUXEWCWDUWPUVSUXEHZHZUWTSFZUXLSFZUXKSFZUXLUWTWERUWTUXKWERHZUYQUYSUW
        QUWSUYSUWLSFZUWQSFUWMVUDUWOUYRUWLWFWGUWLWHWIUYSDUWRUVSDSFUWPUXEDWFVTUYS
        UWNSFUWRSFUYSUWNUWMUWOUYRWJWMUWNWHWIWKWLZUYSUXKUYSUXDUYSVKTFUXCTFZUXDTF
        ZWNUYSJTFUVTTFVUFWOUYSDUVSDTFUWPUXEDWPVTUYSDUVSDXDFUWPUXEDWQVTWRWSJUVTW
        TXAVKUXCXBXAZXCZXEVUIUYSUWTTFZUXKTFZUXBUXKWERZVUCUYSUWTVUEXFUYSUXKVUIXF
        ZUYSVULUXBUXKVKUILZUJRZUYSUXBUXDVUNUYSUXBUYSUXBUYSUYTUXBXDFVUEUWTXGWIXH
        ZXFVUHUYSVUKVUNTFVUMUXKXIWIUWPUVSUXEWCUYSVUGUXDVUNUJRVUHUXDXJWIXKUYSUXB
        SFVUBVULVUOXLVUPVUIUXBUXKXMXOXNVUJVUKHVULVUCUWTUXKXPXQXRUYTVUAVUBXSUYQV
        UCUWTUXLUXKXTYAYBYCYEUXGUXAUWBUYEUWPUXAUXEYDWDUWTUXMQYFYGYHYIUUHYJUUAUU
        BUWBUXJUYAAUXOSUWBUWJUXOFZUXJUWJSFZUYAHZUWBVUQVURUXPHZUXJVUSYKVUQUWJUXM
        FZUWJUXNFZUFZHUWBVUTUWJUXMUXNUUCUWBVVAVVCVUTVVAVURUWBVVCVUTYKUWJUXLUXKU
        UDUWBVURVVCVUTUWBVURVVCXSVURUXPUWBVURVVCUUEVVCUWBUXPVURVVBUWJQVVBUWJQPA
        QUUFUUGUUIYLUUJYMUUKYNYJUWBVUTUXJVUSUWBVUTUXJXSZVURUXPUXTUWBVURUXPUXJUU
        LUWBVURUXPUXJUUMVVDUXSEYORZEUXSYORZUXTUXSEEUUNZYORZVVGEUMRVVEVVGYPFUXSV
        VGYQVVHEEYRYRUUOZUXQBCEEUUPZUXSVVGYPYSUVIUUQUXSVVGEUUSUURVVDEUXIUMRZUXI
        UXSYORZVVFUXJUWBVVKVUTUXIEUUTYLUXSYPFVVDUXIUXSYQZVVLUXSVVGVVIVVJUVAUWBV
        UTVVMUXJUWBVUTHZUCUXIUXSUCUGZUXIFVVOUXHFZVVOIGZJKLZDVVOMGZJKLZNLZOLZUWJ
        PZHVVNVVOUXSFZUWKVWCUBVVOUXHUWCVVOPZUWIVWBUWJVWEUWEVVRUWHVWAOVWEUWDVVQJ
        KUWCVVOIVHVIVWEUWGVVTDNVWEUWFVVSJKUWCVVOMVHVIVLVJUVJUVBVVNVWCVVPVWDVVNV
        WCVVPVWDVVNVWCHZVVOUYDPZUXGHZCVFBVFVWGUXRHZCVFBVFVVPVWDVWFVWHVWIBCVWFVW
        HVWIVWFVWHHZVWGUWPUXQVWFVWGUXGYDVWFVWGUWPUXFWAVWJUWTVWBUWJVWGUWTVWBPVWF
        UXGVWGVWBUYMUWTVWGVVRUYIVWAUYLOVWGVVQUYHJKVVOUYDIVHVIVWGVVTUYKDNVWGVVSU
        YJJKVVOUYDMVHVIVLVJUYPUVCVTVVNVWCVWHWJUVDYTYIUVEUXGBCVVOVGUXRBCVVOVGUVF
        UVGUVHYJUVKUVLUXIUXSYPYSUVMEUXIUXSUVNXOUXSEUVOXAYTYMUVPYNUVQUVR $.
    $}

    ${
      pellex.ann $e |- ( ph -> A e. NN ) $. $( A,B first pigeon $)
      pellex.bnn $e |- ( ph -> B e. NN ) $.
      pellex.cz $e |- ( ph -> C e. ZZ ) $. $( common norm $)
      pellex.dnn $e |- ( ph -> D e. NN ) $. $( discriminant $)
      pellex.irr $e |- ( ph -> -. ( sqrt ` D ) e. QQ ) $.
      pellex.enn $e |- ( ph -> E e. NN ) $. $( E,F second pigeon $)
      pellex.fnn $e |- ( ph -> F e. NN ) $.
      pellex.neq $e |- ( ph -> -. ( A = E /\ B = F ) ) $.
      pellex.cn0 $e |- ( ph -> C =/= 0 ) $.
      pellex.no1 $e |- ( ph -> ( ( A ^ 2 ) - ( D x. ( B ^ 2 ) ) ) = C ) $.
      pellex.no2 $e |- ( ph -> ( ( E ^ 2 ) - ( D x. ( F ^ 2 ) ) ) = C ) $.
      pellex.xcg $e |- ( ph -> ( A mod ( abs ` C ) ) = ( E mod ( abs ` C ) ) )
          $.
      pellex.ycg $e |- ( ph -> ( B mod ( abs ` C ) ) = ( F mod ( abs ` C ) ) )
          $.

      $(
        math form:

        |(A+dB)/(E+dF)| = |(A+dB)(E-dF) / (E+dF)(E-dF)| =
          |(AE-DBF)+d(BE-AF)| / |EE+DFF=C| is the soln
        norm: (AE-DBF)(AE-DBF)-D(BE-AF)(BE-AF) / CC;
        AAEE-2AEDBF+DDBBFF-DBBEE+2DBEAF-DAAFF / CC
        AAEE+DDBBFF-DBBEE-DAAFF / CC
        (AA-DBB)EE-DFF(AA-DBB) / CC
        EE-DFF / C
        1
        divisibility: AE-DBF ~~ AA-DBB ~ C ~ 0 mod C; BE-AF ~~ FE-FE ~ 0
        nontriviality: via the norm, AE-DBF=0 implies d = AF-BE / CC
        contradicting irrationality.  BE-AF=0 means B/A = F/E = r; common norm
        then implies B=A and F=E
      $)

      $( Lemma for ~ pellex .  Doing a field division between near solutions
         get us to norm 1, and the modularity constraint ensures we still have
         an integer.  Returning NN guarantees that we are not returning the
         trivial solution (1,0).  We are not explicitly defining the
         Pell-field, Pell-ring, and Pell-norm explicitly because after this
         construction is done we will never use them.  This is mostly basic
         algebraic number theory and could be simplified if a generic framework
         for that were in place.  (Contributed by Stefan O'Rear,
         19-Oct-2014.) $)
      pellexlem6 $p |- ( ph -> E. a e. NN E. b e. NN ( ( a ^ 2 ) - ( D x. ( b ^
          2 ) ) ) = 1 ) $=
        ( cmul co cmin cdiv cabs cfv cn wcel c2 cexp c1 wceq cv wrex cz cc0 wne
        nncnd mulcld subcld absdivd cmo caddc negsubd eqcomd oveq1d cr remulcld
        cneg nnred renegcld nnzd modmul1 syl221anc sqcld sqvald resubcld abscld
        resqcld dividd eqeltrd wb syl2anc mpbird absmod0 3eqtr4d modadd1 oveq2d
        mod0 syl mul12d 3eqtrd eqtrd negidd redivcld absz cle wbr divcld nnnn0d
        mpbid nn0ge0d wa absresq sqdivd cc sqne0 3eqtr2d oveq12d mulsubd addcld
        subdid adddid mulcomd mulassd sqmuld eqtr4d subdird eqtr3d subdi negeqd
        clt w3a syl3anc 3eqtr3d adantr simpr neqned divne0d nnne0d oveq1 adantl
        nnabscl divcan1d csqrt ad2antrr ex mullidd zcnd crp npcand eqtr2d recnd
        absrpcld 0red absne0d 1zzd zred 0mod addlidd zmulcld wn 0lt1 0re ltnlei
        1re mpbi mulge0d suble0d breq1 syl5ibrcom mtoi divassd divsubdird mul4d
        sqge0d nnncan2d addsub4d mulneg2d mulneg1d fvoveq1d div0d abs00bd sq0id
        negsubdi2 mtand negsub divmuleqd divcan4d nngt0d syl22anc sqrtsqd fveq2
        divge0 sqrt1 a1i simplr jca syld sylbird mtod subne0d eqeq1d rspc2ev
        mpd ) ABFUCUDZECGUCUDZUCUDZUEUDZDUFUDZUGUHZUIUJZCFUCUDZBGUCUDZUEUDZDUFU
        DZUGUHZUIUJZUXCUKULUDZEUXIUKULUDZUCUDZUEUDZUMUNZHUOZUKULUDZEIUOZUKULUDZ
        UCUDZUEUDZUMUNZIUIUPHUIUPAUXBUQUJZUXBURUSUXDAUYCUXCUQUJZAUXCUXAUGUHZDUG
        UHZUFUDZUQAUXADAUWRUWTABFABJUTZAFOUTZVAZAEUWSAEMUTZACGACKUTZAGPUTZVAZVA
        ZVBZADLUUAZRVCAUYEUYFVDUDURUNZUYGUQUJZAUXAUYFVDUDZURUNZUYRAUYTURUYFVDUD
        ZURAUYTUWRUWTVKZVEUDZUYFVDUDZUWTVUCVEUDZUYFVDUDZVUBAUXAVUDUYFVDAVUDUXAA
        UWRUWTUYJUYOVFVGVHAUWRVIUJUWTVIUJVUCVIUJUYFUUBUJZUWRUYFVDUDZUWTUYFVDUDZ
        UNVUEVUGUNABFABJVLZAFOVLZVJZAEUWSAEMVLZACGACKVLZAGPVLZVJVJZAUWTVUQVMADU
        YQRUUFZAVUIFFUCUDZUYFVDUDZGEGUCUDZUCUDZUYFVDUDZVUJABVIUJZFVIUJZFUQUJZVU
        HBUYFVDUDFUYFVDUDUNZVUIVUTUNVUKVULAFOVNZVURUABFFUYFVOVPAVUTFUKULUDZEGUK
        ULUDZUCUDZUEUDZVVKVEUDZUYFVDUDZURVVKVEUDZUYFVDUDZVVCAVUSVVMUYFVDAVVMVVI
        VUSAVVIVVKAFUYIVQZAEVVJUYKAGUYMVQZVAZUUCAFUYIVRUUDVHAVVLVIUJURVIUJVVKVI
        UJVUHVVLUYFVDUDZVUBUNVVNVVPUNAVVIVVKAFVULWAAEVVJVUNAGVUPWAVJZVSAUUGZVWA
        VURADUYFVDUDZURVVTVUBAVWCURUNZUYFUYFVDUDURUNZAVWEUYFUYFUFUDZUQUJZAVWFUM
        UQAUYFAUYFADUYQVTZUUEADUYQRUUHWBAUUIWCAUYFVIUJVUHVWEVWGWDVWHVURUYFUYFWK
        WEWFADVIUJVUHVWDVWEWDADLUUJZVURDUYFWGWEWFAVVLDUYFVDTVHAVUHVUBURUNVURUYF
        UUKWLZWHVVLURVVKUYFWIVPAVVOVVBUYFVDAVVOVVKEGGUCUDZUCUDVVBAVVKVVSUULAVVJ
        VWKEUCAGUYMVRWJAEGGUYKUYMUYMWMWNVHWNAVVCCVVAUCUDZUYFVDUDZVUJAGVIUJZCVIU
        JZVVAUQUJVUHGUYFVDUDZCUYFVDUDZUNVVCVWMUNVUPVUOAEGAEMVNAGPVNZUUMVURAVWQV
        WPUBVGGCVVAUYFVOVPAVWLUWTUYFVDACEGUYLUYKUYMWMVHWOWNUWRUWTVUCUYFWIVPAVUF
        URUYFVDAUWTUYOWPVHWNVWJWOAUXAVIUJVUHVUAUYRWDAUWRUWTVUMVUQVSZVURUXAUYFWG
        WEXCAUYEVIUJVUHUYRUYSWDAUXAUYPVTVURUYEUYFWKWEXCWCAUXBVIUJZUYCUYDWDAUXAD
        VWSVWIRWQZUXBWRWLWFAUXADUYPUYQAUXAURAUXAURUNZUMURUXMUEUDZUNZAVXDUMURWSW
        TZURUMYDWTVXEUUNUUOURUMUUPUURUUQUUSAVXEVXDVXCURWSWTZAVXFURUXMWSWTAEUXLV
        UNAUXIAUXHAUXGDAUXEUXFACFUYLUYIVAZABGUYHUYMVAZVBZUYQRXAVTZWAZAEAEMXBXDA
        UXIVXJUVHUUTAURUXMVWBAEUXLVUNVXKVJUVAWFUMVXCURWSUVBUVCUVDAVXBXEZUXNUMVX
        CAUXOVXBAUXNUXAUXAUCUDZDUKULUDZUFUDZEUXGUXGUCUDZUCUDZVXNUFUDZUEUDVXMVXQ
        UEUDZVXNUFUDZUMAUXKVXOUXMVXRUEAUXKUXBUKULUDZUXAUKULUDZVXNUFUDVXOAVWTUXK
        VYAUNVXAUXBXFWLAUXADUYPUYQRXGAVYBVXMVXNUFAUXAUYPVRVHWNAUXMEUXGUKULUDZVX
        NUFUDZUCUDEVYCUCUDZVXNUFUDVXRAUXLVYDEUCAUXLUXHUKULUDZVYDAUXHVIUJZUXLVYF
        UNAUXGDAUXEUXFACFVUOVULVJZABGVUKVUPVJZVSZVWIRWQZUXHXFWLAUXGDVXIUYQRXGWO
        WJAEVYCVXNUYKAUXGVXIVQADUYQVQZAVXNURUSZDURUSZRADXHUJZVYMVYNWDUYQDXIWLWF
        ZUVEAVYEVXQVXNUFAVYCVXPEUCAUXGVXIVRWJVHXJXKAVXMVXQVXNAUXAUXAUYPUYPVAAEV
        XPUYKAUXGUXGVXIVXIVAVAVYLVYPUVFAVXTUWRUWRUCUDZUWTUWTUCUDZVEUDZUWRUWTUCU
        DZVYTVEUDZUEUDZEUXEUXEUCUDZUCUDZEUXFUXFUCUDZUCUDZVEUDZEUXEUXFUCUDZUCUDZ
        WUIVEUDZUEUDZUEUDZVXNUFUDVXNVXNUFUDUMAVXSWULVXNUFAVXMWUBVXQWUKUEAUWRUWT
        UWRUWTUYJUYOUYJUYOXLAVXQEWUCWUEVEUDZWUHWUHVEUDZUEUDZUCUDEWUMUCUDZEWUNUC
        UDZUEUDWUKAVXPWUOEUCAUXEUXFUXEUXFVXGVXHVXGVXHXLWJAEWUMWUNUYKAWUCWUEAUXE
        UXEVXGVXGVAZAUXFUXFVXHVXHVAZXMAWUHWUHAUXEUXFVXGVXHVAZWUTXMXNAWUPWUGWUQW
        UJUEAEWUCWUEUYKWURWUSXOAEWUHWUHUYKWUTWUTXOXKWNXKVHAWULVXNVXNUFAWULVYSWU
        JUEUDZWUKUEUDVYSWUGUEUDZVXNAWUBWVAWUKUEAWUAWUJVYSUEAVYTWUIVYTWUIVEAVYTU
        WTUWRUCUDEUWSUWRUCUDZUCUDWUIAUWRUWTUYJUYOXPAEUWSUWRUYKUYNUYJXQAWVCWUHEU
        CAWVCUWSFBUCUDZUCUDUXEGBUCUDZUCUDWUHAUWRWVDUWSUCABFUYHUYIXPWJACGFBUYLUY
        MUYIUYHUVGAWVEUXFUXEUCAGBUYMUYHXPWJWNWJWNZWVFXKWJVHAVYSWUGWUJAVYQVYRAUW
        RUWRUYJUYJVAZAUWTUWTUYOUYOVAZXMAWUDWUFAEWUCUYKWURVAZAEWUEUYKWUSVAZXMAWU
        IWUIAEWUHUYKWUTVAZWVKXMUVIAWVBVYQWUDUEUDZVYRWUFUEUDZVEUDUWRUKULUDZEUXEU
        KULUDZUCUDZUEUDZUWTUKULUDZEUXFUKULUDZUCUDZUEUDZVEUDZVXNAVYQVYRWUDWUFWVG
        WVHWVIWVJUVJAWVQWVLWWAWVMVEAWVNVYQWVPWUDUEAUWRUYJVRAWVOWUCEUCAUXEVXGVRW
        JXKAWVRVYRWVTWUFUEAUWTUYOVRAWVSWUEEUCAUXFVXHVRWJXKXKAWWBBUKULUDZVVIUCUD
        ZECUKULUDZUCUDZVVIUCUDZUEUDZEEUCUDZWWEUCUDZVVJUCUDZEWWCUCUDZVVJUCUDZUEU
        DZVEUDDVVIUCUDZEDUCUDZVKZVVJUCUDZVEUDZVXNAWVQWWHWWAWWNVEAWVNWWDWVPWWGUE
        ABFUYHUYIXRAWVPEWWEVVIUCUDZUCUDWWGAWVOWWTEUCACFUYLUYIXRWJAEWWEVVIUYKACU
        YLVQZVVQXQXSXKAWVRWWKWVTWWMUEAEUKULUDZUWSUKULUDZUCUDWWIWWEVVJUCUDZUCUDW
        VRWWKAWXBWWIWXCWXDUCAEUYKVRACGUYLUYMXRXKAEUWSUYKUYNXRAWWIWWEVVJAEEUYKUY
        KVAZWXAVVRXQWHAWVTEWWCVVJUCUDZUCUDWWMAWVSWXFEUCABGUYHUYMXRWJAEWWCVVJUYK
        ABUYHVQZVVRXQXSXKXKAWWHWWOWWNWWRVEAWWCWWFUEUDZVVIUCUDWWHWWOAWWCWWFVVIWX
        GAEWWEUYKWXAVAZVVQXTAWXHDVVIUCSVHYAAWWJWWLUEUDZVVJUCUDEWWFUCUDZWWLUEUDZ
        VVJUCUDWWNWWRAWXJWXLVVJUCAWWJWXKWWLUEAEEWWEUYKUYKWXAXQVHVHAWWJWWLVVJAWW
        IWWEWXEWXAVAAEWWCUYKWXGVAVVRXTAWXLWWQVVJUCAWXLEWWFWWCUEUDZUCUDZEDVKZUCU
        DWWQAEXHUJZWWFXHUJZWWCXHUJZWXLWXNUNUYKWXIWXGWXPWXQWXRYEWXNWXLEWWFWWCYBV
        GYFAWXMWXOEUCAWXMWXHVKZWXOAWXRWXQWXMWXSUNWXGWXIWXRWXQXEWXSWXMWWCWWFUVQV
        GWEAWXHDSYCWOWJAEDUYKUYQUVKWNVHYGXKAWWSWWODVVKUCUDZVKZVEUDWWOWXTUEUDZVX
        NAWWRWYAWWOVEAWWRWWPVVJUCUDZVKWYAAWWPVVJAEDUYKUYQVAVVRUVLAWYCWXTAWYCDEU
        CUDZVVJUCUDWXTAWWPWYDVVJUCAEDUYKUYQXPVHADEVVJUYQUYKVVRXQWOYCWOWJAWWOWXT
        ADVVIUYQVVQVAADVVKUYQVVSVAVFADVVLUCUDZDDUCUDWYBVXNAVVLDDUCTWJAVYOVVIXHU
        JZVVKXHUJZWYBWYEUNUYQVVQVVSVYOWYFWYGYEWYEWYBDVVIVVKYBVGYFADUYQVRWHWNWNX
        JWNVHAVXNVYLVYPWBWNXJZYHVXLUXKURUXMUEVXLUXCVXLUXCURDUFUDZUGUHZURVXLUXAU
        RDUGUFAVXBYIUVMAWYJURUNVXBAWYIADUYQRUVNUVOYHWOUVPVHYAUVRYJRYKUXBYOWEAUX
        HUQUJZUXHURUSUXJAWYKUXIUQUJZAUXIUXGUGUHZUYFUFUDZUQAUXGDVXIUYQRVCAWYMUYF
        VDUDURUNZWYNUQUJZAUXGUYFVDUDZURUNZWYOAWYQVUBURAWYQUXEUXFVKZVEUDZUYFVDUD
        ZUXFWYSVEUDZUYFVDUDZVUBAUXGWYTUYFVDAUXEXHUJZUXFXHUJZUXGWYTUNVXGVXHXUDXU
        EXEWYTUXGUXEUXFUVSVGWEVHAUXEVIUJUXFVIUJWYSVIUJVUHUXEUYFVDUDZUXFUYFVDUDZ
        UNXUAXUCUNVYHVYIAUXFVYIVMVURAGFUCUDZUYFVDUDZFGUCUDZUYFVDUDZXUFXUGAXUHXU
        JUYFVDAGFUYMUYIXPVHAVWOVWNVVFVUHVWQVWPUNXUFXUIUNVUOVUPVVHVURUBCGFUYFVOV
        PAVVDVVEGUQUJVUHVVGXUGXUKUNVUKVULVWRVURUABFGUYFVOVPWHUXEUXFWYSUYFWIVPAX
        UBURUYFVDAUXFVXHWPVHWNVWJWOAUXGVIUJVUHWYRWYOWDVYJVURUXGUYFWGWEXCAWYMVIU
        JVUHWYOWYPWDAUXGVXIVTVURWYMUYFWKWEXCWCAVYGWYKWYLWDVYKUXHWRWLWFAUXGDVXIU
        YQAUXEUXFVXGVXHAUXEUXFAUXEUXFUNZBFUNZCGUNZXEZQAXULCGUFUDZBFUFUDZUNZXUOA
        CGBFUYLUYMUYHUYIAGPYLZAFOYLZUVTAXURXUOAXURXEZXUPUKULUDZUMUNZXUOXVAXVBDU
        CUDZDUFUDWXHWXHUFUDZXVBUMXVAXVDWXHDWXHUFXVAXVDXVBVVLUCUDXVBVVIUCUDZXVBV
        VKUCUDZUEUDWXHXVADVVLXVBUCXVAVVLDAVVLDUNXURTYHVGWJXVAXVBVVIVVKAXVBXHUJX
        URAXUPACGUYLUYMXUSXAVQYHZAWYFXURVVQYHZAWYGXURVVSYHXNXVAXVFWWCXVGWWFUEXV
        AXVFXUQUKULUDZVVIUCUDZWWCVVIUFUDZVVIUCUDWWCXURXVFXVKUNAXURXVBXVJVVIUCXU
        PXUQUKULYMVHYNXVAXVJXVLVVIUCXVABFABXHUJXURUYHYHAFXHUJZXURUYIYHAFURUSZXU
        RXUTYHXGVHXVAWWCVVIAWXRXURWXGYHXVIAVVIURUSZXURAXVOXVNXUTAXVMXVOXVNWDUYI
        FXIWLWFYHYPWNXVAXVGEXVBVVJUCUDZUCUDEWWEVVJUFUDZVVJUCUDZUCUDWWFXVAXVBEVV
        JXVHAWXPXURUYKYHAVVJXHUJXURVVRYHZWMXVAXVPXVREUCXVAXVBXVQVVJUCXVACGACXHU
        JXURUYLYHAGXHUJZXURUYMYHAGURUSZXURXUSYHXGVHWJXVAXVRWWEEUCXVAWWEVVJAWWEX
        HUJXURWXAYHXVSAVVJURUSZXURAXWBXWAXUSAXVTXWBXWAWDUYMGXIWLWFYHYPWJWNXKWNA
        DWXHUNXURAWXHDSVGYHXKXVAXVBDXVHAVYOXURUYQYHAVYNXURRYHUWAAXVEUMUNXURAXVE
        DDUFUDUMAWXHDWXHDUFSSXKADUYQRWBWOYHYGXVAXVCXUPUMUNZXUOXVAXVCXWCXVAXVCXE
        ZXUPXVBYQUHZUMYQUHZUMAXUPXWEUNXURXVCAXWEXUPAXUPACGVUOVUPXUSWQAVWOURCWSW
        TVWNURGYDWTURXUPWSWTVUOACACKXBXDVUPAGPUWBCGUWFUWCUWDVGYRXVCXWEXWFUNXVAX
        VBUMYQUWEYNXWFUMUNXWDUWGUWHWNYSXVAXWCXUOXVAXWCXEZXUMXUNXWGXUQFUCUDZUMFU
        CUDZBFXWGXUQUMFUCXWGXUPXUQUMAXURXWCUWIXVAXWCYIZYAVHAXWHBUNXURXWCABFUYHU
        YIXUTYPYRAXWIFUNXURXWCAFUYIYTYRYGXWGXUPGUCUDZUMGUCUDZCGXWGXUPUMGUCXWJVH
        AXWKCUNXURXWCACGUYLUYMXUSYPYRAXWLGUNXURXWCAGUYMYTYRYGUWJYSUWKUWQYSUWLUW
        MYJUWNRYKUXHYOWEWYHUYBUXOUXKUXTUEUDZUMUNHIUXCUXIUIUIUXPUXCUNZUYAXWMUMXW
        NUXQUXKUXTUEUXPUXCUKULYMVHUWOUXRUXIUNZXWMUXNUMXWOUXTUXMUXKUEXWOUXSUXLEU
        CUXRUXIUKULYMWJWJUWOUWPYF $.
    $}

    ${
      $d D x y $.
      $( Every Pell equation has a nontrivial solution.  Theorem 62 in
         [vandenDries] p. 43.  (Contributed by Stefan O'Rear, 19-Oct-2014.) $)
      pellex $p |- ( ( D e. NN /\ -. ( sqrt ` D ) e. QQ ) -> E. x e. NN E. y e.
          NN ( ( x ^ 2 ) - ( D x. ( y ^ 2 ) ) ) = 1 ) $=
        ( vb vc vf vg cn wcel cfv wa cv c2 cexp co wceq wbr c1st cmo c2nd va vd
        ve csqrt cq wn cc0 wne cmul cmin copab cen c1 wrex cz cabs cop cfz csdm
        cxp fzfi xpfi mp2an isfinite mpbi nnenom ensymi sdomentr ensym ad2antll
        com cfn sylancr opabssxp sseli cvv simprrl nnzd simpllr nnabscl syl2anc
        simplr zmodfz simprrr jca ex elxp7 opelxp 3imtr4g syl5 imp adantlrr weq
        fveq2 oveq1d opeq12d wi eleq1w bi2anan9 oveq2d oveqan12d eqeq1d anbi12d
        fphpd oveq1 cbvopabv eleq2i biimpi wex elopab w3a simp3ll 3expb simp3lr
        3ad2ant1 simp1lr 3adant1r simp-4l simp-4r simp2ll simp2lr simp2l simp3l
        3adant2l simp1rl simp3 simp2 simp1 opth sylib syl3anc ovex fveq2d op1st
        vex eqtrdi 3eqtr3d op2nd exlimdvv biimtrid 3netr3d simp3r simprl simpll
        necon3abii simp1rr 3adant1l simp2rr simprr mpd simpld simprd pellexlem6
        3adant3 3exp impd sylan2i rexlimdvv mpdan pellexlem5 r19.29a ) CHIZCUDJ
        UEIUFZKZUALZUGUHZDLZHIZELZHIZKZUVGMNOZCUVIMNOZUIOZUJOZUVEPZKZDEUKZHULQZ
        KZALMNOCBLMNOUIOUJOUMPBHUNAHUNZUAUOUVDUVEUOIZKZUVTKZUBLZUCLZUHZUWERJZUV
        EUPJZSOZUWETJZUWISOZUQZUWFRJZUWISOZUWFTJZUWISOZUQZPZKZUCUVRUNUBUVRUNZUW
        AUWDUBUCUVRUGUWIUMUJOZUROZUXCUTZUWMUWRUWDUXDHUSQZHUVRULQZUXDUVRUSQUXDVK
        USQZVKHULQUXEUXDVLIZUXGUXCVLIZUXIUXHUGUXBVAZUXJUXCUXCVBVCUXDVDVEHVKVFVG
        UXDVKHVHVCUVSUXFUWCUVFUVRHVIVJUXDHUVRVHVMUWCUVFUWEUVRIZUWMUXDIZUVSUWCUV
        FKZUXKUXLUXKUWEHHUTZIZUXMUXLUVRUXNUWEUVPDEHHVNVOUXMUWEVPVPUTIZUWHHIZUWK
        HIZKKZUWJUXCIZUWLUXCIZKZUXOUXLUXMUXSUYBUXMUXSKZUXTUYAUYCUWHUOIUWIHIZUXT
        UYCUWHUXMUXPUXQUXRVQVRUYCUWBUVFUYDUVDUWBUVFUXSVSUWCUVFUXSWBUVEVTWAZUWHU
        WIWCWAUYCUWKUOIUYDUYAUYCUWKUXMUXPUXQUXRWDVRUYEUWKUWIWCWAWEWFUWEHHWGUWJU
        WLUXCUXCWHWIWJWKWLUBUCWMZUWJUWOUWLUWQUYFUWHUWNUWISUWEUWFRWNWOUYFUWKUWPU
        WISUWEUWFTWNWOWPXDUWCUVFUXAUWAUVSUXMUXAUWAUXMUWTUWAUBUCUVRUVRUWFUVRIZUX
        MUXKUWFFLZHIZGLZHIZKZUYHMNOZCUYJMNOZUIOZUJOZUVEPZKZFGUKZIZUWTUWAWQZUYGU
        YTUVRUYSUWFUVQUYRDEFGDFWMZEGWMZKZUVKUYLUVPUYQVUBUVHUYIVUCUVJUYKDFHWREGH
        WRWSVUDUVOUYPUVEVUBVUCUVLUYMUVNUYOUJUVGUYHMNXEVUCUVMUYNCUIUVIUYJMNXEWTX
        AXBXCXFXGXHUXMUXKUYTVUAUXKUWEUVGUVIUQZPZUVQKZEXIDXIUXMUYTVUAWQZUVQDEUWE
        XJUXMVUGVUHDEUXMVUGVUHUYTUWFUYHUYJUQZPZUYRKZGXIFXIUXMVUGKZVUAUYRFGUWFXJ
        VULVUKVUAFGVULVUKUWTUWAVULVUKUWTXKZUVGUVIUVECUYHUYJABVULVUKUVHUWTUXMVUF
        UVQUVHUVHUVJUVPUXMVUFXLXMXOVULVUKUVJUWTUXMVUFUVQUVJUVHUVJUVPUXMVUFXNXMX
        OUXMVUKUWTUWBVUGUVDUWBUVFVUKUWTXPXQVULVUKUVBUWTUVBUVCUWBUVFVUGXRXOVULVU
        KUVCUWTUVBUVCUWBUVFVUGXSXOVULUYRUWTUYIVUJUYIUYKUYQVULUWTXTYDVULUYRUWTUY
        KVUJUYIUYKUYQVULUWTYAYDVUMVUJVUFUWGVUDUFZVULVUJUYRUWTYBZVUFUVQUXMVUKUWT
        YEZVULVUKUWGUWSYCVUJVUFUWGXKZVUEVUIUHVUNVUQUWEUWFVUEVUIVUJVUFUWGYFVUJVU
        FUWGYGVUJVUFUWGYHUUAVUDVUEVUIUVGUVIUYHUYJDYOZEYOZYIUUEYJYKUWCUVFVUGVUKU
        WTXPVUGVUKUWTUVPUXMUVKUVPVUFVUKUWTUUFUUGUYLUYQVUJVULUWTUUHVUMUVGUWISOZU
        YHUWISOZPZUVIUWISOZUYJUWISOZPZVUMVUFVUJUWSVVBVVEKZVUPVUOVULVUKUWGUWSUUB
        VUFVUJUWSXKZUWJUWOPZUWLUWQPZKZVVFVVGUWSVVJVUFVUJUWSYFUWJUWLUWOUWQUWHUWI
        SYLUWKUWISYLYIYJVUFVUJVVJVVFWQUWSVUFVUJKZVVJVVFVVKVVJKZVVBVVEVVLUWJUWOV
        UTVVAVVKVVHVVIUUCVVLUWHUVGUWISVVLUWHVUERJUVGVVLUWEVUERVUFVUJVVJUUDZYMUV
        GUVIVURVUSYNYPWOVVLUWNUYHUWISVVLUWNVUIRJUYHVVLUWFVUIRVUFVUJVVJWBZYMUYHU
        YJFYOZGYOZYNYPWOYQVVLUWLUWQVVCVVDVVKVVHVVIUUIVVLUWKUVIUWISVVLUWKVUETJUV
        IVVLUWEVUETVVMYMUVGUVIVURVUSYRYPWOVVLUWPUYJUWISVVLUWPVUITJUYJVVLUWFVUIT
        VVNYMUYHUYJVVOVVPYRYPWOYQWEWFUUNUUJYKZUUKVUMVVBVVEVVQUULUUMUUOYSYTWFYSY
        TUUPUUQUURWKWLUUSUADECUUTUVA $.
    $}
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Pell equations 2: Algebraic number theory of the solution set
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c Pell1QR Pell14QR Pell1234QR PellFund []NN $.

  ${
    $d a b c d e f A $.  $d a b c d e f B $.  $d a b c d e f D $.
    $d a b c d e f w $.  $d a b c d e f x $.  $d a b c d e f y $.
    $d a b c d e f z $.

    $( define image of ZZ or NN $)
    $( prove non-denseness $)
    $( use logarithms to show all elements are powers of a base $)
    $( value of PellFund ` a*a-1 $)
    $( define Ak, Bk $)
    $( Lucas sequence $)

    $( Extend class notation to include the set of square positive integers. $)
    csquarenn $a class []NN $.
    $( Extend class notation to include the class of quadrant-1 Pell
       solutions. $)
    cpell1qr $a class Pell1QR $.
    $( Extend class notation to include the class of any-quadrant Pell
       solutions. $)
    cpell1234qr $a class Pell1234QR $.
    $( Extend class notation to include the class of positive Pell
       solutions. $)
    cpell14qr $a class Pell14QR $.
    $( Extend class notation to include the Pell-equation fundamental solution
       function. $)
    cpellfund $a class PellFund $.

    $( Define the set of square positive integers.  (Contributed by Stefan
       O'Rear, 18-Sep-2014.) $)
    df-squarenn $a |- []NN = { x e. NN | ( sqrt ` x ) e. QQ } $.

    ${
      $d x y z w $.
      $( Define the solutions of a Pell equation in the first quadrant.  To
         avoid pair pain, we represent this via the canonical embedding into
         the reals.  (Contributed by Stefan O'Rear, 17-Sep-2014.) $)
      df-pell1qr $a |- Pell1QR = ( x e. ( NN \ []NN ) |-> { y e. RR | E. z e.
          NN0 E. w e. NN0 ( y = ( z + ( ( sqrt ` x ) x. w ) ) /\ ( ( z ^ 2 ) -
          ( x x. ( w ^ 2 ) ) ) = 1 ) } ) $.
      $( Define the positive solutions of a Pell equation.  (Contributed by
         Stefan O'Rear, 17-Sep-2014.) $)
      df-pell14qr $a |- Pell14QR = ( x e. ( NN \ []NN ) |-> { y e. RR | E. z e.
          NN0 E. w e. ZZ ( y = ( z + ( ( sqrt ` x ) x. w ) ) /\ ( ( z ^ 2 ) - (
          x x. ( w ^ 2 ) ) ) = 1 ) } ) $.
      $( Define the general solutions of a Pell equation.  (Contributed by
         Stefan O'Rear, 17-Sep-2014.) $)
      df-pell1234qr $a |- Pell1234QR = ( x e. ( NN \ []NN ) |-> { y e. RR | E.
          z e. ZZ E. w e. ZZ ( y = ( z + ( ( sqrt ` x ) x. w ) ) /\ ( ( z ^ 2 )
          - ( x x. ( w ^ 2 ) ) ) = 1 ) } ) $.
      $( A function mapping Pell discriminants to the corresponding fundamental
         solution.  (Contributed by Stefan O'Rear, 18-Sep-2014.)  (Revised by
         AV, 17-Sep-2020.) $)
      df-pellfund $a |- PellFund = ( x e. ( NN \ []NN ) |-> inf ( { z e. (
          Pell14QR ` x ) | 1 < z } , RR , < ) ) $.
    $}

    ${
      $d y z w D $.  $d y z w A $.
      $( Value of the set of first-quadrant Pell solutions.  (Contributed by
         Stefan O'Rear, 17-Sep-2014.) $)
      pell1qrval $p |- ( D e. ( NN \ []NN ) -> ( Pell1QR ` D ) = { y e. RR | E.
          z e. NN0 E. w e. NN0 ( y = ( z + ( ( sqrt ` D ) x. w ) ) /\ ( ( z ^ 2
          ) - ( D x. ( w ^ 2 ) ) ) = 1 ) } ) $=
        ( va cv csqrt cfv cmul co caddc wceq c2 cexp cmin c1 wa cn0 wrex cr cn
        crab csquarenn cpell1qr fveq2 oveq1d oveq2d eqeq2d oveq1 eqeq1d anbi12d
        cdif 2rexbidv rabbidv df-pell1qr reex rabex fvmpt ) EDAFZBFZEFZGHZCFZIJ
        ZKJZLZUTMNJZVAVCMNJZIJZOJZPLZQZCRSBRSZATUBUSUTDGHZVCIJZKJZLZVGDVHIJZOJZ
        PLZQZCRSBRSZATUBUAUCULUDVADLZVMWBATWCVLWABCRRWCVFVQVKVTWCVEVPUSWCVDVOUT
        KWCVBVNVCIVADGUEUFUGUHWCVJVSPWCVIVRVGOVADVHIUIUGUJUKUMUNEABCUOWBATUPUQU
        R $.

      $( Membership in a first-quadrant Pell solution set.  (Contributed by
         Stefan O'Rear, 17-Sep-2014.) $)
      elpell1qr $p |- ( D e. ( NN \ []NN ) -> ( A e. ( Pell1QR ` D ) <-> ( A e.
          RR /\ E. z e. NN0 E. w e. NN0 ( A = ( z + ( ( sqrt ` D ) x. w ) ) /\
          ( ( z ^ 2 ) - ( D x. ( w ^ 2 ) ) ) = 1 ) ) ) ) $=
        ( va cn csquarenn cdif wcel cfv cv cmul co wceq c2 cexp wa cn0 wrex cr
        cpell1qr csqrt caddc cmin pell1qrval eleq2d eqeq1 anbi1d 2rexbidv elrab
        c1 crab bitrdi ) DFGHIZCDUAJZICEKZAKZDUBJBKZLMUCMZNZUQOPMDUROPMLMUDMUKN
        ZQZBRSARSZETULZICTICUSNZVAQZBRSARSZQUNUOVDCEABDUEUFVCVGECTUPCNZVBVFABRR
        VHUTVEVAUPCUSUGUHUIUJUM $.

      $( Value of the set of positive Pell solutions.  (Contributed by Stefan
         O'Rear, 17-Sep-2014.) $)
      pell14qrval $p |- ( D e. ( NN \ []NN ) -> ( Pell14QR ` D ) = { y e. RR |
          E. z e. NN0 E. w e. ZZ ( y = ( z + ( ( sqrt ` D ) x. w ) ) /\ ( ( z ^
          2 ) - ( D x. ( w ^ 2 ) ) ) = 1 ) } ) $=
        ( va cv csqrt cfv cmul co caddc wceq c2 cexp cmin c1 cz wrex cn0 cr wa
        crab csquarenn cdif cpell14qr fveq2 oveq1d oveq2d eqeq2d eqeq1d anbi12d
        cn oveq1 2rexbidv rabbidv df-pell14qr reex rabex fvmpt ) EDAFZBFZEFZGHZ
        CFZIJZKJZLZVAMNJZVBVDMNJZIJZOJZPLZUAZCQRBSRZATUBUTVADGHZVDIJZKJZLZVHDVI
        IJZOJZPLZUAZCQRBSRZATUBULUCUDUEVBDLZVNWCATWDVMWBBCSQWDVGVRVLWAWDVFVQUTW
        DVEVPVAKWDVCVOVDIVBDGUFUGUHUIWDVKVTPWDVJVSVHOVBDVIIUMUHUJUKUNUOEABCUPWC
        ATUQURUS $.

      $( Membership in the set of positive Pell solutions.  (Contributed by
         Stefan O'Rear, 17-Sep-2014.) $)
      elpell14qr $p |- ( D e. ( NN \ []NN ) -> ( A e. ( Pell14QR ` D ) <-> ( A
          e. RR /\ E. z e. NN0 E. w e. ZZ ( A = ( z + ( ( sqrt ` D ) x. w ) )
          /\ ( ( z ^ 2 ) - ( D x. ( w ^ 2 ) ) ) = 1 ) ) ) ) $=
        ( va cn csquarenn wcel cfv cv cmul co wceq c2 cexp wa cz wrex cn0 cr c1
        cdif cpell14qr csqrt caddc cmin crab pell14qrval eleq2d anbi1d 2rexbidv
        eqeq1 elrab bitrdi ) DFGUBHZCDUCIZHCEJZAJZDUDIBJZKLUELZMZURNOLDUSNOLKLU
        FLUAMZPZBQRASRZETUGZHCTHCUTMZVBPZBQRASRZPUOUPVECEABDUHUIVDVHECTUQCMZVCV
        GABSQVIVAVFVBUQCUTULUJUKUMUN $.

      $( Value of the set of general Pell solutions.  (Contributed by Stefan
         O'Rear, 17-Sep-2014.) $)
      pell1234qrval $p |- ( D e. ( NN \ []NN ) -> ( Pell1234QR ` D ) = { y e.
          RR | E. z e. ZZ E. w e. ZZ ( y = ( z + ( ( sqrt ` D ) x. w ) ) /\ ( (
          z ^ 2 ) - ( D x. ( w ^ 2 ) ) ) = 1 ) } ) $=
        ( vd cv csqrt cfv cmul co caddc wceq c2 cexp cmin c1 wa cz wrex cr crab
        cn csquarenn cdif cpell1234qr fveq2 oveq1d oveq2d eqeq2d eqeq1d anbi12d
        oveq1 2rexbidv rabbidv df-pell1234qr reex rabex fvmpt ) EDAFZBFZEFZGHZC
        FZIJZKJZLZUTMNJZVAVCMNJZIJZOJZPLZQZCRSBRSZATUAUSUTDGHZVCIJZKJZLZVGDVHIJ
        ZOJZPLZQZCRSBRSZATUAUBUCUDUEVADLZVMWBATWCVLWABCRRWCVFVQVKVTWCVEVPUSWCVD
        VOUTKWCVBVNVCIVADGUFUGUHUIWCVJVSPWCVIVRVGOVADVHIULUHUJUKUMUNEABCUOWBATU
        PUQUR $.

      $( Membership in the set of general Pell solutions.  (Contributed by
         Stefan O'Rear, 17-Sep-2014.) $)
      elpell1234qr $p |- ( D e. ( NN \ []NN ) -> ( A e. ( Pell1234QR ` D ) <->
          ( A e. RR /\ E. z e. ZZ E. w e. ZZ ( A = ( z + ( ( sqrt ` D ) x. w )
          ) /\ ( ( z ^ 2 ) - ( D x. ( w ^ 2 ) ) ) = 1 ) ) ) ) $=
        ( va cn csquarenn cdif wcel cfv cv cmul co wceq c2 cexp wa cz wrex cr
        cpell1234qr csqrt caddc cmin pell1234qrval eleq2d eqeq1 anbi1d 2rexbidv
        c1 crab elrab bitrdi ) DFGHIZCDUAJZICEKZAKZDUBJBKZLMUCMZNZUQOPMDUROPMLM
        UDMUJNZQZBRSARSZETUKZICTICUSNZVAQZBRSARSZQUNUOVDCEABDUEUFVCVGECTUPCNZVB
        VFABRRVHUTVEVAUPCUSUGUHUIULUM $.
    $}

    $( General Pell solutions are (coded as) real numbers.  (Contributed by
       Stefan O'Rear, 17-Sep-2014.) $)
    pell1234qrre $p |- ( ( D e. ( NN \ []NN ) /\ A e. ( Pell1234QR ` D ) ) -> A
        e. RR ) $=
      ( va vb cn csquarenn cdif wcel cpell1234qr cfv cr cv csqrt cmul wceq cexp
      co c2 cz wrex caddc cmin c1 wa elpell1234qr simprbda ) BEFGHABIJHAKHACLZB
      MJDLZNQUAQOUGRPQBUHRPQNQUBQUCOUDDSTCSTCDABUEUF $.

    $( No solution to a Pell equation is zero.  (Contributed by Stefan O'Rear,
       17-Sep-2014.) $)
    pell1234qrne0 $p |- ( ( D e. ( NN \ []NN ) /\ A e. ( Pell1234QR ` D ) ) ->
        A =/= 0 ) $=
      ( va vb cn csquarenn wcel cfv cc0 wne cmul co wceq c2 cexp cmin c1 wa cz
      cc cdif cpell1234qr cr csqrt caddc wrex elpell1234qr simprl eldifi adantr
      cv ax-1ne0 nncnd ad3antrrr sqrtcld ad2antll ad2antrr sqmuld oveq1d eqtr2d
      zcn sqsqrtd oveq2d ad2antrl mulcld subsq eqtrd simplr simpr subcld mul02d
      syl2anc 3eqtr3d necon3d mpi adantrl eqnetrd rexlimdvva expimpd sylbid imp
      ex ) BEFUAGZABUBHGZAIJZWCWDAUCGZACUKZBUDHZDUKZKLZUELZMZWGNOLZBWINOLZKLZPL
      ZQMZRZDSUFCSUFZRWECDABUGWCWFWSWEWCWFRZWRWECDSSWTWGSGZWISGZRZRZWRWEXDWRRAW
      KIXDWLWQUHXDWQWKIJZWLXDWQRZQIJXEULXFWKIQIXFWKIMZQIMXFXGRZWPWKWGWJPLZKLZQI
      XHWPWMWJNOLZPLZXJXHWOXKWMPXHXKWHNOLZWNKLWOXHWHWIXHBWTBTGXCWQXGWTBWCBEGWFB
      EFUIUJUMUNZUOZXDWITGZWQXGXBXPWTXAWIVAUPUQZURXHXMBWNKXHBXNVBUSUTVCXHWGTGZW
      JTGXLXJMXDXRWQXGXAXRWTXBWGVAVDUQZXHWHWIXOXQVEZWGWJVFVLVGXDWQXGVHXHXJIXIKL
      IXHWKIXIKXFXGVIUSXHXIXHWGWJXSXTVJVKVGVMWBVNVOVPVQWBVRVSVTWA $.

    $( General solutions of the Pell equation are closed under reciprocals.
       (Contributed by Stefan O'Rear, 18-Sep-2014.) $)
    pell1234qrreccl $p |- ( ( D e. ( NN \ []NN ) /\ A e. ( Pell1234QR ` D ) )
        -> ( 1 / A ) e. ( Pell1234QR ` D ) ) $=
      ( vc vd va vb wcel wa c1 co cv cmul caddc wceq c2 cexp cmin cz cc oveq2d
      cn csquarenn cdif cpell1234qr cfv cdiv cr csqrt elpell1234qr pell1234qrre
      wrex biimpa pell1234qrne0 rereccld ad2antrr simplrl simplrr znegcld recnd
      cneg zcn adantr ad2antlr eldifi nncnd ad3antrrr zcnd negcld mulcld addcld
      sqrtcld cc0 wne sqmuld sqsqrtd oveq1d eqtr2d simprr subsq syl2anc 3eqtr3d
      recidd simprl mulneg2d negsubd eqtrd oveq12d 3eqtr4d mulcanad sqneg oveq1
      syl weq eqeq2d eqeq1d anbi12d rspc2ev syl112anc jca ex rexlimdvva adantld
      oveq2 mpd wb mpbird ) BUAUBUCGZABUDUEZGZHZIAUFJZXHGZXKUGGZXKCKZBUHUEZDKZL
      JZMJZNZXNOPJZBXPOPJZLJZQJZINZHZDRUKCRUKZHZXJAUGGZAEKZXOFKZLJZMJZNZYIOPJZB
      YJOPJZLJZQJZINZHZFRUKERUKZHZYGXGXIUUAEFABUIULXJYTYGYHXJYSYGEFRRXJYIRGZYJR
      GZHZHZYSYGUUEYSHZXMYFXJXMUUDYSXJAABUJZABUMZUNZUOUUFUUBYJUTZRGXKYIXOUUJLJZ
      MJZNZYNBUUJOPJZLJZQJZINZYFXJUUBUUCYSUPUUFYJXJUUBUUCYSUQZURUUFXKUULAXJXKSG
      UUDYSXJXKUUIUSUOUUFYIUUKUUDYISGZXJYSUUBUUSUUCYIVAVBVCZUUFXOUUJUUFBXGBSGXI
      UUDYSXGBBUAUBVDVEVFZVKZUUFYJUUFYJUURVGZVHVIVJXJASGUUDYSXJAUUGUSUOZXJAVLVM
      UUDYSUUHUOZUUFIYLYIYKQJZLJZAXKLJAUULLJUUFYQYNYKOPJZQJZIUVGUUFYPUVHYNQUUFU
      VHXOOPJZYOLJYPUUFXOYJUVBUVCVNUUFUVJBYOLUUFBUVAVOVPVQTUUEYMYRVRZUUFUUSYKSG
      UVIUVGNUUTUUFXOYJUVBUVCVIZYIYKVSVTWAUUFAUVDUVEWBUUFAYLUULUVFLUUEYMYRWCUUF
      UULYIYKUTZMJUVFUUFUUKUVMYIMUUFXOYJUVBUVCWDTUUFYIYKUUTUVLWEWFWGWHWIUUFUUPY
      QIUUFUUOYPYNQUUFUUNYOBLUUFYJSGUUNYONUVCYJWJWLTTUVKWFYEUUMUUQHXKYIXQMJZNZY
      NYBQJZINZHCDYIUUJRRCEWMZXSUVOYDUVQUVRXRUVNXKXNYIXQMWKWNUVRYCUVPIUVRXTYNYB
      QXNYIOPWKVPWOWPXPUUJNZUVOUUMUVQUUQUVSUVNUULXKUVSXQUUKYIMXPUUJXOLXCTWNUVSU
      VPUUPIUVSYBUUOYNQUVSYAUUNBLXPUUJOPWKTTWOWPWQWRWSWTXAXBXDXGXLYGXEXICDXKBUI
      VBXF $.

    $( General solutions of the Pell equation are closed under multiplication.
       (Contributed by Stefan O'Rear, 18-Sep-2014.) $)
    pell1234qrmulcl $p |- ( ( D e. ( NN \ []NN ) /\ A e. ( Pell1234QR ` D ) /\
        B e. ( Pell1234QR ` D ) ) -> ( A x. B ) e. ( Pell1234QR ` D ) ) $=
      ( wcel cmul co wa cv caddc wceq c2 cexp cmin c1 cz wrex oveq12d cc mulcld
      oveq2d va vb vc vd ve vf cn csquarenn cpell1234qr cfv cr csqrt wi remulcl
      cdif ad5antlr simprl ad3antrrr simplrl zmulcld eldifi nnzd simplrr simprr
      ad2antrr zaddcld ad2antrl sqrtcld ad2antll adantr ad2antlr adantl muladdd
      zcn nncnd mul4d msqsqrtd oveq1d mul12d adddid eqtr4d 3eqtrd addcld sqmuld
      eqtrd sqsqrtd eqtr2d subsq syl2anc mulsubd subcld 3eqtr2d 1t1e1 a1i oveq1
      eqeq2d eqeq1d anbi12d oveq2 rspc2ev syl112anc jca rexlimdvva impd expimpd
      ex elpell1234qr an4 bitrdi 3imtr4d 3impib ) CUGUHUODZACUIUJZDZBXMDZABEFZX
      MDZXLAUKDZBUKDZGZAUAHZCULUJZUBHZEFZIFZJZYAKLFZCYCKLFZEFZMFZNJZGZUBOPUAOPZ
      BUCHZYBUDHZEFZIFZJZYNKLFZCYOKLFZEFZMFZNJZGZUDOPUCOPZGZGZXPUKDZXPUEHZYBUFH
      ZEFZIFZJZUUIKLFZCUUJKLFZEFZMFZNJZGZUFOPUEOPZGZXNXOGZXQXLXTUUFUVAXLXTGZYMU
      UEUVAUVCYLUUEUVAUMZUAUBOOUVCYAODZYCODZGZGZYLUVDUVHYLGZUUDUVAUCUDOOUVIYNOD
      ZYOODZGZGZUUDUVAUVMUUDGZUUHUUTXTUUHXLUVGYLUVLUUDABUNUPUVNYAYNEFZCYOYCEFZE
      FZIFZODYAYOEFZYNYCEFZIFZODXPUVRYBUWAEFZIFZJZUVRKLFZCUWAKLFZEFZMFZNJZUUTUV
      NUVOUVQUVNYAYNUVHUVEYLUVLUUDUVCUVEUVFUQURZUVIUVJUVKUUDUSZUTUVNCUVPUVHCODY
      LUVLUUDUVHCXLCUGDXTUVGCUGUHVAVEZVBURUVNYOYCUVIUVJUVKUUDVCZUVHUVFYLUVLUUDU
      VCUVEUVFVDURZUTUTVFUVNUVSUVTUVNYAYOUWJUWMUTUVNYNYCUWKUWNUTVFUVNXPYEYQEFZU
      VOYPYDEFZIFZYAYPEFZYNYDEFZIFZIFZUWCUVNAYEBYQEUVIYFUVLUUDUVHYFYKUQVEUVMYRU
      UCUQQUVNYAYDYNYPUVHYARDZYLUVLUUDUVEUXBUVCUVFYAVNVGURZUVNYBYCUVNCUVHCRDYLU
      VLUUDUVHCUWLVOURZVHZUVHYCRDZYLUVLUUDUVFUXFUVCUVEYCVNVIURZSZUVLYNRDZUVIUUD
      UVJUXIUVKYNVNVJVKZUVNYBYOUXEUVLYORDZUVIUUDUVKUXKUVJYOVNVLVKZSZVMZUVNUWQUV
      RUWTUWBIUVNUWPUVQUVOIUVNUWPYBYBEFZUVPEFUVQUVNYBYOYBYCUXEUXLUXEUXGVPUVNUXO
      CUVPEUVNCUXDVQVRWETZUVNUWTYBUVSEFZYBUVTEFZIFUWBUVNUWRUXQUWSUXRIUVNYAYBYOU
      XCUXEUXLVSUVNYNYBYCUXJUXEUXGVSQUVNYBUVSUVTUXEUVNYAYOUXCUXLSZUVNYNYCUXJUXG
      SZVTWAZQZWBUVNUWHUWOYAYDMFZYNYPMFZEFZEFZYGYBKLFZYHEFZMFZYSUYGYTEFZMFZEFZN
      UVNUWHUWEUWBKLFZMFZUWCUVRUWBMFZEFZUYFUVNUWGUYMUWEMUVNUYMUYGUWFEFUWGUVNYBU
      WAUXEUVNUVSUVTUXSUXTWCZWDUVNUYGCUWFEUVNCUXDWFZVRWGTUVNUVRRDUWBRDUYNUYPJUV
      NUVOUVQUVNYAYNUXCUXJSUVNCUVPUXDUVNYOYCUXLUXGSSWCUVNYBUWAUXEUYQSUVRUWBWHWI
      UVNUWCUWOUYOUYEEUVNUWOUXAUWCUXNUYBWGUVNUYEUWQUWTMFUYOUVNYAYDYNYPUXCUXHUXJ
      UXMWJUVNUWQUVRUWTUWBMUXPUYAQWGQWBUVNUYFYEUYCEFZYQUYDEFZEFYGYDKLFZMFZYSYPK
      LFZMFZEFUYLUVNYEYQUYCUYDUVNYAYDUXCUXHWCUVNYNYPUXJUXMWCUVNYAYDUXCUXHWKUVNY
      NYPUXJUXMWKVPUVNVUBUYSVUDUYTEUVNUXBYDRDVUBUYSJUXCUXHYAYDWHWIUVNUXIYPRDVUD
      UYTJUXJUXMYNYPWHWIQUVNVUBUYIVUDUYKEUVNVUAUYHYGMUVNYBYCUXEUXGWDTUVNVUCUYJY
      SMUVNYBYOUXEUXLWDTQWLUVNUYLYJUUBEFNNEFZNUVNUYIYJUYKUUBEUVNUYHYIYGMUVNUYGC
      YHEUYRVRTUVNUYJUUAYSMUVNUYGCYTEUYRVRTQUVNYJNUUBNEUVIYKUVLUUDUVHYFYKVDVEUV
      MYRUUCVDQVUENJUVNWMWNWBWBUUSUWDUWIGXPUVRUUKIFZJZUWEUUPMFZNJZGUEUFUVRUWAOO
      UUIUVRJZUUMVUGUURVUIVUJUULVUFXPUUIUVRUUKIWOWPVUJUUQVUHNVUJUUNUWEUUPMUUIUV
      RKLWOVRWQWRUUJUWAJZVUGUWDVUIUWIVUKVUFUWCXPVUKUUKUWBUVRIUUJUWAYBEWSTWPVUKV
      UHUWHNVUKUUPUWGUWEMVUKUUOUWFCEUUJUWAKLWOTTWQWRWTXAXBXFXCXFXCXDXEXLUVBXRYM
      GZXSUUEGZGUUGXLXNVULXOVUMUAUBACXGUCUDBCXGWRXRYMXSUUEXHXIUEUFXPCXGXJXK $.

    $( ( Characterize the right branch Pell14 as the positive elements ) $)

    $( A positive Pell solution is a general Pell solution.  (Contributed by
       Stefan O'Rear, 18-Sep-2014.) $)
    pell14qrss1234 $p |- ( D e. ( NN \ []NN ) -> ( Pell14QR ` D ) C_ (
        Pell1234QR ` D ) ) $=
      ( va vb vc cn csquarenn cdif wcel cpell14qr cv cmul co wceq c2 cexp wa cz
      cfv wrex cn0 cpell1234qr cr csqrt caddc cmin c1 wi nn0z a1i anim1d anim2d
      reximdv2 elpell14qr elpell1234qr 3imtr4d ssrdv ) AEFGHZBAIRZAUARZUQBJZUBH
      ZUTCJZAUCRDJZKLUDLMVBNOLAVCNOLKLUELUFMPDQSZCTSZPVAVDCQSZPUTURHUTUSHUQVEVF
      VAUQVDVDCTQUQVBTHZVBQHZVDVGVHUGUQVBUHUIUJULUKCDUTAUMCDUTAUNUOUP $.

    $( A positive Pell solution is a real number.  (Contributed by Stefan
       O'Rear, 18-Sep-2014.) $)
    pell14qrre $p |- ( ( D e. ( NN \ []NN ) /\ A e. ( Pell14QR ` D ) ) -> A e.
        RR ) $=
      ( cn csquarenn cdif cpell14qr cfv cpell1234qr pell14qrss1234 pell1234qrre
      wcel cr sselda syldan ) BCDEKZABFGZKABHGZKALKOPQABIMABJN $.

    $( A positive Pell solution is a nonzero number.  (Contributed by Stefan
       O'Rear, 17-Sep-2014.) $)
    pell14qrne0 $p |- ( ( D e. ( NN \ []NN ) /\ A e. ( Pell14QR ` D ) ) -> A
        =/= 0 ) $=
      ( cn csquarenn cdif wcel cpell14qr cfv cpell1234qr cc0 wne pell14qrss1234
      sselda pell1234qrne0 syldan ) BCDEFZABGHZFABIHZFAJKPQRABLMABNO $.

    $( A positive Pell solution is a positive number.  (Contributed by Stefan
       O'Rear, 18-Sep-2014.) $)
    pell14qrgt0 $p |- ( ( D e. ( NN \ []NN ) /\ A e. ( Pell14QR ` D ) ) -> 0 <
        A ) $=
      ( va vb cn wcel cfv cc0 clt cr cmul co wceq c2 cexp cmin wa cabs ad2antlr
      wbr csquarenn cdif cpell14qr cv csqrt caddc c1 wrex cn0 elpell14qr eldifi
      0cnd ad3antrrr nnred nnnn0d nn0ge0d resqrtcld zre adantl remulcld abssubd
      cz recnd subid1d fveq2d eqtrd absresq syl sqrtcld cc sqmuld oveq1d 3eqtrd
      sqsqrtd 0lt1 simpr breqtrrid resqcld adantr posdifd mpbird eqbrtrd abscld
      nn0re absge0d cle nn0ge0 lt2sqd 0red absdifltd mpbid simprd nn0cn addcomd
      breqtrrd adantrl simprl ex rexlimdvva expimpd sylbid imp ) BEUAUBFZABUCGF
      ZHAITZXCXDAJFZACUDZBUEGZDUDZKLZUFLZMZXGNOLZBXINOLZKLZPLZUGMZQZDVBUHCUIUHZ
      QXECDABUJXCXFXSXEXCXFQZXRXECDUIVBXTXGUIFZXIVBFZQZQZXRXEYDXRQHXKAIYDXQHXKI
      TXLYDXQQZHXJXGUFLZXKIYEXJXGPLHITZHYFITZYEHXJPLRGZXGITYGYHQYEYIXJRGZXGIYEY
      IXJHPLZRGYJYEHXJYEULYEXJYEXHXIYEBYEBXCBEFXFYCXQBEUAUKUMZUNZYEBYEBYLUOUPUQ
      YCXIJFZXTXQYBYNYAXIURUSZSZUTZVCZVAYEYKXJRYEXJYRVDVEVFYEYJXGITYJNOLZXMITYE
      YSXOXMIYEYSXJNOLZXHNOLZXNKLXOYEXJJFYSYTMYQXJVGVHYEXHXIYEBYEBYMVCZVIYCXIVJ
      FXTXQYCXIYOVCSVKYEUUABXNKYEBUUBVNVLVMYEXOXMITHXPITYEHUGXPIVOYDXQVPVQYEXOX
      MYEBXNYMYEXIYPVRUTYEXGYCXGJFZXTXQYAUUCYBXGWDVSSZVRVTWAWBYEYJXGYEXJYRWCUUD
      YEXJYRWEYCHXGWFTZXTXQYAUUEYBXGWGVSSWHWAWBYEHXJXGYEWIYQUUDWJWKWLYEXGXJYCXG
      VJFZXTXQYAUUFYBXGWMVSSYRWNWOWPYDXLXQWQWOWRWSWTXAXB $.

    $( A positive Pell solution is a positive real.  (Contributed by Stefan
       O'Rear, 19-Sep-2014.) $)
    pell14qrrp $p |- ( ( D e. ( NN \ []NN ) /\ A e. ( Pell14QR ` D ) ) -> A e.
        RR+ ) $=
      ( cn csquarenn cdif wcel cpell14qr cfv wa pell14qrre pell14qrgt0 elrpd )
      BCDEFABGHFIAABJABKL $.

    $( A general Pell solution is either a positive solution, or its negation
       is.  (Contributed by Stefan O'Rear, 18-Sep-2014.) $)
    pell1234qrdich $p |- ( ( D e. ( NN \ []NN ) /\ A e. ( Pell1234QR ` D ) ) ->
        ( A e. ( Pell14QR ` D ) \/ -u A e. ( Pell14QR ` D ) ) ) $=
      ( va vb vc wcel cneg cmul co caddc wceq c2 cexp cmin c1 wa wrex cn0 oveq1
      cz vd cn csquarenn cdif cpell1234qr cpell14qr wo cr cv csqrt elpell1234qr
      cfv wi simp-4r weq eqeq2d oveq1d eqeq1d anbi12d rexbidv rspcev adantll wb
      elpell14qr ad4antr mpbir2and orcd exp31 simp-5r renegcld simpllr ad2antlr
      znegcl simprl negeqd cc zcn ad4antlr eldifi ad5antr sqrtcld mulcld negdid
      nncnd mulneg2 eqcomd syl2anc oveq2d 3eqtrd sqneg syl oveq12d simprr eqtrd
      oveq2 rspc2ev syl112anc ex rexlimdva elznn0 simprbi adantl mpjaod expimpd
      olcd sylbid imp ) BUBUCUDFZABUEULFZABUFULZFZAGZXJFZUGZXHXIAUHFZACUIZBUJUL
      ZDUIZHIZJIZKZXPLMIZBXRLMIZHIZNIZOKZPZDTQZCTQZPXNCDABUKXHXOYIXNXHXOPZYHXNC
      TYJXPTFZPZXPRFZYHXNUMZXPGZRFZYLYMYHXNYLYMPYHPZXKXMYQXKXOAEUIZXSJIZKZYRLMI
      ZYDNIZOKZPZDTQZERQZXHXOYKYMYHUNYMYHUUFYLUUEYHEXPRECUOZUUDYGDTUUGYTYAUUCYF
      UUGYSXTAYRXPXSJSUPUUGUUBYEOUUGUUAYBYDNYRXPLMSUQURUSUTVAVBXHXKXOUUFPVCXOYK
      YMYHEDABVDVEVFVGVHYLYPYNYLYPPZYGXNDTUUHXRTFZPZYGXNUUJYGPZXMXKUUKXMXLUHFZX
      LYRXQUAUIZHIZJIZKZUUABUUMLMIZHIZNIZOKZPZUATQERQZUUKAXHXOYKYPUUIYGVIVJUUKY
      PXRGZTFZXLYOXQUVCHIZJIZKZYOLMIZBUVCLMIZHIZNIZOKZUVBYLYPUUIYGVKUUIUVDUUHYG
      XRVMVLUUKXLXTGYOXSGZJIUVFUUKAXTUUJYAYFVNVOUUKXPXSYKXPVPFZYJYPUUIYGXPVQVRZ
      UUKXQXRUUKBXHBVPFXOYKYPUUIYGXHBBUBUCVSWDVTWAZUUIXRVPFZUUHYGXRVQVLZWBWCUUK
      UVMUVEYOJUUKXQVPFZUVQUVMUVEKUVPUVRUVSUVQPUVEUVMXQXRWEWFWGWHWIUUKUVKYEOUUK
      UVHYBUVJYDNUUKUVNUVHYBKUVOXPWJWKUUKUVIYCBHUUKUVQUVIYCKUVRXRWJWKWHWLUUJYAY
      FWMWNUVAUVGUVLPXLYOUUNJIZKZUVHUURNIZOKZPEUAYOUVCRTYRYOKZUUPUWAUUTUWCUWDUU
      OUVTXLYRYOUUNJSUPUWDUUSUWBOUWDUUAUVHUURNYRYOLMSUQURUSUUMUVCKZUWAUVGUWCUVL
      UWEUVTUVFXLUWEUUNUVEYOJUUMUVCXQHWOWHUPUWEUWBUVKOUWEUURUVJUVHNUWEUUQUVIBHU
      UMUVCLMSWHWHURUSWPWQXHXMUULUVBPVCXOYKYPUUIYGEUAXLBVDVTVFXEWRWSWRYKYMYPUGZ
      YJYKXPUHFUWFXPWTXAXBXCWSXDXFXG $.

    $( A number is a positive Pell solution iff it is positive and a Pell
       solution, justifying our name choice.  (Contributed by Stefan O'Rear,
       19-Oct-2014.) $)
    elpell14qr2 $p |- ( D e. ( NN \ []NN ) -> ( A e. ( Pell14QR ` D ) <-> ( A
        e. ( Pell1234QR ` D ) /\ 0 < A ) ) ) $=
      ( cn csquarenn cdif wcel cpell14qr cfv cpell1234qr cc0 clt pell14qrss1234
      wbr wa sselda pell14qrgt0 wn cr wi adantrr jca wo 0re pell1234qrre ltnsym
      cneg sylancr impr lt0neg1d mtbid ex adantr mtod pell1234qrdich orel2 sylc
      impbida ) BCDEFZABGHZFZABIHZFZJAKMZNZURUTNVBVCURUSVAABLOABPUAURVDNZAUFZUS
      FZQUTVGUBZUTVEVGJVFKMZVEAJKMZVIURVBVCVJQZURVBNJRFARFZVCVKSUCABUDZJAUEUGUH
      VEAURVBVLVCVMTUIUJURVGVISVDURVGVIVFBPUKULUMURVBVHVCABUNTVGUTUOUPUQ $.

    $( Positive Pell solutions are closed under multiplication.  (Contributed
       by Stefan O'Rear, 17-Sep-2014.) $)
    pell14qrmulcl $p |- ( ( D e. ( NN \ []NN ) /\ A e. ( Pell14QR ` D ) /\ B e.
        ( Pell14QR ` D ) ) -> ( A x. B ) e. ( Pell14QR ` D ) ) $=
      ( cn csquarenn cdif wcel cpell14qr cfv cmul co cpell1234qr cc0 clt wbr wa
      cr pell1234qrre syldan elpell14qr2 simprll simprrl pell1234qrmulcl jca ex
      simpl syl3anc simprlr simprrr mulgt0d anbi12d 3imtr4d 3impib ) CDEFGZACHI
      ZGZBUOGZABJKZUOGZUNACLIZGZMANOZPZBUTGZMBNOZPZPZURUTGZMURNOZPZUPUQPUSUNVGV
      JUNVGPZVHVIVKUNVAVDVHUNVGUFUNVAVBVFUAZUNVCVDVEUBZABCUCUGVKABUNVGVAAQGVLAC
      RSUNVGVDBQGVMBCRSUNVAVBVFUHUNVCVDVEUIUJUDUEUNUPVCUQVFACTBCTUKURCTULUM $.

    $( Positive Pell solutions are closed under reciprocal.  (Contributed by
       Stefan O'Rear, 18-Sep-2014.) $)
    pell14qrreccl $p |- ( ( D e. ( NN \ []NN ) /\ A e. ( Pell14QR ` D ) ) -> (
        1 / A ) e. ( Pell14QR ` D ) ) $=
      ( cn csquarenn cdif wcel cpell14qr cfv c1 cdiv co cpell1234qr cc0 clt wbr
      wa pell1234qrreccl adantrr cr elpell14qr2 pell1234qrre simprr recgt0d jca
      ex 3imtr4d imp ) BCDEFZABGHZFZIAJKZUIFZUHABLHZFZMANOZPZUKUMFZMUKNOZPZUJUL
      UHUPUSUHUPPZUQURUHUNUQUOABQRUTAUHUNASFUOABUARUHUNUOUBUCUDUEABTUKBTUFUG $.

    $( Positive Pell solutions are closed under division.  (Contributed by
       Stefan O'Rear, 18-Sep-2014.) $)
    pell14qrdivcl $p |- ( ( D e. ( NN \ []NN ) /\ A e. ( Pell14QR ` D ) /\ B e.
        ( Pell14QR ` D ) ) -> ( A / B ) e. ( Pell14QR ` D ) ) $=
      ( cn csquarenn cdif wcel cpell14qr cfv w3a cdiv co c1 cc pell14qrre recnd
      cmul wa 3adant3 3adant2 cc0 wne pell14qrne0 divrecd pell14qrreccl eqeltrd
      pell14qrmulcl syld3an3 ) CDEFGZACHIZGZBUJGZJZABKLAMBKLZQLZUJUMABUIUKANGUL
      UIUKRAACOPSUIULBNGUKUIULRBBCOPTUIULBUAUBUKBCUCTUDUIUKULUNUJGZUOUJGUIULUPU
      KBCUETAUNCUGUHUF $.

    $( Lemma for ~ pell14qrexpcl .  (Contributed by Stefan O'Rear,
       18-Sep-2014.) $)
    pell14qrexpclnn0 $p |- ( ( D e. ( NN \ []NN ) /\ A e. ( Pell14QR ` D ) /\ B
        e. NN0 ) -> ( A ^ B ) e. ( Pell14QR ` D ) ) $=
      ( va vb cn csquarenn wcel cn0 cexp co cv wi cc0 wceq oveq2 eleq1d eqeltrd
      c1 imbi2d cdif cpell14qr cfv caddc weq pell14qrre recnd exp0d pell14qrne0
      wa cdiv dividd eqtr4d pell14qrdivcl 3anidm23 w3a cc 3ad2ant2 simp1 expp1d
      cmul simp2l simp3 simp2r pell14qrmulcl syl3anc 3exp nn0ind expdcom 3imp
      a2d ) CFGUAHZACUBUCZHZBIHZABJKZVMHZVOVLVNVQVLVNUJZADLZJKZVMHZMVRANJKZVMHZ
      MVRAELZJKZVMHZMVRAWDSUDKZJKZVMHZMVRVQMDEBVSNOZWAWCVRWJVTWBVMVSNAJPQTDEUEZ
      WAWFVRWKVTWEVMVSWDAJPQTVSWGOZWAWIVRWLVTWHVMVSWGAJPQTVSBOZWAVQVRWMVTVPVMVS
      BAJPQTVRWBAAUKKZVMVRWBSWNVRAVRAACUFUGZUHVRAWOACUIULUMVLVNWNVMHAACUNUORWDI
      HZVRWFWIWPVRWFWIWPVRWFUPZWHWEAVAKZVMWQAWDVRWPAUQHWFWOURWPVRWFUSUTWQVLWFVN
      WRVMHWPVLVNWFVBWPVRWFVCWPVLVNWFVDWEACVEVFRVGVKVHVIVJ $.

    $( Positive Pell solutions are closed under integer powers.  (Contributed
       by Stefan O'Rear, 18-Sep-2014.) $)
    pell14qrexpcl $p |- ( ( D e. ( NN \ []NN ) /\ A e. ( Pell14QR ` D ) /\ B e.
        ZZ ) -> ( A ^ B ) e. ( Pell14QR ` D ) ) $=
      ( cn csquarenn cdif wcel cpell14qr cfv co cn0 wa simplll pell14qrexpclnn0
      cexp simpllr simpr syl3anc cc recnd cz cr cneg wo c1 cdiv wceq pell14qrre
      elznn0 ad2antrr simplr expneg2 pell14qrreccl syl2anc jaodan expl biimtrid
      eqeltrd 3impia ) CDEFGZACHIZGZBUAGZABOJZVAGZVCBUBGZBKGZBUCZKGZUDZLUTVBLZV
      EBUIVKVFVJVEVKVFLZVGVEVIVLVGLUTVBVGVEUTVBVFVGMUTVBVFVGPVLVGQABCNRVLVILZVD
      UEAVHOJZUFJZVAVMASGZBSGVIVDVOUGVKVPVFVIVKAACUHTUJVMBVKVFVIUKTVLVIQZABULRV
      MUTVNVAGZVOVAGUTVBVFVIMZVMUTVBVIVRVSUTVBVFVIPVQAVHCNRVNCUMUNURUOUPUQUS $.

    $( First-quadrant Pell solutions are a subset of the positive solutions.
       (Contributed by Stefan O'Rear, 18-Sep-2014.) $)
    pell1qrss14 $p |- ( D e. ( NN \ []NN ) -> ( Pell1QR ` D ) C_ ( Pell14QR ` D
        ) ) $=
      ( va vc vb cn csquarenn cdif wcel cpell1qr cfv cv cmul co wceq c2 cexp wa
      cn0 wrex cz cpell14qr cr csqrt caddc cmin c1 wi nn0z a1i reximdv2 reximdv
      anim1d anim2d elpell1qr elpell14qr 3imtr4d ssrdv ) AEFGHZBAIJZAUAJZURBKZU
      BHZVACKZAUCJDKZLMUDMNVCOPMAVDOPMLMUEMUFNQZDRSZCRSZQVBVEDTSZCRSZQVAUSHVAUT
      HURVGVIVBURVFVHCRURVEVEDRTURVDRHZVDTHZVEVJVKUGURVDUHUIULUJUKUMCDVAAUNCDVA
      AUOUPUQ $.

    $( A positive Pell solution is either in the first quadrant, or its
       reciprocal is.  (Contributed by Stefan O'Rear, 18-Sep-2014.) $)
    pell14qrdich $p |- ( ( D e. ( NN \ []NN ) /\ A e. ( Pell14QR ` D ) ) -> ( A
        e. ( Pell1QR ` D ) \/ ( 1 / A ) e. ( Pell1QR ` D ) ) ) $=
      ( va vb wcel wa cmul co caddc wceq c2 cexp cmin c1 cn0 ad2antrr cc adantr
      wrex oveq2d vc cn csquarenn cdif cpell14qr cfv cr cv csqrt cz cpell1qr wo
      cdiv elpell14qr biimpa cneg elznn0 sylib simprd simplr simprl simpr rsp2e
      simplrr syl3anc jca ex elpell1qr ad4antr sylibrd cc0 pell14qrne0 rereccld
      wne pell14qrre recnd reccld ad3antrrr nn0cn ad2antrl eldifi nncnd sqrtcld
      wb zcn ad2antll negcld mulcld addcld recidd simprr eqtr4d syl2anc sqsqrtd
      subsq sqmuld oveq1d eqtr2d mulneg2d negsub eqcomd oveq12d 3eqtr4d adantrr
      eqtrd mulcanad sqneg syl oveq2 eqeq2d oveq1 eqeq1d anbi12d rspcev orim12d
      rspe mpd rexlimdvva expimpd ) BUBUCUDEZABUEUFEZFZAUGEZACUHZBUIUFZDUHZGHZI
      HZJZYDKLHZBYFKLHZGHZMHZNJZFZDUJSCOSZFZABUKUFZEZNAUMHZYREZULZXTYAYQCDABUNU
      OYBYCYPUUBYBYCFZYOUUBCDOUJUUCYDOEZYFUJEZFZFZYOUUBUUGYOFZYFOEZYFUPZOEZULZU
      UBUUHYFUGEZUULUUHUUEUUMUULFUUCUUDUUEYOVDYFUQURUSUUHUUIYSUUKUUAUUHUUIYCYOD
      OSCOSZFZYSUUHUUIUUOUUHUUIFZYCUUNUUGYCYOUUIYBYCUUFUTZPUUPUUDUUIYOUUNUUGUUD
      YOUUIUUCUUDUUEVAZPUUHUUIVBUUGYOUUIUTYOCDOOVCVEVFVGXTYSUUOWDYAYCUUFYOCDABV
      HVIVJUUHUUKYTUGEZYTYDYEUAUHZGHZIHZJZYJBUUTKLHZGHZMHZNJZFZUAOSZCOSZFZUUAUU
      HUUKUVKUUHUUKFZUUSUVJUVLAUUGYCYOUUKUUQPYBAVKVNZYCUUFYOUUKABVLZVIVMUVLUUDU
      VIUVJUUGUUDYOUUKUURPUVLUUKYTYDYEUUJGHZIHZJZYJBUUJKLHZGHZMHZNJZFZUVIUUHUUK
      VBUVLUVQUWAUUHUVQUUKUUHYTUVPAYBYTQEYCUUFYOYBAYBAABVOVPZUVNVQVRUUGUVPQEYOU
      UGYDUVOUUDYDQEZUUCUUEYDVSVTZUUGYEUUJUUGBXTBQEYAYCUUFXTBBUBUCWAWBVRZWCZUUG
      YFUUEYFQEZUUCUUDYFWEWFZWGWHWIRYBAQEYCUUFYOUWCVRYBUVMYCUUFYOUVNVRUUHAYTGHZ
      YMAUVPGHZUUHUWJNYMYBUWJNJYCUUFYOYBAUWCUVNWJVRUUGYIYNWKWLUUGYIYMUWKJYNUUGY
      IFZYJYGKLHZMHZYHYDYGMHZGHZYMUWKUWLUWDYGQEZUWNUWPJUUGUWDYIUWERUUGUWQYIUUGY
      EYFUWGUWIWHZRYDYGWOWMUUGYMUWNJYIUUGYLUWMYJMUUGUWMYEKLHZYKGHYLUUGYEYFUWGUW
      IWPUUGUWSBYKGUUGBUWFWNWQWRTRUWLAYHUVPUWOGUUGYIVBUUGUVPUWOJYIUUGUVPYDYGUPZ
      IHZUWOUUGUVOUWTYDIUUGYEYFUWGUWIWSTUUGUWDUWQUWOUXAJUWEUWRUWDUWQFUXAUWOYDYG
      WTXAWMWLRXBXCXDXEXFRUVLUVTYMNUVLUVSYLYJMUVLUVRYKBGUVLUWHUVRYKJUUGUWHYOUUK
      UWIPYFXGXHTTUUGYIYNUUKVDXEVFUVHUWBUAUUJOUUTUUJJZUVCUVQUVGUWAUXBUVBUVPYTUX
      BUVAUVOYDIUUTUUJYEGXITXJUXBUVFUVTNUXBUVEUVSYJMUXBUVDUVRBGUUTUUJKLXKTTXLXM
      XNWMUVICOXPWMVFVGXTUUAUVKWDYAYCUUFYOCUAYTBVHVIVJXOXQVGXRXSXQ $.

    $( A Pell solution in the first quadrant is at least 1.  (Contributed by
       Stefan O'Rear, 17-Sep-2014.) $)
    pell1qrge1 $p |- ( ( D e. ( NN \ []NN ) /\ A e. ( Pell1QR ` D ) ) -> 1 <_ A
        ) $=
      ( va vb cn csquarenn wcel c1 cle wbr co wceq c2 wa cn0 nn0red nn0ge0d cc0
      cexp a1i cdif cpell1qr cr cv csqrt cmul caddc cmin wrex elpell1qr simplrl
      cfv 1red eldifi ad3antrrr nnnn0d resqrtcld simplrr remulcld readdcld 2nn0
      nn0expcld nn0mulcld addge02d mpbid cc nn0cn ad2antrl sqcld ad2antrr nncnd
      sq1 ad2antll mulcld 1cnd subaddd biimpa eqcomd 3brtr4d 0le1 le2sqd mpbird
      sqrtge0d mulge0d addge01d letrd adantrl simprl breqtrrd rexlimdvva sylbid
      ex expimpd imp ) BEFUAGZABUBULGZHAIJZWOWPAUCGZACUDZBUEULZDUDZUFKZUGKZLZWS
      MSKZBXAMSKZUFKZUHKHLZNZDOUICOUIZNWQCDABUJWOWRXJWQWOWRNZXIWQCDOOXKWSOGZXAO
      GZNZNZXIWQXOXINHXCAIXOXHHXCIJXDXOXHNZHWSXCXPUMZXPWSXKXLXMXHUKZPZXPWSXBXSX
      PWTXAXPBXPBXPBWOBEGZWRXNXHBEFUNZUOUPZPZXPBYBQZUQZXPXAXKXLXMXHURZPZUSZUTXP
      HWSIJHMSKZXEIJXPHXGHUGKZYIXEIXPRXGIJHYJIJXPXGXPBXFYBXPXAMYFMOGXPVATVBVCZQ
      XPHXGXQXPXGYKPVDVEYIHLXPVLTXPYJXEXOXHYJXELXOXEXGHXOWSXLWSVFGXKXMWSVGVHVIX
      OBXFXOBWOXTWRXNYAVJVKXOXAXMXAVFGXKXLXAVGVMVIVNXOVOVPVQVRVSXPHWSXQXSRHIJXP
      VTTXPWSXRQWAWBXPRXBIJWSXCIJXPWTXAYEYGXPBYCYDWCXPXAYFQWDXPWSXBXSYHWEVEWFWG
      XOXDXHWHWIWLWJWMWKWN $.

    $( 1 is a Pell solution and in the first quadrant as one.  (Contributed by
       Stefan O'Rear, 17-Sep-2014.) $)
    pell1qr1 $p |- ( D e. ( NN \ []NN ) -> 1 e. ( Pell1QR ` D ) ) $=
      ( va vb cn csquarenn wcel c1 cmul co caddc wceq c2 cexp wa cn0 cc0 oveq2d
      cmin a1i oveq1 cdif cpell1qr cr cv csqrt wrex 1red 1nn0 0nn0 eldifi nncnd
      cfv sqrtcld mul01d eqtr2di sq1 oveq2i eqtrid oveq12d eqtrdi eqeq2d oveq1d
      1p0e1 1m0e1 eqeq1d anbi12d oveq2 rspc2ev syl112anc elpell1qr mpbir2and
      sq0 ) ADEUAFZGAUBULFGUCFGBUDZAUEULZCUDZHIZJIZKZVNLMIZAVPLMIZHIZRIZGKZNZCO
      UFBOUFZVMUGVMGOFZPOFZGGVOPHIZJIZKZGLMIZAPLMIZHIZRIZGKZWFWGVMUHSWHVMUISVMW
      JGPJIGVMWIPGJVMVOVMAVMAADEUJUKZUMUNQVCUOVMWOGPRIGVMWLGWNPRWLGKVMUPSVMWNAP
      HIPWMPAHVLUQVMAWQUNURUSVDUTWEWKWPNGGVQJIZKZWLWBRIZGKZNBCGPOOVNGKZVSWSWDXA
      XBVRWRGVNGVQJTVAXBWCWTGXBVTWLWBRVNGLMTVBVEVFVPPKZWSWKXAWPXCWRWJGXCVQWIGJV
      PPVOHVGQVAXCWTWOGXCWBWNWLRXCWAWMAHVPPLMTQQVEVFVHVIBCGAVJVK $.

    $( The first quadrant solutions are precisely the positive Pell solutions
       which are at least one.  (Contributed by Stefan O'Rear, 18-Sep-2014.) $)
    elpell1qr2 $p |- ( D e. ( NN \ []NN ) -> ( A e. ( Pell1QR ` D ) <-> ( A e.
        ( Pell14QR ` D ) /\ 1 <_ A ) ) ) $=
      ( wcel cfv c1 cle wbr wa pell1qrge1 clt wceq wo 1red cdiv co wn cr adantr
      a1i cc0 cn csquarenn cpell1qr cpell14qr pell1qrss14 sselda jca pell14qrre
      cdif leloed ltnled biimpa 1div1e1 eqcomi breq2d pell14qrgt0 0lt1 syl22anc
      bitrd mtbid simplll sylancom mtand pell14qrdich orel2 sylc simpr pell1qr1
      wb lerec2 ad2antrr eqeltrrd jaodan ex sylbid impr impbida ) BUAUBUICZABUC
      DZCZABUDDZCZEAFGZHVRVTHWBWCVRVSWAABUEUFABIUGVRWBWCVTVRWBHZWCEAJGZEAKZLZVT
      WDEAWDMZABUHZUJWDWGVTWDWEVTWFWDWEHZEANOZVSCZPVTWLLZVTWJWLEWKFGZWJAEFGZWNW
      DWEWOPWDEAWHWIUKULWJWOAEENOZFGZWNWJEWPAFEWPKWJWPEUMUNSUOWJAQCZTAJGZEQCTEJ
      GZWQWNVIWDWRWEWIRWDWSWEABUPRWJMWTWJUQSAEVJURUSUTWJWLVRWNVRWBWEWLVAWKBIVBV
      CWDWMWEABVDRWLVTVEVFWDWFHEAVSWDWFVGVREVSCWBWFBVHVKVLVMVNVOVPVQ $.

    $( Lemma for ~ pell1qrgap .  (Contributed by Stefan O'Rear,
       18-Sep-2014.) $)
    pell1qrgaplem $p |- ( ( ( D e. NN /\ ( A e. NN0 /\ B e. NN0 ) ) /\ ( 1 < (
        A + ( ( sqrt ` D ) x. B ) ) /\ ( ( A ^ 2 ) - ( D x. ( B ^ 2 ) ) ) = 1 )
        ) -> ( ( sqrt ` ( D + 1 ) ) + ( sqrt ` D ) )
          <_ ( A + ( ( sqrt ` D ) x. B ) ) ) $=
      ( wcel wa c1 cmul co caddc wbr cexp cmin wceq a1i adantr ad2antlr cle cc0
      c2 oveq2d cn cn0 csqrt cfv clt crp nnrp ad2antrr rpaddcld rpsqrtcld rpred
      1rp cr nn0re adantl remulcld 1re resqcld resubcld 0red sq1 nnge1 wn oveq1
      simplrl sq0 eqtrdi rpcnd mul01d eqtrd simplrr recnd sqcld subid1d 3eqtr3d
      cc eqtr2id wb nn0ge0 0le1 sq11 syl22anc mpbid simpr oveq12d 1p0e1 breqtrd
      ltnri pm2.24 mpisyl wo elnn0 sylib mpjaodan le2sqd suble0d mpbird lemul2d
      eqbrtrrd sqsqrtd simprr eqcomd mulcld subdid mulridd oveq1d eqtr2d 3eqtrd
      leadd2dd addsub12d addridd 3brtr4d rpge0d le2addd ) CUADZAUBDZBUBDZEZEZFA
      CUCUDZBGHZIHZUEJZASKHZCBSKHZGHZLHZFMZEZEZCFIHZUCUDZXTAYAYJYLYJYKYJCFXOCUF
      DXRYICUGUHZFUFDYJULNUIZUJZUKZYJXTYJCYMUJZUKZXRAUMDZXOYIXPYSXQAUNOPZYJXTBY
      RXRBUMDZXOYIXQUUAXPBUNUOPZUPYJYLAQJYLSKHZYDQJYJYDCFYELHZGHZIHZYDCRGHZIHZU
      UCYDQYJUUEUUGYDYJCUUDYJCYMUKZYJFYEFUMDZYJUQNZYJBUUBURZUSZUPYJCRUUIYJUTZUP
      YJAYTURYJUUDRQJZUUEUUGQJYJUUOFYEQJYJFSKHZFYEQUUPFMYJVANYJFBQJZUUPYEQJYJBU
      ADZUUQBRMZUURUUQYJBVBUOYJUUSEZFFUEJZUVAVCUUQUUTFYBFUEXSYCYHUUSVEUUTYBFRIH
      FUUTAFYARIUUTYDUUPMZAFMZUUTUUPFYDVAUUTYGYDRLHFYDUUTYFRYDLUUTYFUUGRUUTYERC
      GUUTYERSKHZRUUSYEUVDMYJBRSKVDUOVFVGTUUTCYJCVPDUUSYJCYMVHZOVIVJTXSYCYHUUSV
      KUUTYDYJYDVPDUUSYJAYJAYTVLVMZOVNVOVQYJUVBUVCVRZUUSYJYSRAQJZUUJRFQJZUVGYTX
      RUVHXOYIXPUVHXQAVSOPZUUKUVIYJVTNZAFWAWBOWCUUTYAXTRGHRUUTBRXTGYJUUSWDTUUTX
      TYJXTVPDUUSYJXTYQVHZOVIVJWEWFVGWGFUQWHUVAUUQWIWJYJXQUURUUSWKXOXPXQYIVKBWL
      WMWNZYJFBUUKUUBUVKXRRBQJZXOYIXQUVNXPBVSUOPWOWCWSYJFYEUUKUULWPWQYJUUDRCUUM
      UUNYMWRWCXIYJUUCYKCYGIHZUUFYJYKYJYKYNVHWTYJFYGCIYJYGFXSYCYHXAXBTYJUVOYDCY
      FLHZIHUUFYJCYDYFUVEUVFYJCYEUVEYJBYJBUUBVLVMZXCXJYJUVPUUEYDIYJUUECFGHZYFLH
      UVPYJCFYEUVEYJFUUKVLUVQXDYJUVRCYFLYJCUVEXEXFXGTVJXHYJUUHYDRIHYDYJUUGRYDIY
      JCUVEVITYJYDUVFXKXGXLYJYLAYPYTYJYLYOXMUVJWOWQYJXTFGHZXTYAQYJXTUVLXEYJUUQU
      VSYAQJUVMYJFBXTUUKUUBYQWRWCWSXN $.

    $( First-quadrant Pell solutions are bounded away from 1.  (This particular
       bound allows to prove exact values for the fundamental solution later.)
       (Contributed by Stefan O'Rear, 18-Sep-2014.) $)
    pell1qrgap $p |- ( ( D e. ( NN \ []NN ) /\ A e. ( Pell1QR ` D ) /\ 1 < A )
        -> ( ( sqrt ` ( D + 1 ) ) + ( sqrt ` D ) ) <_ A ) $=
      ( va vb cn csquarenn wcel cfv c1 clt wbr caddc co csqrt cle cmul wceq cn0
      wa cv cdif cpell1qr wi cr c2 cexp cmin wb elpell1qr adantr eldifi ad4antr
      wrex simplr simp-4r simprl breqtrd simprr pell1qrgaplem syl22anc breqtrrd
      ex rexlimdvva expimpd sylbid com23 3imp ) BEFUAGZABUBHGZIAJKZBILMNHBNHZLM
      ZAOKZVHVJVIVMVHVJVIVMUCVHVJSZVIAUDGZACTZVKDTZPMLMZQZVPUEUFMBVQUEUFMPMUGMI
      QZSZDRUMCRUMZSZVMVHVIWCUHVJCDABUIUJVNVOWBVMVNVOSZWAVMCDRRWDVPRGVQRGSZSZWA
      VMWFWASZVLVRAOWGBEGZWEIVRJKVTVLVROKVHWHVJVOWEWABEFUKULWDWEWAUNWGIAVRJVHVJ
      VOWEWAUOWFVSVTUPZUQWFVSVTURVPVQBUSUTWIVAVBVCVDVEVBVFVG $.

    $( Positive Pell solutions are bounded away from 1.  (Contributed by Stefan
       O'Rear, 18-Sep-2014.) $)
    pell14qrgap $p |- ( ( D e. ( NN \ []NN ) /\ A e. ( Pell14QR ` D ) /\ 1 < A
        ) -> ( ( sqrt ` ( D + 1 ) ) + ( sqrt ` D ) ) <_ A ) $=
      ( cn csquarenn cdif wcel cpell1qr cfv cpell14qr c1 clt wbr caddc co csqrt
      cle w3a simp2 wa cr wi pell14qrre ltle sylancr 3impia elpell1qr2 3ad2ant1
      1re wb mpbir2and pell1qrgap syld3an2 ) BCDEFZABGHFZABIHFZJAKLZBJMNOHBOHMN
      APLUMUOUPQUNUOJAPLZUMUOUPRUMUOUPUQUMUOSJTFATFUPUQUAUHABUBJAUCUDUEUMUOUNUO
      UQSUIUPABUFUGUJABUKUL $.

    $( Positive Pell solutions are bounded away from 1, with a friendlier
       bound.  (Contributed by Stefan O'Rear, 18-Sep-2014.) $)
    pell14qrgapw $p |- ( ( D e. ( NN \ []NN ) /\ A e. ( Pell14QR ` D ) /\ 1 < A
        ) -> 2 < A ) $=
      ( cn csquarenn wcel cfv c1 clt wbr c2 caddc co csqrt rpsqrtcld rpred cexp
      cr a1i syl cle cdif cpell14qr w3a eldifi 3ad2ant1 nnrpd rpaddcld readdcld
      2re crp 1rp pell14qrre 3adant3 df-2 1red nnred peano2re nnge1d ltp1d wceq
      lelttrd sq1 cc nncnd peano2cn sqsqrtd 3brtr4d rpge0d lt2sqd mpbird le2sqd
      cc0 0le1 ltleaddd eqbrtrid pell14qrgap ltletrd ) BCDUAEZABUBFEZGAHIZUCZJB
      GKLZMFZBMFZKLZAJQEWAUIRWAWCWDWAWCWAWBWABGWABVRVSBCEVTBCDUDUEZUFZGUJEWAUKR
      UGNZOZWAWDWABWGNZOZUHVRVSAQEVTABULUMWAJGGKLWEHUNWAGGWCWDWAUOZWLWIWKWAGWCH
      IGJPLZWCJPLZHIWAGWBWMWNHWAGBWBWLWABWFUPZWABQEWBQEWOBUQSWABWFURZWABWOUSVAW
      MGUTWAVBRZWAWBWABVCEWBVCEWABWFVDZBVESVFVGWAGWCWLWIVLGTIWAVMRZWAWCWHVHVIVJ
      WAGWDTIWMWDJPLZTIWAGBWMWTTWPWQWABWRVFVGWAGWDWLWKWSWAWDWJVHVKVJVNVOABVPVQ
      $.

    $( Condition for a calculated real to be a Pell solution.  (Contributed by
       Stefan O'Rear, 19-Sep-2014.) $)
    pellqrexplicit $p |- ( ( ( D e. ( NN \ []NN ) /\ A e. NN0 /\ B e. NN0 ) /\
        ( ( A ^ 2 ) - ( D x. ( B ^ 2 ) ) ) = 1 ) -> ( A + ( ( sqrt ` D ) x. B )
        ) e. ( Pell1QR ` D ) ) $=
      ( va vb cn wcel cn0 c2 cexp co cmul cmin c1 wceq wa caddc cr oveq1 oveq2d
      csquarenn cdif w3a csqrt cfv cpell1qr wrex nn0re 3ad2ant2 eldifi 3ad2ant1
      cv nnrpd rpsqrtcld 3ad2ant3 remulcld readdcld adantr simpl2 simpl3 eqeq2d
      rpred eqidd simpr oveq1d eqeq1d anbi12d oveq2 rspc2ev syl112anc elpell1qr
      wb mpbir2and ) CFUAUBGZAHGZBHGZUCZAIJKZCBIJKZLKZMKZNOZPZACUDUEZBLKZQKZCUF
      UEGZWFRGZWFDULZWDEULZLKZQKZOZWIIJKZCWJIJKZLKZMKZNOZPZEHUGDHUGZVQWHWBVQAWE
      VOVNARGVPAUHUIVQWDBVQWDVQCVQCVNVOCFGVPCFUAUJUKUMUNVBVPVNBRGVOBUHUOUPUQURW
      CVOVPWFWFOZWBWTVNVOVPWBUSVNVOVPWBUTWCWFVCVQWBVDWSXAWBPWFAWKQKZOZVRWPMKZNO
      ZPDEABHHWIAOZWMXCWRXEXFWLXBWFWIAWKQSVAXFWQXDNXFWNVRWPMWIAIJSVEVFVGWJBOZXC
      XAXEWBXGXBWFWFXGWKWEAQWJBWDLVHTVAXGXDWANXGWPVTVRMXGWOVSCLWJBIJSTTVFVGVIVJ
      VQWGWHWTPVLZWBVNVOXHVPDEWFCVKUKURVM $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Pell equations 3: characterizing fundamental solution
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x z A $.  $d x z B $.
    $( Any lower bound of a nonempty set of real numbers is less than or equal
       to its infimum, one-direction version.  (Contributed by Stefan O'Rear,
       1-Sep-2013.)  (Revised by AV, 17-Sep-2020.) $)
    infmrgelbi $p |- ( ( ( A C_ RR /\ A =/= (/) /\ B e. RR ) /\
                      A. x e. A B <_ x ) -> B <_ inf ( A , RR , < ) ) $=
      ( vz cr wss c0 wne wcel w3a cv cle wbr wral wa clt cinf simpr wrex wb
      simpl1 simpl2 wceq breq1 ralbidv rspcev 3ad2antl3 simpl3 infregelb mpbird
      syl31anc ) BEFZBGHZCEIZJZCAKZLMZABNZOZCBEPQLMZURUOURRUSULUMDKZUPLMZABNZDE
      SZUNUTURTULUMUNURUAULUMUNURUBUNULURVDUMVCURDCEVACUCVBUQABVACUPLUDUEUFUGUL
      UMUNURUHDAABCUIUKUJ $.
  $}

  ${
    $d a b c d A $.  $d a b c d D $.  $d a b c d x $.

    $( the only place we directly use D's non-squareness $)
    ${
      $d D x $.
      $( There is a nontrivial solution of a Pell equation in the first
         quadrant.  (Contributed by Stefan O'Rear, 18-Sep-2014.) $)
      pellqrex $p |- ( D e. ( NN \ []NN ) -> E. x e. ( Pell1QR ` D ) 1 < x ) $=
        ( vc vd va cn csquarenn wcel cv c2 cexp co c1 clt wbr wa cr 1re a1i cle
        cdif cmul cmin wceq cpell1qr cfv csqrt cq wn eldifi eldifn anim1i fveq2
        wrex eleq1d df-squarenn elrab2 sylibr mtand pellex syl2anc caddc simpll
        cn0 nnnn0 adantr ad2antlr adantl simpr pellqrexplicit syl31anc readdcli
        nnre ad2antrl nnrpd rpsqrtcld rpred ad2antll remulcld ltp1i nnge1 1t1e1
        readdcld sq1 nncn sqsqrtd 3brtr4d nnrp cc0 0le1 rpge0d le2sqd mpbird wi
        syl jctir lemul12a syl22anc mp2and eqbrtrrid le2addd ltletrd rexlimdvva
        breq2 rspcev ex mpd ) BFGUAHZCIZJKLBDIZJKLUBLUCLMUDZDFUNCFUNZMAIZNOZABU
        EUFZUNZXHBFHZBUGUFZUHHZUIXLBFGUJZXHXSBGHZBFGUKXHXSPXQXSPYAXHXQXSXTULEIZ
        UGUFZUHHXSEBFGYBBUDYCXRUHYBBUGUMUOEUPUQURUSCDBUTVAXHXKXPCDFFXHXIFHZXJFH
        ZPZPZXKXPYGXKPZXIXRXJUBLZVBLZXOHZMYJNOZXPYHXHXIVDHZXJVDHZXKYKXHYFXKVCYF
        YMXHXKYDYMYEXIVEVFVGYFYNXHXKYEYNYDXJVEVHVGYGXKVIXIXJBVJVKYGYLXKYGMMMVBL
        ZYJMQHZYGRSZYOQHYGMMRRVLSYGXIYIYDXIQHXHYEXIVMVNZYGXRXJYGXRYGBYGBXHXQYFX
        TVFZVOVPVQZYEXJQHZXHYDXJVMVRZVSZWCMYONOYGMRVTSYGMMXIYIYQYQYRUUCYDMXITOX
        HYEXIWAVNYGMMMUBLZYITWBYGMXRTOZMXJTOZUUDYITOZYGXQUUEYSXQUUEMJKLZXRJKLZT
        OXQMBUUHUUITBWAUUHMUDXQWDSXQBBWEWFWGXQMXRYPXQRSXQXRXQBBWHVPZVQWIMTOZXQW
        JSXQXRUUJWKWLWMWOYEUUFXHYDXJWAVRYGYPUUKPZXRQHUULUUAUUEUUFPUUGWNYGYPUUKY
        QWJWPZYTUUMUUBMXRMXJWQWRWSWTXAXBVFXNYLAYJXOXMYJMNXDXEVAXFXCXG $.
    $}

    ${
      $d D x $.
      $( Value of the fundamental solution of a Pell equation.  (Contributed by
         Stefan O'Rear, 18-Sep-2014.)  (Revised by AV, 17-Sep-2020.) $)
      pellfundval $p |- ( D e. ( NN \ []NN ) -> ( PellFund ` D ) = inf ( { x e.
          ( Pell14QR ` D ) | 1 < x } , RR , < ) ) $=
        ( va c1 cv clt wbr cpell14qr crab cr cinf csquarenn cdif cpellfund wceq
        cfv cn fveq2 rabeq syl infeq1d df-pellfund ltso infex fvmpt ) CBDAEFGZA
        CEZHPZIZJFKUFABHPZIZJFKQLMNUGBOZJUIUKFULUHUJOUIUKOUGBHRUFAUHUJSTUACAUBJ
        UKFUCUDUE $.
    $}

    $( The fundamental solution of a Pell equation exists as a real number.
       (Contributed by Stefan O'Rear, 18-Sep-2014.) $)
    pellfundre $p |- ( D e. ( NN \ []NN ) -> ( PellFund ` D ) e. RR ) $=
      ( va vb vc cn wcel cfv c1 cv clt wbr wss cle wral wrex pell14qrre sylancr
      cr 1re wa csquarenn cdif cpellfund cpell14qr crab cinf pellfundval c0 wne
      ssrab2 ssrdv sstrid cpell1qr pell1qrss14 pellqrex ssrexv sylc rabn0 breq2
      ex sylibr elrab ltle expimpd biimtrid ralrimiv wceq breq1 ralbidv infrecl
      wi rspcev syl3anc eqeltrd ) AEUAUBFZAUCGHBIZJKZBAUDGZUEZRJUFZRBAUGVOVSRLV
      SUHUIZCIZDIZMKZDVSNZCROZVTRFVOVSVRRVQBVRUJVOBVRRVOVPVRFVPRFVPAPUTUKULVOVQ
      BVROZWAVOAUMGZVRLVQBWHOWGAUNBAUOVQBWHVRUPUQVQBVRURVAVOHRFZHWCMKZDVSNZWFSV
      OWJDVSWCVSFWCVRFZHWCJKZTVOWJVQWMBWCVRVPWCHJUSVBVOWLWMWJVOWLTWIWCRFWMWJVKS
      WCAPHWCVCQVDVEVFWEWKCHRWBHVGWDWJDVSWBHWCMVHVIVLQCDVSVJVMVN $.

    $( Lower bound on the fundamental solution of a Pell equation.
       (Contributed by Stefan O'Rear, 19-Sep-2014.) $)
    pellfundge $p |- ( D e. ( NN \ []NN )
        -> ( ( sqrt ` ( D + 1 ) ) + ( sqrt ` D ) ) <_ ( PellFund ` D ) ) $=
      ( va vb cn csquarenn wcel c1 caddc co csqrt cfv cv clt wbr cle wrex nnrpd
      cr wss rpsqrtcld cdif cpell14qr crab cinf cpellfund wne ssrab2 pell14qrre
      c0 wral ex ssrdv sstrid cpell1qr pell1qrss14 pellqrex ssrexv rabn0 sylibr
      sylc eldifi peano2nnd rpred readdcld wa breq2 pell14qrgap 3expib biimtrid
      elrab ralrimiv infmrgelbi syl31anc pellfundval breqtrrd ) ADEUAFZAGHIZJKZ
      AJKZHIZGBLZMNZBAUBKZUCZRMUDZAUEKOVPWDRSWDUIUFZVTRFVTCLZONZCWDUJVTWEONVPWD
      WCRWBBWCUGVPBWCRVPWAWCFWARFWAAUHUKULUMVPWBBWCPZWFVPAUNKZWCSWBBWJPWIAUOBAU
      PWBBWJWCUQUTWBBWCURUSVPVRVSVPVRVPVQVPVQVPAADEVAZVBQTVCVPVSVPAVPAWKQTVCVDV
      PWHCWDWGWDFWGWCFZGWGMNZVEVPWHWBWMBWGWCWAWGGMVFVJVPWLWMWHWGAVGVHVIVKCWDVTV
      LVMBAVNVO $.

    $( Weak lower bound on the Pell fundamental solution.  (Contributed by
       Stefan O'Rear, 19-Sep-2014.) $)
    pellfundgt1 $p |- ( D e. ( NN \ []NN ) -> 1 < ( PellFund ` D ) ) $=
      ( cn csquarenn c1 caddc co csqrt cfv nnrpd rpsqrtcld rpred readdcld sqrt1
      wcel cr clt wbr c2 a1i cle cdif cpellfund 1red eldifi pellfundre eqeltrid
      peano2nnd 1lt2 oveq12i 1p1e2 eqtri breqtrri nnge1d cc0 nnred peano2re syl
      0le1 nnnn0d nn0ge0d sqrtled mpbid le2addd ltletrd pellfundge ) ABCUANZDAD
      EFZGHZAGHZEFZAUBHVFUCZVFVHVIVFVHVFVGVFVGVFAABCUDZUGZIJKZVFVIVFAVFAVLIJKZL
      ZAUEVFDDGHZVQEFZVJVKVFVQVQVFVQDOMVKUFZVSLVPDVRPQVFDRVRPUHVRDDEFRVQDVQDEMM
      UIUJUKULSVFVQVQVHVIVSVSVNVOVFDVGTQVQVHTQVFVGVMUMVFDVGVKUNDTQVFURSZVFAONVG
      ONVFAVLUOZAUPUQVFVGVFVGVMUSUTVAVBVFDATQVQVITQVFAVLUMVFDAVKVTWAVFAVFAVLUSU
      TVAVBVCVDAVEVD $.

    $( A nontrivial first quadrant solution is at least as large as the
       fundamental solution.  (Contributed by Stefan O'Rear, 19-Sep-2014.)
       (Proof shortened by AV, 15-Sep-2020.) $)
    pellfundlb $p |- ( ( D e. ( NN \ []NN ) /\ A e. ( Pell14QR ` D ) /\ 1 < A )
        -> ( PellFund ` D ) <_ A ) $=
      ( va vb vc vd wcel cfv c1 clt wbr cv cr cle wceq 3ad2ant1 wral pell14qrre
      1re wa cn csquarenn cdif cpell14qr cpellfund crab cinf pellfundval ssrab2
      w3a wss wrex ex ssrdv sstrid breq2 elrab wi ltle sylancr expimpd biimtrid
      ralrimiv breq1 ralbidv rspcev simp2 sylanbrc infrelb syl3anc eqbrtrd
      simp3 ) BUAUBUCGZABUDHZGZIAJKZUJZBUEHZICLZJKZCVNUFZMJUGZANVMVOVRWBOVPCBUH
      PVQWAMUKZDLZELZNKZEWAQZDMULZAWAGZWBANKVMVOWCVPVMWAVNMVTCVNUIVMFVNMVMFLZVN
      GWJMGWJBRUMUNUOPVQIMGZIWENKZEWAQZWHSVMVOWMVPVMWLEWAWEWAGWEVNGZIWEJKZTVMWL
      VTWOCWEVNVSWEIJUPUQVMWNWOWLVMWNTWKWEMGWOWLURSWEBRIWEUSUTVAVBVCPWGWMDIMWDI
      OWFWLEWAWDIWENVDVEVFUTVQVOVPWIVMVOVPVGVMVOVPVLVTVPCAVNVSAIJUPUQVHDEAWAVIV
      JVK $.

    ${
      $d x D $.  $d x A $.
      $( If a real is larger than the fundamental solution, there is a
         nontrivial solution less than it.  (Contributed by Stefan O'Rear,
         18-Sep-2014.) $)
      pellfundglb $p |- ( ( D e. ( NN \ []NN ) /\ A e. RR
            /\ ( PellFund ` D ) < A )
          -> E. x e. ( Pell1QR ` D ) ( ( PellFund ` D ) <_ x /\ x < A ) ) $=
        ( va wcel cr cfv clt wbr w3a cv cle wn wa c1 wrex 3ad2ant1 ltnled wss
        wi cn csquarenn cdif cpellfund cpell1qr cpell14qr crab wral pellfundval
        cinf wceq simp3 eqbrtrrd pellfundre eqeltrrd simp2 mpbid wne pell14qrre
        c0 ssrab2 ex ssrdv sstrid pell1qrss14 pellqrex ssrexv sylc rabn0 sylibr
        infmrgelbi syl3anc mtod rexnal breq2 elrab simprl simpl1 syl2anc simprr
        1red ltled jca wb elpell1qr2 syl mpbird sylan2b adantrr sselid biimtrid
        simpr a1i imp pellfundlb adantr sseldd simpl2 reximssdv ) CUAUBUCEZBFEZ
        CUDGZBHIZJZBAKZLIZMZXBXELIZXEBHIZNACUEGZODKZHIZDCUFGZUGZXDXFAXNUHZMXGAX
        NPXDXOBXNFHUJZLIZXDXPBHIXQMXDXBXPBHWTXAXBXPUKXCDCUIQZWTXAXCULUMXDXPBXDX
        BXPFXRWTXAXBFEXCCUNQUOWTXAXCUPZRUQXDXNFSZXNUTURZXAXOXQTXDXNXMFXLDXMVAZW
        TXAXMFSZXCWTDXMFWTXKXMEXKFEXKCUSVBVCQZVDXDXLDXMPZYAXDXJXMSZXLDXJPZYEWTX
        AYFXCCVEQWTXAYGXCDCVFQXLDXJXMVGVHXLDXMVIVJXSXTYAXAJXOXQAXNBVKVBVLVMXFAX
        NVNVJXDXEXNEZXEXJEZXGYHXDXEXMEZOXEHIZNZYIXLYKDXEXMXKXEOHVOVPZXDYLNZYIYJ
        OXELIZNZYNYJYOXDYJYKVQZYNOXEYNWAYNWTYJXEFEWTXAXCYLVRZYQXECUSVSXDYJYKVTW
        BWCYNWTYIYPWDYRXECWEWFWGWHWIXDYHXGNZNZXHXIYTWTYJYKXHWTXAXCYSVRYTXNXMXEY
        BXDYHXGVQWJZXDYHYKXGXDYHYKYHYLXDYKYMYLYKTXDYJYKWLWMWKWNWIXECWOVLYTXIXGX
        DYHXGVTYTXEBYTXMFXEXDYCYSYDWPUUAWQWTXAXCYSWRRWGWCWS $.
    $}

    $( The fundamental solution as an infimum is itself a solution, showing
       that the solution set is discrete.

       Since the fundamental solution is an infimum, there must be an element
       ge to Fund and lt 2*Fund.  If this element is equal to the fundamental
       solution we're done, otherwise use the infimum again to find another
       element which must be ge Fund and lt the first element; their ratio is a
       group element in (1,2), contradicting ~ pell14qrgapw .  (Contributed by
       Stefan O'Rear, 18-Sep-2014.) $)
    pellfundex $p |- ( D e. ( NN \ []NN ) -> ( PellFund ` D ) e. ( Pell1QR ` D
        ) ) $=
      ( va vb wcel cfv cle wbr c2 cmul co clt wa cr 2re sylancr cc0 a1i syl2anc
      c1 adantr cn csquarenn cdif cpellfund cv cpell1qr wrex pellfundre remulcl
      caddc 0red 1red 0lt1 pellfundgt1 lttrd elrpd ltaddrpd 2timesd pellfundglb
      recnd breqtrrd mpd3an23 wo cpell14qr pell1qrss14 sselda pell14qrre syldan
      wceq wi leloed simp-4l simp-4r simplr simprr ad3antrrr ad4antr wss sseldd
      ad2antrr simprl wb 2pos lemul2 syl112anc mpbid ltletrd w3a simp1 3ad2ant1
      cdiv simp2l simp2r pell14qrdivcl syl3anc mullidd simp3l eqbrtrd ltdivmul2
      pell14qrgt0 ltmuldiv simp3r mpbird wn simpll pell14qrgapw ltnsym pm2.21dd
      mpd syl22anc syl122anc r19.29a exp32 simp1r eqeltrd 3exp jaod sylbid impd
      simp2 rexlimdva ) AUAUBUCDZAUDEZBUEZFGZYDHYCIJZKGZLZBAUFEZUGZYCYIDZYBYFMD
      ZYCYFKGYJYBHMDZYCMDZYLNAUHZHYCUIOZYBYCYCYCUJJYFKYBYCYCYOYBYCYOYBPSYCYBUKY
      BULYOPSKGYBUMQAUNUOUPUQYBYCYBYCYOUTURVABYFAUSVBYBYHYKBYIYBYDYIDZLZYEYGYKY
      RYEYCYDKGZYCYDVIZVCYGYKVJZYRYCYDYBYNYQYOTYBYQYDAVDEZDZYDMDZYBYIUUBYDAVEZV
      FYDAVGZVHZVKYRYSUUAYTYRYSYGYKYRYSYGLZLZYCCUEZFGZUUJYDKGZLZYKCYIUUIUUJYIDZ
      LZUUMLZYBYQUUNUULYDHUUJIJZKGZYKYBYQUUHUUNUUMVLZYBYQUUHUUNUUMVMUUIUUNUUMVN
      ZUUOUUKUULVOUUPYDYFUUQYRUUDUUHUUNUUMUUGVPYBYLYQUUHUUNUUMYPVQUUPYMUUJMDZUU
      QMDNUUPYBUUJUUBDZUVAUUSUUPYIUUBUUJYBYIUUBVRZYQUUHUUNUUMUUEVQUUTVSUUJAVGZR
      ZHUUJUIOUUIYGUUNUUMYRYSYGVOVTUUPUUKYFUUQFGZUUOUUKUULWAUUPYNUVAYMPHKGZUUKU
      VFWBYBYNYQUUHUUNUUMYOVQUVEYMUUPNQUVGUUPWCQYCUUJHWDWEWFWGYBYQUUNLZUULUURLZ
      WHZYBYDUUJWKJZUUBDZSUVKKGZUVKHKGZYKYBUVHUVIWIZUVJYBUUCUVBUVLUVOUVJYIUUBYD
      YBUVHUVCUVIUUEWJZYBYQUUNUVIWLVSZUVJYIUUBUUJUVPYBYQUUNUVIWMVSZYDUUJAWNWOUV
      JSUUJIJZYDKGZUVMUVJUVSUUJYDKUVJUUJUVJUUJUVJYBUVBUVAUVOUVRUVDRZUTWPYBUVHUU
      LUURWQWRUVJSMDUUDUVAPUUJKGZUVTUVMWBUVJULUVJYBUUCUUDUVOUVQUUFRZUWAUVJYBUVB
      UWBUVOUVRUUJAWTRZSYDUUJXAWEWFUVJUVNUURYBUVHUULUURXBUVJUUDYMUVAUWBUVNUURWB
      UWCYMUVJNQUWAUWDYDHUUJWSWEXCYBUVLLZUVMUVNLZLZUVNYKUWEUVMUVNVOUWGHUVKKGZUV
      NXDZUWGYBUVLUVMUWHYBUVLUWFXEYBUVLUWFVNUWEUVMUVNWAUVKAXFWOUWGYMUVKMDZUWHUW
      IVJNUWEUWJUWFUVKAVGTHUVKXGOXIXHXJXKUUIYBUUDYSUUMCYIUGYBYQUUHXEYRUUDUUHUUG
      TYRYSYGWACYDAUSWOXLXMYRYTYGYKYRYTYGWHYCYDYIYRYTYGXTYBYQYTYGXNXOXPXQXRXSYA
      XI $.

    $( There are no solutions between 1 and the fundamental solution.
       (Contributed by Stefan O'Rear, 18-Sep-2014.) $)
    pellfund14gap $p |- ( ( D e. ( NN \ []NN ) /\ A e. ( Pell14QR ` D ) /\ ( 1
        <_ A /\ A < ( PellFund ` D ) ) ) -> A = 1 ) $=
      ( cn csquarenn cdif wcel cpell14qr cfv c1 cle wbr cpellfund clt wa w3a wn
      wceq wo cr mpbid simp3r pell14qrre 3adant3 pellfundre ltnled simpl1 simpr
      3ad2ant1 simpl2 pellfundlb syl3anc mtand simp3l wb 1re leloe sylancr sylc
      orel1 eqcomd ) BCDEFZABGHFZIAJKZABLHZMKZNZOZIAVGIAMKZPVHIAQZRZVIVGVHVDAJK
      ZVGVEVKPVAVBVCVEUAVGAVDVAVBASFZVFABUBUCZVAVBVDSFVFBUDUHUETVGVHNVAVBVHVKVA
      VBVFVHUFVAVBVFVHUIVGVHUGABUJUKULVGVCVJVAVBVCVEUMVGISFVLVCVJUNUOVMIAUPUQTV
      HVIUSURUT $.

    $( The fundamental Pell solution is a positive real.  (Contributed by
       Stefan O'Rear, 19-Sep-2014.) $)
    pellfundrp $p |- ( D e. ( NN \ []NN ) -> ( PellFund ` D ) e. RR+ ) $=
      ( csquarenn cdif wcel cpellfund cfv pellfundre cc0 0red 1red clt wbr 0lt1
      cn c1 a1i pellfundgt1 lttrd elrpd ) ANBCDZAEFZAGZTHOUATITJUBHOKLTMPAQRS
      $.

    $( The fundamental Pell solution is never 1.  (Contributed by Stefan
       O'Rear, 19-Sep-2014.) $)
    pellfundne1 $p |- ( D e. ( NN \ []NN ) -> ( PellFund ` D ) =/= 1 ) $=
      ( cn csquarenn cdif wcel c1 cpellfund cfv 1red pellfundgt1 gtned ) ABCDEZ
      FAGHLIAJK $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Logarithm laws generalized to an arbitrary base
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  Section should be obsolete because its contents are covered by section
  "Logarithms to an arbitrary base" now.

$)

  $( General logarithm is a real number.  (Contributed by Stefan O'Rear,
     19-Sep-2014.)  (New usage is discouraged.)  Use ~ relogbcl instead. $)
  reglogcl $p |- ( ( A e. RR+ /\ B e. RR+ /\ B =/= 1 ) -> ( ( log ` A ) / (
      log ` B ) ) e. RR ) $=
    ( crp wcel c1 wne w3a clog cfv relogcl 3ad2ant1 3ad2ant2 cc0 logne0 3adant1
    cr redivcld ) ACDZBCDZBEFZGAHIZBHIZRSUAPDTAJKSRUBPDTBJLSTUBMFRBNOQ $.

  $( General logarithm preserves "less than".  (Contributed by Stefan O'Rear,
     19-Sep-2014.)  (New usage is discouraged.)  Use ~ logblt instead. $)
  reglogltb $p |- ( ( ( A e. RR+ /\ B e. RR+ ) /\ ( C e. RR+ /\ 1 < C ) ) ->
      ( A < B <-> ( ( log ` A ) / ( log ` C ) ) < ( ( log ` B ) / ( log ` C )
      ) ) ) $=
    ( crp wcel wa c1 clt wbr clog cfv cdiv co wb logltb adantr relogcl ad2antrr
    cr cc0 ad2antlr ad2antrl log1 mpan biimpa eqbrtrrid adantl ltdiv1 syl112anc
    1rp bitrd ) ADEZBDEZFZCDEZGCHIZFZFZABHIZAJKZBJKZHIZUTCJKZLMVAVCLMHIZUNUSVBN
    UQABOPURUTSEZVASEZVCSEZTVCHIZVBVDNULVEUMUQAQRUMVFULUQBQUAUOVGUNUPCQUBUQVHUN
    UQTGJKZVCHUCUOUPVIVCHIZGDEUOUPVJNUJGCOUDUEUFUGUTVAVCUHUIUK $.

  $( General logarithm preserves ` <_ ` .  (Contributed by Stefan O'Rear,
     19-Oct-2014.)  (New usage is discouraged.)  Use ~ logbleb instead. $)
  reglogleb $p |- ( ( ( A e. RR+ /\ B e. RR+ ) /\ ( C e. RR+ /\ 1 < C ) ) ->
      ( A <_ B <-> ( ( log ` A ) / ( log ` C ) ) <_ ( ( log ` B ) / ( log ` C
      ) ) ) ) $=
    ( crp wcel wa c1 clt wbr cle clog cfv cdiv co wb logleb adantr cc0 relogcl
    cr ad2antrr ad2antlr ad2antrl log1 logltb biimpa eqbrtrrid adantl syl112anc
    1rp mpan lediv1 bitrd ) ADEZBDEZFZCDEZGCHIZFZFZABJIZAKLZBKLZJIZVBCKLZMNVCVE
    MNJIZUPVAVDOUSABPQUTVBTEZVCTEZVETEZRVEHIZVDVFOUNVGUOUSASUAUOVHUNUSBSUBUQVIU
    PURCSUCUSVJUPUSRGKLZVEHUDUQURVKVEHIZGDEUQURVLOUJGCUEUKUFUGUHVBVCVEULUIUM $.

  $( Multiplication law for general log.  (Contributed by Stefan O'Rear,
     19-Sep-2014.)  (New usage is discouraged.)  Use ~ relogbmul instead. $)
  reglogmul $p |- ( ( A e. RR+ /\ B e. RR+ /\ ( C e. RR+ /\ C =/= 1 ) ) -> (
      ( log ` ( A x. B ) ) / ( log ` C ) ) = ( ( ( log ` A ) / ( log ` C ) )
      + ( ( log ` B ) / ( log ` C ) ) ) ) $=
    ( crp wcel c1 wne wa w3a cmul co clog cfv cdiv caddc wceq cc recnd 3ad2ant3
    relogcl relogmul 3adant3 oveq1d 3ad2ant1 3ad2ant2 adantr cc0 logne0 divdird
    eqtrd ) ADEZBDEZCDEZCFGZHZIZABJKLMZCLMZNKALMZBLMZOKZURNKUSURNKUTURNKOKUPUQV
    AURNUKULUQVAPUOABUAUBUCUPUSUTURUKULUSQEUOUKUSATRUDULUKUTQEUOULUTBTRUEUOUKUR
    QEZULUMVBUNUMURCTRUFSUOUKURUGGULCUHSUIUJ $.

  $( Power law for general log.  (Contributed by Stefan O'Rear, 19-Sep-2014.)
     (New usage is discouraged.)  Use ~ relogbzexp instead. $)
  reglogexp $p |- ( ( A e. RR+ /\ N e. ZZ /\ ( C e. RR+ /\ C =/= 1 ) ) -> ( (
      log ` ( A ^ N ) ) / ( log ` C ) ) = ( N x. ( ( log ` A ) / ( log ` C )
      ) ) ) $=
    ( crp wcel cz c1 wne wa w3a cexp co clog cfv cdiv cc relogcl recnd 3ad2ant3
    cmul wceq relogexp 3adant3 oveq1d zcn 3ad2ant2 3ad2ant1 adantr logne0 eqtrd
    cc0 divassd ) ADEZCFEZBDEZBGHZIZJZACKLMNZBMNZOLCAMNZTLZUTOLCVAUTOLTLURUSVBU
    TOUMUNUSVBUAUQACUBUCUDURCVAUTUNUMCPEUQCUEUFUMUNVAPEUQUMVAAQRUGUQUMUTPEZUNUO
    VCUPUOUTBQRUHSUQUMUTUKHUNBUISULUJ $.

  $( General log of the base is 1.  (Contributed by Stefan O'Rear,
     19-Sep-2014.)  (New usage is discouraged.)  Use ~ logbid1 instead. $)
  reglogbas $p |- ( ( C e. RR+ /\ C =/= 1 ) -> ( ( log ` C ) / ( log ` C ) )
      = 1 ) $=
    ( crp wcel c1 wne wa clog cfv cc relogcl recnd adantr logne0 dividd ) ABCZA
    DEZFAGHZOQICPOQAJKLAMN $.

  $( General log of 1 is 0.  (Contributed by Stefan O'Rear, 19-Sep-2014.)
     (New usage is discouraged.)  Use ~ logb1 instead. $)
  reglog1 $p |- ( ( C e. RR+ /\ C =/= 1 ) -> ( ( log ` 1 ) / ( log ` C ) ) =
      0 ) $=
    ( crp wcel c1 wne wa clog cfv cdiv co cc0 log1 oveq1i relogcl adantr logne0
    cc recnd div0d eqtrid ) ABCZADEZFZDGHZAGHZIJKUEIJKUDKUEILMUCUEUAUEQCUBUAUEA
    NROAPST $.

  $( General log of a power of the base is the exponent.  (Contributed by
     Stefan O'Rear, 19-Sep-2014.)  (New usage is discouraged.)  Use ~ relogbexp
     instead. $)
  reglogexpbas $p |- ( ( N e. ZZ /\ ( C e. RR+ /\ C =/= 1 ) ) -> ( ( log ` (
      C ^ N ) ) / ( log ` C ) ) = N ) $=
    ( cz wcel crp c1 wne wa cexp clog cfv cdiv cmul wceq simprl simpl reglogexp
    co simpr syl3anc reglogbas adantl oveq2d cc zcn adantr mulridd 3eqtrd ) BCD
    ZAEDZAFGZHZHZABIRJKAJKZLRZBUNUNLRZMRZBFMRBUMUJUIULUOUQNUIUJUKOUIULPUIULSAAB
    QTUMUPFBMULUPFNUIAUAUBUCUMBUIBUDDULBUEUFUGUH $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Pell equations 4: the positive solution group is infinite cyclic
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x D $.  $d x A $.
    $( Every positive Pell solution is a power of the fundamental solution.
       (Contributed by Stefan O'Rear, 19-Sep-2014.) $)
    pellfund14 $p |- ( ( D e. ( NN \ []NN ) /\ A e. ( Pell14QR ` D ) ) ->
        E. x e. ZZ A = ( ( PellFund ` D ) ^ x ) ) $=
      ( wcel cfv clog cdiv co cz cexp wceq crp adantr cle wbr clt caddc syl2anc
      c1 cc0 cn csquarenn cdif cpell14qr wa cpellfund cfl cv wrex cr pell14qrrp
      pellfundrp pellfundne1 reglogcl syl3anc flcld cneg pell14qrre recnd rpcnd
      rpexpcld znegcld rpne0d cmul simpl cpell1qr pell1qrss14 pellfundex sseldd
      wne pell14qrexpcl pell14qrmulcl mpd3an3 cmo 1rp cmin zcnd negsubd modfrac
      a1i modge0 syl breqtrrd reglog1 reglogmul syl112anc reglogexpbas syl12anc
      eqtr4d oveq2d eqtrd 3brtr4d rpmulcld pellfundgt1 reglogleb syl22anc modlt
      wb mpbird eqbrtrd reglogbas reglogltb pellfund14gap negidd exp0d 3eqtr3rd
      cc expaddz mulcan2ad oveq2 rspceeqv ) CUAUBUCDZBCUDEZDZUEZBFECUFEZFEZGHZU
      GEZIDZBXPXSJHZKBXPAUHZJHZKAIUIXOXRXOBLDZXPLDZXPSVJZXRUJDZBCUKZXLYEXNCULMZ
      XLYFXNCUMMZBXPUNUOZUPZXOBYAXPXSUQZJHZXOBBCURUSXOYAXOXPXSYIYLVAUTXOYNXOXPY
      MYIXOXSYLVBZVAZUTXOYNYPVCXOBYNVDHZSYAYNVDHZXOXLYQXMDZSYQNOZYQXPPOZYQSKXLX
      NVEZXLXNYNXMDZYSXOXLXPXMDZYMIDZUUCUUBXLUUDXNXLCVFEXMXPCVGCVHVIMYOXPYMCVKU
      OBYNCVLVMXOYTSFEXQGHZYQFEXQGHZNOZXOTXRYMQHZUUFUUGNXOTXRSVNHZUUINXOYGSLDZT
      UUJNOYKUUKXOVOVTZXRSWARXOUUIXRXSVPHZUUJXOXRXSXOXRYKUSXOXSYLVQZVRXOYGUUJUU
      MKYKXRVSWBWIZWCXOYEYFUUFTKYIYJXPWDRXOUUGXRYNFEXQGHZQHZUUIXOYDYNLDYEYFUUGU
      UQKYHYPYIYJBYNXPWEWFXOUUPYMXRQXOUUEYEYFUUPYMKYOYIYJXPYMWGWHWJWKZWLXOUUKYQ
      LDZYESXPPOZYTUUHWRUULXOBYNYHYPWMZYIXLUUTXNCWNMZSYQXPWOWPWSXOUUAUUGXQXQGHZ
      POZXOUUISUUGUVCPXOUUIUUJSPUUOXOYGUUKUUJSPOYKUULXRSWQRWTUURXOYEYFUVCSKYIYJ
      XPXARWLXOUUSYEYEUUTUUAUVDWRUVAYIYIUVBYQXPXPXBWPWSYQCXCWFXOXPXSYMQHZJHZXPT
      JHYRSXOUVETXPJXOXSUUNXDWJXOXPXGDXPTVJXTUUEUVFYRKXOXPYIUTZXOXPYIVCYLYOXPXS
      YMXHWPXOXPUVGXEXFWKXIAXSIYCYABYBXSXPJXJXKR $.

    $( The positive Pell solutions are precisely the integer powers of the
       fundamental solution.  To get the general solution set (which we will
       not be using), throw in a copy of Z/2Z. (Contributed by Stefan O'Rear,
       19-Sep-2014.) $)
    pellfund14b $p |- ( D e. ( NN \ []NN ) -> ( A e. ( Pell14QR ` D ) <->
        E. x e. ZZ A = ( ( PellFund ` D ) ^ x ) ) ) $=
      ( cn csquarenn cdif wcel cpell14qr cfv cpellfund cv cexp co cz pellfund14
      wceq wrex wa simpll cpell1qr pell1qrss14 pellfundex sseldd simplr syl3anc
      ad2antrr pell14qrexpcl wb eleq1 adantl mpbird r19.29an impbida ) CDEFGZBC
      HIZGZBCJIZAKZLMZPZANQABCOUNUTUPANUNURNGZRZUTRZUPUSUOGZVCUNUQUOGZVAVDUNVAU
      TSUNVEVAUTUNCTIUOUQCUACUBUCUFUNVAUTUDUQURCUGUEUTUPVDUHVBBUSUOUIUJUKULUM
      $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  X and Y sequences 1: Definition and recurrence laws
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c rmX rmY $.

  $( Extend class notation to include the Robertson-Matiyasevich X sequence. $)
  crmx $a class rmX $.
  $( Extend class notation to include the Robertson-Matiyasevich Y sequence. $)
  crmy $a class rmY $.

  ${
    $d a n b $.
    $( Define the X sequence as the rational part of some solution of a special
       Pell equation.  See ~ frmx and ~ rmxyval for a more useful but
       non-eliminable definition.  (Contributed by Stefan O'Rear,
       21-Sep-2014.) $)
    df-rmx $a |- rmX = ( a e. ( ZZ>= ` 2 ) , n e. ZZ |-> ( 1st ` ( `' ( b e. (
        NN0 X. ZZ ) |-> ( ( 1st ` b ) + ( ( sqrt ` ( ( a ^ 2 ) - 1 ) ) x. ( 2nd
        ` b ) ) ) ) ` ( ( a + ( sqrt ` ( ( a ^ 2 ) - 1 ) ) ) ^ n ) ) ) ) $.
    $( Define the X sequence as the irrational part of some solution of a
       special Pell equation.  See ~ frmy and ~ rmxyval for a more useful but
       non-eliminable definition.  (Contributed by Stefan O'Rear,
       21-Sep-2014.) $)
    df-rmy $a |- rmY = ( a e. ( ZZ>= ` 2 ) , n e. ZZ |-> ( 2nd ` ( `' ( b e. (
        NN0 X. ZZ ) |-> ( ( 1st ` b ) + ( ( sqrt ` ( ( a ^ 2 ) - 1 ) ) x. ( 2nd
        ` b ) ) ) ) ` ( ( a + ( sqrt ` ( ( a ^ 2 ) - 1 ) ) ) ^ n ) ) ) ) $.
  $}

  ${
    $d a n b A $.  $d a n b N $.
    $( Value of the X sequence.  Not used after ~ rmxyval is proved.
       (Contributed by Stefan O'Rear, 21-Sep-2014.) $)
    rmxfval $p |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. ZZ ) -> ( A rmX N ) = ( 1st ` (
       `' ( b e. ( NN0 X. ZZ ) |-> ( ( 1st ` b ) + ( ( sqrt ` ( ( A ^ 2 ) - 1 )
        ) x. ( 2nd ` b ) ) ) ) ` ( ( A + ( sqrt ` ( ( A ^ 2 ) - 1 ) ) ) ^ N ) )
        ) ) $=
      ( va vn c2 cfv cz cv cexp co c1 cmin csqrt caddc c1st cmul cmpt ccnv wceq
      cuz cn0 cxp c2nd crmx oveq1 fvoveq1d oveq1d oveq2d mpteq2dv cnveqd adantr
      wa id oveq12d oveqan12d fveq12d fveq2d df-rmx fvex ovmpoa ) DEABFUAGHDIZV
      BFJKZLMKNGZOKZEIZJKZCUBHUCZCIZPGZVDVIUDGZQKZOKZRZSZGZPGAAFJKZLMKNGZOKZBJK
      ZCVHVJVRVKQKZOKZRZSZGZPGUEVBATZVFBTZUMZVPWEPWHVGVTVOWDWFVOWDTWGWFVNWCWFCV
      HVMWBWFVLWAVJOWFVDVRVKQWFVCVQLNMVBAFJUFUGZUHUIUJUKULWFWGVEVSVFBJWFVBAVDVR
      OWFUNWIUOWGUNUPUQUREDCUSWEPUTVA $.

    $( Value of the Y sequence.  Not used after ~ rmxyval is proved.
       (Contributed by Stefan O'Rear, 21-Sep-2014.) $)
    rmyfval $p |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. ZZ ) -> ( A rmY N ) = ( 2nd ` (
       `' ( b e. ( NN0 X. ZZ ) |-> ( ( 1st ` b ) + ( ( sqrt ` ( ( A ^ 2 ) - 1 )
        ) x. ( 2nd ` b ) ) ) ) ` ( ( A + ( sqrt ` ( ( A ^ 2 ) - 1 ) ) ) ^ N ) )
        ) ) $=
      ( va vn c2 cfv cz cv cexp co c1 cmin csqrt caddc c2nd cmul cmpt ccnv wceq
      cuz cn0 cxp c1st crmy oveq1 fvoveq1d oveq1d oveq2d mpteq2dv cnveqd adantr
      wa id oveq12d oveqan12d fveq12d fveq2d df-rmy fvex ovmpoa ) DEABFUAGHDIZV
      BFJKZLMKNGZOKZEIZJKZCUBHUCZCIZUDGZVDVIPGZQKZOKZRZSZGZPGAAFJKZLMKNGZOKZBJK
      ZCVHVJVRVKQKZOKZRZSZGZPGUEVBATZVFBTZUMZVPWEPWHVGVTVOWDWFVOWDTWGWFVNWCWFCV
      HVMWBWFVLWAVJOWFVDVRVKQWFVCVQLNMVBAFJUFUGZUHUIUJUKULWFWGVEVSVFBJWFVBAVDVR
      OWFUNWIUOWGUNUPUQUREDCUSWEPUTVA $.
  $}

  $( The discriminant used to define the X and Y sequences has an irrational
     square root.  (Contributed by Stefan O'Rear, 21-Sep-2014.)  (Proof
     shortened by AV, 2-Aug-2021.) $)
  rmspecsqrtnq $p |- ( A e. ( ZZ>= ` 2 )
      -> ( sqrt ` ( ( A ^ 2 ) - 1 ) ) e. ( CC \ QQ ) ) $=
    ( c2 cfv wcel cexp co c1 cmin cc cq ax-1cn sylancl cn0 clt caddc cn nnm1nn0
    wbr syl cr cuz csqrt eluzelcn sqcld subcl sqrtcld eluz2nn nnsqcld cmul wceq
    wn binom2sub1 2cnd mulcld a1i subsubd eqtr4d 2re eluzelre remulcld resubcld
    1red nnred eluz2gt1 lt2addmuld remulcl sylancr mpbid ltsub2dd eqbrtrd ltm1d
    ltaddsubd npcan oveq1d breqtrrd nonsq syl22anc eldifd ) ABUACDZABEFZGHFZUBC
    ZIJVSWAVSVTIDGIDZWAIDVSABAUCZUDZKVTGUELUFVSWAMDZAGHFZMDZWGBEFZWANRWAWGGOFZB
    EFZNRWBJDUKVSVTPDWFVSAAUGZUHZVTQSVSAPDWHWLAQSVSWIVTBAUIFZGHFZHFZWANVSWIVTWN
    HFGOFZWPVSAIDZWIWQUJWDAULSVSVTWNGWEVSBAVSUMWDUNWCVSKUOUPUQVSGWOVTVSVBZVSWNG
    VSBABTDZVSURUOBAUSZUTWSVAVSVTWMVCZVSGGOFWNNRGWONRVSGGAWSWSXAAVDZXCVEVSGGWNW
    SWSVSWTATDWNTDURXABAVFVGVLVHVIVJVSWAVTWKNVSVTXBVKVSWJABEVSWRWCWJAUJWDKAGVML
    VNVOWAWGVPVQVR $.

  ${
    $d a A $.
    $( The discriminant used to define the X and Y sequences is a nonsquare
       positive integer and thus a valid Pell equation discriminant.
       (Contributed by Stefan O'Rear, 21-Sep-2014.) $)
    rmspecnonsq $p |- ( A e. ( ZZ>= ` 2 ) -> ( ( A ^ 2 ) - 1 ) e. ( NN \ []NN )
        ) $=
      ( va c2 cuz cfv wcel cexp co c1 cn csquarenn cz cc0 clt wbr eluzelz mpbid
      cmin csqrt cq syl 1zzd zsubcld sq1 eluz2b2 simprbi 1red eluzelre cle 0le1
      zsqcl a1i eluzge2nn0 nn0ge0d lt2sqd eqbrtrrid resqcld posdifd sylanbrc wa
      elnnz cc rmspecsqrtnq eldifbd intnand crab df-squarenn eleq2i wceq eleq1d
      cv fveq2 elrab bitr2i sylnib eldifd ) ACDEFZACGHZIRHZJKVQVSLFMVSNOZVSJFZV
      QVRIVQALFVRLFCAPAUKUAVQUBUCVQIVRNOVTVQIICGHZVRNUDVQIANOZWBVRNOVQAJFWCAUEU
      FVQIAVQUGZCAUHZMIUIOVQUJULVQAAUMUNUOQUPVQIVRWDVQAWEUQURQVSVAUSVQWAVSSEZTF
      ZUTZVSKFZVQWGWAVQWFVBTAVCVDVEWIVSBVKZSEZTFZBJVFZFWHKWMVSBVGVHWLWGBVSJWJVS
      VIWKWFTWJVSSVLVJVMVNVOVP $.
  $}

  $( This lemma implements the concept of "equate rational and irrational
     parts", used to prove many arithmetical properties of the X and Y
     sequences.  (Contributed by Stefan O'Rear, 21-Sep-2014.) $)
  qirropth $p |- ( ( A e. ( CC \ QQ ) /\ ( B e. QQ /\ C e. QQ ) /\ ( D e. QQ /\
      E e. QQ ) ) -> ( ( B + ( A x. C ) ) = ( D + ( A x. E ) ) <-> ( B = D /\ C
      = E ) ) ) $=
    ( cc cq wcel wa cmul caddc wceq adantr cmin ad2antrr qcn syl syl2anc mulcld
    co cdif wn eldifn 3ad2ant1 cdiv simpll1 eldifad simp2r simp3r subdid qsubcl
    w3a mulcomd simplr simp2l simp3l addsubeq4d mpbid 3eqtr4d cc0 wne wb subeq0
    simpr necon3abid mpbird divmuld qdivcl syl3anc eqeltrrd mt3d simpl2l simpl1
    simpl3l simpl3r eqcomd oveq2d eqtrd addcan2ad jcai ancomd oveqan12d impbid1
    ex id oveq2 ) AFGUAHZBGHZCGHZIZDGHZEGHZIZULZBACJTZKTZDAEJTZKTZLZBDLZCELZIZW
    NWSXBWNWSIZXAWTXCXAWTXCXAAGHZWNXDUBZWSWGWJXEWMAFGUCUDMXCXAUBZXDXCXFIZDBNTZC
    ENTZUETZAGXGXJALXIAJTZXHLXGAXIJTWOWQNTZXKXHXGACEXGAFGWGWJWMWSXFUFUGZXGWICFH
    ZWNWIWSXFWGWHWIWMUHOZCPQZXGWLEFHZWNWLWSXFWGWJWKWLUIOZEPZQZUJXGXIAXGXIGHZXIF
    HXGWIWLYAXOXRCEUKRZXIPQZXMUMXGWSXHXLLWNWSXFUNXGBWODWQXGWHBFHZWNWHWSXFWGWHWI
    WMUOOZBPZQXGACXMXPSXGWKDFHZWNWKWSXFWGWJWKWLUPOZDPZQXGAEXMXTSUQURUSXGXHXIAXG
    XHGHZXHFHXGWKWHYJYHYEDBUKRZXHPQYCXMXGXIUTVAZXFXCXFVDXGXNXQYLXFVBXPXTXNXQIXA
    XIUTCEVCVERVFZVGVFXGYJYAYLXJGHYKYBYMXHXIVHVIVJWDVKXCXAWTXCXAIZBDWQXCYDXAXCW
    HYDWHWIWGWMWSVLYFQMXCYGXAXCWKYGWKWLWGWJWSVNYIQMXCWQFHXAXCAEXCAFGWGWJWMWSVMU
    GXCWLXQWKWLWGWJWSVOXSQSMYNBWQKTWPWRYNWQWOBKYNECAJYNCEXCXAVDVPVQVQWNWSXAUNVR
    VSWDVTWAWDWTXABDWOWQKWTWECEAJWFWBWC $.

  $( The base of exponent used to define the X and Y sequences is the
     fundamental solution of the corresponding Pell equation.  (Contributed by
     Stefan O'Rear, 21-Sep-2014.) $)
  rmspecfund $p |- ( A e. ( ZZ>= ` 2 ) -> ( PellFund ` ( ( A ^ 2 ) - 1 ) ) = (
      A + ( sqrt ` ( ( A ^ 2 ) - 1 ) ) ) ) $=
    ( c2 cfv wcel cexp co c1 cmin csqrt caddc wceq cle wbr cn clt cmul cz recnd
    syl a1i cuz cpellfund csquarenn cdif cpell14qr rmspecnonsq eluzelz resubcld
    zsqcl zred 1red cc0 eluz2b2 simprbi eluzelre 0le1 eluzge2nn0 nn0ge0d lt2sqd
    sq1 mpbid eqbrtrrd posdifd elrpd rpsqrtcld rpred mulridd oveq2d pell1qrss14
    cpell1qr wss cn0 1nn0 oveq2i eqtrid 1cnd nncand eqtrd pellqrexplicit sseldd
    syl31anc eqeltrrd readdcld ltaddrpd ltadd1dd lttrd pellfundlb npcand fveq2d
    syl3anc sqrtsqd oveq1d pellfundge cr pellfundre letri3d mpbir2and ) ABUACDZ
    ABEFZGHFZUBCZAWTICZJFZKXAXCLMZXCXALMWRWTNUCUDDZXCWTUECZDGXCOMXDAUFZWRAXBGPF
    ZJFZXCXFWRXHXBAJWRXBWRXBWRXBWRWTWRWTWRWSGWRWSWRAQDWSQDBAUGAUISUJZWRUKZUHZWR
    GWSOMULWTOMWRGBEFZGWSOXMGKWRUTTWRGAOMZXMWSOMWRANDXNAUMUNZWRGAXKBAUOZULGLMWR
    UPTWRAAUQZURZUSVAVBWRGWSXKXJVCVAVDVEZVFZRVGVHWRWTVJCZXFXIWRXEYAXFVKXGWTVISW
    RXEAVLDGVLDZWSWTXMPFZHFZGKXIYADXGXQYBWRVMTWRYDWSWTHFGWRYCWTWSHWRYCWTGPFWTXM
    GWTPUTVNWRWTWRWTXLRVGVOVHWRWSGWRWSXJRZWRVPZVQVRAGWTVSWAVTWBWRGGXBJFXCXKWRGX
    BXKXTWCWRAXBXPXTWCZWRGXBXKXSWDWRGAXBXKXPXTXOWEWFXCWTWGWJWRWTGJFZICZXBJFZXCX
    ALWRYIAXBJWRYIWSICAWRYHWSIWRWSGYEYFWHWIWRAXPXRWKVRWLWRXEYJXALMXGWTWMSVBWRXA
    XCWRXEXAWNDXGWTWOSYGWPWQ $.

  ${
    $d A a c d $.  $d N a $.
    $( The solutions used to construct the X and Y sequences are quadratic
       irrationals.  (Contributed by Stefan O'Rear, 21-Sep-2014.)  (Proof
       shortened by SN, 23-Dec-2024.) $)
    rmxyelqirr $p |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. ZZ ) -> ( ( A + ( sqrt ` ( (
        A ^ 2 ) - 1 ) ) ) ^ N ) e. { a | E. c e. NN0 E. d e. ZZ a = ( c + ( (
        sqrt ` ( ( A ^ 2 ) - 1 ) ) x. d ) ) } ) $=
      ( c2 cfv wcel cz wa cexp co c1 cmin cv cmul caddc wceq wrex cn0 cpell14qr
      cuz csqrt cab cr crab cn csquarenn rmspecnonsq adantr pell14qrval rabssab
      cdif simpl reximi ss2abi sstri eqsstrdi cpellfund simpr rmspecfund eqcomd
      syl oveq1d oveq2 rspceeqv syl2anc wb pellfund14b mpbird sseldd ) AFUBGHZB
      IHZJZAFKLMNLZUAGZCOZDOZVOUCGZEOZPLQLRZEISZDTSZCUDZAVSQLZBKLZVNVPWAVRFKLVO
      VTFKLPLNLMRZJZEISZDTSZCUEUFZWDVNVOUGUHUMHZVPWKRVLWLVMAUIUJZCDEVOUKVCWKWJC
      UDWDWJCUEULWJWCCWIWBDTWHWAEIWAWGUNUOUOUPUQURVNWFVPHZWFVOUSGZVQKLZRCISZVNV
      MWFWOBKLZRWQVLVMUTVNWEWOBKVNWOWEVLWOWERVMAVAUJVBVDCBIWPWRWFVQBWOKVEVFVGVN
      WLWNWQVHWMCWFVOVIVCVJVK $.
  $}

  ${
    $d b c d a A $.
    $( The function used to extract rational and irrational parts in ~ df-rmx
       and ~ df-rmy in fact achieves a one-to-one mapping from the quadratic
       irrationals to pairs of integers.  (Contributed by Stefan O'Rear,
       21-Sep-2014.) $)
    rmxypairf1o $p |- ( A e. ( ZZ>= ` 2 ) -> ( b e. ( NN0 X. ZZ ) |-> ( ( 1st `
        b ) + ( ( sqrt ` ( ( A ^ 2 ) - 1 ) ) x. ( 2nd ` b ) ) ) ) : ( NN0 X. ZZ
        ) -1-1-onto-> { a | E. c e. NN0 E. d e. ZZ a = ( c + ( ( sqrt ` ( ( A ^
        2 ) - 1 ) ) x. d ) ) } ) $=
      ( cfv wcel cn0 cz cv c1st co c2nd cmul caddc wceq wrex ovex fveq2 cq cexp
      c2 cuz cxp c1 cmin csqrt cmpt wfn crn cab wral wf1o eqid fnmpti a1i rnmpt
      wi wb cop op1std op2ndd oveq2d oveq12d eqeq2d rexxp bicomi abbidv eqtr4id
      vex wa fvmpt ad2antrl ad2antll eqeq12d cc cdif rmspecsqrtnq adantr nn0ssq
      xp1st sselid zq syl qirropth syl122anc biimpd xpopth adantl sylibd sylbid
      xp2nd ralrimivva dff1o6 syl3anbrc ) AUBUCFGZCHIUDZCJZKFZAUBUALUEUFLUGFZWR
      MFZNLZOLZUHZWQUIZXDUJZBJZDJZWTEJZNLZOLZPZEIQDHQZBUKZPXHXDFZXIXDFZPZXHXIPZ
      URZEWQULDWQULWQXNXDUMXEWPCWQXCXDWSXBORXDUNZUOUPWPXFXGXCPZCWQQZBUKXNCBWQXC
      XDXTUQWPXMYBBXMYBUSWPYBXMYAXLCDEHIWRXHXIUTPZXCXKXGYCWSXHXBXJOXHXIWRDVJZEV
      JZVAYCXAXIWTNXHXIWRYDYEVBVCVDVEVFVGUPVHVIWPXSDEWQWQWPXHWQGZXIWQGZVKZVKZXQ
      XHKFZWTXHMFZNLZOLZXIKFZWTXIMFZNLZOLZPZXRYIXOYMXPYQYFXOYMPWPYGCXHXCYMWQXDW
      RXHPZWSYJXBYLOWRXHKSYSXAYKWTNWRXHMSVCVDXTYJYLORVLVMYGXPYQPWPYFCXIXCYQWQXD
      WRXIPZWSYNXBYPOWRXIKSYTXAYOWTNWRXIMSVCVDXTYNYPORVLVNVOYIYRYJYNPYKYOPVKZXR
      YIYRUUAYIWTVPTVQGZYJTGYKTGZYNTGYOTGZYRUUAUSWPUUBYHAVRVSYIHTYJVTYFYJHGWPYG
      XHHIWAVMWBYIYKIGZUUCYFUUEWPYGXHHIWLVMYKWCWDYIHTYNVTYGYNHGWPYFXIHIWAVNWBYI
      YOIGZUUDYGUUFWPYFXIHIWLVNYOWCWDWTYJYKYNYOWEWFWGYHUUAXRUSWPXHXIHIHIWHWIWJW
      KWMDEWQXNXDWNWO $.
  $}

  ${
    $d a b c d A $.  $d a N $.
    $( Lemma for ~ frmx and ~ frmy .  (Contributed by Stefan O'Rear,
       22-Sep-2014.) $)
    rmxyelxp $p |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. ZZ )
        -> ( `' ( b e. ( NN0 X. ZZ ) |-> ( ( 1st ` b )
          + ( ( sqrt ` ( ( A ^ 2 ) - 1 ) ) x. ( 2nd ` b ) ) ) ) ` ( ( A
          + ( sqrt ` ( ( A ^ 2 ) - 1 ) ) ) ^ N ) ) e. ( NN0 X. ZZ ) ) $=
      ( va vc vd c2 cuz cfv wcel cz wa cn0 cxp cv cexp co cmul caddc wrex csqrt
      c1 cmin wceq cab c1st c2nd cmpt wf1o ccnv rmxypairf1o rmxyelqirr f1ocnvdm
      adantr syl2anc ) AGHIJZBKJZLMKNZDOEOAGPQUBUCQUAIZFORQSQUDFKTEMTDUEZCURCOZ
      UFIUSVAUGIRQSQUHZUIZAUSSQBPQZUTJVDVBUJIURJUPVCUQADCEFUKUNABDEFULURUTVDVBU
      MUO $.
  $}

  ${
    $d a b c $.
    $( The X sequence is a nonnegative integer.  See ~ rmxnn for a
       strengthening.  (Contributed by Stefan O'Rear, 22-Sep-2014.) $)
    frmx $p |- rmX : ( ( ZZ>= ` 2 ) X. ZZ ) --> NN0 $=
      ( va vb vc cv c2 cexp co cmin csqrt cfv caddc cn0 cxp c1st c2nd wcel wral
      c1 cz crmx cmul cmpt ccnv cuz wf wa rmxyelxp xp1st rgen2 df-rmx fmpo mpbi
      syl ) ADZUNEFGRHGIJZKGBDZFGCLSMZCDZNJUOUROJUAGKGUBUCJZNJZLPZBSQAEUDJZQVBS
      MLTUEVAABVBSUNVBPUPSPUFUSUQPVAUNUPCUGUSLSUHUMUIABVBSUTLTBACUJUKUL $.

    $( The Y sequence is an integer.  (Contributed by Stefan O'Rear,
       22-Sep-2014.) $)
    frmy $p |- rmY : ( ( ZZ>= ` 2 ) X. ZZ ) --> ZZ $=
      ( va vb vc cv c2 cexp co cmin csqrt cfv caddc cn0 cxp c1st c2nd wcel wral
      c1 cz crmy cmul cmpt ccnv cuz wf wa rmxyelxp xp2nd rgen2 df-rmy fmpo mpbi
      syl ) ADZUNEFGRHGIJZKGBDZFGCLSMZCDZNJUOUROJUAGKGUBUCJZOJZSPZBSQAEUDJZQVBS
      MSTUEVAABVBSUNVBPUPSPUFUSUQPVAUNUPCUGUSLSUHUMUIABVBSUTSTBACUJUKUL $.
  $}

  ${
    $d a b c d A $.  $d a b c N $.
    $( Main definition of the X and Y sequences.  Compare definition 2.3 of
       [JonesMatijasevic] p. 694.  (Contributed by Stefan O'Rear,
       19-Oct-2014.) $)
    rmxyval $p |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. ZZ )
        -> ( ( A rmX N ) + ( ( sqrt ` ( ( A ^ 2 ) - 1 ) ) x. ( A rmY N ) ) )
            = ( ( A + ( sqrt ` ( ( A ^ 2 ) - 1 ) ) ) ^ N ) ) $=
      ( vb va vc vd c2 cfv wcel cz co cmul caddc c1st c2nd oveq2d oveq12d fveq2
      cv wceq cuz wa crmx cexp c1 cmin csqrt crmy cn0 cmpt ccnv rmxfval rmyfval
      cxp rmxyelxp weq cbvmptv ovex fvmpt syl cab rmxypairf1o adantr rmxyelqirr
      wrex wf1o f1ocnvfv2 syl2anc 3eqtr2d ) AGUAHIZBJIZUBZABUCKZAGUDKUEUFKUGHZA
      BUHKZLKZMKAVNMKBUDKZCUIJUNZCSZNHZVNVSOHZLKZMKZUJZUKHZNHZVNWEOHZLKZMKZWEWD
      HZVQVLVMWFVPWHMABCULVLVOWGVNLABCUMPQVLWEVRIWJWITABCUODWEDSZNHZVNWKOHZLKZM
      KZWIVRWDWKWETZWLWFWNWHMWKWENRWPWMWGVNLWKWEORPQCDVRWCWOCDUPZVTWLWBWNMVSWKN
      RWQWAWMVNLVSWKORPQUQWFWHMURUSUTVLVRWKESVNFSLKMKTFJVEEUIVEDVAZWDVFZVQWRIWJ
      VQTVJWSVKADCEFVBVCABDEFVDVRWRVQWDVGVHVI $.
  $}

  $( The discriminant used to define the X and Y sequences is a positive real.
     (Contributed by Stefan O'Rear, 22-Sep-2014.) $)
  rmspecpos $p |- ( A e. ( ZZ>= ` 2 ) -> ( ( A ^ 2 ) - 1 ) e. RR+ ) $=
    ( c2 cuz cfv wcel cexp co c1 cmin eluzelre resqcld resubcld clt wbr cc0 sq1
    1red cz eluz2b1 mpbid simprbi cle 0le1 eluzge2nn0 nn0ge0d eqbrtrrid posdifd
    a1i lt2sqd elrpd ) ABCDEZABFGZHIGZUKULHUKABAJZKZUKQZLUKHULMNOUMMNUKHHBFGZUL
    MPUKHAMNZUQULMNUKAREURASUAUKHAUPUNOHUBNUKUCUHUKAAUDUEUITUFUKHULUPUOUGTUJ $.

  ${
    $d A n $.  $d X n $.  $d Y n $.  $d X x y $.  $d Y x y $.  $d A x y $.
    $( The X and Y sequences taken together enumerate all solutions to the
       corresponding Pell equation in the right half-plane.  This is Metamath
       100 proof #39.  (Contributed by Stefan O'Rear, 22-Sep-2014.) $)
    rmxycomplete $p |- ( ( A e. ( ZZ>= ` 2 ) /\ X e. NN0 /\ Y e. ZZ ) -> ( ( (
        X ^ 2 ) - ( ( ( A ^ 2 ) - 1 ) x. ( Y ^ 2 ) ) ) = 1 <-> E. n e. ZZ ( X =
        ( A rmX n ) /\ Y = ( A rmY n ) ) ) ) $=
      ( vx vy c2 wcel cn0 cz cexp co c1 cmin cmul caddc wceq wa cq adantr csqrt
      cuz cfv w3a cpell14qr cpellfund wrex crmx crmy csquarenn cdif rmspecnonsq
      cv cn wb 3ad2ant1 pellfund14b cr nn0re 3ad2ant2 rmspecpos rpsqrtcld rpred
      syl 3ad2ant3 remulcld readdcld biantrurd simpl2 simpl3 eqidd simpr eqeq2d
      zre oveq1 oveq1d eqeq1d anbi12d oveq2 oveq2d syl112anc ex cc rmspecsqrtnq
      rspc2ev nn0ssq simp2 sselid zq sseli ad2antrl ad2antll qirropth syl122anc
      biimpd anim1d eqcomd biimpa syl6 rexlimdvva impbid elpell14qr 3bitr4d cxp
      oveqan12d wf frmx simpl1 fovcdmd zssq rmxyval 3ad2antl1 rmspecfund eqtr4d
      a1i frmy bitr3d rexbidva ) AGUBUCZHZCIHZDJHZUDZCAGKLMNLZUAUCZDOLZPLZYDUEU
      CHZYGYDUFUCZBUMZKLZQZBJUGZCGKLZYDDGKLZOLZNLZMQZCAYJUHLZQDAYJUILZQRZBJUGYC
      YDUNUJUKHZYHYMUOXTYAUUBYBAULUPZBYGYDUQVDYCYGEUMZYEFUMZOLZPLZQZUUDGKLZYDUU
      EGKLZOLZNLZMQZRZFJUGEIUGZYGURHZUUORZYRYHYCUUPUUOYCCYFYAXTCURHYBCUSUTYCYED
      XTYAYEURHYBXTYEXTYDAVAVBVCUPYBXTDURHYADVNVEVFVGVHYCYRUUOYCYRUUOYCYRRZYAYB
      YGYGQZYRUUOXTYAYBYRVIXTYAYBYRVJUURYGVKYCYRVLUUNUUSYRRYGCUUFPLZQZYNUUKNLZM
      QZREFCDIJUUDCQZUUHUVAUUMUVCUVDUUGUUTYGUUDCUUFPVOVMUVDUULUVBMUVDUUIYNUUKNU
      UDCGKVOVPVQVRUUEDQZUVAUUSUVCYRUVEUUTYGYGUVEUUFYFCPUUEDYEOVSVTVMUVEUVBYQMU
      VEUUKYPYNNUVEUUJYOYDOUUEDGKVOVTVTVQVRWEWAWBYCUUNYREFIJYCUUDIHZUUEJHZRZRZU
      UNCUUDQZDUUEQZRZUUMRYRUVIUUHUVLUUMUVIUUHUVLUVIYEWCSUKHZCSHZDSHZUUDSHZUUES
      HZUUHUVLUOYCUVMUVHXTYAUVMYBAWDUPZTYCUVNUVHYCISCWFXTYAYBWGWHZTYCUVOUVHYBXT
      UVOYADWIVEZTUVFUVPYCUVGISUUDWFWJWKUVGUVQYCUVFUUEWIWLYECDUUDUUEWMWNWOWPUVL
      UUMYRUVLUULYQMUVLYQUULUVJUVKYNUUIYPUUKNCUUDGKVOUVKYOUUJYDODUUEGKVOVTXEWQV
      QWRWSWTXAYCUUBYHUUQUOUUCEFYGYDXBVDXCYCUUAYLBJYCYJJHZRZYGYSYEYTOLPLZQZUUAY
      LUWBUVMUVNUVOYSSHYTSHUWDUUAUOYCUVMUWAUVRTYCUVNUWAUVSTYCUVOUWAUVTTUWBISYSW
      FUWBAYJIXSJUHXSJXDZIUHXFUWBXGXOXTYAYBUWAXHZYCUWAVLZXIWHUWBJSYTXJUWBAYJJXS
      JUIUWEJUIXFUWBXPXOUWFUWGXIWHYECDYSYTWMWNUWBUWCYKYGUWBUWCAYEPLZYJKLZYKXTYA
      UWAUWCUWIQYBAYJXKXLUWBYIUWHYJKYCYIUWHQZUWAXTYAUWJYBAXMUPTVPXNVMXQXRXC $.
  $}

  ${
    $d A a $.  $d N a $.
    $( The X and Y sequences define a solution to the corresponding Pell
       equation.  (Contributed by Stefan O'Rear, 22-Sep-2014.) $)
    rmxynorm $p |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. ZZ ) -> ( ( ( A rmX N ) ^ 2 )
        - ( ( ( A ^ 2 ) - 1 ) x. ( ( A rmY N ) ^ 2 ) ) ) = 1 ) $=
      ( va c2 cuz wcel cz wa crmx co cexp cmin crmy wceq eqidd oveq2 eqeq2d cn0
      c1 fovcl cfv cmul cv wrex simpr anim12i anbi12d rspcev syl2anc simpl frmx
      wb frmy rmxycomplete syl3anc mpbird ) ADEUAZFZBGFZHZABIJZDKJADKJSLJABMJZD
      KJUBJLJSNZVAACUCZIJZNZVBAVDMJZNZHZCGUDZUTUSVAVANZVBVBNZHZVJURUSUEURVKUSVL
      URVAOUSVBOUFVIVMCBGVDBNZVFVKVHVLVNVEVAVAVDBAIPQVNVGVBVBVDBAMPQUGUHUIUTURV
      ARFVBGFVCVJULURUSUJABRUQGIUKTABGUQGMUMTACVAVBUNUOUP $.
  $}

  $( The base of exponentiation for the X and Y sequences is a positive real.
     (Contributed by Stefan O'Rear, 22-Sep-2014.) $)
  rmbaserp $p |- ( A e. ( ZZ>= ` 2 ) -> ( A + ( sqrt ` ( ( A ^ 2 ) - 1 ) ) ) e.
      RR+ ) $=
    ( c2 cuz cfv wcel cexp co c1 cpellfund csqrt caddc crp rmspecfund csquarenn
    cmin cn cdif rmspecnonsq pellfundrp syl eqeltrrd ) ABCDEZABFGHOGZIDZAUCJDKG
    LAMUBUCPNQEUDLEARUCSTUA $.

  $( Negation law for X and Y sequences.  JonesMatijasevic is inconsistent on
     whether the X and Y sequences have domain ` NN0 ` or ` ZZ ` ; we use
     ` ZZ ` consistently to avoid the need for a separate subtraction law.
     (Contributed by Stefan O'Rear, 22-Sep-2014.) $)
  rmxyneg $p |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. ZZ ) -> ( ( A rmX -u N ) = ( A
      rmX N ) /\ ( A rmY -u N ) = -u ( A rmY N ) ) ) $=
    ( c2 wcel cz crmx co cexp c1 cmin crmy cmul caddc wceq oveq2d cc adantr cn0
    fovcl cq cuz cfv wa cneg csqrt znegcl rmxyval sylan2 rmbaserp rpcnd cc0 wne
    cdiv rpne0d simpr expclzd eqeltrd frmx nn0cnd csquarenn rmspecnonsq eldifad
    cn nncnd sqrtcld frmy negcld mulcld addcld expne0d eqnetrd mulneg2d negsubd
    eqtrd subsq syl2anc sqmuld sqsqrtd oveq1d rmxynorm 3eqtr2d mvllmuld expnegd
    zcnd 3eqtr4rd cdif rmspecsqrtnq nn0ssq sselid qnegcl syl qirropth syl122anc
    wb zssq mpbid ) ACUAUBZDZBEDZUCZABUDZFGZACHGIJGZUEUBZAXAKGZLGMGZABFGZXDABKG
    ZUDZLGZMGZNZXBXGNXEXINUCZWTXFAXDMGZXAHGZXKWSWRXAEDZXFXONBUFZAXAUGUHWTIXGXDX
    HLGZMGZUMGIXNBHGZUMGXKXOWTXSXTIUMABUGZOWTXSXKIWTXSXTPYAWTXNBWRXNPDWSWRXNAUI
    ZUJQZWRXNUKULWSWRXNYBUNQZWRWSUOZUPUQWTXGXJWTXGABRWQEFURSZUSZWTXDXIWTXCWRXCP
    DWSWRXCWRXCVCUTAVAVBVDQZVEZWTXHWTXHABEWQEKVFSZWDZVGVHVIWTXSXTUKYAWTXNBYCYDY
    EVJVKWTXSXKLGXSXGXRJGZLGZXGCHGZXRCHGZJGZIWTXKYLXSLWTXKXGXRUDZMGYLWTXJYQXGMW
    TXDXHYIYKVLOWTXGXRYGWTXDXHYIYKVHZVMVNOWTXGPDXRPDYPYMNYGYRXGXRVOVPWTYPYNXCXH
    CHGZLGZJGIWTYOYTYNJWTYOXDCHGZYSLGYTWTXDXHYIYKVQWTUUAXCYSLWTXCYHVRVSVNOABVTV
    NWAWBWTXNBYCYDYEWCWEVNWTXDPTWFDZXBTDXETDXGTDXITDZXLXMWNWRUUBWSAWGQWTRTXBWHW
    SWRXPXBRDXQAXARWQEFURSUHWIWTETXEWOWSWRXPXEEDXQAXAEWQEKVFSUHWIWTRTXGWHYFWIWT
    XHTDUUCWTETXHWOYJWIXHWJWKXDXBXEXGXIWLWMWP $.

  $( Addition formula for X and Y sequences.  See ~ rmxadd and ~ rmyadd for
     most uses.  (Contributed by Stefan O'Rear, 22-Sep-2014.) $)
  rmxyadd $p |- ( ( A e. ( ZZ>= ` 2 ) /\ M e. ZZ /\ N e. ZZ ) -> (
        ( A rmX ( M + N ) ) = ( ( ( A rmX M ) x. ( A rmX N ) ) + ( ( ( A ^ 2 )
      - 1 ) x. ( ( A rmY M ) x. ( A rmY N ) ) ) ) /\
        ( A rmY ( M + N ) ) = ( ( ( A rmY M ) x. ( A rmX N ) ) + ( ( A rmX M )
      x. ( A rmY N ) ) ) ) ) $=
    ( wcel cz caddc co crmx cexp crmy cmul wceq syl2anc zssq cn0 fovcdmd sselid
    c1 cq qmulcl c2 cuz cfv w3a cmin csqrt simp1 zaddcl 3adant1 rmxyval cc0 wne
    wa cc eluzelz 3ad2ant1 zcnd zq qsqcl 3syl sselii a1i qsubcl qcn syl sqrtcld
    1z addcld rmbaserp rpne0d simp2 simp3 expaddz syl22anc cxp frmx nn0cnd frmy
    wf mulcld muladdd oveq12d eqtr3d mul4d msqsqrtd mulcomd eqtrd oveq2d mul12d
    adddid addcomd oveq1d 3eqtr2d rmspecsqrtnq nn0ssq qaddcl qirropth syl122anc
    cdif wb mpbid ) AUAUBUCZDZBEDZCEDZUDZABCFGZHGZAUAIGZRUEGZUFUCZAXGJGZKGFGZAB
    HGZACHGZKGZXJABJGZACJGZKGZKGZFGZXKXQXOKGZXNXRKGZFGZKGZFGZLZXHYALXLYDLUMZXFX
    MAXKFGZXGIGZYFXFXCXGEDZXMYJLXCXDXEUGZXDXEYKXCBCUHUIZAXGUJMXFYJYIBIGZYICIGZK
    GZXPXKXRKGZXKXQKGZKGZFGZXNYQKGZXOYRKGZFGZFGZYFXFYIUNDYIUKULZXDXEYJYPLXFAXKX
    FAXCXDAEDZXEUAAUOUPZUQXFXJXFXJSDZXJUNDXFXISDZRSDZUUHXFUUFASDUUIUUGAURAUSUTU
    UJXFESRNVGVAVBXIRVCMZXJVDVEZVFZVHXCXDUUEXEXCYIAVIVJUPXCXDXEVKZXCXDXEVLZYIBC
    VMVNXFXNYRFGZXOYQFGZKGUUDYPXFXNYRXOYQXFXNXFABOXBEHXBEVOZOHVSXFVPVBZYLUUNPZV
    QZXFXKXQUUMXFXQXFABEXBEJUUREJVSXFVRVBZYLUUNPZUQZVTXFXOXFACOXBEHUUSYLUUOPZVQ
    ZXFXKXRUUMXFXRXFACEXBEJUVBYLUUOPZUQZVTWAXFUUPYNUUQYOKXFXCXDUUPYNLYLUUNABUJM
    XFXCXEUUQYOLYLUUOACUJMWBWCXFYTYAUUCYEFXFYSXTXPFXFYSXKXKKGZXRXQKGZKGXTXFXKXR
    XKXQUUMUVHUUMUVDWDXFUVIXJUVJXSKXFXJUULWEXFXRXQUVHUVDWFWBWGWHXFUUCXKYCKGZXKX
    OXQKGZKGZFGXKYCUVLFGZKGYEXFUUAUVKUUBUVMFXFXNXKXRUVAUUMUVHWIXFXOXKXQUVFUUMUV
    DWIWBXFXKYCUVLUUMXFXNXRUVAUVHVTZXFXOXQUVFUVDVTZWJXFUVNYDXKKXFUVNUVLYCFGYDXF
    YCUVLUVOUVPWKXFUVLYBYCFXFXOXQUVFUVDWFWLWGWHWMWBWMWGXFXKUNSWSDZXHSDXLSDYASDZ
    YDSDZYGYHWTXCXDUVQXEAWNUPXFOSXHWOXFAXGOXBEHUUSYLYMPQXFESXLNXFAXGEXBEJUVBYLY
    MPQXFXPSDZXTSDZUVRXFXNSDZXOSDZUVTXFOSXNWOUUTQZXFOSXOWOUVEQZXNXOTMXFUUHXSSDZ
    UWAUUKXFXQSDZXRSDZUWFXFESXQNUVCQZXFESXRNUVGQZXQXRTMXJXSTMXPXTWPMXFYBSDZYCSD
    ZUVSXFUWGUWCUWKUWIUWEXQXOTMXFUWBUWHUWLUWDUWJXNXRTMYBYCWPMXKXHXLYAYDWQWRXA
    $.

  $( Value of the X and Y sequences at 1.  (Contributed by Stefan O'Rear,
     22-Sep-2014.) $)
  rmxy1 $p |- ( A e. ( ZZ>= ` 2 )
      -> ( ( A rmX 1 ) = A /\ ( A rmY 1 ) = 1 ) ) $=
    ( c2 cfv wcel c1 crmx co cexp crmy cmul caddc wceq cz 1z mpan2 rpcnd cq cn0
    fovcl sselid cmin csqrt wa rmxyval rmbaserp exp1d rmspecpos sqrtcld mulridd
    cuz eqcomd oveq2d 3eqtrd cc cdif rmspecsqrtnq nn0ssq frmx zssq frmy eluzelz
    wb zq syl sselii a1i qirropth syl122anc mpbid ) ABUJCZDZAEFGZABHGEUAGZUBCZA
    EIGZJGKGZAVNEJGZKGZLZVLALVOELUCZVKVPAVNKGZEHGZWAVRVKEMDZVPWBLNAEUDOVKWAVKWA
    AUEPUFVKVNVQAKVKVQVNVKVNVKVMVKVMAUGPUHUIUKULUMVKVNUNQUODVLQDVOQDAQDZEQDZVSV
    TVBAUPVKRQVLUQVKWCVLRDNAERVJMFURSOTVKMQVOUSVKWCVOMDNAEMVJMIUTSOTVKAMDWDBAVA
    AVCVDWEVKMQEUSNVEVFVNVLVOAEVGVHVI $.

  $( Value of the X and Y sequences at 0.  (Contributed by Stefan O'Rear,
     22-Sep-2014.) $)
  rmxy0 $p |- ( A e. ( ZZ>= ` 2 )
      -> ( ( A rmX 0 ) = 1 /\ ( A rmY 0 ) = 0 ) ) $=
    ( c2 cfv wcel cc0 crmx co cexp c1 crmy cmul caddc wceq cz 0z mpan2 rpcnd cq
    cn0 zssq cuz cmin csqrt wa rmxyval rmbaserp rmspecpos sqrtcld mul01d oveq2d
    exp0d 1p0e1 eqtr2di 3eqtrd cc cdif wb rmspecsqrtnq nn0ssq frmx fovcl sselid
    frmy 1z sselii a1i qirropth syl122anc mpbid ) ABUACZDZAEFGZABHGIUBGZUCCZAEJ
    GZKGLGZIVNEKGZLGZMZVLIMVOEMUDZVKVPAVNLGZEHGZIVRVKENDZVPWBMOAEUEPVKWAVKWAAUF
    QUKVKVRIELGIVKVQEILVKVNVKVMVKVMAUGQUHUIUJULUMUNVKVNUORUPDVLRDVORDIRDZERDZVS
    VTUQAURVKSRVLUSVKWCVLSDOAESVJNFUTVAPVBVKNRVOTVKWCVONDOAENVJNJVCVAPVBWDVKNRI
    TVDVEVFWEVKNRETOVEVFVNVLVOIEVGVHVI $.

  $( Negation law (even function) for the X sequence.  The method of proof used
     for the previous four theorems ~ rmxyneg , ~ rmxyadd , ~ rmxy0 , and
     ~ rmxy1 via ~ qirropth results in two theorems at once, but typical use
     requires only one, so this group of theorems serves to separate the cases.
     (Contributed by Stefan O'Rear, 22-Sep-2014.) $)
  rmxneg $p |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. ZZ ) -> ( A rmX -u N ) = ( A rmX N
      ) ) $=
    ( c2 cuz cfv wcel cz wa cneg crmx co wceq crmy rmxyneg simpld ) ACDEFBGFHAB
    IZJKABJKLAPMKABMKILABNO $.

  $( Value of X sequence at 0.  Part 1 of equation 2.11 of [JonesMatijasevic]
     p. 695.  (Contributed by Stefan O'Rear, 22-Sep-2014.) $)
  rmx0 $p |- ( A e. ( ZZ>= ` 2 ) -> ( A rmX 0 ) = 1 ) $=
    ( c2 cuz cfv wcel cc0 crmx co c1 wceq crmy rmxy0 simpld ) ABCDEAFGHIJAFKHFJ
    ALM $.

  $( Value of X sequence at 1.  Part 2 of equation 2.11 of [JonesMatijasevic]
     p. 695.  (Contributed by Stefan O'Rear, 22-Sep-2014.) $)
  rmx1 $p |- ( A e. ( ZZ>= ` 2 ) -> ( A rmX 1 ) = A ) $=
    ( c2 cuz cfv wcel c1 crmx co wceq crmy rmxy1 simpld ) ABCDEAFGHAIAFJHFIAKL
    $.

  $( Addition formula for X sequence.  Equation 2.7 of [JonesMatijasevic]
     p. 695.  (Contributed by Stefan O'Rear, 22-Sep-2014.) $)
  rmxadd $p |- ( ( A e. ( ZZ>= ` 2 ) /\ M e. ZZ /\ N e. ZZ ) ->
        ( A rmX ( M + N ) ) = ( ( ( A rmX M ) x. ( A rmX N ) ) + ( ( ( A ^ 2 )
      - 1 ) x. ( ( A rmY M ) x. ( A rmY N ) ) ) ) ) $=
    ( c2 cuz cfv wcel cz w3a caddc crmx cmul cexp cmin crmy wceq rmxyadd simpld
    co c1 ) ADEFGBHGCHGIABCJSZKSABKSZACKSZLSADMSTNSABOSZACOSZLSLSJSPAUAOSUDUCLS
    UBUELSJSPABCQR $.

  $( Negation formula for Y sequence (odd function).  (Contributed by Stefan
     O'Rear, 22-Sep-2014.) $)
  rmyneg $p |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. ZZ ) -> ( A rmY -u N ) = -u ( A
      rmY N ) ) $=
    ( c2 cuz cfv wcel cz wa cneg crmx co wceq crmy rmxyneg simprd ) ACDEFBGFHAB
    IZJKABJKLAPMKABMKILABNO $.

  $( Value of Y sequence at 0.  Part 1 of equation 2.12 of [JonesMatijasevic]
     p. 695.  (Contributed by Stefan O'Rear, 22-Sep-2014.) $)
  rmy0 $p |- ( A e. ( ZZ>= ` 2 ) -> ( A rmY 0 ) = 0 ) $=
    ( c2 cuz cfv wcel cc0 crmx co c1 wceq crmy rmxy0 simprd ) ABCDEAFGHIJAFKHFJ
    ALM $.

  $( Value of Y sequence at 1.  Part 2 of equation 2.12 of [JonesMatijasevic]
     p. 695.  (Contributed by Stefan O'Rear, 22-Sep-2014.) $)
  rmy1 $p |- ( A e. ( ZZ>= ` 2 ) -> ( A rmY 1 ) = 1 ) $=
    ( c2 cuz cfv wcel c1 crmx co wceq crmy rmxy1 simprd ) ABCDEAFGHAIAFJHFIAKL
    $.

  $( Addition formula for Y sequence.  Equation 2.8 of [JonesMatijasevic]
     p. 695.  (Contributed by Stefan O'Rear, 22-Sep-2014.) $)
  rmyadd $p |- ( ( A e. ( ZZ>= ` 2 ) /\ M e. ZZ /\ N e. ZZ ) ->
        ( A rmY ( M + N ) ) = ( ( ( A rmY M ) x. ( A rmX N ) ) + ( ( A rmX M )
      x. ( A rmY N ) ) ) ) $=
    ( c2 cuz cfv wcel cz w3a caddc crmx cmul cexp cmin crmy wceq rmxyadd simprd
    co c1 ) ADEFGBHGCHGIABCJSZKSABKSZACKSZLSADMSTNSABOSZACOSZLSLSJSPAUAOSUDUCLS
    UBUELSJSPABCQR $.

  $( Special addition-of-1 formula for X sequence.  Part 1 of equation 2.9 of
     [JonesMatijasevic] p. 695.  (Contributed by Stefan O'Rear,
     19-Oct-2014.) $)
  rmxp1 $p |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. ZZ ) ->
        ( A rmX ( N + 1 ) ) = ( ( ( A rmX N ) x. A ) + ( ( ( A ^ 2 ) - 1 ) x. (
      A rmY N ) ) ) ) $=
    ( c2 cuz wcel cz wa c1 caddc co crmx cmul cexp cmin crmy wceq adantr oveq2d
    cfv eqtrd 1z rmxadd mp3an3 rmx1 rmy1 frmy fovcl zcnd mulridd oveq12d ) ACDS
    ZEZBFEZGZABHIJKJZABKJZAHKJZLJZACMJHNJZABOJZAHOJZLJZLJZIJZUPALJZUSUTLJZIJULU
    MHFEUOVDPUAABHUBUCUNURVEVCVFIUNUQAUPLULUQAPUMAUDQRUNVBUTUSLUNVBUTHLJZUTULVB
    VGPUMULVAHUTLAUERQUNUTUNUTABFUKFOUFUGUHUITRUJT $.

  $( Special addition of 1 formula for Y sequence.  Part 2 of equation 2.9 of
     [JonesMatijasevic] p. 695.  (Contributed by Stefan O'Rear,
     24-Sep-2014.) $)
  rmyp1 $p |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. ZZ ) ->
        ( A rmY ( N + 1 ) ) = ( ( ( A rmY N ) x. A ) + ( A rmX N ) ) ) $=
    ( c2 cuz wcel cz wa c1 caddc co crmy crmx cmul wceq 1z rmyadd oveq2d adantr
    cfv eqtrd mp3an3 rmx1 rmy1 cn0 frmx fovcl nn0cnd mulridd oveq12d ) ACDSZEZB
    FEZGZABHIJKJZABKJZAHLJZMJZABLJZAHKJZMJZIJZUOAMJZURIJUKULHFEUNVANOABHPUAUMUQ
    VBUTURIUKUQVBNULUKUPAUOMAUBQRUMUTURHMJZURUKUTVCNULUKUSHURMAUCQRUMURUMURABUD
    UJFLUEUFUGUHTUIT $.

  $( Subtraction of 1 formula for X sequence.  Part 1 of equation 2.10 of
     [JonesMatijasevic] p. 695.  (Contributed by Stefan O'Rear,
     14-Oct-2014.) $)
  rmxm1 $p |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. ZZ ) ->
        ( A rmX ( N - 1 ) ) = ( ( A x. ( A rmX N ) ) -
        ( ( ( A ^ 2 ) - 1 ) x. ( A rmY N ) ) ) ) $=
    ( c2 wcel cz c1 cneg caddc co crmx cmul cmin crmy mpan2 eqtrd adantr oveq2d
    wceq 1z cc cuz cfv wa cexp neg1z rmxadd mp3an3 rmxneg rmx1 cn0 fovcl nn0cnd
    frmx mulcomd rmyneg rmy1 negeqd frmy zcnd ax-1cn mulneg2 sylancl mulridd cn
    eluzelcn csquarenn rmspecnonsq eldifad nncnd mulneg2d oveq12d adantl negsub
    zcn mulcld negsubd 3eqtr3d ) ACUAUBZDZBEDZUCZABFGZHIZJIZAABJIZKIZACUDIFLIZA
    BMIZKIZGZHIZABFLIZJIWFWILIWAWDWEAWBJIZKIZWGWHAWBMIZKIZKIZHIZWKVSVTWBEDWDWRR
    UEABWBUFUGWAWNWFWQWJHWAWNWEAKIWFWAWMAWEKVSWMARVTVSWMAFJIZAVSFEDZWMWSRSAFUHN
    AUIOPQWAWEAWAWEABUJVREJUMUKULZVSATDVTCAVEPZUNOWAWQWGWHGZKIWJWAWPXCWGKWAWPWH
    WBKIZXCVSWPXDRVTVSWOWBWHKVSWOAFMIZGZWBVSWTWOXFRSAFUONVSXEFAUPUQOQPWAXDWHFKI
    ZGZXCWAWHTDFTDZXDXHRWAWHABEVREMURUKUSZUTWHFVAVBWAXGWHWAWHXJVCUQOOQWAWGWHVSW
    GTDVTVSWGVSWGVDVFAVGVHVIPZXJVJOVKOWAWCWLAJWABTDZXIWCWLRVTXLVSBVNVLUTBFVMVBQ
    WAWFWIWAAWEXBXAVOWAWGWHXKXJVOVPVQ $.

  $( Subtraction of 1 formula for Y sequence.  Part 2 of equation 2.10 of
     [JonesMatijasevic] p. 695.  (Contributed by Stefan O'Rear,
     19-Oct-2014.) $)
  rmym1 $p |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. ZZ ) ->
        ( A rmY ( N - 1 ) ) = ( ( ( A rmY N ) x. A ) - ( A rmX N ) ) ) $=
    ( c2 wcel cz c1 cmin co crmy cneg caddc crmx cmul cc wceq sylancl oveq2d 1z
    eqtrd adantr cuz cfv wa zcn adantl ax-1cn negsub eqcomd neg1z rmyadd mp3an3
    rmxneg mpan2 rmx1 rmyneg rmy1 negeqd frmx fovcl nn0cnd neg1cn mulcom mulm1d
    cn0 3eqtrd oveq12d frmy zcnd eluzelcn mulcld negsubd ) ACUAUBZDZBEDZUCZABFG
    HZIHABFJZKHZIHZABIHZAVQLHZMHZABLHZAVQIHZMHZKHZVTAMHZWCGHZVOVPVRAIVOVRVPVOBN
    DZFNDVRVPOVNWIVMBUDUEUFBFUGPUHQVMVNVQEDVSWFOUIABVQUJUKVOWFWGWCJZKHWHVOWBWGW
    EWJKVOWAAVTMVMWAAOVNVMWAAFLHZAVMFEDZWAWKORAFULUMAUNSTQVOWEWCVQMHZVQWCMHZWJV
    OWDVQWCMVMWDVQOVNVMWDAFIHZJZVQVMWLWDWPORAFUOUMVMWOFAUPUQSTQVOWCNDVQNDWMWNOV
    OWCABVDVLELURUSUTZVAWCVQVBPVOWCWQVCVEVFVOWGWCVOVTAVOVTABEVLEIVGUSVHVMANDVNC
    AVITVJWQVKSVE $.

  $( The X sequence is a Lucas (second-order integer recurrence) sequence.
     Part 3 of equation 2.11 of [JonesMatijasevic] p. 695.  (Contributed by
     Stefan O'Rear, 14-Oct-2014.) $)
  rmxluc $p |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. ZZ ) -> ( A rmX ( N + 1 ) ) =
      ( ( ( 2 x. A ) x. ( A rmX N ) ) - ( A rmX ( N - 1 ) ) ) ) $=
    ( c2 wcel cz wa cmul co crmx c1 cmin caddc wceq crmy cn0 frmx nn0cnd mulcld
    cc fovcl cuz cfv cexp peano2zm peano2z addcomd rmxp1 rmxm1 oveq12d eluzelcn
    sylan2 adantr csquarenn rmspecnonsq eldifad nncnd frmy zcnd ppncand mulcomd
    oveq1d 2cnd mulassd 2timesd eqtr2d 3eqtrd 2cn sylancr subaddd mpbird eqcomd
    cn mulcl ) ACUAUBZDZBEDZFZCAGHZABIHZGHZABJKHZIHZKHZABJLHZIHZVQWCWEMWBWELHZV
    TMVQWFWEWBLHVSAGHZACUCHJKHZABNHZGHZLHZAVSGHZWJKHZLHZVTVQWBWEVPVOWAEDZWBSDBU
    DVOWOFWBAWAOVNEIPTQUKZVPVOWDEDZWESDBUEVOWQFWEAWDOVNEIPTQUKZUFVQWEWKWBWMLABU
    GABUHUIVQWNWGWLLHWLWLLHZVTVQWGWJWLVQVSAVQVSABOVNEIPTQZVOASDZVPCAUJULZRVQWHW
    IVOWHSDVPVOWHVOWHVLUMAUNUOUPULVQWIABEVNENUQTURRVQAVSXBWTRZUSVQWGWLWLLVQVSAW
    TXBUTVAVQVTCWLGHWSVQCAVSVQVBXBWTVCVQWLXCVDVEVFVFVQVTWBWEVQVRVSVQCSDXAVRSDVG
    XBCAVMVHWTRWPWRVIVJVK $.

  $( The Y sequence is a Lucas sequence, definable via this second-order
     recurrence with ~ rmy0 and ~ rmy1 .  Part 3 of equation 2.12 of
     [JonesMatijasevic] p. 695.  JonesMatijasevic uses this theorem to redefine
     the X and Y sequences to have domain ` ( ZZ X. ZZ ) ` , which simplifies
     some later theorems.  It may shorten the derivation to use this as our
     initial definition.  Incidentally, the X sequence satisfies the exact same
     recurrence.  (Contributed by Stefan O'Rear, 1-Oct-2014.) $)
  rmyluc $p |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. ZZ ) -> ( A rmY ( N + 1 ) ) = ( (
      2 x. ( ( A rmY N ) x. A ) ) - ( A rmY ( N - 1 ) ) ) ) $=
    ( c2 cuz cfv wcel cz wa c1 caddc crmy cmul cmin frmy fovcl sylan2 zcnd crmx
    co cc peano2z 2cn eluzelcn adantr mulcld mulcl sylancr peano2zm rmyp1 rmym1
    subcld oveq12d frmx nn0cnd ppncand npcand 2timesd eqtr2d 3eqtrd addcan2ad
    cn0 ) ACDEZFZBGFZHZABIJSZKSZCABKSZALSZLSZABIMSZKSZMSZVLVEVGVDVCVFGFVGGFBUAA
    VFGVBGKNOPQVEVJVLVECTFVITFVJTFUBVEVHAVEVHABGVBGKNOQVCATFVDCAUCUDUEZCVIUFUGZ
    VEVLVDVCVKGFVLGFBUHAVKGVBGKNOPQZUKVPVEVGVLJSVIABRSZJSZVIVQMSZJSVIVIJSZVMVLJ
    SZVEVGVRVLVSJABUIABUJULVEVIVQVIVNVEVQABVAVBGRUMOUNVNUOVEWAVJVTVEVJVLVOVPUPV
    EVIVNUQURUSUT $.

  $( Lucas sequence property of Y with better output ordering.  (Contributed by
     Stefan O'Rear, 16-Oct-2014.) $)
  rmyluc2 $p |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. ZZ ) -> ( A rmY ( N + 1 ) ) =
        ( ( ( 2 x. A ) x. ( A rmY N ) ) - ( A rmY ( N - 1 ) ) ) ) $=
    ( c2 cuz cfv wcel cz wa c1 caddc co crmy cmul cmin frmy fovcl zcnd eluzelcn
    rmyluc cc adantr mulcomd oveq2d 2cnd mulassd eqtr4d oveq1d eqtrd ) ACDEZFZB
    GFZHZABIJKLKCABLKZAMKZMKZABINKLKZNKCAMKUMMKZUPNKABSULUOUQUPNULUOCAUMMKZMKUQ
    ULUNURCMULUMAULUMABGUIGLOPQZUJATFUKCARUAZUBUCULCAUMULUDUTUSUEUFUGUH $.

  $( "Double-angle formula" for X-values.  Equation 2.13 of [JonesMatijasevic]
     p. 695.  (Contributed by Stefan O'Rear, 2-Oct-2014.) $)
  rmxdbl $p |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. ZZ ) -> ( A rmX ( 2 x. N ) ) = ( (
      2 x. ( ( A rmX N ) ^ 2 ) ) - 1 ) ) $=
    ( c2 wcel cz cmul co crmx caddc cexp c1 cmin crmy cc 2timesd oveq2d oveq12d
    fovcl sqcld sqvald cuz cfv wa zcn adantl wceq rmxadd 3anidm23 cn0 nn0cnd cn
    frmx csquarenn rmspecnonsq eldifad adantr frmy zcnd mulcld pnncand rmxynorm
    nncnd eqcomd 3eqtr3rd 3eqtrd ) ACUAUBZDZBEDZUCZACBFGZHGABBIGZHGZABHGZVMFGZA
    CJGKLGZABMGZVPFGZFGZIGZCVMCJGZFGZKLGZVIVJVKAHVIBVHBNDVGBUDUEOPVGVHVLVSUFABB
    UGUHVIVTVTIGZVTVOVPCJGZFGZLGZLGVTWEIGWBVSVIVTVTWEVIVMVIVMABUIVFEHULRUJZSZWH
    VIVOWDVGVONDVHVGVOVGVOUKUMAUNUOVBUPVIVPVIVPABEVFEMUQRURZSUSUTVIWCWAWFKLVIWA
    WCVIVTWHOVCABVAQVIVTVNWEVRIVIVMWGTVIWDVQVOFVIVPWITPQVDVE $.

  $( "Double-angle formula" for Y-values.  Equation 2.14 of [JonesMatijasevic]
     p. 695.  (Contributed by Stefan O'Rear, 2-Oct-2014.) $)
  rmydbl $p |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. ZZ ) -> ( A rmY ( 2 x. N ) ) = ( (
      2 x. ( A rmX N ) ) x. ( A rmY N ) ) ) $=
    ( c2 cuz cfv wcel cz wa cmul crmy caddc crmx zcn adantl 2timesd oveq2d wceq
    co cc fovcl rmyadd 3anidm23 2cnd cn0 frmx nn0cnd frmy mulassd mulcld oveq1d
    zcnd mulcomd 3eqtrrd 3eqtrd ) ACDEZFZBGFZHZACBIRZJRABBKRZJRZABJRZABLRZIRZVC
    VBIRZKRZCVCIRVBIRZURUSUTAJURBUQBSFUPBMNOPUPUQVAVFQABBUAUBURVGCVEIRVEVEKRVFU
    RCVCVBURUCURVCABUDUOGLUETUFZURVBABGUOGJUGTUKZUHURVEURVCVBVHVIUIOURVEVDVEKUR
    VCVBVHVIULUJUMUN $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Ordering and induction lemmas for the integers
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d A a b x y $.  $d B a b x y $.  $d C a b c d y $.  $d D a x y $.
    $d E a x y $.  $d F b x $.  $d G b x $.  $d H a b c d x y $.
    $d ph a b c d x y $.
    monotuz.1 $e |- ( ( ph /\ y e. H ) -> F < G ) $.
    monotuz.2 $e |- ( ( ph /\ x e. H ) -> C e. RR ) $.
    monotuz.3 $e |- H = ( ZZ>= ` I ) $.
    monotuz.4 $e |- ( x = ( y + 1 ) -> C = G ) $.
    monotuz.5 $e |- ( x = y -> C = F ) $.
    monotuz.6 $e |- ( x = A -> C = D ) $.
    monotuz.7 $e |- ( x = B -> C = E ) $.
    $( A function defined on an upper set of integers which increases at every
       adjacent pair is globally strictly monotonic by induction.  (Contributed
       by Stefan O'Rear, 24-Sep-2014.) $)
    monotuz $p |- ( ( ph /\ ( A e. H /\ B e. H ) ) -> ( A < B <-> D < E ) ) $=
      ( wcel va vb vc vd wa clt wbr csb cv csbeq1 cuz cr cz uzssz zssre eqsstri
      cfv sstri nfv nfcsb1v nfel1 nfim weq eleq1 anbi2d csbeq1a imbi12d chvarfv
      wi eleq1d simpl adantlrr simplrl sselid simplrr simpr caddc breq2d imbi2d
      c1 co wceq vex csbie eqtr3id ovex oveq1 csbeq1d breq12d vtoclg w3a simp2l
      3ad2ant2 cle zre 3ad2ant1 simp3 ltled wb simp11 simp12 eluz mpbird simp2r
      syl2anc eleqtrdi uztrn eleqtrrdi peano2uz syl vtoclf lttrd uzind2 syl3anc
      3exp a2d mpd ex ltord1 nfcvd csbiegf breqan12d adantl bitrd ) ADKTZEKTZUE
      ZUEDEUFUGBDFUHZBEFUHZUFUGZGHUFUGZAUAUBBUAUIZFUHZBUBUIZFUHZDEKYHYIBYLYNFUJ
      BYLDFUJBYLEFUJKLUKUQZULOYPUMULLUNZUOURUPABUIZKTZUEZFULTZVIZAYLKTZUEZYMULT
      ZVIBUAUUDUUEBUUDBUSBYMULBYLFUTVAVBBUAVCZYTUUDUUAUUEUUFYSUUCAYRYLKVDVEUUFF
      YMULBYLFVFVJVGNVHZAUUCYNKTZUEUEZYLYNUFUGZYMYOUFUGZUUIUUJUEZUUDUUKAUUCUUJU
      UDUUHUUDUUJVKVLUULYLUMTZYNUMTUUJUUDUUKVIZUULKUMYLKYPUMOYQUPZAUUCUUHUUJVMV
      NUULKUMYNUUOAUUCUUHUUJVOVNUUIUUJVPUUDYMBUCUIZFUHZUFUGZVIUUDYMBYLVTVQWAZFU
      HZUFUGZVIZUUDYMBUDUIZFUHZUFUGZVIUUDYMBUVCVTVQWAZFUHZUFUGZVIUUNUCUDYLYNUUP
      UUSWBZUURUVAUUDUVIUUQUUTYMUFBUUPUUSFUJVRVSUCUDVCZUURUVEUUDUVJUUQUVDYMUFBU
      UPUVCFUJVRVSUUPUVFWBZUURUVHUUDUVKUUQUVGYMUFBUUPUVFFUJVRVSUCUBVCZUURUUKUUD
      UVLUUQYOYMUFBUUPYNFUJVRVSACUIZKTZUEZIJUFUGZVIZUVBCYLUMCUAVCZUVOUUDUVPUVAU
      VRUVNUUCAUVMYLKVDVEUVRIYMJUUTUFUVRIBUVMFUHZYMBUVMFICWCQWDZBUVMYLFUJWEUVRJ
      BUVMVTVQWAZFUHZUUTBUWAFJUVMVTVQWFPWDZUVRBUWAUUSFUVMYLVTVQWGWHWEWIVGMWJUUM
      UVCUMTZYLUVCUFUGZWKZUUDUVEUVHUWFUUDUVEUVHUWFUUDUVEWKZYMUVDUVGUUDUWFUUEUVE
      UUGWMUWGAUVCKTZUVDULTZUWFAUUCUVEWLZUWGUVCYPKUWGUVCYLUKUQTZYLYPTUVCYPTZUWG
      UWKYLUVCWNUGZUWFUUDUWMUVEUWFYLUVCUUMUWDYLULTUWEYLWOWPUWDUUMUVCULTUWEUVCWO
      WMUUMUWDUWEWQWRWPUWGUUMUWDUWKUWMWSUUMUWDUWEUUDUVEWTUUMUWDUWEUUDUVEXAYLUVC
      XBXEXCUWGYLKYPUWFAUUCUVEXDOXFYLUVCLXGXEZOXHZUUBAUWHUEZUWIVIBUDUWPUWIBUWPB
      USBUVDULBUVCFUTVAVBBUDVCZYTUWPUUAUWIUWQYSUWHAYRUVCKVDVEUWQFUVDULBUVCFVFVJ
      VGNVHXEUWGAUVFKTZUVGULTZUWJUWGUVFYPKUWGUWLUVFYPTUWNLUVCXIXJOXHUUBAUWRUEZU
      WSVIBUVFUWTUWSBUWTBUSBUVGULBUVFFUTVAVBUVCVTVQWFYRUVFWBZYTUWTUUAUWSUXAYSUW
      RAYRUVFKVDVEUXAFUVGULBUVFFVFVJVGNXKXEUWFUUDUVEWQUWGAUWHUVDUVGUFUGZUWJUWOU
      VQUWPUXBVIZCUDUXCCUSCUDVCZUVOUWPUVPUXBUXDUVNUWHAUVMUVCKVDVEUXDIUVDJUVGUFU
      XDIUVSUVDUVTBUVMUVCFUJWEUXDJUWBUVGUWCUXDBUWAUVFFUVMUVCVTVQWGWHWEWIVGMVHXE
      XLXOXPXMXNXQXRXSYGYJYKWSAYEYFYHGYIHUFBDFGKYEBGXTRYABEFHKYFBHXTSYAYBYCYD
      $.
  $}

  ${
    $d ph a b x y $.  $d A a b x y $.  $d B a b x y $.  $d F a b x y $.
    monotoddzzfi.1 $e |- ( ( ph /\ x e. ZZ ) -> ( F ` x ) e. RR ) $.
    monotoddzzfi.2 $e |- ( ( ph /\ x e. ZZ ) -> ( F ` -u x ) = -u ( F ` x ) )
        $.
    monotoddzzfi.3 $e |- ( ( ph /\ x e. NN0 /\ y e. NN0 ) -> ( x < y -> ( F ` x
        ) < ( F ` y ) ) ) $.
    $( A function which is odd and monotonic on ` NN0 ` is monotonic on
       ` ZZ ` .  This proof is far too long.  (Contributed by Stefan O'Rear,
       25-Sep-2014.) $)
    monotoddzzfi $p |- ( ( ph /\ A e. ZZ /\ B e. ZZ ) -> ( A < B <-> ( F ` A )
        < ( F ` B ) ) ) $=
      ( cz wcel clt wbr wa wi eleq1d imbi12d cn0 cc0 cle va vb cfv wb fveq2 weq
      cv zssre cr eleq1 anbi2d chvarvv cn cneg wo simprbi anim12i adantl simpll
      elznn nnnn0 ad2antrl ad2antll w3a vex simpl simpr breq12 breqan12d vtocl2
      3anbi23d syl3anc ex adantrr adantr 0red adantrl znegcl negex vtocl syldan
      wceq ad2antrr 0z c0ex mpan2 recnd neg0 fveq2i negeq fveq2d negeqd eqeq12d
      eqtr3id eqnegad nngt0 simplll 0nn0 a1i simplrl breq12d mpd eqbrtrrd ltled
      0le0 breqtrrid breq2d mpbird biimpi mpjaodan breqtrd le0neg1d lelttrd a1d
      elnn0 simp3 wn c1 ad2antlr 1red nnre nn0ge0 0le1 letrd nnge1 lenltd mpbid
      3adant3 pm2.21dd 3com23 3expb adantlr sylibd ltnegd 3imtr4d ccased ltord1
      zre 3exp 3impb ) ADJKEJKDELMDFUCZEFUCZLMUDAUAUBUAUGZFUCZUBUGZFUCZDEJUUAUU
      BUUCUUEFUEUUCDFUEUUCEFUEUHABUGZJKZNZUUGFUCZUIKZOZAUUCJKZNZUUDUIKZOBUABUAU
      FZUUIUUNUUKUUOUUPUUHUUMAUUGUUCJUJUKZUUPUUJUUDUIUUGUUCFUEZPQGULZAUUMUUEJKZ
      NZNZUUCUMKZUUCUNZRKZUOZUUEUMKZUUEUNZRKZUOZNZUUCUUELMZUUDUUFLMZOZUVAUVKAUU
      MUVFUUTUVJUUMUUCUIKZUVFUUCUTUPUUTUUEUIKZUVJUUEUTUPUQURUVBUVCUVGUVEUVIUVNU
      VBUVCUVGNZUVNUVBUVQNAUUCRKZUUERKZUVNAUVAUVQUSUVCUVRUVBUVGUUCVAVBUVGUVSUVB
      UVCUUEVAZVCAUUGRKZCUGZRKZVDZUUGUWBLMZUUJUWBFUCZLMZOZOZAUVRUVSVDZUVNOBCUUC
      UUEUAVEUBVEZUUPCUBUFZNZUWDUWJUWHUVNUWMUWAUVRUWCUVSAUWMUUGUUCRUUPUWLVFPUWM
      UWBUUERUUPUWLVGPVKUWMUWEUVLUWGUVMUUGUUCUWBUUELVHUUPUWLUUJUUDUWFUUFLUURUWB
      UUEFUEZVIQQIVJVLVMUVBUVEUVGNZUVNUVBUWONZUVMUVLUWPUUDSUUFUVBUUOUWOAUUMUUOU
      UTUUSVNZVOZUWPVPUVBUUFUIKZUWOAUUTUWSUUMUULAUUTNZUWSOBUBBUBUFZUUIUWTUUKUWS
      UXAUUHUUTAUUGUUEJUJUKZUXAUUJUUFUIUUGUUEFUEZPQGULVQZVOUWPUUDSTMSUUDUNZTMUW
      PSUVDFUCZUXETUWPUVDUMKZSUXFTMZUVDSWBZUWPUXGNZSUXFUXJVPUVBUXFUIKZUWOUXGAUV
      AUVDJKZUXKUUMUXLAUUTUUCVRVBUULAUXLNZUXKOBUVDUUCVSZUUGUVDWBZUUIUXMUUKUXKUX
      OUUHUXLAUUGUVDJUJUKUXOUUJUXFUIUUGUVDFUEPQGVTWAWCUXJSFUCZSUXFLUVBUXPSWBZUW
      OUXGAUXQUVAAUXPAUXPASJKZUXPUIKZWDUULAUXRNZUXSOBSWEUUGSWBZUUIUXTUUKUXSUYAU
      UHUXRAUUGSJUJUKZUYAUUJUXPUIUUGSFUEZPQGVTWFWGAUXPSUNZFUCZUXPUNZUYDSFWHWIAU
      XRUYEUYFWBZWDUUIUUGUNZFUCZUUJUNZWBZOZUXTUYGOBSWEUYAUUIUXTUYKUYGUYBUYAUYIU
      YEUYJUYFUYAUYHUYDFUUGSWJWKUYAUUJUXPUYCWLWMQHVTWFWNWOVOZWCUXJSUVDLMZUXPUXF
      LMZUXGUYNUWPUVDWPURUXJASRKZUVEUYNUYOOZAUVAUWOUXGWQUYPUXJWRWSUVBUVEUVGUXGW
      TUWIAUYPUVEVDZUYQOBCSUVDWEUXNUYAUWBUVDWBZNZUWDUYRUWHUYQUYTUWAUYPUWCUVEAUY
      TUUGSRUYAUYSVFZPUYTUWBUVDRUYAUYSVGZPVKUYTUWEUYNUWGUYOUUGSUWBUVDLVHUYTUUJU
      XPUWFUXFLUYTUUGSFVUAWKUYTUWBUVDFVUBWKXAQQIVJVLXBXCXDUWPUXINZUXHSUXPTMZVUC
      SSUXPTXEUVBUXQUWOUXIUYMWCXFUXIUXHVUDUDUWPUXIUXFUXPSTUVDSFUEXGURXHUVEUXGUX
      IUOZUVBUVGUVEVUEUVDXOXIVBXJUVBUXFUXEWBZUWOAUUMVUFUUTUYLUUNVUFOBUAUUPUUIUU
      NUYKVUFUUQUUPUYIUXFUYJUXEUUPUYHUVDFUUGUUCWJWKUUPUUJUUDUURWLWMQHULVNZVOXKU
      WPUUDUWRXLXHUWPUXPSUUFLUVBUXQUWOUYMVOUWPSUUELMZUXPUUFLMZUVGVUHUVBUVEUUEWP
      VCUWPAUYPUVSVUHVUIOZAUVAUWOUSUYPUWPWRWSUVGUVSUVBUVEUVTVCUWIAUYPUVSVDZVUJO
      BCSUUEWEUWKUYAUWLNZUWDVUKUWHVUJVULUWAUYPUWCUVSAVULUUGSRUYAUWLVFPVULUWBUUE
      RUYAUWLVGPVKVULUWEVUHUWGVUIUUGSUWBUUELVHUYAUWLUUJUXPUWFUUFLUYCUWNVIQQIVJV
      LXBXCXMXNVMUVBUVCUVINZUVLUVMUVBVUMUVLVDUVLUVMUVBVUMUVLXPUVBVUMUVLXQZUVLUV
      BVUMNZUUEUUCTMVUNVUOUUEXRUUCUVAUVPAVUMUUTUVPUUMUUEYRURZXSZVUOXTZUVCUVOUVB
      UVIUUCYAVBZVUOUUESXRVUQVUOVPVURVUOUUESTMSUVHTMZUVIVUTUVBUVCUVHYBVCVUOUUEV
      UQXLXHSXRTMVUOYCWSYDUVCXRUUCTMUVBUVIUUCYEVBYDVUOUUEUUCVUQVUSYFYGYHYIYSUVB
      UVEUVINZUVNUVBVVANZUVHUVDLMZUUFUNZUXELMZUVLUVMVVBVVCUVHFUCZUXFLMZVVEAVVAV
      VCVVGOZUVAAUVEUVIVVHAUVIUVEVVHUWIAUVIUVEVDZVVHOBCUVHUVDUUEVSUXNUUGUVHWBZU
      YSNZUWDVVIUWHVVHVVKUWAUVIUWCUVEAVVKUUGUVHRVVJUYSVFPVVKUWBUVDRVVJUYSVGPVKV
      VKUWEVVCUWGVVGUUGUVHUWBUVDLVHVVJUYSUUJVVFUWFUXFLUUGUVHFUEUWBUVDFUEVIQQIVJ
      YJYKYLVVBVVFVVDUXFUXELUVBVVFVVDWBZVVAAUUTVVLUUMUYLUWTVVLOBUBUXAUUIUWTUYKV
      VLUXBUXAUYIVVFUYJVVDUXAUYHUVHFUUGUUEWJWKUXAUUJUUFUXCWLWMQHULVQVOUVBVUFVVA
      VUGVOXAYMVVBUUCUUEUVBUVOVVAUUMUVOAUUTUUCYRVBVOUVAUVPAVVAVUPXSYNVVBUUDUUFU
      VBUUOVVAUWQVOUVBUWSVVAUXDVOYNYOVMYPXBYQYT $.
  $}

  ${
    $d ph a b x y $.  $d A a b x y $.  $d B a b x y $.  $d E a b y $.
    $d C a b x y $.  $d D a b x y $.  $d F a b x $.  $d G a b x $.
    monotoddzz.1 $e |- ( ( ph /\ x e. NN0 /\ y e. NN0 ) -> ( x < y -> E < F ) )
        $.
    monotoddzz.2 $e |- ( ( ph /\ x e. ZZ ) -> E e. RR ) $.
    monotoddzz.3 $e |- ( ( ph /\ y e. ZZ ) -> G = -u F ) $.
    monotoddzz.4 $e |- ( x = A -> E = C ) $.
    monotoddzz.5 $e |- ( x = B -> E = D ) $.
    monotoddzz.6 $e |- ( x = y -> E = F ) $.
    monotoddzz.7 $e |- ( x = -u y -> E = G ) $.
    $( A function (given implicitly) which is odd and monotonic on ` NN0 ` is
       monotonic on ` ZZ ` .  This proof is far too long.  (Contributed by
       Stefan O'Rear, 25-Sep-2014.) $)
    monotoddzz $p |- ( ( ph /\ A e. ZZ /\ B e. ZZ ) -> ( A < B <-> C < D ) ) $=
      ( cz clt cr va vb wcel w3a wbr cmpt cfv cv wa wi nffvmpt1 nfel1 nfim wceq
      nfv eleq1 anbi2d fveq2 eleq1d imbi12d eqid fvmpt2 syl2anc eqeltrd chvarfv
      simpr cneg negeq fveq2d negeqd eqeq12d znegcl adantl negex sylan2 fvmptd3
      vtocl chvarvv 3eqtr4d nfcv nfbr 3anbi2d breq1 breq1d 3anbi3d breq2 breq2d
      cn0 nn0z 3adant3 nfeq1 3adant2 breq12d sylibrd monotoddzzfi simp2 anabsi7
      vtoclg simp3 bitrd ) ADRUCZERUCZUDZDESUEDBRHUFZUGZEXDUGZSUEFGSUEAUAUBDEXD
      ABUHZRUCZUIZXGXDUGZTUCZUJAUAUHZRUCZUIZXLXDUGZTUCZUJBUAXNXPBXNBUOBXOTBRHXL
      UKZULUMXGXLUNZXIXNXKXPXRXHXMAXGXLRUPUQXRXJXOTXGXLXDURZUSUTXIXJHTXIXHHTUCZ
      XJHUNZAXHVFLBRHTXDXDVAZVBVCZLVDVEACUHZRUCZUIZYDVGZXDUGZYDXDUGZVGZUNZUJXNX
      LVGZXDUGZXOVGZUNZUJCUAYDXLUNZYFXNYKYOYPYEXMAYDXLRUPUQYPYHYMYJYNYPYGYLXDYD
      XLVHVIYPYIXOYDXLXDURVJVKUTYFJIVGYHYJMYFBYGHJRXDTYBQYEYGRUCZAYDVLZVMYEAYQJ
      TUCZYRXIXTUJZAYQUIZYSUJBYGYDVNXGYGUNZXIUUAXTYSUUBXHYQAXGYGRUPUQUUBHJTQUSU
      TLVQVOVPYFYIIYFBYDHIRXDTYBPAYEVFYTYFITUCZUJBCXGYDUNZXIYFXTUUCUUDXHYEAXGYD
      RUPUQUUDHITPUSUTLVRVPVJVSVRAXGWHUCZUBUHZWHUCZUDZXGUUFSUEZXJUUFXDUGZSUEZUJ
      ZUJZAXLWHUCZUUGUDZXLUUFSUEZXOUUJSUEZUJZUJBUAUUOUURBUUOBUOUUPUUQBUUPBUOBXO
      UUJSXQBSVTBRHUUFUKWAUMUMXRUUHUUOUULUURXRUUEUUNAUUGXGXLWHUPWBXRUUIUUPUUKUU
      QXGXLUUFSWCXRXJXOUUJSXSWDUTUTAUUEYDWHUCZUDZXGYDSUEZXJYISUEZUJZUJUUMCUBYDU
      UFUNZUUTUUHUVCUULUVDUUSUUGAUUEYDUUFWHUPWEUVDUVAUUIUVBUUKYDUUFXGSWFUVDYIUU
      JXJSYDUUFXDURWGUTUTUUTUVAHISUEUVBKUUTXJHYIISAUUEYAUUSUUEAXHYAXGWIYCVOZWJA
      UUSYIIUNZUUEAUUEUIZYAUJAUUSUIZUVFUJBCUVHUVFBUVHBUOBYIIBRHYDUKWKUMUUDUVGUV
      HYAUVFUUDUUEUUSAXGYDWHUPUQUUDXJYIHIXGYDXDURPVKUTUVEVEWLWMWNVRVEWOXCXEFXFG
      SXCBDHFRXDTYBNAXAXBWPAXAFTUCZXBAXAUVIYTAXAUIZUVIUJBDRXGDUNZXIUVJXTUVIUVKX
      HXAAXGDRUPUQUVKHFTNUSUTLWRWQWJVPXCBEHGRXDTYBOAXAXBWSAXBGTUCZXAAXBUVLYTAXB
      UIZUVLUJBERXGEUNZXIUVMXTUVLUVNXHXBAXGERUPUQUVNHGTOUSUTLWRWQWLVPWMWT $.
  $}

  ${
    $d B a x $.  $d C a x $.  $d D a x y $.  $d E a x $.  $d F a x $.
    $d A a y $.  $d ph a x y $.
    oddcomabszz.1 $e |- ( ( ph /\ x e. ZZ ) -> A e. RR ) $.
    oddcomabszz.2 $e |- ( ( ph /\ x e. ZZ /\ 0 <_ x ) -> 0 <_ A ) $.
    oddcomabszz.3 $e |- ( ( ph /\ y e. ZZ ) -> C = -u B ) $.
    oddcomabszz.4 $e |- ( x = y -> A = B ) $.
    oddcomabszz.5 $e |- ( x = -u y -> A = C ) $.
    oddcomabszz.6 $e |- ( x = D -> A = E ) $.
    oddcomabszz.7 $e |- ( x = ( abs ` D ) -> A = F ) $.
    $( An odd function which takes nonnegative values on nonnegative arguments
       commutes with ` abs ` .  (Contributed by Stefan O'Rear, 26-Sep-2014.) $)
    oddcomabszz $p |- ( ( ph /\ D e. ZZ ) -> ( abs ` E ) = F ) $=
      ( cz wceq cc0 cle va wcel wa csb cabs cfv cv wi eleq1 anbi2d csbeq1 fveq2
      fveq2d csbeq1d eqeq12d imbi12d wbr nfv nfcsb1v nfel1 nfim csbeq1a chvarfv
      cr eleq1d adantr w3a nfcv breq2 3anbi23d breq2d 3expa absidd zre ad2antlr
      nfbr absid sylancom eqtr4d negex csbie negeq eqtr3id negeqd absnid znegcl
      cneg vex vtoclf 3expia sylan2 sylibd adantl le0neg1d 3imtr4d imp 3eqtr4rd
      absnidd 0re letric sylancr mpjaodan vtoclg anabsi7 nfcvd csbiegf fvex a1i
      wo 3eqtr3d ) AGQUBZUCZBGDUDZUEUFZBGUEUFZDUDZHUEUFZIAXKXNXPRZAUAUGZQUBZUCZ
      BXSDUDZUEUFZBXSUEUFZDUDZRZUHXLXRUHUAGQXSGRZYAXLYFXRYGXTXKAXSGQUIUJYGYCXNY
      EXPYGYBXMUEBXSGDUKUMYGBYDXODXSGUEULUNUOUPYASXSTUQZYFXSSTUQZYAYHUCZYCYBYEY
      JYBYAYBVDUBZYHABUGZQUBZUCZDVDUBZUHYAYKUHBUAYAYKBYABURBYBVDBXSDUSZUTVAYLXS
      RZYNYAYOYKYQYMXTAYLXSQUIZUJYQDYBVDBXSDVBZVEUPJVCZVFAXTYHSYBTUQZAYMSYLTUQZ
      VGZSDTUQZUHZAXTYHVGZUUAUHBUAUUFUUABUUFBURBSYBTBSVHZBTVHZYPVPVAYQUUCUUFUUD
      UUAYQYMXTUUBYHAYRYLXSSTVIVJYQDYBSTYSVKUPKVCVLVMYJBYDXSDYAYHXSVDUBZYDXSRXT
      UUIAYHXSVNZVOXSVQVRUNVSYAYIUCZBXSWGZDUDZYBWGZYEYCYAUUMUUNRZYIACUGZQUBZUCZ
      FEWGZRZUHYAUUOUHZCUAUVACURUUPXSRZUURYAUUTUUOUVBUUQXTAUUPXSQUIUJUVBFUUMUUS
      UUNUVBFBUUPWGZDUDUUMBUVCDFUUPVTNWAUVBBUVCUULDUUPXSWBUNWCUVBEYBUVBEBUUPDUD
      YBBUUPDECWHMWABUUPXSDUKWCWDUOUPLVCZVFUUKBYDUULDYAYIUUIYDUULRXTUUIAYIUUJVO
      XSWEVRUNUUKYBYAYKYIYTVFYAYIYBSTUQZYASUULTUQZSUUNTUQZYIUVEYAUVFSUUMTUQZUVG
      XTAUULQUBZUVFUVHUHXSWFAUVIUVFUVHUUEAUVIUVFVGZUVHUHBUULUVJUVHBUVJBURBSUUMT
      UUGUUHBUULDUSVPVAXSVTYLUULRZUUCUVJUUDUVHUVKYMUVIUUBUVFAYLUULQUIYLUULSTVIV
      JUVKDUUMSTBUULDVBVKUPKWIWJWKYAUUMUUNSTUVDVKWLYAXSXTUUIAUUJWMWNYAYBYTWNWOW
      PWRWQXTYHYIXIZAXTSVDUBUUIUVLWSUUJSXSWTXAWMXBXCXDXKXNXQRAXKXMHUEBGDHQXKBHX
      EOXFUMWMXPIRXLBXODIGUEXGPWAXHXJ $.
  $}

  ${
    $d a x y $.  $d a x A $.  $d ps a x $.  $d ch a x $.  $d th a x $.
    $d ta a x $.  $d et a x $.  $d rh a x $.  $d ph a y $.
    2nn0ind.1 $e |- ps $.
    2nn0ind.2 $e |- ch $.
    2nn0ind.3 $e |- ( y e. NN -> ( ( th /\ ta ) -> et ) ) $.
    2nn0ind.4 $e |- ( x = 0 -> ( ph <-> ps ) ) $.
    2nn0ind.5 $e |- ( x = 1 -> ( ph <-> ch ) ) $.
    2nn0ind.6 $e |- ( x = ( y - 1 ) -> ( ph <-> th ) ) $.
    2nn0ind.7 $e |- ( x = y -> ( ph <-> ta ) ) $.
    2nn0ind.8 $e |- ( x = ( y + 1 ) -> ( ph <-> et ) ) $.
    2nn0ind.9 $e |- ( x = A -> ( ph <-> rh ) ) $.
    $( Induction on nonnegative integers with two base cases, for use with
       Lucas-type sequences.  (Contributed by Stefan O'Rear, 1-Oct-2014.) $)
    2nn0ind $p |- ( A e. NN0 -> rh ) $=
      ( c1 va cn0 wcel wsbc caddc co cmin wa cn nn0p1nn cv oveq1 sbceq1d dfsbcq
      wceq anbi12d weq ovex cc0 wb 1m1e0 eqeq2i sylbi sbcie mpbir pm3.2i simprr
      1ex cc nncn ax-1cn pncan sylancl adantr mpbird vex anbi12i 3imtr4g imp ex
      jca nnind syl nn0cn biimpa adantrr mpdan sbcieg mpbid ) JUBUCZAHJUDZGWJAH
      JTUEUFZTUGUFZUDZAHWLUDZUHZWKWJWLUIUCWPJUJAHUAUKZTUGUFZUDZAHWQUDZUHAHTTUGU
      FZUDZAHTUDZUHAHIUKZTUGUFZUDZAHXDUDZUHZAHXDTUEUFZTUGUFZUDZAHXIUDZUHZWPUAIW
      LWQTUOZWSXBWTXCXNAHWRXAWQTTUGULUMAHWQTUNUPUAIUQZWSXFWTXGXOAHWRXEWQXDTUGUL
      UMAHWQXDUNUPWQXIUOZWSXKWTXLXPAHWRXJWQXITUGULUMAHWQXIUNUPWQWLUOZWSWNWTWOXQ
      AHWRWMWQWLTUGULUMAHWQWLUNUPXBXCXBBKABHXATTUGURHUKZXAUOXRUSUOABUTXAUSXRVAV
      BNVCVDVEXCCLACHTVHOVDVEVFXDUIUCZXHXMXSXHUHZXKXLXTXKXGXSXFXGVGXTAHXJXDXSXJ
      XDUOZXHXSXDVIUCTVIUCZYAXDVJVKXDTVLVMVNUMVOXSXHXLXSDEUHFXHXLMXFDXGEADHXEXD
      TUGURPVDAEHXDIVPQVDVQAFHXIXDTUEURRVDVRVSWAVTWBWCWJWNWKWOWJWNWKWJAHWMJWJJV
      IUCYBWMJUOJWDVKJTVLVMUMWEWFWGAGHJUBSWHWI $.
  $}

  ${
    $d ph a b y $.  $d A a b x y $.  $d ps a b x $.  $d ch a b x $.
    $d th a b x $.  $d ta a b x $.
    zindbi.1 $e |- ( y e. ZZ -> ( ps <-> ch ) ) $.
    zindbi.2 $e |- ( x = y -> ( ph <-> ps ) ) $.
    zindbi.3 $e |- ( x = ( y + 1 ) -> ( ph <-> ch ) ) $.
    zindbi.4 $e |- ( x = 0 -> ( ph <-> th ) ) $.
    zindbi.5 $e |- ( x = A -> ( ph <-> ta ) ) $.
    $( Inductively transfer a property to the integers if it holds for zero and
       passes between adjacent integers in either direction.  (Contributed by
       Stefan O'Rear, 1-Oct-2014.) $)
    zindbi $p |- ( A e. ZZ -> ( th <-> ta ) ) $=
      ( vb cz wsbc cc0 cle wb dfsbcq va wcel c0ex sbcie wbr 0z wi cv wceq eleq1
      w3a breq1 3anbi13d bibi1d imbi12d breq2 3anbi23d bibi2d c1 caddc co biidd
      weq vex bitr3id ovex oveq1 sbceq1d bibi12d vtoclga 3ad2ant2 uzind vtocl2g
      biimpd 3adant3 pm2.43i mp3an1 wa mp3an2 bicomd cr 0re zre letric mpjaodan
      wo sylancr sbcieg bitrd ) HOUBZDAFHPZEDAFQPZWJWKADFQUCLUDWJQHRUEZWLWKSZHQ
      RUEZQOUBZWJWMWNUFWPWJWMUKZWNWPWJWQWNUGZWMGUHZOUBZNUHZOUBZWSXARUEZUKZAFWSP
      ZAFXAPZSZUGZWPXBQXARUEZUKZWLXFSZUGWRGNQHOOWSQUIZXDXJXGXKXLWTWPXCXIXBWSQOU
      JWSQXARULUMXLXEWLXFAFWSQTUNUOXAHUIZXJWQXKWNXMXBWJXIWMWPXAHOUJXAHQRUPUQXMX
      FWKWLAFXAHTURUOXEAFUAUHZPZSXEXESXGXEAFXAUSUTVAZPZSZXGUANWSXAUAGVCXOXEXEAF
      XNWSTURUANVCXOXFXEAFXNXATURZXNXPUIXOXQXEAFXNXPTURXSWTXEVBXDXGXRXDXFXQXEXB
      WTXFXQSZXCBCSXTGXAOGNVCZBXFCXQBXEYAXFABFWSGVDJUDAFWSXATVECAFWSUSUTVAZPYAX
      QACFYBWSUSUTVFKUDYAAFYBXPWSXAUSUTVGVHVEVIIVJVKURVNVLZVMVOVPVQWJWOVRWKWLWJ
      WPWOWKWLSZUFWJWPWOUKZYDWJWPYEYDUGZWOXHWJXBHXARUEZUKZWKXFSZUGYFGNHQOOWSHUI
      ZXDYHXGYIYJWTWJXCYGXBWSHOUJWSHXARULUMYJXEWKXFAFWSHTUNUOXAQUIZYHYEYIYDYKXB
      WPYGWOWJXAQOUJXAQHRUPUQYKXFWLWKAFXAQTURUOYCVMVOVPVSVTWJQWAUBHWAUBWMWOWFWB
      HWCQHWDWGWEVEAEFHOMWHWI $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  X and Y sequences 2: Order properties
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d a b A $.  $d a b N $.
    $( For all nonnegative indices, X is positive and Y is nonnegative.
       (Contributed by Stefan O'Rear, 24-Sep-2014.) $)
    rmxypos $p |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. NN0 ) -> ( 0 < ( A rmX N ) /\ 0
        <_ ( A rmY N ) ) ) $=
      ( cn0 wcel cc0 crmx co clt wbr crmy cle wa wi oveq2 breq2d anbi12d imbi2d
      wceq cz 3ad2ant2 va vb c2 cuz cfv cv c1 weq 0lt1 rmx0 breqtrrid 0le0 rmy0
      caddc jca cmul cexp cmin simp2 nn0z 3ad2ant1 frmx fovcl syl2anc nn0red cr
      eluzelre remulcld rmspecpos rpred frmy zred simp3l eluz2nn nngt0d mulgt0d
      rpge0d simp3r mulge0d addgtge0d rmxp1 breqtrrd eluzge2nn0 nn0ge0d addge0d
      w3a rmyp1 3exp a2d nn0ind impcom ) BCDAUCUDUEZDZEABFGZHIZEABJGZKIZLZWMEAU
      AUFZFGZHIZEAWSJGZKIZLZMWMEAEFGZHIZEAEJGZKIZLZMWMEAUBUFZFGZHIZEAXJJGZKIZLZ
      MWMEAXJUGUNGZFGZHIZEAXPJGZKIZLZMWMWRMUAUBBWSERZXDXIWMYBXAXFXCXHYBWTXEEHWS
      EAFNOYBXBXGEKWSEAJNOPQUAUBUHZXDXOWMYCXAXLXCXNYCWTXKEHWSXJAFNOYCXBXMEKWSXJ
      AJNOPQWSXPRZXDYAWMYDXAXRXCXTYDWTXQEHWSXPAFNOYDXBXSEKWSXPAJNOPQWSBRZXDWRWM
      YEXAWOXCWQYEWTWNEHWSBAFNOYEXBWPEKWSBAJNOPQWMXFXHWMEUGXEHUIAUJUKWMEEXGKULA
      UMUKUOXJCDZWMXOYAYFWMXOYAYFWMXOWFZXRXTYGEXKAUPGZAUCUQGUGURGZXMUPGZUNGZXQH
      YGYHYJYGXKAYGXKYGWMXJSDZXKCDYFWMXOUSZYFWMYLXOXJUTVAZAXJCWLSFVBVCVDZVEZWMY
      FAVFDXOUCAVGTZVHYGYIXMWMYFYIVFDXOWMYIAVIZVJTZYGXMYGWMYLXMSDYMYNAXJSWLSJVK
      VCVDVLZVHYGXKAYPYQYFWMXLXNVMWMYFEAHIXOWMAAVNVOTVPYGYIXMYSYTWMYFEYIKIXOWMY
      IYRVQTYFWMXLXNVRZVSVTYGWMYLXQYKRYMYNAXJWAVDWBYGEXMAUPGZXKUNGZXSKYGUUBXKYG
      XMAYTYQVHYPYGXMAYTYQUUAWMYFEAKIXOWMAAWCWDTVSYGXKYOWDWEYGWMYLXSUUCRYMYNAXJ
      WGVDWBUOWHWIWJWK $.
  $}

  ${
    $d N a b $.  $d M a b $.  $d A a b $.
    $( The Y-sequence is strictly monotonic on ` NN0 ` .  Strengthened by
       ~ ltrmy .  (Contributed by Stefan O'Rear, 24-Sep-2014.) $)
    ltrmynn0 $p |- ( ( A e. ( ZZ>= ` 2 ) /\ M e. NN0 /\ N e. NN0 ) -> ( M < N
        <-> ( A rmY M ) < ( A rmY N ) ) ) $=
      ( va vb c2 wcel cn0 clt wbr crmy co cv c1 caddc cc0 cz fovcl sylan2 oveq2
      cuz cfv wb wa cmul crmx nn0z frmy zred cr eluzelre adantr remulcld nn0red
      frmx readdcld cle rmxypos simprd nnge1d lemulge11d simpld ltaddposd mpbid
      eluz2nn lelttrd wceq rmyp1 breqtrrd nn0uz monotuz 3impb ) AFUAUBZGZBHGCHG
      BCIJABKLZACKLZIJUCVNDEBCADMZKLZVOVPAEMZKLZAVSNOLZKLZHPVNVSHGZUDZVTVTAUELZ
      AVSUFLZOLZWBIWDVTWEWGWDVTWCVNVSQGZVTQGVSUGZAVSQVMQKUHRSUIZWDVTAWJVNAUJGWC
      FAUKULZUMZWDWEWFWLWDWFWCVNWHWFHGWIAVSHVMQUFUORSUNZUPWDVTAWJWKWDPWFIJZPVTU
      QJZAVSURZUSVNNAUQJWCVNAAVEUTULVAWDWNWEWGIJWDWNWOWPVBWDWFWEWMWLVCVDVFWCVNW
      HWBWGVGWIAVSVHSVIVNVQHGZUDVRWQVNVQQGVRQGVQUGAVQQVMQKUHRSUIVJVQWAAKTVQVSAK
      TVQBAKTVQCAKTVKVL $.
  $}

  ${
    $d A a b $.  $d M a b $.  $d N a b $.
    $( The X-sequence is strictly monotonic on ` NN0 ` .  (Contributed by
       Stefan O'Rear, 4-Oct-2014.) $)
    ltrmxnn0 $p |- ( ( A e. ( ZZ>= ` 2 ) /\ M e. NN0 /\ N e. NN0 ) -> ( M < N
        <-> ( A rmX M ) < ( A rmX N ) ) ) $=
      ( c2 wcel cn0 clt wbr crmx co c1 cz frmx fovcl sylan2 nn0red adantr oveq2
      cc0 cle va vb cuz cfv wb cv caddc wa cmul nn0z eluzelre remulcld peano2zd
      cr cn eluz2b2 simprbi crmy rmxypos ltmulgt11 syl3anc mpbid cexp csquarenn
      simpld cmin rmspecnonsq eldifad nnred frmy nnnn0d nn0ge0d simprd addge01d
      zred mulge0d wceq rmxp1 breqtrrd ltletrd nn0uz monotuz 3impb ) ADUCUDZEZB
      FECFEBCGHABIJZACIJZGHUEWEUAUBBCAUAUFZIJZWFWGAUBUFZIJZAWJKUGJZIJZFSWEWJFEZ
      UHZWKWKAUIJZWMWOWKWNWEWJLEZWKFEWJUJZAWJFWDLIMNOPZWOWKAWSWEAUNEZWNDAUKQZUL
      ZWOWMWNWEWLLEWMFEWNWJWRUMAWLFWDLIMNOPWOKAGHZWKWPGHZWEXCWNWEAUOEXCAUPUQQWO
      WKUNEWTSWKGHZXCXDUEWSXAWOXESAWJURJZTHZAWJUSZVEWKAUTVAVBWOWPWPADVCJKVFJZXF
      UIJZUGJZWMTWOSXJTHWPXKTHWOXIXFWOXIWEXIUOEWNWEXIUOVDAVGVHQZVIZWOXFWNWEWQXF
      LEWRAWJLWDLURVJNOVOZWOXIWOXIXLVKVLWOXEXGXHVMVPWOWPXJXBWOXIXFXMXNULVNVBWNW
      EWQWMXKVQWRAWJVROVSVTWEWHFEZUHWIXOWEWHLEWIFEWHUJAWHFWDLIMNOPWAWHWLAIRWHWJ
      AIRWHBAIRWHCAIRWBWC $.

    $( The X-sequence is monotonic on ` NN0 ` .  (Contributed by Stefan O'Rear,
       4-Oct-2014.) $)
    lermxnn0 $p |- ( ( A e. ( ZZ>= ` 2 ) /\ M e. NN0 /\ N e. NN0 ) -> ( M <_ N
        <-> ( A rmX M ) <_ ( A rmX N ) ) ) $=
      ( va vb c2 cuz cfv wcel cn0 cle wbr crmx co wb cv oveq2 nn0ssre cz clt wa
      nn0z frmx fovcl sylan2 nn0red wi w3a ltrmxnn0 biimpd 3expb leord1 3impb )
      AFGHZIZBJICJIBCKLABMNZACMNZKLOUODEADPZMNZAEPZMNZBCJUPUQURUTAMQURBAMQURCAM
      QRUOURJIZUAUSVBUOURSIUSJIURUBAURJUNSMUCUDUEUFUOVBUTJIZURUTTLZUSVATLZUGUOV
      BVCUHVDVEAURUTUIUJUKULUM $.

    $( The X-sequence is defined to range over ` NN0 ` but never actually takes
       the value 0.  (Contributed by Stefan O'Rear, 4-Oct-2014.) $)
    rmxnn $p |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. ZZ ) -> ( A rmX N ) e. NN ) $=
      ( wcel cz wa cn0 crmx co cn cc0 clt wbr nn0z frmx sylan2 crmy cle rmxypos
      fovcl simpld c2 cuz cfv cneg elnnnn0b sylanbrc adantlr wceq rmxneg adantr
      eqeltrrd wo cr elznn0 simprbi adantl mpjaodan ) AUAUBUCZCZBDCZEZBFCZABGHZ
      ICZBUDZFCZUSVBVDUTUSVBEZVCFCZJVCKLZVDVBUSUTVHBMABFURDGNSOVGVIJABPHQLABRTV
      CUEUFUGVAVFEAVEGHZVCIVAVJVCUHVFABUIUJUSVFVJICZUTUSVFEZVJFCZJVJKLZVKVFUSVE
      DCVMVEMAVEFURDGNSOVLVNJAVEPHQLAVERTVJUEUFUGUKUTVBVFULZUSUTBUMCVOBUNUOUPUQ
      $.
  $}

  ${
    $d M a b $.  $d N a b $.  $d A a b $.
    $( The Y-sequence is strictly monotonic over ` ZZ ` .  (Contributed by
       Stefan O'Rear, 25-Sep-2014.) $)
    ltrmy $p |- ( ( A e. ( ZZ>= ` 2 ) /\ M e. ZZ /\ N e. ZZ ) -> ( M < N <-> (
        A rmY M ) < ( A rmY N ) ) ) $=
      ( va vb c2 cuz cfv wcel crmy co cv cneg cn0 w3a clt wbr ltrmynn0 cz oveq2
      biimpd wa frmy fovcl zred rmyneg monotoddzz ) AFGHZIZDEBCABJKACJKADLZJKZA
      ELZJKZAULMZJKUIUJNIULNIOUJULPQUKUMPQAUJULRUAUIUJSIUBUKAUJSUHSJUCUDUEAULUF
      UJBAJTUJCAJTUJULAJTUJUNAJTUG $.
  $}

  ${
    $d A a b $.  $d N a b $.
    $( Y is zero only at zero.  (Contributed by Stefan O'Rear, 26-Sep-2014.) $)
    rmyeq0 $p |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. ZZ ) -> ( N = 0 <-> ( A rmY N )
        = 0 ) ) $=
      ( va vb c2 cuz cfv wcel cz wa cc0 wceq crmy co wb 0z cv oveq2 clt wbr w3a
      zssre frmy fovcl zred ltrmy biimpd 3expb eqord1 mpanr2 rmy0 adantr eqeq2d
      wi bitrd ) AEFGZHZBIHZJZBKLZABMNZAKMNZLZVAKLUQURKIHUTVCOPUQCDACQZMNZADQZM
      NZBKIVAVBVDVFAMRVDBAMRVDKAMRUBUQVDIHZJVEAVDIUPIMUCUDUEUQVHVFIHZVDVFSTZVEV
      GSTZUNUQVHVIUAVJVKAVDVFUFUGUHUIUJUSVBKVAUQVBKLURAUKULUMUO $.
  $}

  ${
    $d A a b $.  $d N a b $.  $d M a b $.
    $( Y is one-to-one.  (Contributed by Stefan O'Rear, 3-Oct-2014.) $)
    rmyeq $p |- ( ( A e. ( ZZ>= ` 2 ) /\ M e. ZZ /\ N e. ZZ ) -> ( M = N <-> (
        A rmY M ) = ( A rmY N ) ) ) $=
      ( va vb c2 cuz cfv wcel cz wceq crmy co wb cv oveq2 zssre wa clt wbr frmy
      fovcl zred wi w3a ltrmy biimpd 3expb eqord1 3impb ) AFGHZIZBJICJIBCKABLMZ
      ACLMZKNULDEADOZLMZAEOZLMZBCJUMUNUOUQALPUOBALPUOCALPQULUOJIZRUPAUOJUKJLUAU
      BUCULUSUQJIZUOUQSTZUPURSTZUDULUSUTUEVAVBAUOUQUFUGUHUIUJ $.
  $}

  ${
    $d A a b $.  $d N a b $.  $d M a b $.
    $( Y is monotonic (non-strict).  (Contributed by Stefan O'Rear,
       3-Oct-2014.) $)
    lermy $p |- ( ( A e. ( ZZ>= ` 2 ) /\ M e. ZZ /\ N e. ZZ ) -> ( M <_ N <-> (
        A rmY M ) <_ ( A rmY N ) ) ) $=
      ( va vb c2 cuz cfv wcel cz cle wbr crmy co wb cv oveq2 zssre wa clt fovcl
      frmy zred wi w3a ltrmy biimpd 3expb leord1 3impb ) AFGHZIZBJICJIBCKLABMNZ
      ACMNZKLOULDEADPZMNZAEPZMNZBCJUMUNUOUQAMQUOBAMQUOCAMQRULUOJIZSUPAUOJUKJMUB
      UAUCULUSUQJIZUOUQTLZUPURTLZUDULUSUTUEVAVBAUOUQUFUGUHUIUJ $.
  $}
  $( ` rmY ` is positive for positive arguments.  (Contributed by Stefan
     O'Rear, 16-Oct-2014.) $)
  rmynn $p |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. NN ) -> ( A rmY N ) e. NN ) $=
    ( c2 cuz cfv wcel cn wa crmy co cz cc0 clt wbr nnz frmy fovcl sylan2 adantl
    wceq rmy0 adantr nngt0 wb simpl ltrmy syl3anc mpbid eqbrtrrd elnnz sylanbrc
    0zd ) ACDEZFZBGFZHZABIJZKFZLUQMNUQGFUOUNBKFZURBOZABKUMKIPQRUPALIJZLUQMUNVAL
    TUOAUAUBUPLBMNZVAUQMNZUOVBUNBUCSUPUNLKFUSVBVCUDUNUOUEUPULUOUSUNUTSALBUFUGUH
    UIUQUJUK $.

  $( ` rmY ` is nonnegative for nonnegative arguments.  (Contributed by Stefan
     O'Rear, 16-Oct-2014.) $)
  rmynn0 $p |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. NN0 ) -> ( A rmY N ) e. NN0 ) $=
    ( c2 cuz cfv wcel cn0 wa crmy co cz cc0 cle wbr nn0z frmy fovcl sylan2 crmx
    clt rmxypos simprd elnn0z sylanbrc ) ACDEZFZBGFZHZABIJZKFZLUIMNZUIGFUGUFBKF
    UJBOABKUEKIPQRUHLABSJTNUKABUAUBUIUCUD $.

  ${
    $d A a b $.  $d B a b $.
    $( ` rmY ` commutes with ` abs ` .  (Contributed by Stefan O'Rear,
       26-Sep-2014.) $)
    rmyabs $p |- ( ( A e. ( ZZ>= ` 2 ) /\ B e. ZZ ) -> ( abs ` ( A rmY B ) ) =
        ( A rmY ( abs ` B ) ) ) $=
      ( va vb c2 cuz cfv wcel cv crmy co cneg cabs cz wa frmy cc0 cle wbr oveq2
      fovcl zred w3a crmx clt cn0 elnn0z biimpri 3adant1 rmxypos syl2anc simprd
      simp1 rmyneg oddcomabszz ) AEFGZHZCDACIZJKZADIZJKAUTLZJKBABJKABMGZJKUQURN
      HZOUSAURNUPNJPUAUBUQVCQURRSZUCZQAURUDKUESZQUSRSZVEUQURUFHZVFVGOUQVCVDUMVC
      VDVHUQVHVCVDOURUGUHUIAURUJUKULAUTUNURUTAJTURVAAJTURBAJTURVBAJTUO $.
  $}

  $( X(n) is strictly greater than Y(n) + Y(n-1).  Lemma 2.24 of
     [JonesMatijasevic] p. 697 restricted to ` NN ` .  (Contributed by Stefan
     O'Rear, 3-Oct-2014.) $)
  jm2.24nn $p |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. NN ) -> ( ( A rmY ( N - 1 ) ) +
      ( A rmY N ) ) < ( A rmX N ) ) $=
    ( c2 wcel c1 cmin co crmy caddc cmul cz sylan2 cn0 clt wbr recnd mpbid wceq
    cr cc0 cuz cfv cn wa crmx nnz 1z zsubcl sylancl frmy fovcl readdcld remulcl
    zred 2re sylancr resubcld frmx nn0red eluzelre remulcld a1i nnm1nn0 rmxypos
    adantr cle simprd eluzle lemul1ad mulcomd ltaddposd eqbrtrd lelttrd 2timesd
    simpld rmyp1 cc nnre adantl ax-1cn oveq2d eqtr3d 3brtr3d ltaddsubd ltadd1dd
    npcan oveq1d addsubd eqtrd breqtrrd rmy0 nngt0 simpl ltrmy syl3anc eqbrtrrd
    wb 0zd lemul1 syl112anc lesub1dd rmym1 eqtr2d subsub23 breqtrd ltletrd ) AC
    UAUBZDZBUCDZUDZABEFGZHGZABHGZIGZCXMJGZXLFGZABUEGZXJXLXMXJXLXIXHXKKDZXLKDXIB
    KDZEKDXRBUFZUGBEUHUIZAXKKXGKHUJUKLUNZXJXMXIXHXSXMKDXTABKXGKHUJUKLUNZULXJXOX
    LXJCSDZXMSDZXOSDUOYCCXMUMUPZYBUQXJXQXIXHXSXQMDXTABMXGKUEURUKLUSZXJXNXMXLFGZ
    XMIGZXPNXJXLYHXMYBXJXMXLYCYBUQYCXJXLXLIGZXMNOXLYHNOXJCXLJGZXLAJGZAXKUEGZIGZ
    YJXMNXJYKAXLJGZYNXJYDXLSDYKSDUOYBCXLUMUPXJAXLXHASDZXICAUTVEZYBVAXJYLYMXJXLA
    YBYQVAZXJYMXIXHXRYMMDYAAXKMXGKUEURUKLUSZULXJCAXLYDXJUOVBZYQYBXIXHXKMDZTXLVF
    OZBVCZXHUUAUDZTYMNOZUUBAXKVDZVGLXHCAVFOZXICAVHVEZVIXJYOYLYNNXJAXLXJAYQPZXJX
    LYBPZVJXJUUEYLYNNOXIXHUUAUUEUUCUUDUUEUUBUUFVOLXJYMYLYSYRVKQVLVMXJXLUUJVNXJA
    XKEIGZHGZYNXMXIXHXRUULYNRYAAXKVPLXJUUKBAHXJBVQDEVQDUUKBRXJBXIBSDXHBVRVSPVTB
    EWFUIWAWBWCXJXLXLXMYBYBYCWDQWEXJXPXMXMIGZXLFGYIXJXOUUMXLFXJXMXJXMYCPZVNWGXJ
    XMXMXLUUNUUNUUJWHWIWJXJXPAXMJGZXLFGZXQVFXJXOUUOXLYFXJAXMYQYCVAZYBXJUUGXOUUO
    VFOZUUHXJYDYPYETXMNOUUGUURWQYTYQYCXJATHGZTXMNXHUUSTRXIAWKVEXJTBNOZUUSXMNOZX
    IUUTXHBWLVSXJXHTKDXSUUTUVAWQXHXIWMXJWRXIXSXHXTVSATBWNWOQWPCAXMWSWTQXAXJUUOX
    QFGZXLRZUUPXQRZXJXLXMAJGZXQFGZUVBXIXHXSXLUVFRXTABXBLXJUVEUUOXQFXJXMAUUNUUIV
    JWGXCXJUUOVQDXQVQDXLVQDUVCUVDWQXJUUOUUQPXJXQYGPUUJUUOXQXLXDWOQXEXF $.

  ${
    $d A a b $.  $d N a b $.
    $( First half of lemma 2.17 of [JonesMatijasevic] p. 696.  (Contributed by
       Stefan O'Rear, 14-Oct-2014.) $)
    jm2.17a $p |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. NN0 ) -> ( ( ( 2 x. A ) - 1 ) ^
        N ) <_ ( A rmY ( N + 1 ) ) ) $=
      ( wcel c2 cmul co c1 cmin cexp caddc crmy cle wbr wi wceq oveq2d cc cr cz
      cc0 va vb cn0 cuz cfv cv oveq2 oveq1 breq12d imbi2d weq 1le1 a1i eluzelcn
      mulcl sylancr ax-1cn subcl sylancl exp0d 0p1e1 oveq2i rmy1 eqtrid 3brtr4d
      2cn w3a 2re eluzelre adantl remulcl 1re resubcl peano2nn0 adantr reexpcld
      wa 3adant3 simpr nn0z peano2zd frmy fovcl syl2anc remulcld 3ad2ant2 simp1
      zred expp1d simpl cn 2nn eluz2nn nnmulcl nnm1nn0 nn0ge0 3syl 3jca lemul1a
      jca stoic3 eqbrtrd nn0cn pncan eqeltrd nn0re lep1d wb lermy syl3anc mpbid
      recnd mulridd lesub2dd subdid mulcomd oveq1d eqtrd rmyluc2 letrd 3exp a2d
      nn0ind impcom ) BUCCADUDUEZCZDAEFZGHFZBIFZABGJFZKFZLMZYFYHUAUFZIFZAYMGJFZ
      KFZLMZNYFYHTIFZATGJFZKFZLMZNYFYHUBUFZIFZAUUBGJFZKFZLMZNYFYHUUDIFZAUUDGJFZ
      KFZLMZNYFYLNUAUBBYMTOZYQUUAYFUUKYNYRYPYTLYMTYHIUGUUKYOYSAKYMTGJUHPUIUJUAU
      BUKZYQUUFYFUULYNUUCYPUUELYMUUBYHIUGUULYOUUDAKYMUUBGJUHPUIUJYMUUDOZYQUUJYF
      UUMYNUUGYPUUILYMUUDYHIUGUUMYOUUHAKYMUUDGJUHPUIUJYMBOZYQYLYFUUNYNYIYPYKLYM
      BYHIUGUUNYOYJAKYMBGJUHPUIUJYFGGYRYTLGGLMYFULUMYFYHYFYGQCZGQCZYHQCZYFDQCAQ
      CUUOVFDAUNDAUOUPUQYGGURUSZUTYFYTAGKFGYSGAKVAVBAVCVDVEUUBUCCZYFUUFUUJUUSYF
      UUFUUJUUSYFUUFVGZUUGUUEYHEFZUUIUUSYFUUGRCUUFUUSYFVQZYHUUDUVBYGRCZGRCZYHRC
      ZUVBDRCARCZUVCVHYFUVFUUSDAVIVJDAVKUPZVLYGGVMUSZUUSUUDUCCYFUUBVNVOVPVRUUSY
      FUVARCUUFUVBUUEYHUVBYFUUDSCZUUERCZUUSYFVSZUVBUUBUUSUUBSCZYFUUBVTVOZWAZYFU
      VIVQUUEAUUDSYESKWBWCWHWDZUVHWEVRUUSYFUUIRCZUUFUVBYFUUHSCZUVPUVKUVBUUDUVNW
      AYFUVQVQUUIAUUHSYESKWBWCWHWDVRUUTUUGUUCYHEFZUVALUUTYHUUBYFUUSUUQUUFUURWFU
      USYFUUFWGWIUUSYFUUCRCZUVJUVETYHLMZVQZVGUUFUVRUVALMUVBUVSUVJUWAUVBYHUUBUVH
      UUSYFWJVPUVOUVBUVEUVTUVHUVBYGWKCZYHUCCUVTUVBDWKCAWKCZUWBWLYFUWCUUSAWMVJDA
      WNUPYGWOYHWPWQWTWRUUCUUEYHWSXAXBUUSYFUVAUUILMUUFUVBYGUUEEFZUUEGEFZHFZUWDA
      UUDGHFZKFZHFZUVAUUILUVBUWHUWEUWDUVBUWHAUUBKFZRUVBUWGUUBAKUVBUUBQCZUUPUWGU
      UBOUUSUWKYFUUBXCVOUQUUBGXDUSPZUVBYFUVLUWJRCUVKUVMYFUVLVQUWJAUUBSYESKWBWCW
      HWDXEUVBUVJUVDUWERCUVOVLUUEGVKUSUVBYGUUEUVGUVOWEUVBUWJUUEUWHUWELUVBUUBUUD
      LMZUWJUUELMZUVBUUBUUSUUBRCYFUUBXFVOXGUVBYFUVLUVIUWMUWNXHUVKUVMUVNAUUBUUDX
      IXJXKUWLUVBUUEUVBUUEUVOXLZXMVEXNUVBUVAUUEYGEFZUWEHFUWFUVBUUEYGGUWOUVBYGUV
      GXLZUUPUVBUQUMXOUVBUWPUWDUWEHUVBUUEYGUWOUWQXPXQXRUVBYFUVIUUIUWIOUVKUVNAUU
      DXSWDVEVRXTYAYBYCYD $.

    $( Weak form of the second half of lemma 2.17 of [JonesMatijasevic] p. 696,
       allowing induction to start lower.  (Contributed by Stefan O'Rear,
       15-Oct-2014.) $)
    jm2.17b $p |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. NN0 ) -> ( A rmY ( N + 1 ) )
        <_ ( ( 2 x. A ) ^ N ) ) $=
      ( wcel c2 c1 caddc co crmy cmul cexp cle wbr wi wceq oveq2d breq12d cr wa
      cc0 cz va vb cn0 cuz cfv cv oveq1 oveq2 imbi2d weq 1le1 0p1e1 oveq2i rmy1
      eqtrid eluzelre remulcl sylancr recnd exp0d mpbiri cmin simpr nn0z adantr
      2re w3a peano2zd rmyluc2 syl2anc crmx clt rmxypos simprd ancoms cc ax-1cn
      nn0re pncan sylancl breqtrrd adantl fovcl remulcld eqeltrd subge02d mpbid
      frmy zred eqbrtrd 3adant3 wb simpl reexpcld cn 2nn eluz2nn nnmulcl nngt0d
      lemul2 syl112anc biimp3a expp1d mulcomd eqtrd peano2nn0 letr syl3anc 3exp
      mp2and a2d nn0ind impcom ) BUCCADUDUEZCZABEFGZHGZDAIGZBJGZKLZXOAUAUFZEFGZ
      HGZXRYAJGZKLZMXOASEFGZHGZXRSJGZKLZMXOAUBUFZEFGZHGZXRYJJGZKLZMXOAYKEFGZHGZ
      XRYKJGZKLZMXOXTMUAUBBYASNZYEYIXOYSYCYGYDYHKYSYBYFAHYASEFUGOYASXRJUHPUIUAU
      BUJZYEYNXOYTYCYLYDYMKYTYBYKAHYAYJEFUGOYAYJXRJUHPUIYAYKNZYEYRXOUUAYCYPYDYQ
      KUUAYBYOAHYAYKEFUGOYAYKXRJUHPUIYABNZYEXTXOUUBYCXQYDXSKUUBYBXPAHYABEFUGOYA
      BXRJUHPUIXOYIEEKLUKXOYGEYHEKXOYGAEHGEYFEAHULUMAUNUOXOXRXOXRXODQCZAQCZXRQC
      ZVFDAUPZDAUQZURUSUTPVAYJUCCZXOYNYRUUHXOYNYRUUHXOYNVGZYPXRYLIGZKLZUUJYQKLZ
      YRUUHXOUUKYNUUHXORZYPUUJAYKEVBGZHGZVBGZUUJKUUMXOYKTCZYPUUPNUUHXOVCZUUMYJU
      UHYJTCZXOYJVDVEZVHZAYKVIVJUUMSUUOKLUUPUUJKLUUMSAYJHGZUUOKXOUUHSUVBKLZXOUU
      HRSAYJVKGVLLUVCAYJVMVNVOUUMUUNYJAHUUMYJVPCEVPCUUNYJNUUMYJUUHYJQCXOYJVRVEU
      SVQYJEVSVTOZWAUUMUUJUUOUUMXRYLUUMUUCUUDUUEVFXOUUDUUHUUFWBUUGURZUUMXOUUQYL
      QCZUURUVAXOUUQRYLAYKTXNTHWHWCWIVJZWDZUUMUUOUVBQUVDUUMXOUUSUVBQCUURUUTXOUU
      SRUVBAYJTXNTHWHWCWIVJWEWFWGWJWKUUIUUJXRYMIGZYQKUUHXOYNUUJUVIKLZUUMUVFYMQC
      UUESXRVLLZYNUVJWLUVGUUMXRYJUVEUUHXOWMZWNZUVEXOUVKUUHXOXRXODWOCAWOCXRWOCWP
      AWQDAWRURWSWBYLYMXRWTXAXBUUHXOYQUVINYNUUMYQYMXRIGUVIUUMXRYJUUMXRUVEUSZUVL
      XCUUMYMXRUUMYMUVMUSUVNXDXEWKWAUUHXOUUKUULRYRMZYNUUMYPQCZUUJQCYQQCUVOUUMXO
      YOTCZUVPUURUUMYKUVAVHXOUVQRYPAYOTXNTHWHWCWIVJUVHUUMXRYKUVEUUHYKUCCXOYJXFV
      EWNYPUUJYQXGXHWKXJXIXKXLXM $.
  $}

  $( Second half of lemma 2.17 of [JonesMatijasevic] p. 696.  (Contributed by
     Stefan O'Rear, 15-Oct-2014.) $)
  jm2.17c $p |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. NN ) ->
      ( A rmY ( ( N + 1 ) + 1 ) ) < ( ( 2 x. A ) ^ ( N + 1 ) ) ) $=
    ( c2 wcel cn wa cmul co c1 caddc crmy clt cr adantr cz adantl cc0 wbr mpbid
    wceq cuz cfv cmin cexp 2re eluzelre remulcl sylancr nnz peano2zd frmy fovcl
    zred syldan remulcld cc ax-1cn pncan sylancl oveq2d sylan2 eqeltrd resubcld
    nncn cn0 nnnn0 reexpcld rmy0 nngt0 wb simpl ltrmy syl3anc eqbrtrrd breqtrrd
    0zd ltsubposd cle jm2.17b 2nn eluz2nn nnmulcl nngt0d lemul2 ltletrd rmyluc2
    syl112anc recnd expp1d mulcomd eqtrd 3brtr4d ) ACUAUBZDZBEDZFZCAGHZABIJHZKH
    ZGHZAWRIUCHZKHZUCHZWQWQBUDHZGHZAWRIJHKHZWQWRUDHZLWPXCWTXEWPWTXBWPWQWSWPCMDA
    MDZWQMDZUEWNXHWOCAUFNCAUGUHZWNWOWRODZWSMDZWPBWOBODZWNBUIZPZUJZWNXKFWSAWROWM
    OKUKULUMUNZUOZWPXBABKHZMWPXABAKWPBUPDZIUPDXABTWOXTWNBVDPUQBIURUSUTZWOWNXMXS
    MDXNWNXMFXSABOWMOKUKULUMVAVBZVCXRWPWQXDXJWPWQBXJWOBVEDZWNBVFZPZVGZUOWPQXBLR
    XCWTLRWPQXSXBLWPAQKHZQXSLWNYGQTWOAVHNWPQBLRZYGXSLRZWOYHWNBVIPWPWNQODXMYHYIV
    JWNWOVKWPVPXOAQBVLVMSVNYAVOWPXBWTYBXRVQSWPWSXDVRRZWTXEVRRZWOWNYCYJYDABVSVAW
    PXLXDMDXIQWQLRZYJYKVJXQYFXJWNYLWOWNWQWNCEDAEDWQEDVTAWACAWBUHWCNWSXDWQWDWGSW
    EWNWOXKXFXCTXPAWRWFUNWPXGXDWQGHXEWPWQBWPWQXJWHZYEWIWPXDWQWPXDYFWHYMWJWKWL
    $.

  $( Lemma 2.24 of [JonesMatijasevic] p. 697 extended to ` ZZ ` .  Could be
     eliminated with a more careful proof of ~ jm2.26lem3 .  (Contributed by
     Stefan O'Rear, 3-Oct-2014.) $)
  jm2.24 $p |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. ZZ ) -> ( ( A rmY ( N - 1 ) ) + (
      A rmY N ) ) < ( A rmX N ) ) $=
    ( wcel cz wa cc0 cle wbr c1 crmy caddc clt ad2antlr frmy fovcl syl2anc zred
    co cneg wceq c2 cuz cfv cmin crmx simpll peano2zm adantr readdcld 0red frmx
    cr cn0 nn0red znegcl peano2zd rmy0 ad2antrr simpr zre le0neg1d mpbid wb 0zd
    zleltp1 ltrmy syl3anc eqbrtrrd lermy addgtge0d negdid rmyneg oveq12d cc zcn
    recnd ax-1cn negsubdi sylancl oveq2d oveq1d 3eqtr2d breqtrrd mpbird nn0ge0d
    lt0neg1d ltletrd cn elnnz biimpri adantll jm2.24nn adantl lelttric mpjaodan
    wo 0re ) AUAUBUCZCZBDCZEZBFGHZABIUDRZJRZABJRZKRZABUERZLHZFBLHZXAXBEZXFFXGXJ
    XDXEXJXDXJWSXCDCZXDDCWSWTXBUFZWTXKWSXBBUGMZAXCDWRDJNOPQZXAXEULCXBXAXEABDWRD
    JNOQUHZUIZXJUJXJXGXAXGUMCXBABUMWRDUEUKOUHZUNXJXFFLHFXFSZLHXJFABSZIKRZJRZAXS
    JRZKRZXRLXJYAYBXJYAXJWSXTDCZYADCXLXJXSWTXSDCZWSXBBUOMZUPZAXTDWRDJNOPQXJYBXJ
    WSYEYBDCXLYFAXSDWRDJNOPQXJAFJRZFYALWSYHFTWTXBAUQURZXJFXTLHZYHYALHZXJFXSGHZY
    JXJXBYLXAXBUSXJBWTBULCZWSXBBUTZMVAVBZXJFDCZYEYLYJVCXJVDZYFFXSVEPVBXJWSYPYDY
    JYKVCXLYQYGAFXTVFVGVBVHXJYHFYBGYIXJYLYHYBGHZYOXJWSYPYEYLYRVCXLYQYFAFXSVIVGV
    BVHVJXJXRXDSZXESZKRAXCSZJRZYBKRYCXJXDXEXJXDXNVPXJXEXOVPVKXJUUBYSYBYTKXJWSXK
    UUBYSTXLXMAXCVLPXAYBYTTXBABVLUHVMXJUUBYAYBKXJUUAXTAJXJBVNCZIVNCUUAXTTWTUUCW
    SXBBVOMVQBIVRVSVTWAWBWCXJXFXPWFWDXJXGXQWEWGXAXIEWSBWHCZXHWSWTXIUFWTXIUUDWSU
    UDWTXIEBWIWJWKABWLPXAYMFULCXBXIWPWTYMWSYNWMWQBFWNVSWO $.

  ${
    $d A a b $.  $d N a b $.
    $( Y(n) increases faster than n.  Used implicitly without proof or comment
       in lemma 2.27 of [JonesMatijasevic] p. 697.  (Contributed by Stefan
       O'Rear, 4-Oct-2014.) $)
    rmygeid $p |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. NN0 ) -> N <_ ( A rmY N ) ) $=
      ( va vb wcel crmy co cle wbr wi cc0 c1 id oveq2 breq12d imbi2d cz syl2anc
      wceq zred cn0 c2 cuz cfv cv weq 0le0 rmy0 breqtrrid w3a 3ad2ant1 peano2zd
      caddc nn0z simp2 frmy fovcl cr nn0re 1red simp3 leadd1dd ltp1d wb syl3anc
      clt ltrmy mpbid zltp1le letrd 3exp a2d nn0ind impcom ) BUAEAUBUCUDZEZBABF
      GZHIZVPCUEZAVSFGZHIZJVPKAKFGZHIZJVPDUEZAWDFGZHIZJVPWDLUMGZAWGFGZHIZJVPVRJ
      CDBVSKSZWAWCVPWJVSKVTWBHWJMVSKAFNOPCDUFZWAWFVPWKVSWDVTWEHWKMVSWDAFNOPVSWG
      SZWAWIVPWLVSWGVTWHHWLMVSWGAFNOPVSBSZWAVRVPWMVSBVTVQHWMMVSBAFNOPVPKKWBHUGA
      UHUIWDUAEZVPWFWIWNVPWFWIWNVPWFUJZWGWELUMGZWHWOWGWOWDWNVPWDQEZWFWDUNUKZULZ
      TWOWPWOWEWOVPWQWEQEZWNVPWFUOZWRAWDQVOQFUPUQRZULTWOWHWOVPWGQEZWHQEZXAWSAWG
      QVOQFUPUQRZTWOWDWELWNVPWDUREWFWDUSUKZWOWEXBTWOUTWNVPWFVAVBWOWEWHVFIZWPWHH
      IZWOWDWGVFIZXGWOWDXFVCWOVPWQXCXIXGVDXAWRWSAWDWGVGVEVHWOWTXDXGXHVDXBXEWEWH
      VIRVHVJVKVLVMVN $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Congruential equations
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( A wff of the form ` A || ( B - C ) ` is interpreted as a congruential
     equation.  This is similar to ` ( B mod A ) = ( C mod A ) ` , but is
     defined such that behavior is regular for zero and negative values of
     ` A ` .  To use this concept effectively, we need to show that
     congruential equations behave similarly to normal equations; first a
     transitivity law.  Idea for the future:  If there was a congruential
     equation symbol, it could incorporate type constraints, so that most of
     these would not need them.  (Contributed by Stefan O'Rear, 1-Oct-2014.) $)
  congtr $p |- ( ( ( A e. ZZ /\ B e. ZZ ) /\ ( C e. ZZ /\ D e. ZZ ) /\ ( A || (
      B - C ) /\ A || ( C - D ) ) ) -> A || ( B - D ) ) $=
    ( cz wcel wa co cdvds wbr w3a caddc simp1l simp1r simp2l 3ad2ant2 cc adantl
    cmin zcn zsubcld zsubcl simp3 dvds2add imp syl31anc 3ad2ant1 adantr npncand
    breqtrd ) AEFZBEFZGZCEFZDEFZGZABCSHZIJACDSHZIJGZKZAUQURLHZBDSHIUTUKUQEFZURE
    FZUSAVAIJZUKULUPUSMUTBCUKULUPUSNUMUNUOUSOUAUPUMVCUSCDUBPUMUPUSUCUKVBVCKUSVD
    AUQURUDUEUFUTBCDUMUPBQFZUSULVEUKBTRUGUPUMCQFZUSUNVFUOCTUHPUPUMDQFZUSUOVGUND
    TRPUIUJ $.

  $( If two pairs of numbers are componentwise congruent, so are their sums.
     (Contributed by Stefan O'Rear, 1-Oct-2014.) $)
  congadd $p |- ( ( ( A e. ZZ /\ B e. ZZ /\ C e. ZZ ) /\ ( D e. ZZ /\ E e. ZZ )
      /\ ( A || ( B - C ) /\ A || ( D - E ) ) ) -> A || ( ( B + D ) - ( C + E )
      ) ) $=
    ( cz wcel w3a wa cmin co cdvds wbr caddc wi simpl1 zsubcl zcnd cc zcn wceq
    3adant1 adantr dvds2add syl3anc ad2antrl ad2antll addsub4d 3adant3 breqtrrd
    adantl 3impia simpl2 simpl3 ) AFGZBFGZCFGZHZDFGZEFGZIZABCJKZLMADEJKZLMIZHAV
    BVCNKZBDNKCENKJKZLURVAVDAVELMZURVAIZUOVBFGZVCFGZVDVGOUOUPUQVAPURVIVAUPUQVIU
    OBCQUBUCVAVJURDEQUKAVBVCUDUEULURVAVFVEUAVDVHBDCEVHBUOUPUQVAUMRUSDSGURUTDTUF
    VHCUOUPUQVAUNRUTESGURUSETUGUHUIUJ $.

  $( If two pairs of numbers are componentwise congruent, so are their
     products.  (Contributed by Stefan O'Rear, 1-Oct-2014.) $)
  congmul $p |- ( ( ( A e. ZZ /\ B e. ZZ /\ C e. ZZ ) /\ ( D e. ZZ /\ E e. ZZ )
      /\ ( A || ( B - C ) /\ A || ( D - E ) ) ) -> A || ( ( B x. D ) - ( C x. E
      ) ) ) $=
    ( cz wcel w3a wa cmin co cdvds wbr cmul zmulcld wi 3ad2ant2 syl3anc cc zcn
    simp11 simp12 simp2l simp2r simp13 simp3r zsubcl dvdsmultr2 3ad2ant1 adantr
    mpd adantl subdid breqtrd simp3l zsubcld dvdsmultr1 3ad2ant3 subdird congtr
    syl222anc ) AFGZBFGZCFGZHZDFGZEFGZIZABCJKZLMZADEJKZLMZIZHZVBBDNKZFGBENKZFGC
    ENKZFGAVOVPJKZLMAVPVQJKZLMAVOVQJKLMVBVCVDVHVMUAZVNBDVBVCVDVHVMUBZVEVFVGVMUC
    OVNBEWAVEVFVGVMUDZOVNCEVBVCVDVHVMUEZWBOVNABVKNKZVRLVNVLAWDLMZVEVHVJVLUFVNVB
    VCVKFGZVLWEPVTWAVHVEWFVMDEUGQABVKUHRUKVNBDEVEVHBSGZVMVCVBWGVDBTQUIZVHVEDSGZ
    VMVFWIVGDTUJQVHVEESGZVMVGWJVFETULQZUMUNVNAVIENKZVSLVNVJAWLLMZVEVHVJVLUOVNVB
    VIFGVGVJWMPVTVNBCWAWCUPWBAVIEUQRUKVNBCEWHVEVHCSGZVMVDVBWNVCCTURUIWKUSUNAVOV
    PVQUTVA $.

  $( Congruence mod ` A ` is a symmetric/commutative relation.  (Contributed by
     Stefan O'Rear, 1-Oct-2014.) $)
  congsym $p |- ( ( ( A e. ZZ /\ B e. ZZ ) /\ ( C e. ZZ /\ A || ( B - C ) ) )
      -> A || ( C - B ) ) $=
    ( cz wcel wa cmin co cdvds wbr cneg simprr zcn ad2antrl ad2antlr negsubdi2d
    cc breqtrrd wb simpll simprl simplr zsubcld dvdsnegb syl2anc mpbird ) ADEZB
    DEZFZCDEZABCGHZIJZFZFZACBGHZIJZAUOKZIJZUNAUKUQIUIUJULLUNCBUJCQEUIULCMNUHBQE
    UGUMBMOPRUNUGUODEUPURSUGUHUMTUNCBUIUJULUAUGUHUMUBUCAUOUDUEUF $.

  $( If two integers are congruent mod ` A ` , so are their negatives.
     (Contributed by Stefan O'Rear, 1-Oct-2014.) $)
  congneg $p |- ( ( ( A e. ZZ /\ B e. ZZ ) /\ ( C e. ZZ /\ A || ( B - C ) ) )
      -> A || ( -u B - -u C ) ) $=
    ( cz wcel wa cmin co cdvds wbr cneg congsym cc zcn neg2sub syl2an ad2ant2lr
    wceq breqtrrd ) ADEZBDEZFCDEZABCGHIJZFFACBGHZBKCKGHZIABCLUAUBUEUDRZTUCUABME
    CMEUFUBBNCNBCOPQS $.

  $( If two pairs of numbers are componentwise congruent, so are their
     differences.  (Contributed by Stefan O'Rear, 2-Oct-2014.) $)
  congsub $p |- ( ( ( A e. ZZ /\ B e. ZZ /\ C e. ZZ ) /\ ( D e. ZZ /\ E e. ZZ )
      /\ ( A || ( B - C ) /\ A || ( D - E ) ) ) -> A || ( ( B - D ) - ( C - E )
      ) ) $=
    ( cz wcel w3a wa cmin co cdvds wbr cneg caddc simp11 simp12 znegcld negsubd
    zcnd simp13 simp2l simp2r simp3l congneg syl22anc congadd syl322anc oveq12d
    simp3r breqtrd ) AFGZBFGZCFGZHZDFGZEFGZIZABCJKLMZADEJKLMZIZHZABDNZOKZCENZOK
    ZJKZBDJKZCEJKZJKLVBULUMUNVCFGVEFGUSAVCVEJKLMZAVGLMULUMUNURVAPZULUMUNURVAQZU
    LUMUNURVAUAZVBDUOUPUQVAUBZRVBEUOUPUQVAUCZRUOURUSUTUDVBULUPUQUTVJVKVNVOUOURU
    SUTUJADEUEUFABCVCVEUGUHVBVDVHVFVIJVBBDVBBVLTVBDVNTSVBCEVBCVMTVBEVOTSUIUK $.

  $( Every integer is congruent to itself mod every base.  (Contributed by
     Stefan O'Rear, 1-Oct-2014.) $)
  congid $p |- ( ( A e. ZZ /\ B e. ZZ ) -> A || ( B - B ) ) $=
    ( cz wcel wa cc0 cmin co cdvds wbr dvds0 adantr zcn adantl subidd breqtrrd
    cc ) ACDZBCDZEZAFBBGHIRAFIJSAKLTBSBQDRBMNOP $.

  ${
    $d F a b c $.  $d X a b c k $.  $d V a b c k $.  $d Y a b c k $.
    $d N a b c k $.

    $( Polynomials commute with congruences.  (Does this characterize them?)
       (Contributed by Stefan O'Rear, 5-Oct-2014.) $)
    mzpcong $p |- ( ( F e. ( mzPoly ` V ) /\ ( X e. ( ZZ ^m V ) /\ Y e. ( ZZ ^m
        V ) ) /\ ( N e. ZZ /\ A. k e. V N || ( ( X ` k ) - ( Y ` k ) ) ) ) -> N
        || ( ( F ` X ) - ( F ` Y ) ) ) $=
      ( vc cfv wcel cz co wa cmin cdvds wbr cvv wceq oveq12d breq2d fveq1 va vb
      cmzp cmap cv wral w3a elfvex 3anim1i simp1 csn cxp cmpt caddc cof simpl3l
      cmul congid syl2anc simpl2l vex fvconst2 syl simpl2r breqtrrd simpl3r weq
      simpr fveq2 rspcva eqid fvmpt wf simp13l simp2l simp12l ffvelcdmd simp12r
      fvex simp3l simp2r simp3r congadd syl322anc wfn ffnd ovexd fnfvof congmul
      syl22anc mzpindd ) BDUCHIZEJDUDKZIZFWMIZLZCJIZCAUEZEHZWRFHZMKZNOZADUFZLZU
      GDPIZWPXDUGZWLCEBHZFBHZMKZNOZWLXEWPXDBDUCUHUIWLWPXDUJXFCEUAUEZHZFXKHZMKZN
      OCEWMUBUEZUKULZHZFXPHZMKZNOCEGWMXOGUEZHZUMZHZFYBHZMKZNOCEXOHZFXOHZMKZNOZC
      EXTHZFXTHZMKZNOZCEXOXTUNUOKZHZFYNHZMKZNOCEXOXTUQUOKZHZFYRHZMKZNOXJUABUBGD
      XFXOJIZLZCXOXOMKZXSNUUCWQUUBCUUDNOWQXCXEWPUUBUPXFUUBVHCXOURUSUUCXQXOXRXOM
      UUCWNXQXOQWNWOXEXDUUBUTWMXOEUBVAZVBVCUUCWOXRXOQWNWOXEXDUUBVDWMXOFUUEVBVCR
      VEXFXODIZLZCXOEHZXOFHZMKZYENUUGUUFXCCUUJNOZXFUUFVHWQXCXEWPUUFVFXBUUKAXODA
      UBVGZXAUUJCNUULWSUUHWTUUIMWRXOEVIWRXOFVIRSVJUSUUGYCUUHYDUUIMUUGWNYCUUHQWN
      WOXEXDUUFUTGEYAUUHWMYBXOXTETYBVKZXOEVSVLVCUUGWOYDUUIQWNWOXEXDUUFVDGFYAUUI
      WMYBXOXTFTUUMXOFVSVLVCRVEXFWMJXOVMZYILZWMJXTVMZYMLZUGZCYFYJUNKZYGYKUNKZMK
      ZYQNUURWQYFJIZYGJIZYJJIZYKJIZYIYMCUVANOWQXCXEWPUUOUUQVNZUURWMJEXOXFUUNYIU
      UQVOZWNWOXEXDUUOUUQVPZVQZUURWMJFXOUVGWNWOXEXDUUOUUQVRZVQZUURWMJEXTXFUUOUU
      PYMVTZUVHVQZUURWMJFXTUVLUVJVQZXFUUNYIUUQWAZXFUUOUUPYMWBZCYFYGYJYKWCWDUURY
      OUUSYPUUTMUURXOWMWEZXTWMWEZWMPIZWNYOUUSQUURWMJXOUVGWFZUURWMJXTUVLWFZUURJD
      UDWGZUVHWMUNXOXTPEWHWJUURUVQUVRUVSWOYPUUTQUVTUWAUWBUVJWMUNXOXTPFWHWJRVEUU
      RCYFYJUQKZYGYKUQKZMKZUUANUURWQUVBUVCUVDUVEYIYMCUWENOUVFUVIUVKUVMUVNUVOUVP
      CYFYGYJYKWIWDUURYSUWCYTUWDMUURUVQUVRUVSWNYSUWCQUVTUWAUWBUVHWMUQXOXTPEWHWJ
      UURUVQUVRUVSWOYTUWDQUVTUWAUWBUVJWMUQXOXTPFWHWJRVEXKXPQZXNXSCNUWFXLXQXMXRM
      EXKXPTFXKXPTRSXKYBQZXNYECNUWGXLYCXMYDMEXKYBTFXKYBTRSUAUBVGZXNYHCNUWHXLYFX
      MYGMEXKXOTFXKXOTRSUAGVGZXNYLCNUWIXLYJXMYKMEXKXTTFXKXTTRSXKYNQZXNYQCNUWJXL
      YOXMYPMEXKYNTFXKYNTRSXKYRQZXNUUACNUWKXLYSXMYTMEXKYRTFXKYRTRSXKBQZXNXICNUW
      LXLXGXMXHMEXKBTFXKBTRSWKUS $.
  $}

  ${
    $d A a $.  $d N a $.
    $( Every integer is congruent to some number in the fundamental domain.
       (Contributed by Stefan O'Rear, 2-Oct-2014.) $)
    congrep $p |- ( ( A e. NN /\ N e. ZZ ) -> E. a e. ( 0 ... ( A - 1 ) ) A ||
        ( a - N ) ) $=
      ( cn wcel cz wa cmo co cc0 c1 cmin cfz cdvds cv wrex zmodfz ancoms adantr
      wbr nnz simpr cn0 zmodcl nn0zd cdiv cr crp zre nnrp moddifz syl2anr nnne0
      wne wb zsubcld dvdsval2 syl3anc mpbird congsym syl22anc wceq oveq1 breq2d
      rspcev syl2anc ) ADEZBFEZGZBAHIZJAKLIMIZEZAVJBLIZNTZACOZBLIZNTZCVKPVHVGVL
      BAQRVIAFEZVHVJFEABVJLIZNTZVNVGVRVHAUASZVGVHUBZVIVJVHVGVJUCEBAUDRUEZVIVTVS
      AUFIFEZVHBUGEAUHEWDVGBUIAUJBAUKULVIVRAJUNZVSFEVTWDUOWAVGWEVHAUMSVIBVJWBWC
      UPAVSUQURUSABVJUTVAVQVNCVJVKVOVJVBVPVMANVOVJBLVCVDVEVF $.
  $}

  $( If two integers are congruent, they are either equal or separated by at
     least the congruence base.  (Contributed by Stefan O'Rear, 4-Oct-2014.) $)
  congabseq $p |- ( ( ( A e. NN /\ B e. ZZ /\ C e. ZZ ) /\ A || ( B - C ) ) ->
      ( ( abs ` ( B - C ) ) < A <-> B = C ) ) $=
    ( wcel cz w3a cmin co wbr wa clt wceq cc zcn ad2antrr cr 3ad2ant1 ad3antrrr
    cc0 adantr cn cdvds cabs cfv 3ad2ant2 3ad2ant3 cle wn zsubcl 3adant1 abscld
    zcnd nnre ltnled biimpa wne nnz 3jca simpllr dvdsleabs sylc ex necon1bd mpd
    simpr subeq0d oveq1 adantl subidd eqtrd abs00bd nngt0 eqbrtrd impbida ) AUA
    DZBEDZCEDZFZABCGHZUBIZJZVSUCUDZAKIZBCLZWAWCJZBCVRBMDZVTWCVPVOWFVQBNUEOVRCMD
    ZVTWCVQVOWGVPCNUFZOWEAWBUGIZUHZVSSLWAWCWJWAWBAVRWBPDVTVRVSVRVSVPVQVSEDZVOBC
    UIUJZULUKTVRAPDZVTVOVPWMVQAUMQTUNUOWEWIVSSWEVSSUPZWIWEWNJZAEDZWKWNFVTWIWOWP
    WKWNVRWPVTWCWNVOVPWPVQAUQQRVRWKVTWCWNWLRWEWNVEURVRVTWCWNUSAVSUTVAVBVCVDVFWA
    WDJZWBSAKWQVSWQVSCCGHZSWDVSWRLWABCCGVGVHWQCVRWGVTWDWHOVIVJVKVRSAKIZVTWDVOVP
    WSVQAVLQOVMVN $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Alternating congruential equations
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( A wff like that in this theorem will be known as an "alternating
     congruence".  A special symbol might be considered if more uses come up.
     They have many of the same properties as normal congruences, starting with
     reflexivity.

     JonesMatijasevic uses "a &#8801; &#xB1; b (mod c)" for this construction.
     The disjunction of divisibility constraints seems to adequately capture
     the concept, but it's rather verbose and somewhat inelegant.  Use of an
     explicit equivalence relation might also work.  (Contributed by Stefan
     O'Rear, 2-Oct-2014.) $)
  acongid $p |- ( ( A e. ZZ /\ B e. ZZ ) -> ( A || ( B - B ) \/ A || ( B - -u B
      ) ) ) $=
    ( cz wcel wa cmin co cdvds wbr cneg congid orcd ) ACDBCDEABBFGHIABBJFGHIABK
    L $.

  $( Symmetry of alternating congruence.  (Contributed by Stefan O'Rear,
     2-Oct-2014.) $)
  acongsym $p |- ( ( ( A e. ZZ /\ B e. ZZ /\ C e. ZZ ) /\
          ( A || ( B - C ) \/ A || ( B - -u C ) ) ) -> ( A || ( C - B ) \/ A ||
      ( C - -u B ) ) ) $=
    ( cz wcel w3a cmin co cdvds wbr cneg wo wi wa congsym exp32 3impia 3ad2ant2
    cc zcn negnegd oveq1d negcld 3ad2ant3 neg2subd eqtr3d breq2d biimpd orim12d
    imp ) ADEZBDEZCDEZFZABCGHIJZABCKZGHZIJZLACBGHIJZACBKZGHZIJZLUNUOUSURVBUKULU
    MUOUSMUKULNUMUOUSABCOPQUNURVBUNUQVAAIUNUTKZUPGHUQVAUNVCBUPGUNBULUKBSEUMBTZR
    UAUBUNUTCULUKUTSEUMULBVDUCRUMUKCSEULCTUDUEUFUGUHUIUJ $.

  $( Negate right side of alternating congruence.  Makes essential use of the
     "alternating" part.  (Contributed by Stefan O'Rear, 3-Oct-2014.) $)
  acongneg2 $p |- ( ( ( A e. ZZ /\ B e. ZZ /\ C e. ZZ ) /\
          ( A || ( B - -u C ) \/ A || ( B - -u -u C ) ) ) -> ( A || ( B - C )
      \/ A || ( B - -u C ) ) ) $=
    ( cz wcel w3a cneg co cdvds wbr wo wa cc zcn 3ad2ant3 negnegd oveq2d breq2d
    cmin biimpd orim2d imp orcomd ) ADEZBDEZCDEZFZABCGZSHIJZABUHGZSHZIJZKZLUIAB
    CSHZIJZUGUMUIUOKUGULUOUIUGULUOUGUKUNAIUGUJCBSUGCUFUDCMEUECNOPQRTUAUBUC $.

  $( Transitivity of alternating congruence.  (Contributed by Stefan O'Rear,
     2-Oct-2014.) $)
  acongtr $p |- ( ( ( A e. ZZ /\ B e. ZZ ) /\ ( C e. ZZ /\ D e. ZZ ) /\
          ( ( A || ( B - C ) \/ A || ( B - -u C ) ) /\ ( A || ( C - D ) \/ A ||
      ( C - -u D ) ) ) ) -> ( A || ( B - D ) \/ A || ( B - -u D ) ) ) $=
    ( cz wcel wa cmin co cdvds wbr wo congtr ex simpll ad2antlr simpr cc adantl
    cneg 3expa orcd znegcl anim12i simplll simplrl simplrr congsym syl22anc zcn
    wceq adantr neg2subd eqcomd breq2d sylibd anim2d syl3anc olcd anim2i anim1i
    imp simpl an42s syl12anc negnegd oveq2d syl eqtr3d ccased 3impia ) AEFZBEFZ
    GZCEFZDEFZGZABCHIJKZABCTZHIJKZLACDHIJKZACDTZHIJKZLGABDHIJKZABWBHIJKZLZVNVQG
    ZVRWAVTWCWFWGVRWAGZWFWGWHGWDWEVNVQWHWDABCDMUAUBNWGVTWAGZWFWGWIGZWEWDWJVNVSE
    FZWBEFZGZVTAVSWBHIZJKZGZWEVNVQWIOVQWMVNWIVOWKVPWLCUCZDUCZUDZPWGWIWPWGWAWOVT
    WGWAADCHIZJKZWOWGWAXAWGWAGVLVOVPWAXAVLVMVQWAUEVNVOVPWAUFVNVOVPWAUGWGWAQACDU
    HUINWGWTWNAJWGWNWTVQWNWTUKVNVQCDVOCRFVPCUJULZVPDRFVODUJSZUMSUNUOUPUQVBABVSW
    BMURUSNWGVRWCGZWFWGXDGZWEWDXEVNVOWLGZXDWEVNVQXDOVQXFVNXDVPWLVOWRUTPWGXDQABC
    WBMURUSNWGVTWCGZWFWGXGGZWDWEXHVNWKVPGZVTAVSDHIZJKZGZWDVNVQXGOVQXIVNXGVOWKVP
    WQVAPWGXGXLWGWCXKVTWGWCAWBCHIZJKZXKWGWCXNWGWCGVLVOGZWLWCXNWGXOWCVLVPVMVOXOV
    LVPGVLVMVOGVOVLVPVCVMVOQUDVDULVQWLVNWCVPWLVOWRSPWGWCQACWBUHVENWGXMXJAJVQXMX
    JUKVNVQWBVSTZHIXMXJVQXPCWBHVQCXBVFVGVQDVSXCVQWMVSRFZWSWKXQWLVSUJULVHUMVISUO
    UPUQVBABVSDMURUBNVJVK $.

  ${
    acongeq12d.1 $e |- ( ph -> B = C ) $.
    acongeq12d.2 $e |- ( ph -> D = E ) $.
    $( Substitution deduction for alternating congruence.  (Contributed by
       Stefan O'Rear, 3-Oct-2014.) $)
    acongeq12d $p |- ( ph -> ( ( A || ( B - D ) \/ A || ( B - -u D ) ) <-> ( A
        || ( C - E ) \/ A || ( C - -u E ) ) ) ) $=
      ( cmin co cdvds wbr cneg oveq12d breq2d negeqd orbi12d ) ABCEIJZKLBDFIJZK
      LBCEMZIJZKLBDFMZIJZKLARSBKACDEFIGHNOAUAUCBKACDTUBIGAEFHPNOQ $.
  $}

  ${
    $d A a b $.  $d N a b $.
    $( Every integer is alternating-congruent to some number in the first half
       of the fundamental domain.  (Contributed by Stefan O'Rear,
       2-Oct-2014.) $)
    acongrep $p |- ( ( A e. NN /\ N e. ZZ ) -> E. a e. ( 0 ... A ) ( ( 2 x. A )
        || ( a - N ) \/ ( 2 x. A ) || ( a - -u N ) ) ) $=
      ( vb cn wcel cz wa c2 co cdvds wbr wo cc0 sylancr syl2anc cr cle 3ad2ant1
      cmin cmul cv cneg cfz c1 2nn simpl nnmulcl simpr congrep elfzelz ad2antrl
      wrex zred nnre ad2antrr elfzle1 anim1i 0zd nnz elfz syl3anc adantr mpbird
      wb simplrr orcd weq id acongeq12d rspcev simplll simplrl w3a 3ad2ant2 2re
      eqidd remulcl 2z zmulcl simp2 elfzm11 biimpa syl21anc simp3d subge0d wceq
      clt ltled nncn caddc 2times oveq1d pncan2 anidms eqtrd syl eqbrtrd subled
      cc simp3 jca zsubcld simplr simprr congsym syl22anc dvdsadd zcnd ad2antlr
      mpbid zcn subnegd recnd subadd23d breqtrrd olcd lecasei rexlimddv ) AEFZB
      GFZHZIAUAJZDUBZBTJKLZYCCUBZBTJKLYCYFBUCZTJKLMZCNAUDJZUMZDNYCUETJZUDJZYBYC
      EFZYAYEDYLUMYBIEFXTYMUFXTYAUGIAUHOXTYAUIYCBDUJPYBYDYLFZYEHZHZYJYDAYNYDQFZ
      YBYEYNYDYDNYKUKZUNZULZXTAQFZYAYOAUOZUPYPYDARLZHZYDYIFZYEYCYDYGTJKLZMZYJUU
      DUUENYDRLZUUCHZYPUUHUUCYNUUHYBYEYDNYKUQULURYPUUEUUIVEZUUCYPYDGFZNGFZAGFZU
      UJYNUUKYBYEYRULZYPUSZXTUUMYAYOAUTZUPZYDNAVAVBVCVDUUDYEUUFYBYNYEUUCVFVGYHU
      UGCYDYICDVHZYCYFYDBBUURVIUURBVQVJVKPYPAYDRLZHZYCYDTJZYIFZYCUVABTJKLZYCUVA
      YGTJZKLZMZYJUUTUVBNUVARLZUVAARLZHZUUTXTYNUUSUVIXTYAYOUUSVLYBYNYEUUSVMYPUU
      SUIXTYNUUSVNZUVGUVHUVJUVGYDYCRLUVJYDYCYNXTYQUUSYSVOZXTYNYCQFZUUSXTIQFUUAU
      VLVPUUBIAVROSZUVJUUKUUHYDYCWHLZUVJUULYCGFZYNUUKUUHUVNVNZUVJUSXTYNUVOUUSXT
      IGFZUUMUVOVSUUPIAVTZOSXTYNUUSWAUULUVOHYNUVPYDNYCWBWCWDWEWIUVJYCYDUVMUVKWF
      VDUVJYCAYDUVMXTYNUUAUUSUUBSUVKUVJYCATJZAYDRXTYNUVSAWGZUUSXTAWTFZUVTAWJUWA
      UVSAAWKJZATJZAUWAYCUWBATAWLWMUWAUWCAWGAAWNWOWPWQSXTYNUUSXAWRWSXBVBYPUVBUV
      IVEZUUSYPUVAGFUULUUMUWDYPYCYDYPUVQUUMUVOVSUUQUVROZUUNXCZUUOUUQUVANAVAVBVC
      VDUUTUVEUVCYPUVEUUSYPYCYCBYDTJZWKJZUVDKYPYCUWGKLZYCUWHKLZYPUVOUUKYAYEUWIU
      WEUUNXTYAYOXDZYBYNYEXEYCYDBXFXGYPUVOUWGGFUWIUWJVEUWEYPBYDUWKUUNXCYCUWGXHP
      XKYPUVDUVABWKJUWHYPUVABYPUVAUWFXIYABWTFXTYOBXLXJZXMYPYCYDBYPYCUWEXIYPYDYT
      XNUWLXOWPXPVCXQYHUVFCUVAYIYFUVAWGZYCYFUVABBUWMVIUWMBVQVJVKPXRXS $.
  $}

  $( Bound on the difference between two integers constrained to two possibly
     overlapping finite ranges.  (Contributed by Stefan O'Rear, 4-Oct-2014.) $)
  fzmaxdif $p |- ( ( ( C e. ZZ /\ A e. ( B ... C ) ) /\ ( F e. ZZ /\ D e. ( E
      ... F ) ) /\ ( C - E ) <_ ( F - B ) ) -> ( abs ` ( A - D ) ) <_ ( F - B )
      ) $=
    ( cz wcel cfz co wa cmin cle wbr caddc zred syl resubcld recnd letrd simp2r
    w3a cabs cfv elfzelzd simp2l simp1r elfzel1 elfzle2 lesub1dd nncand breqtrd
    elfzle1 readdcld lesub2dd simp3 lesubaddd mpbid addcomd absdifled mpbir2and
    simp1l ) CGHZABCIJHZKZFGHZDEFIJHZKZCELJZFBLJZMNZUBZADLJUCUDVJMNDVJLJZAMNADV
    JOJZMNVLVMBAVLDVJVLDVLDEFVEVFVGVKUAZUEPZVLFBVLFVEVFVGVKUFPZVLBVLVDBGHVCVDVH
    VKUGZABCUHQPZRZRVSVLAVLABCVRUEPZVLVMFVJLJBMVLDFVJVPVQVTVLVGDFMNVODEFUIQUJVL
    FBVLFVQSVLBVSSUKULVLVDBAMNVRABCUMQTVLACVNWAVLCVCVDVHVKVBPZVLDVJVPVTUNVLVDAC
    MNVRABCUIQVLCVJDOJZVNMVLCDLJZVJMNCWCMNVLWDVIVJVLCDWBVPRVLCEWBVLEVLVGEGHVODE
    FUHQPZRVTVLEDCWEVPWBVLVGEDMNVODEFUMQUOVEVHVKUPTVLCDVJWBVPVTUQURVLVJDVLVJVTS
    VLDVPSUSULTVLADVJWAVPVTUTVA $.

  $( Reflection of a finite range of integers about 0.  (Contributed by Stefan
     O'Rear, 4-Oct-2014.) $)
  fzneg $p |- ( ( A e. ZZ /\ B e. ZZ /\ C e. ZZ ) -> ( A e. ( B ... C ) <-> -u
      A e. ( -u C ... -u B ) ) ) $=
    ( cz wcel w3a cle wbr wa cneg cfz co ancom cr 3ad2ant1 3ad2ant3 lenegd elfz
    zre znegcl 3ad2ant2 anbi12d bitrid wb syl3an 3com23 3bitr4d ) ADEZBDEZCDEZF
    ZBAGHZACGHZIZCJZAJZGHZUPBJZGHZIZABCKLEUPUOURKLEZUNUMULIUKUTULUMMUKUMUQULUSU
    KACUHUIANEUJASOZUJUHCNEUICSPQUKBAUIUHBNEUJBSUAVBQUBUCABCRUHUJUIVAUTUDZUHUPD
    EUJUODEUIURDEVCATCTBTUPUOURRUEUFUG $.

  $( Two numbers in the fundamental domain are alternating-congruent iff they
     are equal.  TODO: could be used to shorten ~ jm2.26 .  (Contributed by
     Stefan O'Rear, 4-Oct-2014.) $)
  acongeq $p |- ( ( A e. NN /\ B e. ( 0 ... A ) /\ C e. ( 0 ... A ) ) -> ( B =
      C <-> ( ( 2 x. A ) || ( B - C ) \/ ( 2 x. A ) || ( B - -u C ) ) ) ) $=
    ( wcel cc0 co wceq c2 cmin cdvds wbr wa cz clt cr cle caddc wb c1 ad2antrr
    cn cfz w3a cmul cneg wo nnz 3ad2ant1 zmulcl sylancr elfzelz 3ad2ant2 congid
    2z syl2anc adantr adantl breqtrd orcd cabs cfv 3ad2ant3 zsubcld zcnd abscld
    oveq2 nnre 0re resubcl sylancl remulcl simp2 simp3 leidd fzmaxdif syl221anc
    2re crp nnrp ltaddrpd subid1d 2timesd 3brtr4d lelttrd simpl1 nnmulcl simpl2
    recnd 2nn elfzelzd simpl3 simpr congabseq syl31anc simpll2 elfzle1 syl zred
    mpbid renegcld resubcld 1re znegcld abssubd 0zd 1z zsubcl fzneg syl3anc a1i
    neg0 oveq2d eleqtrd cn0 simp1 nnm1nn0 nn0ge0d 1cnd addsubassd oveq1d ax-1cn
    0m0e0 cc subcl subnegd 3eqtr4rd eqbrtrd ltm1d simplr le0neg1d mpbird letri3
    mpbir2and negeqd eqtrd 3eqtr4d fveq2d eqbrtrrd ppncand eqtr4d addcomd nnnn0
    breqtrrd dvdsadd cuz nn0uz eleqtrdi fzm1 biimpa mpjaodan jaodan impbida ) A
    UADZBEAUBFZDZCUUNDZUCZBCGZHAUDFZBCIFZJKZUUSBCUEZIFZJKZUFUUQUURLZUVAUVDUVEUU
    SBBIFZUUTJUUQUUSUVFJKZUURUUQUUSMDZBMDZUVGUUQHMDAMDZUVHUNUUMUUOUVJUUPAUGUHZH
    AUIUJZUUOUUMUVIUUPBEAUKULZUUSBUMUOUPUURUVFUUTGUUQBCBIVFUQURUSUUQUVAUURUVDUU
    QUVALZUUTUTVAZUUSNKZUURUUQUVPUVAUUQUVOAEIFZUUSUUQUUTUUQUUTUUQBCUVMUUPUUMCMD
    ZUUOCEAUKVBZVCVDVEUUQAODZEODZUVQODUUMUUOUVTUUPAVGUHZVHAEVIVJZUUQHODUVTUUSOD
    ZVQUWBHAVKUJZUUQUVJUUOUVJUUPUVQUVQPKUVOUVQPKUVKUUMUUOUUPVLUVKUUMUUOUUPVMZUU
    QUVQUWCVNBEACEAVOVPUUQAAAQFZUVQUUSNUUQAAUWBUUMUUOAVRDUUPAVSUHVTUUQAUUQAUWBW
    HZWAUUQAUWHWBZWCWDZUPUVNUUSUADZUVIUVRUVAUVPUURRUVNHUADZUUMUWKWIUUMUUOUUPUVA
    WEHAWFZUJUVNBEAUUMUUOUUPUVAWGWJUVNCEAUUMUUOUUPUVAWKWJUUQUVAWLUUSBCWMWNWSUUQ
    UVDLZCEASIFZUBFDZUURCAGZUWNUWPLZUVBEBCUWRUVBEUEZEUWRCEUWRCEGZCEPKZECPKZUWRU
    XAEUVBPKUWREBUVBPUWRUUOEBPKUUMUUOUUPUVDUWPWOZBEAWPWQUWRUVCUTVAZUUSNKZBUVBGZ
    UWRUXDAUWOUEZIFZUUSUUQUXDODUVDUWPUUQUVCUUQUVCUUQBUVBUUQBUVMWRUUQCUUQCUVSWRW
    TXAWHVETUUQUXHODUVDUWPUUQAUXGUWBUUQUWOUUQUVTSODUWOODUWBXBASVIVJWTXATUUQUWDU
    VDUWPUWETUWRUXDUVBBIFUTVAZUXHPUWRBUVBUWRBUUQUVIUVDUWPUVMTZVDUWRUVBUUQUVBMDZ
    UVDUWPUUQCUVSXCTZVDXDUWREMDZUVBUXGEUBFZDUVJUUOEEIFZUXHPKZUXIUXHPKUWRXEUWRUV
    BUXGUWSUBFZUXNUWRUWPUVBUXQDZUWNUWPWLUUQUWPUXRRZUVDUWPUUQUVRUXMUWOMDZUXSUVSU
    UQXEUUQUVJSMDUXTUVKXFASXGVJCEUWOXHXITWSUWRUWSEUXGUBUWSEGUWRXKXJZXLXMUUQUVJU
    VDUWPUVKTUXCUUQUXPUVDUWPUUQEUUSSIFZUXOUXHPUUQUYBUUQUWKUYBXNDUUQUWLUUMUWKWIU
    UMUUOUUPXOUWMUJZUUSXPWQXQUXOEGUUQYBXJUUQUWGSIFAUWOQFUYBUXHUUQAASUWHUWHUUQXR
    XSUUQUUSUWGSIUWIXTUUQAUWOUWHUUQAYCDSYCDUWOYCDUWHYAASYDVJYEYFZWCTUVBUXGEBEAV
    OVPYGUUQUXHUUSNKUVDUWPUUQUXHUYBUUSNUYDUUQUUSUWEYHYGTWDUWRUWKUVIUXKUVDUXEUXF
    RUUQUWKUVDUWPUYCTUXJUXLUUQUVDUWPYIUUSBUVBWMWNWSZURUWRCUWPCODZUWNUWPCCEUWOUK
    WRUQZYJYKUWPUXBUWNCEUWOWPUQUWRUYFUWAUWTUXAUXBLRUYGVHCEYLVJYMZYNUYAYOUYEUYHY
    PUWNUWQLZBACUYIBAIFZUTVAZUUSNKZBAGZUYIUVOUYKUUSNUYIUUTUYJUTUWQUUTUYJGUWNCAB
    IVFUQYQUUQUVPUVDUWQUWJTYRUYIUWKUVIUVJUUSUYJJKZUYLUYMRUUQUWKUVDUWQUYCTUUQUVI
    UVDUWQUVMTUUQUVJUVDUWQUVKTUYIUYNUUSUUSUYJQFZJKZUYIUUSUVCUYOJUUQUVDUWQYIUYIU
    WGUYJQFZBCQFZUYOUVCUYIUYQBAQFZUYRUUQUYQUYSGUVDUWQUUQUYQABQFUYSUUQAABUWHUWHU
    UQBUVMVDZYSUUQABUWHUYTUUAYOTUWQUYRUYSGUWNCABQVFUQYTUUQUYOUYQGUVDUWQUUQUUSUW
    GUYJQUWIXTTUUQUVCUYRGUVDUWQUUQBCUYTUUQCUVSVDYETYPUUCUYIUVHUYJMDZUYNUYPRUUQU
    VHUVDUWQUVLTUUQVUAUVDUWQUUQBAUVMUVKVCTUUSUYJUUDUOYKUUSBAWMWNWSUWNUWQWLYTUUQ
    UWPUWQUFZUVDUUQAEUUEVAZDZUUPVUBUUQAXNVUCUUMUUOAXNDUUPAUUBUHUUFUUGUWFVUDUUPV
    UBCEAUUHUUIUOUPUUJUUKUUL $.

  $( Alternating congruence passes from a base to a dividing base.
     (Contributed by Stefan O'Rear, 4-Oct-2014.) $)
  dvdsacongtr $p |- ( ( ( A e. ZZ /\ B e. ZZ ) /\ ( C e. ZZ /\ D e. ZZ ) /\ ( D
      || A /\ ( A || ( B - C ) \/ A || ( B - -u C ) ) ) ) -> ( D || ( B - C )
      \/ D || ( B - -u C ) ) ) $=
    ( cz wcel wa cdvds wbr cmin co cneg ad2antrr simp-4l simplr zsubcld dvdstrd
    wo simpr ex simprr simprl znegcld orim12d expimpd 3impia ) AEFZBEFZGZCEFZDE
    FZGZDAHIZABCJKZHIZABCLZJKZHIZRZGDUNHIZDUQHIZRZUIULGZUMUSVBVCUMGZUOUTURVAVDU
    OUTVDUOGZDAUNVCUKUMUOUIUJUKUAZMUGUHULUMUONVEBCVCUHUMUOUGUHULOZMVCUJUMUOUIUJ
    UKUBZMPVCUMUOOVDUOSQTVDURVAVDURGZDAUQVCUKUMURVFMUGUHULUMURNVIBUPVCUHUMURVGM
    VICVCUJUMURVHMUCPVCUMUROVDURSQTUDUEUF $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Additional theorems on integer divisibility
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Multiplication by a coprime number does not affect divisibility.
     (Contributed by Stefan O'Rear, 23-Sep-2014.) $)
  coprmdvdsb $p |- ( ( K e. ZZ /\ N e. ZZ /\ ( M e. ZZ /\ ( K gcd M ) = 1 ) )
      -> ( K || N <-> K || ( M x. N ) ) ) $=
    ( cz wcel cgcd co c1 wceq wa w3a cdvds wbr wi simp1 simp3l simp2 dvdsmultr2
    cmul syl3anc simp3r coprmdvds mpan2d impbid ) ADEZCDEZBDEZABFGHIZJZKZACLMZA
    BCSGLMZUJUEUGUFUKULNUEUFUIOZUEUFUGUHPZUEUFUIQZABCRTUJULUHUKUEUFUGUHUAUJUEUG
    UFULUHJUKNUMUNUOABCUBTUCUD $.

  $( Divisibility in terms of modular reduction by the absolute value of the
     base.  (Contributed by Stefan O'Rear, 26-Sep-2014.) $)
  modabsdifz $p |- ( ( N e. RR /\ M e. RR /\ M =/= 0 ) -> ( ( N - ( N mod ( abs
      ` M ) ) ) / M ) e. ZZ ) $=
    ( cr wcel cc0 wne w3a cabs cfv cmo co cmin cz recnd syl absdivd wb redivcld
    cdiv absz crp simp1 simp2 simp3 absrpcld moddifz syl2anc wceq absidm oveq2d
    cc modcld resubcld abscld rpne0d 3eqtr4d eleq1d 3bitr4d mpbid ) BCDZACDZAEF
    ZGZBBAHIZJKZLKZVDSKZMDZVFASKZMDZVCUTVDUADVHUTVAVBUBZVCAVCAUTVAVBUCZNZUTVAVB
    UDZUEZBVDUFUGVCVGHIZMDZVIHIZMDZVHVJVCVPVRMVCVFHIZVDHIZSKVTVDSKVPVRVCWAVDVTS
    VCAUKDWAVDUHVMAUIOUJVCVFVDVCVFVCBVEVKVCBVDVKVOULUMZNZVCVDVCAVMUNZNVCVDVOUOZ
    PVCVFAWCVMVNPUPUQVCVGCDVHVQQVCVFVDWBWDWERVGTOVCVICDVJVSQVCVFAWBVLVNRVITOURU
    S $.

  $( Divisibility in terms of modular reduction by the absolute value of the
     base.  (Contributed by Stefan O'Rear, 24-Sep-2014.)  (Proof shortened by
     OpenAI, 3-Jul-2020.) $)
  dvdsabsmod0 $p |- ( ( M e. ZZ /\ N e. ZZ /\ M =/= 0 ) -> ( M || N <-> ( N mod
      ( abs ` M ) ) = 0 ) ) $=
    ( cz wcel cc0 wne cdvds wbr cabs cfv co wceq wb wa absdvdsb adantlr nnabscl
    cmo cn dvdsval3 sylan bitrd an32s 3impa ) ACDZBCDZAEFZABGHZBAIJZRKELZMZUEUG
    UFUKUEUGNZUFNUHUIBGHZUJUEUFUHUMMUGABOPULUISDUFUMUJMAQUIBTUAUBUCUD $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  X and Y sequences 3: Divisibility properties
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d A a b $.  $d K a b $.  $d N a b $.
    $( Theorem 2.18 of [JonesMatijasevic] p. 696.  Direct relationship of the
       exponential function to X and Y sequences.  (Contributed by Stefan
       O'Rear, 14-Oct-2014.) $)
    jm2.18 $p |- ( ( A e. ( ZZ>= ` 2 ) /\ K e. NN0 /\ N e. NN0 ) ->
        ( ( ( ( 2 x. A ) x. K ) - ( K ^ 2 ) ) - 1 ) ||
        ( ( ( A rmX N ) - ( ( A - K ) x. ( A rmY N ) ) ) - ( K ^ N ) ) ) $=
      ( wcel cmul co cexp cmin c1 crmx crmy cdvds wbr cz adantr oveq12d syl2anc
      cc0 wceq oveq2 va vb c2 cuz cfv cn0 wa cv wi caddc eluzelz zmulcl sylancr
      2z nn0z adantl zmulcld zsqcl zsubcld peano2zm dvds0 rmx0 rmy0 oveq2d zcnd
      mul01d eqtrd 1m0e1 eqtrdi cc nn0cn exp0d 1m1e0 breqtrrd rmx1 rmy1 mulridd
      syl nncand exp1d subidd pm3.43 simpll nnz frmx fovcl nn0zd frmy jca nnnn0
      cn zexpcl nnm1nn0 zaddcl w3a 3jca ad2antrr congid simpr congmul syl112anc
      adantrl simprl congsub zaddcld 0zd iddvds subid1d congadd syl322anc sqcld
      0z 1cnd addsubd npcand oveq1d eqtr3d ad2antlr expcld subdid mul12d expm1t
      eqtr4d 3eqtrrd congtr rmxluc rmyluc subcld 2cn mulcld 2cnd mulcomd 3eqtrd
      mulcl nn0cnd sub4d eqcomd expp1d breq2d imbi2d nncn npcan sylancl mulassd
      ax-1cn addlidd sqvald eqtr2d ex expcom a2d syl5 weq 2nn0ind impcom 3impa
      ) AUCUDUEZDZBUFDZCUFDZUCAEFZBEFZBUCGFZHFZIHFZACJFZABHFZACKFZEFZHFZBCGFZHF
      ZLMZUUTUURUUSUGZUVMUVNUVEAUAUHZJFZUVGAUVOKFZEFZHFZBUVOGFZHFZLMZUIUVNUVEAR
      JFZUVGARKFZEFZHFZBRGFZHFZLMZUIUVNUVEAIJFZUVGAIKFZEFZHFZBIGFZHFZLMZUIUVNUV
      EAUBUHZIHFZJFZUVGAUWRKFZEFZHFZBUWRGFZHFZLMZUIZUVNUVEAUWQJFZUVGAUWQKFZEFZH
      FZBUWQGFZHFZLMZUIZUVNUVEAUWQIUJFZJFZUVGAUXOKFZEFZHFZBUXOGFZHFZLMZUIZUVNUV
      MUIUAUBCUVNUVERUWHLUVNUVENDZUVERLMUVNUVDNDUYDUVNUVBUVCUVNUVABUVNUCNDANDZU
      VANDZUNUURUYEUUSUCAUKZOZUCAULUMZUUSBNDZUURBUOUPZUQZUVNUYJUVCNDZUYKBURVRZU
      SZUVDUTVRZUVEVAVRZUVNUWHIIHFRUVNUWFIUWGIHUVNUWFIRHFIUVNUWCIUWERHUURUWCISU
      USAVBOUVNUWEUVGREFRUVNUWDRUVGEUURUWDRSUUSAVCOVDUVNUVGUVNUVGUVNABUYHUYKUSZ
      VEZVFVGPVHVIUVNBUUSBVJDZUURBVKZUPZVLPVMVIVNUVNUVERUWOLUYQUVNUWOBBHFRUVNUW
      MBUWNBHUVNUWMAUVGHFBUVNUWJAUWLUVGHUURUWJASUUSAVOOUVNUWLUVGIEFUVGUVNUWKIUV
      GEUURUWKISUUSAVPOVDUVNUVGUYSVQVGPUVNABUVNAUYHVEVUBVSVGUVNBVUBVTPUVNBVUBWA
      VGVNUXFUXNUGUVNUXEUXMUGZUIUWQWKDZUYCUVNUXEUXMWBVUDUVNVUCUYBUVNVUDVUCUYBUI
      UVNVUDUGZVUCUYBVUEVUCUGZUVEUVAUXJEFZUXBHFZUXCRUVCUJFZEFZHFZUYALVUFUYDVUHN
      DZUGZUVAUXKEFZUXCHFZNDZVUJNDZUGZUVEVUHVUOHFLMZUVEVUOVUJHFZLMZUVEVUKLMVUEV
      UMVUCVUEUYDVULUVNUYDVUDUYPOZVUEVUGUXBVUEUVAUXJUVNUYFVUDUYIOZVUEUXGUXIVUEU
      XGVUEUURUWQNDZUXGUFDUURUUSVUDWCZVUDVVDUVNUWQWDUPZAUWQUFUUQNJWEWFZQWGVUEUV
      GUXHUVNUVGNDVUDUYROZVUEUURVVDUXHNDVVEVVFAUWQNUUQNKWHWFZQUQUSZUQZVUEUWSUXA
      VUEUWSVUEUURUWRNDZUWSUFDVVEVUEVVDVVLVVFUWQUTVRZAUWRUFUUQNJWEWFZQWGVUEUVGU
      WTVVHVUEUURVVLUWTNDVVEVVMAUWRNUUQNKWHWFZQUQUSZUSWIOVUEVURVUCVUEVUPVUQVUEV
      UNUXCVUEUVAUXKVVCVUEUYJUWQUFDZUXKNDZUVNUYJVUDUYKOZVUDVVQUVNUWQWJUPZBUWQWL
      QZUQZVUEUYJUWRUFDZUXCNDZVVSVUDVWCUVNUWQWMUPZBUWRWLQZUSVUEUXCVUIVWFUVNVUIN
      DZVUDUVNRNDZUYMVWGXLUYNRUVCWNUMOZUQWIOVUFUYDVUGNDZVUNNDZWOZUXBNDZVWDUGZUV
      EVUGVUNHFLMZUXEVUSVUEVWLVUCVUEUYDVWJVWKVVBVVKVWBWPOVUEVWNVUCVUEVWMVWDVVPV
      WFWIOVUEUXMVWOUXEVUEUXMUGUYDUYFUYFWOZUXJNDZVVRUGZUVEUVAUVAHFLMZUXMVWOUVNV
      WPVUDUXMUVNUYDUYFUYFUYPUYIUYIWPWQVUEVWRUXMVUEVWQVVRVVJVWAWIOUVNVWSVUDUXMU
      VNUYDUYFVWSUYPUYIUVEUVAWRQWQVUEUXMWSUVEUVAUVAUXJUXKWTXAXBVUEUXEUXMXCUVEVU
      GVUNUXBUXCXDXAVUEVVAVUCVUEUVEUXCUVEUVCUJFZEFZVUJHFZVUTLVUEUYDVWDVWDVWTNDZ
      VWGUVEUXCUXCHFLMZUVEVWTVUIHFLMZUVEVXBLMVVBVWFVWFUVNVXCVUDUVNUVEUVCUYPUYNX
      EOVWIVUEUYDVWDVXDVVBVWFUVEUXCWRQUVNVXEVUDUVNUYDUYDVWHUYMUYMUVEUVERHFZLMUV
      EUVCUVCHFLMZVXEUYPUYPUVNXFUYNUYNUVNUVEUVEVXFLUVNUYDUVEUVELMUYPUVEXGVRUVNU
      VEUVNUVEUYPVEXHVNUVNUYDUYMVXGUYPUYNUVEUVCWRQUVEUVERUVCUVCXIXJOUVEUXCUXCVW
      TVUIWTXJVUEVUOVXAVUJHVUEVXAUXCUVBIHFZEFUXCUVBEFZUXCIEFZHFVUOVUEVWTVXHUXCE
      UVNVWTVXHSVUDUVNUVDUVCUJFZIHFVWTVXHUVNUVDUVCIUVNUVDUYOVEUVNBVUBXKZUVNXMXN
      UVNVXKUVBIHUVNUVBUVCUVNUVBUYLVEZVXLXOXPXQOVDVUEUXCUVBIVUEBUWRUUSUYTUURVUD
      VUAXRZVWEXSZUVNUVBVJDVUDVXMOVUEXMXTVUEVXIVUNVXJUXCHVUEVXIUVAUXCBEFZEFVUNV
      UEUXCUVABVXOUVNUVAVJDVUDUVNUVAUYIVEOZVXNYAVUEUXKVXPUVAEVUEUYTVUDUXKVXPSVX
      NUVNVUDWSBUWQYBQVDYCVUEUXCVXOVQPYDXPVNOUVEVUHVUOVUJYEXAVUEUYAVUKSVUCVUEUX
      SVUHUXTVUJHVUEUXSUVAUXGEFZUWSHFZUVAUXIEFZUXAHFZHFVXRVXTHFZUXBHFVUHVUEUXPV
      XSUXRVYAHVUEUURVVDUXPVXSSVVEVVFAUWQYFQVUEUXRUVGUCUXHAEFZEFZUWTHFZEFUVGVYD
      EFZUXAHFVYAVUEUXQVYEUVGEVUEUURVVDUXQVYESVVEVVFAUWQYGQVDVUEUVGVYDUWTVUEABU
      URAVJDUUSVUDUURAUYGVEWQZVXNYHZVUEUCVJDVYCVJDVYDVJDYIVUEUXHAVUEUURVVDUXHVJ
      DVVEVVFUURVVDUGZUXHVVIVEQZVYGYJUCVYCYNUMVUEUURVVLUWTVJDVVEVVMUURVVLUGZUWT
      VVOVEQZXTVUEVYFVXTUXAHVUEVYFUVGUVAUXHEFZEFVXTVUEVYDVYMUVGEVUEVYDUXHUVAEFV
      YMVUEUCUXHAVUEYKVYJVYGYAVUEUXHUVAVYJVXQYLVGVDVUEUVGUVAUXHVYHVXQVYJYAVGXPY
      MPVUEVXRUWSVXTUXAVUEUVAUXGVXQVUEUURVVDUXGVJDVVEVVFVYIUXGVVGYOQZYJVUEUURVV
      LUWSVJDVVEVVMVYKUWSVVNYOQVUEUVAUXIVXQVUEUVGUXHVYHVYJYJZYJVUEUVGUWTVYHVYLY
      JYPVUEVYBVUGUXBHVUEVUGVYBVUEUVAUXGUXIVXQVYNVYOXTYQXPYMVUEUXTUXKBEFVXPBEFZ
      VUJVUEBUWQVXNVVTYRVUEUXKVXPBEVUEBUWRIUJFZGFUXKVXPVUEVYQUWQBGVUEUWQVJDZIVJ
      DVYQUWQSVUDVYRUVNUWQUUAUPUUEUWQIUUBUUCVDVUEBUWRVXNVWEYRXQXPVUEVYPUXCBBEFZ
      EFVUJVUEUXCBBVXOVXNVXNUUDVUEVYSVUIUXCEUVNVYSVUISVUDUVNVUIUVCVYSUVNUVCVXLU
      UFUVNBVUBUUGUUHOVDVGYMPOVNUUIUUJUUKUULUVORSZUWBUWIUVNVYTUWAUWHUVELVYTUVSU
      WFUVTUWGHVYTUVPUWCUVRUWEHUVORAJTVYTUVQUWDUVGEUVORAKTVDPUVORBGTPYSYTUVOISZ
      UWBUWPUVNWUAUWAUWOUVELWUAUVSUWMUVTUWNHWUAUVPUWJUVRUWLHUVOIAJTWUAUVQUWKUVG
      EUVOIAKTVDPUVOIBGTPYSYTUVOUWRSZUWBUXEUVNWUBUWAUXDUVELWUBUVSUXBUVTUXCHWUBU
      VPUWSUVRUXAHUVOUWRAJTWUBUVQUWTUVGEUVOUWRAKTVDPUVOUWRBGTPYSYTUAUBUUMZUWBUX
      MUVNWUCUWAUXLUVELWUCUVSUXJUVTUXKHWUCUVPUXGUVRUXIHUVOUWQAJTWUCUVQUXHUVGEUV
      OUWQAKTVDPUVOUWQBGTPYSYTUVOUXOSZUWBUYBUVNWUDUWAUYAUVELWUDUVSUXSUVTUXTHWUD
      UVPUXPUVRUXRHUVOUXOAJTWUDUVQUXQUVGEUVOUXOAKTVDPUVOUXOBGTPYSYTUVOCSZUWBUVM
      UVNWUEUWAUVLUVELWUEUVSUVJUVTUVKHWUEUVPUVFUVRUVIHUVOCAJTWUEUVQUVHUVGEUVOCA
      KTVDPUVOCBGTPYSYTUUNUUOUUP $.
  $}

  $( Lemma for ~ jm2.19 .  X and Y values are coprime.  (Contributed by Stefan
     O'Rear, 23-Sep-2014.) $)
  jm2.19lem1 $p |- ( ( A e. ( ZZ>= ` 2 ) /\ M e. ZZ ) -> ( ( A rmX M ) gcd ( A
      rmY M ) ) = 1 ) $=
    ( c2 wcel cz crmx co cmul crmy cexp cmin cneg caddc wceq fovcl sqcld sqvald
    c1 cn zcnd cuz cfv wa cgcd frmx nn0cnd csquarenn rmspecnonsq eldifad adantr
    cn0 nncnd frmy mulcld negsubd oveq2d mulneg1d nnnegz mul12d 3eqtr3d oveq12d
    syl rmxynorm wi nn0zd zmulcld bezoutr1 syl22anc mpd ) ACUAUBZDZBEDZUCZABFGZ
    VNHGZABIGZACJGRKGZLZVPHGZHGZMGZRNZVNVPUDGRNZVMVNCJGZVQVPCJGZHGZLZMGWDWFKGWA
    RVMWDWFVMVNVMVNABUKVJEFUEOZUFZPVMVQWEVMVQVKVQSDZVLVKVQSUGAUHUIUJZULZVMVPVMV
    PABEVJEIUMOZTZPZUNUOVMWDVOWGVTMVMVNWIQVMVRWEHGVRVPVPHGZHGWGVTVMWEWPVRHVMVPW
    NQUPVMVQWEWLWOUQVMVRVPVPVMVRVMWJVREDWKVQURVBZTWNWNUSUTVAABVCUTVMVNEDZVPEDWR
    VSEDWBWCVDVMVNWHVEZWMWSVMVRVPWQWMVFVNVPVNVSVGVHVI $.

  $( Lemma for ~ jm2.19 .  (Contributed by Stefan O'Rear, 23-Sep-2014.) $)
  jm2.19lem2 $p |- ( ( A e. ( ZZ>= ` 2 ) /\ M e. ZZ /\ N e. ZZ ) -> ( ( A rmY M
      ) || ( A rmY N ) <-> ( A rmY M ) || ( A rmY ( N + M ) ) ) ) $=
    ( wcel cz crmy co cdvds wbr crmx cmul caddc cgcd c1 wceq frmy fovcl 3adant3
    wb cn0 c2 cuz cfv w3a 3adant2 frmx nn0zd gcdcomd jm2.19lem1 eqtrd syl112anc
    coprmdvdsb nn0cnd zcnd mulcomd breq2d bitrd zmulcld dvdsmul2 syl2anc rmyadd
    dvdsadd2b 3com23 mulcld addcomd eqtr2d 3bitrd ) AUAUBUCZDZBEDZCEDZUDZABFGZA
    CFGZHIZVMVNABJGZKGZHIZVMACJGZVMKGZVQLGZHIZVMACBLGFGZHIVLVOVMVPVNKGZHIZVRVLV
    MEDZVNEDZVPEDVMVPMGZNOVOWESVIVJWFVKABEVHEFPQRZVIVKWGVJACEVHEFPQUEZVLVPVIVJV
    PTDVKABTVHEJUFQRZUGZVLWHVPVMMGZNVLVMVPWIWLUHVIVJWMNOVKABUIRUJVMVPVNULUKVLWD
    VQVMHVLVPVNVLVPWKUMZVLVNWJUNZUOUPUQVLWFVQEDVTEDVMVTHIZVRWBSWIVLVNVPWJWLURVL
    VSVMVLVSVIVKVSTDVJACTVHEJUFQUEZUGZWIURVLVSEDWFWPWRWIVSVMUSUTVMVQVTVBUKVLWAW
    CVMHVLWCVQVTLGZWAVIVKVJWCWSOACBVAVCVLVQVTVLVNVPWOWNVDVLVSVMVLVSWQUMVLVMWIUN
    VDVEVFUPVG $.

  ${
    $d A a b $.  $d M a b $.  $d N a b $.  $d I a b $.
    $( Lemma for ~ jm2.19 .  (Contributed by Stefan O'Rear, 26-Sep-2014.) $)
    jm2.19lem3 $p |- ( ( A e. ( ZZ>= ` 2 ) /\ ( M e. ZZ /\ N e. ZZ ) /\ I e.
        NN0 ) -> ( ( A rmY M ) || ( A rmY N ) <-> ( A rmY M ) || ( A rmY ( N +
        ( I x. M ) ) ) ) ) $=
      ( wcel cz crmy co cdvds wbr cmul caddc wb cc0 oveq2d breq2d bibi2d imbi2d
      wi oveq1 va vb c2 cuz cfv wa cn0 cv wceq weq zcn ad2antrl mul02d ad2antll
      c1 cc addridd eqtr2d w3a simp3 simprl simprrl simprrr nn0z adantr zmulcld
      zaddcld jm2.19lem2 syl3anc zcnd addassd nn0cn adddird mullidd eqtrd bitrd
      1cnd 3adant3 3exp a2d nn0ind com12 3impia ) AUCUDUEEZCFEZDFEZUFZBUGEZACGH
      ZADGHZIJZWIADBCKHZLHZGHZIJZMZWHWDWGUFZWPWQWKWIADUAUHZCKHZLHZGHZIJZMZSWQWK
      WIADNCKHZLHZGHZIJZMZSWQWKWIADUBUHZCKHZLHZGHZIJZMZSWQWKWIADXIUOLHZCKHZLHZG
      HZIJZMZSWQWPSUAUBBWRNUIZXCXHWQYAXBXGWKYAXAXFWIIYAWTXEAGYAWSXDDLWRNCKTOOPQ
      RUAUBUJZXCXNWQYBXBXMWKYBXAXLWIIYBWTXKAGYBWSXJDLWRXICKTOOPQRWRXOUIZXCXTWQY
      CXBXSWKYCXAXRWIIYCWTXQAGYCWSXPDLWRXOCKTOOPQRWRBUIZXCWPWQYDXBWOWKYDXAWNWII
      YDWTWMAGYDWSWLDLWRBCKTOOPQRWQWJXFWIIWQDXEAGWQXEDNLHDWQXDNDLWQCWECUPEWDWFC
      UKULUMOWQDWFDUPEWDWEDUKUNUQUROPXIUGEZWQXNXTYEWQXNXTYEWQXNUSWKXMXSYEWQXNUT
      YEWQXMXSMXNYEWQUFZXMWIAXKCLHZGHZIJZXSYFWDWEXKFEXMYIMYEWDWGVAYEWDWEWFVBZYF
      DXJYEWDWEWFVCZYFXICYEXIFEWQXIVDVEYJVFZVGACXKVHVIYFYHXRWIIYFYGXQAGYFYGDXJC
      LHZLHXQYFDXJCYFDYKVJYFXJYLVJYFCYJVJZVKYFYMXPDLYFXPXJUOCKHZLHYMYFXIUOCYEXI
      UPEWQXIVLVEYFVQYNVMYFYOCXJLYFCYNVNOUROVOOPVPVRVPVSVTWAWBWC $.
  $}

  $( Lemma for ~ jm2.19 .  Extend to ZZ by symmetry.  TODO: use ~ zindbi .
     (Contributed by Stefan O'Rear, 26-Sep-2014.) $)
  jm2.19lem4 $p |- ( ( A e. ( ZZ>= ` 2 ) /\ ( M e. ZZ /\ N e. ZZ ) /\ I e. ZZ )
      -> ( ( A rmY M ) || ( A rmY N ) <-> ( A rmY M ) || ( A rmY ( N + ( I x. M
      ) ) ) ) ) $=
    ( wcel cz wa crmy co cdvds wbr cmul caddc wb cn0 jm2.19lem3 ad2antrr cc zcn
    cneg c2 cuz cr wo elznn0 wi 3expia adantr simplll simprl simprr nn0z adantl
    cfv simplr recnd znegclb syl mpbird zmulcld zaddcld syl121anc cmin ad2antrl
    simpr mulneg1d oveq2d ad2antll mulcld addcld pncand 3eqtrd breq2d bitr2d ex
    negsubd jaod expimpd biimtrid 3impia ) AUAUBUNEZCFEZDFEZGZBFEZACHIZADHIZJKZ
    WFADBCLIZMIZHIJKZNZWEBUCEZBOEZBTZOEZUDZGWAWDGZWLBUEWRWMWQWLWRWMGZWNWLWPWRWN
    WLUFWMWAWDWNWLABCDPUGUHWSWPWLWSWPGZWKWFAWJWOCLIZMIZHIZJKZWHWTWAWBWJFEWPWKXD
    NWAWDWMWPUIWRWBWMWPWAWBWCUJQZWTDWIWRWCWMWPWAWBWCUKQWTBCWTWEWOFEZWPXFWSWOULU
    MWTBREWEXFNWTBWRWMWPUOUPZBUQURUSXEUTVAWSWPVEAWOCWJPVBWTXCWGWFJWTXBDAHWTXBWJ
    WITZMIWJWIVCIDWTXAXHWJMWTBCXGWRCREZWMWPWBXIWAWCCSVDQZVFVGWTWJWIWTDWIWRDREZW
    MWPWCXKWAWBDSVHQZWTBCXGXJVIZVJXMVPWTDWIXLXMVKVLVGVMVNVOVQVRVSVT $.

  $( Lemma 2.19 of [JonesMatijasevic] p. 696.  Transfer divisibility
     constraints between Y-values and their indices.  (Contributed by Stefan
     O'Rear, 24-Sep-2014.) $)
  jm2.19 $p |- ( ( A e. ( ZZ>= ` 2 ) /\ M e. ZZ /\ N e. ZZ ) -> ( M || N <-> (
      A rmY M ) || ( A rmY N ) ) ) $=
    ( cfv wcel cz cdvds wbr crmy co wb cc0 wceq syl adantr oveq2d cabs ad2antrr
    clt syl2anc c2 cuz w3a wa rmyeq0 3adant2 0dvds 3ad2ant3 fovcl 3bitr4d simpr
    frmy breq1d simpl1 rmy0 eqtrd wne cmo 3adant3 dvds0 3ad2ant1 breqtrrd oveq2
    wi breq2d syl5ibrcom wn cle cr crp zre zcn 3ad2ant2 simplr absrpcld simpll1
    cc modlt simpll3 cn simpll2 nnabscl zmodcld nn0abscl ltrmynn0 syl3anc mpbid
    cn0 nn0zd rmyabs modcld modge0 absidd 3brtr4d nn0red ltnled dvdsleabs2 mtod
    necon3bid ex necon4ad impbid simpl2 simpl3 dvdsabsmod0 cmin cdiv cneg caddc
    modabsdifz znegcld jm2.19lem4 syl121anc recnd subcld divcld mulneg1d mulcld
    cmul negsubd divcan1d nncand 3eqtrrd bitr4d pm2.61dane ) AUAUBDZEZBFEZCFEZU
    CZBCGHZABIJZACIJZGHZKBLYJBLMZUDZLCGHZLYMGHZYKYNYJYQYRKYOYJCLMZYMLMZYQYRYGYI
    YSYTKYHACUEUFYIYGYQYSKYHCUGUHYJYMFEZYRYTKYGYIUUAYHACFYFFIULUIUFYMUGNUJOYPBL
    CGYJYOUKZUMYPYLLYMGYPYLALIJZLYPBLAIUUBPYPYGUUCLMZYGYHYIYOUNAUOZNUPUMUJYJBLU
    QZUDZCBQDZURJZLMZYLAUUIIJZGHZYKYNUUGUUJUULYJUUJUULVDUUFYJUULUUJYLUUCGHYJYLL
    UUCGYJYLFEZYLLGHYGYHUUMYIABFYFFIULUIUSZYLUTNYGYHUUDYIUUEVAVBUUJUUKUUCYLGUUI
    LAIVCVEVFOUUGUULUUILUUGUUILUQZUULVGUUGUUOUDZUULYLQDZUUKQDZVHHZUUPUURUUQSHUU
    SVGUUPUUKAUUHIJZUURUUQSUUPUUIUUHSHZUUKUUTSHZUUPCVIEZUUHVJEZUVAYJUVCUUFUUOYI
    YGUVCYHCVKUHZRZUUPBYJBVQEZUUFUUOYHYGUVGYIBVLVMZRYJUUFUUOVNZVOZCUUHVRTUUPYGU
    UIWHEUUHWHEZUVAUVBKYGYHYIUUFUUOVPZUUPCUUHYGYHYIUUFUUOVSUUPYHUUFUUHVTEYGYHYI
    UUFUUOWAZUVIBWBTWCZYJUVKUUFUUOYHYGUVKYIBWDVMRAUUIUUHWEWFWGUUPUURAUUIQDZIJZU
    UKUUPYGUUIFEZUURUVPMUVLUUPUUIUVNWIZAUUIWJTUUPUVOUUIAIUUPUUIUUPCUUHUVFUVJWKU
    UPUVCUVDLUUIVHHUVFUVJCUUHWLTWMPUPUUPYGYHUUQUUTMUVLUVMABWJTWNUUPUURUUQUUPUUR
    UUPUUKFEZUURWHEUUPYGUVQUVSUVLUVRAUUIFYFFIULUITZUUKWDNWOUUPUUQUUPUUMUUQWHEYJ
    UUMUUFUUOUUNRZYLWDNWOWPWGUUPUUMUVSUUKLUQZUULUUSVDUWAUVTUUPUUOUWBUUGUUOUKUUP
    UUILUUKLUUPYGUVQUUJUUKLMKUVLUVRAUUIUETWSWGYLUUKWQWFWRWTXAXBUUGYHYIUUFYKUUJK
    YGYHYIUUFXCZYGYHYIUUFXDZYJUUFUKZBCXEWFUUGYNYLACCUUIXFJZBXGJZXHZBXSJZXIJZIJZ
    GHZUULUUGYGYHYIUWHFEYNUWLKYGYHYIUUFUNUWCUWDUUGUWGUUGUVCBVIEZUUFUWGFEYJUVCUU
    FUVEOZYJUWMUUFYHYGUWMYIBVKVMOUWEBCXJWFXKAUWHBCXLXMUUGUUKUWKYLGUUGUUIUWJAIUU
    GUWJCUWGBXSJZXHZXIJCUWOXFJZUUIUUGUWIUWPCXIUUGUWGBUUGUWFBUUGCUUIYJCVQEUUFYJC
    UVEXNOZUUGUUIUUGCUUHUWNUUGBYJUVGUUFUVHOZUWEVOWKXNZXOZUWSUWEXPZUWSXQPUUGCUWO
    UWRUUGUWGBUXBUWSXRXTUUGUWQCUWFXFJUUIUUGUWOUWFCXFUUGUWFBUXAUWSUWEYAPUUGCUUIU
    WRUWTYBUPYCPVEYDUJYE $.

  $( Lemma for ~ jm2.20nn .  Express X and Y values as a binomial.
     (Contributed by Stefan O'Rear, 26-Sep-2014.) $)
  jm2.21 $p |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. ZZ /\ J e. ZZ ) ->
      ( ( A rmX ( N x. J ) ) + ( ( sqrt ` ( ( A ^ 2 ) - 1 ) ) x. ( A rmY ( N x.
      J ) ) ) ) =
      ( ( ( A rmX N ) + ( ( sqrt ` ( ( A ^ 2 ) - 1 ) ) x. ( A rmY N ) ) ) ^ J )
      ) $=
    ( c2 cuz wcel cz cmul co crmx cexp c1 cmin csqrt crmy caddc wceq wa rmxyval
    cfv cc cc0 wne rmbaserp rpcnne0d expmulz sylan zmulcl sylan2 adantrr oveq1d
    3eqtr4d 3impb ) ADETFZCGFZBGFZACBHIZJIADKILMINTZAUQOIHIPIZACJIURACOIHIPIZBK
    IZQUNUOUPRZRZAURPIZUQKIZVDCKIZBKIZUSVAUNVDUAFVDUBUCRVBVEVGQUNVDAUDUEVDCBUFU
    GVBUNUQGFUSVEQCBUHAUQSUIVCUTVFBKUNUOUTVFQUPACSUJUKULUM $.

  $( what lemmas can be pulled out of these two to shrink them? $)

  ${
    $d A i x $.  $d N i x $.  $d J i x $.
    $( Lemma for ~ jm2.20nn .  Applying binomial theorem and taking irrational
       part.  (Contributed by Stefan O'Rear, 26-Sep-2014.)  (Revised by Stefan
       O'Rear, 6-May-2015.) $)
    jm2.22 $p |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. ZZ /\ J e. NN0 ) ->
        ( A rmY ( N x. J ) ) = sum_ i e. { x e. ( 0 ... J ) | -. 2 || x }
            ( ( J _C i ) x. ( ( ( A rmX N ) ^ ( J - i ) ) x.
            ( ( ( A rmY N ) ^ i ) x. ( ( ( A ^ 2 ) - 1 ) ^ ( ( i - 1 ) / 2 ) )
        ) ) ) ) $=
      ( c2 wcel cz cn0 cmul co wbr cc0 cexp wceq cc zcnd a1i adantr adantrr cuz
      cfv w3a crmx cv cdvds cfz crab cbc cmin c1 csqrt crmy csu cdiv caddc nn0z
      wn wa jm2.21 syl3an3 fovcl 3adant3 nn0cnd eluzelz zsqcl peano2zm 3ad2ant1
      frmx 3syl sqrtcld mulcld simp3 binom syl3anc cin c0 rabnc cun rabxm fzfid
      frmy simpl3 elfzelz adantl bccl syl2anc fznn0sub expcld elfznn0 fsumsplit
      nn0zd cfn wss fzfi ssrab2 ssfi mp2an breq2 notbid elrab zexpcl syl2an cle
      simpr 1zzd n2dvds1 syl22anc wb 2z 2ne0 syl dvdsval2 mpbid 2re 2pos divge0
      elnn0z sylanbrc sylan2b mul12d mulcomd 2nn0 ad2antrl 2cnd divcan2d oveq2d
      cr expmuld sqsqrtd oveq1d 3eqtr4d eqtrd mulexpd 3eqtrd cq zmulcld fsumzcl
      sselid zssq omoe wne clt cn wo dvds0 ax-mp mpbiri con3i elnn0 sylib orel2
      zred sylc nnm1nn0 nn0ge0d fsummulc2 3eqtr3rd expm1t sumeq2dv rmspecsqrtnq
      eqtr2d cdif nn0ssq simp1 simp2 3ad2ant3 eqcomd biimpa nn0re sylan eqeltrd
      nn0ge0 qirropth syl122anc simprd ) BFUAUBZGZEHGZDIGZUCZBEDJKZUDKZFAUEZUFL
      ZAMDUGKZUHZDCUEZUIKZBEUDKZDUWHUJKZNKZBFNKZUKUJKZULUBZBEUMKZJKZUWHNKZJKZJK
      ZCUNZOZBUWBUMKZUWEURZAUWFUHZUWIUWLUWPUWHNKZUWNUWHUKUJKZFUOKZNKZJKZJKZJKZC
      UNZOZUWAUWCUWOUXCJKUPKZUXAUWOUXMJKZUPKZOZUXBUXNUSZUWAUXOUWJUWQUPKDNKZUWFU
      WTCUNZUXQUVTUVRUVSDHGZUXOUXTODUQZBDEUTVAUWAUWJPGUWQPGUVTUXTUYAOUWAUWJUVRU
      VSUWJIGUVTBEIUVQHUDVIVBVCZVDUWAUWOUWPUWAUWNUWAUWNUVRUVSUWNHGZUVTUVRBHGUWM
      HGUYEFBVEBVFUWMVGVJVHZQVKZUWAUWPUVRUVSUWPHGZUVTBEHUVQHUMWBVBVCZQVLUVRUVSU
      VTVMUWJUWQCDVNVOUWAUYAUXAUXEUWTCUNZUPKUXQUWAUWGUXEUWTUWFCUWGUXEVPVQOUWAUW
      EAUWFVRRUWFUWGUXEVSOUWAUWEAUWFVTRUWAMDWAUWAUWHUWFGZUSZUWIUWSUYLUWIUYLUVTU
      WHHGZUWIHGZUVRUVSUVTUYKWCUYKUYMUWAUWHMDWDZWEUVTUYMUSUWIUWHDWFWLWGZQZUYLUW
      LUWRUYLUWJUWKUYLUWJUWAUWJHGZUYKUWAUWJUYDWLSZQUYKUWKIGZUWAUWHMDWHWEZWIZUYL
      UWQUWHUYLUWOUWPUYLUWNUYLUWNUWAUYEUYKUYFSQZVKZUYLUWPUWAUYHUYKUYISQZVLUYKUW
      HIGZUWAUWHDWJZWEZWIVLVLWKUWAUYJUXPUXAUPUWAUXPUXEUWOUXLJKZCUNUYJUWAUXEUXLU
      WOCUXEWMGZUWAUWFWMGZUXEUWFWNVUJMDWOZUXDAUWFWPUWFUXEWQWRRZUYGUWHUXEGZUWAUY
      KFUWHUFLZURZUSZUXLPGUXDVUPAUWHUWFUWDUWHOUWEVUOUWDUWHFUFWSZWTXAZUWAVUQUSZU
      WIUXKUWAUYKUWIPGVUPUYQTZVUTUWLUXJUWAUYKUWLPGVUPVUBTZVUTUXFUXIUWAUYKUXFPGV
      UPUYLUXFUWAUYHVUFUXFHGZUYKUYIVUGUWPUWHXBXCZQTZVUTUWNUXHUWAUYKUWNPGZVUPVUC
      TZVUQUXHIGZUWAVUQUXHHGZMUXHXDLZVVHVUQFUXGUFLZVVIVUQUYMVUPUKHGFUKUFLURZVVK
      UYKUYMVUPUYOSUYKVUPXEVUQXFVVLVUQXGRUWHUKUUAXHVUQFHGZFMUUBZUXGHGZVVKVVIXIV
      VMVUQXJRVVNVUQXKRUYKVVOVUPUYKUYMVVOUYOUWHVGXLZSFUXGXMVOXNVUQUXGYHGZMUXGXD
      LFYHGZMFUUCLZVVJUYKVVQVUPUYKUXGVVPUUMSVUQUXGVUQUWHUUDGZUXGIGVUQUWHMOZURZV
      VTVWAUUEZVVTVUPVWBUYKVWAVUOVWAVUOFMUFLZVVMVWDXJFUUFUUGUWHMFUFWSUUHUUIWEVU
      QVUFVWCUYKVUFVUPVUGSUWHUUJUUKVWAVVTUULUUNZUWHUUOXLUUPVVRVUQXORVVSVUQXPRUX
      GFXQXHUXHXRXSZWEZWIZVLZVLZVLXTUUQUWAUXEVUIUWTCVUNUWAVUQVUIUWTOVUSVUTVUIUW
      IUWOUXKJKZJKUWTVUTUWOUWIUXKUWAUYKUWOPGZVUPVUDTZVVAVWJYAVUTVWKUWSUWIJVUTVW
      KUWLUWOUXJJKZJKUWSVUTUWOUWLUXJVWMVVBVWIYAVUTVWNUWRUWLJVUTUXFUWOUWHNKZJKZV
      WOUXFJKZVWNUWRVUTUXFVWOVVEUWAUYKVWOPGVUPUYLUWOUWHVUDVUHWITYBVUTVWNUXFUWOU
      XIJKZJKVWPVUTUWOUXFUXIVWMVVEVWHYAVUTVWRVWOUXFJVUTUXIUWOJKUWOUXGNKZUWOJKZV
      WRVWOVUTUXIVWSUWOJVUTUWOFUXHJKZNKUWOFNKZUXHNKVWSUXIVUTUWOFUXHVWMVWGFIGZVU
      TYCRYIVUTVXAUXGUWONVUTUXGFUYKUXGPGUWAVUPUYKUXGVVPQYDVUTYEVVNVUTXKRYFYGVUT
      VXBUWNUXHNVUTUWNVVGYJYKUURYKVUTUWOUXIVWMVWHYBVUTVWLVVTVWOVWTOVWMVUQVVTUWA
      VWEWEUWOUWHUUSWGYLYGYMUWAUYKUWRVWQOVUPUYLUWOUWPUWHVUDVUEVUHYNTYLYGYMYGYMX
      TUUTUVBYGYMYOUWAUWOPYPUVCGZUWCYPGUXCYPGUXAYPGUXMYPGUXRUXSXIUVRUVSVXDUVTBU
      VAVHUWAIYPUWCUVDUWAUVRUWBHGZUWCIGUVRUVSUVTUVEZUWAEDUVRUVSUVTUVFUVTUVRUYBU
      VSUYCUVGYQZBUWBIUVQHUDVIVBWGYSUWAHYPUXCYTUWAUVRVXEUXCHGVXFVXGBUWBHUVQHUMW
      BVBWGYSUWAHYPUXAYTUWAUWGUWTCUWGWMGZUWAVUKUWGUWFWNVXHVULUWEAUWFWPUWFUWGWQW
      RRUWHUWGGUWAUYKVUOUSZUWTHGUWEVUOAUWHUWFVURXAUWAVXIUSZUWIUWSUWAUYKUYNVUOUY
      PTVXJUWLUWRUWAUYKUWLHGZVUOUYLUYRUYTVXKUYSVUAUWJUWKXBWGZTVXJUWRUWNUWHFUOKZ
      NKZUXFJKZHVXJUWRVWQVXOVXJUWOUWPUWHUWAUYKVWLVUOVUDTZUWAUYKUWPPGVUOVUETUYKV
      UFUWAVUOVUGYDYNVXJVWOVXNUXFJVXJVWOUWOFVXMJKZNKVXBVXMNKVXNVXJUWHVXQUWONUWA
      UYKUWHVXQOVUOUYLVXQUWHUYLUWHFUYKUWHPGUWAUYKUWHUYOQWEUYLYEVVNUYLXKRYFUVHTY
      GVXJUWOFVXMVXPVXIVXMIGZUWAUYKVUFVUOVXRVUGVUFVUOUSZVXMHGZMVXMXDLZVXRVUFVUO
      VXTVUFVVMVVNUYMVUOVXTXIVVMVUFXJRVVNVUFXKRUWHUQFUWHXMVOUVIVXSUWHYHGZMUWHXD
      LZVVRVVSVYAVUFVYBVUOUWHUVJSVUFVYCVUOUWHUVMSVVRVXSXORVVSVXSXPRUWHFXQXHVXMX
      RXSUVKZWEVXCVXJYCRYIVXJVXBUWNVXMNVXJUWNUWAUYKVVFVUOVUCTYJYKYOYKYMVXJVXNUX
      FUWAUYEVXRVXNHGVXIUYFVYDUWNVXMXBXCUWAUYKVVCVUOVVDTYQUVLYQYQXTYRYSUWAHYPUX
      MYTUWAUXEUXLCVUMVUNUWAVUQUXLHGVUSVUTUWIUXKUWAUYKUYNVUPUYPTVUTUWLUXJUWAUYK
      VXKVUPVXLTVUTUXFUXIUWAUYKVVCVUPVVDTUWAUYEVVHUXIHGVUQUYFVWFUWNUXHXBXCYQYQY
      QXTYRYSUWOUWCUXCUXAUXMUVNUVOXNUVP $.
  $}

  ${
    $d A a b $.  $d N a b $.  $d J a b $.
    $( Lemma for ~ jm2.20nn .  Truncate binomial expansion p-adicly.
       (Contributed by Stefan O'Rear, 26-Sep-2014.) $)
    jm2.23 $p |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. ZZ /\ J e. NN ) -> ( ( A rmY N )
        ^ 3 ) || ( ( A rmY ( N x. J ) ) - ( J x. ( ( ( A rmX N ) ^ ( J - 1 ) )
        x. ( A rmY N ) ) ) ) ) $=
      ( va c2 wcel cz co c3 cexp cdvds wbr c1 cmul a1i wa cn0 syl cc0 cc vb cuz
      cfv cn w3a crmy cv wn cfz crab cbc crmx cmin cdiv csu cfn wss fzfi ssrab2
      ssfi mp2an nnnn0 sseli elfzelz bccl syl2an nn0zd simpl1 simpl2 frmx fovcl
      3ad2ant3 syl2anc adantl fznn0sub zexpcl rmspecnonsq eldifad nnzd 3ad2ant1
      csquarenn cle wceq breq2 notbid simprbi 1zzd n2dvds1 omoe syl22anc wne wb
      elrab 2ne0 peano2zm dvdsval2 syl3anc mpbid clt zred 0red elfzle1 sylanbrc
      2z 3re nnm1nn0 nn0ge0d 2re 2pos elnn0z sylancl zmulcld 3adant3 3nn0 caddc
      cr wo simpr adantr ad2antlr biimpi 1z mpbiri pm2.21dd jaodan ax-mp nn0cnd
      elfzd expcld expcl mulcld mulassd oveq2d oveq1d 3eqtrd eqtrd eqtr2d oveq2
      zcnd oveq12d 3pos ltletrd elnnz divge0 frmy elfzel1 zsubcld subge0 mpbird
      fsumzcl dvdsmul2 csn jm2.22 syl3an3 cin 1lt3 1re ltnlei mpbi mto intnanrd
      c0 sylnibr disjsn sylibr cun olcd ad2antrr elfznn0 simplrr elnn1uz2 df-ne
      3z nnz pm2.21d imp uzp1 dvdsmul1 2t1e2 breqtri eluzle 2p1e3 fveq2i eleq2s
      sylan2 sylan2b dvds0 elnn0 mpjaodan elfzle2 orcd pm2.61dane nn0uz eleqtri
      jca fzss1 anim1i 0le1 nnge1 eleq1 anbi12d mpbir2and impbida velsn orbi12i
      0zd elun bitri 3bitr4g eqrdv rmspecpos rpcnd wi con3dimp sylbi orel2 sylc
      fsumsplit fsummulc1 mulcomd expaddd 3cn npcan eqtr3d sumeq2dv 1nn0 oveq1i
      1nn 1m1e0 div0i eqtri 0nn0 eqeltri oveq1 sumsn sylancr eqcomd exp1d exp0d
      2cn bcn1 mulridd fsumcl pncand breqtrrd ) AEUBUCZFZCGFZBUDFZUEZACUFHZIJHZ
      EUAUGZKLZUHZUAIBUIHZUJZBDUGZUKHZACULHZBVURUMHZJHZAEJHMUMHZVURMUMHZEUNHZJH
      ZVUKVURIUMHZJHZNHZNHZNHZDUOZVULNHZACBNHUFHZBVUTBMUMHZJHZVUKNHZNHZUMHZKVUJ
      VVLGFVULGFZVULVVMKLVUJVUQVVKDVUQUPFZVUJVUPUPFVUQVUPUQVWAIBURVUOUAVUPUSZVU
      PVUQUTVAOZVUJVURVUQFZPZVUSVVJVWEVUSVUJBQFZVURGFZVUSQFZVWDVUIVUGVWFVUHBVBZ
      VLZVWDVURVUPFZVWGVUQVUPVURVWBVCZVURIBVDZRZVURBVEZVFZVGVWEVVBVVIVWEVUTGFVV
      AQFZVVBGFVWEVUTVWEVUGVUHVUTQFZVUGVUHVUIVWDVHZVUGVUHVUIVWDVIZACQVUFGULVJVK
      ZVMVGVWEVWKVWQVWDVWKVUJVWLVNVURIBVORZVUTVVAVPVMVWEVVFVVHVUJVVCGFZVVEQFZVV
      FGFVWDVUGVUHVXCVUIVUGVVCVUGVVCUDWAAVQVRVSVTVWDVVEGFZSVVEWBLZVXDVWDEVVDKLZ
      VXEVWDVWGEVURKLZUHZMGFZEMKLZUHZVXGVWNVWDVWKVXIVUOVXIUAVURVUPVUMVURWCVUNVX
      HVUMVUREKWDWEZWMZWFVWDWGVXLVWDWHOVURMWIZWJVWDEGFZESWKZVVDGFZVXGVXEWLZVXPV
      WDXDOVXQVWDWNOVWDVWGVXRVWNVURWOZRZEVVDWPZWQWRVWDVVDXPFZSVVDWBLZEXPFZSEWSL
      ZVXFVWDVVDVYAWTVWDVWKVYDVWLVWKVVDVWKVURUDFZVVDQFZVWKVWGSVURWSLVYGVWMVWKSI
      VURVWKXAIXPFZVWKXEOVWKVURVWMWTZSIWSLVWKUUAOVURIBXBZUUBVURUUCXCVURXFZRXGRV
      YEVWDXHOVYFVWDXIOVVDEUUDZWJVVEXJZXCZVVCVVEVPVFVWEVUKGFZVVGQFZVVHGFVWEVUGV
      UHVYPVWSVWTACGVUFGUFUUEVKZVMVWDVYQVUJVWDVWKVYQVWLVWKVVGGFSVVGWBLZVYQVWKVU
      RIVWMVURIBUUFUUGVWKVYSIVURWBLZVYKVWKVURXPFVYIVYSVYTWLVYJXEVURIUUHXKUUIVVG
      XJXCRZVNZVUKVVGVPVMXLXLXLZUUJVUJVYPIQFZVVTVUGVUHVYPVUIVYRXMZXNVUKIVPXKVVL
      VULUUKVMVUJVVSVVMBMUKHZVVPVUKMJHZVVCMMUMHZEUNHZJHZNHZNHZNHZXOHZWUMUMHVVMV
      UJVVNWUNVVRWUMUMVUJVVNVUOUASBUIHZUJZVUSVVBVUKVURJHZVVFNHZNHZNHZDUOZVUQWUT
      DUOZMUULZWUTDUOZXOHWUNVUIVUGVUHVWFVVNWVAWCVWIUAADBCUUMUUNVUJVUQWVCWUTWUPD
      VUJMVUQFZUHVUQWVCUUOUVBWCVUJMVUPFZVXLPWVEVUJWVFVXLWVFUHVUJWVFIMWBLZMIWSLW
      VGUHUUPMIUUQXEUURUUSMIBXBUUTOUVAVUOVXLUAMVUPVUMMWCVUNVXKVUMMEKWDWEWMUVCVU
      QMUVDUVEVUJDWUPVUQWVCUVFZVUJVURWUOFZVXIPZVWKVXIPZVURMWCZXQZVURWUPFZVURWVH
      FZVUJWVJWVMVUJWVJPZWVMVURMWVPWVLPWVLWVKWVPWVLXRUVGWVPVURMWKZPZWVKWVLWVRVW
      KVXIWVRVURIBIGFWVRUVMOVUJBGFZWVJWVQVUIVUGWVSVUHBUVNVLZUVHWVJVWGVUJWVQWVIV
      WGVXIVURSBVDZXSXTWVRVURQFZVXIWVQVYTWVJWWBVUJWVQWVIWWBVXIVURBUVIZXSXTVUJWV
      IVXIWVQUVJZWVPWVQXRWWBVXIWVQUEZVYGVYTVURSWCZVYGWWEWVLVURVUFFZXQVYTVURUVKW
      WEWVLVYTWWGWWEWVLVYTWWEWVLVYTWVQWWBWVLUHZVXIWVQWWHVURMUVLYAVLUVOUVPWWGWWE
      VUREWCZVUREMXOHZUBUCZFZXQVYTEVURUVQWWEWWIVYTWWLWWEWWIPZVXHVYTWWMVXHEEKLZE
      EMNHZEKVXPVXJEWWOKLXDYBEMUVRVAUVSUVTWWIVXHWWNWLWWEVUREEKWDVNYCWWBVXIWVQWW
      IVIYDWWLVYTWWEVYTVURIUBUCWWKIVURUWAWWJIUBUWBUWCUWDVNYEUWEYEUWFWWEWWFPVXHV
      YTWWFVXHWWEWWFVXHESKLZVXPWWPXDEUWGYFVURSEKWDYCZVNWWBVXIWVQWWFVIYDWWBVXIVY
      GWWFXQZWVQWWBWWRVURUWHYAZVTUWIWQWVJVURBWBLZVUJWVQWVIWWTVXIVURSBUWJXSXTYHW
      WDUWOUWKUWLVUJWVKWVJWVLWVKWVJVUJVWKWVIVXIVUPWUOVURISUBUCZFVUPWUOUQIQWXAXN
      UWMUWNISBUWPYFVCUWQVNVUJWVLPZWVJMWUOFZVXLWXBMSBWXBUXFVUJWVSWVLWVTXSWXBWGS
      MWBLWXBUWROVUJMBWBLZWVLVUIVUGWXDVUHBUWSVLXSYHVXLWXBWHOWVLWVJWXCVXLPWLVUJW
      VLWVIWXCVXIVXLVURMWUOUWTWVLVXHVXKVURMEKWDWEUXAVNUXBYEUXCVUOVXIUAVURWUOVXM
      WMZWVOVWDVURWVCFZXQWVMVURVUQWVCUXGVWDWVKWXFWVLVXNDMUXDUXEUXHUXIUXJWUPUPFZ
      VUJWUOUPFWUPWUOUQWXGSBURVUOUAWUOUSZWUOWUPUTVAOVUJWVNPZVUSWUSWXIVUSVUJVWFV
      WGVWHWVNVWJWVNWVIVWGWUPWUOVURWXHVCZWWARZVWOVFYGWXIVVBWURWXIVUTVVAVUJVUTTF
      ZWVNVUJVUTVUGVUHVWRVUIVXAXMYGZXSWXIWVIVWQWVNWVIVUJWXJVNVURSBVORYIWXIWUQVV
      FVUJVUKTFZWWBWUQTFWVNVUJVUKWUEYSZWVNWVIWWBWXJWWCRZVUKVURYJVFVUJVVCTFZVXDV
      VFTFZWVNVUGVUHWXQVUIVUGVVCAUXKUXLVTZWVNVXEVXFVXDWVNVXGVXEWVNVWGVXIVXJVXLV
      XGWXKWVNWVIVXIWXEWFWVNWGVXLWVNWHOVXOWJWVNVXPVXQVXRVXSVXPWVNXDOVXQWVNWNOWV
      NVWGVXRWXKVXTRZVYBWQWRWVNVYCVYDVYEVYFVXFWVNVVDWXTWTWVNVVDWVNVYGVYHWVNWWFU
      HZWWRVYGWVNWVJWYAWXEWVIWWFVXHWWFVXHUXMWVIWWQOUXNUXOWVNWWBWWRWXPWWSRWWFVYG
      UXPUXQVYLRXGVYEWVNXHOVYFWVNXIOVYMWJVYNXCVVCVVEYJZVFYKYKYKUXRVUJWVBVVMWVDW
      UMXOVUJVVMVUQVVKVULNHZDUOWVBVUJVUQVVKVULDVWCVUJWXNWUDVULTFZWXOXNVUKIYJXKZ
      VWEVVKWUCYSZUXSVUJVUQWYCWUTDVWEWYCVUSVVJVULNHZNHWUTVWEVUSVVJVULVWEVUSVWPY
      GVWEVVBVVIVWEVUTVVAVUJWXLVWDWXMXSVXBYIZVWEVVFVVHVUJWXQVXDWXRVWDWXSVYOWYBV
      FZVUJWXNVYQVVHTFVWDWXOWUAVUKVVGYJVFZYKZYKVUJWYDVWDWYEXSZYLVWEWYGWUSVUSNVW
      EWYGVVBVVIVULNHZNHWUSVWEVVBVVIVULWYHWYKWYLYLVWEWYMWURVVBNVWEWYMVVFVVHVULN
      HZNHWYNVVFNHWURVWEVVFVVHVULWYIWYJWYLYLVWEVVFWYNWYIVWEVVHVULWYJWYLYKUXTVWE
      WYNWUQVVFNVWEVUKVVGIXOHZJHWYNWUQVWEVUKVVGIVUJWXNVWDWXOXSWUDVWEXNOWUBUYAVW
      EWYOVURVUKJVWEVURTFITFWYOVURWCVWEVURVWDVWGVUJVWNVNYSUYBVURIUYCXKYMUYDYNYO
      YMYPYMYPUYEYQVUJMUDFWUMTFWVDWUMWCUYHVUJWUFWULVUIVUGWUFTFVUHVUIWUFVUIVWFVX
      JWUFQFVWIYBMBVEXKYGVLVUJVVPWUKVUJVUTVVOWXMVUIVUGVVOQFVUHBXFVLYIVUJWUGWUJV
      UJWXNMQFWUGTFWXOUYFVUKMYJXKVUJWXQWUIQFWUJTFWXSWUISQWUISEUNHSWUHSEUNUYIUYG
      EUYTWNUYJUYKZUYLUYMVVCWUIYJXKYKYKYKZWUTWUMDMUDWVLVUSWUFWUSWULNVURMBUKYRWV
      LVVBVVPWURWUKNWVLVVAVVOVUTJVURMBUMYRYMWVLWUQWUGVVFWUJNVURMVUKJYRWVLVVEWUI
      VVCJWVLVVDWUHEUNVURMMUMUYNYNYMYTYTYTUYOUYPYTYOVUJBWUFVVQWULNVUJWUFBVUJVWF
      WUFBWCVWJBVUARUYQVUJVUKWUKVVPNVUJWUKVUKMNHVUKVUJWUGVUKWUJMNVUJVUKWXOUYRVU
      JWUJVVCSJHMVUJWUISVVCJWUISWCVUJWYPOYMVUJVVCWXSUYSYPYTVUJVUKWXOVUBYQYMYTYT
      VUJVVMWUMVUJVVLVULVUJVUQVVKDVWCWYFVUCWYEYKWYQVUDYPVUE $.
  $}

  $( Lemma 2.20 of [JonesMatijasevic] p. 696, the "first step down lemma".
     (Contributed by Stefan O'Rear, 27-Sep-2014.) $)
  jm2.20nn $p |- ( ( A e. ( ZZ>= ` 2 ) /\ M e. NN /\ N e. NN ) -> ( ( ( A rmY N
      ) ^ 2 ) || ( A rmY M ) <-> ( N x. ( A rmY N ) ) || M ) ) $=
    ( c2 wcel crmy co cdvds wbr cmul cz syl2anc zcnd adantr c1 cmin syl3anc cc0
    wb c3 cuz cfv cn w3a cexp wa cdiv simp1 nnz 3ad2ant3 frmy fovcl sqvald crmx
    cc cgcd wceq zsqcl syl cn0 nn0zd simpr eqbrtrrd wi 3ad2ant2 muldvds1 simpl1
    frmx mpd jm2.19 mpbird simpl2 simpl3 nndivdvds mpbid nnm1nn0 zexpcl zmulcld
    nnzd nncn wne nnne0 divcan2d oveq2d eqeltrd zsubcld 3nn0 a1i 2nn0 cle 3z 2z
    2le3 eluz1i mpbir2an dvdsexp jm2.23 dvdstrd dvds2sub syl32anc oveq1d nncand
    imp mul12d breqtrd gcdcomd jm2.19lem1 rpexp12i syl112anc coprmdvds clt rmy0
    eqtrd 3ad2ant1 nngt0 0zd ltrmy sylanbrc dvdsmulcr dvdsmul2 dvdssub2 impbida
    elnnz dvdscmulr syl31anc ) ADUAUBZEZBUCEZCUCEZUDZACFGZDUEGZABFGZHIZCYKJGZBH
    IZYJYNUFZYOCBCUGGZJGZBHYQYOYSHIZYKYRHIZYQYKYKJGZYRYKJGZHIZUUAYQYLUUBUUCHYQY
    KYJYKUOEYNYJYKYJYGCKEZYKKEZYGYHYIUHZYIYGUUEYHCUIUJZACKYFKFUKULLZMZNZUMYQYLK
    EZACUNGZYROPGZUEGZKEZUUCKEZYLUUOUUCJGZHIZYLUUOUPGOUQZYLUUCHIZYJUULYNYJUUFUU
    LUUIYKURUSZNZYQUUMKEZUUNUTEZUUPYJUVDYNYJUUMYJYGUUEUUMUTEUUGUUHACUTYFKUNVHUL
    LVAZNZYQYRUCEZUVEYQCBHIZUVHYQUVIYKYMHIZYQUUBYMHIZUVJYQYLUUBYMHYJYLUUBUQYNYJ
    YKUUJUMZNYJYNVBZVCYJUVKUVJVDZYNYJUUFUUFYMKEZUVNUUIUUIYJYGBKEZUVOUUGYHYGUVPY
    IBUIVEZABKYFKFUKULLZYKYKYMVFQNVIYQYGUUEUVPUVIUVJSYGYHYIYNVGZYJUUEYNUUHNZYJU
    VPYNUVQNACBVJQVKYQYHYIUVIUVHSYGYHYIYNVLYGYHYIYNVMBCVNLVOZYRVPUSZUUMUUNVQLZY
    QYRYKYQYRUWAVSZYJUUFYNUUINZVRYQYLYMAYSFGZYRUUOYKJGZJGZPGZPGZUURHYQUULUVOUWI
    KEZYNYLUWIHIZYLUWJHIZUVCYJUVOYNUVRNYQUWFUWHYJUWFKEYNYJUWFYMKYJYSBAFYJBCYHYG
    BUOEYIBVTVEYIYGCUOEYHCVTUJYIYGCRWAZYHCWBUJZWCZWDUVRWENYQYRUWGUWDYQUUOYKUWCU
    WEVRVRZWFZUVMYQYLYKTUEGZUWIUVCYJUWSKEZYNYJUUFTUTEZUWTUUIUXAYJWGWHYKTVQLZNUW
    RYJYLUWSHIZYNYJUUFDUTEZTYFEZUXCUUIUXDYJWIWHUXEYJUXETKEDTWJIWKWMDTWLWNWOWHYK
    DTWPQZNYQYGUUEUVHUWSUWIHIUVSUVTUWAAYRCWQQWRUULUVOUWKUDYNUWLUFUWMYLYMUWIWSXC
    WTYQUWJYMYMUWHPGZPGZUURYQUWIUXGYMPYQUWFYMUWHPYQYSBAFYJYSBUQYNUWPNZWDXAWDYQU
    XHUWHUURYQYMUWHYJYMUOEYNYJYMUVRMNYQUWHUWQMXBYQYRUUOYKYQYRUWDMYQUUOUWCMUUKXD
    XMXMXEYQYKUUMUPGZOUQZUUTYJUXKYNYJUXJUUMYKUPGZOYJYKUUMUUIUVFXFYJYGUUEUXLOUQU
    UGUUHACXGLXMNYQUUFUVDUXDUVEUXKUUTVDUWEUVGUXDYQWIWHUWBYKUUMDUUNXHXIVIUULUUPU
    UQUDUUSUUTUFUVAYLUUOUUCXJXCWTVCYQUUFYRKEZUUFYKRWAZUUDUUASUWEUWDUWEYJUXNYNYJ
    YKUCEZUXNYJUUFRYKXKIUXOUUIYJARFGZRYKXKYGYHUXPRUQYIAXLXNYJRCXKIZUXPYKXKIZYIY
    GUXQYHCXOUJYJYGRKEUUEUXQUXRSUUGYJXPUUHARCXQQVOVCYKYCXRZYKWBUSNYKYKYRXSXIVOY
    QUUFUXMUUEUWNYTUUASUWEUWDUVTYJUWNYNUWONCYKYRYDXIVKUXIXEYJYPUFZYLAYOFGZYMYJU
    ULYPUVBNYJUYAKEZYPYJYGYOKEZUYBUUGYJCYKUUHUUIVRZAYOKYFKFUKULLZNYJUVOYPUVRNYJ
    YLUYAHIZYPYJUYFYLYKUUMYKOPGZUEGZYKJGZJGZHIZYJYLUYHYLJGZUYJHYJUYHKEZUULYLUYL
    HIYJUVDUYGUTEZUYMUVFYJUXOUYNUXSYKVPUSUUMUYGVQLZUVBUYHYLXTLYJUYLUYHUUBJGUYJY
    JYLUUBUYHJUVLWDYJUYHYKYKYJUYHUYOMUUJUUJXDXMXEYJUULUYBUYJKEYLUYAUYJPGZHIUYFU
    YKSUVBUYEYJYKUYIUUIYJUYHYKUYOUUIVRVRZYJYLUWSUYPUVBUXBYJUYAUYJUYEUYQWFUXFYJY
    GUUEUXOUWSUYPHIUUGUUHUXSAYKCWQQWRYLUYAUYJYAYEVKNUXTYPUYAYMHIZYJYPVBUXTYGUYC
    UVPYPUYRSYGYHYIYPVGYJUYCYPUYDNYJUVPYPUVQNAYOBVJQVOWRYB $.

  $( Lemma for ~ jm2.26 .  (Contributed by Stefan O'Rear, 2-Oct-2014.) $)
  jm2.25lem1 $p |- ( ( ( A e. ZZ /\ B e. ZZ ) /\ ( C e. ZZ /\ D e. ZZ ) /\ ( A
      || ( C - D ) \/ A || ( C - -u D ) ) ) ->
          ( ( A || ( D - B ) \/ A || ( D - -u B ) ) <-> ( A || ( C - B ) \/ A
      || ( C - -u B ) ) ) ) $=
    ( cz wcel wa cmin co cdvds wbr cneg wo simpl1l simpl2l simpl2r simpl3 simpr
    simpl1r acongtr w3a syl222anc acongsym syl31anc impbida ) AEFZBEFZGZCEFZDEF
    ZGZACDHIJKACDLHIJKMZUAZADBHIJKADBLZHIJKMZACBHIJKACUNHIJKMZUMUOGUFUIUJUGULUO
    UPUFUGUKULUONUIUJUHULUOOUIUJUHULUOPUFUGUKULUOSUHUKULUOQUMUORACDBTUBUMUPGZUF
    UJUIUGADCHIJKADCLHIJKMZUPUOUFUGUKULUPNZUIUJUHULUPPZUIUJUHULUPOZUFUGUKULUPSU
    QUFUIUJULURUSVAUTUHUKULUPQACDUCUDUMUPRADCBTUBUE $.

  ${
    $d A a b $.  $d M a b $.  $d N a b $.  $d I a b $.
    $( Lemma for ~ jm2.26 .  Remainders mod X(2n) are negaperiodic mod 2n.
       (Contributed by Stefan O'Rear, 2-Oct-2014.) $)
    jm2.25 $p |- ( ( A e. ( ZZ>= ` 2 ) /\ ( M e. ZZ /\ N e. ZZ ) /\ I e. ZZ )
        -> ( ( A rmX N ) || ( ( A rmY ( M + ( I x. ( 2 x. N ) ) ) ) - ( A rmY M
        ) ) \/ ( A rmX N ) || ( ( A rmY ( M + ( I x. ( 2 x. N ) ) ) ) - -u ( A
        rmY M ) ) ) ) $=
      ( c2 wcel cz co cmul caddc crmy cmin cdvds wbr syl2anc wceq oveq2d oveq1d
      c1 zcnd va vb cuz cfv wa crmx cneg wo cc0 simprl simprrr frmx fovcl nn0zd
      wi cn0 simprrl frmy congid 2cnd mulcld mul02d adantl addridd adantr eqtrd
      ad2antll breqtrrd orcd ex cv wb peano2zd eluzel2 ad2antrl zmulcld zaddcld
      zcn simpl znegcld zsubcld dvdsmul2 cexp rmxdbl nn0cnd sqcld npcand sqvald
      cc w3a mulass eqcomd syl3anc 3eqtrd dvdsmultr2 mpd mulridd adddid subnegd
      1cnd 3eqtr4d breqtrd rmydbl mul32d dvds2addd adddird 1zzd addassd mullidd
      3eqtr2d rmyadd addsubd jm2.25lem1 syl221anc pm5.74da oveq1 breq2d orbi12d
      olcd weq imbi2d zindbi mpbid impcom 3impa ) AEUCUDZFZCGFZDGFZUEZBGFZADUFH
      ZACBEDIHZIHZJHZKHZACKHZLHZMNZYLYPYQUGZLHZMNZUHZYKYGYJUEZUUCYKUUDYLACUIYMI
      HZJHZKHZYQLHZMNZYLUUGYTLHZMNZUHZUOZUUDUUCUOZYKUUDUULYKUUDUEZUUIUUKUUOYLYQ
      YQLHZUUHMUUOYLGFZYQGFZYLUUPMNUUOYGYIUUQYKYGYJUJZYKYGYHYIUKYGYIUEYLADUPYFG
      UFULUMZUNZOUUOYGYHUURUUSYKYGYHYIUQACGYFGKURUMZOYLYQUSOUUOUUGYQYQLUUOUUFCA
      KYJUUFCPYKYGYJUUFCUIJHZCYJUUEUICJYIUUEUIPYHYIYMYIEDYIUTDVRVAVBVCQYHUVCCPY
      IYHCCVRVDVEVFVGQRVHVIVJUUDYLACUAVKZYMIHZJHZKHZYQLHZMNZYLUVGYTLHZMNZUHZUOU
      UDYLACUBVKZYMIHZJHZKHZYQLHZMNZYLUVPYTLHZMNZUHZUOUUDYLACUVMSJHZYMIHZJHZKHZ
      YQLHZMNZYLUWEYTLHZMNZUHZUOUUMUUNUAUBBUVMGFZUUDUWAUWJUWKUUDUEZUUQUURUWEGFZ
      UVPGFZYLUWEUVPLHMNZYLUWEUVPUGZLHZMNZUHUWAUWJVLUWLYGYIUUQUWKYGYJUJZUWKYGYH
      YIUKZUVAOZUWLYGYHUURUWSUWKYGYHYIUQZUVBOUWLYGUWDGFUWMUWSUWLCUWCUXBUWLUWBYM
      UWLUVMUWKUUDVSZVMUWLEDYGEGFUWKYJEAVNVOZUWTVPZVPVQAUWDGYFGKURUMOUWLYGUVOGF
      ZUWNUWSUWLCUVNUXBUWLUVMYMUXCUXEVPZVQZAUVOGYFGKURUMOZUWLUWRUWOUWLYLUVPAYMU
      FHZIHZUWPLHZAUVOUFHZAYMKHZIHZJHZUWQMUWLYLUXLUXOUXAUWLUXKUWPUWLUVPUXJUXIUW
      LYGYMGFZUXJGFUWSUXEYGUXQUEUXJAYMUPYFGUFULUMUNOZVPZUWLUVPUXIVTZWAUWLUXMUXN
      UWLYGUXFUXMGFZUWSUXHYGUXFUEUXMAUVOUPYFGUFULUMUNOZUWLYGUXQUXNGFZUWSUXEAYMG
      YFGKURUMOZVPZUWLYLUVPUXJSJHZIHZUXLMUWLYLUYFMNZYLUYGMNZUWLYLEYLIHZYLIHZUYF
      MUWLUYJGFUUQYLUYKMNUWLEYLUXDUXAVPUXAUYJYLWBOUWLUYFEYLEWCHZIHZSLHZSJHUYMUY
      KUWLUXJUYNSJUWLYGYIUXJUYNPUWSUWTADWDORUWLUYMSUWLEUYLUWLUTZUWLYLUWLYLUWLYG
      YIYLUPFUWSUWTUUTOWEZWFVAUWLWTZWGUWLUYMEYLYLIHZIHZUYKUWLUYLUYREIUWLYLUYPWH
      QUWLEWIFZYLWIFZVUAUYSUYKPUYOUYPUYPUYTVUAVUAWJUYKUYSEYLYLWKWLWMVFWNVHUWLUU
      QUWNUYFGFUYHUYIUOUXAUXIUWLUXJUXRVMYLUVPUYFWOWMWPUWLUXKUVPSIHZJHUXKUVPJHUY
      GUXLUWLVUBUVPUXKJUWLUVPUWLUVPUXITZWQQUWLUVPUXJSVUCUWLUXJUXRTUYQWRUWLUXKUV
      PUWLUXKUXSTZVUCWSXAXBUWLYLUXNMNZYLUXOMNZUWLYLEADKHZIHZYLIHZUXNMUWLVUHGFUU
      QYLVUIMNUWLEVUGUXDUWLYGYIVUGGFUWSUWTADGYFGKURUMOZVPUXAVUHYLWBOUWLUXNUYJVU
      GIHZVUIUWLYGYIUXNVUKPUWSUWTADXCOUWLEYLVUGUYOUYPUWLVUGVUJTXDVFVHUWLUUQUYAU
      YCVUEVUFUOUXAUYBUYDYLUXMUXNWOWMWPXEUWLUWQUXKUXOJHZUWPLHUXPUWLUWEVULUWPLUW
      LUWEAUVOYMJHZKHZVULUWLUWDVUMAKUWLUWDCUVNSYMIHZJHZJHUVOVUOJHVUMUWLUWCVUPCJ
      UWLUVMSYMUWLUVMUXCTUYQUWLYMUXETZXFQUWLCUVNVUOUWLCUXBTUWLUVNUXGTUWLVUOUWLS
      YMUWLXGUXEVPTXHUWLVUOYMUVOJUWLYMVUQXIQXJQUWLYGUXFUXQVUNVULPUWSUXHUXEAUVOY
      MXKWMVFRUWLUXKUXOUWPVUDUWLUXOUYETUWLUWPUXTTXLVFVHXSYLYQUWEUVPXMXNXOUAUBXT
      ZUVLUWAUUDVURUVIUVRUVKUVTVURUVHUVQYLMVURUVGUVPYQLVURUVFUVOAKVURUVEUVNCJUV
      DUVMYMIXPQQZRXQVURUVJUVSYLMVURUVGUVPYTLVUSRXQXRYAUVDUWBPZUVLUWJUUDVUTUVIU
      WGUVKUWIVUTUVHUWFYLMVUTUVGUWEYQLVUTUVFUWDAKVUTUVEUWCCJUVDUWBYMIXPQQZRXQVU
      TUVJUWHYLMVUTUVGUWEYTLVVARXQXRYAUVDUIPZUVLUULUUDVVBUVIUUIUVKUUKVVBUVHUUHY
      LMVVBUVGUUGYQLVVBUVFUUFAKVVBUVEUUECJUVDUIYMIXPQQZRXQVVBUVJUUJYLMVVBUVGUUG
      YTLVVCRXQXRYAUVDBPZUVLUUCUUDVVDUVIYSUVKUUBVVDUVHYRYLMVVDUVGYPYQLVVDUVFYOA
      KVVDUVEYNCJUVDBYMIXPQQZRXQVVDUVJUUAYLMVVDUVGYPYTLVVERXQXRYAYBYCYDYE $.
  $}

  ${
    $d A a $.  $d N a $.  $d K a $.  $d M a $.
    $( Lemma for ~ jm2.26 .  Reverse direction is required to prove forward
       direction, so do it separately.  Induction on difference between K and
       M, together with the addition formula fact that adding 2N only inverts
       sign.  (Contributed by Stefan O'Rear, 2-Oct-2014.) $)
    jm2.26a $p |- ( ( ( A e. ( ZZ>= ` 2 ) /\ N e. ZZ ) /\ ( K e. ZZ /\ M e. ZZ
        ) ) -> ( ( ( 2 x. N ) || ( K - M ) \/ ( 2 x. N ) || ( K - -u M ) ) -> (
        ( A rmX N ) || ( ( A rmY K ) - ( A rmY M ) ) \/ ( A rmX N ) || ( ( A
        rmY K ) - -u ( A rmY M ) ) ) ) ) $=
      ( va c2 wcel cz wa co cmin cdvds wbr crmy cneg wceq syl2anc caddc adantr
      wo cuz cfv cmul crmx cv wb 2z simplr zmulcl sylancr zsubcl adantl divides
      simplll simplrr simpllr simpr jm2.25 syl121anc oveq2 oveq2d cc zcn pncan3
      wrex syl2anr ad2antlr sylan9eqr eqidd acongeq12d rexlimdva2 sylbid simprl
      mpbid znegcl ad2antll zsubcld w3a cn0 frmx fovcl simplrl frmy 3jca negcld
      nn0zd rmyneg acongneg2 jaod ) AFUAUBZGZDHGZIZBHGZCHGZIZIZFDUCJZBCKJZLMZAD
      UDJZABNJZACNJZKJLMXAXBXCOZKJLMZTZWRBCOZKJZLMZWQWTEUEZWRUCJZWSPZEHVEZXFWQW
      RHGZWSHGZWTXMUFWQFHGWLXNUGWKWLWPUHFDUIUJZWPXOWMBCUKULEWRWSUMQWQXLXFEHWQXJ
      HGZIZXLIZXAACXKRJZNJZXCKJLMXAYAXDKJLMTZXFXRYBXLXRWKWOWLXQYBWKWLWPXQUNZWMW
      NWOXQUOZWKWLWPXQUPZWQXQUQZAXJCDURUSSXSXAYAXBXCXCXLXRYAACWSRJZNJXBXLXTYGAN
      XKWSCRUTVAXRYGBANWPYGBPZWMXQWOCVBGBVBGZYHWNCVCZBVCZCBVDVFVGVAVHXSXCVIVJVN
      VKVLWQXIXKXHPZEHVEZXFWQXNXHHGXIYMUFXPWQBXGWMWNWOVMWOXGHGZWMWNCVOVPZVQEWRX
      HUMQWQYLXFEHXRYLIZXAHGZXBHGZXCHGZVRZXEXAXBXDOKJLMTZXFXRYTYLXRYQYRYSXRWKWL
      YQYCYEWMXAADVSWJHUDVTWAWFQXRWKWNYRYCWMWNWOXQWBABHWJHNWCWAQXRWKWOYSYCYDACH
      WJHNWCWAQWDSYPXAAXGXKRJZNJZAXGNJZKJLMXAUUCUUDOKJLMTZUUAXRUUEYLXRWKYNWLXQU
      UEYCWQYNXQYOSYEYFAXJXGDURUSSYPXAUUCXBUUDXDYLXRUUCAXGXHRJZNJXBYLUUBUUFANXK
      XHXGRUTVAXRUUFBANWPUUFBPZWMXQWOXGVBGYIUUGWNWOCYJWEYKXGBVDVFVGVAVHXRUUDXDP
      ZYLXRWKWOUUHYCYDACWGQSVJVNXAXBXCWHQVKVLWI $.
  $}

  $( Lemma for ~ jm2.26 .  Use ~ acongrep to find K', M' ~~ K, M in [ 0,N ].
     Thus Y(K') ~~ Y(M') and both are small; K' = M' on pain of contradicting
     2.24, so K ~~ M. (Contributed by Stefan O'Rear, 3-Oct-2014.) $)
  jm2.26lem3 $p |- ( ( ( A e. ( ZZ>= ` 2 ) /\ N e. NN ) /\ ( K e. ( 0 ... N )
      /\ M e. ( 0 ... N ) ) /\ ( ( A rmX N ) || ( ( A rmY K ) - ( A rmY M ) )
      \/ ( A rmX N ) || ( ( A rmY K ) - -u ( A rmY M ) ) ) ) -> K = M ) $=
    ( cfv wcel wa cc0 co crmy wbr wceq wne cz adantr ad2antlr syl2anc cle mpbid
    cabs c2 cuz cn cfz crmx cmin cdvds cneg wo caddc clt w3a wn simplll elfzelz
    rmyabs cr zred elfzle1 absidd oveq2d eqtrd adantl oveq12d c1 fovcl readdcld
    frmy simpllr nnzd peano2zm syl frmx nn0red elfzle2 wb lermy syl3anc simplrr
    cn0 wi le2add syl22anc mp2and zcnd addcomd id necomd neeqtrd neneqd adantll
    simpr nnnn0 nn0uz eleqtrdi ad4antlr simprr ad2antrr fzm1 orel2 sylc simplrl
    biimpa eqbrtrd nnnn0d mpjaodan jm2.24 lelttrd rmyeq necon3bid 0red ad2antll
    le0neg2d letri3 biimpar simplr eqtr3d cc recnd negeq0d mpbird mpdan necon3d
    eqtr4d imp znegcld rmyneg 3jca negsubd fveq2d negcld addcld abstrid zsubcld
    ex abscld ltnled subne0d dvdsleabs mtod nn0zd absneg eqcomd breqtrrd simpr1
    nnz eqbrtrrd simpr2 subnegd simpr3 jca pm4.56 sylib syld necon4ad 3impia )
    AUAUBEZFZDUCFZGZBHDUDIZFZCUVAFZGZADUEIZABJIZACJIZUFIZUGKZUVEUVFUVGUHZUFIZUG
    KZUIZBCLZUUTUVDGZUVMBCUVOBCMZUVFTEZUVGTEZUJIZUVEUKKZUVFUVGMZUVFUVJMZULZUVMU
    MZUVOUVPUWCUVOUVPGZUVTUWAUWBUWEUVSUVFUVGUJIZUVEUKUWEUVQUVFUVRUVGUJUWEUVQABT
    EZJIZUVFUWEUURBNFZUVQUWHLUURUUSUVDUVPUNZUVDUWIUUTUVPUVBUWIUVCBHDUOOZPZABUPQ
    UWEUWGBAJUWEBUVDBUQFZUUTUVPUVDBUWKURZPUVDHBRKZUUTUVPUVBUWOUVCBHDUSOZPUTVAVB
    UWEUVRACTEZJIZUVGUWEUURCNFZUVRUWRLUWJUVDUWSUUTUVPUVCUWSUVBCHDUOZVCZPZACUPQU
    WEUWQCAJUWECUVDCUQFZUUTUVPUVDCUXAURZPUVDHCRKZUUTUVPUVCUXEUVBCHDUSZVCPUTVAVB
    VDUWEUWFADVEUFIZJIZADJIZUJIZUVEUWEUVFUVGUWEUVFUWEUURUWIUVFNFZUWJUWLABNUUQNJ
    VHVFZQZURZUWEUVGUWEUURUWSUVGNFZUWJUXBACNUUQNJVHVFZQZURZVGUWEUXHUXIUWEUXHUWE
    UURUXGNFZUXHNFUWJUWEDNFZUXSUWEDUURUUSUVDUVPVIZVJZDVKVLZAUXGNUUQNJVHVFQURZUW
    EUXIUWEUURUXTUXINFUWJUYBADNUUQNJVHVFQURZVGUWEUVEUWEUURUXTUVEVTFUWJUYBADVTUU
    QNUEVMVFZQVNUWEBHUXGUDIZFZUWFUXJRKZBDLZUWEUYHGZUVFUXHRKZUVGUXIRKZUYIUYKBUXG
    RKZUYLUYHUYNUWEBHUXGVOVCUWEUYNUYLVPZUYHUWEUURUWIUXSUYOUWJUWLUYCABUXGVQVROSU
    WEUYMUYHUWECDRKZUYMUWEUVCUYPUUTUVBUVCUVPVSZCHDVOVLUWEUURUWSUXTUYPUYMVPUWJUX
    BUYBACDVQVRSOUWEUYLUYMGUYIWAZUYHUWEUVFUQFZUVGUQFZUXHUQFZUXIUQFZUYRUXNUXRUYD
    UYEUVFUVGUXHUXIWBWCOWDUWEUYJGZUWFUVGUVFUJIZUXJRUWEUWFVUDLUYJUWEUVFUVGUWEUVF
    UXMWEUWEUVGUXQWEWFOVUCUVGUXHRKZUVFUXIRKZVUDUXJRKZVUCCUXGRKZVUEVUCCUYGFZVUHV
    UCCDLZUMZVUIVUJUIZVUIUVPUYJVUKUVOUVPUYJGZCDVUMCBDUVPCBMUYJUVPBCUVPWGWHOUVPU
    YJWLWIWJWKVUCDHUBEZFZUVCVULUUSVUOUURUVDUVPUYJUUSDVTVUNDWMWNWOWPUVOUVCUVPUYJ
    UUTUVBUVCWQWRVUOUVCVULCHDWSXCQVUJVUIWTXACHUXGVOVLUWEVUHVUEVPZUYJUWEUURUWSUX
    SVUPUWJUXBUYCACUXGVQVROSUWEVUFUYJUWEBDRKZVUFUWEUVBVUQUUTUVBUVCUVPXBZBHDVOVL
    UWEUURUWIUXTVUQVUFVPUWJUWLUYBABDVQVRSOUWEVUEVUFGVUGWAZUYJUWEUYTUYSVUAVUBVUS
    UXRUXNUYDUYEUVGUVFUXHUXIWBWCOWDXDUWEVUOUVBUYHUYJUIZUWEDVTVUNUWEDUYAXEWNWOVU
    RVUOUVBVUTBHDWSXCQXFUWEUURUXTUXJUVEUKKUWJUYBADXGQXHXDUWEUVPUWAUVOUVPWLUWEUU
    RUWIUWSUVPUWAVPUWJUWLUXBUURUWIUWSULBCUVFUVGABCXIXJVRSUWEUVFACUHZJIZUVJUWEBV
    VAMZUVFVVBMZUVOUVPVVCUVOBVVABCUVOBVVALZUVNUVOVVEGZBHLZUVNVVFUWMHUQFZBHRKZUW
    OVVGUVDUWMUUTVVEUWNPVVFXKVVFBVVAHRUVOVVEWLUVOVVAHRKZVVEUVOUXEVVJUVCUXEUUTUV
    BUXFXLUVOCUVDUXCUUTUXDVCZXMSOXDUVDUWOUUTVVEUWPPUWMVVHGVVGVVIUWOGBHXNXOWCVVF
    VVGGZBHCVVFVVGWLZVVLCHLVVAHLVVLBVVAHUVOVVEVVGXPVVMXQVVLCUVOCXRFVVEVVGUVOCVV
    KXSWRXTYAYDYBYOYCYEUWEUURUWIVVANFZVVCVVDVPUWJUWLUWECUWEUVCUWSUYQUWTVLYFUURU
    WIVVNULBVVAUVFVVBABVVAXIXJVRSUWEUURUWSVVBUVJLUWJUXBACYGQWIYHYOUVOUWCUWDUVOU
    WCGZUVIUMZUVLUMZGUWDVVOVVPVVQVVOUVIUVEUVHTEZRKZVVOVVRUVEUKKVVSUMVVOUVFUVJUJ
    IZTEZVVRUVEUKVVOVVTUVHTVVOUVFUVGVVOUVFVVOUURUWIUXKUURUUSUVDUWCUNZUVDUWIUUTU
    WCUWKPUXLQZWEZVVOUVGVVOUURUWSUXOVWBUVDUWSUUTUWCUXAPUXPQZWEZYIYJVVOVWAUVSUVE
    VVOVVTVVOUVFUVJVWDVVOUVGVWFYKZYLYPVVOUVQUVRVVOUVFVWDYPVVOUVGVWFYPVGZVVOUVEV
    VOUURUXTUVENFZVWBUUTUXTUVDUWCUUSUXTUURDUUFVCWRUURUXTGUVEUYFUUAQZURZVVOVWAUV
    QUVJTEZUJIUVSRVVOUVFUVJVWDVWGYMVVOUVRVWLUVQUJVVOUVGXRFZUVRVWLLVWFVWMVWLUVRU
    VGUUBUUCVLVAUUDUVOUVTUWAUWBUUEZXHUUGVVOVVRUVEVVOUVHVVOUVHVVOUVFUVGVWCVWEYNZ
    WEYPVWKYQSVVOVWIUVHNFUVHHMUVIVVSWAVWJVWOVVOUVFUVGVWDVWFUVOUVTUWAUWBUUHYRUVE
    UVHYSVRYTVVOUVLUVEUVKTEZRKZVVOVWPUVEUKKVWQUMVVOVWPUWFTEZUVEUKVVOUVKUWFTVVOU
    VFUVGVWDVWFUUIYJVVOVWRUVSUVEVVOUWFVVOUVFUVGVWDVWFYLYPVWHVWKVVOUVFUVGVWDVWFY
    MVWNXHXDVVOVWPUVEVVOUVKVVOUVKVVOUVFUVJVWCVVOUVGVWEYFYNZWEYPVWKYQSVVOVWIUVKN
    FUVKHMUVLVWQWAVWJVWSVVOUVFUVJVWDVWGUVOUVTUWAUWBUUJYRUVEUVKYSVRYTUUKUVIUVLUU
    LUUMYOUUNUUOUUP $.

  ${
    $d A k m $.  $d N k m $.  $d K k m $.  $d M k m $.
    $( Lemma 2.26 of [JonesMatijasevic] p. 697, the "second step down lemma".
       (Contributed by Stefan O'Rear, 2-Oct-2014.) $)
    jm2.26 $p |- ( ( ( A e. ( ZZ>= ` 2 ) /\ N e. NN ) /\ ( K e. ZZ /\ M e. ZZ )
        ) -> ( ( ( A rmX N ) || ( ( A rmY K ) - ( A rmY M ) ) \/ ( A rmX N ) ||
        ( ( A rmY K ) - -u ( A rmY M ) ) ) <-> ( ( 2 x. N ) || ( K - M ) \/ ( 2
        x. N ) || ( K - -u M ) ) ) ) $=
      ( vm vk c2 wcel wa cz co crmy cmin cdvds wbr cneg wo wi fovcl syl2anc cuz
      cfv cn crmx cmul cc0 cfz wrex acongrep ad2ant2l ad2ant2lr w3a simpl1l nnz
      cv 2z adantl syl zmulcl sylancr simplrl 3ad2antl1 simpl3l simplrr simpl2r
      elfzelzd weq wb simpl2l simplll cn0 frmx nn0zd jm2.26a syl22anc mpd simpr
      acongtr syl222anc simpl3r acongsym syl31anc jm2.26lem3 syl121anc id eqidd
      frmy acongeq12d mpbid 3exp1 expd rexlimdv sylanl2 impbid ) AGUAUBZHZDUCHZ
      IZBJHZCJHZIZIZADUDKZABLKZACLKZMKNOXCXDXEPZMKNOQZGDUEKZBCMKNOXHBCPZMKNOQZX
      BXHEUOZCMKNOXHXKXIMKNOQZEUFDUGKZUHZXGXJRZWQWTXNWPWSDCEUIUJXBXLXOEXMXBXKXM
      HZXLXOXBXHFUOZBMKNOXHXQBPZMKNOQZFXMUHZXPXLIZXORZWQWSXTWPWTDBFUIUKXBXSYBFX
      MXBXQXMHZXSYBXBYCXSIZYAXGXJXBYDYAULZXGIZXHJHZWSXKJHZWTXHBXKMKNOXHBXKPZMKN
      OQZXLXJYFGJHDJHZYGUPYFWRYKWRXAYDYAXGUMZWQYKWPDUNZUQURZGDUSUTZXBYDXGWSYAWR
      WSWTXGVAVBZYFXKUFDXPXLXBYDXGVCZVFZXBYDXGWTYAWRWSWTXGVDVBZYFYGYHWSXHXKBMKN
      OXHXKXRMKNOQZYJYOYRYPYFXSYTYCXSXBYAXGVEZYFFEVGZXSYTVHYFWRYCXPXCAXQLKZAXKL
      KZMKNOXCUUCUUDPZMKNOQZUUBYLYCXSXBYAXGVIZYQYFXCJHZUUCJHZXEJHZUUDJHZXCUUCXE
      MKNOXCUUCXFMKNOQZXCXEUUDMKNOXCXEUUEMKNOQZUUFYFWPYKUUHXBYDXGWPYAWPWQXAXGVJ
      VBZYNWPYKIXCADVKWOJUDVLSVMTZYFWPXQJHZUUIUUNYFXQUFDUUGVFZAXQJWOJLWGSTZYFWP
      WTUUJUUNYSACJWOJLWGSTZYFWPYHUUKUUNYRAXKJWOJLWGSTYFUUHUUIXDJHZUUJXCUUCXDMK
      NOXCUUCXDPMKNOQZXGUULUUOUURYFWPWSUUTUUNYPABJWOJLWGSTUUSYFXSUVAUUAYFWPYKUU
      PWSXSUVARUUNYNUUQYPAXQBDVNVOVPYEXGVQXCUUCXDXEVRVSYFXHCXKMKNOXHCYIMKNOQZUU
      MYFYGYHWTXLUVBYOYRYSXPXLXBYDXGVTZXHXKCWAWBYFWPYKWTYHUVBUUMRUUNYNYSYRACXKD
      VNVOVPXCUUCXEUUDVRVSAXQXKDWCWDUUBXHXQXKBBUUBWEUUBBWFWHURWIXHXKBWAWBUVCXHB
      XKCVRVSWJWKWLVPWKWLVPWQWPYKXAXJXGRYMABCDVNWMWN $.
  $}

  ${
    $d a b A $.  $d a b B $.  $d a b N $.
    $( Lemma 2.15 of [JonesMatijasevic] p. 695. ` rmY ` is a polynomial for
       fixed N, so has the expected congruence property.  (Contributed by
       Stefan O'Rear, 1-Oct-2014.) $)
    jm2.15nn0 $p |- ( ( A e. ( ZZ>= ` 2 ) /\ B e. ( ZZ>= ` 2 ) /\ N e. NN0 ) ->
        ( A - B ) || ( ( A rmY N ) - ( B rmY N ) ) ) $=
      ( c2 wcel cmin co crmy cdvds wbr wi cc0 c1 cz syl2anc wceq oveq12d breq2d
      oveq2 imbi2d va vb cuz cfv cn0 wa cv eluzelz zsubcl syl2an congid sylancl
      caddc 0z rmy0 oveqan12d breqtrrd 1z rmy1 cn pm3.43 w3a 3ad2ant2 2z simp2l
      cmul a1i 3ad2ant1 frmy fovcl adantr zmulcld simp2r adantl peano2zm simp3r
      nnz syl iddvds congmul syl322anc simp3l congsub 3exp a2d syl5 weq 2nn0ind
      rmyluc impcom 3impa ) ADUCUDZEZBWLEZCUEEZABFGZACHGZBCHGZFGZIJZWOWMWNUFZWT
      XAWPAUAUGZHGZBXBHGZFGZIJZKXAWPALHGZBLHGZFGZIJZKXAWPAMHGZBMHGZFGZIJZKXAWPA
      UBUGZMFGZHGZBXPHGZFGZIJZKZXAWPAXOHGZBXOHGZFGZIJZKZXAWPAXOMUMGZHGZBYGHGZFG
      ZIJZKZXAWTKUAUBCXAWPLLFGZXIIXAWPNEZLNEWPYMIJWMANEZBNEZYNWNDAUHZDBUHZABUIU
      JZUNWPLUKULWMWNXGLXHLFAUOBUOUPUQXAWPMMFGZXMIXAYNMNEWPYTIJYSURWPMUKULWMWNX
      KMXLMFAUSBUSUPUQYAYFUFXAXTYEUFZKXOUTEZYLXAXTYEVAUUBXAUUAYKUUBXAUUAYKUUBXA
      UUAVBZWPDYBAVFGZVFGZXQFGZDYCBVFGZVFGZXRFGZFGZYJIUUCYNUUENEUUHNEXQNEZXRNEZ
      WPUUEUUHFGIJZXTWPUUJIJXAUUBYNUUAYSVCZUUCDUUDDNEZUUCVDVGZUUCYBAUUCWMXONEZY
      BNEZUUBWMWNUUAVEZUUBXAUUQUUAXOVQZVHZAXONWLNHVIVJOZXAUUBYOUUAWMYOWNYQVKVCZ
      VLZVLUUCDUUGUUPUUCYCBUUCWNUUQYCNEZUUBWMWNUUAVMZUVABXONWLNHVIVJOZXAUUBYPUU
      AWNYPWMYRVNVCZVLZVLUUCWMXPNEZUUKUUSUUBXAUVJUUAUUBUUQUVJUUTXOVOVRVHZAXPNWL
      NHVIVJOUUCWNUVJUULUVFUVKBXPNWLNHVIVJOUUCYNUUOUUOUUDNEUUGNEWPDDFGIJZWPUUDU
      UGFGIJZUUMUUNUUPUUPUVDUVIUUCYNUUOUVLUUNVDWPDUKULUUCYNUURUVEYOYPYEWPWPIJZU
      VMUUNUVBUVGUVCUVHUUBXAXTYEVPUUCYNUVNUUNWPVSVRWPYBYCABVTWAWPDDUUDUUGVTWAUU
      BXAXTYEWBWPUUEUUHXQXRWCWAUUCYHUUFYIUUIFUUCWMUUQYHUUFPUUSUVAAXOWIOUUCWNUUQ
      YIUUIPUVFUVABXOWIOQUQWDWEWFXBLPZXFXJXAUVOXEXIWPIUVOXCXGXDXHFXBLAHSXBLBHSQ
      RTXBMPZXFXNXAUVPXEXMWPIUVPXCXKXDXLFXBMAHSXBMBHSQRTXBXPPZXFXTXAUVQXEXSWPIU
      VQXCXQXDXRFXBXPAHSXBXPBHSQRTUAUBWGZXFYEXAUVRXEYDWPIUVRXCYBXDYCFXBXOAHSXBX
      OBHSQRTXBYGPZXFYKXAUVSXEYJWPIUVSXCYHXDYIFXBYGAHSXBYGBHSQRTXBCPZXFWTXAUVTX
      EWSWPIUVTXCWQXDWRFXBCAHSXBCBHSQRTWHWJWK $.
  $}

  ${
    $d a b A $.  $d a b N $.
    $( Lemma 2.16 of [JonesMatijasevic] p. 695.  This may be regarded as a
       special case of ~ jm2.15nn0 if ` rmY ` is redefined as described in
       ~ rmyluc .  (Contributed by Stefan O'Rear, 1-Oct-2014.) $)
    jm2.16nn0 $p |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. NN0 ) -> ( A - 1 ) || ( ( A
        rmY N ) - N ) ) $=
      ( wcel c2 c1 cmin co crmy cdvds wbr wi cz cmul 3adant3 wceq oveq12d oveq2
      cc0 wa id va vb cn0 cuz cfv cv caddc eluzelz peano2zm syl 0z sylancl rmy0
      congid oveq1d breqtrrd 1z rmy1 pm3.43 w3a adantl eluzel2 simpr nnz adantr
      cn frmy fovcl syl2anc zmulcld zmulcl 3jca jca jctir simp3r iddvds congmul
      syl112anc simp3l congsub rmyluc nncn mulridd oveq2d 2timesd eqtrd pnncand
      1cnd eqtr2d 3exp a2d syl5 breq2d imbi2d weq 2nn0ind impcom ) BUCCADUDUEZC
      ZAEFGZABHGZBFGZIJZWSWTAUAUFZHGZXDFGZIJZKWSWTARHGZRFGZIJZKWSWTAEHGZEFGZIJZ
      KWSWTAUBUFZEFGZHGZXOFGZIJZKZWSWTAXNHGZXNFGZIJZKZWSWTAXNEUGGZHGZYDFGZIJZKZ
      WSXCKUAUBBWSWTRRFGZXIIWSWTLCZRLCWTYIIJWSALCZYJDAUHZAUIZUJZUKWTRUNULWSXHRR
      FAUMUOUPWSWTEEFGZXLIWSYJELCZWTYOIJYNUQWTEUNULWSXKEEFAURUOUPXSYCSWSXRYBSZK
      XNVFCZYHWSXRYBUSYRWSYQYGYRWSYQYGYRWSYQUTZWTDXTAMGZMGZXPFGZDXNEMGZMGZXOFGZ
      FGZYFIYSYJUUALCZUUDLCZUTZXPLCZXOLCZSZWTUUAUUDFGIJZXRWTUUFIJYRWSUUIYQYRWSS
      ZYJUUGUUHUUNYKYJWSYKYRYLVAZYMUJZUUNDYTWSDLCZYRDAVBVAZUUNXTAUUNWSXNLCZXTLC
      ZYRWSVCZYRUUSWSXNVDVEZAXNLWRLHVGVHVIZUUOVJZVJUUNDUUCUURUUNUUSYPUUCLCZUVBU
      QXNEVKULZVJVLNYRWSUULYQUUNUUJUUKUUNWSUUKUUJUVAUUNUUSUUKUVBXNUIUJZAXOLWRLH
      VGVHVIUVGVMNYSYJUUQUUQUTZYTLCZUVESZWTDDFGIJZWTYTUUCFGIJZUUMYRWSUVHYQUUNYJ
      UUQUUQUUPUURUURVLNYRWSUVJYQUUNUVIUVEUVDUVFVMNYRWSUVKYQUUNYJUUQUVKUUPUURWT
      DUNVINYSYJUUTUUSUTZYKYPSZYBWTWTIJZUVLYRWSUVMYQUUNYJUUTUUSUUPUVCUVBVLNYRWS
      UVNYQUUNYKYPUUOUQVNNYRWSXRYBVOYRWSUVOYQUUNYJUVOUUPWTVPUJNWTXTXNAEVQVRWTDD
      YTUUCVQVRYRWSXRYBVSWTUUAUUDXPXOVTVRYRWSYFUUFOYQUUNYEUUBYDUUEFUUNWSUUSYEUU
      BOUVAUVBAXNWAVIYRYDUUEOWSYRUUEXNXNUGGZXOFGYDYRUUDUVPXOFYRUUDDXNMGUVPYRUUC
      XNDMYRXNXNWBZWCWDYRXNUVQWEWFUOYRXNXNEUVQUVQYRWHWGWIVEPNUPWJWKWLXDROZXGXJW
      SUVRXFXIWTIUVRXEXHXDRFXDRAHQUVRTPWMWNXDEOZXGXMWSUVSXFXLWTIUVSXEXKXDEFXDEA
      HQUVSTPWMWNXDXOOZXGXRWSUVTXFXQWTIUVTXEXPXDXOFXDXOAHQUVTTPWMWNUAUBWOZXGYBW
      SUWAXFYAWTIUWAXEXTXDXNFXDXNAHQUWATPWMWNXDYDOZXGYGWSUWBXFYFWTIUWBXEYEXDYDF
      XDYDAHQUWBTPWMWNXDBOZXGXCWSUWCXFXBWTIUWCXEXAXDBFXDBAHQUWCTPWMWNWPWQ $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  X and Y sequences 4: Diophantine representability of Y
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    jm2.27a1 $e |- ( ph -> A e. ( ZZ>= ` 2 ) ) $.
    jm2.27a2 $e |- ( ph -> B e. NN ) $.
    jm2.27a3 $e |- ( ph -> C e. NN ) $.
    ${
      jm2.27a4 $e |- ( ph -> D e. NN0 ) $.
      jm2.27a5 $e |- ( ph -> E e. NN0 ) $.
      jm2.27a6 $e |- ( ph -> F e. NN0 ) $.
      jm2.27a7 $e |- ( ph -> G e. NN0 ) $.
      jm2.27a8 $e |- ( ph -> H e. NN0 ) $.
      jm2.27a9 $e |- ( ph -> I e. NN0 ) $.
      jm2.27a10 $e |- ( ph -> J e. NN0 ) $.
      jm2.27a11 $e |- ( ph -> ( ( D ^ 2 ) - ( ( ( A ^ 2 ) - 1 ) x. ( C ^ 2 ) )
          ) = 1 ) $.
      jm2.27a12 $e |- ( ph -> ( ( F ^ 2 ) - ( ( ( A ^ 2 ) - 1 ) x. ( E ^ 2 ) )
          ) = 1 ) $.
      jm2.27a13 $e |- ( ph -> G e. ( ZZ>= ` 2 ) ) $.
      jm2.27a14 $e |- ( ph -> ( ( I ^ 2 ) - ( ( ( G ^ 2 ) - 1 ) x. ( H ^ 2 ) )
          ) = 1 ) $.
      jm2.27a15 $e |- ( ph -> E = ( ( J + 1 ) x. ( 2 x. ( C ^ 2 ) ) ) ) $.
      jm2.27a16 $e |- ( ph -> F || ( G - A ) ) $.
      jm2.27a17 $e |- ( ph -> ( 2 x. C ) || ( G - 1 ) ) $.
      jm2.27a18 $e |- ( ph -> F || ( H - C ) ) $.
      jm2.27a19 $e |- ( ph -> ( 2 x. C ) || ( H - B ) ) $.
      jm2.27a20 $e |- ( ph -> B <_ C ) $.

      ${
        jm2.27a21 $e |- ( ph -> P e. ZZ ) $.
        jm2.27a22 $e |- ( ph -> D = ( A rmX P ) ) $.
        jm2.27a23 $e |- ( ph -> C = ( A rmY P ) ) $.
        jm2.27a24 $e |- ( ph -> Q e. ZZ ) $.
        jm2.27a25 $e |- ( ph -> F = ( A rmX Q ) ) $.
        jm2.27a26 $e |- ( ph -> E = ( A rmY Q ) ) $.
        jm2.27a27 $e |- ( ph -> R e. ZZ ) $.
        jm2.27a28 $e |- ( ph -> I = ( G rmX R ) ) $.
        jm2.27a29 $e |- ( ph -> H = ( G rmY R ) ) $.
        $( Lemma for ~ jm2.27 .  Reverse direction after existential
           quantifiers are expanded.  (Contributed by Stefan O'Rear,
           4-Oct-2014.) $)
        jm2.27a $p |- ( ph -> C = ( A rmY B ) ) $=
          ( crmy co wceq c2 cmul cmin cdvds wbr cneg wo cz wcel 2z nnzd sylancr
          zmulcl nn0zd congsym syl22anc c1 peano2zm syl zsubcld cuz cfv cn0 cc0
          cle nn0ge0d rmy0 eqcomd 3brtr4d wb 0zd syl3anc mpbird elnn0z sylanbrc
          lermy jm2.16nn0 syl2anc oveq1d breqtrrd dvdstrd congtr syl222anc orcd
          caddc zsqcl dvdsmul2 wi peano2zd dvdsmultr2 mpd eqtr3d 3brtr3d cn clt
          cexp zred nn0p1nn nngt0d nnsqcld nnmulcl mulgt0d ltrmy elnnz jm2.20nn
          2nn mpbid eqeltrrd muldvds2 eqbrtrd a1i nnnn0d elfz2nn0 syl3anbrc cfz
          dvdscmul crmx frmy fovcl eluzelz jm2.15nn0 oveq12d jm2.26 dvdsacongtr
          eqbrtrrd acongtr rmygeid acongeq oveq2d eqtr4d ) ADBFVDVEZBCVDVEUQACF
          BVDACFVFZVGDVHVEZCFVIVEVJVKUUSCFVLZVIVEVJVKVMZAUUSVNVOZCVNVOZHVNVOZFV
          NVOZUUSCHVIVEVJVKZUUSCHVLVIVEVJVKZVMUUSHFVIVEZVJVKUUSHUUTVIVEZVJVKVMZ
          UVAAVGVNVOZDVNVOZUVBVPADQVQZVGDVSVRZACPVQZVAUOAUVFUVGAUVBUVCLVNVOZUVD
          UUSCLVIVEVJVKZUUSLHVIVEZVJVKUVFUVNUVOALUBVTZVAAUVBUVPUVCUUSLCVIVEVJVK
          UVQUVNUVSUVOUMUUSLCWAWBAUUSKWCVIVEZUVRUVNAKVNVOZUVTVNVOAKUAVTZKWDWEAL
          HUVSVAWFUKAUVTKHVDVEZHVIVEZUVRVJAKVGWGWHZVOZHWIVOZUVTUWDVJVKUGAUVDWJH
          WKVKZUWGVAAUWHKWJVDVEZUWCWKVKZAWJLUWIUWCWKALUBWLAUWFUWIWJVFUGKWMWEALU
          WCVCWNWOAUWFWJVNVOZUVDUWHUWJWPUGAWQZVAKWJHXBWRWSHWTXAZKHXCXDALUWCHVIV
          CXEXFXGUUSCLHXHXIXJAVGGVHVEZVNVOZUVDUVEUVBUUSUWNVJVKZUWNUVHVJVKUWNUVI
          VJVKVMZUVJAUVKGVNVOZUWOVPURVGGVSVRVAUOUVNADGVJVKZUWPADUUQGVJUQAFUUQVH
          VEGVJVKZUUQGVJVKZAUUQVGYBVEZBGVDVEZVJVKZUWTADVGYBVEZNWCXKVEZVGUXEVHVE
          ZVHVEZUXBUXCVJAUXEUXGVJVKZUXEUXHVJVKZAUVKUXEVNVOZUXIVPAUVLUXKUVMDXLWE
          ZVGUXEXMVRAUXKUXFVNVOUXGVNVOZUXIUXJXNUXLANANUDVTXOZAUVKUXKUXMVPUXLVGU
          XEVSVRZUXEUXFUXGXPWRXQADUUQVGYBUQXEAIUXHUXCUIUTXRXSABUWEVOZGXTVOZFXTV
          OZUXDUWTWPOAUWRWJGYAVKZUXQURAUXSBWJVDVEZUXCYAVKZAWJIUXTUXCYAAWJUXHIYA
          AUXFUXGAUXFUXNYCAUXGUXOYCAUXFANWIVOUXFXTVOUDNYDWEYEAUXGAVGXTVOUXEXTVO
          UXGXTVOYLADQYFVGUXEYGVRYEYHUIXFAUXPUXTWJVFOBWMWEZAIUXCUTWNWOAUXPUWKUW
          RUXSUYAWPOUWLURBWJGYIWRWSGYJXAZAUVEWJFYAVKZUXRUOAUYDUXTUUQYAVKZAWJDUX
          TUUQYAADQYEUYBADUUQUQWNWOAUXPUWKUVEUYDUYEWPOUWLUOBWJFYIWRWSFYJXAZBGFY
          KWRYMAUVEUUQVNVOZUWRUWTUXAXNUOADUUQVNUQUVMYNZURFUUQGYOWRXQYPAUVLUWRUV
          KUWSUWPXNUVMURUVKAVPYQVGDGUUBWRXQABGUUCVEZBHVDVEZUUQVIVEVJVKZUYIUYJUU
          QVLVIVEVJVKZVMZUWQAUYKUYLAUYIVNVOUYJVNVOZUWCVNVOUYGUYIUYJUWCVIVEZVJVK
          UYIUWCUUQVIVEZVJVKUYKAJUYIVNUSAJTVTZYNZAUXPUVDUYNOVABHVNUWEVNVDUUDUUE
          XDZALUWCVNVCUVSYNZUYHAUYIBKVIVEZUYOUYRABKAUXPBVNVOZOVGBUUFWEZUWBWFAUY
          JUWCUYSUYTWFAJUYIVUAVJUSAJVNVOUWAVUBJKBVIVEVJVKJVUAVJVKUYQUWBVUCUJJKB
          WAWBUUKAUXPUWFUWGVUAUYOVJVKOUGUWMBKHUUGWRXGAJLDVIVEUYIUYPVJULUSALUWCD
          UUQVIVCUQUUHXSUYIUYJUWCUUQXHXIXJAUXPUXQUVDUVEUYMUWQWPOUYCVAUOBHFGUUIW
          BYMUWNHFUUSUUJXIUUSCHFUULXIADXTVOCWJDUUAVEZVOZFVUDVOZUURUVAWPQACWIVOD
          WIVOZCDWKVKVUEACPYRADQYRZUNCDYSYTAFWIVOZVUGFDWKVKVUFAFUYFYRZVUHAFUUQD
          WKAUXPVUIFUUQWKVKOVUJBFUUMXDUQXFFDYSYTDCFUUNWRWSUUOUUP $.
      $}

      ${
        $d ph p q r $.  $d A p q r $.  $d B p q r $.  $d C p q r $.
        $d D p q r $.  $d E q r $.  $d F q r $.  $d G r $.  $d H r $.
        $d I r $.
        $( Lemma for ~ jm2.27 .  Expand existential quantifiers for reverse
           direction.  (Contributed by Stefan O'Rear, 4-Oct-2014.) $)
        jm2.27b $p |- ( ph -> C = ( A rmY B ) ) $=
          ( vp vq vr cv crmx co wceq crmy wa cz c2 cexp cmin cmul wrex cuz wcel
          c1 cfv cn0 wb nnzd rmxycomplete mpbid adantr nn0zd ad2antrr ad3antrrr
          syl3anc cn caddc cdvds wbr cle simprl simprrl simprrr ad2antlr simprr
          simplrl jm2.27a rexlimddv ) AEBULUOZUPUQURZDBWNUSUQURZUTZDBCUSUQURZUL
          VAAEVBVCUQBVBVCUQVIVDUQZDVBVCUQZVEUQVDUQVIURZWQULVAVFZUBABVBVGVJZVHZE
          VKVHZDVAVHXAXBVLLOADNVMBULEDVNVTVOAWNVAVHZWQUTZUTZGBUMUOZUPUQURZFBXIU
          SUQURZUTZWRUMVAXHGVBVCUQWSFVBVCUQVEUQVDUQVIURZXLUMVAVFZAXMXGUCVPXHXDG
          VKVHZFVAVHZXMXNVLAXDXGLVPAXOXGQVPAXPXGAFPVQVPBUMGFVNVTVOXHXIVAVHZXLUT
          ZUTZJHUNUOZUPUQURZIHXTUSUQURZUTZWRUNVAXSJVBVCUQHVBVCUQVIVDUQIVBVCUQVE
          UQVDUQVIURZYCUNVAVFZAYDXGXRUEVRXSHXCVHZJVKVHZIVAVHZYDYEVLAYFXGXRUDVRA
          YGXGXRTVRAYHXGXRAISVQVRHUNJIVNVTVOXSXTVAVHZYCUTZUTBCDEWNXIXTFGHIJKAXD
          XGXRYJLVSACWAVHXGXRYJMVSADWAVHXGXRYJNVSAXEXGXRYJOVSAFVKVHXGXRYJPVSAXO
          XGXRYJQVSAHVKVHXGXRYJRVSAIVKVHXGXRYJSVSAYGXGXRYJTVSAKVKVHXGXRYJUAVSAX
          AXGXRYJUBVSAXMXGXRYJUCVSAYFXGXRYJUDVSAYDXGXRYJUEVSAFKVIWBUQVBWTVEUQVE
          UQURXGXRYJUFVSAGHBVDUQWCWDXGXRYJUGVSAVBDVEUQZHVIVDUQWCWDXGXRYJUHVSAGI
          DVDUQWCWDXGXRYJUIVSAYKICVDUQWCWDXGXRYJUJVSACDWEWDXGXRYJUKVSXHXFXRYJAX
          FWQWFVRXHWOXRYJAXFWOWPWGVRXHWPXRYJAXFWOWPWHVRXHXQXLYJWKXRXJXHYJXQXJXK
          WFWIXRXKXHYJXQXJXKWJWIXSYIYCWFXSYIYAYBWGXSYIYAYBWHWLWMWMWM $.
      $}
    $}

    ${
      jm2.27c4 $e |- ( ph -> C = ( A rmY B ) ) $.
      jm2.27c5 $e |- D = ( A rmX B ) $.
      jm2.27c6 $e |- Q = ( B x. ( A rmY B ) ) $.
      jm2.27c7 $e |- E = ( A rmY ( 2 x. Q ) ) $.
      jm2.27c8 $e |- F = ( A rmX ( 2 x. Q ) ) $.
      jm2.27c9 $e |- G = ( A + ( ( F ^ 2 ) x. ( ( F ^ 2 ) - A ) ) ) $.
      jm2.27c10 $e |- H = ( G rmY B ) $.
      jm2.27c11 $e |- I = ( G rmX B ) $.
      jm2.27c12 $e |- J = ( ( E / ( 2 x. ( C ^ 2 ) ) ) - 1 ) $.
      $( Lemma for ~ jm2.27 .  Forward direction with substitutions.
         (Contributed by Stefan O'Rear, 4-Oct-2014.) $)
      jm2.27c $p |- ( ph ->
      ( ( ( D e. NN0
            /\ E e. NN0
            /\ F e. NN0 )
         /\ ( G e. NN0
            /\ H e. NN0
            /\ I e. NN0 ) )
      /\ ( J e. NN0
         /\ ( ( ( ( ( D ^ 2 ) - ( ( ( A ^ 2 ) - 1 ) x. ( C ^ 2 ) ) ) = 1
                  /\ ( ( F ^ 2 ) - ( ( ( A ^ 2 ) - 1 ) x. ( E ^ 2 ) ) ) = 1
                  /\ G e. ( ZZ>= ` 2 ) )
               /\ ( ( ( I ^ 2 ) - ( ( ( G ^ 2 ) - 1 ) x. ( H ^ 2 ) ) ) = 1
                  /\ E = ( ( J + 1 ) x. ( 2 x. ( C ^ 2 ) ) )
                  /\ F || ( G - A ) ) )
            /\ ( ( ( 2 x. C ) || ( G - 1 )
                  /\ F || ( H - C ) )
               /\ ( ( 2 x. C ) || ( H - B )
                  /\ B <_ C ) ) ) ) ) ) $=
        ( cn0 wcel w3a c2 cexp co c1 cmin cmul wceq cuz cfv caddc cdvds wbr cle
        wa crmx cz nnzd frmx fovcl syl2anc eqeltrid crmy cc0 2z eqeltrrd zmulcl
        zmulcld sylancr frmy rmy0 syl cn 2nn nnmulcld nnmulcl nnnn0d nn0ge0d wb
        lermy syl3anc mpbid eqbrtrrd elnn0z sylanbrc 3jca 2nn0 nn0cnd nn0mulcld
        0zd sqvald eqeltrd eluz2nn nn0red remulcld rmx1 1nn0 breqtrrdi breqtrrd
        nnge1d a1i zsqcl wi mpd nn0zd dvdsmul1 zcnd eqtrd dvdstrd oveq1d oveq2d
        3brtr4d clt oveq1i oveq12d rmxynorm oveq2i oveq12i eqtrid nncnd sylancl
        cc ax-1cn eqtr2d mulassd eluzelz 1z eqtr4d peano2zm sqcld syl322anc jca
        zsubcld jca31 rmxnn lemulge12d letrd nn0sub uzaddcl eluznn0 cdiv iddvds
        lermxnn0 jm2.20nn mpbird dvdscmul rmydbl 2cnd mul32d nngt0d ltrmy elnnz
        eqcomd nnsqcld nnm1nn0 nnne0d divcld npcan pncan2d 3eqtrd zsubcl congid
        nndivdvds divcan1d eqbrtrd muldvds1 dvdsmultr2 subsub23 congsub congmul
        subcl mulcld congadd mullidd pncan3 jm2.15nn0 jm2.16nn0 rmygeid ) AEUEU
        FZGUEUFZHUEUFZUGIUEUFZJUEUFZKUEUFZUGLUEUFZEUHUIUJZBUHUIUJZUKULUJZDUHUIU
        JZUMUJZULUJZUKUNZHUHUIUJZUWNGUHUIUJZUMUJZULUJZUKUNZIUHUOUPZUFZUGZKUHUIU
        JZIUHUIUJUKULUJZJUHUIUJZUMUJZULUJZUKUNZGLUKUQUJZUHUWOUMUJZUMUJZUNZHIBUL
        UJZURUSZUGZVAUHDUMUJZIUKULUJZURUSZHJDULUJZURUSZVAUXTJCULUJZURUSZCDUTUSZ
        VAZVAZVAZVAAUWEUWFUWGAEBCVBUJZUEQABUXDUFZCVCUFZUYKUEUFMACNVDZBCUEUXDVCV
        BVEVFVGVHAGBUHFUMUJZVIUJZUESAUYPVCUFZVJUYPUTUSUYPUEUFAUYLUYOVCUFZUYQMAU
        HVCUFZFVCUFZUYRVKAFCBCVIUJZUMUJZVCRACVUAUYNADVUAVCPADOVDZVLZVNZVHZUHFVM
        VOZBUYOVCUXDVCVIVPVFVGZABVJVIUJZVJUYPUTAUYLVUIVJUNMBVQVRZAVJUYOUTUSZVUI
        UYPUTUSZAUYOAUYOAUHVSUFZFVSUFZUYOVSUFVTAFVUBVSRACVUANADVUAVSPOVLWAVHZUH
        FWBVOZWCZWDAUYLVJVCUFZUYRVUKVULWEMAWPZVUGBVJUYOWFWGWHWIUYPWJWKVHAHBUYOV
        BUJZUETAUYLUYRVUTUEUFMVUGBUYOUEUXDVCVBVEVFVGVHZWLAUWHUWIUWJAUHUEUFUXEUW
        HWMAIBUWSUWSBULUJZUMUJZUQUJZUXDUAAUYLVVCUEUFVVDUXDUFMAUWSVVBAUWSHHUMUJZ
        UEAHAHVVAWNZWQZAHHVVAVVAWOWRZABUWSUTUSZVVBUEUFZABVVEUWSUTABHVVEABABAUYL
        BVSUFMBWSVRWCZWTAHVVAWTZAHHVVLVVLXAABVUTHUTABUKVBUJZBVUTUTAUYLVVMBUNMBX
        BVRAUKUYOUTUSZVVMVUTUTUSZAUYOVUPXFAUYLUKUEUFZUYOUEUFVVNVVOWEMVVPAXCXGVU
        QBUKUYOUUIWGWHWITXDAHHVVLVVLAHVVAWDAHAHVUTVSTAUYLUYRVUTVSUFMVUGBUYOUUAV
        GVHXFUUBUUCVVGXEABUEUFUWSUEUFVVIVVJWEVVKVVHBUWSUUDVGWHZWOZVVCUHBUUEVGVH
        ZIUHUUFVOAJICVIUJZUEUBAVVTVCUFZVJVVTUTUSVVTUEUFAUXEUYMVWAVVSUYNICVCUXDV
        CVIVPVFVGZAIVJVIUJZVJVVTUTAUXEVWCVJUNVVSIVQVRAVJCUTUSZVWCVVTUTUSZACACNW
        CZWDAUXEVURUYMVWDVWEWEVVSVUSUYNIVJCWFWGWHWIVVTWJWKVHAKICVBUJZUEUCAUXEUY
        MVWGUEUFVVSUYNICUEUXDVCVBVEVFVGVHWLAUWKUYJALGUXNUUGUJZUKULUJZUEUDAVWHVS
        UFZVWIUEUFAUXNGURUSZVWJAUHVUAUHUIUJZUMUJZUYPUXNGURAVWMUHBFVIUJZUMUJZUYP
        AUYSVWLVCUFZVWMVCUFVKAVUAVCUFVWPVUDVUAXHVRZUHVWLVMVOAUYSVWNVCUFZVWOVCUF
        ZVKAUYLUYTVWRMVUFBFVCUXDVCVIVPVFVGZUHVWNVMVOZVUHAVWLVWNURUSZVWMVWOURUSZ
        AVXBVUBFURUSZAVUBVUBFURAVUBVCUFVUBVUBURUSVUEVUBUUHVRRXDAUYLVUNCVSUFVXBV
        XDWEMVUONBFCUUJWGUUKAVWPVWRUYSVXBVXCXIVWQVWTUYSAVKXGUHVWLVWNUULWGXJAVWO
        VWOBFVBUJZUMUJZUYPURAVWSVXEVCUFVWOVXFURUSVXAAVXEAUYLUYTVXEUEUFMVUFBFUEU
        XDVCVBVEVFVGZXKVWOVXEXLVGAUYPUHVXEUMUJVWNUMUJZVXFAUYLUYTUYPVXHUNMVUFBFU
        UMVGAUHVXEVWNAUUNZAVXEVXGWNAVWNVWTXMUUOXNXEXOAUWOVWLUHUMADVUAUHUIPXPZXQ
        GUYPUNASXGZXRZAGVSUFZUXNVSUFZVWKVWJWEAGVCUFZVJGXSUSVXMAGUYPVCSVUHVHZAVU
        IUYPVJGXSAVJUYOXSUSZVUIUYPXSUSZAUYOVUPUUPAUYLVURUYRVXQVXRWEMVUSVUGBVJUY
        OUUQWGWHAVUIVJVUJUUSVXKXRGUURWKAVUMUWOVSUFVXNVTADOUUTUHUWOWBVOZGUXNUVIV
        GWHVWHUVAVRVHAUXFUXSUYIAUWRUXCUXEAUWQUYKUHUIUJZUWNVWLUMUJZULUJZUKAUWLVX
        TUWPVYAULUWLVXTUNAEUYKUHUIQXTXGAUWOVWLUWNUMVXJXQYAAUYLUYMVYBUKUNMUYNBCY
        BVGXNAUXBVUTUHUIUJZUWNUYPUHUIUJZUMUJZULUJZUKUWSVYCUXAVYEULHVUTUHUITXTUW
        TVYDUWNUMGUYPUHUISXTYCYDAUYLUYRVYFUKUNMVUGBUYOYBVGYEZVVSWLAUXLUXPUXRAUX
        KVWGUHUIUJZUXHVVTUHUIUJZUMUJZULUJZUKUXGVYHUXJVYJULKVWGUHUIUCXTUXIVYIUXH
        UMJVVTUHUIUBXTYCYDAUXEUYMVYKUKUNVVSUYNICYBVGYEAUXOVWHUXNUMUJGAUXMVWHUXN
        UMAUXMVWIUKUQUJZVWHALVWIUKUQLVWIUNAUDXGXPAVWHYHUFUKYHUFZVYLVWHUNAGUXNAG
        VXPXMZAUXNVXSYFZAUXNVXSUVBZUVCYIVWHUKUVDYGXNXPAGUXNVYNVYOVYPUVJYJAHHHVV
        BUMUJZUMUJZUXQURAHVCUFVYQVCUFHVYRURUSAHVVAXKZAHVVBVYSAVVBVVQXKZVNHVYQXL
        VGAUXQVVDBULUJZVYRIVVDBULUAXTAWUAVVCVVEVVBUMUJVYRABVVCABVVKWNZAVVCVVRWN
        UVEAUWSVVEVVBUMVVGXPAHHVVBVVFVVFAVVBVVQWNYKUVFYEXEZWLAUYBUYDUYHAUXTVVDB
        UKUKBULUJZUMUJZUQUJZULUJZUYAURAUXTVCUFZBVCUFZWUIVVCVCUFWUEVCUFZUXTBBULU
        JURUSZUXTVVCWUEULUJURUSZUXTWUGURUSAUYSDVCUFZWUHVKVUCUHDVMVOZAUYLWUIMUHB
        YLVRZWUOAVVCVVRXKAUKVCUFZWUDVCUFZWUJYMAWUPWUIWUQYMWUOUKBUVGVOZUKWUDVMVO
        AWUHWUIWUKWUNWUOUXTBUVHVGZAWUHUWSVCUFZWUPVVBVCUFWUQUXTUWSUKULUJZURUSZUX
        TVVBWUDULUJURUSZWULWUNAUWSVVHXKZWUPAYMXGZVYTWURAUXTUXAWVAURAUXTUWNGUMUJ
        ZGUMUJZUXAURAUXTGURUSZUXTWVGURUSZAUXTDUMUJZGURUSZWVHAWVJUXNGURAWVJUHDDU
        MUJZUMUJUXNAUHDDVXIADOYFZWVMYKAUWOWVLUHUMADWVMWQXQYNVXLUVKAWUHWUMVXOWVK
        WVHXIWUNVUCVXPUXTDGUVLWGXJAWUHWVFVCUFVXOWVHWVIXIWUNAUWNGAUWMVCUFZUWNVCU
        FAWUIWVNWUOBXHVRUWMYOVRVXPVNVXPUXTWVFGUVMWGXJAUXAUWNGGUMUJZUMUJWVGAUWTW
        VOUWNUMAGVYNWQXQAUWNGGAUWMYHUFVYMUWNYHUFABWUBYPYIUWMUKUVQYGZVYNVYNYKYNX
        EAUXCWVAUXAUNZVYGAUWSYHUFUXAYHUFVYMUXCWVQWEAHVVFYPAUWNUWTWVPAGVYNYPUVRV
        YMAYIXGUWSUXAUKUVNWGWHXEZAWUHWUTWUPWUIWUIWVBWUKWVCWUNWVDWVEWUOWUOWVRWUS
        UXTUWSUKBBUVOYQUXTUWSUKVVBWUDUVPYQUXTBBVVCWUEUVSYQAIVVDUKWUFULIVVDUNAUA
        XGAWUFBWUDUQUJZUKAWUEWUDBUQAWUDAWUDWURXMUVTXQABYHUFVYMWVSUKUNWUBYIBUKUW
        AYGYJYAXEZAHUXQUYCVYSAIBAUXEIVCUFZVVSUHIYLVRZWUOYSAJDAJVVTVCUBVWBVHZVUC
        YSWUCAUXQVVTVUAULUJZUYCURAUXEUYLCUEUFZUXQWWDURUSVVSMVWFIBCUWBWGAJVVTDVU
        AULJVVTUNAUBXGPYAXEXOAUYFUYGAUXTUYAUYEWUNAWWAUYAVCUFWWBIYOVRAJCWWCUYNYS
        WVTAUYAVVTCULUJZUYEURAUXEWWEUYAWWFURUSVVSVWFICUWCVGJVVTCULUBXTXDXOACVUA
        DUTAUYLWWECVUAUTUSMVWFBCUWDVGPXEYRYTYTYRYT $.
    $}
  $}

  ${
    $d A d e f g h i j $.  $d B d e f g h i j $.  $d C d e f g h i j $.

    $( Lemma 2.27 of [JonesMatijasevic] p. 697; rmY is a diophantine relation.
       0 was excluded from the range of B and the lower limit of G was imposed
       because the source proof does not seem to work otherwise; quite possible
       I'm just missing something.  The source proof uses both i and I; i has
       been changed to j to avoid collision.  This theorem is basically nothing
       but substitution instances, all the work is done in ~ jm2.27a and
       ~ jm2.27c .  Once Diophantine relations have been defined, the content
       of the theorem is "rmY is Diophantine".  (Contributed by Stefan O'Rear,
       4-Oct-2014.) $)
    jm2.27 $p |- ( ( A e. ( ZZ>= ` 2 ) /\ B e. NN /\ C e. NN ) -> ( C = ( A rmY
        B ) <->
        E. d e. NN0 E. e e. NN0 E. f e. NN0 E. g e. NN0 E. h e. NN0 E. i e. NN0
        E. j e. NN0
          ( ( ( ( ( d ^ 2 ) - ( ( ( A ^ 2 ) - 1 ) x. ( C ^ 2 ) ) ) = 1
                /\ ( ( f ^ 2 ) - ( ( ( A ^ 2 ) - 1 ) x. ( e ^ 2 ) ) ) = 1
                /\ g e. ( ZZ>= ` 2 ) )
             /\ ( ( ( i ^ 2 ) - ( ( ( g ^ 2 ) - 1 ) x. ( h ^ 2 ) ) ) = 1
                /\ e = ( ( j + 1 ) x. ( 2 x. ( C ^ 2 ) ) )
                /\ f || ( g - A ) ) )
          /\ ( ( ( 2 x. C ) || ( g - 1 )
                /\ f || ( h - C ) )
             /\ ( ( 2 x. C ) || ( h - B )
                /\ B <_ C ) ) ) ) ) $=
      ( c2 wcel co wceq cexp c1 cmin wa cn0 wrex cuz cfv cn w3a crmy cmul caddc
      cv cdvds wbr cle crmx cdiv simpl1 simpl2 simpl3 simpr eqid jm2.27c simpld
      simprd oveq1 oveq1d eqeq2d 3anbi2d anbi2d anbi1d rspcev syl eleq1 3anbi3d
      oveq2d eqeq1d breq2d 3anbi13d anbi12d rexbidv 3anbi1d rspc3ev eqeq1 breq1
      syl2anc 2rexbidv simpll1 ad3antrrr simpll2 simpll3 simplrl simplrr simprl
      ex simprr ad2antrr simplr simp2l1 simp2l2 simp2l3 simp2r1 simp2r2 simp2r3
      simp3ll simp3lr simp3rl simp3rr jm2.27b rexlimdva2 rexlimdvva impbid
      3expb ) AKUAUBZLZBUCLZCUCLZUDZCABUEMZNZJUHZKOMZAKOMPQMZCKOMZUFMZQMZPNZEUH
      ZKOMZXSDUHZKOMZUFMZQMZPNZFUHZXJLZUDZHUHZKOMZYKKOMZPQMZGUHZKOMZUFMZQMZPNZY
      FIUHZPUGMZKXTUFMZUFMZNZYDYKAQMZUIUJZUDZRZKCUFMZYKPQMZUIUJZYDYRCQMZUIUJZRZ
      UULYRBQMZUIUJZBCUKUJZRZRZRZISTZHSTZGSTZFSTZESTZDSTJSTZXNXPUVIXNXPRZABULMZ
      SLAKBXOUFMZUFMZUEMZSLAUVMULMZSLUDZUVKKOMZYAQMZPNZUVOKOMZXSUVNKOMZUFMZQMZP
      NZYLUDZUUBUVNUUFNZUVOUUHUIUJZUDZRZUUNUVOUUOUIUJZRZUVARZRZISTZHSTZGSTFSTZU
      VIUVJUVPAUVTUVTAQMUFMUGMZSLUWQBUEMZSLUWQBULMZSLUDZUVJUVPUWTRZUVNUUEUMMPQM
      ZSLUVSUWDUWQXJLZUDZUWSKOMZUWQKOMZPQMZUWRKOMZUFMZQMZPNZUVNUXBPUGMZUUEUFMZN
      ZUVOUWQAQMZUIUJZUDZRZUULUWQPQMZUIUJZUVOUWRCQMZUIUJZRZUULUWRBQMZUIUJZUUTRZ
      RZRZRZUVJABCUVKUVLUVNUVOUWQUWRUWSUXBXKXLXMXPUNXKXLXMXPUOXKXLXMXPUPXNXPUQU
      VKURUVLURUVNURUVOURUWQURUWRURUWSURUXBURUSZUTZUTUVJUWTUXDUXKUWFUXPUDZRZUYG
      RZISTZUWPUVJUVPUWTUYKVAUVJUYIUYOUVJUXAUYIUYJVAUYNUYHIUXBSUUCUXBNZUYMUXRUY
      GUYPUYLUXQUXDUYPUWFUXNUXKUXPUYPUUFUXMUVNUYPUUDUXLUUEUFUUCUXBPUGVBVCVDVEVF
      VGVHVIUWNUYOUXDYOUXGYSUFMZQMZPNZUWFUXPUDZRZUXTUWJRZUVARZRZISTUXDYOUXIQMZP
      NZUWFUXPUDZRZUYGRZISTFGHUWQUWRUWSSSSYKUWQNZUWMVUDISVUJUWIVUAUWLVUCVUJUWEU
      XDUWHUYTVUJYLUXCUVSUWDYKUWQXJVJVKVUJUUBUYSUWGUXPUWFVUJUUAUYRPVUJYTUYQYOQV
      UJYQUXGYSUFVUJYPUXFPQYKUWQKOVBVCVCVLVMVUJUUHUXOUVOUIYKUWQAQVBVNVOVPVUJUWK
      VUBUVAVUJUUNUXTUWJVUJUUMUXSUULUIYKUWQPQVBVNVGVGVPVQYRUWRNZVUDVUIISVUKVUAV
      UHVUCUYGVUKUYTVUGUXDVUKUYSVUFUWFUXPVUKUYRVUEPVUKUYQUXIYOQVUKYSUXHUXGUFYRU
      WRKOVBVLVLVMVRVFVUKVUBUYCUVAUYFVUKUWJUYBUXTVUKUUOUYAUVOUIYRUWRCQVBVNVFVUK
      UUSUYEUUTVUKUURUYDUULUIYRUWRBQVBVNVGVPVPVQYNUWSNZVUIUYNISVULVUHUYMUYGVULV
      UGUYLUXDVULVUFUXKUWFUXPVULVUEUXJPVULYOUXEUXIQYNUWSKOVBVCVMVRVFVGVQVSWBUVG
      UWPUVSYJYLUDZUUJRZUVBRZISTHSTZGSTFSTUVSYEUWBQMZPNZYLUDZUUBUWFUUIUDZRZUVBR
      ZISTHSTZGSTFSTJDEUVKUVNUVOSSSXQUVKNZUVEVUPFGSSVVDUVCVUOHISSVVDUUKVUNUVBVV
      DYMVUMUUJVVDYCUVSYJYLVVDYBUVRPVVDXRUVQYAQXQUVKKOVBVCVMVRVGVGWCWCYFUVNNZVU
      PVVCFGSSVVEVUOVVBHISSVVEVUNVVAUVBVVEVUMVUSUUJVUTVVEYJVURUVSYLVVEYIVUQPVVE
      YHUWBYEQVVEYGUWAXSUFYFUVNKOVBVLVLVMVEVVEUUGUWFUUBUUIYFUVNUUFVTVEVPVGWCWCY
      DUVONZVVCUWOFGSSVVFVVBUWMHISSVVFVVAUWIUVBUWLVVFVUSUWEVUTUWHVVFVURUWDUVSYL
      VVFVUQUWCPVVFYEUVTUWBQYDUVOKOVBVCVMVEVVFUUIUWGUUBUWFYDUVOUUHUIWAVKVPVVFUU
      QUWKUVAVVFUUPUWJUUNYDUVOUUOUIWAVFVGVPWCWCVSWBWKXNUVHXPJDSSXNXQSLZYFSLZRZR
      ZUVFXPEFSSVVJYDSLZYKSLZRZRZUVDXPGHSSVVNYRSLZYNSLZRZRZUVCXPISVVRUUCSLZRZUV
      CRABCXQYFYDYKYRYNUUCVVNXKVVQVVSUVCXKXLXMVVIVVMWDWEVVNXLVVQVVSUVCXKXLXMVVI
      VVMWFWEVVNXMVVQVVSUVCXKXLXMVVIVVMWGWEVVNVVGVVQVVSUVCXNVVGVVHVVMWHWEVVNVVH
      VVQVVSUVCXNVVGVVHVVMWIWEVVNVVKVVQVVSUVCVVJVVKVVLWJWEVVNVVLVVQVVSUVCVVJVVK
      VVLWLWEVVRVVOVVSUVCVVNVVOVVPWJWMVVRVVPVVSUVCVVNVVOVVPWLWMVVRVVSUVCWNVVTUU
      KUVBYCYCYJYLUUJVVTUVBWOXIVVTUUKUVBYJYCYJYLUUJVVTUVBWPXIVVTUUKUVBYLYCYJYLU
      UJVVTUVBWQXIVVTUUKUVBUUBUUBUUGUUIYMVVTUVBWRXIVVTUUKUVBUUGUUBUUGUUIYMVVTUV
      BWSXIVVTUUKUVBUUIUUBUUGUUIYMVVTUVBWTXIVVTUUKUVBUUNUUNUUPUVAVVTUUKXAXIVVTU
      UKUVBUUPUUNUUPUVAVVTUUKXBXIVVTUUKUVBUUSUUSUUTUUQVVTUUKXCXIVVTUUKUVBUUTUUS
      UUTUUQVVTUUKXDXIXEXFXGXGXGXH $.
  $}

  ${
    $d A a b $.  $d B a b $.
    jm2.27dlem1.1 $e |- A e. ( 1 ... B ) $.
    $( Lemma for ~ rmydioph .  Substitution of a tuple restriction into a
       projection that doesn't care.  (Contributed by Stefan O'Rear,
       11-Oct-2014.) $)
    jm2.27dlem1 $p |- ( a = ( b |` ( 1 ... B ) ) -> ( a ` A ) = ( b ` A ) ) $=
      ( cv c1 cfz co cres wceq cfv fveq1 wcel fvres ax-mp eqtrdi ) CFZDFZGBHIZJ
      ZKARLAUALZASLZARUAMATNUBUCKEATSOPQ $.
  $}

  ${
    jm2.27dlem2.1 $e |- A e. ( 1 ... B ) $.
    jm2.27dlem2.2 $e |- C = ( B + 1 ) $.
    jm2.27dlem2.3 $e |- B e. NN $.
    $( Lemma for ~ rmydioph .  This theorem is used along with the next three
       to efficiently infer steps like ` 7 e. ( 1 ... ; 1 0 ) ` .  (Contributed
       by Stefan O'Rear, 11-Oct-2014.) $)
    jm2.27dlem2 $p |- A e. ( 1 ... C ) $=
      ( c1 cfz co wcel cz cle wbr elfzelz ax-mp elfzle1 caddc cr zrei nnrei w3a
      elfzle2 letrp1 mp3an breqtrri wb 1z cn nnz peano2z eqeltri elfz1 mpbir3an
      mp2b mp2an ) AGCHIJZAKJZGALMZACLMZAGBHIJZUQDAGBNOZUTURDAGBPOABGQIZCLARJBR
      JABLMZAVBLMAVASBFTUTVCDAGBUBOABUCUDEUEGKJCKJUPUQURUSUAUFUGCVBKEBUHJBKJVBK
      JFBUIBUJUNUKAGCULUOUM $.
  $}

  ${
    jm2.27dlem3.1 $e |- A e. NN $.
    $( Lemma for ~ rmydioph .  Infer membership of the endpoint of a range.
       (Contributed by Stefan O'Rear, 11-Oct-2014.) $)
    jm2.27dlem3 $p |- A e. ( 1 ... A ) $=
      ( cn wcel c1 cfz co elfz1end mpbi ) ACDAEAFGDBAHI $.

    jm2.27dlem4.2 $e |- B = ( A + 1 ) $.
    $( Lemma for ~ rmydioph .  Infer ` NN ` -hood of large numbers.
       (Contributed by Stefan O'Rear, 11-Oct-2014.) $)
    jm2.27dlem4 $p |- B e. NN $=
      ( c1 caddc co cn wcel peano2nn ax-mp eqeltri ) BAEFGZHDAHIMHICAJKL $.
  $}

  ${
    jm2.27dlem5.2 $e |- B = ( A + 1 ) $.
    jm2.27dlem5.3 $e |- ( 1 ... B ) C_ ( 1 ... C ) $.
    $( Lemma for ~ rmydioph .  Used with ~ sselii to infer membership of
       midpoints of range; ~ jm2.27dlem2 is deprecated.  (Contributed by Stefan
       O'Rear, 11-Oct-2014.) $)
    jm2.27dlem5 $p |- ( 1 ... A ) C_ ( 1 ... C ) $=
      ( c1 cfz co caddc fzssp1 oveq2i sseqtrri sstri ) FAGHZFBGHZFCGHNFAFIHZGHO
      FAJBPFGDKLEM $.
  $}

  ${
    $d a b c d e f g h i $.

    $( ~ jm2.27 restated in terms of Diophantine sets.  (Contributed by Stefan
       O'Rear, 11-Oct-2014.)  (Revised by Stefan O'Rear, 6-May-2015.) $)
    rmydioph $p |- { a e. ( NN0 ^m ( 1 ... 3 ) ) | ( ( a ` 1 ) e. ( ZZ>= ` 2 )
        /\ ( a ` 3 ) = ( ( a ` 1 ) rmY ( a ` 2 ) ) ) } e. ( Dioph ` 3 ) $=
      ( vi c1 cfv c2 wcel c3 co wceq wa cn0 crab cexp cmin cmul cdvds wbr mp2an
      wb cmpt vb vd vc ve vg vf vh cv cuz crmy cfz cmap cn w3a caddc cle cc0 wo
      wrex cdioph wf elmapi jm2.27dlem3 df-3 jm2.27dlem2 ffvelcdm sylancl elnn0
      2nn anbi2d cz clt simplr adantl ad2antlr eleq1 pm5.32da bitrd ex pm5.32rd
      syl3anc eqeq2d cmzp 3nn0 2z cvv ovex df-2 eluzrabdioph mp3an elnnrabdioph
      mzpproj wsbc c9 c8 c7 c6 c5 c4 fvex oveq1 oveq2d oveqan12rd eqeq1d oveq1d
      1nn 3ad2ant3 3anbi12d breq2d anbi1d anbi12d sbc3ie sbcbii oveq12d breq12d
      3ad2ant1 3anbi23d jm2.27dlem1 adantr df-5 df-6 df-7 df-8 df-9 jm2.27dlem5
      sselii 2nn0 mzpexpmpt df-4 mzpconstmpt mzpsubmpt mzpmulmpt eqrabdioph 9nn
      10nn0 3anrabdioph dvdsrabdioph anrabdioph eqeltri eq0rabdioph andi bitrdi
      sylib iba syl nnz frmy fovcl syl2anc nngt0 0zd ltrmy mpbid eqbrtrrd elnnz
      rmy0 sylanbrc syl5ibrcom simpllr simpr jm2.27 oveq2 eqtrd orbi12d rabbiia
      pm4.71rd 3nn cdc 3adant3 3ad2ant2 eqeq1 simp2 3anbi123d bi2anan9r 3adant1
      cres breq1 vex resex breq1d sbc2ie 3bitri rabbii 9p1e10 eqcomi 4nn 1z 6nn
      ssid 5nn 7nn 8nn 10nn mzpaddmpt lerabdioph 7rexfrabdioph orrabdioph ) CAU
      HZDZEUIDZFZGUWRDZUWSEUWRDZUJHZIZJZAKCGUKHZULHZLUXAUXBUMFZUAUHZEMHZUWSEMHZ
      CNHZUXBEMHZOHZNHZCIZUBUHZEMHZUXMUCUHZEMHZOHZNHZCIZUDUHZUWTFZUNZUEUHZEMHZU
      YEEMHZCNHZUFUHZEMHZOHZNHZCIZUXTUGUHZCUOHZEUXNOHZOHZIZUXRUYEUWSNHZPQZUNZJZ
      EUXBOHZUYECNHZPQZUXRUYLUXBNHZPQZJZVUFUYLUXCNHZPQZUXCUXBUPQZJZJZJZUGKUSUEK
      USUFKUSUDKUSUBKUSUCKUSUAKUSZJZUXCUMFZJZUXBUQIZUXCUQIZJZURZJZAUXHLZGUTDZUX
      FVVFAUXHUWRUXHFZUXFUXAUXEVUTJZUXEVVCJZURZJZVVFVVIVUTVVCURZUXFVVMSVVIUXCKF
      ZVVNVVIUXGKUWRVAEUXGFZVVOUWRKUXGVBEEGEVIVCZVDVIVEZUXGKEUWRVFVGUXCVHUUCVVN
      UXEVVLUXAVVNUXEUXEVVNJVVLVVNUXEUUDUXEVUTVVCUUAUUBVJUUEVVIUXAVVLVVEVVIUXAJ
      ZVVJVVAVVKVVDVVSVUTUXEVUSVVSVUTUXEVUSSVVSVUTJZUXEUXIUXEJVUSVVTUXEUXIVVTUX
      IUXEUXDUMFZVVTUXDVKFZUQUXDVLQVWAVVTUXAUXCVKFZVWBVVIUXAVUTVMZVUTVWCVVSUXCU
      UFVNZUWSUXCVKUWTVKUJUUGUUHUUIVVTUWSUQUJHZUQUXDVLUXAVWFUQIZVVIVUTUWSUUPZVO
      VVTUQUXCVLQZVWFUXDVLQZVUTVWIVVSUXCUUJVNVVTUXAUQVKFVWCVWIVWJSVWDVVTUUKVWEU
      WSUQUXCUULWAUUMUUNUXDUUOUUQUXBUXDUMVPUURUVFVVTUXIUXEVURVVTUXIJUXAVUTUXIUX
      EVURSVVIUXAVUTUXIUUSVVSVUTUXIVMVVTUXIUUTUWSUXCUXBUCUBUDUFUEUGUAUVAWAVQVRV
      SVTVVSVVCUXEVVBVVSVVCUXEVVBSVVSVVCJZUXDUQUXBVWKUXDVWFUQVVCUXDVWFIVVSUXCUQ
      UWSUJUVBVNUXAVWGVVIVVCVWHVOUVCWBVSVTUVDVQVRUVEUXAAUXHLVVHFZVVEAUXHLVVHFZV
      VGVVHFGKFZEVKFZAVKUXGULHZUWSTUXGWCDZFZVWLWDWEUXGWFFZCUXGFVWRCGUKWGZCEGCCE
      CXFVCZWHXFVEVDVIVEZAUXGCWLRAUWSEGWIWJVVAAUXHLVVHFZVVDAUXHLVVHFZVWMVUSAUXH
      LVVHFZVUTAUXHLVVHFZVXCUXIAUXHLVVHFZVURAUXHLVVHFZVXEVWNAVWPUXBTVWQFZVXGWDV
      WSGUXGFVXIVWTGUVGVCZAUXGGWLRZAUXBGWKRVWNVUQUGCUQUVHZBUHZDZWMUEWNVXMDZWMUF
      WOVXMDZWMZUDWPVXMDZWMZUBWQVXMDZWMZUCWRVXMDZWMZUAWSVXMDZWMZAVXMUXGUVPZWMZB
      KCVXLUKHZULHZLZVXLUTDZFVXHWDVYJVYDEMHZCVXMDZEMHZCNHZGVXMDZEMHZOHZNHZCIZVX
      TEMHZVYOVYBEMHZOHZNHZCIZVXRUWTFZUNZVXOEMHZVXREMHZCNHZVXPEMHZOHZNHZCIZVYBV
      XNCUOHZEVYQOHZOHZIZVXTVXRVYMNHZPQZUNZJZEVYPOHZVXRCNHZPQZVXTVXPVYPNHZPQZJZ
      WVCVXPEVXMDZNHZPQZWVIVYPUPQZJZJZJZBVYILZVYKVYGWVOBVYIVYGUYGWUHUYKWUKOHZNH
      ZCIZUXTWUOUYSOHZIZVUCUNZJZVUHUXRVXPUXBNHZPQZJZVUFVXPUXCNHZPQZVUNJZJZJZUDV
      XRWMZUBVXTWMZUCVYBWMZUAVYDWMZAVYFWMUXQWUAUXMWUBOHZNHZCIZWUFUNZWUNVYBWVTIZ
      VXTVXRUWSNHZPQZUNZJZVUFWVDPQZVXTWWDPQZJZWWIJZJZUAVYDWMZAVYFWMWVOVYEWWOAVY
      FVYCWWNUAVYDVYAWWMUCVYBVXSWWLUBVXTVXQWWKUDVXRVUQWWKUFUEUGVXPVXOVXNWOVXMWT
      WNVXMWTVXLVXMWTUYLVXPIZUYHVXOIZUYQVXNIZUNZVUEWWCVUPWWJWXNVUDWWBUYGWXNUYPW
      VSVUAWWAVUCWXKWXLUYPWVSSWXMWXKWXLJUYOWVRCWXLWXKUYIWUHUYNWVQNUYHVXOEMXAWXK
      UYMWUKUYKOUYLVXPEMXAXBXCXDUVIWXMWXKVUAWWASWXLWXMUYTWVTUXTWXMUYRWUOUYSOUYQ
      VXNCUOXAXEWBXGXHVJWXKWXLVUPWWJSWXMWXKVUKWWFVUOWWIWXKVUJWWEVUHWXKVUIWWDUXR
      PUYLVXPUXBNXAXIVJWXKVUMWWHVUNWXKVULWWGVUFPUYLVXPUXCNXAXIXJXKXPXKXLXMXMXMX
      MXMWWOWXJAVYFWWNWXIUAVYDWWKWXIUCUBUDVYBVXTVXRWRVXMWTWQVXMWTWPVXMWTUXTVYBI
      ZUXRVXTIZUYEVXRIZUNZWWCWXDWWJWXHWXRUYGWWSWWBWXCWXRUYDWWRUYFWUFUXQWXRUYCWW
      QCWXRUXSWUAUYBWWPNWXPWXOUXSWUAIWXQUXRVXTEMXAUVJWXOWXPUYBWWPIWXQWXOUYAWUBU
      XMOUXTVYBEMXAXBXPXNXDWXQWXOUYFWUFSWXPUYEVXRUWTVPXGXQWXRWVSWUNWWAWWTVUCWXB
      WXQWXOWVSWUNSWXPWXQWVRWUMCWXQWVQWULWUHNWXQUYKWUJWUKOWXQUYJWUICNUYEVXREMXA
      XEXEXBXDXGWXOWXPWWAWWTSWXQUXTVYBWVTUVKXPWXRUXRVXTVUBWXAPWXOWXPWXQUVLWXQWX
      OVUBWXAIWXPUYEVXRUWSNXAXGXOUVMXKWXPWXQWWJWXHSWXOWXPWXQJWWFWXGWWIWXQVUHWXE
      WXPWWEWXFWXQVUGWVDVUFPUYEVXRCNXAXIUXRVXTWWDPUVQUVNXJUVOXKXLXMXMWXIWVOAUAV
      YFVYDVXMUXGBUVRUVSWSVXMWTUWRVYFIZUXJVYDIZJZWXDWVBWXHWVNWYAWWSWUGWXCWVAWYA
      UXQVYTWWRWUEWUFWYAUXPVYSCWXTWXSUXKVYLUXOVYRNUXJVYDEMXAWXSUXMVYOUXNVYQOWXS
      UXLVYNCNWXSUWSVYMEMCGABVXBXRZXEXEZWXSUXBVYPEMGGABVXJXRZXEZXNXCXDWXSWWRWUE
      SWXTWXSWWQWUDCWXSWWPWUCWUANWXSUXMVYOWUBOWYCXEXBXDXSXHWXSWXCWVASWXTWXSWWTW
      URWXBWUTWUNWXSWVTWUQVYBWXSUYSWUPWUOOWXSUXNVYQEOWYEXBXBWBWXSWXAWUSVXTPWXSU
      WSVYMVXRNWYBXBXIXQXSXKWXSWXHWVNSWXTWXSWXGWVHWWIWVMWXSWXEWVEWXFWVGWXSVUFWV
      CWVDPWXSUXBVYPEOWYDXBZUVTWXSWWDWVFVXTPWXSUXBVYPVXPNWYDXBXIXKWXSWWHWVKVUNW
      VLWXSVUFWVCWWGWVJPWYFWXSUXCWVIVXPNEGABVVRXRZXBXOWXSUXCWVIUXBVYPUPWYGWYDXO
      XKXKXSXKUWAUWBUWCWVBBVYILVYKFZWVNBVYILVYKFZWVPVYKFWUGBVYILVYKFZWVABVYILVY
      KFZWYHVYTBVYILVYKFZWUEBVYILVYKFZWUFBVYILVYKFZWYJVXLKFZBVKVYHULHZVYSTVYHWC
      DZFZBWYPCTWYQFZWYLYOBWYPVYLTWYQFZBWYPVYRTWYQFZWYRBWYPVYDTWYQFZEKFZWYTVYHW
      FFZWSVYHFXUBCVXLUKWGZCWSUKHVYHWSWSWRVXLXTWRWQVXLYAWQWPVXLYBWPWOVXLYCWOWNV
      XLYDWNVXLVXLWNCUOHVXLUWDUWEZVYHUWIYEYEZYEZYEZYEZYEZWSUWFVCYFBVYHWSWLRYGBV
      YDEVYHYHRBWYPVYOTWYQFZBWYPVYQTWYQFZXUABWYPVYNTWYQFZWYSXULBWYPVYMTWYQFZXUC
      XUNXUDCVYHFXUOXUECCUKHVYHCCEVXLWHEGVXLVDGWSVXLYIXUKYEZYEZYEVXAYFBVYHCWLRZ
      YGBVYMEVYHYHRXUDCVKFWYSXUEUWGBCVYHYJRZBVYNCVYHYKRZBWYPVYPTWYQFZXUCXUMXUDG
      VYHFXVAXUEUXGVYHGXUPVXJYFBVYHGWLRZYGBVYPEVYHYHRZBVYOVYQVYHYLRBVYLVYRVYHYK
      RXUSBVYSCVXLYMWJWYOBWYPWUDTWYQFZWYSWYMYOBWYPWUATWYQFZBWYPWUCTWYQFZXVDBWYP
      VXTTWYQFZXUCXVEXUDWQVYHFXVGXUECWQUKHVYHWQXUIWQUWHVCYFBVYHWQWLRZYGBVXTEVYH
      YHRXULBWYPWUBTWYQFZXVFXUTBWYPVYBTWYQFZXUCXVIXUDWRVYHFXVJXUECWRUKHVYHWRXUJ
      WRUWJVCYFBVYHWRWLRZYGBVYBEVYHYHRBVYOWUBVYHYLRBWUAWUCVYHYKRXUSBWUDCVXLYMWJ
      WYOVWOBWYPVXRTWYQFZWYNYOWEXUDWPVYHFXVLXUECWPUKHVYHWPXUHWPUWKVCYFBVYHWPWLR
      ZBVXREVXLWIWJVYTWUEWUFBVXLYPWJWUNBVYILVYKFZWURBVYILVYKFZWUTBVYILVYKFZWYKW
      YOBWYPWUMTWYQFZWYSXVNYOBWYPWUHTWYQFZBWYPWULTWYQFZXVQBWYPVXOTWYQFZXUCXVRXU
      DWNVYHFXVTXUEWNWNVXLWNYNVCXUFYNVEBVYHWNWLRYGBVXOEVYHYHRBWYPWUJTWYQFZBWYPW
      UKTWYQFZXVSBWYPWUITWYQFZWYSXWAXVLXUCXWCXVMYGBVXREVYHYHRXUSBWUICVYHYKRBWYP
      VXPTWYQFZXUCXWBXUDWOVYHFXWDXUECWOUKHVYHWOXUGWOUWLVCYFBVYHWOWLRZYGBVXPEVYH
      YHRBWUJWUKVYHYLRBWUHWULVYHYKRXUSBWUMCVXLYMWJWYOXVJBWYPWUQTWYQFZXVOYOXVKBW
      YPWUOTWYQFZBWYPWUPTWYQFZXWFBWYPVXNTWYQFZWYSXWGXUDVXLVYHFXWIXUEVXLUWMVCBVY
      HVXLWLRXUSBVXNCVYHUWNRBWYPETWYQFZXUMXWHXUDVWOXWJXUEWEBEVYHYJRZXVCBEVYQVYH
      YLRBWUOWUPVYHYLRBVYBWUQVXLYMWJWYOXVGBWYPWUSTWYQFZXVPYOXVHXVLXUOXWLXVMXURB
      VXRVYMVYHYKRBVXTWUSVXLYQWJWUNWURWUTBVXLYPWJWUGWVABVXLYRRWVHBVYILVYKFZWVMB
      VYILVYKFZWYIWVEBVYILVYKFZWVGBVYILVYKFZXWMWYOBWYPWVCTWYQFZBWYPWVDTWYQFZXWO
      YOXWJXVAXWQXWKXVBBEVYPVYHYLRZXVLWYSXWRXVMXUSBVXRCVYHYKRBWVCWVDVXLYQWJWYOX
      VGBWYPWVFTWYQFZXWPYOXVHXWDXVAXWTXWEXVBBVXPVYPVYHYKRBVXTWVFVXLYQWJWVEWVGBV
      XLYRRWVKBVYILVYKFZWVLBVYILVYKFZXWNWYOXWQBWYPWVJTWYQFZXXAYOXWSXWDBWYPWVITW
      YQFZXXCXWEXUDEVYHFXXDXUECEUKHVYHEXUQVVQYFBVYHEWLRZBVXPWVIVYHYKRBWVCWVJVXL
      YQWJWYOXXDXVAXXBYOXXEXVBBWVIVYPVXLUWOWJWVKWVLBVXLYRRWVHWVMBVXLYRRWVBWVNBV
      XLYRRYSVUQUBUDUFUCUAABVXLWNWOWPWQWRWSGUGUEYIXTYAYBYCYDXUFUWPRUXIVURAGYRRV
      WNAVWPUXCTVWQFZVXFWDVWSVVPXXFVWTVVRAUXGEWLRZAUXCGWKRVUSVUTAGYRRVVBAUXHLVV
      HFZVVCAUXHLVVHFZVXDVWNVXIXXHWDVXKAUXBGYTRVWNXXFXXIWDXXGAUXCGYTRVVBVVCAGYR
      RVVAVVDAGUWQRUXAVVEAGYRRYS $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  X and Y sequences 5: Diophantine representability of X, ^, _C
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d A y $.  $d N y $.  $d X y $.
    $( X can be expressed in terms of Y, so it is also Diophantine.
       (Contributed by Stefan O'Rear, 15-Oct-2014.) $)
    rmxdiophlem $p |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. NN0 /\ X e. NN0 ) -> ( X =
      ( A rmX N ) <-> E. y e. NN0 ( y = ( A rmY N ) /\ ( ( X ^ 2 ) - ( (
        ( A ^ 2 ) - 1 ) x. ( y ^ 2 ) ) ) = 1 ) ) ) $=
      ( c2 wcel cn0 crmx co wceq cexp cmin cmul nn0sqcl 3ad2ant3 nn0cnd syl2anc
      c1 wa syl cuz cfv w3a crmy cv wrex cz simp1 nn0z 3ad2ant2 fovcl csquarenn
      cn rmspecnonsq eldifad nnnn0d 3ad2ant1 rmynn0 3adant3 nn0mulcld subcan2ad
      frmx rmxynorm eqeq2d cr cc0 cle wbr nn0re nn0ge0 jca sq11 3bitr3rd oveq2d
      wb oveq1 eqeq1d ceqsrexv bitr4d ) BEUAUBZFZCGFZDGFZUCZDBCHIZJZDEKIZBEKIRL
      IZBCUDIZEKIZMIZLIZRJZAUEZWIJZWGWHWNEKIZMIZLIZRJZSAGUFZWDWLWEEKIZWKLIZJWGX
      AJZWMWFWDWGXAWKWDWGWCWAWGGFWBDNOPWDXAWDWEGFZXAGFWDWACUGFZXDWAWBWCUHZWBWAX
      EWCCUIUJZBCGVTUGHVBUKQZWENTPWDWKWDWHWJWAWBWHGFWCWAWHWAWHUMULBUNUOUPUQWDWI
      GFZWJGFWAWBXIWCBCURUSZWINTUTPVAWDXBRWLWDWAXEXBRJXFXGBCVCQVDWDDVEFZVFDVGVH
      ZSZWEVEFZVFWEVGVHZSZXCWFVOWCWAXMWBWCXKXLDVIDVJVKOWDXDXPXHXDXNXOWEVIWEVJVK
      TDWEVLQVMWDXIWTWMVOXJWSWMAWIGWOWRWLRWOWQWKWGLWOWPWJWHMWNWIEKVPVNVNVQVRTVS
      $.
  $}

  ${
    $d a b c $.
    $( X is a Diophantine function.  (Contributed by Stefan O'Rear,
       17-Oct-2014.) $)
    rmxdioph $p |- { a e. ( NN0 ^m ( 1 ... 3 ) ) | ( ( a ` 1 ) e. ( ZZ>= ` 2 )
        /\ ( a ` 3 ) = ( ( a ` 1 ) rmX ( a ` 2 ) ) ) } e. ( Dioph ` 3 ) $=
      ( vb vc c1 cfv c2 wcel c3 co wceq wa cn0 cfz crab crmy cexp cmin c4 mp2an
      cmpt cv cuz crmx cmap cmul wrex cdioph simpr elmapi df-3 ssid jm2.27dlem5
      wb 2nn jm2.27dlem3 sselii ffvelcdm sylancl adantr 3nn rmxdiophlem syl3anc
      wf pm5.32da anass rexbii r19.42v bitr2i bitrdi rabbiia wsbc cres 3nn0 vex
      fvex df-2 1nn jm2.27dlem1 eleq1d oveq12d eqeq12d anbi12d oveq1d oveqan12d
      resex oveq1 eqeq1d sbc2ie rabbii 4nn0 rmydioph w3a simp1 simp3 simp2 df-4
      4nn rabren3dioph cz cmzp cvv ovex mzpproj mzpexpmpt mzpconstmpt mzpsubmpt
      2nn0 1z mzpmulmpt eqrabdioph mp3an anrabdioph eqeltri rexfrabdioph ) DAUA
      ZEZFUBEZGZHXOEZXPFXOEZUCIJZKZALDHMIZUDIZNXRBUAZXPXTOIZJZKZXSFPIZXPFPIZDQI
      ZYEFPIZUEIZQIZDJZKZBLUFZAYDNZHUGEZYBYQAYDXOYDGZYBXRYGYOKZBLUFZKZYQYTXRYAU
      UBYTXRKXRXTLGZXSLGZYAUUBUMYTXRUHYTUUDXRYTYCLXOVCZFYCGUUDXOLYCUIZDFMIZYCFF
      HHUJYCUKULZFUNUOZUPZYCLFXOUQURUSYTUUEXRYTUUFHYCGUUEUUGHUTUOZYCLHXOUQURUSB
      XPXTXSVAVBVDYQXRUUAKZBLUFUUCYPUUMBLXRYGYOVEVFXRUUABLVGVHVIVJHLGYPBRCUAZEZ
      VKAUUNYCVLZVKZCLDRMIZUDIZNZRUGEZGYRYSGVMUUTDUUNEZXQGZUUOUVBFUUNEZOIZJZKZH
      UUNEZFPIZUVBFPIZDQIZUUOFPIZUEIZQIZDJZKZCUUSNZUVAUUQUVPCUUSYPUVPABUUPUUOUU
      NYCCVNWERUUNVOXOUUPJZYEUUOJZKZYHUVGYOUVOUVTXRUVCYGUVFUVRXRUVCUMUVSUVRXPUV
      BXQDHACDDMIZYCDDFHVPUUIULDVQUOZUPVRZVSUSUVTYEUUOYFUVEUVRUVSUHUVRYFUVEJUVS
      UVRXPUVBXTUVDOUWCFHACUUKVRVTUSWAWBUVTYNUVNDUVTYIUVIYMUVMQUVRYIUVIJUVSUVRX
      SUVHFPHHACUULVRWCUSUVRUVSYKUVKYLUVLUEUVRYJUVJDQUVRXPUVBFPUWCWCWCYEUUOFPWF
      WDVTWGWBWHWIUVGCUUSNUVAGZUVOCUUSNUVAGZUVQUVAGRLGZDYEEZXQGZHYEEZUWGFYEEZOI
      ZJZKZBYDNYSGUWDWJBWKUWMUVGRDFRBCUWGUVBJZUWJUVDJZUWIUUOJZWLZUWHUVCUWLUVFUW
      QUWGUVBXQUWNUWOUWPWMZVSUWQUWIUUOUWKUVEUWNUWOUWPWNUWQUWGUVBUWJUVDOUWRUWNUW
      OUWPWOVTWAWBUWAUURDDFRVPFHRUJHRRWPUURUKULZULZULUWBUPZUUHUURFUWTUUJUPRWQUO
      ZWRSUWFCWSUURUDIZUVNTUURWTEZGZCUXCDTUXDGZUWEWJCUXCUVITUXDGZCUXCUVMTUXDGZU
      XECUXCUVHTUXDGZFLGZUXGUURXAGZHUURGUXIDRMXBZYCUURHUWSUULUPCUURHXCSXGCUVHFU
      URXDSCUXCUVKTUXDGZCUXCUVLTUXDGZUXHCUXCUVJTUXDGZUXFUXMCUXCUVBTUXDGZUXJUXOU
      XKDUURGUXPUXLUXACUURDXCSXGCUVBFUURXDSUXKDWSGUXFUXLXHCDUURXESZCUVJDUURXFSC
      UXCUUOTUXDGZUXJUXNUXKRUURGUXRUXLUXBCUURRXCSXGCUUOFUURXDSCUVKUVLUURXISCUVI
      UVMUURXFSUXQCUVNDRXJXKUVGUVOCRXLSXMYPBACRHWPXNSXM $.
  $}

  ${
    jm3.1.a $e |- ( ph -> A e. ( ZZ>= ` 2 ) ) $.
    jm3.1.b $e |- ( ph -> K e. ( ZZ>= ` 2 ) ) $.
    jm3.1.c $e |- ( ph -> N e. NN ) $.
    jm3.1.d $e |- ( ph -> ( K rmY ( N + 1 ) ) <_ A ) $.
    $( Lemma for ~ jm3.1 .  (Contributed by Stefan O'Rear, 16-Oct-2014.) $)
    jm3.1lem1 $p |- ( ph -> ( K ^ N ) < A ) $=
      ( cexp co c2 c1 cmin wcel syl cn cz clt wbr cc cuz cfv cr eluzelre nnnn0d
      cmul reexpcld 2z uzid ax-mp uz2mulcl sylancr uz2m1nn nnred cc0 nngt0d 2cn
      recnd mulcl 1cnd sub32d 2timesd mvrladdd oveq1d eqtrd breqtrrd mpbird crp
      posdifd wb eluz2nn nnrpd rpexpmord syl3anc mpbid caddc crmy nnzd peano2zd
      frmy fovcl syl2anc zred cn0 cle jm2.17a letrd ltletrd ) ACDIJZKCUFJZLMJZD
      IJZBACDACKUAUBZNZCUCNFKCUDOZADGUEZUGAWKDAWKAWJWMNZWKPNAKWMNZWNWQKQNWRUHKU
      IUJFKCUKULWJUMOZUNZWPUGZABWMNBUCNEKBUDOZACWKRSZWIWLRSZAXCUOWKCMJZRSAUOCLM
      JZXERAXFAWNXFPNFCUMOUPAXEWJCMJZLMJXFAWJLCAKTNCTNWJTNUQACWOURZKCUSULAUTXHV
      AAXGCLMAWJCCXHXHACXHVBVCVDVEVFACWKWOWTVIVGADPNCVHNWKVHNXCXDVJGACAWNCPNFCV
      KOVLAWKWSVLCWKDVMVNVOAWLCDLVPJZVQJZBXAAXJAWNXIQNXJQNFADADGVRVSCXIQWMQVQVT
      WAWBWCXBAWNDWDNWLXJWESFWPCDWFWBHWGWH $.

    $( Lemma for ~ jm3.1 .  (Contributed by Stefan O'Rear, 16-Oct-2014.) $)
    jm3.1lem2 $p |- ( ph -> ( K ^ N ) < ( ( ( ( 2 x. A ) x. K ) - ( K ^ 2 ) ) -
        1 ) ) $=
      ( co c2 cmul cmin c1 wcel cr syl caddc clt wbr recnd cexp eluzelre nnnn0d
      cuz cfv reexpcld 2re remulcl sylancr remulcld resqcld 1re resubcl sylancl
      resubcld jm3.1lem1 readdcld cz eluz2b1 simprbi cc0 wb cn nngt0d ltmulgt11
      eluz2nn syl3anc mpbid nnrpd ltaddrpd lttrd cle peano2re exp1d nnge1d nnuz
      uz2m1nn eleqtrdi leexp2ad eqbrtrrd lelttrd eluzelz zltp1le syl2anc lemul1
      syl112anc leadd1dd 1cnd addsub12d adddird sqvald oveq12d mulcld cc ax-1cn
      mulcl pncan2d mullidd 3eqtrd oveq1d oveq2d subadd23d 3eqtr3d 2cnd mulassd
      2timesd eqtrd sub32d addsubassd 3brtr4d ltletrd ) ACDUAIZBJBKIZCKIZCJUAIZ
      LIZMLIZACDACJUDUEZNZCONZFJCUBPZADGUCUFZABXRNZBONZEJBUBPZAXPONMONZXQONAXNX
      OAXMCAJONYDXMONUGYEJBUHUIYAUJACYAUKZUOULXPMUMUNZABCDEFGHUPZABBCKIZCMLIZQI
      ZXQYEAYJYKABCYEYAUJZAXTYFYKONYAULCMUMUNUQZYHABYJYLYEYMYNAMCRSZBYJRSZAXSYO
      FXSCURNZYOCUSUTPAYDXTVABRSYOYPVBYEYAABAYCBVCNEBVFPVDBCVEVGVHAYJYKYMAYKAXS
      YKVCNFCVQPVIVJVKACMQIZCKIZYJMLIZXOLIZQIZYJUUAQIZYLXQVLAYSYJUUAAYRCAXTYRON
      ZYACVMPZYAUJZYMAYTXOAYJONYFYTONYMULYJMUMUNZYGUOAYRBVLSZYSYJVLSZACBRSZUUHA
      CXLBYAYBYEACMUAICXLVLACACYATZVNACMDYAACAXSCVCNFCVFPZVOADVCMUDUEGVPVRVSVTY
      IWAAYQBURNZUUJUUHVBAXSYQFJCWBPAYCUUMEJBWBPCBWCWDVHAUUDYDXTVACRSUUHUUIVBUU
      EYEYAACUULVDYRBCWEWFVHWGAYJYSXOLIZMLIZQIUUNYTQIYLUUBAYJUUNMAYJYMTZAUUNAYS
      XOUUFYGUOTAWHZWIAUUOYKYJQAUUNCMLAUUNCCKIZMCKIZQIZUURLIUUSCAYSUUTXOUURLACM
      CUUKUUQUUKWJACUUKWKWLAUURUUSACCUUKUUKWMAMWNNCWNNUUSWNNWOUUKMCWPUIWQACUUKW
      RWSWTXAAYSXOYTAYSUUFTAXOYGTZAYTUUGTZXBXCAXQYJYJQIZXOLIZMLIUVCMLIZXOLIZUUC
      AXPUVDMLAXNUVCXOLAXNJYJKIUVCAJBCAXDABYETUUKXEAYJUUPXFXGWTWTAUVCXOMAUVCAYJ
      YJYMYMUQTUVAUUQXHAUVFYJYTQIZXOLIUUCAUVEUVGXOLAYJYJMUUPUUPUUQXIWTAYJYTXOUU
      PUVBUVAXIXGWSXJXKVK $.

    $( Lemma for ~ jm3.1 .  (Contributed by Stefan O'Rear, 17-Oct-2014.) $)
    jm3.1lem3 $p |- ( ph -> ( ( ( ( 2 x. A ) x. K ) -
        ( K ^ 2 ) ) - 1 ) e. NN ) $=
      ( c2 cmul co cexp cmin c1 cz wcel cc0 clt cn syl wbr cuz cfv eluzelz nnzd
      zmulcl sylancr eluz2nn zmulcld zsqcl zsubcld peano2zm 0red nnexpcld nnred
      2z nnnn0d zred nngt0d jm3.1lem2 lttrd elnnz sylanbrc ) AIBJKZCJKZCILKZMKZ
      NMKZOPZQVHRUAVHSPAVGOPVIAVEVFAVDCAIOPBOPZVDOPUPABIUBUCZPVJEIBUDTIBUFUGACA
      CVKPCSPFCUHTZUEZUIACOPVFOPVMCUJTUKVGULTZAQCDLKZVHAUMAVOACDVLADGUQUNZUOAVH
      VNURAVOVPUSABCDEFGHUTVAVHVBVC $.
  $}

  $( Diophantine expression for exponentiation.  Lemma 3.1 of
     [JonesMatijasevic] p. 698.  (Contributed by Stefan O'Rear,
     16-Oct-2014.) $)
  jm3.1 $p |- ( ( ( A e. ( ZZ>= ` 2 ) /\ K e. ( ZZ>= ` 2 ) /\ N e. NN ) /\
      ( K rmY ( N + 1 ) ) <_ A ) -> ( K ^ N ) = ( ( ( A rmX N ) - ( ( A - K )
        x. ( A rmY N ) ) ) mod ( ( ( ( 2 x. A ) x. K ) - ( K ^ 2 ) ) -
        1 ) ) ) $=
    ( c2 wcel cn c1 co crmy wbr cexp crmx cmin cmul cn0 adantr syl3anc 3ad2ant3
    wa cz cuz cfv w3a caddc cle wceq cdvds simpl1 simpl2 simpl3 simpr jm3.1lem2
    cmo clt eluzge2nn0 3ad2ant2 nnnn0d jm2.18 wb simp1 frmx fovcl syl2anc nn0zd
    nnz eluzelz zsubcl syl2an 3adant3 zmulcld zsubcld jm3.1lem3 nnnn0 nn0expcld
    frmy divalgmodcl mpbir2and ) ADUAUBZEZBVREZCFEZUCZBCGUDHIHAUEJZSZBCKHZACLHZ
    ABMHZACIHZNHZMHZDANHBNHBDKHMHGMHZUMHUFZWEWKUNJZWKWJWEMHUGJZWDABCVSVTWAWCUHZ
    VSVTWAWCUIZVSVTWAWCUJZWBWCUKZULWDVSBOEZCOEZWNWOWBWSWCVTVSWSWABUOUPZPWDCWQUQ
    ABCURQWDWJTEZWKFEWEOEZWLWMWNSUSWBXBWCWBWFWIWBWFWBVSCTEZWFOEVSVTWAUTZWAVSXDV
    TCVERZACOVRTLVAVBVCVDWBWGWHVSVTWGTEZWAVSATEBTEXGVTDAVFDBVFABVGVHVIWBVSXDWHT
    EXEXFACTVRTIVOVBVCVJVKPWDABCWOWPWQWRVLWBXCWCWBBCXAWAVSWTVTCVMRVNPWKWEWJVPQV
    Q $.

  ${
    $d A d e f $.  $d B d e f $.  $d C d e f $.
    $( Lemma for ~ expdioph .  Fully expanded expression for exponential.
       (Contributed by Stefan O'Rear, 17-Oct-2014.) $)
    expdiophlem1 $p |- ( C e. NN0 -> ( ( ( A e. ( ZZ>= ` 2 ) /\ B e. NN ) /\ C
        = ( A ^ B ) ) <-> E. d e. NN0 E. e e. NN0 E. f e. NN0 ( ( A e. ( ZZ>= `
        2 ) /\ B e. NN ) /\ ( ( A e. ( ZZ>= ` 2 ) /\ d = ( A rmY ( B + 1 ) ) )
        /\ ( ( d e. ( ZZ>= ` 2 ) /\ e = ( d rmY B ) ) /\ ( ( d e. ( ZZ>= ` 2 )
        /\ f = ( d rmX B ) ) /\ ( C < ( ( ( ( 2 x. d ) x. A ) - ( A ^ 2 ) ) - 1
        ) /\ ( ( ( ( 2 x. d ) x. A ) - ( A ^ 2 ) ) - 1 ) || ( ( f - ( ( d - A )
        x. e ) ) - C ) ) ) ) ) ) ) ) $=
      ( cn0 wcel c2 wa co wceq c1 cmul cmin wbr cdvds wrex syl cz cuz cfv cn cv
      cexp caddc crmy crmx clt cmo cle cr 2re a1i nnre peano2re adantl peano2zd
      frmy fovcl sylan2 zred elnnuz eluzp1p1 df-2 fveq2i eleqtrrdi sylbi eluzle
      nnz nnnn0 peano2nn0 rmygeid letrd wb 2z eluz sylancr mpbird simprl simprr
      leidd jm3.1 syl31anc eqeq2d frmx syl2anc eluzelz adantr zsubcld jm3.1lem3
      nn0zd zmulcld simpl divalgmodcl syl3anc bitrd rmynn0 oveq1d breq2d oveq2d
      oveq1 oveq2 breq12d anbi12d rexbidv ceqsrexv anbi2d 3bitrrd r19.42v bitri
      ad2antll anbi2i rexbii eleq1 syl5ibrcom imp ibar anbi1d pm5.32da ad2antrl
      bitr4di 2rexbidv 2rexbii ) CGHZAIUAUBZHZBUCHZJZCABUEKZLZJYIYGFUDZABMUFKZU
      GKZLZJZYLYFHZDUDZYLBUGKZLZJZYQEUDZYLBUHKZLZJZCIYLNKZANKZAIUEKZOKZMOKZUIPZ
      UUJUUBYLAOKZYRNKZOKZCOKZQPZJZJZJZJZEGRZDGRZFGRZJZYIUUTJEGRZDGRFGRZYEYIYKU
      VCYEYIJZYKCIYNNKZANKZUUHOKZMOKZUIPZUVKYNBUHKZYNAOKZYNBUGKZNKZOKZCOKZQPZJZ
      UVCUVGYKCUVQUVKUJKZLZUVTUVGYJUWACUVGYNYFHZYGYHYNYNUKPZYJUWALYIUWCYEYIUWCI
      YNUKPZYIIYMYNIULHYIUMUNYHYMULHZYGYHBULHUWFBUOBUPSUQYIYNYHYGYMTHYNTHZYHBBV
      JZURAYMTYFTUGUSUTVAZVBZYHIYMUKPZYGYHYMYFHZUWKYHBMUAUBHZUWLBVCUWMYMMMUFKZU
      AUBYFMBVDIUWNUAVEVFVGVHIYMVISUQYHYGYMGHZYMYNUKPYHBGHZUWOBVKZBVLSZAYMVMVAV
      NYIITHUWGUWCUWEVOVPUWIIYNVQVRVSZUQZYEYGYHVTZYEYGYHWAZYIUWDYEYIYNUWJWBUQZY
      NABWCWDWEUVGUVQTHZUVKUCHYEUWBUVTVOYIUXDYEYIUVMUVPYIUVMYIUWCBTHZUVMGHZUWSY
      HUXEYGUWHUQZYNBGYFTUHWFUTZWGWLYIUVNUVOYIYNAUWIYGATHYHIAWHWIWJYIUWCUXEUVOT
      HUWSUXGYNBTYFTUGUSUTWGWMWJUQUVGYNABUWTUXAUXBUXCWKYEYIWNUVKCUVQWOWPWQUVGUV
      TYOYTUUDUUQJZJZJZEGRZDGRZFGRZUVCUVGUVTYOYTUXIEGRZJZDGRZJZFGRZUXNUVGUXSYRU
      VOLZUUBUVMLZUVLUVKUUBUVNYRNKZOKZCOKZQPZJZJZEGRZJZDGRZUYAUVLUVKUUBUVPOKZCO
      KZQPZJZJZEGRZUVTUVGYNGHZUXSUYJVOYIUYQYEYHYGUWOUYQUWRAYMWRVAUQUXQUYJFYNGYO
      UXPUYIDGYOYTUXTUXOUYHYOYSUVOYRYLYNBUGXBWEYOUXIUYGEGYOUUDUYAUUQUYFYOUUCUVM
      UUBYLYNBUHXBWEYOUUKUVLUUPUYEYOUUJUVKCUIYOUUIUVJMOYOUUGUVIUUHOYOUUFUVHANYL
      YNINXCWSWSWSZWTYOUUJUVKUUOUYDQUYRYOUUNUYCCOYOUUMUYBUUBOYOUULUVNYRNYLYNAOX
      BWSXAWSXDXEXEXFXEXFXGSUVGUVOGHZUYJUYPVOUVGUWCUWPUYSUWTYHUWPYEYGUWQXLYNBWR
      WGUYHUYPDUVOGUXTUYGUYOEGUXTUYFUYNUYAUXTUYEUYMUVLUXTUYDUYLUVKQUXTUYCUYKCOU
      XTUYBUVPUUBOYRUVOUVNNXCXAWSWTXHXHXFXGSUVGUXFUYPUVTVOUVGUWCUXEUXFUWTYHUXEY
      EYGUWHXLUXHWGUYNUVTEUVMGUYAUYMUVSUVLUYAUYLUVRUVKQUYAUYKUVQCOUUBUVMUVPOXBW
      SWTXHXGSXIUXMUXRFGUXMYOUXPJZDGRUXRUXLUYTDGUXLYOUXJEGRZJUYTYOUXJEGXJVUAUXP
      YOYTUXIEGXJXMXKXNYOUXPDGXJXKXNYBUVGUXLUVAFDGGUVGUXKUUTEGUVGUXKYOUUSJUUTUV
      GYOUXJUUSUVGYOJYQUXJUUSVOUVGYOYQUVGYQYOUWCUWTYLYNYFXOXPXQYQYTUUAUXIUURYQY
      TXRYQUUDUUEUUQYQUUDXRXSXESXTUVGYOYPUUSYGYOYPVOYEYHYGYOXRYAXSWQXFYCWQWQXTU
      VFYIUVAJZDGRZFGRZUVDUVEVUBFDGGYIUUTEGXJYDVUDYIUVBJZFGRUVDVUCVUEFGYIUVADGX
      JXNYIUVBFGXJXKXKYB $.
  $}

  ${
    $d a b c d e $.

    $( Lemma for ~ expdioph .  Exponentiation on a restricted domain is
       Diophantine.  (Contributed by Stefan O'Rear, 17-Oct-2014.) $)
    expdiophlem2 $p |- { a e. ( NN0 ^m ( 1 ... 3 ) ) | ( ( ( a ` 1 ) e. ( ZZ>=
        ` 2 ) /\ ( a ` 2 ) e. NN ) /\ ( a ` 3 ) = ( ( a ` 1 ) ^ ( a ` 2 ) ) ) }
        e. ( Dioph ` 3 ) $=
      ( vb ve c1 cfv c2 wcel wa c3 co wceq cn0 crab cmin c6 c4 anbi12d mp2an c7
      cmpt vc vd cv cuz cexp cfz cmap caddc crmy crmx cmul clt wbr cdvds cdioph
      cn wb wf elmapi 3nn jm2.27dlem3 ffvelcdm sylancl expdiophlem1 syl rabbiia
      wrex wsbc c5 cres 3nn0 fvex eqeq1 anbi2d adantr adantl simpr oveq2 oveq1d
      oveq12d breq2d sbc2ie sbcbii resex df-2 df-3 ssid jm2.27dlem5 jm2.27dlem1
      vex 1nn sselii eleq1d 2nn jm2.27dlem2 eqeqan12rd eleq1 oveqan12rd breq12d
      id eqeq2d oveq2d bitri rabbii cz cmzp 6nn0 2z ovex df-4 df-5 df-6 mzpproj
      eluzrabdioph mp3an elnnrabdioph anrabdioph peano2nn0 ceqsrexv 3syl bicomd
      cvv 4nn oveqan12d eqeq12d 7nn0 df-7 6nn 1z mzpconstmpt rmydioph w3a simp1
      simp3 simp2 rabren3dioph eqeltri 5nn mzpmulmpt mzpsubmpt 7nn rexfrabdioph
      mzpaddmpt eqrabdioph 2nn0 mzpexpmpt ltrabdioph dvdsrabdioph 3rexfrabdioph
      rmxdioph ) DAUCZEZFUDEZGZFUUKEZUPGZHZIUUKEZUULUUOUEJKHZALDIUFJZUGJZMUUQUU
      NBUCZUULUUODUHJZUIJZKZHZUVBUUMGZUAUCZUVBUUOUIJZKZHZUVGUBUCZUVBUUOUJJZKZHZ
      UURFUVBUKJZUULUKJZUULFUEJZNJZDNJZULUMZUVTUVLUVBUULNJZUVHUKJZNJZUURNJZUNUM
      ZHZHZHZHZHZUBLVGUALVGBLVGZAUVAMZIUOEZUUSUWLAUVAUUKUVAGZUURLGZUUSUWLUQUWOU
      UTLUUKURIUUTGUWPUUKLUUTUSIUTVAZUUTLIUUKVBVCUULUUOUURUAUBBVDVEVFILGUWKUBOC
      UCZEZVHUAVIUWREZVHZBPUWREZVHZAUWRUUTVJZVHZCLDOUFJZUGJZMZOUOEZGUWMUWNGVKUX
      HDUWREZUUMGZFUWREZUPGZHZUXKUXBUXJUXLDUHJZUIJZKZHZUXBUUMGZUWTUXBUXLUIJZKZH
      ZUXSUWSUXBUXLUJJZKZHZIUWREZFUXBUKJZUXJUKJZUXJFUEJZNJZDNJZULUMZUYKUWSUXBUX
      JNJZUWTUKJZNJZUYFNJZUNUMZHZHZHZHZHZCUXGMZUXIUXEVUBCUXGUXEUUQUVFUVGUWTUVIK
      ZHZUVGUWSUVMKZHZUWAUVTUWSUWBUWTUKJZNJZUURNJZUNUMZHZHZHZHZHZBUXBVHZAUXDVHV
      UBUXCVUQAUXDUXAVUPBUXBUWKVUPUAUBUWTUWSVIUWRVLOUWRVLUVHUWTKZUVLUWSKZHZUWJV
      UOUUQVUTUWIVUNUVFVUTUVKVUEUWHVUMVURUVKVUEUQVUSVURUVJVUDUVGUVHUWTUVIVMVNVO
      VUTUVOVUGUWGVULVUSUVOVUGUQVURVUSUVNVUFUVGUVLUWSUVMVMVNVPVUTUWFVUKUWAVUTUW
      EVUJUVTUNVUTUWDVUIUURNVUTUVLUWSUWCVUHNVURVUSVQVURUWCVUHKVUSUVHUWTUWBUKVRV
      OVTVSWAVNQQVNVNWBWCWCVUPVUBABUXDUXBUWRUUTCWJWDPUWRVLUUKUXDKZUVBUXBKZHZUUQ
      UXNVUOVUAVVAUUQUXNUQVVBVVAUUNUXKUUPUXMVVAUULUXJUUMDIACDDUFJZUUTDDFIWEFIIW
      FUUTWGWHWHDWKVAZWLWIZWMZVVAUUOUXLUPFIACFFIFWNVAZWFWNWOWIZWMQVOVVCUVFUXRVU
      NUYTVVCUUNUXKUVEUXQVVAUUNUXKUQVVBVVGVOVVBVVAUVBUXBUVDUXPVVBWTZVVAUULUXJUV
      CUXOUIVVFVVAUUOUXLDUHVVIVSVTWPQVVCVUEUYBVUMUYSVVCUVGUXSVUDUYAVVBUVGUXSUQV
      VAUVBUXBUUMWQVPZVVCUVIUXTUWTVVBVVAUVBUXBUUOUXLUIVVJVVIWRXAQVVCVUGUYEVULUY
      RVVCUVGUXSVUFUYDVVKVVCUVMUYCUWSVVBVVAUVBUXBUUOUXLUJVVJVVIWRXAQVVCUWAUYLVU
      KUYQVVCUURUYFUVTUYKULVVAUURUYFKVVBIIACUWQWIVOZVVCUVSUYJDNVVCUVQUYHUVRUYIN
      VVBVVAUVPUYGUULUXJUKUVBUXBFUKVRVVFWRVVAUVRUYIKVVBVVAUULUXJFUEVVFVSVOVTVSZ
      WSVVCUVTUYKVUJUYPUNVVMVVCVUIUYOUURUYFNVVCVUHUYNUWSNVVCUWBUYMUWTUKVVCUVBUX
      BUULUXJNVVAVVBVQVVAUULUXJKVVBVVFVOVTVSXBVVLVTWSQQQQQWBXCXDUXNCUXGMUXIGZVU
      ACUXGMUXIGZVUCUXIGUXKCUXGMUXIGZUXMCUXGMUXIGZVVNOLGZFXEGZCXEUXFUGJZUXJTUXF
      XFEZGZVVPXGXHUXFYBGZDUXFGVWBDOUFXIZVVDUXFDDFOWEFIOWFIPOXJPVIOXKVIOOXLUXFW
      GWHWHZWHZWHZWHVVEWLZCUXFDXMRZCUXJFOXNXOVVRCVVTUXLTVWAGZVVQXGVWCFUXFGZVWJV
      WDDFUFJUXFFVWGVVHWLZCUXFFXMRCUXLOXPRUXKUXMCOXQRUXRCUXGMZUXIGUYTCUXGMUXIGZ
      VVOVWMUVBUXOKZUXKUXBUXJUVBUIJZKZHZHZBLVGZCUXGMZUXIUXRVWTCUXGUWRUXGGZVWTUX
      RVXBUXLLGZUXOLGVWTUXRUQVXBUXFLUWRURVWKVXCUWRLUXFUSVWLUXFLFUWRVBVCUXLXRVWR
      UXRBUXOLVWOVWQUXQUXKVWOVWPUXPUXBUVBUXOUXJUIVRXAVNXSXTYAVFVVRVWSBSUUKEZVHC
      UUKUXFVJZVHZALDSUFJZUGJZMZSUOEZGVXAUXIGXGVXIVXDUVCKZUUNPUUKEZUULVXDUIJZKZ
      HZHZAVXHMZVXJVXFVXPAVXHVWSVXPCBVXEVXDUUKUXFAWJWDSUUKVLUWRVXEKZUVBVXDKZHZV
      WOVXKVWRVXOVXSVXRUVBVXDUXOUVCVXSWTZVXRUXLUUODUHFOCAVWLWIVSWPVXTUXKUUNVWQV
      XNVXTUXJUULUUMVXRUXJUULKVXSDOCAVWHWIZVOWMVXTUXBVXLVWPVXMVXRUXBVXLKVXSPOCA
      DPUFJUXFPVWEPYCVAWLZWIVOVXRVXSUXJUULUVBVXDUIVYBVYAYDYEQQWBXDVXKAVXHMVXJGZ
      VXOAVXHMVXJGZVXQVXJGSLGZAXEVXGUGJZVXDTVXGXFEZGZAVYGUVCTVYHGZVYDYFVXGYBGZS
      VXGGVYIDSUFXIZSUUAVAZAVXGSXMRAVYGUUOTVYHGZAVYGDTVYHGZVYJVYKFVXGGVYNVYLFOS
      VWLYGYHWOAVXGFXMRVYKDXEGZVYOVYLYIADVXGYJRAUUODVXGUUCRAVXDUVCSUUDXOVYFDUVB
      EZUUMGZIUVBEZVYQFUVBEZUIJZKZHZBUVAMUWNGVYEYFBYKWUCVXOSDSPBAVYQUULKZVYTVXD
      KZVYSVXLKZYLZVYRUUNWUBVXNWUGVYQUULUUMWUDWUEWUFYMZWMWUGVYSVXLWUAVXMWUDWUEW
      UFYNWUGVYQUULVYTVXDUIWUHWUDWUEWUFYOVTYEQDOSVWHYGYHWOVYMPOSVYCYGYHWOYPRVXK
      VXOASXQRYQVWSBCASOYGUUBRYQUYBCUXGMUXIGZUYSCUXGMUXIGZVWNVVRUUNUURUULUUOUIJ
      ZKZHZAUVAMUWNGWUIXGAYKWUMUYBOPFVIACUULUXBKZUUOUXLKZUURUWTKZYLZUUNUXSWULUY
      AWUQUULUXBUUMWUNWUOWUPYMZWMWUQUURUWTWUKUXTWUNWUOWUPYNWUQUULUXBUUOUXLUIWUR
      WUNWUOWUPYOVTYEQVYCVWLVIVIOVIYRVAXLYRWOZYPRUYECUXGMUXIGZUYRCUXGMUXIGZWUJV
      VRUUNUURUULUUOUJJZKZHZAUVAMUWNGWUTXGAUUJWVDUYEOPFOACWUNWUOUURUWSKZYLZUUNU
      XSWVCUYDWVFUULUXBUUMWUNWUOWVEYMZWMWVFUURUWSWVBUYCWUNWUOWVEYNWVFUULUXBUUOU
      XLUJWVGWUNWUOWVEYOVTYEQVYCVWLOYHVAZYPRUYLCUXGMUXIGZUYQCUXGMUXIGZWVAVVRCVV
      TUYFTVWAGZCVVTUYKTVWAGZWVIXGVWCIUXFGWVKVWDUUTUXFIVWFUWQWLCUXFIXMRZCVVTUYJ
      TVWAGZCVVTDTVWAGZWVLCVVTUYHTVWAGZCVVTUYITVWAGZWVNCVVTUYGTVWAGZVWBWVPCVVTF
      TVWAGZCVVTUXBTVWAGZWVRVWCVVSWVSVWDXHCFUXFYJRVWCPUXFGWVTVWDVYCCUXFPXMRZCFU
      XBUXFYSRVWICUYGUXJUXFYSRVWBFLGWVQVWIUUECUXJFUXFUUFRCUYHUYIUXFYTRVWCVYPWVO
      VWDYICDUXFYJRCUYJDUXFYTRZCUYFUYKOUUGXOVVRWVLCVVTUYPTVWAGZWVJXGWWBCVVTUYOT
      VWAGZWVKWWCCVVTUWSTVWAGZCVVTUYNTVWAGZWWDVWCOUXFGWWEVWDWVHCUXFOXMRCVVTUYMT
      VWAGZCVVTUWTTVWAGZWWFWVTVWBWWGWWAVWICUXBUXJUXFYTRVWCVIUXFGWWHVWDWUSCUXFVI
      XMRCUYMUWTUXFYSRCUWSUYNUXFYTRWVMCUYOUYFUXFYTRCUYKUYPOUUHXOUYLUYQCOXQRUYEU
      YRCOXQRUYBUYSCOXQRUXRUYTCOXQRUXNVUACOXQRYQUWKUBUABACOVIPIXJXKXLUUIRYQ $.

    $( The exponential function is Diophantine.  This result completes and
       encapsulates our development using Pell equation solution sequences and
       is sometimes regarded as Matiyasevich's theorem properly.  (Contributed
       by Stefan O'Rear, 17-Oct-2014.) $)
    expdioph $p |- { a e. ( NN0 ^m ( 1 ... 3 ) ) | ( a ` 3 ) = ( ( a ` 1 ) ^ (
        a ` 2 ) ) } e. ( Dioph ` 3 ) $=
      ( c3 cfv c1 c2 cexp co wceq cn0 cfz crab cn wcel wa wo cc0 wb eqeq2d 3nn0
      mp2an cv cmap cdioph wn pm4.42 ancom wf elmapi df-2 df-3 ssid jm2.27dlem5
      cuz 1nn jm2.27dlem3 sselii ffvelcdm sylancl adantr elnn1uz2 biimpi orim1i
      elnn0 sylib syl biantrurd andir orbi1i bitri nnz 1exp adantl oveq1 bibi1d
      cz syl5ibrcom pm5.32d iba anbi1d orbi12d bitrid bitrd pm5.32da 2nn pm2.53
      0exp sylbi 0nnn eleq1 mtbiri impbid1 nn0cnd exp0d oveq2 rabbiia cmpt cmzp
      wi cvv ovex mzpproj elnnrabdioph 1z mzpconstmpt eqrabdioph 3nn anrabdioph
      mp3an expdiophlem2 orrabdioph eq0rabdioph eqeltri ) BAUAZCZDXMCZEXMCZFGZH
      ZAIDBJGZUBGZKXPLMZXODHZXNDHZNZXOEUMCMZYANZXRNZOZXOPHZXNPHZNZOZNZXPPHZYCNZ
      OZAXTKZBUCCZXRYPAXTXRXRYANZXRYAUDZNZOXMXTMZYPXRYAUEUUBYSYMUUAYOYSYAXRNUUB
      YMXRYAUFUUBYAXRYLUUBYANZXRYBYEOZYIOZXRNZYLUUCUUEXRUUCXOLMZYIOZUUEUUCXOIMZ
      UUHUUBUUIYAUUBXSIXMUGZDXSMZUUIXMIXSUHZDDJGXSDDEBUIEBBUJXSUKULZULDUNUOUPZX
      SIDXMUQURZUSXOVCVDUUGUUDYIUUGUUDXOUTVAVBVEVFUUFYBXRNZYEXRNZOZYIXRNZOZUUCY
      LUUFUUDXRNZUUSOUUTUUDYIXRVGUVAUURUUSYBYEXRVGVHVIUUCUURYHUUSYKUUCUUPYDUUQY
      GUUCYBXRYCUUCXRYCQZYBXNDXPFGZHZYCQUUCUVCDXNYAUVCDHZUUBYAXPVOMUVEXPVJXPVKV
      EVLRYBXRUVDYCYBXQUVCXNXODXPFVMRVNVPVQUUCYEYFXRYAYEYFQUUBYAYEVRVLVSVTUUCYI
      XRYJUUCXRYJQYIXNPXPFGZHZYJQUUCUVFPXNYAUVFPHUUBXPWFVLRYIXRUVGYJYIXQUVFXNXO
      PXPFVMRVNVPVQVTWAWBWCWAUUAYTXRNZUUBYOXRYTUFUUBUVHYNXRNYOUUBYTYNXRUUBXPIMZ
      YTYNQUUBUUJEXSMZUVIUULDEJGXSEUUMEWDUOUPZXSIEXMUQURUVIYTYNUVIYAYNOYTYNWRXP
      VCYAYNWEWGYNYAPLMWHXPPLWIWJWKVEVSUUBYNXRYCUUBUVBYNXNXOPFGZHZYCQUUBUVLDXNU
      UBXOUUBXOUUOWLWMRYNXRUVMYCYNXQUVLXNXPPXOFWNRVNVPVQWBWAVTWAWOYMAXTKYRMZYOA
      XTKYRMZYQYRMYAAXTKYRMZYLAXTKYRMZUVNBIMZAVOXSUBGZXPWPXSWQCZMZUVPSXSWSMZUVJ
      UWADBJWTZUVKAXSEXATZAXPBXBTYHAXTKYRMZYKAXTKYRMZUVQYDAXTKYRMZYGAXTKYRMUWEY
      BAXTKYRMZYCAXTKYRMZUWGUVRAUVSXOWPUVTMZAUVSDWPUVTMZUWHSUWBUUKUWJUWCUUNAXSD
      XATZUWBDVOMUWKUWCXCADXSXDTZAXODBXEXHUVRAUVSXNWPUVTMZUWKUWISUWBBXSMUWNUWCB
      XFUOAXSBXATZUWMAXNDBXEXHZYBYCABXGTAXIYDYGABXJTYIAXTKYRMZYJAXTKYRMZUWFUVRU
      WJUWQSUWLAXOBXKTUVRUWNUWRSUWOAXNBXKTYIYJABXGTYHYKABXJTYAYLABXGTYNAXTKYRMZ
      UWIUVOUVRUWAUWSSUWDAXPBXKTUWPYNYCABXGTYMYOABXJTXL $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Uncategorized stuff not associated with a major project
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x y A $.  $d x y B $.
    $( Set induction for sets contained in a transitive set.  If we are allowed
       to assume Infinity, then all sets have a transitive closure and this
       reduces to ~ setind ; however, this version is useful without Infinity.
       (Contributed by Stefan O'Rear, 28-Oct-2014.) $)
    setindtr $p |- ( A. x ( x C_ A -> x e. A ) -> ( E. y ( Tr y /\ B e. y ) ->
        B e. A ) ) $=
      ( cv wtr wcel wa wex wss wi wal c0 wceq cin wn sylib adantlr ex cvv impel
      cdif wrex wral nfv nfa1 nfan eldifn adantl trss eldifi sseq1d sp ad2antlr
      dfss2 sylbid inssdif0 sylnib ralrimi ralnex wne vex difexi zfreg necon1bi
      mtod mpan syl ssdif0 sylibr simplr sseldd exlimiv com12 ) BEZFZDVOGZHZBIA
      EZCJZVSCGZKZALZDCGZVRWCWDKBVRWCWDVRWCHVOCDVPWCVOCJZVQVPWCHZVOCUBZMNZWEWFV
      SWGOMNZAWGUCZPZWHWFWIPZAWGUDWKWFWLAWGVPWCAVPAUEWBAUFUGWFVSWGGZWLWFWMHZVSV
      OOZCJZWIWNWPWAWMWAPWFVSVOCUHUIWNWPVTWAWNWOVSCVPWMWOVSNZWCVPWMHVSVOJZWQVPV
      SVOGWRWMVOVSUJVSVOCUKUAVSVOUOQRULWCWBVPWMWBAUMUNUPVFVSVOCUQURSUSWIAWGUTQW
      JWGMWGTGWGMVAWJVOCBVBVCAWGTVDVGVEVHVOCVIVJRVPVQWCVKVLSVMVN $.
  $}

  ${
    $d B a x z $.  $d ph y $.  $d ps x $.  $d ch x $.  $d ph a z $.
    $d a x y $.
    setindtrs.a $e |- ( A. y e. x ps -> ph ) $.
    setindtrs.b $e |- ( x = y -> ( ph <-> ps ) ) $.
    setindtrs.c $e |- ( x = B -> ( ph <-> ch ) ) $.
    $( Set induction scheme without Infinity.  See comments at ~ setindtr .
       (Contributed by Stefan O'Rear, 28-Oct-2014.) $)
    setindtrs $p |- ( E. z ( Tr z /\ B e. z ) -> ch ) $=
      ( va cv wtr wcel wa wex wi wral nfsab1 cvv cab setindtr dfss3 nfcv nfralw
      wss nfim weq raleq eleq1w imbi12d vex elab abid 3imtr4i chvarfv sylbi mpg
      ralbii wb elex adantl exlimiv elabg syl mpbid ) FLZMZGVGNZOZFPZGADUAZNZCK
      LZVLUFZVNVLNZQVKVMQKKFVLGUBVOELZVLNZEVNRZVPEVNVLUCVREDLZRZVTVLNZQVSVPQDKV
      SVPDVRDEVNDVNUDADESUEADKSUGDKUHWAVSWBVPVREVTVNUIDKVLUJUKBEVTRAWAWBHVRBEVT
      ABDVQEULIUMUSADUNUOUPUQURVKGTNZVMCUTVJWCFVIWCVHGVGVAVBVCACDGTJVDVEVF $.
  $}

  ${
    $d a b c x y $.  $d N a b c x y $.

    $( Lemma for ~ dford3 .  (Contributed by Stefan O'Rear, 28-Oct-2014.) $)
    dford3lem1 $p |- ( ( Tr N /\ A. y e. N Tr y ) ->
        A. b e. N ( Tr b /\ A. y e. b Tr y ) ) $=
      ( wtr cv wral wa treq cbvralvw bilani wcel wss trss ssralv syl6 com23 imp
      wi ralrimiv r19.26 sylanbrc ) BDZAEZDZABFZGZCEZDZCBFZUDAUGFZCBFUHUJGCBFUE
      UIUBUDUHACBUCUGHIJUFUJCBUBUEUGBKZUJRUBUKUEUJUBUKUGBLUEUJRBUGMUDAUGBNOPQSU
      HUJCBTUA $.

    $( Lemma for ~ dford3 .  (Contributed by Stefan O'Rear, 28-Oct-2014.) $)
    dford3lem2 $p |- ( ( Tr x /\ A. y e. x Tr y ) -> x e. On ) $=
      ( vc va vb cv wtr wa wral con0 wcel vex treq anbi12d wi word sylibr raleq
      weq eleq1w wel wex csuc suctr sucid sucex wceq eleq2 spcev sylancl adantr
      wss simprl dford3lem1 ralim syl5 imp dfss3 ordon a1i trssord syl3anc elon
      ex imbi12d setindtrs mpcom ) CFZGZACUAZHZCUBZAFZGZBFGZBVMIZHZVMJKZVNVLVPV
      NVMUCZGZVMVSKZVLVMUDVMALZUEVKVTWAHCVSVMWBUFVHVSUGVIVTVJWAVHVSMVHVSVMUHNUI
      UJUKDFZGZVOBWCIZHZWCJKZOEFZGZVOBWHIZHZWHJKZOZVQVRODECVMWMEWCIZWFWGWNWFHZW
      CPZWGWOWDWCJULZJPZWPWNWDWEUMWOWLEWCIZWQWNWFWSWFWKEWCIWNWSBWCEUNWKWLEWCUOU
      PUQEWCJURQWRWOUSUTWCJVAVBWCDLVCQVDDESZWFWKWGWLWTWDWIWEWJWCWHMVOBWCWHRNDEJ
      TVEDASZWFVQWGVRXAWDVNWEVPWCVMMVOBWCVMRNDAJTVEVFVG $.

    $( Ordinals are precisely the hereditarily transitive classes.  Definition
       1.2 of [Schloeder] p. 1.  (Contributed by Stefan O'Rear,
       28-Oct-2014.) $)
    dford3 $p |- ( Ord N <-> ( Tr N /\ A. x e. N Tr x ) ) $=
      ( va word wtr cv wral wa ordtr wcel ordelord syl ralrimiva jca con0 simpl
      wss dford3lem1 dford3lem2 ralimi dfss3 sylibr a1i trssord syl3anc impbii
      ordon ) BDZBEZAFZEZABGZHZUHUIULBIUHUKABUHUJBJHUJDUKBUJKUJILMNUMUIBOQZODZU
      HUIULPUMCFZOJZCBGZUNUMUPEUKAUPGHZCBGURABCRUSUQCBCASTLCBOUAUBUOUMUGUCBOUDU
      EUF $.

    $( ~ dford3 expressed in primitives to demonstrate shortness.  (Contributed
       by Stefan O'Rear, 28-Oct-2014.) $)
    dford4 $p |- ( Ord N <-> A. a A. b A. c ( ( a e. N /\ b e. a ) ->
        ( b e. N /\ ( c e. b -> c e. a ) ) ) ) $=
      ( wtr cv wa wcel wel wal dftr2 ancom imbi1i bitri 2albii alcom bitr4i nfv
      wi impexp word wral dford3 19.3v df-ral imbi2i anbi2i anass bitr3i 3bitri
      19.21-2 albii anbi12i 19.26 19.26-2 pm4.76 ) AUAAEZBFZEZBAUBZGZURAHZCBIZG
      ZCFAHZSZDJZCJZVDDCIZDBIZSZSZDJCJZGZBJZVDVEVKGSZDJCJZBJBAUCVAVHBJZVMBJZGVO
      UQVRUTVSUQVCVBGZVESZBJCJZVRCBAKVRWACJBJWBVGWABCVGVFWAVFDUDVDVTVEVBVCLMNOW
      ABCPNQUTVBUSSZBJVSUSBAUEWCVMBWCVBVIVCGZVJSZSZCJDJZVLCJDJVMWCVBWECJDJZSWGU
      SWHVBDCURKUFVBWEDCVBDRVBCRUKQWFVLDCWFVDVIGZVJSZVLWFVBWDGZVJSWJVBWDVJTWKWI
      VJWKVBVCVIGZGWIWDWLVBVIVCLUGVBVCVIUHQMUIVDVIVJTNOVLDCPUJULNUMVHVMBUNQVNVQ
      BVNVFVLGZDJCJVQVFVLCDUOWMVPCDVDVEVKUPOUIULUJ $.
  $}

  $( Unrelated:  Wiener pairs treat proper classes symmetrically.  (Contributed
     by Stefan O'Rear, 19-Sep-2014.) $)
  wopprc $p |- ( ( A e. _V /\ B e. _V ) <-> -. 1o e. { { { A } , (/) } , { { B
      } } } ) $=
    ( cvv wcel wa c0 csn cpr c1o wceq wn id dfsn2 eqtr3di snex 0ex snprc impbii
    con2bii xchbinxr preqr1 syl sylibr biimpi preq1d eqtr4id eqcom bitr2i sneqr
    sneq anbi12i wo pm4.56 elpr bitri df1o2 eleq1i ) ACDZBCDZEZFGZAGZFHZBGZGZHZ
    DZIVFDUTVAVCJZKZVAVEJZKZEZVGKURVIUSVKVHURVHURKZVHVBFJZVMVHVCFFHZJVNVHVAVCVO
    VHLFMZNVBFFAOPUAUBAQZUCVMVAVOVCVPVMVBFFVMVNVQUDUEUFRSUSFVDJZVJVRUSUSKVDFJVR
    BQVDFUGUHSVJVRFVDPUIFVDUJRTUKVLVHVJULVGVHVJUMVAVCVEFOUNTUOIVAVFUPUQT $.

  ${
    $d a b c d $.
    $( Lemma for ~ rpnnen3 .  (Contributed by Stefan O'Rear, 18-Jan-2015.) $)
    rpnnen3lem $p |- ( ( ( a e. RR /\ b e. RR ) /\ a < b ) ->
        { c e. QQ | c < a } =/= { c e. QQ | c < b } ) $=
      ( vd cv cr wcel clt wbr cq crab wne w3a wa wrex qbtwnre simp2 breq1 elrab
      wn simp3r sylanbrc simp11 3ad2ant2 simp3l ltnsymd intnand sylnibr syl2anc
      qre nelne1 necomd rexlimdv3a mpd 3expa ) AEZFGZBEZFGZUPURHIZCEZUPHIZCJKZV
      AURHIZCJKZLZUQUSUTMZUPDEZHIZVHURHIZNZDJOVFDUPURPVGVKVFDJVGVHJGZVKMZVEVCVM
      VHVEGZVHVCGZTVEVCLVMVLVJVNVGVLVKQVGVLVIVJUAVDVJCVHJVAVHURHRSUBVMVLVHUPHIZ
      NVOVMVPVLVMUPVHUQUSUTVLVKUCVLVGVHFGVKVHUJUDVGVLVIVJUEUFUGVBVPCVHJVAVHUPHR
      SUHVHVEVCUKUIULUMUNUO $.

    $( Dedekind cut injection of ` RR ` into ` ~P QQ ` .  (Contributed by
       Stefan O'Rear, 18-Jan-2015.) $)
    rpnnen3 $p |- RR ~<_ ~P QQ $=
      ( va vb vc cq cpw cvv wcel cr cdom wbr qex pwex cv clt crab wa rpnnen3lem
      wss wceq wne ssrab2 elpw2 mpbir wo lttri2 ancom1s necomd jaodan ex sylbid
      a1i necon4d breq2 rabbidv impbid1 dom2 ax-mp ) DEZFGHURIJDKLABHURCMZAMZNJ
      ZCDOZUSBMZNJZCDOZFVBURGZUTHGZVFVBDRVACDUAVBDKUBUCUKVGVCHGZPZVBVESUTVCSZVI
      UTVCVBVEVIUTVCTUTVCNJZVCUTNJZUDZVBVETZUTVCUEVIVMVNVIVKVNVLABCQVIVLPVEVBVH
      VGVLVEVBTBACQUFUGUHUIUJULVJVAVDCDUTVCUSNUMUNUOUPUQ $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  More equivalents of the Axiom of Choice
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Characterization of choice similar to ~ dffin1-5 .  (Contributed by Stefan
     O'Rear, 6-Jan-2015.) $)
  axac10 $p |- ( ~~ " On ) = _V $=
    ( wac cen con0 cima cvv wceq axac3 dfac10b mpbi ) ABCDEFGHI $.

  ${
    $d x S $.  $d x V $.
    $( The Hartogs number of an infinite set is at least ` _om ` . _MOVABLE_
       (Contributed by Stefan O'Rear, 10-Jul-2015.) $)
    harinf $p |- ( ( S e. V /\ -. S e. Fin ) -> _om C_ ( har ` S ) ) $=
      ( vx wcel cfn wn wa com char cfv cv con0 cdom wbr nnon adantl csdm simplr
      nnfi ex sdomdom domfi syl2im mtod simpll fidomtri syl2anc mpbird elharval
      wb sylanbrc ssrdv ) ABDZAEDZFZGZCHAIJZUPCKZHDZURUQDZUPUSGZURLDZURAMNZUTUS
      VBUPUROPVAVCAURQNZFZVAVDUNUMUOUSRVAUREDZVDAURMNZUNUSVFUPURSPZAURUAVFVGUNU
      RAUBTUCUDVAVFUMVCVEUJVHUMUOUSUEURABUFUGUHAURUIUKTUL $.
  $}

  ${
    $d w x X $.  $d w x A $.  $d w x y B $.  $d w x y z C $.  $d w x ph $.
    wdom2d2.a $e |- ( ph -> A e. V ) $.
    wdom2d2.b $e |- ( ph -> B e. W ) $.
    wdom2d2.c $e |- ( ph -> C e. X ) $.
    wdom2d2.o $e |- ( ( ph /\ x e. A ) -> E. y e. B E. z e. C x = X ) $.
    $( Deduction for weak dominance by a Cartesian product. _MOVABLE_
       (Contributed by Stefan O'Rear, 10-Jul-2015.) $)
    wdom2d2 $p |- ( ph -> A ~<_* ( B X. C ) ) $=
      ( vw cv cfv csb wceq wrex cxp cvv c1st c2nd xpexd wcel nfcsb1v nfeq2 nfcv
      wa nfcsbw nfv cop csbopeq1a eqeq2d rexxpf sylibr wdom2d ) ABOEFGUAZHUBCOP
      ZUCQZDUTUDQZJRZRZKAFGIJLMUEABPZEUFUJVEJSZDGTCFTVEVDSZOUSTNVGVFOCDFGCVEVDC
      VAVCUGUHDVEVDDCVAVCDVAUIDVBJUGUKUHVFOULUTCPDPUMSVDJVECDUTJUNUOUPUQUR $.
  $}

  ${
    $d a c $.

    $( Tarski's theorem about choice: ~ infxpidm is equivalent to ~ ax-ac .
       (Contributed by Stefan O'Rear, 4-Nov-2014.)  (Proof shortened by Stefan
       O'Rear, 10-Jul-2015.) $)
    ttac $p |- ( CHOICE <-> A. c ( _om ~<_ c -> ( c X. c ) ~~ c ) ) $=
      ( va cvv wceq com cv cdom wbr cxp cen wi wal wcel vex syl alrimiv wn char
      wss ax-mp wac ccrd cdm dfac10 eleq2 mpbiri infxpidm2 ex cfn finnum adantl
      cfv cun con0 harcl onenon cwdom fvex unex harinf mpan ssun1 sstrdi ssdomg
      wa mpsyl breq2 xpeq12 anidms id breq12d imbi12d spcv syl5 imp harndom mp2
      wo domtr mto unxpwdom2 orel2 wb wdomnumr sylib numdom sylancr ssun2 ssnum
      sylancl pm2.61dan eqv sylibr impbii bitri ) UAUBUCZCDZEAFZGHZWRWRIZWRJHZK
      ZALZUDWQXCWQXBAWQWRWPMZXBWQXDWRCMANWPCWRUEUFXDWSXAWRUGUHOPXCBFZWPMZBLWQXC
      XFBXCXEUIMZXFXGXFXCXEUJUKXCXGQZVEZXERULZXEUMZWPMZXEXKSXFXIXJWPMZXKXJGHZXL
      XJUNMXMXEUOXJUPTZXIXKXJUQHZXNXIXKXKIZXKJHZXPXCXHXRXHEXKGHZXCXRXKCMZXHEXKS
      XSXJXEXERURBNZUSZXHEXJXKXECMXHEXJSYAXECUTVAXJXEVBZVCEXKCVDVFXBXSXRKAXKYBW
      RXKDZWSXSXAXRWRXKEGVGYDWTXQWRXKJYDWTXQDWRXKWRXKVHVIYDVJVKVLVMVNVOXKXEGHZQ
      XRXPYEVRXPYEXJXEGHZXEVPXJXKGHZYEYFXTXJXKSYGYBYCXJXKCVDVQXJXKXEVSVAVTXKXJX
      EWAYEXPWBVFOXMXPXNWCXOXKXJWDTWEXJXKWFWGXEXJWHXKXEWIWJWKPBWPWLWMWNWO $.
  $}

  ${
    $d A x y z w $.  $d X x y $.  $d Y x y $.  $d V x y $.
    pw2f1o2.f $e |- F = ( x e. ( 2o ^m A ) |-> ( `' x " { 1o } ) ) $.
    $( Define a bijection between characteristic functions and subsets.
       _EDITORIAL_: extracted from ~ pw2en , which can be easily reproved in
       terms of this.  (Contributed by Stefan O'Rear, 18-Jan-2015.)  (Revised
       by Stefan O'Rear, 9-Jul-2015.) $)
    pw2f1ocnv $p |- ( A e. V -> ( F : ( 2o ^m A ) -1-1-onto-> ~P A /\ `' F =
          ( y e. ~P A |-> ( z e. A |-> if ( z e. y , 1o , (/) ) ) ) ) ) $=
      ( vw wcel c2o cv c1o c0 cvv wa adantr wceq con0 wb bitr4di cmap ccnv cima
      co cpw csn wel cif cmpt vex cnvex imaexg mp1i mptexg wss wf elmapg anbi1d
      2on mpan wral csuc 1oex sucid df-2o eleqtrri prid1 df2o2 ifcli rgenw eqid
      cpr 0ex fmpt mpbi simpr feq1d mpbiri cfv iftrue noel iffalse eqeq1d 0lt1o
      wn eleq2 biimtrdi con4i impbii fveq1d elequ1 ifbid fvmpt sylan9eq bitr4id
      mtoi fvex elsn pm5.32da ssel pm4.71rd wfn ffn elpreima 3syl 3bitr4d eqrdv
      jca cdm cnvimass fdm sseqtrid eqsstrd simplr eleq2d wbr fnbrfvb sylan 1on
      wi eliniseg ax-mp bitr4d biimpa adantl wo ffvelcdm adantlr df2o3 eleqtrdi
      eqtr4d elpr sylib ord sylibrd con1d imp pm2.61dan ralrimiva eqfnfv mpbird
      sylancl velpw anbi1i f1ocnvd ) DFIZABJDUAUDZDUEZAKZUBZLUFZUCZCDCBUGZLMUHZ
      UIZENNGUUJNIUULNIUUFUUIUUGIZOUUIAUJUKUUJUUKNULUMUUFUUONIBKZUUHIZCDUUNFUNP
      UUFUUPUUQUULQZOZUUQDUOZUUIUUOQZOZUURUVBOUUFUUTDJUUIUPZUUSOZUVCUUFUUPUVDUU
      SJRIUUFUUPUVDSUSJDUUIRFUQUTURUVCUVEUVCUVDUUSUVCUVDDJUUOUPZUUNJIZCDVAUVFUV
      GCDUUMLMJLLVBJLVCVDVEVFMMMUFZVLJMUVHVMVGVHVFVIVJCDJUUNUUOUUOVKZVNVOZUVCDJ
      UUIUUOUVAUVBVPZVQVRZUVCHUUQUULUVCHKZDIZHBUGZOUVNUVMUUIVSZUUKIZOZUVOUVMUUL
      IZUVCUVNUVOUVQUVCUVNOZUVOUVPLQZUVQUVTUVOUVOLMUHZLQZUWAUVOUWCUVOLMVTZUVOUW
      CUVOWEZUWCMMIZMWAUWEUWCMLQZUWFUWEUWBMLUVOLMWBZWCUWGUWFMLIWDMLMWFVRWGWPWHW
      IUVTUVPUWBLUVCUVNUVPUVMUUOVSZUWBUVCUVMUUIUUOUVKWJCUVMUUNUWBDUUOCKUVMQUUMU
      VOLMCHBWKWLUVIUVOLMNVCVMVIWMZWNWCWOUVPLUVMUUIWQZWRTWSUVCUVOUVNUVAUVOUVNXT
      UVBUUQDUVMWTPXAUVCUVDUUIDXBZUVSUVRSUVLDJUUIXCZDUVMUUKUUIXDXEXFXGXHUVEUVAU
      VBUVEUUQUULDUVDUUSVPUVEUUIXIZUULDUUIUUKXJUVDUWNDQUUSDJUUIXKPXLXMUVEUVBUVP
      UWIQZHDVAZUVEUWOHDUVEUVNOZUVPUWBUWIUWQUVOUVPUWBQUWQUVOOUVPLUWBUWQUVOUWAUW
      QUVOUVSUWAUWQUUQUULUVMUVDUUSUVNXNXOUWQUWAUVMLUUIXPZUVSUVEUWLUVNUWAUWRSUVD
      UWLUUSUWMPZDUVMLUUIXQXRLRIUVSUWRSXSUUILUVMRHUJYAYBTYCZYDUVOUWCUWQUWDYEYKU
      WQUWEOUVPMUWBUWQUWEUVPMQZUWQUXAUVOUWQUXAWEUWAUVOUWQUXAUWAUWQUVPMLVLZIUXAU
      WAYFUWQUVPJUXBUVDUVNUVPJIUUSDJUVMUUIYGYHYIYJUVPMLUWKYLYMYNUWTYOYPYQUWEUWB
      MQUWQUWHYEYKYRUVNUWIUWBQUVEUWJYEYKYSUVEUWLUUODXBZUVBUWPSUWSUVFUXCUVJDJUUO
      XCYBHDUUIUUOYTUUBUUAXHWITUURUVAUVBBDUUCUUDTUUE $.

    $( Define a bijection between characteristic functions and subsets.
       _EDITORIAL_: extracted from ~ pw2en , which can be easily reproved in
       terms of this.  (Contributed by Stefan O'Rear, 18-Jan-2015.) $)
    pw2f1o2 $p |- ( A e. V -> F : ( 2o ^m A ) -1-1-onto-> ~P A ) $=
      ( vy vz wcel c2o cmap co cpw wf1o ccnv wel c1o c0 cif cmpt wceq pw2f1ocnv
      simpld ) BDHIBJKBLZCMCNFUCGBGFOPQRSSTAFGBCDEUAUB $.

    $( Function value of the ~ pw2f1o2 bijection.  (Contributed by Stefan
       O'Rear, 18-Jan-2015.)  (Revised by Stefan O'Rear, 6-May-2015.) $)
    pw2f1o2val $p |- ( X e. ( 2o ^m A ) ->
        ( F ` X ) = ( `' X " { 1o } ) ) $=
      ( c2o cmap co wcel ccnv c1o csn cima cvv cfv wceq cnvexg imaexg syl cv
      cnveq imaeq1d fvmptg mpdan ) DFBGHZIZDJZKLZMZNIZDCOUIPUFUGNIUJDUEQUGUHNRS
      ADATZJZUHMUIUENCUKDPULUGUHUKDUAUBEUCUD $.

    $( Membership in a mapped set under the ~ pw2f1o2 bijection.  (Contributed
       by Stefan O'Rear, 18-Jan-2015.)  (Revised by Stefan O'Rear,
       6-May-2015.) $)
    pw2f1o2val2 $p |- ( ( X e. ( 2o ^m A ) /\ Y e. A ) ->
        ( Y e. ( F ` X ) <-> ( X ` Y ) = 1o ) ) $=
      ( c2o cmap co wcel wa cfv ccnv c1o csn cima wceq wb pw2f1o2val eleq2d wfn
      adantr wf elmapi ffn fniniseg 3syl baibd bitrd ) DGBHIJZEBJZKEDCLZJZEDMNO
      PZJZEDLNQZUJUMUORUKUJULUNEABCDFSTUBUJUOUKUPUJBGDUCDBUAUOUKUPKRDGBUDBGDUEB
      NEDUFUGUHUI $.
  $}

  ${
    $d A x $.  $d B x $.

    $( Limit ordinals in the sense inclusive of zero contain all successors of
       their members.  (Contributed by Stefan O'Rear, 20-Jan-2015.) $)
    limsuc2 $p |- ( ( Ord A /\ A = U. A ) -> ( B e. A <-> suc B e. A ) ) $=
      ( vx word cuni wceq wa wcel csuc cv wral ordunisuc2 biimpa eleq1d rspccva
      suceq sylan ex wi wtr ordtr trsuc syl adantr impbid ) ADZAAEFZGZBAHZBIZAH
      ZUHUIUKUHCJZIZAHZCAKZUIUKUFUGUOCALMUNUKCBAULBFUMUJAULBPNOQRUFUKUISZUGUFAT
      ZUPAUAUQUKUIABUBRUCUDUE $.
  $}

  ${
    $d R x y z w a b c $.  $d A x y z w a b c $.  $d F x y z w b c $.
    $d T a b c $.  $d U a b c $.
    wepwso.t $e |- T = { <. x , y >. | E. z e. A ( ( z e. y /\ -. z e. x ) /\
        A. w e. A ( w R z -> ( w e. x <-> w e. y ) ) ) } $.

    ${
      wepwso.u $e |- U = { <. x , y >. | E. z e. A ( ( x ` z ) _E ( y ` z ) /\
          A. w e. A ( w R z -> ( x ` w ) = ( y ` w ) ) ) } $.
      wepwso.f $e |- F = ( a e. ( 2o ^m A ) |-> ( `' a " { 1o } ) ) $.
      $( Transfer an ordering on characteristic functions by isomorphism to the
         power set.  (Contributed by Stefan O'Rear, 18-Jan-2015.) $)
      wepwsolem $p |- ( A e. _V -> F Isom U , T ( ( 2o ^m A ) , ~P A ) ) $=
        ( wcel c2o wb wa wceq c1o c0 vb vc cvv cmap co cpw wf1o cv wbr cfv wral
        wiso pw2f1o2 cep wi wrex fvex epeli elmapi ad2antrl ffvelcdmda ad2antll
        wn wf wo n0i adantl cpr elpri df2o3 eleq2s ad2antlr orel1 onirri eleq12
        sylc 1on biimpd expcom com3r imp adantll mpdan jca adantr orel2 adantrl
        mtoi mpan9 eqeltrdi simprl eleqtrrd impbida syl2anc simplrr pw2f1o2val2
        0lt1o sylancom simplrl notbid anbi12d bitr4d bitrid eqeq1 simplr nesymi
        1n0 mtbiri simpr mtbid ad3antlr eqtr4d ex mpbid mpjaodan impbid2 imbi2d
        bibi12d ralbidva rexbidva vex fveq1 breqan12d eqeqan12d ralbidv rexbidv
        braba wel eleq2 bi2anan9r bi2bian9 3bitr4g ralrimivva df-isom sylanbrc
        ) EUCNZOEUDUEZEUFZIUGUAUHZUBUHZHUIZYSIUJZYTIUJZGUIZPZUBYQUKUAYQUKYQYRHG
        IULJEIUCMUMYPUUEUAUBYQYQYPYSYQNZYTYQNZQQZCUHZYSUJZUUIYTUJZUNUIZDUHZUUIF
        UIZUUMYSUJZUUMYTUJZRZUOZDEUKZQZCEUPZUUIUUCNZUUIUUBNZVCZQZUUNUUMUUBNZUUM
        UUCNZPZUOZDEUKZQZCEUPZUUAUUDUUHUUTUVKCEUUHUUIENZQZUULUVEUUSUVJUULUUJUUK
        NZUVNUVEUUJUUKUUIYTUQURUVNUVOUUKSRZUUJSRZVCZQZUVEUVNUUJONZUUKONZUVOUVSP
        UUHEOUUIYSUUFEOYSVDYPUUGYSOEUSUTZVAUUHEOUUIYTUUGEOYTVDYPUUFYTOEUSVBZVAU
        VTUWAQZUVOUVSUWDUVOQZUVPUVRUWEUUKTRZVCZUWFUVPVEZUVPUVOUWGUWDUUKUUJVFVGU
        WAUWHUVTUVOUWHUUKTSVHZOUUKTSVIVJVKVLUWFUVPVMVPZUWEUVPUVRUWJUWEUVPQUVQSS
        NZSVQVNUVOUVPUVQUWKUOZUWDUVOUVPUWLUVPUVQUVOUWKUVQUVPUVOUWKUOUVQUVPQUVOU
        WKUUJSUUKSVOVRVSVTWAWBWHWCWDUWDUVSQZUUJSUUKUWMUUJTSUWDUVRUUJTRZUVPUWDUW
        NUVQVEZUVRUWNUVTUWOUWAUWOUUJUWIOUUJTSVIVJVKWEUVQUWNWFWIWGWQWJUWDUVPUVRW
        KWLWMWNUVNUVBUVPUVDUVRUUHUVMUUGUVBUVPPYPUUFUUGUVMWOJEIYTUUIMWPWRUVNUVCU
        VQUUHUVMUUFUVCUVQPYPUUFUUGUVMWSJEIYSUUIMWPWRWTXAXBXCUUHUUSUVJPUVMUUHUUR
        UVIDEUUHUUMENZQZUUQUVHUUNUWQUUQUUOSRZUUPSRZPZUVHUWQUUOONZUUPONZUUQUWTPU
        UHEOUUMYSUWBVAUUHEOUUMYTUWCVAUXAUXBQZUUQUWTUUOUUPSXDUXCUUOTRZUWTUUQUOUW
        RUXCUXDQZUWTUUQUXEUWTQZUUOTUUPUXCUXDUWTXEUXFUWSVCUUPTRZUWSVEZUXGUXFUWRU
        WSUXDUWRVCUXCUWTUXDUWRTSRSTXGXFUUOTSXDXHVLUXEUWTXIXJUXBUXHUXAUXDUWTUXHU
        UPUWIOUUPTSVIVJVKXKUWSUXGWFVPXLXMUXCUWRQZUWTUUQUXIUWTQZUUOSUUPUXCUWRUWT
        XEZUXJUWRUWSUXKUXIUWTXIXNXLXMUXAUXDUWRVEZUXBUXLUUOUWIOUUOTSVIVJVKWEXOXP
        WNUWQUVFUWRUVGUWSUUHUWPUUFUVFUWRPYPUUFUUGUWPWSJEIYSUUMMWPWRUUHUWPUUGUVG
        UWSPYPUUFUUGUWPWOJEIYTUUMMWPWRXRXBXQXSWEXAXTUUIAUHZUJZUUIBUHZUJZUNUIZUU
        NUUMUXMUJZUUMUXOUJZRZUOZDEUKZQZCEUPUVAABYSYTHUAYAUBYAUXMYSRZUXOYTRZQZUY
        CUUTCEUYFUXQUULUYBUUSUYDUYEUXNUUJUXPUUKUNUUIUXMYSYBUUIUXOYTYBYCUYFUYAUU
        RDEUYFUXTUUQUUNUYDUYEUXRUUOUXSUUPUUMUXMYSYBUUMUXOYTYBYDXQYEXAYFLYGCBYHZ
        CAYHZVCZQZUUNDAYHZDBYHZPZUOZDEUKZQZCEUPUVLABUUBUUCGYSIUQYTIUQUXMUUBRZUX
        OUUCRZQZUYPUVKCEUYSUYJUVEUYOUVJUYRUYGUVBUYQUYIUVDUXOUUCUUIYIUYQUYHUVCUX
        MUUBUUIYIWTYJUYSUYNUVIDEUYSUYMUVHUUNUYQUYKUVFUYRUYLUVGUXMUUBUUMYIUXOUUC
        UUMYIYKXQYEXAYFKYGYLYMUAUBYQYRHGIYNYO $.
    $}

    $( A well-ordering induces a strict ordering on the power set. _EDITORIAL_:
       when well-orderings are set like, this can be strengthened to remove
       ` A e. V ` .  (Contributed by Stefan O'Rear, 18-Jan-2015.) $)
    wepwso $p |- ( ( A e. V /\ R We A ) -> T Or ~P A ) $=
      ( va wcel wwe wa c2o cv cfv cep wbr wor eqid cmap co wceq wral wrex copab
      wi cpw word com 2onn nnord ax-mp ordwe weso mp2b wemapso mpan2 adantl cvv
      wb ccnv c1o csn cima cmpt wiso elex wepwsolem isoso 3syl adantr mpbid ) E
      HKZEFLZMNEUAUBZCOZAOZPVQBOZPQRDOZVQFRVTVRPVTVSPUCUGDEUDMCEUEABUFZSZEUHZGS
      ZVOWBVNVONQSZWBNUIZNQLWENUJKWFUKNULUMNUNNQUOUPABCDENFQWAWATZUQURUSVNWBWDV
      AZVOVNEUTKVPWCWAGJVPJOVBVCVDVEVFZVGWHEHVHABCDEFGWAWIJIWGWITVIVPWCWAGWIVJV
      KVLVM $.
  $}

  ${
    $d F v w x y $.  $d G v w x y z $.  $d A v w x y z $.  $d ph v x w $.
    dnnumch.f $e |- F = recs ( ( z e. _V |-> ( G ` ( A \ ran z ) ) ) ) $.
    dnnumch.a $e |- ( ph -> A e. V ) $.
    dnnumch.g $e |- ( ph -> A. y e. ~P A ( y =/= (/) -> ( G ` y ) e. y ) ) $.
    $( Define an enumeration of a set from a choice function; second part, it
       restricts to a bijection. _EDITORIAL_: overlaps ~ dfac8a .  (Contributed
       by Stefan O'Rear, 18-Jan-2015.) $)
    dnnumch1 $p |- ( ph -> E. x e. On ( F |` x ) : x -1-1-onto-> A ) $=
      ( vw wcel cv cdif c0 cfv con0 wceq cvv cima wne wi wral cres wf1o wrex wa
      crn cmpt crecs recsval wfun wfn tfr1 fnfun ax-mp vex resfunexg mp2an rneq
      fveq1i df-ima eqtr4di difeq2d fveq2d weq cbvmptv fvex fvmpt fveq2i eqtr3i
      reseq1i 3eqtr4g ad2antlr cpw wss difss wb elpw2g syl mpbiri neeq1 eleq12d
      fveq2 id imbi12d rspcva syl2anc adantr imp eqeltrd ex ralrimiva tz7.49c )
      AEHMZEFBNZUAZOZPUBZWQFQZWSMZUCZBRUDWQEFWQUEZUFBRUGJAXCBRAWQRMZUHZWTXBXFWT
      UHXAWSGQZWSXEXAXGSAWTXEWQDTEDNZUIZOZGQZUJZUKZQXMWQUEZXLQZXAXGWQXLULWQFXMI
      VBXDXLQZXGXOXDTMZXPXGSFUMZWQTMXQFRUNXRFXLIUOZRFUPUQBURFWQTUSUTLXDELNZUIZO
      ZGQZXGTXLXTXDSZYBWSGYDYAWREYDYAXDUIWRXTXDVAFWQVCVDVEVFDLTXKYCDLVGZXJYBGYE
      XIYAEXHXTVAVEVFVHWSGVIVJUQXDXNXLFXMWQIVMVKVLVNVOXFWTXGWSMZAWTYFUCZXEAWSEV
      PZMZCNZPUBZYJGQZYJMZUCZCYHUDYGAYIWSEVQZEWRVRAWPYIYOVSJWSEHVTWAWBKYNYGCWSY
      HYJWSSZYKWTYMYFYJWSPWCYPYLXGYJWSYJWSGWEYPWFWDWGWHWIWJWKWLWMWNBEHFXSWOWI
      $.

    $( Define an enumeration (weak dominance version) of a set from a choice
       function.  (Contributed by Stefan O'Rear, 18-Jan-2015.) $)
    dnnumch2 $p |- ( ph -> A C_ ran F ) $=
      ( vx cv cres wf1o con0 wrex crn wss dnnumch1 wi wfo wceq f1ofo forn resss
      syl rnss mp1i eqsstrrd a1i rexlimdvw mpd ) AKLZDEUMMZNZKOPDEQZRZAKBCDEFGH
      IJSAUOUQKOUOUQTAUODUNQZUPUOUMDUNUAURDUBUMDUNUCUMDUNUDUFUNERURUPRUOEUMUEUN
      EUGUHUIUJUKUL $.

    $( Value of the ordinal injection function.  (Contributed by Stefan O'Rear,
       18-Jan-2015.) $)
    dnnumch3lem $p |- ( ( ph /\ w e. A ) ->
        ( ( x e. A |-> |^| ( `' F " { x } ) ) ` w ) = |^| ( `' F " { w } ) ) $=
      ( cv wcel csn cima cint cmpt con0 crn wa ccnv eqid weq sneq imaeq2d simpr
      inteqd wss c0 wne cdm cnvimass cvv cdif cfv fndmi sseqtri dnnumch2 sselda
      tfr1 inisegn0 sylib oninton sylancr fvmptd3 ) AEMZFNZUAZBVGGUBZBMZOZPZQZV
      JVGOZPZQZFBFVNRZSVRUCBEUDZVMVPVSVLVOVJVKVGUEUFUHAVHUGVIVPSUIVPUJUKZVQSNVP
      GULSGVOUMSGGDUNFDMTUOHUPRJVAUQURVIVGGTZNVTAFWAVGACDFGHIJKLUSUTVGGVBVCVPVD
      VEVF $.

    $( Define an injection from a set into the ordinals using a choice
       function.  (Contributed by Stefan O'Rear, 18-Jan-2015.) $)
    dnnumch3 $p |- ( ph -> ( x e. A |-> |^| ( `' F " { x } ) )
            : A -1-1-> On ) $=
      ( vv vw con0 cv csn cfv wceq wcel wa ccnv cima cint cmpt wf wi wf1 wss c0
      wral wne cdm cnvimass cvv crn cdif fndmi sseqtri dnnumch2 sselda inisegn0
      tfr1 sylib oninton sylancr fmpttd dnnumch3lem adantrr adantrl fveq2 onint
      eqeq12d adantl wfn wb fniniseg ax-mp simprbi syl adantr 3eqtr3d ex sylbid
      ralrimivva dff13 sylanbrc ) AENBEFUAZBOZPZUBZUCZUDZUELOZWLQZMOZWLQZRZWMWO
      RZUFZMEUJLEUJENWLUGABEWKNAWHESTZWJNUHWJUIUKZWKNSWJFULZNFWIUMNFFDUNEDOUOUP
      GQUDIVBZUQZURWTWHFUOZSXAAEXEWHACDEFGHIJKUSZUTWHFVAVCWJVDVEVFAWSLMEEAWMESZ
      WOESZTTZWQWGWMPZUBZUCZWGWOPZUBZUCZRZWRXIWNXLWPXOAXGWNXLRXHABCDLEFGHIJKVGV
      HAXHWPXORXGABCDMEFGHIJKVGVIVLXIXPWRXIXPTXLFQZXOFQZWMWOXPXQXRRXIXLXOFVJVMX
      IXQWMRZXPAXGXSXHAXGTZXLXKSZXSXTXKNUHXKUIUKZYAXKXBNFXJUMXDURXTWMXESYBAEXEW
      MXFUTWMFVAVCXKVKVEYAXLNSZXSFNVNZYAYCXSTVOXCNWMXLFVPVQVRVSVHVTXIXRWORZXPAX
      HYEXGAXHTZXOXNSZYEYFXNNUHXNUIUKZYGXNXBNFXMUMXDURYFWOXESYHAEXEWOXFUTWOFVAV
      CXNVKVEYGXONSZYEYDYGYIYETVOXCNWOXOFVPVQVRVSVIVTWAWBWCWDLMENWLWEWF $.

    dnwech.h $e |- H = { <. v , w >. | |^| ( `' F " { v } ) e.
        |^| ( `' F " { w } ) } $.
    $( Define a well-ordering from a choice function.  (Contributed by Stefan
       O'Rear, 18-Jan-2015.) $)
    dnwech $p |- ( ph -> H We A ) $=
      ( vx wwe copab cin wcel wa cv ccnv csn cima cint cfv cep wbr wf1 dnnumch3
      cmpt con0 epweon eqid f1we mpisyl cxp wceq fvex epeli dnnumch3lem adantrr
      wb adantrl eleq12d bitr2id pm5.32da opabbidv ineq12i inopab 3eqtri ineq1i
      incom df-xp 3eqtr4g weeq1 syl weinxp 3bitr4g mpbird ) AFIPZFEUAZOFGUBZOUA
      UCUDUEUKZUFZDUAZWDUFZUGUHZEDQZPZAFULWDUIULUGPWJAOBCFGHJKLMUJUMEDFULWIUGWD
      WIUNUOUPAFIFFUQZRZPZFWIWKRZPZWAWJAWLWNURWMWOVCAWBFSZWFFSZTZWCWBUCUDUEZWCW
      FUCUDUEZSZTZEDQZWRWHTZEDQZWLWNAXBXDEDAWRXAWHWHWEWGSAWRTZXAWEWGWFWDUSUTXFW
      EWSWGWTAWPWEWSURWQAOBCEFGHJKLMVAVBAWQWGWTURWPAOBCDFGHJKLMVAVDVEVFVGVHWLWK
      IRWREDQZXAEDQZRXCIWKVMWKXGIXHEDFFVNZNVIWRXAEDVJVKWNWKWIRXGWIRXEWIWKVMWKXG
      WIXIVLWRWHEDVJVKVOFWLWNVPVQFIVRFWIVRVSVT $.
  $}

  ${
    $d U y z a b c d e f $.  $d S x y a b c d e f g $.  $d R x y a b c d e f $.
    $d ph x y z c d e f g $.  $d A x y z a b c d e f g $.
    $d F x y z a b c d e f g $.  $d T a b c d e f $.  $d B a b c d e f $.
    fnwe2.su $e |- ( z = ( F ` x ) -> S = U ) $.
    fnwe2.t $e |- T = { <. x , y >. | ( ( F ` x ) R ( F ` y ) \/
        ( ( F ` x ) = ( F ` y ) /\ x U y ) ) } $.
    $( Lemma for ~ fnwe2 .  Substitute variables.  (Contributed by Stefan
       O'Rear, 19-Jan-2015.) $)
    fnwe2val $p |- ( a T b <-> ( ( F ` a ) R ( F ` b ) \/
        ( ( F ` a ) = ( F ` b ) /\ a [_ ( F ` a ) / z ]_ S b ) ) ) $=
      ( cv cfv wbr wceq wa wo csb vex fveq2 breqan12d eqeqan12d csbeq1d eqtr3id
      simpl fvex csbie adantr simpr breq123d anbi12d orbi12d braba ) AMZHNZBMZH
      NZDOZUPURPZUOUQGOZQZRIMZHNZJMZHNZDOZVDVFPZVCVECVDESZOZQZRABVCVEFITJTUOVCP
      ZUQVEPZQZUSVGVBVKVLVMUPVDURVFDUOVCHUAZUQVEHUAZUBVNUTVHVAVJVLVMUPVDURVFVOV
      PUCVNUOVCUQVEGVIVLVMUFVLGVIPVMVLGCUPESVICUPEGUOHUGKUHVLCUPVDEVOUDUEUIVLVM
      UJUKULUMLUN $.

    fnwe2.s $e |- ( ( ph /\ x e. A ) ->
        U We { y e. A | ( F ` y ) = ( F ` x ) } ) $.
    $( Lemma for ~ fnwe2 .  Substitution in well-ordering hypothesis.
       (Contributed by Stefan O'Rear, 19-Jan-2015.) $)
    fnwe2lem1 $p |- ( ( ph /\ a e. A ) ->
        [_ ( F ` a ) / z ]_ S We { y e. A | ( F ` y ) = ( F ` a ) } ) $=
      ( cv cfv wceq crab csb wwe wral ralrimiva fveq2 csbeq1d fvex csbie eqtrdi
      eqeq2d rabbidv weeq12d cbvralvw sylibr r19.21bi ) ACOJPZKOZJPZQZCERZDUPGS
      ZTZKEAUNBOZJPZQZCERZITZBEUAUTKEUAAVEBENUBUTVEKBEUOVAQZURVDUSIVFUSDVBGSIVF
      DUPVBGUOVAJUCZUDDVBGIVAJUELUFUGVFUQVCCEVFUPVBUNVGUHUIUJUKULUM $.

    fnwe2.f $e |- ( ph -> ( F |` A ) : A --> B ) $.
    fnwe2.r $e |- ( ph -> R We B ) $.

    ${
      $d ph b $.
      fnwe2lem2.a $e |- ( ph -> a C_ A ) $.
      fnwe2lem2.n0 $e |- ( ph -> a =/= (/) ) $.
      $( Lemma for ~ fnwe2 .  An element which is in a minimal fiber and
         minimal within its fiber is minimal globally; thus ` T ` is
         well-founded.  (Contributed by Stefan O'Rear, 19-Jan-2015.) $)
      fnwe2lem2 $p |- ( ph -> E. b e. a A. c e. a -. c T b ) $=
        ( ve vd vf vg cv wbr wn cres cima wral wrex cvv wcel wfr wss c0 wf wfun
        wne ffun vex funimaex 3syl wwe wefr syl crn imassrn frnd sstrid cdm cin
        incom wceq sseqtrrd dfss2 sylib eqtrid eqnetrd imadisj necon3bii sylibr
        fdmd fri syl22anc cfv df-ima rexeqi wfn wb fnssres syl2anc breq2 notbid
        ralbidv rexrn bitrid wel wa raleqi breq1 ralrn adantr resabs1d ad2antrr
        ffnd fveq1d fvres adantl eqtrd ad2antlr breq12d ralbidva bitrd rexbidva
        csb crab inex1 a1i sselda fnwe2lem1 syldan adantrr inss2 simprl fveqeq2
        eqidd elrabd elind wi elin elrab anbi2i bitri weq rspcdva biimtrid mpd
        ex ne0d imbi1i impexp ralbii2 simplrl fveq2 breq1d simplrr simpr breq2d
        wo simprrr mtbird ad3antrrr simprr eleq1w anbi12d imbi12d simplr mp2and
        eqtr2d csbeq1d breqd mtbid expr imnan ioran sylanbrc fnwe2val ralrimiva
        sylnibr rspcev rexlimdv rexlimdvaa sylbid ) AUBUFZUCUFZGUGZUHZUBKEUIZLU
        FZUJZUKZUCUWBULZNUFZMUFZIUGZUHZNUWAUKZMUWAULZAUWBUMUNZFGUOZUWBFUPUWBUQU
        TZUWDAEFUVTURUVTUSUWKREFUVTVAUVTUWALVBZVCVDAFGVEUWLSFGVFVGAUWBUVTVHFUVT
        UWAVIAEFUVTRVJVKAUVTVLZUWAVMZUQUTUWMAUWPUWAUQAUWPUWAUWOVMZUWAUWOUWAVNAU
        WAUWOUPUWQUWAVOAUWAEUWOTAEFUVTRWDVPUWAUWOVQVRVSUAVTUWBUQUWPUQUVTUWAWAWB
        WCUCUBFUWBUMGWEWFAUWDUVQKWGZUDUFZKWGZGUGZUHZUCUWAUKZUDUWAULZUWJAUWDUVPU
        WSUVTUWAUIZWGZGUGZUHZUBUWBUKZUDUWAULZUXDUWDUWCUCUXEVHZULZAUXJUWCUCUWBUX
        KUVTUWAWHZWIAUXEUWAWJZUXLUXJWKAUVTEWJUWAEUPZUXNAEFUVTRXGTEUWAUVTWLWMZUW
        CUXIUCUDUWAUXEUVQUXFVOZUVSUXHUBUWBUXQUVRUXGUVQUXFUVPGWNWOWPWQVGWRAUXIUX
        CUDUWAAUDLWSZWTZUXIUVQUXEWGZUXFGUGZUHZUCUWAUKZUXCAUXIUYCWKUXRUXIUXHUBUX
        KUKZAUYCUXHUBUWBUXKUXMXAAUXNUYDUYCWKUXPUXHUYBUBUCUWAUXEUVPUXTVOUXGUYAUV
        PUXTUXFGXBWOXCVGWRXDUXSUYBUXBUCUWAUXSUCLWSZWTZUYAUXAUYFUXTUWRUXFUWTGUYF
        UXTUVQKUWAUIZWGZUWRUYFUVQUXEUYGAUXEUYGVOUXRUYEAKUWAETXEXFZXHUYEUYHUWRVO
        UXSUVQUWAKXIXJXKUYFUXFUWSUYGWGZUWTUYFUWSUXEUYGUYIXHUXRUYJUWTVOAUYEUWSUW
        AKXIXLXKXMWOXNXOXPXOAUXCUWJUDUWAAUXRUXCWTZWTZUEUFZUVPDUWTHXQZUGZUHZUEUW
        ACUFZKWGUWTVOZCEXRZVMZUKZUBUYTULZUWJUYLUYTUMUNZUYSUYNUOZUYTUYSUPZUYTUQU
        TVUBVUCUYLUWAUYSUWNXSXTAUXRVUDUXCAUXRUWSEUNZVUDAUWAEUWSTYAZAVUFWTUYSUYN
        VEVUDABCDEGHIJKUDOPQYBUYSUYNVFVGYCYDVUEUYLUWAUYSYEXTUYLUYTUWSUYLUWAUYSU
        WSAUXRUXCYFUYLUYRUWTUWTVOCUWSEUYQUWSUWTKYGAUXRVUFUXCVUGYDUYLUWTYHYIYJUU
        AUBUEUYSUYTUMUYNWEWFUYLVUAUWJUBUYTUVPUYTUNZUBLWSZUVPEUNZUVPKWGZUWTVOZWT
        ZWTZUYLVUAUWJYKZVUHVUIUVPUYSUNZWTVUNUVPUWAUYSYLVUPVUMVUIUYRVULCUVPEUYQU
        VPUWTKYGYMYNYOUYLVUNVUOVUAUYMEUNZUYMKWGUWTVOZWTZUYPYKZUEUWAUKZUYLVUNWTZ
        UWJUYPVUTUEUYTUWAUYMUYTUNZUYPYKUELWSZVUSWTZUYPYKVVDVUTYKVVCVVEUYPVVCVVD
        UYMUYSUNZWTVVEUYMUWAUYSYLVVFVUSVVDUYRVURCUYMEUYQUYMUWTKYGYMYNYOUUBVVDVU
        SUYPUUCYOUUDVVBVVAUWJVVBVVAWTZVUIUWEUVPIUGZUHZNUWAUKZUWJUYLVUIVUMVVAUUE
        VVGVVINUWAVVGNLWSZWTZUWEKWGZVUKGUGZVVMVUKVOZUWEUVPDVVMHXQZUGZWTZUUKZVVH
        VVLVVNUHVVRUHZVVSUHVVLVVNVVMUWTGUGZVVLUXBVWAUHUCUWAUWEUCNYPZUXAVWAVWBUW
        RVVMUWTGUVQUWEKUUFUUGWOVVBUXCVVAVVKAUXRUXCVUNUUHXFVVGVVKUUIYQVVLVUKUWTV
        VMGVVBVULVVAVVKUYLVUIVUJVULUULZXFUUJUUMVVLVVOVVQUHZYKVVTVVGVVKVVOVWDVVG
        VVKVVOWTZWTZUWEUVPUYNUGZVVQVWFUWEEUNZVVMUWTVOZVWGUHZVVGVVKVWHVVOVVGUWAE
        UWEAUXOUYKVUNVVATUUNYAYDVWFVVMVUKUWTVVGVVKVVOUUOZVVBVULVVAVWEVWCXFZXKVW
        FVUTVWHVWIWTZVWJYKUEUWAUWEUENYPZVUSVWMUYPVWJVWNVUQVWHVURVWIUENEUUPUYMUW
        EUWTKYGUUQVWNUYOVWGUYMUWEUVPUYNXBWOUURVVBVVAVWEUUSVVGVVKVVOYFYQUUTVWFUY
        NVVPUWEUVPVWFDUWTVVMHVWFVVMVUKUWTVWKVWLUVAUVBUVCUVDUVEVVOVVQUVFVRVVNVVR
        UVGUVHBCDGHIJKNUBOPUVIUVKUVJUWIVVJMUVPUWAMUBYPZUWHVVINUWAVWOUWGVVHUWFUV
        PUWEIWNWOWPUVLWMYTYRYTYRUVMYSUVNUVOYS $.
    $}

    ${
      fnwe2lem3.a $e |- ( ph -> a e. A ) $.
      fnwe2lem3.b $e |- ( ph -> b e. A ) $.
      $( Lemma for ~ fnwe2 .  Trichotomy.  (Contributed by Stefan O'Rear,
         19-Jan-2015.) $)
      fnwe2lem3 $p |- ( ph -> ( a T b \/ a = b \/ b T a ) ) $=
        ( cv cfv wbr weq w3o wceq wa csb animorrl fnwe2val sylibr 3mix1d simplr
        simpr jca olcd 3mix2 adantl eqcomd csbeq1 breqd biimpa 3mix3d crab wcel
        wo wor wwe fnwe2lem1 mpdan weso syl adantr fveqeq2 eqidd solin syl12anc
        elrabd mpjao3dan cres fvresd ffvelcdmd eqeltrrd ) ALUAZKUBZMUAZKUBZGUCZ
        WDWFIUCZLMUDZWFWDIUCZUEZWEWGUFZWGWEGUCZAWHUGZWIWJWKWOWHWMWDWFDWEHUHZUCZ
        UGZVFZWIAWHWRUIBCDGHIJKLMNOUJZUKULAWMUGZWQWLWJWFWDWPUCZXAWQUGZWIWJWKXCW
        SWIXCWRWHXCWMWQAWMWQUMXAWQUNUOUPWTUKULWJWLXAWJWIWKUQURXAXBUGZWKWIWJXDWN
        WGWEUFZWFWDDWGHUHZUCZUGZVFZWKXDXHWNXDXEXGXDWEWGAWMXBUMUSXAXBXGXAWPXFWFW
        DWMWPXFUFADWEWGHUTURVAVBUOUPBCDGHIJKMLNOUJZUKVCXACUAZKUBWEUFZCEVDZWPVGZ
        WDXMVEWFXMVEWQWJXBUEAXNWMAXMWPVHZXNAWDEVEZXOSABCDEGHIJKLNOPVIVJXMWPVKVL
        VMXAXLWEWEUFCWDEXKWDWEKVNAXPWMSVMXAWEVOVRXAXLXECWFEXKWFWEKVNAWFEVEWMTVM
        XAWEWGAWMUNUSVRXMWDWFWPVPVQVSAWNUGZWKWIWJXQXIWKAWNXHUIXJUKVCAFGVGZWEFVE
        WGFVEWHWMWNUEAFGVHXRRFGVKVLAWDKEVTZUBWEFAWDEKSWAAEFWDXSQSWBWCAWFXSUBWGF
        AWFEKTWAAEFWFXSQTWBWCFWEWGGVPVQVS $.
    $}

    $d ph a b $.
    $( A well-ordering can be constructed on a partitioned set by patching
       together well-orderings on each partition using a well-ordering on the
       partitions themselves.  Similar to ~ fnwe but does not require the
       within-partition ordering to be globally well.  (Contributed by Stefan
       O'Rear, 19-Jan-2015.) $)
    fnwe2 $p |- ( ph -> T We A ) $=
      ( va vb vd cv vc wfr wbr weq w3o wral wwe wss c0 wne wa wrex wal wcel cfv
      wn wi wceq crab adantlr cres wf adantr simprl simprr fnwe2lem2 ex alrimiv
      df-fr sylibr fnwe2lem3 ralrimivva dfwe2 sylanbrc ) AEIUBZQTZRTZIUCQRUDVQV
      PIUCUEZREUFQEUFEIUGAVPEUHZVPUIUJZUKZSTUATIUCUPSVPUFUAVPULZUQZQUMVOAWCQAWA
      WBAWAUKBCDEFGHIJKQUASLMABTZEUNZCTKUOWDKUOURCEUSJUGZWANUTAEFKEVAVBZWAOVCAF
      GUGZWAPVCAVSVTVDAVSVTVEVFVGVHQUASEIVIVJAVRQREEAVPEUNZVQEUNZUKZUKBCDEFGHIJ
      KQRLMAWEWFWKNUTAWGWKOVCAWHWKPVCAWIWJVDAWIWJVEVKVLQREIVMVN $.
  $}

  ${
    $d z a b c d $.
    aomclem1.b $e |- B = { <. a , b >. | E. c e. ( R1 ` U. dom z )
        ( ( c e. b /\ -. c e. a ) /\ A. d e. ( R1 ` U. dom z )
          ( d ( z ` U. dom z ) c -> ( d e. a <-> d e. b ) ) ) } $.
    aomclem1.on $e |- ( ph -> dom z e. On ) $.
    aomclem1.su $e |- ( ph -> dom z = suc U. dom z ) $.
    aomclem1.we $e |- ( ph -> A. a e. dom z ( z ` a ) We ( R1 ` a ) ) $.
    $( Lemma for ~ dfac11 .  This is the beginning of the proof that multiple
       choice is equivalent to choice.  Our goal is to construct, by
       transfinite recursion, a well-ordering of ` ( R1 `` A ) ` .  In what
       follows, ` A ` is the index of the rank we wish to well-order, ` z ` is
       the collection of well-orderings constructed so far, ` dom z ` is the
       set of ordinal indices of constructed ranks i.e. the next rank to
       construct, and ` y ` is a postulated multiple-choice function.

       Successor case 1, define a simple ordering from the well-ordered
       predecessor.  (Contributed by Stefan O'Rear, 18-Jan-2015.) $)
    aomclem1 $p |- ( ph -> B Or ( R1 ` dom z ) ) $=
      ( cv cr1 cfv wor cvv wcel wwe wceq fveq2 cdm cuni cpw fvex wral csuc dmex
      vex uniex sucid eleqtrrid weeq12d rspcva syl2anc wepwso sylancr wb fveq2d
      con0 onuni r1suc 3syl eqtrd soeq2 syl mpbird ) ABLZUAZMNZCOZVHUBZMNZUCZCO
      ZAVLPQVLVKVGNZRZVNVKMUDAVKVHQDLZMNZVQVGNZRZDVHUEVPAVKVKUFZVHVKVHVGBUHUGUI
      UJJUKKVTVPDVKVHVQVKSVRVLVSVOVQVKVGTVQVKMTULUMUNDEFGVLVOCPHUOUPAVIVMSVJVNU
      QAVIWAMNZVMAVHWAMJURAVHUSQVKUSQWBVMSIVHUTVKVAVBVCVIVMCVDVEVF $.
  $}

  ${
    $d z y a b c d $.  $d ph a $.
    aomclem2.b $e |- B = { <. a , b >. | E. c e. ( R1 ` U. dom z )
        ( ( c e. b /\ -. c e. a ) /\ A. d e. ( R1 ` U. dom z )
          ( d ( z ` U. dom z ) c -> ( d e. a <-> d e. b ) ) ) } $.
    aomclem2.c $e |- C = ( a e. _V |->
        sup ( ( y ` a ) , ( R1 ` dom z ) , B ) ) $.
    aomclem2.on $e |- ( ph -> dom z e. On ) $.
    aomclem2.su $e |- ( ph -> dom z = suc U. dom z ) $.
    aomclem2.we $e |- ( ph -> A. a e. dom z ( z ` a ) We ( R1 ` a ) ) $.
    aomclem2.a $e |- ( ph -> A e. On ) $.
    aomclem2.za $e |- ( ph -> dom z C_ A ) $.
    aomclem2.y $e |- ( ph -> A. a e. ~P ( R1 ` A ) ( a =/= (/) ->
        ( y ` a ) e. ( ( ~P a i^i Fin ) \ { (/) } ) ) ) $.
    $( Lemma for ~ dfac11 .  Successor case 2, a choice function for subsets of
       ` ( R1 `` dom z ) ` .  (Contributed by Stefan O'Rear, 18-Jan-2015.) $)
    aomclem2 $p |- ( ph -> A. a e. ~P ( R1 ` dom z ) ( a =/= (/) ->
          ( C ` a ) e. a ) ) $=
      ( wcel cfn cv c0 wne cfv wi cdm cr1 cpw w3a csup cvv wceq vex cin wss csn
      cdif wral con0 jca r1ord3 sylc sspwd sseld rsp sylsyld 3imp eldifad inss1
      wa sseli elpwid syl aomclem1 3ad2ant1 inss2 eldifsni elpwi 3ad2ant2 sstrd
      wor sselid fisupcl syl13anc sseldd fvmpt2 sylancr eqeltrd 3exp ralrimiv )
      AGUAZUBUCZWKFUDZWKSZUEGCUAUFZUGUDZUHZAWKWQSZWLWNAWRWLUIZWMWKBUAUDZWPEUJZW
      KWSWKUKSXAWKSWMXAULGUMWSWTWKXAWSWTWKUHZTUNZSZWTWKUOWSWTXCUBUPZAWRWLWTXCXE
      UQSZAWLXFUEZGDUGUDZUHZURWRWKXISXGRAWQXIWKAWPXHAWOUSSZDUSSZVJWODUOWPXHUOAX
      JXKMPUTQWODVAVBVCVDXGGXIVEVFVGZVHZXDWTWKXCXBWTXBTVIVKVLVMZWSWPEWAZWTTSWTU
      BUCZWTWPUOXAWTSAWRXOWLACEGHIJKMNOVNVOWSXCTWTXBTVPXMWBWSXFXPXLWTXCUBVQVMWS
      WTWKWPXNWRAWKWPUOWLWKWPVRVSVTWPWTEWCWDWEZGUKXAWKFLWFWGXQWHWIWJ $.
  $}

  ${
    $d z y a b c d $.  $d ph a b $.  $d C a b c d $.  $d D a b c d $.
    aomclem3.b $e |- B = { <. a , b >. | E. c e. ( R1 ` U. dom z )
        ( ( c e. b /\ -. c e. a ) /\ A. d e. ( R1 ` U. dom z )
          ( d ( z ` U. dom z ) c -> ( d e. a <-> d e. b ) ) ) } $.
    aomclem3.c $e |- C = ( a e. _V |->
        sup ( ( y ` a ) , ( R1 ` dom z ) , B ) ) $.
    aomclem3.d $e |- D = recs ( ( a e. _V |->
        ( C ` ( ( R1 ` dom z ) \ ran a ) ) ) ) $.
    aomclem3.e $e |- E = { <. a , b >. | |^| ( `' D " { a } ) e.
        |^| ( `' D " { b } ) } $.
    aomclem3.on $e |- ( ph -> dom z e. On ) $.
    aomclem3.su $e |- ( ph -> dom z = suc U. dom z ) $.
    aomclem3.we $e |- ( ph -> A. a e. dom z ( z ` a ) We ( R1 ` a ) ) $.
    aomclem3.a $e |- ( ph -> A e. On ) $.
    aomclem3.za $e |- ( ph -> dom z C_ A ) $.
    aomclem3.y $e |- ( ph -> A. a e. ~P ( R1 ` A ) ( a =/= (/) ->
        ( y ` a ) e. ( ( ~P a i^i Fin ) \ { (/) } ) ) ) $.
    $( Lemma for ~ dfac11 .  Successor case 3, our required well-ordering.
       (Contributed by Stefan O'Rear, 19-Jan-2015.) $)
    aomclem3 $p |- ( ph -> E We ( R1 ` dom z ) ) $=
      ( cv cdm cr1 cfv cvv crn cdif cmpt crecs wceq rneq difeq2d fveq2d cbvmptv
      weq recseq ax-mp eqtri fvexd c0 wne wcel wi cpw wral aomclem2 neeq1 fveq2
      id eleq12d imbi12d cbvralvw sylib dnwech ) ALKJICUCUDZUEUFZGFHUGGIUGVRIUC
      ZUHZUIZFUFZUJZUKZKUGVRKUCZUHZUIZFUFZUJZUKZOWCWIULWDWJULIKUGWBWHIKUQZWAWGF
      WKVTWFVRVSWEUMUNUOUPWCWIURUSUTAVQUEVAAVSVBVCZVSFUFZVSVDZVEZIVRVFZVGLUCZVB
      VCZWQFUFZWQVDZVEZLWPVGABCDEFIJKLMNQRSTUAUBVHWOXAILWPILUQZWLWRWNWTVSWQVBVI
      XBWMWSVSWQVSWQFVJXBVKVLVMVNVOPVP $.
  $}

  ${
    $d z a b c $.  $d ph a b c $.
    aomclem4.f $e |- F = { <. a , b >. | ( ( rank ` a ) _E ( rank ` b ) \/
        ( ( rank ` a ) = ( rank ` b ) /\ a ( z ` suc ( rank ` a ) ) b ) ) } $.
    aomclem4.on $e |- ( ph -> dom z e. On ) $.
    aomclem4.su $e |- ( ph -> dom z = U. dom z ) $.
    aomclem4.we $e |- ( ph -> A. a e. dom z ( z ` a ) We ( R1 ` a ) ) $.
    $( Lemma for ~ dfac11 .  Limit case.  Patch together well-orderings
       constructed so far using ~ fnwe2 to cover the limit rank.  (Contributed
       by Stefan O'Rear, 20-Jan-2015.) $)
    aomclem4 $p |- ( ph -> F We ( R1 ` dom z ) ) $=
      ( cv cr1 cfv con0 csuc crnk wceq wcel wa wwe fveq2 vc cdm cep fveq2d crab
      suceq wss cab cima cuni wfun wfn r1fnon fnfun ax-mp fndmi eqimss2i pm3.2i
      funfvima2 mpsyl elssuni syl sselda rankidb eleq2d syl5ibcom expimpd abid1
      ss2abdv df-rab 3sstr4g adantr weeq12d wral cbvralvw sylib rankr1ai adantl
      weq wb word eloni limsuc2 syl2anc mpbid rspcdva wess wf rankf a1i fssresd
      sylc epweon fnwe2 ) ADEUABJZUBZKLZMUCUAJZNZWOLCDJZOLZNZWOLZOWRXAPWSXBWOWR
      XAUFUDFAWTWQQZRZEJZOLZXAPZEWQUEZXBKLZUGZXJXCSZXIXCSAXKXDAXFWQQZXHRZEUHXFX
      JQZEUHXIXJAXNXOEAXMXHXOAXMRZXFXGNZKLZQZXHXOXPXFKMUIZUJZQXSAWQYAXFAWQXTQZW
      QYAUGKUKZMKUBZUGZRAWPMQZYBYCYEKMULYCUMMKUNUOYDMMKUMUPUQURGMWPKUSUTWQXTVAV
      BZVCXFVDVBXHXRXJXFXHXQXBKXGXAUFUDVEVFVGVIXHEWQVJEXJVHVKVLXEXFKLZXFWOLZSZX
      LEWPXBXFXBPYHXJYIXCXFXBWOTXFXBKTVMAYJEWPVNZXDAWTKLZWTWOLZSZDWPVNYKIYNYJDE
      WPDEVSYLYHYMYIWTXFWOTWTXFKTVMVOVPVLXEXAWPQZXBWPQZXDYOAWTWPVQVRAYOYPVTZXDA
      WPWAZWPWPUJPYQAYFYRGWPWBVBHWPXAWCWDVLWEWFXIXJXCWGWLAYAMWQOYAMOWHAWIWJYGWK
      MUCSAWMWJWN $.
  $}

  ${
    $d z y a b c d $.  $d ph a b $.  $d C a b c d $.  $d D a b c d $.
    aomclem5.b $e |- B = { <. a , b >. | E. c e. ( R1 ` U. dom z )
        ( ( c e. b /\ -. c e. a ) /\ A. d e. ( R1 ` U. dom z )
          ( d ( z ` U. dom z ) c -> ( d e. a <-> d e. b ) ) ) } $.
    aomclem5.c $e |- C = ( a e. _V |->
        sup ( ( y ` a ) , ( R1 ` dom z ) , B ) ) $.
    aomclem5.d $e |- D = recs ( ( a e. _V |->
        ( C ` ( ( R1 ` dom z ) \ ran a ) ) ) ) $.
    aomclem5.e $e |- E = { <. a , b >. | |^| ( `' D " { a } ) e.
        |^| ( `' D " { b } ) } $.
    aomclem5.f $e |- F = { <. a , b >. | ( ( rank ` a ) _E ( rank ` b ) \/
        ( ( rank ` a ) = ( rank ` b ) /\ a ( z ` suc ( rank ` a ) ) b ) ) } $.
    aomclem5.g $e |- G = ( if ( dom z = U. dom z , F , E ) i^i
        ( ( R1 ` dom z ) X. ( R1 ` dom z ) ) ) $.
    aomclem5.on $e |- ( ph -> dom z e. On ) $.
    aomclem5.we $e |- ( ph -> A. a e. dom z ( z ` a ) We ( R1 ` a ) ) $.
    aomclem5.a $e |- ( ph -> A e. On ) $.
    aomclem5.za $e |- ( ph -> dom z C_ A ) $.
    aomclem5.y $e |- ( ph -> A. a e. ~P ( R1 ` A ) ( a =/= (/) ->
        ( y ` a ) e. ( ( ~P a i^i Fin ) \ { (/) } ) ) ) $.
    $( Lemma for ~ dfac11 .  Combine the successor case with the limit case.
       (Contributed by Stefan O'Rear, 20-Jan-2015.) $)
    aomclem5 $p |- ( ph -> G We ( R1 ` dom z ) ) $=
      ( cv cdm cr1 cfv cuni wceq cif cxp cin wwe wa con0 wcel adantr simpr wral
      aomclem4 iftrue adantl eqidd weeq12d mpbird wn csuc word orduniorsuc 3syl
      wo eloni orcanai wss c0 wne cpw cfn csn cdif wi aomclem3 pm2.61dan weinxp
      iffalse sylib wb weeq1 ax-mp sylibr ) ACUFZUGZUHUIZWNWNUJZUKZIHULZWOWOUMU
      NZUOZWOJUOZAWOWRUOZWTAWQXBAWQUPZXBWOIUOXCCIKLSAWNUQURZWQUAUSAWQUTAKUFZUHU
      IXEWMUIUOKWNVAZWQUBUSVBXCWOWOWRIWQWRIUKAWQIHVCVDXCWOVEVFVGAWQVHZUPZXBWOHU
      OXHBCDEFGHKLMNOPQRAXDXGUAUSAWQWNWPVIUKZAXDWNVJWQXIVMUAWNVNWNVKVLVOAXFXGUB
      USADUQURXGUCUSAWNDVPXGUDUSAXEVQVRXEBUFUIXEVSVTUNVQWAWBURWCKDUHUIVSVAXGUEU
      SWDXHWOWOWRHXGWRHUKAWQIHWGVDXHWOVEVFVGWEWOWRWFWHJWSUKXAWTWITWOJWSWJWKWL
      $.
  $}

  ${
    $d z y a b c d $.  $d ph a b c d z $.  $d C a b c d $.  $d D a b c d $.
    $d A a b c d z $.  $d H a b c d z $.  $d G d $.
    aomclem6.b $e |- B = { <. a , b >. | E. c e. ( R1 ` U. dom z )
        ( ( c e. b /\ -. c e. a ) /\ A. d e. ( R1 ` U. dom z )
          ( d ( z ` U. dom z ) c -> ( d e. a <-> d e. b ) ) ) } $.
    aomclem6.c $e |- C = ( a e. _V |->
        sup ( ( y ` a ) , ( R1 ` dom z ) , B ) ) $.
    aomclem6.d $e |- D = recs ( ( a e. _V |->
        ( C ` ( ( R1 ` dom z ) \ ran a ) ) ) ) $.
    aomclem6.e $e |- E = { <. a , b >. | |^| ( `' D " { a } ) e.
        |^| ( `' D " { b } ) } $.
    aomclem6.f $e |- F = { <. a , b >. | ( ( rank ` a ) _E ( rank ` b ) \/
        ( ( rank ` a ) = ( rank ` b ) /\ a ( z ` suc ( rank ` a ) ) b ) ) } $.
    aomclem6.g $e |- G = ( if ( dom z = U. dom z , F , E ) i^i
        ( ( R1 ` dom z ) X. ( R1 ` dom z ) ) ) $.
    aomclem6.h $e |- H = recs ( ( z e. _V |-> G ) ) $.
    aomclem6.a $e |- ( ph -> A e. On ) $.
    aomclem6.y $e |- ( ph -> A. a e. ~P ( R1 ` A ) ( a =/= (/) ->
        ( y ` a ) e. ( ( ~P a i^i Fin ) \ { (/) } ) ) ) $.
    $( Lemma for ~ dfac11 .  Transfinite induction, close over ` z ` .
       (Contributed by Stefan O'Rear, 20-Jan-2015.) $)
    aomclem6 $p |- ( ph -> ( H ` A ) We ( R1 ` A ) ) $=
      ( wss cr1 cfv wwe ssid con0 wcel wa adantr cv wi weq sseq1 anbi2d weeq12d
      fveq2 imbi12d wceq wral w3a cres csb wsbc wal cdm dmeq adantl simpl1 onss
      wfn cmpt tfr1 fnssres mpan fndm 4syl eqtrd eqeltrd eleq2d simpll2 simpl3l
      cvv biimpa onelss syl imp simpl3r sstrd rspcva syl22anc wb fveq1 ad2antlr
      eqsstrd fvres weeq1 mpbird ralrimiva c0 wne cpw cfn cin csn cdif aomclem5
      fveq2d weeq2 mpbid ex alrimiv nfv nfsbc1v nfim eqeq1 sbceq1a cbvalv1 wfun
      sylib fnfun ax-mp resfunexg mp2an ceqsal sbccow nfcsb1v nfcv nfwe csbeq1a
      vex sbciegf crecs recsval fveq1i cuni cif fvex inex2 eqeltri csbex fvmpts
      xpex eqid reseq1i fveq2i eqtr3i 3eqtr4g 3ad2ant1 3exp tfis3 mpcom mpan2
      cxp ) ADDUEZDUFUGZDKUGZUHZDUIDUJUKZAUURULZUVAAUVBUURUCUMANUNZDUEZULZUVDUF
      UGZUVDKUGZUHZUOAOUNZDUEZULZUVJUFUGZUVJKUGZUHZUOZUVCUVAUONODNOUPZUVFUVLUVI
      UVOUVQUVEUVKAUVDUVJDUQURUVQUVGUVMUVHUVNUVDUVJKUTUVDUVJUFUTUSVAUVDDVBZUVFU
      VCUVIUVAUVRUVEUURAUVDDDUQURUVRUVGUUSUVHUUTUVDDKUTUVDDUFUTUSVAUVDUJUKZUVPO
      UVDVCZUVFUVIUVSUVTUVFVDZUVIUVGCKUVDVEZJVFZUHZUWAUVGJUHZCUWBVGZUWDUWAUWECU
      VJVGZOUWBVGZUWFUWAUVJUWBVBZUWGUOZOVHZUWHUWACUNZUWBVBZUWEUOZCVHUWKUWAUWNCU
      WAUWMUWEUWAUWMULZUWLVIZUFUGZJUHZUWEUWOBCDEFGHIJLMNOPQRSTUAUWOUWPUVDUJUWOU
      WPUWBVIZUVDUWMUWPUWSVBUWAUWLUWBVJVKUWOUVSUVDUJUEZUWBUVDVNZUWSUVDVBUVSUVTU
      VFUWMVLZUVDVMKUJVNZUWTUXAKCWFJVOZUBVPZUJUVDKVQVRUVDUWBVSVTWAZUXBWBZUWOLUN
      ZUFUGZUXHUWLUGZUHZLUWPUWOUXHUWPUKZULZUXKUXIUXHKUGZUHZUXMUXHUVDUKZUVTAUXHD
      UEZUXOUWOUXLUXPUWOUWPUVDUXHUXFWCWGZUVSUVTUVFUWMUXLWDUWOAUXLAUVEUVSUVTUWMW
      EZUMUXMUXHUWPDUWOUXLUXHUWPUEZUWOUWPUJUKUXLUXTUOUXGUWPUXHWHWIWJUWOUWPDUEUX
      LUWOUWPUVDDUXFAUVEUVSUVTUWMWKWRZUMWLUXPUVTULAUXQULZUXOUVPUYBUXOUOOUXHUVDO
      LUPZUVLUYBUVOUXOUYCUVKUXQAUVJUXHDUQURUYCUVMUXIUVNUXNUVJUXHKUTUVJUXHUFUTUS
      VAWMWJWNUXMUXJUXNVBUXKUXOWOUXMUXJUXHUWBUGZUXNUWMUXJUYDVBUWAUXLUXHUWLUWBWP
      WQUXMUXPUYDUXNVBUXRUXHUVDKWSWIWAUXIUXJUXNWTWIXAXBUWOAUVBUXSUCWIUYAUWOAUXH
      XCXDUXHBUNUGUXHXEXFXGXCXHXIUKUOLUUSXEVCUXSUDWIXJUWOUWQUVGVBUWRUWEWOUWOUWP
      UVDUFUXFXKUWQUVGJXLWIXMXNXOUWNUWJCOUWNOXPUWIUWGCUWICXPUWECUVJXQXRCOUPUWMU
      WIUWEUWGUWLUVJUWBXSUWECUVJXTVAYAYCUWGUWHOUWBUWGOUWBXQKYBZUVDWFUKUWBWFUKZU
      XCUYEUXEUJKYDYENYNKUVDWFYFYGZUWGOUWBXTYHYCUWECOUWBYIYCUYFUWFUWDWOUYGUWEUW
      DCUWBWFCUVGUWCCUWBJYJCUVGYKYLUWMJUWCVBUWEUWDWOCUWBJYMUVGJUWCWTWIYOYEYCUVS
      UVTUVIUWDWOZUVFUVSUVHUWCVBUYHUVSUVDUXDYPZUGUYIUVDVEZUXDUGZUVHUWCUVDUXDYQU
      VDKUYIUBYRUWBUXDUGZUWCUYKUYFUWCWFUKUYLUWCVBUYGCUWBJJUWPUWPYSVBIHYTZUWQUWQ
      UUQZXGWFUAUYNUYMUWQUWQUWPUFUUAZUYOUUFUUBUUCUUDCUWBJWFUXDWFUXDUUGUUEYGUWBU
      YJUXDKUYIUVDUBUUHUUIUUJUUKUVGUVHUWCWTWIUULXAUUMUUNUUOUUP $.

    $( Lemma for ~ dfac11 . ` ( R1 `` A ) ` is well-orderable.  (Contributed by
       Stefan O'Rear, 20-Jan-2015.) $)
    aomclem7 $p |- ( ph -> E. b b We ( R1 ` A ) ) $=
      ( cr1 cfv wwe cv wex aomclem6 fvex weeq1 spcev syl ) ADUEUFZDKUFZUGZUOMUH
      ZUGZMUIABCDEFGHIJKLMNOPQRSTUAUBUCUDUJUSUQMUPDKUKUOURUPULUMUN $.
  $}

  ${
    $d ph c d e f g h i j l b $.  $d A a b c d e f g h i j l $.
    $d y a c d e f g h i j l b $.
    aomclem8.a $e |- ( ph -> A e. On ) $.
    aomclem8.y $e |- ( ph -> A. a e. ~P ( R1 ` A ) ( a =/= (/) ->
        ( y ` a ) e. ( ( ~P a i^i Fin ) \ { (/) } ) ) ) $.
    $( Lemma for ~ dfac11 .  Perform variable substitutions.  This is the most
       we can say without invoking regularity.  (Contributed by Stefan O'Rear,
       20-Jan-2015.) $)
    aomclem8 $p |- ( ph -> E. b b We ( R1 ` A ) ) $=
      ( vi vh vg vj vc vd wel wa cv cfv cvv wceq nfcv ve vl vf wn cdm wbr wb wi
      cuni cr1 wral wrex copab csup cmpt crn cdif crecs ccnv csn cima cint wcel
      crnk cep csuc wo cif cxp cin weq elequ2 notbid bi2anan9r bi2bian9 ralbidv
      imbi2d anbi12d rexbidv elequ1 breq2 imbi1d breq1 bibi12d imbi12d cbvralvw
      bitrdi cbvrexvw cbvopabv nfopab1 nfsup fveq2 supeq1d cbvmpt nffvmpt1 rneq
      difeq2d fveq2d recseq ax-mp nfmpt1 nfrecs nfcnv nfima nfint nfopab2 nfmpt
      nfv nfel nffv sneq imaeq2d inteqd eleq12 syl2an breqan12d eqeqan12d simpl
      cbvopab suceq adantr simpr breq123d orbi12d eqid dmeq unieqd breqd anbi2d
      syl opabbidv fveq12d mpteq2dv difeq1d imaeq1d eleq12d c0 wne cpw cfn pweq
      eqeq12d fveq1 orbi2d eqidd raleqbidv rexeqbidv supeq123d cnveqd ifbieq12d
      id sqxpeqd ineq12d cbvmptv neeq1 ineq1d sylib aomclem7 ) ABUACHINZHJNZUDZ
      OZKPZHPZUAPZUEZUIZUVEQZUFZKJNZKINZUGZUHZKUVGUJQZUKZOZHUVNULZJIUMZJRJPZBPZ
      QZUVFUJQZUVRUNZUOZJRUWBUVSUPZUQZUWDQZUOZURZUWIUSZUVSUTZVAZVBZUWJIPZUTZVAZ
      VBZVCZJIUMZUVSVDQZUWNVDQZVEUFZUWTUXASZUVSUWNUWTVFZUVEQZUFZOZVGZJIUMZUVFUV
      GSZUXIUWSVHZUWBUWBVIZVJZUBRUBPZUEZUXOUIZSZUXBUXCUVSUWNUXDUXNQZUFZOZVGZJIU
      MZJRUXOUJQZUWEUQZJRUWAUYCUVBUVCUVDUXPUXNQZUFZUVLUHZKUXPUJQZUKZOZHUYHULZJI
      UMZUNZUOZQZUOZURZUSZUWKVAZVBZUYRUWOVAZVBZVCZJIUMZVHZUYCUYCVIZVJZUOZURZLEM
      UCUVQMENZMLNZUDZOZUCPZMPZUVHUFZUCLNZUCENZUGZUHZUCUVNUKZOZMUVNULZJILEJLVKZ
      IEVKZOZUVQHENZHLNZUDZOZUVIKLNZKENZUGZUHZKUVNUKZOZHUVNULVVCVVFUVPVVPHUVNVV
      FUVBVVJUVOVVOVVEUUSVVGVVDUVAVVIIEHVLVVDUUTVVHJLHVLVMVNVVFUVMVVNKUVNVVFUVL
      VVMUVIVVDUVJVVKVVEUVKVVLJLKVLIEKVLVOVQVPVRVSVVPVVBHMUVNHMVKZVVJVUMVVOVVAV
      VQVVGVUJVVIVULHMEVTVVQVVHVUKHMLVTVMVRVVQVVOUVCVUOUVHUFZVVMUHZKUVNUKVVAVVQ
      VVNVVSKUVNVVQUVIVVRVVMUVDVUOUVCUVHWAWBVPVVSVUTKUCUVNKUCVKZVVRVUPVVMVUSUVC
      VUNVUOUVHWCVVTVVKVUQVVLVURKUCLVTKUCEVTWDWEWFWGVRWHWGWIJLRUWCLPZUVTQZUWBUV
      RUNLUWCTJVWBUWBUVRJVWBTJUWBTUVQJIWJWKVVDUWBUWAVWBUVRUVSVWAUVTWLWMWNUWHLRU
      WBVWAUPZUQZUWDQZUOZSUWIVWFURSJLRUWGVWELUWGTJRUWCVWDWOVVDUWFVWDUWDVVDUWEVW
      CUWBUVSVWAWPWQWRWNUWHVWFWSWTUWRUWJVWAUTZVAZVBZUWJEPZUTZVAZVBZVCZJILEUWRLX
      HUWREXHJVWIVWMJVWHJUWJVWGJUWIJUWHJRUWGXAXBXCZJVWGTXDXEJVWLJUWJVWKVWOJVWKT
      XDXEXIIVWIVWMIVWHIUWJVWGIUWIIUWHIJRUWGIRTZIUWFUWDIJRUWCVWPIUWAUWBUVRIUWAT
      IUWBTUVQJIXFWKXGIUWFTXJXGXBXCZIVWGTXDXEIVWLIUWJVWKVWQIVWKTXDXEXIVVDUWMVWI
      SUWQVWMSUWRVWNUGVVEVVDUWLVWHVVDUWKVWGUWJUVSVWAXKXLXMVVEUWPVWLVVEUWOVWKUWJ
      UWNVWJXKXLXMUWMVWIUWQVWMXNXOXSUXHVWAVDQZVWJVDQZVEUFZVWRVWSSZVWAVWJVWRVFZU
      VEQZUFZOZVGJILEVVFUXBVWTUXGVXEVVDVVEUWTVWRUXAVWSVEUVSVWAVDWLZUWNVWJVDWLZX
      PVVFUXCVXAUXFVXDVVDVVEUWTVWRUXAVWSVXFVXGXQVVFUVSVWAUWNVWJUXEVXCVVDVVEXRVV
      FUXDVXBUVEVVDUXDVXBSZVVEVVDUWTVWRSVXHVXFUWTVWRXTYJYAWRVVDVVEYBYCVRYDWIUXM
      YEVUHUARUXMUOZSVUIVXIURSUBUARVUGUXMUBUAVKZVUEUXKVUFUXLVXJUXQUXJUYBVUDUXIU
      WSVXJUXOUVFUXPUVGUXNUVEYFZVXJUXOUVFVXKYGZUUBVXJUYAUXHJIVXJUXTUXGUXBVXJUXS
      UXFUXCVXJUXRUXEUVSUWNUXDUXNUVEUUCYHYIUUDYKVXJVUCUWRJIVXJUYTUWMVUBUWQVXJUY
      SUWLVXJUYRUWJUWKVXJUYQUWIVXJUYPUWHSUYQUWISVXJJRUYOUWGVXJUYDUWFUYNUWDVXJJR
      UYMUWCVXJUWAUYCUYLUWAUWBUVRVXJUWAUUEVXJUXOUVFUJVXKWRZVXJUYKUVQJIVXJUYJUVP
      HUYHUVNVXJUXPUVGUJVXLWRZVXJUYIUVOUVBVXJUYGUVMKUYHUVNVXNVXJUYFUVIUVLVXJUYE
      UVHUVCUVDVXJUXPUVGUXNUVEVXJUUKVXLYLYHWBUUFYIUUGYKUUHYMVXJUYCUWBUWEVXMYNYL
      YMUYPUWHWSYJUUIZYOXMVXJVUAUWPVXJUYRUWJUWOVXOYOXMYPYKUUJVXJUYCUWBVXMUULUUM
      UUNVUHVXIWSWTFADPZYQYRZVXPUVTQZVXPYSZYTVJZYQUTZUQZVCZUHZDCUJQYSZUKVWAYQYR
      ZVWBVWAYSZYTVJZVYAUQZVCZUHZLVYEUKGVYDVYKDLVYEDLVKZVXQVYFVYCVYJVXPVWAYQUUO
      VYLVXRVWBVYBVYIVXPVWAUVTWLVYLVXTVYHVYAVYLVXSVYGYTVXPVWAUUAUUPYNYPWEWFUUQU
      UR $.
  $}

  ${
    $d x z f a b c d $.
    $( The right-hand side of this theorem (compare with ~ ac4 ), sometimes
       known as the "axiom of multiple choice", is a choice equivalent.
       Curiously, this statement cannot be proved without ~ ax-reg , despite
       not mentioning the cumulative hierarchy in any way as most consequences
       of regularity do.

       This is definition (MC) of [Schechter] p. 141. _EDITORIAL_: the proof is
       not original with me of course but I lost my reference sometime after
       writing it.

       A multiple choice function allows any total order to be extended to a
       choice function, which in turn defines a well-ordering.  Since a
       well-ordering on a set defines a simple ordering of the power set, this
       allows the trivial well-ordering of the empty set to be transfinitely
       bootstrapped up the cumulative hierarchy to any desired level.
       (Contributed by Stefan O'Rear, 20-Jan-2015.)  (Revised by Stefan O'Rear,
       1-Jun-2015.) $)
    dfac11 $p |- ( CHOICE <-> A. x E. f A. z e. x ( z =/= (/) ->
        ( f ` z ) e. ( ( ~P z i^i Fin ) \ { (/) } ) ) ) $=
      ( vd vc va vb wac cv c0 wne cfv cfn csn wcel wi wral wex wal wceq cpw cin
      cdif dfac3 raleq exbidv cbvalvw cmpt neeq1 fveq2 eleq12d imbi12d cbvralvw
      w3a sneqd eqid snex fvmpt 3ad2ant1 wss simp3 snssd elpw sylibr snfi elind
      a1i fvex snnz eldifsn sylanbrc eqeltrd 3exp a2d ralimia sylbi mptex fveq1
      vex eleq1d imbi2d ralbidv spcev syl exlimiv alimi wwe crnk pwex spcv con0
      id cr1 rankon aomclem8 cvv r1rankid wess eximdv mp2b alrimiv dfac8 impbii
      3syl ) HBIZJKZXECIZLZXEUAZMUBZJNUCZOZPZBAIZQZCRZASZHDIZJKZXREIZLZXROZPZDF
      IZQZERZFSZXQFDEUDYGYCDXNQZERZASXQYFYIFAYDXNTYEYHEYCDYDXNUEUFUGYIXPAYHXPEY
      HXFXEGXNGIZXTLZNZUHZLZXKOZPZBXNQZXPYHXFXEXTLZXEOZPZBXNQYQYCYTDBXNXRXETZXS
      XFYBYSXRXEJUIUUAYAYRXRXEXRXEXTUJUUAWLUKULUMYTYPBXNXEXNOZXFYSYOUUBXFYSYOUU
      BXFYSUNZYNYRNZXKUUBXFYNUUDTYSGXEYLUUDXNYMYJXETYKYRYJXEXTUJUOYMUPYRUQZURUS
      UUCUUDXJOUUDJKZUUDXKOUUCXIMUUDUUCUUDXEUTUUDXIOUUCYRXEUUBXFYSVAVBUUDXEUUEV
      CVDUUDMOUUCYRVEVGVFUUFUUCYRXEXTVHVIVGUUDXJJVJVKVLVMVNVOVPXOYQCYMGXNYLAVSV
      QXGYMTZXMYPBXNUUGXLYOXFUUGXHYNXKXEXGYMVRVTWAWBWCWDWEWFVPVPXQYDYJWGZGRZFSH
      XQUUIFXQXMBYDWHLZWMLZUAZQZCRZUUKYJWGZGRZUUIXPUUNAUULUUKUUJWMVHWIXNUULTXOU
      UMCXMBXNUULUEUFWJUUMUUPCUUMCUUJBGUUJWKOUUMYDWNVGUUMWLWOWEYDWPOYDUUKUTZUUP
      UUIPFVSYDWPWQUUQUUOUUHGYDUUKYJWRWSWTXDXAFGXBVDXC $.
  $}

  ${
    $d ph f x y z $.  $d C f w $.  $d C y z $.  $d I f x y z $.  $d J f y z $.
    $d S y $.  $d U y $.  $d w x $.
    kelac1.z $e |- ( ( ph /\ x e. I ) -> S =/= (/) ) $.
    kelac1.j $e |- ( ( ph /\ x e. I ) -> J e. Top ) $.
    kelac1.c $e |- ( ( ph /\ x e. I ) -> C e. ( Clsd ` J ) ) $.
    kelac1.b $e |- ( ( ph /\ x e. I ) -> B : S -1-1-onto-> C ) $.
    kelac1.u $e |- ( ( ph /\ x e. I ) -> U e. U. J ) $.
    kelac1.k $e |- ( ph -> ( Xt_ ` ( x e. I |-> J ) ) e. Comp ) $.
    $( Kelley's choice, basic form: if a collection of sets can be cast as
       closed sets in the factors of a topology, and there is a definable
       element in each topology (which need not be in the closed set - if it
       were this would be trivial), then compactness (via finite intersection)
       guarantees that the final product is nonempty.  (Contributed by Stefan
       O'Rear, 22-Feb-2015.) $)
    kelac1 $p |- ( ph -> X_ x e. I S =/= (/) ) $=
      ( vy wcel c0 wral wa cvv vz vf vw cixp wne wex cuni weq cif ciin cin wceq
      cv wss ccld cfv eqid cldss syl ralrimiva boxriin cmpt ctop wf ccmp cmptop
      cpt wn 0ntop fvprc eleq1d mtbiri con4i 3syl fmpttd dmfex syl2anc ptunimpt
      ineq1d topcld ifcld ptcldmpt adantr cfn wrex simprr cima wf1o f1ofo foima
      wfo eqcomd wfn wb f1ofn ssid fnimaeq0 sylancl necon3bid mpbird eqnetrd n0
      sylib rexv sylibr wi ssralv mpan9 eleq1 ac6sfi ad2antrr wel cdif ad2antrl
      cun iftrue simpll simprl sselda sseld impr eqeltrd expr ralimdva iffalsed
      imp eldifn adantl eldifi sylan2 ralun undif raleqdv mpbid mptelixpg eleq2
      biimpi adantlr ne0d exlimddv simplrr ifbothda disjdifr a1i simplr syl3anc
      simpr disjne neneqd 3eltr4d ad3antrrr mptexg eliin elind adantrl cmpfiiin
      ccnv elixp2 simp3bi f1ocnv f1of ffvelcdm ex 4syl ) AOUMZBGDUDZPZBGEUDZQUE
      OAUVFQUEUVGOUFAUVFBGHUGZUDZOGBGBOUHZDUVIUIZUDZUJZUKZQADUVIUNZBGRUVFUVOULA
      UVPBGABUMZGPZSZDHUOUPZPUVPKDHUVIUVIUQZURUSZUTBODUVIGVAUSAUVOBGHVBZVGUPZUG
      ZUVNUKQAUVJUWEUVNAGTPZHVCPZBGRUVJUWEULAUWCTPZGVCUWCVDUWFAUWDVEPUWDVCPZUWH
      NUWDVFUWHUWIUWHVHZUWIQVCPVIUWJUWDQVCUWCVGVJVKVLVMVNABGHVCJVOGVCTUWCVPVQZA
      UWGBGJUTBGUWDHTUWDUQVRVQZVSAUVMOGUWDUWEUAUWEUQNAUVMUWDUOUPPUVEGPAGUVLBHTU
      WKJUVSUVKDUVIUVTKUVSUWGUVIUVTPJHUVIUWAVTUSWAWBWCAUAUMZGUNZUWMWDPZSZSZUWMT
      UBUMZVDZUVQUWRUPZDPZBUWMRZSZUWEOUWMUVMUJZUKZQUEZUBUWQUWOUCUMZDPZUCTWEZBUW
      MRZUXCUBUFAUWNUWOWFAUXIBGRZUWPUXJAUXIBGUVSUXHUCUFZUXIUVSDQUEUXLUVSDCEWGZQ
      UVSUXMDUVSEDCWHZEDCWKUXMDULLEDCWIEDCWJVNWLUVSUXMQUEEQUEIUVSUXMQEQUVSCEWMZ
      EEUNUXMQULEQULWNUVSUXNUXOLEDCWOUSEWPEECWQWRWSWTXAUCDXBXCUXHUCXDXEUTUWNUXK
      UXJXFUWOUXIBUWMGXGWCXHUXHUXABUCUWMTUBUXGUWTDXIXJVQUWQUXBUXFUWSUWQUXBSZUXE
      UVJUXDUKZQAUXEUXQULUWPUXBAUWEUVJUXDAUVJUWEUWLWLVSXKUXPUXQBGBUAXLZUWTFUIZV
      BZUXPUVJUXDUXTUXPUXTUVJPZUXSUVIPZBGRZUXPUYBBUWMGUWMXMZXOZRZUYCUXPUYBBUWMR
      ZUYBBUYDRZUYFUWQUXBUYGUWQUXAUYBBUWMUWQUXRUXAUYBUWQUXRUXASSZUXSUWTUVIUXRUX
      SUWTULUWQUXAUXRUWTFXPXNZUWQUXRUXAUWTUVIPZUWQUXRSZDUVIUWTUYLAUVRUVPAUWPUXR
      XQUWQUWMGUVQAUWNUWOXRXSUWBVQXTYAZYBYCYDYFAUYHUWPUXBAUYBBUYDAUVQUYDPZSUXSF
      UVIUYNUXSFULZAUYNUXRUWTFUVQGUWMYGYEZYHUYNAUVRFUVIPZUVQGUWMYIMYJZYBUTXKUYB
      BUWMUYDYKVQUWQUYFUYCWNUXBUWQUYBBUYEGUWNUYEGULZAUWOUWNUYSUWMGYLYQXNZYMWCYN
      UXPUWFUYAUYCWNAUWFUWPUXBUWKXKBGUXSUVITYOUSWTUXPUXTUXDPZUXTUVMPZOUWMRZUXPV
      UBOUWMUXPOUAXLZSZVUBUXSUVLPZBGRZVUEVUFBUYERZVUGVUEVUFBUWMRZVUFBUYDRZVUHUX
      PVUIVUDUWQUXBVUIUWQUXAVUFBUWMUWQUXRUXAVUFUYIUXSUWTUVLUYJUVKUXAUYKUWTUVLPU
      YIDUVIDUVLUWTYPUVIUVLUWTYPUWQUXRUXAUVKUUAUYIUYKUVKVHUYMWCUUBYBYCYDYFWCUWQ
      VUDVUJUXBAVUDVUJUWPAVUDSZVUFBUYDVUKUYNSZFUVIUXSUVLAUYNUYQVUDUYRYRUYNUYOVU
      KUYPYHVULUVKDUVIVULUVQUVEVULUYDUWMUKQULZUYNVUDUVQUVEUEVUMVULUWMGUUCUUDVUK
      UYNUUGAVUDUYNUUEUYDUWMUVQUVEUUHUUFUUIYEUUJUTYRYRVUFBUWMUYDYKVQUWQVUHVUGWN
      UXBVUDUWQVUFBUYEGUYTYMXKYNVUEUWFVUBVUGWNAUWFUWPUXBVUDUWKUUKBGUXSUVLTYOUSW
      TUTUXPUXTTPZVUAVUCWNAVUNUWPUXBAUWFVUNUWKBGUXSTUULUSXKOUXTUWMUVMTUUMUSWTUU
      NYSXAUUOYTUUPXAXAOUVFXBXCAUVGSZUVHBGUVQUVEUPZCUUQZUPZVBZVUOVUSUVHPZVUREPZ
      BGRZUVGAVUPDPZBGRZVVBUVGUVETPUVEGWMVVDBGDUVEUURUUSAVVDVVBAVVCVVABGUVSUXND
      EVUQWHDEVUQVDZVVCVVAXFLEDCUUTDEVUQUVAVVEVVCVVADEVUPVUQUVBUVCUVDYDYFYJAVUT
      VVBWNZUVGAUWFVVFUWKBGVURETYOUSWCWTYSYT $.
  $}

  ${
    $d S x y $.
    $( Lemma for ~ kelac2 and ~ dfac21 : knob topologies are compact.
       (Contributed by Stefan O'Rear, 22-Feb-2015.) $)
    kelac2lem $p |- ( S e. V -> ( topGen ` { S , { ~P U. S } } ) e. Comp ) $=
      ( vx vy wcel cpw ctop cfn cin cvv cv c0 wceq wo wral vex elpr eqtr3 orcd
      wa cuni csn cpr ctg cfv ccmp ctb weq prex ineq12 incom wn pwuninel disjsn
      mpbir eqtri eqtrdi olcd ccase syl2anb rgen2 baspartn mp2an tgcl mp1i cdom
      wbr prfi pwfi mpbi tgdom ax-mp domfi a1i elind fincmp syl ) ABEZAAUAFZUBZ
      UCZUDUEZGHIEWBUFEVRGHWBWAUGEZWBGEVRWAJEZCDUHZCKZDKZIZLMZNZDWAOCWAOWCAVTUI
      ZWJCDWAWAWFWAEWFAMZWFVTMZNWGAMZWGVTMZNWJWGWAEWFAVTCPQWGAVTDPQWLWNWMWOWJWL
      WNTWEWIWFWGARSWMWNTZWIWEWPWHVTAIZLWFVTWGAUJWQAVTIZLVTAUKWRLMVSAEULAUMAVSU
      NUOZUPUQURWLWOTZWIWEWTWHWRLWFAWGVTUJWSUQURWMWOTWEWIWFWGVTRSUSUTVACDWAJVBV
      CWAVDVEWBHEZVRWAFZHEZWBXBVFVGZXAWAHEXCAVTVHWAVIVJWDXDWKWAJVKVLXBWBVMVCVNV
      OWBVPVQ $.
  $}

  ${
    $d ph x $.  $d I x $.
    kelac2.s $e |- ( ( ph /\ x e. I ) -> S e. V ) $.
    kelac2.z $e |- ( ( ph /\ x e. I ) -> S =/= (/) ) $.
    kelac2.k $e |- ( ph -> ( Xt_ `
          ( x e. I |-> ( topGen ` { S , { ~P U. S } } ) ) ) e. Comp ) $.
    $( Kelley's choice, most common form: compactness of a product of knob
       topologies recovers choice.  (Contributed by Stefan O'Rear,
       22-Feb-2015.) $)
    kelac2 $p |- ( ph -> X_ x e. I S =/= (/) ) $=
      ( cuni cfv wcel 3syl cdif cun cvv wceq cin c0 a1i wss cid cpw csn cpr ctg
      cres cv ccmp ctop kelac2lem cmptop ccld uncom difeq1i difun2 eqtri uniprg
      wa snex sylancl difeq1d incom pwuninel disjsn sylibr eqtrid disj3 3eqtr4a
      wn sylib prex bastg mp1i prid2 sseldd eqeltrd prid1g elssuni unitg eqcomi
      ax-mp iscld2 syl2anc mpbird wf1o f1oi uniexg pwexg snidg eleqtrrdi kelac1
      wb 4syl ) ABUACUFZCCCIZUBZDCWPUCZUDZUEJZGABUGDKURZCEKZWSUHKWSUIKZFCEUJWSU
      KLZWTCWSULJKZWRIZCMZWSKZWTXFWQWSWTCWQNZCMZWQCMZXFWQXIWQCNZCMXJXHXKCCWQUMU
      NWQCUOUPWTXEXHCWTXAWQOKXEXHPFWPUSZCWQEOUQUTVAWTWQCQZRPWQXJPWTXMCWQQZRWQCV
      BWTWPCKVIZXNRPXOWTCVCSCWPVDVEVFWQCVGVJVHWTWRWSWQWROKZWRWSTWTCWQVKZWROVLVM
      WQWRKZWTCWQXLVNZSVOVPWTXBCXETZXDXGWLXCWTXACWRKXTFCWQEVQCWRVRLCWSXEWSIZXEX
      PYAXEPXQWROVSWAZVTWBWCWDCCWNWEWTCWFSWTWPXEYAWTWQXEWPXRWQXETWTXSWQWRVRVMWT
      XAWOOKWPOKWPWQKFCEWGWOOWHWPOWIWMVOYBWJHWK $.
  $}

  ${
    $d f g y $.  $d g x $.  $d x y $.
    $( Tychonoff's theorem is a choice equivalent.  Definition AC21 of
       Schechter p. 461.  (Contributed by Stefan O'Rear, 22-Feb-2015.)
       (Revised by Mario Carneiro, 27-Aug-2015.) $)
    dfac21 $p |- ( CHOICE <-> A. f ( f : dom f --> Comp ->
            ( Xt_ ` f ) e. Comp ) ) $=
      ( vg vx vy wac cv cdm ccmp cpt cfv wcel wi wa cvv cuni cufl fvex wceq ctg
      c0 wf wal ccrd cin vex dmex a1i simpr uniex acufl adantr eleqtrrid dfac10
      birani elind eqid ptcmpg syl3anc ex alrimiv wfun crn wnel wne cpw csn cpr
      cixp cmpt kelac2lem mp1i fmpttd ffdmd mptex id dmeq feq12d eleq1d imbi12d
      fveq2 syl5com wn df-nel biimpi ad2antlr fvelrn adantlr syl5ibcom necon3bd
      spcv eleq1 unieqd pweqd sneqd preq12d fveq2d cbvmptv fveq2i eleq1i bilani
      mpd kelac2 syldc dfac9 sylibr impbii ) EAFZGZHXGUAZXGIJZHKZLZAUBZEXLAEXIX
      KEXIMZXHNKZXIXJOZPUCGZUDKXKXOXNXGAUEUFUGEXIUHXNPXQXPXNXPNPXJXGIQUIZEPNRXI
      UJUKULXNXPNXQXREXQNRXIUMUNULUOXHXGXJNXPXJUPXPUPUQURUSUTXMBFZVAZTXSVBZVCZM
      ZCXSGZCFZXSJZVHTVDZLZBUBEXMYHBYCXMDYDDFZXSJZYJOZVEZVFZVGZSJZVIZIJZHKZYGYC
      YPGZHYPUAZXMYRYCYDHYPYCDYDYOHYJNKYOHKYCYIYDKMYIXSQYJNVJVKVLVMXLYTYRLAYPDY
      DYOXSBUEUFVNXGYPRZXIYTXKYRUUAXHYSHXGYPUUAVOXGYPVPVQUUAXJYQHXGYPIVTVRVSWJW
      AYCYRYGYCYRMZCYFYDNYFNKUUBYEYDKZMYEXSQUGYCUUCYFTVDZYRYCUUCMZTYAKZWBZUUDYB
      UUGXTUUCYBUUGTYAWCWDWEUUEUUFYFTUUEYFYAKZYFTRUUFXTUUCUUHYBYEXSWFWGYFTYAWKW
      HWIXAWGYRCYDYFYFOZVEZVFZVGZSJZVIZIJZHKYCYQUUOHYPUUNIDCYDYOUUMYIYERZYNUULS
      UUPYJYFYMUUKYIYEXSVTZUUPYLUUJUUPYKUUIUUPYJYFUUQWLWMWNWOWPWQWRWSWTXBUSXCUT
      CBXDXEXF $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Finitely generated left modules
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c LFinGen $.

  $( Extend class notation with the class of finitely generated left
     modules. $)
  clfig $a class LFinGen $.

  $( Define the class of finitely generated left modules.  Finite generation of
     subspaces can be interpreted using ` |``s ` .  (Contributed by Stefan
     O'Rear, 1-Jan-2015.) $)
  df-lfig $a |- LFinGen = { w e. LMod | ( Base ` w ) e. ( ( LSpan ` w ) "
      ( ~P ( Base ` w ) i^i Fin ) ) } $.

  ${
    $d W a b $.  $d B a b $.  $d N a b $.
    islmodfg.b $e |- B = ( Base ` W ) $.
    islmodfg.n $e |- N = ( LSpan ` W ) $.
    $( Property of a finitely generated left module.  (Contributed by Stefan
       O'Rear, 1-Jan-2015.) $)
    islmodfg $p |- ( W e. LMod -> ( W e. LFinGen <-> E. b e. ~P B ( b e. Fin /\
          ( N ` b ) = B ) ) ) $=
      ( va clmod wcel clfig cbs cfv cpw cfn cin cima cv wceq wa clspn wrex crab
      df-lfig eleq2i fveq2 eqtr4di pweqd ineq1d imaeq12d eleq12d elrab3 wfn wss
      bitrid clss eqid lspf ffnd inss1 fvelimab sylancl elin eqcomi pweqi bitri
      wb anbi1i eqeq2i anbi12i anass rexbii2 bitrdi bitrd ) CHIZCJIZCKLZBVPMZNO
      ZPZIZDQZNIZWABLZARZSZDAMZUAZVOCGQZKLZWHTLZWIMZNOZPZIZGHUBZIVNVTJWOCGUCUDW
      NVTGCHWHCRZWIVPWMVSWHCKUEZWPWJBWLVRWPWJCTLBWHCTUEFUFWPWKVQNWPWIVPWQUGUHUI
      UJUKUNVNVTWCVPRZDVRUAZWGVNBVQULVRVQUMVTWSVFVNVQCUOLZBWTBVPCVPUPWTUPFUQURV
      QNUSDVQVRVPBUTVAWRWEDVRWFWAVRIZWRSWAWFIZWBSZWDSXBWESXAXCWRWDXAWAVQIZWBSXC
      WAVQNVBXDXBWBVQWFWAVPAAVPEVCZVDUDVGVEVPAWCXEVHVIXBWBWDVJVEVKVLVM $.
  $}

  ${
    $d W b $.  $d X b $.  $d S b $.  $d U b $.  $d N b $.
    islssfg.x $e |- X = ( W |`s U ) $.
    islssfg.s $e |- S = ( LSubSp ` W ) $.
    islssfg.n $e |- N = ( LSpan ` W ) $.
    $( Property of a finitely generated left (sub)module.  (Contributed by
       Stefan O'Rear, 1-Jan-2015.) $)
    islssfg $p |- ( ( W e. LMod /\ U e. S ) -> ( X e. LFinGen <->
          E. b e. ~P U ( b e. Fin /\ ( N ` b ) = U ) ) ) $=
      ( clmod wcel wa cfv cbs wceq cpw wrex wb wss eqid cv clspn clfig ressbas2
      cfn lssss pweqd rexeqdv adantl elpwi lsslsp 3expa sylan2 ad2antlr eqeq12d
      syl eqcomd anbi2d rexbidva lsslmod islmodfg 3bitr4rd ) DJKZBAKZLZFUAZUEKZ
      VFEUBMZMZENMZOZLZFBPZQZVLFVJPZQZVGVFCMZBOZLZFVMQEUCKZVDVNVPRVCVDVLFVMVOVD
      BVJVDBDNMZSBVJOZABWADWATZHUFBWAEDGWCUDUPZUGUHUIVEVSVLFVMVEVFVMKZLZVRVKVGW
      FVQVIBVJWFVIVQWEVEVFBSZVIVQOZVFBUJVCVDWGWHBVFACVHDEGIVHTZHUKULUMUQVDWBVCW
      EWDUNUOURUSVEEJKVTVPRABDEGHUTVJVHEFVJTWIVAUPVB $.

    islssfg2.b $e |- B = ( Base ` W ) $.
    $( Property of a finitely generated left (sub)module, with a relaxed
       constraint on the spanning vectors.  (Contributed by Stefan O'Rear,
       24-Jan-2015.) $)
    islssfg2 $p |- ( ( W e. LMod /\ U e. S ) -> ( X e. LFinGen <->
          E. b e. ( ~P B i^i Fin ) ( N ` b ) = U ) ) $=
      ( wcel wa cfn cpw wrex wb wi wss elpw clmod clfig cv cfv wceq cin islssfg
      lssss adantl sstr2 mpan9 lspssid adantlr impbida vex 3bitr4g eleq1 anbi2d
      pweq eleq2d bibi1d imbi12d mpbii com12 adantld pm5.32rd elin anbi1i anass
      bitr2i bitrdi rexbidv2 bitrd ) EUALZCBLZMZFUBLGUCZNLZVQDUDZCUEZMZGCOZPVTG
      AOZNUFZPBCDEFGHIJUGVPWAVTGWBWDVPVQWBLZWAMVQWCLZWAMZVQWDLZVTMZVPWAWEWFVPVT
      WEWFQZVRVTVPWJVTVNVSBLZMZVQVSOZLZWFQZRVPWJRWLVQVSSZVQASZWNWFWLWPWQWLVSASZ
      WPWQWKWRVNBVSAEKIUHUIVQVSAUJUKVNWQWPWKVQDAEKJULUMUNVQVSGUOZTVQAWSTUPVTWLV
      PWOWJVTWKVOVNVSCBUQURVTWNWEWFVTWMWBVQVSCUSUTVAVBVCVDVEVFWIWFVRMZVTMWGWHWT
      VTVQWCNVGVHWFVRVTVIVJVKVLVM $.
  $}

  ${
    $d W a $.  $d N a $.  $d W a $.  $d V a $.  $d X a $.  $d B a $.
    islssfgi.n $e |- N = ( LSpan ` W ) $.
    islssfgi.v $e |- V = ( Base ` W ) $.
    islssfgi.x $e |- X = ( W |`s ( N ` B ) ) $.
    $( Finitely spanned subspaces are finitely generated.  (Contributed by
       Stefan O'Rear, 24-Jan-2015.) $)
    islssfgi $p |- ( ( W e. LMod /\ B C_ V /\ B e. Fin ) -> X e. LFinGen ) $=
      ( va clmod wcel wss cfn w3a clfig cv cfv wceq cpw eqid cin wrex cbs fvexi
      elpw2 biimpri 3ad2ant2 simp3 elind fveqeq2 rspcev sylancl clss wb 3adant3
      simp1 lspcl islssfg2 syl2anc mpbird ) DJKZACLZAMKZNZEOKZIPZBQABQZRZICSZMU
      AZUBZVDAVJKVGVGRZVKVDVIMAVBVAAVIKZVCVMVBACCDUCGUDUEUFUGVAVBVCUHUIVGTVHVLI
      AVJVFAVGBUJUKULVDVAVGDUMQZKZVEVKUNVAVBVCUPVAVBVOVCVNABCDGVNTZFUQUOCVNVGBD
      EIHVPFGURUSUT $.
  $}

  $( Finitely generated left modules are left modules.  (Contributed by Stefan
     O'Rear, 1-Jan-2015.) $)
  fglmod $p |- ( M e. LFinGen -> M e. LMod ) $=
    ( va clfig clmod cbs cfv clspn cpw cfn cin cima wcel df-lfig ssrab3 sseli
    cv ) CDABPZEFZQGFRHIJKLBDCBMNO $.

  ${
    $d ph a b $.  $d D a b $.  $d E a b $.  $d F a b $.  $d A a b $.
    $d B a b $.  $d W a b $.  $d .(+) a b $.  $d U a b $.
    lsmfgcl.u $e |- U = ( LSubSp ` W ) $.
    lsmfgcl.p $e |- .(+) = ( LSSum ` W ) $.
    lsmfgcl.d $e |- D = ( W |`s A ) $.
    lsmfgcl.e $e |- E = ( W |`s B ) $.
    lsmfgcl.f $e |- F = ( W |`s ( A .(+) B ) ) $.
    lsmfgcl.w $e |- ( ph -> W e. LMod ) $.
    lsmfgcl.a $e |- ( ph -> A e. U ) $.
    lsmfgcl.b $e |- ( ph -> B e. U ) $.
    lsmfgcl.df $e |- ( ph -> D e. LFinGen ) $.
    lsmfgcl.ef $e |- ( ph -> E e. LFinGen ) $.
    $( The sum of two finitely generated submodules is finitely generated.
       (Contributed by Stefan O'Rear, 24-Jan-2015.) $)
    lsmfgcl $p |- ( ph -> F e. LFinGen ) $=
      ( wcel va vb co cress clfig cv clspn cfv wceq cbs cpw cfn wrex clmod eqid
      cin wb islssfg2 syl2anc mpbid wa adantr cun wss inss1 sseli elpwid lsmsp2
      syl3an 3expb oveq2d unss biimpi syl2an adantl inss2 unfi islssfgi syl3anc
      eqeltrd anassrs oveq2 eleq1d syl5ibcom rexlimdva mpd oveq1 eqeltrid ) AHI
      BCEUCZUDUCZUENAUAUFZIUGUHZUHZBUIZUAIUJUHZUKZULUPZUMZWJUETZADUETZWRRAIUNTZ
      BFTWTWRUQOPWOFBWLIDUALJWLUOZWOUOZURUSUTAWNWSUAWQAWKWQTZVAZIWMCEUCZUDUCZUE
      TZWNWSXEUBUFZWLUHZCUIZUBWQUMZXHAXLXDAGUETZXLSAXACFTXMXLUQOQWOFCWLIGUBMJXB
      XCURUSUTVBXEXKXHUBWQXEXIWQTZVAIWMXJEUCZUDUCZUETZXKXHAXDXNXQAXDXNVAZVAZXPI
      WKXIVCZWLUHZUDUCZUEXSXOYAIUDAXDXNXOYAUIZAXAXDWKWOVDZXNXIWOVDZYCOXDWKWOWQW
      PWKWPULVEZVFVGZXNXIWOWQWPXIYFVFVGZEWKXIWLWOIXCXBKVHVIVJVKXSXAXTWOVDZXTULT
      ZYBUETAXAXROVBXRYIAXDYDYEYIXNYGYHYDYEVAYIWKXIWOVLVMVNVOXRYJAXDWKULTXIULTY
      JXNWQULWKWPULVPZVFWQULXIYKVFWKXIVQVNVOXTWLWOIYBXBXCYBUOVRVSVTWAXKXPXGUEXK
      XOXFIUDXJCWMEWBVKWCWDWEWFWNXGWJUEWNXFWIIUDWMBCEWGVKWCWDWEWFWH $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Noetherian left modules I
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c LNoeM $.

  $( Extend class notation with the class of Noetherian left modules. $)
  clnm $a class LNoeM $.

  ${
    $d i w $.

    $( A left-module is _Noetherian_ iff it is hereditarily finitely generated.
       (Contributed by Stefan O'Rear, 12-Dec-2014.) $)
    df-lnm $a |- LNoeM = { w e. LMod | A. i e. ( LSubSp ` w )
        ( w |`s i ) e. LFinGen } $.
  $}

  ${
    $d w i M $.  $d w i S $.
    islnm.s $e |- S = ( LSubSp ` M ) $.
    $( Property of being a Noetherian left module.  (Contributed by Stefan
       O'Rear, 12-Dec-2014.) $)
    islnm $p |- ( M e. LNoeM <-> ( M e. LMod /\
        A. i e. S ( M |`s i ) e. LFinGen ) ) $=
      ( vw cv cress co clfig wcel clss wral clmod clnm wceq fveq2 eqtr4di oveq1
      cfv eleq1d raleqbidv df-lnm elrab2 ) EFZBFZGHZIJZBUDKSZLCUEGHZIJZBALECMNU
      DCOZUGUJBUHAUKUHCKSAUDCKPDQUKUFUIIUDCUEGRTUAEBUBUC $.
  $}

  ${
    $d i g M $.  $d i g N $.  $d i g S $.  $d i g B $.
    islnm2.b $e |- B = ( Base ` M ) $.
    islnm2.s $e |- S = ( LSubSp ` M ) $.
    islnm2.n $e |- N = ( LSpan ` M ) $.
    $( Property of being a Noetherian left module with finite generation
       expanded in terms of spans.  (Contributed by Stefan O'Rear,
       24-Jan-2015.) $)
    islnm2 $p |- ( M e. LNoeM <-> ( M e. LMod /\
        A. i e. S E. g e. ( ~P B i^i Fin ) i = ( N ` g ) ) ) $=
      ( clnm wcel clmod cv cress co clfig wral wa wceq wrex islnm eqid islssfg2
      cfv cpw cfn cin eqcom rexbii bitrdi ralbidva pm5.32i bitri ) EJKELKZEDMZN
      OZPKZDBQZRUNUOCMFUDZSZCAUEUFUGZTZDBQZRBDEHUAUNURVCUNUQVBDBUNUOBKRUQUSUOSZ
      CVATVBABUOFEUPCUPUBHIGUCVDUTCVAUSUOUHUIUJUKULUM $.
  $}

  ${
    $d M a $.  $d U a $.  $d S a $.  $d R a $.
    $( A Noetherian left module is a left module.  (Contributed by Stefan
       O'Rear, 12-Dec-2014.) $)
    lnmlmod $p |- ( M e. LNoeM -> M e. LMod ) $=
      ( va clnm wcel clmod cv cress co clfig clss cfv wral eqid islnm simplbi )
      ACDAEDABFGHIDBAJKZLPBAPMNO $.

    ${
      lnmlssfg.s $e |- S = ( LSubSp ` M ) $.
      lnmlssfg.r $e |- R = ( M |`s U ) $.
      $( A submodule of Noetherian module is finitely generated.  (Contributed
         by Stefan O'Rear, 1-Jan-2015.) $)
      lnmlssfg $p |- ( ( M e. LNoeM /\ U e. S ) -> R e. LFinGen ) $=
        ( va clnm wcel cv cress co clfig wral clmod islnm simprbi oveq2 eqtr4di
        wceq eleq1d rspcv mpan9 ) DHIZDGJZKLZMIZGBNZCBIAMIZUDDOIUHBGDEPQUGUIGCB
        UECTZUFAMUJUFDCKLAUECDKRFSUAUBUC $.

      $( All submodules of a Noetherian module are Noetherian.  (Contributed by
         Stefan O'Rear, 1-Jan-2015.) $)
      lnmlsslnm $p |- ( ( M e. LNoeM /\ U e. S ) -> R e. LNoeM ) $=
        ( va clnm wcel wa clmod cress co clfig cfv sylan wss wceq cbs eqid clss
        cv wral lnmlmod lsslmod oveq1i simplr adantl ressbas2 ad2antlr sseqtrrd
        lssss ressabs syl2anc eqtrid simpll wb lsslss simprbda lnmlssfg eqeltrd
        syl ralrimiva islnm sylanbrc ) DHIZCBIZJZAKIZAGUBZLMZNIZGAUAOZUCAHIVFDK
        IZVGVIDUDZBCDAFEUEPVHVLGVMVHVJVMIZJZVKDVJLMZNVQVKDCLMZVJLMZVRAVSVJLFUFV
        QVGVJCQZVTVRRVFVGVPUGVQVJASOZCVPVJWBQVHVMVJWBAWBTVMTZULUHVGCWBRZVFVPVGC
        DSOZQWDBCWEDWETZEULCWEADFWFUIVBUJUKCVJDBUMUNUOVQVFVJBIZVRNIVFVGVPUPVHVP
        WGWAVFVNVGVPWGWAJUQVOBVMCVJDAFEWCURPUSVRBVJDEVRTUTUNVAVCVMGAWCVDVE $.
    $}

    $( A Noetherian left module is finitely generated.  (Contributed by Stefan
       O'Rear, 12-Dec-2014.) $)
    lnmfg $p |- ( M e. LNoeM -> M e. LFinGen ) $=
      ( clnm wcel cbs cfv cress co clfig eqid ressid clss lnmlmod lss1 lnmlssfg
      clmod syl mpdan eqeltrrd ) ABCZAADEZFGZAHTABTIZJSTAKEZCZUAHCSAOCUDALUCTAU
      BUCIZMPUAUCTAUEUAINQR $.
  $}

  ${
    $d a b .0. $.  $d a b B $.  $d a b D $.  $d a b F $.  $d a b K $.
    $d a b ph $.  $d a b S $.  $d a b T $.  $d a b U $.  $d a b .(+) $.
    kercvrlsm.u $e |- U = ( LSubSp ` S ) $.
    kercvrlsm.p $e |- .(+) = ( LSSum ` S ) $.
    kercvrlsm.z $e |- .0. = ( 0g ` T ) $.
    kercvrlsm.k $e |- K = ( `' F " { .0. } ) $.
    kercvrlsm.b $e |- B = ( Base ` S ) $.
    kercvrlsm.f $e |- ( ph -> F e. ( S LMHom T ) ) $.
    kercvrlsm.d $e |- ( ph -> D e. U ) $.
    kercvrlsm.cv $e |- ( ph -> ( F " D ) = ran F ) $.
    $( The domain of a linear function is the subspace sum of the kernel and
       any subspace which covers the range.  (Contributed by Stefan O'Rear,
       24-Jan-2015.)  (Revised by Stefan O'Rear, 6-May-2015.) $)
    kercvrlsm $p |- ( ph -> ( K .(+) D ) = B ) $=
      ( wcel syl va vb wss clmod clmhm lmhmlmod1 lmhmkerlss lsmcl syl3anc lssss
      co cv wa cfv wceq wrex cima crn wfn cbs wf eqid lmhmf ffnd fnfvelrn sylan
      adantr eleqtrrd wb fvelimab syl2anc mpbid wi cplusg lmodgrp simprl sselda
      csg cgrp adantrl grpnpcan ad2antrr eqcom cghm lmghm bitrid biimpa simplrr
      ghmeqker lsmelvalix syl32anc eqeltrrd ex anassrs rexlimdva mpd eqelssd )
      AUAICDUKZBAWRGSZWRBUCAEUDSZIGSZCGSZWSAHEFUEUKSZWTPEFHUFTZAXCXAPEFGHIJNMKU
      GTZQDGICEKLUHUIGWRBEOKUJTAUAULZBSZUMZUBULZHUNZXFHUNZUOZUBCUPZXFWRSZXHXKHC
      UQZSZXMXHXKHURZXOAHBUSZXGXKXQSABFUTUNZHAXCBXSHVAPBXSEFHOXSVBVCTVDZBXFHVEV
      FAXOXQUOXGRVGVHXHXRCBUCZXPXMVIAXRXGXTVGAYAXGAXBYAQGCBEOKUJTZVGUBBCXKHVJVK
      VLXHXLXNUBCAXGXICSZXLXNVMAXGYCUMZUMZXLXNYEXLUMZXFXIEVRUNZUKZXIEVNUNZUKZXF
      WRYEYJXFUOZXLYEEVSSZXGXIBSZYKAYLYDAWTYLXDEVOTVGAXGYCVPZAYCYMXGACBXIYBVQVT
      ZBYIEYGXFXIOYIVBZYGVBZWAUIVGYFWTIBUCZYAYHISZYCYJWRSAWTYDXLXDWBAYRYDXLAXAY
      RXEGIBEOKUJTWBAYAYDXLYBWBYEXLYSXLXKXJUOZYEYSXJXKWCYEHEFWDUKSZXGYMYTYSVIAU
      UAYDAXCUUAPEFHWETVGYNYOBEFXFHIYGXIJOMNYQWIUIWFWGAXGYCXLWHBYIDICEUDYHXIOYP
      LWJWKWLWMWNWOWPWQ $.
  $}

  ${
    $d ph x $.  $d X x $.  $d S x $.  $d A x $.  $d U x $.  $d Y x $.
    $d T x $.  $d F x $.
    lmhmfgima.y $e |- Y = ( T |`s ( F " A ) ) $.
    lmhmfgima.x $e |- X = ( S |`s A ) $.
    lmhmfgima.u $e |- U = ( LSubSp ` S ) $.
    lmhmfgima.xf $e |- ( ph -> X e. LFinGen ) $.
    lmhmfgima.a $e |- ( ph -> A e. U ) $.
    lmhmfgima.f $e |- ( ph -> F e. ( S LMHom T ) ) $.
    $( A homomorphism maps finitely generated submodules to finitely generated
       submodules.  (Contributed by Stefan O'Rear, 24-Jan-2015.) $)
    lmhmfgima $p |- ( ph -> Y e. LFinGen ) $=
      ( cress clfig cfv cfn wcel eqid vx cima co cv clspn wceq cbs cpw cin wrex
      clmod wb clmhm lmhmlmod1 syl islssfg2 syl2anc mpbid wa inss1 sseli elpwid
      wss lmhmlsp syl2an oveq2d lmhmlmod2 adantr crn imassrn wf lmhmf frnd cres
      sstrid wfo inss2 wfun cdm ffund fdmd sseqtrrd fores fofi islssfgi syl3anc
      adantl eqeltrd imaeq2 eleq1d syl5ibcom rexlimdva mpd eqeltrid ) AHDFBUBZO
      UCZPIAUAUDZCUEQZQZBUFZUACUGQZUHZRUIZUJZWPPSZAGPSZXDLACUKSZBESXFXDULAFCDUM
      UCSZXGNCDFUNUOMXAEBWRCGUAJKWRTZXATZUPUQURAWTXEUAXCAWQXCSZUSZDFWSUBZOUCZPS
      WTXEXLXNDFWQUBZDUEQZQZOUCZPXLXMXQDOAXHWQXAVCZXMXQUFXKNXKWQXAXCXBWQXBRUTVA
      VBZCDWQFWRXPXAXJXIXPTZVDVEVFXLDUKSZXODUGQZVCZXORSZXRPSAYBXKAXHYBNCDFVGUOV
      HAYDXKAXOFVIYCFWQVJAXAYCFAXHXAYCFVKNXAYCCDFXJYCTZVLUOZVMVOVHXLWQRSZWQXOFW
      QVNZVPZYEXKYHAXCRWQXBRVQVAWGXLFVRZWQFVSZVCYJAYKXKAXAYCFYGVTVHXLWQXAYLXKXS
      AXTWGAYLXAUFXKAXAYCFYGWAVHWBWQFWCUQWQXOYIWDUQXOXPYCDXRYAYFXRTWEWFWHWTXNWP
      PWTXMWODOWSBFWIVFWJWKWLWMWN $.
  $}

  ${
    $d T a $.  $d S a $.  $d F a $.  $d B a $.
    lnmepi.b $e |- B = ( Base ` T ) $.
    $( Epimorphic images of Noetherian modules are Noetherian.  (Contributed by
       Stefan O'Rear, 24-Jan-2015.) $)
    lnmepi $p |- ( ( F e. ( S LMHom T ) /\ S e. LNoeM /\ ran F = B ) ->
        T e. LNoeM ) $=
      ( va clmhm wcel clnm crn wceq cress clfig clss cfv 3ad2ant1 cima sylanbrc
      co eqid w3a clmod cv wral lmhmlmod2 wa ccnv cbs wfo wss lmhmf simp3 dffo2
      lssss foimacnv syl2an oveq2d simpl2 lmhmpreima 3ad2antl1 lnmlssfg syl2anc
      wf simpl1 lmhmfgima eqeltrrd ralrimiva islnm ) DBCGSHZBIHZDJAKZUAZCUBHZCF
      UCZLSZMHZFCNOZUDCIHVIVJVMVKBCDUEPVLVPFVQVLVNVQHZUFZCDDUGVNQZQZLSZVOMVSWAV
      NCLVLBUHOZADUIZVNAUJWAVNKVRVLWCADVCZVKWDVIVJWEVKWCABCDWCTEUKPVIVJVKULWCAD
      UMRVQVNACEVQTZUNWCAVNDUOUPUQVSVTBCBNOZDBVTLSZWBWBTWHTZWGTZVSVJVTWGHZWHMHV
      IVJVKVRURVIVJVRWKVKBCVNDWGVQWJWFUSUTZWHWGVTBWJWIVAVBWLVIVJVKVRVDVEVFVGVQF
      CWFVHR $.
  $}

  ${
    $d F a b $.  $d S a b $.  $d T a b $.  $d K a b $.  $d U a b $.
    $d V a b $.
    lmhmfgsplit.z $e |- .0. = ( 0g ` T ) $.
    lmhmfgsplit.k $e |- K = ( `' F " { .0. } ) $.
    lmhmfgsplit.u $e |- U = ( S |`s K ) $.
    lmhmfgsplit.v $e |- V = ( T |`s ran F ) $.
    $( If the kernel and range of a homomorphism of left modules are finitely
       generated, then so is the domain.  (Contributed by Stefan O'Rear,
       1-Jan-2015.)  (Revised by Stefan O'Rear, 6-May-2015.) $)
    lmhmfgsplit $p |- ( ( F e. ( S LMHom T ) /\ U e. LFinGen /\
          V e. LFinGen ) -> S e. LFinGen ) $=
      ( va co wcel clfig cfn cfv wceq wa eqid vb clmhm w3a clspn crn wrex simp3
      cv cpw clmod clss lmhmlmod2 3ad2ant1 lmhmrnlss islssfg syl2anc mpbid cima
      wb cbs cin wfn wss wf simpl1 lmhmf 3syl ad2antrl simprrl fipreima syl3anc
      ffn elpwi clsm cress simpll1 lmhmlmod1 ad2antrr inss1 sseli lspcl lmhmlsp
      syl fveq2 ad2antll 3expa 3eqtrd kercvrlsm oveq2d ressid eqtr2d lmhmkerlss
      simp2rr simpll2 inss2 islssfgi lsmfgcl eqeltrd rexlimddv ) DABUBMNZCONZFO
      NZUCZLUHZPNZXDBUDQZQZDUEZRZSZAONZLXHUIZXCXBXJLXLUFZWTXAXBUGXCBUJNZXHBUKQZ
      NZXBXMUSWTXAXNXBABDULUMWTXAXPXBABDUNUMXOXHXFBFLKXOTXFTZUOUPUQXCXDXLNZXJSZ
      SZDUAUHZURZXDRZXKUAAUTQZUIZPVAZXTDYDVBZXDXHVCZXEYCUAYFUFXTWTYDBUTQZDVDYGW
      TXAXBXSVEYDYIABDYDTZYITVFYDYIDVLVGXRYHXCXJXDXHVMVHXCXRXEXIVIXDYDDUAVJVKXT
      YAYFNZYCSZSZAAEYAAUDQZQZAVNQZMZVOMZOYMYRAYDVOMZAYMYQYDAVOYMYDYOYPABAUKQZD
      EGYTTZYPTZHIYJWTXAXBXSYLVPZYMAUJNZYAYDVCZYOYTNXCUUDXSYLWTXAUUDXBABDVQUMZV
      RZYKUUEXTYCYKYAYENUUEYFYEYAYEPVSVTYAYDVMWCVHZYTYAYNYDAYJUUAYNTZWAUPZYMDYO
      URZYBXFQZXGXHYMWTUUEUUKUULRUUCUUHABYADYNXFYDYJUUIXQWBUPYCUULXGRXTYKYBXDXF
      WDWEXCXSYLXIXEXIXRXCYLWMWFWGWHWIXCYSARZXSYLXCUUDUUMUUFYDAUJYJWJWCVRWKYMEY
      OCYPYTAYOVOMZYRAUUAUUBJUUNTZYRTUUGXCEYTNZXSYLWTXAUUPXBABYTDEGIHUUAWLUMVRU
      UJWTXAXBXSYLWNYMUUDUUEYAPNZUUNONUUGUUHYKUUQXTYCYFPYAYEPWOVTVHYAYNYDAUUNUU
      IYJUUOWPVKWQWRWSWS $.

    $( If the kernel and range of a homomorphism of left modules are
       Noetherian, then so is the domain.  (Contributed by Stefan O'Rear,
       1-Jan-2015.)  (Revised by Stefan O'Rear, 12-Jun-2015.) $)
    lmhmlnmsplit $p |- ( ( F e. ( S LMHom T ) /\ U e. LNoeM /\ V e. LNoeM ) ->
        S e. LNoeM ) $=
      ( va co wcel cress clfig eqid cin cvv syl clmhm clnm w3a cv clss cfv wral
      clmod lmhmlmod1 3ad2ant1 wa cres ccnv csn crn reslmhm 3ad2antl1 cnvresima
      cima eqcomi ineq1i incom 3eqtri oveq2i wss vex inss1 ressabs mp2an oveq1i
      wceq simpl1 cnvexg imaexg eqeltrid inss2 sylancl eqtrid simpl2 lmhmkerlss
      eqtr4id adantr simpr lssincl syl3anc wb lsslss syl2anc mpbir2and lnmlssfg
      a1i eqeltrd resss rnss ax-mp dfss2 eqtr2i rnexg resexg ressress lmhmrnlss
      mpbi simpl3 lmhmlmod2 lmhmfgsplit ralrimiva islnm sylanbrc ) DABUAMZNZCUB
      NZFUBNZUCZAUHNZALUDZOMZPNZLAUEUFZUGAUBNXJXKXNXLABDUIUJZXMXQLXRXMXOXRNZUKZ
      DXOULZXPBUAMNZXPYBUMGUNZUSZOMZPNBYBUOZOMZPNXQXJXKXTYCXLXPABXRDXOXRQZXPQUP
      UQZYAYFCXOERZOMZPYAYFXPYKOMZYLYEYKXPOYEDUMZYDUSZXOREXORYKXOYDDURYOEXOEYOI
      UTVAEXOVBVCVDYAYMAYKOMZYLXOSNYKXOVEYMYPVKLVFXOEVGXOYKASVHVIYAYLAEOMZYKOMZ
      YPCYQYKOJVJYAESNZYKEVEZYRYPVKYAXJYSXJXKXLXTVLZXJEYOSIXJYNSNYOSNDXIVMYNYDS
      VNTVOTXOEVPZEYKASVHVQVRWAVRYAXKYKCUEUFZNZYLPNXJXKXLXTVSYAUUDYKXRNZYTYAXNX
      TEXRNZUUEXMXNXTXSWBZXMXTWCYAXJUUFUUAABXRDEGIHYIVTTZXRXOEAYIWDWEYTYAUUBWKY
      AXNUUFUUDUUEYTUKWFUUGUUHXRUUCEYKACJYIUUCQZWGWHWIYLUUCYKCUUIYLQWJWHWLYAYHF
      YGOMZPYAXJYHUUJVKUUAXJYHBDUOZYGRZOMZUUJYGUULBOUULYGUUKRZYGUUKYGVBYGUUKVEZ
      UUNYGVKYBDVEUUODXOWMYBDWNWOZYGUUKWPXBWQVDXJUUJBUUKOMZYGOMZUUMFUUQYGOKVJXJ
      UUKSNYGSNZUURUUMVKDXIWRXJYBSNUUSDXOXIWSYBSWRTUUKYGBSSWTWHVRWATYAXLYGFUEUF
      ZNZUUJPNXJXKXLXTXCYAUVAYGBUEUFZNZUUOYAYCUVCYJXPBYBXATUUOYAUUPWKYABUHNZUUK
      UVBNZUVAUVCUUOUKWFYAXJUVDUUAABDXDTYAXJUVEUUAABDXATUVBUUTUUKYGBFKUVBQUUTQZ
      WGWHWIUUJUUTYGFUVFUUJQWJWHWLXPBYFYBYEYHGHYEQYFQYHQXEWEXFXRLAYIXGXH $.
  $}

  ${
    $d R a $.  $d S a $.
    $( Noetherian is an invariant property of modules.  (Contributed by Stefan
       O'Rear, 25-Jan-2015.) $)
    lnmlmic $p |- ( R ~=m S -> ( R e. LNoeM <-> S e. LNoeM ) ) $=
      ( va clmic wbr cv co wcel clnm clmhm crn cbs cfv wceq adantr simpr lnmepi
      wa eqid syl3anc clmim wex wb c0 wne brlmic n0 bitri lmimlmhm wf1o lmimf1o
      wfo f1ofo forn 3syl islmim2 simprbi cdm dfdm4 syl eqtr3id impbida exlimiv
      ccnv f1odm sylbi ) ABDEZCFZABUAGZHZCUBZAIHZBIHZUCZVGVIUDUEVKABUFCVIUGUHVJ
      VNCVJVLVMVJVLRVHABJGHZVLVHKBLMZNZVMVJVOVLABVHUIOVJVLPVJVQVLVJALMZVPVHUJZV
      RVPVHULVQVRVPABVHVRSZVPSZUKZVRVPVHUMVRVPVHUNUOOVPABVHWAQTVJVMRZVHVDZBAJGH
      ZVMWDKZVRNVLVJWEVMVJVOWEABVHUPUQOVJVMPWCWFVHURZVRVHUSVJWGVRNZVMVJVSWHWBVR
      VPVHVEUTOVAVRBAWDVTQTVBVCVF $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Addenda for structure powers
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d A a x y $.  $d B a x y $.  $d C x y $.  $d D a x y $.  $d E x y $.
    $d F a $.  $d G x y $.  $d K a x $.  $d L a x $.  $d R a x y $.
    $d V a x y $.  $d .0. x y $.
    pwssplit4.e $e |- E = ( R ^s ( A u. B ) ) $.
    pwssplit4.g $e |- G = ( Base ` E ) $.
    pwssplit4.z $e |- .0. = ( 0g ` R ) $.
    pwssplit4.k $e |- K = { y e. G | ( y |` A ) = ( A X. { .0. } ) } $.
    pwssplit4.f $e |- F = ( x e. K |-> ( x |` B ) ) $.
    pwssplit4.c $e |- C = ( R ^s A ) $.
    pwssplit4.d $e |- D = ( R ^s B ) $.
    pwssplit4.l $e |- L = ( E |`s K ) $.
    $( Splitting for structure powers 4: maps isomorphically onto the other
       half.  (Contributed by Stefan O'Rear, 25-Jan-2015.) $)
    pwssplit4 $p |- ( ( R e. LMod /\ ( A u. B ) e. V /\ ( A i^i B ) = (/) ) ->
          F e. ( L LMIso D ) ) $=
      ( va clmod wcel cun cin c0 wceq w3a clmhm co cbs cfv wf1o clmim cres cmpt
      cv wss csn cxp crab ssrab2 eqsstri resmpt ax-mp eqtr4i clss a1i pwssplit3
      ssun2 eqid syld3an3 c0g cmnd cvv cgrp simp1 lmodgrp 3syl ssun1 ssexg mpan
      grpmnd 3ad2ant2 pws0g syl2anc eqeq2d rabbidv eqtrid ccnv cima fvex eqcomi
      mptiniseg lmhmkerlss syl eqeltrd reslmhm eqeltrid wf1 wi wral wa fvtresfn
      crn eqcomd eqeqan12rd reseq1 eqeq1d elrab2 uneq12 resundi xpundir 3eqtr4g
      adantll adantl wfn simpl1 simp2 adantr simprll pwselbas ffn fnresdm eqtrd
      wf 3adant3 wb mpbird lmhmf pwselbasb uncom fnresdisj uneq12d resundir un0
      mp2b sylanbrc csubg pwslmod lsssubg subg0 exp32 biimtrid sylbid ralrimiva
      3eqtr3d imp cghm lmghm ressbas2 ghmf1 frn biimpa fvexi mndidcl snssd fssd
      fconst incom simp3 fun syl21anc unidm feq23i sylib simpl3 fnconstg eqtr2i
      resexd fvmptd3 biimpi 3ad2ant3 eqtrdi fnfvelrn eqeltrrd eqelssd dff1o5
      mpbid islmim ) GUDUEZCDUFZMUEZCDUGZUHUIZUJZILFUKULZUEZKFUMUNZIUOZILFUPULU
      EUWHIAJAUSZDUQZURZKUQZUWIIAKUWNURZUWPSKJUTZUWPUWQUIKBUSZCUQZCNVAZVBZUIZBJ
      VCZJRUXCBJVDVEZAJKUWNVFVGVHUWHUWOHFUKULUEZKHVIUNZUEZUWPUWIUEUWCUWEUWGDUWD
      UTZUXFUXIUWHDCVLZVJAJUWKUWDUWODGMHFOUAPUWKVMZUWOVMVKVNUWHKUWTEVOUNZUIZBJV
      CZUXGUWHKUXDUXNRUWHUXCUXMBJUWHUXBUXLUWTUWHGVPUEZCVQUEZUXBUXLUIUWHUWCGVRUE
      UXOUWCUWEUWGVSZGVTGWEWAZUWEUWCUXPUWGCUWDUTZUWEUXPCDWBZCUWDMWCWDWFGCVQENTQ
      WGWHWIWJWKUWHBJUWTURZHEUKULUEZUXNUXGUEUWCUWEUWGUXSUYBUXSUWHUXTVJBJEUMUNZU
      WDUYACGMHEOTPUYCVMUYAVMZVKVNHEUXGUYAUXNUXLUYAWLUXLVAWMZUXNUXLVQUEUYEUXNUI
      EVOWNBJUWTUXLUYAVQUYDWPVGWOUXLVMUXGVMZWQWRWSZLHFUXGUWOKUYFUBWTWHXAZUWHKUW
      KIXBZIXGZUWKUIUWLUWHUYIUCUSZIUNZFVOUNZUIZUYKLVOUNZUIZXCZUCKXDZUWHUYQUCKUW
      HUYKKUEZXEUYNUYKDUQZDUXAVBZUIZUYPUYSUWHUYLUYTUYMVUAAKIDUYKSXFUWHVUAUYMUWH
      UXODVQUEZVUAUYMUIUXRUWEUWCVUCUWGUXIUWEVUCUXJDUWDMWCWDWFZGDVQFNUAQWGWHXHXI
      UWHUYSVUBUYPXCZUYSUYKJUEZUYKCUQZUXBUIZXEZUWHVUEUXCVUHBUYKJKUWSUYKUIUWTVUG
      UXBUWSUYKCXJXKRXLUWHVUIVUBUYPUWHVUIVUBXEZXEZUYKUWDUQZUWDUXAVBZUYKUYOVUJVU
      LVUMUIZUWHVUHVUBVUNVUFVUHVUBXEVUGUYTUFUXBVUAUFVULVUMVUGUXBUYTVUAXMUYKCDXN
      CDUXAXOXPXQXRVUKUWDGUMUNZUYKYHUYKUWDXSVULUYKUIVUKVUOGUWDJUDUYKHMOVUOVMZPU
      WCUWEUWGVUJXTUWHUWEVUJUWCUWEUWGYAZYBUWHVUFVUHVUBYCYDUWDVUOUYKYEUWDUYKYFWA
      UWHVUMUYOUIVUJUWHVUMHVOUNZUYOUWHUXOUWEVUMVURUIUXRVUQGUWDMHNOQWGWHUWHKHUUA
      UNUEZVURUYOUIUWHHUDUEZUXHVUSUWCUWEVUTUWGGUWDMHOUUBYIUYGUXGKHUYFUUCWHKHLVU
      RUBVURVMUUDWRYGYBUUIUUEUUFUUJUUGUUHUWHUWJILFUUKULUEUYIUYRYJUYHLFIUULUCKUW
      KLFIUYOUYMUWRKLUMUNZUIUXEKJLHUBPUUMVGZUXKUYOVMUYMVMUUNWAYKUWHUCUYJUWKUWHU
      WJVVAUWKIYHUYJUWKUTUYHVVAUWKLFIVVAVMUXKYLVVAUWKIUUOWAUWHUYKUWKUEZXEZUYKUX
      BUFZIUNZUYKUYJVVDVVFVVEDUQZUYKVVDAVVEUWNVVGKIVQSUWMVVEDXJVVDVVEJUEZVVECUQ
      ZUXBUIZVVEKUEZVVDVVHUWDVUOVVEYHZVVDDCUFZVUOVUOUFZVVEYHZVVLVVDDVUOUYKYHZCV
      UOUXBYHDCUGZUHUIZVVOUWHVVCVVPUWHUWCVUCVVCVVPYJUXQVUDVUOGDUWKUDUYKFVQUAVUP
      UXKYMWHUUPZVVDCUXAVUOUXBCUXAUXBYHZVVDCNNGVOQUUQZUVAZVJVVDNVUOVVDUXONVUOUE
      UWHUXOVVCUXRYBVUOGNVUPQUURWRUUSUUTUWHVVRVVCUWHVVQUWFUHDCUVBZUWCUWEUWGUVCW
      KYBDCVUOVUOUYKUXBUVDUVEVVMVVNUWDVUOVVEDCYNVUOUVFUVGUVHUWHVVHVVLYJZVVCUWCU
      WEVWDUWGVUOGUWDJUDVVEHMOVUPPYMYIYBYKZVVDVUGUXBCUQZUFUHUXBUFZVVIUXBVVDVUGU
      HVWFUXBVVDVVRVUGUHUIZVVDVVQUWFUHVWCUWCUWEUWGVVCUVIWKVVDVVPUYKDXSZVVRVWHYJ
      VVSDVUOUYKYEZDCUYKYOWAUWAVWFUXBUIZVVDNVQUEUXBCXSZVWKVWACNVQUVJCUXBYFYSVJY
      PUYKUXBCYQVWGUXBUHUFUXBUHUXBYNUXBYRUVKXPUXCVVJBVVEJKUWSVVEUIUWTVVIUXBUWSV
      VECXJXKRXLYTZVVDVVEDJVWEUVLUVMVVDVVGUYTUXBDUQZUFZUYKUYKUXBDYQVVDVWOUYKUHU
      FUYKVVDUYTUYKVWNUHVVDVVPVWIUYTUYKUIVVSVWJDUYKYFWAUWHVWNUHUIZVVCUWGUWCVWPU
      WEUWGVWPVVTVWLUWGVWPYJVWBCUXAUXBYECDUXBYOYSUVNUVOYBYPUYKYRUVPWKYGVVDIKXSZ
      VVKVVFUYJUEUWHVWQVVCUWHUWJKUWKIYHVWQUYHKUWKLFIVVBUXKYLKUWKIYEWAYBVWMKVVEI
      UVQWHUVRUVSKUWKIUVTYTKUWKLFIVVBUXKUWBYT $.
  $}

  ${
    $d B a b $.  $d W a b $.
    filnm.b $e |- B = ( Base ` W ) $.
    $( Finite left modules are Noetherian.  (Contributed by Stefan O'Rear,
       24-Jan-2015.) $)
    filnm $p |- ( ( W e. LMod /\ B e. Fin ) -> W e. LNoeM ) $=
      ( va vb clmod wcel cfn wa cv cfv wceq cpw cin wrex clss wral eqid syl2anc
      clspn clnm simpl wss lssss adantl velpw sylibr simplr elind lspid adantlr
      ssfi eqcomd fveq2 rspceeqv ralrimiva islnm2 sylanbrc ) BFGZAHGZIZUSDJZEJZ
      BTKZKZLEAMZHNZOZDBPKZQBUAGUSUTUBVAVHDVIVAVBVIGZIZVBVGGVBVBVDKZLVHVKVFHVBV
      KVBAUCZVBVFGVJVMVAVIVBABCVIRZUDUEZDAUFUGVKUTVMVBHGUSUTVJUHVOAVBULSUIVKVLV
      BUSVJVLVBLUTVIVBVDBVNVDRZUJUKUMEVBVGVEVLVBVCVBVDUNUOSUPAVIEDBVDCVNVPUQUR
      $.
  $}

  ${
    pwslnmlem0.y $e |- Y = ( W ^s (/) ) $.
    $( Zeroeth powers are Noetherian.  (Contributed by Stefan O'Rear,
       24-Jan-2015.) $)
    pwslnmlem0 $p |- ( W e. LMod -> Y e. LNoeM ) $=
      ( clmod wcel cbs cfv cfn clnm cvv 0ex pwslmod mpan2 cmap wceq eqid pwsbas
      c0 co c1o csn fvex map0e ax-mp df1o2 eqtri snfi eqeltri eqeltrrdi syl2anc
      filnm ) ADEZBDEZBFGZHEBIEULRJEZUMKARJBCLMULUNAFGZRNSZHULUOUQUNOKUPARDJBCU
      PPQMUQRUAZHUQTURUPJEUQTOAFUBUPJUCUDUEUFRUGUHUIUNBUNPUKUJ $.
  $}

  ${
    $d Y x $.  $d W i x $.
    pwslnmlem1.y $e |- Y = ( W ^s { i } ) $.
    $( First powers are Noetherian.  (Contributed by Stefan O'Rear,
       24-Jan-2015.) $)
    pwslnmlem1 $p |- ( W e. LNoeM -> Y e. LNoeM ) $=
      ( vx clnm wcel cbs cfv cv csn cxp cmpt clmhm co crn wceq clmod cvv eqid
      lnmlmod vsnex pwsdiaglmhm sylancl id wf1o pwssnf1o elvd f1ofo forn lnmepi
      wfo 3syl syl3anc ) BFGZEBHIZAJZKZEJKLMZBCNOGZUOUSPCHIZQZCFGUOBRGURSGUTBUA
      AUBEUPBUSURSCDUPTZUSTZUCUDUOUEUOUPVAUSUFZUPVAUSULVBUOVEAEUPVABUSUQFSCDVCV
      DVATZUGUHUPVAUSUIUPVAUSUJUMVABCUSVFUKUN $.
  $}

  ${
    $d X x y $.  $d A x y $.  $d W x y $.  $d Z x y $.  $d B x y $.
    $d Y x y $.  $d ph x y $.
    pwslnmlem2.a $e |- A e. _V $.
    pwslnmlem2.b $e |- B e. _V $.
    pwslnmlem2.x $e |- X = ( W ^s A ) $.
    pwslnmlem2.y $e |- Y = ( W ^s B ) $.
    pwslnmlem2.z $e |- Z = ( W ^s ( A u. B ) ) $.
    pwslnmlem2.w $e |- ( ph -> W e. LMod ) $.
    pwslnmlem2.dj $e |- ( ph -> ( A i^i B ) = (/) ) $.
    pwslnmlem2.xn $e |- ( ph -> X e. LNoeM ) $.
    pwslnmlem2.yn $e |- ( ph -> Y e. LNoeM ) $.
    $( A sum of powers is Noetherian.  (Contributed by Stefan O'Rear,
       25-Jan-2015.) $)
    pwslnmlem2 $p |- ( ph -> Z e. LNoeM ) $=
      ( vx wcel clnm eqid vy cbs cfv cv cres cmpt clmhm ccnv c0g csn cima cress
      crn clmod cun cvv wss unex a1i ssun1 pwssplit3 syl3anc cxp wceq crab fvex
      mptiniseg ax-mp cmnd cgrp lmodgrp grpmnd 3syl pws0g sylancl eqcomd eqeq2d
      co rabbidv eqtrid oveq2d clmim clmic wbr wb cin pwssplit4 brlmici lnmlmic
      c0 mpbird eqeltrd wfo pwssplit1 forn syl ressid eqtrd lmhmlnmsplit ) AQGU
      BUCZQUDBUEZUFZGEUGVRRZGXBUHEUIUCZUJUKZULVRZSREXBUMZULVRZSRGSRADUNRZBCUOZU
      PRZBXJUQZXCMXKABCHIURUSZXLABCUTUSZQWTEUBUCZXJXBBDUPGELJWTTZXOTZXBTZVAVBAX
      FGXABDUIUCZUJVCZVDZQWTVEZULVRZSAXEYBGULAXEXAXDVDZQWTVEZYBXDUPRXEYEVDEUIVF
      QWTXAXDXBUPXRVGVHAYDYAQWTAXDXTXAAXTXDADVIRZBUPRXTXDVDAXIDVJRYFMDVKDVLVMZH
      DBUPEXSJXSTZVNVOVPVQVSVTWAAYCSRZFSRZPAUAYBUAUDCUEUFZYCFWBVRRZYCFWCWDYIYJW
      EAXIXKBCWFWJVDYLMXMNUAQBCEFDGYKWTYBYCUPXSLXPYHYBTYKTJKYCTWGVBYCFYKWHYCFWI
      VMWKWLAXHESAXHEXOULVRZEAXGXOEULAWTXOXBWMZXGXOVDAYFXKXLYNYGXMXNQWTXOXJXBBD
      UPGELJXPXQXRWNVBWTXOXBWOWPWAAESRYMEVDOXOESXQWQWPWROWLGEXFXBXEXHXDXDTXETXF
      TXHTWSVB $.
  $}

  ${
    $d W a b c $.  $d I a b c $.
    pwslnm.y $e |- Y = ( W ^s I ) $.
    $( Finite powers of Noetherian modules are Noetherian.  (Contributed by
       Stefan O'Rear, 24-Jan-2015.) $)
    pwslnm $p |- ( ( W e. LNoeM /\ I e. Fin ) -> Y e. LNoeM ) $=
      ( va vb vc clnm wcel wa cpws co cv wi c0 wceq oveq2 eleq1d imbi2d eqid wn
      cfn csn cun weq clmod lnmlmod pwslnmlem0 syl wel vex ad2antrl cin biimpri
      vsnex disjsn ad2antlr pwslnmlem1 pwslnmlem2 exp32 a2d findcard2s eqeltrid
      simprr impcom ) BHIZAUBIZJCBAKLZHDVGVFVHHIZVFBEMZKLZHIZNVFBOKLZHIZNVFBFMZ
      KLZHIZNVFBVOGMZUCZUDZKLZHIZNVFVINEFGAVJOPZVLVNVFWCVKVMHVJOBKQRSEFUEZVLVQV
      FWDVKVPHVJVOBKQRSVJVTPZVLWBVFWEVKWAHVJVTBKQRSVJAPZVLVIVFWFVKVHHVJABKQRSVF
      BUFIZVNBUGZBVMVMTUHUIVOUBIZGFUJUAZJZVFVQWBWKVFVQWBWKVFVQJZJVOVSBVPBVSKLZW
      AFUKGUOVPTWMTZWATVFWGWKVQWHULWJVOVSUMOPZWIWLWOWJVOVRUPUNUQWKVFVQVDVFWMHIW
      KVQGBWMWNURULUSUTVAVBVEVC $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Every set admits a group structure iff choice
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d a b c d B $.  $d a b c d C $.  $d a b c d D $.  $d a b c d .+ $.
    $d a b c d ph $.  $d b c A $.  $d a c d x y B $.  $d x y C $.  $d x y D $.
    $d x y .+ $.  $d x ph $.
    unxpwdom3.av $e |- ( ph -> A e. V ) $.
    unxpwdom3.bv $e |- ( ph -> B e. W ) $.
    unxpwdom3.dv $e |- ( ph -> D e. X ) $.
    unxpwdom3.ov $e |- ( ( ph /\ a e. C /\ b e. D ) ->
        ( a .+ b ) e. ( A u. B ) ) $.
    unxpwdom3.lc $e |- ( ( ( ph /\ a e. C ) /\ ( b e. D /\ c e. D ) ) ->
        ( ( a .+ b ) = ( a .+ c ) <-> b = c ) ) $.
    unxpwdom3.rc $e |- ( ( ( ph /\ d e. D ) /\ ( a e. C /\ c e. C ) ) ->
        ( ( c .+ d ) = ( a .+ d ) <-> c = a ) ) $.
    unxpwdom3.ni $e |- ( ph -> -. D ~<_ A ) $.
    $( Weaker version of ~ unxpwdom where a function is required only to be
       cancellative, not an injection. ` D ` and ` B ` are to be thought of as
       "large" "horizonal" sets, the others as "small".  Because the operator
       is row-wise injective, but the whole row cannot inject into ` A ` , each
       row must hit an element of ` B ` ; by column injectivity, each row can
       be identified in at least one way by the ` B ` element that it hits and
       the column in which it is hit.  (Contributed by Stefan O'Rear,
       8-Jul-2015.) _MOVABLE_ $)
    unxpwdom3 $p |- ( ph -> C ~<_* ( D X. B ) ) $=
      ( vx vy cxp cvv cv c1st cfv co c2nd wceq crio xpexd wcel wa simprr simplr
      wrex weq wb an4s anassrs adantlrr riota5 eqeq2 riotabidv rspceeqv syl2anc
      eqcomd wn wral cdom wbr adantr ad2antrr wi oveq2 eleq1d notbid adantl cun
      rspcv wo 3expa elun sylib orcomd ord syld impancom dom2d mpd mtand dfrex2
      sylibr reximddv cop vex op1std oveq2d op2ndd eqeq12d eqeq2d rexxp wdomd
      ex ) AJUADECUCZUDLUEZUAUEZUFUGZFUHZXHUIUGZUJZLDUKZAECIHPOULAJUEZDUMZUNZXN
      XGMUEZFUHZUBUEZUJZLDUKZUJZUBCUQZMEUQXNXMUJZUAXFUQXPXNXQFUHZCUMZYCMEXPXQEU
      MZYFUNZUNZYFXNXRYEUJZLDUKZUJYCXPYGYFUOYIYKXNYIYJLDXNAXOYHUPXPYGXGDUMZYJLJ
      URUSZYFXPYGYLYMAYGXOYLYMSUTVAVBVCVHUBYECYAYKXNXSYEUJXTYJLDXSYEXRVDVEVFVGX
      PYFVIZMEVJZVIYFMEUQXPYOEBVKVLZAYPVIXOTVMXPYOUNZBGUMZYPAYRXOYONVNYQKLEBXNK
      UEZFUHZXNXGFUHZGXPYSEUMZYOYTBUMZXPUUBUNZYOYTCUMZVIZUUCUUBYOUUFVOXPYNUUFMY
      SEMKURZYFUUEUUGYEYTCXQYSXNFVPVQVRWAVSUUDUUEUUCUUDUUCUUEUUDYTBCVTUMZUUCUUE
      WBAXOUUBUUHQWCYTBCWDWEWFWGWHWIXPUUBXGEUMUNZYTUUAUJKLURUSZVOYOXPUUIUUJRXEV
      MWJWKWLYFMEWMWNWOYDYBUAMUBECXHXQXSWPUJZXMYAXNUUKXLXTLDUUKXJXRXKXSUUKXIXQX
      GFXQXSXHMWQZUBWQZWRWSXQXSXHUULUUMWTXAVEXBXCWNXD $.
  $}

  ${
    $d x y A $.  $d x S $.  $d x y V $.
    pwfi2f1o.s $e |- S = { y e. ( 2o ^m A ) | y finSupp (/) } $.
    pwfi2f1o.f $e |- F = ( x e. S |-> ( `' x " { 1o } ) ) $.
    $( The ~ pw2f1o bijection relates finitely supported indicator functions on
       a two-element set to finite subsets. _MOVABLE_ (Contributed by Stefan
       O'Rear, 10-Jul-2015.)  (Revised by AV, 14-Jun-2020.) $)
    pwfi2f1o $p |- ( A e. V -> F : S -1-1-onto-> ( ~P A i^i Fin ) ) $=
      ( wcel c2o ccnv c1o cima wf1o cfn cin wss syl c0 wceq cmap co cv csn cmpt
      cres cpw wf1 eqid pw2f1o2 f1of1 cfsupp crab ssrab2 eqsstri f1ores sylancl
      wbr wb wa csupp wfun cvv w3a elmapfun 0ex a1i 3jca adantl funisfsupp cdif
      id anim2i elmapi fsuppeq sylc cun csuc df-2o df-suc equncomi eqtri eqcomi
      wf df1o2 difeq12i difun2 incom word 1on onordi orddisj ax-mp disj3 eqtr4i
      mpbi imaeq2i eqtrdi eleq1d cnvimass fssdm biantrurd 3bitrd elfpw rabbidva
      bitr4di cnveq imaeq1d cbvmptv mptpreima 3eqtr4g imaeq2d f1ofo inss1 eqtrd
      wfo foimacnv f1oeq3 resmpt f1oeq1 mp1i bitrd mpbid ) CFIZDAJCUAUBZAUCZKZL
      UDZMZUEZDMZYJDUFZNZDCUGZOPZENZYDYEYNYJUHZDYEQZYMYDYEYNYJNZYQACYJFYJUIUJZY
      EYNYJUKRDBUCZSULURZBYEUMZYEGUUBBYEUNUOZYEYNDYJUPUQYDYMDYOYLNZYPYDYKYOTYMU
      UEUSYDYKYJYJKYOMZMZYOYDDUUFYJYDUUCUUAKZYHMZYOIZBYEUMDUUFYDUUBUUJBYEYDUUAY
      EIZUTZUUBUUICQZUUIOIZUTZUUJUULUUBUUASVAUBZOIZUUNUUOUULUUAVBZUUKSVCIZVDZUU
      BUUQUSUUKUUTYDUUKUURUUKUUSUUAJCVEUUKVLUUSUUKVFVGZVHVIUUAYEVCSVJRUULUUPUUI
      OUULUUPUUHJSUDZVKZMZUUIUULYDUUSUTCJUUAWDZUUPUVDTUUKUUSYDUVAVMUUKUVEYDUUAJ
      CVNVIZJUUACFVCSVOVPUVCYHUUHUVCYHLVQZLVKZYHJUVGUVBLJLVRZUVGVSUVILYHLVTWAWB
      LUVBWEWCWFUVHYHLVKZYHYHLWGYHLPZSTYHUVJTUVKLYHPZSYHLWHLWIUVLSTLWJWKLWLWMWB
      YHLWNWPWOWBWQWRWSUULUUMUUNUULCJUUIUUAUUAYHWTUVFXAXBXCUUICXDXFXEGBYEUUIYOY
      JABYEYIUUIYFUUATYGUUHYHYFUUAXGXHXIXJXKXLYDYEYNYJXPZYOYNQUUGYOTYDYSUVMYTYE
      YNYJXMRYNOXNYEYNYOYJXQUQXOYKYODYLXRRYLETUUEYPUSYDYLADYIUEZEYRYLUVNTUUDAYE
      DYIXSWMHWODYOYLEXTYAYBYC $.
  $}

  ${
    $d x y A $.  $d x S $.  $d x y V $.
    pwfi2en.s $e |- S = { y e. ( 2o ^m A ) | y finSupp (/) } $.
    $( Finitely supported indicator functions are equinumerous to finite
       subsets. _MOVABLE_ (Contributed by Stefan O'Rear, 10-Jul-2015.)
       (Revised by AV, 14-Jun-2020.) $)
    pwfi2en $p |- ( A e. V -> S ~~ ( ~P A i^i Fin ) ) $=
      ( vx wcel cpw cfn cin cv ccnv c1o csn cima cmpt wf1o wbr c2o cmap eqid c0
      cen pwfi2f1o cfsupp co ovex rabex2 f1oen syl ) BDGCBHIJZFCFKLMNOPZQCUKUCR
      FABCULDEULUAUDCUKULAKUBUERASBTUFCESBTUGUHUIUJ $.
  $}

  ${
    $d x I $.  $d x R $.  $d x V $.
    frlmpwfi.r $e |- R = ( Z/nZ ` 2 ) $.
    frlmpwfi.y $e |- Y = ( R freeLMod I ) $.
    frlmpwfi.b $e |- B = ( Base ` Y ) $.
    $( Formal linear combinations over Z/2Z are equivalent to finite subsets.
       _MOVABLE_ (Contributed by Stefan O'Rear, 10-Jul-2015.)  (Proof shortened
       by AV, 14-Jun-2020.) $)
    frlmpwfi $p |- ( I e. V -> B ~~ ( ~P I i^i Fin ) ) $=
      ( vx wcel c0 wbr c2o cen cfn cfv cvv c2 eqid ax-mp cv cfsupp cmap co crab
      cpw cin c0g cbs wceq czn fvexi frlmbas eqtr4di enrefg chash cn 2nn znhash
      mpan hash2 eqtr4i wb cn0 2nn0 eqeltri fvex hashclb mpbir 2onn nnfi hashen
      com mpbi a1i crg ccrg zncrng crngring mp2b ring0cl mp1i wne 2on0 con0 2on
      mp2an on0eln0 mapfien2 eqbrtrrd pwfi2en entr syl2anc ) CDJZAIUAZKUBLIMCUC
      UDUEZNLWPCUFOUGZNLAWQNLWNWOBUHPZUBLIBUIPZCUCUDUEZAWPNWNWTEUIPZABQJWNWTXAU
      JBRUKFULWTBIECWSQDWRGWSSZWRSZWTSZUMUTHUNWNICWSCMWTWPKWRXDWPSZCDUOWSMNLZWN
      WSUPPZMUPPZUJZXFXGRXHRUQJXGRUJURWSRBFXBUSTZVAVBWSOJZMOJZXIXFVCXKXGVDJZXGR
      VDXJVEVFWSQJXKXMVCBUIVGWSQVHTVIMVMJXLVJMVKTWSMVLWGVNVOBVPJZWRWSJWNRVDJBVQ
      JXNVERBFVRBVSVTWSBWRXBXCWAWBKMJZWNXOMKWCZWDMWEJXOXPVCWFMWHTVIVOWIWJICWPDX
      EWKAWPWQWLWM $.
  $}

  ${
    $d v w x y G $.  $d v x y z G $.  $d v w x y H $.  $d z H $.
    $( Being Abelian is a group invariant. _MOVABLE_ (Contributed by Stefan
       O'Rear, 8-Jul-2015.) $)
    gicabl $p |- ( G ~=g H -> ( G e. Abel <-> H e. Abel ) ) $=
      ( vx vy vz vw vv co wcel wb syl cfv wceq wral eqid adantr syl3anc eqeq12d
      cv wa cgic wbr cgim c0 wne cabl brgic n0 cgrp ccmn gimghm ghmgrp1 ghmgrp2
      wex cghm 2thd cmnd cplusg cbs grpmndd wf1 wf1o gimf1o f1of1 simprl simprr
      grpcl f1fveq syl12anc ghmlin bitr3d 2ralbidva wfo f1ofo foima raleqdv wfn
      cima f1ofn ssid oveq2 oveq1 ralima sylancl ralbidv bitr4d anbi12d 3bitr4g
      wss iscmn isabl exlimiv sylbi ) ABUAUBABUCHZUDUEZAUFIZBUFIZJZABUGWOCSZWNI
      ZCUNWRCWNUHWTWRCWTAUIIZAUJIZTBUIIZBUJIZTWPWQWTXAXCXBXDWTXAXCWTWSABUOHIZXA
      ABWSUKZABWSULKZWTXEXCXFABWSUMKZUPWTAUQIZDSZESZAURLZHZXKXJXLHZMZEAUSLZNDXP
      NZTBUQIZFSZGSZBURLZHZXTXSYAHZMZGBUSLZNZFYENZTXBXDWTXIXRXQYGWTXIXRWTAXGUTW
      TBXHUTUPWTXQXJWSLZXTYAHZXTYHYAHZMZGYENZDXPNZYGWTXQYHXKWSLZYAHZYNYHYAHZMZE
      XPNZDXPNYMWTXOYQDEXPXPWTXJXPIZXKXPIZTZTZXMWSLZXNWSLZMZXOYQUUBXPYEWSVAZXMX
      PIZXNXPIZUUEXOJWTUUFUUAWTXPYEWSVBZUUFXPYEABWSXPOZYEOZVCZXPYEWSVDKPUUBXAYS
      YTUUGWTXAUUAXGPZWTYSYTVEZWTYSYTVFZXPXLAXJXKUUJXLOZVGQUUBXAYTYSUUHUUMUUOUU
      NXPXLAXKXJUUJUUPVGQXPYEXMXNWSVHVIUUBUUCYOUUDYPUUBXEYSYTUUCYOMWTXEUUAXFPZU
      UNUUOXLYAABXJWSXKXPUUJUUPYAOZVJQUUBXEYTYSUUDYPMUUQUUOUUNXLYAABXKWSXJXPUUJ
      UUPUURVJQRVKVLWTYLYRDXPWTYKGWSXPVRZNZYLYRWTYKGUUSYEWTUUIUUSYEMZUULUUIXPYE
      WSVMUVAXPYEWSVNXPYEWSVOKKZVPWTWSXPVQZXPXPWIZUUTYRJWTUUIUVCUULXPYEWSVSKZXP
      VTZYKYQGEXPXPWSXTYNMYIYOYJYPXTYNYHYAWAXTYNYHYAWBRWCWDVKWEWFWTYFFUUSNZYGYM
      WTYFFUUSYEUVBVPWTUVCUVDUVGYMJUVEUVFYFYLFDXPXPWSXSYHMZYDYKGYEUVHYBYIYCYJXS
      YHXTYAWBXSYHXTYAWARWEWCWDVKWFWGDEXPXLAUUJUUPWJFGYEYABUUKUURWJWHWGAWKBWKWH
      WLWMWM $.
  $}

  ${
    $d a b c d F $.  $d a b c d R $.  $d a b c d U $.  $d a b c d V $.
    $d a b c d ph $.  $d c d B $.
    imasgim.u $e |- ( ph -> U = ( F "s R ) ) $.
    imasgim.v $e |- ( ph -> V = ( Base ` R ) ) $.
    imasgim.f $e |- ( ph -> F : V -1-1-onto-> B ) $.
    imasgim.r $e |- ( ph -> R e. Grp ) $.
    $( A relabeling of the elements of a group induces an isomorphism to the
       relabeled group. _MOVABLE_ (Contributed by Stefan O'Rear, 8-Jul-2015.)
       (Revised by Mario Carneiro, 11-Aug-2015.) $)
    imasgim $p |- ( ph -> F e. ( R GrpIso U ) ) $=
      ( va vb vd vc co wcel cfv wf1o eqid cv cghm cbs cgim cplusg cgrp c0g wceq
      eqidd wfo f1ofo f1ocpbl imasgrp simpld wf wb imasbas f1oeq3 mpbid f1oeq2d
      syl f1of wa eleq2d anbi12d w3a imasaddval eqcomd 3expib sylbird imp isgim
      isghmd sylanbrc ) AECDUAOPCUBQZDUBQZERZECDUCOPAKLCUDQZDUDQZCDEVNVOVNSZVOS
      ZVQSZVRSZJADUEPCUFQZEQDUFQUGABVQCDEFWCMNKLGHAVQUHAFBERZFBEUIIFBEUJUTZAKTZ
      LTZNTMTVQEFBIUKZJWCSULUMAVPVNVOEUNAFVOERZVPAWDWIIABVOUGWDWIUOABCDEFUEGHWE
      JUPBVOFEUQUTURAFVNVOEHUSURZVNVOEVAUTAWFVNPZWGVNPZVBZWFWGVQOEQZWFEQWGEQVRO
      ZUGZAWMWFFPZWGFPZVBWPAWQWKWRWLAFVNWFHVCAFVNWGHVCVDAWQWRWPAWQWRVEWOWNABCVR
      VQDEFWFWGUEMNKLWEWHGHJWAWBVFVGVHVIVJVLWJVNVOCDEVSVTVKVM $.
  $}

  ${
    $d f B $.  $d f C $.  $d f R $.
    isnumbasgrplem1.b $e |- B = ( Base ` R ) $.
    $( A set which is equipollent to the base set of a definable Abelian group
       is the base set of some (relabeled) Abelian group.  (Contributed by
       Stefan O'Rear, 8-Jul-2015.) $)
    isnumbasgrplem1 $p |- ( ( R e. Abel /\ C ~~ B ) ->
        C e. ( Base " Abel ) ) $=
      ( vf cen wbr cabl wcel cv wf1o wex cbs cima ensymb bren bitri co cfv cvv
      wi wa cimas eqidd wceq a1i wfo f1ofo adantr simpr imasbas cgim cgic simpl
      cgrp ablgrp adantl imasgim brgici gicabl 3syl mpbid wfn wss basfn fnfvima
      wb ssv mp3an12 syl eqeltrd ex exlimiv impcom sylan2b ) BAFGZCHIZABEJZKZEL
      ZBMHNZIZVPABFGVTBAOABEPQVTVQWBVSVQWBUAEVSVQWBVSVQUBZBVRCUCRZMSZWAWCBCWDVR
      AHWCWDUDZACMSUEWCDUFZVSABVRUGVQABVRUHUIVSVQUJZUKWCWDHIZWEWAIZWCVQWIWHWCVR
      CWDULRICWDUMGVQWIVGWCBCWDVRAWFWGVSVQUNVQCUOIVSCUPUQURCWDVRUSCWDUTVAVBMTVC
      HTVDWIWJVEHVHTHMWDVFVIVJVKVLVMVNVO $.
  $}

  $( The Hartogs number of a set is never zero. _MOVABLE_ (Contributed by
     Stefan O'Rear, 9-Jul-2015.) $)
  harn0 $p |- ( S e. V -> ( har ` S ) =/= (/) ) $=
    ( wcel char cfv c0 con0 cdom wbr 0elon a1i 0domg elharval sylanbrc ne0d ) A
    BCZADEZFPFGCZFAHIFQCRPJKABLAFMNO $.

  $( A numerable infinite set contains a countable subset. _MOVABLE_
     (Contributed by Stefan O'Rear, 9-Jul-2015.) $)
  numinfctb $p |- ( ( S e. dom card /\ -. S e. Fin ) -> _om ~<_ S ) $=
    ( ccrd cdm wcel com cdom wbr cfn wn csdm wb con0 omelon onenon domtri2 mpan
    ax-mp isfinite notbii bitr4di biimpar ) ABCZDZEAFGZAHDZIZUCUDAEJGZIZUFEUBDZ
    UCUDUHKELDUIMENQEAOPUEUGARSTUA $.

  ${
    $d a b c d x S $.
    $( If the (to be thought of as disjoint, although the proof does not
       require this) union of a set and its Hartogs number supports a group
       structure (more generally, a cancellative magma), then the set must be
       numerable.  (Contributed by Stefan O'Rear, 9-Jul-2015.) $)
    isnumbasgrplem2 $p |- ( ( S u. ( har ` S ) ) e. ( Base " Grp ) ->
        S e. dom card ) $=
      ( vx va vc vd vb cfv cbs cgrp wcel cv wceq cvv wss wb wbr sseldd ad2antrr
      wa co char cun cima wrex ccrd cdm wfn basfn ssv fvelimab mp2an cdom harcl
      cxp con0 onenon ax-mp xpnum cwdom ssun1 simpr sseqtrrid fvex ssex syl a1i
      cplusg w3a simp1l 3ad2ant1 simp2 ssun2 simp3 grpcl syl3anc simp1r eleqtrd
      simplll simprl simprr simplr grplcan syl13anc grprcan wn harndom wdomnumr
      eqid unxpwdom3 sylib numdom sylancr rexlimiva sylbi ) AAUAGZUBZHIUCJZBKZH
      GZWPLZBIUDZAUEUFZJZHMUGIMNWQXAOUHIUIBMIWPHUJUKWTXCBIWRIJZWTSZWOWOUNZXBJZA
      XFULPZXCWOXBJZXIXGWOUOJXIAUMWOUPUQZXJWOWOURUKZXEAXFUSPZXHXEAWOAWOWRVGGZMX
      BXBCDEFXEAWSNZAMJXEWPAWSAWOUTXDWTVAZVBZAWSWRHVCVDVEXIXEXJVFZXQXECKZAJZDKZ
      WOJZVHZXRXTXMTZWSWPYBXDXRWSJZXTWSJZYCWSJXDWTXSYAVIYBAWSXRXEXSXNYAXPVJXEXS
      YAVKQYBWOWSXTXEXSWOWSNZYAXEWPWOWSWOAVLXOVBZVJXEXSYAVMQWSXMWRXRXTWSWHZXMWH
      ZVNVOXDWTXSYAVPVQXEXSSZYAEKZWOJZSZSZXDYEYKWSJZYDYCXRYKXMTLXTYKLOXDWTXSYMV
      RYNWOWSXTXEYFXSYMYGRZYJYAYLVSQYNWOWSYKYPYJYAYLVTQYNAWSXRXEXNXSYMXPRXEXSYM
      WAQWSXMWRXTYKXRYHYIWBWCXEFKZWOJZSZXSYKAJZSZSZXDYOYDYQWSJYKYQXMTXRYQXMTLYK
      XRLOXDWTYRUUAVRUUBAWSYKXEXNYRUUAXPRZYSXSYTVTQUUBAWSXRUUCYSXSYTVSQUUBWOWSY
      QXEYFYRUUAYGRXEYRUUAWAQWSXMWRYKXRYQYHYIWDWCWOAULPWEXEAWFVFWIXGXLXHOXKAXFW
      GUQWJXFAWKWLWMWN $.

    $( Every nonempty numerable set can be given the structure of an Abelian
       group, either a finite cyclic group or a vector space over Z/2Z.
       (Contributed by Stefan O'Rear, 10-Jul-2015.) $)
    isnumbasgrplem3 $p |- ( ( S e. dom card /\ S =/= (/) ) ->
        S e. ( Base " Abel ) ) $=
      ( wcel wa cfn cbs cabl chash cfv czn cen wbr cn0 ccrg crg zncrng crngring
      eqid syl syl2anc c2 ccrd cdm wne cima hashcl adantl ringabl 4syl hashnncl
      c0 wceq cn biimparc znhash eqcomd simpr znfi hashen mpbid isnumbasgrplem1
      wb adantll wn cfrlm co clmod 2nn0 mp2b frlmlmod mpan lmodabl ad2antrr cpw
      cin frlmpwfi com cdom simpll numinfctb adantlr infpwfien ensymd pm2.61dan
      entr ) AUAUBZBZAUJUCZCZADBZAEFUDBZWGWIWJWFWGWICZAGHZIHZFBZAWMEHZJKZWJWKWL
      LBZWMMBWMNBWNWIWQWGAUEUFWLWMWMQZOWMPWMUGUHWKWLWOGHZUKZWPWKWSWLWKWLULBZWSW
      LUKWIXAWGAUIUMZWOWLWMWRWOQZUNRUOWKWIWODBZWTWPVAWGWIUPWKXAXDXBWOWLWMWRXCUQ
      RAWOURSUSWOAWMXCUTSVBWHWIVCZCZTIHZAVDVEZFBZAXHEHZJKWJWFXIWGXEWFXHVFBZXIXG
      NBZWFXKTLBXGMBXLVGTXGXGQZOXGPVHXGXHAWEXHQZVIVJXHVKRVLXFXJAXFXJAVMDVNZJKZX
      OAJKZXJAJKWFXPWGXEXJXGAWEXHXMXNXJQZVOVLXFWFVPAVQKZXQWFWGXEVRWFXEXSWGAVSVT
      AWASXJXOAWDSWBXJAXHXRUTSWC $.
  $}

  $( A set is numerable iff it and its Hartogs number can be jointly given the
     structure of an Abelian group.  (Contributed by Stefan O'Rear,
     9-Jul-2015.) $)
  isnumbasabl $p |- ( S e. dom card <->
      ( S u. ( har ` S ) ) e. ( Base " Abel ) ) $=
    ( vx ccrd cdm wcel char cfv cun cbs cabl cima c0 wne con0 harcl ax-mp unnum
    onenon wss cgrp mpan2 ssun2 harn0 sylancr isnumbasgrplem3 syl2anc cv ablgrp
    ssn0 ssriv imass2 sseli isnumbasgrplem2 syl impbii ) ACDZEZAAFGZHZIJKZEZUQU
    SUPEZUSLMZVAUQURUPEZVBURNEVDAOURRPAURQUAUQURUSSURLMVCURAUBAUPUCURUSUIUDUSUE
    UFVAUSITKZEUQUTVEUSJTSUTVESBJTBUGUHUJJTIUKPULAUMUNUO $.

  $( A set is numerable iff it and its Hartogs number can be jointly given the
     structure of a group.  (Contributed by Stefan O'Rear, 9-Jul-2015.) $)
  isnumbasgrp $p |- ( S e. dom card <->
      ( S u. ( har ` S ) ) e. ( Base " Grp ) ) $=
    ( vx ccrd cdm wcel char cfv cun cbs cgrp cima wss ablgrp ssriv imass2 ax-mp
    cabl cv isnumbasabl biimpi sselid isnumbasgrplem2 impbii ) ACDEZAAFGHZIJKZE
    UDIQKZUFUEQJLUGUFLBQJBRMNQJIOPUDUEUGEASTUAAUBUC $.

  ${
    $d x y $.
    $( A choice equivalent in abstract algebra:  All nonempty sets admit a
       group structure.  From ~ http://mathoverflow.net/a/12988 .  (Contributed
       by Stefan O'Rear, 9-Jul-2015.) $)
    dfacbasgrp $p |- ( CHOICE <-> ( Base " Grp ) = ( _V \ { (/) } ) ) $=
      ( vx vy cvv wceq cbs cgrp cima c0 cv wcel wne wa cfv wss mp2an cabl ax-mp
      eleqtrrd eldifsn eqrdv wac ccrd cdm csn cdif dfac10 wrex wfn wb basfn ssv
      fvelimab grpbn0 neeq1 syl5ibcom rexlimiv sylbi adantl jctil ablgrp imass2
      eqid vex ssriv simprl simpl simprr isnumbasgrplem3 syl2anc sselid impbida
      bitr4di char cun fvex unex ssun2 harn0 mpbir2an a1i id isnumbasgrp sylibr
      ssn0 2thd impbii bitri ) UAUBUCZCDZEFGZCHUDUEZDZUFWIWLWIAWJWKWIAIZWJJZWMC
      JZWMHKZLZWMWKJWIWNWQWIWNLWPWOWNWPWIWNBIZEMZWMDZBFUGZWPECUHFCNWNXAUIUJFUKB
      CFWMEULOWTWPBFWRFJWSHKWTWPWSWRWSVBUMWSWMHUNUOUPUQURAVCZUSWIWQLZEPGZWJWMPF
      NXDWJNAPFWMUTVDPFEVAQXCWMWHJZWPWMXDJXCWMCWHWIWOWPVEWIWQVFRWIWOWPVGWMVHVIV
      JVKWMCHSVLTWLAWHCWLXEWOWLWMWMVMMZVNZWJJXEWLXGWKWJXGWKJZWLXHXGCJXGHKZWMXFX
      BWMVMVOVPXFXGNXFHKZXIXFWMVQWOXJXBWMCVRQXFXGWDOXGCHSVSVTWLWARWMWBWCWOWLXBV
      TWETWFWG $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Noetherian rings and left modules II
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c LNoeR $.

  $( Extend class notation with the class of left Noetherian rings. $)
  clnr $a class LNoeR $.

  $( A ring is _left-Noetherian_ iff it is Noetherian as a left module over
     itself.  (Contributed by Stefan O'Rear, 24-Jan-2015.) $)
  df-lnr $a |- LNoeR = { a e. Ring | ( ringLMod ` a ) e. LNoeM } $.

  ${
    $d A a $.
    $( Property of a left-Noetherian ring.  (Contributed by Stefan O'Rear,
       24-Jan-2015.) $)
    islnr $p |- ( A e. LNoeR <-> ( A e. Ring /\
        ( ringLMod ` A ) e. LNoeM ) ) $=
      ( va cv crglmod cfv clnm wcel crg clnr wceq fveq2 eleq1d df-lnr elrab2 )
      BCZDEZFGADEZFGBAHIOAJPQFOADKLBMN $.

    $( Left-Noetherian rings are rings.  (Contributed by Stefan O'Rear,
       24-Jan-2015.) $)
    lnrring $p |- ( A e. LNoeR -> A e. Ring ) $=
      ( clnr wcel crg crglmod cfv clnm islnr simplbi ) ABCADCAEFGCAHI $.

    $( Left-Noetherian rings have Noetherian associated modules.  (Contributed
       by Stefan O'Rear, 24-Jan-2015.) $)
    lnrlnm $p |- ( A e. LNoeR -> ( ringLMod ` A ) e. LNoeM ) $=
      ( clnr wcel crg crglmod cfv clnm islnr simprbi ) ABCADCAEFGCAHI $.
  $}

  ${
    $d i g R $.  $d i g N $.  $d i g U $.  $d i g B $.
    islnr2.b $e |- B = ( Base ` R ) $.
    islnr2.u $e |- U = ( LIdeal ` R ) $.
    islnr2.n $e |- N = ( RSpan ` R ) $.
    $( Property of being a left-Noetherian ring in terms of finite generation
       of ideals (the usual "pure ring theory" definition).  (Contributed by
       Stefan O'Rear, 24-Jan-2015.) $)
    islnr2 $p |- ( R e. LNoeR <-> ( R e. Ring /\
        A. i e. U E. g e. ( ~P B i^i Fin ) i = ( N ` g ) ) ) $=
      ( clnr wcel crg crglmod cfv clnm wa cv wceq cbs eqtri cpw wrex wral islnr
      cfn cin clmod wb rlmlmod rlmbas clidl clss lidlval crsp clspn rspval baib
      islnm2 syl pm5.32i bitri ) BJKBLKZBMNZOKZPVBEQDQFNRDAUAUEUFUBECUCZPBUDVBV
      DVEVBVCUGKZVDVEUHBUIVDVFVEACDEVCFABSNVCSNGBUJTCBUKNVCULNHBUMTFBUNNVCUONIB
      UPTURUQUSUTVA $.
  $}

  ${
    $d B x y $.  $d R x y $.  $d U x y $.
    islnr3.b $e |- B = ( Base ` R ) $.
    islnr3.u $e |- U = ( LIdeal ` R ) $.
    $( Relate left-Noetherian rings to Noetherian-type closure property of the
       left ideal system.  (Contributed by Stefan O'Rear, 4-Apr-2015.) $)
    islnr3 $p |- ( R e. LNoeR <-> ( R e. Ring /\ U e. ( NoeACS ` B ) ) ) $=
      ( vx vy clnr wcel crg cv crsp cfv wceq cpw cfn wrex wral wa eqid cin cacs
      cnacs islnr2 mrcrsp fveq1d eqeq2d rexbidv ralbidv lidlacs biantrurd bitrd
      cmrc isnacs bitr4di pm5.32i bitri ) BHIBJIZFKZGKZBLMZMZNZGAOPUAZQZFCRZSUR
      CAUCMIZSABCGFVADEVATZUDURVFVGURVFCAUBMIZUSUTCUMMZMZNZGVDQZFCRZSZVGURVFVNV
      OURVEVMFCURVCVLGVDURVBVKUSURUTVAVJBCVJVAEVHVJTZUEUFUGUHUIURVIVNACBDEUJUKU
      LCGVJAFVPUNUOUPUQ $.
  $}

  ${
    $d I g i $.  $d N g i $.  $d R g i $.  $d U g i $.
    lnr2i.u $e |- U = ( LIdeal ` R ) $.
    lnr2i.n $e |- N = ( RSpan ` R ) $.
    $( Given an ideal in a left-Noetherian ring, there is a finite subset which
       generates it.  (Contributed by Stefan O'Rear, 31-Mar-2015.) $)
    lnr2i $p |- ( ( R e. LNoeR /\ I e. U ) ->
        E. g e. ( ~P I i^i Fin ) I = ( N ` g ) ) $=
      ( vi wcel wa cv cfv wceq cpw cfn cin wrex wi wss 3imtr4g clnr wral islnr2
      cbs eqid simprbi eqeq1 rexbidv rspcva sylan2 ancoms lnrring rspssid sylan
      crg ex vex elpw anim1d elin pweq ineq1d eleq2d syl5ibrcom imdistand ancom
      imbi2d reximdv2 adantr mpd ) AUAIZDBIZJDCKZELZMZCAUDLZNZOPZQZVOCDNZOPZQZV
      LVKVSVKVLHKZVNMZCVRQZHBUBZVSVKAUOIZWFVPABCHEVPUEZFGUCUFWEVSHDBWCDMWDVOCVR
      WCDVNUGUHUIUJUKVKVSWBRVLVKVOVOCVRWAVKVOVMVRIZJVOVMWAIZJWIVOJWJVOJVKVOWIWJ
      VKWIWJRVOWIVMVNNZOPZIZRVKVMVQIZVMOIZJVMWKIZWOJWIWMVKWNWPWOVKVMVPSZVMVNSZW
      NWPVKWQWRVKWGWQWRAULVPAVMEGWHUMUNUPVMVPCUQZURVMVNWSURTUSVMVQOUTVMWKOUTTVO
      WJWMWIVOWAWLVMVOVTWKODVNVAVBVCVGVDVEWIVOVFWJVOVFTVHVIVJ $.
  $}

  ${
    $d a b c R $.
    $( Left principal ideal rings are left Noetherian.  (Contributed by Stefan
       O'Rear, 24-Jan-2015.) $)
    lpirlnr $p |- ( R e. LPIR -> R e. LNoeR ) $=
      ( va vb vc clpir wcel crg cv crsp cfv wceq cbs cpw cfn wrex clidl wral wa
      cin eqid clnr lpirring clpidl csn islpidl syl biimpa snelpwi adantl elind
      wb snfi a1i fveq2 rspceeqv sylancl eqeq1 rexbidv syl5ibrcom rexlimdva mpd
      ralrimiva islpir simprbi raleqtrrdv islnr2 sylanbrc ) AEFZAGFZBHZCHZAIJZJ
      ZKZCALJZMZNSZOZBAPJZQAUAFAUBZVHVRBAUCJZVSVHVRBWAVHVJWAFZRZVJDHZUDZVLJZKZD
      VOOZVRVHWBWHVHVIWBWHUKVTVOWAADVJVLWATZVLTZVOTZUEUFUGWCWGVRDVOWCWDVOFZRZVR
      WGWFVMKZCVQOZWMWEVQFWFWFKWOWMVPNWEWLWEVPFWCWDVOUHUIWENFWMWDULUMUJWFTCWEVQ
      VMWFWFVKWEVLUNUOUPWGVNWNCVQVJWFVMUQURUSUTVAVBVHVIVSWAKWAAVSWIVSTZVCVDVEVO
      AVSCBVLWKWPWJVFVG $.
  $}

  ${
    lnrfrlm.y $e |- Y = ( R freeLMod I ) $.
    $( Finite-dimensional free modules over a Noetherian ring are Noetherian.
       (Contributed by Stefan O'Rear, 3-Feb-2015.) $)
    lnrfrlm $p |- ( ( R e. LNoeR /\ I e. Fin ) -> Y e. LNoeM ) $=
      ( clnr wcel cfn wa crglmod cfv cpws co clnm frlmpwsfi lnrlnm pwslnm sylan
      eqid eqeltrd ) AEFZBGFZHCAIJZBKLZMACBEDNTUBMFUAUCMFAOBUBUCUCRPQS $.
  $}

  ${
    $d S a b $.  $d M a b $.
    lnrfg.s $e |- S = ( Scalar ` M ) $.
    $( Finitely-generated modules over a Noetherian ring, being homomorphic
       images of free modules, are Noetherian.  (Contributed by Stefan O'Rear,
       7-Feb-2015.) $)
    lnrfg $p |- ( ( M e. LFinGen /\ S e. LNoeR ) -> M e. LNoeM ) $=
      ( va vb clfig wcel clnr wa cv cfv cbs wceq clnm co crn cvv eqid a1i wf wb
      cfn clspn cpw cfrlm cid cres cvsca cgsu cmpt clmhm clmod fglmod ad3antrrr
      cof vex csca wss wf1o f1oi f1of ax-mp fss sylancr ad2antlr frlmup1 simprl
      elpwi simpllr lnrfrlm syl2anc frlmup3 rnresi fveq2i simprr eqtrid syl3anc
      eqtrd lnmepi wrex islmodfg syl ibi adantr r19.29a ) BFGZAHGZIZDJZUBGZWIBU
      CKZKZBLKZMZIZBNGZDWMUDZWHWIWQGZIZWOIZEAWIUEOZLKZBEJUFWIUGZBUHKZUOOUIOUJZX
      ABUKOGXANGZXEPZWMMWPWTEXCXBWMABXDXEXAWIQXARZXBRZWMRZXDRZXERZWFBULGZWGWRWO
      BUMZUNZWIQGWTDUPSZABUQKMWTCSZWRWIWMXCTZWHWOWRWIWIXCTZWIWMURXRWIWIXCUSXSWI
      UTWIWIXCVAVBWIWMVHWIWIWMXCVCVDVEZVFWTWGWJXFWFWGWRWOVIWSWJWNVGAWIXAXHVJVKW
      TXGXCPZWKKZWMWTEXCXBWMABXDXEXAWIWKQXHXIXJXKXLXOXPXQXTWKRZVLWTYBWLWMYAWIWK
      WIVMVNWSWJWNVOVPVRWMXABXEXJVSVQWFWODWQVTZWGWFYDWFXMWFYDUAXNWMWKBDXJYCWAWB
      WCWDWE $.

    lnrfgtr.u $e |- U = ( LSubSp ` M ) $.
    lnrfgtr.n $e |- N = ( M |`s P ) $.
    $( A submodule of a finitely generated module over a Noetherian ring is
       finitely generated.  Often taken as the definition of Noetherian ring.
       (Contributed by Stefan O'Rear, 7-Feb-2015.) $)
    lnrfgtr $p |- ( ( M e. LFinGen /\ S e. LNoeR /\ P e. U ) ->
        N e. LFinGen ) $=
      ( clfig wcel clnr clnm lnrfg lnmlssfg stoic3 ) DIJBKJDLJACJEIJBDFMECADGHN
      O $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Hilbert's Basis Theorem
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c ldgIdlSeq $.

  $( The leading ideal sequence used in the Hilbert Basis Theorem. $)
  cldgis $a class ldgIdlSeq $.

  ${
    $d r i x j k $.
    $( Define a function which carries polynomial ideals to the sequence of
       coefficient ideals of leading coefficients of degree- ` x ` elements in
       the polynomial ideal.  The proof that this map is strictly monotone is
       the core of the Hilbert Basis Theorem ~ hbt .  (Contributed by Stefan
       O'Rear, 31-Mar-2015.) $)
    df-ldgis $a |- ldgIdlSeq = ( r e. _V |-> ( i e.
            ( LIdeal ` ( Poly1 ` r ) ) |-> ( x e. NN0 |->
                { j | E. k e. i ( ( ( deg1 ` r ) ` k ) <_ x /\
                      j = ( ( coe1 ` k ) ` x ) ) } ) ) ) $.
  $}

  ${
    hbtlem.p $e |- P = ( Poly1 ` R ) $.
    hbtlem.u $e |- U = ( LIdeal ` P ) $.
    hbtlem.s $e |- S = ( ldgIdlSeq ` R ) $.

    ${
      $d D i r x $.  $d I i j k x $.  $d R i j k r x $.  $d U i r $.
      $d X j k x $.
      hbtlem.d $e |- D = ( deg1 ` R ) $.
      $( Value of the leading coefficient sequence function.  (Contributed by
         Stefan O'Rear, 31-Mar-2015.) $)
      hbtlem1 $p |- ( ( R e. V /\ I e. U /\ X e. NN0 ) -> ( ( S ` I ) ` X ) =
          { j | E. k e. I ( ( D ` k ) <_ X /\ j = ( ( coe1 ` k ) ` X ) ) } ) $=
        ( vi vx wcel cn0 cfv wceq vr w3a cv cle wbr cco1 wa wrex cab cldgis cvv
        cmpt elex clidl cpl1 eqtr4di fveq2d fveq1d breq1d anbi1d rexbidv abbidv
        cdg1 fveq2 mpteq2dv mpteq12dv df-ldgis mptfvmpt syl 3ad2ant1 rexeq eqid
        eqtrid nn0ex mptex fvmpt 3ad2ant2 breq2 eqeq2d anbi12d simp3 wss reximi
        simpr ss2abi abrexexg ssexg sylancr fvmptd3 3eqtrd ) CIQZHEQZJRQZUBZJHD
        SZSZJHOEPRGUCZASZPUCZUDUEZFUCZWSWQUFSZSZTZUGZGOUCZUHZFUIZULZULZSZSZJPRX
        EGHUHZFUIZULZSZWRJUDUEZXAJXBSZTZUGZGHUHZFUIZWKWLWPXLTWMWKJWOXKWKHDXJWKD
        CUJSZXJMWKCUKQYCXJTCIUMOUAXIUNUJOUAUCZUOSZUNSZPRWQYDVCSZSZWSUDUEZXDUGZG
        XFUHZFUIZULZULEUKBCYDCTZOYFYMEXIYNYFBUNSEYNYEBUNYNYECUOSBYDCUOVDKUPUQLU
        PYNPRYLXHYNYKXGFYNYJXEGXFYNYIWTXDYNYHWRWSUDYNWQYGAYNYGCVCSAYDCVCVDNUPUR
        USUTVAVBVEVFPOFGUAVGLVHVIVMURURVJWLWKXLXPTWMWLJXKXOOHXIXOEXJXFHTZPRXHXN
        YOXGXMFXEGXFHVKVBVEXJVLPRXNVNVOVPURVQWNPJXNYBRXOUKXOVLWSJTZXMYAFYPXEXTG
        HYPWTXQXDXSWSJWRUDVRYPXCXRXAWSJXBVDVSVTVAVBWKWLWMWAWNYBXSGHUHZFUIZWBYRU
        KQZYBUKQYAYQFXTXSGHXQXSWDWCWEWLWKYSWMGFHXREWFVQYBYRUKWGWHWIWJ $.
    $}

    ${
      $d I a b c d e f $.  $d I g $.  $d P b $.  $d R a b c d e f $.  $d R g $.
      $d U a b c d e f $.  $d U g $.  $d X a b c d e f $.  $d X g $.  $d a g $.
      $d b g $.  $d c g $.  $d e g $.  $d f g $.
      hbtlem2.t $e |- T = ( LIdeal ` R ) $.
      $( Leading coefficient ideals are ideals.  (Contributed by Stefan O'Rear,
         1-Apr-2015.) $)
      hbtlem2 $p |- ( ( R e. Ring /\ I e. U /\ X e. NN0 ) ->
          ( ( S ` I ) ` X ) e. T ) $=
        ( vb va wcel cfv cle cco1 wceq wa eqid vc vd ve vf crg cn0 w3a cdg1 wbr
        vg cv wrex cab hbtlem1 cbs wss c0 wne cmulr co cplusg wral wi wf lidlss
        3ad2ant2 sselda coe1f syl simpl3 ffvelcdmd eleq1a adantld rexlimdva c0g
        abssdv ply1ring 3ad2ant1 simp2 lidl0cl syl2anc cmnf deg1z cxr cr ressxr
        nn0ssre sstri simp3 sselid mnfle eqbrtrd csn coe1z fveq1d fvex fvconst2
        cxp 3ad2ant3 eqtr2d fveq2 breq1d eqeq2d anbi12d rspcev syl12anc rexbidv
        eqeq1 anbi2d elab sylibr ne0d wal adantr simpl2 ply1sclf simprl simprll
        cascl adantl lidlmcl syl22anc simprrl lidlacl simpl1 sseldd syl3anc imp
        ringcl deg1xrcl oveq1d oveq2 eleq1d syl5ibrcom expimpd alrimiv cbvrexvw
        weq bitrdi ralab deg1mul3le simprlr xrletrd simprrr deg1addle2 syl31anc
        coe1addfv coe1sclmulfv syl121anc ovex exp45 ralbidv ralrimiva syl3anbrc
        exp5c imp41 islidl eqeltrd ) BUENZFENZGUFNZUGZGFCOOLUKZBUHOZOZGPUIZMUKZ
        GUVCQOZOZRZSZLFULZMUMZDUVDABCEMLFUEGHIJUVDTZUNUVBUVMBUOOZUPUVMUQURUAUKZ
        UBUKZBUSOZUTZUCUKZBVAOZUTZUVMNZUCUVMVBZUBUVMVBZUAUVOVBUVMDNUVBUVLMUVOUV
        BUVKUVGUVONZLFUVBUVCFNZSZUVJUWFUVFUWHUVIUVONUVJUWFVCUWHUFUVOGUVHUWHUVCA
        UOOZNUFUVOUVHVDUVBFUWIUVCUUTUUSFUWIUPZUVAUWIFEAUWITZIVEVFZVGUVHUWIABUVC
        UVOUVHTUWKHUVOTZVHVIUUSUUTUVAUWGVJVKUVIUVOUVGVLVIVMVNVPUVBUVMBVOOZUVBUV
        FUWNUVIRZSZLFULZUWNUVMNUVBAVOOZFNZUWRUVDOZGPUIZUWNGUWRQOZOZRZUWQUVBAUEN
        ZUUTUWSUUSUUTUXEUVAABHVQVRZUUSUUTUVAVSAEFUWRIUWRTZVTWAUVBUWTWBGPUUSUUTU
        WTWBRUVAUVDABUWRUVNHUXGWCVRUVBGWDNWBGPUIUVBUFWDGUFWEWDWGWFWHZUUSUUTUVAW
        IWJGWKVIWLUVBUXCGUFUWNWMWRZOZUWNUVBGUXBUXIUUSUUTUXBUXIRUVAABUWNUWRHUXGU
        WNTWNVRWOUVAUUSUXJUWNRUUTUFUWNGBVOWPZWQWSWTUWPUXAUXDSLUWRFUVCUWRRZUVFUX
        AUWOUXDUXLUVEUWTGPUVCUWRUVDXAXBUXLUVIUXCUWNUXLGUVHUXBUVCUWRQXAWOXCXDXEX
        FUVLUWQMUWNUXKUVGUWNRZUVKUWPLFUXMUVJUWOUVFUVGUWNUVIXHXIXGXJXKXLUVBUWEUA
        UVOUVBUVPUVONZSZUDUKZUVDOZGPUIZUVQGUXPQOZOZRZSZUDFULZUWDVCZUBXMUWEUXOUY
        DUBUXOUYBUWDUDFUXOUXPFNZSZUXRUYAUWDUYFUXRSZUWDUYAUVPUXTUVRUTZUVTUWAUTZU
        VMNZUCUVMVBZUYGUJUKZUVDOZGPUIZUVTGUYLQOZOZRZSZUJFULZUYJVCZUCXMUYKUYGUYT
        UCUYGUYRUYJUJFUYGUYLFNZSZUYNUYQUYJVUBUYNSUYJUYQUYHUYPUWAUTZUVMNZUYFUXRV
        UAUYNVUDUXOUYEUXRVUAUYNVUDVCVCVCUXOUYEUXRVUAUYNVUDUVBUXNUYEUXRSZVUAUYNS
        ZVUDVCVCUVBUXNVUEVUFVUDUVBUXNVUEVUFSZSZSZUVFVUCUVIRZSZLFULZVUDVUIUVPAXS
        OZOZUXPAUSOZUTZUYLAVAOZUTZFNZVURUVDOZGPUIZVUCGVURQOZOZRZVULVUIUXEUUTVUP
        FNZVUAVUSUVBUXEVUHUXFXNZUUSUUTUVAVUHXOZVUIUXEUUTVUNUWINZUYEVVEVVFVVGVUI
        UVOUWIUVPVUMUVBUVOUWIVUMVDZVUHUUSUUTVVIUVAVUMUWIABUVOHVUMTZUWMUWKXPVRXN
        UVBUXNVUGXQZVKZVUHUYEUVBUXNUYEUXRVUFXRXTZUWIAVUOEFVUNUXPIUWKVUOTZYAYBVU
        HVUAUVBUXNVUEVUAUYNYCXTZVUQAEFVUPUYLIVUQTZYDYBVUIUWIUVDVUQBVUPUYLGAHUVN
        UUSUUTUVAVUHYEZUWKVVPVUIUXEVVHUXPUWINZVUPUWINZVVFVVLVUIFUWIUXPUVBUWJVUH
        UWLXNZVVMYFZUWIAVUOVUNUXPUWKVVNYIYGZVUIFUWIUYLVVTVVOYFZVUIUFWDGUXHUUSUU
        TUVAVUHVJZWJZVUIVUPUVDOZUXQGVUIVVSVWFWDNVWBUWIUVDABVUPUVNHUWKYJVIVUIVVR
        UXQWDNVWAUWIUVDABUXPUVNHUWKYJVIVWEVUIUUSUXNVVRVWFUXQPUIVVQVVKVWAVUMUWIU
        VDABVUOUVPUXPUVOUVNHUWMUWKVVNVVJUUAYGVUHUXRUVBUXNUYEUXRVUFUUBXTUUCVUHUY
        NUVBUXNVUEVUAUYNUUDXTUUEVUIVVCGVUPQOOZUYPUWAUTZVUCVUIUUSVVSUYLUWINUVAVV
        CVWHRVVQVWBVWCVWDUWIUWAVUQBVUPUYLGAHUWKVVPUWATZUUGUUFVUIVWGUYHUYPUWAVUI
        UUSUXNVVRUVAVWGUYHRVVQVVKVWAVWDVUMUWIABVUOUVRUVOUVPUXPGHUWKUWMVVJVVNUVR
        TZUUHUUIYKWTVUKVVAVVDSLVURFUVCVURRZUVFVVAVUJVVDVWKUVEVUTGPUVCVURUVDXAXB
        VWKUVIVVCVUCVWKGUVHVVBUVCVURQXAWOXCXDXEXFUVLVULMVUCUYHUYPUWAUUJUVGVUCRZ
        UVKVUKLFVWLUVJVUJUVFUVGVUCUVIXHXIXGXJXKUUKYHUUOYHUUPUYQUYIVUCUVMUVTUYPU
        YHUWAYLYMYNYOVNYPUVLUYSUYJUCMMUCYRZUVLUVFUVTUVIRZSZLFULUYSVWMUVKVWOLFVW
        MUVJVWNUVFUVGUVTUVIXHXIXGVWOUYRLUJFLUJYRZUVFUYNVWNUYQVWPUVEUYMGPUVCUYLU
        VDXAXBVWPUVIUYPUVTVWPGUVHUYOUVCUYLQXAWOXCXDYQYSYTXKUYAUWCUYJUCUVMUYAUWB
        UYIUVMUYAUVSUYHUVTUWAUVQUXTUVPUVRYLYKYMUULYNYOVNYPUVLUYCUWDUBMMUBYRZUVL
        UVFUVQUVIRZSZLFULUYCVWQUVKVWSLFVWQUVJVWRUVFUVGUVQUVIXHXIXGVWSUYBLUDFLUD
        YRZUVFUXRVWRUYAVWTUVEUXQGPUVCUXPUVDXAXBVWTUVIUXTUVQVWTGUVHUXSUVCUXPQXAW
        OXCXDYQYSYTXKUUMUAUVOUWABUVRDUVMUBUCKUWMVWIVWJUUQUUNUUR $.
    $}

    ${
      $d I i j x y $.  $d R i j r x y $.  $d S x $.  $d T x $.  $d U i r x $.
      hbtlem7.t $e |- T = ( LIdeal ` R ) $.
      $( Functionality of leading coefficient ideal sequence.  (Contributed by
         Stefan O'Rear, 4-Apr-2015.) $)
      hbtlem7 $p |- ( ( R e. Ring /\ I e. U ) -> ( S ` I ) : NN0 --> T ) $=
        ( vx vj vy vi wcel cfv cn0 cv cmpt cvv vr crg wa wfn wral cdg1 cle cco1
        wf wbr wceq wrex cab wss simpr reximi ss2abi abrexexg sylancr ralrimivw
        ssexg adantl eqid fnmpt syl cldgis elex clidl cpl1 fveq2 eqtr4di fveq2d
        fveq1d breq1d anbi1d abbidv mpteq2dv mpteq12dv df-ldgis mptfvmpt eqtrid
        rexbidv rexeq nn0ex mptex fvmpt sylan9eq fneq1d hbtlem2 3expa ralrimiva
        mpbird ffnfv sylanbrc ) BUBOZFEOZUCZFCPZQUDZKRZWRPDOZKQUEQDWRUIWQWSKQLR
        ZBUFPZPZWTUGUJZMRWTXBUHPPZUKZUCZLFULZMUMZSZQUDZWQXJTOZKQUEZXLWPXNWOWPXM
        KQWPXJXGLFULZMUMZUNXPTOXMXIXOMXHXGLFXEXGUOUPUQLMFXFEURXJXPTVAUSUTVBKQXJ
        XKTXKVCVDVEWQQWRXKWOWPWRFNEKQXHLNRZULZMUMZSZSZPXKWOFCYAWOCBVFPZYAIWOBTO
        YBYAUKBUBVGNUAXTVHVFNUARZVIPZVHPZKQXBYCUFPZPZWTUGUJZXGUCZLXQULZMUMZSZSE
        TABYCBUKZNYEYLEXTYMYEAVHPEYMYDAVHYMYDBVIPAYCBVIVJGVKVLHVKYMKQYKXSYMYJXR
        MYMYIXHLXQYMYHXEXGYMYGXDWTUGYMXBYFXCYCBUFVJVMVNVOWBVPVQVRKNMLUAVSHVTVEW
        AVMNFXTXKEYAXQFUKZKQXSXJYNXRXIMXHLXQFWCVPVQYAVCKQXJWDWEWFWGWHWLWQXAKQWO
        WPWTQOXAABCDEFWTGHIJWIWJWKKQDWRWMWN $.
    $}

    ${
      $d ph a c $.  $d I a b c $.  $d P b $.  $d R a b c $.  $d X a b c $.
      $d Y a b c $.
      hbtlem4.r $e |- ( ph -> R e. Ring ) $.
      hbtlem4.i $e |- ( ph -> I e. U ) $.
      hbtlem4.x $e |- ( ph -> X e. NN0 ) $.
      hbtlem4.y $e |- ( ph -> Y e. NN0 ) $.
      hbtlem4.xy $e |- ( ph -> X <_ Y ) $.
      $( The leading ideal function goes to increasing sequences.  (Contributed
         by Stefan O'Rear, 1-Apr-2015.) $)
      hbtlem4 $p |- ( ph -> ( ( S ` I ) ` X ) C_ ( ( S ` I ) ` Y ) ) $=
        ( cfv cle wceq wcel vc va vb cv cdg1 wbr cco1 wa wrex cab cmin cv1 cmgp
        co cmg cmulr crg cbs ad2antrr ply1ring syl eqid mgpbas cmnd ringmgp cn0
        nn0sub2 syl3anc vr1cl mulgnn0cld simplr lidlmcl caddc wss lidlss sseldd
        syl22anc syl2anc simpr deg1mulle2 nn0cnd npcand breqtrd c0g coe1pwmulfv
        deg1pwle fveq2d eqtr3d fveq2 breq1d fveq1d eqeq2d rspcev syl12anc eqeq1
        anbi12d rexbidv syl5ibrcom expimpd rexlimdva ss2abdv hbtlem1 3sstr4d
        anbi2d ) AUAUDZCUEQZQGRUFZUBUDZGXEUGQQZSZUHZUAFUIZUBUJZUCUDZXFQZHRUFZXH
        HXNUGQZQZSZUHZUCFUIZUBUJZGFDQZQZHYCQZAXLYAUBAXKYAUAFAXEFTZUHZXGXJYAYGXG
        UHZYAXJXPXIXRSZUHZUCFUIZYHHGUKUNZCULQZBUMQZUOQZUNZXEBUPQZUNZFTZYRXFQZHR
        UFZXIHYRUGQZQZSZYKYHBUQTZFETZYPBURQZTYFYSYHCUQTZUUEAUUHYFXGLUSZBCIUTVAZ
        AUUFYFXGMUSZYHUUGYOYNYLYMUUGBYNYNVBZUUGVBZVCYOVBZYHUUEYNVDTUUJBYNUULVEV
        AYHGVFTZHVFTZGHRUFZYLVFTZAUUOYFXGNUSZAUUPYFXGOUSZAUUQYFXGPUSGHVGVHZYHUU
        HYMUUGTUUIUUGBCYMYMVBZIUUMVIVAVJZAYFXGVKZUUGBYQEFYPXEJUUMYQVBZVLVQYHYTY
        LGVMUNZHRYHUUGXFCYQYPXEYLGBIXFVBZUUIUUMUVEUVCYHFUUGXEYHUUFFUUGVNUUKUUGF
        EBUUMJVOVAUVDVPZUVAUUSYHUUHUURYPXFQYLRUFUUIUVAXFBCYOYLYNYMUVGIUVBUULUUN
        WFVRYGXGVSVTYHHGYHHUUTWAYHGUUSWAWBZWCYHUVFUUBQXIUUCYHXEUUGYLBCYQYOYNYMG
        CWDQZUVJVBIUVBUULUUNUUMUVEUUIUVHUVAUUSWEYHUVFHUUBUVIWGWHYJUUAUUDUHUCYRF
        XNYRSZXPUUAYIUUDUVKXOYTHRXNYRXFWIWJUVKXRUUCXIUVKHXQUUBXNYRUGWIWKWLWPWMW
        NXJXTYJUCFXJXSYIXPXHXIXRWOXDWQWRWSWTXAAUUHUUFUUOYDXMSLMNXFBCDEUBUAFUQGI
        JKUVGXBVHAUUHUUFUUPYEYBSLMOXFBCDEUBUCFUQHIJKUVGXBVHXC $.
    $}

    ${
      hbtlem3.r $e |- ( ph -> R e. Ring ) $.
      hbtlem3.i $e |- ( ph -> I e. U ) $.
      hbtlem3.j $e |- ( ph -> J e. U ) $.
      hbtlem3.ij $e |- ( ph -> I C_ J ) $.
      ${
        $d ph a $.  $d I a b $.  $d J a b $.  $d R a b $.  $d X a b $.
        hbtlem3.x $e |- ( ph -> X e. NN0 ) $.
        $( The leading ideal function is monotone.  (Contributed by Stefan
           O'Rear, 31-Mar-2015.) $)
        hbtlem3 $p |- ( ph -> ( ( S ` I ) ` X ) C_ ( ( S ` J ) ` X ) ) $=
          ( vb va cfv wcel cv cdg1 cle wbr cco1 wceq wa wrex cab wss ssrexv syl
          wi ss2abdv crg cn0 eqid hbtlem1 syl3anc 3sstr4d ) AQUAZCUBSZSHUCUDRUA
          HVAUESSUFUGZQFUHZRUIZVCQGUHZRUIZHFDSSZHGDSSZAVDVFRAFGUJVDVFUMOVCQFGUK
          ULUNACUOTZFETHUPTZVHVEUFLMPVBBCDERQFUOHIJKVBUQZURUSAVJGETVKVIVGUFLNPV
          BBCDERQGUOHIJKVLURUSUT $.
      $}
      $d ph a b c d e $.  $d I a b c d e $.  $d I x $.  $d J a b c d e $.
      $d J x $.  $d P a $.  $d R a b c d e $.  $d S x $.  $d b x $.
      hbtlem5.e $e |- ( ph ->
          A. x e. NN0 ( ( S ` J ) ` x ) C_ ( ( S ` I ) ` x ) ) $.
      $( The leading ideal function is strictly monotone.  (Contributed by
         Stefan O'Rear, 1-Apr-2015.) $)
      hbtlem5 $p |- ( ph -> I = J ) $=
        ( wcel cfv clt syl va vb vc vd ve cv cdg1 wbr cn0 wrex cmnf csn cun cbs
        wa wss eqid lidlss sselda deg1cl wo elun cn nnssnn0 cr nn0re arch mpsyl
        ssrexv wceq elsni cc0 0nn0 mnflt0 breq2 rspcev mp2an breq1 rexbidv jaoi
        mpbiri sylbi wi wral c1 caddc co imbi1d ralbidv imbi2d weq fveq2 breq1d
        eleq1 imbi12d cbvralvw bitrdi c0g crg wb adantr deg1lt0 syl2anc lidl0cl
        ply1ring eleq1a sylbid ralrimiva w3a cz 3ad2ant2 simpl1 nn0zd degltp1le
        cle cco1 cab sseq12d rspcva sylan2 adantl simpl hbtlem1 syl3anc 3sstr3d
        3adant3 simpr eqidd fveq1d eqeq2d anbi12d fvex eqeq1 anbi2d elab sseldd
        syl12anc ad2antrr syl22anc mpd sylibr csg cplusg simpll2 ringgrp simprl
        cgrp simplrl grpnpcan simpll1 simplrr simprrl simprrr deg1sublt simpll3
        lidlsubcl lidlacl eqeltrrd rexlimdvaa biimtrid expr 3exp a2d nn0ind rsp
        syl6com com23 imp rexlimdv eqelssd ) AUAGHOAUAUFZHQZUOZUVKDUGRZRZUBUFZS
        UHZUBUIUJZUVKGQZUVMUVOUIUKULZUMZQZUVRUVMUVKCUNRZQZUWBAHUWCUVKAHFQZHUWCU
        PZNUWCHFCUWCUQZJURTZUSZUWCUVNCDUVKUVNUQZIUWGUTTUWBUVOUIQZUVOUVTQZVAUVRU
        VOUIUVTVBUWKUVRUWLVCUIUPUWKUVQUBVCUJZUVRVDUWKUVOVEQUWMUVOVFUVOUBVGTUVQU
        BVCUIVIVHUWLUVOUKVJZUVRUVOUKVKUWNUVRUKUVPSUHZUBUIUJZVLUIQUKVLSUHZUWPVMV
        NUWOUWQUBVLUIUVPVLUKSVOVPVQUWNUVQUWOUBUIUVOUKUVPSVRVSWATVTWBTUVMUVQUVSU
        BUIAUVLUVPUIQZUVQUVSWCZWCAUWRUVLUWSUWRAUWSUAHWDZUVLUWSWCAUVOUCUFZSUHZUV
        SWCZUAHWDZWCAUVOVLSUHZUVSWCZUAHWDZWCAUWTWCZAUDUFZUVNRZUVPWEWFWGZSUHZUXI
        GQZWCZUDHWDZWCUXHUCUBUVPUXAVLVJZUXDUXGAUXPUXCUXFUAHUXPUXBUXEUVSUXAVLUVO
        SVOWHWIWJUCUBWKZUXDUWTAUXQUXCUWSUAHUXQUXBUVQUVSUXAUVPUVOSVOWHWIWJZUXAUX
        KVJZUXDUXOAUXSUXDUVOUXKSUHZUVSWCZUAHWDUXOUXSUXCUYAUAHUXSUXBUXTUVSUXAUXK
        UVOSVOWHWIUYAUXNUAUDHUAUDWKZUXTUXLUVSUXMUYBUVOUXJUXKSUVKUXIUVNWLWMUVKUX
        IGWNWOWPWQWJUXRAUXFUAHUVMUXEUVKCWRRZVJZUVSUVMDWSQZUWDUXEUYDWTAUYEUVLLXA
        UWIUWCUVNCDUVKUYCUWJIUYCUQZUWGXBXCAUYDUVSWCZUVLAUYCGQZUYGACWSQZGFQZUYHA
        UYEUYILCDIXETZMCFGUYCJUYFXDXCUYCGUVKXFTXAXGXHUWRAUWTUXOUWRAUWTUXOUWRAUW
        TXIZUXNUDHUYLUXIHQZUOZUXLUXJUVPXOUHZUXMUYNUXJUWAQZUVPXJQUXLUYOWTUYNUXIU
        WCQZUYPUYLHUWCUXIAUWRUWFUWTUWHXKUSUWCUVNCDUXIUWJIUWGUTTUYNUVPUWRAUWTUYM
        XLXMUXJUVPXNXCUYLUYMUYOUXMUYLUYMUYOUOZUOZUVPUXIXPRZRZUEUFZUVNRZUVPXOUHZ
        UXAUVPVUBXPRZRZVJZUOZUEGUJZUCXQZQZUXMUYSVUHUEHUJZUCXQZVUJVUAUYLVUMVUJUP
        ZUYRUWRAVUNUWTUWRAUOZUVPHERZRZUVPGERZRZVUMVUJAUWRBUFZVUPRZVUTVURRZUPZBU
        IWDVUQVUSUPZPVVCVVDBUVPUIBUBWKVVAVUQVVBVUSVUTUVPVUPWLVUTUVPVURWLXRXSXTV
        UOUYEUWEUWRVUQVUMVJAUYEUWRLYAZAUWEUWRNYAUWRAYBZUVNCDEFUCUEHWSUVPIJKUWJY
        CYDVUOUYEUYJUWRVUSVUJVJVVEAUYJUWRMYAVVFUVNCDEFUCUEGWSUVPIJKUWJYCYDYEYFX
        AUYRVUAVUMQZUYLUYRVUDVUAVUFVJZUOZUEHUJZVVGUYRUYMUYOVUAVUAVJZVVJUYMUYOYB
        UYMUYOYGUYRVUAYHVVIUYOVVKUOUEUXIHUEUDWKZVUDUYOVVHVVKVVLVUCUXJUVPXOVUBUX
        IUVNWLWMVVLVUFVUAVUAVVLUVPVUEUYTVUBUXIXPWLYIYJYKVPYQVULVVJUCVUAUVPUYTYL
        ZUXAVUAVJZVUHVVIUEHVVNVUGVVHVUDUXAVUAVUFYMYNZVSYOUUAYAYPVUKVVIUEGUJZUYS
        UXMVUIVVPUCVUAVVMVVNVUHVVIUEGVVOVSYOUYSVVIUXMUEGUYSVUBGQZVVIUOZUOZUXIVU
        BCUUBRZWGZVUBCUUCRZWGZUXIGVVSCUUGQZUYQVUBUWCQVWCUXIVJVVSUYIVWDVVSAUYIUW
        RAUWTUYRVVRUUDZUYKTZCUUETVVSHUWCUXIVVSAUWFVWEUWHTUYLUYMUYOVVRUUHZYPZVVS
        GUWCVUBVVSAGUWCUPZVWEAUYJVWIMUWCGFCUWGJURTTUYSVVQVVIUUFZYPZUWCVWBCVVTUX
        IVUBUWGVWBUQZVVTUQZUUIYDVVSUYIUYJVWAGQZVVQVWCGQVWFUYLUYJUYRVVRAUWRUYJUW
        TMXKYRVVSVWAUVNRZUVPSUHZVWNVVSUYTUWCVUEUVNCDUXIVUBUVPVVTUWJIUWGVWMUWRAU
        WTUYRVVRUUJVVSAUYEVWELTVWHUYLUYMUYOVVRUUKVWKUYSVVQVUDVVHUULUYTUQVUEUQUY
        SVVQVUDVVHUUMUUNVVSVWAHQZUWTVWPVWNWCZVVSUYIUWEUYMVUBHQVWQVWFVVSAUWEVWEN
        TVWGVVSGHVUBUYLGHUPZUYRVVRAUWRVWSUWTOXKYRVWJYPCFHVVTUXIVUBJVWMUUPYSUWRA
        UWTUYRVVRUUOUWSVWRUAVWAHUVKVWAVJZUVQVWPUVSVWNVWTUVOVWOUVPSUVKVWAUVNWLWM
        UVKVWAGWNWOXSXCYTVWJVWBCFGVWAVUBJVWLUUQYSUURUUSUUTYTUVAXGXHUVBUVCUVDUWS
        UAHUVEUVFUVGUVHUVIYTUVJ $.
    $}

    ${
      $d ph a k $.  $d I a k $.  $d I b c d $.  $d N a $.  $d N b c e $.
      $d R a k $.  $d R b c d $.  $d R e $.  $d S a k $.  $d X a k $.
      $d X b c d $.  $d X e $.  $d b k $.  $d c k $.  $d e k $.
      hbtlem6.n $e |- N = ( RSpan ` P ) $.
      hbtlem6.r $e |- ( ph -> R e. LNoeR ) $.
      hbtlem6.i $e |- ( ph -> I e. U ) $.
      hbtlem6.x $e |- ( ph -> X e. NN0 ) $.
      $( There is a finite set of polynomials matching any single stage of the
         image.  (Contributed by Stefan O'Rear, 1-Apr-2015.) $)
      hbtlem6 $p |- ( ph -> E. k e. ( ~P I i^i Fin )
            ( ( S ` I ) ` X ) C_ ( ( S ` ( N ` k ) ) ` X ) ) $=
        ( vb cfv wss wcel va vc vd ve crsp wceq cpw cfn cin wrex clnr clidl crg
        cv cn0 lnrring syl eqid hbtlem2 syl3anc lnr2i syl2anc wa elfpw cdg1 cle
        wbr crab cco1 cmpt cima wfn crn fvex fnmpti a1i cab hbtlem1 rnmpt fveq2
        simprl breq1d rexrab abbii eqtri eqtr4di adantr sseqtrd simprr fipreima
        wi ssrab2 sstr2 mpi adantl velpw sylibr adantrr elind cbs sstrdi lidlss
        ply1ring sstrd rspcl cres df-ima wral rspssid simprbi ad2antrl sylanbrc
        ssrab resmptd resmpt eqtr4d eqsstrrdi rnss eqsstrid sseqtrrd rspssp jca
        resss sseq1d anbi2d syl5ibcom sylan2b expimpd reximdv2 sseq1 syl5ibrcom
        mpd rexbidv rexlimdva ) AIGDRRZUAUNZCUERZRZUFZUAYOUGUHUIZUJZYOIFUNZHRZD
        RRZSZFGUGZUHUIZUJZACUKTZYOCULRZTZUUANACUMTZGETZIUOTZUUKAUUIUULNCUPUQZOP
        BCDUUJEGIJKLUUJURZUSUTCUUJUAYOYQUUPYQURZVAVBAYSUUHUAYTAYPYTTZVCUUHYSYRU
        UDSZFUUGUJZUURAYPYOSZYPUHTZVCZUUTYPYOVDAUVCVCZQUBUNZCVERZRZIVFVGZUBGVHZ
        IQUNZVIRZRZVJZUUBVKZYPUFZFUVIUGUHUIZUJZUUTUVDUVMUVIVLZYPUVMVMZSUVBUVQUV
        RUVDQUVIUVLUVMIUVKVNUVMURZVOVPUVDYPYOUVSAUVAUVBWAAYOUVSUFUVCAYOUVJUVFRZ
        IVFVGZUCUNUVLUFZVCQGUJZUCVQZUVSAUUIUUMUUNYOUWEUFNOPUVFBCDEUCQGUKIJKLUVF
        URZVRUTUVSUWCQUVIUJZUCVQUWEQUCUVIUVLUVMUVTVSUWGUWDUCUVHUWBUWCQUBGUVEUVJ
        UFUVGUWAIVFUVEUVJUVFVTWBZWCWDWEWFWGWHAUVAUVBWIYPUVIUVMFWJUTUVDUVOUUSFUV
        PUUGAUUBUVPTZUVOVCUUBUUGTZUUSVCZWKUVCAUWIUVOUWKUWIAUUBUVISZUUBUHTZVCZUV
        OUWKWKUUBUVIVDAUWNVCZUWJUVNYQRZUUDSZVCUVOUWKUWOUWJUWQUWOUUFUHUUBAUWLUUB
        UUFTZUWMAUWLVCUUBGSZUWRUWLUWSAUWLUVIGSUWSUVHUBGWLZUUBUVIGWMWNWOFGWPWQWR
        AUWLUWMWIWSUWOUULUUDUUJTZUVNUUDSUWQAUULUWNUUOWGZUWOUULUUCETZUUNUXAUXBUW
        OBUMTZUUBBWTRZSZUXCAUXDUWNAUULUXDUUOBCJXCUQWGZUWOUUBGUXEUWOUUBUVIGAUWLU
        WMWAUWTXAAGUXESZUWNAUUMUXHOUXEGEBUXEURZKXBUQWGXDZUXEBEUUBHMUXIKXEVBZAUU
        NUWNPWGZBCDUUJEUUCIJKLUUPUSUTUWOUVNQUVHUBUUCVHZUVLVJZVMZUUDUWOUVNUVMUUB
        XFZVMZUXOUVMUUBXGUWOUXPUXNSUXQUXOSUWOUXPUXNUUBXFZUXNUWOUXRQUUBUVLVJZUXP
        UWOQUXMUUBUVLUWOUUBUUCSZUVHUBUUBXHZUUBUXMSUWOUXDUXFUXTUXGUXJUXEBUUBHMUX
        IXIVBUWLUYAAUWMUWLUWSUYAUVHUBGUUBXMXJXKUVHUBUUCUUBXMXLXNUWLUXPUXSUFAUWM
        QUVIUUBUVLXOXKXPUXNUUBYCXQUXPUXNXRUQXSUWOUUDUWBUDUNUVLUFZVCQUUCUJZUDVQZ
        UXOUWOUULUXCUUNUUDUYDUFUXBUXKUXLUVFBCDEUDQUUCUMIJKLUWFVRUTUXOUYBQUXMUJZ
        UDVQUYDQUDUXMUVLUXNUXNURVSUYEUYCUDUVHUWBUYBQUBUUCUWHWCWDWEWFXTCUUJUVNUU
        DYQUUQUUPYAUTYBUVOUWQUUSUWJUVOUWPYRUUDUVNYPYQVTYDYEYFYGYHWGYIYLYGYSUUEU
        USFUUGYOYRUUDYJYMYKYNYL $.
    $}
  $}

  ${
    $d P a b c e f $.  $d P g $.  $d R a b c d f $.  $d R e g $.  $d a g $.
    $d c g $.  $d d g $.  $d f g $.
    hbt.p $e |- P = ( Poly1 ` R ) $.
    $( The Hilbert Basis Theorem - the ring of univariate polynomials over a
       Noetherian ring is a Noetherian ring.  (Contributed by Stefan O'Rear,
       4-Apr-2015.) $)
    hbt $p |- ( R e. LNoeR -> P e. LNoeR ) $=
      ( vb vc ve vg wcel cv cfv wceq cfn wral wa cn0 wss eqid ralrimiva syl2anc
      adantr va vd vf clnr crg crsp cbs cpw cin wrex clidl lnrring ply1ring syl
      cldgis cuz cnacs wf c1 caddc islnr3 simprbi hbtlem7 sylan ad2antrr simplr
      co simpr peano2nn0 adantl cle wbr nn0re lep1d hbtlem4 nacsfix syl3anc cc0
      cfz wex fzfi simpll elfznn0 hbtlem6 2fveq3 fveq1d sseq2d sylancr crn cuni
      ac6sfi frn ad2antrl inss1 sstrdi unissd unipw sseqtrdi simpllr sstrd fvex
      lidlss elpw2 sylibr ciun wfn simprl fniunfv inss2 ffvelcdmda sselid iunfi
      3syl eqeltrrd elind ad3antrrr rspcl rspssp cr simplrl nn0red simprr fznn0
      ffn wb mpbir2and simplrr fveq2 fveq2d id fveq12d sseq12d rspcva fvssunirn
      weq sstrid anassrs cz nn0z wi rspssid hbtlem3 eluz2 syl3anbrc leidd breq1
      fveqeq2 expr imbi12d mpd eqsstrd lecasei hbtlem5 eqcomd rspceeqv exlimddv
      rexlimddv islnr2 sylanbrc ) BUDHZAUEHZUAIZDIZAUFJZJZKDAUGJZUHZLUIZUJZUAAU
      KJZMAUDHUUTBUEHZUVABULZABCUMZUNZUUTUVIUAUVJUUTUVBUVJHZNZUBIZUVBBUOJZJZJEI
      ZUVSJZKZUBUVTUPJZMZUVIEOUVPBUKJZBUGJZUQJHZOUWEUVSURZUVCUVSJUVCUSUTVGZUVSJ
      PZDOMUWDEOUJUUTUWGUVOUUTUVKUWGUWFBUWEUWFQUWEQZVAVBTUUTUVKUVOUWHUVLABUVRUW
      EUVJUVBCUVJQZUVRQZUWKVCVDUVPUWJDOUVPUVCOHZNABUVRUVJUVBUVCUWICUWLUWMUUTUVK
      UVOUWNUVLVEUUTUVOUWNVFUVPUWNVHUWNUWIOHUVPUVCVIVJUWNUVCUWIVKVLUVPUWNUVCUVC
      VMVNVJVORDEUBUWEUVSUWFVPVQUVPUVTOHZUWDNZNZVRUVTVSVGZUVBUHZLUIZUCIZURZFIZU
      VSJZUXCUXCUXAJZUVDJZUVRJZJZPZFUWRMZNZUVIUCUVPUXKUCVTZUWPUVPUWRLHZUXDUXCUV
      EUVRJZJZPZDUWTUJZFUWRMUXLVRUVTWAZUVPUXQFUWRUVPUXCUWRHZNABUVRUVJDUVBUVDUXC
      CUWLUWMUVDQZUUTUVOUXSWBUUTUVOUXSVFUXSUXCOHUVPUXCUVTWCVJWDRUXPUXIFDUWRUWTU
      CUVCUXEKZUXOUXHUXDUYAUXCUXNUXGUVCUXEUVRUVDWEWFWGWKWHTUWQUXKNZUXAWIZWJZUVH
      HUVBUYDUVDJZKUVIUYBUVGLUYDUYBUYDUVFPZUYDUVGHUYBUYDUVBUVFUYBUYDUWSWJUVBUYB
      UYCUWSUYBUYCUWTUWSUXBUYCUWTPUWQUXJUWRUWTUXAWLWMUWSLWNWOWPUVBWQWRZUYBUVOUV
      BUVFPUUTUVOUWPUXKWSZUVFUVBUVJAUVFQZUWLXBUNWTZUYDUVFAUGXAXCXDUYBGUWRGIZUXA
      JZXEZUYDLUYBUXBUXAUWRXFUYMUYDKUWQUXBUXJXGZUWRUWTUXAYDGUWRUXAXHXMUYBUXMUYL
      LHZGUWRMUYMLHUXRUYBUYOGUWRUYBUYKUWRHZNUWTLUYLUWSLXIUYBUWRUWTUYKUXAUYNXJXK
      RGUWRUYLXLWHXNXOUYBUYEUVBUYBGABUVRUVJUYEUVBCUWLUWMUUTUVKUVOUWPUXKUVLXPZUY
      BUVAUYFUYEUVJHZUUTUVAUVOUWPUXKUVNXPZUYJUVFAUVJUYDUVDUXTUYIUWLXQSZUYHUYBUV
      AUVOUYDUVBPUYEUVBPUYSUYHUYGAUVJUYDUVBUVDUXTUWLXRVQUYBUYKUVSJZUYKUYEUVRJZJ
      ZPZGOUYBUYKOHZNZVUDUYKUVTVUEUYKXSHUYBUYKVMVJVUFUVTUYBUWOVUEUVPUWOUWDUXKXT
      ZTYAUYBVUEUYKUVTVKVLZVUDUYBVUEVUHNZNZVUAUYKUYLUVDJZUVRJZJZVUCVUJUYPUXJVUA
      VUMPZVUJUYPVUEVUHUYBVUEVUHXGZUYBVUEVUHYBVUJUWOUYPVUIYEUYBUWOVUIVUGTUYKUVT
      YCUNYFUWQUXBUXJVUIYGUXIVUNFUYKUWRFGYOZUXDVUAUXHVUMUXCUYKUVSYHVUPUXCUYKUXG
      VULVUPUXFVUKUVRUXCUYKUVDUXAWEYIVUPYJYKYLYMSVUJABUVRUVJVUKUYEUYKCUWLUWMUYB
      UVKVUIUYQTUYBVUKUVJHZVUIUYBUVAUYLUVFPVUQUYSUYBUYLUYDUVFUXAUYKYNZUYJYPUVFA
      UVJUYLUVDUXTUYIUWLXQSTUYBUYRVUIUYTTZVUJUVAUYRUYLUYEPVUKUYEPUYBUVAVUIUYBUV
      KUVAUYQUVMUNTVUSVUJUYLUYDUYEVURUYBUYDUYEPZVUIUYBUVAUYFVUTUYSUYJUVFAUYDUVD
      UXTUYIUUASTYPAUVJUYLUYEUVDUXTUWLXRVQVUOUUBWTZYQUYBVUEUVTUYKVKVLZVUDUYBVUE
      VVBNZNZVUAUWAVUCVVDUYKUWCHZUWDVUAUWAKZUYBUWOVVCVVEVUGUWOVVCNUVTYRHZUYKYRH
      ZVVBVVEUWOVVGVVCUVTYSTVUEVVHUWOVVBUYKYSWMUWOVUEVVBYBUVTUYKUUCUUDVDUWQUWDU
      XKVVCUVPUWOUWDYBVEUWBVVFUBUYKUWCUVQUYKUWAUVSUUGYMSVVDUWAUVTVUBJZVUCUYBUWA
      VVIPZVVCUYBUVTUVTVKVLZVVJUYBUVTUYBUVTVUGYAUUEUYBUWOVUHVUDYTZGOMVVKVVJYTZV
      UGUYBVVLGOUYBVUEVUHVUDVVAUUHRVVLVVMGUVTOGEYOZVUHVVKVUDVVJUYKUVTUVTVKUUFVV
      NVUAUWAVUCVVIUYKUVTUVSYHUYKUVTVUBYHYLUUIYMSUUJTVVDABUVRUVJUYEUVTUYKCUWLUW
      MUYBUVKVVCUYQTUYBUYRVVCUYTTUYBUWOVVCVUGTUYBVUEVVBXGUYBVUEVVBYBVOWTUUKYQUU
      LRUUMUUNDUYDUVHUVEUYEUVBUVCUYDUVDYHUUOSUUPUUQRUVFAUVJDUAUVDUYIUWLUXTUURUU
      S $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Additional material on polynomials [DEPRECATED]
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c Monic Poly< $.

  $( Extend class notation with the class of monic polynomials. $)
  cmnc $a class Monic $.

  $( Extend class notation with the class of limited-degree polynomials. $)
  cplylt $a class Poly< $.

  ${
    $d s p x $.

    $( Define the class of monic polynomials.  (Contributed by Stefan O'Rear,
       5-Dec-2014.) $)
    df-mnc $a |- Monic = ( s e. ~P CC |-> { p e. ( Poly ` s ) |
        ( ( coeff ` p ) ` ( deg ` p ) ) = 1 } ) $.

    $( Define the class of limited-degree polynomials.  (Contributed by Stefan
       O'Rear, 8-Dec-2014.) $)
    df-plylt $a |- Poly< = ( s e. ~P CC , x e. NN0 |-> { p e. ( Poly ` s ) |
        ( p = 0p \/ ( deg ` p ) < x ) } ) $.
  $}

  ${
    dgrsub2.a $e |- N = ( deg ` F ) $.
    $( Subtracting two polynomials with the same degree and top coefficient
       gives a polynomial of strictly lower degree.  (Contributed by Stefan
       O'Rear, 25-Nov-2014.) $)
    dgrsub2 $p |- ( ( ( F e. ( Poly ` S ) /\ G e. ( Poly ` T ) ) /\
          ( ( deg ` G ) = N /\ N e. NN /\
            ( ( coeff ` F ) ` N ) = ( ( coeff ` G ) ` N ) ) ) ->
        ( deg ` ( F oF - G ) ) < N ) $=
      ( cply cfv wcel wa cdgr wceq ccoe cmin clt wbr cle cc eqid cn0 cn w3a cof
      co c0p wi simpr2 cc0 nngt0 eqbrtrid fveq2 breq1d syl5ibrcom syl wo plyssc
      dgr0 cif sseli dgrsub syl2an adantr simpr1 eqcomi a1i ifeq12d ifid eqtrdi
      breqtrd coesub fveq1d nnnn0d cvv coef3 ad2antrr ffnd ad2antlr nn0ex inidm
      wf simplr3 eqidd ofval mpdan ffvelcdmd subidd wb plysubcl dgrlt mpbir2and
      3eqtrd syl2anc ord pm2.61d ) CAGHZIZDBGHZIZJZDKHZELZEUAIZECMHZHEDMHZHZLZU
      BZJZCDNUCZUDZUELZXJKHZEOPZXHXBXKXMUFWSXAXBXFUGZXBXMXKUEKHZEOPXBXOUHEOUQEU
      IUJXKXLXOEOXJUEKUKULUMUNXHXKXMXHXKXMUOZXLEQPZEXJMHZHZUHLZXHXLCKHZWTQPZWTY
      AURZEQWSXLYCQPZXGWPCRGHZIZDYEIZYDWRWOYECAUPUSZWQYEDBUPUSZRCDYAWTYASWTSUTV
      AVBXHYCYBEEUREXHYBWTEYAEWSXAXBXFVCYAELXHEYAFVDVEVFYBEVGVHVIXHXSEXCXDXIUDZ
      HZXEXENUDZUHXHEXRYJWSXRYJLZXGWPYFYGYMWRYHYIXCXDRCDXCSZXDSZVJVAVBVKXHETIZY
      KYLLXHEXNVLZXHTTXEXENTXCXDVMVMEXHTRXCWPTRXCVTWRXGXCACYNVNVOVPXHTRXDWRTRXD
      VTWPXGXDBDYOVNVQZVPTVMIXHVRVEZYSTVSXAXBXFWSYPWAXHYPJXEWBWCWDXHXEXHTREXDYR
      YQWEWFWKXHXJYEIZYPXPXQXTJWGWSYTXGWPYFYGYTWRYHYIRCDWHVAVBYQXRRXJEXLXLSXRSW
      IWLWJWMWN $.
  $}

  ${
    $d S s p $.  $d P s p $.

    $( Property of a monic polynomial.  (Contributed by Stefan O'Rear,
       5-Dec-2014.) $)
    elmnc $p |- ( P e. ( Monic ` S ) <-> ( P e. ( Poly ` S ) /\
          ( ( coeff ` P ) ` ( deg ` P ) ) = 1 ) ) $=
      ( vs vp cmnc cfv wcel cc wss cply cdgr ccoe c1 wceq wa cdm cpw crab fveq2
      cv df-mnc dmmptss elfvdm sselid elpwid plybss adantr cnex elpw2 rabeq syl
      fvex rabex fvmpt sylbir eleq2d fveq12d eqeq1d elrab bitrdi pm5.21nii ) AB
      EFZGZBHIZABJFZGZAKFZALFZFZMNZOZVCBHVCEPHQZBCVLDTZKFZVMLFZFZMNZDCTZJFZRZEC
      DUAZUBABEUCUDUEVFVDVJBAUFUGVDVCAVQDVERZGVKVDVBWBAVDBVLGVBWBNBHUHUICBVTWBV
      LEVRBNVSVENVTWBNVRBJSVQDVSVEUJUKWAVQDVEBJULUMUNUOUPVQVJDAVEVMANZVPVIMWCVN
      VGVOVHVMALSVMAKSUQURUSUTVA $.

    $( A monic polynomial is a polynomial.  (Contributed by Stefan O'Rear,
       5-Dec-2014.) $)
    mncply $p |- ( P e. ( Monic ` S ) -> P e. ( Poly ` S ) ) $=
      ( cmnc cfv wcel cply cdgr ccoe c1 wceq elmnc simplbi ) ABCDEABFDEAGDAHDDI
      JABKL $.

    $( A monic polynomial has leading coefficient 1.  (Contributed by Stefan
       O'Rear, 5-Dec-2014.) $)
    mnccoe $p |- ( P e. ( Monic ` S )
        -> ( ( coeff ` P ) ` ( deg ` P ) ) = 1 ) $=
      ( cmnc cfv wcel cply cdgr ccoe c1 wceq elmnc simprbi ) ABCDEABFDEAGDAHDDI
      JABKL $.

    $( A monic polynomial is not zero.  (Contributed by Stefan O'Rear,
       5-Dec-2014.) $)
    mncn0 $p |- ( P e. ( Monic ` S ) -> P =/= 0p ) $=
      ( cmnc cfv wcel cdgr ccoe wceq c0p wne mnccoe cc0 cn0 csn cxp coe0 fveq1i
      c1 dgr0 fveq2 0nn0 eqeltri c0ex fvconst2 ax-mp eqtri 0ne1 eqnetri fveq12d
      neeq1d mpbiri necon2i syl ) ABCDEAFDZAGDZDZRHAIJABKAIUPRAIHZUPRJIFDZIGDZD
      ZRJUTLRUTURMLNOZDZLURUSVAPQURMEVBLHURLMSUAUBMLURUCUDUEUFUGUHUQUPUTRUQUNUR
      UOUSAIGTAIFTUIUJUKULUM $.
  $}

  $(
  @{
    mncdiv.s @e |- ( ph -> S e. ( SubRing ` CCfld ) ) @.
    mncdiv.f @e |- ( ph -> F e. ( Poly ` S ) ) @.
    mncdiv.g @e |- ( ph -> G e. ( Monic ` S ) ) @.
    @( Monic version of polynomial division algorithm, does not require
       division over the base ring. @)
    mncdivex @p |- ( ph -> E. q e. ( Poly ` S ) ( F oF - ( G oF x. q ) ) e.
          ( S Poly< ( deg ` G ) ) ) @=
      ? @.
  @}
  $)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Degree and minimal polynomial of algebraic numbers
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c degAA minPolyAA $.

  $( Extend class notation to include the degree function for algebraic
     numbers. $)
  cdgraa $a class degAA $.

  $( Extend class notation to include the minimal polynomial for an algebraic
     number. $)
  cmpaa $a class minPolyAA $.

  ${
    $d x d p $.
    $( Define the degree of an algebraic number as the smallest degree of any
       nonzero polynomial which has said number as a root.  (Contributed by
       Stefan O'Rear, 25-Nov-2014.)  (Revised by AV, 29-Sep-2020.) $)
    df-dgraa $a |- degAA = ( x e. AA |-> inf ( { d e. NN |
        E. p e. ( ( Poly ` QQ ) \ { 0p } ) ( ( deg ` p ) = d /\
          ( p ` x ) = 0 ) } , RR , < ) ) $.

    $( Define the minimal polynomial of an algebraic number as the unique monic
       polynomial which achieves the minimum of ` degAA ` .  (Contributed by
       Stefan O'Rear, 25-Nov-2014.) $)
    df-mpaa $a |- minPolyAA = ( x e. AA |-> ( iota_ p e. ( Poly ` QQ )
        ( ( deg ` p ) = ( degAA ` x ) /\ ( p ` x ) = 0 /\
          ( ( coeff ` p ) ` ( degAA ` x ) ) = 1 ) ) ) $.
  $}

  $(
  @{
    @d x A a b @.  @d x B a b @.
    plydeg1.a @e |- F = ( x e. CC |-> ( ( A x. x ) + B ) ) @.
    @( A polynomial with 2 terms. @)
    plydeg1a @p |- ( ( A e. S /\ B e. S /\ S C_ CC ) -> F e. ( Poly ` S ) ) @=
      ? @.

    @( Degree of a polynomial with 2 terms. @)
    plydeg1b @p |- ( ( A e. CC /\ B e. CC /\ A =/= 0 ) -> ( deg ` A ) = 1 ) @=
      ? @.
  @}
  $)

  ${
    $d A d p a b c $.  $d P d p a b c $.
    $( Value of the degree function on an algebraic number.  (Contributed by
       Stefan O'Rear, 25-Nov-2014.)  (Revised by AV, 29-Sep-2020.) $)
    dgraaval $p |- ( A e. AA -> ( degAA ` A ) = inf ( { d e. NN |
        E. p e. ( ( Poly ` QQ ) \ { 0p } ) ( ( deg ` p ) = d /\
          ( p ` A ) = 0 ) } , RR , < ) ) $=
      ( va cv cdgr cfv wceq cc0 wa cq cply c0p csn wrex cn crab cr clt cinf caa
      cdif cdgraa fveqeq2 anbi2d rexbidv rabbidv infeq1d df-dgraa infex fvmpt
      ltso ) DABEZFGCEHZDEZUMGIHZJZBKLGMNUBZOZCPQZRSTUNAUMGIHZJZBUROZCPQZRSTUAU
      CUOAHZRUTVDSVEUSVCCPVEUQVBBURVEUPVAUNUOAIUMUDUEUFUGUHDBCUIRVDSULUJUK $.

    $( Properties of the degree of an algebraic number.  (Contributed by Stefan
       O'Rear, 25-Nov-2014.)  (Proof shortened by AV, 29-Sep-2020.) $)
    dgraalem $p |- ( A e. AA -> ( ( degAA ` A ) e. NN /\
        E. p e. ( ( Poly ` QQ ) \ { 0p } ) ( ( deg ` p ) = ( degAA ` A ) /\
          ( p ` A ) = 0 ) ) ) $=
      ( va vb caa wcel cfv cv cdgr wceq cc0 wa cq c0p wrex cn wne eqeq2 anbi1d
      c1 cdgraa cply csn cdif crab cr clt cinf dgraaval cuz wss c0 nnuz sseqtri
      ssrab2 cc wi eldifsn biimpi ad2antrr simpr simplr dgrnznn syl12anc simpll
      jctil fveqeq2 fveq1 eqeq1d anbi12d rspc2ev syl3anc rexlimiva impcom elqaa
      eqid ex rabn0 3imtr4i infssuzcl sylancr eqeltrd rexbidv elrab sylib ) AEF
      ZAUAGZBHZIGZCHZJZAWHGZKJZLZBMUBGZNUCUDZOZCPUEZFWGPFWIWGJZWMLZBWPOZLWFWGWR
      UFUGUHZWRABCUIWFWRTUJGZUKWRULQZXBWRFWRPXCWQCPUOUMUNAUPFZADHZGZKJZDWPOZLWQ
      CPOZWFXDXIXEXJXHXEXJUQDWPXFWPFZXHLZXEXJXLXELZXFIGZPFZXKXNXNJZXHLZXJXMXFWO
      FXFNQLZXEXHXOXKXRXHXEXKXRXFWONURUSUTXLXEVAXKXHXEVBZAXFMVCVDXKXHXEVEXMXHXP
      XSXNVPVFWNXQWIXNJZWMLCBXNXFPWPWJXNJWKXTWMWJXNWIRSWHXFJZXTXPWMXHWHXFXNIVGY
      AWLXGKAWHXFVHVIVJVKVLVQVMVNADVOWQCPVRVSWRTVTWAWBWQXACWGPWJWGJZWNWTBWPYBWK
      WSWMWJWGWIRSWCWDWE $.

    $( Closure of the degree function on algebraic numbers.  (Contributed by
       Stefan O'Rear, 25-Nov-2014.) $)
    dgraacl $p |- ( A e. AA -> ( degAA ` A ) e. NN ) $=
      ( va caa wcel cdgraa cfv cn cv cdgr wceq cc0 wa cq cply c0p csn cdif wrex
      dgraalem simpld ) ACDAEFZGDBHZIFUAJAUBFKJLBMNFOPQRABST $.

    $( Degree function on algebraic numbers is a function.  (Contributed by
       Stefan O'Rear, 25-Nov-2014.)  (Proof shortened by AV, 29-Sep-2020.) $)
    dgraaf $p |- degAA : AA --> NN $=
      ( va vp vb caa cn cdgraa wf wfn cv cfv wcel wral cdgr wceq cc0 wa cq cply
      cr clt c0p csn cdif wrex crab cinf ltso infex df-dgraa dgraacl rgen ffnfv
      fnmpti mpbir2an ) DEFGFDHAIZFJEKZADLADBIZMJCINUOUQJONPBQRJUAUBUCUDCEUEZST
      UFFSURTUGUHABCUIUMUPADUOUJUKADEFULUN $.

    $( Upper bound on degree of an algebraic number.  (Contributed by Stefan
       O'Rear, 25-Nov-2014.)  (Proof shortened by AV, 29-Sep-2020.) $)
    dgraaub $p |- ( ( ( P e. ( Poly ` QQ ) /\ P =/= 0p ) /\ ( A e. CC /\
          ( P ` A ) = 0 ) ) -> ( degAA ` A ) <_ ( deg ` P ) ) $=
      ( vb va cq cfv wcel c0p wa cc0 wceq cv cdgr wrex cle fveq1 eqeq1d syl2anc
      cn rspcev cply wne cc cdgraa csn cdif crab cr clt cinf caa simprl eldifsn
      biranri simprr elqaa sylanbrc dgraaval syl c1 cuz wss ssrab2 nnuz sseqtri
      wbr dgrnznn eqid jctil fveqeq2 anbi12d eqeq2 anbi1d rexbidv elrab sylancr
      infssuzle eqbrtrd ) BEUAFZGBHUBIZAUCGZABFZJKZIZIZAUDFZCLZMFZDLZKZAWGFZJKZ
      IZCVSHUEUFZNZDSUGZUHUIUJZBMFZOWEAUKGZWFWQKWEWAAWIFZJKZDWNNZWSVTWAWCULWEBW
      NGZWCXBXCVTWDBVSHUMUNZVTWAWCUOZXAWCDBWNWIBKWTWBJAWIBPQTRADUPUQACDURUSWEWP
      UTVAFZVBWRWPGZWQWROVFWPSXFWODSVCVDVEWEWRSGWHWRKZWLIZCWNNZXGABEVGWEXCWRWRK
      ZWCIZXJXDWEWCXKXEWRVHVIXIXLCBWNWGBKZXHXKWLWCWGBWRMVJXMWKWBJAWGBPQVKTRWOXJ
      DWRSWIWRKZWMXICWNXNWJXHWLWIWRWHVLVMVNVOUQWRWPUTVQVPVR $.

    $( A rational polynomial of degree less than an algebraic number cannot be
       zero at that number unless it is the zero polynomial.  (Contributed by
       Stefan O'Rear, 25-Nov-2014.) $)
    dgraa0p $p |- ( ( A e. AA /\ P e. ( Poly ` QQ ) /\
          ( deg ` P ) < ( degAA ` A ) ) -> ( ( P ` A ) = 0 <-> P = 0p ) ) $=
      ( caa wcel cq cply cfv cdgr cdgraa clt wbr w3a cc0 wceq c0p wn simpl2 syl
      wa simpl1 wne cle simpl3 cn0 dgrcl nn0red cn nnred ltnled mpbid cc simprl
      dgraacl aacn simprr dgraaub syl22anc expr mtod ex necon4ad wi 0pval fveq1
      eqeq1d syl5ibrcom 3ad2ant1 impbid ) ACDZBEFGDZBHGZAIGZJKZLZABGZMNZBONZVNV
      PBOVNBOUAZVPPVNVRSZVPVLVKUBKZVSVMVTPVIVJVMVRUCVSVKVLVSVKVSVJVKUDDVIVJVMVR
      QEBUERUFVSVLVSVIVLUGDVIVJVMVRTAUMRUHUIUJVNVRVPVTVNVRVPSZSZVJVRAUKDZVPVTVI
      VJVMWAQVNVRVPULWBVIWCVIVJVMWATAUNZRVNVRVPUOABUPUQURUSUTVAVIVJVQVPVBVMVIVP
      VQAOGZMNZVIWCWFWDAVCRVQVOWEMABOVDVEVFVGVH $.

    $(
    @( Degree of a rational number. @)
    dgraaq @p |- ( A e. QQ -> ( degAA ` A ) = 1 ) @=
      ( va cq wcel cdgraa cfv c1 cle wbr wceq cc cneg cv cmul co caddc cmpt cc0
      oveq1d syl cdgr cply c0p wne qcn oveq2 eqid ovex fvmpt mulm1 negcl addcom
      syl2anc negid 3eqtrd eqtrd dgraaub syl22anc breqtrd cn wb caa qaa dgraacl
      nnle1eq1 mpbid ) ACDZAEFZGHIZVHGJZVGVHBKGLZBMZNOZAPOZQZUAFZGHVGVOCUBFDVOU
      CUDAKDZAVOFZRJVHVPHI??AUEZVGVRVKANOZAPOZRVGVQVRWAJVSBAVNWAKVOVLAJVMVTAPVL
      AVKNUFSVOUGVTAPUHUITVGWAALZAPOZAWBPOZRVGVTWBAPVGVQVTWBJVSAUJTSVGWBKDZVQWC
      WDJVGVQWEVSAUKTVSWBAULUMVGVQWDRJVSAUNTUOUPAVOUQUR?USVGVHUTDZVIVJVAVGAVBDW
      FAVCAVDTVHVETVF @.
      @( [25-Nov-2014] @)
    $)

    $( An algebraic number has exactly one monic polynomial of the least
       degree.  (Contributed by Stefan O'Rear, 25-Nov-2014.) $)
    mpaaeu $p |- ( A e. AA -> E! p e. ( Poly ` QQ ) ( ( deg ` p ) =
          ( degAA ` A ) /\ ( p ` A ) = 0 /\
        ( ( coeff ` p ) ` ( degAA ` A ) ) = 1 ) ) $=
      ( va wcel cdgr cfv wceq cc0 ccoe c1 cq wa c0p cc cmul cn0 ad2antlr adantl
      co cvv vb vc caa cdgraa w3a cply wrex weq wral wreu csn cdif cdiv cxp cof
      cv wi wss qsscn wne wf eldifi cz zssq sselii eqid coef2 sylancl dgrcl syl
      0z ffvelcdmd eldifsni wb dgreq0 necon3bid qreccl syl2anc plyconst sylancr
      mpbid simpl simpr caddc qaddcl qmulcl plymul coef3 reccld recne0d dgrmulc
      syl3anc eqtrd aacn ad2antrr wfn ovex fnconstg mp1i plyf ffn 3syl cnex a1i
      simprl inidm fvconst2 simplrr ofval mpdan mul01d coemulc fveq1d cn nnnn0d
      dgraacl ffnd nn0ex simplrl eqcomd fveq2d recid2d 3eqtrd fveqeq2 3anbi123d
      fveq1 eqeq1d fveq2 rspcev syl13anc dgraalem simprd r19.29a cmin sylan2 ex
      simp2 eqtrdi clt wbr anim12i 0m0e0 impl simpll cneg 1z qnegcl mp2b plysub
      com12 zq simprr1 simprl1 eqeltrd simprl3 simprr3 3eqtr4d dgrsub2 syl23anc
      eqtr4d breqtrd dgraa0p df-0p ofsubeq0 mp3an1 syl2an ralrimivva sylanbrc
      reu4 ) AUCDZBUPZEFZAUDFZGZAUVKFZHGZUVMUVKIFZFZJGZUEZBKUFFZUGZUVTCUPZEFZUV
      MGZAUWCFZHGZUVMUWCIFZFZJGZUEZLZBCUHZUQZCUWAUIBUWAUIUVTBUWAUJUVJUWEUWGLZUW
      BCUWAMUKZULZUVJUWCUWQDZLZUWOLZNJUWDUWHFZUMSZUKZUNZUWCOUOZSZUWADZUXFEFZUVM
      GZAUXFFZHGZUVMUXFIFZFZJGZUWBUWTUXDUWADZUWCUWADZUXGUWTKNURUXBKDZUXOUSUWTUX
      AKDUXAHUTZUXQUWTPKUWDUWHUWTUXPHKDPKUWHVAUWRUXPUVJUWOUWCUWAUWPVBQZVCKHVDVK
      VEUWHKUWCUWHVFZVGVHUWTUXPUWDPDUXSKUWCVIVJZVLUWTUWCMUTZUXRUWRUYBUVJUWOUWCU
      WAMVMQUWTUXPUYBUXRVNUXSUXPUWCMUXAHUWHKUWCUWDUWDVFUXTVOVPVJWAZUXAVQVRUXBKV
      SVTUXSUXOUXPLZUAUBKUXDUWCUXOUXPWBUXOUXPWCUAUPZKDUBUPZKDLZUYEUYFWDSKDZUYDU
      YEUYFWEZRUYGUYEUYFOSKDZUYDUYEUYFWFZRWGVRUWTUXHUWDUVMUWTUXBNDZUXBHUTUXPUXH
      UWDGUWTUXAUWTPNUWDUWHUWTUXPPNUWHVAUXSUWHKUWCUXTWHVJZUYAVLZUYCWIZUWTUXAUYN
      UYCWJUXSUXBKUWCWKWLUWSUWEUWGXEWMUWTUXJUXBHOSZHUWTANDZUXJUYPGUVJUYQUWRUWOA
      WNZWOUWTNNUXBHONUXDUWCTTAUXBTDZUXDNWPUWTJUXAUMWQZNUXBTWRWSUWTUXPNNUWCVAZU
      WCNWPZUXSKUWCWTZNNUWCXAXBNTDZUWTXCXDZVUENXFZUYQAUXDFUXBGUWTNUXBAUYTXGRUWS
      UWEUWGUYQXHXIXJUWTUXBUYOXKWMUWTUXMUVMPUXCUNZUWHUXESZFZUXBUXAOSZJUWTUVMUXL
      VUHUWTUYLUXPUXLVUHGUYOUXSUXBKUWCXLVRXMUWTUVMPDZVUIVUJGUWTUVMUVJUVMXNDZUWR
      UWOAXPZWOXOUWTPPUXBUXAOPVUGUWHTTUVMUYSVUGPWPUWTUYTPUXBTWRWSUWTPNUWHUYMXQP
      TDUWTXRXDZVUNPXFVUKUVMVUGFUXBGUWTPUXBUVMUYTXGRUWTVUKLZUVMUWDUWHVUOUWDUVMU
      WSUWEUWGVUKXSXTYAXIXJUWTUXAUYNUYCYBYCUVTUXIUXKUXNUEBUXFUWAUVKUXFGZUVNUXIU
      VPUXKUVSUXNUVKUXFUVMEYDVUPUVOUXJHAUVKUXFYFYGVUPUVRUXMJVUPUVMUVQUXLUVKUXFI
      YHXMYGYEYIYJUVJVULUWOCUWQUGACYKYLYMUVJUWNBCUWAUWAUVJUVKUWADZUXPLZLZUWLUWM
      VUSUWLLZUVKUWCYNUOSZNHUKUNZGZUWMVUTVVAMVVBVUTAVVAFZHGZVVAMGZUVJVURUWLVVEV
      URUWLLUVJVVEUWLVURUVPUWGLZUVJVVEUQUVTUVPUWKUWGUVNUVPUVSYQUWEUWGUWJYQUUAVU
      RVVGLZUVJVVEVVHUVJLVVDHHYNSZHUVJVVHUYQVVDVVIGUYRVVHNNHHYNNUVKUWCTTAVUQUVK
      NWPUXPVVGVUQNNUVKKUVKWTZXQWOUXPVUBVUQVVGUXPNNUWCVUCXQQVUDVVHXCXDZVVKVUFVU
      RUVPUWGUYQXSVURUVPUWGUYQXHXIYOUUBYRYPYOUUJUUCVUTUVJVVAUWADZVVAEFZUVMYSYTV
      VEVVFVNUVJVURUWLUUDVURVVLUVJUWLVURUAUBKUVKUWCVUQUXPWBVUQUXPWCUYGUYHVURUYI
      RUYGUYJVURUYKRJUUEKDZVURJVCDJKDVVNUUFJUUKJUUGUUHXDUUIQVUTVVMUVLUVMYSVUTVU
      QUXPUWDUVLGUVLXNDUVLUVQFZUVLUWHFZGVVMUVLYSYTUVJVUQUXPUWLXSUVJVUQUXPUWLXHV
      UTUWDUVMUVLUWEUWGUWJUVTVUSUULUVNUVPUVSUWKVUSUUMZUUTVUTUVLUVMXNVVQUVJVULVU
      RUWLVUMWOUUNVUTUVRJVVOVVPUVNUVPUVSUWKVUSUUOVUTUVLUVMUVQVVQYAVUTVVPUWIJVUT
      UVLUVMUWHVVQYAUWEUWGUWJUVTVUSUUPWMUUQKKUVKUWCUVLUVLVFUURUUSVVQUVAAVVAUVBW
      LWAUVCYRVURVVCUWMVNZUVJUWLVUQNNUVKVAZVUAVVRUXPVVJVUCVUDVVSVUAVVRXCNUVKUWC
      TUVDUVEUVFQWAYPUVGUVTUWKBCUWAUWMUVNUWEUVPUWGUVSUWJUVKUWCUVMEYDUWMUVOUWFHA
      UVKUWCYFYGUWMUVRUWIJUWMUVMUVQUWHUVKUWCIYHXMYGYEUVIUVH $.

    $( Value of the minimal polynomial of an algebraic number.  (Contributed by
       Stefan O'Rear, 25-Nov-2014.) $)
    mpaaval $p |- ( A e. AA -> ( minPolyAA ` A ) = ( iota_ p e. ( Poly ` QQ )
        ( ( deg ` p ) = ( degAA ` A ) /\ ( p ` A ) = 0 /\
          ( ( coeff ` p ) ` ( degAA ` A ) ) = 1 ) ) ) $=
      ( va cv cdgr cfv cdgraa wceq cc0 ccoe c1 w3a cq cply crio caa cmpaa fveq2
      eqeq2d fveqeq2 2fveq3 eqeq1d 3anbi123d riotabidv df-mpaa riotaex fvmpt )
      CABDZEFZCDZGFZHZUJUHFIHZUKUHJFZFZKHZLZBMNFZOUIAGFZHZAUHFIHZUSUNFZKHZLZBUR
      OPQUJAHZUQVDBURVEULUTUMVAUPVCVEUKUSUIUJAGRSUJAIUHTVEUOVBKUJAUNGUAUBUCUDCB
      UEVDBURUFUG $.

    $( Properties of the minimal polynomial of an algebraic number.
       (Contributed by Stefan O'Rear, 25-Nov-2014.) $)
    mpaalem $p |- ( A e. AA -> ( ( minPolyAA ` A ) e. ( Poly ` QQ ) /\
        ( ( deg ` ( minPolyAA ` A ) ) = ( degAA ` A ) /\
          ( ( minPolyAA ` A ) ` A ) = 0 /\
          ( ( coeff ` ( minPolyAA ` A ) ) ` ( degAA ` A ) ) = 1 ) ) ) $=
      ( vp caa wcel cmpaa cfv cv cdgr cdgraa wceq cc0 ccoe c1 cq cply crab crio
      w3a wa eqeq1d mpaaval wreu mpaaeu riotacl2 syl eqeltrd fveq1 fveq2 fveq1d
      fveqeq2 3anbi123d elrab sylib ) ACDZAEFZBGZHFAIFZJZAUPFZKJZUQUPLFZFZMJZRZ
      BNOFZPZDUOVEDUOHFUQJZAUOFZKJZUQUOLFZFZMJZRZSUNUOVDBVEQZVFABUAUNVDBVEUBVNV
      FDABUCVDBVEUDUEUFVDVMBUOVEUPUOJZURVGUTVIVCVLUPUOUQHUJVOUSVHKAUPUOUGTVOVBV
      KMVOUQVAVJUPUOLUHUITUKULUM $.

    $( Minimal polynomial is a polynomial.  (Contributed by Stefan O'Rear,
       25-Nov-2014.) $)
    mpaacl $p |- ( A e. AA -> ( minPolyAA ` A ) e. ( Poly ` QQ ) ) $=
      ( caa wcel cmpaa cfv cq cply cdgr cdgraa wceq cc0 ccoe w3a mpaalem simpld
      c1 ) ABCADEZFGECQHEAIEZJAQEKJRQLEEPJMANO $.

    $( Minimal polynomial has degree the degree of the number.  (Contributed by
       Stefan O'Rear, 25-Nov-2014.) $)
    mpaadgr $p |- ( A e. AA -> ( deg ` ( minPolyAA ` A ) ) = ( degAA ` A ) ) $=
      ( caa wcel cmpaa cfv cq cply cdgr cdgraa wceq cc0 ccoe w3a mpaalem simpr1
      c1 wa syl ) ABCADEZFGECZSHEAIEZJZASEKJZUASLEEPJZMQUBANTUBUCUDOR $.

    $( The minimal polynomial of an algebraic number has the number as a root.
       (Contributed by Stefan O'Rear, 25-Nov-2014.) $)
    mpaaroot $p |- ( A e. AA -> ( ( minPolyAA ` A ) ` A ) = 0 ) $=
      ( caa wcel cmpaa cfv cq cply cdgr cdgraa wceq cc0 ccoe w3a mpaalem simpr2
      c1 wa syl ) ABCADEZFGECZSHEAIEZJZASEKJZUASLEEPJZMQUCANTUBUCUDOR $.

    $( Minimal polynomial is monic.  (Contributed by Stefan O'Rear,
       25-Nov-2014.) $)
    mpaamn $p |- ( A e. AA -> ( ( coeff ` ( minPolyAA ` A ) ) `
          ( degAA ` A ) ) = 1 ) $=
      ( caa wcel cmpaa cfv cq cply cdgr cdgraa wceq cc0 ccoe w3a mpaalem simpr3
      c1 wa syl ) ABCADEZFGECZSHEAIEZJZASEKJZUASLEEPJZMQUDANTUBUCUDOR $.

    $(
    @( The minimal polynomial of a rational number. @)
    mpaaq @p |- ( A e. QQ -> ( minPolyAA ` A ) = ( x e. CC |-> ( x - A ) ) ) @=
      ? @.
    $)
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Algebraic integers I
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c _ZZ IntgOver $.

  $( Extend class notation with the integral-over predicate. $)
  citgo $a class IntgOver $.

  $( Extend class notation with the class of algebraic integers. $)
  cza $a class _ZZ $.

  ${
    $d x p s $.

    $( A complex number is said to be integral over a subset if it is the root
       of a monic polynomial with coefficients from the subset.  This
       definition is typically not used for fields but it works there, see
       ~ aaitgo .  This definition could work for subsets of an arbitrary ring
       with a more general definition of polynomials.  TODO: use ` Monic ` .
       (Contributed by Stefan O'Rear, 27-Nov-2014.) $)
    df-itgo $a |- IntgOver = ( s e. ~P CC |-> { x e. CC | E. p e. ( Poly ` s )
        ( ( p ` x ) = 0 /\ ( ( coeff ` p ) ` ( deg ` p ) ) = 1 ) } ) $.

    $( Define an algebraic integer as a complex number which is the root of a
       monic integer polynomial.  (Contributed by Stefan O'Rear,
       30-Nov-2014.) $)
    df-za $a |- _ZZ = ( IntgOver ` ZZ ) $.
  $}

  ${
    $d S x p s a b c $.  $d T x p s a b c $.
    $( Value of the integral-over function.  (Contributed by Stefan O'Rear,
       27-Nov-2014.) $)
    itgoval $p |- ( S C_ CC -> ( IntgOver ` S ) = { x e. CC |
        E. p e. ( Poly ` S ) ( ( p ` x ) = 0 /\
          ( ( coeff ` p ) ` ( deg ` p ) ) = 1 ) } ) $=
      ( vs cc wss cpw wcel citgo cfv cv cc0 wceq cdgr ccoe cply wrex crab cnex
      c1 wa elpw2 fveq2 rexeqdv rabbidv df-itgo rabex fvmpt sylbir ) BEFBEGZHBI
      JAKCKZJLMUKNJUKOJJTMUAZCBPJZQZAERZMBESUBDBULCDKZPJZQZAERUOUJIUPBMZURUNAEU
      SULCUQUMUPBPUCUDUEADCUFUNAESUGUHUI $.

    $( The standard algebraic numbers ` AA ` are generated by ` IntgOver ` .
       (Contributed by Stefan O'Rear, 27-Nov-2014.) $)
    aaitgo $p |- AA = ( IntgOver ` QQ ) $=
      ( va vb caa cq cfv cv cc0 wceq cdgr ccoe c1 wa wrex cc wcel ax-mp c0p wne
      fveq2 cn0 citgo cply crab rabid qsscn itgoval eleq2i aacn mpaacl mpaaroot
      wss cmpaa cdgraa mpaadgr fveq2d mpaamn eqtrd fveq1 eqeq1d fveq12d anbi12d
      rspcev syl12anc jca csn cdif simpl cxp coe0 fveq1i dgr0 0nn0 eqeltri c0ex
      fvconst2 eqtri 0ne1 eqnetri neeq1d mpbiri necon2i ad2antll eldifsn simprl
      sylanbrc reximi2 anim2i elqaa sylibr impbii 3bitr4ri eqriv ) ACDUAEZAFZWN
      BFZEZGHZWOIEZWOJEZEZKHZLZBDUBEZMZANUCZOWNNOZXDLZWNWMOWNCOZXDANUDWMXEWNDNU
      KWMXEHUEADBUFPUGXHXGXHXFXDWNUHXHWNULEZXCOWNXIEZGHZXIIEZXIJEZEZKHZXDWNUIWN
      UJXHXNWNUMEZXMEKXHXLXPXMWNUNUOWNUPUQXBXKXOLBXIXCWOXIHZWQXKXAXOXQWPXJGWNWO
      XIURUSXQWTXNKXQWRXLWSXMWOXIJSWOXIISUTUSVAVBVCVDXGXFWQBXCQVEVFZMZLXHXDXSXF
      XBWQBXCXRWOXCOZXBLZWOXROZWQYAXTWOQRZYBXTXBVGXAYCXTWQWOQWTKWOQHZWTKRQIEZQJ
      EZEZKRYGGKYGYETGVEVHZEZGYEYFYHVIVJYETOYIGHYEGTVKVLVMTGYEVNVOPVPVQVRYDWTYG
      KYDWRYEWSYFWOQJSWOQISUTVSVTWAWBWOXCQWCWEXTWQXAWDVDWFWGWNBWHWIWJWKWL $.

    $( An integral element is integral over a subset.  (Contributed by Stefan
       O'Rear, 27-Nov-2014.) $)
    itgoss $p |- ( ( S C_ T /\ T C_ CC ) ->
          ( IntgOver ` S ) C_ ( IntgOver ` T ) ) $=
      ( va vb wss cc wa cv cfv cc0 wceq cdgr ccoe c1 cply wrex crab syl itgoval
      citgo wi wcel plyss ssrexv adantr ss2rabdv sstr adantl 3sstr4d ) ABEZBFEZ
      GZCHZDHZIJKUNLIUNMIINKGZDAOIZPZCFQZUODBOIZPZCFQZATIZBTIZULUQUTCFULUQUTUAZ
      UMFUBULUPUSEVDABUCUODUPUSUDRUEUFULAFEVBURKABFUGCADSRUKVCVAKUJCBDSUHUI $.

    $( All integral elements are complex numbers.  (Contributed by Stefan
       O'Rear, 27-Nov-2014.) $)
    itgocn $p |- ( IntgOver ` S ) C_ CC $=
      ( va vb vc citgo wcel cfv cc wss cv cc0 wceq cdgr ccoe cply wrex eqsstrdi
      c1 wa crab cdm cpw df-itgo dmmptss sseli cnex elpw2 itgoval ssrab2 syl wn
      sylbi c0 ndmfv 0ss pm2.61i ) AEUAZFZAEGZHIZURAHUBZFZUTUQVAABVACJZDJZGKLVD
      MGVDNGGRLSDBJZOGPCHTECBDUCUDUEVBAHIZUTAHUFUGVFUSVEVCGKLVCMGVCNGGRLSCAOGPZ
      BHTHBACUHVGBHUIQULUJURUKUSUMHAEUNHUOQUP $.
  $}

  ${
    $d ph a b $.  $d X a b $.  $d Y a b $.  $d S a b $.
    cnsrexpcl.s $e |- ( ph -> S e. ( SubRing ` CCfld ) ) $.
    cnsrexpcl.x $e |- ( ph -> X e. S ) $.
    cnsrexpcl.y $e |- ( ph -> Y e. NN0 ) $.
    $( Exponentiation is closed in number rings.  (Contributed by Stefan
       O'Rear, 30-Nov-2014.) $)
    cnsrexpcl $p |- ( ph -> ( X ^ Y ) e. S ) $=
      ( wcel cexp co wi cc0 c1 wceq oveq2 eleq1d imbi2d cc ccnfld 3ad2ant2 cmul
      va vb cn0 caddc csubrg cfv wss cnfldbas subrgss syl sseldd exp0d subrg1cl
      cv cnfld1 eqeltrd w3a simp1 expp1d simp3 cnfldmul subrgmcl syl3anc nn0ind
      3exp a2d mpcom ) DUDHACDIJZBHZGACUBUOZIJZBHZKACLIJZBHZKACUCUOZIJZBHZKACVP
      MUEJZIJZBHZKAVJKUBUCDVKLNZVMVOAWBVLVNBVKLCIOPQVKVPNZVMVRAWCVLVQBVKVPCIOPQ
      VKVSNZVMWAAWDVLVTBVKVSCIOPQVKDNZVMVJAWEVLVIBVKDCIOPQAVNMBACABRCABSUFUGHZB
      RUHEBRSUIUJUKFULZUMAWFMBHEBSMUPUNUKUQVPUDHZAVRWAWHAVRWAWHAVRURZVTVQCUAJZB
      WICVPAWHCRHVRWGTWHAVRUSUTWIWFVRCBHZWJBHAWHWFVRETWHAVRVAAWHWKVRFTBSUAVQCVB
      VCVDUQVFVGVEVH $.
  $}

  ${
    $d ph k a b $.  $d A k a b $.  $d B a b $.  $d S k a b $.
    fsumcnsrcl.s $e |- ( ph -> S e. ( SubRing ` CCfld ) ) $.
    fsumcnsrcl.a $e |- ( ph -> A e. Fin ) $.
    fsumcnsrcl.b $e |- ( ( ph /\ k e. A ) -> B e. S ) $.
    $( Finite sums are closed in number rings.  (Contributed by Stefan O'Rear,
       30-Nov-2014.) $)
    fsumcnsrcl $p |- ( ph -> sum_ k e. A B e. S ) $=
      ( va vb ccnfld csubrg cfv wcel cc wss cnfldbas cv caddc cc0 subrgss wa co
      syl cnfldadd subrgacl 3expb sylan subrgsubg cnfld0 subg0cl 3syl fsumcllem
      csubg ) AIJBCDEADKLMNZDOPFDOKQUAUDAUOIRZDNZJRZDNZUBUPURSUCDNZFUOUQUSUTDSK
      UPURUEUFUGUHGHAUODKUNMNTDNFDKUIDKTUJUKULUM $.
  $}

  ${
    $d P k $.  $d ph k $.  $d X k $.  $d S k $.  $d C k $.
    cnsrplycl.s $e |- ( ph -> S e. ( SubRing ` CCfld ) ) $.
    cnsrplycl.p $e |- ( ph -> P e. ( Poly ` C ) ) $.
    cnsrplycl.x $e |- ( ph -> X e. S ) $.
    cnsrplycl.c $e |- ( ph -> C C_ S ) $.
    $( Polynomials are closed in number rings.  (Contributed by Stefan O'Rear,
       30-Nov-2014.) $)
    cnsrplycl $p |- ( ph -> ( P ` X ) e. S ) $=
      ( vk cfv cc0 co wcel cc wss ccnfld syl2anc adantr cn0 cdgr ccoe cexp cmul
      cfz cv csu cply wceq csubrg cnfldbas subrgss syl plyss sseldd eqid coeid2
      fzfid wa wf csubg subrgsubg cnfld0 subg0cl coef2 elfznn0 adantl ffvelcdmd
      3syl cnsrexpcl cnfldmul subrgmcl syl3anc fsumcnsrcl eqeltrd ) AECKZLCUAKZ
      UEMZJUFZCUBKZKZEVSUCMZUDMZJUGZDACDUHKZNZEONVPWDUIABUHKZWECABDPDOPZWGWEPIA
      DQUJKNZWHFDOQUKULUMZBDUNRGUOZADOEWJHUOVTDJCVQEVTUPZVQUPUQRAVRWCDJFALVQURA
      VSVRNZUSZWIWADNWBDNWCDNAWIWMFSZWNTDVSVTATDVTUTZWMAWFLDNZWPWKAWIDQVAKNWQFD
      QVBDQLVCVDVIVTDCWLVERSWMVSTNAVSVQVFVGZVHWNDEVSWOAEDNWMHSWRVJDQUDWAWBVKVLV
      MVNVO $.
  $}

  ${
    rgspnid.r $e |- ( ph -> R e. Ring ) $.
    rgspnid.sr $e |- ( ph -> A e. ( SubRing ` R ) ) $.
    rgspnid.sp $e |- ( ph -> S = ( ( RingSpan ` R ) ` A ) ) $.
    $( The span of a subring is itself.  (Contributed by Stefan O'Rear,
       30-Nov-2014.) $)
    rgspnid $p |- ( ph -> S = A ) $=
      ( cbs cfv crgspn eqidd wcel wss eqid subrgss syl ssidd rgspnmin rgspnssid
      csubrg eqssd ) ADBABCHIZCBDCJIZEAUBKZABCTILBUBMFBUBCUBNOPZAUCKZGFABQRABUB
      CDUCEUDUEUFGSUA $.
  $}

  ${
    $d ph a b c d e p $.  $d B a b c d e p $.  $d X a b c d e p $.
    $d V a b c d e p $.
    rngunsnply.b $e |- ( ph -> B e. ( SubRing ` CCfld ) ) $.
    rngunsnply.x $e |- ( ph -> X e. CC ) $.
    rngunsnply.s $e |- ( ph -> S = ( ( RingSpan ` CCfld ) `
        ( B u. { X } ) ) ) $.
    $( Adjoining one element to a ring results in a set of polynomial
       evaluations.  (Contributed by Stefan O'Rear, 30-Nov-2014.) $)
    rngunsnply $p |- ( ph -> ( V e. S <->
        E. p e. ( Poly ` B ) V = ( p ` X ) ) ) $=
      ( va wcel ccnfld cfv wceq wrex cc caddc co cmul rexbidv vb csn cun crgspn
      vc ve vd cv eleq2d cab crg cnring a1i cbs cnfldbas csubrg wss subrgss syl
      cply snssd unssd eqidd cress c1 cc0 c0g cnfld0 cplusg cnfldadd wa wf plyf
      ffvelcdm syl2anr eleq1 syl5ibrcom rexlimdva abid2 eqtri sseqtrdi plyconst
      ss2abdv cxp sylan adantr fvconst2 eqcomd fveq1 rspceeqv syl2anc eqsstrrid
      vex ex csubg subrgsubg subg0cl sseldd w3a biid weq eqeq2d cbvrexvw bitrdi
      eqeq1 elab wi cof simplr simpr subrgacl 3expb adantlr plyadd wfn cvv ffnd
      ad2antlr adantl cnex ad2antrr fnfvof syl22anc oveq2 eqeq1d imbi2d syl3anb
      oveq1 3imp ovex sylibr cminusg cneg cnfldneg mp1i cnfld1 plymul fvex cidp
      cnfldmul ax-1cn subrg1cl eqid subginvcl eqeltrrd subrgmcl fnconstg oveq1d
      negex mulm1d 3eqtrd fveqeq2 imp sylan2b cur cmulr issubrgd plyid cid cres
      eqtr4d df-idp fveq1i fvresi eqtr2id elabd rgspnmin sseld mpbiri rexlimivw
      elab3 imbitrdi rgspncl rgspnssid unssbd snidg unssad cnsrplycl impbid
      bitrd ) ADCKDBEUBZUCZLUDMZMZKZDEFUHZMZNZFBUTMZOZACUWDDIUIAUWEUWJAUWEDJUHZ
      UWGNZFUWIOZJUJZKUWJAUWDUWNDAUWBPLUWNUWDUWCLUKKAULUMZPLUNMZNAUOUMZABUWAPAB
      LUPMZKZBPUQZGBPLUOURUSZAEPHVAVBZAUWCVCZAUWDVCZAUAUEUWNQLUWNVDRZSVELVFAUXE
      VCVFLVGMNAVHUMQLVIMNAVJUMAUWNUWKPKZJUJZUWPAUWMUXFJAUWLUXFFUWIAUWFUWIKZVKZ
      UXFUWLUWGPKZUXHPPUWFVLEPKZUXJABUWFVMHPPEUWFVNVOUWKUWGPVPVQVRWCUXGPUWPJPVS
      UOVTWAABUWNVFABUWKBKZJUJUWNJBVSAUXLUWMJAUXLUWMAUXLVKZPUWKUBWDZUWIKZUWKEUX
      NMZNUWMAUWTUXLUXOUXAUWKBWBWEUXMUXPUWKUXMUXKUXPUWKNAUXKUXLHWFPUWKEJWMWGUSW
      HFUXNUWIUWGUXPUWKEUWFUXNWIWJWKWNWCWLZABLWOMKZVFBKAUWSUXRGBLWPUSZBLVFVHWQU
      SWRAUAUHZUWNKZUEUHZUWNKZWSZUXTUYBQRZUWGNZFUWIOZUYEUWNKAAUYAUXTEUFUHZMZNZU
      FUWIOZUYCUYBEUGUHZMZNZUGUWIOZUYGAWTZUWMUYKJUXTUAWMJUAXAZUWMUXTUWGNZFUWIOU
      YKUYQUWLUYRFUWIUWKUXTUWGXETUYRUYJFUFUWIFUFXAUWGUYIUXTEUWFUYHWIXBXCXDXFZUW
      MUYOJUYBUEWMJUEXAZUWMUYBUWGNZFUWIOUYOUYTUWLVUAFUWIUWKUYBUWGXETVUAUYNFUGUW
      IFUGXAUWGUYMUYBEUWFUYLWIXBXCXDXFZAUYKUYOUYGAUYJUYOUYGXGZUFUWIAUYHUWIKZVKZ
      VUCUYJUYOUYIUYBQRZUWGNZFUWIOZXGVUEUYNVUHUGUWIVUEUYLUWIKZVKZVUHUYNUYIUYMQR
      ZUWGNZFUWIOZVUJUYHUYLQXHRZUWIKVUKEVUNMZNVUMVUJJUABUYHUYLAVUDVUIXIZVUEVUIX
      JZVUEUXLUXTBKZVKZUWKUXTQRBKZVUIAVUSVUTVUDAUWSVUSVUTGUWSUXLVURVUTBQLUWKUXT
      VJXKXLWEXMZXMZXNVUJVUOVUKVUJUYHPXOZUYLPXOZPXPKZUXKVUOVUKNVUDVVCAVUIVUDPPU
      YHBUYHVMZXQZXRZVUIVVDVUEVUIPPUYLBUYLVMXQXSZVVEVUJXTUMZAUXKVUDVUIHYAZPQUYH
      UYLXPEYBYCWHFVUNUWIUWGVUOVUKEUWFVUNWIWJWKUYNVUGVULFUWIUYNVUFVUKUWGUYBUYMU
      YIQYDYETVQVRUYJUYGVUHUYOUYJUYFVUGFUWIUYJUYEVUFUWGUXTUYIUYBQYHYETYFVQVRYIY
      GUWMUYGJUYEUXTUYBQYJUWKUYENUWLUYFFUWIUWKUYEUWGXETXFYKAUYAVKUXTLYLMZMZUWGN
      ZFUWIOZVVMUWNKUYAAUYKVVOUYSAUYKVVOAUYJVVOUFUWIVUEVVOUYJUYIVVLMZUWGNZFUWIO
      ZVUEPVEYMZUBWDZUYHSXHZRZUWIKVVPEVWBMZNVVRVUEJUABVVTUYHAVVTUWIKZVUDAUWTVVS
      BKVWDUXAAVEVVLMZVVSBVEPKVWEVVSNAUUAVEYNYOAUXRVEBKZVWEBKUXSAUWSVWFGBLVEYPU
      UBUSZBLVVLVEVVLUUCUUDWKUUEVVSBWBWKWFAVUDXJVVAAVUSUWKUXTSRBKZVUDAUWSVUSVWH
      GUWSUXLVURVWHBLSUWKUXTYTUUFXLWEXMZYQVUEVVPUYIYMZVWCVUEUYIPKZVVPVWJNVUDPPU
      YHVLUXKVWKAVVFHPPEUYHVNVOZUYIYNUSVUEVWCEVVTMZUYISRZVVSUYISRVWJVUEVVTPXOZV
      VCVVEUXKVWCVWNNVVSXPKVWOVUEVEUUIZPVVSXPUUGYOVUDVVCAVVGXSVVEVUEXTUMAUXKVUD
      HWFZPSVVTUYHXPEYBYCVUEVWMVVSUYISVUEUXKVWMVVSNVWQPVVSEVWPWGUSUUHVUEUYIVWLU
      UJUUKUVAFVWBUWIUWGVWCVVPEUWFVWBWIWJWKUYJVVNVVQFUWIUXTUYIUWGVVLUULTVQVRUUM
      UUNUWMVVOJVVMUXTVVLYRUWKVVMNUWLVVNFUWIUWKVVMUWGXETXFYKVELUUOMNAYPUMSLUUPM
      NAYTUMABUWNVEUXQVWGWRUYDUXTUYBSRZUWGNZFUWIOZVWRUWNKAAUYAUYKUYCUYOVWTUYPUY
      SVUBAUYKUYOVWTAUYJUYOVWTXGZUFUWIVUEVXAUYJUYOUYIUYBSRZUWGNZFUWIOZXGVUEUYNV
      XDUGUWIVUJVXDUYNUYIUYMSRZUWGNZFUWIOZVUJUYHUYLVWARZUWIKVXEEVXHMZNVXGVUJJUA
      BUYHUYLVUPVUQVVBVUEVUSVWHVUIVWIXMYQVUJVXIVXEVUJVVCVVDVVEUXKVXIVXENVVHVVIV
      VJVVKPSUYHUYLXPEYBYCWHFVXHUWIUWGVXIVXEEUWFVXHWIWJWKUYNVXCVXFFUWIUYNVXBVXE
      UWGUYBUYMUYISYDYETVQVRUYJVWTVXDUYOUYJVWSVXCFUWIUYJVWRVXBUWGUXTUYIUYBSYHYE
      TYFVQVRYIYGUWMVWTJVWRUXTUYBSYJUWKVWRNUWLVWSFUWIUWKVWRUWGXETXFYKUWOUUQABUW
      AUWNUXQAEUWNAUWMEUWGNZFUWIOZJEPHAYSUWIKZEEYSMZNVXKAUWTVWFVXLUXAVWGBUURWKA
      VXMEUUSPUUTZMZEEYSVXNUVBUVCAUXKVXOENHPEUVDUSUVEFYSUWIUWGVXMEEUWFYSWIWJWKU
      WKENUWLVXJFUWIUWKEUWGXETUVFVAVBUVGUVHUWMUWJJDXPUWHDXPKZFUWIUWHVXPUWGXPKEU
      WFYRDUWGXPVPUVIUVJUWKDNUWLUWHFUWIUWKDUWGXETUVKUVLAUWHUWEFUWIUXIUWEUWHUWGU
      WDKUXIBUWFUWDEAUWDUWRKUXHAUWBPLUWDUWCUWOUWQUXBUXCUXDUVMWFAUXHXJAEUWDKUXHA
      UWAUWDEABUWAUWDAUWBPLUWDUWCUWOUWQUXBUXCUXDUVNZUVOAUXKEUWAKHEPUVPUSWRWFABU
      WDUQUXHABUWAUWDVXQUVQWFUVRDUWGUWDVPVQVRUVSUVT $.
  $}

  ${
    $d ph i j $.  $d F i $.  $d S i j $.  $d K i j $.  $d B j $.
    flcidc.f $e |- ( ph -> F = ( j e. S |-> if ( j = K , 1 , 0 ) ) ) $.
    flcidc.s $e |- ( ph -> S e. Fin ) $.
    flcidc.k $e |- ( ph -> K e. S ) $.
    flcidc.b $e |- ( ( ph /\ i e. S ) -> B e. CC ) $.
    $( Finite linear combinations with an indicator function.  (Contributed by
       Stefan O'Rear, 5-Dec-2014.) $)
    flcidc $p |- ( ph -> sum_ i e. S ( ( F ` i ) x. B ) = [_ K / i ]_ B ) $=
      ( cmul co wcel wa c1 wceq cc0 eqtrd cc csn cv cfv csu csb cif cmpt fveq1d
      adantr snssd sselda eqeq1 ifbid eqid 1ex c0ex ifex fvmpt syl elsni adantl
      iftrued oveq1d syldan mullidd sumeq2dv ax-1cn eqeltrdi mulcld cdif eldifi
      0cn ifcli eldifn velsn sylnib iffalsed mul02d fsumss anbi2d csbeq1 eleq1d
      eleq1 imbi12d nfv nfcsb1v nfel1 nfim csbeq1a chvarfv vtoclg anabsi7 mpdan
      wi sumsns syl2anc 3eqtr3d ) AGUAZDUBZFUCZBLMZDUDWRBDUDZCXADUDDGBUEZAWRXAB
      DAWSWRNZOZXAPBLMBXEWTPBLXEWTWSGQZPRUFZPXEWTWSECEUBZGQZPRUFZUGZUCZXGAWTXLQ
      ZXDAWSFXKHUHZUIXEWSCNZXLXGQZAWRCWSAGCJUJZUKZEWSXJXGCXKXHWSQXIXFPRXHWSGULU
      MXKUNXFPRUOUPUQURZUSSZXDXGPQAXDXFPRWSGUTVBVASVCXEBAXDXOBTNZXRKVDZVESVFAWR
      CXADXQXEWTBXEWTXGTXTXFPRTVGVLVMVHYBVIAWSCWRVJNZOZXARBLMRYDWTRBLYDWTXGRYDW
      TXLXGAXMYCXNUIYDXOXPYCXOAWSCWRVKVAZXSUSSYCXGRQAYCXFPRYCXDXFWSCWRVNDGVOVPV
      QVASVCYDBAYCXOYAYEKVDVRSIVSAGCNZXCTNZXBXCQJAYFYGJAYFYGAXHCNZOZDXHBUEZTNZW
      NZAYFOZYGWNEGCXIYIYMYKYGXIYHYFAXHGCWCVTXIYJXCTDXHGBWAWBWDAXOOZYAWNYLDEYIY
      KDYIDWEDYJTDXHBWFWGWHWSXHQZYNYIYAYKYOXOYHAWSXHCWCVTYOBYJTDXHBWIWBWDKWJWKW
      LWMBDGCWOWPWQ $.
  $}

  $(
  @{
    @d ph i a b c @.  @d B i a b c @.  @d G i a b c @.  @d F i a b c @.
    cnplyspn.b @e |- ( ph -> B e. ( SubRing ` CCfld ) ) @.
    cnplyspn.a @e |- ( ph -> A = ( ( subringAlg ` CCfld ) ` B ) ) @.
    cnplyspn.s @e |- ( ph -> S = ( ( LSpan ` A ) ` ran F ) ) @.
    cnplyspn.f @e |- ( ph -> F = ( j e. ( 0 ... ( K - 1 ) ) |-> ( R ^ j ) ) )
        @.
    @( Finite spans of powers are the values of limited-degree polynomials. @)
    cnplyspn @p |- ( ph -> ( X e. S <->
        E. f e. ( B Poly< K ) X = ( f ` R ) ) ) @=
      ? @.
  @}

    @( TODO @)
    @( Finite spans in terms of limited degree polynomials. @)
    @( Patch monic definition into itgo. @)
    @( Transitivity of finite spans. @)
    @( Forward itgofg. @)
    @( Reverse using ac6sfi. @)
    @( itgofg2 and lemmas @)
    @( start on Noetherian @)

  @{
    Xitgofglem5.b @e |- ( ph -> B e. ( SubRing ` CCfld ) ) @.
    Xitgofglem5.x @e |- ( ph -> X e. CC ) @.
    Xitgofglem5.u @e |- ( ph -> U e. ( Poly ` B ) ) @.
    Xitgofglem5.d @e |- ( ph -> D e. NN0 ) @.
    Xitgofglem5.d2 @e |- ( ph -> ( deg ` U ) < D ) @.
    Xitgofglem5.a @e |- A = ( ( subringAlg ` CCfld ) ` B ) @.
    Xitgofglem5.q @e |- Q = { x | E. i e. ( 0 ... ( D - 1 ) ) x = ( X ^ i ) }
        @.
    @( Lemma for ~ itgofg .  The span of the first ` D ` powers of ` X `
       contains all evaluations of polynomials with degree at most ` D ` . @)
    Xitgofglem5 @p |- ( ph -> ( U ` X ) e. ( ( LSpan ` A ) ` Q ) ) @=
      ? @.
  @}

  @{
    Xitgofglem4.b @e |- ( ph -> B e. ( SubRing ` CCfld ) ) @.
    Xitgofglem4.p @e |- ( ph -> P e. ( Monic ` B ) ) @.
    Xitgofglem4.x @e |- ( ph -> X e. CC ) @.
    Xitgofglem4.x0 @e |- ( ph -> ( P ` X ) = 0 ) @.
    Xitgofglem4.u @e |- ( ph -> U e. ( Poly ` B ) ) @.
    Xitgofglem4.f @e |- A = ( ( subringAlg ` CCfld ) ` B ) @.
    Xitgofglem4.g @e |- Q = { x | E. i e. ( 0 ... ( ( deg ` P ) - 1 ) )
        x = ( X ^ i ) } @.
    @( Lemma for ~ itgofg .  Use the polynomial identity to inductively prove
       that the span of Q contains all polynomial evaluations. @)
    Xitgofglem4 @p |- ( ph -> ( U ` X ) e. ( ( LSpan ` A ) ` Q ) ) @=
      ? @.
  @}

  @{
    Xitgofglem3.a @e |- ( ph -> B e. ( SubRing ` CCfld ) ) @.
    Xitgofglem3.b @e |- ( ph -> P e. ( Monic ` B ) ) @.
    Xitgofglem3.c @e |- ( ph -> X e. CC ) @.
    Xitgofglem3.d @e |- ( ph -> ( P ` X ) = 0 ) @.
    Xitgofglem3.e @e |- S = ( ( RingSpan ` CCfld ) ` ( B u. { X } ) ) @.
    Xitgofglem3.f @e |- A = ( ( subringAlg ` ( CCfld |` S ) ) ` B ) @.
    Xitgofglem3.g @e |- Q = { x | E. i e. ( 0 ... ( deg ` P ) )
        x = ( X ^ i ) } @.
    @( Lemma for ~ itgofg .  Given a polynomial witnessing the integrality of
       ` X ` , demonstrate the finite generation of ` A ` . @)
    Xitgofglem3 @p |- ( ph -> ( ( LSpan ` A ) ` Q ) = S ) @=
      ? @.
  @}

  @{
    Xitgofg.s @e |- S = ( ( RingSpan ` CCfld ) ` ( B u. { X } ) ) @.
    Xitgofg.a @e |- A = ( ( subringAlg ` ( CCfld |` S ) ) ` B ) @.
    @( Lemma for ~ itgofg . @)
    Xitgofglem2 @p |- ( ( B e. ( SubRing ` CCfld ) /\ A e. LFinGen ) ->
          X e. ( IntgOver ` B ) ) @=
      ? @.

    @( Lemma for ~ itgofg . @)
    Xitgofglem1 @p |- ( ( B e. ( SubRing ` CCfld ) /\ X e. ( IntgOver ` B ) )
        ->
          A e. LFinGen ) @=
      ? @.

    @( An element is finitely generated over a ring if and only adjoining it to
       the base ring results in a finitely spanned algebra.

       Both directions:  The ring span of a ring R and a singleton is the
       R-linear span of the powers of the singleton.  It is also the set of
       values of R-polynomials evaluated at the singleton.

       Forward:  If X is algebraic, it is the root of a monic polynomial P with
       degree D. The span of the finite set of powers (X^0 ...  X^D) is
       finitely spanned, and it is equal to the span of all the powers: it is a
       subset because the ring span is a ring which contains all the powers,
       and it also a superset, because it is a linear subspace that contains
       all of the powers (by induction).

       Reverse:  Suppose the ring of polynomial values is finitely spanned,
       that is, there is a finite set of polynomials P(i) such that any linear
       subspace that contains P(i)(X) contains all polynomials of X. Let N be
       one more than the supremum of the degrees of P(i).  By assumption (X^N)
       is in the span of P(i)(X), so there is an R-linear combination of
       P(i)(X) equal to (X^N); but an R-linear combination of R-polynomials
       with degree less than N is an R-polynomial with degree less than N, so
       let Q be an R-polynomial such that Q(X) = (X^N) and deg(Q) < N. Then
       (X^N) - Q(X) is a monic R-polynomial with X as a root, i.e., X is
       algebraic. @)
    itgofg @p |- ( B e. ( SubRing ` CCfld ) -> ( X e. ( IntgOver ` B ) <->
          A e. LFinGen ) ) @=
      ? @.
  @}

  @{
    rgspnchn.r @e |- ( ph -> R e. Ring ) @.
    rgspnchn.s @e |- ( ph -> S = ( RingSpan ` R ) ) @.
    rgspnchn.b @e |- ( ph -> B = ( Base ` R ) ) @.
    rgspnchn.x @e |- ( ph -> X C_ B ) @.
    rgspnchn.a @e |- ( ph -> A C_ B ) @.
    @( Chaining lemma for ring spans. @)
    rgspnchn @p |- ( ph -> ( R ` ( ( R ` X ) u. A ) ) = ( R ` ( X u. A ) ) ) @=
      ? @.
  @}

  @{
    itgofg2.ba @e |- ( ph -> B e. ( SubRing ` CCfld ) ) @.
    itgofg2.fi @e |- ( ph -> F e. Fin ) @.
    itgofg2.ss @e |- ( ph -> F C_ ( IntgOver ` B ) ) @.
    itgofg2.sp @e |- ( ph -> S = ( ( RingSpan ` CCfld ) ` ( B u. F ) ) ) @.
    itgofg2.al @e |- ( ph -> A = ( ( subringAlg ` ( CCfld |` S ) ) ` B ) ) @.
    @( Adjoining finitely many integral elements to a ring still gives a finite
       extension. @)
    itgofg2 @p |- ( ph -> A e. LFinGen ) @=
      ? @.
  @}

  @{
    itgocllem.a @e |- S = ( ( RingSpan ` CCfld ) ` ( R u. { X } ) ) @.
    itgocllem.b @e |- T = ( ( RingSpan ` CCfld ) ` ( S u. { Y } ) ) @.
    itgocllem.c @e |- A = ( ( subringAlg ` ( CCfld |` S ) ) ` R ) @.
    itgocllem.d @e |- B = ( ( subringAlg ` ( CCfld |` T ) ) ` S ) @.
    itgocllem.e @e |- C = ( ( subringAlg ` ( CCfld |` T ) ) ` R ) @.
    itgocllem.f @e |- Z e. { ( X + Y ) , ( X x. Y ) } @.
    @( Integrality is transitive(?). @)
    itgocllem @p |- ( ( R e. ( SubRing ` CCfld ) /\ X e. ( IntgOver ` R ) /\
          Y e. ( IntgOver ` R ) ) -> Z e. ( IntgOver ` R ) ) @=
      ? @.
  @}
  $)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  The determinant / matrix adjugate/adjunct
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(
  @{
    gsumiunfi.b @e |- B = ( Base ` G ) @.
    gsumiunfi.g @e |- ( ph -> G e. CMnd ) @.
    gsumiunfi.c @e |- ( ph -> C e. Fin ) @.
    gsumiunfi.d @e |- ( ( ph /\ i e. C ) -> D e. Fin ) @.
    gsumiunfi.a @e |- ( ( ph /\ j e. A ) -> E! i e. C j e. D ) @.
    gsumiunfi.x @e |- ( ( ph /\ j e. A ) -> X e. B ) @.
    @( An iterated splitting rule for finite sums.  (Contributed by Stefan
       O'Rear, 10-Sep-2015.) @)
    gsumiunfi @p |- ( ph -> ( G gsum ( j e. A |-> X ) ) =
        ( G gsum ( i e. C |-> ( G gsum ( j e. D |-> X ) ) ) ) ) @= ? @.
  @}
$)

$(
  @{
    mdetlap.d @e |- D = ( N maDet R ) @.
    mdetlap.a @e |- A = ( N Mat R ) @.
    mdetlap.b @e |- B = ( Base ` A ) @.
    mdetlap.t @e |- .x. = ( .r ` R ) @.
    mdetlap.j @e |- J = ( N maAdju R ) @.

 @(
   @{
      @( Express the cofactor as a portion of the determinant sum.
         (Contributed by Stefan O'Rear, 10-Sep-2015.) @)
      mdetlaplem @p |- ( ( R e. CRing /\ M e. B )
        -> ( J ` M ) = ( i e. N , j e. N |->  ( R gsum ( p e. { q e. P | ...
    @}
@)

    @( The Laplace formula for the determinant.  (Contributed by Stefan
       O'Rear, 9-Sep-2015.) @)
    mdetlap @p |- ( ( R e. CRing /\ M e. B /\ X e. N ) -> ( D ` M ) =
        ( R gsum ( y e. N |-> ( ( X M y ) .x. ( y ( J ` M ) X ) ) ) ) ) @= ? @.
  @}
$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Endomorphism algebra
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c MEndo $.
  $( Syntax for module endomorphism algebra. $)
  cmend $a class MEndo $.

  ${
    $d m b x y $.
    $( Define the endomorphism algebra of a module.  (Contributed by Stefan
       O'Rear, 2-Sep-2015.) $)
    df-mend $a |- MEndo = ( m e. _V |-> [_ ( m LMHom m ) / b ]_
      ( { <. ( Base ` ndx ) , b >. ,
          <. ( +g ` ndx ) , ( x e. b , y e. b |-> ( x oF ( +g ` m ) y ) ) >. ,
          <. ( .r ` ndx ) , ( x e. b , y e. b |-> ( x o. y ) ) >. } u.
        { <. ( Scalar ` ndx ) , ( Scalar ` m ) >. ,
          <. ( .s ` ndx ) , ( x e. ( Base ` ( Scalar ` m ) ) , y e. b |->
             ( ( ( Base ` m ) X. { x } ) oF ( .s ` m ) y ) ) >. } ) ) $.
  $}

  ${
    algpart.a $e |- A = ( { <. ( Base ` ndx ) , B >. ,
       <. ( +g ` ndx ) , .+ >. , <. ( .r ` ndx ) , .X. >. } u.
     { <. ( Scalar ` ndx ) , S >. , <. ( .s ` ndx ) , .x. >. } ) $.
    $( Lemma to shorten proofs of ~ algbase through ~ algvsca .  (Contributed
       by Stefan O'Rear, 27-Nov-2014.)  (Revised by Mario Carneiro,
       29-Aug-2015.) $)
    algstr $p |- A Struct <. 1 , 6 >. $=
      ( cnx cbs cfv cop cplusg cmulr ctp csca cvsca cpr c1 c6 c5 cstr c3 rngstr
      cun eqid 5nn scandx 5lt6 6nn vscandx strle2 3lt5 strleun eqbrtri ) AHIJBK
      HLJCKHMJFKNZHOJZDKHPJZEKQZUDRSKUAGRUBTSUOURBCUOFUOUEUCUPUQTSDEUFUGUHUIUJU
      KULUMUN $.

    $( The base set of a constructed algebra.  (Contributed by Stefan O'Rear,
       27-Nov-2014.)  (Revised by Mario Carneiro, 29-Aug-2015.) $)
    algbase $p |- ( B e. V -> B = ( Base ` A ) ) $=
      ( cbs c1 c6 cop algstr baseid cnx cfv csn cplusg cmulr ctp csca cvsca cpr
      snsstp1 cun ssun1 sseqtrri sstri strfv ) BAIGJKLABCDEFHMNOIPBLZQUJORPCLZO
      SPFLZTZAUJUKULUDUMUMOUAPDLOUBPELUCZUEAUMUNUFHUGUHUI $.

    $( The additive operation of a constructed algebra.  (Contributed by Stefan
       O'Rear, 27-Nov-2014.)  (Revised by Mario Carneiro, 29-Aug-2015.) $)
    algaddg $p |- ( .+ e. V -> .+ = ( +g ` A ) ) $=
      ( cplusg c1 c6 cop algstr plusgid cnx cfv csn cbs cmulr ctp snsstp2 cvsca
      csca cpr cun ssun1 sseqtrri sstri strfv ) CAIGJKLABCDEFHMNOIPCLZQORPBLZUJ
      OSPFLZTZAUKUJULUAUMUMOUCPDLOUBPELUDZUEAUMUNUFHUGUHUI $.

    $( The multiplicative operation of a constructed algebra.  (Contributed by
       Stefan O'Rear, 27-Nov-2014.)  (Revised by Mario Carneiro,
       29-Aug-2015.) $)
    algmulr $p |- ( .X. e. V -> .X. = ( .r ` A ) ) $=
      ( cmulr c1 c6 cop algstr mulridx cnx cfv csn cbs cplusg ctp snsstp3 cvsca
      csca cpr cun ssun1 sseqtrri sstri strfv ) FAIGJKLABCDEFHMNOIPFLZQORPBLZOS
      PCLZUJTZAUKULUJUAUMUMOUCPDLOUBPELUDZUEAUMUNUFHUGUHUI $.

    $( The set of scalars of a constructed algebra.  (Contributed by Stefan
       O'Rear, 27-Nov-2014.)  (Revised by Mario Carneiro, 29-Aug-2015.) $)
    algsca $p |- ( S e. V -> S = ( Scalar ` A ) ) $=
      ( csca c1 c6 cop algstr scaid cnx cfv csn cvsca cpr snsspr1 cbs cmulr ctp
      cplusg cun ssun2 sseqtrri sstri strfv ) DAIGJKLABCDEFHMNOIPDLZQUJORPELZSZ
      AUJUKTULOUAPBLOUDPCLOUBPFLUCZULUEAULUMUFHUGUHUI $.

    $( The scalar product operation of a constructed algebra.  (Contributed by
       Stefan O'Rear, 27-Nov-2014.)  (Revised by Mario Carneiro,
       29-Aug-2015.) $)
    algvsca $p |- ( .x. e. V -> .x. = ( .s ` A ) ) $=
      ( cvsca c1 c6 cop algstr vscaid cnx cfv csn csca cpr snsspr2 cplusg cmulr
      cbs ctp cun ssun2 sseqtrri sstri strfv ) EAIGJKLABCDEFHMNOIPELZQORPDLZUJS
      ZAUKUJTULOUCPBLOUAPCLOUBPFLUDZULUEAULUMUFHUGUHUI $.
  $}

  ${
    $d b m x y B $.  $d b m x y M $.  $d b m .+ $.  $d b m S $.  $d b m .X. $.
    $d b m .x. $.
    mendval.b $e |- B = ( M LMHom M ) $.
    mendval.p $e |- .+ = ( x e. B , y e. B |-> ( x oF ( +g ` M ) y ) ) $.
    mendval.t $e |- .X. = ( x e. B , y e. B |-> ( x o. y ) ) $.
    mendval.s $e |- S = ( Scalar ` M ) $.
    mendval.v $e |- .x. = ( x e. ( Base ` S ) , y e. B |->
        ( ( ( Base ` M ) X. { x } ) oF ( .s ` M ) y ) ) $.
    $( Value of the module endomorphism algebra.  (Contributed by Stefan
       O'Rear, 2-Sep-2015.) $)
    mendval $p |- ( M e. X -> ( MEndo ` M ) = ( { <. ( Base ` ndx ) , B >. ,
        <. ( +g ` ndx ) , .+ >. , <. ( .r ` ndx ) , .X. >. } u. { <. ( Scalar `
          ndx ) , S >. , <. ( .s ` ndx ) , .x. >. } ) ) $=
      ( vb cfv cbs cop wceq co vm wcel cvv cmend cnx cplusg cmulr ctp cvsca cpr
      csca cun elex cv clmhm cof cmpo csn cxp csb oveq12 anidms eqtr4di csbeq1d
      ccom ovex eqeltrrdi wa simpr opeq2d fveq2 ofeqd mpoeq123dv eqidd tpeq123d
      oveqdr adantr fveq2d xpeq1d oveq123d preq12d uneq12d csbied eqtrd df-mend
      tpex prex unex fvmpt syl ) HIUBHUCUBHUDPUEQPZCRZUEUFPZDRZUEUGPZGRZUHZUEUK
      PZERZUEUIPZFRZUJZULZSHIUMUAHOUAUNZXDUOTZWKOUNZRZWMABXFXFAUNZBUNZXDUFPZUPZ
      TZUQZRZWOABXFXFXHXIVEZUQZRZUHZWRXDUKPZRZWTABXSQPZXFXDQPZXHURZUSZXIXDUIPZU
      PZTZUQZRZUJZULZUTZXCUCUDXDHSZYLOCYKUTXCYMOXECYKYMXEHHUOTZCYMXEYNSXDHXDHUO
      VAVBJVCZVDYMOCYKXCUCYMCXEUCYOXDXDUOVFVGYMXFCSZVHZXRWQYJXBYQXGWLXNWNXQWPYQ
      XFCWKYMYPVIZVJYQXMDWMYQXMABCCXHXIHUFPZUPZTZUQDYQABXFXFXLCCUUAYRYRYMYPABXK
      YTYMXJYSXDHUFVKVLVPVMKVCVJYQXPGWOYQXPABCCXOUQGYQABXFXFXOCCXOYRYRYQXOVNVML
      VCVJVOYQXTWSYIXAYQXSEWRYQXSHUKPZEYMXSUUBSYPXDHUKVKVQMVCZVJYQYHFWTYQYHABEQ
      PZCHQPZYCUSZXIHUIPZUPZTZUQFYQABYAXFYGUUDCUUIYQXSEQUUCVRYRYQYDUUFXIXIYFUUH
      YQYEUUGYMYEUUGSYPXDHUIVKVQVLYQYBUUEYCYMYBUUESYPXDHQVKVQVSYQXIVNVTVMNVCVJW
      AWBWCWDABUAOWEWQXBWLWNWPWFWSXAWGWHWIWJ $.
  $}

  ${
    $d x y M $.
    mendbas.a $e |- A = ( MEndo ` M ) $.
    $( Base set of the module endomorphism algebra.  (Contributed by Stefan
       O'Rear, 2-Sep-2015.) $)
    mendbas $p |- ( M LMHom M ) = ( Base ` A ) $=
      ( vx vy cvv wcel clmhm co cbs cfv wceq cnx cop cplusg cv cof cmpo eqid c0
      cmulr ccom ctp csca cvsca csn cxp cpr cun ovex algbase mp1i cmend mendval
      eqtrid fveq2d eqtr4d wn base0 reldmlmhm ovprc1 fvprc 3eqtr4a pm2.61i ) BF
      GZBBHIZAJKZLVEVFMJKVFNMOKDEVFVFDPZEPZBOKQIRZNMUAKDEVFVFVHVIUBRZNUCMUDKBUD
      KZNMUEKDEVLJKVFBJKVHUFUGVIBUEKQIRZNUHUIZJKZVGVFFGVFVOLVEBBHUJVNVFVJVLVMVK
      FVNSUKULVEAVNJVEABUMKZVNCDEVFVJVLVMVKBFVFSVJSVKSVLSVMSUNUOUPUQVEURZTTJKVF
      VGUSBBHUTVAVQATJVQAVPTCBUMVBUOUPVCVD $.
  $}

  ${
    $d x y B $.  $d x y M $.  $d x y .+ $.  $d x y X $.  $d x y Y $.
    mendplusgfval.a $e |- A = ( MEndo ` M ) $.
    mendplusgfval.b $e |- B = ( Base ` A ) $.
    mendplusgfval.p $e |- .+ = ( +g ` M ) $.
    $( Addition in the module endomorphism algebra.  (Contributed by Stefan
       O'Rear, 2-Sep-2015.)  (Proof shortened by AV, 31-Oct-2024.) $)
    mendplusgfval $p |- ( +g ` A ) = ( x e. B , y e. B |-> ( x oF .+ y ) ) $=
      ( cvv wcel cplusg cfv co wceq cnx cbs cop eqid c0 cof cmpo cmulr ccom ctp
      cv csca cvsca csn cxp cpr cun cmend clmhm mendbas eqtr4i ofeq ax-mp oveqi
      wa a1i mpoeq3ia mendval eqtrid fveq2d fvexi mpoex algaddg eqtr4d wn fvprc
      mp1i plusgid str0 eqtr4di wo base0 3eqtr4g olcd 0mpo0 syl pm2.61i ) FJKZC
      LMZABDDAUFZBUFZEUAZNZUBZOWCWDPQMDRPLMZWIRPUCMABDDWEWFUDUBZRUEPUGMFUGMZRPU
      HMABWLQMDFQMWEUIUJWFFUHMUANUBZRUKULZLMZWIWCCWNLWCCFUMMZWNGABDWIWLWMWKFJDC
      QMZFFUNNHCFGUOUPABDDWHWEWFFLMZUAZNZWHWTOWEDKWFDKUTWGWSWEWFEWROWGWSOIEWRUQ
      URUSVAVBWKSWLSWMSVCVDVEWIJKWIWOOWCABDDWHDCQHVFZXAVGWNDWIWLWMWKJWNSVHVLVIW
      CVJZWDTWIXBWDTLMTXBCTLXBCWPTGFUMVKVDZVELWJVMVNVOXBDTOZXDVPWITOXBXDXDXBWQT
      QMDTXBCTQXCVEHVQVRVSABDDWHVTWAVIWB $.

    mendplusg.q $e |- .+b = ( +g ` A ) $.
    $( A specific addition in the module endomorphism algebra.  (Contributed by
       Stefan O'Rear, 3-Sep-2015.) $)
    mendplusg $p |- ( ( X e. B /\ Y e. B ) -> ( X .+b Y ) = ( X oF .+ Y ) ) $=
      ( vx vy cv cof co oveq12 cplusg cfv cmpo mendplusgfval eqtri ovex ovmpoa
      ) LMFGBBLNZMNZCOZPZFGUGPDUEFUFGUGQDARSLMBBUHTKLMABCEHIJUAUBFGUGUCUD $.
  $}

  ${
    $d x y B $.  $d x y M $.  $d x y X $.  $d x y Y $.
    mendmulrfval.a $e |- A = ( MEndo ` M ) $.
    mendmulrfval.b $e |- B = ( Base ` A ) $.
    $( Multiplication in the module endomorphism algebra.  (Contributed by
       Stefan O'Rear, 2-Sep-2015.)  (Proof shortened by AV, 31-Oct-2024.) $)
    mendmulrfval $p |- ( .r ` A ) = ( x e. B , y e. B |-> ( x o. y ) ) $=
      ( cvv cmulr cfv cmpo wceq cnx cbs cop co eqid eqtrid fveq2d c0 cplusg cof
      wcel cv ccom ctp cvsca csn cxp cpr cun cmend clmhm mendbas eqtr4i mendval
      csca fvexi mpoex algmulr mp1i wn fvprc mulridx str0 eqtr4di wo base0 olcd
      eqtr4d 0mpo0 syl pm2.61i ) EHUCZCIJZABDDAUDZBUDZUEZKZLVNVOMNJDOMUAJABDDVP
      VQEUAJUBPKZOMIJZVSOUFMUQJEUQJZOMUGJABWBNJDENJVPUHUIVQEUGJUBPKZOUJUKZIJZVS
      VNCWDIVNCEULJZWDFABDVTWBWCVSEHDCNJZEEUMPGCEFUNUOVTQVSQWBQWCQUPRSVSHUCVSWE
      LVNABDDVRDCNGURZWHUSWDDVTWBWCVSHWDQUTVAVJVNVBZVOTVSWIVOTIJTWICTIWICWFTFEU
      LVCRZSIWAVDVEVFWIDTLZWKVGVSTLWIWKWKWIDTNJZTWIDWGWLGWICTNWJSRVHVFVIABDDVRV
      KVLVJVM $.

    mendmulr.q $e |- .x. = ( .r ` A ) $.
    $( A specific multiplication in the module endormoprhism algebra.
       (Contributed by Stefan O'Rear, 3-Sep-2015.) $)
    mendmulr $p |- ( ( X e. B /\ Y e. B ) -> ( X .x. Y ) = ( X o. Y ) ) $=
      ( vx vy wcel ccom cvv co wceq coexg cv coeq1 coeq2 cmulr cfv mendmulrfval
      cmpo eqtri ovmpog mpd3an3 ) EBLFBLEFMZNLEFCOUHPEFBBQJKEFBBJRZKRZMZUHCEUJM
      NUIEUJSUJFETCAUAUBJKBBUKUDIJKABDGHUCUEUFUG $.
  $}

  ${
    $d x y M $.
    mendsca.a $e |- A = ( MEndo ` M ) $.
    mendsca.s $e |- S = ( Scalar ` M ) $.
    $( The module endomorphism algebra has the same scalars as the underlying
       module.  (Contributed by Stefan O'Rear, 2-Sep-2015.)  (Proof shortened
       by AV, 31-Oct-2024.) $)
    mendsca $p |- S = ( Scalar ` A ) $=
      ( vx vy csca cfv cmend cvv wcel wceq cnx cbs co cop cplusg cmpo eqid ccom
      clmhm cof cmulr ctp cvsca csn cxp cpr cun fvex algsca mp1i mendval fveq2d
      cv eqtr4d c0 scaid str0 eqcomi fveqprc pm2.61i fveq2i 3eqtr4i ) CHIZCJIZH
      IZBAHICKLZVFVHMVIVFNOICCUBPZQNRIFGVJVJFUPZGUPZCRIUCPSZQNUDIFGVJVJVKVLUASZ
      QUENHIZVFQNUFIFGVFOIVJCOIVKUGUHVLCUFIUCPSZQUIUJZHIZVHVFKLVFVRMVICHUKVQVJV
      MVFVPVNKVQTULUMVIVGVQHFGVJVMVFVPVNCKVJTVMTVNTVFTVPTUNUOUQHJCVGURURHIHVOUS
      UTVAVGTVBVCEAVGHDVDVE $.
  $}

  ${
    $d x y B $.  $d x y K $.  $d x y M $.
    mendvscafval.a $e |- A = ( MEndo ` M ) $.
    mendvscafval.v $e |- .x. = ( .s ` M ) $.
    mendvscafval.b $e |- B = ( Base ` A ) $.
    mendvscafval.s $e |- S = ( Scalar ` M ) $.
    mendvscafval.k $e |- K = ( Base ` S ) $.
    mendvscafval.e $e |- E = ( Base ` M ) $.
    $( Scalar multiplication in the module endomorphism algebra.  (Contributed
       by Stefan O'Rear, 2-Sep-2015.)  (Proof shortened by AV, 31-Oct-2024.) $)
    mendvscafval $p |- ( .s ` A ) = ( x e. K , y e. B |->
          ( ( E X. { x } ) oF .x. y ) ) $=
      ( cvsca cfv wceq cbs c0 cmend cv csn cxp cof cmpo fveq2i cvv wcel cnx cop
      cplusg cmulr ccom ctp csca cpr cun clmhm mendbas eqtr4i eqid xpeq1i ax-mp
      co ofeq oveq123i mpoeq123i mendval fveq2d fvexi mpoex algvsca mp1i eqtr4d
      wn fvprc vscaid str0 eqtr4di wo eqtrid base0 3eqtr4g orcd 0mpo0 syl eqtri
      pm2.61i ) CPQIUAQZPQZABHDGAUBZUCZUDZBUBZFUEZVEZUFZCWJPJUGIUHUIZWKWRRWSWKU
      JSQDUKUJULQABDDWLWOIULQUEVEUFZUKUJUMQABDDWLWOUNUFZUKUOUJUPQEUKUJPQZWRUKUQ
      URZPQZWRWSWJXCPABDWTEWRXAIUHDCSQIIUSVELCIJUTVAWTVBXAVBMABHDWQESQZDISQZWMU
      DZWOIPQZUEZVENDVBWNWOXGWOWPXIGXFWMOVCWOVBFXHRWPXIRKFXHVFVDVGVHVIVJWRUHUIW
      RXDRWSABHDWQHESNVKDCSLVKVLXCDWTEWRXAUHXCVBVMVNVOWSVPZWKTWRXJWKTPQTXJWJTPI
      UAVQVJPXBVRVSVTXJHTRZDTRZWAWRTRXJXKXLXJXETSQHTXJETSXJEIUPQTMIUPVQWBVJNWCW
      DWEABHDWQWFWGVOWIWH $.

    $d x y E $.  $d x y .x. $.  $d x y X $.  $d x y Y $.
    mendvsca.w $e |- .xb = ( .s ` A ) $.
    $( A specific scalar multiplication in the module endomorphism algebra.
       (Contributed by Stefan O'Rear, 3-Sep-2015.) $)
    mendvsca $p |- ( ( X e. K /\ Y e. B ) ->
        ( X .xb Y ) = ( ( E X. { X } ) oF .x. Y ) ) $=
      ( vx vy cv csn cxp cof co wceq xpeq2d id oveqan12d cvsca cfv mendvscafval
      sneq cmpo eqtri ovex ovmpoa ) RSIJGBFRTZUAZUBZSTZEUCZUDZFIUAZUBZJVAUDDUQI
      UEZUTJUEZUSVDUTJVAVEURVCFUQIULUFVFUGUHDAUIUJRSGBVBUMQRSABCEFGHKLMNOPUKUNV
      DJVAUOUP $.
  $}

  ${
    $d x y z A $.  $d k u v w x y z M $.  $d k u v w x y z S $.
    mendassa.a $e |- A = ( MEndo ` M ) $.
    $( The module endomorphism algebra is a ring.  (Contributed by Stefan
       O'Rear, 5-Sep-2015.) $)
    mendring $p |- ( M e. LMod -> A e. Ring ) $=
      ( vx vy wcel co cfv wceq ccom eqid mendplusg syl2anc sylibr 3eqtr4d eqtrd
      syl lmhmco mendmulr cvv clmod clmhm cplusg cmulr cid cbs cres mendbas a1i
      eqidd cminusg c0g csn cxp cof lmhmplusg eqeltrd 3adant1 w3a simpr1 simpr2
      vz cv wa simpr3 oveq1d oveq2d cmnd cmap lmodgrp grpmndd adantr lmhmf fvex
      wf elmap mndvass syl13anc csca 0lmhm syl3anc sylan mndvlid syl2an invlmhm
      sylancom cgrp grpvlinv isgrpd coass 3eqtr4a oveq12d cmhm cghm ghmmhm 3syl
      id lmghm mhmvlin wfn inidm ofco idlmhm adantl fcoi2 syl2anr fcoi1 isringd
      ffn ) BUAFZDEVBBBUBGZAUCHZAAUDHZUEBUFHZUGZXKAUFHIXJABCUHZUIZXJXLUJZXJXMUJ
      XJDEVBXKXLABUKHZDVCZJZXNBULHZUMUNZXQXRXTXKFZEVCZXKFZXTYEXLGZXKFXJYDYFVDZY
      GXTYEBUCHZUOZGZXKAXKYIXLBXTYECXPYIKZXLKZLZYIXTYEBBYLUPZUQURXJYDYFVBVCZXKF
      ZUSZVDZYKYPXLGZYKYPYJGZYGYPXLGXTYEYPXLGZXLGZYSYKXKFZYQYTUUAIYSYDYFUUDXJYD
      YFYQUTZXJYDYFYQVAZYOMZXJYDYFYQVEZAXKYIXLBYKYPCXPYLYMLMYSYGYKYPXLYSYDYFYGY
      KIUUEUUFYNMZVFYSXTYEYPYJGZXLGZXTUUJYJGZUUCUUAYSYDUUJXKFZUUKUULIUUEYSYFYQU
      UMUUFUUHYIYEYPBBYLUPMZAXKYIXLBXTUUJCXPYLYMLMYSUUBUUJXTXLYSYFYQUUBUUJIUUFU
      UHAXKYIXLBYEYPCXPYLYMLMZVGYSBVHFZXTXNXNVIGZFZYEUUQFZYPUUQFZUUAUULIXJUUPYR
      XJBBVJZVKZVLYSXNXNXTVOZUURYSYDUVCUUEXNXNBBXTXNKZUVDVMZQXNXNXTBUFVNZUVFVPZ
      NYSXNXNYEVOZUUSYSYFUVHUUFXNXNBBYEUVDUVDVMZQXNXNYEUVFUVFVPNZYSXNXNYPVOZUUT
      YSYQUVKUUHXNXNBBYPUVDUVDVMQZXNXNYPUVFUVFVPNZXNYIXNBXTYEYPUVDYLVQVROOXJXJX
      JBVSHZUVNIYCXKFZXJWQZUVPXJUVNUJXNUVNUVNBBYBYBKZUVDUVNKZUVRVTWAZXJYDVDZYCX
      TXLGZYCXTYJGZXTXJUVOYDUWAUWBIUVSAXKYIXLBYCXTCXPYLYMLWBXJUUPUURUWBXTIYDUVB
      YDUVCUURUVEUVGNZXNYIXNBXTYBUVDYLUVQWCWDPXJXSXKFYDYAXKFZXSBXSKZWEXSXTBBBRW
      BZUVTYAXTXLGZYAXTYJGZYCXJYDUWDUWGUWHIUWFAXKYIXLBYAXTCXPYLYMLWFXJBWGFUURUW
      HYCIYDUVAUWCXNYIBXNXSXTYBUVDYLUWEUVQWHWDPWIYDYFXTYEXMGZXKFXJYHUWIXTYEJZXK
      AXKXMBXTYECXPXMKZSZXTYEBBBRZUQURYSUWJYPJZXTYEYPJZJZUWIYPXMGZXTYEYPXMGZXMG
      ZXTYEYPWJYSUWQUWJYPXMGZUWNYSUWIUWJYPXMYSYDYFUWIUWJIUUEUUFUWLMZVFYSUWJXKFZ
      YQUWTUWNIYSYDYFUXBUUEUUFUWMMZUUHAXKXMBUWJYPCXPUWKSMPYSUWSXTUWOXMGZUWPYSUW
      RUWOXTXMYSYFYQUWRUWOIUUFUUHAXKXMBYEYPCXPUWKSMZVGYSYDUWOXKFZUXDUWPIUUEYSYF
      YQUXFUUFUUHYEYPBBBRMZAXKXMBXTUWOCXPUWKSMPWKYSXTUUJXMGZXTUUJJZXTUUBXMGUWIX
      TYPXMGZXLGZYSYDUUMUXHUXIIUUEUUNAXKXMBXTUUJCXPUWKSMYSUUBUUJXTXMUUOVGYSUWJX
      TYPJZXLGZUWJUXLYJGZUXKUXIYSUXBUXLXKFZUXMUXNIUXCYSYDYQUXOUUEUUHXTYPBBBRMZA
      XKYIXLBUWJUXLCXPYLYMLMYSUWIUWJUXJUXLXLUXAYSYDYQUXJUXLIUUEUUHAXKXMBXTYPCXP
      UWKSMZWLYSXTBBWMGFZUUSUUTUXIUXNIYSYDXTBBWNGFUXRUUEBBXTWRBBXTWOWPUVJUVMXNY
      IYIXTXNBBYEYPUVDYLYLWSWAOOYSYKYPXMGZYKYPJZYGYPXMGUXJUWRXLGZYSUUDYQUXSUXTI
      UUGUUHAXKXMBYKYPCXPUWKSMYSYGYKYPXMUUIVFYSUXLUWOXLGZUXLUWOYJGZUYAUXTYSUXOU
      XFUYBUYCIUXPUXGAXKYIXLBUXLUWOCXPYLYMLMYSUXJUXLUWRUWOXLUXQUXEWLYSXNXNXNXNY
      IXTYEYPTTTYSYDUVCXTXNWTUUEUVEXNXNXTXIWPYSYFUVHYEXNWTUUFUVIXNXNYEXIWPUVLXN
      TFYSUVFUIZUYDUYDXNXAXBOOXNBUVDXCZUVTXOXTXMGZXOXTJZXTXJXOXKFZYDUYFUYGIUYEA
      XKXMBXOXTCXPUWKSWBUVTUVCUYGXTIYDUVCXJUVEXDZXNXNXTXEQPUVTXTXOXMGZXTXOJZXTY
      DYDUYHUYJUYKIXJYDWQUYEAXKXMBXTXOCXPUWKSXFUVTUVCUYKXTIUYIXNXNXTXGQPXH $.

    mendassa.s $e |- S = ( Scalar ` M ) $.
    $( The module endomorphism algebra is a left module.  (Contributed by Mario
       Carneiro, 22-Sep-2015.) $)
    mendlmod $p |- ( ( M e. LMod /\ S e. CRing ) -> A e. LMod ) $=
      ( vy vk wcel cbs cfv co wceq eqidd syl cv w3a eqid mendvsca syl2anc cvv
      vx vz vw vv vu clmod ccrg wa cplusg cvsca cmulr cur clmhm mendbas mendsca
      a1i csca crg crngring adantl cgrp mendring adantr ringgrp csn cxp 3adant1
      cof lmhmvsca 3adant1l eqeltrd simpr2 simpr3 mendplusg oveq2d simpr1 grpcl
      syl3anc oveq12d 3adant3r3 eleq1w 3anbi3d eleq1d imbi12d chvarvv 3adant3r2
      wi oveq2 fvexd wf fconst6g lmhmf simpll lmodvsdi caofdi 3eqtr4d lmodvsdir
      sylan caofdir ringacl ofc12 oveq1d eqtr4d oveq1 3adant3r1 cmpt ffvelcdmda
      3anbi2d eqtrd fconstmpt feqmptd offval2 ringcl simplr2 lmodvsass syl13anc
      ovexd mpteq2dva ringidcl sylancom lmodvs1 caofid0l islmodd ) CUFHZBUGHZUH
      ZUAFUBBIJZAUIJZBUIJZAUJJZBUKJZBULJZBCCUMKZAYMAIJLYFACDUNZUPYFYHMBAUQJLYFA
      BCDEUOUPYFYJMYFYGMYFYIMYFYKMYFYLMYEBURHZYDBUSUTZYFAURHZAVAHZYDYQYEACDVBVC
      AVDNZYFUAOZYGHZFOZYMHZPZYTUUBYJKZCIJZYTVEVFZUUBCUJJZVHZKZYMUUAUUCUUEUUJLZ
      YFAYMBYJUUHUUFYGCYTUUBDUUHQZYNEYGQZUUFQZYJQZRZVGYEUUAUUCUUJYMHYDYTUUHUUBB
      YGCCUUFUUNUULEUUMVIVJVKZYFUUAUUCUBOZYMHZPZUHZUUGUUBUURYHKZUUIKZUUGUUBUURC
      UIJZVHZKZUUIKZYTUVBYJKZUUEYTUURYJKZYHKZUVAUVBUVFUUGUUIUVAUUCUUSUVBUVFLYFU
      UAUUCUUSVLZYFUUAUUCUUSVMZAYMUVDYHCUUBUURDYNUVDQZYHQZVNSVOUVAUUAUVBYMHZUVH
      UVCLYFUUAUUCUUSVPZUVAYRUUCUUSUVOYFYRUUTYSVCUVKUVLYMYHAUUBUURYNUVNVQVRAYMB
      YJUUHUUFYGCYTUVBDUULYNEUUMUUNUUORSUVAUUEUVIUVEKZUUJUUGUURUUIKZUVEKUVJUVGU
      VAUUEUUJUVIUVRUVEUVAUUAUUCUUKUVPUVKUUPSUVAUUAUUSUVIUVRLZUVPUVLAYMBYJUUHUU
      FYGCYTUURDUULYNEUUMUUNUUORZSVSUVAUUEYMHZUVIYMHZUVJUVQLYFUUAUUCUWAUUSUUQVT
      YFUUAUUSUWBUUCUUDUWAWGYFUUAUUSPZUWBWGZFUBUUBUURLZUUDUWCUWAUWBUWEUUCUUSYFU
      UAFUBYMWAWBUWEUUEUVIYMUUBUURYTYJWHWCWDUUQWEZWFAYMUVDYHCUUEUVIDYNUVMUVNVNS
      UVAUCUDUEUUFUVDUUFUUHUUGUUBUURYGUVDTUVACIWIUVAUUAUUFYGUUGWJZUVPUUFYTYGWKZ
      NUVAUUCUUFUUFUUBWJUVKUUFUUFCCUUBUUNUUNWLNUVAUUSUUFUUFUURWJZUVLUUFUUFCCUUR
      UUNUUNWLZNUVAYDUCOZYGHZUDOZUUFHUEOZUUFHZPUWKUWMUWNUVDKUUHKUWKUWMUUHKUWKUW
      NUUHKZUVDKLYDYEUUTWMUVDUWKUUHBYGUUFCUWMUWNUUNUVMEUULUUMWNWRWOWPWPYFUUAUUB
      YGHZUUSPZUHZUUGUUFUUBVEVFZYIVHKZUURUUIKZUVRUWTUURUUIKZUVEKZYTUUBYIKZUURYJ
      KZUVIUUBUURYJKZYHKZUWSUCUDUEUUFYIYGUUHUURUUGUWTUUFUVDTUWSCIWIZUWSUUSUWIYF
      UUAUWQUUSVMZUWJNZUWSUUAUWGYFUUAUWQUUSVPZUWHNUWSUWQUUFYGUWTWJYFUUAUWQUUSVL
      ZUUFUUBYGWKNUWSYDUWLUWMYGHUWOPUWKUWMYIKUWNUUHKUWPUWMUWNUUHKUVDKLYDYEUWRWM
      ZUVDYIUWKUWMUUHBYGUUFCUWNUUNUVMEUULUUMYIQZWQWRWSUWSUXFUUFUXEVEVFZUURUUIKZ
      UXBUWSUXEYGHZUUSUXFUXQLUWSYOUUAUWQUXRYFYOUWRYPVCZUXLUXMYGYIBYTUUBUUMUXOWT
      VRUXJAYMBYJUUHUUFYGCUXEUURDUULYNEUUMUUNUUORSUWSUXAUXPUURUUIUWSUUFYTUUBYIT
      YGYGUXIUXLUXMXAXBXCUWSUXHUVIUXGUVEKZUXDUWSUWBUXGYMHZUXHUXTLYFUUAUUSUWBUWQ
      UWFWFYFUWQUUSUYAUUAUWDYFUWQUUSPZUYAWGUAFYTUUBLZUWCUYBUWBUYAUYCUUAUWQYFUUS
      UAFYGWAXHUYCUVIUXGYMYTUUBUURYJXDWCWDUWFWEXEZAYMUVDYHCUVIUXGDYNUVMUVNVNSUW
      SUVIUVRUXGUXCUVEUWSUUAUUSUVSUXLUXJUVTSUWSUWQUUSUXGUXCLUXMUXJAYMBYJUUHUUFY
      GCUUBUURDUULYNEUUMUUNUUORSZVSXIWPUWSUUFYTUUBYKKZVEVFZUURUUIKZGUUFUYFGOZUU
      RJZUUHKZXFZUYFUURYJKZYTUXGYJKZUWSGUUFUYFUYJUUHUYGUURTTUUFUXIUWSUYIUUFHZUH
      ZYTUUBYKXQUWSUUFUUFUYIUURUXKXGZUYGGUUFUYFXFLUWSGUUFUYFXJUPUWSGUUFUUFUURUX
      KXKZXLUWSUYFYGHZUUSUYMUYHLUWSYOUUAUWQUYSUXSUXLUXMYGBYKYTUUBUUMYKQZXMVRUXJ
      AYMBYJUUHUUFYGCUYFUURDUULYNEUUMUUNUUORSUWSUUGUXGUUIKZGUUFYTUUBUYJUUHKZUUH
      KZXFUYNUYLUWSGUUFYTVUBUUHUUGUXGTYGTUXIUWSUUAUYOUXLVCZUYPUUBUYJUUHXQUUGGUU
      FYTXFLUWSGUUFYTXJUPUWSUXGUXCGUUFVUBXFUYEUWSGUUFUUBUYJUUHUWTUURTYGUUFUXIUU
      AUWQUUSYFUYOXNZUYQUWTGUUFUUBXFLUWSGUUFUUBXJUPUYRXLXIXLUWSUUAUYAUYNVUALUXL
      UYDAYMBYJUUHUUFYGCYTUXGDUULYNEUUMUUNUUORSUWSGUUFUYKVUCUYPYDUUAUWQUYJUUFHU
      YKVUCLUWSYDUYOUXNVCVUDVUEUYQYTUUBUUHYKBYGUUFCUYJUUNEUULUUMUYTXOXPXRWPWPYF
      YTYMHZUHZYLYTYJKZUUFYLVEVFYTUUIKZYTYFVUFYLYGHZVUHVUILVUGYOVUJYFYOVUFYPVCY
      GBYLUUMYLQZXSNZAYMBYJUUHUUFYGCYLYTDUULYNEUUMUUNUUORXTVUGFUUFYLUUHUUFYTTYG
      VUGCIWIVUFUUFUUFYTWJYFUUFUUFCCYTUUNUUNWLUTVULVUGYDUUBUUFHYLUUBUUHKUUBLYDY
      EVUFWMUUHYLBUUFCUUBUUNEUULVUKYAWRYBXIYC $.

    $( The module endomorphism algebra is an algebra.  (Contributed by Mario
       Carneiro, 22-Sep-2015.) $)
    mendassa $p |- ( ( M e. LMod /\ S e. CRing ) -> A e. AssAlg ) $=
      ( vv vw wcel wa cbs cfv co wceq a1i cv cmpt eqid syl2anc cvv syl3anc ccrg
      vy vz vx clmod cvsca cmulr clmhm mendbas csca eqidd mendlmod crg mendring
      mendsca adantr w3a ccom csn cxp cof wf simpr3 lmhmf syl ffvelcdmda simpr1
      feqmptd simpr2 mendvsca fvexd simplr1 fconstmpt eqtrd fveq2 oveq2d fmptco
      offval2 mendmulr fcompt eqtr4d lmodvscl 3eqtr4d simplr2 lmhmlin mpteq2dva
      ringcl simplll isassad ) CUEHZBUAHZIZUBUCBJKZAUFKZAUGKZBCCUHLZAUDWPAJKMWL
      ACDUIZNBAUJKMWLABCDEUOZNWLWMUKWLWNUKWLWOUKABCDEULZWJAUMHZWKACDUNUPZWLUDOZ
      WMHZUBOZWPHZUCOZWPHZUQZIZXBXDWNLZXFURZCJKZXBUSUTZXDXFWOLZCUFKZVAZLZXJXFWO
      LZXBXNWNLZXIXKFXLXBFOZXFKZXDKZXOLZPZXQXIFGXLXLYAXBGOZXDKZXOLZYCXFXJXIXLXL
      XTXFXIXGXLXLXFVBZWLXCXEXGVCZXLXLCCXFXLQZYJVDVEZVFZXIFXLXLXFYKVHZXIXJXMXDX
      PLZGXLYGPXIXCXEXJYNMWLXCXEXGVGZWLXCXEXGVIZAWPBWNXOXLWMCXBXDDXOQZWQEWMQZYJ
      WNQZVJRXIGXLXBYFXOXMXDSWMSXICJVKZXCXEXGWLYEXLHZVLXIUUAIYEXDVKXMGXLXBPMXIG
      XLXBVMNXIGXLXLXDXIXEXLXLXDVBZYPXLXLCCXDYJYJVDVEZVHZVRVNYEYAMYFYBXBXOYEYAX
      DVOVPVQXIFXLXBYBXOXMXNSWMSYTXCXEXGWLXTXLHZVLZXIUUEIZYAXDVKXMFXLXBPMXIFXLX
      BVMNZXIXNXDXFURZFXLYBPZXIXEXGXNUUIMYPYIAWPWOCXDXFDWQWOQZVSRXIUUBYHUUIUUJM
      UUCYKFXDXFXLXLXLVTRVNVRZWAXIXJWPHZXGXRXKMXIAUEHZXCXEUUMWLUUNXHWSUPZYOYPXB
      WNBWMWPAXDWQWRYSYRWBTYIAWPWOCXJXFDWQUUKVSRXIXCXNWPHZXSXQMYOXIWTXEXGUUPWLW
      TXHXAUPYPYIWPAWOXDXFWQUUKWGTAWPBWNXOXLWMCXBXNDYQWQEYRYJYSVJRZWCXIXDXBXFWN
      LZURZXQXDUURWOLZXSXIFXLXBYAXOLZXDKZPYDUUSXQXIFXLUVBYCUUGXEXCYAXLHZUVBYCMX
      CXEXGWLUUEWDUUFYLWMCCXOXOXLXDBXBYAEYRYJYQYQWETWFXIFGXLXLUVAYFUVBUURXDUUGW
      JXCUVCUVAXLHWJWKXHUUEWHUUFYLXBXOBWMXLCYAYJEYQYRWBTXIUURXMXFXPLZFXLUVAPXIX
      CXGUURUVDMYOYIAWPBWNXOXLWMCXBXFDYQWQEYRYJYSVJRXIFXLXBYAXOXMXFSWMSYTUUFUUG
      XTXFVKUUHYMVRVNUUDYEUVAXDVOVQUULWCXIXEUURWPHZUUTUUSMYPXIUUNXCXGUVEUUOYOYI
      XBWNBWMWPAXFWQWRYSYRWBTAWPWOCXDUURDWQUUKVSRUUQWCWI $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  The class equation
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Cyclic groups and order
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(
  @{
    isgenod.o @e |- O = ( od ` G ) @.
    isgenod.b @e |- B = ( Base ` G ) @.
    isgenod.k @e |- K = ( mrCls ` ( SubGrp ` G ) ) @.

    @( An element generates a (cyclic) group iff it has full order.
      (Contributed by Stefan O'Rear, 11-Sep-2015.) @)
    isgenod @p |- ( ( G e Grp /\ B e. Fin /\ X e. B ) ->
        ( ( K ` { X } ) = B <-> ( O ` X ) = ( # ` B ) ) ) @= ? @.
  @}
$)

  ${
    $d x B $.  $d x N $.  $d x R $.
    idomodle.g $e |- G = ( ( mulGrp ` R ) |`s ( Unit ` R ) ) $.
    idomodle.b $e |- B = ( Base ` G ) $.
    idomodle.o $e |- O = ( od ` G ) $.
    $( Limit on the number of ` N ` -th roots of unity in an integral domain.
       (Contributed by Stefan O'Rear, 12-Sep-2015.) $)
    idomodle $p |- ( ( R e. IDomn /\ N e. NN ) ->
        ( # ` { x e. B | ( O ` x ) || N } ) <_ N ) $=
      ( wcel cfv wbr crab chash wceq cbs cvv cxr syl eqid cidom cn wa cdvds cmg
      cv cmgp cur fvexi rabex hashxrcl mp1i fvex nnre rexrd adantl cle c0g cgrp
      co cz crg ccrg cdomn isidom simplbi adantr crngring cui unitgrp simpr nnz
      wb ad2antlr oddvds syl3anc csubmnd cn0 unitsubm nnnn0 unitgrpbas eleqtrdi
      eqtr4i submmulg unitgrpid eqeq12d bitr4d fveq2d cdom unitss rabss2 ssdomg
      rabbidva wss mpsyl hashdomi eqbrtrd simpl ringidcl idomrootle xrletrd ) C
      UAJZEUBJZUCZAUFZFKEUDLZABMZNKZEXECUGKZUEKZUTZCUHKZOZACPKZMZNKZEXGQJXHRJXD
      XFABBDPHUIUJXGQUKULXOQJZXPRJXDXMAXNCPUMUJZXOQUKULXCERJXBXCEEUNUOUPXDXHXMA
      BMZNKZXPUQXDXGXSNXDXFXMABXDXEBJZUCZXFEXEDUEKZUTZDURKZOZXMYBDUSJZYAEVAJZXF
      YFVMYBCVBJZYGXDYIYAXDCVCJZYIXBYJXCXBYJCVDJCVEVFVGCVHSZVGZCCVIKZDYMTZGVJSX
      DYAVKZXCYHXBYAEVLVNXEYCDEFBYEHIYCTZYETVOVPYBXKYDXLYEYBYMXIVQKJZEVRJZXEYMJ
      XKYDOYBYIYQYLCYMXIYNXITVSSXCYRXBYAEVTVNYBXEBYMYOBDPKYMHCYMDYNGWAWCZWBYMXJ
      YCXIDEXEXJTZGYPWDVPYBYIXLYEOYLCYMXLDYNGXLTZWESWFWGWMWHXDXSXOWILZXTXPUQLXQ
      XDXSXOWNZUUBXRBXNWNUUCXDXNCBXNTZYSWJXMABXNWKULXSXOQWLWOXSXOWPSWQXDXBXLXNJ
      ZXCXPEUQLXBXCWRXDYIUUEYKXNCXLUUDUUAWSSXBXCVKAXNCXJEXLUUDYTWTVPXA $.
  $}

  $( Two finite sets of equal size have a union of the same size iff they were
     equal.  (Contributed by Stefan O'Rear, 12-Sep-2015.) $)
  fiuneneq $p |- ( ( A ~~ B /\ A e. Fin ) ->
      ( ( A u. B ) ~~ A <-> A = B ) ) $=
    ( cen wbr cfn wcel wa cun wceq w3a wss simp2 wb 3ad2ant1 syl2anc a1i ensymd
    enfi fisseneq syl3anc mpbid unfi ssun1 simp3 ssun2 simp1 entr eqtr4d 3expia
    enrefg adantl unidm uneq2 eqtr3id breq1d syl5ibcom impbid ) ABCDZAEFZGZABHZ
    ACDZABIZURUSVBVCURUSVBJZAVABVDVAEFZAVAKZAVACDAVAIVDUSBEFZVEURUSVBLZVDUSVGVH
    URUSUSVGMVBABRNUAABUBOZVFVDABUCPVDVAAURUSVBUDZQAVASTVDVEBVAKZBVACDBVAIVIVKV
    DBAUEPVDVABVDVBURVABCDVJURUSVBUFVAABUGOQBVASTUHUIUTAACDZVCVBUSVLURAEUJUKVCA
    VAACVCAAAHVAAULABAUMUNUOUPUQ $.

  ${
    $d x y z G $.  $d x y z N $.  $d x y z R $.
    idomsubgmo.g $e |- G = ( ( mulGrp ` R ) |`s ( Unit ` R ) ) $.
    $( The units of an integral domain have at most one subgroup of any single
       finite cardinality.  (Contributed by Stefan O'Rear, 12-Sep-2015.)
       (Revised by NM, 17-Jun-2017.) $)
    idomsubgmo $p |- ( ( R e. IDomn /\ N e. NN ) ->
        E* y e. ( SubGrp ` G ) ( # ` y ) = N ) $=
      ( vx vz wcel wa cv chash cfv wbr cdom cdvds cvv wss cn0 wb adantr cn wceq
      cidom weq csubg wral wrmo w3a cun cen cod cbs crab fvex rabex simp2l eqid
      subgss syl wel cfn simpl2l simp3l simp1r nnnn0d eqeltrd vex hashclb ax-mp
      sylibr simpr odsubdvds syl3anc breqtrd ssrabdv simp2r simp3r unssd ssdomg
      wi simpl2r mpsyl cle idomodle 3ad2ant1 breqtrrd a1i hashbnd hashdom mpbid
      sylancl domtr syl2anc unex ssun1 mp2 sbth eqtr4d hashen 3expia ralrimivva
      fiuneneq fveqeq2 rmo4 ) BUCHZDUAHZIZAJZKLZDUBZFJZKLZDUBZIZAFUDZVTZFCUELZU
      FAXQUFXJAXQUGXGXPAFXQXQXGXHXQHZXKXQHZIZXNXOXGXTXNUHZXHXKUIZXHUJMZXOYAYBXH
      NMZXHYBNMZYCYAYBGJZCUKLZLZDOMZGCULLZUMZNMZYKXHNMZYDYKPHZYAYBYKQYLYIGYJCUL
      UNUOZYAXHXKYKYAYIGYJXHYAXRXHYJQXGXRXSXNUPYJXHCYJUQZURUSYAGAUTZIZYHXIDOYRX
      RXHVAHZYQYHXIOMXRXSXGXNYQVBYAYSYQYAXIRHZYSYAXIDRXGXTXJXMVCZYADXEXFXTXNVDV
      EZVFZXHPHZYSYTSAVGZXHPVHVIVJZTYAYQVKYFXHCYGYGUQZVLVMYAXJYQUUATVNVOYAYIGYJ
      XKYAXSXKYJQXGXRXSXNVPYJXKCYPURUSYAGFUTZIZYHXLDOUUIXSXKVAHZUUHYHXLOMXRXSXG
      XNUUHWAYAUUJUUHYAXLRHZUUJYAXLDRXGXTXJXMVQZUUBVFXKPHUUJUUKSFVGZXKPVHVIVJZT
      YAUUHVKYFXKCYGUUGVLVMYAXMUUHUULTVNVOVRYBYKPVSWBYAYKKLZXIWCMZYMYAUUODXIWCX
      GXTUUODWCMXNGYJBCDYGEYPUUGWDWEUUAWFZYAYKVAHZUUDUUPYMSYAYNYTUUPUURYNYAYOWG
      UUCUUQYKXIPWHVMUUEYKXHPWIWKWJYBYKXHWLWMYBPHXHYBQYEXHXKUUEUUMWNXHXKWOXHYBP
      VSWPYBXHWQWKYAXHXKUJMZYSYCXOSYAXIXLUBZUUSYAXIDXLUUAUULWRYAYSUUJUUTUUSSUUF
      UUNXHXKWSWMWJUUFXHXKXBWMWJWTXAXJXMAFXQXHXKDKXCXDVJ $.

    $d x K $.  $d x X $.  $d x Y $.
    proot1mul.o $e |- O = ( od ` G ) $.
    proot1mul.k $e |- K = ( mrCls ` ( SubGrp ` G ) ) $.
    $( Any primitive ` N ` -th root of unity is a multiple of any other.
       (Contributed by Stefan O'Rear, 2-Nov-2015.) $)
    proot1mul $p |- ( ( ( R e. IDomn /\ N e. NN ) /\
          ( X e. ( `' O " { N } ) /\ Y e. ( `' O " { N } ) ) ) ->
        X e. ( K ` { Y } ) ) $=
      ( vx wcel cn wa csn cfv wss wceq wb chash cidom ccnv cima csubg cgrp cacs
      cbs cmre crg simpll ccrg isidom simprbi domnring cui eqid unitgrp subgacs
      cdomn 4syl acsmre 3syl simprl cn0 wfn odf ffn fniniseg sylib simpld snssd
      wf mp2b mrcssidd snssg syl mpbird cv wrmo idomsubgmo adantr mrccl syl2anc
      simprd simplr eqeltrd odhash2 syl3anc eqtrd simprr fveqeq2 rmoi syl122anc
      eleqtrd ) AUALZDMLZNZFEUBDOUCZLZGWRLZNZNZFFOZCPZGOZCPZXBFXDLZXCXDQZXBBUDP
      ZXCCBUGPZXBBUELZXIXJUFPLXIXJUHPLZXBWOAUSLZAUILXKWOWPXAUJWOAUKLXMAULUMAUNA
      AUOPZBXNUPHUQUTZXJBXJUPZURXIXJVAVBZJXBFXJXBFXJLZFEPZDRZXBWSXRXTNZWQWSWTVC
      ZXJVDEVLZEXJVEZWSYASBEXJXPIVFZXJVDEVGZXJDFEVHVMVIZVJZVKZVNXBWSXGXHSYBFXDW
      RVOVPVQXBKVRZTPDRZKXIVSZXDXILZXDTPZDRZXFXILZXFTPZDRZXDXFRWQYLXAKABDHVTWAX
      BXLXCXJQYMXQYIXIXCCXJJWBWCXBYNXSDXBXKXRXSMLYNXSRXOYHXBXSDMXBXRXTYGWDZWOWP
      XAWEZWFFBCEXJXPIJWGWHYSWIXBXLXEXJQYPXQXBGXJXBGXJLZGEPZDRZXBWTUUAUUCNZWQWS
      WTWJYCYDWTUUDSYEYFXJDGEVHVMVIZVJZVKXIXECXJJWBWCXBYQUUBDXBXKUUAUUBMLYQUUBR
      XOUUFXBUUBDMXBUUAUUCUUEWDZYTWFGBCEXJXPIJWGWHUUGWIYKYOYRKXIXDXFYJXDDTWKYJX
      FDTWKWLWMWN $.
  $}

  ${
    $d x G $.  $d x N $.  $d x O $.  $d x R $.  $d x X $.
    proot1hash.g $e |- G = ( ( mulGrp ` R ) |`s ( Unit ` R ) ) $.
    proot1hash.o $e |- O = ( od ` G ) $.
    $( If an integral domain has a primitive ` N ` -th root of unity, it has
       exactly ` ( phi `` N ) ` of them.  (Contributed by Stefan O'Rear,
       12-Sep-2015.) $)
    proot1hash $p |- ( ( R e. IDomn /\ N e. NN /\ X e. ( `' O " { N } ) ) ->
        ( # ` ( `' O " { N } ) ) = ( phi ` N ) ) $=
      ( vx wcel cn csn chash cfv wceq crab cphi cn0 eqid mp2b 3syl ccnv cima cv
      cidom w3a csubg cmrc cbs wf wfn odf ffn fniniseg2 wa simp3 fniniseg sylib
      cin wb simprd eqeq2d rabbidv cmre wss cgrp cacs cdomn ccrg isidom simprbi
      crg 3ad2ant1 domnring unitgrp subgacs acsmre mrcssv dfrab3ss incom simpl1
      cui simpl2 simpr simpl3 proot1mul syl22anc ssrdv eqsstrrid eqtrid 3eqtrrd
      ex dfss2 fveq2d simpld simp2 eqeltrd odngen syl3anc 3eqtrd ) AUDIZCJIZEDU
      ACKUBZIZUEZXBLMHUCZDMZEDMZNZHEKZBUFMZUGMZMZOZLMZXGPMZCPMXDXBXMLXDXBXFCNZH
      BUHMZOZXMXQQDUIZDXQUJZXBXRNBDXQXQRZGUKZXQQDULZHXQCDUMSZXDXMXPHXLOZXLXRURZ
      XRXDXHXPHXLXDXGCXFXDEXQIZXGCNZXDXCYGYHUNZWTXAXCUOXSXTXCYIUSYBYCXQCEDUPSUQ
      ZUTZVAVBXDXJXQVCMIZXLXQVDYEYFNXDBVEIZXJXQVFMIYLXDAVGIZAVKIYMWTXAYNXCWTAVH
      IYNAVIVJVLAVMAAWAMZBYORFVNTZXQBYAVOXJXQVPTXJXIXKXQXKRZVQXPHXLXQVRTXDYFXRX
      LURZXRXLXRVSXDXRXLVDYRXRNXDXRXBXLYDXDHXBXLXDXEXBIZXEXLIZXDYSUNWTXAYSXCYTW
      TXAXCYSVTWTXAXCYSWBXDYSWCWTXAXCYSWDABXKCDXEEFGYQWEWFWKWGWHXRXLWLUQWIWJWIW
      MXDYMYGXGJIXNXONYPXDYGYHYJWNXDXGCJYKWTXAXCWOWPHEBXKDXQYAGYQWQWRXDXGCPYKWM
      WS $.
  $}

  ${
    $d x G $.  $d x N $.  $d x O $.
    proot1ex.g $e |- G = ( ( mulGrp ` CCfld ) |`s ( CC \ { 0 } ) ) $.
    proot1ex.o $e |- O = ( od ` G ) $.
    $( The complex field has primitive ` N ` -th roots of unity for all ` N ` .
       (Contributed by Stefan O'Rear, 12-Sep-2015.) $)
    proot1ex $p |- ( N e. NN -> ( -u 1 ^c ( 2 / N ) ) e. ( `' O " { N } ) ) $=
      ( wcel c1 c2 cdiv co cc cc0 cfv wceq a1i cn0 cmul ci cpi ccnfld cneg ccxp
      vx ccnv csn cima cdif wne neg1cn crp 2rp nnrp rpdivcl sylancr rpcnd cxpcl
      cn neg1ne0 cxpne0d eldifsn sylanbrc cv cdvds wbr wb wral wa cz clog nn0cn
      cmg ce mulcl syl2an cxpefd eqeq1d logcl mp2an sylancl syl 2cn nncn adantr
      efeq1 adantl nnne0 div13d logm1 oveq12d divcld ax-icn picn mulcli mulassd
      mul12d oveq2d 3eqtrd ine0 2ne0 pire pipos gt0ne0ii mulne0i divcan4d eqtrd
      oveq1d eleq1d 3bitrd cexp cmgp simpr cxpmul2d cnfldexp csubmnd crg cnring
      sylan cnfldbas cnfld0 cndrng eqid unitsubm mp1i submmulg syl3anc 3eqtr2rd
      drngui nnz nn0z dvdsval2 3bitr4rd ralrimiva cgrp unitgrp nnnn0 unitgrpbas
      c0g cnfld1 unitgrpid ax-mp odeq mpbird eqcomd wfn odf fniniseg mpbir2and
      wf ffn ) BUQFZGUAZHBIJZUBJZCUDBUEUFFZUUMKLUEUGZFZUUMCMZBNZUUJUUMKFZUUMLUH
      UUPUUJUUKKFZUULKFZUUSUIUUJUULUUJHUJFBUJFUULUJFUKBULHBUMUNUOZUUKUULUPUNZUU
      JUUKUULUUTUUJUIOUUKLUHZUUJUROUVBUSUUMKLUTVAZUUJBUUQUUJBUUQNZBUCVBZVCVDZUV
      GUUMAVKMZJZGNZVEZUCPVFZUUJUVLUCPUUJUVGPFZVGZUUKUULUVGQJZUBJZGNZUVGBIJZVHF
      ZUVKUVHUVOUVRUVPUUKVIMZQJZVLMZGNZUWBRHSQJZQJZIJZVHFZUVTUVOUVQUWCGUVOUUKUV
      PUUTUVOUIOZUVDUVOUROUUJUVAUVGKFZUVPKFZUVNUVBUVGVJZUULUVGVMVNZVOVPUVOUWBKF
      ZUWDUWHVEUVOUWKUWAKFZUWNUWMUUTUVDUWOUIURUUKVQVRUVPUWAVMVSUWBWDVTUVOUWGUVS
      VHUVOUWGUVSUWFQJZUWFIJUVSUVOUWBUWPUWFIUVOUWBUVSHQJZRSQJZQJUVSHUWRQJZQJUWP
      UVOUVPUWQUWAUWRQUVOHBUVGHKFUVOWAOZUUJBKFUVNBWBWCZUVNUWJUUJUWLWEZUUJBLUHZU
      VNBWFWCZWGUWAUWRNUVOWHOWIUVOUVSHUWRUVOUVGBUXBUXAUXDWJZUWTUWRKFUVORSWKWLWM
      OWNUVOUWSUWFUVSQUVOHRSUWTRKFUVOWKOSKFUVOWLOWOWPWQXFUVOUVSUWFUXEUWFKFUVORU
      WEWKHSWAWLWMZWMOUWFLUHUVORUWEWKUXFWRHSWAWLWSSWTXAXBXCXCOXDXEXGXHUVOUVJUVQ
      GUVOUVQUUMUVGXIJZUVGUUMTXJMZVKMZJZUVJUVOUUKUULUVGUWIUUJUVAUVNUVBWCUUJUVNX
      KZXLUUJUUSUVNUXJUXGNUVCUUMUVGXMXQUVOUUOUXHXNMFZUVNUUPUXJUVJNTXOFZUXLUVOXP
      TUUOUXHKTLXRXSXTYGZUXHYAYBYCUXKUUJUUPUVNUVEWCUUOUXIUVIUXHAUVGUUMUXIYADUVI
      YAZYDYEYFVPUVOBVHFZUXCUVGVHFZUVHUVTVEUUJUXPUVNBYHWCUXDUVNUXQUUJUVGYIWEBUV
      GYJYEYKYLUUJAYMFZUUPBPFUVFUVMVEUXMUXRUUJXPTUUOAUXNDYNYCUVEBYOUCUUMUVIABCU
      UOGTUUOAUXNDYPZEUXOUXMGAYQMNXPTUUOGAUXNDYRYSYTUUAYEUUBUUCCUUOUUDZUUNUUPUU
      RVGVEUUJUUOPCUUHUXTACUUOUXSEUUEUUOPCUUIYTUUOBUUMCUUFYCUUG $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Cyclotomic polynomials
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c CytP $.
  $( Syntax for the sequence of cyclotomic polynomials. $)
  ccytp $a class CytP $.

  ${
    $d n r $.
    $( The Nth _cyclotomic polynomial_ is the polynomial which has as its zeros
       precisely the primitive Nth roots of unity.  (Contributed by Stefan
       O'Rear, 5-Sep-2015.) $)
    df-cytp $a |- CytP = ( n e. NN |-> ( ( mulGrp ` ( Poly1 ` CCfld ) ) gsum
        ( r e. ( `' ( od ` ( ( mulGrp ` CCfld ) |`s ( CC \ { 0 } ) ) ) " { n
        } ) |-> ( ( var1 ` CCfld ) ( -g ` ( Poly1 ` CCfld ) ) ( ( algSc ` (
        Poly1 ` CCfld ) ) ` r ) ) ) ) ) $.
  $}

$(
  @{
    mon1pvr.x @e |- X = ( var1 ` R ) @.
    mon1pvr.m @e |- M = ( Monic1p ` R ) @.
    mon1pvr.d @e |- D = ( deg1 ` R ) @.
    @( Monicity and degree of the polynomial generator.  (Contributed by
       Stefan O'Rear, 12-Sep-2015.) @)
    mon1pvr @p |- ( R e. NzRing -> ( X e. M /\ ( D ` X ) = 1 ) ) @= ? @.
  @}

  @{
    mon1plin.p @e |- P = ( Poly1 ` R ) @.
    mon1plin.x @e |- X = ( var1 ` R ) @.
    mon1plin.m @e |- M = ( Monic1p ` R ) @.
    mon1plin.d @e |- D = ( deg1 ` R ) @.
    mon1plin.s @e |- .- = ( -g ` P ) @.
    mon1plin.a @e |- A = ( algSc ` P ) @.
    mon1plin.k @e |- K = ( Base ` R ) @.
    @( Monicity and degree of a linear factor.  (Contributed by Stefan O'Rear,
       12-Sep-2015.) @)
    mon1plin @p |- ( ( R e. NzRing /\ Y e. K ) ->
        ( ( X .- ( A ` Y ) ) e. M /\ ( D ` ( X .- ( A ` Y ) ) ) = 1 ) ) @= ? @.
  @}
$)

  ${
    $d x y M $.  $d x P $.  $d x y R $.  $d x y U $.
    mon1psubm.p $e |- P = ( Poly1 ` R ) $.
    mon1psubm.m $e |- M = ( Monic1p ` R ) $.
    mon1psubm.u $e |- U = ( mulGrp ` P ) $.
    $( Monic polynomials are a multiplicative submonoid.  (Contributed by
       Stefan O'Rear, 12-Sep-2015.) $)
    mon1psubm $p |- ( R e. NzRing -> M e. ( SubMnd ` U ) ) $=
      ( vx vy wcel cfv co eqid wceq wne cco1 syl adantr ad2antrl cn0 csubmnd cv
      cnzr cbs wss cur cmulr wral mon1pcl ssriv a1i cdg1 cc0 mon1pid simpld c0g
      wa crg ply1nz nzrring simprr sselid ringcl syl3anc caddc mon1pn0 mon1pldg
      crlreg unitrrg 1unit sseldd eqeltrd ad2antll deg1mul2 deg1nn0cl nn0addcld
      cui deg1nn0clb syl2anc mpbird coe1mul4 oveq12d ringidcl ringlidm syl2anc2
      wb fveq2d eqtrd ismon1p syl3anbrc ralrimivva w3a ringmgp mgpbas ringidval
      cmnd mgpplusg issubm mpbir3and ) BUCJZDCUAKJZDAUDKZUEZAUFKZDJZHUBZIUBZAUG
      KZLZDJZIDUHHDUHZXCWTHDXBXBABXFDEXBMZFUIZUJZUKWTXEXDBULKZKUMNXOABXDDEXDMZF
      XOMZUNUOWTXJHIDDWTXFDJZXGDJZUQZUQZXIXBJZXIAUPKZOZXIXOKZXIPKZKZBUFKZNXJYAA
      URJZXFXBJZXGXBJZYBWTYIXTWTAUCJYIABEUSAUTQZRXRYJWTXSXMSZYADXBXGXNWTXRXSVAV
      BZXBAXHXFXGXLXHMZVCVDZYAYDYETJZYAYEXFXOKZXGXOKZVELZTYAXBXOABXHBVHKZXFXGYC
      XQEUUAMZXLYOYCMZWTBURJZXTBUTZRZYMXRXFYCOZWTXSABXFDYCEUUCFVFSZYAYRXFPKKZYH
      UUAXRUUIYHNWTXSXOBYHXFDXQYHMZFVGSZWTYHUUAJXTWTBVQKZUUAYHWTUUDUULUUAUEUUEB
      UULUUAUUBUULMZVIQWTUUDYHUULJUUEBUULYHUUMUUJVJQVKRVLYNXSXGYCOZWTXRABXGDYCE
      UUCFVFVMZVNZYAYRYSYAUUDYJUUGYRTJUUFYMUUHXBXOABXFYCXQEUUCXLVOVDYAUUDYKUUNY
      STJUUFYNUUOXBXOABXGYCXQEUUCXLVOVDVPVLYAUUDYBYDYQWFUUFYPXBXOABXIYCXQEUUCXL
      VRVSVTYAYGYTYFKZYHYAYEYTYFUUPWGYAUUQUUIYSXGPKKZBUGKZLZYHYAXBXOBXHUUSXFXGA
      YCEYOUUSMZXLXQUUCUUFYMUUHYNUUOWAYAUUTYHYHUUSLZYHYAUUIYHUURYHUUSUUKXSUURYH
      NWTXRXOBYHXGDXQUUJFVGVMWBWTUVBYHNZXTWTUUDYHBUDKZJUVCUUEUVDBYHUVDMZUUJWCUV
      DBUUSYHYHUVEUVAUUJWDWERWHWHWHXBXOABYHXIDYCEXLUUCXQFUUJWIWJWKWTCWPJZXAXCXE
      XKWLWFWTYIUVFYLACGWMQHIXBXHDCXDXBACGXLWNAXDCGXPWOAXHCGYOWQWRQWS $.
  $}

  ${
    $d x y B $.  $d x y D $.  $d x y N $.  $d x y R $.  $d x y Y $.
    $d x y .0. $.
    deg1mhm.d $e |- D = ( deg1 ` R ) $.
    deg1mhm.b $e |- B = ( Base ` P ) $.
    deg1mhm.p $e |- P = ( Poly1 ` R ) $.
    deg1mhm.z $e |- .0. = ( 0g ` P ) $.
    deg1mhm.y $e |- Y = ( ( mulGrp ` P ) |`s ( B \ { .0. } ) ) $.
    deg1mhm.n $e |- N = ( CCfld |`s NN0 ) $.
    $( Homomorphic property of the polynomial degree.  (Contributed by Stefan
       O'Rear, 12-Sep-2015.) $)
    deg1mhm $p |- ( R e. Domn ->
        ( D |` ( B \ { .0. } ) ) e. ( Y MndHom N ) ) $=
      ( vx wcel cn0 cfv wceq eqid syl vy cdomn cmnd wa cdif cres wf cv cmulr co
      csn caddc wral c0g cc0 w3a cmhm cmgp csubmnd ply1domn crg isdomn3 simprbi
      submmnd ccnfld nn0subm mp1i jca wfn wss cxr deg1xrf ffn ax-mp difss mp2an
      fnssres a1i fvres adantl domnring adantr eldifi deg1nn0cl syl3anc eqeltrd
      wne eldifsni ralrimiva ffnfv sylanbrc crlreg ad2antrl cco1 simpl ad2antll
      deg1ldgdomn deg1mul2 ringcl domnmuln0 syl122anc eldifsn oveqan12d 3eqtr4d
      ralrimivva cur ringidcl cnzr domnnzr nzrnz ringidval subm0 fveq2d mon1pid
      3syl cmn1 simprd 3eqtr3d 3jca cbs mgpbas ressbas2 cc nn0sscn cnfldbas cvv
      cplusg fvexi difexg mgpplusg ressplusg nn0ex cnfldadd cnfld0 ismhm ) DUBO
      ZFUCOZEUCOZUDAGUKZUEZPBYTUFZUGZNUHZUAUHZCUIQZUJZUUAQZUUCUUAQZUUDUUAQZULUJ
      ZRZUAYTUMNYTUMZFUNQZUUAQZUORZUPUUAFEUQUJOYPYQYRYPYTCURQZUSQOZYQYPCUBOZUUQ
      CDJUTZUURCVAOZUUQACUUPGIKUUPSZVBVCTZYTFUUPLVDTPVEUSQOZYRYPVFPEVEMVDVGVHYP
      UUBUULUUOYPUUAYTVIZUUHPOZNYTUMUUBUVDYPBAVIZYTAVJZUVDAVKBUGUVFABCDHJIVLAVK
      BVMVNAYSVOZAYTBVQVPVRYPUVENYTYPUUCYTOZUDZUUHUUCBQZPUVIUUHUVKRYPUUCYTBVSZV
      TUVJDVAOZUUCAOZUUCGWGZUVKPOYPUVMUVIDWAZWBUVIUVNYPUUCAYSWCZVTUVIUVOYPUUCAG
      WHZVTABCDUUCGHJKIWDWEWFWINYTPUUAWJWKYPUUKNUAYTYTYPUVIUUDYTOZUDZUDZUUFBQZU
      VKUUDBQZULUJZUUGUUJUWAABCDUUEDWLQZUUCUUDGHJUWESZIUUESZKYPUVMUVTUVPWBUVIUV
      NYPUVSUVQWMZUVIUVOYPUVSUVRWMZUWAYPUVNUVOUVKUUCWNQZQUWEOYPUVTWOUWHUWIUWJAB
      CDUWEUUCGHJKIUWFUWJSWQWEUVSUUDAOZYPUVIUUDAYSWCWPZUVSUUDGWGZYPUVIUUDAGWHWP
      ZWRUWAUUFYTOZUUGUWBRUWAUUFAOZUUFGWGZUWOUWAUUTUVNUWKUWPYPUUTUVTYPUURUUTUUS
      CWATZWBUWHUWLACUUEUUCUUDIUWGWSWEUWAUURUVNUVOUWKUWMUWQYPUURUVTUUSWBUWHUWIU
      WLUWNACUUEUUCUUDGIUWGKWTXAUUFAGXBWKUUFYTBVSTUVTUUJUWDRYPUVIUVSUUHUVKUUIUW
      CULUVLUUDYTBVSXCVTXDXEYPCXFQZUUAQZUWSBQZUUNUOYPUWSYTOZUWTUXARYPUWSAOZUWSG
      WGZUXBYPUUTUXCUWRACUWSIUWSSZXGTYPUURCXHOUXDUUSCXICUWSGUXEKXJXOUWSAGXBWKUW
      SYTBVSTYPUWSUUMUUAYPUUQUWSUUMRUVBYTFUUPUWSLCUWSUUPUVAUXEXKXLTXMYPDXHOZUXA
      UORZDXIUXFUWSDXPQZOUXGBCDUWSUXHJUXEUXHSHXNXQTXRXSNUAYTPUUEULFEUUAUOUUMUVG
      YTFXTQRUVHYTAFUUPLACUUPUVAIYAYBVNPYCVJPEXTQRYDPYCEVEMYEYBVNYTYFOZUUEFYGQR
      AYFOUXIACXTIYHAYSYFYIVNYTUUEUUPFYFLCUUEUUPUVAUWGYJYKVNPYFOULEYGQRYLPULVEE
      YFMYMYKVNUUMSUVCUOEUNQRVFPEVEUOMYNXLVNYOWK $.
  $}

  ${
    $d n r $.
    $( Functionality of the cyclotomic polynomial sequence.  (Contributed by
       Stefan O'Rear, 5-Sep-2015.) $)
    cytpfn $p |- CytP Fn NN $=
      ( vn vr cn ccnfld cpl1 cfv cmgp cc cc0 csn cdif cress co cod ccnv cv cima
      cv1 cascl cgsu csg cmpt ccytp ovex df-cytp fnmpti ) ACDEFZGFZBDGFHIJKLMNF
      OAPJQDRFBPUGSFFUGUAFMUBZTMUCUHUITUDABUEUF $.
  $}

  ${
    $d n r N $.  $d n A $.  $d n .- $.  $d n O $.  $d n Q $.  $d n X $.
    cytpval.t $e |- T = ( ( mulGrp ` CCfld ) |`s ( CC \ { 0 } ) ) $.
    cytpval.o $e |- O = ( od ` T ) $.
    cytpval.p $e |- P = ( Poly1 ` CCfld ) $.
    cytpval.x $e |- X = ( var1 ` CCfld ) $.
    cytpval.q $e |- Q = ( mulGrp ` P ) $.
    cytpval.m $e |- .- = ( -g ` P ) $.
    cytpval.a $e |- A = ( algSc ` P ) $.
    $( Substitutions for the Nth cyclotomic polynomial.  (Contributed by Stefan
       O'Rear, 5-Sep-2015.) $)
    cytpval $p |- ( N e. NN -> ( CytP ` N ) =
          ( Q gsum ( r e. ( `' O " { N } ) |-> ( X .- ( A ` r ) ) ) ) ) $=
      ( cfv cmgp co cgsu vn ccnfld cpl1 cc cc0 csn cdif cress cod ccnv cima cv1
      cv cascl csg cmpt cn ccytp wceq eqcomi fveq2i eqtr4i eqtri cnveqi imaeq1i
      sneq imaeq2d eqtr3id fveq1i oveq123i mpteq12dv oveq12d df-cytp ovex fvmpt
      a1i ) UAFUBUCQZRQZIUBRQUDUEUFUGUHSZUIQZUJZUAUMZUFZUKZUBULQZIUMZVQUNQZQZVQ
      UOQZSZUPZTSCIGUJZFUFZUKZHWFAQZESZUPZTSUQURWBFUSZVRCWKWQTVRCUSWRVRBRQCVQBR
      BVQLUTVANVBVPWRIWDWJWNWPWRWDWLWCUKWNWLWAWCGVTGDUIQVTKDVSUIJVAVCVDVEWRWCWM
      WLWBFVFVGVHWJWPUSWRWPWJHWOWEWHEWIMWFAWGABUNQWGPBVQUNLVAVCVIEBUOQWIOBVQUOL
      VAVCVJUTVPVKVLUAIVMCWQTVNVO $.
  $}

$(
  @{
    @d r M @.  @d r N @.
    cytpcl.m @e |- M = ( Monic1p ` CCfld ) @.
    @( The ` N ` -th cyclotomic polynomial is a monic polynomial with complex
       coefficients.  (Contributed by Stefan O'Rear, 12-Sep-2015.) @)
    cytpcl @p |- ( N e. NN -> ( CytP ` N ) e. M ) @=
      ( vr cn wcel cfv ccnfld cmgp cc cc0 csn cdif co eqid ax-mp a1i cn0 cndrng
      cvv ccytp cpl1 cress cod ccnv cima cv1 cv cascl csg cmpt cgsu cytpval cfn
      ccmn ccrg cncrng ply1crng crngmgp chash cphi cidom c1 cneg cdiv ccxp wceq
      c0g c2 cdomn cdr drngdomn isidom mpbir2an id proot1ex cui cnfldbas cnfld0
      drngui oveq2i proot1hash syl3anc phicl nnnn0 syl eqeltrd wb cnvexg imaexg
      fvex mp2b hashclb sylibr csubmnd cnzr drngnzr mon1psubm cdg1 cdm cnvimass
      wa unitgrpbas odf fdmi sseqtri difss sstri adantl mon1plin sylancr simpld
      sseli fmptd fisuppfi gsumsubmclOLD )
      BEFZBUAGHUBGZIGZDHIGZJKLZMZUCNZUDGZUEZB
      LZUFZHUGGZDUHZXRUIGZGXRUJGZNZUKZULNAYJXRXSYCYKBYDYHDYCOZYDOZXROZYHOZXSOZY
      KOZYJOZUMXQYGAYMXSUNXSVHGZUUAOXSUOFZXQXRUPFZUUBHUPFZUUCUQXRHYPURPXRXSYRUS
      PQXQYGUTGZRFZYGUNFZXQUUEBVAGZRXQHVBFZXQVCVDVIBVENVFNZYGFUUEUUHVGUUIXQUUIU
      UDHVJFZUQHVKFZUUKSHVLPHVMVNQXQVOYCBYDYNYOVPHYCBYDUUJYBHVQGXTUCJHKVRVSSVTZ
      WAYOWBWCXQUUHEFUUHRFBWDUUHWEWFWGYGTFZUUGUUFWHYDTFYETFUUNYCUDWKYDTWIYEYFTW
      JWLYGTWMPWNZAXSWOGFZXQHWPFZUUPUULUUQSHWQPZXRHXSAYPCYRWRPQXQDYGYLAYMXQYIYG
      FZXBZYLAFZYLHWSGZGVCVGZUUTUUQYIJFZUVAUVCXBUURUUSUVDXQYGJYIYGYBJYGYDWTYBYD
      YFXAYBRYDYCYDYBHYBYCUUMYNXCYOXDXEXFJYAXGXHXMXIYJUVBXRHYKJAYHYIYPYQCUVBOYS
      YTVRXJXKXLYMOXNZXQYGATUUALMYMUUOUVEXOXPWG @.
      @( [12-Sep-2015] @)
  @}

  @{
    cytpdeg.d @e |- D = ( deg1 ` CCfld ) @.
    @( The ` N ` -th cyclotomic polynomial has degree ` ( phi `` N ) ` .
       (Contributed by Stefan O'Rear, 12-Sep-2015.) @)
    cytdeg @p |- ( N e. NN -> ( D ` ( CytP ` N ) ) = ( phi ` N ) ) @= ? @.
  @}
$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Wedderburn's little theorem
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Hybrid categories proposal
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Miscellaneous topology
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d F x a b $.  $d A x a b $.  $d B x a b $.
    $( Express a function as a subset of the Cartesian product.  (Contributed
       by Stefan O'Rear, 25-Jan-2015.) $)
    fgraphopab $p |- ( F : A --> B -> F =
          { <. a , b >. | ( ( a e. A /\ b e. B ) /\ ( F ` a ) = b ) } ) $=
      ( wf cv cfv cmpt cxp cin wcel wa wceq copab wss fssxp dfss2 sylib anbi2i
      wfn ffn dffn5 ineq1d eqtr3d df-mpt df-xp ineq12i inopab ancom anass eqcom
      anandi 3bitr2i bitr3i opabbii 3eqtri eqtrdi ) ABCFZCDADGZCHZIZABJZKZUTALZ
      EGZBLZMZVAVFNZMZDEOZUSCVCKZCVDUSCVCPVLCNABCQCVCRSUSCVBVCUSCAUACVBNABCUBDA
      CUCSUDUEVDVEVFVANZMZDEOZVHDEOZKVNVHMZDEOVKVBVOVCVPDEAVAUFDEABUGUHVNVHDEUI
      VQVJDEVQVEVMVGMZMZVJVEVMVGUMVSVEVGVMMZMVHVMMVJVRVTVEVMVGUJTVEVGVMUKVMVIVH
      VFVAULTUNUOUPUQUR $.

    $( Express a function as a subset of the Cartesian product.  (Contributed
       by Stefan O'Rear, 25-Jan-2015.) $)
    fgraphxp $p |- ( F : A --> B -> F =
          { x e. ( A X. B ) | ( F ` ( 1st ` x ) ) = ( 2nd ` x ) } ) $=
      ( va vb wf cv wcel cfv wceq copab c1st c2nd cxp crab fgraphopab w3a vex
      wa cop op1std fveq2d op2ndd eqeq12d rabxp df-3an opabbii eqtri eqtr4di )
      BCDGDEHZBIZFHZCIZTUKDJZUMKZTZEFLZAHZMJZDJZUSNJZKZABCOPZBCDEFQVDULUNUPRZEF
      LURVCUPAEFBCUSUKUMUAKZVAUOVBUMVFUTUKDUKUMUSESZFSZUBUCUKUMUSVGVHUDUEUFVEUQ
      EFULUNUPUGUHUIUJ $.
  $}

  ${
    $d J a $.  $d K a $.  $d F a $.
    $( The graph of a continuous function into a Hausdorff space is closed.
       (Contributed by Stefan O'Rear, 25-Jan-2015.) $)
    hausgraph $p |- ( ( K e. Haus /\ F e. ( J Cn K ) ) ->
        F e. ( Clsd ` ( J tX K ) ) ) $=
      ( va wcel ccn co wa c1st cuni cres c2nd cfv wceq crab wfn wf ax-mp adantl
      ffn cha cxp ccom cin cdm ctx ccld f1stres fvco2 mpan fvres fveq2d eqeq12d
      eqtrd rabbidva eqid cnf fco sylancl ffnd f2ndres fndmin fgraphxp 3eqtr4rd
      cv syl simpl ctopon ctop cntop1 toptopon sylib haustop tx1cn syl2anc cnco
      sylancom tx2cn hauseqlcld eqeltrd ) CUAEZABCFGEZHZAAIBJZCJZUBZKZUCZLWFKZU
      DUEZBCUFGZUGMWCDVEZWHMZWLWIMZNZDWFOZWLIMZAMZWLLMZNZDWFOZWJAWCWOWTDWFWCWLW
      FEZHZWMWRWNWSXCWMWLWGMZAMZWRXBWMXENZWCWGWFPZXBXFWFWDWGQZXGWDWEUHZWFWDWGTR
      WFAWGWLUIUJSXBXEWRNWCXBXDWQAWLWFIUKULSUNXBWNWSNWCWLWFLUKSUMUOWCWHWFPWIWFP
      ZWJWPNWCWFWEWHWCWDWEAQZXHWFWEWHQWBXKWAABCWDWEWDUPZWEUPZUQSZXIWFWDWEAWGURU
      SUTWFWEWIQXJWDWEVAWFWEWITRDWFWHWIVBUSWCXKAXANXNDWDWEAVCVFVDWCWHWIWKCWAWBV
      GZWAWBWGWKBFGEZWHWKCFGZEWCBWDVHMEZCWEVHMEZXPWCBVIEZXRWBXTWAABCVJSBWDXLVKV
      LZWCCVIEZXSWCWAYBXOCVMVFCWEXMVKVLZBCWDWEVNVOWGAWKBCVPVQWCXRXSWIXQEYAYCBCW
      DWEVRVOVSVT $.
  $}

  $c TopSep TopLnd $.

  $( The class of separable topologies. $)
  ctopsep $a class TopSep $.

  $( The class of Lindel&ouml;f topologies. $)
  ctoplnd $a class TopLnd $.

  ${
    $d j x y z $.
    $( A topology is _separable_ iff it has a countable dense subset.
       (Contributed by Stefan O'Rear, 8-Jan-2015.) $)
    df-topsep $a |- TopSep = { j e. Top | E. x e. ~P U. j ( x ~<_ _om /\
        ( ( cls ` j ) ` x ) = U. j ) } $.

    $( A topology is _Lindel&ouml;f_ iff every open cover has a countable
       subcover.  (Contributed by Stefan O'Rear, 8-Jan-2015.) $)
    df-toplnd $a |- TopLnd = { x e. Top | A. y e. ~P x ( U. x = U. y ->
        E. z e. ~P x ( z ~<_ _om /\ U. x = U. z ) ) } $.
  $}

  $( Expand definitions $)
  $( RR is separable $)
  $( A set is dense iff it meets every open set $)
  $( A set is dense iff it meets every basis element $)
  $( Lindelof criterion for subspaces $)
  $( Lindelof for closed subspaces $)
  $( A countable union of Lindelof subspaces $)
  $( In a general space, open Lindelof <=> all families of open sets have
     countable subfamilies with the same union $)
  $( Both of the above are equivalent to hereditary Lindelof above $)
  $( Hereditary Lindelof => Lindelof $)
  $( 2nd countable => hered Lindelof; RR is h Lind $)
  $( 2nd countable => separable $)
  $( Expansions of first-countability $)
  $( Metric spaces are first-countable: use balls of (1/NN) or QQ+ radius $)
  $( Binary products preserve second-countability $)
  $( Binary products preserve first-countability $)

  $( The Sorgenfrey line basis is a basis $)
  $( A set is Sorgenfrey-dense iff it is RR-dense $)
  $( SorgenfreyLine is separable $)
  $( The Sorgenfrey line is a topology on RR $)
  $( The Sorgenfrey line is finer than the usual line $)
  $( A topology finer than a Hausdorff topology is Hausdorff; Sorgenfrey line
     is Hausdorff $)
  $( Hereditary Lindelof proof: there may be a simpler one $)
    $( Basis sets are Lindelof: close/open advancing argument like icccmp $)
    $( Open intervals are countable unions of half-open $)
    $( Open intervals are Lindelof in the SL $)
    $( A Lindelof open set is equal to the union of its maximal intervals $)
    $( A union of half-open intervals sharing a point is a half-open or open
       interval $)
    $( Each maximal interval is a half-open or open interval $)
    $( Each maximal interval is disjoint $)
    $( There are countably many disjoint intervals $)
    $( All open sets are Lindelof $)
  $( Sorgenfrey line is first-countable: [x,x+q) or [x,x+(1/n)) is a countable
     neighborhood base $)

  $( Natural open sets in the Sorgenfrey plane $)
  $( Antidiagonal is closed $)
  $( Antidiagonal is discrete $)
  $( Sorgenfrey plane is NOT Lindelof, despite h. Lindelof of the line $)
  $( This proves that the Sorgenfrey line is NOT 2c $)
    $( alternate direct proof: a point is "special" in an open set if the point
       is in the open set and the open set contains no interval around it.  The
       special points of a union is at most the special points of the elements.
       An element of the standard basis has at most one special point.  The
       special points of every open set are countable.  Given a countable
       collection of open sets, find a point which is not special for any
       element; [x,x+1) thus has a special point which is not in the union, and
       so cannot be a union of elements of the countable set. $)

  $( Define the general order topology and the lexicographic order $)
    $( does it make sense to first define poset infinity and intervals? $)
  $( Define ordinal spaces or at least their ordering $)
  $( Redefine CCfld with a topology and an order $)
  $( Define the closed long ray (CLR) $)
  $( A Lindelof subset of the CLR is not cofinal $)
  $( The CLR is not Lindelof $)
  $( A countable ordinal can be continuously order-embedded in QQ $)
    $( this is also the key step for Aronsjazn trees $)
    $( an ordinal is countable iff it can be embedded in RR $)
  $( A continuous embedding extends to a homomorphism of a long line initial
     segment which "fixes" 0 $)
  $( Initial segments of the CLR are homeomorph to [0,1) $)
  $( CLR is connected $)
  $( Intial segments of the OLR are homeomorph to (0,1), thus RR $)
  $( OLR is connected $)
  $( Every Lindelof subset of OLR is contained in a homeomorph of RR $)
  $( Define LL $)
  $( Every Lindelof subset of LL is contained in a homeomorph of RR $)
  $( LL contains CLR as a closed set and OLR as open $)
  $( LL is not Lindelof $)
  $( LL has a reversing homeomorphism $)
  $( A homeomorphism of interval-connected ordered spaces is monotone $)
  $( OLR has downward cofinal sequences but not upward cofinal $)
  $( All OLR homeomorphisms are monotone increasing $)

$( (End of Stefan O'Rear's mathbox.) $)
