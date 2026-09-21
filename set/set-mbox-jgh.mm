$[ set-main.mm $]
$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Mathbox for Jeff Hankins
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Miscellany
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    a1i14.1 $e |- ( ps -> ( ch -> ta ) ) $.
    $( Add two antecedents to a wff.  (Contributed by Jeff Hankins,
       4-Aug-2009.) $)
    a1i14 $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $=
      ( wi a1dd a1i ) BCDEGGGABCEDFHI $.
  $}

  ${
    a1i24.1 $e |- ( ph -> ( ch -> ta ) ) $.
    $( Add two antecedents to a wff.  Deduction associated with ~ a1i13 .
       (Contributed by Jeff Hankins, 5-Aug-2009.) $)
    a1i24 $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $=
      ( wi a1dd a1d ) ACDEGGBACEDFHI $.
  $}

  ${
    exp5d.1 $e |- ( ( ( ph /\ ps ) /\ ch ) -> ( ( th /\ ta ) -> et ) ) $.
    $( An exportation inference.  (Contributed by Jeff Hankins, 7-Jul-2009.) $)
    exp5d $p |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $=
      ( wi wa expd exp31 ) ABCDEFHHABICIDEFGJK $.
  $}

  ${
    exp5g.1 $e |- ( ( ph /\ ps ) -> ( ( ( ch /\ th ) /\ ta ) -> et ) ) $.
    $( An exportation inference.  (Contributed by Jeff Hankins, 7-Jul-2009.) $)
    exp5g $p |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $=
      ( wi wa exp4c ex ) ABCDEFHHHABICDEFGJK $.
  $}

  ${
    exp5k.1 $e |- ( ph -> ( ( ( ps /\ ( ch /\ th ) ) /\ ta ) -> et ) ) $.
    $( An exportation inference.  (Contributed by Jeff Hankins, 7-Jul-2009.) $)
    exp5k $p |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $=
      ( wi wa expd exp4d ) ABCDEFHABCDIIEFGJK $.
  $}

  ${
    exp56.1 $e |- ( ( ( ( ph /\ ps ) /\ ch ) /\ ( th /\ ta ) ) -> et ) $.
    $( An exportation inference.  (Contributed by Jeff Hankins, 7-Jul-2009.) $)
    exp56 $p |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $=
      ( wa ex exp5d ) ABCDEFABHCHDEHFGIJ $.
  $}

  ${
    exp58.1 $e |- ( ( ( ph /\ ps ) /\ ( ( ch /\ th ) /\ ta ) ) -> et ) $.
    $( An exportation inference.  (Contributed by Jeff Hankins, 7-Jul-2009.) $)
    exp58 $p |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $=
      ( wa ex exp5g ) ABCDEFABHCDHEHFGIJ $.
  $}

  ${
    exp510.1 $e |- ( ( ph /\ ( ( ( ps /\ ch ) /\ th ) /\ ta ) ) -> et ) $.
    $( An exportation inference.  (Contributed by Jeff Hankins, 7-Jul-2009.) $)
    exp510 $p |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $=
      ( wa ex exp5j ) ABCDEFABCHDHEHFGIJ $.
  $}

  ${
    exp511.1 $e |- ( ( ph /\ ( ( ps /\ ( ch /\ th ) ) /\ ta ) ) -> et ) $.
    $( An exportation inference.  (Contributed by Jeff Hankins, 7-Jul-2009.) $)
    exp511 $p |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $=
      ( wa ex exp5k ) ABCDEFABCDHHEHFGIJ $.
  $}

  ${
    exp512.1 $e |- ( ( ph /\ ( ( ps /\ ch ) /\ ( th /\ ta ) ) ) -> et ) $.
    $( An exportation inference.  (Contributed by Jeff Hankins, 7-Jul-2009.) $)
    exp512 $p |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $=
      ( wa ex exp5l ) ABCDEFABCHDEHHFGIJ $.
  $}

  ${
    3com12d.1 $e |- ( ph -> ( ps /\ ch /\ th ) ) $.
    $( Commutation in consequent.  Swap 1st and 2nd.  (Contributed by Jeff
       Hankins, 17-Nov-2009.) $)
    3com12d $p |- ( ph -> ( ch /\ ps /\ th ) ) $=
      ( w3a id 3com12 syl ) ABCDFCBDFZECBDJJGHI $.
  $}

  ${
    3imp5.1 $e |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $.
    $( A triple importation inference.  (Contributed by Jeff Hankins,
       8-Jul-2009.) $)
    imp5p $p |- ( ph -> ( ps -> ( ( ch /\ th /\ ta ) -> et ) ) ) $=
      ( w3a wi com52l 3imp com3l ) CDEHABFCDEABFIIABCDEFGJKL $.

    $( A triple importation inference.  (Contributed by Jeff Hankins,
       8-Jul-2009.) $)
    imp5q $p |- ( ( ph /\ ps ) -> ( ( ch /\ th /\ ta ) -> et ) ) $=
      ( wa wi imp 3impd ) ABHCDEFABCDEFIIIGJK $.
  $}

  ${
    subtr.1 $e |- F/_ x A $.
    subtr.2 $e |- F/_ x B $.
    ${
      subtr.3 $e |- F/_ x Y $.
      subtr.4 $e |- F/_ x Z $.
      subtr.5 $e |- ( x = A -> X = Y ) $.
      subtr.6 $e |- ( x = B -> X = Z ) $.
      $( Transitivity of implicit substitution.  (Contributed by Jeff Hankins,
         13-Sep-2009.)  (Proof shortened by Mario Carneiro, 11-Dec-2016.) $)
      subtr $p |- ( ( A e. C /\ B e. D ) -> ( A = B -> Y = Z ) ) $=
        ( wcel wceq wi cv nfeq nfim eqeq1 eqeq1d imbi12d vtoclgf adantr ) BDOBC
        PZGHPZQZCEOARZCPZFHPZQUHABDIUFUGAABCIJSAGHKLSTUIBPZUJUFUKUGUIBCUAULFGHM
        UBUCNUDUE $.
    $}

    ${
      subtr2.3 $e |- F/ x ps $.
      subtr2.4 $e |- F/ x ch $.
      subtr2.5 $e |- ( x = A -> ( ph <-> ps ) ) $.
      subtr2.6 $e |- ( x = B -> ( ph <-> ch ) ) $.
      $( Transitivity of implicit substitution into a wff.  (Contributed by
         Jeff Hankins, 19-Sep-2009.)  (Proof shortened by Mario Carneiro,
         11-Dec-2016.) $)
      subtr2 $p |- ( ( A e. C /\ B e. D ) -> ( A = B -> ( ps <-> ch ) ) ) $=
        ( wcel wceq wb wi cv nfeq nfbi nfim eqeq1 bibi1d imbi12d vtoclgf adantr
        ) EGOEFPZBCQZRZFHODSZFPZACQZRUJDEGIUHUIDDEFIJTBCDKLUAUBUKEPZULUHUMUIUKE
        FUCUNABCMUDUENUFUG $.
    $}
  $}

  ${
    $d a b c r s t .<_ $.
    $( A relation intersected with its converse is an equivalence relation if
       the relation is transitive.  (Contributed by Jeff Hankins, 6-Oct-2009.)
       (Revised by Mario Carneiro, 12-Aug-2015.) $)
    trer $p |- ( A. a A. b A. c ( ( a .<_ b /\ b .<_ c ) -> a .<_ c ) ->
      ( .<_ i^i `' .<_ ) Er dom ( .<_ i^i `' .<_ ) ) $=
      ( vr vs vt cv wbr wa wi wal brin vex brcnv weq breq1 imbi12d spvv breq2
      ccnv cin wrel cdm wer wss inss2 relcnv relss mp2 a1i eqidd anbi2i anbi12i
      wceq bitri anbi1d 2albidv anbi12d imbi1d albidv anbi2d pm3.3 adantrd impd
      4syl adantld jcad bitr2i imbitrdi biimtrid bicomi anbi12ci 3bitr4i biimpi
      com23 jctil alrimiv alrimivv dfer2 syl3anbrc ) BHZCHZAIZWCDHZAIZJZWBWEAIZ
      KZDLCLZBLZAAUAZUBZUCZWMUDZWOUOEHZFHZWMIZWQWPWMIZKZWRWQGHZWMIZJZWPXAWMIZKZ
      JZGLZFLELWOWMUEWNWKWMWLUFWLUCWNAWLUGAUHWMWLUIUJUKWKWOULWKXGEFWKXFGWKXEWTX
      CWPWQAIZWQWPAIZJZWQXAAIZXAWQAIZJZJZWKXDWRXJXBXMWRXHWPWQWLIZJZXJWPWQAWLMZX
      OXIXHWPWQAENZFNZOZUMUPXBXKWQXAWLIZJXMWQXAAWLMYAXLXKWQXAAXSGNZOUMUPUNWKXNW
      PXAAIZXAWPAIZJZXDWKXNYCYDWKWPWCAIZWFJZWPWEAIZKZDLZCLZXHWQWEAIZJZYHKZDLZXH
      XKJZYCKZXNYCKWJYKBEBEPZWIYICDYRWGYGWHYHYRWDYFWFWBWPWCAQUQWBWPWEAQRURSYJYO
      CFCFPZYIYNDYSYGYMYHYSYFXHWFYLWCWQWPATWCWQWEAQZUSUTVASYNYQDGDGPZYMYPYHYCUU
      AYLXKXHWEXAWQATVBWEXAWPATRSYQXJXMYCYQXHXMYCKXIYQXMXHYCYQXKXHYCKXLYQXHXKYC
      XHXKYCVCVPVDVPVDVEVFWKXAWCAIZWFJZXAWEAIZKZDLZCLZXLYLJZUUDKZDLZXLXIJZYDKZX
      NYDKWJUUGBGBGPZWIUUECDUUMWGUUCWHUUDUUMWDUUBWFWBXAWCAQUQWBXAWEAQRURSUUFUUJ
      CFYSUUEUUIDYSUUCUUHUUDYSUUBXLWFYLWCWQXAATYTUSUTVASUUIUULDEDEPZUUHUUKUUDYD
      UUNYLXIXLWEWPWQATVBWEWPXAATRSUULXJXMYDUULXIXMYDKXHUULXMXIYDUULXLXIYDKXKXL
      XIYDVCVGVPVGVEVFVHXDYCWPXAWLIZJYEWPXAAWLMUUOYDYCWPXAAXRYBOUMVIVJVKWRWSXPX
      IWQWPWLIZJWRWSXHUUPXOXIUUPXHWQWPAXSXROVLXTVMXQWQWPAWLMVNVOVQVRVSEFGWOWMVT
      WA $.
  $}

  $( An equivalent membership condition for closed intervals.  (Contributed by
     Jeff Hankins, 14-Jul-2009.) $)
  elicc3 $p |- ( ( A e. RR* /\ B e. RR* ) -> ( C e. ( A [,] B ) <-> ( C e. RR*
  /\ A <_ B /\ ( C = A \/ ( A < C /\ C < B ) \/ C = B ) ) ) ) $=
    ( cxr wcel wa cle wbr w3a wceq clt wi simp1 a1i xrleltne biimprd syl5ibrcom
    wn wne wo cicc co elicc1 xrletr exp5o com23 imp5q df-ne biimtrrid 3adant3r3
    adantlr eqcom necon3bbii biimtrid 3exp com12 imp32 3adantr2 adantll anim12d
    w3o ex df-or 3orass pm5.6 orcom imbi2i bitri 3bitr4ri imbitrdi 3jcad xrleid
    ad3antrrr breq2 xrltle adantr adantllr simpr 3jaod exp31 3impd breq1 ancoms
    adantrd adantld ad3antlr impbid bitrd ) ADEZBDEZFZCABUAUBECDEZACGHZCBGHZIZW
    LABGHZCAJZACKHZCBKHZFZCBJZVAZIZABCUCWKWOXCWKWOWLWPXBWOWLLWKWLWMWNMNWIWJWLWM
    WNWPWIWLWJWMWNWPLLWIWLWJWMWNWPACBUDUEUFUGWKWOWQRZXARZFWTLZXBWKWOXFWKWOFXDWR
    XEWSWIWOXDWRLZWJWIWLWMXGWNXDCASZWIWLWMIZWRCAUHXIWRXHACOPUIUJUKWJWOXEWSLZWIW
    JWLWNXJWMWJWLWNXJWLWJWNXJLWLWJWNXJXEBCSZWLWJWNIZWSXABCCBULUMXLWSXKCBOPUNUOU
    PUQURUSUTVBWQWTXATZTXDXMLZXBXFWQXMVCWQWTXAVDXFXDXAWTTZLXNXDXAWTVEXOXMXDXAWT
    VFVGVHVIVJVKWKXCWLWMWNXCWLLWKWLWPXBMNWKWLWPXBWMWKWLWPXBWMLWKWLFZWPFZWQWMWTX
    AXQWMWQAAGHZWIXRWJWLWPAVLVMCAAGVNQXQWRWMWSWIWLWPWRWMLZWJWIWLFXSWPACVOVPVQWD
    XQWMXAWPXPWPVRZCBAGVNQVSVTWAWKWLWPXBWNWKWLWPXBWNLXQWQWNWTXAXQWNWQWPXTCABGWB
    QXPWTWNLZWPWJWLYAWIWJWLFWSWNWRWLWJWSWNLCBVOWCWEUSVPXQWNXABBGHZWJYBWIWLWPBVL
    WFCBBGWBQVSVTWAVKWGWH $.

  ${
    $d k m n y ph $.  $d k m n x ps $.  $d x y $.
    finminlem.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( A useful lemma about finite sets.  If a property holds for a finite set,
       it holds for a minimal set.  (Contributed by Jeff Hankins,
       4-Dec-2009.) $)
    finminlem $p |- ( E. x e. Fin ph -> E. x ( ph /\ A. y ( ( y C_ x /\ ps ) ->
    x = y ) ) ) $=
      ( vn vm vk cfn wrex cv cen wbr wa wex com c0 wi wcel ex crab wne cin wceq
      wss weq nfe1 nfcv nfrabw nfne isfi 19.8a anim2i 3impb breq2 anbi1d exbidv
      wal w3a elrab sylibr ne0d 3exp rexlimiv sylbi rexlimi con0 cep wwe epweon
      ssrab2 omsson sstri wefrc mp3an12 nfin nfeq1 nfan simprr wpss wo sspss wn
      nfv rspe pssss ssfi sylan2 sylbir syl adantrr simprll simprlr simplrr vex
      breq1 anbi12d spcev syl2anc csdm adantr php3 cdom ssdomg endomtr ad2antrr
      cvv ax-mp ad2antlr ensym domentr expcom ad2antll syld domnsym con2i nsyli
      syl5 impr word wb nnord ad2antrl ordtri1 con2bid mpbird jca31 elin anbi1i
      bitri exp44 rexlimdv biimtrid com23 mpdd necon2bd imp31 pm2.21d equcomi
      a1i jaod expr impd alrimiv jca eximd impancom 3syl ) ACIJCKZFKZLMZANZCOZF
      PUAZQUBZUUNGKZUCZQUDZGUUNJZADKZUUIUEZBNCDUFZRZDURZNZCOZAUUOCICUUNQUUMCFPU
      ULCUGCPUHUIZCQUHUJUUIISZUUIUUPLMZGPJZAUUORZGUUIUKZUVIUVKGPUUPPSZUVIAUUOUV
      MUVIAUSZUUNUUPUVNUVMUVIANZCOZNZUUPUUNSZUVMUVIAUVQUVOUVPUVMUVOCULUMUNUUMUV
      PFUUPPFGUFZUULUVOCUVSUUKUVIAUUJUUPUUILUOUPUQUTZVAVBVCVDVEVFVGVHVIUUNVGUEU
      UOUUSVJUUNPVGUUMFPVKVLVMGVGUUNVNVOUURUVFGUUNUVRUVQUURUVFRUVTUVMUURUVPUVFU
      VMUURNZUVOUVECUVMUURCUVMCWDCUUQQCUUNUUPUVGCUUPUHVPVQVRUWAUVOUVEUWAUVONZAU
      VDUWAUVIAVSUWBUVCDUWBUVABUVBUWBBUVAUVBUWAUVOBUVAUVBRUVAUUTUUIVTZDCUFZWAUW
      AUVOBNZNZUVBUUTUUIWBUWFUWCUVBUWDUWFUWCUVBUVMUURUWEUWCWCZUVMUWEUURUWGUVMUW
      EUURUWGRUVMUWENZUWCUUQQUWHUWCUUTISZUUQQUBZUVMUVOUWCUWIRZBUVMUVIUWKAUVMUVI
      NZUVJUWKUVIGPWEZUVJUVHUWKUVLUVHUWCUWIUWCUVHUVAUWIUUTUUIWFUUIUUTWGWHTWIWJW
      KWKUWHUWIUWCUWJUWIUUTHKZLMZHPJUWHUWCUWJRZHUUTUKUWHUWOUWPHPUWHUWNPSZUWOUWC
      UWJUWHUWQUWONZUWCNZNZUUQUWNUWTUWQUUIUWNLMZANZCOZNZUWNUUPSZNZUWNUUQSZUWTUW
      QUXCUXEUWHUWQUWOUWCWLUWTUWOBUXCUWHUWQUWOUWCWMUVMUVOBUWSWNUXBUWOBNCUUTDWOU
      VBUXAUWOABUUIUUTUWNLWPEWQWRWSUWTUXEUUPUWNUEZWCZUWHUWRUWCUXIUWHUWRNZUWCUUT
      UUIWTMZUXIUXJUVHUWCUXKRUWHUVHUWRUVMUVOUVHBUVMUVIUVHAUWLUVJUVHUWMUVLVAWKWK
      XAUVHUWCUXKUUIUUTXBTWJUXJUXHUUIUUTXCMZUXKUXHUUPUWNXCMZUXJUXLUWNXGSUXHUXMR
      HWOUUPUWNXGXDXHUXJUXMUUIUWNXCMZUXLUWEUXMUXNRZUVMUWRUVIUXOABUVIUXMUXNUUIUU
      PUWNXETXFXIUWOUXNUXLRUWHUWQUXNUWOUXLUWOUXNUWNUUTLMUXLUUTUWNXJUUIUWNUUTXKW
      HXLXMXNXRUXLUXKUUIUUTXOXPXQXNXSUWTUUPXTZUWNXTZUXEUXIYAUVMUXPUWEUWSUUPYBXF
      UWRUXQUWHUWCUWQUXQUWOUWNYBXAYCUXPUXQNUXHUXEUUPUWNYDYEWSYFYGUXGUWNUUNSZUXE
      NUXFUWNUUNUUPYHUXRUXDUXEUUMUXCFUWNPFHUFZUULUXBCUXSUUKUXAAUUJUWNUUILUOUPUQ
      UTYIYJVAVBYKYLYMYNYOYPTYNYQYRUWDUVBRUWFDCYSYTUUAYMUUBYNUUCUUDUUETUUFUUGVE
      VDUUH $.
  $}

  ${
    $d z A $.  $d x y z S $.
    $( Any number greater than an infimum is greater than some element of the
       set.  (Contributed by Jeff Hankins, 29-Sep-2013.)  (Revised by AV,
       10-Oct-2021.) $)
    gtinf $p |- ( ( ( S C_ RR /\ S =/= (/) /\ E. x e. RR A. y e. S x <_ y ) /\
    ( A e. RR /\ inf ( S , RR , < ) < A ) ) -> E. z e. S z < A ) $=
      ( cr wss c0 wne cv cle wbr wral wrex w3a wcel clt cinf wa simprl wor ltso
      simprr a1i wn wi infm3 adantr infglb mp2and ) EFGEHIAJZBJZKLBEMAFNOZDFPZE
      FQRDQLZSZSZUNUOCJZDQLCENUMUNUOTUMUNUOUCUQABCFEDQFQUAUQUBUDUMULUKQLUEBEMUK
      ULQLURULQLCENUFBFMSAFNUPABCEUGUHUIUJ $.
  $}

  ${
    $d x y A $.
    $( A set is open in the standard topology of the reals precisely when every
       point can be enclosed in an open ball.  (Contributed by Jeff Hankins,
       23-Sep-2013.)  (Proof shortened by Mario Carneiro, 30-Jan-2014.) $)
    opnrebl $p |- ( A e. ( topGen ` ran (,) ) <-> ( A C_ RR /\ A. x e. A E. y
    e. RR+ ( ( x - y ) (,) ( x + y ) ) C_ A ) ) $=
      ( cioo crn ctg cfv wcel cr wss cv cabs cmin co crp wrex wral wa wb eqid
      ccom cxp cres cbl caddc cxmet rexmet cmopn tgioo elmopn2 ax-mp ssel2 wceq
      rpre bl2ioo sylan2 sseq1d rexbidva syl ralbidva pm5.32i bitri ) CDEFGZHZC
      IJZAKZBKZLMUAIIUBUCZUDGNZCJZBOPZACQZRZVEVFVGMNVFVGUENDNZCJZBOPZACQZRVHIUF
      GHVDVMSVHVHTZUGABCVHVCIVHVHUHGZVRVSTUIUJUKVEVLVQVEVKVPACVEVFCHRVFIHZVKVPS
      CIVFULVTVJVOBOVTVGOHZRVIVNCWAVTVGIHVIVNUMVGUNVFVGVHVRUOUPUQURUSUTVAVB $.
  $}

  ${
    $d x y z A $.
    $( A set is open in the standard topology of the reals precisely when every
       point can be enclosed in an arbitrarily small ball.  (Contributed by
       Jeff Hankins, 22-Sep-2013.)  (Proof shortened by Mario Carneiro,
       30-Jan-2014.) $)
    opnrebl2 $p |- ( A e. ( topGen ` ran (,) ) <-> ( A C_ RR /\ A. x e. A A. y
    e. RR+ E. z e. RR+ ( z <_ y /\ ( ( x - z ) (,) ( x + z ) ) C_ A ) ) ) $=
      ( cioo cfv wcel cr wss cv wbr cmin co wa crp wrex wral eqid wi c1 crn ctg
      cle caddc cabs ccom cxp cres cxmet rexmet cmopn tgioo mopnss mpan clt cbl
      w3a mopni3 mp3an1 sselda wceq bl2ioo sylan2 sseq1d anbi2d rexbidva biimpd
      ex rpre ltle syl2anr anim1d reximdva syl9 syl expimpd ralrimivv jca ssel2
      1rp simpr reximi ralimi biidd rspcv mpsyl imbitrrid ralimdva imdistani wb
      mpdd elmopn2 ax-mp sylibr impbii ) DEUAUBFZGZDHIZCJZBJZUCKZAJZWSLMXBWSUDM
      EMZDIZNZCOPZBOQZADQZNZWQWRXHUELUFHHUGUHZHUIFGZWQWRXJXJRZUJZDXJWPHXJXJUKFZ
      XLXNRULZUMUNZWQXFABDOWQXBDGZWTOGZXFWQXQNZXRWSWTUOKZXBWSXJUPFMZDIZNZCOPZXF
      XKWQXQXRYDSXMXKWQXQUQXRYDCDXJXBWTWPHXOURVHUSXSXBHGZXRYDXFSSWQDHXBXPUTYEYD
      XTXDNZCOPZXRXFYEYDYGYEYCYFCOYEWSOGZNZYBXDXTYIYAXCDYHYEWSHGZYAXCVAWSVIZXBW
      SXJXLVBVCVDZVEVFVGXRYFXECOXRYHNXTXAXDYHYJWTHGXTXASXRYKWTVIWSWTVJVKVLVMVNV
      OWKVPVQVRXIWRYBCOPZADQZNZWQWRXHYNWRXGYMADWRXQNYEXGYMSDHXBVSXGYMYEXDCOPZTO
      GXGYPBOQYPVTXFYPBOXEXDCOXAXDWAWBWCYPYPBTOWTTVAYPWDWEWFYEYBXDCOYLVFWGVOWHW
      IXKWQYOWJXMACDXJWPHXOWLWMWNWO $.
  $}

  ${
    $d k m n p q r t x y A $.  $d k m n p q r t x y B $.
    $( Lemma for ~ nn0prpw .  Use strong induction to show that every positive
       integer has unique prime power divisors.  (Contributed by Jeff Hankins,
       28-Sep-2013.) $)
    nn0prpwlem $p |- ( A e. NN -> A. k e. NN ( k < A -> E. p e. Prime E. n e.
    NN -. ( ( p ^ n ) || k <-> ( p ^ n ) || A ) ) ) $=
      ( clt wbr cexp co cdvds wb wn cn wrex cprime wi notbid c1 wcel wa breq1d
      vx vy vq vt vr vm cv wral wceq bibi2d 2rexbidv imbi12d ralbidv weq nnnlt1
      breq2 pm2.21d rgen c2 cuz cfv exprmfct w3a cdiv cc0 wne prmz adantr prmnn
      cz nnne0d adantl dvdsval2 syl3anc biimpd 3ad2antl2 adantrl simprr cr nnre
      nnz nngt0 jca divgt0 syl2anr adantrr elnnz sylanbrc expr eluzelz eluzelre
      syl 2z breq1 rspcv 3ad2ant1 cmul ad2antrr ad2antlr syl112anc mpbid bibi1d
      cle 3ad2ant2 3ad2ant3 biimpa ad2antrl ad4antlr syl2anc ad3antlr dvdsmulcr
      zexpcl cc divcan1d breq12d bitr3d ad4antr bibi12d impr oveq2 rspcev oveq1
      anbi2d rexbidv dvdsmultr2 simp-4r bitrdi coprmdvds mpan2d impbid divcan2d
      cgcd breq2d bitrd ex com23 pm2.61d embantd syld biimpar eluz1i zre ltletr
      2pos 0re 2re mp3an12 mpani imp sylbi a1d imbitrrdi sylbid ancoms eluzelcn
      ancld mullidd prmgt1 nnred ltmul1 eqbrtrrd ltdivmul mpbird ltdiv1 simprll
      1red caddc peano2nn nnnn0 ad2antll nncnd expp1d eqcomd nncn mpbiri simplr
      com12 gcdcomd simprl prmdvdsexpb equcom con3d coprm eqtrd exp32 rexlimdvv
      cn0 3exp2 3impia com24 imp32 3syld simpl2 1nn a1i exp1d 3adant1 mpid mtod
      biimpr nsyl rspc2ev expd ralrimiv cbvrex2vw cbvralvw sylib 3exp1 rexlimdv
      idd mpd indstr2 vtoclga ) BUGZUAUGZEFZDUGZCUGZGHZUXNIFZUXSUXOIFZJZKZCLMDN
      MZOZBLUHZUXNAEFZUXTUXSAIFZJZKZCLMDNMZOZBLUHUAALUXOAUIZUYEUYLBLUYMUXPUYGUY
      DUYKUXOAUXNEUPUYMUYCUYJDCNLUYMUYBUYIUYMUYAUYHUXTUXOAUXSIUPUJPUKULUMUYFUXN
      UBUGZEFZUXTUXSUYNIFZJZKZCLMDNMZOZBLUHZUXNQEFZUXTUXSQIFZJZKZCLMDNMZOZBLUHU
      AUBUXOQUIZUYEVUGBLVUHUXPVUBUYDVUFUXOQUXNEUPVUHUYCVUEDCNLVUHUYBVUDVUHUYAVU
      CUXTUXOQUXSIUPUJPUKULUMUAUBUNZUYEUYTBLVUIUXPUYOUYDUYSUXOUYNUXNEUPVUIUYCUY
      RDCNLVUIUYBUYQVUIUYAUYPUXTUXOUYNUXSIUPUJPUKULUMVUGBLUXNLRVUBVUFUXNUOUQURU
      XOUSUTVARZUCUGZUXOIFZUCNMUYNUXOEFZVUAOZUBLUHZUYFOZUXOUCVBVUJVULVUPUCNVUJV
      UKNRZVULVUOUYFVUJVUQVULVCZVUOSZUDUGZUXOEFZUEUGZUFUGZGHZVUTIFZVVDUXOIFZJZK
      ZUFLMZUENMZOZUDLUHUYFVUSVVKUDLVURVUOVUTLRZVVKVURVUOVVLSSZVUKVUTIFZVVKVVMV
      VNVUTVUKVDHZVJRZVVOLRZVVKVURVVLVVNVVPOZVUOVUQVUJVVLVVRVULVUQVVLSZVVNVVPVV
      SVUKVJRZVUKVEVFZVUTVJRZVVNVVPJVUQVVTVVLVUKVGZVHVUQVWAVVLVUQVUKVUKVIZVKZVH
      VVLVWBVUQVUTWAVLVUKVUTVMVNVOVPVQVURVVLVVPVVQOVUOVURVVLVVPVVQVURVVLVVPSSVV
      PVEVVOEFZVVQVURVVLVVPVRVURVVLVWFVVPVUQVUJVVLVWFVULVVLVUTVSRZVEVUTEFZSVUKV
      SRZVEVUKEFZSZVWFVUQVVLVWGVWHVUTVTZVUTWBWCVUQVUKLRZVWKVWDVWMVWIVWJVUKVTVUK
      WBZWCWLZVUTVUKWDWEVPWFVVOWGWHWIVQVURVUOVVLVVQVVKOVURVVQVVLVUOVVKVUJVUQVUL
      VVQVVLVUOVVKOZOOZVUJVUQSZVULUXOVUKVDHZLRZVWQVUQVUJVULVWTOVUQVUJSZVULVWSVJ
      RZVWTVXAVVTVWAUXOVJRZVULVXBJVUQVVTVUJVWCVHVUQVWAVUJVWEVHVUJVXCVUQUSUXOWJV
      LVUKUXOVMVNVXAVXBVXBVEVWSEFZSVWTVXAVXBVXDVXAVXDVXBVUJUXOVSRZVEUXOEFZSVWKV
      XDVUQVUJVXEVXFUSUXOWKZVUJVXCUSUXOXCFZSVXFUSUXOWMUUAVXCVXHVXFVXCVEUSEFZVXH
      VXFUUDVXCVXEVXIVXHSVXFOZUXOUUBVEVSRUSVSRVXEVXJUUEUUFVEUSUXOUUCUUGWLUUHUUI
      UUJZWCVWOUXOVUKWDWEUUKUUPVWSWGUULUUMUUNVWRVWTVVQVVLVWPVWRVWTVVQVVLVCZSZVU
      OVWSUXOEFZUXNVWSEFZUXTUXSVWSIFZJZKZCLMDNMZOZBLUHZOZVVKVXLVUOVYBOZVWRVWTVV
      QVYCVVLVUNVYBUBVWSLUYNVWSUIZVUMVXNVUAVYAUYNVWSUXOEWNVYDUYTVXTBLVYDUYOVXOU
      YSVXSUYNVWSUXNEUPVYDUYRVXRDCNLVYDUYQVXQVYDUYPVXPUXTUYNVWSUXSIUPUJPUKULUMU
      LWOWPVLVXMVXNVYAVVKVXMVXNUXOVUKUXOWQHZEFZVXMQUXOWQHZUXOVYEEVUJVYGUXOUIVUQ
      VXLVUJUXOUSUXOUUOZUUQWRVXMQVUKEFZVYGVYEEFZVUQVYIVUJVXLVUKUURWSVXMQVSRVWIV
      XEVXFVYIVYJJVXMUVFVUQVWIVUJVXLVUQVUKVWDUUSWSZVUJVXEVUQVXLVXGWRZVUJVXFVUQV
      XLVXKWRQVUKUXOUUTWTXAUVAVXMVXEVXEVWIVWJVXNVYFJVYLVYLVYKVUQVWJVUJVXLVUQVWM
      VWJVWDVWNWLWSZUXOUXOVUKUVBWTUVCVXMVYAVVOVWSEFZUXSVVOIFZVXPJZKZCLMDNMZOZVV
      KVXLVYAVYSOZVWRVVQVWTVYTVVLVXTVYSBVVOLUXNVVOUIZVXOVYNVXSVYRUXNVVOVWSEWNWU
      AVXRVYQDCNLWUAVXQVYPWUAUXTVYOVXPUXNVVOUXSIUPXBPUKULWOXDVLVXMVVAVYSVVJVXMV
      VAVYSVVJOVXMVVASZVYNVYRVVJVXMVVAVYNVXMVWGVXEVWIVWJVVAVYNJVXLVWGVWRVVLVWTV
      WGVVQVWLXEVLVYLVYKVYMVUTUXOVUKUVDWTXFWUBVYQVVJDCNLWUBUXQNRZUXRLRZSZVYQVVJ
      WUBWUEVYQSZSZWUCUXQVVCGHZVUTIFZWUHUXOIFZJZKZUFLMZVVJWUBWUCWUDVYQUVEWUGDUC
      UNZWUMWUNWUGWUMWUNWUGWUMOWUBWUEVUKUXRGHZVVOIFZWUOVWSIFZJZKZSZSZVUKVVCGHZV
      UTIFZWVBUXOIFZJZKZUFLMZOWVAUXRQUVGHZLRZVUKWVHGHZVUTIFZWVJUXOIFZJZKZWVGWUE
      WVIWUBWUSWUDWVIWUCUXRUVHVLXGWUBWUEWUSWVNWUBWUESZWUSWVNWVOWURWVMWVOWUPWVKW
      UQWVLWVOWUOVUKWQHZVVOVUKWQHZIFZWUPWVKWVOWUOVJRZVVPVVTVWAWVRWUPJWVOVVTUXRU
      WGRZWVSVUQVVTVUJVXLVVAWUEVWCXHZWUDWVTWUBWUCUXRUVIZUVJZVUKUXRXLXIZVXLVVPVW
      RVVAWUEVVQVWTVVPVVLVVOWAXDZXJWWAVUQVWAVUJVXLVVAWUEVWEXHZVUKWUOVVOXKWTWVOW
      VPWVJWVQVUTIWVOWVJWVPWVOVUKUXRVUQVUKXMRZVUJVXLVVAWUEVUQVUKVWDUVKZXHZWWCUV
      LUVMZWVOVUTVUKVXLVUTXMRZVWRVVAWUEVVLVWTWWKVVQVUTUVNXEZXJWWIWWFXNXOXPWVOWV
      PVWSVUKWQHZIFZWUQWVLWVOWVSVXBVVTVWAWWNWUQJWWDVXLVXBVWRVVAWUEVWTVVQVXBVVLV
      WSWAWPZXJWWAWWFVUKWUOVWSXKWTWVOWVPWVJWWMUXOIWWJWVOUXOVUKVUJUXOXMRZVUQVXLV
      VAWUEVYHXQWWIWWFXNXOXPXRPVOXSWVFWVNUFWVHLVVCWVHUIZWVEWVMWWQWVCWVKWVDWVLWW
      QWVBWVJVUTIVVCWVHVUKGXTZTWWQWVBWVJUXOIWWRTXRPYAXIWUNWUGWVAWUMWVGWUNWUFWUT
      WUBWUNVYQWUSWUEWUNVYPWURWUNVYOWUPVXPWUQWUNUXSWUOVVOIUXQVUKUXRGYBZTWUNUXSW
      UOVWSIWWSTXRPYCYCWUNWULWVFUFLWUNWUKWVEWUNWUIWVCWUJWVDWUNWUHWVBVUTIUXQVUKV
      VCGYBZTWUNWUHWVBUXOIWWTTXRPYDULUVOUVQWUBWUEVYQWUNKZWUMOWVOWXAVYQWUMWUBWUE
      WXAVYQWUMOWUBWUEWXASZSZVYQWUMWXCVYQSWUDUXSVUTIFZUYAJZKZWUMWXBWUDWUBVYQWUC
      WUDWXAUVPWSWXCVYQWXFWXCVYPWXEWXCVYOWXDVXPUYAWXCVYOUXSVUKVVOWQHZIFZWXDWXCV
      YOWXHWXCUXSVJRZVVTVVPVYOWXHOWXCUXQVJRZWVTWXIWUEWXJWUBWXAWUCWXJWUDUXQVGVHX
      GWUEWVTWUBWXAWUDWVTWUCWWBVLXGUXQUXRXLXIZVUQVVTVUJVXLVVAWXBVWCXHZVXLVVPVWR
      VVAWXBWWEXJZUXSVUKVVOYEVNWXCWXHUXSVUKYLHZQUIZVYOWXCWXNVUKUXSYLHZQWXCUXSVU
      KWXKWXLUVRWXCVUKUXSIFZKZWXPQUIZWUBWUEWXAWXRWVOWXQWUNWVOVUQWUCWUDWXQWUNOVU
      JVUQVXLVVAWUEYFWUBWUCWUDUVSWUBWUCWUDVRVUQWUCWUDVCZWXQWUNWXTWXQUCDUNWUNVUK
      UXQUXRUVTUCDUWAYGVOVNUWBXSWXCVUQWXIWXRWXSJVUJVUQVXLVVAWXBYFWXKVUKUXSUWCXI
      XAUWDZWXCWXIVVTVVPWXHWXOSVYOOWXKWXLWXMUXSVUKVVOYHVNYIYJWXCWXGVUTUXSIWXCVU
      TVUKVXLWWKVWRVVAWXBWWLXJVUQWWGVUJVXLVVAWXBWWHXHZVUQVWAVUJVXLVVAWXBVWEXHZY
      KYMYNWXCVXPUXSVUKVWSWQHZIFZUYAWXCVXPWYEWXCWXIVVTVXBVXPWYEOWXKWXLVXLVXBVWR
      VVAWXBWWOXJZUXSVUKVWSYEVNWXCWYEWXOVXPWYAWXCWXIVVTVXBWYEWXOSVXPOWXKWXLWYFU
      XSVUKVWSYHVNYIYJWXCWYDUXOUXSIWXCUXOVUKVUJWWPVUQVXLVVAWXBVYHXQWYBWYCYKYMYN
      XRPXFWULWXFUFUXRLUFCUNZWUKWXEWYGWUIWXDWUJUYAWYGWUHUXSVUTIVVCUXRUXQGXTZTWY
      GWUHUXSUXOIWYHTZXRPYAXIYOWIYPXSYQVVIWUMUEUXQNUEDUNZVVHWULUFLWYJVVGWUKWYJV
      VEWUIVVFWUJWYJVVDWUHVUTIVVBUXQVVCGYBZTWYJVVDWUHUXOIWYKTZXRPYDYAXIUWEUWFYR
      YOYPYSYRYSUWHYSUWIUWJUWKUWLVURVVLVVNKZVVKOVUOVURVVLSWYMVVAVVJVURVVLWYMVVA
      SZVVJVURVVLWYNSZSZVUQQLRZVUKQGHZVUTIFZWYRUXOIFZJZKZVVJVUJVUQVULWYOUWMWYQW
      YPUWNUWOWYPWYTWYSOZXUAWYPXUCWYSVURWYNWYSKZVVLVURWYMXUDVVAVUQVUJWYMXUDVULV
      UQXUDWYMVUQWYSVVNVUQWYRVUKVUTIVUQVUKWWHUWPZTPYTVPWFVQVURXUCWYSOWYOVURXUCW
      YTWYSVUQVULWYTVUJVUQWYTVULVUQWYRVUKUXOIXUETYTUWQVURXUCUXJUWRVHUWSWYSWYTUW
      TUXAVVHXUBWVFUEUFVUKQNLUEUCUNZVVGWVEXUFVVEWVCVVFWVDXUFVVDWVBVUTIVVBVUKVVC
      GYBZTXUFVVDWVBUXOIXUGTXRPVVCQUIZWVEXUAXUHWVCWYSWVDWYTXUHWVBWYRVUTIVVCQVUK
      GXTZTXUHWVBWYRUXOIXUITXRPUXBVNWIUXCVQYQWIUXDVVKUYEUDBLUDBUNZVVAUXPVVJUYDV
      UTUXNUXOEWNXUJVVJVVDUXNIFZVVFJZKZUFLMUENMUYDXUJVVHXUMUEUFNLXUJVVGXULXUJVV
      EXUKVVFVUTUXNVVDIUPXBPUKXUMUYCWUHUXNIFZWUJJZKUEUFDCNLWYJXULXUOWYJXUKXUNVV
      FWUJWYJVVDWUHUXNIWYKTWYLXRPWYGXUOUYBWYGXUNUXTWUJUYAWYGWUHUXSUXNIWYHTWYIXR
      PUXEYGULUXFUXGUXHUXIUXKUXLUXM $.

    $( Two nonnegative integers are the same if and only if they are divisible
       by the same prime powers.  (Contributed by Jeff Hankins,
       29-Sep-2013.) $)
    nn0prpw $p |- ( ( A e. NN0 /\ B e. NN0 ) -> ( A = B <-> A. p e. Prime A. n
    e. NN ( ( p ^ n ) || A <-> ( p ^ n ) || B ) ) ) $=
      ( vk wcel wa wceq cdvds wbr wb cn wral cprime cc0 wi wn wrex clt c1 cv co
      cn0 cexp breq2 a1d ralrimivv wo elnn0 wne lttri2 syl2an ancoms nn0prpwlem
      cr nnre breq1 bibi1d notbid 2rexbidv imbi12d rspcv mpan9 bicom impel jaod
      bitrdi sylbid df-ne rexnal2 3imtr3g con4d prmunb w3a 1nn prmz 1nn0 zexpcl
      ex cz sylancl dvds0 syl 3ad2ant2 cle dvdsle sylan prmnn lenlt nncnd exp1d
      reexpcl adantr breq2d bitrd sylibd con2d 3impia jcnd biimpr oveq2 bibi12d
      nsyl breq1d rspcev sylancr 3expia reximdva mpd sylib pm2.21d bibi2d eqeq2
      2ralbidv imbitrrid jaoi sylbi com12 orcom df-or 3bitri biimp imim2i eqcom
      imbitrdi eqeq1 imp sylanb impbid2 ) AUCFZBUCFZGABHZDUAZCUAZUDUBZAIJZYOBIJ
      ZKZCLMDNMZYLYRDCNLYLYRYMNFZYNLFGABYOIUEUFUGYJALFZAOHZUHZYKYSYLPZAUIUUCYKU
      UDUUAYKUUDPUUBYKUUAUUDYKBLFZBOHZUHZUUAUUDPZBUIZUUEUUHUUFUUEUUAUUDUUEUUAGZ
      YLYSUUJABUJZYRQZCLRDNRZYLQYSQUUJUUKABSJZBASJZUHZUUMUUAUUEUUKUUPKZUUAAUOFZ
      BUOFZUUQUUEAUPZBUPZABUKULUMUUJUUNUUMUUOUUEEUAZBSJZYOUVBIJZYQKZQZCLRDNRZPZ
      ELMUUAUUNUUMPZBECDUNUVHUVIEALUVBAHZUVCUUNUVGUUMUVBABSUQUVJUVFUULDCNLUVJUV
      EYRUVJUVDYPYQUVBAYOIUEURUSUTVAVBVCUUEUVBASJZUVDYPKZQZCLRDNRZPZELMUUOUUMPZ
      UUAUVOUVPEBLUVBBHZUVKUUOUVNUUMUVBBASUQUVQUVMUULDCNLUVQUVLYRUVQUVLYQYPKYRU
      VQUVDYQYPUVBBYOIUEURYQYPVDVGUSUTVAVBAECDUNVEVFVHABVIYRDCNLVJVKVLVSUUAUUDU
      UFYPYOOIJZKZCLMDNMZUUBPUUAUVTUUBUUAUVSQZCLRZDNRZUVTQUUAAYMSJZDNRUWCADVMUU
      AUWDUWBDNUUAYTUWDUWBUUAYTUWDVNZTLFZYMTUDUBZAIJZUWGOIJZKZQZUWBVOUWEUWIUWHP
      UWJUWEUWIUWHYTUUAUWIUWDYTUWGVTFZUWIYTYMVTFTUCFZUWLYMVPVQYMTVRWAZUWGWBWCZW
      DUUAYTUWDUWHQUUAYTGUWHUWDYTUUAUWHUWDQZPYTUUAGZUWHUWGAWEJZUWPYTUWLUUAUWHUW
      RPUWNUWGAWFWGUWQUWRAUWGSJZQZUWPYTUWGUOFZUURUWRUWTKUUAYTYMUOFZUWMUXAYTYMLF
      UXBYMWHZYMUPWCVQYMTWLWAZUUTUWGAWIULUWQUWSUWDUWQUWGYMASYTUWGYMHZUUAYTYMYTY
      MUXCWJWKZWMWNUSWOWPUMWQWRWSUWHUWIWTXCUWAUWKCTLYNTHZUVSUWJUXGYPUWHUVRUWIUX
      GYOUWGAIYNTYMUDXAZXDUXGYOUWGOIUXHXDZXBUSXEXFXGXHXIUVSDCNLVJXJXKUUFYSUVTYL
      UUBUUFYRUVSDCNLUUFYQUVRYPBOYOIUEXLXNBOAXMVAXOXPXQXRYKUUDUUBUVRYQKZCLMDNMZ
      OBHZPYKUXKUUFUXLYKUUFUXKYKUUFQZUUEPZUXMUXKQZPYKUUGUUFUUEUHUXNUUIUUEUUFXSU
      UFUUEXTYAUUEUXOUXMUUEUXJQZCLRZDNRZUXOUUEBYMSJZDNRUXRBDVMUUEUXSUXQDNUUEYTU
      XSUXQUUEYTUXSVNZUWFUWIUWGBIJZKZQZUXQVOUXTUWIUYAPUYBUXTUWIUYAYTUUEUWIUXSUW
      OWDUUEYTUXSUYAQUUEYTGUYAUXSYTUUEUYAUXSQZPYTUUEGZUYAUWGBWEJZUYDYTUWLUUEUYA
      UYFPUWNUWGBWFWGUYEUYFBUWGSJZQZUYDYTUXAUUSUYFUYHKUUEUXDUVAUWGBWIULUYEUYGUX
      SUYEUWGYMBSYTUXEUUEUXFWMWNUSWOWPUMWQWRWSUWIUYAYBXCUXPUYCCTLUXGUXJUYBUXGUV
      RUWIYQUYAUXIUXGYOUWGBIUXHXDXBUSXEXFXGXHXIUXJDCNLVJXJYCXQVLBOYDYEUUBYSUXKY
      LUXLUUBYRUXJDCNLUUBYPUVRYQAOYOIUEURXNAOBYFVAXOXPYGYHYI $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Basic topological facts
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    topbnd.1 $e |- X = U. J $.
    $( Two equivalent expressions for the boundary of a topology.  (Contributed
       by Jeff Hankins, 23-Sep-2009.) $)
    topbnd $p |- ( ( J e. Top /\ A C_ X ) -> ( ( ( cls ` J ) ` A ) i^i ( ( cls
    ` J ) ` ( X \ A ) ) ) = ( ( ( cls ` J ) ` A ) \ ( ( int ` J ) ` A ) ) ) $=
      ( ctop wcel wss wa ccl cfv cdif cin cnt clsdif ineq2d indif2 eqtrdi dfss2
      wceq clsss3 sylib difeq1d eqtrd ) BEFACGHZABIJZJZCAKUEJZLZUFCLZABMJJZKZUF
      UJKUDUHUFCUJKZLUKUDUGULUFABCDNOUFCUJPQUDUIUFUJUDUFCGUIUFSABCDTUFCRUAUBUC
      $.
  $}

  ${
    opnbnd.1 $e |- X = U. J $.
    $( A set is open iff it is disjoint from its boundary.  (Contributed by
       Jeff Hankins, 23-Sep-2009.) $)
    opnbnd $p |- ( ( J e. Top /\ A C_ X ) -> ( A e. J <-> ( A i^i ( ( ( cls ` J
    ) ` A ) i^i ( ( cls ` J ) ` ( X \ A ) ) ) ) = (/) ) ) $=
      ( ctop wcel wss wa cnt cfv wceq ccl cdif cin disjdif a1i eqeq1d syl5ibcom
      c0 ineq1 ntrss2 adantr inssdif0 sscls dfss2 sylib eqcomd eqimss syl sylan
      sstr sylan2br eqssd ex impbid isopn3 topbnd ineq2d 3bitr4d ) BEFACGHZABIJ
      JZAKZAABLJZJZVAMZNZSKZABFAVDCAMVCJNZNZSKUTVBVGUTVAVENZSKZVBVGVKUTVAVDOPVB
      VJVFSVAAVETQRUTVGVBUTVGHVAAUTVAAGVGABCDUAUBVGUTAVDNZVAGZAVAGZAVDVAUCUTAVL
      GZVMVNUTAVLKVOUTVLAUTAVDGVLAKABCDUDAVDUEUFUGAVLUHUIAVLVAUKUJULUMUNUOABCDU
      PUTVIVFSUTVHVEAABCDUQURQUS $.

    $( A set is closed iff it contains its boundary.  (Contributed by Jeff
       Hankins, 1-Oct-2009.) $)
    cldbnd $p |- ( ( J e. Top /\ A C_ X ) -> ( A e. ( Clsd ` J ) <-> ( ( ( cls
    ` J ) ` A ) i^i ( ( cls ` J ) ` ( X \ A ) ) ) C_ A ) ) $=
      ( ctop wcel wss wa ccld cfv cdif wceq c0 adantl ex sylbi ineq2d wb adantr
      cin ccl iscld3 eqimss biimtrdi ssinss1 sslin disjdifr sseq0 sylancl incom
      syl6 dfss4 fveq2 eqcomd eqtrid eqeq1d difss opnbnd mpan2 bitr4d wi opncld
      eleq1 sylibd sylbid syld impbid ) BEFZACGZHZABIJZFZABUAJZJZCAKZVMJZTZAGZV
      JVLVNAGZVRVJVLVNALVSABCDUBVNAUCUDVNVPAUEUKVJVRVOVQTZMLZVLVJVRWAVJVRHVTVOA
      TZGZWBMLWAVRWCVJVQAVOUFNACUGVTWBUHUIOVJWAVOBFZVLVJWAVOVPCVOKZVMJZTZTZMLZW
      DVJVTWHMVJVQWGVOVJVQVPVNTWGVNVPUJVJVNWFVPVIVNWFLZVHVIWEALZWJACULZWKWFVNWE
      AVMUMUNPNQUOQUPVHWDWIRZVIVHVOCGWMCAUQVOBCDURUSSUTVJWDWEVKFZVLVHWDWNVAVIVH
      WDWNVOBCDVBOSVIWNVLRZVHVIWKWOWLWEAVKVCPNVDVEVFVG $.
  $}

  ${
    $d o J $.  $d o O $.  $d o X $.
    ntruni.1 $e |- X = U. J $.
    $( A union of interiors is a subset of the interior of the union.  The
       reverse inclusion may not hold.  (Contributed by Jeff Hankins,
       31-Aug-2009.) $)
    ntruni $p |- ( ( J e. Top /\ O C_ ~P X ) -> U_ o e. O ( ( int ` J ) ` o
    ) C_ ( ( int ` J ) ` U. O ) ) $=
      ( ctop wcel cpw wss wa cv cnt cfv cuni wral ciun elssuni wi sspwuni ntrss
      3expia sylan2b syl5 ralrimiv iunss sylibr ) BFGZCDHIZJZAKZBLMZMZCNZUKMZIZ
      ACOACULPUNIUIUOACUJCGUJUMIZUIUOUJCQUHUGUMDIZUPUORCDSUGUQUPUOUMUJBDETUAUBU
      CUDACULUNUEUF $.
  $}

  ${
    clsun.1 $e |- X = U. J $.
    $( A pairwise union of closures is the closure of the union.  (Contributed
       by Jeff Hankins, 31-Aug-2009.) $)
    clsun $p |- ( ( J e. Top /\ A C_ X /\ B C_ X ) -> ( ( cls ` J ) ` ( A u. B
    ) ) = ( ( ( cls ` J ) ` A ) u. ( ( cls ` J ) ` B ) ) ) $=
      ( wcel wss cun cfv cdif difundi wceq difss wa unss ntrdif syl2anc 3adant3
      cin 3adant2 w3a ccl cnt fveq2i ntrin mp3an23 3ad2ant1 eqtrid simp1 biimpi
      ctop 3adant1 ineq12d eqtr4di 3eqtr3d difeq2d clscld cldss syl dfss4 sylib
      ccld clsss3 jca bitri ) CUKFZADGZBDGZUAZDDABHZCUBIZIZJZJZDDAVKIZBVKIZHZJZ
      JZVLVQVIVMVRDVIDVJJZCUCIZIZDAJZWAIZDBJZWAIZSZVMVRVIWBWCWESZWAIZWGVTWHWADA
      BKUDVFVGWIWGLZVHVFWCDGWEDGWJDAMDBMWCWECDEUEUFUGUHVIVFVJDGZWBVMLVFVGVHUIZV
      GVHWKVFVGVHNWKABDOUJULZVJCDEPQVIWGDVOJZDVPJZSVRVIWDWNWFWOVFVGWDWNLVHACDEP
      RVFVHWFWOLVGBCDEPTUMDVOVPKUNUOUPVIVLDGZVNVLLVIVLCVBIFZWPVIVFWKWQWLWMVJCDE
      UQQVLCDEURUSVLDUTVAVIVODGZVPDGZNZVSVQLZVIWRWSVFVGWRVHACDEVCRVFVHWSVGBCDEV
      CTVDWTVQDGXAVOVPDOVQDUTVEVAUO $.
  $}

  ${
    $d c C $.  $d c J $.  $d c X $.
    clsint2.1 $e |- X = U. J $.
    $( The closure of an intersection is a subset of the intersection of the
       closures.  (Contributed by Jeff Hankins, 31-Aug-2009.) $)
    clsint2 $p |- ( ( J e. Top /\ C C_ ~P X ) -> ( ( cls ` J ) ` |^| C ) C_
    |^|_ c e. C ( ( cls ` J ) ` c ) ) $=
      ( ctop wcel cpw wss wa cint ccl cfv cv wral ciin cuni wi sspwuni elssuni
      sstr2 syl adantl intss1 clsss syl3an3 3com23 3expia syld impancom sylan2b
      ralrimiv ssiin sylibr ) BFGZACHIZJZAKZBLMZMZDNZUSMZIZDAOUTDAVBPIUQVCDAUPU
      OAQZCIZVAAGZVCRACSUOVFVEVCUOVFJVEVACIZVCVFVEVGRZUOVFVAVDIVHVAATVAVDCUAUBU
      CUOVFVGVCUOVGVFVCVFUOVGURVAIVCVAAUDVAURBCEUEUFUGUHUIUJUKULDAVBUTUMUN $.
  $}

  ${
    $d c o A $.  $d c o J $.  $d c o X $.
    opnregcld.1 $e |- X = U. J $.
    $( A set is regularly closed iff it is the closure of some open set.
       (Contributed by Jeff Hankins, 27-Sep-2009.) $)
    opnregcld $p |- ( ( J e. Top /\ A C_ X ) -> ( ( ( cls ` J ) ` ( ( int ` J )
    ` A ) ) = A <-> E. o e. J A = ( ( cls ` J ) ` o ) ) ) $=
      ( ctop wcel wss wa cnt cfv wceq cv wrex ntropn eqcom syldan clsss syl3anc
      ccl biimpi rspceeqv syl2an ex eltopss clsss3 ntrss2 clsidm sseqtrd ntrss3
      fveq2 simpl simpr sscls ssntr syl22anc eqssd adantlr 2fveq3 id syl5ibrcom
      eqeq12d rexlimdva impbid ) CFGZADHZIZACJKZKZCTKZKZALZABMZVJKZLZBCNZVGVLVP
      VGVICGAVKLZVPVLACDEOVLVQVKAPUABVICVNVKAVMVIVJUKUBUCUDVGVOVLBCVGVMCGZIVLVO
      VNVHKZVJKZVNLZVEVRWAVFVEVRIZVTVNWBVTVNVJKZVNWBVEVNDHZVSVNHZVTWCHVEVRULZVE
      VRVMDHZWDVMCDEUEZVMCDEUFQZVEVRWDWEWIVNCDEUGQVNVSCDERSVEVRWGWCVNLWHVMCDEUH
      QUIWBVEVSDHZVMVSHZVNVTHWFVEVRWDWJWIVNCDEUJQWBVEWDVRVMVNHZWKWFWIVEVRUMVEVR
      WGWLWHVMCDEUNQVNCVMDEUOUPVSVMCDERSUQURVOVKVTAVNAVNVJVHUSVOUTVBVAVCVD $.

    $( A set if regularly open iff it is the interior of some closed set.
       (Contributed by Jeff Hankins, 27-Sep-2009.) $)
    cldregopn $p |- ( ( J e. Top /\ A C_ X ) -> ( ( ( int ` J ) ` ( ( cls ` J )
    ` A ) ) = A <-> E. c e. ( Clsd ` J ) A = ( ( int ` J ) ` c ) ) ) $=
      ( ctop wcel wss wa ccl cfv wceq cv ccld wrex clscld syl2anc ntrss syl3anc
      cnt eqcom biimpi fveq2 rspceeqv syl2an cldrcl ntrss2 clsss2 ntridm ntrss3
      ex cldss mpdan clsss3 sscls eqsstrrd eqssd adantl id syl5ibrcom rexlimdva
      2fveq3 eqeq12d impbid ) BFGZACHIZABJKZKZBTKZKZALZADMZVIKZLZDBNKZOZVFVKVPV
      FVHVOGAVJLZVPVKABCEPVKVQVJAUAUBDVHVOVMVJAVLVHVIUCUDUEUKVFVNVKDVOVFVLVOGZI
      VKVNVMVGKZVIKZVMLZVRWAVFVRVTVMVRVEVLCHZVSVLHZVTVMHVLBUFZVLBCEULZVRVMVLHZW
      CVRVEWBWFWDWEVLBCEUGQVLVMBCEUHUMVLVSBCERSVRVMVMVIKZVTVRVEWBWGVMLWDWEVLBCE
      UIQVRVEVSCHZVMVSHZWGVTHWDVRVEVMCHZWHWDVRVEWBWJWDWEVLBCEUJQZVMBCEUNQVRVEWJ
      WIWDWKVMBCEUOQVSVMBCERSUPUQURVNVJVTAVMAVMVIVGVBVNUSVCUTVAVD $.
  $}

  $( Two neighborhoods intersect to form a neighborhood of the intersection.
     (Contributed by Jeff Hankins, 31-Aug-2009.) $)
  neiin $p |- ( ( J e. Top /\ M e. ( ( nei ` J ) ` A ) /\ N e. ( ( nei ` J ) `
  B ) ) -> ( M i^i N ) e. ( ( nei ` J ) ` ( A i^i B ) ) ) $=
    ( cfv cin wss wa simpr wb simpl neiss2 neii1 neiint syl3anc ssinss1 3adant3
    wcel syl ctop cnei w3a cnt cuni eqid mpbid inss2 3adant2 sstrid ssind simp1
    wceq ntrin sseqtrrd mpbird ) CUASZDACUBFZFSZEBURFSZUCZDEGZABGZURFSZVCVBCUDF
    ZFZHZVAVCDVEFZEVEFZGZVFVAVCVHVIUQUSVCVHHZUTUQUSIZAVHHZVKVLUSVMUQUSJVLUQACUE
    ZHZDVNHZUSVMKUQUSLZACDVNVNUFZMZACDVNVRNZACDVNVROPUGABVHQTRVAVCBVIABUHUQUTBV
    IHZUSUQUTIZUTWAUQUTJWBUQBVNHEVNHZUTWAKUQUTLBCEVNVRMBCEVNVRNZBCEVNVROPUGUIUJ
    UKVAUQVPWCVFVJUMUQUSUTULUQUSVPUTVTRUQUTWCUSWDUIDECVNVRUNPUOUQUSVDVGKZUTVLUQ
    VCVNHZVBVNHZWEVQVLVOWFVSABVNQTVLVPWGVTDEVNQTVCCVBVNVROPRUP $.

  $( Homeomorphisms preserve closedness.  (Contributed by Jeff Hankins,
     3-Jul-2009.)  (Revised by Mario Carneiro, 3-Jun-2014.) $)
  hmeoclda $p |- ( ( ( J e. Top /\ K e. Top /\ F e. ( J Homeo K ) ) /\ S e. (
  Clsd ` J ) ) -> ( F " S ) e. ( Clsd ` K ) ) $=
    ( ctop wcel chmeo co w3a ccnv ccn ccld cima hmeocnvcn 3ad2ant3 wa imacnvcnv
    cfv cnclima eqeltrrid sylan ) CEFZDEFZBCDGHFZIBJZDCKHFZACLRFZBAMZDLRZFUDUBU
    FUCBCDNOUFUGPUHUEJAMUIBAQAUEDCSTUA $.

  $( Homeomorphisms preserve closedness.  (Contributed by Jeff Hankins,
     3-Jul-2009.) $)
  hmeocldb $p |- ( ( ( J e. Top /\ K e. Top /\ F e. ( J Homeo K ) ) /\ S e. (
  Clsd ` K ) ) -> ( `' F " S ) e. ( Clsd ` J ) ) $=
    ( ctop wcel chmeo w3a ccn ccld cfv ccnv cima hmeocn 3ad2ant3 cnclima sylan
    co ) CEFZDEFZBCDGRFZHBCDIRFZADJKFBLAMCJKFUASUBTBCDNOABCDPQ $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Topology of the real numbers
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x y A $.  $d x y B $.  $d x y D $.  $d x y F $.  $d x y U $.
    $( An alternate proof of the Intermediate Value Theorem ~ ivth using
       topology.  (Contributed by Jeff Hankins, 17-Aug-2009.)  (Revised by
       Mario Carneiro, 15-Dec-2013.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    ivthALT $p |- ( ( ( A e. RR /\ B e. RR /\ U e. RR ) /\ A < B /\ ( ( A [,] B
    ) C_ D /\ D C_ CC /\ ( F e. ( D -cn-> CC ) /\ ( F " ( A [,] B ) ) C_ RR /\
    U e. ( ( F ` A ) (,) ( F ` B ) ) ) ) ) -> E. x e. ( A (,) B ) ( F ` x ) = U
    ) $=
      ( cr wcel w3a wbr co wss cc cfv wceq syl 3ad2ant3 crest ccn wa cicc ccncf
      vy clt cima cioo cv wrex wfun wf simp31 cncff ffun wral crn ctg cuni cres
      cconn iccconn 3adant3 3ad2ant1 simpr1 anim2i 3impb adantl sseq2d biimparc
      wfo cdm fdm fores ctop retop simp332 uniretop restuni sylancr foeq3 mpbid
      jca wb ccnfld ctopn simp331 ssid eqid cnfldtop cnfldtopon toponunii ax-mp
      restid eqcomi cncfcn mpan2 3ad2ant2 eleqtrd ctopon simp32 toponuni cnrest
      resttopon sseqtrd syl2anc cvv cnex sylancl restabs syl3anc iccssre rerest
      ssexg eqtrd oveq1d df-ima eqimss2i ax-resscn sstrdi cnrest2 oveq2d cnconn
      a1i reconn wi cxr rexrd funfvima2 sseq1d mpd sseldd adantr eqnetrd neneqd
      sylc wne fveq2 nsyl jcad rexr syl2an cle simp11 simp12 ltle lbicc2 ubicc2
      imp 3adantl3 oveq1 oveq2 rspc2v ioossicc sseli fvelima w3o simpl1 simp333
      simprr elioo2 simp2d gtned simp13 simp3d ltned simprl3 ecase13d ex 3anass
      imbitrrdi elicc3 anbi1d elioo1 3imtr4d simpr reximdv2 ) BGHZCGHZEGHZIZBCU
      DJZBCUAKZDLZDMLZFDMUBKZHZFUWAUEZGLZEBFNZCFNZUFKZHZIZIZIZAUGZFNZEOZAUWAUHZ
      UWQABCUFKZUHUWNFUIZEUWFHUWRUWMUVSUWTUVTUWMDMFUJZUWTUWMUWEUXAUWBUWCUWEUWGU
      WKUKDMFULZPDMFUMZPQUWNUWHUWIUAKZUWFEUWNUWOUCUGZUAKZUWFLZUCUWFUNAUWFUNZUXD
      UWFLZUWNUFUOUPNZUWFRKZUSHZUXHUWNUXJUWARKZUSHZUWAUXKUQZFUWAURZVIZUXPUXMUXK
      SKZHUXLUVSUVTUXNUWMUVPUVQUXNUVRBCUTVAVBUWNUWAUWFUXPVIZUXQUWNUWTUWAFVJZLZT
      ZUXSUWNUWBUXATZUYBUWMUVSUYCUVTUWBUWCUWLUYCUWCUWLTZUXAUWBUYDUWEUXAUWCUWEUW
      GUWKVCUXBPVDVEQUYCUWTUYAUXAUWTUWBUXCVFUXAUYAUWBUXAUXTDUWADMFVKVGVHWAPZUWA
      FVLPUWNUWFUXOOZUXSUXQWBUWNUXJVMHUWGUYFVNUWEUWGUWKUWBUWCUVSUVTVOZUWFUXJGVP
      VQVRUWFUXOUWAUXPVSPVTUWNUXPUXMWCWDNZUWFRKZSKZUXRUWNUXPUXMUYHSKZHZUXPUYJHZ
      UWNUXPUYHDRKZUWARKZUYHSKZUYKUWNFUYNUYHSKZHUWAUYNUQZLUXPUYPHUWNFUWDUYQUWEU
      WGUWKUWBUWCUVSUVTWEUWMUVSUWDUYQOZUVTUWCUWBUYSUWLUWCMMLUYSMWFDMUYHUYNUYHUY
      HWGZUYNWGUYHMRKZUYHUYHVMHZVUAUYHOUYHUYTWHZUYHVMMMUYHUYHUYTWIZWJWLWKWMWNWO
      WPQWQUWNUWADUYRUVSUVTUWBUWCUWLUKZUWNUYNDWRNHZDUYROUWNUYHMWRNHZUWCVUFVUDUV
      SUVTUWBUWCUWLWSZDUYHMXBVRDUYNWTPXCUWAFUYNUYHUYRUYRWGXAXDUWNUYOUXMUYHSUWNU
      YOUYHUWARKZUXMUWNVUBUWBDXEHZUYOVUIOVUBUWNVUCYBVUEUWNUWCMXEHVUJVUHXFDMXEXL
      XGUWADUYHVMXEXHXIUWNUWAGLZVUIUXMOUVSUVTVUKUWMUVPUVQVUKUVRBCXJVAVBUWAUXJUY
      HUYTUXJWGZXKPXMXNWQUWNVUGUXPUOZUWFLZUWFMLUYLUYMWBVUGUWNVUDYBVUNUWNUWFVUMF
      UWAXOXPYBUWNUWFGMUYGXQXRUWFUXPUXMUYHMXSXIVTUWNUYIUXKUXMSUWNUWGUYIUXKOUYGU
      WFUXJUYHUYTVULXKPXTWQUXPUXMUXKUWAUXOUXOWGYAXIUWMUVSUXLUXHWBZUVTUWLUWBVUOU
      WCUWGUWEVUOUWKAUCUWFYCWPQQVTUWNUWHUWFHZUWIUWFHZUXHUXIYDUWNUYBBUWAHZVUPUYE
      UWNBYEHZCYEHZBCUUAJZVURUWNBUVPUVQUVRUVTUWMUUBYFZUWNCUVPUVQUVRUVTUWMUUCYFZ
      UVSUVTVVAUWMUVPUVQUVTVVAUVRUVPUVQTUVTVVABCUUDUUGUUHVAZBCUUEXIUWABFYGYNZUW
      NUYBCUWAHZVUQUYEUWNVUSVUTVVAVVFVVBVVCVVDBCUUFXIUWACFYGYNZUXGUXIUWHUXEUAKZ
      UWFLAUCUWHUWIUWFUWFUWOUWHOUXFVVHUWFUWOUWHUXEUAUUIYHUXEUWIOVVHUXDUWFUXEUWI
      UWHUAUUJYHUUKXDYIUWMUVSEUXDHZUVTUWLUWBVVIUWCUWKUWEVVIUWGUWJUXDEUWHUWIUULU
      UMQQQYJAEUWAFUUNXDUWNUWQUWQAUWAUWSUWNUWOUWAHZUWQTZUWOUWSHZUWQUWNUWOYEHZVV
      AUWOBOZBUWOUDJZUWOCUDJZTZUWOCOZUUOZIZUWQTZVVMVVOVVPIZVVKVVLUWNVWAVVMVVQTV
      WBUWNVWAVVMVVQVWAVVMYDUWNVVMVVAVVSUWQUUPYBUWNVWAVVQUWNVWATZVVQVVNVVRVWCUW
      PUWHOVVNVWCUWPUWHVWCUWPEUWHUWNVVTUWQUURZUWNEUWHYOVWAUWNUWHEUWNUWFGUWHUYGV
      VEYJZUWNUVRUWHEUDJZEUWIUDJZUWNUWKUVRVWFVWGIZUWEUWGUWKUWBUWCUVSUVTUUQUWNUW
      HYEHUWIYEHUWKVWHWBUWNUWHVWEYFUWNUWIUWNUWFGUWIUYGVVGYJYFUWHUWIEUUSXDVTZUUT
      UVAYKYLYMUWOBFYPYQVWCUWPUWIOVVRVWCUWPUWIVWCUWPEUWIVWDUWNEUWIYOVWAUWNEUWIU
      VPUVQUVRUVTUWMUVBUWNUVRVWFVWGVWIUVCUVDYKYLYMUWOCFYPYQVVMVVAVVSUWQUWNUVEUV
      FUVGYRVVMVVOVVPUVHUVIUWNVVJVVTUWQUVSUVTVVJVVTWBZUWMUVPUVQVWJUVRUVPVUSVUTV
      WJUVQBYSZCYSZBCUWOUVJYTVAVBUVKUVSUVTVVLVWBWBZUWMUVPUVQVWMUVRUVPVUSVUTVWMU
      VQVWKVWLBCUWOUVLYTVAVBUVMVVKUWQYDUWNVVJUWQUVNYBYRUVOYI $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Refinements
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c Fne $.
  $( Extend class definition to include the "finer than" relation. $)
  cfne $a class Fne $.

  ${
    $d x y z $.
    $( Define the fineness relation for covers.  (Contributed by Jeff Hankins,
       28-Sep-2009.) $)
    df-fne $a |- Fne = { <. x , y >. | ( U. x = U. y /\ A. z e. x z C_ U. ( y
    i^i ~P z ) ) } $.
  $}

  ${
    $d x y z $.
    $( Fineness is a relation.  (Contributed by Jeff Hankins, 28-Sep-2009.) $)
    fnerel $p |- Rel Fne $=
      ( vx vy vz cv cuni wceq cpw cin wss wral wa cfne df-fne relopabiv ) ADZEB
      DZEFCDZPQGHEICOJKABLABCMN $.
  $}

  ${
    $d r s x y z A $.  $d r s x y z B $.  $d x y z C $.  $d r s X $.
    $d r s Y $.
    isfne.1 $e |- X = U. A $.
    isfne.2 $e |- Y = U. B $.
    $( The predicate " ` B ` is finer than ` A ` ".  This property is, in a
       sense, the opposite of refinement, as refinement requires every element
       to be a subset of an element of the original and fineness requires that
       every element of the original have a subset in the finer cover
       containing every point.  I do not know of a literature reference for
       this.  (Contributed by Jeff Hankins, 28-Sep-2009.) $)
    isfne $p |- ( B e. C -> ( A Fne B <-> ( X = Y /\ A. x e. A x C_ U. ( B i^i
    ~P x ) ) ) ) $=
      ( vr vs wcel cfne wceq cv cin cuni wss wral wa cvv fnerel brrelex1i simpr
      wbr cpw anim1i ancoms 3eqtr3g uniexg adantr eqeltrd uniexb sylibr adantrr
      simpl jca syldan unieq eqtr4di eqeq1d raleq anbi12d eqeq2d unieqd ralbidv
      ineq1 sseq2d df-fne brabg pm5.21nd ) CDKZBCLUDZEFMZANZCVNUEZOZPZQZABRZSZB
      TKZVKSZVLVKWBVLWAVKBCLUAUBUFUGVKVMWBVSVKVMBPZCPZMZWBVKVMSEFWCWDVKVMUCGHUH
      VKWESZWAVKWFWCTKWAWFWCWDTVKWEUCVKWDTKWECDUIUJUKBULUMVKWEUOUPUQUNINZPZJNZP
      ZMZVNWIVOOZPZQZAWGRZSEWJMZWNABRZSVTIJBCTDLWGBMZWKWPWOWQWRWHEWJWRWHWCEWGBU
      RGUSUTWNAWGBVAVBWICMZWPVMWQVSWSWJFEWSWJWDFWICURHUSVCWSWNVRABWSWMVQVNWSWLV
      PWICVOVFVDVGVEVBIJAVHVIVJ $.

    $( The predicate " ` B ` is finer than ` A ` " in terms of the topology
       generation function.  (Contributed by Mario Carneiro, 11-Sep-2015.) $)
    isfne4 $p |- ( A Fne B <-> ( X = Y /\ A C_ ( topGen ` B ) ) ) $=
      ( vx cfne wbr cvv wcel wceq ctg cfv wss wa fnerel brrelex2i cuni wral cpw
      simpl 3eqtr3g fvex ssex adantl uniexd eqeltrrd uniexb sylibr cv cin isfne
      dfss3 eltg ralbidv bitrid anbi2d bitr4d pm5.21nii ) ABHIZBJKZCDLZABMNZOZP
      ZABHQRVFBSZJKVBVFASZVGJVFCDVHVGVCVEUBEFUCVFAJVEAJKVCAVDBMUDUEUFUGUHBUIUJV
      BVAVCGUKZBVIUAULSOZGATZPVFGABJCDEFUMVBVEVKVCVEVIVDKZGATVBVKGAVDUNVBVLVJGA
      VIBJUOUPUQURUSUT $.

    $( A condition for a topology to be finer than another.  (Contributed by
       Jeff Hankins, 28-Sep-2009.)  (Revised by Mario Carneiro,
       11-Sep-2015.) $)
    isfne4b $p |- ( B e. V -> ( A Fne B <-> ( X = Y /\
        ( topGen ` A ) C_ ( topGen ` B ) ) ) ) $=
      ( wcel cfne wbr wceq ctg cfv wss wa isfne4 cvv wb cuni simpr uniexg simpl
      3eqtr3g adantr eqeltrd uniexb sylibr tgss3 syl2anc pm5.32da bitr4id ) BCH
      ZABIJDEKZABLMZNZOUMALMUNNZOABDEFGPULUMUPUOULUMOZAQHZULUPUORUQASZQHURUQUSB
      SZQUQDEUSUTULUMTFGUCULUTQHUMBCUAUDUEAUFUGULUMUBABQCUHUIUJUK $.

    $( The predicate " ` B ` is finer than ` A ` ".  (Contributed by Jeff
       Hankins, 28-Sep-2009.)  (Proof shortened by Mario Carneiro,
       11-Sep-2015.) $)
    isfne2 $p |- ( B e. C -> ( A Fne B <-> ( X = Y /\ A. x e. A A. y e. x E. z
    e. B ( y e. z /\ z C_ x ) ) ) ) $=
      ( cfne wbr wceq ctg wss wa wcel cv wral bitrid wrex isfne4 eltg2b ralbidv
      cfv dfss3 anbi2d ) DEKLGHMZDENUEZOZPEFQZUHBRCRZQULARZOPCEUABUMSZADSZPDEGH
      IJUBUKUJUOUHUJUMUIQZADSUKUOADUIUFUKUPUNADBCUMEFUCUDTUGT $.

    $( The predicate " ` B ` is finer than ` A ` ".  (Contributed by Jeff
       Hankins, 11-Oct-2009.)  (Proof shortened by Mario Carneiro,
       11-Sep-2015.) $)
    isfne3 $p |- ( B e. C -> ( A Fne B <-> ( X = Y /\ A. x e. A E. y ( y C_ B
    /\ x = U. y ) ) ) ) $=
      ( cfne wbr wceq ctg cfv wss wa wcel cv wral bitrid wex isfne4 dfss3 eltg3
      cuni ralbidv anbi2d ) CDJKFGLZCDMNZOZPDEQZUHBRZDOARZULUELPBUAZACSZPCDFGHI
      UBUKUJUOUHUJUMUIQZACSUKUOACUIUCUKUPUNACBUMDEUDUFTUGT $.
  $}

  ${
    fnebas.1 $e |- X = U. A $.
    fnebas.2 $e |- Y = U. B $.
    $( A finer cover covers the same set as the original.  (Contributed by Jeff
       Hankins, 28-Sep-2009.) $)
    fnebas $p |- ( A Fne B -> X = Y ) $=
      ( cfne wbr wceq ctg cfv wss isfne4 simplbi ) ABGHCDIABJKLABCDEFMN $.
  $}

  $( A finer cover generates a topology finer than the original set.
     (Contributed by Mario Carneiro, 11-Sep-2015.) $)
  fnetg $p |- ( A Fne B -> A C_ ( topGen ` B ) ) $=
    ( cfne wbr cuni wceq ctg cfv wss eqid isfne4 simprbi ) ABCDAEZBEZFABGHIABMN
    MJNJKL $.

  ${
    $d x A $.  $d x B $.  $d x P $.  $d x S $.
    $( If ` B ` is finer than ` A ` and ` S ` is an element of ` A ` , every
       point in ` S ` is an element of a subset of ` S ` which is in ` B ` .
       (Contributed by Jeff Hankins, 28-Sep-2009.) $)
    fnessex $p |- ( ( A Fne B /\ S e. A /\ P e. S ) -> E. x e. B
        ( P e. x /\ x C_ S ) ) $=
      ( cfne wbr wcel ctg cfv cv wss wa wrex fnetg sselda tg2 stoic3 ) BCFGZEBH
      ECIJZHDEHDAKZHUAELMACNSBTEBCOPAECDQR $.
  $}

  ${
    $d x A $.  $d x B $.  $d x S $.
    $( If ` B ` is finer than ` A ` , every element of ` A ` is a union of
       elements of ` B ` .  (Contributed by Jeff Hankins, 11-Oct-2009.) $)
    fneuni $p |- ( ( A Fne B /\ S e. A ) -> E. x ( x C_ B /\ S = U. x ) ) $=
      ( cfne wbr wcel wa ctg cfv cv wss cuni wceq wex fnetg sselda cdm wb syl
      elfvdm eltg3 ibi ) BCEFZDBGHDCIJZGZAKZCLDUGMNHAOZUDBUEDBCPQUFUHUFCIRZGUFU
      HSDCIUAADCUIUBTUCT $.
  $}

  ${
    $d x y z A $.  $d x y z B $.  $d x y z P $.
    $( If a cover is finer than another, every point can be approached more
       closely by intersections.  (Contributed by Jeff Hankins,
       11-Oct-2009.) $)
    fneint $p |- ( A Fne B -> |^| { x e. B | P e. x }
    C_ |^| { x e. A | P e. x } ) $=
      ( vy vz cfne wbr cv wcel crab cint wss wral wa eleq2w elrab fnessex 3expb
      wrex intminss sstr sylan expl rexlimiv syl biimtrid ralrimiv ssint sylibr
      ex ) BCGHZDAIJZACKLZEIZMZEUMABKZNUNUQLMULUPEUQUOUQJUOBJZDUOJZOZULUPUMUSAU
      OBAEDPQULUTUPULUTODFIZJZVAUOMZOZFCTZUPULURUSVEFBCDUORSVDUPFCVACJZVBVCUPVF
      VBOUNVAMVCUPUMVBAVACAFDPUAUNVAUOUBUCUDUEUFUKUGUHEUNUQUIUJ $.
  $}

  ${
    $d x y z A $.  $d x y z B $.  $d x y z C $.
    fness.1 $e |- X = U. A $.
    fness.2 $e |- Y = U. B $.
    $( A cover is finer than its subcovers.  (Contributed by Jeff Hankins,
       11-Oct-2009.) $)
    fness $p |- ( ( B e. C /\ A C_ B /\ X = Y ) -> A Fne B ) $=
      ( vy vz vx wcel wss wceq w3a cfne wel cv wa wral simp3 wrex ssel2 3adant3
      wbr ssid jctir elequ2 anbi12d rspcev syl2anc 3expib ralrimivv 3ad2ant2 wb
      sseq1 isfne2 3ad2ant1 mpbir2and ) BCKZABLZDEMZNABOUDZVAHIPZIQZJQZLZRZIBUA
      ZHVESJASZUSUTVATUTUSVIVAUTVHJHAVEUTVEAKZHJPZVHUTVJVKNZVEBKZVKVEVELZRZVHUT
      VJVMVKABVEUBUCVLVKVNUTVJVKTVEUEUFVGVOIVEBVDVEMVCVKVFVNIJHUGVDVEVEUOUHUIUJ
      UKULUMUSUTVBVAVIRUNVAJHIABCDEFGUPUQUR $.
  $}

  ${
    $d x y z A $.  $d x y z V $.
    $( Reflexivity of the fineness relation.  (Contributed by Jeff Hankins,
       12-Oct-2009.) $)
    fneref $p |- ( A e. V -> A Fne A ) $=
      ( vy vz vx wcel cfne wbr cuni wceq wel cv wss wrex wral eqid elequ2 sseq1
      wa ssid anbi12d rspcev mpanr2 rgen2 pm3.2i isfne2 mpbiri ) ABFAAGHAIZUHJZ
      CDKZDLZELZMZSZDANZCULOEAOZSUIUPUHPZUOECAULULAFCEKZULULMZUOULTUNURUSSDULAU
      KULJUJURUMUSDECQUKULULRUAUBUCUDUEECDAABUHUHUQUQUFUG $.
  $}

  $( Transitivity of the fineness relation.  (Contributed by Jeff Hankins,
     5-Oct-2009.)  (Proof shortened by Mario Carneiro, 11-Sep-2015.) $)
  fnetr $p |- ( ( A Fne B /\ B Fne C ) -> A Fne C ) $=
    ( cfne wbr wa cuni wceq ctg cfv wss eqid fnebas cvv wcel brrelex2i simplbda
    fnerel isfne4b mpancom sylan9eq sylan9ss wb adantl syl mpbir2and ) ABDEZBCD
    EZFZACDEZAGZCGZHZAIJZCIJZKZUGUHUKBGZULABUKUQUKLZUQLZMBCUQULUSULLZMUAUGUHUNB
    IJZUOBNOZUGUNVAKZABDRPVBUGUKUQHVCABNUKUQURUSSQTCNOZUHVAUOKZBCDRPZVDUHUQULHV
    EBCNUQULUSUTSQTUBUIVDUJUMUPFUCUHVDUGVFUDACNUKULURUTSUEUF $.

  ${
    fneval.1 $e |- .~ = ( Fne i^i `' Fne ) $.
    $( Two covers are finer than each other iff they are both bases for the
       same topology.  (Contributed by Mario Carneiro, 11-Sep-2015.) $)
    fneval $p |- ( ( A e. V /\ B e. W ) ->
      ( A .~ B <-> ( topGen ` A ) = ( topGen ` B ) ) ) $=
      ( wbr cfne wa wcel ctg cfv wceq anbi2i bitri cuni wss eqid isfne4b unitg
      ccnv breqi brin fnerel relbrcnv eqcom anbi1i bitrdi bi2anan9r eqss anandi
      cin bitr4di unieq eqeqan12d imbitrid pm4.71rd bitr4d bitrid ) ABCGZABHGZB
      AHGZIZADJZBEJZIZAKLZBKLZMZUTABHHUAZULZGZVCABCVKFUBVLVAABVJGZIVCABHVJUCVMV
      BVAABHUDUENOOVFVCAPZBPZMZVIIZVIVFVCVPVGVHQZIZVPVHVGQZIZIZVQVEVAVSVDVBWAAB
      EVNVOVNRZVORZSVDVBVOVNMZVTIWABADVOVNWDWCSWEVPVTVOVNUFUGUHUIVQVPVRVTIZIWBV
      IWFVPVGVHUJNVPVRVTUKOUMVFVIVPVIVGPZVHPZMVFVPVGVHUNVDVEWGVNWHVOADTBETUOUPU
      QURUS $.

    $d x y .~ $.
    $( Fineness intersected with its converse is an equivalence relation.
       (Contributed by Jeff Hankins, 6-Oct-2009.)  (Revised by Mario Carneiro,
       11-Sep-2015.) $)
    fneer $p |- .~ Er _V $=
      ( vx vy ctg cfv fveq2 wbr copab wceq wrel cfne wss ccnv cin inss1 eqsstri
      cv fnerel cvv relss mp2 dfrel4v mpbi wb fneval el2v opabbii eqtri eqer )
      CDCRZEFZDRZEFZAUKUMEGAUKUMAHZCDIZULUNJZCDIAKZAUPJALMLKURALLNZOLBLUSPQSALU
      AUBCDAUCUDUOUQCDUOUQUECDUKUMATTBUFUGUHUIUJ $.
  $}

  ${
    topfne.1 $e |- X = U. J $.
    topfne.2 $e |- Y = U. K $.
    $( Fineness for covers corresponds precisely with fineness for topologies.
       (Contributed by Jeff Hankins, 29-Sep-2009.) $)
    topfne $p |- ( ( K e. Top /\ X = Y ) -> ( J C_ K <-> J Fne K ) ) $=
      ( ctop wcel wss ctg cfv wceq cfne wbr tgtop sseq2d bicomd isfne4 sylan9bb
      baibr ) BGHZABIZABJKZIZCDLZABMNZUAUDUBUAUCBABOPQUFUEUDABCDEFRTS $.
  $}

  ${
    topfneec.1 $e |- .~ = ( Fne i^i `' Fne ) $.
    $( A cover is equivalent to a topology iff it is a base for that topology.
       (Contributed by Jeff Hankins, 8-Oct-2009.)  (Proof shortened by Mario
       Carneiro, 11-Sep-2015.) $)
    topfneec $p |- ( J e. Top -> ( A e. [ J ] .~ <-> ( topGen ` A ) = J ) ) $=
      ( cec wcel wbr ctop ctg cfv wceq wrel wb cvv wer fneer ax-mp wa ctb ex wi
      errel relelec brrelex2i a1i eleq1 biimparc tgclb sylibr elex fneval tgtop
      syl eqeq1d eqcom bitrdi adantr bitrd pm5.21ndd bitrid ) ACBEFZCABGZCHFZAI
      JZCKZBLZVAVBMNBOVFBDPNBUBQZACBUCQVCANFZVBVEVBVHUAVCCABVGUDUEVCVEVHVCVERZA
      SFZVHVIVDHFZVJVEVKVCVDCHUFUGAUHUIASUJUMTVCVHVBVEMVCVHRVBCIJZVDKZVECABHNDU
      KVCVMVEMVHVCVMCVDKVEVCVLCVDCULUNCVDUOUPUQURTUSUT $.
  $}

  ${
    topfneec2.1 $e |- .~ = ( Fne i^i `' Fne ) $.
    $( A topology is precisely identified with its equivalence class.
       (Contributed by Jeff Hankins, 12-Oct-2009.) $)
    topfneec2 $p |- ( ( J e. Top /\ K e. Top ) ->
      ( [ J ] .~ = [ K ] .~ <-> J = K ) ) $=
      ( ctop wcel wa wbr ctg cfv wceq cec fneval cvv wer fneer a1i adantr tgtop
      elex erth eqeqan12d 3bitr3d ) BEFZCEFZGZBCAHBIJZCIJZKBALCALKBCKBCAEEDMUFB
      CANNAOUFADPQUDBNFUEBETRUAUDUEUGBUHCBSCSUBUC $.
  $}

  ${
    $d c t w x y z A $.  $d c t w x y z B $.  $d c t w x y z X $.
    $d c t w x y z Y $.
    fnessref.1 $e |- X = U. A $.
    fnessref.2 $e |- Y = U. B $.
    $( A cover is finer iff it has a subcover which is both finer and a
       refinement.  (Contributed by Jeff Hankins, 18-Jan-2010.)  (Revised by
       Thierry Arnoux, 3-Feb-2020.) $)
    fnessref $p |- ( X = Y ->
      ( A Fne B <-> E. c ( c C_ B /\ ( A Fne c /\ c Ref A ) ) ) ) $=
      ( vx vy vw vz wceq cfne wbr wss wa wrex cvv wcel wi vt cv cref wex fnerel
      crab brrelex2i adantl rabexg syl ssrab2 a1i cuni wral eluni bitri fnessex
      eleq2i 3expia adantll sseq2 rspcev anim2d reximdv syld com23 impd exlimdv
      ex biimtrid elunirab imbitrrdi ssrdv unissi simpl eqtr2di sseqtrid expcom
      eqssd 3expb ad2antll com12 ad2antrl jcad sseq1 rexbidv elrab reximdv2 mpd
      simpr ralrimivva eqid isfne2 3syl mpbir2and cbvrexvw ralrimiv isref jca32
      wb bilani breq2 breq1 anbi12d spcegv sylc simprrl fnebas eqtr3d eqeltrrdi
      eqtrdi vuniex uniexb sylibr simprl fness syl3anc fnetr syl2anc impbid ) C
      DLZABMNZEUBZBOZAYCMNZYCAUCNZPZPZEUDZYAYBYIYAYBPZHUBZIUBZOZIAQZHBUFZRSZYOB
      OZAYOMNZYOAUCNZPZPZYIYJBRSZYPYBUUBYAABMUEUGUHZYNHBRUIZUJYJYQYRYSYQYJYNHBU
      KZULYJYRCYOUMZLZUAUBZJUBZSZUUIKUBZOZPZJYOQZUAUUKUNKAUNZYJCUUFYJUACUUFYJUU
      HCSZUUHYKSZYNPZHBQZUUHUUFSUUPUUHUUKSZUUKASZPZKUDZYJUUSUUPUUHAUMZSUVCCUVDU
      UHFURKUUHAUOUPYJUVBUUSKYJUUTUVAUUSYJUVAUUTUUSYJUVAUUTUUSTYJUVAPZUUTUUQYKU
      UKOZPZHBQZUUSYBUVAUUTUVHTYAYBUVAUUTUVHHABUUHUUKUQUSUTUVEUVGUURHBUVEUVFYNU
      UQUVAUVFYNTYJUVAUVFYNYMUVFIUUKAYLUUKYKVAVBVIUHVCVDVEVIVFVGVHVJYNHUUHBVKVL
      VMYJBUMZUUFCYOBUUEVNYJCDUVIYAYBVOGVPVQVSZYJUUNKUAAUUKYJUVAUUTPZPZUUMJBQZU
      UNYBUVKUVMYAYBUVAUUTUVMJABUUHUUKUQVTUTUVLUUMUUMJBYOUVLUUIBSZUUMPZUUIYOSZU
      UMUVLUVOUVNUUIYLOZIAQZPUVPUVLUVOUVNUVRUVOUVNTUVLUVNUUMVOULUVAUVOUVRTYJUUT
      UVOUVAUVRUULUVAUVRTUVNUUJUVAUULUVRUVQUULIUUKAYLUUKUUIVAVBVRWAWBWCWDYNUVRH
      UUIBYKUUILYMUVQIAYKUUIYLWEWFWGVLUVOUUMTUVLUVNUUMWJULWDWHWIWKYJUUBYPYRUUGU
      UOPWTUUCUUDKUAJAYORCUUFFUUFWLZWMWNWOYJYSUUGUUKUUIOZJAQZKYOUNZUVJYJUWAKYOU
      UKYOSUUKBSZUUKYLOZIAQZPZYJUWAYNUWEHUUKBYKUUKLYMUWDIAYKUUKYLWEWFWGUWFUWATY
      JUWEUWAUWCUWDUVTIJAYLUUIUUKVAWPXAULVJWQYJUUBYPYSUUGUWBPWTUUCUUDKJYOARUUFC
      UVSFWRWNWOWSYHUUAEYORYCYOLZYDYQYGYTYCYOBWEUWGYEYRYFYSYCYOAMXBYCYOAUCXCXDX
      DXEXFVIYAYHYBEYAYHYBYAYHPZYEYCBMNZYBYAYDYEYFXGZUWHUUBYDYCUMZDLUWIUWHUVIRS
      UUBUWHUVIUWKRUWHUWKDUVIUWHCUWKDUWHYECUWKLUWJAYCCUWKFUWKWLZXHUJYAYHVOXIZGX
      KEXLXJBXMXNYAYDYGXOUWMYCBRUWKDUWLGXPXQAYCBXRXSVIVHXT $.
  $}

  ${
    $d c x y A $.  $d c x y B $.  $d c x y X $.  $d c x y Y $.
    refssfne.1 $e |- X = U. A $.
    refssfne.2 $e |- Y = U. B $.
    $( A cover is a refinement iff it is a subcover of something which is both
       finer and a refinement.  (Contributed by Jeff Hankins, 18-Jan-2010.)
       (Revised by Thierry Arnoux, 3-Feb-2020.) $)
    refssfne $p |- ( X = Y -> ( B Ref A <->
      E. c ( B C_ c /\ ( A Fne c /\ c Ref A ) ) ) ) $=
      ( vx vy wceq cref wbr cv wss cfne wa cvv wcel adantl cuni brrelex2i unexg
      wex cun refrel brrelex1i syl2anc ssun2 ssun1 eqimss2 adantr ssequn2 sylib
      eqcomd uneq12i uniun eqtr4i fness syl3anc wrex wral wo elun wi ssid sseq2
      a1i rspcev mpan2 refssex ex jaod biimtrid ralrimiv wb isref syl mpbir2and
      jca32 breq2 breq1 anbi12d spcegv sylc vex ssex ad2antrl simprl simpl eqid
      refbas ad2antll eqtr3d ssref simprrr reftr exlimdv impbid ) CDJZBAKLZBEMZ
      NZAXAOLZXAAKLZPZPZEUCZWSWTXGWSWTPZABUDZQRZBXINZAXIOLZXIAKLZPZPZXGXHAQRZBQ
      RZXJWTXPWSBAKUEUASWTXQWSBAKUEUFSABQQUBUGZXHXKXLXMXKXHBAUHVGXHXJAXINZCCDUD
      ZJZXLXRXSXHABUIVGXHXTCXHDCNZXTCJWSYBWTDCUJUKDCULUMUNZAXIQCXTFXTATZBTZUDXI
      TCYDDYEFGUOABUPUQZURUSXHXMYAHMZIMZNZIAUTZHXIVAZYCXHYJHXIYGXIRYGARZYGBRZVB
      XHYJYGABVCXHYLYJYMYLYJVDXHYLYGYGNZYJYGVEYIYNIYGAYHYGYGVFVHVIVGWTYMYJVDWSW
      TYMYJIBAYGVJVKSVLVMVNXHXJXMYAYKPVOXRHIXIAQXTCYFFVPVQVRVSXFXOEXIQXAXIJZXBX
      KXEXNXAXIBVFYOXCXLXDXMXAXIAOVTXAXIAKWAWBWBWCWDVKWSXFWTEWSXFWTWSXFPZBXAKLZ
      XDWTYPXQXBDXATZJYQXBXQWSXEBXAEWEWFWGWSXBXEWHYPCDYRWSXFWIXECYRJZWSXBXDYSXC
      XAAYRCYRWJZFWKSWLWMBXAQDYRGYTWNUSWSXBXCXDWOBXAAWPUGVKWQWR $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Neighborhood bases determine topologies
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d f k n t v y z G $.  $d j n s u v x y z J $.  $d f o s t u v w x y z P $.
    $d f k o s t u v w x y z N $.  $d f k o t u v x y S $.  $d f k n x y z U $.
    $d a b f g j k n o s t u v w x y z F $.  $d f j k n o s t v w x y z ph $.
    $d a b f g j k n o s t u v w x y z X $.
    neibastop1.1 $e |- ( ph -> X e. V ) $.
    neibastop1.2 $e |- ( ph -> F : X --> ( ~P ~P X \ { (/) } ) ) $.
    neibastop1.3 $e |- ( ( ph /\ ( x e. X /\ v e. ( F ` x ) /\
      w e. ( F ` x ) ) ) -> ( ( F ` x ) i^i ~P ( v i^i w ) ) =/= (/) ) $.
    neibastop1.4 $e |- J = { o e. ~P X |
      A. x e. o ( ( F ` x ) i^i ~P o ) =/= (/) } $.
    $( A collection of neighborhood bases determines a topology.  Part of
       Theorem 4.5 of Stephen Willard's _General Topology_.  (Contributed by
       Jeff Hankins, 8-Sep-2009.)  (Proof shortened by Mario Carneiro,
       11-Sep-2015.) $)
    neibastop1 $p |- ( ph -> J e. ( TopOn ` X ) ) $=
      ( vy wcel wss cin wral wa c0 vz ctop cuni wceq ctopon cfv cv wi wal simpr
      cpw wne crab ssrab2 eqsstri sstrdi sspwuni vuniex elpw sylibr wrex eluni2
      sylib elssuni ad2antrl sspwd sslin syl sselda adantrr weq pweq raleqbi1dv
      ineq2d neeq1d elrab2 simprbi simprr sylc ssn0 syl2anc rexlimdvaa biimtrid
      rsp ralrimiv sylanbrc ex alrimiv anbi12i an4 bitri inss1 elpwi sstrid vex
      inex1 ssralv ax-mp inss2 anim12i r19.26 wex exdistrv simprl sselid elpwid
      ss2in simplll ad2antrr simplr sseldd syl13anc exlimdvv biimtrrid ralimdva
      n0 syl5 impr sylan2b ralrimivva cvv wb mpbi ssexd uniexb istopg mpbir2and
      a1i pwidg csn cdif ffvelcdmda 3syl dfss2 eldifsni eqnetrd ralrimiva eqssd
      eldifi istopon ) AGUBOZIGUCZUDGIUEUFOAUUANUGZGPZUUCUCZGOZUHZNUIZUUCUAUGZQ
      ZGOZUAGRNGRZAUUGNAUUDUUFAUUDSZUUEIUKZOZBUGZFUFZUUEUKZQZTULZBUUERZUUFUUMUU
      EIPZUUOUUMUUCUUNPUVBUUMUUCGUUNAUUDUJZGUUQEUGZUKZQZTULZBUVDRZEUUNUMUUNMUVH
      EUUNUNUOZUPUUCIUQVCUUEINURUSUTUUMUUTBUUEUUPUUEOUUPUUIOZUAUUCVAUUMUUTUAUUP
      UUCVBUUMUVJUUTUAUUCUUMUUIUUCOZUVJSSZUUQUUIUKZQZUUSPZUVNTULZUUTUVLUVMUURPU
      VOUVLUUIUUEUVKUUIUUEPUUMUVJUUIUUCVDVEVFUVMUURUUQVGVHUVLUVPBUUIRZUVJUVPUVL
      UUIGOZUVQUUMUVKUVRUVJUUMUUCGUUIUVCVIVJUVRUUIUUNOZUVQUVHUVQEUUIUUNGUVGUVPB
      UVDUUIEUAVKZUVFUVNTUVTUVEUVMUUQUVDUUIVLVNVOVMMVPZVQVHUUMUVKUVJVRUVPBUUIWD
      VSUVNUUSVTWAWBWCWEUVHUVAEUUEUUNGUVGUUTBUVDUUEUVDUUEUDZUVFUUSTUWBUVEUURUUQ
      UVDUUEVLVNVOVMMVPWFWGWHAUUKNUAGGUUCGOZUVRSZAUUCUUNOZUVSSZUUQUUCUKZQZTULZB
      UUCRZUVQSZSZUUKUWDUWEUWJSZUVSUVQSZSUWLUWCUWMUVRUWNUVHUWJEUUCUUNGUVGUWIBUV
      DUUCENVKZUVFUWHTUWOUVEUWGUUQUVDUUCVLVNVOVMMVPUWAWIUWEUWJUVSUVQWJWKAUWLSZU
      UJUUNOZUUQUUJUKZQZTULZBUUJRZUUKUWPUUJIPZUWQAUWFUXBUWKUWEUXBAUVSUWEUUJUUCI
      UUCUUIWLZUUCIWMWNVEZVJUUJIUUCUUINWOWPUSUTAUWFUWKUXAUWKUWIUVPSZBUUJRZAUWFS
      ZUXAUWKUWIBUUJRZUVPBUUJRZSUXFUWJUXHUVQUXIUUJUUCPUWJUXHUHUXCUWIBUUJUUCWQWR
      UUJUUIPUVQUXIUHUUCUUIWSUVPBUUJUUIWQWRWTUWIUVPBUUJXAUTUXGUXEUWTBUUJUXEDUGZ
      UWHOZDXBZCUGZUVNOZCXBZSZUXGUUPUUJOZSZUWTUWIUXLUVPUXODUWHXPCUVNXPWIUXPUXKU
      XNSZCXBDXBUXRUWTUXKUXNDCXCUXRUXSUWTDCUXRUXSUWTUXRUXSSZUUQUXJUXMQZUKZQZUWS
      PZUYCTULZUWTUXTUYBUWRPUYDUXTUYAUUJUXTUXJUUCPUXMUUIPUYAUUJPUXTUXJUUCUXTUWH
      UWGUXJUUQUWGWSUXRUXKUXNXDZXEXFUXTUXMUUIUXTUVNUVMUXMUUQUVMWSUXRUXKUXNVRZXE
      XFUXJUUCUXMUUIXGWAVFUYBUWRUUQVGVHUXTAUUPIOZUXJUUQOUXMUUQOUYEAUWFUXQUXSXHU
      XTUUJIUUPUXGUXBUXQUXSUXDXIUXGUXQUXSXJXKUXTUWHUUQUXJUUQUWGWLUYFXEUXTUVNUUQ
      UXMUUQUVMWLUYGXELXLUYCUWSVTWAWGXMXNWCXOXQXRUVHUXAEUUJUUNGUVGUWTBUVDUUJUVD
      UUJUDZUVFUWSTUYIUVEUWRUUQUVDUUJVLVNVOVMMVPWFXSXTAGYAOZUUAUUHUULSYBAUUBYAO
      UYJAUUBIHJUUBIPZAGUUNPUYKUVIGIUQYCYHZYDGYEUTNUAYAGYFVHYGAIUUBAIGOZIUUBPAI
      UUNOZUUQUUNQZTULZBIRZUYMAIHOUYNJIHYIVHAUYPBIAUYHSZUYOUUQTUYRUUQUUNPZUYOUU
      QUDUYRUUQUUNUKZTYJZYKZOZUUQUYTOUYSAIVUBUUPFKYLZUUQUYTVUAYSUUQUUNWMYMUUQUU
      NYNVCUYRVUCUUQTULVUDUUQUYTTYOVHYPYQUVHUYQEIUUNGUVGUYPBUVDIUVDIUDZUVFUYOTV
      UEUVEUUNUUQUVDIVLVNVOVMMVPWFIGVDVHUYLYRIGYTWF $.

    neibastop1.5 $e |- ( ( ph /\ ( x e. X /\ v e. ( F ` x ) ) ) -> x e. v ) $.
    neibastop1.6 $e |- ( ( ph /\ ( x e. X /\ v e. ( F ` x ) ) ) ->
      E. t e. ( F ` x ) A. y e. t ( ( F ` y ) i^i ~P v ) =/= (/) ) $.
    ${
      neibastop2.p $e |- ( ph -> P e. X ) $.
      neibastop2.n $e |- ( ph -> N C_ X ) $.
      neibastop2.f $e |- ( ph -> U e. ( F ` P ) ) $.
      neibastop2.u $e |- ( ph -> U C_ N ) $.
      neibastop2.g $e |- G = ( rec ( ( a e. _V |-> U_ z e. a U_ x e. X
        ( ( F ` x ) i^i ~P z ) ) , { U } ) |` _om ) $.
      neibastop2.s $e |- S = { y e. X |
        E. f e. U. ran G ( ( F ` y ) i^i ~P f ) =/= (/) } $.
      $( Lemma for ~ neibastop2 .  (Contributed by Jeff Hankins,
         12-Sep-2009.) $)
      neibastop2lem $p |- ( ph -> E. u e. J ( P e. u /\ u C_ N ) ) $=
        ( vk vn wcel wss cv wa wrex cpw cfv cin c0 wne wral cuni ssrab2 eqsstri
        crn crab wb elpw2g syl mpbiri weq fveq2 ineq1d neeq1d rexbidv elrab2 wi
        com wfn cvv ciun cmpt csn crdg frfnom fneq1i mpbir fnunirn ax-mp wex n0
        cres inss1 sseli anassrs sylan2 adantrl simprl wel fvssunirn frnd sylib
        sspwuni ad2antrr sstrid sselda elpwid adantrr pweq ineq2d eleq2d rspcev
        eliun syl2anc sylibr wceq sseq1d adantr adantl iunss ralrimiva ralrimiv
        iuneq1 expr syl12anc fnfvelrn elunii sylanbrc exlimdv biimtrid rexlimdv
        impr inelcm eleq2 ad3antrrr sseldd cdif difss2d simprlr ad2ant2l bitrid
        csuc rspe simpll simprll fveq1i snex fr0g eqtri pwidg snssd pwexd inss2
        eqtrdi elpwi sspwd ralrimivw ssralv mpan9 ssexd frsucmpt2 expcom finds2
        eqsstrd fvex elpw imbitrrdi com12 ffnfv mpbiran eleqtrrd peano2 sylancr
        wf simprr reqabi ralimdva dfss3 rexlimddv rexlimdvaa expimpd raleqbi1dv
        velpw snidg peano1 mp2an eqeltrri sylancl eluni2 rexrn ffvelcdmda sstrd
        elin simprrr simpllr simprrl elequ1 imbi12d rspcv syl3c exp32 rexlimdva
        3impia rabssdv eqsstrid sseq1 anbi12d ) AJPUOZIJUOZJQUPZIGUQZUOZUXOQUPZ
        URZGPUSAJSUTZUOZBUQZNVAZJUTZVBZVCVDZBJVEZUXLAUXTJSUPZJCUQZNVAZLUQZUTZVB
        ZVCVDZLOVIZVFZUSZCSVJZSULUYPCSVGVHASRUOUXTUYGVKUAJSRVLVMVNAUYEBJUYAJUOU
        YASUOZUYBUYKVBZVCVDZLUYOUSZURAUYEUYPVUACUYASJCBVOZUYMUYTLUYOVUBUYLUYSVC
        VUBUYIUYBUYKUYHUYANVPVQVRVSULVTAUYRVUAUYEAUYRURZUYTUYELUYOUYJUYOUOZUYJU
        MUQZOVAZUOZUMWBUSZVUCUYTUYEWAZOWBWCZVUDVUHVKVUJTWDDTUQZBSUYBDUQZUTZVBZW
        EZWEZWFZKWGZWHWBWPZWBWCVURVUQWIWBOVUSUKWJWKZUMUYJOWBWLWMVUCVUGVUIUMWBUY
        TFUQZUYSUOZFWNVUCVUEWBUOZVUGURZURZUYEFUYSWOVVEVVBUYEFVUCVVDVVBUYEVUCVVD
        VVBURZURZUYIVVAUTZVBZVCVDZCHUQZVEZUYEHUYBVUCVVBVVLHUYBUSZVVDVVBVUCVVAUY
        BUOZVVMUYSUYBVVAUYBUYKWQWRAUYRVVNVVMUFWSWTXAVVGVVKUYBUOZVVLURURZVVOVVKU
        YCUOZUYEVVGVVOVVLXBVVPVVKJUPZVVQVVPUYHJUOZCVVKVEZVVRVVGVVOVVLVVTVVGVVOU
        RZVVJVVSCVVKVWACHXCZVVJVVSVWAVWBVVJURZURZUYHSUOZUYPVVSVWAVWBVWEVVJVWAVV
        KSUYHVWAVVKSVVGUYBUXSVVKVVGUYBNVIZVFZUXSNUYAXDAVWGUXSUPZUYRVVFAVWFUXSUT
        ZUPVWHAVWFVWIVCWGZASVWIVWJUUANUBXEUUBVWFUXSXGXFXHXIXJXKXJXLVWDVVAUYOUOZ
        VVJUYPVVGVWKVVOVWCVVGVVAVUEUUFZOVAZUOVWMUYNUOZVWKVVGVVADVUFVUOWEZVWMVVG
        VVAVUOUOZDVUFUSZVVAVWOUOVVGVUGVVBBSUSZVWQVUCVVCVUGVVBUUCUYRVVBVWRAVVDVV
        BBSUUGUUDVWPVWRDUYJVUFVWPVVAVUNUOZBSUSDLVOZVWRBVVASVUNXQVWTVWSVVBBSVWTV
        UNUYSVVAVWTVUMUYKUYBVULUYJXMXNXOVSUUEXPXRDVVAVUFVUOXQXSVVGAVVCVUFKUTZUP
        ZVWMVWOXTZAUYRVVFUUHVUCVVCVUGVVBUUIZVVGVUFUYOVXAOVUEXDAUYOVXAUPZUYRVVFA
        UYNVXAUTZUPVXEAWBVXFOAUNUQZOVAZVXFUOZUNWBVEZWBVXFOUVRZAVXIUNWBVXGWBUOZA
        VXIVXLAVXHVXAUPZVXIVXMVURVXAUPVXBVWMVXAUPZAUNUMVXGVCXTZVXHVURVXAVXOVXHV
        COVAZVURVXGVCOVPVXPVCVUSVAZVURVCOVUSUKUUJVURWDUOVXQVURXTKUUKVURWDVUQUUL
        WMUUMZUURYAUNUMVOVXHVUFVXAVXGVUEOVPYAVXGVWLXTVXHVWMVXAVXGVWLOVPYAAKVXAA
        KINVAZUOZKVXAUOZUIKVXSUUNVMZUUOAVVCVXBVXNWAAVVCVXBVXNAVVCVXBURZURZVWMVW
        OVXAVYDVVCVWOWDUOVXCAVVCVXBXBVYDVWOVXAWDVYDKVXSAVXTVYCUIYBUUPVYDVUOVXAU
        PZDVUFVEZVWOVXAUPAVYEDVXAVEZVYCVYFAVYEDVXAAVULVXAUOZURZVUNVXAUPZBSVEVYE
        VYIVYJBSVYIVUNVUMVXAUYBVUMUUQVYIVULKVYHVULKUPAVULKUUSYCUUTXIUVABSVUNVXA
        YDXSYEVXBVYGVYFWAVVCVYEDVUFVXAUVBYCUVCDVUFVUOVXAYDXSZUVDTCVURVUEVUPVWOD
        UYHVUOWEOWDUKDUYHVUKVUOYGDUYHVUFVUOYGUVEXRZVYKUVHYHUVFUVGVXHVXAVXGOUVIU
        VJUVKUVLYFVXKVUJVXJVUTUNWBVXFOUVMUVNXSZXEUYNVXAXGXFXHXIVYLYIUVOVVGVUJVW
        LWBUOZVWNVUTVVGVVCVYNVXDVUEUVPVMWBVWLOYJUVQVVAVWMUYNYKXRXHVWAVWBVVJUVSU
        YMVVJLVVAUYOLFVOZUYLVVIVCVYOUYKVVHUYIUYJVVAXMXNVRXPXRUYPCJSULUVTYLYHUWA
        YPCVVKJUWBXSHJUWGXSVVKUYBUYCYQXRUWCYHYMYNUWDYNYOUWEYNYFUYBMUQZUTZVBZVCV
        DZBVYPVEUYFMJUXSPVYSUYEBVYPJVYPJXTZVYRUYDVCVYTVYQUYCUYBVYPJXMXNVRUWFUDV
        TYLAISUOVXSUYKVBZVCVDZLUYOUSZUXMUGAKUYOUOZVXSVXAVBZVCVDZWUCAKVURUOZVURU
        YNUOWUDAVXTWUGUIKVXSUWHVMVXPVURUYNVXRVUJVCWBUOVXPUYNUOVUTUWIWBVCOYJUWJU
        WKKVURUYNYKUWLAVXTVYAWUFUIVYBKVXSVXAYQXRWUBWUFLKUYOUYJKXTZWUAWUEVCWUHUY
        KVXAVXSUYJKXMXNVRXPXRUYPWUCCISJUYHIXTZUYMWUBLUYOWUIUYLWUAVCWUIUYIVXSUYK
        UYHINVPVQVRVSULVTYLAJUYQQULAUYPCSQAVWEUYPUYHQUOZAVWEURZUYMWUJLUYOVUDLDX
        CZDUYNUSZWUKUYMWUJWAZDUYJUYNUWMWUMVUHWUKWUNVUJWUMVUHVKVUTWULVUGDUMWBOVU
        LVUFUYJYRUWNWMWUKVUGWUNUMWBWUKVVCURZVUGUYMWUJWUOVUGUYMURZURZUYJQUYHWUQU
        YJKQWUQUYJKWUOVUGUYJVXAUOUYMWUOVUFVXAUYJWUOVUFVXAWUKWBVXFVUEOAVXKVWEVYM
        YBUWOXKXJXLXKAKQUPVWEVVCWUPUJYSUWPWUOVUGUYMCLXCZUYMVVAUYLUOZFWNWUOVUGUR
        ZWURFUYLWOWUTWUSWURFWUSVVAUYIUOZVVAUYKUOZURZWUTWURVVAUYIUYKUWQWUOVUGWVC
        WURWUOVUGWVCURZURZVVAUYJUYHWVEVVAUYJWUOVUGWVAWVBUWRXKWVEVWEVVNBFXCZWAZB
        SVEZWVACFXCZAVWEVVCWVDUWSAWVHVWEVVCWVDAWVGBSAUYRVVNWVFUEYHYEYSWUOVUGWVA
        WVBUWTWVGWVAWVIWABUYHSBCVOZVVNWVAWVFWVIWVJUYBUYIVVAUYAUYHNVPXOBCFUXAUXB
        UXCUXDYTYHYNYMYNYPYTUXEUXFYNYNYOUXGUXHUXIUXRUXMUXNURGJPUXOJXTUXPUXMUXQU
        XNUXOJIYRUXOJQUXJUXKXPYI $.
    $}

    $( In the topology generated by a neighborhood base, a set is a
       neighborhood of a point iff it contains a subset in the base.
       (Contributed by Jeff Hankins, 9-Sep-2009.)  (Proof shortened by Mario
       Carneiro, 11-Sep-2015.) $)
    neibastop2 $p |- ( ( ph /\ P e. X ) -> ( N e. ( ( nei ` J ) ` { P } ) <->
        ( N C_ X /\ ( ( F ` P ) i^i ~P N ) =/= (/) ) ) ) $=
      ( wcel vs vu vz vg va vb vn vf wa csn cnei cfv wss cpw cin c0 cuni ctopon
      wne ctop neibastop1 topontop syl adantr eqid neii1 wceq toponuni ad2antrr
      sylan sseqtrrd cv wrex neii2 wral wi pweq ineq2d neeq1d raleqbi1dv elrab2
      weq simprrr sspwd sslin simprrl wb snssg ad3antlr mpbird fveq2 rspcv ssn0
      ineq1d syl6an expr com23 expimpd biimtrid rexlimdv mpd jca ex wex n0 elin
      simprl sseqtrd cvv ciun cmpt crdg com cres crn crab cdif wf simpll simplr
      w3a elpwid cbviunv iuneq2d eqtrid mpteq2i rdgeq1 reseq1i cbvrexvw rexbidv
      ax-mp bitrid cbvrabv neibastop2lem eleqtrd isneip syl2anc exlimdv impbid
      mpbir2and ) AGMTZUIZKGUJZJUKULULTZKMUMZGIULZKUNZUOZUPUSZUIZUUBUUDUUJUUBUU
      DUIZUUEUUIUUKKJUQZMUUBJUTTZUUDKUULUMZAUUMUUAAJMURULTZUUMABDEHIJLMNOPQVAZM
      JVBVCZVDZUUCJKUULUULVEZVFVJAMUULVGZUUAUUDAUUOUUTUUPMJVHVCZVIVKUUKUUCCVLZU
      MZUVBKUMZUIZCJVMZUUIUUBUUMUUDUVFUURUUCCJKVNVJUUKUVEUUICJUVBJTUVBMUNZTZBVL
      ZIULZUVBUNZUOZUPUSZBUVBVOZUIUUKUVEUUIVPZUVJHVLZUNZUOZUPUSZBUVPVOUVNHUVBUV
      GJUVSUVMBUVPUVBHCWBZUVRUVLUPUVTUVQUVKUVJUVPUVBVQVRVSVTQWAUUKUVHUVNUVOUUKU
      VHUIUVEUVNUUIUUKUVHUVEUVNUUIVPUUKUVHUVEUIZUIZUUFUVKUOZUUHUMZUVNUWCUPUSZUU
      IUWBUVKUUGUMUWDUWBUVBKUUKUVHUVCUVDWCWDUVKUUGUUFWEVCUWBGUVBTZUVNUWEVPUWBUW
      FUVCUUKUVHUVCUVDWFUUAUWFUVCWGAUUDUWAGUVBMWHWIWJUVMUWEBGUVBUVIGVGZUVLUWCUP
      UWGUVJUUFUVKUVIGIWKWNVSWLVCUWCUUHWMWOWPWQWRWSWTXAXBXCUUBUUEUUIUUDUUIUAVLZ
      UUHTZUAXDUUBUUEUIZUUDUAUUHXEUWJUWIUUDUAUWIUWHUUFTZUWHUUGTZUIZUWJUUDUWHUUF
      UUGXFUUBUUEUWMUUDUUBUUEUWMUIZUIZUUDUUNGUBVLZTUWPKUMUIUBJVMZUWOKMUULUUBUUE
      UWMXGZAUUTUUAUWNUVAVIZXHUWOBCUCDEUBFGDVLZIULZUDVLZUNZUOZUPUSZUDUEXIUFUEVL
      ZUGMUGVLZIULZUFVLZUNZUOZXJZXJZXKZUWHUJZXLZXMXNZXOUQZVMZDMXPUWHUHHIUXQJKLM
      UEAMLTUUAUWNNVIAMUVGUNUPUJXQIXRUUAUWNOVIUWOAUVIMTZEVLZUVJTZUWTUVJTYAUVJUY
      AUWTUOUNUOUPUSAUUAUWNXSZPVJQUWOAUXTUYBUIZUVIUYATUYCRVJUWOAUYDUVBIULZUYAUN
      UOUPUSCFVLVOFUVJVMUYCSVJAUUAUWNXTZUWRUUBUUEUWKUWLWFUWOUWHKUUBUUEUWKUWLWCY
      BUXPUEXIUCUXFBMUVJUCVLZUNZUOZXJZXJZXKZUXOXLZXMUXNUYLVGUXPUYMVGUEXIUXMUYKU
      FUCUXFUXLUYJUFUCWBZUXLBMUVJUXJUOZXJUYJUGBMUXKUYOUGBWBUXHUVJUXJUXGUVIIWKWN
      YCUYNBMUYOUYIUYNUXJUYHUVJUXIUYGVQVRYDYEYCYFUXOUXNUYLYGYKYHUXSUYEUHVLZUNZU
      OZUPUSZUHUXRVMZDCMUXSUXAUYQUOZUPUSZUHUXRVMDCWBZUYTUXEVUBUDUHUXRUDUHWBZUXD
      VUAUPVUDUXCUYQUXAUXBUYPVQVRVSYIVUCVUBUYSUHUXRVUCVUAUYRUPVUCUXAUYEUYQUWTUV
      BIWKWNVSYJYLYMYNUWOUUMGUULTUUDUUNUWQUIWGAUUMUUAUWNUUQVIUWOGMUULUYFUWSYOGU
      BJKUULUUSYPYQYTWPWSYRWSWRYS $.

    $( The topology generated by a neighborhood base is unique.  (Contributed
       by Jeff Hankins, 16-Sep-2009.)  (Proof shortened by Mario Carneiro,
       11-Sep-2015.) $)
    neibastop3 $p |- ( ph -> E! j e. ( TopOn ` X )
      A. x e. X ( ( nei ` j ) ` { x } ) =
        { n e. ~P X | ( ( F ` x ) i^i ~P n ) =/= (/) } ) $=
      ( wcel vz cv ctopon cfv csn cnei cpw cin c0 wne crab wceq wral wa wreu wi
      weu wal neibastop1 cab wss neibastop2 velpw anbi1i bitr4di eqabdv eqtr4di
      df-rab ralrimiva sneq fveq2d fveq2 ineq1d neeq1d rabbidv eqeq12d cbvralvw
      sylibr cuni toponuni eqimss2 syl sspwuni ad2antlr sseqin2 sylib wrex ctop
      topontop ad3antlr eltop2 ssralv adantl simprr eleq2d sseq2d biimpa sylan2
      elpwi sselda adantrr adantr eqid isneip baibd syl21anc pweq ineq2d elrab3
      wb 3bitr3d expr ralimdva syld imp an32s ralbi bitrd rabbi2dva eqtr3d expl
      alrimiv eleq1 fveq1d eqeq1d ralbidv anbi12d eqeu syl121anc df-reu ) AGUBZ
      MUCUDZTZBUBZUEZYKUFUDZUDZYNJUDZHUBZUGZUHZUIUJZHMUGZUKZULZBMUMZUNZGUQZUUFG
      YLUOAKYLTZUUIYOKUFUDZUDZUUDULZBMUMZUUGYKKULZUPZGURUUHABDEIJKLMNOPQUSZUUPA
      UAUBZUEZUUJUDZUUQJUDZYTUHZUIUJZHUUCUKZULZUAMUMUUMAUVDUAMAUUQMTUNZUUSYSUUC
      TZUVBUNZHUTUVCUVEUVGHUUSUVEYSUUSTYSMVAZUVBUNUVGABCDEFUUQIJKYSLMNOPQRSVBUV
      FUVHUVBHMVCVDVEVFUVBHUUCVHVGVIUULUVDBUAMYNUUQULZUUKUUSUUDUVCUVIYOUURUUJYN
      UUQVJVKUVIUUBUVBHUUCUVIUUAUVAUIUVIYRUUTYTYNUUQJVLVMVNVOVPVQVRAUUOGAYMUUFU
      UNAYMUNZUUFUNZUUCYKUHZYKKUVKYKUUCVAZUVLYKULYMUVMAUUFYMYKVSZMVAZUVMYMMUVNU
      LZUVOMYKVTZUVNMWAWBYKMWCVRWDYKUUCWEWFUVKUVLYRIUBZUGZUHZUIUJZBUVRUMZIUUCUK
      KUVKUWBIUUCYKUVKUVRUUCTZUNZUVRYKTZYNUUQTUUQUVRVAUNUAYKWGZBUVRUMZUWBUWDYKW
      HTZUWEUWGXJYMUWHAUUFUWCMYKWIZWJBUAUVRYKWKWBUWDUWFUWAXJZBUVRUMZUWGUWBXJUVJ
      UWCUUFUWKUVJUWCUNZUUFUWKUWLUUFUUEBUVRUMZUWKUWCUUFUWMUPZUVJUWCUVRMVAZUWNUV
      RMWSZUUEBUVRMWLWBWMUWLUUEUWJBUVRUWLYNUVRTZUUEUWJUWLUWQUUEUNZUNZUVRYQTZUVR
      UUDTZUWFUWAUWSYQUUDUVRUWLUWQUUEWNWOUWSUWHYNUVNTZUVRUVNVAZUWTUWFXJYMUWHAUW
      CUWRUWIWJUWLUWQUXBUUEUWLUVRUVNYNUWCUVJUWOUXCUWPUVJUWOUXCUVJMUVNUVRYMUVPAU
      VQWMWPWQWRZWTXAUWLUXCUWRUXDXBUWHUXBUNUWTUXCUWFYNUAYKUVRUVNUVNXCXDXEXFUWCU
      XAUWAXJUVJUWRUUBUWAHUVRUUCYSUVRULZUUAUVTUIUXEYTUVSYRYSUVRXGXHVNXIWDXKXLXM
      XNXOXPUWFUWABUVRXQWBXRXSQVGXTYAYBUUGUUIUUMUNGKYLUUNYMUUIUUFUUMYKKYLYCUUNU
      UEUULBMUUNYQUUKUUDUUNYOYPUUJYKKUFVLYDYEYFYGYHYIUUFGYLYJVR $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Lattice structure of topologies
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d t y A $.  $d j k t x y S $.  $d j k t x V $.  $d j k t x y X $.
    $d t x T $.
    $( The meet of a collection of topologies on ` X ` is again a topology on
       ` X ` .  (Contributed by Jeff Hankins, 5-Oct-2009.)  (Proof shortened by
       Mario Carneiro, 12-Sep-2015.) $)
    topmtcl $p |- ( ( X e. V /\ S C_ ( TopOn ` X ) ) ->
      ( ~P X i^i |^| S ) e. ( TopOn ` X ) ) $=
      ( wcel ctopon cfv cpw cmre wss cint cin toponmre mrerintcl sylan ) CBDCEF
      ZCGZHFDAOIPAJKODCBLOAPMN $.

    $( Two equivalent formulations of the meet of a collection of topologies.
       (Contributed by Jeff Hankins, 4-Oct-2009.)  (Proof shortened by Mario
       Carneiro, 12-Sep-2015.) $)
    topmeet $p |- ( ( X e. V /\ S C_ ( TopOn ` X ) ) ->
      ( ~P X i^i |^| S ) = U. { k e. ( TopOn ` X ) | A. j e. S k C_ j } ) $=
      ( wcel ctopon cfv wss wa cpw cint cin wral cuni wceq sylibr syl sspwuni
      cv crab topmtcl inss2 intss1 sstrid rgen sseq1 ralbidv elrab mpbiran2 w3a
      elssuni toponuni eqimss2 3ad2ant2 simp3 ssint ssind velpw rabssdv sylib
      eqssd ) EDFAEGHZIJZEKZALZMZCTZBTZIZBANZCVCUAZOZVDVGVLFZVGVMIVDVGVCFZVNADE
      UBVNVOVGVIIZBANZVPBAVIAFVGVFVIVEVFUCVIAUDUEUFVKVQCVGVCVHVGPVJVPBAVHVGVIUG
      UHUIUJQVGVLULRVDVLVGKZIVMVGIVDVKCVCVRVDVHVCFZVKUKZVHVGIVHVRFVTVHVEVFVSVDV
      HVEIZVKVSVHOZEIZWAVSEWBPWCEVHUMWBEUNRVHESQUOVTVKVHVFIVDVSVKUPBVHAUQQURCVG
      USQUTVLVGSVAVB $.

    $( Two equivalent formulations of the join of a collection of topologies.
       (Contributed by Jeff Hankins, 6-Oct-2009.)  (Proof shortened by Mario
       Carneiro, 12-Sep-2015.) $)
    topjoin $p |- ( ( X e. V /\ S C_ ( TopOn ` X ) ) ->
      ( topGen ` ( fi ` ( { X } u. U. S ) ) ) =
        |^| { k e. ( TopOn ` X ) | A. j e. S j C_ k } ) $=
      ( wcel ctopon cfv wss wa cuni cun wral sylibr wceq syl sspwuni sstrdi cvv
      sylib csn cfi ctg cv crab cint wi topontop ad2antrl toponmax snssd simprr
      ctop unissb unssd syl2anc expr ralrimiva ssintrab ctb fibas tgtopon ax-mp
      tgfiss uniun unisng adantr eqtr2id cpw simpr toponuni eqimss2 velpw ssriv
      uneq1d ssequn2 snex fvex adantl uniexd unexg sylancr fiuni 3eqtr3d fveq2d
      ssex eleqtrrid elssuni ssun2 ssfii sylan9ssr bastg sseq2 ralbidv sylanbrc
      elrab intss1 eqssd ) EDFZAEGHZIZJZEUAZAKZLZUBHZUCHZBUDZCUDZIZBAMZCWTUEZUF
      ZXBXKXGXIIZUGZCWTMXGXMIXBXOCWTXBXIWTFZXKXNXBXPXKJJZXIUMFZXEXIIXNXPXRXBXKE
      XIUHUIXQXCXDXIXQEXIXPEXIFXBXKEXIUJUIUKXQXKXDXIIXBXPXKULBAXIUNNUOXEXIVDUPU
      QURXKCXGWTUSNXBXGXLFZXMXGIXBXGWTFXHXGIZBAMZXSXBXGXFKZGHZWTXFUTFZXGYCFXEVA
      ZXFVBVCXBEYBGXBEXDKZLZXEKZEYBXBYHXCKZYFLYGXCXDVEXBYIEYFWSYIEOXAEDVFVGVOVH
      XBYFEIZYGEOXBXDEVIZIZYJXBAYKVIZIYLXBAWTYMWSXAVJCWTYMXPXIYKIZXIYMFXPXIKZEI
      ZYNXPEYOOYPEXIVKYOEVLPXIEQNCYKVMNVNRAYKQTXDEQTYFEVPTXBXESFZYHYBOXBXCSFXDS
      FYQEVQXBASXAASFWSAWTEGVRWFVSVTXCXDSSWAWBZXESWCPWDWEWGXBXTBAXBXHAFZJXHXFXG
      YSXBXHXEXFYSXHXDXEXHAWHXDXCWIRXBYQXEXFIYRXESWJPWKYDXFXGIYEXFUTWLVCRURXKYA
      CXGWTXIXGOXJXTBAXIXGXHWMWNWPWOXGXLWQPWR $.

    $( The meet of a collection of equivalence classes of covers with respect
       to fineness.  (Contributed by Jeff Hankins, 5-Oct-2009.)  (Proof
       shortened by Mario Carneiro, 12-Sep-2015.) $)
    fnemeet1 $p |- ( ( X e. V /\ A. y e. S X = U. y /\ A e. S ) ->
      ( ~P X i^i |^|_ t e. S ( topGen ` t ) ) Fne A ) $=
      ( wcel cv cuni wceq wral ctg cfv cfne wss unitg unieq eqeq2d syl 3ad2ant3
      w3a cpw ciin cin c0 wne wa adantl rspccva 3ad2antl2 eqtr4d eqimss sspwuni
      sylibr ralrimiva ne0i riinn0 syl2anc wrex simp3 ssid fveq2 sseq1d sylancl
      rspcev iinss unissd sseqtrd 3adant1 adantr eqtr3d simpr eltg3i eqeltrd wb
      wbr cvv uniexg eliin mpbird elssuni eqssd eqid isfne4 sylanbrc eqbrtrd )
      FEGZFAHZIZJZADKZCDGZUAZFUBZBDBHZLMZUCZUDZWQCNWMWPWNOZBDKDUEUFZWRWQJWMWSBD
      WMWODGZUGZWPIZFOZWSXBXCFJXDXBXCWOIZFXAXCXEJWMWODPUHWKWGXAFXEJZWLWJXFAWODW
      HWOJWIXEFWHWOQRUIUJZUKXCFULSWPFUMUNUOWLWGWTWKDCUPTBWNWPDUQURWMWQIZCIZJWQC
      LMZOZWQCNVPWMXHXIWMXHXJIZXIWMWQXJWMWPXJOZBDUSZXKWMWLXJXJOZXNWGWKWLUTXJVAX
      MXOBCDWOCJWPXJXJWOCLVBVCVEVDBDWPXJVFSZVGWLWGXLXIJWKCDPTVHWMXIWQGZXIXHOWMX
      QXIWPGZBDKZWMXRBDXBXIXEWPXBFXIXEWMFXIJZXAWKWLXTWGWJXTACDWHCJWIXIFWHCQRUIV
      IVJXGVKXBXAWOWOOXEWPGWMXAVLWOVAWOWODVMVDVNUOWMXIVQGZXQXSVOWLWGYAWKCDVRTBX
      IDWPVQVSSVTXIWQWASWBXPWQCXHXIXHWCXIWCWDWEWF $.

    $( The meet of equivalence classes under the fineness relation-part two.
       (Contributed by Jeff Hankins, 6-Oct-2009.)  (Proof shortened by Mario
       Carneiro, 12-Sep-2015.) $)
    fnemeet2 $p |- ( ( X e. V /\ A. y e. S X = U. y ) ->
      ( T Fne ( ~P X i^i |^|_ t e. S ( topGen ` t ) ) <->
        ( X = U. T /\ A. x e. S T Fne x ) ) ) $=
      ( wcel cv cuni wceq wral wa cfne wbr c0 eqid syl wss cvv cpw ctg cfv ciin
      cin wi riin0 unieqd unipw eqtr2di a1i wne wex n0 w3a unieq eqeq2d rspccva
      3adant1 fnemeet1 fnebas eqtr4d 3expia biimtrid pm2.61dne adantr adantl ex
      exlimdv fnetr expcom 3expa ralrimdva jcad simprl eqimss2 ad2antrl sspwuni
      eqtr3d sylibr breq2 cbvralvw fnetg sylbi ad2antll ssiin ssind pwexg bastg
      ralimi inex1g ad2antrr sstrd isfne4 sylanbrc impbid ) GFHZGBIZJZKZBDLZMZE
      GUAZCDCIZUBUCZUDZUEZNOZGEJZKZEAIZNOZADLZMZXBXHXJXMXBXHXJXBXHMGXGJZXIXBGXO
      KZXHXBXPDPDPKZXPUFXBXQXOXCJGXQXGXCCXCXEDUGUHGUIUJUKDPULXKDHZAUMXBXPADUNXB
      XRXPAWQXAXRXPWQXAXRUOZGXKJZXOXAXRGXTKZWQWTYABXKDWRXKKWSXTGWRXKUPUQURUSXSX
      GXKNOZXOXTKBCXKDFGUTZXGXKXOXTXOQZXTQVARVBVCVIVDVEZVFXHXIXOKZXBEXGXIXOXIQZ
      YDVAVGVBVHXBXHXLADWQXAXRXHXLUFZXSYBYHYCXHYBXLEXGXKVJVKRVLVMVNXBXNXHXBXNMZ
      YFEXGUBUCZSXHYIGXIXOXBXJXMVOXBXPXNYEVFVSYIEXGYJYIEXCXFYIXIGSZEXCSXJYKXBXM
      XIGVPVQEGVRVTYIEXESZCDLZEXFSXMYMXBXJXMEXDNOZCDLYMXLYNACDXKXDENWAWBYNYLCDE
      XDWCWJWDWECDXEEWFVTWGYIXGTHZXGYJSWQYOXAXNWQXCTHYOGFWHXCXFTWKRWLXGTWIRWMEX
      GXIXOYGYDWNWOVHWP $.

    $( Join of equivalence classes under the fineness relation-part one.
       (Contributed by Jeff Hankins, 8-Oct-2009.)  (Proof shortened by Mario
       Carneiro, 12-Sep-2015.) $)
    fnejoin1 $p |- ( ( X e. V /\ A. y e. S X = U. y /\ A e. S ) ->
      A Fne if ( S = (/) , { X } , U. S ) ) $=
      ( wcel cv cuni wceq wral w3a c0 cfne wss 3ad2ant3 sspwuni sylibr cvv eqid
      syl csn cif ctg cfv wbr elssuni unissd cpw eqimss2 ralimi 3ad2ant2 unissb
      sylib unieq eqeq2d rspccva 3adant1 eqssd pwexg 3ad2ant1 ssexd bastg sstrd
      sseqtrd isfne4 sylanbrc wne ne0i ifnefalse breqtrrd ) EDFZEAGZHZIZACJZBCF
      ZKZBCHZCLIEUAZVRUBZMVQBHZVRHZIBVRUCUDZNBVRMUEVQWAWBVQBVRVPVKBVRNVOBCUFOZU
      GVQWBEWAVQVREUHZNZWBENVQVLWENZACJZWFVOVKWHVPVNWGACVNVMENWGVMEUIVLEPQUJUKA
      CWEULQZVREPUMVOVPEWAIZVKVNWJABCVLBIVMWAEVLBUNUOUPUQVDURVQBVRWCWDVQVRRFVRW
      CNVQVRWERVKVOWERFVPEDUSUTWIVAVRRVBTVCBVRWAWBWASWBSVEVFVQCLVGZVTVRIVPVKWKV
      OCBVHOCLVSVRVITVJ $.

    $( Join of equivalence classes under the fineness relation-part two.
       (Contributed by Jeff Hankins, 8-Oct-2009.)  (Proof shortened by Mario
       Carneiro, 12-Sep-2015.) $)
    fnejoin2 $p |- ( ( X e. V /\ A. y e. S X = U. y ) ->
      ( if ( S = (/) , { X } , U. S ) Fne T <->
        ( X = U. T /\ A. x e. S x Fne T ) ) ) $=
      ( wcel cuni wceq wral wa c0 cfne wbr adantr eqid syl ex wss cvv cv unisng
      csn cif eqcomd iftrue unieqd eqeq2d syl5ibrcom wne wex n0 rspccva 3adant1
      unieq fnejoin1 fnebas eqtrd 3expia exlimdv biimtrid pm2.61dne sylan9eq wi
      w3a fnetr 3expa ralrimdva jcad simprl eqtr3d sseq1 elex ad2antrr eqeltrrd
      ctg cfv uniexb sylibr ssid eltg3i sylancl eqeltrd snssd wn simplrr ralimi
      fnetg unissb ifbothda isfne4 sylanbrc impbid ) FEGZFBUAZHZIZBCJZKZCLIZFUC
      ZCHZUDZDMNZFDHZIZAUAZDMNZACJZKZWSXDXFXIWSXDXFWSXDFXCHZXEWSFXKIZCLWSXLWTFX
      AHZIZWNXNWRWNXMFFEUBUEOWTXKXMFWTXCXAWTXAXBUFUGUHUICLUJXGCGZAUKWSXLACULWSX
      OXLAWNWRXOXLWNWRXOVEZFXGHZXKWRXOFXQIZWNWQXRBXGCWOXGIWPXQFWOXGUOUHUMUNXPXG
      XCMNZXQXKIBXGCEFUPZXGXCXQXKXQPXKPZUQQURUSUTVAVBZXCDXKXEYAXEPZUQVCRWSXDXHA
      CWNWRXOXDXHVDZXPXSYDXTXSXDXHXGXCDVFRQVGVHVIWSXJXDWSXJKZXKXEIXCDVPVQZSZXDY
      EFXKXEWSXLXJYBOWSXFXIVJZVKWTXAYFSZXBYFSZYGYEXAXBXAXCYFVLXBXCYFVLYEYIWTYEF
      YFYEFXEYFYHYEDTGZDDSXEYFGYEXETGYKYEFXETYHWNFTGWRXJFEVMVNVODVRVSDVTDDTWAWB
      WCWDOYEWTWEZKZXGYFSZACJZYJYMXIYOWSXFXIYLWFXHYNACXGDWHWGQACYFWIVSWJXCDXKXE
      YAYCWKWLRWM $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Filter bases
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d t x B $.  $d t x F $.  $d t x X $.
    $( Minimality property of a generated filter: every filter that contains
       ` B ` contains its generated filter.  (Contributed by Jeff Hankins,
       5-Sep-2009.)  (Revised by Mario Carneiro, 7-Aug-2015.) $)
    fgmin $p |- ( ( B e. ( fBas ` X ) /\ F e. ( Fil ` X ) ) ->
        ( B C_ F <-> ( X filGen B ) C_ F ) ) $=
      ( vt vx cfbas cfv wcel cfil wa wss cfg co cv wrex wb elfg adantr ssrexv
      wi adantl filss 3exp2 com34 rexlimdv ad2antlr syld com23 impd sylbid ssfg
      ssrdv ex sstr2 syl impbid ) ACFGHZBCIGHZJZABKZCALMZBKZUSUTVBUSUTJZDVABVCD
      NZVAHZVDCKZENZVDKZEAOZJZVDBHZUSVEVJPZUTUQVLUREVDACQRRVCVFVIVKVCVIVFVKVCVI
      VHEBOZVFVKTZUTVIVMTUSVHEABSUAURVMVNTUQUTURVHVNEBURVGBHZVFVHVKURVOVFVHVKVG
      VDBCUBUCUDUEUFUGUHUIUJULUMUQVBUTTZURUQAVAKVPACUKAVABUNUORUP $.
  $}

  ${
    $d t u x z J $.  $d t u x z S $.  $d t u x z X $.
    neifg.1 $e |- X = U. J $.
    $( The neighborhood filter of a nonempty set is generated by its open
       supersets.  See comments for ~ opnfbas .  (Contributed by Jeff Hankins,
       3-Sep-2009.) $)
    neifg $p |- ( ( J e. Top /\ S C_ X /\ S =/= (/) ) ->
        ( X filGen { x e. J | S C_ x } ) = ( ( nei ` J ) ` S ) ) $=
      ( vt vu vz wcel wss c0 wne cv crab cpw cin cfv wa wex wb ctop w3a co cnei
      cfg cfbas wceq opnfbas fgval syl pweq ineq2d neeq1d elrab velpw a1i sseq2
      n0 elin anbi12i bitri exbii anbi12d wrex anass df-rex bitr4i anbi2i isnei
      3adant3 bitr4id bitrd bitrid eqrdv eqtrd ) CUAIZBDJZBKLZUBZDBAMZJZACNZUEU
      CZWBFMZOZPZKLZFDOZNZBCUDQQZVSWBDUFQIWCWIUGABCDEUHFWBDUIUJVSGWIWJGMZWIIWKW
      HIZWBWKOZPZKLZRZVSWKWJIZWGWOFWKWHWDWKUGZWFWNKWRWEWMWBWDWKUKULUMUNVSWPWKDJ
      ZHMZCIZBWTJZRZWTWKJZRZHSZRZWQVSWLWSWOXFWLWSTVSGDUOUPWOXFTVSWOWTWNIZHSXFHW
      NURXHXEHXHWTWBIZWTWMIZRXEWTWBWMUSXIXCXJXDWAXBAWTCVTWTBUQUNHWKUOUTVAVBVAUP
      VCVSXGWSXBXDRZHCVDZRZWQXFXLWSXFXAXKRZHSXLXEXNHXAXBXDVEVBXKHCVFVGVHVPVQWQX
      MTVRBHCWKDEVIVJVKVLVMVNVO $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Directed sets, nets
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d d x D $.  $d x X $.  $d x A $.
    tailfval.1 $e |- X = dom D $.
    $( The tail function for a directed set.  (Contributed by Jeff Hankins,
       25-Nov-2009.)  (Revised by Mario Carneiro, 24-Nov-2013.) $)
    tailfval $p |- ( D e. DirRel -> ( tail ` D ) =
                     ( x e. X |-> ( D " { x } ) ) ) $=
      ( vd cdir wcel ctail cfv cuni cv csn cima cmpt cvv wceq uniexg 3syl unieq
      mptexg unieqd imaeq1 mpteq12dv df-tail fvmptg mpdan dirdm eqtr2id mpteq1d
      cdm eqtrd ) BFGZBHIZABJZJZBAKLZMZNZACUQNULUROGZUMURPULUNOGUOOGUSBFQUNOQAU
      OUQOTREBAEKZJZJZUTUPMZNURFOHUTBPZAVBVCUOUQVDVAUNUTBSUAUTBUPUBUCAEUDUEUFUL
      AUOCUQULCBUJUODBUGUHUIUK $.

    $( The tail of an element in a directed set.  (Contributed by Jeff Hankins,
       25-Nov-2009.)  (Revised by Mario Carneiro, 24-Nov-2013.) $)
    tailval $p |- ( ( D e. DirRel /\ A e. X ) ->
                   ( ( tail ` D ) ` A ) = ( D " { A } ) ) $=
      ( vx cdir wcel wa ctail cfv csn cima cmpt wceq tailfval fveq1d adantr cvv
      cv id imaexg sneq imaeq2d eqid fvmptg syl2anr eqtrd ) BFGZACGZHABIJZJZAEC
      BESZKZLZMZJZBAKZLZUHUKUPNUIUHAUJUOEBCDOPQUIUIURRGUPURNUHUITBUQFUAEAUNURCR
      UOULANUMUQBULAUBUCUOUDUEUFUG $.

    $( An element of a tail.  (Contributed by Jeff Hankins, 25-Nov-2009.)
       (Revised by Mario Carneiro, 24-Nov-2013.) $)
    eltail $p |- ( ( D e. DirRel /\ A e. X /\ B e. C ) ->
                   ( B e. ( ( tail ` D ) ` A ) <-> A D B ) ) $=
      ( cdir wcel w3a ctail cfv csn cima wbr wb wa tailval eleq2d 3adant3 cop
      elimasng df-br bitr4di 3adant1 bitrd ) DGHZAEHZBCHZIBADJKKZHZBDALMZHZABDN
      ZUFUGUJULOUHUFUGPUIUKBADEFQRSUGUHULUMOUFUGUHPULABTDHUMDABECUAABDUBUCUDUE
      $.
  $}

  ${
    $d x D $.  $d x X $.
    tailf.1 $e |- X = dom D $.
    $( The tail function of a directed set sends its elements to its subsets.
       (Contributed by Jeff Hankins, 25-Nov-2009.)  (Revised by Mario Carneiro,
       24-Nov-2013.) $)
    tailf $p |- ( D e. DirRel -> ( tail ` D ) : X --> ~P X ) $=
      ( vx cdir wcel cpw ctail cfv wf cv csn cima cmpt wral wss cuni cvv mpbird
      sstri crn imassrn cdm cun ssun2 dmrnssfld dirdm eqtr2id sseqtrid wb dmexg
      eqeltrid elpw2g syl ralrimivw eqid fmpt sylib tailfval feq1d ) AEFZBBGZAH
      IZJBVBDBADKLZMZNZJZVAVEVBFZDBOVGVAVHDBVAVHVEBPZVAAQQZVEBVEAUAZVJAVDUBVKAU
      CZVKUDVJVKVLUEAUFTTVABVLVJCAUGUHUIVABRFVHVIUJVABVLRCAEUKULVEBRUMUNSUODBVB
      VEVFVFUPUQURVABVBVCVFDABCUSUTS $.
  $}

  ${
    tailini.1 $e |- X = dom D $.
    $( A tail contains its initial element.  (Contributed by Jeff Hankins,
       25-Nov-2009.) $)
    tailini $p |- ( ( D e. DirRel /\ A e. X ) -> A e. ( ( tail ` D ) ` A ) ) $=
      ( cdir wcel wa ctail cfv wbr dirref wb eltail 3anidm23 mpbird ) BEFZACFZG
      AABHIIFZAABJZABCDKPQRSLAACBCDMNO $.
  $}

  ${
    $d u v w x y z D $.  $d u v w x y z X $.
    tailfb.1 $e |- X = dom D $.
    $( The collection of tails of a directed set is a filter base.
       (Contributed by Jeff Hankins, 25-Nov-2009.)  (Revised by Mario Carneiro,
       8-Aug-2015.) $)
    tailfb $p |- ( ( D e. DirRel /\ X =/= (/) )
          -> ran ( tail ` D ) e. ( fBas ` X ) ) $=
      ( vz vx vy vu vv wcel c0 wa cfv wss cv wrex adantr wi wb wbr cvv cdir wne
      vw ctail crn cfbas cpw wnel cin wral w3a tailf wex n0 wf wfn ffn fnfvelrn
      frnd ex 3syl ne0i syl6 exlimdv biimtrid imp wn tailini n0i nrexdv fvelrnb
      wceq mtbird df-nel sylibr anbi12d reeanv dirge 3expb sylan ad2ant2r dirtr
      syl exp32 elvd com23 ad2ant2rl anim12d expr eltail mp3an3 adantrr adantrl
      impr vex 3imtr4d elin imbitrrdi ssrdv sseq1 rspcev rexlimddv ineq1 sseq2d
      syl2anc rexbidv ineq2 sylan9bb syl5ibcom rexlimdvva biimtrrid sylbid 3jca
      ralrimivv cdm dmexg eqeltrid isfbas2 mpbir2and ) AUAIZBJUBZKZAUDLZUEZBUFL
      IZYDBUGZMZYDJUBZJYDUHZDNZENZFNZUIZMZDYDOZFYDUJEYDUJZUKZXTYGYAXTBYFYCABCUL
      ZUSPYBYHYIYPXTYAYHYAYKBIZEUMXTYHEBUNXTYSYHEXTYSYKYCLZYDIZYHXTBYFYCUOZYCBU
      PZYSUUAQYRBYFYCUQZUUCYSUUABYKYCURUTVAYDYTVBVCVDVEVFYBJYDIZVGYIYBUUEYTJVLZ
      EBOZXTUUGVGYAXTUUFEBXTYSKYKYTIUUFVGYKABCVHYTYKVIWCVJPXTUUEUUGRZYAXTUUBUUC
      UUHYRUUDEBJYCVKVAPVMJYDVNVOYBYOEFYDYDXTYKYDIZYLYDIZKZYOQYAXTUUKGNZYCLZYKV
      LZGBOZHNZYCLZYLVLZHBOZKZYOXTUUBUUCUUKUUTRYRUUDUUCUUIUUOUUJUUSGBYKYCVKHBYL
      YCVKVPVAUUTUUNUURKZHBOGBOXTYOUUNUURGHBBVQXTUVAYOGHBBXTUULBIZUUPBIZKZKZYJU
      UMUUQUIZMZDYDOZUVAYOUVEUULUCNZASZUUPUVIASZKZUVHUCBXTUVBUVCUVLUCBOUCUULUUP
      ABCVRVSUVEUVIBIZUVLKZKZUVIYCLZYDIZUVPUVFMZUVHXTUVMUVQUVDUVLXTUUCUVMUVQXTU
      UBUUCYRUUDWCBUVIYCURVTWAUVOEUVPUVFUVOYKUVPIZYKUUMIZYKUUQIZKZYKUVFIUVOUVIY
      KASZUULYKASZUUPYKASZKZUVSUWBUVEUVMUVLUWCUWFQUVEUVMKUWCUVLUWFUVEUVMUWCUVLU
      WFQUVEUVMUWCKKUVJUWDUVKUWEXTUWCUVJUWDQZUVDUVMXTUWCUWGXTUVJUWCUWDXTUVJUWCU
      WDQQEXTYKTIZKZUVJUWCUWDUULUVIYKATWBWDWEWFVFWGXTUWCUVKUWEQZUVDUVMXTUWCUWJX
      TUVKUWCUWEXTUVKUWCUWEQQEUWIUVKUWCUWEUUPUVIYKATWBWDWEWFVFWGWHWIWFWNXTUVMUV
      SUWCRZUVDUVLXTUVMUWHUWKEWOZUVIYKTABCWJWKWAUVEUWBUWFRUVNUVEUVTUWDUWAUWEXTU
      VBUVTUWDRZUVCXTUVBUWHUWMUWLUULYKTABCWJWKWLXTUVCUWAUWERZUVBXTUVCUWHUWNUWLU
      UPYKTABCWJWKWMVPPWPYKUUMUUQWQWRWSUVGUVRDUVPYDYJUVPUVFWTXAXEXBUUNUVHYJYKUU
      QUIZMZDYDOUURYOUUNUVGUWPDYDUUNUVFUWOYJUUMYKUUQXCXDXFUURUWPYNDYDUURUWOYMYJ
      UUQYLYKXGXDXFXHXIXJXKXLPXNXMYBBTIZYEYGYQKRXTUWQYAXTBAXOTCAUAXPXQPEFDTBYDX
      RWCXS $.
  $}

  ${
    $d x y A $.  $d d f k m n t u v w x y z F $.  $d d f m t u v w x y z H $.
    $d x y B $.  $d d f t u v w z D $.  $d d f n t u v z X $.
    ${
      filnet.h $e |- H = U_ n e. F ( { n } X. n ) $.
      filnet.d $e |- D = { <. x , y >. |
          ( ( x e. H /\ y e. H ) /\ ( 1st ` y ) C_ ( 1st ` x ) ) } $.
      ${
        filnetlem1.a $e |- A e. _V $.
        filnetlem1.b $e |- B e. _V $.
        $( Lemma for ~ filnet .  Change variables.  (Contributed by Jeff
           Hankins, 13-Dec-2009.)  (Revised by Mario Carneiro, 8-Aug-2015.) $)
        filnetlem1 $p |- ( A D B <-> ( ( A e. H /\ B e. H ) /\
            ( 1st ` B ) C_ ( 1st ` A ) ) ) $=
          ( cv c1st cfv wss wceq fveq2 sseq2d sseq1d sylan9bb brab2a ) BMZNOZAM
          ZNOZPZDNOZCNOZPZABCDHHEUECQZUGUDUIPUCDQZUJUKUFUIUDUECNRSULUDUHUIUCDNR
          TUAJUB $.
      $}

      $( Lemma for ~ filnet .  The field of the direction.  (Contributed by
         Jeff Hankins, 13-Dec-2009.)  (Revised by Mario Carneiro,
         8-Aug-2015.) $)
      filnetlem2 $p |- ( ( _I |` H ) C_ D /\ D C_ ( H X. H ) ) $=
        ( vz cid cres wss cxp cv wbr idref wcel wa c1st cfv ssid vex filnetlem1
        mpbiran2 biimpri anidms mprgbir copab opabssxp eqsstri pm3.2i ) JFKCLZC
        FFMZLULINZUNCOZIFIFCPUNFQZUOUOUPUPRZUOUQUNSTZURLURUAABUNUNCDEFGHIUBZUSU
        CUDUEUFUGCANZFQBNZFQRVASTUTSTLZRABUHUMHVBABFFUIUJUK $.

      $( Lemma for ~ filnet .  (Contributed by Jeff Hankins, 13-Dec-2009.)
         (Revised by Mario Carneiro, 8-Aug-2015.) $)
      filnetlem3 $p |- ( H = U. U. D /\
        ( F e. ( Fil ` X ) -> ( H C_ ( F X. X ) /\ D e. DirRel ) ) ) $=
        ( vv vw vz cfv wcel wss wa cv c1st wbr cvv vu cuni wceq cfil cxp wi cdm
        cdir crn cun cid cres dmresi filnetlem2 dmss ax-mp eqsstrri ssun1 sstri
        simpli dmrnssfld simpri uniss mp2b unixpss unidm sseqtri eqssi csn ciun
        wral filelss xpss2 syl ralrimiva iunxpconst sseqtrdi eqsstrid wrel ccom
        ss2iun ccnv a1i relopabiv jctil wex c0 simpl adantr simprl sseldd xp1st
        cin wne simprr filinn0 syl3anc n0 sylib filin simpr opeliunxp2 sylanbrc
        cop id eleqtrrdi fvex inex1 vex op1st inss1 eqsstri filnetlem1 mpbiran2
        opex inss2 breq2 anbi12d spcev syl2anc exlimddv ralrimivva codir sylibr
        wal simplbi simpld simprd anim12i simprbi sylan9ssr ax-gen gen2 cotr wb
        mpbir filtop xpexg mpdan ssexd xpexd ssexg sylancr mpbir2and jca pm3.2i
        isdir ) FCUBZUBZUCEGUDMZNZFEGUEZOZCUHNZPUFFUUIFCUGZCUIZUJZUUIFUUOUUQFUK
        FULZUGZUUOFUMUURCOZUUSUUOOUUTCFFUEZOZABCDEFHIUNZUTZUURCUOUPUQUUOUUPURUS
        CVAUSUUIUVAUBZUBZFUVBUUHUVEOUUIUVFOUUTUVBUVCVBZCUVAVCUUHUVEVCVDUVFFFUJF
        FFVEFVFVGUSVHZUUKUUMUUNUUKFDEDQZVIZUVIUEZVJZUULHUUKUVLDEUVJGUEZVJZUULUU
        KUVKUVMOZDEVKUVLUVNOUUKUVODEUUKUVIENPUVIGOUVOUVIEGVLUVIGUVJVMVNVODEUVKU
        VMWAVNDEGVPVQVRZUUKUUNCVSZUUTPZCCVTCOZUVACWBCVTOZPZUUKUUTUVQUUTUUKUVDWC
        AQZFNBQZFNPUWCRMUWBRMOPABCIWDWEUUKUVTUVSUUKJQZKQZCSZLQZUWECSZPZKWFZLFVK
        JFVKUVTUUKUWJJLFFUUKUWDFNZUWGFNZPZPZUAQZUWDRMZUWGRMZWMZNZUWJUAUWNUWRWGW
        NZUWSUAWFUWNUUKUWPENZUWQENZUWTUUKUWMWHZUWNUWDUULNUXAUWNFUULUWDUUKUUMUWM
        UVPWIZUUKUWKUWLWJZWKUWDEGWLVNZUWNUWGUULNUXBUWNFUULUWGUXDUUKUWKUWLWOZWKU
        WGEGWLVNZUWPUWQEGWPWQUAUWRWRWSUWNUWSPZUWDUWRUWOXDZCSZUWGUXJCSZUWJUXIUWK
        UXJFNZUXKUWNUWKUWSUXEWIUXIUXJUVLFUXIUWRENZUWSUXJUVLNUWNUXNUWSUWNUUKUXAU
        XBUXNUXCUXFUXHUWPUWQEGWTWQWIUWNUWSXADEUVIUWRUWOUWRUVIUWRUCXEXBXCHXFZUXK
        UWKUXMPUXJRMZUWPOUXPUWRUWPUWRUWOUWPUWQUWDRXGXHUAXIXJZUWPUWQXKXLABUWDUXJ
        CDEFHIJXIZUWRUWOXOZXMXNXCUXIUWLUXMUXLUWNUWLUWSUXGWIUXOUXLUWLUXMPUXPUWQO
        UXPUWRUWQUXQUWPUWQXPXLABUWGUXJCDEFHILXIZUXSXMXNXCUWIUXKUXLPKUXJUXSUWEUX
        JUCUWFUXKUWHUXLUWEUXJUWDCXQUWEUXJUWGCXQXRXSXTYAYBJLKFFCYCYDUVSUWFUWEUWG
        CSZPZUWDUWGCSZUFZLYEZKYEJYEUYEJKUYDLUYBUWMUWQUWPOUYCUWFUWKUYAUWLUWFUWKU
        WEFNZUWFUWKUYFPZUWERMZUWPOZABUWDUWECDEFHIUXRKXIZXMZYFYGUYAUYFUWLUYAUYFU
        WLPZUWQUYHOZABUWEUWGCDEFHIUYJUXTXMZYFYHYIUYAUWFUWQUYHUWPUYAUYLUYMUYNYJU
        WFUYGUYIUYKYJYKABUWDUWGCDEFHIUXRUXTXMXCYLYMJKLCYNYPWEUUKCTNZUUNUVRUWAPY
        OUUKUVBUVATNUYOUVGUUKFFTTUUKFUULTUUKGENUULTNEGYQEGUUJEYRYSUVPYTZUYPUUAC
        UVATUUBUUCFCTUVHUUGVNUUDUUEUUF $.

      $( Lemma for ~ filnet .  (Contributed by Jeff Hankins, 15-Dec-2009.)
         (Revised by Mario Carneiro, 8-Aug-2015.) $)
      filnetlem4 $p |- ( F e. ( Fil ` X ) -> E. d e. DirRel E. f ( f : dom d
          --> X
       /\ F = ( ( X FilMap f ) ` ran ( tail ` d ) ) ) ) $=
        ( vk cfv wcel wceq wa wss wi cvv c0 vt vm vv cfil cdir cdm cv ctail crn
        cfm wex wrex cxp cuni filnetlem3 simpri simprd c2nd cres f2ndres simpld
        wf co fssres2 sylancr filtop xpexg mpdan ssexd simpli dirdm syl eqtr4id
        fexd feq2d mpbid cfg cima c1st wral cpw wfn wb eqid tailf mpbird adantr
        ffn imaeq2 rexrn 3syl wfun wfo fo2nd fofn ax-mp ssv fnssres mp2an fnfun
        sseq1d ffvelcdmda ad2antrr sseqtrrd fndmi sseqtrrdi funimass4 wbr simpr
        elpwid eleqtrd vex a1i eltail biantrurd anbi1d filnetlem1 bitr4d imbi1d
        syl3anc bitr4di eleq1d bitri rexbidva csn ciun cop op1std imbi12d sseq1
        weq wne cfbas wn sylib ss0b syl2anc dmss eqeq2d anbi12d impexp ralbidv2
        fvres pm5.74i bitrdi bitrd op2ndd raliunxp sneq id xpeq12d eqtri raleqi
        cbviunv dfss3 imbi2i r19.21v bitr4i ralbii 3bitr4i rexbii rexeqi sseq2d
        ralbidv rexiunxp 3bitri fileln0 adantlr r19.9rzv ssid rspcv mpii adantl
        sstr2 com12 ralrimivw impbid1 bitr3d bitrid 3bitrd pm5.32da filn0 jctil
        snnz neanior xpeq0 sylnibr ralrimiva r19.2z rexnal sseq1i iunss 3bitr3i
        wo necon3abii sylibr cid dmresi filnetlem2 eqsstrri dmxpid eqssi tailfb
        sseqtri elfm filfbas elfg 3bitr4d eqrdv fgfil eqtr2d feq1 fveq1d spcegv
        jca oveq2 sylc dmeq fveq2 rneqd fveq2d exbidv rspcev ) FHUDMZNZCUENZCUF
        ZHDUGZVBZFCUHMZUIZHUYHUJVCZMZOZPZDUKZIUGZUFZHUYHVBZFUYQUHMZUIZUYLMZOZPZ
        DUKZIUEULUYEGFHUMZQZUYFGCUNUNZOZUYEVUGUYFPRZABCEFGHJKUOZUPZUQZUYEURGUSZ
        SNUYGHVUNVBZFUYKHVUNUJVCZMZOZPZUYPUYEGHSVUNUYEVUFHURVUFUSVBVUGGHVUNVBZF
        HUTUYEVUGUYFVULVAZVUFHGURVDVEZUYEGVUFSUYEHFNZVUFSNFHVFZFHUYDFVGVHVVAVIV
        NUYEVUOVURUYEVUTVUOVVBUYEGUYGHVUNUYEGVUHUYGVUIVUJVUKVJUYEUYFUYGVUHOVUMC
        VKVLVMZVOVPUYEVUQHFVQVCZFUYEUAVUQVVFUYEUAUGZHQZVUNUYQVRZVVGQZIUYKULZPZV
        VHEUGZVVGQZEFULZPZVVGVUQNZVVGVVFNZUYEVVHVVKVVOUYEVVHPZVVKVUNUYHUYJMZVRZ
        VVGQZDGULZUYQVSMZUYHVSMZQZUYQURMZVVGNZRZIGVTZDGULZVVOVVSGUYGWAZUYJVBZUY
        JGWBVVKVWCWCUYEVWMVVHUYEVWMUYGVWLUYJVBZUYEUYFVWNVUMCUYGUYGWDZWEVLUYEGUY
        GVWLUYJVVEVOWFWGZGVWLUYJWHVVJVWBIDGUYJUYQVVTOVVIVWAVVGUYQVVTVUNWIXAWJWK
        VVSVWBVWJDGVVSUYHGNZPZVWBUYQVUNMZVVGNZIVVTVTZVWJVWRVUNWLZVVTVUNUFZQVWBV
        XAWCVUNGWBZVXBURSWBZGSQVXDSSURWMVXEWNSSURWOWPGWQSGURWRWSZGVUNWTWPVWRVVT
        GVXCVWRVVTUYGGVWRVVTUYGVVSGVWLUYHUYJVWPXBXJUYEGUYGOVVHVWQVVEXCZXDGVUNVX
        FXEXFIVVTVVGVUNXGVEVWRVWTVWIIVVTGVWRUYQVVTNZVWTRUYQGNZVWFPZVWTRZVXIVWIR
        ZVWRVXHVXJVWTVWRVXHUYHUYQCXHZVXJVWRUYFUYHUYGNUYQSNZVXHVXMWCUYEUYFVVHVWQ
        VUMXCVWRUYHGUYGVVSVWQXIZVXGXKVXNVWRIXLZXMUYHUYQSCUYGVWOXNXTVWRVXJVWQVXI
        PZVWFPVXMVWRVXIVXQVWFVWRVWQVXIVXOXOXPABUYHUYQCEFGJKDXLVXPXQYAXRXSVXKVXJ
        VWHRVXLVXJVWTVWHVXIVWTVWHWCVWFVXIVWSVWGVVGUYQGURUUCYBWGUUDVXIVWFVWHUUAY
        CUUEUUBUUFYDVWKLUGZVVMQZVXRVVGQZRZLFVTZUBVVMULZEFULZVVSVVOVWKVXRVWEQZVX
        TRZLFVTZDGULVYGDEFVVMYEZVVMUMZYFZULVYDVWJVYGDGVWIILFVXRYEZVXRUMZYFZVTVY
        EUCUGZVVGNZRZUCVXRVTZLFVTVWJVYGVWIVYPILUCFVXRUYQVXRVYNYGOZVWFVYEVWHVYOV
        YRVWDVXRVWEVXRVYNUYQLXLZUCXLZYHXAVYRVWGVYNVVGVXRVYNUYQVYSVYTUUGYBYIUUHV
        WIIGVYMGVYJVYMJELFVYIVYLELYKZVYHVYKVVMVXRVVMVXRUUIWUAUUJUUKUUNUULUUMVYF
        VYQLFVYFVYEVYOUCVXRVTZRVYQVXTWUBVYEUCVXRVVGUUOUUPVYEVYOUCVXRUUQUURUUSUU
        TUVAVYGDGVYJJUVBVYGVYBDEUBFVVMUYHVVMUBUGZYGOZVYFVYALFWUDVYEVXSVXTWUDVWE
        VVMVXRVVMWUCUYHEXLZUBXLYHUVCXSUVDUVEUVFVVSVYCVVNEFVVSVVMFNZPZVYBVYCVVNW
        UGVVMTYLZVYBVYCWCUYEWUFWUHVVHVVMFHUVGZUVHVYBUBVVMUVIVLWUGVYBVVNWUFVYBVV
        NRVVSWUFVYBVVMVVMQZVVNVVMUVJVYAWUJVVNRLVVMFLEYKVXSWUJVXTVVNVXRVVMVVMYJV
        XRVVMVVGYJYIUVKUVLUVMVVNVYALFVXSVVNVXTVXRVVMVVGUVNUVOUVPUVQUVRYDUVSUVTU
        WAUYEVVCUYKGYMMNZVUTVVQVVLWCVVDUYEUYFGTYLZWUKVUMUYEVYITQZEFVTZYNZWULUYE
        WUMYNZEFULZWUOUYEFTYLWUPEFVTWUQFHUWBUYEWUPEFUYEWUFPZVYHTOVVMTOUWNZWUMWU
        RVYHTYLZWUHPWUSYNWURWUHWUTWUIVVMWUEUWDUWCVYHTVVMTUWEYOWUMVYITOWUSVYIYPV
        YHVVMUWFYCUWGUWHWUPEFUWIYQWUMEFUWJYOWUNGTGTQVYJTQGTOWUNGVYJTJUWKGYPEFVY
        ITUWLUWMUWOUWPCGGUYGGUWQGUSZUFZUYGGUWRWVACQZWVBUYGQWVCCGGUMZQZABCEFGJKU
        WSZVJWVACYRWPUWTUYGWVDUFZGWVEUYGWVGQWVCWVEWVFUPCWVDYRWPGUXAUXDUXBUXCYQV
        VBIVVGUYKFVUNHGUXEXTUYEFHYMMNVVRVVPWCFHUXFEVVGFHUXGVLUXHUXIFHUXJUXKUXOU
        YOVUSDVUNSUYHVUNOZUYIVUOUYNVURUYGHUYHVUNUXLWVHUYMVUQFWVHUYKUYLVUPUYHVUN
        HUJUXPUXMYSYTUXNUXQVUEUYPICUEUYQCOZVUDUYODWVIUYSUYIVUCUYNWVIUYRUYGHUYHU
        YQCUXRVOWVIVUBUYMFWVIVUAUYKUYLWVIUYTUYJUYQCUHUXSUXTUYAYSYTUYBUYCYQ $.
    $}

    $( A filter has the same convergence and clustering properties as some net.
       (Contributed by Jeff Hankins, 12-Dec-2009.)  (Revised by Mario Carneiro,
       8-Aug-2015.) $)
    filnet $p |- ( F e. ( Fil ` X ) -> E. d e. DirRel E. f ( f : dom d --> X
       /\ F = ( ( X FilMap f ) ` ran ( tail ` d ) ) ) ) $=
      ( vx vy vn cv csn cxp ciun wcel wa c1st cfv wss copab eqid filnetlem4 ) E
      FEHZGBGHZIUAJKZLFHZUBLMUCNOTNOPMEFQZAGBUBCDUBRUDRS $.
  $}

$( (End of Jeff Hankins's mathbox.) $)
