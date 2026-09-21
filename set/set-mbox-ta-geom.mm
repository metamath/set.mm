

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Elementary Geometry
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Two-dimensional geometry
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  This definition has been superseded by ` TarskiGDim>= ` and is no longer
  needed in the main part of set.mm. It is only kept here for reference.

$)

  $c TarskiG2D $.
  $( Extends class notation with the class of geometries fulfilling the
     planarity axioms. $)
  cstrkg2d $a class TarskiG2D $.

  ${
    $d d f i p u v x y z $.
    $( Define the class of geometries fulfilling the lower dimension axiom,
       Axiom A8 of [Schwabhauser] p. 12, and the upper dimension axiom, Axiom
       A9 of [Schwabhauser] p. 13, for dimension 2.  (Contributed by Thierry
       Arnoux, 14-Mar-2019.)  (New usage is discouraged.) $)
    df-trkg2d $a |- TarskiG2D = { f | [. ( Base ` f ) / p ].
          [. ( dist ` f ) / d ]. [. ( Itv ` f ) / i ].
          ( E. x e. p E. y e. p E. z e. p
            -. ( z e. ( x i y ) \/ x e. ( z i y ) \/ y e. ( x i z ) )
         /\ A. x e. p A. y e. p A. z e. p A. u e. p A. v e. p ( (
    ( ( x d u ) = ( x d v ) /\ ( y d u ) = ( y d v ) /\ ( z d u ) = ( z d v ) )
       /\ u =/= v ) -> ( z e. ( x i y ) \/ x e. ( z i y ) \/ y e. ( x i z ) ) )
      ) } $.
  $}

  ${
    $d .- d f i p u v x y z $.  $d G d f i p $.  $d I d f i p u v x y z $.
    $d P d f i p u v x y z $.
    istrkg2d.p $e |- P = ( Base ` G ) $.
    istrkg2d.d $e |- .- = ( dist ` G ) $.
    istrkg2d.i $e |- I = ( Itv ` G ) $.
    $( Property of fulfilling dimension 2 axiom.  (Contributed by Thierry
       Arnoux, 29-May-2019.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    istrkg2d $p |- ( G e. TarskiG2D <-> ( G e. _V /\
      ( E. x e. P E. y e. P E. z e. P
            -. ( z e. ( x I y ) \/ x e. ( z I y ) \/ y e. ( x I z ) )
         /\ A. x e. P A. y e. P A. z e. P A. u e. P A. v e. P ( ( ( ( x .- u )
         = ( x .- v ) /\ ( y .- u ) = ( y .- v ) /\ ( z .- u ) = ( z .- v ) )
       /\ u =/= v ) -> ( z e. ( x I y ) \/ x e. ( z I y ) \/ y e. ( x I z ) ) )
      ) ) ) $=
      ( cv co wcel wrex wceq wral oveqd raleqbidv vi vp vd vf w3o wn w3a wne wa
      citv cfv wsbc cds cbs cstrkg2d simp1 eqcomd simp3 eleq2d 3orbi123d notbid
      rexeqbidv simp2 eqeq12d 3anbi123d anbi1d imbi12d anbi12d df-trkg2d elab4g
      wi sbcie3s ) CMZAMZBMZUAMZNZOZVNVMVOVPNZOZVOVNVMVPNZOZUEZUFZCUBMZPZBWEPZA
      WEPZVNEMZUCMZNZVNDMZWJNZQZVOWIWJNZVOWLWJNZQZVMWIWJNZVMWLWJNZQZUGZWIWLUHZU
      IZWCVKZDWERZEWERZCWERZBWERZAWERZUIZUAUDMZUJUKULUCXKUMUKULUBXKUNUKULVMVNVO
      HNZOZVNVMVOHNZOZVOVNVMHNZOZUEZUFZCFPZBFPZAFPZVNWIINZVNWLINZQZVOWIINZVOWLI
      NZQZVMWIINZVMWLINZQZUGZXBUIZXRVKZDFRZEFRZCFRZBFRZAFRZUIZUDGUOYTXJUDFIHUNU
      MUJGUBUCUAJKLWEFQZWJIQZVPHQZUGZYBWHYSXIUUDYAWGAFWEUUDWEFUUAUUBUUCUPUQZUUD
      XTWFBFWEUUEUUDXSWDCFWEUUEUUDXRWCUUDXMVRXOVTXQWBUUDXLVQVMUUDHVPVNVOUUDVPHU
      UAUUBUUCURUQZSUSUUDXNVSVNUUDHVPVMVOUUFSUSUUDXPWAVOUUDHVPVNVMUUFSUSUTZVAVB
      VBVBUUDYRXHAFWEUUEUUDYQXGBFWEUUEUUDYPXFCFWEUUEUUDYOXEEFWEUUEUUDYNXDDFWEUU
      EUUDYMXCXRWCUUDYLXAXBUUDYEWNYHWQYKWTUUDYCWKYDWMUUDIWJVNWIUUDWJIUUAUUBUUCV
      CUQZSUUDIWJVNWLUUHSVDUUDYFWOYGWPUUDIWJVOWIUUHSUUDIWJVOWLUUHSVDUUDYIWRYJWS
      UUDIWJVMWIUUHSUUDIWJVMWLUUHSVDVEVFUUGVGTTTTTVHVLABCDEUDUAUBUCVIVJ $.

    ${
      axtglowdim2ALTV.g $e |- ( ph -> G e. TarskiG2D ) $.
      $( Alternate version of ~ axtglowdim2 .  (Contributed by Thierry Arnoux,
         29-May-2019.)  (New usage is discouraged.) $)
      axtglowdim2ALTV $p |- ( ph -> E. x e. P E. y e. P E. z e. P
            -. ( z e. ( x I y ) \/ x e. ( z I y ) \/ y e. ( x I z ) ) ) $=
        ( vu vv cv co wcel wrex wceq wral w3o wn w3a wa cstrkg2d istrkg2d sylib
        wne wi cvv simprd simpld ) ADOZBOZCOZGPQUNUMUOGPQUOUNUMGPQUAZUBDERCERBE
        RZUNMOZHPUNNOZHPSUOURHPUOUSHPSUMURHPUMUSHPSUCURUSUHUDUPUINETMETDETCETBE
        TZAFUJQZUQUTUDZAFUEQVAVBUDLBCDNMEFGHIJKUFUGUKUL $.
    $}

    ${
      $d u v x y z .- $.  $d u v x y z I $.  $d u v x y z P $.  $d u v z Z $.
      $d u v x y z X $.  $d u v y z Y $.  $d u v x y z U $.  $d v x y z V $.
      axtgupdim2ALTV.x $e |- ( ph -> X e. P ) $.
      axtgupdim2ALTV.y $e |- ( ph -> Y e. P ) $.
      axtgupdim2ALTV.z $e |- ( ph -> Z e. P ) $.
      axtgupdim2ALTV.u $e |- ( ph -> U e. P ) $.
      axtgupdim2ALTV.v $e |- ( ph -> V e. P ) $.
      axtgupdim2ALTV.0 $e |- ( ph -> U =/= V ) $.
      axtgupdim2ALTV.1 $e |- ( ph -> ( X .- U ) = ( X .- V ) ) $.
      axtgupdim2ALTV.2 $e |- ( ph -> ( Y .- U ) = ( Y .- V ) ) $.
      axtgupdim2ALTV.3 $e |- ( ph -> ( Z .- U ) = ( Z .- V ) ) $.
      axtgupdim2ALTV.g $e |- ( ph -> G e. TarskiG2D ) $.
      $( Alternate version of ~ axtgupdim2 .  (Contributed by Thierry Arnoux,
         29-May-2019.)  (New usage is discouraged.) $)
      axtgupdim2ALTV $p |- ( ph ->
        ( Z e. ( X I Y ) \/ X e. ( Z I Y ) \/ Y e. ( X I Z ) ) ) $=
        ( vu vv vx vy vz co wceq w3a wne wcel w3o 3jca cv wa wi cvv wn cstrkg2d
        wral wrex istrkg2d sylib simprrd oveq1 eqeq12d 3anbi1d anbi1d 3orbi123d
        eleq2d eleq1 imbi12d 2ralbidv 3anbi2d 3anbi3d rspc3v syl3anc mpd eqeq1d
        oveq2 3anbi123d neeq1 anbi12d imbi1d eqeq2d neeq2 rspc2v syl2anc mp2and
        ) AHCFUIZHGFUIZUJZICFUIZIGFUIZUJZJCFUIZJGFUIZUJZUKZCGULZJHIEUIZUMZHJIEU
        IZUMZIHJEUIZUMZUNZAWNWQWTTUAUBUOSAHUDUPZFUIZHUEUPZFUIZUJZIXJFUIZIXLFUIZ
        UJZJXJFUIZJXLFUIZUJZUKZXJXLULZUQZXIURZUEBVBUDBVBZXAXBUQZXIURZAUFUPZXJFU
        IZYHXLFUIZUJZUGUPZXJFUIZYLXLFUIZUJZUHUPZXJFUIZYPXLFUIZUJZUKZYBUQZYPYHYL
        EUIZUMZYHYPYLEUIZUMZYLYHYPEUIZUMZUNZURZUEBVBUDBVBZUHBVBUGBVBUFBVBZYEADU
        SUMZUUHUTUHBVCUGBVCUFBVCZUUKADVAUMUULUUMUUKUQUQUCUFUGUHUEUDBDEFKLMVDVEV
        FAHBUMIBUMJBUMUUKYEURNOPUUJYEXNYOYSUKZYBUQZYPHYLEUIZUMZHUUDUMZYLHYPEUIZ
        UMZUNZURZUEBVBUDBVBXNXQYSUKZYBUQZYPXCUMZHYPIEUIZUMZIUUSUMZUNZURZUEBVBUD
        BVBUFUGUHHIJBBBYHHUJZUUIUVBUDUEBBUVKUUAUUOUUHUVAUVKYTUUNYBUVKYKXNYOYSUV
        KYIXKYJXMYHHXJFVGYHHXLFVGVHVIVJUVKUUCUUQUUEUURUUGUUTUVKUUBUUPYPYHHYLEVG
        VLYHHUUDVMUVKUUFUUSYLYHHYPEVGVLVKVNVOYLIUJZUVBUVJUDUEBBUVLUUOUVDUVAUVIU
        VLUUNUVCYBUVLYOXQXNYSUVLYMXOYNXPYLIXJFVGYLIXLFVGVHVPVJUVLUUQUVEUURUVGUU
        TUVHUVLUUPXCYPYLIHEWBVLUVLUUDUVFHYLIYPEWBVLYLIUUSVMVKVNVOYPJUJZUVJYDUDU
        EBBUVMUVDYCUVIXIUVMUVCYAYBUVMYSXTXNXQUVMYQXRYRXSYPJXJFVGYPJXLFVGVHVQVJU
        VMUVEXDUVGXFUVHXHYPJXCVMUVMUVFXEHYPJIEVGVLUVMUUSXGIYPJHEWBVLVKVNVOVRVSV
        TACBUMGBUMYEYGURQRYDYGWLXMUJZWOXPUJZWRXSUJZUKZCXLULZUQZXIURUDUECGBBXJCU
        JZYCUVSXIUVTYAUVQYBUVRUVTXNUVNXQUVOXTUVPUVTXKWLXMXJCHFWBWAUVTXOWOXPXJCI
        FWBWAUVTXRWRXSXJCJFWBWAWCXJCXLWDWEWFXLGUJZUVSYFXIUWAUVQXAUVRXBUWAUVNWNU
        VOWQUVPWTUWAXMWMWLXLGHFWBWGUWAXPWPWOXLGIFWBWGUWAXSWSWRXLGJFWBWGWCXLGCWH
        WEWFWIWJVTWK $.
    $}
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Morley's Miracle
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    cgranbtwn.p $e |- P = ( Base ` G ) $.
    cgranbtwn.i $e |- I = ( Itv ` G ) $.
    cgranbtwn.g $e |- ( ph -> G e. TarskiG ) $.
    cgranbtwn.a $e |- ( ph -> A e. P ) $.
    cgranbtwn.b $e |- ( ph -> B e. P ) $.
    cgranbtwn.c $e |- ( ph -> C e. P ) $.
    cgranbtwn.d $e |- ( ph -> D e. P ) $.
    cgranbtwn.e $e |- ( ph -> E e. P ) $.
    cgranbtwn.f $e |- ( ph -> F e. P ) $.
    cgranbtwn.1 $e |- ( ph -> <" A B C "> ( cgrA ` G ) <" D E F "> ) $.
    cgranbtwn.2 $e |- ( ph -> A e. ( B I C ) ) $.
    $( Null angle implies betweenness.  (Contributed by SS, 4-Jun-2026.) $)
    cgranbtwn $p |- ( ph -> ( D e. ( E I F ) \/ F e. ( E I D ) ) ) $=
      ( wne co wcel wo chlg cfv wbr w3a cds eqid cgrane2 cgrane1 btwnhl1 cgrahl
      cstrkg ishlg mpbid simp3d ) AEGUBZHGUBZEGHJUCUDHGEJUCUDUEZAEHGIUFUGZUGUHU
      TVAVBUIABCDEFGHIJVCIUJUGZKLVDUKMNOPQRSTVCUKZACDBBFIJVCKLVEOPNMNUAABCDEFGH
      IJVCKLVEMNOPQRSTULABCDEFGHIJVCKLVEMNOPQRSTUMUNUOAEHGFIJVCUPKLVEQSRMUQURUS
      $.
  $}

  ${
    btwnlng13.p $e |- P = ( Base ` G ) $.
    btwnlng13.i $e |- I = ( Itv ` G ) $.
    btwnlng13.l $e |- L = ( LineG ` G ) $.
    btwnlng13.g $e |- ( ph -> G e. TarskiG ) $.
    btwnlng13.x $e |- ( ph -> X e. P ) $.
    btwnlng13.y $e |- ( ph -> Y e. P ) $.
    btwnlng13.z $e |- ( ph -> Z e. P ) $.
    btwnlng13.d $e |- ( ph -> X =/= Y ) $.
    btwnlng13.1 $e |- ( ph -> ( Z e. ( X I Y ) \/ Y e. ( X I Z ) ) ) $.
    $( If ` Z ` is between ` X ` and ` Y ` , or ` Y ` is between ` X ` and
       ` Z ` , then ` Z ` lies on the line ` X Y ` .  (Contributed by SS,
       4-Jun-2026.) $)
    btwnlng13 $p |- ( ph -> Z e. ( X L Y ) ) $=
      ( co wcel adantr wa cstrkg wne simpr btwnlng1 btwnlng3 mpjaodan ) AHFGDRS
      ZHFGERSGFHDRSZAUHUABCDEFGHIJKACUBSZUHLTAFBSZUHMTAGBSZUHNTAHBSZUHOTAFGUCZU
      HPTAUHUDUEAUIUABCDEFGHIJKAUJUILTAUKUIMTAULUINTAUMUIOTAUNUIPTAUIUDUFQUG $.
  $}

  ${
    morley.s $e |- S = ( Base ` G ) $.
    morley.l $e |- L = ( LineG ` G ) $.
    morley.e $e |- .~ = ( cgrA ` G ) $.
    morley.g $e |- ( ph -> G e. TarskiG ) $.
    morley.a $e |- ( ph -> A e. S ) $.
    morley.b $e |- ( ph -> B e. S ) $.
    morley.c $e |- ( ph -> C e. S ) $.
    morley.p $e |- ( ph -> P e. S ) $.
    morley.q $e |- ( ph -> Q e. S ) $.
    morley.r $e |- ( ph -> R e. S ) $.
    morley.0 $e |- ( ph -> -. ( C e. ( A L B ) \/ A = B ) ) $.
    morley.1 $e |- ( ph -> <" C A Q "> .~ <" Q A R "> ) $.
    morley.2 $e |- ( ph -> <" R A B "> .~ <" Q A R "> ) $.
    morley.3 $e |- ( ph -> <" A B R "> .~ <" R B P "> ) $.
    morley.4 $e |- ( ph -> <" P B C "> .~ <" R B P "> ) $.
    morley.5 $e |- ( ph -> <" B C P "> .~ <" P C Q "> ) $.
    morley.6 $e |- ( ph -> <" Q C A "> .~ <" P C Q "> ) $.
    $( Lemma for morley .  (Contributed by TA and SS, 4-Jun-2026.) $)
    morleylemrneab $p |- ( ph -> -. R e. ( A L B ) ) $=
      ( co wcel wn wceq wo ioran sylib simpld citv cfv eqid cstrkg ad2antrr wne
      wa simprd adantr neqned chlg cs3 ccgra breqi cgrane3 necomd cgrane4 simpr
      cgranbtwn btwnlng13 tglineelsb2 eleqtrd cgracom cgratr tglineeltr cgrane2
      wbr btwnlng3 cds cgrabtwn btwnlng2 eleqtrrd tgellng mpbid mpjao3dan mtand
      cgraswap w3o ) AHBCKUIZUJZDWOUJZAWQUKZBCULZUKZAWQWSUMUKWRWTVCUBWQWSUNUOZU
      PAWPVCZHBCJUQURZUIUJZWQBHCXCUIUJZCBHXCUIUJZXBXDVCZIBCDFJXCKLXCUSZMAJUTUJZ
      WPXDOVAZABIUJZWPXDPVAZACIUJZWPXDQVAZXBBCVBZXDXBBCAWTWPAWRWTXAVDVEVFZVEZAF
      IUJZWPXDTVAZXGBFXGHBCFIBHJXCJVGURZLXHXTUSZXJAHIUJZWPXDUAVAZXLXNXSXLYCXBHB
      CVHZFBHVHZJVIURZWCZXDXBYDYEGWCZYGAYHWPUDVEYDYEGYFNVJUOZVEZVKZVLXGFBHKUIZW
      OXGIJXCKBHFLXHMXJXLYCXSXGHBCFIBHJXCXTLXHYAXJYCXLXNXSXLYCYJVMZXGHBCFIBHJXC
      LXHXJYCXLXNXSXLYCYJXBXDVNZVOVPXGIBHCJXCKLXHMXJXLYCYMXNXGBCXQVLXGIJXCKBHCL
      XHMXJXLYCXNYMYNWDVQVRADIUJZWPXDRVAZXGIJXCKBFDLXHMXJXLXSYPYKXGHBCDIBFJXCLX
      HXJYCXLXNYPXLXSXBYDDBFVHZYFWCZXDXBDBFHIBCJXCXTLXHAXIWPOVEZYAAYOWPRVEZAXKW
      PPVEZAXRWPTVEZAYBWPUAVEZUUAAXMWPQVEZXBDBFFIBBHJHXCCXTLXHYSYAYTUUAUUBUUBUU
      AUUCXBYQYEGWCZYQYEYFWCAUUEWPUCVEYQYEGYFNVJUOZUUCUUAUUDXBHBCFIBHJXCXTLXHYS
      YAUUCUUAUUDUUBUUAUUCYIVSVTVSZVEYNVOVPWAXBXEVCZIBCDFJXCKLXHMAXIWPXEOVAZAXK
      WPXEPVAZAXMWPXEQVAZXBXOXEXPVEAXRWPXETVAZUUHBFXBBFVBZXEXBDBFFIBHJXCXTLXHYA
      YSYTUUAUUBUUBUUAUUCUUFWBZVEZVLUUHFYLWOUUHIJXCKBHFLXHMUUIUUJAYBWPXEUAVAZUU
      LXBBHVBZXEXBHBCFIBHJXCXTLXHYAYSUUCUUAUUDUUBUUAUUCYIVMZVEUUHHBCFIBHJXCJWEU
      RZLXHUUSUSZUUIUUPUUJUUKUULUUJUUPXBYGXEYIVEXBXEVNZWFWGXBWOYLULZXEXBIBCHJXC
      KLXHMYSUUAUUDXPUUCXBBHUURVLAWPVNZVQZVEWHAYOWPXERVAZUUHIJXCKBFDLXHMUUIUUJU
      ULUVEUUOUUHHBCDIBFJXCUUSLXHUUTUUIUUPUUJUUKUVEUUJUULXBYRXEUUGVEUVAWFWGWAXB
      XFVCZIBCDFJXCKLXHMAXIWPXFOVAZAXKWPXFPVAZAXMWPXFQVAZXBXOXFXPVEZAXRWPXFTVAZ
      UVFBFXBUUMXFUUNVEZVLUVFFYLWOUVFIJXCKBHFLXHMUVGUVHAYBWPXFUAVAZUVKXBUUQXFUU
      RVEZUVFCBHFIBHJXCLXHUVGUVIUVHUVMUVKUVHUVMUVFCBHHIBBCJFXCHXTLXHUVGYAUVIUVH
      UVMUVMUVHUVIUVFCBHIJXCXTLXHUVGYAUVIUVHUVMUVFBCUVJVLUVNWMZUVKUVHUVMXBYGXFY
      IVEVTXBXFVNZVOVPXBUVBXFUVDVEWHAYOWPXFRVAZUVFIJXCKBFDLXHMUVGUVHUVKUVQUVLUV
      FCBHDIBFJXCLXHUVGUVIUVHUVMUVQUVHUVKUVFCBHHIBBCJDXCFXTLXHUVGYAUVIUVHUVMUVM
      UVHUVIUVOUVQUVHUVKXBYRXFUUGVEVTUVPVOVPWAXBWPXDXEXFWNUVCXBIJXCKBCHLMXHYSUU
      AUUDXPUUCWIWJWKWL $.
  $}

$(
  @{
    @( Lemma for * morley .  (Contributed by Thierry Arnoux, 5-Oct-2020.) @)
    morleylemrnea @p |- ( ph -> R =/= A ) @=
      ( wceq co wcel wa simpr citv cfv eqid wo wn pm2.46 syl neqned tglinerflx1
      adantr eqeltrd morleylemrneab pm2.65da ) AHBAHBUIZHBCKUJZUKZAVGULHBVHAVGU
      MABVHUKVGAIBCJJUNUOZKLVJUPMOPQABCADVHUKZBCUIZUQURVLURUBVKVLUSUTVAVBVCVDAV
      IURVGABCDEFGHIJKLMNOPQRSTUAUBUCUDUEUFUGUHVEVCVFVA @.

    @( Lemma for * morley .  (Contributed by Thierry Arnoux, 5-Oct-2020.) @)
    morleylemrneb @p |- ( ph -> R =/= B ) @=
      ( wceq co wcel wa simpr citv cfv eqid wo wn pm2.46 syl neqned tglinerflx2
      adantr eqeltrd morleylemrneab pm2.65da ) AHCAHCUIZHBCKUJZUKZAVGULHCVHAVGU
      MACVHUKVGAIBCJJUNUOZKLVJUPMOPQABCADVHUKZBCUIZUQURVLURUBVKVLUSUTVAVBVCVDAV
      IURVGABCDEFGHIJKLMNOPQRSTUAUBUCUDUEUFUGUHVEVCVFVA @.

    @{
      morleylem2.i @e |- I = ( Itv ` G ) @.
      morleylem2.m @e |- M = ( ( ( lInvG ` G ) ` ( R L B ) ) ` P ) @.
      morleylem2.n @e |- N = ( ( ( lInvG ` G ) ` ( R L A ) ) ` Q ) @.
      @( @)
      morleylemmaib @p |- ( ph -> M e. ( A I B ) ) @=
        ? @.

      @( Lemma for * morley @)
      morleylemanen @p |- ( ph -> A =/= N ) @=
        ? @.

      @( The  @)
      morleylem2 @p |- ( ph -> <" B N R "> .~ <" A M R "> ) @=
        ? @.

      morleylem1.d @e |- .- = ( dist ` G ) @.
      @( Two of Morley's triangle sides are of same length.  (Contributed by
         Thierry Arnoux, 5-Oct-2020.) @)
      morleylem1 @p |- ( ph -> ( P .- R ) = ( Q .- R ) ) @=
        ( co wceq wa simpr oveq1d eqcomd wne cstrkg wcel adantr clmi cfv eqcomi
        a1i ncoltgdim2 eqid morleylemrnea tgelrnln lmicl eqeltrrd morleylemrneb
        wn wo morleylemrneab crn morleylemmaib chlg ccgra cs3 morleylem2 breqdi
        cgrane3 tgbtwnne btwnlng1 cgraswaplr tgbtwncom tglinethru eleq2d notbid
        ncolcom mpbird neneqd jca sylibr ncolrot1 ad2antrr morleylemanen necomd
        ioran wbr sacgr cgracom btwnhl1 cgrahl2 tgbtwnexch3 cgrane4 tgbtwnconn3
        mpjaodan isoas tgcgrcomlr pm2.61dane lmiiso tglinerflx1 lmicinv oveq12d
        eqtr3d 3eqtr4rd ) AOHNUQZMHNUQZFHNUQZEHNUQZAYDYEURMOAMOURZUSZYEYDYIMOHN
        AYHUTVAVBAMOVCZUSZHOHMIJKNPUPUMAJVDVEZYJSVFZAHIVEZYJUEVFZAOIVEZYJAFHBLU
        QZJVGVHZVHZVHZOIYTOURAOYTUOVIVJZAFYQIJKLYSNPUPUMSAIJKLBCDPQUMSTUAUBUFVK
        ZYSVLZQAIJKLHBPUMQSUETABCDEFGHIJLPQRSTUAUBUCUDUEUFUGUHUIUJUKULVMZVNZUDV
        OVPZVFZYOAMIVEZYJAEHCLUQZYRVHZVHZMIUUKMURAMUUKUNVIVJZAEUUIIJKLUUJNPUPUM
        SUUBUUJVLZQAIJKLHCPUMQSUEUAABCDEFGHIJLPQRSTUAUBUCUDUEUFUGUHUIUJUKULVQZV
        NZUCVOVPZVFZYKHOMIJKLNPUPUMQYMYOUUGUUQYKIJKLOHMPQUMYMUUGYOUUQYKIJKLMOHP
        QUMYMUUQUUGYOYKHMOLUQZVEZVRZYHVRZUSUUSYHVSVRYKUUTUVAYKUUTHBCLUQZVEZVRZA
        UVDYJABCDEFGHIJLPQRSTUAUBUCUDUEUFUGUHUIUJUKULVTVFYKUUSUVCYKUURUVBHYKUVB
        UURYKUVBIMOJKLPUMQYMUUQUUGAYJUTZUVEAUVBLWAVEYJAIJKLBCPUMQSTUAABMCIJKNPU
        PUMSTUUPUAABCDEFGHIJKLMOPQRSTUAUBUCUDUEUFUGUHUIUJUKULUMUNUOWBZACOHBIMHJ
        KJWCVHZPUMUVGVLZSUAUUFUETUUPUEAGJWDVHZCOHWEBMHWEGUVIURARVJZABCDEFGHIJKL
        MOPQRSTUAUBUCUDUEUFUGUHUIUJUKULUMUNUOWFWGZWHZWIZVNVFAMUVBVEYJAIJKLBCMPU
        MQSTUAUUPUVMUVFWJVFAOUVBVEYJAIJKLBCOPUMQSTUAUUFUVMACOBIJKNPUPUMSUAUUFTA
        CBDFEUVIHIJKLOMPQUVIVLZSUATUBUDUCUEAIJKLBCDPQUMSTUAUBUFWPZAECDHICEJKNPU
        MUPSUCUAUBUEUAUCAGUVIECDWEHCEWEZUVJUJWGWKZABCHHICEJKNPUMUPSTUAUEUEUAUCA
        GUVIBCHWEUVPUVJUIWGWKZAHBCFIBHJKNPUMUPSUETUAUDTUEAGUVIHBCWEFBHWEZUVJUHW
        GWKZADBFFIBHJKNPUMUPSUBTUDUDTUEAGUVIDBFWEUVSUVJUGWGWKZAFDBEIDFJKNPUMUPS
        UDUBTUCUBUDAGUVIFDBWEEDFWEZUVJULWGWKZACDEEIDFJKNPUMUPSUAUBUCUCUBUDAGUVI
        CDEWEUWBUVJUKWGWKZUMUOUNWBZWLZWJVFWMVBWNWOWQYKMOUVEWRWSUUSYHXEWTXAWPYKM
        BOKUQVEZHOMWEHMOWEUVIXFOBMKUQVEZYKUWGUSZHOMHIMCJKUVGOPUMUVHYKYLUWGYMVFZ
        YKYNUWGYOVFZYKYPUWGUUGVFZYKUUHUWGUUQVFZUWKUWMACIVEZYJUWGUAXBZUWIHMCHIOM
        JKUVGPUMUWJUVHUWKUWMUWOUWKUWLUWMUWIHMCHIOBJKUVGMPUMUVHUWJUWKUWMUWOUWKUW
        LABIVEZYJUWGTXBZAHMCWEHOBWEUVIXFYJUWGAHOBHIMCJKUVGPUMSUVHUEUUFTUEUUPUAA
        BOHCIMHJKNPUMUPSTUUFUEUAUUPUEACOHBIMHJKNBCPUMUPSUAUUFUETUUPUETUAUVKUWEU
        VFABOABCDEFGHIJKLMOPQRSTUAUBUCUDUEUFUGUHUIUJUKULUMUNUOXCXDZACMACBDFEUVI
        HIJKLOMPQUVNSUATUBUDUCUEUVOUVQUVRUVTUWAUWCUWDUMUOUNXCXDZXGWKXHXBUWMUWIO
        BMHIJKUVGPUMUVHUWLUWQUWMUWJUWKUWIBMOIJKNPUPUMUWJUWQUWMUWLYKUWGUTZWLAOBV
        CYJUWGUWRXBYKYJUWGUVEVFZXIXJXHUWLUWIMCOHIJKUVGPUMUVHUWMUWOUWLUWJUWKUWIB
        MOCIJKNPUPUMUWJUWQUWMUWLUWOUWTAOBCKUQZVEYJUWGUWFXBXKAMCVCYJUWGUWSXBUWIM
        OUXAXDXIXJYKUWHUSZHOMHIMBJKUVGOPUMUVHYKYLUWHYMVFZYKYNUWHYOVFZYKYPUWHUUG
        VFZYKUUHUWHUUQVFZUXEUXGAUWPYJUWHTXBZUXCHMBHIOMJKUVGPUMUXDUVHUXEUXGUXHUX
        EUXFUXGUXCHMBHIOCJKUVGMPUMUVHUXDUXEUXGUXHUXEUXFAUWNYJUWHUAXBZAHMBWEHOCW
        EUVIXFYJUWHABMHCIOHJKNPUMUPSTUUPUEUAUUFUEACOHBIMHJKUVGPUMSUVHUAUUFUETUU
        PUEUVKXHWKXBZUXGUXCOCMHIJKUVGPUMUVHUXFUXIUXGUXDUXEUXCBOMCIJKNPUPUMUXDUX
        HUXFUXGUXIYKUWHUTZAMUXBVEYJUWHUVFXBXKUXCHMBHIOCJKUVGPUMUVHUXDUXEUXGUXHU
        XEUXFUXIUXJXLYKYJUWHUVEVFZXIXJXHUXFUXCMBOHIJKUVGPUMUVHUXGUXHUXFUXDUXEUX
        CBOMIJKNPUPUMUXDUXHUXFUXGUXKWLAMBVCYJUWHUVLXBUXCMOUXLXDXIXJAUWGUWHVSYJA
        BMOCIJKPUMSTUUPUUFUAUVFUWFXMVFXNXOXPXQAYTHYSVHZNUQYFYDAFHYQIJKLYSNPUPUM
        SUUBUUCQUUEUDUEXRAYTOUXMHNUUAAHYQIJKLYSNPUPUMSUUBUUCQUUEUEAIHBJKLPUMQSU
        ETUUDXSXTYAYBAUUKHUUJVHZNUQYGYEAEHUUIIJKLUUJNPUPUMSUUBUUMQUUOUCUEXRAUUK
        MUXNHNUULAHUUIIJKLUUJNPUPUMSUUBUUMQUUOUEAIHCJKLPUMQSUEUAUUNXSXTYAYBYC
        @.
    @}

    @( Morley's theorem: The three points of intersection of the adjacent
       trisectors of the angles of any triangle form an equilateral triangle.

       Let ABC be any triangle, and PQR the points such that QR trisects BC
       when seen from A, and similarly for other sides.  Then, the triangle
       PQR is equilateral.

       This surprising results has become known as has as Morley's Miracle in
       mathematical folklore. @)
    morley @p |- ( ph -> <" P Q R "> e. ( eqltrG ` G ) ) @=
      ( citv cfv clng eqid co clmi ncolrot2 morleylem1 tgcgrcoml eqcomd iseqlgd
      cds eqtrd ) AEFHIJJUIUJZJUKUJZJUTUJZLVDULZVBULZVCULOSTUAAFHVDUMZEFVDUMZAH
      FEFIJVBVDLVEVFOUATSTADBCHEGFIJVBKHFBKUMJUNUJZUJUJZVDEFDKUMVIUJUJZLMNORPQU
      ASTAIJVBKBCDLMVFOPQRUBUOUGUHUCUDUEUFVFVJULVKULVEUPUQZURAHEVDUMZVGAEHFHIJV
      BVDLVEVFOSUATUAABCDEFGHIJVBKEHCKUMVIUJUJZVDFHBKUMVIUJUJZLMNOPQRSTUAUBUCUD
      UEUFUGUHVFVNULVOULVEUPUQZURAVMVGVHVPVLVAUS @.
  @}
$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Outer Five Segment (not used, no need to move to main)
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $c AFS $.

  $( Declare the syntax for the outer five segment configuration. $)
  cafs $a class AFS $.

  ${
    $d a b c d x y z w e f g h i p $.
    $( The outer five segment configuration is an abbreviation for the
       conditions of the Five Segment Axiom ( ~ axtg5seg ).  See ~ df-ofs .
       Definition 2.10 of [Schwabhauser] p. 28.  (Contributed by Scott Fenton,
       21-Sep-2013.)  (Revised by Thierry Arnoux, 15-Mar-2019.) $)
    df-afs $a |- AFS = ( g e. TarskiG |-> { <. e , f >. |
      [. ( Base ` g ) / p ]. [. ( dist ` g ) / h ]. [. ( Itv ` g ) / i ].
         E. a e. p E. b e. p E. c e. p E. d e. p E. x e. p E. y e. p
         E. z e. p E. w e. p (
         e = <. <. a , b >. , <. c , d >. >. /\
         f = <. <. x , y >. , <. z , w >. >. /\
         ( ( b e. ( a i c ) /\ y e. ( x i z ) ) /\
           ( ( a h b ) = ( x h y ) /\ ( b h c ) = ( y h z ) ) /\
           ( ( a h d ) = ( x h w ) /\ ( b h d ) = ( y h w ) ) ) ) } ) $.
  $}

  ${
    brafs.p $e |- P = ( Base ` G ) $.
    brafs.d $e |- .- = ( dist ` G ) $.
    brafs.i $e |- I = ( Itv ` G ) $.
    brafs.g $e |- ( ph -> G e. TarskiG ) $.

    ${
      $d e f g h i p G $.  $d a b c d g h i p w x y z I $.
      $d a b c d e f g h i p w x y z P $.  $d a b c d g h i p w x y z .- $.
      $d e f g ph $.
      $( Value of the AFS relation for a given geometry structure.
         (Contributed by Thierry Arnoux, 20-Mar-2019.) $)
      afsval $p |- ( ph -> ( AFS ` G ) = { <. e , f >. | E. a e. P E. b e. P
           E. c e. P E. d e. P E. x e. P E. y e. P E. z e. P E. w e. P (
           e = <. <. a , b >. , <. c , d >. >. /\
           f = <. <. x , y >. , <. z , w >. >. /\
           ( ( b e. ( a I c ) /\ y e. ( x I z ) ) /\
             ( ( a .- b ) = ( x .- y ) /\ ( b .- c ) = ( y .- z ) ) /\
             ( ( a .- d ) = ( x .- w ) /\ ( b .- d ) = ( y .- w ) ) ) ) } ) $=
        ( wa vg vi vh vp cv cop wceq wcel w3a wrex citv cfv wsbc cds cbs cstrkg
        co copab cafs cvv cmpt df-afs a1i wb simp1 eqcomd ad7antr simp3 ad8antr
        adantr oveqd anbi12d simp2 eqeq12d 3anbi123d 3anbi3d rexeqbidva sbcie3s
        eleq2d adantl opabbidv cxp df-xp fvexi xpex 3simpa reximi simpr opelxpi
        eqeltrri simp-7r simp-6r syl2anc eqeltrd simp-5r simp-4r simpllr simplr
        anim12dan rexlimdva2 rexlimdva rexlimivv syl ssopab2i ssexi fvmptd ) AU
        AIGUEZLUEZMUEZUFZNUEZOUEZUFZUFZUGZHUEZBUEZCUEZUFZDUEZEUEZUFZUFZUGZXIXHX
        KUBUEZUQZUHZXRXQXTYEUQZUHZTZXHXIUCUEZUQZXQXRYKUQZUGZXIXKYKUQZXRXTYKUQZU
        GZTZXHXLYKUQZXQYAYKUQZUGZXIXLYKUQZXRYAYKUQZUGZTZUIZUIZEUDUEZUJZDUUHUJZC
        UUHUJZBUUHUJZOUUHUJZNUUHUJZMUUHUJZLUUHUJZUBUAUEZUKULUMUCUUQUNULUMUDUUQU
        OULUMZGHURZXOYDXIXHXKJUQZUHZXRXQXTJUQZUHZTZXHXIKUQZXQXRKUQZUGZXIXKKUQZX
        RXTKUQZUGZTZXHXLKUQZXQYAKUQZUGZXIXLKUQZXRYAKUQZUGZTZUIZUIZEFUJZDFUJZCFU
        JZBFUJZOFUJZNFUJZMFUJZLFUJZGHURZUPUSUTUSUAUPUUSVAUGABCDEGHUAUCUBUDLMNOV
        BVCAUUQIUGZTUURUWHGHUWJUURUWHVDAUWHUUPUAFKJUOUNUKIUDUCUBPQRUUHFUGZYKKUG
        ZYEJUGZUIZUWGUUOLFUUHUWNUUHFUWKUWLUWMVEVFZUWNXHFUHZTZUWFUUNMFUUHUWNFUUH
        UGZUWPUWOVJZUWQXIFUHZTZUWEUUMNFUUHUWQUWRUWTUWSVJZUXAXKFUHZTZUWDUULOFUUH
        UXAUWRUXCUXBVJZUXDXLFUHZTZUWCUUKBFUUHUXDUWRUXFUXEVJZUXGXQFUHZTZUWBUUJCF
        UUHUXGUWRUXIUXHVJZUXJXRFUHZTZUWAUUIDFUUHUXJUWRUXLUXKVJUXMXTFUHZTZUVTUUG
        EFUUHUWNUWRUWPUWTUXCUXFUXIUXLUXNUWOVGUXOYAFUHZTZUVSUUFXOYDUXQUVDYJUVKYR
        UVRUUEUXQUVAYGUVCYIUXQUUTYFXIUXQJYEXHXKUXQYEJUWNUWMUWPUWTUXCUXFUXIUXLUX
        NUXPUWKUWLUWMVHVIVFZVKVSUXQUVBYHXRUXQJYEXQXTUXRVKVSVLUXQUVGYNUVJYQUXQUV
        EYLUVFYMUXQKYKXHXIUWNKYKUGUWPUWTUXCUXFUXIUXLUXNUXPUWNYKKUWKUWLUWMVMVFVI
        ZVKUXQKYKXQXRUXSVKVNUXQUVHYOUVIYPUXQKYKXIXKUXSVKUXQKYKXRXTUXSVKVNVLUXQU
        VNUUAUVQUUDUXQUVLYSUVMYTUXQKYKXHXLUXSVKUXQKYKXQYAUXSVKVNUXQUVOUUBUVPUUC
        UXQKYKXIXLUXSVKUXQKYKXRYAUXSVKVNVLVOVPVQVQVQVQVQVQVQVQVRVTWASUWIUTUHAUW
        IXGFFWBZUXTWBZUHZXPUYAUHZTZGHURZUYAUYAWBUYEUTGHUYAUYAWCUYAUYAUXTUXTFFFI
        UOPWDZUYFWEZUYGWEZUYHWEWJUWHUYDGHUWHXOYDTZEFUJZDFUJZCFUJZBFUJZOFUJZNFUJ
        ZMFUJZLFUJUYDUWGUYPLFUWFUYOMFUWEUYNNFUWDUYMOFUWCUYLBFUWBUYKCFUWAUYJDFUV
        TUYIEFXOYDUVSWFWGWGWGWGWGWGWGWGUYOUYDLMFFUWPUWTTZUYNUYDNFUYQUXCTZUYMUYD
        OFUYRUXFTZUYLUYDBFUYSUXITZUYKUYDCFUYTUXLTZUYJUYDDFVUAUXNTZUYIUYDEFVUBUX
        PTZXOUYBYDUYCVUCXOTZXGXNUYAVUCXOWHVUDXJUXTUHZXMUXTUHZXNUYAUHUYQVUEUXCUX
        FUXIUXLUXNUXPXOXHXIFFWIVGVUDUXCUXFVUFUYQUXCUXFUXIUXLUXNUXPXOWKUYRUXFUXI
        UXLUXNUXPXOWLXKXLFFWIWMXJXMUXTUXTWIWMWNVUCYDTZXPYCUYAVUCYDWHVUGXSUXTUHZ
        YBUXTUHZYCUYAUHVUGUXIUXLVUHUYSUXIUXLUXNUXPYDWOUYTUXLUXNUXPYDWPXQXRFFWIW
        MVUGUXNUXPVUIVUAUXNUXPYDWQVUBUXPYDWRXTYAFFWIWMXSYBUXTUXTWIWMWNWSWTXAXAX
        AXAXAXBXCXDXEVCXF $.
    $}

    ${
      $d a b c d e f w x y z .- $.  $d a b c d e f w x y z A $.
      $d a b c d e f w x y z B $.  $d a b c d e f w x y z C $.
      $d a b c d e f w x y z D $.  $d a b c d e f w x y z I $.
      $d a b c d e f w x y z P $.  $d a b c d e f w x y z W $.
      $d a b c d e f w x y z X $.  $d a b c d e f w x y z Y $.
      $d a b c d e f w x y z Z $.  $d e f G $.  $d e f ph $.
      brafs.o $e |- O = ( AFS ` G ) $.
      brafs.1 $e |- ( ph -> A e. P ) $.
      brafs.2 $e |- ( ph -> B e. P ) $.
      brafs.3 $e |- ( ph -> C e. P ) $.
      brafs.4 $e |- ( ph -> D e. P ) $.
      brafs.5 $e |- ( ph -> X e. P ) $.
      brafs.6 $e |- ( ph -> Y e. P ) $.
      brafs.7 $e |- ( ph -> Z e. P ) $.
      brafs.8 $e |- ( ph -> W e. P ) $.
      $( Binary relation form of the outer five segment predicate.
         (Contributed by Scott Fenton, 21-Sep-2013.) $)
      brafs $p |- ( ph -> ( <. <. A , B >. , <. C , D >. >. O
        <. <. X , Y >. , <. Z , W >. >. <-> ( ( B e. ( A I C ) /\
                       Y e. ( X I Z ) ) /\
          ( ( A .- B ) = ( X .- Y ) /\ ( B .- C ) = ( Y .- Z ) ) /\
          ( ( A .- D ) = ( X .- W ) /\ ( B .- D ) = ( Y .- W ) ) ) ) ) $=
        ( vb va vc vy vx vz vd vw vf ve cv co wcel wceq w3a oveq1 eleq2d anbi1d
        eqeq1d 3anbi123d eleq1 oveq2 anbi12d anbi2d 3anbi12d 3anbi3d eqeq2d cfv
        wa cafs cop wrex copab afsval eqtrid br8d ) AUHURZUIURZUJURZHUSZUTZUKUR
        ZULURZUMURZHUSZUTZVPZWEWDIUSZWJWIIUSZVAZWDWFIUSZWIWKIUSZVAZVPZWEUNURZIU
        SZWJUOURZIUSZVAZWDXBIUSZWIXDIUSZVAZVPZVBZWDBWFHUSZUTZWMVPZBWDIUSZWPVAZW
        TVPZBXBIUSZXEVAZXIVPZVBCXLUTZWMVPZBCIUSZWPVAZCWFIUSZWSVAZVPZXSCXBIUSZXH
        VAZVPZVBCBDHUSZUTZWMVPZYDCDIUSZWSVAZVPZYJVBYMYPBEIUSZXEVAZCEIUSZXHVAZVP
        ZVBYLWILWKHUSZUTZVPZYCLWIIUSZVAZYOVPZYQLXDIUSZVAZYTVPZVBYLMUUBUTZVPZYCL
        MIUSZVAZYNMWKIUSZVAZVPZUUIYSMXDIUSZVAZVPZVBYLMLNHUSZUTZVPZUUNYNMNIUSZVA
        ZVPZUUTVBUVCUVFYQLKIUSZVAZYSMKIUSZVAZVPZVBBCDEFJULUKUMUOLMNKUPUQUIUHUJU
        NWEBVAZWNXNXAXQXJXTUVLWHXMWMUVLWGXLWDWEBWFHVCVDVEUVLWQXPWTUVLWOXOWPWEBW
        DIVCVFVEUVLXFXSXIUVLXCXRXEWEBXBIVCVFVEVGWDCVAZXNYBXQYGXTYJUVMXMYAWMWDCX
        LVHVEUVMXPYDWTYFUVMXOYCWPWDCBIVIVFUVMWRYEWSWDCWFIVCVFVJUVMXIYIXSUVMXGYH
        XHWDCXBIVCVFVKVGWFDVAZYBYMYGYPYJUVNYAYLWMUVNXLYKCWFDBHVIVDVEUVNYFYOYDUV
        NYEYNWSWFDCIVIVFVKVLXBEVAZYJUUAYMYPUVOXSYRYIYTUVOXRYQXEXBEBIVIVFUVOYHYS
        XHXBECIVIVFVJVMWJLVAZYMUUDYPUUGUUAUUJUVPWMUUCYLUVPWLUUBWIWJLWKHVCVDVKUV
        PYDUUFYOUVPWPUUEYCWJLWIIVCVNVEUVPYRUUIYTUVPXEUUHYQWJLXDIVCVNVEVGWIMVAZU
        UDUULUUGUUQUUJUUTUVQUUCUUKYLWIMUUBVHVKUVQUUFUUNYOUUPUVQUUEUUMYCWIMLIVIV
        NUVQWSUUOYNWIMWKIVCVNVJUVQYTUUSUUIUVQXHUURYSWIMXDIVCVNVKVGWKNVAZUULUVCU
        UQUVFUUTUVRUUKUVBYLUVRUUBUVAMWKNLHVIVDVKUVRUUPUVEUUNUVRUUOUVDYNWKNMIVIV
        NVKVLXDKVAZUUTUVKUVCUVFUVSUUIUVHUUSUVJUVSUUHUVGYQXDKLIVIVNUVSUURUVIYSXD
        KMIVIVNVJVMAJGVQVOUQURWEWDVRWFXBVRVRVAUPURWJWIVRWKXDVRVRVAXKVBUOFVSUMFV
        SUKFVSULFVSUNFVSUJFVSUHFVSUIFVSUQUPVTSAULUKUMUOFUQUPGHIUIUHUJUNOPQRWAWB
        TUAUBUCUDUEUFUGWC $.
    $}
  $}

  ${
    tg5segofs.p $e |- P = ( Base ` G ) $.
    tg5segofs.m $e |- .- = ( dist ` G ) $.
    tg5segofs.s $e |- I = ( Itv ` G ) $.
    tg5segofs.g $e |- ( ph -> G e. TarskiG ) $.
    tg5segofs.a $e |- ( ph -> A e. P ) $.
    tg5segofs.b $e |- ( ph -> B e. P ) $.
    tg5segofs.c $e |- ( ph -> C e. P ) $.
    tg5segofs.d $e |- ( ph -> D e. P ) $.
    tg5segofs.e $e |- ( ph -> E e. P ) $.
    tg5segofs.f $e |- ( ph -> F e. P ) $.
    tg5segofs.o $e |- O = ( AFS ` G ) $.
    tg5segofs.h $e |- ( ph -> H e. P ) $.
    tg5segofs.i $e |- ( ph -> I e. P ) $.
    tg5segofs.1 $e |- ( ph -> <. <. A , B >. , <. C , D >. >. O
          <. <. E , F >. , <. H , I >. >. ) $.
    tg5segofs.2 $e |- ( ph -> A =/= B ) $.
    $( Rephrase ~ axtg5seg using the outer five segment predicate.  Theorem
       2.10 of [Schwabhauser] p. 28.  (Contributed by Thierry Arnoux,
       23-Mar-2019.) $)
    tg5segofs $p |- ( ph -> ( C .- D ) = ( H .- I ) ) $=
      ( co wcel wceq cop wbr w3a brafs mpbid simp1d simpld simprd simp2d simp3d
      wa axtg5seg ) AGHJFEIKLKBCDNOPQRSTUBUCUEUAUFUHACBDKUIUJZHGJKUIUJZAVDVEVBZ
      BCLUIGHLUIUKZCDLUIHJLUIUKZVBZBELUIGKLUIUKZCELUIHKLUIUKZVBZABCULDEULULGHUL
      JKULULMUMVFVIVLUNUGABCDEFIKLMKGHJNOPQUDRSTUAUBUCUEUFUOUPZUQZURAVDVEVNUSAV
      GVHAVFVIVLVMUTZURAVGVHVOUSAVJVKAVFVIVLVMVAZURAVJVKVPUSVC $.
  $}

