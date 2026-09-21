$[ set-main.mm $]
$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Mathbox for Jim Kingdon
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Circle constant
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Lemma for tau-related theorems.  (Contributed by Jim Kingdon,
     16-Feb-2019.) $)
  taupilem3 $p |- ( A e. ( RR+ i^i ( `' cos " { 1 } ) ) <->
                 ( A e. RR+ /\ ( cos ` A ) = 1 ) ) $=
    ( crp ccos ccnv c1 csn cima cin wcel wa cfv wceq elin cc wf wfn wb cosf ffn
    fniniseg mp2b rpcn biantrurd bitr4id pm5.32i bitri ) ABCDEFGZHIABIZAUGIZJUH
    ACKELZJABUGMUHUIUJUHUIANIZUJJZUJNNCOCNPUIULQRNNCSNEACTUAUHUKUJAUBUCUDUEUF
    $.

  ${
    $d x y $.  $d A x $.
    $( A set of positive reals has (in the reals) a lower bound.  (Contributed
       by Jim Kingdon, 19-Feb-2019.) $)
    taupilemrplb $p |- E. x e. RR A. y e. ( RR+ i^i A ) x <_ y $=
      ( cc0 cr wcel cle wbr crp cin wral wrex 0re inss1 sseli rpge0d rgen breq1
      cv wceq ralbidv rspcev mp2an ) DEFDBSZGHZBICJZKZASZUDGHZBUFKZAELMUEBUFUDU
      FFUDUFIUDICNOPQUJUGADEUHDTUIUEBUFUHDUDGRUAUBUC $.
  $}

  $( Lemma for ~ taupi .  A positive real whose cosine is one is at least
     ` 2 x. _pi ` .  (Contributed by Jim Kingdon, 19-Feb-2019.) $)
  taupilem1 $p |- ( ( A e. RR+ /\ ( cos ` A ) = 1 ) ->
      ( 2 x. _pi ) <_ A ) $=
    ( crp wcel ccos c1 wa c2 cpi co cle wbr cdiv cr ax-mp cc0 clt adantr wb syl
    rpre cfv wceq cmul 2rp pirp rpmulcl mp2an recni rpgt0 dividi rpdivcl rpgt0d
    gt0ne0ii mpan2 cz cc rpcn coseq1 biimpa zgt0ge1 mpbid pm3.2i lediv1 mp3an13
    eqbrtrid mpbird ) ABCZADUAEUBZFZGHUCIZAJKZVJVJLIZAVJLIZJKZVIVLEVMJVJVJVJBCZ
    VJMCZGBCHBCVOUDUEGHUFUGZVJTNZUHVJVRVOOVJPKZVQVJUINZUMUJVIOVMPKZEVMJKZVGWAVH
    VGVOWAVQVGVOFVMAVJUKULUNQVIVMUOCZWAWBRVGVHWCVGAUPCVHWCRAUQAURSUSVMUTSVAVEVI
    AMCZVKVNRZVGWDVHATQVPWDVPVSFWEVRVPVSVRVTVBVJAVJVCVDSVF $.

  ${
    $d x y $.
    $( Lemma for ~ taupi .  The smallest positive real whose cosine is one is
       at most ` 2 x. _pi ` .  (Contributed by Jim Kingdon, 19-Feb-2019.)
       (Revised by AV, 1-Oct-2020.) $)
    taupilem2 $p |- _tau <_ ( 2 x. _pi ) $=
      ( vx vy ctau crp ccos ccnv c1 csn cima cin cr clt cinf c2 cpi cmul cle cv
      wbr wcel co df-tau wss wral wrex inss1 rpssre sstri taupilemrplb cfv wceq
      2rp pirp rpmulcl mp2an cos2pi taupilem3 mpbir2an infrelb mp3an eqbrtri )
      CDEFGHIZJZKLMZNOPUAZQUBVCKUCARBRQSBVCUDAKUEVEVCTZVDVEQSVCDKDVBUFUGUHABVBU
      IVFVEDTZVEEUJGUKNDTODTVGULUMNOUNUOUPVEUQURABVEVCUSUTVA $.
  $}

  ${
    $d x y $.
    $( Relationship between ` _tau ` and ` _pi ` .  This can be seen as
       connecting the ratio of a circle's circumference to its radius and the
       ratio of a circle's circumference to its diameter.  (Contributed by Jim
       Kingdon, 19-Feb-2019.)  (Revised by AV, 1-Oct-2020.) $)
    taupi $p |- _tau = ( 2 x. _pi ) $=
      ( vx vy ctau c2 cpi wceq cle wbr crp ccos c1 cr wral wcel mp2an taupilem3
      cv cfv mpbir2an df-tau cmul co taupilem2 ccnv csn cima cin clt wss c0 wne
      cinf wrex w3a wb inss1 rpssre sstri 2rp rpmulcl cos2pi ne0ii taupilemrplb
      pirp 3pm3.2i 2re pire remulcli infregelb taupilem1 sylbi mprgbir breqtrri
      wa infrecl ax-mp eqeltri letri3i ) CDEUAUBZFCVSGHVSCGHUCVSIJUDKUEUFZUGZLU
      HULZCGVSWBGHZVSAQZGHZAWAWALUIZWAUJUKZWDBQGHBWAMALUMZUNZVSLNWCWEAWAMUOWFWG
      WHWAILIVTUPUQURVSWAVSWANVSINZVSJRKFDINEINWJUSVDDEUTOVAVSPSVBABVTVCVEZDEVF
      VGVHZABAWAVSVIOWDWANWDINWDJRKFVNWEWDPWDVJVKVLTVMCVSCWBLTWIWBLNWKABWAVOVPV
      QWLVRS $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Number theory
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d M d z $.  $d N d z $.
    $( Alternate definition of the ` gcd ` operator.  (Contributed by Jim
       Kingdon, 31-Dec-2021.) $)
    dfgcd3 $p |- ( ( M e. ZZ /\ N e. ZZ )
        -> ( M gcd N ) = ( iota_ d e. NN0 A. z e. ZZ
        ( z || d <-> ( z || M /\ z || N ) ) ) ) $=
      ( cz wcel wa cv cdvds wbr wb wral cn0 wceq wi syl simpr breq1 w3a adantr
      crio cgcd co gcdcl simplr nn0zd iddvds anbi12d bibi12d rspcv mpbid biimpr
      ralimi cc0 cle dfgcd2 nn0ge0d 3biant1d bitr4d mpbir2and ex dvdsgcdb 3coml
      sylc bicomd ad4ant124 breq2 bibi1d mpbird ralrimiva impbid riota5 eqcomd
      ad2antlr ) BEFZCEFZGZAHZDHZIJZVRBIJZVRCIJZGZKZAELZDMUABCUBUCZVQWEDMWFBCUD
      VQVSMFZGZWEVSWFNZWHWEWIWHWEGZWIVSBIJZVSCIJZGZWCVTOZAELZWJVSVSIJZWMWJVSEFZ
      WPWJVSVQWGWEUEUFZVSUGPWJWQWEWPWMKZWRWHWEQZWDWSAVSEVRVSNZVTWPWCWMVRVSVSIRX
      AWAWKWBWLVRVSBIRVRVSCIRUHUIUJVDUKWJWEWOWTWDWNAEVTWCULUMPWHWIWMWOGZKWEWHWI
      UNVSUOJZWMWOSZXBVQWIXDKWGVSABCUPTWHWOWMXCWHVSVQWGQUQURUSTUTVAVQWIWEOWGVQW
      IWEVQWIGZWDAEXEVREFZGWDVRWFIJZWCKZVOVPXFXHWIXFVOVPXHXFVOVPSWCXGVRBCVBVEVC
      VFWIWDXHKVQXFWIVTXGWCVSWFVRIVGVHVNVIVJVATVKVLVM $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Real numbers
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    irrdifflemf.a $e |- ( ph -> A e. RR ) $.
    irrdifflemf.irr $e |- ( ph -> -. A e. QQ ) $.
    irrdifflemf.q $e |- ( ph -> Q e. QQ ) $.
    irrdifflemf.r $e |- ( ph -> R e. QQ ) $.
    irrdifflemf.qr $e |- ( ph -> Q =/= R ) $.
    $( Lemma for ~ irrdiff .  The forward direction.  (Contributed by Jim
       Kingdon, 20-May-2024.) $)
    irrdifflemf $p |- ( ph -> ( abs ` ( A - Q ) ) =/= ( abs ` ( A - R ) ) ) $=
      ( co wceq wfal wa simpr cc wcel adantr cq syl2anc c2 cmin cabs cfv wi wne
      cneg simplll simpllr simplr 3eqtr3d recnd cr qre subcand pm2.21ddne caddc
      syl cdiv 2cnd cc0 2ne0 a1i cmul negsubdi2d eqtrd addsubeq4d mpbird eqtr4d
      2timesd mvllmuld qaddcl cz 2z zq mp1i qdivcl syl3anc eqeltrd wn pm2.21fal
      wo resubcld absord ad2antrr mpjaodan 3eqtr3rd wb ad3antrrr negcon2 neg11d
      mpbid ex df-ne dfnot bitri sylibr ) ABCUAJZUBUCZBDUAJZUBUCZKZLUDZWRWTUEZA
      XALAXAMZWRWQKZLWRWQUFZKZXDXEMZWTWSKZLWTWSUFZKZXHXIMZAWQWSKZLAXAXEXIUGXLWR
      WTWQWSAXAXEXIUHXDXEXIUIXHXINUJAXMMZLCDXNBCDABOPZXMABEUKZQACOPZXMACACRPZCU
      LPGCUMUQZUKZQADOPZXMADADRPZDULPHDUMUQZUKZQAXMNUNACDUEXMIQUOZSXHXKMZAWQXJK
      ZLAXAXEXKUGYFWRWTWQXJAXAXEXKUHXDXEXKUIXHXKNUJAYGMZBRPZYHBCDUPJZTURJZRYHTB
      YJYHUSAXOYGXPQZTUTUEZYHVAVBZYHTBVCJBBUPJZYJYHBYLVIYHYJYOKWQDBUAJZKYHWQXJY
      PAYGNYHBDYLAYAYGYDQZVDVEYHCDBBAXQYGXTQYQYLYLVFVGVHVJYHYJRPZTRPZYMYKRPYHXR
      YBYRAXRYGGQAYBYGHQCDVKSTVLPYSYHVMTVNVOYNYJTVPVQVRAYIVSYGFQVTZSAXIXKWAZXAX
      EAWSABDEYCWBZWCZWDWEXDXGMZXILXKUUDXIMZAYGLAXAXGXIUGUUEWSXFKZYGUUEWRWTXFWS
      AXAXGXIUHXDXGXIUIUUDXINWFUUEWSOPZWQOPZUUFYGWGAUUGXAXGXIAWSUUBUKZWHAUUHXAX
      GXIAWQABCEXSWBZUKZWHWSWQWISWKYTSUUDXKMZAXMLAXAXGXKUGUULWQWSAUUHXAXGXKUUKW
      HAUUGXAXGXKUUIWHUULWRWTXFXJAXAXGXKUHXDXGXKUIUUDXKNUJWJYESAUUAXAXGUUCWDWEA
      XEXGWAXAAWQUUJWCQWEWLXCXAVSXBWRWTWMXAWNWOWP $.
  $}

  ${
    $d A q r $.
    $( The irrationals are exactly those reals that are a different distance
       from every rational.  (Contributed by Jim Kingdon, 19-May-2024.) $)
    irrdiff $p |- ( A e. RR -> ( -. A e. QQ <-> A. q e. QQ A. r e. QQ
        ( q =/= r -> ( abs ` ( A - q ) ) =/= ( abs ` ( A - r ) ) ) ) ) $=
      ( cr wcel cq wne cmin co cabs cfv wi wa clt wbr cc0 wceq neeq12d fveq2d
      c1 wn cv wral simplll simpllr simplrl simplrr simpr irrdifflemf ex simplr
      ralrimivva caddc peano2rem cneg recn 1cnd negsubd neg1lt0 0lt1 neg1rr 0re
      1re lttri mp2an 1red id ltadd2d mpbii eqbrtrrd ltned ad2antrr cz 1z ax-mp
      a1i qsubcl mpan2 qaddcl adantl simpl oveq2 adantr imbi12d rspc2gv syl2an2
      zq neirr nncand subnegd oveq2d recnd eqtr3d absnegd eqtrd mtbiri pm2.65da
      mp2d impbida ) ADEZAFEZUAZCUBZBUBZGZAXCHIZJKZAXDHIZJKZGZLZBFUCCFUCZWTXBMZ
      XKCBFFXMXCFEZXDFEZMZMZXEXJXQXEMAXCXDWTXBXPXEUDWTXBXPXEUEXMXNXOXEUFXMXNXOX
      EUGXQXEUHUIUJULWTXLMZXAAATHIZHIZJKZAATUMIZHIZJKZGZXRXAMXLXSYBGZYEWTXLXAUK
      WTYFXLXAWTXSYBAUNWTATUOZUMIZXSYBNWTATAUPZWTUQZURWTYGTNOZYHYBNOYGPNOPTNOYK
      USUTYGPTVAVBVCVDVEWTYGTAYGDEWTVAVPZWTVFWTVGVHVIVJVKVLXAXSFEZXRYBFEZXLYFYE
      LZLXATFEZYMTVMEYPVNTWGVOZATVQVRXAYNXRXAYPYNYQATVSVRVTXKYOCBXSYBFFXCXSQZXD
      YBQZMZXEYFXJYEYTXCXSXDYBYRYSWAYRYSUHRYTXGYAXIYDYTXFXTJYRXFXTQYSXCXSAHWBWC
      SYTXHYCJYSXHYCQYRXDYBAHWBVTSRWDWEWFWRWTYEUAXLXAWTYETJKZUUAGUUAWHWTYAUUAYD
      UUAWTXTTJWTATYIYJWISWTYDYGJKUUAWTYCYGJWTAAYGHIZHIYCYGWTUUBYBAHWTATYIYJWJW
      KWTAYGYIWTYGYLWLWIWMSWTTYJWNWORWPVLWQWS $.
  $}

  ${
    $d A q r s $.
    $( The rationals are exactly those reals for which there exist two distinct
       rationals that are the same distance from the original number.  Similar
       to ~ irrdiff but here proved with a proof which would also work in
       constructive mathematics.  From an online post by Ingo Blechschmidt.
       For a proof using ~ irrdiff , see ~ qdiffALT .  (Contributed by Jim
       Kingdon, 24-Apr-2026.) $)
    qdiff $p |- ( A e. RR -> ( A e. QQ <-> E. q e. QQ E. r e. QQ
        ( q =/= r /\ ( abs ` ( A - q ) ) = ( abs ` ( A - r ) ) ) ) ) $=
      ( wcel cq wne cmin co cabs cfv wceq wa caddc cc0 cexp cmul syl2anc subcld
      c1 c2 cr cv neeq1 oveq2 fveqeq2d anbi12d rexbidv cz 1z ax-mp qsubcl mpan2
      wrex qaddcl qre crp 1rp pm3.2i rpaddcl mp1i ltaddrpd ltned neneqd neqcomd
      zq qcn 1cnd addassd eqeq1d mtbird addcld subadd2d neqned absnegd subsub4d
      subidd oveq1d df-neg eqtr4di eqtr3d fveq2d nncand 3eqtr4rd neeq2 syl12anc
      cneg eqeq2d rspcev rspcedvdw cdiv 2cnd simpll simplrl qred mulcld simplrr
      recnd subdid sqcld nnncan1d simprr wb resubcld sqabs cc binom2sub 3eqtr3d
      mpbird addsubeq4d mpbid 3eqtr2d a1i divmuld eqtr4d halfcld simprl subne0d
      2ne0 divmul3d qsqcl syl 2z qdivcl syl3anc eqeltrrd ex rexlimdvva impbid2
      ) AUADZAEDZCUBZBUBZFZAYKGHZIJAYLGHZIJZKZLZBEUMZCEUMYJYSASGHZYLFZAYTGHZIJZ
      YPKZLZBEUMZCYTEYKYTKZYRUUEBEUUGYMUUAYQUUDYKYTYLUCUUGYNUUBYPIYKYTAGUDUEUFU
      GYJSEDZYTEDSUHDUUHUISVEUJZASUKULYJASMHZEDZYTUUJFZUUCAUUJGHZIJZKZUUFYJUUHU
      UKUUIASUNULYJYTUUJYJYTUUJKUUJSMHZAKZYJUUQASSMHZMHZAKYJAUUSYJAUUSYJAUUSAUO
      ZYJAUURUUTSUPDZUVALUURUPDYJUVAUVAUQUQURSSUSUTVAVBVCVDYJUUPUUSAYJASSAVFZYJ
      VGZUVCVHVIVJYJASUUJUVBUVCYJASUVBUVCVKVLVJVMYJSWFZIJSIJUUNUUCYJSUVCVNYJUUM
      UVDIYJAAGHZSGHZUUMUVDYJAASUVBUVBUVCVOYJUVFNSGHUVDYJUVENSGYJAUVBVPVQSVRVSV
      TWAYJUUBSIYJASUVBUVCWBWAWCUUEUULUUOLBUUJEYLUUJKZUUAUULUUDUUOYLUUJYTWDUVGY
      PUUNUUCUVGYOUUMIYLUUJAGUDWAWGUFWHWEWIYIYRYJCBEEYIYKEDZYLEDZLZLZYRYJUVKYRL
      ZYKTOHZYLTOHZGHZTWJHZYKYLGHZWJHZAEUVLUVRAKUVPAUVQPHZKUVLUVPAYKPHZAYLPHZGH
      ZUVSUVLUVPUWBKTUWBPHZUVOKUVLUWCTUVTPHZTUWAPHZGHATOHZUWEGHZUWFUWDGHZGHZUVO
      UVLTUVTUWAUVLWKZUVLAYKUVLAYIUVJYRWLZWQZUVLYKUVLYKYIUVHUVIYRWMZWNZWQZWOZUV
      LAYLUWLUVLYLUVLYLYIUVHUVIYRWPZWNZWQZWOZWRUVLUWFUWEUWDUVLAUWLWSZUVLTUWAUWJ
      UWTWOZUVLTUVTUWJUWPWOZWTUVLUWHUVMMHZUWGUVNMHZKUWIUVOKUVLYNTOHZYOTOHZUXDUX
      EUVLUXFUXGKZYQUVKYMYQXAUVLYNUADYOUADUXHYQXBUVLAYKUWKUWNXCUVLAYLUWKUWRXCYN
      YOXDQXHUVLAXEDZYKXEDUXFUXDKUWLUWOAYKXFQUVLUXIYLXEDUXGUXEKUWLUWSAYLXFQXGUV
      LUWHUVMUWGUVNUVLUWFUWDUXAUXCRUVLYKUWOWSZUVLUWFUWEUXAUXBRUVLYLUWSWSZXIXJXK
      UVLUVOTUWBUVLUVMUVNUXJUXKRZUWJUVLUVTUWAUWPUWTRTNFZUVLXRXLZXMXHUVLAYKYLUWL
      UWOUWSWRXNUVLUVPAUVQUVLUVOUXLXOUWLUVLYKYLUWOUWSRUVLYKYLUWOUWSUVKYMYQXPXQZ
      XSXHUVLUVPEDZUVQEDZUVQNFUVREDUVLUVOEDZTEDZUXMUXPUVLUVMEDZUVNEDZUXRUVLUVHU
      XTUWMYKXTYAUVLUVIUYAUWQYLXTYAUVMUVNUKQTUHDUXSUVLYBTVEUTUXNUVOTYCYDUVLUVHU
      VIUXQUWMUWQYKYLUKQUXOUVPUVQYCYDYEYFYGYH $.
  $}

  ${
    $d A q r s $.
    $( Alternate proof of ~ qdiff .  This is a proof from ~ irrdiff using
       excluded middle in a variety of places.  (Contributed by Jim Kingdon,
       27-Apr-2026.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    qdiffALT $p |- ( A e. RR -> ( A e. QQ <-> E. q e. QQ E. r e. QQ
        ( q =/= r /\ ( abs ` ( A - q ) ) = ( abs ` ( A - r ) ) ) ) ) $=
      ( cr wcel cq cv wne cmin co cabs cfv wi wn wrex wceq wral rexnal2 irrdiff
      wa con1bid bitr2id df-an df-ne imbi2i xchbinxr 2rexbii bitr4di ) ADEZAFEZ
      CGZBGZHZAUKIJKLZAULIJKLZHZMZNZBFOCFOZUMUNUOPZTZBFOCFOUSUQBFQCFQZNUIUJUQCB
      FFRUIUJVBABCSUAUBVAURCBFFVAUMUTNZMUQUMUTUCUPVCUMUNUOUDUEUFUGUH $.
  $}

  $( The closed unit interval is equinumerous to the open unit interval.  Based
     on a Mastodon post by Michael Kinyon.  (Contributed by Jim Kingdon,
     4-Jun-2024.) $)
  iccioo01 $p |- ( 0 [,] 1 ) ~~ ( 0 (,) 1 ) $=
    ( cc0 c1 cicc co cioo cdom wbr cen c4 cdiv c2 cr wcel clt 4re 4pos cvv ovex
    wss cxr 4nn nnrecre ax-mp halfre 2lt4 2re 2pos ltrecii mpbi iccen mp3an 0xr
    1xr recgt0ii halflt1 iccssioo mp4an ssdomg mp2 endomtr mp2an ioossicc sbth
    cn ) ABCDZABEDZFGZVFVEFGZVEVFHGVEBIJDZBKJDZCDZHGZVKVFFGZVGVILMZVJLMVIVJNGZV
    LIVDMVNUAIUBUCUDKINGVOUEKIUFOUGPUHUIVIVJUJUKVFQMVKVFSZVMABERATMBTMAVINGVJBN
    GVPULUMIOPUNUOABVIVJUPUQVKVFQURUSVEVKVFUTVAVEQMVFVESVHABCRABVBVFVEQURUSVEVF
    VCVA $.


$( (End of Jim Kingdon's mathbox.) $)
