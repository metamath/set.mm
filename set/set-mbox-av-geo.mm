$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Elementary geometry (extension)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Auxiliary theorems
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( The function value of unordered pair of ordered pairs with first
     components 1 and 2 at 1.  (Contributed by AV, 4-Feb-2023.) $)
  fv1prop $p |- ( A e. V -> ( { <. 1 , A >. , <. 2 , B >. } ` 1 ) = A ) $=
    ( c1 cvv wcel c2 wne cop cpr cfv wceq 1ex 1ne2 fvpr1g mp3an13 ) DEFACFDGHDD
    AIGBIJKALMNDGABECOP $.

  $( The function value of unordered pair of ordered pairs with first
     components 1 and 2 at 1.  (Contributed by AV, 4-Feb-2023.) $)
  fv2prop $p |- ( B e. V -> ( { <. 1 , A >. , <. 2 , B >. } ` 2 ) = B ) $=
    ( c2 cvv wcel c1 wne cop cpr cfv wceq 2ex 1ne2 fvpr2g mp3an13 ) DEFBCFGDHDG
    AIDBIJKBLMNGDABECOP $.

  ${
    submuladdmuld.a $e |- ( ph -> A e. CC ) $.
    submuladdmuld.b $e |- ( ph -> B e. CC ) $.
    submuladdmuld.c $e |- ( ph -> C e. CC ) $.
    submuladdmuld.d $e |- ( ph -> D e. CC ) $.
    $( Transformation of a sum of a product of a difference and a product with
       the subtrahend of the difference.  (Contributed by AV, 2-Feb-2023.) $)
    submuladdmuld $p |- ( ph -> ( ( ( A - B ) x. C ) + ( B x. D ) )
                                = ( ( A x. C ) + ( B x. ( D - C ) ) ) ) $=
      ( cmin co cmul caddc subdird oveq1d mulcld subadd23d subdid eqcomd oveq2d
      3eqtrd ) ABCJKDLKZCELKZMKBDLKZCDLKZJKZUCMKUDUCUEJKZMKUDCEDJKLKZMKAUBUFUCM
      ABCDFGHNOAUDUEUCABDFHPACDGHPACEGIPQAUGUHUDMAUHUGACEDGIHRSTUA $.
  $}

  ${
    $d A t $.  $d B t $.  $d C t $.  $d E t $.  $d F t $.  $d ph t $.
    affinecomb1.a $e |- ( ph -> A e. RR ) $.
    affinecomb1.b $e |- ( ph -> B e. RR ) $.
    affinecomb1.c $e |- ( ph -> C e. RR ) $.
    affinecomb1.d $e |- ( ph -> B =/= C ) $.
    affinecomb1.e $e |- ( ph -> E e. RR ) $.
    affinecomb1.f $e |- ( ph -> F e. RR ) $.
    affinecomb1.g $e |- ( ph -> G e. RR ) $.
    ${
      $d S t $.
      affinecomb1.s $e |- S = ( ( G - F ) / ( C - B ) ) $.
      $( Combination of two real affine combinations, one class variable
         resolved.  (Contributed by AV, 22-Jan-2023.) $)
      affinecomb1 $p |- ( ph
                    -> ( E. t e. RR ( A = ( ( ( 1 - t ) x. B ) + ( t x. C ) )
                                   /\ E = ( ( ( 1 - t ) x. F ) + ( t x. G ) ) )
                         <-> E = ( ( S x. ( A - B ) ) + F ) ) ) $=
        ( co cmul recnd c1 cv cmin caddc wceq wa cr wrex wcel cdiv adantr simpr
        wi wne affineequivne wb oveq2 oveq1d oveq1 eqeq2d adantl eqidd resubcld
        oveq12d necomd subne0d redivcld remulcld readdcld mpbird div13d eqtr4di
        affineequiv4 oveq1i eqtr3d biimpd sylbid ex impd rexlimdva eleq1 eqcomd
        cc sylan9eqr biantrurd a1i 3eqtr4d 3bitr3d rspcedv impbid ) ACUABUBZUCR
        ZDSRZWKESRZUDRZUEZGWLHSRZWKISRZUDRZUEZUFZBUGUHGFCDUCRZSRZHUDRZUEZAXAXEB
        UGAWKUGUIZUFZWPWTXEXGWPWKXBEDUCRZUJRZUEZWTXEUMZXGCDEWKXGCACUGUIXFJUKTXG
        DADUGUIXFKUKTXGEAEUGUIXFLUKTXGWKAXFULTADEUNXFMUKUOXGXJXKXGXJUFWTGUAXIUC
        RZHSRZXIISRZUDRZUEZXEXJWTXPUPXGXJWSXOGXJWQXMWRXNUDXJWLXLHSWKXIUAUCUQZUR
        WKXIISUSVDUTVAXGXPXEUMXJXGXPXEXGXOXDGAXOXDUEXFAXIIHUCRZSRZHUDRZXOXDAXTX
        OUEXTXTUEAXTVBAXTHIXIAXTAXSHAXIXRAXBXHACDJKVCZAEDLKVCZAEDAELTZADKTZADEM
        VEVFZVGZAIHPOVCZVHOVITAHOTZAIPTZAXIYFTZVMVJAXSXCHUDAXSXRXHUJRZXBSRZXCAX
        BXHXRAXBYATAXHYBTAXRYGTYEVKZFYKXBSQVNZVLURVOUKUTVPUKVQVRVQVSVTAXAXEBXIU
        GYFAXJUFZWTGWKXRSRZHUDRZUEXAXEYOGHIWKYOGAGUGUIXJNUKTAHWCUIXJYHUKAIWCUIX
        JYIUKYOWKYOXFXIUGUIZAYRXJYFUKXJXFYRUPAWKXIUGWAVAVJTVMYOWPWTYOWOCXJAWOXL
        DSRZXIESRZUDRZCXJWMYSWNYTUDXJWLXLDSXQURWKXIESUSVDACUUAACUUAUEXIXIUEAXIV
        BACDEXIACJTYDYCYJMUOVJWBWDWBWEYOYQXDGYOYPXCHUDYOXSYLYPXCAXSYLUEXJYMUKXJ
        YPXSUEAWKXIXRSUSVAXCYLUEYOYNWFWGURUTWHWIWJ $.
    $}

    $d G t $.
    $( Combination of two real affine combinations, presented without fraction.
       (Contributed by AV, 22-Jan-2023.) $)
    affinecomb2 $p |- ( ph
                    -> ( E. t e. RR ( A = ( ( ( 1 - t ) x. B ) + ( t x. C ) )
                                   /\ E = ( ( ( 1 - t ) x. F ) + ( t x. G ) ) )
              <-> ( ( C - B ) x. E ) = ( ( ( G - F ) x. A )
                                         + ( ( F x. C ) - ( B x. G ) ) ) ) ) $=
      ( cmin co cmul caddc mulcld c1 cv wceq wa cr wrex cdiv affinecomb1 subcld
      recnd necomd subne0d divcld addcld mulcand adddid divcan2d oveq1d mulassd
      eqid subdid 3eqtr3d subdird oveq12d subadd23d eqtrd mulcomd oveq2d 3eqtrd
      nnncan2d eqeq2d 3bitr2d ) ACUABUBZPQZDRQVMERQSQUCFVNGRQVMHRQSQUCUDBUEUFFH
      GPQZEDPQZUGQZCDPQZRQZGSQZUCVPFRQZVPVTRQZUCWAVOCRQZGERQZDHRQZPQZSQZUCABCDE
      VQFGHIJKLMNOVQUTUHAFVTVPAFMUJAVSGAVQVRAVOVPAHGAHOUJZAGNUJZUIZAEDAEKUJZADJ
      UJZUIZAEDWKWLADELUKULZUMZACDACIUJZWLUIZTZWIUNWMWNUOAWBWGWAAWBVPVSRQZVPGRQ
      ZSQZWCEGRQZDGRQZPQZVODRQZPQZSQZWGAVPVSGWMWRWIUPAXAWCXEPQZXDSQXGAWSXHWTXDS
      AVPVQRQZVRRQVOVRRQWSXHAXIVOVRRAVOVPWJWMWNUQURAVPVQVRWMWOWQUSAVOCDWJWPWLVA
      VBAEDGWKWLWIVCVDAWCXEXDAVOCWJWPTAVODWJWLTAXBXCAEGWKWITADGWLWITUIVEVFAXFWF
      WCSAXFWDGDRQZPQZHDRQZXJPQZPQWDXLPQWFAXDXKXEXMPAXBWDXCXJPAEGWKWIVGADGWLWIV
      GVDAHGDWHWIWLVCVDAWDXLXJAGEWIWKTAHDWHWLTAGDWIWLTVJAXLWEWDPAHDWHWLVGVHVIVH
      VIVKVL $.
  $}

  ${
    affineid.f $e |- ( ph -> A e. CC ) $.
    affineid.x $e |- ( ph -> T e. CC ) $.
    $( Identity of an affine combination.  (Contributed by AV, 2-Feb-2023.) $)
    affineid $p |- ( ph -> ( ( ( 1 - T ) x. A ) + ( T x. A ) ) = A ) $=
      ( c1 cmin co cmul caddc 1cnd subdird mullidd oveq1d eqtrd mulcld npcand )
      AFCGHBIHZCBIHZJHBSGHZSJHBARTSJARFBIHZSGHTAFCBAKEDLAUABSGABDMNONABSDACBEDP
      QO $.
  $}

  $( Subtract the reciprocal of 1 minus a number from 1 results in the number
     divided by the number minus 1.  (Contributed by AV, 15-Feb-2023.) $)
  1subrec1sub $p |- ( ( A e. CC /\ A =/= 1 )
                    -> ( 1 - ( 1 / ( 1 - A ) ) ) = ( A / ( A - 1 ) ) ) $=
    ( cc wcel c1 wne wa cmin co cdiv cmul 1cnd simpl subcld simpr necomd eqcomd
    subne0d oveq1d cneg eqtrd divcan4d mulcld divsubdird mullidd adantr negsubd
    negcl caddc mvrladdd divneg2d divnegd negsubdi2d oveq2d 3eqtr3d 3eqtr2d ) A
    BCZADEZFZDDDAGHZIHZGHDUSJHZUSIHZUTGHVADGHZUSIHZAADGHZIHZURDVBUTGURVBDURDUSU
    RKZURDAVGUPUQLZMZURDAVGVHURADUPUQNOQZUAPRURVADUSURDUSVGVIUBVGVIVJUCURVDASZU
    SIHZVFURVCVKUSIURVCUSDGHVKURVAUSDGURUSVIUDRURUSDVKVGUPVKBCUQAUGUEURDVKUHHUS
    URDAVGVHUFPUITRURAUSIHSAUSSZIHVLVFURAUSVHVIVJUJURAUSVHVIVJUKURVMVEAIURDAVGV
    HULUMUNTUO $.

  ${
    resum2sqcl.q $e |- Q = ( ( A ^ 2 ) + ( B ^ 2 ) ) $.
    $( The sum of two squares of real numbers is a real number.  (Contributed
       by AV, 7-Feb-2023.) $)
    resum2sqcl $p |- ( ( A e. RR /\ B e. RR ) -> Q e. RR ) $=
      ( cr wcel wa c2 cexp co caddc simpl resqcld simpr readdcld eqeltrid ) AEF
      ZBEFZGZCAHIJZBHIJZKJEDSTUASAQRLMSBQRNMOP $.

    $( The sum of the square of a nonzero real number and the square of another
       real number is greater than zero.  (Contributed by AV, 7-Feb-2023.) $)
    resum2sqgt0 $p |- ( ( ( A e. RR /\ A =/= 0 ) /\ B e. RR ) -> 0 < Q ) $=
      ( cr wcel cc0 wne wa c2 co caddc clt simpl resqcld adantr simpr wbr sqgt0
      cexp cle sqge0 adantl addgtge0d breqtrrdi ) AEFZAGHZIZBEFZIZGAJTKZBJTKZLK
      CMUJUKULUHUKEFUIUHAUFUGNOPUJBUHUIQOUHGUKMRUIASPUIGULUARUHBUBUCUDDUE $.

    $( The sum of the square of a nonzero real number and the square of another
       real number is a positive real number.  (Contributed by AV,
       2-May-2023.) $)
    resum2sqrp $p |- ( ( ( A e. RR /\ A =/= 0 ) /\ B e. RR ) -> Q e. RR+ ) $=
      ( cr wcel cc0 wne wa resum2sqcl adantlr resum2sqgt0 elrpd ) AEFZAGHZIBEFZ
      ICNPCEFOABCDJKABCDLM $.

    $( The sum of the square of two real numbers is greater than zero if at
       least one of the real numbers is nonzero.  (Contributed by AV,
       26-Feb-2023.) $)
    resum2sqorgt0 $p |- ( ( A e. RR /\ B e. RR /\ ( A =/= 0 \/ B =/= 0 ) )
                          -> 0 < Q ) $=
      ( cc0 wne cr wcel clt wi wa resum2sqgt0 ex expcom c2 cexp co caddc resqcl
      wbr wo com23 eqid breq2i adantl recnd ad2antrr addcomd breq2d bitrid jaoi
      mpbird 3imp31 ) AEFZBEFZUABGHZAGHZECITZUNUPUQURJZJUOUNUQUPURUQUNUPURJUQUN
      KUPURABCDLMNUBUPUOUSUPUOKZUQURUTUQKZUREBOPQZAOPQZRQZITZBAVDVDUCLUREVCVBRQ
      ZITVAVECVFEIDUDVAVFVDEIVAVCVBVAVCUQVCGHUTASUEUFVAVBUPVBGHUOUQBSUGUFUHUIUJ
      ULMNUKUM $.
  $}

  $( Membership in and outside of a closed real interval.  (Contributed by AV,
     15-Feb-2023.) $)
  reorelicc $p |- ( ( A e. RR /\ B e. RR /\ C e. RR )
                    -> ( C < A \/ C e. ( A [,] B ) \/ B < C ) ) $=
    ( cr wcel w3a clt wbr cicc co wo w3o cle wa wi orc a1d wn simp3 ad2antrr wb
    lenlt biimprd 3adant2 adantr imp simplr 3simpa elicc2 mpbir3and olcd expcom
    syl pm2.61i orcd ex olc a1i simp2 lelttric syl2anc mpjaod df-3or sylibr ) A
    DEZBDEZCDEZFZCAGHZCABIJEZKZBCGHZKZVIVJVLLVHCBMHZVMVLVHVNVMVHVNNZVKVLVIVOVKO
    VIVKVOVIVJPQVOVIRZVKVOVPNZVJVIVQVJVGACMHZVNVHVGVNVPVEVFVGSZTVOVPVRVHVPVROZV
    NVEVGVTVFVEVGNVRVPACUBUCUDUEUFVHVNVPUGVQVEVFNZVJVGVRVNFUAVHWAVNVPVEVFVGUHTA
    BCUIUMUJUKULUNUOUPVLVMOVHVLVKUQURVHVGVFVNVLKVSVEVFVGUSCBUTVAVBVIVJVLVCVD $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Real euclidean space of dimension 2
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    rrx2px.i $e |- I = { 1 , 2 } $.
    rrx2px.b $e |- P = ( RR ^m I ) $.
    $( The x-coordinate of a point in a real Euclidean space of dimension 2 is
       a real number.  (Contributed by AV, 2-Feb-2023.) $)
    rrx2pxel $p |- ( X e. P -> ( X ` 1 ) e. RR ) $=
      ( wcel cr c1 id c2 cpr 1ex prid1 eleqtrri a1i mapfvd ) CAFZGBCAHEQIHBFQHH
      JKBHJLMDNOP $.

    $( The y-coordinate of a point in a real Euclidean space of dimension 2 is
       a real number.  (Contributed by AV, 2-Feb-2023.) $)
    rrx2pyel $p |- ( X e. P -> ( X ` 2 ) e. RR ) $=
      ( wcel cr c2 id c1 cpr 2ex prid2 eleqtrri a1i mapfvd ) CAFZGBCAHEQIHBFQHJ
      HKBJHLMDNOP $.
  $}

  ${
    prelrrx2.i $e |- I = { 1 , 2 } $.
    prelrrx2.b $e |- P = ( RR ^m I ) $.
    $( An unordered pair of ordered pairs with first components 1 and 2 and
       real numbers as second components is a point in a real Euclidean space
       of dimension 2.  (Contributed by AV, 4-Feb-2023.) $)
    prelrrx2 $p |- ( ( A e. RR /\ B e. RR )
                     -> { <. 1 , A >. , <. 2 , B >. } e. P ) $=
      ( cr wcel wa c1 cop c2 cpr cmap co wf cvv pm3.2i a1i sylibr wne 1ne2 3jca
      w3a 1ex 2ex id fprg syl prssi fssd wb reex prex elmapg ax-mp oveq2i eqtri
      eleq2i ) AGHBGHIZJAKLBKMZGJLMZNOZHZVACHUTVBGVAPZVDUTVBABMZGVAUTJQHZLQHZIZ
      UTJLUAZUDVBVFVAPUTVIUTVJVIUTVGVHUEUFRSUTUGVJUTUBSUCJLABQQGGUHUIABGUJUKGQH
      ZVBQHZIVDVEULVKVLUMJLUNRGVBVAQQUOUPTCVCVACGDNOVCFDVBGNEUQURUST $.

    $d A x y $.  $d B x y $.  $d X x y $.  $d Y x y $.  $d Z x y $.
    $( An unordered pair of ordered pairs with first components 1 and 2 and
       real numbers as second components is a point in a real Euclidean space
       of dimension 2, determined by its coordinates.  (Contributed by AV,
       7-May-2023.) $)
    prelrrx2b $p |- ( ( ( A e. RR /\ B e. RR ) /\ ( X e. RR /\ Y e. RR ) )
                      -> ( ( Z e. P /\ ( ( ( Z ` 1 ) = A /\ ( Z ` 2 ) = B )
                                      \/ ( ( Z ` 1 ) = X /\ ( Z ` 2 ) = Y ) ) )
                            <-> Z e. { { <. 1 , A >. , <. 2 , B >. } ,
                                       { <. 1 , X >. , <. 2 , Y >. } } ) ) $=
      ( vx cr wcel wa c1 cfv wceq c2 wb eqeq1d adantl vy wo cop cpr cmap eleq2i
      wi co oveq2i bitri wf elmapi wrex wne 1ne2 1ex 2ex fprb ax-mp fveq1 fvpr1
      cv vex eqtrdi fvpr2 anbi12d opeq2 adantr preq12d eqeq2d biimpcd sylbid ex
      rexlimdvva biimtrid syl5 imp orim12d elprg ad2antlr mpbird elpri prelrrx2
      expl ad2antrr eleq1 cvv simpl a1i fvpr1g mp3an2i simpr jca orcd olcd jaod
      fvpr2g impbid ) AKLZBKLZMZEKLZFKLZMZMZGCLZNGOZAPZQGOZBPZMZXGEPZXIFPZMZUBZ
      MZGNAUCZQBUCZUDZNEUCZQFUCZUDZUDLZXEXFXOYCXEXFMZXOMYCGXSPZGYBPZUBZYDXOYGYD
      XKYEXNYFXEXFXKYEUGZXFGKNQUDZUEUHZLZXEYHXFGKDUEUHZLYKCYLGIUFYLYJGDYIKUEHUI
      UFUJZYKYIKGUKZXEYHGKYIULZYNGNJVBZUCZQUAVBZUCZUDZPZUAKUMJKUMZXEYHNQUNZYNUU
      BRUOJUANQKGUPUQURUSZXEUUAYHJUAKKXEYPKLYRKLMMZUUAYHUUEUUAMZXKYPAPZYRBPZMZY
      EUUAXKUUIRUUEUUAXHUUGXJUUHUUAXGYPAUUAXGNYTOZYPNGYTUTUUCUUJYPPUONQYPYRUPJV
      CVAUSVDZSUUAXIYRBUUAXIQYTOZYRQGYTUTUUCUULYRPUONQYPYRUQUAVCVEUSVDZSVFTUUAU
      UIYEUGUUEUUIUUAYEUUIYTXSGUUIYQXQYSXRUUGYQXQPUUHYPANVGVHUUHYSXRPUUGYRBQVGT
      VIVJVKTVLVMVNVOVPVOVQXEXFXNYFUGZXFYKXEUUNYMYKYNXEUUNYOYNUUBXEUUNUUDXEUUAU
      UNJUAKKUUEUUAUUNUUFXNYPEPZYRFPZMZYFUUAXNUUQRUUEUUAXLUUOXMUUPUUAXGYPEUUKSU
      UAXIYRFUUMSVFTUUAUUQYFUGUUEUUQUUAYFUUQYTYBGUUQYQXTYSYAUUOYQXTPUUPYPENVGVH
      UUPYSYAPUUOYRFQVGTVIVJVKTVLVMVNVOVPVOVQVRVQXFYCYGRXEXOGXSYBCVSVTWAWDYCYGX
      EXPGXSYBWBXEYEXPYFXEYEXPXEYEMZXFXOUURXFXSCLZXAUUSXDYEABCDHIWCWEYEXFUUSRXE
      GXSCWFTWAUURXKXNUURXKNXSOZAPZQXSOZBPZMZXAUVDXDYEXAUVAUVCNWGLZXAWSUUCUVAUP
      WSWTWHUUCXAUOWIZNQABWGKWJWKQWGLZXAWTUUCUVCUQWSWTWLUVFNQABWGKWQWKWMWEYEXKU
      VDRXEYEXHUVAXJUVCYEXGUUTANGXSUTSYEXIUVBBQGXSUTSVFTWAWNWMVMXEYFXPXEYFMZXFX
      OUVHXFYBCLZXDUVIXAYFEFCDHIWCVTYFXFUVIRXEGYBCWFTWAUVHXNXKUVHXNNYBOZEPZQYBO
      ZFPZMZXDUVNXAYFXDUVKUVMUVEXDXBUUCUVKUPXBXCWHUUCXDUOWIZNQEFWGKWJWKUVGXDXCU
      UCUVMUQXBXCWLUVONQEFWGKWQWKWMVTYFXNUVNRXEYFXLUVKXMUVMYFXGUVJENGYBUTSYFXIU
      VLFQGYBUTSVFTWAWOWMVMWPVPWR $.
  $}

  ${
    $d I i $.  $d X i $.  $d Y i $.
    rrx2pnecoorneor.i $e |- I = { 1 , 2 } $.
    rrx2pnecoorneor.b $e |- P = ( RR ^m I ) $.
    $( If two different points ` X ` and ` Y ` in a real Euclidean space of
       dimension 2 are different, then they are different at least at one
       coordinate.  (Contributed by AV, 26-Feb-2023.) $)
    rrx2pnecoorneor $p |- ( ( X e. P /\ Y e. P /\ X =/= Y )
                 -> ( ( X ` 1 ) =/= ( Y ` 1 ) \/ ( X ` 2 ) =/= ( Y ` 2 ) ) ) $=
      ( vi wcel wne c1 cfv wceq c2 wa wral fveq2 eqeq12d wfn cr elmapfn w3a cpr
      wn wo cv raleqi 1ex 2ex ralpr bitri bilanri wb cmap eleq2s anim12i adantr
      co eqfnfv syl mpbird ex necon3ad 3impia neorian sylibr ) CAHZDAHZCDIZUAJC
      KZJDKZLZMCKZMDKZLZNZUCZVIVJIVLVMIUDVFVGVHVPVFVGNZVOCDVQVOCDLZVQVONZVRGUEZ
      CKZVTDKZLZGBOZWDVOVQWDWCGJMUBZOVOWCGBWEEUFWCVKVNGJMUGUHVTJLWAVIWBVJVTJCPV
      TJDPQVTMLWAVLWBVMVTMCPVTMDPQUIUJUKVSCBRZDBRZNZVRWDULVQWHVOVFWFVGWGWFCSBUM
      UQZACSBTFUNWGDWIADSBTFUNUOUPGBCDURUSUTVAVBVCVIVJVLVMVDVE $.

    rrx2pnedifcoorneor.a $e |- A = ( ( Y ` 1 ) - ( X ` 1 ) ) $.
    ${
      rrx2pnedifcoorneor.b $e |- B = ( ( Y ` 2 ) - ( X ` 2 ) ) $.
      $( If two different points ` X ` and ` Y ` in a real Euclidean space of
         dimension 2 are different, then at least one difference of two
         corresponding coordinates is not 0.  (Contributed by AV,
         26-Feb-2023.) $)
      rrx2pnedifcoorneor $p |- ( ( X e. P /\ Y e. P /\ X =/= Y )
                                 -> ( A =/= 0 \/ B =/= 0 ) ) $=
        ( wcel wne cc0 wo c1 cfv wb cc wceq recnd c2 rrx2pnecoorneor cmin co wa
        neeq1i orbi12i rrx2pxel subeq0 syl2anr necon3bid rrx2pyel orbi12d necom
        w3a bitrdi bitrid 3adant3 mpbird ) ECKZFCKZEFLZUOAMLZBMLZNZOEPZOFPZLZUA
        EPZUAFPZLZNZCDEFGHUBUTVAVEVLQVBVEVGVFUCUDZMLZVJVIUCUDZMLZNZUTVAUEZVLVCV
        NVDVPAVMMIUFBVOMJUFUGVRVQVGVFLZVJVILZNVLVRVNVSVPVTVRVMMVGVFVAVGRKVFRKVM
        MSVGVFSQUTVAVGCDFGHUHTUTVFCDEGHUHTVGVFUIUJUKVRVOMVJVIVAVJRKVIRKVOMSVJVI
        SQUTVAVJCDFGHULTUTVICDEGHULTVJVIUIUJUKUMVSVHVTVKVGVFUNVJVIUNUGUPUQURUS
        $.
    $}

    rrx2pnedifcoorneorr.b $e |- B = ( ( X ` 2 ) - ( Y ` 2 ) ) $.
    $( If two different points ` X ` and ` Y ` in a real Euclidean space of
       dimension 2 are different, then at least one difference of two
       corresponding coordinates is not 0.  (Contributed by AV,
       26-Feb-2023.) $)
    rrx2pnedifcoorneorr $p |- ( ( X e. P /\ Y e. P /\ X =/= Y )
                                -> ( A =/= 0 \/ B =/= 0 ) ) $=
      ( wcel wne cc0 c2 cfv cmin co wceq wb wa wo eqid rrx2pnedifcoorneor eqcom
      w3a a1i cc rrx2pyel recnd anim12i ancomd 3adant3 subeq0 syl eqcomi eqeq1i
      3bitr4d bitrdi necon3bid orbi2d mpbid ) ECKZFCKZEFLZUEZAMLZNFOZNEOZPQZMLZ
      UAVFBMLZUAAVICDEFGHIVIUBUCVEVJVKVFVEVIMBMVEVIMRZVHVGPQZMRZBMRVEVGVHRZVHVG
      RZVLVNVOVPSVEVGVHUDUFVEVGUGKZVHUGKZTZVLVOSVBVCVSVDVBVCTVRVQVBVRVCVQVBVHCD
      EGHUHUIVCVGCDFGHUHUIUJZUKULVGVHUMUNVEVRVQTZVNVPSVBVCWAVDVTULVHVGUMUNUQVMB
      MBVMJUOUPURUSUTVA $.
  $}

  ${
    rrx2xpreen.r $e |- R = ( RR ^m { 1 , 2 } ) $.
    ${
      $d u v w x y z $.  $d F u v w z $.  $d R w z $.
      rrx2xpref1o.1 $e |- F = ( x e. RR , y e. RR
                                |-> { <. 1 , x >. , <. 2 , y >. } ) $.
      $( There is a bijection between the set of ordered pairs of real numbers
         (the cartesian product of the real numbers) and the set of points in
         the two dimensional Euclidean plane (represented as mappings from
         ` { 1 , 2 } ` to the real numbers).  (Contributed by AV,
         12-Mar-2023.) $)
      rrx2xpref1o $p |- F : ( RR X. RR ) -1-1-onto-> R $=
        ( vz vw vu vv cr cfv wceq wcel c1 cop c2 cpr opeq2 wa cxp wf1 wfo wf cv
        wf1o weq wi wral wfn prex fnmpoi c1st c2nd 1st2nd2 fveq2d df-ov eqtr4di
        co xp1st xp2nd preq1d preq2d ovmpo syl2anc eqtrd prelrrx2 eqeltrd ffnfv
        eqid rgen mpbir2an wo opex preq12b 1ex fvex simprbi 2ex anim12i a1d wne
        opth 1ne2 eqneqall mpi ad2antrr syl2anb jaoi sylbi com12 bitrdi 3imtr4d
        eqeqan12d rgen2 dff13 wrex w3a cmap eleq2i elmap wb 1re 2re fpr2g mp2an
        reex 3bitri eqeq2d rspc2ev 2rexbiia sylibr fveq2 rexxp dffo3 df-f1o ) K
        KUAZCDUFXQCDUBZXQCDUCZXRXQCDUDZGUEZDLZHUEZDLZMZGHUGZUHZHXQUIGXQUIXTDXQU
        JYBCNZGXQUIABKKOAUEZPZQBUEZPZRZDFYJYLUKULYHGXQYAXQNZYBOYAUMLZPZQYAUNLZP
        ZRZCYNYBYOYQDUSZYSYNYBYOYQPZDLYTYNYAUUADYAKKUOZUPYOYQDUQURYNYOKNZYQKNZY
        TYSMYAKKUTZYAKKVAZABYOYQKKYMYSDYPYLRYIYOMYJYPYLYIYOOSVBYKYQMYLYRYPYKYQQ
        SVCFYPYRUKVDVEVFZYNUUCUUDYSCNUUEUUFYOYQCOQRZUUHVJEVGVEVHVKGXQCDVIVLZYGG
        HXQXQYNYCXQNZTZYSOYCUMLZPZQYCUNLZPZRZMZYOUULMZYQUUNMZTZYEYFUUQUUKUUTUUQ
        YPUUMMZYRUUOMZTZYPUUOMZYRUUMMZTZVMUUKUUTUHZYPYRUUMUUOOYOVNQYQVNOUULVNQU
        UNVNVOUVCUVGUVFUVCUUTUUKUVAUURUVBUUSUVAOOMUUROYOOUULVPYAUMVQZWCVRUVBQQM
        UUSQYQQUUNVSYAUNVQZWCVRVTWAUVDOQMZYOUUNMZTQOMYQUULMTZUVGUVEOYOQUUNVPUVH
        WCQYQOUULVSUVIWCUVJUVGUVKUVLUVJOQWBUVGWDUVGOQWEWFWGWHWIWJWKYNUUJYBYSYDU
        UPUUGUUJYDUULUUNDUSZUUPUUJYDUULUUNPZDLUVMUUJYCUVNDYCKKUOZUPUULUUNDUQURU
        UJUULKNUUNKNUVMUUPMYCKKUTYCKKVAABUULUUNKKYMUUPDUUMYLRYIUULMYJUUMYLYIUUL
        OSVBYKUUNMYLUUOUUMYKUUNQSVCFUUMUUOUKVDVEVFWNUUKYFUUAUVNMUUTYNUUJYAUUAYC
        UVNUUBUVOWNYOYQUULUUNUVHUVIWCWLWMWOGHXQCDWPVLXSXTYCYBMZGXQWQZHCUIUUIUVQ
        HCYCCNZYCIUEZJUEZDUSZMZJKWQIKWQZUVQUVRYCOUVSPZQUVTPZRZMZJKWQIKWQZUWCUVR
        OYCLZKNQYCLZKNYCOUWIPZQUWJPZRZMZWRZUWHUVRYCKUUHWSUSZNUUHKYCUDZUWOCUWPYC
        EWTKUUHYCXGOQUKXAOKNQKNUWQUWOXBXCXDOQKYCKKXEXFXHUWGUWNYCUWKUWERZMIJUWIU
        WJKKUVSUWIMZUWFUWRYCUWSUWDUWKUWEUVSUWIOSVBXIUVTUWJMZUWRUWMYCUWTUWEUWLUW
        KUVTUWJQSVCXIXJWJUWBUWGIJKKUVSKNUVTKNTUWAUWFYCABUVSUVTKKYMUWFDUWDYLRAIU
        GYJUWDYLYIUVSOSVBBJUGYLUWEUWDYKUVTQSVCFUWDUWEUKVDXIXKXLUVPUWBGIJKKYAUVS
        UVTPZMZYBUWAYCUXBYBUXADLUWAYAUXADXMUVSUVTDUQURXIXNXLVKGHXQCDXOVLXQCDXPV
        L $.
    $}

    $d R f $.  $d f x y $.
    $( The set of points in the two dimensional Euclidean plane and the set of
       ordered pairs of real numbers (the cartesian product of the real
       numbers) are equinumerous.  (Contributed by AV, 12-Mar-2023.) $)
    rrx2xpreen $p |- R ~~ ( RR X. RR ) $=
      ( vf vx vy cr cxp cen wbr cv wf1o wex c1 cop cpr cmpo reex mpoex f1oeq1
      c2 eqid rrx2xpref1o ceqsexv2d bren mpbir ensymi ) FFGZAUGAHIUGACJZKZCLUIU
      GADEFFMDJNTEJNOZPZKCUKDEFFUJQQRUGAUHUKSDEAUKBUKUAUBUCUGACUDUEUF $.
  $}

  ${
    $d R x y $.  $d X x y $.  $d Y x y $.
    rrx2plord.o $e |- O = { <. x , y >. | ( ( x e. R /\ y e. R ) /\
               ( ( x ` 1 ) < ( y ` 1 ) \/ ( ( x ` 1 ) = ( y ` 1 )
                                            /\ ( x ` 2 ) < ( y ` 2 ) ) ) ) } $.
    $( The lexicographical ordering for points in the two dimensional Euclidean
       plane: a point is less than another point iff its first coordinate is
       less than the first coordinate of the other point, or the first
       coordinates of both points are equal and the second coordinate of the
       first point is less than the second coordinate of the other point:
       ` <. a , b >. <_ <. x , y >. ` iff
       ` ( a < x \/ ( a = x /\ b <_ y ) ) ` .  (Contributed by AV,
       12-Mar-2023.) $)
    rrx2plord $p |- ( ( X e. R /\ Y e. R )
                      -> ( X O Y <-> ( ( X ` 1 ) < ( Y ` 1 )
                                       \/ ( ( X ` 1 ) = ( Y ` 1 )
                                            /\ ( X ` 2 ) < ( Y ` 2 ) ) ) ) ) $=
      ( wbr cop cv wcel wa c1 cfv clt wceq c2 wo fveq1 breqan12d eleq2i anbi12d
      copab df-br bitri eqeqan12d orbi12d opelopab2a bitrid ) EFDHZEFIZAJZCKBJZ
      CKLMULNZMUMNZOHZUNUOPZQULNZQUMNZOHZLZRZLABUCZKZECKFCKLMENZMFNZOHZVEVFPZQE
      NZQFNZOHZLZRZUJUKDKVDEFDUDDVCUKGUAUEVBVMABEFCCULEPZUMFPZLZUPVGVAVLVNVOUNV
      EUOVFOMULESZMUMFSZTVPUQVHUTVKVNVOUNVEUOVFVQVRUFVNVOURVIUSVJOQULESQUMFSTUB
      UGUHUI $.

    $( The lexicographical ordering for points in the two dimensional Euclidean
       plane: a point is less than another point if its first coordinate is
       less than the first coordinate of the other point.  (Contributed by AV,
       12-Mar-2023.) $)
    rrx2plord1 $p |- ( ( X e. R /\ Y e. R /\ ( X ` 1 ) < ( Y ` 1 ) )
                       -> X O Y ) $=
      ( wcel c1 cfv clt wbr w3a wceq c2 wa wo simp3 orcd wb rrx2plord 3adant3
      mpbird ) ECHZFCHZIEJZIFJZKLZMZEFDLZUHUFUGNOEJOFJKLPZQZUIUHUKUDUEUHRSUDUEU
      JULTUHABCDEFGUAUBUC $.

    rrx2plord2.r $e |- R = ( RR ^m { 1 , 2 } ) $.
    $( The lexicographical ordering for points in the two dimensional Euclidean
       plane: if the first coordinates of two points are equal, a point is less
       than another point iff the second coordinate of the point is less than
       the second coordinate of the other point.  (Contributed by AV,
       12-Mar-2023.) $)
    rrx2plord2 $p |- ( ( X e. R /\ Y e. R /\ ( X ` 1 ) = ( Y ` 1 ) )
                       -> ( X O Y <-> ( X ` 2 ) < ( Y ` 2 ) ) ) $=
      ( wcel c1 cfv wceq w3a wbr clt c2 wa wi ex com12 wo rrx2plord 3adant3 wne
      wb cr cpr eqid rrx2pxel adantr ltne necomd sylan eqneqall syl9 3impia a1d
      simpr jaoi olc 3ad2ant3 impbid bitrd ) ECIZFCIZJEKZJFKZLZMZEFDNZVFVGONZVH
      PEKPFKONZQZUAZVLVDVEVJVNUEVHABCDEFGUBUCVIVNVLVNVIVLVKVIVLRVMVIVKVLVDVEVHV
      KVLRVDVEQZVKVFVGUDZVHVLVOVKVPVOVFUFIZVKVPVDVQVECJPUGZEVRUHHUIUJVQVKQVGVFV
      FVGUKULUMSVLVFVGUNUOUPTVMVLVIVHVLURUQUSTVHVDVLVNRVEVHVLVNVMVKUTSVAVBVC $.

    ${
      $d O a b c d e f $.  $d R a b x y $.  $d c d e f x y $.
      rrx2plordisom.f $e |- F = ( x e. RR , y e. RR
                                  |-> { <. 1 , x >. , <. 2 , y >. } ) $.
      rrx2plordisom.t $e |- T = { <. x , y >. |
                                ( ( x e. ( RR X. RR ) /\ y e. ( RR X. RR ) )
                                  /\ ( ( 1st ` x ) < ( 1st ` y ) \/
                                     ( ( 1st ` x ) = ( 1st ` y )
                                       /\ ( 2nd ` x ) < ( 2nd ` y ) ) ) ) } $.
      $( The set of points in the two dimensional Euclidean plane with the
         lexicographical ordering is isomorphic to the cartesian product of the
         real numbers with the lexicographical ordering implied by the ordering
         of the real numbers.  (Contributed by AV, 12-Mar-2023.) $)
      rrx2plordisom $p |- F Isom T , O ( ( RR X. RR ) , R ) $=
        ( cr c1 cop c2 wcel wa cfv clt wbr wceq va vb vc vd ve vf cxp wiso cmpo
        cv cpr c1st c2nd wo copab wf1o wb wral eqid rrx2xpref1o wex elxpi df-br
        wi opelxpi adantl eleq1 adantr mpbird fveq2 breqan12d eqeqan12d anbi12d
        orbi12d opelopab2a syl2an bitrid wne 1ne2 1ex vex fvpr1 breq12d eqeq12d
        mp1i 2ex fvpr2 prelrrx2 rrx2plord op1std op2ndd 3bitr4rd co eqtr4di cvv
        df-ov eqidd opeq2 preq12d simpl simpr a1i ovmpod sylan9eq eqcomd 3bitrd
        prex expcom exlimivv com12 imp rgen2 mpbir2an isoeq2 ax-mp mpbir isoeq1
        df-isom ) KKUGZCDFEUHZXSCDFABKKLAUJZMZNBUJZMZUKZUIZUHZYGXSCYAXSOYCXSOPY
        AULQZYCULQZRSZYHYITZYAUMQZYCUMQZRSZPZUNZPABUOZFYFUHZYRXSCYFUPUAUJZUBUJZ
        YQSZYSYFQZYTYFQZFSZUQZUBXSURUAXSURABCYFHYFUSUTUUEUAUBXSXSYSXSOZYSUCUJZU
        DUJZMZTZUUGKOZUUHKOZPZPZUDVAUCVAZYTUEUJZUFUJZMZTZUUPKOZUUQKOZPZPZUFVAUE
        VAZUUEYTXSOZUCUDYSKKVBUEUFYTKKVBUUOUVDUUEUUNUVDUUEVDUCUDUVDUUNUUEUVCUUN
        UUEVDUEUFUUNUVCUUEUUNUVCPZUUAYSULQZYTULQZRSZUVGUVHTZYSUMQZYTUMQZRSZPZUN
        ZLUUGMZNUUHMZUKZLUUPMZNUUQMZUKZFSZUUDUUAYSYTMYQOZUVFUVOYSYTYQVCUUNUUFUV
        EUWCUVOUQUVCUUNUUFUUIXSOZUUMUWDUUJUUGUUHKKVEVFUUJUUFUWDUQUUMYSUUIXSVGVH
        VIUVCUVEUURXSOZUVBUWEUUSUUPUUQKKVEVFUUSUVEUWEUQUVBYTUURXSVGVHVIYPUVOABY
        SYTXSXSYAYSTZYCYTTZPZYJUVIYOUVNUWFUWGYHUVGYIUVHRYAYSULVJZYCYTULVJZVKUWH
        YKUVJYNUVMUWFUWGYHUVGYIUVHUWIUWJVLUWFUWGYLUVKYMUVLRYAYSUMVJYCYTUMVJVKVM
        VNVOVPVQUVFLUVRQZLUWAQZRSZUWKUWLTZNUVRQZNUWAQZRSZPZUNZUUGUUPRSZUUGUUPTZ
        UUHUUQRSZPZUNUWBUVOUVFUWMUWTUWRUXCUVFUWKUUGUWLUUPRLNVRZUWKUUGTUVFVSLNUU
        GUUHVTUCWAZWBWEZUXDUWLUUPTUVFVSLNUUPUUQVTUEWAZWBWEZWCUVFUWNUXAUWQUXBUVF
        UWKUUGUWLUUPUXFUXHWDUVFUWOUUHUWPUUQRUXDUWOUUHTUVFVSLNUUGUUHWFUDWAZWGWEU
        XDUWPUUQTUVFVSLNUUPUUQWFUFWAZWGWEWCVMVNUUNUVRCOZUWACOZUWBUWSUQUVCUUMUXK
        UUJUUGUUHCLNUKZUXMUSZHWHVFUVBUXLUUSUUPUUQCUXMUXNHWHVFABCFUVRUWAGWIVPUVF
        UVIUWTUVNUXCUUNUVCUVGUUGUVHUUPRUUJUVGUUGTUUMUUGUUHYSUXEUXIWJVHZUUSUVHUU
        PTUVBUUPUUQYTUXGUXJWJVHZVKUVFUVJUXAUVMUXBUUNUVCUVGUUGUVHUUPUXOUXPVLUUNU
        VCUVKUUHUVLUUQRUUJUVKUUHTUUMUUGUUHYSUXEUXIWKVHUUSUVLUUQTUVBUUPUUQYTUXGU
        XJWKVHVKVMVNWLUUNUVCUVRUUBUWAUUCFUUNUUBUVRUUJUUMUUBUUGUUHYFWMZUVRUUJUUB
        UUIYFQUXQYSUUIYFVJUUGUUHYFWPWNUUMABUUGUUHKKYEUVRYFWOUUMYFWQYAUUGTZYCUUH
        TZPZYEUVRTUUMUXTYBUVPYDUVQUXRYBUVPTUXSYAUUGLWRVHUXSYDUVQTUXRYCUUHNWRVFW
        SVFUUKUULWTUUKUULXAUVRWOOUUMUVPUVQXGXBXCXDXEUVCUUCUWAUUSUVBUUCUUPUUQYFW
        MZUWAUUSUUCUURYFQUYAYTUURYFVJUUPUUQYFWPWNUVBABUUPUUQKKYEUWAYFWOUVBYFWQY
        AUUPTZYCUUQTZPZYEUWATUVBUYDYBUVSYDUVTUYBYBUVSTUYCYAUUPLWRVHUYCYDUVTTUYB
        YCUUQNWRVFWSVFUUTUVAWTUUTUVAXAUWAWOOUVBUVSUVTXGXBXCXDXEVKXFXHXIXJXIXKVP
        XLUAUBXSCYQFYFXRXMDYQTYGYRUQJXSCDFYQYFXNXOXPEYFTXTYGUQIXSCDFYFEXQXOXP
        $.
    $}

    $( The lexicographical ordering for points in the two dimensional Euclidean
       plane is a strict total ordering.  (Contributed by AV, 12-Mar-2023.) $)
    rrx2plordso $p |- O Or R $=
      ( cr cxp cv wcel wa c1st cfv clt wbr c2nd wor ltso eqid cop wceq wo copab
      soxp mp2an c1 c2 cpr cmpo wiso wb rrx2plordisom isoso ax-mp mpbi ) GGHZAI
      ZUPJBIZUPJKUQLMZURLMZNOUSUTUAUQPMURPMNOKUBKABUCZQZCDQZGNQZVDVBRRABGGNNVAV
      ASZUDUEUPCVADABGGUFUQTUGURTUHUIZUJVBVCUKABCVAVFDEFVFSVEULUPCVADVFUMUNUO
      $.
  $}

  ${
    ehl2eudisval0.e $e |- E = ( EEhil ` 2 ) $.
    ehl2eudisval0.x $e |- X = ( RR ^m { 1 , 2 } ) $.
    ehl2eudisval0.d $e |- D = ( dist ` E ) $.
    ehl2eudisval0.0 $e |- .0. = ( { 1 , 2 } X. { 0 } ) $.
    $( The Euclidean distance of a point to the origin in a real Euclidean
       space of dimension 2.  (Contributed by AV, 26-Feb-2023.) $)
    ehl2eudisval0 $p |- ( F e. X -> ( F D .0. ) = ( sqrt ` ( ( ( F ` 1 ) ^ 2 )
                                                   + ( ( F ` 2 ) ^ 2 ) ) ) ) $=
      ( wcel co c1 cfv cmin c2 cexp caddc wceq cvv cc0 prex rrx0el ehl2eudisval
      csqrt cpr mp1i mpdan cop csn cxp 1ex c0ex xpprsng mp3an eqtri fveq1i 1ne2
      2ex wne fvpr1 ax-mp oveq2d eqid rrx2pxel recnd subid1d eqtrd oveq1d fvpr2
      a1i eqtrid rrx2pyel oveq12d fveq2d ) CDJZCEAKZLCMZLEMZNKZOPKZOCMZOEMZNKZO
      PKZQKZUDMZVQOPKZWAOPKZQKZUDMVOEDJZVPWFRLOUEZSJWJVOLOUADWKSEIGUBUFABCEDFGH
      UCUGVOWEWIUDVOVTWGWDWHQVOVSVQOPVOVSVQTNKVQVOVRTVQNVRTRVOVRLLTUHOTUHUEZMZT
      LEWLEWKTUIUJZWLILSJOSJTSJWNWLRUKURULLOTSSSUMUNUOZUPLOUSZWMTRUQLOTTUKULUTV
      AUOVJVBVOVQVOVQDWKCWKVCZGVDVEVFVGVHVOWCWAOPVOWCWATNKWAVOWBTWANVOWBOWLMZTO
      EWLWOUPWPWRTRVOUQLOTTURULVIUFVKVBVOWAVOWADWKCWQGVLVEVFVGVHVMVNVG $.

    $( An upper bound of the Euclidean distance of a point to the origin in a
       real Euclidean space of dimension 2.  (Contributed by AV,
       9-May-2023.) $)
    ehl2eudis0lt $p |- ( ( F e. X /\ R e. RR+ ) -> ( ( F D .0. ) < R
               <-> ( ( ( F ` 1 ) ^ 2 ) + ( ( F ` 2 ) ^ 2 ) ) < ( R ^ 2 ) ) ) $=
      ( wcel wa co clt wbr c2 cexp cr cc0 cle crp cfv caddc csqrt ehl2eudisval0
      c1 wceq adantr breq1d wb eqid rrx2pxel rrx2pyel resum2sqcl syl2anc resqcl
      cpr anim12i sqge0 addge0 resqrtcld sqrtge0d rprege0 lt2sq syl2an resqrtth
      jca syl 3bitrd ) DEKZBUAKZLZDFAMZBNOUFDUBZPQMZPDUBZPQMZUCMZUDUBZBNOZVSPQM
      ZBPQMZNOZVRWBNOVLVMVSBNVJVMVSUGVKACDEFGHIJUEUHUIVJVSRKZSVSTOZLBRKSBTOLVTW
      CUJVKVJWDWEVJVRVJVNRKZVPRKZVRRKZEUFPUQZDWIUKZHULZEWIDWJHUMZVNVPVRVRUKUNUO
      ZVJWFWGSVRTOZWKWLWFWGLVORKZVQRKZLSVOTOZSVQTOZLWNWFWOWGWPVNUPVPUPURWFWQWGW
      RVNUSVPUSURVOVQUTUOUOZVAVJVRWMWSVBVGBVCVSBVDVEVLWAVRWBNVLWHWNLZWAVRUGVJWT
      VKVJWHWNWMWSVGUHVRVFVHUIVI $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Spheres and lines in real Euclidean spaces
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $c LineM Sphere $.

  $( Declare the syntax for lines in generalized real Euclidean spaces. $)
  cline $a class LineM $.

  $( Declare the syntax for spheres in generalized real Euclidean spaces. $)
  csph $a class Sphere $.

  ${
    $d p t w x y $.
    $( Definition of lines passing through two different points in a left
       module (or any extended structure having a base set, an addition, and a
       scalar multiplication).  (Contributed by AV, 14-Jan-2023.) $)
    df-line $a |- LineM = ( w e. _V |-> ( x e. ( Base ` w ) ,
                                         y e. ( ( Base ` w ) \ { x } )
                    |-> { p e. ( Base ` w ) | E. t e. ( Base ` ( Scalar ` w ) )
                          p = ( ( ( ( 1r ` ( Scalar ` w ) )
                                    ( -g ` ( Scalar ` w ) ) t ) ( .s ` w ) x )
                                ( +g ` w ) ( t ( .s ` w ) y ) ) } ) ) $.
  $}

  ${
    $d p r w x $.
    $( Definition of spheres for given centers and radii in a metric space (or
       more generally, in a distance space, see ~ distspace , or even in any
       extended structure having a base set and a distance function into the
       real numbers.  (Contributed by AV, 14-Jan-2023.) $)
    df-sph $a |- Sphere = ( w e. _V |-> ( x e. ( Base ` w ) ,
                                          r e. ( 0 [,] +oo )
                    |-> { p e. ( Base ` w ) | ( p ( dist ` w ) x ) = r } ) ) $.
  $}

  ${
    $d B p w x y $.  $d K t w $.  $d S t w $.  $d V w $.  $d W p t w x y $.
    $d .1. w $.  $d .- w $.  $d .x. w $.  $d .+ w $.
    lines.b $e |- B = ( Base ` W ) $.
    lines.l $e |- L = ( LineM ` W ) $.
    lines.s $e |- S = ( Scalar ` W ) $.
    lines.k $e |- K = ( Base ` S ) $.
    lines.p $e |- .x. = ( .s ` W ) $.
    lines.a $e |- .+ = ( +g ` W ) $.
    lines.m $e |- .- = ( -g ` S ) $.
    lines.1 $e |- .1. = ( 1r ` S ) $.
    $( The lines passing through two different points in a left module (or any
       extended structure having a base set, an addition, and a scalar
       multiplication).  (Contributed by AV, 14-Jan-2023.) $)
    lines $p |- ( W e. V -> L = ( x e. B , y e. ( B \ { x } )
                   |-> { p e. B | E. t e. K
                         p = ( ( ( .1. .- t ) .x. x ) .+ ( t .x. y ) ) } ) ) $=
      ( vw wcel cline cfv cv csn cdif co wceq wrex crab cmpo cbs csca cur cvsca
      csg cplusg cvv df-line fveq2 eqtrid difeq1d fveq2d fveq2i 2fveq3 oveq123d
      eqtri eqidd oveqd eqeq2d rexeqbidv rabeqbidv mpoeq123dv eqcomd elex fvexi
      eqcoms difexi mpoex a1i fvmptd3 ) MLUDZJMUEUFABDDAUGZUHZUIZNUGZHCUGZKUJZW
      FGUJZWJBUGZGUJZEUJZUKZCIULZNDUMZUNZPWEUCMABUCUGZUOUFZXAWGUIZWIWTUPUFZUQUF
      ZWJXCUSUFZUJZWFWTURUFZUJZWJWMXGUJZWTUTUFZUJZUKZCXCUOUFZULZNXAUMZUNZWSVAUE
      VAABUCCNVBXPWSUKMWTMWTUKZWSXPXQABDWHWRXAXBXOXQDMUOUFXAOMWTUOVCVDZXQDXAWGX
      RVEXQWQXNNDXAXRXQWPXLCIXMXQIFUOUFXMRXQFXCUOXQFMUPUFZXCQMWTUPVCVDVFVDXQWOX
      KWIXQWLXHWNXIEXJXQEMUTUFXJTMWTUTVCVDXQWKXFWFWFGXGXQGMURUFXGSMWTURVCVDZXQH
      XDWJWJKXEXQKXSUSUFZXEKFUSUFYAUAFXSUSQVGVJMWTUSUPVHVDXQHXSUQUFZXDHFUQUFYBU
      BFXSUQQVGVJMWTUQUPVHVDXQWJVKVIXQWFVKVIXQGXGWJWMXTVLVIVMVNVOVPVQVTMLVRWSVA
      UDWEABDWHWRDMUOOVSZDWGYCWAWBWCWDVD $.

    $d K x y $.  $d V x y $.  $d X p t x y $.  $d Y p t x y $.  $d .1. x y $.
    $d .- x y $.  $d .x. x y $.  $d .+ x y $.
    $( The line passing through the two different points ` X ` and ` Y ` in a
       left module (or any extended structure having a base set, an addition,
       and a scalar multiplication).  (Contributed by AV, 14-Jan-2023.) $)
    line $p |- ( ( W e. V /\ ( X e. B /\ Y e. B /\ X =/= Y ) )
             -> ( X L Y ) = { p e. B | E. t e. K p = ( ( ( .1. .- t ) .x. X )
                                                        .+ ( t .x. Y ) ) } ) $=
      ( vx vy wcel wne w3a wa co cv cdif wceq wrex crab cmpo lines oveqd adantr
      csn cvv eqidd oveqan12d eqeq2d rexbidv rabbidv adantl sneq difeq2d simpr1
      oveq2 id necomd anim2i 3adant1 eldifsn sylibr cbs fvexi rabex a1i ovmpodx
      eqtrd ) KJUEZLBUEZMBUEZLMUFZUGZUHZLMHUIZLMUCUDBBUCUJZUSZUKZNUJZFAUJZIUIZW
      JEUIZWNUDUJZEUIZCUIZULZAGUMZNBUNZUOZUIZWMWOLEUIZWNMEUIZCUIZULZAGUMZNBUNZW
      CWIXDULWGWCHXCLMUCUDABCDEFGHIJKNOPQRSTUAUBUPUQURWHUCUDLMBWLXBXJXCBLUSZUKZ
      UTWHXCVAWJLULZWQMULZUHZXBXJULWHXOXAXINBXOWTXHAGXOWSXGWMXMXNWPXEWRXFCWJLWO
      EVJWQMWNEVJVBVCVDVEVFXMWLXLULWHXMWKXKBWJLVGVHVFWCWDWEWFVIWGMXLUEZWCWGWEML
      UFZUHZXPWEWFXRWDWFXQWEWFLMWFVKVLVMVNMBLVOVPVFXJUTUEWHXINBBKVQOVRVSVTWAWB
      $.
  $}

  ${
    $d E p t x y $.  $d I p t x y $.  $d P p $.
    rrxlines.e $e |- E = ( RR^ ` I ) $.
    rrxlines.p $e |- P = ( RR ^m I ) $.
    rrxlines.l $e |- L = ( LineM ` E ) $.
    rrxlines.m $e |- .x. = ( .s ` E ) $.
    rrxlines.a $e |- .+ = ( +g ` E ) $.
    $( Definition of lines passing through two different points in a
       generalized real Euclidean space of finite dimension.  (Contributed by
       AV, 14-Jan-2023.) $)
    rrxlines $p |- ( I e. Fin -> L = ( x e. P , y e. ( P \ { x } )
                      |-> { p e. P | E. t e. RR
                            p = ( ( ( 1 - t ) .x. x ) .+ ( t .x. y ) ) } ) ) $=
      ( cfv co wceq c1 cr cfn wcel cbs cv csn cdif csca cur wrex crab cmpo cmin
      csg cvv crrx fvexi eqid mp1i cmap rrxbasefi eqtr4di difeq1d crefld rrxsca
      lines id fveq2d rebase wa oveq1d adantr oveqd eleq2d 1re resubgval eqcomd
      re1r mpan biimtrdi 3eqtrd eqeq2d rexeqbidva rabeqbidv mpoeq123dv eqtrd
      imp ) HUAUBZIABGUCPZWHAUDZUEZUFZJUDZGUGPZUHPZCUDZWMUMPZQZWIFQZWOBUDFQZEQZ
      RZCWMUCPZUIZJWHUJZUKZABDDWJUFZWLSWOULQZWIFQZWSEQZRZCTUIZJDUJZUKGUNUBIXERW
      GGHUOKUPABCWHEWMFWNXBIWPUNGJWHUQZMWMUQXBUQNOWPUQWNUQVEURWGABWHWKXDDXFXLWG
      WHTHUSQDWGWHGHWGVFKXMUTLVAZWGWHDWJXNVBWGXCXKJWHDXNWGXAXJCXBTWGXBVCUCPTWGW
      MVCUCGHUAKVDZVGVHVAZWGWOXBUBZVIZWTXIWLXRWRXHWSEXRWQXGWIFXRWQSWOWPQZSWOVCU
      MPZQZXGWGWQXSRXQWGWNSWOWPWGWNVCUHPSWGWMVCUHXOVGVQVAVJVKWGXSYARXQWGWPXTSWO
      WGWMVCUMXOVGVLVKWGXQYAXGRZWGXQWOTUBZYBWGXBTWOXPVMSTUBZYCYBVNYDYCVIXGYAXTS
      WOXTUQVOVPVRVSWFVTVJVJWAWBWCWDWE $.

    $d P x y $.  $d I x y $.  $d X p t x y $.  $d Y p t x y $.  $d .x. x y $.
    $d .+ x y $.
    $( The line passing through the two different points ` X ` and ` Y ` in a
       generalized real Euclidean space of finite dimension.  (Contributed by
       AV, 14-Jan-2023.) $)
    rrxline $p |- ( ( I e. Fin /\ ( X e. P /\ Y e. P /\ X =/= Y ) )
             -> ( X L Y ) = { p e. P | E. t e. RR
                              p = ( ( ( 1 - t ) .x. X ) .+ ( t .x. Y ) ) } ) $=
      ( vx vy wcel co wceq cfn wne w3a wa cv csn cdif c1 cmin cr wrex crab cmpo
      rrxlines oveqd adantr cvv eqidd simpl oveq2d simpr oveq12d eqeq2d rexbidv
      rabbidv adantl sneq difeq2d simpr1 id necomd anim2i 3adant1 eldifsn ovexi
      sylibr cmap rabex a1i ovmpodx eqtrd ) FUARZHBRZIBRZHIUBZUCZUDZHIGSZHIPQBB
      PUEZUFZUGZJUEZUHAUEZUISZWIDSZWMQUEZDSZCSZTZAUJUKZJBULZUMZSZWLWNHDSZWMIDSZ
      CSZTZAUJUKZJBULZWBWHXCTWFWBGXBHIPQABCDEFGJKLMNOUNUOUPWGPQHIBWKXAXIXBBHUFZ
      UGZUQWGXBURWIHTZWPITZUDZXAXITWGXNWTXHJBXNWSXGAUJXNWRXFWLXNWOXDWQXECXNWIHW
      NDXLXMUSUTXNWPIWMDXLXMVAUTVBVCVDVEVFXLWKXKTWGXLWJXJBWIHVGVHVFWBWCWDWEVIWF
      IXKRZWBWFWDIHUBZUDZXOWDWEXQWCWEXPWDWEHIWEVJVKVLVMIBHVNVPVFXIUQRWGXHJBBUJF
      VQLVOVRVSVTWA $.
  $}

  ${
    $d E p t x y $.  $d I i p t x y $.  $d P i p t $.  $d X i p t $.
    $d Y i p t $.
    rrxlinesc.e $e |- E = ( RR^ ` I ) $.
    rrxlinesc.p $e |- P = ( RR ^m I ) $.
    rrxlinesc.l $e |- L = ( LineM ` E ) $.
    $( Definition of lines passing through two different points in a
       generalized real Euclidean space of finite dimension, expressed by their
       coordinates.  (Contributed by AV, 13-Feb-2023.) $)
    rrxlinesc $p |- ( I e. Fin -> L = ( x e. P , y e. ( P \ { x } )
                   |-> { p e. P | E. t e. RR A. i e. I
                                  ( p ` i ) = ( ( ( 1 - t ) x. ( x ` i ) )
                                                + ( t x. ( y ` i ) ) ) } ) ) $=
      ( wcel cv co cfv wceq cr eqid eleq2d cfn csn cdif c1 cmin cvsca wrex crab
      cplusg cmpo cmul caddc wral rrxlines w3a simpll1 1red simpr resubcld cmap
      wa cbs rrxbasefi eqtr4id biimpa 3adant3 ad2antrr eldifi imbitrid a1d 3imp
      id wi 3ad2ant1 adantr rrxplusgvscavalb rexbidva rabbidva mpoeq3dva eqtrd
      ) GUAMZHABDDANZUBZUCZINZUDCNZUEOZWBFUFPZOWFBNZWHOFUIPZOQZCRUGZIDUHZUJABDW
      DENZWEPWGWNWBPUKOWFWNWIPUKOULOQEGUMZCRUGZIDUHZUJABCDWJWHFGHIJKLWHSZWJSZUN
      WAABDWDWMWQWAWBDMZWIWDMZUOZWLWPIDXBWEDMZVAZWKWOCRXDWFRMZVAZWGFVBPZWFWJWHE
      FGUAWBWIWEJXGSZWRWAWTXAXCXEUPXFUDWFXFUQXDXEURZUSXBWBXGMZXCXEWAWTXJXAWAWTX
      JWADXGWBWADRGUTOXGKWAXGFGWAVLJXHVCVDZTVEVFVGXBWIXGMZXCXEWAWTXAXLWAXAXLVMW
      TXAWIDMWAXLWIDWCVHWADXGWIXKTVIVJVKVGXDWEXGMZXEXBXCXMXBDXGWEWAWTDXGQXAXKVN
      TVEVOWSXIVPVQVRVSVT $.

    $( The line passing through the two different points ` X ` and ` Y ` in a
       generalized real Euclidean space of finite dimension, expressed by its
       coordinates.  Remark:  This proof is shorter and requires less distinct
       variables than the proof using ~ rrxlinesc .  (Contributed by AV,
       13-Feb-2023.) $)
    rrxlinec $p |- ( ( I e. Fin /\ ( X e. P /\ Y e. P /\ X =/= Y ) )
          -> ( X L Y ) = { p e. P | E. t e. RR A. i e. I
                                    ( p ` i ) = ( ( ( 1 - t ) x. ( X ` i ) )
                                                  + ( t x. ( Y ` i ) ) ) } ) $=
      ( wcel wa co cv cfv wceq cr eqid cfn wne w3a c1 cmin cvsca wrex crab cmul
      cplusg caddc wral rrxline cbs simplll 1red simpr resubcld wi id rrxbasefi
      eqtr4id eleq2d biimpcd 3ad2ant1 impcom ad2antrr 3ad2ant2 rrxplusgvscavalb
      cmap adantr biimpa rexbidva rabbidva eqtrd ) EUAMZGBMZHBMZGHUBZUCZNZGHFOI
      PZUDAPZUEOZGDUFQZOWCHWEODUJQZORZASUGZIBUHCPZWBQWDWIGQUIOWCWIHQUIOUKORCEUL
      ZASUGZIBUHABWFWEDEFGHIJKLWETZWFTZUMWAWHWKIBWAWBBMZNZWGWJASWOWCSMZNZWDDUNQ
      ZWCWFWECDEUAGHWBJWRTZWLVPVTWNWPUOWQUDWCWQUPWOWPUQZURWAGWRMZWNWPVTVPXAVQVR
      VPXAUSVSVPVQXAVPBWRGVPBSEVJOWRKVPWRDEVPUTJWSVAVBZVCVDVEVFVGWAHWRMZWNWPVTV
      PXCVRVQVPXCUSVSVPVRXCVPBWRHXBVCVDVHVFVGWOWBWRMZWPWAWNXDWABWRWBVPBWRRVTXBV
      KVCVLVKWMWTVIVMVNVO $.
  $}

  ${
    $d N i k l m p t x y $.
    $( Lemma 1 for ~ eenglngeehlnm .  (Contributed by AV, 15-Feb-2023.) $)
    eenglngeehlnmlem1 $p |- ( ( ( N e. NN /\ x e. ( RR ^m ( 1 ... N ) )
                                    /\ y e. ( ( RR ^m ( 1 ... N ) ) \ { x } ) )
                                    /\ p e. ( RR ^m ( 1 ... N ) ) )
       -> ( ( E. k e. ( 0 [,] 1 ) A. i e. ( 1 ... N )
              ( p ` i ) = ( ( ( 1 - k ) x. ( x ` i ) ) + ( k x. ( y ` i ) ) )
           \/ E. l e. ( 0 [,) 1 ) A. i e. ( 1 ... N )
              ( x ` i ) = ( ( ( 1 - l ) x. ( p ` i ) ) + ( l x. ( y ` i ) ) )
           \/ E. m e. ( 0 (,] 1 ) A. i e. ( 1 ... N )
              ( y ` i ) = ( ( ( 1 - m ) x. ( x ` i ) ) + ( m x. ( p ` i ) ) ) )
             -> E. t e. RR A. i e. ( 1 ... N )
                            ( p ` i ) = ( ( ( 1 - t ) x. ( x ` i ) )
                                          + ( t x. ( y ` i ) ) ) ) ) $=
      ( wcel cr c1 co cmin cmul caddc wceq cc0 oveq1d cdiv cn cfz cmap csn cdif
      cv w3a wa cfv wral cicc wrex cico cioc oveq2 oveq1 oveq12d eqeq2d ralbidv
      cbvrexvw wss wi unitssre ssrexv mp1i biimtrid cneg cle wbr clt cxr wb 0re
      1xr elico2 mp2an simp1 1red resubcld 1cnd recnd wne ltne 3adant2 redivcld
      subne0d sylbi ad2antlr renegcld adantl eqcom 3ad2ant2 ad2antrr ffvelcdmda
      wf elmapi eldifi 3ad2ant3 mulcld subcld subadd2d bitr4id divmuld divrec2d
      syl divsubdird div23d bitrid divcld mulneg1d eqcomd oveq2d reccld negsubd
      eqtrd subnegd cc muldivdir syl112anc mulridd npcand 3eqtr2d biimpd sylbid
      3eqtr3d ralimdva imp rspcedvd rexlimdva2 0xr 1re elioc2 gt0ne0 negsubdi2d
      3adant3 rereccld eqtr3d eqeq1d a1i 3bitr3d subaddd addcld elioc1 divmul2d
      anim1i divdird dividd comraddd 3jaod ) GUAJZAUFZKLGUBMZUCMZJZBUFZUUMUUKUD
      ZUEJZUGZHUFZUUMJZUHZDUFZUUSUIZLEUFZNMZUVBUUKUIZOMZUVDUVBUUOUIZOMZPMZQZDUU
      LUJZERLUKMZULZUVCLCUFZNMZUVFOMZUVOUVHOMZPMZQZDUULUJZCKULZUVFLIUFZNMZUVCOM
      ZUWCUVHOMZPMZQZDUULUJZIRLUMMZULUVHLFUFZNMZUVFOMZUWKUVCOMZPMZQZDUULUJZFRLU
      NMZULUVNUWACUVMULZUVAUWBUVLUWAECUVMUVDUVOQZUVKUVTDUULUWTUVJUVSUVCUWTUVGUV
      QUVIUVRPUWTUVEUVPUVFOUVDUVOLNUOSUVDUVOUVHOUPUQURUSUTUVMKVAUWSUWBVBUVAVCUW
      ACUVMKVDVEVFUVAUWIUWBIUWJUVAUWCUWJJZUHZUWIUHZUWAUVCLUWCUWDTMZVGZNMZUVFOMZ
      UXEUVHOMZPMZQZDUULUJZCUXEKUXCUXDUXAUXDKJZUVAUWIUXAUWCKJZRUWCVHVIZUWCLVJVI
      ZUGZUXLRKJZLVKJZUXAUXPVLVMVNRLUWCVOVPZUXPUWCUWDUXMUXNUXOVQZUXPLUWCUXPVRUX
      TVSUXPLUWCUXPVTUXPUWCUXTWAUXMUXOLUWCWBZUXNUWCLWCWDZWFWEWGWHWIUVOUXEQZUWAU
      XKVLUXCUYCUVTUXJDUULUYCUVSUXIUVCUYCUVQUXGUVRUXHPUYCUVPUXFUVFOUVOUXELNUOSU
      VOUXEUVHOUPUQURUSWJUXBUWIUXKUXBUWHUXJDUULUXBUVBUULJZUHZUWHUVFUWFNMZUWEQZU
      XJUYEUWHUWGUVFQUYGUVFUWGWKUYEUVFUWFUWEUYEUVFUXBUULKUVBUUKUURUULKUUKWOZUUT
      UXAUUNUUJUYHUUQUUKKUULWPWLZWMWNWAZUYEUWCUVHUYEUWCUXAUXMUVAUYDUXAUXPUXMUXS
      UXTWGWHWAZUYEUVHUXBUULKUVBUUOUURUULKUUOWOZUUTUXAUUQUUJUYLUUNUUQUUOUUMJUYL
      UUOUUMUUPWQUUOKUULWPXEWRZWMWNWAZWSZUYEUWDUVCUYELUWCUYEVTZUYKWTZUYEUVCUXBU
      ULKUVBUUSUUTUULKUUSWOZUURUXAUUSKUULWPZWHWNWAZWSXAXBUYEUYGUYFUWDTMZUVCQZUX
      JUYEUYGUWEUYFQVUBUYFUWEWKUYEUYFUWDUVCUYEUVFUWFUYJUYOWTUYQUYTUYELUWCUYPUYK
      UXAUYAUVAUYDUXAUXPUYAUXSUYBWGWHWFZXCXBUYEVUBUVCLUWDTMZUVFOMZUXDUVHOMZNMZQ
      ZUXJVUBUVCVUAQUYEVUHVUAUVCWKUYEVUAVUGUVCUYEVUAUVFUWDTMZUWFUWDTMZNMVUGUYEU
      VFUWFUWDUYJUYOUYQVUCXFUYEVUIVUEVUJVUFNUYEUVFUWDUYJUYQVUCXDUYEUWCUVHUWDUYK
      UYNUYQVUCXGUQXOURXHUYEVUHUXJUYEVUGUXIUVCUYEVUEVUFVGZPMVUEUXHPMVUGUXIUYEVU
      KUXHVUEPUYEUXHVUKUYEUXDUVHUYEUWCUWDUYKUYQVUCXIZUYNXJXKXLUYEVUEVUFUYEVUDUV
      FUYEUWDUYQVUCXMUYJWSUYEUXDUVHVULUYNWSXNUYEVUEUXGUXHPUYEVUDUXFUVFOUYEUXFVU
      DUYEUXFLUXDPMZUWDLOMZUWCPMZUWDTMZVUDUYELUXDUYPVULXPUYELXQJUWCXQJUWDXQJUWD
      RWBVUPVUMQUYPUYKUYQVUCLUWCUWDXRXSUYEVUOLUWDTUYEVUOUWDUWCPMLUYEVUNUWDUWCPU
      YEUWDUYQXTSUYELUWCUYPUYKYAXOSYBXKSSYEURYCYDYDYDYFYGYHYIUVAUWQUWBFUWRUVAUW
      KUWRJZUHZUWQUHZUWAUVCLLUWKTMZNMZUVFOMZVUTUVHOMZPMZQZDUULUJZCVUTKVUQVUTKJZ
      UVAUWQVUQUWKKJZRUWKVJVIZUWKLVHVIZUGZVVGRVKJZLKJVUQVVKVLYJYKRLUWKYLVPZVVKU
      WKVVHVVIVVJVQZVVHVVIUWKRWBZVVJUWKYMYOYPWGWHUVOVUTQZUWAVVFVLVUSVVPUVTVVEDU
      ULVVPUVSVVDUVCVVPUVQVVBUVRVVCPVVPUVPVVAUVFOUVOVUTLNUOSUVOVUTUVHOUPUQURUSW
      JVURUWQVVFVURUWPVVEDUULVURUYDUHZUWPUVCVVCUWKUWKTMZVUTNMZUVFOMZPMZQZVVEUWP
      UWOUVHQZVVQVWBUVHUWOWKVVQUVHUWMNMZUWNQUVHUWKLNMZUVFOMZPMZUWNQZVWCVWBVVQVW
      DVWGUWNVVQUVHUWMVGZPMVWDVWGVVQUVHUWMVVQUVHVURUULKUVBUUOUURUYLUUTVUQUYMWMW
      NWAZVVQUWLUVFVVQLUWKVVQVTZVUQUWKXQJUVAUYDVUQUWKVUQVVKVVHVVMVVNWGWAWHZWTZV
      VQUVFVURUULKUVBUUKUURUYHUUTVUQUYIWMWNWAZWSZXNVVQVWIVWFUVHPVVQUWLVGZUVFOMV
      WIVWFVVQUWLUVFVWMVWNXJVVQVWPVWEUVFOVVQLUWKVWKVWLYNSYQXLYQYRVVQUVHUWMUWNVW
      JVWOVVQUWKUVCVWLVVQUVCVURUULKUVBUUSUUTUYRUURVUQUYSWHWNWAZWSUUAVVQVWGUWKTM
      ZUVCQZUVCVWRQZVWHVWBVWSVWTVLVVQVWRUVCWKYSVVQVWGUVCUWKVVQUVHVWFVWJVVQVWEUV
      FVVQUWKLVWLVWKWTZVWNWSZUUBVWQVWLVUQVVOUVAUYDVUQUWKVKJZVVIVVJUGZVVOVVLUXRV
      UQVXDVLYJVNRLUWKUUCVPVXDUXQVVIUHZVVOVXCVVIVXEVVJVXCUXQVVIUXQVXCVMYSUUEYOR
      UWKWCXEWGWHZUUDVVQVWRVWAUVCVVQVWRUVHUWKTMZVWFUWKTMZPMVWAVVQUVHVWFUWKVWJVX
      BVWLVXFUUFVVQVXGVVCVXHVVTPVVQUVHUWKVWJVWLVXFXDVVQVXHVWEUWKTMZUVFOMVVTVVQV
      WEUVFUWKVXAVWNVWLVXFXGVVQVXIVVSUVFOVVQUWKLUWKVWLVWKVWLVXFXFSXOUQXOURYTYTX
      HVVQVWBVVEVVQVWAVVDUVCVVQVWAVVCVVBVVQVUTUVHVVQUWKVWLVXFXMZVWJWSVVQVVAUVFV
      VQLVUTVWKVXJWTVWNWSVVQVVTVVBVVCPVVQVVSVVAUVFOVVQVVRLVUTNVVQUWKVWLVXFUUGSS
      XLUUHURYCYDYFYGYHYIUUI $.

    $( Lemma 2 for ~ eenglngeehlnm .  (Contributed by AV, 15-Feb-2023.) $)
    eenglngeehlnmlem2 $p |- ( ( ( N e. NN /\ x e. ( RR ^m ( 1 ... N ) )
                                    /\ y e. ( ( RR ^m ( 1 ... N ) ) \ { x } ) )
                                    /\ p e. ( RR ^m ( 1 ... N ) ) )
    -> ( E. t e. RR A. i e. ( 1 ... N )
                ( p ` i ) = ( ( ( 1 - t ) x. ( x ` i ) ) + ( t x. ( y ` i ) ) )
         -> ( E. k e. ( 0 [,] 1 ) A. i e. ( 1 ... N )
                ( p ` i ) = ( ( ( 1 - k ) x. ( x ` i ) ) + ( k x. ( y ` i ) ) )
             \/ E. l e. ( 0 [,) 1 ) A. i e. ( 1 ... N )
                ( x ` i ) = ( ( ( 1 - l ) x. ( p ` i ) ) + ( l x. ( y ` i ) ) )
             \/ E. m e. ( 0 (,] 1 ) A. i e. ( 1 ... N )
                ( y ` i ) = ( ( ( 1 - m ) x. ( x ` i ) )
                              + ( m x. ( p ` i ) ) ) ) ) ) $=
      ( wcel cr c1 co cmin cmul caddc wceq cc0 cdiv oveq1d cn cfz cmap csn cdif
      cv w3a cfv wral cicc wrex cico cioc w3o clt wbr 0red 1red simpr reorelicc
      wa syl3anc wi cxr 0xr a1i 1xr cc simpl recnd 0lt1 lttrd ltned 1subrec1sub
      wne syl2anc resubcld subne0d redivcld rexrd eqeltrd ad4ant23 cle renegcld
      1cnd cneg mpbird ltled mpbid eqtr4d wb oveq2 oveq1 oveq12d eqeq2d ralbidv
      adantl subcld reccld nncand gt0ne0d eqeq1d subaddd bitrd 3bitrd necon3bid
      bitr3d eqcom divmuld bitrid eqtrd oveq2d divrec2d necomd eqtr2d biimpd wf
      elmapi adantr ad2antrr ffvelcdmda mulcld bitr4id divsubdird divcld div23d
      negsubd negsubdi2d 3eqtrd 3eqtr2d sylibrd ralimdva imp exp31 com23 simplr
      rspcedvd ex recrecd eqcomd sublt0d negelrpd le0neg1d divge0d div2negd crp
      breqtrrd elrpd rpreccld ltsubrpd elicod gtned subeq0ad sub32d subidd 0cnd
      posdifd addridd mulridd recid2d mvllmuld eqtr3d eqeltrrd divne1d 3ad2ant2
      subdivcomb2 syl112anc eldifi syl 3ad2ant3 subadd2d divneg2d 3mix2d 3mix1d
      recgt0d recgt1i simprr mpdan 3jca 1re pm3.2i elioc2 gt0ne0 recne0d dividd
      mp1i syld divnegd mulneg1d addcomd 3mix3d 3jaod mpid rexlimdva ) GUAJZAUF
      ZKLGUBMZUCMZJZBUFZUWRUWPUDZUEJZUGZHUFZUWRJZVAZDUFZUXDUHZLCUFZNMZUXGUWPUHZ
      OMZUXIUXGUWTUHZOMZPMZQZDUWQUIZUXHLEUFZNMZUXKOMZUXRUXMOMZPMZQZDUWQUIZERLUJ
      MZUKZUXKLIUFZNMZUXHOMZUYGUXMOMZPMZQZDUWQUIZIRLULMZUKZUXMLFUFZNMZUXKOMZUYP
      UXHOMZPMZQZDUWQUIZFRLUMMZUKZUNZCKUXFUXIKJZVAZUXQUXIRUOUPZUXIUYEJZLUXIUOUP
      ZUNZVUEVUGRKJLKJZVUFVUKVUGUQVUGURUXFVUFUSRLUXIUTVBVUGUXQVUKVUEVCVUGUXQVAZ
      VUHVUEVUIVUJVUGUXQVUHVUEVCVUGVUHUXQVUEVUGVUHUXQVUEVUGVUHVAZUXQVAZUYOUYFVU
      DVUOUYMUXKLLLUXJSMZNMZNMZUXHOMZVUQUXMOMZPMZQZDUWQUIZIVUQUYNVUORLVUQRVDJZV
      UOVEVFLVDJVUOVGVFVUFVUHVUQVDJUXFUXQVUFVUHVAZVUQUXIUXILNMZSMZVDVVEUXIVHJZU
      XILVOVUQVVGQVVEUXIVUFVUHVIZVJZVVEUXILVVIVVEUXIRLVVIVVEUQZVVEURZVUFVUHUSZR
      LUOUPZVVEVKVFZVLZVMZUXIVNVPZVVEVVGVVEUXIVVFVVIVVEUXILVVIVVLVQZVVEUXILVVJV
      VEWEZVVQVRZVSVTWAWBVUFVUHRVUQWCUPUXFUXQVVERUXIWFZVVFWFZSMZVUQWCVVEVWBVWCV
      VEUXIVVIWDVVEVVFVVSVVEVVFRUOUPUXILUOUPZVVPVVEUXILVVIVVLUUAWGUUBVVEUXIRWCU
      PRVWBWCUPVVEUXIRVVIVVKVVMWHVVEUXIVVIUUCWIUUDVVEVUQVVGVWDVVRVVEUXIVVFVVJVV
      EVVFVVSVJZVWAUUEWJUUGWBVUOLVUPVUOURVUOUXJVUFVUHUXJUUFJUXFUXQVVEUXJVVELUXI
      VVLVVIVQVVEVWERUXJUOUPVVPVVEUXILVVIVVLUUQWIUUHWBUUIUUJUUKUYGVUQQZUYMVVCWK
      VUOVWGUYLVVBDUWQVWGUYKVVAUXKVWGUYIVUSUYJVUTPVWGUYHVURUXHOUYGVUQLNWLTUYGVU
      QUXMOWMWNWOWPWQVUNUXQVVCVUNUXPVVBDUWQVUNUXGUWQJZVAZUXPUXHLVURSMZUXKOMZVUQ
      VUQLNMZSMZUXMOMZPMZQZVVBVWIUXPVWPVWIUXOVWOUXHVWIUXLVWKUXNVWNPVWIUXJVWJUXK
      OVUFVUHUXJVWJQUXFVWHVVEVURUXJLVVEVURVUPVHVVELVUPVVTVVEUXJVVELUXIVVTVVJWRZ
      VVELUXIVVTVVJVVEUXILVVIVVPUULZVRZWSZWTZVWTWAZVWQVVELVUQVVTVVELVUPVVTVWTWR
      ZVVELVUQVOVVFUXIVOZVVEVXDLRVOVVELVVOXAVVEVVFUXILRVVEVVFUXINMZRQZVVFUXIQZL
      RQZVVEVVFUXIVWFVVJUUMVVEVXFUXIUXINMZLNMZRQRLNMZRQZVXHVVEVXEVXJRVVEUXILUXI
      VVJVVTVVJUUNXBVVEVXJVXKRVVEVXIRLNVVEUXIVVJUUOTXBVVEVXLLRPMZRQVXHVVERLRVVE
      UUPZVVTVXNXCVVEVXMLRVVELVVTUURXBXDXEXGXFWGZVVELVUQVVFUXIVVELVUQQLVVGQZVVF
      LOMZUXIQZVXGVVEVUQVVGLVVRWOVXPVVGLQVVEVXRLVVGXHVVEUXIVVFLVVJVWFVVTVWAXIXJ
      VVEVXQVVFUXIVVEVVFVWFUUSZXBXEXFWGZVRZVVEVURUXJOMVUPUXJOMLVVEVURVUPUXJOVXA
      TVVEUXJVWQVWSUUTXKUVAWBTVWIUXIVWMUXMOVUFVUHUXIVWMQUXFVWHVVEVWMVVGVVGLNMZS
      MZUXIVVEVUQVVGVWLVYBSVVRVVEVUQVVGLNVVRTWNVVEVYCUXIQVYBUXIOMZVVGQVVEVYDLVV
      FSMZUXIOMVVGVVEVYBVYEUXIOVVEUXIVXQNMZVVFSMZVYBVYEVVEVVHLVHJVVFVHJVVFRVOVY
      GVYBQVVJVVTVWFVWAUXILVVFUVFUVGVVEVYFLVVFSVVEVYFUXIVVFNMLVVEVXQVVFUXINVXSX
      LVVEUXILVVJVVTWTXKTUVBTVVEUXIVVFVVJVWFVWAXMWJVVEVVGVYBUXIVVEVUQVVGVHVVRVX
      CUVCZVVEVVGLVYHVVTWRVVJVVEVVGLVYHVVTVVEUXIVVFVVJVWFVWAVVEVVFUXIVXOXNUVDVR
      XIWGXOWBTWNWOXPVWIVVBUXKVUTNMZVUSQZVWPVWIVVBVVAUXKQVYJUXKVVAXHVWIUXKVUTVU
      SVWIUXKVUNUWQKUXGUWPUXFUWQKUWPXQZVUFVUHUXCVYKUXEUWSUWOVYKUXBUWPKUWQXRUVEX
      SZXTYAVJZVWIVUQUXMVWILVUPVWIWEZVWIUXJVWILUXIVYNVUFVUHVVHUXFVWHVVJWBZWRVWI
      LUXIVYNVYOVUFVUHLUXIVOUXFVWHVWRWBVRWSWRZVWIUXMVUNUWQKUXGUWTUXFUWQKUWTXQZV
      UFVUHUXCVYQUXEUXBUWOVYQUWSUXBUWTUWRJVYQUWTUWRUXAUVHUWTKUWQXRUVIUVJXSZXTYA
      VJZYBZVWIVURUXHVUFVUHVURVHJUXFVWHVXBWBZVWIUXHVUNUWQKUXGUXDUXFUWQKUXDXQZVU
      FVUHUXEWUBUXCUXDKUWQXRWQZXTYAVJZYBUVKYCVYJVUSVYIQZVWIVWPVYIVUSXHVWIVYIVUR
      SMZUXHQZWUEVWPVWIVYIVURUXHVWIUXKVUTVYMVYTWRWUAWUDVUFVUHVURRVOUXFVWHVYAWBZ
      XIWUGUXHWUFQVWIVWPWUFUXHXHVWIWUFVWOUXHVWIWUFUXKVURSMZVUTVURSMZNMWUIWUJWFZ
      PMVWOVWIUXKVUTVURVYMVYTWUAWUHYDVWIWUIWUJVWIUXKVURVYMWUAWUHYEVWIVUTVURVYTW
      UAWUHYEYGVWIWUIVWKWUKVWNPVWIUXKVURVYMWUAWUHXMVWIWUKVUTVURWFZSMVUTVWLSMVWN
      VWIVUTVURVYTWUAWUHUVLVWIWULVWLVUTSVWILVUQVYNVYPYHXLVWIVUQUXMVWLVYPVYSVWIV
      UQLVYPVYNWRVUFVUHVWLRVOUXFVWHVVEVUQLVXCVVTVVELVUQVXTXNVRWBYFYIWNYJWOXJXGX
      JXDYKYLYMYQUVMYNYOYMVUMVUIVUEVUMVUIVAZUYFUYOVUDWUMUYDUXQEUXIUYEVUMVUIUSUX
      RUXIQZUYDUXQWKWUMWUNUYCUXPDUWQWUNUYBUXOUXHWUNUXTUXLUYAUXNPWUNUXSUXJUXKOUX
      RUXILNWLTUXRUXIUXMOWMWNWOWPWQVUGUXQVUIYPYQUVNYRVUGUXQVUJVUEVCVUGVUJUXQVUE
      VUGVUJUXQVUEVUGVUJVAZUXQVAZVUDUYFUYOWUPVUBUXMLLUXISMZNMZUXKOMZWUQUXHOMZPM
      ZQZDUWQUIZFWUQVUCVUFVUJWUQVUCJZUXFUXQVUFVUJVAZWVDWUQKJZRWUQUOUPZWUQLWCUPZ
      UGZWVEWVFWVGWVHWVELUXIWVEURZVUFVUJVIZWVEUXIWVERLUXIWVEUQWVJWVKVVNWVEVKVFV
      UFVUJUSVLZXAVSZWVEUXIWVKWVLUVOWVEWVGWUQLUOUPZVAZWVHUXIUVPWVEWVOVAZWUQLWVE
      WVFWVOWVMXSWVPURWVEWVGWVNUVQWHUVRUVSVVDVULVAWVDWVIWKWVEVVDVULVEUVTUWARLWU
      QUWBUWFWGWBUYPWUQQZVUBWVCWKWUPWVQVUAWVBDUWQWVQUYTWVAUXMWVQUYRWUSUYSWUTPWV
      QUYQWURUXKOUYPWUQLNWLTUYPWUQUXHOWMWNWOWPWQWUOUXQWVCWUOUXPWVBDUWQWUOVWHVAZ
      UXPUXHWUQLNMZWUQSMZUXKOMZLWUQSMZUXMOMZPMZQZWVBWVRUXPWWEWVRUXOWWDUXHWVRUXL
      WWAUXNWWCPWVRUXJWVTUXKOWVRWVTWUQWUQSMZWWBNMUXJWVRWUQLWUQWVRUXIWUOVVHVWHWU
      OUXIUXFVUFVUJYPVJZXSZWUOUXIRVOZVWHVUGVUJWWIVUFVUJWWIVCUXFVUFVUJRUXIUOUPZW
      WIVUFVUJWWJWVLYRVUFWWJWWIUXIUWCYRUWGWQYMZXSZWSZWVRWEZWWMWVRUXIWWHWWLUWDZY
      DWVRWWFLWWBUXINWVRWUQWWMWWOUWEWVRUXIWWHWWLYSWNXOTWVRUXIWWBUXMOWUOUXIWWBQV
      WHWUOWWBUXIWUOUXIWWGWWKYSYTXSTWNWOXPWVRWVBUXMWUSNMZWUTQZWWPWUQSMZUXHQZWWE
      WVRWVBWVAUXMQWWQUXMWVAXHWVRUXMWUSWUTWVRUXMWUOUWQKUXGUWTUXFVYQVUFVUJVYRXTY
      AVJZWVRWURUXKWVRLWUQWWNWWMWRZWVRUXKWUOUWQKUXGUWPUXFVYKVUFVUJVYLXTYAVJZYBZ
      WVRWUQUXHWWMWVRUXHWUOUWQKUXGUXDUXFWUBVUFVUJWUCXTYAVJZYBXCYCWVRWWQWUTWWPQW
      WSWWPWUTXHWVRWWPWUQUXHWVRUXMWUSWWTWXCWRWWMWXDWWOXIYCWWSUXHWWRQWVRWWEWWRUX
      HXHWVRWWRWWDUXHWVRWWRUXMWUQSMZWUSWUQSMZNMWXEWXFWFZPMZWWDWVRUXMWUSWUQWWTWX
      CWWMWWOYDWVRWXEWXFWVRUXMWUQWWTWWMWWOYEWVRWUSWUQWXCWWMWWOYEYGWVRWXHWXEWWAP
      MWWCWWAPMWWDWVRWXGWWAWXEPWVRWXGWUSWFZWUQSMWURWFZUXKOMZWUQSMZWWAWVRWUSWUQW
      XCWWMWWOUWHWVRWXIWXKWUQSWVRWXKWXIWVRWURUXKWXAWXBUWIYTTWVRWXLWVSUXKOMZWUQS
      MWWAWVRWXKWXMWUQSWVRWXJWVSUXKOWVRLWUQWWNWWMYHTTWVRWVSUXKWUQWVRWUQLWWMWWNW
      RZWXBWWMWWOYFXKYIXLWVRWXEWWCWWAPWVRUXMWUQWWTWWMWWOXMTWVRWWCWWAWVRWWBUXMWV
      RWUQWWMWWOWSWWTYBWVRWVTUXKWVRWVSWUQWXNWWMWWOYEWXBYBUWJYIYJWOXJXEYKYLYMYQU
      WKYNYOYMUWLYRUWMUWN $.

    $d N i n p t v w x y z $.
    $( The line definition in the Tarski structure for the Euclidean geometry
       (see ~ elntg ) corresponds to the definition of lines passing through
       two different points in a left module (see ~ rrxlines ).  (Contributed
       by AV, 16-Feb-2023.) $)
    eenglngeehlnm $p |- ( N e. NN -> ( LineG ` ( EEG ` N ) )
                                     = ( LineM ` ( EEhil ` N ) ) ) $=
      ( vx vy vi vp vz vv vw vt wcel cfv cv c1 cmin co cmul wceq cr wa eqid cbs
      vn cn ceeng csn cdif caddc cfz wral cc0 cicc wrex cico cioc w3o crab cmpo
      cmap clng cehl cline cee eqcomd oveq2 oveq2d df-ee ovex fvmpt eqtrd ancli
      eengbas jca difeq1 ad2antlr sylan adantr wb simpll eleq2d biimpcd difeq1d
      wi impcom biimpd adantld imp eenglngeehlnmlem1 eenglngeehlnmlem2 syl31anc
      biimpa w3a impbid rabeqbidva mpoeq123dva elntg2 crrx cn0 nnnn0 ehlval syl
      fveq2d cfn fzfid rrxlinesc 3eqtr4d ) AUCJZBCAUDKZUAKZXHBLZUEZUFZDLZELZKZM
      FLZNOXLXIKZPOXOXLCLZKZPOUGOQDMAUHOZUIFUJMUKOULXPMGLZNOXNPOXTXRPOUGOQDXSUI
      GUJMUMOULXRMHLZNOXPPOYAXNPOUGOQDXSUIHUJMUNOULUOZEXHUPZUQBCRXSUROZYDXJUFZX
      NMILZNOXPPOYFXRPOUGOQDXSUIIRULZEYDUPZUQZXGUSKAUTKZVAKZXFBCXHXKYCYDYEYHXFX
      HAVBKZYDXFYLXHAVKVCZUBARMUBLZUHOZUROYDUCVBYNAQYOXSRURYNAMUHVDVEUBVFRXSURV
      GVHVIZXFXFXHYLQZSZXHYDQZSXIXHJZXKYEQZXFYRYSXFYQYMVJYPVLYSUUAYRYTXHYDXJVMV
      NVOXFYTXQXKJZSZSZYBYGEXHYDXFYSUUCYPVPZUUDXMXHJZSXFXIYDJZXQYEJZXMYDJZYBYGV
      QXFUUCUUFVRUUDUUGUUFUUCXFUUGYTXFUUGWBUUBXFYTUUGXFXHYDXIYPVSVTVPWCVPUUDUUH
      UUFXFUUCUUHXFUUBUUHYTXFUUBUUHXFXKYEXQXFXHYDXJYPWAVSWDWEWFVPUUDUUFUUIUUDXH
      YDXMUUEVSWJXFUUGUUHWKUUISYBYGBCIDFHAEGWGBCIDFHAEGWHWLWIWMWNBCXHDFHXSAEGXH
      TXSTWOXFYKXSWPKZVAKZYIXFYJUUJVAXFAWQJYJUUJQAWRYJAYJTWSWTXAXFXSXBJUUKYIQXF
      MAXCBCIYDDUUJXSUUKEUUJTYDTUUKTXDWTVIXE $.
  $}

  ${
    $d E i p t $.  $d I i p t $.  $d P i p t $.  $d X i p t $.  $d Y i p t $.
    rrx2line.i $e |- I = { 1 , 2 } $.
    rrx2line.e $e |- E = ( RR^ ` I ) $.
    rrx2line.b $e |- P = ( RR ^m I ) $.
    rrx2line.l $e |- L = ( LineM ` E ) $.
    $( The line passing through the two different points ` X ` and ` Y ` in a
       real Euclidean space of dimension 2.  (Contributed by AV, 22-Jan-2023.)
       (Proof shortened by AV, 13-Feb-2023.) $)
    rrx2line $p |- ( ( X e. P /\ Y e. P /\ X =/= Y )
                     -> ( X L Y ) = { p e. P | E. t e. RR
     ( ( p ` 1 ) = ( ( ( 1 - t ) x. ( X ` 1 ) ) + ( t x. ( Y ` 1 ) ) )
    /\ ( p ` 2 ) = ( ( ( 1 - t ) x. ( X ` 2 ) ) + ( t x. ( Y ` 2 ) ) ) ) } ) $=
      ( vi co cfv c1 cmul wceq c2 fveq2 wcel wne w3a cv cmin caddc wral cr wrex
      crab wa cfn cpr prfi eqeltri rrxlinec mpan a1i raleqdv 1ex oveq2d oveq12d
      2ex eqeq12d ralpr bitrdi rexbidva rabbidva eqtrd ) FBUAGBUAFGUBUCZFGENZMU
      DZHUDZOZPAUDZUENZVLFOZQNZVOVLGOZQNZUFNZRZMDUGZAUHUIZHBUJZPVMOZVPPFOZQNZVO
      PGOZQNZUFNZRZSVMOZVPSFOZQNZVOSGOZQNZUFNZRZUKZAUHUIZHBUJDULUAVJVKWERDPSUMZ
      ULIPSUNUOABMCDEFGHJKLUPUQVJWDXAHBVJVMBUAUKZWCWTAUHXCVOUHUAUKZWCWBMXBUGWTX
      DWBMDXBDXBRXDIURUSWBWLWSMPSUTVCVLPRZVNWFWAWKVLPVMTXEVRWHVTWJUFXEVQWGVPQVL
      PFTVAXEVSWIVOQVLPGTVAVBVDVLSRZVNWMWAWRVLSVMTXFVRWOVTWQUFXFVQWNVPQVLSFTVAX
      FVSWPVOQVLSGTVAVBVDVEVFVGVHVI $.

    $( The vertical line passing through the two different points ` X ` and
       ` Y ` in a real Euclidean space of dimension 2 in "standard form".
       (Contributed by AV, 2-Feb-2023.) $)
    rrx2vlinest $p |- ( ( X e. P /\ Y e. P /\ ( ( X ` 1 ) = ( Y ` 1 )
                                                /\ ( X ` 2 ) =/= ( Y ` 2 ) ) )
                        -> ( X L Y ) = { p e. P | ( p ` 1 ) = ( X ` 1 ) } ) $=
      ( wcel c1 wceq wa co cmul caddc cr adantr vt cfv c2 wne cv cmin wrex crab
      w3a fveq1 necon3i adantl rrx2line syl3an3 oveq2 oveq2d eqcoms 3ad2ant3 cc
      rrx2pxel recnd 3ad2ant1 recn affineid eqtrd eqeq2d anbi1d rexbidva wi a1i
      simpl rexlimdva cdiv rrx2pyel resubcld 3ad2ant2 cc0 simpr necomd redivcld
      subne0d oveq1d oveq1 oveq12d anbi2d mullidd subcld 3adant3 pncan3d eqtr2d
      wb divcan1d 1cnd submuladdmuld eqtr4d jca rspcedvd impbid bitrd rabbidva
      ex ) EALZFALZMEUBZMFUBZNZUCEUBZUCFUBZUDZOZUIZEFDPZMGUEZUBZMUAUEZUFPZXDQPZ
      XOXEQPZRPZNZUCXMUBZXPXGQPZXOXHQPZRPZNZOZUASUGZGAUHZXNXDNZGAUHXJXBXCEFUDZX
      LYHNXIYJXFEFXGXHUCEFUJUKULUAABCDEFGHIJKUMUNXKYGYIGAXKXMALZOZYGYIYEOZUASUG
      ZYIYLYFYMUASYLXOSLZOZXTYIYEYPXSXDXNYPXSXQXOXDQPZRPZXDYLXSYRNZYOXKYSYKXJXB
      YSXCXFYSXIYSXEXDXEXDNXRYQXQRXEXDXOQUOUPUQTURTTYPXDXOYLXDUSLZYOXKYTYKXBXCY
      TXJXBXDACEHJUTVAVBTTYOXOUSLYLXOVCULVDVEVFVGVHYLYNYIYLYMYIUASYMYIVIYPYIYEV
      KVJVLYLYIYNYLYIOZYMYIYAMYAXGUFPZXHXGUFPZVMPZUFPZXGQPZUUDXHQPZRPZNZOZUAUUD
      SYLUUDSLYIYLUUBUUCYLYAXGYKYASLXKACXMHJVNZULXKXGSLZYKXBXCUULXJACEHJVNZVBZT
      VOZXKUUCSLYKXKXHXGXCXBXHSLXJACFHJVNZVPUUNVOTXKUUCVQUDYKXKXHXGXCXBXHUSLZXJ
      XCXHUUPVAZVPZXBXCXGUSLZXJXBXGUUMVAZVBZXJXBXHXGUDXCXJXGXHXFXIVRVSURWATZVTZ
      TXOUUDNZYMUUJWKUUAUVEYEUUIYIUVEYDUUHYAUVEYBUUFYCUUGRUVEXPUUEXGQXOUUDMUFUO
      WBXOUUDXHQWCWDVFWEULUUAYIUUIYLYIVRUUAYAMXGQPZUUDUUCQPZRPZUUHYLYAUVHNYIYLU
      VHXGUUBRPYAYLUVFXGUVGUUBRXKUVFXGNZYKXBXCUVIXJXBXGUVAWFVBTYLUUBUUCYLUUBUUO
      VAXKUUCUSLZYKXBXCUVJXJXBXCOXHXGXCUUQXBUURULXBUUTXCUVATWGWHTUVCWLWDYLXGYAX
      KUUTYKUVBTZYKYAUSLXKYKYAUUKVAULWIWJTYLUUHUVHNYIYLMUUDXGXHYLWMYLUUDUVDVAUV
      KXKUUQYKUUSTWNTWOWPWQXAWRWSWTVE $.

    ${
      rrx2linest.a $e |- A = ( ( Y ` 1 ) - ( X ` 1 ) ) $.
      rrx2linest.b $e |- B = ( ( Y ` 2 ) - ( X ` 2 ) ) $.
      rrx2linest.c $e |- C = ( ( ( X ` 2 ) x. ( Y ` 1 ) )
                             - ( ( X ` 1 ) x. ( Y ` 2 ) ) ) $.
      $( The line passing through the two different points ` X ` and ` Y ` in a
         real Euclidean space of dimension 2 in "standard form".  (Contributed
         by AV, 2-Feb-2023.) $)
      rrx2linest $p |- ( ( X e. P /\ Y e. P /\ X =/= Y ) -> ( X L Y )
            = { p e. P | ( A x. ( p ` 2 ) ) = ( ( B x. ( p ` 1 ) ) + C ) } ) $=
        ( wceq co cmul vi vt wcel wne w3a c1 cfv c2 cv caddc crab simpl1 simpl2
        wa simpr wi wral anim1i cpr raleqi 1ex fveq2 eqeq12d ralpr bitri sylibr
        2ex wfn wb cr cmap elmapfn eleq2s anim12i ad2antrr eqfnfv syl mpbird ex
        necon3d com23 3impia imp rrx2vlinest syl112anc ancom cmin simplr simpll
        cc0 oveq1i a1i oveq2 adantl rrx2pxel recnd 3ad2ant2 subidd eqtrd oveq1d
        cc rrx2pyel ad2antlr mul02d 3eqtrd oveq1 oveq2d eqtrid oveq12d syl21anc
        mulcomd 3ad2ant1 subdird eqtr4d eqeq2d cneg eqcom subcld mulcld syl2anc
        addeq0 mulneg1d negsubdi2d eqtr3d 3imtr3i adantr subne0d mulcand 3bitrd
        necom bitrd simpl eqcomd 3bitrrd rabbidva sylbi wn wrex rrx2line eqcomi
        df-ne affinecomb2 oveq12i eqeq12i bitrdi expcom sylbir impcom pm2.61dan
        expd ) HDUCZIDUCZHIUDZUEZUFHUGZUFIUGZRZHIGSZAUHJUIZUGZTSZBUFUUSUGZTSZCU
        JSZRZJDUKZRUUNUUQUNZUURUVBUUORZJDUKZUVFUVGUUKUULUUQUHHUGZUHIUGZUDZUURUV
        IRUUKUULUUMUUQULUUKUULUUMUUQUMUUNUUQUOUUNUUQUVLUUKUULUUMUUQUVLUPUUKUULU
        NZUUQUUMUVLUVMUUQUUMUVLUPUVMUUQUNZUVJUVKHIUVNUVJUVKRZHIRZUVNUVOUNZUVPUA
        UIZHUGZUVRIUGZRZUAFUQZUVQUUQUVOUNZUWBUVNUUQUVOUVMUUQUOURUWBUWAUAUFUHUSZ
        UQUWCUWAUAFUWDKUTUWAUUQUVOUAUFUHVAVGUVRUFRUVSUUOUVTUUPUVRUFHVBUVRUFIVBV
        CUVRUHRUVSUVJUVTUVKUVRUHHVBUVRUHIVBVCVDVEVFUVQHFVHZIFVHZUNZUVPUWBVIUVMU
        WGUUQUVOUUKUWEUULUWFUWEHVJFVKSZDHVJFVLMVMUWFIUWHDIVJFVLMVMVNVOUAFHIVPVQ
        VRVSVTVSWAWBWCZDEFGHIJKLMNWDWEUVGUUQUUNUNZUVIUVFRUUNUUQWFZUWJUVHUVEJDUW
        JUUSDUCZUNZUVEWJUVKUVJWGSZUVBTSZUVJUUPTSZUUPUVKTSZWGSZUJSZRZUVBUUPRZUVH
        UWMUUNUWLUUQUVEUWTVIUUQUUNUWLWHUWJUWLUOUUQUUNUWLWIUUNUWLUNZUUQUNZUVAWJU
        VDUWSUXCUVAUUPUUOWGSZUUTTSZWJUUTTSWJUVAUXERUXCAUXDUUTTOWKWLUXCUXDWJUUTT
        UXCUXDUUPUUPWGSZWJUUQUXDUXFRUXBUUOUUPUUPWGWMWNUXCUUPUUNUUPXAUCZUWLUUQUU
        LUUKUXGUUMUULUUPDFIKMWOZWPWQZVOWRWSWTUXCUUTUWLUUTXAUCUUNUUQUWLUUTDFUUSK
        MXBZWPXCXDXEUXCUVCUWOCUWRUJUVCUWORUXCBUWNUVBTPWKWLUUQCUWRRUXBUUQCUWPUUO
        UVKTSZWGSZUWRQUUQUXKUWQUWPWGUUOUUPUVKTXFXGXHWNXIVCXJUWMUWTWJUWOUVJUVKWG
        SZUUPTSZUJSZRZUXAUWMUWSUXOWJUWMUWRUXNUWOUJUUNUWRUXNRUUQUWLUUNUWRUWPUVKU
        UPTSZWGSUXNUUNUWQUXQUWPWGUUNUUPUVKUXIUULUUKUVKXAUCZUUMUULUVKDFIKMXBZWPW
        QZXKXGUUNUVJUVKUUPUUKUULUVJXAUCZUUMUUKUVJDFHKMXBZWPXLZUXTUXIXMXNXCXGXOU
        WMUXPUXOWJRZUWOUXNXPZRZUXAUXPUYDVIUWMWJUXOXQWLUWMUWOXAUCUXNXAUCUYDUYFVI
        UWMUWNUVBUWMUVKUVJUUNUXRUUQUWLUXTXCZUUNUYAUUQUWLUYCXCZXRZUWLUVBXAUCUWJU
        WLUVBDFUUSKMWOZWPWNZXSUWMUXMUUPUWMUVJUVKUYHUYGXRZUUNUXGUUQUWLUXIXCZXSUW
        OUXNYAXTUWMUYFUWOUWNUUPTSZRUXAUWMUYEUYNUWOUWMUXMXPZUUPTSUYEUYNUWMUXMUUP
        UYLUYMYBUWMUYOUWNUUPTUWMUVJUVKUYHUYGYCWTYDXOUWMUVBUUPUWNUYKUYMUYIUWMUVK
        UVJUYGUYHUWJUVKUVJUDZUWLUVGUVLUWJUYPUWIUWKUVJUVKYJYEYFYGYHYKYIYKUWMUUPU
        UOUVBUWJUUPUUORUWLUWJUUOUUPUUQUUNYLYMYFXOYNYOYPWSUUNUUQYQZUNZUURUVBUFUB
        UIZWGSZUUOTSUYSUUPTSUJSRUUTUYTUVJTSUYSUVKTSUJSRUNUBVJYRZJDUKZUVFUUNUURV
        UBRUYQUBDEFGHIJKLMNYSYFUYRVUAUVEJDUYRUWLVUAUVEVIZUYQUUNUWLVUCUPUYQUUNUW
        LVUCUYQUUOUUPUDZUXBVUCUPUUOUUPUUAUXBVUDVUCUXBVUDUNZVUAUXEUWOUXLUJSZRUVE
        VUEUBUVBUUOUUPUUTUVJUVKUWLUVBVJUCUUNVUDUYJXCUUNUUOVJUCZUWLVUDUUKUULVUGU
        UMDFHKMWOXLVOUUNUUPVJUCZUWLVUDUULUUKVUHUUMUXHWQVOUXBVUDUOUWLUUTVJUCUUNV
        UDUXJXCUUNUVJVJUCZUWLVUDUUKUULVUIUUMUYBXLVOUUNUVKVJUCZUWLVUDUULUUKVUJUU
        MUXSWQVOUUBUXEUVAVUFUVDUXDAUUTTAUXDOYTWKUWOUVCUXLCUJUWNBUVBTBUWNPYTWKCU
        XLQYTUUCUUDUUEUUFUUGUUJUUHWCYOWSUUI $.
    $}

    $d S t $.
    rrx2linesl.s $e |- S = ( ( ( Y ` 2 ) - ( X ` 2 ) )
                             / ( ( Y ` 1 ) - ( X ` 1 ) ) ) $.
    $( The line passing through the two different points ` X ` and ` Y ` in a
       real Euclidean space of dimension 2, expressed by the slope ` S `
       between the two points ("point-slope form"), sometimes also written as
       ` ( ( p `` 2 ) - ( X `` 2 ) ) = ( S x. ( ( p `` 1 ) - ( X `` 1 ) ) ) ` .
       (Contributed by AV, 22-Jan-2023.) $)
    rrx2linesl $p |- ( ( X e. P /\ Y e. P /\ ( X ` 1 ) =/= ( Y ` 1 ) )
                       -> ( X L Y ) = { p e. P |
          ( p ` 2 ) = ( ( S x. ( ( p ` 1 ) - ( X ` 1 ) ) ) + ( X ` 2 ) ) } ) $=
      ( wcel c1 cfv co c2 cr a1i vt wne cv cmin cmul caddc wceq wrex crab fveq1
      w3a wa necon3i rrx2line syl3an3 cmap wf reex cpr cvv eqeltri elmap id 1ex
      prid1 eleqtrri ffvelcdmd sylbi eleq2s adantl 3ad2ant1 adantr 3ad2ant2 2ex
      prex simpl3 prid2 eleq2i bitri affinecomb1 rabbidva eqtrd ) FANZGANZOFPZO
      GPZUBZUKZFGEQZOHUCZPZOUAUCZUDQZWEUEQWLWFUEQUFQUGRWJPZWMRFPZUEQWLRGPZUEQUF
      QUGULUASUHZHAUIZWNBWKWEUDQUEQWOUFQUGZHAUIWGWCWDFGUBWIWRUGFGWEWFOFGUJUMUAA
      CDEFGHIJKLUNUOWHWQWSHAWHWJANZULUAWKWEWFBWNWOWPWTWKSNZWHXAWJSDUPQZAWJXBNZD
      SWJUQZXASDWJURDORUSZUTIORVOVAZVBZXDDSOWJXDVCZODNZXDOXEDORVDVEIVFZTVGVHKVI
      VJWHWESNZWTWCWDXKWGXKFXBAFXBNZDSFUQZXKSDFURXFVBZXMDSOFXMVCZXIXMXJTVGVHKVI
      VKVLWHWFSNZWTWDWCXPWGXPGXBAGXBNZDSGUQZXPSDGURXFVBZXRDSOGXRVCZXIXRXJTVGVHK
      VIVMVLWCWDWGWTVPWTWNSNZWHYAWJXBAXCXDYAXGXDDSRWJXHRDNZXDRXEDORVNVQIVFZTVGV
      HKVIVJWHWOSNZWTWCWDYDWGYDFXBAXLXMYDXNXMDSRFXOYBXMYCTVGVHKVIVKVLWHWPSNZWTW
      DWCYEWGWDXRYEWDXQXRAXBGKVRXSVSXRDSRGXTYBXRYCTVGVHVMVLMVTWAWB $.
  $}

  ${
    $d E p $.  $d I p $.  $d P p $.  $d X p $.  $d Y p $.
    rrx2linest2.i $e |- I = { 1 , 2 } $.
    rrx2linest2.e $e |- E = ( RR^ ` I ) $.
    rrx2linest2.p $e |- P = ( RR ^m I ) $.
    rrx2linest2.l $e |- L = ( LineM ` E ) $.
    ${
      rrx2linest2.a $e |- A = ( ( X ` 2 ) - ( Y ` 2 ) ) $.
      rrx2linest2.b $e |- B = ( ( Y ` 1 ) - ( X ` 1 ) ) $.
      rrx2linest2.c $e |- C = ( ( ( X ` 2 ) x. ( Y ` 1 ) )
                             - ( ( X ` 1 ) x. ( Y ` 2 ) ) ) $.
      $( The line passing through the two different points ` X ` and ` Y ` in a
         real Euclidean space of dimension 2 in another "standard form"
         (usually with ` ( p `` 1 ) = x ` and ` ( p `` 2 ) = y ` ).
         (Contributed by AV, 23-Feb-2023.) $)
      rrx2linest2 $p |- ( ( X e. P /\ Y e. P /\ X =/= Y ) -> ( X L Y )
            = { p e. P | ( ( A x. ( p ` 1 ) ) + ( B x. ( p ` 2 ) ) ) = C } ) $=
        ( wcel co cr wne w3a c2 cv cmul cmin c1 caddc wceq crab eqid rrx2linest
        cfv wa eqcom rrx2pyel 3ad2ant2 3ad2ant1 resubcld adantr rrx2pxel adantl
        remulcld recnd eqeltrid addrsub cneg addcomd negsubdi2d oveq1d mulneg1d
        eqtr4id eqtrd oveq2d negsubd 3eqtrd eqeq1d bitr4id bitrid rabbidva
        bitrd ) HDRZIDRZHIUAZUBZHIGSBUCJUDZUMZUESZUCIUMZUCHUMZUFSZUGWFUMZUESZCU
        HSZUIZJDUJAWLUESZWHUHSZCUIZJDUJBWKCDEFGHIJKLMNPWKUKQULWEWOWRJDWOWNWHUIZ
        WEWFDRZUNZWRWHWNUOXAWSCWHWMUFSZUIZWRXAWMCWHXAWMXAWKWLWEWKTRWTWEWIWJWCWB
        WITRZWDDFIKMUPUQZWBWCWJTRZWDDFHKMUPURZUSUTZWTWLTRWEDFWFKMVAVBZVCVDZXACW
        ECTRWTWECWJUGIUMZUESZUGHUMZWIUESZUFSTQWEXLXNWEWJXKXGWCWBXKTRWDDFIKMVAUQ
        ZVCWEXMWIWBWCXMTRWDDFHKMVAURZXEVCUSVEUTVDXAWHXABWGWEBTRWTWEBXKXMUFSTPWE
        XKXMXOXPUSVEUTWTWGTRWEDFWFKMUPVBVCVDZVFXAXCXBCUIWRCXBUOXAWQXBCXAWQWHWPU
        HSWHWMVGZUHSXBXAWPWHXAWPXAAWLWEATRWTWEAWJWIUFSZTOWEWJWIXGXEUSVEUTXIVCVD
        XQVHXAWPXRWHUHXAWPWKVGZWLUESXRXAAXTWLUEXAAXSXTOXAWIWJXAWIWEXDWTXEUTVDXA
        WJWEXFWTXGUTVDVIVLVJXAWKWLXAWKXHVDXAWLXIVDVKVMVNXAWHWMXQXJVOVPVQVRWAVSV
        TVM $.

      $d A p $.  $d B p $.  $d C p $.  $d G p $.
      $( The line passing through the two different points ` X ` and ` Y ` in a
         real Euclidean space of dimension 2 in another "standard form"
         (usually with ` ( p `` 1 ) = x ` and ` ( p `` 2 ) = y ` ).
         (Contributed by AV, 23-Feb-2023.) $)
      elrrx2linest2 $p |- ( ( X e. P /\ Y e. P /\ X =/= Y ) -> ( G e. ( X L Y )
       <-> ( G e. P /\ ( ( A x. ( G ` 1 ) ) + ( B x. ( G ` 2 ) ) ) = C ) ) ) $=
        ( wcel co cmul vp wne w3a c1 cv cfv c2 caddc wceq wa rrx2linest2 eleq2d
        crab fveq1 oveq2d oveq12d eqeq1d elrab bitrdi ) IDRJDRIJUBUCZFIJHSZRFAU
        DUAUEZUFZTSZBUGVBUFZTSZUHSZCUIZUADUMZRFDRAUDFUFZTSZBUGFUFZTSZUHSZCUIZUJ
        UTVAVIFABCDEGHIJUAKLMNOPQUKULVHVOUAFDVBFUIZVGVNCVPVDVKVFVMUHVPVCVJATUDV
        BFUNUOVPVEVLBTUGVBFUNUOUPUQURUS $.
    $}
  $}

  ${
    $d B p r w x $.  $d D w $.  $d V w $.  $d W p r w x $.
    spheres.b $e |- B = ( Base ` W ) $.
    spheres.l $e |- S = ( Sphere ` W ) $.
    spheres.d $e |- D = ( dist ` W ) $.
    $( The spheres for given centers and radii in a metric space (or any
       extensible structure having a base set and a distance function).
       (Contributed by AV, 22-Jan-2023.) $)
    spheres $p |- ( W e. V -> S = ( x e. B , r e. ( 0 [,] +oo )
                                    |-> { p e. B | ( p D x ) = r } ) ) $=
      ( vw cfv co cv wceq a1i cbs cds cvv wcel csph cpnf cicc crab df-sph fveq2
      cc0 cmpo eqcomi eqtrd eqidd eqeq1d rabeqbidv mpoeq123dv elex fvex eqeltri
      oveqd ovex mpoex fvmptd3 ) FEUAZDFUBMZAGBUHUCUDNZHOZAOZCNZGOZPZHBUEZUIZDV
      DPVCJQVCLFAGLOZRMZVEVFVGVMSMZNZVIPZHVNUEZUIVLTUBTALGHUFVMFPZAGVNVEVRBVEVK
      VSVNFRMZBVMFRUGVTBPVSBVTIUJQUKZVSVEULVSVQVJHVNBWAVSVPVHVIVSVOCVFVGVSVOFSM
      ZCVMFSUGWBCPVSCWBKUJQUKUSUMUNUOFEUPVLTUAVCAGBVEVKBVTTIFRUQURUHUCUDUTVAQVB
      UK $.

    $d D r x $.  $d R p r x $.  $d V r x $.  $d X p r x $.
    $( A sphere with center ` X ` and radius ` R ` in a metric space (or any
       extensible structure having a base set and a distance function).
       (Contributed by AV, 22-Jan-2023.) $)
    sphere $p |- ( ( W e. V /\ X e. B /\ R e. ( 0 [,] +oo ) )
                   -> ( X S R ) = { p e. B | ( p D X ) = R } ) $=
      ( vx vr wcel cc0 co cv wceq crab cvv cpnf cicc w3a spheres 3ad2ant1 oveq2
      cmpo wa eqeqan12d rabbidv adantl simp2 simp3 cbs fvexi rabex a1i ovmpod
      id ) FENZGANZCOUAUBPZNZUCZLMGCAVBHQZLQZBPZMQZRZHASZVEGBPZCRZHASZDTUTVADLM
      AVBVJUGRVCLABDEFMHIJKUDUEVFGRZVHCRZUHZVJVMRVDVPVIVLHAVNVOVGVKVHCVFGVEBUFV
      OUSUIUJUKUTVAVCULUTVAVCUMVMTNVDVLHAAFUNIUOUPUQUR $.
  $}

  ${
    $d E p r x $.  $d I p $.  $d M p $.  $d P p $.  $d R p $.
    rrxspheres.e $e |- E = ( RR^ ` I ) $.
    rrxspheres.p $e |- P = ( RR ^m I ) $.
    rrxspheres.d $e |- D = ( dist ` E ) $.
    rrxspheres.s $e |- S = ( Sphere ` E ) $.
    $( The sphere with center ` M ` and radius ` R ` in a generalized real
       Euclidean space of finite dimension.  Remark: this theorem holds also
       for the degenerate case ` R < 0 ` (negative radius): in this case,
       ` ( M S R ) ` is empty.  (Contributed by AV, 5-Feb-2023.) $)
    rrxsphere $p |- ( ( I e. Fin /\ M e. P /\ R e. RR )
                      -> ( M S R ) = { p e. P | ( p D M ) = R } ) $=
      ( vx cc0 wcel co wceq wa cfv c0 vr cle wbr cfn cr w3a cv crab wi cbs cpnf
      cvv cicc crrx cmap id eqid rrxbasefi eqtr4id eleq2d biimpa 3adant3 adantl
      fvexi cxr rexr 3ad2ant3 anim2i ancomd elxrge0 sylibr sphere mp3an2i simp1
      eqtr4di rabeqdv eqtrd ex wn cdm cxp cmpo spheres ax-mp rabex dmmpo wb 0xr
      fvex pnfxr pm3.2i elicc1 mp1i simp2 biimtrdi con3d intnand ndmovg sylancr
      imp wral cds fveq2i eqtri rrxmetfi 3ad2ant1 adantr eleqtrrdi simpr metge0
      cmet syl3anc breq2 syl5ibcom impancom ralrimiva eqcom rabeq0 bitri expcom
      pm2.61i ) NCUBUCZFUDOZGBOZCUEOZUFZGCDPZHUGZGAPZCQZHBUHZQZUIYBYFYLYBYFRZYG
      YJHEUJSZUHZYKEULOZYMGYNOZCNUKUMPZOZYGYOQEFUNIVDZYFYQYBYCYDYQYEYCYDYQYCBYN
      GYCBUEFUOPZYNJYCYNEFYCUPIYNUQZURUSUTVAVBVCYMCVEOZYBRYSYMYBUUCYFUUCYBYEYCU
      UCYDCVFVGVHVICVJVKYNACDULEGHUUBLKVLVMYMYJHYNBYFYNBQYBYFYNUUABYFYNEFYCYDYE
      VNIUUBURJVOVCVPVQVRYFYBVSZYLYFUUDRZYGTYKUUEDVTYNYRWAQYQYSRVSYGTQMUAYNYRYH
      MUGAPUAUGQZHYNUHZDYPDMUAYNYRUUGWBQYTMYNADULEUAHUUBLKWCWDUUFHYNEUJWIWEWFUU
      EYSYQYFUUDYSVSYFYSYBYFYSUUCYBCUKUBUCZUFZYBNVEOZUKVEOZRYSUUIWGYFUUJUUKWHWJ
      WKNUKCWLWMUUCYBUUHWNWOWPWTWQGCYNYRDWRWSUUEYJVSZHBXAZTYKQZUUEUULHBUUEYHBOZ
      UULYFUUOUUDUULYFUUORZYJYBUUPNYIUBUCZYJYBUUPABXKSZOUUOYDUUQUUPAUUAXKSZUURY
      FAUUSOZUUOYCYDUUTYEAFAEXBSFUNSZXBSKEUVAXBIXCXDXEXFXGBUUAXKJXCXHYFUUOXIYFY
      DUUOYCYDYEWNXGYHGABXJXLYICNUBXMXNWPXOWTXPUUNYKTQUUMTYKXQYJHBXRXSVKVQXTYA
      $.
  $}

  ${
    $d E p $.  $d I p $.  $d M p $.  $d P p $.  $d R p $.
    2sphere.i $e |- I = { 1 , 2 } $.
    2sphere.e $e |- E = ( RR^ ` I ) $.
    2sphere.p $e |- P = ( RR ^m I ) $.
    2sphere.s $e |- S = ( Sphere ` E ) $.
    ${
      2sphere.c $e |- C = { p e. P | ( ( ( ( p ` 1 ) - ( M ` 1 ) ) ^ 2 )
                         + ( ( ( p ` 2 ) - ( M ` 2 ) ) ^ 2 ) ) = ( R ^ 2 ) } $.
      $( The sphere with center ` M ` and radius ` R ` in a two dimensional
         Euclidean space is a circle.  (Contributed by AV, 5-Feb-2023.) $)
      2sphere $p |- ( ( M e. P /\ R e. ( 0 [,) +oo ) ) -> ( M S R ) = C ) $=
        ( wcel co wa cfv wceq cr c2 cc0 cpnf cico cds crab cfn cpr prfi eqeltri
        cv c1 simpl cle elrege0 simplbi adantl eqid rrxsphere mp3an2i cmin cexp
        wbr caddc biimpi ad2antlr sqrtsq syl eqeq2d wb rrx2pxel adantr resubcld
        csqrt resqcld rrx2pyel readdcld sqge0d addge0d jca adantlr resqcl sqge0
        sqrt11 syl2anc anim1ci crrx cehl 2nn0 ehlval ax-mp fz12pr eqtr4i fveq2i
        cfz cn0 cmap oveq2i ehl2eudisval eqcomd eqeq1d 3bitr3d rabbidva eqtr2id
        eqtri eqtrd ) GBNZCUAUBUCONZPZGCDOZHUJZGEUDQZOZCRZHBUEZAFUFNXHXFCSNZXIX
        NRFUKTUGZUFIUKTUHUIXFXGULZXGXOXFXGXOUACUMVBZCUNZUOZUPXKBCDEFGHJKXKUQZLU
        RUSXHAUKXJQZUKGQZUTOZTVAOZTXJQZTGQZUTOZTVAOZVCOZCTVAOZRZHBUEXNMXHYLXMHB
        XHXJBNZPZYJVMQZYKVMQZRZYOCRYLXMYNYPCYOYNXOXRPZYPCRXGYRXFYMXGYRXSVDVECVF
        VGVHYNYJSNZUAYJUMVBZPZYKSNZUAYKUMVBZPZYQYLVIXFYMUUAXGXFYMPZYSYTUUEYEYIU
        UEYDUUEYBYCYMYBSNXFBFXJIKVJUPXFYCSNYMBFGIKVJVKVLZVNZUUEYHUUEYFYGYMYFSNX
        FBFXJIKVOUPXFYGSNYMBFGIKVOVKVLZVNZVPUUEYEYIUUGUUIUUEYDUUFVQUUEYHUUHVQVR
        VSVTXGUUDXFYMXGXOUUDXTXOUUBUUCCWACWBVSVGVEYJYKWCWDYNYOXLCYNXLYOYNYMXFPX
        LYORXHXFYMXQWEXKEXJGBEFWFQZTWGQZJUUKUKTWNOZWFQZUUJTWONUUKUUMRWHUUKTUUKU
        QWIWJUULFWFUULXPFWKIWLWMXDWLBSFWPOSXPWPOKFXPSWPIWQXDYAWRVGWSWTXAXBXCXE
        $.
    $}

    ${
      $d .0. p $.
      2sphere0.0 $e |- .0. = ( I X. { 0 } ) $.
      2sphere0.c $e |- C = { p e. P | ( ( ( p ` 1 ) ^ 2 )
                                      + ( ( p ` 2 ) ^ 2 ) ) = ( R ^ 2 ) } $.
      $( The sphere around the origin ` .0. ` (see ~ rrx0 ) with radius ` R `
         in a two dimensional Euclidean space is a circle.  (Contributed by AV,
         5-Feb-2023.) $)
      2sphere0 $p |- ( R e. ( 0 [,) +oo ) -> ( .0. S R ) = C ) $=
        ( cc0 co wcel c1 c2 cexp cpnf cico cv cfv cmin caddc wceq crab cvv prex
        cpr eqeltri rrx0el ax-mp eqid 2sphere mpan wb csn cxp fveq1i c0ex prid1
        1ex eleqtrri fvconst2g mp2an eqtri oveq2d rrx2pxel recnd subid1d oveq1d
        a1i eqtrd 2ex prid2 rrx2pyel oveq12d eqeq1d adantl rabbidva eqtr4di ) C
        OUAUBPQZGCDPZRHUCZUDZRGUDZUEPZSTPZSWFUDZSGUDZUEPZSTPZUFPZCSTPZUGZHBUHZA
        GBQZWDWEWRUGFUIQWSFRSUKZUIIRSUJULBFUIGMKUMUNWRBCDEFGHIJKLWRUOUPUQWDWRWG
        STPZWKSTPZUFPZWPUGZHBUHAWDWQXDHBWFBQZWQXDURWDXEWOXCWPXEWJXAWNXBUFXEWIWG
        STXEWIWGOUEPWGXEWHOWGUEWHOUGXEWHRFOUSUTZUDZORGXFMVAOUIQZRFQXGOUGVBRWTFR
        SVDVCIVEFORUIVFVGVHVNVIXEWGXEWGBFWFIKVJVKVLVOVMXEWMWKSTXEWMWKOUEPWKXEWL
        OWKUEWLOUGXEWLSXFUDZOSGXFMVAXHSFQXIOUGVBSWTFRSVPVQIVEFOSUIVFVGVHVNVIXEW
        KXEWKBFWFIKVRVKVLVOVMVSVTWAWBNWCVO $.
    $}
  $}

  ${
    $d A p $.  $d B p $.  $d C p $.  $d P p $.
    line2ylem.i $e |- I = { 1 , 2 } $.
    line2ylem.p $e |- P = ( RR ^m I ) $.
    $( Lemma for ~ line2y .  This proof is based on counterexamples for the
       following cases: 1. ` C =/= 0 ` : p = (0,0) (LHS of biconditional is
       false, RHS is true); 2. ` C = 0 /\ B =/= 0 ` : p = (1,-A/B) (LHS of
       biconditional is true, RHS is false); 3. ` A = B = C = 0 ` : p = (1,1)
       (LHS of biconditional is true, RHS is false).  (Contributed by AV,
       4-Feb-2023.) $)
    line2ylem $p |- ( ( A e. RR /\ B e. RR /\ C e. RR )
               -> ( A. p e. P ( ( ( A x. ( p ` 1 ) ) + ( B x. ( p ` 2 ) ) ) = C
                    <-> ( p ` 1 ) = 0 ) -> ( A =/= 0 /\ B = 0 /\ C = 0 ) ) ) $=
      ( wcel c1 cmul co c2 caddc wceq cc0 wb wn eqtrdi cvv cr w3a cv cfv wne wa
      wral wrex wo ianor wi df-ne cop cpr prelrrx2 mp2an eqneqall com12 pm2.24i
      0re eqid impbid1 adantl xor3 sylibr simp1 recnd mul01d simp2 oveq12d 00id
      eqeq1d eqcom bitrdi adantr bibi1d mtbird fveq1 1ex c0ex 1ne2 fvpr1g mp3an
      oveq2d fvpr2g bibi12d notbid rspcev sylancr expcom notnotb cneg cdiv 1red
      2ex sylbir renegcld simprl redivcld syl2anc ax-1ne0 neii mpbir mulridd cc
      2th negcld divcan2d negidd eqtrd simprr eqeq12d mtbiri ovex ex nne bicomi
      1re oveq1 ax-1cn mul02i id eqeqan12d syl2anbr jaoi3 orcoms sylbi biimtrid
      a1d imp rexnal imbitrdi con4d df-3an imbitrrdi ) AUAIZBUAIZCUAIZUBZAJFUCZ
      UDZKLZBMYTUDZKLZNLZCOZUUAPOZQZFDUGZAPUEZBPOZUFZCPOZUFZUUJUUKUUMUBYSUUNUUI
      YSUUNRZUUHRZFDUHZUUIRUUOUULRZUUMRZUIZYSUUQUULUUMUJUUTYSUUQUUSUURYSUUQUKZU
      USUVAUURUUSCPUEZUVACPULYSUVBUUQYSUVBUFZJPUMMPUMUNZDIZAPKLZBPKLZNLZCOZPPOZ
      QZRZUUQPUAIZUVMUVEUTUTPPDEGHUOUPUVCUVKUUMUVJQZUVCUUMUVJRZQZUVNRUVBUVPYSUV
      BUUMUVOUUMUVBUVOUVOCPUQURUVJUUMPVAZUSVBVCUUMUVJVDVEUVCUVIUUMUVJYSUVIUUMQU
      VBYSUVIPCOUUMYSUVHPCYSUVHPPNLZPYSUVFPUVGPNYSAYSAYPYQYRVFZVGZVHYSBYSBYPYQY
      RVIZVGZVHVJVKSVLPCVMVNVOVPVQUUPUVLFUVDDYTUVDOZUUHUVKUWCUUFUVIUUGUVJUWCUUE
      UVHCUWCUUBUVFUUDUVGNUWCUUAPAKUWCUUAJUVDUDZPJYTUVDVRJTIZPTIZJMUEZUWDPOVSVT
      WAJMPPTTWBWCSZWDUWCUUCPBKUWCUUCMUVDUDZPMYTUVDVRMTIZUWFUWGUWIPOWOVTWAJMPPT
      TWEWCSWDVJVLUWCUUAPPUWHVLWFWGWHWIWJWPUUSRZUURUVAUWKUUMUURUVAUKUUMWKUURUUM
      UVAUURUUJRZUUKRZUIUUMUVAUKZUUJUUKUJUWMUWLUWNUWMUWNUWLUWMBPUEZUWNBPULUWOUU
      MUVAYSUWOUUMUFZUUQYSUWPUFZJJUMZMAWLZBWMLZUMUNZDIZAJKLZBUWTKLZNLZCOZJPOZQZ
      RZUUQUWQJUAIZUWTUAIUXBUWQWNUWQUWSBUWQAYSYPUWPUVSVOWQYSYQUWPUWAVOYSUWOUUMW
      RZWSJUWTDEGHUOWTUWQUXHUVJUXGQZUXLRUVJUXGRZQUVJUXMUVQJPXAXBXFUVJUXGVDXCZUW
      QUXFUVJUXGUWQUXEPCPUWQUXEAUWSNLZPUWQUXCAUXDUWSNYSUXCAOUWPYSAUVTXDVOUWQUWS
      BYSUWSXEIUWPYSAUVTXGVOYSBXEIUWPUWBVOUXKXHVJYSUXOPOUWPYSAUVTXIVOXJYSUWOUUM
      XKXLVPXMUUPUXIFUXADYTUXAOZUUHUXHUXPUUFUXFUUGUXGUXPUUEUXECUXPUUBUXCUUDUXDN
      UXPUUAJAKUXPUUAJUXAUDZJJYTUXAVRUWEUWEUWGUXQJOVSVSWAJMJUWTTTWBWCSZWDUXPUUC
      UWTBKUXPUUCMUXAUDZUWTMYTUXAVRUWJUWTTIUWGUXSUWTOWOUWSBWMXNWAJMJUWTTTWEWCSW
      DVJVLUXPUUAJPUXRVLWFWGWHWTWJXOWPUWMRUUKAPOZUWNUWLUUKWKUWLUXTAPXPXQUUKUXTU
      FZUUMUVAUYAUUMUFZUUQYSUYBUWRMJUMUNZDIZUXCBJKLZNLZCOZUXGQZRZUUQUXJUXJUYDXR
      XRJJDEGHUOUPUYBUYHUXLUXNUYBUYGUVJUXGUYAUUMUYFPCPUYAUYFUVRPUYAUXCPUYEPNUYA
      UXCPJKLZPUXTUXCUYJOUUKAPJKXSVCJXTYAZSUYAUYEUYJPUUKUYEUYJOUXTBPJKXSVOUYKSV
      JVKSUUMYBYCVPXMUUPUYIFUYCDYTUYCOZUUHUYHUYLUUFUYGUUGUXGUYLUUEUYFCUYLUUBUXC
      UUDUYENUYLUUAJAKUYLUUAJUYCUDZJJYTUYCVRUWEUWEUWGUYMJOVSVSWAJMJJTTWBWCSZWDU
      YLUUCJBKUYLUUCMUYCUDZJMYTUYCVRUWJUWEUWGUYOJOWOVSWAJMJJTTWEWCSWDVJVLUYLUUA
      JPUYNVLWFWGWHWIYIXOYDYEYFYGURWPYJYEYFURYHUUHFDYKYLYMUUJUUKUUMYNYO $.
  $}

  ${
    $d A p $.  $d B p $.  $d C p $.  $d E p $.  $d I p $.  $d P p $.  $d X p $.
    $d Y p $.
    line2.i $e |- I = { 1 , 2 } $.
    line2.e $e |- E = ( RR^ ` I ) $.
    line2.p $e |- P = ( RR ^m I ) $.
    line2.l $e |- L = ( LineM ` E ) $.
    line2.g $e |- G = { p e. P | ( ( A x. ( p ` 1 ) )
                                   + ( B x. ( p ` 2 ) ) ) = C } $.
    ${
      line2.x $e |- X = { <. 1 , 0 >. , <. 2 , ( C / B ) >. } $.
      line2.y $e |- Y = { <. 1 , 1 >. , <. 2 , ( ( C - A ) / B ) >. } $.
      $( Example for a line ` G ` passing through two different points in
         "standard form".  (Contributed by AV, 3-Feb-2023.) $)
      line2 $p |- ( ( A e. RR /\ ( B e. RR /\ B =/= 0 ) /\ C e. RR )
                    -> G = ( X L Y ) ) $=
        ( c1 co cr wcel cc0 wne wa w3a cv cfv cmul c2 caddc wceq crab cmin cdiv
        cneg simp1 adantr rrx2pxel adantl remulcld recnd simpl2l rrx2pyel simpl
        cc 3ad2ant2 simp2r divdird divcan3d oveq2d eqtrd redivcld simp3 addrsub
        eqeq1d simpl3 negsubdi2d negsubdid eqtr3d eqeq2d 3bitrd readdcld anim1i
        wb recn div11 syl3anc divnegd mulneg1d eqcomd oveq1d 3ad2ant1 div23 cop
        renegcl cpr fveq1i cvv 1ex c0ex 1ne2 3pm3.2i fvpr1g mp1i eqtrid subid1d
        eqtr2d 3eqtrd 3bitr3d sub32 subid eqtr4di 3adant2 bitrd 2ex a1i resubcl
        df-neg ancoms 3jca fvpr2g syl mp3an2i oveq12d fvpr1 ax-mp eqtri eqeltrd
        cmap wf jctil fprg prssd fssd feq1i sylibr reex elmap eleqtrrdi oveq12i
        resubcld divsubdir 1m0e1 subcld div1d pm3.2i 0red prex oveq2i 1red 0ne1
        rabbidva neeq12i mpbir eqid rrx2linesl 3eqtr4d ) AUAUBZBUAUBZBUCUDZUEZC
        UAUBZUFZASKUGZUHZUITZBUJUVEUHZUITZUKTZCULZKDUMZUVHUJJUHZUJIUHZUNTZSJUHZ
        SIUHZUNTZUOTZUVFUVQUNTZUITZUVNUKTZULZKDUMZFIJHTZUVDUVKUWCKDUVDUVEDUBZUE
        ZUVKUVHCAUNTZCUNTZBUOTZUVTUITZCBUOTZUKTZULZUVHUVOUVTUITZUWLUKTZULUWCUWG
        UVKUVHAUPZBUOTZUVTUITZUWLUKTZULZUWNUWGUVJBUOTZUWLULZUVHUVGBUOTZUPZUWLUK
        TZULZUVKUXAUWGUXCUXDUVHUKTZUWLULUVHUWLUXDUNTZULUXGUWGUXBUXHUWLUWGUXBUXD
        UVIBUOTZUKTUXHUWGUVGUVIBUWGUVGUWGAUVFUVDUUSUWFUUSUVBUVCUQZURUWFUVFUAUBU
        VDDGUVELNUSZUTVAZVBZUWGUVIUWGBUVHUUTUVAUUSUVCUWFVCZUWFUVHUAUBUVDDGUVELN
        VDZUTVAZVBUVDBVFUBZUWFUVBUUSUXRUVCUVBBUUTUVAVEZVBVGURZUVDUVAUWFUUSUUTUV
        AUVCVHZURZVIUWGUXJUVHUXDUKUWGUVHBUWFUVHVFUBUVDUWFUVHUXPVBUTZUXTUYBVJVKV
        LVPUWGUXDUVHUWLUWGUXDUWGUVGBUXMUXOUYBVMVBZUYCUVDUWLVFUBUWFUVDUWLUVDCBUU
        SUVBUVCVNZUVBUUSUUTUVCUXSVGZUYAVMZVBZURVOUWGUXIUXFUVHUWGUXDUWLUNTUPUXIU
        XFUWGUXDUWLUYDUWGUWLUWGCBUUSUVBUVCUWFVQUXOUYBVMVBZVRUWGUXDUWLUYDUYIVSVT
        WAWBUWGUVJVFUBCVFUBZUXRUVAUEZUXCUVKWEUWGUVJUWGUVGUVIUXMUXQWCVBUVDUYJUWF
        UVDCUYEVBZURUVDUYKUWFUVBUUSUYKUVCUUTUXRUVABWFWDVGZURZUVJCBWGWHUWGUXFUWT
        UVHUWGUXEUWSUWLUKUWGUXEUWQUVFUITZBUOTZUWRUVFUITZUWSUWGUXEUVGUPZBUOTUYPU
        WGUVGBUXNUXTUYBWIUWGUYRUYOBUOUWGUYOUYRUWGAUVFUVDAVFUBZUWFUVDAUXKVBURUWF
        UVFVFUBZUVDUWFUVFUXLVBUTZWJWKWLVLUWGUWQVFUBZUYTUYKUYPUYQULUVDVUBUWFUUSU
        VBVUBUVCUUSUWQAWPVBWMURVUAUYNUWQUVFBWNWHUWGUVFUVTUWRUIUWGUVTUVFUCUNTUVF
        UWGUVQUCUVFUNUVDUVQUCULUWFUVDUVQSSUCWOUJUWLWOWQZUHZUCSIVUCQWRZSWSUBZUCW
        SUBZSUJUDZUFZVUDUCULZUVDVUFVUGVUHWTXAXBXCZSUJUCUWLWSWSXDZXEXFURVKUWGUVF
        VUAXGXHVKXIWLWAXJUWGUWTUWMUVHUWGUWSUWKUWLUKUWGUWRUWJUVTUIUVDUWRUWJULUWF
        UVDUWQUWIBUOUUSUVCUWQUWIULZUVBUUSUVCUEUYJUYSUYJVUMUVCUYJUUSCWFUTZUUSUYS
        UVCAWFURVUNUYJUYSUYJUFZUWICCUNTZAUNTZUWQCACXKVUOVUQUCAUNTUWQVUOVUPUCAUN
        UYJUYSVUPUCULUYJCXLWMWLAXSXMXHWHXNWLURWLWLWAXOUWGUWMUWPUVHUWGUWKUWOUWLU
        KUWGUWJUVOUVTUIUWGUVOUWHBUOTZUWLUNTZUWJUWGUVMVURUVNUWLUNUWGUVMUJSSWOUJV
        URWOWQZUHZVURUJJVUTRWRZUWGUJWSUBZVURUAUBZVUHUFZVVAVURULZUVDVVEUWFUVDVVC
        VVDVUHVVCUVDXPXQUVDUWHBUUSUVCUWHUAUBZUVBUVCUUSVVGCAXRXTXNUYFUYAVMZVUHUV
        DXBXQZYAURSUJSVURWSUAYBZYCXFUVDUVNUWLULUWFUVDUVNUJVUCUHZUWLUJIVUCQWRVVC
        UVDUWLUAUBZVUHVVKUWLULXPUYGVVISUJUCUWLWSUAYBYDXFZURYEUVDVUSUWJULUWFUVDU
        WJVUSUVDUWHVFUBUYJUYKUWJVUSULUVDUWHUVDCAUYEUXKUUBVBUYLUYMUWHCBUUCWHWKUR
        XHWLWLWAUWGUWPUWBUVHUWGUWBUWPUVDUWBUWPULUWFUVDUWAUWOUVNUWLUKUVDUVSUVOUV
        TUIUVDUVSUVOSUOTUVOUVDUVRSUVOUOUVRSULUVDUVRSUCUNTSUVPSUVQUCUNUVPSVUTUHZ
        SSJVUTRWRZVUHVVNSULZXBSUJSVURWTWTYFYGYHUVQVUDUCVUEVUHVUJXBSUJUCUWLWTXAY
        FYGYHUUAUUDYHXQVKUVDUVOUVDUVMUVNUVDUVMVURVFUVDUVMVVAVURVVBVVCUVDVVDVUHV
        VFXPVVHVVIVVJYDXFUVDVURVVHVBYIUVDUVNUWLVFVVMUYHYIUUEUUFVLWLVVMYEURWKWAW
        BUUMFUVLULUVDPXQUVDIDUBJDUBUVQUVPUDZUWEUWDULUVDIUASUJWQZYJTZDUVDVVRUAIY
        KZIVVSUBUVDVVRUAVUCYKVVTUVDVVRUCUWLWQZUAVUCVUFVVCUEZUVDVUGVVLUEVUHVVRVW
        AVUCYKVUFVVCWTXPUUGZUVDVVLVUGUYGXAYLVVISUJUCUWLWSWSWSUAYMYDUVDUCUWLUAUV
        DUUHUYGYNYOVVRUAIVUCQYPYQUAVVRIYRSUJUUIZYSYQDUAGYJTVVSNGVVRUAYJLUUJYHZY
        TUVDJVVSDUVDVVRUAJYKZJVVSUBUVDVVRUAVUTYKVWFUVDVVRSVURWQZUAVUTVWBUVDVUFV
        VDUEVUHVVRVWGVUTYKVWCUVDVVDVUFVVHWTYLVVISUJSVURWSWSWSUAYMYDUVDSVURUAUVD
        UUKVVHYNYOVVRUAJVUTRYPYQUAVVRJYRVWDYSYQVWEYTVVQUVDVVQUCSUDUULUVQUCUVPSU
        VQVUDUCVUEVUIVUJVUKVULYGYHUVPVVNSVVOVUFVUFVUHUFVVPVUFVUFVUHWTWTXBXCSUJS
        VURWSWSXDYGYHUUNUUOXQDUVSEGHIJKLMNOUVSUUPUUQWHUUR $.
    $}

    ${
      $d M p $.
      line2x.x $e |- X = { <. 1 , 0 >. , <. 2 , M >. } $.
      line2x.y $e |- Y = { <. 1 , 1 >. , <. 2 , M >. } $.
      $( Lemma for ~ line2x .  This proof is based on counterexamples for the
         following cases: 1. ` M =/= ( C / B ) ` : p = (0,C/B) (LHS of
         biconditional is true, RHS is false); 2.
         ` A =/= 0 /\ M = ( C / B ) ` : p = (1,C/B) (LHS of biconditional is
         false, RHS is true).  (Contributed by AV, 4-Feb-2023.) $)
      line2xlem $p |- ( ( ( A e. RR /\ ( B e. RR /\ B =/= 0 ) /\ C e. RR )
                       /\ M e. RR )
               -> ( A. p e. P ( ( ( A x. ( p ` 1 ) ) + ( B x. ( p ` 2 ) ) ) = C
                    <-> ( p ` 2 ) = M ) -> ( A = 0 /\ M = ( C / B ) ) ) ) $=
        ( wceq cr wcel cc0 wne wa w3a cdiv co c1 cv cmul c2 caddc wb wral wn wo
        cfv ianor df-ne orbi12i bitr4i wrex cop cpr simp3 adantr simpl 3ad2ant2
        wi 0red simp2r redivcld adantl prelrrx2 syl2anc necomd neneqd a1d eqidd
        id a1i impbid xor3 sylibr fv1prop syl oveq2d recn mul01d 3ad2ant1 eqtrd
        cvv ovexd fv2prop cc recnd divcan2d oveq12d addlidd eqeq1d mtbird fveq1
        bibi12d notbid rspcev nne 1red jca eqneqall com12 pm2.24 eqcoms simprl1
        ex addcomd anim12ci 3adant2 addid0 bitrd bibi1d 1ex mpbird sylanb jaoi3
        ax-1rid orcoms rexnal imbitrdi biimtrid con4d ) AUAUBZBUAUBZBUCUDZUEZCU
        AUBZUFZIUAUBZUEZAUCTZICBUGUHZTZUEZAUILUJZURZUKUHZBULUUDURZUKUHZUMUHZCTZ
        UUGITZUNZLDUOZUUCUPZAUCUDZIUUAUDZUQZYSUUMUPZUUNYTUPZUUBUPZUQUUQYTUUBUSU
        UOUUSUUPUUTAUCUTIUUAUTVAVBYSUUQUULUPZLDVCZUURUUQYSUVBUUPUUOYSUVBVJZUUPU
        VCUUOUUPYSUVBUUPYSUEZUIUCVDULUUAVDZVEZDUBZAUIUVFURZUKUHZBULUVFURZUKUHZU
        MUHZCTZUVJITZUNZUPZUVBUVDUCUAUBZUUAUAUBZUVGUVDVKYSUVRUUPYSCBYQYPYRYLYOY
        PVFZVGZYQYMYRYOYLYMYPYMYNVHZVIZVGYQYNYRYLYMYNYPVLZVGZVMVNUCUUADGMOVOVPU
        VDUVOCCTZUUAITZUNZUUPUWGUPZYSUUPUWEUWFUPZUNUWHUUPUWEUWIUUPUWIUWEUUPUUAI
        UUPIUUAUUPWAVQVRVSUWIUWEVJUUPUWICVTWBWCUWEUWFWDWEVGUVDUVMUWEUVNUWFUVDUV
        LCCUVDUVLUCCUMUHZCYSUVLUWJTUUPYSUVIUCUVKCUMYSUVIAUCUKUHZUCYSUVHUCAUKYSU
        VQUVHUCTYSVKUCUUAUAWFWGWHYQUWKUCTZYRYLYOUWLYPYLAAWIZWJWKVGWLYSUVKBUUAUK
        UHZCYSUVJUUABUKYSUUAWMUBZUVJUUATYSCBUGWNZUCUUAWMWOWGZWHYSCBYQCWPUBZYRYQ
        CUVSWQZVGYQBWPUBZYRYOYLUWTYPYOBUWAWQVIVGZUWDWRWLWSVNYSUWJCTZUUPYQUXBYRY
        QCUWSWTVGVNWLXAYSUVNUWFUNUUPYSUVJUUAIUWQXAVNXDXBUVAUVPLUVFDUUDUVFTZUULU
        VOUXCUUJUVMUUKUVNUXCUUIUVLCUXCUUFUVIUUHUVKUMUXCUUEUVHAUKUIUUDUVFXCWHUXC
        UUGUVJBUKULUUDUVFXCZWHWSXAUXCUUGUVJIUXDXAXDXEXFVPXOUUPUPUUBUUOUVCIUUAXG
        UUBUUOUEZYSUVBUXEYSUEZUIUIVDUVEVEZDUBZAUIUXGURZUKUHZBULUXGURZUKUHZUMUHZ
        CTZUXKITZUNZUPZUVBYSUXHUXEYSUIUAUBZUVRUEZUXHYQUXSYRYQUXRUVRYQXHYQCBUVSU
        WBUWCVMXIVGUIUUADGMOVOWGVNUXFUXQACUMUHZCTZUWFUNZUPZUXFUYBYTUWFUNZUXEUYD
        UPZYSUXEYTUWIUNUYEUXEYTUWIUUOYTUWIVJUUBYTUUOUWIUWIAUCXJXKVNUUBUWIYTVJZU
        UOUYFUUAIUWFYTXLXMVGWCYTUWFWDWEVGUXFUYAYTUWFUXFUYACAUMUHZCTZYTUXFUXTUYG
        CUXFACUXFAYLYOYPYRUXEXNWQUXFCYSYPUXEUVTVNWQXPXAUXFUWRAWPUBZUEZUYHYTUNYS
        UYJUXEYQUYJYRYLYPUYJYOYLUYIYPUWRUWMCWIXQXRVGVNCAXSWGXTYAXBYSUXQUYCUNUXE
        YSUXPUYBYSUXNUYAUXOUWFYSUXMUXTCYSUXJAUXLCUMYSUXJAUIUKUHZAYSUXIUIAUKYSUI
        WMUBZUXIUITUYLYSYBWBUIUUAWMWFWGWHYQUYKATZYRYLYOUYMYPAYFWKVGWLYSUXLUWNCY
        SUXKUUABUKYSUWOUXKUUATUWPUIUUAWMWOWGZWHYSCBYSCUVTWQUXAUWDWRWLWSXAYSUXKU
        UAIUYNXAXDXEVNYCUVAUXQLUXGDUUDUXGTZUULUXPUYOUUJUXNUUKUXOUYOUUIUXMCUYOUU
        FUXJUUHUXLUMUYOUUEUXIAUKUIUUDUXGXCWHUYOUUGUXKBUKULUUDUXGXCZWHWSXAUYOUUG
        UXKIUYPXAXDXEXFVPXOYDYEYGXKUULLDYHYIYJYK $.

      $( Example for a horizontal line ` G ` passing through two different
         points in "standard form".  (Contributed by AV, 3-Feb-2023.) $)
      line2x $p |- ( ( ( A e. RR /\ ( B e. RR /\ B =/= 0 ) /\ C e. RR )
                       /\ M e. RR )
                     -> ( G = ( X L Y ) <-> ( A = 0 /\ M = ( C / B ) ) ) ) $=
        ( c1 cr wcel cc0 wne wa w3a co wceq cv cfv cmul c2 caddc crab cmin cdiv
        a1i cop cpr cmap wf cvv 1ex 2ex pm3.2i c0ex jctl 1ne2 fprg 0red anim12i
        wss simpr 3adant3 prssi syl fssd mp3an2i feq2i sylibr reex prex eqeltri
        elmap 3eltr4g mpan wb elmapg mp1i mpbird wo opex orci opthne mpbir 0ne1
        1re olci jctil orcd prneimg 3netr4g 3jca adantl eqid rrx2linest eqeq12d
        mpsyl fveq1i 3pm3.2i fvpr1g eqtrid oveq12d eqtrdi oveq1d fvpr2g mp3an13
        rabbi 1m0e1 subidd eqtrd mp3an12i ax-1rid mul02d subid1d rrx2pyel recnd
        wral recn mullidd rrx2pxel bibi2d ralbidva addlidd ad2antlr cc 3ad2ant2
        adantr ad3antrrr eqeq1d sylan9bb eqeq2d oveq1 mulcld simp3 simpl simp2r
        line2xlem divmuld eqcomd 3bitr2d bitrdi ralrimiva impbid 3bitrd bitr3id
        eqcom ex bitrd ) AUAUBZBUAUBZBUCUDZUEZCUAUBZUFZIUAUBZUEZFJKHUGZUHATLUIZ
        UJZUKUGZBULUVIUJZUKUGZUMUGZCUHZLDUNZTKUJZTJUJZUOUGZUVLUKUGZULKUJZULJUJZ
        UOUGZUVJUKUGZUWBUVQUKUGZUVRUWAUKUGZUOUGZUMUGZUHZLDUNZUHZAUCUHZICBUPUGZU
        HZUEZUVGFUVPUVHUWJFUVPUHUVGQUQUVGJDUBZKDUBZJKUDZUFZUVHUWJUHUVFUWSUVEUVF
        UWPUWQUWRUVFTUCURZULIURZUSZUAGUTUGZJDUVFGUAUXBVAZUXBUXCUBUVFTULUSZUAUXB
        VAZUXDTVBUBZULVBUBZUEZUVFUCVBUBZUVFUEZTULUDZUXFUXGUXHVCVDVEZUVFUXJVFVGU
        XLUVFVHUQZUXIUXKUXLUFZUXEUCIUSZUAUXBTULUCIVBVBVBUAVIUXOUCUAUBZUVFUEZUXP
        UAVLUXIUXKUXRUXLUXIUXQUXKUVFUXIVJUXJUVFVMVKVNUCIUAVOVPVQVRGUXEUAUXBMVSV
        TUAGUXBWAGUXEVBMTULWBWCZWDVTROWEUVFTTURZUXAUSZUXCKDUVFUYAUXCUBZGUAUYAVA
        ZUVFUXEUAUYAVAUYCUVFUXETIUSZUAUYAUXIUVFUXGUVFUEUXLUXEUYDUYAVAUXMUVFUXGV
        CVGUXNTULTIVBVBVBUAVIVRTUAUBUVFUYDUAVLWQTIUAVOWFVQGUXEUAUYAMVSVTUAVBUBZ
        GVBUBZUEUYBUYCWGUVFUYEUYFWAUXSVEUAGUYAVBVBWHWIWJSOWEUVFUXBUYAJKUWTVBUBZ
        UXAVBUBZUEZUXTVBUBZUYHUEZUEUVFUWTUXTUDZUWTUXAUDZUEZUXAUXTUDUXAUXAUDUEZW
        KUXBUYAUDUYIUYKUYGUYHTUCWLULIWLZVEUYJUYHTTWLUYPVEVEUVFUYNUYOUVFUYMUYLUY
        MUVFUYMUXLUCIUDZWKUXLUYQVHWMTUCULIVCVFWNWOUQUYLTTUDZUCTUDZWKUYSUYRWPWRT
        UCTTVCVFWNWOWSWTUWTUXAUXTUXAVBVBVBVBXAXHRSXBXCXDUVSUWCUWGDEGHJKLMNOPUVS
        XEUWCXEUWGXEXFVPXGUWKUVOUWIWGZLDYHZUVGUWOUVOUWILDXRUVGVUAUVOUVLUCIUMUGZ
        UHZWGZLDYHZUVOUVLIUHZWGZLDYHZUWOUVGUYTVUDLDUVGUVIDUBZUEUWIVUCUVOUVGUWIT
        UVLUKUGZUCUVJUKUGZIUMUGZUHZVUIVUCUVFUWIVUMWGUVEUVFUVTVUJUWHVULUVFUVSTUV
        LUKUVFUVSTUCUOUGTUVFUVQTUVRUCUOUVFUVQTUYAUJZTTKUYASXIZUXGUXGUXLUFVUNTUH
        ZUVFUXGUXGUXLVCVCVHXJTULTIVBVBXKZWIXLUVFUVRTUXBUJZUCTJUXBRXIZUXGUXJUXLU
        FVURUCUHZUVFUXGUXJUXLVCVFVHXJTULUCIVBVBXKZWIXLXMXSXNXOUVFUWDVUKUWGIUMUV
        FUWCUCUVJUKUVFUWCIIUOUGUCUVFUWAIUWBIUOUVFUWAULUYAUJZIULKUYASXIUXHUVFUXL
        VVBIUHVDVHTULTIVBUAXPXQXLZUVFUWBULUXBUJZIULJUXBRXIUXHUVFUXLVVDIUHVDVHTU
        LUCIVBUAXPXQXLZXMUVFIIYIZXTYAXOUVFUWGIUCUOUGIUVFUWEIUWFUCUOUVFUWEITUKUG
        IUVFUWBIUVQTUKVVEUVFUVQVUNTVUOUXGUXGUVFUXLVUPVCVCUXNVUQYBXLXMIYCYAUVFUW
        FUCIUKUGUCUVFUVRUCUWAIUKUVFUVRVURUCVUSUXGUXJUVFUXLVUTVCVFUXNVVAYBXLVVCX
        MUVFIVVFYDYAXMUVFIVVFYEYAXMXGXDVUIVUJUVLVULVUBVUIUVLVUIUVLDGUVIMOYFYGZY
        JVUIVUKUCIUMVUIUVJVUIUVJDGUVIMOYKYGYDZXOXGUUAYLYMUVFVUEVUHWGUVEUVFVUDVU
        GLDUVFVUIUEZVUCVUFUVOVVIVUBIUVLUVFVUBIUHVUIUVFIVVFYNYRUUBYLYMXDUVGVUHUW
        OABCDEFGHIJKLMNOPQRSUUHUVGUWOVUHUVGUWOUEZVUGLDVVJVUIUEZUVOIUVLUHZVUFVVK
        UVOUVMCUHUWMUVLUHVVLVVKUVNUVMCVVKUVNUCUVMUMUGUVMVVKUVKUCUVMUMVVKUVKVUKU
        CUWOUVKVUKUHZUVGVUIUWLVVMUWNAUCUVJUKUUCYRYOVUIVUKUCUHVVJVVHXDYAXOVVKUVM
        VVKBUVLUVEBYPUBZUVFUWOVUIUVCUUTVVNUVDUVAVVNUVBBYIYRYQYSVUIUVLYPUBVVJVVG
        XDZUUDYNYAYTVVKCBUVLUVECYPUBUVFUWOVUIUVECUUTUVCUVDUUEYGYSUVEVVNUVFUWOVU
        IUVCUUTVVNUVDUVCBUVAUVBUUFYGYQYSVVOUVEUVBUVFUWOVUIUUTUVAUVBUVDUUGYSUUIV
        VKUWMIUVLUWOUWMIUHUVGVUIUWOIUWMUWLUWNVMUUJYOYTUUKIUVLUUQUULUUMUURUUNUUO
        UUPUUS $.
    $}

    ${
      $d M p $.  $d N p $.
      line2y.x $e |- X = { <. 1 , 0 >. , <. 2 , M >. } $.
      line2y.y $e |- Y = { <. 1 , 0 >. , <. 2 , N >. } $.
      $( Example for a vertical line ` G ` passing through two different points
         in "standard form".  (Contributed by AV, 3-Feb-2023.) $)
      line2y $p |- ( ( ( A e. RR /\ B e. RR /\ C e. RR )
                      /\ ( M e. RR /\ N e. RR /\ M =/= N ) )
                    -> ( G = ( X L Y ) <-> ( A =/= 0 /\ B = 0 /\ C = 0 ) ) ) $=
        ( cr wcel w3a wne wa co wceq c1 cv cfv cmul caddc crab cc0 a1i cop cmap
        c2 cpr wf cvv 1ex 2ex pm3.2i c0ex jctl 1ne2 fprg 0red simp2r prssd fssd
        mp3an2i feq2i sylibr reex prex eqeltri elmap 3eltr4g 3ad2ant1 wss prssi
        mpan wb elmapg mp1i mpbird 3ad2ant2 fveq1i 3pm3.2i fvpr1g eqtrid eqtr4d
        0re simp3 simp1 fvpr2g simp2 3netr4d jca adantl rrx2vlinest syl eqeq12d
        3jca ax-mp eqtri eqeq2d rabbidv wral rabbi wi line2ylem adantr ad2antlr
        oveq1 oveq2d rrx2pyel recnd mul02d cc ad3antrrr rrx2pxel mulcld addridd
        eqtrd eqeq1d wo mul0ord eqneqall com12 idd jaod impbid1 bitrd ralrimiva
        olc 3bitrd ex impbid bitr3id ) AUAUBZBUAUBZCUAUBZUCZIUAUBZJUAUBZIJUDZUC
        ZUEZFKLHUFZUGAUHMUIZUJZUKUFZBURUUMUJZUKUFZULUFZCUGZMDUMZUUNUHKUJZUGZMDU
        MZUGUUTUUNUNUGZMDUMZUGZAUNUDZBUNUGZCUNUGZUCZUUKFUUTUULUVCFUUTUGUUKRUOUU
        KKDUBZLDUBZUVAUHLUJZUGZURKUJZURLUJZUDZUEZUCZUULUVCUGUUJUVSUUFUUJUVKUVLU
        VRUUGUUHUVKUUIUUGUHUNUPZURIUPUSZUAGUQUFZKDUUGGUAUWAUTZUWAUWBUBUUGUHURUS
        ZUAUWAUTZUWCUHVAUBZURVAUBZUEZUUGUNVAUBZUUGUEZUHURUDZUWEUWFUWGVBVCVDZUUG
        UWIVEVFUWKUUGVGUOUWHUWJUWKUCZUWDUNIUSUAUWAUHURUNIVAVAVAUAVHUWMUNIUAUWMV
        IUWHUWIUUGUWKVJVKVLVMGUWDUAUWANVNVOUAGUWAVPGUWDVANUHURVQVRZVSVOSPVTWAUU
        HUUGUVLUUIUUHUVTURJUPUSZUWBLDUUHUWOUWBUBZGUAUWOUTZUUHUWDUAUWOUTUWQUUHUW
        DUNJUSZUAUWOUWHUUHUWIUUHUEUWKUWDUWRUWOUTUWLUUHUWIVEVFUWKUUHVGUOUHURUNJV
        AVAVAUAVHVMUNUAUBUUHUWRUAWBWOUNJUAWCWDVLGUWDUAUWONVNVOUAVAUBZGVAUBZUEUW
        PUWQWEUUHUWSUWTVPUWNVDUAGUWOVAVAWFWGWHTPVTWIUUJUVNUVQUUJUVAUNUVMUUJUVAU
        HUWAUJZUNUHKUWASWJZUWFUWIUWKUCZUXAUNUGZUUJUWFUWIUWKVBVEVGWKZUHURUNIVAVA
        WLZWGWMUUJUVMUHUWOUJZUNUHLUWOTWJUXCUXGUNUGUUJUXEUHURUNJVAVAWLWGWMWNUUJI
        JUVOUVPUUGUUHUUIWPUUJUVOURUWAUJZIURKUWASWJUWGUUJUUGUWKUXHIUGVCUUGUUHUUI
        WQUWKUUJVGUOZUHURUNIVAUAWRVMWMUUJUVPURUWOUJZJURLUWOTWJUWGUUJUUHUWKUXJJU
        GVCUUGUUHUUIWSUXIUHURUNJVAUAWRVMWMWTXAXFXBDEGHKLMNOPQXCXDXEUUKUVCUVEUUT
        UUKUVBUVDMDUUKUVAUNUUNUVAUNUGUUKUVAUXAUNUXBUXCUXDUXEUXFXGXHUOXIXJXIUVFU
        USUVDWEZMDXKZUUKUVJUUSUVDMDXLUUKUXLUVJUUFUXLUVJXMUUJABCDGMNPXNXOUUKUVJU
        XLUUKUVJUEZUXKMDUXMUUMDUBZUEZUUSUUOUNUUPUKUFZULUFZUNUGZUUOUNUGZUVDUVJUU
        SUXRWEUUKUXNUVJUURUXQCUNUVJUUQUXPUUOULUVHUVGUUQUXPUGUVIBUNUUPUKXQWIXRUV
        GUVHUVIWPXEXPUXOUXQUUOUNUXOUXQUUOUNULUFUUOUXOUXPUNUUOULUXNUXPUNUGUXMUXN
        UUPUXNUUPDGUUMNPXSXTYAXBXRUXOUUOUXOAUUNUUFAYBUBUUJUVJUXNUUFAUUCUUDUUEWQ
        XTYCZUXNUUNYBUBUXMUXNUUNDGUUMNPYDXTXBZYEYFYGYHUXOUXSAUNUGZUVDYIZUVDUXOA
        UUNUXTUYAYJUXOUYCUVDUXOUYBUVDUVDUVJUYBUVDXMZUUKUXNUVGUVHUYDUVIUYBUVGUVD
        UVDAUNYKYLWAXPUXOUVDYMYNUVDUYBYRYOYPYSYQYTUUAUUBYS $.
    $}
  $}

  $( Lemma for theorems about intersections of lines and circles in a real
     Euclidean space of dimension 2 .  (Contributed by AV, 2-May-2023.) $)
  itsclc0lem1 $p |- ( ( ( S e. RR /\ T e. RR /\ U e. RR )
                          /\ ( V e. RR /\ 0 <_ V ) /\ ( W e. RR /\ W =/= 0 ) )
                   -> ( ( ( S x. U ) + ( T x. ( sqrt ` V ) ) ) / W ) e. RR ) $=
    ( cr wcel w3a cc0 cle wbr wa wne cmul co csqrt cfv caddc remulcl 3adant2
    adantr simpl2 resqrtcl adantl remulcld readdcld 3adant3 simp3l redivcld
    simp3r ) AFGZBFGZCFGZHZDFGIDJKLZEFGZEIMZLZHACNOZBDPQZNOZROZEUNUOVBFGURUNUOL
    ZUSVAUNUSFGZUOUKUMVDULACSTUAVCBUTUKULUMUOUBUOUTFGUNDUCUDUEUFUGUNUOUPUQUHUNU
    OUPUQUJUI $.

  $( Lemma for theorems about intersections of lines and circles in a real
     Euclidean space of dimension 2 .  (Contributed by AV, 3-May-2023.) $)
  itsclc0lem2 $p |- ( ( ( S e. RR /\ T e. RR /\ U e. RR )
                          /\ ( V e. RR /\ 0 <_ V ) /\ ( W e. RR /\ W =/= 0 ) )
                   -> ( ( ( S x. U ) - ( T x. ( sqrt ` V ) ) ) / W ) e. RR ) $=
    ( cr wcel w3a cc0 cle wbr wa wne cmul co csqrt cfv cmin simp1 remulcld
    simp3 adantr simpl2 resqrtcl adantl resubcld 3adant3 simp3l simp3r redivcld
    ) AFGZBFGZCFGZHZDFGIDJKLZEFGZEIMZLZHACNOZBDPQZNOZROZEUNUOVBFGURUNUOLZUSVAUN
    USFGUOUNACUKULUMSUKULUMUATUBVCBUTUKULUMUOUCUOUTFGUNDUDUETUFUGUNUOUPUQUHUNUO
    UPUQUIUJ $.

  ${
    itsclc0lem3.q $e |- Q = ( ( A ^ 2 ) + ( B ^ 2 ) ) $.
    itsclc0lem3.d $e |- D = ( ( ( R ^ 2 ) x. Q ) - ( C ^ 2 ) ) $.
    $( Lemma for theorems about intersections of lines and circles in a real
       Euclidean space of dimension 2 .  (Contributed by AV, 2-May-2023.) $)
    itsclc0lem3 $p |- ( ( ( A e. RR /\ B e. RR /\ C e. RR ) /\ R e. RR )
                        -> D e. RR ) $=
      ( cr wcel w3a wa c2 cexp co cmul cmin simpr resqcld resum2sqcl remulcld
      3adant3 adantr simpl3 resubcld eqeltrid ) AIJZBIJZCIJZKZFIJZLZDFMNOZEPOZC
      MNOZQOIHULUNUOULUMEULFUJUKRSUJEIJZUKUGUHUPUIABEGTUBUCUAULCUGUHUIUKUDSUEUF
      $.
  $}

  ${
    itscnhlc0yqe.q $e |- Q = ( ( A ^ 2 ) + ( B ^ 2 ) ) $.
    ${
      itscnhlc0yqe.t $e |- T = -u ( 2 x. ( B x. C ) ) $.
      itscnhlc0yqe.u $e |- U = ( ( C ^ 2 ) - ( ( A ^ 2 ) x. ( R ^ 2 ) ) ) $.
      $( Lemma for ~ itsclc0 .  Quadratic equation for the y-coordinate of the
         intersection points of a nonhorizontal line and a circle.
         (Contributed by AV, 6-Feb-2023.) $)
      itscnhlc0yqe $p |- ( ( ( ( A e. RR /\ A =/= 0 ) /\ B e. RR /\ C e. RR )
                             /\ R e. RR+ /\ ( X e. RR /\ Y e. RR ) )
                 -> ( ( ( ( X ^ 2 ) + ( Y ^ 2 ) ) = ( R ^ 2 )
                        /\ ( ( A x. X ) + ( B x. Y ) ) = C )
                      -> ( ( Q x. ( Y ^ 2 ) ) + ( ( T x. Y ) + U ) ) = 0 ) ) $=
        ( wcel c2 co caddc wceq cmul 3ad2ant1 recnd cr cc0 wne wa w3a cexp cmin
        crp cdiv recn adantr simp2 simpr 3ad2ant3 remulcld simp3 simp11r anbi2d
        cc lineq oveq1 oveq1d eqeq1d biimpac cneg simpl resqcld resubcld adddid
        redivcld sqdivd oveq2d wb sqne0 biimpar divcan2d readdcld rpre 3ad2ant2
        syl mulcand binom2sub syl2anc 2re a1i subcan2ad addassd mulassd mulcomd
        eqtrd eqtr3d eqtr4d sqmuld adddird oveq12d subadd23d addsubassd negsubd
        comraddd eqcomd renegcld 3eqtrd subidd eqeq12d 3bitr2d 3bitr3d mulneg1d
        biimpd sylbid syl5 ) AUAMZAUBUCZUDZBUAMZCUAMZUEZEUHMZHUAMZIUAMZUDZUEZHN
        UFOZINUFOZPOZENUFOZQZAHROBIROZPOCQZUDYFHCYGUGOZAUIOZQZUDZDYCROZFIROZGPO
        ZPOZUBQZYAYHYKYFYAAYGHCXPXQAUSMZXTXMXNYRXOXKYRXLAUJZUKSSYAYGYABIXPXQXNX
        TXMXNXOULZSZXTXPXSXQXRXSUMZUNZUOZTZXTXPHUSMZXQXRUUFXSHUJUKUNXPXQCUSMZXT
        XPCXMXNXOUPZTZSZXKXLXNXOXQXTUQZUTURYLYJNUFOZYCPOZYEQZYAYQYKYFUUNYKYDUUM
        YEYKYBUULYCPHYJNUFVAVBVCVDYAUUNBNUFOZANUFOZPOZYCROZNBCROZROZIROZVEZCNUF
        OZUUPYEROZUGOZPOZPOZUBQZYQYAUUPUUMROZUVDQYINUFOZUUPYCROZPOZUVDQZUUNUVHY
        AUVIUVLUVDYAUVIUUPUULROZUVKPOUVLYAUUPUULYCXPXQUUPUSMZXTXPUUPXPAXMXNXKXO
        XKXLVFZSZVGTSYAUULYAYJYAYIAYACYGXPXQXOXTUUHSZUUDVHZXPXQXKXTUVQSZUUKVJVG
        ZTXTXPYCUSMXQXTYCXTIUUBVGTUNVIYAUVNUVJUVKPYAUVNUUPUVJUUPUIOZROUVJYAUULU
        WBUUPRYAYIAYAYIUVSTXPXQYRXTXMXNYRXOXMAUVPTSSUUKVKVLYAUVJUUPYAUVJYAYIUVS
        VGTXPXQUVOXTXMXNUVOXOXMUUPXMAUVPVGZTSSXPXQUUPUBUCZXTXMXNUWDXOXKUWDXLXKY
        RUWDXLVMYSAVNVTVOSSZVPWJVBWJVCYAUUMYEUUPYAUUMYAUULYCUWAYAIUUCVGZVQTXQXP
        YEUSMXTXQYEXQEEVRVGZTVSYAUUPXPXQUUPUAMZXTXMXNUWHXOUWCSZSZTUWEWAYAUVMUVC
        NCYGROZROZUGOZYGNUFOZPOZUVKPOZUVDQUWPUVDUGOZUVDUVDUGOZQUVHYAUVLUWPUVDYA
        UVJUWOUVKPYAUUGYGUSMUVJUWOQUUJUUECYGWBWCVBVCYAUWPUVDUVDYAUWPYAUWOUVKYAU
        WMUWNYAUVCUWLXPXQUVCUAMXTXPCUUHVGSZYANUWKNUAMYAWDWEZYACYGUVRUUDUOUOVHZY
        AYGUUDVGZVQYAUUPYCUWJUWFUOZVQTYAUVDYAUUPYEUWJXQXPYEUAMXTUWGVSUOZTZUXEWF
        YAUWQUVGUWRUBYAUWQUVCUVAUGOZUURPOZUVDUGOUURUVAUGOZUVCPOZUVDUGOZUVGYAUWP
        UXGUVDUGYAUWPUWMUWNUVKPOZPOUXGYAUWMUWNUVKYAUWMUXATYAUWNUXBTYAUVKUXCTWGY
        AUWMUXFUXKUURPYAUWLUVAUVCUGYAUWLNUUSIROZROUVAYAUWKUXLNRYACBROZIROUWKUXL
        YACBIYACUVRTXPXQBUSMXTXPBYTTZSZYAIUUCTZWHYAUXMUUSIRXPXQUXMUUSQXTXPCBUUI
        UXNWISVBWKVLYANUUSIYANUWTTYAUUSXPXQUUSUAMXTXPBCYTUUHUOSTUXPWHWLVLYAUXKU
        UOYCROZUVKPOUURYAUWNUXQUVKPYABIUXOUXPWMVBYAUUOUUPYCYAUUOYABUUAVGTZYAUUP
        YAAUVTVGTZYAYCUWFTWNWLWOWJVBYAUXGUXIUVDUGYAUXGUVCUXHYAUVCUWSTZYAUXHYAUU
        RUVAYAUUQYCXPXQUUQUAMXTXPUUOUUPXPBYTVGUWIVQSUWFUOZYAUUTIYANUUSUWTYABCUU
        AUVRUOUOZUUCUOZVHTZYAUVCUVAUURUXTYAUVAUYCTZYAUURUYATZWPWSVBYAUXJUXHUVEP
        OUURUVBPOZUVEPOUVGYAUXHUVCUVDUYDUXTUXEWQYAUXHUYGUVEPYAUYGUXHYAUURUVAUYF
        UYEWRWTVBYAUURUVBUVEUYFYAUVBYAUVAUYCXATYAUVEYAUVCUVDUWSUXDVHTWGXBXBYAUV
        DUXEXCXDXEXFYAUVHYQYAUVGYPUBYAYPUVGYAYMUURYOUVFPYADUUQYCRYADUUPUUOUXSUX
        RDUUPUUOPOQYAJWEWSVBYAYNUVBGUVEPYAYNUUTVEZIROUVBYAFUYHIRFUYHQYAKWEVBYAU
        UTIYAUUTUYBTUXPXGWJGUVEQYALWEWOWOWTVCXHXIXJXI $.

      $( Lemma for ~ itsclc0 .  Quadratic equation for the y-coordinate of the
         intersection points of a horizontal line and a circle.  (Contributed
         by AV, 25-Feb-2023.) $)
      itschlc0yqe $p |- ( ( ( ( A e. RR /\ A = 0 ) /\ B e. RR /\ C e. RR )
                             /\ R e. RR+ /\ ( X e. RR /\ Y e. RR ) )
                 -> ( ( ( ( X ^ 2 ) + ( Y ^ 2 ) ) = ( R ^ 2 )
                        /\ ( ( A x. X ) + ( B x. Y ) ) = C )
                      -> ( ( Q x. ( Y ^ 2 ) ) + ( ( T x. Y ) + U ) ) = 0 ) ) $=
        ( wcel cc0 wceq c2 cexp co caddc cmul cr wa w3a crp wi cneg cmin oveq2d
        oveq2 oveq1d negeqd oveq1 oveq12d eqcoms simp12 recnd simp3r sqcld 2cnd
        cc mulcld negcld add32r syl3anc addcld negsubd mulassd 2timesd subeq0bd
        mul32d sqvald eqtr4d eqtrd sylan9eqr simp3l mul02d eqeq1d sqmuld simp13
        3eqtrrd ex addlidd mulneg1d rpcn 3ad2ant2 subid1d 3imtr4d 3exp 3adant1r
        3imp adantld wb anbi2d eqtrid oveq1i a1i imbi12d adantl 3ad2ant1 mpbird
        sq0i ) AUAMZANOZUBZBUAMZCUAMZUCZEUDMZHUAMZIUAMZUBZUCZHPQRIPQRZSREPQRZOZ
        AHTRZBITRZSRZCOZUBZDXMTRZFITRZGSRZSRZNOZUEZXONHTRZXQSRZCOZUBZNBPQRZSRZX
        MTRZPBCTRZTRZUFZITRZCPQRZNXNTRZUGRZSRZSRZNOZUEZXLYIUUCXOXGXHXKYIUUCUEZX
        BXEXFXHXKUUEUEUEXCXBXEXFUCZXHXKUUEUUFXHXKUCZXQCOZXQPQRZYOITRZUFZYRSRZSR
        ZNOZYIUUCUUGUUHUUNUUHUUGUUMUUIPBXQTRZTRZITRZUFZUUISRZSRZNUUMUUTOCXQCXQO
        ZUULUUSUUISUVAUUKUURYRUUISUVAUUJUUQUVAYOUUPITUVAYNUUOPTCXQBTUIUHUJUKCXQ
        PQULUMUHUNUUGUUTUUIUUISRZUURSRZNUUGUUIUTMZUURUTMUVDUUTUVCOUUGXQUUGBIUUG
        BXBXEXFXHXKUOUPZUUGIUUFXHXIXJUQUPZVAZURZUUGUUQUUGUUPIUUGPUUOUUGUSZUUGBX
        QUVEUVGVAZVAUVFVAZVBUVHUUIUURUUIVCVDUUGUVCUVBUUQUGRNUUGUVBUUQUUGUUIUUIU
        VHUVHVEZUVKVFUUGUVBUUQUVLUUGUUQPUUOITRZTRPUUITRUVBUUGPUUOIUVIUVJUVFVGUU
        GUVMUUIPTUUGUVMXQXQTRUUIUUGBXQIUVEUVGUVFVJUUGXQUVGVKVLUHUUGUUIUVHVHVTVI
        VMVMVNWAUUGYHXQCUUGYHNXQSRXQUUGYGNXQSUUGHUUGHUUFXHXIXJVOUPVPUJUUGXQUVGW
        BVMVQUUGUUBUUMNUUGYMUUIUUAUULSUUGYMYKXMTRUUIUUGYLYKXMTUUGYKUUGBUVEURWBU
        JUUGBIUVEUVFVRVLUUGYQUUKYTYRSUUGYOIUUGPYNUVIUUGBCUVEUUGCXBXEXFXHXKVSUPZ
        VAVAUVFWCUUGYTYRNUGRZYRXHUUFYTUVOOXKXHYSNYRUGXHXNXHEEWDURVPUHWEUUGYRUUG
        CUVNURWFVMUMUMVQWGWHWIWJWKXGXHYFUUDWLZXKXDXEUVPXFXCUVPXBXCXTYJYEUUCXCXS
        YIXOXCXRYHCXCXPYGXQSANHTULUJVQWMXCYDUUBNXCYAYMYCUUASXCDYLXMTXCDAPQRZYKS
        RYLJXCUVQNYKSAXAZUJWNUJXCYBYQGYTSYBYQOXCFYPITKWOWPXCGYRUVQXNTRZUGRYTLXC
        UVSYSYRUGXCUVQNXNTUVRUJUHWNUMUMVQWQWRWSWSWT $.

      $( Lemma for ~ itsclc0 .  Quadratic equation for the y-coordinate of the
         intersection points of an arbitrary line and a circle.  This theorem
         holds even for degenerate lines ( ` A = B = 0 ` ).  (Contributed by
         AV, 25-Feb-2023.) $)
      itsclc0yqe $p |- ( ( ( A e. RR /\ B e. RR /\ C e. RR )
                               /\ R e. RR+ /\ ( X e. RR /\ Y e. RR ) )
                 -> ( ( ( ( X ^ 2 ) + ( Y ^ 2 ) ) = ( R ^ 2 )
                        /\ ( ( A x. X ) + ( B x. Y ) ) = C )
                      -> ( ( Q x. ( Y ^ 2 ) ) + ( ( T x. Y ) + U ) ) = 0 ) ) $=
        ( cr wcel wa co caddc wceq cmul cc0 w3a c2 cexp wi simp11 anim1i ancoms
        crp simpr12 simpr13 simpr2 simpr3 itschlc0yqe syl311anc ex itscnhlc0yqe
        wne pm2.61ine ) AMNZBMNZCMNZUAZEUHNZHMNIMNOZUAZHUBUCPIUBUCPZQPEUBUCPRAH
        SPBISPQPCRODVFSPFISPGQPQPTRUDZUDATATRZVEVGVHVEOUSVHOZUTVAVCVDVGVEVHVIVE
        USVHUSUTVAVCVDUEZUFUGUSUTVAVCVDVHUIUSUTVAVCVDVHUJVHVBVCVDUKVHVBVCVDULAB
        CDEFGHIJKLUMUNUOATUQZVEVGVKVEOUSVKOZUTVAVCVDVGVEVKVLVEUSVKVJUFUGUSUTVAV
        CVDVKUIUSUTVAVCVDVKUJVKVBVCVDUKVKVBVCVDULABCDEFGHIJKLUPUNUOUR $.

      itsclc0yqsollem1.d $e |- D = ( ( ( R ^ 2 ) x. Q ) - ( C ^ 2 ) ) $.
      $( Lemma 1 for ~ itsclc0yqsol .  (Contributed by AV, 6-Feb-2023.) $)
      itsclc0yqsollem1 $p |- ( ( ( A e. CC /\ B e. CC /\ C e. CC ) /\ R e. CC )
                           -> ( ( T ^ 2 ) - ( 4 x. ( Q x. U ) ) )
                              = ( ( 4 x. ( A ^ 2 ) ) x. D ) ) $=
        ( cc c2 cexp co c4 cmul cmin mulcld wcel wa caddc cneg oveq1i wceq 2cnd
        w3a simpl2 simpl3 sqneg syl sqmuld sq2 a1i oveq12d 3eqtrd eqtrid simpl1
        oveq12i sqcld addcld simpr subdid adddird mul12d oveq2d assraddsubd 4cn
        addcomd simp1 adantr eqeltrid subcld mulassd subsub4d cc0 subidd oveq1d
        subsub2d addlidd eqtr3d adddid eqcomd eqtr4d mulcomd eqtrd 3eqtr2rd
        0cnd ) AMUAZBMUAZCMUAZUHZFMUAZUBZGNOPZQEHRPZRPZSPQBNOPZCNOPZRPZRPZQXAAN
        OPZWTRPZXCXCFNOPZRPZRPZXCWSXERPZRPZUCPZSPZUCPZRPZSPZQXCRPDRPZWOWPXBWRXM
        SWOWPNBCRPZRPZUDZNOPZXBGXRNOJUEWOXSXQNOPZNNOPZXPNOPZRPXBWOXQMUAXSXTUFWO
        NXPWOUGZWOBCWJWKWLWNUIZWJWKWLWNUJZTZTXQUKULWONXPYCYFUMWOYAQYBXARYAQUFWO
        UNUOWOBCYDYEUMUPUQURWOWQXLQRWOWQXCWSUCPZWTXFSPZRPZXLEYGHYHRIKUTWOYIYGWT
        RPZYGXFRPZSPXDXAUCPZXGWSXFRPZUCPZSPZXLWOYGWTXFWOXCWSWOAWJWKWLWNUSVAZWOB
        YDVAZVBZWOCYEVAZWOXCXEYPWOFWMWNVCVAZTZVDWOYJYLYKYNSWOXCWSWTYPYQYSVEWOXC
        WSXFYPYQUUAVEUPWOYOXAXDXJWOWSWTYQYSTZWOXCWTYPYSTZWOXGXIWOXCXFYPUUATWOXC
        XHYPWOWSXEYQYTTZTVBZWOYLXAXDUCPYNXJSWOXDXAUUCUUBVJWOYMXIXGUCWOWSXCXEYQY
        PYTVFVGUPVHUQURVGUPWOXOQXCDRPZRPQXAXLSPZRPXNWOQXCDQMUAWOVIUOZWMXCMUAWNW
        MAWJWKWLVKVAVLWODXEERPZWTSPZMLWOUUIWTWOXEEYTWOEYGMIYRVMTYSVNVMVOWOUUGUU
        FQRWOUUGXJXDSPZXCYGXERPZWTSPZRPZUUFWOXAXASPZXKSPZUUGUUKWOXAXAXKUUBUUBWO
        XDXJUUCUUEVNZVPWOUUPVQXKSPVQUUKUCPUUKWOUUOVQXKSWOXAUUBVRVSWOVQXDXJWOWIU
        UCUUEVTWOUUKWOXJXDUUEUUCVNWAUQWBWOUUKXCUULRPZXDSPUUNWOXJUURXDSWOXCXFXHU
        CPZRPXJUURWOXCXFXHYPUUAUUDWCWOUUSUULXCRWOUULUUSWOXCWSXEYPYQYTVEWDVGWBVS
        WOXCUULWTYPWOYGXEYRYTTYSVDWEWOUUMDXCRWODUUMWODUUJUUMLWOUUIUULWTSWOUUIXE
        YGRPUULWOEYGXEREYGUFWOIUOVGWOXEYGYTYRWFWGVSURWDVGUQVGWOQXAXLUUHUUBWOXAX
        KUUBUUQVBVDWHWG $.

      $( Lemma 2 for ~ itsclc0yqsol .  (Contributed by AV, 6-Feb-2023.) $)
      itsclc0yqsollem2 $p |- ( ( ( A e. RR /\ B e. RR /\ C e. RR )
                             /\ R e. RR /\ 0 <_ D )
                           -> ( sqrt ` ( ( T ^ 2 ) - ( 4 x. ( Q x. U ) ) ) )
                              = ( ( 2 x. ( abs ` A ) ) x. ( sqrt ` D ) ) ) $=
        ( cr wcel c2 co c4 cmul csqrt 3ad2ant1 w3a cc0 cle wbr cexp cmin cfv cc
        cabs wa wceq recn 3anim123i anim12i 3adant3 itsclc0yqsollem1 syl fveq2d
        4re a1i simp1 resqcld remulcld 0re 4pos ltleii mulge0d simp2 resum2sqcl
        sqge0d simp3 resubcld eqeltrid sqrtmuld pm3.2i resqcl sqge0 sqrt4 absre
        sqrtmul syl12anc eqcomd oveq12d eqtrd oveq1d 3eqtrd ) AMNZBMNZCMNZUAZFM
        NZUBDUCUDZUAZGOUEPQEHRPRPUFPZSUGQAOUEPZRPZDRPZSUGWPSUGZDSUGZRPOAUIUGZRP
        ZWSRPWMWNWQSWMAUHNZBUHNZCUHNZUAZFUHNZUJZWNWQUKWJWKXGWLWJXEWKXFWGXBWHXCW
        IXDAULBULCULUMFULUNUOABCDEFGHIJKLUPUQURWMWPDWMQWOQMNZWMUSUTZWJWKWOMNZWL
        WJAWGWHWIVAZVBTZVCWMQWOXIXLUBQUCUDZWMUBQVDUSVEVFZUTWJWKUBWOUCUDZWLWJAXK
        VJTVGWMDFOUEPZERPZCOUEPZUFPMLWMXQXRWMXPEWMFWJWKWLVHVBWJWKEMNZWLWGWHXSWI
        ABEIVIUOTVCWJWKXRMNWLWJCWGWHWIVKVBTVLVMWJWKWLVKVNWMWRXAWSRWMWRQSUGZWOSU
        GZRPZXAWJWKWRYBUKZWLWGWHYCWIWGXHXMUJZXJXOYCYDWGXHXMUSXNVOUTAVPAVQQWOVTW
        ATTWMXTOYAWTRXTOUKWMVRUTWJWKYAWTUKZWLWGWHYEWIWGWTYAAVSWBTTWCWDWEWF $.
    $}

    itsclc0yqsol.d $e |- D = ( ( ( R ^ 2 ) x. Q ) - ( C ^ 2 ) ) $.
    $( Lemma for ~ itsclc0 .  Solutions of the quadratic equations for the
       y-coordinate of the intersection points of a (nondegenerate) line and a
       circle.  (Contributed by AV, 7-Feb-2023.) $)
    itsclc0yqsol $p |- ( ( ( ( A e. RR /\ B e. RR /\ C e. RR )
                                 /\ ( A =/= 0 \/ B =/= 0 ) )
                          /\ ( R e. RR+ /\ 0 <_ D ) /\ ( X e. RR /\ Y e. RR ) )
                         -> ( ( ( ( X ^ 2 ) + ( Y ^ 2 ) ) = ( R ^ 2 )
                                /\ ( ( A x. X ) + ( B x. Y ) ) = C )
               -> ( Y = ( ( ( B x. C ) - ( A x. ( sqrt ` D ) ) ) / Q )
                 \/ Y = ( ( ( B x. C ) + ( A x. ( sqrt ` D ) ) ) / Q ) ) ) ) $=
      ( wcel cc0 c2 co caddc wceq cmul cmin cdiv 3ad2ant1 cr w3a wne wo crp cle
      wa wbr cexp cneg csqrt cfv wi eqid itsclc0yqe 3adant1r 3adant2r c4 3simpa
      cabs adantr resum2sqcl syl recnd simpr1 simpl simpr2 resum2sqgt0 syl21anc
      clt ex simp1 sqcld simp2 addcomd adantl eqtrid breqtrrd jaoi gt0ne0d 2cnd
      impcom recn 3ad2ant2 3ad2ant3 mulcld negcld rpcnd subcld eqidd quad rpred
      abscld resqcld remulcld simp1l3 resubcld eqeltrid sqrtcld mulassd negnegd
      oveq2d simp2r itsclc0yqsollem2 syl3anc oveq12d adddid 3eqtr4d oveq1d 2ne0
      cc addcld divcan5d eqtrd eqeq2d subdid orbi12d bitrd absid pm1.4 biimtrdi
      a1i wn subnegd mulneg1d simp1d id 0red ltnled ltle sylbird absnidd negeqd
      mpdan eqtr3d negsubd biimpd pm2.61ian sylbid syld ) AUAKZBUAKZCUAKZUBZALU
      CZBLUCZUDZUGZFUEKZLDUFUHZUGZGUAKZHUAKZUGZUBZGMUINHMUINZONFMUINZPAGQNBHQNO
      NCPUGZEUUPQNMBCQNZQNZUJZHQNCMUINZAMUINZUUQQNZRNZONONLPZHUUSADUKULZQNZRNZE
      SNZPZHUUSUVHONZESNZPZUDZUUHUUIUUNUURUVFUMZUUJUUDUUIUUNUVPUUGABCEFUVAUVEGH
      IUVAUNZUVEUNZUOUPUQUUOUVFHUUSAUTULZUVGQNZONZESNZPZHUUSUVTRNZESNZPZUDZUVOU
      UOUVFHUVAUJZUVAMUINUREUVEQNQNRNZUKULZONZMEQNZSNZPZHUWHUWJRNZUWLSNZPZUDUWG
      UUOEUVAUVEUWIHUUOEUUHUUKEUAKZUUNUUHUUAUUBUGZUWRUUDUWSUUGUUAUUBUUCUSVAABEI
      VBVCTZVDZUUHUUKELUCUUNUUHEUUGUUDLEVJUHZUUEUUDUXBUMUUFUUEUUDUXBUUEUUDUGUUA
      UUEUUBUXBUUEUUAUUBUUCVEUUEUUDVFUUEUUAUUBUUCVGABEIVHVIVKUUFUUDUXBUUFUUDUGZ
      LBMUINZUVCONZEVJUXCUUBUUFUUALUXEVJUHUUFUUAUUBUUCVGUUFUUDVFUUFUUAUUBUUCVEB
      AUXEUXEUNVHVIUXCEUVCUXDONZUXEIUUDUXFUXEPUUFUUDUVCUXDUUDAUUDAUUAUUBUUCVLVD
      VMUUDBUUDBUUAUUBUUCVNVDVMVOVPVQVRVKVSWBVTTZUUOUUTUUOMUUSUUOWAZUUOBCUUHUUK
      BXKKZUUNUUDUXIUUGUUBUUAUXIUUCBWCWDVATUUHUUKCXKKZUUNUUDUXJUUGUUCUUAUXJUUBC
      WCWEVATZWFZWFZWGUUOUVBUVDUUOCUXKVMUUOUVCUUQUUOAUUHUUKAXKKZUUNUUDUXNUUGUUA
      UUBUXNUUCAWCZTVATZVMUUOFUUKUUHFXKKUUNUUKFUUIUUJVFZWHWDVMWFWIUUNUUHHXKKZUU
      KUUMUXRUULHWCVPWEUUOUWIWJWKUUOUWNUWCUWQUWFUUOUWMUWBHUUOUWMMUWAQNZUWLSNUWB
      UUOUWKUXSUWLSUUOUUTMUVSQNUVGQNZONUUTMUVTQNZONUWKUXSUUOUXTUYAUUTOUUOMUVSUV
      GUXHUUHUUKUVSXKKZUUNUUDUYBUUGUUAUUBUYBUUCUUAUVSUUAAUXOWMVDTVATZUUODUUODUU
      ODUUQEQNZUVBRNUAJUUOUYDUVBUUOUUQEUUOFUUKUUHFUAKZUUNUUKFUXQWLWDZWNUWTWOUUO
      CUUAUUBUUCUUGUUKUUNWPWNWQWRVDWSZWTZXBUUOUWHUUTUWJUXTOUUOUUTUXMXAZUUOUUDUY
      EUUJUWJUXTPUUHUUKUUDUUNUUDUUGVFTZUYFUUHUUIUUJUUNXCABCDEFUVAUVEIUVQUVRJXDX
      EZXFUUOMUUSUVTUXHUXLUUOUVSUVGUYCUYGWFZXGXHXIUUOUWAEMUUOUUSUVTUXLUYLXLUXAU
      XHUXGMLUCUUOXJYBZXMXNXOUUOUWPUWEHUUOUWPMUWDQNZUWLSNUWEUUOUWOUYNUWLSUUOUUT
      UXTRNUUTUYARNUWOUYNUUOUXTUYAUUTRUYHXBUUOUWHUUTUWJUXTRUYIUYKXFUUOMUUSUVTUX
      HUXLUYLXPXHXIUUOUWDEMUUOUUSUVTUXLUYLWIUXAUXHUXGUYMXMXNXOXQXRLAUFUHZUUOUWG
      UVOUMUYOUUOUGZUWGUVNUVKUDUVOUYPUWCUVNUWFUVKUYPUWBUVMHUYPUWAUVLESUYPUVTUVH
      UUSOUYPUVSAUVGQUUOUYOUVSAPZUUHUUKUYOUYQUMZUUNUUDUYRUUGUUAUUBUYRUUCUUAUYOU
      YQAXSVKTVATWBXIZXBXIXOUYPUWEUVJHUYPUWDUVIESUYPUVTUVHUUSRUYSXBXIXOXQUVNUVK
      XTYAUYOYCZUUOUGZUWGUVOVUAUWCUVKUWFUVNVUAUWBUVJHVUAUWAUVIESVUAUUSUVTUJZRNU
      WAUVIVUAUUSUVTUUOUUSXKKUYTUXLVPZUUOUVTXKKUYTUYLVPZYDVUAVUBUVHUUSRVUAUVSUJ
      ZUVGQNVUBUVHVUAUVSUVGUUOUYBUYTUYCVPUUOUVGXKKUYTUYGVPYEVUAVUEAUVGQVUAVUEAU
      JZUJAVUAUVSVUFVUAAUUOUUAUYTUUOUUAUUBUUCUYJYFVPUUOUYTALUFUHZUUHUUKUYTVUGUM
      ZUUNUUDVUHUUGUUAUUBVUHUUCUUAUYTALVJUHZVUGUUAALUUAYGUUAYHZYIUUALUAKVUIVUGU
      MVUJALYJYNYKTVATWBYLYMVUAAUUOUXNUYTUXPVPXAXNXIYOZXBYOXIXOVUAUWEUVMHVUAUWD
      UVLESVUAUUSVUBONUWDUVLVUAUUSUVTVUCVUDYPVUAVUBUVHUUSOVUKXBYOXIXOXQYQYRYSYT
      $.

    $( Lemma for ~ itsclc0 .  Solutions of the quadratic equations for the
       coordinates of the intersection points of a nonhorizontal line and a
       circle.  (Contributed by AV, 8-Feb-2023.) $)
    itscnhlc0xyqsol $p |- ( ( ( ( A e. RR /\ A =/= 0 ) /\ B e. RR /\ C e. RR )
                          /\ ( R e. RR+ /\ 0 <_ D ) /\ ( X e. RR /\ Y e. RR ) )
                         -> ( ( ( ( X ^ 2 ) + ( Y ^ 2 ) ) = ( R ^ 2 )
                                /\ ( ( A x. X ) + ( B x. Y ) ) = C )
           -> ( ( X = ( ( ( A x. C ) + ( B x. ( sqrt ` D ) ) ) / Q )
               /\ Y = ( ( ( B x. C ) - ( A x. ( sqrt ` D ) ) ) / Q ) )
             \/ ( X = ( ( ( A x. C ) - ( B x. ( sqrt ` D ) ) ) / Q )
               /\ Y = ( ( ( B x. C ) + ( A x. ( sqrt ` D ) ) ) / Q ) ) ) ) ) $=
      ( wcel wa co caddc wceq cmul cdiv cmin recnd mulcld cr cc0 wne w3a crp c2
      cle wbr cexp csqrt cfv wo wi simpl 3anim1i 3ad2ant1 orcd jca itsclc0yqsol
      simpr syl oveq2 oveq2d eqeq1d simp12 simp13 simp11l adantr adantl resqcld
      imp rpre simp1l simp2 resum2sqcl syl2anc remulcld simpl3 resubcld 3adant3
      eqeltrid sqrtcld subcld clt resum2sqgt0 gt0ne0d divassd eqcomd divsubdird
      divcan3d eqeq12d divcld simp3l subadd2d eqcom a1i simp11r divmul2d eqeq2d
      divdiv1d 3bitr3d bitrd sylan9bbr oveq1i sqcld simp3 adddird eqtrid subdid
      mulassd recn sqvald 3ad2ant2 oveq1d eqtr3d mul12d oveq12d addcomd pnncand
      wb cc eqtrd 3eqtrd mulcomd adddid addcld simpl1r divcan5d biimpd ex com23
      sylbid adantld ancrd pnpcand orim12d mpd ) AUAKZAUBUCZLZBUAKZCUAKZUDZFUEK
      ZUBDUGUHZLZGUAKZHUAKZLZUDZGUFUIMHUFUIMNMFUFUIMZOZAGPMZBHPMZNMZCOZLZGACPMZ
      BDUJUKZPMZNMZEQMZOZHBCPMZAUUSPMZRMZEQMZOZLZGUURUUTRMZEQMZOZHUVDUVENMZEQMZ
      OZLZULZUUJUUQLZUVHUVOULZUVQUUJUUQUVSUUJYRUUAUUBUDZYSBUBUCZULZLZUUFUUIUDUU
      QUVSUMUUCUWCUUFUUIUUCUVTUWBYTYRUUAUUBYRYSUNUOUUCYSUWAYTUUAYSUUBYRYSUTUPUQ
      URUOABCDEFGHIJUSVAVKUVRUVHUVIUVOUVPUVRUVHUVCUUJUUQUVHUVCUMZUUJUUPUWDUULUU
      JUVHUUPUVCUUJUVHUUPUVCUMUUJUVHLUUPGECPMZBUVFPMZRMZEAPMZQMZOZUVCUVHUUPUUMB
      UVGPMZNMZCOZUUJUWJUVHUUOUWLCUVHUUNUWKUUMNHUVGBPVBVCVDUUJUWMUUMUWFEQMZNMZU
      WEEQMZOZUWJUUJUWLUWOCUWPUUJUWKUWNUUMNUUJUWNUWKUUJBUVFEUUJBYTUUAUUBUUFUUIV
      ESZUUJUVDUVEUUJBCUWRUUJCYTUUAUUBUUFUUIVFSZTZUUJAUUSUUJAYRYSUUAUUBUUFUUIVG
      SZUUJDUUJDUUCUUFDUAKUUIUUCUUFLZDUUKEPMZCUFUIMZRMUAJUXBUXCUXDUXBUUKEUXBFUU
      FFUAKZUUCUUDUXEUUEFVLVHVIVJUUCEUAKZUUFUUCYRUUAUXFYRYSUUAUUBVMZYTUUAUUBVNZ
      ABEIVOVPZVHZVQUXBCYTUUAUUBUUFVRZVJVSWAZVTSWBTZWCZUUJEUUCUUFUXFUUIUXIUPSZU
      UCUUFEUBUCZUUIUUCEYTUUAUBEWDUHUUBABEIWEVTWFZUPZWGWHVCUUJUWPCUUJCEUWSUXOUX
      RWJWHZWKUUJUWPUWNRMZUUMOUWGEQMZUUMOZUWQUWJUUJUXTUYAUUMUUJUYAUXTUUJUWEUWFE
      UUJECUXOUWSTZUUJBUVFUWRUXNTZUXOUXRWIWHVDUUJUWPUWNUUMUUJUWEEUYCUXOUXRWLZUU
      JUWFEUYDUXOUXRWLUUJAGUXAUUJGUUCUUFUUGUUHWMSZTZWNUUJUYAAQMZGOZGUYHOZUYBUWJ
      UYIUYJXTUUJUYHGWOWPUUJUYAGAUUJUWGEUUJUWEUWFUYCUYDWCZUXOUXRWLUYFUXAYRYSUUA
      UUBUUFUUIWQZWRUUJUYHUWIGUUJUWGEAUYKUXOUXAUXRUYLWTWSXAXAXBXCUUJUWJUVCUMZUV
      HUUCUUFUYMUUIUXBUWJUVCUXBUWIUVBGUXBUWIAUFUIMZCPMZAUUTPMZNMZUWHQMAUURPMZUY
      PNMZAEPMZQMZUVBUXBUWGUYQUWHQUXBUWGUYOBUFUIMZCPMZNMZVUCUYPRMZRMVUCUYONMZVU
      ERMUYQUXBUWEVUDUWFVUERUUCUWEVUDOUUFUUCUWEUYNVUBNMZCPMVUDEVUGCPIXDUUCUYNVU
      BCUUCAUUCAUXGSZXEUUCBUUCBUXHSZXEUUCCYTUUAUUBXFSZXGXHVHZUXBUWFBUVDPMZBUVEP
      MZRMVUEUXBBUVDUVEUUCBYAKUUFVUIVHZUXBBCVUNUXBCUXKSZTZUXBAUUSUUCAYAKUUFVUHV
      HZUXBDUXBDUXLSWBZTZXIUXBVULVUCVUMUYPRUUCVULVUCOUUFUUCBBPMZCPMVULVUCUUCBBC
      VUIVUIVUJXJUUCVUTVUBCPUUCVUBVUTUUAYTVUBVUTOUUBUUABBXKXLXMWHXNXOVHZUXBBAUU
      SVUNVUQVURXPZXQYBXQUXBVUDVUFVUERUXBUYOVUCUXBUYNCUXBAVUQXEVUOTZUXBVUBCUXBB
      VUNXEVUOTZXRZXNUXBVUCUYOUYPVVDVVCUXBAUUTVUQUXBBUUSVUNVURTZTZXSYCXNUXBUYQU
      YSUWHUYTQUXBUYOUYRUYPNUUCUYOUYROUUFUUCUYOAAPMZCPMUYRUUCUYNVVHCPUUCAVUHXLX
      NUUCAACVUHVUHVUJXJYBVHZXNUXBEAUXBEUXJSZVUQYDZXQUXBVUAAUVAPMZUYTQMUVBUXBUY
      SVVLUYTQUXBVVLUYSUXBAUURUUTVUQUXBACVUQVUOTZVVFYEWHXNUXBUVAEAUXBUURUUTVVMV
      VFYFVVJVUQUUCUXPUUFUXQVHZYRYSUUAUUBUUFYGZYHYBYCWSYIVTVHYLYJYKYMVKYNUVRUVO
      UVLUUJUUQUVOUVLUMZUUJUUPVVPUULUUJUVOUUPUVLUUJUVOUUPUVLUMUUJUVOLUUPGUWEBUV
      MPMZRMZUWHQMZOZUVLUVOUUPUUMBUVNPMZNMZCOZUUJVVTUVOUUOVWBCUVOUUNVWAUUMNHUVN
      BPVBVCVDUUJVWCUUMVVQEQMZNMZUWPOZVVTUUJVWBVWECUWPUUJVWAVWDUUMNUUJVWDVWAUUJ
      BUVMEUWRUUJUVDUVEUWTUXMYFZUXOUXRWGWHVCUXSWKUUJUWPVWDRMZUUMOVVREQMZUUMOZVW
      FVVTUUJVWHVWIUUMUUJVWIVWHUUJUWEVVQEUYCUUJBUVMUWRVWGTZUXOUXRWIWHVDUUJUWPVW
      DUUMUYEUUJVVQEVWKUXOUXRWLUYGWNUUJVWIAQMZGOZGVWLOZVWJVVTVWMVWNXTUUJVWLGWOW
      PUUJVWIGAUUJVVREUUJUWEVVQUYCVWKWCZUXOUXRWLUYFUXAUYLWRUUJVWLVVSGUUJVVREAVW
      OUXOUXAUXRUYLWTWSXAXAXBXCUUJVVTUVLUMZUVOUUCUUFVWPUUIUXBVVTUVLUXBVVSUVKGUX
      BVVSUYOUYPRMZUWHQMUYRUYPRMZUYTQMZUVKUXBVVRVWQUWHQUXBVVRVUDVUCUYPNMZRMVUFV
      WTRMVWQUXBUWEVUDVVQVWTRVUKUXBVVQVULVUMNMVWTUXBBUVDUVEVUNVUPVUSYEUXBVULVUC
      VUMUYPNVVAVVBXQYBXQUXBVUDVUFVWTRVVEXNUXBVUCUYOUYPVVDVVCVVGYOYCXNUXBVWQVWR
      UWHUYTQUXBUYOUYRUYPRVVIXNVVKXQUXBVWSAUVJPMZUYTQMUVKUXBVWRVXAUYTQUXBVXAVWR
      UXBAUURUUTVUQVVMVVFXIWHXNUXBUVJEAUXBUURUUTVVMVVFWCVVJVUQVVNVVOYHYBYCWSYIV
      TVHYLYJYKYMVKYNYPYQYJ $.

    $( Lemma for ~ itsclc0 .  Solutions of the quadratic equations for the
       coordinates of the intersection points of a horizontal line and a
       circle.  (Contributed by AV, 25-Feb-2023.) $)
    itschlc0xyqsol1 $p |- ( ( ( ( A e. RR /\ B e. RR /\ C e. RR )
                             /\ ( A = 0 /\ B =/= 0 ) )
                          /\ ( R e. RR+ /\ 0 <_ D ) /\ ( X e. RR /\ Y e. RR ) )
                         -> ( ( ( ( X ^ 2 ) + ( Y ^ 2 ) ) = ( R ^ 2 )
                                /\ ( ( A x. X ) + ( B x. Y ) ) = C )
                -> ( Y = ( C / B ) /\ ( X = -u ( ( sqrt ` D ) / B )
                                        \/ X = ( ( sqrt ` D ) / B ) ) ) ) ) $=
      ( wcel cc0 wceq wa c2 co cmul cdiv adantr cc cr w3a wne crp cle wbr caddc
      cexp csqrt cfv cneg wo cmin animorr anim2i itsclc0yqsol syl3an1 imp oveq1
      adantl rpcn sqcld resum2sqcl recnd 3adant3 mulcld simpll3 subcld eqeltrid
      wi sqrtcld mul02d eqtrd oveq2d simpll2 subid1d sq0i oveq1d addlidd eqtrid
      recn sqvald 3ad2ant2 oveq12d simplrr divcan5d eqeq2d biimpd addridd simp2
      simpl3 simpr jaod eqeq1d simp1rr divcld simp3l subadd2d wb sqdivd resqcld
      sqgt0d elrpd subdivcomb1 syl3anc eqtr4d eqcomd oveq1i eqeq1i eqcom sqrtth
      rpcnne0d mulcomd syl jca sqeqor orcom a1i 3bitrd biimtrrid sylbid sylbird
      biimtrid com12 biimtrdi com13 adantrd ancld syld mpd ex ) AUAKZBUAKZCUAKZ
      UBZALMZBLUCZNZNZFUDKZLDUEUFZNZGUAKZHUAKZNZUBZGOUHPZHOUHPZUGPZFOUHPZMZAGQP
      BHQPUGPCMZNZHCBRPZMZGDUIUJZBRPZUKMZGUUQMZULZNZUUFUUMNZHBCQPZAUUPQPZUMPZER
      PZMZHUVCUVDUGPZERPZMZULZUVAUUFUUMUVKYSYOALUCZYQULZNUUBUUEUUMUVKVJYRUVMYOY
      PYQUVLUNUOABCDEFGHIJUPUQURUVBUVKUUOUVAUUFUVKUUOVJZUUMYSUUBUVNUUEYSUUBNZUV
      GUUOUVJUVOUVGUUOUVOUVFUUNHUVOUVFUVCBBQPZRPZUUNUVOUVEUVCEUVPRUVOUVEUVCLUMP
      UVCUVOUVDLUVCUMUVOUVDLUUPQPZLYSUVDUVRMZUUBYRUVSYOYPUVSYQALUUPQUSSUTSUVOUU
      PUVODUVODUUJEQPZCOUHPZUMPZTJUVOUVTUWAUVOUUJEUVOFUUBFTKZYSYTUWCUUAFVASUTVB
      ZYSETKZUUBYOUWEYRYLYMUWEYNYLYMNEABEIVCVDVESSVFUVOCUVOCYLYMYNYRUUBVGVDZVBZ
      VHVIZVKZVLVMZVNUVOUVCUVOBCUVOBYLYMYNYRUUBVOZVDZUWFVFZVPVMUVOEBOUHPZUVPUVO
      EAOUHPZUWNUGPZUWNIUVOUWPLUWNUGPUWNUVOUWOLUWNUGYSUWOLMZUUBYRUWQYOYPUWQYQAV
      QSUTSVRUVOUWNUVOBUWLVBZVSVMVTZYSUWNUVPMZUUBYOUWTYRYMYLUWTYNYMBBWAWBWCSSVM
      WDUVOCBBUWFUWLUWLYOYPYQUUBWEZUXAWFVMWGWHUVOUVJUUOUVOUVIUUNHUVOUVIUVCUWNRP
      ZUUNUVOUVHUVCEUWNRUVOUVHUVCLUGPUVCUVOUVDLUVCUGUWJVNUVOUVCUWMWIVMUWSWDYSUX
      BUUNMUUBYSUXBUVQUUNYSUWNUVPUVCRYOUWTYRYOBYOBYLYMYNWJVDZWBSVNYSCBBYSCYLYMY
      NYRWKVDYOBTKZYRUXCSZUXEYRYQYOYPYQWLUTZUXFWFVMSVMWGWHWMVESUVBUUOUUTUUFUUMU
      UOUUTVJZUUFUUKUXGUULUUOUUKUUFUUTUUOUUKUUGUUNOUHPZUGPZUUJMZUUFUUTVJUUOUUIU
      XIUUJUUOUUHUXHUUGUGHUUNOUHUSVNWNUUFUXJUUTUUFUXJUUJUXHUMPZUUGMZUUTUUFUUJUX
      HUUGYSUUBUUJTKZUUEUWDVEZUUFUUNUUFCBYSUUBCTKUUEUWFVEYSUUBUXDUUEUWLVEZYPYQY
      OUUBUUEWOZWPVBUUFGUUFGYSUUBUUCUUDWQVDZVBWRUUFUXLUWNUUJQPZUWAUMPZUWNRPZUUG
      MZUUTYSUUBUXLUYAWSUUEUVOUXKUXTUUGUVOUXKUUJUWAUWNRPZUMPZUXTUVOUXHUYBUUJUMU
      VOCBUWFUWLUXAWTVNUVOUXMUWATKUWNTKZUWNLUCNUXTUYCMUWDUWGUVOUWNUVOUWNUVOBUWK
      XAUVOBUWKUXAXBXCXLUUJUWAUWNXDXEXFWNVEUUFUYAUWBUWNRPZUUGMZUUTUUFUXTUYEUUGU
      UFUXSUWBUWNRUUFUXRUVTUWAUMUUFUXRUUJUWNQPUVTUUFUWNUUJYSUUBUYDUUEUWRVEUXNXM
      UUFUWNEUUJQUUFEUWNYSUUBEUWNMUUEUWSVEXGVNVMVRVRWNUYFDUWNRPZUUGMZUUFUUTUYGU
      YEUUGDUWBUWNRJXHXIUYHUUGUYGMZUUFUUTUYGUUGXJUUFUYIUUTUUFUYIUUGUUQOUHPZMZUU
      SUURULZUUTUUFUYGUYJUUGUUFUYGUUPOUHPZUWNRPUYJUUFDUYMUWNRUUFDTKZDUYMMYSUUBU
      YNUUEUWHVEUYNUYMDDXKXGXNVRUUFUUPBYSUUBUUPTKUUEUWIVEZUXOUXPWTXFWGUUFGTKZUU
      QTKZNUYKUYLWSUUFUYPUYQUXQUUFUUPBUYOUXOUXPWPXOGUUQXPXNUYLUUTWSUUFUUSUURXQX
      RXSWHYCXTYAYAYBYDYEYFYGURYHYIYJYK $.

    $( Lemma for ~ itsclc0 .  Solutions of the quadratic equations for the
       coordinates of the intersection points of a horizontal line and a
       circle.  (Contributed by AV, 8-Feb-2023.) $)
    itschlc0xyqsol $p |- ( ( ( ( A e. RR /\ B e. RR /\ C e. RR )
                             /\ ( A = 0 /\ B =/= 0 ) )
                          /\ ( R e. RR+ /\ 0 <_ D ) /\ ( X e. RR /\ Y e. RR ) )
                         -> ( ( ( ( X ^ 2 ) + ( Y ^ 2 ) ) = ( R ^ 2 )
                                /\ ( ( A x. X ) + ( B x. Y ) ) = C )
           -> ( ( X = ( ( ( A x. C ) + ( B x. ( sqrt ` D ) ) ) / Q )
               /\ Y = ( ( ( B x. C ) - ( A x. ( sqrt ` D ) ) ) / Q ) )
             \/ ( X = ( ( ( A x. C ) - ( B x. ( sqrt ` D ) ) ) / Q )
               /\ Y = ( ( ( B x. C ) + ( A x. ( sqrt ` D ) ) ) / Q ) ) ) ) ) $=
      ( wcel cc0 wceq wa co caddc cmul cdiv adantr eqtrd cr w3a wne crp cle wbr
      c2 cexp csqrt cfv cneg wo cmin itschlc0xyqsol1 orcom oveq1 ad2antrl recnd
      simpll3 mul02d oveq1d simpll2 rpre adantl sqcld resum2sqcl 3adant3 mulcld
      subcld eqeltrid sqrtcld addlidd sq0i simp2 sqvald eqtrid simplrr divcan5d
      oveq2d eqcomd eqeq2d biimpd subid1d oveq12d eqtr2d biimpa jctird mulneg2d
      cc simp1rr negcld df-neg eqtr4di divnegd 3eqtr4d 3ad2ant1 simp1l3 simp1l2
      3ad2ant2 addridd orim12d biimtrid expimpd syld ) AUAKZBUAKZCUAKZUBZALMZBL
      UCZNZNZFUDKZLDUEUFZNZGUAKHUAKNZUBZGUGUHOHUGUHOPOFUGUHOZMAGQOBHQOPOCMNHCBR
      OZMZGDUIUJZBROZUKZMZGYBMZULZNGACQOZBYAQOZPOZEROZMZHBCQOZAYAQOZUMOZEROZMZN
      ZGYGYHUMOZEROZMZHYLYMPOZEROZMZNZULZABCDEFGHIJUNXQXTYFUUEYFYEYDULXQXTNZUUE
      YDYEUOUUFYEYQYDUUDUUFYEYKYPUUFYEYKUUFYBYJGUUFYJYBXQYJYBMZXTXLXOUUGXPXLXON
      ZYJYHEROZYBUUHYIYHERUUHYILYHPOYHUUHYGLYHPUUHYGLCQOZLXLYGUUJMZXOXIUUKXHXJA
      LCQUPUQSUUHCUUHCXEXFXGXKXOUSURZUTTZVAUUHYHUUHBYAUUHBXEXFXGXKXOVBURZUUHDUU
      HDXREQOZCUGUHOZUMOZWIJUUHUUOUUPUUHXREUUHFXOFWIKZXLXOFXMFUAKXNFVCSURZVDVEX
      LEWIKZXOXHUUTXKXEXFUUTXGXEXFNEABEIVFURVGSZSVHUUHCUULVEVIVJVKZVHVLTVAUUHUU
      IYHBBQOZROYBUUHEUVCYHRXLEUVCMZXOXLEAUGUHOZBUGUHOZPOZUVCIXLUVGLUVFPOZUVCXL
      UVELUVFPXIUVELMXHXJAVMUQVAXHUVHUVCMXKXHUVHUVFUVCXHUVFXHBXHBXEXFXGVNURZVEV
      LXHBUVIVOTSTVPZSZVSUUHYABBUVBUUNUUNXHXIXJXOVQZUVLVRTTVGSVTWAWBXQXTYPXQXSY
      OHXQYOYLUVCROZXSXLXOYOUVMMXPUUHYNYLEUVCRUUHYNYLLUMOYLUUHYMLYLUMUUHYMLYAQO
      ZLXLYMUVNMZXOXIUVOXHXJALYAQUPUQZSUUHYAUVBUTTVSUUHYLUUHBCUUNUULVHWCTUVKWDV
      GXQCBBXLXOCWIKXPUULVGXLXOBWIKXPUUNVGZUVQXIXJXHXOXPWJZUVRVRWEWAWFWGUUFYDYT
      UUCUUFYDYTUUFYCYSGUUFYSYCXQYSYCMZXTXLXOUVSXPUUHYHUKZEROZYAUKZBROZYSYCUUHU
      WABUWBQOZUVCROUWCUUHUVTUWDEUVCRUUHUWDUVTUUHBYAUUNUVBWHVTUVKWDUUHUWBBBUUHY
      AUVBWKUUNUUNUVLUVLVRTUUHYRUVTERUUHYRLYHUMOUVTUUHYGLYHUMUUMVAYHWLWMVAUUHYA
      BUVBUUNUVLWNWOVGSVTWAWBXQXTUUCXQXSUUBHXQUUBUVMXSXQUUAYLEUVCRXQUUAYLLPOYLX
      QYMLYLPXQYMUVNLXLXOUVOXPUVPWPXQYAXQDXQDUUQWIJXQUUOUUPXQXREXQFXOXLUURXPUUS
      WSVEXLXOUUTXPUVAWPVHXQCXQCXEXFXGXKXOXPWQURZVEVIVJVKUTTVSXQYLXQBCXQBXEXFXG
      XKXOXPWRURZUWEVHWTTXLXOUVDXPUVJWPWDXQCBBUWEUWFUWFUVRUVRVRWEWAWFWGXAXBXCXD
      $.

    $( Lemma for ~ itsclc0 .  Solutions of the quadratic equations for the
       coordinates of the intersection points of a (nondegenerate) line and a
       circle.  (Contributed by AV, 25-Feb-2023.) $)
    itsclc0xyqsol $p |- ( ( ( ( A e. RR /\ B e. RR /\ C e. RR )
                                 /\ ( A =/= 0 \/ B =/= 0 ) )
                          /\ ( R e. RR+ /\ 0 <_ D ) /\ ( X e. RR /\ Y e. RR ) )
                         -> ( ( ( ( X ^ 2 ) + ( Y ^ 2 ) ) = ( R ^ 2 )
                                /\ ( ( A x. X ) + ( B x. Y ) ) = C )
           -> ( ( X = ( ( ( A x. C ) + ( B x. ( sqrt ` D ) ) ) / Q )
               /\ Y = ( ( ( B x. C ) - ( A x. ( sqrt ` D ) ) ) / Q ) )
             \/ ( X = ( ( ( A x. C ) - ( B x. ( sqrt ` D ) ) ) / Q )
               /\ Y = ( ( ( B x. C ) + ( A x. ( sqrt ` D ) ) ) / Q ) ) ) ) ) $=
      ( cr wcel cc0 wa co caddc wceq cmul cdiv wi w3a wne wo crp cle cexp csqrt
      wbr c2 cfv cmin itscnhlc0xyqsol expcom 3impd wn nne itschlc0xyqsol sylanb
      3exp jaoi3 impcom 3imp ) AKLZBKLZCKLZUAZAMUBZBMUBZUCZNFUDLMDUEUHNZGKLHKLN
      ZGUIUFOHUIUFOPOFUIUFOQAGROBHROPOCQNGACROZBDUGUJZROZPOESOQHBCROZAVMROZUKOE
      SOQNGVLVNUKOESOQHVOVPPOESOQNUCTZVIVFVJVKVQTTZVGVFVRTZVHVGVCVDVEVRVCVGVDVE
      VRTTVCVGNZVDVEVRVTVDVEUAVJVKVQABCDEFGHIJULUSUSUMUNVGUOAMQZVHVSAMUPVFWAVHN
      ZVRVFWBNVJVKVQABCDEFGHIJUQUSUMURUTVAVB $.
  $}

  ${
    itsclc0xyqsolr.q $e |- Q = ( ( A ^ 2 ) + ( B ^ 2 ) ) $.
    itsclc0xyqsolr.d $e |- D = ( ( ( R ^ 2 ) x. Q ) - ( C ^ 2 ) ) $.
    $( Lemma for ~ itsclc0 .  Solutions of the quadratic equations for the
       coordinates of the intersection points of a (nondegenerate) line and a
       circle.  (Contributed by AV, 2-May-2023.)  (Revised by AV,
       14-May-2023.) $)
    itsclc0xyqsolr $p |- ( ( ( A e. RR /\ B e. RR /\ C e. RR )
                          /\ ( A =/= 0 \/ B =/= 0 ) /\ ( R e. RR+ /\ 0 <_ D ) )
                -> ( ( ( X = ( ( ( A x. C ) + ( B x. ( sqrt ` D ) ) ) / Q )
                      /\ Y = ( ( ( B x. C ) - ( A x. ( sqrt ` D ) ) ) / Q ) )
                    \/ ( X = ( ( ( A x. C ) - ( B x. ( sqrt ` D ) ) ) / Q )
                      /\ Y = ( ( ( B x. C ) + ( A x. ( sqrt ` D ) ) ) / Q ) ) )
                     -> ( ( ( X ^ 2 ) + ( Y ^ 2 ) ) = ( R ^ 2 )
                          /\ ( ( A x. X ) + ( B x. Y ) ) = C ) ) ) $=
      ( cmul co caddc cdiv wceq c2 cexp mulcld oveq1d eqtrd cr wcel w3a cc0 wne
      wo crp cle wbr csqrt cfv cmin recn 3ad2ant1 3ad2ant3 3ad2ant2 rpre adantr
      wa anim2i 3adant2 itsclc0lem3 syl recnd sqrtcld addcld resum2sqcl 3adant3
      cc simp11 simp12 simp2 resum2sqorgt0 syl3anc gt0ne0d sqdivd binom2 sqmuld
      clt syl2anc simp3r resqrtth oveq2d oveq12d subcld binom2sub mul4d mulcomd
      sqcld 2cnd cz 2z a1i expne0d divdird add4d ppncand adddird eqcomi 3eqtr2d
      addcomd eqtr3d adddid eqcomd sqvald divcan5d rpcn pncan3d divmul3d mpbird
      divassd adantl mulassd subdid simpl 3adant1 divmul2d jca oveqan12d eqeq1d
      simpr oveq1 oveq2 anbi12d syl5ibrcom nppcan3d simp1 simp3 remulcld jaod )
      AUAUBZBUAUBZCUAUBZUCZAUDUEBUDUEUFZFUGUBZUDDUHUIZUSZUCZGACKLZBDUJUKZKLZMLZ
      ENLZOZHBCKLZAUUAKLZULLZENLZOZUSZGPQLZHPQLZMLZFPQLZOZAGKLZBHKLZMLZCOZUSZGY
      TUUBULLZENLZOZHUUFUUGMLZENLZOZUSZYSUVAUUKUUDPQLZUUIPQLZMLZUUOOZAUUDKLZBUU
      IKLZMLZCOZUSYSUVLUVPYSUVKAPQLZCPQLZKLZPYTUUBKLZKLZMLZBPQLZDKLZMLZEPQLZNLZ
      UWCUVRKLZUWAULLZUVQDKLZMLZUWFNLZMLUWEUWKMLZUWFNLZUUOYSUVIUWGUVJUWLMYSUVIU
      UCPQLZUWFNLUWGYSUUCEYSYTUUBYSACYNYOAVIUBZYRYKYLUWPYMAUMZUNZUNZYNYOCVIUBZY
      RYMYKUWTYLCUMZUOZUNZRZYSBUUAYNYOBVIUBZYRYLYKUXEYMBUMZUPZUNZYSDYSDYSYNFUAU
      BZUSZDUAUBZYNYRUXJYOYRUXIYNYPUXIYQFUQURUTVAABCDEFIJVBVCZVDZVEZRZVFZYNYOEV
      IUBYRYNEYKYLEUAUBYMABEIVGVHVDUNZYSEYSYKYLYOUDEVSUIYKYLYMYOYRVJZYKYLYMYOYR
      VKYNYOYRVLABEIVMVNVOZVPYSUWOUWEUWFNYSUWOYTPQLZUWAMLZUUBPQLZMLZUWEYSYTVIUB
      ZUUBVIUBZUWOUYCOYNYOUYDYRYNACUWRUXBRUNZUXOYTUUBVQVTYSUYAUWBUYBUWDMYSUXTUV
      SUWAMYNYOUXTUVSOYRYNACUWRUXBVRUNZSYSUYBUWCUUAPQLZKLUWDYSBUUAUXHUXNVRYSUYH
      DUWCKYSUXKYQUYHDOUXLYNYOYPYQWADWBVTZWCTZWDTSTYSUVJUUHPQLZUWFNLUWLYSUUHEYS
      UUFUUGYSBCUXHUXCRZYSAUUAUWSUXNRZWEZUXQUXSVPYSUYKUWKUWFNYSUYKUUFPQLZPUUFUU
      GKLZKLZULLZUUGPQLZMLZUWKYSUUFVIUBZUUGVIUBZUYKUYTOUYLYSAUUAYSAUXRVDZUXNRZU
      UFUUGWFVTYSUYRUWIUYSUWJMYSUYOUWHUYQUWAULYNYOUYOUWHOYRYNBCUXGUXBVRUNZYSUYP
      UVTPKYSUYPBAKLZCUUAKLZKLZUVTYSBCAUUAUXHUXCVUCUXNWGYSVUHABKLZVUGKLUVTYSVUF
      VUIVUGKYSBAUXHVUCWHSYSABCUUAVUCUXHUXCUXNWGTTWCZWDYSUYSUVQUYHKLUWJYSAUUAVU
      CUXNVRYSUYHDUVQKUYIWCTZWDTSTWDYSUWEUWKUWFYSUWBUWDYSUVSUWAYSUVQUVRYSAUWSWI
      ZYSCUXCWIZRZYSPUVTYSWJZYSYTUUBUXDUXORRZVFZYSUWCDYSBUXHWIZUXMRZVFYSUWIUWJY
      SUWHUWAYSUWCUVRVURVUMRZVUPWEZYSUVQDVULUXMRZVFYSEUXQWIZYSEPUXQUXSPWKUBYSWL
      WMWNZWOYSUWNEUVRKLZEDKLZMLZUWFNLZUUOYSUWMVVGUWFNYSUWMUWBUWIMLZUWDUWJMLZML
      VVGYSUWBUWDUWIUWJVUQVUSVVAVVBWPYSVVIVVEVVJVVFMYSVVIUVSUWHMLZUVQUWCMLZUVRK
      LZVVEYSUVSUWAUWHVUNVUPVUTWQYSUVQUWCUVRYSAVUCWIZVURVUMWRZYSVVLEUVRKVVLEOYS
      EVVLIWSWMZSZWTYSUWCUVQMLZDKLVVJVVFYSUWCUVQDVURVVNUXMWRYSVVREDKYSVVRVVLEYS
      UWCUVQVURVVNXAVVPTSXBZWDTSYSVVHUVRDMLZENLZUUOYSVVHEVVTKLZEEKLZNLVWAYSVVGV
      WBUWFVWCNYSVWBVVGYSEUVRDUXQVUMUXMXCXDYSEUXQXEWDYSVVTEEYSUVRDVUMUXMVFZUXQU
      XQUXSUXSXFTYSVWAUUOOVVTUUOEKLZOYSVVTUVRVWEUVRULLZMLVWEYSDVWFUVRMDVWFOYSJW
      MWCYSUVRVWEVUMYSUUOEYSFYRYNFVIUBZYOYPVWGYQFXGURUOWIZUXQRXHTYSVVTUUOEVWDVW
      HUXQUXSXIXJTZTWTYSUVOUVQCKLZVUIUUAKLZMLZENLZUWCCKLZVWKULLZENLZMLVWLVWOMLZ
      ENLZCYSUVMVWMUVNVWPMYSAUUCKLZENLUVMVWMYSAUUCEUWSUXPUXQUXSXKYSVWSVWLENYSVW
      SAYTKLZAUUBKLZMLVWLYSAYTUUBUWSUXDUXOXCYSVWTVWJVXAVWKMYNYOVWTVWJOZYRYKYMVX
      BYLYKYMUSZAAKLZCKLVWTVWJVXCAACYKUWPYMUWQURZVXEYMUWTYKUXAXLXMVXCVXDUVQCKVX
      CUVQVXDVXCAVXEXEXDSXBVAUNZYSVWKVXAYSABUUAUWSUXHUXNXMXDZWDTSXBYSBUUHKLZENL
      UVNVWPYSBUUHEUXHUYNUXQUXSXKYSVXHVWOENYSVXHBUUFKLZBUUGKLZULLVWOYSBUUFUUGUX
      HUYLUYMXNYSVXIVWNVXJVWKULYNYOVXIVWNOZYRYLYMVXKYKYLYMUSZBBKLZCKLVXIVWNVXLB
      BCVXLBYLYMXOVDZVXNVXLCYLYMYAVDXMVXLVXMUWCCKYLVXMUWCOYMYLUWCVXMYLBUXFXEXDU
      RSXBXPUNZYSVUFUUAKLVXJVWKYSBAUUAUXHUWSUXNXMYSVUFVUIUUAKYNYOVUFVUIOYRYNBAU
      XGUWRWHUNSXBZWDTSXBWDYSVWLVWOEYSVWJVWKYSUVQCVULUXCRZYSVUIUUAYSABUWSUXHRUX
      NRZVFZYSVWNVWKYSUWCCVURUXCRZVXRWEZUXQUXSWOYSVWRCOVWQECKLZOYSVWQVWJVWNMLZV
      VLCKLZVYBYSVWJVWKVWNVXQVXRVXTWQYSUVQUWCCVULVURUXCWRZYSVVLECKYSEVVLEVVLOYS
      IWMXDSZWTYSVWQCEYSVWLVWOVXSVYAVFUXCUXQUXSXQXJWTXRUUKUUPUVLUUTUVPUUKUUNUVK
      UUOUUEUUJUULUVIUUMUVJMGUUDPQYBHUUIPQYBXSXTUUKUUSUVOCUUEUUJUUQUVMUURUVNMGU
      UDAKYCHUUIBKYCXSXTYDYEYSUVAUVHUVCPQLZUVFPQLZMLZUUOOZAUVCKLZBUVFKLZMLZCOZU
      SYSVYJVYNYSVYIVVHUUOYSVYIUVSUWAULLZUWDMLZUWFNLZUWHUWAMLZUWJMLZUWFNLZMLVYP
      VYSMLZUWFNLVVHYSVYGVYQVYHVYTMYSVYGUVBPQLZUWFNLVYQYSUVBEYSYTUUBUYFUXOWEUXQ
      UXSVPYSWUBVYPUWFNYSWUBUXTUWAULLZUYBMLZVYPYSUYDUYEWUBWUDOUYFUXOYTUUBWFVTYS
      WUCVYOUYBUWDMYSUXTUVSUWAULUYGSUYJWDTSTYSVYHUVEPQLZUWFNLVYTYSUVEEYSUUFUUGU
      YLVUDVFUXQUXSVPYSWUEVYSUWFNYSWUEUYOUYQMLZUYSMLZVYSYSVUAVUBWUEWUGOUYLVUDUU
      FUUGVQVTYSWUFVYRUYSUWJMYSUYOUWHUYQUWAMVUEVUJWDVUKWDTSTWDYSVYPVYSUWFYSVYOU
      WDYSUVSUWAYSUVQUVRVVNVUMRZYSPUVTVUOYSYTUUBUYFUXORRZWEZVUSVFYSVYRUWJYSUWHU
      WAVUTWUIVFZYSUVQDVVNUXMRZVFVVCVVDWOYSWUAVVGUWFNYSWUAVYOVYRMLZVVJMLVVGYSVY
      OUWDVYRUWJWUJVUSWUKWULWPYSWUMVVEVVJVVFMYSWUMVVKVVMVVEYSUVSUWAUWHWUHWUIVUT
      YFVVOVVQWTVVSWDTSWTVWITYSVYMVWJVWKULLZENLZVWNVWKMLZENLZMLWUNWUPMLZENLZCYS
      VYKWUOVYLWUQMYSAUVBKLZENLVYKWUOYSAUVBEUWSYSYTUUBYNYOUYDYRYNYTYNACYKYLYMYG
      YKYLYMYHYIVDUNZUXOWEUXQUXSXKYSWUTWUNENYSWUTVWTVXAULLWUNYSAYTUUBUWSWVAUXOX
      NYSVWTVWJVXAVWKULVXFVXGWDTSXBYSBUVEKLZENLVYLWUQYSBUVEEUXHYSUUFUUGUYLUYMVF
      UXQUXSXKYSWVBWUPENYSWVBVXIVXJMLWUPYSBUUFUUGUXHUYLUYMXCYSVXIVWNVXJVWKMVXOV
      XPWDTSXBWDYSWUNWUPEYSVWJVWKVXQVXRWEZYSVWNVWKVXTVXRVFZUXQUXSWOYSWUSCOWURVY
      BOYSWURVYCVYDVYBYSVWJVWKVWNVXQVXRVXTYFVYEVYFWTYSWURCEYSWUNWUPWVCWVDVFUXCU
      XQUXSXQXJWTXRUVHUUPVYJUUTVYNUVHUUNVYIUUOUVDUVGUULVYGUUMVYHMGUVCPQYBHUVFPQ
      YBXSXTUVHUUSVYMCUVDUVGUUQVYKUURVYLMGUVCAKYCHUVFBKYCXSXTYDYEYJ $.

    $( Lemma for ~ itsclc0 .  Solutions of the quadratic equations for the
       coordinates of the intersection points of a (nondegenerate) line and a
       circle.  (Contributed by AV, 2-May-2023.)  (Revised by AV,
       14-May-2023.) $)
    itsclc0xyqsolb $p |- ( ( ( ( A e. RR /\ B e. RR /\ C e. RR )
                               /\ ( A =/= 0 \/ B =/= 0 ) )
                      /\ ( ( R e. RR+ /\ 0 <_ D ) /\ ( X e. RR /\ Y e. RR ) ) )
                         -> ( ( ( ( X ^ 2 ) + ( Y ^ 2 ) ) = ( R ^ 2 )
                                /\ ( ( A x. X ) + ( B x. Y ) ) = C )
           <-> ( ( X = ( ( ( A x. C ) + ( B x. ( sqrt ` D ) ) ) / Q )
               /\ Y = ( ( ( B x. C ) - ( A x. ( sqrt ` D ) ) ) / Q ) )
             \/ ( X = ( ( ( A x. C ) - ( B x. ( sqrt ` D ) ) ) / Q )
               /\ Y = ( ( ( B x. C ) + ( A x. ( sqrt ` D ) ) ) / Q ) ) ) ) ) $=
      ( cr wcel cc0 wa c2 co caddc wceq cmul cdiv w3a wne wo crp cle cexp csqrt
      wbr cfv cmin wi itsclc0xyqsol 3expb simpl itsclc0xyqsolr syl2an3an impbid
      simpr ) AKLBKLCKLUAZAMUBBMUBUCZNZFUDLMDUEUHNZGKLHKLNZNZNGOUFPHOUFPQPFOUFP
      RAGSPBHSPQPCRNZGACSPZBDUGUIZSPZQPETPRHBCSPZAVGSPZUJPETPRNGVFVHUJPETPRHVIV
      JQPETPRNUCZVAVBVCVEVKUKABCDEFGHIJULUMVAUSUTVDVBVKVEUKUSUTUNUSUTURVBVCUNAB
      CDEFGHIJUOUPUQ $.
  $}

  ${
    $d A p $.  $d B p $.  $d C p $.  $d E p $.  $d I p $.  $d P p $.  $d R p $.
    $d X p $.  $d .0. p $.
    itsclc0.i $e |- I = { 1 , 2 } $.
    itsclc0.e $e |- E = ( RR^ ` I ) $.
    itsclc0.p $e |- P = ( RR ^m I ) $.
    itsclc0.s $e |- S = ( Sphere ` E ) $.
    itsclc0.0 $e |- .0. = ( I X. { 0 } ) $.
    itsclc0.q $e |- Q = ( ( A ^ 2 ) + ( B ^ 2 ) ) $.
    itsclc0.d $e |- D = ( ( ( R ^ 2 ) x. Q ) - ( C ^ 2 ) ) $.
    ${
      itsclc0.l $e |- L = { p e. P | ( ( A x. ( p ` 1 ) )
                                        + ( B x. ( p ` 2 ) ) ) = C } $.
      $( The intersection points of a line ` L ` and a circle around the
         origin.  (Contributed by AV, 25-Feb-2023.) $)
      itsclc0 $p |- ( ( ( A e. RR /\ B e. RR /\ C e. RR )
                          /\ ( A =/= 0 \/ B =/= 0 ) /\ ( R e. RR+ /\ 0 <_ D ) )
         -> ( ( X e. ( .0. S R ) /\ X e. L )
            -> ( ( ( X ` 1 ) = ( ( ( A x. C ) + ( B x. ( sqrt ` D ) ) ) / Q )
                /\ ( X ` 2 ) = ( ( ( B x. C ) - ( A x. ( sqrt ` D ) ) ) / Q ) )
              \/ ( ( X ` 1 ) = ( ( ( A x. C ) - ( B x. ( sqrt ` D ) ) ) / Q )
                /\ ( X ` 2 )
                   = ( ( ( B x. C ) + ( A x. ( sqrt ` D ) ) ) / Q ) ) ) ) ) $=
        ( cr wcel w3a cc0 wne wo crp cle wbr wa co c1 cv cfv c2 cexp caddc wceq
        crab cmul cdiv cmin cpnf cico wb rprege0 elrege0 sylibr adantr 3ad2ant3
        csqrt eqid 2sphere0 eleq2d syl oveq2d oveq12d eqeq1d elrab2 a1i anbi12d
        fveq1 wi oveq1d elrab 3simpa simpl3 rrx2pxel rrx2pyel jca itsclc0xyqsol
        adantl syl3anc expcomd expimpd com23 adantld biimtrid impd sylbid ) AUC
        UDBUCUDCUCUDUEZAUFUGBUFUGUHZGUIUDZUFDUJUKZULZUEZLMGHUMZUDZLKUDZULLUNNUO
        ZUPZUQURUMZUQXLUPZUQURUMZUSUMZGUQURUMZUTZNEVAZUDZLEUDZAUNLUPZVBUMZBUQLU
        PZVBUMZUSUMZCUTZULZULYCACVBUMZBDVMUPZVBUMZUSUMFVCUMUTYEBCVBUMZAYKVBUMZV
        DUMFVCUMUTULYCYJYLVDUMFVCUMUTYEYMYNUSUMFVCUMUTULUHZXHXJYAXKYIXHGUFVEVFU
        MUDZXJYAVGXGXCYPXDXEYPXFXEGUCUDUFGUJUKULYPGVHGVIVJVKVLYPXIXTLXTEGHIJMNO
        PQRSXTVNVOVPVQXKYIVGXHAXMVBUMZBXOVBUMZUSUMZCUTYHNLEKXLLUTZYSYGCYTYQYDYR
        YFUSYTXMYCAVBUNXLLWDZVRYTXOYEBVBUQXLLWDZVRVSVTUBWAWBWCXHYAYIYOYAYBYCUQU
        RUMZYEUQURUMZUSUMZXRUTZULXHYIYOWEZXSUUFNLEYTXQUUEXRYTXNUUCXPUUDUSYTXMYC
        UQURUUAWFYTXOYEUQURUUBWFVSVTWGXHUUFUUGYBXHYIUUFYOXHYBYHUUFYOWEXHYBULZUU
        FYHYOUUHXCXDULZXGYCUCUDZYEUCUDZULZUUFYHULYOWEXHUUIYBXCXDXGWHVKXCXDXGYBW
        IYBUULXHYBUUJUUKEJLOQWJEJLOQWKWLWNABCDFGYCYETUAWMWOWPWQWRWSWTXAXB $.

      $( The intersection points of a (nondegenerate) line through two points
         and a circle around the origin.  (Contributed by AV, 2-May-2023.)
         (Revised by AV, 14-May-2023.) $)
      itsclc0b $p |- ( ( ( A e. RR /\ B e. RR /\ C e. RR )
                    /\ ( A =/= 0 \/ B =/= 0 ) /\ ( R e. RR+ /\ 0 <_ D ) )
         -> ( ( X e. ( .0. S R ) /\ X e. L )
              <-> ( X e. P
            /\ ( ( ( X ` 1 ) = ( ( ( A x. C ) + ( B x. ( sqrt ` D ) ) ) / Q )
                /\ ( X ` 2 ) = ( ( ( B x. C ) - ( A x. ( sqrt ` D ) ) ) / Q ) )
              \/ ( ( X ` 1 ) = ( ( ( A x. C ) - ( B x. ( sqrt ` D ) ) ) / Q )
                /\ ( X ` 2 )
                  = ( ( ( B x. C ) + ( A x. ( sqrt ` D ) ) ) / Q ) ) ) ) ) ) $=
        ( cr wcel w3a cc0 wne wo crp cle wbr wa co c1 cv cfv c2 cexp caddc wceq
        crab cmul cdiv cmin cpnf cico wb rprege0 elrege0 sylibr adantr 3ad2ant3
        csqrt eqid 2sphere0 eleq2d syl oveq2d oveq12d eqeq1d elrab2 a1i anbi12d
        fveq1 oveq1d elrab anbi1i anandi simpl1 simpl2 simpl3l simpl3r rrx2pxel
        rrx2pyel jca adantl jca31 itsclc0xyqsolb syl21anc pm5.32da bitrid bitrd
        bitr3id ) AUCUDBUCUDCUCUDUEZAUFUGBUFUGUHZGUIUDZUFDUJUKZULZUEZLMGHUMZUDZ
        LKUDZULLUNNUOZUPZUQURUMZUQXMUPZUQURUMZUSUMZGUQURUMZUTZNEVAZUDZLEUDZAUNL
        UPZVBUMZBUQLUPZVBUMZUSUMZCUTZULZULZYCYDACVBUMZBDVMUPZVBUMZUSUMFVCUMUTYF
        BCVBUMZAYMVBUMZVDUMFVCUMUTULYDYLYNVDUMFVCUMUTYFYOYPUSUMFVCUMUTULUHZULZX
        IXKYBXLYJXIGUFVEVFUMUDZXKYBVGXHXDYSXEXFYSXGXFGUCUDUFGUJUKULYSGVHGVIVJVK
        VLYSXJYALYAEGHIJMNOPQRSYAVNVOVPVQXLYJVGXIAXNVBUMZBXPVBUMZUSUMZCUTYINLEK
        XMLUTZUUBYHCUUCYTYEUUAYGUSUUCXNYDAVBUNXMLWDZVRUUCXPYFBVBUQXMLWDZVRVSVTU
        BWAWBWCYKYCYDUQURUMZYFUQURUMZUSUMZXSUTZULZYJULZXIYRYBUUJYJXTUUINLEUUCXR
        UUHXSUUCXOUUFXQUUGUSUUCXNYDUQURUUDWEUUCXPYFUQURUUEWEVSVTWFWGUUKYCUUIYIU
        LZULXIYRYCUUIYIWHXIYCUULYQXIYCULZXDXEXHYDUCUDZYFUCUDZULZULUULYQVGXDXEXH
        YCWIXDXEXHYCWJUUMXFXGUUPXFXGXDXEYCWKXFXGXDXEYCWLYCUUPXIYCUUNUUOEJLOQWME
        JLOQWNWOWPWQABCDFGYDYFTUAWRWSWTXCXAXB $.
    $}

    $d .0. p $.  $d A p $.  $d B p $.  $d C p $.  $d D p $.  $d E p $.
    $d I p $.  $d P p $.  $d R p $.  $d X p $.  $d Y p $.  $d Z p $.
    itsclinecirc0.l $e |- L = ( LineM ` E ) $.
    itsclinecirc0.a $e |- A = ( ( Y ` 2 ) - ( Z ` 2 ) ) $.
    itsclinecirc0.b $e |- B = ( ( Z ` 1 ) - ( Y ` 1 ) ) $.
    itsclinecirc0.c $e |- C = ( ( ( Y ` 2 ) x. ( Z ` 1 ) )
                             - ( ( Y ` 1 ) x. ( Z ` 2 ) ) ) $.
    $( The intersection points of a line through two different points ` Y ` and
       ` Z ` and a circle around the origin, using the definition of a line in
       a two dimensional Euclidean space.  (Contributed by AV, 25-Feb-2023.)
       (Proof shortened by AV, 16-May-2023.) $)
    itsclinecirc0 $p |- ( ( ( Y e. P /\ Z e. P /\ Y =/= Z )
                               /\ ( R e. RR+ /\ 0 <_ D ) )
         -> ( ( X e. ( .0. S R ) /\ X e. ( Y L Z ) )
            -> ( ( ( X ` 1 ) = ( ( ( A x. C ) + ( B x. ( sqrt ` D ) ) ) / Q )
                /\ ( X ` 2 ) = ( ( ( B x. C ) - ( A x. ( sqrt ` D ) ) ) / Q ) )
              \/ ( ( X ` 1 ) = ( ( ( A x. C ) - ( B x. ( sqrt ` D ) ) ) / Q )
                /\ ( X ` 2 )
                   = ( ( ( B x. C ) + ( A x. ( sqrt ` D ) ) ) / Q ) ) ) ) ) $=
      ( vp wcel wne w3a crp cc0 cle wbr wa co c1 cv cfv cmul c2 caddc wceq crab
      csqrt cdiv wo rrx2linest2 adantr eleq2d anbi2d rrx2pyel 3ad2ant1 3ad2ant2
      cmin cr wi resubcld eqeltrid rrx2pxel remulcld rrx2pnedifcoorneorr orcomd
      simpr eqid itsclc0 syl311anc sylbid ) MEUHZOEUHZMOUIZUJZGUKUHULDUMUNUOZUO
      ZLNGHUPUHZLMOKUPZUHZUOWOLAUQUGURZUSUTUPBVAWRUSUTUPVBUPCVCUGEVDZUHZUOZUQLU
      SZACUTUPZBDVEUSZUTUPZVBUPFVFUPVCVALUSZBCUTUPZAXDUTUPZVOUPFVFUPVCUOXBXCXEV
      OUPFVFUPVCXFXGXHVBUPFVFUPVCUOVGZWNWQWTWOWNWPWSLWLWPWSVCWMABCEIJKMOUGPQRUC
      UDUEUFVHVIVJVKWNAVPUHZBVPUHZCVPUHZAULUIZBULUIZVGZWMXAXIVQWLXJWMWLAVAMUSZV
      AOUSZVOUPVPUDWLXPXQWIWJXPVPUHWKEJMPRVLVMZWJWIXQVPUHWKEJOPRVLVNZVRVSVIWLXK
      WMWLBUQOUSZUQMUSZVOUPVPUEWLXTYAWJWIXTVPUHWKEJOPRVTVNZWIWJYAVPUHWKEJMPRVTV
      MZVRVSVIWLXLWMWLCXPXTUTUPZYAXQUTUPZVOUPVPUFWLYDYEWLXPXTXRYBWAWLYAXQYCXSWA
      VRVSVIWLXOWMWLXNXMBAEJMOPRUEUDWBWCVIWLWMWDABCDEFGHIJWSLNUGPQRSTUAUBWSWEWF
      WGWH $.
  $}

  ${
    $d A p $.  $d B p $.  $d C p $.  $d E p $.  $d I p $.  $d P p $.  $d R p $.
    $d X p $.  $d .0. p $.  $d .0. p $.  $d A p $.  $d B p $.  $d C p $.
    $d D p $.  $d E p $.  $d I p $.  $d P p $.  $d R p $.  $d X p $.  $d Y p $.
    $d Z p $.
    itsclinecirc0b.i $e |- I = { 1 , 2 } $.
    itsclinecirc0b.e $e |- E = ( RR^ ` I ) $.
    itsclinecirc0b.p $e |- P = ( RR ^m I ) $.
    itsclinecirc0b.s $e |- S = ( Sphere ` E ) $.
    itsclinecirc0b.0 $e |- .0. = ( I X. { 0 } ) $.
    itsclinecirc0b.q $e |- Q = ( ( A ^ 2 ) + ( B ^ 2 ) ) $.
    itsclinecirc0b.d $e |- D = ( ( ( R ^ 2 ) x. Q ) - ( C ^ 2 ) ) $.
    itsclinecirc0b.l $e |- L = ( LineM ` E ) $.
    itsclinecirc0b.a $e |- A = ( ( X ` 2 ) - ( Y ` 2 ) ) $.
    itsclinecirc0b.b $e |- B = ( ( Y ` 1 ) - ( X ` 1 ) ) $.
    itsclinecirc0b.c $e |- C = ( ( ( X ` 2 ) x. ( Y ` 1 ) )
                                 - ( ( X ` 1 ) x. ( Y ` 2 ) ) ) $.
    $( The intersection points of a line through two different points and a
       circle around the origin, using the definition of a line in a two
       dimensional Euclidean space.  (Contributed by AV, 2-May-2023.)  (Revised
       by AV, 14-May-2023.) $)
    itsclinecirc0b $p |- ( ( ( X e. P /\ Y e. P /\ X =/= Y )
                             /\ ( R e. RR+ /\ 0 <_ D ) )
          -> ( ( Z e. ( .0. S R ) /\ Z e. ( X L Y ) )
            <-> ( Z e. P
            /\ ( ( ( Z ` 1 ) = ( ( ( A x. C ) + ( B x. ( sqrt ` D ) ) ) / Q )
                /\ ( Z ` 2 ) = ( ( ( B x. C ) - ( A x. ( sqrt ` D ) ) ) / Q ) )
              \/ ( ( Z ` 1 ) = ( ( ( A x. C ) - ( B x. ( sqrt ` D ) ) ) / Q )
                /\ ( Z ` 2 )
                  = ( ( ( B x. C ) + ( A x. ( sqrt ` D ) ) ) / Q ) ) ) ) ) ) $=
      ( vp wcel wne w3a crp cc0 cle wbr wa co c1 cv cfv cmul c2 caddc wceq crab
      csqrt cdiv cmin rrx2linest adantr eqcom rrx2pxel adantl resubcld eqeltrid
      wo cr 3adant3 ad2antrr rrx2pyel remulcld recnd cc subaddd bitr4id addcomd
      eqid cneg negsubdi2d eqtr4id oveq1d mulneg1d eqtr2d oveq2d negsubd eqeq1d
      3eqtr2rd bitrd rabbidva eqtrd eleq2d anbi2d wb rrx2pnedifcoorneorr orcomd
      simpr itsclc0b syl311anc ) LEUHZMEUHZLMUIZUJZGUKUHULDUMUNUOZUOZONGHUPUHZO
      LMKUPZUHZUOXNOAUQUGURZUSZUTUPZBVAXQUSZUTUPZVBUPZCVCZUGEVDZUHZUOZOEUHUQOUS
      ZACUTUPZBDVEUSZUTUPZVBUPFVFUPVCVAOUSZBCUTUPZAYIUTUPZVGUPFVFUPVCUOYGYHYJVG
      UPFVFUPVCYKYLYMVBUPFVFUPVCUOVOUOZXMXPYEXNXMXOYDOXMXOYAVAMUSZVALUSZVGUPZXR
      UTUPZCVBUPZVCZUGEVDZYDXKXOUUAVCXLBYQCEIJKLMUGPQRUCUEYQWFUFVHVIXMYTYCUGEXM
      XQEUHZUOZYTYAYRVGUPZCVCZYCUUCYTYSYAVCUUEYAYSVJUUCYAYRCUUCYAUUCBXTXKBVPUHZ
      XLUUBXHXIUUFXJXHXIUOZBUQMUSZUQLUSZVGUPVPUEUUGUUHUUIXIUUHVPUHXHEJMPRVKVLZX
      HUUIVPUHXIEJLPRVKVIZVMVNVQZVRUUBXTVPUHXMEJXQPRVSVLVTWAZUUCYRUUCYQXRXKYQVP
      UHZXLUUBXHXIUUNXJUUGYOYPXIYOVPUHZXHEJMPRVSVLZXHYPVPUHZXIEJLPRVSVIZVMZVQVR
      UUBXRVPUHXMEJXQPRVKVLZVTWAZXKCWBUHZXLUUBXHXIUVBXJUUGCUUGCYPUUHUTUPZUUIYOU
      TUPZVGUPVPUFUUGUVCUVDUUGYPUUHUURUUJVTUUGUUIYOUUKUUPVTVMVNZWAVQVRWCWDUUCUU
      DYBCUUCYBYAXSVBUPYAYRWGZVBUPUUDUUCXSYAUUCXSUUCAXRXKAVPUHZXLUUBXHXIUVGXJUU
      GAYPYOVGUPZVPUDUUGYPYOUURUUPVMVNVQZVRUUTVTWAUUMWEUUCUVFXSYAVBUUCXSYQWGZXR
      UTUPUVFUUCAUVJXRUTUUCAUVHUVJUDUUCYOYPUUCYOXKUUOXLUUBXHXIUUOXJUUPVQVRWAUUC
      YPXKUUQXLUUBXHXIUUQXJUURVQVRWAWHWIWJUUCYQXRXKYQWBUHZXLUUBXHXIUVKXJUUGYQUU
      SWAVQVRUUCXRUUTWAWKWLWMUUCYAYRUUMUVAWNWPWOWQWRWSWTXAXMUVGUUFCVPUHZAULUIZB
      ULUIZVOZXLYFYNXBXKUVGXLUVIVIXKUUFXLUULVIXKUVLXLXHXIUVLXJUVEVQVIXKUVOXLXKU
      VNUVMBAEJLMPRUEUDXCXDVIXKXLXEABCDEFGHIJYDONUGPQRSTUAUBYDWFXFXGWQ $.

    $d A z $.  $d B z $.  $d C z $.  $d D z $.  $d L z $.  $d P z $.  $d Q z $.
    $d R z $.  $d S z $.  $d X z $.  $d Y z $.  $d .0. z $.
    $( The intersection points of a line through two different points and a
       circle around the origin, using the definition of a line in a two
       dimensional Euclidean space, expressed as intersection.  (Contributed by
       AV, 7-May-2023.)  (Revised by AV, 14-May-2023.) $)
    itsclinecirc0in $p |- ( ( ( X e. P /\ Y e. P /\ X =/= Y )
                              /\ ( R e. RR+ /\ 0 <_ D ) )
     -> ( ( .0. S R ) i^i ( X L Y ) )
        = { { <. 1 , ( ( ( A x. C ) + ( B x. ( sqrt ` D ) ) ) / Q ) >. ,
              <. 2 , ( ( ( B x. C ) - ( A x. ( sqrt ` D ) ) ) / Q ) >. } ,
            { <. 1 , ( ( ( A x. C ) - ( B x. ( sqrt ` D ) ) ) / Q ) >. ,
              <. 2 , ( ( ( B x. C ) + ( A x. ( sqrt ` D ) ) ) / Q ) >. } } ) $=
      ( vz wcel wne w3a crp cc0 cle wbr wa co cin cmul csqrt cfv caddc cdiv cop
      c1 c2 cmin cpr cv wceq wo itsclinecirc0b bitrid cr rrx2pyel adantr adantl
      elin wb resubcld eqeltrid 3adant3 rrx2pxel remulcld 3jca rpre itsclc0lem3
      syl2an simprr jca resum2sqcl syl rrx2pnedifcoorneorr orcomd resum2sqorgt0
      syl3anc gt0ne0d itsclc0lem1 itsclc0lem2 prelrrx2b syl22anc bitrd eqrdv
      clt ) LEUGZMEUGZLMUHZUIZGUJUGZUKDULUMZUNZUNZUFNGHUOZLMKUOZUPZVCACUQUOZBDU
      RUSZUQUOZUTUOFVAUOZVBVDBCUQUOZAXOUQUOZVEUOFVAUOZVBVFVCXNXPVEUOFVAUOZVBVDX
      RXSUTUOFVAUOZVBVFVFZXJUFVGZXMUGZYDEUGVCYDUSZXQVHVDYDUSZXTVHUNYFYAVHYGYBVH
      UNVIUNZYDYCUGZYEYDXKUGYDXLUGUNXJYHYDXKXLVPABCDEFGHIJKLMNYDOPQRSTUAUBUCUDU
      EVJVKXJXQVLUGZXTVLUGZYAVLUGZYBVLUGZYHYIVQXJAVLUGZBVLUGZCVLUGZUIZDVLUGZXHU
      NZFVLUGZFUKUHZUNZYJXJYNYOYPXFYNXIXCXDYNXEXCXDUNZAVDLUSZVDMUSZVEUOVLUCUUCU
      UDUUEXCUUDVLUGXDEJLOQVMVNZXDUUEVLUGXCEJMOQVMVOZVRVSZVTZVNZXFYOXIXCXDYOXEU
      UCBVCMUSZVCLUSZVEUOVLUDUUCUUKUULXDUUKVLUGXCEJMOQWAVOZXCUULVLUGXDEJLOQWAVN
      ZVRVSZVTZVNZXFYPXIXCXDYPXEUUCCUUDUUKUQUOZUULUUEUQUOZVEUOVLUEUUCUURUUSUUCU
      UDUUKUUFUUMWBUUCUULUUEUUNUUGWBVRVSVTZVNZWCZXJYRXHXFYQGVLUGZYRXIXFYNYOYPUU
      IUUPUUTWCXGUVCXHGWDVNABCDFGTUAWEWFXFXGXHWGWHZXFUUBXIXFYTUUAXCXDYTXEUUCYNY
      OUNYTUUCYNYOUUHUUOWHABFTWIWJVTZXFFXFYNYOAUKUHZBUKUHZVIUKFXBUMUUIUUPXFUVGU
      VFBAEJLMOQUDUCWKWLABFTWMWNWOZWHVNABCDFWPWNXJYOYNYPUIZYSUUBYKXJYOYNYPUUQUU
      JUVAWCZUVDXJYTUUAXFYTXIUVEVNXFUUAXIUVHVNWHZBACDFWQWNXJYQYSUUBYLUVBUVDUVKA
      BCDFWQWNXJUVIYSUUBYMUVJUVDUVKBACDFWPWNXQXTEJYAYBYDOQWRWSWTXA $.
  $}

  ${
    itsclquadb.q $e |- Q = ( ( A ^ 2 ) + ( B ^ 2 ) ) $.
    ${
      $d A x $.  $d B x $.  $d C x $.  $d Q x $.  $d R x $.  $d T x $.
      $d U x $.  $d Y x $.
      itsclquadb.t $e |- T = -u ( 2 x. ( B x. C ) ) $.
      itsclquadb.u $e |- U = ( ( C ^ 2 ) - ( ( A ^ 2 ) x. ( R ^ 2 ) ) ) $.
      $( Quadratic equation for the y-coordinate of the intersection points of
         a line and a circle.  (Contributed by AV, 22-Feb-2023.) $)
      itsclquadb $p |- ( ( ( ( A e. RR /\ A =/= 0 ) /\ B e. RR /\ C e. RR )
                           /\ R e. RR+ /\ Y e. RR )
                -> ( E. x e. RR ( ( ( x ^ 2 ) + ( Y ^ 2 ) ) = ( R ^ 2 )
                                    /\ ( ( A x. x ) + ( B x. Y ) ) = C )
                     <-> ( ( Q x. ( Y ^ 2 ) ) + ( ( T x. Y ) + U ) ) = 0 ) ) $=
        ( wcel c2 co caddc wceq cmul cdiv recnd cr cc0 wne wa w3a crp cexp wrex
        cv wi simpl1 simp2 adantr simp3 anim1ci itscnhlc0yqe rexlimdva 3ad2ant1
        syl3anc cmin remulcld resubcld simp11l simp11r redivcld wb oveq1 oveq1d
        eqeq1d oveq2 anbi12d adantl sqdivd cc binom2sub syl2anc resqcld 2re a1i
        cneg negsubd mulassd eqcomd oveq2d mulcomd 3eqtrd negeqd eqtr3d oveq12d
        2cnd sqmuld mulneg1d eqcomi oveq1i eqtrd resqcl 3ad2ant3 recn sqne0 syl
        biimpar divcan2d divassd divdird addassd adddird addcomd oveq2i oveq12i
        renegcld eqeltrid readdcld rpre 3ad2ant2 eqtr4id addeq0 nncand divcan3d
        bitrd sylan9eqr ex sylbid imp npcand jca rspcedvd impbid ) BUAMZBUBUCZU
        DZCUAMZDUAMZUEZFUFMZIUAMZUEZAUIZNUGOZINUGOZPOZFNUGOZQZBYQROZCIROZPOZDQZ
        UDZAUAUHZEYSROZGIROZHPOZPOZUBQZYPUUGUUMAUAYPYQUAMZUDYMYNUUNYOUDUUGUUMUJ
        YMYNYOUUNUKYPYNUUNYMYNYOULUMYPYOUUNYMYNYOUNZUOBCDEFGHYQIJKLUPUSUQYPUUMU
        UHYPUUMUDZUUGDUUDUTOZBSOZNUGOZYSPOZUUAQZBUURROZUUDPOZDQZUDZAUURUAYPUURU
        AMUUMYPUUQBYPDUUDYMYNYLYOYJYKYLUNURZYPCIYMYNYKYOYJYKYLULURZUUOVAZVBZYHY
        IYKYLYNYOVCZYHYIYKYLYNYOVDZVEUMYQUURQZUUGUVEVFUUPUVLUUBUVAUUFUVDUVLYTUU
        TUUAUVLYRUUSYSPYQUURNUGVGVHVIUVLUUEUVCDUVLUUCUVBUUDPYQUURBRVJVHVIVKVLUU
        PUVAUVDUUPUUTDNUGOZUUJPOZCNUGOZYSROZPOZBNUGOZYSROZPOZUVRSOZUVMUVRUVOPOZ
        YSROZUUJPOZPOZUVRSOZUUAYPUUTUWAQUUMYPUUTUVQUVRSOZUVRYSUVRSOROZPOUWGUVSU
        VRSOZPOZUWAYPUUSUWGYSUWHPYPUUSUUQNUGOZUVRSOUWGYPUUQBYPUUQUVITZYPBUVJTZU
        VKVMYPUWKUVQUVRSYPUWKUVMNDUUDROZROZUTOZUUDNUGOZPOZUVMNCDROZROZIROZVTZPO
        ZUVPPOUVQYPDVNMUUDVNMUWKUWRQYPDUVFTZYPUUDUVHTZDUUDVOVPYPUWPUXCUWQUVPPYP
        UVMUWOVTZPOUWPUXCYPUVMUWOYPUVMYPDUVFVQZTZYPUWOYPNUWNNUAMYPVRVSZYPDUUDUV
        FUVHVAVATWAYPUXFUXBUVMPYPUWOUXAYPUWONDCROZIROZROZNUXJROZIROZUXAYPUWNUXK
        NRYPUXKUWNYPDCIUXDYPCUVGTZYPIUUOTZWBWCWDYPUXNUXLYPNUXJIYPWJYPUXJYPDCUVF
        UVGVATUXPWBWCYPUXMUWTIRYPUXJUWSNRYPDCUXDUXOWEWDVHWFWGWDWHYPCIUXOUXPWKWI
        YPUXCUVNUVPPYPUXBUUJUVMPYPUWTVTZIROZUXBUUJYPUWTIYPUWTYPNUWSUXIYPCDUVGUV
        FVAVAZTUXPWLUXRUUJQYPUXQGIRGUXQKWMWNVSWHWDVHWFVHWOYPUWHYSYPYSUVRYOYMYSV
        NMYNYOYSIWPTWQZYPUVRYPBUVJVQZTZYMYNUVRUBUCZYOYJYKUYCYLYHUYCYIYHBVNMUYCY
        IVFBWRBWSWTXAURURZXBWCWIYPUWHUWIUWGPYPUWIUWHYPUVRYSUVRUYBUXTUYBUYDXCWCW
        DYPUWAUWJYPUVQUVSUVRYPUVQYPUVNUVPYPUVMUUJUXGYPGIYPGUXQUAKYPUWTUXSXJXKUU
        OVAZXLZYPUVOYSYPCUVGVQZYPIUUOVQZVAZXLTYPUVSYPUVRYSUYAUYHVATZUYBUYDXDWCW
        FUMUUPUVTUWEUVRSYPUVTUWEQUUMYPUVTUVNUVPUVSPOZPOUVNUWCPOZUWEYPUVNUVPUVSY
        PUVNUYFTYPUVPUYITUYJXEYPUYKUWCUVNPYPUVOUVRPOZYSROUYKUWCYPUVOUVRYSYPUVOU
        YGTZUYBYPYSUYHTXFYPUYMUWBYSRYPUVOUVRUYNUYBXGVHWHWDYPUYLUVMUUJUWCPOZPOUW
        EYPUVMUUJUWCUXHYPUUJUYETZYPUWCYPUWBYSYPUVRUVOUYAUYGXLUYHVAZTZXEYPUYOUWD
        UVMPYPUUJUWCUYPUYRXGWDWOWFUMVHYPUUMUWFUUAQZYPUUMUWDUVMUVRUUAROZUTOZVTZQ
        ZUYSYPUUMUWDVUAPOZUBQZVUCYPUULVUDUBYPUULUWCUUJVUAPOZPOVUDUUIUWCUUKVUFPE
        UWBYSRJWNHVUAUUJPLXHXIYPUWCUUJVUAUYRUYPYPVUAYPUVMUYTUXGYPUVRUUAUYAYNYMU
        UAUAMYOYNFFXMVQXNZVAZVBTZXEXOVIYPUWDVNMVUAVNMVUEVUCVFYPUWDYPUWCUUJUYQUY
        EXLTVUIUWDVUAXPVPXSYPVUCUYSVUCYPUWFUVMVUBPOZUVRSOZUUAVUCUWEVUJUVRSUWDVU
        BUVMPVJVHYPVUKUYTUVRSOUUAYPVUJUYTUVRSYPVUJUVMVUAUTOUYTYPUVMVUAUXHVUIWAY
        PUVMUYTUXHYPUYTVUHTXQWOVHYPUUAUVRYPUUAVUGTUYBUYDXRWOXTYAYBYCWFYPUVDUUMY
        PUVCUUQUUDPODYPUVBUUQUUDPYPUUQBUWLUWMUVKXBVHYPDUUDUXDUXEYDWOUMYEYFYAYG
        $.

      $d A x z $.  $d B z $.  $d C z $.  $d R z $.  $d Y z $.
      $( Quadratic equation for the y-coordinate of the intersection points of
         a line and a circle.  (Contributed by AV, 23-Feb-2023.) $)
      itsclquadeu $p |- ( ( ( ( A e. RR /\ A =/= 0 ) /\ B e. RR /\ C e. RR )
                           /\ R e. RR+ /\ Y e. RR )
                -> ( E! x e. RR ( ( ( x ^ 2 ) + ( Y ^ 2 ) ) = ( R ^ 2 )
                                    /\ ( ( A x. x ) + ( B x. Y ) ) = C )
                     <-> ( ( Q x. ( Y ^ 2 ) ) + ( ( T x. Y ) + U ) ) = 0 ) ) $=
        ( vz cr wcel wa co caddc wceq cmul cc0 wne w3a crp cv c2 cexp wreu wral
        weq wi wrex wb oveq1 oveq1d eqeq1d oveq2 anbi12d reu8 a1i eqcoms eqeq2d
        adantl simp11l ad2antrr simpr remulcld recnd adantr simp12 simp3 simplr
        id addcan2d simp11r mulcand equcom 3bitrd biimpd sylbid an32s ralrimiva
        adantld ex pm4.71d bicomd rexbidva itsclquadb ) BNOZBUAUBZPZCNOZDNOZUCZ
        FUDOZINOZUCZAUEZUFUGQZIUFUGQZRQZFUFUGQZSZBWRTQZCITQZRQZDSZPZANUHZXHMUEZ
        UFUGQZWTRQZXBSZBXJTQZXERQZDSZPZAMUJZUKZMNUIZPZANULZXHANULEWTTQGITQHRQRQ
        UASXIYBUMWQXHXQAMNXRXCXMXGXPXRXAXLXBXRWSXKWTRWRXJUFUGUNUOUPXRXFXODXRXDX
        NXERWRXJBTUQUOUPURUSUTWQYAXHANWQWRNOZPZXHYAYDXHXTYDXGXTXCYDXGXTYDXGPZXS
        MNYEXJNOZPXPXRXMYDYFXGXPXRUKYDYFPZXGPXPXOXFSZXRXGXPYHUMYGXGDXFXODXFSZDX
        FYIVMVAVBVCYGYHXRUKXGYGYHXRYGYHXNXDSMAUJZXRYGXNXDXEYGXNYGBXJWQWIYCYFWIW
        JWLWMWOWPVDZVEZYDYFVFZVGVHYGXDYDXDNOYFYDBWRWQWIYCYKVIWQYCVFVGVIVHYGXEWQ
        XENOYCYFWQCIWKWLWMWOWPVJWNWOWPVKVGVEVHVNYGXJWRBYGXJYMVHYGWRWQYCYFVLVHYG
        BYLVHWQWJYCYFWIWJWLWMWOWPVOVEVPYJXRUMYGMAVQUTVRVSVIVTWAWCWBWDWCWEWFWGAB
        CDEFGHIJKLWHVR $.
    $}
  $}

  ${
    2itscp.a $e |- ( ph -> A e. RR ) $.
    2itscp.b $e |- ( ph -> B e. RR ) $.
    2itscp.x $e |- ( ph -> X e. RR ) $.
    2itscp.y $e |- ( ph -> Y e. RR ) $.
    2itscp.d $e |- D = ( X - A ) $.
    2itscp.e $e |- E = ( B - Y ) $.
    $( Lemma 1 for ~ 2itscp .  (Contributed by AV, 4-Mar-2023.) $)
    2itscplem1 $p |- ( ph -> ( ( ( ( E ^ 2 ) x. ( B ^ 2 ) )
                               + ( ( D ^ 2 ) x. ( A ^ 2 ) ) )
                               - ( 2 x. ( ( D x. A ) x. ( E x. B ) ) ) )
                             = ( ( ( D x. A ) - ( E x. B ) ) ^ 2 ) ) $=
      ( c2 cexp co cmul caddc cmin mulcld recnd subcld eqeltrid 2cnd addsubassd
      cc sqcld addcomd sqmuld eqcomd oveq1d oveq12d wcel wceq binom2sub syl2anc
      3eqtrd eqtr4d ) AENOPZCNOPZQPZDNOPZBNOPZQPZRPNDBQPZECQPZQPZQPZSPZVENOPZVH
      SPZVFNOPZRPZVEVFSPNOPZAVIVAVDVHSPZRPVOVARPVMAVAVDVHAUSUTAEAECGSPUFMACGACI
      UAZAGKUAUBUCZUGACVPUGTZAVBVCADADFBSPUFLAFBAFJUAABHUAZUBUCZUGABVSUGTZANVGA
      UDAVEVFADBVTVSTZAECVQVPTZTTZUEAVAVOVRAVDVHWAWDUBUHAVOVKVAVLRAVDVJVHSAVJVD
      ADBVTVSUIUJUKAVLVAAECVQVPUIUJULUQAVEUFUMVFUFUMVNVMUNWBWCVEVFUOUPUR $.

    2itscp.c $e |- C = ( ( D x. B ) + ( E x. A ) ) $.
    $( Lemma 2 for ~ 2itscp .  (Contributed by AV, 4-Mar-2023.) $)
    2itscplem2 $p |- ( ph -> ( C ^ 2 ) = ( ( ( ( D ^ 2 ) x. ( B ^ 2 ) )
                                     + ( 2 x. ( ( D x. A ) x. ( E x. B ) ) ) )
                                           + ( ( E ^ 2 ) x. ( A ^ 2 ) ) ) ) $=
      ( c2 cexp co cmul cc caddc wceq oveq1i a1i wcel cmin subcld mulcld binom2
      recnd eqeltrid syl2anc sqmuld mul4r syl22anc oveq2d oveq12d 3eqtrd ) ADPQ
      RZECSRZFBSRZUARZPQRZUTPQRZPUTVASRZSRZUARZVAPQRZUARZEPQRCPQRSRZPEBSRFCSRSR
      ZSRZUARZFPQRBPQRSRZUARUSVCUBADVBPQOUCUDAUTTUEVATUEVCVIUBAECAEGBUFRTMAGBAG
      KUJABIUJZUGUKZACJUJZUHAFBAFCHUFRTNACHVQAHLUJUGUKZVOUHUTVAUIULAVGVMVHVNUAA
      VDVJVFVLUAAECVPVQUMAVEVKPSAETUECTUEFTUEBTUEVEVKUBVPVQVRVOECFBUNUOUPUQAFBV
      RVOUMUQUR $.

    2itscp.r $e |- ( ph -> R e. RR ) $.
    ${
      2itscplem3.q $e |- Q = ( ( E ^ 2 ) + ( D ^ 2 ) ) $.
      2itscplem3.s $e |- S = ( ( ( R ^ 2 ) x. Q ) - ( C ^ 2 ) ) $.
      $( Lemma D for ~ 2itscp .  (Contributed by AV, 4-Mar-2023.) $)
      2itscplem3 $p |-
                 ( ph -> S = ( ( ( ( E ^ 2 ) x. ( ( R ^ 2 ) - ( A ^ 2 ) ) )
                                 + ( ( D ^ 2 ) x. ( ( R ^ 2 ) - ( B ^ 2 ) ) ) )
                               - ( 2 x. ( ( D x. A ) x. ( E x. B ) ) ) ) ) $=
        ( c2 cexp co cmul cmin caddc wceq oveq2d recnd sqcld cc subcld eqeltrid
        a1i addcld mulcomd adddird 3eqtrd 2itscplem2 oveq12d mulcld 2cnd eqcomd
        subsub4d oveq1d sub32d eqtrd addsubassd subdid addsubd 3eqtr3d ) AHGUBU
        CUDZFUEUDZDUBUCUDZUFUDZIUBUCUDZVMUEUDZEUBUCUDZVMUEUDZUGUDZVSCUBUCUDZUEU
        DZUBEBUEUDZICUEUDZUEUDZUEUDZUGUDZVQBUBUCUDZUEUDZUGUDZUFUDZVQVMWIUFUDUEU
        DZVSVMWBUFUDZUEUDZUGUDZWGUFUDZHVPUHAUAUOAVNWAVOWKUFAVNVMVQVSUGUDZUEUDWR
        VMUEUDWAAFWRVMUEFWRUHATUOUIAVMWRAGAGSUJUKZAVQVSAIAICKUFUDULQACKACMUJZAK
        OUJUMUNZUKZAEAEJBUFUDULPAJBAJNUJABLUJZUMUNZUKZUPUQAVQVSVMXBXEWSURUSABCD
        EIJKLMNOPQRUTVAAWAWHUFUDZWJUFUDZWAWCUFUDZWJUFUDZWGUFUDZWLWQAXGXHWGUFUDZ
        WJUFUDXJAXFXKWJUFAXKXFAWAWCWGAVRVTAVQVMXBWSVBZAVSVMXEWSVBZUPZAVSWBXEACW
        TUKZVBZAUBWFAVCAWDWEAEBXDXCVBAICXAWTVBVBVBZVEVDVFAXHWGWJAWAWCXNXPUMXQAV
        QWIXBABXCUKZVBZVGVHAWAWHWJXNAWCWGXPXQUPXSVEAXIWPWGUFAXIVRWOUGUDZWJUFUDV
        RWJUFUDZWOUGUDWPAXHXTWJUFAXHVRVTWCUFUDZUGUDXTAVRVTWCXLXMXPVIAYBWOVRUGAW
        OYBAVSVMWBXEWSXOVJVDUIVHVFAVRWOWJXLAVSWNXEAVMWBWSXOUMVBXSVKAYAWMWOUGAWM
        YAAVQVMWIXBWSXRVJVDVFUSVFVLUS $.
    $}

    2itscp.l $e |- ( ph -> ( ( A ^ 2 ) + ( B ^ 2 ) ) < ( R ^ 2 ) ) $.
    ${
      2itscp.n $e |- ( ph -> ( B =/= Y \/ A =/= X ) ) $.
      2itscp.q $e |- Q = ( ( E ^ 2 ) + ( D ^ 2 ) ) $.
      2itscp.s $e |- S = ( ( ( R ^ 2 ) x. Q ) - ( C ^ 2 ) ) $.
      $( A condition for a quadratic equation with real coefficients (for the
         intersection points of a line with a circle) to have (exactly) two
         different real solutions.  (Contributed by AV, 5-Mar-2023.)  (Revised
         by AV, 16-May-2023.) $)
      2itscp $p |- ( ph -> 0 < S ) $=
        ( cc0 c2 cexp co cmin cmul caddc clt wbr wne wa wcel recnd adantr simpr
        cc subne0d necomd neeq1i anbi12i 2re resubcld eqeltrid remulcld resqcld
        ex a1i readdcld cle sqge0d 2itscplem1 breqtrrd subge0d mpbid crp sqn0rp
        cr simpl syl2an ltaddsub2d ltmul2dd ltaddsubd lt2addd lelttrd biimtrrid
        syl2and imp wn wceq eqcom subeq0ad biimprd biimtrid eqeq1i 0red mulge0d
        simprl syl2an2r oveq1 adantl mul02d sylan9eqr oveq1d eqtrd oveq2d 2t0e0
        nne eqtrdi addridd 3brtr4d simprr addcomd eqbrtrd mulcld mul01d addlidd
        sq0i wo ioran pm2.24d 4casesdan posdifd 2itscplem3 ) AUDIUEUFUGZGUEUFUG
        ZBUEUFUGZUHUGZUIUGZEUEUFUGZYHCUEUFUGZUHUGZUIUGZUJUGZUEEBUIUGZICUIUGZUIU
        GZUIUGZUHUGZHUKAYTYPUKULZUDUUAUKULACKUMZBJUMZUUBAUUCUUDUNUUBAUUCCKUHUGZ
        UDUMZUUDJBUHUGZUDUMZUUBAUUCUUFAUUCUNCKACUSUOUUCACMUPZUQAKUSUOUUCAKOUPZU
        QAUUCURUTVIZAUUDUUHAUUDUNZJBAJUSUOUUDAJNUPZUQABUSUOZUUDABLUPZUQUULBJAUU
        DURVAUTVIZUUFUUHUNIUDUMZEUDUMZUNZAUUBUUQUUFUURUUHIUUEUDQVBZEUUGUDPVBZVC
        AUUSUUBAUUSUNZYTYGYMUIUGZYLYIUIUGZUJUGZYPAYTVTUOUUSAUEYSUEVTUOAVDVJAYQY
        RAEBAEUUGVTPAJBNLVEVFZLVGZAICAIUUEVTQACKMOVEVFZMVGZVGVGZUQAUVEVTUOUUSAU
        VCUVDAYGYMAIUVHVHZACMVHZVGZAYLYIAEUVFVHZABLVHZVGZVKZUQAYPVTUOUUSAYKYOAY
        GYJUVKAYHYIAGSVHZUVOVEZVGZAYLYNUVNAYHYMUVRUVLVEZVGZVKZUQAYTUVEVLULZUUSA
        UDUVEYTUHUGZVLULUWDAUDYQYRUHUGZUEUFUGUWEVLAUWFAYQYRUVGUVIVEVMABCEIJKLMN
        OPQVNVOAUVEYTUVQUVJVPVQUQUVBUVCUVDYKYOAUVCVTUOZUUSUVMUQAUVDVTUOZUUSUVPU
        QAYKVTUOZUUSUVTUQAYOVTUOZUUSUWBUQUVBYMYJYGAYMVTUOZUUSUVLUQAYJVTUOZUUSUV
        SUQAIVTUOZUUQYGVRUOZUUSUVHUUQUURWAIVSZWBAYMYJUKULZUUSAYIYMUJUGZYHUKULZU
        WPTAYIYMYHUVOUVLUVRWCVQZUQWDUVBYIYNYLAYIVTUOZUUSUVOUQAYNVTUOZUUSUWAUQAE
        VTUOZUURYLVRUOZUUSUVFUUQUURUREVSZWBAYIYNUKULZUUSAUWRUXETAYIYMYHUVOUVLUV
        RWEVQUQWDWFWGVIWHWIWJAUUCUUDWKZUNUUBAUUCUUFUXFUUGUDWLZUUBUUKUXFBJWLZAUX
        GBJXJUXHJBWLZAUXGBJWMAUXGUXIAJBUUMUUOWNWOWPWPUUFUXGUNUUQEUDWLZUNZAUUBUU
        QUUFUXJUXGUUTEUUGUDPWQVCAUXKUUBAUXKUNZUDYKYTYPUKUXLUDUVCYKUXLWRAUWGUXKU
        VMUQAUWIUXKUVTUQAUDUVCVLULUXKAYGYMUVKUVLAIUVHVMACMVMWSUQUXLYMYJYGAUWKUX
        KUVLUQAUWLUXKUVSUQAUWMUXKUUQUWNUVHAUUQUXJWTUWOXAAUWPUXKUWSUQWDWGUXLYTUE
        UDUIUGZUDUXLYSUDUEUIUXLYSUDYRUIUGZUDUXLYQUDYRUIUXKAYQUDBUIUGZUDUXJYQUXO
        WLUUQEUDBUIXBXCABUUOXDXEXFAUXNUDWLUXKAYRAYRUVIUPXDUQXGXHXIXKUXLYPYKUDUJ
        UGZYKUXLYOUDYKUJUXLYOUDYNUIUGZUDUXLYLUDYNUIUXKYLUDWLZAUXJUXRUUQEXTXCXCX
        FAUXQUDWLUXKAYNAYNUWAUPXDUQXGXHAUXPYKWLUXKAYKAYKUVTUPXLUQXGXMVIWHWIWJAU
        UCWKZUUDUNUUBAUXSUUEUDWLZUUDUUHUUBUXSCKWLZAUXTCKXJAUXTUYAACKUUIUUJWNWOW
        PUUPUXTUUHUNIUDWLZUURUNZAUUBUYBUXTUURUUHIUUEUDQWQUVAVCAUYCUUBAUYCUNZUDY
        OYTYPUKUYDUDUVDYOUYDWRAUWHUYCUVPUQAUWJUYCUWBUQAUDUVDVLULUYCAYLYIUVNUVOA
        EUVFVMABLVMWSUQUYDYIYNYLAUWTUYCUVOUQAUXAUYCUWAUQAUXBUYCUURUXCUVFAUYBUUR
        XNUXDXAAUXEUYCAYMYIUJUGZYHUKULUXEAUYEUWQYHUKAYMYIAYMUVLUPAYIUVOUPXOTXPA
        YMYIYHUVLUVOUVRWCVQUQWDWGUYDYTUXMUDUYDYSUDUEUIUYDYSYQUDUIUGUDUYDYRUDYQU
        IUYCAYRUDCUIUGZUDUYBYRUYFWLUURIUDCUIXBUQACUUIXDXEXHUYDYQUYDEBUYDEAUXBUY
        CUVFUQUPAUUNUYCUUOUQXQXRXGXHXIXKUYDYPUDYOUJUGZYOUYDYKUDYOUJUYDYKUDYJUIU
        GZUDUYDYGUDYJUIUYCYGUDWLZAUYBUYIUURIXTUQXCXFAUYHUDWLUYCAYJAYJUVSUPXDUQX
        GXFAUYGYOWLUYCAYOAYOUWBUPXSUQXGXMVIWHWIWJAUXSUXFUNZUUBUYJUUCUUDYAZWKAUU
        BUUCUUDYBAUYKUUBUAYCWHWJYDAYTYPUVJUWCYEVQABCDEFGHIJKLMNOPQRSUBUCYFVO $.
    $}

    itscnhlinecirc02plem1.n $e |- ( ph -> B =/= Y ) $.
    $( Lemma 1 for ~ itscnhlinecirc02p .  (Contributed by AV, 6-Mar-2023.) $)
    itscnhlinecirc02plem1 $p |- ( ph -> 0 < ( ( -u ( 2 x. ( D x. C ) ) ^ 2 )
                                           - ( 4 x. ( ( ( E ^ 2 ) + ( D ^ 2 ) )
                       x. ( ( C ^ 2 ) - ( ( E ^ 2 ) x. ( R ^ 2 ) ) ) ) ) ) ) $=
      ( co cc0 c4 c2 cexp cmul caddc cmin cneg clt cr 4re a1i resubcld eqeltrid
      wcel resqcld remulcld readdcld wbr 4pos wceq recnd subne0d eqnetrd sqgt0d
      wne orcd eqid 2itscp adddird addcld mulcomd eqtr3d oveq1d breqtrrd mul12d
      mulgt0d oveq2d mulcld adddid eqtr4d subdid sqcld mulsubaddmulsub syl22anc
      cc 4cn subcld breqtrd 2cnd sqneg syl sqmuld sq2 oveq12d 3eqtrd ) AUAUBEUC
      UDTZDUCUDTZUETZUETZUBGUCUDTZWQUFTZWRXAFUCUDTZUETZUGTZUETZUETZUGTZUCEDUETZ
      UETZUHUCUDTZXGUGTUIAUAUBWSXFUGTZUETXHUIAUBXLUBUJUOAUKULAWSXFAWQWRAEAEHBUG
      TUJNAHBLJUMUNZUPZADADECUETZGBUETZUFTUJPAXOXPAECXMKUQAGBAGCIUGTZUJOACIKMUM
      UNZJUQURUNZUPZUQAXBXEAXAWQAGXRUPZXNURAWRXDXTAXAXCYAAFQUPZUQZUMUQUMUAUBUIU
      SAUTULAUAXAXDUETZWQXDUETZUFTZXAWRUETZUGTZXLUIAUAXAXDWQXCUETZUFTZWRUGTZUET
      ZYHUIAXAYKYAAYJWRAXDYIYCAWQXCXNYBUQURXTUMAGXRAGXQUAGXQVAAOULACIACKVBAIMVB
      SVCVDVEAUAXCXBUETZWRUGTZYKUIABCDEXBFYNGHIJKLMNOPQRACIVFBHVFSVGXBVHYNVHVIA
      YJYMWRUGAXBXCUETYJYMAXAWQXCAXAYAVBZAWQXNVBZAXCYBVBZVJAXBXCAXAWQYOYPVKYQVL
      VMVNVOVQAYHXAYJUETZYGUGTYLAYFYRYGUGAYFYDXAYIUETZUFTYRAYEYSYDUFAWQXAXCYPYO
      YQVPVRAXAXDYIYOAXAXCYOYQVSZAWQXCYPYQVSZVTWAVNAXAYJWRYOAXDYIYTUUAVKAWRXTVB
      ZWBWAVOAXAWFUOWQWFUOWRWFUOXDWFUOXLYHVAAGAGXRVBWCZAEAEXMVBZWCZUUBAXDYCVBXA
      WQWRXDWDWEVOVQAUBWSXFUBWFUOAWGULAWQWRUUEADADXSVBZWCZVSAXBXEAXAWQUUCUUEVKA
      WRXDUUGAXAXCUUCAFAFQVBWCVSWHVSWBWIAXKWTXGUGAXKXJUCUDTZUCUCUDTZXIUCUDTZUET
      WTAXJWFUOXKUUHVAAUCXIAWJZAEDUUDUUFVSZVSXJWKWLAUCXIUUKUULWMAUUIUBUUJWSUEUU
      IUBVAAWNULAEDUUDUUFWMWOWPVNVO $.
  $}

  ${
    itscnhlinecirc02plem2.d $e |- D = ( X - A ) $.
    itscnhlinecirc02plem2.e $e |- E = ( B - Y ) $.
    itscnhlinecirc02plem2.c $e |- C = ( ( B x. X ) - ( A x. Y ) ) $.
    $( Lemma 2 for ~ itscnhlinecirc02p .  (Contributed by AV, 10-Mar-2023.) $)
    itscnhlinecirc02plem2 $p |- ( ( ( ( A e. RR /\ B e. RR )
                                      /\ ( X e. RR /\ Y e. RR ) /\ B =/= Y )
                     /\ ( R e. RR /\ ( ( A ^ 2 ) + ( B ^ 2 ) ) < ( R ^ 2 ) ) )
  -> 0 < ( ( -u ( 2 x. ( D x. C ) ) ^ 2 )
           - ( 4 x. ( ( ( E ^ 2 ) + ( D ^ 2 ) )
                       x. ( ( C ^ 2 ) - ( ( E ^ 2 ) x. ( R ^ 2 ) ) ) ) ) ) ) $=
      ( cr wcel wa c2 cexp co caddc cmul cmin wne w3a clt wbr cneg simpl1l eqid
      cc0 c4 simpl1r simpl2l simpl2r simprl simprr simpl3 itscnhlinecirc02plem1
      simplr mulcomd simpll oveq12d subdird oveq1d oveq2d mulcld npncand 3eqtrd
      wceq recnd eqtr4d oveq1i oveq12i 3eqtr4g negeqd 3adant3 adantr breqtrrd )
      ALMZBLMZNZGLMZHLMZNZBHUAZUBZELMZAOPQBOPQRQEOPQZUCUDZNZNZUHODDBSQZFASQZRQZ
      SQZSQZUEZOPQZUIFOPQZDOPQRQZWLOPQZWQWFSQZTQZSQZSQZTQZODCSQZSQZUEZOPQZUIWRC
      OPQZWTTQZSQZSQZTQZUCWIABWLDEFGHVQVRWBWCWHUFVQVRWBWCWHUJVTWAVSWCWHUKVTWAVS
      WCWHULIJWLUGWDWEWGUMWDWEWGUNVSWBWCWHUOUPWDXMXDVGZWHVSWBXNWCVSWBNZXHWPXLXC
      TXOXGWOOPXOXFWNXOXEWMOSXOCWLDSXOBGSQZAHSQZTQZGATQZBSQZBHTQZASQZRQZCWLXOXR
      GBSQZHASQZTQZYCXOXPYDXQYETXOBGXOBVQVRWBUQVHZXOGVSVTWAUMVHZURXOAHXOAVQVRWB
      USVHZXOHVSVTWAUNVHZURUTXOYCYDABSQZTQZBASQZYETQZRQYLYKYETQZRQYFXOXTYLYBYNR
      XOGABYHYIYGVAXOBHAYGYJYIVAUTXOYNYOYLRXOYMYKYETXOBAYGYIURVBVCXOYDYKYEXOGBY
      HYGVDXOABYIYGVDXOHAYJYIVDVEVFVIKWJXTWKYBRDXSBSIVJFYAASJVJVKVLZVCVCVMVBXOX
      KXBUISXOXJXAWRSXOXIWSWTTXOCWLOPYPVBVBVCVCUTVNVOVP $.
  $}

  ${
    itscnhlinecirc02p.i $e |- I = { 1 , 2 } $.
    itscnhlinecirc02p.e $e |- E = ( RR^ ` I ) $.
    itscnhlinecirc02p.p $e |- P = ( RR ^m I ) $.
    itscnhlinecirc02p.s $e |- S = ( Sphere ` E ) $.
    itscnhlinecirc02p.0 $e |- .0. = ( I X. { 0 } ) $.
    itscnhlinecirc02p.l $e |- L = ( LineM ` E ) $.
    itscnhlinecirc02p.d $e |- D = ( dist ` E ) $.
    $( Lemma 3 for ~ itscnhlinecirc02p .  (Contributed by AV, 10-Mar-2023.) $)
    itscnhlinecirc02plem3 $p |- ( ( ( X e. P /\ Y e. P
                                    /\ ( X ` 2 ) =/= ( Y ` 2 ) )
                                  /\ ( R e. RR+ /\ ( X D .0. ) < R ) )
                  -> 0 < ( ( -u ( 2 x. ( ( ( Y ` 1 ) - ( X ` 1 ) )
                                    x. ( ( ( X ` 2 ) x. ( Y ` 1 ) )
                                      - ( ( X ` 1 ) x. ( Y ` 2 ) ) ) ) ) ^ 2 )
                           - ( 4 x. ( ( ( ( ( X ` 2 ) - ( Y ` 2 ) ) ^ 2 )
                                        + ( ( ( Y ` 1 ) - ( X ` 1 ) ) ^ 2 ) )
                               x. ( ( ( ( ( X ` 2 ) x. ( Y ` 1 ) )
                                      - ( ( X ` 1 ) x. ( Y ` 2 ) ) ) ^ 2 )
                                    - ( ( ( ( X ` 2 ) - ( Y ` 2 ) ) ^ 2 )
                                        x. ( R ^ 2 ) ) ) ) ) ) ) $=
      ( wcel c2 co cfv wne w3a crp clt wbr wa c1 cr cexp caddc cc0 cmin cmul c4
      cneg rrx2pxel rrx2pyel 3ad2ant1 adantr 3ad2ant2 simpl3 rpre adantl simpl1
      jca csqrt wceq crrx cehl cfz cn0 2nn0 eqid ehlval ax-mp cpr fz12pr eqtr4i
      fveq2i eqtri oveq2i csn cxp xpeq1i ehl2eudisval0 syl breq1d rpge0 sqrtsqd
      cmap eqcomd breq2d biimpa resqcld sqge0d addge0d sqrtltd mpbird ex sylbid
      readdcld impr itscnhlinecirc02plem2 syl32anc ) HBRZIBRZSHUAZSIUAZUBZUCZCU
      DRZHJATZCUEUFZUGZUGUHHUAZUIRZXHUIRZUGZUHIUAZUIRZXIUIRZUGZXJCUIRZXPSUJTZXH
      SUJTZUKTZCSUJTZUEUFZULSXTXPUMTZXHXTUNTXPXIUNTUMTZUNTUNTUPSUJTUOXHXIUMTZSU
      JTZYJSUJTUKTYKSUJTYMYHUNTUMTUNTUNTUMTUEUFXKXSXOXFXGXSXJXFXQXRBFHKMUQZBFHK
      MURZVFUSUTXKYCXOXGXFYCXJXGYAYBBFIKMUQBFIKMURVFVAUTXFXGXJXOVBXOYDXKXLYDXNC
      VCZUTVDXKXLXNYIXKXLUGZXNYGVGUAZCUEUFZYIYQXMYRCUEYQXFXMYRVHXFXGXJXLVEZAEHB
      JEFVIUAZSVJUAZLUUBUHSVKTZVIUAZUUASVLRUUBUUDVHVMUUBSUUBVNVOVPUUCFVIUUCUHSV
      QZFVRKVSVTWAVSBUIFWKTUIUUEWKTMFUUEUIWKKWBWAQJFULWCZWDUUEUUFWDOFUUEUUFKWEW
      AWFWGWHYQYSYIYQYSUGZYIYRYHVGUAZUEUFZYQYSUUIYQCUUHYRUEXLCUUHVHXKXLUUHCXLCY
      PCWIWJWLVDWMWNUUGYGYHUUGYEYFUUGXPYQXQYSYQXFXQYTYNWGUTZWOZUUGXHYQXRYSYQXFX
      RYTYOWGUTZWOZXBUUGYEYFUUKUUMUUGXPUUJWPUUGXHUULWPWQUUGCYQYDYSXLYDXKYPVDUTZ
      WOUUGCUUNWPWRWSWTXAXCXPXHYKYJCYLXTXIYJVNYLVNYKVNXDXE $.

    ${
      $d D s x y $.  $d P s y $.  $d R s y $.  $d X s y $.  $d Y s y $.
      $d .0. s y $.  $d E p $.  $d I p $.  $d P p x $.  $d R p x $.
      $d X p x $.  $d .0. p x $.  $d p y $.  $d Y p x $.  $d Z p $.
      itscnhlinecirc02p.z $e |- Z = { <. 1 , x >. , <. 2 , y >. } $.
      $( Intersection of a nonhorizontal line with a circle:  A nonhorizontal
         line passing through a point within a circle around the origin
         intersects the circle at exactly two different points.  (Contributed
         by AV, 28-Jan-2023.) $)
      itscnhlinecirc02p $p |- ( ( ( X e. P /\ Y e. P
                                      /\ ( X ` 2 ) =/= ( Y ` 2 ) )
                                    /\ ( R e. RR+ /\ ( X D .0. ) < R ) )
                       -> E! s e. ~P RR ( ( # ` s ) = 2 /\ A. y e. s E! x e. RR
                                  ( Z e. ( .0. S R ) /\ Z e. ( X L Y ) ) ) ) $=
        ( vp wcel c2 cfv wne w3a crp co clt wbr wa cv chash wceq wreu wral cmin
        cr cpw cexp caddc cmul cneg cc0 itscnhlinecirc02plem3 rrx2pyel 3ad2ant1
        c1 c4 adantr 3ad2ant2 resubcld resqcld rrx2pxel readdcld subne0d sqgt0d
        recnd simp3 sqge0d addgtge0d gt0ne0d 2re remulcld renegcld adantl eqidd
        a1i rpre requad2 mpbird crab cpnf cico cxr 0xr pnfxr rpge0 ltpnf elicod
        rpxr syl eqid 2sphere0 eleq2d fveq1 cop cpr fveq1i 1ne2 1ex fvpr1 ax-mp
        vex eqtri eqtrd oveq1d 2ex fvpr2 oveq12d eqeq1d elrab bitrd simp1 simp2
        wb wi necon3d ex 3jca oveq2d reubidva biantrurd bicomd expcom ad3antrrr
        anbi12d imp 3imp rrx2linest2 elelpwi prelrrx2 ancoms eleq1i jca simplrl
        sylibr itsclquadeu ralbidva pm5.32da ) JDUDZKDUDZUEJUFZUEKUFZUGZUHZEUIU
        DZJLCUJEUKULZUMZUMZNUNZUOUFUEUPZMLEFUJZUDZMJKIUJZUDZUMZAUTUQZBUVCURZUMZ
        NUTVAZUQUVDUUOUUPUSUJZUEVBUJZVJKUFZVJJUFZUSUJZUEVBUJZVCUJZBUNZUEVBUJZVD
        UJUEUVRUUOUVPVDUJZUVQUUPVDUJZUSUJZVDUJZVDUJZVEZUWAVDUJUWEUEVBUJZUVOEUEV
        BUJZVDUJZUSUJZVCUJVCUJVFUPZBUVCURZUMZNUVMUQZUVBUWPVFUWHUEVBUJVKUVTUWLVD
        UJVDUJUSUJZUKULCDEFGHIJKLOPQRSTUAVGUVBBUVTUWHUWLUWQNUVBUVOUVSUVBUVNUVBU
        UOUUPUURUUOUTUDZUVAUUMUUNUWRUUQDHJOQVHVIZVLZUURUUPUTUDZUVAUUNUUMUXAUUQD
        HKOQVHVMZVLZVNVOZUVBUVRUVBUVPUVQUURUVPUTUDZUVAUUNUUMUXEUUQDHKOQVPVMZVLZ
        UURUVQUTUDZUVAUUMUUNUXHUUQDHJOQVPVIZVLZVNZVOVQUURUVTVFUGUVAUURUVTUURUVO
        UVSUURUVNUURUUOUUPUWSUXBVNZVOUURUVRUURUVPUVQUXFUXIVNZVOUURUVNUXLUURUUOU
        UPUURUUOUWSVTUURUUPUXBVTUUMUUNUUQWAVRZVSUURUVRUXMWBWCWDVLUVBUWGUVBUEUWF
        UEUTUDUVBWEWJUVBUVRUWEUXKUVBUWCUWDUVBUUOUVPUWTUXGWFUVBUVQUUPUXJUXCWFVNZ
        WFWFWGUVBUWIUWKUVBUWEUXOVOUVBUVOUWJUXDUVBEUVAEUTUDZUURUUSUXPUUTEWKZVLWH
        VOWFVNUVBUWQWIWLWMUVBUVLUWONUVMUVBUVCUVMUDZUMZUVDUVKUWNUXSUVDUMZUVJUWMB
        UVCUXTUWAUVCUDZUMZUVJMDUDZAUNZUEVBUJZUWBVCUJZUWJUPZUMZUYCUVNUYDVDUJZUVR
        UWAVDUJZVCUJZUWEUPZUMZUMZAUTUQZUWMUYBUVIUYNAUTUYBUYDUTUDZUMZUVFUYHUVHUY
        MUYQUVFMVJUCUNZUFZUEVBUJZUEUYRUFZUEVBUJZVCUJZUWJUPZUCDWNZUDZUYHUYQUVEVU
        EMUYBUVEVUEUPZUYPUXTVUGUYAUXSVUGUVDUVBVUGUXRUVAVUGUURUUSVUGUUTUUSEVFWOW
        PUJUDVUGUUSVFWOEVFWQUDUUSWRWJWOWQUDUUSWSWJEXCEWTUUSUXPEWOUKULUXQEXAXDXB
        VUEDEFGHLUCOPQRSVUEXEXFXDVLWHVLVLVLVLXGVUFUYHYHUYQVUDUYGUCMDUYRMUPZVUCU
        YFUWJVUHUYTUYEVUBUWBVCVUHUYSUYDUEVBVUHUYSVJMUFZUYDVJUYRMXHVUIUYDUPVUHVU
        IVJVJUYDXIUEUWAXIXJZUFZUYDVJMVUJUBXKVJUEUGZVUKUYDUPXLVJUEUYDUWAXMAXPXNX
        OXQWJXRZXSVUHVUAUWAUEVBVUHVUAUEMUFZUWAUEUYRMXHVUNUWAUPVUHVUNUEVUJUFZUWA
        UEMVUJUBXKVULVUOUWAUPXLVJUEUYDUWAXTBXPYAXOXQWJXRZXSYBYCYDWJYEUYQUVHMUVN
        UYSVDUJZUVRVUAVDUJZVCUJZUWEUPZUCDWNZUDZUYMUYQUVGVVAMUYQUUMUUNJKUGZUHZUV
        GVVAUPUYBVVDUYPUXTVVDUYAUXSVVDUVDUVBVVDUXRUURVVDUVAUURUUMUUNVVCUUMUUNUU
        QYFUUMUUNUUQYGUUMUUNUUQVVCUUMUUNUUQVVCYIUUMUUNUMZJKUUOUUPJKUPUUOUUPUPYI
        VVEUEJKXHWJYJYKUUAYLVLVLVLVLVLUVNUVRUWEDGHIJKUCOPQTUVNXEUVRXEUWEXEUUBXD
        XGVVBUYMYHUYQVUTUYLUCMDVUHVUSUYKUWEVUHVUQUYIVURUYJVCVUHUYSUYDUVNVDVUMYM
        VUHVUAUWAUVRVDVUPYMYBYCYDWJYEYSYNUYBUYOUYGUYLUMZAUTUQZUWMUXTUYAUYOVVGYH
        ZUXSUYAVVHYIZUVDUXRVVIUVBUYAUXRVVHUYAUXRUMUWAUTUDZVVHUWAUVCUTUUCZVVJUYN
        VVFAUTVVJUYPUMZUYHUYGUYMUYLVVLUYGUYHVVLUYCUYGVVLVUJDUDZUYCUYPVVJVVMUYDU
        WADHOQUUDUUEMVUJDUBUUFUUIZYOYPVVLUYLUYMVVLUYCUYLVVNYOYPYSYNXDYQWHVLYTUY
        BUVNUTUDZUVNVFUGZUMZUVRUTUDZUWEUTUDZUHZUUSVVJUHVVGUWMYHUYBVVTUUSVVJUYBV
        VQVVRVVSUVBVVQUXRUVDUYAUURVVQUVAUURVVOVVPUXLUXNUUGVLYRUYBUVPUVQUVBUXEUX
        RUVDUYAUXGYRZUVBUXHUXRUVDUYAUXJYRZVNUYBUWCUWDUYBUUOUVPUVBUWRUXRUVDUYAUW
        TYRVWAWFUYBUVQUUPVWBUVBUXAUXRUVDUYAUXCYRWFVNYLUXTUUSUYAUXSUUSUVDUURUUSU
        UTUXRUUHVLVLUXTUYAVVJUXSUYAVVJYIZUVDUXRVWCUVBUYAUXRVVJVVKYQWHVLYTYLAUVN
        UVRUWEUVTEUWHUWLUWAUVTXEUWHXEUWLXEUUJXDYEYEUUKUULYNWM $.
    $}
  $}

  ${
    $d L a b $.  $d P a b $.  $d R a b $.  $d S a b $.  $d X a b $.
    $d Y a b $.  $d .0. a b $.
    inlinecirc02p.i $e |- I = { 1 , 2 } $.
    inlinecirc02p.e $e |- E = ( RR^ ` I ) $.
    inlinecirc02p.p $e |- P = ( RR ^m I ) $.
    inlinecirc02p.s $e |- S = ( Sphere ` E ) $.
    inlinecirc02p.0 $e |- .0. = ( I X. { 0 } ) $.
    inlinecirc02p.l $e |- L = ( LineM ` E ) $.
    ${
      $d A a b $.  $d B a b $.  $d C a b $.  $d D a b $.  $d Q a b $.
      inlinecirc02plem.q $e |- Q = ( ( A ^ 2 ) + ( B ^ 2 ) ) $.
      inlinecirc02plem.d $e |- D = ( ( ( R ^ 2 ) x. Q ) - ( C ^ 2 ) ) $.
      inlinecirc02plem.a $e |- A = ( ( X ` 2 ) - ( Y ` 2 ) ) $.
      inlinecirc02plem.b $e |- B = ( ( Y ` 1 ) - ( X ` 1 ) ) $.
      inlinecirc02plem.c $e |- C = ( ( ( X ` 2 ) x. ( Y ` 1 ) )
                                        - ( ( X ` 1 ) x. ( Y ` 2 ) ) ) $.
      $( Lemma for ~ inlinecirc02p .  (Contributed by AV, 7-May-2023.)
         (Revised by AV, 15-May-2023.) $)
      inlinecirc02plem $p |- ( ( ( X e. P /\ Y e. P /\ X =/= Y )
                                    /\ ( R e. RR+ /\ 0 < D ) )
               -> E. a e. P E. b e. P
                  ( ( ( .0. S R ) i^i ( X L Y ) ) = { a , b } /\ a =/= b ) ) $=
        ( wcel wne w3a crp cc0 clt wbr wa c1 cmul csqrt cfv caddc cdiv cop cmin
        co c2 cpr cin wceq cv wrex simprr gt0ne0d cr cle rrx2pyel adantr adantl
        resubcld eqeltrid 3adant3 rrx2pxel remulcld 3jca rpre itsclc0lem3 elrpd
        syl2an rprege0d resum2sqcl syl2anc wo rrx2pnedifcoorneorr resum2sqorgt0
        orcomd syl3anc jca itsclc0lem1 syl311anc itsclc0lem2 prelrrx2 syl simpl
        simprl 0red ltled jca32 itsclinecirc0in cvv opex pm3.2i orcom cc mulcld
        wb recnd sqrtcld addcld div11 addsubeq0 mul0ord wi eqneqall jaod sylbid
        com12 necon3d impancom imp olcd 1ex ovex opthne sylibr 1ne2 orci ex 2ex
        mpbir eqeq2d anbi12d subcld resqrtcld sqrt00 biimpd jctir bitrid necomi
        readdcld eqcom jctil orim12d biimtrid mpd prneimg mpsyl4anc mpdan preq1
        neeq1 preq2 neeq2 rspc2ev ) LEUHZMEUHZLMUIZUJZGUKUHZULDUMUNZUOZUOZUPACU
        QVDZBDURUSZUQVDZUTVDZFVAVDZVBZVEBCUQVDZAUVKUQVDZVCVDZFVAVDZVBZVFZEUHZUP
        UVJUVLVCVDZFVAVDZVBZVEUVPUVQUTVDZFVAVDZVBZVFZEUHZNGHVDLMKVDVGZUWAUWIVFZ
        VHZUWAUWIUIZUOZUJZUWKOVIZPVIZVFZVHZUWQUWRUIZUOZPEVJOEVJUVIDULUIZUWPUVID
        UVEUVFUVGVKZVLUVIUXCUOZUWBUWJUWOUXEUVNVMUHZUVSVMUHZUOZUWBUVIUXHUXCUVIUX
        FUXGUVIAVMUHZBVMUHZCVMUHZDVMUHZULDVNUNZUOZFVMUHZFULUIZUOZUXFUVEUXIUVHUV
        BUVCUXIUVDUVBUVCUOZAVELUSZVEMUSZVCVDVMUEUXRUXSUXTUVBUXSVMUHUVCEJLQSVOVP
        ZUVCUXTVMUHUVBEJMQSVOVQZVRVSZVTZVPZUVEUXJUVHUVBUVCUXJUVDUXRBUPMUSZUPLUS
        ZVCVDVMUFUXRUYFUYGUVCUYFVMUHUVBEJMQSWAVQZUVBUYGVMUHUVCEJLQSWAVPZVRVSZVT
        ZVPZUVEUXKUVHUVBUVCUXKUVDUXRCUXSUYFUQVDZUYGUXTUQVDZVCVDVMUGUXRUYMUYNUXR
        UXSUYFUYAUYHWBUXRUYGUXTUYIUYBWBVRVSZVTVPZUVIDUVIDUVEUXIUXJUXKUJZGVMUHZU
        XLUVHUVBUVCUYQUVDUXRUXIUXJUXKUYCUYJUYOWCVTUVFUYRUVGGWDVPABCDFGUCUDWEWGZ
        UXDWFWHZUVEUXQUVHUVEUXOUXPUVBUVCUXOUVDUXRUXIUXJUXOUYCUYJABFUCWIWJVTZUVE
        FUVEUXIUXJAULUIZBULUIZWKZULFUMUNUYDUYKUVEVUCVUBBAEJLMQSUFUEWLWNZABFUCWM
        WOVLZWPVPZABCDFWQWRUVIUXJUXIUXKUXNUXQUXGUYLUYEUYPUYTVUGBACDFWSWRWPVPUVN
        UVSEJQSWTXAUXEUWDVMUHZUWGVMUHZUOZUWJUVIVUJUXCUVIVUHVUIUVIUXIUXJUXKUXNUX
        QVUHUYEUYLUYPUYTVUGABCDFWSWRUVIUXJUXIUXKUXNUXQVUIUYLUYEUYPUYTVUGBACDFWQ
        WRWPVPUWDUWGEJQSWTXAUXEUWMUWNUXEUVEUVFUXMUOUOZUWMUVIVUKUXCUVIUVEUVFUXMU
        VEUVHXBUVEUVFUVGXCUVIULDUVIXDUYSUXDXEZXFVPABCDEFGHIJKLMNQRSTUAUCUDUBUEU
        FUGXGXAUVOXHUHZUVTXHUHZUWEXHUHZUWHXHUHZUOZUXEUVOUWEUIZUVOUWHUIZUOZUVTUW
        EUIZUVTUWHUIZUOZWKZUWNUPUVNXIVEUVSXIVUOVUPUPUWDXIVEUWGXIXJUXEVUDVVDUVIV
        UDUXCUVEVUDUVHVUEVPVPVUDVUCVUBWKUXEVVDVUBVUCXKUXEVUCVUTVUBVVCUXEVUCVUTU
        XEVUCUOZVURVUSVVEUPUPUIZUVNUWDUIZWKVURVVEVVGVVFUXEVUCVVGUVIVUCUXCVVGUVI
        VUCUOZUVNUWDDULVVHUVNUWDVHZUVMUWCVHZDULVHZVVHUVMXLUHUWCXLUHFXLUHZUXPUOZ
        VVIVVJXNVVHUVJUVLVVHACUVIAXLUHVUCUVIAUYEXOZVPUVICXLUHVUCUVICUYPXOVPXMZV
        VHBUVKUVIBXLUHVUCUVIBUYLXOZVPVVHDUVIDXLUHVUCUVIDUYSXOVPXPXMZXQVVHUVJUVL
        VVOVVQUUAUVIVVMVUCUVIVVLUXPUVIFUVEUXOUVHVUAVPXOUVEUXPUVHVUFVPWPZVPUVMUW
        CFXRWOVVHVVJUVLULVHZVVKVVHUVJXLUHUVLXLUHVVJVVSXNVVOVVQUVJUVLXSWJVVHVVSB
        ULVHZUVKULVHZWKZVVKUVIVVSVWBXNVUCUVIBUVKVVPUVIUVKUVIDUYSVULUUBZXOZXTVPV
        VHVVTVVKVWAVUCVVTVVKYAUVIVVTVUCVVKVVKBULYBYEVQUVIVWAVVKYAZVUCUVIVWAVVKU
        VIUXLUXMVWAVVKXNUYSVULDUUCWJUUDZVPYCYDYDYDYFYGYHYIUPUVNUPUWDYJUVMFVAYKZ
        YLYMVUSUPVEUIZUVNUWGUIZWKVWHVWIYNYOUPUVNVEUWGYJVWGYLYRUUEYPUXEVUBVVCUXE
        VUBUOZVVBVVAVWJVEVEUIZUVSUWGUIZWKVVBVWJVWLVWKUXEVUBVWLUVIVUBUXCVWLUVIVU
        BUOZUVSUWGDULVWMUVSUWGVHZUVRUWFVHZVVKVWMUVRXLUHZUWFXLUHVVMVWNVWOXNUVIVW
        PVUBUVIUVRUVIUVPUVQUVEUVPVMUHZUVHUVBUVCVWQUVDUXRBCUYJUYOWBVTVPZUVIAUVKU
        YEVWCWBZVRXOVPVWMUWFUVIUWFVMUHVUBUVIUVPUVQUVIBCUYLUYPWBVWSUUHVPXOUVIVVM
        VUBVVRVPUVRUWFFXRWOVWMVWOUVQULVHZVVKVWMUVPXLUHZUVQXLUHZUOZVWOVWTXNUVIVX
        CVUBUVIVXAVXBUVIUVPVWRXOUVIUVQVWSXOWPVPVWOUWFUVRVHVXCVWTUVRUWFUUIUVPUVQ
        XSUUFXAVWMVWTAULVHZVWAWKZVVKUVIVWTVXEXNVUBUVIAUVKVVNVWDXTVPVWMVXDVVKVWA
        VUBVXDVVKYAUVIVXDVUBVVKVVKAULYBYEVQUVIVWEVUBVWFVPYCYDYDYDYFYGYHYIVEUVSV
        EUWGYQUVRFVAYKZYLYMVVAVEUPUIZUVSUWDUIZWKVXGVXHUPVEYNUUGYOVEUVSUPUWDYQVX
        FYLYRUUJYPUUKUULUUMVUMVUNUOVUQUOVVDUWNUVOUVTUWEUWHXHXHXHXHUUNYHUUOWPWCU
        UPUXBUWOUWKUWAUWRVFZVHZUWAUWRUIZUOOPUWAUWIEEUWQUWAVHZUWTVXJUXAVXKVXLUWS
        VXIUWKUWQUWAUWRUUQYSUWQUWAUWRUURYTUWRUWIVHZVXJUWMVXKUWNVXMVXIUWLUWKUWRU
        WIUWAUUSYSUWRUWIUWAUUTYTUVAXA $.
    $}

    inlinecirc02p.d $e |- D = ( dist ` E ) $.
    $( Intersection of a line with a circle:  A line passing through a point
       within a circle around the origin intersects the circle at exactly two
       different points.  (Contributed by AV, 9-May-2023.)  (Revised by AV,
       16-May-2023.) $)
    inlinecirc02p $p |- ( ( ( X e. P /\ Y e. P /\ X =/= Y )
                                   /\ ( R e. RR+ /\ ( X D .0. ) < R ) )
                     -> ( ( .0. S R ) i^i ( X L Y ) ) e. ( PrPairs ` P ) ) $=
      ( wcel co c2 va vb wne w3a crp clt wbr wa cvv cin cpr wceq wrex cprpr cfv
      cv cr cmap ovexi a1i cc0 cexp cmin c1 caddc cmul adantl rrx2pxel 3ad2ant1
      simpl adantr rrx2pyel 3ad2ant2 eqid rpre wb crrx cehl cfz cn0 2nn0 ehlval
      ax-mp fz12pr eqtr4i fveq2i eqtri oveq2i csn xpeq1i ehl2eudis0lt 3ad2antl1
      cxp biimpd impr wo rrx2pnecoorneor orcomd 2itscp cc recnd subdird oveq12d
      mulcomd oveq1d mulcld npncand 3adant3 breqtrrd inlinecirc02plem prprelprb
      3eqtrd eqcomd oveq2d syl12anc sylanbrc ) HBRZIBRZHIUCZUDZCUERZHJASCUFUGZU
      HZUHZBUIRZJCDSHIGSUJZUAUPZUBUPZUKULYGYHUCUHUBBUMUABUMZYFBUNUORYEYDBUQFURM
      USUTYDXTYAVACTVBSZTHUOZTIUOZVCSZTVBSVDIUOZVDHUOZVCSZTVBSVESZVFSZYKYNVFSZY
      OYLVFSZVCSZTVBSZVCSZUFUGYIXTYCVJYCYAXTYAYBVJVGYDVAYRYPYKVFSZYMYOVFSZVESZT
      VBSZVCSZUUCUFYDYOYKUUFYPYQCUUHYMYNYLXTYOUQRZYCXQXRUUIXSBFHKMVHZVIVKXTYKUQ
      RZYCXQXRUUKXSBFHKMVLZVIVKXTYNUQRZYCXRXQUUMXSBFIKMVHZVMVKXTYLUQRZYCXRXQUUO
      XSBFIKMVLZVMVKYPVNZYMVNZUUFVNYCCUQRZXTYAUUSYBCVOVKVGXTYAYBYOTVBSYKTVBSVES
      YJUFUGZXTYAUHYBUUTXQXRYAYBUUTVPXSACEHBJEFVQUOZTVRUOZLUVBVDTVSSZVQUOZUVATV
      TRUVBUVDULWAUVBTUVBVNWBWCUVCFVQUVCVDTUKZFWDKWEWFWGWEBUQFURSUQUVEURSMFUVEU
      QURKWHWGQJFVAWIZWMUVEUVFWMOFUVEUVFKWJWGWKWLWNWOXTYKYLUCZYOYNUCZWPYCXTUVHU
      VGBFHIKMWQWRVKYQVNZUUHVNWSYDUUBUUGYRVCYDUUAUUFTVBYDUUFUUAXTUUFUUAULZYCXQX
      RUVJXSXQXRUHZUUFYNYKVFSZYOYKVFSZVCSZYKYOVFSZYLYOVFSZVCSZVESYSUVMVCSZUVMYT
      VCSZVESUUAUVKUUDUVNUUEUVQVEUVKYNYOYKXRYNWTRXQXRYNUUNXAVGZXQYOWTRXRXQYOUUJ
      XAVKZXQYKWTRXRXQYKUULXAVKZXBUVKYKYLYOUWBXRYLWTRXQXRYLUUPXAVGZUWAXBXCUVKUV
      NUVRUVQUVSVEUVKUVLYSUVMVCUVKYNYKUVTUWBXDXEUVKUVOUVMUVPYTVCUVKYKYOUWBUWAXD
      UVKYLYOUWCUWAXDXCXCUVKYSUVMYTUVKYKYNUWBUVTXFUVKYOYKUWAUWBXFUVKYOYLUWAUWCX
      FXGXLXHVKXMXEXNXIYMYPUUAUUCBYQCDEFGHIJUAUBKLMNOPUVIUUCVNUURUUQUUAVNXJXOYF
      BUAUBXKXP $.

    $d L p $.  $d P p $.  $d R p $.  $d S p $.  $d X p $.  $d Y p $.
    $d .0. p $.
    $( Intersection of a line with a circle:  A line passing through a point
       within a circle around the origin intersects the circle at exactly two
       different points, expressed with restricted uniqueness (and without the
       definition of proper pairs).  (Contributed by AV, 16-May-2023.) $)
    inlinecirc02preu $p |- ( ( ( X e. P /\ Y e. P /\ X =/= Y )
                                   /\ ( R e. RR+ /\ ( X D .0. ) < R ) )
                  -> E! p e. ~P P ( ( # ` p ) = 2
                                    /\ p = ( ( .0. S R ) i^i ( X L Y ) ) ) ) $=
      ( wcel co wne w3a crp clt wbr wa cv cin wceq cprpr cfv wreu inlinecirc02p
      chash c2 cpw reueq sylib cvv wb cr cmap ovexi prprreueq mp1i mpbid ) HBSI
      BSHIUAUBCUCSHJATCUDUEUFUFZKUGZJCDTHIGTUHZUIZKBUJUKZULZVHUNUKUOUIVJUFKBUPU
      LZVGVIVKSVLABCDEFGHIJLMNOPQRUMKVKVIUQURBUSSVLVMUTVGBVAFVBNVCVJBUSKVDVEVF
      $.
  $}
