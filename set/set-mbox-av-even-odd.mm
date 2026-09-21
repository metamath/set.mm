$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Even and odd numbers
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  Even and odd numbers can be characterized in many different ways.  In the
  following, the definition of even and odd numbers is based on the fact that
  dividing an even number (resp. an odd number increased by 1) by 2 is an
  integer, see ~ df-even and ~ df-odd .  Alternate definitions resp.
  characterizations are provided in ~ dfeven2 , ~ dfeven3 , ~ dfeven4 and in
  ~ dfodd2 , ~ dfodd3 , ~ dfodd4 , ~ dfodd5 , ~ dfodd6 . Each characterization
  can be useful (and used) in an appropriate context, e.g. ~ dfodd6 in
  ~ opoeALTV and ~ dfodd3 in ~ oddprmALTV .  Having a fixed definition for even
  and odd numbers, and alternate characterizations as theorems, advanced
  theorems about even and/or odd numbers can be expressed more explicitly, and
  the appropriate characterization can be chosen for their proof, which may
  become clearer and sometimes also shorter (see, for example, ~ divgcdoddALTV
  and ~ divgcdodd ).

$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Definitions and basic properties
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $c Even Odd $.

  $( Extend the definition of a class to include the set of even numbers. $)
  ceven $a class Even $.

  $( Extend the definition of a class to include the set of odd numbers. $)
  codd $a class Odd $.

  $( Define the set of even numbers.  (Contributed by AV, 14-Jun-2020.) $)
  df-even $a |- Even = { z e. ZZ | ( z / 2 ) e. ZZ } $.

  $( Define the set of odd numbers.  (Contributed by AV, 14-Jun-2020.) $)
  df-odd $a |- Odd = { z e. ZZ | ( ( z + 1 ) / 2 ) e. ZZ } $.

  ${
    $d Z z $.
    $( The predicate "is an even number".  An even number is an integer which
       is divisible by 2, i.e. the result of dividing the even integer by 2 is
       still an integer.  (Contributed by AV, 14-Jun-2020.) $)
    iseven $p |- ( Z e. Even <-> ( Z e. ZZ /\ ( Z / 2 ) e. ZZ ) ) $=
      ( vz cv c2 cdiv co cz wcel ceven wceq oveq1 eleq1d df-even elrab2 ) BCZDE
      FZGHADEFZGHBAGIOAJPQGOADEKLBMN $.

    $( The predicate "is an odd number".  An odd number is an integer which is
       not divisible by 2, i.e. the result of dividing the odd integer
       increased by 1 and then divided by 2 is still an integer.  (Contributed
       by AV, 14-Jun-2020.) $)
    isodd $p |- ( Z e. Odd <-> ( Z e. ZZ /\ ( ( Z + 1 ) / 2 ) e. ZZ ) ) $=
      ( vz cv c1 caddc co c2 cdiv cz wcel codd wceq oveq1d eleq1d df-odd elrab2
      oveq1 ) BCZDEFZGHFZIJADEFZGHFZIJBAIKRALZTUBIUCSUAGHRADEQMNBOP $.
  $}

  $( An even number is an integer.  (Contributed by AV, 14-Jun-2020.) $)
  evenz $p |- ( Z e. Even -> Z e. ZZ ) $=
    ( ceven wcel cz c2 cdiv co iseven simplbi ) ABCADCAEFGDCAHI $.

  $( An odd number is an integer.  (Contributed by AV, 14-Jun-2020.) $)
  oddz $p |- ( Z e. Odd -> Z e. ZZ ) $=
    ( codd wcel cz c1 caddc co c2 cdiv isodd simplbi ) ABCADCAEFGHIGDCAJK $.

  $( The result of dividing an even number by 2 is an integer.  (Contributed by
     AV, 15-Jun-2020.) $)
  evendiv2z $p |- ( Z e. Even -> ( Z / 2 ) e. ZZ ) $=
    ( ceven wcel cz c2 cdiv co iseven simprbi ) ABCADCAEFGDCAHI $.

  $( The result of dividing an odd number increased by 1 and then divided by 2
     is an integer.  (Contributed by AV, 15-Jun-2020.) $)
  oddp1div2z $p |- ( Z e. Odd -> ( ( Z + 1 ) / 2 ) e. ZZ ) $=
    ( codd wcel cz c1 caddc co c2 cdiv isodd simprbi ) ABCADCAEFGHIGDCAJK $.

  $( The result of dividing an odd number decreased by 1 and then divided by 2
     is an integer.  (Contributed by AV, 15-Jun-2020.) $)
  oddm1div2z $p |- ( Z e. Odd -> ( ( Z - 1 ) / 2 ) e. ZZ ) $=
    ( codd wcel c1 caddc co c2 cdiv cz cmin oddp1div2z wb oddz zob syl mpbid )
    ABCZADEFGHFICZADJFGHFICZAKQAICRSLAMANOP $.

  $( The predicate "is an odd number".  An odd number is an integer which is
     not divisible by 2, i.e. the result of dividing the odd number decreased
     by 1 and then divided by 2 is still an integer.  (Contributed by AV,
     15-Jun-2020.) $)
  isodd2 $p |- ( Z e. Odd <-> ( Z e. ZZ /\ ( ( Z - 1 ) / 2 ) e. ZZ ) ) $=
    ( codd wcel cz c1 caddc co c2 cdiv wa cmin isodd zob pm5.32i bitri ) ABCADC
    ZAEFGHIGDCZJPAEKGHIGDCZJALPQRAMNO $.

  ${
    $d x z $.
    $( Alternate definition for odd numbers.  (Contributed by AV,
       15-Jun-2020.) $)
    dfodd2 $p |- Odd = { z e. ZZ | ( ( z - 1 ) / 2 ) e. ZZ } $=
      ( vx codd cv c1 cmin co c2 cdiv cz wcel wa isodd2 weq oveq1 oveq1d eleq1d
      crab elrab bitr4i eqriv ) BCADZEFGZHIGZJKZAJRZBDZCKUGJKUGEFGZHIGZJKZLUGUF
      KUGMUEUJAUGJABNZUDUIJUKUCUHHIUBUGEFOPQSTUA $.
  $}

  ${
    $d i z $.
    $( Alternate definition for odd numbers.  (Contributed by AV,
       18-Jun-2020.) $)
    dfodd6 $p |- Odd = { z e. ZZ | E. i e. ZZ z = ( ( 2 x. i ) + 1 ) } $=
      ( cv c1 cmin co c2 cdiv cz wcel crab cmul caddc wceq wa simpr 2cnd adantr
      cc syl codd wrex dfodd2 weq oveq2 cc0 wne w3a peano2zm zcnd 2ne0 a1i 3jca
      divcan2 sylan9eqr oveq1d zcn npcan1 eqtrd eqeq2d eqidd rspcedvd ex syl2an
      oveq1 mulcl pncan1 adantl divcan3d eqeltrd rexlimdva2 impbid rabbiia
      eqtri ) UAACZDEFZGHFZIJZAIKVOGBCZLFZDMFZNZBIUBZAIKAUCVRWCAIVOIJZVRWCWDVRW
      CWDVROZWBAAUDBVQIWDVRPWEVSVQNZOZWAVOVOWGWAVPDMFZVOWGVTVPDMWFWEVTGVQLFZVPV
      SVQGLUEWEVPSJZGSJZGUFUGZUHZWIVPNWDWMVRWDWJWKWLWDVPVOUIUJWDQZWLWDUKULUMRVP
      GUNTUOUPWEWHVONZWFWDWOVRWDVOSJWOVOUQVOURTRRUSUTWEVOVAVBVCWDWBVRBIWDVSIJZO
      ZWBOZVQVSIWRVQVTGHFZVSWRVPVTGHWBWQVPWADEFZVTVOWADEVEWQVTSJZWTVTNWDWKVSSJZ
      XAWPWNVSUQZGVSVFVDVTVGTUOUPWQWSVSNWBWQVSGWPXBWDXCVHWQQWLWQUKULVIRUSWQWPWB
      WDWPPRVJVKVLVMVN $.

    $( Alternate definition for even numbers.  (Contributed by AV,
       18-Jun-2020.) $)
    dfeven4 $p |- Even = { z e. ZZ | E. i e. ZZ z = ( 2 x. i ) } $=
      ( cv c2 cdiv co cz wcel crab cmul wceq wa simpr adantl cc zcn adantr 2cnd
      2ne0 a1i ceven wrex df-even oveq2 eqeq2d cc0 wne divcan2d eqcomd rspcedvd
      wb ex oveq1 divcan3d sylan9eqr eqeltrd rexlimdva2 impbid rabbiia eqtri )
      UAACZDEFZGHZAGIVADBCZJFZKZBGUBZAGIAUCVCVGAGVAGHZVCVGVHVCVGVHVCLZVFVADVBJF
      ZKZBVBGVHVCMVDVBKZVFVKUKVIVLVEVJVAVDVBDJUDUENVIVJVAVIVADVHVAOHVCVAPQVIRDU
      FUGZVISTUHUIUJULVHVFVCBGVHVDGHZLZVFLVBVDGVFVOVBVEDEFVDVAVEDEUMVOVDDVNVDOH
      VHVDPNVORVMVOSTUNUOVOVNVFVHVNMQUPUQURUSUT $.
  $}

  $( The predecessor of an even number is odd.  (Contributed by AV,
     16-Jun-2020.) $)
  evenm1odd $p |- ( Z e. Even -> ( Z - 1 ) e. Odd ) $=
    ( ceven wcel c1 cmin co cz caddc c2 cdiv codd evenz peano2zm wa iseven wceq
    syl cc zcn npcan1 eqcomd oveq1d eleq1d biimpa sylbi isodd sylanbrc ) ABCZAD
    EFZGCZUIDHFZIJFZGCZUIKCUHAGCZUJALAMQUHUNAIJFZGCZNUMAOUNUPUMUNUOULGUNAUKIJUN
    UKAUNARCUKAPASATQUAUBUCUDUEUIUFUG $.

  $( The successor of an even number is odd.  (Contributed by AV,
     16-Jun-2020.) $)
  evenp1odd $p |- ( Z e. Even -> ( Z + 1 ) e. Odd ) $=
    ( ceven wcel c1 caddc co cz cmin c2 cdiv codd evenz peano2zd wa iseven wceq
    cc zcn pncan1 syl eqcomd oveq1d eleq1d biimpa sylbi isodd2 sylanbrc ) ABCZA
    DEFZGCUIDHFZIJFZGCZUIKCUHAALMUHAGCZAIJFZGCZNULAOUMUOULUMUNUKGUMAUJIJUMUJAUM
    AQCUJAPARASTUAUBUCUDUEUIUFUG $.

  $( The successor of an odd number is even.  (Contributed by AV,
     16-Jun-2020.) $)
  oddp1eveni $p |- ( Z e. Odd -> ( Z + 1 ) e. Even ) $=
    ( codd wcel c1 caddc co cz c2 cdiv oddz peano2zd oddp1div2z iseven sylanbrc
    ceven ) ABCZADEFZGCQHIFGCQOCPAAJKALQMN $.

  $( The predecessor of an odd number is even.  (Contributed by AV,
     6-Jul-2020.) $)
  oddm1eveni $p |- ( Z e. Odd -> ( Z - 1 ) e. Even ) $=
    ( codd wcel c1 cmin co cz c2 cdiv ceven oddz peano2zm syl oddm1div2z iseven
    sylanbrc ) ABCZADEFZGCZRHIFGCRJCQAGCSAKALMANROP $.

  $( An even number is not an odd number.  (Contributed by AV, 16-Jun-2020.) $)
  evennodd $p |- ( Z e. Even -> -. Z e. Odd ) $=
    ( ceven wcel cz wn c1 caddc co c2 cdiv wo codd iseven zeo2 biimpd imp sylbi
    wa olcd isodd notbii ianor bitri sylibr ) ABCZADCZEZAFGHIJHDCZEZKZALCZEZUEU
    IUGUEUFAIJHDCZRUIAMUFUMUIUFUMUIANOPQSULUFUHRZEUJUKUNATUAUFUHUBUCUD $.

  $( An odd number is not an even number.  (Contributed by AV, 16-Jun-2020.) $)
  oddneven $p |- ( Z e. Odd -> -. Z e. Even ) $=
    ( codd wcel cz wn c2 cdiv co wo ceven c1 caddc isodd biimpd con2d imp sylbi
    wa zeo2 olcd ianor iseven xchnxbir sylibr ) ABCZADCZEZAFGHDCZEZIZAJCZEUEUIU
    GUEUFAKLHFGHDCZRUIAMUFULUIUFUHULUFUHULEASNOPQTUFUHRUJUKUFUHUAAUBUCUD $.

  $( The negative of an even number is even.  (Contributed by AV,
     20-Jun-2020.) $)
  enege $p |- ( A e. Even -> -u A e. Even ) $=
    ( cz wcel c2 cdiv co wa cneg ceven znegcl adantr adantl cc cc0 wne w3a 2cnd
    wb zcn iseven 2ne0 a1i 3jca divneg eleq1d syl mpbid jca 3imtr4i ) ABCZADEFZ
    BCZGZAHZBCZUNDEFZBCZGAICUNICUMUOUQUJUOULAJKUMUKHZBCZUQULUSUJUKJLUMAMCZDMCZD
    NOZPZUSUQRUJVCULUJUTVAVBASUJQVBUJUAUBUCKVCURUPBADUDUEUFUGUHATUNTUI $.

  $( The negative of an odd number is odd.  (Contributed by AV,
     20-Jun-2020.) $)
  onego $p |- ( A e. Odd -> -u A e. Odd ) $=
    ( cz wcel c1 cmin co c2 cdiv wa cneg caddc codd znegcl adantr adantl cc cc0
    wne wb eleq1d peano2zm zcnd 2cnd 2ne0 a1i w3a divneg syl3anc mpbid wceq zcn
    1cnd negsubdi eqcomd syl2anc oveq1d mpbird jca isodd2 isodd 3imtr4i ) ABCZA
    DEFZGHFZBCZIZAJZBCZVGDKFZGHFZBCZIALCVGLCVFVHVKVBVHVEAMNVFVKVCJZGHFZBCZVFVDJ
    ZBCZVNVEVPVBVDMOVFVCPCZGPCZGQRZVPVNSVBVQVEVBVCAUAUBNVFUCVSVFUDUEVQVRVSUFVOV
    MBVCGUGTUHUIVBVKVNSVEVBVJVMBVBVIVLGHVBAPCZDPCZVIVLUJAUKVBULVTWAIVLVIADUMUNU
    OUPTNUQURAUSVGUTVA $.

  ${
    $d N i n $.
    $( Exponentiation of -1 by an even power.  (Contributed by Glauco
       Siliprandi, 29-Jun-2017.)  (Revised by AV, 6-Jul-2020.) $)
    m1expevenALTV $p |- ( N e. Even -> ( -u 1 ^ N ) = 1 ) $=
      ( vi vn ceven wcel cz c2 cv cmul co wceq wrex wa c1 eqeq1 rexbidv dfeven4
      cneg cexp a1i elrab2 oveq2 cc cc0 wne neg1cn neg1ne0 2z syl22anc neg1sqe1
      id expmulz oveq1i 1exp eqtrid eqtrd adantl sylan9eqr rexlimdva2 imp sylbi
      ) ADEAFEZAGBHZIJZKZBFLZMNRZASJZNKZCHZVDKZBFLVFCAFDVJAKVKVEBFVJAVDOPCBQUAV
      BVFVIVBVEVIBFVEVBVCFEZMVHVGVDSJZNAVDVGSUBVLVMNKVBVLVMVGGSJZVCSJZNVLVGUCEZ
      VGUDUEZGFEZVLVMVOKVPVLUFTVQVLUGTVRVLUHTVLUKVGGVCULUIVLVONVCSJNVNNVCSUJUMV
      CUNUOUPUQURUSUTVA $.
  $}

  $( Exponentiation of -1 by an odd power.  (Contributed by AV, 6-Jul-2020.) $)
  m1expoddALTV $p |- ( N e. Odd -> ( -u 1 ^ N ) = -u 1 ) $=
    ( codd wcel c1 cneg cexp co cmin caddc cmul cc wceq oddz zcnd npcan1 eqcomd
    syl oveq2d a1i cz cc0 wne neg1ne0 peano2zm expp1zd oddm1eveni m1expevenALTV
    neg1cn ceven oveq1d mullidd eqtrd 3eqtrd ) ABCZDEZAFGUOADHGZDIGZFGUOUPFGZUO
    JGZUOUNAUQUOFUNAKCZAUQLUNAAMZNUTUQAAOPQRUNUOUPUOKCUNUHSZUOUAUBUNUCSUNATCUPT
    CVAAUDQUEUNUSDUOJGUOUNURDUOJUNUPUICURDLAUFUPUGQUJUNUOVBUKULUM $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Alternate definitions using the "divides" relation
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)
  ${
    $d i z $.
    $( Alternate definition for even numbers.  (Contributed by AV,
       18-Jun-2020.) $)
    dfeven2 $p |- Even = { z e. ZZ | 2 || z } $=
      ( vi ceven cv c2 cmul co wceq cz wrex crab cdvds wbr dfeven4 wcel wa 2cnd
      eqcom cc zcn adantl mulcomd eqeq1d bitrid rexbidva wb divides mpan bitr4d
      2z rabbiia eqtri ) CADZEBDZFGZHZBIJZAIKEUMLMZAIKABNUQURAIUMIOZUQUNEFGZUMH
      ZBIJZURUSUPVABIUPUOUMHUSUNIOZPZVAUMUORVDUOUTUMVDEUNVDQVCUNSOUSUNTUAUBUCUD
      UEEIOUSURVBUFUJBEUMUGUHUIUKUL $.

    $( Alternate definition for odd numbers.  (Contributed by AV,
       18-Jun-2020.) $)
    dfodd3 $p |- Odd = { z e. ZZ | -. 2 || z } $=
      ( vi codd cv c2 cmul co c1 caddc wceq cz wrex crab cdvds wbr wn dfodd6 wb
      wcel wa eqcom a1i rexbidva odd2np1 bitr4d rabbiia eqtri ) CADZEBDZFGHIGZJ
      ZBKLZAKMEUHNOPZAKMABQULUMAKUHKSZULUJUHJZBKLUMUNUKUOBKUKUORUNUIKSTUHUJUAUB
      UCBUHUDUEUFUG $.
  $}

  ${
    $d Z z $.
    $( The predicate "is an even number".  An even number is an integer which
       is divisible by 2.  (Contributed by AV, 18-Jun-2020.) $)
    iseven2 $p |- ( Z e. Even <-> ( Z e. ZZ /\ 2 || Z ) ) $=
      ( vz c2 cv cdvds wbr cz ceven breq2 dfeven2 elrab2 ) CBDZEFCAEFBAGHLACEIB
      JK $.

    $( The predicate "is an odd number".  An odd number is an integer which is
       not divisible by 2.  (Contributed by AV, 18-Jun-2020.) $)
    isodd3 $p |- ( Z e. Odd <-> ( Z e. ZZ /\ -. 2 || Z ) ) $=
      ( vz c2 cv cdvds wbr wn cz codd wceq breq2 notbid dfodd3 elrab2 ) CBDZEFZ
      GCAEFZGBAHIOAJPQOACEKLBMN $.
  $}

  $( 2 divides an even number.  (Contributed by AV, 18-Jun-2020.) $)
  2dvdseven $p |- ( Z e. Even -> 2 || Z ) $=
    ( ceven wcel cz c2 cdvds wbr iseven2 simprbi ) ABCADCEAFGAHI $.

  $( A multiple of 2 is an even number.  (Contributed by AV, 5-Jun-2023.) $)
  m2even $p |- ( Z e. ZZ -> ( 2 x. Z ) e. Even ) $=
    ( cz wcel c2 co cdvds wbr ceven 2z a1i id zmulcld dvdsmul1 iseven2 sylanbrc
    cmul mpan ) ABCZDAPEZBCDSFGZSHCRDADBCZRIJRKLUARTIDAMQSNO $.

  $( 2 does not divide an odd number.  (Contributed by AV, 18-Jun-2020.) $)
  2ndvdsodd $p |- ( Z e. Odd -> -. 2 || Z ) $=
    ( codd wcel cz c2 cdvds wbr wn isodd3 simprbi ) ABCADCEAFGHAIJ $.

  $( 2 divides an odd number increased by 1.  (Contributed by AV,
     18-Jun-2020.) $)
  2dvdsoddp1 $p |- ( Z e. Odd -> 2 || ( Z + 1 ) ) $=
    ( codd wcel c2 cdvds wbr wn c1 caddc co 2ndvdsodd cz wb oddp1even syl mpbid
    oddz ) ABCZDAEFGZDAHIJEFZAKRALCSTMAQANOP $.

  $( 2 divides an odd number decreased by 1.  (Contributed by AV,
     18-Jun-2020.) $)
  2dvdsoddm1 $p |- ( Z e. Odd -> 2 || ( Z - 1 ) ) $=
    ( codd wcel c2 cdvds wbr wn c1 cmin co 2ndvdsodd cz wb oddz oddm1even mpbid
    syl ) ABCZDAEFGZDAHIJEFZAKRALCSTMANAOQP $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Alternate definitions using the "modulo" operation
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( Alternate definition for even numbers.  (Contributed by AV,
     18-Jun-2020.) $)
  dfeven3 $p |- Even = { z e. ZZ | ( z mod 2 ) = 0 } $=
    ( ceven cv c2 cdiv co cz wcel crab cmo cc0 wceq df-even cr crp zre 2rp mod0
    wb sylancl bicomd rabbiia eqtri ) BACZDEFGHZAGIUDDJFKLZAGIAMUEUFAGUDGHZUFUE
    UGUDNHDOHUFUESUDPQUDDRTUAUBUC $.

  $( Alternate definition for odd numbers.  (Contributed by AV,
     18-Jun-2020.) $)
  dfodd4 $p |- Odd = { z e. ZZ | ( z mod 2 ) = 1 } $=
    ( codd cv c1 cmin co c2 cdiv cz wcel crab cmo dfodd2 cc0 cr crp wb peano2zm
    wceq a1i zred 2rp sylancl clt wbr zre 2re m1mod0mod1 syl3anc bitr3d rabbiia
    mod0 1lt2 eqtri ) BACZDEFZGHFIJZAIKUOGLFDSZAIKAMUQURAIUOIJZUPGLFNSZUQURUSUP
    OJGPJUTUQQUSUPUORUAUBUPGULUCUSUOOJGOJZDGUDUEZUTURQUOUFVAUSUGTVBUSUMTUOGUHUI
    UJUKUN $.

  $( Alternate definition for odd numbers.  (Contributed by AV,
     18-Jun-2020.) $)
  dfodd5 $p |- Odd = { z e. ZZ | ( z mod 2 ) =/= 0 } $=
    ( codd cv c2 cmo co c1 wceq cz crab cc0 wne dfodd4 wcel cpr wb elmod2 prcom
    eleq2i biimpi ax-1ne0 elprneb sylancl syl rabbiia eqtri ) BACZDEFZGHZAIJUHK
    LZAIJAMUIUJAIUGINUHKGOZNZUIUJPZUGQULUHGKOZNZGKLUMULUOUKUNUHKGRSTUAUHGKUBUCU
    DUEUF $.

  $( The floor of an even number divided by 2 is equal to the even number
     divided by 2.  (Contributed by AV, 7-Jun-2020.)  (Revised by AV,
     18-Jun-2020.) $)
  zefldiv2ALTV $p |- ( N e. Even -> ( |_ ` ( N / 2 ) ) = ( N / 2 ) ) $=
    ( ceven wcel c2 cdiv co cz cfl cfv wceq evendiv2z flid syl ) ABCADEFZGCNHIN
    JAKNLM $.

  $( The floor of an odd number divided by 2 is equal to the odd number first
     decreased by 1 and then divided by 2.  (Contributed by AV, 7-Jun-2020.)
     (Revised by AV, 18-Jun-2020.) $)
  zofldiv2ALTV $p |- ( N e. Odd -> ( |_ ` ( N / 2 ) ) = ( ( N - 1 ) / 2 ) ) $=
    ( codd wcel c2 cdiv co cfl cfv c1 cmin caddc cc wceq oddz zcnd npcan1 eqtrd
    cc0 wa wbr eqcomd oveq1d wne peano2cnm 2cnne0 a1i divdir syl3anc syl fveq2d
    1cnd cle clt halfge0 halflt1 pm3.2i cz cr wb oddm1div2z halfre flbi2 mpbiri
    sylancl ) ABCZADEFZGHAIJFZDEFZIDEFZKFZGHZVHVEVFVJGVEALCZVFVJMVEAANOVLVFVGIK
    FZDEFZVJVLAVMDEVLVMAAPUAUBVLVGLCILCDLCDRUCSZVNVJMAUDVLUKVOVLUEUFVGIDUGUHQUI
    UJVEVKVHMZRVIULTZVIIUMTZSZVQVRUNUOUPVEVHUQCVIURCVPVSUSAUTVAVIVHVBVDVCQ $.

  $( Odd number representation by using the floor function.  (Contributed by
     Glauco Siliprandi, 11-Dec-2019.)  (Revised by AV, 18-Jun-2020.) $)
  oddflALTV $p |- ( K e. Odd -> K = ( ( 2 x. ( |_ ` ( K / 2 ) ) ) + 1 ) ) $=
    ( codd wcel c2 cdiv co cfl cmul c1 caddc cmin zofldiv2ALTV oveq2d oveq1d cz
    cfv cc oddz zcnd syl peano2zm 2cnd cc0 wne 2ne0 a1i divcan2d npcan1 3eqtrrd
    wceq ) ABCZDADEFGPZHFZIJFDAIKFZDEFZHFZIJFUNIJFZAUKUMUPIJUKULUODHALMNUKUPUNI
    JUKUNDUKAOCZUNQCARZURUNAUASTUKUBDUCUDUKUEUFUGNUKAQCUQAUJUKAUSSAUHTUI $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Alternate definitions using the "gcd" operation
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( The predicate "is an even number".  An even number and 2 have 2 as
     greatest common divisor.  (Contributed by AV, 1-Jul-2020.) $)
  iseven5 $p |- ( Z e. Even <-> ( Z e. ZZ /\ ( 2 gcd Z ) = 2 ) ) $=
    ( ceven wcel cz c2 cdvds wbr wa cgcd co wceq iseven2 2nn gcdzeq mpan bicomd
    cn wb pm5.32i bitri ) ABCADCZEAFGZHUAEAIJEKZHALUAUBUCUAUCUBEQCUAUCUBRMEANOP
    ST $.

  $( The predicate "is an odd number".  An odd number and 2 have 1 as greatest
     common divisor.  (Contributed by AV, 1-Jul-2020.) $)
  isodd7 $p |- ( Z e. Odd <-> ( Z e. ZZ /\ ( 2 gcd Z ) = 1 ) ) $=
    ( codd wcel cz c2 cdvds wn wa cgcd co c1 wceq isodd3 cprime 2prm coprm mpan
    wbr wb pm5.32i bitri ) ABCADCZEAFRGZHUBEAIJKLZHAMUBUCUDENCUBUCUDSOEAPQTUA
    $.

  ${
    $d x z $.
    $( Alternate definition for even numbers.  (Contributed by AV,
       1-Jul-2020.) $)
    dfeven5 $p |- Even = { z e. ZZ | ( 2 gcd z ) = 2 } $=
      ( vx ceven c2 cv cgcd co wceq cz crab wcel iseven5 weq oveq2 eqeq1d elrab
      wa bitr4i eqriv ) BCDAEZFGZDHZAIJZBEZCKUDIKDUDFGZDHZQUDUCKUDLUBUFAUDIABMU
      AUEDTUDDFNOPRS $.

    $( Alternate definition for odd numbers.  (Contributed by AV,
       1-Jul-2020.) $)
    dfodd7 $p |- Odd = { z e. ZZ | ( 2 gcd z ) = 1 } $=
      ( vx codd c2 cv cgcd co c1 wceq cz crab wcel wa isodd7 oveq2 eqeq1d elrab
      weq bitr4i eqriv ) BCDAEZFGZHIZAJKZBEZCLUEJLDUEFGZHIZMUEUDLUENUCUGAUEJABR
      UBUFHUAUEDFOPQST $.
  $}

  $( The greatest common divisor of an odd number and 2 is 1, i.e., 2 and any
     odd number are coprime.  Remark:  The proof using ~ dfodd7 is longer (see
     proof in comment)!  (Contributed by AV, 5-Jun-2023.) $)
  gcd2odd1 $p |- ( Z e. Odd -> ( Z gcd 2 ) = 1 ) $=
    ( codd wcel c2 cgcd co c1 cz wceq oddz 2z gcdcom sylancl cdvds wn 2ndvdsodd
    wbr cprime wb 2prm coprm sylancr mpbid eqtrd ) ABCZADEFZDAEFZGUEAHCZDHCUFUG
    IAJZKADLMUEDANQOZUGGIZAPUEDRCUHUJUKSTUIDAUAUBUCUD $.
   $( vz c2 cgcd co c1 wceq cv cz crab codd wcel oveq2 eqeq1d elrab gcdcom mpan
    wa 2z biimpa sylbi dfodd7 eleq2s ) ACDEZFGZACBHZDEZFGZBIJZKAUILAILZCADEZFGZ
    RUEUHULBAIUFAGUGUKFUFACDMNOUJULUEUJUKUDFCILUJUKUDGSCAPQNTUABUBUC $)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Theorems of part 5 revised
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( No even integer equals an odd integer (i.e. no integer can be both even
     and odd).  Exercise 10(a) of [Apostol] p. 28.  (Contributed by NM,
     31-Jul-2004.)  (Revised by AV, 16-Jun-2020.) $)
  zneoALTV $p |- ( ( A e. Even /\ B e. Odd ) -> A =/= B ) $=
    ( codd wcel ceven wn wne oddneven nelne2 sylan2 ) BCDAEDBEDFABGBHABEIJ $.

  $( An integer is even or odd.  (Contributed by NM, 1-Jan-2006.)  (Revised by
     AV, 16-Jun-2020.) $)
  zeoALTV $p |- ( Z e. ZZ -> ( Z e. Even \/ Z e. Odd ) ) $=
    ( cz wcel c2 cdiv co wa c1 caddc wo ceven codd zeo ancli sylib iseven isodd
    andi orbi12i sylibr ) ABCZUAADEFBCZGZUAAHIFDEFBCZGZJZAKCZALCZJUAUAUBUDJZGUF
    UAUIAMNUAUBUDROUGUCUHUEAPAQST $.

  $( An integer is even or odd but not both.  (Contributed by Mario Carneiro,
     12-Sep-2015.)  (Revised by AV, 16-Jun-2020.) $)
  zeo2ALTV $p |- ( Z e. ZZ -> ( Z e. Even <-> -. Z e. Odd ) ) $=
    ( cz wcel ceven codd wn evennodd wo wi zeoALTV ax-1 pm2.24 jaoi syl impbid2
    ) ABCZADCZAECZFZAGPQRHSQIZAJQTRQSKRQLMNO $.

  $( A positive integer is even or odd but not both.  (Contributed by NM,
     1-Jan-2006.)  (Revised by AV, 19-Jun-2020.) $)
  nneoALTV $p |- ( N e. NN -> ( N e. Even <-> -. N e. Odd ) ) $=
    ( cn wcel cz ceven codd wn wb nnz zeo2ALTV syl ) ABCADCAECAFCGHAIAJK $.

  ${
    nneoiALTV.1 $e |- N e. NN $.
    $( A positive integer is even or odd but not both.  (Contributed by NM,
       20-Aug-2001.)  (Revised by AV, 19-Jun-2020.) $)
    nneoiALTV $p |- ( N e. Even <-> -. N e. Odd ) $=
      ( cn wcel ceven codd wn wb nneoALTV ax-mp ) ACDAEDAFDGHBAIJ $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Theorems of part 6 revised
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d N n z $.
    $( An integer is odd iff it is one plus twice another integer.
       (Contributed by Scott Fenton, 3-Apr-2014.)  (Revised by AV,
       19-Jun-2020.) $)
    odd2np1ALTV $p |- ( N e. ZZ ->
      ( N e. Odd <-> E. n e. ZZ ( ( 2 x. n ) + 1 ) = N ) ) $=
      ( vz cz wcel c2 cv cmul co c1 caddc wceq wrex wa codd ibar wb a1i rexbidv
      eqcom eqeq1 dfodd6 elrab2 3bitr4rd ) BDEZBFAGHIJKIZLZADMZUEUHNZUFBLZADMBO
      EZUEUHPUEUJUGADUJUGQUEUFBTRSUKUIQUECGZUFLZADMUHCBDOULBLUMUGADULBUFUASCAUB
      UCRUD $.
  $}

  $( An integer is odd iff its predecessor is even.  (Contributed by Mario
     Carneiro, 5-Sep-2016.)  (Revised by AV, 19-Jun-2020.) $)
  oddm1evenALTV $p |- ( N e. ZZ -> ( N e. Odd <-> ( N - 1 ) e. Even ) ) $=
    ( cz wcel codd c1 cmin co c2 cdiv wa ceven isodd2 peano2zm biantrurd iseven
    baib bitrd bitr4di ) ABCZADCZAEFGZBCZUAHIGBCZJZUAKCSTUCUDTSUCALPSUBUCAMNQUA
    OR $.

  $( An integer is odd iff its successor is even.  (Contributed by Mario
     Carneiro, 5-Sep-2016.)  (Revised by AV, 19-Jun-2020.) $)
  oddp1evenALTV $p |- ( N e. ZZ -> ( N e. Odd <-> ( N + 1 ) e. Even ) ) $=
    ( cz wcel codd c1 caddc co c2 cdiv ceven isodd baib peano2z biantrurd bitrd
    wa iseven bitr4di ) ABCZADCZAEFGZBCZUAHIGBCZPZUAJCSTUCUDTSUCAKLSUBUCAMNOUAQ
    R $.

  ${
    $d A n $.  $d N n $.
    $( The exponential of the negative of a number, when the exponent is odd.
       (Contributed by Mario Carneiro, 25-Apr-2015.)  (Revised by AV,
       19-Jun-2020.)  (Proof shortened by AV, 10-Jul-2022.) $)
    oexpnegALTV $p |- ( ( A e. CC /\ N e. NN /\ N e. Odd ) ->
      ( -u A ^ N ) = -u ( A ^ N ) ) $=
      ( vn wcel c2 cmul co c1 wceq cneg cz syl wa cn0 oveq1d a1i expmuld expp1d
      cexp eqtr3d cc cn codd w3a cv caddc wrex wb oddz odd2np1ALTV ibi 3ad2ant3
      simpl1 cmin simprr simpl2 nncnd 1cnd 2z simprl zmulcl sylancr zcnd mpbird
      subadd2d nnm1nn0 eqeltrrd expcld mulneg2d negcld cc0 cle wbr crp 2rp zred
      sqneg nn0ge0d prodge0rd elnn0z sylanbrc 3eqtr4d oveq2d negeqd rexlimddv
      2nn0 ) AUADZBUBDZBUCDZUDZECUEZFGZHUFGZBIZAJZBSGZABSGZJZICKWIWGWNCKUGZWHWI
      WSWIBKDWIWSUHBUICBUJLUKULWJWKKDZWNMZMZAWLSGZAFGZJZWPWRXBXCWOFGZXEWPXBXCAX
      BAWLWGWHWIXAUMZXBBHUNGZWLNXBXHWLIWNWJWTWNUOZXBBHWLXBBWGWHWIXAUPZUQXBURXBW
      LXBEKDWTWLKDUSWJWTWNUTZEWKVAVBVCVEVDXBWHXHNDXJBVFLVGZVHXGVIXBWOWLSGZWOFGZ
      XFWPXBXMXCWOFXBWOESGZWKSGAESGZWKSGXMXCXBXOXPWKSXBWGXOXPIXGAVQLOXBWOEWKXBA
      XGVJZXBWTVKWKVLVMWKNDXKXBEWKEVNDXBVOPXBWKXKVPXBWLXLVRVSWKVTWAZENDXBWFPZQX
      BAEWKXGXRXSQWBOXBWOWMSGXNWPXBWOWLXQXLRXBWMBWOSXIWCTTTXBXDWQXBAWMSGXDWQXBA
      WLXGXLRXBWMBASXIWCTWDTWE $.

    $( The exponential of the negative of a number not being 0, when the
       exponent is odd.  (Contributed by AV, 19-Jun-2020.) $)
    oexpnegnz $p |- ( ( A e. CC /\ A =/= 0 /\ N e. Odd )
                      -> ( -u A ^ N ) = -u ( A ^ N ) ) $=
      ( vn cc wcel cc0 wne c2 cmul co wceq cneg cexp cz syl wa 2z oveq1d eqtr3d
      jca31 codd w3a cv c1 caddc wrex wb oddz odd2np1ALTV biimpd pm2.43i simpl1
      3ad2ant3 simpl2 simprl zmulcl sylancr expclzd mulneg2d negcld negne0d a1i
      sqneg simpl adantl expmulz 3eqtr4d expp1zd simprr oveq2d negeqd rexlimddv
      jca ) ADEZAFGZBUAEZUBZHCUCZIJZUDUEJZBKZALZBMJZABMJZLZKCNVPVNWACNUFZVOVPWF
      VPVPWFVPBNEVPWFUGBUHCBUIOUJUKUMVQVRNEZWAPZPZAVSMJZAIJZLZWCWEWIWJWBIJZWLWC
      WIWJAWIAVSVNVOVPWHULZVNVOVPWHUNZWIHNEZWGVSNEQVQWGWAUOHVRUPUQZURWNUSWIWBVS
      MJZWBIJZWMWCWIWRWJWBIWIWBHMJZVRMJZAHMJZVRMJZWRWJWIWTXBVRMWIVNWTXBKWNAVCOR
      WIWBDEZWBFGZPWPWGPZPWRXAKWIXDXEXFWIAWNUTZWIAWNWOVAZWHXFVQWHWPWGWPWHQVBWGW
      AVDVMVEZTWBHVRVFOWIVNVOPXFPWJXCKWIVNVOXFWNWOXITAHVRVFOVGRWIWBVTMJWSWCWIWB
      VSXGXHWQVHWIVTBWBMVQWGWAVIZVJSSSWIWKWDWIAVTMJWKWDWIAVSWNWOWQVHWIVTBAMXJVJ
      SVKSVL $.
  $}

  $( Value of the zeroth bit.  (Contributed by Mario Carneiro, 5-Sep-2016.)
     (Revised by AV, 19-Jun-2020.) $)
  bits0ALTV $p |- ( N e. ZZ -> ( 0 e. ( bits ` N ) <-> N e. Odd ) ) $=
    ( cz wcel cc0 cbits cfv c2 cexp co cdiv cfl cdvds wbr wn codd 0nn0 bitsval2
    cn0 wb c1 mpan2 cc wceq 2cn exp0 ax-mp oveq2i zcn div1d eqtrid fveq2d eqtrd
    flid breq2d notbid isodd3 baibr 3bitrd ) ABCZDAEFCZGAGDHIZJIZKFZLMZNZGALMZN
    ZAOCZUSDRCUTVESPDAQUAUSVDVFUSVCAGLUSVCAKFAUSVBAKUSVBATJIAVATAJGUBCVATUCUDGU
    EUFUGUSAAUHUIUJUKAUMULUNUOVHUSVGAUPUQUR $.

  $( The zeroth bit of an even number is zero.  (Contributed by Mario Carneiro,
     5-Sep-2016.)  (Revised by AV, 19-Jun-2020.) $)
  bits0eALTV $p |- ( N e. Even -> -. 0 e. ( bits ` N ) ) $=
    ( ceven wcel cc0 cbits cfv codd evennodd cz wb evenz bits0ALTV syl mtbird )
    ABCZDAEFCZAGCZAHOAICPQJAKALMN $.

  $( The zeroth bit of an odd number is zero.  (Contributed by Mario Carneiro,
     5-Sep-2016.)  (Revised by AV, 19-Jun-2020.) $)
  bits0oALTV $p |- ( N e. Odd -> 0 e. ( bits ` N ) ) $=
    ( codd wcel cc0 cbits cfv cz wb oddz bits0ALTV syl ibir ) ABCZDAEFCZMAGCNMH
    AIAJKL $.

  $( Either ` A / ( A gcd B ) ` is odd or ` B / ( A gcd B ) ` is odd.
     (Contributed by Scott Fenton, 19-Apr-2014.)  (Revised by AV,
     21-Jun-2020.) $)
  divgcdoddALTV $p |- ( ( A e. NN /\ B e. NN ) ->
    ( ( A / ( A gcd B ) ) e. Odd \/ ( B / ( A gcd B ) ) e. Odd ) ) $=
    ( cn wcel wa co cdiv cz c2 cdvds wbr wn wo codd nnz cc0 wceq adantr mpbid
    wb cgcd divgcdodd gcddvds syl2an simpld wne anim12i neneqd intnanrd gcdn0cl
    syl2anc nnzd nnne0d dvdsval2 syl3anc biantrurd simprd adantl orbi12d isodd3
    nnne0 orbi12i sylibr ) ACDZBCDZEZAABUAFZGFZHDZIVHJKLZEZBVGGFZHDZIVLJKLZEZMZ
    VHNDZVLNDZMVFVJVNMVPABUBVFVJVKVNVOVFVIVJVFVGAJKZVIVFVSVGBJKZVDAHDZBHDZVSVTE
    VEAOZBOZABUCUDZUEVFVGHDZVGPUFZWAVSVITVFVGVFWAWBEAPQZBPQZELZVGCDVDWAVEWBWCWD
    UGVDWJVEVDWHWIVDAPAVAUHUIRABUJUKZULZVFVGWKUMZVDWAVEWCRVGAUNUOSUPVFVMVNVFVTV
    MVFVSVTWEUQVFWFWGWBVTVMTWLWMVEWBVDWDURVGBUNUOSUPUSSVQVKVRVOVHUTVLUTVBVC $.

  ${
    $d A a i j n z $.  $d B b i j n z $.
    $( The sum of two odds is even.  (Contributed by Scott Fenton, 7-Apr-2014.)
       (Revised by AV, 20-Jun-2020.) $)
    opoeALTV $p |- ( ( A e. Odd /\ B e. Odd ) -> ( A + B ) e. Even ) $=
      ( vn vi vj codd wcel wa caddc co cz c2 cv cmul wceq wrex c1 wi imp cc zcn
      va vb vz ceven oddz zaddcl syl2an eqeq1 rexbidv dfodd6 elrab2 ex ad3antlr
      adantr peano2zd wb oveq2 eqeq2d adantl oveq12 2cnd anim1i ancoms syl 1cnd
      mulcl sylan add4d simpl simpr adddid oveq1d addcl 1p1e2 eqtr4i a1i oveq2d
      2t1e2 3eqtr4rd eqtrd rspcedvd rexlimdva2 expimpd biimtrid sylbi sylanbrc
      dfeven4 ) AFGZBFGZHABIJZKGZWKLCMZNJZOZCKPZWKUEGWIAKGZBKGZWLWJAUFBUFABUGUH
      WIWJWPWIWQALDMZNJZQIJZOZDKPZHZWJWPRUBMZXAOZDKPXCUBAKFXEAOXFXBDKXEAXAUIUJU
      BDUKULWJWRBLEMZNJZQIJZOZEKPZHZXDWPUCMZXIOZEKPXKUCBKFXMBOXNXJEKXMBXIUIUJUC
      EUKULWQXCXLWPRZWQXBXODKWQWSKGZHZXBHZWRXKWPXRWRHZXJWPEKXSXGKGZHZXJHZWOWKLW
      SXGIJZQIJZNJZOZCYDKYBYCYAYCKGZXJXSXTYGXPXTYGRWQXBWRXPXTYGWSXGUGUMUNSUOUPW
      MYDOZWOYFUQYBYHWNYEWKWMYDLNURUSUTYBWKXAXIIJZYEYAXJWKYIOZXBXJYJRXQWRXTXBXJ
      YJAXABXIIVAUMUNSYAYIYEOZXJXSXTYKXPXTYKRWQXBWRXPXTYKXPWSTGZXGTGZYKXTWSUAXG
      UAYLYMHZYIWTXHIJZQQIJZIJZYEYNWTQXHQYNLTGZYLHZWTTGYMYLYSYMYRYLYMVBVCVDLWSV
      GVEYNVFZYLYRYMXHTGYLVBLXGVGVHYTVIYNLYCNJZLQNJZIJYOUUBIJYEYQYNUUAYOUUBIYNL
      WSXGYNVBZYLYMVJYLYMVKVLVMYNLYCQUUCWSXGVNYTVLYNYPUUBYOIYPUUBOYNYPLUUBVOVSV
      PVQVRVTWAUHUMUNSUOWAWBWCWDWCSWEWFSUDMZWNOZCKPWPUDWKKUEUUDWKOUUEWOCKUUDWKW
      NUIUJUDCWHULWG $.

    $( The sum of an odd and an even is odd.  (Contributed by Scott Fenton,
       7-Apr-2014.)  (Revised by AV, 20-Jun-2020.) $)
    opeoALTV $p |- ( ( A e. Odd /\ B e. Even ) -> ( A + B ) e. Odd ) $=
      ( vn vi vj codd wcel wa caddc co cz c2 cv cmul c1 wceq wrex wi imp cc zcn
      va vb vz ceven evenz zaddcl syl2an eqeq1 rexbidv dfodd6 elrab2 dfeven4 ex
      oddz ad3antlr adantr oveq2 oveq1d eqeq2d adantl oveq12 2cnd mulcld ancoms
      wb mulcl add32d adddid eqcomd eqtrd rspcedvd rexlimdva2 r19.29an biimtrid
      1cnd expimpd sylbi sylanbrc ) AFGZBUEGZHABIJZKGZWBLCMZNJZOIJZPZCKQZWBFGVT
      AKGZBKGZWCWAAUOBUFABUGUHVTWAWHVTWIALDMZNJZOIJZPZDKQZHZWAWHRUBMZWMPZDKQWOU
      BAKFWQAPWRWNDKWQAWMUIUJUBDUKULWAWJBLEMZNJZPZEKQZHZWPWHUCMZWTPZEKQXBUCBKUE
      XDBPXEXAEKXDBWTUIUJUCEUMULWIWNXCWHRDKWIWKKGZHZWNHZWJXBWHXHWJHZXAWHEKXIWSK
      GZHZXAHZWGWBLWKWSIJZNJZOIJZPZCXMKXKXMKGZXAXIXJXQXFXJXQRWIWNWJXFXJXQWKWSUG
      UNUPSUQWDXMPZWGXPVFXLXRWFXOWBXRWEXNOIWDXMLNURUSUTVAXLWBWMWTIJZXOXKXAWBXSP
      ZWNXAXTRXGWJXJWNXAXTAWMBWTIVBUNUPSXKXSXOPZXAXIXJYAXFXJYARWIWNWJXFXJYAXFXJ
      HZXSWLWTIJZOIJXOYBWLOWTXJXFWLTGXJXFHZLWKYDVCXFWKTGZXJWKUAZVAVDVEYBVPXFLTG
      WSTGZWTTGXJXFVCWSUAZLWSVGUHVHYBYCXNOIYBXNYCYBLWKWSYBVCXFYEXJYFUQXJYGXFYHV
      AVIVJUSVKUNUPSUQVKVLVMVQVNVOVRSUDMZWFPZCKQWHUDWBKFYIWBPYJWGCKYIWBWFUIUJUD
      CUKULVS $.
  $}

  $( The difference of two odds is even.  (Contributed by Scott Fenton,
     7-Apr-2014.)  (Revised by AV, 20-Jun-2020.) $)
  omoeALTV $p |- ( ( A e. Odd /\ B e. Odd ) -> ( A - B ) e. Even ) $=
    ( codd wcel wa cneg caddc co cmin ceven cc wceq oddz negsub syl2an opoeALTV
    zcnd onego sylan2 eqeltrrd ) ACDZBCDZEABFZGHZABIHZJUAAKDBKDUDUELUBUAAAMQUBB
    BMQABNOUBUAUCCDUDJDBRAUCPST $.

  $( The difference of an odd and an even is odd.  (Contributed by Scott
     Fenton, 7-Apr-2014.)  (Revised by AV, 20-Jun-2020.) $)
  omeoALTV $p |- ( ( A e. Odd /\ B e. Even ) -> ( A - B ) e. Odd ) $=
    ( codd wcel ceven wa cneg caddc co cmin wceq oddz evenz negsub syl2an enege
    cc zcnd opeoALTV sylan2 eqeltrrd ) ACDZBEDZFABGZHIZABJIZCUBAQDBQDUEUFKUCUBA
    ALRUCBBMRABNOUCUBUDEDUECDBPAUDSTUA $.

  $( A prime not equal to ` 2 ` is odd.  (Contributed by Mario Carneiro,
     4-Feb-2015.)  (Revised by AV, 21-Jun-2020.) $)
  oddprmALTV $p |- ( N e. ( Prime \ { 2 } ) -> N e. Odd ) $=
    ( cprime c2 csn cdif wcel wne wa codd eldifsn cz cdvds wbr prmz adantr wceq
    wn c1 a1i sylanbrc wo necom df-ne sylbb adantl nesymi ioran cn wb dvdsprime
    1ne2 2nn sylan2 mtbird isodd3 sylbi ) ABCDEFABFZACGZHZAIFZABCJUSAKFZCALMZQU
    TUQVAURANOUSVBCAPZCRPZUAZUSVCQZVDQZVEQURVFUQURCAGVFACUBCAUCUDUEVGUSRCUKUFSV
    CVDUGTURUQCUHFZVBVEUIVHURULSACUJUMUNAUOTUP $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Theorems of AV's mathbox revised
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( 0 is an even number.  (Contributed by AV, 11-Feb-2020.)  (Revised by AV,
     17-Jun-2020.) $)
  0evenALTV $p |- 0 e. Even $=
    ( cc0 ceven wcel cz c2 cdiv co 0z 2cn 2ne0 div0i eqeltri iseven mpbir2an )
    ABCADCAEFGZDCHOADEIJKHLAMN $.

  $( 0 is not an odd number.  (Contributed by AV, 3-Feb-2020.)  (Revised by AV,
     17-Jun-2020.) $)
  0noddALTV $p |- 0 e/ Odd $=
    ( cc0 codd wnel ceven 0evenALTV wn df-nel cz wb zeo2ALTV bicomd ax-mp bitri
    wcel 0z mpbir ) ABCZADNZEQABNFZRABGAHNZSRIOTRSAJKLMP $.

  $( 1 is an odd number.  (Contributed by AV, 3-Feb-2020.)  (Revised by AV,
     18-Jun-2020.) $)
  1oddALTV $p |- 1 e. Odd $=
    ( c1 codd wcel cz caddc co c2 cdiv 1p1e2 oveq1i 2div2e1 eqtri eqeltri isodd
    1z mpbir2an ) ABCADCAAEFZGHFZDCORADRGGHFAQGGHIJKLOMANP $.

  $( 1 is not an even number.  (Contributed by AV, 12-Feb-2020.)  (Revised by
     AV, 18-Jun-2020.) $)
  1nevenALTV $p |- 1 e/ Even $=
    ( c1 codd wcel ceven wnel 1oddALTV wn cz wb 1z zeo2ALTV ax-mp df-nel bitr4i
    con2bii mpbi ) ABCZADEZFQADCZGRSQAHCSQGIJAKLOADMNP $.

  $( 2 is an even number.  (Contributed by AV, 12-Feb-2020.)  (Revised by AV,
     18-Jun-2020.) $)
  2evenALTV $p |- 2 e. Even $=
    ( c2 ceven wcel cz cdiv co 2z c1 2div2e1 1z eqeltri iseven mpbir2an ) ABCAD
    CAAEFZDCGNHDIJKALM $.

  $( 2 is not an odd number.  (Contributed by AV, 3-Feb-2020.)  (Revised by AV,
     18-Jun-2020.) $)
  2noddALTV $p |- 2 e/ Odd $=
    ( c2 codd wnel ceven wcel 2evenALTV wn df-nel cz wb 2z zeo2ALTV ax-mp bitri
    bicomd mpbir ) ABCZADEZFQABEGZRABHAIEZSRJKTRSALOMNP $.

  $( An odd nonnegative integer is either 1 or greater than 2.  (Contributed by
     AV, 2-Jun-2020.)  (Revised by AV, 21-Jun-2020.) $)
  nn0o1gt2ALTV $p |- ( ( N e. NN0 /\ N e. Odd ) -> ( N = 1 \/ 2 < N ) ) $=
    ( wcel codd wceq c2 wbr wo cc0 wi a1d eleq1 wn df-nel pm2.21 sylbi biimtrdi
    wnel ax-mp jaoi imp cn0 c1 clt cn elnn0 cuz cfv elnn1uz2 cz wa 2z eluz1i cr
    orc cle 2re a1i zre leloed olc wb eqcoms 2noddALTV 0noddALTV ) AUABZACBZAUB
    DZEAUCFZGZVEAUDBZAHDZGVFVIIZAUEVJVLVKVJVGAEUFUGBZGVLAUHVGVLVMVGVIVFVGVHUNJV
    MAUIBZEAUOFZUJVLEAUKULVNVOVLVNVOVHEADZGVLVNEAEUMBVNUPUQAURUSVHVLVPVHVIVFVHV
    GUTJVPVFECBZVIVFVQVAAEAECKVBECQZVQVIIZVCVRVQLVSECMVQVINORPSPTOSOVKVFHCBZVIA
    HCKHCQZVTVIIZVDWAVTLWBHCMVTVINORPSOT $.

  $( An alternate characterization of an odd number greater than 1.
     (Contributed by AV, 2-Jun-2020.)  (Revised by AV, 21-Jun-2020.) $)
  nnoALTV $p |- ( ( N e. ( ZZ>= ` 2 ) /\ N e. Odd )
                 -> ( ( N - 1 ) / 2 ) e. NN ) $=
    ( c2 cuz cfv wcel codd wa c1 cmin co cz cc0 clt wbr cn oddm1div2z cr adantr
    cdiv a1i adantl eluz2b1 1red zre posdifd biimpa w3a peano2zm zred 2pos 3jca
    wb 2re gt0div syl mpbid sylbi elnnz sylanbrc ) ABCDEZAFEZGAHIJZBSJZKEZLVCMN
    ZVCOEVAVDUTAPUAUTVEVAUTAKEZHAMNZGZVEAUBVHLVBMNZVEVFVGVIVFHAVFUCAUDUEUFVHVBQ
    EZBQEZLBMNZUGZVIVEULVFVMVGVFVJVKVLVFVBAUHUIVKVFUMTVLVFUJTUKRVBBUNUOUPUQRVCU
    RUS $.

  $( An alternate characterization of an odd nonnegative integer.  (Contributed
     by AV, 28-May-2020.)  (Revised by AV, 21-Jun-2020.) $)
  nn0oALTV $p |- ( ( N e. NN0 /\ N e. Odd ) -> ( ( N - 1 ) / 2 ) e. NN0 ) $=
    ( cn0 wcel codd wa c1 cmin co c2 cz cc0 cle wbr oddm1div2z adantl wi cr a1i
    cdiv sylbi cn wceq wo elnn0 nnm1ge0 clt nnre peano2rem syl 2re 2pos syl3anc
    wb ge0div mpbid a1d eleq1 wnel 0noddALTV wn df-nel pm2.21 biimtrdi jaoi imp
    ax-mp elnn0z sylanbrc ) ABCZADCZEAFGHZISHZJCZKVLLMZVLBCVJVMVIANOVIVJVNVIAUA
    CZAKUBZUCVJVNPZAUDVOVQVPVOVNVJVOKVKLMZVNAUEVOVKQCZIQCZKIUFMZVRVNUMVOAQCVSAU
    GAUHUIVTVOUJRWAVOUKRVKIUNULUOUPVPVJKDCZVNAKDUQKDURZWBVNPZUSWCWBUTWDKDVAWBVN
    VBTVFVCVDTVEVLVGVH $.

  $( An alternate characterization of an even nonnegative integer.
     (Contributed by AV, 22-Jun-2020.) $)
  nn0e $p |- ( ( N e. NN0 /\ N e. Even ) -> ( N / 2 ) e. NN0 ) $=
    ( cn0 wcel ceven wa c2 cdiv co cz cc0 cle wbr nn0ge0 cr clt wb 2re a1i 2pos
    nn0re ge0div syl3anc mpbid evendiv2z anim12ci elnn0z sylibr ) ABCZADCZEAFGH
    ZICZJUJKLZEUJBCUHULUIUKUHJAKLZULAMUHANCFNCZJFOLZUMULPATUNUHQRUOUHSRAFUAUBUC
    AUDUEUJUFUG $.

  $( An alternate characterization of an even positive integer.  (Contributed
     by AV, 5-Jun-2023.) $)
  nneven $p |- ( ( N e. NN /\ N e. Even ) -> ( N / 2 ) e. NN ) $=
    ( cn wcel ceven wa c2 cdiv co cz cc0 clt wbr nnre cr 2re nngt0 2pos divgt0d
    a1i evendiv2z anim12ci elnnz sylibr ) ABCZADCZEAFGHZICZJUFKLZEUFBCUDUHUEUGU
    DAFAMFNCUDOSAPJFKLUDQSRATUAUFUBUC $.

  ${
    $d N m $.
    $( For each odd nonnegative integer there is a nonnegative integer which,
       multiplied by 2 and increased by 1, results in the odd nonnegative
       integer.  (Contributed by AV, 30-May-2020.)  (Revised by AV,
       22-Jun-2020.) $)
    nn0onn0exALTV $p |- ( ( N e. NN0 /\ N e. Odd )
                         -> E. m e. NN0 N = ( ( 2 x. m ) + 1 ) ) $=
      ( wcel codd c1 cmin co c2 cdiv cv cmul caddc wceq wrex nn0oALTV wa oveq1d
      cn0 cc syl simpr wb oveq2 eqeq2d adantl nn0cn peano2cnm 2cnd cc0 wne 2ne0
      a1i divcan2d npcan1 eqtr2d adantr rspcedvd syldan ) BRCZBDCBEFGZHIGZRCZBH
      AJZKGZELGZMZARNBOUSVBPZVFBHVAKGZELGZMZAVARUSVBUAVCVAMZVFVJUBVGVKVEVIBVKVD
      VHELVCVAHKUCQUDUEUSVJVBUSVIUTELGZBUSVHUTELUSUTHUSBSCZUTSCBUFZBUGTUSUHHUIU
      JUSUKULUMQUSVMVLBMVNBUNTUOUPUQUR $.

    $( For each even nonnegative integer there is a nonnegative integer which,
       multiplied by 2, results in the even nonnegative integer.  (Contributed
       by AV, 30-May-2020.)  (Revised by AV, 22-Jun-2020.) $)
    nn0enn0exALTV $p |- ( ( N e. NN0 /\ N e. Even )
                         -> E. m e. NN0 N = ( 2 x. m ) ) $=
      ( cn0 wcel ceven wa c2 cv cmul co wceq cdiv wb oveq2 eqeq2d adantl cc cc0
      nn0e wne nn0cn 2cnd 2ne0 a1i w3a divcan2 eqcomd syl3anc adantr rspcedvd )
      BCDZBEDZFZBGAHZIJZKZBGBGLJZIJZKZAUQCBSUNUQKZUPUSMUMUTUOURBUNUQGINOPUKUSUL
      UKBQDZGQDZGRTZUSBUAUKUBVCUKUCUDVAVBVCUEURBBGUFUGUHUIUJ $.

    $( For each even positive integer there is a positive integer which,
       multiplied by 2, results in the even positive integer.  (Contributed by
       AV, 5-Jun-2023.) $)
    nnennexALTV $p |- ( ( N e. NN /\ N e. Even )
                        -> E. m e. NN N = ( 2 x. m ) ) $=
      ( cn wcel ceven wa c2 cv cmul co wceq cdiv nneven oveq2 eqeq2d adantl cc0
      wb cc wne nncn 2cnd 2ne0 a1i w3a divcan2 eqcomd syl3anc adantr rspcedvd )
      BCDZBEDZFZBGAHZIJZKZBGBGLJZIJZKZAUQCBMUNUQKZUPUSRUMUTUOURBUNUQGINOPUKUSUL
      UKBSDZGSDZGQTZUSBUAUKUBVCUKUCUDVAVBVCUEURBBGUFUGUHUIUJ $.
  $}

  $( 2 to the power of a positive integer is even.  (Contributed by AV,
     2-Jun-2020.)  (Revised by AV, 20-Jun-2020.) $)
  nnpw2evenALTV $p |- ( N e. NN -> ( 2 ^ N ) e. Even ) $=
    ( cn wcel c2 cexp co cz cdvds wbr ceven cn0 2z nnnn0 sylancr iddvdsexp mpan
    zexpcl iseven2 sylanbrc ) ABCZDAEFZGCZDUAHIZUAJCTDGCZAKCUBLAMDAQNUDTUCLDAOP
    UARS $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Additional theorems
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( The sum of an even and an odd is odd.  (Contributed by AV,
     24-Jul-2020.) $)
  epoo $p |- ( ( A e. Even /\ B e. Odd ) -> ( A + B ) e. Odd ) $=
    ( ceven wcel codd wa caddc co wceq evenz zcnd addcom syl2an opeoALTV ancoms
    cc oddz eqeltrd ) ACDZBEDZFABGHZBAGHZESAPDBPDUAUBITSAAJKTBBQKABLMTSUBEDBANO
    R $.

  $( The difference of an even and an odd is odd.  (Contributed by AV,
     24-Jul-2020.) $)
  emoo $p |- ( ( A e. Even /\ B e. Odd ) -> ( A - B ) e. Odd ) $=
    ( ceven wcel codd wa cneg caddc co cmin wceq evenz zcnd negsub syl2an onego
    cc oddz epoo sylan2 eqeltrrd ) ACDZBEDZFABGZHIZABJIZEUBAQDBQDUEUFKUCUBAALMU
    CBBRMABNOUCUBUDEDUEEDBPAUDSTUA $.

  $( The sum of two even numbers is even.  (Contributed by AV, 21-Jul-2020.) $)
  epee $p |- ( ( A e. Even /\ B e. Even ) -> ( A + B ) e. Even ) $=
    ( ceven wcel wa c1 caddc co cmin codd evenp1odd evenm1odd opoeALTV cc evenz
    syl2an wb zcnd adantr 1cnd adantl w3a ppncan eleq1d syl3anc mpbid ) ACDZBCD
    ZEZAFGHZBFIHZGHZCDZABGHZCDZUGUJJDUKJDUMUHAKBLUJUKMPUIANDZFNDZBNDZUMUOQUGUPU
    HUGAAORSUITUHURUGUHBBORUAUPUQURUBULUNCAFBUCUDUEUF $.

  $( The difference of two even numbers is even.  (Contributed by AV,
     21-Jul-2020.) $)
  emee $p |- ( ( A e. Even /\ B e. Even ) -> ( A - B ) e. Even ) $=
    ( ceven wcel wa cneg caddc co cmin wceq evenz zcnd negsub syl2an enege epee
    cc sylan2 eqeltrrd ) ACDZBCDZEABFZGHZABIHZCTAQDBQDUCUDJUATAAKLUABBKLABMNUAT
    UBCDUCCDBOAUBPRS $.

  $( If a summand is even, the other summand is even iff the sum is even.
     (Contributed by AV, 21-Jul-2020.) $)
  evensumeven $p |- ( ( A e. ZZ /\ B e. Even )
                      -> ( A e. Even <-> ( A + B ) e. Even ) ) $=
    ( cz wcel ceven wa caddc co wi epee expcom adantl cmin wceq zcn evenz pncan
    cc zcnd syl2an adantr simpr anim1i ancomd emee syl eqeltrrd ex impbid ) ACD
    ZBEDZFZAEDZABGHZEDZUKUMUOIUJUMUKUOABJKLULUOUMULUOFZUNBMHZAEULUQANZUOUJARDBR
    DURUKAOUKBBPSABQTUAUPUOUKFUQEDUPUKUOULUKUOUJUKUBUCUDUNBUEUFUGUHUI $.

  $( 3 is an odd number.  (Contributed by AV, 20-Jul-2020.) $)
  3odd $p |- 3 e. Odd $=
    ( c2 ceven wcel c3 codd 2evenALTV c1 caddc co df-3 evenp1odd eqeltrid ax-mp
    ) ABCZDECFNDAGHIEJAKLM $.

  $( 4 is an even number.  (Contributed by AV, 23-Jul-2020.) $)
  4even $p |- 4 e. Even $=
    ( c3 codd wcel c4 ceven 3odd c1 caddc co df-4 oddp1eveni eqeltrid ax-mp ) A
    BCZDECFNDAGHIEJAKLM $.

  $( 5 is an odd number.  (Contributed by AV, 23-Jul-2020.) $)
  5odd $p |- 5 e. Odd $=
    ( c4 ceven wcel c5 codd 4even c1 caddc co df-5 evenp1odd eqeltrid ax-mp ) A
    BCZDECFNDAGHIEJAKLM $.

  $( 6 is an even number.  (Contributed by AV, 20-Jul-2020.) $)
  6even $p |- 6 e. Even $=
    ( c6 ceven wcel cz c2 cdiv co 6nn nnzi c3 cmul 3t2e6 eqcomi oveq1i 3cn 2ne0
    2cn divcan4i eqtri 3z eqeltri iseven mpbir2an ) ABCADCAEFGZDCAHIUDJDUDJEKGZ
    EFGJAUEEFUEALMNJEOQPRSTUAAUBUC $.

  $( 7 is an odd number.  (Contributed by AV, 20-Jul-2020.) $)
  7odd $p |- 7 e. Odd $=
    ( c7 c6 c1 caddc co codd df-7 ceven wcel 6even evenp1odd ax-mp eqeltri ) AB
    CDEZFGBHINFIJBKLM $.

  $( 8 is an even number.  (Contributed by AV, 23-Jul-2020.) $)
  8even $p |- 8 e. Even $=
    ( c8 ceven wcel cz c2 cdiv co 8nn nnzi c4 cmul 4t2e8 eqcomi oveq1i 4cn 2ne0
    2cn divcan4i eqtri 4z eqeltri iseven mpbir2an ) ABCADCAEFGZDCAHIUDJDUDJEKGZ
    EFGJAUEEFUEALMNJEOQPRSTUAAUBUC $.

  $( A prime number is even iff it is 2.  (Contributed by AV, 21-Jul-2020.) $)
  evenprm2 $p |- ( P e. Prime -> ( P e. Even <-> P = 2 ) ) $=
    ( cprime wcel ceven c2 wceq wi 2a1 wn wa csn cdif codd df-ne biimpri anim2i
    wne ancoms eldifsn sylibr oddprmALTV oddneven pm2.21d 3syl ex pm2.61i eleq1
    2evenALTV mpbiri impbid1 ) ABCZADCZAEFZUMUKULUMGZGUMUKULHUMIZUKUNUOUKJZABEK
    LCZAMCZUNUPUKAEQZJZUQUKUOUTUOUSUKUSUOAENOPRABESTAUAURULUMAUBUCUDUEUFUMULEDC
    UHAEDUGUIUJ $.

  $( Every prime number not being 2 is an odd prime number.  (Contributed by
     AV, 21-Aug-2021.) $)
  oddprmne2 $p |- ( ( P e. Prime /\ P e. Odd ) <-> P e. ( Prime \ { 2 } ) ) $=
    ( cprime wcel codd wa c2 wne csn cdif wn wceq ceven cz wb prmz zeo2ALTV syl
    evenprm2 bitr3d nne bitr4di con4bid pm5.32i eldifsn bitr4i ) ABCZADCZEUFAFG
    ZEABFHICUFUGUHUFUGUHUFUGJZAFKZUHJUFALCZUIUJUFAMCUKUINAOAPQARSAFTUAUBUCABFUD
    UE $.

  $( A prime number which is odd is an integer greater than or equal to 3.
     (Contributed by AV, 20-Jul-2020.)  (Proof shortened by AV,
     21-Aug-2021.) $)
  oddprmuzge3 $p |- ( ( P e. Prime /\ P e. Odd ) -> P e. ( ZZ>= ` 3 ) ) $=
    ( cprime wcel codd wa c2 csn cdif c3 cuz cfv oddprmne2 oddprmge3 sylbi ) AB
    CADCEABFGHCAIJKCALAMN $.

  $( If an even number is greater than another even number, then it is greater
     than or equal to the other even number plus 2.  (Contributed by AV,
     25-Dec-2021.) $)
  evenltle $p |- ( ( N e. Even /\ M e. Even /\ M < N ) -> ( M + 2 ) <_ N ) $=
    ( ceven wcel clt wbr caddc co cle wa c1 cz wb evenz zltp1le syl2anr wceq cr
    zred sylbid c2 peano2re syl leloe peano2zd zcnd adantl add1p1 breq1d biimpd
    wo cc codd wi evenp1odd zneoALTV eqneqall eqcoms syl5com sylan2 jaod 3impia
    wne ) BCDZACDZABEFZAUAGHZBIFZVDVEJZVFAKGHZBIFZVHVEALDBLDZVFVKMVDANZBNZABOPV
    IVKVJBEFZVJBQZUKZVHVEVJRDZBRDVKVQMVDVEARDVRVEAVMSAUBUCVDBVNSVJBUDPVIVOVHVPV
    IVOVJKGHZBIFZVHVEVJLDVLVOVTMVDVEAVMUEVNVJBOPVIVTVHVIVSVGBIVIAULDZVSVGQVEWAV
    DVEAVMUFUGAUHUCUIUJTVEVDVJUMDZVPVHUNAUOVDWBJBVJVCZVPVHBVJUPWCVHUNBVJVHBVJUQ
    URUSUTVATTVB $.

  $( If an odd number is the sum of two prime numbers, one of the prime numbers
     must be 2.  (Contributed by AV, 26-Dec-2021.) $)
  odd2prm2 $p |- ( ( N e. Odd /\ ( P e. Prime /\ Q e. Prime )
                      /\ N = ( P + Q ) )
                    -> ( P = 2 \/ Q = 2 ) ) $=
    ( c2 wceq codd cprime wa caddc wi wn wne df-ne eldifsn oddprmALTV sylbir ex
    wcel biimtrrid a1d co w3a wo eleq1 ceven evennodd pm2.21d csn cdif im2anan9
    imp opoeALTV syl syl11 expd biimtrdi 3imp231 com12 orc olc pm2.61ii ) ADEZB
    DEZCFRZAGRZBGRZHZCABIUAZEZUBZVBVCUCZJZVBKZVCKZVLVJVMVNHZVKVIVDVGVOVKJZVIVDV
    HFRZVGVPJCVHFUDVQVGVOVKVHUERZVQVKVGVOHZVRVQVKVHUFUGVSAFRZBFRZHZVRVGVOWBVEVM
    VTVFVNWAVMADLZVEVTADMVEWCVTVEWCHAGDUHUIZRVTAGDNAOPQSVNBDLZVFWABDMVFWEWAVFWE
    HBWDRWABGDNBOPQSUJUKABULUMUNUOUPUQURQVBVKVJVBVCUSTVCVKVJVCVBUTTVA $.

  $( If an even number is the sum of three prime numbers, one of the prime
     numbers must be 2.  (Contributed by AV, 25-Dec-2021.) $)
  even3prm2 $p |- ( ( N e. Even /\ ( P e. Prime /\ Q e. Prime /\ R e. Prime )
                      /\ N = ( ( P + Q ) + R ) )
                    -> ( P = 2 \/ Q = 2 \/ R = 2 ) ) $=
    ( wcel cprime w3a caddc co wceq c2 wo wi wa codd adantl cc zcnd prmz cz w3o
    ceven olc a1d wn cmin wne df-ne csn cdif eldifsn oddprmALTV emoo expcom syl
    sylbir biimtrrid com23 3ad2ant3 impcom 3adant3 3simpa 3ad2ant2 eqcom adantr
    evenz zaddcl syl2an subadd2d biimprd biimtrid odd2prm2 syl3anc orcd pm2.61i
    ex 3impia df-3or sylibr ) DUBEZAFEZBFEZCFEZGZDABHIZCHIZJZGZAKJZBKJZLZCKJZLZ
    WIWJWLUAWLWHWMMWLWMWHWLWKUCUDWLUEZWHWMWNWHNZWKWLWODCUFIZOEZWAWBNZWPWEJZWKWH
    WNWQVTWDWNWQMZWGWDVTWTWCWAVTWTMWBWCWNVTWQWNCKUGZWCVTWQMZCKUHWCXAXBWCXANCFKU
    IUJEZXBCFKUKXCCOEZXBCULVTXDWQDCUMUNUOUPVPUQURUSUTVAUTWHWRWNWDVTWRWGWAWBWCVB
    VCPWHWSWNVTWDWGWSWGWFDJZVTWDNZWSDWFVDXFWSXEXFDCWEVTDQEWDVTDDVFRVEWDCQEZVTWC
    WAXGWBWCCCSRUSPWDWEQEZVTWAWBXHWCWRWEWAATEBTEWETEWBASBSABVGVHRVAPVIVJVKVQPAB
    WPVLVMVNVPVOWIWJWLVRVS $.

  ${
    $d N p q $.  $d P p q $.  $d Q p q $.  $d R p q $.
    $( Lemma for ~ mogoldbb .  (Contributed by AV, 26-Dec-2021.) $)
    mogoldbblem $p |- ( ( ( P e. Prime /\ Q e. Prime /\ R e. Prime )
                          /\ N e. Even /\ ( N + 2 ) = ( ( P + Q ) + R ) )
                        -> E. p e. Prime E. q e. Prime N = ( p + q ) ) $=
      ( c2 wceq cprime wcel caddc co wi wa eqeq2d cc zcnd adantr adantl cz wrex
      w3o w3a ceven 2evenALTV epee mpan2 3ad2ant2 simp1 simp3 even3prm2 syl3anc
      cv oveq1 oveq1d wb 2cnd addcl 3adant1 addass comraddd evenz zaddcl syl2an
      prmz addcan2d bitrd simpll simplr simpr oveq2 eqcomd sylan9eq rspcedeq2vd
      rexbidv rspcedvd ex sylbid com12 biimtrdi com13 3imp 3jca 3adant2 3adant3
      add32 syl 3jaoi mpcom ) AGHZBGHZCGHZUBZAIJZBIJZCIJZUCZDUDJZDGKLZABKLZCKLZ
      HZUCZDFUMZEUMZKLZHZEIUAZFIUAZXCWSUDJZWQXBWMWRWQXJXBWRGUDJXJUEDGUFUGUHWQWR
      XBUIWQWRXBUJABCWSUKULWJXCXIMWKWLXCWJXIWQWRXBWJXIMZWOWPWRXBXKMZMWNWOWPNZWR
      XLWJXBXMWRNZXIWJXBWSGBKLZCKLZHZXNXIMWJXAXPWSWJWTXOCKAGBKUNUOOXNXQXIXNXQDB
      CKLZHZXIXNXQWSXRGKLZHZXSXMXQYAUPWRXMXPXTWSXMGPJZBPJZCPJZXPXTHXMUQWOYCWPWO
      BBVEZQRWPYDWOWPCCVEZQZSYBYCYDUCXPGXRYBYCYDUIYCYDXRPJZYBBCURUSGBCUTVAULORX
      NDXRGWRDPJZXMWRDDVBQZSXMYHWRXMXRWOBTJZCTJZXRTJWPYEYFBCVCVDQRXNUQVFVGXMXSX
      IMWRXMXSXIXMXSNZXHDBXEKLZHZEIUAZFBIWOWPXSVHXDBHZXHYPUPYMYQXGYOEIYQXFYNDXD
      BXEKUNOVOSYMECIDYNWOWPXSVIYMXECHZDXRYNXMXSVJYRYNXRXECBKVKVLVMVNVPVQRVRVSV
      TWAVQUSWBVSXCWKXIWQWRXBWKXIMZWNWPWRXBYSMZMWOWNWPNZWRYTWKXBUUAWRNZXIWKXBWS
      AGKLZCKLZHZUUBXIMWKXAUUDWSWKWTUUCCKBGAKVKUOOUUBUUEXIUUBUUEDACKLZHZXIUUBUU
      EWSUUFGKLZHUUGUUBUUDUUHWSUUBAPJZYBYDUCZUUDUUHHUUAUUJWRUUAUUIYBYDWNUUIWPWN
      AAVEZQRUUAUQWPYDWNYGSWCRAGCWFWGOUUBDUUFGWRYIUUAYJSUUAUUFPJWRUUAUUFWNATJZY
      LUUFTJWPUUKYFACVCVDQRUUBUQVFVGUUAUUGXIMWRUUAUUGXIUUAUUGNZXHDAXEKLZHZEIUAZ
      FAIWNWPUUGVHXDAHZXHUUPUPZUUMUUQXGUUOEIUUQXFUUNDXDAXEKUNOVOZSUUMECIDUUNWNW
      PUUGVIUUMYRDUUFUUNUUAUUGVJYRUUNUUFXECAKVKVLVMVNVPVQRVRVSVTWAVQWDWBVSXCWLX
      IWQWRXBWLXIMZWNWOWRXBUUTMZMWPWNWONZWRUVAWLXBUVBWRNZXIWLXBWSWTGKLZHZUVCXIM
      WLXAUVDWSCGWTKVKOUVCUVEXIUVCUVEDWTHZXIUVCDWTGWRYIUVBYJSUVBWTPJWRUVBWTWNUU
      LYKWTTJWOUUKYEABVCVDQRUVCUQVFUVBUVFXIMWRUVBUVFXIUVBUVFNZXHUUPFAIWNWOUVFVH
      UUQUURUVGUUSSUVGEBIDUUNWNWOUVFVIUVGXEBHZDWTUUNUVBUVFVJUVHUUNWTXEBAKVKVLVM
      VNVPVQRVRVSVTWAVQWEWBVSWHWI $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Perfect Number Theorem (revised)
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d k n x A $.  $d k n x B $.  $d k n x ph $.
    perfectALTVlem.1 $e |- ( ph -> A e. NN ) $.
    perfectALTVlem.2 $e |- ( ph -> B e. NN ) $.
    perfectALTVlem.3 $e |- ( ph -> B e. Odd ) $.
    perfectALTVlem.4 $e |- ( ph -> ( 1 sigma ( ( 2 ^ A ) x. B ) )
                                   = ( 2 x. ( ( 2 ^ A ) x. B ) ) ) $.
    $( Lemma for ~ perfectALTV .  (Contributed by Mario Carneiro, 7-Jun-2016.)
       (Revised by AV, 1-Jul-2020.) $)
    perfectALTVlem1 $p |- ( ph -> ( ( 2 ^ ( A + 1 ) ) e. NN
                              /\ ( ( 2 ^ ( A + 1 ) ) - 1 ) e. NN
                              /\ ( B / ( ( 2 ^ ( A + 1 ) ) - 1 ) ) e. NN ) ) $=
      ( c2 c1 co cn wcel syl sylancr wbr cmul cgcd wceq csgm cz caddc cexp cmin
      cdiv cn0 2nn nnnn0d peano2nn0 nnexpcl clt cr 2re peano2nnd expgt1 syl3anc
      a1i 1lt2 wb nnsub mpbid cdvds nnzd peano2zm 1nn0 sgmnncl dvdsmul1 syl2anc
      1nn 2cn expp1 nncnd mulcom sylancl eqtrd oveq1d mulassd 1cnd codd simprbi
      cc isodd7 wi 2z rpexp1i mpd sgmmul syl13anc pncan1 oveq2d 1sgm2ppw eqtr3d
      3eqtr3d 3eqtrd breqtrrd gcdcomd nnpw2evenALTV evenm1odd 4syl wa coprmdvds
      ceven mp2and nndivdvds 3jca ) AHBIUAJZUBJZKLZXFIUCJZKLZCXHUDJKLZAHKLZXEUE
      LZXGUFABUELZXLABDUGZBUHMZHXEUINZAIXFUJOZXIAHUKLZXEKLZIHUJOZXQXRAULUPABDUM
      ZXTAUQUPHXEUNUOAIKLXGXQXIURVHXPIXFUSNUTZAXHCVAOZXJAXHXFCPJZVAOZXHXFQJZIRZ
      YCAXHXHICSJZPJZYDVAAXHTLZYHTLXHYIVAOAXFTLZYJAXFXPVBZXFVCMZAYHAIUELCKLZYHK
      LVDEICVENVBXHYHVFVGAYDHHBUBJZPJZCPJHYOCPJZPJZYIAXFYPCPAXFYOHPJZYPAHVTLZXM
      XFYSRVIXNHBVJNAYOVTLYTYSYPRAYOAXKXMYOKLZUFXNHBUINZVKZVIYOHVLVMVNVOAHYOCYT
      AVIUPUUCACEVKVPAIYQSJZIYOSJZYHPJZYRYIAIVTLUUAYNYOCQJIRZUUDUUFRAVQUUBEAHCQ
      JIRZUUGACVRLZUUHFUUICTLZUUHCWAVSMAHTLZUUJXMUUHUUGWBUUKAWCUPZACEVBZXNHCBWD
      UOWEIYOCWFWGGAUUEXHYHPAIHXEIUCJZUBJZSJZUUEXHAUUOYOISAUUNBHUBABVTLUUNBRABD
      VKBWHMWIWIAXSUUPXHRYAXEWJMWKVOWLWMWNAYFXFXHQJZIAXHXFYMYLWOAHXHQJIRZUUQIRZ
      AXSXFXALXHVRLZUURYAXEWPXFWQUUTYJUURXHWAVSWRAUUKYJXLUURUUSWBUULYMXOHXHXEWD
      UOWEVNAYJYKUUJYEYGWSYCWBYMYLUUMXHXFCWTUOXBAYNXIYCXJUREYBCXHXCVGUTXD $.

    $( Lemma for ~ perfectALTV .  (Contributed by Mario Carneiro, 17-May-2016.)
       (Revised by AV, 1-Jul-2020.) $)
    perfectALTVlem2 $p |- ( ph -> ( B e. Prime
                                    /\ B = ( ( 2 ^ ( A + 1 ) ) - 1 ) ) ) $=
      ( vk wcel c2 c1 caddc co wceq cdvds wbr cn clt a1i cmul vn vx cprime cexp
      cmin cuz cfv cv wo wi wral cdiv cr perfectALTVlem1 simp3d nnred nnge1d cc
      1re 2cn exp1 ax-mp df-2 eqtri cz 2re 1zzd peano2nnd nnzd 1lt2 crp ltaddrp
      nnrpd sylancr ax-1cn nncnd addcom breqtrd ltexp2a syl32anc wa syl syl3anc
      jca sylibr sylanbrc cle wn ctp csu cfn wss syl2anc ad2antrr sselda nnnn0d
      mpbid nn0ge0d csn cun df-tp unssd eqsstrid w3o eltpi breq1 syl5ibrcom imp
      3jaod syl5 ssrabdv fsumless cin c0 simpr disjsn tpfi fsumsplit id oveq12d
      sumsn wne gtned mulcld oveq2d eqtrd oveq1d divcan3d 3eqtr3d csgm cn0 cgcd
      sylancl mpd 3brtr3d ltnled necomd 1nn eqeq1 adantr eqbrtrrid ltaddsubd wb
      simp1d 1rp cc0 peano2rem expgt1 posdif elrp ltdiv2d div1d lelttrd eluz2b2
      nnrp cpr crab cfz fzfid dvdsssfz1 ssfi ssrab2 prssi snssd simp2d dvdsmul2
      simplrl nnne0d divcan2d iddvds simplrr incom disjsn2 eqtr3id prfi divdird
      df-pr subdird mullidd pncan3d divassd 3eqtr4d ccxp nnexpcl mulcom mulassd
      expp1 2nn codd isodd7 sylbi rpexp1i sgmmul syl13anc pncan 1sgm2ppw eqtr3d
      2z 3eqtrd sgmnncl sgmval sselid cxp1d sumeq2dv remulcld ltaddrpd readdcld
      1nn0 3eqtrrd condan elpri ralrimiva 1dvds orbi12d imbi12d rspcv syl3c ord
      expr necon1ad eqeq2d orbi1d imbi2d ralbidv mpbird isprm2 ltp1d snssi mp1i
      peano2re diveq1ad necon3bid biimpar nelprd ex necon1bd ) ACUCIZCJBKLMZUDM
      ZKUEMZNZACJUFUGIZUAUHZCOPZVUCKNZVUCCNZUIZUJZUAQUKZUYQACQIZKCRPVUBEAKCUYTU
      LMZCKUMIZAUSSZAVUKAUYSQIZUYTQIZVUKQIZABCDEFGUNZUOZUPZACEUPAVUKVURUQAVUKCK
      ULMZCRAKUYTRPZVUKVUTRPAKKLMZUYSRPVVAAVVBJKUDMZUYSRVVCJVVBJURIZVVCJNUTJVAV
      BVCVDAJUMIZKVEIUYRVEIKJRPZKUYRRPVVCUYSRPVVEAVFSZAVGAUYRABDVHZVIVVFAVJSZAK
      KBLMZUYRRAVULBVKIKVVJRPUSABDVMKBVLVNAKURIZBURIZVVJUYRNVOABDVPZKBVQVNVRJKU
      YRVSVTUUAAKKUYSVUMVUMAUYSAVUNVUOVUPVUQUUDZUPZUUBWQAKUYTCKVKIAUUESAUYTUMIZ
      UUFUYTRPZWAUYTVKIAVVPVVQAUYSUMIZVVPVVOUYSUUGWBAKUYSRPZVVQAVVEUYRQIZVVFVVS
      VVGVVHVVIJUYRUUHWCAVULVVRVVSVVQUUCUSVVOKUYSUUIVNWQWDUYTUUJWEAVUJCVKIECUUO
      WBUUKWQACACEVPZUULVRZUUMZCUUNWFAVUIVUDVUCVUKNZVUFUIZUJZUAQUKZAVWFUAQAVUCQ
      IZVUDVWEAVWHVUDWAZWAZVUCVUKCUUPZIZVWEVWJVWLUYSVUKTMZVUCLMZVWMWGPZVWJVWLWH
      ZWAZVUKCVUCWIZHUHZHWJZUBUHZCOPZUBQUUQZVWSHWJZVWNVWMWGVWQVXCVWSVWRHAVXCWKI
      ZVWIVWPAKCUURMZWKIVXCVXFWLZVXEAKCUUSAVUJVXGECUBUUTWBVXFVXCUVAWMZWNVWQVWSV
      XCIZWAZVWSVWQVXCQVWSVXCQWLVWQVXBUBQUVBZSWOZUPVXJVWSVXJVWSVXLWPWRVWQVXBUBQ
      VWRVWQVWRVWKVUCWSZWTZQVUKCVUCXAZVWQVWKVXMQAVWKQWLZVWIVWPAVUPVUJVXPVUREVUK
      CQUVCWMZWNVWQVUCQAVWHVUDVWPUVGZUVDXBXCZVWQVXAVWRIZVXBVXTVXAVUKNZVXACNZVXA
      VUCNZXDVWQVXBVXAVUKCVUCXEVWQVYAVXBVYBVYCAVYAVXBUJVWIVWPAVXBVYAVUKCOPAVUKU
      YTVUKTMZCOAUYTVEIVUKVEIVUKVYDOPAUYTAVUNVUOVUPVUQUVEZVIAVUKVURVIUYTVUKUVFW
      MACUYTVWAAUYTVYEVPZAUYTVYEUVHZUVIVRVXAVUKCOXFXGZWNAVYBVXBUJVWIVWPAVXBVYBC
      COPZACVEIZVYIACEVIZCUVJWBVXACCOXFXGZWNVWQVXBVYCVUDAVWHVUDVWPUVKVXAVUCCOXF
      XGXIXJXHXKXLVWQVWTVWKVWSHWJZVXMVWSHWJZLMVWNVWQVWKVXMVWSVWRHVWQVWPVWKVXMXM
      XNNVWJVWPXOVWKVUCXPWEVWRVXNNVWQVXOSVWRWKIVWQVUKCVUCXQSVWQVWSVWRIWAVWSVWQV
      WRQVWSVXSWOVPXRVWQVYMVWMVYNVUCLAVYMVWMNVWIVWPAVUKWSZVWSHWJZCWSZVWSHWJZLMV
      UKCLMZVYMVWMAVYPVUKVYRCLAVUPVUKURIVYPVUKNVURAVUKVURVPVWSVUKHVUKQVWSVUKNXS
      YAWMAVUJCURIVYRCNEVWAVWSCHCQVWSCNXSYAWMXTAVYOVYQVWSVWKHAVYOVYQXMVYQVYOXMZ
      XNVYQVYOUVLACVUKYBVYTXNNAVUKCVUSVWBYCCVUKUVMWBUVNVWKVYOVYQWTNAVUKCUVQSVWK
      WKIAVUKCUVOSAVWSVWKIWAVWSAVWKQVWSVXQWOVPXRACUYTCTMZLMZUYTULMZVUKWUAUYTULM
      ZLMVWMVYSACWUAUYTVWAAUYTCVYFVWAYDVYFVYGUVPAWUCUYSCTMZUYTULMZVWMAWUBWUEUYT
      ULAWUBCWUECUEMZLMWUEAWUAWUGCLAWUAWUEKCTMZUEMWUGAUYSKCAUYSVVNVPZVVKAVOSZVW
      AUVRAWUHCWUEUEACVWAUVSYEYFYEACWUEVWAAUYSCWUIVWAYDUVTYFYGAUYSCUYTWUIVWAVYF
      VYGUWAZYFAWUDCVUKLACUYTVWAVYFVYGYHYEYIUWBZWNVWQVUCURIZWUMVYNVUCNVWQVUCVXR
      VPZWUNVWSVUCHVUCURVWSVUCNXSYAWMXTYFAVXDVWMNZVWIVWPAVWMKCYJMZVXCVWSKUWCMZH
      WJZVXDAWUFUYTWUPTMZUYTULMVWMWUPAWUEWUSUYTULAWUEJJBUDMZTMZCTMJWUTCTMZTMZWU
      SAUYSWVACTAUYSWUTJTMZWVAAVVDBYKIZUYSWVDNUTABDWPZJBUWGVNAWUTURIVVDWVDWVANA
      WUTAJQIWVEWUTQIZUWHWVFJBUWDVNZVPZUTWUTJUWEYMYFYGAJWUTCVVDAUTSWVIVWAUWFAKW
      VBYJMZKWUTYJMZWUPTMZWVCWUSAVVKWVGVUJWUTCYLMKNZWVJWVLNWUJWVHEAJCYLMKNZWVMA
      CUWIIZWVNFWVOVYJWVNWAWVNCUWJVYJWVNXOUWKWBAJVEIZVYJWVEWVNWVMUJWVPAUWRSVYKW
      VFJCBUWLWCYNKWUTCUWMUWNGAWVKUYTWUPTAKJUYRKUEMZUDMZYJMZWVKUYTAWVRWUTKYJAWV
      QBJUDAVVLVVKWVQBNVVMVOBKUWOYMYEYEAVVTWVSUYTNVVHUYRUWPWBUWQYGYIUWSYGWUKAWU
      PUYTAWUPAKYKIVUJWUPQIUXHEKCUWTVNVPVYFVYGYHYIAVVKVUJWUPWURNVOEKCHUBUXAVNAV
      XCWUQVWSHAVXIWAZVWSWVTVWSWVTVXCQVWSVXKAVXIXOUXBZVPUXCUXDUXIZWNYOVWQVWMVWN
      RPVWOWHVWQVWMVUCAVWMUMIZVWIVWPAUYSVUKVVOVUSUXEZWNZVWQVUCVXRVMUXFVWQVWMVWN
      WWEVWQVWMVUCWWEVWQVUCVXRUPUXGYPWQUXJVUCVUKCUXKWBUXSUXLZAVUHVWFUAQAVUGVWEV
      UDAVUEVWDVUFAKVUKVUCAKCYBZKVUKNZACKAKCVUMVWCYCYQZAWWHKCAWWHKCNZAKQIZVWGKC
      OPZWWHWWJUIZWWKAYRSWWFAVYJWWLVYKCUXMWBZVWFWWLWWMUJUAKQVUEVUDWWLVWEWWMVUCK
      COXFVUEVWDWWHVUFWWJVUCKVUKYSVUCKCYSUXNUXOUXPUXQUXRUXTYNUYAUYBUYCUYDUYEUAC
      UYFWFAVWMKLMZVWMWGPZWHZVUAAVWMWWORPWWQAVWMWWDUYGAVWMWWOWWDAWWCWWOUMIWWDVW
      MUYJWBYPWQAWWPCUYTACUYTYBZWWPAWWRWAZVUKCKWIZVWSHWJZVXDWWOVWMWGAWXAVXDWGPW
      WRAVXCVWSWWTHVXHWVTVWSWWAUPWVTVWSWVTVWSWWAWPWRAVXBUBQWWTAWWTVWKKWSZWTZQVU
      KCKXAZAVWKWXBQVXQWWKWXBQWLAYRKQUYHUYIXBXCZAVXAWWTIZVXBWXFVYAVYBVXAKNZXDAV
      XBVXAVUKCKXEAVYAVXBVYBWXGVYHVYLAVXBWXGWWLWWNVXAKCOXFXGXIXJXHXKXLYTWWSWXAV
      YMWXBVWSHWJZLMZWWOWWSVWKWXBVWSWWTHWWSKVWKIWHVWKWXBXMXNNWWSKVUKCWWSVUKKAVU
      KKYBWWRAVUKKCUYTACUYTVWAVYFVYGUYKUYLUYMYQAWWGWWRWWIYTUYNVWKKXPWEWWTWXCNWW
      SWXDSWWTWKIWWSVUKCKXQSWWSVWSWWTIWAVWSWWSWWTQVWSAWWTQWLWWRWXEYTWOVPXRAWXIW
      WONWWRAVYMVWMWXHKLWULAVVKVVKWXHKNWUJVOVWSKHKURVWSKNXSYAYMXTYTYFAWUOWWRWWB
      YTYOUYOUYPYNWD $.
  $}

  ${
    $d p N $.
    $( The Euclid-Euler theorem, or Perfect Number theorem.  A positive even
       integer ` N ` is a perfect number (that is, its divisor sum is ` 2 N ` )
       if and only if it is of the form ` 2 ^ ( p - 1 ) x. ( 2 ^ p - 1 ) ` ,
       where ` 2 ^ p - 1 ` is prime (a Mersenne prime).  (It follows from this
       that ` p ` is also prime.)  This is Metamath 100 proof #70.
       (Contributed by Mario Carneiro, 17-May-2016.)  (Revised by AV,
       1-Jul-2020.)  (Proof modification is discouraged.) $)
    perfectALTV $p |- ( ( N e. NN /\ N e. Even )
                        -> ( ( 1 sigma N ) = ( 2 x. N )
        <-> E. p e. ZZ ( ( ( 2 ^ p ) - 1 ) e. Prime /\
                        N = ( ( 2 ^ ( p - 1 ) ) x. ( ( 2 ^ p ) - 1 ) ) ) ) ) $=
      ( cn wcel wa c1 csgm co c2 cmul wceq cexp cmin cprime cz cdvds sylancr cc
      wbr oveq2d ceven cv wrex caddc 2dvdseven ad2antlr wb simpll pcelnn mpbird
      cpc 2prm nnzd peano2zd cdiv pcdvds cn0 2nn nnnn0d nnexpcl nndivdvds mpbid
      syl2anc wn codd pcndvds2 isodd3 sylanbrc simpr nncn ad2antrr nncnd nnne0d
      3eqtr4d perfectALTVlem2 simprd simpld ax-1cn pncan sylancl eqcomd oveq12d
      divcan2d eqeltrrd eqtr3d oveq2 oveq1d eleq1d oveq1 eqeq2d rspcev syl12anc
      anbi12d perfect1 2cn mersenne prmnn syl expm1t nnm1nn0 expcl mulcom eqtrd
      ex 2cnd adantl mulassd 3eqtrd eqeq12d syl5ibrcom impr rexlimiva impbid1 )
      ACDZAUADZEZFAGHZIAJHZKZIBUBZLHZFMHZNDZAIXTFMHZLHZYBJHZKZEZBOUCZXPXSYIXPXS
      EZIAUKHZFUDHZODIYLLHZFMHZNDZAIYLFMHZLHZYNJHZKZYIYJYKYJYKYJYKCDZIAPSZXOUUA
      XNXSAUEUFYJINDZXNYTUUAUGULXNXOXSUHZIAUIQUJZUMUNYJAIYKLHZUOHZYNNYJUUFNDZUU
      FYNKZYJYKUUFUUDYJUUEAPSZUUFCDZYJUUBXNUUIULUUCIAUPQYJXNUUECDZUUIUUJUGUUCYJ
      ICDYKUQDUUKURYJYKUUDUSIYKUTQZAUUEVAVCVBZYJUUFODIUUFPSVDZUUFVEDYJUUFUUMUMY
      JUUBXNUUNULUUCIAVFQUUFVGVHYJXQXRFUUEUUFJHZGHIUUOJHXPXSVIYJUUOAFGYJAUUEXNA
      RDXOXSAVJVKYJUUEUULVLYJUUEUULVMWCZTYJUUOAIJUUPTVNVOZVPZYJUUGUUHUUQVQWDYJU
      UOAYRUUPYJUUEYQUUFYNJYJYKYPILYJYPYKYJYKRDFRDYPYKKYJYKUUDVLVRYKFVSVTWATUUR
      WBWEYHYOYSEBYLOXTYLKZYCYOYGYSUUSYBYNNUUSYAYMFMXTYLILWFWGZWHUUSYFYRAUUSYEY
      QYBYNJUUSYDYPILXTYLFMWITUUTWBWJWMWKWLXDYHXSBOXTODZYCYGXSUVAYCEZXSYGFYFGHZ
      IYFJHZKUVBUVCYAYBJHIYEJHZYBJHUVDXTWNUVBYAUVEYBJUVBYAYEIJHZUVEUVBIRDZXTCDZ
      YAUVFKWOUVBXTNDUVHXTWPXTWQWRZIXTWSQUVBYERDZUVGUVFUVEKUVBUVGYDUQDZUVJWOUVB
      UVHUVKUVIXTWTWRIYDXAQZWOYEIXBVTXCWGUVBIYEYBUVBXEUVLUVBYBYCYBCDUVAYBWQXFVL
      XGXHYGXQUVCXRUVDAYFFGWFAYFIJWFXIXJXKXLXM $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Number theory (extension 2)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Fermat pseudoprimes
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  "In number theory, the _Fermat pseudoprimes_ make up the most important class
  of pseudoprimes that come from Fermat's little theorem  ... [[which] states
  that if p is prime and a is coprime to p, then a^(p-1)-1 is divisible by p
  [[see ~ fermltl ].

  For an integer a > 1, if a composite integer x divides a^(x-1)-1, then x is
  called a Fermat pseudoprime to base a.  In other words, a composite integer
  is a Fermat pseudoprime to base a if it successfully passes the Fermat
  primality test for the base a. The false statement [[see ~ nfermltl2rev ]
  that all numbers that pass the Fermat primality test for base 2, are prime,
  is called the Chinese hypothesis.", see Wikipedia "Fermat pseudoprime",
  ~ https://en.wikipedia.org/wiki/Fermat_pseudoprime , 29-May-2023.

$)

  $c FPPr $.

  $( Extend class notation with the Fermat pseudoprimes. $)
  cfppr $a class FPPr $.

  ${
    $d n x $.
    $( Define the function that maps a positive integer to the set of _Fermat
       pseudoprimes_ to the base of this positive integer.  Since Fermat
       pseudoprimes shall be composite (positive) integers, they must be
       nonprime integers greater than or equal to 4 (we cannot use ` x e. NN `
       ` /\ x e/ Prime ` because ` x = 1 ` would fulfil this requirement, but
       should not be regarded as "composite" integer).  (Contributed by AV,
       29-May-2023.) $)
    df-fppr $a |- FPPr = ( n e. NN |-> { x e. ( ZZ>= ` 4 ) | ( x e/ Prime
                                     /\ x || ( ( n ^ ( x - 1 ) ) - 1 ) ) } ) $.
  $}

  ${
    $d N n x $.
    $( The set of Fermat pseudoprimes to the base ` N ` .  (Contributed by AV,
       29-May-2023.) $)
    fppr $p |- ( N e. NN -> ( FPPr ` N ) = { x e. ( ZZ>= ` 4 ) | ( x e/ Prime
                                     /\ x || ( ( N ^ ( x - 1 ) ) - 1 ) ) } ) $=
      ( vn cv cprime wnel c1 cmin co cexp cdvds wbr wa c4 cuz cfv crab cn cfppr
      wceq oveq1 oveq1d breq2d anbi2d rabbidv df-fppr fvex rabex fvmpt ) CBADZE
      FZUJCDZUJGHIZJIZGHIZKLZMZANOPZQUKUJBUMJIZGHIZKLZMZAURQRSULBTZUQVBAURVCUPV
      AUKVCUOUTUJKVCUNUSGHULBUMJUAUBUCUDUEACUFVBAURNOUGUHUI $.
  $}

  ${
    $d N x $.
    $( The set of Fermat pseudoprimes to the base ` N ` , expressed by a modulo
       operation instead of the divisibility relation.  (Contributed by AV,
       30-May-2023.) $)
    fpprmod $p |- ( N e. NN -> ( FPPr ` N ) = { x e. ( ZZ>= ` 4 ) |
                       ( x e/ Prime /\ ( ( N ^ ( x - 1 ) ) mod x ) = 1 ) } ) $=
      ( cn wcel cfppr cfv cv cprime wnel c1 cmin co cexp cdvds wbr wa c4 cuz cz
      crab cmo wceq fppr c2 wb uzuzle24 cn0 nnz eluz4nn nnm1nn0 zexpcl modm1div
      syl syl2an syl2an2 bicomd anbi2d rabbidva eqtrd ) BCDZBEFAGZHIZVABVAJKLZM
      LZJKLNOZPZAQRFZTVBVDVAUALJUBZPZAVGTABUCUTVFVIAVGUTVAVGDZPZVEVHVBVKVHVEVJV
      AUDRFDUTVDSDZVHVEUEVAUFUTBSDVCUGDZVLVJBUHVJVACDVMVAUIVAUJUMBVCUKUNVDVAULU
      OUPUQURUS $.

    $d X x $.
    $( A Fermat pseudoprime to the base ` N ` .  (Contributed by AV,
       30-May-2023.) $)
    fpprel $p |- ( N e. NN -> ( X e. ( FPPr ` N ) <-> ( X e. ( ZZ>= ` 4 )
                      /\ X e/ Prime /\ ( ( N ^ ( X - 1 ) ) mod X ) = 1 ) ) ) $=
      ( vx cn wcel cfppr cfv c4 cuz cprime wnel c1 cmin co cexp cmo wceq wa w3a
      cv crab fpprmod eleq2d neleq1 oveq1 oveq2d id oveq12d eqeq1d elrab bitrdi
      anbi12d 3anass bitr4di ) ADEZBAFGZEZBHIGZEZBJKZABLMNZONZBPNZLQZRZRZUSUTVD
      SUOUQBCTZJKZAVGLMNZONZVGPNZLQZRZCURUAZEVFUOUPVNBCAUBUCVMVECBURVGBQZVHUTVL
      VDVGBJUDVOVKVCLVOVJVBVGBPVOVIVAAOVGBLMUEUFVOUGUHUIULUJUKUSUTVDUMUN $.
  $}

  ${
    $d n x $.
    $( The base of a Fermat pseudoprime is a positive integer.  (Contributed by
       AV, 30-May-2023.) $)
    fpprbasnn $p |- ( X e. ( FPPr ` N ) -> N e. NN ) $=
      ( vn vx cn wcel cfppr cfv wi ax-1 wn c0 wceq cv cprime wnel c1 cmin cexp
      co cdvds wbr wa cuz crab df-fppr fvmptndm eleq2 noel pm2.21i biimtrdi syl
      c4 pm2.61i ) AEFZBAGHZFZUOIZUOUQJUOKUPLMZURCEDNZOPUTCNUTQRTSTQRTUAUBUCDUM
      UDHUEGADCUFUGUSUQBLFZUOUPLBUHVAUOBUIUJUKULUN $.
  $}

  $( A Fermat pseudoprime to the base ` N ` is a positive integer.
     (Contributed by AV, 30-May-2023.) $)
  fpprnn $p |- ( X e. ( FPPr ` N ) -> X e. NN ) $=
    ( cn wcel cfppr cfv fpprbasnn c4 cuz cprime wnel c1 cmin co cexp cmo fpprel
    wceq w3a eluz4nn 3ad2ant1 biimtrdi mpcom ) ACDZBAEFDZBCDZABGUDUEBHIFDZBJKZA
    BLMNONBPNLRZSUFABQUGUHUFUIBTUAUBUC $.

  ${
    $d X m y $.
    $( A Fermat pseudoprime to the base 2 is odd.  (Contributed by AV,
       5-Jun-2023.) $)
    fppr2odd $p |- ( X e. ( FPPr ` 2 ) -> X e. Odd ) $=
      ( vy vm c2 wcel c1 cmin co cexp wceq wi cn wb wa cmul adantr cz syl cn0
      cc cfppr cfv codd c4 cuz cprime wnel cmo w3a wn 2nn fpprel ax-mp cv ceven
      wrex eluz4nn eluzelz zeo2ALTV biimprd nnennexALTV syl6an oveq1 id oveq12d
      oveq2d eqeq1d adantl caddc crp 2z a1i nnmulcld nnm1nn0 zexpcl modmuladdim
      sylancr nnrpd syl2anc zcnd zcn 2cnd nncn mulcld 1cnd subadd eqcom syl3anc
      bitrdi subcld npcan1 eqcomd eqcomi oveq2i sub1m1 subdid 3eqtr4a nn0mulcld
      2t1e2 2nn0 eqeltrd expp1d expcld mulcomd eqtrd mul12d wne zmulcld zsubcld
      simpr m2even 1oddALTV zneoALTV sylancl eqneqall syl5com sylbird rexlimdva
      nnz sylbid syld ex com23 imp 3adant2 sylbi pm2.18d ) ADUAUBEZAUCEZYHAUDUE
      UBEZAUFUGZDAFGHZIHZAUHHZFJZUIZYIUJZYIKZDLEZYHYPMUKDAULUMYJYOYRYKYJYONZYQA
      DBUNZOHZJZBLUPZYIYTALEZYQAUOEZUUDYJUUEYOAUQPYTUUFYQYJUUFYQMZYOYJAQEUUGUDA
      URAUSRPUTBAVAVBYJYOUUDYIKYJUUDYOYIYJUUCYOYIKZBLYJUUALEZNZUUCUUHUUJUUCNYOD
      UUBFGHZIHZUUBUHHZFJZYIUUCYOUUNMUUJUUCYNUUMFUUCYMUULAUUBUHUUCYLUUKDIAUUBFG
      VCVFUUCVDVEVGVHUUJUUNYIKZUUCUUIUUOYJUUIUUNUULCUNZUUBOHZFVIHZJZCQUPZYIUUIU
      ULQEZUUBVJEUUNUUTKUUIDQEZUUKSEZUVAVKUUIUUBLEUVCUUIDUUAYSUUIUKVLUUIVDVMZUU
      BVNRZDUUKVOZVQUUIUUBUVDVRUULFCUUBVPVSUUIUUSYICQUUIUUPQEZNZUUSUULUUQGHZFJZ
      YIUVHUULTEZUUQTEZFTEZUVJUUSMUVHUULUVHUVBUVCUVAVKUUIUVCUVGUVEPUVFVQVTUVHUU
      PUUBUVGUUPTEUUIUUPWAVHZUVHDUUAUVHWBZUUIUUATEUVGUUAWCZPZWDZWDUVHWEZUVKUVLU
      VMUIUVJUURUULJUUSUULUUQFWFUURUULWGWIWHUVHUVJDDUUKFGHZIHZUUPUUAOHZGHZOHZFJ
      ZYIUVHUVIUWDFUVHUVIDUWAOHZDUWBOHZGHZUWDUVHUULUWFUUQUWGGUVHUULDUVTFVIHZIHZ
      UWFUVHUUKUWIDIUVHUWIUUKUVHUUKTEZUWIUUKJUUIUWKUVGUUIUUBFUUIDUUAUUIWBUVPWDU
      UIWEWJPUUKWKRWLVFUVHUWJUWADOHUWFUVHDUVTUVOUVHUVTDUUAFGHZOHZSUVHUUBDGHZUUB
      DFOHZGHUVTUWMDUWOUUBGUWODWSWMWNUVHUUBTEUVTUWNJUVRUUBWORUVHDUUAFUVOUVQUVSW
      PWQUVHDUWLDSEUVHWTVLUUIUWLSEUVGUUAVNPWRXAZXBUVHUWADUVHDUVTUVOUWPXCZUVOXDX
      EXEUVHUUPDUUAUVNUVOUVQXFVEUVHUWDUWHUVHDUWAUWBUVOUWQUVHUUPUUAUVNUVQWDWPWLX
      EVGUVHUWDFXGZUWEYIUVHUWDUOEZFUCEUWRUVHUWCQEUWSUVHUWAUWBUVHUVBUVTSEUWAQEVK
      UWPDUVTVOVQUVHUUPUUAUUIUVGXJUUIUUAQEUVGUUAXSPXHXIUWCXKRXLUWDFXMXNYIUWDFXO
      XPXTXQXRYAVHPXTYBXRYCYDYAYEYFYG $.
  $}

  $( 341 is the product of 11 and 31.  (Contributed by AV, 3-Jun-2023.) $)
  11t31e341 $p |- ( ; 1 1 x. ; 3 1 ) = ; ; 3 4 1 $=
    ( c1 c3 c4 cdc 3nn0 1nn0 deccl eqid cmul co nn0cni mullidi 3cn ax-1cn 3p1e4
    addcomli decaddi decmul1c ) AABCDABADZBAADZBAEFGZFFTHFEBACASIJBEFESSUAKLZBA
    CMNOPQUBR $.

  $( Eight to the eighth power modulo nine is one.  (Contributed by AV,
     3-Jun-2023.) $)
  2exp340mod341 $p |- ( ( 2 ^ ; ; 3 4 0 ) mod ; ; 3 4 1 ) = 1 $=
    ( c2 c3 c4 cdc cc0 co c1 3nn0 4nn0 deccl 2nn 1nn0 c8 2nn0 oveq1i caddc cmul
    c6 eqid eqtri cexp cmo c7 1nn decnncl 7nn0 0nn0 0z c5 8nn0 5nn0 3z 6nn0 5cn
    2exp5 2cn 5t2e10 mulcomli 3p1e4 decsuc decmulnc 3t3e9 9p1e10 4cn 3cn 4t3e12
    c9 decmul2c mulridi deceq12i 9nn0 3t2e6 6p6e12 decaddci 2t3e6 2t2e4 3eqtr4i
    decmul1c mod2xi 2t0e0 0p1e1 nncni mul02i 1t1e1 addlidi mullidi 2t4e8 nn0cni
    modxp1i 4t4e16 4p1e5 2p1e3 6t2e12 8cn 8t2e16 7cn 7t2e14 cr wcel crp cle wbr
    6p1e7 clt wceq 1re nnrp ax-mp 0le1 4nn 9re 1lt9 ltleii decltdi modid mp4an
    cn ) ABCDZEDZUAFXRGDZUBFGXTUBFZGAGUCDZEDZEXSGGXTXRGBCHIJZUDUEZKYBEGUCLUFJZU
    GJUHLLAMUIDZBYCBADZGXTYEKMUIUJUKJULBAHNJZLAMCDZEYGGRDZYHXTYEKMCUJIJUHGRLUMJ
    ZYIACADZEYJCYKXTYEKCAINJUHIYLAAGDZEYMACXTYEKAGNLJUHNIAAEDZEYNGAXTYEKAENUGJU
    HLNAGEDZEYOGGXTYEKGELUGJZUHLLAUIBYPYHGXTYEKUKULYILAUIUAFYHXTUBUOOUIAYPUNUPU
    QURZYPADZBDZGPFYSCDBXTQFZGPFYHYHQFYSBCYTYPAYQNJHUSYTSUTUUAYTGPUUABXRQFZBGQF
    ZDYTXRGBHYDLVAUUBYSUUCBBCYPABGXRHHIXRSNLBBQFZGPFVGGPFYPUUDVGGPVBOVCTCBGADVD
    VEVFURVHBVEVIVJTOBAYSCYHRYHYIHNYHSIUMBYHQFZRPFUUDBAQFZDZRPFYSUUEUUGRPBABHHN
    VAOVGRAYPUUGRVKUMUMUUDVGUUFRVBVLVJVCNVMVNTAYHQFABQFZAAQFZDRCDBAANHNVAUUHRUU
    ICVOVPVJTVRVQZVSAYPQFAGQFZAEQFZDYOGEANLUGVAUUKAUULEAUPVIZVTVJTEGPFGEXTQFZGP
    FGGQFWAUUNEGPXTXTYEWBWCZOWDVQZVSAEGYONUGWAYOSUTEAPFAUUNAPFGAQFZAUPWEUUNEAPU
    UOOAUPWFZVQWIAYNQFUUIUUKDYMAGANNLVAUUICUUKAVPUUMVJTECPFCUUNCPFUUICVDWEUUNEC
    PUUOOVPVQVSAYMQFACQFZUUIDYJCAANINVAUUSMUUICWGVPVJTEYKPFYKUUNYKPFCCQFYKYKYLW
    HWEUUNEYKPUUOOWJVQVSMCUIYJUJIWKYJSUTEYHPFYHUUNYHPFYKAQFYHYHYIWHWEUUNEYHPUUO
    OGRBAAGYKNLUMYKSNLUUQGPFAGPFZBUUQAGPUUROWLTWMVRVQWIMUIYBEAGYGNUJUKYGSUGLGRU
    CAMQFLUMXCMAYKWNUPWOURUTYRVHUUJVSAYCQFAYBQFZUULDXSYBEANYFUGVAUVAXRUULEGUCBC
    AGYBNLUFYBSILUUKGPFUUTBUUKAGPUUMOWLTUCAGCDWPUPWQURVHVTVJTUUPVSGWRWSXTWTWSZE
    GXAXBGXTXDXBYAGXEXFXTXQWSUVBYEXTXGXHXIXRGGBCHXJUELLGVGXFXKXLXMXNGXTXOXPT $.

  $( 341 is the (smallest) _Poulet number_ (Fermat pseudoprime to the base 2).
     (Contributed by AV, 3-Jun-2023.) $)
  341fppr2 $p |- ; ; 3 4 1 e. ( FPPr ` 2 ) $=
    ( c3 c4 cdc c1 c2 cfv wcel cprime co cexp cmo cle wbr 3nn0 1nn decnncl nnzi
    cz 1nn0 mpbir3an cfppr cuz wnel cmin wceq 4z 4nn0 deccl 4nn c9 4re 9re 4lt9
    ltleii declei eluz2 cmul wn 2nn0 2re 2lt9 3nn mp2an df-nel 11t31e341 eqcomi
    nprm eleq1i xchbinx mpbir cc0 caddc eqid 1m1e0 decsubi oveq2i 2exp340mod341
    2z oveq1i eqtri cn w3a wb 2nn fpprel ax-mp ) ABCZDCZEUAFGZWHBUBFGZWHHUCZEWH
    DUDIZJIZWHKIZDUEZWJBRGWHRGBWHLMUFWHWGDABNUGUHZOPQWGDBABNUIPSUGBUJUKULUMUNUO
    BWHUPTWKDDCZADCZUQIZHGZURZWQEUBFZGZWRXBGZXAXCERGZWQRGEWQLMVRWQDDSOPQDDEOSUS
    EUJUTULVAUNZUOEWQUPTXDXEWRRGEWRLMVRWRADNOPQADEVBSUSXFUOEWRUPTWQWRVGVCWKWHHG
    WTWHHVDWHWSHWSWHVEVFVHVIVJWNEWGVKCZJIZWHKIDWMXHWHKWLXGEJWGDVKWGDVLIZWHDWPSS
    WHVMXIVMVNVOVPVSVQVTEWAGWIWJWKWOWBWCWDEWHWEWFT $.

  $( 4 is the (smallest) Fermat pseudoprime to the base 1.  (Contributed by AV,
     3-Jun-2023.) $)
  4fppr1 $p |- 4 e. ( FPPr ` 1 ) $=
    ( c4 c1 cfppr cfv wcel cuz cprime wnel cmin co cexp cmo wceq cz ax-mp 4nprm
    4z uzid c3 eqtri nelir 4m1e3 oveq2i 3z 1exp oveq1i cr clt wbr 4re 1lt4 1mod
    mp2an cn w3a wb 1nn fpprel mpbir3an ) ABCDEZAAFDEZAGHZBABIJZKJZALJZBMZANEVA
    QAROAGPUAVEBALJZBVDBALVDBSKJZBVCSBKUBUCSNEVHBMUDSUEOTUFAUGEBAUHUIVGBMUJUKAU
    LUMTBUNEUTVAVBVFUOUPUQBAUROUS $.

  $( Eight to the eighth power modulo nine is one.  (Contributed by AV,
     2-Jun-2023.) $)
  8exp8mod9 $p |- ( ( 8 ^ 8 ) mod 9 ) = 1 $=
    ( c8 cexp co c9 cmo c1 c4 cc0 9nn 0z 1nn0 c2 c7 wcel oveq1i c6 caddc mod2xi
    8nn cmul 4nn0 2nn0 7nn nnzi 8nn0 cc wceq 8cn exp1 ax-mp 2t1e2 cdc 6nn0 3nn0
    3p1e4 eqid decsuc 9cn 7cn 9t7e63 mulcomli 8t8e64 3eqtr4i 2t2e4 0p1e1 mul02i
    c3 1t1e1 2t4e8 cr crp cle wbr clt 1re cn nnrp 0le1 1lt9 modid mp4an eqtri )
    AABCDECFDECZFAGHAFFDISUAJKKALHGFFDISUBJKKAFMLAFDISKMUCUDUEKAFBCZADEAUFNWDAU
    GUHAUIUJOUKPVGULZFQCPGULMDTCZFQCAATCPVGGWEUMUNUOWEUPUQWFWEFQDMWEURUSUTVAOVB
    VCRVDHFQCFHDTCZFQCFFTCVEWGHFQDURVFOVHVCZRVIWHRFVJNDVKNZHFVLVMFDVNVMWCFUGVOD
    VPNWIIDVQUJVRVSFDVTWAWB $.

  $( 9 is the (smallest) Fermat pseudoprime to the base 8.  (Contributed by AV,
     2-Jun-2023.) $)
  9fppr8 $p |- 9 e. ( FPPr ` 8 ) $=
    ( c8 cn wcel c9 cfv c4 cuz cprime c1 co cexp cmo cz cle wbr ltleii mpbir3an
    eluz2 c3 c2 cfppr 8nn wnel cmin wceq w3a 4z 9nn nnzi 4re 4lt9 cmul wn 2z 3z
    9re 2re 3re 2lt3 nprm mp2an df-nel 3t3e9 eqcomi eleq1i xchbinx mpbir oveq2i
    9m1e8 oveq1i 8exp8mod9 eqtri 3pm3.2i fpprel mpbiri ax-mp ) ABCZDAUAECZUBVQV
    RDFGECZDHUCZADIUDJZKJZDLJZIUEZUFVSVTWDVSFMCDMCFDNOUGDUHUIFDUJUPUKPFDRQVTSSU
    LJZHCZUMZSTGECZWHWGWHTMCSMCTSNOUNUOTSUQURUSPTSRQZWISSUTVAVTDHCWFDHVBDWEHWED
    VCVDVEVFVGWCAAKJZDLJIWBWJDLWAAAKVIVHVJVKVLVMADVNVOVP $.

  ${
    $( Alternate definition of a _weak pseudoprime_ ` X ` , which fulfils
       ` ( N ^ X ) == N ` (modulo ` X ` ), see Wikipedia "Fermat pseudoprime",
       ~ https://en.wikipedia.org/wiki/Fermat_pseudoprime , 29-May-2023.
       (Contributed by AV, 31-May-2023.) $)
    dfwppr $p |- ( ( N e. NN /\ X e. NN )
                   -> ( ( ( N ^ X ) mod X ) = ( N mod X )
                        <-> X || ( ( N ^ X ) - N ) ) ) $=
      ( cn wcel wa cexp co cz cmo wceq cmin cdvds wbr wb simpr cn0 nnnn0 zexpcl
      nnz syl2an adantr moddvds syl3anc ) ACDZBCDZEUEABFGZHDZAHDZUFBIGABIGJBUFA
      KGLMNUDUEOUDUHBPDUGUEASZBQABRTUDUHUEUIUAUFABUBUC $.
  $}

  $( A Fermat pseudoprime to the base ` N ` is a _weak pseudoprime_ (see
     Wikipedia "Fermat pseudoprime", 29-May-2023,
     ~ https://en.wikipedia.org/wiki/Fermat_pseudoprime .  (Contributed by AV,
     31-May-2023.) $)
  fpprwppr $p |- ( X e. ( FPPr ` N )
                     -> ( ( N ^ X ) mod X ) = ( N mod X ) ) $=
    ( cn wcel cfppr cfv cexp co cmo wceq fpprbasnn c1 cmul syl2an adantr oveq1d
    wi wa cz sylbid cuz cprime wnel cmin w3a fpprel cn0 nnz eluz4nn nnm1nn0 syl
    c4 zexpcl zred crp nnrpd adantl modcld recnd 1cnd cc nncn cc0 nnne0 mulcand
    oveq1 cr modmulmodr syl3anc eqeq1d zcnd mulcomd expm1t eqcomd eqtrd mulridd
    wne eqeq12d biimpd syl5 sylbird a1d ex 3impd mpcom ) ACDZBAEFDZABGHZBIHZABI
    HZJZABKWFWGBULUAFDZBUBUCZABLUDHZGHZBIHZLJZUEWKABUFWFWLWMWQWKWFWLWMWQWKQZQWF
    WLRZWRWMWSWQAWPMHZALMHZJZWKWSWPLAWSWPWSWOBWSWOWFASDZWNUGDZWOSDWLAUHZWLBCDZX
    DBUIZBUJUKAWNUMNZUNZWLBUODZWFWLBXGUPUQZURUSWSUTWFAVADZWLAVBZOZWFAVCVQWLAVDO
    VEXBWTBIHZXABIHZJZWSWKWTXABIVFWSXQAWOMHZBIHZXPJZWKWSXOXSXPWSXCWOVGDXJXOXSJW
    FXCWLXEOXIXKAWOBVHVIVJWSXTWKWSXSWIXPWJWSXRWHBIWSXRWOAMHZWHWSAWOXNWSWOXHVKVL
    WFXLXFYAWHJWLXMXGXLXFRWHYAABVMVNNVOPWSXAABIWFXAAJWLWFAXMVPOPVRVSTVTWAWBWCWD
    TWE $.

  $( An integer ` X ` which is coprime with an integer ` N ` is a Fermat
     pseudoprime to the base ` N ` iff it is a weak pseudoprime to the base
     ` N ` .  (Contributed by AV, 2-Jun-2023.) $)
  fpprwpprb $p |- ( ( X gcd N ) = 1 -> ( X e. ( FPPr ` N )
             <-> ( ( X e. ( ZZ>= ` 4 ) /\ X e/ Prime )
                   /\ ( N e. NN /\ ( ( N ^ X ) mod X ) = ( N mod X ) ) ) ) ) $=
    ( co c1 wceq cfv wcel wa cmo cmin wi sylbid cdvds wbr adantr syl2anr adantl
    cz wb cmul cgcd cfppr c4 cuz cprime wnel cn fpprbasnn w3a fpprel 3simpa a1i
    cexp fpprwppr jca simprll simprlr eluz4nn cn0 nnnn0d zexpcl moddvds syl3anc
    mpcom nnz cc nncn expm1t oveq1d nnm1nn0 syl mulsubfacd eqtrd breq2d zsubcld
    zcnd 1zzd dvdsmulgcd syl2anc eluzelz gcdcom syl2an eqeq1d biimpd imp oveq2d
    mulridd ex com23 expimpd impcom uzuzle24 modm1div mpbird mpbir3and impbid2
    c2 ) BAUACZDEZBAUBFGZBUCUDFGZBUEUFZHZAUGGZABUMCZBICABICEZHZHZWTXCXGXDWTXCAB
    UHZXDWTXAXBABDJCZUMCZBICDEZUIZXCABUJZXMXCKXDXAXBXLUKULLVDWTXDXFXIABUNUOUOWS
    XHWTWSXHHZWTXAXBXLWSXAXBXGUPWSXAXBXGUQXOXLBXKDJCZMNZXHWSXQXCXGWSXQKZXAXGXRK
    XBXAXDXFXRXAXDHZXFBXEAJCZMNZXRXSBUGGZXERGZARGZXFYASXAYBXDBURZOXDYDBUSGYCXAA
    VEZXABYEUTABVAPXDYDXAYFQZXEABVBVCXSYABXPATCZMNZXRXSXTYHBMXSXTXKATCZAJCYHXSX
    EYJAJXDAVFGZYBXEYJEXAAVGZYEABVHPVIXSXKAXSXKXDYDXJUSGZXKRGZXAYFXAYBYMYEBVJVK
    ZAXJVAZPZVPXDYKXAYLQVLVMVNXSYIBXPABUACZTCZMNZXRXSXPRGYDYIYTSXSXKDYQXSVQVOZY
    GBXPAVRVSXSWSYTXQXSWSYTXQKXSWSHZYTXQUUBYSXPBMUUBYSXPDTCZXPUUBYRDXPTXSWSYRDE
    ZXSWSUUDXSWRYRDXABRGYDWRYREXDUCBVTYFBAWAWBWCWDWEWFXSUUCXPEWSXSXPXSXPUUAVPWG
    OVMVNWDWHWILLLWJOWEWKXOBWQUDFGZYNHZXLXQSXHUUFWSXHUUEYNXCUUEXGXAUUEXBBWLOOXG
    YDYMYNXCXDYDXFYFOXAYMXBYOOYPPUOQXKBWMVKWNXHWTXMSZWSXGUUGXCXDUUGXFXNOQQWOWHW
    P $.

  $( An alternate definition for a Fermat pseudoprime to the base 2.
     (Contributed by AV, 5-Jun-2023.) $)
  fpprel2 $p |- ( X e. ( FPPr ` 2 )
                  <-> ( ( X e. ( ZZ>= ` 2 ) /\ X e. Odd /\ X e/ Prime )
                        /\ ( ( 2 ^ X ) mod X ) = 2 ) ) $=
    ( c2 cfv wcel w3a co cmo wceq wa c4 c1 wb 3ad2ant1 adantr cr wbr clt 2re c3
    a1i cfppr cuz codd cprime wnel cexp cmin cn 2nn fpprel mp1i uzuzle24 adantl
    fppr2odd simpr2 3jca fpprwppr crp cc0 cle eluz4nn nnrpd 0le2 cz eluz2 wi 4z
    zlem1lt mpan 4m1e3 breq1i 3re zre 2lt3 simpr lttrd ex biimtrid sylbid sylbi
    modid syl22anc sylan9eq jca pm2.43i ge2nprmge4 3adant2 simp3 eluz2nn eqcomd
    3imp syl eqeq2d biimpa cgcd gcd2odd1 3ad2ant2 fpprwpprb mpbir2and impbii )
    ABUACDZABUBCDZAUCDZAUDUEZEZBAUFFAGFZBHZIZXAXHXAXAAJUBCDZXDBAKUGFUFFAGFKHZEZ
    XHBUHDZXAXKLXAUIBAUJUKXAXKXHXAXKIZXEXGXMXBXCXDXKXBXAXIXDXBXJAULMUMXAXCXKAUN
    NXAXIXDXJUOUPXAXKXFBAGFZBBAUQXIXDXNBHZXJXIBODZAURDZUSBUTPZBAQPZXOXPXIRTXIAA
    VAVBXRXIVCTXIJVDDZAVDDZJAUTPZEXSJAVEXTYAYBXSYAYBXSVFVFXTYAYBJKUGFZAQPZXSXTY
    AYBYDLVGJAVHVIYDSAQPZYAXSYCSAQVJVKYAYEXSYAYEIZBSAXPYFRTSODYFVLTYAAODYEAVMNB
    SQPYFVNTYAYEVOVPVQVRVSTWKVTZBAWAZWBMWCWDVQVSWEXHXAXIXDIZXLXFXNHZIZXEYIXGXEX
    IXDXBXDXIXCAWFWGZXBXCXDWHWDNXHXLYJXLXHUITXEXGYJXEBXNXFXEXNBXEXPXQXRXSXOXPXE
    RTXBXCXQXDXBAAWIVBMXRXEVCTXEXIXSYLYGWLYHWBWJWMWNWDXHABWOFKHZXAYIYKILXEYMXGX
    CXBYMXDAWPWQNBAWRWLWSWT $.

  $( Fermat's little theorem with base 8 reversed is not generally true:  There
     is an integer ` p ` (for example 9, see ~ 9fppr8 ) so that " ` p ` is
     prime" does not follow from ` 8 ^ p == 8 ` (mod ` p ` ).  (Contributed by
     AV, 3-Jun-2023.) $)
  nfermltl8rev $p |- E. p e. ( ZZ>= ` 3 )
                     -. ( ( ( 8 ^ p ) mod p ) = ( 8 mod p ) -> p e. Prime ) $=
    ( c8 cexp co cmo wceq cprime wcel wi wn c3 wa c9 cn 9nn eleq1 wbr cc0 caddc
    c1 cv cuz cfv wrex elexi oveq2 id oveq12d eqeq12d imbi12d notbid anbi12d cz
    wex cle 3z nnzi 3re 9re 3lt9 ltleii eluz2 mpbir3an 8nn 8nn0 0z 8exp8mod9 cr
    1nn0 crp clt 1re nnrp ax-mp 0le1 1lt9 modid mp4an eqtr4i 8p1e9 cmul addlidi
    8cn mul02i oveq1i mullidi 3eqtr4i modxp1i 9nprm pm3.2i annim mpbi ceqsexv2d
    9cn df-rex mpbir ) BAUAZCDZWQEDZBWQEDZFZWQGHZIZJZAKUBUCZUDWQXEHZXDLZAUNXGMX
    EHZBMCDZMEDZBMEDZFZMGHZIZJZLAMMNOUEWQMFZXFXHXDXOWQMXEPXPXCXNXPXAXLXBXMXPWSX
    JWTXKXPWRXIWQMEWQMBCUFXPUGUHWQMBEUFUIWQMGPUJUKULXHXOXHKUMHMUMHKMUOQUPMOUQKM
    URUSUTVAKMVBVCXLXMJZLXOXLXQBBRMTBMOVDVEVFVIVEBBCDMEDTTMEDZVGTVHHMVJHZRTUOQT
    MVKQXRTFVLMNHXSOMVMVNVOVPTMVQVRVSVTRBSDBRMWADZBSDTBWADBWCWBXTRBSMWNWDWEBWCW
    FWGWHWIWJXLXMWKWLWJWMXDAXEWOWP $.

  $( Fermat's little theorem with base 2 reversed is not generally true:  There
     is an integer ` p ` (for example 341, see ~ 341fppr2 ) so that " ` p ` is
     prime" does not follow from ` 2 ^ p == 2 ` (mod ` p ` ).  (Contributed by
     AV, 3-Jun-2023.) $)
  nfermltl2rev $p |- E. p e. ( ZZ>= ` 3 )
                     -. ( ( ( 2 ^ p ) mod p ) = ( 2 mod p ) -> p e. Prime ) $=
    ( c2 cexp co cmo wceq cprime wcel wn c3 cfv cdc c1 cle 3nn0 deccl 1nn0 0nn0
    cz cc0 cv wi cuz wrex wa wex c4 decex eleq1 oveq2 id oveq12d eqeq12d notbid
    imbi12d anbi12d wbr 3z 4nn0 nn0zi dec0h c9 3re 9re 3lt9 ltleii 3nn 0re 9pos
    decltdi eqbrtri eluz2 mpbir3an cfppr 341fppr2 fpprwppr ax-mp cmul 11t31e341
    decleh eqcomi 2nn0 2re 2lt9 0lt1 3pos nprm mp2an eqneltri pm3.2i annim mpbi
    2z ceqsexv2d df-rex mpbir ) BAUAZCDZWQEDZBWQEDZFZWQGHZUBZIZAJUCKZUDWQXEHZXD
    UEZAUFXGJUGLZMLZXEHZBXICDZXIEDZBXIEDZFZXIGHZUBZIZUEAXIXHMUHWQXIFZXFXJXDXQWQ
    XIXEUIXRXCXPXRXAXNXBXOXRWSXLWTXMXRWRXKWQXIEWQXIBCUJXRUKULWQXIBEUJUMWQXIGUIU
    OUNUPXJXQXJJSHXISHJXINUQURXIXHMJUGOUSPZQPUTJTJLXINJOVATXHJMRXSOQJVBVCVDVEVF
    JUGTVGUSRTVBVHVDVIVFVJVTVKJXIVLVMXNXOIZUEXQXNXTXIBVNKHXNVOBXIVPVQXIMMLZJMLZ
    VRDZGYCXIVSWAYABUCKZHZYBYDHZYCGHIYEBSHZYASHBYANUQWMYAMMQQPUTBTBLZYANBWBVAZT
    MBMRQWBQBVBWCVDWDVFZWEVTVKBYAVLVMYFYGYBSHBYBNUQWMYBJMOQPUTBYHYBNYITJBMROWBQ
    YJWFVTVKBYBVLVMYAYBWGWHWIWJXNXOWKWLWJWNXDAXEWOWP $.

  ${
    $d a p $.
    $( Fermat's little theorem reversed is not generally true:  There are
       integers ` a ` and ` p ` so that " ` p ` is prime" does not follow from
       ` a ^ p == a ` (mod ` p ` ).  (Contributed by AV, 3-Jun-2023.) $)
    nfermltlrev $p |- E. a e. ZZ E. p e. ( ZZ>= ` 3 )
                      -. ( ( ( a ^ p ) mod p ) = ( a mod p ) -> p e. Prime ) $=
      ( cv cexp co cmo wceq cprime wcel wi wn c3 cuz cfv wrex cz wa 8nn oveq1
      c8 wex cn elexi oveq1d eqeq12d imbi1d notbid rexbidv anbi12d nfermltl8rev
      eleq1 nnzi pm3.2i ceqsexv2d df-rex mpbir ) BCZACZDEZURFEZUQURFEZGZURHIZJZ
      KZALMNZOZBPOUQPIZVGQZBUAVITPIZTURDEZURFEZTURFEZGZVCJZKZAVFOZQBTTUBRUCUQTG
      ZVHVJVGVQUQTPUKVRVEVPAVFVRVDVOVRVBVNVCVRUTVLVAVMVRUSVKURFUQTURDSUDUQTURFS
      UEUFUGUHUIVJVQTRULAUJUMUNVGBPUOUP $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Goldbach's conjectures
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  <HTML>
  According to Wikipedia ("Goldbach's conjecture", 20-Jul-2020,
  ~ https://en.wikipedia.org/wiki/Goldbach's_conjecture ) "Goldbach's
  conjecture ... states: Every even integer greater than 2 can be expressed as
  the sum of two primes."  "It is also known as strong, even or binary Goldbach
  conjecture, to distinguish it from a weaker conjecture, known ... as the
  _Goldbach's weak conjecture_, the _odd Goldbach conjecture_, or the _ternary
  Goldbach conjecture_.  This weak conjecture asserts that all odd numbers
  greater than 7 are the sum of three odd primes.".  In the following, the
  terms "binary Goldbach conjecture" resp. "ternary Goldbach conjecture" will
  be used (following the terminology used in [Helfgott] p. 2), because there
  are a strong and a weak version of the ternary Goldbach conjecture.  The term
  _Goldbach partition_ is used for a sum of two resp. three (odd) primes
  resulting in an even resp. odd number without further specialization.
  <br><br>

  Using the definition of a _Goldbach number_, which is "a positive even
  integer that can be expressed as the sum of two odd primes." (see ~ df-gbe ),
  "another form of the statement of Goldbach's conjecture is that all even
  integers greater than 4 are Goldbach numbers.".  4 is not a Goldbach number,
  but it is the sum of two primes (2 and 2) nevertheless. ~ sbgoldbalt shows
  that both forms are equivalent.
  <br><br>

  Hint (see Wikipedia, ("Goldbach's weak conjecture", 26-Jul-2020,
  ~ https://en.wikipedia.org/wiki/Goldbach's_weak_conjecture ): "Some state the
  [[weak] conjecture as 'Every odd number greater than 7 can be expressed as
  the sum of three odd primes.'  This version excludes 7 = 2+2+3 because this
  requires the even prime 2.  On odd numbers larger than 7 it is slightly
  stronger as it also excludes sums like 17 = 2+2+13, which are allowed in the
  other formulation.  Helfgott's proof [see below] covers both versions of the
  conjecture.  Like the other formulation, this one also immediately follows
  from Goldbach's strong conjecture."  The definition of "weak odd Goldbach
  numbers", see ~ df-gbow , is the basis for "the other formulation", to
  formulate the weak ternary Goldbach conjecture.  Alternately, ~ df-gbo
  provides a definition of "(strong) odd Goldbach numbers" allowing for stating
  the strong ternary Goldbach conjecture.  In literature, the term "Goldbach
  number" is used for "even Goldbach numbers" (according to definition
  ~ df-gbe ), whereas there seems to be no explicit names and definitions for
  "odd Goldbach numbers".  Since there are more theorems for "strong odd
  Goldbach numbers", "odd Goldbach numbers" refers to "strong odd Goldbach
  numbers" in the following. Otherwise, the term "weak odd Goldbach
  numbers" is explicitly used.
  <br><br>

  In contrast to the two versions of the binary Goldbach conjecture, the two
  versions of the ternary Goldbach conjecture are different not only for small
  numbers, but the strong version excludes cases like a=2+2+b in general, e.g.,
  23=2+2+19.  Therefore, it seems to be more difficult to prove the strong
  ternary Goldbach conjecture than the weak version, because there are fewer
  possible partitions available.
  <br><br>

  Although the binary Goldbach conjecture is not proven yet, the ternary
  Goldbach conjecture was proven by Harald Helfgott in 2014 (the weak as well
  as the strong version, see Main theorem in [Helfgott] p. 2).  It would be
  great if this proof can be formalized with Metamath (although it is not in
  the Metamath 100 list).  This section should be a starting point for this.
  <br><br>

  The main problem will be to provide means to express the results from
  checking "small" numbers (performed with a computer): numbers up to about
  4 x 10^18 for the binary Goldbach conjecture (see section 2 in [OeSilva]
  p. 2042, called "even Goldbach conjecture" here) resp. about 9 x 10^30 for
  the ternary Goldbach conjecture (see section 1.2.2 in [Helfgott] p. 4) or
  8 x 10^26 (see theorem 2.1 in [OeSilva] p. 2057, called "odd Goldbach
  conjecture" here).  Maybe each of the results must be provided as theorem,
  like ~ 6gbe , which would be quite a lot...
  <br><br>

  As proposed in the Google group discussion
  ~ https://groups.google.com/g/metamath/c/DOXS4pg0h8w , this problem could be
  solved by using a reflective verifier or adding a concept of verification
  certificates that can be added into the Metamath databases as a reference.
  To sidestep the computation problem for now, the corresponding theorems are
  temporarily provided as axioms, see ~ ax-bgbltosilva , ~ ax-hgprmladder and
  ~ ax-tgoldbachgt .

  <h1>Summary/glossary:</h1>

  <table border="1" id="goldbach-glossary0">
  <tr><th>Term</th><th>Synonyms</th><th>Label fragment</th>
      <th>Definition/Theorem</th><th>Remarks</th></tr>
  <tr><td><b>binary Goldbach partition</b></td>
      <td>simply "Goldbach partition"</td>
      <td></td>
      <td></td>
      <td>A pair of primes (p,q) that sum to an even integer 2n=p+q</td>
      <td>See ~ https://mathworld.wolfram.com/GoldbachPartition.html </td></tr>
  <tr><td><b>weak Goldbach partition</b></td>
      <td></td>
      <td>gbpart</td>
      <td></td>
      <td>A sum of two resp. three primes resulting in an even resp. odd number
          without further specialization.</td>
      <td></td></tr>
  <tr><td><b>Goldbach partition</b></td>
      <td></td>
      <td>gbpart</td>
      <td></td>
      <td>A sum of two resp. three <b>odd</b> primes resulting in an even resp.
          odd number without further specialization.</td>
      <td></td></tr>
  <tr><td><b>even Goldbach number</b></td>
      <td>simply "Goldbach number"</td>
      <td>gbe</td>
      <td> ~ df-gbe </td>
      <td>A positive even integer that can be expressed as the sum of two odd
          primes.</td>
      <td>See ~ https://mathworld.wolfram.com/GoldbachNumber.html </td></tr>
  <tr><td><b>weak odd Goldbach number</b></td>
      <td></td>
      <td>gbow</td>
      <td> ~ df-gbow </td>
      <td>A positive odd integer that can be expressed as the sum of three
          primes.</td>
      <td></td></tr>
  <tr><td><b>odd Goldbach number</b></td>
      <td>strong odd Goldbach number</td>
      <td>gbo</td>
      <td> ~ df-gbo </td>
      <td>A positive odd integer that can be expressed as the sum of three
          <b>odd</b> primes.</td>
      <td></td></tr>
  <tr><td><b>strong binary Goldbach conjecture</b></td>
      <td>"the" Goldbach conjecture" [[*1], even Goldbach conjecture [[*2]</td>
      <td>sbgoldb</td>
      <td></td>
      <td>Every even integer greater than 4 can be expressed as the sum of two
          <b>odd</b> primes.</td>
      <td>[[*1] Equation (1) in [ApostolNT] p. 304 or [[*2] introduction of
          [OeSilva] p. 2033. </td></tr>
  <tr><td><b>binary Goldbach conjecture</b>[[*1][[*3]</td>
      <td>strong Goldbach conjecture [[*1], even Goldbach conjecture [[*1], or
          simply "the Goldbach conjecture" [[*1][[*2]</td>
      <td>bgoldb, b</td>
      <td> ~ sbgoldbb </td>
      <td>Every even integer greater than 2 can be expressed as the sum of two
          primes.</td>
      <td>See [[*1] ~ https://en.wikipedia.org/wiki/Goldbach's_conjecture ,
          [[*2] statement in [ApostolNT] p. 9 or [[*3] section 1.1 in
          [Helfgott] p. 2.</td></tr>
  <tr><td><b>weak ternary Goldbach conjecture</b></td>
      <td>Goldbach's weak conjecture [[*1], odd Goldbach conjecture [[*1][[*3],
          ternary Goldbach conjecture [[*2],  ternary Goldbach problem[[*1],
          three-primes problem [[*1][[*2]</td>
      <td>wtgoldb, wt</td>
      <td> ~ stgoldbwt , ~ sbgoldbwt </td>
      <td>Every odd number greater than 5 can be expressed as the sum of three
          primes.</td>
      <td>See [[*1] ~ https://en.wikipedia.org/wiki/Goldbach's_weak_conjecture,
          [[*2] section 1.1 in [Helfgott] p. 2 or [[*3] section 2.4 in
          [OeSilva] p. 2057.</td></tr>
  <tr><td><b>ternary Goldbach conjecture</b></td>
      <td>strong ternary Goldbach conjecture, the "weak" Goldbach
          conjecture</td>
      <td>tgoldb, stgoldb, st</td>
      <td> ~ sbgoldbst </td>
      <td>Every odd number greater than 7 can be expressed as the sum of three
          <b>odd</b> primes.</td>
      <td>See ~ https://en.wikipedia.org/wiki/Goldbach's_weak_conjecture ,
          ~ https://mathworld.wolfram.com/GoldbachConjecture.html or section
          7.4 in [Helfgott] p. 71.</td></tr>
  <tr><td><b>Goldbach's original conjecture (modern version)</b></td>
      <td>the "ternary" Goldbach conjecture</td>
      <td>mogoldb, m</td>
      <td> ~ sbgoldbm </td>
      <td>Every integer greater than 5 can be written as the sum of three
          primes.</td>
      <td>See ~ https://en.wikipedia.org/wiki/Goldbach's_weak_conjecture ,
          and ~ https://mathworld.wolfram.com/GoldbachConjecture.html
          </td></tr>
  <tr><td><b>Goldbach's original conjecture (original version)</b></td>
      <td></td>
      <td>ogoldb, o</td>
      <td> ~ sbgoldbo </td>
      <td>Every integer greater than 2 can be written as the sum of three
          "primes" (considered the number 1 to be a "prime").</td>
      <td>See ~ https://en.wikipedia.org/wiki/Goldbach's_weak_conjecture ,
          and ~ https://mathworld.wolfram.com/GoldbachConjecture.html
          </td></tr>
  </table>
  </HTML>

$)

  $c GoldbachEven GoldbachOddW GoldbachOdd $.

  $( Extend the definition of a class to include the set of even numbers which
     have a Goldbach partition. $)
  cgbe $a class GoldbachEven $.

  $( Extend the definition of a class to include the set of odd numbers which
     can be written as a sum of three primes. $)
  cgbow $a class GoldbachOddW $.

  $( Extend the definition of a class to include the set of odd numbers which
     can be written as a sum of three odd primes. $)
  cgbo $a class GoldbachOdd $.

  ${
    $d z p q r $.
    $( Define the set of (even) Goldbach numbers, which are positive even
       integers that can be expressed as the sum of two odd primes.  By this
       definition, the binary Goldbach conjecture can be expressed as
       ` A. n e. Even ( 4 < n -> n e. GoldbachEven ) ` .  (Contributed by AV,
       14-Jun-2020.) $)
    df-gbe $a |- GoldbachEven = { z e. Even | E. p e. Prime E. q e. Prime
                                 ( p e. Odd /\ q e. Odd /\ z = ( p + q ) ) } $.

    $( Define the set of weak odd Goldbach numbers, which are positive odd
       integers that can be expressed as the sum of three primes.  By this
       definition, the weak ternary Goldbach conjecture can be expressed as
       ` A. m e. Odd ( 5 < m -> m e. GoldbachOddW ) ` .  (Contributed by AV,
       14-Jun-2020.) $)
    df-gbow $a |- GoldbachOddW = { z e. Odd | E. p e. Prime E. q e. Prime
                                 E. r e. Prime z = ( ( p + q ) + r ) } $.

    $( Define the set of (strong) odd Goldbach numbers, which are positive odd
       integers that can be expressed as the sum of three _odd_ primes.  By
       this definition, the strong ternary Goldbach conjecture can be expressed
       as ` A. m e. Odd ( 7 < m -> m e. GoldbachOdd ) ` .  (Contributed by AV,
       26-Jul-2020.) $)
    df-gbo $a |- GoldbachOdd = { z e. Odd | E. p e. Prime E. q e. Prime
                           E. r e. Prime ( ( p e. Odd /\ q e. Odd /\ r e. Odd )
                                           /\ z = ( ( p + q ) + r ) ) } $.
  $}

  ${
    $d Z z p q r $.
    $( The predicate "is an even Goldbach number".  An even Goldbach number is
       an even integer having a Goldbach partition, i.e. which can be written
       as a sum of two odd primes.  (Contributed by AV, 20-Jul-2020.) $)
    isgbe $p |- ( Z e. GoldbachEven <-> ( Z e. Even
                            /\ E. p e. Prime E. q e. Prime
                               ( p e. Odd /\ q e. Odd /\ Z = ( p + q ) ) ) ) $=
      ( vz cv codd wcel caddc co wceq w3a cprime wrex ceven cgbe eqeq1 2rexbidv
      3anbi3d df-gbe elrab2 ) CEZFGZBEZFGZDEZUAUCHIZJZKZBLMCLMUBUDAUFJZKZBLMCLM
      DANOUEAJZUHUJCBLLUKUGUIUBUDUEAUFPRQDBCST $.

    $( The predicate "is a weak odd Goldbach number".  A weak odd Goldbach
       number is an odd integer having a Goldbach partition, i.e. which can be
       written as a sum of three primes.  (Contributed by AV, 20-Jul-2020.) $)
    isgbow $p |- ( Z e. GoldbachOddW
                  <-> ( Z e. Odd /\ E. p e. Prime E. q e. Prime E. r e. Prime
                                    Z = ( ( p + q ) + r ) ) ) $=
      ( vz cv caddc co wceq cprime wrex codd cgbow eqeq1 rexbidv df-gbow elrab2
      2rexbidv ) EFZDFCFGHBFGHZIZBJKZCJKDJKATIZBJKZCJKDJKEALMSAIZUBUDDCJJUEUAUC
      BJSATNOREBCDPQ $.

    $( The predicate "is an odd Goldbach number".  An odd Goldbach number is an
       odd integer having a Goldbach partition, i.e. which can be written as
       sum of three odd primes.  (Contributed by AV, 26-Jul-2020.) $)
    isgbo $p |- ( Z e. GoldbachOdd
                  <-> ( Z e. Odd /\ E. p e. Prime E. q e. Prime E. r e. Prime
                                    ( ( p e. Odd /\ q e. Odd /\ r e. Odd )
                                      /\ Z = ( ( p + q ) + r ) ) ) ) $=
      ( vz cv codd wcel w3a caddc co wceq cprime wrex cgbo eqeq1 anbi2d rexbidv
      wa 2rexbidv df-gbo elrab2 ) DFZGHCFZGHBFZGHIZEFZUCUDJKUEJKZLZSZBMNZCMNDMN
      UFAUHLZSZBMNZCMNDMNEAGOUGALZUKUNDCMMUOUJUMBMUOUIULUFUGAUHPQRTEBCDUAUB $.

    $( An even Goldbach number is even.  (Contributed by AV, 25-Jul-2020.) $)
    gbeeven $p |- ( Z e. GoldbachEven -> Z e. Even ) $=
      ( vp vq cgbe wcel ceven cv codd caddc wceq w3a cprime wrex isgbe simplbi
      co ) ADEAFEBGZHECGZHEAQRIPJKCLMBLMACBNO $.

    $( A weak odd Goldbach number is odd.  (Contributed by AV, 25-Jul-2020.) $)
    gbowodd $p |- ( Z e. GoldbachOddW -> Z e. Odd ) $=
      ( vp vq vr cgbow wcel codd cv caddc co wceq cprime wrex isgbow simplbi )
      AEFAGFABHCHIJDHIJKDLMCLMBLMADCBNO $.

    $( A (strong) odd Goldbach number is a weak Goldbach number.  (Contributed
       by AV, 26-Jul-2020.) $)
    gbogbow $p |- ( Z e. GoldbachOdd -> Z e. GoldbachOddW ) $=
      ( vp vq vr codd wcel cv w3a caddc co wceq wa cprime wrex cgbo cgbow simpr
      reximi anim2i isgbo isgbow 3imtr4i ) AEFZBGZEFCGZEFDGZEFHZAUDUEIJUFIJKZLZ
      DMNZCMNZBMNZLUCUHDMNZCMNZBMNZLAOFAPFULUOUCUKUNBMUJUMCMUIUHDMUGUHQRRRSADCB
      TADCBUAUB $.

    $( An odd Goldbach number is odd.  (Contributed by AV, 26-Jul-2020.) $)
    gboodd $p |- ( Z e. GoldbachOdd -> Z e. Odd ) $=
      ( cgbo wcel cgbow codd gbogbow gbowodd syl ) ABCADCAECAFAGH $.
  $}

  ${
    $d Z p q r $.
    $( Any even Goldbach number is positive.  (Contributed by AV,
       20-Jul-2020.) $)
    gbepos $p |- ( Z e. GoldbachEven -> Z e. NN ) $=
      ( vp vq cgbe wcel ceven cv codd caddc co wceq w3a cprime wrex wa cn isgbe
      wi prmnn nnaddcl syl2an eleq1 imbitrrid 3ad2ant3 com12 a1i rexlimdvv imp
      sylbi ) ADEAFEZBGZHEZCGZHEZAUKUMIJZKZLZCMNBMNZOAPEZACBQUJURUSUJUQUSBCMMUK
      MEZUMMEZOZUQUSRRUJUQVBUSUPULVBUSRUNVBUSUPUOPEZUTUKPEUMPEVCVAUKSUMSUKUMTUA
      AUOPUBUCUDUEUFUGUHUI $.

    $( Any weak odd Goldbach number is positive.  (Contributed by AV,
       20-Jul-2020.) $)
    gbowpos $p |- ( Z e. GoldbachOddW -> Z e. NN ) $=
      ( vp vq vr cgbow wcel codd cv caddc co wceq cprime wrex wa isgbow anim12i
      cn wi prmnn adantr nnaddcl syl adantl nnaddcld eleq1 syl5ibrcom rexlimdva
      a1i rexlimdvv imp sylbi ) AEFAGFZABHZCHZIJZDHZIJZKZDLMZCLMBLMZNAQFZADCBOU
      LUTVAULUSVABCLLUMLFZUNLFZNZUSVARRULVDURVADLVDUPLFZNZVAURUQQFVFUOUPVFUMQFZ
      UNQFZNZUOQFVDVIVEVBVGVCVHUMSUNSPTUMUNUAUBVEUPQFVDUPSUCUDAUQQUEUFUGUHUIUJU
      K $.

    $( Any odd Goldbach number is positive.  (Contributed by AV,
       26-Jul-2020.) $)
    gbopos $p |- ( Z e. GoldbachOdd -> Z e. NN ) $=
      ( cgbo wcel cgbow cn gbogbow gbowpos syl ) ABCADCAECAFAGH $.

    $( Any even Goldbach number is greater than 5.  (Contributed by AV,
       20-Jul-2020.) $)
    gbegt5 $p |- ( Z e. GoldbachEven -> 5 < Z ) $=
      ( vp vq wcel w3a cprime wa c5 clt wbr wi c3 ancoms cz cle cr c6 a1i imp
      ex cgbe ceven cv codd caddc wceq wrex isgbe cuz cfv oddprmuzge3 eluz2 zre
      co 3re pm3.2i pm3.22 le2add sylancr ancomsd 3p3e6 breq1i 5lt6 5re readdcl
      ltletr syl3anc mpani biimtrid syld syl2an adantl com23 exp4b 3imp 3adant1
      6re com13 sylbi an4s 3adant3 impcom wb breq2 3ad2ant3 mpbird rexlimdvv )
      AUADAUBDZBUCZUDDZCUCZUDDZAWIWKUEUNZUFZEZCFUGBFUGZGHAIJZACBUHWHWPWQWHWOWQB
      CFFWIFDZWKFDZGZWOWQKKWHWTWOWQWTWOGWQHWMIJZWOWTXAWJWLWTXAKWNWJWLGWTXAWJWRW
      LWSXAWJWRGWILUIUJZDZWKXBDZXAWLWSGWRWJXCWIUKMWSWLXDWKUKMXCXDXAXCLNDZWINDZL
      WIOJZEZXDXAKLWIULXDXEWKNDZLWKOJZEZXHXALWKULXFXGXKXAKZXEXFXGXLXKXGXFXAXEXI
      XJXGXFXAKZKXEXIXJXGXMXEXIGXFXJXGGZXAXIXFXNXAKZKXEXIXFXOXIWKPDZWIPDZXOXFWK
      UMWIUMXPXQGZXNLLUEUNZWMOJZXAXRXGXJXTXRLPDZYAGXQXPGXGXJGXTKYAYAUOUOUPXPXQU
      QLLWIWKURUSUTXTQWMOJZXRXAXSQWMOVAVBXRHQIJZYBXAVCXRHPDZQPDZWMPDZYCYBGXAKYD
      XRVDRYEXRVQRXQXPYFWIWKVEMHQWMVFVGVHVIVJVKTVLVMVNVOVRSVPVIVSSVKVTTWAWBWOWQ
      XAWCZWTWNWJYGWLAWMHIWDWEVLWFTRWGSVS $.

    $( Any weak odd Goldbach number is greater than 5.  (Contributed by AV,
       20-Jul-2020.) $)
    gbowgt5 $p |- ( Z e. GoldbachOddW -> 5 < Z ) $=
      ( vp vq vr wcel caddc co cprime wa c5 wbr wi c2 cz anim12i cr 3ad2ant2 c4
      cle c6 cgbow codd wceq wrex clt isgbow w3a cuz cfv prmuz2 eluz2 sylib zre
      cv 2re pm3.2i jctil simp3 le2add sylc 2p2e4 breq1i zaddcl zred adantr 4re
      simpr 4p2e6 5lt6 5re a1i 6re zaddcld ltletr syl3anc mpani biimtrid expcom
      com12 imp exp31 breq2 syl5ibrcom syl2an rexlimdva adantl rexlimdvva sylbi
      mpd ) AUAEAUBEZABUNZCUNZFGZDUNZFGZUCZDHUDZCHUDBHUDZIJAUEKZADCBUFWJWRWSWJW
      QWSBCHHWKHEZWLHEZIZWQWSLWJXBWPWSDHXBMNEZWKNEZMWKSKZUGZXCWLNEZMWLSKZUGZIZX
      CWNNEZMWNSKZUGZWPWSLWNHEZWTXFXAXIWTWKMUHUIZEXFWKUJMWKUKULXAWLXOEXIWLUJMWL
      UKULOXNWNXOEXMWNUJMWNUKULXJXMIWSWPJWOUEKZXJXMXPXJMMFGZWMSKZXMXPLZXJMPEZXT
      IZWKPEZWLPEZIZIXEXHIXRXJYDYAXFYBXIYCXDXCYBXEWKUMQXGXCYCXHWLUMQOXTXTUOUOUP
      UQXFXEXIXHXCXDXEURXCXGXHUROMMWKWLUSUTXFXIXRXSLZXDXCXIYELXEXIXDYEXGXCXDYEL
      XHXDXGYEXRRWMSKZXDXGIZXSXQRWMSVAVBYGYFXMXPYGYFIZXMIZRMFGZWOSKZXPYIRPEZXTI
      ZWMPEZWNPEZIZIYFXLIYKYIYPYMYHYNXMYOYGYNYFYGWMWKWLVCZVDVEXKXCYOXLWNUMQOYLX
      TVFUOUPUQYHYFXMXLYGYFVGXCXKXLURORMWMWNUSUTYHXMYKXPLZYGXMYRLYFXMYGYRXKXCYG
      YRLXLYGXKYRYKTWOSKZYGXKIZXPYJTWOSVHVBYTJTUEKZYSXPVIYTJPEZTPEZWOPEUUAYSIXP
      LUUBYTVJVKUUCYTVLVKYTWOYTWMWNYGWMNEXKYQVEYGXKVGVMVDJTWOVNVOVPVQVRQVSVEVTW
      IWAVQVRQVSQVTWIVTAWOJUEWBWCWDWEWFWGVTWH $.

    $( Any weak odd Goldbach number is greater than or equal to 7.  Because of
       ~ 7gbow , this bound is strict.  (Contributed by AV, 20-Jul-2020.) $)
    gbowge7 $p |- ( Z e. GoldbachOddW -> 7 <_ Z ) $=
      ( vp vq vr wcel c5 clt wbr c7 cle caddc co wi cz sylancr codd cprime wrex
      c6 cv cgbow gbowgt5 c1 cn gbowpos wb 5nn nnzi nnz zltp1le biimpd syl wceq
      wo 5p1e6 breq1i cr 6re nnred leloe bitrid 6nn 6p1e7 imbitrdi isgbow eleq1
      nnzd wa ceven wn 6even evennodd pm2.21 mp2b biimtrrdi com12 adantr sylbid
      sylbi jaod syld mpd ) AUAEZFAGHZIAJHZAUBWCWDFUCKLZAJHZWEWCAUDEZWDWGMAUEZW
      HWDWGWHFNEANEZWDWGUFFUGUHAUIFAUJOUKULWCWGSAGHZSAUMZUNZWEWGSAJHZWCWMWFSAJU
      OUPWCSUQEAUQEWNWMUFURWCAWIUSSAUTOVAWCWKWEWLWCWKSUCKLZAJHZWEWCSNEZWJWKWPMS
      VBUHWCAWIVGWQWJVHWKWPSAUJUKOWOIAJVCUPVDWCAPEZABTCTKLDTKLUMDQRCQRBQRZVHWLW
      EMZADCBVEWRWTWSWLWRWEWLWRSPEZWESAPVFSVIEXAVJXAWEMVKSVLXAWEVMVNVOVPVQVSVTV
      RWAWB $.

    $( Any odd Goldbach number is greater than or equal to 9.  Because of
       ~ 9gbo , this bound is strict.  (Contributed by AV, 26-Jul-2020.) $)
    gboge9 $p |- ( Z e. GoldbachOdd -> 9 <_ Z ) $=
      ( vp vq vr wcel codd cv w3a caddc co wa cprime wrex c9 cle c3 oddprmuzge3
      wbr c6 cr cgbo isgbo wi df-3an an6 cuz cfv 6p3e9 cz eluzelz zaddcl syl2an
      wceq zred eluzelre anim12i 3impa 6re 3re pm3.2i jctil 3p3e6 eluzle le2add
      sylc eqbrtrrid 3adant3 3ad2ant3 jca syl3an sylbi sylanbr breq2 syl5ibrcom
      expimpd rexlimdva a1i rexlimdvv imp ) AUAEAFEZBGZFEZCGZFEZDGZFEZHZAWAWCIJ
      ZWEIJZUMZKZDLMZCLMBLMZKNAORZADCBUBVTWMWNVTWLWNBCLLWALEZWCLEZKZWLWNUCUCVTW
      QWKWNDLWQWELEZKZWGWJWNWSWGKWNWJNWIORZWSWOWPWRHZWGWTWOWPWRUDXAWGKWOWBKZWPW
      DKZWRWFKZHWTWOWPWRWBWDWFUEXBWAPUFUGZEZXCWCXEEZXDWEXEEZWTWAQWCQWEQXFXGXHHZ
      NSPIJZWIOUHXISTEZPTEZKZWHTEZWETEZKZKSWHORZPWEORZKXJWIORXIXPXMXFXGXHXPXFXG
      KZXNXHXOXSWHXFWAUIEWCUIEWHUIEXGPWAUJPWCUJWAWCUKULUNPWEUOUPUQXKXLURUSUTVAX
      IXQXRXFXGXQXHXSSPPIJZWHOVBXSXLXLKZWATEZWCTEZKZKPWAORZPWCORZKXTWHORXSYDYAX
      FYBXGYCPWAUOPWCUOUPXLXLUSUSUTVAXFYEXGYFPWAVCPWCVCUPPPWAWCVDVEVFVGXHXFXRXG
      PWEVCVHVISPWHWEVDVEVFVJVKVLAWINOVMVNVOVPVQVRVSVK $.
  $}

  $( Any even Goldbach number is greater than or equal to 6.  Because of
     ~ 6gbe , this bound is strict.  (Contributed by AV, 20-Jul-2020.) $)
  gbege6 $p |- ( Z e. GoldbachEven -> 6 <_ Z ) $=
    ( cgbe wcel cn c5 clt wbr c6 cle gbepos gbegt5 c1 caddc co 5nn nnzi zltp1le
    cz wb nnz sylancr biimpd 5p1e6 breq1i imbitrdi sylc ) ABCADCZEAFGZHAIGZAJAK
    UGUHELMNZAIGZUIUGUHUKUGERCARCUHUKSEOPATEAQUAUBUJHAIUCUDUEUF $.

  $( The Goldbach partition of 6.  (Contributed by AV, 20-Jul-2020.) $)
  gbpart6 $p |- 6 = ( 3 + 3 ) $=
    ( c3 caddc co c6 3p3e6 eqcomi ) AABCDEF $.

  $( The (weak) Goldbach partition of 7.  (Contributed by AV, 20-Jul-2020.) $)
  gbpart7 $p |- 7 = ( ( 2 + 2 ) + 3 ) $=
    ( c2 caddc co c3 c4 c7 2p2e4 oveq1i 4p3e7 eqtr2i ) AABCZDBCEDBCFKEDBGHIJ $.

  $( The Goldbach partition of 8.  (Contributed by AV, 20-Jul-2020.) $)
  gbpart8 $p |- 8 = ( 3 + 5 ) $=
    ( c3 c5 caddc co c8 5cn 3cn 5p3e8 addcomli eqcomi ) ABCDEBAEFGHIJ $.

  $( The (strong) Goldbach partition of 9.  (Contributed by AV,
     26-Jul-2020.) $)
  gbpart9 $p |- 9 = ( ( 3 + 3 ) + 3 ) $=
    ( c3 caddc co c6 c9 3p3e6 oveq1i 6p3e9 eqtr2i ) AABCZABCDABCEJDABFGHI $.

  $( The (strong) Goldbach partition of 11.  (Contributed by AV,
     29-Jul-2020.) $)
  gbpart11 $p |- ; 1 1 = ( ( 3 + 3 ) + 5 ) $=
    ( c3 caddc co c5 c6 c1 cdc 3p3e6 oveq1i 6p5e11 eqtr2i ) AABCZDBCEDBCFFGLEDB
    HIJK $.

  ${
    $d p q r $.
    $( 6 is an even Goldbach number.  (Contributed by AV, 20-Jul-2020.) $)
    6gbe $p |- 6 e. GoldbachEven $=
      ( vp vq c6 cgbe wcel cv codd caddc co wceq cprime wrex c3 3prm 3odd eleq1
      w3a biidd eqeq2d 3anbi123d ceven 6even gbpart6 oveq1 oveq2 mp3an mpbir2an
      3pm3.2i rspc2ev isgbe ) CDECUAEAFZGEZBFZGEZCUKUMHIZJZQZBKLAKLZUBMKEZUSMGE
      ZUTCMMHIZJZQZURNNUTUTVBOOUCUHUQVCUTUNCMUMHIZJZQABMMKKUKMJZULUTUNUNUPVEUKM
      GPVFUNRVFUOVDCUKMUMHUDSTUMMJZUTUTUNUTVEVBVGUTRUMMGPVGVDVACUMMMHUESTUIUFCB
      AUJUG $.

    $( 7 is a weak odd Goldbach number.  (Contributed by AV, 20-Jul-2020.) $)
    7gbow $p |- 7 e. GoldbachOddW $=
      ( vp vq vr c7 cgbow wcel codd cv caddc co wceq cprime wrex c2 2prm oveq1d
      c3 oveq2 eqeq2d rexbidv gbpart7 rspceeqv mp2an oveq1 rspc2ev mp3an isgbow
      7odd 3prm mpbir2an ) DEFDGFDAHZBHZIJZCHZIJZKZCLMZBLMALMZUHNLFZUSDNNIJZUNI
      JZKZCLMZUROOQLFDUTQIJZKVCUIUACQLVAVDDUNQUTIRUBUCUQVCDNULIJZUNIJZKZCLMABNN
      LLUKNKZUPVGCLVHUOVFDVHUMVEUNIUKNULIUDPSTULNKZVGVBCLVIVFVADVIVEUTUNIULNNIR
      PSTUEUFDCBAUGUJ $.

    $( 8 is an even Goldbach number.  (Contributed by AV, 20-Jul-2020.) $)
    8gbe $p |- 8 e. GoldbachEven $=
      ( vp vq c8 cgbe wcel ceven cv codd caddc co wceq w3a cprime wrex c5 eleq1
      c3 biidd eqeq2d 3anbi123d 8even 5prm 3prm 5odd 5p3e8 eqcomi 3pm3.2i oveq1
      3odd oveq2 rspc2ev mp3an isgbe mpbir2an ) CDECFEAGZHEZBGZHEZCUOUQIJZKZLZB
      MNAMNZUAOMEQMEOHEZQHEZCOQIJZKZLZVBUBUCVCVDVFUDUIVECUEUFUGVAVGVCURCOUQIJZK
      ZLABOQMMUOOKZUPVCURURUTVIUOOHPVJURRVJUSVHCUOOUQIUHSTUQQKZVCVCURVDVIVFVKVC
      RUQQHPVKVHVECUQQOIUJSTUKULCBAUMUN $.

    $( 9 is an odd Goldbach number.  (Contributed by AV, 26-Jul-2020.) $)
    9gbo $p |- 9 e. GoldbachOdd $=
      ( vp vq vr c9 wcel codd cv w3a caddc co wceq wa cprime wrex c8 3prm eleq1
      c3 3odd eqeq2d cgbo c1 df-9 ceven 8even evenp1odd eqeltri 3pm3.2i gbpart9
      ax-mp pm3.2i 3anbi3d oveq2 anbi12d rspcev 3anbi1d rexbidv 3anbi2d rspc2ev
      mp2an oveq1 oveq1d mp3an isgbo mpbir2an ) DUAEDFEAGZFEZBGZFEZCGZFEZHZDVFV
      HIJZVJIJZKZLZCMNZBMNAMNZDOUBIJZFUCOUDEVSFEUEOUFUJUGRMEZVTRFEZWAVKHZDRRIJZ
      VJIJZKZLZCMNZVRPPVTWAWAWAHZDWCRIJZKZLZWGPWHWJWAWAWASSSUHUIUKWFWKCRMVJRKZW
      BWHWEWJWLVKWAWAWAVJRFQULWLWDWIDVJRWCIUMTUNUOUTVQWGWAVIVKHZDRVHIJZVJIJZKZL
      ZCMNABRRMMVFRKZVPWQCMWRVLWMVOWPWRVGWAVIVKVFRFQUPWRVNWODWRVMWNVJIVFRVHIVAV
      BTUNUQVHRKZWQWFCMWSWMWBWPWEWSVIWAWAVKVHRFQURWSWOWDDWSWNWCVJIVHRRIUMVBTUNU
      QUSVCDCBAVDVE $.

    $( 11 is an odd Goldbach number.  (Contributed by AV, 29-Jul-2020.) $)
    11gbo $p |- ; 1 1 e. GoldbachOdd $=
      ( vp vq vr c1 wcel codd cv w3a caddc co wceq wa cprime c6 c5 eleq1 eqeq2d
      wrex c3 anbi12d cdc cgbo 6p5e11 ceven 6even 5odd epoo mp2an eqeltrri 3prm
      3pm3.2i gbpart11 pm3.2i 3anbi3d oveq2 rspcev 3anbi1d oveq1 oveq1d rexbidv
      5prm 3odd 3anbi2d rspc2ev mp3an isgbo mpbir2an ) DDUAZUBEVHFEAGZFEZBGZFEZ
      CGZFEZHZVHVIVKIJZVMIJZKZLZCMRZBMRAMRZNOIJZVHFUCNUDEOFEZWBFEUEUFNOUGUHUISM
      EZWDSFEZWEVNHZVHSSIJZVMIJZKZLZCMRZWAUJUJOMEWEWEWCHZVHWGOIJZKZLZWKVAWLWNWE
      WEWCVBVBUFUKULUMWJWOCOMVMOKZWFWLWIWNWPVNWCWEWEVMOFPUNWPWHWMVHVMOWGIUOQTUP
      UHVTWKWEVLVNHZVHSVKIJZVMIJZKZLZCMRABSSMMVISKZVSXACMXBVOWQVRWTXBVJWEVLVNVI
      SFPUQXBVQWSVHXBVPWRVMIVISVKIURUSQTUTVKSKZXAWJCMXCWQWFWTWIXCVLWEWEVNVKSFPV
      CXCWSWHVHXCWRWGVMIVKSSIUOUSQTUTVDVEVHCBAVFVG $.
  $}

  $( If the strong ternary Goldbach conjecture is valid, then the weak ternary
     Goldbach conjecture holds, too.  (Contributed by AV, 27-Jul-2020.) $)
  stgoldbwt $p |- ( A. n e. Odd ( 7 < n -> n e. GoldbachOdd )
                    -> A. n e. Odd ( 5 < n -> n e. GoldbachOddW ) ) $=
    ( c7 clt wbr wcel wi c5 cgbow codd wa a1d ex cle c6 wceq wo cz caddc com12
    c1 cv cgbo pm3.35 gbogbow syl wn oddz zred 7re a1i lenltd leloed adantr 6nn
    cr co nnzi jctir adantl df-7 breq2i biimpi df-6 wb zltp1le sylancr eqbrtrid
    5nn biimpa anim12ci zgeltp1eq sylc orcd olc jaoi expd sylbid eleq1 evennodd
    ceven 6even pm2.21d mp1i 7gbow mpbiri syl6d sylbird a1dd pm2.61i ralimia )
    BAUAZCDZWKUBEZFZGWKCDZWKHEZFZAIWLWKIEZWNWQFZFWLWSWRWLWNWQWLWNJWMWQWLWMUCWMW
    PWOWKUDKUELKWLUFZWRWQWNWRWTWQWRWTWKBMDZWQWRWKBWRWKWKUGZUHZBUOEWRUIUJZUKWRXA
    WOWKNOZWKBOZPZWPWRXAWKBCDZXFPZWOXGFZWRWKBXCXDULXIWRXJXIWRWOXGXHWRWOJZXGFXFX
    HXKXGXHXKJZXEXFXLWKQEZNQEZJZNWKMDZWKNTRUPZCDZJXEXKXOXHXKXMXNWRXMWOXBUMNUNUQ
    URUSXHXRXKXPXHXRBXQWKCUTVAVBXKNGTRUPZWKMVCWRWOXSWKMDZWRGQEXMWOXTVDGVHUQXBGW
    KVEVFVIVGVJNWKVKVLVMLXFXGXKXFXEVNKVOVPSVQXGWRWPXEWRWPFXFXEWRNIEZWPWKNIVRNVT
    EZYAWPFXEWAYBYAWPNVSWBWCVQXFWPWRXFWPBHEWDWKBHVRWEKVOSWFWGSWHWIWJ $.

  ${
    $d m n p q r $.
    $( If the strong binary Goldbach conjecture is valid, then the (weak)
       ternary Goldbach conjecture holds, too.  (Contributed by AV,
       20-Jul-2020.) $)
    sbgoldbwt $p |- ( A. n e. Even ( 4 < n -> n e. GoldbachEven )
                      -> A. m e. Odd ( 5 < m -> m e. GoldbachOddW ) ) $=
      ( vp vq vr c4 clt wbr wcel wi codd caddc co cle c6 wceq c7 wa c3 cprime
      cv cgbe ceven wral c5 cgbow cz oddz c1 wb 5nn nnzi zltp1le mpan wo breq1i
      5p1e6 cr 6re a1i zre leloed bitrid 6nn 6p1e7 7re cmin simpr 3odd omoeALTV
      jctir breq2 eleq1 imbi12d rspcv 3syl 4p3e7 eqcomi 4re 3re ltaddsub biimpd
      w3a syl3anc biimtrid impcom adantr pm2.27 syl wrex isgbe cc zcn 3cn npcan
      eqcomd oveq2 eqcoms sylan9eq rspcedeq2vd eqeq2d rexbidv imbitrid 3ad2ant3
      oveq1 com12 ad4antlr reximdva jctild isgbow imbitrrdi adantld 3syld com23
      3prm ex 7gbow mpbii a1d jaoi 6even evennodd pm2.21d ax-mp biimtrrdi com24
      sylbid mpcom ralrimiva ) FBUAZGHZYJUBIZJZBUCUDZUEAUAZGHZYOUFIZJZAKYOKIZYN
      YRYOUGIZYSYNYRJYOUHYTYPYNYSYQYTYPUEUILMZYONHZYNYSYQJZJZUEUGIYTYPUUBUJUEUK
      ULUEYOUMUNYTUUBOYOGHZOYOPZUOZUUDUUBOYONHYTUUGUUAOYONUQUPYTOYOOURIYTUSUTYO
      VAZVBVCUUGYTUUDUUEYTUUDJZUUFYTUUEUUDYTUUEOUILMZYONHZUUDOUGIYTUUEUUKUJOVDU
      LOYOUMUNYTUUKQYOGHZQYOPZUOZUUDUUKQYONHYTUUNUUJQYONVEUPYTQYOQURIYTVFUTUUHV
      BVCUUNYTUUDUULUUIUUMUULYTUUDUULYTRZYSYNYQUUOYSYNYQJUUOYSRZYNFYOSVGMZGHZUU
      QUBIZJZUUSYQUUPYSSKIZRUUQUCIZYNUUTJUUPYSUVAUUOYSVHZVIVKYOSVJYMUUTBUUQUCYJ
      UUQPYKUURYLUUSYJUUQFGVLYJUUQUBVMVNVOVPUUPUURUUTUUSJUUOUURYSYTUULUURUULFSL
      MZYOGHZYTUURQUVDYOGUVDQVQVRUPYTFURIZSURIZYOURIZUVEUURJUVFYTVSUTUVGYTVTUTU
      UHUVFUVGUVHWCUVEUURFSYOWAWBWDWEWFWGUURUUSWHWIUUSUVBCUAZKIZDUAZKIZUUQUVIUV
      KLMZPZWCZDTWJZCTWJZRUUPYQUUQDCWKUUPUVQYQUVBUUPUVQYSYOUVMEUAZLMZPZETWJZDTW
      JZCTWJZRYQUUPUVQUWCYSUUPUVPUWBCTUUPUVITIZRUVOUWADTYTUVOUWAJUULYSUWDUVKTIU
      VOYTUWAUVNUVJYTUWAJUVLYTYOUUQUVRLMZPZETWJUVNUWAYTESTYOUWESTIYTXOUTYTUVRSP
      YOUUQSLMZUWEYTYOWLIZSWLIZRZYOUWGPYTUWHUWIYOWMWNVKUWJUWGYOYOSWOWPWIUWGUWEP
      SUVRSUVRUUQLWQWRWSWTUVNUWFUVTETUVNUWEUVSYOUUQUVMUVRLXEXAXBXCXDXFXGXHXHUVC
      XIYOEDCXJXKXLWEXMXPXNXPUUMUUDYTUUMUUCYNUUMYQYSUUMQUFIYQXQQYOUFVMXRXSXSXSX
      TXFYGYGXFUUFUUDYTUUFUUCYNUUFYSOKIZYQOYOKVMOUCIZUWKYQJYAUWLUWKYQOYBYCYDYEX
      SXSXTXFYGYGYFYHWFYI $.

    $( If the strong binary Goldbach conjecture is valid, then the (strong)
       ternary Goldbach conjecture holds, too.  (Contributed by AV,
       26-Jul-2020.) $)
    sbgoldbst $p |- ( A. n e. Even ( 4 < n -> n e. GoldbachEven )
                      -> A. m e. Odd ( 7 < m -> m e. GoldbachOdd ) ) $=
      ( vp vq vr c4 cv clt wbr wcel wi codd wa c3 co wceq caddc a1i cprime wrex
      cgbe ceven wral c7 cgbo cmin simpl 3odd jctir omoeALTV breq2 imbi12d 3syl
      eleq1 rspcv 4p3e7 breq1i 4re 3re oddz zred ltaddsubd biimpd biimtrrid imp
      cr pm2.27 syl w3a isgbe 3prm wb 3anbi3d oveq2 eqeq2d anbi12d adantl simp1
      simp2 3jca cc zcnd ad3antrrr 3cn cz zaddcl syl2an adantll subadd2d biimpa
      prmz eqcomd 3ad2antr3 rspcedvd ex reximdva jctild isgbo imbitrrdi adantld
      jca biimtrid 3syld com12 expd ralrimiv ) FBGZHIZXGUAJZKZBUBUCZUDAGZHIZXLU
      EJZKALXKXLLJZXMXNXOXMMZXKXNXPXKFXLNUFOZHIZXQUAJZKZXSXNXPXONLJZMXQUBJZXKXT
      KXPXOYAXOXMUGZUHUIXLNUJXJXTBXQUBXGXQPXHXRXIXSXGXQFHUKXGXQUAUNULUOUMXPXRXT
      XSKXOXMXRXMFNQOZXLHIZXOXRYDUDXLHUPUQXOYEXRXOFNXLFVFJXOURRNVFJXOUSRXOXLXLU
      TZVAVBVCVDVEXRXSVGVHXSYBCGZLJZDGZLJZXQYGYIQOZPZVIZDSTZCSTZMXPXNXQDCVJXPYO
      XNYBXPYOXOYHYJEGZLJZVIZXLYKYPQOZPZMZESTZDSTZCSTZMXNXPYOUUDXOXPYNUUCCSXPYG
      SJZMZYMUUBDSUUFYISJZMZYMUUBUUHYMMZUUAYHYJYAVIZXLYKNQOZPZMZENSNSJUUIVKRYPN
      PZUUAUUMVLUUIUUNYRUUJYTUULUUNYQYAYHYJYPNLUNVMUUNYSUUKXLYPNYKQVNVOVPVQUUIU
      UJUULYMUUJUUHYMYHYJYAYHYJYLVRYHYJYLVSYAYMUHRVTVQUUHYHYLUULYJUUHYLMUUKXLUU
      HYLUUKXLPUUHXLNYKXOXLWAJXMUUEUUGXOXLYFWBWCNWAJUUHWDRUUEUUGYKWAJXPUUEUUGMY
      KUUEYGWEJYIWEJYKWEJUUGYGWKYIWKYGYIWFWGWBWHWIWJWLWMXAWNWOWPWPYCWQXLEDCWRWS
      WTXBXCXDXEXF $.
  $}

  $( Lemma 1 for ~ sbgoldbalt :  If an even number greater than 4 is the sum of
     two primes, one of the prime summands must be odd, i.e. not 2.
     (Contributed by AV, 22-Jul-2020.) $)
  sbgoldbaltlem1 $p |- ( ( P e. Prime /\ Q e. Prime )
                -> ( ( N e. Even /\ 4 < N /\ N = ( P + Q ) ) -> Q e. Odd ) ) $=
    ( cprime wcel wa ceven c4 clt wbr caddc co wceq w3a wi c2 evenprm2 biimtrdi
    wb adantl codd wn cn prmnn nneoALTV bicomd bitrd oveq2 eqeq2d 3anbi3d breq2
    syl eleq1 anbi12d cz prmz 2evenALTV evensumeven sylancl oveq1 eqtrdi breq2d
    2p2e4 4re ltnri pm2.21i sylbird com13 expd 3imp com12 adantr sylbid ex ax-1
    imp pm2.61d2 ) ADEZBDEZFZBUAEZCGEZHCIJZCABKLZMZNZWAOZVTWAUBZBPMZWGVSWHWISVR
    VSWHBGEZWIVSBUCEZWHWJSBUDWKWJWHBUEUFULBQUGTVRWIWGOVSVRWIWGVRWIFZWFWBWCCAPKL
    ZMZNZWAWLWEWNWBWCWIWEWNSVRWIWDWMCBPAKUHUITUJVRWOWAOWIWOVRWAWBWCWNVRWAOZWNWC
    WBWPWNWCWBWPWNWCWBFHWMIJZWMGEZFWPWNWCWQWBWRCWMHIUKCWMGUMUNWQWRWPVRWRWQWAVRW
    RAGEZWQWAOZVRAUOEPGEWSWRSAUPUQAPURUSVRWSAPMZWTAQXAWQHHIJZWAXAWMHHIXAWMPPKLH
    APPKUTVCVAVBXBWAHVDVEVFRRVGVHVPRVIVHVJVKVLVMVNVLVMWAWFVOVQ $.

  $( Lemma 2 for ~ sbgoldbalt :  If an even number greater than 4 is the sum of
     two primes, the primes must be odd, i.e. not 2.  (Contributed by AV,
     22-Jul-2020.) $)
  sbgoldbaltlem2 $p |- ( ( P e. Prime /\ Q e. Prime )
                        -> ( ( N e. Even /\ 4 < N /\ N = ( P + Q ) )
                             -> ( P e. Odd /\ Q e. Odd ) ) ) $=
    ( cprime wcel wa ceven c4 clt wbr caddc co wceq codd wi prmz sbgoldbaltlem1
    w3a cc zcnd addcom syl2anr eqeq2d 3anbi3d sylbid ancoms jcad ) ADEZBDEZFCGE
    ZHCIJZCABKLZMZRZANEZBNEUIUHUNUOOUIUHFZUNUJUKCBAKLZMZRUOUPUMURUJUKUPULUQCUHA
    SEBSEULUQMUIUHAAPTUIBBPTABUAUBUCUDBACQUEUFABCQUG $.

  ${
    $d n p q $.
    $( An alternate (related to the original) formulation of the binary
       Goldbach conjecture:  Every even integer greater than 2 can be expressed
       as the sum of two primes.  (Contributed by AV, 22-Jul-2020.) $)
    sbgoldbalt $p |- ( A. n e. Even ( 4 < n -> n e. GoldbachEven )
                       <-> A. n e. Even ( 2 < n
                           -> E. p e. Prime E. q e. Prime n = ( p + q ) ) ) $=
      ( c4 clt wbr wcel wi c2 caddc co wceq cprime wrex cle c3 cr a1i wa codd
      cv cgbe ceven c1 cz wb evenz zltp1le sylancr 2p1e3 breq1i 3re zred leloed
      2z wo 3z 3p1e4 4re pm3.35 w3a isgbe simp3 reximdva imp sylbi a1d ex com23
      2prm 2p2e4 eqcomi rspceov mp3an eqeq1 2rexbidv mpbii jaoi sylbid biimtrid
      syl com12 wn 3odd eleq1 oddneven pm2.21d 2lt4 2re lttr mpani simpll simpr
      syl3anc anim1i adantr df-3an sylibr sbgoldbaltlem2 sylanbrc jca imbitrrdi
      sylc embantd impbid ralbiia ) DAUAZEFZXGUBGZHZIXGEFZXGCUAZBUAZJKZLZBMNZCM
      NZHZAUCXGUCGZXJXRXSXKXJXQXSXKIUDJKZXGOFZXJXQHZXSIUEGXGUEGZXKYAUFUOXGUGZIX
      GUHUIYAPXGOFZXSYBXTPXGOUJUKXSYEPXGEFZPXGLZUPZYBXSPXGPQGXSULRXSXGYDUMZUNYH
      XSYBYFXSYBHZYGXSYFYBXSYFPUDJKZXGOFZYBXSPUEGYCYFYLUFUQYDPXGUHUIYLDXGOFZXSY
      BYKDXGOURUKXSYMXHDXGLZUPZYBXSDXGDQGZXSUSRZYIUNYOXSYBXHYJYNXHXJXSXQXHXJXSX
      QHZXHXJSXIYRXHXIUTXIXQXSXIXSXLTGZXMTGZXOVAZBMNZCMNZSZXQXGBCVBZXSUUCXQXSUU
      BXPCMXSXLMGZSZUUAXOBMUUAXOHUUGXMMGZSYSYTXOVCRVDVDVEVFVGWAVHVIYNYBXSYNXQXJ
      YNDXNLZBMNCMNZXQIMGZUUKDIIJKZLUUJVJVJUULDVKVLCBMMIIDJVMVNYNUUIXOCBMMDXGXN
      VOVPVQVGVGVRWBVSVTVSWBYGXSYBYGXGTGZXSWCYGPTGUUMWDPXGTWEVQXGWFWAWGVRWBVSVT
      VSVIXSXHXRXIXSXHXRXIHXSXHSZXKXQXIXSXHXKXSIDEFZXHXKWHXSIQGZYPXGQGUUOXHSXKH
      UUPXSWIRYQYIIDXGWJWNWKVEUUNXQUUDXIUUNXQUUDUUNXQSXSUUCXSXHXQWLUUNXQUUCUUNX
      PUUBCMUUNUUFSZXOUUABMUUQUUHSZXOUUAUURXOSZYSYTSZXOUUAUUSUUFUUHSZXSXHXOVAZU
      UTUURUVAXOUUQUUFUUHUUNUUFWMWOWPUUSUUNXOSUVBUURUUNXOUUNUUFUUHWLWOXSXHXOWQW
      RXLXMXGWSXCUURXOWMYSYTXOWQWTVHVDVDVEXAVHUUEXBXDVHVIXEXF $.

    $( If the strong binary Goldbach conjecture is valid, the binary Goldbach
       conjecture is valid.  (Contributed by AV, 23-Dec-2021.) $)
    sbgoldbb $p |- ( A. n e. Even ( 4 < n -> n e. GoldbachEven )
                     -> A. n e. Even ( 2 < n
                        -> E. p e. Prime E. q e. Prime n = ( p + q ) ) ) $=
      ( c4 cv clt wbr cgbe wcel wi ceven wral caddc wceq cprime wrex sbgoldbalt
      c2 co biimpi ) DAEZFGUAHIJAKLRUAFGUACEBEMSNBOPCOPJAKLABCQT $.
  $}

  ${
    $d N n p q r $.
    $( If the binary Goldbach conjecture is valid, then an even integer greater
       than 5 can be expressed as the sum of three primes:  Since ` ( N - 2 ) `
       is even iff ` N ` is even, there would be primes ` p ` and ` q ` with
       ` ( N - 2 ) = ( p + q ) ` , and therefore ` N = ( ( p + q ) + 2 ) ` .
       (Contributed by AV, 24-Dec-2021.) $)
    sgoldbeven3prm $p |- ( A. n e. Even ( 4 < n -> n e. GoldbachEven )
                           -> ( ( N e. Even /\ 6 <_ N )
                                -> E. p e. Prime E. q e. Prime E. r e. Prime
                                   N = ( ( p + q ) + r ) ) ) $=
      ( c4 cv clt wbr wcel wi ceven c2 caddc co wceq cprime wrex c6 wa cgbe cle
      wral sbgoldbb cmin 2p2e4 evenz zred 4lt6 4re 6re ltletr mp3an12 mpani syl
      cr imp eqbrtrid 2re a1i ltaddsub2d mpbid 2evenALTV emee mpan2 breq2 eqeq1
      adantr 2rexbidv imbi12d rspcv 2prm wb oveq2 eqeq2d adantl zcnd 2cnd npcan
      cc eqcomd syl2anc simpr oveq1d eqtrd rspcedvd ex reximdv imim2d syl9r mpd
      mpid syl5com ) FAGZHIWNUAJKALUCMWNHIZWNEGDGNOZPZDQREQRZKZALUCZBLJZSBUBIZT
      ZBWPCGZNOZPZCQRZDQRZEQRZADEUDXCWTMBMUEOZHIZXIXCMMNOZBHIXKXCXLFBHUFXAXBFBH
      IZXABUPJZXBXMKXABBUGZUHZXNFSHIZXBXMUIFUPJSUPJXNXQXBTXMKUJUKFSBULUMUNUOUQU
      RXCMMBMUPJXCUSUTZXRXAXNXBXPVHVAVBXAWTXKXIKZKZXBXAXJLJZXTXAMLJYAVCBMVDVEYA
      WTXKXJWPPZDQRZEQRZKZXAXSWSYEAXJLWNXJPZWOXKWRYDWNXJMHVFYFWQYBEDQQWNXJWPVGV
      IVJVKXAYDXIXKXAYCXHEQXAYBXGDQXAYBXGXAYBTZXFBWPMNOZPZCMQMQJYGVLUTXDMPZXFYI
      VMYGYJXEYHBXDMWPNVNVOVPYGBXJMNOZYHXABYKPZYBXABVTJZMVTJZYLXABXOVQXAVRYMYNT
      YKBBMVSWAWBVHYGXJWPMNXAYBWCWDWEWFWGWHWHWIWJWKVHWLWM $.
  $}

  ${
    $d m n p q r $.
    $( If the strong binary Goldbach conjecture is valid, the modern version of
       the original formulation of the Goldbach conjecture also holds:  Every
       integer greater than 5 can be expressed as the sum of three primes.
       (Contributed by AV, 24-Dec-2021.) $)
    sbgoldbm $p |- ( A. n e. Even ( 4 < n -> n e. GoldbachEven )
              -> A. n e. ( ZZ>= ` 6 ) E. p e. Prime E. q e. Prime E. r e. Prime
                                      n = ( ( p + q ) + r ) ) $=
      ( vm c4 cv clt wbr cgbe wcel wi ceven wral caddc co cprime wrex c6 c5 cuz
      wceq cfv breq2 eleq1w imbi12d cbvralvw cz cle w3a eluz2 wo sgoldbeven3prm
      codd zeoALTV expdcom cgbow sbgoldbwt wa rspa c1 df-6 breq1i 5nn nnzi oddz
      wb zltp1le sylancr biimprd biimtrid imp isgbow simprbi a1i embantd adantl
      ex com23 mpd syl com13 jaoi 3adant1 sylbi impcom ralrimiva ) FAGZHIZWHJKZ
      LZAMNFEGZHIZWLJKZLZEMNZWHDGCGOPBGOPUBBQRCQRDQRZASUAUCZNWKWOAEMWHWLUBWIWMW
      JWNWHWLFHUDAEJUEUFUGWPWQAWRWHWRKZWPWQWSSUHKZWHUHKZSWHUIIZUJWPWQLZSWHUKXAX
      BXCWTXAXBXCXAWHMKZWHUNKZULXBXCLZWHUOXDXFXEWPXDXBWQEWHBCDUMUPWPXBXEWQWPTWH
      HIZWHUQKZLZAUNNZXBXEWQLLAEURXJXEXBWQXJXEXBWQLZXJXEUSXIXKXIAUNUTXEXIXKLXJX
      EXBXIWQXEXBXIWQLXEXBUSZXGXHWQXEXBXGXBTVAOPZWHUIIZXEXGSXMWHUIVBVCXEXGXNXET
      UHKXAXGXNVGTVDVEWHVFTWHVHVIVJVKVLXHWQLXLXHXEWQWHBCDVMVNVOVPVRVSVQVTVRVSWA
      WBWCWAVLWDWEWFWGWE $.

    $d n p q r x y $.
    $( If the modern version of the original formulation of the Goldbach
       conjecture is valid, the (weak) binary Goldbach conjecture also holds.
       (Contributed by AV, 26-Dec-2021.) $)
    mogoldbb $p |- ( A. n e. ( ZZ>= ` 6 )
                        E. p e. Prime E. q e. Prime E. r e. Prime
                           n = ( ( p + q ) + r )
                     -> A. n e. Even ( 2 < n
                            -> E. p e. Prime E. q e. Prime n = ( p + q ) ) ) $=
      ( vm vy vx cv caddc co wceq cprime wrex c6 c2 wbr wi wcel wa cle cuz wral
      cfv clt ceven nfra1 eqeq1 rexbidv 2rexbidv cbvralvw cz 6nn nnzi a1i evenz
      2z zaddcld adantr cmin c4 4cn 2cn 4p2e6 mvrraddi 2p2e4 2evenALTV evenltle
      eqcomi mp3an2 eqbrtrrid eqbrtrid cr w3a wb 6re 2re zred 3jca lesubadd syl
      mpbid eluz2 syl3anbrc rspcv biimtrid nfv nfre1 nfcv simplrl simplrr simpr
      nfrexw simp-4l mogoldbblem oveq1 eqeq2d oveq2 cbvrex2vw sylibr rexlimdva2
      syl3anc expr rexlimd ex syldc expd ralrimi ) AHZDHZCHZIJZBHZIJZKZBLMZCLMD
      LMZANUAUCZUBZOXHUDPZXHXKKZCLMZDLMZQAUEXPAXQUFXRXHUERZXSYBYCXSSZXRXHOIJZXM
      KZBLMZCLMZDLMZYBXREHZXMKZBLMZCLMDLMZEXQUBZYDYIXPYMAEXQXHYJKZXOYLDCLLYOXNY
      KBLXHYJXMUGUHUIUJYDYEXQRZYNYIQYDNUKRZYEUKRZNYETPZYPYQYDNULUMUNYCYRXSYCXHO
      XHUOZOUKRYCUPUNUQURYDNOUSJZXHTPZYSYDUUAUTXHTNUTOVAVBUTOIJNVCVHVDYDUTOOIJZ
      XHTVEYCOUERXSUUCXHTPVFOXHVGVIVJVKYDNVLRZOVLRZXHVLRZVMZUUBYSVNYCUUGXSYCUUD
      UUEUUFUUDYCVOUNUUEYCVPUNYCXHYTVQVRURNOXHVSVTWANYEWBWCYMYIEYEXQYJYEKZYLYGD
      CLLUUHYKYFBLYJYEXMUGUHUIWDVTWEYDYHYBDLYDDWFYADLWGYDXILRZYHYBQYDUUISZYGYBC
      LUUJCWFYACDLCLWHXTCLWGWLYDUUIXJLRZYGYBQYDUUIUUKSZSZYFYBBLUUMXLLRZSZYFSUUI
      UUKUUNVMZYCYFYBUUOUUPYFUUOUUIUUKUUNYDUUIUUKUUNWIYDUUIUUKUUNWJUUMUUNWKVRUR
      YCXSUULUUNYFWMUUOYFWKUUPYCYFVMXHFHZGHZIJZKZGLMFLMYBXIXJXLXHGFWNXTUUTXHUUQ
      XJIJZKDCFGLLXIUUQKXKUVAXHXIUUQXJIWOWPXJUURKUVAUUSXHXJUURUUQIWQWPWRWSXAWTX
      BXCXDXCXEXFXG $.

    $( The strong binary Goldbach conjecture and the modern version of the
       original formulation of the Goldbach conjecture are equivalent.
       (Contributed by AV, 26-Dec-2021.) $)
    sbgoldbmb $p |- ( A. n e. Even ( 4 < n -> n e. GoldbachEven )
             <-> A. n e. ( ZZ>= ` 6 ) E. p e. Prime E. q e. Prime E. r e. Prime
                                      n = ( ( p + q ) + r ) ) $=
      ( c4 cv clt wbr cgbe wcel wi ceven wral caddc co wceq cprime wrex c6 cuz
      cfv sbgoldbm c2 mogoldbb sbgoldbalt sylibr impbii ) EAFZGHUHIJKALMZUHDFCF
      NOZBFNOPBQRCQRDQRASTUAMZABCDUBUKUCUHGHUHUJPCQRDQRKALMUIABCDUDACDUEUFUG $.
  $}

  ${
    $d P p q r $.  $d n p q r $.
    sbgoldbo.p $e |- P = ( { 1 } u. Prime ) $.
    $( If the strong binary Goldbach conjecture is valid, the original
       formulation of the Goldbach conjecture also holds:  Every integer
       greater than 2 can be expressed as the sum of three "primes" with
       regarding 1 to be a prime (as Goldbach did).  Original text:  "Es
       scheint wenigstens, dass eine jede Zahl, die groesser ist als 2, ein
       aggregatum trium numerorum primorum sey."  (Goldbach, 1742).
       (Contributed by AV, 25-Dec-2021.) $)
    sbgoldbo $p |- ( A. n e. Even ( 4 < n -> n e. GoldbachEven )
                     -> A. n e. ( ZZ>= ` 3 ) E. p e. P E. q e. P E. r e. P
                                             n = ( ( p + q ) + r ) ) $=
      ( c4 wcel caddc co wceq wrex c3 c6 c1 wb c5 cprime adantl c2 clt wbr cgbe
      cv wi ceven wral cuz cfv nfra1 cmin cfz cun cz cle 3z 6nn nnzi 3re ltleii
      6re 3lt6 eluz2 mpbir3an uzsplit eleq2d ax-mp wo elun csn 6m1e5 oveq2i 5nn
      cfzo 5re 3lt5 fzopredsuc eqtri eleq2i elsni 1ex snid orci eleqtrri a1i wa
      mpbir simpl oveq1 oveq1d eqeq12d 2rexbidv eqeq2d rexbidv df-3 df-2 oveq1i
      oveq2 eqtr4id rspcedeq2vd rspcedvd syl df-5 oveq12i 4z fzval3 eqtr4i fzsn
      3p1e4 bitri 2prm olci df-4 eqcomd eqtrd sylbi jaoi 3prm a1d sbgoldbm rspa
      wss ssun2 sseqtrri rexss simpr reximi ex com12 biimtrid ralrimi ) GBUDZUA
      UBYLUCHUEZBUFUGZYLEUDZDUDZIJZCUDZIJZKZCALZDALZEALZBMUHUIZYMBUFUJYLUUDHZYL
      MNOUKJZULJZNUHUIZUMZHZYNUUCNUUDHZUUEUUJPUUKMUNHZNUNHMNUOUBUPNUQURMNUSVAVB
      UTMNVCVDUUKUUDUUIYLMNVEVFVGUUJYNUUCUUJYLUUGHZYLUUHHZVHYNUUCUEZYLUUGUUHVIU
      UMUUOUUNUUMYLMVJZMOIJZQVNJZUMZQVJZUMZHZUUOUUGUVAYLUUGMQULJZUVAUUFQMULVKVL
      QUUDHZUVCUVAKUVDUULQUNHMQUOUBUPQVMURMQUSVOVPUTMQVCVDMQVQVGVRVSUVBUUCYNUVB
      YLUUSHZYLUUTHZVHUUCYLUUSUUTVIUVEUUCUVFUVEYLUUPHZYLUURHZVHUUCYLUUPUURVIUVG
      UUCUVHUVGYLMKZUUCYLMVTUVIUUBMOYPIJZYRIJZKZCALZDALEOAOAHZUVIOOVJZRUMZAOUVP
      HOUVOHZORHZVHUVQUVROWAWBWCOUVORVIWGFWDZWEZUVIYOOKZWFZYTUVLDCAAUWBYLMYSUVK
      UVIUWAWHUWAYSUVKKUVIUWAYQUVJYRIYOOYPIWIWJSWKWLUVIUVMMOOIJZYRIJZKZCALZDOAU
      VTYPOKZUVMUWFPUVIUWGUVLUWECAUWGUVKUWDMUWGUVJUWCYRIYPOOIWRWJWMWNSUVICOAMUW
      DUVTYROKZUWEUVIUWHMUWCOIJZUWDMTOIJZUWIWOTUWCOIWPWQVRYROUWCIWRWSSWTXAXAXBU
      VHYLGVJZHZUUCUVHYLGGULJZHUWLUURUWMYLUURGGOIJZVNJZUWMUUQGQUWNVNXIXCXDGUNHZ
      UWMUWOKXEGGXFVGXGVSUWMUWKYLUWPUWMUWKKXEGXHVGVSXJUWLYLGKZUUCYLGVTUWQUUBYLT
      YPIJZYRIJZKZCALZDALZETATAHUWQTUVPATUVPHTUVOHZTRHZVHUXDUXCXKXLTUVORVIWGFWD
      WEYOTKZUUBUXBPUWQUXEYTUWTDCAAUXEYSUWSYLUXEYQUWRYRIYOTYPIWIWJWMWLSUWQUXAYL
      UWJYRIJZKZCALZDOAUVNUWQUVSWEZUWGUXAUXHPUWQUWGUWTUXGCAUWGUWSUXFYLUWGUWRUWJ
      YRIYPOTIWRWJWMWNSUWQCOAYLUXFUXIUWQUWHWFZYLGUXFUWQUWHWHUXJGUWJOIJZUXFGUXKK
      UXJGUUQUXKXMMUWJOIWOWQVRWEUWHUXKUXFKUWQUWHUXFUXKYROUWJIWRXNSXOXOWTXAXAXBX
      PXQXPUVFYLQKZUUCYLQVTUXLUUBYLMYPIJZYRIJZKZCALZDALZEMAMAHUXLMUVPAMUVPHMUVO
      HZMRHZVHUXSUXRXRXLMUVORVIWGFWDWEYOMKZUUBUXQPUXLUXTYTUXODCAAUXTYSUXNYLUXTY
      QUXMYRIYOMYPIWIWJWMWLSUXLUXPYLUUQYRIJZKZCALZDOAUVNUXLUVSWEZUWGUXPUYCPUXLU
      WGUXOUYBCAUWGUXNUYAYLUWGUXMUUQYRIYPOMIWRWJWMWNSUXLCOAYLUYAUYDUXLUWHWFYLQU
      YAUXLUWHWHUWHQUYAKUXLUWHQUUQOIJZUYAQUWNUYEXCGUUQOIXMWQVRYROUUQIWRWSSXOWTX
      AXAXBXQXPXSXPYNUUNUUCYNYTCRLZDRLZERLZBUUHUGZUUNUUCUEBCDEXTUYIUUNUUCUYIUUN
      WFUYHUUCUYHBUUHYAUYHYORHZUYGWFZEALZUUCRAYBZUYHUYLPRUVPARUVOYCFYDZUYGERAYE
      VGUYKUUBEAUYGUUBUYJUYGYPRHZUYFWFZDALZUUBUYMUYGUYQPUYNUYFDRAYEVGUYPUUADAUY
      FUUAUYOUYFYRRHZYTWFZCALZUUAUYMUYFUYTPUYNYTCRAYEVGUYSYTCAUYRYTYFYGXPSYGXPS
      YGXPXBYHXBYIXQXPYIYJYK $.
  $}

  ${
    $d d f k $.
    $( 4 is the sum of at most 3 (actually 2) primes.  (Contributed by AV,
       2-Aug-2020.) $)
    nnsum3primes4 $p |- E. d e. NN E. f e. ( Prime ^m ( 1 ... d ) )
                        ( d <_ 3 /\ 4 = sum_ k e. ( 1 ... d ) ( f ` k ) ) $=
      ( c2 cn wcel c3 cle c4 c1 cpr cfv wceq wa cprime co cfz 1ne2 2ex ax-mp cv
      wbr csu cmap wrex 2nn cop wne 1ex fpr wss 2prm pm3.2i prss mpbi fss mpan2
      wf mp2b prmex prex elmap mpbir 2re 3re 2lt3 ltleii caddc cc 2cn cvv fveq2
      fvpr1 eqtrdi fvpr2 id ancri a1i sumpr 2p2e4 eqtr2i fveq1 sumeq2sdv eqeq2d
      jctl anbi2d rspcev mp2an oveq2 df-2 oveq2i cz 1z fzpr 1p1e2 preq2i oveq2d
      eqtri breq1 sumeq1d anbi12d rexeqbidv ) DEFDGHUBZIJDKZBUAZAUAZLZBUCZMZNZA
      OXDUDPZUEZCUAZGHUBZIJXMQPZXGBUCZMZNZAOXOUDPZUEZCEUEUFJDUGDDUGKZXKFZXCIXDX
      EYALZBUCZMZNZXLYBXDOYAURZJDUHZXDDDKZYAURZYGRJDDDUISSSUJYJYIOUKZYGDOFZYLNY
      KYLYLULULUMDDOSSUNUOXDYIOYAUPUQUSOXDYAUTJDVAVBVCXCYEDGVDVEVFVGYDDDVHPZIDV
      IFZYDYMMVJYNJDYCDBDVKVIXEJMYCJYALZDXEJYAVLYHYODMRJDDDUISVMTVNXEDMYCDYALZD
      XEDYAVLYHYPDMRJDDDSSVOTVNYNYNYNVPVQYNJVKFUIWEYHYNRVRVSTVTWAUMXJYFAYAXKXFY
      AMZXIYEXCYQXHYDIYQXDXGYCBXEXFYAWBWCWDWFWGWHXTXLCDEXMDMZXRXJAXSXKYRXOXDOUD
      YRXOJDQPZXDXMDJQWIYSJJJVHPZQPZXDDYTJQWJWKUUAJYTKZXDJWLFUUAUUBMWMJWNTYTDJW
      OWPWRWRVNZWQYRXNXCXQXIXMDGHWSYRXPXHIYRXOXDXGBUUCWTWDXAXBWGWH $.

    $( 4 is the sum of at most 4 (actually 2) primes.  (Contributed by AV,
       23-Jul-2020.)  (Proof shortened by AV, 2-Aug-2020.) $)
    nnsum4primes4 $p |- E. d e. NN E. f e. ( Prime ^m ( 1 ... d ) )
                        ( d <_ 4 /\ 4 = sum_ k e. ( 1 ... d ) ( f ` k ) ) $=
      ( cv c3 cle wbr c4 c1 cfz co cfv csu wceq wa wrex cn wcel cr a1i cmap clt
      cprime nnsum3primes4 3lt4 wi nnre 3re 4re leltletr syl3anc mpan2i reximdv
      anim1d reximia ax-mp ) CDZEFGZHIUQJKZBDADLBMNZOZAUCUSUAKZPZCQPUQHFGZUTOZA
      VBPZCQPABCUDVCVFCQUQQRZVAVEAVBVGURVDUTVGUREHUBGZVDUEVGUQSRESRZHSRZURVHOVD
      UFUQUGVIVGUHTVJVGUITUQEHUJUKULUNUMUOUP $.
  $}

  ${
    $d P d f k $.
    $( Every prime is "the sum of at most 3" (actually one - the prime itself)
       primes.  (Contributed by AV, 2-Aug-2020.)  (Proof shortened by AV,
       17-Apr-2021.) $)
    nnsum3primesprm $p |- ( P e. Prime
                            -> E. d e. NN E. f e. ( Prime ^m ( 1 ... d ) )
                        ( d <_ 3 /\ P = sum_ k e. ( 1 ... d ) ( f ` k ) ) ) $=
      ( cprime wcel c1 cn c3 cle cv csu wceq wa cmap co wrex cfz cr sylancr wbr
      csn cfv 1nn cop wf cz 1zzd id fsnd prmex snex elmap sylibr simpl sumeq2dv
      1re fvsng cc prmz zcnd eqidd sumsn eqtr2d 1le3 jctil elsni adantl fveq12d
      eqeq2d anbi2d rspcev syl2anc oveq2 fzsn ax-mp eqtrdi oveq2d breq1 sumeq1d
      1z anbi12d rexeqbidv ) AEFZGHFGIJUAZAGUBZCKZBKZUCZCLZMZNZBEWFOPZQZDKZIJUA
      ZAGWORPZWICLZMZNZBEWQOPZQZDHQUDWDGAUEUBZWMFZWEAWFGXCUCZCLZMZNZWNWDWFEXCUF
      XDWDGAUGEWDUHWDUIUJEWFXCUKGULUMUNWDXGWEWDXFWFACLZAWDWFXEACWDWGWFFZNGSFZWD
      XEAMUQWDXJUOGASEURTUPWDXKAUSFXIAMUQWDAAUTVAAACGSWGGMZAVBVCTVDVEVFWLXHBXCW
      MWHXCMZWKXGWEXMWJXFAXMWFWIXECXMXJNWGGWHXCXMXJUOXJXLXMWGGVGVHVIUPVJVKVLVMX
      BWNDGHWOGMZWTWLBXAWMXNWQWFEOXNWQGGRPZWFWOGGRVNGUGFXOWFMWAGVOVPVQZVRXNWPWE
      WSWKWOGIJVSXNWRWJAXNWQWFWICXPVTVJWBWCVLT $.

    $( Every prime is "the sum of at most 4" (actually one - the prime itself)
       primes.  (Contributed by AV, 23-Jul-2020.)  (Proof shortened by AV,
       2-Aug-2020.) $)
    nnsum4primesprm $p |- ( P e. Prime
                            -> E. d e. NN E. f e. ( Prime ^m ( 1 ... d ) )
                        ( d <_ 4 /\ P = sum_ k e. ( 1 ... d ) ( f ` k ) ) ) $=
      ( cprime wcel cv c3 cle wbr c1 cfz co cfv wa wrex cn c4 cr a1i csu clt wi
      wceq cmap nnsum3primesprm 3lt4 nnre 3re 4re syl3anc mpan2i anim1d reximdv
      leltletr reximia syl ) AEFDGZHIJZAKURLMZCGBGNCUAUDZOZBEUTUEMZPZDQPURRIJZV
      AOZBVCPZDQPABCDUFVDVGDQURQFZVBVFBVCVHUSVEVAVHUSHRUBJZVEUGVHURSFHSFZRSFZUS
      VIOVEUCURUHVJVHUITVKVHUJTURHRUOUKULUMUNUPUQ $.
  $}

  ${
    $d N d f k p q $.
    $( Any even Goldbach number is the sum of at most 3 (actually 2) primes.
       (Contributed by AV, 2-Aug-2020.) $)
    nnsum3primesgbe $p |- ( N e. GoldbachEven
                            -> E. d e. NN E. f e. ( Prime ^m ( 1 ... d ) )
                        ( d <_ 3 /\ N = sum_ k e. ( 1 ... d ) ( f ` k ) ) ) $=
      ( vp vq wcel cv co wceq cprime wrex wa c3 c1 cfz cfv cn c2 cpr cgbe ceven
      codd caddc w3a cle wbr csu cmap isgbe wi 2nn wb oveq2 df-2 oveq2i cz fzpr
      1z ax-mp 1p1e2 preq2i 3eqtri eqtrdi oveq2d breq1 sumeq1d eqeq2d rexeqbidv
      a1i anbi12d adantl cop wne 1ne2 1ex 2ex vex fpr mp1i prssi fssd cvv prmex
      prex pm3.2i elmapg mpbird fveq1 adantr sumeq2dv eqeq1d anbi2d fveq2 fvpr1
      wf prmz fvpr2 zcn anim12i sumpr syl2an 2re 3re 2lt3 ltleii jctil rspcedvd
      cc eqeq1 eqcom bitrdi rexbidv 3ad2ant3 a1d ex rexlimivv impcom sylbi ) CU
      AGCUBGZEHZUCGZFHZUCGZCYAYCUDIZJZUEZFKLEKLZMDHZNUFUGZCOYIPIZBHZAHZQZBUHZJZ
      MZAKYKUIIZLZDRLZCFEUJYHXTYTYGXTYTUKZEFKKYAKGZYCKGZMZYGUUAUUDYGMZYTXTUUEYS
      SNUFUGZCOSTZYNBUHZJZMZAKUUGUIIZLZDSRSRGZUUEULVJYISJZYSUULUMUUEUUNYQUUJAYR
      UUKUUNYKUUGKUIUUNYKOSPIZUUGYISOPUNUUOOOOUDIZPIZOUUPTZUUGSUUPOPUOUPOUQGZUU
      QUURJUSOURUTUUPSOVAVBVCVDZVEUUNYJUUFYPUUIYISNUFVFUUNYOUUHCUUNYKUUGYNBUUTV
      GVHVKVIVLUUEUULUUFUUHYEJZMZAUUKLZUUDUVCYGUUDUVBUUFUUGYLOYAVMSYCVMTZQZBUHZ
      YEJZMZAUVDUUKUUDUVDUUKGZUUGKUVDWPZUUDUUGYAYCTZKUVDOSVNZUUGUVKUVDWPUUDVOOS
      YAYCVPVQEVRZFVRZVSVTYAYCKWAWBKWCGZUUGWCGZMUVIUVJUMUUDUVOUVPWDOSWEWFKUUGUV
      DWCWCWGVTWHYMUVDJZUVBUVHUMUUDUVQUVAUVGUUFUVQUUHUVFYEUVQUUGYNUVEBUVQYNUVEJ
      YLUUGGYLYMUVDWIWJWKWLWMVLUUDUVGUUFUUBYAUQGZYCUQGZUVGUUCYAWQYCWQUVRUVSMZOS
      UVEYABYCUQRYLOJUVEOUVDQZYAYLOUVDWNUVLUWAYAJVOOSYAYCVPUVMWOUTVDYLSJUVESUVD
      QZYCYLSUVDWNUVLUWBYCJVOOSYAYCVQUVNWRUTVDUVRYAXIGUVSYCXIGYAWSYCWSWTUUSUUMM
      UVTUUSUUMUSULWFVJUVLUVTVOVJXAXBSNXCXDXEXFXGXHWJYGUULUVCUMZUUDYFYBUWCYDYFU
      UJUVBAUUKYFUUIUVAUUFYFUUIYEUUHJUVACYEUUHXJYEUUHXKXLWMXMXNVLWHXHXOXPXQXRXS
      $.

    $( Any even Goldbach number is the sum of at most 4 (actually 2) primes.
       (Contributed by AV, 23-Jul-2020.)  (Proof shortened by AV,
       2-Aug-2020.) $)
    nnsum4primesgbe $p |- ( N e. GoldbachEven
                            -> E. d e. NN E. f e. ( Prime ^m ( 1 ... d ) )
                        ( d <_ 4 /\ N = sum_ k e. ( 1 ... d ) ( f ` k ) ) ) $=
      ( cgbe wcel cv c3 cle wbr c1 cfz co cfv wa wrex cn c4 cr a1i csu wceq clt
      cprime cmap nnsum3primesgbe 3lt4 wi nnre 3re 4re leltletr syl3anc reximdv
      mpan2i anim1d reximia syl ) CEFDGZHIJZCKUSLMZBGAGNBUAUBZOZAUDVAUEMZPZDQPU
      SRIJZVBOZAVDPZDQPABCDUFVEVHDQUSQFZVCVGAVDVIUTVFVBVIUTHRUCJZVFUGVIUSSFHSFZ
      RSFZUTVJOVFUHUSUIVKVIUJTVLVIUKTUSHRULUMUOUPUNUQUR $.

    $( Every integer greater than 1 and less than or equal to 8 is the sum of
       at most 3 primes.  (Contributed by AV, 2-Aug-2020.) $)
    nnsum3primesle9 $p |- ( ( N e. ( ZZ>= ` 2 ) /\ N <_ 8 )
                      -> E. d e. NN E. f e. ( Prime ^m ( 1 ... d ) )
                         ( d <_ 3 /\ N = sum_ k e. ( 1 ... d ) ( f ` k ) ) ) $=
      ( c2 wcel c8 cle wbr wceq c3 wo c4 c5 c6 c7 cprime clt a1i wb cuz cfv cfz
      wa cv c1 co csu cmap wrex cn eluzelre cr 8re leloed caddc cz eluzelz nnzi
      7nn zleltp1 sylancl 7re 7p1e8 breq2i 3bitr3rd 6nn 6re 6p1e7 5nn 5re 5p1e6
      4z 4re 4p1e5 3z 3re 3p1e4 w3a eluz2 wi 2re zre cmin eqcomi breq1i zlem1lt
      3m1e2 mpan biimprd biimtrid lenltd pm2.21 biimtrdi syldc biimpi 2a1d jaoi
      wn eqcom com12 sylbid imp breq1 mpbiri impbid1 3adant1 sylbi orbi1d bitrd
      2lt3 biimpd 2prm eleq1 nnsum3primesprm 3prm nnsum3primes4 anbi2d 2rexbidv
      syl eqeq1 5prm cgbe 6gbe nnsum3primesgbe 7prm 8gbe ) CEUAUBFZCGHIZUDCEJZC
      KJZLZCMJZLZCNJZLZCOJZLZCPJZLZCGJZLZDUEZKHIZCUFUUCUCUGZBUEAUEUBBUHZJZUDZAQ
      UUEUIUGZUJDUKUJZYHYIUUBYHYICGRIZUUALZUUBYHCGECULZGUMFYHUNSUOYHUULUUBYHUUK
      YTUUAYHUUKCPRIZYSLZYTYHCPHIZCPUFUPUGZRIZUUOUUKYHCUQFZPUQFUUPUURTECURZPUTU
      SCPVAVBYHCPUUMPUMFYHVCSUOUURUUKTYHUUQGCRVDVESVFYHUUNYRYSYHUUNCORIZYQLZYRY
      HCOHIZCOUFUPUGZRIZUVBUUNYHUUSOUQFUVCUVETUUTOVGUSCOVAVBYHCOUUMOUMFYHVHSUOU
      VEUUNTYHUVDPCRVIVESVFYHUVAYPYQYHUVACNRIZYOLZYPYHCNHIZCNUFUPUGZRIZUVGUVAYH
      UUSNUQFUVHUVJTUUTNVJUSCNVAVBYHCNUUMNUMFYHVKSUOUVJUVATYHUVIOCRVLVESVFYHUVF
      YNYOYHUVFCMRIZYMLZYNYHCMHIZCMUFUPUGZRIZUVLUVFYHUUSMUQFUVMUVOTUUTVMCMVAVBY
      HCMUUMMUMFYHVNSUOUVOUVFTYHUVNNCRVOVESVFYHUVKYLYMYHUVKCKRIZYKLZYLYHCKHIZCK
      UFUPUGZRIZUVQUVKYHUUSKUQFZUVRUVTTUUTVPCKVAVBYHCKUUMKUMFZYHVQSUOUVTUVKTYHU
      VSMCRVRVESVFYHUVPYJYKYHEUQFZUUSECHIZVSUVPYJTZECVTUUSUWDUWEUWCUUSUWDUDUVPY
      JUUSUWDUVPYJWAZUUSUWDECRIZECJZLZUWFUUSECEUMFUUSWBSCWCZUOUWIUUSUWFUWGUUSUW
      FWAUWHUUSUWGKCHIZUWFUWGKUFWDUGZCRIZUUSUWKEUWLCRUWLEWHWEWFUUSUWKUWMUWAUUSU
      WKUWMTVPKCWGWIWJWKUUSUWKUVPWSUWFUUSKCUWBUUSVQSUWJWLUVPYJWMWNWOUWHYJUUSUVP
      UWHYJECWTWPWQWRXAXBXCYJUVPEKRIXKCEKRXDXEXFXGXHXIXJXIXJXIXJXIXJXIXJXIXLXBX
      CYTUUJUUAYRUUJYSYPUUJYQYNUUJYOYLUUJYMYJUUJYKYJCQFZUUJYJUWNEQFXMCEQXNXECAB
      DXOZXTYKUWNUUJYKUWNKQFXPCKQXNXEUWOXTWRYMUUJUUDMUUFJZUDZAUUIUJDUKUJABDXQYM
      UUHUWQDAUKUUIYMUUGUWPUUDCMUUFYAXRXSXEWRYOUWNUUJYOUWNNQFYBCNQXNXEUWOXTWRYQ
      CYCFZUUJYQUWROYCFYDCOYCXNXEABCDYEZXTWRYSUWNUUJYSUWNPQFYFCPQXNXEUWOXTWRUUA
      UWRUUJUUAUWRGYCFYGCGYCXNXEUWSXTWRXT $.

    $( Every integer greater than 1 and less than or equal to 8 is the sum of
       at most 4 primes.  (Contributed by AV, 24-Jul-2020.)  (Proof shortened
       by AV, 2-Aug-2020.) $)
    nnsum4primesle9 $p |- ( ( N e. ( ZZ>= ` 2 ) /\ N <_ 8 )
                      -> E. d e. NN E. f e. ( Prime ^m ( 1 ... d ) )
                         ( d <_ 4 /\ N = sum_ k e. ( 1 ... d ) ( f ` k ) ) ) $=
      ( c2 cuz cfv wcel c8 cle wbr wa cv c3 co wrex cn c4 cr a1i cfz csu cprime
      c1 wceq cmap nnsum3primesle9 clt 3lt4 wi nnre 3re leltletr syl3anc mpan2i
      4re anim1d reximdv reximia syl ) CEFGHCIJKLDMZNJKZCUDVAUAOZBMAMGBUBUEZLZA
      UCVCUFOZPZDQPVARJKZVDLZAVFPZDQPABCDUGVGVJDQVAQHZVEVIAVFVKVBVHVDVKVBNRUHKZ
      VHUIVKVASHNSHZRSHZVBVLLVHUJVAUKVMVKULTVNVKUPTVANRUMUNUOUQURUSUT $.
  $}

  ${
    $d N f k m p q r $.
    $( If the (weak) ternary Goldbach conjecture is valid, then every odd
       integer greater than 5 is the sum of 3 primes.  (Contributed by AV,
       2-Jul-2020.) $)
    nnsum4primesodd $p |- ( A. m e. Odd ( 5 < m -> m e. GoldbachOddW )
                         -> ( ( N e. ( ZZ>= ` 6 ) /\ N e. Odd )
                              -> E. f e. ( Prime ^m ( 1 ... 3 ) )
                                 N = sum_ k e. ( 1 ... 3 ) ( f ` k ) ) ) $=
      ( vp c6 cfv wcel wa c5 cv wi c1 c3 co wceq cprime cz a1i c2 vq vr cuz clt
      codd wbr cgbow wral cfz csu cmap breq2 eleq1 imbi12d rspcv adantl cle w3a
      wrex eluz2 5lt6 5re 6re zre ltletr syl3anc mpani imp 3adant1 sylbi adantr
      cr pm2.27 syl caddc isgbow cop ctp wf 1ex 2ex 3ex vex 1ne2 1re ltneii 2re
      1lt3 2lt3 1p2e3 eqcomi oveq2i 1z fztp ax-mp eqid id 1p1e2 tpeq123d 3eqtri
      ftp feq2i sylibr wss df-3an tpss sylbb1 fssd cvv prmex ovex pm3.2i elmapg
      wb mp1i mpbird fveq1 sumeq2sdv eqeq2d sumeq1d fveq2 wne fvtp1 mp2an fvtp2
      eqtrdi fvtp3 cc prmz zcnd 3anim123i 3expa 2z 3pm3.2i sumtp rspcedvd eqeq1
      3z eqtr2d rexbidv syl5ibrcom rexlimdva rexlimivv 3syld com12 ) DFUCGHZDUE
      HZIZJCKZUDUFZUUIUGHZLZCUEUHZDMNUIOZBKZAKZGZBUJZPZAQUUNUKOZUSZUUHUUMJDUDUF
      ZDUGHZLZUVCUVAUUGUUMUVDLUUFUULUVDCDUEUUIDPUUJUVBUUKUVCUUIDJUDULUUIDUGUMUN
      UOUPUUHUVBUVDUVCLUUFUVBUUGUUFFRHZDRHZFDUQUFZURUVBFDUTUVFUVGUVBUVEUVFUVGUV
      BUVFJFUDUFZUVGUVBVAUVFJVLHZFVLHZDVLHUVHUVGIUVBLUVIUVFVBSUVJUVFVCSDVDJFDVE
      VFVGVHVIVJVKUVBUVCVMVNUVCUVALUUHUVCUUGDEKZUAKZVOOUBKZVOOZPZUBQUSZUAQUSEQU
      SZIUVADUBUAEVPUVQUVAUUGUVPUVAEUAQQUVKQHZUVLQHZIZUVOUVAUBQUVTUVMQHZIZUVAUV
      OUVNUURPZAUUTUSUWBUWCUVNUUNUUOMUVKVQTUVLVQNUVMVQVRZGZBUJZPZAUWDUUTUWBUWDU
      UTHZUUNQUWDVSZUWBUUNUVKUVLUVMVRZQUWDUWBMTNVRZUWJUWDVSZUUNUWJUWDVSUWLUWBMT
      NUVKUVLUVMVTWAWBEWCZUAWCZUBWCZWDMNWEWHWFZTNWGWIWFZXASUUNUWKUWJUWDUUNMMTVO
      OZUIOZMMMVOOZUWRVRZUWKNUWRMUIUWRNWJWKWLMRHZUWSUXAPWMMWNWOMMPZUXAUWKPMWPUX
      CMMUWTTUWRNUXCWQUWTTPUXCWRSUWRNPUXCWJSWSWOWTZXBXCUVRUVSUWAURUWBUWJQXDUVRU
      VSUWAXEUVKUVLUVMQUWMUWNUWOXFXGXHQXIHZUUNXIHZIUWHUWIXNUWBUXEUXFXJMNUIXKXLQ
      UUNUWDXIXIXMXOXPUUPUWDPZUWCUWGXNUWBUXGUURUWFUVNUXGUUNUUQUWEBUUOUUPUWDXQXR
      XSUPUWBUWFUWKUWEBUJUVNUWBUUNUWKUWEBUUNUWKPUWBUXDSXTUWBMTNUWEBUVKUVLUVMRRR
      UUOMPUWEMUWDGZUVKUUOMUWDYAMTYBZMNYBZUXHUVKPWDUWPMTNUVKUVLUVMVTUWMYCYDYFUU
      OTPUWETUWDGZUVLUUOTUWDYAUXITNYBZUXKUVLPWDUWQMTNUVKUVLUVMWAUWNYEYDYFUUONPU
      WENUWDGZUVMUUONUWDYAUXJUXLUXMUVMPUWPUWQMTNUVKUVLUVMWBUWOYGYDYFUVRUVSUWAUV
      KYHHZUVLYHHZUVMYHHZURUVRUXNUVSUXOUWAUXPUVRUVKUVKYIYJUVSUVLUVLYIYJUWAUVMUV
      MYIYJYKYLUXBTRHZNRHZURUWBUXBUXQUXRWMYMYRYNSUXIUWBWDSUXJUWBUWPSUXLUWBUWQSY
      OYSYPUVOUUSUWCAUUTDUVNUURYQYTUUAUUBUUCUPVJSUUDUUE $.

    $( If the (strong) ternary Goldbach conjecture is valid, then every odd
       integer greater than 7 is the sum of 3 primes.  (Contributed by AV,
       26-Jul-2020.) $)
    nnsum4primesoddALTV $p |- ( A. m e. Odd ( 7 < m -> m e. GoldbachOdd )
                         -> ( ( N e. ( ZZ>= ` 8 ) /\ N e. Odd )
                              -> E. f e. ( Prime ^m ( 1 ... 3 ) )
                                 N = sum_ k e. ( 1 ... 3 ) ( f ` k ) ) ) $=
      ( c8 cfv wcel codd wa c7 cv wi c1 c3 co wceq cprime cz a1i c2 cuz clt wbr
      vp vq vr cgbo wral cfz csu cmap wrex breq2 eleq1 imbi12d rspcv adantl cle
      w3a eluz2 7lt8 7re 8re zre ltletr syl3anc mpani imp 3adant1 adantr pm2.27
      cr sylbi syl caddc isgbo cop ctp 1ex 2ex 3ex vex 1ne2 1re 1lt3 ltneii 2re
      wf 2lt3 ftp 1p2e3 eqcomi oveq2i 1z fztp ax-mp 1p1e2 tpeq123d 3eqtri feq2i
      eqid id sylibr wss df-3an tpss sylbb1 fssd cvv wb ovex pm3.2i elmapg mp1i
      prmex mpbird fveq1 sumeq2sdv eqeq2d sumeq1d fveq2 fvtp1 mp2an fvtp2 fvtp3
      wne eqtrdi cc prmz zcnd 3anim123i 3expa 2z 3z sumtp eqtr2d rspcedvd eqeq1
      3pm3.2i rexbidv syl5ibrcom adantld rexlimdva rexlimivv 3syld com12 ) DEUA
      FGZDHGZIZJCKZUBUCZUUJUGGZLZCHUHZDMNUIOZBKZAKZFZBUJZPZAQUUOUKOZULZUUIUUNJD
      UBUCZDUGGZLZUVDUVBUUHUUNUVELUUGUUMUVECDHUUJDPUUKUVCUULUVDUUJDJUBUMUUJDUGU
      NUOUPUQUUIUVCUVEUVDLUUGUVCUUHUUGERGZDRGZEDURUCZUSUVCEDUTUVGUVHUVCUVFUVGUV
      HUVCUVGJEUBUCZUVHUVCVAUVGJVLGZEVLGZDVLGUVIUVHIUVCLUVJUVGVBSUVKUVGVCSDVDJE
      DVEVFVGVHVIVMVJUVCUVDVKVNUVDUVBLUUIUVDUUHUDKZHGUEKZHGUFKZHGUSZDUVLUVMVOOU
      VNVOOZPZIZUFQULZUEQULUDQULZIUVBDUFUEUDVPUVTUVBUUHUVSUVBUDUEQQUVLQGZUVMQGZ
      IZUVRUVBUFQUWCUVNQGZIZUVQUVBUVOUWEUVBUVQUVPUUSPZAUVAULUWEUWFUVPUUOUUPMUVL
      VQTUVMVQNUVNVQVRZFZBUJZPZAUWGUVAUWEUWGUVAGZUUOQUWGWHZUWEUUOUVLUVMUVNVRZQU
      WGUWEMTNVRZUWMUWGWHZUUOUWMUWGWHUWOUWEMTNUVLUVMUVNVSVTWAUDWBZUEWBZUFWBZWCM
      NWDWEWFZTNWGWIWFZWJSUUOUWNUWMUWGUUOMMTVOOZUIOZMMMVOOZUXAVRZUWNNUXAMUIUXAN
      WKWLWMMRGZUXBUXDPWNMWOWPMMPZUXDUWNPMXAUXFMMUXCTUXANUXFXBUXCTPUXFWQSUXANPU
      XFWKSWRWPWSZWTXCUWAUWBUWDUSUWEUWMQXDUWAUWBUWDXEUVLUVMUVNQUWPUWQUWRXFXGXHQ
      XIGZUUOXIGZIUWKUWLXJUWEUXHUXIXOMNUIXKXLQUUOUWGXIXIXMXNXPUUQUWGPZUWFUWJXJU
      WEUXJUUSUWIUVPUXJUUOUURUWHBUUPUUQUWGXQXRXSUQUWEUWIUWNUWHBUJUVPUWEUUOUWNUW
      HBUUOUWNPUWEUXGSXTUWEMTNUWHBUVLUVMUVNRRRUUPMPUWHMUWGFZUVLUUPMUWGYAMTYFZMN
      YFZUXKUVLPWCUWSMTNUVLUVMUVNVSUWPYBYCYGUUPTPUWHTUWGFZUVMUUPTUWGYAUXLTNYFZU
      XNUVMPWCUWTMTNUVLUVMUVNVTUWQYDYCYGUUPNPUWHNUWGFZUVNUUPNUWGYAUXMUXOUXPUVNP
      UWSUWTMTNUVLUVMUVNWAUWRYEYCYGUWAUWBUWDUVLYHGZUVMYHGZUVNYHGZUSUWAUXQUWBUXR
      UWDUXSUWAUVLUVLYIYJUWBUVMUVMYIYJUWDUVNUVNYIYJYKYLUXETRGZNRGZUSUWEUXEUXTUY
      AWNYMYNYSSUXLUWEWCSUXMUWEUWSSUXOUWEUWTSYOYPYQUVQUUTUWFAUVADUVPUUSYRYTUUAU
      UBUUCUUDUQVMSUUEUUF $.

    $d N o $.
    $( If the (weak) ternary Goldbach conjecture is valid, then every even
       integer greater than 8 is the sum of an odd Goldbach number and 3.
       (Contributed by AV, 24-Jul-2020.) $)
    evengpop3 $p |- ( A. m e. Odd ( 5 < m -> m e. GoldbachOddW )
                      -> ( ( N e. ( ZZ>= ` 9 ) /\ N e. Even )
                           -> E. o e. GoldbachOddW N = ( o + 3 ) ) ) $=
      ( c9 wcel wa c5 clt wbr cgbow codd c3 co caddc wceq a1i syl wb c1 c8 wral
      cuz cfv ceven cv wi cmin wrex 3odd anim1i ancomd emoo breq2 eleq1 imbi12d
      adantl rspcdv cz cle w3a eluz2 5p3e8 8p1e9 9cn ax-1cn 8cn subadd2i eqtr4i
      mpbir zlem1lt biimp3a eqbrtrid 5re 3re 3jca 3ad2ant2 ltaddsub mpbid sylbi
      cr zre adantr simpr oveq1 eqeq2d cc eluzelcn 3cn npcan eqcomd rspcedvd ex
      jca embantd syldc ) CDUBUCEZCUDEZFZGAUEZHIZWSJEZUFZAKUAGCLUGMZHIZXCJEZUFZ
      CBUEZLNMZOZBJUHZWRXBXFAXCKWRWQLKEZFXCKEWRXKWQWPXKWQXKWPUIPUJUKCLULQWSXCOZ
      XBXFRWRXLWTXDXAXEWSXCGHUMWSXCJUNUOUPUQWRXDXEXJWPXDWQWPDUREZCUREZDCUSIZUTZ
      XDDCVAXPGLNMZCHIZXDXPXQDSUGMZCHXQTXSVBXSTOTSNMDOVCDSTVDVEVFVGVIVHXMXNXOXS
      CHIDCVJVKVLXPGVTEZLVTEZCVTEZUTZXRXDRXNXMYCXOXNXTYAYBXTXNVMPYAXNVNPCWAVOVP
      GLCVQQVRVSWBWRXEXJWRXEFZXICXCLNMZOZBXCJWRXEWCXGXCOZXIYFRYDYGXHYECXGXCLNWD
      WEUPYDCWFEZLWFEZFZYFWRYJXEWPYJWQWPYHYIDCWGYIWPWHPWMWBWBYJYECCLWIWJQWKWLWN
      WO $.

    $( If the (strong) ternary Goldbach conjecture is valid, then every even
       integer greater than 10 is the sum of an odd Goldbach number and 3.
       (Contributed by AV, 27-Jul-2020.)  (Proof shortened by AV,
       15-Sep-2021.) $)
    evengpoap3 $p |- ( A. m e. Odd ( 7 < m -> m e. GoldbachOdd )
                      -> ( ( N e. ( ZZ>= ` ; 1 2 ) /\ N e. Even )
                           -> E. o e. GoldbachOdd N = ( o + 3 ) ) ) $=
      ( c1 c2 wcel wa c7 clt wbr cgbo wi codd c3 co caddc wceq a1i cr adantr cv
      cdc cuz cfv ceven wral cmin wrex 3odd anim1i ancomd emoo wb breq2 imbi12d
      syl eleq1 adantl rspcdv cle w3a eluz2 cc0 7p3e10 1nn0 0nn0 2nn 2pos declt
      cz eqbrtri 7re 3re readdcli 2nn0 deccl nn0rei zre ltletr mp3an12i 3adant1
      mpani 3ad2ant2 ltaddsubd mpbid sylbi simpr oveq1 eqeq2d cc eluzelcn jctir
      imp 3cn npcan eqcomd rspcedvd ex embantd syldc ) CDEUBZUCUDFZCUEFZGZHAUAZ
      IJZXEKFZLZAMUFHCNUGOZIJZXIKFZLZCBUAZNPOZQZBKUHZXDXHXLAXIMXDXCNMFZGXIMFXDX
      QXCXBXQXCXQXBUIRUJUKCNULUPXEXIQZXHXLUMXDXRXFXJXGXKXEXIHIUNXEXIKUQUOURUSXD
      XJXKXPXBXJXCXBXAVJFZCVJFZXACUTJZVAZXJXACVBYBHNPOZCIJZXJXTYAYDXSXTYAYDXTYC
      XAIJZYAYDYCDVCUBXAIVDDVCEVEVFVGVHVIVKYCSFXASFXTCSFZYEYAGYDLHNVLVMVNXADEVE
      VOVPVQCVRZYCXACVSVTWBWMWAYBHNCHSFYBVLRNSFYBVMRXTXSYFYAYGWCWDWEWFTXDXKXPXD
      XKGZXOCXINPOZQZBXIKXDXKWGXMXIQZXOYJUMYHYKXNYICXMXINPWHWIURYHCWJFZNWJFZGZY
      JXDYNXKXBYNXCXBYLYMXACWKWNWLTTYNYICCNWOWPUPWQWRWSWT $.

    $d N f g k m o $.
    $( If the (weak) ternary Goldbach conjecture is valid, then every even
       integer greater than 8 is the sum of 4 primes.  (Contributed by AV,
       25-Jul-2020.) $)
    nnsum4primeseven $p |- ( A. m e. Odd ( 5 < m -> m e. GoldbachOddW )
                         -> ( ( N e. ( ZZ>= ` 9 ) /\ N e. Even )
                              -> E. f e. ( Prime ^m ( 1 ... 4 ) )
                                 N = sum_ k e. ( 1 ... 4 ) ( f ` k ) ) ) $=
      ( wbr wcel wi cfv wa c1 c4 cfz co wceq cprime c3 caddc cz a1i adantr codd
      vo vg c5 cv clt cgbow wral cuz ceven csu cmap wrex evengpop3 cmin simplll
      c9 imp c6 6nn nnzi 3z 6p3e9 eqcomi fveq2i eleq2i eluzsub syl3anc ad3antlr
      biimpi 3odd anim1i adantl ancomd emoo syl nnsum4primesodd syl12anc wf cop
      csn cun wn simpr 4z cfzo fzonel fzoval ax-mp w3a 4cn ax-1cn 3pm3.2i 3p1e4
      cc 3cn subadd2 mpbiri oveq2i eqtri mtbir pm3.2i 3prm fsnunf fzval3 cle 1z
      1re 4re 1lt4 ltleii eluz2 mpbir3an fzosplitsn uneq1i 3eqtri sylibr cvv wb
      feq2i prmex ovex elmapg mp1i mpbird fveq1 sumeq2dv eqeq2d wo velsn orbi2i
      elun 3bitri wne cr mtbiri adantld ex eqcomd mpd elfz2 3lt4 ltnle necon2ad
      3re mpbii breq1 eqcoms 3ad2ant3 sylbi fvunsn ffvelcdm ancoms prmz eqeltrd
      zcnd fveq2 cdm eleq2 fsnunfv sylan9eq eqeltrdi jaoi com12 biimtrid fsumm1
      fdm sumeq12dv biimpa oveq1d oveq2d eluzelcn npcand eqtrd 3eqtrrd rspcedvd
      expcom elmapi syl11 rexlimdv rexlimdva2 ) UDCUEZUFEUWBUGFGCUAUHZDUQUIHZFZ
      DUJFZIZDJKLMZBUEZAUEZHZBUKZNZAOUWHULMZUMZUWCUWGIZDUBUEZPQMNZUBUGUMZUWOUWC
      UWGUWSCUBDUNURUWPUWRUWOUBUGUWPUWQUGFZIZUWRIZDPUOMZJPLMZUWIUCUEZHZBUKZNZUC
      OUXDULMZUMZUWOUXBUWCUXCUSUIHFZUXCUAFZUXJUWCUWGUWTUWRUPUWGUXKUWCUWTUWRUWEU
      XKUWFUWEUSRFZPRFZDUSPQMZUIHZFZUXKUXMUWEUSUTVASUXNUWEVBSUWEUXQUWDUXPDUQUXO
      UIUXOUQVCVDVEVFVJPUSDVGVHTVIUXBUWFPUAFZIZUXLUXAUXSUWRUWPUXSUWTUWPUXRUWFUW
      GUXRUWFIUWCUWEUXRUWFUXRUWEVKSVLVMVNTTDPVOVPUWCUXKUXLIUXJUCBCUXCVQURVRUWGU
      XJUWOGZUWCUWTUWRUWEUXTUWFUWEUXHUWOUCUXIUXDOUXEVSZUWEUXHUWOGZUXEUXIFUWEUYA
      UYBUWEUYAIZUXHUWOUYCUXHIZUWMDUWHUWIUXEKPVTWAWBZHZBUKZNZAUYEUWNUYCUYEUWNFZ
      UXHUYCUYIUWHOUYEVSZUYCUXDKWAZWBZOUYEVSZUYJUYCUYAKRFZKUXDFZWCZIZPOFZUYMUWE
      UYAWDUYQUYCUYNUYPWEUYOKJKWFMZFJKWGUXDUYSKUYSUXDUYSJKJUOMZLMZUXDUYNUYSVUAN
      WEJKWHWIUYTPJLKWOFZJWOFZPWOFZWJZUYTPNZVUBVUCVUDWKWLWPWMVUEVUFPJQMKNWNKJPW
      QWRWIZWSWTZVDVFXAZXBSUYRUYCXCSUXDOUXERKPXDVHUWHUYLOUYEUWHJKJQMWFMZUYSUYKW
      BZUYLUYNUWHVUJNWEJKXEWIKJUIHFZVUJVUKNVULJRFZUYNJKXFEXGWEJKXHXIXJXKJKXLXMZ
      JKXNWIUYSUXDUYKVUHXOXPZXTXQOXRFZUWHXRFZIUYIUYJXSUYCVUPVUQYAJKLYBXBOUWHUYE
      XRXRYCYDYETUWJUYENZUWMUYHXSUYDVURUWLUYGDVURUWHUWKUYFBVURUWKUYFNUWIUWHFZUW
      IUWJUYEYFTYGYHVMUYDUYGVUAUYFBUKZKUYEHZQMZUXCVVAQMZDUYCUYGVVBNUXHUYCUYFVVA
      BJKVULUYCVUNSUYCVUSUYFWOFZVUSUWIUXDFZUWIKNZYIZUYCVVDVUSUWIUYLFVVEUWIUYKFZ
      YIVVGUWHUYLUWIVUOVFUWIUXDUYKYLVVHVVFVVEBKYJYKYMVVGUYCVVDVVEUYCVVDGVVFVVEU
      YAVVDUWEVVEUYAVVDVVEUYAIZUYFUXFWOVVIKUWIYNZUYFUXFNZVVEVVJUYAVVEVUMUXNUWIR
      FZWJZJUWIXFEZUWIPXFEZIZIVVJUWIJPUUAVVMVVPVVJVVLVUMVVPVVJGUXNVVLVVOVVJVVNV
      VLVVOKUWIKUWINZVVOWCGVVLVVQVVOKPXFEZPYOFZKYOFZIZVVRWCZVVSVVTUUEXIXBVWAPKU
      FEVWBUUBPKUUCUUFWIVVOVVRXSUWIKUWIKPXFUUGUUHYPSUUDYQUUIURUUJZTUXEKPUWIUUKZ
      VPVVIUXFVVIUXFOFZUXFRFUYAVVEVWEUXDOUWIUXEUULUUMUXFUUNVPUUPUUOYRYQVVFUYCVV
      DVVFUYCIUYFPWOVVFUYCUYFVVAPUWIKUYEUUQZUYAVVAPNZUWEUYAUYNUXNKUXEUURZFZWCZV
      WGUYNUYAWESUXNUYAVBSUYAVWHUXDNZVWJUXDOUXEUVGVWKVWIUYOVUIVWHUXDKUUSYPVPZUX
      ERRKPUUTZVHVMUVAWPUVBYRUVCUVDUVEURVWFUVFTUYDVUTUXCVVAQUYDUXCVUTUYCUXHUXCV
      UTNUYCUXGVUTUXCUYCUXDVUAUXFUYFBUXDVUANUYCPUYTJLUYTPVUGVDWSSUYCVVEIZUYFUXF
      VWNVVJVVKVVEVVJUYCVWCVMVWDVPYSUVHYHUVIYSUVJUYCVVCDNUXHUYCVVCUXCPQMZDUYCVV
      APUXCQUYCUYNUXNVWJVWGUYNUYCWESUXNUYCVBSUYAVWJUWEVWLVMVWMVHUVKUWEVWODNUYAU
      WEDPUQDUVLVUDUWEWPSUVMTUVNTUVOUVPYRUVQUXEOUXDUVRUVSUVTTVIYTUWAYTYR $.

    $( If the (strong) ternary Goldbach conjecture is valid, then every even
       integer greater than 10 is the sum of 4 primes.  (Contributed by AV,
       27-Jul-2020.) $)
    nnsum4primesevenALTV $p |- ( A. m e. Odd ( 7 < m -> m e. GoldbachOdd )
                         -> ( ( N e. ( ZZ>= ` ; 1 2 ) /\ N e. Even )
                              -> E. f e. ( Prime ^m ( 1 ... 4 ) )
                                 N = sum_ k e. ( 1 ... 4 ) ( f ` k ) ) ) $=
      ( wbr wcel c1 cfv wa c4 co wceq cprime c3 caddc c8 cz a1i cle adantr cgbo
      vo vg c7 cv clt wi codd wral cdc cuz ceven cfz csu cmap wrex cmin simplll
      c2 8nn nnzi zaddcld eluzelz w3a eluz2 8p4e12 breq1i 1nn0 2nn declt 8p3e11
      3z 1lt2 3brtr4i 8re 3re readdcld 4re zre ltleletr syl3anc mpani biimtrrid
      cr imp 3adant1 sylbi syl3anbrc eluzsub ad3antlr 3odd anim1i adantl ancomd
      emoo syl nnsum4primesoddALTV syl12anc wf cop csn cun wn simpr cfzo fzonel
      4z fzoval ax-mp cc 4cn ax-1cn 3cn 3p1e4 subadd2 mpbiri mp3an oveq2i eqtri
      eqcomi eleq2i mtbir pm3.2i 3prm fsnunf fzval3 1z 1re 1lt4 ltleii mpbir3an
      fzosplitsn cvv wb eqeq2d wo mtbiri adantld ex eqcomd uneq1i 3eqtri sylibr
      feq2i prmex ovex elmapg mp1i mpbird fveq1 sumeq2sdv elun velsn orbi2i wne
      3bitri elfz2 3lt4 ltnle mpbii eqcoms necon2ad 3ad2ant3 fvunsn ancoms prmz
      breq1 ffvelcdm zcnd eqeltrd fveq2 cdm fdm eleq2 fsnunfv sylan9eq eqeltrdi
      jaoi com12 biimtrid fsumm1 sumeq12dv biimpa oveq1d oveq2d eluzelcn npcand
      eqtrd 3eqtrrd rspcedvd expcom elmapi syl11 rexlimdv evengpoap3 r19.29a
      mpd ) UDCUEZUFEUWRUAFUGCUHUIZDGUSUJZUKHFZDULFZIZDGJUMKZBUEZAUEZHZBUNZLZAM
      UXDUOKZUPZUWSUXCIZDUBUEZNOKLZUXKUBUAUXLUXMUAFZIZUXNIZDNUQKZGNUMKZUXEUCUEZ
      HZBUNZLZUCMUXSUOKZUPZUXKUXQUWSUXRPUKHFZUXRUHFZUYEUWSUXCUXOUXNURUXCUYFUWSU
      XOUXNUXAUYFUXBUXAPQFZNQFZDPNOKZUKHFZUYFUYHUXAPUTVARZUYIUXAVLRZUXAUYJQFDQF
      ZUYJDSEZUYKUXAPNUYLUYMVBUWTDVCUXAUWTQFZUYNUWTDSEZVDUYOUWTDVEUYNUYQUYOUYPU
      YNUYQUYOUYQPJOKZDSEZUYNUYOUYRUWTDSVFVGUYNUYJUYRUFEZUYSUYOGGUJUWTUYJUYRUFG
      GUSVHVHVIVMVJVKVFVNUYNUYJWDFUYRWDFDWDFUYTUYSIUYOUGUYNPNPWDFUYNVORZNWDFZUY
      NVPRVQUYNPJVUAJWDFZUYNVRRVQDVSUYJUYRDVTWAWBWCWEWFWGUYJDVEWHNPDWIWATWJUXQU
      XBNUHFZIZUYGUXPVUEUXNUXLVUEUXOUXLVUDUXBUXCVUDUXBIUWSUXAVUDUXBVUDUXAWKRWLW
      MWNTTDNWOWPUWSUYFUYGIUYEUCBCUXRWQWEWRUXCUYEUXKUGZUWSUXOUXNUXAVUFUXBUXAUYC
      UXKUCUYDUXSMUXTWSZUXAUYCUXKUGZUXTUYDFUXAVUGVUHUXAVUGIZUYCUXKVUIUYCIZUXIDU
      XDUXEUXTJNWTXAXBZHZBUNZLZAVUKUXJVUIVUKUXJFZUYCVUIVUOUXDMVUKWSZVUIUXSJXAZX
      BZMVUKWSZVUPVUIVUGJQFZJUXSFZXCZIZNMFZVUSUXAVUGXDVVCVUIVUTVVBXGVVAJGJXEKZF
      GJXFUXSVVEJVVEUXSVVEGJGUQKZUMKZUXSVUTVVEVVGLXGGJXHXIVVFNGUMJXJFZGXJFZNXJF
      ZVVFNLZXKXLXMVVHVVIVVJVDVVKNGOKJLXNJGNXOXPXQZXRXSZXTYAYBZYCRVVDVUIYDRUXSM
      UXTQJNYEWAUXDVURMVUKUXDGJGOKXEKZVVEVUQXBZVURVUTUXDVVOLXGGJYFXIJGUKHFZVVOV
      VPLVVQGQFZVUTGJSEYGXGGJYHVRYIYJGJVEYKZGJYLXIVVEUXSVUQVVMUUAUUBZUUDUUCMYMF
      ZUXDYMFZIVUOVUPYNVUIVWAVWBUUEGJUMUUFYCMUXDVUKYMYMUUGUUHUUITUXFVUKLZUXIVUN
      YNVUJVWCUXHVUMDVWCUXDUXGVULBUXEUXFVUKUUJUUKYOWMVUJVUMVVGVULBUNZJVUKHZOKZU
      XRVWEOKZDVUIVUMVWFLUYCVUIVULVWEBGJVVQVUIVVSRVUIUXEUXDFZVULXJFZVWHUXEUXSFZ
      UXEJLZYPZVUIVWIVWHUXEVURFVWJUXEVUQFZYPVWLUXDVURUXEVVTYAUXEUXSVUQUULVWMVWK
      VWJBJUUMUUNUUPVWLVUIVWIVWJVUIVWIUGVWKVWJVUGVWIUXAVWJVUGVWIVWJVUGIZVULUYAX
      JVWNJUXEUUOZVULUYALZVWJVWOVUGVWJVVRUYIUXEQFZVDZGUXESEZUXENSEZIZIVWOUXEGNU
      UQVWRVXAVWOVWQVVRVXAVWOUGUYIVWQVWTVWOVWSVWQVWTJUXEJUXELZVWTXCUGVWQVXBVWTJ
      NSEZVUBVUCIZVXCXCZVUBVUCVPVRYCVXDNJUFEVXEUURNJUUSUUTXIVWTVXCYNUXEJUXEJNSU
      VGUVAYQRUVBYRUVCWEWGZTUXTJNUXEUVDZWPVWNUYAVWNUYAMFZUYAQFVUGVWJVXHUXSMUXEU
      XTUVHUVEUYAUVFWPUVIUVJYSYRVWKVUIVWIVWKVUIIVULNXJVWKVUIVULVWENUXEJVUKUVKZV
      UGVWENLZUXAVUGVUTUYIJUXTUVLZFZXCZVXJVUTVUGXGRUYIVUGVLRVUGVXKUXSLZVXMUXSMU
      XTUVMVXNVXLVVAVVNVXKUXSJUVNYQWPZUXTQQJNUVOZWAWMUVPXMUVQYSUVRUVSUVTWEVXIUW
      ATVUJVWDUXRVWEOVUJUXRVWDVUIUYCUXRVWDLVUIUYBVWDUXRVUIUXSVVGUYAVULBUXSVVGLV
      UINVVFGUMVVFNVVLXTXRRVUIVWJIZVULUYAVXQVWOVWPVWJVWOVUIVXFWMVXGWPYTUWBYOUWC
      YTUWDVUIVWGDLUYCVUIVWGUXRNOKZDVUIVWENUXROVUIVUTUYIVXMVXJVUTVUIXGRUYIVUIVL
      RVUGVXMUXAVXOWMVXPWAUWEUXAVXRDLVUGUXADNUWTDUWFVVJUXAXMRUWGTUWHTUWIUWJYSUW
      KUXTMUXSUWLUWMUWNTWJUWQUWSUXCUXNUBUAUPCUBDUWOWEUWPYS $.

    $d d f k m n $.
    $( If the (weak) ternary Goldbach conjecture is valid, then every integer
       greater than 1 is the sum of at most 4 primes, showing that
       Schnirelmann's constant would be less than or equal to 4.  See corollary
       1.1 in [Helfgott] p. 4.  (Contributed by AV, 25-Jul-2020.) $)
    wtgoldbnnsum4prm $p |- ( A. m e. Odd ( 5 < m -> m e. GoldbachOddW )
            -> A. n e. ( ZZ>= ` 2 ) E. d e. NN E. f e. ( Prime ^m ( 1 ... d ) )
                         ( d <_ 4 /\ n = sum_ k e. ( 1 ... d ) ( f ` k ) ) ) $=
      ( cv wbr wcel c4 cle c1 cfz co wa wrex cn c2 c9 c3 c6 clt cgbow codd wral
      c5 wi cfv csu wceq cprime cmap cuz cfzo wo cun wb cz 2z 9nn nnzi 2re 2lt9
      9re ltleii eluz2 mpbir3an fzouzsplit eleq2d ax-mp elun bitri c8 w3a simp1
      elfzo2 caddc df-9 breq2i eluz2nn 8nn adantr nnleltp1 syl biimprd biimtrid
      jctir 3impia jca sylbi nnsum4primesle9 a1d ceven 4nn oveq2 oveq2d sumeq1d
      a1i breq1 eqeq2d anbi12d rexeqbidv adantl nnsum4primeseven impcom r19.42v
      4re leidi sylanbrc rspcedvd ex 3nn 3re 3lt4 6nn 6re eluzuzle mp2an anim1i
      6lt9 nnsum4primesodd mpan9 eluzelz zeoALTV mpjaodan jaoi ralrimiva ) UECF
      ZUAGYGUBHUFCUCUDZEFZIJGZDFZKYILMZBFAFUGZBUHZUIZNZAUJYLUKMZOZEPOZDQULUGZYK
      YTHZYHYSUUAYKQRUMMZHZYKRULUGZHZUNZYHYSUFZUUAYKUUBUUDUOZHZUUFRYTHZUUAUUIUP
      UUJQUQHRUQHZQRJGURRUSUTQRVAVCVBVDQRVEVFUUJYTUUHYKQRVGVHVIYKUUBUUDVJVKUUCU
      UGUUEUUCYSYHUUCUUAYKVLJGZNZYSUUCUUAUUKYKRUAGZVMZUUMYKQRVOUUOUUAUULUUAUUKU
      UNVNUUAUUKUUNUULUUNYKVLKVPMZUAGZUUAUUKNZUULRUUPYKUAVQVRUURUULUUQUURYKPHZV
      LPHZNZUULUUQUPUUAUVAUUKUUAUUSUUTYKVSVTWFWAYKVLWBWCWDWEWGWHWIABYKEWJWCWKUU
      EYKWLHZUUGYKUCHZUUEUVBNZYHYSUVDYHNZYRIIJGZYKKILMZYMBUHZUIZNZAUJUVGUKMZOZE
      IPIPHUVEWMWQYIIUIZYRUVLUPUVEUVMYPUVJAYQUVKUVMYLUVGUJUKYIIKLWNZWOUVMYJUVFY
      OUVIYIIIJWRUVMYNUVHYKUVMYLUVGYMBUVNWPWSWTXAXBUVEUVFUVIAUVKOZUVLUVFUVEIXFX
      GWQYHUVDUVOABCYKXCXDUVFUVIAUVKXEXHXIXJUUEUVCNZYHYSUVPYHNZYRSIJGZYKKSLMZYM
      BUHZUIZNZAUJUVSUKMZOZESPSPHUVQXKWQYISUIZYRUWDUPUVQUWEYPUWBAYQUWCUWEYLUVSU
      JUKYISKLWNZWOUWEYJUVRYOUWAYISIJWRUWEYNUVTYKUWEYLUVSYMBUWFWPWSWTXAXBUVQUVR
      UWAAUWCOZUWDUVRUVQSIXLXFXMVDWQUVPYKTULUGHZUVCNYHUWGUUEUWHUVCTUQHTRJGUUEUW
      HUFTXNUTTRXOVCXSVDRTYKXPXQXRABCYKXTYAUVRUWAAUWCXEXHXIXJUUEYKUQHUVBUVCUNRY
      KYBYKYCWCYDYEWIXDYF $.

    $( If the (strong) ternary Goldbach conjecture is valid, then every integer
       greater than 1 is the sum of at most 4 primes.  (Contributed by AV,
       27-Jul-2020.) $)
    stgoldbnnsum4prm $p |- ( A. m e. Odd ( 7 < m -> m e. GoldbachOdd )
            -> A. n e. ( ZZ>= ` 2 ) E. d e. NN E. f e. ( Prime ^m ( 1 ... d ) )
                         ( d <_ 4 /\ n = sum_ k e. ( 1 ... d ) ( f ` k ) ) ) $=
      ( c7 cv clt wbr cgbo wcel wi codd wral c5 cgbow c4 co cfv wrex cle c1 cfz
      csu wceq wa cprime cmap cn c2 cuz stgoldbwt wtgoldbnnsum4prm syl ) FCGZHI
      UOJKLCMNOUOHIUOPKLCMNEGZQUAIDGUBUPUCRZBGAGSBUDUEUFAUGUQUHRTEUITDUJUKSNCUL
      ABCDEUMUN $.

    $d d n o $.
    $( If the binary Goldbach conjecture is valid, then every integer greater
       than 1 is the sum of at most 3 primes, showing that Schnirelmann's
       constant would be equal to 3.  (Contributed by AV, 2-Aug-2020.) $)
    bgoldbnnsum3prm $p |- ( A. m e. Even ( 4 < m -> m e. GoldbachEven )
            -> A. n e. ( ZZ>= ` 2 ) E. d e. NN E. f e. ( Prime ^m ( 1 ... d ) )
                         ( d <_ 3 /\ n = sum_ k e. ( 1 ... d ) ( f ` k ) ) ) $=
      ( vo c4 cv clt wbr wcel wi c3 cle co wa cn c2 c9 c6 cgbe ceven c1 cfz cfv
      wral csu wceq cprime cmap wrex cuz cfzo wo cun wb cz 2z 9nn nnzi 2re 2lt9
      9re ltleii eluz2 mpbir3an fzouzsplit eleq2d ax-mp elun bitri c8 w3a simp1
      elfzo2 caddc df-9 breq2i eluz2nn 8nn adantr nnleltp1 syl biimprd biimtrid
      jctir 3impia jca sylbi nnsum3primesle9 a1d weq breq2 eleq1w imbi12d rspcv
      codd cr 4re a1i eluzelre 3jca adantl eluzle 4lt9 jctil ltletr sylc pm2.27
      ex syl5d impcom nnsum3primesgbe syl6 cgbow 3nn oveq2 oveq2d breq1 sumeq1d
      eqeq2d anbi12d rexeqbidv 3re leidi 6nn 6re eluzuzle mp2an nnsum4primesodd
      c5 6lt9 anim1i mpan9 r19.42v sylanbrc rspcedvd expcom sbgoldbwt syl11
      eluzelz zeoALTV mpjaodan jaoi ralrimiva ) GCHZIJZUUFUAKZLZCUBUFZEHZMNJZDH
      ZUCUUKUDOZBHAHUEZBUGZUHZPZAUIUUNUJOZUKZEQUKZDRULUEZUUMUVBKZUUJUVAUVCUUMRS
      UMOZKZUUMSULUEZKZUNZUUJUVALZUVCUUMUVDUVFUOZKZUVHSUVBKZUVCUVKUPUVLRUQKSUQK
      ZRSNJURSUSUTRSVAVCVBVDRSVEVFUVLUVBUVJUUMRSVGVHVIUUMUVDUVFVJVKUVEUVIUVGUVE
      UVAUUJUVEUVCUUMVLNJZPZUVAUVEUVCUVMUUMSIJZVMZUVOUUMRSVOUVQUVCUVNUVCUVMUVPV
      NUVCUVMUVPUVNUVPUUMVLUCVPOZIJZUVCUVMPZUVNSUVRUUMIVQVRUVTUVNUVSUVTUUMQKZVL
      QKZPZUVNUVSUPUVCUWCUVMUVCUWAUWBUUMVSVTWFWAUUMVLWBWCWDWEWGWHWIABUUMEWJWCWK
      UVGUUMUBKZUVIUUMWQKZUVGUWDPUUJUUMUAKZUVAUWDUVGUUJUWFLUWDUUJGUUMIJZUWFLZUV
      GUWFUUIUWHCUUMUBCDWLUUGUWGUUHUWFUUFUUMGIWMCDUAWNWOWPUWDUVGUWHUWFLZUWDUVGP
      ZUWGUWIUWJGWRKZSWRKZUUMWRKZVMZGSIJZSUUMNJZPUWGUVGUWNUWDUVGUWKUWLUWMUWKUVG
      WSWTUWLUVGVCWTSUUMXAXBXCUWJUWPUWOUVGUWPUWDSUUMXDXCXEXFGSUUMXGXHUWGUWFXIWC
      XJXKXLABUUMEXMXNYKFHZIJUWQXOKLFWQUFZUVGUWEPZUVAUUJUWSUWRUVAUWSUWRPZUUTMMN
      JZUUMUCMUDOZUUOBUGZUHZPZAUIUXBUJOZUKZEMQMQKUWTXPWTUUKMUHZUUTUXGUPUWTUXHUU
      RUXEAUUSUXFUXHUUNUXBUIUJUUKMUCUDXQZXRUXHUULUXAUUQUXDUUKMMNXSUXHUUPUXCUUMU
      XHUUNUXBUUOBUXIXTYAYBYCXCUWTUXAUXDAUXFUKZUXGUXAUWTMYDYEWTUWSUUMTULUEKZUWE
      PUWRUXJUVGUXKUWETUQKTSNJUVGUXKLTYFUTTSYGVCYLVDSTUUMYHYIYMABFUUMYJYNUXAUXD
      AUXFYOYPYQYRFCYSYTUVGUUMUQKUWDUWEUNSUUMUUAUUMUUBWCUUCUUDWIXLUUE $.
  $}

  $( Lemma 1 for ~ bgoldbtbnd : the odd numbers between 7 and 13 (exclusive)
     are odd Goldbach numbers.  (Contributed by AV, 29-Jul-2020.) $)
  bgoldbtbndlem1 $p |- ( ( N e. Odd /\ 7 < N /\ N e. ( 7 [,) ; 1 3 ) )
                         -> N e. GoldbachOdd ) $=
    ( codd wcel c7 clt wbr c1 co cle wb c8 cz nnzi caddc a1i cr c9 com12 ceven
    c2 c3 cdc cico cgbo cxr w3a wa 7re rexri 1nn0 decnncl nnrei elico1 mp2an wi
    3nn wceq wo 7nn oddz zltp1le 7p1e8 breq1i 8re zre syl2an 3bitrd sylancr 8nn
    leloe 8p1e9 9re zred leloed cc0 9p1e10 10re 10nn dec10p eqcomi oveq1i nncni
    9nn 1nn ax-1cn addassi 1p1e2 oveq2i eqtri 3eqtri 2nn wn 2p1e3 lenltd pm2.21
    2cn biimtrdi eleq1 c6 6p6e12 6even epee eqeltrri evennodd pm2.21i biimtrrdi
    ax-mp jaoi sylbid 11gbo mpbii 2a1d 5p5e10 5odd opoeALTV 9gbo 8even 3ad2ant3
    c5 imp biimtrid 3impia ) ABCZDAEFZADGUAUBZUCHCZAUDCZYFAUECZDAIFZAYEEFZUFZYC
    YDUGZYGDUECYEUECYFYKJDUHUIYEYEGUAUJUPUKULZUIDYEAUMUNYKYLYGYJYHYLYGUOYIYLYJY
    GYCYDYJYGUOZYCYDKAEFZKAUQZURZYNYCDLCZALCZYDYQJDUSMAUTZYRYSUGZYDDGNHZAIFZKAI
    FZYQDAVAUUCUUDJUUAUUBKAIVBVCOYRKPCZAPCUUDYQJYSUUEYRVDOAVEKAVJVFVGVHYQYCYNYO
    YCYNUOZYPYCYOYNYCYOQAEFZQAUQZURZYNYCYOKGNHZAIFZQAIFZUUIYCKLCYSYOUUKJKVIMYTK
    AVAVHUUKUULJYCUUJQAIVKVCOYCQAQPCYCVLOYCAYTVMZVNVGUUIYCYNUUGUUFUUHYCUUGYNYCU
    UGGVOUBZAEFZUUNAUQZURZYNYCUUGQGNHZAIFZUUNAIFZUUQYCQLCYSUUGUUSJQWCMYTQAVAVHU
    USUUTJYCUURUUNAIVPVCOYCUUNAUUNPCYCVQOUUMVNVGUUQYCYNUUOUUFUUPYCUUOYNYCUUOGGU
    BZAEFZUVAAUQZURZYNYCUUOUUNGNHZAIFZUVAAIFZUVDYCUUNLCYSUUOUVFJUUNVRMYTUUNAVAV
    HUVFUVGJYCUVEUVAAIGVSZVCOYCUVAAUVAPCYCUVAGGUJWDUKZULOUUMVNVGUVDYCYNUVBUUFUV
    CYCUVBYNYCUVBGTUBZAEFZUVJAUQZURZYNYCUVBUVAGNHZAIFZUVJAIFZUVMYCUVALCYSUVBUVO
    JUVAUVIMYTUVAAVAVHUVOUVPJYCUVNUVJAIUVNUVEGNHUUNGGNHZNHZUVJUVAUVEGNUVEUVAUVH
    VTWAUUNGGUUNVRWBZWEWEWFUVRUUNTNHZUVJUVQTUUNNWGWHTVSZWIWJVCOYCUVJAUVJPCYCUVJ
    GTUJWKUKZULOUUMVNVGUVMYCYNUVKUUFUVLYCUVKYNYCUVKYJWLZYNYCUVKUVJGNHZAIFZYEAIF
    ZUWCYCUVJLCYSUVKUWEJUVJUWBMYTUVJAVAVHUWEUWFJYCUWDYEAIUWDUVTGNHUUNTGNHZNHZYE
    UVJUVTGNUVTUVJUWAVTWAUUNTGUVSWPWEWFUWHUUNUANHYEUWGUAUUNNWMWHUAVSWIWJVCOYCYE
    AYEPCYCYMOUUMWNVGYJYGWOWQRUVLYCUVJBCZYNUVJABWRUWIYNUVJSCUWIWLWSWSNHZUVJSWTW
    SSCZUWKUWJSCXAXAWSWSXBUNXCUVJXDXGXEXFXHRXIRUVCYGYCYJUVCUVAUDCYGXJUVAAUDWRXK
    XLXHRXIRUUPYCUUNBCZYNUUNABWRUWLYNUUNSCUWLWLXSXSNHZUUNSXMXSBCZUWNUWMSCXNXNXS
    XSXOUNXCUUNXDXGXEXFXHRXIRUUHYGYCYJUUHQUDCYGXPQAUDWRXKXLXHRXIRYPYCKBCZYNKABW
    RUWOYNKSCUWOWLXQKXDXGXEXFXHRXIXTRXRRYAYB $.

  ${
    $d D i $.  $d F i $.  $d I i $.  $d N i $.
    bgoldbtbnd.m $e |- ( ph -> M e. ( ZZ>= ` ; 1 1 ) ) $.
    bgoldbtbnd.n $e |- ( ph -> N e. ( ZZ>= ` ; 1 1 ) ) $.
    bgoldbtbnd.b $e |- ( ph -> A. n e. Even ( ( 4 < n /\ n < N )
                                              -> n e. GoldbachEven ) ) $.
    bgoldbtbnd.d $e |- ( ph -> D e. ( ZZ>= ` 3 ) ) $.
    bgoldbtbnd.f $e |- ( ph -> F e. ( RePart ` D ) ) $.
    bgoldbtbnd.i $e |- ( ph -> A. i e. ( 0 ..^ D )
                            ( ( F ` i ) e. ( Prime \ { 2 } )
                              /\ ( ( F ` ( i + 1 ) ) - ( F ` i ) ) < ( N - 4 )
                              /\ 4 < ( ( F ` ( i + 1 ) ) - ( F ` i ) ) ) ) $.
    bgoldbtbnd.0 $e |- ( ph -> ( F ` 0 ) = 7 ) $.
    bgoldbtbnd.1 $e |- ( ph -> ( F ` 1 ) = ; 1 3 ) $.
    bgoldbtbnd.l $e |- ( ph -> M < ( F ` D ) ) $.
    ${
      bgoldbtbndlem2.s $e |- S = ( X - ( F ` ( I - 1 ) ) ) $.
      $( Lemma 2 for ~ bgoldbtbnd .  (Contributed by AV, 1-Aug-2020.) $)
      bgoldbtbndlem2 $p |- ( ( ph /\ X e. Odd /\ I e. ( 1 ..^ D ) )
                             -> ( ( X e. ( ( F ` I ) [,) ( F ` ( I + 1 ) ) )
                                    /\ ( X - ( F ` I ) ) <_ 4 )
                                  -> ( S e. Even /\ S < N /\ 4 < S ) ) ) $=
        ( codd wcel c1 cfzo co w3a cmin cfv cprime c2 csn cdif caddc c4 clt wbr
        cico cle wa ceven wi cv cc0 cz elfzoelz elfzoel2 elfzom1b wss fzossrbm1
        wral adantl sseld sylbid com12 mp2and wceq fveq2 eleq1d fvoveq1 oveq12d
        breq1d breq2d 3anbi123d rspcv syl syl5com a1d simp2 oddprmALTV 3ad2ant1
        3imp anim12i adantr omoeALTV eqeltrid wb cc zcnd 3ad2ant3 npcan1 fveq2d
        oveq1d eldifi prmz cr zre simp1 ralimi fzo0ss1 sseli ex com23 a1i com13
        mpcom cdc cuz eluzelz oddz simplr simprl 4re lesubaddd simpllr resubcld
        zred readdcld resubcl exp32 3adant3 3syl impcom 1eluzge0 sselda 3adant2
        imp mp1i ad2antrr cxr iccpartxr simplrr simplrl simplll lesub1d adantrr
        simprr biimpa simpll ltaddsub2 bicomd syl3anc biimpd adantld recnd recn
        4cn addsubassd mpbird lelttrd sylan2 4syl expcom eqbrtrid syl6 ad2antlr
        fzoss1 mpid 3ad2ant2 syl2an biimpcd cn eluz3nn ciccp cfz fzossfz sstrdi
        c3 fzofzp1 jca elico1 biimtrdi adantrd lesub1dd ltletrd breqtrrdi mpdan
        3jca ) AJUAUBZGUCBUDUEZUBZUFZGUCUGUEZFUHZUIUJUKZULZUBZUWLUCUMUEZFUHZUWM
        UGUEZIUNUGUEZUOUPZUNUWSUOUPZUFZJGFUHZGUCUMUEZFUHZUQUEUBZJUXDUGUEUNURUPZ
        USZCUTUBZCIUOUPZUNCUOUPZUFZVAAUWHUWJUXCAUWJUXCVAUWHADVBZFUHZUWOUBZUXNUC
        UMUEFUHZUXOUGUEZUWTUOUPZUNUXRUOUPZUFZDVCBUDUEZVJZUWJUXCPUWJUWLUYBUBZUYC
        UXCVAUWJGVDUBZBVDUBZUYDGUCBVEZGUCBVFUYEUYFUSZUWJUYDUYHUWJUWLVCBUCUGUEUD
        UEZUBUYDGBVGUYHUYIUYBUWLUYFUYIUYBVHUYEBVIVKVLVMVNVOUYAUXCDUWLUYBUXNUWLV
        PZUXPUWPUXSUXAUXTUXBUYJUXOUWMUWOUXNUWLFVQZVRUYJUXRUWSUWTUOUYJUXQUWRUXOU
        WMUGUXNUWLUCFUMVSUYKVTZWAUYJUXRUWSUNUOUYLWBWCWDWEWFWGWKUWKUXCUSZUXIUXMU
        YMUXIUSZUXJUXKUXLUYNCJUWMUGUEZUTTUYNUWHUWMUAUBZUSZUYOUTUBUYMUYQUXIUWKUW
        HUXCUYPAUWHUWJWHUWPUXAUYPUXBUWMWIWJWLWMJUWMWNWEWOUYNCUYOIUOTUXIUYMUYOIU
        OUPZUXHUYMUYRVAUXGUYMUXHUYRUXCUWKUXHUYRVAZUWPUXAUWKUYSVAZUXBUWPUXAUYTUW
        PUWKUXAUYSUWKUWPUXAUYSVAUWKUWPUSUXAUXDUWMUGUEZUWTUOUPZUYSUWKUXAVUBWPUWP
        UWKUWSVUAUWTUOUWKUWRUXDUWMUGUWKUWQGFUWKGWQUBZUWQGVPZUWJAVUCUWHUWJGUYGWR
        ZWSGWTZWEXAXBWAWMUWPUWKVUBUYSVAZUWPUWMUIUBZUWMVDUBZUWKVUGVAUWMUIUWNXCZU
        WMXDZVUIUWMXEUBZUWKVUGUWMXFUXDUWOUBZUWKVULVUGVAZAUWHUWJVUMUYCAUWHUWJVUM
        VAZVAZPUYCUXPDUYBVJZAVUPVAUYAUXPDUYBUXPUXSUXTXGXHUWHAVUQVUOAVUQVUOVAVAU
        WHAUWJVUQVUMAUWJVUQVUMVAZAUWJUSZGUYBUBZVURUWJVUTAUWIUYBGBXIXJVKUXPVUMDG
        UYBUXNGVPZUXOUXDUWOUXNGFVQZVRZWDWEXKXLXMXNWEXOWKVUMUXDUIUBZUXDVDUBZUWKV
        UNVAUXDUIUWNXCZUXDXDZVVEUXDXEUBZUWKVUNUXDXFAUWHVVHVUNVAZUWJAUWHVVIAIUCU
        CXPZXQUHUBIVDUBIXEUBZUWHVVIVALVVJIXRIXFVVKUWHVVIUWHVVKJXEUBZVVIUWHJJXSY
        FZVVKVVLUSZVVHVULVUGVVNVVHVULUSZUSZUXHVUBUYRVVPUXHJUNUXDUMUEZURUPZVUBUY
        RVAVVPJUXDUNVVKVVLVVOXTZVVNVVHVULYAZUNXEUBZVVPYBXMZYCVVPVVRVUBUYRVVPVVR
        VUBUSZUSZUYOVVQUWMUGUEZIVWDJUWMVVKVVLVVOVWCYDVVNVVHVULVWCUUAZYEVWDVVQUW
        MVWDUNUXDVWAVWDYBXMVVNVVHVULVWCUUBYGVWFYEVVKVVLVVOVWCUUCVVPVVRUYOVWEURU
        PZVUBVVPVVRVWGVVPJVVQUWMVVSVVPUNUXDVWBVVTYGVVNVVHVULUUFUUDUUGUUEVWDVWEI
        UOUPZUNVUAUMUEZIUOUPZVVPVWCVWJVVPVUBVWJVVRVVPVUBVWJVVPVWAVUAXEUBZVVKVUB
        VWJWPVWBVVOVWKVVNUXDUWMYHVKVVKVVLVVOUUHVWAVWKVVKUFVWJVUBUNVUAIUUIUUJUUK
        UULUUMYPVVPVWHVWJWPVWCVVPVWEVWIIUOVVPUNUXDUWMUNWQUBVVPUUPXMVVPUXDVVTUUN
        VVOUWMWQUBZVVNVULVWLVVHUWMUUOVKVKUUQWAWMUURUUSYIVMXLYIUUTXKUVAYPYJWFYKX
        OWFYKYLVMUVBXLYPYJYLVNVKYLUVCUYNUNUYOCUOUYNUNVUAUYOVWAUYNYBXMUYNUXDUWMU
        WKVVHUXCUXIAUWJVVHUWHAUWJVVHAUWJUYCVVHPAUWJUYCVVHVAVUSUYCVUMUXFUXDUGUEZ
        UWTUOUPZUNVWMUOUPZUFZVVHVUSVUTUYCVWPVAAUWIUYBGUCVCXQUHUBZUWIUYBVHZAYMUC
        VCBUVFZYQYNZUYAVWPDGUYBVVAUXPVUMUXSVWNUXTVWOVVCVVAUXRVWMUWTUOVVAUXQUXFU
        XOUXDUGUXNGUCFUMVSVVBVTZWAVVAUXRVWMUNUOVXAWBWCWDWEVUMVWNVVHVWOVUMVVDVVH
        VVFVVDUXDVVGYFWEWJUVDXKUVGYPYOYRZUXCVULUWKUXIUWPUXAVULUXBUWPVUHVULVUJVU
        HUWMVUKYFWEWJZUVEZYEUYMUYOXEUBZUXIUWKVVLVULVXEUXCUWHAVVLUWJVVMUVHZVXCJU
        WMYHUVIWMUYMUNVUAUOUPZUXIUXCUWKVXGUXBUWPUWKVXGVAUXAUWKUXBVXGUWKUWSVUAUN
        UOUWKUWRUXDUWMUGUWKUWQGFUWJAVUDUWHUWJVUCVUDVUEVUFWEWSXAXBWBUVJWSYLWMUYN
        UXDJUWMVXBUWKVVLUXCUXIVXFYRVXDUYMUXIUXDJURUPZUWKUXIVXHVAUXCUWKUXGVXHUXH
        UWKUXGJYSUBZVXHJUXFUOUPZUFZVXHUWKUXDYSUBZUXFYSUBZUSZUXGVXKWPAUWJVXNUWHV
        USVXLVXMVUSFGBABUVKUBZUWJABUVQXQUHUBZVXONBUVLWEWMZAFBUVMUHUBUWJOWMZAUWI
        VCBUVNUEZGAVXPUWIVXSVHNVXPUWIUYBVXSVWQVWRVXPYMVWSYQVCBUVOUVPWEYNYTVUSFU
        XEBVXQVXRVUSVUTUXEVXSUBVWTVCBGUVRWEYTUVSYOUXDUXFJUVTWEVXIVXHVXJWHUWAUWB
        WMYPUWCUWDTUWEUWGXKUWF $.
    $}

    bgoldbtbnd.r $e |- ( ph -> ( F ` D ) e. RR ) $.
    ${
      bgoldbtbndlem3.s $e |- S = ( X - ( F ` I ) ) $.
      $( Lemma 3 for ~ bgoldbtbnd .  (Contributed by AV, 1-Aug-2020.) $)
      bgoldbtbndlem3 $p |- ( ( ph /\ X e. Odd /\ I e. ( 1 ..^ D ) )
                             -> ( ( X e. ( ( F ` I ) [,) ( F ` ( I + 1 ) ) )
                                    /\ 4 < S )
                             -> ( S e. Even /\ S < N /\ 4 < S ) ) ) $=
        ( codd wcel c1 cfzo co w3a cfv cprime c2 csn cdif caddc cmin c4 clt wbr
        cico wa ceven wi cc0 cv wral fzo0ss1 sseli fveq2 eleq1d fvoveq1 oveq12d
        wceq breq1d breq2d 3anbi123d rspcv syl2imc a1d 3imp oddprmALTV 3ad2ant1
        simp2 anim12i adantr omoeALTV syl eqeltrid eldifi prmz zred cfz fzofzp1
        cr wo cun cuz cz elfzo2 cle eluz2 zre leltletr syl3an exp5o com34 sylbi
        1zzd syl3anbrc fzisfzounsn eleq2d elun bitrdi cn eluz3nn ad2antrl ciccp
        c3 simplr iccpartipre exp31 elsni wb mpbird ex jaod sylbid com12 3impia
        a1i mpd cdc cxr rexr simprr resubcld 4re lttr syl3anc exp32 3adant3 imp
        eluzelre anim12ci adantl simpllr simplrl simplrr simpr ltsub1dd simplll
        oddz elico1 mpand impr 4pos simpl ltsubposd mpbii simpll 3ad2ant3 com23
        mp2and syl2an com13 3syl impcom adantrr eqbrtrid 3jca mpdan ) AJUBUCZGU
        DBUEUFZUCZUGZGFUHZUIUJUKZULZUCZGUDUMUFZFUHZUVNUNUFZIUOUNUFZUPUQZUOUVTUP
        UQZUGZJUVNUVSURUFUCZUOCUPUQZUSZCUTUCZCIUPUQZUWFUGZVAAUVJUVLUWDAUVLUWDVA
        UVJUVLGVBBUEUFZUCADVCZFUHZUVPUCZUWLUDUMUFFUHZUWMUNUFZUWAUPUQZUOUWPUPUQZ
        UGZDUWKVDUWDUVKUWKGBVEVFPUWSUWDDGUWKUWLGVKZUWNUVQUWQUWBUWRUWCUWTUWMUVNU
        VPUWLGFVGZVHUWTUWPUVTUWAUPUWTUWOUVSUWMUVNUNUWLGUDFUMVIUXAVJZVLUWTUWPUVT
        UOUPUXBVMVNVOVPVQVRUVMUWDUSZUWGUWJUXCUWGUSZUWHUWIUWFUXDCJUVNUNUFZUTUAUX
        DUVJUVNUBUCZUSZUXEUTUCUXCUXGUWGUVMUVJUWDUXFAUVJUVLWAUVQUWBUXFUWCUVNVSVT
        WBWCJUVNWDWEWFUXDCUXEIUPUAUXCUWEUXEIUPUQZUWFUXCUWEUXHUWDUVMUWEUXHVAZUVQ
        UWBUVMUXIVAZUWCUVQUWBUXJUVQUVNUIUCZUVNWLUCZUWBUXJVAUVNUIUVOWGUXKUVNUVNW
        HWIUVMUWBUXLUXIUVMUVSWLUCZUWBUXLUXIVAVAZAUVJUVLUXMUVLAUVJUSZUXMUVLUVRUD
        BWJUFZUCZUXOUXMVAZUDBGWKUVLUXQUVRUVKUCZUVRBUKZUCZWMZUXRUVLUXQUVRUVKUXTW
        NZUCUYBUVLUXPUYCUVRUVLBUDWOUHZUCZUXPUYCVKUVLGUYDUCZBWPUCZGBUPUQZUGZUYEG
        UDBWQUYIUDWPUCZUYGUDBWRUQZUYEUYIXFUYFUYGUYHWAUYFUYGUYHUYKUYFUYJGWPUCZUD
        GWRUQZUGUYGUYHUYKVAZVAZUDGWSUYJUYLUYMUYOUYJUYLUYGUYMUYNUYJUYLUYGUYMUYHU
        YKUYJUDWLUCUYLGWLUCUYGBWLUCUYMUYHUSUYKVAUDWTGWTBWTUDGBXAXBXCXDVRXEVRUDB
        WSXGXEUDBXHWEXIUVRUVKUXTXJXKUVLUXSUXRUYAUVLUXSUXOUXMUVLUXSUSZUXOUSFUVRB
        ABXLUCZUYPUVJABXPWOUHUCUYQNBXMWEXNAFBXOUHUCUYPUVJOXNUVLUXSUXOXQXRXSUYAU
        XRVAUVLUYAUVRBVKZUXRUVRBXTUYRUXOUXMUYRUXOUSUXMBFUHZWLUCZAUYTUYRUVJTXNUY
        RUXMUYTYAUXOUYRUVSUYSWLUVRBFVGVHWCYBYCWEYHYDYEYIYFYGAUVJUXMUXNVAZUVLAIW
        LUCZJWLUCZVUAUVJAIUDUDYJZWOUHUCVUBLVUDIUUAWEUVJJJUUJWIVUBVUCUSZUXMUXLUW
        BUXIVUEUXMUXLUWBUXIVAVUEUXMUXLUSZUSZUWEUWBUXHVUGUWEJYKUCZUVNJWRUQZJUVSU
        PUQZUGZUWBUXHVAZVUGUVNYKUCZUVSYKUCZUSZUWEVUKYAVUFVUOVUEUXMVUNUXLVUMUVSY
        LUVNYLUUBUUCUVNUVSJUUKWEVUKVUGVULVUJVUHVUGVULVAVUIVUGVUJVULVUGVUJUWBUXH
        VUGVUJUWBUSZUSUXEUWAUPUQZUWAIUPUQZUXHVUGVUJUWBVUQVUGVUJUSZUXEUVTUPUQZUW
        BVUQVUSJUVSUVNVUBVUCVUFVUJUUDVUEUXMUXLVUJUUEZVUEUXMUXLVUJUUFZVUGVUJUUGU
        UHVUSUXEWLUCZUVTWLUCUWAWLUCZVUTUWBUSVUQVAVUGVVCVUJVUGJUVNVUBVUCVUFXQVUE
        UXMUXLYMYNZWCVUSUVSUVNVVAVVBYNVUSIUOVUBVUCVUFVUJUUIUOWLUCZVUSYOYHYNUXEU
        VTUWAYPYQUULUUMVUGVURVUPVUEVURVUFVUEVBUOUPUQVURUUNVUEUOIVVFVUEYOYHVUBVU
        CUUOUUPUUQWCWCVUGVUQVURUSUXHVAZVUPVUGVVCVVDVUBVVGVVEVUGIUOVUBVUCVUFUURZ
        VVFVUGYOYHYNVVHUXEUWAIYPYQWCUVAYRYFUUSYFYEUUTYRXDUVBYSYIUVCUVDYTYSUVEYT
        UVFUVGUXCUWEUWFYMUVHYCUVI $.
    $}

    $d D p q r $.  $d F m p q r $.  $d I m p q r $.  $d N m n $.
    $d X m p q r $.  $d ph p q r $.
    $( Lemma 4 for ~ bgoldbtbnd .  (Contributed by AV, 1-Aug-2020.) $)
    bgoldbtbndlem4 $p |- ( ( ( ph /\ I e. ( 1 ..^ D ) ) /\ X e. Odd )
                           -> ( ( X e. ( ( F ` I ) [,) ( F ` ( I + 1 ) ) )
                                  /\ ( X - ( F ` I ) ) <_ 4 )
                                -> E. p e. Prime E. q e. Prime E. r e. Prime
                                   ( ( p e. Odd /\ q e. Odd /\ r e. Odd )
                                     /\ X = ( ( p + q ) + r ) ) ) ) $=
      ( vm c1 cfzo co wcel wa codd cfv caddc cico cmin c4 cle wbr ceven clt w3a
      cv wceq cprime wrex wi simpll simpr eqid bgoldbtbndlem2 syl3anc cgbe wral
      simplr breq2 breq1 anbi12d eleq1 imbi12d cbvralvw rspcv biimtrid id isgbe
      c2 csn cdif cc0 simp1 ralimi cn0 cn cuz elfzo1 nnm1nn0 3ad2ant1 sylbi a1i
      c3 eluz3nn a1d cz elfzo2 cr eluzelre adantr 1red resubcld zre adantl lttr
      ltm1d mpand 3impia 3jcad syl imp elfzo0 sylibr fveq2 eleq1d eldifi expcom
      syl6 com13 mpcom ad2antrr wb 3anbi3d eqeq2d oddprmALTV ad3antrrr anim12ci
      oveq2 3simpa df-3an cc oddz zcnd com23 reximdva syld prmz oveq1 sylan9req
      npcand exp31 impcom jca rspcedvd ex exp41 com25 syl6com ancoms 3impib mpd
      com15 imp31 ) AFUDBUEUFUGZUHZIUIUGZUHZIFEUJZFUDUKUFEUJULUFUGIUVBUMUFUNUOU
      PUHZIFUDUMUFZEUJZUMUFZUQUGZUVFHURUPZUNUVFURUPZUSZLUTZUIUGZKUTZUIUGZJUTZUI
      UGZUSZIUVKUVMUKUFZUVOUKUFZVAZUHZJVBVCZKVBVCZLVBVCZUVAAUUTUURUVCUVJVDAUURU
      UTVEUUSUUTVFAUURUUTVLABUVFCDEFGHIMNOPQRSTUAUVFVGVHVIAUURUUTUVJUWDVDZAUNDU
      TZURUPZUWFHURUPZUHZUWFVJUGZVDZDUQVKZUURUUTUWEVDVDOUVJUWLUURUUTAUWDUVGUVHU
      VIUWLUURUUTAUWDVDVDVDZVDUVGUWLUVHUVIUHZUWMUVGUWLUVIUVHUHZUVFVJUGZVDZUWNUW
      MVDUWLUNUCUTZURUPZUWRHURUPZUHZUWRVJUGZVDZUCUQVKUVGUWQUWKUXCDUCUQUWFUWRVAZ
      UWIUXAUWJUXBUXDUWGUWSUWHUWTUWFUWRUNURVMUWFUWRHURVNVOUWFUWRVJVPVQVRUXCUWQU
      CUVFUQUWRUVFVAZUXAUWOUXBUWPUXEUWSUVIUWTUVHUWRUVFUNURVMUWRUVFHURVNVOUWRUVF
      VJVPVQVSVTUWNUWQUVGUWMUVIUVHUWQUVGUWMVDZVDUWQUWOUWPUXFUWQWAUWPUWMUVGUWPUV
      GUVLUVNUVFUVRVAZUSZKVBVCZLVBVCZUHUWMUVFKLWBUVGUXJUWMUVGAUURUUTUXJUWDUVGAU
      URUUTUXJUWDVDUVGAUHZUURUHZUUTUHZUXIUWCLVBUXMUVKVBUGZUHZUXHUWBKVBUXOUVMVBU
      GZUHZUXHUWBUXQUXHUHZUWAUVLUVNUVEUIUGZUSZIUVRUVEUKUFZVAZUHZJUVEVBUXOUVEVBU
      GZUXPUXHUXLUYDUUTUXNUXKUURUYDAUURUYDVDZUVGCUTZEUJZVBWCWDZWEZUGZUYFUDUKUFE
      UJUYGUMUFZHUNUMUFURUPZUNUYKURUPZUSZCWFBUEUFZVKZAUYERUYPUYJCUYOVKZAUYEVDUY
      NUYJCUYOUYJUYLUYMWGWHZUURAUYQUYDAUURUYQUYDVDUUSUYQUVEUYIUGZUYDUUSUVDUYOUG
      ZUYQUYSVDUUSUVDWIUGZBWJUGZUVDBURUPZUSZUYTAUURVUDABWQWKUJUGZUURVUDVDPVUEUU
      RVUAVUBVUCUURVUAVDVUEUURFWJUGZVUBFBURUPZUSVUABFWLVUFVUBVUAVUGFWMWNWOWPVUE
      VUBUURBWRWSUURVUCVDVUEUURFUDWKUJUGZBWTUGZVUGUSVUCFUDBXAVUHVUIVUGVUCVUHVUI
      UHZUVDFURUPZVUGVUCVUJFVUHFXBUGZVUIUDFXCXDZXJVUJUVDXBUGVULBXBUGZVUKVUGUHVU
      CVDVUJFUDVUMVUJXEXFVUMVUIVUNVUHBXGXHUVDFBXIVIXKXLWOWPXMXNXOUVDBXPXQUYJUYS
      CUVDUYOUYFUVDVAUYGUVEUYIUYFUVDEXRXSVSXNZUVEVBUYHXTZYBYAYCXNYDXHXOYEYEUVOU
      VEVAZUWAUYCYFUXRVUQUVQUXTUVTUYBVUQUVPUXSUVLUVNUVOUVEUIVPYGVUQUVSUYAIUVOUV
      EUVRUKYLYHVOXHUXRUXTUYBUXRUVLUVNUHZUXSUHUXTUXQUXSUXHVURUXLUXSUUTUXNUXPUXK
      UURUXSAUURUXSVDZUVGUYPAVUSRUYPUYQAVUSVDUYRUURAUYQUXSAUURUYQUXSVDUUSUYQUYS
      UXSVUOUVEYIYBYAYCXNYDXHXOYJUVLUVNUXGYMYKUVLUVNUXSYNXQUXHUXQUYBUVLUVNUXGUX
      QUYBVDVURUXQUXGUYBVURUXQUXGUYBVURUXQUHZUXGIUVFUVEUKUFUYAVUTIUVEUXQIYOUGZV
      URUXMVVAUXNUXPUUTVVAUXLUUTIIYPYQXHYEXHUXQUVEYOUGZVURUXLVVBUUTUXNUXPUXKUUR
      VVBAUURVVBVDZUVGUYPAVVCRUYPUYQAVVCVDUYRUURAUYQVVBAUURUYQVVBVDUUSUYQUYSVVB
      VUOUYSUYDVVBVUPUYDUVEUVEUUAYQXNYBYAYCXNYDXHXOYJXHUUDUVFUVRUVEUKUUBUUCUUEY
      RXLUUFUUGUUHUUIYSYSUUJUUKXOWOWSUULUUMYCYTYRUUNUUPUUOUUQYT $.

    $d D f i j $.  $d F f i j m $.  $d M j p q r $.  $d N i m n $.
    $d N p q r $.  $d ph j n p q r $.  $d f j n $.
    $( If the binary Goldbach conjecture is valid up to an integer ` N ` , and
       there is a series ("ladder") of primes with a difference of at most
       ` N ` up to an integer ` M ` , then the strong ternary Goldbach
       conjecture is valid up to ` M ` , see section 1.2.2 in [Helfgott] p. 4
       with N = 4 x 10^18, taken from [OeSilva], and M = 8.875 x 10^30.
       (Contributed by AV, 1-Aug-2020.) $)
    bgoldbtbnd $p |- ( ph -> A. n e. Odd ( ( 7 < n /\ n < M )
                                           -> n e. GoldbachOdd ) ) $=
      ( wa wcel wi vp vq vr vf vj vm c7 clt wbr cgbo codd w3a caddc wceq cprime
      cv co wrex simprl cc0 cfv cico c1 cfzo ciccp wral cn c3 eluz3nn iccelpart
      cuz syl fveq1 oveq12d eleq2d rexbidv imbi12d rspcv cxr oddz zred ad2antrl
      cle rexrd cr 7re ltle sylancr com12 adantr impcom adantl eluzelre simprrr
      cdc xrlttrd wb oveq1d rexri elico1 bitrd mpbir3and csn wo cun fzo0sn0fzo1
      elun velsn fveq2 fv0p1e1 sylan9eq simprrl simpr bgoldbtbndlem1 syl3anc ex
      bitrdi isgbo sylbid sylbi cmin c4 expcomd ceven breq2 breq1 anbi12d eleq1
      cgbe 3ad2ant1 sylibr cc zcnd ad2antlr com23 jca reximdva imp syld mpd a1d
      sylib simprd c2 cdif fzo0ss1 sseli eleq1d fvoveq1 breq1d breq2d 3anbi123d
      mpan9 bgoldbtbndlem4 ad2ant2r simplll eqid bgoldbtbndlem3 cbvralvw pm3.35
      simpllr biimtrid isgbe eldifi ad5antlr 3anbi3d eqeq2d oddprmALTV ad4antlr
      oveq2 3simpa anim12ci df-3an npcand oveq1 sylan9req exp31 3impia rspcedvd
      prmz exp41 com25 ancoms com13 3impib com15 impl resubcld lelttric sylancl
      4re mpjaod mpdan expcom impd jaoi rexlimdv embantd exp32 ralrimiv ) AUGDU
      PZUHUIZUXAFUHUIZRZUXAUJSZTDUKAUXAUKSZUXDUXEAUXFUXDRZRZUXFUAUPZUKSZUBUPZUK
      SZUCUPZUKSZULZUXAUXIUXKUMUQZUXMUMUQZUNZRZUCUOURZUBUOURZUAUOURZRZUXEUXHUXF
      UYBAUXFUXDUSZAUXGUYBAUXAUTUDUPZVAZBUYEVAZVBUQZSZUXAUEUPZUYEVAZUYJVCUMUQZU
      YEVAZVBUQZSZUEUTBVDUQZURZTZUDBVEVAZVFZUXGUYBTZABVGSZUYTABVHVKVASVUBKBVIVL
      ZUEBUXAUDVJVLAUYTUXAUTEVAZBEVAZVBUQZSZUXAUYJEVAZUYLEVAZVBUQZSZUEUYPURZTZV
      UAAEUYSSUYTVUMTLUYRVUMUDEUYSUYEEUNZUYIVUGUYQVULVUNUYHVUFUXAVUNUYFVUDUYGVU
      EVBUTUYEEVMBUYEEVMVNVOVUNUYOVUKUEUYPVUNUYNVUJUXAVUNUYKVUHUYMVUIVBUYJUYEEV
      MUYLUYEEVMVNVOVPVQVRVLAUXGVUMUYBAUXGVUMUYBTUXHVUGVULUYBUXHVUGUXAVSSZUGUXA
      WCUIZUXAVUEUHUIZUXFVUOAUXDUXFUXAUXFUXAUXAVTZWAZWDWBZUXGVUPAUXDUXFVUPUXBUX
      FVUPTUXCUXFUXBVUPUXFUGWESUXAWESZUXBVUPTWFVUSUGUXAWGWHWIWJWKWLUXHUXAFVUEVU
      TAFVSSZUXGAFVCVCWOZVKVASZVVBHVVDFVVCFWMWDVLWJAVUEVSSZUXGAVUEQWDWJZAUXFUXB
      UXCWNAFVUEUHUIUXGPWJWPUXHVUGUXAUGVUEVBUQZSZVUOVUPVUQULZAVUGVVHWQUXGAVUFVV
      GUXAAVUDUGVUEVBNWRVOWJUXHUGVSSVVEVVHVVIWQUGWFWSVVFUGVUEUXAWTWHXAXBUXHVUKU
      YBUEUYPUXHUYJUYPSZUYJUTXCZSZUYJVCBVDUQZSZXDZVUKUYBTZAVVJVVOWQZUXGAVUBVVQV
      UCVUBVVJUYJVVKVVMXEZSVVOVUBUYPVVRUYJBXFVOUYJVVKVVMXGXQVLWJVVOUXHVVPVVLUXH
      VVPTZVVNVVLUYJUTUNZVVSUEUTXHVVTUXHVVPVVTUXHRZVUKUXAUGVCVHWOZVBUQZSZUYBVWA
      VUJVWCUXAVVTUXHVUJVUDVCEVAZVBUQZVWCVVTVUHVUDVUIVWEVBUYJUTEXIEUYJXJVNAVWFV
      WCUNUXGAVUDUGVWEVWBVBNOVNWJXKVOUXHVWDUYBTVVTUXHVWDUYBUXHVWDRZUXFUYBVWGUXE
      UYCVWGUXFUXBVWDUXEUXHUXFVWDUYDWJUXHUXBVWDAUXFUXBUXCXLWJUXHVWDXMUXAXNXOUXA
      UCUBUAXRZUUBUUCXPWLXSXPXTVVNAUXGVVPAVVNUXGVVPTZAVVNRZVUHUOUUDXCZUUEZSZVUI
      VUHYAUQZGYBYAUQZUHUIZYBVWNUHUIZULZVWIACUPZEVAZVWLSZVWSVCUMUQEVAZVWTYAUQZV
      WOUHUIZYBVXCUHUIZULZCUYPVFZVVNVWRMVVNVVJVXGVWRTVVMUYPUYJBUUFUUGVXFVWRCUYJ
      UYPVWSUYJUNZVXAVWMVXDVWPVXEVWQVXHVWTVUHVWLVWSUYJEXIZUUHVXHVXCVWNVWOUHVXHV
      XBVUIVWTVUHYAVWSUYJVCEUMUUIVXIVNZUUJVXHVXCVWNYBUHVXJUUKUULVRVLUUMVWJVWRRZ
      UXGVVPVXKUXGRZUXAVUHYAUQZYBWCUIZVVPYBVXMUHUIZVXLVUKVXNUYBVWJUXFVUKVXNRUYB
      TVWRUXDABCDEUYJFGUXAUCUBUAHIJKLMNOPQUUNUUOYCVXLVUKVXOUYBVXLVUKVXORZVXMYDS
      ZVXMGUHUIZVXOULZUYBVXLAUXFVVNVXPVXSTAVVNVWRUXGUUPVXKUXFUXDUSAVVNVWRUXGUVA
      ABVXMCDEUYJFGUXAHIJKLMNOPQVXMUUQUURXOVXKUXGVXSUYBTZAVVNVWRUXGVXTTZAYBUXAU
      HUIZUXAGUHUIZRZUXAYISZTZDYDVFZVVNVWRRZVYATJVXSVYGVYHUXGAUYBVXQVXRVXOVYGVY
      HUXGAUYBTTTZTVXQVYGVXRVXORZVYIVXQVYGVXOVXRRZVXMYISZTZVYJVYITVYGYBUFUPZUHU
      IZVYNGUHUIZRZVYNYISZTZUFYDVFVXQVYMVYFVYSDUFYDUXAVYNUNZVYDVYQVYEVYRVYTVYBV
      YOVYCVYPUXAVYNYBUHYEUXAVYNGUHYFYGUXAVYNYIYHVQUUSVYSVYMUFVXMYDVYNVXMUNZVYQ
      VYKVYRVYLWUAVYOVXOVYPVXRVYNVXMYBUHYEVYNVXMGUHYFYGVYNVXMYIYHVQVRUVBVYJVYMV
      XQVYIVXOVXRVYMVXQVYITZTVYKVYMWUBVYKVYMRVYLWUBVYKVYLUUTVYLVYIVXQVYLVXQUXJU
      XLVXMUXPUNZULZUBUOURZUAUOURZRVYIVXMUBUAUVCVXQWUFVYIVXQAVYHUXGWUFUYBVXQAVY
      HUXGWUFUYBTVXQARZVYHRZUXGRZWUEUYAUAUOWUIUXIUOSZRZWUDUXTUBUOWUKUXKUOSZRZWU
      DUXTWUMWUDRZUXSUXJUXLVUHUKSZULZUXAUXPVUHUMUQZUNZRZUCVUHUOVYHVUHUOSZWUGUXG
      WUJWULWUDVWRWUTVVNVWMVWPWUTVWQVUHUOVWKUVDZYJWLUVEUXMVUHUNZUXSWUSWQWUNWVBU
      XOWUPUXRWURWVBUXNWUOUXJUXLUXMVUHUKYHUVFWVBUXQWUQUXAUXMVUHUXPUMUVJUVGYGWLW
      UNWUPWURWUNUXJUXLRZWUORWUPWUMWUOWUDWVCVYHWUOWUGUXGWUJWULVWRWUOVVNVWMVWPWU
      OVWQVUHUVHYJWLUVIUXJUXLWUCUVKUVLUXJUXLWUOUVMYKWUDWUMWURUXJUXLWUCWUMWURTWV
      CWUMWUCWURWVCWUMWUCWURWVCWUMRWUCUXAVXMVUHUMUQZWUQWUKWVDUXAUNZWVCWULWUIWVE
      WUJWUIUXAVUHUXFUXAYLSWUHUXDUXFUXAVURYMWBVYHVUHYLSZWUGUXGVWRWVFVVNVWMVWPWV
      FVWQVWMWUTWVFWVAWUTVUHVUHUVTZYMVLYJWLYNUVNWJWBVXMUXPVUHUMUVOUVPUVQYOUVRWK
      YPUVSXPYQYQUWAUWBYRXTUUAVLXPUWCUWDYSYOUWEUWFYTUWGYRYSYCVXLVXMWESYBWESVXNV
      XOXDVXLUXAVUHUXFVVAVXKUXDVUSWBVWRVUHWESZVWJUXGVWMVWPWVHVWQVWMWUTWVHWVAWUT
      VUHWVGWAVLYJYNUWHUWKVXMYBUWIUWJUWLXPUWMUWNUWOUWPWIXSUWQUWRXPYOYSYTYRYPVWH
      YKUWSUWT $.
  $}

  $(
      The following theorems are not proven or are based on not proven
      theorems, provided as "axioms" temporarily.
  $)

  $( The binary Goldbach conjecture is valid for all even numbers less than or
     equal to 4x10^18, see section 2 in [OeSilva] p. 2042.  Temporarily
     provided as "axiom".  (Contributed by AV, 3-Aug-2020.)  (Revised by AV,
     9-Sep-2021.) $)
  ax-bgbltosilva $a |- ( ( N e. Even /\ 4 < N
                           /\ N <_ ( 4 x. ( ; 1 0 ^ ; 1 8 ) ) )
                        -> N e. GoldbachEven ) $.

  ${
    $d G m $.  $d O m p q r z $.  $d m n p q r z $.
    ax-tgoldbachgt.o $e |- O = { z e. ZZ | -. 2 || z } $.
    ax-tgoldbachgt.g $e |- G = { z e. O | E. p e. Prime E. q e. Prime
                           E. r e. Prime ( ( p e. O /\ q e. O /\ r e. O )
                                           /\ z = ( ( p + q ) + r ) ) } $.
    $( Temporary duplicate of ~ tgoldbachgt , provided as "axiom" as long as
       this theorem is in the mathbox of Thierry Arnoux:  Odd integers greater
       than ` ( ; 1 0 ^ ; 2 7 ) ` have at least a representation as a sum of
       three odd primes.  Final statement in section 7.4 of [Helfgott] p. 70 ,
       expressed using the set ` G ` of odd numbers which can be written as a
       sum of three odd primes.  (Contributed by Thierry Arnoux,
       22-Dec-2021.) $)
    ax-tgoldbachgt $a |- E. m e. NN ( m <_ ( ; 1 0 ^ ; 2 7 )
                          /\ A. n e. O ( m < n -> n e. G ) ) $.
  $}

  ${
    $d m n z p q r $.
    $( Variant of Thierry Arnoux's ~ tgoldbachgt using the symbols ` Odd ` and
       ` GoldbachOdd ` :  The ternary Goldbach conjecture is valid for large
       odd numbers (i.e. for all odd numbers greater than a fixed ` m ` ).
       This is proven by Helfgott (see section 7.4 in [Helfgott] p. 70) for
       ` m ` = 10^27.  (Contributed by AV, 2-Aug-2020.)  (Revised by AV,
       15-Jan-2022.) $)
    tgoldbachgtALTV $p |- E. m e. NN ( m <_ ( ; 1 0 ^ ; 2 7 )
                          /\ A. n e. Odd ( m < n -> n e. GoldbachOdd ) ) $=
      ( vz vr vq vp cgbo codd dfodd3 df-gbo ax-tgoldbachgt ) CABGHDEFCICDEFJK
      $.
  $}

  ${
    $d m n $.
    $( The binary Goldbach conjecture is valid for small even numbers (i.e. for
       all even numbers less than or equal to a fixed big ` m ` ).  This is
       verified for m = 4 x 10^18 by Oliveira e Silva, see ~ ax-bgbltosilva .
       (Contributed by AV, 3-Aug-2020.)  (Revised by AV, 9-Sep-2021.) $)
    bgoldbachlt $p |- E. m e. NN ( ( 4 x. ( ; 1 0 ^ ; 1 8 ) ) <_ m
                                     /\ A. n e. Even ( ( 4 < n /\ n < m )
                                                -> n e. GoldbachEven ) ) $=
      ( c4 c1 cc0 cdc c8 co cn wcel cv cle wbr clt wa wi ceven wral breq2 cr id
      cexp cmul cgbe wrex 4nn cn0 10nn 1nn0 8nn0 deccl nnexpcl nnmulcli wceq wb
      mp2an anbi2d imbi1d ralbidv anbi12d adantl nnre leidd simplr simprl evenz
      zred ltle syl2anr a1d imp32 ax-bgbltosilva syl3anc ralrimiva jca rspcedvd
      ex ax-mp ) CDEFZDGFZUBHZUCHZIJZWBAKZLMZCBKZNMZWFWDNMZOZWFUDJZPZBQRZOZAIUE
      CWAUFVSIJVTUGJWAIJUHDGUIUJUKVSVTULUPUMWCWMWBWBLMZWGWFWBNMZOZWJPZBQRZOZAWB
      IWCUAWDWBUNZWMWSUOWCWTWEWNWLWRWDWBWBLSWTWKWQBQWTWIWPWJWTWHWOWGWDWBWFNSUQU
      RUSUTVAWCWNWRWCWBWBVBZVCWCWQBQWCWFQJZOZWPWJXCWPOXBWGWFWBLMZWJWCXBWPVDXCWG
      WOVEXCWGWOXDXCWOXDPZWGXBWFTJWBTJXEWCXBWFWFVFVGXAWFWBVHVIVJVKWFVLVMVQVNVOV
      PVR $.

    $( There is a partition ("ladder") of primes from 7 to 8.8 x 10^30 with
       parts ("rungs") having lengths of at least 4 and at most N - 4, see
       section 1.2.2 in [Helfgott] p. 4.  Temporarily provided as "axiom".
       (Contributed by AV, 3-Aug-2020.)  (Revised by AV, 9-Sep-2021.) $)
    ax-hgprmladder $a |- E. d e. ( ZZ>= ` 3 ) E. f e. ( RePart ` d )
                     ( ( ( f ` 0 ) = 7 /\ ( f ` 1 ) = ; 1 3
                         /\ ( f ` d ) = ( ; 8 9 x. ( ; 1 0 ^ ; 2 9 ) ) )
                       /\ A. i e. ( 0 ..^ d )
                          ( ( f ` i ) e. ( Prime \ { 2 } )
                            /\ ( ( f ` ( i + 1 ) ) - ( f ` i ) )
                               < ( ( 4 x. ( ; 1 0 ^ ; 1 8 ) ) - 4 )
                            /\ 4 < ( ( f ` ( i + 1 ) ) - ( f ` i ) ) ) ) $.

    $d N d f i n $.
    $( The ternary Goldbach conjecture is valid for all odd numbers less than
       8.8 x 10^30 (actually 8.875694 x 10^30, see section 1.2.2 in [Helfgott]
       p. 4, using ~ bgoldbachlt , ~ ax-hgprmladder and ~ bgoldbtbnd .
       (Contributed by AV, 4-Aug-2020.)  (Revised by AV, 9-Sep-2021.) $)
    tgblthelfgott $p |- ( ( N e. Odd /\ 7 < N
                             /\ N < ( ; 8 8 x. ( ; 1 0 ^ ; 2 9 ) ) )
                           -> N e. GoldbachOdd ) $=
      ( cc0 cfv c1 cdc c8 co wcel c4 clt wbr wa wi cz cle mp2an cr nnrei pm3.2i
      nnzi vf vd vi vn cv c7 wceq c3 c9 c2 cexp cmul w3a cprime cdif caddc cmin
      csn cfzo wral wrex cuz codd cgbo ax-hgprmladder 1nn0 1nn decnncl 8nn0 8nn
      ciccp cn0 10nn 2nn0 9nn nnnn0i nnexpcl nnmulcli 1re 0le1 1lt10 declti 0re
      cn 10re 10pos ltleii cc nncni exp1 ax-mp breqtrri 1z 3pm3.2i 9nn0 ltexp2a
      2nn ltmul12a mp4an wb zmulcl zltp1le 1t10e1p1e11 eqcomi breq1i bitri mpbi
      eluz2 mpbir3an a1i 4nn 1lt4 4z cgbe ceven simpl simprl evenz zred sylancl
      4re ltle imp32 ax-bgbltosilva syl3anc ex ralrimiv ad2antrr simpr ad2antlr
      a1d simpl1 simpl2 nngt0i 8lt9 breq2 mpbiri 3ad2ant3 adantr eleq1 ltmul1a
      declt bgoldbtbnd exp31 rexlimivv breq1 anbi12d imbi12d rspcv com23 3impib
      sylcom ) BUAUEZCUFUGZDUUMCDUHEUGZUBUEZUUMCZFUIEZDBEZUJUIEZUKGZULGZUGZUMZU
      CUEZUUMCZUNUJURUOHUVEDUPGUUMCUVFUQGZIUUSDFEZUKGZULGZIUQGJKIUVGJKUMUCBUUPU
      SGUTZLZUAUUPVKCZVAUBUHVBCZVAZAVCHZUFAJKZAFFEZUVAULGZJKZUMZAVDHZMUAUCUBVEU
      VOUWAUFUDUEZJKZUWCUVSJKZLZUWCVDHZMZUDVCUTZUWBUVLUWAUWIMUBUAUVNUVMUUPUVNHZ
      UUMUVMHZLZUVLUWAUWIUWLUVLLUWALZUUPUCUDUUMUVSUVJUVSDDEZVBCZHZUWMUWPUWNNHZU
      VSNHZUWNUVSOKZUWNDDVFVGVHTZUVSUVRUVAFFVIVJVHZUUSWDHZUUTVLHUVAWDHVMUUTUJUI
      VNVOVHZVPUUSUUTVQPZVRTZDUUSDUKGZULGZUVSJKZUWSDQHZUVRQHZLBDOKZDUVRJKZLUXFQ
      HZUVAQHZLBUXFOKZUXFUVAJKZLUXHUXIUXJVSUVRUXARZSUXKUXLVTFFDVJVIVFWAWBSUXMUX
      NUXFUXBDVLHUXFWDHVMVFUUSDVQPZRZUVAUXDRZSUXOUXPBUUSUXFOBUUSWCWEWFWGUUSWHHU
      XFUUSUGUUSVMWIUUSWJWKWLZUUSQHZDNHZUUTNHZUMDUUSJKZDUUTJKZLUXPUYBUYCUYDWEWM
      UUTUXCTWNUYEUYFWAUJUIDWQWOVFWAWBSUUSDUUTWPPSDUVRUXFUVAWRWSUXHUXGDUPGZUVSO
      KZUWSUXGNHZUWRUXHUYHWTUYCUXFNHUYIWMUXFUXRTDUXFXAPZUXEUXGUVSXBPUYGUWNUVSOU
      WNUYGXCXDZXEXFXGUWNUVSXHXIXJUVJUWOHZUWMUYLUWQUVJNHZUWNUVJOKZUWTUVJIUVIXKU
      XBUVHVLHUVIWDHVMUVHDFVFVJVHZVPUUSUVHVQPZVRZTUXGUVJJKZUYNUXIIQHZLUXKDIJKZL
      UXMUVIQHZLUXOUXFUVIJKZLUYRUXIUYSVSYASUXKUYTVTXLSUXMVUAUXSUVIUYPRSUXOVUBUY
      AUYBUYCUVHNHZUMUYEDUVHJKZLVUBUYBUYCVUCWEWMUVHUYOTWNUYEVUDWADFDVGVIVFWAWBS
      UUSDUVHWPPSDIUXFUVIWRWSUYRUYGUVJOKZUYNUYIUYMUYRVUEWTUYJINHUVINHUYMXMUVIUY
      PTIUVIXAPUXGUVJXBPUYGUWNUVJOUYKXEXFXGUWNUVJXHXIXJUWMIUWCJKZUWCUVJJKZLZUWC
      XNHZMZUDXOUWCXOHZVUJMUWMVUKVUHVUIVUKVUHLVUKVUFUWCUVJOKZVUIVUKVUHXPVUKVUFV
      UGXQVUKVUFVUGVULVUKVUGVULMZVUFVUKUWCQHUVJQHVUMVUKUWCUWCXRXSUVJUYQRUWCUVJY
      BXTYKYCUWCYDYEYFXJYGUWLUWJUVLUWAUWJUWKXPYHUWLUWKUVLUWAUWJUWKYIYHUVLUVKUWL
      UWAUVDUVKYIYJUVLUUNUWLUWAUUNUUOUVCUVKYLYJUVLUUOUWLUWAUUNUUOUVCUVKYMYJUVLU
      VSUUQJKZUWLUWAUVDVUNUVKUVCUUNVUNUUOUVCVUNUVSUVBJKZUXJUURQHZUXNBUVAJKZLZUM
      UVRUURJKVUOUXJVUPVURUXQUURFUIVIVOVHZRUXNVUQUXTUVAUXDYNSWNFFUIVIVIVOYOUUBU
      VRUURUVAUUAPUUQUVBUVSJYPYQYRYSYJUVLUUQQHZUWLUWAUVDVUTUVKUVCUUNVUTUUOUVCVU
      TUVBQHUVBUURUVAVUSUXDVRRUUQUVBQYTYQYRYSYJUUCUUDUUEUVPUVQUVTUWIUWBMUVPUWIU
      VQUVTLZUWBUWHVVAUWBMUDAVCUWCAUGZUWFVVAUWGUWBVVBUWDUVQUWEUVTUWCAUFJYPUWCAU
      VSJUUFUUGUWCAVDYTUUHUUIUUJUUKUULWK $.

    $( The ternary Goldbach conjecture is valid for small odd numbers (i.e. for
       all odd numbers less than a fixed big ` m ` greater than 8 x 10^30).
       This is verified for m = 8.875694 x 10^30 by Helfgott, see
       ~ tgblthelfgott .  (Contributed by AV, 4-Aug-2020.)  (Revised by AV,
       9-Sep-2021.) $)
    tgoldbachlt $p |- E. m e. NN ( ( 8 x. ( ; 1 0 ^ ; 3 0 ) ) < m
                                     /\ A. n e. Odd ( ( 7 < n /\ n < m )
                                               -> n e. GoldbachOdd ) ) $=
      ( c8 cdc cc0 cexp co cmul cn wcel clt wbr wa codd 8nn 10nn nnmulcli caddc
      oveq1i nncni c1 c2 c9 c3 cv c7 cgbo wral wrex 8nn0 decnncl cn0 2nn0 deccl
      wi 9nn0 nnexpcl mp2an id wceq anbi2d imbi1d ralbidv anbi12d adantl simplr
      wb breq2 simprl simprr tgblthelfgott syl3anc ex ralrimiva nnrei 3nn0 0nn0
      nngt0i ltaddposi mpbi dfdec10 8cn adddiri mulcomi mulassi nncn a1i expp1d
      ax-mp eqcomi 3eqtr2i eqid decsucc oveq2i cc mulcom oveq1d 3eqtri breqtrri
      2p1e3 jctil rspcedvd ) CCDZUAEDZUBUCDZFGZHGZIJZCXDUDEDZFGZHGZAUEZKLZUFBUE
      ZKLZXNXLKLZMZXNUGJZUOZBNUHZMZAIUIXCXFCCUJOUKXDIJZXEULJZXFIJPUBUCUMUPUNZXD
      XEUQURZQXHYAXKXGKLZXOXNXGKLZMZXRUOZBNUHZMZAXGIXHUSXLXGUTZYAYKVGXHYLXMYFXT
      YJXLXGXKKVHYLXSYIBNYLXQYHXRYLXPYGXOXLXGXNKVHVAVBVCVDVEXHYJYFXHYIBNXHXNNJZ
      MZYHXRYNYHMYMXOYGXRXHYMYHVFYNXOYGVIYNXOYGVJXNVKVLVMVNXKXKCXFHGZRGZXGKEYOK
      LXKYPKLYOCXFOYEQZVRYOXKYOYQVOXKCXJOYBXIULJXJIJPUDEVPVQUNXDXIUQURZQVOVSVTX
      GXDCHGZCRGZXFHGYSXFHGZYORGZYPXCYTXFHCCWASYSCXFYSXDCPOQTZWBXFYETZWCUUBXDXE
      UARGZFGZCHGZYORGXJCHGZYORGZYPUUAUUGYORUUAXFYSHGXFXDHGZCHGUUGYSXFUUCUUDWDX
      FXDCUUDXDPTWBWEUUJUUFCHUUFUUJYBUUFUUJUTPYBXDXEXDWFYCYBYDWGWHWIWJSWKSUUGUU
      HYORUUFXJCHUUEXIXDFUBUDXEUMWTXEWLWMWNSSXJWOJZCWOJZUUIYPUTXJYRTWBUUKUULMUU
      HXKYORXJCWPWQURWRWRWSXAXBWI $.

    $d m n o $.
    $( The ternary Goldbach conjecture is valid.  Main theorem in [Helfgott]
       p. 2.  This follows from ~ tgoldbachlt and ~ ax-tgoldbachgt .
       (Contributed by AV, 2-Aug-2020.)  (Revised by AV, 9-Sep-2021.) $)
    tgoldbach $p |- A. n e. Odd ( 7 < n -> n e. GoldbachOdd ) $=
      ( vm vo c7 clt wbr wcel wi codd c1 cc0 co cle cr c8 wa pm3.2i a1i com23
      cn cv cgbo cdc c2 cexp oddz zred cn0 10re 2nn0 7nn decnncl nnnn0i reexpcl
      wo mp2an lelttric sylancl c3 cmul wral wrex tgoldbachlt wceq breq2 eleq1w
      breq1 anbi12d imbi12d rspcv recni mullidi 1re 8re 0le1 3nn decnncl2 10nn0
      1lt8 nn0expcli nn0ge0i w3a nnzi 3pm3.2i 1lt10 3nn0 7nn0 0nn0 7lt10 decltc
      cz 2lt3 ltexp2a ltmul12a syl22anc eqbrtrrid remulcli adantl syl3anc mpand
      nnre lttr imp adantr 3jca lelttr syl mpan2d anim1i ancomd pm2.27 ex exp41
      com25 syld com15 imp32 rexlimiva ax-mp tgoldbachgtALTV expcomd imp43 a1dd
      com14 impr jaoi mpcom rgen ) DAUAZEFZYIUBGZHZAIYIJKUCZUDDUCZUELZMFZYOYIEF
      ZUOZYIIGZYLYSYINGZYONGZYRYSYIYIUFUGZYMNGZYNUHGUUAUIYNUDDUJUKULZUMZYMYNUNU
      PZYIYOUQURYPYSYLHZYQOYMUSKUCZUELZUTLZBUAZEFZDCUAZEFZUUMUUKEFZPZUUMUBGZHZC
      IVAZPZBTVBYPUUGHZBCVCUUTUVABTUUKTGZUULUUSUVAUVBUUSUULUVAYSUUSUULYPUVBYLYS
      UUSYJYIUUKEFZPZYKHZUULYPUVBYLHHHUURUVECYIIUUMYIVDZUUPUVDUUQYKUVFUUNYJUUOU
      VCUUMYIDEVEUUMYIUUKEVGVHCAUBVFZVIVJYSUVBUULYPUVEYLYSUVBUULYPUVEYLHYSUVBPZ
      UULPZYPPZYJUVEYKUVJYJUVEYKHZUVJYJPZUVDUVKUVLUVCYJUVJUVCYJUVIYPUVCUVIYPYOU
      UKEFZUVCUVHUULUVMUVHYOUUJEFZUULUVMUVHYOJYOUTLZUUJEYOYOUUFVKVLUVHJNGZONGZP
      ZKJMFZJOEFZPZUUAUUINGZPZKYOMFZYOUUIEFZPZUVOUUJEFUVRUVHUVPUVQVMVNQRUWAUVHU
      VSUVTVOVSQRUWCUVHUUAUWBUUFUUCUUHUHGUWBUIUUHUSVPVQZUMYMUUHUNUPZQRUWFUVHUWD
      UWEYOYMYNVRUUEVTWAUUCYNWKGZUUHWKGZWBJYMEFZYNUUHEFZPUWEUUCUWIUWJUIYNUUDWCU
      UHUWGWCWDUWKUWLWEUDUSDKUJWFWGWHWIWLWJQYMYNUUHWMUPQRJOYOUUIWNWOWPUVHUUAUUJ
      NGZUUKNGZUVNUULPUVMHUUAUVHUUFRZUWMUVHOUUIVNUWHWQRUVBUWNYSUUKXAWRZYOUUJUUK
      XBWSWTXCUVIYTUUAUWNWBZYPUVMPUVCHUVHUWQUULUVHYTUUAUWNYSYTUVBUUBXDZUWOUWPXE
      XDYIYOUUKXFXGXHXCXIXJUVDYKXKXGXLSXMXNXOXPSXQXRXSUUKYOMFZUUKUUMEFZUUQHZCIV
      AZPZBTVBYQUUGHZBCXTUXCUXDBTUVBUWSUXBUXDYSUXBYQUVBUWSPZYLYSUXBUUKYIEFZYKHZ
      YQUXEYLHZHUXAUXGCYIIUVFUWTUXFUUQYKUUMYIUUKEVEUVGVIVJYSYQUXGUXHYSYQUXGUXHH
      YSYQPZUXEUXGYLUXIUXEUXGYLHUXIUXEPZUXGYKYJUXJUXFUXGYKHYSYQUVBUWSUXFYSUVBYQ
      UWSUXFHZYSUVBYQUXKHUVHUWSYQUXFUVHUWNUUAYTUWSYQPUXFHUWPUWOUWRUUKYOYIXFWSYA
      XLSYBUXFYKXKXGYCXLSXLSXOYDYEXRXSYFYGYH $.
  $}

  $(
    @( The binary Goldbach conjecture is valid. @)
    goldbach @p |- A. n e. Even ( 4 < n -> n e. GoldbachEven ) @=
      ? @.
  $)
