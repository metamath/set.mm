$[ set-main.mm $]
$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Mathbox for Asger C. Ipsen
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Continuous nowhere differentiable functions
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d A x $.
    dnival.1 $e |- T = ( x e. RR |->
                            ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) ) $.
    $( Value of the "distance to nearest integer" function.  (Contributed by
       Asger C. Ipsen, 4-Apr-2021.) $)
    dnival $p |- ( A e. RR ->
              ( T ` A ) = ( abs ` ( ( |_ ` ( A + ( 1 / 2 ) ) ) - A ) ) ) $=
      ( cv c1 c2 cdiv co caddc cfl cfv cmin cabs cr wceq fvoveq1 oveq12d fveq2d
      id fvex fvmpt ) ABAEZFGHIZJIKLZUCMIZNLBUDJIKLZBMIZNLOCUCBPZUFUHNUIUEUGUCB
      MUCBUDKJQUITRSDUHNUAUB $.
  $}

  ${
    dnicld1.1 $e |- ( ph -> A e. RR ) $.
    $( Closure theorem for the "distance to nearest integer" function.
       (Contributed by Asger C. Ipsen, 4-Apr-2021.) $)
    dnicld1 $p |- ( ph -> ( abs ` ( ( |_ ` ( A + ( 1 / 2 ) ) ) - A ) ) e. RR )
      $=
      ( c1 c2 cdiv co caddc cfl cfv cmin cr wa halfre a1i jca readdcl syl recnd
      wcel reflcl subcld abscld ) ABDEFGZHGZIJZBKGAUFBAUFAUELTZUFLTABLTZUDLTZMU
      GAUHUICUIANOPBUDQRUEUARSABCSUBUC $.
  $}

  ${
    $d A x $.
    dnicld2.1 $e |- T = ( x e. RR |->
                            ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) ) $.
    dnicld2.2 $e |- ( ph -> A e. RR ) $.
    $( Closure theorem for the "distance to nearest integer" function.
       (Contributed by Asger C. Ipsen, 4-Apr-2021.) $)
    dnicld2 $p |- ( ph -> ( T ` A ) e. RR ) $=
      ( cfv c1 c2 cdiv co caddc cfl cmin cabs cr wcel wceq dnival syl dnicld1
      eqeltrd ) ACDGZCHIJKLKMGCNKOGZPACPQUCUDRFBCDESTACFUAUB $.
  $}

  ${
    dnif.t $e |- T = ( x e. RR |->
                            ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) ) $.
    $( The "distance to nearest integer" function is a function.  (Contributed
       by Asger C. Ipsen, 4-Apr-2021.) $)
    dnif $p |- T : RR --> RR $=
      ( cr cv c1 c2 cdiv co caddc cfl cfv cmin cabs wcel id dnicld1 fmpti ) ADD
      AEZFGHIJIKLSMINLBCSDOZSTPQR $.
  $}

  ${
    $d A x $.
    dnizeq0.t $e |- T = ( x e. RR |->
                            ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) ) $.
    dnizeq0.1 $e |- ( ph -> A e. ZZ ) $.
    $( The distance to nearest integer is zero for integers.  (Contributed by
       Asger C. Ipsen, 15-Jun-2021.) $)
    dnizeq0 $p |- ( ph -> ( T ` A ) = 0 ) $=
      ( cfv c1 co caddc cmin cabs cc0 wcel wceq syl halfre a1i cxr eqtrd c2 cfl
      cdiv cr zred dnival cz wa jca flzadd cle wbr clt w3a rexri halfgt0 ltleii
      cico 0re halflt1 3pm3.2i wb 0xr pm3.2i elico1 ax-mp mpbir ico01fl0 oveq2d
      1xr recnd addridd oveq1d subidd fveq2d abs0 ) ACDGZCHUAUCIZJIUBGZCKIZLGZM
      ACUDNVQWAOACFUEZBCDEUFPAWAMLGZMAVTMLAVTCCKIMAVSCCKAVSCVRUBGZJIZCACUGNZVRU
      DNZUHVSWEOAWFWGFWGAQRUIVRCUJPAWECMJICAWDMCJAVRMHURINZWDMOWHAWHVRSNZMVRUKU
      LZVRHUMULZUNZWIWJWKVRQUOMVRUSQUPUQUTVAMSNZHSNZUHWHWLVBWMWNVCVJVDMHVRVEVFV
      GRVRVHPVIACACWBVKZVLTTVMACWOVNTVOWCMOAVPRTT $.
  $}

  ${
    $d A x $.
    dnizphlfeqhlf.t $e |- T = ( x e. RR |->
                            ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) ) $.
    dnizphlfeqhlf.1 $e |- ( ph -> A e. ZZ ) $.
    $( The distance to nearest integer is a half for half-integers.
       (Contributed by Asger C. Ipsen, 15-Jun-2021.) $)
    dnizphlfeqhlf $p |- ( ph -> ( T ` ( A + ( 1 / 2 ) ) ) = ( 1 / 2 ) ) $=
      ( c1 co caddc cfv cabs cr wcel wceq halfre a1i syl recnd cz cc0 cdiv cmin
      c2 cfl zred readdcld dnival addcld addassd 2halvesd oveq2d eqtrd peano2zd
      1cnd eqeltrd flid mvrladdd fveq2d cle wbr clt halfgt0 ltlei absidd 3eqtrd
      0re ax-mp ) ACGUCUAHZIHZDJZVIVHIHZUDJZVIUBHZKJZVHKJVHAVILMVJVNNACVHACFUEZ
      VHLMAOPZUFBVIDEUGQAVMVHKAVLVIVHACVHACVORZAVHVPRZUHVRAVKSMVLVKNAVKCGIHZSAV
      KCVHVHIHZIHVSACVHVHVQVRVRUIAVTGCIAGAUNUJUKULACFUMUOVKUPQUQURAVHVPTVHUSUTZ
      ATVHVAUTWAVBTVHVFOVCVGPVDVE $.
  $}

  $( Variant of ~ rddif .  (Contributed by Asger C. Ipsen, 4-Apr-2021.) $)
  rddif2 $p |- ( A e. RR ->
    0 <_ ( ( 1 / 2 ) - ( abs ` ( ( |_ ` ( A + ( 1 / 2 ) ) ) - A ) ) ) ) $=
    ( cr wcel cc0 c1 c2 cdiv co caddc cfl cfv cmin cabs cle wbr rddif halfre id
    a1i dnicld1 subge0d mpbird ) ABCZDEFGHZAUDIHJKALHMKZLHNOUEUDNOAPUCUDUEUDBCU
    CQSUCAUCRTUAUB $.

  ${
    $d A x $.  $d B x $.
    dnibndlem1.1 $e |- T = ( x e. RR |->
                            ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) ) $.
    dnibndlem1.2 $e |- ( ph -> A e. RR ) $.
    dnibndlem1.3 $e |- ( ph -> B e. RR ) $.
    $( Lemma for ~ dnibnd .  (Contributed by Asger C. Ipsen, 4-Apr-2021.) $)
    dnibndlem1 $p |- ( ph -> ( ( abs ` ( ( T ` B ) - ( T ` A ) ) ) <_ S
                          <->
                          ( abs `
                             ( ( abs ` ( ( |_ ` ( B + ( 1 / 2 ) ) ) - B ) ) -
                               ( abs ` ( ( |_ ` ( A + ( 1 / 2 ) ) ) - A ) ) ) )
                            <_ S ) ) $=
      ( cfv cmin co cabs caddc cfl cr wcel wceq dnival syl c1 c2 oveq12d fveq2d
      cdiv cle breq1d ) ADFJZCFJZKLZMJDUAUBUELZNLOJDKLMJZCUKNLOJCKLMJZKLZMJEUFA
      UJUNMAUHULUIUMKADPQUHULRIBDFGSTACPQUIUMRHBCFGSTUCUDUG $.
  $}

  ${
    $d A x $.  $d B x $.
    dnibndlem2.1 $e |- T = ( x e. RR |->
                            ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) ) $.
    dnibndlem2.2 $e |- ( ph -> A e. RR ) $.
    dnibndlem2.3 $e |- ( ph -> B e. RR ) $.
    dnibndlem2.4 $e |- ( ph ->
                  ( |_ ` ( B + ( 1 / 2 ) ) ) = ( |_ ` ( A + ( 1 / 2 ) ) ) ) $.
    $( Lemma for ~ dnibnd .  (Contributed by Asger C. Ipsen, 4-Apr-2021.) $)
    dnibndlem2 $p |- ( ph -> ( abs ` ( ( T ` B ) - ( T ` A ) ) )
                              <_ ( abs ` ( B - A ) ) ) $=
      ( cfv cmin co cabs cle wbr cr wcel recnd subcld abscld c1 c2 caddc cfl wa
      halfre a1i jca readdcl syl reflcl cc eqeltrrd abs2difabsd nnncan1d eqcomd
      cdiv fveq2d oveq1d abssubd 3eqtrd leidd eqbrtrrd letrd dnibndlem1 mpbird
      ) ADEJCEJKLMJDCKLZMJZNODUAUBUQLZUCLZUDJZDKLZMJZCVIUCLUDJZCKLZMJZKLZMJZVHN
      OAVRVLVOKLZMJZVHAVQAVMVPAVMAVLAVKDAVKAVJPQZVKPQADPQZVIPQZUEWAAWBWCHWCAUFU
      GUHDVIUIUJVJUKUJRZADHRZSZTRAVPAVOAVNCAVKVNULIWDUMACGRZSZTRSTAVSAVLVOWFWHS
      TAVGADCWEWGSTZAVLVOWFWHUNAVHVTVHNAVHVKCKLZVLKLZMJVOVLKLZMJVTAVGWKMAWKVGAV
      KCDWDWGWEUOUPURAWKWLMAWJVOVLKAVKVNCKIUSUSURAVOVLWHWFUTVAAVHWIVBVCVDABCDVH
      EFGHVEVF $.
  $}

  ${
    dnibndlem3.1 $e |- T = ( x e. RR |->
                            ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) ) $.
    dnibndlem3.2 $e |- ( ph -> A e. RR ) $.
    dnibndlem3.3 $e |- ( ph -> B e. RR ) $.
    dnibndlem3.4 $e |- ( ph ->
          ( |_ ` ( B + ( 1 / 2 ) ) ) = ( ( |_ ` ( A + ( 1 / 2 ) ) ) + 1 ) ) $.
    $( Lemma for ~ dnibnd .  (Contributed by Asger C. Ipsen, 4-Apr-2021.) $)
    dnibndlem3 $p |- ( ph -> ( abs ` ( B - A ) ) =
        ( abs ` ( ( B - ( ( |_ ` ( B + ( 1 / 2 ) ) ) - ( 1 / 2 ) ) )
                  + ( ( ( |_ ` ( A + ( 1 / 2 ) ) ) + ( 1 / 2 ) ) - A ) ) ) )
      $=
      ( cmin co c1 caddc cc wcel wceq recnd cr a1i syl c2 cdiv cfl cfv cabs w3a
      wa halfre jca readdcl reflcl halfcn subcld 3jca npncan eqcomd oveq1d 1cnd
      addsubass 1mhlfehlf oveq2d 3eqtrd eqtrd fveq2d ) ADCJKZDDLUAUBKZMKZUCUDZV
      FJKZJKZCVFMKZUCUDZVFMKZCJKZMKZUEAVEVJVICJKZMKZVOAVQVEADNOZVINOZCNOZUFVQVE
      PAVRVSVTADHQAVHVFAVHAVGROZVHROADROZVFROZUGWAAWBWCHWCAUHSZUIDVFUJTVGUKTQVF
      NOZAULSZUMACGQUNDVICUOTUPAVPVNVJMAVIVMCJAVIVLLMKZVFJKZVLLVFJKZMKZVMAVHWGV
      FJIUQAVLNOZLNOZWEUFWHWJPAWKWLWEAVLAVKROZVLROACROZWCUGWMAWNWCGWDUICVFUJTVK
      UKTQAURWFUNVLLVFUSTAWIVFVLMWIVFPAUTSVAVBUQVAVCVD $.
  $}

  $( Lemma for ~ dnibnd .  (Contributed by Asger C. Ipsen, 4-Apr-2021.) $)
  dnibndlem4 $p |- ( B e. RR ->
    0 <_ ( B - ( ( |_ ` ( B + ( 1 / 2 ) ) ) - ( 1 / 2 ) ) ) ) $=
    ( cr wcel cc0 c1 c2 cdiv caddc cfl cfv cmin cle wbr halfre a1i readdcld syl
    co id mpbird flle reflcl lesubaddd wa jca resubcl subge0d ) ABCZDAAEFGRZHRZ
    IJZUIKRZKRLMULALMZUHUMUKUJLMZUHUJBCZUNUHAUIUHSZUIBCZUHNOZPZUJUAQUHUKUIAUHUO
    UKBCZUSUJUBQZURUPUCTUHAULUPUHUTUQUDULBCUHUTUQVAURUEUKUIUFQUGT $.

  $( Lemma for ~ dnibnd .  (Contributed by Asger C. Ipsen, 4-Apr-2021.) $)
  dnibndlem5 $p |- ( A e. RR ->
    0 < ( ( ( |_ ` ( A + ( 1 / 2 ) ) ) + ( 1 / 2 ) ) - A ) ) $=
    ( cr wcel c1 c2 cdiv co caddc cfl cfv clt wbr cc0 cmin a1i readdcl syl wceq
    cc recnd halfre syl2anc2 flltp1 ax-1cn 2halves ax-mp eqcomi oveq2d w3a 3jca
    id reflcl addass eqcomd eqtrd breqtrd wa jca ltadd1d mpbird posdifd mpbid )
    ABCZAADEFGZHGZIJZVDHGZKLZMVGANGKLVCVHVEVGVDHGZKLVCVEVFDHGZVIKVCVEBCZVEVJKLV
    CVCVDBCZVKVCUKZVLVCUAOZAVDPUBZVEUCQVCVJVFVDVDHGZHGZVIVCDVPVFHDVPRVCVPDDSCVP
    DRUDDUEUFUGOUHVCVIVQVCVFSCZVDSCZVSUIVIVQRVCVRVSVSVCVFVCVKVFBCZVOVEULQZTVCVD
    VNTZWBUJVFVDVDUMQUNUOUPVCAVGVDVMVCVTVLUQVGBCVCVTVLWAVNURVFVDPQZVNUSUTVCAVGV
    MWCVAVB $.

  ${
    dnibndlem6.1 $e |- ( ph -> A e. RR ) $.
    dnibndlem6.2 $e |- ( ph -> B e. RR ) $.
    $( Lemma for ~ dnibnd .  (Contributed by Asger C. Ipsen, 4-Apr-2021.) $)
    dnibndlem6 $p |- ( ph ->
            ( abs `
                 ( ( abs ` ( ( |_ ` ( B + ( 1 / 2 ) ) ) - B ) ) -
                   ( abs ` ( ( |_ ` ( A + ( 1 / 2 ) ) ) - A ) ) ) )
            <_
            ( ( ( 1 / 2 ) - ( abs ` ( ( |_ ` ( B + ( 1 / 2 ) ) ) - B ) ) ) +
              ( ( 1 / 2 ) - ( abs ` ( ( |_ ` ( A + ( 1 / 2 ) ) ) - A ) ) ) ) )
      $=
      ( co caddc cfl cfv cmin cabs dnicld1 subcld abscld cc wcel cr syl cle wbr
      c1 c2 recnd halfcn a1i readdcld wa halfre jca resubcl w3a abs3dif abssubd
      cdiv 3jca cc0 rddif2 absidd eqtrd oveq12d eqled letrd ) ACUAUBUNFZGFHICJF
      KIZBVCGFHIBJFKIZJFZKIZVDVCJFZKIZVCVEJFZKIZGFZVCVDJFZVJGFZAVFAVDVEAVDACELZ
      UCZAVEABDLZUCZMNAVIVKAVHAVDVCVPVCOPZAUDUEZMNAVJAVCVEVTVRMNUFZAVMVJAVCQPZV
      DQPZUGVMQPAWBWCWBAUHUEZVOUIVCVDUJRZAWBVEQPZUGVJQPAWBWFWDVQUIVCVEUJRZUFAVD
      OPZVEOPZVSUKVGVLSTAWHWIVSVPVRVTUOVDVEVCULRAVLVNWAAVIVMVKVJGAVIVMKIVMAVDVC
      VPVTUMAVMWEACQPUPVMSTECUQRURUSAVJWGABQPUPVJSTDBUQRURUTVAVB $.
  $}

  ${
    dnibndlem7.1 $e |- ( ph -> B e. RR ) $.
    $( Lemma for ~ dnibnd .  (Contributed by Asger C. Ipsen, 4-Apr-2021.) $)
    dnibndlem7 $p |- ( ph ->
        ( ( 1 / 2 ) - ( abs ` ( ( |_ ` ( B + ( 1 / 2 ) ) ) - B ) ) )
        <_ ( B - ( ( |_ ` ( B + ( 1 / 2 ) ) ) - ( 1 / 2 ) ) ) ) $=
      ( c1 c2 cdiv co caddc cfl cfv cmin cabs cle cr wcel wa jca recnd subsub3d
      syl halfre a1i readdcl reflcl resubcl dnicld1 leabsd oveq1d eqcomd 3eqtrd
      lesub2dd addcomd breqtrd ) ADEFGZBUNHGZIJZBKGZLJZKGUNUQKGZBUPUNKGKGZMAUQU
      RUNAUPNOZBNOZPUQNOAVAVBAUONOZVAAVBUNNOZPVCAVBVDCVDAUAUBZQBUNUCTUOUDTZCQUP
      BUETZABCUFVEAUQVGUGUKAUSUNBHGZUPKGUOUPKGZUTAUNUPBAUNVERZAUPVFRZABCRZSAVHU
      OUPKAUNBVJVLULUHAUTVIABUPUNVLVKVJSUIUJUM $.
  $}

  ${
    dnibndlem8.1 $e |- ( ph -> A e. RR ) $.
    $( Lemma for ~ dnibnd .  (Contributed by Asger C. Ipsen, 4-Apr-2021.) $)
    dnibndlem8 $p |- ( ph ->
        ( ( 1 / 2 ) - ( abs ` ( ( |_ ` ( A + ( 1 / 2 ) ) ) - A ) ) )
        <_ ( ( ( |_ ` ( A + ( 1 / 2 ) ) ) + ( 1 / 2 ) ) - A ) ) $=
      ( c1 c2 cdiv co caddc cfl cfv cmin cabs cle wcel halfre a1i recnd breqtrd
      cr syl jca simpl readdcld reflcl resubcld dnicld1 leabsd abssubd lesub2dd
      wa subsub3d addcomd oveq1d eqtrd ) ADEFGZBUOHGZIJZBKGLJZKGUOBUQKGZKGZUQUO
      HGZBKGZMAUSURUOABUQCAUPSNZUQSNABSNZUOSNZUJZVCAVDVECVEAOPZUAVFBUOVDVEUBVEV
      FOPUCTUPUDTZUEZABCUFVGAUSUSLJURMAUSVIUGABUQABCQZAUQVHQZUHRUIAUTUOUQHGZBKG
      VBAUOBUQAUOVGQZVJVKUKAVLVABKAUOUQVMVKULUMUNR $.
  $}

  ${
    $d A x $.  $d B x $.
    dnibndlem9.1 $e |- T = ( x e. RR |->
                            ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) ) $.
    dnibndlem9.2 $e |- ( ph -> A e. RR ) $.
    dnibndlem9.3 $e |- ( ph -> B e. RR ) $.
    dnibndlem9.4 $e |- ( ph ->
          ( |_ ` ( B + ( 1 / 2 ) ) ) = ( ( |_ ` ( A + ( 1 / 2 ) ) ) + 1 ) ) $.
    $( Lemma for ~ dnibnd .  (Contributed by Asger C. Ipsen, 4-Apr-2021.) $)
    dnibndlem9 $p |- ( ph -> ( abs ` ( ( T ` B ) - ( T ` A ) ) )
                              <_ ( abs ` ( B - A ) ) ) $=
      ( cfv cmin co cabs cle caddc recnd cr wcel wa syl wbr c1 cdiv cfl dnicld1
      c2 subcld abscld halfre a1i jca resubcl readdcld reflcl addcld dnibndlem6
      dnibndlem7 dnibndlem8 le2addd cc0 dnibndlem4 clt dnibndlem5 ltled addge0d
      0red absidd eqcomd breqtrd letrd dnibndlem3 dnibndlem1 mpbird ) ADEJCEJKL
      MJDCKLMJZNUADUBUFUCLZOLZUDJZDKLMJZCVOOLZUDJZCKLMJZKLZMJZVNNUAAWCDVQVOKLZK
      LZVTVOOLZCKLZOLZMJZVNNAWCVOVRKLZVOWAKLZOLZWIAWBAVRWAAVRADHUEZPAWAACGUEZPU
      GUHAWJWKAVOQRZVRQRZSWJQRAWOWPWOAUIUJZWMUKVOVRULTZAWOWAQRZSWKQRAWOWSWQWNUK
      VOWAULTZUMAWHAWEWGADWDADHPAVQVOAVQAVPQRVQQRZADVOHWQUMVPUNTZPAVOWQPZUGUGAW
      FCAVTVOAVTAVSQRVTQRACVOGWQUMVSUNTZPXCUOACGPUGUOUHACDGHUPAWLWHWINAWJWKWEWG
      WRWTADQRZWDQRZSWEQRAXEXFHAXAWOSXFAXAWOXBWQUKVQVOULTUKDWDULTZAWFQRZCQRZSWG
      QRAXHXIAVTVOXDWQUMGUKWFCULTZADHUQACGURUSAWIWHAWHAWEWGXGXJUMAWEWGXGXJAXEUT
      WENUAHDVATAUTWGAVFXJAXIUTWGVBUAGCVCTVDVEVGVHVIVJAVNWIABCDEFGHIVKVHVIABCDV
      NEFGHVLVM $.
  $}

  ${
    dnibndlem10.1 $e |- ( ph -> A e. RR ) $.
    dnibndlem10.2 $e |- ( ph -> B e. RR ) $.
    dnibndlem10.3 $e |- ( ph ->
          ( ( |_ ` ( A + ( 1 / 2 ) ) ) + 2 ) <_ ( |_ ` ( B + ( 1 / 2 ) ) ) ) $.
    $( Lemma for ~ dnibnd .  (Contributed by Asger C. Ipsen, 4-Apr-2021.) $)
    dnibndlem10 $p |- ( ph -> 1 <_ ( B - A ) ) $=
      ( c1 c2 co caddc cmin cr wcel wa a1i readdcld syl jca cle wbr cdiv halfre
      cfl cfv 1red reflcl resubcl resubcld recnd 2cnd addsubassd oveq1d pnpcand
      subcld subsub4d wceq cc ax-1cn 2halves ax-mp oveq2d 2m1e1 3eqtrd lesub1dd
      eqcomd eqbrtrd flle lesubaddd mpbird fllep1 addassd eqtrd breqtrd leadd1d
      2re le2subd letrd ) AGCGHUAIZJIZUCUDZVRKIZBVRJIZUCUDZVRJIZKIZCBKIAUEAWALM
      ZWDLMZNWELMAWFWGAVTLMZVRLMZNWFAWHWIAVSLMZWHACVREWIAUBOZPZVSUFQZWKRVTVRUGQ
      ZAWCVRAWBLMZWCLMABVRDWKPZWBUFQZWKPZRWAWDUGQACBEDUHAGWCHJIZVRKIZWDKIZWESAX
      AGAXAWCHVRKIZJIZWDKIXBVRKIZGAWTXCWDKAWCHVRAWCWQUIZAUJZAVRWKUIZUKULAWCXBVR
      XEAHVRXFXGUNXGUMAXDHVRVRJIZKIHGKIZGAHVRVRXFXGXGUOAXHGHKXHGUPZAGUQMXJURGUS
      UTOZVAXIGUPAVBOVCVCVEAWTWAWDAWSLMZWINWTLMAXLWIAWCHWQHLMAVOOPZWKRWSVRUGQWN
      WRAWSVTVRXMWMWKFVDVDVFAWABCWDWNDEWRAWACSTVTVSSTZAWJXNWLVSVGQAVTVRCWMWKEVH
      VIABWDSTWBWDVRJIZSTAWBWCGJIZXOSAWOWBXPSTWPWBVJQAXOXPAXOWCXHJIXPAWCVRVRXEX
      GXGVKAXHGWCJXKVAVLVEVMABWDVRDWRWKVNVIVPVQ $.
  $}

  ${
    dnibndlem11.1 $e |- ( ph -> A e. RR ) $.
    dnibndlem11.2 $e |- ( ph -> B e. RR ) $.
    $( Lemma for ~ dnibnd .  (Contributed by Asger C. Ipsen, 4-Apr-2021.) $)
    dnibndlem11 $p |- ( ph ->
                          ( abs `
                            ( ( abs ` ( ( |_ ` ( B + ( 1 / 2 ) ) ) - B ) ) -
                              ( abs ` ( ( |_ ` ( A + ( 1 / 2 ) ) ) - A ) ) ) )
                          <_ ( 1 / 2 ) ) $=
      ( co caddc cfl cfv cmin cabs cle wbr cneg dnicld1 resubcld wcel recnd syl
      cr c1 c2 cdiv wa halfre a1i negsubdi2d cc0 readdcld reflcl subcld absge0d
      subge02d mpbid rddif letrd eqbrtrd lenegcon1d jca absled mpbird ) ACUAUBU
      CFZGFZHIZCJFZKIZBVBGFZHIZBJFZKIZJFZKIVBLMVBNVKLMZVKVBLMZUDAVLVMAVKVBAVFVJ
      ACEOZABDOZPZVBTQAUEUFZAVKNVJVFJFZVBLAVFVJAVFVNRAVJVORUGAVRVJVBAVJVFVOVNPV
      OVQAUHVFLMVRVJLMAVEAVDCAVDAVCTQVDTQACVBEVQUIVCUJSRACERUKULAVJVFVOVNUMUNAB
      TQVJVBLMDBUOSUPUQURAVKVFVBVPVNVQAUHVJLMVKVFLMAVIAVHBAVHAVGTQVHTQABVBDVQUI
      VGUJSRABDRUKULAVFVJVNVOUMUNACTQVFVBLMECUOSUPUSAVKVBVPVQUTVA $.
  $}

  ${
    $d A x $.  $d B x $.
    dnibndlem12.1 $e |- T = ( x e. RR |->
                            ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) ) $.
    dnibndlem12.2 $e |- ( ph -> A e. RR ) $.
    dnibndlem12.3 $e |- ( ph -> B e. RR ) $.
    dnibndlem12.4 $e |- ( ph ->
        ( ( |_ ` ( A + ( 1 / 2 ) ) ) + 2 ) <_ ( |_ ` ( B + ( 1 / 2 ) ) ) ) $.
    $( Lemma for ~ dnibnd .  (Contributed by Asger C. Ipsen, 4-Apr-2021.) $)
    dnibndlem12 $p |- ( ph -> ( abs ` ( ( T ` B ) - ( T ` A ) ) )
                              <_ ( abs ` ( B - A ) ) ) $=
      ( cfv cmin co cabs cle wbr c1 caddc cfl dnicld1 letrd cdiv resubcld recnd
      c2 abscld 1red rehalfcld dnibndlem11 clt halflt1 cr wcel wa wi halfre 1re
      pm3.2i ltle ax-mp a1i dnibndlem10 leabsd dnibndlem1 mpbird ) ADEJCEJKLMJD
      CKLZMJZNODPUDUALZQLRJDKLMJZCVGQLRJCKLMJZKLZMJZVFNOAVKPVFAVJAVJAVHVIADHSAC
      GSUBUCUEZAUFZAVEAVEADCHGUBZUCUEZAVKVGPVLAPVMUGVMACDGHUHVGPNOZAVGPUIOZVPUJ
      VGUKULZPUKULZUMVQVPUNVRVSUOUPUQVGPURUSUSUTTAPVEVFVMVNVOACDGHIVAAVEVNVBTTA
      BCDVFEFGHVCVD $.
  $}

  ${
    $d A x $.  $d B x $.
    dnibndlem13.1 $e |- T = ( x e. RR |->
                            ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) ) $.
    dnibndlem13.2 $e |- ( ph -> A e. RR ) $.
    dnibndlem13.3 $e |- ( ph -> B e. RR ) $.
    dnibndlem13.4 $e |- ( ph ->
         ( |_ ` ( A + ( 1 / 2 ) ) ) <_ ( |_ ` ( B + ( 1 / 2 ) ) ) ) $.
    $( Lemma for ~ dnibnd .  (Contributed by Asger C. Ipsen, 4-Apr-2021.) $)
    dnibndlem13 $p |- ( ph -> ( abs ` ( ( T ` B ) - ( T ` A ) ) )
                              <_ ( abs ` ( B - A ) ) ) $=
      ( c1 c2 co caddc cfv wbr cle wa cr wcel adantr cdiv cfl clt cmin ad2antrr
      cabs wceq simpr dnibndlem12 eqcomd dnibndlem9 wo cz halfre readdcld flcld
      wb a1i jca zltp1le syl mpbid reflcl peano2re zred leloed wi peano2zd 1cnd
      recnd addassd 1p1e2 oveq2d eqtrd breq1d biimpd orim1d mpjaodan dnibndlem2
      bitrd mpd ) ACJKUALZMLZUBNZDWBMLZUBNZUCOZDENCENUDLUFNDCUDLUFNPOZWDWFUGZAW
      GQZWDKMLZWFPOZWHWDJMLZWFUGZWJWLQBCDEFACRSZWGWLGUEADRSZWGWLHUEWJWLUHUIWJWN
      QZBCDEFAWOWGWNGUEAWPWGWNHUEWQWMWFWJWNUHUJUKWJWMWFUCOZWNULZWLWNULWJWMWFPOZ
      WSWJWGWTAWGUHWJWDUMSZWFUMSZQZWGWTUQAXCWGAXAXBAWCACWBGWBRSAUNURZUOZUPZAWEA
      DWBHXDUOUPZUSTWDWFUTVAVBWJWMWFAWMRSZWGAWDRSZXHAWCRSXIXEWCVCVAZWDVDVATAWFR
      SWGAWFXGVEZTVFVBWJWRWLWNAWRWLVGWGAWRWLAWRWMJMLZWFPOZWLAWMUMSZXBQWRXMUQAXN
      XBAWDXFVHXGUSWMWFUTVAAXLWKWFPAXLWDJJMLZMLWKAWDJJAWDXJVJAVIZXPVKAXOKWDMXOK
      UGAVLURVMVNVOVTVPTVQWAVRAWIQZBCDEFAWOWIGTAWPWIHTXQWDWFAWIUHUJVSAWDWFPOWGW
      IULIAWDWFXJXKVFVBVR $.
  $}

  ${
    $d A x $.  $d B x $.
    dnibnd.1 $e |- T = ( x e. RR |->
                            ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) ) $.
    dnibnd.2 $e |- ( ph -> A e. RR ) $.
    dnibnd.3 $e |- ( ph -> B e. RR ) $.
    $( The "distance to nearest integer" function is 1-Lipschitz continuous,
       i.e., is a short map.  (Contributed by Asger C. Ipsen, 4-Apr-2021.) $)
    dnibnd $p |- ( ph -> ( abs ` ( ( T ` B ) - ( T ` A ) ) )
                              <_ ( abs ` ( B - A ) ) ) $=
      ( co caddc cfl cfv cle wbr cmin cabs cr wcel adantr recnd c1 c2 cdiv wceq
      wa dnibndlem13 dnicld2 abssubd breqtrd eqbrtrd halfre a1i readdcld reflcl
      simpr syl letrid mpjaodan ) ACUAUBUCIZJIZKLZDUSJIZKLZMNZDELZCELZOIPLZDCOI
      PLZMNVCVAMNZAVDUEBCDEFACQRZVDGSADQRZVDHSAVDUOUFAVIUEZVGVFVEOIPLZVHMAVGVMU
      DVIAVEVFAVEABDEFHUGTAVFABCEFGUGTUHSVLVMCDOIPLZVHMVLBDCEFAVKVIHSAVJVIGSAVI
      UOUFAVNVHUDVIACDACGTADHTUHSUIUJAVAVCAUTQRVAQRACUSGUSQRAUKULZUMUTUNUPAVBQR
      VCQRADUSHVOUMVBUNUPUQUR $.
  $}

  ${
    $d T d e y z $.  $d x y z $.
    dnicn.1 $e |- T = ( x e. RR |->
                            ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) ) $.
    $( The "distance to nearest integer" function is continuous.  (Contributed
       by Asger C. Ipsen, 4-Apr-2021.) $)
    dnicn $p |- T e. ( RR -cn-> RR ) $=
      ( vz vy vd ve cr co wcel cv cmin cabs cfv clt wbr wi wral crp wa ccncf wf
      wrex dnif simpr simplr dnicld2 simplll resubcld recnd abscld rpred dnibnd
      ad2antrr lelttrd ex ralrimiva breq2 rspceaimv syl2anc rgen2 wss ax-resscn
      cc wb elcncf2 mp2an mpbir2an ) BHHUAIJZHHBUBZDKZEKZLIZMNZFKZOPZVKBNZVLBNZ
      LIZMNZGKZOPZQDHRFSUCZGSREHRZABCUDWCEGHSVLHJZWASJZTZWFVNWAOPZWBQZDHRWCWEWF
      UEZWGWIDHWGVKHJZTZWHWBWLWHTZVTVNWAWMVSWMVSWMVQVRWMAVKBCWGWKWHUFZUGWMAVLBC
      WEWFWKWHUHZUGUIUJUKWMVMWMVMWMVKVLWNWOUIUJUKWMWAWGWFWKWHWJUNULWMAVLVKBCWOW
      NUMWLWHUEUOUPUQVPWHWBFDWASHVOWAVNOURUSUTVAHVDVBZWPVIVJWDTVEVCVCEGFDHHBVFV
      GVH $.
  $}

  ${
    $d A n y $.  $d C n y $.  $d M n $.  $d N n y $.  $d T n y $.  $d ph y n $.
    knoppcnlem1.f $e |- F = ( y e. RR |-> ( n e. NN0 |->
            ( ( C ^ n ) x. ( T ` ( ( ( 2 x. N ) ^ n ) x. y ) ) ) ) ) $.
    knoppcnlem1.2 $e |- ( ph -> A e. RR ) $.
    knoppcnlem1.3 $e |- ( ph -> M e. NN0 ) $.
    $( Lemma for ~ knoppcn .  (Contributed by Asger C. Ipsen, 4-Apr-2021.) $)
    knoppcnlem1 $p |- ( ph -> ( ( F ` A ) ` M ) =
            ( ( C ^ M ) x. ( T ` ( ( ( 2 x. N ) ^ M ) x. A ) ) ) ) $=
      ( cexp co cmul cfv cn0 cvv wceq oveq2 cv cmpt fveq2d oveq2d mpteq2dv wcel
      c2 cr nn0ex mptex a1i fvmptd3 fvoveq1d oveq12d adantl ovexd fvmptd ) AFHD
      FUAZMNZUGIONZURMNZCONZEPZONZDHMNZUTHMNZCONEPZONZQCGPRABCFQUSVABUAZONZEPZO
      NZUBFQVDUBZUHGRJVICSZFQVLVDVNVKVCUSOVNVJVBEVICVAOTUCUDUEKVMRUFAFQVDUIUJUK
      ULURHSZVDVHSAVOUSVEVCVGOURHDMTVOVAVFCEOURHUTMTUMUNUOLAVEVGOUPUQ $.
  $}

  ${
    $d A x $.  $d M x $.  $d N x $.
    knoppcnlem2.t $e |- T = ( x e. RR |->
                            ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) ) $.
    knoppcnlem2.n $e |- ( ph -> N e. NN ) $.
    knoppcnlem2.1 $e |- ( ph -> C e. RR ) $.
    knoppcnlem2.2 $e |- ( ph -> A e. RR ) $.
    knoppcnlem2.3 $e |- ( ph -> M e. NN0 ) $.
    $( Lemma for ~ knoppcn .  (Contributed by Asger C. Ipsen, 4-Apr-2021.)
       (Revised by Asger C. Ipsen, 5-Jul-2021.) $)
    knoppcnlem2 $p |- ( ph ->
        ( ( C ^ M ) x. ( T ` ( ( ( 2 x. N ) ^ M ) x. A ) ) ) e. RR ) $=
      ( cexp co c2 cmul reexpcld cr wcel remulcld cfv 2re a1i nnre syl dnicld2
      cn ) ADFMNOGPNZFMNZCPNZEUAADFJLQABUJEHAUICAUHFAOGORSAUBUCAGUGSGRSIGUDUETL
      QKTUFT $.
  $}

  ${
    $d A n y $.  $d A x $.  $d C n y $.  $d M n $.  $d M x $.  $d N n y $.
    $d N x $.  $d T n y $.  $d ph n y $.
    knoppcnlem3.t $e |- T = ( x e. RR |->
                            ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) ) $.
    knoppcnlem3.f $e |- F = ( y e. RR |-> ( n e. NN0 |->
            ( ( C ^ n ) x. ( T ` ( ( ( 2 x. N ) ^ n ) x. y ) ) ) ) ) $.
    knoppcnlem3.n $e |- ( ph -> N e. NN ) $.
    knoppcnlem3.1 $e |- ( ph -> C e. RR ) $.
    knoppcnlem3.2 $e |- ( ph -> A e. RR ) $.
    knoppcnlem3.3 $e |- ( ph -> M e. NN0 ) $.
    $( Lemma for ~ knoppcn .  (Contributed by Asger C. Ipsen, 4-Apr-2021.)
       (Revised by Asger C. Ipsen, 5-Jul-2021.) $)
    knoppcnlem3 $p |- ( ph -> ( ( F ` A ) ` M ) e. RR ) $=
      ( cfv cexp co cmul c2 cr knoppcnlem1 knoppcnlem2 eqeltrd ) AIDHQQEIRSUAJT
      SIRSDTSFQTSUBACDEFGHIJLOPUCABDEFIJKMNOPUDUE $.
  $}

  ${
    $d A n y $.  $d A x $.  $d C m $.  $d C n y $.  $d M m $.  $d M n $.
    $d M x $.  $d N n y $.  $d N x $.  $d T n y $.  $d ph m $.  $d ph n y $.
    knoppcnlem4.t $e |- T = ( x e. RR |->
                            ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) ) $.
    knoppcnlem4.f $e |- F = ( y e. RR |-> ( n e. NN0 |->
            ( ( C ^ n ) x. ( T ` ( ( ( 2 x. N ) ^ n ) x. y ) ) ) ) ) $.
    knoppcnlem4.n $e |- ( ph -> N e. NN ) $.
    knoppcnlem4.1 $e |- ( ph -> C e. RR ) $.
    knoppcnlem4.2 $e |- ( ph -> A e. RR ) $.
    knoppcnlem4.3 $e |- ( ph -> M e. NN0 ) $.
    $( Lemma for ~ knoppcn .  (Contributed by Asger C. Ipsen, 4-Apr-2021.)
       (Revised by Asger C. Ipsen, 5-Jul-2021.) $)
    knoppcnlem4 $p |- ( ph ->
        ( abs ` ( ( F ` A ) ` M ) ) <_
        ( ( m e. NN0 |-> ( ( abs ` C ) ^ m ) ) ` M ) ) $=
      ( cfv cabs co cexp c2 cmul cn0 cv cmpt knoppcnlem1 fveq2d recnd expcld cr
      cle wcel 2re a1i cn nnre remulcld reexpcld dnicld2 absmuld absexpd oveq1d
      syl eqtrd c1 abscld 1red absge0d expge0d cdiv cfl cmin wceq dnival halfre
      caddc cc readdcld reflcl resubcld absidm eqeltrrd wbr rddif halflt1 ltlei
      clt 1re ax-mp letrd eqbrtrd lemul2ad ax-1rid breqtrd adantl fvmptd eqcomd
      eqidd oveq2 ) AJDIRRZSREJUATZUBKUCTZJUATZDUCTZFRZUCTZSRZJGUDESRZGUEZUATZU
      FZRZULAXAXGSACDEFHIJKMPQUGUHAXHXIJUATZXMULAXHXNXFSRZUCTZXNULAXHXBSRZXOUCT
      XPAXBXFAEJAEOUIZQUJAXFABXEFLAXDDAXCJAUBKUBUKUMAUNUOAKUPUMKUKUMNKUQVDURQUS
      PURZUTZUIZVAAXQXNXOUCAEJXRQVBVCVEAXPXNVFUCTZXNULAXOVFXNAXFYAVGAVHZAXIJAEX
      RVGZQUSZAXIJYDQAEXRVIVJAXOXEVFUBVKTZVQTZVLRZXEVMTZSRZVFULAXOYJSRZYJAXFYJS
      AXEUKUMZXFYJVNXSBXEFLVOVDZUHAYIVRUMYKYJVNAYIAYHXEAYGUKUMYHUKUMAXEYFXSYFUK
      UMAVPUOZVSYGVTVDXSWAUIYIWBVDVEAYJYFVFAXFYJUKYMXTWCYNYCAYLYJYFULWDXSXEWEVD
      YFVFULWDZAYFVFWHWDYOWFYFVFVPWIWGWJUOWKWLWMAXNUKUMYBXNVNYEXNWNVDWOWLAXMXNA
      GJXKXNUDXLUKAXLWSXJJVNXKXNVNAXJJXIUAWTWPQYEWQWRWOWL $.
  $}

  ${
    $d C n y $.  $d N n y $.  $d N x $.  $d T n y $.  $d ph m n y z $.
    $d m x z $.
    knoppcnlem5.t $e |- T = ( x e. RR |->
                            ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) ) $.
    knoppcnlem5.f $e |- F = ( y e. RR |-> ( n e. NN0 |->
            ( ( C ^ n ) x. ( T ` ( ( ( 2 x. N ) ^ n ) x. y ) ) ) ) ) $.
    knoppcnlem5.n $e |- ( ph -> N e. NN ) $.
    knoppcnlem5.1 $e |- ( ph -> C e. RR ) $.
    $( Lemma for ~ knoppcn .  (Contributed by Asger C. Ipsen, 4-Apr-2021.)
       (Revised by Asger C. Ipsen, 5-Jul-2021.) $)
    knoppcnlem5 $p |- ( ph ->
        ( m e. NN0 |-> ( z e. RR |-> ( ( F ` z ) ` m ) ) )
                         : NN0 --> ( CC ^m RR ) ) $=
      ( cn0 cr cc wcel wa cvv cv cfv cmpt cmap co wf ad2antrr simpr knoppcnlem3
      cn simplr recnd fmpttd wb cnex reex pm3.2i elmapg ax-mp sylibr ) AGODPGUA
      ZDUAZIUBUBZUCZQPUDUEZAVAORZSZPQVDUFZVDVERZVGDPVCQVGVBPRZSZVCVKBCVBEFHIVAJ
      KLAJUJRVFVJMUGAEPRVFVJNUGVGVJUHAVFVJUKUIULUMQTRZPTRZSVIVHUNVLVMUOUPUQQPVD
      TTURUSUTUM $.
  $}

  ${
    $d C k m n w y $.  $d F k m w z $.  $d N n y $.  $d N x $.  $d T n y $.
    $d ph k m n w y z $.  $d k m w x z $.
    knoppcnlem6.t $e |- T = ( x e. RR |->
                            ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) ) $.
    knoppcnlem6.f $e |- F = ( y e. RR |-> ( n e. NN0 |->
            ( ( C ^ n ) x. ( T ` ( ( ( 2 x. N ) ^ n ) x. y ) ) ) ) ) $.
    knoppcnlem6.n $e |- ( ph -> N e. NN ) $.
    knoppcnlem6.1 $e |- ( ph -> C e. RR ) $.
    knoppcnlem6.2 $e |- ( ph -> ( abs ` C ) < 1 ) $.
    $( Lemma for ~ knoppcn .  (Contributed by Asger C. Ipsen, 4-Apr-2021.)
       (Revised by Asger C. Ipsen, 5-Jul-2021.) $)
    knoppcnlem6 $p |- ( ph ->
        seq 0 ( oF + , ( m e. NN0 |-> ( z e. RR |-> ( ( F ` z ) ` m ) ) ) )
        e. dom ( ~~>u ` RR ) ) $=
      ( cr cn0 cfv cvv wcel vw vk cv cmpt cabs cexp co cc0 0zd reex knoppcnlem5
      nn0uz a1i nn0ex mptex wa wceq eqid simpr oveq2d ovexd fvmptd recnd abscld
      adantr reexpcld eqeltrd fveq2d mpteq2dv adantrr fveq1d simprr knoppcnlem4
      cle fvexd cn eqbrtrd caddc cseq c1 cmin cdiv cli wbr cdm cc absidm geolim
      clt syl seqex ovex breldm mtest ) AUAPUBGQDPGUCZDUCZIRZRZUDZUDZGQEUERZWOU
      FUGZUDZUHSSQULAUIPSTAUJUMABCDEFGHIJKLMNUKXCSTAGQXBUNUOUMAUBUCZQTZUPZXDXCR
      ZXAXDUFUGZPXFGXDXBXHQXCSXCXCUQXFXCURUMXFWOXDUQZUPWOXDXAUFXFXIUSUTAXEUSZXF
      XAXDUFVAVBZXFXAXDAXAPTXEAEAENVCZVDZVEXJVFVGAXEUAUCZPTZUPZUPZXNXDWTRZRZUER
      XDXNIRZRZUERXGVNXQXSYAUEXQDXNXDWQRZYAPXRSXQGXDWSDPYBUDZQWTSWTWTUQXQWTURUM
      XQXIUPZDPWRYBYDWOXDWQXQXIUSVHVIAXEXEXOXJVJZYCSTXQDPYBUJUOUMVBXQWPXNUQZUPZ
      XDWQXTYGWPXNIXQYFUSVHVKAXEXOVLZXQXDXTVOVBVHXQBCXNEFGHIXDJKLAJVPTXPMVEAEPT
      XPNVEYHYEVMVQAVRXCUHVSZVTVTXAWAUGZWBUGZWCWDYIWCWETAXAUBXCAXAXMVCAXAUERZXA
      VTWIAEWFTYLXAUQXLEWGWJOVQXKWHYIYKWCVRXCUHWKVTYJWBWLWMWJWN $.
  $}

  ${
    $d F k m w z $.  $d M k m w $.  $d ph k m w $.
    knoppcnlem7.t $e |- T = ( x e. RR |->
                            ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) ) $.
    knoppcnlem7.f $e |- F = ( y e. RR |-> ( n e. NN0 |->
            ( ( C ^ n ) x. ( T ` ( ( ( 2 x. N ) ^ n ) x. y ) ) ) ) ) $.
    knoppcnlem7.n $e |- ( ph -> N e. NN ) $.
    knoppcnlem7.1 $e |- ( ph -> C e. RR ) $.
    knoppcnlem7.2 $e |- ( ph -> M e. NN0 ) $.
    $( Lemma for ~ knoppcn .  (Contributed by Asger C. Ipsen, 4-Apr-2021.)
       (Revised by Asger C. Ipsen, 5-Jul-2021.) $)
    knoppcnlem7 $p |- ( ph ->
        ( seq 0
            ( oF + , ( m e. NN0 |-> ( z e. RR |-> ( ( F ` z ) ` m ) ) ) )
        ` M )
        = ( w e. RR |-> ( seq 0 ( + , ( F ` w ) ) ` M ) ) ) $=
      ( cr cfv wcel vk caddc cn0 cv cmpt cc0 cvv reex a1i cuz elnn0uz sylib cfz
      co wa wceq eqid fveq2 fveq1d cbvmptv mpteq2dv adantl eqtrd elfznn0 fvmptd
      mptex seqof ) AUAERUBHUCDRHUDZDUDZJSZSZUEZUEZEUDZJSZUFKUGRUGTAUHUIAKUCTKU
      FUJSTQKUKULAUAUDZUFKUMUNTZUOZHVPVLERVPVOSZUEZUCVMUGVMVMUPVRVMUQUIVRVHVPUP
      ZUOZVLERVHVOSZUEZVTVLWDUPWBDERVKWCVIVNUPVHVJVOVIVNJURUSUTUIWAWDVTUPVRWAER
      WCVSVHVPVOURVAVBVCVQVPUCTAVPKVDVBVTUGTVRERVSUHVFUIVEVG $.
  $}

  ${
    $d C n y $.  $d F a b k w $.  $d F k m w z $.  $d N n y $.  $d N x $.
    $d T n y $.  $d ph a k n w y $.  $d a w x $.  $d ph b k w $.  $d ph m w $.
    knoppcnlem8.t $e |- T = ( x e. RR |->
                            ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) ) $.
    knoppcnlem8.f $e |- F = ( y e. RR |-> ( n e. NN0 |->
            ( ( C ^ n ) x. ( T ` ( ( ( 2 x. N ) ^ n ) x. y ) ) ) ) ) $.
    knoppcnlem8.n $e |- ( ph -> N e. NN ) $.
    knoppcnlem8.1 $e |- ( ph -> C e. RR ) $.
    $( Lemma for ~ knoppcn .  (Contributed by Asger C. Ipsen, 4-Apr-2021.)
       (Revised by Asger C. Ipsen, 5-Jul-2021.) $)
    knoppcnlem8 $p |- ( ph ->
        seq 0 ( oF + , ( m e. NN0 |-> ( z e. RR |-> ( ( F ` z ) ` m ) ) ) )
                : NN0 --> ( CC ^m RR ) ) $=
      ( cn0 cc cr cfv cc0 wcel vk vw va vb cmap co cv caddc cof cmpt cseq wf wa
      cn adantr simpr knoppcnlem7 cuz simplr nn0uz eleqtrdi cfz ad2antrr adantl
      elfznn0 knoppcnlem3 recnd addcl seqcl fmpttd cvv cnex pm3.2i elmapg ax-mp
      wb reex sylibr eqeltrd wfn wceq cz 0z seqfn fneq2i mpbir dffn5 mpbi feq1i
      ) AOPQUEUFZUAOUAUGZUHUIZGODQGUGDUGIRRUJUJZSUKZRZUJZULOWJWNULAUAOWOWJAWKOT
      ZUMZWOUBQWKUHUBUGZIRZSUKRZUJZWJWRBCDUBEFGHIWKJKLAJUNTZWQMUOZAEQTZWQNUOZAW
      QUPUQWRQPXBULZXBWJTZWRUBQXAPWRWSQTZUMZUCUDUHPWTSWKXJWKOSURRZAWQXIUSUTVAXJ
      UCUGZSWKVBUFTZUMZXLWTRXNBCWSEFHIXLJKLWRXCXIXMXDVCWRXEXIXMXFVCWRXIXMUSXMXL
      OTXJXLWKVEVDVFVGXLPTUDUGZPTUMXLXOUHUFPTXJXLXOVHVDVIVJPVKTZQVKTZUMXHXGVPXP
      XQVLVQVMPQXBVKVKVNVOVRVSVJOWJWNWPWNOVTZWNWPWAXRWNXKVTZSWBTXSWCWLWMSWDVOOX
      KWNUTWEWFUAOWNWGWHWIVR $.
  $}

  ${
    $d C m n y $.  $d F f i m w z $.  $d F f k m v w z $.  $d N n y $.
    $d N x $.  $d T n y $.  $d W f $.  $d ph f i m w z $.  $d ph i m n w y z $.
    $d i m w x z $.  $d ph k m v w z $.
    knoppcnlem9.t $e |- T = ( x e. RR |->
                            ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) ) $.
    knoppcnlem9.f $e |- F = ( y e. RR |-> ( n e. NN0 |->
            ( ( C ^ n ) x. ( T ` ( ( ( 2 x. N ) ^ n ) x. y ) ) ) ) ) $.
    knoppcnlem9.w $e |- W = ( w e. RR |-> sum_ i e. NN0 ( ( F ` w ) ` i ) ) $.
    knoppcnlem9.n $e |- ( ph -> N e. NN ) $.
    knoppcnlem9.1 $e |- ( ph -> C e. RR ) $.
    knoppcnlem9.2 $e |- ( ph -> ( abs ` C ) < 1 ) $.
    $( Lemma for ~ knoppcn .  (Contributed by Asger C. Ipsen, 4-Apr-2021.)
       (Revised by Asger C. Ipsen, 5-Jul-2021.) $)
    knoppcnlem9 $p |- ( ph ->
        seq 0 ( oF + , ( m e. NN0 |-> ( z e. RR |-> ( ( F ` z ) ` m ) ) ) )
        ( ~~>u ` RR ) W ) $=
      ( cr vf vk vv caddc cof cn0 cv cfv cmpt cc0 cseq culm wbr wex knoppcnlem6
      cdm wcel seqex eldm sylib wa simpr csu wceq cc ulmcl feqmptd adantl nn0uz
      0zd eqidd ad2antrr simplr knoppcnlem3 adantllr recnd cvv cmap knoppcnlem8
      cn co wf knoppcnlem7 fveq1d eqid fveq2 seqeq3d adantr fvexd fvmptd3 eqtrd
      a1i ulmclm isumclim eqcomd mpteq2dva 3eqtrd breqtrd ex exlimdv mpd ) AUDU
      EZIUFDTIUGDUGKUHUHUIUIZUJUKZUAUGZTULUHZUMZUAUNZXDMXFUMZAXDXFUPUQXHABCDFGI
      JKLNOQRSUOUAXDXFXBXCUJURUSUTAXGXIUAAXGXIAXGVAZXDXEMXFAXGVBXJXEETEUGZXEUHZ
      UIZETUFHUGZXKKUHZUHZHVCZUIZMXGXEXMVDAXGETVEXETXDXEVFVGVHXJETXLXQXJXKTUQZV
      AZXQXLXTXPXLHXOUJUFVIXTVJZXTXNUFUQZVAZXPVKYCXPAXSYBXPTUQXGAXSVAZYBVABCXKF
      GJKXNLNOALVTUQZXSYBQVLAFTUQZXSYBRVLAXSYBVMYDYBVBVNVOVPXTXKTUBXDXEUDXOUJUK
      ZUJVQUFVIYAAUFVETVRWAXDWBXGXSABCDFGIJKLNOQRVSVLXJXSVBZYGVQUQXTUDXOUJURWLX
      TUBUGZUFUQZVAZXKYIXDUHZUHXKUCTYIUDUCUGZKUHZUJUKZUHZUIZUHYIYGUHZYKXKYLYQAX
      SYJYLYQVDXGYDYJVABCDUCFGIJKYILNOAYEXSYJQVLAYFXSYJRVLYDYJVBWCVOWDYKUCXKYPY
      RTYQVQYQWEYMXKVDZYIYOYGYSYNXOUDUJYMXKKWFWGWDXTXSYJYHWHYKYIYGWIWJWKAXGXSVM
      WMWNWOWPXJMXRMXRVDXJPWLWOWQWRWSWTXA $.
  $}

  ${
    $d C n y z u v $.  $d M n z u v $.  $d N n y z u v $.  $d T n y z u v $.
    $d ph n y z $.
    knoppcnlem10.t $e |- T = ( x e. RR |->
                            ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) ) $.
    knoppcnlem10.f $e |- F = ( y e. RR |-> ( n e. NN0 |->
            ( ( C ^ n ) x. ( T ` ( ( ( 2 x. N ) ^ n ) x. y ) ) ) ) ) $.
    knoppcnlem10.n $e |- ( ph -> N e. NN ) $.
    knoppcnlem10.1 $e |- ( ph -> C e. RR ) $.
    knoppcnlem10.2 $e |- ( ph -> M e. NN0 ) $.
    $( Lemma for ~ knoppcn .  (Contributed by Asger C. Ipsen, 4-Apr-2021.)
       (Revised by Asger C. Ipsen, 5-Jul-2021.)  Avoid ~ ax-mulf .  (Revised by
       GG, 19-Apr-2025.) $)
    knoppcnlem10 $p |- ( ph -> ( z e. RR |-> ( ( F ` z ) ` M ) )
      e. ( ( topGen ` ran (,) ) Cn ( TopOpen ` CCfld ) ) ) $=
      ( cr cfv co wcel cc vu vv cv cmpt cexp cmul cioo crn ctg ccnfld ctopn ccn
      c2 wa cn0 adantr knoppcnlem1 mpteq2dva ctopon retopon a1i eqid cnfldtopon
      simpr recnd expcld cnmptc crest 2cnd mulcld tgioo4 ctop cnfldtop cnrest2r
      nncnd oveq2i wss ax-mp eqsstri cnmptid sselid ctx mpomulcn oveq12 cnmpt12
      cmpo wb 2re nnred remulcld reexpcld fmpttd frnd ax-resscn cnrest2 mp3an2i
      mpbid eleqtrrdi ccncf ssid cncfss mp2an dnicn toponrestid cncfcn eleqtrdi
      wceq cnmpt11f eqeltrd ) ADPIDUCZHQQZUDDPEIUERZUMJUFRZIUERZXJUFRZFQZUFRZUD
      UGUHUIQZUJUKQZULRZADPXKXQAXJPSZUNZCXJEFGHIJLAYAVDZAIUOSYAOUPUQURADUAUBXLX
      PUAUCZUBUCZUFRZXQXRXSXSXSPTTXRPUSQSAUTVAZADXLXRXSPTYGXSTUSQSZAXSXSVBZVCZV
      AZAEIAENVEOVFVGADXOFXRXRXSPYGADPXOUDZXRXSPVHRZULRZXRXRULRZAYLXTSZYLYNSZAD
      UAUBXNXJYFXOXRXSXSXSPTTYGADXNXRXSPTYGYKAXMIAUMJAVIAJMVOVJOVFVGAYOXTDPXJUD
      YOYNXTXRYMXRULVKVPZXSVLSYNXTVQXSYIVMPXRXSVNVRVSADXRPYGVTWAYKYKUAUBTTYFWFX
      SXSWBRXSULRSAUAUBXSYIWCVAZYDXNYEXJUFWDWEYHAYLUHPVQPTVQZYPYQWGYJAPPYLADPXO
      PYBXNXJAXNPSYAAXMIAUMJUMPSAWHVAAJMWIWJOWKUPYCWJWLWMYTAWNVAPYLXRXSTWOWPWQY
      RWRAFPTWSRZXTAPPWSRZUUAFYTTTVQZUUBUUAVQWNTWTZPPTXAXBFUUBSABFKXCVAWAYTUUCU
      UAXTXGWNUUDPTXSXRXSYIVKXSTYJXDXEXBXFXHYKYKYSYDXLYEXPUFWDWEXI $.
    $( $j usage 'knoppcnlem10' avoids 'ax-mulf'; $)
  $}

  ${
    $d C n w y $.  $d F k l w $.  $d F k m w z $.  $d N n w y $.  $d N w x $.
    $d T n w y $.  $d ph k l n w y $.  $d l w x $.  $d ph m w $.
    knoppcnlem11.t $e |- T = ( x e. RR |->
                            ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) ) $.
    knoppcnlem11.f $e |- F = ( y e. RR |-> ( n e. NN0 |->
            ( ( C ^ n ) x. ( T ` ( ( ( 2 x. N ) ^ n ) x. y ) ) ) ) ) $.
    knoppcnlem11.n $e |- ( ph -> N e. NN ) $.
    knoppcnlem11.1 $e |- ( ph -> C e. RR ) $.
    $( Lemma for ~ knoppcn .  (Contributed by Asger C. Ipsen, 4-Apr-2021.)
       (Revised by Asger C. Ipsen, 5-Jul-2021.) $)
    knoppcnlem11 $p |- ( ph ->
        seq 0 ( oF + , ( m e. NN0 |-> ( z e. RR |-> ( ( F ` z ) ` m ) ) ) )
                : NN0 --> ( RR -cn-> CC ) ) $=
      ( vw cn0 cr cfv cc0 wcel vk vl cc ccncf co cv caddc cof cmpt cseq cfz csu
      wf wa cn adantr simpr knoppcnlem7 eqidd cuz simplr elnn0uz sylib ad2antrr
      elfzuz nn0uz eleqtrrdi adantl knoppcnlem3 recnd fsumser eqcomd eqtrd cioo
      mpteq2dva crn ctg ccnfld ctopn ccn eqid ctopon retopon fzfid knoppcnlem10
      a1i fsumcn wss wceq ax-resscn pm3.2i tgioo4 cnfldtopon toponrestid cncfcn
      ssid ax-mp eqeltrd fmpttd wfn cz 0z seqfn fneq2i mpbir dffn5 feq1i sylibr
      mpbi ) APQUCUDUEZUAPUAUFZUGUHZGPDQGUFDUFIRRUIUIZSUJZRZUIZUMPXJXNUMAUAPXOX
      JAXKPTZUNZXOOQSXKUKUEZUBUFZOUFZIRZRZUBULZUIZXJXRXOOQXKUGYBSUJRZUIYEXRBCDO
      EFGHIXKJKLAJUOTZXQMUPZAEQTZXQNUPZAXQUQURXROQYFYDXRYAQTZUNZYDYFYLYCUBYBSXK
      YLXTXSTZUNZYCUSYLXQXKSUTRZTAXQYKVAXKVBVCYNYCYNBCYAEFHIXTJKLXRYGYKYMYHVDXR
      YIYKYMYJVDXRYKYMVAYMXTPTZYLYMXTYOPXTSXKVEVFVGZVHVIVJVKVLVOVMXRYEVNVPVQRZV
      RVSRZVTUEZXJXROXSYCUBYRYSQYSWAZYRQWBRTXRWCWFXRSXKWDXRYMUNBCOEFHIXTJKLXRYG
      YMYHUPXRYIYMYJUPYMYPXRYQVHWEWGQUCWHZUCUCWHZUNXJYTWIUUBUUCWJUCWPWKQUCYSYRY
      SUUAWLYSUCYSUUAWMWNWOWQVGWRWSPXJXNXPXNPWTZXNXPWIUUDXNYOWTZSXATUUEXBXLXMSX
      CWQPYOXNVFXDXEUAPXNXFXIXGXH $.
  $}

  ${
    $d C m n y $.  $d F i m w z $.  $d N n y $.  $d N x $.  $d T n y $.
    $d ph i m n w y z $.  $d i m w x z $.
    knoppcn.t $e |- T = ( x e. RR |->
                            ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) ) $.
    knoppcn.f $e |- F = ( y e. RR |-> ( n e. NN0 |->
            ( ( C ^ n ) x. ( T ` ( ( ( 2 x. N ) ^ n ) x. y ) ) ) ) ) $.
    knoppcn.w $e |- W = ( w e. RR |-> sum_ i e. NN0 ( ( F ` w ) ` i ) ) $.
    knoppcn.n $e |- ( ph -> N e. NN ) $.
    knoppcn.1 $e |- ( ph -> C e. RR ) $.
    knoppcn.2 $e |- ( ph -> ( abs ` C ) < 1 ) $.
    $( The continuous nowhere differentiable function ` W ` ( Knopp, K. (1918).
       Math.  Z. 2, 1-26 ) is, in fact, continuous.  (Contributed by Asger C.
       Ipsen, 4-Apr-2021.)  (Revised by Asger C. Ipsen, 5-Jul-2021.) $)
    knoppcn $p |- ( ph -> W e. ( RR -cn-> CC ) ) $=
      ( vm vz cr caddc cof cn0 cfv cmpt cc0 cseq nn0uz knoppcnlem11 knoppcnlem9
      cv 0zd ulmcn ) ATUAUBRUCSTRUKSUKIUDUDUEUEUFUGKUFUCUHAULABCSEFRHIJLMOPUIAB
      CSDEFGRHIJKLMNOPQUJUM $.
  $}

  ${
    $d C n y $.  $d F i w $.  $d N n y $.  $d N x $.  $d T n y $.
    $d ph i n w y $.  $d i w x $.
    knoppcld.t $e |- T = ( x e. RR |->
                            ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) ) $.
    knoppcld.f $e |- F = ( y e. RR |-> ( n e. NN0 |->
            ( ( C ^ n ) x. ( T ` ( ( ( 2 x. N ) ^ n ) x. y ) ) ) ) ) $.
    knoppcld.w $e |- W = ( w e. RR |-> sum_ i e. NN0 ( ( F ` w ) ` i ) ) $.
    knoppcld.a $e |- ( ph -> A e. RR ) $.
    knoppcld.n $e |- ( ph -> N e. NN ) $.
    knoppcld.1 $e |- ( ph -> C e. RR ) $.
    knoppcld.2 $e |- ( ph -> ( abs ` C ) < 1 ) $.
    $( Closure theorem for Knopp's function.  (Contributed by Asger C. Ipsen,
       26-Jul-2021.) $)
    knoppcld $p |- ( ph -> ( W ` A ) e. CC ) $=
      ( cr cc ccncf co wcel wf knoppcn cncff syl ffvelcdmd ) ATUAELALTUAUBUCUDT
      UALUEABCDFGHIJKLMNOQRSUFTUALUGUHPUI $.
  $}

  ${
    $d A b d x $.  $d A d x y $.  $d F b d x $.  $d F d x y $.  $d S b d x $.
    $d S d x y $.  $d ph b c d x $.  $d ph c d x y $.
    unblimceq0lem.0 $e |- ( ph -> S C_ CC ) $.
    unblimceq0lem.1 $e |- ( ph -> F : S --> CC ) $.
    unblimceq0lem.2 $e |- ( ph -> A e. CC ) $.
    unblimceq0lem.3 $e |- ( ph -> A. b e. RR+ A. d e. RR+ E. x e. S
      ( ( abs ` ( x - A ) ) < d /\ b <_ ( abs ` ( F ` x ) ) ) ) $.
    $( Lemma for ~ unblimceq0 .  (Contributed by Asger C. Ipsen,
       12-May-2021.) $)
    unblimceq0lem $p |- ( ph -> A. c e. RR+ A. d e. RR+ E. y e. S
      ( y =/= A /\ ( abs ` ( y - A ) ) < d /\ c <_ ( abs ` ( F ` y ) ) ) ) $=
      ( cabs wbr cle crp wcel wa adantr cv wne cmin cfv clt w3a wrex caddc wral
      co cif breq1 anbi2d rexbidv ralbidv cc wf ad2antrr simpr ffvelcdmd abscld
      wceq cr simprl rpred readdcld absge0d cc0 rpgt0d addgegt0d simplrl ifclda
      elrpd wn rspcdva simprr rsp sylc wb neeq1 fvoveq1 breq1d 2fveq3 3anbi123d
      breq2d adantl adantlr iftrued eqcomd simprrr eqbrtrd lensymd wi ltaddposd
      mpbid ex necon3bd simprrl addge02d letrd 3jca eqeltrrd iffalsed pm2.61dan
      mpd rspcedvd rexlimddv ralrimivva ) ACUAZDUBZXIDUCUJNUDZIUAZUEOZHUAZXIFUD
      NUDZPOZUFZCEUGZHIQQAXNQRZXLQRZSZSZBUAZDUCUJNUDZXLUEOZDERZDFUDZNUDZXNUHUJZ
      XNUKZYCFUDZNUDZPOZSZXRBEYBYNBEUGZIQUIZXTYOYBYEGUAZYLPOZSZBEUGZIQUIZYPGQYJ
      YQYJVBZYTYOIQUUBYSYNBEUUBYRYMYEYQYJYLPULUMUNUOAUUAGQUIYAMTYBYFYIXNQYBYFSZ
      YIUUCYHXNUUCYGUUCEUPDFAEUPFUQZYAYFKURYBYFUSUTZVAZYBXNVCRZYFYBXNAXSXTVDZVE
      TZVFZUUCYHXNUUFUUIUUCYGUUEVGYBVHXNUEOZYFYBXNUUHVITZVJVMAXSXTYFVNZVKVLVOAX
      SXTVPYOIQVQVRYBYCERZYNSZSZXQYCDUBZYEXNYLPOZUFZCYCEYBUUNYNVDZXIYCVBZXQUUSV
      SUUPUVAXJUUQXMYEXPUURXIYCDVTUVAXKYDXLUEXIYCDNUCWAWBUVAXOYLXNPXIYCNFWCWEWD
      WFUUPYFUUSUUPYFSZUUQYEUURUVBYLYIUEOZVNUUQUVBYIYLYBYFYIVCRUUOUUJWGZUUPYLVC
      RYFUUPYKUUPEUPYCFAUUDYAUUOKURUUTUTVATZUVBYIYJYLPUVBYJYIUVBYFYIXNUUPYFUSWH
      WIUUPYMYFYBUUNYEYMWJZTWKZWLUVBUVCYCDYBYFYCDVBZUVCWMUUOUUCUVHUVCUUCUVHSYLY
      HYIUEUVHYLYHVBUUCYCDNFWCWFUUCYHYIUEOZUVHUUCUUKUVIUULUUCXNYHUUIUUFWNWOTWKW
      PWGWQXEUUPYEYFYBUUNYEYMWRZTUVBXNYIYLYBYFUUGUUOUUIWGZUVDUVEUVBVHYHPOXNYIPO
      UVBYGYBYFYGUPRUUOUUEWGVGUVBXNYHUVKYBYFYHVCRUUOUUFWGWSWOUVGWTXAUUPUUMSZUUQ
      YEUURUVLUUMUUQUUPUUMUSZUVLYFYCDUVLUVHYFUVLUVHSYCDEUVLUVHUSUVLUUNUVHUUPUUN
      UUMUUTTTXBWPWQXEUUPYEUUMUVJTUVLXNYJYLPUVLYJXNUVLYFYIXNUVMXCWIUUPYMUUMUVFT
      WKXAXDXFXGXH $.
  $}

  ${
    $d A a b d x $.  $d A a c d y z $.  $d A c e y z $.  $d F a b d x $.
    $d F a c d y z $.  $d F c e y z $.  $d S a b d x $.  $d S a c d z $.
    $d S c e z $.  $d ph a b d x $.  $d ph c d y z $.  $d ph e y z $.
    $d x z $.
    unblimceq0.0 $e |- ( ph -> S C_ CC ) $.
    unblimceq0.1 $e |- ( ph -> F : S --> CC ) $.
    unblimceq0.2 $e |- ( ph -> A e. CC ) $.
    unblimceq0.3 $e |- ( ph -> A. b e. RR+ A. d e. RR+ E. x e. S
      ( ( abs ` ( x - A ) ) < d /\ b <_ ( abs ` ( F ` x ) ) ) ) $.
    $( If ` F ` is unbounded near ` A ` it has no limit at ` A ` .
       (Contributed by Asger C. Ipsen, 12-May-2021.) $)
    unblimceq0 $p |- ( ph -> ( F limCC A ) = (/) ) $=
      ( vz vc ve wcel clt wbr crp wrex c1 vy va climc co cv cc wne cmin cabs wa
      cfv wi wral wn 1rp a1i wb breq2 imbi2d rexralbidv notbid adantl caddc cle
      wceq w3a simprr1 simprr2 jca 1red ad2antrr adantr simprl ffvelcdmd simplr
      wf subcld abscld cr resubcld 1cnd recnd pncand readdcld lesub1dd eqbrtrrd
      simprr3 abs2difd letrd lensymd jcnd 3anbi2d rexbidv breq1 3anbi3d ralbidv
      unblimceq0lem cc0 0lt1 absge0d addgtge0d elrpd rspcdva simpr rexnal sylib
      reximddv nrexdv rspcedvd ex imnan ellimc3 mtbird eq0rdv ) AUAECUCUDZAUAUE
      ZXOOXPUFOZLUEZCUGZXRCUHUDUIUKZMUEZPQZUJZXREUKZXPUHUDZUIUKZNUEZPQZULZLDUMM
      RSZNRUMZUJZAXQYKUNZULYLUNAXQYMAXQUJZYJUNZNRSYMYNYOYCYFTPQZULZLDUMZMRSZUNZ
      NTRTROYNUOUPYGTVEZYOYTUQYNUUAYJYSUUAYIYQMLRDUUAYHYPYCYGTYFPURUSUTVAVBYNYR
      MRYNYAROZUJZYQUNZLDSYRUNUUCXSYBTXPUIUKZVCUDZYDUIUKZVDQZVFZUUDLDUUCXRDOZUU
      IUJZUJZYCYPUULXSYBXSYBUUHUUJUUCVGXSYBUUHUUJUUCVHVIUULTYFUULVJZUULYEUULYDX
      PUULDUFXREUUCDUFEVPZUUKAUUNXQUUBIVKVLUUCUUJUUIVMVNZUUCXQUUKAXQUUBVOZVLZVQ
      VRZUULTUUGUUEUHUDZYFUUMUULUUGUUEUULYDUUOVRZUUCUUEVSOUUKUUCXPUUPVRZVLZVTUU
      RUULUUFUUEUHUDTUUSVDUULTUUEUULWAUULUUEUVBWBWCUULUUFUUGUUEUUCUUFVSOUUKUUCT
      UUEUUCVJZUVAWDZVLUUTUVBXSYBUUHUUJUUCWGWEWFUULYDXPUUOUUQWHWIWJWKUUCXSXTGUE
      ZPQZUUHVFZLDSZUUILDSGRYAUVEYAVEZUVGUUILDUVIUVFYBXSUUHUVEYAXTPURWLWMUUCXSU
      VFUBUEZUUGVDQZVFZLDSZGRUMZUVHGRUMUBRUUFUVJUUFVEZUVMUVHGRUVOUVLUVGLDUVOUVK
      UUHXSUVFUVJUUFUUGVDWNWOWMWPAUVNUBRUMXQUUBABLCDEFUBGHIJKWQVKUUCUUFUVDUUCTU
      UEUVCUVAWRTPQUUCWSUPUUCXPUUPWTXAXBXCYNUUBXDXCXGYQLDXEXFXHXIYJNRXEXFXJXQYK
      XKXFANMLDCXPEIHJXLXMXN $.
  $}

  ${
    $d A b d x $.  $d A y z $.  $d F b d x $.  $d F y z $.  $d G b d x $.
    $d S b d x $.  $d S y z $.  $d X b d x $.  $d X z $.  $d ph b d x $.
    $d ph y z $.
    unbdqndv1.g $e |- G = ( z e. ( X \ { A } ) |->
        ( ( ( F ` z ) - ( F ` A ) ) / ( z - A ) ) ) $.
    unbdqndv1.1 $e |- ( ph -> S C_ CC ) $.
    unbdqndv1.2 $e |- ( ph -> X C_ S ) $.
    unbdqndv1.3 $e |- ( ph -> F : X --> CC ) $.
    unbdqndv1.4 $e |- ( ph -> A. b e. RR+ A. d e. RR+ E. x e. ( X \ { A } )
      ( ( abs ` ( x - A ) ) < d /\ b <_ ( abs ` ( G ` x ) ) ) ) $.
    $( If the difference quotient
       ` ( ( ( F `` z ) - ( F `` A ) ) / ( z - A ) ) ` is unbounded near ` A `
       then ` F ` is not differentiable at ` A ` .  (Contributed by Asger C.
       Ipsen, 12-May-2021.) $)
    unbdqndv1 $p |- ( ph -> -. A e. dom ( S _D F ) ) $=
      ( vy co wn cfv cc cdv cdm wcel wa cv wbr wal ccnfld ctopn crest cnt climc
      c0 noel a1i csn cdif wss sstrd adantr ssdifssd cmin wf dvbss sselda dvlem
      cdiv fmptd sseldd cabs clt cle wrex crp wral unblimceq0 neleqtrrd intnand
      wb eqid eldv notbid mpbird alrimiv wex simpr eldmg syl alnex bicomd bitrd
      pm2.01da ) ADEFUAQZUBZUCZAWOUDZWORZDPUEZWMUFZRZPUGZWPWTPWPWTDHUHUISZEUJQZ
      UKSSUCZWRGDULQZUCZUDZRZWPXFXDWPXEUMWRWRUMUCRWPWRUNUOWPBDHDUPZUQZGIJWPHTXI
      AHTURWOAHETMLUSUTZVAWPCXJCUEZFSDFSVBQXLDVBQVGQTGWPXLDHFAHTFVCWONUTXKAWNHD
      AHEFLNMVDVEZVFKVHWPHTDXKXMVIABUEZDVBQVJSJUEVKUFIUEXNGSVJSVLUFUDBXJVMJVNVO
      IVNVOWOOUTVPVQVRAWTXHVSWOAWSXGACHDWREXCFGXBXCVTXBVTKLNMWAWBUTWCWDWPWQWSPW
      EZRZXAWPWOXOWPWOWOXOVSAWOWFPDWMWNWGWHWBWPXAXPXAXPVSWPWSPWIUOWJWKWCWL $.
  $}

  ${
    unbdqndv2lem1.a $e |- ( ph -> A e. CC ) $.
    unbdqndv2lem1.b $e |- ( ph -> B e. CC ) $.
    unbdqndv2lem1.c $e |- ( ph -> C e. CC ) $.
    unbdqndv2lem1.d $e |- ( ph -> D e. CC ) $.
    unbdqndv2lem1.e $e |- ( ph -> E e. RR+ ) $.
    unbdqndv2lem1.1 $e |- ( ph -> D =/= 0 ) $.
    unbdqndv2lem1.2 $e |- ( ph ->
          ( 2 x. E ) <_ ( abs ` ( ( A - B ) / D ) ) ) $.
    $( Lemma for ~ unbdqndv2 .  (Contributed by Asger C. Ipsen,
       12-May-2021.) $)
    unbdqndv2lem1 $p |- ( ph -> ( ( E x. ( abs ` D ) ) <_ ( abs ` ( A - C ) )
                      \/ ( E x. ( abs ` D ) ) <_ ( abs ` ( B - C ) ) ) ) $=
      ( cabs co wbr clt adantr cr wcel cfv cmul cmin cle wo cdiv c2 wceq subcld
      wn wa absdivd caddc abscld readdcld 2re a1i rpred remulcld abssubd oveq2d
      abs3difd breqtrd pm2.45 adantl ltnled mpbird pm2.46 lt2addd recnd 2timesd
      wb eqcomd mulassd eqtrd lelttrd cc0 w3a wne cc absgt0 syl mpbid ltdivmul2
      jca 3jca eqbrtrd divcld lenltd condan ) AFENUAZUBOZBDUCOZNUAZUDPZWLCDUCOZ
      NUAZUDPZUEZBCUCOZEUFOZNUAZUGFUBOZQPZAWSUJZUKZXBWTNUAZWKUFOZXCQAXBXHUHXEAW
      TEABCGHUIZJLULRXFXHXCQPZXGXCWKUBOZQPZXFXGWNWQUMOZXKAXGSTZXEAWTXIUNZRAXMST
      XEAWNWQAWMABDGIUIUNZAWPACDHIUIUNZUORAXKSTXEAXCWKAUGFUGSTAUPUQZAFKURZUSZAE
      JUNZUSRAXGXMUDPXEAXGWNDCUCONUAZUMOXMUDABCDGHIVBAYBWQWNUMADCIHUTVAVCRXFXMW
      LWLUMOZXKQXFWNWQWLWLAWNSTXEXPRAWQSTXEXQRAWLSTXEAFWKXSYAUSZRZYEXFWNWLQPZWO
      UJZXEYGAWOWRVDVEAYFYGVLXEAWNWLXPYDVFRVGXFWQWLQPZWRUJZXEYIAWOWRVHVEAYHYIVL
      XEAWQWLXQYDVFRVGVIAYCXKUHXEAYCUGWLUBOZXKAYJYCAWLAWLYDVJVKVMAXKYJAUGFWKAUG
      XRVJAFXSVJAWKYAVJVNVMVORVCVPAXJXLVLZXEAXNXCSTZWKSTZVQWKQPZUKZVRYKAXNYLYOX
      OXTAYMYNYAAEVQVSZYNLAEVTTYPYNVLJEWAWBWCWEWFXGXCWKWDWBRVGWGAXDUJZXEAXCXBUD
      PYQMAXCXBXTAXAAWTEXIJLWHUNWIWCRWJ $.
  $}

  ${
    $d A z $.  $d B z $.  $d F z $.  $d U z $.  $d V z $.  $d X z $.
    $d ph z $.
    unbdqndv2lem2.g $e |- G = ( z e. ( X \ { A } ) |->
        ( ( ( F ` z ) - ( F ` A ) ) / ( z - A ) ) ) $.
    unbdqndv2lem2.w $e |- W =
        if ( ( B x. ( V - U ) )
            <_ ( abs ` ( ( F ` U ) - ( F ` A ) ) ) , U , V ) $.
    unbdqndv2lem2.x $e |- ( ph -> X C_ RR ) $.
    unbdqndv2lem2.f $e |- ( ph -> F : X --> CC ) $.
    unbdqndv2lem2.a $e |- ( ph -> A e. X ) $.
    unbdqndv2lem2.b $e |- ( ph -> B e. RR+ ) $.
    unbdqndv2lem2.d $e |- ( ph -> D e. RR+ ) $.
    unbdqndv2lem2.u $e |- ( ph -> U e. X ) $.
    unbdqndv2lem2.v $e |- ( ph -> V e. X ) $.
    unbdqndv2lem2.1 $e |- ( ph -> U =/= V ) $.
    unbdqndv2lem2.2 $e |- ( ph -> U <_ A ) $.
    unbdqndv2lem2.3 $e |- ( ph -> A <_ V ) $.
    unbdqndv2lem2.4 $e |- ( ph -> ( V - U ) < D ) $.
    unbdqndv2lem2.5 $e |- ( ph ->
      ( 2 x. B ) <_ ( ( abs ` ( ( F ` V ) - ( F ` U ) ) ) / ( V - U ) ) ) $.
    $( Lemma for ~ unbdqndv2 .  (Contributed by Asger C. Ipsen,
       12-May-2021.) $)
    unbdqndv2lem2 $p |- ( ph ->
     ( W e. ( X \ { A } ) /\
      ( ( abs ` ( W - A ) ) < D /\ B <_ ( abs ` ( G ` W ) ) ) ) ) $=
      ( cmin cmul cfv cabs cle wbr csn cdif wcel clt cif wceq a1i iftrue adantl
      co wa eqtrd wne adantr cc0 simplr fveq2 eqcomd oveq2d fveq2d cc ffvelcdmd
      subidd abs0 adantlr breqtrd wn rpred sseldd resubcld rpgt0d letrd leneltd
      necomd posdifd mpbid mulgt0d 0red remulcld ltnled pm2.65da neqned eldifsn
      jca sylibr eqeltrd oveq1d abssuble0d lesub1dd lelttrd eqbrtrd cdiv subcld
      cr abscld ltled lemul2ad simpr crp wb ltlend mpbird elrp lemuldivd cv cvv
      oveq1 oveq12d ovexd fvmptd3 subne0d absdivd iffalsed wo abssubge0d breq1d
      recnd mtbird gtned c2 unbdqndv2lem1 orel2 sylc lesub2dd 3brtr4d pm2.61dan
      absrpcld ) ADIFUFVAZUGVAZFGUHZCGUHZUFVAZUIUHZUJUKZJKCULUMZUNZJCUFVAZUIUHZ
      EUOUKZDJHUHZUIUHZUJUKZVBZVBAUUEVBZUUGUUNUUOJFUUFUUOJUUEFIUPZFJUUPUQZUUOMU
      RUUEUUPFUQAUUEFIUSUTVCZUUOFKUNZFCVDZVBFUUFUNUUOUUSUUTAUUSUUESVEUUOFCUUOFC
      UQZYTVFUJUKZUUOUVAVBYTUUDVFUJAUUEUVAVGAUVAUUDVFUQUUEAUVAVBZUUDUUAUUAUFVAZ
      UIUHZVFUVAUUDUVEUQAUVAUUCUVDUIUVAUUBUUAUUAUFUVAUUAUUBFCGVHVIVJVKUTUVCUVEV
      FUIUHZVFAUVEUVFUQUVAAUVDVFUIAUUAAKVLFGOSVMZVNVKVEUVFVFUQZUVCVOURVCVCVPVQU
      UOUVBVRZUVAAUVIUUEAVFYTUOUKUVIADYSADQVSZAIFAKXEINTVTZAKXEFNSVTZWAZADQWBZA
      FIUOUKVFYSUOUKAFIUVLUVKAFCIUVLAKXECNPVTZUVKUBUCWCZAFIUAWEWDAFIUVLUVKWFWGZ
      WHAVFYTAWIZADYSUVJUVMWJZWKWGZVEVEWLWMZWOFKCWNWPZWQUUOUUJUUMUUOUUICFUFVAZE
      UOUUOUUIFCUFVAZUIUHZUWCUUOUUHUWDUIUUOJFCUFUURWRVKAUWEUWCUQUUEAFCUVLUVOUBW
      SVEZVCAUWCEUOUKUUEAUWCYSEACFUVOUVLWAZUVMAERVSZACIFUVOUVKUVLUCWTZUDXAVEXBU
      UODUUDUWCXCVAZUULUJUUODUWCUGVAZUUDUJUKDUWJUJUKUUOUWKYTUUDAUWKXEUNUUEADUWC
      UVJUWGWJVEAYTXEUNUUEUVSVEAUUDXEUNUUEAUUCAUUAUUBUVGAKVLCGOPVMZXDZXFVEZAUWK
      YTUJUKUUEAUWCYSDUWGUVMUVJAVFDUVRUVJUVNXGZUWIXHVEAUUEXIWCUUODUUDUWCADXEUNZ
      UUEUVJVEUWNUUOUWCXEUNZVFUWCUOUKZVBUWCXJUNUUOUWQUWRAUWQUUEUWGVEUUOFCUOUKZU
      WRUUOUWSFCUJUKZCFVDZVBZUUOUWTUXAAUWTUUEUBVEUUOFCUWAWEWOAUWSUXBXKUUEAFCUVL
      UVOXLVEXMAUWSUWRXKUUEAFCUVLUVOWFVEWGWOUWCXNWPXOWGUUOUULUWJUUOUULUUCUWDXCV
      AZUIUHZUWJUUOUUKUXCUIUUOUUKFHUHUXCUUOJFHUURVKUUOBFBXPZGUHZUUBUFVAZUXECUFV
      AZXCVAZUXCUUFHXQLUXEFUQZUXGUUCUXHUWDXCUXJUXFUUAUUBUFUXEFGVHWRUXEFCUFXRXSU
      WBUUOUUCUWDXCXTYAVCVKUUOUXDUUDUWEXCVAUWJUUOUUCUWDAUUCVLUNUUEUWMVEAUWDVLUN
      UUEAFCAFUVLYHZACUVOYHZXDVEUUOFCAFVLUNUUEUXKVEACVLUNZUUEUXLVEUWAYBYCUUOUWE
      UWCUUDXCUWFVJVCVCVIVQWOWOAUUEVRZVBZUUGUUNUXOJIUUFUXOJUUPIUUQUXOMURUXOUUEF
      IAUXNXIZYDVCZUXOIKUNZICVDZVBIUUFUNUXOUXRUXSAUXRUXNTVEUXOICUXOICUQZDYSUIUH
      ZUGVAZVFUJUKZUXOUXTVBUYBIGUHZUUBUFVAZUIUHZVFUJUXOUYBUYFUJUKZUXTUXOUYBUUDU
      JUKZVRUYGUYHYEZUYGUXOUYHUUEUXPAUYHUUEXKUXNAUYBYTUUDUJAUYAYSDUGAFIUVLUVKUV
      PYFZVJZYGVEYIAUYIUXNAUYDUUAUUBYSDAKVLIGOTVMZUVGUWLAYSUVMYHZQAVFYSUVRUVQYJ
      ZAYKDUGVAUYDUUAUFVAZUIUHZYSXCVAZUYOYSXCVAUIUHZUJUEAUYRUYQAUYRUYPUYAXCVAUY
      QAUYOYSAUYDUUAUYLUVGXDUYMUYNYCAUYAYSUYPXCUYJVJVCVIVQYLVEUYHUYGYMYNZVEAUXT
      UYFVFUQUXNAUXTVBZUYFUVFVFUYTUYEVFUIUYTUYEUUBUUBUFVAZVFUXTUYEVUAUQAUXTUYDU
      UBUUBUFICGVHWRUTAVUAVFUQUXTAUUBUWLVNVEVCVKUVHUYTVOURVCVPVQUXOUYCVRZUXTAVU
      BUXNAUYCUVBUVTAUYBYTVFUJUYKYGYIVEVEWLWMZWOIKCWNWPZWQUXOUUJUUMUXOUUIICUFVA
      ZEUOUXOUUIVUEUIUHZVUEUXOUUHVUEUIUXOJICUFUXQWRVKAVUFVUEUQUXNACIUVOUVKUCYFZ
      VEVCAVUEEUOUKUXNAVUEYSEAICUVKUVOWAZUVMUWHAFCIUVLUVOUVKUBYOZUDXAVEXBUXODUY
      FVUFXCVAZUULUJUXODVUFUGVAZUYFUJUKDVUJUJUKUXOVUKUYBUYFAVUKXEUNUXNADVUFUVJA
      VUFVUEXEVUGVUHWQZWJVEAUYBXEUNUXNAUYBYTXEUYKUVSWQVEAUYFXEUNUXNAUYEAUYDUUBU
      YLUWLXDZXFVEZAVUKUYBUJUKUXNAVUFUYADVULAUYAYSXEUYJUVMWQUVJUWOAVUEYSVUFUYAU
      JVUIVUGUYJYPXHVEUYSWCUXODUYFVUFAUWPUXNUVJVEVUNUXOVUEAVUEVLUNUXNAVUEVUHYHV
      EZUXOICAIVLUNUXNAIUVKYHVEAUXMUXNUXLVEVUCYBZYRXOWGUXOUULVUJUXOUULUYEVUEXCV
      AZUIUHVUJUXOUUKVUQUIUXOUUKIHUHVUQUXOJIHUXQVKUXOBIUXIVUQUUFHXQLUXEIUQZUXGU
      YEUXHVUEXCVURUXFUYDUUBUFUXEIGVHWRUXEICUFXRXSVUDUXOUYEVUEXCXTYAVCVKUXOUYEV
      UEAUYEVLUNUXNVUMVEVUOVUPYCVCVIVQWOWOYQ $.
  $}

  ${
    $d A b c d x y $.  $d A c d w x y z $.  $d F b c d x y $.
    $d F c d w x y z $.  $d X b c d x y $.  $d X c d w x y z $.
    $d ph b c d x y $.  $d ph w x y z $.
    unbdqndv2.x $e |- ( ph -> X C_ RR ) $.
    unbdqndv2.f $e |- ( ph -> F : X --> CC ) $.
    unbdqndv2.1 $e |- ( ph -> A. b e. RR+ A. d e. RR+ E. x e. X E. y e. X
      ( ( x <_ A /\ A <_ y ) /\ ( ( y - x ) < d /\ x =/= y ) /\
         b <_ ( ( abs ` ( ( F ` y ) - ( F ` x ) ) ) / ( y - x ) ) ) ) $.
    $( Variant of ~ unbdqndv1 with the hypothesis that
       ` ( ( ( F `` y ) - ( F `` x ) ) / ( y - x ) ) ` is unbounded where
       ` x <_ A ` and ` A <_ y ` .  (Contributed by Asger C. Ipsen,
       12-May-2021.) $)
    unbdqndv2 $p |- ( ph -> -. A e. dom ( RR _D F ) ) $=
      ( co wcel wa cfv cmin cabs wbr cle crp vw vz vc cr cdv cdm cdif cdiv cmpt
      csn cv eqid cc wss ax-resscn a1i adantr wf clt wrex wne c2 cmul wral wceq
      w3a breq1 3anbi3d rexbidv ralbidv ad2antrr simprl rpmulcld rspcdva simprr
      2rp rsp sylc ad3antrrr dvbss simpr sseldd simplrl simplrr simpr2r simpr1l
      cif simpr1r simpr2l simpr3 unbdqndv2lem2 simpld wb fvoveq1 breq1d anbi12d
      2fveq3 breq2d adantl simprd rspcedvd ex rexlimdvva mpd unbdqndv1 pm2.01da
      ralrimivva ) ADUDEUELUFZMZAXINZUAUBDUDEUBFDUJUGZUBUKZEODEOZPLXLDPLUHLUIZF
      UCHXNULZUDUMUNXJUOUPZAFUDUNZXIIUQZAFUMEURZXIJUQZXJUAUKZDPLQOZHUKZUSRZUCUK
      ZYAXNOQOZSRZNZUAXKUTZUCHTTXJYETMZYCTMZNZNZBUKZDSRZDCUKZSRZNZYPYNPLZYCUSRZ
      YNYPVAZNZVBYEVCLZYPEOYNEOZPLQOYSUHLZSRZVFZCFUTZBFUTZYIYMUUIHTVDZYKUUIYMYR
      UUBGUKZUUESRZVFZCFUTZBFUTZHTVDZUUJGTUUCUUKUUCVEZUUOUUIHTUUQUUNUUHBFUUQUUM
      UUGCFUUQUULUUFYRUUBUUKUUCUUESVGVHVIVIVJAUUPGTVDXIYLKVKYMVBYEVBTMYMVPUPXJY
      JYKVLZVMVNXJYJYKVOZUUIHTVQVRYMUUGYIBCFFYMYNFMZYPFMZNZNZUUGYIUVCUUGNZYHYEY
      SVCLUUDXMPLQOSRYNYPWGZDPLQOZYCUSRZYEUVEXNOQOZSRZNZUAUVEXKUVDUVEXKMZUVJUVD
      UBDYEYCYNEXNYPUVEFXOUVEULXJXQYLUVBUUGXRVSXJXSYLUVBUUGXTVSUVCDFMZUUGYMUVLU
      VBXJUVLYLXJXHFDXJFUDEXPXTXRVTAXIWAWBUQUQUQYMYJUVBUUGUURVKYMYKUVBUUGUUSVKY
      MUUTUVAUUGWCYMUUTUVAUUGWDYTUUAYRUUFUVCWEYOYQUUBUUFUVCWFYOYQUUBUUFUVCWHYTU
      UAYRUUFUVCWIUVCYRUUBUUFWJWKZWLYAUVEVEZYHUVJWMUVDUVNYDUVGYGUVIUVNYBUVFYCUS
      YAUVEDQPWNWOUVNYFUVHYESYAUVEQXNWQWRWPWSUVDUVKUVJUVMWTXAXBXCXDXGXEXF $.
  $}

  ${
    knoppndvlem1.n $e |- ( ph -> N e. NN ) $.
    knoppndvlem1.j $e |- ( ph -> J e. ZZ ) $.
    knoppndvlem1.m $e |- ( ph -> M e. ZZ ) $.
    $( Lemma for ~ knoppndv .  (Contributed by Asger C. Ipsen, 15-Jun-2021.)
       (Revised by Asger C. Ipsen, 5-Jul-2021.) $)
    knoppndvlem1 $p |- ( ph -> ( ( ( ( 2 x. N ) ^ -u J ) / 2 ) x. M ) e. RR )
      $=
      ( c2 cmul co cneg wcel a1i syl zred remulcld recnd cc0 c1 wbr cexp cr 2re
      cdiv cn cz nnz wne 2ne0 0red 1red clt 0lt1 cle nnge1 ltletrd ltned necomd
      mulne0d znegcld reexpclzd redivcld ) AHDIJZBKZUAJZHUDJCAVEHAVCVDAHDHUBLAU
      CMZADADUELZDUFLEDUGNOZPAHDAHVFQADVHQHRUHAUIMZARDARDAUJZARSDVJAUKVHRSULTAU
      MMAVGSDUNTEDUONUPUQURUSABFUTVAVFVIVBACGOP $.
  $}

  ${
    knoppndvlem2.n $e |- ( ph -> N e. NN ) $.
    knoppndvlem2.i $e |- ( ph -> I e. ZZ ) $.
    knoppndvlem2.j $e |- ( ph -> J e. ZZ ) $.
    knoppndvlem2.m $e |- ( ph -> M e. ZZ ) $.
    knoppndvlem2.1 $e |- ( ph -> J < I ) $.
    $( Lemma for ~ knoppndv .  (Contributed by Asger C. Ipsen, 15-Jun-2021.)
       (Revised by Asger C. Ipsen, 5-Jul-2021.) $)
    knoppndvlem2 $p |- ( ph -> ( ( ( 2 x. N ) ^ I ) x.
      ( ( ( ( 2 x. N ) ^ -u J ) / 2 ) x. M ) ) e. ZZ ) $=
      ( c2 cmul co cexp cz wcel syl cc0 wa jca cneg cdiv cmin c1 2cnd cn mulcld
      nnz zcnd wne 2ne0 a1i 0red 1red zred clt wbr 0lt1 cle nnge1 ltletrd ltned
      necomd mulne0d expclzd znegcld divcld mulassd eqcomd divassd wceq expaddz
      caddc cc negsubd oveq2d wb znnsub mpbid expm1t 3eqtrd oveq1d cn0 peano2zm
      zsubcl posdifd 0zd zltlem1 elnn0z sylibr expcld divcan3d 2z zmulcl zexpcl
      eqtrd zmulcld eqeltrd ) AKELMZBNMZWSCUAZNMZKUBMZDLMLMZWSBCUCMZUDUCMZNMZEL
      MZDLMZOAXDWTXCLMZDLMZXIAXKXDAWTXCDAWSBAKEAUEZAEAEUFPZEOPZFEUHQZUIZUGZAKEX
      LXPKRUJAUKULZAREAREAUMZARUDEXSAUNAEXOUORUDUPUQAURULAXMUDEUSUQFEUTQVAVBVCV
      DZGVEZAXBKAWSXAXQXTACHVFZVEZXLXRVGADIUIVHVIAXJXHDLAXJWTXBLMZKUBMZXGWSLMZK
      UBMZXHAYEXJAWTXBKYAYCXLXRVJVIAYDYFKUBAYDWSBXAVMMZNMZWSXENMZYFAYIYDAWSVNPZ
      WSRUJZSZBOPZXAOPZSZSYIYDVKAYMYPAYKYLXQXTTAYNYOGYBTTWSBXAVLQVIAYHXEWSNABCA
      BGUIACHUIVOVPAYKXEUFPZSYJYFVKAYKYQXQACBUPUQZYQJACOPZYNSYRYQVQAYSYNHGTCBVR
      QVSTWSXEVTQWAWBAYGXGWSKUBMZLMXHAXGWSKAWSXFXQAXFOPZRXFUSUQZSXFWCPZAUUAUUBA
      XEOPZUUAAYNYSSUUDAYNYSGHTBCWEQZXEWDQARXEUPUQZUUBAYRUUFJACBACHUOABGUOWFVSA
      ROPZUUDSUUFUUBVQAUUGUUDAWGUUETRXEWHQVSTXFWIWJZWKXQXLXRVJAYTEXGLAEKXPXLXRW
      LVPWPWAWBWPAXHDAXGEAWSOPZUUCSXGOPAUUIUUCAKOPZXNSUUIAUUJXNUUJAWMULXOTKEWNQ
      UUHTWSXFWOQXOWQIWQWR $.
  $}

  ${
    knoppndvlem3.c $e |- ( ph -> C e. ( -u 1 (,) 1 ) ) $.
    $( Lemma for ~ knoppndv .  (Contributed by Asger C. Ipsen, 15-Jun-2021.) $)
    knoppndvlem3 $p |- ( ph -> ( C e. RR /\ ( abs ` C ) < 1 ) ) $=
      ( cr wcel cabs cfv c1 clt wbr cneg cioo co elioore syl wa eliooord absltd
      1red mpbird jca ) ABDEZBFGHIJZABHKZHLMEZUBCBUDHNOZAUCUDBIJBHIJPZAUEUGCBUD
      HQOABHUFASRTUA $.
  $}

  ${
    $d A k v $.  $d C m n y $.  $d F i m w z $.  $d F k m v z $.  $d N n y $.
    $d N x $.  $d T n y $.  $d W k $.  $d ph i m n w y z $.  $d i m w x z $.
    $d ph k m v z $.
    knoppndvlem4.t $e |- T = ( x e. RR |->
                            ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) ) $.
    knoppndvlem4.f $e |- F = ( y e. RR |-> ( n e. NN0 |->
            ( ( C ^ n ) x. ( T ` ( ( ( 2 x. N ) ^ n ) x. y ) ) ) ) ) $.
    knoppndvlem4.w $e |- W =
                        ( w e. RR |-> sum_ i e. NN0 ( ( F ` w ) ` i ) ) $.
    knoppndvlem4.a $e |- ( ph -> A e. RR ) $.
    knoppndvlem4.c $e |- ( ph -> C e. ( -u 1 (,) 1 ) ) $.
    knoppndvlem4.n $e |- ( ph -> N e. NN ) $.
    $( Lemma for ~ knoppndv .  (Contributed by Asger C. Ipsen, 15-Jun-2021.)
       (Revised by Asger C. Ipsen, 5-Jul-2021.) $)
    knoppndvlem4 $p |- ( ph
                      -> seq 0 ( + , ( F ` A ) ) ~~> ( W ` A ) ) $=
      ( cfv cc0 vk vm vz vv cr caddc cof cn0 cv cmpt cseq cvv nn0uz 0zd wcel c1
      cabs clt wbr knoppndvlem3 simpld knoppcnlem8 seqex a1i wa cn adantr simpr
      knoppcnlem7 fveq1d wceq eqid fveq2 seqeq3d fvexd eqtrd simprd knoppcnlem9
      fvmptd3 ulmclm ) AEUEUAUFUGUBUHUCUEUBUIUCUIJSSUJUJTUKZLUFEJSZTUKZTULUHUMA
      UNABCUCFGUBIJKMNRAFUEUOZFUQSUPURUSZAFQUTZVAZVBPWCULUOAUFWBTVCVDAUAUIZUHUO
      ZVEZEWHWASZSEUDUEWHUFUDUIZJSZTUKZSZUJZSZWHWCSZWJEWKWPWJBCUCUDFGUBIJWHKMNA
      KVFUOWIRVGAWDWIWGVGAWIVHVIVJAWQWRVKWIAUDEWOWRUEWPULWPVLWLEVKZWHWNWCWSWMWB
      UFTWLEJVMVNVJPAWHWCVOVSVGVPABCUCDFGHUBIJKLMNORWGAWDWEWFVQVRVT $.
  $}

  ${
    $d A n y $.  $d A x $.  $d C n y $.  $d J i n y $.  $d N n y $.  $d N x $.
    $d T n y $.  $d ph i n y $.  $d i x $.
    knoppndvlem5.t $e |- T = ( x e. RR |->
                            ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) ) $.
    knoppndvlem5.f $e |- F = ( y e. RR |-> ( n e. NN0 |->
            ( ( C ^ n ) x. ( T ` ( ( ( 2 x. N ) ^ n ) x. y ) ) ) ) ) $.
    knoppndvlem5.a $e |- ( ph -> A e. RR ) $.
    knoppndvlem5.c $e |- ( ph -> C e. RR ) $.
    knoppndvlem5.n $e |- ( ph -> N e. NN ) $.
    $( Lemma for ~ knoppndv .  (Contributed by Asger C. Ipsen, 15-Jun-2021.)
       (Revised by Asger C. Ipsen, 5-Jul-2021.) $)
    knoppndvlem5 $p |- ( ph ->
              sum_ i e. ( 0 ... J ) ( ( F ` A ) ` i ) e. RR ) $=
      ( cc0 cfv wcel adantr cfz co cv fzfid wa cn cr elfznn0 adantl knoppcnlem3
      cn0 fsumrecl ) AQJUAUBZGUCZDIRRGAQJUDAUNUMSZUEBCDEFHIUNKLMAKUFSUOPTAEUGSU
      OOTADUGSUONTUOUNUKSAUNJUHUIUJUL $.
  $}

  ${
    $d A i n w y $.  $d A i w x $.  $d C n y $.  $d F i w $.  $d J i n y $.
    $d N n y $.  $d N x $.  $d T n y $.  $d ph i n w y $.
    knoppndvlem6.t $e |- T = ( x e. RR |->
                            ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) ) $.
    knoppndvlem6.f $e |- F = ( y e. RR |-> ( n e. NN0 |->
            ( ( C ^ n ) x. ( T ` ( ( ( 2 x. N ) ^ n ) x. y ) ) ) ) ) $.
    knoppndvlem6.w $e |- W =
                        ( w e. RR |-> sum_ i e. NN0 ( ( F ` w ) ` i ) ) $.
    knoppndvlem6.a $e |- A = ( ( ( ( 2 x. N ) ^ -u J ) / 2 ) x. M ) $.
    knoppndvlem6.c $e |- ( ph -> C e. ( -u 1 (,) 1 ) ) $.
    knoppndvlem6.j $e |- ( ph -> J e. NN0 ) $.
    knoppndvlem6.m $e |- ( ph -> M e. ZZ ) $.
    knoppndvlem6.n $e |- ( ph -> N e. NN ) $.
    $( Lemma for ~ knoppndv .  (Contributed by Asger C. Ipsen, 15-Jun-2021.)
       (Revised by Asger C. Ipsen, 5-Jul-2021.) $)
    knoppndvlem6 $p |- ( ph -> ( W ` A ) =
                        sum_ i e. ( 0 ... J ) ( ( F ` A ) ` i ) ) $=
      ( cfv cc0 cfz co cv csu c1 caddc cuz cn0 cmin cr cvv wceq fveq2 sumeq2sdv
      fveq1d c2 cmul cneg cexp cdiv a1i nn0zd knoppndvlem1 eqeltrd wcel fvmptd3
      sumex nn0uz eqid peano2nn0 syl wa eqidd cn adantr clt knoppndvlem3 simpld
      cabs wbr simpr knoppcnlem3 recnd cseq cli cdm knoppndvlem4 fvex isumsplit
      seqex breldm nn0cnd 1cnd pncand oveq2d sumeq1d oveq1d eluznn0 knoppcnlem1
      3eqtrd sylan cz cle eluzle adantl jca zltp1le mpbird knoppndvlem2 dnizeq0
      wb cc expcld mul01d sumeq2dv wss cfn ssidd orcd sumz knoppndvlem5 addridd
      wo eqtrd ) AENUCZUDKUEUFZHUGZEJUCZUCZHUHZKUIUJUFZUKUCZYMHUHZUJUFZYNAYIULY
      MHUHZUDYOUIUMUFZUEUFZYMHUHZYQUJUFYRADEULYKDUGZJUCZUCZHUHYSUNNUOQUUCEUPZUL
      UUEYMHUUFYKUUDYLUUCEJUQUSURAEUTMVAUFZKVBVCUFUTVDUFLVAUFZUNEUUHUPZARVEAKLM
      UBAKTVFZUAVGVHZYSUOVIAULYMHVKVEVJAYMHYLUDYOYPULVLYPVMAKULVIYOULVIZTKVNVOZ
      AYKULVIZVPZYMVQUUOYMUUOBCEFGIJYKMOPAMVRVIZUUNUBVSAFUNVIZUUNAUUQFWCUCUIVTW
      DAFSWAWBZVSAEUNVIZUUNUUKVSAUUNWEWFWGAUJYLUDWHZYIWIWDUUTWIWJVIABCDEFGHIJMN
      OPQUUKSUBWKUUTYIWIUJYLUDWNENWLWOVOWMAUUBYNYQUJAUUAYJYMHAYTKUDUEAKUIAKTWPA
      WQWRWSWTXAXDAYRYNUDUJUFYNAYQUDYNUJAYQYPUDHUHZUDAYPYMUDHAYKYPVIZVPZYMFYKVC
      UFZUUGYKVCUFZEVAUFZGUCZVAUFUVDUDVAUFUDUVCCEFGIJYKMPAUUSUVBUUKVSAUULUVBUUN
      UUMYKYOXBXEZXCUVCUVGUDUVDVAUVCBUVFGOUVCUVFUVEUUHVAUFXFUVCEUUHUVEVAUUIUVCR
      VEWSUVCYKKLMAUUPUVBUBVSUVCYKUVHVFZAKXFVIZUVBUUJVSZALXFVIUVBUAVSUVCKYKVTWD
      ZYOYKXGWDZUVBUVMAYOYKXHXIUVCUVJYKXFVIZVPUVLUVMXOUVCUVJUVNUVKUVIXJKYKXKVOX
      LXMVHXNWSUVCUVDUVCFYKAFXPVIUVBAFUURWGVSUVHXQXRXDXSAYPYPXTZYPYAVIZYGUVAUDU
      PAUVOUVPAYPYBYCYPHYOYDVOYHWSAYNAYNABCEFGHIJKMOPUUKUURUBYEWGYFYHYH $.
  $}

  ${
    $d A n y $.  $d C n y $.  $d J n $.  $d N n y $.  $d T n y $.  $d ph n y $.
    knoppndvlem7.t $e |- T = ( x e. RR |->
                            ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) ) $.
    knoppndvlem7.f $e |- F = ( y e. RR |-> ( n e. NN0 |->
            ( ( C ^ n ) x. ( T ` ( ( ( 2 x. N ) ^ n ) x. y ) ) ) ) ) $.
    knoppndvlem7.a $e |- A = ( ( ( ( 2 x. N ) ^ -u J ) / 2 ) x. M ) $.
    knoppndvlem7.j $e |- ( ph -> J e. NN0 ) $.
    knoppndvlem7.m $e |- ( ph -> M e. ZZ ) $.
    knoppndvlem7.n $e |- ( ph -> N e. NN ) $.
    $( Lemma for ~ knoppndv .  (Contributed by Asger C. Ipsen, 15-Jun-2021.)
       (Revised by Asger C. Ipsen, 5-Jul-2021.) $)
    knoppndvlem7 $p |- ( ph -> ( ( F ` A ) ` J ) =
                            ( ( C ^ J ) x. ( T ` ( M / 2 ) ) ) ) $=
      ( co c2 cmul cfv cexp cdiv cneg wceq a1i knoppndvlem1 eqeltrd knoppcnlem1
      cr nn0zd oveq2i c1 2cnd wcel nnz syl zcnd mulcld expcld cc0 wne 2ne0 0red
      cn 1red zred clt wbr 0lt1 cle nnge1 ltletrd ltned mulne0d znegcld expclzd
      necomd divcld mulassd eqcomd divassd expnegd oveq2d expne0d recidd oveq1d
      cz eqtrd divrec2d 3eqtrd fveq2d ) AIDHUAUAEIUBRZSKTRZIUBRZDTRZFUAZTRWMJSU
      CRZFUAZTRACDEFGHIKMADWNIUDZUBRZSUCRZJTRZUJDXCUEANUFAIJKQAIOUKZPUGUHOUIAWQ
      WSWMTAWPWRFAWPWOXCTRZWRWPXEUEADXCWOTNULUFAXEWOXBTRZJTRZUMSUCRZJTRZWRAXGXE
      AWOXBJAWNIASKAUNZAKAKVEUOZKWHUOQKUPUQZURZUSZOUTZAXASAWNWTXNASKXJXMSVAVBAV
      CUFZAVAKAVAKAVDZAVAUMKXQAVFAKXLVGVAUMVHVIAVJUFAXKUMKVKVIQKVLUQVMVNVRVOZAI
      XDVPVQZXJXPVSAJPURZVTWAAXFXHJTAXFWOXATRZSUCRZXHAYBXFAWOXASXOXSXJXPWBWAAYA
      UMSUCAYAWOUMWOUCRZTRUMAXAYCWOTAWNIXNXRXDWCWDAWOXOAWNIXNXRXDWEWFWIWGWIWGAW
      RXIAJSXTXJXPWJWAWKWIWLWDWI $.
  $}

  ${
    $d A n y $.  $d C n y $.  $d J n $.  $d M x $.  $d N n y $.  $d T n y $.
    $d n ph y $.
    knoppndvlem8.t $e |- T = ( x e. RR |->
                            ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) ) $.
    knoppndvlem8.f $e |- F = ( y e. RR |-> ( n e. NN0 |->
            ( ( C ^ n ) x. ( T ` ( ( ( 2 x. N ) ^ n ) x. y ) ) ) ) ) $.
    knoppndvlem8.a $e |- A = ( ( ( ( 2 x. N ) ^ -u J ) / 2 ) x. M ) $.
    knoppndvlem8.c $e |- ( ph -> C e. ( -u 1 (,) 1 ) ) $.
    knoppndvlem8.j $e |- ( ph -> J e. NN0 ) $.
    knoppndvlem8.m $e |- ( ph -> M e. ZZ ) $.
    knoppndvlem8.n $e |- ( ph -> N e. NN ) $.
    knoppndvlem8.1 $e |- ( ph -> 2 || M ) $.
    $( Lemma for ~ knoppndv .  (Contributed by Asger C. Ipsen, 15-Jun-2021.)
       (Revised by Asger C. Ipsen, 5-Jul-2021.) $)
    knoppndvlem8 $p |- ( ph -> ( ( F ` A ) ` J ) = 0 ) $=
      ( c2 cfv cexp co cdiv cmul cc0 knoppndvlem7 cdvds wbr cz wcel wne w3a a1i
      wb 2z 2ne0 3jca dvdsval2 syl mpbid dnizeq0 oveq2d cr cabs c1 knoppndvlem3
      clt simpld recnd expcld mul01d 3eqtrd ) AIDHUAUAEIUBUCZJTUDUCZFUAZUEUCVNU
      FUEUCUFABCDEFGHIJKLMNPQRUGAVPUFVNUEABVOFLATJUHUIZVOUJUKZSATUJUKZTUFULZJUJ
      UKZUMVQVRUOAVSVTWAVSAUPUNVTAUQUNQURTJUSUTVAVBVCAVNAEIAEAEVDUKEVEUAVFVHUIA
      EOVGVIVJPVKVLVM $.
  $}

  ${
    $d A n y $.  $d C n y $.  $d J n $.  $d M m $.  $d N n y $.  $d T m $.
    $d T n y $.  $d ph m $.  $d m x $.  $d ph n y $.
    knoppndvlem9.t $e |- T = ( x e. RR |->
                            ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) ) $.
    knoppndvlem9.f $e |- F = ( y e. RR |-> ( n e. NN0 |->
            ( ( C ^ n ) x. ( T ` ( ( ( 2 x. N ) ^ n ) x. y ) ) ) ) ) $.
    knoppndvlem9.a $e |- A = ( ( ( ( 2 x. N ) ^ -u J ) / 2 ) x. M ) $.
    knoppndvlem9.c $e |- ( ph -> C e. ( -u 1 (,) 1 ) ) $.
    knoppndvlem9.j $e |- ( ph -> J e. NN0 ) $.
    knoppndvlem9.m $e |- ( ph -> M e. ZZ ) $.
    knoppndvlem9.n $e |- ( ph -> N e. NN ) $.
    knoppndvlem9.1 $e |- ( ph -> -. 2 || M ) $.
    $( Lemma for ~ knoppndv .  (Contributed by Asger C. Ipsen, 15-Jun-2021.)
       (Revised by Asger C. Ipsen, 5-Jul-2021.) $)
    knoppndvlem9 $p |- ( ph -> ( ( F ` A ) ` J ) = ( ( C ^ J ) / 2 ) ) $=
      ( c2 vm cfv cexp co cdiv cmul c1 knoppndvlem7 cv caddc wceq cz cdvds wrex
      wbr wn wcel wb odd2np1 mpbid wa eqcom biimpi oveq1d adantl 2cnd cc mulcld
      syl zcn 1cnd cc0 wne 2ne0 a1i divdird divcan3d eqtrd fveq2d dnizphlfeqhlf
      adantrr id rexlimddv oveq2d cr cabs clt knoppndvlem3 simpld expcld div12d
      recnd divcld mullidd 3eqtrd ) AIDHUBUBEIUCUDZJTUEUDZFUBZUFUDWPUGTUEUDZUFU
      DZWPTUEUDZABCDEFGHIJKLMNPQRUHAWRWSWPUFATUAUIZUFUDZUGUJUDZJUKZWRWSUKUAULAT
      JUMUOUPZXEUAULUNZSAJULUQXFXGURQUAJUSVIUTAXBULUQZXEVAZVAZWRXBWSUJUDZFUBZWS
      XJWQXKFXJWQXDTUEUDZXKXIWQXMUKZAXEXNXHXEJXDTUEXEJXDUKXDJVBVCVDVEVEAXHXMXKU
      KXEAXHVAZXMXCTUEUDZWSUJUDXKXOXCUGTXOTXBXOVFZXHXBVGUQAXBVJVEZVHXOVKXQTVLVM
      ZXOVNVOZVPXOXPXBWSUJXOXBTXRXQXTVQVDVRWAVRVSAXHXLWSUKZXEXHYAAXHBXBFLXHWBVT
      VEWAVRWCWDAWTUGXAUFUDXAAWPUGTAEIAEAEWEUQEWFUBUGWGUOAEOWHWIWLPWJZAVKAVFZXS
      AVNVOZWKAXAAWPTYBYCYDWMWNVRWO $.
  $}

  ${
    $d A n y $.  $d A x $.  $d B n y $.  $d B x $.  $d C n y $.  $d J n $.
    $d J x $.  $d M n y $.  $d M x $.  $d N n y $.  $d N x $.  $d T n y $.
    $d ph n y $.
    knoppndvlem10.t $e |- T = ( x e. RR |->
                            ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) ) $.
    knoppndvlem10.f $e |- F = ( y e. RR |-> ( n e. NN0 |->
            ( ( C ^ n ) x. ( T ` ( ( ( 2 x. N ) ^ n ) x. y ) ) ) ) ) $.
    knoppndvlem10.a $e |- A = ( ( ( ( 2 x. N ) ^ -u J ) / 2 ) x. M ) $.
    knoppndvlem10.b $e |- B = ( ( ( ( 2 x. N ) ^ -u J ) / 2 ) x. ( M + 1 ) ) $.
    knoppndvlem10.c $e |- ( ph -> C e. ( -u 1 (,) 1 ) ) $.
    knoppndvlem10.j $e |- ( ph -> J e. NN0 ) $.
    knoppndvlem10.m $e |- ( ph -> M e. ZZ ) $.
    knoppndvlem10.n $e |- ( ph -> N e. NN ) $.
    $( Lemma for ~ knoppndv .  (Contributed by Asger C. Ipsen, 15-Jun-2021.)
       (Revised by Asger C. Ipsen, 5-Jul-2021.) $)
    knoppndvlem10 $p |- ( ph ->
                  ( abs ` ( ( ( F ` B ) ` J ) - ( ( F ` A ) ` J ) ) )
                = ( ( ( abs ` C ) ^ J ) / 2 ) ) $=
      ( cfv cmin co cabs cexp c2 cdiv cdvds wbr wceq wa c1 caddc cneg cioo wcel
      cc0 adantr cn0 cz peano2zd cn wn notnot adantl oddp1even syl knoppndvlem9
      wb mtbid notnotrd knoppndvlem8 oveq12d clt knoppndvlem3 simpld recnd 2cnd
      expcld wne 2ne0 a1i divcld subid1d eqtrd fveq2d cmul knoppndvlem1 eqeltrd
      cr nn0zd knoppcnlem3 abssubd simpr pm2.61dan absdivd absexpd cle 0le2 2re
      mpbid absidi ax-mp ) AJEIUAUAZJDIUAUAZUBUCZUDUAZFJUEUCZUFUGUCZUDUAZFUDUAZ
      JUEUCZUFUGUCZAUFKUHUIZXGXJUJAXNUKZXFXIUDXOXFXIUQUBUCZXIXOXDXIXEUQUBXOBCEF
      GHIJKULUMUCZLMNPAFULUNULUOUCUPZXNQURZAJUSUPZXNRURZAXQUTUPZXNAKSVAZURALVBU
      PZXNTURZXOXNVCZUFXQUHUIZXNYFVCAXNVDVEZXOKUTUPZYFYGVIZAYIXNSURZKVFZVGVJVHX
      OBCDFGHIJKLMNOXSYAYKYEXOXNYHVKVLVMAXPXIUJZXNAXIAXHUFAFJAFAFWJUPXKULVNUIAF
      QVOVPZVQZRVSZAVRZUFUQVTAWAWBZWCWDZURWEWFAYFUKZXGXEXDUBUCZUDUAZXJAXGUUBUJY
      FAXDXEAXDABCEFGHIJLMNTYNAEUFLWGUCJUNUEUCUFUGUCZXQWGUCZWJEUUDUJAPWBAJXQLTA
      JRWKZYCWHWIRWLVQAXEABCDFGHIJLMNTYNADUUCKWGUCZWJDUUFUJAOWBAJKLTUUESWHWIRWL
      VQWMURYTUUAXIUDYTUUAXPXIYTXEXIXDUQUBYTBCDFGHIJKLMNOAXRYFQURZAXTYFRURZAYIY
      FSURZAYDYFTURZAYFWNZVHYTBCEFGHIJXQLMNPUUGUUHAYBYFYCURUUJYTYFYGUUKYTYIYJUU
      IYLVGXAVLVMAYMYFYSURWEWFWEWOAXJXHUDUAZUFUDUAZUGUCXMAXHUFYPYQYRWPAUULXLUUM
      UFUGAFJYORWQUUMUFUJZAUQUFWRUIUUNWSUFWTXBXCWBVMWEWE $.
  $}

  ${
    $d A i n y $.  $d A i x $.  $d B i n y $.  $d B i x $.  $d C n y $.
    $d J i n y $.  $d N n y $.  $d N x $.  $d T n y $.  $d ph i n y $.
    knoppndvlem11.t $e |- T = ( x e. RR |->
                            ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) ) $.
    knoppndvlem11.f $e |- F = ( y e. RR |-> ( n e. NN0 |->
            ( ( C ^ n ) x. ( T ` ( ( ( 2 x. N ) ^ n ) x. y ) ) ) ) ) $.
    knoppndvlem11.a $e |- ( ph -> A e. RR ) $.
    knoppndvlem11.b $e |- ( ph -> B e. RR ) $.
    knoppndvlem11.c $e |- ( ph -> C e. ( -u 1 (,) 1 ) ) $.
    knoppndvlem11.j $e |- ( ph -> J e. NN0 ) $.
    knoppndvlem11.n $e |- ( ph -> N e. NN ) $.
    $( Lemma for ~ knoppndv .  (Contributed by Asger C. Ipsen, 28-Jun-2021.)
       (Revised by Asger C. Ipsen, 5-Jul-2021.) $)
    knoppndvlem11 $p |- ( ph ->
      ( abs ` ( sum_ i e. ( 0 ... ( J - 1 ) ) ( ( F ` B ) ` i )
              - sum_ i e. ( 0 ... ( J - 1 ) ) ( ( F ` A ) ` i ) ) )
         <_ ( ( abs ` ( B - A ) ) x. sum_ i e. ( 0 ... ( J - 1 ) )
                                ( ( ( 2 x. N ) x. ( abs ` C ) ) ^ i ) ) ) $=
      ( co cc0 c1 cmin cfz cv cfv csu cabs c2 cmul cexp fzfid wcel wa cn adantr
      cle cr clt wbr knoppndvlem3 simpld cn0 elfznn0 adantl knoppcnlem3 fsumsub
      recnd eqcomd fveq2d subcld fsumcl fsumrecl resubcld 2re a1i nnre remulcld
      abscld syl reexpcld fsumabs knoppcnlem1 oveq12d dnicld2 subdid absmuld cc
      eqtrd absexpd oveq1d absge0d expge0d dnibnd lemul2ad wceq 0le2 ax-mp 0red
      absidi 1red 0le1 nnge1 letrd absidd oveq2d mulassd mulcld mulcomd mulexpd
      3eqtrd breqtrd eqbrtrd fsumle eqeltrrd fsummulc2 ) AUAKUBUCTZUDTZHUEZEJUF
      UFZHUGXRXSDJUFUFZHUGUCTZUHUFXRXTYAUCTZHUGZUHUFZEDUCTZUHUFZXRUILUJTZFUHUFZ
      UJTZXSUKTZHUGZUJTZUQAYBYDUHAYDYBAXRXTYAHAUAXQULZAXSXRUMZUNZXTYPBCEFGIJXSL
      MNALUOUMZYOSUPZAFURUMZYOAYSYIUBUSUTAFQVAVBZUPZAEURUMYOPUPZYOXSVCUMAXSXQVD
      VEZVFVHZYPYAYPBCDFGIJXSLMNYRUUAADURUMYOOUPZUUCVFVHZVGVIVJAYEXRYCUHUFZHUGZ
      YMAYDAXRYCHYNYPXTYAUUDUUFVKZVLVSAXRUUGHYNYPYCUUIVSZVMAYGYLAYFAYFAEDPOVNVH
      ZVSZAXRYKHYNYPYJXSAYJURUMYOAYHYIAUILUIURUMAVOVPZAYQLURUMSLVQVTZVRZAFAFYTV
      HZVSZVRUPUUCWAZVMVRAXRYCHYNUUIWBAUUHXRYGYKUJTZHUGZYMUQAXRUUGUUSHYNUUJYPYG
      YKAYGURUMYOUULUPZUURVRYPUUGYIXSUKTZYHXSUKTZEUJTZGUFZUVCDUJTZGUFZUCTZUHUFZ
      UJTZUUSUQYPUUGFXSUKTZUVHUJTZUHUFZUVJYPYCUVLUHYPYCUVKUVEUJTZUVKUVGUJTZUCTZ
      UVLYPXTUVNYAUVOUCYPCEFGIJXSLNUUBUUCWCYPCDFGIJXSLNUUEUUCWCWDYPUVLUVPYPUVKU
      VEUVGYPUVKYPFXSUUAUUCWAVHZYPUVEYPBUVDGMYPUVCEYPYHXSAYHURUMYOUUOUPZUUCWAZU
      UBVRZWEVHZYPUVGYPBUVFGMYPUVCDUVSUUEVRZWEVHZWFVIWIVJYPUVMUVKUHUFZUVIUJTUVJ
      YPUVKUVHUVQYPUVEUVGUWAUWCVKZWGYPUWDUVBUVIUJYPFXSAFWHUMYOUUPUPZUUCWJWKWIWI
      YPUVJUVBUVDUVFUCTZUHUFZUJTZUUSUQYPUVIUWHUVBYPUVHUWEVSYPUWGYPUWGYPUVDUVFUV
      TUWBVNVHVSYPYIXSAYIURUMYOUUQUPZUUCWAZYPYIXSUWJUUCYPFUWFWLWMYPBUVFUVDGMUWB
      UVTWNWOYPUWIUVBUVCYGUJTZUJTZUUSYPUWHUWLUVBUJYPUWHUVCYFUJTZUHUFZUWLYPUWGUW
      NUHYPUWNUWGYPUVCEDYPUVCUVSVHZYPEUUBVHYPDUUEVHWFVIVJYPUWOUVCUHUFZYGUJTUWLY
      PUVCYFUWPAYFWHUMYOUUKUPWGYPUWQUVCYGUJYPUWQYHUHUFZXSUKTZUVCYPYHXSYPYHUVRVH
      ZUUCWJAUWSUVCWPYOAUWRYHXSUKAUWRUIUHUFZLUHUFZUJTYHAUILAUIUUMVHALUUNVHWGAUX
      AUIUXBLUJUXAUIWPZAUAUIUQUTUXCWQUIVOWTWRVPALUUNAUAUBLAWSAXAUUNUAUBUQUTAXBV
      PAYQUBLUQUTSLXCVTXDXEWDWIWKUPWIWKWIWIXFYPUWMUVBUVCUJTZYGUJTZYGUXDUJTUUSYP
      UXEUWMYPUVBUVCYGYPUVBUWKVHZUWPYPYGUVAVHZXGVIYPUXDYGYPUVBUVCUXFUWPXHZUXGXI
      YPUXDYKYGUJYPUXDUVCUVBUJTZYKYPUVBUVCUXFUWPXIYPYKUXIYPYHYIXSUWTYPYIUWJVHUU
      CXJVIWIZXFXKWIXLXMXNAYMUUTAXRYKYGHYNAYGUULVHYPUXDYKWHUXJUXHXOXPVIXLXDXM
      $.
  $}

  ${
    knoppndvlem12.c $e |- ( ph -> C e. ( -u 1 (,) 1 ) ) $.
    knoppndvlem12.n $e |- ( ph -> N e. NN ) $.
    knoppndvlem12.1 $e |- ( ph -> 1 < ( N x. ( abs ` C ) ) ) $.
    $( Lemma for ~ knoppndv .  (Contributed by Asger C. Ipsen, 29-Jun-2021.)
       (Revised by Asger C. Ipsen, 5-Jul-2021.) $)
    knoppndvlem12 $p |- ( ph -> ( ( ( 2 x. N ) x. ( abs ` C ) ) =/= 1
      /\ 1 < ( ( ( 2 x. N ) x. ( abs ` C ) ) - 1 ) ) ) $=
      ( c2 cmul co c1 clt wbr cr wcel a1i syl remulcld recnd wceq eqbrtrd wa cn
      cabs cfv wne cmin 1red 2re nnre knoppndvlem3 simpld abscld 1lt2 2t1e2 crp
      eqcomi 2rp ltmul2dd mulassd eqcomd breqtrd lttrd jca ltne caddc ltaddsubd
      1p1e2 mpbid ) AGCHIZBUCUDZHIZJUEZJVKJUFIKLZAJMNZJVKKLZUAVLAVNVOAUGZAJGVKV
      PGMNAUHOZAVIVJAGCVQACUBNCMNECUIPZQABABABMNVJJKLABDUJUKRULZQZJGKLAUMOAGGCV
      JHIZHIZVKKAGGJHIZWBKGWCSAWCGUNUPOAJWAGVPACVJVRVSQGUONAUQOFURTAVKWBAGCVJAG
      VQRACVRRAVJVSRUSUTVAZVBVCJVKVDPAJJVEIZVKKLVMAWEGVKKWEGSAVGOWDTAJJVKVPVPVT
      VFVHVC $.
  $}

  ${
    knoppndvlem13.c $e |- ( ph -> C e. ( -u 1 (,) 1 ) ) $.
    knoppndvlem13.n $e |- ( ph -> N e. NN ) $.
    knoppndvlem13.1 $e |- ( ph -> 1 < ( N x. ( abs ` C ) ) ) $.
    $( Lemma for ~ knoppndv .  (Contributed by Asger C. Ipsen, 1-Jul-2021.)
       (Revised by Asger C. Ipsen, 5-Jul-2021.) $)
    knoppndvlem13 $p |- ( ph -> C =/= 0 ) $=
      ( cc0 wceq c1 cabs cfv cmul co clt wbr adantr wa wn 0lt1 wcel 0re ltnsymi
      1re ax-mp a1i id abs00bd oveq2d adantl cc cn nncn syl mul01d eqtrd eqcomd
      breq2d mtbid pm2.65da neqned ) ABGABGHZICBJKZLMZNOZAVDVAFPAVAQZIGNOZVDVFR
      ZVEGINOVGSGIUAUCUBUDUEVEGVCINVEVCGVEVCCGLMZGVAVCVHHAVAVBGCLVABVAUFUGUHUIV
      ECACUJTZVAACUKTVIECULUMPUNUOUPUQURUSUT $.
  $}

  ${
    $d A i n y $.  $d A i x $.  $d B i n y $.  $d B i x $.  $d C i n y $.
    $d J i n y $.  $d N i n y $.  $d N i x $.  $d T n y $.  $d ph i n y $.
    knoppndvlem14.t $e |- T = ( x e. RR |->
                            ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) ) $.
    knoppndvlem14.f $e |- F = ( y e. RR |-> ( n e. NN0 |->
            ( ( C ^ n ) x. ( T ` ( ( ( 2 x. N ) ^ n ) x. y ) ) ) ) ) $.
    knoppndvlem14.a $e |- A = ( ( ( ( 2 x. N ) ^ -u J ) / 2 ) x. M ) $.
    knoppndvlem14.b $e |- B = ( ( ( ( 2 x. N ) ^ -u J ) / 2 ) x. ( M + 1 ) ) $.
    knoppndvlem14.c $e |- ( ph -> C e. ( -u 1 (,) 1 ) ) $.
    knoppndvlem14.j $e |- ( ph -> J e. NN0 ) $.
    knoppndvlem14.m $e |- ( ph -> M e. ZZ ) $.
    knoppndvlem14.n $e |- ( ph -> N e. NN ) $.
    knoppndvlem14.1 $e |- ( ph -> 1 < ( N x. ( abs ` C ) ) ) $.
    $( Lemma for ~ knoppndv .  (Contributed by Asger C. Ipsen, 1-Jul-2021.)
       (Revised by Asger C. Ipsen, 7-Jul-2021.) $)
    knoppndvlem14 $p |- ( ph ->
      ( abs ` ( sum_ i e. ( 0 ... ( J - 1 ) ) ( ( F ` B ) ` i )
              - sum_ i e. ( 0 ... ( J - 1 ) ) ( ( F ` A ) ` i ) ) )
      <_ ( ( ( ( abs ` C ) ^ J ) / 2 ) x.
          ( 1 / ( ( ( 2 x. N ) x. ( abs ` C ) ) - 1 ) ) ) ) $=
      ( cc0 c1 cmin co cfz cv cfv csu cabs c2 cmul cexp cdiv cneg caddc cr wceq
      a1i nn0zd peano2zd knoppndvlem1 eqeltrd clt wbr knoppndvlem3 knoppndvlem5
      wcel simpld resubcld recnd abscld fzfid wa 2re cn syl remulcld adantr cn0
      nnre elfznn0 reexpcld fsumrecl 2ne0 redivcld 1red 0red 0lt1 knoppndvlem12
      adantl wne lttrd jca ltne knoppndvlem11 cle oveq12d nnge1 ltletrd mulne0d
      simprd znegcld reexpclzd zcnd subdid eqcomd pncan2d oveq2d mulridd 3eqtrd
      1cnd eqtrd fveq2d absdivd cc w3a mulcld 3jca absexpz absmuld pm3.2i absid
      0le2 ax-mp ltled absidd oveq1d geoser expcld necomd div2subd eqeltrrd crp
      cz 2rp rpgt0d mulgt0d mulassd expgt0 divge0d elrpd lem1d lediv1dd divrecd
      lemul2ad div23d knoppndvlem13 absne0d mulexpz jca32 expaddz nn0cnd negidd
      addcomd exp0d mullidd breqtrd eqbrtrd letrd ) AUCKUDUEUFZUGUFZHUHZEJUIUIH
      UJZUVCUVDDJUIUIHUJZUEUFZUKUIEDUEUFZUKUIZUVCULMUMUFZFUKUIZUMUFZUVDUNUFZHUJ
      ZUMUFZUVKKUNUFZULUOUFZUDUVLUDUEUFZUOUFZUMUFZAUVGAUVGAUVEUVFABCEFGHIJUVBMN
      OAEUVJKUPZUNUFZULUOUFZLUDUQUFZUMUFZUREUWEUSAQUTZAKUWDMUAAKSVAZALTVBZVCVDZ
      AFURVIUVKUDVEVFAFRVGVJZUAVHABCDFGHIJUVBMNOADUWCLUMUFZURDUWKUSAPUTZAKLMUAU
      WGTVCVDZUWJUAVHVKVLVMAUVIUVNAUVHAUVHAEDUWIUWMVKVLVMAUVCUVMHAUCUVBVNAUVDUV
      CVIZVOUVLUVDAUVLURVIUWNAUVJUVKAULMULURVIZAVPUTZAMVQVIZMURVIUAMWBVRZVSZAFA
      FUWJVLZVMZVSZVTUWNUVDWAVIAUVDUVBWCWLWDWEZVSAUVQUVSAUVPULAUVKKUXASWDZUWPUL
      UCWMAWFUTZWGAUDUVRAWHZAUVLUDUXBUXFVKZAUCURVIZUCUVRVEVFZVOUVRUCWMAUXHUXIAW
      IZAUCUDUVRUXJUXFUXGUCUDVEVFAWJUTZAUVLUDWMZUDUVRVEVFZAFMRUAUBWKZXCWNZWOUCU
      VRWPVRZWGZVSABCDEFGHIJKMNOUWMUWIRSUAWQAUVOUWCUVLKUNUFZUDUEUFZUVRUOUFZUMUF
      ZUVTWRAUVIUWCUVNUXTUMAUVIUWCUKUIZUWCAUVHUWCUKAUVHUWEUWKUEUFZUWCAEUWEDUWKU
      EUWFUWLWSAUYCUWCUWDLUEUFZUMUFZUWCUDUMUFUWCAUYEUYCAUWCUWDLAUWCAUWBULAUVJUW
      AUWSAULMAULUWPVLZAMUWRVLZUXEAUXHUCMVEVFZVOMUCWMAUXHUYHUXJAUCUDMUXJUXFUWRU
      XKAUWQUDMWRVFUAMWTVRXAZWOUCMWPVRXBZAKUWGXDZXEZUWPUXEWGZVLZAUWDUWHXFALTXFZ
      XGXHAUYDUDUWCUMALUDUYOAXMZXIXJAUWCUYNXKXLXNXOAUYBUWBUKUIZULUKUIZUOUFUWCAU
      WBULAUWBUYLVLZUYFUXEXPAUYQUWBUYRULUOAUYQUVJUKUIZUWAUNUFZUWBAUVJXQVIZUVJUC
      WMZUWAYPVIZXRUYQVUAUSAVUBVUCVUDAULMUYFUYGXSZUYJUYKXTUVJUWAYAVRAUYTUVJUWAU
      NAUYTUYRMUKUIZUMUFUVJAULMUYFUYGYBAUYRULVUFMUMUYRULUSZAUWOUCULWRVFZVOVUGUW
      OVUHVPYEYCULYDYFUTZAMUWRAUCMUXJUWRUYIYGYHWSXNYIXNVUIWSXNXNAUVNUDUXRUEUFUD
      UVLUEUFUOUFUXTAUVLHKAUVLUXBVLZAUXLUXMUXNVJZSYJAUDUXRUDUVLUYPAUVLKVUJSYKZU
      YPVUJAUVLUDVUKYLYMXNZWSAUYAUWCUXRUVRUOUFZUMUFZUVTWRAUXTVUNUWCAUVNUXTURVUM
      UXCYNAUXRUVRAUVLKUXBSWDZUXGUXPWGUYMAUWBULUYLULYOVIAYQUTZAUCUWBUXJUYLAUVJU
      RVIZVUDUCUVJVEVFZXRUCUWBVEVFAVURVUDVUSUWSUYKAULMUWPUWRAULVUQYRUYIYSXTUVJU
      WAUUAVRYGUUBAUXSUXRUVRAUXRUDVUPUXFVKVUPAUVRUXGUXOUUCAUXRVUPUUDUUEUUGAVUOU
      WCUXRUVSUMUFZUMUFZUWCUXRUMUFZUVSUMUFZUVTAVUNVUTUWCUMAUXRUVRVULAUVRUXGVLUX
      PUUFXJAVVCVVAAUWCUXRUVSUYNVULAUVSUXQVLYTXHAVVBUVQUVSUMAVVBUWBUXRUMUFZULUO
      UFZUVQAVVEVVBAUWBUXRULUYSVULUYFUXEUUHXHAVVDUVPULUOAVVDUWBUVJKUNUFZUVPUMUF
      ZUMUFZUWBVVFUMUFZUVPUMUFZUVPAUXRVVGUWBUMAVUBVUCVOZUVKXQVIZUVKUCWMZVOZKYPV
      IZXRUXRVVGUSAVVKVVNVVOAVUBVUCVUEUYJWOZAVVLVVMAUVKUXAVLAFUWTAFMRUAUBUUIUUJ
      WOUWGXTUVJUVKKUUKVRXJAVVJVVHAUWBVVFUVPUYSAUVJKVUESYKAUVPUXDVLZYTXHAVVJUDU
      VPUMUFUVPAVVIUDUVPUMAVVIUVJUWAKUQUFZUNUFZUVJUCUNUFUDAVVSVVIAVVKVUDVVOVOVO
      VVSVVIUSAVVKVUDVVOVVPUYKUWGUULUVJUWAKUUMVRXHAVVRUCUVJUNAVVRKUWAUQUFUCAUWA
      KAUWAUYKXFAKSUUNZUUPAKVVTUUOXNXJAUVJVUEUUQXLYIAUVPVVQUURXNXLYIXNYIXLUUSUU
      TUVA $.
  $}

  ${
    $d A i n w y $.  $d A i w x $.  $d B i n w y $.  $d B i w x $.
    $d C i n y $.  $d F i w $.  $d J i n y $.  $d J i x $.  $d M n y $.
    $d M x $.  $d N i n y $.  $d N i x $.  $d T n y $.  $d ph i n w y $.
    knoppndvlem15.t $e |- T = ( x e. RR |->
                            ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) ) $.
    knoppndvlem15.f $e |- F = ( y e. RR |-> ( n e. NN0 |->
            ( ( C ^ n ) x. ( T ` ( ( ( 2 x. N ) ^ n ) x. y ) ) ) ) ) $.
    knoppndvlem15.w $e |- W =
                        ( w e. RR |-> sum_ i e. NN0 ( ( F ` w ) ` i ) ) $.
    knoppndvlem15.a $e |- A = ( ( ( ( 2 x. N ) ^ -u J ) / 2 ) x. M ) $.
    knoppndvlem15.b $e |- B = ( ( ( ( 2 x. N ) ^ -u J ) / 2 ) x. ( M + 1 ) ) $.
    knoppndvlem15.c $e |- ( ph -> C e. ( -u 1 (,) 1 ) ) $.
    knoppndvlem15.j $e |- ( ph -> J e. NN0 ) $.
    knoppndvlem15.m $e |- ( ph -> M e. ZZ ) $.
    knoppndvlem15.n $e |- ( ph -> N e. NN ) $.
    knoppndvlem15.1 $e |- ( ph -> 1 < ( N x. ( abs ` C ) ) ) $.
    $( Lemma for ~ knoppndv .  (Contributed by Asger C. Ipsen, 6-Jul-2021.) $)
    knoppndvlem15 $p |- ( ph ->
      ( ( ( ( abs ` C ) ^ J ) / 2 ) x.
          ( 1 - ( 1 / ( ( ( 2 x. N ) x. ( abs ` C ) ) - 1 ) ) ) )
        <_ ( abs ` ( ( W ` B ) - ( W ` A ) ) ) ) $=
      ( cabs cfv cexp co c2 cdiv c1 cmul cmin cc0 cfz csu cle wcel knoppndvlem3
      cv cr clt wbr simpld recnd abscld reexpcld 2re a1i wne 2ne0 redivcld 1red
      nnred remulcld resubcld wa 0red knoppndvlem12 simprd lttrd jca gt0ne0 syl
      0lt1 cneg wceq nn0zd knoppndvlem1 knoppcnlem3 caddc peano2zd knoppndvlem5
      eqeltrd subcld remulcl resubcl 1cnd subdid mulridd oveq1d eqbrtrd abssubd
      leidd knoppndvlem10 eqtrd eqcomd breqtrd knoppndvlem14 letrd knoppndvlem6
      le2subd abs2difd cn0 cuz elnn0uz sylib adantr elfznn0 adantl fveq2 fsumm1
      cn oveq12d subadd4d fveq2d ) AGUFUGZLUHUIZUJUKUIZULULUJNUMUIZYHUMUIZULUNU
      IZUKUIZUNUIZUMUIZUOLULUNUIZUPUIZIVAZFKUGZUGZIUQZYRYSEKUGZUGZIUQZUNUIZLUUC
      UGZLYTUGZUNUIZUNUIZUFUGZFOUGZEOUGZUNUIZUFUGZURAYPUUIUUFUNUIZUFUGZUUKURAYP
      UUIUFUGZUUFUFUGZUNUIZUUQAYJYOAYIUJAYHLAGAGAGVBUSZYHULVCVDAGUAUTVEZVFVGZUB
      VHUJVBUSAVIVJZUJUOVKAVLVJVMZAULYNAVNZAULYMUVFAYLULAYKYHAUJNUVDANUDVOVPUVC
      VPUVFVQZAYMVBUSZUOYMVCVDZVRYMUOVKAUVHUVIUVGAUOULYMAVSUVFUVGUOULVCVDAWFVJA
      YLULVKULYMVCVDAGNUAUDUEVTWAWBWCYMWDWEVMZVQVPZAUURUUSAUUIAUUGUUHAUUGABCEGH
      JKLNPQUDUVBAEYKLWGUHUIUJUKUIZMUMUIZVBEUVMWHASVJALMNUDALUBWIZUCWJWOZUBWKVF
      ZAUUHABCFGHJKLNPQUDUVBAFUVLMULWLUIZUMUIZVBFUVRWHATVJALUVQNUDUVNAMUCWMZWJW
      OZUBWKVFZWPZVGZAUUFAUUBUUEAUUBABCFGHIJKYQNPQUVTUVBUDWNVFZAUUEABCEGHIJKYQN
      PQUVOUVBUDWNVFZWPZVGZVQZAUUPAUUIUUFUWBUWFWPVGAYPYJYJYNUMUIZUNUIZUUTUVKAYJ
      VBUSZUWIVBUSZVRUWJVBUSAUWKUWLUVEAUWKYNVBUSZVRUWLAUWKUWMUVEUVJWCYJYNWQWEWC
      YJUWIWRWEZUWHAYPYJULUMUIZUWIUNUIZUWJURAYJULYNAYJUVEVFZAWSAYNUVJVFWTAUWPUW
      JUWJURAUWOYJUWIUNAYJUWQXAXBAUWJUWNXEXCXCAYJUUSUURUWIUVEUWGUWCAYJYNUVEUVJV
      PAYJYJUURURAYJUVEXEAUURYJAUURUUHUUGUNUIUFUGYJAUUGUUHUVPUWAXDABCEFGHJKLMNP
      QSTUAUBUCUDXFXGXHXIABCEFGHIJKLMNPQSTUAUBUCUDUEXJXMXKAUUIUUFUWBUWFXNXKAUUI
      UUFUWBUWFXDXIAUUOUUKAUUNUUJUFAUUNUUBUUHWLUIZUUEUUGWLUIZUNUIZUUJAUULUWRUUM
      UWSUNAUULUOLUPUIZUUAIUQUWRABCDFGHIJKLUVQNOPQRTUAUBUVSUDXLAUUAUUHIUOLALXOU
      SLUOXPUGUSUBLXQXRZAYSUXAUSZVRZUUAUXDBCFGHJKYSNPQANYDUSUXCUDXSZAUVAUXCUVBX
      SZAFVBUSUXCUVTXSUXCYSXOUSAYSLXTYAZWKVFYSLYTYBYCXGAUUMUXAUUDIUQUWSABCDEGHI
      JKLMNOPQRSUAUBUCUDXLAUUDUUGIUOLUXBUXDUUDUXDBCEGHJKYSNPQUXEUXFAEVBUSUXCUVO
      XSUXGWKVFYSLUUCYBYCXGYEAUUJUWTAUUBUUEUUGUUHUWDUWEUVPUWAYFXHXGYGXHXI $.
  $}

  ${
    knoppndvlem16.a $e |- A = ( ( ( ( 2 x. N ) ^ -u J ) / 2 ) x. M ) $.
    knoppndvlem16.b $e |- B = ( ( ( ( 2 x. N ) ^ -u J ) / 2 ) x. ( M + 1 ) ) $.
    knoppndvlem16.j $e |- ( ph -> J e. NN0 ) $.
    knoppndvlem16.m $e |- ( ph -> M e. ZZ ) $.
    knoppndvlem16.n $e |- ( ph -> N e. NN ) $.
    $( Lemma for ~ knoppndv .  (Contributed by Asger C. Ipsen, 19-Jul-2021.) $)
    knoppndvlem16 $p |- ( ph -> ( B - A ) = ( ( ( 2 x. N ) ^ -u J ) / 2 ) ) $=
      ( cmin co c2 cmul cneg cexp c1 wceq a1i cdiv caddc oveq12d 2cnd nncnd cc0
      mulcld wne 2ne0 nnne0d mulne0d znegcld expclzd mulne0bad divcld zcnd 1cnd
      nn0zd addcld subdid eqcomd pncan2d oveq2d mulridd eqtrd 3eqtrd ) ACBLMNFO
      MZDPZQMZNUAMZERUBMZOMZVJEOMZLMZVJVKELMZOMZVJACVLBVMLCVLSAHTBVMSAGTUCAVPVN
      AVJVKEAVINAVGVHANFAUDZAFKUEZUGANFVQVRNUFUHAUITAFKUJUKZADADIURULUMVQANFVQV
      RVSUNUOZAERAEJUPZAUQZUSWAUTVAAVPVJROMVJAVORVJOAERWAWBVBVCAVJVTVDVEVF $.
  $}

  ${
    $d A i n w y $.  $d A i w x $.  $d B i n w y $.  $d B i w x $.
    $d C i n y $.  $d F i w $.  $d J i n y $.  $d J i x $.  $d M n y $.
    $d M x $.  $d N i n y $.  $d N i x $.  $d T n y $.  $d ph i n w y $.
    knoppndvlem17.t $e |- T = ( x e. RR |->
                            ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) ) $.
    knoppndvlem17.f $e |- F = ( y e. RR |-> ( n e. NN0 |->
            ( ( C ^ n ) x. ( T ` ( ( ( 2 x. N ) ^ n ) x. y ) ) ) ) ) $.
    knoppndvlem17.w $e |- W =
                        ( w e. RR |-> sum_ i e. NN0 ( ( F ` w ) ` i ) ) $.
    knoppndvlem17.a $e |- A = ( ( ( ( 2 x. N ) ^ -u J ) / 2 ) x. M ) $.
    knoppndvlem17.b $e |- B = ( ( ( ( 2 x. N ) ^ -u J ) / 2 ) x. ( M + 1 ) ) $.
    knoppndvlem17.c $e |- ( ph -> C e. ( -u 1 (,) 1 ) ) $.
    knoppndvlem17.j $e |- ( ph -> J e. NN0 ) $.
    knoppndvlem17.m $e |- ( ph -> M e. ZZ ) $.
    knoppndvlem17.n $e |- ( ph -> N e. NN ) $.
    knoppndvlem17.1 $e |- ( ph -> 1 < ( N x. ( abs ` C ) ) ) $.
    $( Lemma for ~ knoppndv .  (Contributed by Asger C. Ipsen, 12-Aug-2021.) $)
    knoppndvlem17 $p |- ( ph ->
     ( ( ( ( 2 x. N ) x. ( abs ` C ) ) ^ J ) x.
          ( 1 - ( 1 / ( ( ( 2 x. N ) x. ( abs ` C ) ) - 1 ) ) ) )
      <_ ( ( abs ` ( ( W ` B ) - ( W ` A ) ) ) / ( B - A ) ) ) $=
      ( c2 cmul co cabs cfv cexp c1 cmin cdiv cneg cle cr wcel clt knoppndvlem3
      wbr simpld recnd abscld reexpcld 2re a1i cc0 wne 2ne0 redivcld 1red nnred
      remulcld resubcld 0red 0lt1 knoppndvlem12 simprd lttrd jca gt0ne0 mulcomd
      syl oveq1d crp 2rp nnrpd rpmulcld nn0zd znegcld rpexpcld rphalfcld rpne0d
      wa rpcnd divassd divcld divcan7d expnegd oveq2d 1cnd expcld gtned expne0d
      divdiv2d mulcld div1d cc cz w3a wceq knoppndvlem13 absne0d mulexpz eqcomd
      3eqtrd eqtrd caddc peano2zd knoppndvlem1 eqeltrd knoppcld subcld lediv1dd
      3jca knoppndvlem15 eqbrtrd knoppndvlem16 breqtrd ) AUFNUGUHZGUIUJZUGUHZLU
      KUHZULULYMULUMUHZUNUHZUMUHZUGUHZFOUJZEOUJZUMUHZUIUJZYKLUOZUKUHZUFUNUHZUNU
      HZUUBFEUMUHZUNUHUPAYRYLLUKUHZUFUNUHZYQUGUHZUUEUNUHZUUFUPAUUKYRAUUKYQUUIUG
      UHZUUEUNUHYQUUIUUEUNUHZUGUHZYRAUUJUULUUEUNAUUIYQAUUIAUUHUFAYLLAGAGAGUQURZ
      YLULUSVAZAGUAUTZVBZVCZVDZUBVEZUFUQURAVFVGZUFVHVIAVJVGZVKZVCZAYQAULYPAVLZA
      ULYOUVFAYMULAYKYLAUFNUVBANUDVMVNZUUTVNUVFVOZAYOUQURZVHYOUSVAZWOYOVHVIAUVI
      UVJUVHAVHULYOAVPZUVFUVHVHULUSVAAVQVGZAYMULVIULYOUSVAAGNUAUDUEVRVSVTWAYOWB
      WDVKVOZVCZWCWEAYQUUIUUEUVNUVEAUUEAUUDAYKUUCAUFNUFWFURAWGVGANUDWHWIZALALUB
      WJZWKWLZWMZWPZAUUEUVRWNZWQAUUNUUMYQUGUHYRAYQUUMUVNAUUIUUEUVEUVSUVTWRWCAUU
      MYNYQUGAUUMUUHUUDUNUHZYNAUUHUUDUFAUUHUVAVCZAUUDUVQWPAUFUVBVCAUUDUVQWNUVCW
      SAUWAUUHULYKLUKUHZUNUHZUNUHUUHUWCUGUHZULUNUHZYNAUUDUWDUUHUNAYKLAYKUVGVCZA
      YKUVOWNZUVPWTXAAUUHULUWCUWBAXBAYKLUWGUBXCZAVHULUVKUVLXDAYKLUWGUWHUVPXEXFA
      UWFUWEUWCUUHUGUHZYNAUWEAUUHUWCUWBUWIXGXHAUUHUWCUWBUWIWCAYNUWJAYKXIURZYKVH
      VIZWOZYLXIURZYLVHVIZWOZLXJURZXKYNUWJXLAUWMUWPUWQAUWKUWLUWGUWHWAAUWNUWOAYL
      UUTVCAGUUSAGNUAUDUEXMXNWAUVPYFYKYLLXOWDXPXQXQXRWEXRXQXPAUUJUUBUUEAUUIYQUV
      DUVMVNAUUAAYSYTABCDFGHIJKNOPQRAFUUEMULXSUHZUGUHZUQFUWSXLATVGALUWRNUDUVPAM
      UCXTYAYBUDUURAUUOUUPUUQVSZYCABCDEGHIJKNOPQRAEUUEMUGUHZUQEUXAXLASVGALMNUDU
      VPUCYAYBUDUURUWTYCYDVDUVRABCDEFGHIJKLMNOPQRSTUAUBUCUDUEYGYEYHAUUEUUGUUBUN
      AUUGUUEAEFLMNSTUBUCUDYIXPXAYJ $.
  $}

  ${
    $d C j $.  $d D j $.  $d E j $.  $d G j $.  $d N j $.  $d ph j $.
    knoppndvlem18.c $e |- ( ph -> C e. ( -u 1 (,) 1 ) ) $.
    knoppndvlem18.n $e |- ( ph -> N e. NN ) $.
    knoppndvlem18.d $e |- ( ph -> D e. RR+ ) $.
    knoppndvlem18.e $e |- ( ph -> E e. RR+ ) $.
    knoppndvlem18.g $e |- ( ph -> G e. RR+ ) $.
    knoppndvlem18.1 $e |- ( ph -> 1 < ( N x. ( abs ` C ) ) ) $.
    $( Lemma for ~ knoppndv .  (Contributed by Asger C. Ipsen, 14-Aug-2021.) $)
    knoppndvlem18 $p |- ( ph -> E. j e. NN0
      ( ( ( ( 2 x. N ) ^ -u j ) / 2 ) < D /\
      E <_ ( ( ( ( 2 x. N ) x. ( abs ` C ) ) ^ j ) x. G ) ) ) $=
      ( c2 co wbr cle c1 wcel adantr cmul cv cneg cexp cdiv clt cabs wa cn wrex
      cfv cn0 cif wceq 2re a1i nnred remulcld recnd cc0 wne 2pos nngt0d mulgt0d
      cr gt0ne0d cz nnz adantl expnegd adantrr crp 2rp jca rpmulcl syl rpexpcld
      elrpd rprecred knoppndvlem3 simpld abscld nnnn0 reexpcld rpred ifcld max1
      rpne0d redivcld simprr lelttrd cc mulexpd rpge0d w3a absge0d simprd ltled
      1red exple1 lemul2ad mulridd breqtrd eqbrtrd ltletrd ltrec1d wb reexpclzd
      3jca nnnegz ltdivmuld mpbird max2 letrd ledivmul2d mpbid eqcomi 0le1 1lt2
      1t1e1 ltmul12ad mulassd eqcomd expnbnd reximddv wss nnssnn0 ssrexv ax-mp
      wi ) ANGUAOZDUBZUCZUDOZNUEOCUFPZEYKBUGUKZUAOZYLUDOZFUAOQPZUHZDUIUJZYTDULU
      JZARNCUAOZUEOZEFUEOZQPZUUEUUDUMZYRUFPZYTDUIAYLUISZUUHUHZUHZYOYSUUKYOYNUUC
      UFPZUUKYNRYKYLUDOZUEOZUUCUFAUUIYNUUNUNUUHAUUIUHZYKYLUUOYKAYKVESUUIANGNVES
      AUOUPZAGIUQZURZTZUSZAYKUTVAUUIAYKANGUUPUUQUTNUFPAVBUPAGIVCVDZVFTZUUIYLVGS
      AYLVHVIZVJVKUUKUUCUUMAUUCVLSZUUJANVLSZCVLSZUHUVDAUVEUVFUVEAVMUPJVNNCVOVPZ
      TZAUUIUUMVLSUUHUUOYKYLAYKVLSUUIAYKUURUVAVRTUVCVQZVKZUUKUUDYRUUMUUKUUCUVHV
      SZAUUIYRVESUUHUUOYQYLAYQVESZUUIAYKYPUURABABABVESZYPRUFPZABHVTZWAUSZWBZURZ
      TUUIYLULSZAYLWCVIZWDVKZUUKUUMUVJWEUUKUUDUUGYRUVKAUUGVESZUUJAUUFUUEUUDVEAE
      FAEKWEZAFLWEAFLWHWIZAUUCUVGVSZWFZTZUWAAUUDUUGQPZUUJAUUDVESZUUEVESZUHZUWHA
      UWIUWJUWEUWDVNZUUDUUEWGVPTAUUIUUHWJZWKAUUIYRUUMQPUUHUUOYRUUMYPYLUDOZUAOZU
      UMQUUOYKYPYLUUTAYPWLSUUIAYPUVQUSZTUVTWMUUOUWOUUMRUAOUUMQUUOUWNRUUMUUOYPYL
      AYPVESZUUIUVQTUVTWDUUOWSUUOUUMUVIWEZUUOUUMUVIWNUUOUWQUTYPQPZYPRQPZWOZUVSU
      HUWNRQPUUOUXAUVSAUXAUUIAUWQUWSUWTUVQABUVPWPAYPRUVQAWSZAUVMUVNUVOWQWRXITUV
      TVNYPYLWTVPXAUUOUUMUUOUUMUWRUSXBXCXDVKXEXFXDAUUIYOUULXGUUHUUOYNCNUUOYKYMU
      USUVBUUIYMVGSAYLXJVIXHACVESUUIACJWETUVEUUOVMUPXKVKXLUUKUUEYRQPYSUUKUUEUUG
      YRAUWJUUJUWDTUWGUWAAUUEUUGQPZUUJAUWKUXCUWLUUDUUEXMVPTUUKUUGYRUWGUWAUWMWRX
      NUUKEYRFAEVESUUJUWCTUWAAFVLSUUJLTXOXPVNAUWBUVLRYQUFPZWOUUHDUIUJAUWBUVLUXD
      UWFUVRARNGYPUAOZUAOZYQUFARRRUAOZUXFUFRUXGUNAUXGRXTXQUPARNRUXEUXBUUPUXBAGY
      PUUQUVQURUTRQPAXRUPZRNUFPAXSUPUXHMYAXDAYQUXFANGYPANUUPUSAGUUQUSUWPYBYCXCX
      IUUGYQDYDVPYEUIULYFUUAUUBYJYGYTDUIULYHYIVP $.
  $}

  ${
    $d ph m $.  $d J m $.  $d H m $.  $d N m $.
    knoppndvlem19.a $e |- A = ( ( ( ( 2 x. N ) ^ -u J ) / 2 ) x. m ) $.
    knoppndvlem19.b $e |- B = ( ( ( ( 2 x. N ) ^ -u J ) / 2 ) x. ( m + 1 ) ) $.
    knoppndvlem19.j $e |- ( ph -> J e. NN0 ) $.
    knoppndvlem19.h $e |- ( ph -> H e. RR ) $.
    knoppndvlem19.n $e |- ( ph -> N e. NN ) $.
    $( Lemma for ~ knoppndv .  (Contributed by Asger C. Ipsen, 17-Aug-2021.) $)
    knoppndvlem19 $p |- ( ph -> E. m e. ZZ ( A <_ H /\ H <_ B ) ) $=
      ( cle wbr c2 cmul co cr wcel a1i wa cneg cexp cdiv cfl cfv c1 caddc nnred
      cz 2re remulcld cc0 clt 2pos nngt0d mulgt0d gt0ne0d nn0zd reexpclzd recnd
      znegcld mulne0bad redivcld w3a 3jca expgt0 syl divgt0d flcld cv wb oveq2d
      wceq id eqtrd breq1d oveq1d breq2d anbi12d adantl zred 0red flle lemul2ad
      ltled divcan2d breqtrd eqcomd peano2re fllep1 eqbrtrd jca rspcedvd ) ABEM
      NZECMNZUAZOGPQZFUBZUCQZOUDQZEXAUDQZUEUFZPQZEMNZEXAXCUGUHQZPQZMNZUAZDXCUJA
      XBAEXAKAWTOAWRWSAOGORSAUKTZAGLUIZULZAWRAOGXJXKUMOUNNAUOTZAGLUPUQZURZAFAFJ
      USVBZUTZXJAOGAOXJVAAGXKVAXOVCVDZAXAAWTOXQXJAWRRSZWSUJSZUMWRUNNZVEUMWTUNNA
      XSXTYAXLXPXNVFWRWSVGVHXMVIZURZVDZVJZDVKZXCVNZWQXIVLAYGWOXEWPXHYGBXDEMYGBX
      AYFPQZXDBYHVNYGHTYGYFXCXAPYGVOZVMVPVQYGCXGEMYGCXAYFUGUHQZPQZXGCYKVNYGITYG
      YJXFXAPYGYFXCUGUHYIVRVMVPVSVTWAAXEXHAXDXAXBPQZEMAXCXBXAAXCYEWBZYDXRAUMXAA
      WCXRYBWFZAXBRSZXCXBMNYDXBWDVHWEAEXAAEKVAAXAXRVAYCWGZWHAEYLXGMAYLEYPWIAXBX
      FXAYDAXCRSXFRSYMXCWJVHXRYNAYOXBXFMNYDXBWKVHWEWLWMWN $.
  $}

  ${
    knoppndvlem20.c $e |- ( ph -> C e. ( -u 1 (,) 1 ) ) $.
    knoppndvlem20.n $e |- ( ph -> N e. NN ) $.
    knoppndvlem20.1 $e |- ( ph -> 1 < ( N x. ( abs ` C ) ) ) $.
    $( Lemma for ~ knoppndv .  (Contributed by Asger C. Ipsen, 18-Aug-2021.) $)
    knoppndvlem20 $p |- ( ph ->
      ( 1 - ( 1 / ( ( ( 2 x. N ) x. ( abs ` C ) ) - 1 ) ) ) e. RR+ ) $=
      ( c1 c2 cmul co cabs cmin clt wbr wcel cr a1i remulcld cc0 mpbid cfv cdiv
      crp wne knoppndvlem12 simprd 2re nnred knoppndvlem3 simpld recnd resubcld
      abscld 1red 0red 0lt1 lttrd elrpd recgt1d wa wb rprecred jca difrp syl )
      AGHCIJZBKUAZIJZGLJZUBJZGMNZGVJLJUCOZAGVIMNZVKAVHGUDVMABCDEFUEUFZAVIAVIAVH
      GAVFVGAHCHPOAUGQACEUHRABABABPOVGGMNABDUIUJUKUMRAUNZULZASGVIAUOVOVPSGMNAUP
      QVNUQURZUSTAVJPOZGPOZUTVKVLVAAVRVSAVIVQVBVOVCVJGVDVET $.
  $}

  ${
    $d C i n y $.  $d D a b m $.  $d E a b m $.  $d F i w $.  $d H a b m $.
    $d J a b m $.  $d J i m n w y $.  $d J i m w x $.  $d N a b m $.
    $d N i m n w y $.  $d N i m w x $.  $d T n y $.  $d W a b m $.
    $d ph i m n w y $.
    knoppndvlem21.t $e |- T = ( x e. RR |->
                            ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) ) $.
    knoppndvlem21.f $e |- F = ( y e. RR |-> ( n e. NN0 |->
            ( ( C ^ n ) x. ( T ` ( ( ( 2 x. N ) ^ n ) x. y ) ) ) ) ) $.
    knoppndvlem21.w $e |- W =
                        ( w e. RR |-> sum_ i e. NN0 ( ( F ` w ) ` i ) ) $.
    knoppndvlem21.g $e |- G =
                   ( 1 - ( 1 / ( ( ( 2 x. N ) x. ( abs ` C ) ) - 1 ) ) ) $.
    knoppndvlem21.c $e |- ( ph -> C e. ( -u 1 (,) 1 ) ) $.
    knoppndvlem21.d $e |- ( ph -> D e. RR+ ) $.
    knoppndvlem21.e $e |- ( ph -> E e. RR+ ) $.
    knoppndvlem21.h $e |- ( ph -> H e. RR ) $.
    knoppndvlem21.j $e |- ( ph -> J e. NN0 ) $.
    knoppndvlem21.n $e |- ( ph -> N e. NN ) $.
    knoppndvlem21.1 $e |- ( ph -> 1 < ( N x. ( abs ` C ) ) ) $.
    knoppndvlem21.2 $e |- ( ph -> ( ( ( 2 x. N ) ^ -u J ) / 2 ) < D ) $.
    knoppndvlem21.3 $e |- ( ph ->
            E <_ ( ( ( ( 2 x. N ) x. ( abs ` C ) ) ^ J ) x. G ) ) $.
    $( Lemma for ~ knoppndv .  (Contributed by Asger C. Ipsen, 18-Aug-2021.) $)
    knoppndvlem21 $p |- ( ph -> E. a e. RR E. b e. RR
      ( ( a <_ H /\ H <_ b ) /\ ( ( b - a ) < D /\ a =/= b ) /\
         E <_ ( ( abs ` ( ( W ` b ) - ( W ` a ) ) ) / ( b - a ) ) ) ) $=
      ( vm c2 cmul co cneg cexp cdiv cv cle wbr caddc cmin clt wne cfv cabs w3a
      c1 wa cr wrex cz eqid knoppndvlem19 wcel 2re a1i remulcld cc0 2pos nngt0d
      nnred mulgt0d gt0ne0d nn0zd znegcld reexpclzd rehalfcld adantr simpr zred
      adantrr peano2re syl jca remulcl simprr cn0 cn knoppndvlem16 eqbrtrd 3jca
      expgt0 divgt0d eqcomd mpbird ltned rpred knoppndvlem3 simpld recnd abscld
      breqtrd posdifd reexpcld wceq knoppndvlem20 simprd knoppcld subcld oveq2i
      eqeltrd redivcld cioo knoppndvlem17 letrd breq1 anbi1d oveq2 breq1d neeq1
      anbi12d fveq2 oveq2d fveq2d oveq12d breq2d 3anbi123d breq2 oveq1 fvoveq1d
      anbi2d neeq2 rspc2ev rexlimddv ) AUMOUNUOZNUPZUQUOZUMURUOZULUSZUNUOZMUTVA
      ZMUUJUUKVIVBUOZUNUOZUTVAZVJZQUSZMUTVAZMRUSZUTVAZVJZUUTUURVCUOZFVDVAZUURUU
      TVEZVJZJUUTPVFZUURPVFZVCUOZVGVFZUVCURUOZUTVAZVHZRVKVLQVKVLZULVMAUULUUOULM
      NOUULVNZUUOVNZUGUFUHVOAUUKVMVPZUUQVJVJZUULVKVPZUUOVKVPZUUQUUOUULVCUOZFVDV
      AZUULUUOVEZVJZJUUOPVFZUULPVFZVCUOZVGVFZUWAURUOZUTVAZVHZVHUVNUVRUVSUVTUWKA
      UVQUVSUUQAUVQVJZUUJUUKAUUJVKVPZUVQAUUIAUUGUUHAUMOUMVKVPAVQVRZAOUHWCZVSZAU
      UGAUMOUWNUWOVTUMVDVAAWAVRZAOUHWBWDZWEANANUGWFWGZWHZWIWJZUWLUUKAUVQWKZWLZV
      SZWMAUVQUVTUUQUWLUWMUUNVKVPZVJUVTUWLUWMUXEUXAUWLUUKVKVPUXEUXCUUKWNWOWPUUJ
      UUNWQWOZWMUVRUUQUWDUWJAUVQUUQWRAUVQUWDUUQUWLUWBUWCUWLUWAUUJFVDUWLUULUUONU
      UKOUVOUVPANWSVPUVQUGWJZUXBAOWTVPUVQUHWJZXAZAUUJFVDVAUVQUJWJXBUWLUULUUOUXD
      UWLUULUUOVDVAVTUWAVDVAUWLVTUUJUWAVDAVTUUJVDVAUVQAUUIUMUWTUWNAUUGVKVPZUUHV
      MVPZVTUUGVDVAZVHVTUUIVDVAAUXJUXKUXLUWPUWSUWRXCUUGUUHXDWOUWQXEWJUWLUWAUUJU
      XIXFXNZUWLUULUUOUXDUXFXOXGXHWPWMAUVQUWJUUQUWLJUUGEVGVFZUNUOZNUQUOZLUNUOZU
      WIAJVKVPUVQAJUEXIWJAUXQVKVPUVQAUXPLAUXONAUUGUXNUWPAEAEAEVKVPZUXNVIVDVAZAE
      UCXJZXKZXLXMVSUGXPALVIVIUXOVIVCUOURUOVCUOZVKLUYBXQAUBVRAUYBAEOUCUHUIXRXIY
      CVSWJUWLUWHUWAUWLUWGUWLUWEUWFUWLBCDUUOEGHIKOPSTUAUXFUXHAUXRUVQUYAWJZAUXSU
      VQAUXRUXSUXTXSWJZXTUWLBCDUULEGHIKOPSTUAUXDUXHUYCUYDXTYAXMUWLUWAUUJVKUXIUX
      AYCUWLUWAUXMWEYDAJUXQUTVAUVQUKWJUWLUXQUXPUYBUNUOZUWIUTUXQUYEXQUWLLUYBUXPU
      NUBYBVRUWLBCDUULUUOEGHIKNUUKOPSTUAUVOUVPAEVIUPVIYEUOVPUVQUCWJUXGUXBUXHAVI
      OUXNUNUOVDVAUVQUIWJYFXBYGWMXCXCUVMUWKUUMUVAVJZUUTUULVCUOZFVDVAZUULUUTVEZV
      JZJUVGUWFVCUOZVGVFZUYGURUOZUTVAZVHQRUULUUOVKVKUURUULXQZUVBUYFUVFUYJUVLUYN
      UYOUUSUUMUVAUURUULMUTYHYIUYOUVDUYHUVEUYIUYOUVCUYGFVDUURUULUUTVCYJZYKUURUU
      LUUTYLYMUYOUVKUYMJUTUYOUVJUYLUVCUYGURUYOUVIUYKVGUYOUVHUWFUVGVCUURUULPYNYO
      YPUYPYQYRYSUUTUUOXQZUYFUUQUYJUWDUYNUWJUYQUVAUUPUUMUUTUUOMUTYTUUCUYQUYHUWB
      UYIUWCUYQUYGUWAFVDUUTUUOUULVCUUAZYKUUTUUOUULUUDYMUYQUYMUWIJUTUYQUYLUWHUYG
      UWAURUYQUVGUWEUWFVGVCUUTUUOPYNUUBUYRYQYRYSUUEWOUUF $.
  $}

  ${
    $d C i j n w y $.  $d D a b j $.  $d D i j n w y $.  $d E a b j $.
    $d E i j n w y $.  $d F i w $.  $d H a b j $.  $d N a b j $.
    $d N i j n w y $.  $d N i j w x $.  $d T n y $.  $d W a b j $.
    $d ph i j n w y $.
    knoppndvlem22.t $e |- T = ( x e. RR |->
                            ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) ) $.
    knoppndvlem22.f $e |- F = ( y e. RR |-> ( n e. NN0 |->
            ( ( C ^ n ) x. ( T ` ( ( ( 2 x. N ) ^ n ) x. y ) ) ) ) ) $.
    knoppndvlem22.w $e |- W =
                        ( w e. RR |-> sum_ i e. NN0 ( ( F ` w ) ` i ) ) $.
    knoppndvlem22.c $e |- ( ph -> C e. ( -u 1 (,) 1 ) ) $.
    knoppndvlem22.d $e |- ( ph -> D e. RR+ ) $.
    knoppndvlem22.e $e |- ( ph -> E e. RR+ ) $.
    knoppndvlem22.h $e |- ( ph -> H e. RR ) $.
    knoppndvlem22.n $e |- ( ph -> N e. NN ) $.
    knoppndvlem22.1 $e |- ( ph -> 1 < ( N x. ( abs ` C ) ) ) $.
    $( Lemma for ~ knoppndv .  (Contributed by Asger C. Ipsen, 19-Aug-2021.) $)
    knoppndvlem22 $p |- ( ph -> E. a e. RR E. b e. RR
      ( ( a <_ H /\ H <_ b ) /\ ( ( b - a ) < D /\ a =/= b ) /\
         E <_ ( ( abs ` ( ( W ` b ) - ( W ` a ) ) ) / ( b - a ) ) ) ) $=
      ( vj c2 cmul co cv cneg cexp cdiv clt wbr cabs cfv c1 cmin cle wa wne w3a
      cr wrex cn0 knoppndvlem20 knoppndvlem18 wcel eqid cioo adantr crp simprrl
      simprl cn simprrr knoppndvlem21 rexlimddv ) AUGMUHUIZUFUJZUKULUIUGUMUIFUN
      UOZJVTEUPUQZUHUIZWAULUIURURWDURUSUIUMUIUSUIZUHUIUTUOZVAZOUJZLUTUOLPUJZUTU
      OVAWIWHUSUIZFUNUOWHWIVBVAJWINUQWHNUQUSUIUPUQWJUMUIUTUOVCPVDVEOVDVEUFVFAEF
      UFJWEMTUDUAUBAEMTUDUEVGUEVHAWAVFVIZWGVAZVABCDEFGHIJKWELWAMNOPQRSWEVJAEURU
      KURVKUIVIWLTVLAFVMVIWLUAVLAJVMVIWLUBVLALVDVIWLUCVLAWKWGVOAMVPVIWLUDVLAURM
      WCUHUIUNUOWLUEVLAWKWBWFVNAWKWBWFVQVRVS $.
  $}

  ${
    $d C i n w y $.  $d F i w $.  $d N a b $.  $d N i n w y $.  $d N i w x $.
    $d T n y $.  $d W a b d e h $.  $d ph a b d e h $.  $d ph d e h i n w y $.
    knoppndv.t $e |- T = ( x e. RR |->
                            ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) ) $.
    knoppndv.f $e |- F = ( y e. RR |-> ( n e. NN0 |->
            ( ( C ^ n ) x. ( T ` ( ( ( 2 x. N ) ^ n ) x. y ) ) ) ) ) $.
    knoppndv.w $e |- W =
                        ( w e. RR |-> sum_ i e. NN0 ( ( F ` w ) ` i ) ) $.
    knoppndv.c $e |- ( ph -> C e. ( -u 1 (,) 1 ) ) $.
    knoppndv.n $e |- ( ph -> N e. NN ) $.
    knoppndv.1 $e |- ( ph -> 1 < ( N x. ( abs ` C ) ) ) $.
    $( The continuous nowhere differentiable function ` W ` ( Knopp, K. (1918).
       Math.  Z. 2, 1-26 ) is, in fact, nowhere differentiable.  (Contributed
       by Asger C. Ipsen, 19-Aug-2021.) $)
    knoppndv $p |- ( ph -> dom ( RR _D W ) = (/) ) $=
      ( cr co wcel vh va vb ve vd cv cdv cdm wn wal c0 wceq simpl wss ax-resscn
      wa cc a1i ccncf wf cabs cfv c1 clt wbr knoppndvlem3 simpld simprd knoppcn
      cncff syl ssidd dvbss adantr simpr sseldd jca cle cmin wne cdiv wrex cneg
      w3a cioo ad2antrr simprr simprl simplr knoppndvlem22 ralrimivva unbdqndv2
      crp cn cmul pm2.01da alrimiv eq0 sylibr ) AUAUFZRKUGSUHZTZUIZUAUJXAUKULAX
      CUAAXBAXBUPZAWTRTZUPZXCXDAXEAXBUMXDXARWTAXARUNXBARRKRUQUNAUOURAKRUQUSSTRU
      QKUTZABCDEFGHIJKLMNPAERTZEVAVBZVCVDVEZAEOVFZVGAXHXJXKVHVIRUQKVJVKZARVLVMV
      NAXBVOVPVQXFUBUCWTKRUDUEXFRVLAXGXEXLVNXFUBUFZWTVRVEWTUCUFZVRVEUPXNXMVSSZU
      EUFZVDVEXMXNVTUPUDUFZXNKVBXMKVBVSSVAVBXOWASVRVEWDUCRWBUBRWBUDUEWMWMXFXQWM
      TZXPWMTZUPZUPBCDEXPFGHXQIWTJKUBUCLMNAEVCWCVCWESTXEXTOWFXFXRXSWGXFXRXSWHAX
      EXTWIAJWNTXEXTPWFAVCJXIWOSVDVEXEXTQWFWJWKWLVKWPWQUAXAWRWS $.
  $}

  ${
    $d C n y $.  $d F i w z $.  $d N n y $.  $d N x $.  $d T n y $.
    $d ph i n w y z $.  $d i w x z $.
    knoppf.t $e |- T = ( x e. RR |->
                            ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) ) $.
    knoppf.f $e |- F = ( y e. RR |-> ( n e. NN0 |->
            ( ( C ^ n ) x. ( T ` ( ( ( 2 x. N ) ^ n ) x. y ) ) ) ) ) $.
    knoppf.w $e |- W =
                        ( w e. RR |-> sum_ i e. NN0 ( ( F ` w ) ` i ) ) $.
    knoppf.c $e |- ( ph -> C e. ( -u 1 (,) 1 ) ) $.
    knoppf.n $e |- ( ph -> N e. NN ) $.
    $( Knopp's function is a function.  (Contributed by Asger C. Ipsen,
       25-Aug-2021.) $)
    knoppf $p |- ( ph -> W : RR --> RR ) $=
      ( cr cfv wcel adantr vz cn0 cv csu wa cc0 nn0uz 0zd eqidd cn cabs clt wbr
      knoppndvlem3 simpld simpr knoppcnlem3 caddc cseq cli cdm cmpt wceq fveq1d
      c1 fveq2 sumeq2sdv cbvmptv eqtri cneg cioo knoppndvlem4 seqex fvex breldm
      co syl isumrecl fmptd ) ADQUBGUCZDUCZIRZRZGUDZQKAWAQSZUEZWCGWBUFUBUGWFUHW
      FVTUBSZUEZWCUIWHBCWAEFHIVTJLMWFJUJSZWGAWIWEPTZTWFEQSZWGAWKWEAWKEUKRVEULUM
      AEOUNUOTTWFWEWGAWEUPZTWFWGUPUQWFURWBUFUSZWAKRZUTUMWMUTVASWFBCUAWAEFGHIJKL
      MKDQWDVBUAQUBVTUAUCZIRZRZGUDZVBNDUAQWDWRWAWOVCZUBWCWQGWSVTWBWPWAWOIVFVDVG
      VHVIWLAEVEVJVEVKVPSWEOTWJVLWMWNUTURWBUFVMWAKVNVOVQVRNVS $.
  $}

  ${
    $d C n y $.  $d F i w $.  $d N n y $.  $d N x $.  $d T n y $.
    $d ph i n w y $.  $d i w x $.
    knoppcn2.t $e |- T = ( x e. RR |->
                            ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) ) $.
    knoppcn2.f $e |- F = ( y e. RR |-> ( n e. NN0 |->
            ( ( C ^ n ) x. ( T ` ( ( ( 2 x. N ) ^ n ) x. y ) ) ) ) ) $.
    knoppcn2.w $e |- W = ( w e. RR |-> sum_ i e. NN0 ( ( F ` w ) ` i ) ) $.
    knoppcn2.n $e |- ( ph -> N e. NN ) $.
    knoppcn2.c $e |- ( ph -> C e. ( -u 1 (,) 1 ) ) $.
    $( Variant of ~ knoppcn with different codomain.  (Contributed by Asger C.
       Ipsen, 25-Aug-2021.) $)
    knoppcn2 $p |- ( ph -> W e. ( RR -cn-> RR ) ) $=
      ( cr ccncf wcel cc co wf knoppf wss wa wb ax-resscn a1i cabs knoppndvlem3
      cfv c1 clt wbr simpld simprd knoppcn jca cncfcdm syl mpbird ) AKQQRUASZQQ
      KUBZABCDEFGHIJKLMNPOUCAQTUDZKQTRUASZUEVBVCUFAVDVEVDAUGUHABCDEFGHIJKLMNOAE
      QSZEUIUKULUMUNZAEPUJZUOAVFVGVHUPUQURQTQKUSUTVA $.
  $}

  ${
    $d F i w $.  $d T n y $.  $d i n w y $.  $d i w x $.
    cnndvlem1.t $e |- T = ( x e. RR |->
                            ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) ) $.
    cnndvlem1.f $e |- F = ( y e. RR |-> ( n e. NN0 |->
            ( ( ( 1 / 2 ) ^ n ) x. ( T ` ( ( ( 2 x. 3 ) ^ n ) x. y ) ) ) ) ) $.
    cnndvlem1.w $e |- W = ( w e. RR |-> sum_ i e. NN0 ( ( F ` w ) ` i ) ) $.
    $( Lemma for ~ cnndv .  (Contributed by Asger C. Ipsen, 25-Aug-2021.) $)
    cnndvlem1 $p |- ( W e. ( RR -cn-> RR ) /\ dom ( RR _D W ) = (/) ) $=
      ( co wcel wtru c1 c2 c3 clt wbr cc0 cr ccncf cdv cdm c0 wceq cdiv 3nn a1i
      cn cneg cxr w3a wa neg1rr rexri 1re halfre 3pm3.2i neg1lt0 halfgt0 pm3.2i
      cioo 0re lttri ax-mp halflt1 elioo3g mpbir knoppcn2 cabs cfv cmul mullidi
      mptru 2cn 2lt3 eqbrtri wb 2pos nnrei 2re ltmuldivi mpbi cle ltleii absidi
      oveq2i nncni 2ne0 divreci eqcomi eqtri breqtrri knoppndv ) HUAUAUBLMZUAHU
      CLUDUEUFZWPNABCOPUGLZDEFGQHIJKQUJMNUHUIZWROUKZOVCLMZNXAWTULMZOULMZWRULMZU
      MZWTWRRSZWRORSZUNZUNXEXHXBXCXDWTUOUPOUQUPWRURUPUSXFXGWTTRSZTWRRSZUNXFXIXJ
      UTVAVBWTTWRUOVDURVEVFVGVBVBWTOWRVHVIUIZVJVOWQNABCWRDEFGQHIJKXKWSOQWRVKVLZ
      VMLZRSNOQPUGLZXMROPVMLZQRSZOXNRSZXOPQRPVPVNVQVRTPRSXPXQVSVTOQPUQQUHWAWBWC
      VFWDXMQWRVMLZXNXLWRQVMTWRWESXLWRUFTWRVDURVAWFWRURWGVFWHXNXRQPQUHWIVPWJWKW
      LWMWNUIWOVOVB $.
  $}

  ${
    $d F i w $.  $d T n y $.  $d W f $.  $d i n w y $.  $d i w x $.
    cnndvlem2.t $e |- T = ( x e. RR |->
                            ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) ) $.
    cnndvlem2.f $e |- F = ( y e. RR |-> ( n e. NN0 |->
            ( ( ( 1 / 2 ) ^ n ) x. ( T ` ( ( ( 2 x. 3 ) ^ n ) x. y ) ) ) ) ) $.
    cnndvlem2.w $e |- W = ( w e. RR |-> sum_ i e. NN0 ( ( F ` w ) ` i ) ) $.
    $( Lemma for ~ cnndv .  (Contributed by Asger C. Ipsen, 26-Aug-2021.) $)
    cnndvlem2 $p |- E. f ( f e. ( RR -cn-> RR ) /\ dom ( RR _D f ) = (/) ) $=
      ( cr co wcel cdv cdm c0 wceq cv ccncf wex cnndvlem1 cn0 cfv csu cmpt reex
      wa cvv mptex eqeltri eleq1 oveq2 dmeqd eqeq1d anbi12d spcev ax-mp ) IMMUA
      NZOZMIPNZQZRSZUIZETZUTOZMVFPNZQZRSZUIZEUBABCDFGHIJKLUCVKVEEIICMUDFTCTHUEU
      EFUFZUGUJLCMVLUHUKULVFISZVGVAVJVDVFIUTUMVMVIVCRVMVHVBVFIMPUNUOUPUQURUS $.
  $}

  ${
    $d f i n w x y $.
    $( There exists a continuous nowhere differentiable function.  The result
       follows directly from ~ knoppcn and ~ knoppndv .  (Contributed by Asger
       C. Ipsen, 26-Aug-2021.) $)
    cnndv $p |- E. f ( f e. ( RR -cn-> RR ) /\ dom ( RR _D f ) = (/) ) $=
      ( vx vy vw vi vn cr cv c1 c2 cdiv caddc cfl cfv cmpt cn0 cexp cmul eqid
      co cmin cabs c3 csu cnndvlem2 ) BCDBGBHZIJKTZLTMNUFUATUBNOZAEFCGFPUGFHZQT
      JUCRTUIQTCHRTUHNRTOOZDGPEHDHUJNNEUDOZUHSUJSUKSUE $.
  $}

$( (End of Asger C. Ipsen's mathbox.) $)
