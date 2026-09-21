$[ set-main.mm $]
$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Mathbox for Jeff Hoffman
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Inferences for finite induction on generic function values
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( findrec.mm - Inferences for finite induction on generic function values
     and specifically, functions defined via rec(G, A). $)

  $( Please add description here.  (Contributed by Jeff Hoffman,
     12-Feb-2008.) $)
  fveleq $p |- ( A = B ->
             ( ( ph -> ( F ` A ) e. P ) <-> ( ph -> ( F ` B ) e. P ) ) ) $=
    ( wceq cfv wcel fveq2 eleq1d imbi2d ) BCFZBEGZDHCEGZDHALMNDBCEIJK $.

  ${
    $d F x y $.  $d P x y $.  $d x y ph $.  $d x A $.
    findfvcl.1 $e |- ( ph -> ( F ` (/) ) e. P ) $.
    findfvcl.2 $e |- ( y e. _om -> ( ph -> ( ( F ` y ) e. P ->
                     ( F ` suc y ) e. P ) ) ) $.
    $( Please add description here.  (Contributed by Jeff Hoffman,
       12-Feb-2008.) $)
    findfvcl $p |- ( A e. _om -> ( ph -> ( F ` A ) e. P ) ) $=
      ( vx cv cfv wcel wi c0 csuc fveleq com a2d finds ) AHIZEJDKLAMEJDKLABIZEJ
      DKZLATNZEJDKZLACEJDKLHBCASMDEOASTDEOASUBDEOASCDEOFTPKAUAUCGQR $.
  $}

  ${
    $d y z $.  $d G y $.  $d A y $.  $d P y $.  $d G z $.  $d A z $.  $d P z $.
    findreccl.1 $e |- ( z e. P -> ( G ` z ) e. P ) $.
    $( Please add description here.  (Contributed by Jeff Hoffman,
       19-Feb-2008.) $)
    findreccl $p |- ( C e. _om -> ( A e. P -> ( rec ( G , A ) ` C ) e. P ) ) $=
      ( vy wcel crdg c0 cfv wceq rdg0g eleq1a mpd cv com csuc wi eleq1d vtoclga
      con0 nnon fveq2 rdgsuc imbitrrid syl a1d findfvcl ) BDHZGCDEBIZUJJUKKZBLU
      LDHBDEMBDULNOGPZQHZUMUKKZDHZUMRUKKZDHZSZUJUNUMUBHZUSUMUCUPURUTUOEKZDHZAPZ
      EKZDHVBAUODVCUOLVDVADVCUOEUDTFUAUTUQVADBUMEUETUFUGUHUI $.
  $}

  ${
    $d G x $.  $d A x $.  $d C x $.  $d G z $.  $d A z $.  $d P z $.
    findabrcl.1 $e |- ( z e. P -> ( G ` z ) e. P ) $.
    $( Please add description here.  (Contributed by Jeff Hoffman,
       16-Feb-2008.)  (Revised by Mario Carneiro, 11-Sep-2015.) $)
    findabrcl $p |- ( ( C e. _om /\ A e. P ) ->
                  ( ( x e. _V |-> ( rec ( G , A ) ` x ) ) ` C ) e. P ) $=
      ( com wcel wa cvv cv crdg cfv cmpt wceq elex fveq2 eqid fvex fvmpt adantr
      syl findreccl imp eqeltrd ) DHIZCEIZJDAKALZFCMZNZOZNZDUJNZEUGUMUNPZUHUGDK
      IUODHQADUKUNKULUIDUJRULSDUJTUAUCUBUGUHUNEIBCDEFGUDUEUF $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  gdc.mm
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( gdc.mm  9-Apr-2008 $)

  ${
    nnssi2.1 $e |- NN C_ D $.
    nnssi2.2 $e |- ( B e. NN -> ph ) $.
    nnssi2.3 $e |- ( ( A e. D /\ B e. D /\ ph ) -> ps ) $.
    $( Convert a theorem for real/complex numbers into one for positive
       integers.  (Contributed by Jeff Hoffman, 17-Jun-2008.) $)
    nnssi2 $p |- ( ( A e. NN /\ B e. NN ) -> ps ) $=
      ( cn wcel wa w3a sseli 3anim123i 3anidm23 syl ) CIJZDIJZKCEJZDEJZALZBQRUA
      QSRTRAIECFMIEDFMGNOHP $.
  $}

  ${
    nnssi3.1 $e |- NN C_ D $.
    nnssi3.2 $e |- ( C e. NN -> ph ) $.
    nnssi3.3 $e |- ( ( ( A e. D /\ B e. D /\ C e. D ) /\ ph ) -> ps ) $.
    $( Convert a theorem for real/complex numbers into one for positive
       integers.  (Contributed by Jeff Hoffman, 17-Jun-2008.) $)
    nnssi3 $p |- ( ( A e. NN /\ B e. NN /\ C e. NN ) -> ps ) $=
      ( cn wcel w3a sseli 3anim123i 3ad2ant3 syl2anc ) CJKZDJKZEJKZLCFKZDFKZEFK
      ZLABQTRUASUBJFCGMJFDGMJFEGMNSQARHOIP $.
  $}

  $( Please add description here.  (Contributed by Jeff Hoffman,
     17-Jun-2008.) $)
  nndivsub $p |- ( ( ( A e. NN /\ B e. NN /\ C e. NN )
                       /\ ( ( A / C ) e. NN /\ A < B ) )
                    -> ( ( B / C ) e. NN <-> ( ( B - A ) / C ) e. NN ) ) $=
    ( cn wcel cdiv co clt wbr wa cmin wi cr cc0 wb nnre jca biimpd cc nncn wceq
    w3a nngt0 ltdiv1 syl3an nnsub sylan9bb exp32 com34 imp32 nnaddcl expcom wne
    caddc nnsscn nnne0 divcl nnssi2 anim12i 3impdir npcan ancoms eleq1d sylan9r
    adantrr impbid 3ad2ant2 3ad2ant1 3ad2ant3 divsubdir syl3anc adantr bitr4d
    syl ) ADEZBDEZCDEZUBZACFGZDEZABHIZJZJZBCFGZDEZWDVSKGZDEZBAKGCFGZDEZWCWEWGVR
    VTWAWEWGLVRVTWEWAWGVRVTWEWAWGLVRVTWEJZJWAWGVRWAVSWDHIZWJWGVOAMEVPBMEVQCMEZN
    CHIZJWAWKOAPBPVQWLWMCPCUCQABCUDUEVSWDUFUGRUHUIUJVRVTWGWELWAVTWGWFVSUNGZDEZV
    RWEWGVTWOWFVSUKULVRWOWEVRWNWDDVRVSSEZWDSEZJZWNWDUAZVOVQVPWRVOVQJWPVPVQJWQCN
    UMZWPACSUOCUPZACUQURWTWQBCSUOXABCUQURUSUTWQWPWSWDVSVAVBVNVCRVDVEVFVRWIWGOWB
    VRWHWFDVRBSEZASEZCSEZWTJZWHWFUAVPVOXBVQBTVGVOVPXCVQATVHVQVOXEVPVQXDWTCTXAQV
    IBACVJVKVCVLVM $.

  $( A factor of a positive integer cannot exceed it.  (Contributed by Jeff
     Hoffman, 17-Jun-2008.) $)
  nndivlub $p |- ( ( A e. NN /\ B e. NN )
        -> ( ( A / B ) e. NN -> B <_ A ) ) $=
    ( cn wcel cr cc0 clt wbr wa cdiv co cle wi nnre nngt0 jca c1 nnge1 lediv2
    wb 3anidm23 cc wne recn adantr gt0ne0 divid breq1d syl2anc adantl imbitrrid
    bitrd syl2anr ) BCDZBEDZFBGHZIZAEDZFAGHZIZABJKZCDZBALHZMACDZUNUOUPBNBOPVDUR
    USANAOPVBVCUQUTIZQVALHZVARVEVCAAJKZVALHZVFUQUTVCVHTBAASUAUTVHVFTZUQUTAUBDZA
    FUCZVIURVJUSAUDUEAUFVJVKIVGQVALAUGUHUIUJULUKUM $.

  $c gcdOLD $. $( The greatest common divisor $)

  $( Extend class notation to include the gdc function.
     (New usage is discouraged.) $)
  cgcdOLD $a class gcdOLD ( A , B ) $.

  ${
    $d x A $.  $d x B $.
    $( ` gcdOLD ( A , B ) ` is the largest positive integer that evenly divides
       both ` A ` and ` B ` .  (Contributed by Jeff Hoffman, 17-Jun-2008.)
       (New usage is discouraged.) $)
    df-gcdOLD $a |- gcdOLD ( A , B ) = sup ( { x e. NN | ( ( A / x ) e. NN
                                           /\ ( B / x ) e. NN ) } , NN , < ) $.

    $( Lemma for Euclid's Elements, Book 7, proposition 2.  The original
       mentions the smaller measure being 'continually subtracted' from the
       larger.  Many authors interpret this phrase as ` A ` mod ` B ` .  Here,
       just one subtraction step is proved to preserve the ` gcdOLD ` .  The
       ` rec ` function will be used in other proofs for iterated subtraction.
       (Contributed by Jeff Hoffman, 17-Jun-2008.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    ee7.2aOLD $p |- ( ( A e. NN /\ B e. NN )
         -> ( A < B -> gcdOLD ( A , B ) = gcdOLD ( A , ( B - A ) ) ) ) $=
      ( vx cn wcel wa clt wbr cgcdOLD cmin co wceq cv cdiv crab com23 df-gcdOLD
      csup wi imp wb w3a nndivsub exp32 3expia pm5.32d rabbidva supeq1d 3eqtr4g
      ex ) ADEZBDEZFZABGHZABIZABAJKZIZLUMUNFZACMZNKDEZBUSNKDEZFZCDOZDGRUTUPUSNK
      DEZFZCDOZDGRUOUQURDVCVFGURVBVECDURUSDEZFUTVAVDURVGUTVAVDUAZSZUMUNVGVISUMV
      GUNVIUKULVGUNVISUKULVGUBZUTUNVHVJUTUNVHABUSUCUDPUEPTTUFUGUHCABQCAUPQUIUJ
      $.
  $}

$( (End of Jeff Hoffman's mathbox.) $)
