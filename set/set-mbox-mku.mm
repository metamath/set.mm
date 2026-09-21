$[ set-main.mm $]
$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Mathbox for metakunt
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Commutative Semiring
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c CSRing $.

  $( Extend class notation with the class of all commutative semirings. $)
  ccsrg $a class CSRing $.

  ${
    $( Define the class of all commutative semirings.  (Contributed by
       metakunt, 4-Apr-2025.) $)
    df-csring $a |- CSRing = { f e. SRing | ( mulGrp ` f ) e. CMnd } $.
  $}

  ${
    $d G r $.  $d R r $.
    iscsrg.g $e |- G = ( mulGrp ` R ) $.
    $( A commutative semiring is a semiring whose multiplication is a
       commutative monoid.  (Contributed by metakunt, 4-Apr-2025.) $)
    iscsrg $p |- ( R e. CSRing <-> ( R e. SRing /\ G e. CMnd ) ) $=
      ( vr cv cmgp cfv ccmn wcel csrg ccsrg wceq fveq2 eqtr4di eleq1d df-csring
      elrab2 ) DEZFGZHIBHIDAJKRALZSBHTSAFGBRAFMCNODPQ $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  General helpful statements
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d R x $.  $d S x $.  $d X x $.  $d ph x $.
    rhmzrhval.1 $e |- ( ph -> F e. ( R RingHom S ) ) $.
    rhmzrhval.2 $e |- ( ph -> X e. ZZ ) $.
    rhmzrhval.3 $e |- M = ( ZRHom ` R ) $.
    rhmzrhval.4 $e |- N = ( ZRHom ` S ) $.
    $( Evaluation of integers across a ring homomorphism.  (Contributed by
       metakunt, 4-Jun-2025.) $)
    rhmzrhval $p |- ( ph -> ( F ` ( M ` X ) ) = ( N ` X ) ) $=
      ( vx cfv cz co wcel wceq syl eqid eqtrd cv cur cmg crg crh rhmrcl1 fveq1d
      cmpt zrhval2 fveq2d cvv eqidd oveq1 adantl ovexd fvmptd cghm cbs ringidcl
      rhmghm ghmmulg syl3anc rhm1 oveq2d eqcomd rhmrcl2 ) AGEMZDMZGLNLUAZCUBMZC
      UCMZOZUHZMZGFMZAVHGLNVIBUBMZBUCMZOZUHZMZDMZVNAVGVTDAGEVSABUDPZEVSQADBCUEO
      PZWBHBCDUFRZBVQVPLEJVQSZVPSZUIRUGUJAWAGVJVKOZVNAWAGVPVQOZDMZWGAVTWHDALGVR
      WHNVSUKAVSULVIGQZVRWHQAVIGVPVQUMUNIAGVPVQUOUPUJAWIGVPDMZVKOZWGADBCUQOPZGN
      PVPBURMZPZWIWLQAWCWMHBCDUTRIAWBWOWDWNBVPWNSZWFUSRWNVQVKDBCGVPWPWEVKSZVAVB
      AWKVJGVKAWCWKVJQHBCVPDVJWFVJSZVCRVDTTAVNWGALGVLWGNVMUKAVMULWJVLWGQAVIGVJV
      KUMUNIAGVJVKUOUPVETTAVOVNACUDPZVOVNQAWCWSHBCDVFRWSGFVMCVKVJLFKWQWRUIUGRVE
      T $.
  $}

  ${
    $d N a b $.  $d N x y $.  $d R a b $.  $d R x y $.  $d Z a b $.  $d Z x $.
    $d a b ph $.  $d ph y $.
    zndvdchrrhm.1 $e |- ( ph -> R e. Ring ) $.
    zndvdchrrhm.2 $e |- ( ph -> N e. NN ) $.
    zndvdchrrhm.3 $e |- ( ph -> ( chr ` R ) e. ZZ ) $.
    zndvdchrrhm.4 $e |- ( ph -> ( chr ` R ) || N ) $.
    zndvdchrrhm.5 $e |- Z = ( Z/nZ ` N ) $.
    zndvdchrrhm.6 $e |- F = ( x e. ( Base ` Z ) |->
     U. ( ( ZRHom ` R ) " x ) ) $.
    $( Construction of a ring homomorphism from ` Z/nZ ` to ` R ` when the
       characteristic of ` R ` divides ` N ` .  (Contributed by metakunt,
       4-Jun-2025.) $)
    zndvdchrrhm $p |- ( ph -> F e. ( Z RingHom R ) ) $=
      ( va czring cfv co wcel eqid syl cz vy vb csn crsp cqg cqus crh czrh cima
      cbs cv cuni cmpt cn0 wceq nnnn0d znbas2 eqcomd mpteq1d eqtrid ccnv zrhrhm
      c0g crg nfcv imaeq2 unieqd ccrg zringcrng a1i clidl wss zringring kerlidl
      cbvmpt wa simpr elsng syl5ibcom imp mpdan wf zringbas rhmf ffnd nnzd cchr
      cdvds wbr chrdvds syl2anc mpbid cvv fvexd mpbird elpreimad adantr eqeltrd
      wb ssrdv rspssp crngringd rspcl rhmqusnsg eqidd cplusg znadd oveqdr cmulr
      ex syl3anc znmul rhmpropd eleqtrd ) ADNNEUCZNUDOZOZUEPUFPZCUGPZFCUGPADBXR
      UJOZCUHOZBUKZUIZULZUMZXSADBFUJOZYDUMYELABYFXTYDAXTYFAEUNQZXTYFUOAEHUPZXPX
      REFXPRZXRRZKUQSZURUSUTAXRYANCYEYAVACVCOZUCZUIZXQYLUAYLRZACVDQZYANCUGPQZGC
      YAYARZVBZSZYNRYJBUAXTYDYAUAUKZUIZULZUAYDVEBUUCVEYBUUAUOYCUUBYBUUAYAVFVGVO
      NVHQAVIVJZANVDQZYNNVKOZQZXOYNVLXQYNVLUUEAVMVJAYQUUGYTNCYAUUFYLUUFRZYOVNSA
      MXOYNAMUKZXOQZUUIYNQAUUJVPZUUIEYNUUKUUJUUIEUOZAUUJVQZUUKUUJUULUUKUUJUUJUU
      LUUMUUIEXOVRVSVTWAZAEYNQUUJATEYMYAATCUJOZYAAYPTUUOYAWBZGYPYQUUPYSTUUONCYA
      WCUUORWDSSWEAEHWFZAEYAOZYMQZUURYLUOZACWGOZEWHWIZUUTJAYPETQZUVBUUTWSGUUQUV
      ACYAEYLUVARYRYOWJWKWLAUURWMQUUSUUTWSAEYAWNUURYLWMVRSWOWPWQWRXJWTNUUFXOYNX
      PYIUUHXAXKAUUEXOTVLXQUUFQANUUDXBAMXOTAUUJUUITQUUKUUIETUUNAUVCUUJUUQWQWRXJ
      WTTNUUFXOXPYIWCUUHXCWKXDWRAMUBXTUUOXRCFCAXTXEAUUOXEZYKUVDAUUIXTQUBUKZXTQV
      PZMUBXRXFOZFXFOZAYGUVGUVHUOYHXPXREFYIYJKXGSXHAUUIUUOQUVEUUOQVPVPZUUIUVECX
      FOPXEAUVFMUBXRXIOZFXIOZAYGUVJUVKUOYHXPXREFYIYJKXLSXHUVIUUIUVECXIOPXEXMXN
      $.
  $}

  ${
    relogbcld.1 $e |- ( ph -> B e. RR ) $.
    relogbcld.2 $e |- ( ph -> 0 < B ) $.
    relogbcld.3 $e |- ( ph -> X e. RR ) $.
    relogbcld.4 $e |- ( ph -> 0 < X ) $.
    relogbcld.5 $e |- ( ph -> B =/= 1 ) $.
    $( Closure of the general logarithm with a positive real base on positive
       reals, a deduction version.  (Contributed by metakunt, 22-May-2024.) $)
    relogbcld $p |- ( ph -> ( B logb X ) e. RR ) $=
      ( crp wcel c1 wne w3a clogb co cr elrpd 3jca relogbcl syl ) ABIJZCIJZBKLZ
      MBCNOPJAUAUBUCABDEQACFGQHRBCST $.
  $}

  ${
    relogbexpd.1 $e |- ( ph -> B e. RR+ ) $.
    relogbexpd.2 $e |- ( ph -> B =/= 1 ) $.
    relogbexpd.3 $e |- ( ph -> M e. ZZ ) $.
    $( Identity law for general logarithm: the logarithm of a power to the base
       is the exponent, a deduction version.  (Contributed by metakunt,
       22-May-2024.) $)
    relogbexpd $p |- ( ph -> ( B logb ( B ^ M ) ) = M ) $=
      ( crp wcel c1 wne cz w3a cexp co clogb wceq 3jca relogbexp syl ) ABGHZBIJ
      ZCKHZLBBCMNONCPATUAUBDEFQBCRS $.
  $}

  ${
    relogbzexpd.1 $e |- ( ph -> B e. RR+ ) $.
    relogbzexpd.2 $e |- ( ph -> B =/= 1 ) $.
    relogbzexpd.3 $e |- ( ph -> C e. RR+ ) $.
    relogbzexpd.4 $e |- ( ph -> N e. ZZ ) $.
    $( Power law for the general logarithm for integer powers:  The logarithm
       of a positive real number to the power of an integer is equal to the
       product of the exponent and the logarithm of the base of the power, a
       deduction version.  (Contributed by metakunt, 22-May-2024.) $)
    relogbzexpd $p |- ( ph -> ( B logb ( C ^ N ) ) = ( N x. ( B logb C ) ) ) $=
      ( cc cc0 c1 cpr cdif wcel crp cz w3a cexp co clogb cmul wceq rpcnd rpne0d
      nelprd eldifd 3jca relogbzexp syl ) ABIJKLZMNZCONZDPNZQBCDRSTSDBCTSUASUBA
      UKULUMABIUJABEUCABJKABEUDFUEUFGHUGBCDUHUI $.
  $}

  ${
    logblebd.1 $e |- ( ph -> B e. ZZ ) $.
    logblebd.2 $e |- ( ph -> 2 <_ B ) $.
    logblebd.3 $e |- ( ph -> X e. RR ) $.
    logblebd.4 $e |- ( ph -> 0 < X ) $.
    logblebd.5 $e |- ( ph -> Y e. RR ) $.
    logblebd.6 $e |- ( ph -> 0 < Y ) $.
    logblebd.7 $e |- ( ph -> X <_ Y ) $.
    $( The general logarithm is monotone/increasing, a deduction version.
       (Contributed by metakunt, 22-May-2024.) $)
    logblebd $p |- ( ph -> ( B logb X ) <_ ( B logb Y ) ) $=
      ( cle wbr clogb co c2 wcel crp wb cz cuz cfv w3a wa 2z eluz1 ax-mp sylibr
      jca elrpd 3jca logbleb syl mpbid ) ACDLMZBCNOBDNOLMZKABPUAUBQZCRQZDRQZUCU
      OUPSAUQURUSABTQZPBLMZUDZUQAUTVAEFUIPTQUQVBSUEPBUFUGUHACGHUJADIJUJUKBCDULU
      MUN $.
  $}

  ${
    $d M j k $.  $d N j $.  $d ch j $.  $d et j $.  $d j k ph $.  $d j ta $.
    $d j th $.  $d k ps $.
    uzindd.1 $e |- ( j = M -> ( ps <-> ch ) ) $.
    uzindd.2 $e |- ( j = k -> ( ps <-> th ) ) $.
    uzindd.3 $e |- ( j = ( k + 1 ) -> ( ps <-> ta ) ) $.
    uzindd.4 $e |- ( j = N -> ( ps <-> et ) ) $.
    uzindd.5 $e |- ( ph -> ch ) $.
    uzindd.6 $e |- ( ( ph /\ th /\ ( k e. ZZ /\ M <_ k ) ) -> ta ) $.
    uzindd.7 $e |- ( ph -> M e. ZZ ) $.
    uzindd.8 $e |- ( ph -> N e. ZZ ) $.
    uzindd.9 $e |- ( ph -> M <_ N ) $.
    $( Induction on the upper integers that start at ` M ` .  The first four
       hypotheses give us the substitution instances we need; the following two
       are the basis and the induction step, a deduction version.  (Contributed
       by metakunt, 8-Jun-2024.) $)
    uzindd $p |- ( ph -> et ) $=
      ( wi cz wcel cle wbr w3a 3jca cv wceq imbi2d c1 caddc co adantr expcom wa
      3anass ancom bitri ad4ant123 anasss sylan2b 3impa 3com23 3expia a2d uzind
      mpcom ) IUAUBZJUAUBZIJUCUDZUEAFAVHVIVJQRSUFABTACTADTAETAFTGHIJGUGZIUHBCAK
      UIVKHUGZUHBDALUIVKVLUJUKULUHBEAMUIVKJUHBFANUIAVHCACVHOUMUNVHVLUAUBZIVLUCU
      DZUEZADEAVODETAVODEADVOEADVOEVOADUOZVMVNUOZVHUOZEVOVHVQUOVRVHVMVNUPVHVQUQ
      URVPVQVHEADVQEVHPUSUTVAVBVCVDUNVEVFVG $.
  $}

  ${
    fzadd2d.1 $e |- ( ph -> M e. ZZ ) $.
    fzadd2d.2 $e |- ( ph -> N e. ZZ ) $.
    fzadd2d.3 $e |- ( ph -> O e. ZZ ) $.
    fzadd2d.4 $e |- ( ph -> P e. ZZ ) $.
    fzadd2d.5 $e |- ( ph -> J e. ( M ... N ) ) $.
    fzadd2d.6 $e |- ( ph -> K e. ( O ... P ) ) $.
    fzadd2d.7 $e |- ( ph -> Q = ( M + O ) ) $.
    fzadd2d.8 $e |- ( ph -> R = ( N + P ) ) $.
    $( Membership of a sum in a finite interval of integers, a deduction
       version.  (Contributed by metakunt, 10-May-2024.) $)
    fzadd2d $p |- ( ph -> ( J + K ) e. ( Q ... R ) ) $=
      ( co cfz wcel caddc wa jca cz wi fzadd2 syl mpd oveq12d eleqtrrd ) AEFUAR
      ZGIUARZHBUARZSRZCDSRAEGHSRTZFIBSRTZUBZUKUNTZAUOUPNOUCAGUDTZHUDTZUBZIUDTZB
      UDTZUBZUBUQURUEAVAVDAUSUTJKUCAVBVCLMUCUCBEFGHIUFUGUHACULDUMSPQUIUJ $.
  $}

  ${
    fzne2d.1 $e |- ( ph -> K e. ( M ... N ) ) $.
    fzne2d.2 $e |- ( ph -> K =/= N ) $.
    $( Elementhood in a finite set of sequential integers, except its upper
       bound.  (Contributed by metakunt, 23-May-2024.) $)
    fzne2d $p |- ( ph -> K < N ) $=
      ( clt wbr wne necomd cz wcel w3a cle wa cfz co elfz2 sylib zred simprrd
      simpld simp3d simp2d leltned mpbird ) ABDGHDBIABDFJABDABACKLZDKLZBKLZAUGU
      HUIMZCBNHZBDNHZOZABCDPQLUJUMOEBCDRSZUBZUCTADAUGUHUIUOUDTAUJUKULUNUAUEUF
      $.
  $}

  ${
    $d A x $.  $d F x $.  $d G x $.  $d ph x $.
    eqfnfv2d2.1 $e |- ( ph -> F Fn A ) $.
    eqfnfv2d2.2 $e |- ( ph -> G Fn B ) $.
    eqfnfv2d2.3 $e |- ( ph -> A = B ) $.
    eqfnfv2d2.4 $e |- ( ( ph /\ x e. A ) -> ( F ` x ) = ( G ` x ) ) $.
    $( Equality of functions is determined by their values, a deduction
       version.  (Contributed by metakunt, 28-May-2024.) $)
    eqfnfv2d2 $p |- ( ph -> F = G ) $=
      ( wceq cv cfv wral wa ralrimiva jca wfn wb eqfnfv2 syl mpbird ) AEFKZCDKZ
      BLZEMUEFMKZBCNZOZAUDUGIAUFBCJPQAECRZFDRZOUCUHSAUIUJGHQBCDEFTUAUB $.
  $}

  ${
    fzsplitnd.1 $e |- ( ph -> K e. ( M ... N ) ) $.
    $( Split a finite interval of integers into two parts.  (Contributed by
       metakunt, 28-May-2024.) $)
    fzsplitnd $p |- ( ph -> ( M ... N ) =
     ( ( M ... ( K - 1 ) ) u. ( K ... N ) ) ) $=
      ( cfz co c1 cmin cun cuz cfv wcel wceq elfzuz syl elfzelzd mpbird syl2anc
      caddc zcnd 1cnd npcand eleq1d 1zzd zsubcld elfzuz3 fveq2d eleq2d fzsplit2
      cz peano2uzr oveq1d uneq2d eqtrd ) ACDFGZCBHIGZFGZUQHTGZDFGZJZURBDFGZJAUS
      CKLZMZDUQKLMZUPVANAVDBVCMZABUPMZVFEBCDOPAUSBVCABHABABCDEQZUAAUBUCZUDRAUQU
      KMDUSKLZMZVEABHVHAUEUFAVKDBKLZMZAVGVMEBCDUGPAVJVLDAUSBKVIUHUIRUQDULSUQCDU
      JSAUTVBURAUSBDFVIUMUNUO $.
  $}

  ${
    fzsplitnr.1 $e |- ( ph -> M e. ZZ ) $.
    fzsplitnr.2 $e |- ( ph -> N e. ZZ ) $.
    fzsplitnr.3 $e |- ( ph -> K e. ZZ ) $.
    fzsplitnr.4 $e |- ( ph -> M <_ K ) $.
    fzsplitnr.5 $e |- ( ph -> K <_ N ) $.
    $( Split a finite interval of integers into two parts.  (Contributed by
       metakunt, 28-May-2024.) $)
    fzsplitnr $p |- ( ph -> ( M ... N ) =
     ( ( M ... ( K - 1 ) ) u. ( K ... N ) ) ) $=
      ( elfzd fzsplitnd ) ABCDABCDEFGHIJK $.
  $}

  ${
    addassnni.1 $e |- A e. NN $.
    addassnni.2 $e |- B e. NN $.
    addassnni.3 $e |- C e. NN $.
    $( Associative law for addition.  (Contributed by metakunt,
       25-Apr-2024.) $)
    addassnni $p |- ( ( A + B ) + C ) = ( A + ( B + C ) ) $=
      ( nncni addassi ) ABCADGBEGCFGH $.
  $}

  ${
    addcomnni.1 $e |- A e. NN $.
    addcomnni.2 $e |- B e. NN $.
    $( Commutative law for addition.  (Contributed by metakunt,
       25-Apr-2024.) $)
    addcomnni $p |- ( A + B ) = ( B + A ) $=
      ( nncni addcomi ) ABACEBDEF $.
  $}

  ${
    mulassnni.1 $e |- A e. NN $.
    mulassnni.2 $e |- B e. NN $.
    mulassnni.3 $e |- C e. NN $.
    $( Associative law for multiplication.  (Contributed by metakunt,
       25-Apr-2024.) $)
    mulassnni $p |- ( ( A x. B ) x. C ) = ( A x. ( B x. C ) ) $=
      ( nncni mulassi ) ABCADGBEGCFGH $.
  $}

  ${
    mulcomnni.1 $e |- A e. NN $.
    mulcomnni.2 $e |- B e. NN $.
    $( Commutative law for multiplication.  (Contributed by metakunt,
       25-Apr-2024.) $)
    mulcomnni $p |- ( A x. B ) = ( B x. A ) $=
      ( nncni mulcomi ) ABACEBDEF $.
  $}

  ${
    gcdcomnni.1 $e |- M e. NN $.
    gcdcomnni.2 $e |- N e. NN $.
    $( Commutative law for gcd.  (Contributed by metakunt, 25-Apr-2024.) $)
    gcdcomnni $p |- ( M gcd N ) = ( N gcd M ) $=
      ( cz wcel wa cgcd co wceq nnzi pm3.2i gcdcom ax-mp ) AEFZBEFZGABHIBAHIJOP
      ACKBDKLABMN $.
  $}

  ${
    gcdnegnni.1 $e |- M e. NN $.
    gcdnegnni.2 $e |- N e. NN $.
    $( Negation invariance for gcd.  (Contributed by metakunt, 25-Apr-2024.) $)
    gcdnegnni $p |- ( M gcd -u N ) = ( M gcd N ) $=
      ( cz wcel wa cneg cgcd co wceq nnzi pm3.2i gcdneg ax-mp ) AEFZBEFZGABHIJA
      BIJKPQACLBDLMABNO $.
  $}

  ${
    neggcdnni.1 $e |- M e. NN $.
    neggcdnni.2 $e |- N e. NN $.
    $( Negation invariance for gcd.  (Contributed by metakunt, 25-Apr-2024.) $)
    neggcdnni $p |- ( -u M gcd N ) = ( M gcd N ) $=
      ( cz wcel wa cneg cgcd co wceq nnzi pm3.2i neggcd ax-mp ) AEFZBEFZGAHBIJA
      BIJKPQACLBDLMABNO $.
  $}

  ${
    bccl2d.1 $e |- ( ph -> N e. NN ) $.
    bccl2d.2 $e |- ( ph -> K e. NN0 ) $.
    bccl2d.3 $e |- ( ph -> K <_ N ) $.
    $( Closure of the binomial coefficient, a deduction version.  (Contributed
       by metakunt, 12-May-2024.) $)
    bccl2d $p |- ( ph -> ( N _C K ) e. NN ) $=
      ( cc0 cfz co wcel cbc cn cz cle wbr w3a nn0zd nn0ge0d 3jca syl wb nnzd 0z
      elfz1 mpan mpbird bccl2 ) ABGCHIJZCBKILJAUHBMJZGBNOZBCNOZPZAUIUJUKABEQABE
      RFSACMJZUHULUAZACDUBGMJUMUNUCBGCUDUETUFBCUGT $.
  $}

  ${
    recbothd.1 $e |- ( ph -> A e. CC ) $.
    recbothd.2 $e |- ( ph -> A =/= 0 ) $.
    recbothd.3 $e |- ( ph -> B e. CC ) $.
    recbothd.4 $e |- ( ph -> B =/= 0 ) $.
    recbothd.5 $e |- ( ph -> C e. CC ) $.
    recbothd.6 $e |- ( ph -> C =/= 0 ) $.
    recbothd.7 $e |- ( ph -> D e. CC ) $.
    recbothd.8 $e |- ( ph -> D =/= 0 ) $.
    $( Take reciprocal on both sides.  (Contributed by metakunt,
       12-May-2024.) $)
    recbothd $p |- ( ph -> ( ( A / B ) = ( C / D )
     <-> ( B / A ) = ( D / C ) ) ) $=
      ( cdiv co wceq c1 cc wa jca wcel cc0 wne divcld divne0d rec11 syl recdivd
      wb bicomd eqeq12d bitrd ) ABCNOZDENOZPZQUMNOZQUNNOZPZCBNOZEDNOZPAURUOAUMR
      UAZUMUBUCZSZUNRUAZUNUBUCZSZSURUOUIAVCVFAVAVBABCFHIUDABCFHGIUETAVDVEADEJLM
      UDADEJLKMUETTUMUNUFUGUJAUPUSUQUTABCFHGIUHADEJLKMUHUKUL $.
  $}

  ${
    gcdmultiplei.1 $e |- M e. NN $.
    gcdmultiplei.2 $e |- N e. NN $.
    $( The GCD of a multiple of a positive integer is the positive integer
       itself.  (Contributed by metakunt, 25-Apr-2024.) $)
    gcdmultiplei $p |- ( M gcd ( M x. N ) ) = M $=
      ( cn wcel cmul co cgcd wceq gcdmultiple mp2an ) AEFBEFAABGHIHAJCDABKL $.
  $}

  ${
    gcdaddmzz2nni.1 $e |- M e. NN $.
    gcdaddmzz2nni.2 $e |- N e. NN $.
    gcdaddmzz2nni.3 $e |- K e. ZZ $.
    $( Adding a multiple of one operand of the gcd operator to the other does
       not alter the result.  (Contributed by metakunt, 25-Apr-2024.) $)
    gcdaddmzz2nni $p |- ( M gcd N ) = ( M gcd ( N + ( K x. M ) ) ) $=
      ( cz wcel w3a cgcd co cmul caddc wceq nnzi 3pm3.2i gcdaddm ax-mp ) AGHZBG
      HZCGHZIBCJKBCABLKMKJKNSTUAFBDOCEOPABCQR $.
  $}

  ${
    gcdaddmzz2nncomi.1 $e |- M e. NN $.
    gcdaddmzz2nncomi.2 $e |- N e. NN $.
    gcdaddmzz2nncomi.3 $e |- K e. ZZ $.
    $( Adding a multiple of one operand of the gcd operator to the other does
       not alter the result.  (Contributed by metakunt, 25-Apr-2024.) $)
    gcdaddmzz2nncomi $p |- ( M gcd N ) = ( M gcd ( ( K x. M ) + N ) ) $=
      ( cgcd co cmul caddc gcdaddmzz2nni nncni cz wcel zcn ax-mp mulcli addcomi
      cc oveq2i eqtri ) BCGHBCABIHZJHZGHBUBCJHZGHABCDEFKUCUDBGCUBCELABAMNASNFAO
      PBDLQRTUA $.
  $}

  ${
    gcdnncli.1 $e |- M e. NN $.
    gcdnncli.2 $e |- N e. NN $.
    $( Closure of the gcd operator.  (Contributed by metakunt, 25-Apr-2024.) $)
    gcdnncli $p |- ( M gcd N ) e. NN $=
      ( cn wcel cgcd co gcdnncl mp2an ) AEFBEFABGHEFCDABIJ $.
  $}

  ${
    muldvds1d.1 $e |- ( ph -> K e. ZZ ) $.
    muldvds1d.2 $e |- ( ph -> M e. ZZ ) $.
    muldvds1d.3 $e |- ( ph -> N e. ZZ ) $.
    muldvds1d.4 $e |- ( ph -> ( K x. M ) || N ) $.
    $( If a product divides an integer, so does one of its factors, a deduction
       version.  (Contributed by metakunt, 12-May-2024.) $)
    muldvds1d $p |- ( ph -> K || N ) $=
      ( cmul co cdvds wbr cz wcel w3a wi 3jca muldvds1 syl mpd ) ABCIJDKLZBDKLZ
      HABMNZCMNZDMNZOUAUBPAUCUDUEEFGQBCDRST $.
  $}

  ${
    muldvds2d.1 $e |- ( ph -> K e. ZZ ) $.
    muldvds2d.2 $e |- ( ph -> M e. ZZ ) $.
    muldvds2d.3 $e |- ( ph -> N e. ZZ ) $.
    muldvds2d.4 $e |- ( ph -> ( K x. M ) || N ) $.
    $( If a product divides an integer, so does one of its factors, a deduction
       version.  (Contributed by metakunt, 12-May-2024.) $)
    muldvds2d $p |- ( ph -> M || N ) $=
      ( cz wcel w3a cmul co cdvds wbr 3jca muldvds2 sylc ) ABIJZCIJZDIJZKBCLMDN
      OCDNOASTUAEFGPHBCDQR $.
  $}

  ${
    nndivdvdsd.1 $e |- ( ph -> M e. NN ) $.
    nndivdvdsd.2 $e |- ( ph -> N e. NN ) $.
    $( A positive integer divides a natural number if and only if the quotient
       is a positive integer, a deduction version of ~ nndivdvds .
       (Contributed by metakunt, 12-May-2024.) $)
    nndivdvdsd $p |- ( ph -> ( M || N <-> ( N / M ) e. NN ) ) $=
      ( cn wcel cdvds wbr cdiv co wb nndivdvds syl2anc ) ACFGBFGBCHICBJKFGLEDCB
      MN $.
  $}

  ${
    nnproddivdvdsd.1 $e |- ( ph -> K e. NN ) $.
    nnproddivdvdsd.2 $e |- ( ph -> M e. NN ) $.
    nnproddivdvdsd.3 $e |- ( ph -> N e. NN ) $.
    $( A product of natural numbers divides a natural number if and only if a
       factor divides the quotient, a deduction version.  (Contributed by
       metakunt, 12-May-2024.) $)
    nnproddivdvdsd $p |- ( ph -> ( ( K x. M ) || N <->
       K || ( N / M ) ) ) $=
      ( cmul co cdvds wbr cdiv cn wcel cc nncnd adantr nndivdvdsd cz nnzd nnne0
      wa cc0 wne syl nnne0d divdiv1d eqcomd divdiv32d eqtrd nnmulcld biimpd imp
      eqeltrrd wi 3jca muldvds2 mpbid mpbird ex dvdszrcl simprd adantl dvdsmulc
      w3a syl3an1 syl3an3 3anidm13 impancom mpd wceq divcan1d breqtrd impbid )
      ABCHIZDJKZBDCLIZJKZAVPVRAVPUBZVRVQBLIZMNVSDVOLIZVTMVSWADBLICLIZVTVSWBWAVS
      DBCADONVPADGPZQZABONVPABEPQZACONVPACFPZQZVSBMNZBUCUDAWHVPEQZBUAUEZVSCACMN
      VPFQZUFZUGUHVSDBCWDWEWGWJWLUIUJAVPWAMNZAVPWMAVODABCEFUKGRULUMUNVSBVQWIVSC
      DJKZVQMNAVPWNABSNZCSNZDSNZVEVPWNUOAWOWPWQABETZACFTZADGTUPBCDUQUEUMVSCDWKA
      DMNVPGQRURRUSUTAVRVPAVRUBZVOVQCHIZDJWTVQSNZVOXAJKZVRXBAVRWOXBBVQVAVBVCAXB
      VRXCAXBVRXCUOZAAXBWPXDWSAWOXBWPXDWRCBVQVDVFVGVHVIVJAXADVKVRADCWCWFACFUFVL
      QVMUTVN $.
  $}

  ${
    coprmdvds2d.1 $e |- ( ph -> K e. ZZ ) $.
    coprmdvds2d.2 $e |- ( ph -> M e. ZZ ) $.
    coprmdvds2d.3 $e |- ( ph -> N e. ZZ ) $.
    coprmdvds2d.4 $e |- ( ph -> ( K gcd M ) = 1 ) $.
    coprmdvds2d.5 $e |- ( ph -> K || N ) $.
    coprmdvds2d.6 $e |- ( ph -> M || N ) $.
    $( If an integer is divisible by two coprime integers, then it is divisible
       by their product, a deduction version.  (Contributed by metakunt,
       12-May-2024.) $)
    coprmdvds2d $p |- ( ph -> ( K x. M ) || N ) $=
      ( cdvds wbr cmul co cz wcel w3a cgcd c1 wa wceq wi 3jca coprmdvds2 mp2and
      jca syl ) ABDKLZCDKLZBCMNDKLZIJABOPZCOPZDOPZQZBCRNSUAZTUHUITUJUBAUNUOAUKU
      LUMEFGUCHUFDBCUDUGUE $.
  $}

  ${
    $( An image of a function under a finite set is dominated by the set.
       (Contributed by SN, 10-May-2025.) $)
    imadomfi $p |- ( ( A e. Fin /\ Fun F ) -> ( F " A ) ~<_ A ) $=
      ( wfun cfn wcel cima cdom wbr cdm wa crn df-ima wfo wfn funfn resfnfinfin
      cres sylanb dmfi syl funres funforn sylib adantr fodomfi syl2anc eqbrtrid
      wss resdmss ssdomfi mpi domtr sylan2 sylancom ancoms ) BCZADEZBAFZAGHZUPU
      QURBAQZIZGHZUSUPUQJZURUTKZVAGBALVCVADEZVAVDUTMZVDVAGHVCUTDEZVEUPBBIZNUQVG
      BOVHABPRUTSTUPVFUQUPUTCVFABUAUTUBUCUDVAVDUTUEUFUGUQVBVAAGHZUSUQVAAUHVIBAU
      IVAAUJUKURVAAULUMUNUO $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Some gcd and lcm results
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $( The gcd of 12 and 5 is 1.  (Contributed by metakunt, 25-Apr-2024.) $)
    12gcd5e1 $p |- ( ; 1 2 gcd 5 ) = 1 $=
      ( c1 c5 c2 cdc cgcd co clt wbr cr wcel wb mp2an mpbir cprime cmul 5nn 2nn
      caddc cc0 eqtr3i wceq wne wo 2lt5 olci 5re 2re 5prm 2prm gcdaddmzz2nncomi
      lttri2 prmrp nnzi mulcomnni 5t2e10 oveq1i 1nn0 0nn0 nnnn0i eqid dec0h 2cn
      1p0e1 addlidi decadd eqtri oveq2i decnncl gcdcomnni eqtr2i ) ABACDZEFZVKB
      EFBCEFZAVLVMAUAZBCUBZVOBCGHZCBGHZUCZVQVPUDUEBIJCIJVOVRKUFUGBCUKLMBNJCNJVN
      VOKUHUIBCULLMVMBCBOFZCRFZEFVLCBCPQCQUMUJVTVKBEVTASDZCRFVKVSWACRBCOFVSWABC
      PQUNUOTUPASSCACWACUQURURCQUSZWAUTCWBVAVCCVBVDVEVFVGVFTBVKPACUQQVHVIVJ $.
  $}

  ${
    $( The gcd of 60 and 6 is 6.  (Contributed by metakunt, 25-Apr-2024.) $)
    60gcd6e6 $p |- ( ; 6 0 gcd 6 ) = 6 $=
      ( c6 cc0 cdc cgcd co 6nn decnncl2 gcdcomnni c1 cmul nnnn0i 1nn0 0nn0 eqid
      6cn mullidi mul02i decmul1 10nn eqtr3i mulcomnni oveq2i gcdmultiplei
      eqtri ) AABCZDEZUEADEAAUEFAFGHUFAAIBCZJEZDEAUEUHADUGAJEUEUHIBABAUGAFKLMUG
      NAOPAOQRUGASFUATUBAUGFSUCUDT $.
  $}

  ${
    $( The gcd of 60 and 7 is 1.  (Contributed by metakunt, 25-Apr-2024.) $)
    60gcd7e1 $p |- ( ; 6 0 gcd 7 ) = 1 $=
      ( c7 c6 cc0 cdc cgcd co c1 7nn caddc 1nn0 c4 c9 oveq2i eqid c5 eqtri wcel
      ax-1cn clt wbr 6nn decnncl2 gcdcomnni cmul 1nn decnncl nnzi gcdaddmzz2nni
      7t7e49 4nn0 9nn0 4cn 4p1e5 addcomli oveq1i 5p1e6 9cn 9p1e10 decaddc2 wceq
      wne cr 7re nnnn0i dec0h 0nn0 cle 7lt9 wa wi pm3.2i ltle ax-mp 0lt1 declth
      9re eqbrtri ltne mp2an necom mpbir cprime wb 7prm 11prm prmrp eqtr3i ) AB
      CDZEFZWHAEFGAWHHBUAUBUCAGGDZEFZWIGWKAWJAAUDFZIFZEFWIAAWJHGGJUEUFAHUGUHWMW
      HAEWMWJKLDZIFWHWLWNWJIUIMGGKLBWJWNJJUJUKWJNWNNGKIFZGIFOGIFBWOOGIKGOULRUMU
      NUOUPPLGGCDUQRURUNUSPMPWKGUTZAWJVAZWQWJAVAZAVBQZAWJSTWRVCACADWJSAAHVDZVEC
      GAGVFJWTJALSTZALVGTZVHWSLVBQZVIXAXBVJWSXCVCVPVKALVLVMVMVNVOVQAWJVRVSAWJVT
      WAAWBQWJWBQWPWQWCWDWEAWJWFVSWAWGWG $.
  $}

  ${
    $( The gcd of 420 and 8 is 4.  (Contributed by metakunt, 25-Apr-2024.) $)
    420gcd8e4 $p |- ( ; ; 4 2 0 gcd 8 ) = 4 $=
      ( c8 c4 cgcd co c2 cdc cc0 c5 cmul caddc 8nn 4nn 5nn0 2nn decnncl c1 4nn0
      c6 1nn0 eqtr3i nnzi gcdaddmzz2nncomi deccl 6nn0 0nn0 dec0h nn0cni addridi
      eqid 1p1e2 decsuc 6p4e10 decaddc2 8nn0 2nn0 0p1e1 8t5e40 8t2e16 mulcomnni
      decmul2c oveq1i oveq2i eqtr4i gcdcomnni 4t2e8 gcdmultiplei eqtri decnncl2
      3eqtr3ri ) ABCDZABEFZGFZCDZBVLACDVJAHEFZAIDZBJDZCDVMVNABKLVNHEMNOZUAUBVLV
      PACBPFZRFZBJDVLVPVRRGBVKVSBBPQSUCZUDUEQVSUIBQUFBPEVRGJDQSUJVRVRVTUGUHUKUL
      UMVSVOBJAVNIDVSVOHEVRRAPVNUNMUOVNUIUDSBGPAHIDQUEUPUQUKURUTAVNKVQUSTVATVBV
      CVJBACDZBABKLVDBBEIDZCDWABWBABCVEVBBELNVFTVGAVLKVKBEQNOVHVDVI $.
  $}

  ${
    lcmeprodgcdi.1 $e |- M e. NN $.
    lcmeprodgcdi.2 $e |- N e. NN $.
    lcmeprodgcdi.3 $e |- G e. NN $.
    lcmeprodgcdi.4 $e |- H e. NN $.
    lcmeprodgcdi.5 $e |- ( M gcd N ) = G $.
    lcmeprodgcdi.6 $e |- ( G x. H ) = A $.
    lcmeprodgcdi.7 $e |- ( M x. N ) = A $.
    $( Calculate the least common multiple of two natural numbers.
       (Contributed by metakunt, 25-Apr-2024.) $)
    lcmeprodgcdi $p |- ( M lcm N ) = H $=
      ( co cmul wceq cn wcel eqtr4i cc wa clcm cgcd oveq2i lcmgcdnn mp2an eqtri
      mulcomnni eqtr3i cc0 wne w3a wb cn0 nnzi pm3.2i lcmcl ax-mp nn0cni nnne0i
      cz nncni 3pm3.2i mulcan2 mpbi ) DEUAMZBNMZCBNMZOZVECOZVEDEUBMZNMZVFVGVJBV
      ENJUCVKBCNMZVGVKDENMZVLDPQEPQVKVMOFGDEUDUEVLAVMKLRRBCHIUGUFUHVESQZCSQZBSQ
      ZBUIUJZTZUKVHVIULVNVOVRVEDUTQZEUTQZTVEUMQVSVTDFUNEGUNUODEUPUQURCIVAVPVQBH
      VABHUSUOVBVECBVCUQVD $.
  $}

  ${
    $( The lcm of 12 and 5 is 60.  (Contributed by metakunt, 25-Apr-2024.) $)
    12lcm5e60 $p |- ( ; 1 2 lcm 5 ) = ; 6 0 $=
      ( c6 cc0 cdc c1 c2 c5 1nn0 2nn decnncl 5nn 1nn 6nn decnncl2 12gcd5e1 6nn0
      0nn0 mullidi co caddc 5cn deccl nn0cni 5nn0 2nn0 eqid oveq1i 5p1e6 5t2e10
      cmul eqtri 2cn mulcomli decmul1c lcmeprodgcdi ) ABCZDUODECZFDEGHIJKALMNUO
      UOABOPUAUBQDEABFDUPUCGUDUPUEPGDFUIRZDSRFDSRAUQFDSFTQUFUGUJFEDBCTUKUHULUMU
      N $.
  $}

  ${
    $( The lcm of 60 and 6 is 60.  (Contributed by metakunt, 25-Apr-2024.) $)
    60lcm6e60 $p |- ( ; 6 0 lcm 6 ) = ; 6 0 $=
      ( c6 cc0 cdc cmul co 6nn decnncl2 60gcd6e6 eqid mulcomnni lcmeprodgcdi )
      AABCZDEZALLAAFGZFFNHMILANFJK $.
  $}

  ${
    $( The lcm of 60 and 7 is 420.  (Contributed by metakunt, 25-Apr-2024.) $)
    60lcm7e420 $p |- ( ; 6 0 lcm 7 ) = ; ; 4 2 0 $=
      ( c4 c2 cdc cc0 c1 c6 c7 6nn decnncl2 7nn 1nn 4nn0 2nn 2nn0 deccl 0nn0 co
      cmul 7cn mulcomli decnncl 60gcd7e1 nn0cni mullidi 7nn0 6cn 7t6e42 addridi
      6nn0 eqid 2cn decaddi mul01i dec0h eqcomi eqtr4i decmul1c lcmeprodgcdi
      0cn ) ABCZDCZEVAFDCZGFHIJKUTABLMUAIUBVAVAUTDABLNOPOUCUDFDUTDGDVBUEUIPVBUJ
      PPABBFGRQDLNPGFUTSUFUGTBUKUHULGDDDCZSUSGDRQDVCGSUMDVCDPUNUOUPTUQUR $.
  $}

  ${
    $( The lcm of 420 and 8 is 840.  (Contributed by metakunt, 25-Apr-2024.) $)
    420lcm8e840 $p |- ( ; ; 4 2 0 lcm 8 ) = ; ; 8 4 0 $=
      ( c4 c8 cdc cc0 cmul co c2 4nn0 2nn decnncl decnncl2 8nn 8nn0 eqid oveq1i
      4nn eqtr4i eqtri 0nn0 caddc 420gcd8e4 mulcomnni 4t2e8 mulassnni 2t4e8 8cn
      nnnn0i addridi 2t2e4 dec0h eqcomi decmul2c 4cn decaddi 2t0e0 lcmeprodgcdi
      oveq2i ) ABACZDCZEFZAUSAGCZDCZBVAAGHIJZKZLPURBAMPJKUAUTNVBBEFZAGVBEFZEFZU
      TVEAGEFZVBEFZVGVEBVBEFVIVBBVDLUBVHBVBEUCOQAGVBPIVDUDRVFUSAEVADURDGDVBGIUG
      ZVAVCUGSVBNSSBAAGVAEFDMHSAGBAGDVAVJHVJVANHSGAEFZDTFBDTFBVKBDTUEOBUFUHRGGE
      FADACZUIAVLAHUJUKQULAUMUHUNGDEFDDDCZUODVMDSUJUKQULUQRUP $.
  $}

  ${
    lcmfunnnd.1 $e |- ( ph -> N e. NN ) $.
    $( Useful equation to calculate the least common multiple of 1 to n.
       (Contributed by metakunt, 29-Apr-2024.) $)
    lcmfunnnd $p |- ( ph -> ( _lcm ` ( 1 ... N ) ) =
      ( ( _lcm ` ( 1 ... ( N - 1 ) ) ) lcm N ) ) $=
      ( c1 cfz co clcmf cfv cmin csn cun cuz wcel wceq cc0 cn0 syl eleq2i a1i
      cz clcm caddc nncnd npcand oveq2d cn nnm1nn0 nn0uz sylib wb fveq2i mpbird
      1cnd 1m1e0 fzsuc2 mpan eqtr3d sneqd uneq2d eqtrd fveq2d wss cfn w3a fzssz
      1z fzfi nnz 3jca lcmfunsn ) ADBEFZGHDBDIFZEFZBJZKZGHZVMGHBUAFZAVKVOGAVKVM
      VLDUBFZJZKZVOADVREFZVKVTAVRBDEABDABCUCAUMUDZUEAVLDDIFZLHZMZWAVTNZAWEVLOLH
      ZMZAVLPMZWHABUFMZWICBUGQPWGVLUHRUIWEWHUJAWDWGVLWCOLUNUKRSULDTMWEWFVFDVLUO
      UPQUQAVSVNVMAVRBWBURUSUTVAAVMTVBZVMVCMZBTMZVDVPVQNAWKWLWMWKADVLVESWLADVLV
      GSAWJWMCBVHQVIBVMVJQUT $.
  $}

  ${
    $( Least common multiple of natural numbers up to 1 equals 1.  (Contributed
       by metakunt, 25-Apr-2024.) $)
    lcm1un $p |- ( _lcm ` ( 1 ... 1 ) ) = 1 $=
      ( c1 cfz co clcmf cfv cmin clcm cn wcel wceq 1nn id lcmfunnnd ax-mp 1m1e0
      c0 cc0 oveq2i fz10 eqtri fveq2i lcmf0 oveq1i cabs cz 1z lcmid abs1 ) AABC
      DEZAAAFCZBCZDEZAGCZAAHIZUIUMJKUNAUNLMNUMAAGCZAULAAGULPDEAUKPDUKAQBCPUJQAB
      ORSTUAUBTUCUOAUDEZAAUEIUOUPJUFAUGNUHTTT $.
  $}

  ${
    $( Least common multiple of natural numbers up to 2 equals 2.  (Contributed
       by metakunt, 25-Apr-2024.) $)
    lcm2un $p |- ( _lcm ` ( 1 ... 2 ) ) = 2 $=
      ( c1 c2 cfz co clcmf cfv clcm cmin cn wcel wceq 2nn lcmfunnnd ax-mp 2m1e1
      id oveq1i eqtri cz 2z oveq2i fveq2i lcm1un lcmcom mp2an cabs lcm1 cc0 cle
      1z cr wbr wa 2re 0le2 pm3.2i absid ) ABCDEFZAACDZEFZBGDZBURABAHDZCDZEFZBG
      DZVABIJZURVEKLVFBVFPMNVDUTBGVCUSEVBAACOUAUBQRVAABGDZBUTABGUCQVGBAGDZBASJB
      SJZVGVHKUJTABUDUEVHBUFFZBVIVHVJKTBUGNBUKJZUHBUIULZUMVJBKVKVLUNUOUPBUQNRRR
      R $.
  $}

  ${
    $( Least common multiple of natural numbers up to 3 equals 6.  (Contributed
       by metakunt, 25-Apr-2024.) $)
    lcm3un $p |- ( _lcm ` ( 1 ... 3 ) ) = 6 $=
      ( c1 c3 cfz co clcmf cfv cmin clcm c6 cn wcel wceq 3nn id lcmfunnnd ax-mp
      c2 3m1e2 eqtri cz oveq2i fveq2i lcm2un oveq1i wa 2z pm3.2i lcmcom 3lcm2e6
      3z ) ABCDEFZABAGDZCDZEFZBHDZIBJKZUKUOLMUPBUPNOPUOQBHDZIUNQBHUNAQCDZEFQUMU
      REULQACRUAUBUCSUDUQBQHDZIQTKZBTKZUEUQUSLUTVAUFUJUGQBUHPUISSS $.
  $}

  ${
    $( Least common multiple of natural numbers up to 4 equals 12.
       (Contributed by metakunt, 25-Apr-2024.) $)
    lcm4un $p |- ( _lcm ` ( 1 ... 4 ) ) = ; 1 2 $=
      ( c1 c4 cfz co clcmf cfv cmin clcm c6 c2 cdc cn wcel wceq lcmfunnnd ax-mp
      4nn id c3 4m1e3 oveq2i fveq2i lcm3un eqtri oveq1i 6lcm4e12 3eqtri ) ABCDE
      FZABAGDZCDZEFZBHDZIBHDAJKBLMZUHULNQUMBUMROPUKIBHUKASCDZEFIUJUNEUISACTUAUB
      UCUDUEUFUG $.
  $}

  ${
    $( Least common multiple of natural numbers up to 5 equals 60.
       (Contributed by metakunt, 25-Apr-2024.) $)
    lcm5un $p |- ( _lcm ` ( 1 ... 5 ) ) = ; 6 0 $=
      ( c1 c5 cfz co clcmf cfv cmin clcm c2 cdc cc0 wcel wceq 5nn a1i lcmfunnnd
      c6 cn c4 oveq1i ax-mp 5m1e4 oveq2i fveq2i lcm4un eqtri 12lcm5e60 3eqtri )
      ABCDEFZABAGDZCDZEFZBHDZAIJZBHDZQKJBRLZUIUMMNUPBUPUPNOPUAUMASCDZEFZBHDUOUL
      URBHUKUQEUJSACUBUCUDTURUNBHUETUFUGUH $.
  $}

  ${
    $( Least common multiple of natural numbers up to 6 equals 60.
       (Contributed by metakunt, 25-Apr-2024.) $)
    lcm6un $p |- ( _lcm ` ( 1 ... 6 ) ) = ; 6 0 $=
      ( c1 c6 cfz co clcmf cfv cmin clcm cc0 cdc cn wcel wceq 6nn a1i lcmfunnnd
      ax-mp c5 6m1e5 oveq1i oveq2i fveq2i lcm5un eqtri 60lcm6e60 3eqtri ) ABCDE
      FZABAGDZCDZEFZBHDZBIJZBHDZULBKLZUGUKMNUNBUNUNNOPQUKARCDZEFZBHDUMUJUPBHUIU
      OEUHRACSUAUBTUPULBHUCTUDUEUF $.
  $}

  ${
    $( Least common multiple of natural numbers up to 7 equals 420.
       (Contributed by metakunt, 25-Apr-2024.) $)
    lcm7un $p |- ( _lcm ` ( 1 ... 7 ) ) = ; ; 4 2 0 $=
      ( c1 c7 cfz co clcmf cfv cmin clcm c6 cc0 cdc c4 c2 cn wcel 7nn lcmfunnnd
      wceq id oveq1i ax-mp 7m1e6 oveq2i fveq2i lcm6un eqtri 60lcm7e420 3eqtri )
      ABCDEFZABAGDZCDZEFZBHDZIJKZBHDZLMKJKBNOZUIUMRPUPBUPSQUAUMAICDZEFZBHDUOULU
      RBHUKUQEUJIACUBUCUDTURUNBHUETUFUGUH $.
  $}

  ${
    $( Least common multiple of natural numbers up to 8 equals 840.
       (Contributed by metakunt, 25-Apr-2024.) $)
    lcm8un $p |- ( _lcm ` ( 1 ... 8 ) ) = ; ; 8 4 0 $=
      ( c1 c8 cfz co clcmf cfv cmin clcm c4 c2 cdc cc0 cn wcel 8nn id lcmfunnnd
      wceq c7 oveq1i ax-mp 8m1e7 oveq2i fveq2i lcm7un eqtri 420lcm8e840 3eqtri
      ) ABCDEFZABAGDZCDZEFZBHDZIJKLKZBHDZBIKLKBMNZUIUMROUPBUPPQUAUMASCDZEFZBHDU
      OULURBHUKUQEUJSACUBUCUDTURUNBHUETUFUGUH $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Least common multiple inequality theorem
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d A k x $.  $d A q r x $.  $d B k x $.  $d F q r $.  $d G q r x $.
    $d H q r $.  $d L q r $.  $d U q r $.  $d k ph x $.  $d ph q x $.
    3factsumint1.1 $e |- A = ( L [,] U ) $.
    3factsumint1.2 $e |- ( ph -> B e. Fin ) $.
    3factsumint1.3 $e |- ( ph -> L e. RR ) $.
    3factsumint1.4 $e |- ( ph -> U e. RR ) $.
    3factsumint1.5 $e |- ( ( ph /\ x e. A ) -> F e. CC ) $.
    3factsumint1.6 $e |- ( ph -> ( x e. A |-> F ) e. ( A -cn-> CC ) ) $.
    3factsumint1.7 $e |- ( ( ph /\ k e. B ) -> G e. CC ) $.
    3factsumint1.8 $e |- ( ( ph /\ ( x e. A /\ k e. B ) ) -> H e. CC ) $.
    3factsumint1.9 $e |- ( ( ph /\ k e. B ) -> ( x e. A |-> H ) e.
     ( A -cn-> CC ) ) $.
    $( Move constants out of integrals or sums and/or commute sum and integral.
       (Contributed by metakunt, 26-Apr-2024.) $)
    3factsumint1 $p  |- ( ph -> S. A sum_ k e. B ( F x. ( G x. H ) ) _d x =
       sum_ k e. B S. A ( F x. ( G x. H ) ) _d x ) $=
      ( wcel vr vq cmul co csu cmpt cibl citg wceq cicc cvol cdm iccmbl syl2anc
      cc cr eqeltrid cv wa adantrr adantrl mulcld cof cvv ovex eqeltri anass1rs
      a1i eqidd offval2 cmbf cfv cabs cle wral ccncf cnmbf adantr oveq1i eleq2i
      wbr sylib cnicciblnc syl3anc iblmulc2 cniccbdd wb ralrimiva dmmptg eqtrdi
      wrex syl raleqdv rexbidv mpbird bddmulibl eqeltrrd itgfsum simprd ) ABCDG
      HIUCUDZUCUDZFUEZUFUGTBCXBUHDBCXAUHFUEUIABCDXAFUOACJEUJUDZUKULZKAJUPTZEUPT
      ZXCXDTMNJEUMUNUQZLABURCTZFURDTZUSUSZGWTAXHGUOTZXIOUTZXJHIAXIHUOTXHQVARVBZ
      VBAXIUSZBCGUFZBCWTUFZUCVCUDZBCXAUFUGXNBCGWTUCXOXPVDUOUOCVDTXNCXCVDKJEUJVE
      VFVHAXHXIXKXLVGAXHXIWTUOTXMVGXNXOVIXNXPVIVJXNXOVKTZXPUGTUAURXOVLVMVLUBURV
      NWAZUAXOULZVOZUBUPWKZXQUGTAXRXIACXDTXOCUOVPUDZTZXRXGPCXOVQUNVRXNBCIHUOQAX
      HXIIUOTRVGXNXEXFBCIUFZXCUOVPUDZTZYEUGTAXEXIMVRAXFXINVRXNYEYCTYGSYCYFYECXC
      UOVPKVSZVTWBJEYEWCWDWEXNYBXSUAXCVOZUBUPWKZAYJXIAXEXFXOYFTZYJMNAYDYKPYCYFX
      OYHVTWBUBUAJEXOWFWDVRAYBYJWGXIAYAYIUBUPAXSUAXTXCAXTCXCAXKBCVOXTCUIAXKBCOW
      HBCGUOWIWLKWJWMWNVRWOUBUAXOXPWPWDWQWRWS $.
  $}

  ${
    $d B k x $.  $d k ph x $.
    3factsumint2.1 $e |- ( ( ph /\ x e. A ) -> F e. CC ) $.
    3factsumint2.2 $e |- ( ( ph /\ k e. B ) -> G e. CC ) $.
    3factsumint2.3 $e |- ( ( ph /\ ( x e. A /\ k e. B ) ) -> H e. CC ) $.
    $( Move constants out of integrals or sums and/or commute sum and integral.
       (Contributed by metakunt, 26-Apr-2024.) $)
    3factsumint2 $p  |- ( ph -> sum_ k e. B S. A ( F x. ( G x. H ) ) _d x =
       sum_ k e. B S. A ( G x. ( F x. H ) ) _d x ) $=
      ( cmul co citg cv wcel wa cc adantlr wi adantr ancom anbi2i bicomi imbi1i
      anass bitri mpbi mul12d itgeq2dv sumeq2dv ) ADBCFGHLMLMZNBCGFHLMLMZNEAEOD
      PZQZBCULUMUOBOCPZQZFGHAUPFRPUNISUOGRPUPJUAAUPUNQZQZHRPZTUQUTTKUSUQUTUSAUN
      UPQZQZUQURVAAUPUNUBUCUQVBAUNUPUFUDUGUEUHUIUJUK $.
  $}

  ${
    $d A x $.  $d B k x $.  $d G x $.  $d k ph x $.
    3factsumint3.1 $e |- A = ( L [,] U ) $.
    3factsumint3.2 $e |- ( ph -> L e. RR ) $.
    3factsumint3.3 $e |- ( ph -> U e. RR ) $.
    3factsumint3.4 $e |- ( ( ph /\ x e. A ) -> F e. CC ) $.
    3factsumint3.5 $e |- ( ph -> ( x e. A |-> F ) e. ( A -cn-> CC ) ) $.
    3factsumint3.6 $e |- ( ( ph /\ k e. B ) -> G e. CC ) $.
    3factsumint3.7 $e |- ( ( ph /\ ( x e. A /\ k e. B ) ) -> H e. CC ) $.
    3factsumint3.8 $e |- ( ( ph /\ k e. B ) -> ( x e. A |-> H ) e.
     ( A -cn-> CC ) ) $.
    $( Move constants out of integrals or sums and/or commute sum and integral.
       (Contributed by metakunt, 26-Apr-2024.) $)
    3factsumint3 $p  |- ( ph -> sum_ k e. B S. A ( G x. ( F x. H ) ) _d x
    = sum_ k e. B ( G x. S. A ( F x. H ) _d x ) ) $=
      ( co wcel cmul cv wa cc adantlr wi ancom anbi2i anass bicomi bitri imbi1i
      citg mpbi mulcld cr cmpt cicc ccncf cibl adantr mulcncf oveq1i cnicciblnc
      eleqtrdi syl3anc itgmulc2 eqcomd sumeq2dv ) ADBCHGIUASZUASUMZHBCVJUMUASZF
      AFUBDTZUCZVLVKVNBCVJHUDPVNBUBCTZUCZGIAVOGUDTVMNUEAVOVMUCZUCZIUDTZUFVPVSUF
      QVRVPVSVRAVMVOUCZUCZVPVQVTAVOVMUGUHVPWAAVMVOUIUJUKULUNUOVNJUPTZEUPTZBCVJU
      QZJEURSZUDUSSZTWDUTTAWBVMLVAAWCVMMVAVNWDCUDUSSZWFVNBGICABCGUQWGTVMOVARVBC
      WEUDUSKVCVEJEWDVDVFVGVHVI $.
  $}

  ${
    $d A k $.  $d B k $.  $d F k $.  $d k ph x $.
    3factsumint4.1 $e |- ( ph -> B e. Fin ) $.
    3factsumint4.2 $e |- ( ( ph /\ x e. A ) -> F e. CC ) $.
    3factsumint4.3 $e |- ( ( ph /\ k e. B ) -> G e. CC ) $.
    3factsumint4.4 $e |- ( ( ph /\ ( x e. A /\ k e. B ) ) -> H e. CC ) $.
    $( Move constants out of integrals or sums and/or commute sum and integral.
       (Contributed by metakunt, 26-Apr-2024.) $)
    3factsumint4 $p |- ( ph -> S. A sum_ k e. B ( F x. ( G x. H ) ) _d x =
       S. A ( F x. sum_ k e. B ( G x. H ) ) _d x ) $=
      ( cmul co csu cv wcel wa cc wi cfn adantr anass bicomi imbi1i mpbi mulcld
      adantlr fsummulc2 eqcomd itgeq2dv ) ABCDFGHMNZMNEOZFDULEOMNZABPCQZRZUNUMU
      PDULFEADUAQUOIUBJUPEPDQZRZGHAUQGSQUOKUHAUOUQRRZHSQZTURUTTLUSURUTURUSAUOUQ
      UCUDUEUFUGUIUJUK $.
  $}

  ${
    $d A k x $.  $d B k x $.  $d F k $.  $d G x $.  $d k ph x $.
    3factsumint.1 $e |- A = ( L [,] U ) $.
    3factsumint.2 $e |- ( ph -> B e. Fin ) $.
    3factsumint.3 $e |- ( ph -> L e. RR ) $.
    3factsumint.4 $e |- ( ph -> U e. RR ) $.
    3factsumint.5 $e |- ( ph -> ( x e. A |-> F ) e. ( A -cn-> CC ) ) $.
    3factsumint.6 $e |- ( ( ph /\ k e. B ) -> G e. CC ) $.
    3factsumint.7 $e |- ( ( ph /\ k e. B ) -> ( x e. A |-> H ) e.
     ( A -cn-> CC ) ) $.
    $( Helpful equation for lcm inequality proof.  (Contributed by metakunt,
       26-Apr-2024.) $)
    3factsumint $p  |- ( ph -> S. A ( F x. sum_ k e. B ( G x. H ) ) _d x =
       sum_ k e. B ( G x. S. A ( F x. H ) _d x ) ) $=
      ( cmul co cc csu citg wcel cmpt wral ccncf cncff syl eqid sylibr r19.21bi
      wf fmpt cv wa wi anass ancom anbi2i imbi1i mpbi 3factsumint4 3factsumint1
      bitri eqtr3d 3factsumint2 3factsumint3 3eqtrd ) ABCGDHIRSZFUARSUBZDBCGVIR
      SZUBFUAZDBCHGIRSZRSUBFUADHBCVMUBRSFUAABCDVKFUAUBVJVLABCDFGHILAGTUCZBCACTB
      CGUDZULZVNBCUEAVOCTUFSZUCVPOCTVOUGUHBCTGVOVOUIUMUJUKZPAFUNDUCZUOZBUNCUCZU
      OZITUCZUPAWAVSUOZUOZWCUPVTWCBCVTCTBCIUDZULZWCBCUEVTWFVQUCWGQCTWFUGUHBCTIW
      FWFUIUMUJUKWBWEWCWBAVSWAUOZUOWEAVSWAUQWHWDAVSWAURUSVDUTVAZVBABCDEFGHIJKLM
      NVROPWIQVCVEABCDFGHIVRPWIVFABCDEFGHIJKMNVROPWIQVGVH $.
  $}

  ${
    resopunitintvd.1 $e |- ( ph -> ( x e. CC |-> A ) e. ( CC -cn-> CC ) ) $.
    $( Restrict continuous function on open unit interval.  (Contributed by
       metakunt, 12-May-2024.) $)
    resopunitintvd $p |- ( ph -> ( x e. ( 0 (,) 1 ) |-> A )
     e. ( ( 0 (,) 1 ) -cn-> CC ) ) $=
      ( cc0 c1 cioo co cmpt cc cres ccncf wss wceq ioosscn resmpt ax-mp wcel wi
      rescncf syl eqeltrrid ) ABEFGHZCIZBJCIZUCKZUCJLHZUCJMZUFUDNEFOZBJUCCPQAUE
      JJLHRZUFUGRZDUHUJUKSUIJJUCUETQUAUB $.
  $}

  ${
    resclunitintvd.1 $e |- ( ph -> ( x e. CC |-> A ) e. ( CC -cn-> CC ) ) $.
    $( Restrict continuous function on closed unit interval.  (Contributed by
       metakunt, 12-May-2024.) $)
    resclunitintvd $p |- ( ph -> ( x e. ( 0 [,] 1 ) |-> A )
     e. ( ( 0 [,] 1 ) -cn-> CC ) ) $=
      ( cc0 c1 cicc co cmpt cc cres ccncf wss wceq unitsscn resmpt wcel rescncf
      ax-mp wi syl eqeltrrid ) ABEFGHZCIZBJCIZUCKZUCJLHZUCJMZUFUDNOBJUCCPSAUEJJ
      LHQZUFUGQZDUHUIUJTOJJUCUERSUAUB $.
  $}

  ${
    $d ph x $.
    resdvopclptsd.1 $e |- ( ph -> ( CC _D ( x e. CC |-> A ) ) =
    ( x e. CC |-> B ) ) $.
    resdvopclptsd.2 $e |- ( ( ph /\ x e. CC ) -> A e. CC ) $.
    resdvopclptsd.3 $e |- ( ( ph /\ x e. CC ) -> B e. CC ) $.
    $( Restrict derivative on unit interval.  (Contributed by metakunt,
       12-May-2024.) $)
    resdvopclptsd $p |- ( ph -> ( RR _D ( x e. ( 0 [,] 1 ) |-> A ) ) =
    ( x e. ( 0 (,) 1 ) |-> B ) ) $=
      ( cc0 c1 cc cmpt eqid 0red 1red dvmptresicc ) ABCDHIBJCKZPLFEGAMANO $.
  $}

  ${
    $d M k $.  $d N k $.  $d k ph x $.
    lcmineqlem1.1 $e |- F = S. ( 0 [,] 1 ) ( ( x ^ ( M - 1 ) ) x.
     ( ( 1 - x ) ^ ( N - M ) ) ) _d x $.
    lcmineqlem1.2 $e |- ( ph -> N e. NN ) $.
    lcmineqlem1.3 $e |- ( ph -> M e. NN ) $.
    lcmineqlem1.4 $e |- ( ph -> M <_ N ) $.
    $( Part of lcm inequality lemma, this part eventually shows that F times
       the least common multiple of 1 to n is an integer.  (Contributed by
       metakunt, 29-Apr-2024.) $)
    lcmineqlem1 $p |- ( ph -> F = S. ( 0 [,] 1 ) ( ( x ^ ( M - 1 ) ) x.
     sum_ k e. ( 0 ... ( N - M ) ) ( ( ( -u 1 ^ k ) x.
       ( ( N - M ) _C k ) ) x. ( x ^ k ) ) ) _d x ) $=
      ( c1 co cmin cexp cmul wcel cc wceq cn0 cz cc0 cicc citg cfz cneg cbc csu
      cv wa elunitcn caddc ax-1cn negsub mpan oveq1d adantl negcl wi cle wbr wb
      1cnd nnnn0d nn0sub syl2anc mpbid binom 3com23 3expia syl5 imp w3a elfzelz
      eqtr3d nnzd zsubcl sylan 1exp syl 3adant2 3ad2ant2 elfznn0 3ad2ant3 expcl
      sylan2 mullidd eqtrd mulm1 eqtr4d neg1cn mulexp mp3an1 oveq2d bccl syl2an
      3adant1 nn0cnd sylancr mulassd mulcomd 3expa sumeq2dv itgeq2dv eqtrid ) A
      DBUAKUBLZBUHZEKMLNLZKXFMLZFEMLZNLZOLZUCBXEXGUAXIUDLZKUEZCUHZNLZXIXNUFLZOL
      ZXFXNNLZOLZCUGZOLZUCGABXEXKYAAXFXEPZUIXJXTXGOYBAXFQPZXJXTRXFUJAYCUIZXJXLX
      PKXIXNMLZNLZXFUEZXNNLZOLZOLZCUGZXTYDKYGUKLZXINLZXJYKYCYMXJRAYCYLXHXINKQPZ
      YCYLXHRULKXFUMUNUOUPAYCYMYKRZYCYGQPZAYOXFUQZAYNXISPZYPYOURAVBAEFUSUTZYRJA
      ESPFSPYSYRVAAEIVCAFHVCEFVDVEVFZYNYRYPYOYNYPYRYOKYGCXIVGVHVIVEVJVKVNYDXLYJ
      XSCAYCXNXLPZYJXSRAYCUUAVLZYJXPXOOLZXROLZXSUUBYJXPXOXROLZOLUUDUUBYIUUEXPOU
      UBYIXMXFOLZXNNLZUUEUUBYIYHUUGUUBYIKYHOLYHUUBYFKYHOAUUAYFKRZYCAUUAUIYETPZU
      UHUUAAXNTPZUUIXNUAXIVMZAXITPZUUJUUIAFTPETPUULAFHVOAEIVOFEVPVEXIXNVPVQWEYE
      VRVSVTUOUUBYHUUBYPXNSPZYHQPYCAYPUUAYQWAUUAAUUMYCXNXIWBZWCZYGXNWDVEWFWGYCA
      UUGYHRUUAYCUUFYGXNNXFWHUOWAWIYCUUAUUGUUERZAUUAYCUUMUUPUUNXMQPZYCUUMUUPWJX
      MXFXNWKWLWEWPWGWMUUBXPXOXRUUBXPAUUAXPSPZYCAYRUUJUURUUAYTUUKXNXIWNWOVTWQZU
      UBUUQUUMXOQPWJUUOXMXNWDWRZYCUUAXRQPZAUUAYCUUMUVAUUNXFXNWDWEWPWSWIUUBUUCXQ
      XROUUBXPXOUUSUUTWTUOWGXAXBWGWEWMXCXD $.
  $}

  ${
    $d M k x $.  $d N k x $.  $d k ph x $.
    lcmineqlem2.1 $e |- F = S. ( 0 [,] 1 ) ( ( x ^ ( M - 1 ) ) x.
     ( ( 1 - x ) ^ ( N - M ) ) ) _d x $.
    lcmineqlem2.2 $e |- ( ph -> N e. NN ) $.
    lcmineqlem2.3 $e |- ( ph -> M e. NN ) $.
    lcmineqlem2.4 $e |- ( ph -> M <_ N ) $.
    $( Part of lcm inequality lemma, this part eventually shows that F times
       the least common multiple of 1 to n is an integer.  (Contributed by
       metakunt, 29-Apr-2024.) $)
    lcmineqlem2 $p |- ( ph -> F = sum_ k
                           e. ( 0 ... ( N - M ) )
                                ( ( ( -u 1 ^ k ) x. ( ( N - M ) _C k ) )
                                  x.
                                  S. ( 0 [,] 1 )
                                     ( ( x ^ ( M - 1 ) ) x. ( x ^ k ) )
                                  _d x ) ) $=
      ( cc0 c1 co cmul cmpt cc unitsscn ax-mp wcel cn0 cicc cv cmin cfz cbc csu
      cexp cneg citg lcmineqlem1 eqid fzfid 0red 1red cres ccncf wceq resmpt cn
      wss nnm1nn0 expcncf wi rescncf 4syl eqeltrrid wa elfznn0 neg1cn expcl syl
      mpan adantl cle wbr wb nnnn0d nn0sub syl2anc mpbid nn0z bccl sylan2 sylan
      cz nn0cnd mulcld 3factsumint eqtrd ) ADBKLUAMZBUBZELUCMZUGMZKFEUCMZUDMZLU
      HZCUBZUGMZWNWQUEMZNMZWKWQUGMZNMCUFNMUIWOWTBWJWMXANMUINMCUFABCDEFGHIJUJABW
      JWOLCWMWTXAKWJUKAKWNULAUMAUNABWJWMOZBPWMOZWJUOZWJPUPMZWJPUTZXDXBUQQBPWJWM
      URRAEUSSWLTSXCPPUPMZSZXDXESZIEVABWLVBXFXHXIVCQPPWJXCVDRVEVFAWQWOSZVGZWRWS
      XJWRPSZAXJWQTSZXLWQWNVHZWPPSXMXLVIWPWQVJVLVKVMXKWSAWNTSZXJWSTSZAEFVNVOZXO
      JAETSFTSXQXOVPAEIVQAFHVQEFVRVSVTXJXOWQWESZXPXJXMXRXNWQWAVKWQWNWBWCWDWFWGX
      JBWJXAOZXESAXJXSBPXAOZWJUOZXEXFYAXSUQQBPWJXAURRXJXTXGSZYAXESZXJXMYBXNBWQV
      BVKXFYBYCVCQPPWJXTVDRVKVFVMWHWI $.
  $}

  ${
    $d M k x $.  $d N k x $.  $d k ph x $.
    lcmineqlem3.1 $e |- F = S. ( 0 [,] 1 ) ( ( x ^ ( M - 1 ) ) x.
     ( ( 1 - x ) ^ ( N - M ) ) ) _d x $.
    lcmineqlem3.2 $e |- ( ph -> N e. NN ) $.
    lcmineqlem3.3 $e |- ( ph -> M e. NN ) $.
    lcmineqlem3.4 $e |- ( ph -> M <_ N ) $.
    $( Part of lcm inequality lemma, this part eventually shows that F times
       the least common multiple of 1 to n is an integer.  (Contributed by
       metakunt, 30-Apr-2024.) $)
    lcmineqlem3 $p |- ( ph -> F = sum_ k
                           e. ( 0 ... ( N - M ) )
                                ( ( ( -u 1 ^ k ) x. ( ( N - M ) _C k ) )
                                  x.
                                  ( 1 / ( M + k ) ) ) ) $=
      ( cc0 cmin co c1 cexp cmul csu wcel syl oveq2d cfz cneg cv cbc cicc caddc
      citg cdiv lcmineqlem2 wa w3a cc elunitcn 3ad2ant3 cn0 elfznn0 3ad2ant2 cn
      wceq nnm1nn0 3ad2ant1 expaddd 3expa itgeq2dv sumeq2dv 0red cle wbr adantr
      1red 0le1 adantl nn0addcld itgpowd nncnd nn0cn nppcand oveq12d nnnn0addcl
      a1i 1cnd cz syl2anc nnzd 1exp 0exp eqtrd 1m0e1 eqtrdi 3eqtr2d ) ADKFELMZU
      AMZNUBCUCZOMWKWMUDMPMZBKNUEMZBUCZENLMZOMWPWMOMPMZUGZPMZCQWLWNBWOWPWQWMUFM
      ZOMZUGZPMZCQWLWNNEWMUFMZUHMZPMZCQABCDEFGHIJUIAWLXDWTCAWMWLRZUJZXCWSWNPXIB
      WOXBWRAXHWPWORZXBWRUSAXHXJUKWPWQWMXJAWPULRXHWPUMUNXHAWMUORZXJWMWKUPZUQAXH
      WQUORZXJAEURRZXMIEUTSZVAVBVCVDTVEAWLXDXGCXIXCXFWNPXIXCNXANUFMZOMZKXPOMZLM
      ZXPUHMXFXIBKNXAXIVFXIVJKNVGVHXIVKVTXIWQWMAXMXHXOVIXHXKAXLVLZVMVNXIXSNXPXE
      UHXIXSNKLMZNXIXSNXEOMZKXEOMZLMYAXIXQYBXRYCLXIXPXENOXIENWMAEULRXHAEIVOVIXI
      WAXHWMULRZAXHXKYDXLWMVPSVLVQZTXIXPXEKOYETVRXIYBNYCKLXIXEWBRYBNUSXIXEXIXNX
      KXEURRZAXNXHIVIXTEWMVSWCZWDXEWESXIYFYCKUSYGXEWFSVRWGWHWIYEVRWGTVEWJ $.
  $}

  ${
    $d K k $.  $d M k $.  $d N k $.
    lcmineqlem4.1 $e |- ( ph -> N e. NN ) $.
    lcmineqlem4.2 $e |- ( ph -> M e. NN ) $.
    lcmineqlem4.3 $e |- ( ph -> M <_ N ) $.
    lcmineqlem4.4 $e |- ( ph -> K e. ( 0 ... ( N - M ) ) ) $.
    $( Part of lcm inequality lemma, this part eventually shows that F times
       the least common multiple of 1 to n is an integer.  F is found in
       ~ lcmineqlem6 .  (Contributed by metakunt, 10-May-2024.) $)
    lcmineqlem4 $p |- ( ph -> ( ( _lcm ` ( 1 ... N ) ) / ( M + K ) ) e. ZZ ) $=
      ( vk c1 cfz co caddc cdvds cn wcel wa syl wb wceq clcmf cfv cdiv cv breq1
      wbr cz wss cfn wral fzssz fzfi pm3.2i a1i dvdslcmf cmin cc0 1zzd nnzd 0zd
      zsubcld cle nnred leidd fznn mpbir2and 1cnd addridd eqcomd wi nncnd eqcom
      npcand jca subcl addcom eqeq2 bitrd pm5.74i mpbi fzadd2d rspcdva lcmfnncl
      cc fz1ssnn ax-mp cn0 elfznn0 nnnn0addcl syl2anc nndivdvds mpbid ) AJDKLZU
      AUBZCBMLZUCLZAWOWNNUFZWPOPZAIUDZWNNUFZWQIWMWOWSWOWNNUEAWMUGUHZWMUIPZQZWTI
      WMUJXCAXAXBJDUKJDULZUMUNIWMUORADCUPLZJDCBJCUQAURACFUSZAUTADCADEUSXFVAACJC
      KLPZCOPZCCVBUFZFACACFVCVDACUGPXGXHXIQSXFCCVERVFHAJUQMLJAJAVGVHVIAXECMLZDT
      ZVJADCXEMLZTZVJADCADEVKZACFVKZVMAXKXMAXKDXJTZXMXKXPSAXJDVLUNAXJXLTZXPXMSA
      XEWDPZCWDPZQXQAXRXSADWDPZXSQXRAXTXSXNXOVNDCVORXOVNXECVPRXJXLDVQRVRVSVTWAW
      BAWNOPZWOOPZWQWRSYAAWMOUHZXBQYAYCXBDWEXDUMWMWCWFUNAXHBWGPZYBFABUQXEKLPYDH
      BXEWHRCBWIWJWNWOWKWJWLUS $.
  $}

  ${
    lcmineqlem5.1 $e |- ( ph -> A e. CC ) $.
    lcmineqlem5.2 $e |- ( ph -> B e. CC ) $.
    lcmineqlem5.3 $e |- ( ph -> C e. CC ) $.
    lcmineqlem5.4 $e |- ( ph -> C =/= 0 ) $.
    $( Technical lemma for reciprocal multiplication in deduction form.
       (Contributed by metakunt, 10-May-2024.) $)
    lcmineqlem5 $p |- ( ph -> ( A x. ( B x. ( 1 / C ) ) ) =
        ( B x. ( A / C ) ) ) $=
      ( c1 cdiv cmul reccld mulassd mulcomd oveq1d eqtr3d eqtrd divrecd oveq2d
      co eqtr4d ) ABCIDJTZKTKTZCBUBKTZKTZCBDJTZKTAUCCBKTZUBKTZUEABCKTZUBKTUCUHA
      BCUBEFADGHLZMAUIUGUBKABCEFNOPACBUBFEUJMQAUFUDCKABDEGHRSUA $.
  $}

  ${
    $d M k x $.  $d N k x $.  $d k ph x $.
    lcmineqlem6.1 $e |- F = S. ( 0 [,] 1 ) ( ( x ^ ( M - 1 ) ) x.
     ( ( 1 - x ) ^ ( N - M ) ) ) _d x $.
    lcmineqlem6.2 $e |- ( ph -> N e. NN ) $.
    lcmineqlem6.3 $e |- ( ph -> M e. NN ) $.
    lcmineqlem6.4 $e |- ( ph -> M <_ N ) $.
    $( Part of lcm inequality lemma, this part eventually shows that F times
       the least common multiple of 1 to n is an integer.  (Contributed by
       metakunt, 10-May-2024.) $)
    lcmineqlem6 $p |- ( ph -> ( ( _lcm ` ( 1 ... N ) ) x. F ) e. ZZ ) $=
      ( vk c1 co cmul cc0 cz cc wcel cn adantl adantr cfz cfv cmin cneg cv cexp
      clcmf cbc caddc cdiv csu lcmineqlem3 oveq2d fzfid wss cfn wa fz1ssnn fzfi
      pm3.2i lcmfnncl ax-mp nncni a1i elfzelz m1expcl bccl2 nncnd mulcld addcld
      syl zcnd cn0 elfznn0 nnnn0addcl sylan2 sylan nnne0d fsummulc2 lcmineqlem5
      reccld eqtrd sumeq2dv nnzd zmulcld cle simpr lcmineqlem4 fsumzcl eqeltrd
      wbr ) AKEUALZUGUBZCMLZNEDUCLZUALZKUDJUEZUFLZWOWQUHLZMLZWMDWQUILZUJLZMLZJU
      KZOAWNWPWMWTKXAUJLZMLZMLZJUKZXDAWNWMWPXFJUKZMLXHACXIWMMABJCDEFGHIULUMAWPX
      FWMJANWOUNZWMPQZAWMWLRUOZWLUPQZUQWMRQXLXMEURKEUSUTWLVAVBVCZVDAWQWPQZUQZWT
      XEXPWRWSXOWRPQAXOWRXOWQOQWROQZWQNWOVEZWQVFVKZVLSXOWSPQAXOWSWQWOVGZVHSVIZX
      PXAXPDWQADPQXOADHVHTXOWQPQAXOWQXRVLSVJZXPXAADRQZXOXARQZHXOYCWQVMQYDWQWOVN
      DWQVOVPVQVRZWAVIVSWBAWPXGXCJXPWMWTXAXKXPXNVDYAYBYEVTWCWBAWPXCJXJXPWTXBXPW
      RWSXOXQAXSSXOWSOQAXOWSXTWDSWEXPWQDEAERQXOGTAYCXOHTADEWFWKXOITAXOWGWHWEWIW
      J $.
  $}

  ${
    $( Derivative of 1-x for chain rule application.  (Contributed by metakunt,
       12-May-2024.) $)
    lcmineqlem7 $p |- ( CC _D ( x e. CC |-> ( 1 - x ) ) )
                         = ( x e. CC |-> -u 1 ) $=
      ( cc c1 cv cmin co cmpt cdv cneg wceq wtru cc0 cr cpr wcel cnelprrecn a1i
      wa 1cnd 0cnd dvmptc simpr dvmptid dvmptsub df-neg eqcomd mpteq2dv eqtrd
      mptru ) BABCADZEFGHFZABCIZGZJKUKABLCEFZGUMKACLUJCBBBBBMBNOKPQZKUJBOZRZSZU
      QTKACBUOKSUAKUPUBURKABUOUCUDKABUNULKULUNULUNJKCUEQUFUGUHUI $.
  $}

  ${
    $d M x y $.  $d N x y $.  $d ph x y $.
    lcmineqlem8.1 $e |- ( ph -> M e. NN ) $.
    lcmineqlem8.2 $e |- ( ph -> N e. NN ) $.
    lcmineqlem8.3 $e |- ( ph -> M < N ) $.
    $( Derivative of (1-x)^(N-M).  (Contributed by metakunt, 12-May-2024.) $)
    lcmineqlem8 $p |- ( ph ->
    ( CC _D ( x e. CC |-> ( ( 1 - x ) ^ ( N - M ) ) ) )
        = ( x e. CC |-> ( -u ( N - M ) x.
                           ( ( 1 - x ) ^ ( ( N - M ) - 1 ) ) ) ) ) $=
      ( vy cc c1 cmin co cexp cmpt cmul wcel a1i subcld adantr wceq cv cdv cneg
      cr cpr cnelprrecn wa 1cnd simpr neg1cn cn0 clt wbr cn nnzd znnsub syl2anc
      cz wb mpbid nnnn0d expcld nncnd nnm1nn0 syl expcl lcmineqlem7 dvexp oveq1
      mulcld oveq2d dvmptco ax-1cn mpan syl2anr mul32d mulcomd oveq1d mpteq2dva
      subcl eqtrd mulm1d ) AIBIJBUAZKLZDCKLZMLZNUBLBIWEWDWEJKLZMLZOLZJUCZOLZNBI
      WEUCZWHOLZNABHWDWJHUAZWEMLZWEWNWGMLZOLZIIWFWIIIIIIUDIUEPAUFQZWRAWCIPZUGZJ
      WCWTUHAWSUIRWJIPZWTUJQZAWNIPZUGZWNWEAXCUIZAWEUKPXCAWEACDULUMZWEUNPZGACURP
      DURPXFXGUSACEUOADFUOCDUPUQUTZVASVBXDWEWPXDDCADIPZXCADFVCZSACIPZXCACEVCZSR
      XDXCWGUKPZWPIPXEAXMXCAXGXMXHWEVDVEZSWNWGVFUQVJIBIWDNUBLBIWJNTABVGQAXGIHIW
      ONUBLHIWQNTXHHWEVHVEWNWDWEMVIWNWDTWPWHWEOWNWDWGMVIVKVLABIWKWMWTWKWJWEOLZW
      HOLZWMWTWKWEWJOLZWHOLZXPWTWEWHWJWTDCAXIWSXJSAXKWSXLSRWSWDIPZXMWHIPAJIPWSX
      SVMJWCVTVNXNWDWGVFVOXBVPAXRXPTWSAXQXOWHOAWEWJADCXJXLRZXAAUJQVQVRSWAWTXOWL
      WHOAXOWLTWSAWEXTWBSVRWAVSWA $.
  $}

  ${
    $d ph x $.  $d N x y $.  $d M x y $.
    lcmineqlem9.1 $e |- ( ph -> M e. NN ) $.
    lcmineqlem9.2 $e |- ( ph -> N e. NN ) $.
    lcmineqlem9.3 $e |- ( ph -> M <_ N ) $.
    $( (1-x)^(N-M) is continuous.  (Contributed by metakunt, 12-May-2024.) $)
    lcmineqlem9 $p  |- ( ph
                      -> ( x e. CC |-> ( ( 1 - x ) ^ ( N - M ) ) )
                         e. ( CC -cn-> CC ) ) $=
      ( vy cc c1 cv cmin co cexp nfv wcel cmpt ccncf cz nnzd eqid sub2cncf mp1i
      ax-1cn cn0 cle wbr wb znn0sub syl2anc mpbid expcncf syl ssidd cncfcompt2
      oveq1 ) ABHIIIJBKLMZHKZDCLMZNMZUQUSNMIABOJIPBIUQQZIIRMZPAUDBJVAVAUAUBUCAU
      SUEPZHIUTQVBPACDUFUGZVCGACSPDSPVDVCUHACETADFTCDUIUJUKHUSULUMAIUNURUQUSNUP
      UO $.
  $}

  ${
    $d ph x $.  $d N x $.  $d M x $.
    lcmineqlem10.1 $e |- ( ph -> M e. NN ) $.
    lcmineqlem10.2 $e |- ( ph -> N e. NN ) $.
    lcmineqlem10.3 $e |- ( ph -> M < N ) $.
    $( Induction step of ~ lcmineqlem13 (deduction form).  (Contributed by
       metakunt, 12-May-2024.) $)
    lcmineqlem10 $p  |- ( ph
                      -> S. ( 0 [,] 1 )
                              ( ( x ^ ( ( M + 1 ) - 1 ) )
                                x.
                                ( ( 1 - x ) ^ ( N - ( M + 1 ) ) ) )
                           _d x
                         = ( ( M / ( N - M ) )
                             x.
                             S. ( 0 [,] 1 )
                                ( ( x ^ ( M - 1 ) )
                                  x.
                                  ( ( 1 - x ) ^ ( N - M ) ) )
                             _d x ) ) $=
      ( cc0 c1 co cmin cexp cmul citg wceq cc wcel sylan2 adantr mulcld cicc cv
      caddc cdiv cneg nncnd subcld wa elunitcn cn0 nnnn0d expcl ancoms simpr cn
      1cnd clt wbr cz wb nnzd znnsub syl2anc mpbid nnm1nn0 expcld cr cmpt ccncf
      syl cibl expcncf 1nn nnge1d lcmineqlem9 mulcncf resclunitintvd cnicciblnc
      0red 1red a1i syl3anc itgcl mulneg1d negcld itgmulc2 mul12d itgeq2dv cioo
      itgioo cle 0le1 wi ltle mpd wss ssid cncfmptc mp3an23 resopunitintvd 3syl
      nnred ioossicc cdm ioombl iblss cdv dvexp resdvopclptsd lcmineqlem8 oveq1
      cvol adantl 0expd eqtrd oveq1d 0cn eleq1 mpbiri mul02d oveq2 1m1e0 eqtrdi
      oveq2d ax-1cn mul01d itgparts eqtr3d oveq1i mulassd eqtr4d df-neg eqtr4di
      0m0e0 neg11ad nnne0d divmuld mpbird pncand eqcomd subsub4d oveq12d div23d
      ) ABHIUAJZBUBZCIUCJZIKJZLJZIUUEKJZDUUFKJZLJZMJZNZCBUUDUUECIKJZLJZUUIDCKJZ
      LJZMJZNZMJZUUPUDJZCUUPUDJUUSMJAUVAUUMAUVABUUDUUECLJZUUIUUPIKJZLJZMJZNZUUM
      AUVAUVFOUUPUVFMJZUUTOZAUVGUEZUUTUEZOUVHAUUPUEZUVFMJZUVIUVJAUUPUVFADCADFUF
      ZACEUFZUGZABUUDUVEPAUUEUUDQZUHZUVBUVDUVPAUUEPQZUVBPQZUUEUIZUVRAUVSAUVRCUJ
      QZUVSACEUKZUUECULRUMZRZUVPAUVRUVDPQUVTAUVRUHZUUIUVCUWEIUUEUWEUPAUVRUNUGZA
      UVCUJQZUVRAUUPUOQZUWGACDUQURZUWHGACUSQDUSQUWIUWHUTACEVAADFVACDVBVCVDZUUPV
      EVJSVFZRZTZAHVGQZIVGQZBUUDUVEVHZUUDPVIJZQUWPVKQAVSZAVTZABUVEABUVBUVDPAUWA
      BPUVBVHZPPVIJZQUWBBCVLVJZABIUUPIUOQAVMWAUWJAUUPUWJVNVOZVPVQHIUWPVRWBZWCZW
      DAUVLHUUTKJZUVJAUVLHBUUDCUURMJZNZKJZUXFAUVLHBUUDCUUOMJZUUQMJZNZKJZUXIAUVL
      BUUDUVKUVEMJZNZUXMABUUDUVEUVKPAUUPUVOWEZUWMUXDWFABUUDUVBUVKUVDMJZMJZNZUXO
      UXMABUUDUXRUXNUVPAUVRUXRUXNOUVTUWEUVBUVKUVDUWCUWEUUPUWEDCADPQZUVRUVMSACPQ
      ZUVRUVNSZUGWEZUWKWGRWHAUXSHHKJZUXLKJZUXMAUXSUYDBHIWIJZUXKNZKJZUYEABUYFUXR
      NUXSUYHABHIUXRUWRUWSUVQUVBUXQUWDUVQUVKUVDUVQUUPUVQDCAUXTUVPUVMSAUYAUVPUVN
      SZUGWEUWLTTZWJABUVBUXJUUQUXQHHHIUWRUWSHIWKURAWLWAABUVBUXBVQABUUQABCDEFAUW
      ICDWKURZGACVGQDVGQUWIUYKWMACEXBADFXBCDWNVCWOVOZVQABCUUOUYFABCAUYABPCVHUXA
      QZUVNUYAPPWPZUYNUYMPWQZUYOBCPPWRWSVJZWTABUUOACUOQZUUNUJQZBPUUOVHUXAQECVEZ
      BUUNVLXAZWTVPABUVKUVDUYFABUVKAUVKPQZBPUVKVHUXAQZUXPVUAUYNUYNVUBUYOUYOBUVK
      PPWRWSVJZWTABUVDUXCWTVPABUYFUUDUXRPUYFUUDWPAHIXCWAZUYFXLXDQAHIXEWAZUYJAUW
      NUWOBUUDUXRVHZUWQQVUFVKQUWRUWSABUXRABUVBUXQPUXBABUVKUVDPVUCUXCVPVPVQHIVUF
      VRWBXFABUYFUUDUXKPVUDVUEUVQUXJUUQUVQCUUOUYIUVPAUVRUUOPQZUVTUVRAVUGAUVRUYR
      VUGAUYQUYREUYSVJUUEUUNULRUMZRZTUVPAUVRUUQPQUVTUWEUUIUUPUWFAUUPUJQUVRAUUPU
      WJUKSVFZRZTZAUWNUWOBUUDUXKVHZUWQQVUMVKQUWRUWSABUXKABUXJUUQPABCUUOPUYPUYTV
      PUYLVPVQHIVUMVRWBXFABUVBUXJAUYQPUWTXGJBPUXJVHOEBCXHVJUWCUWECUUOUYBVUHTXIA
      BUUQUXQABCDEFGXJVUJUWEUVKUVDUYCUWKTXIAUUEHOZUHZUVBUUQMJZHUUQMJZHVUOUVBHUU
      QMVUOUVBHCLJZHVUNUVBVUROAUUEHCLXKXMAVURHOVUNACEXNSXOXPVUNAUVRVUQHOVUNUVRH
      PQXQUUEHPXRXSUWEUUQVUJXTRXOAUUEIOZUHZVUPUVBHMJZHVUTUUQHUVBMVUTUUQHUUPLJZH
      VUSUUQVVBOAVUSUUIHUUPLVUSUUIIIKJHUUEIIKYAYBYCXPXMAVVBHOVUSAUUPUWJXNSXOYDV
      USAUVRVVAHOVUSUVRIPQZYEUUEIPXRXSUWEUVBUWCYFRXOYGYHAUYGUXLUYDKABHIUXKUWRUW
      SVULWJYDXOUYDHUXLKYNYIYCYHXOAUXLUXHHKABUUDUXKUXGUVPAUVRUXKUXGOUVTUWECUUOU
      UQUYBVUHVUJYJRWHYDXOAUUTUXHHKABUUDUURCPUVNUVQUUOUUQVUIVUKTZAUWNUWOBUUDUUR
      VHZUWQQVVEVKQUWRUWSABUURABUUOUUQPUYTUYLVPVQHIVVEVRWBZWFYDYKUUTYLYMYHAUVGU
      UTAUUPUVFUVOUXETACUUSUVNABUUDUURPVVDVVFWCZTZYOVDAUUTUUPUVFVVHUVOUXEAUUPUW
      JYPZYQYRABUUDUVEUULAUVEUULOUVPAUVBUUHUVDUUKMACUUGUUELAUUGCACIUVNVVCAYEWAZ
      YSYTYDAUVCUUJUUILADCIUVMUVNVVJUUAYDUUBSWHXOYTACUUSUUPUVNVVGUVOVVIUUCXO $.
  $}

  ${
    lcmineqlem11.1 $e |- ( ph -> M e. NN ) $.
    lcmineqlem11.2 $e |- ( ph -> N e. NN ) $.
    lcmineqlem11.3 $e |- ( ph -> M < N ) $.
    $( Induction step, continuation for binomial coefficients.  (Contributed by
       metakunt, 12-May-2024.) $)
    lcmineqlem11 $p |- ( ph -> ( 1 / ( ( M + 1 ) x. ( N _C ( M + 1 ) ) ) ) =
     ( ( M / ( N - M ) ) x. ( 1 / ( M x. ( N _C M ) ) ) ) ) $=
      ( c1 co cbc cmul cdiv cmin wceq nncnd wcel cz mulcld eqtrd nnne0d eqtr4d
      caddc 1cnd addcld nnnn0d cn0 a1i nn0addcld clt wbr cle wb zltp1le syl2anc
      1nn0 nnzd mpbid bccl2d div1d cfz w3a peano2zd peano2nnd nnge1d 3jca elfz1
      1z mpan syl mpbird bcm1k pncand oveq2d oveq1d oveq12d nnred ltled divassd
      subcld eqcomd divmul2d mulcomd divcan3d mul12d cc0 wne 0ne1 mulne0d gtned
      necomd subne0d recbothd mulridd divmuldivd ) AGBGUAHZCWNIHZJHZKHZBGJHZCBL
      HZBCBIHZJHZJHZKHZBWSKHGXAKHJHAWQBXBKHZXCAWQXDMWPGKHZXBBKHZMAXEBWSWTJHZJHZ
      BKHZXFAXEXGXIAXEWPXGAWPAWNWOABGABDNZAUBZUCZAWOAWNCEABGABDUDZGUEOAUNUFUGAB
      CUHUIZWNCUJUIZFABPOCPOZXNXOUKABDUOZACEUOZBCULUMUPZUQZNZQZURAWPWTWSJHZXGAY
      CWPAYCWNKHZWOMYCWPMAWOYDAWOWTWSWNKHZJHZYDAWOCWNGLHZIHZCYGLHZWNKHZJHZYFAWN
      GCUSHOZWOYKMAYLWNPOZGWNUJUIZXOUTZAYMYNXOABXQVAAWNABDVBZVCXSVDAXPYLYOUKZXR
      GPOXPYQVFWNGCVEVGVHVIWNCVJVHAYHWTYJYEJAYGBCIABGXJXKVKZVLAYIWSWNKAYGBCLYRV
      LVMVNRAWTWSWNAWTABCEXMABCABDVOZACEVOFVPUQZNZACBACENZXJVRZXLAWNYPSZVQTVSAY
      CWOWNAWTWSUUAUUCQYAXLUUDVTUPVSAWTWSUUAUUCWARRAXGBAWSWTUUCUUAQXJABDSZWBTAX
      HXBBKABWSWTXJUUCUUAWCVMRAGWPBXBXKAWDGWDGWEAWFUFWIYBAWNWOXLYAUUDAWOXTSWGXJ
      UUEAWSXAUUCABWTXJUUAQZQAWSXAUUCUUFACBUUBXJABCYSFWHWJZABWTXJUUAUUEAWTYTSWG
      ZWGWKVIAWRBXBKABXJWLVMTABWSGXAXJUUCXKUUFUUGUUHWMT $.
  $}

  ${
    $d N t x $.  $d N x y $.  $d ph t x $.  $d ph x y $.
    lcmineqlem12.1 $e |- ( ph -> N e. NN ) $.
    $( Base case for induction.  (Contributed by metakunt, 12-May-2024.) $)
    lcmineqlem12 $p |- ( ph
                      -> S. ( 0 [,] 1 )
                              ( ( t ^ ( 1 - 1 ) )
                                x.
                                ( ( 1 - t ) ^ ( N - 1 ) ) )
                           _d t
                         = ( 1 / ( 1 x. ( N _C 1 ) ) ) ) $=
      ( vx vy cc0 c1 co cmin cexp cmul wcel cc wceq syl adantr eqtrd cmpt a1i
      cicc cv citg cdiv elunitcn wa 1m1e0 oveq2i simpr exp0d eqtrid oveq1d 1cnd
      cbc subcld cn0 cn nnm1nn0 expcld mullidd sylan2 itgeq2dv cioo 0red itgioo
      1red cfv eqidd oveq2 adantl adantlr cr elioore recn 3syl fvmptd cneg wral
      cdv cpr cnelprrecn nnnn0 nn0cnd mulcld negcld 0cnd dvmptc dvmptsub df-neg
      dvmptid mpteq2dv eqtr4d dvexp oveq1 oveq2d dvmptco nncnd nnne0d dvmptcmul
      divcld mulassd eqcomd wne divcan1d mul32d mul2negd 1t1e1 eqtrdi mpteq2dva
      resdvopclptsd fveq1d ralrimivw itgeq2 cle wbr 0le1 ccncf nfv wss cncfmptc
      ax-1cn ssid mp3an cncfmptid mp2an subcncf ssidd cncfcompt2 resopunitintvd
      expcncf eleq1d mpbird cibl ioossicc cvol cdm ioombl resclunitintvd eqtr3d
      w3a 3jca cnicciblnc iblss eqeltrd mp3an23 mulcncf ftc2 0exp 1elunit 1m0e1
      mul01d cz 1exp mulridd 0elunit oveq12d divnegd eqtr2d reccld negnegd bcn1
      nn0zd ) ABGHUAIZBUBZHHJIZKIZHUVDJIZCHJIZKIZLIZUCBUVCUVIUCZHHCHUNIZLIZUDIZ
      ABUVCUVJUVIUVDUVCMZAUVDNMZUVJUVIOUVDUEZAUVPUFZUVJHUVILIUVIUVRUVFHUVILUVRU
      VFUVDGKIHUVEGUVDKUGUHUVRUVDAUVPUIZUJUKULUVRUVIUVRUVGUVHUVRHUVDUVRUMUVSUOA
      UVHUPMZUVPACUQMZUVTDCURPZQUSZUTRVAVBAUVKHCUDIZUVNABGHVCIZUVIUCZUVKUWDABGH
      UVIAVDZAVFZUVOAUVPUVINMUVQUWCVAVEABUWEUVDEUWEHEUBZJIZUVHKIZSZVGZUCZUWFUWD
      ABUWEUWMUVIAUVDUWEMZUFZEUVDUWKUVIUWEUWLNUWPUWLVHAUWIUVDOZUWKUVIOZUWOUWQUW
      RAUWQUWJUVGUVHKUWIUVDHJVIULVJVKAUWOUIZUWPUVGUVHUWPHUVDUWPUMUWPUWOUVDVLMUV
      PUWSUVDGHVMUVDVNVOUOAUVTUWOUWBQUSVPVBABUWEUVDVLEUVCHVQZCUDIZUWJCKIZLIZSZV
      SIZVGZUCZUWNUWDAUXFUWMOZBUWEVRUXGUWNOAUXHBUWEAUVDUXEUWLAEUXCUWKANENUXCSVS
      IENUXACUWKLIZUWTLIZLIZSENUWKSAEUXBUXJUXANNNNVLNVTMAWATZAUWINMZUFZUWJCUXNH
      UWIUXNUMZAUXMUIZUOZACUPMZUXMAUWAUXRDCWBPZQZUSZUXNUXIUWTUXNCUWKUXNCUXTWCZU
      XNUWJUVHUXQAUVTUXMUWBQUSZWDZUXNHUXOWEZWDAEFUWJUWTFUBZCKIZCUYFUVHKIZLIZNNU
      XBUXINNNNUXLUXLUXQUYEAUYFNMZUFZUYFCAUYJUIZAUXRUYJUXSQZUSUYKCUYHUYKCUYMWCU
      YKUYFUVHUYLAUVTUYJUWBQUSWDANENUWJSVSIENGHJIZSENUWTSAEHGUWIHNNNNUXLUXOUXNW
      FAEHNUXLAUMZWGUXPUXOAENUXLWJWHAENUWTUYNUWTUYNOAHWITWKWLAUWANFNUYGSZVSIFNU
      YISODFCWMPUYFUWJCKWNZUYFUWJOUYHUWKCLUYFUWJUVHKWNZWOWPAUWTCAHUYOWEACDWQZAC
      DWRZWTZWSAENUXKUWKUXNUXKUWTUWTLIZUWKLIZUWKUXNUXKUWTUWKLIZUWTLIZVUCUXNUXKU
      XACLIZUWKLIZUWTLIZVUEUXNUXKUXAUXILIZUWTLIZVUHUXNVUJUXKUXNUXAUXIUWTAUXANMZ
      UXMVUAQZUYDUYEXAXBUXNVUHVUJUXNVUGVUIUWTLUXNUXACUWKVULUYBUYCXAULXBRUXNVUGV
      UDUWTLUXNVUFUWTUWKLUXNUWTCUYEUYBACGXCUXMUYTQXDULULRUXNVUCVUEUXNUWTUWTUWKU
      YEUYEUYCXEXBRUXNVUCHUWKLIUWKUXNVUBHUWKLUXNVUBHHLIHUXNHHUXOUXOXFXGXHULUXNU
      WKUYCUTRRXIRUXNUXAUXBVULUYAWDUYCXJZXKXLBUWEUXFUWMXMPAUXGGUXAJIZUWDAUXGHUX
      DVGZGUXDVGZJIVUNABGHUXDUWGUWHGHXNXOAXPTAUXEUWENXQIZMUWLVUQMAEUWKAEFNNNUWJ
      UYHUWKNAEXRZAEHUWINENHSNNXQIZMZAHNMNNXSZVVAVUTYANYBZVVBEHNNXTYCTENUWISVUS
      MZAVVAVVAVVCVVBVVBENNYDYETYFZAUVTFNUYHSVUSMUWBFUVHYJPZANYGZUYRYHYIAUXEUWL
      VUQVUMYKYLAUXEUWLYMVUMAEUWEUVCUWKNUWEUVCXSAGHYNTUWEYOYPMAGHYQTUWIUVCMAUXM
      UWKNMUWIUEUYCVAAGVLMZHVLMZEUVCUWKSZUVCNXQIMZYTVVIYMMAVVGVVHVVJUWGUWHAEUWK
      AEFNNNUWJUYHUWKNVURVVDVVEVVAAVVBTUYRYHYRUUAGHVVIUUBPUUCUUDAEUXAUXBUVCAEUX
      AAVUKENUXASVUSMZVUAVUKVVAVVAVVKVVBVVBEUXANNXTUUEPYRAEUXBAEFNNNUWJUYGUXBNV
      URVVDAUXRUYPVUSMUXSFCYJPVVFUYQYHYRUUFUUGAVUOGVUPUXAJAEHUXCGUVCUXDNAUXDVHZ
      AUWIHOZUFZUXCUXAGLIZGVVNUXBGUXALVVNUXBGCKIZGVVNUWJGCKVVNUWJUVEGVVNUWIHHJA
      VVMUIWOUGXHULAVVPGOZVVMAUWAVVQDCUUHPQRWOAVVOGOVVMAUXAVUAUUKQRHUVCMAUUITAW
      FVPAEGUXCUXAUVCUXDNVVLAUWIGOZUFZUXCUXAHLIUXAVVSUXBHUXALVVSUXBHCKIZHVVSUWJ
      HCKVVSUWJHGJIHVVSUWIGHJAVVRUIWOUUJXHULAVVTHOZVVRACUULMVWAACUXSUVBCUUMPQRW
      OVVSUXAAVUKVVRVUAQUUNRGUVCMAUUOTVUAVPUUPRAVUNUWDVQZVQZUWDAVWCGVWBJIZVUNVW
      CVWDOAVWBWITAVWBUXAGJAHCUYOUYSUYTUUQWOUURAUWDACUYSUYTUUSUUTRRYSYSYSAUVMCH
      UDAUVMHCLICAUVLCHLAUXRUVLCOUXSCUVAPWOACUYSUTRWOWLR $.
  $}

  ${
    $d M i x $.  $d N i m x $.  $d i m ph x $.
    lcmineqlem13.1 $e |- F = S. ( 0 [,] 1 ) ( ( x ^ ( M - 1 ) ) x.
     ( ( 1 - x ) ^ ( N - M ) ) ) _d x $.
    lcmineqlem13.2 $e |- ( ph -> M e. NN ) $.
    lcmineqlem13.3 $e |- ( ph -> N e. NN ) $.
    lcmineqlem13.4 $e |- ( ph -> M <_ N ) $.
    $( Induction proof for lcm integral.  (Contributed by metakunt,
       12-May-2024.) $)
    lcmineqlem13 $p |- ( ph -> F = ( 1 / ( M x. ( N _C M ) ) ) ) $=
      ( c1 co cmin cexp cmul cbc cdiv wceq oveq2d oveq2 oveq12d vi vm cicc citg
      cc0 cv cz wcel cle wbr w3a nnzd cn nnge1 3jca caddc oveq1 adantr itgeq2dv
      syl id eqeq12d lcmineqlem12 wa elnnz1 biimpri 3adant3 adantl lcmineqlem10
      simpr3 3ad2ant3 eqtrd lcmineqlem11 eqtr4d 1zzd nnge1d fzindd mpdan eqtrid
      clt ) ACBUEJUCKZBUFZDJLKZMKZJWBLKZEDLKZMKZNKZUDZJDEDOKZNKZPKZFADUGUHZJDUI
      UJZDEUIUJZUKWIWLQZAWMWNWOADGULADUMUHWNGDUNUTIUOABWAWBUAUFZJLKZMKZWEEWQLKZ
      MKZNKZUDZJWQEWQOKZNKZPKZQBWAWBJJLKZMKZWEEJLKZMKZNKZUDZJJEJOKZNKZPKZQBWAWB
      UBUFZJLKZMKZWEEXPLKZMKZNKZUDZJXPEXPOKZNKZPKZQZBWAWBXPJUPKZJLKZMKZWEEYGLKZ
      MKZNKZUDZJYGEYGOKZNKZPKZQWPUAUBDJEWQJQZXCXLXFXOYQBWAXBXKYQXBXKQWBWAUHZYQW
      SXHXAXJNYQWRXGWBMWQJJLUQRYQWTXIWEMWQJELSRTURUSYQXEXNJPYQWQJXDXMNYQVAWQJEO
      STRVBWQXPQZXCYBXFYEYSBWAXBYAYSXBYAQYRYSWSXRXAXTNYSWRXQWBMWQXPJLUQRYSWTXSW
      EMWQXPELSRTURUSYSXEYDJPYSWQXPXDYCNYSVAWQXPEOSTRVBWQYGQZXCYMXFYPYTBWAXBYLY
      TXBYLQYRYTWSYIXAYKNYTWRYHWBMWQYGJLUQRYTWTYJWEMWQYGELSRTURUSYTXEYOJPYTWQYG
      XDYNNYTVAWQYGEOSTRVBWQDQZXCWIXFWLUUABWAXBWHUUAXBWHQYRUUAWSWDXAWGNUUAWRWCW
      BMWQDJLUQRUUAWTWFWEMWQDELSRTURUSUUAXEWKJPUUAWQDXDWJNUUAVAWQDEOSTRVBABEHVC
      AXPUGUHZJXPUIUJZXPEVTUJZUKZYFUKZYMXPXSPKZYENKZYPUUFYMUUGYBNKZUUHAUUEYMUUI
      QYFAUUEVDZBXPEUUEXPUMUHZAUUBUUCUUKUUDUUKUUBUUCVDXPVEVFVGVHZAEUMUHUUEHURZA
      UUBUUCUUDVJZVIVGYFAUUIUUHQUUEYBYEUUGNSVKVLAUUEYPUUHQYFUUJXPEUULUUMUUNVMVG
      VNAVOAEHULAEHVPVQVRVS $.
  $}

  ${
    lcmineqlem14.1 $e |- ( ph -> A e. NN ) $.
    lcmineqlem14.2 $e |- ( ph -> B e. NN ) $.
    lcmineqlem14.3 $e |- ( ph -> C e. NN ) $.
    lcmineqlem14.4 $e |- ( ph -> D e. NN ) $.
    lcmineqlem14.5 $e |- ( ph -> E e. NN ) $.
    lcmineqlem14.6 $e |- ( ph -> ( A x. C ) || D ) $.
    lcmineqlem14.7 $e |- ( ph -> ( B x. C ) || E ) $.
    lcmineqlem14.8 $e |- ( ph -> D || E ) $.
    lcmineqlem14.9 $e |- ( ph -> ( A gcd B ) = 1 ) $.
    $( Technical lemma for inequality estimate.  (Contributed by metakunt,
       12-May-2024.) $)
    lcmineqlem14 $p |- ( ph -> ( ( A x. B ) x. C ) || E ) $=
      ( cmul co cdvds wbr nnzd cdiv cz nnproddivdvdsd mpbid dvdszrcl syl simprd
      wcel wa zmulcld dvdstrd coprmdvds2d nnmulcld mpbird ) ABCPQZDPQFRSUOFDUAQ
      ZRSABCUPABGTZACHTACUBUHZUPUBUHZACUPRSZURUSUIACDPQFRSUTMACDFHIKUCUDZCUPUEU
      FUGOABDPQZFRSBUPRSAVBEFABDUQADITUJAEJTAFKTLNUKABDFGIKUCUDVAULAUODFABCGHUM
      IKUCUN $.

  $}

  ${
    $d M x $.  $d N x $.  $d ph x $.
    lcmineqlem15.1 $e |- F = S. ( 0 [,] 1 ) ( ( x ^ ( M - 1 ) ) x.
     ( ( 1 - x ) ^ ( N - M ) ) ) _d x $.
    lcmineqlem15.2 $e |- ( ph -> N e. NN ) $.
    lcmineqlem15.3 $e |- ( ph -> M e. NN ) $.
    lcmineqlem15.4 $e |- ( ph -> M <_ N ) $.
    $( F times the least common multiple of 1 to n is a natural number.
       (Contributed by metakunt, 10-May-2024.) $)
    lcmineqlem15 $p |- ( ph -> ( ( _lcm ` ( 1 ... N ) ) x. F ) e. NN ) $=
      ( c1 cfz co clcmf cmul wcel cc0 clt wbr cn nnred cfv lcmineqlem6 wss fzfi
      cz cfn fz1ssnn lcmfnncl mp2an a1i cdiv cr lcmineqlem13 1red nnnn0d bccl2d
      cbc nnmulcld nnne0d redivcld eqeltrd nngt0d nnrecgt0 syl breqtrrd mulgt0d
      elnnz sylanbrc ) AJEKLZMUAZCNLZUEOPVKQRVKSOABCDEFGHIUBAVJCAVJVJSOZAVISUCV
      IUFOVLEUGJEUDVIUHUIUJZTACJDEDUQLZNLZUKLZULABCDEFHGIUMZAJVOAUNAVOADVNHADEG
      ADHUOIUPURZTAVOVRUSUTVAAVJVMVBAPVPCQAVOSOPVPQRVRVOVCVDVQVEVFVKVGVH $.
  $}

  ${
    $d M x $.  $d N x $.  $d ph x $.
    lcmineqlem16.1 $e |- ( ph -> M e. NN ) $.
    lcmineqlem16.2 $e |- ( ph -> N e. NN ) $.
    lcmineqlem16.3 $e |- ( ph -> M <_ N ) $.
    $( Technical divisibility lemma.  (Contributed by metakunt,
       12-May-2024.) $)
    lcmineqlem16 $p |- ( ph -> ( M x. ( N _C M ) ) ||
     ( _lcm ` ( 1 ... N ) ) ) $=
      ( vx cbc co cmul c1 cfz clcmf cdiv cn wcel nncnd nnne0d cmin cexp cfv wbr
      cdvds wss cfn fz1ssnn lcmfnncl mp2an nnnn0d bccl2d mulcld mulne0d divrecd
      fzfi a1i cc0 cicc cv citg eqid lcmineqlem13 lcmineqlem15 eqeltrrd eqeltrd
      oveq2d nnmulcld nndivdvdsd mpbird ) ABCBHIZJIZKCLIZMUAZUCUBVLVJNIZOPAVMVL
      KVJNIZJIZOAVLVJAVLVLOPZAVKOUDVKUEPVPCUFKCUNVKUGUHUOZQABVIABDQZAVIABCEABDU
      IFUJZQZUKABVIVRVTABDRAVIVSRULUMAVLGUPKUQIGURZBKSITIKWASICBSITIJIUSZJIVOOA
      WBVNVLJAGWBBCWBUTZDEFVAVEAGWBBCWCEDFVBVCVDAVJVLABVIDVSVFVQVGVH $.
  $}

  ${
    $d N k $.  $d k ph $.
    lcmineqlem17.1 $e |- ( ph -> N e. NN0 ) $.
    $( Inequality of 2^{2n}.  (Contributed by metakunt, 29-Apr-2024.) $)
    lcmineqlem17 $p |- ( ph -> ( 2 ^ ( 2 x. N ) ) <_
     ( ( ( 2 x. N ) + 1 ) x. ( ( 2 x. N ) _C N ) ) ) $=
      ( vk c2 cmul co cc0 cbc csu cle cn0 wcel wceq syl wa adantr bccl nn0red
      cz cexp cfz c1 caddc cv a1i nn0mulcld binom11 fzfid elfzelz adantl jca cr
      2nn0 nn0zd syl2anc wbr bcmax syl2an fsumle eqbrtrd chash cfv cc fsumconst
      cfn nn0cnd hashfz0 oveq1d eqtrd breqtrd ) AEEBFGZUAGZHVLUBGZVLBIGZDJZVLUC
      UDGZVOFGZKAVMVNVLDUEZIGZDJZVPKAVLLMZVMWANAEBELMAUNUFCUGZDVLUHOAVNVTVODAHV
      LUIZAVSVNMZPZVTWFWBVSTMZPVTLMWFWBWGAWBWEWCQWEWGAVSHVLUJZUKULVSVLROSAVOUMM
      WEAVOAWBBTMVOLMWCABCUOBVLRUPZSQABLMWGVTVOKUQWECWHVSBURUSUTVAAVPVNVBVCZVOF
      GZVRAVNVFMVOVDMVPWKNWDAVOWIVGVNVODVEUPAWJVQVOFAWBWJVQNWCVLVHOVIVJVK $.
  $}

  ${
    lcmineqlem18.1 $e |- ( ph -> N e. NN ) $.
    $( Technical lemma to shift factors in binomial coefficient.  (Contributed
       by metakunt, 12-May-2024.) $)
    lcmineqlem18 $p |- ( ph ->
     ( ( N + 1 ) x. ( ( ( 2 x. N ) + 1 ) _C ( N + 1 ) ) )
    = ( ( ( 2 x. N ) + 1 ) x. ( ( 2 x. N ) _C N ) ) ) $=
      ( c1 caddc co c2 cmul cfa cfv cdiv cmin cc0 wcel a1i cle oveq1d eqtrd syl
      wceq cbc cfz 0zd cz 2z nnzd zmulcld peano2zd 1red nnnn0d nn0ge0d wbr 0le1
      nnred addge0d readdcld addge01d mpbid recnd add32d 2timesd eqcomd breqtrd
      1cnd elfzd bcval2 addsub4d pncand 1m1e0 oveq12d addridd fveq2d oveq2d cn0
      zcnd cn faccl nncnd 1nn0 nn0addcld mulcomd facp1 addcld mulassd nn0mulcld
      2nn0 mulcld peano2nnd nnne0d mulne0d divassd dividd divcld mullidd breq2d
      divmuldivd bitr4d ) ABDEFZGBHFZDEFZWRUAFZHFZWTWSIJZBIJZXDHFZKFZHFZWTWSBUA
      FZHFZAXBWTXCHFZXEKFZXGAXBWRWRKFZXKHFZXKAXBWRXJHFWRXEHFZKFZXMAXBWRXJXNKFZH
      FZXOAXAXPWRHAXAWTIJZXNKFZXPAXAXRXDWRIJZHFZKFZXSAXAXRWTWRLFZIJZXTHFZKFZYBA
      WRMWTUBFNXAYFTAWRMWTAUCZAWSAGBGUDNAUEOABCUFZUGZUHABYHUHABDABCUNZAUIZABABC
      UJZUKZMDPULAUMOUOAWRWRBEFZWTPAMBPULZWRYNPULYMAWRBABDYJYKUPYJUQURAYNBBEFZD
      EFZWTABDBABYJUSZAVDZYRUTAWTYQAWSYPDEABYRVAZQVBRVCVEWRWTVFSAYEYAXRKAYDXDXT
      HAYCBIAYCWSBLFZDDLFZEFZBAWSDBDAWSYIVOZYSYRYSVGAUUCBMEFBAUUABUUBMEAUUAYPBL
      FBAWSYPBLYTQABBYRYRVHRZUUBMTAVIOVJABYRVKRRVLQVMRAYAXNXRKAYAXTXDHFZXNAXDXT
      AXDABVNNZXDVPNYLBVQSZVRZAXTAWRVNNXTVPNABDYLDVNNAVSOVTWRVQSVRWAAUUFWRXDHFZ
      XDHFXNAXTUUJXDHAXTXDWRHFZUUJAUUGXTUUKTYLBWBSAXDWRUUIABDYRYSWCZWARQAWRXDXD
      UULUUIUUIWDRRVMRAXRXJXNKAXRXCWTHFZXJAWSVNNZXRUUMTAGBGVNNAWFOYLWEZWSWBSAXC
      WTAXCAUUNXCVPNUUOWSVQSVRZAWSDUUDYSWCZWARQRVMAXOXQAWRXJXNUULAWTXCUUQUUPWGZ
      AWRXEUULAXDXDUUIUUIWGZWGAWRXEUULUUSAWRABCWHWIZAXDXDUUIUUIAXDUUHWIZUVAWJZW
      JWKVBRAXMXOAWRWRXJXEUULUULUURUUSUUTUVBWPVBRAXMDXKHFXKAXLDXKHAWRUULUUTWLQA
      XKAXJXEUURUUSUVBWMWNRRAWTXCXEUUQUUPUUSUVBWKRAXIXGAXHXFWTHAXHXCUUAIJZXDHFZ
      KFZXFABMWSUBFNXHUVETABMWSYGYIYHYMAYOBWSPULZYMAYOBYPPULUVFABBYJYJUQAWSYPBP
      YTWOWQURVEBWSVFSAUVDXEXCKAUVCXDXDHAUUABIUUEVLQVMRVMVBR $.
  $}

  ${
    lcmineqlem19.1 $e |- ( ph -> N e. NN ) $.
    $( Dividing implies inequality for lcm inequality lemma.  (Contributed by
       metakunt, 12-May-2024.) $)
    lcmineqlem19 $p |- ( ph -> ( ( N x. ( ( 2 x. N ) + 1 ) ) x.
    ( ( 2 x. N ) _C N ) )
    || ( _lcm ` ( 1 ... ( ( 2 x. N ) + 1 ) ) ) ) $=
      ( c2 cmul co c1 caddc cfz clcmf cfv cn wcel a1i cdvds clcm nnzd syl cgcd
      cz cbc 2nn nnmulcld peano2nnd nnnn0d 2re nn0ge0d nnge1d lemulge12d bccl2d
      nnred cr wss cfn fz1ssnn fzfi lcmfnncl lcmineqlem16 lcmineqlem18 remulcld
      mp2an 1red leadd1dd eqbrtrrd wbr wa jca dvdslcm cmin lcmfunnnd recnd 1cnd
      simpld pncand oveq2d fveq2d oveq1d eqtrd breqtrrd wceq 2z gcdaddm mp3an13
      1z addcomd gcd1 eqtr3d lcmineqlem14 ) ABDBEFZGHFZWIBUAFZGWIIFZJKZGWJIFZJK
      ZCAWIADBDLMAUBNZCUCZUDZABWIWQABCUEZABDABCUKZDULMAUFNZABWSUGADWPUHUIZUJWML
      MZAWLLUMWLUNMXCWIUOGWIUPWLUQVANZWOLMZAWNLUMWNUNMXEWJUOGWJUPWNUQVANABWICWQ
      XBURABGHFZWJXFUAFEFWJWKEFWOOABCUSAXFWJABCUDWRABWIGWTADBXAWTUTZAVBXBVCURVD
      AWMWMWJPFZWOOAWMXHOVEZWJXHOVEZAWMTMZWJTMZVFXIXJVFAXKXLAWMXDQAWJWRQVGWMWJV
      HRVMAWOGWJGVIFZIFZJKZWJPFXHAWJWRVJAXOWMWJPAXNWLJAXMWIGIAWIGAWIXGVKZAVLZVN
      VOVPVQVRVSABGSFZBWJSFZGAXRBGWIHFZSFZXSABTMZXRYAVTZABCQZDTMYBGTMYCWAWDDBGW
      BWCRAXTWJBSAGWIXQXPWEVOVRAYBXRGVTYDBWFRWGWH $.
  $}

  ${
    lcmineqlem20.1 $e |- ( ph -> N e. NN ) $.
    $( Inequality for lcm lemma.  (Contributed by metakunt, 12-May-2024.) $)
    lcmineqlem20 $p |- ( ph -> ( N x. ( 2 ^ ( 2 x. N ) ) ) <_
    ( _lcm ` ( 1 ... ( ( 2 x. N ) + 1 ) ) ) ) $=
      ( c2 cmul co cexp c1 nnred cn0 wcel cr a1i 2re remulcld cn nnmulcld recnd
      cle wbr caddc cbc cfz cfv 2nn0 nnnn0d nn0mulcld reexpcl mpan syl readdcld
      clcmf 1red 2nn nn0ge0d nnge1d lemulge12d bccl2d wss fz1ssnn fzfi lcmfnncl
      cfn mp2an lcmineqlem17 nnrpd lemul2d mpbid mulassd lcmineqlem19 peano2nnd
      cdvds cz wi nnzd dvdsle syl2anc mpd eqbrtrrd letrd ) ABDDBEFZGFZEFZBWAHUA
      FZWABUBFZEFZEFZHWDUCFZULUDZABWBABCIZAWAJKZWBLKZADBDJKAUEMABCUFZUGDLKZWKWL
      NDWAUHUIUJZOABWFWJAWDWEAWAHADBWNANMZWJOAUMUKZAWEABWAADBDPKAUNMZCQZWMABDWJ
      WPABWMUOADWRUPUQURZIZOZOAWIWIPKZAWHPUSWHVCKXCWDUTHWDVAWHVBVDMZIAWBWFSTWCW
      GSTABWMVEAWBWFBWOXBABCVFVGVHABWDEFZWEEFZWGWISABWDWEABWJRAWDWQRAWEXARVIAXF
      WIVLTZXFWISTZABCVJAXFVMKXCXGXHVNAXFAXEWEABWDCAWAWSVKQWTQVOXDXFWIVPVQVRVSV
      T $.
  $}

  ${
    lcmineqlem21.1 $e |- ( ph -> N e. NN ) $.
    lcmineqlem21.2 $e |- ( ph -> 4 <_ N ) $.
    $( The lcm inequality lemma without base cases 7 and 8.  (Contributed by
       metakunt, 12-May-2024.) $)
    lcmineqlem21 $p |- ( ph -> ( 2 ^ ( ( 2 x. N ) + 2 ) ) <_
                     ( _lcm ` ( 1 ... ( ( 2 x. N ) + 1 ) ) ) ) $=
      ( c2 cmul co caddc cexp c1 cfz clcmf cfv wcel a1i nnred cn cle wbr c4 cn0
      nn0red nnnn0d nn0mulcld nn0addcld reexpcld crp 2rp cz 2z zmulcld rpexpcld
      2nn0 nnzd rpred remulcld wss cfn fz1ssnn fzfi lcmfnncl mp2an cr 4re mpbid
      lemul1d expaddd sq2 oveq2i eqtrdi rpcnd recnd mulcomd eqtrd breq1d mpbird
      2cnd lcmineqlem20 letrd ) AEEBFGZEHGZIGZBEVTIGZFGZJVTJHGZKGZLMZAEWAAEEUAN
      AUMOZUBAVTEAEBWHABCUCUDZWHUEUFABWCABCPZAWCAEVTEUGNAUHOAEBEUINAUJOABCUNUKU
      LZUOUPAWGWGQNZAWFQUQWFURNWLWEUSJWEUTWFVAVBOPAWBWDRSTWCFGZWDRSZATBRSWNDATB
      WCTVCNAVDOZWJWKVFVEAWBWMWDRAWBWCTFGZWMAWBWCEEIGZFGWPAEVTEAVQWHWIVGWQTWCFV
      HVIVJAWCTAWCWKVKATWOVLVMVNVOVPABCVRVS $.
  $}

  ${
    lcmineqlem22.1 $e |- ( ph -> N e. NN ) $.
    lcmineqlem22.2 $e |- ( ph -> 4 <_ N ) $.
    $( The lcm inequality lemma without base cases 7 and 8.  (Contributed by
       metakunt, 12-May-2024.) $)
    lcmineqlem22 $p |- ( ph -> ( ( 2 ^ ( ( 2 x. N ) + 1 ) ) <_
                     ( _lcm ` ( 1 ... ( ( 2 x. N ) + 1 ) ) )
      /\ ( 2 ^ ( ( 2 x. N ) + 2 ) ) <_
                   ( _lcm ` ( 1 ... ( ( 2 x. N ) + 2 ) ) ) ) ) $=
      ( c2 co c1 caddc cfz clcmf cfv cle wbr wcel a1i cn nnred cz cdvds clcm cr
      cmul cexp 2re cn0 2nn0 nn0mulcld 1nn0 nn0addcld reexpcld wss fz1ssnn fzfi
      nnnn0d cfn lcmfnncl mp2an 1red remulcld clt 1lt2 leadd2dd 2z nnzd zmulcld
      ltled peano2zd zaddcld leexp2d mpbid lcmineqlem21 letrd wa dvdslcm simpld
      jca syl cmin 2nn nnmulcld nnaddcld lcmfunnnd recnd 1cnd addsubassd oveq2i
      2m1e1 eqtrdi oveq2d fveq2d oveq1d eqtrd breqtrrd wi dvdsle mpd ) AEEBUBFZ
      GHFZUCFZGWRIFZJKZLMEWQEHFZUCFZGXBIFZJKZLMAWSXCXAAEWREUANAUDOZAWQGAEBEUENA
      UFOZABCUNUGZGUENAUHOUIUJAEXBXFAWQEXHXGUIUJZAXAXAPNZAWTPUKWTUONXJWRULGWRUM
      WTUPUQOZQZAWRXBLMWSXCLMAGEWQAURZXFAEBXFABCQUSZAGEXMXFGEUTMAVAOZVFVBAEWRXB
      XFAWQAEBERNAVCOZABCVDVEZVGAWQEXQXPVHZXOVIVJABCDVKZVLAXCXAXEXIXLAXEXEPNZAX
      DPUKXDUONXTXBULGXBUMXDUPUQOZQXSAXAXESMZXAXELMZAXAXAXBTFZXESAXAYDSMZXBYDSM
      ZAXARNZXBRNZVMYEYFVMAYGYHAXAXKVDZXRVPXAXBVNVQVOAXEGXBGVRFZIFZJKZXBTFYDAXB
      AWQEAEBEPNAVSOZCVTYMWAWBAYLXAXBTAYKWTJAYJWRGIAYJWQEGVRFZHFWRAWQEGAWQXNWCA
      EXFWCAWDWEYNGWQHWGWFWHWIWJWKWLWMAYGXTVMYBYCWNAYGXTYIYAVPXAXEWOVQWPVLVP $.
  $}

  ${
    lcmineqlem23.1 $e |- ( ph -> N e. NN ) $.
    lcmineqlem23.2 $e |- ( ph -> 9 <_ N ) $.
    $( Penultimate step to the lcm inequality lemma.  (Contributed by metakunt,
       12-May-2024.) $)
    lcmineqlem23 $p |- ( ph -> ( 2 ^ N ) <_
                     ( _lcm ` ( 1 ... N ) ) ) $=
      ( c2 cdvds wbr cexp co c1 cfz cle caddc wcel cn a1i c4 c5 c9 c8 clcmf cfv
      wa cdiv cmin cmul cz cc0 clt wb 2nn jca nndivdvds syl biimpa nnzd zsubcld
      1zzd 0red cr 4re nnred 1red resubcld 4pos 5m1e4 5re cdc nncni 5cn mulcomi
      wceq 5t2e10 eqtri recni nnne0i divmuli mpbir adantr crp 2rp 9p1e10 wo 9re
      10re leloed mpbid 2t4e8 8re 4cn 4nn eqeltri 8nn mp2an 9m1e8 breqtrri nnzi
      9nn oddm1even ax-mp breq2 mtbii con2i adantl olcnd zltp1le mpan eqbrtrrid
      lediv1dd lesub1dd ltletrd elnnz sylibr lcmineqlem22 simprd halfcld muls1d
      wn nncnd oveq1d mulcld npcand eqtrd nnne0d divcan2d oveq2d fveq2d breq12d
      8pos nndivdvdsd nnrpd simpld 1cnd subcld pm2.61dan ) AEBFGZEBHIZJBKIZUAUB
      ZLGZAYPUCZEEBEUDIZJUEIZUFIZEMIZHIZJUUEKIZUAUBZLGZYTUUAEUUDJMIZHIJUUJKIUAU
      BLGUUIUUAUUCUUAUUCUGNZUHUUCUIGZUCUUCONUUAUUKUULUUAUUBJUUAUUBAYPUUBONZABON
      ZEONZUCYPUUMUJAUUNUUOCUUOAUKPZULBEUMUNUOZUPUUAURUQUUAUHQUUCUUAUSQUTNUUAVA
      PUUAUUBJUUAUUBUUQVBZUUAVCZVDUHQUIGUUAVEPUUAQRJUEIUUCLVFUUARUUBJRUTNUUAVGP
      UURUUSUUARJUHVHZEUDIZUUBLUVARVLERUFIZUUTVLUVBREUFIUUTEREUKVIZVJVKVMVNUUTE
      RUUTWEVOUVCVJEUKVPZVQVRUUAUUTBEUUTUTNUUAWEPABUTNYPABCVBZVSEVTNUUAWAPUUAUU
      TSJMIZBLWBUUASBUIGZUVFBLGZUUAUVGSBVLZAUVGUVIWCZYPASBLGUVJDASBSUTNAWDPZUVE
      WFWGVSYPUVIXRAUVIYPUVIESFGZYPUVLXRZESJUEIZFGZETUVNFETFGZTEUDIZONZUVQQOUVQ
      QVLEQUFITVLWHTEQTWIVOUVCWJUVDVQVRZWKWLTONUUOUVPUVRUJWMUKTEUMWNVRWOWPSUGNZ
      UVMUVOUJSWRWQZSWSWTVRSBEFXAXBXCXDXEAUVGUVHUJZYPABUGNZUWBABCUPZUVTUWCUWBUW
      ASBXFXGUNVSWGXHXIXHXJXHZXKULUUCXLXMUWEXNXOAUUIYTUJYPAUUFYQUUHYSLAUUEBEHAU
      UEEUUBUFIZBAUUEUWFEUEIZEMIUWFAUUDUWGEMAEUUBAEUUPXSZABABCXSZXPZXQXTAUWFEAE
      UUBUWHUWJYAUWHYBYCABEUWIUWHAEUUPYDZYEYCZYFAUUGYRUAAUUEBJKUWLYFYGYHVSWGAYP
      XRZUCZEEBJUEIZEUDIZUFIZJMIZHIZJUWRKIZUAUBZLGZYTUWNUXBEUWQEMIZHIJUXCKIUAUB
      LGUWNUWPUWNEUWOFGZUWPONAUWMUXDAUWCUWMUXDUJUWDBWSUNUOUWNEUWOUUOUWNUKPAUWOO
      NZUWMAUWOUGNZUHUWOUIGZUCUXEAUXFUXGABJUWDAURUQAUHTUWOAUSTUTNAWIPZABJUVEAVC
      ZVDZUHTUIGAYIPATUVNUWOLWOASBJUVKUVEUXIDXJXHZXKULUWOXLXMVSYJWGAQUWPLGUWMAQ
      UVQUWPLUVSATUWOEUXHUXJAEUUPYKUXKXIXHVSXNYLAUXBYTUJUWMAUWSYQUXAYSLAUWRBEHA
      UWRUWOJMIBAUWQUWOJMAUWOEABJUWIAYMZYNUWHUWKYEXTABJUWIUXLYBYCZYFAUWTYRUAAUW
      RBJKUXMYFYGYHVSWGYO $.
  $}

  ${
    lcmineqlem.1 $e |- ( ph -> N e. NN ) $.
    lcmineqlem.2 $e |- ( ph -> 7 <_ N ) $.
    $( The least common multiple inequality lemma, a central result for future
       use.  Theorem 3.1 from ~ https://www3.nd.edu/%7eandyp/notes/AKS.pdf
       (Contributed by metakunt, 16-May-2024.) $)
    lcmineqlem $p |- ( ph -> ( 2 ^ N ) <_ ( _lcm ` ( 1 ... N ) ) ) $=
      ( c7 cle wbr c2 cexp co c1 cfz clcmf clt wcel c8 cdc c4 cc0 decnncl wo cr
      cfv wceq 7re a1i nnred leloed caddc cz wb nnzd 7nn nnzi zltp1le syl 7p1e8
      breq1i bitrdi 8re wa cn adantr c9 8p1e9 8nn biimpd eqbrtrrid lcmineqlem23
      mpan imp ex c5 2nn0 8nn0 5nn0 4nn0 6nn0 0nn0 2lt8 5lt10 6lt10 3decltc 5nn
      c6 nnnn0i 6nn nnrei 4nn decnncl2 ltlei ax-mp 2exp8 eqtr3id lcm8un breq12d
      oveq2 fveq2d mpbii adantl jaod sylbid wi 1nn0 1lt4 2lt10 8lt10 2nn lcm7un
      2exp7 mpd ) AEBFGZHBIJZKBLJZMUCZFGZDAXLEBNGZEBUDZUAXPAEBEUBOAUEUFABCUGZUH
      AXQXPXRAXQPBFGZXPAXQEKUIJZBFGZXTABUJOZXQYBUKZABCULZEUJOYCYDEUMUNEBUOVJUPY
      APBFUQURUSAXTPBNGZPBUDZUAXPAPBPUBOAUTUFXSUHAYFXPYGAYFXPAYFVAZBABVBOYFCVCY
      HVDPKUIJZBFVEAYFYIBFGZAYFYJAYCYFYJUKZYEPUJOYCYKPVFUNPBUOVJUPVGVKVHVIVLAYG
      XPYGXPAYGHVMQZWEQZPRQZSQZFGZXPYMYONGYPHPVMRWESVNVOVPVQVRVSVTWAWBWCYMYOYMY
      LWEYLHVMVNWDTWFWGTWHYOYNPRVOWITWJWHWKWLYGYMXMYOXOFYGYMHPIJXMWMPBHIWQWNYGY
      OKPLJZMUCXOWOYGYQXNMPBKLWQWRWNWPWSWTVLXAXBXBXRXPXCAXRKHQZPQZRHQZSQZFGZXPY
      SUUANGUUBKRHHPSXDVQVNVNVOVSXEXFXGWCYSUUAYSYRPYRKHXDXHTWFVFTWHUUAYTRHVQXHT
      WJWHWKWLXRYSXMUUAXOFXRYSHEIJXMXJEBHIWQWNXRUUAKELJZMUCXOXIXRUUCXNMEBKLWQWR
      WNWPWSUFXAXBXK $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Logarithm inequalities
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $( 3 to the power of 7 equals 2187.  (Contributed by metakunt,
       21-Aug-2024.) $)
    3exp7 $p |- ( 3 ^ 7 ) = ; ; ; 2 1 8 7 $=
      ( c3 c2 c1 cdc c8 c7 c6 3nn0 c9 co 7nn0 2nn0 1nn0 8nn0 0nn0 cmul caddc c4
      cc0 4nn0 6nn0 6p1e7 cexp deccl 9nn0 2t3e6 3exp3 eqid nn0cni mul02i ax-1cn
      dec0h 6cn addcomli oveq12i 7cn addlidi eqtri 2t2e4 2cn 4p2e6 7t2e14 1p1e2
      mulcomli 8cn 8p4e12 decaddci decma2c decmac 4p4e8 decaddi 7t7e49 decmul2c
      4cn decmul1c numexp2x 7t3e21 1p0e1 oveq1i 6p2e8 decma 9t3e27 numexpp1 ) A
      BCDZEDZFDGFHUAUBFBDZIWEFABAGUCJHFBKLUDUEAWFIDBFDZAGHHUFUGBFWFIWGCEDZWGBFL
      KUDZLKWGUHZUECEMNUDSBCEWGFBGBWHOLMNBLULZWHUHWILUASWGPJZCGQJZQJSFQJFWLSWMF
      QWGWGWIUIUJGCFUMUKUBUNUOFUPUQURBFSEBGBBWGELKONWJENULLLLBBPJZSBQJZQJRBQJGW
      NRWOBQUSBUTUQUOVAURCRBBBFPJEMTNFBCRDUPUTVBVDVCLERCBDVEVNVFUNVGVHVIBFWHIFR
      WGKLKWJUETCREFBPJRMTTVBVJVKVLVMVOVPKLFBSBAWDEWFBKLOLWFUHWKHBCCFAPJSLMOVQV
      RVKBAPJZBQJGBQJEWPGBQUFVSVTURWAWBVOWC $.
  $}

  $( First inequality in inequality chain, proposed by Mario Carneiro
     (Contributed by metakunt, 22-May-2024.) $)
  3lexlogpow5ineq1 $p |- 9 < ( ( ; 1 1 / 7 ) ^ 5 ) $=
    ( c9 c1 cdc c5 co c7 cmul c6 c8 c2 c4 caddc eqid eqtri 2nn0 4nn0 deccl 1nn0
    cc0 0nn0 cexp cdiv clt wbr 2p2e4 oveq1i 4p1e5 eqtr4i oveq2i cc wcel wa wceq
    cn0 7cn nn0addcli pm3.2i expp1 ax-mp w3a 3pm3.2i expadd sqvali oveq12i 9nn0
    7t7e49 6nn0 4t4e16 1p1e2 4p4e8 8cn 6cn 8p6e14 addcomli decaddci 3nn0 9t4e36
    c3 3p1e4 6p4e10 decaddci2 decmac 8nn0 9cn mulcomli 9t9e81 decmul1c decmul2c
    4cn 3eqtri 7nn0 2cn 7t2e14 4p2e6 decaddi 7t4e28 addridi mul01i dec0h eqcomi
    00id ax-1cn mulridi nn0cni mulcomi 5nn0 mullidi addlidi 9p6e15 9t6e54 5p1e6
    7p4e11 9t8e72 mul02i decma 9t7e63 3lt10 6lt10 2lt10 1lt10 5lt6 declt decltc
    0cn 6nn eqbrtri decsuc decadd 5cn 2t1e2 2t2e4 decma2c 0p1e1 breqtri cr 7pos
    7re reexpcl wtru a1i 6p1e7 wb cz 5nn expgt0 9re 1nn decnncl nnrei ltmuldivi
    nnzi mpbi 0red ltned necomd expdivd eqcomd mptru ) ABBCZDUAEZFDUAEZUBEZUUSF
    UBEDUAEZUCAUVAGEZUUTUCUDZAUVBUCUDZUVDBHCZBCZSCZDCZBCZUUTUCUVDAUVGICZSCZFCZG
    EZUVKUCUVAUVNAGUVAJKCZSCZBCZFGEZUVNUVAFJJLEZBLEZUAEZFUVTUAEZFGEZUVSDUWAFUAD
    DUWADMUWAKBLEZDUVTKBLUEUFUGNUHUIFUJUKZUVTUNUKZULUWBUWDUMUWFUWGUOJJOOUPUQFUV
    TURUSUWCUVRFGUWCFJUAEZUWHGEZUVRUWFJUNUKZUWJUTUWCUWIUMUWFUWJUWJUOOOVAFJJVBUS
    UWIKACZUWKGEUVRUWHUWKUWHUWKGUWHFFGEUWKFUOVCVFNZUWLVDKAUVQBUWKKKCZUWKKAPVEQP
    VEUWKMZRKKPPQKAKKKUVPSKUWKUWMPVEPPUWNUWMMPTPBHKJKKGEKKLEZRVGKKPPUPVHVIPHUWO
    LEHILEBKCZUWOIHLVJUIIHUWPVKVLVMVNZNVOVRHKAKGEKVPVGPVQVSVTWAWBKAUWMBAIUWKVEP
    VEUWNRWCVRHKKKAGEIVPVGWCAKVRHCWDWIVQWEVSPUWQVOWFWGWHNNUFWJUVQBUVMFFSUVRWKUV
    PSJKOPQZTQRUVRMWKTUVLSSUVQFGESUVGIBHRVGQZWCQZTTUVPSUVLSFSUVQWKUWRTUVQMTTUVG
    IIUVPFGESUWSWCTJKUVGIFJUVPWKOPUVPMZWCOBKHJFGEJRPOFJUWPUOWLWMWEWNWOFKJICUOWI
    WPWEWGIVKWQWOFSSSCZUOYDFSGESUXBFUOWRSUXBSTWSWTUHWEWGXAWOFBSFCZUOXBFBGEFUXCF
    UOXCFUXCFWKWSZWTZUHWEWGNUIUVOUVNAGEZUVKUCAUVNWDUVNUVMFUVLSUWTTQZWKQXDXEUXFB
    DCZBCZJCZHCZVRCUVKUCUVMFUXKVRAHUVNVEUXGWKUVNMVPVGUVLSSHAUXJHUVMHUWTTTVGUVMM
    HVGWSVEUXIJJUVLAGESUXHBBDRXFQZRQZOTUVGIUXIJAFUVLVEUWSWCUVLMOWKBHSFAUXHBHUVG
    FRVGTWKUVGMUXDVERVGBAGEZSHLEZLEAHLEUXHUXNAUXOHLAWDXGHVLXHZVDXINDKBHHAGEFXFP
    WKAHDKCWDVLXJWEXKRFKUUSUOWIXLVNZVOWBAIFJCWDVKXMWEWGJWLWQZWOSAGEZHLEUXOHUXSS
    HLAWDXNUFUXPNXOAFHVRCWDUOXPWEWGUXKUVJVRBUXJHUXIJUXMOQZVGQUVIDUVHSUVGBUWSRQZ
    TQZXFQVPRXQUXJUVIHDUXTUYBVGXFXRUXIUVHJSUXMUYAOTXSUXHUVGBBUXLUWSRRXTBDHRXFYE
    YAYBYCYCYCYCYFYFYFUUTUVKUUTUWPHCZKCZBCZUUSGEZUVKUUTUUSUWEUAEZUYFDUWEUUSUAUW
    EDUGWTUIUYGUUSKUAEZUUSGEZUYFUUSUJUKZKUNUKZULUYGUYIUMUYJUYKUUSBBRRQZXDZPUQUU
    SKURUSUYHUYEUUSGUYHUUSUVTUAEZUYEKUVTUUSUAUVTKUEWTUIUYNUUSJUAEZUYOGEZUYEUYJU
    WJUWJUTUYNUYPUMUYJUWJUWJUYMOOVAUUSJJVBUSUYPBJCZBCZUYRGEUYEUYOUYRUYOUYRGUYOU
    USUUSGEUYRUUSUYMVCBBUYQBUUSBUUSUYLRRUUSMZRRBBJBUUSGEZRRVIUUSUYMXGZYGVUAWGNZ
    VUBVDUYQBUYDBUYRUYQUYRUYQBBJROQZRQZVUCRUYRMZRVUCBJBJUYRUYCKUVPUYQUYQROROUYQ
    MZVUFVUDPUWRUYQBJDUWPHBUYRGEBUVPLEVUCROXFUYRUYRVUDXDXGZSBJKJDBUVPTROPBRWSZU
    XAJWLXHKBDWIXBUGVNYHBJKUYQJROOVUFUEWODBHYIXBXKVNZYHUYQBSJJUVPKSUYRJVUCRTOVU
    EJOWSOPTJKKJUYQGESSLEZOPSSTTUPBJJKJSUYQOROVUFPTJBGEZSLEJSLEJVUKJSLYJUFUXRNJ
    JGEKSKCZYKKVULKPWSZWTZUHWHKVUJLEKSLEZKVUJSKLXAUIKWIWQZNWOVUKJLEZKVULVUQUVTK
    VUKJJLYJUFUENVUNUHYLWBVUGWGNNNUFNNUYDBUVJBUUSBUYEUYLUYCKUWPHBKRPQZVGQZPQRUY
    EMRRUYCKSBUUSUVIDKUYDBVUSPTRUYDMVUHUYLXFPUWPHSKUUSUVHSFUYCSKLEVURVGTPUYCMKS
    VULWIYDVUOKVULVUPVUNUHVNUYLTWKBKSFUUSUVGBDUWPSFLERPTWKUWPMFSUXCUOYDFSLEFUXC
    FUOWQUXEUHVNUYLRXFBBHUYTSDLEZRRSDTXFUPVUABVUTLEBDLEHVUTDBLDYIXHUIVUINWOBBSF
    KDBBUUSFRRTWKUYSUXDPRRKBGEZSBLEZLEUWEDVVAKVVBBLKWIXCZYMVDUGNVVAFLEKFLEUUSVV
    AKFLVVCUFUXQNYLWBBBSKHFSBUUSKRRTPUYSVUMVGTRHBGEZVVBLEHBLEFVVDHVVBBLHVLXCZBX
    BXHVDUUANVVDKLEHKLEBSCVVDHKKLVVEKMVDVTNYLWBBBSBKKDSUUSBRRTRUYSVUHPXFTVVAVUJ
    LEVUOKVVAKVUJSLVVCXAVDVUPNVVABLEZDSDCZVVFUWEDVVAKBLVVCUFUGNDVVGDXFWSWTUHYLW
    BVUAWGNWTYNSUVAUCUDZUVEUVFUUBFYOUKZDUUCUKZSFUCUDZUTVVHVVIVVJVVKYQDUUDUUKYPV
    AFDUUEUSAUUTUVAUUFUUSYOUKZDUNUKZULUUTYOUKVVLVVMUUSBBRUUGUUHUUIXFUQUUSDYRUSV
    VIVVMULUVAYOUKVVIVVMYQXFUQFDYRUSUUJUSUULUVBUVCUMYSUVCUVBYSUUSFDUYJYSUYMYTUW
    FYSUOYTYSSFYSSFYSUUMVVKYSYPYTUUNUUOVVMYSXFYTUUPUUQUURYN $.

  ${
    3lexlogpow5ineq2.1 $e |- ( ph -> X e. RR ) $.
    3lexlogpow5ineq2.2 $e |- ( ph -> 3 <_ X ) $.
    $( Second inequality in inequality chain, proposed by Mario Carneiro.
       (Contributed by metakunt, 22-May-2024.) $)
    3lexlogpow5ineq2 $p |- ( ph ->
    ( ( ; 1 1 / 7 ) ^ 5 ) <_ ( ( 2 logb X ) ^ 5 ) ) $=
      ( c1 cdc c7 co c2 clogb wcel decnncl a1i cc0 clt wbr c3 cle 0nn0 c8 c5 cn
      cdiv 1nn0 1nn nnred 7re 0red 7pos ltned necomd redivcld 2re 2pos 3re 3pos
      cr ltletrd 1red 1lt2 relogbcld cn0 5nn0 7nn nnrpd wtru tru 9re 9pos ltled
      c9 ax-mp declei divge0d cmul c4 cexp wceq 2exp11 eqcomi oveq2d elrpd nnzd
      relogbexpd eqtrd eqcomd cz 2z leidd 2nn0 deccl 4nn0 8nn 8nn0 decltdi 7nn0
      4nn caddc 8re nn0addge1i 8p1e9 breqtri 4lt10 declt decltc decleh logblebd
      0lt1 eqbrtrd recnd 3exp7 relogbzexpd mulcomd 3brtr3d lemul1d mpbird letrd
      divcan1d leexp1ad ) AEEFZGUCHZIBJHZUAAXTGAXTXTUBKAEEUDUELMZUFZGUQKAUGMZAN
      GANGAUHZNGOPAUIMUJUKZULZAIBIUQKAUMMZNIOPAUNMZCANQBYFQUQKAUOMZCNQOPAUPMZDU
      RZAEIAEIAUSEIOPAUTMUJUKZVAZUAVBKAVCMAXTGYDAGGUBKAVDMZVEZNXTRPAEENUEUDSVFN
      VKRPVGVFNVKVFUHVKUQKVFVHMNVKOPVFVIMVJVLZVMMVNAYAIQJHZYBYHAIQYIYJYKYLYNVAZ
      YOAYAYSRPYAGVOHZYSGVOHZRPAXTIIEFZTFZGFZJHZUUAUUBRAXTIINFZVPFZTFZJHZUUFRAU
      UJXTAUUJIIXTVQHZJHXTAUUIUUKIJUUIUUKVRAUUKUUIVSVTMWAAIXTAIYIYJWBZYNAXTYCWC
      WDWEWFAIUUIUUEIWGKAWHMZAIYIWIZAUUIUUIUBKAUUHTUUGVPINWJSWKZWLWKZWMLMUFNUUI
      OPAUUHTNUUGVPUUOWQLWNSYRWOMAUUEUUEUBKAUUDGUUCTIEWJUDWKZWNWKZVDLMUFNUUEOPA
      UUDGNUUCTUUQWMLWPSYRWOMUUIUUERPAUUHUUDTGUUPUURWNWPTTEWRHVKRTEWSUDWTXAXBUU
      GUUCVPTUUOUUQWLWNXCINEWJSUEXHXDXEXFMXGXIAUUAXTAXTGAXTYDXJAGYEXJZYGXRWFAUU
      FGYSVOHZUUBAUUFIQGVQHZJHUUTAUUEUVAIJUUEUVAVRAUVAUUEXKVTMWAAIQGUULYNAQYKYL
      WBAGYPWCXLWEAGYSUUSAYSYTXJXMWEXNAYAYSGYHYTYQXOXPAIQBUUMUUNYKYLCYMDXGXQXS
      $.
  $}

  ${
    3lexlogpow5ineq4.1 $e |- ( ph -> X e. RR ) $.
    3lexlogpow5ineq4.2 $e |- ( ph -> 3 <_ X ) $.
    $( Sharper logarithm inequality chain.  (Contributed by metakunt,
       21-Aug-2024.) $)
    3lexlogpow5ineq4 $p |- ( ph -> 9 < ( ( 2 logb X ) ^ 5 ) ) $=
      ( c9 c1 c7 co c5 cexp c2 cr wcel a1i cc0 clt wbr ltned necomd c3 cdc cdiv
      clogb 9re cn 11nn nnred 7re 0red 7pos redivcld cn0 5nn0 reexpcld 2re 2pos
      3re 3pos ltletrd 1red 1lt2 relogbcld 3lexlogpow5ineq1 3lexlogpow5ineq2 )
      AEFFUAZGUBHZIJHZKBUCHZIJHELMAUDNAVFIAVEGAVEVEUEMAUFNUGGLMAUHNAOGAOGAUIZOG
      PQAUJNRSUKIULMAUMNZUNAVHIAKBKLMAUONOKPQAUPNCAOTBVITLMAUQNCOTPQAURNDUSAFKA
      FKAUTFKPQAVANRSVBVJUNEVGPQAVCNABCDVDUS $.
  $}

  ${
    3lexlogpow5ineq3.1 $e |- ( ph -> X e. RR ) $.
    3lexlogpow5ineq3.2 $e |- ( ph -> 3 <_ X ) $.
    $( Combined inequality chain for a specific power of the binary logarithm,
       proposed by Mario Carneiro.  (Contributed by metakunt, 22-May-2024.) $)
    3lexlogpow5ineq3 $p |- ( ph -> 7 < ( ( 2 logb X ) ^ 5 ) ) $=
      ( c7 c9 c2 clogb co c5 cexp cr wcel 7re a1i cc0 clt wbr c3 c1 9re 2re 3re
      2pos 0red 3pos ltletrd 1red 1lt2 ltned necomd relogbcld cn0 5nn0 reexpcld
      7lt9 3lexlogpow5ineq4 lttrd ) AEFGBHIZJKIELMANOFLMAUAOAUSJAGBGLMAUBOPGQRA
      UDOCAPSBAUESLMAUCOCPSQRAUFODUGATGATGAUHTGQRAUIOUJUKULJUMMAUNOUOEFQRAUPOAB
      CDUQUR $.
  $}

  ${
    $( Result for bound in AKS inequality lemma.  (Contributed by metakunt,
       21-Aug-2024.) $)
    3lexlogpow2ineq1 $p |- ( ( 3 / 2 ) < ( 2 logb 3 ) /\
     ( 2 logb 3 ) < ( 5 / 3 ) ) $=
      ( wtru c3 c2 co clogb clt wbr c5 cmul cexp c8 c9 wcel crp ax-mp nnrp wceq
      cn a1i eqtrd cdiv wa tru 8lt9 cuz cfv w3a wb cz 2z 8nn 9nn 3pm3.2i logblt
      uzid mpbi eqid cu2 eqtr4i oveq2d 2rp c1 1red 1lt2 ltned necomd relogbexpd
      3z sq3 3brtr3d 3re recnd 2re cc0 2pos gt0ne0d divcan1d eqcomd relogbzexpd
      cr 3pos elrpd relogbcld mulcomd rehalfcld ltmul1d mpbird c7 cdc 2nn0 3nn0
      7nn0 7lt10 2lt3 7nn decnncl 2nn 2exp5 breqtrd 3exp3 5re 5nn nnzd redivcld
      decltc jca ) ABCUADZCBEDZFGZXHHBUADZFGZUBUCAXIXKAXIXGCIDZXHCIDZFGABCBCJDZ
      EDZXLXMFACKEDZCLEDZBXOFXPXQFGZAKLFGZXRUDCCUEUFMZKNMZLNMZUGXSXRUHXTYAYBCUI
      MZXTUJCUOOZKRMYAUKKPOLRMYBULLPOUMCKLUNOUPSAXPCCBJDZEDBAKYECEKYEQAKKYEKUQU
      RUSSUTACBCNMAVASZAVBCAVBCAVCVBCFGAVDSVEVFZBUIMAVHSZVGTALXNCELXNQALLXNLUQV
      IUSSUTVJAXLBABCABBVTMAVKSZVLZACCVTMAVMSZVLZACVNCFGAVOSZVPVQVRAXOCXHIDXMAC
      BCYFYGABYIVNBFGAWASZWBZYCAUJSVSACXHYLAXHACBYKYMYIYNYGWCZVLZWDTVJAXGXHCABY
      IWEYPYFWFWGAXKXHBIDZXJBIDZFGACCWHWIZEDZCCHJDZEDZYRYSFAUUACBCWIZEDZUUCFUUA
      UUEFGZAYTUUDFGZUUFCBWHCWJWKWLWJWMWNXEXTYTNMZUUDNMZUGUUGUUFUHXTUUHUUIYDYTR
      MUUHCWHWJWOWPYTPOUUDRMUUIBCWKWQWPUUDPOUMCYTUUDUNOUPSAUUDUUBCEUUDUUBQAUUDU
      UDUUBUUDUQWRUSSUTWSAUUABXHIDZYRAUUACBBJDZEDUUJAYTUUKCEYTUUKQAYTYTUUKYTUQW
      TUSSUTACBBYFYGYOYHVSTABXHYJYQWDTAYSUUCAYSHUUCAHBAHHVTMAXASZVLYJABYNVPZVQA
      UUCHACHYFYGAHHRMAXBSXCVGVRTVRVJAXHXJBYPAHBUULYIUUMXDYOWFWGXFO $.
  $}

  ${
    $( Result for bound in AKS inequality lemma.  (Contributed by metakunt,
       21-Aug-2024.) $)
    3lexlogpow2ineq2 $p |- ( 2 < ( ( 2 logb 3 ) ^ 2 ) /\
     ( ( 2 logb 3 ) ^ 2 ) < 3 ) $=
      ( wtru c2 c3 co clt wbr cdiv cr wcel a1i c9 c4 cmul wceq eqbrtrd recnd c5
      cc0 cn crp clogb cexp wa tru 2re rehalfcld resqcld 2pos 3pos c1 1red 1lt2
      3re ltned necomd relogbcld 2cnd cc 4cn 0red 4pos divcan4d eqcomd remulcld
      4re 9re elrpd 2t4e8 8lt9 ltdiv1dd eqid 3t3e9 eqtr4i 2t2e4 oveq12d gt0ne0d
      c8 divmuldivd eqtrd syl breqtrd 3lexlogpow2ineq1 simpld 2nn 3rp rphalfcld
      sqval wb divgt0d lttrd rpexpmord mpbid 5re gtned redivcld nnnn0d reexpcld
      syl3anc simprd 5nn nnrpd rpdivcld sqvald cdc 5t5e25 c7 2nn0 5nn0 7nn 5lt7
      declt 9cn 3cn 9t3e27 mulcomli breqtrri decnncl nnred 9nn ltdivmul2d ax-mp
      mpbird jca ) ABBCUADZBUBDZEFZYECEFZUCUDAYFYGABCBGDZBUBDZYEBHIAUEJZAYHACCH
      IAUMJZUFZUGAYDABCYJRBEFAUHJZYKRCEFAUIJZAUJBAUJBAUKUJBEFAULJUNUOUPZUGZABKL
      GDZYIEABBLMDZLGDZYQEAYSBABLAUQLURIAUSJARLARLAUTZRLEFAVAJZUNUOVBVCAYRKLABL
      YJLHIAVEJZVDKHIAVFJALUUBUUAVGAYRVQKEYRVQNAVHJVQKEFAVIJOVJOAYQYHYHMDZYIAYQ
      CCMDZBBMDZGDZUUCAKUUDLUUEGKUUDNAKKUUDKVKVLVMJLUUENALLUUELVKVNVMJVOAUUCUUF
      ACBCBACYKPZABYJPZUUGUUHABYMVPZUUIVRVCVSAYHURIZUUCYINAYHYLPUUJYIUUCYHWGVCV
      TVSWAAYHYDEFZYIYEEFZAUUKYDQCGDZEFZUUKUUNUCAWBJZWCZABSIZYHTIYDTIZUUKUULWHU
      UQAWDJZACCTIAWEJZWFAYDYOARYHYDYTYLYOACBYKYJYNYMWIUUPWJVGZYHYDBWKWRWLWJAYE
      UUMBUBDZCYPAUUMBAQCQHIAWMJZYKARCYTYNWNZWOZABUUSWPWQYKAUUNYEUVBEFZAUUKUUNU
      UOWSAUUQUURUUMTIUUNUVFWHUUSUVAAQCAQQSIAWTJXAUUTXBYDUUMBWKWRWLAUVBUUMUUMMD
      ZCEAUUMAUUMUVEPXCAUVGQQMDZUUDGDZCEAQCQCAQUVCPZUUGUVJUUGUVDUVDVRAUVIBQXDZK
      GDZCEAUVHUVKUUDKGUVHUVKNAXEJUUDKNAVLJVOAUVLCEFUVKCKMDZEFZUVNAUVKBXFXDZUVM
      EBQXFXGXHXIXJXKKCUVOXLXMXNXOXPJAUVKCKAUVKUVKSIABQXGWTXQJXRYKAKKSIAXSJXAXT
      YBOOOWJYCYA $.
  $}

  ${
    $( Result for bound in AKS inequality lemma.  (Contributed by metakunt,
       21-Aug-2024.) $)
    3lexlogpow5ineq5 $p |- ( ( 2 logb 3 ) ^ 5 ) <_ ; 1 5 $=
      ( c2 c3 co c5 cexp c1 cdc cle wbr wtru wcel a1i cc0 5nn0 c4 cmul caddc c9
      wceq 2nn0 clogb cdiv cr 2re clt 2pos 3re 3pos 1red ltned necomd relogbcld
      1lt2 cn0 reexpcld nn0red gt0ne0d redivcld cn 1nn0 decnncl nnred rehalfcld
      5nn 0red divgt0d 3lexlogpow2ineq1 simpli lttrd ltled simpri leexp1ad df-5
      oveq2d recnd 4nn0 expp1d eqtrd c6 c8 6nn0 deccl 7nn0 9nn0 9re mptru 2lt10
      c7 5lt9 6lt7 decltc decleh 8nn0 eqid 0nn0 9cn 8cn 9t8e72 mulcomli addridi
      2cn decaddi ax-1cn mulridi dec0h eqcomi eqtr4i decmul1c eqcomd breqtrd cc
      2p2e4 expaddd sqvali 5t5e25 oveq12d 3eqtrd nn0cni mul02i addcomli oveq12i
      nncni eqtri 5p1e6 addlidi 2t2e4 0p1e1 4p1e5 5t2e10 decmac decmul2c eqtr2d
      6cn decma2c 3cn 3t3e9 9t9e81 oveq1d 3brtr3d mpbird crp 3rp cz 4z rpexpcld
      ledivmuld expdivd nngt0i divdiv2d 9t5e45 3nn0 mullidi oveq1i 3p1e4 5t3e15
      5cn mulcld divmuld elrpd rpdivcld lemuldivd eqbrtrd letrd ) ABUACZDECZFDG
      ZHIJUVEDBUBCZDECZUVFJUVDDJABAUCKJUDLZMAUEIJUFLZBUCKJUGLZMBUEIJUHLZJFAJFAJ
      UIFAUEIJUMLUJUKULZDUNKJNLZUOJUVGDJDBJDUVNUPZUVKJBUVLUQZURZUVNUOJUVFUVFUSK
      JFDUTVDVALVBZJUVDUVGDUVMUVQUVNJMUVDJVEZUVMJMBAUBCZUVDUVSJBUVKVCUVMJBAUVKU
      VIUVLUVJVFUVTUVDUEIZJUWAUVDUVGUEIZVGVHLVIVJJUVDUVGUVMUVQUWBJUWAUWBVGVKLVJ
      VLJUVHUVGOECZUVGPCZUVFHJUVHUVGOFQCZECUWDJDUWEUVGEDUWESJVMLVNJUVGOJUVGUVQV
      OOUNKJVPLZVQVRJUWDUVFHIUWCUVFUVGUBCZHIJDOECZBOECZUBCZRUWCUWGHJUWJRHIUWHUW
      IRPCZHIJVSAGZDGZVTFGZRPCZUWHUWKHJUWMWHAGZRGZUWOHUWMUWQHIJUWLUWPDRVSAWATWB
      WHAWCTWBNWDDRHIJDRUVORUCKJWELZDRUEIJWILVJWFVSWHAAWAWCTTWGWJWKWLLJUWOUWQUW
      OUWQSJVTFUWPRRMUWNWDWMUTUWNWNWDWOWHAAVTRPCMWCTWORVTUWPWPWQWRWSAXAWTXBRFMR
      GZWPXCRFPCRUWSRWPXDRUWSRWDXEXFXGWSXHLXIXJJUWHADGZUWTPCZUWMJUWHDAAQCZECDAE
      CZUXCPCUXAJOUXBDEOUXBSJOOUXBOWNXLXGLZVNJDAADXKKJDVDYBZLAUNKJTLZUXFXMJUXCU
      WTUXCUWTPUXCUWTSJUXCDDPCUWTDUXEXNXOYCLZUXGXPXQUXAUWMSJADUWLDUWTFAGZUWTADT
      NWBZTNUWTWNZNFAUTTWBMAFAUWTVSADAUXHWOTUTTATXEZUXHWNUXITNMUWTPCZFDQCZQCMVS
      QCVSUXLMUXMVSQUWTUWTUXIXRXSDFVSUXEXCYDXTYAVSYMYEYCADMAADAFUWTATNWOTUXJUXK
      TTUTAAPCZMFQCZQCUWEDUXNOUXOFQYFYGYAYHYCFMAADPCAUTWOTDAFMGUXEXAYIWSAXAYEZX
      BYNYJADUXHDDAUWTNTNUXJNTFMADAPCAUTWOTYIUXPXBXOYKXHLYLJUWNUWIRPJUWIUWNJUWI
      BUXBECBAECZUXQPCZUWNJOUXBBEUXDVNJBAABXKKJYOLZUXFUXFXMJUXRRRPCZUWNJUXQRUXQ
      RPUXQRSJUXQBBPCRBYOXNYPYCLZUYAXPUXTUWNSJYQLVRXQXIYRYSJUWHRUWIJDOUVOUWFUOU
      WRJBOBUUAKJUUBLZOUUCKJUUDLUUEUUFYTJUWCUWJJDBOJDUVOVOZUXSUVPUWFUUGXIJUWGUV
      FBPCZDUBCZRJUVFDBJUVFUVRVOZUYCUXSJMDJMDUVSMDUEIJDVDUUHLZUJUKZUVPUUIJUYERS
      DRPCZUYDSJUYIODGZUYDUYIUYJSJRDUYJWPUUPUUJWSLJUYDUYJUYDUYJSJFDODBFUVFUUKUT
      NUVFWNNUTFBPCZFQCBFQCOUYKBFQBYOUULUUMUUNYCUUOXHLXIVRJUYDDRJUVFBUYFUXSUUQU
      YCRXKKJWPLUYHUURYTYLYSJUWCUVFUVGJUVGOUVQUWFUOUVRJDBJDUVOUYGUUSUYBUUTUVAYT
      UVBUVCWF $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Miscellaneous results for AKS formalisation
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d A t x $.  $d B t x $.  $d F t $.  $d G t $.  $d P t $.  $d Q t $.
    $d ph t x $.
    intlewftc.1 $e |- ( ph -> A e. RR ) $.
    intlewftc.2 $e |- ( ph -> B e. RR ) $.
    intlewftc.3 $e |- ( ph -> A <_ B ) $.
    intlewftc.4 $e |- ( ph -> F e. ( ( A [,] B ) -cn-> RR ) ) $.
    intlewftc.5 $e |- ( ph -> G e. ( ( A [,] B ) -cn-> RR ) ) $.
    intlewftc.6 $e |- ( ph -> D = ( RR _D F ) ) $.
    intlewftc.7 $e |- ( ph -> E = ( RR _D G ) ) $.
    intlewftc.8 $e |- ( ph -> D e. ( ( A (,) B ) -cn-> RR ) ) $.
    intlewftc.9 $e |- ( ph -> E e. ( ( A (,) B ) -cn-> RR ) ) $.
    intlewftc.10 $e |- ( ph -> D e. L^1 ) $.
    intlewftc.11 $e |- ( ph -> E e. L^1 ) $.
    intlewftc.12 $e |- ( ph -> D = ( x e. ( A (,) B ) |-> P ) ) $.
    intlewftc.13 $e |- ( ph -> E = ( x e. ( A (,) B ) |-> Q ) ) $.
    intlewftc.14 $e |- ( ( ph /\ x e. ( A (,) B ) ) -> P <_ Q ) $.
    intlewftc.15 $e |- ( ph -> ( F ` A ) <_ ( G ` A ) ) $.
    $( Inequality inference by invoking fundamental theorem of calculus.
       (Contributed by metakunt, 22-Jul-2024.) $)
    intlewftc $p |- ( ph -> ( F ` B ) <_ ( G ` B ) ) $=
      ( vt cfv cmin co caddc cle wbr cicc cr ccncf wcel wf cncff syl leidd 3jca
      w3a wb elicc2 syl2anc mpbird ffvelcdmd resubcld cioo citg cibl cmpt mpbid
      eleq1d feq1d fvmptelcdm itgle cv itgmpt fveq1d adantr eqcomd itgeq2dv cdv
      wa wceq wss ax-resscn a1i fss ssidd cncfcdm eqeltrrd ftc2 breq12d le2addd
      cc eqtrd sselid npcand ) ADIUGZCIUGZUHUIZXBUJUIZDJUGZCJUGZUHUIZXFUJUIZUKU
      LXAXEUKULAXCXBXGXFAXAXBACDUMUIZUNDIAIXIUNUOUIZUPZXIUNIUQZNXIUNIURUSZADXIU
      PZDUNUPZCDUKULZDDUKULZVBZAXOXPXQLMADLUTVAACUNUPZXOXNXRVCKLCDDVDVEVFZVGZAX
      IUNCIXMACXIUPZXSCCUKULZXPVBZAXSYCXPKACKUTMVAAXSXOYBYDVCKLCDCVDVEVFZVGZVHY
      FAXEXFAXIUNDJAJXJUPZXIUNJUQZOXIUNJURUSZXTVGZAXIUNCJYIYEVGZVHYKABCDVIUIZFV
      JZBYLGVJZUKULXCXGUKULABYLFGAEVKUPBYLFVLZVKUPTAEYOVKUBVNVMAHVKUPBYLGVLZVKU
      PUAAHYPVKUCVNVMABYLFUNAYLUNEUQZYLUNYOUQAEYLUNUOUIZUPZYQRYLUNEURUSZAYLUNEY
      OUBVOVMVPZABYLGUNAYLUNHUQZYLUNYPUQAHYRUPZUUBSYLUNHURUSZAYLUNHYPUCVOVMVPZU
      DVQAYMXCYNXGUKAYMUFYLUFVRZYOUGZVJZXCABUFYLFUNUUAVSAUUHUFYLUUFEUGZVJZXCAUF
      YLUUGUUIAUUFYLUPZWEZUUIUUGAUUIUUGWFUUKAUUFEYOUBVTWAWBWCAUUJUFYLUUFUNIWDUI
      ZUGZVJXCAUFYLUUIUUNUULUUFEUUMAEUUMWFUUKPWAVTWCAUFCDIKLMAEYLWQUOUIZUPZUUMU
      UOUPAUUPYLWQEUQZAYQUNWQWGZUUQYTUURAWHWIZYLUNWQEWJVEAWQWQWGZYSUUPUUQVCAWQW
      KZRYLUNWQEWLVEVFAEUUMUUOPVNVMAEUUMVKPTWMAIXIWQUOUIZUPZXIWQIUQZAXLUURUVDXM
      UUSXIUNWQIWJVEAUUTXKUVCUVDVCUVANXIUNWQIWLVEVFWNWRWRWRAYNUFYLUUFHUGZVJZXGA
      YNUFYLUUFYPUGZVJUVFABUFYLGUNUUEVSAUFYLUVGUVEUULUUFYPHUULHYPAHYPWFUUKUCWAW
      BVTWCWRAUVFUFYLUUFUNJWDUIZUGZVJXGAUFYLUVEUVIUULUUFHUVHAHUVHWFUUKQWAVTWCAU
      FCDJKLMAHUUOUPZUVHUUOUPZAUVJUVKAUVJUVKAUVJYLWQHUQZAUUBUURUVLUUDUUSYLUNWQH
      WJVEAUUTUUCUVJUVLVCUVASYLUNWQHWLVEVFAHUVHUUOQVNZVMUVMVFUVMVMAHUVHVKQUAWMA
      JUVBUPZXIWQJUQZAYHUURUVOYIUUSXIUNWQJWJVEAUUTYGUVNUVOVCUVAOXIUNWQJWLVEVFWN
      WRWRWOVMUEWPAXDXAXHXEUKAXAXBAUNWQXAWHYAWSAUNWQXBWHYFWSWTAXEXFAUNWQXEWHYJW
      SAUNWQXFWHYKWSWTWOVM $.
  $}

  ${
    aks4d1lem1.1 $e |- ( ph -> N e. ( ZZ>= ` 3 ) ) $.
    aks4d1lem1.2 $e |- B = ( |^ ` ( ( 2 logb N ) ^ 5 ) ) $.
    $( Technical lemma to reduce proof size.  (Contributed by metakunt,
       14-Nov-2024.) $)
    aks4d1lem1 $p |- ( ph -> ( B e. NN /\ 9 < B ) ) $=
      ( cn wcel c9 clt wbr c2 co c5 cfv cc0 cr a1i c3 syl c1 clogb cceil cz 2re
      cexp wa 2pos cuz eluzelz zred 0red 3re 3pos cle eluzle ltletrd 1red ltned
      1lt2 necomd relogbcld cn0 5nn0 reexpcld ceilcld 9re 9pos 3lexlogpow5ineq4
      ceilge lttrd jca elnnz sylibr eleq1i wceq breqtrrd ) ABFGZHBIJAKCUALZMUEL
      ZUBNZFGZVQAVTUCGZOVTIJZUFWAAWBWCAVSAVRMAKCKPGAUDQOKIJAUGQACACRUHNGZCUCGDR
      CUISUJZAORCAUKZRPGAULQWEORIJAUMQAWDRCUNJDRCUOSZUPATKATKAUQTKIJAUSQURUTVAM
      VBGAVCQVDZVEZAOHVTWFHPGAVFQZAVTWIUJZOHIJAVGQAHVSVTWJWHWKACWEWGVHAVSPGVSVT
      UNJWHVSVISUPZVJVKVTVLVMBVTFEVNVMAHVTBIWLBVTVOAEQVPVK $.
  $}

  ${
    $d A k $.  $d N k $.  $d k ph $.
    aks4d1p1p1.1 $e |- ( ph -> A e. RR+ ) $.
    aks4d1p1p1.2 $e |- ( ph -> N e. NN ) $.
    $( Exponential law for finite products, special case.  (Contributed by
       metakunt, 22-Jul-2024.) $)
    aks4d1p1p1 $p |- ( ph -> prod_ k e. ( 1 ... N ) ( A ^c k ) =
     ( A ^c sum_ k e. ( 1 ... N ) k ) ) $=
      ( c1 co ccxp cprod cfv cmul ce csu wcel wa cc adantr adantl eqtrd cv clog
      cfz cc0 wne w3a wceq rpcnd elfzelz zcnd 3jca cxpef syl prodeq2dv cuz eqid
      rpne0d cn nnuz eleqtrdi eluzelcn logcld mulcld fprodefsum fzfid fsummulc1
      eqcomd fveq2d fsumcl cxpefd ) AGDUCHZBCUAZIHZCJVKVLBUBKZLHZMKZCJZBVKVLCNZ
      IHZAVKVMVPCAVLVKOZPZBQOZBUDUEZVLQOZUFVMVPUGWAWBWCWDAWBVTABEUHZRAWCVTABEUQ
      ZRVTWDAVTVLVLGDUIUJSZUKBVLULUMUNAVQVKVOCNZMKZVSAVOCGDGUOKZWJUPADURWJFUSUT
      AVLWJOZPZVLVNWKWDAGVLVASWLBAWBWKWERAWCWKWFRVBVCVDAWIVRVNLHZMKZVSAWHWMMAWM
      WHAVKVLVNCAGDVEZABWEWFVBWGVFVGVHAVSWNABVRWEWFAVKVLCWOWGVIVJVGTTT $.
  $}

  ${
    $d A x $.  $d A y $.  $d B x $.  $d B y $.  $d ph x $.  $d ph y $.
    dvrelog2.1 $e |- ( ph -> A e. RR ) $.
    dvrelog2.2 $e |- ( ph -> B e. RR ) $.
    dvrelog2.3 $e |- ( ph -> 0 < A ) $.
    dvrelog2.4 $e |- ( ph -> A <_ B ) $.
    dvrelog2.5 $e |- F = ( x e. ( A [,] B ) |-> ( log ` x ) ) $.
    dvrelog2.6 $e |- G = ( x e. ( A (,) B ) |-> ( 1 / x ) ) $.
    $( The derivative of the logarithm, ~ ftc2 version.  (Contributed by
       metakunt, 11-Aug-2024.) $)
    dvrelog2 $p |- ( ph -> ( RR _D F ) = G ) $=
      ( cr cdv co clog crp cc wcel cc0 vy cioo c1 cv cdiv cmpt cicc wceq oveq2d
      cfv a1i crn ctg ccnfld ctopn cpr reelprrecn rpssre ax-resscn sstri adantl
      wa sseli wne rpne0 logcld 1red redivcld cres csn cdif wf wf1o logf1o f1of
      ax-mp wss cin c0 wn disjsn mpbir disjdif2 ssdif eqsstrri feqresmpt eqcomd
      0nrp dvrelog eqtrd clt wbr cle w3a wb elicc2 syl2anc biimpa simp1d adantr
      0red simp2d ltletrd jca elrp sylibr ex ssrdv tgioo4 eqid iccntr dvmptres2
      cnt ) AMENOZBCDUBOZUCBUDZUEOZUFZFAXNMBCDUGOZXPPUJZUFZNOXRAEYAMNEYAUHAKUKU
      IABXTXQMUBULUMUJZUNUOUJZMQXOXSMMRUPSAUQUKAXPQSZVBXPYDXPRSAQRXPQMRURUSUTZV
      CVAYDXPTVDAXPVEZVAVFYDXQMSAYDUCXPYDVGQMXPURVCYFVHVAAMBQXTUFZNOMPQVIZNOZBQ
      XQUFZAYGYHMNAYHYGABRTVJZVKZPULZQPYLYMPVLZAYLYMPVMYNVNYLYMPVOVPUKQYLVQAQQY
      KVKZYLQYKVRVSUHZYOQUHYPTQSVTWHQTWAWBQYKWCVPQRVQYOYLVQYEQRYKWDVPWEUKWFWGUI
      YIYJUHABWIUKWJAUAXSQAUAUDZXSSZYQQSZAYRVBZYQMSZTYQWKWLZVBYSYTUUAUUBYTUUACY
      QWMWLZYQDWMWLZAYRUUAUUCUUDWNZACMSZDMSZYRUUEWOGHCDYQWPWQWRZWSZYTTCYQYTXAAU
      UFYRGWTUUIATCWKWLYRIWTYTUUAUUCUUDUUHXBXCXDYQXEXFXGXHXIYCXJAUUFUUGXSYBXMUJ
      UJXOUHGHCDXKWQXLWJAFXRFXRUHALUKWGWJ $.
  $}

  ${
    $d A x $.  $d A y $.  $d B x $.  $d B y $.  $d ph x $.  $d ph y $.
    dvrelog3.1 $e |- ( ph -> A e. RR* ) $.
    dvrelog3.2 $e |- ( ph -> B e. RR* ) $.
    dvrelog3.3 $e |- ( ph -> 0 <_ A ) $.
    dvrelog3.4 $e |- ( ph -> A <_ B ) $.
    dvrelog3.5 $e |- F = ( x e. ( A (,) B ) |-> ( log ` x ) ) $.
    dvrelog3.6 $e |- G = ( x e. ( A (,) B ) |-> ( 1 / x ) ) $.
    $( The derivative of the logarithm on an open interval.  (Contributed by
       metakunt, 11-Aug-2024.) $)
    dvrelog3 $p |- ( ph -> ( RR _D F ) = G ) $=
      ( cr cdv co clog a1i crp wcel cc0 vy cioo c1 cv cdiv cmpt cfv wceq oveq2d
      crn ctg ccnfld ctopn cc cpr reelprrecn wa rpcn adantl wne rpne0 1red rpre
      logcld redivcld cres csn cdif wf wf1o logf1o f1of ax-mp wss cin c0 disjsn
      wn mpbir disjdif2 rpssre ax-resscn sstri ssdif eqsstrri feqresmpt dvrelog
      0nrp eqcomd eqtrd clt wbr w3a cxr elioo2 syl2anc biimpa simp1d 0red rexrd
      wb adantr cle simp2d xrlelttrd jca elrp sylibr ssrdv tgioo4 eqid ctop cnt
      ex retop iooretop isopn3i dvmptres2 ) AMENOZBCDUBOZUCBUDZUEOZUFZFAXSMBXTY
      APUGZUFZNOYCAEYEMNEYEUHAKQUIABYDYBMUBUJUKUGZULUMUGZMRXTXTMMUNUOSAUPQAYARS
      ZUQZYAYHYAUNSAYAURUSYHYATUTAYAVAUSZVDYIUCYAYIVBYHYAMSAYAVCUSYJVEAMBRYDUFZ
      NOMPRVFZNOZBRYBUFZAYKYLMNAYLYKABUNTVGZVHZPUJZRPYPYQPVIZAYPYQPVJYRVKYPYQPV
      LVMQRYPVNARRYOVHZYPRYOVOVPUHZYSRUHYTTRSVRWHRTVQVSRYOVTVMRUNVNYSYPVNRMUNWA
      WBWCRUNYOWDVMWEQWFWIUIYMYNUHABWGQWJAUAXTRAUAUDZXTSZUUARSZAUUBUQZUUAMSZTUU
      AWKWLZUQUUCUUDUUEUUFUUDUUECUUAWKWLZUUADWKWLZAUUBUUEUUGUUHWMZACWNSZDWNSUUB
      UUIXAGHCDUUAWOWPWQZWRZUUDTCUUAUUDTUUDWSWTAUUJUUBGXBUUDUUAUULWTATCXCWLUUBI
      XBUUDUUEUUGUUHUUKXDXEXFUUAXGXHXNXIXJYGXKAYFXLSZXTYFSZXTYFXMUGUGXTUHUUMAXO
      QUUNACDXPQXTYFXQWPXRWJAFYCFYCUHALQWIWJ $.
  $}

  ${
    $d A x $.  $d B x $.  $d ph x $.
    dvrelog2b.1 $e |- ( ph -> A e. RR* ) $.
    dvrelog2b.2 $e |- ( ph -> B e. RR* ) $.
    dvrelog2b.3 $e |- ( ph -> 0 <_ A ) $.
    dvrelog2b.4 $e |- ( ph -> A <_ B ) $.
    dvrelog2b.5 $e |- F = ( x e. ( A (,) B ) |-> ( 2 logb x ) ) $.
    dvrelog2b.6 $e |- G = ( x e. ( A (,) B ) |->
     ( 1 / ( x x. ( log ` 2 ) ) ) ) $.
    $( Derivative of the binary logarithm.  (Contributed by metakunt,
       11-Aug-2024.) $)
    dvrelog2b $p |- ( ph -> ( RR _D F ) = G ) $=
      ( cr co c2 a1i wcel cc0 c1 wn cdv cioo cv clog cdiv cmpt clogb wceq wa cc
      cfv cpr cdif csn 2cnd wne 2ne0 1red clt 1lt2 necomd nelprd eldifd elioore
      wbr ltned recn syl adantl elsni wo cle cxr 0xr xrlenlt syl2anc mpbid orcd
      wb ianor sylibr elioo5 syl3anc notbid mpbird pm2.01da adantr eleq1 mtbird
      a1d imp sylan2 con2d logbval mpteq2dva eqtrd oveq2d reelprrecn necon3bbid
      ex biidd pm5.74i sylib logcld redivcld eqid dvrelog3 0red crp 2rp loggt0b
      wi ax-mp mpbir dvmptdivc cmul recdiv2d eqcomd ) AMEUANMBCDUBNZBUCZUDUKZOU
      DUKZUENZUFZUANZFAEYDMUAAEBXSOXTUGNZUFZYDEYGUHAKPABXSYFYCAXTXSQZUIZOUJRSUL
      ZUMQXTUJRUNZUMQYFYCUHYIOUJYJYIUOZYIORSORUPZYIUQPZYISOYISOYIURZSOUSVEZYIUT
      PVFVAVBVCYIXTUJYKYHXTUJQZAYHXTMQZYQXTCDVDZXTVGVHVIZAYHXTYKQZTAUUAYHAUUAYH
      TZUUAAXTRUHZUUBXTRVJAUUCUIYHRXSQZAUUDTZUUCAUUDAUUDUUEAUUEUUDAUUECRUSVEZRD
      USVEZUIZTZAUUFTZUUGTZVKUUIAUUJUUKARCVLVEZUUJIARVMQZCVMQZUULUUJVSUUMAVNPZG
      RCVOVPVQVRUUFUUGVTWAAUUDUUHAUUNDVMQUUMUUDUUHVSGHUUOCDRWBWCWDWEWJWKWFWGUUC
      YHUUDVSAXTRXSWHVIWIZWLWTWMWKVCOXTWNVPWOWPWQAYEBXSSXTUENZYBUENZUFZFABYAUUQ
      YBMMXSMMUJULQAWRPYIXTYTAYHXTRUPZAYHUUCTZXLYHUUTXLAUUCYHAUUCUUBUUPWTWMYHUV
      AUUTYHUUCXTRYHUUCXAWSXBXCWKZXDYISXTYOYHYRAYSVIUVBXEABCDBXSYAUFZBXSUUQUFZG
      HIJUVCXFUVDXFXGAOAUOYMAUQPXDARYBARYBAXHRYBUSVEZAUVEYPUTOXIQUVEYPVSXJOXKXM
      XNPVFVAZXOAUUSBXSSXTYBXPNUENZUFZFABXSUURUVGYIXTYBYTYIOYLYNXDUVBAYBRUPYHUV
      FWGXQWOAFUVHFUVHUHALPXRWPWPWP $.
  $}

  ${
    0nonelaleb.1 $e |- ( ph -> A e. RR ) $.
    0nonelaleb.2 $e |- ( ph -> B e. RR ) $.
    0nonelaleb.3 $e |- ( ph -> 0 < A ) $.
    0nonelaleb.4 $e |- ( ph -> A <_ B ) $.
    0nonelalab.5 $e |- ( ph -> C e. ( A (,) B ) ) $.
    $( Technical lemma for open interval.  (Contributed by metakunt,
       12-Aug-2024.) $)
    0nonelalab $p |- ( ph -> 0 =/= C ) $=
      ( cc0 0red cioo co wcel cr elioore clt wbr cxr rexrd syl w3a elioo2 mpbid
      wb syl2anc simp2d lttrd ltned ) AJDAKZAJBDUJEADBCLMNZDONZIDBCPUAGAULBDQRZ
      DCQRZAUKULUMUNUBZIABSNCSNUKUOUEABETACFTBCDUCUFUDUGUHUI $.
  $}

  ${
    $d A x $.  $d B x $.  $d N x y $.  $d ph x y $.
    dvrelogpow2b.1 $e |- ( ph -> A e. RR ) $.
    dvrelogpow2b.2 $e |- ( ph -> B e. RR ) $.
    dvrelogpow2b.3 $e |- ( ph -> 0 < A ) $.
    dvrelogpow2b.4 $e |- ( ph -> A <_ B ) $.
    dvrelogpow2b.5 $e |- F = ( x e. ( A (,) B ) |-> ( ( 2 logb x ) ^ N ) ) $.
    dvrelogpow2b.6 $e |- G = ( x e. ( A (,) B ) |->
     ( C x. ( ( ( log ` x ) ^ ( N - 1 ) ) / x ) ) ) $.
    dvrelogpow2b.7 $e |- C = ( N / ( ( log ` 2 ) ^ N ) ) $.
    dvrelogpow2b.8 $e |- ( ph -> N e. NN ) $.
    $( Derivative of the power of the binary logarithm.  (Contributed by
       metakunt, 12-Aug-2024.) $)
    dvrelogpow2b $p |- ( ph -> ( RR _D F ) = G ) $=
      ( co c2 cmul wcel vy cr cdv cioo cv clogb cexp cmpt wceq oveq2d cmin clog
      a1i c1 cfv cdiv cc cpr reelprrecn cnelprrecn wa elioore adantl cc0 adantr
      recnd clt wbr cle 0nonelalab necomd logcld 2cnd wne 0ne2 0red 1lt2 crp wb
      simpr 2rp loggt0b ax-mp sylibr ltned divcld cdif 1red nelprd eldifd necom
      csn wi imbi2i neneqd velsn sylnibr logbval syl2anc eleq1d mpbird relogcld
      mpbi remulcld rpne0d mulne0d redivcld cn0 nnnn0d expcld nncnd nnm1nn0 syl
      cn mulcld rexrd ltled eqid dvrelog2b dvexp oveq1 dvmptco cz nn0zd expclzd
      oveq1d expne0d divmuldivd mulcomd caddc 1cnd pncan3d eqcomd expaddd eqtrd
      1nn0 exp1d mulassd 1zzd zsubcld divdiv1d divassd expdivd mpteq2dva
      divrecd ) AUBFUCQUBBCDUDQZRBUEZUFQZHUGQZUHZUCQZGAFUUJUBUCFUUJUIAMUMUJAUUK
      BUUFHUUHHUNUKQZUGQZSQZUNUUGRULUOZSQZUPQZSQZUHZGABUAUUHUUQUAUEZHUGQZHUUTUU
      LUGQZSQZUBUQUUIUUNUBUQUUFUQUBUBUQURZTAUSUMUQUVDTAUTUMAUUGUUFTZVAZUUHUQTUU
      GULUOZUUOUPQZUQTUVFUVGUUOUVFUUGUVFUUGUVEUUGUBTAUUGCDVBVCZVFZUVFVDUUGUVFCD
      UUGACUBTUVEIVEADUBTUVEJVEAVDCVGVHUVEKVEACDVIVHUVELVEAUVEVTVJZVKZVLZUVFRUV
      FVMZUVFVDRVDRVNUVFVOUMVKZVLZUVFVDUUOUVFVDUUOUVFVPUVFUNRVGVHZVDUUOVGVHZUVQ
      UVFVQUMZRVRTZUVRUVQVSWARWBWCWDWEVKZWFUVFUUHUVHUQUVFRUQVDUNURZWGTUUGUQVDWL
      ZWGTUUHUVHUIUVFRUQUWBUVNUVFRVDUNUVOUVFUNRUVFUNRUVFWHZUVSWEVKWIWJUVFUUGUQU
      WCUVJUVFUUGVDUIUUGUWCTUVFUUGVDUVFVDUUGVNZWMUVFUUGVDVNZWMUVKUWEUWFUVFVDUUG
      WKWNXCWOBVDWPWQWJRUUGWRWSZWTXAZUVFUNUUPUWDUVFUUGUUOUVIUVFRUVTUVFWAUMZXBXD
      UVFUUGUUOUVJUVFRUVNUVFRUWIXEVLUVLUWAXFZXGAUUTUQTZVAZUUTHAUWKVTZAHXHTUWKAH
      PXIZVEXJUWLHUVBAHUQTZUWKAHPXKZVEUWLUUTUULUWMAUULXHTZUWKAHXNTZUWQPHXLXMZVE
      XJXOABCDBUUFUUHUHZBUUFUUQUHZACIXPADJXPAVDCAVPIKXQLUWTXRUXAXRXSAUWRUQUAUQU
      VAUHUCQUAUQUVCUHUIPUAHXTXMUUTUUHHUGYAUUTUUHUIUVBUUMHSUUTUUHUULUGYAUJYBAGU
      USAGBUUFEUVGUULUGQZUUGUPQZSQZUHZUUSGUXEUIANUMABUUFUXDUURUVFUXDUUNUUPUPQZU
      URUVFUXDHUVHUULUGQZSQZUUPUPQZUXFUVFUXDHUXBUUOUULUGQZUPQZSQZUUPUPQZUXIUVFU
      XDHUXBSQZUXJUPQZUUPUPQZUXMUVFUXDUXNUXJUUPSQZUPQZUXPUVFUXDHUUOHUGQZUPQZUXC
      SQZUXRUVFEUXTUXCSEUXTUIUVFOUMYFUVFUYAUXNUXSUUGSQZUPQUXRUVFHUXSUXBUUGAUWOU
      VEUWPVEZUVFUUOHUVPUWAAHYCTUVEAHUWNYDVEZYEZUVFUVGUULUVMAUWQUVEUWSVEZXJZUVJ
      UVFUUOHUVPUWAUYDYGUVLYHUVFUYBUXQUXNUPUVFUYBUUPUXJSQZUXQUVFUYBUUGUUOUXJSQZ
      SQZUYHUVFUYBUUGUXSSQUYJUVFUXSUUGUYEUVJYIUVFUXSUYIUUGSUVFUXSUUOUNUGQZUXJSQ
      ZUYIUVFUXSUUOUNUULYJQZUGQUYLUVFHUYMUUOUGAHUYMUIUVEAUYMHAUNHAYKUWPYLYMVEUJ
      UVFUUOUNUULUVPUYFUNXHTUVFYPUMYNYOUVFUYKUUOUXJSUVFUUOUVPYQYFYOUJYOUVFUYHUY
      JUVFUUGUUOUXJUVJUVPUVFUUOUULUVPUYFXJZYRYMYOUVFUUPUXJUVFUUGUUOUVJUVPXOZUYN
      YIYOUJYOYOUVFUXPUXRUVFUXNUXJUUPUVFHUXBUYCUYGXOUYNUYOUVFUUOUULUVPUWAUVFHUN
      UYDUVFYSYTYGZUWJUUAYMYOUVFUXOUXLUUPUPUVFHUXBUXJUYCUYGUYNUYPUUBYFYOUVFUXLU
      XHUUPUPUVFUXKUXGHSUVFUXGUXKUVFUVGUUOUULUVMUVPUWAUYFUUCYMUJYFYOUVFUXFUXIUV
      FUUNUXHUUPUPUVFUUMUXGHSUVFUUHUVHUULUGUWGYFUJYFYMYOUVFUUNUUPUVFHUUMUYCUVFU
      UHUULUWHUYFXJXOUYOUWJUUEYOUUDYOYMYOYO $.
  $}

  ${
    aks4d1p1p3.1 $e |- ( ph -> N e. NN ) $.
    aks4d1p1p3.2 $e |- B = ( |^ ` ( ( 2 logb N ) ^ 5 ) ) $.
    aks4d1p1p3.3 $e |- ( ph -> 3 <_ N ) $.
    $( Bound of a ceiling of the binary logarithm to the fifth power.
       (Contributed by metakunt, 19-Aug-2024.) $)
    aks4d1p1p3 $p |- ( ph -> ( N ^c ( |_ ` ( 2 logb B ) ) ) <
    ( N ^c ( 2 logb ( ( ( 2 logb N ) ^ 5 ) + 1 ) ) ) ) $=
      ( c2 clogb co cfv c5 c1 clt wbr cr wcel a1i cc0 syl c7 cfl cexp caddc 2re
      ccxp 2pos cceil cz nnred nngt0d 1red 1lt2 ltned necomd relogbcld cn0 5nn0
      reexpcld ceilcl zred wceq eleq1d mpbird 0red 7pos 3lexlogpow5ineq3 ceilge
      7re ltletrd eqcomd breqtrd lttrd flcld readdcld ltp1d flle cmin ltsubaddd
      cle ceilm1lt mpbid eqbrtrd cuz crp wb 2z uzidd logblt syl3anc lelttrd 3re
      elrpd c3 1lt3 cxpltd ) AGBHIZUAJZGGCHIZKUBIZLUCIZHIZMNCWQUEICXAUEIMNAWQWP
      XAAWQAWPAGBGOPAUDQZRGMNAUFQZABOPWSUGJZOPAXDAWSOPZXDUHPAWRKAGCXBXCACDUIZAC
      DUJALGALGAUKZLGMNAULQUMUNZUOKUPPAUQQURZWSUSSUTZABXDOBXDVAAEQZVBVCZARTBAVD
      ZTOPAVHQZXLRTMNAVEQZATXDBMATWSXDXNXIXJACXFFVFZAXEWSXDVSNXIWSVGSVIABXDXKVJ
      VKVLZXHUOZVMUTZXRAGWTXBXCAWSLXIXGVNZARTWTXMXNXTXOATWSWTXNXIXTXPAWSXIVOVLV
      LZXHUOZAWPOPWQWPVSNXRWPVPSABWTMNZWPXAMNZABXDWTMXKAXDLVQIWSMNZXDWTMNAXEYEX
      IWSVTSAXDLWSXJXGXIVRWAWBAGGWCJPBWDPWTWDPYCYDWEAGGUHPAWFQWGABXLXQWLAWTXTYA
      WLGBWTWHWIWAWJACWQXAXFALWMCXGWMOPAWKQXFLWMMNAWNQFVIXSYBWOWA $.
  $}

  ${
    $d N k $.  $d k ph $.
    aks4d1p1p2.1 $e |- ( ph -> N e. NN ) $.
    aks4d1p1p2.2 $e |- A = ( ( N ^ ( |_ ` ( 2 logb B ) ) ) x. prod_ k e.
     ( 1 ... ( |_ ` ( ( 2 logb N ) ^ 2 ) ) ) ( ( N ^ k ) - 1 ) ) $.
    aks4d1p1p2.3 $e |- B = ( |^ ` ( ( 2 logb N ) ^ 5 ) ) $.
    aks4d1p1p2.4 $e |- ( ph -> 3 <_ N ) $.
    $( Rewrite ` A ` in more suitable form.  (Contributed by metakunt,
       19-Aug-2024.) $)
    aks4d1p1p2 $p |- ( ph -> A < ( N ^c ( ( ( 2 logb
           ( ( ( 2 logb N ) ^ 5 ) + 1 ) )
         +
         ( ( ( 2 logb N ) ^ 2 ) / 2 ) )
       +
       ( ( ( 2 logb N ) ^ 4 ) / 2 ) ) ) ) $=
      ( c2 co c1 caddc clt cr wcel cc0 cle wbr a1i clogb cexp cdiv ccxp cfl cfv
      c5 c4 cfz cv cmin cprod cmul nnred cz cn0 2re 2pos cceil nngt0d 1red 1lt2
      wa necomd relogbcld 5nn0 reexpcld ceilcl syl zred wceq eleq1d mpbird 0red
      ltned nn0zd c3 3re 1lt3 ltletrd crp wb 2rp pm3.2i logbgt0b syl2anc expgt0
      elrpd syl3anc ceilge breq2d flcld c7 7re 3lexlogpow5ineq3 lttrd ltled 0zd
      1lt7 mpbid jca elnn0z sylibr fzfid adantr cn elfznn adantl nnnn0 resubcld
      flge fprodrecl remulcld nnnn0d nn0ge0d readdcld ltp1d csu 0lt1 2nn0 leidd
      resqcld cc wne recnd gtned logbid1 eqcomd breqtrd expge1d 1exp eqtrd 1nn0
      oveq1d letrd recxpcld reflcl cxpexp oveq2d divcld 2p1e3 logblebd 1z zsqcl
      nn0addge1i breqtri eqbrtrd ax-mp elnnz bicomi fsumrecl eqeltrrd rehalfcld
      arisum 4nn0 rpcxpcld aks4d1p1p1 rpregt0d simpld expge0d nfv nnge1d lesubd
      subid1d fprodle lemul2ad breq1d prodeq2dv 3jca aks4d1p1p3 ltmul1a lelttrd
      lem1d w3a nncnd sqcld addcld halfcld cxpaddd flle leexp1ad expmuld oveq2i
      id 2t2e4 eqled le2addd lediv1dd leadd2dd cxpled divdird addcomd addassd )
      ABEJJEUAKZUGUBKZLMKZUAKZUWNUHUBKZJUCKZUWNJUBKZJUCKZMKZMKZUDKZEUWQUXAMKUWS
      MKZUDKNABEUWQUWRUWTMKZJUCKZMKZUDKZUXDNABEUWQUWTUEUFZJUBKZUXJMKZJUCKZMKZUD
      KZUXIABOPEJCUAKZUEUFZUBKZLUXJUIKZEDUJZUBKZLUKKZDULZUMKZOPAUXRUYCAEUXQAEFU
      NZAUXQUOPZQUXQRSZVCUXQUPPZAUYFUYGAUXPAJCJOPAUQTZQJNSAURTZACOPUWOUSUFZOPAU
      YKAUWOOPZUYKUOPAUWNUGAJEUYIUYJUYEAEFUTZALJALJAVAZLJNSZAVBTVOVDZVEZUGUPPAV
      FTZVGZUWOVHVIVJZACUYKOCUYKVKAHTZVLVMZAQCNSQUYKNSAQUWOUYKAVNZUYSUYTAUWNOPU
      GUOPQUWNNSZQUWONSUYQAUGUYRVPAVUDLENSZALVQEUYNVQOPAVRTZUYELVQNSAVSTIVTZAEW
      APJWAPZUYOVCZVUDVUEWBAEUYEUYMWHZVUIAVUHUYOWCVBWDTZEJWEWFVMUWNUGWGWIZAUYLU
      WOUYKRSUYSUWOWJVIZVTACUYKQNVUAWKVMZUYPVEZWLAQUXPRSZUYGAQUXPVUCVUOAQUXPNSZ
      LCNSZAVURLUYKNSALUWOUYKUYNUYSUYTALWMUWOUYNWMOPAWNTUYSLWMNSAWSTAEUYEIWOWPV
      UMVTACUYKLNVUAWKVMACWAPVUIVUQVURWBACVUBVUNWHVUKCJWEWFVMWQAUXPOPZQUOPVUPUY
      GWBVUOAWRUXPQXKWFWTXAUXQXBXCZVGZAUXSUYBDALUXJXDZAUXTUXSPZVCZUYALVVDEUXTAE
      OPVVCUYEXEZVVDUXTXFPZUXTUPPZVVCVVFAUXTUXJXGXHZUXTXIVIZVGZVVDVAZXJZXLZXMAB
      UYDOBUYDVKAGTZVLVMZAEUXNUYEAEAEFXNXOZAUWQUXMAJUWPUYIUYJAUWOLUYSUYNXPZAQUW
      OUWPVUCUYSVVQVULAUWOUYSXQWPUYPVEZAUXSUXTDXRZUXMOAUXJUPPVVSUXMVKAUXJAUXJUO
      PZQUXJNSZVCZUXJXFPZAVVTVWAAUWTAUWNUYQYBZWLZAQLUXJVUCUYNAUXJVWEVJZQLNSAXST
      ALJJUAKZJUBKZUXJUYNAVWGAJJUYIUYJUYIUYJUYPVEZYBVWFAVWGJVWIJUPPAXTTZALLVWGR
      ALUYNYAAVWGLAJYCPJQYDJLYDVWGLVKAJUYIYEZAQJVUCUYJYFZUYPJYGWIYHZYIZYJAVWHUW
      TRSZVWHUXJRSZAVWHLUWTRAVWHLJUBKZLAVWGLJUBALVWGVWMYHYNZAJUOPVWQLVKAJVWJVPZ
      JYKVIYLAUWNJUYQVWJALVWGUWNUYNVWIUYQVWNAJJEVWSAJUYIYAUYIUYJUYEUYMAJVQEUYIV
      UFUYEJVQRSAJJLMKVQRJLUQYMUUEUUAUUFTIYOUUBYOYJUUGAUWTOPZVWHUOPZVCVWOVWPWBA
      VWTVXAVWDAVXAVWQUOPZVXBALUOPVXBUUCLUUDUUHTAVWHVWQUOVWRVLVMXAUWTVWHXKVIWTY
      OVTXAVWBVWCWBAVWCVWBUXJUUIUUJTWTZXNZDUXJUUNVIZAUXSUXTDVVBVVDUXTVVHUNUUKZU
      ULZXPZYPAEUXHUYEVVPAUWQUXGVVRAUXFAUWRUWTAUWNUHUYQUHUPPAUUOTVGZVWDXPZUUMZX
      PZYPABEUWQUDKZEUXMUDKZUMKZUXONABVXMEVVSUDKZUMKZVXONABVXMUXSEUXTUDKZDULZUM
      KZVXQNABEUXQUDKZVXSUMKZVXTVVOAVYAVXSAEUXQUYEVVPAVUSUXQOPVUOUXPYQVIYPZAVXS
      OPZQVXSNSZAVXSAVXSWAPVXPWAPAEVVSVUJVXFUUPAVXSVXPWAAEDUXJVUJVXCUUQZVLVMUUR
      ZUUSZXMAVXMVXSAEUWQUYEVVPVVRYPZVYHXMABUXRVXSUMKZVYBRABUXRUXSUYADULZUMKZVY
      JRABVYLRSUYDVYLRSAUYCVYKUXRVVMAUXSUYADVVBVVJXLVVAAEUXQUYEVUTVVPUUTAUXSUYB
      UYADADUVAVVBVVLVVDLUYAQVVKVVJVVDVNVVDLUYAQUKKZRSLUYARSVVDEUXTVVEVVIALERSV
      VCAEFUVBXEYJVVDVYMUYALRVVDUYAVVDUYAVVJYEUVDWKVMUVCVVJVVDUYAVVJUVMUVEUVFAB
      UYDVYLRVVNUVGVMAVYKVXSUXRUMAUXSUYAVXRDVVDVXRUYAVVDEYCPZVVGVXRUYAVKVVDEVVE
      YEVVIEUXTYRWFYHUVHYSYIAVYBVYJAVYAUXRVXSUMAVYNUYHVYAUXRVKAEUYEYEZVUTEUXQYR
      WFYNYHYIAVYAOPZVXMOPZVYDVYEVCZUVNVYAVXMNSVYBVXTNSAVYPVYQVYRVYCVYIVYGUVIAC
      EFHIUVJVYAVXMVXSUVKWFUVLAVXSVXPVXMUMVYFYSYIAVXPVXNVXMUMAVVSUXMEUDVXEYSYSY
      IAUXOVXOAEUWQUXMVYOAQEVUCUYMYFAUWQVVRYEZAUXLAUXKUXJAUXJAUXJVXCUVOZUVPVYTU
      VQUVRUVSYHYIAUXNUXHRSUXOUXIRSAUXMUXGUWQVXGVXKVVRAUXLUXFJAUXKUXJAUXJAVWTUX
      JOPVWDUWTYQVIZYBZWUAXPVXJVUHAWCTAUXKUXJUWRUWTWUBWUAVXIVWDAUXKUWTJUBKZUWRW
      UBAUWTJVWDVWJVGZVXIAAUXKWUCRSAUWDAUXJUWTJWUAVWDVWJAUXJVXDXOAVWTUXJUWTRSVW
      DUWTUVTVIZUWAVIAWUCUWRWUDAWUCUWNJJUMKZUBKZUWRAWUGWUCAUWNJJAUWNUYQYEVWJVWJ
      UWBYHWUGUWRVKAWUFUHUWNUBUWEUWCTYLUWFYOWUEUWGUWHUWIAEUXNUXHUYEVUGVXHVXLUWJ
      WTVTAUXHUXCEUDAUXGUXBUWQMAUWRUWTJAUWRVXIYEZAUWTVWDYEZVWKVWLUWKYSYSYIAUXCU
      XEEUDAUXCUWQUXAUWSMKZMKZUXEAUXBWUJUWQMAUWSUXAAUWRJWUHVWKVWLYTZAUWTJWUIVWK
      VWLYTZUWLYSAUXEWUKAUWQUXAUWSVYSWUMWULUWMYHYLYSYI $.
  $}

  ${
    $d N k $.  $d k ph $.
    aks4d1p1p4.1 $e |- ( ph -> N e. NN ) $.
    aks4d1p1p4.2 $e |- A = ( ( N ^ ( |_ ` ( 2 logb B ) ) ) x. prod_ k e.
     ( 1 ... ( |_ ` ( ( 2 logb N ) ^ 2 ) ) ) ( ( N ^ k ) - 1 ) ) $.
    aks4d1p1p4.3 $e |- B = ( |^ ` ( ( 2 logb N ) ^ 5 ) ) $.
    aks4d1p1p4.4 $e |- ( ph -> 3 <_ N ) $.
    aks4d1p1p4.5 $e |- C = ( 2 logb ( ( ( 2 logb N ) ^ 5 ) + 1 ) ) $.
    aks4d1p1p4.6 $e |- D = ( ( 2 logb N ) ^ 2 ) $.
    aks4d1p1p4.7 $e |- E = ( ( 2 logb N ) ^ 4 ) $.
    aks4d1p1p4.8 $e |- ( ph -> ( ( 2 x. C ) + D ) <_ E ) $.
    $( Technical step for inequality.  The hard work is in to prove the final
       hypothesis.  (Contributed by metakunt, 19-Aug-2024.) $)
    aks4d1p1p4 $p |- ( ph -> A < ( 2 ^ B ) ) $=
      ( c2 co wcel c1 clogb c5 cexp ccxp cr cfl cfv cv cmin cprod cmul nnred cz
      cfz cc0 cle wbr wa cn0 2re a1i clt 2pos cceil nngt0d 1red ltned relogbcld
      1lt2 necomd 5nn0 reexpcld ceilcl syl zred wceq eleq1d mpbird c7 0red 7pos
      3lexlogpow5ineq3 ltled ceilge breqtrrd letrd ltletrd flcld caddc readdcld
      7re leidd 1cnd addlidd wne recnd gtned logbid1 syl3anc eqcomd breq12d 5re
      cc nn0addge1i recni 5cn addcomi 5p2e7 eqtri eqbrtrd cuz wb 2z uzidd elrpd
      crp 2rp logbleb mpbid fllep1 leadd1d jca elnn0z sylibr adantr cn remulcld
      fzfid c4 oveq2d cdif eldifd wi syl2anc oveq1d eqtrd eqeltrd cdiv breqtrd
      c3 elfznn adantl nnnn0d resubcld fprodrecl cpr rpne0d nelprd necom imbi2i
      2cnd mpbi neneqd c0ex elsn2 sylnibr cxplogb eqidd 4nn0 cxpmuld exp1d 1nn0
      csn expaddd 4cn ax-1cn 4p1e5 addcomli 3re 0le1 1lt3 recxpcld eqeltrrd w3a
      nn0zd logb1 1rp logblt lelttrd 3jca ltp1 lttrd resqcld rehalfcld redivcld
      expgt0 rpcxpcld rpred aks4d1p1p2 divcan3d divdird lediv1d leadd1dd cxpled
      2halvesd 1le2 nn0red cxplead cxpexp ) ABQQHUARZUBUCRZUDRZQCUCRZABUESHQCUA
      RZUFUGZUCRZTUWTQUCRZUFUGZUNRZHFUHZUCRZTUIRZFUJZUKRZUESAUXFUXMAHUXEAHIULZA
      UXEUMSZUOUXEUPUQZURUXEUSSAUXPUXQAUXDAQCQUESAUTVAZUOQVBUQAVCVAZACUESUXAVDU
      GZUESAUXTAUXAUESZUXTUMSZAUWTUBAQHUXRUXSUXOAHIVEZATQATQAVFZTQVBUQAVIVAVGVJ
      ZVHZUBUSSAVKVAZVLZUXAVMVNZVOACUXTUECUXTVPAKVAZVQVRZAUOVSCAVTZVSUESAWKVAZU
      YKUOVSVBUQAWAVAAVSUXACUYMUYHUYKAVSUXAUYMUYHAHUXOLWBWCAUXAUXTCUPAUYAUXAUXT
      UPUQUYHUXAWDVNZUYJWEWFZWGZUYEVHZWHZAUXQUOTWIRZUXETWIRZUPUQAUYSUXDUYTAUOTU
      YLUYDWJZUYQAUXETAUXEUYRVOZUYDWJAUYSQQUARZUXDVUAAQQUXRUXSUXRUXSUYEVHUYQAUY
      SVUCUPUQTTUPUQATUYDWLAUYSTVUCTUPATAWMWNATVUCAVUCTAQXCSZQUOWOZQTWOZVUCTVPA
      QUXRWPZAUOQUYLUXSWQZUYEQWRWSWTWTXAVRAQCUPUQZVUCUXDUPUQZAQVSCUXRUYMUYKAQQU
      BWIRZVSUXRAQUBUXRUBUESAXBVAWJUYMQVUKUPUQAQUBUTVKXDVAAVUKVSVSUPVUKVSVPAVUK
      UBQWIRVSQUBQUTXEXFXGXHXIVAAVSUYMWLXJWFUYOWFAQQXKUGSZQXPSZCXPSVUIVUJXLAQQU
      MSAXMVAXNZVUMAXQVAZACUYKUYPXOQQCXRWSXSWFAUXDUESUXDUYTUPUQUYQUXDXTVNWFAUOU
      XETUYLVUBUYDYAVRYBUXEYCYDVLAUXIUXLFATUXHYHAUXJUXISZURZUXKTVUQHUXJAHUESVUP
      UXOYEVUQUXJVUPUXJYFSAUXJUXHUUAUUBUUCVLVUQVFUUDUUEYGABUXNUEBUXNVPAJVAVQVRZ
      AHGUDRZUXBUEAVUSQUWTTYIWIRZUCRZUDRZUXBAVUSQUWTUWTYIUCRZUKRZUDRZVVBAVUSQUW
      TUDRZVVCUDRZVVEAVUSHVVCUDRZVVGAGVVCHUDGVVCVPAOVAZYJAVVHVVGVVGAHVVFVVCUDAV
      VFHAQXCUOTUUFZYKSHXCUOUVCZYKSVVFHVPAQXCVVJAUUKZAQUOTAQVUOUUGZUYEUUHYLAHXC
      VVKAHUXOWPAHUOVPHVVKSAHUOAUOHWOZYMAHUOWOZYMAUOHUYLUYCVGVVNVVOAUOHUUIUUJUU
      LUUMHUOUUNUUOUUPYLQHUUQYNWTYOAVVGUURYPYPAVVEVVGAQUWTVVCVUOUYFAVVCGXCAGVVC
      VVIWTZAGAGUESVVCUESAUWTYIUYFYIUSSAUUSVAZVLAGVVCUEVVIVQVRZWPZYQUUTWTYPAVVD
      VVAQUDAVVDUWTTUCRZVVCUKRZVVAAUWTVVTVVCUKAVVTUWTAUWTAUWTUYFWPZUVAWTYOAVVAV
      WAAUWTTYIVWBVVQTUSSAUVBVAUVDWTYPYJYPAVVAUXAQUDAVUTUBUWTUCVUTUBVPAYITUBUVE
      UVFUVGUVHVAYJYJYPZAHGUXOAUOYTHUYLYTUESAUVIVAZUXOAUOTYTUYLUYDVWDUOTUPUQAUV
      JVAATYTUYDVWDTYTVBUQAUVKVAZWCWFLWFVVRUVLZUVMAQCUXRACUMSZUOCUPUQZURCUSSZAV
      WGVWHAVWGUYBUYIACUXTUMUYJVQVRAUOCUYLUYKUYPWCYBCYCYDZVLABVUSUXBVBABHDEQYRR
      ZWIRZGQYRRZWIRZUDRZVUSVURAVWOAHVWNAHUXOUYCXOZAVWLVWMADVWKADUESQUXATWIRZUA
      RZUESAQVWQUXRUXSAUXATUYHUYDWJZAUOUXAVWQUYLUYHVWSAUWTUESZUBUMSZUOUWTVBUQZU
      VNUOUXAVBUQAVWTVXAVXBUYFAUBUYGUVOAUOQTUARZUWTUYLAVXCUOUEAVUDVUEVUFVXCUOVP
      VUGVUHUYEQUVPWSZUYLYQUYFAUOUOVXCUPAUOUYLWLAVXCUOVXDWTYSATHVBUQZVXCUWTVBUQ
      ZATYTHUYDVWDUXOVWELWGZAVULTXPSZHXPSVXEVXFXLVUNVXHAUVQVAVWPQTHUVRWSXSUVSUV
      TUWTUBUWFVNAUYAUXAVWQVBUQUYHUXAUWAVNUWBUYEVHADVWRUEDVWRVPAMVAZVQVRZAEAEUE
      SUXGUESAUWTUYFUWCAEUXGUEEUXGVPANVAZVQVRZUWDWJZAGQVVRUXRVVMUWEZWJZUWGUWHVW
      FABHVWRUXGQYRRZWIRZVVCQYRRZWIRZUDRVWOVBABCFHIJKLUWIAVXSVWNHUDAVXSVXQVWMWI
      RVWNAVXRVWMVXQWIAVVCGQYRVVPYOYJAVXQVWLVWMWIAVXQDVXPWIRVWLAVWRDVXPWIADVWRV
      XIWTYOAVXPVWKDWIAUXGEQYRAEUXGVXKWTYOYJYPYOYPYJYSAVWNGUPUQVWOVUSUPUQAVWNVW
      MVWMWIRGUPAVWLVWMVWMVXMVXNVXNAVWLQDUKRZEWIRZQYRRZVWMUPAVWLVXTQYRRZVWKWIRZ
      VYBADVYCVWKWIAVYCDADQADVXJWPVVLVVMUWJWTYOAVYBVYDAVXTEQAVXTAQDUXRVXJYGZWPA
      EVXLWPVUGVVMUWKWTYPAVYAGUPUQVYBVWMUPUQPAVYAGQAVXTEVYEVXLWJVVRVUOUWLXSXJUW
      MAGVVSUWOYSAHVWNGUXOVXGVXOVVRUWNXSWGVWCYSAUXBQCUDRZUXCUPAQUXACUXRTQUPUQAU
      WPVAUYHACVWJUWQAUXAUXTCUPUYNACUXTUYJWTYSUWRAVUDVWIVYFUXCVPVVLVWJQCUWSYNYS
      WG $.
  $}

  ${
    $d A x $.  $d B x $.  $d P x $.  $d Q x $.  $d R x $.  $d S x $.
    $d ph x $.
    dvle2.1 $e |- ( ph -> A e. RR ) $.
    dvle2.2 $e |- ( ph -> B e. RR ) $.
    dvle2.3 $e |- ( ph -> ( x e. ( A [,] B ) |-> E ) e. ( ( A [,] B )
    -cn-> RR ) ) $.
    dvle2.4 $e |- ( ph -> ( x e. ( A [,] B ) |-> G ) e. ( ( A [,] B )
    -cn-> RR ) ) $.
    dvle2.5 $e |- ( ph -> ( RR _D ( x e. ( A (,) B ) |-> E ) ) =
     ( x e. ( A (,) B ) |-> F ) ) $.
    dvle2.6 $e |- ( ph -> ( RR _D ( x e. ( A (,) B ) |-> G ) ) =
     ( x e. ( A (,) B ) |-> H ) ) $.
    dvle2.7 $e |- ( ( ph /\ x e. ( A (,) B ) ) -> F <_ H ) $.
    dvle2.8 $e |- ( x = A -> E = P ) $.
    dvle2.9 $e |- ( x = A -> G = Q ) $.
    dvle2.10 $e |- ( x = B -> E = R ) $.
    dvle2.11 $e |- ( x = B -> G = S ) $.
    dvle2.12 $e |- ( ph -> P <_ Q ) $.
    dvle2.13 $e |- ( ph -> A <_ B ) $.
    $( Collapsed ~ dvle .  (Contributed by metakunt, 19-Aug-2024.) $)
    dvle2 $p |- ( ph -> R <_ S ) $=
      ( cmin co caddc cle wbr cr wcel cicc cv wceq eleq1d cmpt wral ccncf cncff
      wf syl eqid fmpt sylibr cxr w3a rexrd leidd 3jca wb elicc1 syl2anc mpbird
      rspcdva resubcld dvle le2addd recnd npcand breq12d mpbid ) AGEUFUGZEUHUGZ
      HFUFUGZFUHUGZUIUJGHUIUJAWCEWEFAGEAIUKULZGUKULBCDUMUGZDBUNZDUOZIGUKUBUPAWH
      UKBWHIUQZVAZWGBWHURAWKWHUKUSUGZULWLOWHUKWKUTVBBWHUKIWKWKVCVDVEZADWHULZDVF
      ULZCDUIUJZDDUIUJZVGZAWPWQWRADNVHZUEADNVIVJACVFULZWPWOWSVKACMVHZWTCDDVLVMV
      NZVOZAWGEUKULBWHCWICUOZIEUKTUPWNACWHULZXACCUIUJZWQVGZAXAXGWQXBACMVIUEVJAX
      AWPXFXHVKXBWTCDCVLVMVNZVOZVPXJAHFAKUKULZHUKULBWHDWJKHUKUCUPAWHUKBWHKUQZVA
      ZXKBWHURAXLWMULXMPWHUKXLUTVBBWHUKKXLXLVCVDVEZXCVOZAXKFUKULBWHCXEKFUKUAUPX
      NXIVOZVPXPABIJKLEFGHCDCDMNOQPRSXIXCUETUAUBUCVQUDVRAWDGWFHUIAGEAGXDVSAEXJV
      SVTAHFAHXOVSAFXPVSVTWAWB $.
  $}

  ${
    $d A x $.  $d B x $.  $d ph x y $.  $d ph x z $.
    aks4d1p1p6.1 $e |- ( ph -> A e. RR ) $.
    aks4d1p1p6.2 $e |- ( ph -> B e. RR ) $.
    aks4d1p1p6.3 $e |- ( ph -> 3 <_ A ) $.
    aks4d1p1p6.4 $e |- ( ph -> A <_ B ) $.
    $( Inequality lift to differentiable functions for a term in AKS inequality
       lemma.  (Contributed by metakunt, 19-Aug-2024.) $)
    aks4d1p1p6 $p  |- ( ph
     -> ( RR
            _D
            ( x
            e. ( A (,) B )
            |-> ( ( 2
                    x.
                    ( 2
                      logb
                      ( ( ( 2 logb x ) ^ 5 ) + 1 ) ) )
                  +
                  ( ( 2 logb x ) ^ 2 ) ) ) )
        = ( x
          e. ( A (,) B )
          |-> ( ( 2
                  x.
                  ( ( 1
                      /
                      ( ( ( ( 2 logb x ) ^ 5 ) + 1 )
                        x.
                        ( log ` 2 ) ) )
                    x.
                    ( ( ( 5 x. ( ( 2 logb x ) ^ 4 ) )
                        x.
                        ( 1 / ( x x. ( log ` 2 ) ) ) )
                      +
                      0 ) ) )
                +
                ( ( 2 / ( ( log ` 2 ) ^ 2 ) )
                  x.
                  ( ( ( log ` x ) ^ ( 2 - 1 ) ) / x ) ) ) ) ) $=
      ( c2 co c5 c1 cmul cc0 cr cc wcel a1i clt wbr vy vz clogb cexp caddc clog
      cv cfv cdiv c4 cmin cioo cpr reelprrecn 2cnd 2re 2pos elioore adantl 0red
      wa adantr c3 3re 3pos cle ltletrd simpr cxr wb rexrd elioo5 syl3anc mpbid
      simpld lttrd 1red 1lt2 ltned necomd relogbcld cn0 reexpcld readdcld ltp1d
      5nn0 cz nn0zd wceq wtru wne logb1 mptru cuz crp 2z uzidd 1rp elrpd logblt
      2lt3 eqbrtrrid expgt0 ltadd1dd recn syl mulcld 2rp relogcld remulcld 1cnd
      recnd addcld gt0ne0d logcld loggt0b ax-mp mpbir mulne0d redivcld 5re 4nn0
      gtned rpre rpgt0 rpne0d rpne0 expcld cmpt eqid dvrelog2b cdv oveq2d oveq1
      cn dvmptco dvmptadd cpnf mpteq1d eqtrd cnelprrecn 5cn ltled 5nn mpteq2dva
      dvexp 5m1e4 eqtrid crn ctg ccnfld dvmptc ioossre tgioo4 iooretop dvmptres
      ctopn wss dfrp2 pnfxr leidd 0lepnf eqcomd oveq2 dvmptcmul resqcld expne0d
      sqcld 2m1e1 1nn0 eqeltri 2nn dvrelogpow2b ) ABIIIBUGZUCJZKUDJZLUEJZUCJZMJ
      ILUVQIUFUHZMJZUIJZKUVOUJUDJZMJZLUVNUVSMJZUIJZMJZNUEJZMJZMJUVOIUDJZIUVSIUD
      JZUIJZUVNUFUHZILUKJZUDJZUVNUIJZMJZOOOCDULJZOOPUMZQAUNRZAUVNUWQQZVAZIUVRUX
      AUOZUXAUVROQUVRPQUXAIUVQIOQZUXAUPRZNISTZUXAUQRZUXAUVPLUXAUVOKUXAIUVNUXDUX
      FUWTUVNOQZAUVNCDURUSZUXANCUVNUXAUTZACOQUWTEVBZUXHUXANVCCUXIVCOQZUXAVDRZUX
      JNVCSTZUXAVERAVCCVFTUWTGVBZVGUXACUVNSTZUVNDSTZUXAUWTUXOUXPVAZAUWTVHUXACVI
      QZDVIQZUVNVIQUWTUXQVJAUXRUWTACEVKZVBAUXSUWTADFVKZVBUXAUVNUXHVKCDUVNVLVMVN
      VOZVPZUXALIUXALIUXAVQZLISTZUXAVRRZVSVTZWAZKWBQZUXAWFRZWCZUYDWDZUXANNLUEJU
      VQUXIUXANLUXIUYDWDUYLUXANUXIWEUXANUVPLUXIUYKUYDUXAUVOOQKWGQNUVOSTNUVPSTUY
      HUXAKUYJWHUXANILUCJZUVOSUYMNWIZWJIPQINWKILWKUYNWJUOWJNIWJNIWJUTUXEWJUQRVS
      VTWJLIWJLIWJVQUYEWJVRRVSVTIWLVMWMUXALUVNSTZUYMUVOSTZUXALCUVNUYDUXJUXHUXAL
      VCCUYDUXLUXJUXALIVCUYDUXDUXLUYFIVCSTUXAXARVPUXNVGUYBVPUXAIIWNUHQLWOQZUVNW
      OQUYOUYPVJUXAIIWGQUXAWPRZWQUYQUXAWRRUXAUVNUXHUYCWSZILUVNWTVMVNXBUVOKXCVMX
      DVPZUYGWAUVRXEXFZXGUXAIUWHUXDUXAUWAUWGUXALUVTUYDUXAUVQUVSUYLUXAIIWOQZUXAX
      HRZXIZXJUXAUVQUVSUXAUVPLUXAUVPUYKXLZUXAXKZXMUXAIUXBUXAIUXFXNXOZUXAUVQUYTX
      NAUVSNWKUWTANUVSANUVSAUTZNUVSSTZAVUIUYEVRVUBVUIUYEVJXHIXPXQXRRVSVTZVBZXSX
      TUXAUWFNUXAUWCUWEUXAKUWBKOQUXAYARUXAUVOUJUYHUJWBQZUXAYBRWCXJUXALUWDUYDUXA
      UVNUVSUXHVUDXJUXAUVNUVSUXAUVNUXHXLVUGUXANUVNUXIUYCYCVUKXSXTZXJZUXIWDZXJZX
      JABUVRUWHIOOUWQUWSVUAVUPABUAUVQUWGIUAUGZUCJZLVUQUVSMJZUIJZOOUVRUWAOOUWQWO
      UWSUWSUXAUVQUYLUYTWSVUOAVUQWOQZVAZVURVVBIVUQUXCVVBUPRUXEVVBUQRVVAVUQOQAVU
      QYDUSZVVANVUQSTAVUQYEUSVVBLIVVBLIVVBVQZUYEVVBVRRVSVTWAXLVVBLVUSVVDVVBVUQU
      VSVVCVVBIVUBVVBXHRZXIXJVVBVUQUVSVVBVUQVVCXLVVBIVVBUOVVBIVVEYFXOVVAVUQNWKA
      VUQYGUSVVBNUVSANUVSWKVVAAUVSNVUJVTVBVTXSXTABUVPUWFLNOOOUWQUWSVUEVUNABUBUV
      OUWEUBUGZKUDJZKVVFUJUDJZMJZOPUVPUWCOPUWQPUWSPUWRQAUUARUXAUVOUYHXLZVUMAVVF
      PQZVAZVVFKAVVKVHZUYIVVLWFRYHVVLKVVHKPQVVLUUBRVVLVVFUJVVMVULVVLYBRYHXGABCD
      BUWQUVOYIZBUWQUWEYIZUXTUYAANCVUHEANVCCVUHUXKAVDREUXMAVERGVGZUUCHVVNYJVVOY
      JYKAPUBPVVGYIYLJZUBPKVVFKLUKJZUDJZMJZYIZUBPVVIYIKYOQVVQVWAWIUUDUBKUUFXQAU
      BPVVTVVIVVLVVSVVHKMVVLVVRUJVVFUDVVRUJWIVVLUUGRYMYMUUEUUHVVFUVOKUDYNVVFUVO
      WIVVHUWBKMVVFUVOUJUDYNYMYPVUFUXIABLNOULUUIUUJUHZUUKUUQUHZOOUWQUWSALPQUXGA
      XKZVBAUXGVAUTABLOUWSVWDUULUWQOUURACDUUMRUUNVWCYJUWQVWBQACDUUORUUPYQAOUAWO
      VURYIZYLJOUANYRULJZVURYIZYLJZUAWOVUTYIZAVWEVWGOYLAUAWOVWFVURWOVWFWIAUUSRZ
      YSYMAVWHUAVWFVUTYIZVWIAUANYRVWGVWKANVUHVKYRVIQAUUTRANVUHUVANYRVFTAUVBRVWG
      YJVWKYJYKAUAVWFWOVUTAWOVWFVWJUVCYSYTYTVUQUVQIUCUVDVUQUVQWIVUSUVTLUIVUQUVQ
      UVSMYNYMYPAIUXCAUPRXLUVEUXAUVOVVJUVHUXAUWKUWOUXAIUWJUXDUXAUVSVUDUVFUXAUVS
      IUXAIUXBUXAIVUCYFXOVUKUYRUVGXTUXAUWNUVNUXAUWLUWMUXAUVNUYSXIUWMWBQUXAUWMLW
      BUVIUVJUVKRWCUXHUXAUVNUYSYFXTXJABCDUWKBUWQUWIYIZBUWQUWPYIZIEFVVPHVWLYJVWM
      YJUWKYJIYOQAUVLRUVMYQ $.
  $}

  ${
    aks4d1p1p7.1 $e |- ( ph -> A e. RR ) $.
    aks4d1p1p7.2 $e |- ( ph -> 4 <_ A ) $.
    $( Bound of intermediary of inequality step.  (Contributed by metakunt,
       19-Aug-2024.) $)
    aks4d1p1p7 $p |- ( ph
        -> ( ( 2
               x.
               ( ( 1
                   /
                   ( ( ( ( 2 logb A ) ^ 5 ) + 1 )
                     x.
                     ( log ` 2 ) ) )
                 x.
                 ( ( ( 5 x. ( ( 2 logb A ) ^ 4 ) )
                     x.
                     ( 1 / ( A x. ( log ` 2 ) ) ) )
                   +
                   0 ) ) )
             +
             ( ( 2 / ( ( log ` 2 ) ^ 2 ) )
               x.
               ( ( ( log ` A ) ^ ( 2 - 1 ) ) / A ) ) )
           <_
           ( ( 4 / ( ( log ` 2 ) ^ 4 ) )
             x.
             ( ( ( log ` A ) ^ 3 ) / A ) ) ) $=
      ( c2 c1 cdiv co c5 cexp caddc cmul cc0 cle a1i oveq1d oveq2d eqcomd eqtrd
      c4 clog cfv c3 clogb cmin recnd 0red wcel 4re clt wbr 4pos ltletrd necomd
      cr ltned logcld 2cnd 2pos 1lt2 crp wb 2rp loggt0b ax-mp mpbir cn0 expdivd
      5nn0 2re elrpd relogcld reexpcld nn0zd expne0d redivcld readdcld remulcld
      1red expcld divcld 1cnd rplogcld rpexpcld 3nn0 df-4 letrd expge0d divge0d
      mulne0d 5re resqcld syl mpbird rpmulcld lemul1ad lediv2ad lemul2ad div23d
      cz divmuldivd oveq12d mulcld mulassd divassd mulridd mulcomd expsubd wceq
      leadd1dd recni cc jca syl2anc mpbid divdiv1d dividd eqeltrd cdc 10nn0 ceu
      wa wn ltled lenltd gtned rpne0d exp1d eqeltrrd eqbrtrd c6 2nn0 c7 3brtr3d
      c9 expaddd adddird lemul1d eqidd div32d addcld nn0addge2i breqtrrdi ltp1d
      1re logge0d lelttrd 4nn0 2z 1nn0 1lt4 divne0d 4z nn0ge0d mulge0d rpdivcld
      0le2 sylib ge0p1rpd 0le1 rpred rpge0d lep1d sqcld divdiv2d ax-1cn subaddi
      cneg 4p1e5 subid1d eqtr4d jctir 0cnd subeqrev df-neg eqtr4di 1zzd expnegd
      5t2e10 nn0cni mullidd 10re 3z ere nn0red egt2lt3 simpri 3lt4 lttrd mtbird
      loglt1b cn 10nn nnledivrp relogbcld logbgt0b rehalfcld nn0ge0i relogbexpd
      sq2 leidd logblebd 1nn 6nn0 nn0addcli 5p2e7 7re nn0addge1i breqtri declei
      7p2e9 eqbrtri 4t4e16 eqcomi leexp1ad divdird 2p1e3 subadd2d lediv1d uzidd
      ldiv cuz relogbval df-2 eqnetrd div12d 5cn df-5 reccld addridd 1e2m1 4cn
      ) AEFBUAUBZEUAUBZGHZIJHZFKHZUYNLHZGHZIUYMTJHZLHZUYNIJHZBLHZGHZLHZLHZEUYNE
      JHZGHZUYMFJHZBGHZLHZKHZTUYMUCJHZLHZUYNTJHZBLHZGHZEFEBUDHZIJHZFKHZUYNLHZGH
      ZIVURTJHZLHZFBUYNLHZGHZLHZMKHZLHZLHZVUHUYMEFUEHZJHZBGHZLHZKHTVUOGHVUMBGHL
      HZNAVULEFUYMIJHZVUBGHZFKHZUYNLHZGHZVUDLHZLHZVUKKHZVUQNAVUFVWBVUKKAVUEVWAE
      LAUYSVVTVUDLAUYRVVSFGAUYQVVRUYNLAUYPVVQFKAUYMUYNIABABCUFZAMBAMBAUGZAMTBVW
      ETUOUHAUIOZCMTUJUKAULOZDUMZUPUNZUQZAEAURZAMEAMEVWEMEUJUKAUSOZUPUNZUQZAMUY
      NAMUYNVWEMUYNUJUKZAVWOFEUJUKZUTEVAUHZVWOVWPVBVCEVDVEZVFOZUPUNZIVGUHAVIOZV
      HPPQPQPAVWCEFVVQUYNLHZGHZVUDLHZLHZVUKKHZVUQAVWBVUKAEVWAEUOUHAVJOZAVVTVUDA
      FVVSAVSZAVVRUYNAVVQFAVVPVUBAUYMIABABCVWHVKZVLZVXAVMZAUYNIAEVWQAVCOZVLZVXA
      VMZAUYNIVWNVWTAIVXAVNZVOZVPZVXHVQZVXMVRAVVRUYNAVVQFAVVPVUBAUYMIVWJVXAVTZA
      UYNIVWNVXAVTZVXPWAZAWBZUUAVWNAMVVRAMVVRVWEAMVVQVVRVWEVXQVXRAVVPVUBVXKAUYN
      IAEVXGVWPAUTOZWCZVXOWDZAUYMIVXJVXAABCAFTBVXHVWFCAFUCFKHZTNFVYFNUKAFUCUUEW
      EUUBOWFUUCDWGUUFZWHZWIAVVQVXQUUDUUGUPUNVWTWJVPZAVUAVUCAIUYTIUOUHAWKOZAUYM
      TVXJTVGUHAUUHOZVMZVRZAVUBBVXNCVRAVUBBVXTVWDVXPVWIWJZVPZVRZVRZAVUHVUJAEVUG
      VXGAUYNVXMWLZAUYNEVWNVWTEWTUHAUUIOZVOZVPAVUIBAUYMFVXJFVGUHAUUJOZVMZCVWIVP
      VRZVQAVXEVUKAEVXDVXGAVXCVUDAFVXBVXHAVVQUYNVXQVXMVRAVVQUYNVYAVWNAVVPVUBVXS
      VXTAUYMIVWJAMUYMAMUYMVWEAMUYMUJUKZFBUJUKZAFTBVXHVWFCFTUJUKAUUKODUMZABVAUH
      ZWUDWUEVBVXIBVDWMWNUPUNZVXOVOZVXPUULVWTWJVPZVYOVRZVRZWUCVQAVUNVUPATVUMVWF
      AUYMUCVXJUCVGUHAWEOZVMZVRZAVUOBAUYNTVXMVYKVMZCVRAVUOBAUYNTVWNVYKVTZVWDAUY
      NTVWNVWTTWTUHAUUMOVOZVWIWJVPZAVWBVXEVUKVYQWULWUCAVWAVXDEVYPWUKVXGMENUKAUU
      QOZAVVTVXCVUDVYIWUJVYOAVUAVUCVYMAVUBBVYEVXIWOAIUYTVYJVYLAIVXAUUNAUYMTVXJV
      YKVYGWHUUOWIAVXBVVSFAVVQUYNAVVPVUBAUYMIABCWUFWCZVXOWDVYEUUPVYDWOAVVRUYNAV
      VQVXQAVVPVUBVXKAUYNIAEVXGAVWOVWPVWSVWRUURWCZVXOWDVYHWIUUSWVBWOVXHMFNUKAUU
      TOAVVQVVRUYNVXQVXRAUYNWVBUVAAUYNWVBUVBAVVQVXQUVCWPWQWPWRXJAVXFEFVVPUYNLHZ
      VUBGHZGHZVUDLHZLHZEVUILHZVUGBLHZGHZKHZVUQNAVXEWVGVUKWVJKAVXDWVFELAVXCWVEV
      UDLAVXBWVDFGAWVDVXBAVVPUYNVUBVXSVWNVXTVXPWSRQPQAEVUGVUIBVWKAUYNVWNUVDZAUY
      MFVWJWUAVTZVWDVYTVWIXAZXBAWVKEFVUBLHZWVCGHZLHZVUDLHZWVJKHZVUQNAWVGWVRWVJK
      AWVGEWVPVUDLHZLHZWVRAWVFWVTELAWVEWVPVUDLAFWVCVUBVYBAVVPUYNVXSVWNXCZVXTAVV
      PUYNVXSVWNWUIVWTWJZVXPUVEPQAWVRWWAAEWVPVUDVWKAWVOWVCAFVUBVYBVXTXCZWWBWWCW
      AAVUDVYOUFXDRSPAWVSEWVOLHZWVCGHZVUDLHZWVJKHZVUQNAWVRWWGWVJKAWVQWWFVUDLAWW
      FWVQAEWVOWVCVWKWWDWWBWWCXERPPAWWHEFLHZVUBLHZWVCGHZVUDLHZWVJKHZVUQNAWWGWWL
      WVJKAWWFWWKVUDLAWWEWWJWVCGAWWJWWEAEFVUBVWKVYBVXTXDRPPPAWWMEVUBLHZWVCGHZVU
      DLHZWVJKHZVUQNAWWLWWPWVJKAWWKWWOVUDLAWWJWWNWVCGAWWIEVUBLAEVWKXFZPPPPAWWQW
      WNVUALHZWVCVUCLHZGHZWVJKHZVUQNAWWPWXAWVJKAWWNWVCVUAVUCAEVUBVWKVXTXCZWWBAV
      UAVYMUFZAVUBBVXTVWDXCZWWCVYNXAPAWXBWWSVVPUYNVUCLHZLHZGHZWVJKHZVUQNAWXAWXH
      WVJKAWWTWXGWWSGAVVPUYNVUCVXSVWNWXEXDQPAWXIVUAWWNLHZVVPUYNVUBLHZBLHZLHZGHZ
      WVJKHZVUQNAWXHWXNWVJKAWWSWXJWXGWXMGAWWNVUAWXCWXDXGAWXFWXLVVPLAWXLWXFAUYNV
      UBBVWNVXTVWDXDZRQXBPAWXOVUAVVPGHZWWNWXLGHZLHZWVJKHZVUQNAWXNWXSWVJKAWXSWXN
      AVUAVVPWWNWXLWXDVXSWXCAWXKBAUYNVUBVWNVXTXCZVWDXCWUIAWXKBWYAVWDAUYNVUBVWNV
      XTVWTVXPWJVWIWJXARPAWXTIUYTVVPGHZLHZWWNWXFGHZLHZWVJKHZVUQNAWXSWYEWVJKAWXQ
      WYCWXRWYDLAIUYTVVPAIVYJUFZAUYTVYLUFZVXSWUIXEAWXLWXFWWNGWXPQXBPAWYFIUYMFUV
      HZJHZLHZEUYNGHZVUBVUCGHZLHZLHZWVJKHZVUQNAWYEWYOWVJKAWYCWYKWYDWYNLAWYBWYJI
      LAWYBUYMTIUEHZJHZWYJAWYRWYBAUYMTIVWJWUHVXOATVYKVNZXHRAWYQWYIUYMJAWYQMFUEH
      ZWYIAITUEHZFMUEHZXIZWYQWYTXIZAXUAFXUBXUAFXIZAXUETFKHZIXIUVIITFIWKXKTUIXKZ
      UVFUVGVFOAFVYBUVJUVKAIXLUHZTXLUHZYBFXLUHZMXLUHZYBXUCXUDVBAXUHXUIWYGXUGUVL
      AXUJXUKVYBAUVMXMITFMUVNXNXOFUVOUVPQSQAWYNWYDAEUYNVUBVUCVWKVWNVXTWXEVWTVYN
      XARXBPAWYPIFVUIGHZLHZWYLVUBVUBGHZBGHZLHZLHZWVJKHZVUQNAWYOXUQWVJKAWYKXUMWY
      NXUPLAWYJXULILAUYMFVWJWUHAUVQZUVRQAWYMXUOWYLLAXUOWYMAVUBVUBBVXTVXTVWDVXPV
      WIXPRQXBPAXURIFLHZVUIGHZWYLFBGHZLHZLHZWVJKHZVUQNAXUQXVDWVJKAXUMXVAXUPXVCL
      AXVAXUMAIFVUIWYGVYBWVMAUYMFVWJWUHXUSVOZXERAXUOXVBWYLLAXUNFBGAVUBVXTVXPXQP
      QXBPAXVEIVUIGHZWWIUYNBLHZGHZLHZWVJKHZVUQNAXVDXVJWVJKAXVAXVGXVCXVILAXUTIVU
      IGAIWYGXFPAEUYNFBVWKVWNVYBVWDVWTVWIXAXBPAXVKIELHZVUIXVHLHZGHZWVJKHZVUQNAX
      VJXVNWVJKAXVJIWWILHZXVMGHXVNAIVUIWWIXVHWYGWVMAWWIEXLWWRVWKXRAUYNBVWNVWDXC
      ZXVFAUYNBVWNVWDVWTVWIWJZXAAXVPXVLXVMGAWWIEILWWRQPSPAXVOFMXSZXVMGHZWVJKHZV
      UQNAXVNXVTWVJKAXVLXVSXVMGXVLXVSXIZAUVSOZPPAXWAVUQNUKXWABLHZVUQBLHZNUKAXVT
      BLHZWVJBLHZKHZVUNBVUPGHZLHZXWDXWENAXVSBXVMGHZLHZWVHBWVIGHZLHZKHZVUNBBGHZV
      UOGHZLHZXWHXWJNAXVSBBVUIUYNLHZLHZGHZLHZWVHXWPVUGGHZLHZKHZVUNFVUOGHZLHZXWO
      XWRNAXVSFXWSGHZLHZWVHFVUGGHZLHZKHZVUNFLHZVUOGHZXXEXXGNAXVSFLHZXWSGHZFWVHV
      UGGHZLHZKHZVUNVUOGHZXXLXXNNAXXSXVSXWSGHZXXQKHZXXTNAXXPXYAXXRXXQKAXXOXVSXW
      SGAXVSXVSXLUHAXVSXTUVTOZXFPAXXQAWVHVUGAEVUIVWKWVMXCZWVLVYTWAZUWAXBAXYBXXT
      NUKXYBUYNLHZXXTUYNLHZNUKAXYAUYNLHZXXQUYNLHZKHZVUNUYNLHZVUOGHZXYFXYGNAXVSU
      YNLHXWSGHZWVHUYNLHZVUGGHZKHZXYKUYNUCJHZUYNFJHZLHZGHZXYJXYLNAXVSVUIGHZWVHX
      YRLHZXYRXYRLHZGHZKHZVUNXYQGHZFLHZXYPXYTNAYUAWVHXYRGHZFLHZKHZYUFYUEYUGNAYU
      JYUAYUHKHZYUFNAYUIYUHYUAKAYUHAWVHXYRXYDAUYNFVWNWUAVTZAUYNFVWNVWTXUSVOZWAX
      FQAXVSUYMGHZEUYOFJHZLHZKHZTVUMXYQGHZLHZYUKYUFNAYUQXVSYUPKHZYUSAYUNYUPAXVS
      UYMXVSUOUHAUWBOZVXJWUHVPZAEYUOVXGAUYOFAUYMUYNVXJVXMVWTVPWUAVMVRZVQAXVSYUP
      YVAYVCVQATYURVWFAVUMXYQWUNAUYNUCVXMWUMVMAUYNUCVWNVWTUCWTUHAUWCOZVOZVPVRAY
      UNXVSYUPYVBYVAYVCAFUYMNUKZYUNXVSNUKZAYVFUYMFUJUKZYCAYVHBYAUJUKZAYABNUKYVI
      YCAYABYAUOUHAUWDOZCAYAUCBYVJAUCWUMUWEZCYAUCUJUKZAEYAUJUKYVLUWFUWGOAUCTBYV
      KVWFCUCTUJUKAUWHODUMUWIYDAYABYVJCYEXOAWUGYVHYVIVBVXIBUWKWMUWJAFUYMVXHVXJY
      EWNAXVSUWLUHZUYMVAUHYVFYVGVBYVMAUWMOWVAXVSUYMUWNXNXOXJAXVSEVURFJHZLHZKHZT
      VURUCJHZLHZYUTYUSNAYVPYVRNUKYVPYVNGHZYVRYVNGHZNUKAXVSYVNGHZEKHZTVUREJHZLH
      ZYVSYVTNAYWBTEEJHZLHZYWDAYWAEAXVSYVNYVAAVURFAEBVXGVWLCVWHAFEVXHVYCYFZUWOZ
      WUAVMZAYVNAVURFAVURYWHAMVURUJUKZWUEWUFAWUGVWQVWPYBYWJWUEVBVXIAVWQVWPVXLVY
      CXMBEUWPXNWNZVKZXUSWDZYGZVPZVXGVQZATYWEVWFAYWETUOYWETXIAUWTOZVWFXRZVRZATY
      WCVWFAVURYWHWLZVRAYWBXVSVURGHZEKHZYWFNAYWAYXAEKAYVNVURXVSGAVURAVURYWHUFZY
      HQZPZAYXBXVSEGHZEKHZYWFAYWBYXBUOYXEYWPYIAYXFEAXVSYVAUWQVXGVQYWSAYXAYXFEAY
      WAYXAUOYXDYWOYIAXVSEYVAVXGVWMVPVXGAEVURXVSVXLYWLYVAMXVSNUKAXVSXTUWROAEETU
      DHZVURNAEEYWEUDHZYXHAYXIEAEEVXLYWGVYSUWSRAYWETEUDYWQQSAETBVYSAEVXGUXAVWFV
      WGCVWHDUXBYJZWQXJAIEKHZFYKXSZYXGYWFNYXKYXLNUKAFYKYXKUXCUXDIEVIYLUXEYXKYMY
      ONUXFYMYMEKHYONYMEUXGYLUXHUXKUXIUXLUXJOAIYXFEKAXWBIYXFXIXWCAIEXVSWYGVWKXY
      CVWMUYAXOPAYXLTTLHZYWFYXLYXMXIAYXMYXLUXMUXNOATYWETLAYWETYWQRQSYNWGYJAYWEY
      WCTYWRYWTVWFAMTVWEVWFVWGYDAEVUREVXGYWHEVGUHAYLOWUTYXJUXOWRWGAYVSYWBAYVSYW
      AYVOYVNGHZKHZYWBAXVSYVOYVNXYCAYVOAEYVNVXGYWIVRZUFAYVNYWIUFZYWNUXPAYXOYWAE
      YVNYVNGHZLHZKHYWBAYXNYXSYWAKAEYVNYVNVWKYXQYXQYWNXEQAYXSEYWAKAYXSWWIEAYXRF
      ELAYVNYXQYWNXQQWWRSQSSRAYWDTYVQYVNGHZLHZYVTAYWDTVURUCFUEHZJHZLHYYAAYWCYYC
      TLAEYYBVURJAYYBEAYYBEXIEFKHUCXIZYYDAUXQOAUCFEAUCYVKUFVYBVWKUXRWNRQQAYYCYX
      TTLAVURUCFYXCAMVURVWEYWKYFXUSYVDXHQSAYVTYYAATYVQYVNXUIAXUGOZAYVQAVURUCYWH
      WUMVMZUFYXQYWNXERSYNAYVPYVRYVNAXVSYVOYVAYXPVQATYVQVWFYYFVRYWMUXSWNAYVOYUP
      XVSKAYVNYUOELAVURUYOFJAEEUYBUBUHZWUGYBVURUYOXIZAYYGWUGAEVYSUXTZVXIXMEBUYC
      ZWMZPQQAYVQYURTLAYVQUYOUCJHYURAVURUYOUCJYYKPAUYMUYNUCVWJVWNVWTWUMVHSQYNWG
      AYUNYUAYUPYUHKAUYMVUIXVSGAVUIUYMAUYMVWJYHRQAYUHYUPAYUHEVUIXYRGHZLHYUPAEVU
      IXYRVWKWVMYULYUMXEAYYLYUOELAYUOYYLAUYMUYNFVWJVWNVWTWUAVHRQSRXBAYUFYUSATVU
      MXYQYYEAVUMWUNUFZAUYNUCVWNWUMVTZYVEXERYNYJAYUIYUDYUAKAYUIYUHXYRXYRGHZLHYU
      DAFYYOYUHLAYYOFAXYRYULYUMXQRQAWVHXYRXYRXYRXYDYULYULYULYUMYUMXASQAYUGYUFAY
      UFAVUNXYQATVUMYYEYYMXCZYYNYVEWAXFRYNAYUAXYMYUDXYOKAYUAYUAUYNUYNGHZLHZXYMA
      YUAYUAFLHZYYRAYYSYUAAYUAAXVSVUIXYCWVMXVFWAXFRAFYYQYUALAYYQFAUYNVWNVWTXQRZ
      QSAXVSVUIUYNUYNXYCWVMVWNVWNXVFVWTXASAYUBXYNYUCVUGGAXYRUYNWVHLAUYNVWNYHZQA
      VUGYUCAVUGUYNFFKHZJHYUCAEUUUBUYNJEUUUBXIAUYDOQAUYNFFVWNWUAWUAYPSRXBXBAYUG
      YUFUYNXYRGHZLHXYTAFUUUCYUFLAFYYQUUUCYYTAUYNXYRUYNGAXYRUYNUUUARQSQAVUNXYQU
      YNXYRYYPYYNVWNAXYRUYNXLUUUAVWNXRYVEAXYRUYNMUUUAVWTUYEXASYNAXYMXYHXYOXYIKA
      XVSUYNXWSXYCVWNAVUIUYNWVMVWNXCZAVUIUYNWVMVWNXVFVWTWJZWSAWVHUYNVUGXYDVWNWV
      LVYTWSXBAXYSVUOXYKGAVUOXYSAVUOUYNVYFJHXYSATVYFUYNJTVYFXIAWFOQAUYNUCFVWNWU
      AWUMYPSRQYNAXYFXYJAXYAXXQUYNAXYAAXVSXWSYVAAVUIUYNWUBVXMVRUUUEVPZUFXYEVWNY
      QRAVUNUYNVUOYYPVWNWUQAUYNTVWNVWTWYSVOZWSYNAXYBXXTUYNAXYAXXQUUUFAWVHVUGAEV
      UIVXGWUBVRVYRVYTVPVQAVUNVUOWUOWUPWURVPWVBYRWNYJAXXPXXIXXRXXKKAXVSFXWSXYCV
      YBUUUDUUUEXEAFWVHVUGVYBXYDWVLVYTUYFXBAVUNXXMVUOGAXXMVUNAVUNYYPXFRPYNAXXIX
      XBXXKXXDKAXXHXXAXVSLAXXHXWPXWSGHXXAAFXWPXWSGAXWPFABVWDVWIXQRZPABBXWSVWDVW
      DUUUDVWIUUUEXPSQAXXKXXKXXDAXXKYSAXXJXXCWVHLAFXWPVUGGUUUHPQSXBAVUNFVUOYYPV
      YBWUQUUUGXEYNAXXBXWLXXDXWNKAXXAXWKXVSLAXWTXVMBGAXWTXWSBLHXVMABXWSVWDUUUDX
      GAVUIUYNBWVMVWNVWDXDSQQAXXCXWMWVHLAXXCBBVUGLHZGHXWMABBVUGVWDVWDWVLVWIVYTX
      PAUUUIWVIBGABVUGVWDWVLXGQSQXBAXXFXWQVUNLAXXFXXFXWQAXXFYSAFXWPVUOGUUUHPSQY
      NAXWLXWFXWNXWGKAXWFXWLAXVSXVMBXYCAVUIXVHWVMXVQXCVWDAVUIXVHWVMXVQXVFXVRWJZ
      YTRAXWGXWNAWVHWVIBXYDAVUGBWVLVWDXCVWDAVUGBWVLVWDVYTVWIWJYTRXBAXWQXWIVUNLA
      XWQBBVUOLHZGHXWIABBVUOVWDVWDWUQVWIUUUGXPAUUUKVUPBGABVUOVWDWUQXGQSQYNAXWDX
      WHAXVTWVJBAXVTAXVSXVMYVAAVUIXVHWUBAUYNBVXMCVRVRUUUJVPZUFAWVJAVUKWVJUOWVNW
      UCYIZUFVWDYQRAXWEXWJAVUNVUPBATVUMYYEAUYMUCVWJWUMVTZXCAVUOBWUQVWDXCVWDAVUO
      BWUQVWDUUUGVWIWJYTRYNAXWAVUQBAXVTWVJUUULUUUMVQWUSVXIYRWNYJYJYJYJYJYJYJYJY
      JYJYJYJYJYJYJYJWGYJAVUFVVJVUKVVNKAVUEVVIELAUYSVVBVUDVVHLAUYRVVAFGAUYQVUTU
      YNLAUYPVUSFKAUYOVURIJAVURUYOAYYGWUGYYHYYIVXIYYJXNRZPPPQAVUDVVGVVHAVUDIUYO
      TJHZLHZVVFLHZVVGAVUDIUYTVUOGHZLHZVVFLHZUUURAVUDVUAVUOGHZVVFLHZUUVAAVUDVUA
      FLHZVUOVVELHZGHZUUVCAVUAUUVDVUCUUVEGAUUVDVUAAVUAAIUYTXUHAUYGOZWYHXCXFRAVU
      CVUOXVHLHZUUVEAVUCVUOUYNLHZBLHZUUVHAVUCVUCUUVJAVUCYSAVUBUUVIBLAVUBVUOXYRL
      HZUUVIAVUBUYNXUFJHUUVKAIXUFUYNJIXUFXIAUYHOQAUYNTFVWNWUAVYKYPSAXYRUYNVUOLU
      UUAQSPSAVUOUYNBWUQVWNVWDXDSAXVHVVEVUOLAUYNBVWNVWDXGQSXBAUUVCUUVFAVUAVUOFV
      VEWXDWUQVYBABUYNVWDVWNXCZWURABUYNVWDVWNVWIVWTWJXARSAUUVBUUUTVVFLAIUYTVUOW
      YGWYHWUQWURXEPSAUUUTUUUQVVFLAUUUSUUUPILAUUUPUUUSAUYMUYNTVWJVWNVWTVYKVHRQP
      SAUUUQVVDVVFLAUUUPVVCILAUYOVURTJUUUOPQPSAVVHVVGAVVGAVVDVVFAIVVCUUVGAVURTY
      XCVYKVTXCAVVEUUVLABUYNVWDVWNABVXIYGZVWTWJUYIXCUYJRSXBQAVUJVVMVUHLAVUIVVLB
      GAFVVKUYMJFVVKXIAUYKOQPQXBAVVOVUQATVUOVUMBXUIAUYLOWUQUUUNVWDWURUUVMXARYN
      $.
  $}

  ${
    $d C x $.  $d D x $.  $d E x $.  $d N k $.  $d N x $.  $d k ph $.
    $d ph x $.
    aks4d1p1p5.1 $e |- ( ph -> N e. NN ) $.
    aks4d1p1p5.2 $e |- A = ( ( N ^ ( |_ ` ( 2 logb B ) ) ) x. prod_ k e.
     ( 1 ... ( |_ ` ( ( 2 logb N ) ^ 2 ) ) ) ( ( N ^ k ) - 1 ) ) $.
    aks4d1p1p5.3 $e |- B = ( |^ ` ( ( 2 logb N ) ^ 5 ) ) $.
    aks4d1p1p5.4 $e |- ( ph -> 4 <_ N ) $.
    aks4d1p1p5.5 $e |- C = ( 2 logb ( ( ( 2 logb N ) ^ 5 ) + 1 ) ) $.
    aks4d1p1p5.6 $e |- D = ( ( 2 logb N ) ^ 2 ) $.
    aks4d1p1p5.7 $e |- E = ( ( 2 logb N ) ^ 4 ) $.
    $( Show inequality for existence of a non-divisor.  (Contributed by
       metakunt, 19-Aug-2024.) $)
    aks4d1p1p5 $p |- ( ph -> A < ( 2 ^ B ) ) $=
      ( c4 a1i c1 co c2 vx c3 cr wcel 3re 4re nnred caddc cle lep1d letrd clogb
      c5 cexp cmul clog cfv cdiv cc0 cmin cmpt ccncf wf wa 2re clt wbr 2pos w3a
      wb syl2anc 0red adantr 4pos simp2d ltletrd wne 1red 1lt2 necomd relogbcld
      ltned cn0 5nn0 reexpcld readdcld ltp1d cz nn0zd cc ax-resscn sselid gtned
      syl3anc crp 2z elrpd mpbid expgt0 ltadd1dd lttrd remulcld jca syl resqcld
      wceq fmpttd wss cioo cres cxr rexrd elioo5 mpbird resmptd cdv cdm elioore
      adantl 3pos eliooord 2rp addcld 3jca wfn wral redivcld 4nn0 1nn0 eqeltrrd
      recnd leidd eqid cn oveq2d oveq1d eqtrd eqcomd c6 breqtrd breqtrdi elicc2
      3p1e4 cv cicc biimpd imp simp1d logb1 cuz uzidd 1rp logblt eqbrtrrd simpr
      1lt4 3lt4 lelttrd iccssioo2 2cnd simpl 2lt3 jca32 logbgt0b mulcld ioossre
      sqcld relogcld 1cnd logcld loggt0b ax-mp sylibr mulne0d 5re expne0d 2m1e1
      eqeltri ralrimiva nfcv fnmptf aks4d1p1p6 fneq1d fndmd dvcn wi rescncf mpd
      cncfcdm 4z 4m1e3 4nn dvrelogpow2b mpteq2dva simpld ltled aks4d1p1p7 oveq2
      3nn0 oveq12d cdc sq2 oveq2i relogbexp eqeltrd breqtrrd 6nn0 leadd2dd df-6
      expge1d 2cn expaddd exp1d times2d logblebd relogbexpd eqbrtrd 6cn decnncl
      6t2e12 2nn ldiv mpbii lemuldiv2d eqtrdi 2nn0 4cn addcomli decaddi addlsub
      4p2e6 6nn eqtr4d leaddsub 2exp4 dvle2 aks4d1p1p4 ) ABCDEFGHIJKAUBPHUBUCUD
      ZAUEQZPUCUDZAUFQZAHIUGZAUBUBRUHSPUIAUBUYSUJUUCUUAZLUKZMNOAUAPHTTTPULSZUMU
      NSZRUHSZULSZUOSZVUETUNSZUHSZVUEPUNSZTDUOSZEUHSGTTTUAUUDZULSZUMUNSZRUHSZUL
      SZUOSZVUOTUNSZUHSZTRVUQTUPUQZUOSZURSZUMVUOPUNSZUOSZRVUNVVBUOSZURSZUOSZUSU
      HSZUOSZUOSZTVVBTUNSZURSZVUNUPUQZTRUTSZUNSZVUNURSZUOSZUHSZVVEPVVBPUNSZURSZ
      VVOUBUNSZVUNURSZUOSZVUAVUBAUAPHUUESZVVAVAZVWFUCVBSZUDZVWFUCVWGVCZAUAVWFVV
      AUCAVUNVWFUDZVDZVUSVUTVWLTVURTUCUDZVWLVEQZVWLTVUQVWNUSTVFVGZVWLVHQZVWLVUP
      RVWLVUOUMVWLTVUNVWNVWPVWLVUNUCUDZPVUNUIVGZVUNHUIVGZAVWKVWQVWRVWSVIZAVWKVW
      TAUYTHUCUDZVWKVWTVJZVUAVUBPHVUNUUBZVKUUFUUGZUUHZVWLUSPVUNAUSUCUDVWKAVLZVM
      ZUYTVWLUFQZVXEUSPVFVGZVWLVNQZVWLVWQVWRVWSVXDVOZVPZATRVQZVWKARTARTAVRZRTVF
      VGZAVSQZWBVTZVMZWAZUMWCUDZVWLWDQZWEZVWLVRZWFZVWLUSUSRUHSZVUQVXGVWLUSRVXGV
      YCWFVYDVWLUSVXGWGVWLUSVUPRVXGVYBVYCVWLVUOUCUDZUMWHUDZUSVUOVFVGZUSVUPVFVGZ
      VXSVWLUMVYAWIVWLTRULSZUSVUOVFVWLTWJUDZTUSVQVXMVYJUSXFVWLUCWJTWKVWNWLVWLUS
      TVXGVWPWMVXRTUUIWNVWLRVUNVFVGZVYJVUOVFVGZVWLRPVUNVYCVXHVXERPVFVGVWLUUPQVX
      KVPVWLTTUUJUQUDRWOUDZVUNWOUDZVYLVYMVJVWLTTWHUDZVWLWPQUUKVYNVWLUULQVWLVUNV
      XEVXLWQTRVUNUUMWNWRUUNVUOUMWSZWNWTXAVXRWAXBVWLVUOVWLTVUNVWNVWPVXEVWLUSPVU
      NVWLVLVXHVXEVXJVWLVWQVWRVWSVWLVWKVWTAVWKUUOVWLUYTVXAVDZVXBAVYRVWKAUYTVXAV
      UAVUBXCVMVXCXDWRVOVPVXRWAXEWFXGAUCWJXHZVWGVWFWJVBSZUDVWIVWJVJVYSAWKQZAUAU
      BHRUHSZXISZVVAVAZVWFXJZVWGVYTAUAWUCVWFVVAAPWUCUDZHWUCUDZVWFWUCXHZAWUFUBPV
      FVGZPWUBVFVGZVDZAWUIWUJWUIAUUQQZAPHWUBVUAVUBAHRVUBVXNWFZLAHVUBWGZUURXCAUB
      XKUDZWUBXKUDZPXKUDWUFWUKVJAUBUYSXLZAWUBWUMXLZAPVUAXLUBWUBPXMWNXNAWUGUBHVF
      VGZHWUBVFVGZVDZAWUSWUTAUBPHUYSVUAVUBWULLVPWUNXCAWUOWUPHXKUDWUGWVAVJWUQWUR
      AHVUBXLUBWUBHXMWNXNUBWUBPHUUSVKZXOAWUDWUCWJVBSZUDZWUEVYTUDZAVYSWUCWJWUDVC
      ZWUCUCXHZVIUCWUDXPSZXQWUCXFWVDAVYSWVFWVGWUAAUAWUCVVAWJAVUNWUCUDZVDZVUSVUT
      WVJTVURWVJUUTZWVJVURWVJTVUQVWMWVJVEQZVWOWVJVHQZWVJVUPRWVJVUOUMWVJTVUNWVLW
      VMWVIVWQAVUNUBWUBXRXSZWVJUSUBVUNWVJVLZUYRWVJUEQZWVNUSUBVFVGZWVJXTQWVIUBVU
      NVFVGZAWVIWVRVUNWUBVFVGZVDWVRVUNUBWUBYAWVRWVSUVAXDXSZXAZAVXMWVIVXQVMWAZVX
      TWVJWDQZWEZWVJVRZWFZWVJUSVYEVUQWVOWVJUSRWVOWWEWFWWFWVJUSWVOWGWVJUSVUPRWVO
      WWDWWEWVJVYFVYGVYHVYIWWBWVJUMWWCWIWVJVYHVYLWVJRUBVUNWWEWVPWVNWVJRTUBWWEWV
      LWVPVXOWVJVSQZTUBVFVGWVJUVBQXAWVTXAWVJVYOTWOUDZVXOVDVDVYHVYLVJWVJVYOWWHVX
      OWVJVUNWVNWWAWQZWWHWVJYBQZWWGUVCVUNTUVDXDXNVYQWNWTXAZWVJRTWVJRTWWEWWGWBVT
      WAYKUVEWVJVUOWVJUCWJVUOWKWWBWLUVGYCXGWVGAUBWUBUVFQZYDAWUCWVHAWVHWUCYEUAWU
      CVVTVAZWUCYEZAVVTUCUDZUAWUCYFWWNAWWOUAWUCWVJVVLVVSWVJTVVKWVLWVJVVDVVJWVJR
      VVCWWEWVJVUQVVBWWFWVJTWWJUVHZXBWVJVUQVVBWVJVUPRWVJUCWJVUPWKWWDWLWVJUVIYCW
      VJTWVKWVJUSTWVOWVMWMUVJZWVJUSVUQWVOWWKWMAVVBUSVQWVIAUSVVBAUSVVBVXFAVXOUSV
      VBVFVGZVXPWWHWWRVXOVJYBTUVKUVLUVMWBVTVMZUVNYGWVJVVIUSWVJVVFVVHWVJUMVVEUMU
      CUDWVJUVOQWVJVUOPWWBPWCUDZWVJYHQZWEZXBWVJRVVGWWEWVJVUNVVBWVNWWPXBWVJVUNVV
      BWVJUCWJVUNWKWVNWLWWQWVJUSVUNWVOWWAWMZWWSUVNYGXBWVOWFXBXBWVJVVNVVRWVJTVVM
      WVLWVJVVBWWPXEWVJVVBTWWQWWSVYPWVJWPQUVPYGWVJVVQVUNWVJVVOVVPWVJVUNWWIUVHZV
      VPWCUDWVJVVPRWCUVQYIUVRQWEWVNWXCYGXBWFUVSUAWUCVVTUCUAWUCUVTZUWAXDAWUCWVHW
      WMAUAUBWUBUYSWUMAUBUYSYLAUBHWUBUYSVUBWUMVUDAHVUBUJUKZUWBUWCXNUWDWUCUCWUDU
      WEVKAWUHWVDWVEUWFWVBWUCWJVWFWUDUWGXDUWHYJVWFWJUCVWGUWIVKXNAUAVWFVVEVAZVWH
      UDZVWFUCWXGVCZAUAVWFVVEUCVWLVUOPVXSWWTVWLYHQWEXGAVYSWXGVYTUDWXHWXIVJWUAAU
      AWUCVVEVAZVWFXJZWXGVYTAUAWUCVWFVVEWVBXOAWXJWVCUDZWXKVYTUDZAVYSWUCWJWXJVCZ
      WVGVIUCWXJXPSZXQWUCXFWXLAVYSWXNWVGWUAAUAWUCVVEWJWVJUCWJVVEWKWXBWLXGWWLYDA
      WUCWXOAWXOWUCYEUAWUCVWBVVOPRUTSZUNSZVUNURSZUOSZVAZWUCYEZAWXSUCUDZUAWUCYFW
      YAAWYBUAWUCWVJVWBWXRWVJPVWAUYTWVJUFQWVJVVBPWWPWXAWEWVJVVBPWWQWWSPWHUDWVJU
      WJQUVPYGWVJWXQVUNWVJVVOWXPWXDWXPWCUDWVJWXPUBWCUWKUWSUVRQWEWVNWXCYGXBUVSUA
      WUCWXSUCWXEUWAXDAWUCWXOWXTAUAUBWUBVWBWXJWXTPUYSWUMWVQAXTQWXFWXJYMWXTYMVWB
      YMZPYNUDAUWLQZUWMUWCXNUWDWUCUCWXJUWEVKAWUHWXLWXMUWFWVBWUCWJVWFWXJUWGXDUWH
      YJVWFWJUCWXGUWIVKXNAUAPHVUAVUBVUCLUWBAUCUAPHXISZVVEVAZXPSUAWYEWXSVAZUAWYE
      VWEVAAUAPHVWBWYFWYGPVUAVUBVXIAVNQLWYFYMWYGYMWYCWYDUWMAUAWYEWXSVWEAVUNWYEU
      DZVDZWXRVWDVWBUOWYIWXQVWCVUNURWYIWXPUBVVOUNWXPUBXFWYIUWKQYOYPYOUWNYQWYIVU
      NWYHVWQAVUNPHXRXSZWYIPVUNUYTWYIUFQWYJWYHPVUNVFVGZAWYHWYKVUNHVFVGVUNPHYAUW
      OXSUWPUWQVUNPXFZVUSVUIVUTVUJUHWYLVURVUHTUOWYLVUQVUGTULWYLVUPVUFRUHWYLVUOV
      UEUMUNVUNPTULUWRZYPYPYOYOWYLVUOVUETUNWYMYPUWTWYLVUOVUEPUNWYMYPVUNHXFZVUSV
      UMVUTEUHWYNVUSTTTHULSZUMUNSZRUHSZULSZUOSZVUMWYNVURWYRTUOWYNVUQWYQTULWYNVU
      PWYPRUHWYNVUOWYOUMUNVUNHTULUWRZYPYPYOYOWYNVUMWYSWYNDWYRTUODWYRXFWYNMQYOYR
      YQWYNVUTWYOTUNSZEWYNVUOWYOTUNWYTYPWYNEXUAEXUAXFWYNNQYRYQUWTWYNVVEWYOPUNSZ
      GWYNVUOWYOPUNWYTYPWYNGXUBGXUBXFWYNOQYRYQAVUKRYSUXAZVULUIAVUKXUCUIVGZVUIXU
      CVUJUTSZUIVGZAVUIRTUXAZXUEUIAVUIXUGUIVGVUHXUGTURSZUIVGAVUHYSXUHUIAVUHTTUM
      UNSZRUHSZULSZYSUIAVUGXUJTULAVUFXUIRUHAVUETUMUNAVUETTTUNSZULSZTAXUMVUEXUMV
      UEXFAXULPTULUXBUXCQYRAWWHVXMVYPXUMTXFWWHAYBQZVXQVYPAWPQZTTUXDWNYQZYPZYPYO
      AXUKTTYSUNSZULSYSUIATXUJXURXUOATVWMAVEQZYLAXUIRAVUFXUIUCXUQAVUEUMAVUETUCX
      UPXUSUXEZVXTAWDQZWEZYJZVXNWFZAUSXUIXUJVXFXVCXVDAUSVUFXUIVFAVUEUCUDZVYGUSV
      UEVFVGZVIUSVUFVFVGAXVEVYGXVFXUTAUMXVAWIAUSTVUEVFVWOAVHQZXUPUXFYDVUEUMWSXD
      ZXUQYTAXUIXVCWGXAATYSXUSYSWCUDAUXGQZWEZAVWMYSWHUDVWOUSXURVFVGXUSAYSXVIWIZ
      XVGTYSWSWNAXUJXUIXUIUHSZXURXVDAXUIXUIXVCXVCWFZXVJARXUIXUIVXNXVCXVCATUMXUS
      XVAARTVXNXUSVXPUWPUXJUXHAXVLXVLXURUIAXVLXVMYLAXURXVLAXURXUITUOSZXVLAXURXU
      ITRUNSZUOSZXVNAXURTUMRUHSZUNSXVPAYSXVQTUNYSXVQXFAUXIQYOATUMRVYKAUXKQZRWCU
      DAYIQXVAUXLYQAXVOTXUIUOATXVRUXMYOYQAXUIAUCWJXUIWKXVCWLUXNYQYRYTUKUXOATYSX
      UNVXQXVKUXPYTUXQAYSTUOSXUGXFYSXUHXFUXTAYSTXUGYSWJUDAUXRQXVRAXUGAXUGXUGYNU
      DARTYIUYAUXSQUGZYKZAUSTVXFXVGWMUYBUYCYTAVUHXUGTATVUGXUSXVGAVUFRXVBVXNWFZA
      USVYEVUGVXFAUSRVXFVXNWFXWAAUSVXFWGAUSVUFRVXFXVBVXNXVHWTXAVXQWAZXVSXUNUYDX
      NAXUEXUGAXUEXUCPUTSZXUGAVUJPXUCUTAVUJXULPAVUETTUNXUPYPUXBUYEYOAXUGPUHSXUC
      XFXUGXWCXFRTYSXUGPYIUYFYHXUGYMPTYSUYGUXKUYKUYHUYIAXUGPXUCXVTPWJUDAUYGQAUC
      WJXUCWKAXUCXUCYNUDARYSYIUYLUXSQUGZWLUYJUYCUYMYRYTAVUIUCUDVUJUCUDXUCUCUDXU
      DXUFVJATVUHXUSXWBXBAVUEXUTXEXWDVUIVUJXUCUYNWNXNAVULXUCAVULTPUNSXUCAVUETPU
      NXUPYPUYOUYEYRYTLUYPUYQ $.
  $}

  ${
    $d N k $.  $d k ph $.
    aks4d1p1.1 $e |- ( ph -> N e. ( ZZ>= ` 3 ) ) $.
    aks4d1p1.2 $e |- A = ( ( N ^ ( |_ ` ( 2 logb B ) ) ) x. prod_ k e.
     ( 1 ... ( |_ ` ( ( 2 logb N ) ^ 2 ) ) ) ( ( N ^ k ) - 1 ) ) $.
    aks4d1p1.3 $e |- B = ( |^ ` ( ( 2 logb N ) ^ 5 ) ) $.
    $( Show inequality for existence of a non-divisor.  (Contributed by
       metakunt, 21-Aug-2024.) $)
    aks4d1p1 $p |- ( ph -> A < ( 2 ^ B ) ) $=
      ( c3 clt wbr c2 cexp co wceq c1 wcel a1i cmul 1nn0 wa clogb caddc cuz cfv
      c5 c4 cn 3nn adantr eluznn syl2anc cle 3p1e4 simpr cz 3z eluzelz zltp1led
      syl mpbid eqbrtrrid eqid aks4d1p1p5 ex cfl cfz cv cmin cprod cceil eqcomd
      oveq1d oveq2d c8 crp relogbexpd eqtrd leidd cr cc0 relogbcld cn0 reexpcld
      zred 5nn0 c9 breqtrd ltled letrd ltletrd eqbrtrd cdc decnncl decsuc recnd
      c6 1cnd mpbird syl3anc jca flbi resqcld prodeq1d 3cn adantl expcld subcld
      wb cc oveq2 oveq12d 3nn0 resubcld remulcld wo c7 mulcomli 6nn0 deccl 2nn0
      2cn 7nn0 0nn0 dec0h nn0cni ax-1cn oveq12i eqtri 0p1e1 2p1e3 6t2e12 decmac
      4nn0 decmul1c decltc exp1d eqtr2d 3brtr3d fveq2d w3a simp2 prodeq2dv 1red
      3expa 2rp 1lt2 ltned necomd cu2 2z 8re 8pos rpgt0d 3re nngt0i ceilcl 0red
      9re lep1d 8p1e9 2pos 3pos 3lexlogpow5ineq4 ceilge logblebd readdcld nnred
      2re 6nn ceilm1lt ltsubaddd 3lexlogpow5ineq5 5p1e6 nncnd subadd2d leaddsub
      5nn 2exp4 eqtr4i uzidd elrpd rpexpcld logblt eqcomi 9pos 3lexlogpow2ineq2
      simpld simprd df-3 1zzd 1le2 eluz elfznn nnnn0d fprodm1 2m1e1 fprod1 9nn0
      4z elnnz sylanbrc orcd elnn0 8cn 8t2e16 mul02i addcomli 4cn addlidi 2t1e2
      6cn decma2c mulridi oveq1i 7p4e11 7t6e42 decmul2c 2lt10 3lt10 3exp3 3m1e2
      7cn 4lt5 sq3 9m1e8 df-9 eqeltrd expaddd 2exp8 2t2e4 4p1e5 5t2e10 subadd2i
      8nn0 1p1e2 mpbir ltm1d nn0zd leexp2d lttrd oveq2i eluzle leloed mpjaod )
      AIEJKZBLCMNZJKZIEOZAVUFVUHAVUFUAZBCLLEUBNZUFMNZPUCNUBNZVUKLMNZDVUKUGMNZEV
      UJIUHQZEIUDUEQZEUHQVUPVUJUIRAVUQVUFFUJEIUKULGHVUJUGIPUCNZEUMUNVUJVUFVUREU
      MKAVUFUOVUJIEIUPQZVUJUQRAEUPQZVUFAVUQVUTFIEURUTZUJUSVAVBVUMVCVUNVCVUOVCVD
      VEAVUIVUHAVUIUAZELCUBNZVFUEZMNZPVUNVFUEZVGNZEDVHZMNZPVINZDVJZSNZLVULVKUEZ
      MNZBVUGJVVBILLIUBNZUFMNZVKUEZUBNZVFUEZMNZPVVOLMNZVFUEZVGNZVVJDVJZSNZLVVQM
      NZVVLVVNJVVBVWEVVTVWCIVVHMNZPVINZDVJZSNZVWFJVVBVWDVWIVVTSVVBVWCVVJVWHDAVU
      IVVHVWCQZVVJVWHOAVUIVWKUUAZVVIVWGPVIVWLEIVVHMVWLIEAVUIVWKUUBVLVMVMUUEUUCV
      NAVWJVWFJKVUIAVWJIIMNZIPMNZPVINZILMNZPVINZSNZSNZVWFJAVVTVWMVWIVWRSAVVSIIM
      AVVSIOZIVVRUMKZVVRVURJKZUAZAVXAVXBAILVOUBNZVVRUMAILLIMNZUBNZVXDAVXFIALILV
      PQAUUFRZAPLAPLAUUDZPLJKAUUGRZUUHUUIZVUSAUQRZVQVLAVXEVOLUBVXEVOOAUUJRVNVRA
      LVOVVQLUPQZAUUKRZALALVXMWEZVSVOVTQAUULRZWAVOJKAUUMRZAVVQAVVPVTQZVVQUPQZAV
      VOUFALIVXNALVXGUUNIVTQAUUORZWAIJKZAIUIUUPRZVXJWBUFWCQAWFRZWDVVPUUQZUTWEZA
      WAVOVVQAUURZVXOVYDVXPAVOWGVVQVXOWGVTQAUUSRZVYDAVOVOPUCNZWGUMAVOVXOUUTVYGW
      GOAUVARWHAWGVVPVVQVYFAVVOUFALILVTQAUVIRZWALJKAUVBRZVXSVXTAUVCRVXJWBZVYBWD
      ZAVVQAVXQVXRVYKVYCUTWEZAWGVVPVYFVYKAIVXSAIVXSVSUVDWIAVXQVVPVVQUMKVYKVVPUV
      EUTWJZWJZWKZVYNUVFWLAVVRLLUGMNZUBNZVURJAVVQVYPJKZVVRVYQJKZAVVQPWQWMZVYPJA
      VVQVVPPUCNZVYTVYLAVVPPVYKVXHUVGAVYTVYTUHQAPWQTUVJWNRUVHZAVVQPVINVVPJKZVVQ
      WUAJKAVXQWUCVYKVVPUVKUTAVVQPVVPVYLVXHVYKUVLVAAWUAVYTUMKZVVPVYTPVINZUMKZAV
      VPPUFWMZWUEUMVVPWUGUMKAUVMRAWUEWUGAWUEWUGOWUGPUCNVYTOZWUHAPUFWQWUGTWFUVNW
      UGVCWORAVYTPWUGAVYTWUBWPAWRZAWUGWUGUHQAPUFTUVRWNRUVOUVPWSVLWHAVXQPVTQVYTV
      TQWUDWUFXIVYKVXHWUBVVPPVYTUVQWTWSWKVYTVYPOAVYTVYTVYPVYTVCZUVSUVTRWHALLUDU
      EQVVQVPQVYPVPQVYRVYSXIALVXMUWAAVVQVYDVYOUWBALUGVXGUGUPQAUWTRZUWCLVVQVYPUW
      DWTVAAVYQUGVURALUGVXGVXJWUKVQUGVUROAVURUGUNUWERVRWHXAAVVRVTQVUSVWTVXCXIAL
      VVQVYHVYIAVVQAVXQVXRAVVOUFALIVYHVYIVXSVYAVXJWBZVYBWDVYCUTZWEZAWAWGVVQVYEV
      YFWUNWAWGJKAUWFRVYMWKZVXJWBVXKVVRIXBULWSVNAVWIPLVGNZVWHDVJZVWRAVWCWUPVWHD
      AVWBLPVGAVWBLOZLVWAUMKZVWALPUCNZJKZUAZAWUSWVAALVWAVYHAVVOVYJXCALVWAJKZVWA
      IJKZWVCWVDUAAUWGRZUWHWIAVWAIWUTJAWVCWVDWVEUWIIWUTOAUWJRWHXAAVWAVTQVXLWURW
      VBXIAVVOWULXCVXMVWALXBULWSVNXDAWUQPLPVINZVGNZVWHDVJZVWQSNVWRAVWHVWQDPLAPU
      PQZVXLUAZLPUDUEQZAWVIVXLAUWKZVXMXAWVJWVKPLUMKZWVMWVJUWLRPLUWMWSUTAVVHWUPQ
      ZUAZVWGPWVOIVVHIXJQWVOXERWVOVVHWVNVVHUHQAVVHLUWNXFUWOXGWVOWRXHVVHLOVWGVWP
      PVIVVHLIMXKVMUWPAWVHVWOVWQSAWVHPPVGNZVWHDVJZVWOAWVGWVPVWHDAWVFPPVGWVFPOAU
      WQRVNXDAWVIVWOXJQZUAWVQVWOOAWVIWVRWVLAVWNPAIPAIVXSWPZPWCQATRZXGWUIXHZXAVW
      HVWODPVVHPOVWGVWNPVIVVHPIMXKVMUWRUTVRVMVRVRXLAVWSLWGMNZPVINZVWFAVWMVWRAII
      VXSIWCQAXMRWDAVWOVWQAVWNPAIPVXSWVTWDVXHXNAVWPPAIVXSXCVXHXNXOXOAWWBPALWGVY
      HWGWCQAUWSRZWDZVXHXNZALVVQVYHAVVQWCQZVVQUHQZVVQWAOZXPZAWWHWWIAVXRWAVVQJKW
      WHWUMWUOVVQUXAUXBUXCWWGWWJXIAVVQUXDRWSWDZALXQWMZLVOSNZSNZUFPWMZPWMZVWSWWC
      JAWWNUGIWMZLWMZWWPJAWWNWWLVYTSNZWWRAWWMVYTWWLSWWMVYTOAVOLVYTUXEYBUXFXRRVN
      WWSWWROALXQWWQLVYTPPWMZWWLPWQTXSXTZYAYCWWLVCYAPPTTXTWALPPVYTUGIILWWTYDYAT
      TLYAYEWWTVCWXAXMXMWAVYTSNZPIUCNZUCNWAUGUCNUGWXBWAWXCUGUCVYTVYTWXAYFUXGIPU
      GXEYGUNUXHYHUGUXIUXJYIPWQWAPLIIPVYTPTXSYDTWUJPTYEZYAXMTLPSNZWAPUCNZUCNWUT
      IWXELWXFPUCUXKYJYHYKYIPLILWQSNTYAYKWQLPLWMUXLYBYLXRWOUXMYMPWQWWTLXQUGVYTY
      CTXSWUJYAYNXQPSNZUGUCNXQUGUCNWWTWXGXQUGUCXQUYCUXNUXOUXPYIUXQUXRYORVRWWRWW
      PJKAWWQWWOLPUGIYNXMXTUFPWFTXTZYATUXSUGUFIPYNWFXMTUXTUYDYPYPRWLAWWLVWMWWMV
      WRSAVWMWWLVWMWWLOAUYARVLALVWOVOVWQSAVWOIPVINZLAVWNIPVIAIWVSYQVMWXILOAUYBR
      YRZAVWQWGPVINZVOAVWPWGPVIVWPWGOAUYERVMWXKVOOAUYFRYRXLXLAWWCWWOLWMZPVINZWW
      PAWWBWXLPVIAWWBLVOMNZLPMNZSNZWXLAWWBLVYGMNWXPAWGVYGLMWGVYGOAUYGRVNALVOPAL
      VWOXJWXJWWAUYHZWVTVOWCQAUYORUYIVRAWXPLUFWMZWQWMZLSNZWXLAWXPWXSWXOSNWXTAWX
      NWXSWXOSWXNWXSOAUYJRVMAWXOLWXSSALWXQYQVNVRWXTWXLOAWXRWQWWOLLPWXSYALUFYAWF
      XTXSWXSVCYATLUFWAPLUFPPWXRPYAWFYDTWXRVCWXDYATTLLSNZWXFUCNUGPUCNUFWYAUGWXF
      PUCUYKYJYHUYLYIPWAPUFLSNTYDYJUYMWOYMYLYORVRVRVMWXMWWPOZAWYBWWPPUCNWXLOWWO
      PLWWPWXHTUYPWWPVCWOWXLPWWPWXLWWOLWXHYAXTYFYGWWPWWOPWXHTXTYFUYNUYQRYRYSAWW
      CWWBVWFWWFWWEWWKAWWBWWEUYRAWGVVQUMKWWBVWFUMKVYMALWGVVQVYHAWGWWDUYSWUMVXIU
      YTVAWKVUAWLUJWLVVBVVTVVEVWDVVKSVVBIEVVSVVDMAVUIUOZVVBVVRVVCVFVVBVVQCLUBVV
      BVVQVVMCVVBVVPVULVKVVBVVOVUKUFMVUIVVOVUKOAIELUBXKXFVMYTZVVBCVVMCVVMOVVBHR
      VLVRVNYTXLVVBVWCVVGVVJDVVBVWBVVFPVGVVBVWAVUNVFVVBVVOVUKLMVVBIELUBWYCVNVMY
      TVNXDXLVVBVVQVVMLMWYDVNYSVVBBVVLBVVLOVVBGRVLVVBVUGVVNVUGVVNOVVBCVVMLMHVUB
      RVLYSVEAIEUMKZVUFVUIXPAVUQWYEFIEVUCUTAIEVXSAEVVAWEVUDVAVUE $.
  $}

  ${
    aks4d1p2.1 $e |- ( ph -> N e. ( ZZ>= ` 3 ) ) $.
    aks4d1p2.2 $e |- A = ( ( N ^ ( |_ ` ( 2 logb B ) ) ) x. prod_ k e.
     ( 1 ... ( |_ ` ( ( 2 logb N ) ^ 2 ) ) ) ( ( N ^ k ) - 1 ) ) $.
    aks4d1p2.3 $e |- B = ( |^ ` ( ( 2 logb N ) ^ 5 ) ) $.
    $( Technical lemma for existence of non-divisor.  (Contributed by metakunt,
       27-Oct-2024.) $)
    aks4d1p2 $p |- ( ph -> ( 2 ^ B ) <_ ( _lcm ` ( 1 ... B ) ) ) $=
      ( cz wcel cc0 clt wbr c2 c5 a1i cr c3 syl c7 wa cn clogb co cexp cfv wceq
      cceil 2re 2pos cuz eluzelz zred 0red 3re 3pos eluzle ltletrd c1 1red 1lt2
      cle ltned necomd relogbcld cn0 5nn0 reexpcld eqeltrd 7re 3lexlogpow5ineq3
      ceilcl 7pos lttrd ceilge breqtrrd jca elnnz sylibr ltled letrd lcmineqlem
      ) ACACIJZKCLMZUACUBJAWCWDACNEUCUDZOUEUDZUHUFZICWGUGAHPZAWFQJZWGIJAWEOANEN
      QJAUIPKNLMAUJPAEAERUKUFJZEIJFREULSUMZAKREAUNZRQJAUOPWKKRLMAUPPAWJREVBMFRE
      UQSZURAUSNAUSNAUTUSNLMAVAPVCVDVEOVFJAVGPVHZWFVLSZVIAKWGCLAKWFWGWLWNAWGWOU
      MZAKTWFWLTQJAVJPZWNKTLMAVMPAEWKWMVKZVNAWIWFWGVBMWNWFVOSZURWHVPVQCVRVSATWG
      CVBATWFWGWQWNWPATWFWQWNWRVTWSWAWHVPWB $.
  $}

  ${
    $d A r $.  $d B q $.  $d B r $.  $d N k $.  $d k ph $.  $d ph q $.
    aks4d1p3.1 $e |- ( ph -> N e. ( ZZ>= ` 3 ) ) $.
    aks4d1p3.2 $e |- A = ( ( N ^ ( |_ ` ( 2 logb B ) ) ) x. prod_ k e.
     ( 1 ... ( |_ ` ( ( 2 logb N ) ^ 2 ) ) ) ( ( N ^ k ) - 1 ) ) $.
    aks4d1p3.3 $e |- B = ( |^ ` ( ( 2 logb N ) ^ 5 ) ) $.
    $( There exists a small enough number such that it does not divide ` A ` .
       (Contributed by metakunt, 27-Oct-2024.) $)
    aks4d1p3 $p |- ( ph -> E. r e. ( 1 ... B ) -. r || A ) $=
      ( wbr c1 co c2 clt adantr cr wcel a1i cz cc0 vq cv cdvds cfz wral wn wrex
      wa cexp aks4d1p1 cle clcmf cfv 2re cn0 clogb c5 cceil wceq c3 cuz eluzelz
      2pos syl zred 0red 3re 3pos eluzle ltletrd 1red 1lt2 ltned relogbcld 5nn0
      necomd reexpcld ceilcl eqeltrd 7re 3lexlogpow5ineq3 lttrd ceilge breqtrrd
      c7 7pos ltled jca elnn0z sylibr wss cfn cn elfznn adantl nnzd ssrdv fzfid
      ex lcmfcl syl2anc nn0red cfl cmin cprod cmul elnnz sylanbrc flcld 0le1 cc
      wne recnd gtned logbid1 syl3anc eqcomd breqtrd 2z leidd letrd logblebd wb
      2lt7 0zd flge mpbid nnexpcld nnnn0d zexpcl 1zzd zsubcld 1cnd addridd 1nn0
      caddc 1lt3 exp1d nnge1d elfzuz leexp2ad eqbrtrd ltaddsub2d nnmulcld nnred
      fprodnncl aks4d1p2 lcmfdvdsb biimpd syldbl2 wi dvdsle mpd lenltd pm2.21dd
      nn0zd simpr pm2.61dan rexnal ) AFUBBUCJZFKCUDLZUEZUFZUUTUFFUVAUGAUVBUVCAU
      VBUHZBMCUILZNJZUVCAUVFUVBABCDEGHIUJOUVDUVEBUKJUVFUFUVDUVEUVAULUMZBAUVEPQU
      VBAMCMPQAUNRZACSQZTCUKJZUHCUOQAUVIUVJACMEUPLZUQUILZURUMZSCUVMUSAIRZAUVLPQ
      ZUVMSQAUVKUQAMEUVHTMNJAVCRZAEAEUTVAUMQZESQZGUTEVBVDZVEZATUTEAVFZUTPQAVGRZ
      UVTTUTNJAVHRAUVQUTEUKJGUTEVIVDZVJZAKMAKMAVKZKMNJAVLRVMVPZVNUQUOQAVORVQZUV
      LVRVDZVSATCUWAACUVMPUVNAUVMUWHVEZVSZATUVMCNATUVLUVMUWAUWGUWIATWEUVLUWAWEP
      QAVTRZUWGTWENJAWFRAEUVTUWCWAZWBAUVOUVLUVMUKJUWGUVLWCVDZVJUVNWDZWGWHCWIWJV
      QOZAUVGPQUVBAUVGAUVASWKZUVAWLQZUVGUOQAUAUVASAUAUBZUVAQZUWRSQAUWSUHUWRUWSU
      WRWMQAUWRCWNWOWPWSWQZAKCWRUVAWTXAZXBOABPQUVBABABEMCUPLZXCUMZUILZKUVKMUILX
      CUMZUDLZEDUBZUILZKXDLZDXEZXFLZWMBUXKUSAHRAUXDUXJAEUXCAUVRTENJEWMQUVSUWDEX
      GXHZAUXCSQZTUXCUKJZUHUXCUOQAUXMUXNAUXBAMCUVHUVPUWJUWNUWFVNZXIATUXBUKJZUXN
      ATMMUPLZUXBUWAAMMUVHUVPUVHUVPUWFVNUXOATKUXQUKTKUKJAXJRAUXQKAMXKQMTXLMKXLU
      XQKUSAMUVHXMATMUWAUVPXNUWFMXOXPXQXRAMMCMSQAXSRAMUVHXTUVHUVPUWJUWNAMWECUVH
      UWKUWJAMWEUVHUWKMWENJAYDRWGAWECUWKUWJAWEUVMCNAWEUVLUVMUWKUWGUWIUWLUWMVJUV
      NWDWGYAYBYAAUXBPQTSQUXPUXNYCUXOAYEUXBTYFXAYGWHUXCWIWJYHAUXFUXIDAKUXEWRAUX
      GUXFQZUHZUXISQZTUXINJZUHUXIWMQUXSUXTUYAUXSUXHKUXSUVRUXGUOQUXHSQAUVRUXRUVS
      OUXSUXGUXRUXGWMQAUXGUXEWNWOYIEUXGYJXAZUXSYKYLUXSKTYPLZUXHNJUYAUXSUYCKUXHN
      UXSKUXSYMYNUXSKEKUILZUXHAKPQUXRUWEOZAUYDPQUXRAEKUVTKUOQAYORVQOUXSUXHUYBVE
      ZAKUYDNJUXRAKEUYDNAKUTEUWEUWBUVTKUTNJAYQRUWCVJAUYDEAEAEUVTXMYRXQXROUXSEKU
      XGAEPQUXRUVTOAKEUKJUXRAEUXLYSOUXRUXGKVAUMQAUXGKUXEYTWOUUAVJUUBUXSKTUXHUYE
      ATPQUXRUWAOUYFUUCYGWHUXIXGWJUUFUUDVSZUUEOZAUVEUVGUKJUVBABCDEGHIUUGOUVDUVG
      BUCJZUVGBUKJZAUVBUYIUVDUVBUYIUVDBSQZUWPUWQUVBUYIYCAUYKUVBABUYGWPOAUWPUVBU
      WTOUVDKCWRFBUVAUUHXPUUIUUJUVDUVGSQZBWMQZUYIUYJUUKAUYLUVBAUVGUXAUUPOAUYMUV
      BUYGOUVGBUULXAUUMYAUVDUVEBUWOUYHUUNYGUUOAUVCUUQUURUUTFUVAUUSWJ $.
  $}

  ${
    $d A r $.  $d B o $.  $d B r $.  $d N k $.  $d R r $.  $d k ph $.
    $d o ph $.
    aks4d1p4.1 $e |- ( ph -> N e. ( ZZ>= ` 3 ) ) $.
    aks4d1p4.2 $e |- A = ( ( N ^ ( |_ ` ( 2 logb B ) ) ) x. prod_ k e.
     ( 1 ... ( |_ ` ( ( 2 logb N ) ^ 2 ) ) ) ( ( N ^ k ) - 1 ) ) $.
    aks4d1p4.3 $e |- B = ( |^ ` ( ( 2 logb N ) ^ 5 ) ) $.
    aks4d1p4.4 $e |- R = inf ( { r e. ( 1 ... B ) | -. r || A } , RR , < ) $.
    $( There exists a small enough number such that it does not divide ` A ` .
       (Contributed by metakunt, 28-Oct-2024.) $)
    aks4d1p4 $p |- ( ph -> ( R e. ( 1 ... B ) /\ -. R || A ) ) $=
      ( vo cv cdvds wbr wn wcel cr clt a1i c1 cfz co crab cinf wceq wor cfn wne
      wa c0 wss w3a ltso fzfid ssrab2 ssfid aks4d1p3 rabn0 sylibr elfznn adantl
      wrex cn nnred ssrdv sstrd 3jca fiinfcl syl2anc eqeltrd breq1 notbid elrab
      ex sylib ) ADGMZBNOZPZGUACUBUCZUDZQDVTQDBNOZPZUJADWARSUEZWADWDUFAKTARSUGZ
      WAUHQZWAUKUIZWARULZUMWDWAQWEAUNTAWFWGWHAVTWAAUACUOWAVTULAVSGVTUPTZUQAVSGV
      TVCWGABCEFGHIJURVSGVTUSUTAWAVTRWIALVTRALMZVTQZWJRQAWKUJWJWKWJVDQAWJCVAVBV
      EVOVFVGVHRWASVIVJVKVSWCGDVTVQDUFVRWBVQDBNVLVMVNVP $.
  $}

  ${
    $d A r x y $.  $d B o $.  $d B r x y $.  $d N k $.  $d N r y $.
    $d R r y $.  $d k ph $.  $d o ph $.
    aks4d1p5.1 $e |- ( ph -> N e. ( ZZ>= ` 3 ) ) $.
    aks4d1p5.2 $e |- A = ( ( N ^ ( |_ ` ( 2 logb B ) ) ) x. prod_ k e.
     ( 1 ... ( |_ ` ( ( 2 logb N ) ^ 2 ) ) ) ( ( N ^ k ) - 1 ) ) $.
    aks4d1p5.3 $e |- B = ( |^ ` ( ( 2 logb N ) ^ 5 ) ) $.
    aks4d1p5.4 $e |- R = inf ( { r e. ( 1 ... B ) | -. r || A } , RR , < ) $.
    aks4d1p5.5 $e |- ( ( ( ph /\ 1 < ( N gcd R ) )
                         /\ ( R / ( N gcd R ) ) || A )
                      -> -. ( R / ( N gcd R ) ) || A ) $.
    $( Show that ` N ` and ` R ` are coprime for AKS existence theorem.
       Precondition will be eliminated in further theorem.  (Contributed by
       metakunt, 30-Oct-2024.) $)
    aks4d1p5 $p |- ( ph -> ( N gcd R ) = 1 ) $=
      ( c1 clt wbr cr wcel a1i adantr c2 vx vy vo cgcd co wceq wa cdiv simpr wn
      cle cfz cn cdvds aks4d1p4 simpld elfznn syl nnred cz cc0 cuz eluzelz 0red
      c3 cfv 3re zred 3pos eluzle ltletrd elnnz sylibr gcdnncl syl2anc redivcld
      jca nnne0d ltnled biimprd imp cv crab cinf wss wral wrex ssrab2 adantl ex
      ssrdv sstrd cfn wne fzfid ssfid aks4d1p3 rabn0 fiminre syl3anc breq1 1zzd
      c0 notbid clogb cexp cceil 2re 2pos 1red 1lt2 ltned necomd relogbcld 5nn0
      cn0 reexpcld ceilcl eqeltrd nnzd divgcdnnr nnge1d crp nnrpd rpne0d dividd
      c5 recnd eqbrtrd ltdiv23d ltled elfzle2 letrd elfzd exmidd mpjaodan mpbid
      lenltd pm2.21dd pm2.61dan elrabd lbinfle rpred wb ltnrd wo elnn1uz2 sylib
      lelttrd ) AMFDUDUEZNOZUUJMUFZAUUKUGZDDUUJUHUEZUKOZUULUUMUUOUUOUUMUUOUIUUM
      UUOUJZUGUUNDNOZUUOUUMUUPUUQUUMUUQUUPUUMUUNDAUUNPQUUKADUUJADADMCULUEZQZDUM
      QZAUUSDBUNOUJABCDEFGHIJKUOUPZDCUQURZUSZAUUJAFUMQZUUTUUJUMQZAFUTQZVAFNOZUG
      UVDAUVFUVGAFVEVBVFQZUVFHVEFVCURZAVAVEFAVDVEPQAVGRAFUVIVHZVAVENOAVIRAUVHVE
      FUKOHVEFVJURVKZVQFVLVMZUVBFDVNVOZUSZAUUJUVMVRVPSZADPQZUUKUVCSZVSVTWAUUMUU
      QUJZUUPUUMUUOUVRUUMDGWBZBUNOZUJZGUURWCZPNWDZUUNUKDUWCUFUUMKRUUMUWBPWEZUAW
      BUBWBUKOUBUWBWFUAUWBWGZUUNUWBQUWCUUNUKOAUWDUUKAUWBUURPUWBUURWEAUWAGUURWHR
      ZAUCUURPAUCWBZUURQZUWGPQAUWHUGUWGUWHUWGUMQAUWGCUQWIUSWJWKWLSZUUMUWDUWBWMQ
      ZUWBXCWNZUWEUWIAUWJUUKAUURUWBAMCWOUWFWPSAUWKUUKAUWAGUURWGUWKABCEFGHIJWQUW
      AGUURWRVMSUAUBUWBWSWTUUMUWAUUNBUNOZUJZGUUNUURUVSUUNUFUVTUWLUVSUUNBUNXAXDU
      UMUUNMCUUMXBACUTQUUKACTFXEUEZYGXFUEZXGVFZUTCUWPUFAJRAUWOPQUWPUTQAUWNYGATF
      TPQZAXHRVATNOAXIRUVJUVKAMTAMTAXJZMTNOZAXKRXLXMXNYGXPQAXORXQUWOXRURXSSZUUM
      UUNAUUNUMQZUUKAUUTUVFUXAUVBAFUVLXTDFYAVOZSZXTUUMUUNUXCYBUUMUUNDCUVOUVQUUM
      CUWTVHUUMUUNDUVOUVQUUMDDUUJUVQADYCQUUKADUVBYDZSZAUUJYCQUUKAUUJUVMYDSUUMDD
      UHUEZMUUJNUUMDUUMDUVQYHUUMDUXEYEZYFAUUKUIZYIYJZYKADCUKOZUUKAUUSUXJUVADMCY
      LURSYMYNUUMUWLUWMUWMLUUMUWMUIUUMUWLYOYPUUAUAUBUUNUWBUUBWTYIUUMDUUNUVQUVOY
      RYQZSYSYTUUMUUQUUPUUMDDUUJAUVPUUKADUXDUUCZSZUXEUUMUUJUUMUUQUVEUXIUXKYSYDU
      UMUXFMUUJNUUMDUUMDUXMYHUXGYFUXHYIYJAUUQUUPUUDUUKAUUNDAUUNUXBUSUXLVSSYQYSA
      UUKUJZUGZUULUULUUJTVBVFQZUXOUULUIUXOUXPUGZUUJUUJNOUULUXQUUJTUUJUXOUUJPQUX
      PUXOUUJAUVEUXNUVMSZUSSZUWQUXQXHRZUXSUXQUUJMTUXSUXQXJUXTUXOUUJMUKOZUXPAUXN
      UYAAUYAUXNAUUJMUVNUWRYRVTWASUWSUXQXKRUUIUXPTUUJUKOUXOTUUJVJWIVKUXQUUJUXSU
      UEYSUXOUVEUULUXPUUFUXRUUJUUGUUHYPYT $.
  $}

  ${
    $d A r $.  $d B r $.  $d N k $.  $d k ph $.  $d R r $.
    aks4d1p6.1 $e |- ( ph -> N e. ( ZZ>= ` 3 ) ) $.
    aks4d1p6.2 $e |- A = ( ( N ^ ( |_ ` ( 2 logb B ) ) ) x. prod_ k e.
     ( 1 ... ( |_ ` ( ( 2 logb N ) ^ 2 ) ) ) ( ( N ^ k ) - 1 ) ) $.
    aks4d1p6.3 $e |- B = ( |^ ` ( ( 2 logb N ) ^ 5 ) ) $.
    aks4d1p6.4 $e |- R = inf ( { r e. ( 1 ... B ) | -. r || A } , RR , < ) $.
    aks4d1p6.5 $e |- ( ph -> P e. Prime ) $.
    aks4d1p6.6 $e |- ( ph -> P || R ) $.
    aks4d1p6.7 $e |- K = ( P pCnt R ) $.
    $( The maximal prime power exponent is smaller than the binary logarithm
       floor of ` B ` .  (Contributed by metakunt, 30-Oct-2024.) $)
    aks4d1p6 $p |- ( ph -> K <_ ( |_ ` ( 2 logb B ) ) ) $=
      ( c2 cle wbr wcel clogb co cfl cfv cpc cn0 wceq a1i c1 cfz cdvds aks4d1p4
      cn wn simpld elfznn pccld eqeltrd nn0zd zred cprime prmnn nnred nngt0d cz
      syl cc0 clt wa c5 cexp cceil cr 2re 2pos cuz eluzelz 0red 3re 3pos eluzle
      c3 ltletrd 1red 1lt2 ltned necomd relogbcld 5nn0 reexpcld ceilcl 9re 9pos
      c9 3lexlogpow5ineq4 lttrd ceilge breqtrrd jca elnnz sylibr 2z prmuz2 ccxp
      nnrpd rpne0d cxpexpzd oveq2d pcdvds syl2anc wi nnzd zexpcl dvdsle eqbrtrd
      rpcnd mpd elfzle2 letrd cc cpr cdif csn nelprd eldifd recnd neneqd mtbird
      elsng cxplogb rpred cxpled clog cdiv rplogcld crp mpbid relogbval eqcomd
      wb mpbird relogcld nnge1d logge0d 2rp logled lediv2ad uzidd 3brtr3d flge
      ) AGQCUAUBZRSZGUUKUCUDRSZAGDCUAUBZUUKAGAGAGDEUEUBZUFGUUOUGAPUHZADENAEUICU
      JUBTZEUMTZAUUQEBUKSUNABCEFHIJKLMULUOZECUPVFZUQZURZUSZUTZADCADADVATZDUMTND
      VBVFZVCZADUVFVDACACVETZVGCVHSZVICUMTZAUVHUVIACQHUAUBZVJVKUBZVLUDZVECUVMUG
      ALUHZAUVLVMTZUVMVETAUVKVJAQHQVMTAVNUHZVGQVHSAVOUHZAHAHWBVPUDTZHVETJWBHVQV
      FUTZAVGWBHAVRZWBVMTAVSUHUVSVGWBVHSAVTUHAUVRWBHRSJWBHWAVFZWCAUIQAUIQAWDZUI
      QVHSAWEUHZWFWGZWHVJUFTAWIUHWJZUVLWKVFURZAVGUVLCUVTUWEACUWFUTAVGWNUVLUVTWN
      VMTAWLUHUWEVGWNVHSAWMUHAHUVSUWAWOWPAUVLUVMCRAUVOUVLUVMRSUWEUVLWQVFUVNWRWC
      WSCWTXAZVCZACUWGVDZAUIDAUIDUWBAUIQDUWBAQQVETAXBUHZUTZUVGUWCADQVPUDZTZQDRS
      ZAUVEUWMNDXCVFZQDWAVFZWCWFWGZWHZAQCUWKUVQUWHUWIUWDWHZAGUUNRSDGXDUBZDUUNXD
      UBZRSAUWTDGVKUBZUXARADGADADUVFXEZXPZADUXCXFZUVCXGAUXBCUXARAUXBECADGUVGUVB
      WJAEUUTVCUWHAUXBDUUOVKUBZERAGUUODVKUUPXHAUXFEUKSZUXFERSZAUVEUURUXGNUUTDEX
      IXJAUXFVETZUURUXGUXHXKADVETUUOUFTUXIADUVFXLUVADUUOXMXJUUTUXFEXNXJXQXOAUUQ
      ECRSUUSEUICXRVFXSADXTVGUIYAZYBTCXTVGYCZYBTUXACUGADXTUXJUXDADVGUIUXEUWQYDY
      EACXTUXKACUWHYFACUXKTZCVGUGZACVGAVGCAVGCUVTUWIWFWGYGAUVJUXLUXMYTUWGCVGUMY
      IVFYHYEDCYJXJWRXOADGUUNADUXCYKZAUIQDUWBUWKUXNUWCUWPWCZUVDUWRYLUUAACYMUDZD
      YMUDZYNUBZUXPQYMUDZYNUBZUUNUUKRAUXSUXQUXPAQUVPUWCYOADUXNUXOYOACACUWGXEZUU
      BACUWHACUWGUUCUUDAUWNUXSUXQRSUWPAQDQYPTAUUEUHUXCUUFYQUUGAUUNUXRAUWMCYPTZU
      UNUXRUGUWOUYADCYRXJYSAUUKUXTAQUWLTUYBUUKUXTUGAQUWJUUHUYAQCYRXJYSUUIXSAUUK
      VMTGVETUULUUMYTUWSUVCUUKGUUJXJYQ $.
  $}

  ${
    $d A r $.  $d B p $.  $d B r $.  $d N k p $.  $d R k p $.  $d R r $.
    $d k p ph $.
    aks4d1p7d1.1 $e |- ( ph -> N e. ( ZZ>= ` 3 ) ) $.
    aks4d1p7d1.2 $e |- A = ( ( N ^ ( |_ ` ( 2 logb B ) ) ) x. prod_ k e.
     ( 1 ... ( |_ ` ( ( 2 logb N ) ^ 2 ) ) ) ( ( N ^ k ) - 1 ) ) $.
    aks4d1p7d1.3 $e |- B = ( |^ ` ( ( 2 logb N ) ^ 5 ) ) $.
    aks4d1p7d1.4 $e |- R = inf ( { r e. ( 1 ... B ) | -. r || A } , RR , < ) $.
    aks4d1p7d1.5 $e |- ( ph -> A. p e. Prime ( p || R -> p || N ) ) $.
    $( Technical step in AKS lemma 4.1.  (Contributed by metakunt,
       31-Oct-2024.) $)
    aks4d1p7d1 $p |- ( ph -> R || ( N ^ ( |_ ` ( 2 logb B ) ) ) ) $=
      ( c2 co wbr wcel c1 cc0 adantr clogb cfl cfv cexp cdvds cv cpc cle cprime
      wral wa cn0 w3a simp2 cn cfz wn aks4d1p4 simpld elfznn syl 3ad2ant1 pccld
      3expa nn0red cr 2re a1i clt 2pos c5 cceil wceq cz c3 cuz eluzelz zred 3re
      0red 3pos eluzle ltletrd 1red 1lt2 ltned necomd relogbcld reexpcld ceilcl
      5nn0 eqeltrd c9 9re 3lexlogpow5ineq4 lttrd ceilge breqtrrd flcld ad2antrr
      9pos simplr jca elnnz sylibr caddc 1cnd addlidd wne recnd logbid1 syl3anc
      cc gtned eqcomd eqtrd 2z leidd 2lt9 ltled letrd logblebd eqbrtrd peano2zd
      wb flge syl2anc mpbid zltp1led mpbird nnnn0d nnexpcld simp3 eqid aks4d1p6
      0zd cmul wi rsp imp pcelnn nnge1 lemulge11d cq nnne0d pcexp simpr nn0ge0d
      zq pceq0 pm2.61dan ralrimiva elfzelzd zexpcld pc2dvds ) ADFNCUAOZUBUCZUDO
      ZUEPZHUFZDUGOZUUTUURUGOZUHPZHUIUJZAUVCHUIAUUTUIQZUKZUUTDUEPZUVCUVFUVGUKZU
      VAUUQUVBUVHUVAAUVEUVGUVAULQAUVEUVGUMZUUTDAUVEUVGUNZAUVEDUOQZUVGADRCUPOQZU
      VKAUVLDBUEPUQABCDEFGIJKLURUSZDCUTVAZVBVCVDVEAUUQVFQUVEUVGAUUQAUUPANCNVFQA
      VGVHZSNVIPAVJVHZACNFUAOZVKUDOZVLUCZVFCUVSVMAKVHZAUVSAUVRVFQZUVSVNQAUVQVKA
      NFUVOUVPAFAFVOVPUCQZFVNQZIVOFVQVAZVRZASVOFAVTZVOVFQAVSVHUWESVOVIPAWAVHAUW
      BVOFUHPIVOFWBVAZWCZARNARNAWDRNVIPAWEVHWFWGZWHVKULQAWKVHWIZUVRWJVAVRZWLZAS
      UVSCVIASUVRUVSUWFUWJUWKASWMUVRUWFWMVFQAWNVHZUWJSWMVIPAXAVHAFUWEUWGWOZWPAU
      WAUVRUVSUHPUWJUVRWQVAZWCUVTWRZUWIWHZWSZVRZWTZUVHUVBUVHUUTUURAUVEUVGXBZUVH
      FUUQAFUOQZUVEUVGAUWCSFVIPZUKUXBAUWCUXCUWDUWHXCFXDXEZWTZAUUQULQZUVEUVGAUUQ
      AUUQVNQZSUUQVIPZUKUUQUOQAUXGUXHUWRAUXHSRXFOZUUQUHPZAUXIUUPUHPZUXJAUXINNUA
      OZUUPUHAUXIRUXLARAXGXHAUXLRANXMQNSXINRXIUXLRVMANUVOXJASNUWFUVPXNUWINXKXLX
      OXPANNCNVNQAXQVHANUVOXRUVOUVPUWLUWPANWMCUVOUWMUWLANWMUVOUWMNWMVIPAXSVHXTA
      WMCUWMUWLAWMUVSCVIAWMUVRUVSUWMUWJUWKUWNUWOWCUVTWRXTYAYBYCAUUPVFQUXIVNQUXK
      UXJYEUWQASAYPZYDUUPUXIYFYGYHASUUQUXMUWRYIYJZXCUUQXDXEYKZWTYLVCVEAUVEUVGUV
      AUUQUHPUVIBCUUTDEUVAFGAUVEUWBUVGIVBJKLUVJAUVEUVGYMUVAYNYOVDUVHUUQUUQUUTFU
      GOZYQOZUVBUHUVHUUQUXPUWTUVHUXPUVHUUTFUXAUXEVCVEUVFSUUQUHPZUVGAUXRUVEASUUQ
      UWFUWSUXNXTTTUVHUXPUOQZRUXPUHPUVHUXSUUTFUEPZUVFUVGUXTAUVEUVGUXTYRZAUYAHUI
      UJUVEUYAYRMUYAHUIYSVAYTYTUVHUVEUXBUXSUXTYEUXAUVFUXBUVGAUXBUVEUXDTZTUUTFUU
      AYGYJUXPUUBVAUUCUVHUVEFUUDQZFSXIZUKZUXGUVBUXQVMUXAUVFUYEUVGAUYEUVEAUYCUYD
      AUWCUYCUWDFUUIVAAFUXDUUEXCTTUVFUXGUVGAUXGUVEUWRTTFUUTUUQUUFXLWRYAUVFUVGUQ
      ZUKZUVASUVBUHUYGUVASVMZUYFUVFUYFUUGUYGUVEUVKUYHUYFYEAUVEUYFXBZUVFUVKUYFAU
      VKUVEUVNTTUUTDUUJYGYJUYGUVBUYGUUTUURUYIUYGFUUQUVFUXBUYFUYBTUVFUXFUYFAUXFU
      VEUXOTTYLVCUUHYCUUKUULADVNQUURVNQUUSUVDYEADRCUVMUUMAFUUQUWDUXOUUNDUURHUUO
      YGYJ $.
  $}

  ${
    $d A r $.  $d B o $.  $d B q $.  $d B r $.  $d N k p q $.  $d R k p q $.
    $d R r $.  $d k ph q $.  $d o ph $.
    aks4d1p7.1 $e |- ( ph -> N e. ( ZZ>= ` 3 ) ) $.
    aks4d1p7.2 $e |- A = ( ( N ^ ( |_ ` ( 2 logb B ) ) ) x. prod_ k e.
     ( 1 ... ( |_ ` ( ( 2 logb N ) ^ 2 ) ) ) ( ( N ^ k ) - 1 ) ) $.
    aks4d1p7.3 $e |- B = ( |^ ` ( ( 2 logb N ) ^ 5 ) ) $.
    aks4d1p7.4 $e |- R = inf ( { r e. ( 1 ... B ) | -. r || A } , RR , < ) $.
    $( Technical step in AKS lemma 4.1.  (Contributed by metakunt,
       31-Oct-2024.) $)
    aks4d1p7 $p |- ( ph -> E. p e. Prime ( p || R /\ -. p || N ) ) $=
      ( cdvds wbr c2 wcel c1 cr a1i cc0 vq vo cv wn wa cprime wral wi clogb cfl
      wrex co cfv cexp cuz adantr wceq breq1 imbi12d cbvralvw bilani aks4d1p7d1
      c3 cfz crab clt cinf wor cfn wne wss w3a ltso fzfid ssrab2 ssfid aks4d1p3
      c0 rabn0 sylibr cn elfznn adantl nnred ssrdv 3jca fiinfcl syl2anc eqeltrd
      ex sstrd notbid elrab sylib simprd cmin cprod cz aks4d1p4 simpld elfzelzd
      cmul eluzelz syl cle cn0 2re 2pos cceil zred 0red 3re 3pos eluzle ltletrd
      c5 1red 1lt2 ltned necomd relogbcld reexpcld ceilcld 9re 3lexlogpow5ineq4
      5nn0 c9 9pos ceilged breqtrrd lttrd flcld syl3anc ltled wb zexpcld bicomi
      wo notnotb bitri cc recnd gtned logb1 eqcomd 2z leidd 0lt1 letrd logblebd
      1lt9 eqbrtrd 0zd flge mpbid jca elnn0z nnnn0d zsubcld fprodzcl dvdsmultr1
      1zzd breq2d mpbird con3d pm2.65da ianor orbi2i df-or imbi1i ralbii notbii
      imp mpd ralnex con2bii ) AHUCZDMNZUVQFMNZUDZUEZUDZHUFUGZUDZUWAHUFUKZAUVRU
      VSUHZHUFUGZUDUWDAUWGDFOCUIULZUJUMZUNULZMNZAUWGUEBCDEFGUAAFVCUOUMPZUWGIUPJ
      KLUWGUAUCZDMNZUWMFMNZUHZUAUFUGAUWFUWPHUAUFUVQUWMUQUVRUWNUVSUWOUVQUWMDMURU
      VQUWMFMURUSUTVAVBAUWKUDZUWGADBMNZUDZUWQADQCVDULZPZUWSADGUCZBMNZUDZGUWTVEZ
      PUXAUWSUEADUXERVFVGZUXEDUXFUQALSARVFVHZUXEVIPZUXEVRVJZUXERVKZVLUXFUXEPUXG
      AVMSAUXHUXIUXJAUWTUXEAQCVNUXEUWTVKAUXDGUWTVOSZVPAUXDGUWTUKUXIABCEFGIJKVQU
      XDGUWTVSVTAUXEUWTRUXKAUBUWTRAUBUCZUWTPZUXLRPAUXMUEUXLUXMUXLWAPAUXLCWBWCWD
      WJWEWKWFRUXEVFWGWHWIUXDUWSGDUWTUXBDUQUXCUWRUXBDBMURWLWMWNWOAUWKUWRAUWKUWR
      AUWKUEUWRDUWJQOFUIULZOUNULUJUMZVDULZFEUCZUNULZQWPULZEWQZXBULZMNZAUWKUYBAD
      WRPUWJWRPUXTWRPUWKUYBUHADQCAUXAUWSABCDEFGIJKLWSWTXAAFUWIAUWLFWRPZIVCFXCXD
      ZAUWIWRPZTUWIXENZUEUWIXFPAUYEUYFAUWHAOCORPAXGSZTOVFNAXHSZACUXNXPUNULZXIUM
      ZRCUYJUQAKSZAUYJAUYIAUXNXPAOFUYGUYHAFUYDXJZATVCFAXKZVCRPAXLSUYLTVCVFNAXMS
      AUWLVCFXENIVCFXNXDZXOAQOAQOAXQZQOVFNAXRSXSXTZYAXPXFPAYFSYBZYCXJZWIZATYGCU
      YMYGRPAYDSZUYSTYGVFNAYHSAYGUYJCVFAYGUYIUYJUYTUYQUYRAFUYLUYNYEAUYIUYQYIXOU
      YKYJZYKZUYPYAZYLATUWHXENZUYFATOQUIULZUWHXEAVUETAOUUAPOTVJOQVJVUETUQAOUYGU
      UBATOUYMUYHUUCUYPOUUDYMUUEAOQCOWRPAUUFSAOUYGUUGUYOTQVFNAUUHSUYSVUBAQYGCUY
      OUYTUYSAQYGUYOUYTQYGVFNAUUKSYNAYGCUYTUYSVUAYNUUIUUJUULAUWHRPTWRPVUDUYFYOV
      UCAUUMUWHTUUNWHUUOUUPUWIUUQVTYPAUXPUXSEAQUXOVNAUXQUXPPZUEZUXRQVUGFUXQAUYC
      VUFUYDUPVUGUXQVUFUXQWAPAUXQUXOWBWCUURYPVUGUVBUUSUUTDUWJUXTUVAYMUVMAUWRUYB
      YOUWKABUYADMBUYAUQAJSUVCUPUVDWJUVEUVNUPUVFUWCUWGUWBUWFHUFUWBUVRUDZUDZUVSU
      HZUWFUWBVUHUVSYRZVUJUWBVUHUVTUDZYRZVUKUVRUVTUVGVUKVUMUVSVULVUHUVSYSUVHYQY
      TVUHUVSUVIYTUWFVUJUVRVUIUVSUVRYSUVJYQYTUVKUVLVTUWEUWDUWCUWEUWAHUFUVOUVPYQ
      WN $.
  $}

  ${
    aks4d1p8d1.1 $e |- ( ph -> P e. Prime ) $.
    aks4d1p8d1.2 $e |- ( ph -> M e. NN ) $.
    aks4d1p8d1.3 $e |- ( ph -> N e. NN ) $.
    aks4d1p8d1.4 $e |- ( ph -> P || M ) $.
    aks4d1p8d1.5 $e |- ( ph -> -. P || N ) $.
    $( If a prime divides one number ` M ` , but not another number ` N ` ,
       then it divides the quotient of ` M ` and the gcd of ` M ` and ` N ` .
       (Contributed by Thierry Arnoux, 10-Nov-2024.) $)
    aks4d1p8d1 $p |- ( ph -> P || ( M / ( M gcd N ) ) ) $=
      ( cgcd co cmul cdvds wbr wcel cn nnzd syl2anc cz wa cdiv cprime prmnn syl
      gcdnncl wn c1 wceq intnand wb dvdsgcdb syl3anc mtbid coprm biimpa gcddvds
      syl21anc simpld coprmdvds2d nnproddivdvdsd mpbid ) ABCDJKZLKCMNBCVBUAKMNA
      BVBCABABUBOZBPOEBUCUDZQZAVBACPODPOVBPOFGCDUERZQZACFQZAVCVBSOZBVBMNZUFZBVB
      JKUGUHZEVGABCMNZBDMNZTZVJAVNVMIUIABSOCSOZDSOZVOVJUJVEVHADGQZBCDUKULUMVCVI
      TVKVLBVBUNUOUQHAVBCMNZVBDMNZAVPVQVSVTTVHVRCDUPRURUSABVBCVDVFFUTVA $.
  $}

  ${
    $d P p $.  $d Q p $.  $d R p $.  $d p ph $.
    aks4d1p8d2.1 $e |- ( ph -> R e. NN ) $.
    aks4d1p8d2.2 $e |- ( ph -> N e. NN ) $.
    aks4d1p8d2.3 $e |- ( ph -> P e. Prime ) $.
    aks4d1p8d2.4 $e |- ( ph -> Q e. Prime ) $.
    aks4d1p8d2.5 $e |- ( ph -> P || R ) $.
    aks4d1p8d2.6 $e |- ( ph -> Q || R ) $.
    aks4d1p8d2.7 $e |- ( ph -> -. P || N ) $.
    aks4d1p8d2.8 $e |- ( ph -> Q || N ) $.
    $( Any prime power dividing a positive integer is less than that integer if
       that integer has another prime factor.  (Contributed by metakunt,
       13-Nov-2024.) $)
    aks4d1p8d2 $p |- ( ph -> ( P ^ ( P pCnt R ) ) < R ) $=
      ( cpc co wcel c1 wbr cdvds wn vp cexp cmul cprime cn prmnn nnred reexpcld
      syl pccld remulcld clt recnd mulridd nnrpd nn0zd rpexpcld prmgt1 ltmul2dd
      1red eqbrtrrd cle nnzd zexpcld cgcd gcdcomd wceq cv wral wrex wa cc0 0lt1
      a1i 0red ltnled mpbid exp1d eqcomd oveq2d cz 1zzd syl2anc eqtrd adantr wb
      breq1 adantl bicomd biimpd mpd pm2.65da neqcomd pcelnn mpbird prmdvdsexpb
      syl3anc notbid nnexpcld pceq0 breq12d simpr oveq1d rspcime rexnal pc2dvds
      pcid coprm pcdvds coprmdvds2d wi zmulcld dvdsle ltletrd ) ABBDNOZUBOZXPCU
      COZDABXOABABUDPZBUEPHBUFUIZUGABDHFUJZUHZAXPCYAACACUDPZCUEPICUFUIZUGZUKADF
      UGAXPQUCOXPXQULAXPAXPYAUMUNAQCXPAUTZYDABXOABXSUOAXOXTUPUQAYBQCULRICURUIUS
      VAAXQDSRZXQDVBRZAXPCDABXOABXSVCXTVDZACYCVCZADFVCAXPCVEOCXPVEOZQAXPCYHYIVF
      ACXPSRZTZYJQVGZAYLUAVHZCNOZYNXPNOZVBRZUAUDVIZTZAYQTZUAUDVJZYSAYTUACUDAYNC
      VGZVKZYTCCNOZCXPNOZVBRZTZAUUGUUBAUUGQVLVBRZTZAVLQULRZUUIUUJAVMVNAVLQAVOYE
      VPVQAUUFUUHAUUDQUUEVLVBAUUDCCQUBOZNOZQACUUKCNAUUKCACACYDUMVRVSVTAYBQWAPUU
      LQVGIAWBQCXGWCWDAUUEVLVGZYLAYLCBVGZTABCABCVGZBESRZAUUOVKZCESRZUUPAUURUUOM
      WEUUQUURUUPUUQUUPUURUUOUUPUURWFABCESWGWHWIWJWKAUUPTUUOLWEWLWMAYKUUNAYBXRX
      OUEPZYKUUNWFIHAUUSBDSRZJAXRDUEPZUUSUUTWFHFBDWNWCWOCBXOWPWQWRWOAYBXPUEPUUM
      YLWFIABXOXSXTWSCXPWTWCWOXAWRWOWEUUCYQUUFUUCYOUUDYPUUEVBUUCYNCCNAUUBXBZXCU
      UCYNCXPNUVBXCXAWRWOIXDUUAYSWFAYQUAUDXEVNVQAYKYRACWAPXPWAPZYKYRWFYIYHCXPUA
      XFWCWRWOAYBUVCYLYMWFIYHCXPXHWCVQWDAXRUVAXPDSRHFBDXIWCKXJAXQWAPUVAYFYGXKAX
      PCYHYIXLFXQDXMWCWKXN $.
  $}

  ${
    aks4d1p8d3.1 $e |- ( ph -> N e. NN ) $.
    aks4d1p8d3.2 $e |- ( ph -> P e. Prime ) $.
    aks4d1p8d3.3 $e |- ( ph -> P || N ) $.
    $( The remainder of a division with its maximal prime power is coprime with
       that prime power.  (Contributed by metakunt, 13-Nov-2024.) $)
    aks4d1p8d3 $p |- ( ph ->
     ( ( N / ( P ^ ( P pCnt N ) ) ) gcd ( P ^ ( P pCnt N ) ) ) = 1 ) $=
      ( co cgcd c1 cdvds wbr cz wcel cn syl2anc cc0 wb syl nnzd clt cexp cprime
      cpc cdiv pcdvds prmnn pccld zexpcld zcnd 0red 1red zred 0lt1 prmgt1 lttrd
      wne a1i ltned necomd nn0zd expne0d dvdsval2 syl3anc mpbid gcdcomd wceq wn
      pcndvds2 coprm pcelnn mpbird rpexp eqtrd ) ACBBCUCGZUAGZUDGZVOHGVOVPHGZIA
      VPVOAVOCJKZVPLMZABUBMZCNMZVREDBCUEOAVOLMVOPUPCLMVRVSQABVNABAVTBNMEBUFRSZA
      BCEDUGZUHZABVNABWBUIAPBAPBAUJZAPIBWEAUKABWBULPITKAUMUQAVTIBTKEBUNRUOURUSA
      VNWCUTVAACDSVOCVBVCVDZWDVEAVQIVFZBVPHGIVFZABVPJKVGZWHAVTWAWIEDBCVHOAVTVSW
      IWHQEWFBVPVIOVDABLMVSVNNMZWGWHQWBWFAWJBCJKZFAVTWAWJWKQEDBCVJOVKBVPVNVLVCV
      KVM $.
  $}

  ${
    $d A p r y $.  $d A r x y $.  $d B o $.  $d B r x y $.  $d N k p $.
    $d N p r $.  $d R k p $.  $d R p r y $.  $d k p ph $.  $d o ph $.
    $d B f $.  $d N p q $.  $d R p q $.  $d f ph $.  $d ph q $.
    aks4d1p8.1 $e |- ( ph -> N e. ( ZZ>= ` 3 ) ) $.
    aks4d1p8.2 $e |- A = ( ( N ^ ( |_ ` ( 2 logb B ) ) ) x. prod_ k e.
     ( 1 ... ( |_ ` ( ( 2 logb N ) ^ 2 ) ) ) ( ( N ^ k ) - 1 ) ) $.
    aks4d1p8.3 $e |- B = ( |^ ` ( ( 2 logb N ) ^ 5 ) ) $.
    aks4d1p8.4 $e |- R = inf ( { r e. ( 1 ... B ) | -. r || A } , RR , < ) $.
    $( Show that ` N ` and ` R ` are coprime for AKS existence theorem, with
       eliminated hypothesis.  (Contributed by metakunt, 10-Nov-2024.)  (Proof
       sketch by Thierry Arnoux.) $)
    aks4d1p8 $p |- ( ph -> ( N gcd R ) = 1 ) $=
      ( c1 co clt wbr wcel cle adantr c2 cc0 vp vx vy vo vf vq cgcd wa cdvds wn
      cdiv cv cprime cfz crab cr cinf wceq a1i wss wral ssrab2 cn elfznn adantl
      nnred ex ssrdv sstrd cfn c0 wne fzfid ssfid aks4d1p3 rabn0 sylibr fiminre
      wrex syl3anc breq1 notbid 1zzd cz clogb c5 cexp cceil cfv c3 zred ltletrd
      syl 1red ltned necomd relogbcld cn0 ad4antr wb ad2antrr wi dvdsval2 mpbid
      nnzd cmul nncnd mullidd sylbir jca dvdsle syl2anc eqbrtrd nnrpd lemuldivd
      lttrd ltled letrd mpbird elfzd simplr zexpcld eqcomd cfl ad3antrrr simprl
      c9 recnd cc crp redivcld ltnled breq1d infrefilb 3expa mpd elrab3 con2bid
      con3d r19.29a 2re 2pos cuz eluzelz 0red 3re 3pos eluzle 1lt2 5nn0 ceilcld
      reexpcld eqeltrd simplrl prmnn nnne0d aks4d1p4 simpld anass anbi1i imbi1i
      mpbi imp remulcld elfzle2 9pos eqeltrrd 3lexlogpow5ineq4 ceilged breqtrrd
      9re nnge1d lemulge11d ledivmul2d anasss pccld zcnd nn0zd expne0d divcan1d
      cpc pcdvds cmin cprod elnnz flcld gtned logb1 2z leidd 0lt1 1lt9 logblebd
      0zd elnn0z nnnn0d zsubcld fprodzcl zmulcld eleq1d aks4d1p8d3 exp0d pcelnn
      flge nngt0d prmgt1 ltexp2d eqbrtrrd ltmulgt11d rpexpcld expge1d nnledivrp
      ltdivmul2d simprr simplrr simpr prmdvdsncoprmbd bicomd biimpd coprmdvds2d
      aks4d1p8d2 simprd ad5antr pm2.21dd lbinfle ltdiv2d div1d breqtrd pm2.65da
      elrabd 1rp aks4d1p7 aks4d1p5 ) ABCDEFGHIJKALFDUGMZNOZUHZDUYNUKMBUIOZUJZUY
      QUYPUAULZDUIOZUYSFUIOUJZUHZUYRUAUMUYPUYSUMPZUHZVUBUHZUYQDDUYSUKMZQOZVUEUY
      QUHZDGULZBUIOZUJZGLCUNMZUOZUPNUQZVUFQDVUNURZVUHKUSVUHVUMUPUTZUBULUCULQOUC
      VUMVAUBVUMVSZVUFVUMPVUNVUFQOVUEVUPUYQVUDVUPVUBUYPVUPVUCAVUPUYOAVUMVULUPVU
      MVULUTAVUKGVULVBUSZAUDVULUPAUDULZVULPZVUSUPPAVUTUHVUSVUTVUSVCPAVUSCVDVEVF
      VGVHVIZRRRRVUEVUQUYQVUDVUQVUBUYPVUQVUCAVUQUYOAVUPVUMVJPZVUMVKVLZVUQVVAAVU
      LVUMALCVMVURVNZAVUKGVULVSVVCABCEFGHIJVOVUKGVULVPVQUBUCVUMVRVTRRRRVUHVUKVU
      FBUIOZUJZGVUFVULVUIVUFURVUJVVEVUIVUFBUIWAWBVUHVUFLCVUHWCACWDPZUYOVUCVUBUY
      QACSFWEMZWFWGMZWHWIZWDCVVJURAJUSZAVVIAVVHWFASFSUPPAUUAUSZTSNOAUUBUSZAFAFW
      JUUCWIPZFWDPZHWJFUUDWMZWKZATWJFAUUEZWJUPPAUUFUSVVQTWJNOAUUGUSAVVNWJFQOHWJ
      FUUHWMZWLZALSALSAWNZLSNOAUUIUSWOWPZWQWFWRPAUUJUSUULZUUKUUMZWSVUHUYTVUFWDP
      ZVUDUYTVUAUYQUUNZVUHUYSWDPZUYSTVLZDWDPZUYTVWEWTVUHUYSVUDUYSVCPZVUBUYQVUCV
      WJUYPUYSUUOVEZXAZXEZVUDVWHVUBUYQVUDUYSVWKUUPZXAVUDUYTUHZVUAUHZUYQUHZVWIXB
      VUHVWIXBVWQDVWPDVCPZUYQAVWRUYOVUCUYTVUAADVULPZVWRAVWSDBUIOZUJZABCDEFGHIJK
      UUQZUURZDCVDWMZWSZRZXEVWQVUHVWIVWPVUEUYQVUDUYTVUAUUSZUUTZUVAUVBUYSDXCVTXD
      VUHLUYSXFMZDQOLVUFQOVUHVXIUYSDQVUHUYSVUHUYSVWLXGXHVUHVWGVWRUHZUYTUYSDQOZV
      UHVWGVWRVWMVUHVWQVWRVXHVXFXIXJVWFVXJUYTVXKUYSDXKUVCXLXMVUHLDUYSVUHWNVUEDU
      PPZUYQVUDVXLVUBUYPVXLVUCAVXLUYOADVXDVFZRRRZRZVUHUYSVWLXNZXOXDVUEVUFCQOZUY
      QVUDVXQVUBVUDVXQDCUYSXFMZQOVUDDCVXRAVXLUYOVUCVXMXAZVUDCAVVGUYOVUCVWDXAZWK
      ZVUDCUYSVYAVUDUYSVWKVFZUVDUYPDCQOZVUCAVYCUYOAVWSVYCVXCDLCUVEWMRRZVUDCUYSV
      YAVYBUYPTCQOZVUCAVYEUYOATCVVRACVWDWKZATYGCVVRYGUPPAUVKUSZVYFTYGNOAUVFUSAY
      GVVJCNAYGVVIVVJVYGVWCACVVJUPVVKVYFUVGAFVVQVVSUVHAVVIVWCUVIWLVVKUVJZXPZXQR
      RVUDUYSVWKUVLZUVMXRVUDDCUYSVXSVYAVUDUYSVWKXNZUVNXSRRXTVUHVWTVVFVUEVWTUYQV
      UEDDUYSUYSDUWAMZWGMZUKMZVYMXFMZBUIVUEVYODVUEDVYMVUEDVXNYHZVUEVYMVUEUYSVYL
      VUEUYSVUDVWJVUBVWKRZXEVUEUYSDUYPVUCVUBYAZVUDUYTVUAVWRVXEUVOZUVPZYBZUVQZVU
      EUYSVYLVUEUYSVYQXGZVUDVWHVUBVWNRVUEVYLVYTUVRZUVSZUVTYCVUEVYNVYMBVUEVYMDUI
      OZVYNWDPZVUEVUCVWRWUFVYRVYSUYSDUWBXLZVUEVYMWDPZVYMTVLVWIWUFWUGWTWUAWUEVUE
      DVYSXEVYMDXCVTXDZWUAABWDPZUYOVUCVUBAWUKFSCWEMZYDWIZWGMZLVVHSWGMYDWIZUNMZF
      EULZWGMZLUWCMZEUWDZXFMZWDPAWUNWUTAFWUMAFAFVCPZVVOTFNOZUHZAVVOWVCVVPVVTXJW
      VBWVDWTAFUWEUSXSZXEZAWUMWRPZWUMWDPZTWUMQOZUHZAWVHWVIAWULASCVVLVVMVYFVYIVW
      BWQZUWFATWULQOZWVIATSLWEMZWULQAWVMTASYIPSTVLSLVLWVMTURASVVLYHATSVVRVVMUWG
      VWBSUWHVTYCASLCSWDPAUWIUSASVVLUWJVWATLNOAUWKUSVYFVYIALCVWAVYFALYGCVWAVYGV
      YFLYGNOAUWLUSVYHXPXQUWMXMAWULUPPTWDPZWVLWVIWTWVKAUWNZWULTUXDXLXDXJWVGWVJW
      TAWUMUWOUSXSYBAWUPWUSEALWUOVMAWUQWUPPZUHZWURLWVQFWUQAVVOWVPWVFRWVQWUQWVPW
      UQVCPAWUQWUOVDVEUWPYBWVQWCUWQUWRUWSABWVAWDBWVAURAIUSUWTXSYEVUEUYSDVYSVYRV
      UDUYTVUAYFZUXAVUEVYNBUIOZVYNVUMPZUJZVUEVUNVYNQOZUJZWWAVUEDVYNQOZUJZWWCVUE
      VYNDNOZWWEVUEWWFDDVYMXFMNOZVUELVYMNOWWGVUEUYSTWGMZLVYMNVUEUYSWUCUXBVUETVY
      LNOWWHVYMNOVUEVYLVUEVYLVCPZUYTWVRVUEVUCVWRWWIUYTWTVYRVYSUYSDUXCXLXSUXEVUE
      UYSTVYLVUDUYSUPPVUBVYBRZAWVNUYOVUCVUBWVOYEWUDVUDLUYSNOZVUBVUCWWKUYPUYSUXF
      VERZUXGXDUXHVUEVYMDVUEVYMWUAWKZVUDDYJPZVUBUYPWWNVUCAWWNUYOADVXDXNRRRZUXIX
      DVUEDDVYMVXNVXNVUEUYSVYLVUDUYSYJPVUBVYKRWUDUXJZUXMXSVUEVYNDVUEDVYMVXNWWMW
      UEYKZVXNYLXDVUEWWDWWBVUEDVUNVYNQVUOVUEKUSZYMWBXDVUEVUPVVBWWCWWAXBVUDVUPVU
      BUYPVUPVUCAVUPUYOAVUMVULUPVURAUEVULUPAUEULZVULPZWWSUPPAWWTUHWWSWWTWWSVCPA
      WWSCVDVEVFVGVHVIRRRZVUDVVBVUBUYPVVBVUCAVVBUYOVVDRRRZVUPVVBUHZWVTWWBWXCWVT
      WWBVUPVVBWVTWWBVYNVUMYNYOVGYSXLYPVUEVYNVULPZWVSWWAWTVUEVYNLCVUEWCZVUDVVGV
      UBVXTRZWUJVUELVYMXFMZDQOLVYNQOVUEWXGVYMDQVUEVYMWUBXHVUEWUFVYMDQOZWUHVUEWU
      IVWRWUFWXHXBWUAVYSVYMDXKXLYPZXMVUELDVYMUYPLUPPZVUCVUBAWXJUYOVWARXAZVXNWWP
      XOXDVUEVYNDCWWQVXNVUDCUPPVUBVYARZVUELVYMQOZVYNDQOZVUEUYSVYLWWJVYTVUDLUYSQ
      OVUBVYJRUXKZVUEVWRVYMYJPWXMWXNWTVYSWWPDVYMUXLXLXDVUDVYCVUBVYDRZXRXTWXDWVT
      WVSVUKWVSUJGVYNVULVUIVYNURVUJWVSVUIVYNBUIWAWBYQYRWMXSVUEVYMBUIOZVYMVUMPZU
      JZVUEVUNVYMQOZUJZWXSVUEDVYMQOZUJZWYAVUEVYMDNOZWYCVUEUFULZFUIOZWYEDUIOZUHZ
      WYDUFUMVUEWYEUMPZUHZWYHUHUYSWYEDFVUEVWRWYIWYHVYSXAVUEWVBWYIWYHVUEVWPWVBVX
      GVWOWVBVUAVUDWVBUYTUYPWVBVUCAWVBUYOWVERRRRXIZXAVUEVUCWYIWYHVYRXAVUEWYIWYH
      YAVUEUYTWYIWYHWVRXAWYJWYFWYGUXNWYJVUAWYHVUDUYTVUAWYIUXORWYJWYFWYGYFUYAVUE
      UYNLVLZWYHUFUMVSZVUELUYNVUELUYNWXKUYPUYOVUCVUBAUYOUXPXAWOWPVUEWYLWYMVUEWY
      MWYLVUEFDUFWYKVYSUXQUXRUXSYPYTVUEVYMDWWMVXNYLXDVUEWYBWXTVUEDVUNVYMQWWRYMW
      BXDVUEVUPVVBWYAWXSXBWXAWXBWXCWXRWXTWXCWXRWXTVUPVVBWXRWXTVYMVUMYNYOVGYSXLY
      PVUEWXRWXQVUEVYMVULPWXRWXQUJZWTVUEVYMLCWXEWXFWUAWXOVUEVYMDCWWMVXNWXLWXIWX
      PXRXTVUKWYNGVYMVULVUIVYMURVUJWXQVUIVYMBUIWAWBYQWMYRXSUXTXMRVUHVWQVXAVXHAV
      XAUYOVUCUYTVUAUYQAVWSVXAVXBUYBUYCXIUYDUYJUBUCVUFVUMUYEVTXMVUHVUFDNOVUGUJV
      UHVUFDLUKMZDNVUHWWKVUFWYONOVUEWWKUYQWWLRVUHLUYSDLYJPVUHUYKUSVXPVUEWWNUYQW
      WORUYFXDVUHDVUEDYIPUYQVYPRUYGUYHVUHVUFDVUEVUFUPPZUYQVUDWYPVUBVUDDUYSVXSVY
      BVWNYKRRVXOYLXDUYIAVUBUAUMVSUYOABCDEFGUAHIJKUYLRYTRUYM $.
  $}

  ${
    $d A r $.  $d B r $.  $d N k x z $.  $d N r $.  $d R k x z $.  $d R r $.
    $d k ph x z $.
    aks4d1p9.1 $e |- ( ph -> N e. ( ZZ>= ` 3 ) ) $.
    aks4d1p9.2 $e |- A = ( ( N ^ ( |_ ` ( 2 logb B ) ) ) x. prod_ k e.
     ( 1 ... ( |_ ` ( ( 2 logb N ) ^ 2 ) ) ) ( ( N ^ k ) - 1 ) ) $.
    aks4d1p9.3 $e |- B = ( |^ ` ( ( 2 logb N ) ^ 5 ) ) $.
    aks4d1p9.4 $e |- R = inf ( { r e. ( 1 ... B ) | -. r || A } , RR , < ) $.
    $( Show that the order is bound by the squared binary logarithm.
       (Contributed by metakunt, 14-Nov-2024.) $)
    aks4d1p9 $p |- ( ph -> ( ( 2 logb N ) ^ 2 ) < ( ( odZ ` R ) ` N ) ) $=
      ( c2 co wbr cdvds wcel cz cc0 c1 adantr vx vz clogb cexp codz cfv clt cle
      wn wa cfl cr wb 2re a1i 2pos c3 cuz eluzelz syl zred 0red 3re 3pos eluzle
      ltletrd 1red 1lt2 ltned necomd relogbcld resqcld cn cgcd w3a cfz aks4d1p4
      wceq simpld elfznn aks4d1p8 3jca nnzd flge syl2anc biimpd imp wi cmin cn0
      odzcl nnnn0d zexpcld 1zzd zsubcld cv cprod cmul c9 aks4d1lem1 nnred flcld
      nngt0d cc wne 2cnd gtned logb1 2z leidd 0lt1 nnge1d logblebd eqbrtrrd 0zd
      mpbid jca elnn0z sylibr fzfid adantl zmulcld eleq1d mpbird iddvds odzdvds
      cmpt fveq2 breq1d wral ssidd fmpttd fprodfvdvdsd simpr elfzd eqidd oveq2d
      fprodzcl oveq1d fvmptd rspcdva breq12d dvdsmultr2d breqtrrd dvdstrd mpdan
      prodeq2dv ex simprd pm2.65da ltnled ) ALFUCMZLUDMZFDUEUFUFZUGNUUNUUMUHNZU
      IAUUODBONZAUUOUJZUUNUUMUKUFZUHNZUUPAUUOUUSAUUOUUSAUUMULPUUNQPZUUOUUSUMAUU
      LALFLULPAUNUOZRLUGNAUPUOZAFAFUQURUFPZFQPZHUQFUSUTZVAZARUQFAVBZUQULPAVCUOU
      VFRUQUGNAVDUOAUVCUQFUHNHUQFVEUTVFASLASLAVGZSLUGNAVHUOVIVJZVKZVLZAUUNADVMP
      ZUVDFDVNMSVRZVOZUUNVMPAUVLUVDUVMADSCVPMPZUVLAUVOUUPUIZABCDEFGHIJKVQZVSDCV
      TUTZUVEABCDEFGHIJKWAWBZFDWKUTZWCZUUMUUNWDWEWFWGUUQUUSUUPAUUSUUPWHUUOAUUSU
      UPAUUSUJZDFUUNUDMZSWIMZBADQPUUSADUVRWCTUWBUWCSUWBFUUNAUVDUUSUVETZAUUNWJPZ
      UUSAUUNUVTWLZTWMUWBWNZWOZABQPZUUSAUWJFLCUCMZUKUFZUDMZSUURVPMZFEWPZUDMZSWI
      MZEWQZWRMZQPAUWMUWRAFUWLUVEAUWLQPZRUWLUHNZUJUWLWJPZAUWTUXAAUWKALCUVAUVBAC
      ACVMPWSCUGNACFHJWTVSZXAZACUXCXCZUVIVKZXBARUWKUHNZUXAALSUCMZRUWKUHALXDPZLR
      XEZLSXEZVOUXHRVRAUXIUXJUXKAXFARLUVGUVBXGUVIWBLXHUTALSCLQPAXIUOALUVAXJUVHR
      SUGNAXKUOUXDUXEACUXCXLXMXNAUWKULPRQPUXGUXAUMUXFAXOUWKRWDWEXPXQUWLXRXSZWMA
      UWNUWQEASUURXTZAUWOUWNPZUJZUWPSUXOFUWOAUVDUXNUVETUXNUWOWJPAUXNUWOUWOUURVT
      ZWLYAWMUXOWNWOYRYBABUWSQBUWSVRZAIUOYCYDTADUWDONZUUSAUXRUUNUUNONZAUUTUXSUW
      AUUNYEUTAUVNUWFUXRUXSUMUVSUWGFUUNDYFWEYDTUWBUWDUWSBOUWBUWDUWMUWRUWIUWBFUW
      LUWEAUXBUUSUXLTWMUWBUWNUWQEUWBSUURXTUWBUXNUJZUWPSUXTFUWOUWBUVDUXNUWETUXTU
      WOUXNUWOVMPUWBUXPYAWLWMUXTWNWOZYRUWBUUNUAUWNFUAWPZUDMZSWIMZYGZUFZUWNUWOUY
      EUFZEWQZONZUWDUWRONUWBUBWPZUYEUFZUYHONZUYIUBUWNUUNUYJUUNVRUYKUYFUYHOUYJUU
      NUYEYHYIAUYLUBUWNYJUUSAUBUWNUWNEUYEUXMAUWNYKAUAUWNUYDQAUYBUWNPZUJZUYCSUYN
      FUYBAUVDUYMUVETUYNUYBUYMUYBVMPAUYBUURVTYAWLWMUYNWNWOYLYMTUWBUUNSUURUWHUWB
      UUMUWBUULAUULULPUUSUVJTVLXBAUUTUUSUWATASUUNUHNUUSAUUNUVTXLTAUUSYNYOZUUAUW
      BUYFUWDUYHUWROUWBUAUUNUYDUWDUWNUYEQUWBUYEYPUWBUYBUUNVRZUJZUYCUWCSWIUYQUYB
      UUNFUDUWBUYPYNYQYSUYOUWIYTUWBUWNUYGUWQEUXTUAUWOUYDUWQUWNUYEQUXTUYEYPUXTUY
      BUWOVRZUJZUYCUWPSWIUYSUYBUWOFUDUXTUYRYNYQYSUWBUXNYNUYAYTUUGUUBXPUUCUXQUWB
      IUOUUDUUEUUHTWGUUFAUVPUUOAUVOUVPUVQUUITUUJAUUMUUNUVKAUUNUVTXAUUKYD $.
  $}

  ${
    $d B a h $.  $d B h k $.  $d B h r $.  $d N a b c $.  $d N a b h $.
    $d N b c k $.  $d N c r $.  $d a ph $.  $d ph r $.
    aks4d1.1 $e |- ( ph -> N e. ( ZZ>= ` 3 ) ) $.
    aks4d1.2 $e |- B = ( |^ ` ( ( 2 logb N ) ^ 5 ) ) $.
    $( Lemma 4.1 from ~ https://www3.nd.edu/%7eandyp/notes/AKS.pdf , existence
       of a polynomially bounded number by the digit size of ` N ` that asserts
       the polynomial subspace that we need to search to guarantee that ` N `
       is prime.  Eventually we want to show that the polynomial searching
       space is bounded by degree ` B ` .  (Contributed by metakunt,
       14-Nov-2024.) $)
    aks4d1 $p |- ( ph -> E. r e. ( 1 ... B ) ( ( N gcd r ) = 1 /\
    ( ( 2 logb N ) ^ 2 ) < ( ( odZ ` r ) ` N ) ) ) $=
      ( vb va vk cv co c1 wceq cexp cfv clt wbr cmin cmul cdvds vh vc cgcd codz
      c2 clogb wa cfl cfz cprod wn crab cr cinf oveq2 oveq1d cbvprodv oveq2i id
      wcel a1i breq12d notbid cbvrabv infeq1i simpld adantl eqeq1d fveq2 fveq1d
      aks4d1p4 breq2d anbi12d aks4d1p8 aks4d1p9 jca rspcedvd ) ACDJZUCKZLMZUECU
      FKUENKZCVRUDOZOZPQZUGCUAJZCUEBUFKUHONKZLWAUHOUIKZCUBJZNKZLRKZUBUJZSKZTQZU
      KZUALBUIKZULZUMPUNZUCKZLMZWACWQUDOZOZPQZUGDWQWOAWQWOUTWQWFWGCGJZNKZLRKZGU
      JZSKZTQUKAXGBWQHCIEXFWGCHJZNKZLRKZHUJWFSWGXEXJGHXCXHMXDXILRXCXHCNUOUPUQUR
      ZFUMWPIJZXGTQZUKZIWOULPWNXNUAIWOWEXLMZWMXMXOWEXLWLXGTXOUSWLXGMXOWKXFWFSWG
      WJXEUBGWHXCMWIXDLRWHXCCNUOUPUQURVAVBVCVDVEZVKVFAVRWQMZUGZVTWSWDXBXRVSWRLX
      QVSWRMAVRWQCUCUOVGVHXRWCXAWAPXRCWBWTXQWBWTMAVRWQUDVIVGVJVLVMAWSXBAXGBWQHC
      IEXKFXPVNAXGBWQHCIEXKFXPVOVPVQ $.
  $}

  ${
    $d A a b $.  $d F a b $.  $d a b ph $.
    fldhmf1.1 $e |- ( ph -> K e. Field ) $.
    fldhmf1.2 $e |- ( ph -> L e. Field ) $.
    fldhmf1.3 $e |- ( ph -> F e. ( K RingHom L ) ) $.
    fldhmf1.4 $e |- A = ( Base ` K ) $.
    fldhmf1.5 $e |- B = ( Base ` L ) $.
    $( A field homomorphism is injective.  This follows immediately from the
       definition of the ring homomorphism that sends the multiplicative
       identity to the multiplicative identity.  (Contributed by metakunt,
       7-Jan-2025.) $)
    fldhmf1 $p |- ( ph -> F : A -1-1-> B ) $=
      ( wne cfv wa co wcel syl wceq eqid syl2anc va vb wf wral wf1 crh rhmf c0g
      cv wi cur cminusg cplusg cinvr cmulr cghm ad4antr rhmghm simp-4r cgrp cdr
      cfield isfld simpld drnggrp simpllr grpinvcl ghmlin syl3anc ghminv oveq2d
      ccrg sylib simpr oveq1d crg ad3antrrr drngring ringgrpd ffvelcdmd grprinv
      adantr eqtrd grpcl grpinvinv simplr necomd eqnetrd wb grpinvid2 necon3bid
      cui w3a jca drngunit mpbird rhmunitinv elrhmunit unitinvcl biimpd eqeltrd
      mpd ringlz eqcomd simprd crngringd unitcl eqcomi eleqtrdi rhmmul unitrinv
      cbs fveq2d rhm1 3eqtrd drngunz neneqd pm2.65da neqned ex ralrimiva dff14a
      mpbid sylibr ) ABCDUCZUAUIZUBUIZLZYFDMZYGDMZLZUJZUBBUDZUABUDZNBCDUEAYEYNA
      DEFUFOPZYEIBCEFDJKUGZQAYMUABAYFBPZNZYLUBBYRYGBPZNZYHYKYTYHNZYIYJUUAYIYJRZ
      FUHMZFUKMZRUUAUUBNZUUCYFYGEULMZMZEUMMZOZDMZUUIEUNMZMZDMZFUOMZOZUUIUULEUOM
      ZOZDMZUUDUUEUUOUUCUUEUUOUUCUUMUUNOZUUCUUEUUJUUCUUMUUNUUEUUJYIUUGDMZFUMMZO
      ZUUCUUEDEFUPOPZYQUUGBPZUUJUVBRUUEYOUVCAYOYQYSYHUUBIUQZEFDURQZAYQYSYHUUBUS
      ZUUEEUTPZYSUVDUUEEVAPZUVHAUVIYQYSYHUUBAUVIEVLPZAEVBPUVIUVJNGEVCVMZVDUQZEV
      EQZYRYSYHUUBVFZBEUUFYGJUUFSZVGTZUUHUVAEFYFDUUGBJUUHSZUVASZVHVIUUEUVBYIYJF
      ULMZMZUVAOZUUCUUEUUTUVTYIUVAUUEUVCYSUUTUVTRUVFUVNBEFDUUFUVSYGJUVOUVSSZVJT
      VKUUEUWAYJUVTUVAOZUUCUUEYIYJUVTUVAUUAUUBVNVOUUEFUTPYJCPUWCUUCRUUEFUUEFVAP
      ZFVPPZUUAUWDUUBUUAUWDFVLPZUUAFVBPZUWDUWFNAUWGYQYSYHHVQFVCVMVDZWBZFVRQZVSU
      UEBCYGDUUEYOYEUVEYPQUVNVTCUVAFUVSYJUUCKUVRUUCSZUWBWATWCWCWCVOUUEUWEUUMCPZ
      NUUSUUCRUUEUWEUWLUWJUUEUUMUUJFUNMZMZCUUEYOUUIEWLMZPZUUMUWNRUVEUUEUWPUUIBP
      ZUUIEUHMZLZNZUUEUWQUWSUUEUVHYQUVDUWQUVMUVGUVPBUUHEYFUUGJUVQWDVIZUUEUUGUUF
      MZYFLZUWSUUEUXBYGYFUUEUVHYSUXBYGRUVMUVNBEUUFYGJUVOWETUUEYFYGYTYHUUBWFWGWH
      UUEUVHUVDYQUXCUWSWIUVMUVPUVGUVHUVDYQWMUXBYFUUIUWRBUUHEUUFUUGYFUWRJUVQUWRS
      ZUVOWJWKVIYCWNUUEUVIUWPUWTWIUVLBEUWOUUIUWRJUWOSZUXDWOQWPZUUIEFDWQTUUEUWNC
      PZUWNUUCLZUUEUWNFWLMZPZUXGUXHNZUUEUWEUUJUXIPZUXJUWJUUEYOUWPUXLUVEUXFUUIEF
      DWRTFUXIUWMUUJUXISZUWMSWSTUUEUXJUXKUUEUWDUXJUXKWIUWICFUXIUWNUUCKUXMUWKWOQ
      WTXBVDXAWNCFUUNUUMUUCKUUNSZUWKXCQWCXDUUEUURUUOUUEYOUWQUULBPZUURUUORUVEUXA
      UUEUULUWOPZUXOUUEEVPPZUWPUXPAUXQYQYSYHUUBAEAUVIUVJUVKXEXFUQUXFEUWOUUKUUIU
      XEUUKSZWSTUXPUULEXLMZBUXSEUWOUULUXSSUXEXGBUXSJXHXIQUUIUULEFUUPUUNDBJUUPSZ
      UXNXJVIXDUUEUUREUKMZDMZUUDUUEUUQUYADUUEUXQUWPUUQUYARUUEUVIUXQUVLEVRQUXFEU
      UPUWOUYAUUKUUIUXEUXRUXTUYASZXKTXMUUEYOUYBUUDRUVEEFUYADUUDUYCUUDSZXNQWCXOU
      UEUUCUUDUUAUUCUUDLUUBUUAUUDUUCUUAUWDUUDUUCLUWHFUUDUUCUWKUYDXPQWGWBXQXRXSX
      TYAYAWNUAUBBCDYBYD $.
  $}

  $c PrimRoots $.
  $( Define the class of primitive roots.  (Contributed by metakunt,
     25-Apr-2025.) $)
  cprimroots $a class PrimRoots $.

  ${
    $d a b k l r $.
    $( A ` r ` -th primitive root is a root of unity such that the exponent
       divides ` r ` .  (Contributed by metakunt, 25-Apr-2025.) $)
    df-primroots $a |- PrimRoots = ( r e. CMnd , k e. NN0 |->
    [_ ( Base ` r ) / b ]_ { a e. b | ( ( k ( .g ` r ) a ) = ( 0g ` r ) /\
    A. l e. NN0 ( ( l ( .g ` r ) a ) = ( 0g ` r ) -> k || l ) ) } ) $.
  $}

  ${
    $d K b k l r x $.  $d M l x $.  $d R b k l r x $.  $d b k l ph r x $.
    isprimroot.1 $e |- ( ph -> R e. CMnd ) $.
    isprimroot.2 $e |- ( ph -> K e. NN0 ) $.
    isprimroot.3 $e |- .^ = ( .g ` R ) $.
    $( The value of a primitive root.  (Contributed by metakunt,
       25-Apr-2025.) $)
    isprimroot $p |- ( ph -> ( M e. ( R PrimRoots K ) <->
    ( M e. ( Base ` R ) /\ ( K .^ M ) = ( 0g ` R ) /\
    A. l e. NN0 ( ( l .^ M ) = ( 0g ` R ) -> K || l ) ) ) ) $=
      ( vx vb vr co wcel cv cfv wceq cn0 wa cvv vk cprimroots cmg c0g cdvds wbr
      wi wral cbs crab w3a csb ccmn cmpo df-primroots a1i simprl fveq2d simplrl
      simplrr oveq123d eqeq12d oveqdr breq1d imbi12d ralbidv rabbidva csbeq12dv
      eqidd anbi12d eqid fvexd rabexd simpr rabeqdv csbied eleq1d mpbird ovmpod
      eqtrd eleq2d wb oveq2 eqeq1d imbi1d elrab 3anass bicomi biidd oveqd bitrd
      eqcomi 3anbi123d ) AEBDUBMZNEDJOZBUCPZMZBUDPZQZFOZWOWPMZWRQZDWTUEUFZUGZFR
      UHZSZJBUIPZUJZNZEXGNZDECMZWRQZWTECMZWRQZXCUGZFRUHZUKZAWNXHEAWNKXGXFJKOZUJ
      ZULZXHALUABDUMRKLOZUIPZUAOZWOYAUCPZMZYAUDPZQZWTWOYDMZYFQZYCWTUEUFZUGZFRUH
      ZSZJXRUJZULZXTUBTUBLUAUMRYOUNQAUALJKFUOUPAYABQZYCDQZSSZKYBYNXGXSYRYABUIAY
      PYQUQZURYRYMXFJXRYRWOXRNZSZYGWSYLXEUUAYEWQYFWRUUAYCDWOWOYDWPUUAYABUCAYPYQ
      YTUSZURAYPYQYTUTZUUAWOVIVAUUAYABUDUUBURZVBUUAYKXDFRUUAYIXBYJXCUUAYHXAYFWR
      YRYTFJYDWPYRYABUCYSURVCUUDVBUUAYCDWTUEUUCVDVEVFVJVGVHGHAXTTNXHTNAXFJXGXHT
      XHVKABUIVLZVMAXTXHTAKXGXSXHTUUEAXRXGQZSXFJXRXGAUUFVNVOVPZVQVRVSUUGVTWAAXI
      XJDEWPMZWRQZWTEWPMZWRQZXCUGZFRUHZSZSZXQXIUUOWBAXFUUNJEXGWOEQZWSUUIXEUUMUU
      PWQUUHWRWOEDWPWCWDUUPXDUULFRUUPXBUUKXCUUPXAUUJWRWOEWTWPWCWDWEVFVJWFUPAUUO
      XJUUIUUMUKZXQUUOUUQWBAUUQUUOXJUUIUUMWGWHUPAXJXJUUIXLUUMXPAXJWIAUUHXKWRAWP
      CDEWPCQACWPIWLUPZWJWDAUULXOFRAUUKXNXCAUUJXMWRAWPCWTEUURWJWDWEVFWMWKWKWK
      $.
  $}

  ${
    $d K l $.  $d M l $.  $d R l $.  $d l ph $.
    isprimroot2.1 $e |- ( ph -> R e. CMnd ) $.
    isprimroot2.2 $e |- ( ph -> K e. NN ) $.
    isprimroot2.3 $e |- ( ph -> M e. ( Base ` R ) ) $.
    isprimroot2.4 $e |- ( ph -> ( ( od ` R ) ` M ) = K ) $.
    $( Alternative way of creating primitive roots.  (Contributed by metakunt,
       14-Jul-2025.) $)
    isprimroot2 $p |- ( ph -> M e. ( R PrimRoots K ) ) $=
      ( vl co wcel cfv wceq cdvds wbr cn0 eqcomd eqid wa adantr cprimroots wral
      cbs cmg c0g cv wi w3a cod oveq1d odid syl eqtrd ad2antrr wb cmnmndd simpr
      cmnd oddvdsnn0 syl3anc bicomd biimpd imp eqbrtrd ex ralrimiva 3jca nnnn0d
      isprimroot mpbird ) ADBCUAJKDBUCLZKZCDBUDLZJZBUELZMZIUFZDVMJVOMZCVQNOZUGZ
      IPUBZUHAVLVPWAGAVNDBUILZLZDVMJZVOACWCDVMAWCCHQUJAVLWDVOMGDVMBWBVKVOVKRZWB
      RZVMRZVORZUKULUMAVTIPAVQPKZSZVRVSWJVRSZCWCVQNWKWCCAWCCMWIVRHUNQWJVRWCVQNO
      ZWJVRWLWJWLVRWJBURKZVLWIWLVRUOAWMWIABEUPTAVLWIGTAWIUQDVMBVQWBVKVOWEWFWGWH
      USUTVAVBVCVDVEVFVGABVMCDIEACFVHWGVIVJ $.
  $}

  ${
    $d A x y $.  $d B x y $.  $d M x y $.  $d ph x y $.
    mndmolinv.1 $e |- B = ( Base ` M ) $.
    mndmolinv.2 $e |- ( ph -> M e. Mnd ) $.
    mndmolinv.3 $e |- ( ph -> A e. B ) $.
    mndmolinv.4 $e |- ( ph -> E. x e. B ( A ( +g ` M ) x ) = ( 0g ` M ) ) $.
    $( An element of a monoid that has a right inverse has at most one left
       inverse.  (Contributed by metakunt, 25-Apr-2025.) $)
    mndmolinv $p |- ( ph -> E* x e. B ( x ( +g ` M ) A ) = ( 0g ` M ) ) $=
      ( vy cv cfv co wceq wrex nfv wcel wa syl2anc eqcomd cplusg c0g wral oveq2
      wi wrmo eqeq1d cbvrexw biimpi syl cmnd ad4antr simplr eqid mndrid simpllr
      oveq2d eqtrd w3a simp-4r 3jca mndass simpr oveq1d mndlid 3eqtrd ralrimiva
      ex reximdva mpd rmo2i ) ABKZCEUALZMZEUBLZNZVLJKZNZUEZBDUCZJDOZVPBDUFACVQV
      MMZVONZJDOZWAACVLVMMZVONZBDOZWDIWGWDWFWCBJDWFJPWCBPVRWEWBVOVLVQCVMUDUGUHU
      IUJAWCVTJDAVQDQZRZWCVTWIWCRZVSBDWJVLDQZRZVPVRWLVPRZVLVLWBVMMZVNVQVMMZVQWM
      VLVLVOVMMZWNWMWPVLWMEUKQZWKWPVLNAWQWHWCWKVPGULZWJWKVPUMZDVMEVLVOFVMUNZVOU
      NZUOSTWMVOWBVLVMWMWBVOWIWCWKVPUPTUQURWMWOWNWMWQWKCDQZWHUSWOWNNWRWMWKXBWHW
      SAXBWHWCWKVPHULAWHWCWKVPUTZVADVMEVLCVQFWTVBSTWMWOVOVQVMMZVQWMVNVOVQVMWLVP
      VCVDWMWQWHXDVQNWRXCDVMEVQVOFWTXAVESURVFVHVGVHVIVJVPBJDVPJPVKUJ $.
  $}

  ${
    $d R i $.  $d X i $.
    linvh.1 $e |- ( ph -> X e. ( Base ` R ) ) $.
    linvh.2 $e |- ( ph -> E! i e. ( Base ` R )
     ( i ( +g ` R ) X ) = ( 0g ` R ) ) $.
    $( If an element has a unique left inverse, then the value satisfies the
       left inverse value equation.  (Contributed by metakunt, 25-Apr-2025.) $)
    linvh $p |- ( ph -> ( ( ( invg ` R ) ` X ) ( +g ` R ) X ) = ( 0g ` R ) ) $=
      ( cminusg cfv cv cplusg co c0g wceq cbs crab wcel crio eqid grpinvval syl
      wreu riotacl2 eqeltrd oveq1 eqeq1d elrab simprbi ) ADBGHZHZCIZDBJHZKZBLHZ
      MZCBNHZOZPZUIDUKKZUMMZAUIUNCUOQZUPADUOPUIUTMECUOUKBUHDUMUORUKRUMRUHRSTAUN
      CUOUAUTUPPFUNCUOUBTUCUQUIUOPUSUNUSCUIUOUJUIMULURUMUJUIDUKUDUEUFUGT $.
  $}

  ${
    $d K c i $.  $d K c l $.  $d R a b d i $.  $d R a c i $.  $d R a i j q $.
    $d R c l $.  $d R i q w $.  $d U b d i $.  $d U c i $.  $d U i j q $.
    $d U c l $.  $d U i q w $.  $d b d i ph $.  $d c i ph $.  $d j ph q $.
    $d l ph $.  $d ph q w $.
    primrootsunit1.1 $e |- ( ph -> R e. CMnd ) $.
    primrootsunit1.2 $e |- ( ph -> K e. NN ) $.
    primrootsunit1.3 $e |- U = { a e. ( Base ` R ) |
     E. i e. ( Base ` R ) ( i ( +g ` R ) a ) = ( 0g ` R ) } $.
    $( Primitive roots have left inverses.  (Contributed by metakunt,
       25-Apr-2025.) $)
    primrootsunit1 $p |- ( ph -> ( ( R PrimRoots K ) =
     ( ( R |`s U ) PrimRoots K ) /\ ( R |`s U ) e. Abel ) ) $=
      ( co wceq wcel wa cfv wrex adantr syl syl3anc jca mpbird vc vl cprimroots
      vb vd vw vq vj cress cabl cv cbs cmg c0g cdvds wbr wi cn0 wral w3a cplusg
      crab ccmn nnnn0d eqid isprimroot biimpd syldbl2 simp1d c1 cmin cmnmndd cn
      cmnd nnm1nn0 mulgnn0cl simpr oveq1d eqeq1d caddc nncnd 1cnd npcand eqcomd
      mulgnn0p1 eqtr2d simp2d eqtrd oveq2 rexbidv elrab sylibr eleq2i wss simpl
      rspcedvd a1i eleq2d imp elrabi adantl ssrdv ressbas2 mpbid ad2antrr mndcl
      ex crio wreu bitri biimpi simprd ad4antr simplr cmncom reximdva mndmolinv
      wrmo mpd reu5 riotacl grpinvval eleq1d wb oveq1 3jca mndass syl2anc linvh
      oveq2d mndlid ralrimiva nfv eqidd eqeq12d imbi1d submmulg simp3d 3impa
      cvv csubmnd cminusg ad2antlr mndidcl rspcev elrabd issubmnd simprl simpld
      sylan sylib simprr eqtr3d cbvrexw rabbii eqtri reximssdv rabexd ressplusg
      fvexd oveq123d ress0g cbvrexdva2 rexeqtrrdv isgrp grpcl oveqdr raleqbidva
      cgrp issubmndb 3ad2ant1 iscmnd sselda mpdan 3eqtrd ralbidva eqssd isabl )
      ABEUCJZBCUIJZEUCJZKUVTUJLZAUVSUWAAUAUVSUWAAUAUKZUVSLZUWCUWALZAUWDMZUWEUWC
      UVTULNZLZEUWCUVTUMNZJZUVTUNNZKZUBUKZUWCUWIJZUWKKZEUWMUOUPZUQZUBURUSZUTZUW
      FUWHUWLUWRUWFUWCCLZUWHUWFUWCDUKZFUKZBVANZJZBUNNZKZDBULNZOZFUXGVBZLZUWTUWF
      UWCUXGLZUXAUWCUXCJZUXEKZDUXGOZMUXJUWFUXKUXNUWFUXKEUWCBUMNZJZUXEKZUWMUWCUX
      OJZUXEKZUWPUQZUBURUSZAUWDUXKUXQUYAUTZUWFUWDUYBUWFBUXOEUWCUBABVCLZUWDGPAEU
      RLZUWDAEHVDZPZUXOVEZVFVGVHZVIZUWFUXMEVJVKJZUWCUXOJZUWCUXCJZUXEKDUYKUXGUWF
      BVNLZUYJURLZUXKUYKUXGLAUYMUWDABGVLZPZAUYNUWDAEVMLUYNHEVOQPZUYIUXGUXOBUYJU
      WCUXGVEZUYGVPRUWFUXAUYKKZMZUXLUYLUXEUYTUXAUYKUWCUXCUWFUYSVQVRVSUWFUYLUXPU
      XEUWFUXPUYJVJVTJZUWCUXOJZUYLUWFEVUAUWCUXOAEVUAKUWDAVUAEAEVJAEHWAAWBWCWDPV
      RUWFUYMUYNUXKVUBUYLKUYPUYQUYIUXGUXCUXOBUYJUWCUYRUYGUXCVEZWERWFUWFUXKUXQUY
      AUYHWGZWHWPSUXHUXNFUWCUXGUXBUWCKZUXFUXMDUXGVUEUXDUXLUXEUXBUWCUXAUXCWIVSWJ
      WKWLCUXIUWCIWMWLZUWFCUWGUWCACUWGKZUWDACUXGWNZVUGAUDCUXGAUDUKZCLZVUIUXGLZA
      VUJMZAVUIUXILZMVUKVULAVUMAVUJWOZAVUJVUMAVUJVUMACUXIVUICUXIKAIWQZWRVGWSSVU
      MVUKAUXHFVUIUXGWTXAQZXGXBZCUXGUVTBUVTVEZUYRXCQZPWRXDUWFUWLUXQVUDUWFUWJUXP
      UWKUXEUWFCBUUANLZUYDUWTUTZUWJUXPKUWFVUTUYDUWTAVUTUWDAUYMUVTVNLZMZVUHUXECL
      ZMZMVUTAVVCVVEAUYMVVBUYOAVVBVUIUEUKZUXCJZCLZUECUSZUDCUSZAVVIUDCVULVVHUECV
      ULVVFCLZMZVVHVUIVVFUVTVANZJZCLZVVLVVOVVNUWGLZVVLUVTUVILZVUIUWGLZVVFUWGLZV
      VPAVVQVUJVVKAVVBUFUKZUGUKZVVMJZUWKKZUFUWGOZUGUWGUSZMVVQAVVBVWEAVVBVVJAVVI
      UDCVULVVHUECVVLVVHVVGUXILZVVLVVGUXGLZUXAVVGUXCJZUXEKZDUXGOZMVWFVVLVWGVWJV
      VLUYMVUKVVFUXGLZVWGAUYMVUJVVKUYOXEZVULVUKVVKVUPPZVULAVVKVWKVUNAVVKMZAVVFU
      XILZMVWKVWNAVWOAVVKWOAVVKVWOAVVKVWOACUXIVVFVUOWRVGWSSVWOVWKAUXHFVVFUXGWTX
      AQUUJZUXGUXCBVUIVVFUYRVUCXFRZVVLVWIVVFBUUBNZNZVUIVWRNZUXCJZVVGUXCJZUXEKZD
      VXAUXGVVLUYMVWSUXGLZVWTUXGLZVXAUXGLVWLVVLVXDUXAVVFUXCJZUXEKZDUXGXHZUXGLZV
      VLVXGDUXGXIZVXIVVLVXGDUXGOZVXGDUXGXRZMVXJVVLVXKVXLVVKVXKVULVVKVWKVXKVVKVW
      KVXKMZVVKVWOVXMCUXIVVFIWMUXHVXKFVVFUXGUXBVVFKZUXFVXGDUXGVXNUXDVXFUXEUXBVV
      FUXAUXCWIVSWJWKXJXKXLXAZVVLDVVFUXGBUYRVWLVWPVVLVXKVVFUXAUXCJZUXEKZDUXGOVX
      OVVLVXGVXQDUXGVVLUXAUXGLZMZVXGVXQVXSVXGMZVXPVXFUXEVXTUYCVWKVXRVXPVXFKAUYC
      VUJVVKVXRVXGGXMVVLVWKVXRVXGVWPXEVVLVXRVXGXNUXGUXCBVVFUXAUYRVUCXORVXSVXGVQ
      WHXGXPXSXQSVXGDUXGXTWLZVXGDUXGYAQVVLVWSVXHUXGVVLVWKVWSVXHKVWPDUXGUXCBVWRV
      VFUXEUYRVUCUXEVEZVWRVEZYBQYCTZVVLVXEUXAVUIUXCJZUXEKZDUXGXHZUXGLZVVLVYFDUX
      GXIZVYHVVLVYFDUXGOZVYFDUXGXRZMVYIVVLVYJVYKVUJVYJAVVKVUJVUKVYJVUJVUKVYJMZV
      UJVUMVYLCUXIVUIIWMUXHVYJFVUIUXGUXBVUIKZUXFVYFDUXGVYMUXDVYEUXEUXBVUIUXAUXC
      WIVSWJWKXJXKXLUUCZVVLDVUIUXGBUYRVWLVWMVVLVYJVUIUXAUXCJZUXEKZDUXGOVYNVVLVY
      FVYPDUXGVXSVYFVYPVXSVYFMZVYOVYEUXEVYQUYCVUKVXRVYOVYEKAUYCVUJVVKVXRVYFGXMV
      VLVUKVXRVYFVWMXEVVLVXRVYFXNUXGUXCBVUIUXAUYRVUCXORVXSVYFVQWHXGXPXSXQSVYFDU
      XGXTWLZVYFDUXGYAQVVLVWTVYGUXGVVLVUKVWTVYGKVWMDUXGUXCBVWRVUIUXEUYRVUCVYBVY
      CYBQYCTZUXGUXCBVWSVWTUYRVUCXFRUXAVXAKZVWIVXCYDVVLVYTVWHVXBUXEUXAVXAVVGUXC
      YEVSXAVVLVXBVWSVWTVVGUXCJZUXCJZUXEVVLUYMVXDVXEVWGUTVXBWUBKVWLVVLVXDVXEVWG
      VYDVYSVWQYFUXGUXCBVWSVWTVVGUYRVUCYGYHVVLWUBVWSVWTVUIUXCJZVVFUXCJZUXCJZUXE
      VVLWUAWUDVWSUXCVVLUYMVXEVUKVWKUTZWUAWUDKVWLVVLVXEVUKVWKVYSVWMVWPYFUYMWUFM
      WUDWUAUXGUXCBVWTVUIVVFUYRVUCYGWDYHYJVVLWUEVWSUXEVVFUXCJZUXCJZUXEVVLWUDWUG
      VWSUXCVVLWUCUXEVVFUXCVVLBDVUIVWMVYRYIVRYJVVLWUHVWSVVFUXCJUXEVVLWUGVVFVWSU
      XCVVLUYMVWKWUGVVFKVWLVWPUXGUXCBVVFUXEUYRVUCVYBYKYHYJVVLBDVVFVWPVYAYIWHWHW
      HWHWPSUXHVWJFVVGUXGUXBVVGKZUXFVWIDUXGWUIUXDVWHUXEUXBVVGUXAUXCWIVSWJWKWLVV
      HVWFYDVVLCUXIVVGIWMWQTYLYLAUYMVUHVVDVVBVVJYDUYOVUQAVVDUXEUXILAUXHUXAUXEUX
      CJZUXEKZDUXGOZFUXEUXGUXBUXEKZUXFWUKDUXGWUMUXDWUJUXEUXBUXEUXAUXCWIVSWJAUYM
      UXEUXGLZUYOUXGBUXEUYRVYBUUDQZAWUNUXEUXEUXCJZUXEKZMWULAWUNWUQWUOAUYMWUNMWU
      QAUYMWUNUYOWUOSUXGUXCBUXEUXEUYRVUCVYBYKQSWUKWUQDUXEUXGUXAUXEKWUJWUPUXEUXA
      UXEUXEUXCYEVSUUEQUUFACUXIUXEVUOWRTZUDUEUXGUXCCBUVTUXEUYRVUCVYBVURUUGRZTAV
      WDUGUWGAVWAUWGLZVWDAVWACLZVWDUQWUTVWDUQAWVAVWDAWVAMZVWCUFCUWGWVBVWCUFCOUX
      AVWAUXCJZUXEKZDCOWVBWVDWVDDCUXGWVBVWAUXGLZWVDDUXGOZWVBVWAUXILZWVEWVFMAWVA
      WVGAWVAWVGACUXIVWAVUOWRVGWSUXHWVFFVWAUXGUXBVWAKZUXFWVDDUXGWVHUXDWVCUXEUXB
      VWAUXAUXCWIVSWJWKUUKZXLWVBVXRWVDMZMZVXRUHUKZUXAUXCJZUXEKZUHUXGOZMZUXACLZW
      VKVXRWVOWVBVXRWVDUUHZWVKWVNVWAUXAUXCJZUXEKUHVWAUXGWVBWVEWVJWVBWVEWVFWVIUU
      IPZWVKWVLVWAKZMZWVMWVSUXEWWBWVLVWAUXAUXCWVKWWAVQVRVSWVKWVCWVSUXEWVKUYCVXR
      WVEWVCWVSKAUYCWVAWVJGXEWVRWVTUXGUXCBUXAVWAUYRVUCXORWVBVXRWVDUULZUUMWPSWVQ
      UXAWVLUXBUXCJZUXEKZUHUXGOZFUXGVBZLWVPCWWGUXACUXIWWGIUXHWWFFUXGUXFWWEDUHUX
      GUXFUHYMWWEDYMUXAWVLKUXDWWDUXEUXAWVLUXBUXCYEVSUUNUUOUUPWMWWFWVOFUXAUXGUXB
      UXAKZWWEWVNUHUXGWWHWWDWVMUXEUXBUXAWVLUXCWIVSWJWKXJWLWWCUUQWVBVWCWVDUFDCCW
      VBVVTUXAKZMZVWBWVCUWKUXEWWJVVTUXAVWAVWAVVMUXCWVBVVMUXCKZWWIAWWKWVAAUXCVVM
      ACYTLUXCVVMKZAUXHFUXGCYTIABULUUTUURCUXCBUVTYTVURVUCUUSQZWDPPWVBWWIVQWWJVW
      AYNUVAWVBUWKUXEKZWWIAWWNWVAAUXEUWKAUYMVVDVUHUXEUWKKZUYOWURVUQCUXGBUVTUXEV
      URUYRVYBUVBRZWDZPPYOWWJCYNUVCTAUWGCKWVAACUWGVUSWDPUVDXGAWVAWUTVWDACUWGVWA
      VUSWRYPXDWSYLSUWGVVMUFUVTUWKUGUWGVEZVVMVEZUWKVEUVEWLZXEVVLVUJVVRAVUJVVKXN
      VVLCUWGVUIVULVUGVVKAVUGVUJVUSPPZWRXDVVLVVKVVSVULVVKVQVVLCUWGVVFWXAWRXDUWG
      VVMUVTVUIVVFWWRWWSUVFRVVLCUWGVVNWXAWRTVVLVVGVVNCVULVVKUDUEUXCVVMAWWLVUJWW
      MPUVGYCTYLYLWUSTZSAVUHVVDVUQWURSSUXGCBUXEUYRVYBUVJWLZPZUYFVUFYFVVAUXPUWJC
      UXOUWIBUVTEUWCUYGVURUWIVEZYQZWDQAWWNUWDWWQPYOTUWFUYAUWRUWFUXKUXQUYAUYHYRU
      WFUXTUWQUBURURUWFURYNUWFUWMURLZMZUXSUWOUWPWXHUXRUWNUXEUWKWXHVUTWXGUWTUTUX
      RUWNKZWXHVUTWXGUWTUWFVUTWXGWXDPUWFWXGVQUWFUWTWXGVUFPYFCUXOUWIBUVTUWMUWCUY
      GVURWXEYQZQAWWOUWDWXGWWPXEYOYPUVHXDYFAUWEUWSYDUWDAUVTUWIEUWCUBAUDUECUXCUV
      TVUSWWMWXBAVUJVVKUTUYCVUKVWKVVGVVFVUIUXCJKAVUJUYCVVKGUVKAVUJVVKVUKVWMYSAV
      UJVVKVWKVWPYSUXGUXCBVUIVVFUYRVUCXORUVLZUYEWXEVFPTXGXBAUAUWAUVSAUWEUWDAUWE
      MZUWDUYBWXLUXKUXQUYAWXLUWHUXKWXLUWHUWLUWRAUWEUWSWXLUWEUWSWXLUVTUWIEUWCUBA
      UVTVCLZUWEWXKPAUYDUWEUYEPZWXEVFVGVHZVIZWXLUWHUXKAUWHUXKUQZUWEAUWTUXKUQWXQ
      AUWTUXKACUXGUWCVUQUVMXGAUWTUWHUXKACUWGUWCVUSWRZYPXDPWSUVNWXLUXPUWJUWKUXEW
      XLVUTUYDUWTUXPUWJKAVUTUWEWXCPZWXNWXLUWTUWHWXPAUWTUWHYDUWEWXRPTZWXFRWXLUWH
      UWLUWRWXOWGAWWNUWEWWQPZUVOWXLUWRUYAWXLUWHUWLUWRWXOYRWXLUWQUXTUBURWXLWXGMZ
      UWOUXSUWPWYBUWNUXRUWKUXEWYBUXRUWNWYBVUTWXGUWTWXIWXLVUTWXGWXSPWXLWXGVQWXLU
      WTWXGWXTPWXJRWDWXLWWNWXGWYAPYOYPUVPXDYFWXLBUXOEUWCUBAUYCUWEGPWXNUYGVFTXGX
      BUVQAVVQWXMMUWBAVVQWXMWWTWXKSUVTUVRWLS $.
  $}

  ${
    $d K j $.  $d R a i j $.  $d U j $.  $d j ph $.
    primrootsunit.1 $e |- ( ph -> R e. CMnd ) $.
    primrootsunit.2 $e |- ( ph -> K e. NN ) $.
    primrootsunit.3 $e |- U = { a e. ( Base ` R ) |
     E. i e. ( Base ` R ) ( i ( +g ` R ) a ) = ( 0g ` R ) } $.
    $( Primitive roots have left inverses.  (Contributed by metakunt,
       25-Apr-2025.) $)
    primrootsunit $p |- ( ph -> ( ( R PrimRoots K ) =
     ( ( R |`s U ) PrimRoots K ) /\ ( R |`s U ) e. Abel ) ) $=
      ( vj cv cplusg cfv co c0g wceq cbs wrex crab nfv cbvrexw primrootsunit1
      oveq1 eqeq1d rabbii eqtri ) ABCJEFGHCDKZFKZBLMZNZBOMZPZDBQMZRZFUMSJKZUHUI
      NZUKPZJUMRZFUMSIUNURFUMULUQDJUMULJTUQDTUGUOPUJUPUKUGUOUHUIUCUDUAUEUFUB $.
  $}

  ${
    $d E l x y $.  $d K l x y $.  $d M l x y $.  $d R a c i $.  $d R l x y $.
    $d U c $.  $d U l x y $.  $d c i ph $.  $d l ph x y $.
    primrootscoprmpow.1 $e |- ( ph -> R e. CMnd ) $.
    primrootscoprmpow.2 $e |- ( ph -> K e. NN ) $.
    primrootscoprmpow.3 $e |- ( ph -> E e. NN ) $.
    primrootscoprmpow.4 $e |- ( ph -> ( E gcd K ) = 1 ) $.
    primrootscoprmpow.5 $e |- ( ph -> M e. ( R PrimRoots K ) ) $.
    primrootscoprmpow.6 $e |- U = { a e. ( Base ` R ) |
     E. i e. ( Base ` R ) ( i ( +g ` R ) a ) = ( 0g ` R ) } $.
    $( Coprime powers of primitive roots are primitive roots.  (Contributed by
       metakunt, 25-Apr-2025.) $)
    primrootscoprmpow $p |- ( ph -> ( E ( .g ` R ) M ) e.
     ( R PrimRoots K ) ) $=
      ( co wcel wceq cmul cz eqtrd vl vc vx vy cmg cfv cprimroots cress cbs c0g
      cv cdvds wbr wi cn0 wral eqid primrootsunit simprd ablcmnd cmnmndd nnnn0d
      w3a cabl simpld eleq2d mpbid isprimroot biimpd mpd mulgnn0cld csubmnd wss
      simp1d cmnd cplusg wrex wa eleq2i oveq2 eqeq1d rexbidv elrab bitri biimpi
      crab adantl ssrdv mndidcl syl simpr oveq1d mndlid syl2anc rspcedvd elrabd
      ex mpbird 3jca wb issubm2 ressbas2 submmulg syl3anc eleq1d oveq2d ablgrpd
      cgrp nn0zd mulgass nncnd mulcomd simp2d mulgz eqtr3d simp3d cgcd caddc c1
      simp-6r nn0cnd mullidd eqcomd ad6antr eqtr2d simp-4l simpllr simplr jca31
      a1i jca cc ad4antr zcnd mulcld zmulcld ad3antrrr mulassd adantr ad2antrr
      simp-4r adddird mulgdir simplll oveq12d grpidcl grpridd simp-5r r19.29vva
      bezout ralimdva cn nnnn0 ) AEGBUEUFZOZBFUGOZPUUOBCUHOZFUGOZPZAUUSUUOUUQUI
      UFZPZFUUOUUQUEUFZOZUUQUJUFZQZUAUKZUUOUVBOZUVDQZFUVFULUMZUNZUAUOUPZVCAUVAU
      VEUVKAUVAEGUVBOZUUTPZAUUTUVBUUQEGUUTUQZUVBUQZAUUQAUUQAUUPUURQZUUQVDPZABCD
      FHIJNURZUSZUTZVAZAEKVBZAGUUTPZFGUVBOZUVDQZUVFGUVBOZUVDQZUVIUNZUAUOUPZAGUU
      RPZUWCUWEUWIVCZAGUUPPUWJMAUUPUURGAUVPUVQUVRVEZVFVGAUWJUWKAUUQUVBFGUAUVTAF
      JVBZUVOVHVIVJZVNZVKZAUUOUVLUUTACBVLUFPZEUOPZGCPZUUOUVLQZAUWQCBUIUFZVMZBUJ
      UFZCPZUUQVOPZVCZAUXBUXDUXEAUBCUXAAUBUKZCPZUXGUXAPZUXHUXIAUXHUXIDUKZUXGBVP
      UFZOZUXCQZDUXAVQZUXHUXIUXNVRZUXHUXGUXJHUKZUXKOZUXCQZDUXAVQZHUXAWFZPUXOCUX
      TUXGNVSUXSUXNHUXGUXAUXPUXGQZUXRUXMDUXAUYAUXQUXLUXCUXPUXGUXJUXKVTWAWBWCWDW
      EVEWGWQWHZAUXDUXCUXTPAUXSUXJUXCUXKOZUXCQZDUXAVQHUXCUXAUXPUXCQZUXRUYDDUXAU
      YEUXQUYCUXCUXPUXCUXJUXKVTWAWBABVOPZUXCUXAPZABIVAZUXABUXCUXAUQZUXCUQZWIWJZ
      AUYDUXCUXCUXKOZUXCQZDUXCUXAUYKAUXJUXCQZVRZUYCUYLUXCUYOUXJUXCUXCUXKAUYNWKW
      LWAAUYFUYGUYMUYHUYKUXAUXKBUXCUXCUYIUXKUQUYJWMWNWOWPACUXTUXCCUXTQANYJVFWRU
      WAWSAUYFUWQUXFWTUYHUXACUUQBUXCUYIUYJUUQUQZXAWJWRZUWBAUWSUWCUWOACUUTGAUXBC
      UUTQUYBCUXAUUQBUYPUYIXBWJVFWRZCUUNUVBBUUQEGUUNUQUYPUVOXCZXDZXEWRAUVCFUVLU
      VBOZUVDAUUOUVLFUVBUYTXFAFEROZGUVBOZVUAUVDAUUQXHPZFSPZESPZUWCVCVUCVUAQAUUQ
      UVSXGZAVUEVUFUWCAFUWMXIZAEUWBXIZUWOWSUUTUVBUUQFEGUVNUVOXJWNAVUCEFROZGUVBO
      ZUVDAVUBVUJGUVBAFEAFJXKZAEKXKZXLWLAVUKEUWDUVBOZUVDAVUDVUFVUEUWCVCVUKVUNQV
      UGAVUFVUEUWCVUIVUHUWOWSUUTUVBUUQEFGUVNUVOXJWNAVUNEUVDUVBOZUVDAUWDUVDEUVBA
      UWCUWEUWIUWNXMZXFAVUDVUFVUOUVDQVUGVUIUUTUVBUUQEUVDUVNUVOUVDUQZXNWNTTTXOTA
      UWIUVKAUWCUWEUWIUWNXPAUWHUVJUAUOAUVFUOPZVRZUWHUVJVUSUWHVRZUVHUVIVUTUVHVRZ
      EFXQOZEUCUKZROZFUDUKZROZXROZQZUVIUCUDSSVVAVVCSPZVRZVVESPZVRZVVHVRZUWGUVIV
      VMUWFVVBUVFROZGUVBOZUVDVVMUVFVVNGUVBVVMUVFXSUVFROZVVNVVMVVPUVFVVMUVFVVMUV
      FAVURUWHUVHVVIVVKVVHXTYAYBYCVVMXSVVBUVFRVVMVVBVVGXSVVLVVHWKZVVMVVBVVGXSVV
      QAVVBXSQVURUWHUVHVVIVVKVVHLYDXOYEWLTWLVVMVVOVVGUVFROZGUVBOZUVDVVMVVNVVRGU
      VBVVMVVBVVGUVFRVVQWLWLVVLVVSUVDQZVVHVVLVUSUVHVRZVVIVRZVVKVRZVVTVVLVWBVVKV
      VLVUSUVHVVIVUSUWHUVHVVIVVKYFVUTUVHVVIVVKYGVVAVVIVVKYHYIVVJVVKWKYKVWCVVSVV
      DUVFROZVVFUVFROZXROZGUVBOZUVDVWCVVRVWFGUVBVWCVVDVVFUVFVWCEVVCAEYLPZVURUVH
      VVIVVKVUMYMVWCVVCVWAVVIVVKYHZYNYOVWCFVVEAFYLPZVURUVHVVIVVKVULYMVWCVVEVWBV
      VKWKZYNYOVWCUVFAVURUVHVVIVVKUUAZYAUUBWLVWCVWGVWDGUVBOZVWEGUVBOZUUQVPUFZOZ
      UVDVWCVUDVWDSPZVWESPZUWCVCVWGVWPQAVUDVURUVHVVIVVKVUGYMZVWCVWQVWRUWCVWCVVD
      UVFVWCEVVCAVUFVURUVHVVIVVKVUIYMVWIYPVWCUVFVWLXIZYPVWCVVFUVFVWCFVVEAVUEVUR
      UVHVVIVVKVUHYMVWKYPVWTYPAUWCVURUVHVVIVVKUWOYMWSUUTVWOUVBUUQVWDVWEGUVNUVOV
      WOUQZUUCWNVWCVWPUVDUVDVWOOUVDVWCVWMUVDVWNUVDVWOVWBVWMUVDQVVKVWBVWMVVCUVFR
      OZEROZGUVBOZUVDVWBVWDVXCGUVBVWBVWDEVXBROVXCVWBEVVCUVFAVWHVURUVHVVIVUMYQZV
      WBVVCVWAVVIWKZYNZVWBUVFAVURUVHVVIYGZYAZYRVWBEVXBVXEVWBVVCUVFVXGVXIYOXLTWL
      VWBVXDVXBUVLUVBOZUVDVWBVUDVXBSPZVUFUWCVCVXDVXJQAVUDVURUVHVVIVUGYQZVWBVXKV
      UFUWCVWBVVCUVFVXFVWBUVFVXHXIZYPAVUFVURUVHVVIVUIYQAUWCVURUVHVVIUWOYQWSUUTU
      VBUUQVXBEGUVNUVOXJWNVWBVXJVVCUVFUVLUVBOZUVBOZUVDVWBVUDVVIUVFSPZUVMVCVXJVX
      OQVXLVWBVVIVXPUVMVXFVXMAUVMVURUVHVVIUWPYQWSUUTUVBUUQVVCUVFUVLUVNUVOXJWNVW
      BVXOVVCUVDUVBOZUVDVWBVXNUVDVVCUVBVWBVXNUVGUVDVWBUVLUUOUVFUVBVWBUUOUVLVUSU
      WTUVHVVIVUSUWQUWRUWSUWTAUWQVURUYQYSAUWRVURUWBYSAUWSVURUYRYSUYSXDYTYCXFVUS
      UVHVVIYHTXFVWBVUDVVIVXQUVDQVXLVXFUUTUVBUUQVVCUVDUVNUVOVUQXNWNTTTTYSVWCVUS
      VVKVRZVWNUVDQVWCVUSVVKVUSUVHVVIVVKUUDVWKYKVXRVWNVVEUVFROZFROZGUVBOZUVDVXR
      VWEVXTGUVBVXRVWEFVXSROVXTVXRFVVEUVFAVWJVURVVKVULYTZVXRVVEVUSVVKWKZYNZVXRU
      VFAVURVVKYHZYAZYRVXRFVXSVYBVXRVVEUVFVYDVYFYOXLTWLVXRVYAVXSUWDUVBOZUVDVXRV
      UDVXSSPZVUEUWCVCVYAVYGQAVUDVURVVKVUGYTZVXRVYHVUEUWCVXRVVEUVFVYCVXRUVFVYEX
      IYPZAVUEVURVVKVUHYTAUWCVURVVKUWOYTWSUUTUVBUUQVXSFGUVNUVOXJWNVXRVYGVXSUVDU
      VBOZUVDVXRUWDUVDVXSUVBAUWEVURVVKVUPYTXFVXRVUDVYHVYKUVDQVYIVYJUUTUVBUUQVXS
      UVDUVNUVOVUQXNWNTTTWJUUEVWCUUTVWOUUQUVDUVDUVNVXAVUQVWSVWCVUDUVDUUTPVWSUUT
      UUQUVDUVNVUQUUFWJUUGTTTWJYSTTVUSUWHUVHVVIVVKVVHUUHVJAVVHUDSVQUCSVQZVURUWH
      UVHAVUFVUEVYLVUIVUHUCUDEFUUJWNYQUUIWQWQUUKVJWSAUUQUVBFUUOUAUVTAFUULPFUOPJ
      FUUMWJUVOVHWRAUUPUURUUOUWLVFWR $.
  $}

  ${
    $d A w x y z $.  $d B w x y z $.
    $( Bezout's identity restricted on positive integers in all but one
       variable.  (Contributed by metakunt, 26-Apr-2025.) $)
    posbezout $p |- ( ( A e. NN /\ B e. NN ) -> E. x e. NN E. y e. ZZ
     ( A gcd B ) = ( ( A x. x ) + ( B x. y ) ) ) $=
      ( wcel wa co cmul caddc cz c2 cmin cc0 clt wbr a1i cle adantr mulcld c1
      vw vz cn cgcd cv wceq wrex oveq2 oveq1d eqeq2d oveq2d simplr simpllr nnzd
      zmulcld simpr zaddcld 2z cneg zred renegcld 0red df-neg addge0d lesubaddd
      cr leidd mpbird eqbrtrd nnred nngt0d 2re readdcld 2pos 2cn addlidi eqtr4i
      eqid breqtri msqge0d le2addd ltletrd mulgt0d lelttrd wn wi nnnn0d nn0ge0d
      remulcld mulge0d recnd subidd 1red letrd lemulge11d negcld addridd eqcomd
      0le1 breqtrd ltadd2dd mul2negd subid1d ltsub13d zcnd 2cnd addcld zltlem1d
      subnegd ex 0zd eqcomi breq2d lenegd 1cnd negnegd breq1d biimpd imim1d mpd
      bitrd imp mullidd leadd1dd nnge1d lemul1ad ltsubadd2d mpbid nncnd addassd
      0le2 adddid eqtrd cc addcomd ltsubaddd ltnled bicomd jca nnz elnnz sylibr
      pm2.61dan posdifd simp-4l zsubcld simplll ppncand eqidd eqtr2d 2rspcedvdw
      mul12d subdid oveq12d adantl bezout syl r19.29vva ) CUCEZDUCEZFZCDUDGZCUA
      UEZHGZDUBUEZHGZIGZUFZUVBCAUEZHGZDBUEZHGZIGZUFZBJUGAUCUGUAUBJJUVAUVCJEZFZU
      VEJEZFZUVHFZUVNUVBCUVCDUVCUVCHGZUVEUVEHGZIGZKIGZHGZIGZHGZUVLIGZUFUVBUWFDU
      VECUWCHGZLGZHGZIGZUFABUWEUWIUCJUVIUWEUFZUVMUWGUVBUWLUVJUWFUVLIUVIUWECHUHU
      IUJUVKUWIUFZUWGUWKUVBUWMUVLUWJUWFIUVKUWIDHUHUKUJUVRUWEUCEZUVHUVRUWEJEZMUW
      ENOZFUWNUVRUWOUWPUVRUVCUWDUVAUVOUVQULZUVRDUWCUVRDUUSUUTUVOUVQUMZUNUVRUWBK
      UVRUVTUWAUVRUVCUVCUWQUWQUOUVRUVEUVEUVPUVQUPZUWSUOZUQZKJEZUVRURPUQZUOZUQUV
      RMUWDUVCUSZLGZUWENUVRUXEUWDNOZMUXFNOUVRMUVCQOZUXGUVRUXHFZUXEMUWDUVRUXEVFE
      ZUXHUVRUVCUVRUVCUWQUTZVAZRUXIVBZUVRUWDVFEZUXHUVRUWDUXDUTZRUXIUXEMUVCLGZMQ
      UXEUXPUFZUXIUVCVCZPUXIUXPMQOMMUVCIGQOUXIMUVCUXMUVRUVCVFEZUXHUXKRZUXIMUXMV
      GUVRUXHUPVDUXIMUVCMUXMUXTUXMVEVHVIUVRMUWDNOUXHUVRDUWCUVRDUWRVJZUVRUWCUXCU
      TZUVRDUWRVKUVRMMKIGZUWCUVRVBZUVRMKUYDKVFEZUVRVLPZVMZUYBMUYCNOUVRMKUYCNVNK
      KUYCKVRKVOVPVQVSPUVRMKUWBKUYDUYFUVRUWBUXAUTUYFUVRUVTUWAUVRUVCUVCUXKUXKWIU
      VRUWAUWTUTUVRUVCUXKVTZUVRUVEUVRUVEUWSUTZVTVDUVRKUYFVGWAWBWCRWDUVRUXHWEZUX
      GUVRUVCMNOZUXGWFUYJUXGWFUVRUYKUXGUVRUYKFZUXEUXPUWDNUXQUYLUXRPUYLUXPUWDNOM
      UWDUVCIGZNOUYLMDUWAHGZDUVTKIGZHGZUVCIGZIGZUYMNUYLMUYNUYRUVRMVFEZUYKUYDRZU
      YLDUWAUVRDVFEUYKUYARZUYLUVEUVEUVRUVEVFEUYKUYIRZVUBWIZWIZUYLUYNUYQVUDUYLUY
      PUVCUYLDUYOVUAUYLUVTKUYLUVCUVCUVRUXSUYKUXKRZVUEWIZUYEUYLVLPZVMZWIZVUEVMZV
      MUYLDUWAVUAVUCUYLDUYLDUVRUUTUYKUWRRZWGWHUYLUVEVUBVTWJUYLUYNUYNLGZUYQNOUYN
      UYRNOUYLVULMUYQNUYLUYNUYLDUWAUYLDVUAWKUYLUVEUVEUYLUVEVUBWKZVUMSSWLUYLMTUY
      OHGZUVCIGZUYQUYTUYLVUNUVCUYLTUYOUYLWMZVUHWIZVUEVMVUJUYLMUYOUVCIGZVUONUVRU
      YKMVURNOZUVRTUXEQOZVUSWFUYKVUSWFUVRVUTVUSUVRVUTFZMUYOUXELGVURNVVAUXEUYOMU
      VRUXJVUTUXLRZVVAUVTKVVAUVCUVCUVRUXSVUTUXKRZVVCWIUYEVVAVLPZVMZUVRUYSVUTUYD
      RZVVAUXEUYOUYOMLGZNVVAUXEUXEUXEHGZKIGZUYONVVAUXEVVHVVIVVBVVAUXEUXEVVBVVBW
      IZVVAVVHKVVJVVDVMZVVAUXEUXEVVBVVBVVAMTUXEVVFUVRTVFEVUTUVRWMZRVVBMTQOVVAWS
      PUVRVUTUPZWNVVMWOVVAVVHVVHMIGZVVIVVJVVAVVHMVVJVVFVMVVKVVAVVHVVHVVNQVVAVVH
      VVJVGVVAVVNVVHVVAVVHVVAUXEUXEVVAUVCVVAUVCVVCWKZWPZVVPSWQWRWTVVAMKVVHVVFVV
      DVVJMKNOVVAVNPXAWDWDVVAVVHUVTKIVVAUVCUVCVVOVVOXBUIWTVVAVVGUYOVVAUYOVVAUYO
      VVEWKXCWRWTXDVVAUYOUVCVVAUVTKVVAUVCUVCVVAUVCUVRUVOVUTUWQRXEZVVQSVVAXFXGVV
      QXIWTXJUVRUYKVUTVUSUVRUYKVUTUVRUYKTUSZUSZUXEQOZVUTUVRUYKUVCVVRQOZVVTUVRUY
      KUVCMTLGZQOVWAUVRUVCMUWQUVRXKXHUVRVWBVVRUVCQVWBVVRUFUVRVVRVWBTVCXLPXMYAUV
      RUVCVVRUXKUVRTVVLVAXNYAUVRVVSTUXEQUVRTUVRXOXPXQYAXRXSXTYBUYLUYOVUNUVCIUYL
      VUNUYOUYLUYOUYLUYOVUHWKYCWRUIWTUYLVUNUYPUVCVUQVUIVUEUYLTDUYOVUPVUAVUHUYLM
      UYCUYOUYTUVRUYCVFEUYKUYGRVUHUYLMKUYTVUGUYLMUYTVGMKQOUYLYKPVDUYLMUVTKUYTVU
      FVUGUVRMUVTQOUYKUYHRYDWNUYLDVUKYEYFYDWBVIUYLUYNUYNUYQVUDVUDVUJYGYHWDUYLUY
      RDUWAUYOIGZHGZUVCIGZUYMUYLUYRUYNUYPIGZUVCIGZVWEUYLVWGUYRUYLUYNUYPUVCUYLDU
      WAUYLDVUKYIZUYLUVEUVEUYLUVEUVRUVQUYKUWSRXEZVWISZSUYLDUYOVWHUYLUVTKUYLUVCU
      VCUYLUVCVUEWKZVWKSZUYLXFXGZSVWKYJWRUYLVWFVWDUVCIUYLVWDVWFUYLDUWAUYOVWHVWJ
      VWMYLWRUIYMUYLVWDUWDUVCIUYLVWCUWCDHUYLVWCUWAUVTIGZKIGZUWCUYLVWOVWCUYLUWAU
      VTKVWJVWLKYNEUYLVOPYJWRUYLVWNUWBKIUYLUWAUVTVWJVWLYOUIYMUKUIYMWTUYLMUVCUWD
      UYTVUEUVRUXNUYKUXORYPVHVIXJUVRUYJUYKUXGUVRUYJUYKUVRUYKUYJUVRUVCMUXKUYDYQY
      RXRXSXTYBUUCUVRUXEUWDUXLUXOUUDYHUVRUXFUYMUWEUVRUWDUVCUVRUWDUXDXEZUVRUVCUW
      QXEZXIUVRUWDUVCVWPVWQYOYMWTYSUWEUUAUUBRUVSUVEUWHUVPUVQUVHULZUVSCUWCUVSCUU
      SUUTUVOUVQUVHUUEUNUVSUWBKUVSUVTUWAUVSUVCUVCUVAUVOUVQUVHUMZVWSUOUVSUVEUVEV
      WRVWRUOUQUXBUVSURPUQUOUUFUVSUVBUVGUWKUVRUVHUPUVRUVGUWKUFUVHUVRUVGUVDCUWDH
      GZIGZUVFDUWHHGZLGZIGZUWKUVRUVGVXAUVFVWTLGZIGZVXDUVRVXFUVGUVGUVRUVDVWTUVFU
      VRCUVCUVRCUUSUUTUVOUVQUUGYIZVWQSUVRCUWDVXGUVRDUWCUVRDUWRYIZUVRUWBKUVRUVTU
      WAUVRUVCUVCVWQVWQSUVRUVEUVEUVRUVEUWSXEZVXISXGUVRXFXGZSSUVRDUVEVXHVXISUUHU
      VRUVGUUIUUJUVRVXEVXCVXAIUVRVWTVXBUVFLUVRCDUWCVXGVXHUVRUWCUXCXEUULUKUKYMUV
      RVXAUWFVXCUWJIUVRUWFVXAUVRCUVCUWDVXGVWQVWPYLWRUVRUWJVXCUVRDUVEUWHVXHVXIUV
      RCUWCVXGVXJSUUMWRUUNYMRYMUUKUVACJEZDJEZFUVHUBJUGUAJUGUVAVXKVXLUUSVXKUUTCY
      TRUUTVXLUUSDYTUUOYSUAUBCDUUPUUQUUR $.
  $}

  ${
    $d K m x $.  $d R m x $.  $d R x y $.  $d m ph x $.
    primrootscoprf.1 $e |- F = ( m e. ( R PrimRoots K ) |->
     ( E ( .g ` R ) m ) ) $.
    primrootscoprf.2 $e |- ( ph -> R e. CMnd ) $.
    primrootscoprf.3 $e |- ( ph -> K e. NN ) $.
    primrootscoprf.4 $e |- ( ph -> E e. NN ) $.
    primrootscoprf.5 $e |- ( ph -> ( E gcd K ) = 1 ) $.
    $( Coprime powers of primitive roots are primitive roots, as a function.
       (Contributed by metakunt, 26-Apr-2025.) $)
    primrootscoprf $p |- ( ph -> F :
     ( R PrimRoots K ) --> ( R PrimRoots K ) ) $=
      ( vx vy co cv cfv wcel wceq adantr cn cprimroots cmg cplusg c0g wrex crab
      wa cbs ccmn cgcd c1 simpr eqid primrootscoprmpow fmptd ) ACBFUANZDCOZBUBP
      NUPEAUQUPQZUGBLOMOBUCPNBUDPRLBUHPZUEMUSUFZLDFUQMABUIQURHSAFTQURISADTQURJS
      ADFUJNUKRURKSAURULUTUMUNGUO $.
  $}

  ${
    $d F x $.  $d F y $.  $d I m $.  $d I n $.  $d J m x $.  $d J n x $.
    $d J m y $.  $d K l x $.  $d K m x $.  $d K n x $.  $d K t x $.
    $d K l y $.  $d R a f i $.  $d R l x $.  $d R m x $.  $d R n x $.
    $d R s t $.  $d R l y $.  $d U f $.  $d U l x $.  $d f i ph $.
    $d l ph x $.  $d m ph x $.  $d n ph x $.  $d n ph y $.  $d ph t x $.
    $d t y $.
    primrootscoprbij.1 $e |- F = ( m e. ( R PrimRoots K ) |->
     ( I ( .g ` R ) m ) ) $.
    primrootscoprbij.2 $e |- ( ph -> R e. CMnd ) $.
    primrootscoprbij.3 $e |- ( ph -> K e. NN ) $.
    primrootscoprbij.4 $e |- ( ph -> I e. NN ) $.
    primrootscoprbij.5 $e |- ( ph -> J e. NN ) $.
    primrootscoprbij.6 $e |- ( ph -> Z e. ZZ ) $.
    primrootscoprbij.7 $e |- ( ph -> 1 = ( ( I x. J ) + ( K x. Z ) ) ) $.
    primrootscoprbij.8 $e |- U = { a e. ( Base ` R ) |
     E. i e. ( Base ` R ) ( i ( +g ` R ) a ) = ( 0g ` R ) } $.
    $( A bijection between coprime powers of primitive roots and primitive
       roots.  (Contributed by metakunt, 26-Apr-2025.) $)
    primrootscoprbij $p |- ( ph -> F :
     ( R PrimRoots K ) -1-1-onto-> ( R PrimRoots K ) ) $=
      ( co vn vx vy vl vt vs vf cprimroots cv cmg cmpt cz wcel wa cmul caddc c1
      cfv wceq cgcd nnzd jca jca31 eqcomd bezoutr1 imp syl primrootscoprf nncnd
      eqid mulcomd oveq1d eqtrd cbs a1i simpr oveq2d cmnd cmnmndd adantr nnnn0d
      cn0 c0g wbr wi wral w3a isprimroot biimpd simp1d mulgnn0cl syl3anc fvmptd
      cdvds fveq2d eqidd wrex crab ccmn cn primrootscoprmpow mulgnn0ass syl2anc
      cplusg 3jca cress cabl primrootsunit simpld eleq2d wss cgrp simprd ablgrp
      csubmnd grpmnd oveq2 eqeq1d rexbidv elrab biimpi ex ssrdv mpbird submmulg
      nn0mulcld cmin 1zzd zmulcld znegcld mulgdir mulg1 mulgneg oveq12d mulgass
      mulcld simp2d eqtr3d ralrimiva sseld mndidcl mndlid elrabd sylibr ablcmnd
      rspcedvd issubmndb ressbas2 cneg zcnd 1cnd addlsub mpbid eqeltrrd negsubd
      cc cminusg mulgz grpinvid mndrid imim2d mpd sseq1d sseqtrd imbi1d grpridd
      2fvidf1od ) ABIUHTZUVHFUAUVHHUAUIZBUJURZTZUKZUBUCABEGFILMNOAGULUMZIULUMZU
      NHULUMZJULUMZUNZUNZGHUOTZIJUOTZUPTZUQUSZUNGIUTTUQUSZAUVRUWBAUVMUVNUVQAGOV
      AZAINVAZAUVOUVPAHPVAZQVBVCAUQUWARVDZVBUVRUWBUWCGIHJVEVFVGZVHABUAHUVLIUVLV
      JMNPAUVOUVNUNZUVMUVPUNZUNZHGUOTZUVTUPTZUQUSZUNHIUTTUQUSZAUWKUWNAUWIUWJAUV
      OUVNUWFUWEVBAUVMUVPUWDQVBVBAUWMUWAUQAUWLUVSUVTUPAHGAHPVIZAGOVIZVKZVLUWGVM
      VBUWKUWNUWOHIGJVEVFVGZVHAUBUIZFURZUVLURZUWTUSUBUVHAUWTUVHUMZUNZUXBGUWTUVJ
      TZUVLURZUWTUXDUXAUXEUVLUXDEUWTGEUIZUVJTZUXEUVHFBVNURZFEUVHUXHUKUSZUXDLVOU
      XDUXGUWTUSZUNUXGUWTGUVJUXDUXKVPVQAUXCVPZUXDBVRUMZGWBUMZUWTUXIUMZUXEUXIUMZ
      AUXMUXCABMVSZVTZAUXNUXCAGOWAZVTZUXDUXOIUWTUVJTBWCURZUSZUDUIZUWTUVJTUYAUSI
      UYCWNWDZWEUDWBWFZAUXCUXOUYBUYEWGZAUXCUYFABUVJIUWTUDMAINWAZUVJVJZWHWIVFWJZ
      UXIUVJBGUWTUXIVJZUYHWKWLZWMWOUXDUXFHUXEUVJTZUWTUXDUAUXEUVKUYLUVHUVLUXIUXD
      UVLWPUXDUVIUXEUSZUNUVIUXEHUVJUXDUYMVPVQUXDBUEUIUFUIBXDURZTUYAUSUEUXIWQUFU
      XIWRZUEGIUWTUFABWSUMZUXCMVTAIWTUMZUXCNVTAGWTUMUXCOVTAUWCUXCUWHVTUXLUYOVJZ
      XAUXDUXMHWBUMZUXPUYLUXIUMUXRAUYSUXCAHPWAZVTZUYKUXIUVJBHUXEUYJUYHWKWLWMUXD
      UWLUWTUVJTZUYLUWTUXDUXMUYSUXNUXOWGVUBUYLUSUXRUXDUYSUXNUXOVUAUXTUYIXEUXIUV
      JBHGUWTUYJUYHXBXCAUXCVUBUWTUSZAUXCUWTBCXFTZIUHTZUMZWEUXCVUCWEAUXCVUFAUVHV
      UEUWTAUVHVUEUSZVUDXGUMZABCDIKMNSXHZXIZXJWIAVUFVUCUXCAVUFVUCAVUFUNZVUBUWLU
      WTVUDUJURZTZUWTVUKCBXOURUMZUWLWBUMUWTCUMZVUBVUMUSAVUNVUFAUXMVUDVRUMZUNZCU
      XIXKZUYACUMZUNZUNVUNAVUQVUTAUXMVUPUXQAVUDXLUMZVUPAVUHVVAAVUGVUHVUIXMZVUDX
      NVGZVUDXPZVGVBAVURVUSAUGCUXIAUGUIZCUMZVVEUXIUMZAVVFUNVVEDUIZKUIZUYNTZUYAU
      SZDUXIWQZKUXIWRZUMZVVGAVVFVVNAVVFVVNACVVMVVECVVMUSASVOZXJWIVFVVNVVGVVHVVE
      UYNTZUYAUSZDUXIWQZVVNVVGVVRUNVVLVVRKVVEUXIVVIVVEUSZVVKVVQDUXIVVSVVJVVPUYA
      VVIVVEVVHUYNXQXRXSXTYAXIVGYBYCZAVUSUYAVVMUMAVVLVVHUYAUYNTZUYAUSZDUXIWQKUY
      AUXIVVIUYAUSZVVKVWBDUXIVWCVVJVWAUYAVVIUYAVVHUYNXQXRXSAUXMUYAUXIUMZUXQUXIB
      UYAUYJUYAVJZUUAVGZAVWBUYAUYAUYNTZUYAUSZDUYAUXIVWFAVVHUYAUSZUNZVWAVWGUYAVW
      JVVHUYAUYAUYNAVWIVPVLXRAUXMVWDVWHUXQVWFUXIUYNBUYAUYAUYJUYNVJVWEUUBXCUUFUU
      CACVVMUYAVVOXJYDVBVBUXICBUYAUYJVWEUUGUUDZVTVUKHGAUYSVUFUYTVTAUXNVUFUXSVTY
      FVUKVUOUWTVUDVNURZUMZVUKVWMIUWTVULTZVUDWCURZUSZUYCUWTVULTVWOUSUYDWEUDWBWF
      ZAVUFVWMVWPVWQWGZAVUFVWRAVUDVULIUWTUDAVUDVVBUUEZUYGVULVJZWHWIVFZWJZVUKCVW
      LUWTACVWLUSZVUFAVURVXCVVTCUXIVUDBVUDVJZUYJUUHVGZVTXJYDZCUVJVULBVUDUWLUWTU
      YHVXDVWTYEWLVUKVUMUQJIUOTZUUIZUPTZUWTVULTZUWTVUKUWLVXIUWTVULVUKUWLUVSVXIA
      UWLUVSUSVUFUWRVTAUVSVXIUSZVUFAUVSUQVXGYGTZVXIAUVSUQUVTYGTZVXLAUWBUVSVXMUS
      UWGAUVSUVTUQAGHUWQUWPYPAIJAINVIZAJQUUJZYPZAUUKZUULUUMAUVTVXGUQYGAIJVXNVXO
      VKZVQVMAVXIVXLAUQVXGVXQAUVTVXGUUPVXRVXPUUNUUOVDVMZVTVMVLVUKVXJUQUWTVULTZV
      XHUWTVULTZVUDXDURZTZUWTVUKVVAUQULUMZVXHULUMZVWMWGVXJVYCUSAVVAVUFVVCVTZVUK
      VYDVYEVWMVUKYHVUKVXGVUKJIAUVPVUFQVTZAUVNVUFUWEVTZYIZYJVXBXEVWLVYBVULVUDUQ
      VXHUWTVWLVJZVWTVYBVJZYKXCVUKVYCUWTVXGUWTVULTZVUDUUQURZURZVYBTZUWTVUKVXTUW
      TVYAVYNVYBVUKVWMVXTUWTUSVXBVWLVULVUDUWTVYJVWTYLVGVUKVVAVXGULUMZVWMVYAVYNU
      SVYFVYIVXBVWLVULVUDVYMVXGUWTVYJVWTVYMVJZYMWLYNVUKVYOUWTVWOVYBTZUWTVUKVYNV
      WOUWTVYBVUKVYNVWOVYMURZVWOVUKVYLVWOVYMVUKVYLJVWNVULTZVWOVUKVVAUVPUVNVWMWG
      VYLVYTUSVYFVUKUVPUVNVWMVYGVYHVXBXEVWLVULVUDJIUWTVYJVWTYOXCVUKVYTJVWOVULTZ
      VWOVUKVWNVWOJVULVUKVWMVWPVWQVXAYQVQVUKVVAUVPWUAVWOUSZVYFVYGVWLVULVUDJVWOV
      YJVWTVWOVJZUURZXCVMVMWOAVYSVWOUSZVUFAVVAWUEVVCVUDVYMVWOWUCVYQUUSZVGVTVMVQ
      VUKVUPVWMVYRUWTUSVUKVVAVUPVYFVVDVGVXBVWLVYBVUDUWTVWOVYJVYKWUCUUTXCVMVMVMV
      MVMYBUVAUVBVFYRVMVMYSAUCUIZUVLURZFURZWUGUSUCUVHAWUGUVHUMZUNZWUIHWUGUVJTZF
      URZWUGWUKWUHWULFWUKUAWUGUVKWULUVHUVLUXIWUKUVLWPWUKUVIWUGUSZUNUVIWUGHUVJWU
      KWUNVPVQAWUJVPZWUKUXMUYSWUGUXIUMZWULUXIUMZAUXMWUJUXQVTZAUYSWUJUYTVTZWUKWU
      PIWUGUVJTUYAUSZUYCWUGUVJTUYAUSUYDWEUDWBWFZAWUJWUPWUTWVAWGZAWUJWVBABUVJIWU
      GUDMUYGUYHWHWIVFWJZUXIUVJBHWUGUYJUYHWKWLZWMWOWUKWUMGWULUVJTZWUGWUKEWULUXH
      WVEUVHFUXIUXJWUKLVOWUKUXGWULUSZUNUXGWULGUVJWUKWVFVPVQWUKBUYOUEHIWUGUFAUYP
      WUJMVTAUYQWUJNVTAHWTUMWUJPVTAUWOWUJUWSVTWUOUYRXAWUKUXMUXNWUQWVEUXIUMWURAU
      XNWUJUXSVTZWVDUXIUVJBGWULUYJUYHWKWLWMWUKUVSWUGUVJTZWVEWUGWUKUXMUXNUYSWUPW
      GWVHWVEUSWURWUKUXNUYSWUPWVGWUSWVCXEUXIUVJBGHWUGUYJUYHXBXCWUKWVHUVSWUGVULT
      ZWUGWUKVUNUVSWBUMWUGCUMZWVHWVIUSAVUNWUJVWKVTWUKGHWVGWUSYFAWUJWVJAUVHCWUGA
      UVHCXKVUECXKAUBVUECAVUFVUOVXFYBYCAUVHVUECVUJUVCYDZYTVFCUVJVULBVUDUVSWUGUY
      HVXDVWTYEWLWUKWVIVXIWUGVULTZWUGWUKUVSVXIWUGVULAVXKWUJVXSVTVLWUKWVLUQWUGVU
      LTZVXHWUGVULTZVYBTZWUGWUKVVAVYDVYEWUGVWLUMZWGWVLWVOUSAVVAWUJVVCVTZWUKVYDV
      YEWVPWUKYHWUKVXGWUKJIAUVPWUJQVTZAUVNWUJUWEVTZYIZYJAWUJWVPAUVHVWLWUGAUVHCV
      WLWVKVXEUVDYTVFZXEVWLVYBVULVUDUQVXHWUGVYJVWTVYKYKXCWUKWVOWUGVWOVYBTWUGWUK
      WVMWUGWVNVWOVYBWUKWVPWVMWUGUSWWAVWLVULVUDWUGVYJVWTYLVGWUKWVNVXGWUGVULTZVY
      MURZVWOWUKVVAVYPWVPWVNWWCUSWVQWVTWWAVWLVULVUDVYMVXGWUGVYJVWTVYQYMWLWUKWWC
      VYSVWOWUKWWBVWOVYMWUKWWBJIWUGVULTZVULTZVWOWUKVVAUVPUVNWVPWGWWBWWEUSWVQWUK
      UVPUVNWVPWVRWVSWWAXEVWLVULVUDJIWUGVYJVWTYOXCWUKWWEWUAVWOWUKWWDVWOJVULAWUJ
      WWDVWOUSZAWUJWWFWEWUGVUEUMZWWFWEAWWGWWFAWWGUNWVPWWFUYCWUGVULTVWOUSUYDWEUD
      WBWFZAWWGWVPWWFWWHWGZAWWGWWIAVUDVULIWUGUDVWSUYGVWTWHWIVFYQYBAWUJWWGWWFAUV
      HVUEWUGVUJXJUVEYDVFVQWUKVVAUVPWUBWVQWVRWUDXCVMVMWOWUKVVAWUEWVQWUFVGVMVMYN
      WUKVWLVYBVUDWUGVWOVYJVYKWUCWVQWWAUVFVMVMVMVMYRVMVMYSUVG $.
  $}

  ${
    $d F x y $.  $d I m x y $.  $d I x y z $.  $d K m x y $.  $d K x y z $.
    $d R m x y $.  $d R w z $.  $d m ph x y $.  $d ph x y z $.
    primrootscoprbij2.1 $e |- F = ( m e. ( R PrimRoots K ) |->
     ( I ( .g ` R ) m ) ) $.
    primrootscoprbij2.2 $e |- ( ph -> R e. CMnd ) $.
    primrootscoprbij2.3 $e |- ( ph -> K e. NN ) $.
    primrootscoprbij2.4 $e |- ( ph -> I e. NN ) $.
    primrootscoprbij2.5 $e |- ( ph -> ( I gcd K ) = 1 ) $.
    $( A bijection between coprime powers of primitive roots and primitive
       roots.  (Contributed by metakunt, 26-Apr-2025.) $)
    primrootscoprbij2 $p |- ( ph -> F :
     ( R PrimRoots K ) -1-1-onto-> ( R PrimRoots K ) ) $=
      ( vx vy vz co cv cn wcel wa ad3antrrr vw cgcd cmul wceq cprimroots cplusg
      caddc wf1o cz cfv c0g cbs wrex crab ccmn simpllr simplr simpr eqtr3d eqid
      c1 primrootscoprbij jca posbezout syl r19.29vva ) AEFUBOZELPZUCOFMPZUCOUG
      OZUDZBFUEOZVLDUHLMQUIAVHQRZSZVIUIRZSZVKSZBNPUAPBUFUJOBUKUJUDNBULUJZUMUAVR
      UNZNCDEVHFVIUAGABUORVMVOVKHTAFQRZVMVOVKITAEQRZVMVOVKJTAVMVOVKUPVNVOVKUQVQ
      VGVAVJAVGVAUDVMVOVKKTVPVKURUSVSUTVBAWAVTSVKMUIUMLQUMAWAVTJIVCLMEFVDVEVF
      $.
  $}

  ${
    $d A x y $.  $d N x y $.  $d ph x y $.
    remexz.1 $e |- ( ph -> N e. ZZ ) $.
    remexz.2 $e |- ( ph -> A e. NN ) $.
    $( Division with rest.  (Contributed by metakunt, 15-May-2025.) $)
    remexz $p |- ( ph -> E. x e. ZZ E. y e. ( 0 ... ( A - 1 ) )
     N = ( ( x x. A ) + y ) ) $=
      ( cv cmul co caddc wceq cz wrex cc0 c1 cmin cfz wcel syl2anc cfzo zmodfzo
      cmo cn nnzd fzoval syl eleqtrd wa simpr oveq2d eqeq2d rexbidv eqidd nnrpd
      crp wi modmuladdim mpd rspcedvd rexcom sylibr ) AEBHDIJZCHZKJZLZBMNZCODPQ
      JRJZNVFCVHNBMNAVGEVCEDUCJZKJZLZBMNZCVIVHAVIODUAJZVHAEMSZDUDSVIVMSFGEDUBTA
      DMSVMVHLADGUEODUFUGUHAVDVILZUIZVFVKBMVPVEVJEVPVDVIVCKAVOUJUKULUMAVIVILZVL
      AVIUNAVNDUPSVQVLUQFADGUOEVIBDURTUSUTVFBCMVHVAVB $.
  $}

  ${
    $d K l $.  $d M l $.  $d N l $.  $d R l $.  $d l ph $.
    primrootlekpowne0.1 $e |- ( ph -> R e. CMnd ) $.
    primrootlekpowne0.2 $e |- ( ph -> K e. NN ) $.
    primrootlekpowne0.3 $e |- ( ph -> M e. ( R PrimRoots K ) ) $.
    primrootlekpowne0.4 $e |- ( ph -> N e. ( 1 ... ( K - 1 ) ) ) $.
    $( There is no smaller power of a primitive root that sends it to the
       neutral element.  (Contributed by metakunt, 15-May-2025.) $)
    primrootlekpowne0 $p |- ( ph -> ( N ( .g ` R ) M ) =/=
     ( 0g ` R ) ) $=
      ( vl cfv co wceq cdvds wbr wi cn0 wcel adantr c1 cmg c0g wne wa cv eqeq1d
      oveq1 breq2 imbi12d wral cbs cprimroots w3a nnnn0d eqid isprimroot biimpd
      mpd simp3d cmin cfz cn elfznn syl rspcdva syldbl2 cle nnred 1red resubcld
      wn clt elfzle2 ltm1d lelttrd ltnled mpbid cz nn0zd syl2anc con3d pm2.21dd
      dvdsle simpr pm2.61dane ) AEDBUAKZLZBUBKZUCZWGWHAWGWHMZUDZCENOZWIAWJWLWKJ
      UEZDWFLZWHMZCWMNOZPZWJWLPJQEWMEMZWOWJWPWLWRWNWGWHWMEDWFUGUFWMECNUHUIAWQJQ
      UJZWJADBUKKRZCDWFLWHMZWSADBCULLRZWTXAWSUMZHAXBXCABWFCDJFACGUNZWFUOUPUQURU
      SSAEQRWJAEAETCTUTLZVALRZEVBRZIEXEVCVDZUNSVEVFAWLVKZWJACEVGOZVKZXIAECVLOXK
      AEXECAEXHVHZACTACGVHZAVIVJXMAXFEXEVGOIETXEVMVDACXMVNVOAECXLXMVPVQAWLXJACV
      RRXGWLXJPACXDVSXHCEWCVTWAURSWBAWIWDWE $.
  $}

  ${
    $d K l $.  $d K x y $.  $d M l $.  $d M x y $.  $d N x y $.  $d R a i $.
    $d R l $.  $d R x y $.  $d U l $.  $d U x y $.  $d l ph $.  $d ph x y $.
    primrootspoweq0.1 $e |- ( ph -> R e. CMnd ) $.
    primrootspoweq0.2 $e |- ( ph -> K e. NN ) $.
    primrootspoweq0.3 $e |- ( ph -> M e. ( R PrimRoots K ) ) $.
    primrootspoweq0.4 $e |- U = { a e. ( Base ` R ) |
     E. i e. ( Base ` R ) ( i ( +g ` R ) a ) = ( 0g ` R ) } $.
    primrootspoweq0.5 $e |- ( ph -> N e. ZZ ) $.
    $( The power of a ` R ` -th primitive root is zero if and only if it
       divides ` R ` .  (Contributed by metakunt, 15-May-2025.) $)
    primrootspoweq0 $p |- ( ph -> ( ( N ( .g ` ( R |`s U ) ) M ) =
     ( 0g ` ( R |`s U ) ) <-> K || N ) ) $=
      ( co wceq cz cc0 c1 wcel wa vx vy vl cv caddc cress cmg cfv c0g cdvds wbr
      cmul wb cmin cfz wn simplr oveq1d cplusg cbs w3a cprimroots primrootsunit
      cgrp cabl simprd ad4antr ablgrpd simp-4r nnzd zmulcld simpllr elfzelzd wi
      cn0 wral simpld eleqtrd ccmn ablcmn syl nnnn0d eqid isprimroot biimpd mpd
      simp1d 3jca mulgdir syl2anc mulgass simp2d mulgz eqtrd mulgcld grplidd cn
      oveq2d wo cuz cle 1cnd addlidd nnge1d eqbrtrd cr 0red 1red nnred leaddsub
      syl3anc 0zd 1zzd zsubcld eluz mpbird elfzp12 simp-5r adantr dvdsmul2 zcnd
      mpbid nncnd mulcld addridd eqcomd simpr breqtrd pm2.21dd ex ssidd eqsstrd
      sseld jaod primrootlekpowne0 eqnetrd neneqd wrex ad3antrrr nfv jca ablgrp
      con4d simp-4l divides oveq1 eqeq1d cbvrexw bilani impbid remexz r19.29vva
      imp r19.29a ) AGUAUDZEULNZUBUDZUENZOZGFBCUFNZUGUHZNZUUTUIUHZOZEGUJUKZUMUA
      UBPQERUNNZUONZAUUOPSZTZUUQUVGSZTZUUSTZUVDUVEUVLUVEUVDUVLUVEUPZUVDUPUVLUVM
      TZUVBUVCUVNUVBUUQFUVANZUVCUVNUVBUURFUVANZUVOUVNGUURFUVAUVKUUSUVMUQZURUVNU
      VPUUPFUVANZUVOUUTUSUHZNZUVOUVNUUTVDSZUUPPSZUUQPSZFUUTUTUHZSZVAUVPUVTOUVNU
      UTAUUTVESZUVHUVJUUSUVMABEVBNZUUTEVBNZOZUWFABCDEHIJLVCZVFZVGZVHZUVNUWBUWCU
      WEUVNUUOEAUVHUVJUUSUVMVIZAEPSZUVHUVJUUSUVMAEJVJZVGZVKUVNUUQQUVFUVIUVJUUSU
      VMVLZVMZAUWEUVHUVJUUSUVMAUWEEFUVANZUVCOZUCUDZFUVANUVCOEUXBUJUKVNUCVOVPZAF
      UWHSZUWEUXAUXCVAZAFUWGUWHKAUWIUWFUWJVQZVRAUXDUXEAUUTUVAEFUCAUWFUUTVSSZUWK
      UUTVTZWAAEJWBUVAWCZWDWEWFZWGZVGZWHUWDUVSUVAUUTUUPUUQFUWDWCZUXIUVSWCZWIWJU
      VNUVTUVCUVOUVSNUVOUVNUVRUVCUVOUVSUVNUVRUUOUWTUVANZUVCUVNUWAUVHUWOUWEVAUVR
      UXOOUWMUVNUVHUWOUWEUWNUWQUXLWHUWDUVAUUTUUOEFUXMUXIWKWJUVNUXOUUOUVCUVANZUV
      CUVNUWTUVCUUOUVAAUXAUVHUVJUUSUVMAUWEUXAUXCUXJWLZVGWRUVNUWAUVHUXPUVCOUWMUW
      NUWDUVAUUTUUOUVCUXMUXIUVCWCZWMWJWNWNURUVNUWDUVSUUTUVOUVCUXMUXNUXRUWMUVNUW
      DUVAUUTUUQFUXMUXIUWMUWSUXLWOWPWNWNWNUVNUUTEFUUQUVNUWFUXGUWLUXHWAAEWQSZUVH
      UVJUUSUVMJVGZUVNFUWGUWHAFUWGSUVHUVJUUSUVMKVGAUWIUVHUVJUUSUVMUXFVGVRUVNUUQ
      QOZUUQQRUENZUVFUONZSZWSZUUQRUVFUONZSZUVNUVJUYEUWRUVNUVJUYEAUVJUYEUMZUVHUV
      JUUSUVMAUVFQWTUHSZUYHAUYIQUVFXAUKZAUYBEXAUKZUYJAUYBREXAARAXBXCAEJXDXEAQXF
      SRXFSEXFSUYKUYJUMAXGAXHAEJXIQREXJXKYBAQPSUVFPSUYIUYJUMAXLAERUWPAXMXNQUVFX
      OWJXPUUQQUVFXQWAVGWEWFUVNUYAUYGUYDUVNUYAUYGUVNUYATZUVEUYGUYLEUURGUJUYLEUU
      PUURUJUYLUVHUWOEUUPUJUKAUVHUVJUUSUVMUYAXRZUYLEUVNUXSUYAUXTXSZVJUUOEXTWJUY
      LUUPUUPQUENZUURUYLUYOUUPUYLUUPUYLUUOEUYLUUOUYMYAUYLEUYNYCYDYEYFUYLQUUQUUP
      UEUYLUUQQUVNUYAYGYFWRWNYHUYLGUURUVNUUSUYAUVQXSYFYHUVLUVMUYAUQYIYJUVNUYCUY
      FUUQUVNUYCUYFUYFUVNUYBRUVFUOUVNRUVNXBXCURUVNUYFYKYLYMYNWFYOYPYQYJUUCUVLUV
      EUVDUVLUVETZAUVETZUVDUYPAUVEAUVHUVJUUSUVEUUDUVLUVEYGUUAUYQUUPGOZUAPYRZUVD
      AUVEUYSAUVEUYSAUWOGPSUVEUYSUMUWPMUAEGUUEWJWEUUMAUYSUVDVNUVEAUYSUVDAUYSTZU
      UQEULNZGOZUVDUBPUYTUWCTZVUBTZUVBVUAFUVANZUVCVUDGVUAFUVAVUDVUAGVUCVUBYGYFU
      RVUDVUEUUQUWTUVANZUVCVUDUWAUWCUWOUWEVAVUEVUFOVUDUWFUWAAUWFUYSUWCVUBUWKYSU
      UTUUBWAZVUDUWCUWOUWEUYTUWCVUBUQZAUWOUYSUWCVUBUWPYSAUWEUYSUWCVUBUXKYSWHUWD
      UVAUUTUUQEFUXMUXIWKWJVUDVUFUUQUVCUVANZUVCVUDUWTUVCUUQUVAAUXAUYSUWCVUBUXQY
      SWRVUDUWAUWCVUIUVCOVUGVUHUWDUVAUUTUUQUVCUXMUXIUXRWMWJWNWNWNUYSVUBUBPYRAUY
      RVUBUAUBPUYRUBYTVUBUAYTUUOUUQOUUPVUAGUUOUUQEULUUFUUGUUHUUIUUNYJXSWFWAYJUU
      JAUAUBEGMJUUKUUL $.
  $}

  ${
    $d .^ e f $.  $d B e f $.  $d D e f $.  $d E e f y $.  $d F e f y $.
    $d K e f $.  $d O e f $.  $d R e f $.
    aks6d1c1p1.1 $e |- .~ = { <. e , f >. | ( e e. NN /\ f e. B /\
    A. y e. ( K PrimRoots R )
     ( e .^ ( ( O ` f ) ` y ) ) = ( ( O ` f ) ` ( e D y ) ) ) } $.
    aks6d1c1p1.2 $e |- ( ph -> F e. B ) $.
    aks6d1c1p1.3 $e |- ( ph -> E e. NN ) $.
    $( Definition of the introspective relation.  (Contributed by metakunt,
       25-Apr-2025.) $)
    aks6d1c1p1 $p |- ( ph -> ( E .~ F <-> A. y e. ( K PrimRoots R )
     ( E .^ ( ( O ` F ) ` y ) ) = ( ( O ` F ) ` ( E D y ) ) ) ) $=
      ( cfv co wceq wa wbr cv cprimroots wral cn wcel w3a wb simpl eleq1d simpr
      fveq2d fveq1d oveq12d oveq1d fveq12d eqeq12d ralbidv 3anbi123d brabga imp
      syl2anc biimpd simp3d jca df-3an bicomi a1i biimprd sylbid anassrs impbid
      ex wi mpdan ) AIKEUAZIBUBZKMQZQZJRZIVQDRZVRQZSZBLFUCRZUDZAVPWEAVPTIUEUFZK
      CUFZWEAVPWFWGWEUGZAVPWHAWFWGVPWHUHPOGUBZUEUFZHUBZCUFZWIVQWKMQZQZJRZWIVQDR
      ZWMQZSZBWDUDZUGWHGHIKEUECWIISZWKKSZTZWJWFWLWGWSWEXBWIIUEWTXAUIZUJXBWKKCWT
      XAUKZUJXBWRWCBWDXBWOVTWQWBXBWIIWNVSJXCXBVQWMVRXBWKKMXDULZUMUNXBWPWAWMVRXE
      XBWIIVQDXCUOUPUQURUSNUTVBZVCVAVDVMAWFWGTZWEVPVNAWFWGPOVEAXGTWEVPAXGWEVPAX
      GWETZVPAXHWHVPXHWHUHAWHXHWFWGWEVFVGVHAVPWHXFVIVJVAVKVMVOVL $.
  $}

  ${
    $d B e f $.
    aks6d1c1p1rcl.1 $e |- .~ = { <. e , f >. | ( e e. NN /\ f e. B /\
    A. y e. ( K PrimRoots R )
     ( e .^ ( ( O ` f ) ` y ) ) = ( ( O ` f ) ` ( e D y ) ) ) } $.
    aks6d1c1p1rcl.2 $e |- ( ph -> E .~ F ) $.
    $( Reverse closure of the introspective relation.  (Contributed by
       metakunt, 25-Apr-2025.) $)
    aks6d1c1p1rcl $p |- ( ph -> ( E e. NN /\ F e. B ) ) $=
      ( cn wcel wa cv cfv wbr wceq cprimroots wral copab cxp w3a df-3an opabbii
      co eqtri opabssxp eqsstri brel syl ) AIKEUAIPQKCQROIKPCEEGSZPQZHSZCQZRUPB
      SZURMTZTJUJUPUTDUJVATUBBLFUCUJUDZRZGHUEZPCUFEUQUSVBUGZGHUEVDNVEVCGHUQUSVB
      UHUIUKVBGHPCULUMUNUO $.
  $}

  ${
    $d .^ e f $.  $d B e f $.  $d F e f y $.  $d O e f $.  $d P e f y $.
    $d R e f $.  $d R l $.  $d V e f $.  $d V l $.  $d l ph y $.
    aks6d1c1p2.1 $e |- .~ = { <. e , f >. | ( e e. NN /\ f e. B /\
    A. y e. ( V PrimRoots R )
     ( e .^ ( ( O ` f ) ` y ) ) = ( ( O ` f ) ` ( e .^ y ) ) ) } $.
    aks6d1c1p2.2 $e |- S = ( Poly1 ` K ) $.
    aks6d1c1p2.3 $e |- B = ( Base ` S ) $.
    aks6d1c1p2.4 $e |- X = ( var1 ` K ) $.
    aks6d1c1p2.5 $e |- W = ( mulGrp ` S ) $.
    aks6d1c1p2.6 $e |- V = ( mulGrp ` K ) $.
    aks6d1c1p2.7 $e |- .^ = ( .g ` V ) $.
    aks6d1c1p2.8 $e |- C = ( algSc ` S ) $.
    aks6d1c1p2.9 $e |- D = ( .g ` W ) $.
    aks6d1c1p2.10 $e |- P = ( chr ` K ) $.
    aks6d1c1p2.11 $e |- O = ( eval1 ` K ) $.
    aks6d1c1p2.12 $e |- .+ = ( +g ` S ) $.
    aks6d1c1p2.13 $e |- ( ph -> K e. Field ) $.
    aks6d1c1p2.14 $e |- ( ph -> P e. Prime ) $.
    aks6d1c1p2.15 $e |- ( ph -> R e. NN ) $.
    aks6d1c1p2.16 $e |- ( ph -> ( N gcd R ) = 1 ) $.
    aks6d1c1p2.17 $e |- ( ph -> P || N ) $.
    aks6d1c1p2.18 $e |- F = ( X .+ ( C ` ( ( ZRHom ` K ) ` A ) ) ) $.
    aks6d1c1p2.19 $e |- ( ph -> A e. ZZ ) $.
    $( ` P ` and linear factors are introspective.  (Contributed by metakunt,
       25-Apr-2025.) $)
    aks6d1c1p2 $p |- ( ph -> P .~ F ) $=
      ( vl wbr cv cfv co wceq cprimroots wral wcel cbs wa c0g cdvds wi cn0 ccrg
      w3a ccmn cdr cfield isfld simprd crngmgp syl nnnn0d isprimroot biimpd imp
      sylib simp1d eqid mgpbas eqcomi adantr eleq2d mpbid ex czrh cplusg fveq2d
      a1i fveq1d oveq2d simpr crg crngring 3syl evl1vard jca cz czring crh cghm
      wf crngringd zrhrhm rhmghm zringbas ghmf 4syl ffvelcdmd ply1sclcl syl2anc
      vr1cl evl1scad evl1addd eqtrd cmnd ringmgp cprime prmnn eleqtrdi cmg cmgp
      cn fveq2i eqtri evl1expd eqcomd mpbird ply1fermltlchr 3eqtrd adantlr mpdd
      mulgnn0cld eqidd ralrimiva cgrp ply1crng ringgrpd grpcl eleq1d aks6d1c1p1
      3jca ) AGOIVBGBVCZORVDZVDZNVEZGUUONVEZUUPVDZVFZBSJVGVEZVHAUVABUVBAUUOUVBV
      IZUVAAUVCUUOPVJVDZVIZUVAAUVCUVEAUVCVKZUUOSVJVDZVIZUVEUVFUVHJUUONVESVLVDZV
      FZVAVCZUUONVEUVIVFJUVKVMVBVNVAVOVHZAUVCUVHUVJUVLVQZAUVCUVMASNJUUOVAAPVPVI
      ZSVRVIAPVSVIZUVNAPVTVIUVOUVNVKUNPWAWIWBZPSUGWCWDAJUPWEUHWFWGWHWJUVFUVGUVD
      UUOAUVGUVDVFZUVCUVQAUVDUVGUVDPSUGUVDWKZWLZWMZXAWNWOWPWQAUVCUVEUVAVNUVFUVE
      UVAAUVEUVAUVCAUVEVKZUURGUUOCPWRVDZVDZPWSVDZVEZNVEZUUTUWAUURGUUOUAUWCEVDZH
      VEZRVDZVDZNVEUWFUWAUUQUWJGNUWAUUOUUPUWIUWAOUWHROUWHVFZUWAUSXAWTZXBXCUWAUW
      JUWEGNUWAUWHDVIZUWJUWEVFUWAUVDKUWDHPDUAUWGRUUOUWCUUOULUCUVRUDAUVNUVEUVPWN
      ZAUVEXDZUWAUADVIZUUOUARVDVDUUOVFZUWAUVNPXEVIZUWPUWNPXFZDKPUAUEUCUDYDZXGUW
      AUWPUWQUWAUVDKPDRUAUUOULUEUVRUCUDUWNUWOXHZWBXIUWAUWGDVIZUUOUWGRVDZVDUWCVF
      ZAUXBUVEAUWRUWCUVDVIZUXBAUVNUWRUVPUWSWDAXJUVDCUWBAUWRUWBXKPXLVEVIUWBXKPXM
      VEVIXJUVDUWBXNAPUVPXOZPUWBUWBWKXPXKPUWBXQXKPUWBXJUVDXRUVRXSXTUTYAZEDKPUWC
      UVDUCUIUVRUDYBYCZWNZUWAUXBUXDUWAEUVDKPDRUWCUUOULUCUVRUIUDUWNAUXEUVEUXGWNZ
      UWOYEZWBXIZUMUWDWKZYFWBXCYGUWAUUTUWFUWAUUTUUSUWCUWDVEZUWFUWAUUTUUSUWIVDZU
      XNUWAUUSUUPUWIUWLXBUWAUWMUXOUXNVFUWAUVDKUWDHPDUAUWGRUUSUWCUUSULUCUVRUDUWN
      UWAUUSUVGUVDUWAUVGNSGUUOUVGWKUHUWAUVNUWRSYHVIUWNUWSPSUGYIXGAGVOVIUVEAGAGY
      JVIGYOVIUOGYKWDZWEWNZUWAUUOUVDUVGUWOUVSYLUUEUVTYLZUWAUVDKPDRUAUUSULUEUVRU
      CUDUWNUXRXHUWAUXBUUSUXCVDUWCVFZUXIUWAUXBUXSUWAEUVDKPDRUWCUUSULUCUVRUIUDUW
      NUXJUXRYEWBXIUMUXMYFWBYGUWAUXNUUOGUAFVEZUWGKWSVDZVEZRVDZVDZUUOGUAUWGUYAVE
      ZFVEZRVDZVDZUWFUWAUYDUXNUWAUYDUXNUXNUWAUYBDVIUYDUXNVFUWAUVDKUWDUYAPDUXTUW
      GRUUSUWCUUOULUCUVRUDUWNUWOUWAUVDKPFDNUAGRUUOUUOULUCUVRUDUWNUWOUXAFTYMVDKY
      NVDZYMVDUJTUYIYMUFYPYQZNSYMVDPYNVDZYMVDUHSUYKYMUGYPYQZUXQYRUXLUYAWKZUXMYF
      WBUWAUXNUUFYGYSAUYDUYHVFUVEAUYHUYDAUUOUYGUYCAUYFUYBRAUWGEGUYACFPTKUAUCUEU
      YMUFUJUIUWGWKUKUVPUOUTUUAWTXBYSWNUWAUYFDVIUYHUWFVFUWAUVDKPFDNUYEGRUWEUUOU
      LUCUVRUDUWNUWOUWAUVDKUWDUYAPDUAUWGRUUOUWCUUOULUCUVRUDUWNUWOUXAUXKUYMUXMYF
      UYJUYLUXQYRWBUUBYGYSYGUUCWQWQUUDWHUUGABDNIJLMGNOSRUBAODVIUWMAKUUHVIZUWPUX
      BVQUWMAUYNUWPUXBAKAKVPVIZKXEVIAUVNUYOUVPKPUCUUIWDKXFWDUUJAUWRUWPUXFUWTWDU
      XHUUNDHKUAUWGUDUMUUKWDAOUWHDUWKAUSXAUULYTUXPUUMYT $.
  $}

  ${
    $d .^ e f y $.  $d .^ x y $.  $d .^ y z $.  $d A x $.  $d B e f $.
    $d F e f y $.  $d F y z $.  $d K x $.  $d N e f y $.  $d N x y $.
    $d N y z $.  $d O e f y $.  $d O y z $.  $d P e f y $.  $d P x y $.
    $d R e f y $.  $d R l y $.  $d R x y $.  $d R y z $.  $d V e f y $.
    $d V l y $.  $d V x y $.  $d V y z $.  $d l ph y $.  $d ph x y $.
    aks6d1c1p3.1 $e |- .~ = { <. e , f >. | ( e e. NN /\ f e. B /\
    A. y e. ( V PrimRoots R )
     ( e .^ ( ( O ` f ) ` y ) ) = ( ( O ` f ) ` ( e .^ y ) ) ) } $.
    aks6d1c1p3.2 $e |- S = ( Poly1 ` K ) $.
    aks6d1c1p3.3 $e |- B = ( Base ` S ) $.
    aks6d1c1p3.4 $e |- X = ( var1 ` K ) $.
    aks6d1c1p3.5 $e |- W = ( mulGrp ` S ) $.
    aks6d1c1p3.6 $e |- V = ( mulGrp ` K ) $.
    aks6d1c1p3.7 $e |- .^ = ( .g ` V ) $.
    aks6d1c1p3.8 $e |- C = ( algSc ` S ) $.
    aks6d1c1p3.9 $e |- D = ( .g ` W ) $.
    aks6d1c1p3.10 $e |- P = ( chr ` K ) $.
    aks6d1c1p3.11 $e |- O = ( eval1 ` K ) $.
    aks6d1c1p3.12 $e |- .+ = ( +g ` S ) $.
    aks6d1c1p3.13 $e |- ( ph -> K e. Field ) $.
    aks6d1c1p3.14 $e |- ( ph -> P e. Prime ) $.
    aks6d1c1p3.15 $e |- ( ph -> R e. NN ) $.
    aks6d1c1p3.16 $e |- ( ph -> ( N gcd R ) = 1 ) $.
    aks6d1c1p3.17 $e |- ( ph -> P || N ) $.
    aks6d1c1p3.18 $e |- F = ( X .+ ( C ` ( ( ZRHom ` K ) ` A ) ) ) $.
    aks6d1c1p3.19 $e |- ( ph -> A e. ZZ ) $.
    aks6d1c1p3.20 $e |- ( ph -> N .~ F ) $.
    aks6d1c1p3.21 $e |- ( ph -> ( x e. ( Base ` K ) |-> ( P .^ x ) )
     e. ( K RingIso K ) ) $.
    $( In a field with a Frobenius isomorphism (read: algebraic closure or
       finite field), ` N ` and linear factors are introspective.  (Contributed
       by metakunt, 25-Apr-2025.) $)
    aks6d1c1p3 $p |- ( ph -> ( N / P ) .~ F ) $=
      ( vl vz cdiv co wbr cv cfv wceq cprimroots wral wcel wa cplusg a1i fveq2d
      czrh fveq1d cbs eqid ccrg fldcrngd adantr cmnd ccmn crngmgp cmnmndd cdvds
      syl cn0 cn wb aks6d1c1p1rcl simpld syl2anc mpbid nnnn0d mulgnn0cld mgpbas
      w3a eleqtrd evl1vard cz czring cghm rhmghm evl1scad evl1addd simprd eqtrd
      crh oveq2d crnggrpd grpcld f1ocnvfv1 eqcomd id adantl cmg fvmptd eqeltrrd
      sylib oveq12d 3eqtrd cc nncnd oveq1d fveq2 eqeq12d 3jca mpbird aks6d1c1p1
      oveq2 jca eqtr2d eleqtrdi mulgnn0ass eqtr3d cprime prmnn nndivdvds c0g wi
      isprimroot biimpd imp simp1d eqcomi crg wf crngringd zrhrhm zringbas ghmf
      4syl ffvelcdmd eleq2d cmpt ccnv wf1o crs isrim eqidd fveq2i eqtri ringmgp
      cmgp ghmlin syl3anc fermltlchr cmul cc0 wne nnne0d divcan2d cgrp ply1crng
      vr1cl ply1sclcl grpcl eleq1d cbvralvw simpr rspcdva ralrimiva ) ARHVFVGZP
      JVHUWHCVIZPSVJZVJZOVGZUWHUWIOVGZUWJVJZVKZCTKVLVGZVMAUWOCUWPAUWIUWPVNZVOZU
      WNUWLUWRUWNUWMDQVSVJZVJZQVPVJZVGZUWLUWRUWNUWMUBUWTFVJZIVGZSVJZVJZUXBUWRUW
      MUWJUXEUWRPUXDSPUXDVKZUWRUTVQVRZVTUWRUXDEVNZUXFUXBVKUWRQWAVJZLUXAIQEUBUXC
      SUWMUWTUWMUMUDUXJWBZUEAQWCVNZUWQAQUOWDZWEZUWRUWMTWAVJZUXJUWRUXOOTUWHUWIUX
      OWBZUIATWFVNUWQATAUXLTWGVNUXMQTUHWHWKZWIWEZAUWHWLVNZUWQAUWHAHRWJVHZUWHWMV
      NZUSARWMVNZHWMVNZUXTUYAWNAUYBPEVNZACEOJKMNROPTSUCVBWOWPZAHUUAVNUYCUPHUUBW
      KZRHUUCWQWRZWSWEZUWRUWIUXOVNZKUWIOVGTUUDVJZVKZVDVIZUWIOVGUYJVKKUYLWJVHUUE
      VDWLVMZAUWQUYIUYKUYMXBZAUWQUYNATOKUWIVDUXQAKUQWSUIUUFUUGUUHUUIZWTAUXOUXJV
      KZUWQUYPAUXJUXOUXJQTUHUXKXAUUJZVQWEZXCZUWRUXJLQESUBUWMUMUFUXKUDUEUXNUYSXD
      UWRFUXJLQESUWTUWMUMUDUXKUJUEUXNAUWTUXJVNZUWQAXEUXJDUWSAQUUKVNZUWSXFQXMVGV
      NUWSXFQXGVGVNXEUXJUWSUULAQUXMUUMZQUWSUWSWBUUNXFQUWSXHXFQUWSXEUXJUUOUXKUUP
      UUQVAUURZWEZUYSXIUNUXAWBZXJXKXLUWRUWLUWHUWIUWTUXAVGZOVGZUXBUWRUWLUWHUWIUX
      EVJZOVGVUGUWRUWKVUHUWHOUWRUWIUWJUXEUXHVTZXNUWRVUHVUFUWHOUWRUXIVUHVUFVKUWR
      UXJLUXAIQEUBUXCSUWIUWTUWIUMUDUXKUEUXNUWRUYIUWIUXJVNUYOUWRUXOUXJUWIUYRUUSW
      RZUWRUXOLQESUBUWIUMUFUYQUDUEUXNUYOXDUWRFUXJLQESUWTUWIUMUDUXKUJUEUXNVUDVUJ
      XIUNVUEXJXKZXNXLUWRUXBVUGUWRUXBUXBBUXJHBVIZOVGZUUTZVJZVUNUVAZVJZVUGVUNVJZ
      VUPVJZVUGUWRVUQUXBUWRUXJUXJVUNUVBZUXBUXJVNVUQUXBVKAVUTUWQAVUNQQXMVGVNZVUT
      AVUNQQUVCVGVNVVAVUTVOVCUXJUXJQQVUNUXKUXKUVDYDZXKWEZUWRUXJUXAQUWMUWTUXKVUE
      UWRQUXNXOZUYSVUDXPZUXJUXJUXBVUNXQWQXRUWRVUOVURVUPUWRVUOHUXBOVGZHVUGOVGZVU
      RUWRBUXBVUMVVFUXJVUNUXJUWRVUNUVEZUWRVULUXBVKZVOVULUXBHOVVIVVIUWRVVIXSXTXN
      VVEUWRUXJOQUVIVJZHUXBUXJQVVJVVJWBZUXKXAZOTYAVJVVJYAVJUITVVJYAUHUVFUVGZAVV
      JWFVNZUWQAVUAVVNVUBQVVJVVKUVHWKWEZAHWLVNZUWQAHUYFWSWEZVVEWTZYBZUWRVVFHUWM
      OVGZHUWTOVGZUXAVGZVVGUWRVVFVUOUWMVUNVJZUWTVUNVJZUXAVGZVWBUWRVUOVVFVVSXRUW
      RVUNQQXGVGVNZUWMUXJVNUYTVUOVWEVKAVWFUWQAVVAVWFAVVAVUTVVBWPQQVUNXHWKWEUYSV
      UDUXAUXAQQUWMVUNUWTUXJUXKVUEVUEUVJUVKUWRVWCVVTVWDVWAUXAUWRBUWMVUMVVTUXJVU
      NUXJVVHUWRVULUWMVKZVOVULUWMHOVWGVWGUWRVWGXSXTXNUYSUWRUXJOVVJHUWMVVLVVMVVO
      VVQUYSWTYBUWRBUWTVUMVWAUXJVUNUXJVVHVULUWTVKZVUMVWAVKUWRVWHVULUWTHOVWHXSXN
      XTVUDUWRUWTVWAUXJAUWTVWAVKUWQAVWAUWTAUWTUXJHDOQULUXKVVMUWTWBUPVAUXMUVLXRW
      EZVUDYCYBYEYFUWRHUWHUVMVGZVUFOVGZVWBVVGUWRVWJUWIOVGZVWAUXAVGZVWKVWBUWRVWK
      RUWIOVGZUWTUXAVGZVWMUWRVWKRVUFOVGZVWOUWRVWJRVUFOUWRRHARYGVNUWQARUYEYHWEAH
      YGVNUWQAHUYFYHWEAHUVNUVOUWQAHUYFUVPWEUVQZYIUWRVWPRUWKOVGZVWOUWRVWRVWPUWRV
      WRRVUHOVGVWPUWRUWKVUHROVUIXNUWRVUHVUFROVUKXNXLXRUWRVWRVWNUWJVJZVWOUWRRVEV
      IZUWJVJZOVGZRVWTOVGZUWJVJZVKZVWRVWSVKZVEUWPUWIVWTUWIVKZVXBVWRVXDVWSVXGVXA
      UWKROVWTUWIUWJYJXNVXGVXCVWNUWJVWTUWIROYOVRYKAVXEVEUWPVMZUWQAVXFCUWPVMZVXH
      ARPJVHVXIVBACEOJKMNROPTSUCAUYDUXIALUVRVNZUBEVNZUXCEVNZXBUXIAVXJVXKVXLALAU
      XLLWCVNUXMLQUDUVSWKXOAVUAVXKVUBELQUBUFUDUEUVTWKZAVUAUYTVXLVUBVUCFELQUWTUX
      JUDUJUXKUEUWAWQZYLEILUBUXCUEUNUWBWKAPUXDEUXGAUTVQUWCYMZUYEYNWRVXFVXECVEUW
      PUWIVWTVKZVWRVXBVWSVXDVXPUWKVXAROUWIVWTUWJYJXNVXPVWNVXCUWJUWIVWTROYOVRYKU
      WDYDWEAUWQUWEUWFUWRVWSVWNUXEVJZVWOUWRVWNUWJUXEUXHVTUWRUXIVXQVWOVKUWRUXJLU
      XAIQEUBUXCSVWNUWTVWNUMUDUXKUEUXNUWRVWNUXOUXJUWRUXOOTRUWIUXPUIUXRARWLVNUWQ
      ARUYEWSWEUYOWTUYRXCZUWRVXKVWNUBSVJVJVWNVKZAVXKUWQVXMWEUWRVXKVXSUWRUXJLQES
      UBVWNUMUFUXKUDUEUXNVXRXDXKYPUWRVXLVWNUXCSVJVJUWTVKZAVXLUWQVXNWEUWRVXLVXTU
      WRFUXJLQESUWTVWNUMUDUXKUJUEUXNVUDVXRXIXKYPUNVUEXJXKXLXLXLXLUWRVWNVWLUWTVW
      AUXAUWRRVWJUWIOUWRVWJRVWQXRYIVWIYEYQUWRVWLVVTVWAUXAUWRVVNVVPUXSUWIVVJWAVJ
      ZVNZXBVWLVVTVKVVOUWRVVPUXSVYBVVQUYHUWRUWIUXJVYAVUJVVLYRYLVYAOVVJHUWHUWIVY
      AWBZVVMYSWQYIYTUWRVVNVVPUXSVUFVYAVNZXBVWKVVGVKVVOUWRVVPUXSVYDVVQUYHUWRVUF
      UXJVYAUWRUXJUXAQUWIUWTUXKVUEVVDVUJVUDXPZVVLYRYLVYAOVVJHUWHVUFVYCVVMYSWQYT
      XLZUWRVURVVGUWRBVUGVUMVVGUXJVUNUXJVVHVULVUGVKZVUMVVGVKUWRVYGVULVUGHOVYGXS
      XNXTUWRUXJOVVJUWHVUFVVLVVMVVOUYHVYEWTZUWRVVFVVGUXJVYFVVRYCYBXRYFVRUWRVUTV
      UGUXJVNVUSVUGVKVVCVYHUXJUXJVUGVUNXQWQYFXRYQXLXRUWGACEOJKMNUWHOPTSUCVXOUYG
      YNYM $.
  $}

  ${
    $d .^ e f y $.  $d .^ y z $.  $d B e f $.  $d E e f y $.  $d E y z $.
    $d F e f y $.  $d F y z $.  $d G e f y $.  $d G y z $.  $d O e f y $.
    $d O y z $.  $d R e f y $.  $d R l y $.  $d R y z $.  $d V e f y $.
    $d V l y $.  $d V y z $.  $d W e f y $.  $d l ph y $.
    aks6d1c1p4.1 $e |- .~ = { <. e , f >. | ( e e. NN /\ f e. B /\
    A. y e. ( V PrimRoots R )
     ( e .^ ( ( O ` f ) ` y ) ) = ( ( O ` f ) ` ( e .^ y ) ) ) } $.
    aks6d1c1p4.2 $e |- S = ( Poly1 ` K ) $.
    aks6d1c1p4.3 $e |- B = ( Base ` S ) $.
    aks6d1c1p4.4 $e |- X = ( var1 ` K ) $.
    aks6d1c1p4.5 $e |- W = ( mulGrp ` S ) $.
    aks6d1c1p4.6 $e |- V = ( mulGrp ` K ) $.
    aks6d1c1p4.7 $e |- .^ = ( .g ` V ) $.
    aks6d1c1p4.8 $e |- C = ( algSc ` S ) $.
    aks6d1c1p4.9 $e |- D = ( .g ` W ) $.
    aks6d1c1p4.10 $e |- P = ( chr ` K ) $.
    aks6d1c1p4.11 $e |- O = ( eval1 ` K ) $.
    aks6d1c1p4.12 $e |- .+ = ( +g ` S ) $.
    aks6d1c1p4.13 $e |- ( ph -> K e. Field ) $.
    aks6d1c1p4.14 $e |- ( ph -> P e. Prime ) $.
    aks6d1c1p4.15 $e |- ( ph -> R e. NN ) $.
    aks6d1c1p4.16 $e |- ( ph -> ( N gcd R ) = 1 ) $.
    aks6d1c1p4.17 $e |- ( ph -> P || N ) $.
    aks6d1c1p4.18 $e |- ( ph -> E .~ F ) $.
    aks6d1c1p4.19 $e |- ( ph -> E .~ G ) $.
    $( The product of polynomials is introspective.  (Contributed by metakunt,
       25-Apr-2025.) $)
    aks6d1c1p4 $p |- ( ph -> E .~ ( F ( +g ` W ) G ) ) $=
      ( vl vz cplusg cfv co wbr cv wceq cprimroots wral wcel wa cmulr eqid ccrg
      cbs fldcrngd adantr mgpbas cmnd ccmn crngmgp syl cmnmndd cn aks6d1c1p1rcl
      cn0 simpld nnnn0d cmg c0g cdvds wi w3a isprimroot biimpd simp1d eleqtrrdi
      imp mulgnn0cld simprd eqidd jca mgpplusg eqcomi evl1muld cmgp fveval1fvcl
      fveq2i eqtr4i a1i eleq2d mpbid 3jca mulgnn0di syl2anc eqtri eqcomd oveq2d
      fveq2 oveq2 fveq2d eqeq12d aks6d1c1p1 cbvralvw sylib simpr rspcdva eqtr2d
      oveq123d oveqd eqtrd ralrimiva ply1crng crngringd ringcld mpbird ) AMOPUA
      VDVEZVFZHVGMBVHZYTSVEZVEZNVFZMUUANVFZUUBVEZVIZBTIVJVFZVKAUUGBUUHAUUAUUHVL
      ZVMZUUFUUDUUJUUFUUEOSVEZVEZUUEPSVEZVEZQVNVEZVFZUUDUUJYTCVLZUUFUUPVIUUJQVQ
      VEZJQYSUUOCOPSUULUUNUUEUMUDUURVOZUEAQVPVLZUUIAQUOVRZVSZUUJUURNTMUUAUURQTU
      HUUSVTZUIATWAVLUUIATAUUTTWBVLZUVAQTUHWCWDZWEVSAMWHVLZUUIAMAMWFVLZOCVLZABC
      NHIKLMNOTSUCUTWGZWIZWJVSZUUJUUATVQVEZUURUUJUUAUVLVLZIUUATWKVEZVFTWLVEZVIZ
      VBVHZUUAUVNVFUVOVIIUVQWMVGWNVBWHVKZAUUIUVMUVPUVRWOZAUUIUVSATUVNIUUAVBUVEA
      IUQWJUVNVOWPWQWTWRUVCWSZXAUUJUVHUULUULVIAUVHUUIAUVGUVHUVIXBZVSZUUJUULXCXD
      UUJPCVLZUUNUUNVIAUWCUUIAUVGUWCABCNHIKLMNPTSUCVAWGXBZVSZUUJUUNXCXDJVNVEZYS
      JUWFUAUGUWFVOXEXFZUUOVOZXGXBUUJUUPMUUAUUKVEZUUAUUMVEZUUOVFZNVFZUUDUUJUUPM
      UWIUWJQXHVEZVDVEZVFZNVFZUWLUUJUWPMUWINVFZMUWJNVFZUWNVFZUUPUUJUVDUVFUWIUWM
      VQVEZVLZUWJUWTVLZWOUWPUWSVIAUVDUUIUVEVSUUJUVFUXAUXBUVKUUJUWIUURVLUXAUUJUU
      RJQCOSUUAUMUDUUSUEUVBUVTUWBXIUUJUURUWTUWIUURUWTVIUUJUURUVLUWTUVCUWMTVQTUW
      MUHXFZXJZXKXLZXMXNUUJUWJUURVLUXBUUJUURJQCPSUUAUMUDUUSUEUVBUVTUWEXIUUJUURU
      WTUWJUXEXMXNXOUWTUWNNTMUWIUWJUXDUIUWMTVDUXCXJXPXQUUJUWQUULUWRUUNUWNUUOUUJ
      UUOUWNUUOUWNVIUUJUUOTVDVEUWNQUUOTUHUWHXETUWMVDUHXJXRZXLXSUUJMVCVHZUUKVEZN
      VFZMUXGNVFZUUKVEZVIZUWQUULVIZVCUUHUUAUXGUUAVIZUXIUWQUXKUULUXNUXHUWIMNUXGU
      UAUUKYAXTUXNUXJUUEUUKUXGUUAMNYBZYCYDAUXLVCUUHVKZUUIAUXMBUUHVKZUXPAMOHVGUX
      QUTABCNHIKLMNOTSUCUWAUVJYEXNUXMUXLBVCUUHUUAUXGVIZUWQUXIUULUXKUXRUWIUXHMNU
      UAUXGUUKYAXTUXRUUEUXJUUKUUAUXGMNYBZYCYDYFYGVSAUUIYHZYIUUJMUXGUUMVEZNVFZUX
      JUUMVEZVIZUWRUUNVIZVCUUHUUAUXNUYBUWRUYCUUNUXNUYAUWJMNUXGUUAUUMYAXTUXNUXJU
      UEUUMUXOYCYDAUYDVCUUHVKZUUIAUYEBUUHVKZUYFAMPHVGUYGVAABCNHIKLMNPTSUCUWDUVJ
      YEXNUYEUYDBVCUUHUXRUWRUYBUUNUYCUXRUWJUYAMNUUAUXGUUMYAXTUXRUUEUXJUUMUXSYCY
      DYFYGVSUXTYIYKYJUUJUWOUWKMNUUJUWNUUOUWIUWJUWNUUOVIUUJUUOUWNUXFXFXLYLXTYMU
      UJUWKUUCMNUUJUUCUWKUUJUUQUUCUWKVIUUJUURJQYSUUOCOPSUWIUWJUUAUMUDUUSUEUVBUV
      TUUJUVHUWIUWIVIUWBUUJUWIXCXDUUJUWCUWJUWJVIUWEUUJUWJXCXDUWGUWHXGXBXSXTYMYM
      XSYNABCNHIKLMNYTTSUCACJYSOPUEUWGAJAUUTJVPVLUVAJQUDYOWDYPUWAUWDYQUVJYEYR
      $.
  $}

  ${
    $d .^ e f y $.  $d .^ i l y $.  $d .^ y z $.  $d B e f $.  $d D e f y $.
    $d D i y $.  $d E e f y $.  $d E i l y $.  $d E y z $.  $d F e f y $.
    $d F i y $.  $d F y z $.  $d O e f y $.  $d O i y $.  $d O y z $.
    $d R e f y $.  $d R i l y $.  $d R q y $.  $d R y z $.  $d V e f y $.
    $d V i l y $.  $d V q y $.  $d V y z $.  $d l ph y $.  $d ph q y $.
    aks6d1c1p5.1 $e |- .~ = { <. e , f >. | ( e e. NN /\ f e. B /\
    A. y e. ( V PrimRoots R )
     ( e .^ ( ( O ` f ) ` y ) ) = ( ( O ` f ) ` ( e .^ y ) ) ) } $.
    aks6d1c1p5.2 $e |- S = ( Poly1 ` K ) $.
    aks6d1c1p5.3 $e |- B = ( Base ` S ) $.
    aks6d1c1p5.4 $e |- X = ( var1 ` K ) $.
    aks6d1c1p5.5 $e |- W = ( mulGrp ` S ) $.
    aks6d1c1p5.6 $e |- V = ( mulGrp ` K ) $.
    aks6d1c1p5.7 $e |- .^ = ( .g ` V ) $.
    aks6d1c1p5.8 $e |- C = ( algSc ` S ) $.
    aks6d1c1p5.10 $e |- P = ( chr ` K ) $.
    aks6d1c1p5.11 $e |- O = ( eval1 ` K ) $.
    aks6d1c1p5.12 $e |- .+ = ( +g ` S ) $.
    aks6d1c1p5.13 $e |- ( ph -> K e. Field ) $.
    aks6d1c1p5.14 $e |- ( ph -> P e. Prime ) $.
    aks6d1c1p5.15 $e |- ( ph -> R e. NN ) $.
    aks6d1c1p5.16 $e |- ( ph -> ( E gcd R ) = 1 ) $.
    aks6d1c1p5.17 $e |- ( ph -> P || N ) $.
    aks6d1c1p5.18 $e |- ( ph -> D .~ F ) $.
    aks6d1c1p5.19 $e |- ( ph -> E .~ F ) $.
    $( The product of exponents is introspective.  (Contributed by metakunt,
       26-Apr-2025.) $)
    aks6d1c1p5 $p |- ( ph -> ( D x. E ) .~ F ) $=
      ( vq vl vi vz cmul co wbr cv cfv wceq cprimroots wral wcel wa cn0 cbs w3a
      cmnd ccrg fldcrngd crngmgp syl cmnmndd adantr aks6d1c1p1rcl simpld nnnn0d
      ccmn cn eqid c0g cdvds wi isprimroot biimpd imp simp1d mgpbas a1i eleqtrd
      eqcomd simprd fveval1fvcl eleq2d 3jca mulgnn0ass syl2anc cmpt eqidd simpr
      mpbird oveq2d mulgnn0cld fvmptd fveq2d 2fveq3 fveq2 eqeq12d aks6d1c1p1 wb
      mpd wfo wf1o cmg oveqi mpteq2ia primrootscoprbij2 f1ofo oveq2 cbvfo eqtrd
      rspcdva eqtr2d nfv cbvralw sylibr 3eqtrd ralrimiva nnmulcld ) AEMVDVEZOHV
      FYSBVGZORVHZVHZNVEZYSYTNVEZUUAVHZVIZBSIVJVEZVKAUUFBUUGAYTUUGVLZVMZUUCEMUU
      BNVEZNVEZEMYTNVEZNVEZUUAVHZUUEUUISVQVLZEVNVLZMVNVLZUUBSVOVHZVLZVPUUCUUKVI
      AUUOUUHASAPVRVLZSWGVLAPUMVSZPSUGVTWAZWBWCZUUIUUPUUQUUSAUUPUUHAEAEWHVLZOCV
      LZABCNHIKLENOSRUBURWDZWEZWFWCZAUUQUUHAMAMWHVLUVEABCNHIKLMNOSRUBUSWDWEZWFW
      CZUUIUUSUUBPVOVHZVLUUIUVKJPCORYTUKUCUVKWIZUDAUUTUUHUVAWCUUIYTUURUVKUUIYTU
      URVLZIYTNVESWJVHZVIZUTVGZYTNVEUVNVIIUVPWKVFWLUTVNVKZAUUHUVMUVOUVQVPZAUUHU
      VRASNIYTUTUVBAIUOWFUHWMWNWOWPZAUURUVKVIUUHAUVKUURUVKUURVIAUVKPSUGUVLWQWRW
      TWCZWSAUVEUUHAUVDUVEUVFXAZWCXBUUIUURUVKUUBUVTXCXJXDUURNSEMUUBUURWIZUHXEXF
      UUIUUNUUKUUIUUNEUULUUAVHZNVEZUUKUUIUWDEYTVAUUGMVAVGZNVEZXGZVHZUUAVHZNVEZU
      UNUUIUWJUWDUUIUWIUWCENUUIUWHUULUUAUUIVAYTUWFUULUUGUWGUURUUIUWGXHUUIUWEYTV
      IZVMUWEYTMNUUIUWKXIXKAUUHXIZUUIUURNSMYTUWBUHUVCUVJUVSXLXMZXNXKWTUUIUWJEUW
      HNVEZUUAVHZUUNUUIEVBVGZUWGVHZUUAVHZNVEZEUWQNVEZUUAVHZVIZUWJUWOVIVBUUGYTUW
      PYTVIZUWSUWJUXAUWOUXCUWRUWIENUWPYTUUAUWGXOXKUXCUWTUWNUUAUXCUWQUWHENUWPYTU
      WGXPXKXNXQAUXBVBUUGVKZUUHAUXDEUUBNVEZEYTNVEZUUAVHZVIZBUUGVKZAEOHVFZUXIURA
      UXJUXIABCNHIKLENOSRUBUWAUVGXRWNXTAUUGUUGUWGYAZUXDUXIXSAUUGUUGUWGYBUXKASVA
      UWGMIVAUUGUWFMUWESYCVHZVEZUWFUXMVIUWEUUGVLNUXLMUWEUHYDWRYEUVBUOUVIUPYFUUG
      UUGUWGYGWAUXBUXHVBBUUGUUGUWGUWQYTVIZUWSUXEUXAUXGUXNUWRUUBENUWQYTUUAXPXKUX
      NUWTUXFUUAUWQYTENYHXNXQYIWAXJWCUWLYKUUIUWNUUMUUAUUIUWHUULENUWMXKXNYJYLUUI
      UWCUUJENUUIUUJUWCUUIMVCVGZUUAVHZNVEZMUXONVEZUUAVHZVIZUUJUWCVIZVCUUGYTUXOY
      TVIZUXQUUJUXSUWCUYBUXPUUBMNUXOYTUUAXPXKUYBUXRUULUUAUXOYTMNYHXNXQZAUXTVCUU
      GVKZUUHAUYABUUGVKZUYDAMOHVFZUYEUSAUYFUYEABCNHIKLMNOSRUBUWAUVIXRWNXTUXTUYA
      VCBUUGUXTBYMUYAVCYMUYCYNYOWCUWLYKWTXKYJWTUUIUUMUUDUUAUUIUUOUUPUUQUVMVPZUU
      MUUDVIUVCUUIUUPUUQUVMUVHUVJUVSXDUUOUYGVMUUDUUMUURNSEMYTUWBUHXEWTXFXNYPYQA
      BCNHIKLYSNOSRUBUWAAEMUVGUVIYRXRXJ $.
  $}

  ${
    $d .^ e f $.  $d B e f $.  $d L e f y $.  $d O e f $.  $d R e f $.
    $d R l $.  $d V e f $.  $d V l $.  $d X e f y $.  $d l ph y $.
    aks6d1c1p7.1 $e |- .~ = { <. e , f >. | ( e e. NN /\ f e. B /\
    A. y e. ( V PrimRoots R )
     ( e .^ ( ( O ` f ) ` y ) ) = ( ( O ` f ) ` ( e .^ y ) ) ) } $.
    aks6d1c1p7.2 $e |- S = ( Poly1 ` K ) $.
    aks6d1c1p7.3 $e |- B = ( Base ` S ) $.
    aks6d1c1p7.4 $e |- X = ( var1 ` K ) $.
    aks6d1c1p7.5 $e |- V = ( mulGrp ` K ) $.
    aks6d1c1p7.6 $e |- .^ = ( .g ` V ) $.
    aks6d1c1p7.7 $e |- P = ( chr ` K ) $.
    aks6d1c1p7.8 $e |- O = ( eval1 ` K ) $.
    aks6d1c1p7.9 $e |- ( ph -> K e. Field ) $.
    aks6d1c1p7.10 $e |- ( ph -> P e. Prime ) $.
    aks6d1c1p7.11 $e |- ( ph -> R e. NN ) $.
    aks6d1c1p7.12 $e |- ( ph -> N e. NN ) $.
    aks6d1c1p7.13 $e |- ( ph -> P || N ) $.
    aks6d1c1p7.14 $e |- ( ph -> ( N gcd R ) = 1 ) $.
    aks6d1c1p7.15 $e |- ( ph -> L e. NN ) $.
    $( ` X ` is introspective to all positive integers.  (Contributed by
       metakunt, 30-Apr-2025.) $)
    aks6d1c1p7 $p |- ( ph -> L .~ X ) $=
      ( vl wbr cv cfv co wceq cprimroots wral wcel wa eqid ccrg fldcrngd adantr
      cbs c0g cdvds wi cn0 w3a ccmn crngmgp syl nnnn0d isprimroot biimpd simp1d
      imp mgpbas eleqtrrdi evl1vard simprd oveq2d cmnd cmnmndd eleqtrdi syl3anc
      mulgnn0cl eqidd eqtr2d eqtrd ralrimiva crngring vr1cl aks6d1c1p1 mpbird
      crg ) ALPEUMLBUNZPNUOZUOZJUPZLWSJUPZWTUOZUQZBOFURUPZUSAXEBXFAWSXFUTZVAZXB
      XCXDXHXAWSLJXHPCUTZXAWSUQXHKVFUOZGKCNPWSUDTXJVBZRSAKVCUTZXGAKUEVDZVEZXHWS
      OVFUOZXJXHWSXOUTZFWSJUPOVGUOZUQZULUNZWSJUPXQUQFXSVHUMVIULVJUSZAXGXPXRXTVK
      ZAXGYAAOJFWSULAXLOVLUTXMKOUAVMVNZAFUGVOUBVPVQVSVRXJKOUAXKVTZWAZWBWCWDXHXD
      XCXCXHXIXDXCUQXHXJGKCNPXCUDTXKRSXNXHXCXOXJXHOWEUTZLVJUTZXPXCXOUTAYEXGAOYB
      WFVEAYFXGALUKVOVEXHWSXJXOYDYCWGXOJOLWSXOVBUBWIWHYCWAWBWCXHXCWJWKWLWMABCJE
      FHILJPONQAPGVFUOZCAKWRUTZPYGUTAXLYHXMKWNVNYGGKPTRYGVBWOVNSWAUKWPWQ $.
  $}

  ${
    aks6d1c1.1 $e |- .~ = { <. e , f >. | ( e e. NN /\ f e. B /\
    A. y e. ( V PrimRoots R )
     ( e .^ ( ( O ` f ) ` y ) ) = ( ( O ` f ) ` ( e .^ y ) ) ) } $.
    aks6d1c1.2 $e |- S = ( Poly1 ` K ) $.
    aks6d1c1.3 $e |- B = ( Base ` S ) $.
    aks6d1c1.4 $e |- X = ( var1 ` K ) $.
    aks6d1c1.5 $e |- W = ( mulGrp ` S ) $.
    aks6d1c1.6 $e |- V = ( mulGrp ` K ) $.
    aks6d1c1.7 $e |- .^ = ( .g ` V ) $.
    aks6d1c1.8 $e |- C = ( algSc ` S ) $.
    aks6d1c1.9 $e |- D = ( .g ` W ) $.
    aks6d1c1.10 $e |- P = ( chr ` K ) $.
    aks6d1c1.11 $e |- O = ( eval1 ` K ) $.
    aks6d1c1.12 $e |- .+ = ( +g ` S ) $.
    aks6d1c1.13 $e |- ( ph -> K e. Field ) $.
    aks6d1c1.14 $e |- ( ph -> P e. Prime ) $.
    aks6d1c1.15 $e |- ( ph -> R e. NN ) $.
    aks6d1c1.16 $e |- ( ph -> N e. NN ) $.
    aks6d1c1.17 $e |- ( ph -> P || N ) $.
    aks6d1c1.18 $e |- ( ph -> ( N gcd R ) = 1 ) $.
    ${
      $d .^ e f y $.  $d .~ h i $.  $d .~ i y $.  $d B e f $.  $d D e f i y $.
      $d D h i $.  $d E e f i y $.  $d E h i $.  $d F e f i y $.  $d F h i $.
      $d L h $.  $d O e f y $.  $d R e f y $.  $d R y z $.  $d V e f y $.
      $d V y z $.  $d W e f y $.  $d h i ph $.  $d ph y z $.
      aks6d1c1p6.1 $e |- ( ph -> E .~ F ) $.
      aks6d1c1p6.2 $e |- ( ph -> L e. NN0 ) $.
      $( If a polynomials ` F ` is introspective to ` E ` , then so are its
         powers.  (Contributed by metakunt, 30-Apr-2025.) $)
      aks6d1c1p6 $p |- ( ph -> E .~ ( L D F ) ) $=
        ( vh vi vz cn0 wcel co wbr cv cc0 c1 caddc wceq oveq1 breq2d cprimroots
        cfv wral wa cur c0g cbs aks6d1c1p1rcl simprd eleqtrdi eqid mgpbas mulg0
        cn syl ringidval eqcomi eqtrdi adantr fveq2d fveq1d oveq2d crg fldcrngd
        ccrg crngring ply1scl1 eqcomd ringidcl cmg cdvds wi ccmn crngmgp nnnn0d
        w3a isprimroot biimpd imp simp1d evl1scad cmnd cmnmndd mulgnn0z syl2anc
        simpld mulgnn0cl syl3anc 3eqtrd ralrimiva ply1ring a1i mpbid aks6d1c1p1
        eleq12d mpbird cplusg cfield ad2antrr cprime simpr aks6d1c1p4 ringmgp
        cgcd simplr eqtrd eleq2d mulgnn0p1 breqtrrd nn0indd mpdan ) AQVFVGMQOEV
        HZHVIZVBAMVCVJZOEVHZHVIMVKOEVHZHVIZMVDVJZOEVHZHVIZMUUNVLVMVHZOEVHZHVIUU
        IVCVDQUUJVKVNUUKUULMHUUJVKOEVOVPUUJUUNVNUUKUUOMHUUJUUNOEVOVPUUJUUQVNUUK
        UURMHUUJUUQOEVOVPUUJQVNUUKUUHMHUUJQOEVOVPAUUMMBVJZUULSVRZVRZNVHZMUUSNVH
        ZUUTVRZVNZBTIVQVHZVSAUVEBUVFAUUSUVFVGZVTZUVBMUUSJWAVRZSVRZVRZNVHZUVCUVJ
        VRZUVDUVHUVAUVKMNUVHUUSUUTUVJUVHUULUVISAUULUVIVNUVGAUULUAWBVRZUVIAOUAWC
        VRZVGZUULUVNVNAOJWCVRZUVOAOCUVQAMWJVGZOCVGZABCNHIKLMNOTSUCVAWDZWEZUEWFU
        VQJUAUGUVQWGZWHZWFUVOEUAOUVNUVOWGZUVNWGUKWIWKUVIUVNJUVIUAUGUVIWGZWLWMWN
        ZWOZWPWQWRUVHUVLMUUSPWAVRZDVRZSVRZVRZNVHZUVCUWJVRZUVMUVHUVKUWKMNUVHUUSU
        VJUWJUVHUVIUWISUVHUWIUVIAUWIUVIVNZUVGAPWSVGZUWNAPXAVGZUWOAPUOWTZPXBWKZD
        JPUWHUVIUDUJUWHWGZUWEXCWKWOZXDWPWQWRUVHUWLMUWHNVHZUWHUWMUVHUWKUWHMNUVHU
        WICVGZUWKUWHVNUVHDPWCVRZJPCSUWHUUSUMUDUXCWGZUJUEAUWPUVGUWQWOZAUWHUXCVGZ
        UVGAUWOUXFUWRUXCPUWHUXDUWSXEWKWOZUVHUUSTWCVRZUXCUVHUUSUXHVGZIUUSTXFVRZV
        HTWBVRZVNZVEVJZUUSUXJVHUXKVNIUXMXGVIXHVEVFVSZAUVGUXIUXLUXNXLZAUVGUXOATU
        XJIUUSVEAUWPTXIVGUWQPTUHXJWKZAIUQXKUXJWGXMXNXOXPUXCUXHUXCPTUHUXDWHZWMWF
        ZXQWEWRAUXAUWHVNZUVGATXRVGZMVFVGZUXSATUXPXSZAMAUVRUVSUVTYBZXKZUXHNTMUWH
        UXHWGUIPUWHTUHUWSWLXTYAWOUVHUWMUWHUVHUXBUWMUWHVNUVHDUXCJPCSUWHUVCUMUDUX
        DUJUEUXEUXGUVHUXTUYAUUSUXCVGUVCUXCVGAUXTUVGUYBWOAUYAUVGUYDWOUXRUXCNTMUU
        SUXQUIYCYDXQWEXDYEUVHUVCUWJUVJUVHUWIUVISUWTWPWQYEUVHUVCUVJUUTUVHUVIUULS
        UVHUULUVIUWGXDWPWQYEYFABCNHIKLMNUULTSUCAUVIUVQVGZUULCVGAJWSVGZUYEAUWOUY
        FUWRJPUDYGWKZUVQJUVIUWBUWEXEWKAUVIUULUVQCAUULUVIUWFXDACUVQCUVQVNAUEYHZX
        DYKYIUYCYJYLAUUNVFVGZVTZUUPVTZMUUOOUAYMVRZVHZUURHUYKBCDEFGHIJKLMNUUOOPR
        STUAUBUCUDUEUFUGUHUIUJUKULUMUNAPYNVGUYIUUPUOYOAFYPVGUYIUUPUPYOAIWJVGUYI
        UUPUQYOARIYTVHVLVNUYIUUPUTYOAFRXGVIUYIUUPUSYOUYJUUPYQAMOHVIUYIUUPVAYOYR
        UYKUAXRVGZUYIUVPUURUYMVNUYJUYNUUPAUYNUYIAUYFUYNUYGJUAUGYSWKWOWOAUYIUUPU
        UAUYJUVPUUPAUVPUYIAUVSUVPUWAACUVOOACUVQUVOUYHUVQUVOVNAUWCYHUUBUUCYIWOWO
        UVOUYLEUAUUNOUWDUKUYLWGUUDYDUUEUUFUUG $.
    $}

    ${
      $d .^ e f y $.  $d .~ h i $.  $d .~ i y $.  $d B e f $.  $d E e f i y $.
      $d E h i $.  $d F e f i y $.  $d F h i $.  $d L h $.  $d O e f y $.
      $d R e f y $.  $d R l y $.  $d V e f y $.  $d V l y $.  $d h i ph $.
      $d l ph y $.
      aks6d1c1p8.1 $e |- ( ph -> E .~ F ) $.
      aks6d1c1p8.2 $e |- ( ph -> L e. NN0 ) $.
      aks6d1c1p8.3 $e |- ( ph -> ( E gcd R ) = 1 ) $.
      $( If a number ` E ` is introspective to ` F ` , then so are its powers.
         (Contributed by metakunt, 30-Apr-2025.) $)
      aks6d1c1p8 $p |- ( ph -> ( E ^ L ) .~ F ) $=
        ( vh vi vl cn0 wcel cexp co wbr cv cc0 caddc oveq2 breq1d aks6d1c1p1rcl
        c1 wceq cn simpld nncnd exp0d cfv cprimroots wral wa eqid ccrg fldcrngd
        cbs adantr c0g cdvds wi w3a crngmgp syl nnnn0d isprimroot biimpd simp1d
        imp mgpbas eleqtrrdi simprd fveval1fvcl eleqtrdi mulg1 eqcomd ralrimiva
        ccmn fveq2d eqtrd 1nn aks6d1c1p1 mpbird eqbrtrd cmul cc ad2antrr simplr
        a1i 1nn0 expaddd exp1d oveq2d cfield cprime cgcd simpr aks6d1c1p5 mpdan
        nn0indd ) AQVGVHMQVIVJZOHVKZVBAMVDVLZVIVJZOHVKMVMVIVJZOHVKMVEVLZVIVJZOH
        VKZMYTVRVNVJZVIVJZOHVKYPVDVEQYQVMVSYRYSOHYQVMMVIVOVPYQYTVSYRUUAOHYQYTMV
        IVOVPYQUUCVSYRUUDOHYQUUCMVIVOVPYQQVSYRYOOHYQQMVIVOVPAYSVROHAMAMAMVTVHZO
        CVHZABCNHIKLMNOTSUCVAVQZWAWBZWCAVROHVKVRBVLZOSWDZWDZNVJZVRUUINVJZUUJWDZ
        VSZBTIWEVJZWFAUUOBUUPAUUIUUPVHZWGZUULUUKUUNUURUUKTWKWDZVHUULUUKVSUURUUK
        PWKWDZUUSUURUUTJPCOSUUIUMUDUUTWHZUEAPWIVHZUUQAPUOWJZWLUURUUIUUSUUTUURUU
        IUUSVHZIUUINVJTWMWDZVSZVFVLZUUINVJUVEVSIUVGWNVKWOVFVGWFZAUUQUVDUVFUVHWP
        ZAUUQUVIATNIUUIVFAUVBTXLVHUVCPTUHWQWRAIUQWSUIWTXAXCXBZUUTPTUHUVAXDZXEAU
        UFUUQAUUEUUFUUGXFZWLXGUVKXHUUSNTUUKUUSWHZUIXIWRUURUUIUUMUUJUURUUMUUIUUR
        UVDUUMUUIVSUVJUUSNTUUIUVMUIXIWRXJXMXNXKABCNHIKLVRNOTSUCUVLVRVTVHAXOYCXP
        XQXRAYTVGVHZWGZUUBWGZUUDUUAMXSVJZOHUVPUUDUUAMVRVIVJZXSVJUVQUVPMYTVRAMXT
        VHUVNUUBUUHYAZVRVGVHUVPYDYCAUVNUUBYBYEUVPUVRMUUAXSUVPMUVSYFYGXNUVPBCDUU
        AFGHIJKLMNOPRSTUAUBUCUDUEUFUGUHUIUJULUMUNAPYHVHUVNUUBUOYAAFYIVHUVNUUBUP
        YAAIVTVHUVNUUBUQYAAMIYJVJVRVSUVNUUBVCYAAFRWNVKUVNUUBUSYAUVOUUBYKAMOHVKU
        VNUUBVAYAYLXRYNYM $.
    $}

    ${
      $d .+ a j $.  $d .+ e f j k y $.  $d .+ g i $.  $d .+ h i j $.
      $d .^ e f y $.  $d .^ x y $.  $d .~ a j $.  $d .~ h j $.  $d .~ j k y $.
      $d A a j $.  $d A g i $.  $d A h i j $.  $d A i j k y $.  $d A j x y $.
      $d B e f $.  $d C a j $.  $d C e f j k y $.  $d C g i $.  $d C h i j $.
      $d D e f j k y $.  $d D g i $.  $d D h i j $.  $d E e f j k y $.
      $d E h j $.  $d F e f j k y $.  $d F g i $.  $d F h i j $.  $d K a j $.
      $d K e f j k y $.  $d K g i $.  $d K h i j $.  $d K j x y $.
      $d L e f y $.  $d N a $.  $d N e f y $.  $d N x y $.  $d O e f y $.
      $d P e f y $.  $d P x y $.  $d R e f y $.  $d R x y $.  $d U e f y $.
      $d V e f y $.  $d V x y $.  $d W e f j k y $.  $d W g i $.  $d W h i j $.
      $d X a j $.  $d X e f j k y $.  $d X g i $.  $d X h i j $.  $d a j ph $.
      $d g i ph $.  $d h i j ph $.  $d k ph y $.  $d ph x y $.
      aks6d1c1.19 $e |- ( ph -> F : ( 0 ... A ) --> NN0 ) $.
      aks6d1c1.20 $e |- G = ( g e. ( NN0 ^m ( 0 ... A ) ) |->
      ( W gsum ( i e. ( 0 ... A ) |->
        ( ( g ` i ) D ( X .+ ( C ` ( ( ZRHom ` K ) ` i ) ) ) ) ) ) ) $.
      aks6d1c1.21 $e |- ( ph -> A e. NN0 ) $.
      aks6d1c1.22 $e |- ( ph -> U e. NN0 ) $.
      aks6d1c1.23 $e |- ( ph -> L e. NN0 ) $.
      aks6d1c1.24 $e |- E = ( ( P ^ U ) x. ( ( N / P ) ^ L ) ) $.
      aks6d1c1.25 $e |- ( ph -> A. a e. ( 1 ... A ) N .~
      ( X .+ ( C ` ( ( ZRHom ` K ) ` a ) ) ) ) $.
      aks6d1c1.26 $e |- ( ph -> ( x e. ( Base ` K ) |-> ( P .^ x ) )
      e. ( K RingIso K ) ) $.
      $( Claim 1 of Theorem 6.1 ~ https://www3.nd.edu/%7eandyp/notes/AKS.pdf .
         (Contributed by metakunt, 30-Apr-2025.) $)
      aks6d1c1 $p |- ( ph -> E .~ ( G ` F ) ) $=
        ( vk cc0 cfz co cv cfv cmpt cgsu cz wcel cle wbr w3a 3jca c1 caddc wceq
        oveq2 mpteq1d oveq2d breq2d cdiv cmul cn syl wa wb nnzd syl3anc jca cbs
        mpbid eqid syl2anc breqtrrd eqtrd cn0 0zd elfzd ffvelcdmd a1i ply1sclcl
        fveq2d mndcl eleqtrdi mulgnn0cld 2fveq3 oveq12d 3ad2ant1 cgcd adantr wi
        fveq2 gcdcom eqeq1 pm5.74i mpbi oveq1d eqeltrd mpbird ex zred cvv ovexd
        3adant3 vh vj czrh nn0zd nn0ge0d nn0red leidd csn c0g cexp cprime prmnn
        nnexpcld clt cdvds nnne0d dvdsval2 nnred nngt0d divgt0d sylibr nnmulcld
        wne elnnz eqeltrid aks6d1c1p7 cmnd ccmn ccrg fldcrngd ply1crng crngring
        crg ringcmn cmnmnd vr1cl zrh0 ply1ascl0 0red aks6d1c1p6 crngmgp cmnmndd
        mndrid 0z 0le0 czring crh zrhrhm zringbas rhmf mgpbas gsumsn fzsn ax-mp
        wf cplusg cfield simp3 nfcv cbvmpt breqtrd recnd gtned divdiv2d mulcomd
        oveq2i eqcomd dividd div1d rpdvds simpr1 peano2zd aks6d1c1p2 aks6d1c1p8
        rpexp1i imp wral wo simpr 1cnd addlidd eleq2d imbi1d jaod eluz1 elfzp12
        cuz ralimdv2 mpd 1red simpr2 addge0d simpr3 zltp1led rspcdva aks6d1c1p3
        0le1 aks6d1c1p5 eqbrtrd aks6d1c1p4 simp21 simp22 elnn0z elfzelz elfzle1
        adantl readdcld elfzle2 simpl23 letrd 3syl gsummptfzsplit fzindd simplr
        crs cmap fveq1d mpteq2dva nn0ex elmapd fvmptd ) ARUGQVQDVRVSZQVTZTWAZUH
        VVCUBUUCWAZWAFWAZIVSZGVSZWBZWCVSZTUAWAJADWDWEZVQDWFWGZDDWFWGZWHZRVVJJWG
        ZAVVKVVLVVMADVJUUDZADVJUUEZADADVJUUFUUGWIAVVNVVOARUGQVQUUAVTZVRVSZVVHWB
        ZWCVSZJWGRUGQVQVQVRVSZVVHWBZWCVSZJWGRUGQVQUUBVTZVRVSZVVHWBZWCVSZJWGZRUG
        QVQVWEWJWKVSZVRVSZVVHWBZWCVSZJWGVVOUUAUUBDVQDVVRVQWLZVWAVWDRJVWNVVTVWCU
        GWCVWNQVVSVWBVVHVVRVQVQVRWMWNWOWPVVRVWEWLZVWAVWHRJVWOVVTVWGUGWCVWOQVVSV
        WFVVHVVRVWEVQVRWMWNWOWPVVRVWJWLZVWAVWMRJVWPVVTVWLUGWCVWPQVVSVWKVVHVVRVW
        JVQVRWMWNWOWPVVRDWLZVWAVVJRJVWQVVTVVIUGWCVWQQVVSVVBVVHVVRDVQVRWMWNWOWPA
        RUGQVQUUHZVVHWBZWCVSZVWDJARVQTWAZUHVQVVEWAZFWAZIVSZGVSZVWTJACEFGHIJKLNO
        RSVXDUBVXAUDUEUFUGUHUJUKULUMUNUOUPUQURUSUTVAVBVCVDVEVFVGARUHLUUIWAZIVSZ
        VXDJARUHVXGJACEHJKLNOSUBRUDUEUFUHUJUKULUMUOUPUSUTVBVCVDVEVFVGARHMUUJVSZ
        UDHWQVSZUCUUJVSZWRVSZWSVMAVXHVXJAHMAHUUKWEZHWSWEVCHUULWTZVKUUMAVXIUCAVX
        IWDWEZVQVXIUUNWGZXAVXIWSWEAVXNVXOAHUDUUOWGZVXNVFAHWDWEZHVQUVCUDWDWEZVXP
        VXNXBAHVXMXCZAHVXMUUPZAUDVEXCZHUDUUQXDXGZAUDHAUDVEUURZAHVXMUURZAUDVEUUS
        ZAHVXMUUSUUTZXEVXIUVDUVAVLUUMUVBUVEUVFALUVGWEZUHLXFWAZWEZVXGUHWLALUVHWE
        ZVYGALUVIWEZVYJAUBUVIWEZVYKAUBVBUVJZLUBUKUVKWTZVYKLUVMWEVYJLUVLLUVNWTWT
        LUVOWTZAUBUVMWEZVYIAVYLVYPVYMUBUVLWTZVYHLUBUHUMUKVYHXHZUVPWTZVYHILUHVXF
        VYRVAVXFXHZUWCXIZXJAVXCVXFUHIAVXCUBUUIWAZFWAVXFAVXBWUBFAVYPVXBWUBWLVYQU
        BVVEWUBVVEXHZWUBXHZUVQWTXRAFUBWUBLVXFUKUQWUDVYTVYQUVRXKWOZXJAVVBXLVQTVH
        AVQVQDAXMZVVPWUFAVQAUVSZUUGVVQXNXOUVTAUGUVGWEZVQWDWEZVXEUGXFWAZWEVWTVXE
        WLAUGAVYKUGUVHWEZVYNLUGUNUWAWTZUWBZWUIAUWDXPZAWUJGUGVXAVXDWUJXHZURWUMAV
        VBXLVQTVHAVQVQDWUNVVPWUNVQVQWFWGAUWEXPVVQXNXOAVXDVYHWUJAVYGVYIVXCVYHWEZ
        VXDVYHWEVYOVYSAVYPVXBUBXFWAZWEWUPVYQAWDWUQVQVVEAVVEUWFUBUWGVSWEZWDWUQVV
        EUWOZAVYPWURVYQUBVVEWUCUWHZWTWDWUQUWFUBVVEUWIWUQXHZUWJZWTZWUFXOFVYHLUBV
        XBWUQUKUQWVAVYRXQXIVYHILUHVXCVYRVAXSXDVYHLUGUNVYRUWKZXTYAVVHWUJVXEQUGVQ
        WDWUOVVCVQWLZVVDVXAVVGVXDGVVCVQTYHWVEVVFVXCUHIVVCVQFVVEYBWOYCUWLXDXJAVW
        CVWSUGWCAQVWBVWRVVHVWBVWRWLZAWUIWVFUWDVQUWMUWNXPWNWOXJAVWEWDWEZVQVWEWFW
        GZVWEDUUNWGZWHZVWIWHZRUGVPVWFVPVTZTWAZUHWVLVVEWAZFWAZIVSZGVSZWBZWCVSZUG
        VPVWJUUHWVQWBWCVSZUGUWPWAZVSZVWMJWVKCEFGHIJKLNORSWVSWVTUBUDUEUFUGUHUJUK
        ULUMUNUOUPUQURUSUTVAAWVJUBUWQWEZVWIVBYDAWVJVXLVWIVCYDAWVJKWSWEZVWIVDYDA
        WVJUDKYEVSZWJWLZVWIVGYDAWVJVXPVWIVFYDWVKRVWHWVSJAWVJVWIUWRVWHWVSWLWVKVW
        GWVRUGWCQVPVWFVVHWVQVPVVHUWSZQWVQUWSZVVCWVLWLZVVDWVMVVGWVPGVVCWVLTYHWWI
        VVFWVOUHIVVCWVLFVVEYBWOYCZUWTUXFXPUXAAWVJRWVTJWGVWIAWVJXAZRVWJTWAZUHVWJ
        VVEWAZFWAZIVSZGVSZWVTJWWKCEFGHIJKLNORSWWOUBWWLUDUEUFUGUHUJUKULUMUNUOUPU
        QURUSUTVAAWWCWVJVBYFZAVXLWVJVCYFZAWWDWVJVDYFZAUDWSWEWVJVEYFZAVXPWVJVFYF
        ZAWWFWVJVGYFZWWKRVXKWWOJRVXKWLWWKVMXPWWKCEFVXHHIJKLNOVXJSWWOUBUDUEUFUGU
        HUJUKULUMUNUOUPUQUSUTVAWWQWWRWWSAVXJKYEVSWJWLZWVJAVXNKWDWEZUCXLWEZWHZVX
        IKYEVSZWJWLZWXCAVXNWXDWXEVYBAKVDXCZVLWIAKVXIYEVSZWJWLZYGAWXHYGAWXDVXNVX
        RWHKUDYEVSZWJWLZVXIUDUUOWGZXAWXKAWXDVXNVXRWXIVYBVYAWIAWXMWXNAWWFYGAWXMY
        GVGAWWFWXMAWWEWXLWLZWWFWXMXBAVXRWXDXAWXOAVXRWXDVYAWXIXEUDKYIWTWWEWXLWJY
        JWTYKYLZAWXNUDVXIWQVSZWDWEZAWXQUDHWRVSZUDWQVSZWDAUDUDHAUDVYCUXBZWYAAHVY
        DUXBZAVQUDWUGVYEUXCZVXTUXDAWXTHUDUDWQVSZWQVSZWDAWXTHUDWRVSZUDWQVSZWYEAW
        XSWYFUDWQAUDHWYAWYBUXEYMAWYEWYGAHUDUDWYBWYAWYAWYCWYCUXDUXGXKAWYEHWDAWYE
        HWJWQVSHAWYDWJHWQAUDWYAWYCUXHWOAHWYBUXIXKVXSYNYNYNAVXNVXIVQUVCVXRWXNWXR
        XBVYBAVQVXIWUGVYFUXCVYAVXIUDUUQXDYOXEKVXIUDUXJXIAWXKWXHAWXJWXGWLZWXKWXH
        XBAWXDVXNXAWYHAWXDVXNWXIVYBXEKVXIYIWTWXJWXGWJYJWTYKYLZWXFWXHWXCVXIKUCUX
        OUXPXIYFWXAWWKCEFGHIJKLNOHSWWOUBMUDUEUFUGUHUJUKULUMUNUOUPUQURUSUTVAWWQW
        WRWWSWWTWXAWXBWWKCVWJEFGHIJKLNOSWWOUBUDUEUFUGUHUJUKULUMUNUOUPUQURUSUTVA
        WWQWWRWWSWXBWXAWWOXHZWWKVWEAWVGWVHWVIUXKZUXLZUXMAMXLWEWVJVKYFAHKYEVSZWJ
        WLZWVJAKHYEVSZWJWLZYGAWYNYGAWXDVXQVXRWHWXMVXPXAWYPAWXDVXQVXRWXIVXSVYAWI
        AWXMVXPWXPVFXEKHUDUXJXIAWYPWYNAWYOWYMWLZWYPWYNXBAWXDVXQXAWYQAWXDVXQWXIV
        XSXEKHYIWTWYOWYMWJYJWTYKYLYFUXNWWKCEFGHIJKLNOVXISWWOUBUCUDUEUFUGUHUJUKU
        LUMUNUOUPUQURUSUTVAWWQWWRWWSWWTWXAWXBWWKBCVWJEFGHIJKLNOSWWOUBUDUEUFUGUH
        UJUKULUMUNUOUPUQURUSUTVAWWQWWRWWSWXBWXAWYJWYLWWKUDUHUIVTZVVEWAZFWAZIVSZ
        JWGZUDWWOJWGUIVVBVWJWYRVWJWLZXUAWWOUDJXUCWYTWWNUHIWYRVWJFVVEYBWOWPAXUBU
        IVVBUXQZWVJAXUBUIWJDVRVSZUXQXUDVNAXUBXUBUIXUEVVBAWYRXUEWEZXUBYGZWYRVVBW
        EZXUBYGZAXUGXAZXUIWYRVQWLZWYRVQWJWKVSZDVRVSZWEZUXRZXUBYGXUJXUKXUBXUNAXU
        KXUBYGXUGAXUKXUBAXUKXAZUDVXDXUAJAUDVXDJWGXUKAUDVXGVXDJAUDUHVXGJACEHJKLN
        OSUBUDUDUEUFUHUJUKULUMUOUPUSUTVBVCVDVEVFVGVEUVFWUAXJWUEXJYFXUPWYTVXCUHI
        XUPWYSVXBFXUPWYRVQVVEAXUKUXSXRXRWOXJYPYFXUJXUNXUBYGXUGAXUGUXSXUJXUNXUFX
        UBXUJXUMXUEWYRXUJXULWJDVRXUJWJXUJUXTUYAYMUYBUYCYOUYDXUJXUHXUOXUBXUJDVQU
        YGWAWEZXUHXUOXBAXUQXUGAXUQVVKVVLXAZAVVKVVLVVPVVQXEAWUIXUQXURXBWUFVQDUYE
        WTYOYFWYRVQDUYFWTUYCYOYPUYHUYIYFWWKVWJVQDWWKXMAVVKWVJVVPYFZWYLWWKVWEWJW
        WKVWEWYKYQWWKUYJAWVGWVHWVIUYKVQWJWFWGWWKUYQXPUYLWWKWVIVWJDWFWGZAWVGWVHW
        VIUYMWWKVWEDWYKXUSUYNXGXNZUYOABWUQHBVTSVSWBUBUBVUOVSWEWVJVOYFUYPAWXEWVJ
        VLYFAWXHWVJWYIYFUXNUYRUYSWWKVVBXLVWJTAVVBXLTUWOZWVJVHYFXVAXOZUVTWWKWUHV
        WJYRWEWWPWUJWEWVTWWPWLAWUHWVJWUMYFZWWKVWEWJWKYSWWKWUJGUGWWLWWOWUOURXVDX
        VCWWKWWOVYHWUJWWKVYGVYIWWNVYHWEZWWOVYHWEAVYGWVJVYOYFZAVYIWVJVYSYFZWWKVY
        PWWMWUQWEXVEAVYPWVJVYQYFZWWKWDWUQVWJVVEAWUSWVJWVCYFWYLXOFVYHLUBWWMWUQUK
        UQWVAVYRXQXIVYHILUHWWNVYRVAXSXDWVDXTYAWVQWUJWWPVPUGVWJYRWUOWVLVWJWLZWVM
        WWLWVPWWOGWVLVWJTYHXVIWVOWWNUHIWVLVWJFVVEYBWOYCUWLXDXJYTUYTWVKVWMUGVPVW
        KWVQWBZWCVSWWBWVKVWLXVJUGWCVWLXVJWLWVKQVPVWKVVHWVQWWGWWHWWJUWTXPWOWVKWU
        JWWAVPUGVWEWVQWUOWWAXHAWVJWUKVWIWULYDWVKWVGWVHXAVWEXLWEWVKWVGWVHAWVGWVH
        WVIVWIVUAZAWVGWVHWVIVWIVUBXEVWEVUCUVAWVKWVLVWKWEZXAZWUJGUGWVMWVPWUOURWV
        KWUHXVLAWVJWUHVWIXVDYTYFXVMVVBXLWVLTWVKXVBXVLAWVJXVBVWIVHYDYFXVMWVLVQDX
        VMXMWVKVVKXVLAWVJVVKVWIVVPYDYFZXVLWVLWDWEWVKWVLVQVWJVUDVUFZXVLVQWVLWFWG
        WVKWVLVQVWJVUEVUFXVMWVLVWJDXVMWVLXVOYQXVMVWEWJXVMVWEWVKWVGXVLXVKYFZYQXV
        MUYJVUGXVMDXVNYQXVLWVLVWJWFWGWVKWVLVQVWJVUHVUFXVMWVIXUTWVGWVHWVIAVWIXVL
        VUIXVMVWEDXVPXVNUYNXGVUJXNXOXVMWVPVYHWUJXVMVYGVYIWVOVYHWEZWVPVYHWEWVKVY
        GXVLAWVJVYGVWIXVFYTYFWVKVYIXVLAWVJVYIVWIXVGYTYFXVMVYPWVNWUQWEXVQWVKVYPX
        VLAWVJVYPVWIXVHYTYFZXVMWDWUQWVLVVEXVMVYPWURWUSXVRWUTWVBVUKXVOXOFVYHLUBW
        VNWUQUKUQWVAVYRXQXIVYHILUHWVOVYRVAXSXDWVDXTYAVULXKXJWUFVVPVVQVUMYPUYIAP
        TUGQVVBVVCPVTZWAZVVGGVSZWBZWCVSZVVJXLVVBVUPVSZUAYRUAPXWDXWCWBWLAVIXPAXV
        STWLZXAZXWBVVIUGWCXWFQVVBXWAVVHXWFVVCVVBWEZXAZXVTVVDVVGGXWHVVCXVSTAXWEX
        WGVUNVUQYMVURWOATXWDWEXVBVHAXLVVBTYRYRXLYRWEAVUSXPAVQDVRYSVUTYOAUGVVIWC
        YSVVAXJ $.
    $}
  $}

  ${
    $d M a b c $.  $d M b c y $.  $d N a b c x $.  $d N b c x y $.
    $d O a b c x $.  $d O b c x y $.  $d Q a b c $.  $d Q b c y $.
    $d S a b c $.  $d S b c y $.  $d U x y $.  $d Y a b c x $.  $d Y b c x y $.
    $d a b c ph $.  $d ph y $.
    evl1gprodd.1 $e |- O = ( eval1 ` R ) $.
    evl1gprodd.2 $e |- P = ( Poly1 ` R ) $.
    evl1gprodd.3 $e |- Q = ( mulGrp ` P ) $.
    evl1gprodd.4 $e |- B = ( Base ` R ) $.
    evl1gprodd.5 $e |- U = ( Base ` P ) $.
    evl1gprodd.6 $e |- S = ( mulGrp ` R ) $.
    evl1gprodd.7 $e |- ( ph -> R e. CRing ) $.
    evl1gprodd.8 $e |- ( ph -> Y e. B ) $.
    evl1gprodd.9 $e |- ( ph -> A. x e. N M e. U ) $.
    evl1gprodd.10 $e |- ( ph -> N e. Fin ) $.
    $( Polynomial evaluation builder for a finite group product of polynomials.
       (Contributed by metakunt, 29-Apr-2025.) $)
    evl1gprodd $p |- ( ph -> ( ( O ` ( Q gsum ( x e. N |-> M ) ) ) ` Y )
         = ( S gsum ( x e. N |-> ( ( O ` M ) ` Y ) ) ) ) $=
      ( va vb vc vy cv cmpt cgsu co cfv wceq c0 csn mpteq1 oveq2d fveq2d fveq1d
      cun eqeq12d mpt0 a1i c0g eqid gsum0 cur ringidval cascl wcel cbs cmnd crg
      eqcomi crngringd ringmgp syl mndidcl mgpbas eqtri eleqtrrdi eleq1d mpbird
      evl1scad simprd eqcomd ply1scl1 eqtrd 3eqtrd eqtr2d wss cdif wa csb cmulr
      nfcv nfcsb1v csbeq1a cbvmpt mgpplusg ply1crng crngmgp adantr cfn ad2antrr
      ccmn ccrg simplrl ssfid wral ad3antrrr sselda rspcsbela expcom imp eleq2d
      syl2anc simplrr eldifbd eldifad csbeq1 gsumunsn ralrimiva gsummptcl eqidd
      equcoms jca evl1muld cmgp eqeltrid csbfv12 cvv csbfv2g elv csbgfi fveq12i
      vex fveval1fvcl eleqtrdi nfcsb1 nffv csbhypf simpr oveq1d ex findcard2d )
      ALEBUCUGZIUHZUIUJZKUKZUKZGBUUFLIKUKZUKZUHZUIUJZULLEBUMIUHZUIUJZKUKZUKZGBU
      MUULUHZUIUJZULLEBUDUGZIUHZUIUJZKUKZUKZGBUVAUULUHZUIUJZULZLEBUVAUEUGZUNUSZ
      IUHZUIUJZKUKZUKZGBUVJUULUHZUIUJZULZLEBJIUHZUIUJZKUKZUKZGBJUULUHZUIUJZULUC
      UDUEJUUFUMULZUUJUURUUNUUTUWDLUUIUUQUWDUUHUUPKUWDUUGUUOEUIBUUFUMIUOUPUQURU
      WDUUMUUSGUIBUUFUMUULUOUPUTUUFUVAULZUUJUVEUUNUVGUWELUUIUVDUWEUUHUVCKUWEUUG
      UVBEUIBUUFUVAIUOUPUQURUWEUUMUVFGUIBUUFUVAUULUOUPUTUUFUVJULZUUJUVNUUNUVPUW
      FLUUIUVMUWFUUHUVLKUWFUUGUVKEUIBUUFUVJIUOUPUQURUWFUUMUVOGUIBUUFUVJUULUOUPU
      TUUFJULZUUJUWAUUNUWCUWGLUUIUVTUWGUUHUVSKUWGUUGUVREUIBUUFJIUOUPUQURUWGUUMU
      WBGUIBUUFJUULUOUPUTAUURLEUMUIUJZKUKZUKZUUTALUUQUWIAUUPUWHKAUUOUMEUIUUOUMU
      LABIVAVBUPUQURAUUTGUMUIUJZUWJAUUSUMGUIUUSUMULABUULVAVBUPAUWKGVCUKZLEVCUKZ
      KUKZUKZUWJUWKUWLULAGUWLUWLVDZVEVBAUWLFVFUKZUWOUWLUWQULAUWQUWLFUWQGRUWQVDZ
      VGZVMVBAUWQLUWQDVHUKZUKZKUKZUKZUWOAUXCUWQAUXAHVIUXCUWQULAUWTCDFHKUWQLMNPU
      WTVDZQSAUWQCVIUWLCVIAUWLGVJUKZCAGVKVIZUWLUXEVIAFVLVIZUXFAFSVNZFGRVOVPUXEG
      UWLUXEVDZUWPVQVPCFVJUKZUXEPUXJFGRUXJVDVRZVSZVTAUWQUWLCUWQUWLULAUWSVBWAWBT
      WCWDWEALUXBUWNAUXAUWMKAUXADVFUKZUWMAUXGUXAUXMULUXHUWTDFUWQUXMNUXDUWRUXMVD
      ZWFVPUXMUWMULADUXMEOUXNVGVBWGUQURWGWGALUWNUWIAUWMUWHKAUWHUWMUWHUWMULAEUWM
      UWMVDVEVBWEUQURWHWIWGAUVAJWJZUVIJUVAWKZVIZWLZWLZUVHUVQUXSUVHWLZUVNGUFUVJB
      UFUGZUULWMZUHZUIUJZUVPUXTUVNUVELBUVIIWMZKUKZUKZFWNUKZUJZUYDUXTUVNLEUFUVJB
      UYAIWMZUHZUIUJZKUKZUKZUYIUXTLUVMUYMUXTUVLUYLKUXTUVKUYKEUIUVKUYKULUXTBUFUV
      JIUYJUFIWOZBUYAIWPZBUYAIWQZWRVBUPUQURUXTUYNLEUFUVAUYJUHZUIUJZUYEDWNUKZUJZ
      KUKZUKZUYIUXTLUYMVUBUXTUYLVUAKUXTUVAEVJUKZUYTUFEUVIUXPUYJUYEVUDVDDUYTEOUY
      TVDZWSUXSEXEVIZUVHAVUFUXRADXFVIZVUFAFXFVIZVUGSDFNWTVPDEOXAVPXBXBZUXTJUVAA
      JXCVIUXRUVHUBXDAUXOUXQUVHXGZXHZUXTUYAUVAVIZWLZUYJVUDVIUYJHVIZVUMIHVIBJXIZ
      UYAJVIZVUNAVUOUXRUVHVULUAXJUXTUVAJUYAVUJXKVUOVUPVUNVUPVUOVUNBUYAJIHXLXMXN
      XPZVUMVUDHUYJUXTVUDHULZVULUXSVURUVHAVURUXRVURAHVUDHDEOQVRZVMVBXBXBZXBXOWB
      AUXOUXQUVHXQZUXTUVIJUVAVVAXRZUXTUYEVUDVIUYEHVIZUXTUVIJVIVUOVVCUXTUVIJUVAV
      VAXSAVUOUXRUVHUAXDBUVIJIHXLXPZUXTVUDHUYEVUTXOWBBUYAUVIIXTYAUQURUXTVUAHVIV
      UCUYIULUXTCDFUYTUYHHUYSUYEKUVEUYGLMNPQAVUHUXRUVHSXDZALCVIZUXRUVHTXDZUXTUY
      SHVILUYSKUKZUKUVEULUXTHUFEUVAUYJVUSVUIVUKUXTVUNUFUVAVUQYBYCUXTLVVHUVDUXTU
      YSUVCKUXTUYRUVBEUIUYRUVBULUXTUFBUVAUYJIUYPUYOUYABUGZULIUYJIUYJULBUFUYQYEW
      EWRVBUPUQURYFUXTVVCUYGUYGULVVDUXTUYGYDYFVUEUYHVDZYGWDWGWGUXTUYDUYIUXTUYDG
      UFUVAUYBUHZUIUJZUYGUYHUJUYIUXTUVAUXEUYHUFGUVIUXPUYBUYGUXIFUYHGRVVJWSUXSGX
      EVIZUVHAVVMUXRAGFYHUKZXERAVUHVVNXEVISFVVNVVNVDXAVPYIXBXBVUKVUMUYBLUYJKUKZ
      UKZUXEUYBBUYALWMZBUYAUUKWMZUKVVPBUYALUUKYJVVQLVVRVVOVVRVVOULUFBUYAIYKKYLY
      MBUYALUFYPBLWOZYNYOVSVUMUXEDFHUYJKLMNUXJUXEUXKVMQAVUHUXRUVHVULSXJVUMLUXEV
      IVVFAVVFUXRUVHVULTXJVUMUXECLUXECULVUMCUXEUXLVMVBXOWBVUQYQYIVVAVVBUXTUYGCU
      XEUXTCDFHUYEKLMNPQVVEVVGVVDYQUXLYRBUFUVIUULUYGBUVIWOZBLUYFBUYEKBKWOBUVIIV
      VTYSYTVVSYTVVIUVIULZLUUKUYFVWAIUYEKBUVIIWQUQURUUAYAUXTVVLUVEUYGUYHUXTUVEU
      VGVVLUXSUVHUUBUXTUVFVVKGUIUVFVVKULUXTBUFUVAUULUYBUFUULWOZBUYAUULWPZBUYAUU
      LWQZWRVBUPWIUUCWGWEWGUXTUYCUVOGUIUYCUVOULUXTUVOUYCBUFUVJUULUYBVWBVWCVWDWR
      VMVBUPWGUUDUBUUE $.
  $}

  ${
    $d N a k l $.  $d P a k l $.  $d a ph $.
    aks6d1c2p1.1 $e |- ( ph -> N e. NN ) $.
    aks6d1c2p1.2 $e |- ( ph -> P e. Prime ) $.
    aks6d1c2p1.3 $e |- ( ph -> P || N ) $.
    aks6d1c2p1.4 $e |- E = ( k e. NN0 , l e. NN0 |->
    ( ( P ^ k ) x. ( ( N / P ) ^ l ) ) ) $.
    $( In the AKS-theorem the subset defined by ` E ` takes values in the
       positive integers.  (Contributed by metakunt, 7-Jan-2025.) $)
    aks6d1c2p1 $p |- ( ph -> E : ( NN0 X. NN0 ) --> NN ) $=
      ( va cn0 cv cfv cexp co cmul cn wcel syl cxp c1st cdiv c2nd cprime adantr
      wa prmnn simpr xp1st nnexpcld cdvds wbr wb nndivdvds mpbid xp2nd nnmulcld
      jca cmpo cmpt cop wceq vex op1std oveq2d op2ndd mpompt eqcomi eqtri fmptd
      oveq12d ) AKLLUAZBKMZUBNZOPZEBUCPZVNUDNZOPZQPZRDAVNVMSZUGZVPVSWBBVOABRSZW
      AABUESWCHBUHTZUFWBWAVOLSAWAUIZVNLLUJTUKWBVQVRAVQRSZWAABEULUMZWFIAERSZWCUG
      WGWFUNAWHWCGWDUSEBUOTUPUFWBWAVRLSWEVNLLUQTUKURDCFLLBCMZOPZVQFMZOPZQPZUTZK
      VMVTVAZJWOWNCFKLLVTWMVNWIWKVBVCZVPWJVSWLQWPVOWIBOWIWKVNCVDZFVDZVEVFWPVRWK
      VQOWIWKVNWQWRVGVFVLVHVIVJVK $.
  $}

  ${
    $d E a b c d $.  $d N k l $.  $d N p $.  $d P k l $.  $d P p $.  $d Q p $.
    $d a b c d k l ph $.  $d a b c d p ph $.
    aks6d1c2p2.1 $e |- ( ph -> N e. NN ) $.
    aks6d1c2p2.2 $e |- ( ph -> P e. Prime ) $.
    aks6d1c2p2.3 $e |- ( ph -> P || N ) $.
    aks6d1c2p2.4 $e |- E = ( k e. NN0 , l e. NN0 |->
    ( ( P ^ k ) x. ( ( N / P ) ^ l ) ) ) $.
    aks6d1c2p2.5 $e |- ( ph -> Q e. Prime ) $.
    aks6d1c2p2.6 $e |- ( ph -> Q || N ) $.
    aks6d1c2p2.7 $e |- ( ph -> P =/= Q ) $.
    $( Injective condition for countability argument assuming that ` N ` is not
       a prime power.  (Contributed by metakunt, 7-Jan-2025.) $)
    aks6d1c2p2 $p |- ( ph -> E : ( NN0 X. NN0 ) -1-1-> NN ) $=
      ( cn0 co wceq wa wcel syl va vb vc vd vp cxp cn wf cv wral wf1 aks6d1c2p1
      wi wn wne cexp cdiv cmul neneq orcd simpr neneqd olcd jaoi anim1ci adantl
      wo neqne pm2.61dan impbii orcom bitri ianor bicomi cpc cprime wrex oveq1d
      ad5antr neeq12d caddc cc0 0cnd cdvds wbr prmnn jca nndivdvds mpbid adantr
      ad2antrr simp-4r nnexpcld pccld nn0cnd simplr simp-5l nncnd nnne0d eqcomd
      wb divcan2d breq2d cz nnzd euclemma syl3anc biimpd mpd c1 necom mpbi 1red
      imbi2i mpbird ad4antr simpllr nn0zd 3jca pcexp 3netr3d prmdvdsexpr zexpcl
      w3a pceq0 expne0d pcmul rspcedvd pcidlem simprl oveq2d biidd nnnn0d bitrd
      nnmulcld a1i simprr oveq12d ovmpod ralrimiva prmgt1 ltned sylib dvdsprime
      clt necomd pm4.56 syl2anc mtbird pcelnn mulcan2d necon3bid cq nnq divne0d
      orcnd addneintrd con3d divcld simp-5r addneintr2d eqidd jaodan necon3abid
      mtod pc11 notbid rexnal necon3bbid rexbidv sylan2br ex con4d f1opr sylibr
      cmpo ) AOOUFZUGEUHZUAUIZUBUIZEPZUCUIZUDUIZEPZQZUVSUWBQZUVTUWCQZRZUMZUDOUJ
      ZUCOUJZUBOUJZUAOUJZRUVQUGEUKAUVRUWMABDEFGHIJKULAUWLUAOAUVSOSZRZUWKUBOUWOU
      VTOSZRZUWJUCOUWQUWBOSZRZUWIUDOUWSUWCOSZRZUWHUWEUXAUWHUNZUWEUNUXAUXBRZUWAU
      WDUXCUWAUWDUOZBUVSUPPZFBUQPZUVTUPPZURPZBUWBUPPZUXFUWCUPPZURPZUOZUXBUXAUVT
      UWCUOZUWGUVSUWBUOZRZVGZUXLUXPUWFUNZUWGUNZVGZUXBUXPUXRUXQVGZUXSUXPUXTUXMUX
      TUXOUXMUXRUXQUVTUWCUSUTUXOUXQUXRUXOUVSUWBUWGUXNVAZVBVCVDUXRUXPUXQUXRUXMUX
      OUVTUWCVHUTZUXQUWGUXPUXQUWGRUXOUXMUXQUXNUWGUVSUWBVHVEVCUXRUXPUXQUYBVFVIVD
      VJUXRUXQVKVLUXBUXSUWFUWGVMVNVLUXAUXPRUXLUEUIZUXHVOPZUYCUXKVOPZUOZUEVPVQZU
      XAUXMUYGUXOUXAUXMRZUYFCUXHVOPZCUXKVOPZUOUECVPACVPSZUWNUWPUWRUWTUXMLVSZUYH
      UYCCQZRZUYDUYIUYEUYJUYNUYCCUXHVOUYHUYMVAZVRUYNUYCCUXKVOUYOVRVTUYHCUXEVOPZ
      CUXGVOPZWAPZCUXIVOPZCUXJVOPZWAPZUYIUYJUYHWBUYQWAPZWBUYTWAPZUYRVUAUYHWBUYQ
      UYTUYHWCUYHUYQUYHCUXGUYLUYHUXFUVTUXAUXFUGSZUXMUWQVUDUWRUWTUWOVUDUWPAVUDUW
      NABFWDWEZVUDJAFUGSZBUGSZRVUEVUDXAAVUFVUGHABVPSZVUGIBWFZTZWGFBWHTWIZWJWJZW
      KZWJZUWOUWPUWRUWTUXMWLZWMWNWOUYHUYTUYHCUXJUYLUYHUXFUWCVUNUWSUWTUXMWPZWMWN
      WOUYHUVTCUXFVOPZURPZUWCVUQURPZUYQUYTUYHVURVUSUOUXMUXAUXMVAUYHVURVUSUVTUWC
      UYHUVTUWCVUQUYHUVTVUOWOUYHUWCVUPWOUYHVUQUYHCUXFUYLVUNWNWOUYHVUQUYHAVUQUGS
      ZAUWNUWPUWRUWTUXMWQAVUTCUXFWDWEZACBWDWEZVVAACBUXFURPZWDWEZVVBVVAVGZACFWDW
      EVVDMAFVVCCWDAVVCFAFBAFHWRABVUJWRABVUJWSXBWTXCWIAVVDVVEAUYKBXDSZUXFXDSZVV
      DVVEXALABVUJXEAUXFVUKXECBUXFXFXGXHXIAVVBCBQZCXJQZVGZAVVHUNZVVIUNZRVVJUNAV
      VKVVLACBABCUOZUMACBUOZUMNVVMVVNABCXKXNXLVBZACXJAXJCAXJCAXMAUYKXJCUUEWELCU
      UATUUBUUFVBWGVVHVVIUUGUUCAVUHCUGSZVVBVVJXAIAUYKVVPLCWFTBCUUDUUHUUIUUPAUYK
      VUDRVUTVVAXAAUYKVUDLVUKWGCUXFUUJTXOTWSUUKUULXOUYHUYQVURUXAUYQVURQZUXMUXAU
      YKUXFUUMSZUXFWBUOZRZUVTXDSZYDVVQUXAUYKVVTVWAAUYKUWNUWPUWRUWTLXPZUXAVVRVVS
      UXAVUDVVRVUMUXFUUNTUXAFBUXAFAVUFUWNUWPUWRUWTHXPZWRZUXABUWQVUGUWRUWTUWOVUG
      UWPAVUGUWNVUJWJWJZWKZWRZUXAFVWCWSUXABVWFWSZUUOZWGZUXAUVTUWOUWPUWRUWTXQZXR
      ZXSUXFCUVTXTTWJWTUYHUYTVUSUXAUYTVUSQZUXMUXAUYKVVTUWCXDSZYDVWMUXAUYKVVTVWN
      VWBVWJUXAUWCUWSUWTVAZXRXSUXFCUWCXTTWJWTYAUUQUXAVUBUYRQUXMUXAWBUYPUYQWAUXA
      UYPWBUXAUYPWBQZCUXEWDWEZUNZUXAVVKVWRAVVKUWNUWPUWRUWTVVOXPZUXAVWQVVHUXAUYK
      VUHUWNVWQVVHUMVWBAVUHUWNUWPUWRUWTIXPZAUWNUWPUWRUWTWLZCBUVSYBXGUURXIUXAUYK
      UXEUGSZRVWPVWRXAUXAUYKVXBVWBUWQVXBUWRUWTUWQBUVSVWEAUWNUWPWPWMZWKWGCUXEYET
      XOWTVRWJUXAVUCVUAQUXMUXAWBUYSUYTWAUXAUYSWBUXAUYSWBQZCUXIWDWEZUNZUXAVXEVVH
      VWSUXAUYKVUHUWRVXEVVHUMVWBVWTUWQUWRUWTWPZCBUWBYBXGUVEUXAUYKUXIUGSZRVXDVXF
      XAUXAUYKVXHVWBUXABUWBVWFVXGWMZWGCUXIYETXOWTVRWJYAUYHUYIUYRUXAUYIUYRQZUXMU
      XAUYKUXEXDSZUXEWBUOZRZUXGXDSZUXGWBUOZRZYDVXJUXAUYKVXMVXPVWBUXAVXKVXLUXAVV
      FUWNRVXKUXAVVFUWNUXABVWFXEVXAWGBUVSYCTUXABUVSVWGVWHUXAUVSVXAXRYFWGZUXAVXN
      VXOUXAVVGUWPRVXNUXAVVGUWPUXAUXFVUMXEVWKWGUXFUVTYCTUXAUXFUVTUXAFBVWDVWGVWH
      UUSVWIVWLYFWGZXSUXEUXGCYGTWJWTUYHUYJVUAUXAUYJVUAQZUXMUXAUYKUXIXDSZUXIWBUO
      ZRZUXJXDSZUXJWBUOZRZYDVXSUXAUYKVYBVYEVWBUXAVXTVYAUXAUXIVXIXEUXAUXIVXIWSWG
      ZUXAVYCVYDUXAUXJUXAUXFUWCVUMVWOWMZXEUXAUXJVYGWSWGZXSUXIUXJCYGTWJWTYAYHUXA
      UXORZUYFBUXHVOPZBUXKVOPZUOUEBVPAVUHUWNUWPUWRUWTUXOIVSVYIUYCBQZRZUYDVYJUYE
      VYKVYMUYCBUXHVOVYIVYLVAZVRVYMUYCBUXKVOVYNVRVTVYIBUXEVOPZBUXGVOPZWAPZBUXIV
      OPZBUXJVOPZWAPZVYJVYKVYIVYQVYRVYPWAPVYQVYTVYIVYOVYRVYPVYIVYOVYIBUXEUXAVUH
      UXOVWTWJZVYIBUVSVYIVUHVUGWUAVUITZAUWNUWPUWRUWTUXOUUTZWMWNWOVYIVYRVYIBUXIW
      UAVYIBUWBWUBUWQUWRUWTUXOXQZWMWNWOVYIVYPVYIBUXGWUAVYIUXFUVTUXAVUDUXOVUMWJU
      WOUWPUWRUWTUXOWLWMWNWOVYIUVSUWBVYOVYRUXOUXNUXAUYAVFVYIVYOUVSVYIVUHUWNRVYO
      UVSQVYIVUHUWNWUAWUCWGUVSBYITWTVYIVYRUWBVYIVUHUWRRVYRUWBQVYIVUHUWRWUAWUDWG
      UWBBYITWTYAUVAVYIVYQUVBVYIVYPVYSVYRWAVYIUXGUXJBVOVYIUVTUWCUXFUPUXAUWGUXNY
      JYKYKYKYAUXAVYQVYJQUXOUXAVYJVYQUXAVUHVXMVXPYDVYJVYQQUXAVUHVXMVXPVWTVXQVXR
      XSUXEUXGBYGTWTWJUXAVYTVYKQZUXOUXAVUHVYBVYEYDZWUEUXAVUHVYBVYEVWTVYFVYHXSWU
      FVYKVYTUXIUXJBYGWTTWJYAYHUVCUXAUXLUYGXAUXPUXAUXLUYDUYEQZUNZUEVPVQZUYGUXAU
      XLWUGUEVPUJZUNZWUIUXAUXLUXHUXKQZUNWUKUXAWULUXHUXKUXAWULYLUVDUXAWULWUJUXAU
      XHOSZUXKOSZRWULWUJXAUXAWUMWUNUXAUXHUWSUXHUGSZUWTUWQWUOUWRUWQUXEUXGVXCUWQU
      XFUVTVULUWOUWPVAWMYOWJWJZYMUXAUXKUXAUXIUXJVXIVYGYOZYMWGUXHUXKUEUVFTUVGYNW
      UKWUIXAUXAWUIWUKWUGUEVPUVHVNYPYNUXAWUHUYFUEVPUXAWUGUYDUYEUXAWUGYLUVIUVJYN
      WJXOUVKUXAUXDUXLXAUXBUXAUWAUXHUWDUXKUXADGUVSUVTOOBDUIZUPPZUXFGUIZUPPZURPZ
      UXHEUGEDGOOWVBUVPQUXAKYPZUXAWURUVSQZWUTUVTQZRRZWUSUXEWVAUXGURWVFWURUVSBUP
      UXAWVDWVEYJYKWVFWUTUVTUXFUPUXAWVDWVEYQYKYRVXAVWKWUPYSUXADGUWBUWCOOWVBUXKE
      UGWVCUXAWURUWBQZWUTUWCQZRRZWUSUXIWVAUXJURWVIWURUWBBUPUXAWVGWVHYJYKWVIWUTU
      WCUXFUPUXAWVGWVHYQYKYRVXGVWOWUQYSVTWJXOVBUVLUVMYTYTYTYTWGUDUCOOUGEUBUAUVN
      UVO $.
  $}

  ${
    hashscontpowcl.1 $e |- ( ph -> N e. NN ) $.
    hashscontpowcl.2 $e |- ( ph -> P e. Prime ) $.
    hashscontpowcl.3 $e |- ( ph -> P || N ) $.
    hashscontpowcl.4 $e |- ( ph -> R e. NN ) $.
    hashscontpowcl.5 $e |- ( ph -> ( N gcd R ) = 1 ) $.
    hashscontpowcl.6 $e |- E = ( k e. NN0 , l e. NN0 |->
    ( ( P ^ k ) x. ( ( N / P ) ^ l ) ) ) $.
    hashscontpowcl.7 $e |- L = ( ZRHom ` Y ) $.
    hashscontpowcl.8 $e |- Y = ( Z/nZ ` R ) $.
    $( Closure of E for ~ https://www3.nd.edu/%7eandyp/notes/AKS.pdf Theorem
       6.1.  (Contributed by metakunt, 28-Apr-2025.) $)
    hashscontpowcl $p |- ( ph -> ( # ` ( L "
     ( E " ( NN0 X. NN0 ) ) ) ) e. NN0 ) $=
      ( cn0 wcel syl cxp cima cfn chash cfv cbs cn eqid crg czring crh co cz wf
      znfi ccrg nnnn0d zncrng crngring zrhrhm zringbas rhmf fimass ssfid hashcl
      wss 4syl ) AFERRUAUBZUBZUCSVIUDUERSAHUFUEZVIACUGSVJUCSMVJCHQVJUHZUOTAHUIS
      ZFUJHUKULSUMVJFUNVIVJVFAHUPSZVLACRSVMACMUQCHQURTHUSTHFPUTUMVJUJHFVAVKVBUM
      VJFVHVCVGVDVIVET $.
  $}

  ${
    $d A i $.  $d B i $.  $d N i j $.  $d N i x y $.  $d R i j $.
    $d R i x y $.  $d j ph $.  $d ph x y $.
    hashscontpow1.1 $e |- ( ph -> N e. NN ) $.
    hashscontpow1.2 $e |- ( ph -> A e. ( 1 ... ( ( odZ ` R ) ` N ) ) ) $.
    hashscontpow1.3 $e |- ( ph -> B e. ( 1 ... ( ( odZ ` R ) ` N ) ) ) $.
    hashscontpow1.4 $e |- ( ph -> R e. NN ) $.
    hashscontpow1.5 $e |- ( ph -> ( N gcd R ) = 1 ) $.
    hashscontpow1.6 $e |- L = ( ZRHom ` Y ) $.
    hashscontpow1.7 $e |- Y = ( Z/nZ ` R ) $.
    hashscontpow1.8 $e |- ( ph -> A < B ) $.
    $( Helper lemma for to prove inequality in Zr.  (Contributed by metakunt,
       28-Apr-2025.) $)
    hashscontpow1 $p |- ( ph -> ( L ` ( N ^ A ) )
     =/= ( L ` ( N ^ B ) ) ) $=
      ( co wbr c1 wcel adantr vi vx vy vj cexp cfv wceq cmin codz elfzelzd zred
      clt resubcld cn cz cgcd odzcl syl3anc nnred cfz elfznn syl nnrpd ltsubrpd
      nnzd cle elfzle2 ltletrd wa wn cv cdvds crab cr cinf odzval wss wral wrex
      elrabi adantl ex ssrdv 1red simpr breq1d ralbidv ralrimiva rspcedvd oveq2
      nnge1d oveq1d breq2d cc0 zsubcld posdifd mpbid jca sylibr w3a cmul nnnn0d
      elnnz cn0 zexpcld 1zzd 3jca eqcomd wb zndvds zcnd 0red elnn0z 1cnd subdid
      ltled caddc pncan3d oveq2d expaddd mulridd oveq12d eqtr2d breqtrd gcdcomd
      recnd nncnd eqtrd rpexp mpbird coprmdvds syl2anc infrelb eqbrtrd pm2.65da
      imp elrabd lenltd neqned ) AFBUEPZEUFZFCUEPZEUFZAUUAUUCUGZCBUHPZFDUIUFUFZ
      ULQZAUUGUUDAUUECUUFACBACACRUUFJUJZUKZABABRUUFIUJZUKZUMZUUIAUUFADUNSZFUOSZ
      FDUPPRUGZUUFUNSZKAFHVEZLFDUQURZUSACBUUIABABRUUFUTPZSBUNSZIBUUFVAVBZVCVDAC
      UUSSZCUUFVFQJCRUUFVGVBVHTAUUDVIZUUFUUEVFQUUGVJUVCUUFDFUAVKZUEPZRUHPZVLQZU
      AUNVMZVNULVOZUUEVFAUUFUVIUGZUUDAUUMUUNUUOUVJKUUQLFUADVPURTUVCUVHVNVQZUBVK
      ZUCVKZVFQZUCUVHVRZUBVNVSZUUEUVHSUVIUUEVFQAUVKUUDAUDUVHVNAUDVKZUVHSZUVQVNS
      AUVRVIUVQUVRUVQUNSAUVGUAUVQUNVTWAUSWBWCTAUVPUUDAUVORUVMVFQZUCUVHVRUBRVNAW
      DAUVLRUGZVIZUVNUVSUCUVHUWAUVLRUVMVFAUVTWEWFWGAUVSUCUVHAUVMUVHSZVIUVMUWBUV
      MUNSAUVGUAUVMUNVTWAWKWHWITUVCUVGDFUUEUEPZRUHPZVLQZUAUUEUNUVDUUEUGZUVFUWDD
      VLUWFUVEUWCRUHUVDUUEFUEWJWLWMUVCUUEUOSZWNUUEULQZVIUUEUNSUVCUWGUWHUVCCBACU
      OSUUDUUHTABUOSUUDUUJTWOAUWHUUDABCULQUWHOABCUUKUUIWPWQZTWRUUEXCWSZUVCDUOSZ
      YTUOSZUWDUOSZWTZDYTUWDXAPZVLQZDYTUPPZRUGZVIZUWEUVCUWKUWLUWMAUWKUUDADKVEZT
      UVCFBAUUNUUDUUQTZABXDSUUDABUVAXBZTXEZUVCUWCRUVCFUUEUXAUVCUUEUWJXBXEUVCXFW
      OXGUVCUWPUWRUVCDUUBYTUHPZUWOVLUVCUUCUUAUGZDUXDVLQZUVCUUAUUCAUUDWEXHUVCDXD
      SZUUBUOSZUWLUXEUXFXIAUXGUUDADKXBTAUXHUUDAFCUUQACAUVBCUNSJCUUFVAVBXBXETUXC
      UUBYTEDGNMXJURWQAUXDUWOUGUUDAUWOYTUWCXAPZYTRXAPZUHPUXDAYTUWCRAYTAFBUUQUXB
      XEZXKZAUWCAFUUEUUQAUWGWNUUEVFQZVIUUEXDSAUWGUXMACBUUHUUJWOAWNUUEAXLUULUWIX
      PWRUUEXMWSZXEXKAXNXOAUXIUUBUXJYTUHAUUBUXIAUUBFBUUEXQPZUEPUXIACUXOFUEAUXOC
      ABCABUUKYFACUUIYFXRXHXSAFBUUEAFHYGUXNUXBXTYHXHAYTUXLYAYBYCTYDAUWRUUDAUWQY
      TDUPPZRADYTUWTUXKYEAUXPRUGZUUOLAUUNUWKUUTUXQUUOXIUUQUWTUVAFDBYIURYJYHTWRU
      WNUWSUWEDYTUWDYKYPYLYQUBUCUUEUVHYMURYNUVCUUFUUEUVCUUFAUUPUUDUURTUSAUUEVNS
      UUDUULTYRWQYOYS $.
  $}

  ${
    $d E k x $.  $d L a b x $.  $d N a b x $.  $d N k x $.  $d R a b x $.
    $d a b ph x $.
    hashscontpow.1 $e |- ( ph -> E C_ ZZ ) $.
    hashscontpow.2 $e |- ( ph -> N e. NN ) $.
    hashscontpow.3 $e |- ( ph -> A. k e. NN0 ( N ^ k ) e. E ) $.
    hashscontpow.4 $e |- ( ph -> R e. NN ) $.
    hashscontpow.5 $e |- ( ph -> ( N gcd R ) = 1 ) $.
    hashscontpow.6 $e |- L = ( ZRHom ` Y ) $.
    hashscontpow.7 $e |- Y = ( Z/nZ ` R ) $.
    $( If a set contains all ` N ` -th powers, then the size of the image under
       the ZR homomorphism is greater than the ` R ` -th order of ` N ` .
       (Contributed by metakunt, 28-Apr-2025.) $)
    hashscontpow $p |- ( ph -> ( ( odZ ` R ) ` N ) <_ ( # ` ( L " E ) ) ) $=
      ( cfv co wcel wceq cvv wa vx va vb c1 codz cfz chash cima cle cn0 cn cgcd
      cz nnzd odzcl syl3anc nnnn0d hashfz1 syl cv cexp cmpt wf1 wbr mptexd czrh
      ovexd fvexi a1i imaexg wf wi wral wfn cbs ccrg crg czring zncrng crngring
      crh zrhrhm zringbas eqid rhmf 4syl ffnd adantr elfznn adantl oveq2 eleq1d
      zexpcld rspcdva fnfvimad fmpttd wn wne clt ad3antrrr simpllr simplr simpr
      wo hashscontpow1 necomd jaodan ex biidd necon3bbid cr elfzelz zred lttri2
      syl2anc bitrd imbi1d mpbird imp eqidd oveq2d fveq2d fvmptd neeq12d neneqd
      wb fvexd con4d ralrimiva jca dff13 sylibr hashf1dmcdm eqbrtrrd ) AUDFBUEO
      OZUFPZUGOZYOEDUHZUGOZUIAYOUJQYQYORAYOABUKQZFUMQZFBULPUDRZYOUKQKAFIUNZLFBU
      OUPUQYOURUSAUAYPFUAUTZVAPZEOZVBZSQYRSQZYPYRUUGVCZYQYSUIVDAUAYPUUFSAUDYOUF
      VGVEAESQZUUHUUJAEGVFMVHVIEDSVJUSAYPYRUUGVKZUBUTZUUGOZUCUTZUUGOZRZUULUUNRZ
      VLZUCYPVMZUBYPVMZTUUIAUUKUUTAUAYPUUFYRAUUDYPQZTZUMUUEDEAEUMVNUVAAUMGVOOZE
      AGVPQZGVQQEVRGWAPQUMUVCEVKABUJQUVDABKUQBGNVSUSGVTGEMWBUMUVCVRGEWCUVCWDWEW
      FWGWHUVBFUUDAUUAUVAUUCWHUVBUUDUVAUUDUKQAUUDYOWIWJUQZWMUVBFCUTZVAPZDQZUUED
      QCUJUUDUVFUUDRUVGUUEDUVFUUDFVAWKWLAUVHCUJVMUVAJWHUVEWNWOWPAUUSUBYPAUULYPQ
      ZTZUURUCYPUVJUUNYPQZTZUUQUUPUVLUUQWQZUUPWQUVLUVMTZUUMUUOUVNUUMUUOWRFUULVA
      PZEOZFUUNVAPZEOZWRZUVLUVMUVSUVLUVMUVSVLUULUUNWSVDZUUNUULWSVDZXDZUVSVLUVLU
      WBUVSUVLUVTUVSUWAUVLUVTTUULUUNBEFGAFUKQZUVIUVKUVTIWTAUVIUVKUVTXAUVJUVKUVT
      XBAYTUVIUVKUVTKWTAUUBUVIUVKUVTLWTMNUVLUVTXCXEUVLUWATZUVRUVPUWDUUNUULBEFGA
      UWCUVIUVKUWAIWTUVJUVKUWAXBAUVIUVKUWAXAAYTUVIUVKUWAKWTAUUBUVIUVKUWALWTMNUV
      LUWAXCXEXFXGXHUVLUVMUWBUVSUVLUVMUULUUNWRZUWBUVLUUQUULUUNUVLUUQXIXJUVLUULX
      KQUUNXKQZUWEUWBYFUVLUULUVJUULUMQZUVKUVIUWGAUULUDYOXLWJWHXMUVKUWFUVJUVKUUN
      UUNUDYOXLXMWJUULUUNXNXOXPXQXRXSUVNUUMUVPUUOUVRUVNUAUULUUFUVPYPUUGSUVNUUGX
      TZUVNUUDUULRZTZUUEUVOEUWJUUDUULFVAUVNUWIXCYAYBAUVIUVKUVMXAUVNUVOEYGYCUVNU
      AUUNUUFUVRYPUUGSUWHUVNUUDUUNRZTZUUEUVQEUWLUUDUUNFVAUVNUWKXCYAYBUVJUVKUVMX
      BUVNUVQEYGYCYDXRYEXHYHYIYIYJUBUCYPYRUUGYKYLYPYRUUGSSYMUPYN $.
  $}

  ${
    $d E i $.  $d E x $.  $d N i q $.  $d N k l q $.  $d P k l q $.
    $d ph k l $.  $d i ph q $.  $d ph x $.  $d N k l $.
    aks6d1c3.1 $e |- ( ph -> N e. NN ) $.
    aks6d1c3.2 $e |- ( ph -> P e. Prime ) $.
    aks6d1c3.3 $e |- ( ph -> P || N ) $.
    aks6d1c3.4 $e  |- ( ph -> R e. NN ) $.
    aks6d1c3.5 $e |- ( ph -> ( N gcd R ) = 1 ) $.
    aks6d1c3.6 $e |- E = ( k e. NN0 , l e. NN0 |->
    ( ( P ^ k ) x. ( ( N / P ) ^ l ) ) ) $.
    aks6d1c3.7 $e |- L = ( ZRHom ` Y ) $.
    aks6d1c3.8 $e |- Y = ( Z/nZ ` R ) $.
    aks6d1c3.9 $e |- ( ph -> ( ( 2 logb N ) ^ 2 ) < ( ( odZ ` R ) ` N ) ) $.
    $( Claim 3 of Theorem 6.1 of the AKS inequality lemma.
       ~ https://www3.nd.edu/%7eandyp/notes/AKS.pdf (Contributed by metakunt,
       28-Apr-2025.) $)
    aks6d1c3 $p |- ( ph -> ( ( 2 logb N ) ^ 2 ) <
     ( # ` ( L " ( E " ( NN0 X. NN0 ) ) ) ) ) $=
      ( co cn0 vi vx vq clogb cexp codz cfv cxp cima chash wcel 2re a1i cc0 clt
      c2 cr 2pos nnred nngt0d c1 1red 1lt2 ltned necomd relogbcld resqcld cn cz
      wbr cgcd wceq nnzd odzcl syl3anc hashscontpowcl nn0red nfv cdiv cmul wral
      cv wf wa cprime prmnn syl adantr simplr zexpcld cdvds wne nnne0d dvdsval2
      wb mpbid simpr zmulcld ralrimiva sylib ffund ffvelcdmda funimassd cop wfn
      fmpo ffnd opelxpd fnfvimad c1st c2nd cmpt vex op1std oveq2d op2ndd mpompt
      cmpo oveq12d eqtr4i fveq2d opelxp sylibr xp1st xp2nd op1st op2nd cc recnd
      fvmptd divcan2d eqcomd oveq1d mulexpd eqtr2d eleq1d hashscontpow ltletrd
      zcnd eqtrd ) AUPGUDSZUPUESGCUFUGUGZFETTUHZUIZUIUJUGZAUUAAUPGUPUQUKAULUMUN
      UPUOVJAURUMAGJUSZAGJUTAVAUPAVAUPAVBVAUPUOVJAVCUMVDVEVFVGAUUBACVHUKGVIUKZG
      CVKSVAVLUUBVHUKMAGJVMZNGCVNVOUSAUUEABCDEFGHIJKLMNOPQVPVQRACUAUUDFGHAUBUUC
      VIEAUBVRAUUCVIEABDWBZUESZGBVSSZIWBZUESZVTSZVIUKZITWAZDTWAUUCVIEWCAUUPDTAU
      UITUKZWDZUUOITUURUULTUKZWDZUUJUUMUUTBUUIUURBVIUKZUUSAUVAUUQABABWEUKBVHUKK
      BWFWGZVMZWHWHAUUQUUSWIWJUUTUUKUULUURUUKVIUKZUUSAUVDUUQABGWKVJZUVDLAUVABUN
      WLZUUGUVEUVDWOUVCABUVBWMZUUHBGWNVOWPZWHWHUURUUSWQWJWRWSWSDITTUUNVIEOXFWTZ
      XAAUUCVIUBWBEUVIXBXCJAGUAWBZUESZUUDUKZUATAUVJTUKZWDZUVJUVJXDZEUGZUUDUKUVL
      UVNUUCUVOUUCEAEUUCXEUVMAUUCVIEUVIXGWHUVNUVJUVJTTAUVMWQZUVQXHZUVRXIUVNUVPU
      VKUUDUVNUVPBUVOXJUGZUESZUUKUVOXKUGZUESZVTSZUVKUVNUCUVOBUCWBZXJUGZUESZUUKU
      WDXKUGZUESZVTSZUWCUUCEVIEUCUUCUWIXLZVLUVNEDITTUUNXRUWJODIUCTTUWIUUNUWDUUI
      UULXDVLZUWFUUJUWHUUMVTUWKUWEUUIBUEUUIUULUWDDXMZIXMZXNXOUWKUWGUULUUKUEUUIU
      ULUWDUWLUWMXPXOXSXQXTUMUVNUWDUVOVLZWDZUWFUVTUWHUWBVTUWOUWEUVSBUEUWOUWDUVO
      XJUVNUWNWQZYAXOUWOUWGUWAUUKUEUWOUWDUVOXKUWPYAXOXSUVNUVMUVMWDZUVOUUCUKZUVN
      UWRUWQUVRUVJUVJTTYBZWTUWSYCUVNUVTUWBUVNBUVSAUVAUVMUVCWHZUVNUWRUVSTUKUVRUV
      OTTYDWGWJUVNUUKUWAAUVDUVMUVHWHZUVNUWRUWATUKUVRUVOTTYEWGWJWRYJUVNUWCBUVJUE
      SZUUKUVJUESZVTSZUVKUVNUVTUXBUWBUXCVTUVNUVSUVJBUEUVSUVJVLUVNUVJUVJUAXMZUXE
      YFUMXOUVNUWAUVJUUKUEUWAUVJVLUVNUVJUVJUXEUXEYGUMXOXSUVNUVKBUUKVTSZUVJUESUX
      DUVNGUXFUVJUEUVNUXFGUVNGBAGYHUKUVMAGUUFYIWHUVNBUWTYSZAUVFUVMUVGWHYKYLYMUV
      NBUUKUVJUXGUVNUUKUXAYSUVQYNYOYTYTYPWPWSMNPQYQYR $.
  $}

  ${
    $d E a b c $.  $d E c d e $.  $d L a b c $.  $d N k l m $.  $d P k l m $.
    $d R a c $.  $d R c e $.  $d a c ph $.  $d e m ph $.
    aks6d1c4.1 $e |- ( ph -> N e. NN ) $.
    aks6d1c4.2 $e |- ( ph -> P e. Prime ) $.
    aks6d1c4.3 $e |- ( ph -> P || N ) $.
    aks6d1c4.4 $e |- ( ph -> R e. NN ) $.
    aks6d1c4.5 $e |- ( ph -> ( N gcd R ) = 1 ) $.
    aks6d1c4.6 $e |- E = ( k e. NN0 , l e. NN0 |->
    ( ( P ^ k ) x. ( ( N / P ) ^ l ) ) ) $.
    aks6d1c4.7 $e |- L = ( ZRHom ` ( Z/nZ ` R ) ) $.
    $( Claim 4 of Theorem 6.1 of the AKS inequality lemma.
       ~ https://www3.nd.edu/%7eandyp/notes/AKS.pdf (Contributed by metakunt,
       12-May-2025.) $)
    aks6d1c4 $p |- ( ph -> ( # ` ( L " ( E " ( NN0 X. NN0 ) ) ) ) <_
    ( phi ` R ) ) $=
      ( wcel wa wceq co adantr va vb vc vd vm ve cn0 cxp cima chash cfv czn cui
      cphi cle cvv wss wbr fvexd cv wrex wfun cz cbs ccrg crg czring crh nnnn0d
      wf eqid zncrng syl crngring zrhrhm zringbas rhmf 4syl ffund simpr fvelima
      syl2anc wi eqcomd simpll jca cgcd c1st cexp cdiv c2nd cmul ovexd cmpo vex
      c1 oveq2d oveq12d oveq1d fveq2d cn nnzd adantl zexpcld cdvds cc0 dvdsval2
      wne wb syl3anc eqeltrd w3a 3jca rpdvds ad2antrr rprpwr mpd anim1i elnnne0
      wn sylibr ex necon1bd cc exp0d eqtrd pm2.61dan nnred recnd nngt0d gt0ne0d
      imp mpbird simprd simpld nfv fveqeq2 cbvrexw bilani r19.29a op1std op2ndd
      cmpt cop mpompt eqcomi eqtri fmptd simplll a1i fvmptd cprime prmnn nnne0d
      xp1st mpbid xp2nd zmulcld gcdcomd gcdcom pm5.74i mpbi zcnd ddcand divgt0d
      eqeq1 gcd1 clt elnnz divcld rpmul znunit ssrdv hashss znunithash breqtrd
      ) AFEUGUGUHZUIZUIZUJUKZCULUKZUMUKZUJUKZCUNUKZUOAUWBUPPUVSUWBUQUVTUWCUOURA
      UWAUMUSAUAUVSUWBAUAUTZUVSPZUWEUWBPZAUWFQZUBUTZFUKUWERZUBUVRVAZUWGUWHFVBZU
      WFUWKAUWLUWFAVCUWAVDUKZFAUWAVEPZUWAVFPFVGUWAVHSPVCUWMFVJACUGPZUWNACLVIZCU
      WAUWAVKZVLVMUWAVNUWAFOVOVCUWMVGUWAFVPUWMVKVQVRVSTAUWFVTUBUWEUVRFWAWBAUWKU
      WGWCUWFAUWKUWGAUWKQZUCUTZFUKZUWERZUWGUCUVRUWRUWSUVRPZQZUXAQZUWEUWTUWBUXDU
      WTUWEUXCUXAVTWDUXCUWTUWBPZUXAUXCAUXBQZUXEUXCAUXBAUWKUXBWEUWRUXBVTWFUXFUXE
      UWSCWGSZWPRZUXFUXHUWSVCPZUXFUDUTZEUKUWSRZUDUVQVAZUXHUXIQZUXFEVBZUXBUXLAUX
      NUXBAUVQUPEAUEUVQBUEUTZWHUKZWISZGBWJSZUXOWKUKZWISZWLSZUPEAUXOUVQPQUXQUXTW
      LWMEDHUGUGBDUTZWISZUXRHUTZWISZWLSZWNZUEUVQUYAUUCZNUYHUYGDHUEUGUGUYAUYFUXO
      UYBUYDUUDRZUXQUYCUXTUYEWLUYIUXPUYBBWIUYBUYDUXODWOZHWOZUUAWQUYIUXSUYDUXRWI
      UYBUYDUXOUYJUYKUUBWQWRUUEUUFUUGZUUHVSTAUXBVTUDUWSUVQEWAWBUXFUXLUXMUXFUXLQ
      ZUFUTZEUKZUWSRZUXMUFUVQUYMUYNUVQPZQZUYPQZUXHUXIUYSUXGUYOCWGSZWPUYSUWSUYOC
      WGUYSUYOUWSUYRUYPVTWDZWSUYSUYOVCPZUYTWPRZUYRVUBVUCQZUYPUYRAUYQQZVUDUYRAUY
      QAUXBUXLUYQUUIUYMUYQVTWFVUEVUBVUCVUEUYOBUYNWHUKZWISZUXRUYNWKUKZWISZWLSZVC
      VUEUEUYNUYAVUJUVQEUPEUYHRVUEUYLUUJVUEUXOUYNRZQZUXQVUGUXTVUIWLVULUXPVUFBWI
      VULUXOUYNWHVUEVUKVTZWTWQVULUXSVUHUXRWIVULUXOUYNWKVUMWTWQWRAUYQVTVUEVUGVUI
      WLWMUUKZVUEVUGVUIVUEBVUFABVCPZUYQABABUULPBXAPZJBUUMVMZXBZTZUYQVUFUGPZAUYN
      UGUGUUOXCZXDZVUEUXRVUHAUXRVCPZUYQABGXEURZVVCKAVUOBXFXHZGVCPZVVDVVCXIVURAB
      VUQUUNZAGIXBZBGXGXJUUPZTUYQVUHUGPZAUYNUGUGUUQXCZXDZUURZXKVUEUYTVUJCWGSZWP
      VUEUYOVUJCWGVUNWSVUEVVNCVUJWGSZWPVUEVUJCVVMACVCPZUYQACLXBZTZUUSVUECVUGWGS
      ZWPRZCVUIWGSZWPRZQZVVOWPRZVUEVVTVWBVUEVUFXAPZVVTVUEVWEQZCBWGSWPRZVVTVUEVW
      GVWEAVWGUYQAVVPVUOVVFXLCGWGSZWPRZVVDQVWGAVVPVUOVVFVVQVURVVHXMAVWIVVDAGCWG
      SZWPRZWCAVWIWCMAVWKVWIAVWJVWHRZVWKVWIXIAVVFVVPQVWLAVVFVVPVVHVVQWFGCUUTVMV
      WJVWHWPUVFVMUVAUVBZKWFCBGXNWBTTVWFCXAPZVUPVWEVWGVVTWCAVWNUYQVWELXOAVUPUYQ
      VWEVUQXOVUEVWEVTCBVUFXPXJXQVUEVWEXTZQZVVSCBXFWISZWGSZWPVWPVUGVWQCWGVWPVUF
      XFBWIVUEVWOVUFXFRVUEVWEVUFXFVUEVUFXFXHZVWEVUEVWSQVUTVWSQVWEVUEVUTVWSVVAXR
      VUFXSYAYBYCYLWQWQVWPVWRCWPWGSZWPVWPVWQWPCWGVWPBVUEBYDPZVWOVUEBVUSUVCZTYEW
      QVWPVVPVWTWPRZVUEVVPVWOVVRTCUVGZVMYFYFYGVUEVUHXAPZVWBVUEVXEQZCUXRWGSWPRZV
      WBVUEVXGVXEAVXGUYQAVVPVVCVVFXLVWIUXRGXEURZQVXGAVVPVVCVVFVVQVVIVVHXMAVWIVX
      HVWMAVXHGUXRWJSZVCPZAVXIBVCAGBAGAGIYHZYIZABABVUQYHZYIAGAGIYJZYKVVGUVDVURX
      KAVVCUXRXFXHVVFVXHVXJXIVVIAUXRAGBVXKVXMVXNABVUQYJUVEZYKVVHUXRGXGXJYMWFCUX
      RGXNWBTTVXFVWNUXRXAPZVXEVXGVWBWCAVWNUYQVXELXOVUEVXPVXEAVXPUYQAVVCXFUXRUVH
      URZQVXPAVVCVXQVVIVXOWFUXRUVIYATTVUEVXEVTCUXRVUHXPXJXQVUEVXEXTZQZVWAVWTWPV
      XSVWACUXRXFWISZWGSVWTVXSVUIVXTCWGVXSVUHXFUXRWIVUEVXRVUHXFRVUEVXEVUHXFVUEV
      UHXFXHZVXEVUEVYAQVVJVYAQVXEVUEVVJVYAVVKXRVUHXSYAYBYCYLWQWQVXSVXTWPCWGVXSU
      XRVXSGBVUEGYDPZVXRAVYBUYQVXLTTVUEVXAVXRVXBTAVVEUYQVXRVVGXOUVJYEWQYFVXSVVP
      VXCVUEVVPVXRVVRTVXDVMYFYGWFVUEVVPVUGVCPVUIVCPVWCVWDWCVVRVVBVVLCVUGVUIUVKX
      JXQYFYFWFVMTZYNYFUYSUWSUYOVCVUAUYSVUBVUCVYCYOXKWFUXLUYPUFUVQVAUXFUXKUYPUD
      UFUVQUXKUFYPUYPUDYPUXJUYNUWSEYQYRYSYTYBXQZYOUXFUWOUXIUXEUXHXIAUWOUXBUWPTU
      XFUXHUXIVYDYNUWSUWBFCUWAUWQUWBVKZOUVLWBYMVMTXKUWKUXAUCUVRVAAUWJUXAUBUCUVR
      UWJUCYPUXAUBYPUWIUWSUWEFYQYRYSYTYBTXQYBUVMUWBUVSUPUVNWBAVWNUWCUWDRLUWBCUW
      AUWQVYEUVOVMUVP $.
  $}

  ${
    $d .~ a $.  $d N x $.  $d P e f $.  $d R x $.  $d N e f z $.  $d a ph $.
    $d N a $.  $d L e f z $.  $d R e f y z $.  $d E e f z $.  $d A g i $.
    $d A x z $.  $d A a $.  $d F g i $.  $d K x $.  $d K g i $.  $d K a $.
    $d P x z $.  $d K e f y z $.  $d i z $.  $d ph x z $.  $d .~ z $.
    $d U e f z $.  $d g i ph $.  $d F e f z $.
    aks6d1c1rh.1 $e |- .~ = { <. e , f >. | ( e e. NN /\ f e.
     ( Base ` ( Poly1 ` K ) ) /\ A. y e. ( ( mulGrp ` K ) PrimRoots R )
     ( e ( .g ` ( mulGrp ` K ) ) ( ( ( eval1 ` K ) ` f ) ` y ) ) =
     ( ( ( eval1 ` K ) ` f ) ` ( e ( .g ` ( mulGrp ` K ) ) y ) ) ) } $.
    aks6d1c1rh.2 $e |- P = ( chr ` K ) $.
    aks6d1c1rh.3 $e |- ( ph -> K e. Field ) $.
    aks6d1c1rh.4 $e |- ( ph -> P e. Prime ) $.
    aks6d1c1rh.5 $e |- ( ph -> R e. NN ) $.
    aks6d1c1rh.6 $e |- ( ph -> N e. NN ) $.
    aks6d1c1rh.7 $e |- ( ph -> P || N ) $.
    aks6d1c1rh.8 $e |- ( ph -> ( N gcd R ) = 1 ) $.
    aks6d1c1rh.9 $e |- ( ph -> F : ( 0 ... A ) --> NN0 ) $.
    aks6d1c1rh.10 $e |- G = ( g e. ( NN0 ^m ( 0 ... A ) ) |->
    ( ( mulGrp ` ( Poly1 ` K ) ) gsum ( i e. ( 0 ... A ) |-> ( ( g ` i )
    ( .g ` ( mulGrp ` ( Poly1 ` K ) ) ) ( ( var1 ` K ) ( +g ` ( Poly1 ` K ) )
    ( ( algSc ` ( Poly1 ` K ) ) ` ( ( ZRHom ` K ) ` i ) ) ) ) ) ) ) $.
    aks6d1c1rh.11 $e |- ( ph -> A e. NN0 ) $.
    aks6d1c1rh.12 $e |- ( ph -> U e. NN0 ) $.
    aks6d1c1rh.13 $e |- ( ph -> L e. NN0 ) $.
    aks6d1c1rh.14 $e |- E = ( ( P ^ U ) x. ( ( N / P ) ^ L ) ) $.
    aks6d1c1rh.15 $e |- ( ph -> A. a e. ( 1 ... A ) N .~ ( ( var1 ` K )
     ( +g ` ( Poly1 ` K ) )
     ( ( algSc ` ( Poly1 ` K ) ) ` ( ( ZRHom ` K ) ` a ) ) ) ) $.
    aks6d1c1rh.16 $e |- ( ph -> ( x e. ( Base ` K ) |->
     ( P ( .g ` ( mulGrp ` K ) ) x ) ) e. ( K RingIso K ) ) $.
    $( Claim 1 of AKS primality proof with collapsed definitions since their
       ease of use is no longer needed.  (Contributed by metakunt,
       1-May-2025.) $)
    aks6d1c1rh $p |- ( ph -> E .~ ( G ` F ) ) $=
      ( vz cpl1 cfv cbs cascl cmgp cmg cplusg ce1 cv cn wcel co wceq cprimroots
      cv1 wral w3a copab nfv fveq2 oveq2d oveq2 eqeq12d cbvralw 3anbi3i opabbii
      fveq2d eqtri eqid aks6d1c1 ) ABUPDPUQURZUSURZWGUTURZWGVAURZVBURZEWGVCURZF
      GWGHIJKLMPVAURZVBURZNOPQRPVDURZWMWJPVKURZSFIVEZVFVGZJVEZWHVGZWQCVEZWSWOUR
      ZURZWNVHZWQXAWNVHZXBURZVIZCWMGVJVHZVLZVMZIJVNWRWTWQUPVEZXBURZWNVHZWQXKWNV
      HZXBURZVIZUPXHVLZVMZIJVNTXJXRIJXIXQWRWTXGXPCUPXHXGUPVOXPCVOXAXKVIZXDXMXFX
      OXSXCXLWQWNXAXKXBVPVQXSXEXNXBXAXKWQWNVRWCVSVTWAWBWDWGWEWHWEWPWEWJWEWMWEWN
      WEWIWEWKWEUAWOWEWLWEUBUCUDUEUFUGUHUIUJUKULUMUNUOWF $.
  $}

  ${
    aks6d1c2.1 $e |- .~ = { <. e , f >. | ( e e. NN /\ f e.
     ( Base ` ( Poly1 ` K ) ) /\ A. y e. ( ( mulGrp ` K ) PrimRoots R )
     ( e ( .g ` ( mulGrp ` K ) ) ( ( ( eval1 ` K ) ` f ) ` y ) ) =
     ( ( ( eval1 ` K ) ` f ) ` ( e ( .g ` ( mulGrp ` K ) ) y ) ) ) } $.
    aks6d1c2.2 $e |- P = ( chr ` K ) $.
    aks6d1c2.3 $e |- ( ph -> K e. Field ) $.
    aks6d1c2.4 $e |- ( ph -> P e. Prime ) $.
    aks6d1c2.5 $e |- ( ph -> R e. NN ) $.
    aks6d1c2.6 $e |- ( ph -> N e. NN ) $.
    aks6d1c2.7 $e |- ( ph -> P || N ) $.
    aks6d1c2.8 $e |- ( ph -> ( N gcd R ) = 1 ) $.
    aks6d1c2.9 $e |- ( ph -> F : ( 0 ... A ) --> NN0 ) $.
    aks6d1c2.10 $e |- G = ( g e. ( NN0 ^m ( 0 ... A ) ) |->
    ( ( mulGrp ` ( Poly1 ` K ) ) gsum ( i e. ( 0 ... A ) |-> ( ( g ` i )
    ( .g ` ( mulGrp ` ( Poly1 ` K ) ) ) ( ( var1 ` K ) ( +g ` ( Poly1 ` K ) )
    ( ( algSc ` ( Poly1 ` K ) ) ` ( ( ZRHom ` K ) ` i ) ) ) ) ) ) ) $.
    aks6d1c2.11 $e |- ( ph -> A e. NN0 ) $.
    aks6d1c2.12 $e |- E = ( k e. NN0 , l e. NN0 |->
    ( ( P ^ k ) x. ( ( N / P ) ^ l ) ) ) $.
    aks6d1c2.13 $e |- L = ( ZRHom ` ( Z/nZ ` R ) ) $.
    aks6d1c2.14 $e |- ( ph -> A. a e. ( 1 ... A ) N .~ ( ( var1 ` K )
     ( +g ` ( Poly1 ` K ) )
     ( ( algSc ` ( Poly1 ` K ) ) ` ( ( ZRHom ` K ) ` a ) ) ) ) $.
    aks6d1c2.15 $e |- ( ph -> ( x e. ( Base ` K ) |->
     ( P ( .g ` ( mulGrp ` K ) ) x ) ) e. ( K RingIso K ) ) $.
    aks6d1c2.16 $e |- ( ph -> M e. ( ( mulGrp ` K ) PrimRoots R ) ) $.
    aks6d1c2.17 $e |- H = ( h e. ( NN0 ^m ( 0 ... A ) ) |->
     ( ( ( eval1 ` K ) ` ( G ` h ) ) ` M ) ) $.
    aks6d1c2.18 $e |- B = ( |_ ` ( sqrt `
     ( # ` ( L " ( E " ( NN0 X. NN0 ) ) ) ) ) ) $.
    aks6d1c2.19 $e |- C = ( E " ( ( 0 ... B ) X. ( 0 ... B ) ) ) $.
    aks6d1c2.20 $e |- ( ph -> I e. C ) $.
    aks6d1c2.21 $e |- ( ph -> J e. C ) $.
    aks6d1c2.22 $e |- ( ph -> I < J ) $.
    aks6d1c2.23 $e |- .^ = ( .g ` ( mulGrp ` ( Poly1 ` K ) ) ) $.
    aks6d1c2.24 $e |- X = ( var1 ` K ) $.
    aks6d1c2.25 $e |- S = ( ( J .^ X ) ( -g ` ( Poly1 ` K ) ) ( I .^ X ) ) $.
    aks6d1c2.26 $e |- ( ph -> U e. NN ) $.
    aks6d1c2.27 $e |- ( ph -> J = ( I + ( U x. R ) ) ) $.
    ${
      $d .~ a $.  $d A a $.  $d A g i $.  $d A x $.  $d G e f y $.  $d K a $.
      $d K e f y $.  $d K g i $.  $d K v $.  $d K x $.  $d M v $.  $d M y $.
      $d N a $.  $d N e f y $.  $d N k l $.  $d N x $.  $d P e f y $.
      $d P k l $.  $d P x $.  $d R e f y $.  $d R v $.  $d R x $.  $d a ph $.
      $d e f o y $.  $d e f p y $.  $d e f q y $.  $d e f r y $.  $d e f s y $.
      $d g i ph $.  $d g i s $.  $d k l o $.  $d k l p $.  $d k l ph $.
      $d k l q $.  $d k l r $.  $d ph v $.  $d ph x $.
      aks6d1c2p3.1 $e |- ( ph -> s e. ( NN0 ^m ( 0 ... A ) ) ) $.
      aks6d1c2p3.2 $e |- ( ph -> r e. ( 0 ... B ) ) $.
      aks6d1c2p3.3 $e |- ( ph -> o e. ( 0 ... B ) ) $.
      aks6d1c2p3.4 $e |- ( ph -> J = ( r E o ) ) $.
      aks6d1c2p3.5 $e |- ( ph -> p e. ( 0 ... B ) ) $.
      aks6d1c2p3.6 $e |- ( ph -> q e. ( 0 ... B ) ) $.
      aks6d1c2p3.7 $e |- ( ph -> I = ( p E q ) ) $.
      aks6d1c2p3.8 $e |- ( ph -> I e. NN0 ) $.
      $( Lemma for ~ aks6d1c2 to simplify context.  (Contributed by metakunt,
         1-May-2025.) $)
      aks6d1c2lem3 $p |- ( ph -> ( J ( .g ` ( mulGrp ` K ) ) ( (
      ( eval1 ` K ) ` ( G ` s ) ) ` M ) ) = ( I ( .g ` ( mulGrp ` K ) ) ( (
        ( eval1 ` K ) ` ( G ` s ) ) ` M ) ) ) $=
        ( vv cv cfv ce1 cmgp cmg co cexp cdiv cmul cn0 cvv cmpo wceq a1i simprl
        wa oveq2d simprr oveq12d cc0 cfz wcel elfznn0 ovexd ovmpod eqtrd oveq1d
        syl oveq2 fveq2d eqeq12d wbr wral syl2anc eqid aks6d1c1rh aks6d1c1p1rcl
        mpbid cbs cn simpld aks6d1c1p1 rspcdva eqcomd w3a nnnn0d 3jca eqtr2d wf
        cprimroots fveq2 cmap wb nn0ex elmapg cpl1 simprd caddc cplusg cmnd crg
        ccrg fldcrngd crngring ringmgp nn0mulcld c0g wi ccmn crngmgp isprimroot
        cdvds biimpd mpd simp1d mulgnn0dir mulgnn0ass simp2d mulgnn0cld mndrid
        mulgnn0z ) AUEUHUKWMZUBWNZUFWOWNZWNZWNZUFWPWNZWQWNZWRGULWMZWSWRZUIGWTWR
        ZRWMZWSWRZXAWRZUVRUVTWRZUDUVRUVTWRZAUEUWFUVRUVTAUEUWAUWDSWRUWFWGAQUPUWA
        UWDXBXBGQWMZWSWRZUWCUPWMZWSWRZXAWRZUWFSXCSQUPXBXBUWMXDXEAVHXFZAUWIUWAXE
        ZUWKUWDXEZXHXHZUWJUWBUWLUWEXAUWQUWIUWAGWSAUWOUWPXGXIUWQUWKUWDUWCWSAUWOU
        WPXJXIXKAUWAXLEXMWRZXNUWAXBXNWEUWAEXOXTZAUWDUWRXNUWDXBXNWFUWDEXOXTZAUWB
        UWEXAXPXQXRZXSAUWHGUNWMZWSWRZUWCUMWMZWSWRZXAWRZUVRUVTWRZUWGAUDUXFUVRUVT
        AUDUXBUXDSWRUXFWJAQUPUXBUXDXBXBUWMUXFSXCUWNAUWIUXBXEZUWKUXDXEZXHXHZUWJU
        XCUWLUXEXAUXJUWIUXBGWSAUXHUXIXGXIUXJUWKUXDUWCWSAUXHUXIXJXIXKAUXBUWRXNUX
        BXBXNWHUXBEXOXTZAUXDUWRXNUXDXBXNWIUXDEXOXTZAUXCUXEXAXPXQXRZXSAUXGUXFUHU
        VTWRZUVQWNZUWGAUXFCWMZUVQWNZUVTWRZUXFUXPUVTWRZUVQWNZXEZUXGUXOXECUVSIUUB
        WRZUHUXPUHXEZUXRUXGUXTUXOUYCUXQUVRUXFUVTUXPUHUVQUUCZXIUYCUXSUXNUVQUXPUH
        UXFUVTYAYBYCAUXFUVOHYDUYACUYBYEABCDGHIUXBLMNPUXFUVNUBUFUXDUIUOUQURUSUTV
        AVBVCVDAUVNXBXLDXMWRZUUDWRXNZUYEXBUVNUUAZWDAXBXCXNZUYEXCXNUYFUYGUUEUYHA
        UUFXFAXLDXMXPXBUYEUVNXCXCUUGYFYJZVFVGUXKUXLUXFYGVJVKYHZACUFUUHWNYKWNZUV
        THILMUXFUVTUVOUVSUVPUQAUXFYLXNZUVOUYKXNZACUYKUVTHILMUXFUVTUVOUVSUVPUQUY
        JYIZUUIZAUYLUYMUYNYMYNYJVLYOAUXOUWFUHUVTWRZUVQWNZUWGAUXNUYPUVQAUXNUDUHU
        VTWRZUYPAUXFUDUHUVTAUDUXFUXMYPXSAUYPUEUHUVTWRZUYRAUWFUEUHUVTAUEUWFUXAYP
        XSAUYSUDKIXAWRZUUJWRZUHUVTWRZUYRAUEVUAUHUVTWCXSAVUBUYRUYTUHUVTWRZUVSUUK
        WNZWRZUYRAUVSUULXNZUDXBXNZUYTXBXNZUHUVSYKWNZXNZYQVUBVUEXEAUFUUMXNZVUFAU
        FUUNXNZVUKAUFUSUUOZUFUUPXTUFUVSUVSYGZUUQXTZAVUGVUHVUJWKAKIAKWBYRZAIVAYR
        ZUURAVUJIUHUVTWRZUVSUUSWNZXEZWLWMZUHUVTWRVUSXEIVVAUVDYDUUTWLXBYEZAUHUYB
        XNZVUJVUTVVBYQZVLAVVCVVDAUVSUVTIUHWLAVULUVSUVAXNVUMUFUVSVUNUVBXTVUQUVTY
        GZUVCUVEUVFZUVGZYSVUIVUDUVTUVSUDUYTUHVUIYGZVVEVUDYGZUVHYFAVUEUYRVUSVUDW
        RZUYRAVUCVUSUYRVUDAVUCKVURUVTWRZVUSAVUFKXBXNZIXBXNZVUJYQVUCVVKXEVUOAVVL
        VVMVUJVUPVUQVVGYSVUIUVTUVSKIUHVVHVVEUVIYFAVVKKVUSUVTWRZVUSAVURVUSKUVTAV
        UJVUTVVBVVFUVJXIAVUFVVLVVNVUSXEVUOVUPVUIUVTUVSKVUSVVHVVEVUSYGZUVMYFXRXR
        XIAVUFUYRVUIXNVVJUYRXEVUOAVUIUVTUVSUDUHVVHVVEVUOWKVVGUVKVUIVUDUVSUYRVUS
        VVHVVIVVOUVLYFXRXRXRYTXRYBAUWGUYQAUWFUXQUVTWRZUWFUXPUVTWRZUVQWNZXEZUWGU
        YQXECUYBUHUYCVVPUWGVVRUYQUYCUXQUVRUWFUVTUYDXIUYCVVQUYPUVQUXPUHUWFUVTYAY
        BYCAUWFUVOHYDVVSCUYBYEABCDGHIUWALMNPUWFUVNUBUFUWDUIUOUQURUSUTVAVBVCVDUY
        IVFVGUWSUWTUWFYGVJVKYHZACUYKUVTHILMUWFUVTUVOUVSUVPUQUYOAUWFYLXNUYMACUYK
        UVTHILMUWFUVTUVOUVSUVPUQVVTYIYMYNYJVLYOYPXRXRYTXR $.
    $}

    ${
      $d .~ a $.  $d A a o p q r s $.  $d A g i o p q r s $.  $d A h s $.
      $d A k l o p q r s $.  $d A o p q r s x $.  $d B a o p q r $.
      $d B g i o p q r $.  $d B k l o p q r $.  $d B o p q r x $.
      $d E a o p q r $.  $d E g i o p q r $.  $d E k l o p q r $.
      $d E o p q r x $.  $d G e f o p q r y $.  $d G h $.  $d H s $.
      $d I a o p q r $.  $d I g i o p q r $.  $d I k l o p q r $.
      $d I o p q r x $.  $d J a o p q r $.  $d J g i o p q r $.
      $d J k l o p q r $.  $d J o p q r x $.  $d K a o p q r s $.
      $d K e f o p q r s y $.  $d K g i o p q r s $.  $d K h s $.  $d K v $.
      $d K o p q r s x $.  $d M h $.  $d M o p q r y $.  $d M v $.
      $d N a o r $.  $d N e f o r y $.  $d N k l o r $.  $d N o r x $.
      $d P e f y $.  $d P k l $.  $d P x $.  $d R e f y $.  $d R v $.
      $d R x $.  $d S s $.  $d a o p ph q r s $.  $d g i o p ph q r s $.
      $d h ph s $.  $d k l o p ph q r s $.  $d ph v $.  $d ph q r s x $.
      $( Claim 2 of Theorem 6.1 AKS, Preparation for injectivity proof.
         (Contributed by metakunt, 1-May-2025.) $)
      aks6d1c2lem4 $p |- ( ph -> ( # ` ( H " ( NN0 ^m ( 0 ... A ) ) ) ) <_
       ( N ^ B ) ) $=
        ( vs vv vr vo vp vq cn0 cc0 cfz co cima chash cfv c0g cexp wcel cvv cle
        wbr fvexd syl cv wa wceq a1i fveq2d cbs eqid adantr simpr nnnn0d mpd cn
        cmul c1 wf adantl simprd eqeltrd oveq2d wss nn0expcld cz wne wb syl3anc
        mpbid jca elnn0z sylibr wrex nn0red cr syl2anc r19.29vva ad7antr eqcomd
        eqtrd reexpcld letrd recnd eqbrtrd cmap ce1 csn cfn cnvexg imaexd fmptd
        ccnv nfv ffnd fnfund cpl1 csg fveq1d ccrg fldcrngd cmpt fvmptd cmgp cmg
        cdvds wi wral cprimroots w3a crngmgp isprimroot biimpd simp1d eleqtrrdi
        ccmn mgpbas cdiv cfield cprime cgcd elmapi 0nn0 cascl cplusg aks6d1c1rh
        cv1 czrh aks6d1c1p1rcl fveval1fvcl ply1crng cmnmndd cmpo simprl oveq12d
        crs simprr fz0ssnn0 sselda sseli ovexd prmnn nn0zd dvdsval2 nnred nnrpd
        ovmpod nnne0d nn0ge0d divge0d nn0mulcld cxp eleqtrd aks6d1c2p1 c0 csqrt
        wfn cuz cfl czn hashscontpowcl resqrtcld flcld sqrtge0d 0zd sylib eluz1
        flge ax-mp fzn0 ssxpb mpbird ovelimab crg crngringd vr1cl eqcomi eleq2i
        xpnz mulgnn0cld evl1vard evl1expd caddc ad6antr simp-6r simp-5r simp-4r
        clt simpllr simplr ad3antrrr ad2antrr aks6d1c2lem3 ad4antr 3eqtrd eqidd
        0z evl1subd cgrp crnggrpd grpsubid elsng wfun cdm grpsubcl eqeltrid crh
        cpws evl1rhm rhmf ffvelcdmda pwsbas eleqtrrd elmapd fnfun fndm fvimacnv
        ex ffn funimassd ssexd cdg1 cnzr cdr isfld biimpi simpld drngnzr deg1pw
        3brtr3d deg1sub cidom fldidom deg1nn0clb hashbnd hashcl hashss redivcld
        fta1g remulcld 0red 1red prmgt1 expge0d nnge1d elfzuz3 leexp2ad mullidd
        0le1 ltled nnzd dvdsle lemuldivd lemul12ad divcan2d oveq1d eqtr2d leidd
        mulexpd ) AUBWEWFDWGWHZUUAWHZWIZWJWKZJUEUUBWKZWKZUUHZUEWLWKZUUCZWIZWJWK
        ZUHEWMWHZAVXRAVXQUUDWNZVXRWEWNAVXQWOWNVYEWEWNZVXRVYEWPWQZVYGAVXQVYDWOAV
        YAVYCWOAVXTWOWNVYAWOWNAJVXSWRVXTWOUUEWSUUFZAVSVXPVYDUBAVSUUIAVXPUBAVXPW
        OUBAOVXPUGOWTZUAWKZVXSWKZWKZWOUBAVYKVXPWNXAUGVYMWRVHUUGUUJUUKAVSWTZVXPW
        NZXAZVYOUBWKZVXTWKZVYCWNZVYRVYDWNZVYQVYTVYSVYBXBZVYQVYSVYRUDUISWHZUCUIS
        WHZUEUULWKZUUMWKZWHZVXSWKZWKZVYBVYQVYRVXTWUHVYQJWUGVXSJWUGXBZVYQVPXCXDU
        UNVYQWUIVYRWUDVXSWKWKZWUKUEUUMWKZWHZVYBVYQWUGWUEXEWKZWNZWUIWUMXBVYQUEXE
        WKZWULWUEUEWUNWUCWUFWUDVXSWUKWUKVYRVXSXFZWUEXFZWUPXFZWUNXFZAUEUUOWNZVYP
        AUEUNUUPZXGZVYQVYRUGVYOUAWKZVXSWKZWKZWUPVYQOVYOVYNWVFVXPUBWOUBOVXPVYNUU
        QXBVYQVHXCVYQVYKVYOXBZXAZUGVYMWVEWVHVYLWVDVXSWVHVYKVYOUAVYQWVGXHXDXDUUN
        AVYPXHZVYQUGWVEWRUURZVYQWUPWUEUEWUNWVDVXSUGWUQWURWUSWUTWVCAUGWUPWNVYPAU
        GUEUUSWKZXEWKZWUPAUGWVLWNZIUGWVKUUTWKZWHWVKWLWKZXBZVTWTZUGWVNWHWVOXBIWV
        QUVAWQUVBVTWEUVCZAUGWVKIUVDWHWNZWVMWVPWVRUVEZVGAWVSWVTAWVKWVNIUGVTAWVAW
        VKUVKWNWVBUEWVKWVKXFZUVFWSAIUPXIWVNXFZUVGUVHXJUVIWUPUEWVKWWAWUSUVLUVJXG
        VYQGWFWMWHUHGUVMWHZWFWMWHXLWHZXKWNWVDWUNWNVYQCWUNWVNHILMWWDWVNWVDWVKVXS
        ULVYQBCDGHIWFLMNPWWDVYOUAUEWFUHUJULUMAUEUVNWNZVYPUNXGAGUVOWNZVYPUOXGAIX
        KWNZVYPUPXGAUHXKWNZVYPUQXGAGUHUVAWQZVYPURXGAUHIUVPWHXMXBZVYPUSXGVYPVXOW
        EVYOXNAVYOWEVXOUVQXOVAADWEWNZVYPVBXGWFWEWNVYQUVRXCZWWLWWDXFAUHUEUWBWKUJ
        WTUEUWCWKWKWUEUVSWKWKWUEUVTWKWHHWQUJXMDWGWHUVCZVYPVEXGABWUPGBWTWVNWHUUQ
        UEUEUWKWHWNZVYPVFXGUWAUWDXPUWEXQZVYQWUCWUNWNZVYRWUCVXSWKWKZWUKXBAWWPVYP
        AWUCWUEUUSWKZXEWKZWUNAWWSSWWRUDUIWWSXFZVNAWWRAWUEUUOWNZWWRUVKWNAWVAWXAW
        VBWUEUEWURUWFWSZWUEWWRWWRXFZUVFWSUWGZAUDWAWTZWBWTZRWHZXBZUDWEWNZWAWBWFE
        WGWHZWXJAWXEWXJWNZXAZWXFWXJWNZXAZWXHXAZUDWXGWEWXNWXHXHZWXNWXGWEWNWXHWXN
        WXGGWXEWMWHZWWCWXFWMWHZXLWHZWEWXNQUKWXEWXFWEWEGQWTZWMWHZWWCUKWTZWMWHZXL
        WHZWXSRWORQUKWEWEWYDUWHXBZWXNVCXCWXNWXTWXEXBZWYBWXFXBZXAXAZWYAWXQWYCWXR
        XLWYHWXTWXEGWMWXNWYFWYGUWIXRWYHWYBWXFWWCWMWXNWYFWYGUWLXRUWJWXLWXEWEWNWX
        MAWXJWEWXEWXJWEXSZAEUWMZXCZUWNXGZWXMWXFWEWNWXLWXJWEWXFWYJUWOXOZWXNWXQWX
        RXLUWPUXBZWXNWXQWXRWXNGWXEWXLGWEWNZWXMAWYOWXKAGAWWFGXKWNUOGUWQZWSZXIZXG
        XGWYLXTWXNWWCWXFWXLWWCWEWNZWXMAWYSWXKAWWCYAWNZWFWWCWPWQZXAWYSAWYTXUAAWW
        IWYTURAGYAWNZGWFYBUHYAWNWWIWYTYCAGWYRUWRAGWYQUXCZAUHAUHUQXIZUWRGUHUWSYD
        YEAUHGAUHUQUWTZAGWYQUXAZAUHXUDUXDUXEZYFWWCYGYHZXGXGWYMXTUXFXQXGXQAUDRWX
        JWXJUXGZWIZWNZWXHWBWXJYIWAWXJYIZAUDFXUJVLFXUJXBAVJXCZUXHARWEWEUXGZUXLZX
        UIXUNXSZXUKXULYCAXUNXKRAGQRUHUKUQUOURVCUXIUUJZAXUPWYIWYIXAZAWYIWYIWYKWY
        KYFAXUIUXJYBZXUPXURYCAWXJUXJYBZXUTXAXUSAXUTXUTAEWFUXMWKWNZXUTAEYAWNWFEW
        PWQXAZXVAAEWEWNZXVBAEUFRXUNWIWIWJWKZUXKWKZUXNWKZWEEXVFXBAVIXCAXVFYAWNZW
        FXVFWPWQZXAXVFWEWNAXVGXVHAXVEAXVDAXVDAGIQRUFUHIUXOWKZUKUQUOURUPUSVCVDXV
        IXFUXPZYJZAXVDXVJUXDZUXQZUXRAWFXVEWPWQZXVHAXVDXVKXVLUXSAXVEYKWNWFYAWNZX
        VNXVHYCXVMAUXTXVEWFUYCYLYEYFXVFYGYHXQZEYGUYAXVOXVAXVBYCVULWFEUYBUYDYHWF
        EUYEYHZXVQYFWXJWXJUYNUYAWXJWXJWEWEUYFWSUYGZWAWBXUNWXJWXJUDRUYHYLYEZYMZA
        UIWUNWNZUIWWSWNAUEUYIWNZXWAAUEWVBUYJZWUNWUEUEUIVOWURWUTUYKWSZWWSWUNUIWU
        NWWSWUNWUEWWRWXCWUTUVLZUYLUYMYHZUYOXWEUVJZXGVYQWWQUDVYRWVNWHZUCVYRWVNWH
        ZWUKVYQWWPWWQXWHXBVYQWUPWUEUESWUNWVNUIUDVXSVYRVYRWUQWURWUSWUTWVCWWOVYQX
        WAVYRUIVXSWKWKVYRXBZAXWAVYPXWDXGVYQXWAXWJVYQWUPWUEUEWUNVXSUIVYRWUQVOWUS
        WURWUTWVCWWOUYPXPYFZVNWWBAWXIVYPXVTXGUYQXPVYQXWHUDWVFWVNWHZUCWVFWVNWHZX
        WIVYQVYRWVFUDWVNWVJXRVYQWXHXWLXWMXBZWAWBWXJWXJVYQWXKXAZWXMXAZWXHXAZUCWC
        WTZWDWTZRWHZXBZXWNWCWDWXJWXJXWQXWRWXJWNZXAZXWSWXJWNZXAZXXAXABCDEFGHIJKL
        MNOPQWBRSTUAUBUCUDUEUFUGUHUIVSWAWDWCUJUKULUMAWWEVYPWXKWXMWXHXXBXXDXXAUN
        YNAWWFVYPWXKWXMWXHXXBXXDXXAUOYNAWWGVYPWXKWXMWXHXXBXXDXXAUPYNAWWHVYPWXKW
        XMWXHXXBXXDXXAUQYNAWWIVYPWXKWXMWXHXXBXXDXXAURYNAWWJVYPWXKWXMWXHXXBXXDXX
        AUSYNAVXOWETXNVYPWXKWXMWXHXXBXXDXXAUTYNVAAWWKVYPWXKWXMWXHXXBXXDXXAVBYNV
        CVDAWWMVYPWXKWXMWXHXXBXXDXXAVEYNAWWNVYPWXKWXMWXHXXBXXDXXAVFYNAWVSVYPWXK
        WXMWXHXXBXXDXXAVGYNVHVIVJAUCFWNVYPWXKWXMWXHXXBXXDXXAVKYNAUDFWNVYPWXKWXM
        WXHXXBXXDXXAVLYNAUCUDVUCWQVYPWXKWXMWXHXXBXXDXXAVMYNVNVOVPAKXKWNVYPWXKWX
        MWXHXXBXXDXXAVQYNAUDUCKIXLWHUYRWHXBVYPWXKWXMWXHXXBXXDXXAVRYNVYQVYPWXKWX
        MWXHXXBXXDXXAWVIUYSVYQWXKWXMWXHXXBXXDXXAUYTXWOWXMWXHXXBXXDXXAVUAXWPWXHX
        XBXXDXXAVUBXWQXXBXXDXXAVUDXXCXXDXXAVUEXXEXXAXHVYQUCWEWNZWXKWXMWXHXXBXXD
        XXAAXXFVYPAXXAXXFWCWDWXJWXJAXXBXAZXXDXAZXXAXAZUCGXWRWMWHZWWCXWSWMWHZXLW
        HZWEXXIUCXWTXXLXXHXXAXHXXIQUKXWRXWSWEWEWYDXXLRWOWYEXXIVCXCXXIWXTXWRXBZW
        YBXWSXBZXAXAZWYAXXJWYCXXKXLXXOWXTXWRGWMXXIXXMXXNUWIXRXXOWYBXWSWWCWMXXIX
        XMXXNUWLXRUWJXXHXWRWEWNZXXAXXGXXPXXDAWXJWEXWRWYKUWNXGXGZXXHXWSWEWNZXXAX
        XDXXRXXGWXJWEXWSWYJUWOXOXGZXXIXXJXXKXLUWPUXBYPXXIXXJXXKXXIGXWRAWYOXXBXX
        DXXAWYRVUFXXQXTXXIWWCXWSXXHWYSXXAAWYSXXBXXDXUHVUGXGXXSXTUXFXQAUCXUJWNZX
        XAWDWXJYIWCWXJYIZAUCFXUJVKXUMUXHAXUOXUPXXTXYAYCXUQXVRWCWDXUNWXJWXJUCRUY
        HYLYEZYMZXGZUYSVUHAXYAVYPWXKWXMWXHXYBVUIYMAXULVYPXVSXGYMVYQWVFVYRUCWVNV
        YQVYRWVFWVJYOXRVUJVYQWUKXWIVYQWUDWUNWNZWUKXWIXBVYQWUPWUEUESWUNWVNUIUCVX
        SVYRVYRWUQWURWUSWUTWVCWWOXWKVNWWBXYDUYQXPYOVUJYFVYQXYEWUKWUKXBAXYEVYPAW
        UDWWSWNXYEAWWSSWWRUCUIWWTVNWXDXYCXWFUYOWUNWWSWUDXWEUYMYHZXGZVYQWUKVUKYF
        WUFXFZWULXFZVUMXPVYQUEVUNWNWUKWUPWNWUMVYBXBVYQUEWVCVUOVYQWUPWUEUEWUNWUD
        VXSVYRWUQWURWUSWUTWVCWWOXYGUWEWUPUEWULWUKVYBWUSVYBXFZXYIVUPYLYPYPVYQVYS
        WOWNVYTWUBYCVYQVYRVXTWRVYSVYBWOVUQWSUYGVYQVXTVURZVYRVXTVUSZWNVYTWUAYCVY
        QVXTWUPUXLZXYKAXYMVYPAWUPWUPVXTXNZXYMAVXTWUPWUPUUAWHZWNXYNAVXTUEWUPVVCW
        HZXEWKZXYOAJWUNWNZVXTXYQWNZAJWUGWUNVPAWUEVUNWNWWPXYEWUOAWUEWXBVUOXWGXYF
        WUNWUEWUFWUCWUDWUTXYHVUTYDVVAZAXYRXYSAWUNXYQJVXSAVXSWUEXYPVVBWHWNZWUNXY
        QVXSXNAWVAYUAWVBWUPWUEUEXYPVXSWUQWURXYPXFZWUSVVDWSWUNXYQWUEXYPVXSWUTXYQ
        XFVVEWSVVFVVMXJAWWEWUPWOWNXYOXYQXBUNAUEXEWRZWUPUEWUPUVNWOXYPYUBWUSVVGYL
        VVHAWUPWUPVXTWOWOYUCYUCVVIYEWUPWUPVXTVVNWSZXGWUPVXTVVJWSVYQVYRWUPXYLWWO
        AXYLWUPXBZVYPAXYMYUEYUDWUPVXTVVKWSXGVVHVYRVYCVXTVVLYLYEVVOZVVPAVYDUUDWN
        ZVYHAVYDWOWNZJUEVVQWKZWKZWEWNZVYEYUJWPWQYUGVYJAYUJUDWEAYUJWUCYUIWKZUDAY
        UJWUGYUIWKZYULAJWUGYUIWUJAVPXCXDZAWUNYUIUEWUCWUDWUFWUEWURYUIXFZXWCWUTXY
        HXWGXYFAUCUDWUDYUIWKZYULVUCVMAYUPUCAUEVVRWNZXXFYUPUCXBAWWEYUQUNWWEUEVVS
        WNZYUQWWEYURWVAWWEYURWVAXAUEVVTVWAVWBUEVWCWSWSZXYCYUIWUEUESUCWWRUIYUOWU
        RVOWXCVNVWDYLYOAYULUDAYUQWXIYULUDXBYUSXVTYUIWUEUESUDWWRUIYUOWURVOWXCVNV
        WDYLZYOVWEVWFZYPYUTYPXVTXQZAWUNYUIWUEUEJVXSVYBWUEWLWKZWURWUTYUOWUQXYJYV
        CXFZAWWEUEVWGWNUNUEVWHWSXYTAJYVCYBZYUKYVBAXWBXYRYVEYUKYCXWCXYTWUNYUIWUE
        UEJYVCYUOWURYVDWUTVWIYLUYGVWNZVYDYUJWOVWJYDVYDVWKWSZAYUHVXQVYDXSVYIVYJY
        UFVYDVXQWOVWLYLZVXQVYEWOVWJYDVXQVWKWSYJAVYEYVGYJZAVYFAUHEXUDXVPXTYJZYVH
        AVYEYUJVYFYVIAYUJYUMYKYUNAYUMYULYKYVAAYULUDYKYUTAUDXVTYJXQXQXQYVJYVFAYU
        JYUMVYFWPYUNAYUMYULVYFWPYVAAYULUDVYFWPYUTAWXHUDVYFWPWQWAWBWXJWXJWXOUDWX
        GVYFWPWXPWXNWXGVYFWPWQWXHWXNWXGWXSVYFWPWYNWXNWXSGEWMWHZWWCEWMWHZXLWHZVY
        FWXNWXQWXRWXNGWXEWXLGYKWNZWXMAYVNWXKAWWFYVNUOWWFGWYPUWTWSZXGXGZWYLYQZWX
        NWWCWXFWXLWWCYKWNZWXMAYVRWXKAUHGXUEYVOXUCVWMZXGXGZWYMYQZVWOWXLYVMYKWNWX
        MWXLYVKYVLAYVKYKWNZWXKAGEYVOXVPYQXGZAYVLYKWNZWXKAWWCEYVSXVPYQXGZVWOXGWX
        LVYFYKWNZWXMAYWFWXKAUHEXUEXVPYQXGXGZWXNWXQYVKWXRYVLYVQWXLYWBWXMYWCXGYWA
        WXLYWDWXMYWEXGWXNGWXEYVPWYLWXLWFGWPWQZWXMAYWHWXKAWFXMGAVWPAVWQZYVOWFXMW
        PWQAVXDXCAXMGYWIYVOAWWFXMGVUCWQUOGVWRWSVXEYRXGXGVWSWXNWWCWXFYVTWYMWXLXU
        AWXMAXUAWXKXUGXGXGVWSWXNGWXEEYVPWXLXMGWPWQZWXMAYWJWXKAGWYQVWTXGXGWXLEWX
        EUXMWKWNZWXMWXKYWKAWXEWFEVXAXOXGVXBWXNWWCWXFEYVTWXLXMWWCWPWQZWXMAYWLWXK
        AXMGXLWHZUHWPWQYWLAYWMGUHWPAGAGYVOYSZVXCAWWIGUHWPWQZURAXUBWWHWWIYWOUVBA
        GWYQVXFUQGUHVXGYLXJYTAXMUHGYWIXUEXUFVXHYEXGXGWXMEWXFUXMWKWNWXLWXFWFEVXA
        XOVXBVXIWXNYVMVYFVYFWPWXNVYFGWWCXLWHZEWMWHYVMWXNUHYWPEWMWXLUHYWPXBZWXMA
        YWQWXKAYWPUHAUHGAUHXUEYSYWNXUCVXJYOXGXGVXKWXNGWWCEWXNGYVPYSWXNWWCYVTYSA
        XVCWXKWXMXVPVUGVXNVXLWXNVYFYWGVXMYTYRYTXGYTXVSYMYTYTYTYRYR $.
    $}
  $}

  ${
    $d A f $.  $d A x y $.  $d B f $.  $d F f $.  $d F x y $.
    hashnexinj.1 $e |- ( ph -> A e. Fin ) $.
    hashnexinj.2 $e |- ( ph -> B e. Fin ) $.
    hashnexinj.3 $e |- ( ph -> ( # ` B ) < ( # ` A ) ) $.
    hashnexinj.4 $e |- ( ph -> F : A --> B ) $.
    $( If the number of elements of the domain are greater than the number of
       elements in a codomain, then there are two different values that map to
       the same.  (Contributed by metakunt, 2-May-2025.) $)
    hashnexinj $p |- ( ph -> E. x e. A E. y e. A
     ( ( F ` x ) = ( F ` y ) /\ x =/= y ) ) $=
      ( vf cfv wa wn cfn wcel syl notbid mpd wral cv wceq wne wrex wf1 wal cdom
      wf wex wbr chash cle clt cn0 hashcl nn0red ltnled mpbid wb hashdom biimpd
      syl2anc wi brdomg alnex sylibr cmap elmapdd f1eq1 spcgv dff13 iman anbi2i
      co df-ne xchbinxr 2ralbii ralnex2 bitri a1i mpnanrd notnotrd ) ABUAZFLCUA
      ZFLUBZWCWDUCZMZCDUDBDUDZADEFUHZWHNZJADEFUEZNZWIWJMZNZADEKUAZUEZNZKUFZWLAW
      PKUIZNZWRADEUGUJZNZWTADUKLZEUKLZULUJZNZXBAXDXCUMUJXFIAXDXCAXDAEOPZXDUNPHE
      UOQUPAXCADOPZXCUNPGDUOQUPUQURAXFXBAXEXAAXHXGXEXAUSGHDEOUTVBRVASAXGXBWTVCH
      XGXBWTXGXAWSDEOKVDRVAQSWPKVEVFAFEDVGVNZPWRWLVCAEDFOOHGJVHWQWLKFXIWOFUBWPW
      KDEWOFVIRVJQSAWLWNAWKWMWKWMUSAWKWIWEWCWDUBZVCZCDTBDTZMWMBCDEFVKXLWJWIXLWG
      NZCDTBDTWJXKXMBCDDXKWEXJNZMWGWEXJVLWFXNWEWCWDVOVMVPVQWGBCDDVRVSVMVSVTRVAS
      WAWB $.
  $}

  ${
    $d A w x y z $.  $d F w x y z $.  $d ph x y $.
    hashnexinjle.1 $e |- ( ph -> A e. Fin ) $.
    hashnexinjle.2 $e |- ( ph -> B e. Fin ) $.
    hashnexinjle.3 $e |- ( ph -> ( # ` B ) < ( # ` A ) ) $.
    hashnexinjle.4 $e |- ( ph -> F : A --> B ) $.
    hashnexinjle.5 $e |- ( ph -> A C_ RR ) $.
    $( If the number of elements of the domain are greater than the number of
       elements in a codomain, then there are two different values that map to
       the same.  Also we introduce a one sided inequality to simplify a
       duplicateable proof.  (Contributed by metakunt, 2-May-2025.) $)
    hashnexinjle $p |- ( ph -> E. x e. A E. y e. A
     ( ( F ` x ) = ( F ` y ) /\ x < y ) ) $=
      ( vw vz cv cfv wceq clt wbr wa wrex simpr fveq2 anbi12d fveqeq2 cbvrex2vw
      eqeq2d breq2 breq1 bilani sylib rexcom wne wo hashnexinj wcel simplrl jca
      orcd eqcomd olcd simprr cr simpl simprl sselda syl lttri2d mpbid mpjaodan
      adantr ex reximdvva imp r19.43 rexbii mpd ) ABNZFOZCNZFOZPZVQVSQRZSZCDTZB
      DTZWEVTVRPZVSVQQRZSZCDTZBDTZAWEUAAWJSZWCBDTCDTZWEWKLNZFOZMNZFOZPZWMWOQRZS
      ZLDTMDTZWLWJWTAWHWSVTWPPZVSWOQRZSBCMLDDVQWOPZWFXAWGXBXCVRWPVTVQWOFUBUFVQW
      OVSQUGUCVSWMPXAWQXBWRVSWMWPFUDVSWMWOQUHUCUEUIWSWCWNVTPZWMVSQRZSMLCBDDWOVS
      PZWQXDWRXEXFWPVTWNWOVSFUBUFWOVSWMQUGUCWMVQPXDWAXEWBWMVQVTFUDWMVQVSQUHUCUE
      UJWCCBDDUKUJAWAVQVSULZSZCDTBDTZWEWJUMZABCDEFGHIJUNAXIXJAXISZWDWIUMZBDTZXJ
      XKWCWHUMZCDTZBDTZXMAXIXPAXHXNBCDDAVQDUOZVSDUOZSZSZXHXNXTXHSZWBXNWGYAWBSZW
      CWHYBWAWBXTWAXGWBUPYAWBUAUQURYAWGSZWHWCYCWFWGYCVRVTXTWAXGWGUPUSYAWGUAUQUT
      YAXGWBWGUMXTWAXGVAYAVQVSXTVQVBUOZXHXTAXQSYDXTAXQAXSVCZAXQXRVDUQADVBVQKVEV
      FVJXTVSVBUOZXHXTAXRSYFXTAXRYEAXQXRVAUQADVBVSKVEVFVJVGVHVIVKVLVMXOXLBDWCWH
      CDVNVOUJWDWIBDVNUJVKVPVI $.
  $}

  ${
    $d .~ a $.  $d A a b c d $.  $d A b c d g i $.  $d A b c d h $.
    $d A b c d j $.  $d A b c d k l $.  $d A b c d x $.  $d B a b c d $.
    $d B b c d g i $.  $d B b c d k l $.  $d B u w $.  $d B b c d x $.
    $d C a b c d $.  $d C b c d g i $.  $d C b c d h $.  $d C b c d j $.
    $d C b c d k l $.  $d C b c s t $.  $d C b c d x $.  $d E a $.  $d E g i $.
    $d E k l $.  $d E o $.  $d E t $.  $d E u w $.  $d E x $.  $d G e f y $.
    $d G h $.  $d H b c d $.  $d K a $.  $d K e f y $.  $d K g i $.  $d K h $.
    $d K x $.  $d L b c d t $.  $d L b c s t $.  $d M h $.  $d M y $.
    $d N a b c d $.  $d N e f y $.  $d N b c d k l $.  $d N b c d x $.
    $d P e f y $.  $d P k l $.  $d P x $.  $d R a d $.  $d R e f y $.
    $d R d g i $.  $d R d h $.  $d R d j $.  $d R d k l $.  $d R d x $.
    $d a b c d ph $.  $d g i ph $.  $d h ph $.  $d j ph $.  $d k l ph $.
    $d o ph $.  $d ph s t $.  $d ph w $.  $d ph x $.
    aks6d1c2a.1 $e |- .~ = { <. e , f >. | ( e e. NN /\ f e.
     ( Base ` ( Poly1 ` K ) ) /\ A. y e. ( ( mulGrp ` K ) PrimRoots R )
     ( e ( .g ` ( mulGrp ` K ) ) ( ( ( eval1 ` K ) ` f ) ` y ) ) =
     ( ( ( eval1 ` K ) ` f ) ` ( e ( .g ` ( mulGrp ` K ) ) y ) ) ) } $.
    aks6d1c2a.2 $e |- P = ( chr ` K ) $.
    aks6d1c2a.3 $e |- ( ph -> K e. Field ) $.
    aks6d1c2a.4 $e |- ( ph -> P e. Prime ) $.
    aks6d1c2a.5 $e |- ( ph -> R e. NN ) $.
    aks6d1c2a.6 $e |- ( ph -> N e. NN ) $.
    aks6d1c2a.7 $e |- ( ph -> P || N ) $.
    aks6d1c2a.8 $e |- ( ph -> ( N gcd R ) = 1 ) $.
    aks6d1c2a.10 $e |- G = ( g e. ( NN0 ^m ( 0 ... A ) ) |->
    ( ( mulGrp ` ( Poly1 ` K ) ) gsum ( i e. ( 0 ... A ) |-> ( ( g ` i )
    ( .g ` ( mulGrp ` ( Poly1 ` K ) ) ) ( ( var1 ` K ) ( +g ` ( Poly1 ` K ) )
    ( ( algSc ` ( Poly1 ` K ) ) ` ( ( ZRHom ` K ) ` i ) ) ) ) ) ) ) $.
    aks6d1c2a.11 $e |- ( ph -> A e. NN0 ) $.
    aks6d1c2a.12 $e |- E = ( k e. NN0 , l e. NN0 |->
    ( ( P ^ k ) x. ( ( N / P ) ^ l ) ) ) $.
    aks6d1c2a.13 $e |- L = ( ZRHom ` ( Z/nZ ` R ) ) $.
    aks6d1c2a.14 $e |- ( ph -> A. a e. ( 1 ... A ) N .~ ( ( var1 ` K )
     ( +g ` ( Poly1 ` K ) )
     ( ( algSc ` ( Poly1 ` K ) ) ` ( ( ZRHom ` K ) ` a ) ) ) ) $.
    aks6d1c2a.15 $e |- ( ph -> ( x e. ( Base ` K ) |->
     ( P ( .g ` ( mulGrp ` K ) ) x ) ) e. ( K RingIso K ) ) $.
    aks6d1c2a.16 $e |- ( ph -> M e. ( ( mulGrp ` K ) PrimRoots R ) ) $.
    aks6d1c2a.17 $e |- H = ( h e. ( NN0 ^m ( 0 ... A ) ) |->
     ( ( ( eval1 ` K ) ` ( G ` h ) ) ` M ) ) $.
    aks6d1c2a.18 $e |- B = ( |_ ` ( sqrt `
     ( # ` ( L " ( E " ( NN0 X. NN0 ) ) ) ) ) ) $.
    aks6d1c2a.19 $e |- C = ( E " ( ( 0 ... B ) X. ( 0 ... B ) ) ) $.
    aks6d1c2a.20 $e |- ( ph -> ( Q e. Prime /\ Q || N /\ P =/= Q ) ) $.
    $( Claim 2 of Theorem 6.1 of ~ https://www3.nd.edu/%7eandyp/notes/AKS.pdf
       (Contributed by metakunt, 2-May-2025.) $)
    aks6d1c2 $p |- ( ph -> ( # ` ( H " ( NN0 ^m ( 0 ... A ) ) ) ) <_
       ( N ^ B ) ) $=
      ( vb vc vd vj vt vs vo vu vw cv clt wbr cmul co caddc wceq cn wrex wa cn0
      cc0 cfz cima chash cfv cle wcel simprl jca simprr cmgp cmg ad5antr cprime
      cmpt cdvds c1 a1i eqid fmptd cbs simpllr simplr simpr imp syl cz cvv nfcv
      fveq2d fvexd fvmptd eqcomd eqtrd wb adantr wss cxp nn0red nn0ge0d syl2anc
      wne cr mpbid sylibr mpbird wf1 wf sstrd sseq1d ad2antrr syl3anc recnd cfn
      breqtrrd crn cmap cexp simpl cpl1 cfield cgcd 0nn0 czrh cascl cplusg wral
      cv1 csg crs cprimroots simp-5r simp-4r aks6d1c2lem4 rexlimdva cmin cbvmpt
      ex fveq2 nnnn0d fz0ssnn0 cuz csqrt cfl czn hashscontpowcl resqrtcld flcld
      c0 sqrtge0d 0zd flge elnn0z eleq1d nn0zd eluz fzn0 xpnz biimpi imass2 nfv
      simp1d simp2d simp3d aks6d1c2p2 f1f ffnd fnfund ffvelcdmda funimassd nnzd
      ssxpb sseldd zndvds zsubcld divides biimpd mpd nnred resubcld nnrpd rpred
      cdiv posdifd rpgt0d divgt0d zred mulcomd gt0ne0d divmuld breqtrd elnnz cc
      crp eqeltrd subaddd reximssdv wfun fzfid xpfi imafi czring crh crg zncrng
      ccrg crngring zrhrhm imaexd hashclb hashcl sqrtmsq readdcld flltp1 oveq1d
      sqrtmul 1red ltmul12ad eqbrtrd hashfz0 hashxp wf1o wex ovexd xpexg mptexd
      oveq12d wfn sselda fnfvimad feqresmpt feq1d f1resf1 eqidd f1eq123d df-ima
      cres rneqd eqtr2d dff1o5 f1oeq1 spcedv hasheqf1oi zringbas rhmf resss frn
      wi rnss nnssz sseld fnfvima nnssre hashnexinjle reximddv2 r19.29vva ) AVE
      VNZVFVNZVOVPZVWBVWAVGVNZJVQVRZVSVRZVTZVGWAWBZWCZSWDWEDWFVRZUUAVRWGWHWIUCE
      UUBVRWJVPZVEVFFFAVWAFWKZWCZVWBFWKZWCZVWIWCZVWOVWCWCZVWHWCVWKVWPVWQVWHVWPV
      WOVWCVWOVWIUUCVWOVWCVWHWLWMVWOVWCVWHWNWMVWQVWHVWKVWQVWGVWKVGWAVWQVWDWAWKZ
      WCZVWGVWKVWSVWGWCZBCDEFGIJVWBTUULWIZTUUDWIZWOWIWPWIZVRVWAVXAVXCVRVXBUUMWI
      VRZVWDKLMNOPQVXCVHVWJWEWSZRSVWAVWBTUAUBUCVXAUDUEUFUGATUUEWKVWLVWNVWCVWRVW
      GUHWQAGWRWKVWLVWNVWCVWRVWGUIWQAJWAWKVWLVWNVWCVWRVWGUJWQAUCWAWKVWLVWNVWCVW
      RVWGUKWQAGUCWTVPVWLVWNVWCVWRVWGULWQAUCJUUFVRXAVTVWLVWNVWCVWRVWGUMWQVWTVHV
      WJWEWDVXEWEWDWKVWTVHVNVWJWKWCUUGXBVXEXCXDUNADWDWKVWLVWNVWCVWRVWGUOWQUPUQA
      UCVXAUDVNTUUHWIWIVXBUUIWIWIVXBUUJWIVRIVPUDXADWFVRUUKVWLVWNVWCVWRVWGURWQAB
      TXEWIGBVNTWOWIZWPWIVRWSTTUUNVRWKVWLVWNVWCVWRVWGUSWQAUBVXFJUUOVRWKVWLVWNVW
      CVWRVWGUTWQVAVBVCAVWLVWNVWCVWRVWGUUPVWMVWNVWCVWRVWGUUQVWOVWCVWRVWGXFVXCXC
      VXAXCVXDXCVWQVWRVWGXGVWSVWGXHUURUVBUUSXIXJAVWAVIFVIVNZUAWIZWSZWIZVWBVXIWI
      ZVTZVWCWCZVWIVEVFFFVWOVXMWCZVWCVWHVWOVXLVWCWNZVXNVWEVWBVWAUUTVRZVTZVWGVGW
      AXKVXNJVXPWTVPZVXQVGXKWBZVXNVWBUAWIZVWAUAWIZVTZVXRVXNVYAVXTVXNVYAVXJVXTVX
      NVXJVYAVXNVJVWAVJVNZUAWIZVYAFVXIXLVXIVJFVYDWSVTVXNVIVJFVXHVYDVJVXHXMVIVYD
      XMVXGVYCUAUVCUVAXBZVXNVYCVWAVTZWCVYCVWAUAVXNVYFXHXNAVWLVWNVXMXFVXNVWAUAXO
      XPXQVXNVXJVXKVXTVWOVXLVWCWLVXNVJVWBVYDVXTFVXIXLVYEVXNVYCVWBVTZWCVYCVWBUAV
      XNVYGXHXNVWMVWNVXMXGVXNVWBUAXOXPXRXRXQVXNJWDWKZVWBXKWKZVWAXKWKZVYBVXRXSVW
      OVYHVXMVWMVYHVWNAVYHVWLAJUJUVDZXTXTXTZVWOVYIVXMVWOVWBVWOFWAVWBAFWAYAZVWLV
      WNAVYMQWEEWFVRZVYNYBZWGZWAYAAVYPQWDWDYBZWGZWAAVYOVYQYAZVYPVYRYAZAVYSVYNWD
      YAZWUAWCZAWUAWUAWUAAEUVEXBZWUCWMAVYOUVMYFZVYSWUBXSAVYNUVMYFZWUEWCZWUDAWUE
      WUEAEWEUVFWIWKZWUEAWUGWEEWJVPZAEAEWDWKZUAVYRWGZWHWIZUVGWIZUVHWIZWDWKZAWUM
      XKWKZWEWUMWJVPZWCZWUNAWUOWUPAWULAWUKAWUKAGJPQUAUCJUVIWIZUEUKUIULUJUMUPUQW
      URXCZUVJZYCZAWUKWUTYDZUVKZUVLAWEWULWJVPZWUPAWUKWVAWVBUVNAWULYGWKZWEXKWKZW
      VDWUPXSZWVCAUVOZWULWEUVPZYEYHWMWUMUVQZYIAEWUMWDEWUMVTAVBXBZUVRZYJZYDAWVFE
      XKWKWUGWUHXSWVHAEWVMUVSWEEUVTYEYJWEEUWAYIZWVNWMWUFWUDVYNVYNUWBUWCXJVYNVYN
      WDWDUWPXJYJZVYOVYQQUWDXJZAVKVYQWAQAVKUWEAVYQQAVYQWAQAVYQWAQYKZVYQWAQYLZAG
      HPQUCUEUKUIULUPAHWRWKZHUCWTVPZGHYFZVDUWFAWVSWVTWWAVDUWGAWVSWVTWWAVDUWHUWI
      ZVYQWAQUWJXJZUWKZUWLZAVYQWAVKVNQWWCUWMUWNYMAFVYPWAFVYPVTAVCXBZYNYJZYOZVWM
      VWNXHUWQZUWOXTZVWOVYJVXMVWOVWAVWOFWAVWAWWHAVWLVWNXGUWQZUWOXTZVWBVWAUAJWUR
      WUSUQUWRYPYHVXNVXRVXSVXNJXKWKVXPXKWKVXRVXSXSVXNJVYLUVSVXNVWBVWAWWJWWLUWSV
      GJVXPUWTYEUXAUXBVXNVWDXKWKZVXQWCZWCZWWMWEVWDVOVPZWCVWRWWOWWMWWPVXNWWMVXQW
      LZWWOWEVXPJUXGVRZVWDVOWWOVXPJWWOVWBVWAWWOVWBVWOVWBWAWKVXMWWNWWIYOUXCZWWOV
      WAVWOVWAWAWKVXMWWNWWKYOUXCZUXDZWWOJVXNJUXRWKZWWNVWOWXBVXMVWMWXBVWNAWXBVWL
      AJUJUXEXTXTXTXTZUXFZWWOVWCWEVXPVOVPVXNVWCWWNVXOXTWWOVWAVWBWWTWWSUXHYHWWOJ
      WXCUXIZUXJWWOWWRVWDVTJVWDVQVRZVXPVTWWOWXFVWEVXPWWOJVWDWWOJWXDYQZWWOVWDWWO
      VWDWWQUXKYQZUXLVXNWWMVXQWNZXRWWOVXPJVWDWWOVXPWXAYQZWXGWXHWWOJWXEUXMUXNYJU
      XOWMVWDUXPYIWWOVWFVWBWWOVXPVWEVTVWFVWBVTWWOVWEVXPWXIXQWWOVWBVWAVWEWWOVWBW
      WSYQWWOVWAWWTYQWWOVWEVXPUXQWXIWXJUXSUXTYHXQUYAWMAVEVFFWUJVXIAFYRWKVYPYRWK
      ZAQUYBVYOYRWKZWXKWWEAVYNYRWKZWXMWXLAWEEUYCZWXNVYNVYNUYDYEQVYOUYEYEAFVYPYR
      WWFUVRYJAWUJYRWKZWUKWDWKZWUTAWUJXLWKWXOWXPXSAUAVYRUYFWURUYGVRZAWURUYHWKZU
      AWXQWKZAWURUYJWKZWXRAVYHWXTVYKJWURWUSUYIXJWURUYKXJWURUAUQUYLXJZUYMWUJXLUY
      NXJYJZAWUKVYPWHWIZFWHWIVOAWUKVYOWHWIZWYCVOAWUKVYNWHWIZWYEVQVRZWYDVOAWUKEX
      AVSVRZWYGVQVRZWYFVOAWUKWUKWUKVQVRUVGWIZWYHVOAWYIWUKAWUKYGWKZWEWUKWJVPZWYI
      WUKVTAWUKAWXOWXPWYBWUJUYOXJZYCZAWUKWYLYDZWUKUYPYEXQAWYIWULWULVQVRZWYHVOAW
      YJWYKWCZWYPWYIWYOVTAWYJWYKWYMWYNWMZWYQWUKWUKUYTYEAWULWYGWULWYGAWUKWYMWYNU
      VKZAEXAAEAWUIWUNAWUQWUNAWUOWUPAWULWYRUVLAWVDWUPAWUKWYMWYNUVNZAWVEWVFWVGWY
      RWVHWVIYEYHWMWVJYIWVLYJZYCAVUAUYQZWYRXUAWYSAWULWUMXAVSVRZWYGVOAWVEWULXUBV
      OVPWYRWULUYRXJAEWUMXAVSWVKUYSYSZWYSXUCVUBVUCVUCAWYEWYGWYEWYGVQAWUIWYEWYGV
      TWYTEVUDXJZXUDVUKYSAWXMWXMWCWYDWYFVTAWXMWXMWXNWXNWMVYNVYNVUEXJYSAVYOVYPVL
      VNZVUFZVLVUGZWYDWYCVTZAXUFVYOVYPVMVYOVMVNZQWIZWSZVUFZVLXLXUKAVMVYOXUJXLAV
      YNXLWKZXUMWCVYOXLWKZAXUMXUMAWEEWFVUHZXUOWMVYNVYNXLXLVUIXJZVUJAVYOVYPXUKYK
      ZXUKYTZVYPVTZWCXULAXUQXUSAVYOVYPQVYOVVAZYKZXUQAWVQVYSVYOVYPXUTYLZXVAWWBWV
      OAXVBVYOVYPXUKYLAVMVYOXUJVYPXUKAXUIVYOWKZWCVYQXUIVYOQAQVYQVULXVCWWDXTAVYO
      VYQXUIWVOVUMAXVCXHVUNXUKXCXDAVYOVYPXUTXUKAVMVYQWAVYOQWWCWVOVUOZVUPYJVYQWA
      VYOVYPQVUQYPAVYOVYOVYPVYPXUTXUKXVDAVYOVURAVYPVURVUSYHAVYPXUTYTZXURVYPXVEV
      TAQVYOVUTXBAXUTXUKXVDVVBVVCWMVYOVYPXUKVVDYIVYOVYPXUEXUKVVEVVFAXUNXUGXUHVV
      LXUPVYOVYPVLXLVVGXJUXBUXOAFVYPWHWWFXNYSAVIFVXHWUJVXIAVXGFWKZWCUAXKVULZVYR
      XKYAZVXGVYRWKZVXHWUJWKAXVGXVFAXKWURXEWIZUAAWXSXKXVJUAYLWYAXKXVJUYFWURUAVV
      HXVJXCVVIXJUWKXTAXVHXVFAVYRWAXKAVYRQYTZWAAVYRXVKYAQVYQVVAZYTZXVKYAZAXVLQY
      AZXVNXVOAQVYQVVJXBXVLQVVMXJAVYRXVMXVKVYRXVMVTAQVYQVUTXBYNYJAWVRXVKWAYAWWC
      VYQWAQVVKXJYMWAXKYAAVVNXBYMXTAXVFXVIAFVYRVXGAFVYRYAVYTWVPAFVYPVYRWWFYNYJV
      VOXIXKVYRUAVXGVVPYPVXIXCXDAFWAYGWWGWAYGYAAVVQXBYMVVRVVSVVT $.
  $}

  ${
    $d B x $.  $d D x $.
    $( Special case related to ~ rspsbc .  (Contributed by metakunt,
       5-May-2025.) $)
    rspcsbnea $p |- ( ( A e. B /\ A. x e. B C =/= D ) ->
     [_ A / x ]_ C =/= D ) $=
      ( wcel wne wral csb wsbc rspsbc wceq wn wb df-ne sbcbii a1i sbcng sbceq1g
      bitrd notbid biidd necon3bbid sylibd imp ) BCFZDEGZACHZABDIZEGZUFUHUGABJZ
      UJUGABCKUFUKUIELZMZUJUFUKDELZMZABJZUMUKUPNUFUGUOABDEOPQUFUPUNABJZMUMUNABC
      RUFUQULABDECSUATTUFULUIEUFULUBUCTUDUE $.
  $}

  ${
    $d .^ x y $.  $d A x y $.  $d N x $.  $d R x y $.  $d ph x y $.
    idomnnzpownz.1 $e |- ( ph -> R e. IDomn ) $.
    idomnnzpownz.2 $e |- ( ph -> A e. ( Base ` R ) ) $.
    idomnnzpownz.3 $e |- ( ph -> A =/= ( 0g ` R ) ) $.
    idomnnzpownz.4 $e |- ( ph -> N e. NN0 ) $.
    idomnnzpownz.5 $e |- .^ = ( .g ` ( mulGrp ` R ) ) $.
    $( A nonzero power in an integral domain is nonzero.  (Contributed by
       metakunt, 5-May-2025.) $)
    idomnnzpownz $p |- ( ph -> ( N .^ A ) =/= ( 0g ` R ) ) $=
      ( wcel wa co cfv wne wceq oveq1 neeq1d eqid adantr vx vy cn0 c0g ancli cv
      cc0 c1 caddc cur cmgp cbs mgpbas eleqtrdi mulg0 syl ringidval cidom cdomn
      eqtr4di cnzr ccrg isidom simprbi domnnzr nzrnz 4syl cplusg cmnd idomringd
      eqnetrd crg ringmgp simplr ad2antrr mulgnn0p1 syl3anc mgpplusg a1i eqcomd
      cmulr oveqd mulgnn0cl eqcomi eleqtrd simpr jca domnmuln0 nn0indd ) AAEUCK
      ZLEBDMZCUDNZOZAWJIUEAUAUFZBDMZWLOUGBDMZWLOUBUFZBDMZWLOZWQUHUIMZBDMZWLOWMU
      AUBEWNUGPWOWPWLWNUGBDQRWNWQPWOWRWLWNWQBDQRWNWTPWOXAWLWNWTBDQRWNEPWOWKWLWN
      EBDQRAWPCUJNZWLAWPCUKNZUDNZXBABXCULNZKZWPXDPABCULNZXEGXGCXCXCSZXGSZUMZUNZ
      XEDXCBXDXESZXDSJUOUPCXBXCXHXBSZUQUTACURKZCUSKZCVAKXBWLOFXNCVBKXOCVCVDZCVE
      CXBWLXMWLSZVFVGVKAWQUCKZLZWSLZXAWRBXCVHNZMZWLXTXCVIKZXRXFXAYBPXSYCWSAYCXR
      ACVLKYCACFVJCXCXHVMUPTTZAXRWSVNZAXFXRWSXKVOZXEYADXCWQBXLJYASVPVQXTYBWRBCW
      ANZMZWLXTYAYGWRBXTYGYAYGYAPXTCYGXCXHYGSZVRVSVTWBXTXOWRXGKZWSLBXGKZBWLOZLZ
      YHWLOXSXOWSAXOXRAXNXOFXPUPTTXTYJWSXTWRXEXGXTYCXRXFWRXEKYDYEYFXEDXCWQBXLJW
      CVQXEXGPXTXGXEXJWDVSWEXSWSWFWGXSYMWSAYMXRAYKYLGHWGTTXGCYGWRBWLXIYIXQWHVQV
      KVKWIUP $.
  $}

  ${
    $d A m y z $.  $d A x y z $.  $d G m y z $.  $d G x y z $.  $d N m n y z $.
    $d N n x y z $.  $d R m n y z $.  $d R n x y z $.  $d m n ph y z $.
    $d ph x y z $.
    idomnnzgmulnz.1 $e |- G = ( mulGrp ` R ) $.
    idomnnzgmulnz.2 $e |- ( ph -> R e. IDomn ) $.
    idomnnzgmulnz.3 $e |- ( ph -> N e. Fin ) $.
    idomnnzgmulnz.4 $e |- ( ( ph /\ n e. N ) -> A e. ( Base ` R ) ) $.
    idomnnzgmulnz.5 $e |- ( ( ph /\ n e. N ) -> A =/= ( 0g ` R ) ) $.
    $( A finite product of nonzero elements in an integral domain is nonzero.
       (Contributed by metakunt, 5-May-2025.) $)
    idomnnzgmulnz $p |- ( ph -> ( G gsum ( n e. N |-> A ) )
    =/= ( 0g ` R ) ) $=
      ( vm cmpt cgsu co cfv wne wceq wcel adantr vx vy vz cv c0g csn cun mpteq1
      c0 oveq2d neeq1d mpt0 a1i eqid gsum0 eqtrd cur ringidval cidom cdomn cnzr
      eqcomi ccrg isidom simprbi domnnzr nzrnz 4syl eqnetrd wss cdif csb cplusg
      wa nfcv nfcsb1v csbeq1a cbvmpt oveq2i cbs ccmn simplbi syl crngmgp simprl
      cfn ssfid wral ad2antrr simpr sseldd ralrimiva ad3antrrr rspcsbela mgpbas
      syl2anc eleqtrd eldifi adantl wn eldifn csbeq1 gsumunsn gsummptcl equcoms
      eqcomd jca rspcsbnea cmulr mgpplusg domnmuln0 syl3anc ex findcard2d ) AED
      UAUDZBMZNOZCUEPZQEDUIBMZNOZXRQEDUBUDZBMZNOZXRQZEDYAUCUDZUFUGZBMZNOZXRQZED
      FBMZNOZXRQUAUBUCFXOUIRZXQXTXRYLXPXSENDXOUIBUHUJUKXOYARZXQYCXRYMXPYBENDXOY
      ABUHUJUKXOYFRZXQYHXRYNXPYGENDXOYFBUHUJUKXOFRZXQYKXRYOXPYJENDXOFBUHUJUKAXT
      EUEPZXRAXTEUINOZYPAXSUIENXSUIRADBULUMUJYQYPRAEYPYPUNUOUMUPAYPCUQPZXRYPYRR
      AYRYPCYREGYRUNZURVBUMACUSSZCUTSZCVASYRXRQHYTCVCSZUUACVDZVEZCVFCYRXRYSXRUN
      ZVGVHVIVIAYAFVJZYEFYAVKSZVNZVNZYDYIUUIYDVNZYHELYADLUDZBVLZMZNOZDYEBVLZEVM
      PZOZXRUUJYHELYFUULMZNOZUUQYHUUSRUUJYGUURENDLYFBUULLBVOZDUUKBVPZDUUKBVQZVR
      VSUMUUJYAEVTPZUUPLEYEFUULUUOUVCUNUUPUNUUIEWASZYDAUVDUUHAUUBUVDAYTUUBHYTUU
      BUUAUUCWBWCCEGWDWCTTZUUIYAWFSYDUUIFYAAFWFSUUHITAUUFUUGWEZWGTZUUJUUKYASZVN
      ZUULCVTPZUVCUVIUUKFSBUVJSZDFWHZUULUVJSZUVIYAFUUKUUIUUFYDUVHUVFWIUUJUVHWJW
      KAUVLUUHYDUVHAUVKDFJWLZWMDUUKFBUVJWNWPZUVJUVCRZUVIUVJCEGUVJUNZWOZUMWQUUIY
      EFSZYDUUHUVSAUUGUVSUUFYEFYAWRWSWSZTZUUIYEYASWTZYDUUHUWBAUUGUWBUUFYEFYAXAW
      SWSTUUJUUOUVJUVCUUJUVSUVLUUOUVJSZUWAAUVLUUHYDUVNWIDYEFBUVJWNWPZUVPUUJUVRU
      MWQDUUKYEBXBXCUPUUJUUAUUNUVJSZUUNXRQZVNUWCUUOXRQZVNUUQXRQUUIUUAYDAUUAUUHA
      YTUUAHUUDWCTTUUJUWEUWFUUJUVJLEYAUULUVRUVEUVGUUJUVMLYAUVOWLXDUUJUUNYCXRUUJ
      UUMYBENUUMYBRUUJLDYAUULBUVAUUTUUKDUDRBUULBUULRDLUVBXEXFVRUMUJUUIYDWJVIXGU
      UJUWCUWGUWDUUIUWGYDUUIUVSBXRQZDFWHZUWGUVTAUWIUUHAUWHDFKWLTDYEFBXRXHWPTXGU
      VJCUUPUUNUUOXRUVQCXIPZUUPCUWJEGUWJUNXJVBUUEXKXLVIXMIXN $.
  $}

  ${
    $d .^ x y $.  $d N x $.  $d R x y $.  $d ph x y $.
    ringexp0nn.1 $e |- ( ph -> R e. Ring ) $.
    ringexp0nn.2 $e |- ( ph -> N e. NN ) $.
    ringexp0nn.3 $e |- .^ = ( .g ` ( mulGrp ` R ) ) $.
    $( Zero to the power of a positive integer is zero.  (Contributed by
       metakunt, 5-May-2025.) $)
    ringexp0nn $p |- ( ph -> ( N .^ ( 0g ` R ) ) = ( 0g ` R ) ) $=
      ( vx vy cn wcel wa cfv co wceq c1 oveq1 eqeq1d syl eqid c0g ancli cv cmgp
      caddc cbs cmnd crg ringmnd mndidcl mgpbas a1i eleqtrd mulg1 cplusg simplr
      ad2antrr mulgnnp1 syl2anc simpr oveq1d cmulr mgpplusg eqcomi ringrz eqtrd
      adantr nnindd ) AADJKZLDBUAMZCNZVJOZAVIFUBAHUCZVJCNZVJOPVJCNZVJOZIUCZVJCN
      ZVJOZVQPUENZVJCNZVJOVLHIDVMPOVNVOVJVMPVJCQRVMVQOVNVRVJVMVQVJCQRVMVTOVNWAV
      JVMVTVJCQRVMDOVNVKVJVMDVJCQRAVJBUDMZUFMZKZVPAVJBUFMZWCABUGKZVJWEKZABUHKZW
      FEBUISWEBVJWETZVJTZUJSZWEWCOAWEBWBWBTZWIUKULUMZWCCWBVJWCTZGUNSAVQJKZLZVSL
      ZWAVRVJWBUOMZNZVJWQWOWDWAWSOAWOVSUPAWDWOVSWMUQWCWRCWBVQVJWNGWRTURUSWQWSVJ
      VJWRNZVJWQVRVJVJWRWPVSUTVAWPWTVJOZVSAXAWOAWHWGXAEWKWEBWRVJVJWIBVBMZWRBXBW
      BWLXBTVCVDWJVEUSVGVGVFVFVHS $.

  $}

  ${
    aks6d1p5.1 $e |- ( ph -> K e. Field ) $.
    aks6d1p5.2 $e |- ( ph -> P e. Prime ) $.
    aks6d1c5.3 $e |- P = ( chr ` K ) $.
    aks6d1c5.4 $e |- ( ph -> A e. NN0 ) $.
    aks6d1c5.5 $e |- ( ph -> A < P ) $.
    aks6d1c5.6 $e |- X = ( var1 ` K ) $.
    aks6d1c5.7 $e |- .^ = ( .g ` ( mulGrp ` ( Poly1 ` K ) ) ) $.
    aks6d1c5.8 $e |- G = ( g e. ( NN0 ^m ( 0 ... A ) ) |->
    ( ( mulGrp ` ( Poly1 ` K ) ) gsum ( i e. ( 0 ... A ) |-> ( ( g ` i )
    .^ ( X ( +g ` ( Poly1 ` K ) )
    ( ( algSc ` ( Poly1 ` K ) ) ` ( ( ZRHom ` K ) ` i ) ) ) ) ) ) ) $.

    ${
      $d A g i $.  $d K g i $.  $d g i ph $.
      $( Lemma for Claim 5 of Theorem 6.1, G defines a map into the
         polynomials.  (Contributed by metakunt, 5-May-2025.) $)
      aks6d1c5lem0 $p |- ( ph -> G : ( NN0 ^m ( 0 ... A ) ) -->
     ( Base ` ( Poly1 ` K ) ) ) $=
        ( cfv wcel eqid cn0 cc0 cfz co cmap cpl1 cmgp cv czrh cascl cplusg cmpt
        cgsu cbs wa ccmn ccrg fldcrngd ply1crng syl crngmgp adantr cmnd cmnmndd
        fzfid cvv nn0ex a1i ovexd elmapd biimpd imp ffvelcdmda crngringd cmnmnd
        wf ringcmnd crg vr1cl simpl elfzelz adantl jca czring crh zringbas rhmf
        cz zrhrhm ply1sclcl syl2anc mndcl syl3anc wceq mgpbas eleqtrd ralrimiva
        mulgnn0cld gsummptcl eqcomi fmptd ) ADUAUBBUCUDZUEUDZHUFRZUGRZEXBEUHZDU
        HZRZIXFHUIRZRZXDUJRZRZXDUKRZUDZFUDZULUMUDZXDUNRZGAXGXCSZUOZXPXEUNRZXQXS
        XTEXEXBXOXTTZAXEUPSZXRAXDUQSZYBAHUQSYCAHJURZXDHXDTZUSUTZXDXEXETZVAUTVBZ
        XSUBBVEXSXOXTSEXBXSXFXBSZUOZXTFXEXHXNYAPXSXEVCSYIXSXEYHVDVBXSXBUAXFXGAX
        RXBUAXGVPZAXRYKAUAXBXGVFVFUAVFSAVGVHAUBBUCVIVJVKVLVMYJXNXQXTYJXDVCSZIXQ
        SZXLXQSZXNXQSXSYLYIAYLXRAXDUPSYLAXDAXDYFVNVQXDVOUTVBVBYJHVRSZYMXSYOYIAY
        OXRAHYDVNVBZVBZXQXDHIOYEXQTZVSUTYJYOXJHUNRZSZYNYQYJXSXFWHSZUOYTYJXSUUAX
        SYIVTYIUUAXSXFUBBWAWBWCXSWHYSXFXIXSYOWHYSXIVPZYPYOXIWDHWEUDSUUBHXIXITWI
        WHYSWDHXIWFYSTZWGUTUTVMUTXKXQXDHXJYSYEXKTUUCYRWJWKXQXMXDIXLYRXMTWLWMXQX
        TWNYJXQXDXEYGYRWOZVHWPWRWQWSXTXQWNXSXQXTUUDWTVHWPQXA $.
    $}

    ${
      aks6d1c5p1.1 $e |- ( ph -> B e. ( 0 ... A ) ) $.
      aks6d1c5p1.2 $e |- ( ph -> C e. ( 0 ... A ) ) $.
      $( Lemma for claim 5, evaluate the linear factor at -c to get a root.
         (Contributed by metakunt, 5-May-2025.) $)
      aks6d1c5lem1 $p |- ( ph -> ( B = C <-> (
       ( ( eval1 ` K ) `
        ( X ( +g ` ( Poly1 ` K ) )
    ( ( algSc ` ( Poly1 ` K ) ) ` ( ( ZRHom ` K ) ` B ) ) )
       )
       ` ( ( ZRHom ` K ) ` ( 0 - C ) ) ) = ( 0g ` K ) ) ) $=
        ( wceq cc0 cmin co czrh cfv cplusg c0g cpl1 cascl ce1 czring zringplusg
        caddc eqcomi a1i oveqd 0cnd elfzelzd zcnd subadd23d subcld eqtrd fveq2d
        addlidd eqeq1d cdvds wbr wa cz wcel cprime cn adantr prmnn syl dvds0 cc
        nnzd subidd eqcomd simpr oveq2d breqtrd ex wn clt 1zzd zsubcld ad2antrr
        c1 cfz cle 1e0p1 zred posdifd mpbid 0zd zltp1led eqbrtrd nnred subge02d
        cr elfzle1 nn0red elfzle2 lelttrd zltlem1d elfzd fzm1ndvds simpll wo wb
        syl2anc axlttri ioran bitr2d biimpd imp anassrs jca dvdsnegb negsubdi2d
        cneg breq2d bitrd mtbird pm2.61dan con4d crg ccrg fldcrngd crngring cbs
        impbid eqid zringbas eleqtrdi ffvelcdmd bicomd crh zrhrhm rhmghm ghmlin
        chrdvds cghm syl3anc wf ghmf evl1vard evl1scad evl1addd simprd ) ACDUBZ
        UCDUDUEZJUFUGZUGZCUUQUGZJUHUGZUEZJUIUGZUBZUURKUUSJUJUGZUKUGZUGZUVDUHUGZ
        UEZJULUGZUGUGZUVBUBAUUOUUPCUMUHUGZUEZUUQUGZUVBUBZUVCAUVNUUOAUVNCDUDUEZU
        UQUGZUVBUBZUUOAUVMUVPUVBAUVLUVOUUQAUVLUUPCUOUEZUVOAUVKUOUUPCUVKUOUBAUOU
        VKUNUPUQURAUVRUCUVOUOUEUVOAUCDCAUSADADUCBUAUTZVAZACACUCBTUTZVAZVBAUVOAC
        DUWBUVTVCVFVDVDVEVGAUUOEUVOVHVIZUVQAUUOUWCAUUOUWCAUUOVJZEUCUVOVHUWDEVKV
        LZEUCVHVIUWDEUWDEVMVLZEVNVLZAUWFUUOMVOEVPZVQVTEVRVQUWDUCCCUDUEZUVOUWDUW
        IUCUWDCACVSVLUUOUWBVOWAWBUWDCDCUDAUUOWCWDVDWEWFAUUOUWCAUUOWGZUWCWGZAUWJ
        VJZDCWHVIZUWKUWLUWMVJZUWGUVOWLEWLUDUEZWMUEZVLUWKUWLUWGUWMAUWGUWJAUWFUWG
        MUWHVQZVOVOZUWNUVOWLUWOUWNWIZUWNEWLUWNEUWRVTZUWSWJAUVOVKVLZUWJUWMACDUWA
        UVSWJZWKZUWNWLUCWLUOUEZUVOWNWLUXDUBZUWNWOUQUWNUCUVOWHVIZUXDUVOWNVIUWNUW
        MUXFUWLUWMWCUWNDCUWLDXDVLZUWMAUXGUWJADUVSWPZVOVOZUWLCXDVLZUWMAUXJUWJACU
        WAWPZVOVOZWQWRUWNUCUVOUWNWSUXCWTWRXAUWNUVOEWHVIUVOUWOWNVIUWNUVOCEUWNUVO
        UXCWPUXLUWNEUWRXBUWNUCDWNVIZUVOCWNVIUWLUXMUWMAUXMUWJADUCBWMUEZVLZUXMUAD
        UCBXEVQVOVOUWNCDUXLUXIXCWRUWLCEWHVIZUWMAUXPUWJACBEUXKABOXFZAEUWQXBZACUX
        NVLZCBWNVITCUCBXGVQPXHVOVOXHUWNUVOEUXCUWTXIWRXJEUVOXKXOUWLUWMWGZVJZACDW
        HVIZVJZUWKUYAAUYBAUWJUXTXLAUWJUXTUYBAUWJUXTVJZUYBAUYDUYBAUYBUUOUWMXMWGZ
        UYDAUXJUXGUYBUYEXNUXKUXHCDXPXOUYEUYDXNAUUOUWMXQUQXRXSXTYAYBUYCUWCEDCUDU
        EZVHVIZUYCUWGUYFUWPVLUYGWGAUWGUYBUWQVOUYCUYFWLUWOUYCWIZUYCEWLAUWEUYBAEU
        WQVTZVOZUYHWJUYCDCADVKVLUYBUVSVOACVKVLUYBUWAVOWJZUYCWLUXDUYFWNUXEUYCWOU
        QUYCUCUYFWHVIZUXDUYFWNVIAUYBUYLAUYBUYLACDUXKUXHWQXSXTUYCUCUYFUYCWSUYKWT
        WRXAUYCUYFEWHVIUYFUWOWNVIUYCUYFDEUYCUYFUYKWPAUXGUYBUXHVOZAEXDVLUYBUXRVO
        ZUYCUCCWNVIZUYFDWNVIUYCUXSUYOAUXSUYBTVOCUCBXEVQUYCDCUYMAUXJUYBUXKVOXCWR
        UYCDBEUYMABXDVLUYBUXQVOUYNADBWNVIZUYBAUXOUYPUADUCBXGVQVOABEWHVIUYBPVOXH
        XHUYCUYFEUYKUYJXIWRXJEUYFXKXOAUWCUYGXNUYBAUWCEUVOYEZVHVIZUYGAUWEUXAUWCU
        YRXNUYIUXBEUVOYCXOAUYQUYFEVHACDUWBUVTYDYFYGVOYHVQYIWFYJYPAJYKVLZUXAUWCU
        VQXNAJYLVLUYSAJLYMZJYNVQZUXBEJUUQUVOUVBNUUQYQZUVBYQUUFXOXRYGUUAAUVMUVAU
        VBAUUQUMJUUGUEVLZUUPUMYOUGZVLCVUDVLUVMUVAUBAUYSVUCVUAUYSUUQUMJUUBUEVLVU
        CJUUQVUBUUCUMJUUQUUDVQVQZAUUPVKVUDAUCDAWSUVSWJZYRYSACVKVUDUWAYRYSUVKUUT
        UMJUUPUUQCVUDVUDYQUVKYQUUTYQZUUEUUHVGYGAUVAUVJUVBAUVJUVAAUVHUVDYOUGZVLU
        VJUVAUBAJYOUGZUVDUUTUVGJVUHKUVFUVIUURUUSUURUVIYQZUVDYQZVUIYQZVUHYQZUYTA
        VKVUIUUPUUQAVUCVKVUIUUQUUIVUEUMJUUQVKVUIYRVULUUJVQZVUFYTZAVUIUVDJVUHUVI
        KUURVUJQVULVUKVUMUYTVUOUUKAUVEVUIUVDJVUHUVIUUSUURVUJVUKVULUVEYQVUMUYTAV
        KVUICUUQVUNUWAYTVUOUULUVGYQVUGUUMUUNWBVGYG $.
    $}

    ${
      $d .^ g i $.  $d A g i $.  $d K g i $.  $d M g i $.  $d S g i $.
      $d W i $.  $d X g i $.  $d Y g i $.  $d g i ph $.
      aks6d1c5p3.1 $e |- ( ph -> Y e. ( NN0 ^m ( 0 ... A ) ) ) $.
      aks6d1c5p3.2 $e |- ( ph -> W e. ( 0 ... A ) ) $.
      aks6d1c5p3.3 $e |- ( ph -> C e. NN0 ) $.
      aks6d1c5p3.4 $e |- ( ph -> C <_ ( Y ` W ) ) $.
      aks6d1c5p3.5 $e |- Q = ( quot1p ` K ) $.
      aks6d1c5p3.6 $e |- S = ( algSc ` ( Poly1 ` K ) ) $.
      aks6d1c5p3.7 $e |- M = ( mulGrp ` ( Poly1 ` K ) ) $.
      $( Lemma for Claim 5, polynomial division with a linear power.
         (Contributed by metakunt, 5-May-2025.) $)
      aks6d1c5lem3 $p |- ( ph -> ( ( G ` Y ) Q
      ( C .^ ( X ( +g ` ( Poly1 ` K ) )
       ( S ` ( ( ZRHom ` K ) ` W ) ) ) ) ) = ( ( ( ( Y ` W ) - C )
        .^ ( X ( +g ` ( Poly1 ` K ) ) ( S ` ( ( ZRHom ` K ) ` W ) ) ) )
       ( +g ` M ) ( M gsum ( i e. ( ( 0 ... A ) \ { W } ) |->
       ( ( Y ` i ) .^ ( X ( +g ` ( Poly1 ` K ) )
       ( S ` ( ( ZRHom ` K ) ` i ) ) ) ) ) ) ) ) $=
        ( cfv cmin co czrh cpl1 cplusg cc0 cfz csn cdif cv cmpt cgsu wcel cmulr
        cbs csg cdg1 clt wbr wceq cmnd cmgp crg ccrg fldcrngd eqid ply1crng syl
        wa crngring ringmgp eqeltrid fveq2i cz cle cn0 cmap wf cvv wb nn0ex a1i
        ovexd elmapg syl2anc mpbid ffvelcdmd nn0zd zsubcld nn0red mpbird elnn0z
        subge0d jca sylibr ringcmnd cmnmnd vr1cl czring ply1sclcl mndcl syl3anc
        ccmn crh eqcomi eleqtrrdi mulgnn0cld cfn adantr eleqtrdi mgpplusg eqtrd
        oveq1d oveq2d recnd eqcomd eqtr2d fveq1d fveq2d cmnf wne cdomn deg1xrcl
        oveq12d cxr c1 eqeltrd deg1nn0clb eqbrtrd zrhrhm zringbas rhmf elfzelzd
        mgpbas eqtri crngmgp fzfid diffi eldifi adantl 3syl mulgnn0cl ralrimiva
        elfzelz gsummptcl c0g cmncom oveqd ringassd caddc npcand w3a mulgnn0dir
        eleqtrd 3jca cun cascl simplr mpteq2dva fvmptd wss snssd undifr mpteq1d
        sylib neldifsnd fveq2 2fveq3 gsumunsn ringgrpd aks6d1c5lem0 deg1z cidom
        cgrp grpsubid cdr flddrngd drngdomn ply1domn isidom 0xr deg1sclle mulg1
        0lt1 cnzr cfield isfld biimpi simpld drngnzr 1nn0 deg1pw eqtr3d breqtrd
        xrlelttrd deg1add idomnnzpownz mnfltd cuc1p drnguc1p q1peqb ) AMOUKZCUL
        UMZNMKUNUKZUKZFUKZKUOUKZUPUKZUMZIUMZLHUQBURUMZMUSZUTZHVAZOUKZNUYEUXOUKZ
        FUKZUXSUMZIUMZVBVCUMZLUPUKZUMZUXRVFUKZVDZOJUKZUYMCUXTIUMZUXRVEUKZUMZUXR
        VGUKZUMZKVHUKZUKZUYQVUBUKZVIVJZVTZUYPUYQEUMUYMVKZAUYOVUEAUYMLVFUKZUYNAL
        VLVDUYAVUHVDZUYKVUHVDZUYMVUHVDALUXRVMUKZVLUJAUXRVNVDZVUKVLVDZAUXRVOVDZV
        ULAKVOVDZVUNAKPVPZUXRKUXRVQZVRVSZUXRWAVSZUXRVUKVUKVQZWBVSZWCAVUHIVUKUXN
        UXTLVUKVFUJWDZUBVVAAUXNWEVDZUQUXNWFVJZVTUXNWGVDZAVVCVVDAUXMCAUXMAUYBWGM
        OAOWGUYBWHUMZVDZUYBWGOWIZUDAWGWJVDZUYBWJVDVVGVVHWKVVIAWLWMAUQBURWNWGUYB
        OWJWJWOWPWQZUEWRZWSACUFWSWTAVVDCUXMWFVJUGAUXMCAUXMVVKXAZACUFXAZXDXBXEUX
        NXCXFZAUXTUYNVUHAUXRVLVDZNUYNVDZUXQUYNVDZUXTUYNVDZAUXRXNVDVVOAUXRVUSXGU
        XRXHVSZAKVNVDZVVPAVUOVVTVUPKWAVSZUYNUXRKNUAVUQUYNVQZXIVSZAVVTUXPKVFUKZV
        DZVVQVWAAWEVWDMUXOAUXOXJKXOUMVDZWEVWDUXOWIZAVVTVWFVWAKUXOUXOVQUUAZVSWEV
        WDXJKUXOUUBVWDVQZUUCZVSAMUQBUEUUDWRZFUYNUXRKUXPVWDVUQUIVWIVWBXKWPZUYNUX
        SUXRNUXQVWBUXSVQZXLXMZVUHVUKVFUKZUYNVVBUYNVWOUYNUXRVUKVUTVWBUUEZXPUUFZX
        QZXRZAVUHHLUYDUYJVUHVQZALVUKXNUJAVUNVUKXNVDVURUXRVUKVUTUUGVSWCZAUYBXSVD
        UYDXSVDAUQBUUHUYBUYCUUIVSZAUYJVUHVDZHUYDAUYEUYDVDZVTZVUMUYFWGVDUYIVUHVD
        VXCAVUMVXDVVAXTVXEUYBWGUYEOAVVHVXDVVJXTVXDUYEUYBVDZAUYEUYBUYCUUJUUKZWRV
        XEUYIUYNVUHVXEVVOVVPUYHUYNVDZUYIUYNVDAVVOVXDVVSXTAVVPVXDVWCXTVXEVVTUYGV
        WDVDVXHAVVTVXDVWAXTZVXEWEVWDUYEUXOVXEVVTVWFVWGVXIVWHVWJUULVXEVXFUYEWEVD
        VXGUYEUQBUUOVSWRFUYNUXRKUYGVWDVUQUIVWIVWBXKWPUYNUXSUXRNUYHVWBVWMXLXMVWQ
        XQVUHIVUKUYFUYIVVBUBUUMXMZUUNUUPZVUHUYLLUYAUYKVWTUYLVQZXLXMVWQYAAVUCUXR
        UUQUKZVUBUKZVUDVIAVUAVXMVUBAVUAUYPUYKUYAUYQUYRUMZUYRUMZUYTUMZVXMAUYSVXP
        UYPUYTAUYSUYKUYAUYLUMZUYQUYRUMZVXPAUYMVXRUYQUYRALXNVDVUIVUJUYMVXRVKVXAV
        WSVXKVUHUYLLUYAUYKVWTVXLUURXMYDAVXSUYKUYAUYRUMZUYQUYRUMVXPAVXRVXTUYQUYR
        AUYLUYRUYKUYAUYLUYRVKAUYRUYLUXRUYRLUJUYRVQZYBZXPWMUUSYDAUYNUXRUYRUYKUYA
        UYQVWBVYAVUSAUYKVUHUYNVXKVWQYAAUYAVUHUYNVWSVWQYAAUYNIVUKCUXTVWPUBVVAUFV
        WNXRZUUTYCYCYEAVXQUYPUYPUYTUMZVXMAVXPUYPUYPUYTAVXPUYKUXMUXTIUMZUYRUMZUY
        PAVXOVYEUYKUYRAVYEUXNCUVAUMZUXTIUMZVXOAUXMVYGUXTIAVYGUXMAUXMCAUXMVVLYFA
        CVVMYFUVBYGYDAVUMVVECWGVDZUXTVWOVDZUVCVYHVXOVKVVAAVVEVYIVYJVVNUFAUXTUYN
        VWOVWNUYNVWOVKAVWPWMUVEUVFVWOUYRIVUKUXNCUXTVWOVQZUBUXRUYRVUKVUTVYAYBUVD
        WPYHYEAUYPLHUYDUYCUVGZUYJVBZVCUMZVYFAUYPLHUYBUYJVBZVCUMZVYNAGOVUKHUYBUY
        EGVAZUKZNUYGUXRUVHUKZUKZUXSUMZIUMZVBZVCUMZVYPVVFJWJJGVVFWUDVBVKAUCWMAVY
        QOVKZVTZVUKLWUCVYOVCVUKLVKWUFLVUKUJXPWMWUFHUYBWUBUYJWUFVXFVTZVYRUYFWUAU
        YIIWUGUYEVYQOAWUEVXFUVIYIWUGVYTUYHNUXSWUGUYGVYSFVYSFVKWUGFVYSUIXPWMYIYE
        YOUVJYOUDALVYOVCWNUVKAVYOVYMLVCAHUYBVYLUYJAVYLUYBAUYCUYBUVLVYLUYBVKAMUY
        BUEUVMUYCUYBUVNUVPYGUVOYEYCAUYDVUHUYRHLMUYBUYJVYEVWTVYBVXAVXBVXJUEAMUYB
        UVQAVUHIVUKUXMUXTVVBUBVVAVVKVWRXRUYEMVKZUYFUXMUYIUXTIUYEMOUVRWUHUYHUXQN
        UXSUYEMFUXOUVSYEYOUVTYHYCYEAUXRUWEVDUYPUYNVDZVYDVXMVKAUXRVUSUWAAVVFUYNO
        JABDGHIJKNPQRSTUAUBUCUWBUDWRZUYNUXRUYTUYPVXMVWBVXMVQZUYTVQZUWFWPYCYCYJA
        VXNYKVUDVIAVVTVXNYKVKVWAVUBUXRKVXMVUBVQZVUQWUKUWCVSAVUDAVUDAUYQVXMYLZVU
        DWGVDZAUXTUXRICAVUNUXRYMVDZVTUXRUWDVDAVUNWUPVURAKYMVDZWUPAKUWGVDZWUQAKP
        UWHZKUWIVSUXRKVUQUWJVSXEUXRUWKXFVWNAUXTVXMYLZUXTVUBUKZWGVDZAWVANVUBUKZW
        GAUYNVUBUXSKNUXQUXRVUQWUMVWAVWBVWMVWCVWLAUXQVUBUKZUQWVCAVVQWVDYPVDVWLUY
        NVUBUXRKUXQWUMVUQVWBYNVSUQYPVDAUWLWMAVVPWVCYPVDVWCUYNVUBUXRKNWUMVUQVWBY
        NVSAVVTVWEWVDUQWFVJVWAVWKFVUBUXRKUXPVWDWUMVUQVWIUIUWMWPAUQYQWVCVIUQYQVI
        VJAUWOWMAWVCYQAYQNIUMZVUBUKZWVCYQAWVENVUBANVWOVDWVENVKANUYNVWOVWCVWPYAV
        WOIVUKNVYKUBUWNVSYJAKUWPVDZYQWGVDZWVFYQVKAWURWVGAWURVUOAKUWQVDZWURVUOVT
        ZPWVIWVJKUWRUWSVSUWTKUXAVSWVHAUXBWMZVUBUXRKIYQVUKNWUMVUQUAVUTUBUXCWPUXD
        ZYGUXEUXFUXGAWVCYQWGWVLWVKYRYRAVVTVVRWUTWVBWKVWAVWNUYNVUBUXRKUXTVXMWUMV
        UQWUKVWBYSWPXBUFUBUXHZAVVTUYQUYNVDZWUNWUOWKVWAVYCUYNVUBUXRKUYQVXMWUMVUQ
        WUKVWBYSWPWQXAUXIYTYTXEAVVTWUIUYQKUXJUKZVDZVUFVUGWKVWAWUJAWURWVNWUNWVPW
        USVYCWVMUYNWVOUXRKUYQVXMVUQVWBWUKWVOVQZUXKXMUYNWVOVUBUXREKUYRUYPUYQUYTU
        YMUHVUQVWBWUMWULVYAWVQUXLXMWQ $.
    $}

    ${
      $d .^ g i $.  $d A g i $.  $d K g i $.  $d W i $.  $d X g i $.
      $d Y g i $.  $d Z g i $.  $d g i ph $.
      aks6d1c5p2.1 $e |- ( ph -> Y e. ( NN0 ^m ( 0 ... A ) ) ) $.
      aks6d1c5p2.2 $e |- ( ph -> Z e. ( NN0 ^m ( 0 ... A ) ) ) $.
      aks6d1c5p2.3 $e |- ( ph -> ( G ` Y ) = ( G ` Z ) ) $.
      aks6d1c5p2.4 $e |- ( ph -> W e. ( 0 ... A ) ) $.
      aks6d1c5p2.5 $e |- ( ph -> ( Y ` W ) < ( Z ` W ) ) $.
      $( Lemma for Claim 5, contradiction of different evaluations that map to
         the same.  (Contributed by metakunt, 5-May-2025.) $)
      aks6d1c5lem2 $p |- ( ph -> ( 0g ` K ) =/= ( 0g ` K ) ) $=
        ( c0g cfv cc0 cmin co czrh cpl1 cascl cplusg cmgp cfz cdif cv cmpt cgsu
        csn ce1 cur cmulr cbs wcel wceq eqid cfield ccrg cdr simprbi syl czring
        isfld cz crh wf crg crngringd zrhrhm zringbas rhmf 0zd elfzelzd zsubcld
        ffvelcdmd mgpbas ccmn ply1crng crngmgp cmnmndd cle wbr cn0 cmap cvv a1i
        wa wb elmapg syl2anc mpbid nn0zd nn0red eqcomd jca elnn0z sylibr simpld
        leidd mulgnn0cld oveq1d fveq2d fveq1d ringidval eqcomi eqeltrd evl1expd
        mulg0 simprd eleqtrd cfn cmnd adantr adantl syl3anc ralrimiva gsummptcl
        eqtrd evl1muld wne fveval1fvcl eqidd clt eqnetrd aks6d1c5lem3 eleqtrdi
        ltled caddc nn0ex ovexd recnd subidd breqtrd evl1vard evl1scad evl1addd
        0red ply1idvr1 cmg fzfid diffi eldifi ringcmn cmnmnd ply1sclcl r19.21bi
        3syl mndcl evl1gprodd mgpplusg cdomn cidom fldidom isidom sylib ringmgp
        mndidcl flddrngd drngunz cprime aks6d1c5lem1 idomnnzpownz idomnnzgmulnz
        eldifsni necon3bid domnmuln0 necomd cq1p 3eqtrd resubcld posdifd rhmghm
        cghm ghmlin zringplusg oveqd 0cnd zcnd npcand zrh0 eqtr3d cn ringexp0nn
        oveq2d elnnz ringlzd neeqtrd ) AHUFUGZUHIUIUJZHUKUGZUGZIKUGZUXDUIUJZJIU
        XBUGZHULUGZUMUGZUGZUXGUNUGZUJZFUJZUXGUOUGZEUHBUPUJZIVAZUQZEURZKUGZJUXQU
        XBUGZUXHUGZUXJUJZFUJZUSUTUJZUXMUNUGZUJZHVBUGZUGZUGZUWTAUYHUWTAUYHHVCUGZ
        HUOUGZEUXPUXCUYBUYFUGUGZUSUTUJZHVDUGZUJZUWTAUYEUXGVEUGZVFUYHUYNVGAHVEUG
        ZUXGHUYDUYMUYOUXLUYCUYFUYIUYLUXCUYFVHZUXGVHZUYPVHZUYOVHZAHVIVFZHVJVFZMV
        UAHVKVFZVUBHVOVLVMZAVPUYPUXAUXBAUXBVNHVQUJVFZVPUYPUXBVRZAHVSVFZVUEAHVUD
        VTZHUXBUXBVHZWAZVMZVPUYPVNHUXBWBUYSWCZVMZAUHIAWDAIUHBUDWEZWFZWGZAUXLUYO
        VFUXCUXLUYFUGZUGZUYIVGAUYOFUXMUXEUXKUYOUXGUXMUXMVHZUYTWHZSAUXMAUXGVJVFZ
        UXMWIVFAVUBVVAVUDUXGHUYRWJVMZUXGUXMVUSWKVMZWLZAUXEVPVFZUHUXEWMWNZWSUXEW
        OVFAVVEVVFAUXDUXDAUXDAUXNWOIKAKWOUXNWPUJZVFZUXNWOKVRZUAAWOWQVFZUXNWQVFZ
        VVHVVIWTVVJAUUAWRZAUHBUPUUBZWOUXNKWQWQXAXBXCZUDWGZXDZVVPWFAUHUHUXEWMAUH
        AUUIZXKAUXEUHAUXDAUXDAUXDVVOXEZUUCUUDZXFZUUEXGUXEXHXIZAUXKUYOVFZUXCUXKU
        YFUGUGUXCUXFHUNUGZUJZVGAUYPUXGVWCUXJHUYOJUXIUYFUXCUXFUXCUYQUYRUYSUYTVUD
        VUPAUYPUXGHUYOUYFJUXCUYQRUYSUYRUYTVUDVUPUUFZAUXHUYPUXGHUYOUYFUXFUXCUYQU
        YRUYSUXHVHZUYTVUDAVPUYPIUXBVUMVUNWGVUPUUGUXJVHZVWCVHZUUHZXJZXLAVURUXCUX
        MUFUGZUYFUGZUGZUYIAUXCVUQVWLAUXLVWKUYFAUXLUHUXKFUJZVWKAUXEUHUXKFVVSXMAV
        WBVWNVWKVGVWJUYOFUXMUXKVWKVUTVWKVHSXTVMYJXNXOAVWMUXCUXGVCUGZUYFUGZUGZUY
        IAUXCVWLVWPAVWKVWOUYFVWKVWOVGAVWOVWKUXGVWOUXMVUSVWOVHXPXQWRXNXOAVWQUXCU
        HJFUJZUYFUGZUGZUYIAUXCVWPVWSAVWOVWRUYFAVUGVWOVWRVGVUHVUGVWRVWOUXGHFUXMJ
        UYRRVUSSUUJXFVMXNXOAVWTUHUXCUYJUUKUGZUJZUYIAVWRUYOVFVWTVXBVGAUYPUXGHFUY
        OVXAJUHUYFUXCUXCUYQUYRUYSUYTVUDVUPVWESVXAVHZAUHUXEWOVVTVWAXRXSYAAVXBUYJ
        UFUGZUYIAUXCUYJVEUGZVFVXBVXDVGAUXCUYPVXEVUPUYPVXEVGAUYPHUYJUYJVHZUYSWHZ
        WRYBVXEVXAUYJUXCVXDVXEVHVXDVHZVXCXTVMVXDUYIVGAUYIVXDHUYIUYJVXFUYIVHZXPZ
        XQWRYJYJYJYJYJXGAUYCUYOVFUXCUYCUYFUGUGUYLVGAUYOEUXMUXPUYBVUTVVCAUXNYCVF
        UXPYCVFAUHBUULUXNUXOUUMVMZAUYBUYOVFZEUXPAUXQUXPVFZWSZUYOFUXMUXRUYAVUTSA
        UXMYDVFVXMVVDYEZVXNUXNWOUXQKAVVIVXMVVNYEVXMUXQUXNVFAUXQUXNUXOUUNYFZWGZV
        XNUXGYDVFZJUYOVFZUXTUYOVFZUYAUYOVFZAVXRVXMAUXGWIVFZVXRAUXGVSVFVYBAUXGVV
        BVTUXGUUOVMUXGUUPVMYEAVXSVXMAVXSUXCJUYFUGUGUXCVGVWEXJYEVXNVUGUXSUYPVFVX
        TAVUGVXMVUHYEZVXNVPUYPUXQUXBVXNVUGVUEVUFVYCVUJVULUUSVXNUXQUHBVXPWEWGUXH
        UYOUXGHUXSUYPUYRVWFUYSUYTUUQXBUYOUXJUXGJUXTUYTVWGUUTYGZXLZYHZYIAEUYPUXG
        UXMHUYJUYOUYBUXPUYFUXCUYQUYRVUSUYSUYTVXFVUDVUPAVXLEUXPAVXLEUXPVYFUURYHV
        XKUVAXGUXGVDUGZUYDUXGVYGUXMVUSVYGVHUVBXQZUYMVHZYKYAAHUVCVFZUYIUYPVFZUYI
        UWTYLZWSUYLUYPVFZUYLUWTYLZWSUYNUWTYLAVUBVYJAHUVDVFZVUBVYJWSAVUAVYOMHUVE
        VMZHUVFUVGYAAVYKVYLAUYIVXDUYPUYIVXDVGAVXJWRAUYJYDVFZVXDUYPVFAVUGVYQVUHH
        UYJVXFUVHVMUYPUYJVXDVXGVXHUVIVMXRAVUCVYLAHMUVJHUYIUWTUWTVHZVXIUVKVMXGAV
        YMVYNAUYPEUYJUXPUYKVXGAVUBUYJWIVFVUDHUYJVXFWKVMVXKAUYKUYPVFEUXPVXNUYPUX
        GHUYOUYBUYFUXCUYQUYRUYSUYTAVUBVXMVUDYEZAUXCUYPVFVXMVUPYEZVYEYMZYHYIAUYK
        HEUYJUXPVXFVYPVXKWUAVXNUYKUXRUXCUYAUYFUGUGZVXAUJZUWTVXNVXLUYKWUCVGVXNUY
        PUXGHFUYOVXAUYAUXRUYFWUBUXCUYQUYRUYSUYTVYSVYTVXNVYAWUBWUBVGVXNUYAUXMVEU
        GZUYOVXNUYAUYOWUDVYDUYOWUDVGVXNVUTWRYBZWUDUYOVGVXNUYOWUDVUTXQWRZYBZVXNW
        UBYNXGSVXCVXQXSYAVXNWUBHVXAUXRAVYOVXMVYPYEVXNUYPUXGHUYOUYAUYFUXCUYQUYRU
        YSUYTVYSVYTWUGYMVXNUXQIYLZWUBUWTYLVXMWUHAUXQUXNIUVPYFVXNUXQIWUBUWTVXNBU
        XQICDEFGHJAVUAVXMMYEACUVLVFVXMNYEOABWOVFVXMPYEABCYOWNVXMQYERSTVXPAIUXNV
        FVXMUDYEUVMUVQXCVXQVXCUVNYPUVOXGUYPHUYMUYIUYLUWTUYSVYIVYRUVRYGYPUVSAUYH
        UXCILUGZUXDUIUJZUXKFUJZUXMEUXPUXQLUGZUYAFUJZUSUTUJZUYDUJZUYFUGZUGZUWTAU
        XCUYGWUPAUYEWUOUYFAUYEKGUGZUXDUXKFUJZHUVTUGZUJZLGUGZWUSWUTUJWUOAWVAUYEA
        BUXDCWUTUXHDEFGHUXMIJKMNOPQRSTUAUDVVOAUXDVVRXKWUTVHZVWFVUSYQXFAWURWVBWU
        SWUTUCXMABUXDCWUTUXHDEFGHUXMIJLMNOPQRSTUBUDVVOAUXDWUIVVRAWUIAUXNWOILALV
        VGVFZUXNWOLVRZUBAVVJVVKWVDWVEWTVVLVVMWOUXNLWQWQXAXBXCZUDWGZXEZUEYSWVCVW
        FVUSYQUWAXNXOAWUQUWTUXCWUNUYFUGUGZUYMUJZUWTAWUOUYOVFWUQWVJVGAUYPUXGHUYD
        UYMUYOWUKWUNUYFUWTWVIUXCUYQUYRUYSUYTVUDVUPAWUKUYOVFZUXCWUKUYFUGUGZUWTVG
        AWVKWVLWUJVWDVXAUJZVGZAUYPUXGHFUYOVXAUXKWUJUYFVWDUXCUYQUYRUYSUYTVUDVUPV
        WISVXCAWUJVPVFZUHWUJWMWNZWSWUJWOVFAWVOWVPAWUIUXDAWUIWVGXDVVPWFAUHWUJVVQ
        AWUIUXDWVHVVRUWBAUXDWUIYOWNUHWUJYOWNZUEAUXDWUIVVRWVHUWCXCZYSXGWUJXHXIZX
        SZXJAWVLWVMUWTAWVKWVNWVTYAAWVMWUJUWTVXAUJUWTAVWDUWTWUJVXAAUXAIVNUNUGZUJ
        ZUXBUGZVWDUWTAUXBVNHUWEUJVFZUXAVNVEUGZVFIWWEVFWWCVWDVGAVUEWWDVUKVNHUXBU
        WDVMAUXAVPWWEVUOWBYRAIVPWWEVUNWBYRWWAVWCVNHUXAUXBIWWEWWEVHWWAVHVWHUWFYG
        AWWCUHUXBUGZUWTAWWCUXAIYTUJZUXBUGWWFAWWBWWGUXBAWWAYTUXAIWWAYTVGAYTWWAUW
        GXQWRUWHXNAWWGUHUXBAUHIAUWIAIVUNUWJUWKXNYJAVUGWWFUWTVGVUHHUXBUWTVUIVYRU
        WLVMYJUWMUWPAHVXAWUJVUHAWVOWVQWSWUJUWNVFAWVOWVQAWUJWVSXDWVRXGWUJUWQXIVX
        CUWOYJYJXGAWUNUYOVFWVIWVIVGAUYOEUXMUXPWUMVUTVVCVXKAWUMUYOVFEUXPVXNWUMWU
        DUYOVXNWUDFUXMWULUYAWUDVHSVXOVXNUXNWOUXQLAWVEVXMWVFYEVXPWGWUEXLWUFYBYHY
        IZAWVIYNXGVYHVYIYKYAAUYPHUYMWVIUWTUYSVYIVYRVUHAUYPUXGHUYOWUNUYFUXCUYQUY
        RUYSUYTVUDVUPWWHYMUWRYJYJUWS $.
    $}

    ${
      $d A g i $.  $d A x y z $.  $d G x y z $.  $d K g i $.  $d K z $.
      $d g i ph $.  $d ph x y z $.  $d .^ g i $.  $d A g i x y z $.
      $d G g i x y z $.  $d K g i z $.  $d X g i $.  $d g i ph x y z $.
      $( Claim 5 of Theorem 6.1 ~ https://www3.nd.edu/%7eandyp/notes/AKS.pdf .
         The mapping defined by ` G ` is injective.  (Contributed by metakunt,
         5-May-2025.) $)
      aks6d1c5 $p |- ( ph -> G : ( NN0 ^m ( 0 ... A ) ) -1-1->
     ( Base ` ( Poly1 ` K ) ) ) $=
        ( cfv wa wcel vx vy vz cn0 cc0 cfz co cmap cpl1 cbs wf cv wceq wral wf1
        wi cmgp czrh cascl cplusg cmpt cgsu eqid ccmn fldcrngd ply1crng crngmgp
        ccrg syl adantr fzfid cmnd cmnmndd nn0ex ovexd elmapd biimpd ffvelcdmda
        cvv a1i imp crngringd ringcmnd cmnmnd crg vr1cl cz simpl elfzelz adantl
        jca czring zrhrhm zringbas rhmf ply1sclcl syl2anc mndcl syl3anc eleqtrd
        crh mgpbas mulgnn0cld ralrimiva gsummptcl eqcomi fmptd wn wne c0g eqidd
        wrex wo simpr neneqd wfn simp-4r mpbid ffn simpllr eqfnfv2 notbid ianor
        wb mpd sylib notnotd orcnd rexnal sylibr rexbii clt wbr nn0red ad2antrr
        df-ne ad6antr simplr aks6d1c5lem2 ex simprl simprr jca31 lttri2d cfield
        cprime eqcomd jaodan sylbid rexlimddv pm2.65da notbii notnotb dff13 ) A
        UDUEBUFUGZUHUGZHUIRZUJRZGUKZUAULZGRZUBULZGRZUMZUUTUVBUMZUPZUBUUPUNZUAUU
        PUNZSUUPUURGUOAUUSUVHADUUPUUQUQRZEUUOEULZDULZRZIUVJHURRZRZUUQUSRZRZUUQU
        TRZUGZFUGZVAVBUGZUURGAUVKUUPTZSZUVTUVIUJRZUURUWBUWCEUVIUUOUVSUWCVCZAUVI
        VDTZUWAAUUQVHTZUWEAHVHTUWFAHJVEZUUQHUUQVCZVFVIZUUQUVIUVIVCZVGVIVJZUWBUE
        BVKUWBUVSUWCTEUUOUWBUVJUUOTZSZUWCFUVIUVLUVRUWDPUWBUVIVLTUWLUWBUVIUWKVMV
        JUWBUUOUDUVJUVKAUWAUUOUDUVKUKZAUWAUWNAUDUUOUVKVSVSUDVSTZAVNVTAUEBUFVOVP
        VQWAVRUWMUVRUURUWCUWMUUQVLTZIUURTZUVPUURTZUVRUURTUWBUWPUWLAUWPUWAAUUQVD
        TUWPAUUQAUUQUWIWBWCUUQWDVIVJVJUWMHWETZUWQUWBUWSUWLAUWSUWAAHUWGWBVJZVJZU
        URUUQHIOUWHUURVCZWFVIUWMUWSUVNHUJRZTZUWRUXAUWMUWBUVJWGTZSUXDUWMUWBUXEUW
        BUWLWHUWLUXEUWBUVJUEBWIWJWKUWBWGUXCUVJUVMUWBUWSWGUXCUVMUKZUWTUWSUVMWLHX
        AUGTUXFHUVMUVMVCWMWGUXCWLHUVMWNUXCVCZWOVIVIVRVIUVOUURUUQHUVNUXCUWHUVOVC
        UXGUXBWPWQUURUVQUUQIUVPUXBUVQVCWRWSUURUWCUMUWMUURUUQUVIUWJUXBXBZVTWTXCX
        DXEUWCUURUMUWBUURUWCUXHXFVTWTQXGAUVGUAUUPAUUTUUPTZSZUVFUBUUPUXJUVBUUPTZ
        SZUVDUVEUXLUVDSZUVEXHZXHZUVEUXMUUTUVBXIZXHUXOUXMUXPHXJRZUXQUMUXMUXPSZUX
        QXKUXRUXQUXQUXRUCULZUUTRZUXSUVBRZXIZUXQUXQXIZUCUUOUXRUXTUYAUMZXHZUCUUOX
        LZUYBUCUUOXLUXRUYDUCUUOUNZXHZUYFUXRUUOUUOUMZXHZUYHUXRUYIUYGSZXHZUYJUYHX
        MUXRUXNUYLUXRUUTUVBUXMUXPXNXOUXRUXNUYLUXRUVEUYKUXRUUTUUOXPZUVBUUOXPZUVE
        UYKYDUXRUUOUDUUTUKZUYMUXRUXIUYOAUXIUXKUVDUXPXQZUXRUDUUOUUTVSVSUWOUXRVNV
        TZUXRUEBUFVOZVPZXRUUOUDUUTXSVIUXRUUOUDUVBUKZUYNUXRUXKUYTUXJUXKUVDUXPXTZ
        UXRUDUUOUVBVSVSUYQUYRVPZXRUUOUDUVBXSVIUCUUOUUOUUTUVBYAWQYBVQYEUYIUYGYCY
        FUXRUYIUXRUUOXKYGYHUYDUCUUOYIYJUYBUYEUCUUOUXTUYAYPYKYJUXRUXSUUOTZUYBSZS
        ZUXRVUCSZUYBSUYCVUEUXRVUCUYBUXRVUDWHUXRVUCUYBUUAUXRVUCUYBUUBUUCVUFUYBUY
        CVUFUYBUXTUYAYLYMZUYAUXTYLYMZXMZUYCVUFUXTUYAVUFUXTUXRUUOUDUXSUUTUXRUXIU
        YOUYPUXRUXIUYOUYSVQYEVRYNVUFUYAUXRUUOUDUXSUVBUXRUXKUYTVUAUXRUXKUYTVUBVQ
        YEVRYNUUDVUFVUIUYCVUFVUGUYCVUHVUFVUGSBCDEFGHUXSIUUTUVBAHUUETZUXIUXKUVDU
        XPVUCVUGJYQACUUFTZUXIUXKUVDUXPVUCVUGKYQLABUDTZUXIUXKUVDUXPVUCVUGMYQABCY
        LYMZUXIUXKUVDUXPVUCVUGNYQOPQUXRUXIVUCVUGUYPYOUXRUXKVUCVUGVUAYOUXLUVDUXP
        VUCVUGXQUXRVUCVUGYRVUFVUGXNYSVUFVUHSZBCDEFGHUXSIUVBUUTAVUJUXIUXKUVDUXPV
        UCVUHJYQAVUKUXIUXKUVDUXPVUCVUHKYQLAVULUXIUXKUVDUXPVUCVUHMYQAVUMUXIUXKUV
        DUXPVUCVUHNYQOPQUXRUXKVUCVUHVUAYOUXRUXIVUCVUHUYPYOVUNUVAUVCUXLUVDUXPVUC
        VUHXQUUGUXRVUCVUHYRVUFVUHXNYSUUHYTUUIWAVIUUJXOUUKUXPUXNUUTUVBYPUULYFUVE
        UUMYJYTXDXDWKUAUBUUPUURGUUNYJ $.
    $}
  $}

  ${
    $d C a b c n $.  $d C b c n y $.  $d N a b c n x $.  $d N b c n x y $.
    $d R a b c n x $.  $d R b c n x y $.  $d a b c n ph $.  $d ph y $.
    deg1gprod.1 $e |- ( ph -> R e. IDomn ) $.
    deg1gprod.2 $e |- ( ph -> N e. Fin ) $.
    deg1gprod.3 $e |- ( ph -> A. x e. N ( C e. ( Base ` ( Poly1 ` R ) )
     /\ C =/= ( 0g ` ( Poly1 ` R ) ) ) ) $.
    $( Degree multiplication is a homomorphism.  (Contributed by metakunt,
       6-May-2025.) $)
    deg1gprod $p |- ( ph -> ( ( ( deg1 ` R ) `
     ( ( mulGrp ` ( Poly1 ` R ) ) gsum ( x e. N |-> C ) ) ) =
    sum_ n e. N ( ( deg1 ` R ) ` ( ( x e. N |-> C ) ` n ) ) /\
    0 <_ ( ( deg1 ` R ) ` ( ( mulGrp ` ( Poly1 ` R ) )
     gsum ( x e. N |-> C ) ) ) ) ) $=
      ( vy cfv cgsu co wceq cc0 wa fveq2d eqid wcel adantr va vb cpl1 cmgp cmpt
      vc cv cdg1 csu cle wbr c0 csn mpteq1 oveq2d sumeq1 eqeq12d breq2d anbi12d
      cun c0g a1i gsum0 eqtrd cur cascl crg idomringd ringidval eqcomi ply1scl1
      mpt0 syl eqcomd cbs wne ringidcl cnzr cdomn domnnzr nzrnz deg1scl syl3anc
      idomdomd sum0 0red leidd breqtrd jca wss cdif nfcv nfcsb1v csbeq1a cbvmpt
      csb cplusg ccmn ccrg cidom isidom sylib ply1crng crngmgp ad2antrr simplrl
      simpld ssfid wral sselda r19.26 biimpi ad3antrrr rspcsbela syl2anc mgpbas
      cfn eleqtrdi eldifi adantl wn eldifn csbeq1 gsumunsn caddc cmulr mgpplusg
      ralrimiva gsummptcl ply1idom simprd rspcsbnea idomnnzgmulnz cn0 deg1nn0cl
      oveq1d eqeltrd nn0cnd snssd unssd deg1mul simpl simprl fveq1i eqidd simpr
      nfv csbeq1d fvmptd 2fveq3 fvmpts syl2anr fsumsplitsn wi ssralv mpd oveq2i
      eqnetrd nn0ge0d ex findcard2d ) ADUCKZUDKZBUAUGZCUEZLMZDUHKZKZUVDEUGZBFCU
      EZKZUVGKZEUIZNZOUVHUJUKZPUVCBULCUEZLMZUVGKZULUVLEUIZNZOUVRUJUKZPUVCBUBUGZ
      CUEZLMZUVGKZUWBUVLEUIZNZOUWEUJUKZPZUVCBUWBUFUGZUMZUTZCUEZLMZUVGKZUWLUVLEU
      IZNZOUWOUJUKZPZUVCUVJLMZUVGKZFUVLEUIZNZOUXAUJUKZPUAUBUFFUVDULNZUVNUVTUVOU
      WAUXEUVHUVRUVMUVSUXEUVFUVQUVGUXEUVEUVPUVCLBUVDULCUNUOQZUVDULUVLEUPUQUXEUV
      HUVROUJUXFURUSUVDUWBNZUVNUWGUVOUWHUXGUVHUWEUVMUWFUXGUVFUWDUVGUXGUVEUWCUVC
      LBUVDUWBCUNUOQZUVDUWBUVLEUPUQUXGUVHUWEOUJUXHURUSUVDUWLNZUVNUWQUVOUWRUXIUV
      HUWOUVMUWPUXIUVFUWNUVGUXIUVEUWMUVCLBUVDUWLCUNUOQZUVDUWLUVLEUPUQUXIUVHUWOO
      UJUXJURUSUVDFNZUVNUXCUVOUXDUXKUVHUXAUVMUXBUXKUVFUWTUVGUXKUVEUVJUVCLBUVDFC
      UNUOQZUVDFUVLEUPUQUXKUVHUXAOUJUXLURUSAUVTUWAAUVROUVSAUVRUVCVAKZUVGKZOAUVQ
      UXMUVGAUVQUVCULLMZUXMAUVPULUVCLUVPULNABCVLVBUOUXOUXMNAUVCUXMUXMRVCVBVDQAU
      XNDVEKZUVBVFKZKZUVGKZOAUXMUXRUVGAUXRUXMADVGSZUXRUXMNADGVHZUXQUVBDUXPUXMUV
      BRZUXQRZUXPRZUVBVEKZUXMUVBUYEUVCUVCRZUYERVIVJVKVMVNQAUXTUXPDVOKZSZUXPDVAK
      ZVPZUXSONUYAAUXTUYHUYAUYGDUXPUYGRZUYDVQVMADVRSZUYJADVSSZUYLADGWDZDVTVMDUX
      PUYIUYDUYIRZWAVMUXQUVGUVBDUXPUYGUYIUVGRZUYBUYKUYCUYOWBWCVDVDZOUVSNAUVSOUV
      LEWEVJVBVDAOOUVRUJAOAWFWGAUVROUYQVNWHWIAUWBFWJZUWJFUWBWKSZPZPZUWIUWSVUAUW
      IPZUWQUWRVUBUWOUVCJUWLBJUGZCWPZUEZLMZUVGKZUWPVUBUWNVUFUVGVUBUWMVUEUVCLUWM
      VUENVUBBJUWLCVUDJCWLZBVUCCWMZBVUCCWNZWOZVBUOQVUBVUGUVCJUWBVUDUEZLMZBUWJCW
      PZUVCWQKZMZUVGKZUWPVUBVUFVUPUVGVUBUWBUVCVOKZVUOJUVCUWJFVUDVUNVURRVUORVUAU
      VCWRSZUWIAVUSUYTAUVBWSSZVUSADWSSZVUTAVVAUYMADWTSZVVAUYMPGDXAXBXGUVBDUYBXC
      VMUVBUVCUYFXDVMTTZVUBFUWBAFXQSZUYTUWIHXEZAUYRUYSUWIXFZXHZVUBVUCUWBSZPZVUD
      UVBVOKZVURVVIVUCFSZCVVJSZBFXIZVUDVVJSZVUBUWBFVUCVVFXJZAVVMUYTUWIVVHAVVMCU
      VBVAKZVPZBFXIZAVVLVVQPBFXIZVVMVVRPZIVVSVVTVVLVVQBFXKXLVMZXGZXMBVUCFCVVJXN
      ZXOZVVJUVBUVCUYFVVJRZXPZXRVUAUWJFSZUWIUYTVWGAUYSVWGUYRUWJFUWBXSXTZXTZTZVU
      AUWJUWBSYAZUWIUYTVWKAUYSVWKUYRUWJFUWBYBXTXTZTVUBVUNVVJVURVUBVWGVVMVUNVVJS
      ZVWJAVVMUYTUWIVWBXEBUWJFCVVJXNZXOZVWFXRBVUCUWJCYCYDQVUBVUQVUMUVGKZVUNUVGK
      ZYEMZUWPVUBVVJUVGUVBDVUOVUMVUNVVPUYPUYBVWEUVBYFKZVUOUVBVWSUVCUYFVWSRYGVJV
      VPRZVUAUYMUWIAUYMUYTUYNTTVUBVVJJUVCUWBVUDVWFVVCVVGVUBVVNJUWBVWDYHYIVUBVUD
      UVBJUVCUWBUYFVUAUVBWTSZUWIAVXAUYTAVVBVXAGUVBDUYBYJVMTZTVVGVWDVVIVVKVVRVUD
      VVPVPZVVOAVVRUYTUWIVVHAVVMVVRVWAYKZXMBVUCFCVVPYLZXOYMVWOVUBVWGVVRVUNVVPVP
      ZVWJAVVRUYTUWIVXDXEBUWJFCVVPYLZXOUUAVUBVWRUWEVWQYEMZUWPVUBVWPUWEVWQYEVUBV
      UMUWDUVGVUBVULUWCUVCLVULUWCNVUBUWCVULBJUWBCVUDVUHVUIVUJWOVJVBUOQYPVUBVXHU
      WFVWQYEMZUWPVUBUWEUWFVWQYEUWIUWGVUAUWGUWHUUBXTYPVUBUWPVXIVUBUWPUWFUWJUVJK
      ZUVGKZYEMZVXIVUAUWPVXLNUWIVUAUWBUWJUVLVXKEFVUAEUUGEVXKWLVUAFUWBAVVDUYTHTZ
      AUYRUYSUUCZXHVWIVWLVUAUVIUWBSZPZUVLVXPUVLUVIJFVUDUEZKZUVGKZYNVXPUVKVXRUVG
      UVKVXRNVXPUVIUVJVXQBJFCVUDVUHVUIVUJWOUUDVBQVXPVXSBUVICWPZUVGKZYNVXPVXRVXT
      UVGVXPJUVIVUDVXTFVXQVVJVXPVXQUUEVXPVUCUVINZPBVUCUVICVXPVYBUUFUUHVUAUWBFUV
      IVXNXJZVXPUVIFSZVVMVXTVVJSZVYCVUAVVMVXOAVVMUYTVWBTZTBUVIFCVVJXNXOZUUIQVXP
      UXTVYEVXTVVPVPZVYAYNSVUAUXTVXOAUXTUYTUYATZTVYGVXPVYDVVRVYHVYCAVVRUYTVXOVX
      DXEBUVIFCVVPYLXOVVJUVGUVBDVXTVVPUYPUYBVWTVWEYOWCYQYQYRUVIUWJUVGUVJUUJVUAV
      XKVUAVXKVWQYNVUAVXJVUNUVGVUAVWGVWMVXJVUNNZVWIVUAVWGVVMVWMVWIVYFVWNXOZBUWJ
      CFUVJVVJUVJRUUKXOZQVUAUXTVWMVXFVWQYNSVYIVYKUYTVWGVVRVXFAVWHVXDVXGUULVVJUV
      GUVBDVUNVVPUYPUYBVWTVWEYOWCYQYRUUMTVUBVXKVWQUWFYEVUBVXJVUNUVGVUAVYJUWIVYL
      TQUOVDVNVDVDVDVDVDVUBUWOVUBUXTUWNVVJSUWNVVPVPZUWOYNSVUAUXTUWIVYITVUBVVJBU
      VCUWLCVWFVVCVUBFUWLVVEVUBUWBUWKFVVFVUBUWJFVWJYSYTZXHVUBVVMVVLBUWLXIZVUAVV
      MUWIVYFTVUBUWLFWJVVMVYOUUNVYNVVLBUWLFUUOVMUUPYIVUAVYMUWIVUAUWNVUFVVPUWNVU
      FNVUAUWMVUEUVCLVUKUUQVBVUAVUDUVBJUVCUWLUYFVXBVUAFUWLVXMVUAUWBUWKFVXNVUAUW
      JFVWIYSYTZXHVUAVUCUWLSZPZVVKVVMVVNVUAUWLFVUCVYPXJZVUAVVMVYQVYFTVWCXOVYRVV
      KVVRVXCVYSAVVRUYTVYQVXDXEVXEXOYMUURTVVJUVGUVBDUWNVVPUYPUYBVWTVWEYOWCUUSWI
      UUTHUVA $.
  $}

  ${
    $d .^ x y $.  $d A x $.  $d D x y $.  $d F x y $.  $d ph x y $.
    deg1pow.1 $e |- ( ph -> R e. IDomn ) $.
    deg1pow.2 $e |- ( ph -> F e. ( Base ` ( Poly1 ` R ) ) ) $.
    deg1pow.3 $e |- ( ph -> F =/= ( 0g ` ( Poly1 ` R ) ) ) $.
    deg1pow.4 $e |- ( ph -> A e. NN0 ) $.
    deg1pow.5 $e |- .^ = ( .g ` ( mulGrp ` ( Poly1 ` R ) ) ) $.
    deg1pow.6 $e |- D = ( deg1 ` R ) $.
    $( Exact degree of a power of a polynomial in an integral domain.
       (Contributed by metakunt, 6-May-2025.) $)
    deg1pow $p |- ( ph -> ( D ` ( A .^ F ) ) = ( A x. ( D ` F ) ) ) $=
      ( wcel co cfv cmul wceq cc0 eqid syl vx vy cv caddc fvoveq1 oveq1 eqeq12d
      cn0 cpl1 cur cbs cmgp mgpbas ringidval mulg0 fveq2d cascl crg cidom cdomn
      c1 ccrg isidom simprbi domnring ply1scl1 eqcomd c0g ringidcl cnzr domnnzr
      wne nzrnz deg1scl syl3anc deg1nn0cl nn0cnd mul02d wa cplusg cmnd ply1idom
      eqtrd idomringd adantr ringmgp ad2antrr mulgnn0p1 cmulr mgpplusg idomdomd
      simplr eqcomi mulgnn0cld idomnnzpownz deg1mul oveq1d cc adddirp1d nn0indd
      simpr ex mpd ) ABUHMZBFENCOZBFCOZPNZQZJAXDXHAUAUCZFENCOZXIXFPNZQRFENZCOZR
      XFPNZQUBUCZFENZCOZXOXFPNZQZXOVAUDNZFENZCOZXTXFPNZQXHUAUBBXIRQXJXMXKXNXIRF
      CEUEXIRXFPUFUGXIXOQXJXQXKXRXIXOFCEUEXIXOXFPUFUGXIXTQXJYBXKYCXIXTFCEUEXIXT
      XFPUFUGXIBQXJXEXKXGXIBFCEUEXIBXFPUFUGAXMRXNAXMDUIOZUJOZCOZRAXLYECAFYDUKOZ
      MZXLYEQHYGEYDULOZFYEYGYDYIYISZYGSZUMZYDYEYIYJYESZUNKUOTUPAYFDUJOZYDUQOZOZ
      COZRAYEYPCAYPYEADURMZYPYEQADUSMZYRGYSDUTMZYRYSDVBMYTDVCVDZDVETTZYOYDDYNYE
      YDSZYOSZYNSZYMVFTVGUPAYRYNDUKOZMZYNDVHOZVLZYQRQUUBAYRUUGUUBUUFDYNUUFSZUUE
      VITADVJMZUUIAYTUUKAYSYTGUUATDVKTDYNUUHUUEUUHSZVMTYOCYDDYNUUFUUHLUUCUUJUUD
      UULVNVOWCWCAXNRAXFAXFAYRYHFYDVHOZVLZXFUHMUUBHIYGCYDDFUUMLUUCUUMSZYKVPVOVQ
      ZVRVGWCAXOUHMZVSZXSVSZYBXPFYIVTOZNZCOZYCUUSYAUVACUUSYIWAMZUUQYHYAUVAQUUSY
      DURMZUVCUURUVDXSAUVDUUQAYDAYSYDUSMZGYDDUUCWBTZWDWEWEYDYIYJWFTZAUUQXSWLZAY
      HUUQXSHWGZYGUUTEYIXOFYLKUUTSWHVOUPUUSUVBXQXFUDNZYCUUSYGCYDDUUTXPFUUMLUUCY
      KYDWIOZUUTYDUVKYIYJUVKSWJWMUUOUURYTXSAYTUUQADGWKWEWEUUSYGEYIXOFYLKUVGUVHU
      VIWNUUSFYDEXOUURUVEXSAUVEUUQUVFWEWEUVIAUUNUUQXSIWGZUVHKWOUVIUVLWPUUSUVJXR
      XFUDNZYCUUSXQXRXFUDUURXSXAWQUUSYCUVMUUSXOXFUUSXOUVHVQAXFWRMUUQXSUUPWGWSVG
      WCWCWCWTXBXC $.
  $}

  ${
    $( The value of 5 choose 2.  (Contributed by metakunt, 8-Jun-2024.) $)
    5bc2eq10 $p |- ( 5 _C 2 ) = ; 1 0 $=
      ( c5 c2 cbc co c4 c1 cmin caddc c6 cc0 cdc cn0 wcel cz wceq 4nn0 2z eqtri
      bcpasc oveq2i mp2an 4p1e5 oveq1i eqcomi 2m1e1 4bc2eq6 bcn1 oveq12i 6p4e10
      ax-mp 3eqtri ) ABCDZEBCDZEBFGDZCDZHDZIEHDZFJKUPULUPEFHDZBCDZULELMZBNMUPUS
      OPQBESUAURABCUBUCRUDUPUMEFCDZHDUQUOVAUMHUNFECUETTUMIVAEHUFUTVAEOPEUGUJUHR
      UIUK $.
  $}

  $( The factorial of a successor's successor.  (Contributed by metakunt,
     19-Apr-2024.) $)
  facp2 $p |- ( N e. NN0 -> ( ! ` ( N + 2 ) )
                         = ( ( ! ` N ) x. ( ( N + 1 ) x. ( N + 2 ) ) ) ) $=
    ( cn0 wcel c2 caddc co cfa cfv c1 cmul wceq nn0cn ax-1cn addass mp3an23 syl
    cc df-2 eqtrd facp1 oveq2i eqcomi a1i fveq2d peano2nn0 eqtr3d oveq2d oveq1d
    cn faccl nncn 2cn addcl mpan2 mulass syl3anc ) ABCZADEFZGHZAGHZAIEFZJFZURJF
    ZUTVAURJFJFZUQUSVAGHZURJFZVCUQUSVEVAIEFZJFZVFUQVGGHZUSVHUQVGURGUQVGAIIEFZEF
    ZURUQAQCZVGVKKZALZVLIQCZVOVMMMAIINOPVKURKUQURVKDVJAERUAUBUCSZUDUQVABCZVIVHK
    AUEZVATPUFUQVGURVEJVPUGSUQVEVBURJATUHSUQUTQCZVAQCZURQCZVCVDKUQUTUICVSAUJUTU
    KPUQVQVTVRVALPUQVLWAVNVLDQCWAULADUMUNPUTVAURUOUPS $.

  ${
    2np3bcnp1.1 $e |- ( ph -> N e. NN0 ) $.
    $( Part of induction step for ~ 2ap1caineq .  (Contributed by metakunt,
       8-Jun-2024.) $)
    2np3bcnp1 $p |- ( ph ->
     ( ( ( 2 x. ( N + 1 ) ) + 1 ) _C ( N + 1 ) ) =
     ( ( ( ( 2 x. N ) + 1 ) _C N ) x.
      ( 2 x. ( ( ( 2 x. N ) + 3 ) / ( N + 2 ) ) ) ) ) $=
      ( c2 c1 caddc co cmul c3 cdiv oveq1d eqtrd wceq a1i oveq2d cfa cfv eqcomd
      cc0 wcel 2cnd nn0cnd 1cnd adddid 2t1e2 oveq2i eqtrdi mulcld addassd 2p1e3
      cbc cmin cfz 0zd cz 2z nn0zd zmulcld zaddcld peano2zd nn0red 1red nn0ge0d
      3z cle wbr 0le1 addge0d cr 2re remulcld 3re 1le2 lemulge12d le2addd elfzd
      1le3 bcval2 syl recnd addsub4d cc 2txmxeqx 3m1e2 oveq12d fveq2d nn0addcld
      2nn0 faccld nncnd 1nn0 mulcomd 1p2e3 nn0mulcld facp2 1p1e2 addcld mulassd
      cn0 nnne0d mulne0d readdcld ltp1d lelttrd ltned necomd crp 2rp divmuldivd
      0red ltaddrpd lep1d letrd addsubd divcan4d eqidd ) ADBEFGZHGZEFGZXQUKGDBH
      GZIFGZXQUKGZXTEFGZBUKGZDYABDFGZJGZHGZHGZAXSYAXQUKAXSXTDEFGZFGZYAAXSXTDFGZ
      EFGYJAXRYKEFAXRXTDEHGZFGYKADBEAUAZABCUBZAUCZUDYLDXTFUEUFUGZKAXTDEADBYMYNU
      HZYMYOUILAYIIXTFYIIMAUJNOLKAYBYAPQZYAXQULGZPQZXQPQZHGZJGZYHAXQSYAUMGTYBUU
      CMAXQSYAAUNZAXTIADBDUOTAUPNABCUQZURZIUOTAVDNUSABUUEUTABEABCVAZAVBZABCVCZS
      EVEVFAVGNVHABEXTIUUGUUHADBDVITAVJNZUUGVKZIVITAVLNZABDUUGUUJUUIEDVEVFAVMNV
      NZEIVEVFAVQNVOVPXQYAVRVSAUUCYRYEPQZUUAHGZJGZYHAUUBUUOYRJAYTUUNUUAHAYSYEPA
      YSXTBULGZIEULGZFGYEAXTIBEYQAIUULVTZYNYOWAAUUQBUURDFABWBTUUQBMYNBWCVSZUURD
      MAWDNWELWFKOAUUPYRUUAUUNHGZJGZYHAUUOUVAYRJAUUNUUAAUUNAYEABDCDWSTAWHNZWGWI
      WJAUUAAXQABECEWSTAWKNZWGWIZWJZWLOAUVBYCPQZYKYAHGZHGZUVAJGZYHAYRUVIUVAJAYR
      UVGYCEFGZYCDFGZHGZHGZUVIAYRUVLPQZUVNAUVOYRAUVLYAPAUVLXTEDFGZFGZYAAXTEDYQY
      OYMUIZUVPIXTFWMUFUGWFRAYCWSTUVOUVNMAXTEADBUVCCWNUVDWGZYCWOVSLAUVMUVHUVGHA
      UVKYKUVLYAHAUVKXTEEFGZFGYKAXTEEYQYOYOUIAUVTDXTFUVTDMAWPNOLAUVLUVQYAUVRAUV
      PIXTFUVPIMAWMNOLWEOLKAUVJUVIUUABPQZXQYEHGZHGZHGZJGZYHAUVAUWDUVIJAUUNUWCUU
      AHABWSTUUNUWCMCBWOVSOOAUWEUVIUUAUWAHGZUWBHGZJGZYHAUWDUWGUVIJAUWGUWDAUUAUW
      AUWBUVFAUWAABCWIZWJZAXQYEABEYNYOWQZABDYNYMWQZUHZWRROAUWHUVGUWFJGZUVHUWBJG
      ZHGZYHAUWPUWHAUVGUWFUVHUWBAUVGAYCUVSWIWJAUUAUWAUVFUWJUHAYKYAAXTDYQYMWQZAX
      TIYQUUSWQZUHUWMAUUAUWAUVFUWJAUUAUVEWTAUWAUWIWTXAAXQYEUWKUWLASXQASXQAXJZAS
      BXQUWSUUGABEUUGUUHXBUUIABUUGXCXDXEXFZASYEASYEUWSASBYEUWSUUGABDUUGUUJXBUUI
      ABDUUGDXGTAXHNXKXDXEXFZXAXIRAUWNYDUWOYGHAYDUWNAYDUVGYCBULGZPQZUWAHGZJGZUW
      NABSYCUMGTYDUXEMABSYCUUDAXTUUFUTUUEUUIABXTYCUUGUUKAXTEUUKUUHXBUUMAXTUUKXL
      XMVPBYCVRVSAUXDUWFUVGJAUXCUUAUWAHAUXBXQPAUXBUUQEFGXQAXTEBYQYOYNXNAUUQBEFU
      UTKLWFKOLRAUWOYKXQJGZYFHGZYGAUXGUWOAYKXQYAYEUWQUWKUWRUWLUWTUXAXIRAUXFDYFY
      FHAUXFXRXQJGDAYKXRXQJAXRYKYPRKADXQYMUWKUWTXOLAYFXPWELWELLLLLLLL $.
  $}

  ${
    $d N j $.  $d j k ph $.
    2ap1caineq.1 $e |- ( ph -> N e. ZZ ) $.
    2ap1caineq.2 $e |- ( ph -> 2 <_ N ) $.
    $( Inequality for Theorem 6.6 for AKS. (Contributed by metakunt,
       8-Jun-2024.) $)
    2ap1caineq $p |- ( ph -> ( 2 ^ ( N + 1 ) ) <
     ( ( ( 2 x. N ) + 1 ) _C N ) ) $=
      ( c2 c1 caddc co cexp cmul cbc clt wbr wceq c3 c5 cc0 a1i wcel 3ad2ant3
      vj vk cv oveq1 oveq2d oveq2 oveq1d id oveq12d breq12d c8 cdc 8lt10 eqtr4i
      eqid 5bc2eq10 eqcomi breq12i mpbi df-3 oveq2i c4 2t2e4 oveq1i 4p1e5 eqtri
      cu2 cz cle wa w3a cdiv cr 2re cn simpl 0red zred 2pos simpr ltletrd elnnz
      cn0 jca sylibr nnnn0 syl nn0red remulcld 3re readdcld wne nngt0d ltaddrpd
      nnred crp 2rp lttrd ltned redivcld 1nn0 nn0addcld reexpcld 2nn0 nn0mulcld
      necomd bccl syl2anc 0le2 2t1e2 1red nnrp rpaddcld rpcnd mulridd nnre 1le2
      rpge0d lemulge12d 2lt3 leltaddd eqbrtrd ltmuldiv2d mpbid ltmul2dd expge0d
      simp2 ltmul12ad expaddd expcld mulcomd exp1d eqidd 3eqtrd eqtrd 2np3bcnp1
      2cnd eqcomd mulcld addcld nn0cnd nncnd cc 3cn divcld 2z uzindd ) AEUAUCZF
      GHZIHZEUUHJHZFGHZUUHKHZLMEEFGHZIHZEEJHZFGHZEKHZLMZEUBUCZFGHZIHZEUUTJHZFGH
      ZUUTKHZLMZEUVAFGHZIHZEUVAJHZFGHZUVAKHZLMZEBFGHZIHZEBJHZFGHZBKHZLMUAUBEBUU
      HENZUUJUUOUUMUURLUVRUUIUUNEIUUHEFGUDUEUVRUULUUQUUHEKUVRUUKUUPFGUUHEEJUFUG
      UVRUHUIUJUUHUUTNZUUJUVBUUMUVELUVSUUIUVAEIUUHUUTFGUDUEUVSUULUVDUUHUUTKUVSU
      UKUVCFGUUHUUTEJUFUGUVSUHUIUJUUHUVANZUUJUVHUUMUVKLUVTUUIUVGEIUUHUVAFGUDUEU
      VTUULUVJUUHUVAKUVTUUKUVIFGUUHUVAEJUFUGUVTUHUIUJUUHBNZUUJUVNUUMUVQLUWAUUIU
      VMEIUUHBFGUDUEUWAUULUVPUUHBKUWAUUKUVOFGUUHBEJUFUGUWAUHUIUJUUSAEOIHZPEKHZL
      MZUUSUKFQULZLMUWDUMUKUWBUWEUWCLUKUKUWBUKUOVGUNUWCUWEUPUQURUSUWBUUOUWCUURL
      OUUNEIUTVAPUUQEKPPUUQPUOUUQVBFGHPUUPVBFGVCVDVEVFUNVDURUSRAUVFUUTVHSZEUUTV
      IMZVJZVKZEUVBJHZEUVCOGHZUUTEGHZVLHZJHZUVEJHZLMUVLUWIEUWNUVBUVEEVMSZUWIVNR
      ZUWIEUWMUWQUWIUWKUWLUWIUVCOUWIEUUTUWQUWHAUUTVMSUVFUWHUUTUWHUWFQUUTLMZVJZU
      UTVOSZUWHUWFUWRUWFUWGVPZUWHQEUUTUWHVQZUWPUWHVNRZUWHUUTUWHUWTUUTWCSUWHUWSU
      WTUWHUWFUWRUXAUWHQEUUTUXBUXCUWHUUTUXAVRQELMUWHVSRZUWFUWGVTZWAWDUUTWBZWEUU
      TWFWGZWHUXDUXEWAWDUXFWEZWOZTZWIOVMSZUWIWJRWKUWIUUTEUXJUWQWKUWHAUWLQWLUVFU
      WHQUWLUWHQUWLUXBUWHQUUTUWLUXBUXIUWHUUTEUXIUXCWKZUWHUUTUXHWMUWHUUTEUXIEWPS
      ZUWHWQRZWNWRWSXFZTWTWIUWHAUVBVMSUVFUWHEUVAUXCUWHUUTFUXGFWCSUWHXARZXBZXCTU
      WHAUVEVMSUVFUWHUVEUWHUVDWCSUWFUVEWCSUWHUVCFUWHEUUTEWCSUWHXDRUXGXEUXPXBUXA
      UUTUVDXGXHZWHTQEVIMZUWIXIRUWHAEUWNLMUVFUWHEEFJHZUWNLEUXTNUWHEEUXTEUOXJUNR
      UWHFUWMEUWHXKUWHUWKUWLUWHUVCOUWHEUUTUXCUXIWIUXKUWHWJRWKUXLUXOWTUXNUWHUWTF
      UWMLMZUXHUWTUWLFJHZUWKLMUYAUWTUYBUWLUWKLUWTUWLUWTUWLUWTUUTEUUTXLZUXMUWTWQ
      RXMZXNXOUWTUUTEUVCOUUTXPZUWPUWTVNRZUWTEUUTUYFUYEWIZUXKUWTWJRZUWTUUTEUYEUY
      FUWTUUTUYCXRFEVIMUWTXQRXSEOLMUWTXTRYAYBUWTFUWKUWLUWTXKUWTUVCOUYGUYHWKUYDY
      CYDWGYEYBTUWHAQUVBVIMUVFUWHEUVAUXCUXQUXSUWHXIRYFTAUVFUWHYGYHUWIUWJUVHUWOU
      VKLUWHAUWJUVHNUVFUWHUVHUWJUWHUVHUVBEFIHZJHZUWJUWHEUVAFUWHYQZUXPUXQYIUWHUY
      JUYIUVBJHUWJUWJUWHUVBUYIUWHEUVAUYKUXQYJUWHEFUYKUXPYJYKUWHUYIEUVBJUWHEUYKY
      LUGUWHUWJYMYNYOYRTUWHAUWOUVKNUVFUWHUVKUWOUWHUVKUVEUWNJHUWOUWHUUTUXGYPUWHU
      VEUWNUWHUVEUXRUUAUWHEUWMUYKUWHUWKUWLUWHUVCOUWHEUUTUYKUWHUUTUXHUUBZYSOUUCS
      UWHUUDRYTUWHUUTEUYLUYKYTUXOUUEYSYKYOYRTUJYDEVHSAUUFRCDUUG $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Sticks and stones
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d A f $.  $d I j x y $.  $d I j z $.  $d K f x y $.  $d K j x y $.
    $d K j z $.  $d N a $.  $d N f $.  $d X f x y $.  $d X j x y $.
    $d X j z $.  $d Y f x y $.  $d Y j x y $.  $d Y j z $.  $d a ph $.
    $d f ph $.  $d j ph $.
    sticksstones1.1 $e |- ( ph -> N e. NN0 ) $.
    sticksstones1.2 $e |- ( ph -> K e. NN0 ) $.
    sticksstones1.3 $e |- A = { f | ( f : ( 1 ... K ) --> ( 1 ... N ) /\ A. x
    e. ( 1 ... K ) A. y e. ( 1 ... K )
    ( x < y -> ( f ` x ) < ( f ` y ) ) ) } $.
    sticksstones1.4 $e |- ( ph -> X e. A ) $.
    sticksstones1.5 $e |- ( ph -> Y e. A ) $.
    sticksstones1.6 $e |- ( ph -> X =/= Y ) $.
    sticksstones1.7 $e |- I = inf ( { z e. ( 1 ... K ) |
     ( X ` z ) =/= ( Y ` z ) } , RR , < ) $.
    $( Different strictly monotone functions have different ranges.
       (Contributed by metakunt, 27-Sep-2024.) $)
    sticksstones1 $p  |- ( ph -> ran X =/= ran Y ) $=
      ( clt wcel va vj cfv wbr wo crn wne cv c1 cfz co crab cr cinf wceq a1i c0
      cfn wss w3a syl2anc wral wn nne bitri wa wfn wb wf wi feq1 breq12d imbi2d
      fveq1 2ralbidv anbi12d ralrimiva rspcdva simpld ffnd adantr mpdan syldbl2
      ex imp cn fz1ssnn sstrd sseldd mpbird fveq2 neeq12d syl mpbid nfcv elfznn
      adantl nnre ffvelcdmd wnel wfun ffund fdmd eleqtrrd fvelrn 3ad2ant3 nnred
      nfv 3ad2ant1 lttri4d simp3 sseli simprd simpl3 breq1 breq1d imbi12d breq2
      cdm breq2d rspc2v mpd cle sylib 3expa 3adantl2 ltned necomd neeq1d simpl2
      lttrd 3jaodan neneqd wrex ralnex nnel fvelrnb bitrd con1bid elnelne1 ltso
      wor fzfid ssrab2 ssfi rabeq0 ralbii cab wal mpbi spi bilani eqfnfv bicomd
      biimpd sylan2b necon3d nnssre 3jca fiinfcl eqeltrd eleq1d elrab3 ssrd w3o
      eqabb lttri2 simp2 ltnled infrefilb 3expia con3d elrabf notbii ianor imor
      3ad2ant2 sylibr eqcomd jaodan ) AGJUCZGKUCZSUDZUWBUWASUDZUEZJUFZKUFZUGZAU
      WAUWBUGZUWEAGDUHZJUCZUWJKUCZUGZDUIHUJUKZULZTZUWIAGUWOUMSUNZUWOGUWQUOZARUP
      ZAUMSUUBZUWOURTZUWOUQUGZUWOUMUSZUTUWQUWOTUWTAUUAUPAUXAUXBUXCAUWNURTUWOUWN
      USZUXAAUIHUUCUXDAUWMDUWNUUDUPZUWNUWOUUEVAZAJKUGZUXBQAUXGUXBAUWOUQJKAUWOUQ
      UOZJKUOZUXHAUWKUWLUOZDUWNVBZUXIUXHUWMVCZDUWNVBUXKUWMDUWNUUFUXLUXJDUWNUWKU
      WLVDUUGVEAUXKUXIAUXKVFZUXKUXIUXMUXIUXKUXMJUWNVGZKUWNVGZUXIUXKVHAUXNUXKAUW
      NUIIUJUKZJAUWNUXPJVIZBUHZCUHZSUDZUXRJUCZUXSJUCZSUDZVJZCUWNVBBUWNVBZAUWNUX
      PFUHZVIZUXTUXRUYFUCZUXSUYFUCZSUDZVJZCUWNVBBUWNVBZVFZUXQUYEVFFEJUYFJUOZUYG
      UXQUYLUYEUWNUXPUYFJVKUYNUYKUYDBCUWNUWNUYNUYJUYCUXTUYNUYHUYAUYIUYBSUXRUYFJ
      VNUXSUYFJVNVLVMVOVPAUYMFEUYFETZUYMAUYOUYMVHZFEUYMFUUHUOUYPFUUINUYMFEUVFUU
      JUUKUULVQZOVRZVSZVTZWAAUXOUXKAUWNUXPKAUWNUXPKVIZUXTUXRKUCZUXSKUCZSUDZVJZC
      UWNVBBUWNVBZAKETZVUAVUFVFZPAVUHVUGAUYMVUHFEKUYFKUOZUYGVUAUYLVUFUWNUXPUYFK
      VKVUIUYKVUEBCUWNUWNVUIUYJVUDUXTVUIUYHVUBUYIVUCSUXRUYFKVNUXSUYFKVNVLVMVOVP
      UYQPVRZWAWBVSZVTZWADUWNJKUUMVAUUNUUOWCUUPWDUUQWEWBAUWOUWNUMUXEAUWNWFUMUWN
      WFUSAHWGUPWFUMUSAUURUPWHZWHZUUSUMUWOSUUTVAZUVAAGUWNTZUWPUWIVHAVUPUWQUWNTA
      UWOUWNUWQUXEVUOWIAGUWQUWNUWSUVBWJZUWMUWIDGUWNUWJGUOUWKUWAUWLUWBUWJGJWKUWJ
      GKWKWLUVCWMWNZAUWAUMTZUWBUMTZUWIUWEVHAUXPUMUWAAUAUXPUMAUAXHUAUXPWOUAUMWOA
      UAUHZUXPTZVVAUMTZAVVBVFVVAWFTZVVCVVBVVDAVVAIWPWQVVAWRWMWDUVDZAUWNUXPGJUYS
      VUQWSWIZAUXPUMUWBVVEAUWNUXPGKVUKVUQWSWIZUWAUWBUVGVAWNAUWCUWHUWDAUWCVFZUWA
      UWFTZUWAUWGWTZUWHVVHJXAZGJXSZTZVVIAVVKUWCAUWNUXPJUYSXBWAAVVMUWCAGUWNVVLVU
      QAUWNUXPJUYSXCXDWAGJXEVAVVHUBUHZKUCZUWAUOZVCZUBUWNVBZVVJVVHVVQUBUWNVVHVVN
      UWNTZVFVVOUWAAUWCVVSVVOUWAUGZAUWCVVSUTZVVNGSUDZVVNGUOZGVVNSUDZUVEZVVTVWAV
      VNGVWAVVNVVSAVVNWFTZUWCVVNHWPZXFXGAUWCGUMTZVVSAUWNUMGVUMVUQWIZXIXJVWAVWBV
      VTVWCVWDVWAVWBVFZVVOUWAVWAVVOUMTZVWBVWAVVOUXPTZVWKVWAUWNUXPVVNKAUWCVUAVVS
      VUKXIAUWCVVSXKZWSVWLVVOWFTVWKUXPWFVVOIWGZXLVVOWRWMWMZWAVWJVVOUWASUDVVNJUC
      ZUWASUDZVWAVWBVWQVWJUYEVWBVWQVJZVWAUYEVWBAUWCUYEVVSAUXQUYEUYRXMZXIWAVWJVV
      SVUPUYEVWRVJAUWCVVSVWBXNVWAVUPVWBAUWCVUPVVSVUQXIZWAUYDVWRVVNUXSSUDZVWPUYB
      SUDZVJBCVVNGUWNUWNUXRVVNUOZUXTVXAUYCVXBUXRVVNUXSSXOZVXCUYAVWPUYBSUXRVVNJW
      KXPXQUXSGUOZVXAVWBVXBVWQUXSGVVNSXRZVXEUYBUWAVWPSUXSGJWKXTXQYAVAYBWCVWJVVO
      VWPUWASVWJVWPVVOAVVSVWBVWPVVOUOZUWCAVVSVWBVXGAVVSVWBUTZVVSVXGAVVSVWBUVHVX
      HVVSVFVWPVVOUGZVCZVXGVXHVVSVXJVXHVVSVCVXJUEZVVSVXJVJVXHVVNUWOTZVCZVXKVXHG
      VVNYCUDZVCZVXMVXHVWBVXOAVVSVWBXKVXHVVNGVXHVVNVVSAVWFVWBVWGUVQXGAVVSVWHVWB
      VWIXIUVIWNVXHVXLVXNVXHVXLVXNVXHVXLVFZVXNUWQVVNYCUDZVXHVXLVXQVXHUXCUXAVXLV
      XQVJAVVSUXCVWBVUNXIAVVSUXAVWBUXFXIUXCUXAVXLVXQVVNUWOUVJUVKVAWEVXPGUWQVVNY
      CUWRVXPRUPXPWJWDUVLYBVXMVVSVXIVFZVCVXKVXLVXRUWMVXIDVVNUWNDVVNWODUWNWOVXID
      XHUWJVVNUOUWKVWPUWLVVOUWJVVNJWKUWJVVNKWKWLUVMUVNVVSVXIUVOVEYDVVSVXJUVPUVR
      WEVWPVVOVDYDWBYEZYFUVSXPWJYGVWAVWCVFZVVTUWBUWAUGZVXTUWAUWBVWAUWIVWCAUWCUW
      IVVSVURXIWAYHVWCVVTVYAVHVWAVWCVVOUWBUWAVVNGKWKYIWQWJVWAVWDVFZUWAVVOVYBUWA
      VVOVWAVUSVWDAUWCVUSVVSVVFXIWAZVYBUWAUWBVVOVYCVWAVUTVWDAUWCVUTVVSVVGXIWAVW
      AVWKVWDVWOWAAUWCVVSVWDYJVWAVWDUWBVVOSUDZVYBVUFVWDVYDVJZVWAVUFVWDAUWCVUFVV
      SAVUAVUFVUJXMZXIWAVYBVUPVVSVUFVYEVJVWAVUPVWDVWTWAVWAVVSVWDVWMWAVUEVYEGUXS
      SUDZUWBVUCSUDZVJBCGVVNUWNUWNUXRGUOZUXTVYGVUDVYHUXRGUXSSXOZVYIVUBUWBVUCSUX
      RGKWKXPXQUXSVVNUOZVYGVWDVYHVYDUXSVVNGSXRZVYKVUCVVOUWBSUXSVVNKWKXTXQYAVAYB
      WCYKYGYHYLWBYEYMVQAVVRVVJVHUWCAVVRVVPUBUWNYNZVCZVVJVVRVYNVHAVVPUBUWNYOUPA
      VVJVYMAVVJVCZUWAUWGTZVYMVYOVYPVHAUWAUWGYPUPAUXOVYPVYMVHVULUBUWNUWAKYQWMYR
      YSYRWAWNUWAUWFUWGYTVAAUWDVFZUWBUWGTZUWBUWFWTZUWHVYQKXAZGKXSZTZVYRAVYTUWDA
      UWNUXPKVUKXBWAAWUBUWDAGUWNWUAVUQAUWNUXPKVUKXCXDWAGKXEVAVYQVWPUWBUOZVCZUBU
      WNVBZVYSVYQWUDUBUWNVYQVVSVFVWPUWBAUWDVVSVWPUWBUGZAUWDVVSUTZVWEWUFWUGVVNGW
      UGVVNVVSAVWFUWDVWGXFXGAUWDVWHVVSVWIXIXJWUGVWBWUFVWCVWDWUGVWBVFZVWPUWBWUGV
      WPUMTZVWBWUGVWPWUGVWPUXPTVWPWFTWUGUWNUXPVVNJAUWDUXQVVSUYSXIAUWDVVSXKZWSUX
      PWFVWPVWNXLWMXGZWAWUHVWPUWBSUDVVOUWBSUDZWUGVWBWULWUHVUFVWBWULVJZWUGVUFVWB
      AUWDVUFVVSVYFXIWAWUHVVSVUPVUFWUMVJAUWDVVSVWBXNWUGVUPVWBAUWDVUPVVSVUQXIZWA
      VUEWUMVXAVVOVUCSUDZVJBCVVNGUWNUWNVXCUXTVXAVUDWUOVXDVXCVUBVVOVUCSUXRVVNKWK
      XPXQVXEVXAVWBWUOWULVXFVXEVUCUWBVVOSUXSGKWKXTXQYAVAYBWCWUHVWPVVOUWBSAVVSVW
      BVXGUWDVXSYFXPWJYGWUGVWCVFZWUFUWIWUPUWBUWAWUPUWBUWAWUGVUTVWCAUWDVUTVVSVVG
      XIZWAAUWDVVSVWCYJYGYHVWCWUFUWIVHWUGVWCVWPUWAUWBVVNGJWKYIWQWJWUGVWDVFZUWBV
      WPWURUWBVWPWUGVUTVWDWUQWAZWURUWBUWAVWPWUSWUGVUSVWDAUWDVUSVVSVVFXIWAWUGWUI
      VWDWUKWAAUWDVVSVWDYJWUGVWDUWAVWPSUDZWURUYEVWDWUTVJZWUGUYEVWDAUWDUYEVVSVWS
      XIWAWURVUPVVSUYEWVAVJWUGVUPVWDWUNWAWUGVVSVWDWUJWAUYDWVAVYGUWAUYBSUDZVJBCG
      VVNUWNUWNVYIUXTVYGUYCWVBVYJVYIUYAUWAUYBSUXRGJWKXPXQVYKVYGVWDWVBWUTVYLVYKU
      YBVWPUWASUXSVVNJWKXTXQYAVAYBWCYKYGYHYLWBYEYMVQAWUEVYSVHUWDAWUEWUCUBUWNYNZ
      VCZVYSWUEWVDVHAWUCUBUWNYOUPAVYSWVCAVYSVCZUWBUWFTZWVCWVEWVFVHAUWBUWFYPUPAU
      XNWVFWVCVHUYTUBUWNUWBJYQWMYRYSYRWAWNVYRVYSVFUWGUWFUWBUWGUWFYTYHVAUVTWB $.
  $}

  ${
    $d A a b z $.  $d A f i j z $.  $d B z $.  $d F i j $.  $d K a b x y $.
    $d K f x y $.  $d K r s $.  $d N a $.  $d N f $.  $d a b ph z $.
    $d f i j ph z $.  $d i j r s $.  $d i j r x y $.  $d x y z $.
    sticksstones2.1 $e |- ( ph -> N e. NN0 ) $.
    sticksstones2.2 $e |- ( ph -> K e. NN0 ) $.
    sticksstones2.3 $e |- B = { a e. ~P ( 1 ... N ) | ( # ` a ) = K } $.
    sticksstones2.4 $e |- A = { f | ( f : ( 1 ... K ) --> ( 1 ... N ) /\ A. x
    e. ( 1 ... K ) A. y e. ( 1 ... K )
    ( x < y -> ( f ` x ) < ( f ` y ) ) ) } $.
    sticksstones2.5 $e |- F = ( z e. A |-> ran z ) $.
    $( The range function on strictly monotone functions with finite domain and
       codomain is an injective mapping onto ` K ` -elemental sets.
       (Contributed by metakunt, 27-Sep-2024.) $)
    sticksstones2 $p  |- ( ph -> F : A -1-1-> B ) $=
      ( cfv wceq wcel clt vi vj vb vs vr wf cv wi wral wa wf1 crn chash cfz cpw
      c1 co crab fveqeq2 cfn fzfid wbr eleq1w feq1 fveq1 breq12d imbi2d ralbidv
      anbi12d bibi12d cab wal eqabb mpbi spi chvarvv bilani simpld frnd sselpwd
      wb wfn hashfn syl cn0 adantr hashfz1 eqtrd eqcomd w3a wne wo cr cn elfznn
      3ad2ant3 nnred adantl lttri2 syl2anc 3adant3 simp3 ffvelcdmd simprd simpr
      ffnd breq1 fveq2 breq1d imbi12d breq2 breq2d rspc2v mpd ffvelcdmda necomd
      imp ltned jaodan sylbid necon4d ralrimiva 3expa jca dff13 sylibr hashf1rn
      elrabd eleq2i a1i mpbird fmptd cinf 3ad2ant1 simpl2 simpl3 rneqd 2ralbidv
      ex fvmptd neeq12d cbvrabv infeq1i sticksstones1 cmpt 3adant2 3netr4d ) AE
      FHUFZUAUGZHQZUBUGZHQZRUUIUUKRUHZUBEUIZUAEUIZUJEFHUKAUUHUUOADEDUGZULZFHAUU
      PESZUJZUUQFSZUUQKUGZUMQIRZKUPJUNUQZUOZURZSZUUSUVBUUQUMQZIRKUUQUVDUVAUUQIU
      MUSUUSUUQUVCUTUUSUPJVAUUSUPIUNUQZUVCUUPUUSUVHUVCUUPUFZBUGZCUGZTVBZUVJUUPQ
      ZUVKUUPQZTVBZUHZCUVHUIZBUVHUIZUURUVIUVRUJZAGUGZESZUVHUVCUVTUFZUVLUVJUVTQZ
      UVKUVTQZTVBZUHZCUVHUIZBUVHUIZUJZWAZUURUVSWAGDUVTUUPRZUWAUURUWIUVSGDEVCUWK
      UWBUVIUWHUVRUVHUVCUVTUUPVDUWKUWGUVQBUVHUWKUWFUVPCUVHUWKUWEUVOUVLUWKUWCUVM
      UWDUVNTUVJUVTUUPVEUVKUVTUUPVEVFVGVHVHVIVJUWJGEUWIGVKRUWJGVLOUWIGEVMVNVOZV
      PVQZVRZVSVTUUSIUVGUUSIUUPUMQZUVGUUSUWOIUUSUWOUVHUMQZIUUSUUPUVHWBUWOUWPRUU
      SUVHUVCUUPUWNXFUVHUUPWCWDUUSIWESZUWPIRAUWQUURMWFIWGWDWHWIUUSUVHUTSUVHUVCU
      UPUKZUWOUVGRUUSUPIVAUUSUVIUVAUUPQZUCUGZUUPQZRUVAUWTRUHZUCUVHUIZKUVHUIZUJU
      WRUUSUVIUXDUWNUUSUXCKUVHAUURUVAUVHSZUXCAUURUXEWJZUXBUCUVHUXFUWTUVHSZUJZUV
      AUWTUWSUXAUXHUVAUWTWKZUVAUWTTVBZUWTUVATVBZWLZUWSUXAWKZUXHUVAWMSZUWTWMSZUX
      IUXLWAUXFUXNUXGUXFUVAUXEAUVAWNSUURUVAIWOWPWQWFUXGUXOUXFUXGUWTUWTIWOWQWRUV
      AUWTWSWTUXHUXLUXMUXHUXJUXMUXKUXHUXJUJZUWSUXAUXPUWSUXPUWSUVCSZUWSWNSUXHUXQ
      UXJUXFUXQUXGUXFUVHUVCUVAUUPAUURUVIUXEUWNXAZAUURUXEXBZXCWFWFUWSJWOWDWQUXHU
      XJUWSUXATVBZUXHUVRUXJUXTUHZUXFUVRUXGAUURUVRUXEUUSUVIUVRUWMXDXAWFZUXHUXEUX
      GUVRUYAUHUXFUXEUXGUXSWFZUXFUXGXEZUVPUYAUVAUVKTVBZUWSUVNTVBZUHBCUVAUWTUVHU
      VHUVJUVARZUVLUYEUVOUYFUVJUVAUVKTXGUYGUVMUWSUVNTUVJUVAUUPXHXIXJUVKUWTRZUYE
      UXJUYFUXTUVKUWTUVATXKUYHUVNUXAUWSTUVKUWTUUPXHXLXJXMWTXNXQXRUXHUXKUJZUXAUW
      SUYIUXAUWSUXHUXAWMSUXKUXHUXAUXHUXAUVCSUXAWNSUXFUVHUVCUWTUUPUXRXOUXAJWOWDW
      QWFUXHUXKUXAUWSTVBZUXHUVRUXKUYJUHZUYBUXHUXGUXEUVRUYKUHUYDUYCUVPUYKUWTUVKT
      VBZUXAUVNTVBZUHBCUWTUVAUVHUVHUVJUWTRZUVLUYLUVOUYMUVJUWTUVKTXGUYNUVMUXAUVN
      TUVJUWTUUPXHXIXJUVKUVARZUYLUXKUYMUYJUVKUVAUWTTXKUYOUVNUWSUXATUVKUVAUUPXHX
      LXJXMWTXNXQXRXPXSYSXTYAYBYCYBYDKUCUVHUVCUUPYEYFUVHUVCUUPUTYGWTWHWIYHUUTUV
      FWAUUSFUVEUUQNYIYJYKPYLAUUNUAEAUUIESZUJZUUMUBEAUYPUUKESZUUMAUYPUYRWJZUUIU
      UKUUJUULUYSUUIUUKWKZUUJUULWKUYSUYTUJZUUIULZUUKULZUUJUULVUABCUDEGUEUGZUUIQ
      ZVUDUUKQZWKZUEUVHURZWMTYMIJUUIUUKUYSJWESZUYTAUYPVUIUYRLYNWFUYSUWQUYTAUYPU
      WQUYRMYNWFOAUYPUYRUYTYOZAUYPUYRUYTYPZUYSUYTXEWMVUHUDUGZUUIQZVULUUKQZWKZUD
      UVHURTVUGVUOUEUDUVHVUDVULRVUEVUMVUFVUNVUDVULUUIXHVUDVULUUKXHUUAUUBUUCUUDV
      UADUUIUUQVUBEHUVDHDEUUQUUERVUAPYJZVUAUUPUUIRZUJUUPUUIVUAVUQXEYQVUJVUAVUBU
      VCUTVUAUPJVAVUAUVHUVCUUIUYSUVHUVCUUIUFZUYTAUYPVURUYRUYQVURUVLUVJUUIQZUVKU
      UIQZTVBZUHZCUVHUIBUVHUIZUYPVURVVCUJZAUWJUYPVVDWAGUAUVTUUIRZUWAUYPUWIVVDGU
      AEVCVVEUWBVURUWHVVCUVHUVCUVTUUIVDVVEUWFVVBBCUVHUVHVVEUWEVVAUVLVVEUWCVUSUW
      DVUTTUVJUVTUUIVEUVKUVTUUIVEVFVGYRVIVJUWLVPVQVRXAWFVSVTYTVUADUUKUUQVUCEHUV
      DVUPVUAUUPUUKRZUJUUPUUKVUAVVFXEYQVUKUYSVUCUVDSUYTUYSVUCUVCUTAUYPUVCUTSUYR
      AUPJVAYNUYSUVHUVCUUKAUYRUVHUVCUUKUFZUYPAUYRUJVVGUVLUVJUUKQZUVKUUKQZTVBZUH
      ZCUVHUIBUVHUIZUYRVVGVVLUJZAUWJUYRVVMWAGUBUVTUUKRZUWAUYRUWIVVMGUBEVCVVNUWB
      VVGUWHVVLUVHUVCUVTUUKVDVVNUWFVVKBCUVHUVHVVNUWEVVJUVLVVNUWCVVHUWDVVITUVJUV
      TUUKVEUVKUVTUUKVEVFVGYRVIVJUWLVPVQVRUUFVSVTWFYTUUGYSYAYCYBYBYDUAUBEFHYEYF
      $.
  $}

  ${
    $d A a w $.  $d A f v z $.  $d B c w $.  $d B v w x y $.  $d B v x y z $.
    $d F v w $.  $d K a x y $.  $d K f x y $.  $d N a $.  $d N f $.
    $d a ph w x y $.  $d a ph x y z $.  $d c ph w $.  $d f ph v x y z $.
    sticksstones3.1 $e |- ( ph -> N e. NN0 ) $.
    sticksstones3.2 $e |- ( ph -> K e. NN0 ) $.
    sticksstones3.3 $e |- B = { a e. ~P ( 1 ... N ) | ( # ` a ) = K } $.
    sticksstones3.4 $e |- A = { f | ( f : ( 1 ... K ) --> ( 1 ... N ) /\ A. x
    e. ( 1 ... K ) A. y e. ( 1 ... K )
    ( x < y -> ( f ` x ) < ( f ` y ) ) ) } $.
    sticksstones3.5 $e |- F = ( z e. A |-> ran z ) $.
    $( The range function on strictly monotone functions with finite domain and
       codomain is an surjective mapping onto ` K ` -elemental sets.
       (Contributed by metakunt, 28-Sep-2024.) $)
    sticksstones3 $p  |- ( ph -> F : A -onto-> B ) $=
      ( wral wa wcel clt vw vv vc wfo cfv wceq wrex wf1 sticksstones2 ccnv wfun
      wf cv df-f1 biimpi simpld syl wex c1 chash cfz co wiso wor cfn cr wss w3a
      cn crab eleq2i bilani fveqeq2 elrab sylib elpwid sseld 3impa elfznn nnred
      cpw imp 3expa ex ssrdv ltso mpi fzfid ssfid fz1iso syl2anc wbr wi cab cvv
      soss wf1o wb df-isom 3ad2ant3 simprd f1oeq2d biimpd 3adant3 mpd f1of ffnd
      oveq2 ovexd fnexd fss biimp a1i ralimdva adantr oveq2d raleqdv raleqbidva
      mpbid jca feq1 fveq1 breq12d imbi2d 2ralbidv anbi12d elabd crn cmpt simpr
      sylibr rneqd rnexg fvmptd 3ad2ant1 wfn dff1o2 simp3d eqtrd eqcomd eximdv
      df-rex ralrimiva dffo3 mpbird ) AEFHUDZEFHULZUAUMZUBUMZHUEZUFZUBEUGZUAFQZ
      RZAUUGUUMAEFHUHZUUGABCDEFGHIJKLMNOPUIUUOUUGHUJUKZUUOUUGUUPREFHUNUOUPUQAUU
      LUAFAUUHFSZRZUUIESZUUKRZUBURZUULUURUSUUHUTUEZVAVBZUUHTTUUIVCZUBURZUVAUURU
      UHTVDZUUHVESUVEUURUUHVFVGZUVFUURUCUUHVFUURUCUMZUUHSZUVHVFSZAUUQUVIUVJAUUQ
      UVIVHZUVHUVKUVHUSJVAVBZSZUVHVISAUUQUVIUVMUURUVIUVMUURUUHUVLUVHUURUUHUVLUU
      RUUHUVLWAZSZUVBIUFZUURUUHKUMZUTUEIUFZKUVNVJZSZUVOUVPRUUQUVTAFUVSUUHNVKVLU
      VRUVPKUUHUVNUVQUUHIUTVMVNVOZUPVPZVQWBVRUVHJVSUQVTWCWDWEUVGVFTVDUVFWFUUHVF
      TWPWGUQUURUVLUUHUURUSJWHUWBWIUUHTUBWJWKUURUVDUUTUBUURUVDUUTAUUQUVDUUTAUUQ
      UVDVHZUUSUUKUWCUUIUSIVAVBZUVLGUMZULZBUMZCUMZTWLZUWGUWEUEZUWHUWEUEZTWLZWMZ
      CUWDQBUWDQZRZGWNZSUUSUWCUWOUWDUVLUUIULZUWIUWGUUIUEZUWHUUIUEZTWLZWMZCUWDQZ
      BUWDQZRGUUIWOUWCUWDUUIWOUWCUWDUUHUUIUWCUWDUUHUUIWQZUWDUUHUUIULZUWCUVCUUHU
      UIWQZUXDUWCUXFUWIUWTWRZCUVCQZBUVCQZUVDAUXFUXIRZUUQUVDUXJBCUVCUUHTTUUIWSUO
      WTZUPAUUQUXFUXDWMUVDUURUXFUXDUURUVPUXFUXDWRUURUVOUVPUWAXAZUVPUVCUWDUUHUUI
      UVBIUSVAXHXBUQXCXDXEZUWDUUHUUIXFUQZXGUWCUSIVAXIXJUWCUWQUXCUWCUXEUUHUVLVGZ
      UWQUXNAUUQUXOUVDUWBXDUWDUUHUVLUUIXKWKUWCUXACUVCQZBUVCQZUXCUWCUXIUXQUWCUXF
      UXIUXKXAUWCUXHUXPBUVCUWCUWGUVCSZRZUXGUXACUVCUXGUXAWMUXSUWHUVCSRUWIUWTXLXM
      XNXNXEUWCUXPUXBBUVCUWDUWCUVBIUSVAAUUQUVDUVPUURUVPUVDUXLXOVRXPZUWCUXPUXBWR
      UXRUWCUXACUVCUWDUXTXQXOXRXSXTUWEUUIUFZUWFUWQUWNUXCUWDUVLUWEUUIYAUYAUWMUXA
      BCUWDUWDUYAUWLUWTUWIUYAUWJUWRUWKUWSTUWGUWEUUIYBUWHUWEUUIYBYCYDYEYFYGEUWPU
      UIOVKYKZUWCUUJUUHUWCUUJUUIYHZUUHUWCUUSUUJUYCUFZUYBAUUQUUSUYDWMUVDAUUSUYDA
      UUSRZDUUIDUMZYHZUYCEHWOHDEUYGYIUFUYEPXMUYEUYFUUIUFZRUYFUUIUYEUYHYJYLAUUSY
      JZUYEUUSUYCWOSUYIUUIEYMUQYNWDYOXEUWCUXDUYCUUHUFZUXMUXDUUIUWDYPZUUIUJUKZUY
      JUXDUYKUYLUYJVHUWDUUHUUIYQUOYRUQYSYTXTWCWDUUAXEUUKUBEUUBYKUUCXTUUFUUNWRAU
      BUAEFHUUDXMUUE $.
  $}

  ${
    $d A a p $.  $d A f p $.  $d A g p $.  $d B g p $.  $d B p x y $.
    $d K a x y $.  $d K f x y $.  $d N a $.  $d N f $.  $d a p ph x y $.
    $d f p ph x y $.  $d g p ph $.
    sticksstones4.1 $e |- ( ph -> N e. NN0 ) $.
    sticksstones4.2 $e |- ( ph -> K e. NN0 ) $.
    sticksstones4.3 $e |- B = { a e. ~P ( 1 ... N ) | ( # ` a ) = K } $.
    sticksstones4.4 $e |- A = { f | ( f : ( 1 ... K ) --> ( 1 ... N ) /\ A. x
    e. ( 1 ... K ) A. y e. ( 1 ... K )
    ( x < y -> ( f ` x ) < ( f ` y ) ) ) } $.
    $( Equinumerosity lemma for sticks and stones.  (Contributed by metakunt,
       28-Sep-2024.) $)
    sticksstones4 $p  |- ( ph -> A ~~ B ) $=
      ( vg vp cv cvv c1 wcel cfn wf1o wex cen wbr crn cmpt wf1 wa sticksstones2
      wfo eqid sticksstones3 jca df-f1o sylibr cfz co wf clt cfv wral cab simpl
      wi wss a1i ss2abdv fzfid mapex syl2anc ssexg eleq1i mptexd f1oeq1 biimprd
      wceq adantl spcimedv mpd bren ) ADENPZUAZNUBZDEUCUDADEODOPUEZUFZUAZWCADEW
      EUGZDEWEUJZUHWFAWGWHABCODEFWEGHIJKLMWEUKZUIABCODEFWEGHIJKLMWIULUMDEWEUNUO
      AWBWFNWEQAODWDQARGUPUQZRHUPUQZFPZURZBPZCPZUSUDWNWLUTWOWLUTUSUDVDCWJVABWJV
      AZUHZFVBZQSZDQSAWRWMFVBZVEWTQSZWSAWQWMFWQWMVDAWMWPVCVFVGAWJTSWKTSXAARGVHA
      RHVHWJWKTTFVIVJWRWTQVKVJDWRQMVLUOVMWAWEVPZWFWBVDAXBWBWFDEWAWEVNVOVQVRVSDE
      NVTUO $.
  $}

  ${
    $d A f $.  $d A s $.  $d K f x y $.  $d K s x y $.  $d N f x y $.
    $d N s x y $.  $d f ph x y $.  $d ph s x y $.
    sticksstones5.1 $e |- ( ph -> N e. NN0 ) $.
    sticksstones5.2 $e |- ( ph -> K e. NN0 ) $.
    sticksstones5.3 $e |- A = { f | ( f : ( 1 ... K ) --> ( 1 ... N ) /\ A. x
    e. ( 1 ... K ) A. y e. ( 1 ... K )
    ( x < y -> ( f ` x ) < ( f ` y ) ) ) } $.
    $( Count the number of strictly monotonely increasing functions on finite
       domains and codomains.  (Contributed by metakunt, 28-Sep-2024.) $)
    sticksstones5 $p  |- ( ph -> ( # ` A ) = ( N _C K ) ) $=
      ( vs chash cfv wceq c1 co cbc syl wcel eqtrd cv cfz cpw crab cen wbr eqid
      sticksstones4 hasheni cfn cz fzfid nn0zd hashbc syl2anc eqcomd cn0 oveq1d
      hashfz1 ) ADLMZKUALMFNKOGUBPZUCUDZLMZGFQPZADVBUEUFUTVCNABCDVBEFGKHIVBUGJU
      HDVBUIRAVCVALMZFQPZVDAVFVCAVAUJSFUKSVFVCNAOGULAFIUMKVAFUNUOUPAVEGFQAGUQSV
      EGNHGUSRURTT $.
  $}

  ${
    $d G x $.  $d K x $.  $d X i x $.  $d Y i x $.  $d i ph x $.
    sticksstones6.1 $e |- ( ph -> N e. NN0 ) $.
    sticksstones6.2 $e |- ( ph -> K e. NN0 ) $.
    sticksstones6.3 $e |- ( ph -> G : ( 1 ... ( K + 1 ) ) --> NN0 ) $.
    sticksstones6.4 $e |- ( ph -> X e. ( 1 ... K ) ) $.
    sticksstones6.5 $e |- ( ph -> Y e. ( 1 ... K ) ) $.
    sticksstones6.6 $e |- ( ph -> X < Y ) $.
    sticksstones6.7 $e |- F = ( x e. ( 1 ... K ) |-> ( x + sum_ i e.
    ( 1 ... x ) ( G ` i ) ) ) $.
    $( Function induces an order isomorphism for sticks and stones theorem.
       (Contributed by metakunt, 1-Oct-2024.) $)
    sticksstones6 $p |- ( ph -> ( F ` X ) < ( F ` Y ) ) $=
      ( c1 co wcel adantr cfz cv cfv csu caddc clt cn elfznn syl nnred fzfid wa
      cn0 1zzd cz nn0zd peano2zd adantl nnzd nnge1d cle wbr elfzle2 letrd lep1d
      zred elfzd wf simpr ffvelcdmd adantlr mpdan fsumnn0cl nn0red elfzelz 1red
      readdcld ltp1d ltled elfzle1 fsumrecl cc0 nn0ge0d addge01d mpbid ltleaddd
      cr fsumge0 cmpt a1i oveq2d sumeq1d oveq12d nnnn0d nn0addcld fvmptd eqcomd
      wceq cin c0 fzdisj cun fzsplit recnd fsumsplit eqtrd 3brtr3d ) AHQHUARZCU
      BZEUCZCUDZUERZIXKHQUERZIUARZXJCUDZUERZUERZHDUCZIDUCZUFAHXKIXPAHAHQFUARZSZ
      HUGSZMHFUHUIZUJZAXKAXHXJCAQHUKAXIXHSZULZXIQFQUERZUARZSZXJUMSZYFXIQYGYFUNY
      FFAFUOSZYEAFKUPZTZUQZYFXIYEXIUGSAXIHUHURZUSYFXIYOUTYFXIFYGYFXIYOUJZYFFYMV
      FZYFYGYNVFYFXIHFYPYFHAYBYEYCTUJYQYEXIHVAVBAXIQHVCURAHFVAVBZYEAYAYRMHQFVCU
      ITVDYFFYQVEVDVGAYIYJYEAYIULYHUMXIEAYHUMEVHYILTAYIVIVJZVKVLVMZVNZAIAIXTSZI
      UGSNIFUHUIZUJZAXKXOUUAAXNXJCAXMIUKZAXIXNSZULZXJUUGYIYJUUGXIQYGUUGUNUUGFAY
      KUUFYLTZUQZUUFXIUOSZAXIXMIVOURZUUGQXMXIUUGVPZUUGHQAHWGSUUFYDTUULVQUUGXIUU
      KVFZAQXMVAVBUUFAQHXMAVPZYDAHQYDUUNVQZAHYCUTZAHXMYDUUOAHYDVRZVSVDTUUFXMXIV
      AVBAXIXMIVTURVDUUGXIIYGUUMAIWGSZUUFUUDTZUUGYGUUIVFZUUFXIIVAVBZAXIXMIVCURU
      UGIFYGUUSUUGFUUHVFZUUTAIFVAVBZUUFAUUBUVCNIQFVCUIZTUUGFUVBVEVDVDVGAYIYJUUF
      YSVKVLZVNZWAZVQOAWBXOVAVBXKXPVAVBAXNXJCUUEUVFUUGXJUVEWCWHAXKXOUUAUVGWDWEW
      FAXRXLABHBUBZQUVHUARZXJCUDZUERZXLXTDUMDBXTUVKWIWRAPWJZAUVHHWRZULZUVHHUVJX
      KUEAUVMVIZUVNUVIXHXJCUVNUVHHQUAUVOWKWLWMMAHXKAHYCWNZYTWOWPWQAXSXQAXSIQIUA
      RZXJCUDZUERZXQABIUVKUVSXTDUMUVLAUVHIWRZULZUVHIUVJUVRUEAUVTVIZUWAUVIUVQXJC
      UWAUVHIQUAUWBWKWLWMNAIUVRAIUUCWNZAUVQXJCAQIUKZAXIUVQSZULZYIYJUWFXIQYGUWFU
      NUWFFAYKUWEYLTZUQZUWEUUJAXIQIVOURZUWEQXIVAVBAXIQIVTURUWFXIIYGUWFXIUWIVFAU
      URUWEUUDTZUWFYGUWHVFZUWEUVAAXIQIVCURUWFIFYGUWJUWFFUWGVFZUWKAUVCUWEUVDTUWF
      FUWLVEVDVDVGAYIYJUWEYSVKVLZVMWOWPAUVRXPIUEAXHXNXJUVQCAHXMUFVBXHXNWSWTWRUU
      QQHXMIXAUIAHUVQSUVQXHXNXBWRAHQIAUNAIUWCUPAHUVPUPUUPAHIYDUUDOVSVGHQIXCUIUW
      DUWFXJUWFXJUWMVNXDXEWKXFWQXG $.
  $}

  ${
    $d G x $.  $d K i x $.  $d X i x $.  $d i ph x $.
    sticksstones7.1 $e |- ( ph -> N e. NN0 ) $.
    sticksstones7.2 $e |- ( ph -> K e. NN0 ) $.
    sticksstones7.3 $e |- ( ph -> G : ( 1 ... ( K + 1 ) ) --> NN0 ) $.
    sticksstones7.4 $e |- ( ph -> X e. ( 1 ... K ) ) $.
    sticksstones7.5 $e |- F = ( x e. ( 1 ... K ) |-> ( x + sum_ i e.
    ( 1 ... x ) ( G ` i ) ) ) $.
    sticksstones7.6 $e |- ( ph -> sum_ i e. ( 1 ... ( K + 1 ) )
    ( G ` i ) = N ) $.
    $( Closure property of sticks and stones function.  (Contributed by
       metakunt, 1-Oct-2024.) $)
    sticksstones7 $p |- ( ph -> ( F ` X ) e. ( 1 ... ( N + K ) ) ) $=
      ( c1 co caddc wcel cle wbr cfv cfz cv csu cn0 cmpt wceq a1i simpr sumeq1d
      wa oveq2d oveq12d cn elfznn syl nnnn0d fzfid 1zzd cz nn0zd adantr elfzelz
      peano2zd adantl elfzle1 zred cr nnred elfzle2 nn0red readdcld lep1d letrd
      1red elfzd ffvelcdmda mpdan fsumnn0cl nn0addcld fvmptd zaddcld eqid 1p0e1
      cc0 eqtr4i 0red nnge1d nn0ge0d le2addd eqbrtrd adantlr addge01d mpbid clt
      wf cin c0 ltp1d fzdisj cun fzsplit nn0cn fsumsplit breqtrrd eqcomd nn0cnd
      cc addcomd breqtrd eqeltrd ) AHDUAHOHUBPZCUCZEUAZCUDZQPZOGFQPZUBPABHBUCZO
      XRUBPZXNCUDZQPZXPOFUBPZDUEDBYBYAUFUGAMUHAXRHUGZUKZXRHXTXOQAYCUIZYDXSXLXNC
      YDXRHOUBYEULUJUMLAHXOAHAHYBRZHUNRLHFUOUPZUQZAXLXNCAOHURAXMXLRZUKZXMOFOQPZ
      UBPZRZXNUERZYJXMOYKYJUSYJFAFUTRYIAFJVAZVBVDZYIXMUTRZAXMOHVCVEZYIOXMSTAXMO
      HVFVEYJXMHYKYJXMYRVGAHVHRZYIAHYGVIZVBYJYKYPVGYIXMHSTAXMOHVJVEAHYKSTYIAHFY
      KYTAFJVKZAFOUUAAVOZVLAYFHFSTLHOFVJUPZAFUUAVMVNZVBVNVPYJYLUEXMEAYLUEEWPYIK
      VBVQVRVSZVTZWAAXPOXQAUSZAGFAGIVAYOWBAXPUUFVAAOOWEQPZXPSOUUHUGAOOUUHOWCWDW
      FUHAOWEHXOUUBAWGYTAXOUUEVKZAHYGWHZAXOUUEWIWJWKAXPFGQPXQSAHXOFGYTUUIUUAAGI
      VKUUCAXOYLXNCUDZGSAXOXOHOQPZYKUBPZXNCUDZQPZUUKSAWEUUNSTXOUUOSTAUUNAUUMXNC
      AUULYKURAXMUUMRZUKZYMYNUUQXMOYKAOUTRUUPUUGVBAYKUTRUUPAFYOVDZVBUUPYQAXMUUL
      YKVCVEZUUQOUULXMAOVHRUUPUUBVBZUUQHOAYSUUPYTVBZUUTVLZUUQXMUUSVGUUQOHUULUUT
      UVAUVBAOHSTUUPUUJVBUUQHUVAVMVNUUPUULXMSTAXMUULYKVFVEVNUUPXMYKSTAXMUULYKVJ
      VEVPAYMYNUUPAYLUEXMEKVQZWLVRVSZWIAXOUUNUUIAUUNUVDVKWMWNAXLUUMXNYLCAHUULWO
      TXLUUMWQWRUGAHYTWSOHUULYKWTUPAHYLRYLXLUUMXAUGAHOYKUUGUURAHYHVAUUJUUDVPHOY
      KXBUPAOYKURAYMUKYNXNXHRUVCXNXCUPXDXEAUUKGNXFXEWJAFGAFJXGAGIXGXIXJVPXK $.
  $}

  ${
    $d A a e j l $.  $d A a j l x y $.  $d B a $.  $d K e j l $.
    $d K f j l x y $.  $d K g i $.  $d N f j $.  $d N g $.  $d a f j l x y $.
    $d a g i $.  $d a e j l ph $.  $d i l $.  $d ph x y $.
    sticksstones8.1 $e |- ( ph -> N e. NN0 ) $.
    sticksstones8.2 $e |- ( ph -> K e. NN0 ) $.
    sticksstones8.3 $e |- F = ( a e. A |-> ( j e. ( 1 ... K ) |->
    ( j + sum_ l e. ( 1 ... j ) ( a ` l ) ) ) ) $.
    sticksstones8.4 $e |- A = { g | ( g : ( 1 ... ( K + 1 ) ) --> NN0 /\
     sum_ i e. ( 1 ... ( K + 1 ) ) ( g ` i ) = N ) } $.
    sticksstones8.5 $e |- B = { f | ( f : ( 1 ... K ) --> ( 1 ... ( N + K ) )
    /\ A. x e. ( 1 ... K ) A. y e. ( 1 ... K ) ( x < y ->
    ( f ` x ) < ( f ` y ) ) ) } $.
    $( Establish mapping between strictly monotone functions and functions that
       sum to a fixed non-negative integer.  (Contributed by metakunt,
       1-Oct-2024.) $)
    sticksstones8 $p |- ( ph -> F : A --> B ) $=
      ( wcel ve c1 cfz co cv cfv csu caddc cmpt wa wf clt wbr wi wral cab eqidd
      w3a cvv wceq simpr oveq2d sumeq1d oveq12d simp3 ovexd fvmptd cn0 3ad2ant1
      eqcomd eleqtrrd wb feq1 simpl fveq1d sumeq2dv eqeq1d anbi12d elabg biimpd
      a1i syl mpd simpld 3adant3 eqid fveq2 cbvsum simprd eqtr3id sticksstones7
      eqeltrrd 3expa fmptd ad3antrrr adantr adantl simpllr simplr sticksstones6
      nfcv ex ralrimiva jca cfn fzfid fexd fveq1 breq12d imbi2d 2ralbidv mpbird
      ) AMDIUBKUCUDZIUEZUBXNUCUDZNUEZMUEZUFZNUGZUHUDZUIZEJAXQDTZUJZYAXMUBLKUHUD
      UCUDZFUEZUKZBUEZCUEZULUMZYGYEUFZYHYEUFZULUMZUNZCXMUOBXMUOZUJZFUPZEYCYAYPT
      ZXMYDYAUKZYIYGYAUFZYHYAUFZULUMZUNZCXMUOZBXMUOZUJZYCYRUUDYCIXMXTYDYAAYBXNX
      MTZXTYDTAYBUUFURZXNUAXMUAUEZUBUUHUCUDZXRNUGZUHUDZUIZUFXTYDUUGUAXNUUKXTXMU
      ULUSUUGUULUQUUGUUHXNUTZUJZUUHXNUUJXSUHUUGUUMVAZUUNUUIXOXRNUUNUUHXNUBUCUUO
      VBVCVDAYBUUFVEZUUGXNXSUHVFVGUUGUANUULXQKLXNAYBLVHTZUUFOVIAYBKVHTZUUFPVIAY
      BUBKUBUHUDUCUDZVHXQUKZUUFYCUUTUUSHUEZXQUFZHUGZLUTZYCXQUUSVHGUEZUKZUUSUVAU
      VEUFZHUGZLUTZUJZGUPZTZUUTUVDUJZYCXQDUVKAYBVAZYCDUVKDUVKUTYCRWAVJVKZYCUVLU
      VMYCYBUVLUVMVLZUVNUVJUVMGXQDUVEXQUTZUVFUUTUVIUVDUUSVHUVEXQVMUVQUVHUVCLUVQ
      UUSUVGUVBHUVQUVAUUSTZUJUVAUVEXQUVQUVRVNVOVPVQVRVSZWBVTWCZWDWEUUPUULWFAYBU
      USXRNUGZLUTUUFYCUWAUVCLUUSUVBXRHNUVAXPXQWGNUVBXAHXRXAWHYCUUTUVDUVTWIWJWEW
      KWLWMYAWFZWNZYCUUCBXMYCYGXMTZUJZUUBCXMUWEYHXMTZUJZYIUUAUWGYIUJINYAXQKLYGY
      HUWGUUQYIAUUQYBUWDUWFOWOWPUWGUURYIAUURYBUWDUWFPWOWPUWGUUTYIUWEUUTUWFYCUUT
      UWDYCUUTUVDYCUVLUVMUVOYCUVLUVMYBUVPAUVSWQVTWCWDWPWPWPYCUWDUWFYIWRUWEUWFYI
      WSUWGYIVAUWBWTXBXCXCXDYCYAUSTYQUUEVLYCXMYDXEYAUWCYCUBKXFXGYOUUEFYAUSYEYAU
      TZYFYRYNUUDXMYDYEYAVMUWHYMUUBBCXMXMUWHYLUUAYIUWHYJYSYKYTULYGYEYAXHYHYEYAX
      HXIXJXKVRVSWBXLEYPUTYCSWAVKQWN $.
  $}

  ${
    $d A b $.  $d B b $.  $d K g i $.  $d N g i $.  $d b ph $.
    sticksstones9.1 $e |- ( ph -> N e. NN0 ) $.
    sticksstones9.2 $e |- ( ph -> K = 0 ) $.
    sticksstones9.3 $e |- G = ( b e. B |-> if ( K = 0
     , { <. 1 , N >. } , ( k e. ( 1 ... ( K + 1 ) )
        |-> if ( k = ( K + 1 ) , ( ( N + K ) - ( b ` K ) ) , if
       ( k = 1 , ( ( b ` 1 ) - 1 )
       , ( ( ( b ` k ) - ( b ` ( k - 1 ) ) ) - 1 ) ) ) ) ) ) $.
    sticksstones9.4 $e |- A = { g | ( g : ( 1 ... ( K + 1 ) ) --> NN0 /\
     sum_ i e. ( 1 ... ( K + 1 ) ) ( g ` i ) = N ) } $.
    sticksstones9.5 $e |- B = { f | ( f : ( 1 ... K ) --> ( 1 ... ( N + K ) )
    /\ A. x e. ( 1 ... K ) A. y e. ( 1 ... K ) ( x < y ->
    ( f ` x ) < ( f ` y ) ) ) } $.
    $( Establish mapping between strictly monotone functions and functions that
       sum to a fixed non-negative integer.  (Contributed by metakunt,
       6-Oct-2024.) $)
    sticksstones9 $p |- ( ph -> G : B --> A ) $=
      ( wceq c1 cc0 cop csn caddc co cfz cv cfv cmin cif cmpt wa iftrued adantr
      wcel cn0 wf csu cab wss eqid cn 1nn a1i fsng syl2anc mpbiri snssd jca fss
      wb syl oveq1d 0p1e1 eqtrdi oveq2d cz 1zzd fzsn eqtrd eqcomd feq2d sumeq1d
      mpbid cc fvsng nn0cnd eqeltrd fveq2 sumsn snex feq1 simpl fveq1d sumeq2dv
      cvv eqeq1d anbi12d elabg ax-mp sylibr eleqtrrd fmptd ) AMEKUASZTLUBZUCZIT
      KTUDUEZUFUEZIUGZXGSLKUDUEKMUGZUHUIUEXITSTXJUHTUIUEXIXJUHXITUIUEXJUHUIUETU
      IUEUJUJUKZUJZDJAXJEUOZULZXLXFDAXLXFSXMAXDXFXKOUMUNXNXFXHUPGUGZUQZXHHUGZXO
      UHZHURZLSZULZGUSZDXNXHUPXFUQZXHXQXFUHZHURZLSZULZXFYBUOZAYGXMAYCYFATUCZUPX
      FUQZYCAYILUCZXFUQZYKUPUTZULYJAYLYMAYLXFXFSZXFVAATVBUOZLUPUOZYLYNVKYOAVCVD
      ZNTLVBUPXFVEVFVGALUPNVHVIYIYKUPXFVJVLAYIXHUPXFAXHYIAXHTTUFUEZYIAXGTTUFAXG
      UATUDUETAKUATUDOVMVNVOVPATVQUOYRYISAVRTVSVLVTZWAWBWDAYEYIYDHURZLAXHYIYDHY
      SWCAYTTXFUHZLAYOUUAWEUOZULYTUUASAYOUUBYQAUUALWEAYOYPUUALSZYQNTLVBUPWFZVFA
      LNWGWHVIYDUUAHTVBXQTXFWIWJVLAYOYPULUUCAYOYPYQNVIUUDVLVTVTVIUNXFWPUOYHYGVK
      XEWKYAYGGXFWPXOXFSZXPYCXTYFXHUPXOXFWLUUEXSYELUUEXHXRYDHUUEXQXHUOZULXQXOXF
      UUEUUFWMWNWOWQWRWSWTXADYBSXNQVDXBWHPXC $.
  $}

  ${
    $d A b $.  $d B b i k $.  $d B b i s $.  $d B b i w $.  $d K f x y $.
    $d K g i k $.  $d K i s $.  $d K i w $.  $d N f $.  $d N g i k $.
    $d b f x y $.  $d b g i k $.  $d b i k ph $.  $d k x y $.  $d ph s $.
    $d ph w $.
    sticksstones10.1 $e |- ( ph -> N e. NN0 ) $.
    sticksstones10.2 $e |- ( ph -> K e. NN ) $.
    sticksstones10.3 $e |- G = ( b e. B |-> if ( K = 0
     , { <. 1 , N >. } , ( k e. ( 1 ... ( K + 1 ) )
        |-> if ( k = ( K + 1 ) , ( ( N + K ) - ( b ` K ) ) , if
       ( k = 1 , ( ( b ` 1 ) - 1 )
       , ( ( ( b ` k ) - ( b ` ( k - 1 ) ) ) - 1 ) ) ) ) ) ) $.
    sticksstones10.4 $e |- A = { g | ( g : ( 1 ... ( K + 1 ) ) --> NN0 /\
     sum_ i e. ( 1 ... ( K + 1 ) ) ( g ` i ) = N ) } $.
    sticksstones10.5 $e |- B = { f | ( f : ( 1 ... K ) --> ( 1 ... ( N + K ) )
    /\ A. x e. ( 1 ... K ) A. y e. ( 1 ... K ) ( x < y ->
    ( f ` x ) < ( f ` y ) ) ) } $.
    $( Establish mapping between strictly monotone functions and functions that
       sum to a fixed non-negative integer.  (Contributed by metakunt,
       6-Oct-2024.) $)
    sticksstones10 $p |- ( ph -> G : B --> A ) $=
      ( c1 wcel vs vw cc0 wceq caddc co cfz cv cfv cmin cif wne adantr iffalsed
      wa neneqd eqcomd cn0 wf csu cab w3a eleq1 cz cle wbr nnzd zaddcld cn wral
      clt feq1 fveq1 anbi12d elab 1zzd nnge1d zred leidd elfzd ffvelcdmd elfznn
      syl zsubcld nnred recnd addridd elfzle2 eqbrtrd 0red leaddsub2d mpbid jca
      wi elnn0z sylibr 3impa wn 1red 1cnd elfzle1 3adant3 simp3 adantl readdcld
      neqne necomd ltlend mpbird wb zleltp1 syl2anc lesubadd syl3anc a1i subidd
      cr fveq2 leaddsub ifbothda cvv eqidd simpr eqeq1d fveq2d oveq12d ifbieq2d
      oveq1d ovexd sumeq2dv eqeq1 fvoveq1 iftrued oveq2d eqtrd letrd cc elfzelz
      zcnd cmul cop csn cmpt nnne0d nn0zd eleq2i breq12d imbi2d 2ralbidv bilani
      vex bitri simpld zltlem1d 0p1e1 ltm1d simprd breq1 breq1d imbi12d rspc2va
      breq2 breq2d mpd ltaddsub2d zlem1lt 3expa fmpttd fvoveq1d fvmptd cuz nnuz
      ifcld eleqtrdi zltp1le fsump1 ltp1d lelttrd ltned fzfid ad2antrr resubcld
      zltlem1 lem1d fsumsub id fsum1p npcand sumeq1d peano2zd lep1d nfcv cbvsum
      fsumshft eqeltrd breqtrd nncnd telfsum2 eleq1d chash cfn fsumconst nnnn0d
      pncan3d hashfz1 mulridd addlidd 0cnd subsub3d subsub4d addsubassd fsumzcl
      subcld nn0cnd addlsub ovex mptex simpl fveq1d eleqtrrd eqeltrrd fmptd ) A
      MEKUCUDZSLUUAUUBZISKSUEUFZUGUFZIUHZUYEUDZLKUEUFZKMUHZUIZUJUFZUYGSUDZSUYJU
      IZSUJUFZUYGUYJUIZUYGSUJUFZUYJUIZUJUFZSUJUFZUKZUKZUUCZUKZDJAUYJETZUOZVUCVU
      DDVUFVUDVUCVUFUYCUYDVUCVUFKUCAKUCULVUEAKOUUDUMUPUNUQVUFVUCUYFURGUHZUSZUYF
      HUHZVUGUIZHUTZLUDZUOZGVAZDVUFUYFURVUCUSZUYFVUIVUCUIZHUTZLUDZUOZVUCVUNTVUF
      VUOVURVUFIUYFVUBURAVUEUYGUYFTZVUBURTZUYHUYLURTZVUAURTZVVAAVUEVUTVBZUYLVUA
      UYLVUBURVCVUAVUBURVCVVDVVBUYHAVUEVUTVVBVUFVVBVUTVUFUYLVDTZUCUYLVEVFZUOVVB
      VUFVVEVVFVUFUYIUYKVUFLKALVDTZVUEALNUUEUMZAKVDTZVUEAKOVGUMZVHZVUFUYKVUFUYK
      SUYIUGUFZTZUYKVITZVUFSKUGUFZVVLKUYJVUFVVOVVLUYJUSZBUHZCUHZVKVFZVVQUYJUIZV
      VRUYJUIZVKVFZWNZCVVOVJBVVOVJZVUEVVPVWDUOZAVUEUYJVVOVVLFUHZUSZVVSVVQVWFUIZ
      VVRVWFUIZVKVFZWNZCVVOVJBVVOVJZUOZFVAZTVWEEVWNUYJRUUFVWMVWEFUYJMUUKVWFUYJU
      DZVWGVVPVWLVWDVVOVVLVWFUYJVLVWOVWKVWCBCVVOVVOVWOVWJVWBVVSVWOVWHVVTVWIVWAV
      KVVQVWFUYJVMVVRVWFUYJVMUUGUUHUUIVNVOUULUUJZUUMZVUFKSKVUFVPZVVJVVJASKVEVFV
      UEAKOVQUMZVUFKVUFKVVJVRZVSVTWAZUYKUYIWBWCZVGWDVUFUYKUCUEUFZUYIVEVFVVFVUFV
      XCUYKUYIVEVUFUYKVUFUYKVUFUYKVXBWEZWFZWGVUFVVMUYKUYIVEVFVXAUYKSUYIWHWCWIVU
      FUYKUCUYIVXDVUFWJZVUFUYIVVKVRWKWLWMUYLWOWPZUMWQUMUYMUYOURTZUYTURTZVVCVVDU
      YHWRZUOZUYOUYTUYOVUAURVCUYTVUAURVCVXKVXHUYMVVDVXHVXJAVUEVUTVXHVUFVXHVUTVU
      FUYOVDTZUCUYOVEVFZUOVXHVUFVXLVXMVUFUYNSVUFUYNVVLTZUYNVDTZVUFVVOVVLSUYJVWQ
      VUFSSKVWRVVJVWRVUFSVUFWSZVSVWSVTWAZVXNUYNUYNUYIWBVGWCZVWRWDVUFSUCUEUFZUYN
      VEVFVXMVUFVXSSUYNVEVUFSVUFWTZWGVUFVXNSUYNVEVFVXQUYNSUYIXAWCWIVUFSUCUYNVXP
      VXFVUFUYNVXRVRZWKWLWMUYOWOWPUMWQUMUMVXKUYMWRZUOZUYTVDTZUCUYTVEVFZUOVXIVYC
      VYDVYEVYCUYSSVYCUYPUYRVXKUYPVDTVYBVXKUYPVXKUYPVVLTUYPVITVXKVVOVVLUYGUYJVV
      DVVPVXJAVUEVVPVUTVWQXBUMZVXKUYGSKVXKVPVVDVVIVXJAVUEVVIVUTVVJXBZUMZVXKUYGV
      VDUYGVITZVXJVVDVUTVYIAVUEVUTXCZUYGUYEWBWCZUMZVGZVXKUYGVYLVQZVXKUYGKVEVFZU
      YGUYEVKVFZVXKVYPUYGUYEVEVFZUYEUYGULZUOVXKVYQVYRVVDVYQVXJVVDVUTVYQVYJUYGSU
      YEWHWCZUMVXKUYGUYEVXJUYGUYEULVVDUYGUYEXFXDXGWMVXKUYGUYEVXKUYGVYLWEZVXKKSV
      XKKVYHVRVXKWSZXEXHXIVVDVYOVYPXJZVXJVVDUYGVDTZVVIWUBVVDUYGVYKVGVYGUYGKXKXL
      UMXIVTZWAUYPUYIWBWCVGUMZVYCUYRVYCUYRVVLTUYRVITVYCVVOVVLUYQUYJVXKVVPVYBVYF
      UMVYCUYQSKVYCVPZVXKVVIVYBVYHUMVYCUYGSVXKWUCVYBVYMUMZWUFWDVYCSUYGVKVFZSUYQ
      VEVFVYCWUHSUYGVEVFZUYGSULZUOVYCWUIWUJVXKWUIVYBVYNUMVYBWUJVXKUYGSXFXDWMVYC
      SUYGVXKSXQTZVYBWUAUMZVXKUYGXQTZVYBVYTUMZXHXIVYCSUYGWUFWUGUUNWLVXKUYQKVEVF
      ZVYBVVDWUOVXJVVDWUOVYQVYSVVDWUMWUKKXQTZWUOVYQXJVVDUYGVYKWEAVUEWUKVUTVXPXB
      AVUEWUPVUTVWTXBUYGSKXMXNXIUMUMVTZWAUYRUYIWBWCVGZWDZWUFWDVYCUCSUEUFZUYSVEV
      FZVYEVYCWUTSUYSVEWUTSUDVYCUUOXOVYCSUYSVEVFZSSUJUFZUYSVKVFZVYCWVCUCUYSVKVY
      CSVYCWTXPVYCUYRUCUEUFZUYPVKVFUCUYSVKVFVYCWVEUYRUYPVKVYCUYRVYCUYRVYCUYRWUR
      VRZWFWGVYCUYQUYGVKVFZUYRUYPVKVFZVYCUYGWUNUUPVYCUYQVVOTZUYGVVOTZUOVWDWVGWV
      HWNZVYCWVIWVJWUQVXKWVJVYBWUDUMWMVXKVWDVYBVVDVWDVXJAVUEVWDVUTVUFVVPVWDVWPU
      UQXBUMUMVWCWVKUYQVVRVKVFZUYRVWAVKVFZWNBCUYQUYGVVOVVOVVQUYQUDZVVSWVLVWBWVM
      VVQUYQVVRVKUURWVNVVTUYRVWAVKVVQUYQUYJXRUUSUUTVVRUYGUDZWVLWVGWVMWVHVVRUYGU
      YQVKUVBWVOVWAUYPUYRVKVVRUYGUYJXRUVCUUTUVAXLUVDWIVYCUYRUCUYPWVFVYCWJZVYCUY
      PWUEVRUVEWLWIVYCSVDTZUYSVDTWVBWVDXJWUFWUSSUYSUVFXLXIWIVYCUCXQTWUKUYSXQTWV
      AVYEXJWVPWULVYCUYSWUSVRUCSUYSXSXNWLWMUYTWOWPXTXTUVGUVHVUFVUQUYFVUIUYEUDZU
      YLVUISUDZUYOVUIUYJUIZVUISUJUFZUYJUIZUJUFZSUJUFZUKZUKZHUTZLVUFUYFVUPWWFHVU
      FVUIUYFTZUOZIVUIVUBWWFUYFVUCYAWWIVUCYBWWIUYGVUIUDZUOZUYHWVRVUAWWEUYLWWKUY
      GVUIUYEWWIWWJYCZYDWWKUYMWVSUYTWWDUYOWWKUYGVUISWWLYDWWKUYSWWCSUJWWKUYPWVTU
      YRWWBUJWWKUYGVUIUYJWWLYEWWKUYGVUISUYJUJWWLUVIYFYHYGYGVUFWWHYCWWIWVRUYLWWE
      YAWWIUYIUYKUJYIWWIWVSUYOWWDYAWWIUYNSUJYIWWIWWCSUJYIUVMUVMUVJYJVUFWWGVVOWW
      FHUTZUYEUYEUDZUYLUYESUDZUYOUYEUYJUIZUYESUJUFUYJUIZUJUFZSUJUFZUKZUKZUEUFZL
      VUFWWFWXAHSKVUFKVISUVKUIZAKVITVUEOUMZUVLUVNZWWIWWFAVUEWWHWWFVDTZWVRVVEWWE
      VDTZWXFAVUEWWHVBZUYLWWEUYLWWFVDVCWWEWWFVDVCWXHWVRUOZUYIUYKWXILKWXHVVGWVRA
      VUEVVGWWHVVHXBUMWXHVVIWVRAVUEVVIWWHVVJXBZUMVHWXIUYKWXHVVNWVRAVUEVVNWWHVXB
      XBUMVGWDWVSVXLWWDVDTWXGWXHWVRWRZUOZUYOWWDUYOWWEVDVCWWDWWEVDVCWXLWVSUOZUYN
      SWXLVXOWVSWXHVXOWXKAVUEVXOWWHVXRXBUMUMWXMVPWDWXLWVSWRZUOZWWCSWXOWVTWWBWXO
      WVTWXOWVTVVLTZWVTVITWXOVVOVVLVUIUYJWXLVVPWXNWXHVVPWXKAVUEVVPWWHVWQXBUMUMZ
      WXLVUIVVOTZWXNWXLVUISKWXLVPWXHVVIWXKWXJUMZWXHVUIVDTZWXKWXHVUIAVUEWWHVUIVI
      TZWWHWYAVUFVUIUYEWBXDWQZVGUMZWXHSVUIVEVFZWXKWXHVUIWYBVQUMZWXLVUIKVEVFZVUI
      UYEVKVFZWXLWYGVUIUYEVEVFZUYEVUIULZUOWXLWYHWYIWXHWYHWXKWXHWWHWYHAVUEWWHXCV
      UISUYEWHWCUMZWXLVUIUYEWXKVUIUYEULWXHVUIUYEXFXDXGWMWXLVUIUYEWXLVUIWYCVRWXL
      KSWXLKWXSVRZWXLWSXEXHXIWXLWXTVVIWYFWYGXJWYCWXSVUIKXKXLXIVTUMWAWVTUYIWBZWC
      VGWXOWWBWXOWWBVVLTZWWBVITZWXOVVOVVLWWAUYJWXQWXOWWASKWXOVPZWXLVVIWXNWXSUMW
      XOVUISWXLWXTWXNWYCUMZWYOWDWXOSSUEUFZVUIVEVFZSWWAVEVFZWXOSVUIVKVFZWYRWXOWY
      TWYDVUISULZUOZWXOWYDXUAWXLWYDWXNWYEUMWXNXUAWXLVUISXFZXDWMWXOSVUIWXOWSZWXO
      VUIWYPVRZXHXIWXOWVQWXTWYTWYRXJZWYOWYPSVUIUVOZXLWLWXOWUKWUKVUIXQTZWYRWYSXJ
      XUDXUDXUESSVUIXSXNWLWXOWWAKVEVFZWYHWXLWYHWXNWYJUMWXOXUHWUKWUPXUIWYHXJXUEX
      UDWXLWUPWXNWYKUMVUISKXMXNXIVTWAWWBUYIWBZWCVGWDWYOWDXTXTUVGYSWVRWVRWWNWWEW
      WTUYLVUIUYEUYEYKWVRWVSWWOWWDWWSUYOVUIUYESYKWVRWWCWWRSUJWVRWVTWWPWWBWWQUJV
      UIUYEUYJXRVUIUYESUYJUJYLYFYHYGYGUVPVUFWXBWWMUYLUEUFZLVUFWXAUYLWWMUEVUFWWN
      UYLWWTVUFUYEYBYMYNVUFXUKVVOWWEHUTZUYLUEUFZLVUFWWMXULUYLUEVUFVVOWWFWWEHVUF
      WXRUOZWVRUYLWWEXUNVUIUYEXUNVUIUYEXUNVUIWXRWYAVUFVUIKWBXDZWEZXUNVUIKUYEXUP
      VUFWUPWXRVWTUMZXUNKSXUQXUNWSZXEWXRWYFVUFVUISKWHXDZXUNKXUQUVQUVRUVSUPUNYJY
      HVUFXUMVVOWVSUYNWWCUKZSUJUFZHUTZUYLUEUFZLVUFXULXVBUYLUEVUFVVOWWEXVAHWVSUY
      OXVAUDWWDXVAUDWWEXVAUDXUNUYOWWDUYOWWEXVAYKWWDWWEXVAYKXUNWVSUOZUYOUYOXVAXV
      DUYOYBXVDUYNXUTSUJXVDXUTUYNXVDWVSUYNWWCXUNWVSYCYMUQYHYOXUNWXNUOZWWDWWDXVA
      XVEWWDYBXVEXVAWWDXVEXUTWWCSUJXVEWVSUYNWWCXUNWXNYCZUNYHUQYOXTYJYHVUFXVCLUD
      XVBLUYLUJUFZUDVUFXVBLLKUYKUJUFZUEUFZUJUFZXVGVUFXVBLLUJUFZXVHUJUFZXVJVUFXV
      BUCXVHUJUFZXVLVUFXVBUCUYKUEUFZKUJUFZXVMVUFXVBUYKKUJUFZXVOVUFXVBVVOXUTHUTZ
      VVOSHUTZUJUFXVPVUFVVOXUTSHVUFSKUVTZXUNXUTWVSVXOWWCVDTXUTVDTXUNUYNWWCUYNXU
      TVDVCWWCXUTVDVCVUFVXOWXRWVSVXRUWAXVEWVTWWBXUNWVTVDTZWXNXUNWXPXVTXUNVVOVVL
      VUIUYJVUFVVPWXRVWQUMZVUFWXRYCWAWXPWVTWYLVGWCUMXVEWWBXVEWYMWYNXVEVVOVVLWWA
      UYJXUNVVPWXNXWAUMXVEWWASKXVEVPZVUFVVIWXRWXNVVJUWAXVEVUISXUNWXTWXNXUNVUIXU
      OVGUMZXWBWDXVEWYTWYSXVEWYTXUBXVEWYDXUAXUNWYDWXNXUNVUIXUOVQUMXVEWXNXUAXVFX
      UCWCWMXVESVUIXUNWUKWXNXURUMXUNXUHWXNXUPUMXHXIXVEWVQWXTWYTWYSXJXWBXWCSVUIU
      WCXLWLXUNXUIWXNXUNWWAVUIKXUNVUISXUPXURUWBXUPXUQXUNVUIXUPUWDXUSYPUMVTWAXUJ
      WCVGWDXTZYSZVUFSYQTZWXRVXTUMUWEVUFXVQUYKXVRKUJVUFXVQUYNWYQKUGUFZXUTHUTZUE
      UFZUYKVUFXUTUYNHSKWXEXWEWVSWVSUYNWWCWVSUWFYMUWGVUFXWIUYNXWGWWCHUTZUEUFZUY
      KVUFXWHXWJUYNUEVUFXWGXUTWWCHVUFVUIXWGTZUOZWVSUYNWWCXWMVUISXWMSVUIXWMSVUIV
      UFWUKXWLVXPUMXWMWYTWYRXWLWYRVUFVUIWYQKXAXDXWMWVQWXTXUFVUFWVQXWLVWRUMXWLWX
      TVUFVUIWYQKYRXDXUGXLXIUVSXGUPUNYJYNVUFXWKUYNWYQKSUJUFZSUEUFZUGUFZWWCHUTZU
      EUFZUYKVUFXWJXWQUYNUEVUFXWGXWPWWCHVUFKXWOWYQUGVUFXWOKVUFKSVUFKVWTWFZVXTUW
      HZUQYNUWIYNVUFXWRUYNXWPWWASUEUFZUYJUIZWWBUJUFZHUTZUEUFZUYKVUFXWQXXDUYNUEV
      UFXWPWWCXXCHVUFVUIXWPTZUOZWVTXXBWWBWWBUJXXGVUIXXAUYJXXGXXAVUIXXGVUISXXGVU
      IXXFWXTVUFVUIWYQXWOYRXDYSXXGWTUWHUQYEXXGWWBYBYFYJYNVUFXXEUYNSXWNUGUFZUAUH
      ZSUEUFZUYJUIZXXIUYJUIZUJUFZUAUTZUEUFZUYKVUFXXOXXEVUFXXNXXDUYNUEVUFXXMXXCU
      AHSSXWNVWRVWRVUFKSVVJVWRWDZVUFXXIXXHTZUOZXXMXXRXXKXXLXXRXXKXXRXXKVVLTXXKV
      ITXXRVVOVVLXXJUYJVUFVVPXXQVWQUMZXXRXXJSKXXRVPZVUFVVIXXQVVJUMZXXRXXIXXRXXI
      XXQXXIVITVUFXXIXWNWBXDZVGZUWJXXRSXXIXXJXXRWSZXXRXXIXYBWEZXXRXXISXYEXYDXEX
      XRXXIXYBVQZXXRXXIXYEUWKYPXXRXXJKVEVFZXXIXWNVEVFZXXQXYHVUFXXISXWNWHXDZXXRX
      XIXQTWUKWUPXYGXYHXJXYEXYDVUFWUPXXQVWTUMZXXISKXSXNXIVTWAXXKUYIWBWCVGXXRXXL
      VVLTZXXLVDTXXRVVOVVLXXIUYJXXSXXRXXISKXXTXYAXYCXYFXXRXXIXWNKXYEXXRKSXYJXYD
      UWBXYJXYIXXRKXYJUWDYPVTWAXYKXXLXXLUYIWBVGWCWDYSXXIWWAUDXXKXXBXXLWWBUJXXIW
      WASUYJUEYLXXIWWAUYJXRYFUWNYNUQVUFXXOUYNXXHVUISUEUFZUYJUIZWVTUJUFZHUTZUEUF
      ZUYKVUFXXNXYOUYNUEXXNXYOUDVUFXXHXXMXYNUAHXXIVUIUDXXKXYMXXLWVTUJXXIVUISUYJ
      UEYLXXIVUIUYJXRYFHXXMUWLUAXYNUWLUWMXOYNVUFXYPUYNXWOUYJUIZUYNUJUFZUEUFZUYK
      VUFXYOXYRUYNUEVUFUBUHZUYJUIZWVTXYMUYNHUBXYQSXWNXYTVUIUYJXRXYTXYLUYJXRXYTS
      UYJXRXYTXWOUYJXRXXPVUFXWOKWXCXWTWXEUWOVUFXYTSXWOUGUFTZUOZYUAVVLTZYUAYQTYU
      CVVOVVLXYTUYJVUFVVPYUBVWQUMYUCXYTSKYUCVPVUFVVIYUBVVJUMYUBXYTVDTVUFXYTSXWO
      YRXDYUBSXYTVEVFVUFXYTSXWOXAXDYUCXYTXWOKVEYUBXYTXWOVEVFVUFXYTSXWOWHXDVUFXW
      OKUDYUBXWTUMUWPVTWAYUDYUAYUAUYIWBUWQWCUWRYNVUFXYSXYQUYKVUFUYNXYQVUFUYNVYA
      WFVUFXYQYQTUYKYQTVUFUYKVXBUWQVUFXYQUYKYQVUFXWOKUYJXWTYEZUWSXIUXDYUEYOYOYO
      YOYOYOYOYOVUFXVRVVOUWTUIZSYTUFZKVUFVVOUXATXWFXVRYUGUDXVSVXTVVOSHUXBXLVUFY
      UGKSYTUFKVUFYUFKSYTVUFKURTYUFKUDVUFKWXDUXCKUXEWCYHVUFKXWSUXFYOYOYFYOVUFUY
      KXVNKUJVUFXVNUYKVUFUYKVXEUXGUQYHYOVUFXVMXVOVUFUCKUYKVUFUXHXWSVXEUXIUQYOVU
      FUCXVKXVHUJVUFXVKUCVUFLVUFLVVHYSZXPUQYHYOVUFLLXVHYUHYUHVUFKUYKXWSVXEUXMUX
      JYOVUFXVIUYLLUJVUFUYLXVIVUFLKUYKYUHXWSVXEUXKUQYNYOVUFXVBUYLLVUFXVBVUFVVOX
      VAHXVSXUNXUTSXWDXUNVPWDUXLYSVUFUYLVXGUXNYUHUXOXIYOYOYOYOYOWMVUMVUSGVUCIUY
      FVUBSUYEUGUXPUXQVUGVUCUDZVUHVUOVULVURUYFURVUGVUCVLYUIVUKVUQLYUIUYFVUJVUPH
      YUIWWHUOVUIVUGVUCYUIWWHUXRUXSYJYDVNVOWPDVUNUDVUFQXOUXTUYAPUYB $.
  $}

  ${
    $d A a c j l $.  $d A b c j l $.  $d A a j l x y $.  $d B a $.  $d B b $.
    $d B d $.  $d F c $.  $d F d $.  $d G c $.  $d G d $.  $d K a f j l x y $.
    $d K b j l $.  $d K a g i $.  $d K g i u $.  $d N b j $.  $d N f j $.
    $d N g i u $.  $d N i p u $.  $d a c j l ph $.  $d b c j l ph $.
    $d d f x y $.  $d d ph x y $.  $d i l $.  $d p ph u $.
    sticksstones11.1 $e |- ( ph -> N e. NN0 ) $.
    sticksstones11.2 $e |- ( ph -> K = 0 ) $.
    sticksstones11.3 $e |- F = ( a e. A |-> ( j e. ( 1 ... K ) |->
    ( j + sum_ l e. ( 1 ... j ) ( a ` l ) ) ) ) $.
    sticksstones11.4 $e |- G = ( b e. B |-> if ( K = 0
     , { <. 1 , N >. } , ( k e. ( 1 ... ( K + 1 ) )
        |-> if ( k = ( K + 1 ) , ( ( N + K ) - ( b ` K ) ) , if
       ( k = 1 , ( ( b ` 1 ) - 1 )
       , ( ( ( b ` k ) - ( b ` ( k - 1 ) ) ) - 1 ) ) ) ) ) ) $.
    sticksstones11.5 $e |- A = { g | ( g : ( 1 ... ( K + 1 ) ) --> NN0 /\
     sum_ i e. ( 1 ... ( K + 1 ) ) ( g ` i ) = N ) } $.
    sticksstones11.6 $e |- B = { f | ( f : ( 1 ... K ) --> ( 1 ... ( N + K ) )
    /\ A. x e. ( 1 ... K ) A. y e. ( 1 ... K ) ( x < y ->
    ( f ` x ) < ( f ` y ) ) ) } $.
    $( Establish bijective mapping between strictly monotone functions and
       functions that sum to a fixed non-negative integer.  (Contributed by
       metakunt, 6-Oct-2024.) $)
    sticksstones11 $p |- ( ph -> F : A -1-1-onto-> B ) $=
      ( vc vd vu vp cc0 cn0 wcel a1i eqeltrd sticksstones8 sticksstones9 cv cfv
      0nn0 wceq wa c1 cop csn wf wss caddc co cfz csu cab nfv nfcv wfn ad2antrl
      wi ffn 1nn adantr fnsng syl2anc elsni adantl simpr fveq2d simprl 1ex snid
      cn cc ffvelcdmd nn0cnd fveq2 sumsn eqcomd eqtrd ex mpd fvsng 3eqtrd mpdan
      simplrr eqfnfvd wb mpbird fss mpbid vex elsn sylibr cz syl oveq2d sumeq1d
      feq2d eqeq1d anbi12d imbi1d feq1 fveq1d elab imp ssrd biimpd 3ad2ant1 jca
      eleq1d simpld fvconst eleq2d sylib ralrimiva c0 clt wbr wral fveq1 imbi2d
      breq12d 2ralbidv cvv cmpt fsng ssidd 1zzd fzsn 1e0p1 simpl sumeq2dv impel
      oveq1d bicomd snssd w3a 3adant3 eqtr4d 3expa eqssd eqss biimpi ffvelcdmda
      syldbl2 0lt1 eqbrtrd nn0zd fzn f0bi velsn ral0 raleqtrrdv 0ex elabg ax-mp
      f0 eleqtrrd impbid eqrd eleqtrd mpteq1d mpt0 cfn fzfid mptexd elsng fmptd
      ffvelcdm 2fvidf1od ) ADEKLUDUEABCDEFGHIKMNOQRAMUHUISUHUIUJAUQUKULZTUBUCUM
      ZABCDEFGHJLMNPRSUAUBUCUNZAUDUOZKUPZLUPZUWIURUDDAUWIDUJZUSZUWKUTNVAVBZUWIU
      WMEUWNVBZLVCZUWJEUJUWKUWNURAUWPUWLAEDLVCZDUWOVDZUWPUWHADUWOURZUWRADUTMUTV
      EVFZVGVFZUIGUOZVCZUXAHUOZUXBUPZHVHZNURZUSZGVIZUWODUXIURAUBUKAUXIUWOAUFUXI
      UWOAUFVJZUFUXIVKZUFUWOVKZAUFUOZUXIUJZUXMUWOUJZAUXNUXOAUXNUXOVNUXAUIUXMVCZ
      UXAUXDUXMUPZHVHZNURZUSZUXOVNZAUTVBZUIUXMVCZUYBUXQHVHZNURZUSZUXOVNUYAAUYFU
      XOAUYFUSZUXMUWNURZUXOUYGUYBNVBZUXMVCZUYHUYGUYJUYIUYIVDZUYJUYGUYJUYKUYJUYG
      UYJUYHUYGUGUYBUXMUWNUYCUXMUYBVLAUYEUYBUIUXMVOVMUYGUTWGUJZNUIUJZUWNUYBVLUY
      LUYGVPUKZAUYMUYFRVQZUTNWGUIVRVSUYGUGUOZUYBUJZUSZUYPUTURZUYPUXMUPZUYPUWNUP
      ZURUYQUYSUYGUYPUTVTWAUYRUYSUSZUYTUTUXMUPZUTUWNUPZVUAVUBUYPUTUXMUYRUYSWBZW
      CUYRVUCVUDURUYSUYRVUCNVUDUYGVUCNURZUYQUYGUYDVUCURZVUFUYGUYLVUCWHUJZVUGUYN
      UYGVUCUYGUYBUIUTUXMAUYCUYEWDUTUYBUJUYGUTWEWFUKWIWJUXQVUCHUTWGUXDUTUXMWKWL
      ZVSZUYGVUGVUFUYGVUGUSZVUCUYDNVUKUYDVUCUYGVUGVUGVUJVQWMAUYCUYEVUGWTWNWOWPV
      QUYRVUDNUYRUYLUYMVUDNURZUYLUYRVPUKUYGUYMUYQUYOVQUTNWGUIWQZVSWMWNVQVUBUTUY
      PUWNVUBUYPUTVUEWMWCWRWSXAUYGUYLUYMUYJUYHXBZUYNUYOUTNWGUIUXMUUAZVSZXCUYGUY
      IUUBZUYBUYIUYIUXMXDZVSVUQVURVSVUPXEUXMUWNUFXFZXGXHWOAUYFUXTUXOAUYCUXPUYEU
      XSAUYBUXAUIUXMAUYBUTUHUTVEVFZVGVFZUXAAUYBUTUTVGVFZVVAAVVBUYBAUTXIUJZVVBUY
      BURAUUCZUTUUDXJWMAUTVUTUTVGUTVUTURAUUEUKXKWNAVUTUWTUTVGAUHMUTVEAMUHSWMUUI
      XKWNZXMZAUYDUXRNAUYBUXAUXQHVVEXLXNXOXPXEAUXNUXTUXOUXNUXTXBAUXHUXTGUXMVUSU
      XBUXMURZUXCUXPUXGUXSUXAUIUXBUXMXQVVGUXFUXRNVVGUXAUXEUXQHVVGUXDUXAUJZUSUXD
      UXBUXMVVGVVHUUFXRUUGXNXOXSZUKXPXCXTWOYAAUFUWOUXIUXJUXLUXKAUXOUXNAUXOUSZUX
      TUXNVVJUXPUXSVVJUYCUXPVVJUYJUYIUIVDZUYCAUYHUYJUXOAUYHUYJAUYJUYHAUYLUYMVUN
      UYLAVPUKRVUOVSUUJYBUXMUWNVTZUUHAVVKUXOANUIRUUKVQUYBUYIUIUXMXDVSAUYCUXPXBU
      XOVVFVQXEVVJUYHUXSUXOUYHAVVLWAZAUXOUYHUXSAUXOUYHUULZUXRUYDNVVNUXAUYBUXQHV
      VNUYBUXAAUXOUYBUXAURUYHVVEYCWMXLVVNUYDVUCNVVNUYLVUHVUGUYLVVNVPUKZVVNNWHUJ
      VUHVVNNAUXOUYMUYHRYCZWJVVNNVUCWHVVNNVUDVUCVVNVUDNVVNUYLUYMVULVVOVVPVUMVSZ
      WMVVNUTUXMUWNAUXOUYHUYHVVMUUMXRZUUNYEXEVUIVSVVNVUCVUDNVVRVVQWNWNWNUUOWSYD
      VVIXHWOYAUUPWNZUWSUWRUWODVDZUWSUWRVVTUSDUWOUUQUURYFXJEDUWOLXDVSVQADEUWIKU
      WGUUSEUWNUWJLYGVSUWMUWIUWNUWMUWIUWOUJZUWIUWNURAUWLVWAAUWLVWAADUWOUWIVVSYH
      YBXTUWIUWNUDXFXGYIWMWNYJAUEUOZLUPZKUPZVWBURUEEAVWBEUJZUSZVWDYKVWBVWFVWDYK
      LUPZKUPZYKVWFVWCVWGKVWFVWBYKLVWFVWBYKVBZUJZVWBYKURZVWFVWBEVWIAVWEWBAEVWIU
      RVWEAUEEVWIAUEVJUEEVKUEVWIVKAVWEVWJAVWEVWJVWFVWKVWJVWFYKUTNMVEVFVGVFZVWBV
      CZVWKVWFUTMVGVFZVWLVWBVCZVWMVWFVWOBUOZCUOZYLYMZVWPVWBUPZVWQVWBUPZYLYMZVNZ
      CVWNYNBVWNYNZVWFVWBVWNVWLFUOZVCZVWRVWPVXDUPZVWQVXDUPZYLYMZVNZCVWNYNBVWNYN
      ZUSZFVIZUJZVWOVXCUSZAVWEVXMVWFVWEVXMVWFEVXLVWBEVXLURZVWFUCUKYHYBUUTVXKVXN
      FVWBUEXFZVXDVWBURZVXEVWOVXJVXCVWNVWLVXDVWBXQVXQVXIVXBBCVWNVWNVXQVXHVXAVWR
      VXQVXFVWSVXGVWTYLVWPVXDVWBYOVWQVXDVWBYOYQYPYRXOXSYIYFAVWOVWMXBVWEAVWNYKVW
      LVWBAMUTYLYMZVWNYKURZAMUHUTYLSUHUTYLYMAUVAUKUVBAVVCMXIUJVXRVXSXBVVDAMUWFU
      VCUTMUVDVSXEZXMVQXEVWBVWLUVEYIUEYKUVFXHWOAVWJVWEAVWJUSZVWEYKEUJZAVYBVWJAY
      KVXLEAVWNVWLYKVCZVWRVWPYKUPZVWQYKUPZYLYMZVNZCVWNYNZBVWNYNZUSZYKVXLUJZAVYC
      VYIAVYCYKVWLYKVCZVYLAVWLUVLUKAVWNYKVWLYKVXTXMXCAVYHBYKVWNVYHBYKYNAVYHBUVG
      UKVXTUVHYDYKYSUJVYKVYJXBUVIVXKVYJFYKYSVXDYKURZVXEVYCVXJVYIVWNVWLVXDYKXQVY
      MVXIVYGBCVWNVWNVYMVXHVYFVWRVYMVXFVYDVXGVYEYLVWPVXDYKYOVWQVXDYKYOYQYPYRXOU
      VJUVKXHVXOAUCUKUVMZVQVYAVWBYKEVWJVWKAVWBYKVTWAYEXCWOUVNUVOVQUVPVWBYKVXPXG
      YIZWCWCVWFDVWIKVCZVWGDUJZVWHYKURAVYPVWEAODIVWNIUOZUTVYRVGVFQUOOUOZUPQVHVE
      VFZYTZVWIKAVYSDUJZUSZWUAVWIUJZWUAYKURZWUCWUAIYKVYTYTZYKWUCIVWNYKVYTAVXSWU
      BVXTVQUVQWUFYKURWUCIVYTUVRUKWNAWUDWUEXBZWUBAWUAYSUJWUGAIVWNVYTUVSAUTMUVTU
      WAWUAYKYSUWBXJVQXCTUWCVQAVYQVWEAUWQVYBVYQUWHVYNEDYKLUWDVSVQDYKVWGKYGVSWNV
      WFVWBYKVYOWMWNYJUWE $.
  $}

  ${
    $d A a j l $.  $d d o ph s $.  $d d ph r $.  $d b d g i k $.  $d d ph w $.
    $d a d f l x y $.  $d F b k $.  $d B o s $.  $d B w $.  $d B b $.
    $d N b g i k $.  $d N a f j l $.  $d K o s $.  $d K r $.  $d K j l w $.
    $d K a g i k $.  $d K b f x y $.  $d A b k x y $.  $d B a i k l $.
    $d k s $.  $d B j l r $.  $d a j k l ph x y $.  $d K q $.  $d d j q $.
    $d b i ph $.
    sticksstones12a.1 $e |- ( ph -> N e. NN0 ) $.
    sticksstones12a.2 $e |- ( ph -> K e. NN ) $.
    sticksstones12a.3 $e |- F = ( a e. A |-> ( j e. ( 1 ... K ) |->
    ( j + sum_ l e. ( 1 ... j ) ( a ` l ) ) ) ) $.
    sticksstones12a.4 $e |- G = ( b e. B |-> if ( K = 0
     , { <. 1 , N >. } , ( k e. ( 1 ... ( K + 1 ) )
        |-> if ( k = ( K + 1 ) , ( ( N + K ) - ( b ` K ) ) , if
       ( k = 1 , ( ( b ` 1 ) - 1 )
       , ( ( ( b ` k ) - ( b ` ( k - 1 ) ) ) - 1 ) ) ) ) ) ) $.
    sticksstones12a.5 $e |- A = { g | ( g : ( 1 ... ( K + 1 ) ) --> NN0 /\
     sum_ i e. ( 1 ... ( K + 1 ) ) ( g ` i ) = N ) } $.
    sticksstones12a.6 $e |- B = { f | ( f : ( 1 ... K ) --> ( 1 ... ( N + K ) )
    /\ A. x e. ( 1 ... K ) A. y e. ( 1 ... K ) ( x < y ->
    ( f ` x ) < ( f ` y ) ) ) } $.
    $( Establish bijective mapping between strictly monotone functions and
       functions that sum to a fixed non-negative integer.  (Contributed by
       metakunt, 11-Oct-2024.) $)
    sticksstones12a $p |- ( ph -> A. d e. B ( F ` ( G ` d ) ) = d ) $=
      ( vq vs vw cv cfv wceq wcel wa c1 cfz co cmpt caddc cif cc0 cvv a1i ltned
      cmin wn necomd neneqd ad2antrr iffalsed fveq1 oveq2d oveq1d adantl adantr
      oveq12d eqtrd simpr cfn fvmptd fveq2d csu sumeq2dv cn0 eleq1 cle wbr wral
      wf clt wi cz nnge1d nnred elfzd ffvelcdmd elfzle2 syl wb elfznn ad3antrrr
      1zzd syl2anc mpbid cn nnzd elfzle1 wne 1red readdcld mpbird 3impa zsubcld
      cr w3a 3ad2ant1 zred leaddsub syl3anc resubcld cc 1cnd letrd jca ifbothda
      fveq2 eqidd eqeq1d ifbieq2d ovexd ifcld eqeq1 fvoveq1 nfcv elfzelz eqcomd
      peano2zd 3adant3 lem1d zcnd cmul subcld vo vr cop csn 0red nngt0d ifeq12d
      mpteq2dva fzfid mptexd simpll fveq1d cab eleq2i vex feq1 breq12d 2ralbidv
      imbi2d anbi12d elab bitri biimpi simpld nnnn0d nn0zd leidd nn0addcld 1le1
      nn0sub nnm1nn0 ad3antlr neqne ad2antlr leltned 3ad2ant3 zltp1led 3ad2ant2
      zleltp1 simp2 lesub1dd recnd pncand eqbrtrd ad5ant135 ltm1d simprd breq1d
      breq1 imbi12d breq2 breq2d rspc2va mpd posdifd 0zd zltlem1d elnn0z sylibr
      eqid fmptd fvoveq1d cbvsum cuz 1p0e1 eqtr4i le2addd nn0cnd fsumm1 sumeq1d
      0le1 iftrued ltp1d lelttrd simp3 ltlend 3expa fsumsub nncnd eqeltrd fsum1
      eluz 3eqtrd nnuz eleqtrd 3adantl3 iftrue fsum1p lep1d ffvelcdmda fsumshft
      npcand mpdan ex eleq2d imbi1d imp telfsum2 pncan3d leloed orcomd mpjaodan
      wo chash fsumconst hashfz1 mulridd addridd 0cnd addcomd subsub2d subsub4d
      subidd addsubassd eleq1d fsumzcl addcld addlsub mptex simpl simp1 eluzfz1
      ovex ltletrd ltled hashfzp1 fsumcl addsubd nncand addassd cbvmpt wfn ffnd
      oveq1 dffn5 ralrimiva ) AQUHZLUIZKUIZVVQUJQEAVVQEUKZULZVVSUEUMMUNUOZUEUHZ
      VVQUIZUPZVVQVWAVVSJUMMUMUQUOZUNUOZJUHZVWFUJZNMUQUOZMVVQUIZVCUOZVWHUMUJZUM
      VVQUIZUMVCUOZVWHVVQUIZVWHUMVCUOZVVQUIZVCUOZUMVCUOZURZURZUPZKUIZVWEVWAVVRV
      XCKVWAPVVQMUSUJZUMNUUCUUDZJVWGVWIVWJMPUHZUIZVCUOZVWMUMVXGUIZUMVCUOZVWHVXG
      UIZVWQVXGUIZVCUOZUMVCUOZURZURZUPZURZVXCELUTLPEVXSUPUJVWAUBVAVWAVXGVVQUJZU
      LZVXSVXRVXCVYAVXEVXFVXRAVXEVDVVTVXTAMUSAUSMAUSMAUUEZAMTUUFVBVEVFVGVHVYAJV
      WGVXQVXBVYAVXQVXBUJZVWHVWGUKZVXTVYCVWAVXTVWIVXIVWLVXPVXAVXTVXHVWKVWJVCMVX
      GVVQVIVJVXTVWMVXKVWOVXOVWTVXTVXJVWNUMVCUMVXGVVQVIVKVXTVXNVWSUMVCVXTVXLVWP
      VXMVWRVCVWHVXGVVQVIVWQVXGVVQVIVNVKUUGUUGVLVMUUHVOAVVTVPVWAJVWGVXBVQVWAUMV
      WFUUIUUJVRVSVWAVXDIVWBIUHZUMVYEUNUOZRUHZVXCUIZRVTZUQUOZUPZVWEVWAOVXCIVWBV
      YEVYFVYGOUHZUIZRVTZUQUOZUPZVYKDKUTKODVYPUPUJVWAUAVAVYLVXCUJZVYPVYKUJVWAVY
      QIVWBVYOVYJVYQVYEVWBUKZULZVYNVYIVYEUQVYSVYFVYMVYHRVYSVYGVYFUKZULVYGVYLVXC
      VYQVYRVYTUUKUULWAVJUUHVLVWAVXCVWGWBGUHZWGZVWGHUHZWUAUIZHVTZNUJZULZGUUMZDV
      WAVXCWUHUKZVWGWBVXCWGZVWGWUCVXCUIZHVTZNUJZULZVWAWUJWUMVWAJVWGVXBWBVXCVWIV
      WLWBUKZVXAWBUKZVXBWBUKVWAVYDULZVWLVXAVWLVXBWBWCVXAVXBWBWCWUQVWIULZVWKVWJW
      DWEZWUOWUQWUSVWIVWAWUSVYDVWAVWKUMVWJUNUOZUKZWUSVWAVWBWUTMVVQVWAVWBWUTVVQW
      GZBUHZCUHZWHWEZWVCVVQUIZWVDVVQUIZWHWEZWIZCVWBWFBVWBWFZVVTWVBWVJULZAVVTWVK
      VVTVVQVWBWUTFUHZWGZWVEWVCWVLUIZWVDWVLUIZWHWEZWIZCVWBWFBVWBWFZULZFUUMZUKWV
      KEWVTVVQUDUUNWVSWVKFVVQQUUOWVLVVQUJZWVMWVBWVRWVJVWBWUTWVLVVQUUPWWAWVQWVIB
      CVWBVWBWWAWVPWVHWVEWWAWVNWVFWVOWVGWHWVCWVLVVQVIWVDWVLVVQVIUUQUUSUURUUTUVA
      UVBUVCVLZUVDZVWAMUMMAUMWJUKZVVTAWTZVMZAMWJUKZVVTAMAMTUVEZUVFZVMZWWJAUMMWD
      WEZVVTAMTWKZVMZAMMWDWEZVVTAMAMTWLZUVGZVMWMWNZVWKUMVWJWOWPVMVMWURVWKWBUKZV
      WJWBUKWUSWUOWQWUQWWRVWIVWAWWRVYDVWAWVAWWRWWQWVAVWKVWKVWJWRZUVEWPVMVMWURNM
      ANWBUKVVTVYDVWISWSAMWBUKZVVTVYDVWIWWHWSUVHVWKVWJUVJXAXBVWMVWOWBUKZVWTWBUK
      ZWUPWUQVWIVDZULZVWOVWTVWOVXAWBWCVWTVXAWBWCWXDWXAVWMWUQWXAWXCVWAWXAVYDVWAV
      WNXCUKZWXAVWAVWNWUTUKZWXEVWAVWBWUTUMVVQWWCVWAUMUMMWWFWWJWWFUMUMWDWEVWAUVI
      VAWWMWMZWNVWNVWJWRZWPZVWNUVKWPVMVMVMWXDVWMVDZULZVWTWJUKZUSVWTWDWEZULWXBWX
      KWXLWXMWXKVWSUMWXKVWPVWRWXKVWPWUTUKZVWPWJUKZWXKVWBWUTVWHVVQVWAWVBVYDWXCWX
      JWWCWSZWXKVWHUMMWXKWTZVWAWWGVYDWXCWXJWWJWSVYDVWHWJUKZVWAWXCWXJVYDVWHVWHVW
      FWRZXDZUVLVYDUMVWHWDWEZVWAWXCWXJVWHUMVWFXEZUVLWXDVWHMWDWEZWXJWXDWYCVWHVWF
      WHWEZWXDWYDVWFVWHXFWXDVWHVWFWXCVWHVWFXFWUQVWHVWFUVMVLVEWXDVWHVWFWXDVWHVYD
      VWHXCUKZVWAWXCWXSUVNZWLWXDMUMAMXLUKZVVTVYDWXCWWOWSWXDXGXHVYDVWHVWFWDWEZVW
      AWXCVWHUMVWFWOZUVNUVOXIWXDWXRWWGWYCWYDWQVYDWXRVWAWXCWXTUVNVWAWWGVYDWXCWWJ
      VGVWHMUVSXAXIVMWMZWNWXNVWPVWPVWJWRXDZWPZWXKVWRWXKVWRWUTUKZVWRXCUKZWXKVWBW
      UTVWQVVQWXPAVYDWXJVWQVWBUKZVVTWXCAVYDWXJXMZVWQUMMWYPWTZAVYDWXJWWGAWWGVYDW
      XJWWIVGXJWYPVWHUMAVYDWXJWXRAVYDULWXRWXJVYDWXRAWXTVLVMXJZWYQXKZWYPUMUMUQUO
      ZVWHWDWEZUMVWQWDWEZWYPUMVWHWHWEZXUAWYPXUCVWHUMXFZWXJAXUDVYDVWHUMUVMZUVPWY
      PUMVWHAVYDUMXLUKZWXJAXGZXNZWYPVWHWYRXOZWYPVYDWYAAVYDWXJUVTWYBWPUVOXIWYPUM
      VWHWYQWYRUVQXBWYPXUFXUFVWHXLUKXUAXUBWQXUHXUHXUIUMUMVWHXPXQXBWYPVWQVWFUMVC
      UOZMWYPVWQWYSXOWYPVWFUMWYPMUMAVYDWYGWXJWWOXNZWYPXGZXHZXULXRXUKWYPVWHVWFUM
      XUIXUMXULVYDAWYHWXJWYIUVRUWAWYPXUJMMWDWYPMUMAVYDMXSUKZWXJAMWWOUWBZXNWYPXT
      UWCAVYDWWNWXJWWPXNUWDYAWMUWEZWNVWRVWJWRZWPZXDXKZWXQXKWXKUSVWSWHWEZWXMWXKV
      WRVWPWHWEZXUTWXKVWQVWHWHWEZXVAWXKVWHWXKVWHWXDWYEWXJWYFVMWLUWFWXKWYOVWHVWB
      UKZULWVJXVBXVAWIZWXKWYOXVCXUPWYJYBVWAWVJVYDWXCWXJVWAWVBWVJWWBUWGWSWVIXVDV
      WQWVDWHWEZVWRWVGWHWEZWIBCVWQVWHVWBVWBWVCVWQUJZWVEXVEWVHXVFWVCVWQWVDWHUWIX
      VGWVFVWRWVGWHWVCVWQVVQYDUWHUWJWVDVWHUJZXVEXVBXVFXVAWVDVWHVWQWHUWKXVHWVGVW
      PVWRWHWVDVWHVVQYDUWLUWJUWMXAUWNWXKVWRVWPWXKVWRXURWLWXKVWPWYLXOUWOXBWXKUSV
      WSWXKUWPXUSUWQXBYBVWTUWRUWSYCYCZVXCUWTUXAVWAWULVWGWUCVWFUJZVWLWUCUMUJZVWO
      WUCVVQUIZWUCUMVCUOVVQUIZVCUOZUMVCUOZURZURZHVTZNVWAVWGWUKXVQHVWAWUCVWGUKZU
      LZJWUCVXBXVQVWGVXCUTXVTVXCYEXVTVWHWUCUJZULZVWIXVJVXAXVPVWLXWBVWHWUCVWFXVT
      XWAVPZYFXWBVWMXVKVWTXVOVWOXWBVWHWUCUMXWCYFXWBVWSXVNUMVCXWBVWPXVLVWRXVMVCX
      WBVWHWUCVVQXWCVSXWBVWHWUCUMVVQVCXWCUXBVNVKYGYGVWAXVSVPXVTXVJVWLXVPUTXVTVW
      JVWKVCYHXVTXVKVWOXVOUTXVTVWNUMVCYHXVTXVNUMVCYHYIYIVRWAVWAXVRVWGVXBJVTZNXV
      RXWDUJVWAVWGXVQVXBHJWUCVWHUJZXVJVWIXVPVXAVWLWUCVWHVWFYJXWEXVKVWMXVOVWTVWO
      WUCVWHUMYJXWEXVNVWSUMVCXWEXVLVWPXVMVWRVCWUCVWHVVQYDWUCVWHUMVVQVCYKVNVKYGY
      GJXVQYLHVXBYLUXCVAVWAXWDUMXUJUNUOZVXBJVTZVWFVWFUJZVWLVWFUMUJZVWOVWFVVQUIZ
      XUJVVQUIZVCUOZUMVCUOZURZURZUQUOZNVWAVXBXWOJUMVWFAVWFUMUXDUIZUKZVVTAXWRUMV
      WFWDWEZAUMUMUSUQUOZVWFWDUMXWTUJAUMUMXWTUMUWTZUXEUXFVAAUMUSMUMXUGVYBWWOXUG
      WWLUSUMWDWEAUXKVAUXGUWDAWWDVWFWJUKXWRXWSWQWWEAMWWIYOUMVWFUYBXAXIVMWUQVXBX
      VIUXHVWIVWIXWHVXAXWNVWLVWHVWFVWFYJVWIVWMXWIVWTXWMVWOVWHVWFUMYJVWIVWSXWLUM
      VCVWIVWPXWJVWRXWKVCVWHVWFVVQYDVWHVWFUMVVQVCYKVNVKYGYGUXIVWAXWPVWBVXBJVTZV
      WLUQUOZNVWAXWGXXBXWOVWLUQVWAXWFVWBVXBJVWAXUJMUMUNVWAMUMAXUNVVTXUOVMZVWAXT
      ZUWCVJUXJVWAXWHVWLXWNVWAVWFYEUXLVNVWAXXCNNVWAXXCNUJXXBNVWLVCUOZUJVWAXXBVW
      BVXAJVTZXXFVWAVWBVXBVXAJVWAXVCULZVWIVWLVXAXXHVWHVWFXXHVWHVWFXXHVWHXVCWXRV
      WAVWHUMMYMVLZXOZXXHVWHMVWFXXJAWYGVVTXVCWWOVGZXXHMUMXXKXXHXGXHXVCWYCVWAVWH
      UMMWOZVLXXHMXXKUXMUXNVBVFVHZWAVWAXXGNNMVWKVCUOZUQUOZVCUOZXXFVWAXXGNNVCUOZ
      XXNVCUOZXXPVWAXXGUSXXNVCUOZXXRVWAXXGUSVWKMVCUOZUQUOZXXSVWAXXGXXTXYAVWAXXG
      VWBVWMVWNVWSURZUMVCUOZJVTZXXTVWAVWBVXAXYCJVWMVWOXYCUJVWTXYCUJVXAXYCUJXXHV
      WOVWTVWOVXAXYCYJVWTVXAXYCYJXXHVWMULZVWNXYBUMVCXYEXYBVWNXYEVWMVWNVWSXXHVWM
      VPUXLYNVKXXHWXJULZVWSXYBUMVCXYFXYBVWSXYFVWMVWNVWSXXHWXJVPVHYNVKYCWAVWAXYD
      VWBXYBJVTZVWBUMJVTZVCUOXXTVWAVWBXYBUMJVWAUMMUUIZXXHXYBAVVTXVCXYBWJUKZVWMV
      WNWJUKZVWSWJUKXYJAVVTXVCXMZVWNVWSVWNXYBWJWCVWSXYBWJWCXYLXYKVWMXYLWXFXYKXY
      LVWBWUTUMVVQAVVTWVBXVCWWCYPZAVVTUMVWBUKZXVCWXGYPWNWXFVWNWXHXDWPZVMXYLWXJU
      LZVWPVWRXYLWXOWXJXYLWXNWXOXYLVWBWUTVWHVVQXYMAVVTXVCUXOZWNWYKWPVMXYPVWRXYP
      WYMWYNXYPVWBWUTVWQVVQXYLWVBWXJXYMVMXYPVWQUMMXYPWTZXYLWWGWXJAVVTWWGXVCWWJY
      PVMZXYPVWHUMXYLWXRWXJAVVTXVCWXRXXIXJVMZXYRXKZXYPXUCXUBXYPXUCWYAXUDULXYPWY
      AXUDXYLWYAWXJXYLXVCWYAXYQVWHUMMXEWPVMWXJXUDXYLXUEVLYBXYPUMVWHXYPXGXYPVWHX
      YTXOZUXPXIXYPUMVWHXYRXYTUWQXBXYPVWQVWHMXYPVWQYUAXOYUBXYPMXYSXOXYPVWHYUBYQ
      XYLWYCWXJXYLXVCWYCXYQXXLWPVMYAWMWNXUQWPXDXKZYCUXQYRZVWAUMXSUKZXVCXXEVMUXR
      VWAXYGVWKXYHMVCVWAUMMUJZXYGVWKUJZUMMWHWEZVWAYUFULZXYGUMUMUNUOZXYBJVTZVWNV
      WKYUIVWBYUJXYBJYUIYUJVWBYUIUMMUMUNVWAYUFVPVJYNUXJVWAYUKVWNUJYUFVWAYUKUMUM
      UJZVWNVWNUMUMVCUOVVQUIZVCUOZURZVWNVWAWWDYUOXSUKYUKYUOUJVWAWTVWAYUOVWNXSVW
      AYULVWNYUNYULVWAXXAVAUXLZVWAVWNWXIUXSZUXTXYBYUOJUMVWMVWMYULVWSYUNVWNVWHUM
      UMYJVWMVWPVWNVWRYUMVCVWHUMVVQYDVWHUMUMVVQVCYKVNYGUYAXAYUPVOVMYUFVWNVWKUJV
      WAUMMVVQYDVLUYCAVVTYUHYUGAVVTYUHXMZXYGVWNWYTMUNUOZXYBJVTZUQUOZVWKYURXYBVW
      NJUMMYURMXCXWQAVVTMXCUKYUHTXNXCXWQUJYURUYDVAUYEZAVVTXVCXYBXSUKYUHYUDUYFVW
      MVWNVWSUYGUYHYURYVAVWNYUSVWSJVTZUQUOZVWKYURYUTYVCVWNUQYURYUSXYBVWSJYURVWH
      YUSUKZULZVWMVWNVWSYVFVWHUMYVFUMVWHYVFUMVWHYVFXGYVFXUCXUAYVEXUAYURVWHWYTMX
      EVLYVFUMVWHYVFWTYVEWXRYURVWHWYTMYMVLUVQXIVBVEVFVHWAVJYURYVDVWNWYTMUMVCUOZ
      UMUQUOZUNUOZVWSJVTZUQUOZVWKYURYVCYVJVWNUQYURYUSYVIVWSJYURMYVHWYTUNYURYVHM
      YURMUMAVVTXUNYUHXXDYPYURXTUYLZYNVJUXJVJYURYVKVWNYVIVWQUMUQUOZVVQUIZVWRVCU
      OZJVTZUQUOZVWKYURYVJYVPVWNUQYURYVIVWSYVOJYURVWHYVIUKZULZVWPYVNVWRVCYVSVWH
      YVMVVQYVSYVMVWHYVSVWHUMYVSVWHYVRWXRYURVWHWYTYVHYMVLYRYVSXTUYLYNVSVKWAVJYU
      RYVQVWNUMYVGUNUOZUFUHZUMUQUOZVVQUIZYWAVVQUIZVCUOZUFVTZUQUOZVWKYURYVPYWFVW
      NUQYURYWFYVPYURYWEYVOUFJUMUMYVGAVVTWWDYUHWWFYPZYWHYURMUMAVVTWWGYUHWWJYPZY
      WHXKZYURYWAYVTUKZULZYWEYWLYWCYWDYWLYWCYWLYWCWUTUKYWCXCUKYWLVWBWUTYWBVVQYU
      RWVBYWKAVVTWVBYUHWWCYPVMZYWLYWBUMMYWLWTZYURWWGYWKYWIVMZYWLYWAYWLYWAYWKYWA
      XCUKYURYWAYVGWRVLZXDZYOZYWLUMYWAYWBYWLXGZYWLYWAYWPWLZYWLYWBYWRXOYWLYWAYWP
      WKZYWLYWAYWTUYIYAYWLYWBMWDWEZYWAYVGWDWEZYWKYXCYURYWAUMYVGWOVLZYWLYWAXLUKX
      UFWYGYXBYXCWQYWTYWSYWLMYWOXOZYWAUMMXPXQXIWMWNYWCVWJWRWPXDYWLYWDYWLYWDWUTU
      KZYWDXCUKYWLYWAVWBUKYXFYWLYWAUMMYWNYWOYWQYXAYWLYWAYVGMYWTYWLMUMYXEYWSXRYX
      EYXDYWLMYXEYQYAWMYWLVWBWUTYWAVVQYWMUYJUYMYWDVWJWRWPXDXKYRYWAVWQUJYWCYVNYW
      DVWRVCYWAVWQUMVVQUQYKYWAVWQVVQYDVNUYKYNVJYURYWGVWNYVHVVQUIZVWNVCUOZUQUOZV
      WKYURYWFYXHVWNUQYURUUAUHZVVQUIZYWDYWCVWNUFUUAYXGUMYVGYXJYWAVVQYDYXJYWBVVQ
      YDYXJUMVVQYDYXJYVHVVQYDYWJYURYVHMXWQYVLYVBUXTYURYXJUMYVHUNUOZUKZULZYXKYXN
      YXKWUTUKZYXKXCUKYURYXMYXOYURYXMYXOWIYXJVWBUKZYXOWIYURYXPYXOYURVWBWUTYXJVV
      QAVVTYUHWVBVWAWVBYUHWWCVMXJUYJUYNYURYXMYXPYXOYURYXLVWBYXJYURYVHMUMUNYVLVJ
      UYOUYPXIUYQYXKVWJWRWPUXSUYRVJYURYXIVWNVWKVWNVCUOZUQUOZVWKYURYXHYXQVWNUQYU
      RYXGVWKVWNVCYURYVHMVVQYVLVSVKVJYURYXRVWKVWKYURVWNVWKAVVTVWNXSUKYUHYUQYPAV
      VTVWKXSUKYUHVWAVWKVWAWVAVWKXCUKWWQWWSWPUXSZYPUYSYURVWKYEVOVOVOVOVOVOVOVOU
      XQVWAYUHYUFVWAWWKYUHYUFVUCWWMVWAUMMAXUFVVTXUGVMAWYGVVTWWOVMUYTXBVUAVUBVWA
      XYHVWBVUDUIZUMYSUOZMVWAVWBVQUKYUEXYHYYAUJXYIXXEVWBUMJVUEXAVWAYYAMUMYSUOMV
      WAYXTMUMYSVWAWWTYXTMUJAWWTVVTWWHVMMVUFWPVKVWAMXXDVUGVOVOVNVOVOVWAXXTXXTUS
      UQUOZXYAVWAYYBXXTVWAXXTVWAVWKMYXSXXDYTZVUHYNVWAXXTUSYYCVWAVUIZVUJVOVOVWAX
      XSXYAVWAUSMVWKYYDXXDYXSVUKYNVOVWAUSXXQXXNVCVWAXXQUSVWANANXSUKVVTANSUXHVMZ
      VUMYNVKVOVWANNXXNYYEYYEVWAMVWKXXDYXSYTVULVOVWAXXOVWLNVCVWAVWLXXOVWANMVWKY
      YEXXDYXSVUNYNVJVOVOVWAXXBVWLNVWAXXBVWAVWBVXBJXYIXXHVXBWJUKVXAWJUKZAVVTXVC
      YYFVWMVWOWJUKZWXLYYFXYLVWOVWTVWOVXAWJWCVWTVXAWJWCXYLYYGVWMXYLVWNUMXYOXYLW
      TZXKVMXYPVWSUMYUCXYLWWDWXJYYHVMXKYCUXQXXHVXBVXAWJXXMVUOXIVUPYRVWAVWJVWKVW
      ANMYYEXXDVUQYXSYTYYEVURXIVWANYEVOVOVOVOVOYBWUIWUNWQVWAWUGWUNGVXCJVWGVXBUM
      VWFUNVVCVUSWUAVXCUJZWUBWUJWUFWUMVWGWBWUAVXCUUPYYIWUEWULNYYIVWGWUDWUKHYYIX
      VSULWUCWUAVXCYYIXVSVUTUULWAYFUUTUVAVAXIVWADWUHDWUHUJVWAUCVAYNUYEVWAIVWBVY
      JVQXYIUUJVRVWAVYKIVWBVYEVVQUIZUPZVWEVWAIVWBVYJYYJAVVTVYRVYJYYJUJAVVTVYRXM
      ZVYJVYEVYFVYGVWFUJZVWLVYGUMUJZVWOVYGVVQUIZVYGUMVCUOZVVQUIZVCUOZUMVCUOZURZ
      URZRVTZUQUOZYYJYYLVYIUUUBVYEUQYYLVYFVYHUUUARYYLVYTULZJVYGVXBUUUAVWGVXCUTU
      UUDVXCYEUUUDVWHVYGUJZULZVWIYYMVXAYYTVWLUUUFVWHVYGVWFUUUDUUUEVPZYFUUUFVWMY
      YNVWTYYSVWOUUUFVWHVYGUMUUUGYFUUUFVWSYYRUMVCUUUFVWPYYOVWRYYQVCUUUFVWHVYGVV
      QUUUGVSUUUFVWQYYPVVQUUUFVWHVYGUMVCUUUGVKVSVNVKYGYGUUUDVYGUMVWFUUUDWTZUUUD
      MYYLWWGVYTAVVTWWGVYRWWIXNVMYOZVYTVYGWJUKZYYLVYGUMVYEYMVLZVYTUMVYGWDWEZYYL
      VYGUMVYEXEVLUUUDVYGVYEVWFUUUDVYGUUUKXOYYLVYEXLUKZVYTYYLVYEYYLVYRVYEXCUKZA
      VVTVYRUXOZVYEMWRWPZWLZVMUUUDVWFUUUIXOVYTVYGVYEWDWEZYYLVYGUMVYEWOVLZYYLVYE
      VWFWDWEVYTYYLVYEMVWFUUUQAVVTWYGVYRWWOXNZYYLMUMUUUTYYLXGXHYYLVYRVYEMWDWEZU
      UUOVYEUMMWOWPZYYLMUUUTUYIYAVMYAWMUUUDYYMVWLYYTUTUUUDVWJVWKVCYHUUUDYYNVWOY
      YSUTUUUDVWNUMVCYHUUUDYYRUMVCYHYIYIVRWAVJYYLUUUCVYEVYFYYTRVTZUQUOZYYJYYLUU
      UBUUVCVYEUQYYLVYFUUUAYYTRUUUDYYMVWLYYTUUUDVYGVWFUUUDVYGVWFUUUDVYGVYTVYGXC
      UKYYLVYGVYEWRVLZWLZUUUDVYGMVWFUUVFYYLWYGVYTUUUTVMZUUUDMUMUUVGUUUDXGZXHUUU
      DVYGVYEMUUVFUUUDVYEYYLUUUNVYTUUUPVMWLUUVGUUUSYYLUUVAVYTUUVBVMYAZUUUDMUUVG
      UXMUXNVBVFVHWAVJYYLUUVDVYEVWOWYTVYEUNUOZYYTRVTZUQUOZUQUOZYYJYYLUUVCUUVLVY
      EUQYYLYYTVWORUMVYEYYLVYEXWQUKZUMVYEWDWEZYYLVYEUUUPWKYYLWWDVYEWJUKUUVNUUVO
      WQAVVTWWDVYRWWEXNZYYLVYEUUUPXDZUMVYEUYBXAXIZYYNVWOXSUKZYYSXSUKYYTXSUKUUUD
      VWOYYSVWOYYTXSWCYYSYYTXSWCUUUDUUVSYYNYYLUUVSVYTYYLVWOYYLVWNUMYYLVWNYYLWXF
      WXEYYLVWBWUTUMVVQAVVTWVBVYRWWCYPZYYLMXWQUKZXYNYYLUUWAWWKYYLAWWKAVVTVYRVVA
      ZWWLWPYYLWWDWWGUUWAWWKWQUUVPYYLAWWGUUWBWWIWPZUMMUYBXAXIUMMVVBWPWNWXHWPZXD
      UUVPXKYRZVMVMUUUDYYNVDZULZYYSUUWGYYRUMUUWGYYOYYQUUUDYYOWJUKZUUWFUUUDYYOWU
      TUKZUUWHUUUDVWBWUTVYGVVQYYLWVBVYTUUVTVMZUUUDVYGUMMUUUHYYLWWGVYTUUWCVMZUUU
      DVYGUUVEXDZUUUDVYGUUVEWKZUUVIWMWNYYOUMVWJYMZWPVMUUWGYYQWUTUKZYYQWJUKUUWGV
      WBWUTYYPVVQUUUDWVBUUWFUUWJVMUUWGYYPUMMUUWGWTZUUUDWWGUUWFUUWKVMUUWGVYGUMUU
      UDUUUJUUWFUUWLVMZUUWPXKZUUWGUMVYGWHWEZUMYYPWDWEZUUWGUUWSVYGUMXFZUUWFUUXAU
      UUDVYGUMUVMVLUUWGUMVYGUUUDXUFUUWFUUVHVMUUUDVYGXLUKZUUWFUUVFVMZUUUDUUULUUW
      FUUWMVMUVOXIUUWGUMVYGUUWPUUWQUWQXBUUWGYYPVYGMUUWGYYPUUWRXOUUXCUUUDWYGUUWF
      UUVGVMUUWGVYGUUXCYQUUUDVYGMWDWEUUWFUUVIVMYAWMWNYYQUMVWJYMZWPXKUUWPXKYRYCY
      YNVWOYYSUYGUYHVJYYLUUVMVYEVWOUUVJYYSRVTZUQUOZUQUOZYYJYYLUUVLUUXFVYEUQYYLU
      UVKUUXEVWOUQYYLUUVJYYTYYSRYYLVYGUUVJUKZULZYYNVWOYYSUUXIVYGUMUUXIUMVYGUUXI
      UMVYGYYLXUFUUXHYYLAXUFUUWBXUGWPZVMZUUXIUMWYTVYGUUXKUUXIUMUMUUXKUUXKXHZUUX
      IVYGUUXHUUUJYYLVYGWYTVYEYMVLZXOZUUXIUMUUXKUXMZUUXHWYTVYGWDWEZYYLVYGWYTVYE
      XEVLZVVDVBVEVFVHWAVJVJYYLUUXGVYEVWOUUVJYYRRVTZUUVJUMRVTZVCUOZUQUOZUQUOZYY
      JYYLUUXFUUYAVYEUQYYLUUXEUUXTVWOUQYYLUUVJYYRUMRYYLWYTVYEUUIZUUXIYYOYYQUUXI
      YYOUUXIUUWIUUWHUUXIVWBWUTVYGVVQYYLWVBUUXHUUVTVMZUUXIVYGUMMUUXIWTZYYLWWGUU
      XHUUWCVMZUUXMUUXIUMWYTVYGUUXKUUXLUUXNUUXIUMWYTUUXKUUXLUUXOVVEUUXQYAUUXIVY
      GVYEMUUXNYYLUUUMUUXHUUUQVMYYLWYGUUXHUUUTVMZUUXHUUURYYLVYGWYTVYEWOVLYYLUUV
      AUUXHUUVBVMYAZWMWNUUWNWPYRUUXIUUWOYYQXSUKUUXIVWBWUTYYPVVQUUYDUUXIYYPUMMUU
      YEUUYFUUXIVYGUMUUXMUUYEXKUUXIUUXPUUWTUUXQUUXIXUFXUFUUXBUUXPUUWTWQUUXKUUXK
      UUXNUMUMVYGXPXQXBUUXIYYPVYGMUUXIVYGUMUUXNUUXKXRUUXNUUYGUUXIVYGUUXNYQUUYHY
      AWMWNUUWOYYQUUXDYRWPYTZUUXIXTZUXRVJVJYYLUUYBVYEVWOUUXRVYEUMVCUOZVCUOZUQUO
      ZUQUOZYYJYYLUUYAUUYMVYEUQYYLUUXTUUYLVWOUQYYLUUXSUUYKUUXRVCYYLUUXSUUVJVUDU
      IZUMYSUOZUUYKYYLUUVJVQUKYUEUUXSUUYPUJUUYCYYLXTZUUVJUMRVUEXAYYLUUYPUUYKUMY
      SUOUUYKYYLUUYOUUYKUMYSYYLUUVNUUYOUUYKUJUUVRUMVYEVVFWPVKYYLUUYKYYLVYEUMYYL
      VYEUUUPUXSZUUYQYTZVUGVOVOVJVJVJYYLUUYNVYEVWOUUXRUQUOZUUYKVCUOZUQUOZYYJYYL
      UUYMUVUAVYEUQYYLUVUAUUYMYYLVWOUUXRUUYKUUWEYYLUUVJYYRRUUYCUUYIVVGZUUYSVUNY
      NVJYYLUVUBVYEUUYTUQUOUUYKVCUOZYYJYYLUVUDUVUBYYLVYEUUYTUUYKUUYRYYLVWOUUXRU
      UWEUVUCVUQZUUYSVUNYNYYLUVUDVYEUUYKVCUOZUUYTUQUOZYYJYYLVYEUUYTUUYKUUYRUVUE
      UUYSVVHYYLUVUGUMVWOUMUUYKUNUOZVYGUMUQUOZVVQUIZYYOVCUOZRVTZUQUOZUQUOZYYJYY
      LUVUFUMUUYTUVUMUQYYLVYEUMUUYRUUYQVVIYYLUUXRUVULVWOUQYYLUVULUUXRYYLUVULWYT
      UUYKUMUQUOZUNUOZYYPUMUQUOZVVQUIZYYQVCUOZRVTZUUXRYYLUVULUVUPUGUHZUMVCUOZUM
      UQUOVVQUIZUVVBVVQUIZVCUOZUGVTZUVUTYYLUVUKUVVERUGUMUMUUYKYYLWTZUVVGYYLVYEU
      MUUVQUUVPXKZYYLVYGUVUHUKZULZUVUKUVVJUVUJYYOUVVJUVUJWUTUKUVUJWJUKUVVJVWBWU
      TUVUIVVQYYLWVBUVVIUUVTVMZUVVJUVUIUMMUVVJWTZYYLWWGUVVIUUWCVMZUVVJVYGUVVIUU
      UJYYLVYGUMUUYKYMVLZYOUVVJUMVYGUVUIUVVJXGZUVVJVYGUVVNXOZUVVJVYGUMUVVPUVVOX
      HUVVIUUULYYLVYGUMUUYKXEVLZUVVJVYGUVVPUYIYAUVVJUVUIMWDWEZVYGYVGWDWEZUVVJVY
      GUUYKYVGUVVPUVVJVYEUMYYLUUUMUVVIUUUQVMZUVVOXRZUVVJMUMYYLWYGUVVIUUUTVMZUVV
      OXRUVVIVYGUUYKWDWEYYLVYGUMUUYKWOVLZUVVJVYEMUMUVVTUVWBUVVOYYLUUVAUVVIUUVBV
      MUWAYAUVVJUUXBXUFWYGUVVRUVVSWQUVVPUVVOUVWBVYGUMMXPXQXIWMWNUVUJUMVWJYMWPUV
      VJUUWIUUWHUVVJVWBWUTVYGVVQUVVKUVVJVYGUMMUVVLUVVMUVVNUVVQUVVJVYGUUYKMUVVPU
      VWAUVWBUVWCYYLUUYKMWDWEUVVIYYLUUYKVYEMYYLVYEUMUUUQUUXJXRUUUQUUUTYYLVYEUUU
      QYQUUVBYAVMYAWMWNUUWNWPXKYRVYGUVVBUJUVUJUVVCYYOUVVDVCVYGUVVBUMVVQUQYKVYGU
      VVBVVQYDVNUYKUVVFUVUTUJYYLUVUPUVVEUVUSUGRUVVAVYGUJZUVVCUVURUVVDYYQVCUVWDU
      VVBYYPUMVVQUQUVVAVYGUMVCVVNZUXBUVWDUVVBYYPVVQUVWEVSVNRUVVEYLUGUVUSYLUXCVA
      VOYYLUVUTUUVJUVUSRVTUUXRYYLUVUPUUVJUVUSRYYLUVUOVYEWYTUNYYLVYEUMUUYRUUYQUY
      LZVJUXJYYLUUVJUVUSYYRRUUXIUVURYYOYYQVCUUXIUVUQVYGVVQUUXIVYGUMUUXIVYGUUXNU
      WBUUYJUYLVSVKWAVOVOYNVJVNYYLUVUNUMVWOUVUOVVQUIZVWNVCUOZUQUOZUQUOZYYJYYLUV
      UMUVWIUMUQYYLUVULUVWHVWOUQYYLUUBUHZVVQUIZYYOUVUJVWNRUUBUVWGUMUUYKUVWKVYGV
      VQYDUVWKUVUIVVQYDUVWKUMVVQYDUVWKUVUOVVQYDUVVHYYLUVUOVYEXWQUVWFUUVRUXTYYLU
      VWKUMUVUOUNUOUKZULZUVWLUVWNUVWLWUTUKUVWLWJUKUVWNVWBWUTUVWKVVQYYLWVBUVWMUU
      VTVMUVWNUVWKUMMUVWNWTYYLWWGUVWMUUWCVMUVWMUVWKWJUKYYLUVWKUMUVUOYMVLZUVWMUM
      UVWKWDWEYYLUVWKUMUVUOXEVLUVWNUVWKUVUOMUVWNUVWKUVWOXOUVWNUUYKUMUVWNVYEUMYY
      LUUUMUVWMUUUQVMUVWNXGZXRUVWPXHYYLWYGUVWMUUUTVMUVWMUVWKUVUOWDWEYYLUVWKUMUV
      UOWOVLYYLUVUOMWDWEUVWMYYLUVUOVYEMWDUVWFUUVBUWDVMYAWMWNUVWLUMVWJYMWPYRUYRV
      JVJYYLUVWJUMVWOUQUOZUVWHUQUOZYYJYYLUVWRUVWJYYLUMVWOUVWHUUYQUUWEYYLUVWGVWN
      YYLUVWGYYLUVWGYYJWJYYLUVUOVYEVVQUVWFVSZYYLYYJWUTUKYYJWJUKYYLVWBWUTVYEVVQU
      UVTUUUOWNYYJUMVWJYMWPUXTYRZYYLVWNYYLVWNUUWDWLUWBZYTVVJYNYYLUVWRVWNUVWHUQU
      OZYYJYYLUVWQVWNUVWHUQYYLUMVWNUUYQUVXAUYSVKYYLUVXBUVWGYYJYYLVWNUVWGUVXAUVW
      TUYSUVWSVOVOVOVOVOVOVOVOVOVOVOVOVOVOUXQUUHYYKVWEUJVWAIUEVWBYYJVWDUEYYJYLI
      VWDYLVYEVWCVVQYDVVKVAVOVOVOVWAVVQVWEVWAVVQVWBVVLZVVQVWEUJZVWAVWBWUTVVQWWC
      VVMUVXCUVXDUEVWBVVQVVOUVCWPYNVOVVP $.
  $}

  ${
    $d A a c j k l $.  $d A b c k $.  $d A a j k l x y $.  $d B a d i k l $.
    $d B b d k $.  $d B a d j k l $.  $d F b c k $.  $d F b d k $.  $d G c $.
    $d G d $.  $d K a f j l x y $.  $d K b k $.  $d K a g i k $.
    $d N a f j l $.  $d N b k $.  $d N a g i k $.  $d a c i k l ph $.
    $d b c k ph $.  $d c g i k $.  $d d f j l x y $.  $d d g i k $.
    $d d i k l ph $.  $d j k l ph x y $.  $d B b d i k $.  $d K b f x y $.
    $d N b f $.  $d b c g i k $.  $d b c i k ph $.
    sticksstones12.1 $e |- ( ph -> N e. NN0 ) $.
    sticksstones12.2 $e |- ( ph -> K e. NN ) $.
    sticksstones12.3 $e |- F = ( a e. A |-> ( j e. ( 1 ... K ) |->
    ( j + sum_ l e. ( 1 ... j ) ( a ` l ) ) ) ) $.
    sticksstones12.4 $e |- G = ( b e. B |-> if ( K = 0
     , { <. 1 , N >. } , ( k e. ( 1 ... ( K + 1 ) )
        |-> if ( k = ( K + 1 ) , ( ( N + K ) - ( b ` K ) ) , if
       ( k = 1 , ( ( b ` 1 ) - 1 )
       , ( ( ( b ` k ) - ( b ` ( k - 1 ) ) ) - 1 ) ) ) ) ) ) $.
    sticksstones12.5 $e |- A = { g | ( g : ( 1 ... ( K + 1 ) ) --> NN0 /\
     sum_ i e. ( 1 ... ( K + 1 ) ) ( g ` i ) = N ) } $.
    sticksstones12.6 $e |- B = { f | ( f : ( 1 ... K ) --> ( 1 ... ( N + K ) )
    /\ A. x e. ( 1 ... K ) A. y e. ( 1 ... K ) ( x < y ->
    ( f ` x ) < ( f ` y ) ) ) } $.
    $( Establish bijective mapping between strictly monotone functions and
       functions that sum to a fixed non-negative integer.  (Contributed by
       metakunt, 6-Oct-2024.) $)
    sticksstones12 $p |- ( ph -> F : A -1-1-onto-> B ) $=
      ( vc vd cv cfv wceq wcel wa c1 caddc cfz cmin cif cmpt cvv cc0 a1i necomd
      co 0red adantr mpteq2dva eqtrd fveq1 oveq2d oveq1d oveq12d ifeq12d adantl
      ffvelcdmda cfn fzfid mptexd fvmptd w3a csu simpllr sumeq2dv simpr sumeq1d
      fveq1d 1zzd nnge1d nnred leidd elfzd ovexd cc nn0cnd cz ad2antrr peano2zd
      cn0 elfzelz cle wbr elfzle1 zred cr elfzle2 letrd wf biimpd mpd fsumnn0cl
      wb mpdan 1red eqbrtrd syl2anc mpbird fveq2 fsumm1 1cnd pncand eqcomd nfcv
      simprd 1e0p1 leadd1dd ffvelcdmd subaddd 3adant3 wn eqidd readdcld adantlr
      fveq2d pncan2d cn elfznn 3ad2ant3 nnzd clt wne syl3anc neqne 3ad2ant1 cop
      nnnn0d sticksstones8 sticksstones10 csn nngt0d ltned iffalsed nn0zd recnd
      neneqd addcomd lep1d cab eleq2i bilani vex feq1 simpl eqeq1d anbi12d elab
      simpld pnpcand cuz eqid 1p0e1 eqtr4i 0le1 le2addd eluz cbvsum ltled fsum1
      breqtrd simpll2 simpl3 jca ltlend zleltp1 3impa zsubcld simp2 syl leltned
      elfz zltp1led mpbid leaddsub resubcld 3ad2ant2 lesub1dd 3expa zcnd subcld
      3adantl2 lem1d addsub4d nncand 3jca eluz2 sylibr simp3 ifeqda ffnd biimpi
      wfn dffn5 ralrimiva sticksstones12a 2fvidf1od ) ADEKLUDUEABCDEFGHIKMNOQRA
      MSUUBZTUBUCUUCZABCDEFGHJLMNPRSUAUBUCUUDAUDUFZKUGZLUGZUXNUHUDDAUXNDUIZUJZU
      XPJUKMUKULVAZUMVAZJUFZUXSUHZNMULVAZMUXOUGZUNVAZUYAUKUHZUKUXOUGZUKUNVAZUYA
      UXOUGZUYAUKUNVAZUXOUGZUNVAZUKUNVAZUOZUOZUPZUXNUXRPUXOJUXTUYBUYCMPUFZUGZUN
      VAZUYFUKUYQUGZUKUNVAZUYAUYQUGZUYJUYQUGZUNVAZUKUNVAZUOZUOZUPZUYPELUQALPEVU
      HUPZUHUXQALPEMURUHZUKNUUAUUEZVUHUOZUPZVUILVUMUHAUAUSAPEVULVUHAVULVUHUHUYQ
      EUIAVUJVUKVUHAMURAURMAURMAVBZAMSUUFZUUGUTUUKUUHVCVDVEVCUYQUXOUHZVUHUYPUHU
      XRVUPJUXTVUGUYOVUPVUGUYOUHUYAUXTUIZVUPUYBUYSUYEVUFUYNVUPUYRUYDUYCUNMUYQUX
      OVFVGVUPUYFVUAUYHVUEUYMVUPUYTUYGUKUNUKUYQUXOVFVHVUPVUDUYLUKUNVUPVUBUYIVUC
      UYKUNUYAUYQUXOVFUYJUYQUXOVFVIVHVJVJVCVDVKADEUXNKUXMVLUXRJUXTUYOVMUXRUKUXS
      VNVOVPUXRUYPJUXTUYAUXNUGZUPZUXNUXRJUXTUYOVURAUXQVUQUYOVURUHAUXQVUQVQZUYBU
      YEUYNVURVUTUYBUJZUYEUXSUXNUGZVURVUTUYEVVBUHZUYBAUXQVVCVUQUXRUYEUYCMUKMUMV
      AZQUFZUXNUGZQVRZULVAZUNVAZVVBUXRUYDVVHUYCUNUXRIMIUFZUKVVJUMVAZVVFQVRZULVA
      ZVVHVVDUXOUQUXROUXNIVVDVVJVVKVVEOUFZUGZQVRZULVAZUPZIVVDVVMUPZDKUQKODVVRUP
      UHZUXRTUSUXRVVNUXNUHZUJZIVVDVVQVVMVWBVVJVVDUIZUJZVVPVVLVVJULVWDVVKVVOVVFQ
      VWDVVEVVKUIZUJVVEVVNUXNUXRVWAVWCVWEVSWCVTVGVDAUXQWAUXRIVVDVVMVMUXRUKMVNZV
      OVPZUXRVVJMUHZUJZVVJMVVLVVGULUXRVWHWAZVWIVVKVVDVVFQVWIVVJMUKUMVWJVGWBVIAM
      VVDUIUXQAMUKMAWDZAMUXLUUIZVWLAMSWEZAMAMSWFZWGZWHVCUXRMVVGULWIVPVGUXRVVIMN
      ULVAZVVHUNVAZVVBUXRUYCVWPVVHUNUXRNMANWJUIUXQANRWKVCZAMWJUIZUXQAMVWNUUJZVC
      ZUULVHUXRVWQNVVGUNVAZVVBUXRMNVVGVXAVWRUXRVVGUXRVVDVVFQVWFUXRVVEVVDUIZUJZV
      VEUXTUIZVVFWOUIZVXDVVEUKUXSVXDWDVXDMAMWLUIZUXQVXCVWLWMWNZVXCVVEWLUIZUXRVV
      EUKMWPVKZVXCUKVVEWQWRZUXRVVEUKMWSVKVXDVVEMUXSVXDVVEVXJWTAMXAUIZUXQVXCVWNW
      MZVXDUXSVXHWTVXCVVEMWQWRUXRVVEUKMXBVKVXDMVXMUUMXCWHVXDUXTWOVVEUXNUXRUXTWO
      UXNXDZVXCUXRVXNUXTHUFZUXNUGZHVRZNUHZUXRUXNUXTWOGUFZXDZUXTVXOVXSUGZHVRZNUH
      ZUJZGUUNZUIZVXNVXRUJZUXQVYFADVYEUXNUBUUOUUPUXRVYFVYGVYFVYGXHUXRVYDVYGGUXN
      UDUUQVXSUXNUHZVXTVXNVYCVXRUXTWOVXSUXNUURVYHVYBVXQNVYHUXTVYAVXPHVYHVXOUXTU
      IZUJVXOVXSUXNVYHVYIUUSWCVTUUTUVAUVBUSXEXFZUVCZVCVLXIXGWKZUVDUXRVXBVVBUHVV
      GVVBULVAZNUHUXRVYMUXTVVFQVRZNUXRVYNVYMUXRVYNUKUXSUKUNVAZUMVAZVVFQVRZVVBUL
      VAVYMUXRVVFVVBQUKUXSAUXSUKUVEUGZUIZUXQAVYSUKUXSWQWRZAUKUKURULVAZUXSWQUKWU
      AUHAUKUKWUAUKUVFUVGUVHUSAUKURMUKAXJZVUNVWNWUBVWMURUKWQWRAUVIUSUVJXKAUKWLU
      IZUXSWLUIZVYSVYTXHVWKAMVWLWNUKUXSUVKXLXMVCUXRVXEUJVVFUXRUXTWOVVEUXNVYKVLZ
      WKVVEUXSUXNXNXOUXRVYQVVGVVBULUXRVYPVVDVVFQUXRVYOMUKUMUXRMUKVXAUXRXPZXQVGW
      BVHVEXRUXRVYNVXQNVYNVXQUHUXRUXTVVFVXPQHVVEVXOUXNXNHVVFXSQVXPXSUVLUSUXRVXN
      VXRVYJXTVEVEUXRNVVGVVBVWRVYLUXRVVBUXRUXTWOUXSUXNVYKUXRUXSUKUXSUXRWDZUXRMA
      VXGUXQVWLVCZWNZWUIUXRUKURUKULVAZUXSWQUKWUJUHZUXRYAUSUXRURMUKUXRVBAVXLUXQV
      WNVCUXRXJZAURMWQWRUXQAURMVUNVWNVUOUVMVCYBZXKZAUXSUXSWQWRUXQAMMUKVWNVWNWUB
      VWOYBVCWHYCWKYDXMVEVEVEYEVCVVAVURVVBVVAUYAUXSUXNVUTUYBWAYJXRVEVUTUYBYFZUJ
      ZUYFUYHUYMVURWUPUYFUJZUYHUKUXNUGZVURWUPUYHWURUHZUYFVUTWUSWUOAUXQWUSVUQUXR
      UYHUKVVSUGZUKUNVAZWURUXRUYGWUTUKUNUXRUKUXOVVSVWGWCVHUXRWVAUKUKUKUMVAZVVFQ
      VRZULVAZUKUNVAZWURUXRWUTWVDUKUNUXRIUKVVMWVDVVDVVSUQUXRVVSYGUXRVVJUKUHZUJZ
      VVJUKVVLWVCULUXRWVFWAZWVGVVKWVBVVFQWVGVVJUKUKUMWVHVGWBVIUXRUKUKMWUGWUHWUG
      UXRUKWULWGZAUKMWQWRUXQVWMVCWHUXRUKWVCULWIVPVHUXRWVEWVCWURUXRUKWVCWUFUXRWV
      CUXRWVBVVFQUXRUKUKVNUXRVVEWVBUIZUJZVXEVXFWVKVVEUKUXSWVKWDWVKMUXRVXGWVJWUH
      VCWNZWVJVXIUXRVVEUKUKWPVKZWVJVXKUXRVVEUKUKWSVKWVKVVEWUJUXSWVKVVEWVMWTWVKU
      RUKWVKVBWVKXJYHWVKUXSWVLWTWVKVVEUKWUJWQWVJVVEUKWQWRUXRVVEUKUKXBVKWUKWVKYA
      USUVOUXRWUJUXSWQWRWVJWUMVCXCWHUXRVXEVXFWVJWUEYIXIXGWKYKUXRWUCWURWJUIWVCWU
      RUHWUGUXRWURUXRUXTWOUKUXNVYKUXRUKUKUXSWUGWUIWUGWVIWUNWHYCWKVVFWURQUKVVEUK
      UXNXNUVNXLVEVEVEYEVCVCWUQVURWURWUQUYAUKUXNWUPUYFWAYJXRVEWUPUYFYFZUJZUYMUY
      AVVSUGZUYJVVSUGZUNVAZUKUNVAZVURWVOUYLWVRUKUNWVOUYIWVPUYKWVQUNWVOUYAUXOVVS
      WVOOUXNVVRVVSDKUQVVTWVOTUSWVOVWAUJZIVVDVVQVVMWVTVWCUJZVVPVVLVVJULWWAVVKVV
      OVVFQWWAVWEUJVVEVVNUXNWVOVWAVWCVWEVSWCVTVGVDAUXQVUQWUOWVNUVPWVOIVVDVVMVMW
      VOUKMVNVOVPZWCWVOUYJUXOVVSWWBWCVIVHWVOWVSUYAUKUYAUMVAZVVFQVRZULVAZUYJUKUY
      JUMVAZVVFQVRZULVAZUNVAZUKUNVAZVURWVOWVRWWIUKUNWVOWVPWWEWVQWWHUNWVOIUYAVVM
      WWEVVDVVSUQWVOVVSYGZWVOVVJUYAUHZUJZVVJUYAVVLWWDULWVOWWLWAZWWMVVKWWCVVFQWW
      MVVJUYAUKUMWWNVGWBVIWVOUYAUKMWVOWDWUPVXGWVNVUTVXGWUOAUXQVXGVUQWUHYEVCZVCZ
      WUPUYAWLUIZWVNVUTWWQWUOVUTUYAVUQAUYAYLUIUXQUYAUXSYMZYNZYOZVCZVCZWUPUKUYAW
      QWRZWVNVUTWXCWUOVUTUYAWWSWEZVCVCWUPUYAMWQWRZWVNWUPWXEUYAUXSYPWRZWUPWXFUYA
      UXSWQWRZUXSUYAYQZUJWUPWXGWXHWUPWXCWXGWUPVUQWXCWXGUJZAUXQVUQWUOUVQWUPVUQWX
      IWUPWWQWUCWUDVUQWXIXHWXAWUPWDWUPMWWOWNZUYAUKUXSUWFYRXEXFXTZWUPUYAUXSWUOUY
      AUXSYQVUTUYAUXSYSVKUTUVRWUPUYAUXSWUPUYAWXAWTZWUPUXSWXJWTZUVSXMWUPWWQVXGWX
      EWXFXHWXAWWOUYAMUVTXLXMVCWHWVOUYAWWDULWIVPWVOIUYJVVMWWHVVDVVSUQWWKWVOVVJU
      YJUHZUJZVVJUYJVVLWWGULWVOWXNWAZWXOVVKWWFVVFQWXOVVJUYJUKUMWXPVGWBVIVUTWVNU
      YJVVDUIZWUOAVUQWVNWXQUXQAVUQWVNWXQAVUQWVNVQZUYJUKMWXRWDZAVUQWVNVXGAVXGVUQ
      WVNVWLWMUWAWXRUYAUKAVUQWVNWWQAVUQUJWWQWVNVUQWWQAVUQUYAWWRYOVKVCUWAZWXSUWB
      ZWXRUKUKULVAUYAWQWRZUKUYJWQWRZWXRUKUYAYPWRZWYBWXRWYDUYAUKYQZWVNAWYEVUQUYA
      UKYSYNWXRUKUYAAVUQUKXAUIZWVNWUBYTZWXRUYAWXTWTZWXRVUQWXCAVUQWVNUWCUYAUKUXS
      WSUWDUWEXMWXRUKUYAWXSWXTUWGUWHWXRWYFWYFUYAXAUIZWYBWYCXHWYGWYGWYHUKUKUYAUW
      IYRUWHWXRUYJVYOMWXRUYJWYAWTWXRUXSUKWXRMUKAVUQVXLWVNVWNYTZWXRXJZYHZWYKUWJW
      YJWXRUYAUXSUKWYHWYLWYKVUQAWXGWVNUYAUKUXSXBUWKUWLWXRVYOMMWQWXRMUKAVUQVWSWV
      NVWTYTWXRXPXQAVUQMMWQWRWVNVWOYTXKXCWHUWMUWPYIWVOUYJWWGULWIVPVIVHWVOWWJUYA
      UYJUNVAZWWDWWGUNVAZULVAZUKUNVAZVURWVOWWIWYOUKUNWVOUYAWWDUYJWWGWVOUYAWXBUW
      NZWVOWWDWVOWWCVVFQWVOUKUYAVNWVOVVEWWCUIZUJZVXEVXFWYSVVEUKUXSWYSWDWYSMWVOV
      XGWYRWWPVCWNWYSVVEWYRVVEYLUIZWVOVVEUYAYMVKZYOWYSVVEXUAWEWYSVVEUYAUXSWYSVV
      EXUAWFWUPWYIWVNWYRWXLWMWUPUXSXAUIZWVNWYRWXMWMWYRVVEUYAWQWRWVOVVEUKUYAXBVK
      WUPWXGWVNWYRWXKWMXCWHWYSUXTWOVVEUXNWVOVXNWYRWUPVXNWVNVUTVXNWUOAUXQVXNVUQV
      YKYEZVCVCZVCVLXIZXGWKZWVOUYAUKWYQWVOXPZUWOWVOWWGWVOWWFVVFQWVOUKUYJVNWVOVV
      EWWFUIZUJZVXEVXFXUIVVEUKUXSXUIWDXUIMWVOVXGXUHWWPVCWNXUIVVEXUHWYTWVOVVEUYJ
      YMVKZYOXUIVVEXUJWEXUIVVEUYJUXSXUIVVEXUJWFXUIUYAUKWUPWYIWVNXUHWXLWMZXUIXJU
      WJZWUPXUBWVNXUHWXMWMZXUHVVEUYJWQWRWVOVVEUKUYJXBVKXUIUYJUYAUXSXULXUKXUMXUI
      UYAXUKUWQWUPWXGWVNXUHWXKWMXCXCWHXUIUXTWOVVEUXNWVOVXNXUHXUDVCVLXIXGWKZUWRV
      HWVOWYPUKWYNULVAZUKUNVAZVURWVOWYOXUOUKUNWVOWYMUKWYNULWVOUYAUKWYQXUGUWSVHV
      HWVOXUPWYNVURWVOUKWYNXUGWVOWWDWWGXUFXUNUWOYKWVOWYNVURUHWWGVURULVAZWWDUHWV
      OWWDXUQWVOVVFVURQUKUYAWUPUYAVYRUIZWVNVUTXURWUOVUTWUCWWQWXCVQXURVUTWUCWWQW
      XCAUXQWUCVUQWUGYEWWTWXDUWTUKUYAUXAUXBVCVCWYSVVFXUEWKVVEUYAUXNXNXOXRWVOWWD
      WWGVURXUFXUNWUPVURWJUIZWVNVUTXUSWUOVUTVURVUTUXTWOUYAUXNXUCAUXQVUQUXCYCWKV
      CVCYDXMVEVEVEVEVEUXDUXDUWMVDUXRUXNVUSUXRUXNUXTUXGZUXNVUSUHZUXRUXTWOUXNVYK
      UXEXUTXVAJUXTUXNUXHUXFUWDXRVEVEUXIABCDEFGHIJKLMNOPUEQRSTUAUBUCUXJUXK $.
  $}

  ${
    $d A a j l x y $.  $d A b j l $.  $d B a $.  $d B b $.  $d K a f j l x y $.
    $d K b j l $.  $d K a g i $.  $d N b j $.  $d N f j $.  $d N g i $.
    $d a j l ph x y $.  $d b j l ph $.  $d i l $.  $d A a j k l x y $.
    $d A b j k l x y $.  $d B a i k l $.  $d B b i k l $.  $d B a j k l $.
    $d F b k $.  $d K b f j l x y $.  $d K a g i k $.  $d N a f j l $.
    $d N b f j l $.  $d N a g i k $.  $d a i k l ph $.  $d b g i k $.
    $d b i k l ph $.  $d j k l ph x y $.
    sticksstones13.1 $e |- ( ph -> N e. NN0 ) $.
    sticksstones13.2 $e |- ( ph -> K e. NN0 ) $.
    sticksstones13.3 $e |- F = ( a e. A |-> ( j e. ( 1 ... K ) |->
    ( j + sum_ l e. ( 1 ... j ) ( a ` l ) ) ) ) $.
    sticksstones13.4 $e |- G = ( b e. B |-> if ( K = 0
     , { <. 1 , N >. } , ( k e. ( 1 ... ( K + 1 ) )
        |-> if ( k = ( K + 1 ) , ( ( N + K ) - ( b ` K ) ) , if
       ( k = 1 , ( ( b ` 1 ) - 1 )
       , ( ( ( b ` k ) - ( b ` ( k - 1 ) ) ) - 1 ) ) ) ) ) ) $.
    sticksstones13.5 $e |- A = { g | ( g : ( 1 ... ( K + 1 ) ) --> NN0 /\
     sum_ i e. ( 1 ... ( K + 1 ) ) ( g ` i ) = N ) } $.
    sticksstones13.6 $e |- B = { f | ( f : ( 1 ... K ) --> ( 1 ... ( N + K ) )
    /\ A. x e. ( 1 ... K ) A. y e. ( 1 ... K ) ( x < y ->
    ( f ` x ) < ( f ` y ) ) ) } $.
    $( Establish bijective mapping between strictly monotone functions and
       functions that sum to a fixed non-negative integer.  (Contributed by
       metakunt, 6-Oct-2024.) $)
    sticksstones13 $p |- ( ph -> F : A -1-1-onto-> B ) $=
      ( cc0 wceq wf1o cn wcel wa cn0 adantr simpr sticksstones11 sticksstones12
      wo elnn0 biimpi orcomd syl mpjaodan ) AMUDUEZDEKUFMUGUHZAVAUIBCDEFGHIJKLM
      NOPQANUJUHZVARUKAVAULTUAUBUCUMAVBUIBCDEFGHIJKLMNOPQAVCVBRUKAVBULTUAUBUCUN
      AMUJUHZVAVBUOSVDVBVAVDVBVAUOMUPUQURUSUT $.
  $}

  ${
    $d A a i k l $.  $d A b i k l $.  $d A a j k l x y $.  $d B a f j l $.
    $d B b f j l $.  $d B a i k l $.  $d F b i k $.  $d K a f j l x y $.
    $d K b f j l x y $.  $d K a g i k $.  $d N a f j l x y $.
    $d N b f j l x y $.  $d N a g i k $.  $d a f j l ph x y $.
    $d b g i k ph $.
    sticksstones14.1 $e |- ( ph -> N e. NN0 ) $.
    sticksstones14.2 $e |- ( ph -> K e. NN0 ) $.
    sticksstones14.3 $e |- F = ( a e. A |-> ( j e. ( 1 ... K ) |->
    ( j + sum_ l e. ( 1 ... j ) ( a ` l ) ) ) ) $.
    sticksstones14.4 $e |- G = ( b e. B |-> if ( K = 0
     , { <. 1 , N >. } , ( k e. ( 1 ... ( K + 1 ) )
        |-> if ( k = ( K + 1 ) , ( ( N + K ) - ( b ` K ) ) , if
       ( k = 1 , ( ( b ` 1 ) - 1 )
       , ( ( ( b ` k ) - ( b ` ( k - 1 ) ) ) - 1 ) ) ) ) ) ) $.
    sticksstones14.5 $e |- A = { g | ( g : ( 1 ... ( K + 1 ) ) --> NN0 /\
     sum_ i e. ( 1 ... ( K + 1 ) ) ( g ` i ) = N ) } $.
    sticksstones14.6 $e |- B = { f | ( f : ( 1 ... K ) --> ( 1 ... ( N + K ) )
    /\ A. x e. ( 1 ... K ) A. y e. ( 1 ... K ) ( x < y ->
    ( f ` x ) < ( f ` y ) ) ) } $.
    $( Sticks and stones with definitions as hypotheses.  (Contributed by
       metakunt, 7-Oct-2024.) $)
    sticksstones14 $p |- ( ph -> ( # ` A ) = ( ( N + K ) _C K ) ) $=
      ( chash cfv caddc co cbc cvv c1 cfz cn0 cv wf csu wceq wa cab a1i wcel wi
      wss simpl ss2abdv cfn fzfid nn0ex mapex syl2anc sticksstones13 hasheqf1od
      ssexg eqeltrd nn0addcld sticksstones5 eqtrd ) ADUDUEEUDUENMUFUGZMUHUGADEU
      IKADUJMUJUFUGZUKUGZULGUMZUNZVSHUMVTUEHUONUPZUQZGURZUIDWDUPAUBUSAWDWAGURZV
      BWEUIUTZWDUIUTAWCWAGWCWAVAAWAWBVCUSVDAVSVEUTULUIUTZWFAUJVRVFWGAVGUSVSULVE
      UIGVHVIWDWEUIVLVIVMABCDEFGHIJKLMNOPQRSTUAUBUCVJVKABCEFMVQANMRSVNSUCVOVP
      $.
  $}

  ${
    $d A i t u v w x y z $.  $d K f l t u v x y z $.  $d K g i u v w $.
    $d N f l t u v x y z $.  $d N g i u v w $.  $d f ph t u v x y z $.
    $d g i ph u v w $.  $d i l t u v w x y z $.
    sticksstones15.1 $e |- ( ph -> N e. NN0 ) $.
    sticksstones15.2 $e |- ( ph -> K e. NN0 ) $.
    sticksstones15.3 $e |- A = { g | ( g : ( 1 ... ( K + 1 ) ) --> NN0 /\
     sum_ i e. ( 1 ... ( K + 1 ) ) ( g ` i ) = N ) } $.
    $( Sticks and stones with almost collapsed definitions for positive
       integers.  (Contributed by metakunt, 7-Oct-2024.) $)
    sticksstones15 $p |- ( ph -> ( # ` A ) = ( ( N + K ) _C K ) ) $=
      ( vx vy c1 cfz co cv clt cfv wral cmpt cmin vl vf vz vw vv vt vu caddc wf
      wbr wi wa cab csu cc0 wceq cop csn cif eqid fveq1 breq12d imbi2d 2ralbidv
      feq1 anbi12d cbvabv sticksstones14 ) AJKBLEMNZLFEUHNZMNZUAOZUIZJOZKOZPUJZ
      VNVLQZVOVLQZPUJZUKZKVIRJVIRZULZUAUMZUBCDUCUDUEBUCVIUCOZLWDMNUFOUEOQUFUNUH
      NSSZUGWCEUOUPLFUQURUDLELUHNZMNUDOZWFUPVJEUGOZQTNWGLUPLWHQLTNWGWHQWGLTNWHQ
      TNLTNUSUSSUSSZEFUEUGUFGHWEUTWIUTIWBVIVKUBOZUIZVPVNWJQZVOWJQZPUJZUKZKVIRJV
      IRZULUAUBVLWJUPZVMWKWAWPVIVKVLWJVEWQVTWOJKVIVIWQVSWNVPWQVQWLVRWMPVNVLWJVA
      VOVLWJVAVBVCVDVFVGVH $.
  $}

  ${
    $d K g i j $.  $d N g i $.  $d g i ph $.
    sticksstones16.1 $e |- ( ph -> N e. NN0 ) $.
    sticksstones16.2 $e |- ( ph -> K e. NN ) $.
    sticksstones16.3 $e |- A = { g | ( g : ( 1 ... K ) --> NN0 /\
     sum_ i e. ( 1 ... K ) ( g ` i ) = N ) } $.
    $( Sticks and stones with collapsed definitions for positive integers.
       (Contributed by metakunt, 20-Oct-2024.) $)
    sticksstones16 $p |- ( ph -> ( # ` A ) =
     ( ( N + ( K - 1 ) ) _C ( K - 1 ) ) ) $=
      ( vj chash cfv c1 co cfz cn0 cv csu wceq wa cmin caddc wf cab cbc cbvsumv
      fveq2 eqeq1i anbi2i abbii eqtri a1i nncnd 1cnd npcand eqcomd oveq2d feq2d
      nfv sumeq1d eqeq1d anbi12d abbid eqtrd fveq2d wcel nnm1nn0 sticksstones15
      cn syl ) ABKLMEMUANZMUBNZONZPCQZUCZVMJQZVNLZJRZFSZTZCUDZKLFVKUBNVKUENABWA
      KABMEONZPVNUCZWBVQJRZFSZTZCUDZWABWGSABWCWBDQZVNLZDRZFSZTZCUDWGIWLWFCWKWEW
      CWJWDFWBWIVQDJWHVPVNUGUFUHUIUJUKULAWFVTCACUSAWCVOWEVSAWBVMPVNAEVLMOAVLEAE
      MAEHUMAUNUOUPUQZURAWDVRFAWBVMVQJWMUTVAVBVCVDVEAWACDVKFGAEVIVFVKPVFHEVGVJV
      TVOVMWIDRZFSZTCVSWOVOVRWNFVMVQWIJDVPWHVNUGUFUHUIUJVHVD $.
  $}

  ${
    $d A b $.  $d B b i s $.  $d B b i y $.  $d K g i y $.  $d N g $.
    $d N h $.  $d S h i $.  $d S i s $.  $d Z g i y $.  $d Z i s $.
    $d b g i y $.  $d b h i $.  $d b i ph s $.  $d ph y $.
    sticksstones17.1 $e |- ( ph -> N e. NN0 ) $.
    sticksstones17.2 $e |- ( ph -> K e. NN0 ) $.
    sticksstones17.3 $e |- A = { g | ( g : ( 1 ... K ) --> NN0 /\
     sum_ i e. ( 1 ... K ) ( g ` i ) = N ) } $.
    sticksstones17.4 $e |- B = { h | ( h : S --> NN0 /\
     sum_ i e. S ( h ` i ) = N ) } $.
    sticksstones17.5 $e |- ( ph -> Z : ( 1 ... K ) -1-1-onto-> S ) $.
    sticksstones17.6 $e |- G = ( b e. B |-> ( y e. ( 1 ... K ) |->
    ( b ` ( Z ` y ) ) ) ) $.
    $( Extend sticks and stones to finite sets, bijective builder.
       (Contributed by metakunt, 23-Oct-2024.) $)
    sticksstones17 $p |- ( ph -> G : B --> A ) $=
      ( cn0 vs c1 cfz co cv cfv cmpt wcel wa csu wceq cab w3a wss eqimssi sseld
      a1i imp vex feq1 simpl fveq1d sumeq2dv eqeq1d anbi12d sylib simpld adantr
      wf elab 3impa wf1o f1of syl simp3 ffvelcdmd 3expa fmpttd cvv eqidd fveq2d
      simpr fvexd fvmptd fveq2 cfn cc nn0sscn syl2anc ffvelcdmda fsumf1o eqcomd
      fzfi fss cbvsumv simprd eqtrd wb fzfid mptexd elabg mpbird eleqtrrd fmptd
      jca ) AMDBUBJUCUDZBUEZLUFZMUEZUFZUGZCIAXIDUHZUIZXKXFTFUEZVIZXFHUEZXNUFZHU
      JZKUKZUIZFULZCXMXKYAUHZXFTXKVIZXFXPXKUFZHUJZKUKZUIZXMYCYFXMBXFXJTAXLXGXFU
      HZXJTUHAXLYHUMZETXHXIAXLYHETXIVIZXMYJYHXMYJEXPXIUFZHUJZKUKZXMXIETGUEZVIZE
      XPYNUFZHUJZKUKZUIZGULZUHZYJYMUIZAXLUUAADYTXIDYTUNADYTQUOUQUPURYSUUBGXIMUS
      YNXIUKZYOYJYRYMETYNXIUTUUCYQYLKUUCEYPYKHUUCXPEUHZUIXPYNXIUUCUUDVAVBVCVDVE
      VJVFZVGZVHVKYIXFEXGLAXLYHXFELVIZXMUUGYHAUUGXLAXFELVLZUUGRXFELVMVNVHVHVKAX
      LYHVOVPVPVQVRXMYEXFXPLUFZXIUFZHUJZKXMXFYDUUJHXMXPXFUHZUIZBXPXJUUJXFXKVSUU
      MXKVTUUMXGXPUKZUIZXHUUIXIUUOXGXPLUUMUUNWBWAWAXMUULWBUUMUUIXIWCWDVCXMUUKEU
      AUEZXIUFZUAUJZKXMUURUUKXMEUUQXFUUJUAHLUUIUUPUUIXIWEXFWFUHXMUBJWMUQAUUHXLR
      VHUUMUUIVTXMEWGUUPXIXMYJTWGUNZEWGXIVIUUFUUSXMWHUQETWGXIWNWIWJWKWLXMUURYLK
      UURYLUKXMEUUQYKUAHUUPXPXIWEWOUQXMYJYMUUEWPWQWQWQXEXMXKVSUHYBYGWRXMBXFXJWF
      XMUBJWSWTXTYGFXKVSXNXKUKZXOYCXSYFXFTXNXKUTUUTXRYEKUUTXFXQYDHUUTUULUIXPXNX
      KUUTUULVAVBVCVDVEXAVNXBCYAUKXMPUQXCSXD $.
  $}

  ${
    $d A a i n $.  $d A a i x $.  $d B a $.  $d K g i $.  $d K i n $.
    $d N g $.  $d N h $.  $d S h i x $.  $d Z h i x $.  $d Z i n $.
    $d a g i $.  $d a h i x $.  $d a i n ph $.  $d ph x $.
    sticksstones18.1 $e |- ( ph -> N e. NN0 ) $.
    sticksstones18.2 $e |- ( ph -> K e. NN0 ) $.
    sticksstones18.3 $e |- A = { g | ( g : ( 1 ... K ) --> NN0 /\
     sum_ i e. ( 1 ... K ) ( g ` i ) = N ) } $.
    sticksstones18.4 $e |- B = { h | ( h : S --> NN0 /\
     sum_ i e. S ( h ` i ) = N ) } $.
    sticksstones18.5 $e |- ( ph -> Z : ( 1 ... K ) -1-1-onto-> S ) $.
    sticksstones18.6 $e |- F = ( a e. A |-> ( x e. S |->
    ( a ` ( `' Z ` x ) ) ) ) $.
    $( Extend sticks and stones to finite sets, bijective builder.
       (Contributed by metakunt, 23-Oct-2024.) $)
    sticksstones18 $p |- ( ph -> F : A --> B ) $=
      ( wa vn cv ccnv cfv cmpt wcel cn0 wf csu wceq cab c1 cfz co eqimssi sseld
      wss a1i imp feq1 simpl fveq1d sumeq2dv eqeq1d anbi12d sylib simpld adantr
      vex elab wf1o f1ocnv syl f1of ffvelcdmda ffvelcdmd fmpttd cvv eqidd simpr
      fveq2d fvexd fvmptd fveq2 cfn cen wbr fzfid f1oenfi syl2anc enfii nn0sscn
      ensymd cc fss fsumf1o eqcomd cbvsumv simprd eqtrd jca mptexd elabg mpbird
      wb eleqtrrd fmptd ) AMCBEBUBZLUCZUDZMUBZUDZUEZDIAXKCUFZTZXMEUGGUBZUHZEHUB
      ZXPUDZHUIZKUJZTZGUKZDXOXMYCUFZEUGXMUHZEXRXMUDZHUIZKUJZTZXOYEYHXOBEXLUGXOX
      HEUFZTULJUMUNZUGXJXKXOYKUGXKUHZYJXOYLYKXRXKUDZHUIZKUJZXOXKYKUGFUBZUHZYKXR
      YPUDZHUIZKUJZTZFUKZUFZYLYOTZAXNUUCACUUBXKCUUBUQACUUBPUOURUPUSUUAUUDFXKMVI
      YPXKUJZYQYLYTYOYKUGYPXKUTUUEYSYNKUUEYKYRYMHUUEXRYKUFZTXRYPXKUUEUUFVAVBVCV
      DVEVJVFZVGZVHXOEYKXHXIAEYKXIUHZXNAEYKXIVKZUUIAYKELVKZUUJRYKELVLVMZEYKXIVN
      VMVHVOVPVQXOYGEXRXIUDZXKUDZHUIZKXOEYFUUNHXOXREUFZTZBXRXLUUNEXMVRUUQXMVSUU
      QXHXRUJZTZXJUUMXKUUSXHXRXIUUQUURVTWAWAXOUUPVTUUQUUMXKWBWCVCXOUUOYKUAUBZXK
      UDZUAUIZKXOUVBUUOXOYKUVAEUUNUAHXIUUMUUTUUMXKWDXOYKWEUFZEYKWFWGZEWEUFZXOUL
      JWHZXOYKEXOUVCUUKYKEWFWGZUVFAUUKXNRVHYKELWIZWJWMEYKWKZWJAUUJXNUULVHUUQUUM
      VSXOYKWNUUTXKXOYLUGWNUQZYKWNXKUHUUHUVJXOWLURYKUGWNXKWOWJVOWPWQXOUVBYNKUVB
      YNUJXOYKUVAYMUAHUUTXRXKWDWRURXOYLYOUUGWSWTWTWTXAXOXMVRUFYDYIXEXOBEXLWEXOU
      VCUVDUVEAUVCXNAULJWHZVHAUVDXNAYKEAUVCUUKUVGUVKRUVHWJWMVHUVIWJXBYBYIGXMVRX
      PXMUJZXQYEYAYHEUGXPXMUTUVLXTYGKUVLEXSYFHUVLUUPTXRXPXMUVLUUPVAVBVCVDVEXCVM
      XDDYCUJXOQURXFSXG $.
  $}

  ${
    $d A a c i x y $.  $d A b c i x y $.  $d B a d i x y $.  $d B b d i x y $.
    $d F b c y $.  $d F b d y $.  $d G a c x $.  $d G a d x $.  $d K a g i y $.
    $d K b g i y $.  $d K a i x y $.  $d N g $.  $d N h $.  $d S a h i x $.
    $d S b h i x $.  $d S a i x y $.  $d Z a g i y $.  $d Z b g i y $.
    $d Z a h i x $.  $d a c i ph x y $.  $d b c i ph x y $.  $d c g i y $.
    $d d h i x $.  $d d i ph x y $.
    sticksstones19.1 $e |- ( ph -> N e. NN0 ) $.
    sticksstones19.2 $e |- ( ph -> K e. NN0 ) $.
    sticksstones19.3 $e |- A = { g | ( g : ( 1 ... K ) --> NN0 /\
     sum_ i e. ( 1 ... K ) ( g ` i ) = N ) } $.
    sticksstones19.4 $e |- B = { h | ( h : S --> NN0 /\
     sum_ i e. S ( h ` i ) = N ) } $.
    sticksstones19.5 $e |- ( ph -> Z : ( 1 ... K ) -1-1-onto-> S ) $.
    sticksstones19.6 $e |- F = ( a e. A |-> ( x e. S |->
    ( a ` ( `' Z ` x ) ) ) ) $.
    sticksstones19.7 $e |- G = ( b e. B |-> ( y e. ( 1 ... K ) |->
    ( b ` ( Z ` y ) ) ) ) $.
    $( Extend sticks and stones to finite sets, bijective builder.
       (Contributed by metakunt, 23-Oct-2024.) $)
    sticksstones19 $p |- ( ph -> F : A -1-1-onto-> B ) $=
      ( vc vd sticksstones18 sticksstones17 cv cfv wceq wcel wa c1 cfz cmpt cvv
      a1i simplr fveq1d mpteq2dva ffvelcdmda cfn fzfid mptexd fvmptd ccnv 3expa
      co w3a eqidd cen wf1o f1oenfi syl2anc ensymd enfii adantr simpr fveq2d wf
      wbr f1of syl ad2antrr f1ocnvfv1 wfn cn0 csu cab eleqtrd vex feq1 sumeq2dv
      fvexd simpl eqeq1d anbi12d elab sylib simpld dffn5 eqcomd eqtrd ralrimiva
      ffn f1ocnv f1ocnvfv2 2fvidf1od ) ADEJKUDUEABDEFGHIJLMNOQRSTUAUBUFZACDEFGH
      IKLMNPQRSTUAUCUGZAUDUHZJUIZKUIZXKUJUDDAXKDUKZULZXMCUMLUNVHZCUHZNUIZXLUIZU
      OZXKXOPXLCXPXRPUHZUIZUOZXTEKUPKPEYCUOUJZXOUCUQXOYAXLUJZULZCXPYBXSYFXQXPUK
      ZULXRYAXLXOYEYGURUSUTADEXKJXIVAXOCXPXSVBXOUMLVCVDVEXOXTCXPXRXKODBFBUHZNVF
      ZUIZOUHZUIZUOZUOZUIZUIZUOZXKXOCXPXSYPAXNYGXSYPUJAXNYGVIZXRXLYOYRXKJYNJYNU
      JZYRUBUQUSUSVGUTXOYQCXPXRBFYJXKUIZUOZUIZUOZXKXOCXPYPUUBXOYGULZXRYOUUAUUDO
      XKYMUUADYNUPUUDYNVJUUDYKXKUJZULZBFYLYTUUFYHFUKZULYJYKXKUUDUUEUUGURUSUTAXN
      YGURUUDBFYTVBXOFVBUKZYGAUUHXNAXPVBUKZFXPVKWAUUHAUMLVCZAXPFAUUIXPFNVLZXPFV
      KWAUUJUAXPFNVMVNVOFXPVPVNZVQVQVDVEUSUTXOUUCCXPXRYIUIZXKUIZUOZXKXOCXPUUBUU
      NUUDBXRYTUUNFUUAUPUUDUUAVJUUDYHXRUJZULZYJUUMXKUUQYHXRYIUUDUUPVRVSVSXOXPFX
      QNAXPFNVTZXNAUUKUURUAXPFNWBWCVQVAUUDUUMXKWNVEUTXOUUOCXPXQXKUIZUOZXKXOCXPU
      UNUUSUUDUUMXQXKUUDUUKYGUUMXQUJAUUKXNYGUAWDXOYGVRXPFXQNWEVNVSUTXOXKUUTXOXK
      XPWFZXKUUTUJXOXPWGXKVTZUVAXOUVBXPIUHZXKUIZIWHZMUJZXOXKXPWGGUHZVTZXPUVCUVG
      UIZIWHZMUJZULZGWIZUKUVBUVFULZXOXKDUVMAXNVRDUVMUJXOSUQWJUVLUVNGXKUDWKUVGXK
      UJZUVHUVBUVKUVFXPWGUVGXKWLUVOUVJUVEMUVOXPUVIUVDIUVOUVCXPUKZULUVCUVGXKUVOU
      VPWOUSWMWPWQWRWSWTXPWGXKXEWCCXPXKXAWSXBXCXCXCXCXCXDAUEUHZKUIZJUIZUVQUJUEE
      AUVQEUKZULZUVSBFYJUVRUIZUOZUVQUWAOUVRYMUWCDJUPYSUWAUBUQUWAYKUVRUJZULZBFYL
      UWBUWEUUGULYJYKUVRUWAUWDUUGURUSUTAEDUVQKXJVAUWABFUWBVBAUUHUVTUULVQVDVEUWA
      UWCBFYJCXPXRUVQUIZUOZUIZUOZUVQUWABFUWBUWHUWAUUGULZYJUVRUWGUWJPUVQYCUWGEKU
      PYDUWJUCUQUWJYAUVQUJZULZCXPYBUWFUWLYGULXRYAUVQUWJUWKYGURUSUTAUVTUUGURUWJC
      XPUWFVBUWJUMLVCVDVEUSUTUWAUWIBFYJNUIZUVQUIZUOZUVQUWABFUWHUWNUWJCYJUWFUWNX
      PUWGUPUWJUWGVJUWJXQYJUJZULZXRUWMUVQUWQXQYJNUWJUWPVRVSVSUWAFXPYHYIAFXPYIVT
      ZUVTAFXPYIVLZUWRAUUKUWSUAXPFNXFWCFXPYIWBWCVQVAUWJUWMUVQWNVEUTUWAUWOBFYHUV
      QUIZUOZUVQUWABFUWNUWTUWJUWMYHUVQUWJUUKUUGUWMYHUJAUUKUVTUUGUAWDUWAUUGVRXPF
      YHNXGVNVSUTUWAUVQUXAUWAUVQFWFZUVQUXAUJUWAFWGUVQVTZUXBUWAUXCFUVCUVQUIZIWHZ
      MUJZUWAUVQFWGHUHZVTZFUVCUXGUIZIWHZMUJZULZHWIZUKUXCUXFULZUWAUVQEUXMAUVTVRE
      UXMUJUWATUQWJUXLUXNHUVQUEWKUXGUVQUJZUXHUXCUXKUXFFWGUXGUVQWLUXOUXJUXEMUXOF
      UXIUXDIUXOUVCFUKZULUVCUXGUVQUXOUXPWOUSWMWPWQWRWSWTFWGUVQXEWCBFUVQXAWSXBXC
      XCXCXCXDXH $.
  $}

  ${
    $d A a b i p x y $.  $d A a p q x $.  $d B a b i p x y $.  $d B a p q x $.
    $d K a b g i y $.  $d K a b i x y $.  $d N g i $.  $d N h i $.
    $d S a b h i p x $.  $d S a p q x $.  $d S a b i p x y $.
    $d a b g i p ph y $.  $d ph x y $.
    sticksstones20.1 $e |- ( ph -> N e. NN0 ) $.
    sticksstones20.2 $e |- ( ph -> S e. Fin ) $.
    sticksstones20.3 $e |- ( ph -> K e. NN ) $.
    sticksstones20.4 $e |- A = { g | ( g : ( 1 ... K ) --> NN0 /\
     sum_ i e. ( 1 ... K ) ( g ` i ) = N ) } $.
    sticksstones20.5 $e |- B = { h | ( h : S --> NN0 /\
     sum_ i e. S ( h ` i ) = N ) } $.
    sticksstones20.6 $e |- ( ph -> ( # ` S ) = K ) $.
    $( Lift sticks and stones to arbitrary finite non-empty sets.  (Contributed
       by metakunt, 24-Oct-2024.) $)
    sticksstones20 $p |- ( ph -> ( # ` B ) =
     ( ( N + ( K - 1 ) ) _C ( K - 1 ) ) ) $=
      ( vp cfv cv wcel cvv vq va vx vy vb chash c1 cmin co cbc cen wbr wceq cfz
      caddc wf1o wex cfn isfinite4 bren syl oveq2d f1oeq2d biimpd eximdv mpd wa
      sylbb ccnv cn0 wf csu cab a1i fzfid nn0ex mapex syl2anc simprl ex ss2abdv
      cmpt ssexd eqeltrd adantr mptexd nnnn0d eqid sticksstones19 f1oeq1 spcedv
      simpr sylibr exlimddv hasheni eqcomd sticksstones16 eqtrd ) ACUFQZBUFQZIH
      UGUHUIZUOUIXAUJUIAWTWSABCUKULZWTWSUMAUGHUNUIZDPRZUPZXBPAUGDUFQZUNUIZDXDUP
      ZPUQZXEPUQADURSZXIKXJXGDUKULXIDUSXGDPUTVHVAAXHXEPAXHXEAXGXCDXDAXFHUGUNOVB
      VCVDVEVFAXEVGZBCUARZUPZUAUQXBXKXMBCUBBUCDUCRXDVIQUBRQWBZWBZUPUATXOXKUBBXN
      TABTSXEABXCVJERZVKZXCGRXPQGVLIUMZVGZEVMZTBXTUMAMVNAXTXQEVMZTAXCURSVJTSZYA
      TSAUGHVOYBAVPVNXCVJURTEVQVRAXSXQEAXSXQAXQXRVSVTWAWCWDWEWFXKUCUDBCDEFGXOUE
      CUDXCUDRXDQUERQWBWBZHIXDUBUEAIVJSXEJWEAHVJSXEAHLWGWEMNAXEWLXOWHYCWHWIBCXL
      XOWJWKBCUAUTWMWNBCWOVAWPABEGHIJLMWQWR $.
  $}

  ${
    $d A k $.  $d N f k $.  $d N g k $.  $d S f i k $.  $d S g j k $.
    $d g k ph $.
    sticksstones21.1 $e |- ( ph -> N e. NN0 ) $.
    sticksstones21.2 $e |- ( ph -> S e. Fin ) $.
    sticksstones21.3 $e |- ( ph -> S =/= (/) ) $.
    sticksstones21.4 $e |- A = { f | ( f : S --> NN0 /\
     sum_ i e. S ( f ` i ) = N ) } $.
    $( Lift sticks and stones to arbitrary finite non-empty sets.  (Contributed
       by metakunt, 24-Oct-2024.) $)
    sticksstones21 $p |- ( ph -> ( # ` A ) =
     ( ( N + ( ( # ` S ) - 1 ) ) _C ( ( # ` S ) - 1 ) ) ) $=
      ( vg vj vk cfv cn0 cv csu wceq wa cab c1 chash cfz co wf cn c0 wne cfn wb
      wcel hashnncl syl mpbird fveq2 cbvsumv eqeq1i anbi2i abbii sticksstones20
      eqtri eqidd ) AUACUBNZUCUDZOKPZUEZVDLPZVENZLQZFRZSZKTBCKDMVCFGHAVCUFUKZCU
      GUHZIACUIUKVLVMUJHCULUMUNVKVFVDMPZVENZMQZFRZSKVJVQVFVIVPFVDVHVOLMVGVNVEUO
      UPUQURUSBCODPZUEZCEPZVRNZEQZFRZSZDTVSCVNVRNZMQZFRZSZDTJWDWHDWCWGVSWBWFFCW
      AWEEMVTVNVRUOUPUQURUSVAAVCVBUT $.
  $}

  ${
    $d N f x $.  $d S f i s y $.  $d S f i x y $.  $d f i ph s y $.
    $d ph x y $.
    sticksstones22.1 $e |- ( ph -> N e. NN0 ) $.
    sticksstones22.2 $e |- ( ph -> S e. Fin ) $.
    sticksstones22.3 $e |- ( ph -> S =/= (/) ) $.
    sticksstones22.4 $e |- A = { f | ( f : S --> NN0 /\
     sum_ i e. S ( f ` i ) <_ N ) } $.
    $( Non-exhaustive sticks and stones.  (Contributed by metakunt,
       26-Oct-2024.) $)
    sticksstones22 $p |- ( ph -> ( # ` A ) =
     ( ( N + ( # ` S ) ) _C ( # ` S ) ) ) $=
      ( cle wa caddc co cbc wceq wcel cc0 c1 adantr vx vy chash cfv cn0 csu wbr
      vs cv cab a1i fveq2d breq2 anbi2d abbidv oveq1d eqeq12d simprl clt simprr
      wf oveq1 cfn simpr ffvelcdmda fsumnn0cl syldan nn0ge0d 0red nn0red lenltd
      wn mpbid jca eqleltd mpbird leidd eqbrtrd impbid cmin 0nn0 sticksstones21
      ex eqid c0 wne cn wb hashnncl syl bicomd biimpd nncnd 1cnd subcld addlidd
      mpd nnm1nn0 bcnn eqtrd eqcomd wo ad2antrr cr adantl 1red readdcld syl2anc
      cz nn0zd sylibr cfz cxp cpw fzfid xpfi pwfi sylib wss fsetsspwxp wral 0zd
      ssfid simpllr difssd adantlr mpdan addge01d nn0cnd breqtrd pm2.01da elfzd
      ltletrd ralrimiva ffnfv ss2abdv simplr ltned wi nn0addcld eqidd cun nn0re
      nnnn0d 3eqtrd leloed nn0z zleltp1 orbi1d andi bicomi lep1d letrd jaod cin
      unab wfn ffn csn cdif simplll simplrl jca31 eldifi nfcv fsumsplit1 ltnled
      nfv fveq2 pm2.21dd ad2antrl peano2zd ffvelcdmd eqeltrd syldanl pm2.21ddne
      necomd inab wal adantrr zred ltp1d lelttrd neneqd intnand nan alrimiv ab0
      mpbir hashun syl3anc 1nn0 oveq12d cc ppncand oveq2d bcpasc add32d nn0indd
      ) ABUCUDCUEDUIZVAZCEUIZUWTUDZEUFZFKUGZLZDUJZUCUDZFCUCUDZMNZUXIONZABUXGUCB
      UXGPAJUKULAFUEQUXHUXKPZGAUXAUXDUAUIZKUGZLZDUJZUCUDZUXMUXIMNZUXIONZPUXAUXD
      RKUGZLZDUJZUCUDZRUXIMNZUXIONZPUXAUXDUBUIZKUGZLZDUJZUCUDZUYFUXIMNZUXIONZPZ
      UXAUXDUYFSMNZKUGZLZDUJZUCUDZUYNUXIMNZUXIONZPUXLUAUBFUXMRPZUXQUYCUXSUYEVUA
      UXPUYBUCVUAUXOUYADVUAUXNUXTUXAUXMRUXDKUMUNUOULVUAUXRUYDUXIOUXMRUXIMVBUPUQ
      UXMUYFPZUXQUYJUXSUYLVUBUXPUYIUCVUBUXOUYHDVUBUXNUYGUXAUXMUYFUXDKUMUNUOULVU
      BUXRUYKUXIOUXMUYFUXIMVBUPUQUXMUYNPZUXQUYRUXSUYTVUCUXPUYQUCVUCUXOUYPDVUCUX
      NUYOUXAUXMUYNUXDKUMUNUOULVUCUXRUYSUXIOUXMUYNUXIMVBUPUQUXMFPZUXQUXHUXSUXKV
      UDUXPUXGUCVUDUXOUXFDVUDUXNUXEUXAUXMFUXDKUMUNUOULVUDUXRUXJUXIOUXMFUXIMVBUP
      UQAUYCUXAUXDRPZLZDUJZUCUDZUYEAUYBVUGUCAUYAVUFDAUYAVUFAUYAVUFAUYALZUXAVUEA
      UXAUXTURZVUIVUEUXTUXDRUSUGVLZLVUIUXTVUKAUXAUXTUTVUIRUXDKUGVUKVUIUXDAUYAUX
      AUXDUEQZVUJAUXALZCUXCEACVCQZUXAHTVUMCUEUXBUWTAUXAVDVEVFVGZVHVUIRUXDVUIVIZ
      VUIUXDVUOVJZVKVMVNVUIUXDRVUQVUPVOVPVNWCAVUFUYAAVUFLZUXAUXTAUXAVUEURVURUXD
      RRKAUXAVUEUTVURRVURVIVQVRVNWCVSUOULAVUHRUXISVTNZMNZVUSONZUYEAVUGCDERRUEQA
      WAUKHIVUGWDWBAVVASSUYEAVVAVUSVUSONZSAVUTVUSVUSOAVUSAUXISAUXIACWEWFZUXIWGQ
      ZIAVVCVVDAVVDVVCAVUNVVDVVCWHHCWIWJWKWLWQZWMZAWNWOWPUPAVUSUEQZVVBSPAVVDVVG
      VVEUXIWRWJVUSWSWJWTASUUAASUXIUXIONZUYEAVVHSAUXIUEQZVVHSPAUXIVVEUUDZUXIWSW
      JXAAUXIUYDUXIOAUYDUXIAUXIVVFWPXAUPWTUUEWTWTAUYFUEQZLZUYMLZUYRUYIUXAUXDUYN
      PZLZDUJZUUBZUCUDZUYTVVMUYQVVQUCVVLUYQVVQPUYMVVLUYQUYHVVOXBZDUJZVVQVVLUYPV
      VSDVVLUYPVVSVVLUYPVVSVVLUYPLZUXAUYGVVNXBZLZVVSVWAUXAVWBVVLUXAUYOURZVWAUXD
      UYNUSUGZVVNXBZVWBVWAUYOVWFVVLUXAUYOUTVWAUXDUYNVWAUXDVVLUYPUXAVULVWDVVLUXA
      LZCUXCEAVUNVVKUXAHXCZVWGCUEUXBUWTVVLUXAVDVEZVFZVGZVJVWAUYFSVVLUYFXDQZUYPV
      VKVWLAUYFUUCZXEZTVWAXFXGUUFVMVWAVWEUYGVVNVWAUXDXIQZUYFXIQZVWEUYGWHVWAUXDV
      WKXJVVLVWPUYPVVKVWPAUYFUUGXEZTVWOVWPLUYGVWEUXDUYFUUHWKXHUUIVMVNVWCVVSUXAU
      YGVVNUUJUUKXKWCVVLUYHUYPVVOVVLUYHUYPVVLUYHLZUXAUYOVVLUXAUYGURZVWRUXDUYFUY
      NVWRUXDVVLUYHUXAVULVWSVWJVGVJZVVLVWLUYHVWNTZVWRUYFSVXAVWRXFXGZVVLUXAUYGUT
      ZVWRUYFVXAUULUUMVNWCVVLVVOUYPVVLVVOLZUXAUYOVVLUXAVVNURZVXDUXDUYNUYNKVVLUX
      AVVNUTZVXDUYNVXDUYFSVVLVWLVVOVWNTVXDXFXGZVQVRVNWCUUNVSUOVVLVVQVVTVVQVVTPV
      VLUYHVVODUUPUKXAWTTULVVMVVRUYJVVPUCUDZMNZUYTVVMUYIVCQZVVPVCQZUYIVVPUUOZWE
      PZVVRVXIPVVLVXJUYMVVLCRUYFXLNZUWTVAZDUJZUYIVVLCVXNXMZXNZVXPVVLVXQVCQZVXRV
      CQVVLVUNVXNVCQZLVXSVVLVUNVXTAVUNVVKHTZVVLRUYFXOVNCVXNXPWJVXQXQXRVXPVXRXSV
      VLCVXNDXTUKYCVVLUYHVXODVVLUYHVXOVWRUWTCUUQZUHUIZUWTUDZVXNQZUHCYAZLVXOVWRV
      YBVYFVWRUXAVYBVWSCUEUWTUURZWJVWRVYEUHCVWRVYCCQZLZVYDRUYFVYIYBVWRVWPVYHVVL
      VWPUYHVWQTTVYIVYDVWRCUEVYCUWTVWSVEZXJVYIVYDVYJVHVYIVYDUYFKUGUYFVYDUSUGZVL
      ZVYIVYKVYIVYKLZUYGVYLVWRUYGVYHVYKVXCXCVYMUYFUXDUSUGUYGVLVYMUYFVYDUXDVWRVW
      LVYHVYKVXAXCZVYIVYDXDQVYKVYIVYDVYJVJZTVYIUXDXDQZVYKVWRVYPVYHVWTTTZVYIVYKV
      DVYIVYDUXDKUGVYKVYIVYDVYDCVYCUUSZUUTZUXCEUFZMNZUXDKVYIRVYTKUGZVYDWUAKUGZV
      YIVYTVYIVWGVYTUEQZVYIAVVKUXAAVVKUYHVYHUVAAVVKUYHVYHYDZVVLUXAUYGVYHUVBUVCZ
      VWGVYSUXCEVVLVYSVCQZUXAAWUGVVKACVYSHACVYRYEYCTTVWGUXBVYSQZLUXBCQZUXCUEQZW
      UHWUIVWGUXBCVYRUVDXEVWGWUIWUJWUHVWIYFYGZVFZWJVHVYIVYDVYTVYOVYIVYTVYIVWGWU
      DWUFVWGVYSUXCEVWGCVYSVWHVWGCVYRYEYCWUKVFWJVJYHVMVYIUXDWUAVYIVWGVYHLZUXDWU
      APZVYIVWGVYHWUFVWRVYHVDVNWUMCUXCVYCVYDEWUMEUVHEVYDUVEVWGVUNVYHVWHTWUMWUIL
      UXCVWGWUIWUJVYHVWIYFYIVWGVYHVDUXBVYCUWTUVIUVFZWJXAYJTYMVYMUYFUXDVYNVYQUVG
      VMUVJYKVYIVYDUYFVYOVYIVVKVWLWUEVWMWJVKVPYLYNVNUHCVXNUWTYOXKWCYPYCTVVLVXKU
      YMVVLCRUYNXLNZUWTVAZDUJZVVPVVLCWUPXMZXNZWURVVLWUSVCQZWUTVCQVVLVUNWUPVCQZL
      WVAVVLVUNWVBVYAVVLRUYNXOVNCWUPXPWJWUSXQXRWURWUTXSVVLCWUPDXTUKYCVVLVVOWUQD
      VVLVVOWUQVXDVYBVYDWUPQZUHCYAZLWUQVXDVYBWVDUXAVYBVVLVVNVYGUVKVXDWVCUHCVXDV
      YHLZVYDRUYNWVEYBWVEUYFWVEUYFAVVKVVOVYHYDXJUVLWVEVYDVXDCUEVYCUWTVXEVEZXJWV
      EVYDWVFVHWVEVYDUYNKUGUYNVYDUSUGZVLZWVEWVGWVEWVGLZWVHUXDUYNVXDVVNVYHWVGVXF
      XCZWVIUYNUXDWVIUYNUXDVXDUYNXDQZVYHWVGVXGXCZWVIUYNVYDUXDWVLWVIVYDWVICUEVYC
      UWTVXDUXAVYHWVGVXEXCVXDVYHWVGYQUVMVJZWVIUXDUYNXDWVJWVLUVNWVEWVGVDWVIVYDWU
      AUXDKWVIWUBWUCWVIVYTWVEWUDWVGVXDWUDVYHVVLVVOUXAWUDVXEWULVGTTZVHWVIVYDVYTW
      VMWVIVYTWVNVJYHVMWVIUXDWUAWVEWUNWVGVVLVVOUXAVYHWUNVXEWUOUVOTXAYJYMYRUVQUV
      PYKWVEVYDUYNWVEVYDWVFVJVXDWVKVYHVXGTVKVPYLYNVNUHCWUPUWTYOXKWCYPYCTVVLVXMU
      YMVVLVXLUYHVVOLZDUJZWEVXLWVPPVVLUYHVVODUVRUKVVLWVOVLZDUVSWVPWEPVVLWVQDVVL
      WVQYSVWRVVOVLYSVWRVVNUXAVWRUXDUYNVWRUXDUYNVWRUXDVWRUXDVVLUXAVULUYGVWJUVTX
      JUWAZVWRUXDUYFUYNWVRVXAVXBVXCVWRUYFVXAUWBUWCYRUWDUWEVVLUYHVVOUWFUWIUWGWVO
      DUWHXKWTTUYIVVPUWJUWKVVMVXIUYLUYNVUSMNZVUSONZMNZUYTVVMUYJUYLVXHWVTMVVLUYM
      VDVVMVVPCDEUYNVVMUYFSAVVKUYMYQZSUEQVVMUWLUKYTAVUNVVKUYMHXCAVVCVVKUYMIXCVV
      PWDWBUWMVVMWWAUYKSMNZUXIONZUYTVVMWWAUYLUYKVUSONZMNZWWDVVMWVTWWEUYLMVVMWVS
      UYKVUSOVVMUYFSUXIVVMUYFWWBYIZVVMWNZAUXIUWNQVVKUYMVVFXCZUWOUPUWPVVMUYKUEQU
      XIXIQWWFWWDPVVMUYFUXIWWBAVVIVVKUYMVVJXCZYTVVMUXIWWJXJUXIUYKUWQXHWTVVMWWCU
      YSUXIOVVMUYFUXISWWGWWIWWHUWRUPWTWTWTWTUWSYGWT $.
  $}

  ${
    $d N f $.  $d S f i $.  $d f i ph $.
    sticksstones23.1 $e |- ( ph -> N e. NN0 ) $.
    sticksstones23.2 $e |- ( ph -> S e. Fin ) $.
    sticksstones23.3 $e |- ( ph -> S =/= (/) ) $.
    sticksstones23.4 $e |- A = { f e. ( NN0 ^m S ) |
     sum_ i e. S ( f ` i ) <_ N } $.
    $( Non-exhaustive sticks and stones.  (Contributed by metakunt,
       7-May-2025.) $)
    sticksstones23 $p |- ( ph -> ( # ` A ) =
     ( ( N + ( # ` S ) ) _C ( # ` S ) ) ) $=
      ( chash cfv cn0 cv wa cab co a1i wcel eqtrd wf csu cle wbr caddc cbc cmap
      crab wceq df-rab cvv wb nn0ex elmapg syl2anc anbi1d abbidv sticksstones22
      cfn fveq2d eqid ) ABKLCMDNZUAZCENVBLEUBFUCUDZOZDPZKLFCKLZUEQVGUFQABVFKABV
      DDMCUGQZUHZVFBVIUIAJRAVIVBVHSZVDOZDPZVFVIVLUIAVDDVHUJRAVKVEDAVJVCVDAMUKSZ
      CUSSVJVCULVMAUMRHMCVBUKUSUNUOUPUQTTUTAVFCDEFGHIVFVAURT $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Continuation AKS
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    aks6d1c6.1 $e |- .~ = { <. e , f >. | ( e e. NN /\ f e.
     ( Base ` ( Poly1 ` K ) ) /\ A. y e. ( ( mulGrp ` K ) PrimRoots R )
     ( e ( .g ` ( mulGrp ` K ) ) ( ( ( eval1 ` K ) ` f ) ` y ) ) =
     ( ( ( eval1 ` K ) ` f ) ` ( e ( .g ` ( mulGrp ` K ) ) y ) ) ) } $.
    aks6d1c6.2 $e |- P = ( chr ` K ) $.
    aks6d1c6.3 $e |- ( ph -> K e. Field ) $.
    aks6d1c6.4 $e |- ( ph -> P e. Prime ) $.
    aks6d1c6.5 $e |- ( ph -> R e. NN ) $.
    aks6d1c6.6 $e |- ( ph -> N e. NN ) $.
    aks6d1c6.7 $e |- ( ph -> P || N ) $.
    aks6d1c6.8 $e |- ( ph -> ( N gcd R ) = 1 ) $.
    aks6d1c6.9 $e |- ( ph -> A < P ) $.
    aks6d1c6.10 $e |- G = ( g e. ( NN0 ^m ( 0 ... A ) ) |->
    ( ( mulGrp ` ( Poly1 ` K ) ) gsum ( i e. ( 0 ... A ) |-> ( ( g ` i )
    ( .g ` ( mulGrp ` ( Poly1 ` K ) ) ) ( ( var1 ` K ) ( +g ` ( Poly1 ` K ) )
    ( ( algSc ` ( Poly1 ` K ) ) ` ( ( ZRHom ` K ) ` i ) ) ) ) ) ) ) $.
    aks6d1c6.11 $e |- ( ph -> A e. NN0 ) $.
    aks6d1c6.12 $e |- E = ( k e. NN0 , l e. NN0 |->
    ( ( P ^ k ) x. ( ( N / P ) ^ l ) ) ) $.
    aks6d1c6.13 $e |- L = ( ZRHom ` ( Z/nZ ` R ) ) $.
    aks6d1c6.14 $e |- ( ph -> A. a e. ( 1 ... A ) N .~ ( ( var1 ` K )
     ( +g ` ( Poly1 ` K ) )
     ( ( algSc ` ( Poly1 ` K ) ) ` ( ( ZRHom ` K ) ` a ) ) ) ) $.
    aks6d1c6.15 $e |- ( ph -> ( x e. ( Base ` K ) |->
     ( P ( .g ` ( mulGrp ` K ) ) x ) ) e. ( K RingIso K ) ) $.
    aks6d1c6.16 $e |- ( ph -> M e. ( ( mulGrp ` K ) PrimRoots R ) ) $.
    aks6d1c6.17 $e |- H = ( h e. ( NN0 ^m ( 0 ... A ) ) |->
     ( ( ( eval1 ` K ) ` ( G ` h ) ) ` M ) ) $.
    aks6d1c6.18 $e |- D = ( # ` ( L " ( E " ( NN0 X. NN0 ) ) ) ) $.
    aks6d1c6.19 $e |- S = { s e. ( NN0 ^m ( 0 ... A ) ) |
     sum_ t e. ( 0 ... A ) ( s ` t ) <_ ( D - 1 ) } $.
    ${
      $d A g i $.  $d A i t $.  $d K g i $.  $d K i t $.  $d U g i $.
      $d U i t $.  $d g i ph $.  $d ph t $.
      aks6d1c6lem1.1 $e |- ( ph -> U e. ( NN0 ^m ( 0 ... A ) ) ) $.
      $( Lemma for claim 6, deduce exact degree of the polynomial.
         (Contributed by metakunt, 7-May-2025.) $)
      aks6d1c6lem1 $p |- ( ph -> ( ( deg1 ` K ) ` ( G ` U ) ) =
       sum_ t e. ( 0 ... A ) ( U ` t ) ) $=
        ( cfv cdg1 cn0 cc0 cfz co cmap cpl1 cmgp cv1 czrh cascl cplusg cmg cmpt
        cv cgsu csu wceq a1i fveq1d fveq2d cvv eqidd wa simplr oveq1d mpteq2dva
        wcel oveq2d ovexd fvmptd cle wbr cfield cidom fldidom syl fzfid cbs c0g
        wne eqid mgpbas cmnd crg ccrg fldcrngd crngring ply1ring ringmgp adantr
        wf nn0ex elmapd mpbid simpr ffvelcdmd 2fveq3 eleq1d wral ringmnd czring
        vr1cl cz syl2anc ralrimiva rspcdva c1 clt cxr eqtrd cmul zrhrhm elfzelz
        zringbas rhmf adantl ply1sclcl mndcl syl3anc mulgnn0cld ply1idom neeq1d
        crh deg1xrcl 0xr 1xr deg1sclle 0lt1 xrlelttrd mulg1 eqcomd cnzr drngnzr
        cdr isfld sylbi deg1pw eqtr2d breqtrd deg1add eqeltrd deg1nn0clb mpbird
        1nn0 wb idomnnzpownz deg1gprod simpld oveq12d ffvelcdmda deg1pow nn0cnd
        jca mulridd sumeq2dv ) AKSVHZUAVIVHZVHKNVJVKEVLVMZVNVMZUAVOVHZVPVHZPUWG
        PWCZNWCZVHZUAVQVHZUWKUAVRVHZVHZUWIVSVHZVHZUWIVTVHZVMZUWJWAVHZVMZWBZWDVM
        ZWBZVHZUWFVHZUWGDWCZKVHZDWEZAUWEUXFUWFAKSUXESUXEWFAUQWGWHWIAUXGUWJPUWGU
        WKKVHZUWTUXAVMZWBZWDVMZUWFVHZUXJAUXFUXNUWFANKUXDUXNUWHUXEWJAUXEWKAUWLKW
        FZWLZUXCUXMUWJWDUXQPUWGUXBUXLUXQUWKUWGWPZWLZUWMUXKUWTUXAUXSUWKUWLKAUXPU
        XRWMWHWNWOWQVGAUWJUXMWDWRWSWIAUXOUWGUXHUXMVHZUWFVHZDWEZUXJAUXOUYBWFVKUX
        OWTXAAPUXLUADUWGAUAXBWPZUAXCWPZUJUAXDXEZAVKEXFAUXLUWIXGVHZWPZUXLUWIXHVH
        ZXIZWLPUWGAUXRWLZUYGUYIUYJUYFUXAUWJUXKUWTUYFUWIUWJUWJXJZUYFXJZXKZUXAXJZ
        AUWJXLWPZUXRAUWIXMWPZUYOAUAXMWPZUYPAUAXNWPZUYQAUAUJXOUAXPXEZUWIUAUWIXJZ
        XQXEZUWIUWJUYKXRXEXSUYJUWGVJUWKKAUWGVJKXTZUXRAKUWHWPVUBVGAVJUWGKWJWJVJW
        JWPAYAWGAVKEVLWRYBYCZXSAUXRYDZYEZUYJUWNUXHUWOVHZUWQVHZUWSVMZUYFWPZUWTUY
        FWPDUWGUWKUXHUWKWFZVUHUWTUYFVUJVUGUWRUWNUWSUXHUWKUWQUWOYFWQZYGAVUIDUWGY
        HUXRAVUIDUWGAUXHUWGWPZWLZUWIXLWPZUWNUYFWPZVUGUYFWPZVUIAVUNVULAUYPVUNVUA
        UWIYIXEXSVUMUYQVUOAUYQVULUYSXSZUYFUWIUAUWNUWNXJZUYTUYLYKXEZVUMUYQVUFUAX
        GVHZWPZVUPVUQVUMYLVUTUXHUWOAYLVUTUWOXTZVULAUWOYJUAUULVMWPZVVBAUYQVVCUYS
        UAUWOUWOXJUUAXEYLVUTYJUAUWOUUCVUTXJZUUDXEXSVULUXHYLWPAUXHVKEUUBUUEYEZUW
        QUYFUWIUAVUFVUTUYTUWQXJZVVDUYLUUFYMZUYFUWSUWIUWNVUGUYLUWSXJZUUGUUHZYNXS
        VUDYOZUUIUYJUWTUWIUXAUXKAUWIXCWPZUXRAUYDVVKUYEUWIUAUYTUUJXEXSVVJUYJVUHU
        YHXIZUWTUYHXIDUWGUWKVUJVUHUWTUYHVUKUUKAVVLDUWGYHUXRAVVLDUWGVUMVVLVUHUWF
        VHZVJWPZVUMVVMYPVJVUMVVMUWNUWFVHZYPVUMUYFUWFUWSUAUWNVUGUWIUYTUWFXJZVUQU
        YLVVHVUSVVGVUMVUGUWFVHZYPVVOYQVUMVVQVKYPVUMVUPVVQYRWPVVGUYFUWFUWIUAVUGV
        VPUYTUYLUUMXEVKYRWPVUMUUNWGYPYRWPVUMUUOWGVUMUYQVVAVVQVKWTXAVUQVVEUWQUWF
        UWIUAVUFVUTVVPUYTVVDVVFUUPYMVKYPYQXAVUMUUQWGUURVUMVVOYPUWNUXAVMZUWFVHZY
        PVUMUWNVVRUWFVUMVVRUWNVUMVUOVVRUWNWFVUSUYFUXAUWJUWNUYMUYNUUSXEUUTWIZVUM
        UAUVAWPZYPVJWPZVVSYPWFAVWAVULAUYCVWAUJUYCUAUVCWPZUYRWLVWAUAUVDVWCVWAUYR
        UAUVBXSUVEXEXSVWBVUMUVMWGZUWFUWIUAUXAYPUWJUWNVVPUYTVURUYKUYNUVFYMZUVGUV
        HUVIVUMVVOVVSYPVVTVWEYSYSZVWDUVJVUMUYQVUIVVLVVNUVNVUQVVIUYFUWFUWIUAVUHU
        YHVVPUYTUYHXJUYLUVKYMUVLZYNXSVUDYOVUEUYNUVOUWBYNUVPUVQAUWGUYAUXIDVUMUYA
        UXIVUHUXAVMZUWFVHZUXIVUMUXTVWHUWFVUMPUXHUXLVWHUWGUXMWJVUMUXMWKVUMUWKUXH
        WFZWLZUXKUXIUWTVUHUXAVWKUWKUXHKVUMVWJYDZWIVWKUWRVUGUWNUWSVWKUWPVUFUWQVW
        KUWKUXHUWOVWLWIWIWQUVRAVULYDVUMUXIVUHUXAWRWSWIVUMVWIUXIVVMYTVMZUXIVUMUX
        IUWFUAUXAVUHAUYDVULUYEXSVVIVWGAUWGVJUXHKVUCUVSZUYNVVPUVTVUMVWMUXIYPYTVM
        UXIVUMVVMYPUXIYTVWFWQVUMUXIVUMUXIVWNUWAUWCYSYSYSUWDYSYSYS $.
    $}

    ${
      $d .~ a $.  $d A a $.  $d A g i $.  $d A h $.  $d A s $.  $d A x $.
      $d E e f y $.  $d E j $.  $d G e f w y $.  $d G h $.  $d J w $.
      $d K a w $.  $d K e f w y $.  $d K g i w $.  $d K h $.  $d K j w $.
      $d K o $.  $d K w x $.  $d M h $.  $d M j $.  $d M o $.  $d M y $.
      $d N a $.  $d N e f $.  $d N k l s $.  $d N x $.  $d P e f $.
      $d P k l s $.  $d P x $.  $d R e f y $.  $d R o $.  $d R x $.  $d S h $.
      $d U e f w y $.  $d U g i w $.  $d U h $.  $d V e f w y $.  $d V g i w $.
      $d V h $.  $d a ph w $.  $d g i ph w $.  $d h ph $.  $d j ph w $.
      $d o ph $.  $d ph s w $.  $d ph w x $.
      aks6d1c6lem2.1 $e |- ( ph -> U e. S ) $.
      aks6d1c6lem2.2 $e |- ( ph -> V e. S ) $.
      aks6d1c6lem2.3 $e |- ( ph -> ( ( H |` S ) ` U ) =
       ( ( H |` S ) ` V ) ) $.
      aks6d1c6lem2.4 $e |- ( ph -> U =/= V ) $.
      aks6d1c6lem2.5 $e |- J = ( j e. ( NN0 X. NN0 ) |->
       ( ( E ` j ) ( .g ` ( mulGrp ` K ) ) M ) ) $.
      aks6d1c6lem2.6 $e |- ( ph -> ( # ` ( L " ( E " ( NN0 X. NN0 ) ) ) )
         <_ ( # ` ( J " ( NN0 X. NN0 ) ) ) ) $.
      $( Every primitive root is root of G(u)-G(v).  (Contributed by metakunt,
         8-May-2025.) $)
      aks6d1c6lem2 $p |- ( ph -> D <_ ( # ` ( `' ( ( eval1 ` K ) `
       ( ( G ` U ) ( -g ` ( Poly1 ` K ) )
         ( G ` V ) ) ) " { ( 0g ` K ) } ) ) ) $=
        ( vw vo cn0 cima chash cfv csg co c0g cxr cvv wcel czrh eqeltrid imaexd
        fvexd hashxrcl syl cv cmgp cmg cmpt wceq a1i eqeltrd cle eqbrtrd wss wf
        wbr wfun wa ovexd simpr fveq2d fvmptd cbs adantr crg cn nnnn0d cdvds wi
        eqid wral mpbid cc0 cfz cmap c1 eleq2i sylib elrabi ffvelcdmd c1st cexp
        oveq2d c2nd cmul elmapd eqcomd eqtrd wb mpbird syl2anc cxp cpl1 ce1 csn
        ccnv czn nn0ex xpexd mptexd cnvexg elexd nfv fmptd ffun oveq1d fldcrngd
        ccrg mgpbas cmnd crngringd ringmgp aks6d1c2p1 ffvelcdmda cprimroots w3a
        ccmn crngmgp isprimroot eleqtrrdi mulgnn0cld cv1 aks6d1c5lem0 cmin crab
        simp1d csu mpd eqidd jca evl1subd fveq2 oveq2 eqeq12d cdiv cmpo cop vex
        simprd op1std op2ndd mpompt eqcomi eqtri cfield cprime cgcd xp1st xp2nd
        oveq12d adantl cplusg aks6d1c1rh aks6d1c1p1 rspcdva cres reseq1d ssrab2
        cascl eqsstrd resmptd fveq1d 3eqtrd cgrp crnggrpd fveval1fvcl grpsubeq0
        crs syl3anc elsng cdm cpws crh evl1rhm pwsbas ply1ring ringgrp grpsubcl
        rhmf feq3d ffund ffnd fndmd eleqtrd fvimacnv funimassd hashss xrletrd
        wfn ) AFUBVRVRUUAZVSZVTWAZKTWAZUGTWAZUCUUBWAZWBWAZWCZUCUUCWAZWAZUUEZUCW
        DWAZUUDZVSZVTWAZAFUDSUYSVSZVSZVTWAZWEVHAVUOWFWGVUPWEWGAUDVUNWFAUDIUUFWA
        ZWHWAWFVCAVUQWHWKWIWJVUOWFWLWMWIAUYTWFWGVUAWEWGAUBUYSWFAUBQUYSQWNZSWAZU
        EUCWOWAZWPWAZWCZWQZWFUBVVCWRZAVNWSAQUYSVVBWFAVRVRWFWFVRWFWGAUUGWSZVVEUU
        HUUIWTWJUYTWFWLWMAVULWFWGZVUMWEWGAVUIVUKWFAVUHWFWGVUIWFWGAVUFVUGWKVUHWF
        UUJWMWJZVULWFWLWMAFVUPVUAXAFVUPWRAVHWSVOXBAVVFUYTVULXCVUAVUMXAXEAVULWFV
        VGUUKAVPUYSVULUBAVPUULAUYSWFUBXDUBXFAQUYSVVBWFUBAVURUYSWGXGVUSUEVVAXHVN
        UUMUYSWFUBUUNWMAVPWNZUYSWGZXGZVVHUBWAVVHSWAZUEVVAWCZVULVVJQVVHVVBVVLUYS
        UBWFVVDVVJVNWSVVJVURVVHWRZXGZVUSVVKUEVVAVVNVURVVHSVVJVVMXIXJUUOAVVIXIZV
        VJVVKUEVVAXHXKVVJVVLVUHWAZVUKWGZVVLVULWGZVVJVVQVVPVUJWRZVVJVVPVVLVUBVUG
        WAZWAZVVLVUCVUGWAZWAZUCWBWAZWCZVUJVVJVUFVUDXLWAZWGZVVPVWEWRVVJUCXLWAZVW
        DVUDUCVWFVUBVUEVUCVUGVWAVWCVVLVUGXSZVUDXSZVWHXSZVWFXSZAUCUUQWGZVVIAUCUM
        UUPZXMZVVJVWHVVAVUTVVKUEVWHUCVUTVUTXSZVWKUURZVVAXSZAVUTUUSWGZVVIAUCXNWG
        ZVWSAUCVWNUUTZUCVUTVWPUVAWMXMVVJVVKAUYSXOVVHSAGRSUFUJUPUNUQVBUVBUVCZXPA
        UEVWHWGVVIAUEVUTXLWAZVWHAUEVXCWGZIUEVVAWCVUTWDWAZWRZVQWNZUEVVAWCVXEWRIV
        XGXQXEXRVQVRXTZAUEVUTIUVDWCZWGZVXDVXFVXHUVEVFAVUTVVAIUEVQAVWMVUTUVFWGVW
        NUCVUTVWPUVGWMAIUOXPVWRUVHYAUVOVWQUVIXMUVJZVVJVUBVWFWGZVWAVWAWRAVXLVVIA
        VRYBEYCWCZYDWCZVWFKTAEGNPVUDWOWAWPWAZTUCUCUVKWAZUMUNULVAUSVXPXSVXOXSUTU
        VLZAKVXMDWNUHWNZWADUVPFYEUVMWCXAXEZUHVXNUVNZWGZKVXNWGZAKJWGVYAVJJVXTKVI
        YFYGVYAVYBXRAVXSUHKVXNYHWSUVQZYIZXMZVVJVWAUVRUVSVVJVUCVWFWGZVWCVWCWRAVY
        FVVIAVXNVWFUGTVXQAUGVXTWGZUGVXNWGZAUGJWGVYGVKJVXTUGVIYFYGVYGVYHXRAVXSUH
        UGVXNYHWSUVQZYIZXMZVVJVWCUVRUVSVUEXSZVWDXSZUVTUWHVVJVWEVUJWRZVWAVWCWRZV
        VJVWAVVKUEVWBWAZVVAWCZVWCVVJVWAVVKUEVVTWAZVVAWCZVYQVVJVYSVWAVVJVVKCWNZV
        VTWAZVVAWCZVVKVYTVVAWCZVVTWAZWRZVYSVWAWRCVXIUEVYTUEWRZWUBVYSWUDVWAWUFWU
        AVYRVVKVVAVYTUEVVTUWAYLWUFWUCVVLVVTVYTUEVVKVVAUWBZXJUWCVVJVVKVUBHXEWUEC
        VXIXTVVJVVKGVVHYJWAZYKWCZUFGUWDWCZVVHYMWAZYKWCZYNWCZVUBHVVJUHVVHGVXRYJW
        AZYKWCZWUJVXRYMWAZYKWCZYNWCZWUMUYSSWFSUHUYSWURWQZWRVVJWUSSWUSRUJVRVRGRW
        NZYKWCZWUJUJWNZYKWCZYNWCZUWEZSRUJUHVRVRWURWVDVXRWUTWVBUWFWRZWUOWVAWUQWV
        CYNWVFWUNWUTGYKWUTWVBVXRRUWGZUJUWGZUWIYLWVFWUPWVBWUJYKWUTWVBVXRWVGWVHUW
        JYLUWSUWKSWVEVBUWLUWMUWLWSVVJVXRVVHWRZXGZWUOWUIWUQWULYNWVJWUNWUHGYKWVJV
        XRVVHYJVVJWVIXIZXJYLWVJWUPWUKWUJYKWVJVXRVVHYMWVKXJYLUWSVVOVVJWUIWULYNXH
        XKZVVJBCEGHIWUHLMNPWUMKTUCWUKUFUIUKULAUCUWNWGZVVIUMXMZAGUWOWGVVIUNXMZAI
        XOWGVVIUOXMZAUFXOWGVVIUPXMZAGUFXQXEVVIUQXMZAUFIUWPWCYEWRVVIURXMZAVXMVRK
        XDZVVIAVYBWVTVYCAVRVXMKWFWFVVEAYBEYCXHZYOYAXMUTAEVRWGVVIVAXMZVVIWUHVRWG
        AVVHVRVRUWQUWTZVVIWUKVRWGAVVHVRVRUWRUWTZWUMXSZAUFVXPUIWNUCWHWAWAVUDUXHW
        AWAVUDUXAWAWCHXEUIYEEYCWCXTVVIVDXMZABVWHGBWNVVAWCWQUCUCUXQWCWGVVIVEXMZU
        XBXBVVJCVWFVVAHILMVVKVVAVUBVUTVUGUKVYEVXBUXCYAAVXJVVIVFXMZUXDYPVVJVYRVY
        PVVKVVAAVYRVYPWRVVIAVYRKUAJUXEZWAZUGWWIWAVYPAWWJVYRAOKUEOWNZTWAZVUGWAZW
        AZVYRJWWIWFAWWIOVXNWWNWQZJUXEOJWWNWQAUAWWOJUAWWOWRAVGWSUXFAOVXNJWWNAJVX
        TVXNJVXTWRAVIWSVXTVXNXCAVXSUHVXNUXGWSUXIUXJYQZAWWKKWRZXGZUEWWMVVTWWRWWL
        VUBVUGWWRWWKKTAWWQXIXJXJUXKVJAUEVVTWKXKYPVLAOUGWWNVYPJWWIWFWWPAWWKUGWRZ
        XGZUEWWMVWBWWTWWLVUCVUGWWTWWKUGTAWWSXIXJXJUXKVKAUEVWBWKXKUXLXMYLYQVVJVV
        KVYTVWBWAZVVAWCZWUCVWBWAZWRZVYQVWCWRCVXIUEWUFWXBVYQWXCVWCWUFWXAVYPVVKVV
        AVYTUEVWBUWAYLWUFWUCVVLVWBWUGXJUWCVVJVVKVUCHXEWXDCVXIXTVVJVVKWUMVUCHWVL
        VVJBCEGHIWUHLMNPWUMUGTUCWUKUFUIUKULWVNWVOWVPWVQWVRWVSAVXMVRUGXDZVVIAVYH
        WXEVYIAVRVXMUGWFWFVVEWWAYOYAXMUTWWBWWCWWDWWEWWFWWGUXBXBVVJCVWFVVAHILMVV
        KVVAVUCVUTVUGUKVYKVXBUXCYAWWHUXDYQVVJUCUXMWGZVWAVWHWGVWCVWHWGVYNVYOYRAW
        XFVVIAUCVWNUXNXMVVJVWHVUDUCVWFVUBVUGVVLVWIVWJVWKVWLVWOVXKVYEUXOVVJVWHVU
        DUCVWFVUCVUGVVLVWIVWJVWKVWLVWOVXKVYKUXOVWHUCVWDVWAVWCVUJVWKVUJXSVYMUXPU
        XRYSYQVVJVVPWFWGVVQVVSYRVVJVVLVUHWKVVPVUJWFUXSWMYSVVJVUHXFZVVLVUHUXTZWG
        VVQVVRYRAWXGVVIAVWHVWHVUHAVUHVWHVWHYDWCZWGVWHVWHVUHXDAVWFWXIVUFVUGAVWFW
        XIVUGXDVWFUCVWHUYAWCZXLWAZVUGXDZAVUGVUDWXJUYBWCWGZWXLAVWMWXMVWNVWHVUDUC
        WXJVUGVWIVWJWXJXSZVWKUYCWMVWFWXKVUDWXJVUGVWLWXKXSUYHWMAWXIWXKVUGVWFAWVM
        VWHWFWGWXIWXKWRUMAUCXLWKZVWHUCVWHUWNWFWXJWXNVWKUYDYTUYIYSAVUDUXMWGZVXLV
        YFVWGAVUDXNWGZWXPAVWTWXQVXAVUDUCVWJUYEWMVUDUYFWMVYDVYJVWFVUDVUEVUBVUCVW
        LVYLUYGUXRYIAVWHVWHVUHWFWFWXOWXOYOYAZUYJXMVVJVVLVWHWXHVXKVVJWXHVWHVVJVW
        HVUHAVUHVWHUYRVVIAVWHVWHVUHWXRUYKXMUYLYPUYMVVLVUKVUHUYNYTYAWTUYOVULUYTW
        FUYPYTUYQ $.
    $}

    ${
      $d .~ a $.  $d g i ph $.  $d S s t $.  $d G h $.  $d S h j $.  $d M y $.
      $d N e f $.  $d h j ph $.  $d N s $.  $d K t x $.  $d R e f $.  $d P x $.
      $d R v x y $.  $d K h j $.  $d K e f $.  $d M h j v $.  $d P k l s $.
      $d N k l x $.  $d P e f $.  $d a ph u v $.  $d k l ph x y $.
      $d S g i u x y $.  $d S a v $.  $d ph s t w $.  $d K a $.
      $d K g i v x y $.  $d E x $.  $d E j $.  $d E e f y $.  $d A s t w $.
      $d A a u $.  $d G i t y $.  $d G g y $.  $d D s u v $.  $d H h j u $.
      $d H a u v $.  $d e f u v $.  $d H g i x y $.  $d A h j $.  $d D w $.
      $d G e f $.  $d N a $.  $d A g i v x $.  $d H s t u v $.
      aks6d1c6lem3.1 $e |- J = ( j e. ( NN0 X. NN0 ) |->
       ( ( E ` j ) ( .g ` ( mulGrp ` K ) ) M ) ) $.
      aks6d1c6lem3.2 $e |- ( ph -> ( # ` ( L " ( E " ( NN0 X. NN0 ) ) ) )
         <_ ( # ` ( J " ( NN0 X. NN0 ) ) ) ) $.
      $( Claim 6 of Theorem 6.1 of ~ https://www3.nd.edu/%7eandyp/notes/AKS.pdf
         TODO, eliminate hypothesis.  (Contributed by metakunt, 8-May-2025.) $)
      aks6d1c6lem3 $p |- ( ph -> ( ( D + A ) _C ( D - 1 ) ) <_
         ( # ` ( H " ( NN0 ^m ( 0 ... A ) ) ) ) ) $=
        ( vv vu caddc co c1 cbc cima chash cfv cn0 cc0 cmap wcel eqeltrid nn0zd
        cz eqid nn0cnd eqcomd wceq syl oveq2d eqtrd cle wbr wa a1i cvv wne czrh
        c0 fvexd imaexd jca sylib wss wb cexp cmul wral ovexd ralrimiva syl2anc
        cv necon3bid mpbird cbs ccrg wf 4syl simpr adantr syl3anc mpbid eqeltrd
        crg eqbrtrd rexrd cxr csu wi fveq1d breq1d biimpd mpd wn ad4antr adantl
        wrex ad5antr ad3antrrr vw cmin cfz cxp czn hashscontpowcl zcnd nppcan3d
        1cnd hashfz0 1zzd zsubcld 0p1e1 ne0d xpnz wfn cdiv fnmpo ssidd fnimaeq0
        czring crh nnnn0d zncrng crngring zrhrhm zringbas rhmf ffnd cmpo simprl
        crn simprr oveq12d simplr ovmpod cprime cn ad2antrr prmnn zexpcld cdvds
        nnzd nnne0d dvdsval2 zmulcld ffnov sylibr sseq1d hashge1 eqcomi breqtrd
        frn fnima cr 0red 1red nn0red leaddsub elnn0z cfn hashcl nn0addcld bccl
        fzfid cxnn0 ce1 cmpt mptexd ex simpl sumeq2dv elrab imim1d ssrdv imass2
        crab ssexd hashxnn0 xnn0xr cres wf1 cuz nn0ge0d 0zd eluz sticksstones23
        pncand fzn0 bccmpl resexd hashf1dmcdm wo fveq2d rabssdv eqsstrid sselda
        simp2 cpl1 fldcrngd cmgp cmg c0g cprimroots w3a ccmn crngmgp isprimroot
        fvmptd simp1d eleqtrdi cv1 aks6d1c5lem0 ffvelcdmd fveval1fvcl feqresmpt
        mgpbas fmptd feq1d ffrn feq3d notnotd a1d con4d df-an csg ccnv csn cdg1
        df-ima cfield fldidom cgrp ply1crng ringgrp aks6d1c5 f1f eleq2i simplbi
        cidom sylbi elrabi grpsubcl neqne f1fveq bicomd fta1g deg1xrcl resubcld
        grpsubeq0 clt simp-4l cnvexg cif ifcld idomringd deg1suble cascl cplusg
        id crs simpllr aks6d1c6lem1 bitri simprd simp-4r ifbothda xrletrd ltm1d
        cgcd jca31 aks6d1c6lem2 xrltletrd xrlelttrd deg1nn0clb xrltnle pm2.21dd
        sylbird necon3abid necon1bbid pm5.74i notbii imbi1d imp fveqeq2 equequ1
        biidd imbi12d notbid fveq2 eqeq2d equequ2 cbvrex2vw bilani rexnal2 jaod
        r19.29vva ianor dff13 pm2.61dan hashss ) AFEVLVMZFVNUUBVMZVOVMZTJVPZVQV
        RZTVSVTEUUCVMZWAVMZVPZVQVRZAWUDAWUDAWUBVSWBWUCWEWBZWUDVSWBAWUBWUCWUGVQV
        RZVLVMZVSAWUBWUCEVNVLVMZVLVMZWUMAWUOWUBAFVNEAFAFAFUCRVSVSUUDZVPZVPZVQVR
        ZVSVFAGIQRUCUEIUUEVRZUHUNULUOUMUPUTVAWUTWFZUUFWCZWDZUUGAUUIAEUSWGUUHWHA
        WUNWULWUCVLAWULWUNAEVSWBZWULWUNWIUSEUUJWJWHWKWLZAWUCWULAWUKVTWUCWMWNZWO
        WUCVSWBAWUKWVFAFVNWVCAUUKUULZAVTVNVLVMZFWMWNZWVFAWVHVNFWMWVHVNWIAUUMWPA
        WURWQWBZWURWTWRZVNFWMWNAUCWUQWQAUCWUTWSVRWQVAAWUTWSXAWCXBAWVKWUQWTWRZAW
        VLWUPWTWRZAVSWTWRZWVNWOWVMAWVNWVNAVSEUSUUNZWVOXCVSVSUUOXDAWUQWTWUPWTARW
        UPUUPZWUPWUPXEWUQWTWIZWUPWTWIXFAGQXMZXGVMZUEGUUQVMZUHXMZXGVMZXHVMZWQWBZ
        UHVSXIZQVSXIWVPAWWEQVSAWVRVSWBWOZWWDUHVSWWFWWAVSWBWOWVSWWBXHXJXKXKQUHVS
        VSWWCRWQUTUURWJZAWUPUUSWUPWUPRUUTXLXNXOAWURWTWUQWTAUCWEUUPWUQWEXEZWURWT
        WIWVQXFAWEWUTXPVRZUCAWUTXQWBZWUTYEWBUCUVAWUTUVBVMWBWEWWIUCXRAIVSWBWWJAI
        UMUVCZIWUTWVAUVDWJWUTUVEWUTUCVAUVFWEWWIUVAWUTUCUVGWWIWFUVHXSUVIAWWHRUVL
        ZWEXEZAWUPWERXRZWWMAWVPBXMZCXMZRVMZWEWBZCVSXIZBVSXIZWOWWNAWVPWWTWWGAWWS
        BVSAWWOVSWBZWOZWWRCVSWXBWWPVSWBZWOZWWQGWWOXGVMZWVTWWPXGVMZXHVMZWEWXDQUH
        WWOWWPVSVSWWCWXGRWQRQUHVSVSWWCUVJWIWXDUTWPWXDWVRWWOWIZWWAWWPWIZWOWOZWVS
        WXEWWBWXFXHWXJWVRWWOGXGWXDWXHWXIUVKWKWXJWWAWWPWVTXGWXDWXHWXIUVMWKUVNAWX
        AWXCUVOZWXBWXCXTZWXDWXEWXFXHXJUVPWXDWXEWXFWXDGWWOWXDGWXDGUVQWBZGUVRWBAW
        XMWXAWXCULUVSGUVTWJZUWCZWXKUWAWXDWVTWWPWXDGUEUWBWNZWVTWEWBZAWXPWXAWXCUO
        UVSWXDGWEWBGVTWRUEWEWBZWXPWXQXFWXOWXDGWXNUWDWXBWXRWXCAWXRWXAAUEUNUWCYAY
        AGUEUWEYBYCWXLUWAUWFYDXKXKXCBCVSVSWERUWGUWHWUPWERUWMWJAWUQWWLWEAWVPWUQW
        WLWIWWGWUPRUWNWJUWIXOWEWUQUCUUTXLXNXOWVJWVKWOZVNWUSFWMWURWQUWJWUSFWIWXS
        FWUSVFUWKWPUWLXLYFAVTUWOWBVNUWOWBFUWOWBZWVIWVFXFAUWPAUWQAFWVBUWRZVTVNFU
        WSYBYCXCWUCUWTUWHZAWUGUXAWBWULVSWBAVTEUXEZWUGUXBWJZUXCZYDWVGWUCWUBUXDXL
        UWRYGAWUFUXFWBZWUFYHWBAWUEWQWBZWYFAWUEWUIWQATWUHWQATNWUHUDNXMZSVRZUBUXG
        VRZVRZVRZUXHZWQVEANWUHWYLWQAVSWUGWAXJUXIWCXBZAJWUHXEZWUEWUIXEZAWYOWUGDX
        MZUFXMZVRZDYIZWUCWMWNZUFWUHUXQZWUHXEAUUAXUBWUHAUUAXMZWUHWBZWUGWYQXUCVRZ
        DYIZWUCWMWNZWOZXUDYJXUCXUBWBZXUDYJAXUHXUDAXUDXUGUVKUXJAXUIXUHXUDAXUIXUH
        XUIXUHXFAXUAXUGUFXUCWUHWYRXUCWIZWYTXUFWUCWMXUJWUGWYSXUEDXUJWYQWUGWBZWOW
        YQWYRXUCXUJXUKUXKYKUXLYLUXMWPYMUXNYNUXOAJXUBWUHJXUBWIAVGWPUWIXOJWUHTUXP
        WJZUXRWUEWQUXSWJWUFUXTWJAWUJUXFWBZWUJYHWBAWUIWQWBZXUMWYNWUIWQUXSWJWUJUX
        TWJAJWUETJUYAZUYBZWUDWUFWMWNZAXUPWOZWUDJVQVRZWUFWMAWUDXUSWIXUPAWUDWUMWU
        MWULUUBVMZVOVMZXUSAWUBWUMWUCXUTVOWVEAXUTWUCAWUCWULAWUCWYBWGAWULWYDWGUYH
        WHUVNAXUSXVAAXUSWUMWULVOVMZXVAAJWUGUFDWUCWYBWYCAEVTUYCVRWBZWUGWTWRAXVCV
        TEWMWNZAEUSUYDAVTWEWBEWEWBXVCXVDXFAUYEAEUSWDVTEUYFXLXOVTEUYIUWHVGUYGAWU
        MVSWBWULWEWBXVBXVAWIWYEAWULWYDWDWULWUMUYJXLWLWHWLYAXURXUOWQWBWYGXUPXUSW
        UFWMWNXURTJWQXURTWYMWQTWYMWIZXURVEWPXURNWUHWYLWQXURVSWUGWAXJUXIYDZUYKXU
        RTJWQXVFXBAXUPXTJWUEXUOWQWQUYLYBYFAXUPYOZXUQAJWUEXUOXRZWWOXUOVRWWPXUOVR
        ZWIZWWOWWPWIZYJZCJXIBJXIZWOZYOZXUQYJZXVGXUQYJAXVHYOZXVMYOZUYMZXUQYJXVPA
        XVQXUQXVRAXUQXVQAXVQYOXUQYOAXVHAXVHJXUOUVLZXUOXRZAJUBXPVRZXUOXRZXWAAXWC
        JXWBPJPXMZTVRZUXHZXRAPJXWEXWBXWFAXWDJWBZWOZXWEUDXWDSVRZWYJVRZVRZXWBXWHN
        XWDWYLXWKWUHTWQXVEXWHVEWPXWHWYHXWDWIZWOZUDWYKXWJXWMWYIXWIWYJXWMWYHXWDSX
        WHXWLXTUYNUYNYKAJWUHXWDAJXUBWUHVGAXUAUFWUHWUHAWYRWUHWBXUAUYRUYOUYPZUYQZ
        XWHUDXWJXAVUIXWHXWBUBUYSVRZUBXWPXPVRZXWIWYJUDWYJWFZXWPWFZXWBWFZXWQWFZAU
        BXQWBZXWGAUBUKUYTZYAAUDXWBWBXWGAUDUBVUAVRZXPVRZXWBAUDXXEWBZIUDXXDVUBVRZ
        VMXXDVUCVRZWIZVJXMZUDXXGVMXXHWIIXXJUWBWNYJVJVSXIZAUDXXDIVUDVMWBZXXFXXIX
        XKVUEZVDAXXLXXMAXXDXXGIUDVJAXXBXXDVUFWBXXCUBXXDXXDWFZVUGWJWWKXXGWFVUHYM
        YNVUJXWBXXEXWBUBXXDXXNXWTVUQUWKVUKYAXWHWUHXWQXWDSAWUHXWQSXRZXWGAEGMOXWP
        VUAVRVUBVRZSUBUBVULVRZUKULUJUSUQXXQWFZXXPWFZURVUMYAXWOVUNVUOYDXWFWFVURA
        JXWBXUOXWFAPWUHWQJTANWUHWYLWQTAWYHWUHWBWOUDWYKXAVEVURXWNVUPVUSXOJXWBXUO
        VUTWJAWUEXVTXUOJWUEXVTWIATJVVJWPVVAXOVVBVVCVVDAXVLYOZCJYRBJYRZXUQYJXVRX
        UQYJAXYAXUQAXYAWOZVKXMZXUOVRZXXJXUOVRZWIZXYCXXJWIZYJZYOZXUQVKVJJJXYBXYC
        JWBZWOZXXJJWBZWOZXYIXUQXYMXYFXYGYOZYOZYJZYOZXUQYJXYIXUQYJXYMXYQXYFXYNWO
        ZXUQXYRXYQXFXYMXYFXYNVVEWPXYMXYRXUQXYMXYRWOZXYCSVRZXXJSVRZXWPVVFVRZVMZW
        YJVRZVVGZUBVUCVRZVVHZVPZVQVRZYUCUBVVIVRZVRZWMWNZXUQXYSXWQYUJXWPUBYUCWYJ
        YUFXWPVUCVRZXWSXXAYUJWFZXWRYUFWFYUMWFZAUBVVTWBZXYAXYJXYLXYRAUBVVKWBZYUP
        UKUBVVLWJYPZXYSXWPVVMWBZXYTXWQWBZYUAXWQWBZYUCXWQWBZAYUSXYAXYJXYLXYRAXXB
        XWPXQWBXWPYEWBYUSXXCXWPUBXWSVVNXWPUVEXWPVVOXSYPZXYSWUHXWQXYCSXYSWUHXWQS
        UYBZXXOAYVDXYAXYJXYLXYRAEGMOXXPSUBXXQUKULUJUSUQXXRXXSURVVPYPZWUHXWQSVVQ
        WJZXYMXYCWUHWBZXYRXYKYVGXYLXYJYVGXYBXYJXYCXUBWBZYVGJXUBXYCVGVVRZYVHYVGW
        UGWYQXYCVRZDYIZWUCWMWNZXUAYVLUFXYCWUHWYRXYCWIZWYTYVKWUCWMYVMWUGWYSYVJDY
        VMXUKWOWYQWYRXYCYVMXUKUXKYKUXLYLUXMZVVSVWAYQYAYAZVUNZXYSWUHXWQXXJSYVFXY
        MXXJWUHWBZXYRXYLYVQXYKXYLXXJXUBWBZYVQJXUBXXJVGVVRZXUAUFXXJWUHVWBVWAZYQY
        AZVUNZXWQXWPYUBXYTYUAXXAYUBWFZVWCYBZXYSYUCYUMWRZXYTYUAWRZXYSXYCXXJWRZYW
        FXYRYWGXYMXYNYWGXYFXYCXXJVWDYQZYQXYSYWGYWFXYSXYCXXJXYTYUAXYSXYTYUAWIZXY
        GXYSYVDYVGYVQWOYWIXYGXFYVEXYSYVGYVQYVOYWAXCWUHXWQXYCXXJSVWEXLVWFXNYMYNX
        YSYUSYUTYVAYWEYWFXFYVCYVPYWBYUSYUTYVAVUEYUCYUMXYTYUAXWQXWPYUBXYTYUAYUMX
        XAYUOYWCVWJXNYBXOZVWGXYSYUKYUIVWKWNZYULYOZXYSYUKWUCYUIXYSYVBYUKYHWBZYWD
        XWQYUJXWPUBYUCYUNXWSXXAVWHWJZXYSWUCXYSFVNAWXTXYAXYJXYLXYRWYAYPZXYSUWQVW
        IYGZXYSAYUHWQWBZYUIUXFWBZYUIYHWBZAXYAXYJXYLXYRVWLZAYUEYUGWQAYUDWQWBZYUE
        WQWBZAYUCWYJXAYUDWQVWMZWJXBYUHWQUXSZYUIUXTZXSZXYSYUKXYTYUJVRZYUAYUJVRZW
        MWNZYXHYXGVWNZWUCYWNXYSYXIYXHYXGYHXYSYVAYXHYHWBYWBXWQYUJXWPUBYUAYUNXWSX
        XAVWHWJXYSYUTYXGYHWBYVPXWQYUJXWPUBXYTYUNXWSXXAVWHWJVWOYWPXYSXWQYUJUBXYT
        YUAYUBXWPXWSYUNXYSUBYURVWPZXXAYWCYVPYWBVWQYXIYXHWUCWMWNYXGWUCWMWNYXJWUC
        WMWNXYSYXHYXGYXHYXJWIZYXHYXJWUCWMYXLVWTYLYXGYXJWIZYXGYXJWUCWMYXMVWTYLXY
        SYXIWOZYXHWUGWYQXXJVRZDYIZWUCWMYXNBCDEFGHIJXXJKLMNOQRSTUBUCUDUEUFUGUHUI
        UJAYUQXYAXYJXYLXYRYXIUKYSAWXMXYAXYJXYLXYRYXIULYSAIUVRWBZXYAXYJXYLXYRYXI
        UMYSAUEUVRWBZXYAXYJXYLXYRYXIUNYSAWXPXYAXYJXYLXYRYXIUOYSAUEIVXJVMVNWIZXY
        AXYJXYLXYRYXIUPYSAEGVWKWNZXYAXYJXYLXYRYXIUQYSURAWVDXYAXYJXYLXYRYXIUSYSU
        TVAAUEXXQUGXMUBWSVRVRXWPVWRVRVRXWPVWSVRVMHWNUGVNEUUCVMXIZXYAXYJXYLXYRYX
        IVBYSABXWBGWWOXXGVMUXHUBUBVXAVMWBZXYAXYJXYLXYRYXIVCYSAXXLXYAXYJXYLXYRYX
        IVDYSVEVFVGYXNXYLYVQXYKXYLXYRYXIVXBZYVTWJVXCYXNYVQYXPWUCWMWNZYXNXYLYVQY
        YDWOZYYCXYLYVRYYEYVSXUAYYDUFXXJWUHWYRXXJWIZWYTYXPWUCWMYYFWUGWYSYXODYYFX
        UKWOWYQWYRXXJYYFXUKUXKYKUXLYLUXMVXDXDVXEYFXYSYXIYOZWOZYXGYVKWUCWMYYHBCD
        EFGHIJXYCKLMNOQRSTUBUCUDUEUFUGUHUIUJAYUQXYAXYJXYLXYRYYGUKYSAWXMXYAXYJXY
        LXYRYYGULYSAYXQXYAXYJXYLXYRYYGUMYSAYXRXYAXYJXYLXYRYYGUNYSAWXPXYAXYJXYLX
        YRYYGUOYSAYXSXYAXYJXYLXYRYYGUPYSAYXTXYAXYJXYLXYRYYGUQYSURAWVDXYAXYJXYLX
        YRYYGUSYSUTVAAYYAXYAXYJXYLXYRYYGVBYSAYYBXYAXYJXYLXYRYYGVCYSAXXLXYAXYJXY
        LXYRYYGVDYSVEVFVGXYSYVGYYGYVOYAVXCYYHYVGYVLYYHXYJYVGYVLWOZXYBXYJXYLXYRY
        YGVXFXYJYVHYYIYVIYVNVXDXDVXEYFVXGVXHXYSWUCFYUIYWPXYSFYWOYGYXFXYSFYWOVXI
        XYSAXYJWOZXYLWOZXYRWOZFYUIWMWNXYSYYKXYRXYSAXYJXYLYWTXYBXYJXYLXYRVXBXYKX
        YLXYRUVOVXKXYMXYRXTXCYYLBCDEFGHIJXYCKLMNOPQRSTUAUBUCUDUEXXJUFUGUHUIUJAY
        UQXYJXYLXYRUKYTAWXMXYJXYLXYRULYTAYXQXYJXYLXYRUMYTAYXRXYJXYLXYRUNYTAWXPX
        YJXYLXYRUOYTAYXSXYJXYLXYRUPYTAYXTXYJXYLXYRUQYTURAWVDXYJXYLXYRUSYTUTVAAY
        YAXYJXYLXYRVBYTAYYBXYJXYLXYRVCYTAXXLXYJXYLXYRVDYTVEVFVGAXYJXYLXYRVXBYYJ
        XYLXYRUVOYYKXYFXYNUVKXYRYWGYYKYWHYQVHAWUSUAWUPVPVQVRWMWNXYJXYLXYRVIYTVX
        LWJVXMVXNXYSYWMYWSYWKYWLXFXYSYUKXYSYUKXYSYWEYUKVSWBZYWJXYSUBYEWBYVBYWEY
        YMXFYXKYWDXWQYUJXWPUBYUCYUMYUNXWSYUOXXAVXOXLYCUWRYGXYSYWRYWSXYSYWQYWRXY
        SYUEYUGWQXYSYXAYXBXYSYUCWYJXAYXCWJXBYXDWJYXEWJYUKYUIVXPXLYCVXQUXJVXRXYM
        XYQXYIXUQXYQXYIXFXYMXYPXYHXYFXYOXYGXYFXYNXYCXXJXYFXYGXYCXXJXYFXYGVYGVXS
        VXTVYAVYBWPVYCYCVYDXYAXYIVJJYRVKJYRAXXTXYIXYDXVIWIZXYCWWPWIZYJZYOBCVKVJ
        JJWWOXYCWIZXVLYYPYYQXVJYYNXVKYYOWWOXYCXVIXUOVYEBVKCVYFVYHVYIWWPXXJWIZYY
        PXYHYYRYYNXYFYYOXYGYYRXVIXYEXYDWWPXXJXUOVYJVYKCVJVKVYLVYHVYIVYMVYNVYQUX
        JAXYAXVRXUQXYAXVRXFAXVLBCJJVYOWPVYCYCVYPAXVOXVSXUQAXVOXVSXVOXVSXFAXVHXV
        MVYRWPYMUXNYNAXVGXVOXUQAXVGXVOAXUPXVNXUPXVNXFABCJWUEXUOVYSWPVYIYMUXNYNV
        YDVYTAXUNWYPWUFWUJWMWNWYNXULWUIWUEWQWUAXLVXH $.
    $}
  $}

  ${
    $d .~ a $.  $d P k l s $.  $d h ph $.  $d N s $.  $d k l ph v $.
    $d ph w $.  $d K h $.  $d k l ph y $.  $d K g x $.  $d K e f $.
    $d K m n $.  $d N k l x $.  $d U w $.  $d R x $.  $d P j v $.  $d N e f $.
    $d R w $.  $d S s t $.  $d P e f $.  $d N j v $.  $d R e f y $.
    $d K c j v $.  $d M y $.  $d N a $.  $d M h j $.  $d P k l x $.
    $d S h j $.  $d c j ph v $.  $d U c j v $.  $d S a $.  $d S g i x y $.
    $d g i ph x $.  $d M c v $.  $d M w $.  $d ph s t $.  $d K w $.  $d a ph $.
    $d P b $.  $d N b $.  $d K a $.  $d K i t x y $.  $d D s $.  $d G h $.
    $d G t $.  $d G g i y $.  $d H s t $.  $d H h j $.  $d E x $.
    $d E e f y $.  $d E c j v $.  $d H g i x y $.  $d A a $.  $d G e f $.
    $d A b $.  $d H a $.  $d A g i x $.  $d A h j $.  $d A s t $.
    aks6d1c6lem4.1 $e |- .~ = { <. e , f >. | ( e e. NN /\ f e.
     ( Base ` ( Poly1 ` K ) ) /\ A. y e. ( ( mulGrp ` K ) PrimRoots R )
     ( e ( .g ` ( mulGrp ` K ) ) ( ( ( eval1 ` K ) ` f ) ` y ) ) =
     ( ( ( eval1 ` K ) ` f ) ` ( e ( .g ` ( mulGrp ` K ) ) y ) ) ) } $.
    aks6d1c6lem4.2 $e |- P = ( chr ` K ) $.
    aks6d1c6lem4.3 $e |- ( ph -> K e. Field ) $.
    aks6d1c6lem4.4 $e |- ( ph -> P e. Prime ) $.
    aks6d1c6lem4.5 $e |- ( ph -> R e. NN ) $.
    aks6d1c6lem4.6 $e |- ( ph -> N e. NN ) $.
    aks6d1c6lem4.7 $e |- ( ph -> P || N ) $.
    aks6d1c6lem4.8 $e |- ( ph -> ( N gcd R ) = 1 ) $.
    aks6d1c6lem4.9 $e |- ( ph -> A. b e. ( 1 ... A ) ( b gcd N ) = 1 ) $.
    aks6d1c6lem4.10 $e |- G = ( g e. ( NN0 ^m ( 0 ... A ) ) |->
    ( ( mulGrp ` ( Poly1 ` K ) ) gsum ( i e. ( 0 ... A ) |-> ( ( g ` i )
    ( .g ` ( mulGrp ` ( Poly1 ` K ) ) ) ( ( var1 ` K ) ( +g ` ( Poly1 ` K ) )
    ( ( algSc ` ( Poly1 ` K ) ) ` ( ( ZRHom ` K ) ` i ) ) ) ) ) ) ) $.
    aks6d1c6lem4.11 $e |- A = ( |_ ` ( ( sqrt ` ( phi ` R ) ) x.
     ( 2 logb N ) ) ) $.
    aksaks6dlem4.12 $e |- E = ( k e. NN0 , l e. NN0 |->
    ( ( P ^ k ) x. ( ( N / P ) ^ l ) ) ) $.
    aks6d1c6lem4.13 $e |- L = ( ZRHom ` ( Z/nZ ` R ) ) $.
    aks6d1c6lem4.14 $e |- ( ph -> A. a e. ( 1 ... A ) N .~ ( ( var1 ` K )
     ( +g ` ( Poly1 ` K ) )
     ( ( algSc ` ( Poly1 ` K ) ) ` ( ( ZRHom ` K ) ` a ) ) ) ) $.
    aks6d1c6lem4.15 $e |- ( ph -> ( x e. ( Base ` K ) |->
     ( P ( .g ` ( mulGrp ` K ) ) x ) ) e. ( K RingIso K ) ) $.
    aks6d1c6lem4.16 $e |- ( ph -> M e. ( ( mulGrp ` K ) PrimRoots R ) ) $.
    aks6d1c6lem4.17 $e |- H = ( h e. ( NN0 ^m ( 0 ... A ) ) |->
     ( ( ( eval1 ` K ) ` ( G ` h ) ) ` M ) ) $.
    aks6d1c6lem4.18 $e |- D = ( # ` ( L " ( E " ( NN0 X. NN0 ) ) ) ) $.
    aks6d1c6lem4.19 $e |- S = { s e. ( NN0 ^m ( 0 ... A ) ) |
     sum_ t e. ( 0 ... A ) ( s ` t ) <_ ( D - 1 ) } $.
    aks6d1c6lem4.20 $e |- J = ( j e. ZZ |->
       ( j ( .g ` ( ( mulGrp ` K ) |`s U ) ) M ) ) $.
    aks6d1c6lem4.21 $e |- ( ph -> ( # ` ( L " ( E " ( NN0 X. NN0 ) ) ) )
         <_ ( # ` ( J " ( E " ( NN0 X. NN0 ) ) ) ) ) $.
    aks6d1c6lem4.22 $e |- U = { m e. ( Base ` ( mulGrp ` K ) ) |
     E. n e. ( Base ` ( mulGrp ` K ) ) ( n ( +g `
      ( mulGrp ` K ) ) m ) = ( 0g ` ( mulGrp ` K ) ) } $.
    $( Claim 6 of Theorem 6.1 of ~ https://www3.nd.edu/%7eandyp/notes/AKS.pdf
       Add hypothesis on coprimality, lift function to the integers so that
       group operations may be applied.  Inline definition.  (Contributed by
       metakunt, 14-May-2025.) $)
    aks6d1c6lem4 $p |- ( ph -> ( ( D + A ) _C ( D - 1 ) ) <_
         ( # ` ( H " ( NN0 ^m ( 0 ... A ) ) ) ) ) $=
      ( vv vc vw cn0 cv cfv cmg co cmpt clt wbr simpr wn wa cgcd c1 wceq cle cn
      wcel syl nnred c2 clogb cz cc0 nnnn0d cr a1i wne syl3anc eqcomd nnge1d wb
      cmul syl2anc mpbid eqeltrid wi oveq1 wral adantr nnzd mpd cdvds eqid cima
      biimpd chash eqcomi cres cexp adantl zexpcld vex oveq2d oveq1d cvv wf wfn
      ovexd fmptd ffn eqidd fveq2d eqtrd cxp cmgp cprime prmnn csqrt cfl phicld
      cphi nn0ge0d resqrtcld 2re 2pos nngt0d 1red 1lt2 ltned relogbcld remulcld
      flcld sqrtge0d cc recnd gt0ne0d logb1 leidd 0lt1 logblebd eqbrtrd mulge0d
      necomd 2z 0zd flge jca elnn0z sylibr nn0red lenltd biimpar cfz 1zzd elfzd
      eqeq1d rspcdva coprm con1bid bicomd neqned neneqd pm2.21dd pm2.61dan ccom
      imaco resima c1st cdiv c2nd cress xp1st nnne0d dvdsval2 xp2nd zmulcld cop
      ex cmpo op1std op2ndd oveq12d mpompt eqtr4i reseq1d ssidd resmptd fvmpt2d
      fmptco mpteq2dva fvmptd cbs wss cplusg c0g wrex cprimroots cabl ccrg ccmn
      ssrab3 w3a fldcrngd crngmgp primrootsunit simpld simprd ablcmn isprimroot
      eleqtrd simp1d ressbas2 eleqtrrd aks6d1c2p1 ffvelcdmda ressmulgnnd 3eqtrd
      eqfnfvd imaeq1d eqtrid breqtrd aks6d1c6lem3 ) ABCDEFGHIJLMNOPQRUAUBUCQVRV
      RUUAZQVSZUAVTZUGUEUUBVTZWAVTZWBZWCZUEUFUGUHUIUJULUMUNUOUPUQURUSUTAEGWDWEZ
      VUQAVUQWFAVUQWGZWHZGUHWIWBZWJWKZVUQVUSGEWLWEZVVAAVVBVURAGEAGAGUUCWNZGWMWN
      UPGUUDWOZWPAEAEIUUHVTZUUEVTZWQUHWRWBZXIWBZUUFVTZVRVCAVVIWSWNZWTVVIWLWEZWH
      VVIVRWNAVVJVVKAVVHAVVFVVGAVVEAVVEAIUQUUGZWPZAVVEAVVEVVLXAUUIZUUJZAWQUHWQX
      BWNAUUKXCZWTWQWDWEAUULXCZAUHURWPZAUHURUUMZAWJWQAWJWQAUUNZWJWQWDWEAUUOXCUU
      PUVJZUUQZUURZUUSZAWTVVHWLWEZVVKAVVFVVGVVOVWBAVVEVVMVVNUUTAWTWQWJWRWBZVVGW
      LAVWFWTAWQUVAWNWQWTXDWQWJXDVWFWTWKAWQVVPUVBAWQVVQUVCVWAWQUVDXEXFAWQWJUHWQ
      WSWNAUVKXCAWQVVPUVEVVTWTWJWDWEAUVFXCVVRVVSAUHURXGUVGUVHUVIAVVHXBWNWTWSWNV
      WEVVKXHVWCAUVLVVHWTUVMXJXKUVNVVIUVOUVPXLZUVQUVRUVSAVVBVVAXMVURAVVBVVAAVVB
      WHZUKVSZUHWIWBZWJWKZVVAUKWJEUVTWBZGVWIGWKVWJVUTWJVWIGUHWIXNUWCAVWKUKVWLXO
      VVBVAXPVWHGWJEVWHUWAAEWSWNVVBAEVVIWSVCVWDXLXPAGWSWNZVVBAGVVDXQZXPAWJGWLWE
      VVBAGVVDXGXPAVVBWFUWBUWDUXEXPXRVUSVUTWJAVUTWJXDVURAVUTWJAGUHXSWEZVVAWGZUS
      AVWOVWPAVWPVWOAVWOVVAAVVCUHWSWNZVWOWGVVAXHUPAUHURXQZGUHUWEXJUWFUWGYBXRUWH
      XPUWIUWJUWKVBVWGVDVEVFVGVHVIVJVKVUPXTZAUFUAVUJYAZYAYCVTUDVWTYAZYCVTVUPVUJ
      YAZYCVTWLVMAVXAVXBYCAVXAUDUAUWLZVUJYAZVXBVXDVXAUDUAVUJUWMYDAVXDVXCVUJYEZV
      UJYAZVXBVXDVXFWKAVXFVXDVXCVUJUWNYDXCAVXEVUPVUJAVXEVOVUJGVOVSZUWOVTZYFWBZU
      HGUWPWBZVXGUWQVTZYFWBZXIWBZUGVUMKUWRWBZWAVTZWBZWCZVUJYEZVUPAVXCVXQVUJAVOQ
      VUJWSVXMVUKUGVXOWBZVXPUAUDAVXGVUJWNZWHZVXIVXLVYAGVXHAVWMVXTVWNXPVXTVXHVRW
      NAVXGVRVRUWSYGYHVYAVXJVXKAVXJWSWNZVXTAVWOVYBUSAVWMGWTXDVWQVWOVYBXHVWNAGVV
      DUWTVWRGUHUXAXEXKXPVXTVXKVRWNAVXGVRVRUXBYGYHUXCZUAVOVUJVXMWCZWKAUARULVRVR
      GRVSZYFWBZVXJULVSZYFWBZXIWBZUXFVYDVDRULVOVRVRVXMVYIVXGVYEVYGUXDWKZVXIVYFV
      XLVYHXIVYJVXHVYEGYFVYEVYGVXGRYIZULYIZUXGYJVYJVXKVYGVXJYFVYEVYGVXGVYKVYLUX
      HYJUXIUXJUXKXCZUDQWSVXSWCWKAVLXCVUKVXMUGVXOXNUXPUXLAVXRVXQVUPAVOVUJVUJVXP
      AVUJUXMUXNAVXQVOVUJVXGUAVTZUGVXOWBZWCZVUPAVYPVXQAVOVUJVYOVXPVYAVYNVXMUGVX
      OAVOVUJVXMUAWSVYMVYCUXOYKUXQXFAVPVUJVYPVUPAVUJYLVYPYMVYPVUJYNAVOVUJVYOYLV
      YPVYAVYNUGVXOYOVYPXTYPVUJYLVYPYQWOAVUJYLVUPYMVUPVUJYNAQVUJVUOYLVUPAVUKVUJ
      WNWHVULUGVUNYOVWSYPVUJYLVUPYQWOAVPVSZVUJWNZWHZVYQVYPVTVYQUAVTZUGVXOWBZVYT
      UGVUNWBZVYQVUPVTZVYSVOVYQVYOWUAVUJVYPYLVYSVYPYRVYSVXGVYQWKZWHZVYNVYTUGVXO
      WUEVXGVYQUAVYSWUDWFYSYKAVYRWFZVYSVYTUGVXOYOUXRVYSKVUMVXNVYTUGVXNXTZAKVUMU
      XSVTZUXTZVYRWUIATVSSVSVUMUYAVTWBVUMUYBVTWKTWUHUYCSWUHKVNUYHXCZXPAUGKWNVYR
      AUGVXNUXSVTZKAUGWUKWNZIUGVXOWBVXNUYBVTZWKZVQVSZUGVXOWBWUMWKIWUOXSWEXMVQVR
      XOZAUGVXNIUYDWBZWNZWULWUNWUPUYIZAUGVUMIUYDWBZWUQVHAWUTWUQWKZVXNUYEWNZAVUM
      KTISAUEUYFWNVUMUYGWNAUEUOUYJUEVUMVUMXTUYKWOUQVNUYLZUYMUYQAWURWUSAVXNVXOIU
      GVQAWVBVXNUYGWNAWVAWVBWVCUYNVXNUYOWOAIUQXAVXOXTUYPYBXRUYRAWUIKWUKWKWUJKWU
      HVXNVUMWUGWUHXTUYSWOUYTXPAVUJWMVYQUAAGRUAUHULURUPUSVDVUAVUBVUCVYSWUCWUBVY
      SQVYQVUOWUBVUJVUPYLVYSVUPYRVYSVUKVYQWKZWHZVULVYTUGVUNWVEVUKVYQUAVYSWVDWFY
      SYKWUFVYSVYTUGVUNYOUXRXFVUDVUEYTYTYTVUFYTVUGYSVUHVUI $.
  $}

  ${
    aks6d1c6isolem1.1 $e |- ( ph -> R e. CMnd ) $.
    aks6d1c6isolem1.2 $e |- ( ph -> K e. NN ) $.
    aks6d1c6isolem1.3 $e |- U = { a e. ( Base ` R ) |
     E. i e. ( Base ` R ) ( i ( +g ` R ) a ) = ( 0g ` R ) } $.
    aks6d1c6isolem1.4 $e |- F = ( x e. ZZ |->
     ( x ( .g ` ( R |`s U ) ) M ) ) $.
    aks6d1c6isolem1.5 $e |- ( ph -> M e. ( R PrimRoots K ) ) $.
    ${
      $d F c $.  $d F d f g y $.  $d F e f g z $.  $d F f g h $.  $d K l $.
      $d M h $.  $d M l $.  $d M x $.  $d R a i $.  $d R c $.  $d R f g h $.
      $d R l $.  $d R f g x $.  $d R f g y z $.  $d U c $.  $d U f g h $.
      $d U l $.  $d U f g x $.  $d U f g y z $.  $d c ph $.  $d f g h ph $.
      $d l ph $.  $d ph x $.  $d ph y z $.
      $( Lemma to construct the map out of the quotient for AKS. (Contributed
         by metakunt, 14-May-2025.) $)
      aks6d1c6isolem1 $p |- ( ph -> ( ( R |`s U ) |`s ran F ) e. Grp ) $=
        ( co cfv cz wcel wa wceq vy vz vl vc vd ve vg vf crn cress cplusg eqidd
        vh c0g cbs wf wss cv cmg eqid cgrp cprimroots cabl primrootsunit simprd
        ablgrpd adantr simpr cdvds wbr wi cn0 w3a simpld eleqtrd ablcmnd nnnn0d
        wral isprimroot biimpd mpd simp1d mulgcld frn syl wrex cc0 0zd fveqeq2d
        fmptd cvv cmpt a1i oveq1d mulg0 eqtrd fvexd fvmptd rspcedvd wfn wb ffnd
        fvelrnb mpbird imp 3adant3 simpl1 simpl3 jca simpll1 simplr 3jca eqcomd
        oveq2d simpllr simp3 ovexd simp2 oveq12d caddc 3ad2ant1 mulgdir syl2anc
        zaddcld eqeltrrd eqeltrd simpl2 fveqeq2 cbvrexw biimpi r19.29a ex mpdan
        nfv cminusg fveq2d simplll cneg znegcld mulgneg syl3anc issubgrpd
        bilani ) AUAUBFUIZCDUJOZUKPZUUEUUDUJOZUUEUUEUNPZAUUGULAUUHULAUUFULAQUUE
        UOPZFUPUUDUUIUQABQBURZHUUEUSPZOZUUIFAUUJQRZSUUIUUKUUEUUJHUUIUTZUUKUTZAU
        UEVARZUUMAUUEACGVBOZUUEGVBOZTZUUEVCRZACDEGIJKLVDZVEZVFZVGAUUMVHAHUUIRZU
        UMAUVDGHUUKOUUHTZUCURZHUUKOUUHTGUVFVIVJVKUCVLVRZAHUURRZUVDUVEUVGVMZAHUU
        QUURNAUUSUUTUVAVNVOAUVHUVIAUUEUUKGHUCAUUEUVBVPAGKVQUUOVSVTWAWBZVGWCMWJZ
        QUUIFWDWEAUUHUUDRZUDURZFPUUHTZUDQWFZAUVNWGFPUUHTUDWGQAWHZAUVMWGTZSUVMWG
        UUHFAUVQVHWIABWGUULUUHQFWKFBQUULWLTZAMWMAUUJWGTZSZUULWGHUUKOZUUHUVTUUJW
        GHUUKAUVSVHWNAUWAUUHTZUVSAUVDUWBUVJUUIUUKUUEHUUHUUNUUHUTUUOWOWEVGWPUVPA
        UUEUNWQWRWSAFQWTZUVLUVOXAAQUUIFUVKXBZUDQUUHFXCWEXDAUAURZUUDRZUBURZUUDRZ
        VMZUEURZFPUWETZUEQWFZUWEUWGUUFOZUUDRZAUWFUWLUWHAUWFUWLAUWFUWLAUWCUWFUWL
        XAUWDUEQUWEFXCWEVTXEZXFUWIUWLSZUFURZFPUWGTZUFQWFZUWNUWPAUWHSUWSUWPAUWHA
        UWFUWHUWLXGAUWFUWHUWLXHXIAUWHUWSAUWHUWSAUWCUWHUWSXAUWDUFQUWGFXCWEVTXEWE
        UWPUWSUWNUWPUWSSZAUWLUWSVMZUWNUWTAUWLUWSAUWFUWHUWLUWSXJUWIUWLUWSXKUWPUW
        SVHXLUXAUGURZFPZUWGTZUWNUGQUXAUXBQRZSZUXDSZUWMUWEUXCUUFOZUUDUXGUWGUXCUW
        EUUFUXGUXCUWGUXFUXDVHXMXNUXFUXHUUDRZUXDUXFUHURZFPZUWETZUXIUHQUXFUXJQRZS
        ZUXLSZUXHUXKUXCUUFOZUUDUXOUWEUXKUXCUUFUXOUXKUWEUXNUXLVHXMWNUXOAUXEUXMVM
        ZUXPUUDRUXOAUXEUXMUXNAUXLAUWLUWSUXEUXMXJVGUXAUXEUXMUXLXOUXFUXMUXLXKXLUX
        QUXPUXJHUUKOZUXBHUUKOZUUFOZUUDUXQUXKUXRUXCUXSUUFUXQBUXJUULUXRQFWKUVRUXQ
        MWMZUXQUUJUXJTZSUUJUXJHUUKUXQUYBVHWNAUXEUXMXPZUXQUXJHUUKXQWRUXQBUXBUULU
        XSQFWKUYAUXQUUJUXBTZSUUJUXBHUUKUXQUYDVHWNAUXEUXMXRZUXQUXBHUUKXQWRXSUXQU
        XJUXBXTOZHUUKOZUXTUUDUXQUUPUXMUXEUVDVMUYGUXTTAUXEUUPUXMUVCYAUXQUXMUXEUV
        DUYCUYEAUXEUVDUXMUVJYAXLUUIUUFUUKUUEUXJUXBHUUNUUOUUFUTYBYCUXQUYGUUDRZUM
        URZFPZUYGTZUMQWFZUXQUYKUYFFPUYGTUMUYFQUXQUXJUXBUYCUYEYDZUXQUYIUYFTZSUYI
        UYFUYGFUXQUYNVHWIUXQBUYFUULUYGQFWKUYAUXQUUJUYFTZSUUJUYFHUUKUXQUYOVHWNUY
        MUXQUYFHUUKXQWRWSAUXEUYHUYLXAZUXMAUWCUYPUWDUMQUYGFXCWEYAXDYEYFWEYFUXFUW
        LUXLUHQWFZAUWLUWSUXEYGUWLUYQUWKUXLUEUHQUWKUHYNUXLUEYNUWJUXJUWEFYHYIZYJW
        EYKVGYFUXAUWSUXDUGQWFZAUWLUWSXPUWSUYSUWRUXDUFUGQUWRUGYNUXDUFYNUWQUXBUWG
        FYHYIYJWEYKWEYLWAYMAUWFSZUWLUWEUUEYOPZPZUUDRZUWOUYTUWLVUCAUWLVUCVKUWFAU
        WLVUCAUWLSZUXLVUCUHQVUDUXMSZUXLSZVUBUXKVUAPZUUDVUFUWEUXKVUAVUFUXKUWEVUE
        UXLVHXMYPVUFAUXMSZVUGUUDRZVUFAUXMAUWLUXMUXLYQVUDUXMUXLXKXIVUHVUIVKVUFVU
        HVUIUYJVUGTZUMQWFZVUHVUJUXJYRZFPZVUGTUMVULQVUHUXJAUXMVHZYSZVUHUYIVULTZS
        UYIVULVUGFVUHVUPVHWIVUHVUMVULHUUKOZVUGVUHBVULUULVUQQFWKUVRVUHMWMZVUHUUJ
        VULTZSUUJVULHUUKVUHVUSVHWNVUOVUHVULHUUKXQWRVUHVUQUXRVUAPZVUGVUHUUPUXMUV
        DVUQVUTTAUUPUXMUVCVGVUNAUVDUXMUVJVGUUIUUKUUEVUAUXJHUUNUUOVUAUTYTUUAVUHU
        XRUXKVUAVUHUXKUXRVUHBUXJUULUXRQFWKVURVUHUYBSUUJUXJHUUKVUHUYBVHWNVUNVUHU
        XJHUUKXQWRXMYPWPWPWSAVUIVUKXAZUXMAUWCVVAUWDUMQVUGFXCWEVGXDWMWAYFUWLUYQA
        UYRUUCYKYLVGXEYMUVCUUB $.
    $}

    ${
      $d F v w z $.  $d F y z $.  $d K l $.  $d M l $.  $d M x $.  $d R a i $.
      $d R l $.  $d R w z $.  $d R x y z $.  $d U l $.  $d U w z $.
      $d U x y z $.  $d l ph $.  $d ph w z $.  $d ph x y z $.
      $( Lemma to construct the group homomorphism for the AKS Theorem.
         (Contributed by metakunt, 14-May-2025.) $)
      aks6d1c6isolem2 $p |- ( ph -> F e. ( ZZring GrpHom
       ( ( R |`s U ) |`s ran F ) ) ) $=
        ( co cfv cz wcel wceq wa vy vz vw vv caddc cress cplusg czring zringbas
        vl crn cbs eqid zringplusg cvv cv cmg cmpt mptex eqeltri rnex ressplusg
        zex ax-mp crg cgrp zringring a1i ringgrp aks6d1c6isolem1 wf ovexd fmptd
        syl wfn ffn dffn3 sylib wss wrex wb fvelrnb biimpd imp wi simpr simplll
        eqcomd simplr jca oveq1d fvmptd cprimroots primrootsunit simprd ablgrpd
        cabl adantr c0g cdvds wbr cn0 wral w3a simpld eleqtrd nnnn0d isprimroot
        ablcmnd mpd simp1d mulgcld eqeltrd fveqeq2 cbvrexw bilani r19.29a mpdan
        nfv ex ssrdv ressbas2 feq3d mpbid simprl simprr zaddcld mulgdir syl2anc
        3jca oveq12d eqtrd isghmd ) AUAUBUECDUFOZUGPZUHYNFUKZUFOZFQYQULPZUIYRUM
        UNYPUORYOYQUGPSFFBQBUPZHYNUQPZOZURZUOMBQUUAVCUSUTVAYPYOYNYQUOYQUMZYOUMZ
        VBVDAUHVERZUHVFRUUEAVGVHUHVIVNABCDEFGHIJKLMNVJAQYPFVKZQYRFVKAFQVOZUUFAQ
        UOFVKUUGABQUUAUOFAYSQRTYSHYTVLMVMQUOFVPVNZQFVQVRAYPYRFQAYPYNULPZVSYPYRS
        AUCYPUUIAUCUPZYPRZUUJUUIRZAUUKTZUDUPZFPUUJSZUDQVTZUULAUUKUUPAUUKUUPAUUG
        UUKUUPWAUUHUDQUUJFWBVNWCWDUUMUUPUULAUUPUULWEUUKAUUPUULAUUPTZUBUPZFPZUUJ
        SZUULUBQUUQUURQRZTZUUTTZUUJUUSUUIUVCUUSUUJUVBUUTWFWHUVCAUVATZUUSUUIRUVC
        AUVAAUUPUVAUUTWGUUQUVAUUTWIWJUVDUUSUURHYTOZUUIUVDBUURUUAUVEQFUOFUUBSZUV
        DMVHUVDYSUURSZTYSUURHYTUVDUVGWFWKAUVAWFZUVDUURHYTVLWLUVDUUIYTYNUURHUUIU
        MZYTUMZAYNVFRZUVAAYNACGWMOZYNGWMOZSZYNWQRZACDEGIJKLWNZWOZWPZWRUVHAHUUIR
        ZUVAAUVSGHYTOYNWSPZSZUJUPZHYTOUVTSGUWBWTXAWEUJXBXCZAHUVMRZUVSUWAUWCXDZA
        HUVLUVMNAUVNUVOUVPXEXFAUWDUWEAYNYTGHUJAYNUVQXIAGKXGUVJXHWCXJXKZWRXLXMVN
        XMUUPUUTUBQVTAUUOUUTUDUBQUUOUBXSUUTUDXSUUNUURUUJFXNXOXPXQXTWRWDXRXTYAYP
        UUIYQYNUUCUVIYBVNYCYDAUAUPZQRZUVATZTZUWGUURUEOZFPUWKHYTOZUWGFPZUUSYOOZU
        WJBUWKUUAUWLQFUOUVFUWJMVHZUWJYSUWKSZTYSUWKHYTUWJUWPWFWKUWJUWGUURAUWHUVA
        YEZAUWHUVAYFZYGUWJUWKHYTVLWLUWJUWLUWGHYTOZUVEYOOZUWNUWJUVKUWHUVAUVSXDUW
        LUWTSAUVKUWIUVRWRUWJUWHUVAUVSUWQUWRAUVSUWIUWFWRYJUUIYOYTYNUWGUURHUVIUVJ
        UUDYHYIUWJUWNUWTUWJUWMUWSUUSUVEYOUWJBUWGUUAUWSQFUOUWOUWJYSUWGSZTYSUWGHY
        TUWJUXAWFWKUWQUWJUWGHYTVLWLUWJBUURUUAUVEQFUOUWOUWJUVGTYSUURHYTUWJUVGWFW
        KUWRUWJUURHYTVLWLYKWHYLYLYM $.
    $}

    ${
      $d F z $.  $d K z $.  $d M x $.  $d R a i $.  $d R x z $.  $d S z $.
      $d U x z $.  $d ph x z $.
      aks6d1c6isolem3.1 $e |- S = ( RSpan ` ZZring ) $.
      $( The preimage of a map sending a primitive root to its powers of zero
         is equal to the set of integers that divide ` R ` .  (Contributed by
         metakunt, 15-May-2025.) $)
      aks6d1c6isolem3 $p |- ( ph -> ( S ` { K } ) =
       ( `' F " { ( 0g ` ( R |`s U ) ) } ) ) $=
        ( vz wcel cz wceq csn cfv cv cdvds wbr cab ccnv cress co c0g czring crg
        cima zringring a1i nnzd zringbas dvdsrzring syl2anc crab wfn cvv cmg wa
        rspsn ovexd fmptd ffnd fniniseg2 cmpt simpr oveq1d fvmptd eqeq1d adantr
        syl cn cprimroots primrootspoweq0 bitrd rabbidva df-rab dvdszrcl simprd
        ccmn wb ancri impbii abbidv eqtrd eqtr2d ) AHUADUBZHQUCZUDUEZQUFZGUGCEU
        HUIZUJUBZUAUMZAUKULRZHSRZWLWOTWSAUNUOAHLUPQSUDUKHDUQPURVEUSAWRWMGUBZWQT
        ZQSUTZWOAGSVAWRXCTASVBGABSBUCZIWPVCUBZUIZVBGAXDSRVDXDIXEVFNVGVHQSWQGVIV
        PAXCWNQSUTZWOAXBWNQSAWMSRZVDZXBWMIXEUIZWQTWNXIXAXJWQXIBWMXFXJSGVBGBSXFV
        JTXINUOXIXDWMTZVDXDWMIXEXIXKVKVLAXHVKZXIWMIXEVFVMVNXICEFHIWMJACWERXHKVO
        AHVQRXHLVOAICHVRUIRXHOVOMXLVSVTWAAXGXHWNVDZQUFZWOXGXNTAWNQSWBUOAXMWNQXM
        WNWFAXMWNXHWNVKWNXHWNWTXHHWMWCWDWGWHUOWIWJWJWKWJ $.
    $}
  $}

  ${
    aks6d1c6lem5.1 $e |- .~ = { <. e , f >. | ( e e. NN /\ f e.
     ( Base ` ( Poly1 ` K ) ) /\ A. y e. ( ( mulGrp ` K ) PrimRoots R )
     ( e ( .g ` ( mulGrp ` K ) ) ( ( ( eval1 ` K ) ` f ) ` y ) ) =
     ( ( ( eval1 ` K ) ` f ) ` ( e ( .g ` ( mulGrp ` K ) ) y ) ) ) } $.
    aks6d1c6lem5.2 $e |- P = ( chr ` K ) $.
    aks6d1c6lem5.3 $e |- ( ph -> K e. Field ) $.
    aks6d1c6lem5.4 $e |- ( ph -> P e. Prime ) $.
    aks6d1c6lem5.5 $e |- ( ph -> R e. NN ) $.
    aks6d1c6lem5.6 $e |- ( ph -> N e. NN ) $.
    aks6d1c6lem5.7 $e |- ( ph -> P || N ) $.
    aks6d1c6lem5.8 $e |- ( ph -> ( N gcd R ) = 1 ) $.
    aks6d1c6lem5.9 $e |- ( ph -> A. b e. ( 1 ... A ) ( b gcd N ) = 1 ) $.
    aks6d1c6lem5.10 $e |- G = ( g e. ( NN0 ^m ( 0 ... A ) ) |->
    ( ( mulGrp ` ( Poly1 ` K ) ) gsum ( i e. ( 0 ... A ) |-> ( ( g ` i )
    ( .g ` ( mulGrp ` ( Poly1 ` K ) ) ) ( ( var1 ` K ) ( +g ` ( Poly1 ` K ) )
    ( ( algSc ` ( Poly1 ` K ) ) ` ( ( ZRHom ` K ) ` i ) ) ) ) ) ) ) $.
    aks6d1c6lem5.11 $e |- A = ( |_ ` ( ( sqrt ` ( phi ` R ) ) x.
     ( 2 logb N ) ) ) $.
    aksaks6dlem5.12 $e |- E = ( k e. NN0 , l e. NN0 |->
    ( ( P ^ k ) x. ( ( N / P ) ^ l ) ) ) $.
    aks6d1c6lem5.13 $e |- L = ( ZRHom ` ( Z/nZ ` R ) ) $.
    aks6d1c6lem5.14 $e |- ( ph -> A. a e. ( 1 ... A ) N .~ ( ( var1 ` K )
     ( +g ` ( Poly1 ` K ) )
     ( ( algSc ` ( Poly1 ` K ) ) ` ( ( ZRHom ` K ) ` a ) ) ) ) $.
    aks6d1c6lem5.15 $e |- ( ph -> ( x e. ( Base ` K ) |->
     ( P ( .g ` ( mulGrp ` K ) ) x ) ) e. ( K RingIso K ) ) $.
    aks6d1c6lem5.16 $e |- ( ph -> M e. ( ( mulGrp ` K ) PrimRoots R ) ) $.
    aks6d1c6lem5.17 $e |- H = ( h e. ( NN0 ^m ( 0 ... A ) ) |->
     ( ( ( eval1 ` K ) ` ( G ` h ) ) ` M ) ) $.
    aks6d1c6lem5.18 $e |- D = ( # ` ( L " ( E " ( NN0 X. NN0 ) ) ) ) $.
    aks6d1c6lem5.19 $e |- S = { s e. ( NN0 ^m ( 0 ... A ) ) |
     sum_ t e. ( 0 ... A ) ( s ` t ) <_ ( D - 1 ) } $.
    ${
      $d .~ a $.  $d A a $.  $d A b $.  $d A g i x $.  $d A h j $.  $d A s t $.
      $d D s $.  $d E e f y $.  $d E j y $.  $d E x y $.  $d G e f y $.
      $d G g i y $.  $d G h $.  $d G i t y $.  $d H a $.  $d H g i x y $.
      $d H h j $.  $d H s t $.  $d J b c $.  $d J c d $.  $d J u v w $.
      $d J u v y z $.  $d K a $.  $d K b c $.  $d K c d $.  $d K e f y $.
      $d K g i x y $.  $d K h j $.  $d K l x y $.  $d K m n $.  $d K i t x y $.
      $d K w $.  $d M h j $.  $d M l y $.  $d N a $.  $d N b $.  $d N e f $.
      $d N j $.  $d N k l s $.  $d N k l x $.  $d P b $.  $d P e f $.
      $d P j $.  $d P k l s $.  $d P k l x $.  $d R d $.  $d R e f y $.
      $d R j u y z $.  $d R l x y $.  $d R u v w $.  $d S a $.  $d S g i x y $.
      $d S h j $.  $d S s t $.  $d U b c $.  $d U c d $.  $d U j $.  $d U l $.
      $d U w $.  $d X b c $.  $d a ph $.  $d b c ph $.  $d d ph $.
      $d g i ph x y $.  $d h j ph $.  $d k l ph s $.  $d k l ph x y $.
      $d ph s t $.  $d ph u v w $.  $d ph u v y z $.
      aks6d1c6lem5.20 $e |- J = ( j e. ZZ |->
         ( j ( .g ` ( ( mulGrp ` K ) |`s U ) ) M ) ) $.
      aks6d1c6lem5.22 $e |- U = { m e. ( Base ` ( mulGrp ` K ) ) |
      E. n e. ( Base ` ( mulGrp ` K ) ) ( n ( +g `
      ( mulGrp ` K ) ) m ) = ( 0g ` ( mulGrp ` K ) ) } $.
      aks6d1c6lem5.23 $e |- X = ( b e. ( Base ` ( ZZring /s ( ZZring
       ~QG ( `' J " { ( 0g ` ( ( ( mulGrp ` K ) |`s U ) |`s ran J )
        ) } ) ) ) ) |-> U. ( J " b ) ) $.
      $( Eliminate the size hypothesis.  Claim 6.  (Contributed by metakunt,
         15-May-2025.) $)
      aks6d1c6lem5 $p |- ( ph -> ( ( D + A ) _C ( D - 1 ) ) <_
         ( # ` ( H " ( NN0 ^m ( 0 ... A ) ) ) ) ) $=
        ( vd vc vw vv vu vz cn0 cima chash cfv ccnv cle ccom cz cv czring cress
        crn c0g csn cqg cec cmpt cqus eqid ccrg wcel syl zringbas nfcv cbs wceq
        co wss cprimroots wrex cc0 simpr fveqeq2d cvv a1i oveq1d wbr w3a biimpd
        wa adantr eqtrd fvmptd rspcedvd wfn mulgcld mpbird eqtr2d oveq2d eqcomd
        wb ffnd wf cfn simplr ad3antrrr cn syl2anc fvelimab cxp aks6d1c6isolem2
        cmgp ccmn fldcrngd crngmgp cbvmpt ghmquskerco crsp aks6d1c6isolem3 cmnd
        eceq1 cabl primrootsunit simprd ablgrpd grpmndd 0zd cmg cdvds wi simpld
        wral eleqtrd ablcmnd nnnn0d isprimroot simp1d mulg0 fvexd fmptd fvelrnb
        mpd cgrp ress0g syl3anc sneqd imaeq2d eceq2d mpteq2dv czn znzrh2 coeq2d
        frnd coass eqcomi eqtrdi cid cres wf1o ressbas2 ghmqusker gimf1o coeq1d
        cgim f1ococnv1 crg zncrng crngring zrhrhm rhmf 4syl znbas2 feq3d fveq2d
        crh mpbid fcoi2 imaeq1d imaco cdom wfun cmin cfz simplll jca cmul caddc
        c1 fzssz sselid ovexd cplusg ad2antrr nnzd zmulcld sseli adantl mulgdir
        3jca mulgass simp2d mulgz grplidd remexz r19.29vva eqeq2d rexbidv ssidd
        r19.29a ex ssrdv simprr reximssdv eqssd fnfund fzfid eqeltrd aks6d1c2p1
        imp imafi nnssz fss fnima sseq1d imass2 dff1o2 biimpi imadomfi hashdomi
        ssfid eqbrtrd aks6d1c6lem4 ) ABCDEFGHIJKLMNOPQRSTUAUBUCUDUEUFUGUHUJUKUL
        UMUNUOUPUQURUSUTVAVBVCVDVEVFVGVHVIVJVKVLVMAUFUAWBWBUUAZWCZWCZWDWEUIWFZU
        DVVEWCZWCZWDWEZVVHWDWEZWGAVVFVVIWDAVVFVVGUDWHZVVEWCZVVIAUFVVLVVEAVVLVVG
        UIWHZUFWHZUFAVVLVVGUIUFWHZWHZVVOAUDVVPVVGAUDUIVPWIVPWJZWKUDWFZUEUUCWEZK
        WLXHZUDWMZWLXHZWNWEZWOZWCZWPXHZWQZWRZWHVVPAVQWIWKVWGWSXHZUDWKVWCUIVWFVW
        IVWDULVWDWTZAQVVTKTUDIUGSAUEXAXBVVTUUDXBAUEUPUUEUEVVTVVTWTUUFXCZURVNVMV
        IUUBZVWFWTZVWJWTZVOXDVPVQWIVWHVQWJZVWGWQZVQVWHXEVPVWQXEVVRVWPVWGUULUUGU
        UHAVWIUFUIAVWIVPWIVVRWKIWOWKUUIWEZWEZWPXHZWQZWRZUFAVPWIVWHVXAAVWGVWTVVR
        AVWFVWSWKWPAVWSVVSVWAWNWEZWOZWCVWFAQVVTVWRKTUDIUGSVWLURVNVMVIVWRWTZUUJA
        VXDVWEVVSAVXCVWDAVWAUUKXBVXCVWBXBZVWBVWAXFWEZXIZVXCVWDXGAVWAAVWAAVVTIXJ
        XHZVWAIXJXHZXGZVWAUUMXBZAVVTKTISVWLURVNUUNZUUOZUUPZUUQAVXFVRWJZUDWEVXCX
        GZVRWIXKZAVXQXLUDWEVXCXGVRXLWIAUURZAVXPXLXGZYAVXPXLVXCUDAVXTXMXNAQXLQWJ
        ZUGVWAUUSWEZXHZVXCWIUDXOUDQWIVYCWRXGZAVMXPAVYAXLXGZYAZVYCXLUGVYBXHZVXCV
        YFVYAXLUGVYBAVYEXMXQAVYGVXCXGZVYEAUGVXGXBZVYHAVYIIUGVYBXHZVXCXGZUMWJZUG
        VYBXHVXCXGIVYLUUTXRUVAUMWBUVCZAUGVXJXBZVYIVYKVYMXSZAUGVXIVXJVIAVXKVXLVX
        MUVBUVDAVYNVYOAVWAVYBIUGUMAVWAVXNUVEAIURUVFZVYBWTZUVGXTUVMZUVHZVXGVYBVW
        AUGVXCVXGWTZVXCWTZVYQUVIXCYBYCVXSAVWAWNUVJYDYEAUDWIYFZVXFVXRYLAWIVXGUDA
        QWIVYCVXGUDAVYAWIXBZYAVXGVYBVWAVYAUGVYTVYQAVWAUVNXBZWUCVXOYBAWUCXMAVYIW
        UCVYSYBYGVMUVKZYMZVRWIVXCUDUVLXCYHAWIVXGUDWUEUWDZVWBVXGVWAVWCVXCVWCWTZV
        YTWUAUVOUVPUVQUVRYIZYJUVSUVTAUFVXBAIWBXBZUFVXBXGVYPVPVWTVWRUFIIUWAWEZVX
        EVWTWTWUKWTZVFUWBXCYKYCUWCYCUWCVVOVVQVVGUIUFUWEUWFUWGAVVOUWHVWJXFWEZUWI
        ZUFWHZUFAVVNWUNUFAWUMVWCXFWEZUIUWJZVVNWUNXGAUIVWJVWCUWOXHXBWUQAVWJUDWKV
        WCUIVWFVWDULVWKVWMVWNVWOVOAVXHVWBWUPXGWUGVWBVXGVWCVWAWUHVYTUWKXCUWLWUMW
        UPVWJVWCUIWUMWTWUPWTUWMXCZWUMWUPUIUWPXCUWNAWIWUMUFYNZWUOUFXGAWIWKVWTWSX
        HZXFWEZUFYNZWUSAWVBWIWUKXFWEZUFYNZAWUKXAXBZWUKUWQXBUFWKWUKUXFXHXBWVDAWU
        JWVEVYPIWUKWULUWRXCWUKUWSWUKUFVFUWTWIWVCWKWUKUFXDWVCWTUXAUXBAWVAWVCUFWI
        AWUJWVAWVCXGVYPVWRWUTIWUKVXEWUTWTWULUXCXCUXDYHAWVAWUMUFWIAWUTVWJXFAVWTV
        WGWKWSAVWSVWFWKWPAVWFVWSWUIYKYJYJUXEUXDUXGWIWUMUFUXHXCYCYIUXIVVMVVIXGAV
        VGUDVVEUXJXPYCUXEAVVIVVHUXKXRZVVJVVKWGXRAVVHYOXBVVGUXLZWVFAUDWIWCZVVHAW
        VHUDXLIUXSUXMXHZUXNXHZWCZYOAWVHWVKAVRWVHWVKAVXPWVHXBZVXPWVKXBZAWVLYAZWV
        MVSWJZUDWEZVXPXGZVSWVJXKZWVNVTWJZUDWEZVXPXGZWVRVTWIWVNWVSWIXBZYAZWWAYAZ
        WVRWVPWVTXGZVSWVJXKZWWDAWWBYAZWWFWWDAWWBAWVLWWBWWAUXOWVNWWBWWAYPUXPWWGW
        VSCWJZIUXQXHZWAWJZUXRXHZXGZWWFCWAWIWVJWWGWWHWIXBZYAZWWJWVJXBZYAZWWLYAZW
        WEWWJUDWEZWVTXGVSWWJWVJWWNWWOWWLYPZWWQWVOWWJXGZYAWVOWWJWVTUDWWQWWTXMXNW
        WQWWRWWJUGVYBXHZWVTWWQQWWJVYCWXAWIUDXOVYDWWQVMXPZWWQVYAWWJXGZYAVYAWWJUG
        VYBWWQWXCXMXQWWQWVJWIWWJXLWVIUXTZWWSUYAWWQWWJUGVYBUYBYDWWQWVTWVSUGVYBXH
        ZWXAWWQQWVSVYCWXEWIUDXOWXBWWQVYAWVSXGZYAVYAWVSUGVYBWWQWXFXMXQWWGWWBWWMW
        WOWWLAWWBXMZYQWWQWVSUGVYBUYBYDWWQWXEWWKUGVYBXHZWXAWWQWVSWWKUGVYBWWPWWLX
        MXQWWPWXHWXAXGWWLWWPWXHWWIUGVYBXHZWXAVWAUYCWEZXHZWXAWWPWUDWWIWIXBZWWJWI
        XBZVYIXSWXHWXKXGAWUDWWBWWMWWOVXOYQZWWPWXLWXMVYIWWPWWHIWWGWWMWWOYPZWWPIW
        WGIYRXBZWWMWWOAWXPWWBURYBZUYDUYEZUYFWWOWXMWWNWVJWIWWJWXDUYGUYHZAVYIWWBW
        WMWWOVYSYQZUYJVXGWXJVYBVWAWWIWWJUGVYTVYQWXJWTZUYIYSWWPWXKVXCWXAWXJXHWXA
        WWPWXIVXCWXAWXJWWPWXIWWHVYJVYBXHZVXCWWPWUDWWMIWIXBZVYIXSWXIWYBXGWXNWWPW
        WMWYCVYIWXOWXRWXTUYJVXGVYBVWAWWHIUGVYTVYQUYKYSWWPWYBWWHVXCVYBXHZVXCWWPV
        YJVXCWWHVYBWWNVYKWWOWWGVYKWWMAVYKWWBAVYIVYKVYMVYRUYLYBYBYBYJWWPWUDWWMWY
        DVXCXGWXNWXOVXGVYBVWAWWHVXCVYTVYQWUAUYMYSYCYCXQWWPVXGWXJVWAWXAVXCVYTWYA
        WUAWXNWWPVXGVYBVWAWWJUGVYTVYQWXNWXSWXTYGUYNYCYCYBYCYIYCYEWWGCWAIWVSWXGW
        XQUYOUYPXCWWDWVQWWEVSWVJWWDVXPWVTWVPWWDWVTVXPWWCWWAXMYKUYQUYRYHAWVLWWAV
        TWIXKZAWVLWYEAWUBWIWIXIZWVLWYEYLWUFAWIUYSVTWIWIVXPUDYTYSXTVUJUYTAWVMWVR
        YLZWVLAWUBWVJWIXIZWYGWUFWYHAWXDXPVSWIWVJVXPUDYTYSZYBYHVUAVUBAVRWVKWVHAW
        VMWVLAWVMYAZWVLWVQVSWIXKZWYJWVQWVQVSWIWVJAWVMWVRAWVMWVRWYIXTVUJWVOWVJXB
        ZWVQYAWVOWIXBZWYJWYLWYMWVQWVJWIWVOWXDUYGYBUYHWYJWYLWVQVUCVUDWYJWUBWYFWV
        LWYKYLAWUBWVMWUFYBWYJWIUYSVSWIWIVXPUDYTYSYHVUAVUBVUEAUDUXLWVJYOXBWVKYOX
        BAWIUDWUFVUFAXLWVIVUGUDWVJVUKYSVUHAVVEWIXIZVVHWVHXIAWYNUAWMZWIXIAVVDWIU
        AAVVDYRUAYNZYRWIXIZYAVVDWIUAYNAWYPWYQAGRUAUHUMUSUQUTVEVUIZWYQAVULXPUXPV
        VDYRWIUAVUMXCUWDAVVEWYOWIAUAVVDYFVVEWYOXGAVVDYRUAWYRYMVVDUAVUNXCVUOYHVV
        EWIUDVUPXCVVAAWUQWVGWURWUQUIWUMYFZWVGUIWMWUPXGZWUQWYSWVGWYTXSWUMWUPUIVU
        QVURUYLXCVVHVVGVUSYSVVIVVHVUTXCVVBVNVVC $.
    $}
  $}

  ${
    $d A k $.  $d B k $.  $d C k $.  $d k ph $.
    bcled.1 $e |- ( ph -> A e. NN0 ) $.
    bcled.2 $e |- ( ph -> B e. NN0 ) $.
    bcled.3 $e |- ( ph -> C e. ZZ ) $.
    bcled.4 $e |- ( ph -> A <_ B ) $.
    $( Inequality for binomial coefficients.  (Contributed by metakunt,
       12-May-2025.) $)
    bcled $p |- ( ph -> ( A _C C ) <_ ( B _C C ) ) $=
      ( vk cc0 co wcel cle wbr wa cmin wceq adantl adantr eqcomd cfz cbc bcval2
      cfa cfv cmul cdiv cn0 faccld nncnd nn0zd zsubcld zred nn0red 0red elfzle2
      cz recnd subid1d breqtrd lesubd jca elnn0z sylibr elfznn0 nnne0d divdiv1d
      nnred redivcld letrd nnrpd cfallfac c1 cv cprod fzfid cr elfzelz resubcld
      nfv 1red 0le1 a1i le2subd ad2antrr lesub1dd fprodle cc fallfacval syl2anc
      nn0cnd 3brtr3d fallfacval4 0zd nn0ge0d elfzd syl lediv1dd eqbrtrd elfzle1
      wn simpr bcval3 syl3anc cn bccl2 nnnn0d 0le0 pm2.61dan ) ADJBUAKLZBDUBKZC
      DUBKZMNAXJOZXKBUDUEZBDPKZUDUEZDUDUEZUFKUGKZXLMXJXKXRQADBUCRXMXRCUDUEZCDPK
      ZUDUEZXQUFKUGKZXLMXMXRXNXPUGKZXQUGKZYBMXMYDXRXMXNXPXQXMXNXMBABUHLZXJESZUI
      ZUJXMXPXMXOXMXOUQLZJXOMNZOXOUHLXMYHYIXMBDXMBYFUKADUQLZXJGSZULXMDBJXMDYKUM
      ZXMBYFUNZXMUOZXMDBBJPKZMXJDBMNZADJBUPRZXMYOBXMBXMBYMURUSTUTVAVBXOVCVDUIZU
      JXMXQXMDXJDUHLZADBVERZUIZUJZXMXPYRVFZXMXQUUAVFZVGTXMYDXSYAUGKZXQUGKYBMXMY
      CUUEXQXMXNXPXMXNYGVHXMXPYRVHUUCVIXMXSYAXMXSXMCACUHLZXJFSZUIZVHXMYAXMXTXMX
      TUQLZJXTMNZOXTUHLXMUUIUUJXMCDXMCUUGUKZYKULXMDCJYLXMCUUGUNZYNXMDCCJPKZMXMD
      BCYLYMUULYQABCMNZXJHSZVJXMUUMCXMCXMCUULURUSTUTVAVBXTVCVDUIZVHXMYAUUPVFZVI
      XMXQUUAVKXMBDVLKZCDVLKZYCUUEMXMJDVMPKZUAKZBIVNZPKZIVOZUVACUVBPKZIVOZUURUU
      SMXMUVAUVCUVEIXMIVTXMJUUTVPXMUVBUVALZOZBUVBXMBVQLZUVGYMSZUVHUVBUVGUVBUQLX
      MUVBJUUTVRRUMZVSUVHUVBBJUVKUVJUVHUOZUVHUVBUUTYOUVKUVHDVMXMDVQLUVGXMDYTUNZ
      SZUVHWAZVSUVHBJUVJUVLVSUVGUVBUUTMNXMUVBJUUTUPRUVHDJBVMUVNUVLUVJUVOXMYPUVG
      YQSJVMMNUVHWBWCWDVJVAUVHCUVBXMCVQLUVGUULSZUVKVSUVHBCUVBUVJUVPUVKAUUNXJUVG
      HWEWFWGXMUURUVDXMBWHLYSUURUVDQXMBYFWKYTBIDWIWJTXMUUSUVFXMCWHLYSUUSUVFQXMC
      UUGWKYTCIDWIWJTWLXJUURYCQABDWMRXMDJCUAKLZUUSUUEQXMDJCXMWNZUUKYKXMDYTWOXMD
      BCUVMYMUULYQUUOVJWPCDWMWQWLWRXMXSYAXQXMXSUUHUJXMYAUUPUJUUBUUQUUDVGUTWSXMX
      LYBXMUVQXLYBQXMDJCUVRACUQLXJACFUKSZYKXJJDMNADJBWTRXMDBCYLAUVIXJABEUNSXMCU
      VSUMYQUUOVJWPDCUCWQTUTWSAXJXAZOZXKJXLMUWAYEYJUVTXKJQAYEUVTESAYJUVTGSZAUVT
      XBDBXCXDUWAUVQJXLMNUWAUVQOZXLUWCXLUVQXLXELUWADCXFRXGWOUWAUVQXAZOZJJXLMJJM
      NUWEXHWCUWEXLJUWEUUFYJUWDXLJQAUUFUVTUWDFWEUWAYJUWDUWBSUWAUWDXBDCXCXDTUTXI
      WSXI $.
  $}

  ${
    $d A k $.  $d B k $.  $d C k $.  $d D k $.  $d k ph $.
    bcle2d.1 $e |- ( ph -> A e. NN0 ) $.
    bcle2d.2 $e |- ( ph -> B e. NN0 ) $.
    bcle2d.3 $e |- ( ph -> C e. NN0 ) $.
    bcle2d.4 $e |- ( ph -> D e. ZZ ) $.
    bcle2d.5 $e |- ( ph -> A <_ B ) $.
    bcle2d.6 $e |- ( ph -> D <_ C ) $.
    $( Inequality for binomial coefficients.  (Contributed by metakunt,
       12-May-2025.) $)
    bcle2d $p |- ( ph -> ( ( A + C ) _C ( A + D ) ) <_
     ( ( B + C ) _C ( B + D ) ) ) $=
      ( caddc co cc0 wcel cle wbr cmin cdiv adantr vk cfz cbc cfa cfv cmul wceq
      wa bcval2 adantl cn0 nn0addcld faccld nncnd nn0zd zaddcld elfzle1 anim12i
      cz elnn0z sylibr nnnn0d nn0cnd nn0red recnd addsub4d subidd oveq1d subcld
      cr cc zred addlidd eqtrd zsubcld subge0d mpbird jca eqeltrd nnne0d eqcomd
      divdiv1d cfallfac 0zd cneg renegcld df-neg a1i lesubaddd eqbrtrd leadd2dd
      0red negsubd addcomd 3brtr3d fallfacval4 syl subsubd pncand fveq2d oveq2d
      elfzd c1 cv cprod nfv fzfid readdcld elfzelz resubcld elfzle2 lem1d letrd
      1red wb leaddsub syl3anc mpbid leadd1dd fprodle fallfacval syl2anc addcld
      lesub1dd breqtrd nnred redivcld cn lediv1d pncan2d mulcomd addassd eqtr2d
      nnrpd nppcand wn simpr bcval3 ad2antrr pm2.61dan subsub4d pnpcand leadd1d
      bccl2 nn0ge0d 0le0 ) ABELMZNBDLMZUBMZOZUUHUUGUCMZCDLMZCELMZUCMZPQAUUJUHZU
      UKUUHUDUEZUUHUUGRMZUDUEZUUGUDUEZUFMZSMZUUNPUUJUUKUVAUGAUUGUUHUIUJUUOUVAUU
      LUDUEZUULUUMRMZUDUEZUUMUDUEZUFMZSMZUUNPUUOUUPUUSUURUFMZSMZUVBUVEUVDUFMZSM
      ZUVAUVGPUUOUVIUUPUUSSMZUURSMZUVKPUUOUVMUVIUUOUUPUUSUURUUOUUPUUOUUHAUUHUKO
      ZUUJABDFHULZTZUMZUNUUOUUSUUOUUSUUOUUGUUOUUGUSOZNUUGPQZUHUUGUKOAUVRUUJUVSA
      BEABFUOIUPZUUGNUUHUQZURUUGUTVAUMZVBVCUUOUURUUOUURUUOUUQUUOUUQDERMZUKUUOUU
      QBBRMZUWCLMZUWCUUOBDBEUUOBABVJOZUUJABFVDZTZVEZADVKOUUJADHVCZTZUWIUUOEAEVJ
      OZUUJAEIVLZTZVEZVFZUUOUWENUWCLMUWCUUOUWDNUWCLUUOBUWIVGVHUUOUWCUUODEUWKUWO
      VIVMVNZVNUUOUWCUSOZNUWCPQZUHUWCUKOZUUOUWRUWSUUODEADUSOUUJADHUOZTZAEUSOUUJ
      ITVOZUUOUWSEDPQZAUXDUUJKTUUODEUUODUXBVLUWNVPVQZVRUWCUTVAZVSUMZVBVCUUOUUSU
      WBVTZUUOUURUXGVTWBWAUUOUVMUVBUVESMZUVDSMZUVKPUUOUVLUWCUDUEZSMZUXIUXKSMZUV
      MUXJPUUOUVLUXIPQUXLUXMPQUUOUVLUUHUWCWCMZUXIPUUOUXNUVLUUOUXNUUPUUHUWCRMZUD
      UEZSMZUVLUUOUWCUUIOUXNUXQUGUUOUWCNUUHUUOWDZUUOUUHUVPUOUXCUXEUUODEWEZLMZDB
      LMUWCUUHPUUOUXSBDUUOEUWNWFZUWHUUODADUKOZUUJHTZVDZUUOUXSNERMZBPUXSUYEUGUUO
      EWGWHZUUOUYEBPQUVSUUJUVSAUWAUJZUUONEBUUOWLZUWNUWHWIVQWJWKUUODEUWKUWOWMZUU
      ODBUWKUWIWNWOZXBUUHUWCWPWQUUOUXPUUSUUPSUUOUXOUUGUDAUXOUUGUGUUJAUXOUUHDRMZ
      ELMUUGAUUHDEAUUHUVOVCZUWJAEUWMVEWRAUYKBELABDABUWGVEUWJWSVHVNTWTXAVNWAUUOU
      XNUULUWCWCMZUXIPUUONUWCXCRMZUBMZUUHUAXDZRMZUAXEZUYOUULUYPRMZUAXEZUXNUYMPU
      UOUYOUYQUYSUAUUOUAXFUUONUYNXGUUOUYPUYOOZUHZUUHUYPVUBBDUUOUWFVUAUWHTZUUODV
      JOZVUAAVUDUUJADHVDTTZXHZVUAUYPVJOZUUOVUAUYPUYPNUYNXIVLUJZXJVUBNUYPLMZUUHP
      QZNUYQPQZVUBVUIUYNUUHVUBNUYPVUBWLVUHXHVUBUWCXCVUBDEVUEUUOUWLVUAUWNTXJZVUB
      XNXJZVUFVUBVUIUYPUYNPVUBUYPVUBUYPVUHVEVMVUAUYPUYNPQUUOUYPNUYNXKUJWJVUBUYN
      UWCUUHVUMVULVUFVUBUWCVULXLUUOUWCUUHPQVUAUYJTXMXMVUBNVJOZVUGUUHVJOVUJVUKXO
      UUOVUNVUAUYHTVUHVUFNUYPUUHXPXQXRVUBUULUYPVUBCDUUOCVJOZVUAAVUOUUJACGVDTZTZ
      VUEXHZVUHXJVUBUUHUULUYPVUFVURVUHVUBBCDVUCVUQVUEUUOBCPQZVUAAVUSUUJJTZTXSYD
      XTUUOUXNUYRUUOUUHVKOZUWTUXNUYRUGAVVAUUJUYLTUXFUUHUAUWCYAYBWAUUOUYMUYTUUOU
      ULVKOUWTUYMUYTUGUUOCDUUOCVUPVEZUWKYCZUXFUULUAUWCYAYBWAWOUUOUYMUVBUULUWCRM
      ZUDUEZSMZUXIUUOUWCNUULUBMZOUYMVVFUGUUOUWCNUULUXRAUULUSOUUJACDACGUOZUXAUPT
      ZUXCUXEUUOUXTDCLMZUWCUULPUUOUXSCDUYAVUPUYDUUOUXSUYECPUYFUUOUYECPQNUUMPQZU
      UONUUGUUMUYHUUOBEUWHUWNXHUUOUUMAUUMUSOZUUJACEVVHIUPZTZVLZUYGUUOBCEUWHVUPU
      WNVUTXSXMZUUONECUYHUWNVUPWIVQWJWKUYIUUODCUWKVVBWNWOXBUULUWCWPWQUUOVVEUVEU
      VBSUUOVVDUUMUDUUOVVDUULDRMZELMUUMUUOUULDEVVCUWKUWOWRUUOVVQCELUUOCDVVBUWKW
      SVHVNWTXAVNYEWJUUOUVLUXIUXKUUOUUPUUSUUOUUPUVQYFUUOUUSUWBYFUXHYGUUOUVBUVEU
      UOUVBUUOUULUUOCDACUKOZUUJGTUYCULUMZYFUUOUVEUUOUUMUUOVVLVVKUHUUMUKOUUOVVLV
      VKVVNVVPVRUUMUTVAUMZYFUUOUVEVVTVTZYGUUOUXKUUOUXKUURYHUUOUWCUUQUDUUOUWCUWE
      UUQUUOUWEUWCUWQWAUUOUUQUWEUWPWAVNWTZUXGVSYNYIXRUUOUXKUURUVLSVWBXAUUOUXKUV
      DUXISUUOUWCUVCUDUUOUWCUULCRMZERMUVCUUODVWCERUUOVWCDUUOCDVVBUWKYJWAVHUUOUU
      LCEVVCVVBUWOUUAVNWTXAWOUUOUVBUVEUVDUUOUVBVVSUNUUOUVEVVTUNZUUOUVDUUOUVCUUO
      UVCUWCUKUUOCDEVVBUWKUWOUUBUXFVSUMZUNZVWAUUOUVDVWEVTWBYEWJUUOUVHUUTUUPSUUO
      UUSUURUUOUUSUWBUNUUOUURUXGUNYKXAUUOUVJUVFUVBSUUOUVEUVDVWDVWFYKXAWOUUOUUNU
      VGUUOUUMVVGOZUUNUVGUGUUOUUMNUULUXRVVIVVNVVPUUOUUMUULPQUUMBCRMZLMZUULVWHLM
      ZPQUUOUUGUUHVWIVWJPUUJUUGUUHPQAUUGNUUHXKUJUUOVWIVWHELMCLMZUUGUUOVWIVWHECL
      MZLMZVWKUUOVWIVWLVWHLMVWMUUOUUMVWLVWHLUUOCEVVBUWOWNVHUUOVWLVWHUUOECUWOVVB
      YCUUOVWHUUOBCUWHVUPXJZVEZWNVNUUOVWKVWMUUOVWHECVWOUWOVVBYLWAVNUUOBCEUWIVVB
      UWOYOYMUUOVWJVWHDLMCLMZUUHUUOVWJVWHVVJLMZVWPUUOVWJVWHUULLMVWQUUOUULVWHVVC
      VWOWNUUOUULVVJVWHLUUOCDVVBUWKWNXAVNUUOVWPVWQUUOVWHDCVWOUWKVVBYLWAVNUUOBCD
      UWIVVBUWKYOYMWOUUOUUMUULVWHVVOUUOUULVVIVLVWNUUCVQXBUUMUULUIWQWAYEWJAUUJYP
      ZUHZUUKNUUNPVWSUVNUVRVWRUUKNUGAUVNVWRUVOTAUVRVWRUVTTAVWRYQUUGUUHYRXQVWSVW
      GNUUNPQVWSVWGUHZUUNVWTUUNVWGUUNYHOVWSUUMUULUUDUJVBUUEVWSVWGYPZUHZNNUUNPNN
      PQVXBUUFWHVXBUUNNVXBUULUKOVVLVXAUUNNUGVXBCDAVVRVWRVXAGYSAUYBVWRVXAHYSULVW
      SVVLVXAAVVLVWRVVMTTVWSVXAYQUUMUULYRXQWAYEYTWJYT $.
  $}

  ${
    $d N k l v $.  $d P k l v $.  $d k l ph v $.
    aks6d1c7lem1.1 $e |- ( ph -> P e. Prime ) $.
    aks6d1c7lem1.2 $e |- ( ph -> R e. NN ) $.
    aks6d1c7lem1.3 $e |- ( ph -> N e. ( ZZ>= ` 3 ) ) $.
    aks6d1c7lem1.4 $e |- ( ph -> P || N ) $.
    aks6d1c7lem1.5 $e |- ( ph -> ( N gcd R ) = 1 ) $.
    aks6d1c7lem1.6 $e |- E = ( k e. NN0 , l e. NN0 |->
    ( ( P ^ k ) x. ( ( N / P ) ^ l ) ) ) $.
    aks6d1c7lem1.7 $e |- L = ( ZRHom ` ( Z/nZ ` R ) ) $.
    aks6d1c7lem1.8 $e |- D = ( # ` ( L " ( E " ( NN0 X. NN0 ) ) ) ) $.
    aks6d1c7lem1.9 $e |- A = ( |_ ` ( ( sqrt ` ( phi ` R ) ) x.
     ( 2 logb N ) ) ) $.
    aks6d1c7lem1.10 $e |- ( ph -> ( ( 2 logb N ) ^ 2 ) <
     ( ( odZ ` R ) ` N ) ) $.
    $( The last set of inequalities of Claim 7 of Theorem 6.1
       ~ https://www3.nd.edu/%7eandyp/notes/AKS.pdf .  (Contributed by
       metakunt, 12-May-2025.) $)
    aks6d1c7lem1 $p |- ( ph -> ( N ^ ( |_ ` ( sqrt ` D ) ) ) <
    ( ( D + A ) _C ( D - 1 ) ) ) $=
      ( vv csqrt cfv cfl cexp co cn0 cima caddc c1 cmin cbc clt clogb cmul wcel
      c2 cz cc0 wbr wa cn c3 syl cr a1i cle ltletrd jca nnred wceq eqid eqeltrd
      sylibr nn0red nn0ge0d resqrtcld flcld sqrtge0d wb syl2anc elnn0z reexpcld
      flge mpbid 2re relogbcld eqeltrrd breqtrd remulcld cc recnd gtned syl3anc
      wne eqcomd 1nn0 letrd logblebd eqbrtrd mulge0d nn0addcld nnnn0d bccl ccxp
      ltled recxpcld reflcl fveq2d cdif eldifd oveq1d sqvald simpli cdiv nn0cnd
      zaddcld mpbird flwordi eqtrd oveq2d negsubd cvv wfn wss czring wf ffnd cv
      cop vex op1std op2ndd oveq12d eqcomi c0ex adantl exp0d fnfvima czrh chash
      cxp cphi cneg cuz eluzelz 0red 3re zred 3pos elnnz czn hashscontpowcl 0zd
      eluzle 2pos nngt0d 1ne2 necomi 1red 0le1 logbid1 leidd nn0addge1i breqtri
      2z 2p1e3 peano2zd 1zzd znegcld nn0zd 2nn0 nn0mulcld readdcld 1le2 cxplead
      phicld flle cxpexpzd cpr nelprd neneqd elsng mtbird cxplogb 3brtr3d elrpd
      csn cxpmul fllep1 leneltd cxpled cxpexpz remulcl resqcld 3lexlogpow2ineq2
      crp breqtrrd redivcld divge0d 3lexlogpow2ineq1 leexp1ad aks6d1c3 msqsqrtd
      c5 eqtr2d lt2sqd lemul2ad 2ap1caineq lelttrd 2timesd 1cnd addassd addcomd
      2rp mulcomd eqeltrrid aks6d1c4 sqrtled lemul1ad leadd2dd bcled pncand cbs
      ccrg crg crh zncrng crngring zringbas rhmf 4syl crn aks6d1c2p1 nnssz fssd
      zrhrhm fnima sseq1d c1st c2nd cmpt mpompt eqtri cprime prmnn nncnd nnne0d
      frn cmpo divcld mulridd adantr 0nn0 opelxpd 1nn fvmptd ssidd fvexd imaexd
      hashelne0d neqned elnnne0 nnrpd rpsqrtcld ltmul1dd sqrtmuld fllt zltp1led
      renegcld df-neg lem1d bcle2d ) AICUBUCZUDUCZUEUFZHGUGUGUUBZUHZUHZUUAUCZBU
      IUFZVVTUJUKUFZULUFZCBUIUFZCUJUKUFZULUFUMAVVPVVTEUUCUCZUBUCZUQIUNUFZUOUFZU
      DUCZUIUFZVWBULUFZVWCUMAVVPVWKVVTUJUUDZUIUFZULUFZVWLUMAVVPVWHVVTUBUCZUOUFZ
      UDUCZUJUIUFZVWJUIUFZVWSVWMUIUFZULUFZVWOAIVVOAIAIURUPZUSIUMUTZVAIVBUPZAVXC
      VXDAIVCUUEUCUPZVXCMVCIUUFVDZAUSVCIAUUGZVCVEUPAUUHVFZAIVXGUUIZUSVCUMUTAUUJ
      VFZAVXFVCIVGUTMVCIUUOVDZVHZVIIUUKVNZVJZAVVOURUPZUSVVOVGUTZVAVVOUGUPAVXPVX
      QAVVNACACACVVTUGCVVTVKARVFZADEFGHIEUULUCZJVXNKNLOPQVXSVLZUUMZVMZVOZACVYBV
      PZVQZVRZAUSVVNVGUTZVXQACVYCVYDVSAVVNVEUPZUSURUPZVYGVXQVTVYEAUUNZVVNUSWDWA
      WEVIVVOWBVNWCZAVXBAVWTUGUPZVXAURUPVXBUGUPAVWSVWJAVWRUJAVWRURUPZUSVWRVGUTZ
      VAVWRUGUPAVYMVYNAVWQAVWHVWPAUQIUQVEUPAWFVFZUSUQUMUTAUUPVFZVXOAIVXNUUQUQUJ
      WOZAUJUQUURUUSVFZWGZAVVTACVVTVEVXRVYCWHZAUSCVVTVGVYDVXRWIZVQZWJZVRZAUSVWQ
      VGUTZVYNAVWHVWPVYSWUBAUSUJVWHVXHAUUTZVYSUSUJVGUTAUVAVFAUJUQUQUNUFZVWHVGAW
      UGUJAUQWKUPZUQUSWOZVYQWUGUJVKAUQVYOWLZAUSUQVXHVYPWMZVYRUQUVBWNWPAUQUQIUQU
      RUPZAUVFVFZAUQVYOUVCZVYOVYPVXJVXMAUQVCIVYOVXIVXJUQVCVGUTAUQUQUJUIUFVCVGUQ
      UJWFWQUVDUVGUVEVFVXLWRZWSWTWRZAVVTVYTWUAVSZXAAVWQVEUPZVYIWUEVYNVTWUCVYJVW
      QUSWDWAWEVIVWRWBVNZUJUGUPAWQVFZXBZAVWJURUPZUSVWJVGUTZVAVWJUGUPAWVBWVCAVWI
      AVWGVWHAVWFAVWFAELUVQZVJZAVWFAVWFWVDXCVPZVQZVYSWJZVRAUSVWIVGUTZWVCAVWGVWH
      WVGVYSAVWFWVEWVFVSWUPXAAVWIVEUPZVYIWVIWVCVTWVHVYJVWIUSWDWAWEZVIVWJWBVNZXB
      ZAVWSVWMAVWRWUDUVHZAUJAUVIUVJZXQVXAVWTXDWAVOAVWOAVWKUGUPVWNURUPVWOUGUPAVV
      TVWJVYAWVLXBAVVTVWMAVVTVYAUVKZWVOXQVWNVWKXDWAVOAVVPVWTVWRULUFZVXBUMAVVPVW
      SVWPVWHUOUFZUDUCZUIUFZVWRULUFZWVQVYKAWWAAWVTUGUPVYMWWAUGUPAVWSWVSWVAAWVSU
      RUPZUSWVSVGUTZVAWVSUGUPAWWBWWCAWVRAVWPVWHWUBVYSWJZVRAUSWVRVGUTZWWCAVWPVWH
      WUBVYSWUQWUPXAAWVRVEUPZVYIWWEWWCVTWWDVYJWVRUSWDWAWEVIWVSWBVNZXBZWUDVWRWVT
      XDWAVOAWVQAVYLVYMWVQUGUPWVMWUDVWRVWTXDWAVOAVVPVWSVWRUIUFZVWRULUFZWWAUMAVV
      PVWRVWRUIUFZUJUIUFZVWRULUFZWWJUMAVVPUQVWRUOUFZUJUIUFZVWRULUFZWWMUMAVVPUQV
      WSUEUFZWWPVYKAUQVWSVYOWVAWCAWWPAWWOUGUPVYMWWPUGUPAWWNUJAUQVWRUQUGUPAUVLVF
      ZWUSUVMWUTXBWUDVWRWWOXDWAVOAVVPUQVWSXEUFZWWQVGAVVPUQVWQXEUFZWWSVYKAUQVWQV
      YOAUSUQVXHVYOVYPXFZWUCXGAUQVWSVYOWXAAVWRUJAWURVWRVEUPWUCVWQXHVDWUFUVNZXGA
      VVPUQVWHXEUFZVWPXEUFZWWTVGAIVVOXEUFIVWPXEUFVVPWXDVGAIVVOVWPVXJAUJUQIWUFVY
      OVXJUJUQVGUTAUVOVFZWUOWRAVYHVVOVEUPVYEVVNXHVDWUBAVVOVWPUDUCZVWPVGAVVNVWPU
      DACVVTUBVXRXIXIAVWPVEUPWXFVWPVGUTWUBVWPUVRVDWTUVPAIVVOAIVXJWLZAUSIVXHVXMW
      MZVYFUVSAIWXCVWPXEAWXCIAUQWKUSUJUVTZXJUPIWKUSUWHZXJUPWXCIVKAUQWKWXIWUJAUQ
      USUJWUKVYRUWAXKAIWKWXJWXGAIWXJUPZIUSVKZAIUSWXHUWBAVXEWXKWXLVTVXNIUSVBUWCV
      DUWDXKUQIUWEWAWPXLUWFAUQUWQUPZVWHVEUPZVWPWKUPWWTWXDVKAUQVYOVYPUWGVYSAVWPW
      UBWLZUQVWHVWPUWIWNUWRAVWQVWSVGUTZWWTWWSVGUTAWURWXPWUCVWQUWJVDAUQVWQVWSVYO
      AUJUQWUFVYOWXEVYRUWKWUCAVWSWVAVOUWLWEWRAWUHWUIVWSURUPWWSWWQVKWUJWUKWVNUQV
      WSUWMWNWIAVWRWUDAUQVWHVWHUOUFZUDUCZVWRVYOAWXQVEUPZWXRVEUPAWXNWXNVAWXSAWXN
      WXNVYSVYSVIVWHVWHUWNVDZWXQXHVDAVWRWUSVOAUQWXQVGUTZUQWXRVGUTZAUQVWHUQUEUFZ
      WXQVGAUQUQVCUNUFZUQUEUFZWYCVYOAWYDAUQVCVYOVYPVXIVXKVYRWGZUWOZAWYCWXQVEAVW
      HAVWHVYSWLZXMZWXTVMAUQWYEVYOWYGUQWYEUMUTZAWYJWYEVCUMUTUWPXNVFXFAWYDVWHUQW
      YFVYSWWRAUSVCUQXOUFZWYDVXHAVCUQVXIVYOWUKUWSZWYFAVCUQVXIWXMAUXOVFAUSVCVXHV
      XIVXKXFUWTAWYKWYDWYLWYFWYKWYDUMUTZAWYMWYDUXEVCXOUFUMUTUXAXNVFXFWRAUQVCIWU
      MWUNVXIVXKVXJVXMVXLWSUXBWRWYIWIAWXSWULWYAWYBVTWXTWUMWXQUQWDWAWEAWXSWURWXQ
      VWQVGUTWXRVWRVGUTAVWHVWHVYSVYSWJWUCAVWHVWPVWHVYSWUBVYSWUPAVWHVWPVYSWUBAVW
      HVWPUMUTWYCVWPUQUEUFZUMUTAWYCVVTWYNUMADEFGHIVXSJVXNKNLOPQVXTTUXCAWYNVWPVW
      PUOUFZVVTAVWPWXOXMAVVTAVVTVYAXPZUXDZUXFWIAVWHVWPVYSWUBWUPWUQUXGXRZXFUXHWX
      QVWQXSWNWRUXIUXJAWWOWWLVWRULAWWNWWKUJUIAVWRAVWRWUSXPZUXKXLXLWIAWWLWWIVWRU
      LAWWLVWRVWSUIUFWWIAVWRVWRUJWYSWYSAUXLZUXMAVWRVWSWYSAVWSWVAXPZUXNXTXLWIAWW
      IWVTVWRULAVWRWVSVWSUIAVWQWVRUDAVWHVWPWYHWXOUXPXIYAXLWIAWVTVWTVWRWWHWVMWUD
      AWVSVWJVWSAWVSWWGVOAVWJWVLVOZWXBAWWFWVJWVRVWIVGUTWVSVWJVGUTAVWPVWHAVVTAVV
      TAVVTCUGRVYBUXQZVOAVVTXUCVPVQZVYSWJWVHAVWPVWGVWHXUDWVGVYSWUPAVVTVWFVGUTVW
      PVWGVGUTADEFGHIJVXNKNLOPQUXRAVVTVWFVYTWUAWVEWVFUXSWEUXTWVRVWIXSWNUYAUYBVH
      AVWRVXAVWTULAVWRVWSUJUKUFZVXAAXUEVWRAVWRUJWYSWYTUYCWPAVXAXUEAVWSUJXUAWYTY
      BWPXTYAWIAVWSVVTVWJVWMWVAVYAWVLWVOAVWRVVTUMUTZVWSVVTVGUTAVWQVVTUMUTZXUFAV
      WQVVTVVTUOUFUBUCZVVTUMAVWQWYOXUHUMAVWHVWPVWPVYSWUBAVVTAVVTAVVTUGUPZVVTUSW
      OZVAVVTVBUPAXUIXUJVYAAVVTUSAVVSUJHUCZYCAHURYDVVRURYEZUJVVRUPXUKVVSUPAURVX
      SUYDUCZHAVXSUYEUPZVXSUYFUPHYFVXSUYGUFUPURXUMHYGAEUGUPXUNAELXCEVXSVXTUYHVD
      VXSUYIVXSHQUYQURXUMYFVXSHUYJXUMVLUYKUYLYHAXULGUYMZURYEZAVVQURGYGXUPAVVQVB
      URGADFGIJVXNKNPUYNZVBURYEAUYOVFUYPVVQURGVUIVDAVVRXUOURAGVVQYDZVVRXUOVKAVV
      QVBGXUQYHZVVQGUYRVDUYSXRAUSUSYJZGUCZUJVVRAUAXUTDUAYIZUYTUCZUEUFZIDXOUFZXV
      BVUAUCZUEUFZUOUFZUJVVQGVBGUAVVQXVHVUBZVKAGFJUGUGDFYIZUEUFZXVEJYIZUEUFZUOU
      FZVUJZXVIPXVIXVOFJUAUGUGXVHXVNXVBXVJXVLYJVKZXVDXVKXVGXVMUOXVPXVCXVJDUEXVJ
      XVLXVBFYKZJYKZYLYAXVPXVFXVLXVEUEXVJXVLXVBXVQXVRYMYAYNVUCYOVUDVFAXVBXUTVKZ
      VAZXVHDUSUEUFZXVEUSUEUFZUOUFZUJXVTXVDXWAXVGXWBUOXVTXVCUSDUEXVSXVCUSVKAUSU
      SXVBYPYPYLYQYAXVTXVFUSXVEUEXVSXVFUSVKAUSUSXVBYPYPYMYQYAYNAXWCUJVKXVSAXWCU
      JUJUOUFUJAXWAUJXWBUJUOADADADVUEUPDVBUPKDVUFVDZVUGZYRAXVEAIDWXGXWEADXWDVUH
      VUKYRYNAUJWYTVULXTVUMXTAUSUSUGUGUSUGUPAVUNVFZXWFVUOZUJVBUPAVUPVFVUQAXURVV
      QVVQYEXUTVVQUPXVAVVRUPXUSAVVQVURXWGVVQVVQGXUTYSWNWHURVVRHUJYSWNAHVVRYCAHV
      XSYTUCZYCHXWHVKAQVFAVXSYTVUSVMVUTVVAVVBVIVVTVVCVNVVDVVEWYRVVFAXUHWYOAVVTV
      VTVYTWUAVYTWUAVVGZWPWIAXUHWYOVVTXWIWYQXTWIAWURVVTURUPXUGXUFVTWUCWVPVWQVVT
      VVHWAWEAVWRVVTWUDWVPVVIWEAVWMUSVWJAUJWUFVVJVXHXUBAVWMUSUJUKUFZUSVGVWMXWJV
      KAUJVVKVFAUSVXHVVLWTWVKWRVVMVHAVWNVWBVWKULAVVTUJWYPWYTYBYAWIAVWKVWAVWBULA
      VWJBVVTUIVWJBVKABVWJSYOVFYAXLWIAVWAVWDVWBVWEULAVVTCBUIACVVTVXRWPZXLAVVTCU
      JUKXWKXLYNWI $.
  $}

  ${
    $d .~ a $.  $d A a $.  $d A b c h $.  $d A g i x $.  $d A k l s $.
    $d A i t x $.  $d B a $.  $d B g i x $.  $d B k l x $.  $d C a $.
    $d C g i x $.  $d C h $.  $d C k l x $.  $d D s $.  $d E a $.  $d E c y $.
    $d E e f y $.  $d E g i x y $.  $d E k l x y $.  $d G e f y $.
    $d G g i y $.  $d G h $.  $d G i t y $.  $d H a $.  $d H c h $.
    $d H g i x y $.  $d H s t $.  $d K a $.  $d K b c h j m $.  $d K e f y $.
    $d K g i x y $.  $d K j l m y $.  $d K i t x y $.  $d M b c h $.
    $d M l y $.  $d N a $.  $d N b c $.  $d N e f y $.  $d N k l s $.
    $d N k l x y $.  $d P a $.  $d P b c h $.  $d P e f y $.  $d P g i x y $.
    $d P k l s $.  $d P i t x y $.  $d Q a $.  $d Q b c h $.  $d Q g i x y $.
    $d Q k l s $.  $d Q i t x y $.  $d R a $.  $d R c h $.  $d R e f y $.
    $d R g i x y $.  $d R k l x y $.  $d S a $.  $d S c h $.  $d S g i x y $.
    $d S s t $.  $d a ph $.  $d b c h ph $.  $d g i ph x y $.  $d k l ph s $.
    $d ph s t $.
    aks6d1c7lem2.1 $e |- .~ = { <. e , f >. | ( e e. NN /\ f e.
     ( Base ` ( Poly1 ` K ) ) /\ A. y e. ( ( mulGrp ` K ) PrimRoots R )
     ( e ( .g ` ( mulGrp ` K ) ) ( ( ( eval1 ` K ) ` f ) ` y ) ) =
     ( ( ( eval1 ` K ) ` f ) ` ( e ( .g ` ( mulGrp ` K ) ) y ) ) ) } $.
    aks6d1c7lem2.2 $e |- P = ( chr ` K ) $.
    aks6d1c7lem2.3 $e |- ( ph -> K e. Field ) $.
    aks6d1c7lem2.4 $e |- ( ph -> P e. Prime ) $.
    aks6d1c7lem2.5 $e |- ( ph -> R e. NN ) $.
    aks6d1c7lem2.6 $e |- ( ph -> N e. ( ZZ>= ` 3 ) ) $.
    aks6d1c7lem2.7 $e |- ( ph -> P || N ) $.
    aks6d1c7lem2.8 $e |- ( ph -> ( N gcd R ) = 1 ) $.
    aks6d1c7lem2.9 $e |- E = ( k e. NN0 , l e. NN0 |->
    ( ( P ^ k ) x. ( ( N / P ) ^ l ) ) ) $.
    aks6d1c7lem2.10 $e |- L = ( ZRHom ` ( Z/nZ ` R ) ) $.
    aks6d1c7lem2.11 $e |- D = ( # ` ( L " ( E " ( NN0 X. NN0 ) ) ) ) $.
    aks6d1c7lem2.12 $e |- A = ( |_ ` ( ( sqrt ` ( phi ` R ) ) x.
     ( 2 logb N ) ) ) $.
    aks6d1c7lem2.13 $e |- ( ph -> ( ( 2 logb N ) ^ 2 ) <
     ( ( odZ ` R ) ` N ) ) $.
    aks6d1c7lem2.14 $e |- ( ph -> ( x e. ( Base ` K ) |->
     ( P ( .g ` ( mulGrp ` K ) ) x ) ) e. ( K RingIso K ) ) $.
    aks6d1c7lem2.15 $e |- ( ph -> M e. ( ( mulGrp ` K ) PrimRoots R ) ) $.
    aks6d1c7lem2.16 $e |- H = ( h e. ( NN0 ^m ( 0 ... A ) ) |->
     ( ( ( eval1 ` K ) ` ( G ` h ) ) ` M ) ) $.
    aks6d1c7lem2.17 $e |- B = ( |_ ` ( sqrt `
     ( # ` ( L " ( E " ( NN0 X. NN0 ) ) ) ) ) ) $.
    aks6d1c7lem2.18 $e |- C = ( E " ( ( 0 ... B ) X. ( 0 ... B ) ) ) $.
    aks6d1c7lem2.19 $e |- ( ph -> ( Q e. Prime /\ Q || N ) ) $.
    aks6d1c7lem2.20 $e |- ( ph -> A. b e. ( 1 ... A ) ( b gcd N ) = 1 ) $.
    aks6d1c7lem2.21 $e |- G = ( g e. ( NN0 ^m ( 0 ... A ) ) |->
    ( ( mulGrp ` ( Poly1 ` K ) ) gsum ( i e. ( 0 ... A ) |-> ( ( g ` i )
    ( .g ` ( mulGrp ` ( Poly1 ` K ) ) ) ( ( var1 ` K ) ( +g ` ( Poly1 ` K ) )
    ( ( algSc ` ( Poly1 ` K ) ) ` ( ( ZRHom ` K ) ` i ) ) ) ) ) ) ) $.
    aks6d1c7lem2.22 $e |- ( ph -> A. a e. ( 1 ... A ) N .~ ( ( var1 ` K )
     ( +g ` ( Poly1 ` K ) )
     ( ( algSc ` ( Poly1 ` K ) ) ` ( ( ZRHom ` K ) ` a ) ) ) ) $.
    aks6d1c7lem2.23 $e |- S = { s e. ( NN0 ^m ( 0 ... A ) ) |
     sum_ t e. ( 0 ... A ) ( s ` t ) <_ ( D - 1 ) } $.
    $( Contradiction to Claim 2 and Claim 7.  We assumed in Claim 2 that there
       are two different prime numbers ` P ` and ` Q ` .  (Contributed by
       metakunt, 16-May-2025.) $)
    aks6d1c7lem2 $p |- ( ph -> P = Q ) $=
      ( vm vj vc wceq simpr wne wa cn0 cc0 cfz cmap cima chash cfv cexp cle wbr
      co cfield wcel adantr cprime cn cz clt c3 syl cr a1i zred jca sylibr cgcd
      cdvds c1 csqrt c2 clogb cfl resqrtcld flcld sqrtge0d eqbrtrd flge syl2anc
      nnge1d wb mpbid elnn0z eqeltrid cv cplusg wral cbs cmpt eqid nn0red rexrd
      cmg cvv cxr fveq2i c0g cress czring cuni nfcv cuz eluzelz 0red 3re eluzle
      3pos ltletrd elnnz cphi cmul phicld nnred 1red 0le1 letrd 2pos 1lt2 ltned
      2re necomd relogbcld remulcld cc recnd gtned logb1 syl3anc eqcomd 2z 0lt1
      leidd logblebd mulge0d 0zd cv1 czrh cpl1 cascl cmgp crs cprimroots simpld
      simprd 3jca aks6d1c2 wn caddc cmin cbc cxp hashscontpowcl nn0ge0d zexpcld
      nnzd nn0addcld nn0zd 1zzd zsubcld bccl ovexd mptexd imaexd hashxrcl eqcom
      czn ce1 mpbi eqtri oveq2d codz aks6d1c7lem1 wrex crab ccnv crn csn imaeq2
      cqg cqus unieqd cbvmpt aks6d1c6lem5 xrltletrd xrltnle pm2.21dd pm2.61dane
      ) AIJVQZIJAUYGVRAIJVSZVTZUBWAWBEWCWKZWDWKZWEZWFWGZUFFWHWKZWIWJZUYGUYIBCEF
      GIJKLNOPQRSTUAUBUCUDUEUFUHUJUKULAUCWLWMUYHUMWNZAIWOWMUYHUNWNZALWPWMUYHUOW
      NZAUFWPWMZUYHAUFWQWMZWBUFWRWJZVTUYSAUYTVUAAUFWSUUAWGWMZUYTUPWSUFUUBWTZAWB
      WSUFAUUCZWSXAWMAUUDXBAUFVUCXCZWBWSWRWJAUUFXBAVUBWSUFWIWJUPWSUFUUEWTUUGZXD
      UFUUHXEZWNZAIUFXGWJUYHUQWNZAUFLXFWKXHVQUYHURWNZVKAEWAWMUYHAELUUIWGZXIWGZX
      JUFXKWKZUUJWKZXLWGZWAVBAVUOWQWMZWBVUOWIWJZVTVUOWAWMAVUPVUQAVUNAVULVUMAVUK
      AVUKALUOUUKZUULZAWBXHVUKVUDAUUMZVUSWBXHWIWJAUUNXBAVUKVURXSUUOZXMZAXJUFXJX
      AWMAUUSXBZWBXJWRWJAUUPXBZVUEVUFAXHXJAXHXJVUTXHXJWRWJAUUQXBUURUUTZUVAZUVBZ
      XNAWBVUNWIWJZVUQAVULVUMVVBVVFAVUKVUSVVAXOAWBXJXHXKWKZVUMWIAVVIWBAXJUVCWMX
      JWBVSXJXHVSVVIWBVQAXJVVCUVDAWBXJVUDVVDUVEVVEXJUVFUVGUVHAXJXHUFXJWQWMAUVIX
      BAXJVVCUVKVUTWBXHWRWJAUVJXBVUEVUFAUFVUGXSUVLXPUVMAVUNXAWMWBWQWMZVVHVUQXTV
      VGAUVNZVUNWBXQXRYAXDVUOYBXEYCWNZUSUTAUFUCUVOWGUHYDUCUVPWGWGUCUVQWGZUVRWGW
      GVVMYEWGWKKWJUHXHEWCWKZYFUYHVLWNZABUCYGWGIBYDUCUVSWGZYLWGWKYHUCUCUVTWKWMU
      YHVDWNZAUEVVPLUWAWKWMUYHVEWNZVFVGVHUYIJWOWMZJUFXGWJZUYHAVVSUYHAVVSVVTVIUW
      BWNAVVTUYHAVVSVVTVIUWCWNAUYHVRUWDUWEUYIUYNUYMWRWJZUYOUWFZUYIUYNHEUWGWKZHX
      HUWHWKZUWIWKZUYMUYIUYNAUYNXAWMUYHAUYNAUFFAUFVUGUWNAFUDTWAWAUWJWEWEWFWGZXI
      WGZXLWGZWAVGAVWHWQWMZWBVWHWIWJZVTVWHWAWMAVWIVWJAVWGAVWFAVWFAILSTUDUFLUXEW
      GZUJVUGUNUQUOURUSUTVWKYIUWKZYJZAVWFVWLUWLZXMZXNAWBVWGWIWJZVWJAVWFVWMVWNXO
      AVWGXAWMVVJVWPVWJXTVWOVVKVWGWBXQXRYAXDVWHYBXEYCUWMXCWNYKZUYIVWEUYIVWEUYIV
      WCWAWMVWDWQWMVWEWAWMUYIHEUYIHVWFWAVAAVWFWAWMUYHVWLWNYCZVVLUWOUYIHXHUYIHVW
      RUWPUYIUWQUWRVWDVWCUWSXRYJYKUYIUYLYMWMUYMYNWMZUYIUBUYKYMUYIUBQUYKUEQYDZUA
      WGUCUXFWGWGWGZYHYMVFUYIQUYKVXAYMUYIWAUYJWDUWTUXAYCUXBUYLYMUXCWTZUYIUYNUFH
      XIWGZXLWGZWHWKVWEWRUYIFVXDUFWHFVXDVQUYIFVWHVXDVGVWGVXCXLVWFHXIHVWFVQVWFHV
      QVAHVWFUXDUXGYOYOUXHXBUXIUYIEHILSTUDUFUJUYQUYRAVUBUYHUPWNVUIVUJUSUTVAVBAV
      UMXJWHWKUFLUXJWGWGWRWJUYHVCWNUXKXPUYIBCDEHIKLMVNYDVOYDVVPYEWGWKVVPYPWGVQV
      NVVPYGWGZUXLVOVXEUXMZNOPQRVPSVOVNTUAUBVPWQVPYDUEVVPVXFYQWKZYLWGWKYHZUCUDU
      EUFQYRYRVXHUXNVXGVXHUXOYQWKYPWGUXPWEUXRWKUXSWKYGWGZVXHVWTWEZYSZYHUGUHUIUJ
      UKULUYPUYQUYRVUHVUIVUJAUIYDZUFXFWKXHVQUIVVNYFUYHVJWNVKVBUSUTVVOVVQVVRVFVA
      VMVXHYIVXFYIQUIVXIVXKVXHVXLWEZYSZUIVXKYTQVXNYTVWTVXLVQVXJVXMVWTVXLVXHUXQU
      XTUYAUYBUYCUYIUYNYNWMVWSVWAVWBXTVWQVXBUYNUYMUYDXRYAUYEUYF $.
  $}

  ${
    aks6d1c7.1 $e |- .~ = { <. e , f >. | ( e e. NN /\ f e.
     ( Base ` ( Poly1 ` K ) ) /\ A. y e. ( ( mulGrp ` K ) PrimRoots R )
     ( e ( .g ` ( mulGrp ` K ) ) ( ( ( eval1 ` K ) ` f ) ` y ) ) =
     ( ( ( eval1 ` K ) ` f ) ` ( e ( .g ` ( mulGrp ` K ) ) y ) ) ) } $.
    aks6d1c7.2 $e |- P = ( chr ` K ) $.
    aks6d1c7.3 $e |- ( ph -> K e. Field ) $.
    aks6d1c7.4 $e |- ( ph -> P e. Prime ) $.
    aks6d1c7.5 $e |- ( ph -> R e. NN ) $.
    aks6d1c7.6 $e |- ( ph -> N e. ( ZZ>= ` 3 ) ) $.
    aks6d1c7.7 $e |- ( ph -> P || N ) $.
    aks6d1c7.8 $e |- ( ph -> ( N gcd R ) = 1 ) $.
    aks6d1c7.9 $e |- A = ( |_ ` ( ( sqrt ` ( phi ` R ) ) x.
     ( 2 logb N ) ) ) $.
    aks6d1c7.10 $e |- ( ph -> ( ( 2 logb N ) ^ 2 ) <
     ( ( odZ ` R ) ` N ) ) $.
    aks6d1c7.11 $e |- ( ph -> ( x e. ( Base ` K ) |->
     ( P ( .g ` ( mulGrp ` K ) ) x ) ) e. ( K RingIso K ) ) $.
    aks6d1c7.12 $e |- ( ph -> M e. ( ( mulGrp ` K ) PrimRoots R ) ) $.
    aks6d1c7.13 $e |- ( ph -> A. b e. ( 1 ... A ) ( b gcd N ) = 1 ) $.
    aks6d1c7.14 $e |- ( ph -> A. a e. ( 1 ... A ) N .~ ( ( var1 ` K )
     ( +g ` ( Poly1 ` K ) )
     ( ( algSc ` ( Poly1 ` K ) ) ` ( ( ZRHom ` K ) ` a ) ) ) ) $.
    ${
      $d .~ a $.  $d g h k l ph x y $.  $d P g h i j k x y $.  $d P e f i $.
      $d N i j k v $.  $d R u v $.  $d A a q u $.  $d P o p u $.  $d a ph $.
      $d N e f j $.  $d R e f $.  $d A e f m n y $.  $d M a l $.
      $d A k l o p $.  $d K b $.  $d M g h w x y $.  $d P b v $.  $d M b v $.
      $d Q g h l x y $.  $d R k o p $.  $d b ph v $.  $d R g h k l x y $.
      $d N i j l o $.  $d Q b v $.  $d A q v $.  $d K g h m n x $.
      $d K m n o p $.  $d M o p w $.  $d P a j l $.  $d K l v $.  $d o p q $.
      $d N h p x y $.  $d Q l o p $.  $d R a k $.  $d o p ph $.  $d A b $.
      $d K e f y $.  $d A m n v w $.  $d N g h i j u x y $.  $d A g h q x y $.
      $d N a i k $.  $d K a m n w $.  $d N b $.  $d Q a k $.
      aks6d1c7lem3.1 $e |- ( ph -> ( Q e. Prime /\ Q || N ) ) $.
      $( Remove lots of hypotheses now that we have the AKS contradiction.
         (Contributed by metakunt, 16-May-2025.) $)
      aks6d1c7lem3 $p |- ( ph -> P = Q ) $=
        ( vp vi vj vq vu vk vl vg vv vh vm vn vw vo czn cfv czrh cn0 cv cexp co
        cdiv cmul cmpo cxp cima chash cfl cc0 cfz csu c1 cmin cle wbr cmap crab
        csqrt cpl1 cmgp cv1 cascl cplusg cmg cmpt cgsu ce1 nfcv wa simpl oveq2d
        wceq simpr oveq12d cbvmpo eqid 2fveq3 fveq1d cbvmpt fveq2 a1i mpteq2dva
        wcel oveq1d eqtrd sumeq2dv cbvsum eqcomi imaeq1d imaeq2d fveq2d breq12d
        nfv cbvrabw aks6d1c7lem2 ) ABCUKDHVEVFVGVFZULUMVHVHEULVIZVJVKZMEVLVKZUM
        VIZVJVKZVMVKZVNZVHVHVOZVPZVPZVQVFZWHVFVRVFZYMVSYRVTVKZYSVOVPZYQEFGHVSDV
        TVKZUNVIZUOVIZVFZUNWAZYFUPUQVHVHEUPVIZVJVKZYIUQVIZVJVKZVMVKZVNZYNVPZVPZ
        VQVFZWBWCVKZWDWEZUOVHUUAWFVKZWGIJURUSUTUPYMVAUUQKWIVFZWJVFZVBUUAVBVIZVA
        VIZVFZKWKVFZUUTKVGVFZVFUURWLVFZVFZUURWMVFZVKZUUSWNVFZVKZWOZWPVKZWOZVCUU
        QLVCVIZUVMVFKWQVFZVFZVFZWOKYFLMVDNOUQPQRSTUAUBUCULUMUPUQVHVHYLUUJUPYLWR
        UQYLWRULUUJWRUMUUJWRYGUUFXBZYJUUHXBZWSZYHUUGYKUUIVMUVTYGUUFEVJUVRUVSWTX
        AUVTYJUUHYIVJUVRUVSXCXAXDXEZYFXFYQXFUDUEUFUGVCUSUUQUVQLUSVIZUVMVFUVOVFZ
        VFZUSUVQWRVCUWDWRUVNUWBXBLUVPUWCUVNUWBUVOUVMXGXHXIYRXFYTXFUJUHVAURUUQUV
        LUUSUTUUAUTVIZURVIZVFZUVCUWEUVDVFUVEVFZUVGVKZUVIVKZWOZWPVKZURUVLWRVAUWL
        WRUVAUWFXBZUVKUWKUUSWPUWMUVKUTUUAUWEUVAVFZUWIUVIVKZWOZUWKUVKUWPXBUWMVBU
        TUUAUVJUWOUTUVJWRVBUWOWRUUTUWEXBZUVBUWNUVHUWIUVIUUTUWEUVAXJUWQUVFUWHUVC
        UVGUUTUWEUVEUVDXGXAXDXIXKUWMUTUUAUWOUWJUWMUWEUUAXMZWSZUWNUWGUWIUVIUWSUW
        EUVAUWFUWMUWRWTXHXNXLXOXAXIUIUUPUUAUKVIZVDVIZVFZUKWAZYQWBWCVKZWDWEZUOVD
        UUQUOUUQWRVDUUQWRUUPVDYCUXEUOYCUUCUXAXBZUUEUXCUUOUXDWDUXFUUEUUAUUBUXAVF
        ZUNWAZUXCUXFUUAUUDUXGUNUXFUUBUUAXMZWSUUBUUCUXAUXFUXIWTXHXPUXHUXCXBUXFUU
        AUXGUXBUNUKUUBUWTUXAXJUKUXGWRUNUXBWRXQXKXOUXFUUNYQWBWCUXFUUMYPVQUXFUULY
        OYFUXFUUKYMYNUUKYMXBUXFYMUUKUWAXRXKXSXTYAXNYBYDYE $.
    $}

    ${
      $d .~ a $.  $d A a $.  $d A b $.  $d A e f y $.  $d A x y $.  $d K a $.
      $d K b $.  $d K e f y $.  $d K x y $.  $d M a $.  $d M b $.  $d M x y $.
      $d N a p $.  $d N b p $.  $d N e f y $.  $d N p x y $.  $d P a p $.
      $d P b p $.  $d P e f y $.  $d P p x y $.  $d R a $.  $d R e f y $.
      $d R x y $.  $d a p ph $.  $d b p ph $.  $d ph x y $.
      $( In the AKS algorithm there exists a unique prime number ` p ` that
         divides ` N ` .  (Contributed by metakunt, 16-May-2025.) $)
      aks6d1c7lem4 $p |- ( ph -> E! p e. Prime p || N ) $=
        ( cprime wcel cdvds wbr cv wceq wi wral w3a wreu wa cfield ad2antrr cuz
        cn c3 cfv cgcd co c1 c2 clogb cexp codz clt cbs cmgp cmg crs cprimroots
        cmpt cfz cv1 czrh cpl1 cascl cplusg simplr simpr aks6d1c7lem3 eqcomd ex
        jca ralrimiva 3jca breq1 eqreu syl ) AEUJUKZELULUMZMUNZLULUMZWTEUOZUPZM
        UJUQZURXAMUJUSAWRWSXDSUBAXCMUJAWTUJUKZUTZXAXBXFXAUTZEWTXGBCDEWTFGHIJKLN
        OPQAJVAUKXEXARVBAWRXEXASVBAGVDUKXEXATVBALVEVCVFUKXEXAUAVBAWSXEXAUBVBALG
        VGVHVIUOXEXAUCVBUDAVJLVKVHVJVLVHLGVMVFVFVNUMXEXAUEVBABJVOVFEBUNJVPVFZVQ
        VFVHVTJJVRVHUKXEXAUFVBAKXHGVSVHUKXEXAUGVBAOUNLVGVHVIUOOVIDWAVHZUQXEXAUH
        VBALJWBVFNUNJWCVFVFJWDVFZWEVFVFXJWFVFVHFUMNXIUQXEXAUIVBXGXEXAAXEXAWGXFX
        AWHWLWIWJWKWMWNXAWSMUJEWTELULWOWPWQ $.
    $}

    ${
      $d .~ a $.  $d A a $.  $d A b $.  $d A e f y $.  $d A x y $.  $d K a $.
      $d K b $.  $d K e f y $.  $d K x y $.  $d M a $.  $d M b $.  $d M x y $.
      $d N a p $.  $d N b p $.  $d N e f y $.  $d N p q r s $.  $d N p x y $.
      $d P a p $.  $d P b p $.  $d P e f y $.  $d P p q r s $.  $d P p x y $.
      $d R a $.  $d R e f y $.  $d R x y $.  $d a p ph $.  $d b p ph $.
      $d ph q r $.  $d ph x y $.
      $( ` N ` is a prime power if the hypotheses of the AKS algorithm hold.
         Claim 7 of Theorem 6.1 ~ https://www3.nd.edu/%7eandyp/notes/AKS.pdf .
         (Contributed by metakunt, 16-May-2025.) $)
      aks6d1c7 $p |- ( ph -> N = ( P ^ ( P pCnt N ) ) ) $=
        ( vq vp vr vs cpc co cexp wceq cv cprime wral cdvds wb wcel wa ad2antrr
        wbr simpr breq1 eqeq1 bibi12d nfv equequ1 cbvralw bilani rspcdva biimpd
        mpd eqcomd eqtrd oveq1d cmul c1 cn cz cc0 clt c3 cuz cfv eluzelz syl cr
        0red 3re a1i zred cle eluzle ltletrd elnnz sylibr pcelnn syl2anc mpbird
        3pos jca nncnd mulridd 1nn0 pcidlem prmnn exp1d oveq2d adantr ad3antrrr
        cn0 cq wne nnq nnne0d pcexp syl3anc wn bicomd notbid biimpa pceq0 neqne
        adantl neeqtrd neneqd c2 prmuz2 dvdsprm mtbird ad4antr prmdvdsexp pccld
        nnzd nnexpcld nnnn0d pm2.61dan ralrimiva wreu wrex aks6d1c7lem4 r19.29a
        reu6 sylib nn0expcld pc11 ) ALEELUMUNZUOUNZUPZUIUQZLUMUNZUUNUULUMUNZUPZ
        UIURUSZAUJUQZLUTVEZUUSUKUQZUPZVAZUJURUSZUURUKURAUVAURVBZVCZUVDVCZUUQUIU
        RUVGUUNURVBZVCZUUNUVAUPZUUQUVIUVJVCZUUOUUKUUPUVKUUNELUMUVKUUNUVAEUVIUVJ
        VFUVKEUVAUVGEUVAUPZUVHUVJUVGELUTVEZUVLAUVMUVEUVDUAVDZUVGUVMUVLUVGULUQZL
        UTVEZUVOUVAUPZVAZUVMUVLVAZULUREUVOEUPUVPUVMUVQUVLUVOELUTVGUVOEUVAVHVIZU
        VDUVRULURUSZUVFUVCUVRUJULURUVCULVJUVRUJVJUUSUVOUPUUTUVPUVBUVQUUSUVOLUTV
        GUJULUKVKVIVLVMZAEURVBZUVEUVDRVDZVNVOVPVDVQVRZVSUVKUUKEUULUMUNZUUPUVKUU
        KUUKEEUMUNZVTUNZUWFUVFUUKUWHUPZUVDUVHUVJAUWIUVEAUUKUUKWAVTUNZUWHAUWJUUK
        AUUKAUUKAUUKWBVBZUVMUAAUWCLWBVBZUWKUVMVARALWCVBZWDLWEVEZVCUWLAUWMUWNALW
        FWGWHVBZUWMTWFLWIWJZAWDWFLAWLWFWKVBAWMWNALUWPWOWDWFWEVEAXDWNAUWOWFLWPVE
        TWFLWQWJWRXELWSWTZELXAXBXCZXFXGVQAWAUWGUUKVTAWAEEWAUOUNZUMUNZUWGAUWTWAA
        UWCWAXOVBZUWTWAUPRUXAAXHWNWAEXIXBVQAUWSEEUMAEAEAUWCEWBVBZREXJWJZXFXKXLV
        RXLVRXMXNUVKUWFUWHUVKUWCEXPVBZEWDXQZVCZUUKWCVBZUWFUWHUPUVGUWCUVHUVJUWDV
        DUVFUXFUVDUVHUVJAUXFUVEAUXDUXEAUXBUXDUXCEXRWJAEUXCXSXEXMXNUVIUXGUVJUVGU
        XGUVHUVFUXGUVDAUXGUVEAUUKUWRYRXMXMXMXMEEUUKXTYAVQVRUVKEUUNUULUMUVKUUNEU
        WEVQVSVRVRUVIUVJYBZVCZUUOWDUUPUXIUUOWDUPZUUNLUTVEZYBZUVIUXHUXLUVIUVJUXK
        UVIUXKUVJUVIUVRUXKUVJVAULURUUNUVOUUNUPUVPUXKUVQUVJUVOUUNLUTVGULUIUKVKVI
        UVGUWAUVHUWBXMZUVGUVHVFZVNYCYDYEUXIUVHUWLUXJUXLVAUVIUVHUXHUXNXMZUVFUWLU
        VDUVHUXHAUWLUVEUWQXMXNZUUNLYFXBXCUXIUUPWDUXIUUPWDUPZUUNUULUTVEZYBZUXIUX
        RUUNEUTVEZUXIUXTUUNEUPZUXIUUNEUXIUUNUVAEUXHUUNUVAXQUVIUUNUVAYGYHUXIEUVA
        UVIUVLUXHUVIUVMUVLUVGUVMUVHUVNXMUVIUVMUVLUVIUVRUVSULUREUVTUXMUVGUWCUVHU
        WDXMVNVOVPXMVQYIYJUXIUUNYKWGWHVBZUWCUXTUYAVAUVIUYBUXHUVHUYBUVGUUNYLYHXM
        UVGUWCUVHUXHUWDVDZEUUNYMXBYNUXIUVHEWCVBUWKUXRUXTVAUXOUXIEAUXBUVEUVDUVHU
        XHUXCYOZYRUVIUWKUXHUVGUWKUVHUVFUWKUVDAUWKUVEUWRXMXMXMXMEUUNUUKYPYAYNUXI
        UVHUULWBVBUXQUXSVAUXOUXIEUUKUYDUXIELUYCUXPYQYSUUNUULYFXBXCVQVRUUAUUBAUU
        TUJURUUCUVDUKURUUDABCDEFGHIJKLUJMNOPQRSTUAUBUCUDUEUFUGUHUUEUUTUJUKURUUG
        UUHUUFALXOVBUULXOVBUUMUURVAALUWQYTAEUUKAEUXCYTAELRUWQYQUUILUULUIUUJXBXC
        $.
    $}
  $}

  ${
    $d .0. x z $.  $d F q $.  $d F x z $.  $d G q $.  $d G x y z $.  $d H q $.
    $d J q $.  $d K q $.  $d N q $.  $d Q q $.  $d X x y z $.  $d g ph q $.
    $d ph x z $.
    rhmqusspan.1 $e |- .0. = ( 0g ` H ) $.
    rhmqusspan.2 $e |- ( ph -> F e. ( G RingHom H ) ) $.
    rhmqusspan.3 $e |- K = ( `' F " { .0. } ) $.
    rhmqusspan.4 $e |- Q = ( G /s ( G ~QG N ) ) $.
    rhmqusspan.5 $e |- J = ( q e. ( Base ` Q ) |-> U. ( F " q ) ) $.
    rhmqusspan.6 $e |- ( ph -> G e. CRing ) $.
    rhmqusspan.7 $e |- N = ( ( RSpan ` G ) ` { X } ) $.
    rhmqusspan.8 $e |- ( ph -> X e. ( Base ` G ) ) $.
    rhmqusspan.9 $e |- ( ph -> ( F ` X ) = .0. ) $.
    $( Ring homomorphism out of a quotient given an ideal spanned by a
       singleton.  (Contributed by metakunt, 7-Jun-2025.) $)
    rhmqusspan $p |- ( ph -> ( J e. ( Q RingHom H ) /\
    A. g e. ( Base ` G ) ( J ` [ g ] ( G ~QG N ) ) = ( F ` g ) ) ) $=
      ( vx vy vz crh co wcel cv cqg cec cfv wceq cbs wral csn crsp ccnv cima wa
      cdsr wbr cab crg crngringd rspsn syl2anc eleq2d biimpd imp wi cvv vex a1i
      eqid breq2 elabg syl cmulr wrex dvdsr bilani fveq2 eqcomd adantl ad2antrr
      rhmmul syl3anc oveq2d csrg rhmrcl2 ringsrg 3syl wf rhmf adantr ffvelcdmda
      simpr srgrz eqtrd nfv oveq1 eqeq1d cbvrexw r19.29a ex mpd wb fvexd mpbird
      elsng cdm ffund clidl wss lidl1 snssd rspssp sselda fdm eleqtrrd fvimacnv
      wfun mpbid ssrdv eqcomi sseqtrdi eqsstrid rspcl eqeltrid rhmqusnsg rhmghm
      cghm cnsg lidlnsg ghmqusnsglem1 ralrimiva jca ) AGBFUEUFUGCUHZEIUIUFUJGUK
      YRDUKULZCEUMUKZUNABDEFGHIKLMNOPQRAIJUOZEUPUKZUKZHSAUUCDUQKUOZURZHAUBUUCUU
      EAUBUHZUUCUGZUUFUUEUGZAUUGUSZUUFDUKZUUDUGZUUHUUIUUKUUJKULZUUIUUFJUCUHZEUT
      UKZVAZUCVBZUGZUULAUUGUUQAUUGUUQAUUCUUPUUFAEVCUGZJYTUGZUUCUUPULAERVDZTUCYT
      UUNEJUUBYTVNZUUBVNZUUNVNZVEVFVGVHVIAUUQUULVJUUGAUUQUULAUUQUSJUUFUUNVAZUUL
      AUUQUVDAUUFVKUGZUUQUVDVJUVEAUBVLVMUVEUUQUVDUUOUVDUCUUFVKUUMUUFJUUNVOVPVHV
      QVIAUVDUULVJUUQAUVDUULAUVDUSUUSUUMJEVRUKZUFZUUFULZUCYTVSZUSZUULUVDUVJAUCY
      TUUNEUVFJUUFUVAUVCUVFVNZVTWAAUVJUULVJUVDAUVJUULAUVJUSZUDUHZJUVFUFZUUFULZU
      ULUDYTUVLUVMYTUGZUSZUVOUSUUJUVNDUKZKUVOUUJUVRULUVQUVOUVRUUJUVNUUFDWBWCWDU
      VQUVRKULUVOUVQUVRUVMDUKZJDUKZFVRUKZUFZKUVQDEFUEUFUGZUVPUUSUVRUWBULAUWCUVJ
      UVPNWEZUVLUVPWQAUUSUVJUVPTWEUVMJEFUVFUWADYTUVAUVKUWAVNZWFWGUVQUWBUVSKUWAU
      FZKUVQUVTKUVSUWAAUVTKULUVJUVPUAWEWHUVQFWIUGZUVSFUMUKZUGUWFKULUVQUWCFVCUGU
      WGUWDEFDWJFWKWLUVLYTUWHUVMDAYTUWHDWMZUVJAUWCUWINYTUWHEFDUVAUWHVNZWNVQZWOW
      PUWHFUWAUVSKUWJUWEMWRVFWSWSWOWSUVJUVOUDYTVSZAUVIUWLUUSUVHUVOUCUDYTUVHUDWT
      UVOUCWTUUMUVMULUVGUVNUUFUUMUVMJUVFXAXBXCWAWDXDXEWOXFXEWOXFXEWOXFUUIUUJVKU
      GUUKUULXGUUIUUFDXHUUJKVKXJVQXIUUIDYBZUUFDXKZUGUUKUUHXGAUWMUUGAYTUWHDUWKXL
      WOUUIUUFYTUWNAUUCYTUUFAUURYTEXMUKZUGZUUAYTXNZUUCYTXNUUTAUURUWPUUTYTEUWOUW
      OVNZUVAXOVQAJYTTXPZEUWOUUAYTUUBUVBUWRXQWGXRAUWNYTULZUUGAUWIUWTUWKYTUWHDXS
      VQWOXTUUFUUDDYAVFYCXEYDHUUEOYEYFYGZAIUUCUWOSAUURUWQUUCUWOUGUUTUWSYTEUWOUU
      AUUBUVBUVAUWRYHVFYIZYJAYSCYTAYRYTUGZUSZBDEFGHIYRKLMUXDUWCDEFYLUFUGAUWCUXC
      NWOEFDYKVQOPQAIHXNUXCUXAWOAIEYMUKUGZUXCAUURIUWOUGUXEUUTUXBEIYNVFWOAUXCWQY
      OYPYQ $.
  $}

  ${
    aks5lem1.1 $e |- ( ph -> K e. Field ) $.
    aks5lem1.2 $e |- P = ( chr ` K ) $.
    aks5lem1.3 $e |- ( ph -> ( P e. Prime /\ N e. NN /\ P || N ) ) $.
    aks5lem1.4 $e |- F = ( p e. ( Base ` ( Poly1 ` ( Z/nZ ` N ) ) ) |->
    ( G o. p ) ) $.
    aks5lem1.5 $e |- G = ( q e. ( Base ` ( Z/nZ ` N ) ) |->
    U. ( ( ZRHom ` K ) " q ) ) $.
    aks5lem1.6 $e |- H = ( r e. ( Base ` ( Poly1 ` K ) ) |->
     ( ( ( eval1 ` K ) ` r ) ` M ) ) $.
    ${
      $d G p $.  $d K p $.  $d K q $.  $d K r $.  $d M r $.  $d N p $.
      $d N q $.  $d p ph $.  $d ph r $.
      aks5lem1.7 $e |- ( ph -> M e. ( Base ` K ) ) $.
      $( Section 5 of ~ https://www3.nd.edu/%7eandyp/notes/AKS.pdf.
         Construction of a ring homomorphism out of Zn X to K. (Contributed by
         metakunt, 7-Jun-2025.) $)
      aks5lem1 $p |- ( ph -> ( H o. F ) e. ( ( Poly1 ` ( Z/nZ ` N ) )
      RingHom K ) ) $=
        ( cfv wcel cpl1 crh czn ccom cbs eqid fldcrngd evl1maprhm ccrg crngring
        co ce1 crg syl cprime cn cdvds wbr simp2d cchr eqcomi simp1d prmnn nnzd
        cz eqeltrid simp3d eqbrtrid zndvdchrrhm rhmply1 rhmco syl2anc ) AEFUASZ
        FUBUKTCHUCSZUASZVMUBUKTECUDVOFUBUKTAFUESZVMFVMUESZEFULSZGIVRUFVMUFZVPUF
        VQUFAFLUGZRQUHAVOUESZVOVMVNFCDKVOUFVSWAUFOAJFDHVNAFUITFUMTVTFUJUNABUOTZ
        HUPTZBHUQURZNUSAFUTSZBVEBWEMVAZABAWBBUPTAWBWCWDNVBBVCUNVDVFAWEBHUQWFAWB
        WCWDNVGVHVNUFPVIVJVOVMFECVKVL $.
    $}

    ${
      $d A s $.  $d F s $.  $d G p $.  $d H s $.  $d I s $.  $d K l $.
      $d K p $.  $d K q $.  $d K r $.  $d K s $.  $d L s $.  $d M l $.
      $d M r $.  $d N p $.  $d N q $.  $d N s $.  $d R l $.  $d R p $.
      $d R r $.  $d g ph s $.  $d l ph $.  $d p ph $.  $d ph r $.
      aks5lem2.1 $e |- ( ph -> M e. ( ( mulGrp ` K ) PrimRoots R ) ) $.
      aks5lem2.2 $e |- I = ( s e. ( Base ` A ) |-> U. ( ( H o. F ) " s ) ) $.
      aks5lem2.3 $e |- A = ( ( Poly1 ` ( Z/nZ ` N ) ) /s ( ( Poly1 `
       ( Z/nZ ` N ) ) ~QG L ) ) $.
      aks5lem2.4 $e |- L = ( ( RSpan ` ( Poly1 ` ( Z/nZ ` N ) ) ) `
       { ( ( R ( .g ` ( mulGrp ` ( Poly1 ` ( Z/nZ ` N ) ) ) )
        ( var1 ` ( Z/nZ ` N ) ) ) ( -g ` ( Poly1 ` ( Z/nZ ` N ) ) )
         ( 1r ` ( Poly1 ` ( Z/nZ ` N ) ) ) ) } ) $.
      aks5lem2.5 $e |- ( ph -> R e. NN ) $.
      $( Lemma for section 5 ~ https://www3.nd.edu/%7eandyp/notes/AKS.pdf.
         Construct the quotient for the AKS reduction.  (Contributed by
         metakunt, 7-Jun-2025.) $)
      aks5lem2 $p |- ( ph -> ( I e. ( A RingHom K ) /\
      A. g e. ( Base ` ( Poly1 ` ( Z/nZ ` N ) ) ) ( I ` [ g ] ( ( Poly1 `
       ( Z/nZ ` N ) ) ~QG L ) ) = ( ( H o. F ) ` g ) ) ) $=
        ( vl ccom czn cfv cpl1 ccnv c0g csn cima cv1 cmgp cmg cur csg eqid wcel
        co cbs wceq cv cdvds wbr cn0 wral cprimroots ccrg ccmn fldcrngd crngmgp
        wi w3a syl nnnn0d isprimroot mpbid simp1d mgpbas eqcomi eleqtrdi cprime
        aks5lem1 cn simp2d zncrng ply1crng cgrp crnggrpd cmnd crngringd ringmgp
        crg mulgnn0cld ringidcl grpsubcl syl3anc wfun cdm cvv wa czrh cuni cmpt
        vr1cl fvexd mptexd eqeltrid adantr vex coexd syl2anc cghm rhmghm ghmsub
        a1i crh fveq2d ffvelcdmd cvsca cascl cmulr ringlidmd csca ply1sca eqtrd
        eqcomd oveq1d casa ply1assa eleqtrd asclmul1 rhm1 cfield fmptd eleqtrrd
        ffund fdmd fvco cchr prmnn eqeltrrid nnzd eqbrtrrid zndvdchrrhm rhmply1
        simp3d ce1 evl1maprhm wf elexd clmod ply1lmod ascl1 rhmply1mon crngring
        rhmf ply1ascl1 fveq1d fvmptd evl1vard evl1expd simprd ringidval oveq12d
        simpr ringgrpd grpsubid rhmqusspan ) ABEHFUJZMUKULZUMULZJIUVPUNJUOULZUP
        UQZKDUVQURULZUVRUSULZUTULZVEZUVRVAULZUVRVBULZVEZUVSNUVSVCZACFGHJLMOPQRS
        TUAUBUCALJUSULZVFULZJVFULZALUWJVDZDLUWIUTULZVEZUWIUOULZVGZUIVHZLUWMVEUW
        OVGDUWQVIVJVRUIVKVLZALUWIDVMVEVDUWLUWPUWRVSUDAUWIUWMDLUIAJVNVDZUWIVOVDA
        JRVPZJUWIUWIVCZVQVTADUHWAZUWMVCZWBWCZWDUWKUWJUWKJUWIUXAUWKVCZWEWFWGZWIU
        VTVCUFUEAUVQVNVDZUVRVNVDAMVKVDUXGAMACWHVDZMWJVDZCMVIVJZTWKZWAMUVQUVQVCZ
        WLVTZUVRUVQUVRVCZWMVTZUGAUVRWNVDUWDUVRVFULZVDZUWEUXPVDZUWGUXPVDAUVRUXOW
        OAUXPUWCUWBDUWAUXPUVRUWBUWBVCZUXPVCZWEUWCVCZAUVRWSVDZUWBWPVDAUVRUXOWQZU
        VRUWBUXSWRVTUXBAUVQWSVDZUWAUXPVDAUVQUXMWQZUXPUVRUVQUWAUWAVCZUXNUXTXKVTW
        TZAUYBUXRUYCUXPUVRUWEUXTUWEVCZXAVTZUXPUVRUWFUWDUWEUXTUWFVCZXBXCZAUWGUVP
        ULZUWGFULZHULZUVSAFXDUWGFXEZVDUYLUYNVGAUXPXFFAQUXPGQVHZUJXFFAUYPUXPVDZX
        GZGUYPXFXFAGXFVDUYQAGPUVQVFULZJXHULPVHUQXIZXJXFUBAPUYSUYTXFAUVQVFXLXMXN
        XOUYPXFVDUYRQXPYBXQUAUUAZUUCAUWGUXPUYOUYKAUXPXFFVUAUUDUUBUWGHFUUEXRAUYN
        UWDFULZUWEFULZJUMULZVBULZVEZHULZUVSAUYMVUFHAFUVRVUDXSVEVDZUXQUXRUYMVUFV
        GAFUVRVUDYCVEVDZVUHAUXPUVRVUDUVQJFGQUXNVUDVCZUXTUAAPJGMUVQAJUWTWQZUXKAJ
        UUFULZAVULCWJSAUXHCWJVDAUXHUXIUXJTWDCUUGVTUUHUUIAVULCMVISAUXHUXIUXJTUUM
        UUJUXLUBUUKZUULZUVRVUDFXTVTUYGUYIUXPUVRVUDUWDFUWFVUEUWEUXTUYJVUEVCZYAXC
        YDAVUGVUBHULZVUCHULZJVBULZVEZUVSAHVUDJXSVEVDZVUBVUDVFULZVDVUCVVAVDVUGVU
        SVGAHVUDJYCVEVDZVUTAUWKVUDJVVAHJUUNULZLOVVCVCZVUJUXEVVAVCZUWTUXFUCUUOZV
        UDJHXTVTAUXPVVAUWDFAVUIUXPVVAFUUPVUNUXPVVAUVRVUDFUXTVVEUVCVTZUYGYEAUXPV
        VAUWEFVVGUYIYEVVAVUDJVUBHVUEVURVUCVVEVUOVURVCZYAXCAVUSJVAULZVVIVURVEZUV
        SAVUPVVIVUQVVIVURAVUPVUDVAULZHULZVVIAVUPVVIVVLAVUPUVQVAULZGULZDJURULZVU
        DUSULZUTULZVEZVUDYFULZVEZHULZVVIAVUBVVTHAVUBVVMUWDUVRYFULZVEZFULVVTAUWD
        VWCFAUWDVVMUVRYGULZULZUWDUVRYHULZVEZVWCAUWDUWEUWDVWFVEZVWGAVWHUWDAUXPUV
        RVWFUWEUWDUXTVWFVCZUYHUYCUYGYIYMAUWEVWEUWDVWFAVWEUWEAVWEUVRYJULZVAULZVW
        DULUWEAVVMVWKVWDAUVQVWJVAAUVQXFVDUVQVWJVGAUVQVNUXMUUQUVRUVQXFUXNYKVTZYD
        YDAVWDVWJUVRVWDVCZVWJVCZAUYDUVRUURVDUYEUVRUVQUXNUUSVTUYCUUTYLYMYNYLAUVR
        YOVDZVVMVWJVFULZVDUXQVWGVWCVGAUXGVWOUXMUVRUVQUXNYPVTAVVMUYSVWPAUYDVVMUY
        SVDUYEUYSUVQVVMUYSVCZVVMVCZXAVTZAUVQVWJVFVWLYDYQUYGVWDVVMVWBVWFVWJVWPUX
        PUVRUWDVWMVWNVWPVCUXTVWIVWBVCZYRXCYLYDAUXPVVMUVRVUDUVQJVVSVWBDUWCFGUYSU
        WBVVQVVPUWAVVOQUXNVUJUXTVWQUAUYFVVOVCZVWTVVSVCZUXSVVPVCZUYAVVQVCZVUMVWS
        UXBUVAYLYDAVWAVVIVVRVVSVEZHULZVVIAVVTVXEHAVVNVVIVVRVVSAGUVQJYCVEVDVVNVV
        IVGVUMUVQJVVMGVVIVWRVVIVCZYSVTYNYDAVXFVVIVUDYGULZULZVVRVUDYHULZVEZHULZV
        VIAVXEVXKHAVXKVXEAVUDYOVDZVVIVUDYJULZVFULZVDVVRVVAVDZVXKVXEVGAUWSVXMUWT
        VUDJVUJYPVTAVVIUWKVXOAJWSVDZVVIUWKVDZVUKUWKJVVIUXEVXGXAVTZAJVXNVFAJYTVD
        JVXNVGRVUDJYTVUJYKVTYDYQAVVAVVQVVPDVVOVVAVUDVVPVXCVVEWEVXDAVUDWSVDZVVPW
        PVDAVUDVNVDZVXTAUWSVYAUWTVUDJVUJWMVTVUDUVBVTZVUDVVPVXCWRVTUXBAVXQVVOVVA
        VDVUKVVAVUDJVVOVXAVUJVVEXKVTWTZVXHVVIVVSVXJVXNVXOVVAVUDVVRVXHVCZVXNVCVX
        OVCVVEVXJVCZVXBYRXCYMYDAVXLVVKVVRVXJVEZHULZVVIAVXKVYFHAVXIVVKVVRVXJAVXH
        JVVKVVIVUDVUJVYDVXGVVKVCZVUKUVDYNYDAVYGVVRHULZVVIAVYFVVRHAVVAVUDVXJVVKV
        VRVVEVYEVYHVYBVYCYIYDAVYILVVRVVCULZULZVVIAOVVRLOVHZVVCULZULZVYKVVAHXFHO
        VVAVYNXJVGAUCYBAVYLVVRVGZXGZLVYMVYJVYPVYLVVRVVCAVYOUVLYDUVEVYCALVYJXLUV
        FAVYKUWNVVIAVXPVYKUWNVGAUWKVUDJVVQVVAUWMVVODVVCLLVVDVUJUXEVVEUWTUXFAUWK
        VUDJVVAVVCVVOLVVDVXAUXEVUJVVEUWTUXFUVGVXDUXCUXBUVHUVIAUWNUWOVVIAUWLUWPU
        WRUXDWKUWOVVIVGAVVIUWOJVVIUWIUXAVXGUVJWFYBYLYLYLYLYLYLYLYLAVVLVVIAVVBVV
        LVVIVGVVFVUDJVVKHVVIVYHVXGYSVTZYMYLVYQYLAVUQVVLVVIAVUCVVKHAVUIVUCVVKVGV
        UNUVRVUDUWEFVVKUYHVYHYSVTYDVYQYLUVKAJWNVDVXRVVJUVSVGAJVUKUVMVXSUWKJVURV
        VIUVSUXEUWHVVHUVNXRYLYLYLYLUVO $.
    $}
  $}

  ${
    ply1asclzrhval.1 $e |- W = ( Poly1 ` R ) $.
    ply1asclzrhval.2 $e |- A = ( algSc ` W ) $.
    ply1asclzrhval.3 $e |- B = ( ZRHom ` W ) $.
    ply1asclzrhval.4 $e |- C = ( ZRHom ` R ) $.
    ply1asclzrhval.5 $e |- ( ph -> R e. CRing ) $.
    ply1asclzrhval.6 $e |- ( ph -> X e. ZZ ) $.
    $( Transfer results from algebraic scalars and ZR ring homomorphisms.
       (Contributed by metakunt, 17-Jun-2025.) $)
    ply1asclzrhval $p |- ( ph -> ( A ` ( C ` X ) ) = ( B ` X ) ) $=
      ( cfv crh co casa wcel eqid syl csca cpl1 ccrg ply1assa eqeltrid crg wceq
      asclrhm crngringd ply1sca eqcomd oveq1d eleqtrd rhmzrhval ) AEFBDCGABFUAN
      ZFOPZEFOPAFQRBUPRAFEUBNZQHAEUCRUQQRLUQEUQSUDTUEBUOFIUOSUHTAUOEFOAEUOAEUFR
      EUOUGAELUIFEUFHUJTUKULUMMKJUN $.
  $}

  ${
    aks5lema.1 $e |- ( ph -> K e. Field ) $.
    aks5lema.2 $e |- P = ( chr ` K ) $.
    aks5lema.3 $e |- ( ph -> ( P e. Prime /\ N e. NN /\ P || N ) ) $.
    aks5lema.9 $e |- B = ( S /s ( S ~QG L ) ) $.
    aks5lema.10 $e |- L = ( ( RSpan ` S ) ` { ( ( R ( .g ` ( mulGrp ` S ) )
      ( var1 ` ( Z/nZ ` N ) ) ) ( -g ` S ) ( 1r ` S ) ) } ) $.
    aks5lema.11 $e |- ( ph -> R e. NN ) $.
    aks5lema.14 $e |- .~ = { <. e , f >. | ( e e. NN /\ f e.
     ( Base ` ( Poly1 ` K ) ) /\ A. y e. ( ( mulGrp ` K ) PrimRoots R )
     ( e ( .g ` ( mulGrp ` K ) ) ( ( ( eval1 ` K ) ` f ) ` y ) ) =
     ( ( ( eval1 ` K ) ` f ) ` ( e ( .g ` ( mulGrp ` K ) ) y ) ) ) } $.
    aks5lema.15 $e |- S = ( Poly1 ` ( Z/nZ ` N ) ) $.
    $( Lemma for AKS, section 5, connect to Theorem 6.1.  (Contributed by
       metakunt, 17-Jun-2025.) $)
    ${
      $d A r $.  $d A s u $.  $d F r $.  $d F s u $.  $d G p $.  $d H s u $.
      $d I s u $.  $d K d $.  $d K p $.  $d K q $.  $d K r $.  $d K s $.
      $d L s u $.  $d M d $.  $d M r $.  $d N p $.  $d N q $.  $d N r $.
      $d N s u $.  $d R d $.  $d R p $.  $d R r $.  $d d ph $.  $d p ph $.
      $d ph r $.  $d ph s u $.  $d B s $.
      aks5lem3a.4 $e |- F = ( p e. ( Base ` ( Poly1 ` ( Z/nZ ` N ) ) ) |->
      ( G o. p ) ) $.
      aks5lem3a.5 $e |- G = ( q e. ( Base ` ( Z/nZ ` N ) ) |->
      U. ( ( ZRHom ` K ) " q ) ) $.
      aks5lem3a.6 $e |- H = ( r e. ( Base ` ( Poly1 ` K ) ) |->
       ( ( ( eval1 ` K ) ` r ) ` M ) ) $.
      aks5lem3a.7 $e |- ( ph -> M e. ( ( mulGrp ` K ) PrimRoots R ) ) $.
      aks5lem3a.8 $e |- I = ( s e. ( Base ` B ) |-> U. ( ( H o. F ) " s ) ) $.
      aks5lem3a.12 $e |- ( ph -> A e. ZZ ) $.
      aks5lem3a.13 $e |- ( ph -> [ ( N ( .g ` ( mulGrp ` S ) )
       ( ( var1 ` ( Z/nZ ` N ) ) ( +g ` S ) ( ( algSc ` S ) `
      ( ( ZRHom ` ( Z/nZ ` N ) ) ` A ) ) ) ) ] ( S ~QG L )
         = [ ( ( N ( .g ` ( mulGrp ` S ) ) ( var1 `
         ( Z/nZ ` N ) ) ) ( +g ` S ) ( ( algSc ` S ) `
          ( ( ZRHom ` ( Z/nZ ` N ) ) ` A ) )
     ) ] ( S ~QG L ) ) $.
      $( Lemma for AKS section 5.  (Contributed by metakunt, 17-Jun-2025.) $)
      aks5lem3a $p |- ( ph -> ( N ( .g ` ( mulGrp ` K ) ) ( ( ( eval1 ` K )
      ` ( ( var1 ` K ) ( +g ` ( Poly1 ` K ) ) ( ( algSc ` ( Poly1 ` K ) )
     ` ( ( ZRHom ` K ) ` A ) ) ) ) ` M ) ) = ( ( ( eval1 ` K ) ` ( ( var1 ` K )
      ( +g ` ( Poly1 ` K ) ) ( ( algSc ` ( Poly1 ` K ) ) `
       ( ( ZRHom ` K ) ` A ) ) ) ) ` ( N ( .g ` ( mulGrp ` K ) ) M ) ) ) $=
        ( vd cv1 cfv czrh cpl1 cascl cplusg cmgp cmg cmhm wcel cn0 cbs wceq crh
        vu co cv cdvds wbr wi wral ccrg eqid nnnn0d simp1d mgpbas eqcomi rhmmhm
        syl cn crg ply1crng crngringd ply1asclzrhval cz wf czring zringbas rhmf
        zrhrhm ffvelcdmd grpcld mhmmulg syl3anc a1i fvco3d cvv wa fveq2d fveq1d
        simpr fvexd fvmptd ghmlin eqtrd eqtr4d oveq12d oveq2d cqg eceq1 eqeq12d
        eqtr2d cec fveq2 cqus cur csg csn crsp fveq2i simprd mulgnn0cld rspcdva
        eqtri eqcomd eqidd oveq123d eceq1d eceq2d 3eqtrd evl1vard evl1addd ccom
        ce1 czn c0g cprimroots ccmn fldcrngd isprimroot mpbid eleqtrdi aks5lem1
        crngmgp cprime simp2d cgrp zncrng ringgrp vr1cl eqeltrd cchr prmnn nnzd
        eqeltrid simp3d eqbrtrd zndvdchrrhm rhmply1 cmpt cghm rhmghm rhmply1vr1
        w3a rhmzrhval oveq1i oveq12i oveqi oveq123i sneqi fveq12i aks5lem2 cmnd
        ringmgp oveq1d eqcom imbi2i mpbi oveqd evl1expd jca evl1scad cmnmndd )
        ARQOUSUTZCOVAUTZUTZOVBUTZVCUTZUTZUWOVDUTZVNZOUUBUTZUTZUTZOVEUTZVFUTZVNZ
        RRUUCUTZUSUTZCUXFVAUTZUTZUXFVBUTZVCUTZUTZUXJVDUTZVNZUXJVEUTZVFUTZVNZMKU
        UAZUTZRUXGUXPVNZUXLUXMVNZUXRUTZRQUXDVNZUXAUTZAUXSRUXNUXRUTZUXDVNZUXEAUX
        RUXOUXCVGVNVHZRVIVHZUXNUXJVJUTZVHUXSUYFVKAUXRUXJOVLVNVHUYGAEKLMOQRTUAUB
        UCUDUEUKULUMAQUXCVJUTZOVJUTZAQUYJVHZGQUXDVNUXCUUDUTZVKZURVOZQUXDVNUYMVK
        GUYOVPVQVRURVIVSZAQUXCGUUEVNVHUYLUYNUYPUVLUNAUXCUXDGQURAOVTVHZUXCUUFVHA
        OUCUUGZOUXCUXCWAZUULWGZAGUHWBUXDWAZUUHUUIWCUYKUYJUYKOUXCUYSUYKWAZWDZWEU
        UJZUUKUXJOUXRUXOUXCUXOWAZUYSWFWGARAEUUMVHZRWHVHZERVPVQZUEUUNZWBZAUYIUXM
        UXJUXGUXLUYIWAZUXMWAZAUXJWIVHZUXJUUOVHAUXJAUXFVTVHZUXJVTVHAUYHVUNVUJRUX
        FUXFWAZUUPWGZUXJUXFUXJWAZWJWGWKZUXJUUQWGZAUXFWIVHUXGUYIVHZAUXFVUPWKUYIU
        XJUXFUXGUXGWAZVUQVUKUURWGZAUXLCUXJVAUTZUTZUYIAUXKVVCUXHUXFUXJCVUQUXKWAV
        VCWAZUXHWAVUPUPWLZAWMUYICVVCAVUMWMUYIVVCWNZVURVUMVVCWOUXJVLVNVHVVGUXJVV
        CVVEWRWMUYIWOUXJVVCWPVUKWQWGWGUPWSUUSZWTZUYIUXPUXDUXRUXOUXCRUXNUYIUXJUX
        OVUEVUKWDZUXPWAZVUAXAXBAUYEUXBRUXDAUYEUXNKUTZMUTZUXBAUYIUWOVJUTZUXNMKAK
        UXJUWOVLVNVHZUYIVVNKWNAUYIUXJUWOUXFOKLUBVUQUWOWAZVUKUKAUAOLRUXFAOUYRWKZ
        VUIAOUUTUTZEWMEVVRUDWEZAEAVUFEWHVHAVUFVUGVUHUEWCEUVAWGUVBUVCAVVRERVPVVR
        EVKAVVSXCAVUFVUGVUHUEUVDUVEVUOULUVFZUVGZUYIVVNUXJUWOKVUKVVNWAZWQWGZVVIX
        DAVVMQVVLUWTUTZUTZUXBATVVLQTVOZUWTUTZUTZVWEVVNMXEMTVVNVWHUVHVKAUMXCZAVW
        FVVLVKZXFZQVWGVWDVWKVWFVVLUWTAVWJXIXGXHAUYIVVNUXNKVWCVVIWSAQVWDXJXKAQVW
        DUXAAVVLUWSUWTAVVLUXGKUTZUXLKUTZUWRVNZUWSAKUXJUWOUVIVNVHZVUTUXLUYIVHZVV
        LVWNVKAVVOVWOVWAUXJUWOKUVJWGZVVBVVHUXMUWRUXJUWOUXGKUXLUYIVUKVULUWRWAZXL
        XBAVWLUWLVWMUWQUWRAUYIUXJUWOUXFOKLUXGUWLUBVUQVVPVUKUKVVAUWLWAZVVTUVKZAV
        WMCUWOVAUTZUTZUWQAVWMVVDKUTZVXBAUXLVVDKVVFXGZAUXJUWOKVVCVXACVWAUPVVEVXA
        WAZUVMZXMAUWPVXAUWMOUWOCVVPUWPWAZVXEUWMWAZUYRUPWLZXNXOXMXGXHXMXMXPXTAUX
        SUXQUXJPXQVNZYAZNUTZUYAVXJYAZNUTZUYBAVXLUXSAVMVOZVXJYAZNUTZVXOUXRUTZVKZ
        VXLUXSVKVMUYIUXQVXOUXQVKZVXQVXLVXRUXSVXTVXPVXKNVXOUXQVXJXRXGVXOUXQUXRYB
        XSANDOVLVNVHVXSVMUYIVSADEGVMKLMNOPQRSTUAUBUCUDUEUKULUMUNUODHHPXQVNZYCVN
        UXJVXJYCVNUFHUXJVYAVXJYCUJHUXJPXQUJUVNUVOYLPGUXGHVEUTZVFUTZVNZHYDUTZHYE
        UTZVNZYFZHYGUTZUTGUXGUXPVNZUXJYDUTZUXJYEUTZVNZYFZUXJYGUTZUTUGVYHVYNVYIV
        YOHUXJYGUJYHVYGVYMVYDVYEVYJVYKVYFVYLVYCUXPGUXGVYBUXOVFHUXJVEUJYHYHUVPHU
        XJYDUJYHHUXJYEUJYHUVQUVRUVSYLUHUVTYIZAUYIUXPUXORUXNVVJVVKAVUMUXOUWAVHVU
        RUXJUXOVUEUWBWGZVUJVVIYJYKYMAVXKVXMNAVXKRUXGUXIHVCUTZUTZHVDUTZVNZVYCVNZ
        VYAYAZRUXGVYCVNZVYSVYTVNZVYAYAZVXMAVXKWUBVXJYAWUCAUXQWUBVXJARRUXNWUAUXP
        VYCAUXOVYBVFAUXJHVEUXJHVKZAHUXJUJWEXCZXGXGARYNAUXGUXGUXLVYSUXMVYTAUXJHV
        DWUHXGAUXGYNAUXIUXKVYRAUXJHVCWUHXGXHYOYOYPAVXJVYAWUBAUXJHPXQWUHUWCZYQXM
        UQAWUFUYAVYAYAVXMAWUEUYAVYAAWUDUXTVYSUXLVYTUXMAHUXJVDAWUGVRAHUXJVKZVRWU
        HWUGWUJAUXJHUWDUWEUWFZXGAVYCUXPRUXGAVYBUXOVFAHUXJVEWUKXGXGUWGAUXIVYRUXK
        AHUXJVCWUKXGXHYOYPAVYAVXJUYAAVXJVYAWUIYMYQXMYRXGAVXSVXNUYBVKVMUYIUYAVXO
        UYAVKZVXQVXNVXRUYBWULVXPVXMNVXOUYAVXJXRXGVXOUYAUXRYBXSVYPAUYIUXMUXJUXTU
        XLVUKVULVUSAUYIUXPUXORUXGVVJVVKVYQVUJVVBYJZVVHWTZYKYRAUYBUYAKUTZMUTZUYD
        AUYIVVNUYAMKVWCWUNXDAWUPQWUOUWTUTZUTZUYDATWUOVWHWURVVNMXEVWIAVWFWUOVKZX
        FZQVWGWUQWUTVWFWUOUWTAWUSXIXGXHAUYIVVNUYAKVWCWUNWSAQWUQXJXKAWURQUXTKUTZ
        VWMUWRVNZUWTUTZUTZUYDAQWUQWVCAWUOWVBUWTAVWOUXTUYIVHVWPWUOWVBVKVWQWUMVVH
        UXMUWRUXJUWOUXTKUXLUYIVUKVULVWRXLXBXGXHAWVDQRVWLUWOVEUTZVFUTZVNZVXCUWRV
        NZUWTUTZUTZUYDAQWVCWVIAWVBWVHUWTAWVAWVGVWMVXCUWRAKUXOWVEVGVNVHZUYHVUTWV
        AWVGVKAVVOWVKVWAUXJUWOKUXOWVEVUEWVEWAWFWGVUJVVBUYIUXPWVFKUXOWVERUXGVVJV
        VKWVFWAZXAXBVXDXOXGXHAWVJUYCUWNOVDUTZVNZUYDAWVJQRUWLWVFVNZVXBUWRVNZUWTU
        TZUTZWVNAQWVIWVQAWVHWVPUWTAWVGWVOVXCVXBUWRAVWLUWLRWVFVWTXPVXFXOXGXHAWVR
        UYCQVXBUWTUTZUTZWVMVNZWVNAWVPVVNVHWVRWWAVKAUYKUWOWVMUWROVVNWVOVXBUWTUYC
        WVTQUWTWAZVVPVUBVWBUYRVUDAUYKUWOOWVFVVNUXDUWLRUWTQQWWBVVPVUBVWBUYRVUDAU
        YKUWOOVVNUWTUWLQWWBVWSVUBVVPVWBUYRVUDYSWVLVUAVUJUWHAVXBVVNVHWVTWVTVKAWM
        VVNCVXAAUWOWIVHZWMVVNVXAWNZAUWOAUYQUWOVTVHUYRUWOOVVPWJWGWKWWCVXAWOUWOVL
        VNVHWWDUWOVXAVXEWRWMVVNWOUWOVXAWPVWBWQWGWGUPWSAWVTYNUWIVWRWVMWAZYTYIAWV
        TUWNUYCWVMAUWNQUWQUWTUTZUTZWVTAWWGUWNAUWQVVNVHWWGUWNVKAUWPUYKUWOOVVNUWT
        UWNQWWBVVPVUBVXGVWBUYRAWMUYKCUWMAOWIVHZWMUYKUWMWNZVVQWWHUWMWOOVLVNVHWWI
        OUWMVXHWRWMUYKWOOUWMWPVUBWQWGWGUPWSZVUDUWJYIYMAQWWFWVSAUWQVXBUWTVXIXGXH
        XTXPXMXMAUWSVVNVHUYDWVNVKAUYKUWOWVMUWROVVNUWLUWQUWTUYCUWNUYCWWBVVPVUBVW
        BUYRAUYKUXDUXCRQVUCVUAAUXCUYTUWKVUJVUDYJZAUYKUWOOVVNUWTUWLUYCWWBVWSVUBV
        VPVWBUYRWWKYSAUWPUYKUWOOVVNUWTUWNUYCWWBVVPVUBVXGVWBUYRWWJWWKUWJVWRWWEYT
        YIXNXMXMXMXMYR $.
    $}

    ${
      $d A c d $.  $d B d e $.  $d K a b c d e $.  $d L d $.  $d M c d e $.
      $d N a b c d e $.  $d R b c $.  $d b c d ph $.
      aks5lem4a.7 $e |- ( ph -> M e. ( ( mulGrp ` K ) PrimRoots R ) ) $.
      aks5lem4a.12 $e |- ( ph -> A e. ZZ ) $.
      aks5lem4a.13 $e |- ( ph -> [ ( N ( .g ` ( mulGrp ` S ) )
        ( ( var1 ` ( Z/nZ ` N ) ) ( +g ` S ) ( ( algSc ` S ) `
        ( ( ZRHom ` ( Z/nZ ` N ) ) ` A ) ) ) ) ] ( S ~QG L )
          = [ ( ( N ( .g ` ( mulGrp ` S ) ) ( var1 `
          ( Z/nZ ` N ) ) ) ( +g ` S ) ( ( algSc ` S ) `
            ( ( ZRHom ` ( Z/nZ ` N ) ) ` A ) )
      ) ] ( S ~QG L ) ) $.
      $( Lemma for AKS section 5, reduce hypotheses.  (Contributed by metakunt,
         17-Jun-2025.) $)
      aks5lem4a $p |- ( ph -> ( N ( .g ` ( mulGrp ` K ) ) ( ( ( eval1 ` K )
      ` ( ( var1 ` K ) ( +g ` ( Poly1 ` K ) ) ( ( algSc ` ( Poly1 ` K ) )
    ` ( ( ZRHom ` K ) ` A ) ) ) ) ` M ) ) = ( ( ( eval1 ` K ) ` ( ( var1 ` K )
      ( +g ` ( Poly1 ` K ) ) ( ( algSc ` ( Poly1 ` K ) ) `
      ( ( ZRHom ` K ) ` A ) ) ) ) ` ( N ( .g ` ( mulGrp ` K ) ) M ) ) ) $=
        ( vb va vc czn cfv cpl1 cbs czrh cima cuni cmpt ccom ce1 eqid nfcv wceq
        vd cv imaeq2 unieqd cbvmpt aks5lem3a ) ABCDEFGHIJUFNUIUJZUKUJULUJUGVHUL
        UJKUMUJUGVCUNUOUPZUFVCUQUPZVIUHKUKUJULUJMUHVCKURUJUJUJUPZIDULUJZVKVJUQZ
        IVCZUNZUOZUPKLMNVBUHUGUFOPQRSTUAUBVJUSVIUSVKUSUCIVBVLVPVMVBVCZUNZUOZVBV
        PUTIVSUTVNVQVAVOVRVNVQVMVDVEVFUDUEVG $.
    $}

    ${
      $d A y $.  $d B e $.  $d K e f y $.  $d L y $.  $d N e f y $.
      $d R e f $.  $d S y $.  $d a e f y $.  $d a ph y $.
      aks5lem5a.13 $e |- ( ph -> A. a e. ( 1 ... A ) [ ( N ( .g ` ( mulGrp `
    S ) ) ( ( var1 ` ( Z/nZ ` N ) ) ( +g ` S ) ( ( ZRHom ` S ) ` a ) ) ) ]
      ( S ~QG L ) = [ ( ( N ( .g ` ( mulGrp `
        S ) ) ( var1 ` ( Z/nZ ` N ) ) ) ( +g `
        S ) ( ( ZRHom ` S ) ` a )
       ) ] ( S ~QG L ) ) $.
      $( Lemma for AKS, section 5, connect to Theorem 6.1.  (Contributed by
         metakunt, 17-Jun-2025.) $)
      aks5lem5a $p |- ( ph -> A. a e. ( 1 ... A ) N .~ ( ( var1 ` K )
     ( +g ` ( Poly1 ` K ) )
     ( ( algSc ` ( Poly1 ` K ) ) ` ( ( ZRHom ` K ) ` a ) ) ) ) $=
        ( czn cfv cv1 cv czrh cplusg co cmgp cmg cqg cec wceq c1 cfz wral cascl
        cpl1 wbr wcel wa ce1 cprimroots cfield ad3antrrr cprime cdvds w3a simpr
        elfzelz adantl adantr eqid cn0 ccrg simp2d nnnn0d zncrng ply1asclzrhval
        cn syl oveq2d eceq1d eqcomd 3eqtrd aks5lem4a ralrimiva cbs fldcrngd crg
        cz ply1crng crngring ringgrpd crngringd vr1cl czring wf zrhrhm zringbas
        crh rhmf ffvelcdmd grpcld eqeltrd aks6d1c1p1 mpbird ex ralimdva mpd ) A
        MMUDUEZUFUEZNUGZHUHUEZUEZHUIUEZUJZHUKUEULUEZUJZHLUMUJZUNZMXNXTUJZXQXRUJ
        ZYBUNZUOZNUPCUQUJZURMKUFUEZXOKUHUEZUEKUTUEZUSUEZUEZYKUIUEZUJZFVAZNYHURU
        CAYGYPNYHAXOYHVBZVCZYGYPYRYGVCZYPMBUGZYOKVDUEZUEZUEKUKUEZULUEZUJMYTUUDU
        JUUBUEUOZBUUCGVEUJZURYSUUEBUUFYSYTUUFVBZVCBXODEFGHIJKLYTMAKVFVBYQYGUUGO
        VGPAEVHVBZMWBVBZEMVIVAZVJYQYGUUGQVGRSAGWBVBYQYGUUGTVGUAUBYSUUGVKYSXOWMV
        BZUUGYRUUKYGYQUUKAXOUPCVLVMZVNVNYSMXNXOXMUHUEZUEHUSUEZUEZXRUJZXTUJZYBUN
        ZYDUUOXRUJZYBUNZUOUUGYSUURYCYFUUTYRUURYCUOYGYRUUQYAYBYRUUPXSMXTYRUUOXQX
        NXRYRUUNXPUUMXMHXOUBUUNVOXPVOUUMVOYRMVPVBXMVQVBYRMAUUIYQAUUHUUIUUJQVRVN
        ZVSMXMXMVOVTWCUULWAZWDWDWEVNYRYGVKYRYFUUTUOYGYRYEUUSYBYRXQUUOYDXRYRUUOX
        QUVBWFWDWEVNWGVNWHWIYSBYKWJUEZUUDFGIJMUUDYOUUCUUAUAYRYOUVCVBYGYRYOYIXOY
        KUHUEZUEZYNUJUVCYRYMUVEYIYNYRYLUVDYJKYKXOYKVOZYLVOUVDVOZYJVOAKVQVBZYQAK
        OWKZVNZUULWAWDYRUVCYNYKYIUVEUVCVOZYNVOYRYKYRYKVQVBZYKWLVBZAUVLYQAUVHUVL
        UVIYKKUVFWNWCVNYKWOWCZWPYRKWLVBYIUVCVBYRKUVJWQUVCYKKYIYIVOUVFUVKWRWCYRW
        MUVCXOUVDYRUVDWSYKXCUJVBZWMUVCUVDWTYRUVMUVOUVNYKUVDUVGXAWCWMUVCWSYKUVDX
        BUVKXDWCUULXEXFXGVNYRUUIYGUVAVNXHXIXJXKXL $.
    $}
  $}

  ${
    $d .~ a $.  $d A a e f y $.  $d A b $.  $d A x y $.  $d K a e f y $.
    $d K b $.  $d K x y $.  $d L e y $.  $d M a y $.  $d M b $.  $d M x y $.
    $d N a e f y $.  $d N b $.  $d N x y $.  $d P a e f y $.  $d P b $.
    $d P x y $.  $d R a e f y $.  $d R x y $.  $d S e y $.  $d a ph y $.
    $d b ph $.  $d ph x y $.
    aks5lem6.1 $e |- .~ = { <. e , f >. | ( e e. NN /\ f e.
     ( Base ` ( Poly1 ` K ) ) /\ A. y e. ( ( mulGrp ` K ) PrimRoots R )
     ( e ( .g ` ( mulGrp ` K ) ) ( ( ( eval1 ` K ) ` f ) ` y ) ) =
     ( ( ( eval1 ` K ) ` f ) ` ( e ( .g ` ( mulGrp ` K ) ) y ) ) ) } $.
    aks5lem6.2 $e |- P = ( chr ` K ) $.
    aks5lem6.3 $e |- ( ph -> K e. Field ) $.
    aks5lem6.4 $e |- ( ph -> P e. Prime ) $.
    aks5lem6.5 $e |- ( ph -> R e. NN ) $.
    aks5lem6.6 $e |- ( ph -> N e. ( ZZ>= ` 3 ) ) $.
    aks5lem6.7 $e |- ( ph -> P || N ) $.
    aks5lem6.8 $e |- ( ph -> ( N gcd R ) = 1 ) $.
    aks5lem6.9 $e |- A = ( |_ ` ( ( sqrt ` ( phi ` R ) ) x.
     ( 2 logb N ) ) ) $.
    aks5lem6.10 $e |- ( ph -> ( ( 2 logb N ) ^ 2 ) <
     ( ( odZ ` R ) ` N ) ) $.
    aks5lem6.11 $e |- ( ph -> ( x e. ( Base ` K ) |->
     ( P ( .g ` ( mulGrp ` K ) ) x ) ) e. ( K RingIso K ) ) $.
    aks5lem6.12 $e |- ( ph -> M e. ( ( mulGrp ` K ) PrimRoots R ) ) $.
    aks5lem6.13 $e |- ( ph -> A. b e. ( 1 ... A ) ( b gcd N ) = 1 ) $.
    aks5lem6.14 $e |- S = ( Poly1 ` ( Z/nZ ` N ) ) $.
    aks5lem6.15 $e |- L = ( ( RSpan ` S ) ` { ( ( R ( .g ` ( mulGrp ` S ) )
      ( var1 ` ( Z/nZ ` N ) ) ) ( -g ` S ) ( 1r ` S ) ) } ) $.
    aks5lem6.16 $e |- X = ( var1 ` ( Z/nZ ` N ) ) $.
    aks5lem6.17 $e |- ( ph -> A. a e. ( 1 ... A ) [ ( N ( .g ` ( mulGrp `
    S ) ) ( X ( +g ` S ) ( ( ZRHom ` S ) ` a ) ) ) ]
      ( S ~QG L ) = [ ( ( N ( .g ` ( mulGrp ` S ) ) X ) ( +g ` S )
       ( ( ZRHom ` S ) ` a ) ) ] ( S ~QG L ) ) $.
    $( Connect results of section 5 and Theorem 6.1 AKS. (Contributed by
       metakunt, 25-Jun-2025.) $)
    aks5lem6 $p |- ( ph -> N = ( P ^ ( P pCnt N ) ) ) $=
      ( cqg co cqus cprime wcel cn cdvds wbr cz cc0 clt wa cuz cfv eluzelz 0red
      c3 syl cr 3re a1i zred 3pos cle eluzle ltletrd jca elnnz sylibr 3jca eqid
      cv czrh cplusg cmgp cmg cec wceq c1 cfz wral czn cv1 eqcomi oveq1d oveq2d
      eceq1d simpr wi eqcom imbi2i mpbi 3eqtrd ralimdva mpd aks5lem5a aks6d1c7
      ex ) ABCDEFGIJKMNPQRSTUAUBUCUDUEUFUGUHUIUJACDHHLUOUPZUQUPZEFGHIJKLNPTSAEU
      RUSNUTUSZENVAVBUAANVCUSZVDNVEVBZVFXOAXPXQANVKVGVHUSZXPUCVKNVIVLZAVDVKNAVJ
      VKVMUSAVNVOANXSVPVDVKVEVBAVQVOAXRVKNVRVBUCVKNVSVLVTWANWBWCUDWDXNWEULUBRUK
      ANOPWFZHWGVHVHZHWHVHZUPZHWIVHWJVHZUPZXMWKZNOYDUPZYAYBUPZXMWKZWLZPWMDWNUPZ
      WONNWPVHWQVHZYAYBUPZYDUPZXMWKZNYLYDUPZYAYBUPZXMWKZWLZPYKWOUNAYJYSPYKAXTYK
      USVFZYJYSYTYJVFZYOYFYIYRUUAYNYEXMUUAYMYCNYDUUAYLOYAYBYLOWLZUUAOYLUMWRVOZW
      SWTXAYTYJXBUUAYHYQXMUUAYGYPYAYBUUAOYLNYDUUAUUBXCUUAOYLWLZXCUUCUUBUUDUUAYL
      OXDXEXFWTWSXAXGXLXHXIXJXK $.
  $}

  ${
    $d ph x y $.  $d ch x $.  $d th x $.  $d ps y $.  $d A x $.
    indstrd.1 $e |- ( x = y -> ( ps <-> ch ) ) $.
    indstrd.2 $e |- ( x = A -> ( ps <-> th ) ) $.
    indstrd.3 $e |- ( ( ph /\ x e. NN /\
     A. y e. NN ( y < x -> ch ) ) -> ps ) $.
    indstrd.4 $e |- ( ph -> A e. NN ) $.
    $( Strong induction, deduction version.  (Contributed by Steven Nguyen,
       13-Jul-2025.) $)
    indstrd $p |- ( ph -> th ) $=
      ( cn wcel cv wi wceq wb eleq1 imbi12d wral adantl weq imbi2d bi2.04 bitri
      clt wbr ralbii r19.21v 3com12 3exp a2d biimtrid indstr com12 vtocld mpd )
      AGLMZDKAENZLMZBOZURDOZEGLKUSGPZVAVBQAVCUTURBDUSGLRISUAUTABABOZACOZEFEFUBB
      CAHUCFNUSUFUGZVEOZFLTZAVFCOZFLTZOZUTVDVHAVIOZFLTVKVGVLFLVFACUDUHAVIFLUIUE
      UTAVJBUTAVJBAUTVJBJUJUKULUMUNUOUPUQ $.
  $}

  ${
    $d .^ d l y $.  $d .^ l x y $.  $d B d l y $.  $d B i k w x $.
    $d G d l y $.  $d G i k m $.  $d G i k w x $.  $d N c d l $.  $d N i k m $.
    $d N i k x $.  $d N d l y $.  $d d l ph y $.  $d i k ph $.  $d k l m y $.
    grpods.1 $e |- B = ( Base ` G ) $.
    grpods.2 $e |- .^ = ( .g ` G ) $.
    grpods.3 $e |- ( ph -> G e. Grp ) $.
    grpods.4 $e |- ( ph -> B e. Fin ) $.
    grpods.5 $e |- ( ph -> N e. NN ) $.
    $( Relate sums of elements of orders and roots of unity.  (Contributed by
       metakunt, 14-Jul-2025.) $)
    grpods $p |- ( ph -> sum_ k e. { m e. ( 1 ... N ) | m || N }
    ( # ` { x e. B | ( ( od ` G ) ` x ) = k } ) =
    ( # ` { x e. B | ( N .^ x ) = ( 0g ` G ) } ) ) $=
      ( cv co wceq wcel wa jca syl vy vl vc vd vi vw c0g cfv chash cdvds wbr c1
      crab cfz cod ciun csu oveq2 eqeq1d elrab bilani wi simprl simprr cmnd cn0
      simpl wb cgrp grpmnd cn nnnn0d eqid oddvdsnn0 syl3anc breq1 1zzd ad2antrr
      mpbird cz dvdszrcl simpld adantl cfn simplr odcl2 nnge1d cle simpr dvdsle
      imp syl2anc elfzd elrabd fveqeq2 eqidd eqeq2 rabbidv eliuni ex adantr mpd
      nnzd wrex eliun simplll elrabi simpll elfzelz divides mpbid oveq1 simplrr
      cmul eqcomd oveq2d oveq1d simplrl w3a odcl ad2antlr nn0zd 3jca odid mulgz
      mulgass eqtrd nfv cbvrexw r19.29a eleq2d impbid wss ssrab2 a1i ssfid wral
      c0 biimpi ralrimiva eqrdv fveq2d fzfid cin wo wdisj animorrl wn inrab wne
      rabn0 eqtr2 anbi12d necon1bi olcd pm2.61dan disjor sylibr hashiun eqtr2d
      ) AHBNZFOZGUGUHZPZBCUMZUIUHDENZHUJUKZEULHUNOZUMZUVAGUOUHZUHZDNZPZBCUMZUPZ
      UIUHUVIUVNUIUHDUQAUVEUVOUIAUAUVEUVOAUANZUVEQZUVPUVOQZAUVQUVRAUVQRUVPCQZHU
      VPFOZUVCPZRZUVRUVQUWBAUVDUWABUVPCUVAUVPPUVBUVTUVCUVAUVPHFURUSZUTVAAUWBUVR
      VBUVQAUWBUVRAUWBRZAUVSRZUVPUVJUHZHUJUKZRZUVRUWDUWEUWGUWDAUVSAUWBVGZAUVSUW
      AVCZSUWDUWGUWAAUVSUWAVDUWDGVEQZUVSHVFQUWGUWAVHUWDGVIQZUWKUWDAUWLUWIKTGVJT
      UWJUWDHUWDAHVKQZUWIMTVLUVPFGHUVJCUVCIUVJVMZJUVCVMZVNVOVSSUWHUWFUVIQUVPUVK
      UWFPZBCUMZQUVRUWHUVGUWGEUWFUVHUVFUWFHUJVPUWHUWFULHUWHVQUWHHAUWMUVSUWGMVRZ
      XCUWGUWFVTQZUWEUWGUWSHVTQZUWFHWAWBWCZUWHUWFUWHUWLCWDQZUVSUWFVKQAUWLUVSUWG
      KVRAUXBUVSUWGLVRAUVSUWGWEZUVPGUVJCIUWNWFVOWGUWHUWSUWMRZUWGUWFHWHUKZUWHUWS
      UWMUXAUWRSUWEUWGWIZUXDUWGUXEUWFHWJWKWLWMUXFWNUWHUWPUWFUWFPBUVPCUVAUVPUWFU
      VJWOUXCUWHUWFWPWNDUWFUVNUWQUVIUVPUVLUWFPUVMUWPBCUVLUWFUVKWQWRWSWLTWTXAXBW
      TAUVRUVQAUVRRUVPUVNQZDUVIXDZUVQUVRUXHADUVPUVIUVNXEVAAUXHUVQVBUVRAUXHUVQAU
      XHRZUVPUVKUBNZPZBCUMZQZUVQUBUVIUXIUXJUVIQZRZUXMRZAUXNRZUXMRZUVQUXPUXQUXMU
      XPAUXNAUXHUXNUXMXFUXIUXNUXMWESUXOUXMWISUXRUVDUWABUVPCUWCUXMUVSUXQUXKBUVPC
      XGWCUXRAUXJUVHQZUXJHUJUKZRZRZUVSUWFUXJPZRZRZUWAUXRUYBUYDUXRAUYAAUXNUXMXHU
      XQUYAUXMUXNUYAAUVGUXTEUXJUVHUVFUXJHUJVPUTVAXASUXMUYDUXQUXKUYCBUVPCUVAUVPU
      XJUVJWOUTVASUYEAUCNZUXJXNOZHPZUCVTXDZRZUYDRZUWAUYEUYJUYDUYEAUYIAUYAUYDXHU
      YBUYIUYDUYBUXTUYIAUXSUXTVDUYBUXJVTQZUWTUXTUYIVHUYAUYLAUXSUYLUXTUXJULHXIXA
      WCUYBHAUWMUYAMXAXCUCUXJHXJWLXKXASUYBUYDWISUYKUDNZUXJXNOZHPZUWAUDVTUYKUYMV
      TQZRZUYORUVTUYNUVPFOZUVCUYOUVTUYRPUYQUYOUYRUVTUYNHUVPFXLXOWCUYQUYRUVCPUYO
      UYQUYRUYMUWFXNOZUVPFOZUVCUYQUYNUYSUVPFUYQUYSUYNUYQUWFUXJUYMXNUYJUVSUYCUYP
      XMXPXOXQUYQUWEUYPRZUYTUVCPUYQUWEUYPUYQAUVSAUYIUYDUYPXFUYJUVSUYCUYPXRSUYKU
      YPWISVUAUYTUYMUWFUVPFOZFOZUVCVUAUWLUYPUWSUVSXSUYTVUCPAUWLUVSUYPKVRZVUAUYP
      UWSUVSUWEUYPWIZVUAUWFUVSUWFVFQAUYPUVPGUVJCIUWNXTYAYBAUVSUYPWEZYCCFGUYMUWF
      UVPIJYFWLVUAVUCUYMUVCFOZUVCVUAVUBUVCUYMFVUAUVSVUBUVCPVUFUVPFGUVJCUVCIUWNJ
      UWOYDTXPVUAUWLUYPVUGUVCPVUDVUECFGUYMUVCIJUWOYEWLYGYGTYGXAYGUYJUYOUDVTXDZU
      YDUYIVUHAUYHUYOUCUDVTUYHUDYHUYOUCYHUYFUYMPUYGUYNHUYFUYMUXJXNXLUSYIVAXAYJT
      TWNTUXHUXMUBUVIXDAUXGUXMDUBUVIUXGUBYHUXMDYHUVLUXJPZUVNUXLUVPVUIUVMUXKBCUV
      LUXJUVKWQWRYKYIVAYJWTXAXBWTYLUUAUUBADUVIUVNAUVHUVIAULHUUCUVIUVHYMAUVGEUVH
      YNYOYPAUVLUVIQZRZCUVNAUXBVUJLXAUVNCYMVUKUVMBCYNYOYPAUVLUENZPZUVNUVKVULPZB
      CUMZUUDZYRPZUUEZUEUVIYQZDUVIYQDUVIUVNUUFAVUSDUVIVUKVURUEUVIVUKVULUVIQRZVU
      MVURVUTVUMVUQUUGVUTVUMUUHZRVUQVUMVVAVUQVUTVVAVUPUVMVUNRZBCUMZYRVUPVVCPVVA
      UVMVUNBCUUIYOVUMVVCYRVVCYRUUJZVVBBCXDZVUMVVDVVEVVBBCUUKYSVVEUFNZUVJUHZUVL
      PZVVGVULPZRZVUMUFCVVJVUMVVEVVFCQRVVGUVLVULUULWCVVEVVJUFCXDVVBVVJBUFCVVBUF
      YHVVJBYHUVAVVFPUVMVVHVUNVVIUVAVVFUVLUVJWOUVAVVFVULUVJWOUUMYIYSYJTUUNYGWCU
      UOUUPYTYTUVIUVNVUODUEVUMUVMVUNBCUVLVULUVKWQWRUUQUURUUSUUT $.
  $}

  ${
    unitscyglem1.1 $e |- B = ( Base ` G ) $.
    unitscyglem1.2 $e |- .^ = ( .g ` G ) $.
    unitscyglem1.3 $e |- ( ph -> G e. Grp ) $.
    unitscyglem1.4 $e |- ( ph -> B e. Fin ) $.
    unitscyglem1.5 $e |- ( ph -> A. n e. NN ( # ` { x e. B | ( n .^ x )
     = ( 0g ` G ) } ) <_ n ) $.
    ${
      $d .^ i w y z $.  $d .^ n x $.  $d A i w y z $.  $d A n x $.
      $d B i w y $.  $d B n x $.  $d G i w y $.  $d G n x $.  $d i ph w y $.
      $d w x y $.
      unitscyglem1.6 $e |- ( ph -> A e. B ) $.
      $( Lemma for unitscyg .  (Contributed by metakunt, 13-Jul-2025.) $)
      unitscyglem1 $p |- ( ph -> ( # ` { x e. B |
      ( ( ( od ` G ) ` A ) .^ x ) = ( 0g ` G ) } ) = ( ( od ` G ) ` A ) ) $=
        ( cfv co wceq wa wcel cz adantr vi vy vz vw cod cv c0g chash cle wbr cn
        crab oveq1 eqeq1d rabbidv fveq2d id breq12d cgrp cfn eqid odcl2 syl3anc
        rspcdva cmpt crn cc0 cif dfod2 syl2anc wss simpr mulgcld fmpttd frn syl
        wf ssfid iftrued eqtrd cvv cbs fvexd eqeltrid rabexd wrex wb ovexd ffnd
        wfn fvelrnb biimpa wi eqcomd adantl simpll jca eqidd oveq1d fvmptd cmul
        oveq2 nnzd 3jca mulgass odid oveq2d mulgz eqtr2d simp2d mulgassr elrabd
        w3a sylan eqeltrd nfv fveqeq2 cbvrexw bilani r19.29a mpd hashss eqbrtrd
        ex ssrdv cn0 ssrab2 a1i hashcl nn0red nnred letri3d mpbird ) ACGUENZNZB
        UFZFOZGUGNZPZBDULZUHNZYOPUUAYOUIUJZYOUUAUIUJZQAUUBUUCAEUFZYPFOZYRPZBDUL
        ZUHNZUUDUIUJUUBEUKYOUUDYOPZUUHUUAUUDYOUIUUIUUGYTUHUUIUUFYSBDUUIUUEYQYRU
        UDYOYPFUMUNUOUPUUIUQURLAGUSRZDUTRCDRZYOUKRJKMCGYNDHYNVAZVBVCZVDAYOUASUA
        UFZCFOZVEZVFZUHNZUUAUIAYOUUQUTRZUURVGVHZUURAUUJUUKYOUUTPJMUACFUUPGYNDHU
        ULIUUPVAVIVJAUUSUURVGADUUQKASDUUPVQUUQDVKAUASUUODAUUNSRZQZDFGUUNCHIAUUJ
        UVAJTAUVAVLAUUKUVAMTVMVNSDUUPVOVPVRVSVTAYTWARUUQYTVKUURUUAUIUJAYSBDYTWA
        YTVAADGWBNWAHAGWBWCWDWEAUBUUQYTAUBUFZUUQRZUVCYTRZAUVDQUCUFZUUPNUVCPZUCS
        WFZUVEAUVDUVHAUUPSWJUVDUVHWGASWAUUPAUASUUOWAUVBUUNCFWHVNWIUCSUVCUUPWKVP
        WLAUVHUVEWMUVDAUVHUVEAUVHQZUDUFZUUPNZUVCPZUVEUDSUVIUVJSRZQZUVLQUVCUVKYT
        UVLUVCUVKPUVNUVLUVKUVCUVLUQWNWOUVNUVKYTRZUVLUVNAUVMQZUVOUVNAUVMAUVHUVMW
        PUVIUVMVLWQUVPUVKUVJCFOZYTUVPUAUVJUUOUVQSUUPWAUVPUUPWRUVPUUNUVJPZQUUNUV
        JCFUVPUVRVLWSAUVMVLZUVPUVJCFWHWTUVPYSYOUVQFOZYRPBUVQDYPUVQPYQUVTYRYPUVQ
        YOFXBUNUVPDFGUVJCHIAUUJUVMJTZUVSAUUKUVMMTZVMUVPYRUVJYOXAOCFOZUVTUVPUWCU
        VJYOCFOZFOZYRUVPUUJUVMYOSRZUUKXMUWCUWEPUWAUVPUVMUWFUUKUVSAUWFUVMAYOUUMX
        CTUWBXDZDFGUVJYOCHIXEVJUVPUWEUVJYRFOZYRUVPUWDYRUVJFUVPUUKUWDYRPUWBCFGYN
        DYRHUULIYRVAZXFVPXGAUUJUVMUWHYRPJDFGUVJYRHIUWIXHXNVTXIUVPUUJUWFUVMUUKXM
        UWCUVTPUWAUVPUWFUVMUUKUVPUVMUWFUUKUWGXJUVSUWBXDDFGYOUVJCHIXKVJXIXLXOVPT
        XOUVHUVLUDSWFAUVGUVLUCUDSUVGUDXPUVLUCXPUVFUVJUVCUUPXQXRXSXTYDTYAYDYEYTU
        UQWAYBVJYCWQAUUAYOAUUAAYTUTRUUAYFRADYTKYTDVKAYSBDYGYHVRYTYIVPYJAYOUUMYK
        YLYM $.
    $}

    ${
      $d .^ n x $.  $d A n x $.  $d B c k x $.  $d B k l x $.  $d B n x $.
      $d D a k $.  $d D c k x $.  $d D k l x $.  $d D a y $.  $d G a k $.
      $d G c k x $.  $d G k l x $.  $d G n x $.  $d a k ph $.  $d l ph x $.
      $d ph y $.
      unitscyglem2.1 $e |- ( ph -> D e. NN ) $.
      unitscyglem2.2 $e |- ( ph -> D || ( # ` B ) ) $.
      unitscyglem2.3 $e |- ( ph -> A e. B ) $.
      unitscyglem2.4 $e |- ( ph -> ( ( od ` G ) ` A ) = D ) $.
      unitscyglem2.5 $e |- ( ph -> A. c e. NN ( c < D -> ( ( c || ( # ` B ) /\
      { x e. B | ( ( od ` G ) ` x ) = c } =/= (/) ) -> ( # ` { x e. B |
       ( ( od ` G ) ` x ) = c } ) = ( phi ` c ) ) ) ) $.
      $( Lemma for unitscyg .  (Contributed by metakunt, 13-Jul-2025.) $)
      unitscyglem2 $p |- ( ph -> ( # ` { x e. B | ( ( od ` G ) ` x ) = D } )
       = ( phi ` D ) ) $=
        ( wcel va vk vl vy cv cdvds wbr c1 cmin cfz crab cphi cfv csu cod chash
        co wceq caddc wa wne breq1 elrab bilani simpld elfzelzd adantr nnzd cn0
        c0 cn cfn hashcl syl nn0zd simprd dvdstrd wi sylan2br cmul cdiv ad4antr
        jca simpr eqcomd oveq1d nncnd elfzelz adantl ad3antrrr zcnd cle elfzle1
        cz elnnz1 sylibr ad2antrr nnne0d eqtrd eqeltrd cgcd oveq2d eqtr2d mpbid
        nn0cnd elrabd wb syl2anc ex mpd clt nnred 1red resubcld elfzle2 lelttrd
        ltm1d eqeq2 rabbidv fveq2d fveq2 imbi12d 1zzd zred elfzd rabss3d nnge1d
        sseld mpbird pm2.61dan impbid eqrdv sumeq1d nfcv wss ssrab2 fsumsplitsn
        wn a1i ssfid simpl fveqeq2 cgrp simplr divcan4d nnnn0d mulgcld divcan1d
        eqid syl3anc divcan2d gcdmultipled odcld divne0d mulcand ne0d nndivides
        odmulg wrex biimpd syldbl2 r19.29a neeq1d anbi12d eqeq12d wral sumeq2dv
        rspcdva csn cun wo elun ltled imp elsni leidd iddvds jaodan eqidd elsng
        olcd zsubcld neqne necomd ltlend zltlem1d simprr orcd phisum c0g imbi2i
        cr eqcom mpbi eqeq1d unitscyglem1 grpods eqtr4d dvdsle nfv fzfid biimpi
        ltnled pm2.21dd cc eqeltrrd phicld fsumcl addcand ) AUAUEZEUFUGZUAUHEUH
        UIUQZUJUQZUKZUBUEZULUMZUBUNZBUEZHUOUMZUMZEURZBDUKZUPUMZUSUQZUXQEULUMZUS
        UQZURUYCUYEURAUYDUXNUXTUXOURZBDUKZUPUMZUBUNZUYCUSUQZUYFAUXQUYJUYCUSAUYJ
        UXQAUXNUYIUXPUBAUXOUXNTZUTZUXODUPUMZUFUGZUYHVJVAZUTZUYIUXPURZUYMUYOUYPU
        YMUXOEUYNUYMUXOUHUXLUYMUXOUXMTZUXOEUFUGZUYLUYSUYTUTZAUXKUYTUAUXOUXMUXJU
        XOEUFVBVCZVDZVEZVFZUYMEAEVKTZUYLOVGZVHUYMUYNAUYNVITZUYLADVLTZVUHMDVMVNV
        GVOUYMUYSUYTVUCVPZAEUYNUFUGUYLPVGVQUYMVUAUYPVUCAVUAUYPVRUYLAVUAUYPAVUAU
        TZAUYSUTZUYTUTZUYPVUKVULUYTVUKAUYSAVUAUUAVUAAUYLUYSVUBVUDVSWCVUAAUYLUYT
        VUBVUJVSWCVUMUCUEZUXOVTUQZEURZUYPUCVKVUMVUNVKTZUTZVUPUTZUYHEUXOWAUQZCGU
        QZVUSUYGVVAUXSUMZUXOURZBVVADUXRVVAUXOUXSUUBVUSDGHVUTCJKAHUUCTZUYSUYTVUQ
        VUPLWBZVUSVUTVUSVUTVUSVUTVUNVKVUSVUTVUOUXOWAUQVUNVUSEVUOUXOWAVUSVUOEVUR
        VUPWDWEWFVUSVUNUXOVUSVUNVUMVUQVUPUUDZWGVUSUXOVULUXOWNTZUYTVUQVUPUYSVVGA
        UXOUHUXLWHWIZWJZWKZVUSUXOVUMUXOVKTZVUQVUPVULVVKUYTVULVVGUHUXOWLUGZUTZVV
        KVULVVGVVLVVHUYSVVLAUXOUHUXLWMZWIWCUXOWOZWPVGZWQWRZUUEWSVVFWTUUFZVOZACD
        TZUYSUYTVUQVUPQWBZUUGZVUSVUTVVBVTUQZVUTUXOVTUQZURVVCVUSVWDEVWCVUSEUXOVU
        SEVUMVUFVUQVUPAVUFUYSUYTOWQZWQZWGZVVJVVQUUHVUSEVUTCUXSUMZXAUQZVVBVTUQZV
        WCVUSEVWHVWJVUSVWHEAVWHEURZUYSUYTVUQVUPRWBZWEVUSVVDVVTVUTWNTVWHVWJURVVE
        VWAVVSCGHVUTUXSDJUXSUUIZKUURUUJWSVUSVWIVUTVVBVTVUSVWIVUTEXAUQZVUTVUSVWH
        EVUTXAVWLXBVUSVWNVUTUXOVUTVTUQZXAUQVUTVUSEVWOVUTXAVUSVWOEVUSEUXOVWGVVJV
        VQUUKWEXBVUSVUTUXOVVRVVIUULWSWSWFWSXCVUSVVBUXOVUTVUSVVBVUSVVADHUXSJVWMV
        WBUUMXEVVJVUSVUTVVSWKVUSEUXOVWGVVJVUSEVWFWRVVQUUNUUOXDXFUUPVULUYTVUPUCV
        KUUSZVUMUYTVWPVUMVVKVUFUYTVWPXGVVPVWEUCUXOEUUQXHUUTUVAUVBVNXIVGXJWCUYMU
        XOEXKUGZUYQUYRVRZUYMUXOUXLEUYMUXOUYMVVMVVKUYMVVGVVLVUEUYMUYSVVLVUDVVNVN
        WCVVOWPZXLUYMEUHUYMEVUGXLZUYMXMXNVWTUYMUYSUXOUXLWLUGVUDUXOUHUXLXOVNUYME
        VWTXQXPUYMIUEZEXKUGZVXAUYNUFUGZUXTVXAURZBDUKZVJVAZUTZVXEUPUMZVXAULUMZUR
        ZVRZVRZVWQVWRVRIVKUXOVXAUXOURZVXBVWQVXKVWRVXAUXOEXKVBVXMVXGUYQVXJUYRVXM
        VXCUYOVXFUYPVXAUXOUYNUFVBVXMVXEUYHVJVXMVXDUYGBDVXAUXOUXTXRXSZUVCUVDVXMV
        XHUYIVXIUXPVXMVXEUYHUPVXNXTVXAUXOULYAUVEYBYBAVXLIVKUVFUYLSVGVWSUVHXJXJZ
        UVGWEWFAUYKUXNEUVIZUVJZUXPUBUNZUYFAVXRVXQUYIUBUNZUYKAVXRUXKUAUHEUJUQZUK
        ZUXPUBUNZVXSAVXQVYAUXPUBAUDVXQVYAAUDUEZVXQTZVYCVYATZAVYDVYEAVYDUTVYCUXN
        TZVYCVXPTZUVKZVYEVYDVYHAVYCUXNVXPUVLZVDAVYHVYEVRVYDAVYHVYEAVYFVYEVYGAVY
        FVYEAUXNVYAVYCAUXKUAUXMVXTAUXJUXMTZUXKUTZUTZUXJUHEVYLYCVYLEAVUFVYKOVGZV
        HVYKUXJWNTZAVYJVYNUXKUXJUHUXLWHVGWIZVYKUHUXJWLUGZAVYJVYPUXKUXJUHUXLWMVG
        WIVYLUXJEVYLUXJVYOYDZVYLEVYMXLZVYLUXJUXLEVYQVYLEUHVYRVYLXMXNVYRVYKUXJUX
        LWLUGZAVYJVYSUXKUXJUHUXLXOVGWIVYLEVYRXQXPUVMYEYFYHUVNAVYGUTVYCEURZVYEVY
        GVYTAVYCEUVOWIAVYTVYEVRVYGAVYTVYEAVYTUTVYCEVYAAVYTWDAEVYATVYTAUXKEEUFUG
        ZUAEVXTUXJEEUFVBZAEUHEAYCAEOVHZWUCAEOYGAEAEOXLZUVPYEAEWNTZWUAWUCEUVQVNX
        FVGWTXIVGXJUVRXIVGXJXIAVYEVYDAVYEUTZVYHVYDWUFVYTVYHWUFVYTUTZVYGVYFWUGVY
        CEVXPWUFVYTWDWUGEVXPTZEEURZWUGEUVSWUGVUFWUHWUIXGAVUFVYEVYTOWQEEVKUVTVNY
        IWTUWAWUFVYTYRZUTZVYFVYGWUKVYCVXTTZVYCEUFUGZUTZVYFWUFWUNWUJVYEWUNAUXKWU
        MUAVYCVXTUXJVYCEUFVBZVCVDVGWUKWUNVYFWUKWUNUTZUXKWUMUAVYCUXMWUOWUPVYCUHU
        XLWUPYCZWUPEUHAWUEVYEWUJWUNWUCWJWUQUWBWUNVYCWNTZWUKWULWURWUMVYCUHEWHVGW
        IZWUNUHVYCWLUGZWUKWULWUTWUMVYCUHEWMVGWIWUPVYCEXKUGZVYCUXLWLUGWUPWVAVYCE
        WLUGZEVYCVAZUTWUPWVBWVCWUNWVBWUKWULWVBWUMVYCUHEXOVGWIWUKWVCWUNWUKVYCEWU
        JVYCEVAWUFVYCEUWCWIUWDVGWCWUPVYCEWUPVYCWUSYDAEUWLTVYEWUJWUNWUDWJUWEYIWU
        PVYCEWUSWUPEAVUFVYEWUJWUNOWJVHUWFXDYEWUKWULWUMUWGXFXIXJUWHYJVYIWPXIYKYL
        ZYMAVXSUXKUAVKUKZUXPUBUNZVYBAWVFEVXSAVUFWVFEUROUAEUBUWIVNAEVYAUYIUBUNZV
        XSAEEUXRGUQZHUWJUMZURZBDUKZUPUMZWVGAWVLVWHEAWVLVWHUXRGUQZWVIURZBDUKZUPU
        MVWHAWVKWVOUPAWVJWVNBDAWVHWVMWVIAEVWHUXRGAVWKVRAEVWHURZVRRVWKWVPAVWHEUW
        MUWKUWNWFUWOXSXTABCDFGHJKLMNQUWPWSRXCABDUBUAGHEJKLMOUWQUWRAVYAVXQUYIUBA
        VXQVYAWVDWEYMWSXCAWVEVYAUXPUBAUDWVEVYAAVYCWVETZVYEAWVQVYEAWVQUTZUXKWUMU
        AVYCVXTWUOWVRVYCUHEWVRYCAWUEWVQWUCVGWVRVYCWVRVYCVKTZWUMWVQWVSWUMUTAUXKW
        UMUAVYCVKWUOVCVDZVEZVHZWVRVYCWWAYGWVRWUMWVBWVRWVSWUMWVTVPZWVRWURVUFWUMW
        VBVRWWBAVUFWVQOVGVYCEUWSXHXJYEWWCXFXIAVYAWVEVYCAUXKUAVXTVKAUXJVXTTZUXKU
        TZUTVYNVYPUTZUXJVKTWWEWWFAWWDWWFUXKWWDVYNVYPUXJUHEWHUXJUHEWMWCVGWIUXJWO
        WPYFYHYKYLYMXCWSAUXNEUYIUYCUBVKAUBUWTZUBUYCYNAUXMUXNAUHUXLUXAUXNUXMYOAU
        XKUAUXMYPYSYTZOAEUXNTZWWIYRZAWWIUTZEUXLWLUGZWWJWWKEUXMTZWWLWWIWWMAWWIWW
        MWUAWWIWWMWUAUTUXKWUAUAEUXMWUBVCUXBVEWIEUHUXLXOVNAWWLYRZWWIAUXLEXKUGWWN
        AEWUDXQAUXLEAEUHWUDAXMXNWUDUXCXDVGUXDAWWJWDYJZUYMUYIUYMUYHVLTUYIVITUYMD
        UYHAVUIUYLMVGUYHDYOUYMUYGBDYPYSYTUYHVMVNXEZUXOEURZUYHUYBUPWWQUYGUYABDUX
        OEUXTXRXSXTAUYCAUYBVLTUYCVITADUYBMUYBDYOAUYABDYPYSYTUYBVMVNXEZYQXCAUXNE
        UXPUYEUBVKWWGUBUYEYNWWHOWWOUYMUYIUXPUXEVXOWWPUXFZUXOEULYAAUYEAEOUXGWGZY
        QWSWSAUXQUYCUYEAUXNUXPUBWWHWWSUXHWWRWWTUXIXD $.
    $}

    ${
      $d B a c d x $.  $d B c d e x $.  $d G a c d x $.  $d G c d e x $.
      $d a c d ph $.  $d e ph $.  $d .^ n x z $.  $d B a c d x z $.
      $d B a n x z $.  $d G a c d x z $.  $d G a n x z $.  $d a c d ph z $.
      $d n ph z $.
      $( Lemma for unitscyg .  (Contributed by metakunt, 14-Jul-2025.) $)
      unitscyglem3 $p |- ( ph -> A. d e. NN ( ( d || ( # ` B ) /\
      { x e. B | ( ( od ` G ) ` x ) = d } =/= (/) ) -> ( # ` { x e. B |
      ( ( od ` G ) ` x ) = d } ) = ( phi ` d ) ) ) $=
        ( vc vz chash cfv wceq wa wi cn ve va cv cdvds wbr cod crab c0 wne cphi
        wcel breq1 eqeq2 rabbidv neeq1d anbi12d fveq2d fveq2 eqeq12d imbi2d clt
        imbi12d wral simplr simplll jca adantr rspcdva simp-5r mpd ex ralrimiva
        simpr nfv cbvralw biimpi syl simprl simprr rabn0 bilani simp-4l simp-4r
        wrex jca31 nfcv fveqeq2 cbvrabw a1i ad5antr cfn co c0g cle oveq2 eqeq1d
        breq1d ralbidv biimpd simpllr eqcom neeq1i anbi2i fveq2i eqeq1i imbi12i
        cgrp mpbi imbi2i ralimi adantl unitscyglem2 eqtrd cbvrexw r19.29a com12
        indstr imp ) AGUCZCOPZUDUEZBUCZFUFPZPZXSQZBCUGZUHUIZRZYFOPZXSUJPZQZSZGT
        AXSTUKZYLYMAYLAYLSZAMUCZXTUDUEZYDYOQZBCUGZUHUIZRZYROPZYOUJPZQZSZSZGMXSY
        OQZYLUUDAUUFYHYTYKUUCUUFYAYPYGYSXSYOXTUDULUUFYFYRUHUUFYEYQBCXSYOYDUMUNZ
        UOUPUUFYIUUAYJUUBUUFYFYROUUGUQXSYOUJURUSVBUTYMYOXSVAUEZUUESZMTVCZYNYMUU
        JRZAYLUUKARZYHYKUULYHRZAYMRZUUHUUDSZMTVCZRZYARZYGRZYKUUMUURYGUUMUUQYAUU
        MUUNUUPUUMAYMUUKAYHVDYMUUJAYHVEVFUUMUAUCZXSVAUEZUUTXTUDUEZYDUUTQZBCUGZU
        HUIZRZUVDOPZUUTUJPZQZSZSZUATVCZUUPUUMUVKUATUUMUUTTUKZRZUVAAUVJSZSZUVKUV
        NUUIUVPMTUUTYOUUTQZUUHUVAUUEUVOYOUUTXSVAULUVQUUDUVJAUVQYTUVFUUCUVIUVQYP
        UVBYSUVEYOUUTXTUDULUVQYRUVDUHUVQYQUVCBCYOUUTYDUMUNZUOUPUVQUUAUVGUUBUVHU
        VQYRUVDOUVRUQYOUUTUJURUSVBUTVBUUMUUJUVMUULUUJYHUUKUUJAYMUUJVMVGVGVGUUMU
        VMVMVHUVNUVPUVKUVNUVPRZUVAUVJUVSUVARZAUVJUUKAYHUVMUVPUVAVIUVTUVAUVOUVSU
        VAVMUVNUVPUVAVDVJVJVKVKVJVLUVLUUPUVKUUOUAMTUVKMVNUUOUAVNUUTYOQZUVAUUHUV
        JUUDUUTYOXSVAULUWAUVFYTUVIUUCUWAUVBYPUVEYSUUTYOXTUDULUWAUVDYRUHUWAUVCYQ
        BCUUTYOYDUMUNZUOUPUWAUVGUUAUVHUUBUWAUVDYROUWBUQUUTYOUJURUSVBVBVOVPVQVFU
        ULYAYGVRVFUULYAYGVSVFUUSYEBCWDZYKYGUWCUURYEBCVTWAUURUWCYKSYGUURUWCYKUUR
        UWCRZUBUCZYCPXSQZYKUBCUWDUWECUKZRZUWFRZUURUWGRZUWFRZYKUWIUWJUWFUWIUUQYA
        UWGUUQYAUWCUWGUWFWBUUQYAUWCUWGUWFWCUWDUWGUWFVDWEUWHUWFVMVFUWKYINUCZYCPZ
        XSQZNCUGZOPYJUWKYFUWOOYFUWOQUWKYEUWNBNCBCWFZNCWFZYENVNUWNBVNYBUWLXSYCWG
        WHWIUQUWKNUWECXSDEFMHIAFXGUKYMUUPYAUWGUWFJWJACWKUKYMUUPYAUWGUWFKWJADUCZ
        UWLEWLZFWMPZQZNCUGZOPZUWRWNUEZDTVCZYMUUPYAUWGUWFAUWRYBEWLZUWTQZBCUGZOPZ
        UWRWNUEZDTVCZUXELAUXKUXEAUXJUXDDTAUXIUXCUWRWNAUXHUXBOUXHUXBQAUXGUXABNCU
        WPUWQUXGNVNUXABVNYBUWLQUXFUWSUWTYBUWLUWREWOWPWHWIUQWQWRWSVJWJAYMUUPYAUW
        GUWFVIUUQYAUWGUWFWTUURUWGUWFVDUWJUWFVMUWJUUHYPUWMYOQZNCUGZUHUIZRZUXMOPZ
        UUBQZSZSZMTVCZUWFUURUXTUWGUUQUXTYAUUPUXTUUNUUOUXSMTUUOUXSUUDUXRUUHYTUXO
        UUCUXQYSUXNYPYRUXMUHUXMYRQYRUXMQUXLYQNBCUWQUWPUXLBVNYQNVNUWLYBYOYCWGWHU
        XMYRXAXHZXBXCUUAUXPUUBYRUXMOUYAXDXEXFXIVPXJXKVGVGVGXLXMVQUWCUWFUBCWDUUR
        YEUWFBUBCYEUBVNUWFBVNYBUWEXSYCWGXNWAXOVKVGVJVQVKVKVKXQXPXRVL $.
    $}

    ${
      $d .^ l x $.  $d .^ n x $.  $d B a k $.  $d B l x $.  $d B k m x $.
      $d B n x $.  $d B x y $.  $d B a z $.  $d D k m x $.  $d D x y $.
      $d D x z $.  $d G a k $.  $d G l x $.  $d G k m x $.  $d G n x $.
      $d G x y $.  $d G a z $.  $d a k ph $.  $d l ph x $.  $d m ph x $.
      $d n ph x $.  $d ph x z $.
      unitscyglem4.1 $e |- ( ph -> D e. NN ) $.
      unitscyglem4.2 $e |- ( ph -> D || ( # ` B ) ) $.
      $( Lemma for unitscyg .  (Contributed by metakunt, 14-Jul-2025.) $)
      unitscyglem4 $p |- ( ph -> ( # ` { y e. B | ( ( od ` G ) ` y ) = D } )
       = ( phi ` D ) ) $=
        ( wceq wa adantr c1 wcel vm va vk vl vz cv cfv crab wne chash cphi nfcv
        c0 nfv fveqeq2 a1i cdvds wbr ex wi cn breq1 eqeq2 rabbidv neeq1d fveq2d
        anbi12d fveq2 eqeq12d imbi12d rspcdva imp syl eqtrd necon1bi adantl clt
        wn id cfz co csu cfn hashfingrpnn cmul simpr eqcomd w3a cn0 odcld nn0zd
        cz eqid simplr 3jca syl2anc oveq2d wrex syl3anc wb hashcl mpbid r19.29a
        eqtr2d caddc fzfid wss ssrab2 ssfid nn0cnd 1zzd nnzd nnge1d nnred leidd
        elfzd elrabd fsumsplit1 nn0red phicld cle biimpi elfzelz elfzle1 sylibr
        elrab jca cc0 cdiv ad2antrr nnne0d cgcd mpbird bilani eqbrtrd mpd ssrdv
        zred sumeq1d breqtrd cod cbvrabw fveq2i imdistani unitscyglem3 c0g cgrp
        ancrd grpods mulgass odid mulgz sylan oddvds2 divides rabeqcda csn cdif
        oveq1d iddvds fsumnn0cl eldifi elnnz1 fsumrecl simplll dvdsval2 mulgcld
        diffi phicl cc divdiv2d divcan3d divcan2d nndivdvds nnnn0d gcdmultipled
        nncnd odmulg zcnd eqeltrd eqnetrd gcd2n0cl divmuld ne0i cbvrexw necon4d
        rabn0 bitri hash0 nngt0d cmin eldif velsn bicomi zsubcld elfzle2 simprr
        necon3bi necomd ltlend zltlem1d simprlr 1red resubcld lem1d letrd sseld
        rabss2 adantrr 3syl ltnled pm2.21dd pm2.61dane eldifsnd eqssd cr simpll
        bilanri simprd eqled nn0ge0d pm2.61dan fsumle ltleaddd breqtrrd rabss3d
        wral simpl simprl anassrs nnz dvdsle phisum ltnrd ) ABUFZHUUAUGZUGZEPZB
        DUHZUMUIZCUFZUYPUGEPZCDUHZUJUGZEUKUGZPZAUYTQZVUDUYSUJUGZVUEVUDVUHPVUGVU
        CUYSUJVUBUYRCBDCDULBDULVUBBUNUYRCUNVUAUYOEUYPUOUUBUUCUPVUGAEDUJUGZUQURZ
        UYTQZQVUHVUEPZAUYTVUKAUYTVUJAUYTVUJAVUJUYTORUSUUHUUDAVUKVULAUAUFZVUIUQU
        RZUYQVUMPZBDUHZUMUIZQZVUPUJUGZVUMUKUGZPZUTZVUKVULUTUAVAEVUMEPZVURVUKVVA
        VULVVCVUNVUJVUQUYTVUMEVUIUQVBVVCVUPUYSUMVVCVUOUYRBDVUMEUYQVCVDZVEVGVVCV
        USVUHVUTVUEVVCVUPUYSUJVVDVFVUMEUKVHVIVJABDFGHUAIJKLMUUEZNVKVLVMVNAUYTVR
        ZQUYSUMPZVUFVVFVVGAUYTUYSUMUYTVSVOVPAVVGVUFUTVVFAVVGVUFAVVGQZVUIVUIVQUR
        ZVUFVVHVUIUBUFZVUIUQURZUBSVUIVTWAZUHZUYQUCUFZPZBDUHZUJUGZUCWBZVUIVQVVHV
        VRVUIUYOGWAZHUUFUGZPZBDUHZUJUGVUIVVHBDUCUBGHVUIIJAHUUGTZVVGKRZADWCTZVVG
        LRZVVHDHIVWDVWFWDZUUIVVHVWBDUJAVWBDPVVGAVWABDAUYODTZQZUDUFZUYQWEWAZVUIP
        ZVWAUDWLVWIVWJWLTZQZVWLQZVVSVWKUYOGWAZVVTVWOVUIVWKUYOGVWOVWKVUIVWNVWLWF
        WGUUSVWNVWPVVTPVWLVWNVWPVWJUYQUYOGWAZGWAZVVTVWNVWCVWMUYQWLTZVWHWHVWPVWR
        PVWIVWCVWMAVWCVWHKRZRVWNVWMVWSVWHVWIVWMWFVWNUYQVWIUYQWITVWMVWIUYODHUYPI
        UYPWMZAVWHWFZWJZRWKAVWHVWMWNZWODGHVWJUYQUYOIJUUJWPVWNVWRVWJVVTGWAZVVTVW
        NVWQVVTVWJGVWNVWHVWQVVTPVXDUYOGHUYPDVVTIVXAJVVTWMZUUKVMWQVWIVWCVWMVXEVV
        TPVWTDGHVWJVVTIJVXFUULUUMVNVNRVNVWIUYQVUIUQURZVWLUDWLWRZVWIVWCVWEVWHVXG
        VWTAVWEVWHLRZVXBUYOHUYPDIVXAUUNWSVWIVWSVUIWLTZVXGVXHWTVWIUYQVXCWKVWIVUI
        VWIVWEVUIWITZVXIDXAZVMWKUDUYQVUIUUOWPXBXCUUPRVFXDVVHVVRVVKUBVAUHZVVNUKU
        GZUCWBZVUIVQVVHVVRVVMVXNUCWBZVXOVQVVHVVRUYQVUIPZBDUHZUJUGZVVMVUIUUQZUUR
        ZVVQUCWBZXEWAZVXPVQVVHVVMVVQVUIVXSUCVVHUCUNZUCVXSULVVHVVLVVMVVHSVUIXFVV
        MVVLXGVVHVVKUBVVLXHUPXIZVVHVVNVVMTZQZVVQVYGVVPWCTZVVQWITZVYGDVVPVVHVWEV
        YFVWFRVVPDXGZVYGVVOBDXHZUPXIVVPXAZVMXJVVHVVKVUIVUIUQURZUBVUIVVLVVJVUIVU
        IUQVBVVHVUISVUIVVHXKVVHVUIVWGXLZVYNVVHVUIVWGXMVVHVUIVVHVUIVWGXNXOXPVVHV
        XJVYMVYNVUIUUTVMXQZVVNVUIPZVVPVXRUJVYPVVOVXQBDVVNVUIUYQVCVDVFXRVVHVYCVU
        IUKUGZVYAVXNUCWBZXEWAVXPVQVVHVXSVYBVYQVYRVVHVXSVVHVXRWCTVXSWITVVHDVXRVW
        FVXRDXGVVHVXQBDXHUPXIVXRXAVMXSVVHVYBVVHVYAVVQUCVVHVVMWCTVYAWCTVYEVVMVXT
        UVHVMZVVHVVNVYATZQZVYHVYIWUADVVPVVHVWEVYTVWFRVYJWUAVYKUPXIVYLVMUVAXSVVH
        VYQVVHVUIVWGXTZXNVVHVYAVXNUCVYSWUAVXNWUAVVNVATZVXNVATWUAVVNWLTZSVVNYAUR
        ZQZWUCVYTWUFVVHVYTVYFWUFVVNVVMVXTUVBVYFVVNVVLTZVVNVUIUQURZQZWUFVYFWUIVV
        KWUHUBVVNVVLVVJVVNVUIUQVBZYFZYBWUGWUFWUHWUGWUDWUEVVNSVUIYCVVNSVUIYDYGRZ
        VMVMVPVVNUVCZYEVVNUVIVMXNUVDVVHVXSYHVYQVQVVHVXSUMUJUGZYHVVHVXRUMUJAVVGV
        XRUMPAVXRUMUYSUMAVXRUMUIZUYTAWUOQZUEUFZUYPUGZVUIPZUYTUEDWUPWUQDTZQZWUSQ
        ZAWUTQZWUSQZUYTWVBWVCWUSWVBAWUTAWUOWUTWUSUVEWUPWUTWUSWNYGWVAWUSWFYGWVDV
        UIEYIWAZWUQGWAZUYSTUYTWVDUYRWVFUYPUGZEPBWVFDUYOWVFEUYPUOWVDDGHWVEWUQIJA
        VWCWUTWUSKYJZWVDVUJWVEWLTZAVUJWUTWUSOYJZWVDEWLTEYHUIVXJVUJWVIWTWVDEAEVA
        TZWUTWUSNYJZXLZWVDEWVLYKZWVDVUIWVDVWEVXKAVWEWUTWUSLYJZVXLVMZWKZEVUIUVFW
        SXBZAWUTWUSWNZUVGZWVDEVUIWVEWURYLWAZYIWAZWVGWVDEVUIWVEYIWAZWWBWVDWWCVUI
        EWEWAVUIYIWAEWVDVUIVUIEWVDVUIWVPXJZWWDAEUVJTWUTWUSAENUVQZYJZWVDVUIWVDDH
        IWVHWVOWDZYKZWVNUVKWVDEVUIWWFWWDWWHUVLXDWVDWVEWWAVUIYIWVDWWAWVEWVDWWAWV
        EVUIYLWAZWVEWVDWURVUIWVEYLWVCWUSWFZWQWVDWWIWVEEWVEWEWAZYLWAWVEWVDVUIWWK
        WVEYLWVCVUIWWKPZWUSAWWLWUTAWWKVUIAVUIEAVUIAVWEVXKLVXLVMZXJWWEAENYKUVMWG
        RRWQWVDWVEEWVDWVEWVDVUJWVEVATZWVJWVDVUIVATZWVKVUJWWNWTWWGWVLVUIEUVNWPXB
        UVOWVMUVPVNVNZWGWQVNWVDWWBWVGPWWAWVGWEWAZVUIPWVDVUIWWQWVDVUIWURWWQWVDWU
        RVUIWWJWGWVDVWCWUTWVIWURWWQPWVHWVSWVRWUQGHWVEUYPDIVXAJUVRWSVNWGWVDVUIWW
        AWVGWWDWVDWWAWVEUVJWWPWVDWVEWVRUVSUVTWVDWVGWVDWVFDHUYPIVXAWVTWJXJWVDWWA
        WVDWVIWURWLTZWURYHUIZWHWWAVATWVDWVIWWRWWSWVRWVDWURVUIWLWWJWVQUVTWVDWURV
        UIYHWWJWWHUWAWOWVEWURUWBVMYKUWCYMXDXQUYSWVFUWDVMVMWUOWUSUEDWRZAWUOVXQBD
        WRWWTVXQBDUWGVXQWUSBUEDVXQUEUNWUSBUNUYOWUQVUIUYPUOUWEUWHYNXCUSUWFVLVFWU
        NYHPZVVHUWIUPVNVVHVYQWUBUWJYOAVYBVYRYAURVVGAVYBVVKUBSVUISUWKWAZVTWAZUHZ
        VVQUCWBZVYRYAAVYAWXDVVQUCAVYAWXDAUEVYAWXDAWUQVYATZWUQWXDTZAWXFQWUQVVMTZ
        WUQVXTTZVRZQZWXGWXFWXKAWUQVVMVXTUWLYNAWXKWXGUTWXFAWXKWXGAWXKQWUQVVLTZWU
        QVUIUQURZQZWUQVUIUIZQZWXGWXKWXPAWXKWXNWXOWXHWXNWXJWXHWXNVVKWXMUBWUQVVLV
        VJWUQVUIUQVBZYFYBZRWXJWXOWXHWXIWUQVUIWUQVUIPZWXIWXIWXSUEVUIUWMUWNYBUWRV
        PYGVPAWXPWXGUTWXKAWXPWXGAWXPQZVVKWXMUBWUQWXCWXQWXTWUQSWXBWXTXKZWXTVUISW
        XTVUIWXTVWEVXKAVWEWXPLRVXLVMZWKZWYAUWOWXPWUQWLTZAWXNWYDWXOWXLWYDWXMWUQS
        VUIYCRZRVPZWXPSWUQYAURZAWXNWYGWXOWXLWYGWXMWUQSVUIYDRRVPWXTWUQVUIVQURZWU
        QWXBYAURZWXTWYHWUQVUIYAURZVUIWUQUIZQWXTWYJWYKWXPWYJAWXNWYJWXOWXLWYJWXMW
        UQSVUIUWPRRVPWXTWUQVUIAWXNWXOUWQUWSYGWXTWUQVUIWXTWUQWYFYRWXTVUIWYBXSUWT
        YMWXTWUQVUIWYFWYCUXAXBXPAWXLWXMWXOUXBXQUSRYPUSRYPUSYQAUEWXDVYAAWXGWXFAW
        XGQZWUQVVMVUIAWXGWXHAWXDVVMWUQAWXCVVLXGWXDVVMXGAUEWXCVVLAWUQWXCTZWXLAWY
        MQZWUQSVUIWYNXKAVXJWYMAVUIWWMWKZRZWYMWYDAWUQSWXBYCVPZWYMWYGAWUQSWXBYDVP
        WYNWUQWXBVUIWYNWUQWYQYRWYNVUISWYNVUIWYPYRZWYNUXCUXDWYRWYMWYIAWUQSWXBUWP
        VPZWYNVUIWYRUXEUXFXPUSYQVVKUBWXCVVLUXHVMUXGVLZWYLWXOWUQVUIWYLWXSQZVUIVU
        IYAURZWXOXUAVUIXUAVUIAVXKWXGWXSWWMYJXSZXOXUAVVIXUBVRXUAVUIWUQVUIVQXUAWU
        QVUIWYLWXSWFWGWYLWYHWXSWYLWYHWYIWYLWYMWXMQZWYIWXGXUDAVVKWXMUBWUQWXCWXQY
        FYNAXUDWYIUTWXGAXUDWYIAWYMWYIWXMWYSUXIUSRYPWYLWUQVUIWYLWXHWXNWYDWYTWXRW
        YEUXJAVXJWXGWYORUXAYMRYOXUAVUIVUIXUCXUCUXKXBUXLWYLWXOWFUXMUXNUSYQUXOZYS
        AWXEWXDVXNUCWBZVYRYAAWXDVVQVXNUCAWXCWXDASWXBXFWXDWXCXGAVVKUBWXCXHUPXIAV
        VNWXDTZQZVVQXUHVYHVYIXUHDVVPAVWEXUGLRVYJXUHVYKUPXIVYLVMXSZXUHVXNXUHVVNX
        UHVVNWXCTZWUHQZWUCXUGXUKAVVKWUHUBVVNWXCWUJYFZYNZAXUKWUCUTXUGAXUKWUCAXUK
        QZWUFWUCXUKWUFAXUJWUFWUHXUJWUDWUEVVNSWXBYCVVNSWXBYDYGRVPWUMYEZUSRYPZXTX
        NXUHXUKVVQVXNYAURZXUMAXUKXUQUTXUGAXUKXUQXUNVVPUMUIZXUQXUNXURQZVVQVXNXUS
        XUHVVQUXPTXUSAXUGAXUKXURUXQXUNXUGXURXUGXUKAXULUXRRYGZXUIVMXUSXUHXURQZVV
        QVXNPZXUSXUHXURXUTXUNXURWFYGXVAWUHXURQZXVBXVAWUHXURXUHWUHXURXUHXUJWUHXU
        MUXSRXUHXURWFYGXUHXVCXVBUTZXURXUHVVBXVDUAVAVVNVUMVVNPZVURXVCVVAXVBXVEVU
        NWUHVUQXURVUMVVNVUIUQVBXVEVUPVVPUMXVEVUOVVOBDVUMVVNUYQVCVDZVEVGXVEVUSVV
        QVUTVXNXVEVUPVVPUJXVFVFVUMVVNUKVHVIVJAVVBUAVAUYGXUGVVERXUPVKRYPVMUXTXUN
        XURVRZQZVVQYHVXNYAXVHVVQWUNYHXVHVVPUMUJXVGVVPUMPXUNXURVVPUMXURVSVOVPVFW
        XAXVHUWIUPVNXVHVXNXVHVXNXVHVVNXUNWUCXVGXUORXTUVOUYAYOUYBUSRYPUYCAVYRXUF
        AVYAWXDVXNUCXUEYSWGYTYORUYDVVHVVMVXNVUIVYQUCVYDUCVYQULVYEVYGVXNVYGVVNVY
        GAWUIQZWUCVYGAWUIAVVGVYFUXQVYFWUIVVHWUKYNYGVYGXVIWUCVYGXVIQWUFWUCXVIWUF
        VYGWUIWUFAWULVPVPWUMYEUSYPXTUVQVYOVVNVUIUKVHXRUYEYOVVHVVMVXMVXNUCAVVMVX
        MPVVGAVVMVXMAVVKUBVVLVAAVVJVVLTZVVKQZQVVJWLTZSVVJYAURZQZVVJVATZXVKXVNAX
        VJXVNVVKXVJXVLXVMVVJSVUIYCVVJSVUIYDYGRVPVVJUVCYEUYFAVVKUBVAVVLAXVOVVKQZ
        QZAXVOQZVVKQZXVJXVQXVRVVKXVQAXVOAXVPUYHAXVOVVKUYIZYGAXVOVVKUWQYGXVSVVJS
        VUIXVSXKXVRVXJVVKAVXJXVOWYORRXVSVVJAXVOVVKXVOXVTUYJZXLXVSVVJXWAXMXVRVVK
        VVJVUIYAURZXVRXVLWWOVVKXWBUTXVOXVLAVVJUYKVPAWWOXVOADHIKLWDRVVJVUIUYLWPV
        LXPVMUYFUXORYSYTVVHWWOVXOVUIPVWGUBVUIUCUYMVMYTYOVVHVUIVVHVUIAVXKVVGWWMR
        XSUYNUXLUSRYPUYB $.
    $}
  $}

  ${
    $d D m o $.  $d D m w $.  $d D w z $.  $d G m o $.  $d G m w $.
    $d G y z $.  $d R m o $.  $d R z $.  $d m o ph $.  $d ph y z $.
    unitscyglem5.1 $e |- G = ( ( mulGrp ` R ) |`s ( Unit ` R ) ) $.
    unitscyglem5.2 $e |- ( ph -> R e. IDomn ) $.
    unitscyglem5.3 $e |- ( ph -> ( Base ` R ) e. Fin ) $.
    unitscyglem5.4 $e |- ( ph -> D e. NN ) $.
    unitscyglem5.5 $e |- ( ph -> D || ( # ` ( Base ` G ) ) ) $.
    $( Lemma for unitscyg .  (Contributed by metakunt, 9-Aug-2025.) $)
    unitscyglem5 $p |- ( ph -> ( ( mulGrp ` R ) PrimRoots D ) =/= (/) ) $=
      ( vz cfv co wcel wceq eqid syl a1i wa adantr c1 vm vw vy vo cv cprimroots
      cmgp wex wne cod cbs crab cc0 chash clt wbr cphi phicld cmg crg idomringd
      c0 cn cgrp cui unitgrp wss ressbasss mgpbas eqimsscd sstrd c0g cle eqcomi
      ssfid unitss cin ressbasssg inss1 sseld simpr ressmulgnnd eqeq1d rabbidva
      imp fveq2d cxr fvex rabex hashxrcl eqeltrrd cr nnre adantl rexrd ad2antrr
      cvv simprl mpd rabss3d jca hashss cidom unitgrpid eqcomd ringidcl eqeltrd
      idomrootle syl3anc xrletrd ralrimiva unitscyglem4 eleq1d mpbird nngt0d wb
      cur eqbrtrd hashneq0 mpbid n0 sylib nfv fveqeq2 elrab bilani simpll jca31
      simprr ccmn ccrg idomcringd crngmgp sselda caddc 1cnd sylibr oveq1d eqtrd
      eqtr2d csubmnd unitsubm cdsr cmulr wrex eleqtrdi cmin cmnmndd cn0 cz nnzd
      1zzd zsubcld addridd nnge1d 1red 0red leaddsub2d elnn0z mulgnn0cld cplusg
      nnred mgpplusg oveqd nncnd npcand cmnd mulgnn0p1 ringidval 1unit ad2antlr
      ress0g rspcedvd dvdsr crngunit submod syl2anc isprimroot2 mpdan ex eximd
      odid ) AUAUEZCUGKZBUFLZMZUAUHZUWEVBUIAUWCUBUEZDUJKZKBNZUBDUKKZULZMZUAUHZU
      WGAUWLVBUIZUWNAUMUWLUNKZUOUPZUWOAUWPAUWPVCMBUQKZVCMABHURAUWPUWRVCAJUBUWKB
      UCDUSKZDUWKOZUWSOZACUTMZDVDMACFVAZCCVEKZDUXDOZEVFPACUKKZUWKGAUWKUWDUKKZUX
      FUWKUXGVGAUXDUXGDUWDEUXGOZVHQZAUXFUXGUXFUXGNAUXFCUWDUWDOZUXFOZVIZQVJVKZVO
      AUCUEZJUEZUWSLZDVLKZNZJUWKULZUNKZUXNVMUPUCVCAUXNVCMZRZUXTUXNUXOUWDUSKZLZU
      XQNZJUWKULZUNKZUXNVMUYBUXSUYFUNUYBUXRUYEJUWKUYBUXOUWKMZRZUXPUYDUXQUYIUXDU
      WDDUXNUXOEUYBUXDUXGVGZUYHAUYJUYAUYJAUXGCUXDUXFUXGUXLVNZUXEVPZQSSUYBUYHUXO
      UXDMUYBUWKUXDUXOAUWKUXDVGUYAAUWKUXDUXGVQZUXDUWKUYMVGAUXDUXGDUWDEUXHVRQUYM
      UXDVGAUXDUXGVSQVKZSVTWEUYBUYAUYHAUYAWAZSWBWCWDWFZUYBUYGUYEJUXFULZUNKZUXNU
      YBUXTUYGWGUYPUYBUXSWQMZUXTWGMUYSUYBUXRJUWKDUKWHZWIQUXSWQWJPWKUYBUYQWQMZUY
      RWGMVUAUYBUYEJUXFCUKWHWIQZUYQWQWJPUYBUXNUYAUXNWLMAUXNWMWNWOUYBVUAUYFUYQVG
      ZRUYGUYRVMUPUYBVUAVUCVUBUYBUYEJUWKUXFUYBUYHUYERZRZUYHUXOUXFMUYBUYHUYEWRVU
      EUWKUXFUXOAUWKUXFVGUYAVUDUXMWPVTWSWTXAUYQUYFWQXBPUYBCXCMZUXQUXFMZUYAUYRUX
      NVMUPAVUFUYAFSAVUGUYAAUXQCXQKZUXFAVUHUXQAUXBVUHUXQNUXCCUXDVUHDUXEEVUHOZXD
      PXEAUXBVUHUXFMUXCUXFCVUHUXKVUIXFPXGSUYOJUXFCUYCUXNUXQUXKUYCOZXHXIXJXRXKHI
      XLXMXNXOAUWLWQMZUWQUWOXPVUKAUWJUBUWKUYTWIQUWLWQXSPXTUAUWLYAYBAUWMUWFUAAUA
      YCAUWMUWFAUWMRZUWCUWKMZUWCUWIKZBNZRZUWFUWMVUPAUWJVUOUBUWCUWKUWHUWCBUWIYDY
      EYFVULVUPRZAVUMRZVUORZUWFVUQAVUMVUOAUWMVUPYGVULVUMVUOWRVULVUMVUOYIYHVUSUW
      DBUWCAUWDYJMZVUMVUOACYKMZVUTACFYLZCUWDUXJYMPWPZABVCMVUMVUOHWPZVURUWCUXGMZ
      VUOAUWKUXGUWCUXIYNSZVUSUWCUWDUJKZKZVUNBVUSUXDUWDUUAKMZUWCUXDMZVVHVUNNVUSU
      XBVVIAUXBVUMVUOUXCWPCUXDUWDUXEUXJUUBPVUSVVJUWCVUHCUUCKZUPZVUSUWCUXFMZUDUE
      ZUWCCUUDKZLZVUHNZUDUXFUUEZRVVLVUSVVMVVRVUSUWCUXGUXFVVFUYKUUFZVUSVVQBTUUGL
      ZUWCUYCLZUWCVVOLZVUHNUDVWAUXFVUSUXFUYCUWDVVTUWCUXLVUJVUSUWDVVCUUHZVURVVTU
      UIMZVUOAVWDVUMAVVTUUJMZUMVVTVMUPZRVWDAVWEVWFABTABHUUKAUULUUMATUMYOLZBVMUP
      VWFAVWGTBVMATAYPUUNABHUUOXRATUMBAUUPAUUQABHUVBUURXTXAVVTUUSYQSSZVVSUUTVUS
      VVNVWANZRZVVPVWBVUHVWJVVNVWAUWCVVOVUSVWIWAYRWCVUSVWBVWAUWCUWDUVAKZLZVUHVU
      SVVOVWKVWAUWCVVOVWKNVUSCVVOUWDUXJVVOOZUVCQUVDVUSVWLUWDVLKZVUHVUSVWLBUWCUY
      CLZVWNVUSVWOVVTTYOLZUWCUYCLZVWLVUSBVWPUWCUYCVUSVWPBVUSBTVUSBVVDUVEVUSYPUV
      FXEYRVUSUWDUVGMZVWDVVEVWQVWLNVWCVWHVVFUXGVWKUYCUWDVVTUWCUXHVUJVWKOUVHXIYT
      VUSVWNBUWCUWSLZVWOVUSVWNUXQVWSVUSVWRVWNUXDMZUYJVWNUXQNVWCVURVWTVUOAVWTVUM
      AVWNVUHUXDAVUHVWNVUHVWNNZACVUHUWDUXJVUIUVIZQXEAUXBVUHUXDMUXCCUXDVUHUXEVUI
      UVJPXGSSUYJVUSUYLQZUXDUXGUWDDVWNEUXHVWNOUVLXIVUSVWSUXQVUSVWSVUNUWCUWSLZUX
      QVUSBVUNUWCUWSVUSVUNBVURVUOWAZXEYRVUMVXDUXQNAVUOUWCUWSDUWIUWKUXQUWTUWIOZU
      XAUXQOUWBUVKYSXEYSVUSUXDUWDDBUWCEVXCVURVVJVUOAUWKUXDUWCUYNYNSVVDWBYTYSVUS
      VUHVWNVXAVUSVXBQXEYSYSUVMXAUDUXFVVKCVVOUWCVUHUXKVVKOZVWMUVNYQVUSVVAVVJVVL
      XPVURVVAVUOAVVAVUMVVBSSVVKCUXDVUHUWCUXEVUIVXGUVOPXNUWCUWIUWDDVVGUXDEVVGOV
      XFUVPUVQVXEYSUVRPUVSUVTUWAWSUAUWEYAYQ $.
  $}

  ${
    $d A a e f l $.  $d A b $.  $d A l x $.  $d K a e f l $.  $d K b m $.
    $d K l m x $.  $d L e l $.  $d N a e f l $.  $d N b m $.  $d N l m x $.
    $d P a e f l $.  $d P b m $.  $d P l m x $.  $d R a e f l $.  $d R b m $.
    $d R l m x $.  $d S e l $.  $d a l m ph $.  $d b m ph $.  $d ph x $.
    aks5lem7.1 $e |- ( ph -> ( # ` ( Base ` K ) ) e. NN ) $.
    aks5lem7.2 $e |- P = ( chr ` K ) $.
    aks5lem7.3 $e |- ( ph -> K e. Field ) $.
    aks5lem7.4 $e |- ( ph -> P e. Prime ) $.
    aks5lem7.5 $e |- ( ph -> R e. NN ) $.
    aks5lem7.6 $e |- ( ph -> N e. ( ZZ>= ` 3 ) ) $.
    aks5lem7.7 $e |- ( ph -> P || N ) $.
    aks5lem7.8 $e |- ( ph -> ( N gcd R ) = 1 ) $.
    aks5lem7.9 $e |- A = ( |_ ` ( ( sqrt ` ( phi ` R ) ) x.
     ( 2 logb N ) ) ) $.
    aks5lem7.10 $e |- ( ph -> ( ( 2 logb N ) ^ 2 ) <
     ( ( odZ ` R ) ` N ) ) $.
    aks5lem7.11 $e |- ( ph -> R || ( ( # ` ( Base ` K ) ) - 1 ) ) $.
    aks5lem7.12 $e |- ( ph -> A. a e. ( 1 ... A ) [ ( N ( .g ` ( mulGrp `
    S ) ) ( X ( +g ` S ) ( ( ZRHom ` S ) ` a ) ) ) ]
      ( S ~QG L ) = [ ( ( N ( .g ` ( mulGrp ` S ) ) X ) ( +g ` S )
       ( ( ZRHom ` S ) ` a ) ) ] ( S ~QG L ) ) $.
    aks5lem7.13 $e |- ( ph -> A. b e. ( 1 ... A ) ( b gcd N ) = 1 ) $.
    aks5lem7.14 $e |- S = ( Poly1 ` ( Z/nZ ` N ) ) $.
    aks5lem7.15 $e |- L = ( ( RSpan ` S ) ` { ( ( R ( .g ` ( mulGrp ` S ) )
      X ) ( -g ` S ) ( 1r ` S ) ) } ) $.
    aks5lem7.16 $e |- X = ( var1 ` ( Z/nZ ` N ) ) $.
    ${
      $( Lemma for aks5.  We clean up the hypotheses compared to ~ aks5lem6 .
         (Contributed by metakunt, 9-Aug-2025.) $)
      aks5lem7 $p |- ( ph -> N = ( P ^ ( P pCnt N ) ) ) $=
        ( vm vx vl ve vf cv cmgp cfv cprimroots co wcel cpc cexp wceq wa cn cbs
        cpl1 ce1 cmg wral w3a copab eqid cfield adantr cprime c3 cuz cdvds cgcd
        wbr c1 c2 clogb codz clt cmpt crs crh wf1o cidom fldidom syl idomcringd
        frobrhm wf1 fldhmf1 cen cfn wb cvv fvexd eqeng mpisyl chash cn0 hashclb
        nnnn0d mpbird f1finf1o syl2anc mpbid jca isrim sylibr simpr cfz cur csg
        csn crsp czn cv1 oveq2i oveq1i sneqi fveq2i eqtri czrh cqg cec aks5lem6
        cplusg c0 wne wrex cui cress cmin c0g cdif fveq2d crg cdr isdrng biimpi
        flddrngd simprd cgrp simpld ringgrp grpidcl hashdifsn eqtr2d wss mgpbas
        eqcomi unitss a1i ressbas2 eqtrd breqtrd unitscyglem5 n0rex r19.29a ) A
        UHUMZFUNUOZDUPUQZURZHCCHUSUQUTUQVAZUHUVFAUVGVBZUVHUVGUVIUIUJBCUKUMZVCUR
        ULUMZFVEUOVDUOURUVJUJUMZUVKFVFUOUOZUOUVEVGUOZUQUVJUVLUVNUQUVMUOVAUJUVFV
        HVIUKULVJZDEUKULFGUVDHIJKUVOVKMAFVLURZUVGNVMACVNURUVGOVMADVCURUVGPVMAHV
        OVPUOURUVGQVMACHVQVSUVGRVMAHDVRUQVTVAUVGSVMTAWAHWBUQWAUTUQHDWCUOUOWDVSU
        VGUAVMAUIFVDUOZCUIUMUVNUQWEZFFWFUQURZUVGAUVRFFWGUQURZUVQUVQUVRWHZVBUVSA
        UVTUWAAUIUVQCFUVNUVRUVQVKZMUVNVKUVRVKAFAUVPFWIURNFWJWKZWLOWMZAUVQUVQUVR
        WNZUWAAUVQUVQUVRFFNNUWDUWBUWBWOAUVQUVQWPVSZUVQWQURZUWEUWAWRAUVQWSURZUVQ
        UVQVAUWFAFVDWTZUWBUVQUVQWSXAXBAUWGUVQXCUOZXDURZAUWJLXFAUWHUWGUWKWRUWIUV
        QWSXEWKXGZUVQUVQUVRXHXIXJXKUVQUVQFFUVRUWBUWBXLXMVMAUVGXNAKUMHVRUQVTVAKV
        TBXOUQZVHUVGUDVMUEGDIEUNUOVGUOZUQZEXPUOZEXQUOZUQZXRZEXSUOZUODHXTUOYAUOZ
        UWNUQZUWPUWQUQZXRZUWTUOUFUWSUXDUWTUWRUXCUWOUXBUWPUWQIUXADUWNUGYBYCYDYEY
        FUGAHIJUMEYGUOUOZEYKUOZUQUWNUQEGYHUQZYIHIUWNUQUXEUXFUQUXGYIVAJUWMVHUVGU
        CVMYJVMAUVFYLYMUVGUHUVFYNADFUVEFYOUOZYPUQZUXIVKZUWCUWLPADUWJVTYQUQZUXIV
        DUOZXCUOZVQUBAUXKUXHXCUOZUXMAUXNUVQFYRUOZXRYSZXCUOZUXKAUXHUXPXCAFUUAURZ
        UXHUXPVAZAFUUBURZUXRUXSVBZAFNUUEUXTUYAUVQFUXHUXOUWBUXHVKZUXOVKZUUCUUDWK
        ZUUFYTAUWGUXOUVQURZUXQUXKVAUWLAFUUGURZUYEAUXRUYFAUXRUXSUYDUUHFUUIWKUVQF
        UXOUWBUYCUUJWKUVQUXOUUKXIUULAUXHUXLXCAUXHUVEVDUOZUUMZUXHUXLVAUYHAUYGFUX
        HUVQUYGUVQFUVEUVEVKUWBUUNUUOUYBUUPUUQUXHUYGUXIUVEUXJUYGVKUURWKYTUUSUUTU
        VAUHUVFUVBWKUVC $.
    $}

    ${
      $d A a $.  $d A b $.  $d K a $.  $d K b $.  $d N a $.  $d N b $.
      $d N n p $.  $d P a $.  $d P b $.  $d P n p $.  $d R a $.  $d R b $.
      $d a ph $.  $d b ph $.  $d n p ph $.
      $( Lemma for aks5.  Clean up the conclusion.  (Contributed by metakunt,
         9-Aug-2025.) $)
      aks5lem8 $p |- ( ph -> E. p e. Prime E. n e. NN N = ( p ^ n ) ) $=
        ( cv cexp co wceq cn wrex cprime wa simpr oveq1d eqeq2d rexbidv cn0 cpc
        aks5lem7 wcel wb cz cc0 clt wbr c3 cuz cfv eluzelz syl 0red cr 3re zred
        a1i cle eluzle ltletrd elnnz sylibr pcprmpw syl2anc mpbird simprl nn0zd
        3pos jca wn nn0red lenltd bicomd biimpd imp wi adantr nn0le0eq0 simplrr
        c1 oveq2d ad2antrr prmnn nncnd exp0d eqtrd 1red nnred 1lt3 ltned necomd
        neneqd pm2.21dd ex mpd pm2.61dan simprr reximssdv rspcedvd ) AIKUJZFUJZ
        UKULZUMZFUNUOICYDUKULZUMZFUNUOKCUPQAYCCUMZUQZYFYHFUNYJYEYGIYJYCCYDUKAYI
        URUSUTVAAYHYHFUNVBAYHFVBUOZICCIVCULUKULUMZABCDEGHIJLMNOPQRSTUAUBUCUDUEU
        FUGUHUIVDACUPVEZIUNVEZYKYLVFQAIVGVEZVHIVIVJZUQYNAYOYPAIVKVLVMVEZYOSVKIV
        NVOZAVHVKIAVPVKVQVEAVRVTZAIYRVSVHVKVIVJAWKVTAYQVKIWAVJSVKIWBVOZWCWLIWDW
        EZICFWFWGWHAYDVBVEZYHUQZUQZYDVGVEZVHYDVIVJZUQYDUNVEUUDUUEUUFUUDYDAUUBYH
        WIZWJUUDUUFUUFUUDUUFURUUDUUFWMZUQYDVHWAVJZUUFUUDUUHUUIUUDUUHUUIUUDUUIUU
        HUUDYDVHUUDYDUUGWNUUDVPWOWPWQWRUUDUUIUUFWSUUHUUDUUIUUFUUDUUIUQZYDVHUMZU
        UFUUJUUKUUIUUDUUIURUUJUUBUUKUUIVFUUDUUBUUIUUGWTUUBUUIUUKYDXAWPVOWHUUDUU
        KUUFWSUUIUUDUUKUUFUUDUUKUQZIXCUMUUFUULIYGXCAUUBYHUUKXBUULYGCVHUKULXCUUL
        YDVHCUKUUDUUKURXDUULCUULCUULYMCUNVEAYMUUCUUKQXECXFVOXGXHXIXIUULIXCUULXC
        IUULXCIUULXJUUDXCIVIVJZUUKAUUMUUCAXCVKIAXJYSAIUUAXKXCVKVIVJAXLVTYTWCWTW
        TXMXNXOXPXQWTXRXQWTXRXSWLYDWDWEAUUBYHXTYAYB $.
    $}
  $}

  ${
    $d p n k $.
    $( Existence axiom for finite fields, eventually we want to construct them.
       (Contributed by metakunt, 13-Jul-2025.) $)
    ax-exfinfld $a |- A. p e. Prime A. n e. NN E. k e. Field
    ( ( # ` ( Base ` k ) ) = ( p ^ n ) /\ ( chr ` k ) = p ) $.
  $}

  ${
    $d N k n $.  $d P k n p $.
    exfinfldd.1 $e |- ( ph -> P e. Prime ) $.
    exfinfldd.2 $e |- ( ph -> N e. NN ) $.
    $( For any prime ` P ` and any positive integer ` N ` there exists a field
       ` k ` such that ` k ` contains ` P ^ N ` elements.  (Contributed by
       metakunt, 13-Jul-2025.) $)
    exfinfldd $p |- ( ph -> E. k e. Field
     ( ( # ` ( Base ` k ) ) = ( P ^ N ) /\ ( chr ` k ) = P ) ) $=
      ( vn vp cv cfv cexp co wceq wa cfield wrex cn eqeq2d rexbidv wral anbi12d
      cbs chash oveq2 anbi1d cprime oveq1 eqeq2 ralbidv ax-exfinfld a1i rspcdva
      cchr ) ACIZUBJUCJZBGIZKLZMZUNUMJZBMZNZCOPZUOBDKLZMZUTNZCOPGQDUPDMZVAVECOV
      FURVDUTVFUQVCUOUPDBKUDRUESAUOHIZUPKLZMZUSVGMZNZCOPZGQTZVBGQTHUFBVGBMZVLVB
      GQVNVKVACOVNVIURVJUTVNVHUQUOVGBUPKUGRVGBUSUHUASUIVMHUFTACGHUJUKEULFUL $.
  $}

  ${
    $d A a $.  $d N a k q $.  $d N k n p q $.  $d R a k $.  $d R k n p $.
    $d a k ph q $.  $d n p ph q $.
    aks5.1 $e |- A = ( |_ ` ( ( sqrt ` ( phi ` R ) ) x.
     ( 2 logb N ) ) ) $.
    aks5.2 $e |- X = ( var1 ` ( Z/nZ ` N ) ) $.
    aks5.3 $e |- S = ( Poly1 ` ( Z/nZ ` N ) ) $.
    aks5.4 $e |- L = ( ( RSpan ` S ) ` { ( ( R ( .g ` ( mulGrp ` S ) )
      X ) ( -g ` S ) ( 1r ` S ) ) } ) $.
    aks5.5 $e |- ( ph -> N e. ( ZZ>= ` 3 ) ) $.
    aks5.6 $e |- ( ph -> R e. NN ) $.
    aks5.7 $e |- ( ph -> ( N gcd R ) = 1 ) $.
    aks5.8 $e |- ( ph -> ( ( 2 logb N ) ^ 2 ) < ( ( odZ ` R ) ` N ) ) $.
    aks5.9 $e |- ( ph -> A. a e. ( 1 ... A ) [ ( N ( .g ` ( mulGrp `
    S ) ) ( X ( +g ` S ) ( ( ZRHom ` S ) ` a ) ) ) ]
      ( S ~QG L ) = [ ( ( N ( .g ` ( mulGrp ` S ) ) X ) ( +g ` S )
       ( ( ZRHom ` S ) ` a ) ) ] ( S ~QG L ) ) $.
    aks5.10 $e |- ( ph -> A. a e. ( 1 ... A ) ( a gcd N ) = 1 ) $.
    $( The AKS Primality test, given an integer ` N ` greater than or equal to
       3, find a coprime ` R ` such that ` R ` is big enough.  Then, if a bunch
       of polynomial equalities in the residue ring hold then ` N ` is a prime
       power.  Currently depends on the axiom ~ ax-exfinfld , since we
       currently do not have the existence of finite fields in the database.
       (Contributed by metakunt, 16-Aug-2025.) $)
    aks5 $p |- ( ph -> E. p e. Prime E. n e. NN N = ( p ^ n ) ) $=
      ( vq vk cv cdvds wbr cexp co wceq cn wrex cprime wcel cbs chash codz cchr
      wa cfv cfield simprl simplr ad2antrr prmnn syl cz cgcd c1 nnzd gcdcomd c3
      w3a cuz eluzelz 3jca eqtrd simpr jca rpdvds syl2anc odzcl nnnn0d nnexpcld
      syl3anc eqeltrd eqid simprr ad4antr simpllr eqbrtrd clogb clt cmin eqcomd
      odzid oveq1d breqtrd czrh cplusg cmgp cmg cqg cec wral aks5lem8 exfinfldd
      c2 cfz r19.29a uzuzle23 exprmfct ) AUAUCZGUDUEZGIUCEUCUFUGUHEUIUJIUKUJZUA
      UKAXKUKULZUQZXLUQZUBUCZUMURUNURZXKXKCUOURZURZUFUGZUHZXQUPURZXKUHZUQZXMUBU
      SXPXQUSULZUQZYEUQZBYCCDEXQFGHIJJYHXRYAUIYGYBYDUTZYHXKXTYHXNXKUIULZXPXNYFY
      EAXNXLVAZVBZXKVCZVDZYHXTXPXTUIULZYFYEXPCUIULZXKVEULZXKCVFUGZVGUHZYOAYPXNX
      LPVBZXPXKXPXNYJYKYMVDVHZXPYRCXKVFUGZVGXPXKCUUAXPCYTVHZVIXPCVEULZYQGVEULZV
      KCGVFUGZVGUHZXLUQUUBVGUHXPUUDYQUUEUUCUUAXPGVJVLURULZUUEAUUHXNXLOVBVJGVMVD
      ZVNXPUUGXLXPUUFGCVFUGZVGXPCGUUCUUIVIAUUJVGUHZXNXLQVBVOXOXLVPVQCXKGVRVSVOZ
      XKCVTWCZVBWAWBWDYCWEXPYFYEVAYHYCXKUKYGYBYDWFZYLWDAYPXNXLYFYEPWGZAUUHXNXLY
      FYEOWGYHYCXKGUDUUNXOXLYFYEWHWIAUUKXNXLYFYEQWGKAXFGWJUGXFUFUGGXSURWKUEXNXL
      YFYERWGYHCYAVGWLUGZXRVGWLUGUDYHYPYQYSCUUPUDUEUUOYHXKYNVHXPYSYFYEUULVBXKCW
      NWCYHYAXRVGWLYHXRYAYIWMWOWPAGHJUCZDWQURURZDWRURZUGDWSURWTURZUGDFXAUGZXBGH
      UUTUGUURUUSUGUVAXBUHJVGBXGUGZXCXNXLYFYESWGAUUQGVFUGVGUHJUVBXCXNXLYFYETWGM
      NLXDXPXKUBXTYKUUMXEXHAGXFVLURULZXLUAUKUJAUUHUVCOGXIVDGUAXJVDXH $.
  $}


$( (End of metakunt's mathbox.) $)
