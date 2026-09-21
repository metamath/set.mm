$[ set-main.mm $]
$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Mathbox for Steve Rodriguez
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Miscellanea
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( 'nand' is equivalent to the equivalence of inclusive and exclusive or.
     (Contributed by Steve Rodriguez, 28-Feb-2020.) $)
  nanorxor $p |- ( ( ph -/\ ps ) <->
                   ( ( ph \/ ps ) <-> ( ph \/_ ps ) ) ) $=
    ( wnan wa wn wo wxo wb df-nan xor2 rbaibr bibi2i wi pm4.71 simpl orcd con3i
    id ja sylbir sylbi impbii bitri ) ABCABDZEZABFZABGZHZABIUEUHUGUFUEABJZKUHUF
    UFUEDZHZUEUGUJUFUILUKUFUEMUEUFUENUFUEUEUDUFUDABABOPQUERSTUAUBUC $.

  $( Union of two disjoint restricted class abstractions; compare ~ unrab .
     (Contributed by Steve Rodriguez, 28-Feb-2020.) $)
  undisjrab $p |- ( ( { x e. A | ph } i^i { x e. A | ps } ) = (/) <->
                    ( { x e. A | ph } u. { x e. A | ps } ) =
                    { x e. A | ( ph \/_ ps ) } ) $=
    ( wa crab c0 wceq wo wxo cin cun wn wral rabeq0 wnan df-nan nanorxor eqeq1i
    wb bitr3i ralbii rabbi 3bitri inrab unrab 3bitr4i ) ABEZCDFZGHZABIZCDFZABJZ
    CDFZHZACDFZBCDFZKZGHUPUQLZUNHUJUHMZCDNUKUMTZCDNUOUHCDOUTVACDUTABPVAABQABRUA
    UBUKUMCDUCUDURUIGABCDUESUSULUNABCDUFSUG $.

  ${
    $d x y R $.  $d x y S $.
    $( The empty set is an ` R , S ` isomorphism from the empty set to the
       empty set.  (Contributed by Steve Rodriguez, 24-Oct-2015.) $)
    iso0 $p |- (/) Isom R , S ( (/) , (/) ) $=
      ( vx vy c0 wiso wf1o cv wbr cfv wb wral f1o0 ral0 df-isom mpbir2an ) EEAB
      EFEEEGCHZDHZAIQEJREJBIKDELZCELMSCNCDEEABEOP $.
  $}

  $( ` RR ` is a subset of both ` RR ` and ` CC ` .  (Contributed by Steve
     Rodriguez, 22-Nov-2015.) $)
  ssrecnpr $p |- ( S e. { RR , CC } -> RR C_ S ) $=
    ( cr cc cpr wcel wceq wo wss elpri eqimss2 ax-resscn sseq2 mpbiri jaoi syl
    ) ABCDEABFZACFZGBAHZABCIPRQBAJQRBCHKACBLMNO $.

  ${
    seff.s $e |- ( ph -> S e. { RR , CC } ) $.
    $( Let set ` S ` be the real or complex numbers.  Then the exponential
       function restricted to ` S ` is a mapping from ` S ` to ` S ` .
       (Contributed by Steve Rodriguez, 6-Nov-2015.) $)
    seff $p |- ( ph -> ( exp |` S ) : S --> S ) $=
      ( cr cc cpr wceq ce cres wf crp mp2b wb feq23 anidms mpbiri reseq2 mpbird
      feq1d eff wcel wo elpri wf1 reeff1 f1f wss rpssre fss mpan2 cdm wrel frel
      resdm fdmi reseq2i eqtr3i feq1i mpbi jaoi 3syl ) ABDEFUABDGZBEGZUBBBHBIZJ
      ZCBDEUCVBVEVCVBVEBBHDIZJZVBVGDDVFJZDKVFUDDKVFJZVHUEDKVFUFVIKDUGVHUHDKDVFU
      IUJLVBVGVHMBBDDVFNOPVBBBVDVFBDHQSRVCVEBBHEIZJZVCVKEEVJJZEEHJZVLTEEHVJHHUK
      ZIZHVJVMHULVOHGTEEHUMHUNLVNEHEEHTUOUPUQURUSVCVKVLMBBEEVJNOPVCBBVDVJBEHQSR
      UTVA $.
  $}

  ${
    sblpnf.s $e |- ( ph -> S e. { RR , CC } ) $.
    sblpnf.d $e |- D = ( ( abs o. - ) |` ( S X. S ) ) $.
    $( The infinity ball in the absolute value metric is just the whole space.
       ` S ` analogue of ~ blpnf .  (Contributed by Steve Rodriguez,
       8-Nov-2015.) $)
    sblpnf $p |- ( ( ph /\ P e. S ) -> ( P ( ball ` D ) +oo ) = S ) $=
      ( cmet cfv wcel wceq cr cc cabs cmin cxp cres xpeq12 anidms reseq2d wf co
      cpnf cbl cpr elpri ccom eqid remet fveq2 eleq12d mpbiri eqeltrid cdm wrel
      wo relco resdm ax-mp wss absf ax-resscn fss mp2an subf fco reseq2i eqtr3i
      fdmi cnmet eqeltrri jaoi 3syl blpnf sylan ) ABDGHZIZCDICUBBUCHUADJADKLUDI
      DKJZDLJZUOVPEDKLUEVQVPVRVQBMNUFZDDOZPZVOFVQWAVOIZVSKKOZPZKGHZIWDWDUGUHVQW
      AWDVOWEVQVTWCVSVQVTWCJDKDKQRSDKGUIUJUKULVRBWAVOFVRWBVSLLOZPZLGHZIVSWGWHVS
      VSUMZPZVSWGVSUNWJVSJMNUPVSUQURWIWFVSWFLVSLLMTZWFLNTWFLVSTLKMTKLUSWKUTVALK
      LMVBVCVDWFLLMNVEVCVHVFVGVIVJVRWAWGVOWHVRVTWFVSVRVTWFJDLDLQRSDLGUIUJUKULVK
      VLBCDVMVN $.
  $}

  ${
    $d n p A $.
    $( The primes are unbounded.  This generalizes ~ prmunb to real ` A ` with
       ~ arch and ~ lttrd : every real is less than some positive integer,
       itself less than some prime.  (Contributed by Steve Rodriguez,
       20-Jan-2020.) $)
    prmunb2 $p |- ( A e. RR -> E. p e. Prime A < p ) $=
      ( vn cr wcel cv clt wbr cprime wrex cn wa simplll nnre ad3antlr prmz zred
      ad2antlr sylibr c1 simprl simprr wral arch prmunb r19.29r sylancl r19.42v
      lttrd rgen rexbii reximddv2 c0 wne wb 1nn ne0i r19.9rzv mp2b ) ADEZABFZGH
      ZBIJZCKJZVCUTACFZGHZVEVAGHZLZVBCBKIUTVEKEZLZVAIEZLZVHLAVEVAUTVIVKVHMVIVED
      EUTVKVHVENOVKVADEVJVHVKVAVAPQRVLVFVGUAVLVFVGUBUIUTVFVGBIJZLZCKJZVHBIJZCKJ
      UTVFCKJVMCKUCVOACUDVMCKVEBUEUJVFVMCKUFUGVPVNCKVFVGBIUHUKSULTKEKUMUNVCVDUO
      UPKTUQVCCKURUSS $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Ratio test for infinite series convergence and divergence
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d i k ph $.  $d i k F $.  $d i k N $.  $d i k W $.  $d k M $.  $d k V $.
    $d k Z $.
    dvgrat.z $e |- Z = ( ZZ>= ` M ) $.
    dvgrat.w $e |- W = ( ZZ>= ` N ) $.
    dvgrat.n $e |- ( ph -> N e. Z ) $.
    dvgrat.f $e |- ( ph -> F e. V ) $.
    dvgrat.c $e |- ( ( ph /\ k e. Z ) -> ( F ` k ) e. CC ) $.
    dvgrat.n0 $e |- ( ( ph /\ k e. W ) -> ( F ` k ) =/= 0 ) $.
    dvgrat.le $e |- ( ( ph /\ k e. W ) ->
        ( abs ` ( F ` k ) ) <_ ( abs ` ( F ` ( k + 1 ) ) ) ) $.
    $( Ratio test for divergence of a complex infinite series.  See e.g. remark
       "if ` ( abs `` ( ( a `` ( n + 1 ) ) / ( a `` n ) ) ) >_ 1 ` for all
       large n..." in ~ https://en.wikipedia.org/wiki/Ratio_test#The_test .
       (Contributed by Steve Rodriguez, 28-Feb-2020.) $)
    dvgrat $p |- ( ph -> seq M ( + , F ) e/ dom ~~> ) $=
      ( wcel cc0 cfv cabs wi vi caddc cseq cli cdm wn wnel wbr cle clt eleqtrdi
      cz cuz eluzelz syl uzid eleqtrrdi cv wceq wa eleq1d fveq2d breq2d imbi12d
      simpr wne cc wb eleq2i uztrn2 sylan2b sylan syldan absgt0 mpbid ex vtocld
      mpd 0red abscld ltnled cmpt adantr cvv fvexi mptex a1i adantlr eqidd fvex
      cr fvmptd climabs breqtrdi eqeltrd c1 2fveq3 imbi2d leidd expcom ad2antrr
      abs0 co peano2uzs ovex eleq1 anbi2d fveq2 vtocl sylan2 letrd sylan2br a2d
      chvarvv uzind4 impcom breqtrrd climlec2 mtand eluzel2 serf0 df-nel sylibr
      ) AUBCDUCZUDUEZPZUFYDYEUGAYFCQUDUHZAYGECRZSRZQUIUHZAQYIUJUHZYJUFAEGPZYKAE
      ULPZYLAEDUMRZPZYMAEHYNKIUKZDEUNUOZYMEEUMRZGEUPJUQUOABURZGPZQYSCRZSRZUJUHZ
      TYLYKTBEHKAYSEUSZUTZYTYLUUCYKUUEYSEGAUUDVEZVAUUEUUBYIQUJUUEUUAYHSUUEYSECU
      UFVBZVBVCVDAYTUUCAYTUTZUUAQVFZUUCNUUHUUAVGPZUUIUUCVHAYTYSHPZUUJAEHPZYTUUK
      KYTUULYSYRPZUUKGYRYSJVIZDYSEHIVJVKVLMVMZUUAVNUOVOVPVQVRAQYIAVSAYHAUULYHVG
      PZKAUUKUUJTUULUUPTBEHKUUEUUKUULUUJUUPUUEYSEHUUFVAUUEUUAYHVGUUGVAVDAUUKUUJ
      MVPVQVRVTZWAVOAYGUTZYIQBUAGUAURZCRZSRZWBZEGJAYMYGYQWCZAYIWKPZYGUUQWCUURUV
      BQSRQUDUURQBCUVBEWDGJAYGVEUVBWDPUURUAGUVAGEUMJWEWFWGUVCAYTUUJYGUUOWHZUURY
      TUTZUAYSUVAUUBGUVBWDUVFUVBWIUVFUUSYSUSZUTZUUTUUASUVHUUSYSCUVFUVGVEVBVBUUR
      YTVEUUBWDPUVFUUASWJWGWLZWMXBWNUVFYSUVBRZUUBWKUVIUVFUUAUVEVTWOUVFYIUUBUVJU
      IAYTYIUUBUIUHZYGYTAUUMUVKUUNUUMAUVKAYIUVAUIUHZTAYIYIUIUHZTAUVKTZAYIYSWPUB
      XCZCRZSRZUIUHZTUVNUABEYSUUSEUSZUVLUVMAUVSUVAYIYIUIUUSESCWQVCWRUVGUVLUVKAU
      VGUVAUUBYIUIUUSYSSCWQVCWRZUUSUVOUSZUVLUVRAUWAUVAUVQYIUIUUSUVOSCWQVCWRUVTA
      YMUVMAYMUTYIAUVDYMUUQWCWSWTUUMAUVKUVRAUUMUVKUVRTZUUMAYTUWBUUNUUHUVKUVRUUH
      UVKUTZYIUUBUVQAUVDYTUVKUUQXAUWCUUAUUHUUJUVKUUOWCVTUWCUVPUUHUVPVGPZUVKYTAU
      VOGPZUWDEYSGJXDAUUSGPZUTZUUTVGPZTZAUWEUTZUWDTUAUVOYSWPUBXEUWAUWGUWJUWHUWD
      UWAUWFUWEAUUSUVOGXFXGUWAUUTUVPVGUUSUVOCXHVAVDUUHUUJTUWIBUAYSUUSUSZUUHUWGU
      UJUWHUWKYTUWFAYSUUSGXFXGUWKUUAUUTVGYSUUSCXHVAVDUUOXNXIXJWCVTUUHUVKVEUUHUU
      BUVQUIUHUVKOWCXKVPXLWTXMXOXPVKWHUVIXQXRXSAYFUTBCDFHIADULPZYFAYOUWLYPDEXTU
      OWCACFPYFLWCAYFVEAUUKUUJYFMWHYAXSYDYEYBYC $.
  $}

  ${
    $d i k n r ph $.  $d i k n r F $.  $d i k n r L $.  $d i k n r N $.
    $d i k n W $.  $d k n R $.  $d k M $.  $d i V $.  $d k Z $.
    cvgdvgrat.z $e |- Z = ( ZZ>= ` M ) $.
    cvgdvgrat.w $e |- W = ( ZZ>= ` N ) $.
    cvgdvgrat.n $e |- ( ph -> N e. Z ) $.
    cvgdvgrat.f $e |- ( ph -> F e. V ) $.
    cvgdvgrat.c $e |- ( ( ph /\ k e. Z ) -> ( F ` k ) e. CC ) $.
    cvgdvgrat.n0 $e |- ( ( ph /\ k e. W ) -> ( F ` k ) =/= 0 ) $.
    cvgdvgrat.r $e |- R = ( k e. W |-> ( abs ` ( ( F ` ( k + 1 ) ) /
        ( F ` k ) ) ) ) $.
    cvgdvgrat.cvg $e |- ( ph -> R ~~> L ) $.
    cvgdvgrat.n1 $e |- ( ph -> L =/= 1 ) $.
    $( Ratio test for convergence and divergence of a complex infinite series.
       If the ratio ` R ` of the absolute values of successive terms in an
       infinite sequence ` F ` converges to less than one, then the infinite
       sum of the terms of ` F ` converges to a complex number; and if ` R `
       converges _greater_ then the sum diverges.  This combined form of
       ~ cvgrat and ~ dvgrat directly uses the limit of the ratio.

       (It also demonstrates how to use ~ climi2 and ~ absltd to transform a
       limit to an inequality cf. ~ https://math.stackexchange.com/q/2215191 ,
       and how to use ~ r19.29a in a similar fashion to Mario Carneiro's proof
       sketch with ~ rexlimdva at
       ~ https://groups.google.com/g/metamath/c/2RPikOiXLMo .)  (Contributed by
       Steve Rodriguez, 28-Feb-2020.) $)
    cvgdvgrat $p |- ( ph -> ( L < 1 <-> seq M ( + , F ) e. dom ~~> ) ) $=
      ( c1 vr vn vi clt wbr caddc cseq cli cdm wcel wa cioo co wral cv cfv cabs
      cmul cle cuz eqid cr elioore ad3antlr w3a cxr wb cz eleqtrdi eluzelz cdiv
      syl cmpt wceq a1i cc peano2uzs wi ovex eleq1 anbi2d eleq1d imbi12d eleq2i
      fveq2 uztrn2 sylan2b syldan chvarvv sylan2 divcld abscld fvmpt2d climrecl
      sylan vtocl eqeltrd rexrd 1xr sylancl biimpa simplr ad3antrrr imp breq12d
      ex fveq2d rspccva adantll cmin wrex adantr crp difrp mpbid adantlr climi2
      anassrs adantllr cc0 wne absdivd resubcld absltd ad4antr ltsub1d eqbrtrrd
      cneg mpbird absrpcld rpcnd recnd breqtrd ralimdva reximdva mpd r19.29a wn
      ltled 1red elioo2 simp3d ad2antrr fvoveq1 oveq2d cvgrat ad4antlr remulcld
      simp2d syl2an simplbda ltdivmuld mulcomd ralrimiva ioon0 biimpar r19.3rzv
      c0 iserex wo lttri2d orcanai neeq1d dvgrat 1re sylancr mullidd negsubdi2d
      wnel 1cnd simprbda ltmuldivd df-nel sylib mtbird impcon4bid ) AETUDUEZUFD
      FUGUHUIZUJZAUVQUVSAUVQUKZUVSUFDGUGZUVRUJZUVTUWBUWBUAETULUMZUNZAUWDUVQAUWB
      UAUWCAUAUOZUWCUJZUKZCUOZTUFUMZDUPZUQUPZUWEUWHDUPZUQUPZURUMZUSUEZCUBUOZUTU
      PZUNZUWBUBIUWGUWPIUJZUKZUWRUKZUWEUCDGUWPUWQILUWQVAZUWFUWEVBUJZAUWSUWRUWEE
      TVCZVDUWGUWETUDUEZUWSUWRUWGUXCEUWEUDUEZUXEAUWFUXCUXFUXEVEZAEVFUJZTVFUJZUW
      FUXGVGAEAECBGILAGFUTUPZUJGVHUJZAGJUXJMKVIFGVJVLZRAUWHIUJZUKZUWHBUPZUWJUWL
      VKUMZUQUPZVBACIUXQBVBBCIUXQVMVNAQVOUXNUXPUXNUWJUWLUXMAUWIIUJZUWJVPUJZGUWH
      ILVQAUCUOZIUJZUKZUXTDUPZVPUJZVRZAUXRUKZUXSVRUCUWIUWHTUFVSUXTUWIVNZUYBUYFU
      YDUXSUYGUYAUXRAUXTUWIIVTWAUYGUYCUWJVPUXTUWIDWEWBWCUXNUWLVPUJZVRUYECUCUWHU
      XTVNZUXNUYBUYHUYDUYIUXMUYAAUWHUXTIVTWAZUYIUWLUYCVPUWHUXTDWEZWBWCAUXMUWHJU
      JZUYHUXMAUWHGUTUPZUJZUYLIUYMUWHLWDAGJUJUYNUYLMFUWHGJKWFWOWGOWHZWIZWPWJZUY
      OPWKWLZWMZUYRWQWNZWRZWSETUWEUUAWTXAZUUBUUCUWGUWSUWRXBUXAUYAUYDAUYAUYDVRZU
      WFUWSUWRAUYAUYDUYPXFZXCXDUWRUXTUWQUJZUXTTUFUMDUPZUQUPZUWEUYCUQUPZURUMZUSU
      EZUWTUWOVUJCUXTUWQUYIUWKVUGUWNVUIUSUYIUWJVUFUQUWHUXTTDUFUUDXGZUYIUWMVUHUW
      EURUYIUWLUYCUQUYKXGZUUEXEXHXIUUFUWGUXQEXJUMZUQUPZUWEEXJUMZUDUEZCUWQUNZUBI
      XKUWRUBIXKUWGEUXQVUOUBCBGILAUXKUWFUXLXLUWGUXFVUOXMUJZUWGUXCUXFUXEVUBUUIAE
      VBUJZUXCUXFVURVGUWFUYTUXDEUWEXNUUJXOAUXMUXOUXQVNZUWFUYSXPABEUHUEZUWFRXLXQ
      UWGVUQUWRUBIUWTVUPUWOCUWQUWTUWHUWQUJZUKZVUPUWOVVCVUPUKZUWKUWNVVDUWJVVCUXS
      VUPAUWSVVBUXSUWFAUWSVVBUXSUWSVVBUKZAUXMUXSGUWHUWPILWFZUYQWJXRZXSZXLZWLZVV
      DUWEUWMUWFUXCAUWSVVBVUPUXDUUGZVVDUWLVVCUYHVUPAUWSVVBUYHUWFAUWSVVBUYHVVEAU
      XMUYHVVFUYOWJXRZXSZXLZWLUUHVVDUWKUWMUWEURUMZUWNUDVVDUWKUWMVKUMZUWEUDUEUWK
      VVOUDUEVVDUXQVVPUWEUDVVDUWJUWLVVIVVNVVCUWLXTYAZVUPAUWSVVBVVQUWFAUWSVVBVVQ
      VVEAUXMVVQVVFPWJXRZXSZXLZYBVVDUXQUWEUDUEVUMVUOUDUEZVVCVUPVUOYHVUMUDUEVWAV
      VCVUMVUOVVCUXQEVVCUXPVVCUWJUWLVVHVVMVVSWKWLAVUSUWFUWSVVBUYTXCZYCVVCUWEEUW
      FUXCAUWSVVBUXDVDVWBYCYDUUKVVDUXQUWEEVVDUXPVVDUWJUWLVVIVVNVVTWKWLVVKAVUSUW
      FUWSVVBVUPUYTYEYFYIYGVVDUWKUWEUWMVVJVVKVVDUWLVVNVVTYJZUULXOVVDUWMUWEVVDUW
      MVWCYKVVDUWEVVKYLUUMYMYSXFYNYOYPYQUUNXLUVTUWCUURYAZUWBUWDVGAVWDUVQAUXHUXI
      VWDUVQVGVUAWSETUUOWTUUPUWBUAUWCUUQVLYIAUVSUWBVGZUVQACDFGJKMOUUSZXLYIXFAUV
      QYRZUVSYRZAVWGTEUDUEZVWHAUVQVWIAETYAUVQVWIUUTSAETUYTAYTUVAXOUVBAVWIUKZUVS
      UWBVWJUWAUVRUVIZUWBYRVWJUWMUWKUSUEZCUWQUNZVWKUBIVWJUWSUKZVWMUKZUCDGUWPHUW
      QILUXBVWJUWSVWMXBADHUJVWIUWSVWMNXCVWOUYAUYDAVUCVWIUWSVWMVUDXCXDVWNVUEUYCX
      TYAZVWMAUWSVUEVWPVWIAUWSVUEVWPUWSVUEUKAUYAVWPGUXTUWPILWFUXNVVQVRUYBVWPVRC
      UCUYIUXNUYBVVQVWPUYJUYIUWLUYCXTUYKUVCWCPWIWJXRXSXPVWMVUEVUHVUGUSUEZVWNVWL
      VWQCUXTUWQUYIUWMVUHUWKVUGUSVULVUKXEXHXIUVDVWJVUNETXJUMZUDUEZCUWQUNZUBIXKV
      WMUBIXKVWJEUXQVWRUBCBGILAUXKVWIUXLXLAVWIVWRXMUJZATVBUJVUSVWIVXAVGUVEUYTTE
      XNUVFXAAUXMVUTVWIUYSXPAVVAVWIRXLXQVWJVWTVWMUBIVWNVWSVWLCUWQVWNVVBUKZVWSVW
      LVXBVWSUKZUWMUWKVXCUWLVXBUYHVWSAUWSVVBUYHVWIVVLXSZXLZWLVXCUWJVXBUXSVWSAUW
      SVVBUXSVWIVVGXSZXLZWLZVXCTUWMURUMZUWMUWKUDVXCUWMVXCUWMVXCUWLVXEVXBVVQVWSA
      UWSVVBVVQVWIVVRXSZXLZYJZYKUVGVXCVXIUWKUDUETVVPUDUEVXCTUXQVVPUDVXCTUXQUDUE
      TEXJUMZVUMUDUEVXCVWRYHZVXMVUMUDVXCETVXCEAVUSVWIUWSVVBVWSUYTYEZYLVXCUVJUVH
      VXBVWSVXNVUMUDUEVUMVWRUDUEVXBVUMVWRVXBUXQEVXBUXPVXBUWJUWLVXFVXDVXJWKWLAVU
      SVWIUWSVVBUYTXCZYCVXBETVXPVXBYTYCYDUVKYGVXCTUXQEVXCYTZVXCUXPVXCUWJUWLVXGV
      XEVXKWKWLVXOYFYIVXCUWJUWLVXGVXEVXKYBYMVXCTUWKUWMVXQVXHVXLUVLYIYGYSXFYNYOY
      PYQUWAUVRUVMUVNAVWEVWIVWFXLUVOWHXFUVP $.
  $}

  ${
    $d k n x ph $.  $d n x A $.  $d k n x G $.  $d k r x G $.  $d k x L $.
    $d k n Z $.  $d k D $.  $d k M $.
    $( pser.g $)
    radcnvrat.g $e |- G = ( x e. CC |-> ( n e. NN0 |->
        ( ( A ` n ) x. ( x ^ n ) ) ) ) $.
    $( radcnv.a $)
    radcnvrat.a $e |- ( ph -> A : NN0 --> CC ) $.
    $( radcnv.r $)
    radcnvrat.r $e |- R =
        sup ( { r e. RR | seq 0 ( + , ( G ` r ) ) e. dom ~~> } , RR* , < ) $.
    radcnvrat.rat $e |- D = ( k e. NN0 |->
        ( abs ` ( ( A ` ( k + 1 ) ) / ( A ` k ) ) ) ) $.
    radcnvrat.z $e |- Z = ( ZZ>= ` M ) $.
    radcnvrat.m $e |- ( ph -> M e. NN0 ) $.
    radcnvrat.n0 $e |- ( ( ph /\ k e. Z ) -> ( A ` k ) =/= 0 ) $.
    radcnvrat.l $e |- ( ph -> D ~~> L ) $.
    radcnvrat.ln0 $e |- ( ph -> L =/= 0 ) $.
    $( Let ` L ` be the limit, if one exists, of the ratio
       ` ( abs `` ( ( A `` ( k + 1 ) ) / ( A `` k ) ) ) ` (as in the ratio test
       ~ cvgdvgrat ) as ` k ` increases.  Then the radius of convergence of
       power series ` sum_ n e. NN0 ( ( A `` n ) x. ( x ^ n ) ) ` is
       ` ( 1 / L ) ` if ` L ` is nonzero.  Proof "The limit involved in the
       ratio test..." in ~ https://en.wikipedia.org/wiki/Radius_of_convergence
       &mdash;a few lines that evidently hide quite an involved process to
       confirm.  (Contributed by Steve Rodriguez, 8-Mar-2020.) $)
    radcnvrat $p |- ( ph -> R = ( 1 / L ) ) $=
      ( caddc cv cfv cc0 cseq cli cdm wcel cr crab cxr clt csup c1 cdiv wor a1i
      co cres nn0zd reseq2i wbr cvv wb cn0 cabs cmpt nn0ex mptex climres mpbird
      sylancl wa sylan ex ssrdv resmptd eqtrid fvmpt2d sselda ffvelcdmda syldan
      fvexd cc sylan2 abscld eqeltrd rexrd wn simpr wi wne cle adantr cmul wceq
      adantl 1cnd recnd eqcom biimpa breqtrrd cdif syl fveq2 oveq1d imp adantlr
      ad2antrr eldifi cexp oveq12d fvmptd simplr expcld sylanl2 ad2antlr fveq2d
      wss ovexd oveq2d cmin 3eqtrd biimpd impancom mpd cioo wrex iooss1 wral c0
      an32s ioon0 ancoms r19.2zb sylib ssrexv sylbird syl2anc xrltso cz eqeltri
      eqbrtrid reseq1i eluznn0 eqsstrid peano2uzs divcld climrecl rereccld recn
      elrabi ltlend simplbda biantrud lenltd 3bitr2d divmul3d 3bitr3g necon3bid
      cuz 1red crp fvres eqeltrrd absge0d breqtrd climge0 ne0gt0d ltmuldivd csn
      elrpd cin cun elun inundif eleq2i bitr3i elin simprbi elsni eqtrdi mul02d
      wo abs0 sylan9eqr 0lt1 eqbrtrdi radcnv0 eleq1 syl5ibrcom 2thd ssdif ax-mp
      sseli nn0uz oveq2 mulcld eldifsni expne0d mulne0d eqnetrd fvoveq1 cbvmptv
      ax-resscn eqtr3id eqidd nn0addcld divmuldivd nn0cnd pncan2d expsubd exp1d
      3eqtr3d 3eqtr2d absmuld eqtr3d eqcomd mulcomd climmulc2 cvgdvgrat seqeq3d
      eqbrtrrd eleq1d elrab3 bitr4d jaodan sylan2br bitr3d notbid bitrd ltletrd
      1nn0 con2d leabsd nsyld cneg renegcld eliooord simpld rgen biimpar anasss
      sylc xrltnle ralrimiva recgt0d addgt0d subnegd posdifd adantlrr pm2.61dan
      mpi xrltle w3a elioo2 absltd ltned impr expcom 3impb impcom eqsupd ) AEUB
      LUCZHUDZUEUFZUGUHZUIZLUJUKZULUMUNUOIUPUSZOABFULVVJVVKUMULUMUQAUUAURAVVKAI
      AIFDKUTZJKQAJRVAZAVVLDJUVBUDZUTZIUGKVVNDQVBAVVOIUGVCZDIUGVCZTAJUUBUIZDVDU
      IVVPVVQVEVVMDFVFFUCZUOUBUSZCUDZVVSCUDZUPUSZVGUDZVHZVDPFVFVWDVIVJUUCIDJVDV
      KVMVLUUDAVVSKUIZVNZVVSVVLUDZVWDUJAFKVWDVVLVDAVVLVWEKUTFKVWDVHDVWEKPUUEAFV
      FKVWDAKVVNVFQAFVVNVFAVVSVVNUIZVVSVFUIZAJVFUIZVWIVWJRVVSJUUFVOVPVQUUGZVRVS
      VWGVWCVGWDVTZVWGVWCVWGVWAVWBVWFAVVTKUIZVWAWEUIZJVVSKQUUHAVWNVVTVFUIZVWOAK
      VFVVTVWLWAAVFWEVVTCNWBWCWFZAVWFVWJVWBWEUIZAKVFVVSVWLWAZAVFWEVVSCNWBZWCZSU
      UIZWGWHZUUJZUAUUKZWIZABUCZVVJUIZVNVXHVVKVXGUMVCZWJZAVXHWKVXHAVXGUJUIZVXHV
      XJWLVVILVXGUJUUMAVXKVNZVXHVVKVXGVGUDZUMVCZVXIVXLVXNVXHVXLVXNVXHWJZVXLVXNV
      NVXMVVKWMZVXOVXLVXNVVKVXMWNVCZVXPVXLVVKVXMAVVKUJUIZVXKVXEWOZVXKVXMUJUIZAV
      XKVXGVXGUULWGWRZUUNZUUOVXLVXPVXNVXOVXLVXPVNZVXNVXOVYCVXNVXMVVKUMVCZWJZVXO
      VYCVXNVXQVXPVNZVXQVYEVXLVXNVYFVEVXPVYBWOVYCVXPVXQVXLVXPWKUUPVXLVXQVYEVEVX
      PVXLVVKVXMVXSVYAUUQWOUURVYCVYDVXHVXLVXPVXMIWPUSZUOWMZVYDVXHVEVXLVXPVYHVXL
      VXMVVKVYGUOVXLVVKVXMWQUOVYGWQVXMVVKWQVYGUOWQVXLUOVXMIVXLWSVXLVXMVYAWTAIWE
      UIVXKAIVXDWTZWOAIUEWMVXKUAWOUUSVVKVXMXAUOVYGXAUUTUVAXBVXLVYHVNVYGUOUMVCZV
      YDVXHVXLVYJVYDVEVYHVXLVXMUOIVYAVXLUVCAIUVDUIVXKAIVXDAIVXDAIFDJKQVVMTVWGVW
      HVVSDUDZUJVWFVWHVYKWQAVVSKDUVEWRZVXCUVFZVWGUEVWHVYKWNVWGUEVWDVWHWNVWGVWCV
      XBUVGVWMXCVYLUVHUVIUAUVJZUVMWOUVKWOAVYHVXKVYJVXHVEZVXKAVYHVNZVXGUJUEUVLZU
      VNZUIZVXGUJVYQXDZUIZUWEZVYOWUBVXGVYRVYTUVOZUIVXKVXGVYRVYTUVPWUCUJVXGUJVYQ
      UVQUVRUVSVYPVYSVYOWUAAVYSVYOVYHVYSAVXGUEWQZVYOVYSVXGVYQUIZWUDVYSVXKWUEVXG
      UJVYQUVTUWAVXGUEUWBXEAWUDVNZVYJVXHWUFVYGUEUOUMWUDAVYGUEIWPUSUEWUDVXMUEIWP
      WUDVXMUEVGUDUEVXGUEVGXFUWFUWCXGAIVYIUWDUWGUWHUWIAWUDVXHAVXHWUDUEVVJUIABCG
      HLMNUWJVXGUEVVJUWKUWLXHUWMWFXIAWUAVYHVYOAWUAVNVYHVNVYJUBVXGHUDZUEUFZVVHUI
      ZVXHWUAAVXGWEVYQXDZUIZVYHVYJWUIVEVYTWUJVXGUJWEXTVYTWUJXTUXFUJWEVYQUWNUWOU
      WPAWUKVNZVYHVNZGKGUCZUOUBUSWUGUDZWUNWUGUDZUPUSZVGUDZVHZFWUGVYGUEJVDKVFUWQ
      QAVWKWUKVYHRXJWUMVXGHWDWULVWJVVSWUGUDZWEUIZVYHWUKAVXGWEUIZVWJWVAVXGWEVYQX
      KZAWVBVNZVWJVNZWUTVWBVXGVVSXLUSZWPUSZWEWVEGVVSWUNCUDZVXGWUNXLUSZWPUSZWVGV
      FWUGVDWVDWUGGVFWVJVHZWQZVWJABWEWVKHVDHBWEWVKVHWQAMURWVKVDUIWVDGVFWVJVIVJU
      RVTZWOWUNVVSWQZWVJWVGWQZWVEWVNWVHVWBWVIWVFWPWUNVVSCXFWUNVVSVXGXLUWRXMZWRW
      VDVWJWKZWVEVWBWVFWPYAXNZWVEVWBWVFAVWJVWRWVBVWTXIWVEVXGVVSAWVBVWJXOWVQXPUW
      SWHXQXIWULVWFWUTUEWMVYHWULVWFVNZWUTWVGUEWUKAWVBVWFWUTWVGWQZWVCWVDVWFVWJWV
      TAVWFVWJWVBVWSXIZWVRWCXQWVSVWBWVFAVWFVWRWUKVXAXIZWVSVXGVVSWULWVBVWFWUKWVB
      AWVCWRZWOZAVWFVWJWUKVWSXIZXPZAVWFVWBUEWMWUKSXIZWVSVXGVVSWWDWUKVXGUEWMAVWF
      VXGWEUEUWTXRZWVSVVSWWEVAZUXAZUXBUXCXIGFKWURVVTWUGUDZWUTUPUSZVGUDZWVNWUQWW
      LVGWVNWUOWWKWUPWUTUPWUNVVSUOWUGUBUXDWUNVVSWUGXFXMXSZUXEWULWUSVYGUGVCVYHWU
      LGVFWURVHZVVNUTZWUSVYGUGWULWWPWWOKUTWUSKVVNWWOQVBWULGVFKWURAKVFXTWUKVWLWO
      VRUXGWULWWPVYGUGVCZWWOVYGUGVCZWULIVXMFDWWOJVDKQAVVRWUKVVMWOZAVVQWUKTWOWUL
      VXMWULVXGWWCWGWTZWWOVDUIZWULGVFWURVIVJZURAVWFVYKWEUIWUKVWGVYKVYMWTXIZWVSV
      VSWWOUDZVWDVXMWPUSZVYKVXMWPUSVXMVYKWPUSWVSWXDWWMVWCVXGWPUSZVGUDWXEWVSGVVS
      WURWWMVFWWOVDWVSWWOUXHWVNWURWWMWQWVSWWNWRWWEWVSWWLVGWDXNWVSWWLWXFVGWVSWWL
      VWAVXGVVTXLUSZWPUSZWVGUPUSZVWCWXGWVFUPUSZWPUSWXFWUKAWVBVWFWWLWXIWQWVCWVDV
      WFVNZWWKWXHWUTWVGUPWXKGVVTWVJWXHVFWUGVDWVDWVLVWFWVMWOZWXKWUNVVTWQZVNZWVHV
      WAWVIWXGWPWXNWUNVVTCWXKWXMWKZXSWXNWUNVVTVXGXLWXOYBXMWXKVVSUOWWAUOVFUIWXKU
      YNURUXIZWXKVWAWXGWPYAXNWXKGVVSWVJWVGVFWUGVDWXLWVNWVOWXKWVPWRWWAWXKVWBWVFW
      PYAXNXMXQWVSVWAVWBWXGWVFAVWFVWOWUKVWQXIWWBWVSVXGVVTWWDWUKAWVBVWFVWPWVCWXP
      XQZXPWWFWWGWWJUXJWVSWXJVXGVWCWPWVSVXGVVTVVSYCUSZXLUSVXGUOXLUSWXJVXGWVSWXR
      UOVXGXLWVSVVSUOWVSVVSWWEUXKWVSWSUXLYBWVSVXGVVTVVSWWDWWHWWIWVSVVTWXQVAUXMW
      VSVXGWWDUXNUXOYBUXPXSWVSVWCVXGAVWFVWCWEUIWUKVXBXIWWDUXQYDWVSVWDVYKVXMWPWV
      SVYKVWDAVWFVYKVWDWQWUKVWGVWHVYKVWDVYLVWMUXRXIUXSXGWVSVYKVXMWXCWULVXMWEUIV
      WFWWTWOUXTYDUYAWULVVRWXAWWQWWRVEWWSWXBVYGWWOJVDVKVMVLUYDWOWULVYHWKUYBXQWU
      AVXHWUIVEZAVYHWUAVXKWXSVXGUJVYQXKVVIWUILVXGUJVVEVXGWQZVVGWUHVVHWXTVVFWUGU
      BUEVVEVXGHXFUYCUYEUYFXEXRUYGYMUYHUYIYMUYJWCZUYKUYLYEYFYGVPUYOVXLVXIVXNVXL
      VXIVNZVVKVXGVXMVXLVXRVXIVXSWOAVXKVXIXOZVXLVXTVXIVYAWOVXLVXIWKWYBVXGWYCUYP
      UYMVPUYQWFYGAVXGULUIZVXGVVKUMVCZVNZVNZVXGVVSUMVCZFVVKUYRZVVKYHUSZYIZWYHFV
      VJYIZWYGWYIVXGWNVCZWYKWYGWYMVNVXGVVKYHUSZWYJXTZWYHFWYNYIZWYKAWYMWYOWYFAWY
      IULUIZWYMWYOAWYIAVVKVXEUYSZWIZWYIVXGVVKYJVOXIWYGWYPWYMAWYDWYEWYPAWYDVNZWY
      EVNZWYHFWYNYKZWYPWYHFWYNVVSWYNUIZWYHVVSVVKUMVCVVSVXGVVKUYTVUAZVUBXUAWYNYL
      WMZXUBWYPWLWYTXUEWYEWYDAXUEWYEVEZAWYDVVKULUIZXUFVXFVXGVVKYNWFYOVUCWYHFWYN
      YPYQVUNVUDWOWYHFWYNWYJYRVUEAWYDWYMWJZWYKWYEWYTXUHVNZWYHFWYJYKZWYKXUIWYHFW
      YJXUIVVSWYJUIVNXUCWYHXUIWYJWYNVVSXUIWYDVXGWYIWNVCZWYJWYNXTAWYDXUHXOWYTXUH
      XUKWYDAXUHXUKWLZAWYDWYQXULWYSWYDWYQVNXUHVXGWYIUMVCXUKVXGWYIVUFVXGWYIVUOYS
      WFYOXHVXGWYIVVKYJYTWAXUDXEVUGAXUJWYKWLZWYDXUHAWYJYLWMZXUMAXUNWYIVVKUMVCZA
      XUOUEVVKWYIYCUSZUMVCAUEVVKVVKUBUSXUPUMAVVKVVKVXEVXEAIVXDVYNVUHZXUQVUIAVVK
      VVKAVVKVXEWTZXURVUJXCAWYIVVKWYRVXEVUKVLAWYQXUGXUNXUOVEWYSVXFWYIVVKYNYTVLW
      YHFWYJYPYQXJYGVULVUMAWYKWYLWLZWYFAWYJVVJXTXUSABWYJVVJAVXGWYJUIZVXHAXUTVXK
      WYIVXGUMVCZWYEVUPZVXHAXUTXVBAWYQXUGXUTXVBVEWYSVXFWYIVVKVXGVUQYTXBXVBAVXHV
      XKXVAWYEAVXHWLAVXKXVAWYEVNZVNVXHAVXKXVCVXHVXLXVCVYDVXHVXLVXGVVKAVXKWKVXSV
      URVXLVYDVXHVXLVYDVNZVXPVXHXVDVXMVVKVXLVXTVYDVYAWOVXLVYDWKVUSVXLVXPVYDVXHV
      YCVYDVXHWYAYEYFYGVPYSVUTVVAVVBVVCWCVPVQWYHFWYJVVJYRXEWOYGVVDVS $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Multiples
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x y z $.
    $( The divides relation is in fact a relation.  (Contributed by Steve
       Rodriguez, 20-Jan-2020.) $)
    reldvds $p |- Rel || $=
      ( vx vy vz cv cz wcel wa cmul co wceq wrex cdvds df-dvds relopabiv ) ADZE
      FBDZEFGCDOHIPJCEKGABLABCMN $.
  $}

  ${
    $d x N $.  $d x ph $.
    nznngen.n $e |- ( ph -> N e. ZZ ) $.
    $( All positive integers in the set of multiples of _n_,
       <HTML><i>n</i>&#x2124;,</HTML> are the absolute value of _n_ or greater.
       (Contributed by Steve Rodriguez, 20-Jan-2020.) $)
    nznngen $p |- ( ph -> ( ( || " { N } ) i^i NN ) C_ ( ZZ>= ` ( abs ` N ) )
        ) $=
      ( vx cdvds csn cima cn cin cabs cfv cuz cv wcel wbr wa cz syl2an sylan2b
      wb crab cab wrel reldvds relimasn ax-mp ineq1i dfrab2 eqtr4i eleq2i rabid
      wceq cle nnz absdvdsb wi zabscl syl dvdsle sylan sylbid impr simplbi nnzd
      eluz mpbird ex ssrdv ) ADEBFGZHIZBJKZLKZADMZVJNZVMVLNZVNAVMBVMEOZDHUAZNZV
      OVJVQVMVJVPDUBZHIVQVIVSHEUCVIVSULUDDBEUEUFUGVPDHUHUIUJAVRPVOVKVMUMOZVRAVM
      HNZVPPVTVPDHUKZAWAVPVTAWAPVPVKVMEOZVTABQNZVMQNZVPWCTWACVMUNBVMUORAVKQNZWA
      WCVTUPAWDWFCBUQURZVKVMUSUTVAVBSAWFWEVOVTTVRWGVRVMVRWAVPWBVCVDVKVMVERVFSVG
      VH $.
  $}

  ${
    $d x y n $.  $d n x M $.  $d n x N $.
    nzss.m $e |- ( ph -> M e. ZZ ) $.
    nzss.n $e |- ( ph -> N e. V ) $.
    $( The set of multiples of _m_, <HTML><i>m</i>&#x2124;,</HTML> is a subset
       of those of _n_, <HTML><i>n</i>&#x2124;,</HTML> iff _n_ divides _m_.
       Lemma 2.1(a) of
       ~ https://www.mscs.dal.ca/~~selinger/3343/handouts/ideals.pdf p. 5,
       with <HTML><i>m</i>&#x2124;</HTML> and <HTML><i>n</i>&#x2124;</HTML> as
       images of the divides relation under _m_ and _n_.
       (Contributed by Steve Rodriguez, 20-Jan-2020.) $)
    nzss $p |- ( ph -> ( ( || " { M } ) C_ ( || " { N } ) <-> N || M ) ) $=
      ( vx vn vy cz wcel cdvds wss wbr wa breq2 wceq crab cc0 breq1 csn cima wb
      wi cv iddvds elabg mpbird wrel reldvds relimasn ax-mp eleqtrrdi ssel syl5
      cab elab2g mpbidi com12 adantr ssid simpl dvdszrcl simprd 0dvds sylan9bbr
      syl mpbid breq1d sylan9bb rabbidva 0z rabsn eqtrdi rabbidv rabbiia adantl
      eqtri sseq12d mpbiri cdiv co cmul cc zcnd ad2antrr simpld simplr divcan2d
      wne w3a dvdsval2 biimpd 3expa sylan imp anabss1 muldvds1 sylbird ss2rabdv
      3com23 cbvrabv 3sstr3g pm2.61dane abbidv eqeq12d simpr ancri impbii elrab
      jca elab 3bitr4i eqriv vtoclg imbitrid sseq12i imbitrrdi impbid syl2anc
      vex ) ABJKZCDKZLBUAUBZLCUAUBZMZCBLNZUCEFYBYCOZYFYGYBYFYGUDYCYFYBYGYBBYEKZ
      YGYFYBBYDKYFYIYBBBGUEZLNZGUPZYDYBBYLKBBLNZBUFYKYMGBJYJBBLPUGUHLUIZYDYLQUJ
      GBLUKULZUMYDYEBUNUOCYJLNZYGGBYEJYJBCLPYNYEYPGUPZQUJGCLUKULZUQURUSUTYHYGYL
      YQMZYFYGYKGJRZYPGJRZMZYHYSYGUUBCSYGCSQZOZUUBSUAZUUEMUUEVAUUDYTUUEUUAUUEUU
      DYTYJSQZGJRZUUEUUDYKUUFGJUUDYKSYJLNZYJJKUUFUUDBSYJLUUDYGBSQZYGUUCVBUUCYGS
      BLNZYGUUICSBLTYGYBUUJUUIUCYGCJKZYBCBVCZVDZBVEVGVFVHVIYJVEZVJVKSJKUUGUUEQV
      LGJSVMULZVNUUCUUAUUEQYGUUCUUAUUHGJRZUUEUUCYPUUHGJCSYJLTVOUUPUUGUUEUUHUUFG
      JUUNVPUUOVRVNVQVSVTYGCSWJZOZBHUEZLNZHJRCUUSLNZHJRYTUUAUURUUTUVAHJUURUUSJK
      ZOZUUTCBCWAWBZWCWBZUUSLNZUVAUVCUVEBUUSLUVCBCYGBWDKUUQUVBYGBUUMWEWFYGCWDKU
      UQUVBYGCYGUUKYBUULWGZWEWFYGUUQUVBWHWIVIUURUUKUVDJKZOUVBUVFUVAUDZUURUUKUVH
      YGUUKUUQUVGUTYGUUQUVHUURYGUVHYGUUKYBOUUQYGUVHUDZUULUUKYBUUQUVJUUKUUQYBUVJ
      UUKUUQYBWKYGUVHCBWLWMXAWNWOWPWQXKUUKUVHUVBUVICUVDUUSWRWNWOWSWTUUTYKHGJUUS
      YJBLPXBUVAYPHGJUUSYJCLPXBXCXDYHYTYLUUAYQYBYTYLQZYCUUSYJLNZGJRZUVLGUPZQZUV
      KHBJUUSBQZUVMYTUVNYLUVPUVLYKGJUUSBYJLTZVOUVPUVLYKGUVQXEXFIUVMUVNIUEZJKZUU
      SUVRLNZOZUVTUVRUVMKUVRUVNKUWAUVTUVSUVTXGUVTUVSUVTUVBUVSUUSUVRVCVDXHXIUVLU
      VTGUVRJYJUVRUUSLPZXJUVLUVTGUVRIYAUWBXLXMXNZXOUTYCUUAYQQZYBUVOUWDHCDUUSCQZ
      UVMUUAUVNYQUWEUVLYPGJUUSCYJLTZVOUWEUVLYPGUWFXEXFUWCXOVQVSXPYDYLYEYQYOYRXQ
      XRXSXT $.
  $}

  ${
    $d n M $.  $d n N $.
    nzin.m $e |- ( ph -> M e. ZZ ) $.
    nzin.n $e |- ( ph -> N e. ZZ ) $.
    $( The intersection of the set of multiples of _m_,
       <HTML><i>m</i>&#x2124;,</HTML> and those of _n_,
       <HTML><i>n</i>&#x2124;,</HTML> is the set of multiples of their least
       common multiple.  Roughly Lemma 2.1(c) of
       ~ https://www.mscs.dal.ca/~~selinger/3343/handouts/ideals.pdf p. 5 and
       Problem 1(b) of
       ~ https://people.math.binghamton.edu/mazur/teach/40107/40107h16sol.pdf
       p. 1, with <HTML><i>m</i>&#x2124;</HTML> and
       <HTML><i>n</i>&#x2124;</HTML> as images of the divides relation under
       _m_ and _n_.
       (Contributed by Steve Rodriguez, 20-Jan-2020.) $)
    nzin $p |- ( ph -> ( ( || " { M } ) i^i ( || " { N } ) ) =
        ( || " { ( M lcm N ) } ) ) $=
      ( vn cdvds csn cima wss wa wcel cz dvdszrcl wb reldvds elrelimasn syl2anc
      wbr ax-mp clcm co cv anim12i anandir sylibr ancomd wi lcmdvds 3expb mpcom
      cin elin wrel anbi12i bitri 3imtr4i ssriv dvdslcm simpld lcmcl nn0zd nzss
      a1i cn0 mpbird simprd ssind eqssd ) AGBHIZGCHIZULZGBCUAUBZHIZVLVNJAFVLVNB
      FUCZGSZCVOGSZKZVMVOGSZVOVLLZVOVNLZVOMLZBMLZCMLZKZKVRVSVRWEWBVRWCWBKZWDWBK
      ZKWEWBKVPWFVQWGBVONCVONUDWCWDWBUEUFUGWBWCWDVRVSUHVOBCUIUJUKVTVOVJLZVOVKLZ
      KVRVOVJVKUMWHVPWIVQGUNZWHVPOPBVOGQTWJWIVQOPCVOGQTUOUPWJWAVSOPVMVOGQTUQURV
      DAVNVJVKAVNVJJBVMGSZAWKCVMGSZAWCWDWKWLKDEBCUSRZUTAVMBMAVMAWCWDVMVELDEBCVA
      RVBZDVCVFAVNVKJWLAWKWLWMVGAVMCMWNEVCVFVHVI $.
  $}

  ${
    nzprmdif.m $e |- ( ph -> M e. Prime ) $.
    nzprmdif.n $e |- ( ph -> N e. Prime ) $.
    nzprmdif.ne $e |- ( ph -> M =/= N ) $.
    $( Subtract one prime's multiples from an unequal prime's.  (Contributed by
       Steve Rodriguez, 20-Jan-2020.) $)
    nzprmdif $p |- ( ph -> ( ( || " { M } ) \ ( || " { N } ) ) =
        ( ( || " { M } ) \ ( || " { ( M x. N ) } ) ) ) $=
      ( cdvds csn cima cdif co cmul cprime wcel cz prmz syl difeq2d syl2anc c1
      clcm cin difin nzin eqtr3id cgcd cabs cfv wceq lcmgcd wne wb prmrp mpbird
      oveq2d cn0 lcmcl nn0cnd mulridd eqtrd zred remulcld prmnn nn0ge0d mulge0d
      cn nnnn0d absidd 3eqtr3d sneqd imaeq2d ) AGBHIZGCHIZJZVLGBCUAKZHZIZJZVLGB
      CLKZHZIZJAVNVLVLVMUBZJVRVLVMUCAWBVQVLABCABMNZBONZDBPQZACMNZCONZECPQZUDRUE
      AVQWAVLAVPVTGAVOVSAVOBCUFKZLKZVSUGUHZVOVSAWDWGWJWKUIWEWHBCUJSAWJVOTLKVOAW
      ITVOLAWITUIZBCUKZFAWCWFWLWMULDEBCUMSUNUOAVOAVOAWDWGVOUPNWEWHBCUQSURUSUTAV
      SABCABWEVAZACWHVAZVBABCWNWOABABAWCBVFNDBVCQVGVDACACAWFCVFNECVCQVGVDVEVHVI
      VJVKRUT $.
  $}

  ${
    $d x J $.  $d x K $.  $d x N $.
    hashnzfz.n $e |- ( ph -> N e. NN ) $.
    hashnzfz.j $e |- ( ph -> J e. ZZ ) $.
    hashnzfz.k $e |- ( ph -> K e. ( ZZ>= ` ( J - 1 ) ) ) $.
    $( Special case of ~ hashdvds : the count of multiples in
       <HTML><i>n</i>&#x2124;</HTML> restricted to an interval.
       (Contributed by Steve Rodriguez, 20-Jan-2020.) $)
    hashnzfz $p |- ( ph -> ( # ` ( ( || " { N } ) i^i ( J ... K ) ) ) =
        ( ( |_ ` ( K / N ) ) - ( |_ ` ( ( J - 1 ) / N ) ) ) ) $=
      ( vx cc0 cmin co cdvds chash cfv cdiv cfl cin wcel zcnd subid1d cv wbr c1
      cfz crab csn cima 0zd hashdvds wceq elfzelz breq2d rabbiia dfrab3 reldvds
      cab wrel relimasn ax-mp ineq2i incom eqtr3i 3eqtri fveq2i a1i cuz eluzelz
      cz syl fvoveq1d peano2zm oveq12d 3eqtr3d ) ADHUAZIJKZLUBZHBCUDKZUEZMNZCIJ
      KZDOKPNZBUCJKZIJKZDOKPNZJKLDUFUGZVQQZMNZCDOKPNZWBDOKPNZJKAHBCIDEFGAUHUIVS
      WGUJAVRWFMVRDVNLUBZHVQUEVQWJHUPZQZWFVPWJHVQVNVQRZVOVNDLWMVNWMVNVNBCUKSTUL
      UMWJHVQUNVQWEQWLWFWEWKVQLUQWEWKUJUOHDLURUSUTVQWEVAVBVCVDVEAWAWHWDWIJAVTCD
      POACACACWBVFNRCVHRGWBCVGVISTVJAWCWBDPOAWBAWBABVHRWBVHRFBVKVISTVJVLVM $.
  $}

  ${
    hashnzfz2.n $e |- ( ph -> N e. ( ZZ>= ` 2 ) ) $.
    hashnzfz2.k $e |- ( ph -> K e. NN ) $.
    $( Special case of ~ hashnzfz : the count of multiples in
       <HTML><i>n</i>&#x2124;,</HTML> _n_ greater than one, restricted to an
       interval starting at two.
       (Contributed by Steve Rodriguez, 20-Jan-2020.) $)
    hashnzfz2 $p |- ( ph -> ( # ` ( ( || " { N } ) i^i ( 2 ... K ) ) ) =
        ( |_ ` ( K / N ) ) ) $=
      ( c2 co cfv cdiv cfl c1 cmin cc0 cuz cn wcel cz 2m1e1 wbr clt csn cfz cin
      cdvds cima chash wss 2nn uznnssnn ax-mp sselid a1i fveq2i eqtr4i eleqtrdi
      2z nnuz hashnzfz oveq1i wceq cle caddc 0red nnrecred nnred nngt0d recgt0d
      ltled eluzle syl nnzd zlem1lt sylancr mpbid eqbrtrrid nnrpd recgt1d 0p1e1
      wb breqtrrdi cr wa 0z flbi sylancl mpbir2and eqtrid oveq2d nndivred flcld
      zcnd subid1d 3eqtrd ) AUDCUAUEFBUBGUCUFHBCIGZJHZFKLGZCIGZJHZLGWOMLGWOAFBC
      AFNHZOCFOPWSOUGUHFUIUJDUKZFQPZAUPULABOWPNHZEOKNHXBUQWPKNRUMUNUOURAWRMWOLA
      WRKCIGZJHZMWQXCJWPKCIRUSUMAXDMUTZMXCVASZXCMKVBGZTSZAMXCAVCACWTVDZACACWTVE
      ACWTVFVGVHAXCKXGTAKCTSXCKTSAKWPCTRAFCVASZWPCTSZACWSPXJDFCVIVJAXACQPXJXKVS
      UPACWTVKFCVLVMVNVOACACWTVPVQVNVRVTAXCWAPMQPXEXFXHWBVSXIWCXCMWDWEWFWGWHAWO
      AWOAWNABCABEVEWTWIWJWKWLWM $.
  $}

  ${
    $d k x J $.  $d k x M $.  $d k x ph $.
    hashnzfzclim.m $e |- ( ph -> M e. NN ) $.
    hashnzfzclim.j $e |- ( ph -> J e. ZZ ) $.
    $( As the upper bound ` K ` of the constraint interval ` ( J ... K ) ` in
       ~ hashnzfz increases, the resulting count of multiples tends to
       ` ( K / M ) ` &mdash;that is, there are approximately ` ( K / M ) `
       multiples of ` M ` in a finite interval of integers.  (Contributed by
       Steve Rodriguez, 20-Jan-2020.) $)
    hashnzfzclim $p |- ( ph -> ( k e. ( ZZ>= ` ( J - 1 ) ) |->
        ( ( # ` ( ( || " { M } ) i^i ( J ... k ) ) ) / k ) ) ~~> ( 1 / M ) ) $=
      ( c1 cmin co cfv cdiv cmpt cli wcel cn cz wbr cvv wceq adantl vx cuz cima
      cdvds csn cv cfz cin chash cfl adantr simpr hashnzfz oveq1d mpteq2dva cc0
      wa nnuz 1z a1i cxp cc nncnd nnne0d eqimss2i nnex climconst2 sylancl mptex
      reccld ax-1cn divcnv mp1i fvconst2 eqeltrd cr eqidd oveq2 fvmptd nnrecred
      ovex ovexd recnd oveq2d oveq12d eqtr4d climsub subid1d breqtrd nnre nnne0
      wne rereccld resubcld fvoveq1 nndivred reflcl syl redivcld cle divsubdird
      id clt 1cnd nncn cmul divrecd divcan3d eqtrd 1red crp nnrp caddc readdcld
      flle flflp1 syl2anc mpbid ltsub1dd pncand ltdiv1dd eqbrtrrd ltled 3brtr4d
      fvoveq1d lediv1dd eqbrtrd climsqz zred flcld zcnd divcld 3eqtr4d cres wss
      wb resmpt ax-mp breq1i climres uzssz zsubcld bitr3id reseq2i nnssz mpbird
      zex mp2an 3bitr3i bitr4di ) ABCGHIZUBJZUDDUEUCCBUFZUGIUHUIJZUUMKIZLBUULUU
      MDKIUJJZUUKDKIZUJJZHIZUUMKIZLZGDKIZMABUULUUOUUTAUUMUULNZUQZUUNUUSUUMKUVDC
      UUMDADONZUVCEUKACPNUVCFUKAUVCULUMUNUOAUVAUVBMQZBOUUTLZUVBMQZAUVGUVBUPHIZU
      VBMAUVBUPUABOUUPUUMKIZLZBOUURUUMKIZLZUVGGROURGPNZAUSUTZAUVBUABOUVBGUUMKIZ
      HIZLZUVKGROURUVOAUVRUVIUVBMAUVBUPUAOUVBUEVAZBOUVPLZUVRGROURUVOAUVBVBNZUVN
      UVSUVBMQADADEVCZADEVDZVJZUSUVBGOOGUBJZURVEVFVGVHUVRRNABOUVQVFVIUTGVBNUVTU
      PMQAVKGBVLVMAUAUFZONZUQZUWFUVSJZUVBVBUWGUWIUVBSAOUVBUWFGDKWAVNTZAUWAUWGUW
      DUKZVOUWHUWFUVTJZUWHUWLGUWFKIZVPUWHBUWFUVPUWMOUVTRUWHUVTVQUUMUWFSZUVPUWMS
      UWHUUMUWFGKVRZTAUWGULZUWHGUWFKWBVSZUWHUWFUWPVTVOWCUWHUWFUVRJZUVBUWMHIZUWI
      UWLHIUWHBUWFUVQUWSOUVRRUWHUVRVQUWNUVQUWSSUWHUWNUVPUWMUVBHUWOWDTUWPUWHUVBU
      WMHWBVSZUWHUWIUVBUWLUWMHUWJUWQWEWFWGAUVBUWDWHZWIUVKRNABOUVJVFVIUTUWHUWRUW
      SVPUWTUWHUVBUWMAUVBVPNUWGADEVTUKUWHUWFUWGUWFVPNAUWFWJTZUWGUWFUPWLAUWFWKTZ
      WMWNZVOUWHUWFUVKJZUWFDKIZUJJZUWFKIZVPUWHBUWFUVJUXHOUVKRUWHUVKVQZUWNUVJUXH
      SUWHUWNUUPUXGUUMUWFKUUMUWFDUJKWOZUWNXBZWETUWPUWHUXGUWFKWBZVSZUWHUXGUWFUWH
      UXFVPNZUXGVPNUWHUWFDUXBAUVEUWGEUKWPZUXFWQWRZUXBUXCWSZVOZUWHUWSUXHUWRUXEWT
      UWHUWSUXHUXDUXQUWHUXFGHIZUWFKIZUWSUXHXCUWHUXTUXFUWFKIZUWMHIUWSUWHUXFGUWFU
      WHUXFUXOWCUWHXDZUWGUWFVBNAUWFXETZUXCXAUWHUYAUVBUWMHUWHUYAUWFUVBXFIZUWFKIU
      VBUWHUXFUYDUWFKUWHUWFDUYCADVBNUWGUWBUKADUPWLUWGUWCUKXGUNUWHUVBUWFUWKUYCUX
      CXHXIZUNXIUWHUXSUXGUWFUWHUXFGUXOUWHXJZWNUXPUWGUWFXKNAUWFXLTZUWHUXSUXGGXMI
      ZGHIUXGXCUWHUXFUYHGUXOUWHUXGGUXPUYFXNUYFUWHUXGUXFWTQZUXFUYHXCQZUWHUXNUYIU
      XOUXFXOWRZUWHUXNUXNUYIUYJYPUXOUXOUXFUXFXPXQXRXSUWHUXGGUWHUXGUXPWCZUYBXTWI
      YAYBYCUWTUWHBUWFUVJUXHOUVKRUXIUWHUWNUQZUUPUXGUUMUWFKUYMUUMUWFDUJKUWHUWNUL
      ZYEUYNWEUWPUXLVSZYDUWHUXEUXHUVBWTUYOUWHUXHUYAUVBWTUWHUXGUXFUWFUXPUXOUYGUY
      KYFUYEWIYGYHUVGRNABOUUTVFVIUTAUURVBNZUVMUPMQAUURAUUQAUUKDACGACFYIAXJWNEWP
      YJYKZUURBVLWRUWHUXEUXRWCUWHUWFUVMJZUURUWFKIZVBUWHBUWFUVLUYSOUVMRUWHUVMVQU
      WNUVLUYSSUWHUUMUWFUURKVRTUWPUWHUURUWFKWBVSZUWHUURUWFAUYPUWGUYQUKZUYCUXCYL
      VOUWHUXGUURHIZUWFKIZUXHUYSHIUWFUVGJUXEUYRHIUWHUXGUURUWFUYLVUAUYCUXCXAUWHB
      UWFUUTVUCOUVGRUWHUVGVQUWNUUTVUCSUWHUWNUUSVUBUUMUWFKUWNUUPUXGUURHUXJUNUXKW
      ETUWPUWHVUBUWFKWBVSUWHUXEUXHUYRUYSHUXMUYTWEYMWGUXAWIAUVFBPUUTLZUVBMQZUVHU
      VFVUDUULYNZUVBMQZAVUEVUFUVAUVBMUULPYOVUFUVASUUKUUABPUULUUTYQYRYSAUUKPNVUD
      RNZVUGVUEYPACGFUVOUUBBPUUTUUGVIZUVBVUDUUKRYTVHUUCVUDOYNZUVBMQVUDUWEYNZUVB
      MQZUVHVUEVUJVUKUVBMOUWEVUDURUUDYSVUJUVGUVBMOPYOVUJUVGSUUEBPOUUTYQYRYSUVNV
      UHVULVUEYPUSVUIUVBVUDGRYTUUHUUIUUJUUFYG $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Function operations
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d w x y z F $.  $d w A $.  $d w x y z G $.  $d w x y z H $.
    $d w x y z R $.  $d w x y z ph $.  $d x y z S $.  $d x y z T $.
    caofcan.1 $e |- ( ph -> A e. V ) $.
    caofcan.2 $e |- ( ph -> F : A --> T ) $.
    caofcan.3 $e |- ( ph -> G : A --> S ) $.
    caofcan.4 $e |- ( ph -> H : A --> S ) $.
    caofcan.5 $e |- ( ( ph /\ ( x e. T /\ y e. S /\ z e. S ) ) -> ( ( x R y ) =
        ( x R z ) <-> y = z ) ) $.
    $( Transfer a cancellation law like ~ mulcan to the function operation.
       (Contributed by Steve Rodriguez, 16-Nov-2015.) $)
    caofcan $p |- ( ph -> ( ( F oF R G ) = ( F oF R H ) <-> G = H ) ) $=
      ( vw cfv wceq cv cof co wral wcel wa ffnd inidm eqidd ofval eqeq12d simpl
      wb ffvelcdmda caovcang syl13anc bitrd ralbidva wfn eqfnfv syl2anc 3bitr4d
      offn ) ARUAZIJFUBZUCZSZVDIKVEUCZSZTZREUDZVDJSZVDKSZTZREUDZVFVHTZJKTZAVJVN
      REAVDEUEZUFZVJVDISZVLFUCZVTVMFUCZTZVNVSVGWAVIWBAEEVTVLFEIJLLVDAEHINUGZAEG
      JOUGZMMEUHZVSVTUIZVSVLUIUJAEEVTVMFEIKLLVDWDAEGKPUGZMMWFWGVSVMUIUJUKVSAVTH
      UEVLGUEVMGUEWCVNUMAVRULAEHVDINUNAEGVDJOUNAEGVDKPUNABCDVTVLVMGHFQUOUPUQURA
      VFEUSVHEUSVPVKUMAEEFEIJLLWDWEMMWFVCAEEFEIKLLWDWHMMWFVCREVFVHUTVAAJEUSKEUS
      VQVOUMWEWHREJKUTVAVB $.
  $}

  ${
    $d x A $.  $d x F $.  $d x V $.
    $( Function analogue of ~ subid .  (Contributed by Steve Rodriguez,
       5-Nov-2015.) $)
    ofsubid $p |- ( ( A e. V /\ F : A --> CC ) ->
                    ( F oF - F ) = ( A X. { 0 } ) ) $=
      ( vx wcel cc wf wa cv cfv cmin cc0 csn cxp simpl wfn ffn adantl c0ex wceq
      fconst mp1i eqidd co ffvelcdm subidd adantll fvconst2 eqtr4d offveq ) ACE
      ZAFBGZHZDADIZBJZUOKBBALMZNZCUKULOULBAPUKAFBQRZURAUPUQGUQAPUMALSUAAUPUQQUB
      UMUNAEZHZUOUCZVAUTUOUOKUDZLUNUQJZULUSVBLTUKULUSHUOAFUNBUEUFUGUSVCLTUMALUN
      SUHRUIUJ $.
  $}

  ${
    $d x A $.  $d x F $.  $d x G $.  $d x H $.  $d x V $.
    $( Function analogue of ~ mul12 .  (Contributed by Steve Rodriguez,
       13-Nov-2015.) $)
    ofmul12 $p |- ( ( ( A e. V /\ F : A --> CC ) /\ ( G : A --> CC /\ H : A
      --> CC ) ) -> ( F oF x. ( G oF x. H ) ) = ( G oF x. ( F oF x. H ) ) ) $=
      ( vx wcel cc wf wa cv cfv cmul co cof ffnd offn eqidd ofval ffvelcdmda
      simpll simplr simprl simprr inidm mul12d eqtr4d offveq ) AEGZAHBIZJZAHCIZ
      AHDIZJZJZFAFKZBLZUPCLZUPDLZMNZMBCDMOZNCBDVANZVANZEUIUJUNUAZUOAHBUIUJUNUBZ
      PZUOAAMACDEEUOAHCUKULUMUCZPZUOAHDUKULUMUDZPZVDVDAUEZQUOAAMACVBEEVHUOAAMAB
      DEEVFVJVDVDVKQZVDVDVKQUOUPAGJZUQRZUOAAURUSMACDEEUPVHVJVDVDVKVMURRZVMUSRZS
      VMUQUTMNURUQUSMNZMNUPVCLVMUQURUSUOAHUPBVETUOAHUPCVGTUOAHUPDVITUFUOAAURVQM
      ACVBEEUPVHVLVDVDVKVOUOAAUQUSMABDEEUPVFVJVDVDVKVNVPSSUGUH $.
  $}

  ${
    $d x A $.  $d x F $.  $d x G $.  $d x V $.
    $( Function analogue of ~ divrec , a division analogue of ~ ofnegsub .
       (Contributed by Steve Rodriguez, 3-Nov-2015.) $)
    ofdivrec $p |- ( ( A e. V /\ F : A --> CC /\ G : A --> ( CC \ { 0 } ) )
      -> ( F oF x. ( ( A X. { 1 } ) oF / G ) ) = ( F oF / G ) ) $=
      ( vx wcel cc wf cc0 csn w3a cfv c1 cdiv co cmul ffnd offn wa eqidd cv cxp
      cdif cof simp1 simp2 wfn fnconstg mp1i simp3 inidm 1cnd ofc1 wne ffvelcdm
      ax-1cn wceq sylan eldifsn sylib divrec eqcomd 3expb syl2anc eqtr4d offveq
      ofval ) ADFZAGBHZAGIJUCZCHZKZEAEUAZBLZMVMCLZNOZPBAMJUBZCNUDZOBCVROZDVHVIV
      KUEZVLAGBVHVIVKUFZQZVLAANAVQCDDMGFVQAUGVLUPAMGUHUIVLAVJCVHVIVKUJZQZVTVTAU
      KZRVLAANABCDDWBWDVTVTWERVLVMAFZSZVNTZVLAMVONCDGVMVTVLULWDWGVOTZUMWGVNVPPO
      ZVNVONOZVMVSLWGVNGFZVOGFZVOIUNZSZWJWKUQZVLVIWFWLWAAGVMBUOURVLVKWFWOWCVKWF
      SVOVJFWOAVJVMCUOVOGIUSUTURWLWMWNWPWLWMWNKWKWJVNVOVAVBVCVDVLAAVNVONABCDDVM
      WBWDVTVTWEWHWIVGVEVF $.

    $( Function analogue of ~ divcan4 .  (Contributed by Steve Rodriguez,
       4-Nov-2015.) $)
    ofdivcan4 $p |- ( ( A e. V /\ F : A --> CC /\ G : A --> ( CC \ { 0 } ) )
      -> ( ( F oF x. G ) oF / G ) = F ) $=
      ( vx wcel cc wf cc0 csn cdif cfv cmul co cdiv ffnd eqidd ffvelcdm sylan
      wa w3a cv cof simp1 simp2 simp3 inidm offn ofval wne wceq eldifsn divcan4
      sylib 3expb syl2anc offveq ) ADFZAGBHZAGIJKZCHZUAZEAEUBZBLZVCCLZMNZVEOBCM
      UCNCBDURUSVAUDZVBAAMABCDDVBAGBURUSVAUEZPZVBAUTCURUSVAUFZPZVGVGAUGZUHVKVIV
      BAAVDVEMABCDDVCVIVKVGVGVLVBVCAFZTZVDQVNVEQZUIVOVNVDGFZVEGFZVEIUJZTZVFVEON
      VDUKZVBUSVMVPVHAGVCBRSVBVAVMVSVJVAVMTVEUTFVSAUTVCCRVEGIULUNSVPVQVRVTVDVEU
      MUOUPUQ $.
  $}

  ${
    $d x A $.  $d x F $.  $d x G $.  $d x H $.  $d x V $.
    $( Function analogue of ~ divdiv2 .  (Contributed by Steve Rodriguez,
       23-Nov-2015.) $)
    ofdivdiv2 $p |- ( ( ( A e. V /\ F : A --> CC ) /\ ( G : A --> ( CC \ { 0 }
        ) /\ H : A --> ( CC \ { 0 } ) ) ) -> ( F oF / ( G oF / H ) ) = ( ( F oF
        x. H ) oF / G ) ) $=
      ( wcel cc wf wa cc0 cfv cdiv co cmul ffnd offn eqidd ffvelcdm sylan ofval
      vx csn cdif cv cof simpll simplr simprl simprr inidm wceq eldifsn divdiv2
      wne sylib syl3anc oveq2d 3eqtr4d offveq ) AEFZAGBHZIZAGJUBUCZCHZAVCDHZIZI
      ZUAAUAUDZBKZVHCDLUEZMZKZLBVKBDNUEMZCVJMZEUTVAVFUFZVGAGBUTVAVFUGZOZVGAALAC
      DEEVGAVCCVBVDVEUHZOZVGAVCDVBVDVEUIZOZVOVOAUJZPVGAALAVMCEEVGAANABDEEVQWAVO
      VOWBPZVSVOVOWBPVGVHAFZIZVIQZWEVLQWEVIVHCKZVHDKZLMZLMZVIWHNMZWGLMZVIVLLMVH
      VNKWEVIGFZWGGFWGJUNIZWHGFWHJUNIZWJWLUKVGVAWDWMVPAGVHBRSVGVDWDWNVRVDWDIWGV
      CFWNAVCVHCRWGGJULUOSVGVEWDWOVTVEWDIWHVCFWOAVCVHDRWHGJULUOSVIWGWHUMUPWEVLW
      IVILVGAAWGWHLACDEEVHVSWAVOVOWBWEWGQZWEWHQZTUQVGAAWKWGLAVMCEEVHWCVSVOVOWBV
      GAAVIWHNABDEEVHVQWAVOVOWBWFWQTWPTURUS $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Calculus
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x y $.
    $( Example of the Fundamental Theorem of Calculus, part two ( ~ ftc2 ):
       ` S. ( 1 (,) 2 ) ( ( x ^ 2 ) - 3 ) _d x = -u ( 2 / 3 ) ` .  Section 4.4
       example 1a of [LarsonHostetlerEdwards] p. 311.  (The book teaches ~ ftc2
       as simply the "Fundamental Theorem of Calculus", then ~ ftc1 as the
       "Second Fundamental Theorem of Calculus".)  (Contributed by Steve
       Rodriguez, 28-Oct-2015.)  (Revised by Steve Rodriguez, 31-Oct-2015.) $)
    lhe4.4ex1a $p |- S. ( 1 (,) 2 ) ( ( x ^ 2 ) - 3 ) _d x = -u ( 2 / 3 ) $=
      ( vy c1 c2 co cr c3 cexp cdiv cmul cmin cmpt cdv wceq wtru wcel a1i cc c6
      3cn cioo cv cicc cfv citg cneg 1red 2re cle wbr 1le2 ccncf crn ctg ccnfld
      ctopn cvv cpr reelprrecn recn cn0 3nn0 expcl mpan2 syl cc0 wne 3ne0 divcl
      mp3an23 mulcl sylancr subcld adantl wa ovexd divrec2 mpteq2ia oveq2i cres
      wf wss cdm eqid fmpti ssid ax-resscn ovex dvexp ax-mp 3m1e2 mpteq2i eqtri
      3nn dmmpti mp4an resmpt 3eqtr3i ax-1cn divcli dvmptcmul mptru 3syl 3eqtri
      cn 3t1e3 eqtrdi dvmptsub 1re mp2an w3a 3pm3.2i dvcn rescncf eqeltrri cibl
      mp3an oveq1 oveq1d fvmpt c4 leidi elicc2i mpbir3an oveq2 oveq12d c8 3t2e6
      mp2 oveq1i oveq12i 2cn 6cn addcomli eqtr4i 4cn subaddrii divsubdir eqtr3i
      caddc sseqtrri dvres3 reseq1i sqcl divcan3 eqtr3d 3ex dvmptid iccssre cnt
      tgioo4 iccntr dvmptres2 ioossicc sstri subcl cnelprrecn 2nn c0ex eqeltrdi
      dvmptc cvol ioombl cniccibl iblss eqeltrd ftc2 itgeq2 cu2 divdiri divmuli
      mprg 6p2e8 mpbir subsub3 4p2e6 cz 3z 1exp sub4 pm3.2i 2m1e1 dividi divneg
      3p1e4 negsubdi2i negeqi ) ACDUAEZAUBZFBCDUCEZBUBZGHEZGIEZGUWKJEZKEZLZMEZU
      DZUEZDUWPUDZCUWPUDZKEZAUWHUWIDHEZGKEZUEZDGIEZUFZUWSUXBNOACDUWPOUGDFPZOUHQ
      CDUIUJZOUKQOUWQBUWHUWKDHEZGKEZLZUWHRULEZOBUWOUXKFUAUMUNUDZUOUPUDZUQFUWHUW
      JFFRURZPZOUSQZUWKFPZUWORPOUXSUWMUWNUXSUWLRPZUWMRPZUXSUWKRPZUXTUWKUTZUYBGV
      APUXTVBUWKGVCVDZVEZUXTGRPZGVFVGZUYATVHUWLGVIVJVEZUXSUYFUYBUWNRPZTUYCGUWKV
      KVLZVMZVNOUXSVOZUXJGKVPOBUWMUXJUWNGFUQUQFUXRUXSUYAOUYHVNUYLUWKDHVPFBFUWML
      ZMEZBFUXJLZNOUYNFBFCGIEZUWLJEZLZMEZBFUYPGUXJJEZJEZLZUYOUYMUYRFMBFUWMUYQUX
      SUXTUWMUYQNZUYEUXTUYFUYGVUCTVHUWLGVQVJVEVRVSUYSVUBNOBUWLUYTUYPFUQFUXRUXSU
      XTOUYEVNUYLGUXJJVPFBFUWLLZMEZBFUYTLZNOFBRUWLLZFVTZMEZRVUGMEZFVTZVUEVUFUXQ
      RRVUGWARRWBZFVUJWCZWBVUIVUKNUSBRRUWLVUGVUGWDUYDWERWFZFRVUMWGBRUYTVUJGUXJJ
      WHVUJBRGUWKGCKEZHEZJEZLZBRUYTLZGXEPVUJVURNWNBGWIWJBRVUQUYTVUPUXJGJVUODUWK
      HWKVSVSWLWMZWOUUARFVUGUUBWPVUHVUDFMFRWBZVUHVUDNWGBRFUWLWQWJVSVUKVUSFVTZVU
      FVUJVUSFVUTUUCVVAVVBVUFNWGBRFUYTWQWJWMWRQUYPRPZOCGWSTVHWTZQXAXBBFVUAUXJUX
      SUYTGIEZVUAUXJUXSUYBUYTRPZVVEVUANZUYCUYBUYFUXJRPZVVFTUWKUUDZGUXJVKVLVVFUY
      FUYGVVGTVHUYTGVQVJXCUXSUYBVVHVVEUXJNZUYCVVIVVHUYFUYGVVJTVHUXJGUUEVJXCUUFV
      RXDQUXSUYIOUYJVNGUQPUYLUUGQOFBFUWNLMEBFGCJEZLBFGLOBUWKCGFFFUXRUXSUYBOUYCV
      NUYLUGOBFUXRUUHUYFOTQZXABFVVKGXFWLXGXHZUWJFWBZOCFPZUXHVVNXIUHCDUUIXJZQUUK
      UXOWDUWJUXNUUJUDUDUWHNZOVVOUXHVVQXIUHCDUULXJQUUMZBUWJUXKLZUWHVTZUXLUXMUWH
      UWJWBZVVTUXLNCDUUNZBUWJUWHUXKWQWJVWAVVSUWJRULEZPZVVTUXMPVWBBRUXKLZUWJVTZV
      VSVWCUWJRWBZVWFVVSNUWJFRVVPWGUUOZBRUWJUXKWQWJVWGVWERRULEPZVWFVWCPVWHVULRR
      VWEWAZVULXKRVWEMEZWCRNVWIVULVWJVULVUNBRRUXKVWEVWEWDUYBVVHUXKRPZVVIVVHUYFV
      WLTUXJGUUPVDVEWEVUNXLBRDUWKDCKEZHEZJEZVFKEZVWKVWOVFKWHVWKBRVWPLNOBUXJVWOG
      VFRUQUQRRUXPPOUUQQZUYBVVHOVVIVNOUYBVOZDVWNJVPRBRUXJLMEBRVWOLNZODXEPVWSUUR
      BDWIWJQUYFVWRTQVFUQPVWRUUSQOBGRVWQVVLUVAXHXBWORRVWEXMXJRRUWJVWEXNYIXOZUWJ
      RUWHVVSXNYIXOUUTOUWQUXLXPVVROBUWHUWJUXKUQVWAOVWBQUWHUVBWCPOCDUVCQOUWKUWJP
      VOUXJGKVPVVSXPPZOVVOUXHVWDVXAXIUHVWTCDVVSUVDXQQUVEUVFUWPVWCPOBFUWOLZUWJVT
      ZUWPVWCVVNVXCUWPNVVPBFUWJUWOWQWJVVNVXBFRULEPZVXCVWCPVVPVVAFRVXBWAZFFWBZXK
      FVXBMEZWCFNVXDVVAVXEVXFWGBFRUWOVXBVXBWDUYKWEFWFXLBFUXKVXGUXJGKWHVXGBFUXKL
      NVVMXBWOFFVXBXMXJFRUWJVXBXNYIXOQUVGXBUWRUXDNUWSUXENAUWHAUWHUWRUXDUVHBUWIU
      XKUXDUWHUWQUWKUWINUXJUXCGKUWKUWIDHXRXSUWQUXLNVVRXBUXCGKWHXTUVLUXBCGKEZGIE
      ZUXGUXBUYPGGIEZKEZVXIUXBUYPCKEZVXKUXBUXFYAKEZUYPGKEZKEZUXFUYPKEZYAGKEZKEZ
      VXLUWTVXMUXAVXNKDUWJPZUWTVXMNVXSUXHUXIDDUIUJUHUKDUHYBCDDXIUHYCYDBDUWOVXMU
      WJUWPUWKDNZUWODGHEZGIEZGDJEZKEZVXMVXTUWMVYBUWNVYCKVXTUWLVYAGIUWKDGHXRXSUW
      KDGJYEYFVYDYGGIEZSKEZUXFSDKEZKEZVXMVYBVYEVYCSKVYAYGGIUVIYJYHYKVYFUXFDYTEZ
      SKEZVYHVYEVYISKDSYTEZGIEUXFSGIEZYTEVYEVYIDSGYLYMTVHUVJVYKYGGISDYGYMYLUVMY
      NYJVYLDUXFYTVYLDNVYCSNYHSGDYMTYLVHUVKUVNVSWRYJUXFRPZSRPDRPZVYHVYJNDGYLTVH
      WTZYMYLUXFSDUVOXQYOVYGYAUXFKSDYAYMYLYPYADSYPYLUVPYNYQVSXDXGUWPWDZUXFYAKWH
      XTWJCUWJPZUXAVXNNVYQVVOCCUIUJUXIXICXIYBUKCDCXIUHYCYDBCUWOVXNUWJUWPUWKCNZU
      WOCGHEZGIEZVVKKEVXNVYRUWMVYTUWNVVKKVYRUWLVYSGIUWKCGHXRXSUWKCGJYEYFVYTUYPV
      VKGKVYSCGIGUVQPVYSCNUVRGUVSWJYJXFYKXGVYPUYPGKWHXTWJYKVYMYARPVVCUYFVXOVXRN
      VYOYPVVDTUXFYAUYPGUVTWPVXPUYPVXQCKVWMGIEZVXPUYPVYNCRPZUYFUYGVOZWUAVXPNYLW
      SUYFUYGTVHUWAZDCGYRXQVWMCGIUWBYJYSYAGCYPTWSUWEYQYKXDVXJCUYPKGTVHUWCVSYOWU
      BUYFWUCVXIVXKNWSTWUDCGGYRXQYOUXGDUFZGIEZVXIVYNUYFUYGUXGWUFNYLTVHDGUWDXQVX
      HWUEGIVUOUFVXHWUEGCTWSUWFVUODWKUWGYSYJYOYOWR $.
  $}

  $( Derivative of a constant function on the real or complex numbers.  The
     function may return a complex ` A ` even if ` S ` is ` RR ` .
     (Contributed by Steve Rodriguez, 11-Nov-2015.) $)
  dvsconst $p |- ( ( S e. { RR , CC } /\ A e. CC ) -> ( S _D ( S X. { A } ) )
    = ( S X. { 0 } ) ) $=
    ( cr cc cpr wcel wa csn cxp cres cdv co cc0 wss cdm wceq adantr xpssres syl
    wf fconst6g anim2i recnprss c0ex fconst fdmi sseqtrrdi dvconst adantl dmeqd
    sseqtrrd ssid jctil dvres3 syl2anc oveq2d reseq1d eqtrd 3eqtr3d ) BCDEFZADF
    ZGZBDAHZIZBJZKLZDVDKLZBJZBBVCIZKLZBMHZIZVBUTDDVDTZGDDNZBVGOZNZGVFVHPVAVMUTD
    ADUAUBVBVPVNVBBDVKIZOZVOUTBVRNVAUTBDVRBUCZDVKVQDMUDUEUFUGQVBVGVQVAVGVQPUTAU
    HUIZUJUKDULUMDBVDUNUOUTVFVJPVAUTVEVIBKUTBDNZVEVIPVSDVCBRSUPQVBVHVQBJZVLVBVG
    VQBVTUQUTWBVLPZVAUTWAWCVSDVKBRSQURUS $.

  $( Derivative of the identity function on the real or complex numbers.
     (Contributed by Steve Rodriguez, 11-Nov-2015.) $)
  dvsid $p |- ( S e. { RR , CC } -> ( S _D ( _I |` S ) ) = ( S X. { 1 } ) ) $=
    ( cr cc cpr wcel cid cres cdv co c1 csn cxp wf wa wss cdm wceq wfn crn dvid
    fnresi rnresi eqimssi df-f mpbir2an jctr recnprss 1ex fconst fdmi sseqtrrdi
    dmeqi eqtri jctil dvres3 syl2anc resabs1d oveq2d reseq1i xpssres eqtrid syl
    ssid 3eqtr3d ) ABCDEZAFCGZAGZHIZCVFHIZAGZAFAGZHIAJKZLZVEVECCVFMZNCCOZAVIPZO
    ZNVHVJQVEVNVNVFCRVFSZCOCUAVRCCUBUCCCVFUDUEUFVEVQVOVEACVPAUGZVPCVLLZPCVIVTTU
    LCVLVTCJUHUIUJUMUKCVCUNCAVFUOUPVEVGVKAHVEFACVSUQURVEACOZVJVMQVSWAVJVTAGVMVI
    VTATUSCVLAUTVAVBVD $.

  $( Derivative of the exponential function on the real or complex numbers.
     (Contributed by Steve Rodriguez, 12-Nov-2015.) $)
  dvsef $p |- ( S e. { RR , CC } -> ( S _D ( exp |` S ) ) = ( exp |` S ) ) $=
    ( cr cc cpr wcel ce cres cdv co wf wa wss cdm wceq jctr recnprss dvef dmeqi
    eff fdmi eqtri sseqtrrdi ssid jctil dvres3 syl2anc reseq1i eqtrdi ) ABCDEZA
    FAGZHIZCFHIZAGZUJUIUICCFJZKCCLZAULMZLZKUKUMNUIUNSOUIUQUOUIACUPAPUPFMCULFQRC
    CFSTUAUBCUCUDCAFUEUFULFAQUGUH $.

  ${
    $d t y C $.  $d t y K $.  $d t y S $.  $d x y K $.  $d x y ph $.
    expgrowthi.s $e |- ( ph -> S e. { RR , CC } ) $.
    expgrowthi.k $e |- ( ph -> K e. CC ) $.
    expgrowthi.y0 $e |- ( ph -> C e. CC ) $.
    expgrowthi.yt $e |- Y = ( t e. S |-> ( C x. ( exp ` ( K x. t ) ) ) ) $.
    $( Exponential growth and decay model.  See ~ expgrowth for more
       information.  (Contributed by Steve Rodriguez, 4-Nov-2015.) $)
    expgrowthi $p |- ( ph -> ( S _D Y ) = ( ( S X. { K } ) oF x. Y ) ) $=
      ( vy cdv co cmul ce cmpt wceq wcel cc cr vx cfv csn cxp cof fveq2d oveq2d
      cv oveq2 cbvmptv eqtri oveq2i cvv cpr wo elpri eleq2 recn biimtrdi biimpd
      wi jaoi 3syl imp wa mulcl sylan syl syldan ovexd cnelprrecn adantr adantl
      efcl a1i c1 1cnd dvmptid dvmptcmul mulridd mpteq2dv eqtrd dvef wfn wf eff
      ffn ax-mp dffn5 mpbi 3eqtr3i dvmptco mulcom syl2anr anabss5 mpteq2dva w3a
      fveq2 3anim123i 3anidm12 mul12 eqtrid fconstmpt offval2 eqtr4d ) ADFLMZKD
      ECEKUHZNMZOUBZNMZNMZPZDEUCUDZFNUEMAXFDKDXJPZLMZXLFXNDLFBDCEBUHZNMZOUBZNMZ
      PXNJBKDXSXJXPXGQZXRXICNXTXQXHOXPXGENUIUFUGUJUKZULAXOKDCEXINMZNMZPXLAKXIYB
      CDUMDGAXGDRZXGSRZXISRZAYDYEADTSUNZRDTQZDSQZUOYDYEVAZGDTSUPYHYJYIYHYDXGTRY
      EDTXGUQXGURUSYIYDYEDSXGUQUTVBVCVDZAYEVEXHSRZYFAESRZYEYLHEXGVFVGZXHVNVHVIZ
      AYDVEZEXINVJADKDXIPLMKDXIENMZPKDYBPAKUAXHEUAUHZOUBZYSDSXIXISSDSGSYGRAVKVO
      AYDYEYLYKYNVIAYMYDHVLZYRSRYSSRAYRVNVMZUUAADKDXHPLMKDEVPNMZPKDEPZAKXGVPEDS
      DGYKYPVQAKDGVRHVSAKDUUBEAEHVTWAWBSUASYSPZLMZUUDQASOLMOUUEUUDWCOUUDSLOSWDZ
      OUUDQSSOWEUUFWFSSOWGWHUASOWIWJZULUUGWKVOYRXHOWRZUUHWLAKDYQYBAYDYQYBQZYPYF
      YMUUIAYOHXIEWMWNWOWPWBIVSAKDYCXKYPCSRZYMYFWQZYCXKQAYDUUKAYPUUKAUUJAYMYPYF
      IHYOWSWTWOCEXIXAVHWPWBXBAKDEXJNXMFYGSUMGYTYPCXINVJXMUUCQAKDEXCVOFXNQAYAVO
      XDXE $.
  $}

  ${
    $d c x S $.  $d c x Y $.  $d x y S $.  $d x y ph $.  $d y Y $.
    dvconstbi.s $e |- ( ph -> S e. { RR , CC } ) $.
    dvconstbi.y $e |- ( ph -> Y : S --> CC ) $.
    dvconstbi.dy $e |- ( ph -> dom ( S _D Y ) = S ) $.
    $( The derivative of a function on ` S ` is zero iff it is a constant
       function.  Roughly a biconditional ` S ` analogue of ~ dvconst and
       ~ dveq0 .  Corresponds to integration formula " ` S. 0 _d x = C ` " in
       section 4.1 of [LarsonHostetlerEdwards] p. 278.  (Contributed by Steve
       Rodriguez, 11-Nov-2015.) $)
    dvconstbi $p |- ( ph -> ( ( S _D Y ) = ( S X. { 0 } ) <-> E. c e. CC Y =
      ( S X. { c } ) ) ) $=
      ( vx co cc0 cxp wceq cc wa cfv wcel cr syl adantr 3adant2 vy cdv csn wrex
      cv wf wo cpr elpri 0re mpbiri 0cn jaoi ffvelcdm syl2anc wfn ffnd cvv fvex
      eleq2 fnconstg mp1i fvconst2 adantl w3a cmin cabs cle cmul cpnf ccom cres
      wbr cbl eqid sblpnf mpdan eleq2d biimpar eleqtrrd ssidd cxr pnfxr a1i cdm
      wss eqtr4d eqimss biimpa fveq1 c0ex sylan9eq eqeltrdi abscld abs00bd eqle
      3adant1 syld3an3 3expa dvlip2 sylanr1 3impdi syl3an3 recnprss sseld subcl
      mpan syl6 imp recnd mul02d breqtrd anim12dan sylan 3impb syl3an2 3anidm12
      absge0d letri3 sylancl mpbir2and abs00ad mpbid subeq0 eqtr2d eqfnfvd sneq
      wb xpeq2d rspceeqv ex oveq2 3ad2ant3 dvsconst 3adant3 eqtrd impbid eqeq2d
      rexlimdv3a cbvrexvw bitr4di ) ABCUBIZBJUCKZLZCBHUEZUCZKZLZHMUDZCBDUEZUCZK
      ZLZDMUDAUUDUUIAUUDUUIAUUDNZJCOZMPZCBUUOUCZKZLUUIAUUPUUDABMCUFZJBPZUUPFABQ
      LZBMLZUGZUUTABQMUHPZUVCEBQMUIRUVAUUTUVBUVAUUTJQPZUJBQJUTUKUVBUUTJMPZULBMJ
      UTUKUMRZBMJCUNZUOSUUNUABCUURACBUPUUDABMCFUQSUUOURPUURBUPUUNJCUSZBUUOURVAV
      BUUNUAUEZBPZNUVJUUROZUUOUVJCOZUVKUVLUUOLUUNBUUOUVJUVIVCVDAUUDUVKUUOUVMLZA
      UUDUVKVEZUUOUVMVFIZJLZUVNUVOUVPVGOZJLZUVQUVOUVSUVRJVHVMZJUVRVHVMZUVOUVRJJ
      UVJVFIZVGOZVIIZJVHAUUDUVKUVRUWDVHVMZAUUDAUVKNZUWEUWFAUUDUVJJVJVGVFVKBBKVL
      ZVNOIZPZUWEAUWIUVKAUWHBUVJAUUTUWHBLZUVGAUWGJBEUWGVOZVPVQZVRVSAUUDUWIUWEAU
      UNJUWHPUWIUWEAJBUWHUVGUWLVTUUNHJUWHVJBCUWGJBJUVJAUVDUUDESUWKUUNBWAAUUSUUD
      FSAUUTUUDUVGSVJWBPUUNWCWDUWHVOUUNUWHUUBWEZLUWHUWMWFUUNUWHBUWMAUWJUUDUWLSA
      UWMBLUUDGSWGUWHUWMWHRUVEUUNUJWDAUUDUUEUWHPZUUEUUBOZVGOZJVHVMZAUUDUWNUUEBP
      ZUWQAUWNUWRUUDAUWNUWRAUWHBUUEUWLVRWITUUDUWRUWQAUUDUWRNZUWPQPUWPJLUWQUWSUW
      OUWSUWOJMUUDUWRUWOUUEUUCOJUUEUUBUUCWJBJUUEWKVCWLZULWMWNUWSUWOUWTWOUWPJWPU
      OWQWRWSWTXAXBXCWSXBAUVKUWDJLUUDUWFUWCUWFUWCAUVKUWCQPZAUVKUVJMPZUXAABMUVJA
      UVDBMWFEBXDRXEUVFUXBUXAULUVFUXBNUWBJUVJXFWNXGXHXIXJXKTXLAUVKUWAUUDUWFUVPU
      WFUUPUVMMPZNZUVPMPAUVKUXDAAUUTUVKUXDUVGAUUTUVKUXDAUUSUUTUVKNUXDFUUSUUTUUP
      UVKUXCUVHBMUVJCUNXMXNXOXPXQZUUOUVMXFRZXRTAUVKUVSUVTUWANYHZUUDUWFUVRQPUVEU
      XGUWFUVPUXFWNUJUVRJXSXTTYAAUVKUVSUVQYHUUDUWFUVPUXFYBTYCAUVKUVQUVNYHZUUDUW
      FUXDUXHUXEUUOUVMYDRTYCWSYEYFHUUOMUUGUURCUUEUUOLUUFUUQBUUEUUOYGYIYJUOYKAUU
      HUUDHMAUUEMPZUUHVEUUBBUUGUBIZUUCUUHAUUBUXJLUXICUUGBUBYLYMAUXIUXJUUCLZUUHA
      UVDUXIUXKEUUEBYNXNYOYPYSYQUUMUUHDHMUUJUUELZUULUUGCUXLUUKUUFBUUJUUEYGYIYRY
      TUUA $.
  $}

  ${
    $d c t u x K $.  $d c t u x S $.  $d c x Y $.  $d u x y z K $.
    $d u x y z ph $.  $d y z S $.  $d y z Y $.
    expgrowth.s $e |- ( ph -> S e. { RR , CC } ) $.
    expgrowth.k $e |- ( ph -> K e. CC ) $.
    expgrowth.y $e |- ( ph -> Y : S --> CC ) $.
    expgrowth.dy $e |- ( ph -> dom ( S _D Y ) = S ) $.
    $( Exponential growth and decay model.  The derivative of a function _y_ of
       variable _t_ equals a constant _k_ times _y_ itself, iff _y_ equals some
       constant _C_ times the exponential of _kt_.  This theorem and
       ~ expgrowthi illustrate one of the simplest and most crucial classes of
       _differential equations_, equations that relate functions to their
       derivatives.

       Section 6.3 of [Strang] p. 242 calls _y_' = _ky_ "the most important
       differential equation in applied mathematics".  In the field of
       population ecology it is known as the _Malthusian growth model_ or
       _exponential law_, and _C_, _k_, and _t_ correspond to initial
       population size, growth rate, and time respectively
       ( ~ https://en.wikipedia.org/wiki/Malthusian_growth_model ); and in
       finance, the model appears in a similar role in _continuous compounding_
       with _C_ as the initial amount of money.  In _exponential decay_ models,
       _k_ is often expressed as the negative of a positive constant &lambda;.

       Here _y_' is given as ` ( S _D Y ) ` , _C_ as ` c ` , and _ky_ as
       ` ( ( S X. { K } ) oF x. Y ) ` . ` ( S X. { K } ) ` is the constant
       function that maps any real or complex input to _k_ and ` oF x. ` is
       multiplication as a function operation.

       The leftward direction of the biconditional is as given in
       ~ http://www.saylor.org/site/wp-content/uploads/2011/06/MA221-2.1.1.pdf
       pp. 1-2, which also notes the reverse direction ("While we will not
       prove this here, it turns out that these are the only functions that
       satisfy this equation.").  The rightward direction is Theorem 5.1 of
       [LarsonHostetlerEdwards] p. 375 (which notes " _C_ is the _initial
       value_ of _y_, and _k_ is the _proportionality constant_. _Exponential
       growth_ occurs when _k_ > 0, and _exponential decay_ occurs when _k_ <
       0."); its proof here closely follows the proof of _y_' = _y_ in
       ~ https://proofwiki.org/wiki/Exponential_Growth_Equation/Special_Case .

       Statements for this and ~ expgrowthi formulated by Mario Carneiro.
       (Contributed by Steve Rodriguez, 24-Nov-2015.) $)
    expgrowth $p |- ( ph -> ( ( S _D Y ) = ( ( S X. { K } ) oF x. Y ) <-> E. c
        e. CC Y = ( t e. S |-> ( c x. ( exp ` ( K x. t ) ) ) ) ) ) $=
      ( vu vx vy co cmul wceq ce cc wcel adantr vz cdv csn cxp cof cv cmpt wrex
      cfv wa cneg cc0 caddc cr cpr cnelprrecn a1i wss recnprss syl sseld syl6an
      mulcl imp negcld efcl adantl c1 ax-1cn dvmptid dvmptcmul mulridd mpteq2dv
      eqtrd dvmptneg dvef wfn wf eff ffn ax-mp dffn5 mpbi 3eqtr3i fveq2 dvmptco
      oveq2i oveq2d mulcld fmpttd feq1d mpbird mulcom eqtr3d fconst6g fconstmpt
      caofcom eqidd offval2 cdm dmeqd eqid dmmptd dvmulf 3eqtr4rd ofmul12 oveq1
      syl22anc oveq1d sylan9eq w3a mulass caofass eqeq2d inidm off caofdir cmin
      adddir ofnegsub syl3anc neg1cn fconst6 ofc12 mulm1d sneqd ofsubid syl2anc
      wb xpeq2d mpbid wi cdiv wne efne0 cvv mpteq2dva sylan2 oveq2 weq 0cnd 0cn
      3eqtr3d mul02 caofid2 fdmi eqtrdi dvconstbi cdif eldifsn ofdivcan4 eqeq1d
      sylanbrc imbitrid vex ovexd efneg jca ax-1ne0 pm3.2i divdiv2 mp3an2 div1d
      ancoms an32s sylibd reximdva mpd simprl expgrowthi 3impb eqeq12d 3ad2ant3
      ex rexlimdv3a impbid fveq2d cbvmptv eqtrid cbvrexvw bitrdi ) ACEUBNZCDUCU
      DZEOUEZNZPZEKCLUFZDKUFZONZQUIZONZUGZPZLRUHZEBCFUFZDBUFZONZQUIZONZUGZPZFRU
      HAUWFUWNAUWFUWNAUWFUJZEKCUWIUKZQUIZUGZUWDNZCUWGUCUDZPZLRUHZUWNUXBCUXFUBNZ
      CULUCZUDZPUXIUXBUXJUXLUXEUWDNZUXLUXBUXJUWECDUKZUCZUDZEUWDNZUMUEZNZUXEUWDN
      ZPZUXJUXMPZUXBUYAUXJUWEUXEUWDNZUXQUXEUWDNZUXRNZPZUXBUYFUXJUYCUXPUXFUWDNZU
      XRNZPZAUWFUXJUWBUXEUWDNZUYGUXRNZUYHAUXJUYJEUXPUXEUWDNZUWDNZUXRNZUYKAUYJEK
      CUXDUXNONZUGZUWDNZUXRNUYJCUXEUBNZEUWDNZUXRNUYNUXJAUYQUYSUYJUXRAEUYRUWDNUY
      QUYSAUYRUYPEUWDAKMUXCUXNMUFZQUIZVUACRUXDUXDRRCRGRUNRUOZSAUPUQAUWHCSZUJZUW
      IAVUCUWIRSZADRSZVUCUWHRSZVUEHACRUWHACVUBSZCRURGCUSUTVAZDUWHVCVBVDZVEZAUXN
      RSZVUCADHVEZTZUYTRSZVUARSAUYTVFVGZVUPAKUWIDCRCGVUJAVUFVUCHTACKCUWIUGUBNKC
      DVHONZUGKCDUGAKUWHVHDCRCGAVUCVUGVUIVDVHRSZVUDVIUQAKCGVJHVKAKCVUQDADHVLVMV
      NVORMRVUAUGZUBNZVUSPARQUBNQVUTVUSVPQVUSRUBQRVQZQVUSPRRQVRVVAVSRRQVTWAMRQW
      BWCZWGVVBWDUQUYTUXCQWEZVVCWFZWHALMCOREUYRVUBGIACRUYRVRCRUYPVRAKCUYORVUDUX
      DUXNVUDUXCRSZUXDRSZVUKUXCVFZUTZVUNWIZWJACRUYRUYPVVDWKWLUWGRSZVUOUJZUWGUYT
      ONZUYTUWGONPAUWGUYTWMVGZWQWNWHAUYMUYQUYJUXRAUYLUYPEUWDAUYLUXEUXPUWDNUYPAL
      MCORUXPUXEVUBGAVULCRUXPVRZVUMCUXNRWOUTZAKCUXDRVVHWJZVVMWQAKCUXDUXNOUXEUXP
      VUBRRGVVHVUNAUXEWRUXPKCUXNUGPAKCUXNWPUQWSVNWHWHACEUXECGIVVPJAUYRWTUYPWTCA
      UYRUYPVVDXAAKUYPCUYORUYPXBVVIXCVNXDXEAUYMUYGUYJUXRAVUHCREVRZVVNCRUXEVRUYM
      UYGPGIVVOVVPCEUXPUXEVUBXFXHWHVNUWFUYJUYCUYGUXRUWBUWEUXEUWDXGXIXJAUYFUYIYI
      UWFAUYEUYHUXJAUYDUYGUYCUXRALMUACOOROUXPEUXEOVUBGVVOIVVPVVJVUOUAUFZRSXKZVV
      LVVRONUWGUYTVVRONZONPAUWGUYTVVRXLVGZXMWHXNTWLAUYAUYFYIUWFAUXTUYEUXJALMUAC
      UMROUXEUWEUXQRUMVUBGVVPALMCCCORRRUWCEVUBVUBVVKVVLRSAUWGUYTVCVGZAVUFCRUWCV
      RHCDRWOUTZIGGCXOZXPZALMCCCORRRUXPEVUBVUBVWBVVOIGGVWDXPVVSUWGUYTUMNVVRONUW
      GVVRONVVTUMNPAUWGUYTVVRXSVGXQXNTWLAUYAUYBYIUWFAUXTUXMUXJAUXSUXLUXEUWDAUWE
      CVHUKZUCUDZUWEUWDNZUXRNZUWEUWEXRUENZUXSUXLAVUHCRUWEVRZVWKVWIVWJPGVWEVWECU
      WEUWEVUBXTYAAVWHUXQUWEUXRAVWGUWCUWDNZEUWDNVWHUXQALMUACOOROVWGUWCEOVUBGCRV
      WGVRACVWFRYBYCUQVWCIVWAXMAVWLUXPEUWDAVWLCVWFDONZUCZUDUXPACVWFDOVUBRRGVWFR
      SAYBUQHYDAVWNUXOCAVWMUXNADHYEYFYJVNXIWNWHAVUHVWKVWJUXLPGVWECUWEVUBYGYHUUC
      XIXNTYKAUXMUXLPUWFALCULULORUXEVUBRRGVVPAUUAZVWOVVJULUWGONULPAUWGUUDVGUUET
      VNZUXBCUXFLAVUHUWFGTACRUXFVRUWFALMCCCORRREUXEVUBVUBVWBIVVPGGVWDXPTUXBUXJW
      TUXLWTCUXBUXJUXLVWPXACRUXLCULRUUBYCUUFUUGUUHYKAUXIUWNYLUWFAUXHUWMLRAVVJUJ
      ZUXHEUXGUXEYMUEZNZPZUWMAUXHVWTYLVVJUXHUXFUXEVWRNZVWSPAVWTUXFUXGUXEVWRXGAV
      XAEVWSAVUHVVQCRUXKUUIZUXEVRVXAEPGIAKCUXDVXBVUDVVEUXDVXBSZVUKVVEVVFUXDULYN
      VXCVVGUXCYOUXDRULUUJUUMUTWJCEUXEVUBUUKYAUULUUNTVWQVWSUWLEVWQVWSKCUWGVHUWJ
      YMNZYMNZUGZUWLAVWSVXFPVVJAKCUWGVXDYMUXGUXEVUBYPYPGUWGYPSVUDLUUOUQVUDVHUWJ
      YMUUPUXGKCUWGUGPAKCUWGWPUQAKCUXDVXDVUDVUEUXDVXDPVUJUWIUUQUTYQWSTVWQKCVXEU
      WKAVUCVVJVXEUWKPZVVJVUDVXGVVJVUDUJZVXEUWKVHYMNZUWKVUDVVJUWJRSZUWJULYNZUJZ
      VXEVXIPZVUDVUEVXLVUJVUEVXJVXKUWIVFZUWIYOUURUTVVJVURVHULYNZUJVXLVXMVURVXOV
      IUUSUUTUWGVHUWJUVAUVBYRVXHUWKVUDVVJVXJUWKRSVUDVUEVXJVUJVXNUTUWGUWJVCYRUVC
      VNUVDUVEYQVNXNUVFUVGTUVHUVNAUWMUWFLRAVVJUWMXKUWFCUWLUBNZUWCUWLUWDNZPZAVVJ
      UWMVXRAVVJUWMUJZUJKUWGCDUWLAVUHVXSGTAVUFVXSHTAVVJUWMUVIUWLXBUVJUVKUWMAUWF
      VXRYIVVJUWMUWBVXPUWEVXQEUWLCUBYSEUWLUWCUWDYSUVLUVMWLUVOUVPUWMUXALFRLFYTZU
      WLUWTEVXTUWLBCUWGUWRONZUGUWTKBCUWKVYAKBYTZUWJUWRUWGOVYBUWIUWQQUWHUWPDOYSU
      VQWHUVRVXTBCVYAUWSUWGUWOUWROXGVMUVSXNUVTUWA $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  The generalized binomial coefficient operation
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c _Cc $.
  $( Extend class notation to include the generalized binomial coefficient
     operation. $)
  cbcc $a class _Cc $.

  ${
    $d c k $.
    $( Define a generalized binomial coefficient operation, which unlike
       ~ df-bc allows complex numbers for the first argument.  (Contributed by
       Steve Rodriguez, 22-Apr-2020.) $)
    df-bcc $a |- _Cc = ( c e. CC , k e. NN0 |->
        ( ( c FallFac k ) / ( ! ` k ) ) ) $.
  $}

  ${
    $d c k ph $.  $d c k C $.  $d c k K $.
    bccval.c $e |- ( ph -> C e. CC ) $.
    bccval.k $e |- ( ph -> K e. NN0 ) $.
    $( Value of the generalized binomial coefficient, ` C ` choose ` K ` .
       (Contributed by Steve Rodriguez, 22-Apr-2020.) $)
    bccval $p |- ( ph -> ( C _Cc K ) = ( ( C FallFac K ) / ( ! ` K ) ) ) $=
      ( vc vk cc cn0 cv cfallfac co cfa cfv cdiv cbcc cvv wceq wa oveq12d ovexd
      cmpo df-bcc a1i simprl simprr fveq2d ovmpod ) AFGBCHIFJZGJZKLZUJMNZOLZBCK
      LZCMNZOLPQPFGHIUMUBRAGFUCUDAUIBRZUJCRZSSZUKUNULUOOURUIBUJCKAUPUQUEAUPUQUF
      ZTURUJCMUSUGTDEAUNUOOUAUH $.

    $( Closure of the generalized binomial coefficient.  (Contributed by Steve
       Rodriguez, 22-Apr-2020.) $)
    bcccl $p |- ( ph -> ( C _Cc K ) e. CC ) $=
      ( cbcc co cfallfac cfa cfv cdiv cc bccval wcel fallfaccl syl2anc cn faccl
      cn0 syl nncnd nnne0d divcld eqeltrd ) ABCFGBCHGZCIJZKGLABCDEMAUEUFABLNCSN
      ZUELNDEBCOPAUFAUGUFQNECRTZUAAUFUHUBUCUD $.

    $( The generalized binomial coefficient ` C ` choose ` K ` is zero iff
       ` C ` is an integer between zero and ` ( K - 1 ) ` inclusive.
       (Contributed by Steve Rodriguez, 22-Apr-2020.) $)
    bcc0 $p |- ( ph -> ( ( C _Cc K ) = 0 <-> C e. ( 0 ... ( K - 1 ) ) ) ) $=
      ( vk co cc0 wceq cfv cmin wcel eqeq1d cc cn0 syl2anc wne adantl ad2antrr
      wa cbcc cfallfac cfa cdiv c1 cfz bccval fallfaccl cn faccl nncnd diveq0ad
      syl facne0 cprod fallfacval cuz elfzuz3 nn0uz elfznn0 nn0cn subcld bilani
      cv eqcom subeq0bd fprodeq0 mpdan ex wn fzfid nn0cnd nelne2 necomd adantll
      ancoms subne0d fprodn0 necon4bd impbid bitr4d 3bitrd ) ABCUAGZHIBCUBGZCUC
      JZUDGZHIWDHIZBHCUEKGZUFGZLZAWCWFHABCDEUGMAWDWEABNLZCOLZWDNLDEBCUHPAWEAWLW
      EUILECUJUMUKAWLWEHQECUNUMULAWGWIBFVDZKGZFUOZHIZWJAWDWOHAWKWLWDWOIDEBFCUPP
      MAWJWPAWJWPAWJTZWHBUQJLZWPWJWRABHWHURRWQWNFWHHBOUSWJBOLABWHUTRWQWMOLZTBWM
      AWKWJWSDSWSWMNLZWQWMVARVBWQWMBIZTBWMAWKWJXADSXABWMIWQWMBVEVCVFVGVHVIAWJWO
      HAWJVJZWOHQAXBTZWIWNFXCHWHVKXCWMWILZTZBWMAWKXBXDDSZXDWTXCXDWMWMWHUTVLRZVB
      XEBWMXFXGXBXDBWMQZAXDXBXHXDXBTWMBWMBWIVMVNVPVOVQVRVIVSVTWAWB $.

    $( Generalized binomial coefficient: ` C ` choose ` ( K + 1 ) ` .
       (Contributed by Steve Rodriguez, 22-Apr-2020.) $)
    bccp1k $p |- ( ph -> ( C _Cc ( K + 1 ) ) = ( ( C _Cc K ) x.
        ( ( C - K ) / ( K + 1 ) ) ) ) $=
      ( co cbcc cfallfac cfa cfv cdiv cmul cc wcel cn0 wceq syl2anc syl bccval
      cn c1 caddc cmin fallfacp1 facp1 oveq12d peano2nn0 fallfaccl faccl nn0cnd
      nncnd subcld nnne0d nn0p1nn divmuldivd 3eqtr4d oveq1d eqtr4d ) ABCUAUBFZG
      FZBCHFZCIJZKFZBCUCFZUSKFZLFZBCGFZVELFABUSHFZUSIJZKFVAVDLFZVBUSLFZKFUTVFAV
      HVJVIVKKABMNZCONZVHVJPDEBCUDQAVMVIVKPECUERUFABUSDAVMUSONECUGRZSAVAVBVDUSA
      VLVMVAMNDEBCUHQAVBAVMVBTNECUIRZUKABCDACEUJULAUSVNUJAVBVOUMAUSAVMUSTNECUNR
      UMUOUPAVGVCVELABCDESUQUR $.
  $}

  ${
    bccm1k.c $e |- ( ph -> C e. ( CC \ { ( K - 1 ) } ) ) $.
    bccm1k.k $e |- ( ph -> K e. NN ) $.
    $( Generalized binomial coefficient: ` C ` choose ` ( K - 1 ) ` , when
       ` C ` is not ` ( K - 1 ) ` .  (Contributed by Steve Rodriguez,
       22-Apr-2020.) $)
    bccm1k $p |- ( ph -> ( C _Cc ( K - 1 ) ) = ( ( C _Cc K ) /
        ( ( C - ( K - 1 ) ) / K ) ) ) $=
      ( c1 cmin co cdiv cbcc csn eldifad nncnd 1cnd subcld wcel syl cmul oveq2d
      cc nnne0d divcld cn cn0 nnm1nn0 bcccl cdif eldifsni subne0d divne0d caddc
      wne bccp1k npcand 3eqtr3d mulcomd eqtr2d mvllmuld ) ABCFGHZGHZCIHZBUSJHZB
      CJHZAUTCABUSABTUSKZDLZACFACEMZANZOZOZVFACEUAZUBZABUSVEACUCPUSUDPECUEQZUFZ
      AUTCVIVFABUSVEVHABTVDUGPBUSULDBTUSUHQUIVJUJAVCVBVARHZVAVBRHABUSFUKHZJHVBU
      TVOIHZRHVCVNABUSVEVLUMAVOCBJACFVFVGUNZSAVPVAVBRAVOCUTIVQSSUOAVBVAVMVKUPUQ
      UR $.
  $}

  ${
    bccn0.c $e |- ( ph -> C e. CC ) $.
    $( Generalized binomial coefficient: ` C ` choose ` 0 ` .  (Contributed by
       Steve Rodriguez, 22-Apr-2020.) $)
    bccn0 $p |- ( ph -> ( C _Cc 0 ) = 1 ) $=
      ( cc0 cbcc co cfallfac cfa cfv cdiv c1 cn0 wcel 0nn0 bccval wceq fallfac0
      a1i cc syl fac0 oveq12d 1div1e1 eqtrdi eqtrd ) ABDEFBDGFZDHIZJFZKABDCDLMA
      NROAUHKKJFKAUFKUGKJABSMUFKPCBQTUGKPAUARUBUCUDUE $.

    $( Generalized binomial coefficient: ` C ` choose ` 1 ` .  (Contributed by
       Steve Rodriguez, 22-Apr-2020.) $)
    bccn1 $p |- ( ph -> ( C _Cc 1 ) = C ) $=
      ( c1 cbcc co cmul cc0 caddc cmin cdiv cn0 wcel 0nn0 a1i bccp1k wceq 0p1e1
      oveq12d eqtrd oveq2i bccn0 subid1d div1d 3eqtr3d mullidd ) ABDEFZDBGFZBAB
      HDIFZEFZBHEFZBHJFZUIKFZGFUGUHABHCHLMANOPUJUGQAUIDBERUAOAUKDUMBGABCUBAUMBD
      KFBAULBUIDKABCUCUIDQAROSABCUDTSUEABCUFT $.
  $}

  ${
    bccbc.c $e |- ( ph -> N e. NN0 ) $.
    bccbc.k $e |- ( ph -> K e. NN0 ) $.
    $( The binomial coefficient and generalized binomial coefficient are equal
       when their arguments are nonnegative integers.  (Contributed by Steve
       Rodriguez, 22-Apr-2020.) $)
    bccbc $p |- ( ph -> ( N _Cc K ) = ( N _C K ) ) $=
      ( cc0 cfz co wcel wceq wa cfv adantr adantl eqtr4d wbr c1 cn0 cz syldan
      cbcc cbc cfallfac cfa cdiv nn0cnd bccval bcfallfac clt caddc cuz nn0split
      wn cun wo syl eleqtrd elun sylib orcanai cle eluzle nn0zd zltp1le syl2anc
      wb mpbird nn0ge0d cfzo 0zd syl3anc biimpar cmin fzoval eleq2d biimpa bcc0
      elfzo sylanr1 anabss5 jca bcval3 3expa sylan pm2.61dan ) ABFCGHZIZCBUAHZC
      BUBHZJAWGKWHCBUCHBUDLUEHZWIAWHWJJWGACBACDUFZEUGMWGWIWJJABCUHNOAWGUMZKWHFW
      IAWLCBUIPZWHFJZAWLBCQUJHZUKLZIZWMAWGWQABWFWPUNZIWGWQUOABRWREACRIZRWRJDCUL
      UPUQBWFWPURUSUTAWQKWMWOBVAPZWQWTAWOBVBNAWMWTVFZWQACSIZBSIZXAACDVCZABEVCZC
      BVDVEMVGTAWMWNAAFCVAPZWMWNACDVHAXFWMKZCFBVIHZIZWNAXIXGAXBFSIXCXIXGVFXDAVJ
      XECFBVRVKVLAXICFBQVMHGHZIZWNAXIXKAXHXJCAXCXHXJJXEFBVNUPVOVPAWNXKACBWKEVQV
      LTTVSVTTAWSXCKWLWIFJZAWSXCDXEWAWSXCWLXLBCWBWCWDOWE $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Binomial series
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x y N $.  $d x y Z $.  $d y ph $.  $d x C $.  $d y F $.  $d y M $.
    $d y W $.
    uzmptshftfval.f $e |- F = ( x e. Z |-> B ) $.
    uzmptshftfval.b $e |- B e. _V $.
    uzmptshftfval.c $e |- ( x = ( y - N ) -> B = C ) $.
    uzmptshftfval.z $e |- Z = ( ZZ>= ` M ) $.
    uzmptshftfval.w $e |- W = ( ZZ>= ` ( M + N ) ) $.
    uzmptshftfval.m $e |- ( ph -> M e. ZZ ) $.
    uzmptshftfval.n $e |- ( ph -> N e. ZZ ) $.
    $( When ` F ` is a maps-to function on some set of upper integers ` Z `
       that returns a set ` B ` , ` ( F shift N ) ` is another maps-to function
       on the shifted set of upper integers ` W ` .  (Contributed by Steve
       Rodriguez, 22-Apr-2020.) $)
    uzmptshftfval $p |- ( ph -> ( F shift N ) = ( y e. W |-> C ) ) $=
      ( cfv wcel cc cshi co cmpt wfn wceq cmin crab fnmpti zcnd cvv fvexi mptex
      cv cuz eqeltri shftfn sylancr shftuz syl2anc eleq2i rabbii 3eqtr4g fneq2d
      caddc cz mpbid dffn5 sylib uzssz eqsstri zsscn sstri sseli shftval syl2an
      wa jca eluzsub 3expa sylan sylan2b eleqtrrdi fvmpt3i syl eqtrd mpteq2dva
      ) AFHUAUBZCICUMZWGRZUCZCIEUCAWGIUDZWGWJUEAWGWHHUFUBZJSZCTUGZUDZWKAFJUDHTS
      ZWOBJDFLKUHAHQUIZCHJFFBJDUCUJKBJDJGUNNUKULUOZUPUQAWNIWGAWLGUNRZSZCTUGZGHV
      DUBZUNRZWNIAHVESZGVESZXAXCUEQPCHGURUSWMWTCTJWSWLNUTVAOVBVCVFCIWGVGVHACIWI
      EAWHISZVPZWIWLFRZEAWPWHTSWIXHUEXFWQITWHIVETIXCVEOXBVIVJVKVLVMHWHFWRVNVOXG
      WMXHEUEXGWLWSJXFAWHXCSZWTIXCWHOUTAXEXDVPXIWTAXEXDPQVQXEXDXIWTHGWHVRVSVTWA
      NWBBWLDEJFMKLWCWDWEWFWE $.
  $}

  ${
    $d m r x X $.  $d m n x A $.  $d n X $.  $d m ph $.  $d r G $.  $d m H $.
    dvradcnv2.g $e |- G = ( x e. CC |-> ( n e. NN0 |-> ( ( A ` n ) x. ( x ^ n
        ) ) ) ) $.
    dvradcnv2.r $e |- R = sup ( { r e. RR | seq 0 ( + , ( G ` r ) ) e. dom ~~>
        } , RR* , < ) $.
    dvradcnv2.h $e |- H = ( n e. NN |->
        ( ( n x. ( A ` n ) ) x. ( X ^ ( n - 1 ) ) ) ) $.
    dvradcnv2.a $e |- ( ph -> A : NN0 --> CC ) $.
    dvradcnv2.x $e |- ( ph -> X e. CC ) $.
    dvradcnv2.l $e |- ( ph -> ( abs ` X ) < R ) $.
    $( The radius of convergence of the (formal) derivative ` H ` of the power
       series ` G ` is (at least) as large as the radius of convergence of
       ` G ` .  This version of ~ dvradcnv uses a shifted version of ` H ` to
       match the sum form of ` ( CC _D F ) ` in ~ pserdv2 (and shows how to use
       ~ uzmptshftfval to shift a maps-to function on a set of upper integers).
       (Contributed by Steve Rodriguez, 22-Apr-2020.) $)
    dvradcnv2 $p |- ( ph -> seq 1 ( + , H ) e. dom ~~> ) $=
      ( caddc c1 cc0 co cmul vm cseq cneg cmin cli cdm 0cn ax-1cn subnegi 0p1e1
      wceq eqtri seqeq1 ax-mp cshi cfv wbr wcel cv cexp cmpt cn ovex id oveq12d
      cn0 fveq2 oveq1 oveq2d nnuz cuz nn0uz 1pneg1e0 fveq2i eqtr4i 1zzd znegcld
      uzmptshftfval wa nn0cn adantl 1cnd subnegd fveq2d oveq1d pncand mpteq2dva
      cc eqtrd seqeq3d oveq2 cbvmptv mpteq2i eqid dvradcnv eqeltrd climdm sylib
      cz 0z neg1z cvv nnex mptex eqeltri seqshft mp2an breq1i wb seqex climshft
      bitri fvex breldm sylbi syl eqeltrrid ) APGQUBZPGRQUCZUDSZUBZUEUFZXTQUKYA
      XRUKXTRQPSQRQUGUHUIUJULPGXTQUMUNAPGXSUOSZRUBZYDUEUPZUEUQZYAYBURZAYDYBURYF
      AYDPUAVFUAUSZQPSZYICUPZTSZHYHUTSZTSZVAZRUBYBAYCYNPRAYCUAVFYHXSUDSZYOCUPZT
      SZHYOQUDSZUTSZTSZVAYNAEUAEUSZUUACUPZTSZHUUAQUDSZUTSZTSZYTGQXSVFVBLUUCUUET
      VCUUAYOUKZUUCYQUUEYSTUUGUUAYOUUBYPTUUGVDUUAYOCVGVEUUGUUDYRHUTUUAYOQUDVHVI
      VEVJVFRVKUPQXSPSZVKUPVLUUHRVKVMVNVOAVPZAQUUIVQVRAUAVFYTYMAYHVFURZVSZYQYKY
      SYLTUUKYOYIYPYJTUUKYHQUUJYHWHURAYHVTWAZUUKWBZWCZUUKYOYICUUNWDVEUUKYRYHHUT
      UUKYRYIQUDSYHUUKYOYIQUDUUNWEUUKYHQUULUUMWFWIVIVEWGWIWJABCDUAFYNHIFBWHEVFU
      UBBUSZUUAUTSZTSZVAZVABWHUAVFYHCUPZUUOYHUTSZTSZVAZVAJBWHUURUVBEUAVFUUQUVAU
      UAYHUKUUBUUSUUPUUTTUUAYHCVGUUAYHUUOUTWKVEWLWMULKYNWNMNOWOWPYDWQWRYFYAYEUE
      UQZYGYFYAXSUOSZYEUEUQZUVCYDUVDYEUERWSURXSWSURZYDUVDUKWTXAPGRXSGEVBUUFVAXB
      LEVBUUFXCXDXEXFXGXHUVFYAXBURUVEUVCXIXAPGXTXJZYEYAXSXBXKXGXLYAYEUEUVGYDUEX
      MXNXOXPXQ $.
  $}

  ${
    binomcxplem.c $e |- ( ph -> C e. CC ) $.
    binomcxplem.k $e |- ( ph -> K e. NN ) $.
    $( Lemma for ~ binomcxp .  The lemma in the Wikibooks proof.  (Contributed
       by Steve Rodriguez, 22-Apr-2020.) $)
    binomcxplemwb $p |- ( ph -> ( ( ( C - K ) x. ( C _Cc K ) ) + ( ( C -
        ( K - 1 ) ) x. ( C _Cc ( K - 1 ) ) ) ) = ( C x. ( C _Cc K ) ) ) $=
      ( cfallfac co cmul cfa cfv cdiv cmin caddc c1 oveq1d wcel oveq2d 3eqtr4rd
      cc syl nncnd npcand subcld nnnn0d fallfaccl syl2anc adddird eqtr3d bccval
      cbcc cn0 faccl cc0 facne0 divassd eqtr4d mulcld divdird cn nnm1nn0 nnne0d
      wne divcan5d 1cnd fveq2d wceq facp1 mulcomd 3eqtr4d fallfacp1 oveq12d ) A
      BBCFGZHGZCIJZKGZBCLGZVLHGZCVLHGZMGZVNKGZBBCUJGZHGZVPWAHGZBCNLGZLGZBWDUJGZ
      HGZMGZAVMVSVNKAVPCMGZVLHGVMVSAWIBVLHABCDACEUAZUBOAVPCVLABCDWJUCZWJABSPZCU
      KPZVLSPDACEUDZBCUEUFZUGUHOAWBBVLVNKGZHGVOAWAWPBHABCDWNUIZQABVLVNDWOAWMVNS
      PWNWMVNCULUATZAWMVNUMVBWNCUNTZUOUPAVQVNKGZVRVNKGZMGVPWPHGZXAMGVTWHAWTXBXA
      MAVPVLVNWKWOWRWSUOOAVQVRVNAVPVLWKWOUQACVLWJWOUQWRWSURAWCXBWGXAMAWAWPVPHWQ
      QAVRCWDIJZHGZKGVLXCKGZXAWGAVLXCCWOAWDUKPZXCSPACUSPXFECUTTZXFXCWDULUATZWJA
      XFXCUMVBXGWDUNTZACEVAVCAVNXDVRKAWDNMGZIJZVNXDAXJCIACNWJAVDZUBZVEAXCXJHGZX
      CCHGXKXDAXJCXCHXMQAXFXKXNVFXGWDVGTACXCWJXHVHVIUHQAWEBWDFGZHGZXCKGWEXOXCKG
      ZHGXEWGAWEXOXCABWDDACNWJXLUCUCZAWLXFXOSPDXGBWDUEUFZXHXIUOAVLXPXCKAVLXOWEH
      GZXPABXJFGZVLXTAXJCBFXMQAWLXFYAXTVFDXGBWDVJUFUHAWEXOXRXSVHUPOAWFXQWEHABWD
      DXGUIQRRVKRR $.
  $}

  ${
    binomcxp.a $e |- ( ph -> A e. RR+ ) $.
    binomcxp.b $e |- ( ph -> B e. RR ) $.
    binomcxp.lt $e |- ( ph -> ( abs ` B ) < ( abs ` A ) ) $.
    binomcxp.c $e |- ( ph -> C e. CC ) $.
    $( TODO: how to generalize to complex summands A and B? $)
    ${
      $d j k ph $.  $d j k A $.  $d j k B $.  $d j k C $.
      $( Lemma for ~ binomcxp .  When ` C ` is a nonnegative integer, the
         binomial's finite sum value by the standard binomial theorem ~ binom
         equals this generalized infinite sum: the generalized binomial
         coefficient and exponentiation operators give exactly the same values
         in the standard index set ` ( 0 ... C ) ` , and when the index set is
         widened beyond ` C ` the additional values are just zeroes.
         (Contributed by Steve Rodriguez, 22-Apr-2020.) $)
      binomcxplemnn0 $p |- ( ( ph /\ C e. NN0 ) -> ( ( A + B ) ^c C ) = sum_
           k e. NN0 ( ( C _Cc k ) x. ( ( A ^c ( C - k ) ) x. ( B ^ k ) ) ) ) $=
        ( cn0 wcel cc0 co cmul caddc cc wceq ad2antrr c1 cr vj wa cfz cbcc cmin
        cv ccxp cexp csu cbc rpcnd recnd binom 3expia syl2anc imp adantr addcld
        simpr cxpexp elfznn0 simplr sylan2 cle wbr elfzle2 adantl nn0sub ancoms
        wi bccbc adantll mpbid oveq1d oveq12d sumeq2dv 3eqtr4d eqeltrrd addridd
        wb cxpcld cuz cfv cmpt nn0uz eqid 1nn0 a1i nn0addcld eqidd oveq2d bcccl
        nn0cnd subcld expcld mulcld fvmptd csn cxp peano2nn0 wf c0ex 0red snssd
        fconst fssd ffvelcdmda eqeltrd cseq cli cdm climrel xpeq1i seqeq3 ax-mp
        wrel cz 0z serclim0 eqbrtri releldm mp2an cabs eluznn0 sylan syldan 0zd
        nn0zd 1zzd zsubcld nn0ge0d eluzle zred 1red nn0red syl3anc elfzd mul02d
        leaddsub eqtrd bcc0 mpbird eluzelcn 0re eqeltrdi eqle breqtrrd cvgcmpce
        abs00bd isumsplit 1cnd pncand sumeq1d wss cfn ssid orci eqtrdi 3eqtr4rd
        wo sumz 3eqtrd ) ADJKZUBZLDUCMZDEUFZUDMZBDUVFUEMZUGMZCUVFUHMZNMZNMZEUIZ
        LOMZUVMJUVLEUIZBCOMZDUGMZUVDUVMUVDUVQUVMPUVDUVPDUHMZUVEDUVFUJMZBUVHUHMZ
        UVJNMZNMZEUIZUVQUVMAUVCUVRUWCQZABPKZCPKZUVCUWDVJABFUKZACGULZUWEUWFUVCUW
        DBCEDUMUNUOUPUVDUVPPKUVCUVQUVRQUVDBCAUWEUVCUWGUQAUWFUVCUWHUQURZAUVCUSZU
        VPDUTUOUVDUVEUVLUWBEUVDUVFUVEKZUBZUVGUVSUVKUWANUWKUVDUVFJKZUVGUVSQUVFDV
        AZUVDUWMUBZUVFDAUVCUWMVBUVDUWMUSZVKVCUWLUVIUVTUVJNUWLUWEUVHJKZUVIUVTQAU
        WEUVCUWKUWGRUWLUVFDVDVEZUWQUWKUWRUVDUVFLDVFVGUWKUVDUWMUWRUWQVTZUWNUVCUW
        MUWSAUWMUVCUWSUVFDVHVIVLVCVMBUVHUTUOVNVOVPVQZUVDUVPDUWIADPKZUVCIUQZWAVR
        VSUVDUVOLDSOMZSUEMZUCMZUVLEUIZUXCWBWCZUVLEUIZOMUVMUXHOMUVNUVDUVLEUAJDUA
        UFZUDMZBDUXIUEMZUGMZCUXIUHMZNMZNMZWDZLUXCUXGJWEUXGWFUVDDSUWJSJKUVDWGWHW
        IUWOUAUVFUXOUVLJUXPPUWOUXPWJUWOUXIUVFQZUBZUXJUVGUXNUVKNUXRUXIUVFDUDUWOU
        XQUSZWKUXRUXLUVIUXMUVJNUXRUXKUVHBUGUXRUXIUVFDUEUXSWKWKUXRUXIUVFCUHUXSWK
        VOVOUWPUWOUVGUVKUWODUVFAUXAUVCUWMIRZUWPWLUWOUVIUVJUWOBUVHAUWEUVCUWMUWGR
        UWODUVFUXTUWOUVFUWPWMWNWAUWOCUVFAUWFUVCUWMUWHRUWPWOWPWPZWQZUYAUVDLEJLWR
        ZWSZUXPLUXCJWEUVCUXCJKZADWTVGZUVDJTUVFUYDUVDJUYCTUYDJUYCUYDXAUVDJLXBXEW
        HUVDLTUVDXCZXDXFXGZUWOUVFUXPWCZUVLPUYBUYAXHOUYDLXIZXJXKKZUVDXJXPUYJLXJV
        EUYKXLUYJOLWBWCZUYCWSZLXIZLXJUYDUYMQUYJUYNQJUYLUYCWEXMOUYDUYMLXNXOLXQKU
        YNLXJVEXRLXSXOXTUYJLXJYAYBWHUYGUVDUVFUXGKZUBZUYIYCWCZLLUVFUYDWCZNMVDUYP
        UYQTKUYQLQUYQLVDVEUYPUYQLTUYPUYIUYPUYIUVLLUVDUYOUWMUYIUVLQUVDUYEUYOUWMU
        YFUVFUXCYDYEZUYBYFUYPUVLLUVKNMLUYPUVGLUVKNUYPUVGLQDLUVFSUEMZUCMKUYPDLUY
        TUYPYGUYPUVFSUYPUVFUYSYHUYPYIYJUVDDXQKUYOUVDDUWJYHUQZUVDLDVDVEUYOUVDDUW
        JYKUQUYPUXCUVFVDVEZDUYTVDVEZUYOVUBUVDUXCUVFYLVGUYPDTKSTKUVFTKVUBVUCVTUY
        PDVUAYMUYPYNUYPUVFUYSYODSUVFYSYPVMYQUYPDUVFAUXAUVCUYOIRZUYSUUAUUBVNUYPU
        VKUYPUVIUVJUYPBUVHAUWEUVCUYOUWGRUYPDUVFVUDUYOUVFPKUVDUXCUVFUUCVGWNWAUYP
        CUVFAUWFUVCUYOUWHRUYSWOWPYRYTZYTUUIZUUDUUEVUFUYQLUUFUOUYPUYRUVDUYOUWMUY
        RPKUYSUWOUYRUYHULYFYRUUGUUHUUJUVDUXFUVMUXHOUVDUXEUVEUVLEUVDUXDDLUCUVDDS
        UXBUVDUUKUULWKUUMVNUVDUXHLUVMOUVDUXHUXGLEUIZLUVDUXGUVLLEVUEVPUXGUXGUUNZ
        UXGUUOKZUUTVUGLQVUHVUIUXGUUPUUQUXGEUXCUVAXOUURWKUVBUWTUUS $.
    $}

    ${
      $d k x ph $.  $d k x C $.
      $( Lemma for ~ binomcxp .  As ` k ` increases, this ratio's absolute
         value converges to one.  Part of equation "Since continuity of the
         absolute value..." in the Wikibooks proof (proven for the inverse
         ratio, which we later show is no problem).  (Contributed by Steve
         Rodriguez, 22-Apr-2020.) $)
      binomcxplemrat $p |- ( ph -> ( k e. NN0 |->
          ( abs ` ( ( C - k ) / ( k + 1 ) ) ) ) ~~> 1 ) $=
        ( cn0 cmin co c1 cdiv cabs cfv cc0 cvv cc wcel vx caddc cmpt cneg nn0uz
        cv cli cof 0zd peano2cn syl 1zzd nn0ex mptex wa eqidd wceq simpr oveq1d
        a1i oveq2d ovexd fvmptd divcnvshft wbr csn cxp nn0cn 1cnd addcld nnne0d
        nn0p1nn dividd mpteq2ia fconstmpt eqtr4i ax-1cn cuz eqimss2i climconst2
        cz 0z mp2an eqbrtri adantr nn0cnd wne adantl divcld eqeltrd oveq12d wfn
        ovex eqid fnmpti inidm ofval climsub offval2 divsubdird pnpcan2d eqtr3d
        mpteq2dva eqtrd df-neg eqcomi 3brtr3d oveq2 oveq1 subcld fveq2d climabs
        fvexd eqtr4d absnegi abs1 eqtri breqtrdi ) AEJDEUFZKLZXSMUBLZNLZOPZUCZM
        UDZOPZMUGAYEUAEJYBUCZYDQRJUEAEJDMUBLZYANLZUCZEJYAYANLZUCZKUHZLZQMKLZYGY
        EUGAQMUAYJYLYNQRJUEAUIZAYHMUAYJQRJUEYPADSTZYHSTZIDUJUKZAULYJRTAEJYIUMUN
        UTAUAUFZJTZUOZEYTYIYHYTMUBLZNLZJYJRUUBYJUPUUBXSYTUQZUOZYAUUCYHNUUFXSYTM
        UBUUBUUEURUSZVAAUUAURZUUBYHUUCNVBVCZVDAYJYLYMVBYLMUGVEAYLJMVFVGZMUGYLEJ
        MUCUUJEJYKMXSJTZYAUUKXSMXSVHZUUKVIVJZUUKYAXSVLVKZVMVNEJMVOVPMSTQWATUUJM
        UGVEVQWBMQJJQVRPUEVSUMVTWCWDUTUUBYTYJPZUUDSUUIUUBYHUUCUUBDMAYQUUAIWEZUU
        BVIZVJUUBYTMUUBYTUUHWFZUUQVJZUUAUUCQWGAUUAUUCYTVLVKWHZWIWJUUBYTYLPZUUCU
        UCNLZSUUBEYTYKUVBJYLRUUBYLUPUUFYAUUCYAUUCNUUGUUGWKUUHUUBUUCUUCNVBVCUUBU
        UCUUCUUSUUSUUTWIWJAJJUUOUVAKJYJYLRRYTYJJWLAEJYIYJYHYANWMYJWNWOUTYLJWLAE
        JYKYLYAYANWMYLWNWOUTJRTAUMUTZUVCJWPUUBUUOUPUUBUVAUPWQWRAYNEJYIYKKLZUCYG
        AEJYIYKKYJYLRRRUVCAUUKUOZYHYANVBUVEYAYANVBAYJUPAYLUPWSAEJUVDYBUVEYHYAKL
        ZYANLUVDYBUVEYHYAYAAYRUUKYSWEUUKYASTAUUMWHZUVGUUKYAQWGAUUNWHWTUVEUVFXTY
        ANUVEDXSMAYQUUKIWEUUKXSSTAUULWHUVEVIXAUSXBXCXDYOYEUQAYEYOMXEXFUTXGYDRTA
        EJYCUMUNUTYPUUBYTYGPZDYTKLZUUCNLZSUUBEYTYBUVJJYGRUUBYGUPUUEYBUVJUQUUBUU
        EXTUVIYAUUCNXSYTDKXHXSYTMUBXIWKZWHUUHUUBUVIUUCNVBVCZUUBUVIUUCUUBDYTUUPU
        URXJUUSUUTWIWJUUBYTYDPUVJOPZUVHOPUUBEYTYCUVMJYDRUUBYDUPUUEYCUVMUQUUBUUE
        YBUVJOUVKXKWHUUHUUBUVJOXMVCUUBUVHUVJOUVLXKXNXLYFMOPMMVQXOXPXQXR $.
    $}

    ${
      binomcxplem.f $e |- F = ( j e. NN0 |-> ( C _Cc j ) ) $.
      ${
        $d j k ph $.  $d j k C $.
        $( Lemma for ~ binomcxp . ~ binomcxplemrat implies that when ` C ` is
           not a nonnegative integer, the absolute value of the ratio
           ` ( ( F `` ( k + 1 ) ) / ( F `` k ) ) ` converges to one.  The rest
           of equation "Since continuity of the absolute value..." in the
           Wikibooks proof.  (Contributed by Steve Rodriguez, 22-Apr-2020.) $)
        binomcxplemfrat $p |- ( ( ph /\ -. C e. NN0 ) -> ( k e. NN0 |->
            ( abs ` ( ( F ` ( k + 1 ) ) / ( F ` k ) ) ) ) ~~> 1 ) $=
          ( cn0 wcel wa c1 co wceq cbcc cc0 wn cv caddc cfv cdiv cabs cmpt cmin
          cli cmul cc adantr simpr bccp1k cvv a1i oveq2d nn0addcld ovexd fvmptd
          1nn0 oveq1d 3eqtr4d adantlr eqcomd bcccl eqeltrd nn0cnd subcld addcld
          1cnd wne nn0p1nn nnne0d adantl divcld cfz elfznn0 con3i ad2antlr bcc0
          mulcld necon3abid mpbird eqnetrd divmuld mpteq2dva wbr binomcxplemrat
          fveq2d eqbrtrd ) ADMNZUAZOZFMFUBZPUCQZGUDZWOGUDZUEQZUFUDZUGFMDWOUHQZW
          PUEQZUFUDZUGZPUIWNFMWTXCWNWOMNZOZWSXBUFXFWSXBRWRXBUJQZWQRXFWQXGAXEWQX
          GRWMAXEOZDWPSQZDWOSQZXBUJQWQXGXHDWOADUKNZXEKULZAXEUMZUNXHEWPDEUBZSQZX
          IMGUOGEMXOUGRXHLUPZXHXNWPRZOXNWPDSXHXQUMUQXHWOPXMPMNXHVAUPURXHDWPSUSU
          TXHWRXJXBUJXHEWOXOXJMGUOXPXHXNWORZOXNWODSXHXRUMUQXMXHDWOSUSUTZVBVCVDZ
          VEXFWQWRXBXFWQXGUKXTXFWRXBAXEWRUKNWMXHWRXJUKXSXHDWOXLXMVFVGVDZXFXAWPX
          FDWOAXEXKWMXLVDZXFWOWNXEUMZVHZVIXFWOPYDXFVKVJXEWPTVLWNXEWPWOVMVNVOVPZ
          WBVGYAYEXFWRXJTAXEWRXJRWMXSVDXFXJTVLDTWOPUHQZVQQNZUAZWMYHAXEYGWLDYFVR
          VSVTXFYGXJTXFDWOYBYCWAWCWDWEWFWDWJWGAXDPUIWHWMABCDFHIJKWIULWK $.
      $}

      binomcxplem.s $e |- S = ( b e. CC |-> ( k e. NN0 |-> ( ( F ` k ) x.
          ( b ^ k ) ) ) ) $.
      binomcxplem.r $e |- R = sup ( { r e. RR | seq 0 ( + , ( S ` r ) )
          e. dom ~~> } , RR* , < ) $.
      ${
        $d i k x y C $.  $d b k x y F $.  $d i k x y F $.  $d i j k ph $.
        $d i j k C $.  $d i r x S $.  $d i x y S $.  $d x y ph $.
        $( Lemma for ~ binomcxp .  By ~ binomcxplemfrat and ~ radcnvrat the
           radius of convergence of power series
           ` sum_ k e. NN0 ( ( F `` k ) x. ( b ^ k ) ) ` is one.  (Contributed
           by Steve Rodriguez, 22-Apr-2020.) $)
        binomcxplemradcnv $p |- ( ( ph /\ -. C e. NN0 ) -> R = 1 ) $=
          ( cn0 co vx vi vy wcel wn wa c1 cdiv cv caddc cfv cabs cmpt cexp cmul
          cc0 cc wceq simpl oveq1d oveq2d mpteq2dva fveq2 oveq2 oveq12d cbvmptv
          eqtrdi eqtri cbcc ad2antrr simpr bcccl fmptd fvoveq1 fveq2d nn0uz a1i
          0nn0 cvv ovexd fvmptd wne cmin cfz elfznn0 con3i ad2antlr adantr bcc0
          wb necon3abid adantlr mpbird eqnetrd binomcxplemfrat ax-1ne0 1div1e1
          radcnvrat ) ADSUDZUEZUFZEUGUGUHTUGXAUAIHSHUIZUGUJTIUKZXBIUKZUHTZULUKZ
          UMEUBUCFUGUPSJFKUQHSXDKUIZXBUNTZUOTZUMZUMUAUQUCSUCUIZIUKZUAUIZXKUNTZU
          OTZUMZUMQKUAUQXJXPXGXMURZXJHSXDXMXBUNTZUOTZUMXPXQHSXIXSXQXBSUDZUFZXHX
          RXDUOYAXGXMXBUNXQXTUSUTVAVBHUCSXSXOXBXKURXDXLXRXNUOXBXKIVCXBXKXMUNVDV
          EVFVGVFVHXAGSDGUIZVITZUQIXAYBSUDZUFDYBADUQUDZWTYDOVJXAYDVKVLPVMRHUBSX
          FUBUIZUGUJTIUKZYFIUKZUHTZULUKXBYFURZXEYIULYJXCYGXDYHUHXBYFUGIUJVNXBYF
          IVCVEVOVFVPUPSUDXAVRVQXAYFSUDZUFZYHDYFVITZUPYLGYFYCYMSIVSIGSYCUMURYLP
          VQYLYBYFURZUFYBYFDVIYLYNVKVAXAYKVKYLDYFVIVTWAYLYMUPWBZDUPYFUGWCTZWDTU
          DZUEZWTYRAYKYQWSDYPWEWFWGAYKYOYRWJWTAYKUFZYQYMUPYSDYFAYEYKOWHAYKVKWIW
          KWLWMWNABCDGHILMNOPWOUGUPWBXAWPVQWRWQVG $.
      $}

      binomcxplem.e $e |- E = ( b e. CC |-> ( k e. NN |->
          ( ( k x. ( F ` k ) ) x. ( b ^ ( k - 1 ) ) ) ) ) $.
      binomcxplem.d $e |- D = ( `' abs " ( 0 [,) R ) ) $.
      ${
        $d j k ph $.  $d x y ph $.  $d b k C $.  $d j k C $.  $d x y C $.
        $d x y D $.  $d b k F $.  $d x ph $.  $d r S $.  $d b r $.  $d b y $.
        $( Lemma for ~ binomcxp .  By the power and chain rules, calculate the
           derivative of ` ( ( 1 + b ) ^c -u C ) ` , with respect to ` b ` in
           the disk of convergence ` D ` .  We later multiply the derivative in
           the later ~ binomcxplemdvsum by this derivative to show that
           ` ( ( 1 + b ) ^c C ) ` (with a nonnegated ` C ` ) and the later sum,
           since both at ` b = 0 ` equal one, are the same.  (Contributed by
           Steve Rodriguez, 22-Apr-2020.) $)
        binomcxplemdvbinom $p |- ( ( ph /\ -. C e. NN0 ) ->
            ( CC _D ( b e. D |-> ( ( 1 + b ) ^c -u C ) ) ) =
            ( b e. D |-> ( -u C x. ( ( 1 + b ) ^c ( -u C - 1 ) ) ) ) ) $=
          ( vy vx cn0 wcel wn wa cc c1 cv caddc co cneg ccxp cmpt cdv cmin cmul
          cabs ccnv cc0 cico cima nfcv cfv cseq cli cdm cr crab cxr csup nfmpt1
          clt cexp nfcxfr nffv nfseq nfel1 nfrabw nfsup nfov nfima oveq2 oveq1d
          wceq cbvmptf oveq2i cvv cmnf cioc cdif cpr cnelprrecn a1i crp wi 1cnd
          wss cnvimass eqsstri absf fdmi sseqtri sselda addcld simpr wbr adantr
          pncan2d 1red resubcld eqeltrrd 1pneg1e0 renegcld cle w3a wfn elpreima
          wf ffn mp2b simprbi eleq2s 0re ssrab2 ax-mp eqeltri mp2an adantl eqid
          wb negcld cxpcld ccnfld ctopn cbvmptv oveq1 oveq2d ressxr sstri sylib
          supxrcl elico2 simp3d binomcxplemradcnv breqtrd absltd mpbid ltadd2dd
          simpld eqbrtrrid syldan elrpd ex ellogdm sylanbrc eldifi ovexd dvmptc
          c0ex dvmptid dvmptadd 0p1e1 mpteq2i crest fvex ctps cnfldtps cnfldbas
          eqtrdi cuni tpsuni restid eqcomi ctop cnfldtop ccom cnbl0 eqtri cxmet
          cnt cbl cnxmet cnfldtopn blopn mp3an isopn3i dvmptres2 eqidd dvcncxp1
          0cn 3eqtr3g syl dvmptco subcld mulcld mulridd mpteq2dva 3eqtrd eqtrid
          ) ADUEUFUGZUHZUIMEUJMUKZULUMZDUNZUOUMZUPZUQUMUIUCEUJUCUKZULUMZUXGUOUM
          ZUPZUQUMZMEUXGUXFUXGUJURUMZUOUMZUSUMZUPZUXIUXMUIUQMUCEUXHUXLMEUTVAZVB
          FVCUMZVDZUBMUXSUXTMUXSVEMVBFVCMVBVEZMVCVEMFULLUKZGVFZVBVGZVHVIZUFZLVJ
          VKZVLVOVMZTMUYHVLVOUYGMLVJMUYEUYFMULUYDVBUYBMULVEMUYCGMGMUIIUEIUKZKVF
          UXEUYJVPUMUSUMUPZUPSMUIUYKVNVQMUYCVEVRVSVTMVJVEWAMVLVEMVOVEWBVQWCWDVQ
          ZUCEVEZUCUXHVEMUXLVEUXEUXJWGUXFUXKUXGUOUXEUXJUJULWEWFWHWIUXDUXNUCEUXG
          UXKUXOUOUMZUSUMZUJUSUMZUPUCEUYOUPZUXRUXDUCUDUXKUJUDUKZUXGUOUMZUXGUYRU
          XOUOUMZUSUMZUIUIUXLUYOUIWJEUIWKVBWLUMZWMZUIVJUIWNUFUXDWOWPZVUDUXDUXJE
          UFZUHZUXKUIUFUXKVJUFZUXKWQUFZWRUXKVUCUFVUFUJUXJVUFWSZUXDEUIUXJEUIWTUX
          DEUTVIZUIEUYAVUJUBUTUXTXAXBUIVJUTXCXDXEWPZXFZXGZVUFVUGVUHVUFVUGUHZUXK
          VUFVUGXHZVUFVUGUXJVJUFZVBUXKVOXIVUNUXKUJURUMUXJVJVUNUJUXJVUNWSVUFUXJU
          IUFZVUGVULXJXKVUNUXKUJVUOVUNXLXMXNVUFVUPUHZVBUJUJUNZULUMUXKVOXOVURVUS
          UXJUJVURUJVURXLZXPVUFVUPXHZVUTVURVUSUXJVOXIZUXJUJVOXIZVURUXJUTVFZUJVO
          XIZVVBVVCUHVUFVVEVUPVUFVVDFUJVOVUEVVDFVOXIZUXDVUEVVDVJUFZVBVVDXQXIZVV
          FVUEVVDUXTUFZVVGVVHVVFXRZVVIUXJUYAEUXJUYAUFZVUQVVIUIVJUTYAUTUIXSVVKVU
          QVVIUHYMXCUIVJUTYBUIUXJUXTUTXTYCYDUBYEVBVJUFFVLUFZVVIVVJYMYFFUYIVLTUY
          HVLWTUYIVLUFUYHVJVLUYGLVJYGUUAUUBUYHUUDYHYIZVBFVVDUUEYJUUCUUFYKUXDFUJ
          WGVUEABCDFGHIKLMNOPQRSTUUGXJUUHXJVURUXJUJVVAVUTUUIUUJUULUUKUUMUUNUUOU
          UPUXKVUCVUCYLZUUQUURVUIUXDUYRVUCUFZUHZUYRUXGVVOUYRUIUFZUXDUYRUIVUBUUS
          YKUXDUXGUIUFZVVOUXDDADUIUFZUXCQXJZYNZXJYOVVPUXGUYTUSUUTUXDUIUDEUJUYRU
          LUMZUPZUQUMUDEUJUPUIUCEUXKUPZUQUMUCEUJUPUXDUDVWBUJUIYPYQVFZVWEUIUIEEV
          UDUXDVVQUHZUJUYRVWFWSZUXDVVQXHZXGVWGUXDUIUDUIVWBUPUQUMUDUIVBUJULUMZUP
          UDUIUJUPUXDUDUJVBUYRUJUIWJUIUIVUDVWGVBWJUFVWFUVBWPUXDUDUJUIVUDUXDWSUV
          AVWHVWGUXDUDUIVUDUVCUVDUDUIVWIUJUVEUVFUVLVUKVWEUIUVGUMZVWEVWEWJUFVWJV
          WEWGYPYQUVHVWEWJUIYPUVIUFUIVWEUVMWGUVJUIVWEYPUVKVWEYLZUVNYHUVOYHUVPVW
          KEVWEUWCVFVFEWGZUXDVWEUVQUFEVWEUFVWLVWEVWKUVREVBFUTURUVSZUWDVFUMZVWEE
          UYAVWNUBVVLUYAVWNWGVVMVWMFVWMYLUVTYHUWAVWMUIUWBVFUFVBUIUFVVLVWNVWEUFU
          WEUWMVVMVWMVBFVWEUIVWEVWKUWFUWGUWHYIEVWEUWIYJWPUWJVWCVWDUIUQUDUCEVWBU
          XKUYRUXJUJULWEYRWIUDUCEUJUJUYRUXJWGUJUWKYRUWNUXDVVRUIUDVUCUYSUPUQUMUD
          VUCVUAUPWGVWAUDUXGVUCVVNUWLUWOUYRUXKUXGUOYSUYRUXKWGUYTUYNUXGUSUYRUXKU
          XOUOYSYTUWPUXDUCEUYPUYOVUFUYOVUFUXGUYNVUFDUXDVVSVUEVVTXJYNZVUFUXKUXOV
          UMVUFUXGUJVWOVUIUWQYOUWRUWSUWTUYQUXRWGUXDUCMEUYOUXQUYMUYLMUYOVEUCUXQV
          EUXJUXEWGZUYNUXPUXGUSVWPUXKUXFUXOUOUXJUXEUJULWEWFYTWHWPUXAUXB $.
      $}

      ${
        $d b k ph $.  $d b k F $.  $d b k J $.  $d b r J $.  $d j ph $.
        $d r S $.
        $( Lemma for ~ binomcxp .  The sum in ~ binomcxplemnn0 and its
           derivative (see the next theorem, ~ binomcxplemdvsum ) converge, as
           long as their base ` J ` is within the disk of convergence.  Part of
           remark "This convergence allows us to apply term-by-term
           differentiation..." in the Wikibooks proof.  (Contributed by Steve
           Rodriguez, 22-Apr-2020.) $)
        binomcxplemcvg $p |- ( ( ph /\ J e. D ) ->
            ( seq 0 ( + , ( S ` J ) ) e. dom ~~> /\
              seq 1 ( + , ( E ` J ) ) e. dom ~~> ) ) $=
          ( wcel wa caddc cfv cc0 cseq cli cdm c1 cc wf cv cbcc co adantr simpr
          cn0 bcccl fmptd cabs cico ccnv cima eleq2i wfn absf ffn elpreima mp2b
          cr bitri simplbi adantl clt wbr simprbi cle cxr w3a 0re crab csup wss
          wb ssrab2 ressxr sstri supxrcl ax-mp eqeltri elico2 mp2an simp3bi syl
          radcnvlt2 cn cmul cmin cexp cmpt wceq cvv a1i simplr oveq1d mpteq2dva
          oveq2d nnex mptex fvmptd sylan2 seqeq3d eqid dvradcnv2 eqeltrd jca )
          ALEUDZUEZUFLGUGUHUIUJUKZUDUFLJUGZULUIZYBUDYANKFIGLMTAUTUMKUNXTAHUTDHU
          OZUPUQUMKAYEUTUDZUEDYEADUMUDYFRURAYFUSVASVBURZUAXTLUMUDZAXTYHLVCUGZUH
          FVDUQZUDZXTLVCVEYJVFZUDZYHYKUEZEYLLUCVGUMVMVCUNVCUMVHYMYNWGVIUMVMVCVJ
          UMLYJVCVKVLVNZVOZVPZXTYIFVQVRZAXTYKYRXTYHYKYOVSYKYIVMUDZUHYIVTVRZYRUH
          VMUDFWAUDYKYSYTYRWBWGWCFUFMUOGUGUHUIYBUDZMVMWDZWAVQWEZWAUAUUBWAWFUUCW
          AUDUUBVMWAUUAMVMWHWIWJUUBWKWLWMUHFYIWNWOWPWQVPZWRYAYDUFIWSIUOZUUEKUGW
          TUQZLUUEULXAUQZXBUQZWTUQZXCZULUIYBYAYCUUJUFULXTAYHYCUUJXDYPAYHUEZNLIW
          SUUFNUOZUUGXBUQZWTUQZXCZUUJUMJXEJNUMUUOXCXDUUKUBXFUUKUULLXDZUEZIWSUUN
          UUIUUQUUEWSUDZUEZUUMUUHUUFWTUUSUULLUUGXBUUKUUPUURXGXHXJXIAYHUSUUJXEUD
          UUKIWSUUIXKXLXFXMXNXOYANKFIGUUJLMTUAUUJXPYGYQUUDXQXRXS $.
      $}

      binomcxplem.p $e |- P = ( b e. D |-> sum_ k e. NN0 ( ( S ` b ) ` k ) ) $.
      ${
        $d b k m n x y z F $.  $d b k m n x y ph $.  $d b k m n w y F $.
        $d m n x y D $.  $d b k r z F $.  $d m n y z S $.  $d j k ph $.
        $d n y E $.  $d j C $.  $d x P $.
        $( Lemma for ~ binomcxp .  The derivative of the generalized sum in
           ~ binomcxplemnn0 .  Part of remark "This convergence allows to apply
           term-by-term differentiation..." in the Wikibooks proof.
           (Contributed by Steve Rodriguez, 22-Apr-2020.) $)
        binomcxplemdvsum $p |- ( ph -> ( CC _D P ) =
            ( b e. D |-> sum_ k e. NN ( ( E ` b ) ` k ) ) ) $=
          ( vy vn vx vz vw vm cc cdv co cn cfv csu cmpt cmul cmin cexp cc0 cabs
          cv c1 caddc cn0 cseq cli cdm wcel crab cxr clt csup cdiv cif ccom cbl
          cr c2 ccnv cico cima nfcv nfmpt1 nfcxfr nffv nfseq nfel1 nfrabw nfsup
          nfov nfima nfsum wceq simpl fveq2d fveq1d sumeq2dv fveq2 nfmpt cbvsum
          wa eqtrdi cbvmptf eqtri cbcc cvv ovexd a1i simpr oveq2d adantr fvmptd
          bcccl eqeltrd fmpt2d nfv seqeq3d eleq1d cbvrabw supeq1i fveq1i seqeq3
          ax-mp eleq1i rabbii 3eqtrri oveq2i oveq1i eqid oveq1 mpteq2dv cbvmptv
          ifbieq12i pserdv2 cnvimass oveq1d mpteq2dva oveq12d eqsstri absf fdmi
          sseqtri sseli simplr nnex mptex sylan2 eqtr4d ) AUKFULUMZUEEUNUFVCZUE
          VCZKUOZUOZUFUPZUQZNEUNJVCZNVCZKUOZUOZJUPZUQAUUKUEEUNUULUULLUOZURUMZUU
          MUULVDUSUMZUTUMZURUMZUFUPZUQUUQANUELVAUGVCVBUOZVEUHVCZUIUKJVFUURLUOZU
          IVCZUURUTUMZURUMZUQZUQZUOZVAVGZVHVIZVJZUHVSVKZVLVMVNZVSVJZUVIUWBVEUMZ
          VTVOUMZUVIVDVEUMZVPZVEUMZVTVOUMZVBUSVQVRUOZUMGEUJUFJFHVEUVJNUKJVFUVKU
          USUURUTUMZURUMZUQZUQZUOZVAVGZUVSVJZUHVSVKZVLVMVNZVSVJZUVIUWSVEUMZVTVO
          UMZUWFVPZUHUGTFNEVFUURUUSHUOZUOZJUPZUQUEEVFUJVCZUUMHUOZUOZUJUPZUQUDNU
          EEUXFUXJNEVBWAZVAGWBUMZWCZUCNUXKUXLNUXKWDNVAGWBNVAWDZNWBWDNGVEMVCZHUO
          ZVAVGZUVSVJZMVSVKZVLVMVNZUANUXSVLVMUXRNMVSNUXQUVSNVEUXPVAUXNNVEWDNUXO
          HNHUWNTNUKUWMWEWFZNUXOWDWGWHWINVSWDWJNVLWDNVMWDWKWFWLWMWFZUEEWDZUEUXF
          WDNVFUXIUJNVFWDNUXGUXHNUUMHUYANUUMWDZWGNUXGWDWGWNUUSUUMWOZUXFVFUURUXH
          UOZJUPUXJUYEVFUXEUYFJUYEUURVFVJZXCZUURUXDUXHUYHUUSUUMHUYEUYGWPWQWRWSV
          FUYFUXIJUJUURUXGUXHWTUJUYFWDJUXGUXHJUUMHJHUWNTJNUKUWMJUKWDZJVFUWLWEXA
          WFJUUMWDWGJUXGWDWGXBXDXEXFAIJVFDIVCZXGUMZUKLXHAUYJVFVJXCDUYJXGXILIVFU
          YKUQWOZASXJAUYGXCZUVKDUURXGUMZUKUYMIUURUYKUYNVFLUKUYLUYMSXJUYMUYJUURW
          OZXCUYJUURDXGUYMUYOXKXLAUYGXKZUYMDUURADUKVJUYGRXMUYPXOZXNUYQXPXQGUXTV
          EUVJHUOZVAVGZUVSVJZUHVSVKZVLVMVNZUAVLUXSVUAVMUXRUYTMUHVSMVSWDUHVSWDUX
          RUHXRMUYSUVSMVEUYRVAMVAWDMVEWDMUVJHMHUWNTMUWNWDWFMUVJWDWGWHWIUXOUVJWO
          ZUXQUYSUVSVUCUXPUYRVEVAUXOUVJHWTXSXTYAYBZXFUCUWTGVSVJUXBUWFUVIGVEUMZV
          TVOUMUWFUWSGVSGUXTVUBUWSUAVUDVLVUAUWRVMUYTUWQUHVSUYSUWPUVSUYRUWOWOUYS
          UWPWOUVJHUWNTYCVEUYRUWOVAYDYEYFYGYBYHZYFUXAVUEVTVOUWSGUVIVEVUFYIYJUWF
          YKZYOUWIUVIUXCVEUMZVTVOUMVAUWJUWHVUHVTVOUWGUXCUVIVEUWCUWTUWEUWFUXBUWF
          UWBUWSVSVLUWAUWRVMUVTUWQUHVSUVRUWPUVSUVQUWOWOUVRUWPWOUVJUVPUWNUINUKUV
          OUWMUVLUUSWOZJVFUVNUWLVUIUVMUWKUVKURUVLUUSUURUTYLXLYMYNYCVEUVQUWOVAYD
          YEYFYGYBZYFUWDUXAVTVOUWBUWSUVIVEVUJYIYJVUGYOYIYJYIYPAUEEUUPUVHUUMEVJA
          UUMUKVJZUUPUVHWOEUKUUMEVBVIZUKEUXMVULUCVBUXLYQUUAUKVSVBUUBUUCUUDUUEAV
          UKXCZUNUUOUVGUFVUMUULUNVJZXCZJUULUURUVKURUMZUUMUURVDUSUMZUTUMZURUMZUV
          GUNUUNXHVUMUUNJUNVUSUQZWOVUNVUMNUUMJUNVUPUUSVUQUTUMZURUMZUQZVUTUKKXHK
          NUKVVCUQZWOVUMUBXJVUMUYEXCZJUNVVBVUSVVEUURUNVJZXCZVVAVURVUPURVVGUUSUU
          MVUQUTVUMUYEVVFUUFYRXLYSAVUKXKVUTXHVJVUMJUNVUSUUGUUHXJXNXMVUOUURUULWO
          ZXCZVUPUVDVURUVFURVVIUURUULUVKUVCURVUOVVHXKZVVIUURUULLVVJWQYTVVIVUQUV
          EUUMUTVVIUURUULVDUSVVJYRXLYTVUMVUNXKVUOUVDUVFURXIXNWSUUIYSUUJUENEUUPU
          VBUYCUYBNUNUUOUFNUNWDNUULUUNNUUMKNKVVDUBNUKVVCWEWFUYDWGNUULWDWGWNUEUV
          BWDUUMUUSWOZUUPUNUULUUTUOZUFUPUVBVVKUNUUOVVLUFVVKVUNXCZUULUUNUUTVVMUU
          MUUSKVVKVUNWPWQWRWSUNVVLUVAUFJUULUURUUTWTJUULUUTJUUSKJKVVDUBJNUKVVCUY
          IJUNVVBWEXAWFJUUSWDWGJUULWDWGUFUVAWDXBXDXEXD $.
      $}

      ${
        $d b k r x A $.  $d b k r x B $.  $d b j k ph $.  $d b j k C $.
        $d b k x C $.  $d b x y C $.  $d b k r F $.  $d k r x S $.
        $d x y ph $.  $d j k D $.  $d k x D $.  $d x y D $.  $d j k E $.
        $d k x E $.  $d x y P $.
        $( Lemma for ~ binomcxp .  When ` C ` is not a nonnegative integer, the
           generalized sum in ~ binomcxplemnn0 &mdash;which we will call ` P `
           &mdash;is a convergent power series: its base ` b ` is always of
           smaller absolute value than the radius of convergence.

           ~ pserdv2 gives the derivative of ` P ` , which by ~ dvradcnv also
           converges in that radius.  When ` A ` is fixed at one, ` ( A + b ) `
           times that derivative equals ` ( C x. P ) ` and fraction
           ` ( P / ( ( A + b ) ^c C ) ) ` is always defined with derivative
           zero, so the fraction is a constant&mdash;specifically one, because
           ` ( ( 1 + 0 ) ^c C ) = 1 ` .  Thus
           ` ( ( 1 + b ) ^c C ) = ( P `` b ) ` .

           Finally, let ` b ` be ` ( B / A ) ` , and multiply both the binomial
           ` ( ( 1 + ( B / A ) ) ^c C ) ` and the sum ` ( P `` ( B / A ) ) ` by
           ` ( A ^c C ) ` to get the result.  (Contributed by Steve Rodriguez,
           22-Apr-2020.) $)
        binomcxplemnotnn0 $p |- ( ( ph /\ -. C e. NN0 ) ->
            ( ( A + B ) ^c C ) = sum_ k e. NN0 ( ( C _Cc k ) x.
              ( ( A ^c ( C - k ) ) x. ( B ^ k ) ) ) ) $=
          ( vx cn0 wcel wa c1 cdiv co caddc ccxp cmul cv cbcc cexp csu cmin cfv
          cvv cmpt wceq cabs cc0 nfcv cseq cli cr cxr clt cc nfcxfr nffv fveq2d
          nfel1 fveq1d sumeq2dv cbvmptf eqtri a1i simplr recnd adantr wne mpbid
          abscld wbr cle wb wss ax-mp mp2an wf absf sumex fvmptd cneg adantl wi
          nfv nfim eleq1d imbi12d nn0uz eqidd mptex fvmpt2d ovexd oveq2d oveq1d
          simpr adantlr eqtrd ad2antrr bcccl expcld mulcld eqeltrd fveq2 isumcl
          adantllr 1cnd negcld cxpcld cdv eqtrdi fmpt3d subcld nnuz sylan2 cshi
          cn 3eqtr3d 3eqtrd mpteq2dva oveq12d cuz eqtr4d offval2f ccnv cico cdm
          vy wn cima crab csup nfmpt1 nfseq nfrabw nfsup nfov nfima nfsum simpl
          rpcnd 0red absge0d lelttrd gt0ne0d abs00ad necon3bid mulridd breqtrrd
          divcld 1red elrpd ltdivmuld absdivd binomcxplemradcnv 3brtr4d w3a 0re
          mpbird ssrab2 ressxr supxrcl eqeltri elico2 syl3anbrc eleq2i elpreima
          sstri wfn ffn mp2b bitri sylanbrc cof ccom cbl eqid cnbl0 mulcl nfcri
          0cnd nfan eleq1 0zd cnvimass eqsstri fdmi sseqtri sseli nn0ex sylanl2
          anbi2d ad2antlr seqeq3d anbi12d binomcxplemcvg chvarvv simpld chvarfv
          fmptd addcld oveq2 cnex fex cnvex imaexg inidm off csn cxp 1ex fconst
          fconstmpt feq1i mpbi ax-1cn snssi fss cpr cnelprrecn binomcxplemdvsum
          fdmd binomcxplemdvbinom dvmulf 1zzd ad3antrrr 1nn0 iserex adddid nnex
          feqmptd nnm1nn0 bccp1k nn0cnd npcand divassd divcan2d 3eqtr2d mulcomd
          nnnn0 nnne0 ovex 1pneg1e0 fveq2i eqtr4i znegcld uzmptshftfval cbvmptv
          oveq1 subnegd pncand nncn mul12d expp1d eqtr3id climrel simprd climdm
          nn0cn wrel sylib cz 0z neg1z fvex seqshft subnegi 0p1e1 seqeq1 oveq1i
          0cn breq1i climshft releldm sylancr isermulc2 isumadd adddird mullidd
          seqex sylibr isumshft cbvsumv pncan2d isum1p 0nn0 subid1d bccn0 exp0d
          eqcomi sumeq1i eqeltrrd addassd 3eqtr4rd binomcxplemwb mulassd eqtrid
          isummulc2 3eqtrrd simprbi eleq2s simp3bi syl absnegd eqcomd abssubne0
          3brtr3d mp3an2 syl2anc eqnetrrd divmuld div23d eqtr3d 3eqtr4d cxpsubd
          1re mul32d div32d cxp1d eqtr2d mulneg1d negidd c0ex snid ccnfld ctopn
          eqtr4di dvconst oveq2i 3eqtr3i crest ctps cuni cnfldtps tpsuni restid
          cnfldbas cnt ctop cnfldtop cxmet cnxmet cnfldtopn blopn mp3an isopn3i
          dvmptres2 3eqtr3g crp eqeltrdi blcntr mp3an12 eleqtrrdi anbi1d vtoclf
          1rp nfel2 syldanl syldan 1t1e1 0expd mul01d cfn wo eqimssi orci 1p0e1
          sumz 1cxpd ffnd ofval mpdan fveq1i dv11cn cdif neeq1d cxpne0d eldifsn
          fvconst2 ofdivcan4 syl3anc cxpnegd negnegd rerpdivcld readdcld df-neg
          rpne0d absrpcld div1d eqbrtrd ltdiv23d ltled renegcld eqbrtrrid rpred
          absled lesubaddd rpge0d mulcxpd divcan1d divrecd reccld mulexpd nn0zd
          isummulc1 exprecd cxpexp ) ADUFUGUUEZUHZUICBUJUKZULUKZDUMUKZBDUMUKZUN
          UKZUFDJUOZUPUKZWYFWYKUQUKZUNUKZJURZWYIUNUKZBCULUKZDUMUKZUFWYLBDWYKUSU
          KZUMUKZCWYKUQUKZUNUKUNUKZJURZWYEWYHWYOWYIUNWYEWYFFUTUFWYKWYFHUTZUTZJU
          RZWYHWYOWYEUEWYFUFWYKUEUOZHUTZUTZJURZXUFEFVAFUEEXUJVBZVCZWYEFNEUFWYKN
          UOZHUTZUTZJURZVBZXUKUDNUEEXUPXUJNEVDUUAZVEGUUBUKZUUFZUCNXURXUSNXURVFN
          VEGUUBNVEVFZNUUBVFNGULMUOZHUTZVEVGZVHUUCZUGZMVIUUGZVJVKUUHZUANXVGVJVK
          XVFNMVINXVDXVENULXVCVEXVANULVFZNXVBHNHNVLJUFWYKLUTZXUMWYKUQUKZUNUKZVB
          ZVBZTNVLXVMUUIVMZNXVBVFVNUUJVPNVIVFUUKNVJVFNVKVFUULVMUUMUUNVMZUEEVFZU
          EXUPVFNUFXUIJNUFVFNWYKXUHNXUGHXVONXUGVFZVNNWYKVFZVNUUOZXUMXUGVCZUFXUO
          XUIJXWAWYKUFUGZUHZWYKXUNXUHXWCXUMXUGHXWAXWBUUPVOVQVRZVSVTZWAWYEXUGWYF
          VCZUHZUFXUIXUEJXWGXWBUHZWYKXUHXUDXWHXUGWYFHWYEXWFXWBWBVOVQVRWYEWYFVLU
          GZWYFVDUTZXUSUGZWYFEUGZWYECBACVLUGZWYDACPWCZWDZABVLUGZWYDABOUUQZWDZWY
          EBVDUTZVEWEBVEWEZWYEXWSWYEVECVDUTZXWSWYEUURWYECXWOWGZWYEBXWRWGZWYECXW
          OUUSAXXAXWSVKWHWYDQWDZUUTZUVAWYEXWSVEBVEWYEBXWRUVBUVCWFZUVFZWYEXWJVIU
          GZVEXWJWIWHZXWJGVKWHZXWKWYEWYFXXGWGWYEWYFXXGUUSWYEXXAXWSUJUKZUIXWJGVK
          WYEXXKUIVKWHXXAXWSUIUNUKZVKWHWYEXXAXWSXXLVKXXDWYEXWSWYEXWSXXCWCUVDUVE
          WYEXXAUIXWSXXBWYEUVGZWYEXWSXXCXXEUVHUVIUVOWYECBXWOXWRXXFUVJABCDGHIJLM
          NOPQRSTUAUVKZUVLVEVIUGZGVJUGZXWKXXHXXIXXJUVMWJUVNGXVHVJUAXVGVJWKXVHVJ
          UGXVGVIVJXVFMVIUVPUVQUWDXVGUVRWLUVSZVEGXWJUVTWMUWAXWLWYFXUTUGZXWIXWKU
          HZEXUTWYFUCUWBVLVIVDWNZVDVLUWEZXXRXXSWJWOVLVIVDUWFZVLWYFXUSVDUWCUWGUW
          HUWIZXUFVAUGWYEUFXUEJWPWAWQWYEUEWYFUIXUGULUKZDUMUKZWYHEFVLWYEFNEUIXUM
          ULUKZDUMUKZVBZUEEXYEVBWYEFNEUIXYFDWRZUMUKZUJUKZVBZXYHWYEFNEXYJVBZUNUW
          JZUKZXYMUJUWJZUKZNEUIVBZXYMXYPUKFXYLWYEXYOXYRXYMXYPWYEVEVEGXYOXYREEXU
          TVEGVDUSUWKZUWLUTUKZUCXXPXUTXYTVCXXQXYSGXYSUWMUWNWLVTZWYEUWQZXXPWYEXX
          QWAWYEUEUUDEEEUNVLVLVLFXYMVAVAXUGVLUGZUUDUOZVLUGUHXUGYUDUNUKVLUGWYEXU
          GYUDUWOWSWYEUEEXUJVLFWYEXUMEUGZUHZXUPVLUGZWTWYEXUGEUGZUHZXUJVLUGZWTNU
          EYUIYUJNWYEYUHNWYENXAZNUEEXVPUWPUWRZNXUJVLXVTVPXBXWAYUFYUIYUGYUJXWAYU
          EYUHWYEXUMXUGEUWSUXHZXWAXUPXUJVLXWDXCXDYUFXUOJXUNVEUFXEYUFUWTZYUFXWBU
          HZXUOXFAYUEXWBXUOVLUGZWYDAYUEUHZXWBUHZXUOWYLXVKUNUKZVLYUEAXUMVLUGZXWB
          XUOYUSVCZEVLXUMEVDUUCZVLEXUTYVBUCVDXUSUXAUXBVLVIVDWOUXCUXDZUXEZAYUTUH
          ZXWBUHZXUOXVLYUSYVEJUFXVLXUNVAANVLXVMHVAHXVNVCZATWAXVMVAUGZYVEJUFXVLU
          XFXGZWAXHYVFXVJXVKUNXIXHAXWBXVLYUSVCZYUTAXWBUHZXVJWYLXVKUNYVKIWYKDIUO
          ZUPUKZWYLUFLVALIUFYVMVBVCZYVKSWAYVKYVLWYKVCZUHYVLWYKDUPYVKYVOXLXJAXWB
          XLZYVKDWYKUPXIWQZXKZXMXNUXGZYURWYLXVKYURDWYKADVLUGZYUEXWBRXOYUQXWBXLZ
          XPYURXUMWYKYUEYUTAXWBYVDUXIYWAXQXRXSZYBAYUEULXUNVEVGZXVEUGZWYDYUQYWDU
          LXUMKUTZUIVGZXVEUGZAYUHUHZULXUHVEVGZXVEUGZULXUGKUTZUIVGZXVEUGZUHZWTYU
          QYWDYWGUHZWTUENXUGXUMVCZYWHYUQYWNYWOYWPYUHYUEAXUGXUMEUWSUXHYWPYWJYWDY
          WMYWGYWPYWIYWCXVEYWPXUHXUNULVEXUGXUMHXTUXJXCYWPYWLYWFXVEYWPYWKYWEULUI
          XUGXUMKXTUXJXCUXKXDABCDEGHIJKLXUGMNOPQRSTUAUBUCUXLUXMZUXNZXMZYAZUXOXW
          EUXPZWYEUEEXYDXYIUMUKZVLXYMYUIXYDXYIYUIUIXUGYUIYCZYUHYUCWYEEVLXUGYVCU
          XEWSUXQZYUIDAYVTWYDYUHRXOYDZYEZNUEEXYJYXBXVPXVQUEXYJVFNYXBVFXWAXYFXYD
          XYIUMXUMXUGUIULUXRZXKVSZUXPZEVAUGZWYEEXUTVAUCXURVAUGXUTVAUGVDXXTVLVAU
          GVDVAUGWOUXSVLVIVAVDUXTWMUYAXURXUSVAUYBWLUVSWAZYXKEUYCZUYDEVLXYRWNZWY
          EEUIUYEZXYRWNZYXNVLWKZYXMEYXNEYXNUYFZWNYXOEUIUYGUYHEYXNYXQXYRYXQUEEUI
          VBZXYRUEEUIUYIUENEUIUIXVQXVPNUIVFUEUIVFYWPUIXFVSZVTZUYJUYKUIVLUGZYXPU
          YLUIVLUYMWLEYXNVLXYRUYNWMWAWYEEVEUYEZVLXYOYFUKZWYEUEEVEYYBYYCWYEYYCNE
          VEVBZUEEVEVBZWYEYYCNEDXYFUJUKZXUPUNUKZXYJUNUKZXYIXYFXYIUIUSUKZUMUKZUN
          UKZXUPUNUKZULUKZVBZYYDWYEYYCVLFYFUKZXYMXYNUKZVLXYMYFUKZFXYNUKZULUWJZU
          KNEYYFVBZFXYNUKZXYMXYNUKZNEYYKVBZFXYNUKZYYSUKYYNWYEVLFXYMEVLVIVLUYOUG
          WYEUYPWAZYXAYXIWYEEVAYYOWYEUEEYMWYKYWKUTZJURZVAYYOWYEYYONEYMWYKYWEUTZ
          JURZVBZUEEUUUGVBAYYOUUUJVCWYDABCDEFGHIJKLMNOPQRSTUAUBUCUDUYQWDZNUEEUU
          UIUUUGXVPXVQUEUUUIVFNYMUUUFJNYMVFNWYKYWKNXUGKNKNVLJYMWYKXVJUNUKZXUMWY
          KUIUSUKZUQUKZUNUKZVBZVBZUBNVLUUUPUUIVMXVRVNXVSVNUUOXWAYMUUUHUUUFJXWAW
          YKYMUGZUHZWYKYWEYWKUUUSXUMXUGKXWAUUURUUPVOVQVRVSYGUUUGVAUGYUIYMUUUFJW
          PWAYHUYRWYEEVLYYQWYEUEEXYIXYDYYIUMUKZUNUKZVLYYQWYEYYQUUUCUEEUUVAVBABC
          DEGHIJKLMNOPQRSTUAUBUCUYSZNUEEYYKUUVAXVPXVQUEYYKVFNUUVAVFXWAYYJUUUTXY
          IUNXWAXYFXYDYYIUMYXGXKXJVSYGYUIXYIUUUTYXEYUIXYDYYIYXDYUIXYIUIYXEYXCYI
          YEXRYHUYRUYTWYEYYPUUUBYYRUUUDYYSWYEYYOUUUAXYMXYNWYEUUUJNEYYGVBYYOUUUA
          WYENEUUUIYYGYUFDXUPUNUKZXYFUJUKZUUUIYYGYUFUUVDUUUIVCXYFUUUIUNUKZUUVCV
          CYUFUUVEDUIYMYUSJURZULUKZUNUKZUUVCYUFDUIUNUKZDUUVFUNUKZULUKDUUVJULUKZ
          UUVHUUVEYUFUUVIDUUVJULYUFDAYVTWYDYUERXOZUVDZXKYUFDUIUUVFUUVLYUFYCZYUF
          YUSJXUNUIYMYJYUFVUAZAYUEUUURYVAWYDUUURYUQXWBYVAWYKVUPZYVSYKYBZYUFUUUR
          UHZWYLXVKUUURYUFXWBWYLVLUGZUUVPYUODWYKAYVTWYDYUEXWBRVUBZYUFXWBXLZXPZY
          KZUUURYUFXWBXVKVLUGUUVPYUOXUMWYKYUFYUTXWBYUEYUTWYEYVDWSZWDUUWAXQZYKZX
          RZAYUEULXUNUIVGXVEUGZWYDYUQYWDUUWHYWRYUQJXUNVEUIUFXEUIUFUGZYUQVUCWAYW
          BVUDWFXMZYAVUEYUFUUVEDYMWYSWYLUNUKZDUUUMUSUKZDUUUMUPUKZUNUKZULUKZXVKU
          NUKZJURZULUKZDYMDWYLUNUKZXVKUNUKZJURZULUKZUUVKYUFDYMUUWKXVKUNUKZUUWNX
          VKUNUKZULUKZJURZULUKDYMUUXCJURZYMUUXDJURZULUKZULUKZUUWRUUVEYUFUUXFUUX
          IDULYUFUUXCUUXDJYWEUIWRZYLUKZIYMXUMYVLYWEUTZUNUKZVBZUIYMYJUUVOUUURYUF
          XWBWYKUUXLUTZUUXCVCUUVPYUFJUFUUXCUUXLVAYUFUUXLJUFDWYKUUXKUSUKZUIUSUKZ
          USUKZDUUXRUPUKZUNUKZXUMUUXRUQUKZUNUKZVBZJUFUUXCVBYUFUUXLJYMUUWNUUUNUN
          UKZVBZUUXKYLUKIUFDYVLUUXKUSUKZUIUSUKZUSUKZDUUYHUPUKZUNUKZXUMUUYHUQUKZ
          UNUKZVBZUUYDYUFYWEUUYFUUXKYLYUFYWEJYMUUUHVBUUYFYUFJYMVAYWEYUFJYMUUUOV
          AYWEAYUEYWEUUUPVCZWYDYUEAYUTUUYOYVDANVLUUUPKVAKUUUQVCAUBWAUUUPVAUGYVE
          JYMUUUOVUFXGWAXHZYKXMUUVRUUULUUUNUNXIYHVUGYUFJYMUUUHUUYEAYUEUUURUUUHU
          UYEVCZWYDYUEAYUTUUURUUYQYVDYVEUUURUHZUUUHWYKWYLUNUKZUUUNUNUKZUUWMUUWL
          UNUKZUUUNUNUKZUUYEUUYRUUUHUUUOUUYTYVEJYMUUUOYWEVAUUYPUUYRUUULUUUNUNXI
          XHAUUURUUUOUUYTVCYUTAUUURUHZUUULUUYSUUUNUNUVUCXVJWYLWYKUNUUURAXWBXVJW
          YLVCZUUVPYVQYKXJXKXMXNAUUURUUYTUVUBVCYUTUVUCUUYSUVUAUUUNUNUVUCUUYSWYK
          UUWMUUWLWYKUJUKZUNUKZUNUKWYKUVUAWYKUJUKZUNUKUVUAUVUCWYLUVUFWYKUNUVUCD
          UUUMUIULUKZUPUKUUWMUUWLUVUHUJUKZUNUKWYLUVUFUVUCDUUUMAYVTUUURRWDZUUURU
          UUMUFUGZAWYKVUHZWSZVUIUVUCUVUHWYKDUPUVUCWYKUIUVUCWYKUUURXWBAUUVPWSVUJ
          ZUVUCYCZVUKZXJUVUCUVUIUVUEUUWMUNUVUCUVUHWYKUUWLUJUVUPXJXJYNXJUVUCUVUG
          UVUFWYKUNUVUCUUWMUUWLWYKUVUCDUUUMUVUJUVUMXPZUVUCDUUUMUVUJUVUCWYKUIUVU
          NUVUOYIYIZUVUNUUURWYKVEWEAWYKVUQWSZVULXJUVUCUVUAWYKUVUCUUWMUUWLUVUQUV
          URXRUVUNUVUSVUMVUNXKXMUUYRUVUAUUWNUUUNUNUUYRUUWMUUWLAUUURUUWMVLUGYUTU
          VUQXMAUUURUUWLVLUGYUTUVURXMVUOXKYOZUXGYBZYPXNXKYUFJIUUYEUUYMUUYFUIUUX
          KUFYMUUYFUWMUUWNUUUNUNVURWYKUUYGVCZUUWNUUYKUUUNUUYLUNUVVBUUWLUUYIUUWM
          UUYJUNUVVBUUUMUUYHDUSWYKUUYGUIUSVVEZXJUVVBUUUMUUYHDUPUVVCXJYQUVVBUUUM
          UUYHXUMUQUVVCXJYQYJUFVEYRUTUIUUXKULUKZYRUTXEUVVDVEYRVUSVUTVVAUUVOYUFU
          IUUVOVVBVVCUUYNUUYDVCYUFIJUFUUYMUUYCYVOUUYKUUYAUUYLUUYBUNYVOUUYIUUXSU
          UYJUUXTUNYVOUUYHUUXRDUSYVOUUYGUUXQUIUSYVLWYKUUXKUSVVEXKZXJYVOUUYHUUXR
          DUPUVVEXJYQYVOUUYHUUXRXUMUQUVVEXJYQVVDWAYOYUFJUFUUYCUUXCYUOUUYAUUWKUU
          YBXVKUNYUOUUXSWYSUUXTWYLUNYUOUUXRWYKDUSXWBUUXRWYKVCYUFXWBUUXRWYKUIULU
          KZUIUSUKWYKXWBUUXQUVVFUIUSXWBWYKUIWYKVVOZXWBYCZVVFXKXWBWYKUIUVVGUVVHV
          VGXNWSZXJYUOUUXRWYKDUPUVVIXJYQYUOUUXRWYKXUMUQUVVIXJYQYPXNZYUOUUWKXVKU
          NXIXHZYKZUUURYUFXWBUUXCVLUGUUVPYUOUUWKXVKYUOWYSWYLYUODWYKUUVTXWBWYKVL
          UGZYUFUVVGWSZYIUUWBXRUUWEXRZYKZYUFJYMUUXDUUXOVAYUFUUXOJYMXUMUUUHUNUKZ
          VBJYMUUXDVBJIYMUVVQUUXNWYKYVLVCUUUHUUXMXUMUNWYKYVLYWEXTXJVVDYUFJYMUVV
          QUUXDUUVRUVVQXUMUUYEUNUKZUUXDUUVRUUUHUUYEXUMUNUVVAXJUUVRUVVRUUWNXUMUU
          UNUNUKZUNUKUUXDUUVRXUMUUWNUUUNYUFYUTUUURUUWDWDZUUVRUUWLUUWMUUVRDUUUMA
          YVTWYDYUEUUURRVUBZUUVRWYKUIUUURUVVMYUFWYKVVHWSZUUVRYCYIYIUUVRDUUUMUVW
          AUUURUVUKYUFUVULWSZXPXRZUUVRXUMUUUMUVVTUVWCXQZVVIUUVRUVVSXVKUUWNUNUUV
          RUVVSUUUNXUMUNUKXUMUVUHUQUKXVKUUVRXUMUUUNUVVTUVWEVUOUUVRXUMUUUMUVVTUV
          WCVVJUUVRUVUHWYKXUMUQWYEUUURUVUHWYKVCZYUEAUUURUVWFWYDUVUPXMXMXJVUNXJX
          NZXNZYPVVKUUVRUUWNXVKUNXIXHZUUVRUUWNXVKUVWDUUWFXRYUFULUUXLVEVGZXVEUGZ
          ULUUXLUIVGXVEUGYUFVHVVPZUVWJYWFVHUTZVHWHZUVWKVVLYUFYWFUVWMVHWHZUVWNYU
          FYWGUVWOAYUEYWGWYDYUQYWDYWGYWQVVMXMZYWFVVNVVQZUVWNYWFUUXKYLUKZUVWMVHW
          HZUVWOUVWJUVWRUVWMVHUVWJULYWEVEUUXKUSUKZVGZUUXKYLUKZUVWRVEVVRUGUUXKVV
          RUGZUVWJUVXBVCVVSVVTULYWEVEUUXKXUMKVWAVWBWMUVXAYWFUUXKYLUVWTUIVCUVXAY
          WFVCUVWTVEUIULUKZUIVEUIVWGUYLVWCVWDVTULYWEUVWTUIVWEWLVWFVTVWHUVXCYWFV
          AUGUVWSUVWOWJVVTULYWEUIVWPUVWMYWFUUXKVAVWIWMUWHVWQUVWJUVWMVHVWJVWKZYU
          FJUUXLVEUIUFXEUUWIYUFVUCWAYUOUUXPUUXCVLUVVKUVVOXSVUDWFZYUFUVWLULUUXOU
          IVGZXUMUVWMUNUKZVHWHUVXGXVEUGVVLYUFUVWMXUMJYWEUUXOUIYMYJUUVOUUWDUVWQU
          UVRUUUHUUYEVLUVVAUUVRUUWNUUUNUVWDUVWEXRZXSZUUVRWYKUUXOUTUUXDUVVQUVWIU
          VWHYSVWLUVXGUVXHVHVWJVWKVWMXJYUFUUWQUUXFDULYUFYMUUWPUUXEJUUVRUUWKUUWN
          XVKUUVRWYSWYLUUVRDWYKUVWAUVWBYIUUWCXRUVWDUUWFVWNVRXJYUFUUVEYMUUYEJURZ
          UUXHULUKZDUUXGULUKZUUXHULUKUUXJYUFUUVEXYFUVXKUNUKZUIUVXKUNUKZXUMUVXKU
          NUKZULUKUVXLAYUEUUVEUVXNVCZWYDYUEAYUTUVXQYVDYVEUUUIUVXKXYFUNYVEYMUUUH
          UUYEJUVUTVRXJYKXMYUFUIXUMUVXKUUVNUUWDYUFUUYEJYWEUIYMYJUUVOUVVAUVXIUVW
          PYAZVWNYUFUVXOUVXKUVXPUUXHULYUFUVXKUVXRVWOYUFUVXPYMUVVRJURUUXHYUFUUYE
          XUMJYWEUIYMYJUUVOUVVAUVXIUVWPUUWDVXNYUFYMUVVRUUXDJUVWGVRXNZYQYOYUFUVX
          KUVXMUUXHULYUFUVXKUFUUXCJURZVEUUXLUTZUVXDYRUTZUUXCJURZULUKUVXMYUFUVXK
          UFDUIYVLULUKZUIUSUKZUSUKZDUVYEUPUKZUNUKZXUMUVYEUQUKZUNUKZIURZUFDUIWYK
          ULUKZUIUSUKZUSUKZDUVYMUPUKZUNUKZXUMUVYMUQUKZUNUKZJURZUVXTYUFUUYEUVYJJ
          IUIVEYMUFXEYMUIYRUTZUVYBYJUVXDUIYRVWDVUTVVAZWYKUVYDVCZUUWNUVYHUUUNUVY
          IUNUWUBUUWLUVYFUUWMUVYGUNUWUBUUUMUVYEDUSWYKUVYDUIUSVVEZXJUWUBUUUMUVYE
          DUPUWUCXJYQUWUBUUUMUVYEXUMUQUWUCXJYQUUVOYUNUVXIVWRUVYKUVYSVCYUFUFUVYJ
          UVYRIJYVOUVYHUVYPUVYIUVYQUNYVOUVYFUVYNUVYGUVYOUNYVOUVYEUVYMDUSYVOUVYD
          UVYLUIUSYVLWYKUIULUXRXKZXJYVOUVYEUVYMDUPUWUDXJYQYVOUVYEUVYMXUMUQUWUDX
          JYQVWSWAYUFUFUVYRUUXCJYUOUVYPUUWKUVYQXVKUNYUOUVYNWYSUVYOWYLUNYUOUVYMW
          YKDUSYUOUIWYKYUOYCUVVNVWTZXJYUOUVYMWYKDUPUWUEXJYQYUOUVYMWYKXUMUQUWUEX
          JYQVRYOYUFUUXCJUUXLVEUFXEYUNUVVKUVVOUVXEVXAYUFUVYADUVYCUUXGULYUFUVYAD
          VEUSUKZDVEUPUKZUNUKZXUMVEUQUKZUNUKZUUVIDYUFJVEUUXCUWUJUFUUXLVAUVVJYUF
          WYKVEVCZUHZUUWKUWUHXVKUWUIUNUWULWYSUWUFWYLUWUGUNUWULWYKVEDUSYUFUWUKXL
          ZXJUWULWYKVEDUPUWUMXJYQUWULWYKVEXUMUQUWUMXJZYQVEUFUGZYUFVXBWAZYUFUWUH
          UWUIUNXIWQYUFUWUHDUWUIUIUNYUFUWUHUUVIDYUFUWUFDUWUGUIUNYUFDUUVLVXCYUFD
          UUVLVXDZYQUUVMXNYUFXUMUUWDVXEZYQUUVMYOUVYCUUXGVCYUFUVYBYMUUXCJYMUVYBU
          WUAVXFZVXGWAYQYOXKYUFDUUXGUUXHUUVLYUFUUXCJUUXLUIYMYJUUVOUVVLUVVPUVXFY
          AYUFUVXPUUXHVLUVXSYUFXUMUVXKUUWDUVXRXRVXHVXIYOVXJAUUWRUUXBVCWYDYUEAUU
          WQUUXADULAYMUUWPUUWTJUVUCUUWOUUWSXVKUNUVUCDWYKUVUJAUUURXLVXKXKVRXJXOY
          UFUUXAUUVJDULYUFUUXAYMDYUSUNUKZJURUUVJYUFYMUUWTUWUTJUUVRDWYLXVKUVWAUU
          WCUUWFVXLVRYUFYUSDJXUNUIYMYJUUVOUUVQUUWGUUWJUUVLVXNYSXJYOVXJYUFUUVGXU
          PDUNYUFXUPUFXVLJURVEXUNUTZUVYBXVLJURZULUKUUVGYUFUFXUOXVLJYUFJUFXVLXUN
          VAYUEWYEYUTXUNXVMVCYVDWYENVLXVMHVAYVGWYETWAZYVHWYEYUTUHYVIWAXHYKZYUOX
          VJXVKUNXIXHZVRYUFXVLJXUNVEUFXEYUNUWVEYUOXVJXVKWYEXWBXVJVLUGZYUEAXWBUW
          VFWYDYVKXVJWYLVLYVQYVKDWYKAYVTXWBRWDYVPXPZXSXMXMUUWEXRYWSVXAYUFUWVAUI
          UWVBUUVFULYUFUWVAVELUTZUWUIUNUKZUIUIUNUKZUIYUFJVEXVLUWVIUFXUNVAUWVDUW
          ULXVJUWVHXVKUWUIUNUWULWYKVELUWUMVOUWUNYQUWUPYUFUWVHUWUIUNXIWQYUFUWVHU
          IUWUIUIUNYUFUWVHUWUGUIAUWVHUWUGVCWYDYUEAIVEYVMUWUGUFLVAYVNASWAAYVLVEV
          CZUHYVLVEDUPAUWVKXLXJUWUOAVXBWAADVEUPXIWQXOUWUQXNUWURYQYUFUIUUVNUVDYO
          YUFUWVBYMXVLJURUUVFUVYBYMXVLJUWUSVXGYUFYMXVLYUSJAYUEUUURYVJWYDUUURYUQ
          XWBYVJUUVPAXWBYVJYUEYVRXMYKYBVRVXMYQVXOXJXNYUFUUVCXYFUUUIYUFDXUPUUVLY
          WTXRYUFUIXUMUUVNUUWDUXQZYUFUUUHJYWEUIYMYJUUVOUUVRUUUHXFUVXJUVWPYAYUFU
          IXUMWRZUSUKZXYFVEYUFUIXUMUUVNUUWDVVFYUFUWVMVLUGZUWVMVDUTZUIVKWHZUWVNV
          EWEZYUFXUMUUWDYDYUFXUMVDUTZGUWVPUIVKYUEUWVSGVKWHZWYEYUEUWVSXUSUGZUWVT
          UWWAXUMXUTEXUMXUTUGZYUTUWWAXXTXYAUWWBYUTUWWAUHWJWOXYBVLXUMXUSVDUWCUWG
          VXPUCVXQUWWAUWVSVIUGZVEUWVSWIWHZUWVTXXOXXPUWWAUWWCUWWDUWVTUVMWJUVNXXQ
          VEGUWVSUVTWMVXRVXSWSYUFUWVPUWVSYUFXUMUUWDVXTVYAWYEGUIVCYUEXXNWDVYCUWV
          OUIVIUGUWVQUWVRVYLUWVMUIVYBVYDVYEVYFZVYGUVOYUFDXUPXYFUUVLYWTUWVLUWWEV
          YHVYIYPUUUKWYENEYYFXUPUNYYTFVAVAVAYUKXVPYXKYUFDXYFUJXIXUPVAUGYUFUFXUO
          JWPWAZWYEYYTXFFXUQVCWYEUDWAZYTZVYJXKWYEYYQUUUCFXYNUUVBXKYQWYENEYYHYYL
          ULUUUBUUUDVAVAVAYUKXVPYXKYUFYYGXYJUNXIYUFYYKXUPUNXIWYENEYYGXYJUNUUUAX
          YMVAVAVAYUKXVPYXKYUFYYFXUPUNXIYUFXYFXYIUMXIUWWHWYEXYMXFZYTWYENEYYKXUP
          UNUUUCFVAVAVAYUKXVPYXKYUFXYIYYJUNXIUWWFWYEUUUCXFUWWGYTYTYOZWYENEYYMVE
          YUFYYMDYYJUNUKZXUPUNUKZUWWLWRZULUKVEYUFYYHUWWLYYLUWWMULYUFYYHYYFXYJUN
          UKZXUPUNUKUWWLYUFYYFXUPXYJYUFDXYFUUVLUWVLUWWEUVFYWTYUFXYFXYIUWVLYUFDU
          UVLYDZYEZVYMYUFUWWNUWWKXUPUNYUFUWWNDXYJXYFUJUKZUNUKUWWKYUFDXYFXYJUUVL
          UWVLUWWPUWWEVYNYUFUWWQYYJDUNYUFYYJXYJXYFUIUMUKZUJUKUWWQYUFXYFXYIUIUWV
          LUWWEUWWOUUVNVYKYUFUWWRXYFXYJUJYUFXYFUWVLVYOXJVYPXJXNXKXNYUFYYLUWWKWR
          ZXUPUNUKUWWMYUFYYKUWWSXUPUNYUFDYYJUUVLYUFXYFYYIUWVLYUFXYIUIUWWOUUVNYI
          YEZVYQXKYUFUWWKXUPYUFDYYJUUVLUWWTXRZYWTVYQXNYQYUFUWWLYUFUWWKXUPUWXAYW
          TXRVYRXNYPZXNUENEVEVEXVQXVPXVAUEVEVFYWPVEXFVSZWUCVEYYBUGYUIVEVYSVYTWA
          YHUYRWYEYYNYYDYYCVLXYRYFUKZUWXBUWWJWYEVLYXRYFUKYYEUWXDYYDWYEUEUIVEVLW
          UAWUBUTZUWXEVLVLEEUUUEWYEYUCUHZYCUWXFUWQVLUEVLUIVBZYFUKZUEVLVEVBZVCWY
          EVLVLYXNUYFZYFUKZVLYYBUYFZUWXHUWXIYYAUWXKUWXLVCUYLUIWUDWLUWXJUWXGVLYF
          UEVLUIUYIWUEUEVLVEUYIWUFWAEVLWKWYEYVCWAUWXEVLWUGUKZUWXEUWXEVAUGUWXMUW
          XEVCWUAWUBVWAUWXEVAVLWUAWUHUGVLUWXEWUIVCWUJVLUWXEWUAWUMUWXEUWMZWUKWLW
          ULWLVXFUWXNEUWXEWUNUTUTEVCZWYEUWXEWUOUGEUWXEUGUWXOUWXEUWXNWUPEXYTUWXE
          YUAXYSVLWUQUTUGZVEVLUGZXXPXYTUWXEUGWURVWGXXQXYSVEGUWXEVLUWXEUWXNWUSWU
          TWVAUVSEUWXEWVBWMWAWVCYXRXYRVLYFYXSWUEUWXCWVDVYJWYEVEXYTEWYEGWVEUGZVE
          XYTUGZWYEGUIWVEXXNWVLWVFUWXPUWXQUWXRUWXSWURVWGXYSVEGVLWVGWVHVXSYUAWVI
          ZWYEUFWYKVEHUTZUTZJURZUIVEULUKZXYIUMUKZUNUKZUIVEXYOUTZVEXYRUTZWYEUWYF
          UWYDUIUNUKZUIWYEUWYCUWYDUWYEUIUNWYEUWYCVEUWYAUTZUVYBUWYBJURZULUKUWYDW
          YEUWYBJUWYAVEUFXEWYEUWTZWYEXWBUHZUWYBXFAWYDVEEUGZXWBUWYBVLUGZUWXTYURY
          UPWTAUWYNUHZXWBUHZUWYOWTNVEUWYQUWYONUWYPXWBNAUWYNNANXANVEEXVPWVMUWRZX
          WBNXAUWRNUWYBVLNWYKUWYANVEHXVOXVAVNZXVSVNVPXBVYSXUMVEVCZYURUWYQYUPUWY
          OUWYTYUQUWYPXWBUWYTYUEUWYNAXUMVEEUWSUXHZWVJUWYTXUOUWYBVLUWYTWYKXUNUWY
          AXUMVEHXTZVQXCXDYWBWVKWVNAWYDUWYNULUWYAVEVGZXVEUGZUWXTYUQYWDWTUWYPUXU
          DWTNVEUWYPUXUDNUWYRNUXUCXVENULUWYAVEXVAXVIUWYSUUJVPXBVYSUWYTYUQUWYPYW
          DUXUDUXUAUWYTYWCUXUCXVEUWYTXUNUWYAULVEUXUBUXJXCXDYWRWVKWVOVXAWYEUWYJU
          IUWYKVEULWYEUWYJUWUGVEVEUQUKZUNUKZUWVJUIWYEJVEWYLVEWYKUQUKZUNUKZUXUFU
          FUWYAVAWYENVEXVMJUFUXUHVBZVLHVAUWVCWYEUWYTUHZJUFXVLUXUHUXUJXWBUHZXVJW
          YLXVKUXUGUNWYEXWBUVUDUWYTAXWBUVUDWYDYVQXMZXMUXUKXUMVEWYKUQWYEUWYTXWBW
          BXKYQYPYUBUXUIVAUGWYEJUFUXUHUXFXGWAWQZWYEUWUKUHZWYLUWUGUXUGUXUEUNUXUN
          WYKVEDUPWYEUWUKXLZXJUXUNWYKVEVEUQUXUOXJYQUWUOWYEVXBWAWYEUWUGUXUEUNXIW
          QWYEUWUGUIUXUEUIUNWYEDAYVTWYDRWDZVXDWYEVEYUBVXEYQUWVJUIVCWYEWVPWAYOWY
          EYMUWYBJURYMVEJURZUWYKVEWYEYMUWYBVEJWYEUUURUHZUWYBUXUHWYLVEUNUKVEUUUR
          WYEXWBUWYBUXUHVCUUVPWYEJUFUXUHUWYAVAUXUMUWYMWYLUXUGUNXIXHYKUXURUXUGVE
          WYLUNUXURWYKWYEUUURXLWVQXJUXURWYLUUURWYEXWBUUVSUUVPAXWBUUVSWYDUWVGXMZ
          YKWVRYOVRYMUVYBUWYBJUWUAVXGYMUVYTWKZYMWVSUGZWVTUXUQVEVCUXUTUXVAYMUVYT
          YJWWAWWBYMJUIWWDWLWVDYQXNWYEUWYEUIXYIUMUKUIUWYDUIXYIUMWWCVWFWYEXYIWYE
          DUXUPYDWWEVXMYQUWYIUWVJUIUWYDUIUIUNWWCVWFWVPVTYGWYEUWYNUWYGUWYFVCUWXT
          WYEEEUWYCUWYEUNEFXYMVAVAVEWYEEVLFYXAWWFWYEEVLXYMYXIWWFYXKYXKYXLWYEUWY
          NUHZUEVEXUJUWYCEFVAXULUXVBXWEWAUXVBXUGVEVCZUHZUFXUIUWYBJUXVDXWBUHZWYK
          XUHUWYAUXVEXUGVEHUXVBUXVCXWBWBVOVQVRWYEUWYNXLZUWYCVAUGUXVBUFUWYBJWPWA
          WQUXVBUEVEYXBUWYEEXYMVAXYMUEEYXBVBVCUXVBYXHWAUXVDXYDUWYDXYIUMUXVDXUGV
          EUIULUXVBUXVCXLXJXKUXVFUXVBUWYDXYIUMXIWQWWGWWHWYEUWYHVEYXQUTZUIVEYXQX
          YRYXTWWIWYEUWYNUXVGUIVCUWXTEUIVEUYGWWOVXSVVKVYJWWJXKWYEYXJEVLFWNEVLYY
          BWWKZXYMWNXYQFVCYXKYXAWYEUEEYXBUXVHXYMYUIYXBVLUGYXBVEWEYXBUXVHUGYXFYU
          IXYDXYIYXDYUFXYFVEWEZWTYUIXYDVEWEZWTNUEYUIUXVJNYULUXVJNXAXBXWAYUFYUIU
          XVIUXVJYUMXWAXYFXYDVEYXGWWLXDUWWEUXOYXEWWMYXBVLVEWWNUWIYXHUXPEFXYMVAW
          WPWWQWYENEUIXYJUJXYRXYMVAVLVLYUKXVPYXKUUVNUWWPWYEXYRXFUWWIYTYNWYENEXY
          KXYGYUFXYFXYIWRZUMUKXYKXYGYUFXYFXYIUWVLUWWEUWWOWWRYUFUXVKDXYFUMYUFDUU
          VLWWSXJVYIYPXNNUEEXYGXYEXVPXVQUEXYGVFNXYEVFXWAXYFXYDDUMYXGXKVSYGXWGXY
          DWYGDUMXWGXUGWYFUIULWYEXWFXLXJXKXYCWYEWYGDWYEUIWYFWYEYCZXXGUXQUXUPYEW
          QWYEUFXUEWYNJWYEJUFWYNXUDVAWYENWYFXVMJUFWYNVBZVLHVAUWVCWYEXUMWYFVCZUH
          ZJUFXVLWYNUXVOXWBUHZXVJWYLXVKWYMUNWYEXWBUVUDUXVNUXULXMUXVPXUMWYFWYKUQ
          WYEUXVNXWBWBXKYQYPXXGUXVMVAUGWYEJUFWYNUXFXGWAWQUWYMWYLWYMUNXIXHZVRYNX
          KWYEWYGBUNUKZDUMUKWYJWYRWYEWYGBDWYEUIWYFXXMAWYFVIUGWYDACBPOWWTZWDWXAA
          VEWYGWIWHZWYDAVEWYFUSUKZUIWIWHUXVTAUXWAWYFWRZUIWIWYFWXBAUUXKUXWBWIWHZ
          UXWBUIWIWHZAUXWBVDUTZUIWIWHUXWCUXWDUHAUXWEUIAUXWBAWYFAWYFUXVSWCZYDWGA
          UVGZAUXWEXXKUIVKAUXWEXWJXXKAWYFUXWFVXTACBXWNXWQABOWXCZUVJXNAXXAUIXWSA
          CXWNWGZUIWVEUGAWVLWAABXWQUXWHWXDAXXAUIUJUKXXAXWSVKAXXAAXXAUXWIWCWXEQW
          XFWXGWXFWXHAUXWBUIAWYFUXVSWXIUXWGWXLWFVVMWXJAVEWYFUIAUURUXVSUXWGWXMWF
          WDWYEBABWVEUGWYDOWDZWXKWYEBUXWJWXNUXUPWXOWYEUXVRWYQDUMWYEUXVRUIBUNUKZ
          WYFBUNUKZULUKWYQWYEUIWYFBUXVLXXGXWRVWNWYEUXWKBUXWLCULWYEBXWRVWOWYECBX
          WOXWRXXFWXPYQXNXKVYIWYEWYPUFWYNWYIUNUKZJURXUCWYEWYNWYIJXUDVEUFXEUWYLU
          XVQUWYMWYLWYMUXUSUWYMWYFWYKWYEXWIXWBXXGWDWYEXWBXLZXQXRAWYDXWLULXUDVEV
          GXVEUGZXYCAXWLUHUXWOULWYFKUTUIVGXVEUGABCDEGHIJKLWYFMNOPQRSTUAUBUCUXLU
          XNWVOWYEBDXWRUXUPYEZWYAWYEUFUXWMXUBJUWYMUXWMWYLWYTUNUKXUAUNUKZXUBUWYM
          UXWMWYLXUAUNUKZWYIUIBUJUKZWYKUQUKZUNUKZUNUKZUXWRWYTUNUKUXWQUWYMUXWMUX
          WRUXWTUNUKZWYIUNUKUXWRWYIUNUKUXWTUNUKUXXBUWYMWYNUXXCWYIUNUWYMWYNWYLXU
          AUXWTUNUKZUNUKUXXCUWYMWYMUXXDWYLUNUWYMWYMCUXWSUNUKZWYKUQUKUXXDUWYMWYF
          UXXEWYKUQUWYMCBAXWMWYDXWBXWNXOZAXWPWYDXWBXWQXOZAXWTWYDXWBUXWHXOZWXQXK
          UWYMCUXWSWYKUXXFUWYMBUXXGUXXHWXRZUXWNWXSXNXJUWYMWYLXUAUXWTUXUSUWYMCWY
          KUXXFUXWNXQZUWYMUXWSWYKUXXIUXWNXQZVXLYSXKUWYMUXWRUXWTWYIUWYMWYLXUAUXU
          SUXXJXRZUXXKWYEWYIVLUGXWBUXWPWDZVYMUWYMUXWRWYIUXWTUXXLUXXMUXXKVXLYOUW
          YMUXXAWYTUXWRUNUWYMWYIBWYKUMUKZUJUKWYIUIUXXNUJUKZUNUKWYTUXXAUWYMWYIUX
          XNUXXMUWYMBWYKUXXGUWYMWYKUXWNVUJZYEUWYMBWYKUXXGUXXHUXXPWWMWXQUWYMBDWY
          KUXXGUXXHAYVTWYDXWBRXOZUXXPVYKUWYMUXWTUXXOWYIUNUWYMUXWTUIBWYKUQUKZUJU
          KUXXOUWYMBWYKUXXGUXXHUWYMWYKUXWNWXTWYBUWYMUXXNUXXRUIUJUWYMXWPXWBUXXNU
          XXRVCUXXGUXWNBWYKWYCVYEXJYSXJVXJXJUWYMWYLXUAWYTUXUSUXXJUWYMBWYSUXXGUW
          YMDWYKUXXQUXXPYIYEZVYMYOUWYMWYLWYTXUAUXUSUXXSUXXJVXLXNVRXNYN $.
      $}
    $}

    ${
      $d b j k r x C $.  $d b j k ph $.  $d b k r A $.  $d b k r B $.
      $d j k y C $.
      $( Generalize the binomial theorem ~ binom to positive real summand
         ` A ` , real summand ` B ` , and complex exponent ` C ` .  Proof in
         ~ https://en.wikibooks.org/wiki/Advanced_Calculus ; see also
         ~ https://en.wikipedia.org/wiki/Binomial_series ,
         ~ https://en.wikipedia.org/wiki/Binomial_theorem (sections "Newton's
         generalized binomial theorem" and "Future generalizations"), and proof
         "General Binomial Theorem" in
         ~ https://proofwiki.org/wiki/Binomial_Theorem .  (Contributed by Steve
         Rodriguez, 22-Apr-2020.) $)
      binomcxp $p |- ( ph -> ( ( A + B ) ^c C ) = sum_ k e. NN0
          ( ( C _Cc k ) x. ( ( A ^c ( C - k ) ) x. ( B ^ k ) ) ) ) $=
        ( vb vx cn0 co cv cbcc cexp cmul cc0 cmpt cfv vr vj wcel caddc ccxp csu
        vy cmin wceq binomcxplemnn0 cabs ccnv cc cseq cli cdm crab cxr clt csup
        cr cico cima cn c1 eqid fveq2 oveq2 oveq12d cbvmptv mpteq2i a1i fveq12d
        id oveq1 oveq2d fveq1i oveq1i seqeq3 ax-mp eleq1i rabbii supeq1i oveq2i
        imaeq2i binomcxplemnotnn0 pm2.61dan ) ADLUCBCUDMDUEMLDENZOMBDWHUHMUEMCW
        HPMQMQMEUFUIABCDEFGHIUJABCDUKULZRUDUANZJUMKLKNZKLDWKOMZSZTZJNZWKPMZQMZS
        ZSZTZRUNZUOUPZUCZUAVAUQZURUSUTZVBMZVCZJXGLWHWOJUMKLWKUBLDUBNZOMZSZTZWPQ
        MZSZSZTTEUFSZUDWJXNTZRUNZXBUCZUAVAUQZURUSUTZXNUBEJUMKVDWKWKUGLDUGNZOMZS
        ZTZQMZWOWKVEUHMZPMZQMZSZSXJUAJFGHIXJVFJUMXMELWHXJTZWOWHPMZQMZSKELXLYLWK
        WHUIZXKYJWPYKQWKWHXJVGWKWHWOPVHVIVJVKXTVFJUMYIEVDWHYJQMZWOWHVEUHMZPMZQM
        ZSKEVDYHYQYMYEYNYGYPQYMWKWHYDYJQYMVNZYMWKWHYCXJYCXJUIYMUGUBLYBXIYAXHDOV
        HVJVLYRVMVIYMYFYOWOPWKWHVEUHVOVPVIVJVKXFRXTVBMWIXEXTRVBURXDXSUSXCXRUAVA
        XAXQXBWTXPUIXAXQUIWJWSXNJUMWRXMKLWQXLWNXKWPQWKWMXJKUBLWLXIWKXHDOVHVJVQV
        RVKVKVQUDWTXPRVSVTWAWBWCWDWEXOVFWFWG $.
    $}
  $}

$( (End of Steve Rodriguez's mathbox.) $)
