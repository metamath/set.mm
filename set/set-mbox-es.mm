$[ set-main.mm $]
$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Mathbox for Eric Schmidt
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Miscellany
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x B $.
    rspesbcd.1 $e |- ( ph -> A e. B ) $.
    rspesbcd.2 $e |- ( ph -> [. A / x ]. ps ) $.
    $( Restricted quantifier version of ~ spesbcd .  (Contributed by Eric
       Schmidt, 29-Sep-2025.) $)
    rspesbcd $p |- ( ph -> E. x e. B ps ) $=
      ( cv wcel wa wex wrex wsbc sbcel1v sylibr sbcan sylanbrc spesbcd df-rex )
      ACHEIZBJZCKBCELAUACDATCDMZBCDMUACDMADEIUBFCDENOGTBCDPQRBCESO $.
  $}

  ${
    $d x A $.
    rext0.1 $e |- ph $.
    $( Nonempty existential quantification of a theorem is true.  (Contributed
       by Eric Schmidt, 19-Oct-2025.) $)
    rext0 $p |- ( E. x e. A ph <-> A =/= (/) ) $=
      ( wn wral c0 wceq wrex wne notnoti ralf0 notbii dfrex2 df-ne 3bitr4i ) AE
      ZBCFZECGHZEABCICGJRSQBCADKLMABCNCGOP $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Study of dfbi1ALT
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Version of ~ dfbi1ALT using ` T. ` for step 2 and shortened using ~ a1i ,
     ~ a2i , and ~ con4i .  (Contributed by Eric Schmidt, 22-Oct-2025.)
     (New usage is discouraged.)  (Proof modification is discouraged.) $)
  dfbi1ALTa $p |-
                ( ( ph <-> ps ) <-> -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) ) $=
    ( wb wi wn df-bi wtru tru ax-1 a1i con4i a2i ax-mp ) ABCZABDBADEDEZDONDEDEZ
    NOCZABFGPQDZHRGREZQPDZSDZDSGEZDSTISUAUBUAUBDSUBUAUAEUBENOFJKJLMKMM $.

  ${
    simprimi.1 $e |- -. ( ph -> -. ps ) $.
    $( Inference associated with ~ simprim .  Proved exactly as step 11 is
       obtained from step 4 in ~ dfbi1ALTa .  (Contributed by Eric Schmidt,
       22-Oct-2025.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    simprimi $p |- ps $=
      ( wtru tru wn wi ax-1 a1i con4i a2i ax-mp ) DBEBDBFZAMGZGMDFZGMAHMNONOGMO
      NNFOFCIJIKLJL $.
  $}

  $( Further shorten ~ dfbi1ALTa using ~ simprimi .  (Contributed by Eric
     Schmidt, 22-Oct-2025.)  (New usage is discouraged.)
     (Proof modification is discouraged.) $)
  dfbi1ALTb $p |-
                ( ( ph <-> ps ) <-> -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) ) $=
    ( wb wi wn df-bi simprimi ax-mp ) ABCZABDBADEDEZDJIDEDEZIJCZABFLKDKLDIJFGH
    $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Relation-preserving functions
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c RelPres $.

  $( Extend the definition of a wff to include the relation-preserving
     property.  (Contributed by Eric Schmidt, 11-Oct-2025.) $)
  wrelp $a wff H RelPres R , S ( A , B ) $.

  ${
    $d x y A $.  $d x y B $.  $d x y R $.  $d x y S $.  $d x y H $.
    $( Define the relation-preserving predicate.  This is a viable notion of
       "homomorphism" corresponding to ~ df-isom .  (Contributed by Eric
       Schmidt, 11-Oct-2025.) $)
    df-relp $a |- ( H RelPres R , S ( A , B ) <-> ( H : A --> B /\
        A. x e. A A. y e. A ( x R y -> ( H ` x ) S ( H ` y ) ) ) ) $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x y C $.  $d x y H $.  $d x y G $.
    $d x y R $.  $d x y S $.  $d x y T $.
    $( Equality theorem for relation-preserving functions.  (Contributed by
       Eric Schmidt, 11-Oct-2025.) $)
    relpeq1 $p |- ( H = G ->
          ( H RelPres R , S ( A , B ) <-> G RelPres R , S ( A , B ) ) ) $=
      ( vx vy wceq wf cv wbr cfv wi wral wa wrelp feq1 fveq1 df-relp 2ralbidv
      breq12d imbi2d anbi12d 3bitr4g ) FEIZABFJZGKZHKZCLZUHFMZUIFMZDLZNZHAOGAOZ
      PABEJZUJUHEMZUIEMZDLZNZHAOGAOZPABCDFQABCDEQUFUGUPUOVAABFERUFUNUTGHAAUFUMU
      SUJUFUKUQULURDUHFESUIFESUBUCUAUDGHABCDFTGHABCDETUE $.

    $( Equality theorem for relation-preserving functions.  (Contributed by
       Eric Schmidt, 11-Oct-2025.) $)
    relpeq2 $p |- ( R = T ->
          ( H RelPres R , S ( A , B ) <-> H RelPres T , S ( A , B ) ) ) $=
      ( vx vy wceq wf cv wbr cfv wi wral wa wrelp breq imbi1d df-relp 2ralbidv
      anbi2d 3bitr4g ) CEIZABFJZGKZHKZCLZUFFMUGFMDLZNZHAOGAOZPUEUFUGELZUINZHAOG
      AOZPABCDFQABEDFQUDUKUNUEUDUJUMGHAAUDUHULUIUFUGCERSUAUBGHABCDFTGHABEDFTUC
      $.

    $( Equality theorem for relation-preserving functions.  (Contributed by
       Eric Schmidt, 11-Oct-2025.) $)
    relpeq3 $p |- ( S = T ->
          ( H RelPres R , S ( A , B ) <-> H RelPres R , T ( A , B ) ) ) $=
      ( vx vy wceq wf cv wbr cfv wi wral wa wrelp breq imbi2d df-relp 2ralbidv
      anbi2d 3bitr4g ) DEIZABFJZGKZHKZCLZUFFMZUGFMZDLZNZHAOGAOZPUEUHUIUJELZNZHA
      OGAOZPABCDFQABCEFQUDUMUPUEUDULUOGHAAUDUKUNUHUIUJDERSUAUBGHABCDFTGHABCEFTU
      C $.

    $( Equality theorem for relation-preserving functions.  (Contributed by
       Eric Schmidt, 11-Oct-2025.) $)
    relpeq4 $p |- ( A = C ->
          ( H RelPres R , S ( A , B ) <-> H RelPres R , S ( C , B ) ) ) $=
      ( vx vy wceq wf cv wbr cfv wi wral wa wrelp feq2 raleq df-relp raleqbi1dv
      anbi12d 3bitr4g ) ACIZABFJZGKZHKZDLUFFMUGFMELNZHAOZGAOZPCBFJZUHHCOZGCOZPA
      BDEFQCBDEFQUDUEUKUJUMACBFRUIULGACUHHACSUAUBGHABDEFTGHCBDEFTUC $.

    $( Equality theorem for relation-preserving functions.  (Contributed by
       Eric Schmidt, 11-Oct-2025.) $)
    relpeq5 $p |- ( B = C ->
          ( H RelPres R , S ( A , B ) <-> H RelPres R , S ( A , C ) ) ) $=
      ( vx vy wceq wf cv wbr cfv wi wral wa wrelp feq3 anbi1d df-relp 3bitr4g )
      BCIZABFJZGKZHKZDLUDFMUEFMELNHAOGAOZPACFJZUFPABDEFQACDEFQUBUCUGUFBCAFRSGHA
      BDEFTGHACDEFTUA $.
  $}

  ${
    $d y z H $.  $d y z R $.  $d y z S $.  $d y z A $.  $d y z B $.
    $d x y z $.
    nfrelp.1 $e |- F/_ x H $.
    nfrelp.2 $e |- F/_ x R $.
    nfrelp.3 $e |- F/_ x S $.
    nfrelp.4 $e |- F/_ x A $.
    nfrelp.5 $e |- F/_ x B $.
    $( Bound-variable hypothesis builder for a relation-preserving function.
       (Contributed by Eric Schmidt, 11-Oct-2025.) $)
    nfrelp $p |- F/ x H RelPres R , S ( A , B ) $=
      ( vy vz cv wbr cfv wral nfcv nfbr nffv wrelp wf wi wa df-relp nfim nfralw
      nff nfan nfxfr ) BCDEFUABCFUBZLNZMNZDOZULFPZUMFPZEOZUCZMBQZLBQZUDALMBCDEF
      UEUKUTAABCFGJKUHUSALBJURAMBJUNUQAAULUMDAULRZHAUMRZSAUOUPEAULFGVATIAUMFGVB
      TSUFUGUGUIUJ $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x y R $.  $d x y S $.  $d x y H $.
    $( A relation-preserving function is a function.  (Contributed by Eric
       Schmidt, 11-Oct-2025.) $)
    relpf $p |- ( H RelPres R , S ( A , B ) -> H : A --> B ) $=
      ( vx vy wrelp wf cv wbr cfv wi wral df-relp simplbi ) ABCDEHABEIFJZGJZCKQ
      ELRELDKMGANFANFGABCDEOP $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x y R $.  $d x y S $.  $d x y H $.
    $d x y C $.  $d x y D $.
    $( A relation-preserving function preserves the relation.  (Contributed by
       Eric Schmidt, 11-Oct-2025.) $)
    relprel $p |- ( ( H RelPres R , S ( A , B ) /\ ( C e. A /\ D e. A ) ) ->
                 ( C R D -> ( H ` C ) S ( H ` D ) ) ) $=
      ( vx vy wrelp cv wbr cfv wi wral wcel wa wceq fveq2 imbi12d df-relp breq1
      wf simprbi breq1d breq2 breq2d rspc2v mpan9 ) ABEFGJZHKZIKZELZUKGMZULGMZF
      LZNZIAOHAOZCAPDAPQCDELZCGMZDGMZFLZNZUJABGUCURHIABEFGUAUDUQVCCULELZUTUOFLZ
      NHICDAAUKCRZUMVDUPVEUKCULEUBVFUNUTUOFUKCGSUETULDRZVDUSVEVBULDCEUFVGUOVAUT
      FULDGSUGTUHUI $.
  $}

  ${
    $d x A $.  $d x B $.  $d x R $.  $d x S $.  $d x H $.  $d x C $.  $d x D $.
    $( A preimage of a minimal element under a relation-preserving function is
       minimal.  Essentially one half of ~ isomin .  (Contributed by Eric
       Schmidt, 11-Oct-2025.) $)
    relpmin $p |- ( ( H RelPres R , S ( A , B ) /\ ( C C_ A /\ D e. A ) ) ->
               ( ( ( H " C ) i^i ( `' S " { ( H ` D ) } ) ) = (/) ->
               ( C i^i ( `' R " { D } ) ) = (/) ) ) $=
      ( vx wcel wa ccnv csn cima cin c0 wceq cfv wn wi wbr wrelp wss cv wex wfn
      neq0 relpf ffnd fnfvima 3expia adantrr sylan adantrd ssel wb vex eliniseg
      ad2antll relprel fvex ax-mp imbitrrdi sylbid exp32 syl9r com34 imp32 impd
      cvv jcad elin 3imtr4g n0i syl6 exlimdv biimtrid con4d ) ABEFGUAZCAUBZDAIZ
      JZJZCEKDLMZNZOPZGCMZFKDGQZLMZNZOPZWERHUCZWDIZHUDWBWJRZHWDUFWBWLWMHWBWLWKG
      QZWIIZWMWBWKCIZWKWCIZJZWNWFIZWNWHIZJWLWOWBWRWSWTWBWPWSWQVRGAUEZWAWPWSSZVR
      ABGABEFGUGUHXAVSXBVTXAVSWPWSACGWKUIUJUKULUMWBWPWQWTVRVSVTWPWQWTSZSVRVSWPV
      TXCVSWPWKAIZVRVTXCSCAWKUNVRXDVTXCVRXDVTJJZWQWKDETZWTVTWQXFUOVRXDEDWKAHUPU
      QURXEXFWNWGFTZWTABWKDEFGUSWGVIIWTXGUODGUTFWGWNVIWKGUTUQVAVBVCVDVEVFVGVHVJ
      WKCWCVKWNWFWHVKVLWIWNVMVNVOVPVQ $.
  $}

  ${
    $d w x y z A $.  $d w x y z B $.  $d w x y z H $.  $d w x y z ph $.
    $d w x y z R $.  $d w x y z S $.
    relpfrlem.1 $e |- ( ph -> H RelPres R , S ( A , B ) ) $.
    relpfrlem.2 $e |- ( ph -> ( H " x ) e. _V ) $.
    $( Lemma for ~ relpfr .  Proved without using the Axiom of Replacement.
       This is ~ isofrlem with weaker hypotheses.  (Contributed by Eric
       Schmidt, 11-Oct-2025.) $)
    relpfrlem $p |- ( ph -> ( S Fr B -> R Fr A ) ) $=
      ( vy vw vz cv c0 wa cima cin wceq wrex wi wfr wss wne csn wal wrelp relpf
      ccnv wf syl wfn ffn wel wex w3a cfv fnfvima ne0d exlimdv biimtrid expimpd
      3expia fimass jctild dffr3 cvv wcel sseq1 neeq1 anbi12d eqeq1d rexeqbi1dv
      n0 ineq1 imbi12d spcgv syl5d wfun adantr ffund fvelima syl2an sneq eqcoms
      simpl imaeq2d ineq2d biimpd imdistani relpmin sylan9r adantld exp42 com3l
      ssel imp com4t reximdvai mpd rexlimdvaa ex adantrd syld alrimdv imbitrrdi
      a2d ) ADFUAZBMZCUBZXHNUCZOZXHEUHJMZUDPQNRZJXHSZTZBUECEUAAXGXOBAXGXKGXHPZF
      UHZKMZUDZPZQZNRZKXPSZTXOAXKXPDUBZXPNUCZOZXGYCACDGUIZXKYFTACDEFGUFZYGHCDEF
      GUGUJZYGXKYEYDYGGCUKZXKYETCDGULYJXIXJYEXJJBUMZJUNYJXIOZYEJXHVMYLYKYEJYJXI
      YKYEYJXIYKUOXPXLGUPZCXHGXLUQURVBUSUTVAUJCDGXHVCVDUJXGLMZDUBZYNNUCZOZYNXTQ
      ZNRZKYNSZTZLUEZAYFYCTZLKDFVEAXPVFVGUUBUUCTIUUAUUCLXPVFYNXPRZYQYFYTYCUUDYO
      YDYPYEYNXPDVHYNXPNVIVJYSYBKYNXPUUDYRYANYNXPXTVNVKVLVOVPUJUTVQAXKYCXNAXIYC
      XNTZXJAXIUUEAXIOZYBXNKXPUUFXRXPVGZYBOZOZYMXRRZJXHSZXNUUFGVRUUGUUKUUHUUFCD
      GAYGXIYIVSVTUUGYBWEJXRXHGWAWBUUIUUJXMJXHUUFUUHYKUUJXMTTYKUUJUUFUUHXMUUFYK
      UUJUUHXMTZAXIYKUUJUULTTAXIYKUUJUULAXIYKOZOZUUJOYBXMUUGUUJYBXPXQYMUDZPZQZN
      RZUUNXMUUJYBUURUUJYAUUQNUUJXTUUPXPUUJXSUUOXQXSUUORXRYMXRYMWCWDWFWGVKWHAYH
      XIXLCVGZOUURXMTUUMHXIYKUUSXHCXLWOWICDXHXLEFGWJWBWKWLWMWPWNWQWPWRWSWTXAXBX
      FXCXDBJCEVEXE $.
    $( $j usage 'relpfrlem' avoids 'ax-rep'; $)
  $}

  ${
    $d x A $.  $d x B $.  $d x H $.  $d x R $.  $d x S $.  $d x V $.
    $( If the image of a set under a relation-preserving function is
       well-founded, so is the set.  See ~ isofr for a bidirectional statement.
       A more general version of Lemma I.9.9 of [Kunen2] p. 47.  (Contributed
       by Eric Schmidt, 11-Oct-2025.) $)
    relpfr $p |- ( H RelPres R , S ( A , B ) -> ( S Fr B -> R Fr A ) ) $=
      ( vx wrelp id wf wfun cv cima cvv wcel relpf ffun funimaex 3syl relpfrlem
      vex ) ABCDEGZFABCDEUAHUAABEIEJEFKZLMNABCDEOABEPEUBFTQRS $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Orbits
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Orbits exist.  Given a set ` A ` and a function ` F ` , the orbit of ` A `
     under ` F ` is the smallest set ` Z ` such that ` A e. Z ` and ` Z ` is
     closed under ` F ` .  (Contributed by Eric Schmidt, 6-Nov-2025.) $)
  orbitex $p |- ( rec ( F , A ) " _om ) e. _V $=
    ( crdg wfun com cima cvv wcel rdgfun omex funimaex ax-mp ) BACZDMEFGHABIMEJ
    KL $.

  $( A set is contained in its orbit.  (Contributed by Eric Schmidt,
     6-Nov-2025.) $)
  orbitinit $p |- ( A e. V -> A e. ( rec ( F , A ) " _om ) ) $=
    ( wcel crdg com cres crn cima cfv fr0g wfn frfnom peano1 fnfvelrn eqeltrrdi
    c0 mp2an df-ima eleqtrrdi ) ACDZABAEZFGZHZUBFIUAAQUCJZUDACBKUCFLQFDUEUDDABM
    NFQUCORPUBFST $.

  ${
    $d x A $.  $d x B $.  $d x F $.
    $( The orbit under a function is closed under the function.  (Contributed
       by Eric Schmidt, 6-Nov-2025.) $)
    orbitcl $p |- ( B e. ( rec ( F , A ) " _om ) ->
        ( F ` B ) e. ( rec ( F , A ) " _om ) ) $=
      ( vx crdg com cima wcel cfv cres crn cv wceq wrex wb frfnom fvelrnb ax-mp
      wfn csuc frsuc peano2 fnfvelrn sylancr eqeltrrd eleq1d syl5ibcom rexlimiv
      fveq2 sylbi df-ima eleq2s eleqtrrdi ) BCAEZFGZHBCIZUNFJZKZUOUPURHZBURUOBU
      RHZDLZUQIZBMZDFNZUSUQFSZUTVDOACPZDFBUQQRVCUSDFVAFHZVBCIZURHVCUSVGVATZUQIZ
      VHURAVACUAVGVEVIFHVJURHVFVAUBFVIUQUCUDUEVCVHUPURVBBCUIUFUGUHUJUNFUKZULVKU
      M $.
  $}

  ${
    orbitclmpt.1 $e |- F/_ x B $.
    orbitclmpt.2 $e |- F/_ x D $.
    orbitclmpt.3 $e |- Z = ( rec ( ( x e. _V |-> C ) , A ) " _om ) $.
    orbitclmpt.4 $e |- ( x = B -> C = D ) $.
    $( Version of ~ orbitcl using maps-to notation.  (Contributed by Eric
       Schmidt, 6-Nov-2025.) $)
    orbitclmpt $p |- ( ( B e. Z /\ D e. V ) -> D e. Z ) $=
      ( wcel wa cvv cmpt cfv wceq elex eqid eleq2i fvmptf crdg com cima orbitcl
      sylan 3imtr4i adantr eqeltrrd ) CGLZEFLZMCANDOZPZEGUJCNLUKUMEQCGRACDENULF
      HIKULSUAUFUJUMGLZUKCULBUBUCUDZLUMUOLUJUNBCULUEGUOCJTGUOUMJTUGUHUI $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Well-founded sets
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( The class of well-founded sets is transitive.  (Contributed by Eric
     Schmidt, 9-Sep-2025.) $)
  trwf $p |- Tr U. ( R1 " On ) $=
    ( vx cr1 con0 cima cuni wtr cv wss wral r1elssi rgen dftr3 mpbir ) BCDEZFAG
    ZNHZANIPANOJKANLM $.
    $( $j usage 'trwf' avoids 'ax-reg'; $)

  ${
    $d x y $.
    $( The rank function preserves ` e. ` .  (Contributed by Eric Schmidt,
       11-Oct-2025.) $)
    rankrelp $p |- rank RelPres _E , _E ( U. ( R1 " On ) , On ) $=
      ( vx vy cr1 con0 cima cuni cep crnk wrelp wf cv wbr cfv wi wral rankf wel
      wcel rankelb epel fvex epeli 3imtr4g rgen rgenw df-relp mpbir2an ) CDEFZD
      GGHIUHDHJAKZBKZGLZUIHMZUJHMZGLZNZBUHOZAUHOPUPAUHUOBUHUJUHRABQULUMRUKUNUIU
      JSBUITULUMUJHUAUBUCUDUEABUHDGGHUFUG $.
   $( $j usage 'rankrelp' avoids 'ax-reg'; $)
  $}

  $( The class of well-founded sets is well-founded.  Lemma I.9.24(2) of
     [Kunen2] p. 53.  (Contributed by Eric Schmidt, 11-Oct-2025.) $)
  wffr $p |- _E Fr U. ( R1 " On ) $=
    ( cr1 con0 cima cuni cep crnk wrelp wfr rankrelp onfr relpfr mp2 ) ABCDZBEE
    FGBEHMEHIJMBEEFKL $.
  $( $j usage 'wffr' avoids 'ax-reg'; $)

  ${
    $d y z A $.

    $( A transitive class well-founded by ` e. ` is a subclass of the class of
       well-founded sets.  Part of Lemma I.9.21 of [Kunen2] p. 53.
       (Contributed by Eric Schmidt, 26-Oct-2025.) $)
    trfr $p |- ( ( Tr A /\ _E Fr A ) -> A C_ U. ( R1 " On ) ) $=
      ( vy vz cep wfr wtr cr1 con0 cima cuni wss cv wcel wral wi wse epse dfss3
      r19.21v bitr4di cpred wa wb trpred raleq vex r1elss syl biimpd expcom a2d
      wceq biimtrid weq eleq1w imbi2d frins2 mpan2 sylib imbitrrdi impcom ) ADE
      ZAFZAGHIJZKZVBVCBLZVDMZBANZVEVBVCVGOZBANZVCVHOVBADPVJAQVIVCCLVDMZOZBCADVL
      CADVFUAZNVCVKCVMNZOVFAMZVIVCVKCVMSVOVCVNVGVCVOVNVGOVCVOUBZVNVGVPVMVFULZVN
      VGUCAVFUDVQVNVFVDKZVGVQVNVKCVFNVRVKCVMVFUECVFVDRTVFBUFUGTUHUIUJUKUMBCUNVG
      VKVCBCVDUOUPUQURVCVGBASUSBAVDRUTVA $.
    $( $j usage 'trfr' avoids 'ax-reg'; $)
  $}

  ${
    tcfr.1 $e |- A e. _V $.
    $( A set is well-founded if and only if its transitive closure is
       well-founded by ` e. ` .  This characterization of well-founded sets is
       that in Definition I.9.20 of [Kunen2] p. 53.  (Contributed by Eric
       Schmidt, 26-Oct-2025.) $)
    tcfr $p |- ( A e. U. ( R1 " On ) <-> _E Fr ( TC ` A ) ) $=
      ( cr1 con0 cima cuni wcel ctc cfv cep wfr wss tcwf r1elssi wffr frss 3syl
      mpi cvv tcid ax-mp wtr tctr trfr mpan sstrid r1elss sylibr impbii ) ACDEF
      ZGZAHIZJKZUKULUJGULUJLZUMAMULNUNUJJKUMOULUJJPRQUMAUJLUKUMAULUJASGAULLBAST
      UAULUBUMUNAUCULUDUEUFABUGUHUI $.
    $( $j usage 'tcfr' avoids 'ax-reg'; $)
  $}

  $( The Cartesian product of two well-founded sets is well-founded.
     (Contributed by Eric Schmidt, 12-Sep-2025.) $)
  xpwf $p |- ( ( A e. U. ( R1 " On ) /\ B e. U. ( R1 " On ) ) ->
      ( A X. B ) e. U. ( R1 " On ) ) $=
    ( cr1 con0 cima cuni wcel wa cun cpw cxp unwf pwwf 3bitri xpsspw sswf mpan2
    wss sylbi ) ACDEFZGBTGHZABIZJZJZTGZABKZTGZUAUBTGUCTGUEABLUBMUCMNUEUFUDRUGAB
    OUDUFPQS $.
  $( $j usage 'xpwf' avoids 'ax-reg'; $)

  $( The domain of a well-founded set is well-founded.  (Contributed by Eric
     Schmidt, 12-Sep-2025.) $)
  dmwf $p |- ( A e. U. ( R1 " On ) -> dom A e. U. ( R1 " On ) ) $=
    ( cr1 con0 cima cuni wcel cdm uniwf bitri wss crn cun ssun1 dmrnssfld sstri
    sswf mpan2 sylbi ) ABCDEZFZAEZEZSFZAGZSFZTUASFUCAHUAHIUCUDUBJUEUDUDAKZLUBUD
    UFMANOUBUDPQR $.
  $( $j usage 'dmwf' avoids 'ax-reg'; $)

  $( The range of a well-founded set is well-founded.  (Contributed by Eric
     Schmidt, 12-Sep-2025.) $)
  rnwf $p |- ( A e. U. ( R1 " On ) -> ran A e. U. ( R1 " On ) ) $=
    ( cr1 con0 cima cuni wcel crn uniwf bitri wss cdm cun ssun2 dmrnssfld sstri
    sswf mpan2 sylbi ) ABCDEZFZAEZEZSFZAGZSFZTUASFUCAHUAHIUCUDUBJUEUDAKZUDLUBUD
    UFMANOUBUDPQR $.
  $( $j usage 'rnwf' avoids 'ax-reg'; $)

  $( A relation is a well-founded set iff its domain and range are.
     (Contributed by Eric Schmidt, 29-Sep-2025.) $)
  relwf $p |- ( Rel R -> ( R e. U. ( R1 " On ) <->
      ( dom R e. U. ( R1 " On ) /\ ran R e. U. ( R1 " On ) ) ) ) $=
    ( wrel cr1 con0 cima cuni wcel cdm crn dmwf rnwf jca cxp xpwf wss relssdmrn
    wa sswf sylan2 expcom syl5 impbid2 ) ABZACDEFZGZAHZUDGZAIZUDGZQZUEUGUIAJAKL
    UJUFUHMZUDGZUCUEUFUHNULUCUEUCULAUKOUEAPUKARSTUAUB $.
  $( $j usage 'relwf' avoids 'ax-reg'; $)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Absoluteness in transitive models
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x M $.  $d x A $.
    $( Simplification of restricted quantification in a transitive class.  When
       ` ph ` is quantifier-free, this shows that the formula ` A. x e. y ph `
       is absolute for transitive models, which is a particular case of Lemma
       I.16.2 of [Kunen2] p. 95.  (Contributed by Eric Schmidt,
       19-Oct-2025.) $)
    ralabso $p |- ( ( Tr M /\ A e. M ) ->
        ( A. x e. A ph <-> A. x e. M ( x e. A -> ph ) ) ) $=
      ( wtr wcel wa wss wral cv wi wb trss imp ralss syl ) DEZCDFZGCDHZABCIBJCF
      AKBDILQRSDCMNABCDOP $.

    $( Simplification of restricted quantification in a transitive class.  When
       ` ph ` is quantifier-free, this shows that the formula ` E. x e. y ph `
       is absolute for transitive models, which is a particular case of Lemma
       I.16.2 of [Kunen2] p. 95.  (Contributed by Eric Schmidt,
       19-Oct-2025.) $)
    rexabso $p |- ( ( Tr M /\ A e. M ) ->
        ( E. x e. A ph <-> E. x e. M ( x e. A /\ ph ) ) ) $=
      ( wtr wcel wa wss wrex cv wb trss imp rexss syl ) DEZCDFZGCDHZABCIBJCFAGB
      DIKPQRDCLMABCDNO $.

    ${
      ralabsod.1 $e |- ( ph -> Tr M ) $.
      $( Deduction form of ~ ralabso .  (Contributed by Eric Schmidt,
         19-Oct-2025.) $)
      ralabsod $p |- ( ( ph /\ A e. M ) ->
        ( A. x e. A ps <-> A. x e. M ( x e. A -> ps ) ) ) $=
        ( wtr wcel wral cv wi wb ralabso sylan ) AEGDEHBCDICJDHBKCEILFBCDEMN $.

      $( Deduction form of ~ rexabso .  (Contributed by Eric Schmidt,
         19-Oct-2025.) $)
      rexabsod $p |- ( ( ph /\ A e. M ) ->
        ( E. x e. A ps <-> E. x e. M ( x e. A /\ ps ) ) ) $=
        ( wtr wcel wrex cv wa wb rexabso sylan ) AEGDEHBCDICJDHBKCEILFBCDEMN $.

      ${
        $d x ph $.
        ralabsobidv.2 $e |- ( ph -> ( ps <-> ch ) ) $.
        $( Formula-building lemma for proving absoluteness results.
           (Contributed by Eric Schmidt, 19-Oct-2025.) $)
        ralabsobidv $p |- ( ( ph /\ A e. M ) ->
             ( A. x e. A ps <-> A. x e. M ( x e. A -> ch ) ) ) $=
          ( wcel wa wral cv wi wb ralbidv adantr ralabsod bitrd ) AEFIZJBDEKZCD
          EKZDLEICMDFKATUANSABCDEHOPACDEFGQR $.

        $( Formula-building lemma for proving absoluteness results.
           (Contributed by Eric Schmidt, 19-Oct-2025.) $)
        rexabsobidv $p |- ( ( ph /\ A e. M ) ->
             ( E. x e. A ps <-> E. x e. M ( x e. A /\ ch ) ) ) $=
          ( wcel wa wrex cv wb rexbidv adantr rexabsod bitrd ) AEFIZJBDEKZCDEKZ
          DLEICJDFKASTMRABCDEHNOACDEFGPQ $.
      $}
    $}
  $}

  ${
    $d x M $.  $d x A $.  $d x B $.

    $( The notion " ` x ` is a subset of ` y ` " is absolute for transitive
       models.  Compare Example I.16.3 of [Kunen2] p. 96 and the following
       discussion.  (Contributed by Eric Schmidt, 19-Oct-2025.) $)
    ssabso $p |- ( ( Tr M /\ A e. M ) ->
        ( A C_ B <-> A. x e. M ( x e. A -> x e. B ) ) ) $=
      ( wss cv wcel wral wtr wa wi dfss3 ralabso bitrid ) BCEAFZCGZABHDIBDGJOBG
      PKADHABCLPABDMN $.

    $( Disjointness is absolute for transitive models.  Compare Example I.16.3
       of [Kunen2] p. 96 and the following discussion.  (Contributed by Eric
       Schmidt, 19-Oct-2025.) $)
    disjabso $p |- ( ( Tr M /\ A e. M ) ->
        ( ( A i^i B ) = (/) <-> A. x e. M ( x e. A -> -. x e. B ) ) ) $=
      ( cin c0 wceq cv wcel wn wral wtr wa wi disj ralabso bitrid ) BCEFGAHZCIJ
      ZABKDLBDIMRBISNADKABCOSABDPQ $.

    $( Nonemptiness is absolute for transitive models.  Compare Example I.16.3
       of [Kunen2] p. 96 and the following discussion.  (Contributed by Eric
       Schmidt, 19-Oct-2025.) $)
    n0abso $p |- ( ( Tr M /\ A e. M ) -> ( A =/= (/) <-> E. x e. M x e. A ) )
      $=
      ( wtr wcel wa wtru wrex cv c0 wne rexabso tru rext0 bicomi biantru rexbii
      3bitr4g ) CDBCEFGABHZAIBEZGFZACHBJKZTACHGABCLSUBGABMNOTUAACGTMPQR $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Lemmas for showing axioms hold in models
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x y z M $.

    $( A transitive class models the Axiom of Extensionality ~ ax-ext .  Lemma
       II.2.4(1) of [Kunen2] p. 111.  (Contributed by Eric Schmidt,
       11-Sep-2025.) $)
    traxext $p |- ( Tr M -> A. x e. M A. y e. M
        ( A. z e. M ( z e. x <-> z e. y ) -> x = y ) ) $=
      ( wtr wel wb wral weq wi cv wcel wa df-ral ancomsd expdimp adantrr adantr
      wal trel adantrl simpr pm5.21ndd alimdv biimtrid ax-ext syl6 ralrimivva
      ex ) DEZCAFZCBFZGZCDHZABIZJABDDUJAKZDLZBKZDLZMMZUNUMCSZUOUNCKZDLZUMJZCSUT
      VAUMCDNUTVDUMCUTVDUMUTVDMVCUKULUTUKVCJZVDUJUQVEUSUJUQUKVCUJUKUQVCDVBUPTOP
      QRUTULVCJZVDUJUSVFUQUJUSULVCUJULUSVCDVBURTOPUARUTVDUBUCUIUDUEABCUFUGUH $.
  $}

  ${
    modelaxreplem.1 $e |- ( ps -> x C_ M ) $.
    modelaxreplem.2 $e |- ( ps -> A. f ( ( Fun f /\ dom f e. M /\ ran f C_ M )
        -> ran f e. M ) ) $.
    modelaxreplem.3 $e |- ( ps -> (/) e. M ) $.
    modelaxreplem.4 $e |- ( ps -> x e. M ) $.

    ${
      $d f M $.  $d g x $.  $d A g $.  $d f g $.  $d g ps $.  $d g M $.
      modelaxreplem1.5 $e |- A C_ x $.
      $( Lemma for ~ modelaxrep .  We show that ` M ` is closed under taking
         subsets.  (Contributed by Eric Schmidt, 29-Sep-2025.) $)
      modelaxreplem1 $p |- ( ps -> A e. M ) $=
        ( vg wcel c0 wceq eleq1 syl5ibrcom cv wbr wss wa wne wfo wex csdm ssexi
        vex 0sdom cdom cvv ssdomg mp2 fodomr mpan2 wfn crn df-fo wfun cdm df-fn
        sylbir anim2d biimtrid sstrid sseq1 w3a df-3an wi wal funeq dmeq eleq1d
        weq rneq sseq1d 3anbi123d imbi12d spvv syl biimtrrid syl2and wb exlimdv
        adantl mpbidi syl5 pm2.61dne ) ACELZCMAWGCMNMELHCMEOPCMUAZBQZCKQZUBZKUC
        ZAWGWHMCUDRZWLCCWIBUFZJUEUGWMCWIUHRZWLWIUILCWISWOWNJCWIUIUJUKWICKULUMUT
        AWKWGKWKWJWIUNZWJUOZCNZTZAWGWICWJUPWSWQELZWGAAWPWJUQZWJURZELZTZWRWQESZW
        TWPXAXBWINZTAXDWJWIUSAXFXCXAAXCXFWIELIXBWIEOPVAVBAXEWRCESACWIEJFVCWQCEV
        DPXDXETXAXCXEVEZAWTXAXCXEVFADQZUQZXHURZELZXHUOZESZVEZXLELZVGZDVHXGWTVGZ
        GXPXQDKDKVLZXNXGXOWTXRXIXAXKXCXMXEXHWJVIXRXJXBEXHWJVJVKXRXLWQEXHWJVMZVN
        VOXRXLWQEXSVKVPVQVRVSVTWRWTWGWAWPWQCEOWCWDVBWBWEWF $.
    $}

    ${
      $d y z w M $.  $d f F $.  $d f M $.  $d x y z w $.
      modelaxreplem2.5 $e |- F/ w ps $.
      modelaxreplem2.6 $e |- F/ z ps $.
      modelaxreplem2.7 $e |- F/_ z F $.
      modelaxreplem2.8 $e |- F = { <. w , z >. | ( w e. x /\
        ( z e. M /\ A. y ph ) ) } $.
      modelaxreplem2.9 $e |- ( ps -> ( w e. M -> E. y e. M A. z e. M
        ( A. y ph -> z = y ) ) ) $.
      $( Lemma for ~ modelaxrep .  We define a class ` F ` and show that the
         antecedent of Replacement implies that ` F ` is a function.  We use
         Replacement (in the form of ~ funex ) to show that ` F ` exists.  Then
         we show that, under our hypotheses, the range of ` F ` is a member of
         ` M ` .  (Contributed by Eric Schmidt, 29-Sep-2025.) $)
      modelaxreplem2 $p |- ( ps -> ran F e. M ) $=
        ( wcel cv wfun cdm crn wss wel wal wa wmo sseld weq wral wrex wrmo nfa1
        rmo2i df-rmo sylib syl6 syld moanimv sylibr alrimi copab funeqi funopab
        wi bitri dmeqi dmopabss eqsstri modelaxreplem1 an12 opabbii eqtri rneqi
        rnopabss a1i cvv w3a funex wceq funeq dmeq eleq1d rneq sseq1d 3anbi123d
        syl2anc imbi12d spcgv sylc mp3and ) BHUAZHUBZISZHUCZIUDZWPISZBFCUEZETIS
        ZADUFZUGZUGZEUHZFUFZWMBXDFNBWSXBEUHZVFXDBWSFTZISZXFBCTZIXGJUIBXHXAEDUJV
        FEIUKDIULZXFRXJXAEIUMXFXAEDIADUNUOXAEIUPUQURUSWSXBEUTVAVBWMXCFEVCZUAXEH
        XKQVDXCFEVEVGVAZBCWNGIJKLMWNXKUBXIHXKQVHXBFEXIVIVJVKZWQBWPWTWSXAUGZUGZF
        EVCZUCIHXPHXKXPQXCXOFEWSWTXAVLVMVNVOXNFEIVPVJVQBHVRSZGTZUAZXRUBZISZXRUC
        ZIUDZVSZYBISZVFZGUFWMWOWQVSZWRVFZBWMWOXQXLXMIHVTWHKYFYHGHVRXRHWAZYDYGYE
        WRYIXSWMYAWOYCWQXRHWBYIXTWNIXRHWCWDYIYBWPIXRHWEZWFWGYIYBWPIYJWDWIWJWKWL
        $.

      $( Lemma for ~ modelaxrep .  We show that the consequent of Replacement
         is satisfied with ` ran F ` as the value of ` y ` .  (Contributed by
         Eric Schmidt, 29-Sep-2025.) $)
      modelaxreplem3 $p |- ( ps -> E. y e. M A. z e. M
          ( z e. y <-> E. w e. M ( w e. x /\ A. y ph ) ) ) $=
        ( wa wb wel wal wrex wral crn modelaxreplem2 wsbc cv wex sseld pm4.71rd
        wcel anbi1d an12 anass anbi2i bitri bitrdi exbid copab cab rneqi rnopab
        eqtri eqabri df-rex 19.42v bitr4i 3bitr4g baibd wnfc nfrn sbcralt mpan2
        ralrimia nfel1 sbcbig sbcel2gv nfcv nfv nfa1 nfrexw sbcgf bibi12d bitrd
        nfan ralbid syl mpbird rspesbcd ) BEDUAZFCUAZADUBZSZFIUCZTZEIUDZDHUEZIA
        BCDEFGHIJKLMNOPQRUFZBWQDWRUGZEUHZWRULZWOTZEIUDZBXCEIOBXBXAIULZWOBWLXEWM
        SZSZFUIZXEFUHZIULZWNSZSZFUIZXBXEWOSZBXGXLFNBXGXJWLSZXFSZXLBWLXOXFBWLXJB
        CUHIXIJUJUKUMXPXEXOWMSZSXLXOXEWMUNXQXKXEXJWLWMUOUPUQURUSXHEWRWRXGFEUTZU
        EXHEVAHXRQVBXGFEVCVDVEXNXEXKFUIZSXMWOXSXEWNFIVFUPXEXKFVGVHVIVJVOBWRIULZ
        WTXDTWSXTWTWPDWRUGZEIUDZXDXTEWRVKWTYBTEHPVLZWPDEWRIIVMVNXTYAXCEIEWRIYCV
        PXTYAWKDWRUGZWODWRUGZTXCWKWODWRIVQXTYDXBYEWODXAWRIVRWODWRIWNDFIDIVSWLWM
        DWLDVTADWAWFWBWCWDWEWGWEWHWIWJ $.
    $}

  $}

  ${
    $d x y z w g M $.  $d f g M $.  $d g ph $.
    modelaxrep.1 $e |- ( ps -> Tr M ) $.
    modelaxrep.2 $e |- ( ps -> A. f ( ( Fun f /\ dom f e. M /\ ran f C_ M )
        -> ran f e. M ) ) $.
    modelaxrep.3 $e |- ( ps -> (/) e. M ) $.
    $( Conditions which guarantee that a class models the Axiom of Replacement
       ~ ax-rep .  Similar to Lemma II.2.4(6) of [Kunen2] p. 111.  The first
       two hypotheses are those in Kunen.  The reason for the third hypothesis
       that our version of Replacement is different from Kunen's (which is
       ~ zfrep6 ).  If we assumed Regularity, we could eliminate this extra
       hypothesis, since under Regularity, the empty set is a member of every
       non-empty transitive class.

       Note that, to obtain the relativization of an instance of Replacement to
       ` M ` , the formula ` A. y ph ` would need to be replaced with
       ` A. y e. M ch ` , where ` ch ` is ` ph ` with all quantifiers
       relativized to ` M ` .  However, we can obtain this by using
       ` y e. M /\ ch ` for ` ph ` in this theorem, so it does establish that
       all instances of Replacement hold in ` M ` .  (Contributed by Eric
       Schmidt, 29-Sep-2025.) $)
    modelaxrep $p |- ( ps -> A. x e. M ( A. w e. M E. y e. M A. z e. M ( A. y
        ph -> z = y ) -> E. y e. M A. z e. M ( z e. y <-> E. w e. M ( w e. x
        /\ A. y ph ) ) ) ) $=
      ( vg cv wcel wss wi wal wral wrex wa wtr wfun cdm crn w3a c0 weq wb funeq
      wel dmeq eleq1d rneq sseq1d 3anbi123d imbi12d cbvalvw sylib trss ad5ant14
      copab imp simp-4r simpllr simplr nfv nfan nfcv nfrexw nfralw nfopab2 eqid
      nfra1 rsp adantl modelaxreplem3 ex ralrimiva syl21anc ) BHUAZLMZUBZWAUCZH
      NZWAUDZHOZUEZWEHNZPZLQZUFHNZADQZEDUGPZEHRZDHSZFHRZEDUJFCUJZWLTFHSUHEHRDHS
      ZPZCHRIBGMZUBZWTUCZHNZWTUDZHOZUEZXDHNZPZGQWJJXHWIGLGLUGZXFWGXGWHXIXAWBXCW
      DXEWFWTWAUIXIXBWCHWTWAUKULXIXDWEHWTWAUMZUNUOXIXDWEHXJULUPUQURKVTWJTZWKTZW
      SCHXLCMZHNZTZWPWRAXOWPTCDEFLWQEMHNWLTTZFEVAZHVTXNXMHOZWJWKWPVTXNXRHXMUSVB
      UTVTWJWKXNWPVCXKWKXNWPVDXLXNWPVEXOWPFXOFVFWOFHVMVGXOWPEXOEVFWOEFHEHVHZWNE
      DHXSWMEHVMVIVJVGXPFEVKXQVLWPFMHNWOPXOWOFHVNVOVPVQVRVS $.
  $}

  ${
    $d x y z $.  $d ph y z $.  $d y M $.

    $( A class that is closed under subsets models the Axiom of Separation
       ~ ax-sep .  Lemma II.2.4(3) of [Kunen2] p. 111.

       Note that, to obtain the relativization of an instance of Separation to
       ` M ` , the formula ` ph ` would need to be replaced with its
       relativization to ` M ` .  However, this new formula is a valid
       substitution for ` ph ` , so this theorem does establish that all
       instances of Separation hold in ` M ` .  (Contributed by Eric Schmidt,
       29-Sep-2025.) $)
    ssclaxsep $p |- ( A. z e. M ~P z C_ M -> A. z e. M E. y e. M A. x e. M
        ( x e. y <-> ( x e. z /\ ph ) ) ) $=
      ( cv cpw wss wel wa wb wral wrex wcel wex wal ax-sep wi biimp simpl alimi
      syl6 velpw df-ss bitr2i sylib ssel syl5 alral eximdv df-rex sylibr ralimi
      jca2 mpi ) DFZGZEHZBCIZBDIZAJZKZBELZCEMZDEURCFZENZVCJZCOZVDURVBBPZCOVHABC
      DQURVIVGCURVIVFVCVIVEUQNZURVFVIUSUTRZBPZVJVBVKBVBUSVAUTUSVASUTATUBUAVJVEU
      PHVLCUPUCBVEUPUDUEUFUQEVEUGUHVBBEUIUNUJUOVCCEUKULUM $.
  $}

  ${
    $d x y $.  $d x M $.
    $( A class that contains the empty set models the Null Set Axiom ~ ax-nul .
       (Contributed by Eric Schmidt, 19-Oct-2025.) $)
    0elaxnul $p |- ( (/) e. M -> E. x e. M A. y e. M -. y e. x ) $=
      ( c0 wcel cv wn wral wel wrex noel rgenw wceq eleq2 notbid ralbidv rspcev
      mpan2 ) DCEBFZDEZGZBCHZBAIZGZBCHZACJUABCSKLUEUBADCAFZDMZUDUABCUGUCTUFDSNO
      PQR $.
  $}

  ${
    $d x y z w M $.

    $( Suppose ` M ` is a transitive class that is closed under power sets
       intersected with ` M ` .  Then, ` M ` models the Axiom of Power Sets
       ~ ax-pow .  One direction of Lemma II.2.8 of [Kunen2] p. 113.
       (Contributed by Eric Schmidt, 19-Oct-2025.) $)
    pwclaxpow $p |- ( ( Tr M /\ A. x e. M ( ~P x i^i M ) e. M ) ->
         A. x e. M E. y e. M A. z e. M ( A. w e. M ( w e. z -> w e. x )
         -> z e. y ) ) $=
      ( wtr cv cpw cin wcel wral wel wi wrex wa wss velpw ssabso bitrid elin
      simplbi2com adantl sylbird wceq eleq2 imbi2d ralbidv rspcev sylan2 expcom
      ralrimiva ralimdv imp ) EFZAGZHZEIZEJZAEKDCLDALMDEKZCBLZMZCEKZBENZAEKUNUR
      VCAEURUNVCUNURUSCGZUQJZMZCEKZVCUNVFCEUNVDEJZOZUSVDUPJZVEVJVDUOPVIUSCUOQDV
      DUOERSVHVJVEMUNVEVJVHVDUPETUAUBUCUKVBVGBUQEBGZUQUDZVAVFCEVLUTVEUSVKUQVDUE
      UFUGUHUIUJULUM $.
  $}

  ${
    $d x z w $.  $d y z w $.  $d z M $.

    $( A class that is closed under the pairing operation models the Axiom of
       Pairing ~ ax-pr .  Lemma II.2.4(4) of [Kunen2] p. 111.  (Contributed by
       Eric Schmidt, 29-Sep-2025.) $)
    prclaxpr $p |- ( A. x e. M A. y e. M { x , y } e. M ->
        A. x e. M A. y e. M E. z e. M A. w e. M
        ( ( w = x \/ w = y ) -> w e. z ) ) $=
      ( cv cpr wcel weq wo wel wi wral wrex vex elpr biimpri rgenw wceq eleq2
      imbi2d ralbidv rspcev mpan2 2ralimi ) AFZBFZGZEHZDAIDBIJZDCKZLZDEMZCENZAB
      EEUIUJDFZUHHZLZDEMZUNUQDEUPUJUOUFUGDOPQRUMURCUHECFZUHSZULUQDEUTUKUPUJUSUH
      UOTUAUBUCUDUE $.
  $}

  ${
    $d x w y z $.  $d y M $.

    $( A class that is closed under the union operation models the Axiom of
       Union ~ ax-un .  Lemma II.2.4(5) of [Kunen2] p. 111.  (Contributed by
       Eric Schmidt, 1-Oct-2025.) $)
    uniclaxun $p |- ( A. x e. M U. x e. M ->
        A. x e. M E. y e. M A. z e. M
        ( E. w e. M ( z e. w /\ w e. x ) -> z e. y ) ) $=
      ( cv cuni wcel wel wa wrex wral wex rexex eluni sylibr rgenw wceq eleq2
      wi imbi2d ralbidv rspcev mpan2 ralimi ) AFZGZEHZCDIDAIJZDEKZCBIZTZCELZBEK
      ZAEUHUJCFZUGHZTZCELZUNUQCEUJUIDMUPUIDENDUOUFOPQUMURBUGEBFZUGRZULUQCEUTUKU
      PUJUSUGUOSUAUBUCUDUE $.
  $}

  ${
    $d x y z M $.

    $( A subclass of the class of well-founded sets models the Axiom of
       Regularity ~ ax-reg .  Lemma II.2.4(2) of [Kunen2] p. 111.  (Contributed
       by Eric Schmidt, 19-Oct-2025.) $)
    sswfaxreg $p |- ( M C_ U. ( R1 " On ) -> A. x e. M ( E. y e. M y e. x ->
      E. y e. M ( y e. x /\ A. z e. M ( z e. y -> -. z e. x ) ) ) ) $=
      ( cr1 con0 cima cuni wss wel wrex wn wi wral wa cv cin cep cvv bitri inn0
      c0 wne wbr ssinss1 wcel wfr vex inex2 wffr mpanl12 sylan ralin con2b epel
      fri imbi1i ralbii rexbii rexin sylib sylan2br ex ralrimivw ) DEFGHZIZBAJZ
      BDKZVGCBJZCAJZLZMZCDNZOBDKZMADVFVHVNVHVFDAPZQZUBUCZVNBDVOUAVFVQOCPZBPRUDZ
      LZCVPNZBVPKZVNVFVPVEIZVQWBDVOVEUEVPSUFVERUGWCVQOWBVODAUHUIUJBCVEVPSRUPUKU
      LWBVMBVPKVNWAVMBVPWAVJVTMZCDNVMVTCDVOUMWDVLCDWDVSVKMVLVJVSUNVSVIVKBVRUOUQ
      TURTUSVMBDVOUTTVAVBVCVD $.
    $( $j usage 'sswfaxreg' avoids 'ax-reg'; $)
  $}

  ${
    $d x y z w $.  $d x y z M $.
    $( A class that contains all ordinals up to and including ` _om ` models
       the Axiom of Infinity ~ ax-inf2 .  The antecedent of this theorem is not
       enough to guarantee that the class models the alternate axiom ~ ax-inf .
       (Contributed by Eric Schmidt, 19-Oct-2025.) $)
    omssaxinf2 $p |- ( ( _om C_ M /\ _om e. M ) -> E. x e. M ( E. y e. M
        ( y e. x /\ A. z e. M -. z e. y )
        /\ A. y e. M ( y e. x -> E. z e. M
        ( z e. x /\ A. w e. M ( w e. z <-> ( w e. y \/ w = y ) ) ) ) ) ) $=
      ( com wcel wel wn wral wa wrex wi cv c0 wceq eleq2 ralbidv anbi12d rspcev
      wss weq wo wb peano1 ssel mpi noel rgenw eleq1 notbid mpanr12 csuc peano2
      syl impel adantl vex elsuc bibi1d mpanr2 syl2anc ralrimivw anbi1d rexbidv
      ex imbi12d expcom imp ) FEUAZFEGZBAHZCBHZIZCEJZKZBELZVLCAHZDCHZDBHDBUBUCZ
      UDZDEJZKZCELZMZBEJZKZAELZVJBNZFGZVOKZBELZWJCNZFGZWBKZCELZMZBEJZVKWHMVJOEG
      ZWLVJOFGZWSUEFEOUFUGWSWTWMOGZIZCEJZWLUEXBCEWMUHUIWKWTXCKBOEWIOPZWJWTVOXCW
      IOFUJXDVNXBCEXDVMXAWIOWMQUKRSTULUOVJWQBEVJWJWPVJWJKWIUMZEGZXEFGZWPVJXGXFW
      JFEXEUFWIUNZUPWJXGVJXHUQXFXGDNZXEGZVTUDZDEJZWPXKDEXIWIDURUSUIWOXGXLKCXEEW
      MXEPZWNXGWBXLWMXEFUJXMWAXKDEXMVSXJVTWMXEXIQUTRSTVAVBVFVCVKWLWRKZWHWGXNAFE
      ANZFPZVQWLWFWRXPVPWKBEXPVLWJVOXOFWIQZVDVEXPWEWQBEXPVLWJWDWPXQXPWCWOCEXPVR
      WNWBXOFWMQVDVEVGRSTVHVBVI $.

    $( A transitive class that contains ` _om ` models the Axiom of Infinity
       ~ ax-inf2 .  Lemma II.2.11(7) of [Kunen2] p. 114.  Kunen has the
       additional hypotheses that the Extensionality, Separation, Pairing, and
       Union axioms are true in ` M ` .  This, apparently, is because Kunen's
       statement of the Axiom of Infinity uses the defined notions ` (/) ` and
       ` suc ` , and these axioms guarantee that these notions are
       well-defined.  When we state the axiom using primitives only, the need
       for these hypotheses disappears.

       The antecedent of this theorem is not enough to guarantee that the class
       models the alternate axiom ~ ax-inf .  (Contributed by Eric Schmidt,
       19-Oct-2025.) $)
    omelaxinf2 $p |- ( ( Tr M /\ _om e. M ) -> E. x e. M ( E. y e. M
        ( y e. x /\ A. z e. M -. z e. y )
        /\ A. y e. M ( y e. x -> E. z e. M
        ( z e. x /\ A. w e. M ( w e. z <-> ( w e. y \/ w = y ) ) ) ) ) ) $=
      ( wtr com wcel wss wel wn wral wa wrex weq wo wb wi trss imp omssaxinf2
      sylancom ) EFZGEHZGEIZBAJZCBJKCELMBENUFCAJDCJDBJDBOPQDELMCENRBELMAENUCUDU
      EEGSTABCDEUAUB $.
  $}

  ${
    $d x z y w v $.

    $( ~ dfac5 expanded into primitives.  (Contributed by Eric Schmidt,
       19-Oct-2025.) $)
    dfac5prim $p |- ( CHOICE <-> A. x ( ( A. z ( z e. x -> E. w w e. z ) /\
        A. z A. w ( ( z e. x /\ w e. x ) -> ( -. z = w -> A. y ( y e. z -> -.
        y e. w ) ) ) ) -> E. y A. z ( z e. x -> E. w A. v
        ( ( v e. z /\ v e. y ) <-> v = w ) ) ) ) $=
      ( cv c0 wne wral cin wi wa weu wex wal wel weq wn ralbii bitri wceq dfac5
      wac wcel wb n0 df-ral df-ne disj1 imbi12i 2ralbii r2al anbi12i elin eubii
      eu6 exbii albii ) UCCFZGHZCAFZIZUSDFZHZUSVCJGUAZKZDVAICVAIZLZEFZUSBFZJUDZ
      EMZCVAIZBNZKZAOCAPZDCPDNZKCOZVPDAPLCDQRZBCPBDPRKBOZKZKDOCOZLZVPECPEBPLZED
      QUEEODNZKCOZBNZKZAOABCDEUBVOWHAVHWCVNWGVBVRVGWBVBVQCVAIVRUTVQCVADUSUFSVQC
      VAUGTVGWADVAICVAIWBVFWACDVAVAVDVSVEVTUSVCUHBUSVCUIUJUKWACDVAVAULTUMVMWFBV
      MWECVAIWFVLWECVAVLWDEMWEVKWDEVIUSVJUNUOWDEDUPTSWECVAUGTUQUJURT $.
    $( $j usage 'dfac5prim' avoids 'ax-ac' 'ax-ac2'; $)

    $( ~ ac8 expanded into primitives.  (Contributed by Eric Schmidt,
       19-Oct-2025.) $)
    ac8prim $p |- ( ( A. z ( z e. x -> E. w w e. z ) /\ A. z A. w ( ( z e. x /\
        w e. x ) -> ( -. z = w -> A. y ( y e. z -> -. y e. w ) ) ) ) ->
        E. y A. z ( z e. x -> E. w A. v ( ( v e. z /\ v e. y ) <-> v = w ) ) )
      $=
      ( wel wex wi wal wa weq wn wb dfac5prim axaci ) CAFZDCFDGHCIPDAFJCDKLBCFB
      DFLHBIHHDICIJPECFEBFJEDKMEIDGHCIBGHAABCDENO $.

  $}

  ${
    $d x z y w v M $.

    $( If ` M ` is a transitive class, then the following are equivalent.  (1)
       Every nonempty set ` x e. M ` of pairwise disjoint nonempty sets has a
       choice set in ` M ` .  (2) The class ` M ` models the Axiom of Choice,
       in the form ~ ac8prim .

       Lemma II.2.11(7) of [Kunen2] p. 114.  Kunen has the additional
       hypotheses that the Extensionality, Separation, Pairing, and Union
       axioms are true in ` M ` .  This, apparently, is because Kunen's
       statement of the Axiom of Choice uses defined notions, including ` (/) `
       and ` i^i ` , and these axioms guarantee that these notions are
       well-defined.  When we state the axiom using primitives only, the need
       for these hypotheses disappears.  (Contributed by Eric Schmidt,
       19-Oct-2025.) $)
    modelac8prim $p |- ( Tr M -> ( A. x e. M ( ( A. z e. x z
            =/= (/) /\ A. z e. x A. w e. x ( z =/= w -> ( z i^i w ) = (/) ) )
            -> E. y e. M A. z e. x E! v v e. ( z i^i y ) ) <-> A. x e. M ( (
            A. z e. M ( z e. x -> E. w e. M w e. z ) /\ A. z e. M A. w e. M
            ( ( z e. x /\ w e. x ) -> ( -. z = w -> A. y e. M ( y e. z -> -.
            y e. w ) ) ) ) -> E. y e. M A. z e. M ( z e. x -> E. w e. M
            A. v e. M ( ( v e. z /\ v e. y ) <-> v = w ) ) ) ) )
      $=
      ( cv c0 wne wral cin wi wa wcel weu wrex wel wb imbi2d ralbidva wn n0abso
      wtr wceq weq ralabso adantlr bitrd simpl ralabsobidv anabss3 impexp df-ne
      r19.21v imbi1i bitrid bitr3id ralbidv adantr anbi12d wreu elin eubii trel
      disjabso imp anass1rs adantrl reueubd bitr4id reu6 an32s rexbidva imbi12d
      bitrdi ) FUCZCGZHIZCAGZJZVQDGZIZVQWAKHUDZLZDVSJZCVSJZMZEGZVQBGZKNZEOZCVSJ
      ZBFPZLCAQZDCQDFPZLZCFJZWNDAQZMZCDUEUAZBCQBDQUALBFJZLZLZDFJZCFJZMZWNECQZEB
      QZMZEDUEREFJDFPZLCFJZBFPZLAFVPVSFNZMZWGXFWMXLXNVTWQWFXEXNVTWNVRLZCFJWQVRC
      VSFUFXNXOWPCFXNVQFNZMVRWOWNVPXPVRWORXMDVQFUBUGSTUHXNWFWNWRWDLZDFJZLZCFJZX
      EVPXMWFXTRXNWEXRCVSFVPXMUIWDDVSFUFUJUKVPXTXERXMVPXSXDCFXSWNXQLZDFJVPXPMZX
      DWNXQDFUNYBYAXCDFYAWSWDLYBXCWNWRWDULYBWDXBWSWDWTWCLYBXBWBWTWCVQWAUMUOYBWC
      XAWTBVQWAFVESUPSUQURUQTUSUHUTXNWLXKBFVPWIFNZXMWLXKRVPYCMZWKXJCVSFVPYCUIYD
      WKXIEFVAZXJYDWKXIEOYEWJXIEWHVQWIVBVCYDXIEFYDXHWHFNZXGVPXHYCYFVPXHYCMYFFWH
      WIVDVFVGVHVIVJXIEDFVKVOUJVLVMVNT $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  The class of well-founded sets is a model for ZFC
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    wfax.1 $e |- W = U. ( R1 " On ) $.

    ${
      $d x y z W $.

      $( The class of well-founded sets models the Axiom of Extensionality
         ~ ax-ext .  Part of Corollary II.2.5 of [Kunen2] p. 112.

         This is the first of a series of theorems showing that all the axioms
         of ZFC hold in the class of well-founded sets, which we here denote by
         ` W ` .  More precisely, for each axiom of ZFC, we obtain a provable
         statement if we restrict all quantifiers to ` W ` (including implicit
         universal quantifiers on free variables).

         None of these proofs use the Axiom of Regularity.  In particular, the
         Axiom of Regularity itself is proved to hold in ` W ` without using
         Regularity.  Further, the Axiom of Choice is used only in the proof
         that Choice holds in ` W ` .  This has the consequence that any
         theorem of ZF (possibly proved using Regularity) can be proved,
         without using Regularity, to hold in ` W ` .  This gives us a relative
         consistency result:  If ZF without Regularity is consistent, so is ZF
         itself.  Similarly, if ZFC without Regularity is consistent, so is ZFC
         itself.  These consistency results are metatheorems and are part of
         Theorem II.2.13 of [Kunen2] p. 114.

         (Contributed by Eric Schmidt, 11-Sep-2025.)  (Revised by Eric Schmidt,
         29-Sep-2025.) $)
      wfaxext $p |- A. x e. W A. y e. W
          ( A. z e. W ( z e. x <-> z e. y ) -> x = y ) $=
        ( wtr wel wb wral weq wi cr1 con0 cima cuni trwf wceq treq ax-mp mpbir
        traxext ) DFZCAGCBGHCDIABJKBDIADIUBLMNOZFZPDUCQUBUDHEDUCRSTABCDUAS $.
      $( $j usage 'wfaxext' avoids 'ax-reg' 'ax-ac' 'ax-ac2'; $)
    $}

    ${
      $d x y z w W $.  $d f W $.

      $( The class of well-founded sets models the Axiom of Replacement
         ~ ax-rep .  Actually, our statement is stronger, since it is an
         instance of Replacement only when all quantifiers in ` A. y ph ` are
         relativized to ` W ` .  Essentially part of Corollary II.2.5 of
         [Kunen2] p. 112, but note that our Replacement is different from
         Kunen's.  (Contributed by Eric Schmidt, 29-Sep-2025.) $)
      wfaxrep $p |- A. x e. W ( A. w e. W E. y e. W A. z e. W ( A. y
          ph -> z = y ) -> E. y e. W A. z e. W ( z e. y <-> E. w e. W ( w e. x
          /\ A. y ph ) ) ) $=
        ( vf cr1 con0 wal wi wral wrex wel wtr mpbiri wcel wss c0 cima cuni weq
        wceq wa wb trwf treq cv wfun cdm crn w3a vex rnex r1elss biimpri sseq2i
        eleq2i 3imtr4i 3ad2ant3 ax-gen onwf 0elon sselii eleq2 modelaxrep ax-mp
        a1i ) FIJUAUBZUDZACKZDCUCLDFMCFNEFMDCOEBOVLUEEFNUFDFMCFNLBFMGAVKBCDEHFV
        KFPVJPUGFVJUHQHUIZUJZVMUKFRZVMULZFSZUMVPFRZLZHKVKVSHVQVNVRVOVPVJSZVPVJR
        ZVQVRWAVTVPVMHUNUOUPUQFVJVPGURFVJVPGUSUTVAVBVIVKTFRTVJRJVJTVCVDVEFVJTVF
        QVGVH $.
      $( $j usage 'wfaxrep' avoids 'ax-reg' 'ax-ac' 'ax-ac2'; $)
    $}

    ${
      $d x y z $.  $d ph y z $.  $d y W $.

      $( The class of well-founded sets models the Axiom of Separation
         ~ ax-sep .  Actually, our statement is stronger, since it is an
         instance of Separation only when all quantifiers in ` ph ` are
         relativized to ` W ` .  Part of Corollary II.2.5 of [Kunen2] p. 112.
         (Contributed by Eric Schmidt, 29-Sep-2025.) $)
      wfaxsep $p |- A. z e. W E. y e. W A. x e. W
          ( x e. y <-> ( x e. z /\ ph ) ) $=
        ( cv cpw wss wel wa wb wral wrex ssclaxsep cr1 con0 cima cuni wcel pwwf
        r1elssi sylbi eleq2i sseq2i 3imtr4i mprg ) DGZHZEIZBCJBDJAKLBEMCENDEMDE
        ABCDEOUHPQRSZTZUIUKIZUHETUJULUIUKTUMUHUAUIUBUCEUKUHFUDEUKUIFUEUFUG $.
      $( $j usage 'wfaxsep' avoids 'ax-reg' 'ax-ac' 'ax-ac2'; $)
    $}

    ${
      $d x y $.  $d x W $.
      $( The class of well-founded sets models the Null Set Axiom ~ ax-nul .
         (Contributed by Eric Schmidt, 19-Oct-2025.) $)
      wfaxnul $p |- E. x e. W A. y e. W -. y e. x $=
        ( c0 wcel wel wral wrex cr1 con0 cima cuni onwf 0elon eleqtrri 0elaxnul
        wn sselii ax-mp ) ECFBAGRBCHACIEJKLMZCKUAENOSDPABCQT $.
      $( $j usage 'wfaxnul' avoids 'ax-reg' 'ax-ac' 'ax-ac2'; $)
    $}

    ${
      $d x y z w W $.
      $( The class of well-founded sets models the Axioms of Power Sets.  Part
         of Corollary II.2.9 of [Kunen2] p. 113.  (Contributed by Eric Schmidt,
         19-Oct-2025.) $)
      wfaxpow $p |-
         A. x e. W E. y e. W A. z e. W
         ( A. w e. W ( w e. z -> w e. x ) -> z e. y ) $=
        ( cv cpw cin wcel wel wi wral wrex wtr cr1 con0 cima wceq wb cuni ax-mp
        trwf treq mpbir pwclaxpow mpan pwwf biimpi wss r1elssi dfss2 eleq1 3syl
        sylbi mpbird eleq2i ineq2i eleq12i 3imtr4i mprg ) AGZHZEIZEJZDCKDAKLDEM
        CBKLCEMBENAEMZAEEOZVEAEMVFVGPQRUAZOZUCEVHSVGVITFEVHUDUBUEABCDEUFUGVBVHJ
        ZVCVHIZVHJZVBEJVEVJVLVCVHJZVJVMVBUHUIZVJVMVCVHUJZVLVMTZVNVCUKVOVKVCSVPV
        CVHULVKVCVHUMUOUNUPEVHVBFUQVDVKEVHEVHVCFURFUSUTVA $.
      $( $j usage 'wfaxpow' avoids 'ax-reg' 'ax-ac' 'ax-ac2'; $)
    $}

    ${
      $d x y z w $.  $d y z W $.

      $( The class of well-founded sets models the Axiom of Pairing ~ ax-pr .
         Part of Corollary II.2.5 of [Kunen2] p. 112.  (Contributed by Eric
         Schmidt, 29-Sep-2025.) $)
      wfaxpr $p |- A. x e. W A. y e. W E. z e. W A. w e. W
          ( ( w = x \/ w = y ) -> w e. z ) $=
        ( cv cpr wcel wral weq wo wel wi wrex cr1 con0 cima wa eleq2i cuni prwf
        anbi12i 3imtr4i rgen2 prclaxpr ax-mp ) AGZBGZHZEIZBEJAEJDAKDBKLDCMNDEJC
        EOBEJAEJUKABEEUHPQRUAZIZUIULIZSUJULIUHEIZUIEIZSUKUHUIUBUOUMUPUNEULUHFTE
        ULUIFTUCEULUJFTUDUEABCDEUFUG $.
      $( $j usage 'wfaxpr' avoids 'ax-reg' 'ax-ac' 'ax-ac2'; $)
    $}

    ${
      $d x w y z $.  $d y W $.

      $( The class of well-founded sets models the Axiom of Union ~ ax-un .
         Part of Corollary II.2.5 of [Kunen2] p. 112.  (Contributed by Eric
         Schmidt, 19-Oct-2025.) $)
      wfaxun $p |- A. x e. W E. y e. W A. z e. W
          ( E. w e. W ( z e. w /\ w e. x ) -> z e. y ) $=
        ( cv cuni wcel wel wa wrex wi wral uniclaxun cr1 con0 cima uniwf eleq2i
        3bitr4i biimpi mprg ) AGZHZEIZCDJDAJKDELCBJMCENBELAENAEABCDEOUDEIZUFUDP
        QRHZIUEUHIUGUFUDSEUHUDFTEUHUEFTUAUBUC $.
      $( $j usage 'wfaxun' avoids 'ax-reg' 'ax-ac' 'ax-ac2'; $)
    $}

    ${
      $d x y z W $.

      $( The class of well-founded sets models the Axiom of Regularity
         ~ ax-reg .  Part of Corollary II.2.5 of [Kunen2] p. 112.  (Contributed
         by Eric Schmidt, 19-Oct-2025.) $)
      wfaxreg $p |- A. x e. W ( E. y e. W y e. x -> E. y e. W
      ( y e. x /\ A. z e. W ( z e. y -> -. z e. x ) ) ) $=
        ( cr1 con0 cima cuni wss wel wrex wn wi wral wa eqimssi sswfaxreg ax-mp
        ) DFGHIZJBAKZBDLUACBKCAKMNCDOPBDLNADODTEQABCDRS $.
      $( $j usage 'wfaxreg' avoids 'ax-reg' 'ax-ac' 'ax-ac2'; $)
    $}

    ${
      $d x y z w $.  $d x y z W $.
      $( The class of well-founded sets models the Axiom of Infinity
         ~ ax-inf2 .  Part of Corollary II.2.12 of [Kunen2] p. 114.
         (Contributed by Eric Schmidt, 19-Oct-2025.) $)
      wfaxinf2 $p |- E. x e. W ( E. y e. W ( y e. x /\ A. z e. W -. z e. y )
        /\ A. y e. W ( y e. x -> E. z e. W
        ( z e. x /\ A. w e. W ( w e. z <-> ( w e. y \/ w = y ) ) ) ) ) $=
        ( wtr com wcel wel wn wral wa wrex weq wo wb wi cr1 con0 cima cuni trwf
        wceq treq ax-mp mpbir onwf omelon sselii eleqtrri omelaxinf2 mp2an ) EG
        ZHEIBAJZCBJKCELMBENUOCAJDCJDBJDBOPQDELMCENRBELMAENUNSTUAUBZGZUCEUPUDUNU
        QQFEUPUEUFUGHUPETUPHUHUIUJFUKABCDEULUM $.
      $( $j usage 'wfaxinf2' avoids 'ax-reg' 'ax-ac' 'ax-ac2'; $)
    $}

    ${
      $d x y z w v t W $.

      $( The class of well-founded sets ` W ` models the Axiom of Choice.
         Since the previous theorems show that all the ZF axioms hold in
         ` W ` , we may use any statement that ZF proves is equivalent to
         Choice to prove this.  We use ~ ac8prim .  Part of Corollary II.2.12
         of [Kunen2] p. 114.  (Contributed by Eric Schmidt, 19-Oct-2025.) $)
      wfac8prim $p |- A. x e. W ( ( A. z e. W ( z e. x -> E. w e. W w e. z )
          /\ A. z e. W A. w e. W ( ( z e. x /\ w e. x ) -> ( -. z = w ->
          A. y e. W ( y e. z -> -. y e. w ) ) ) ) -> E. y e. W A. z e. W
          ( z e. x -> E. w e. W A. v e. W ( ( v e. z /\ v e. y ) <->
          v = w ) ) ) $=
        ( vt wtr wel wrex wi wral wa weq wceq cv cin wcel weu wn con0 cima cuni
        wb cr1 trwf treq ax-mp mpbir c0 wne wex ac8 uniwf wss inss2 mpan2 sylbi
        sswf eleq2i 3imtr4i inss1 elssuni sstrid dfss sylib inass eqtrdi eleq2d
        eubidv ralbiia ineq2 ralbidv sylan2b sylan ex exlimdv syl5 modelac8prim
        rspcev rgen mpbii ) FIZCAJZDCJDFKLCFMWEDAJNCDOUABCJBDJUALBFMLLDFMCFMNWE
        ECJEBJNEDOUEEFMDFKLCFMBFKLAFMZWDUFUBUCUDZIZUGFWGPWDWHUEGFWGUHUIUJWDCQZU
        KULCAQZMWIDQZULWIWKRUKPLDWJMCWJMNZEQZWIBQZRZSZETZCWJMZBFKZLZAFMWFWTAFWL
        WMWIHQZRZSZETZCWJMZHUMWJFSZWSAHCDEUNXFXEWSHXFXEWSXFXAWJUDZRZFSZXEWSWJWG
        SZXHWGSZXFXIXJXGWGSZXKWJUOXLXHXGUPXKXAXGUQXGXHUTURUSFWGWJGVAFWGXHGVAVBX
        EXIWMWIXHRZSZETZCWJMZWSXDXOCWJWEXCXNEWEXBXMWMWEXBXBXGRZXMWEXBXGUPXBXQPW
        EXBWIXGWIXAVCWIWJVDVEXBXGVFVGWIXAXGVHVIVJVKVLWRXPBXHFWNXHPZWQXOCWJXRWPX
        NEXRWOXMWMWNXHWIVMVJVKVNWAVOVPVQVRVSWBABCDEFVTWCUI $.
      $( $j usage 'wfac8prim' avoids 'ax-reg' 'ax-ac'; $)
    $}

  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Permutation models
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    permmodel.1 $e |- F : _V -1-1-onto-> _V $.
    permmodel.2 $e |- R = ( `' F o. _E ) $.

    ${
      $d x y A $.  $d x y B $.  $d x C $.  $d x y F $.
      brpermmodel.3 $e |- A e. _V $.
      brpermmodel.4 $e |- B e. _V $.
      $( The membership relation in a permutation model.  We use a permutation
         ` F ` of the universe to define a relation ` R ` that serves as the
         membership relation in our model.  The conclusion of this theorem is
         Definition II.9.1 of [Kunen2] p. 148.  All the axioms of ZFC except
         for Regularity hold in permutation models, and Regularity will be
         false if ` F ` is chosen appropriately.  Thus, permutation models can
         be used to show that Regularity does not follow from the other axioms
         (with the usual proviso that the axioms are consistent).  (Contributed
         by Eric Schmidt, 6-Nov-2025.) $)
      brpermmodel $p |- ( A R B <-> A e. ( F ` B ) ) $=
        ( vx vy cv cep wbr ccnv wa wex wcel cfv cvv anbi1d epel vex brcnv exbii
        anbi12i ccom breqi brco bitri weu wfn wf1o f1ofn ax-mp fneu mp2an eleq1
        wel wceq exbidv fv3 elab2 mpbiran2 3bitr4i ) AIKZLMZVEBDNZMZOZIPZAVEQZB
        VEDMZOZIPZABCMZABDRZQZVIVMIVFVKVHVLIAUAVEBDIUBHUCUEUDVOABVGLUFZMVJABCVR
        FUGIABVGLGHUHUIVQVNVLIUJZDSUKZBSQVSSSDULVTESSDUMUNHISBDUOUPJIURZVLOZIPZ
        VSOVNVSOJAVPGJKZAUSZWCVNVSWEWBVMIWEWAVKVLWDAVEUQTUTTJIBDVAVBVCVD $.

      $( Ordinary membership expressed in terms of the permutation model's
         membership relation.  (Contributed by Eric Schmidt, 6-Nov-2025.) $)
      brpermmodelcnv $p |- ( A R ( `' F ` B ) <-> A e. B ) $=
        ( ccnv cfv wbr wcel fvex brpermmodel wf1o wceq f1ocnvfv2 mp2an eleq2i
        cvv bitri ) ABDIZJZCKAUCDJZLABLAUCCDEFGBUBMNUDBATTDOBTLUDBPEHTTBDQRSUA
        $.
    $}

    ${
      $d x y z $.  $d z F $.

      $( The Axiom of Extensionality ~ ax-ext holds in permutation models.
         Part of Exercise II.9.2 of [Kunen2] p. 148.  (Contributed by Eric
         Schmidt, 6-Nov-2025.) $)
      permaxext $p |- ( A. z ( z R x <-> z R y ) -> x = y ) $=
        ( cv wbr wb wal cfv wceq weq wcel vex brpermmodel bibi12i albii cvv wf1
        dfcleq bitr4i wi wa wf1o f1of1 ax-mp f1veqaeq mpan el2v sylbi ) CHZAHZD
        IZUMBHZDIZJZCKZUNELZUPELZMZABNZUSUMUTOZUMVAOZJZCKVBURVFCUOVDUQVEUMUNDEF
        GCPZAPQUMUPDEFGVGBPQRSCUTVAUBUCVBVCUDZABTTEUAZUNTOUPTOUEVHTTEUFVIFTTEUG
        UHTTUNUPEUIUJUKUL $.
    $}

    ${
      $d x y z w $.  $d y z w F $.  $d y R $.
      $( The Axiom of Replacement ~ ax-rep holds in permutation models.  Part
         of Exercise II.9.2 of [Kunen2] p. 148.

         Note that, to prove that an instance of Replacement holds in the
         model, ` ph ` would need have all instances of ` e. ` replaced with
         ` R ` .  But this still results in an instance of this theorem, so we
         do establish that Replacement holds.  (Contributed by Eric Schmidt,
         6-Nov-2025.) $)
      permaxrep $p |- ( A. w E. y A. z ( A. y ph -> z = y ) ->
                       E. y A. z ( z R y <-> E. w ( w R x /\ A. y ph ) ) ) $=
        ( wal wex cv wbr wa wb cfv cvv wcel vex nfcv weq wi wmo nfa1 albii wrex
        mof cab ccnv fvex nfmo1 nfal brpermmodel wf1o wceq axrep6g mpan sylancr
        f1ocnvfv2 eleq2d bitrid df-rex abid anbi1i 3bitr4i bitrdi alrimi nfrexw
        exbii nfab nffv nfbr nfv nfan nfex nfbi nfab1 nfeq2 breq2 bibi1d spcegf
        albid mpsyl sylbir ) ACJZDCUAUBDJCKZEJWEDUCZEJZDLZCLZFMZELZBLZFMZWENZEK
        ZOZDJZCKZWGWFEWEDCACUDZUGUEWEEWMGPZUFZDUHZGUIZPZQRWHWIXEFMZWPOZDJZWSXCX
        DUJZWHXGDWGDEWEDUKULWHXFWIXCRZWPXFWIXEGPZRWHXJWIXEFGHIDSXIUMWHXKXCWIWHQ
        QGUNXCQRZXKXCUOHXAQRWHXLWMGUJWEEDXAQUPUQQQXCGUSURUTVAXBWLXARZWENZEKXJWP
        WEEXAVBXBDVCWOXNEWNXMWEWLWMFGHIESBSUMVDVIVEVFVGWRXHCXEQCXCXDCXDTXBCDWEC
        EXACXATWTVHVJVKZXGCDXFWPCCWIXEFCWITCFTXOVLWOCEWNWECWNCVMWTVNVOVPULWJXEU
        OZWQXGDDWJXEDXCXDDXDTXBDVQVKVRXPWKXFWPWJXEWIFVSVTWBWAWCWD $.
    $}

    ${
      $d x y z $.  $d y z ph $.  $d x y F $.  $d y R $.

      $( The Axiom of Separation ~ ax-sep holds in permutation models.  Part of
         Exercise II.9.2 of [Kunen2] p. 148.

         Note that, to prove that an instance of Separation holds in the model,
         ` ph ` would need have all instances of ` e. ` replaced with ` R ` .
         But this still results in an instance of this theorem, so we do
         establish that Separation holds.  (Contributed by Eric Schmidt,
         6-Nov-2025.) $)
      permaxsep $p |- E. y A. x ( x R y <-> ( x R z /\ ph ) ) $=
        ( cv wbr wa wb wal cfv crab ccnv fvex wceq wcel vex nfrab1 nfeq2 bibi1d
        breq2 albid rabex brpermmodelcnv rabid brpermmodel bicomi bianbi ax-gen
        nfcv nffv bitri ceqsexv2d ) BIZCIZEJZUQDIZEJZAKZLZBMUQABUTFNZOZFPZNZEJZ
        VBLZBMCVGVEVFQURVGRZVCVIBBURVGBVEVFBVFUMABVDUAUNUBVJUSVHVBURVGUQEUDUCUE
        VIBVHUQVESZVBUQVEEFGHBTZABVDUTFQUFUGVKUQVDSZAVAABVDUHVAVMUQUTEFGHVLDTUI
        UJUKUOULUP $.
    $}

    ${
      $d x y F $.  $d x R $.

      $( The Null Set Axiom ~ ax-nul holds in permutation models.  Part of
         Exercise II.9.2 of [Kunen2] p. 148.  (Contributed by Eric Schmidt,
         6-Nov-2025.) $)
      permaxnul $p |- E. x A. y -. y R x $=
        ( cv wbr wn wal c0 ccnv cfv fvex wceq breq2 notbid albidv wcel noel vex
        0ex brpermmodelcnv mtbir ax-gen ceqsexv2d ) BGZAGZCHZIZBJUGKDLZMZCHZIZB
        JAULKUKNUHULOZUJUNBUOUIUMUHULUGCPQRUNBUMUGKSUGTUGKCDEFBUAUBUCUDUEUF $.
    $}

    ${
      $d x y z w $.  $d y z w F $.  $d y R $.
      $( The Axiom of Power Sets ~ ax-pow holds in permutation models.  Part of
         Exercise II.9.2 of [Kunen2] p. 148.  (Contributed by Eric Schmidt,
         6-Nov-2025.) $)
      permaxpow $p |- E. y A. z ( A. w ( w R z -> w R x ) -> z R y ) $=
        ( cv wbr wi wal cfv fvex wcel vex cvv wa ax-mp brpermmodel breq2 imbi2d
        ccnv cpw cima wceq albidv wfun wfo wf1o dff1o3 mpbi pwex brpermmodelcnv
        simpri funimaex wfn f1ofn elpreima mpbiran bitri wss df-ss elpw imbi12i
        wb albii 3bitr4i sylbbr ax-gen ceqsexv2d ) DIZCIZEJZVLAIZEJZKZDLZVMBIZE
        JZKZCLVRVMFUCZVOFMZUDZUEZWBMZEJZKZCLBWFWEWBNVSWFUFZWAWHCWIVTWGVRVSWFVME
        UAUBUGWHCWGVMFMZWDOZVRWGVMWEOZWKVMWEEFGHCPZWBUHZWEQOQQFUIZWNQQFUJZWOWNR
        GQQFUKULUOWBWDWCVOFNUMUPSUNWLVMQOZWKWMFQUQZWLWQWKRVFWPWRGQQFURSQVMWDFUS
        SUTVAWJWCVBVLWJOZVLWCOZKZDLWKVRDWJWCVCWJWCVMFNVDVQXADVNWSVPWTVLVMEFGHDP
        ZWMTVLVOEFGHXBAPTVEVGVHVIVJVK $.
    $}

    ${
      $d x z w $.  $d y z w $.  $d z w F $.
      $( The Axiom of Pairing ~ ax-pr holds in permutation models.  Part of
         Exercise II.9.2 of [Kunen2] p. 148.  (Contributed by Eric Schmidt,
         6-Nov-2025.) $)
      permaxpr $p |- E. z A. w ( ( w = x \/ w = y ) -> w R z ) $=
        ( weq wo cv wbr wi wal cpr ccnv cfv fvex wceq breq2 wcel brpermmodelcnv
        imbi2d albidv vex prex elpr sylbbr ax-gen ceqsexv2d ) DAIDBIJZDKZCKZELZ
        MZDNUKULAKZBKZOZFPZQZELZMZDNCUTURUSRUMUTSZUOVBDVCUNVAUKUMUTULETUCUDVBDV
        AULURUAUKULUREFGHDUEZUPUQUFUBULUPUQVDUGUHUIUJ $.
    $}

    ${
      $d w x y z $.  $d w y z F $.  $d w R $.
      $( The Axiom of Union ~ ax-un holds in permutation models.  Part of
         Exercise II.9.2 of [Kunen2] p. 148.  (Contributed by Eric Schmidt,
         6-Nov-2025.) $)
      permaxun $p |- E. y A. z ( E. w ( z R w /\ w R x ) -> z R y ) $=
        ( cv wbr wa wi wal cfv fvex wcel vex brpermmodel cvv ax-mp breq2 imbi2d
        wex cima cuni ccnv wceq albidv wfn wss f1ofn ssv fnfvima mp3an12 elunii
        wf1o sylan2 syl2anb f1ofun funimaex uniex brpermmodelcnv sylibr exlimiv
        wfun ax-gen ceqsexv2d ) CIZDIZEJZVIAIZEJZKZDUCZVHBIZEJZLZCMVNVHFVKFNZUD
        ZUEZFUFZNZEJZLZCMBWBVTWAOVOWBUGZVQWDCWEVPWCVNVOWBVHEUAUBUHWDCVMWCDVMVHV
        TPZWCVJVHVIFNZPZVIVRPZWFVLVHVIEFGHCQZDQZRVIVKEFGHWKAQRWIWHWGVSPZWFFSUIZ
        VRSUJWIWLSSFUPZWMGSSFUKTVRULSVRFVIUMUNVHWGVSUOUQURVHVTEFGHWJVSFVEZVSSPW
        NWOGSSFUSTFVRVKFOUTTVAVBVCVDVFVG $.
    $}

    ${
      $d x y z w v F $.  $d z R $.

      ${
        $d x y z Z $.
        permaxinf2lem.3 $e |- Z = ( rec ( ( v e. _V |-> ( `' F ` ( ( F ` v )
            u. { v } ) ) ) , ( `' F ` (/) ) ) " _om ) $.
        $( Lemma for ~ permaxinf2 .  (Contributed by Eric Schmidt,
           6-Nov-2025.) $)
        permaxinf2lem $p |- E. x ( E. y ( y R x /\ A. z -. z R y ) /\
            A. y ( y R x -> E. z ( z R x /\ A. w ( w R z <-> ( w R y \/ w = y )
            ) ) ) ) $=
          ( cv wbr wal wa wex cfv wcel cvv brpermmodelcnv wn wo wb wi ccnv fvex
          weq wceq breq2 anbi1d exbidv imbi12d albidv anbi12d c0 notbid csn cun
          breq1 cmpt crdg com cima orbitinit eleqtrrdi ax-mp orbitex mpbir noel
          eqeltri vex 0ex mtbir ax-gen pm3.2i ceqsexv2d nfcv fveq2 sneq uneq12d
          fveq2d orbitclmpt mpan2 3imtr4i vsnex unex brpermmodel bicomi orbi12i
          elun velsn 3bitri bibi1d spcev sylancl ) BLZALZFMZCLZWPFMZUAZCNZOZBPZ
          WRWSWQFMZDLZWSFMZXFWPFMZDBUGZUBZUCZDNZOZCPZUDZBNZOWPHGUEZQZFMZXBOZBPZ
          XSWSXRFMZXLOZCPZUDZBNZOAXRHXQUFWQXRUHZXDYAXPYFYGXCXTBYGWRXSXBWQXRWPFU
          IZUJUKYGXOYEBYGWRXSXNYDYHYGXMYCCYGXEYBXLWQXRWSFUIUJUKULUMUNYAYFXTUOXQ
          QZXRFMZWSYIFMZUAZCNZOBYIUOXQUFZWPYIUHZXSYJXBYMWPYIXRFUSYOXAYLCYOWTYKW
          PYIWSFUIUPUMUNYJYMYJYIHRZYISRZYPYNYQYIESELZGQZYRUQZURZXQQZUTZYIVAVBVC
          ZHYIUUCSVDKVEVFYIHFGIJYNHUUDSKYIUUCVGVJZTVHYLCYKWSUORWSVIWSUOFGIJCVKV
          LTVMVNVOVPYEBXSWPGQZWPUQZURZXQQZXRFMZXFUUIFMZXJUCZDNZYDWPHRZUUIHRZXSU
          UJUUNUUISRUUOUUHXQUFZEYIWPUUBUUISHEWPVQEUUIVQKEBUGZUUAUUHXQUUQYSUUFYT
          UUGYRWPGVRYRWPVSVTWAWBWCWPHFGIJBVKZUUETUUIHFGIJUUPUUETWDUULDUUKXFUUHR
          XFUUFRZXFUUGRZUBXJXFUUHFGIJDVKZUUFUUGWPGUFBWEWFTXFUUFUUGWJUUSXHUUTXIX
          HUUSXFWPFGIJUVAUURWGWHDWPWKWIWLVNYCUUJUUMOCUUIUUPWSUUIUHZYBUUJXLUUMWS
          UUIXRFUSUVBXKUULDUVBXGUUKXJWSUUIXFFUIWMUMUNWNWOVNVOVP $.
      $}

      $( The Axiom of Infinity ~ ax-inf2 holds in permutation models.  Part of
         Exercise II.9.2 of [Kunen2] p. 148.  (Contributed by Eric Schmidt,
         6-Nov-2025.) $)
      permaxinf2 $p |- E. x ( E. y ( y R x /\ A. z -. z R y ) /\
          A. y ( y R x -> E. z ( z R x /\ A. w ( w R z <-> ( w R y \/ w = y )
          ) ) ) ) $=
        ( vv cvv cv cfv csn cun ccnv cmpt c0 crdg com cima eqid permaxinf2lem )
        ABCDIEFIJIKZFLUCMNFOZLPQUDLRSTZGHUEUAUB $.
    $}

    ${
      $d x z y w v q r s t $.  $d y z w v q r s t F $.  $d s R $.

      $( The Axiom of Choice ~ ac8prim holds in permutation models.  Part of
         Exercise II.9.3 of [Kunen2] p. 149.  Note that ~ ax-ac requires
         Regularity for its derivation from the usual Axiom of Choice and does
         not necessarily hold in permutation models.  (Contributed by Eric
         Schmidt, 16-Nov-2025.) $)
      permac8prim $p |- ( ( A. z ( z R x -> E. w w R z ) /\ A. z A. w
          ( ( z R x /\ w R x ) -> ( -. z = w -> A. y ( y R z ->
          -. y R w ) ) ) ) -> E. y A. z ( z R x -> E. w A. v ( (
          v R z /\ v R y ) <-> v = w ) ) ) $=
        ( vt vs cv wbr wi wal wa wcel wral wb cvv vq vr wex weq wn cin weu cima
        cfv wne wceq df-ral wfn wss wf1o f1ofn ax-mp ssv neeq1 ralima mp2an vex
        c0 brpermmodel exbii n0 bitr4i imbi12i albii 3bitr4i neeq2 ineq2 eqeq1d
        imbi12d ralbii ineq1 ralbidv r2al 3bitri anbi12i df-ne wf1 f1of1 f1fveq
        mpan el2v notbii bitr2i disj1 2albii wfun fvex funimaex mp2b raleqbi1dv
        f1ofun raleq anbi12d exbidv ac8 vtocl syl2anbr eleq2d eubidv bitri ccnv
        a1i wel breq2 brpermmodelcnv bitrdi bibi1d elin eubii eu6 bitr4di spcev
        albidv sylbi exlimiv syl ) CLZALZFMZDLZYBFMZDUCZNZCOZYDYEYCFMZPZCDUDZUE
        ZBLZYBFMZYNYEFMZUEZNZBOZNZNZDOCOZPELZJLZKLZUFZQZEUGZJGYCGUIZUHZRZKUCZYD
        UUCYBFMZUUCYNFMZPZEDUDZSZEOZDUCZNZCOZBUCZYIUUDVCUJZJUUJRZUUDUALZUJZUUDU
        VEUFZVCUKZNZUAUUJRZJUUJRZUULUUBYBGUIZVCUJZCUUIRZYBUUIQZUVMNZCOUVDYIUVMC
        UUIULGTUMZUUITUNZUVDUVNSTTGUOZUVQHTTGUPUQZUUIURZUVCUVMJCTUUIGUUDUVLVCUS
        UTVAYHUVPCYDUVOYGUVMYBYCFGHICVBZAVBZVDZYGYEUVLQZDUCUVMYFUWEDYEYBFGHIDVB
        ZUWBVDVEDUVLVFVGVHVIVJUVKUVOYEUUIQZPZUVLYEGUIZUJZUVLUWIUFZVCUKZNZNZDOCO
        ZUUBUVKUUDUWIUJZUUDUWIUFZVCUKZNZDUUIRZJUUJRZUWMDUUIRZCUUIRZUWOUVJUWTJUU
        JUVQUVRUVJUWTSUVTUWAUVIUWSUADTUUIGUVEUWIUKZUVFUWPUVHUWRUVEUWIUUDVKUXDUV
        GUWQVCUVEUWIUUDVLVMVNUTVAVOUVQUVRUXAUXCSUVTUWAUWTUXBJCTUUIGUUDUVLUKZUWS
        UWMDUUIUXEUWPUWJUWRUWLUUDUVLUWIUSUXEUWQUWKVCUUDUVLUWIVPVMVNVQUTVAUWMCDU
        UIUUIVRVSUUAUWNCDYKUWHYTUWMYDUVOYJUWGUWDYEYCFGHIUWFUWCVDVTYMUWJYSUWLUWJ
        UVLUWIUKZUEYMUVLUWIWAUXFYLUXFYLSZCDTTGWBZYBTQYETQPUXGUVSUXHHTTGWCUQTTYB
        YEGWDWEWFWGWHYSYNUVLQZYNUWIQZUEZNZBOUWLYRUXLBYOUXIYQUXKYNYBFGHIBVBZUWBV
        DYPUXJYNYEFGHIUXMUWFVDWGVHVIBUVLUWIWIVGVHVHWJVGUVCJUBLZRZUVIUAUXNRZJUXN
        RZPZUUHJUXNRZKUCZNUVDUVKPZUULNUBUUJUVSGWKUUJTQHTTGWPGUUIYCGWLWMWNUXNUUJ
        UKZUXRUYAUXTUULUYBUXOUVDUXQUVKUVCJUXNUUJWQUXPUVJJUXNUUJUVIUAUXNUUJWQWOW
        RUYBUXSUUKKUUHJUXNUUJWQWSVNUBKJUAEWTXAXBUUKUVBKUUKUVOUUCUVLUUEUFZQZEUGZ
        NZCOZUVBUUKUYECUUIRZUYGUVQUVRUUKUYHSUVTUWAUUHUYEJCTUUIGUXEUUGUYDEUXEUUF
        UYCUUCUUDUVLUUEVPXCXDUTVAUYECUUIULXEUVAUYGBUUEGXFZUIZUUEUYIWLYNUYJUKZUU
        TUYFCUYKYDUVOUUSUYEYDUVOSUYKUWDXGUYKUUSUUCUVLQZEKXHZPZUUPSZEOZDUCZUYEUY
        KUURUYPDUYKUUQUYOEUYKUUOUYNUUPUYKUUMUYLUUNUYMUUMUYLSUYKUUCYBFGHIEVBZUWB
        VDXGUYKUUNUUCUYJFMUYMYNUYJUUCFXIUUCUUEFGHIUYRKVBXJXKWRXLXRWSUYEUYNEUGUY
        QUYDUYNEUUCUVLUUEXMXNUYNEDXOXEXPVNXRXQXSXTYA $.
    $}
  $}

  ${
    nregmodel.1 $e |- F = ( ( _I |` ( _V \ { (/) , { (/) } } ) ) u.
        { <. (/) , { (/) } >. , <. { (/) } , (/) >. } ) $.
    $( Define a permutation ` F ` used to produce a model in which ~ ax-reg is
       false.  The permutation swaps ` (/) ` and ` { (/) } ` and leaves the
       rest of ` V ` fixed.  This is an example given after Exercise II.9.2 of
       [Kunen2] p. 148.  (Contributed by Eric Schmidt, 16-Nov-2025.) $)
    nregmodelf1o $p |- F : _V -1-1-onto-> _V $=
      ( cvv wf1o cid c0 csn cpr cdif cres cfv cop cun wcel f1ovi 0ex wceq ax-mp
      fvi opeq2i snex f1ofvswap mp3an wb preq12i uneq2i eqtr4i f1oeq1 mpbir ) C
      CADZCCECFFGZHIJZFUKEKZLZUKFEKZLZHZMZDZCCEDFCNZUKCNZUSOPFUAZCCEFUKUBUCAURQ
      UJUSUDAULFUKLZUKFLZHZMURBUQVEULUNVCUPVDUMUKFVAUMUKQVBUKCSRTUOFUKUTUOFQPFC
      SRTUEUFUGCCAURUHRUI $.

    ${
      nregmodel.2 $e |- R = ( `' F o. _E ) $.
      $( Lemma for ~ nregmodel .  (Contributed by Eric Schmidt,
         16-Nov-2025.) $)
      nregmodellem $p |- ( x R (/) <-> x e. { (/) } ) $=
        ( cv c0 wbr cfv wcel csn nregmodelf1o vex 0ex brpermmodel cop cvv ax-mp
        wfun cpr wceq wf1o f1ofun cid cdif cres cun opex prid1 eleqtrri funopfv
        elun2 mp2 eleq2i bitri ) AFZGBHUPGCIZJUPGKZJUPGBCCDLZEAMNOUQURUPCSZGURP
        ZCJUQURUAQQCUBUTUSQQCUCRVAUDQGURTUEUFZVAURGPZTZUGZCVAVDJVAVEJVAVCGURUHU
        IVAVDVBULRDUJGURCUKUMUNUO $.

      ${
        $d x y z $.  $d x R $.

        $( The Axiom of Regularity ~ ax-reg is false in the permutation model
           defined from ` F ` .  Since the other axioms of ZFC hold in all
           permutation models ( ~ permaxext through ~ permac8prim ), we can
           conclude that Regularity does not follow from those axioms, assuming
           ZFC is consistent.  (If we could prove Regularity from the other
           axioms, we could prove it in the permutation model and thus obtain a
           contradiction with this theorem.)  Since we also know that
           Regularity is consistent with the other axioms ( ~ wfaxext through
           ~ wfac8prim ), Regularity is neither provable nor disprovable from
           the other axioms; i.e., it is independent of them.  (Contributed by
           Eric Schmidt, 16-Nov-2025.) $)
        nregmodel $p |- -. A. x ( E. y y R x ->
             E. y ( y R x /\ A. z ( z R y -> -. z R x ) ) ) $=
          ( cv wbr wex wn wi wal wa c0 wcel 0ex wceq breq2 bitrdi csn ceqsexv2d
          snid eleq1 nregmodellem exbidv notbid imbi2d anbi12d imbi12d spcv mpi
          albidv wral df-ral imbi1d rexsn df-rex 3bitr2ri ralsn bitri sylib mt2
          wrex ) BHZAHZDIZBJZVGCHZVEDIZVIVFDIZKZLZCMZNZBJZLZAMZOOUAZPZOQUCZVRVE
          VSPZVJVIVSPZKZLZCMZNZBJZVTKZVRWBBJZWHWBVTBOQVEOVSUDWAUBVQWJWHLAOQVFOR
          ZVHWJVPWHWKVGWBBWKVGVEODIWBVFOVEDSBDEFGUETZUFWKVOWGBWKVGWBVNWFWLWKVMW
          ECWKVLWDVJWKVKWCWKVKVIODIZWCVFOVIDSCDEFGUEZTUGUHUMUIUFUJUKULWHWDCVSUN
          ZWIWOWCWDLZCMZWFBVSVDWHWDCVSUOWFWQBOQVEORZWEWPCWRVJWCWDWRVJWMWCVEOVID
          SWNTUPUMUQWFBVSURUSWDWICOQVIORWCVTVIOVSUDUGUTVAVBVC $.
      $}

      ${
        $d x y z $.  $d z F $.

        $( The Axiom of Extensionality ~ ax-ext is true in the permutation
           model defined from ` F ` .  This theorem is an immediate consequence
           of the fact that ~ ax-ext holds in all permutation models and is
           provided as an illustration.  (Contributed by Eric Schmidt,
           16-Nov-2025.) $)
        nregmodelaxext $p |- ( A. z ( z R x <-> z R y ) -> x = y ) $=
          ( nregmodelf1o permaxext ) ABCDEEFHGI $.
      $}
    $}
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Isomorphism of finite ordinals and non-negative integers
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( The ` # ` function on ` _om ` preserves addition.  (Contributed by Eric
     Schmidt, 7-Jul-2026.) $)
  hashnna $p |- ( ( A e. _om /\ B e. _om ) -> ( # ` ( A +o B ) ) =
      ( ( # ` A ) + ( # ` B ) ) ) $=
    ( vx com wcel wa coa co chash cres cfv caddc hashgval2 hashgadd nnacl fvres
    fvresd oveqan12d 3eqtr3d ) ADEZBDEZFZABGHZIDJZKAUDKZBUDKZLHUCIKAIKZBIKZLHCA
    BUDCMNUBUCDIABOQTUAUEUGUFUHLADIPBDIPRS $.

  $( The ` # ` function on ` _om ` turns successor into adding 1.  (Contributed
     by Eric Schmidt, 7-Jul-2026.) $)
  hashnnsuc $p |- ( A e. _om -> ( # ` suc A ) = ( ( # ` A ) + 1 ) ) $=
    ( com wcel csuc chash cfv c1o caddc co coa con0 wceq nnon oa1suc syl fveq2d
    c1 1onn hashnna mpan2 eqtr3d hash1 oveq2i eqtrdi ) ABCZADZEFZAEFZGEFZHIZUHQ
    HIUEAGJIZEFZUGUJUEUKUFEUEAKCUKUFLAMANOPUEGBCULUJLRAGSTUAUIQUHHUBUCUD $.

  $( The ` # ` function on ` _om ` preserves multiplication.  (Contributed by
     Eric Schmidt, 7-Jul-2026.) $)
  hashnnm $p |- ( ( A e. _om /\ B e. _om ) -> ( # ` ( A .o B ) ) =
      ( ( # ` A ) x. ( # ` B ) ) ) $=
    ( com wcel wa comu co cfv cxp cmul cen wbr wceq con0 nnon omxpen syl2an cfn
    chash nnfi hasheni syl hashxp eqtrd ) ACDZBCDZEZABFGZSHZABIZSHZASHBSHJGZUGU
    HUJKLZUIUKMUEANDBNDUMUFAOBOABPQUHUJUAUBUEARDBRDUKULMUFATBTABUCQUD $.

  $( The ` # ` function on ` _om ` preserves the ordering.  (Contributed by
     Eric Schmidt, 7-Jul-2026.) $)
  hashnnlt $p |- ( ( A e. _om /\ B e. A ) -> ( # ` B ) < ( # ` A ) ) $=
    ( com wcel cfn wpss chash cfv clt wbr nnfi word wi nnord ordpss syl hashpss
    imp syl2an2r ) ACDZAEDBADZBAFZBGHAGHIJAKTUAUBTALUAUBMANBAOPRABQS $.

  $( The ` # ` function on ` _om ` preserves the ordering.  (Contributed by
     Eric Schmidt, 7-Jul-2026.) $)
  hashnnltb $p |- ( ( A e. _om /\ B e. _om ) -> ( A e. B <->
      ( # ` A ) < ( # ` B ) ) ) $=
    ( com wcel wa chash cfv clt wbr wi hashnnlt ex adantl con0 nnon syl2anr cxr
    wn wb hashxrcl wss cle hashss adantr ontri1 xrlenlt 3imtr3d impcon4bid ) AC
    DZBCDZEZABDZAFGZBFGZHIZUJULUOJUIUJULUOBAKLMUKBAUAZUNUMUBIZULRZUORZUIUPUQJUJ
    UIUPUQABCUCLUDUJBNDANDUPURSUIBOAOBAUEPUJUNQDUMQDUQUSSUIBCTACTUNUMUFPUGUH $.

  $( The ` # ` function yields a bijection from ` _om ` to ` NN0 ` .
     (Contributed by Eric Schmidt, 7-Jul-2026.) $)
  hashomf1o $p |- ( # |` _om ) : _om -1-1-onto-> NN0 $=
    ( vx chash com cres hashgval2 hashgf1o ) ABCDAEF $.

  ${
    $d x y $.

    $( The ` # ` function yields an order isomorphism between ` _om ` and
       ` NN0 ` .  (Contributed by Eric Schmidt, 7-Jul-2026.) $)
    hashomiso $p |- ( # |` _om ) Isom _E , < ( _om , NN0 ) $=
      ( vx vy com cn0 cep clt chash cres wiso wf1o cv wbr cfv wb wral hashomf1o
      wcel wa wel fvres epel hashnnltb bitrid breqan12d bitr4d df-isom mpbir2an
      rgen2 ) CDEFGCHZICDUIJAKZBKZELZUJUIMZUKUIMZFLZNZBCOACOPUPABCCUJCQZUKCQZRZ
      ULUJGMZUKGMZFLZUOULABSUSVBBUJUAUJUKUBUCUQURUMUTUNVAFUJCGTUKCGTUDUEUHABCDE
      FUIUFUG $.
  $}

$( (End of Eric Schmidt's mathbox.) $)
