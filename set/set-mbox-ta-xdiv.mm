$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Division in the extended real number system
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $c /e $. $( Division of extended real numbers. $)

  $( Extend class notation to include division of extended reals. $)
  cxdiv $a class /e $.

  ${
    $d x y z $.
    $( Define division over extended real numbers.  (Contributed by Thierry
       Arnoux, 17-Dec-2016.) $)
    df-xdiv $a |- /e = ( x e. RR* , y e. ( RR \ { 0 } ) |->
                   ( iota_ z e. RR* ( y *e z ) = x ) ) $.
  $}

  ${
    $d x y z A $.  $d x y z B $.
    $( Value of division: the (unique) element ` x ` such that
       ` ( B x. x ) = A ` .  This is meaningful only when ` B ` is nonzero.
       (Contributed by Thierry Arnoux, 17-Dec-2016.) $)
    xdivval $p |- ( ( A e. RR* /\ B e. RR /\ B =/= 0 ) ->
                   ( A /e B ) = ( iota_ x e. RR* ( B *e x ) = A ) ) $=
      ( vy vz cxr wcel cr cc0 wne cxdiv co cv cxmu wceq wa csn simpl riotabidva
      crio eldifsn eqeq2d oveq1d eqeq1d df-xdiv riotaex ovmpo sylan2br 3impb
      cdif ) BFGZCHGZCIJZBCKLCAMZNLZBOZAFTZOZULUMPUKCHIQUJZGURCHIUADEBCFUSEMZUN
      NLZDMZOZAFTUQKVABOZAFTVBBOZVCVDAFVEUNFGZPVBBVAVEVFRUBSUTCOZVDUPAFVGVFPZVA
      UOBVHUTCUNNVGVFRUCUDSDEAUEUPAFUFUGUHUI $.
  $}

  ${
    $d x A $.
    $( Existence of reciprocal of nonzero real number.  (Contributed by Thierry
       Arnoux, 17-Dec-2016.) $)
    xrecex $p |- ( ( A e. RR /\ A =/= 0 ) -> E. x e. RR ( A *e x ) = 1 ) $=
      ( cr wcel cc0 wne wa cv cxmu co c1 wceq wrex cmul ax-rrecex rexmul eqeq1d
      wb wi ex adantr pm5.32d rexbidv2 mpbird ) BCDZBEFZGZBAHZIJZKLZACMBUHNJZKL
      ZACMABOUGUJULACCUGUHCDZUJULUEUMUJULRZSUFUEUMUNUEUMGUIUKKBUHPQTUAUBUCUD $.
  $}

  ${
    $d x A $.  $d x B $.  $d x C $.  $d x ph $.
    xmulcand.1 $e |- ( ph -> A e. RR* ) $.
    xmulcand.2 $e |- ( ph -> B e. RR* ) $.
    xmulcand.3 $e |- ( ph -> C e. RR ) $.
    xmulcand.4 $e |- ( ph -> C =/= 0 ) $.
    $( Cancellation law for extended multiplication.  (Contributed by Thierry
       Arnoux, 17-Dec-2016.) $)
    xmulcand $p |- ( ph -> ( ( C *e A ) = ( C *e B ) <-> A = B ) ) $=
      ( vx cxmu co wceq c1 cr wcel syl2anc wa oveq2 cxr adantr cv wi cc0 xrecex
      wne wrex simprl rexrd xmulcom simprr eqtrd oveq1d xmulass syl3anc xmullid
      syl 3eqtr3d eqeq12d imbitrid rexlimddv impbid1 ) ADBJKZDCJKZLZBCLZADIUAZJ
      KZMLZVDVEUBINADNOZDUCUEVHINUFGHIDUDPVDVFVBJKZVFVCJKZLAVFNOZVHQZQZVEVBVCVF
      JRVNVJBVKCVNVFDJKZBJKZMBJKZVJBVNVOMBJVNVOVGMVNVFSOZDSOZVOVGLVNVFAVLVHUGUH
      ZVNDAVIVMGTUHZVFDUIPAVLVHUJUKZULVNVRVSBSOZVPVJLVTWAAWCVMETZVFDBUMUNVNWCVQ
      BLWDBUOUPUQVNVOCJKZMCJKZVKCVNVOMCJWBULVNVRVSCSOZWEVKLVTWAAWGVMFTZVFDCUMUN
      VNWGWFCLWHCUOUPUQURUSUTBCDJRVA $.
  $}

  ${
    $d x y A $.  $d x y B $.
    $( Existential uniqueness of reciprocals.  Theorem I.8 of [Apostol] p. 18.
       (Contributed by Thierry Arnoux, 17-Dec-2016.) $)
    xreceu $p |- ( ( A e. RR* /\ B e. RR /\ B =/= 0 ) ->
                  E! x e. RR* ( B *e x ) = A ) $=
      ( vy cxr wcel cr w3a cv cxmu co wceq wrex wa wi wral 3adant1 oveq2 eqeq1d
      c1 cc0 wne wreu ressxr xrecex ssrexv mpsyl simprl simpll xmulcld ad2antll
      wss oveq1 simplr rexrd xmulass syl3anc xmullid syl 3eqtr3d rspcev syl2anc
      rexlimdvaa 3adant3 mpd eqtr3 simp1 simp3l simp3r xmulcand imbitrid expcom
      simp2 3expa ralrimivv reu4 sylanbrc ) BEFZCGFZCUAUBZHZCAIZJKZBLZAEMZWDCDI
      ZJKZBLZNZWBWFLZOZDEPAEPWDAEUCWAWGTLZDEMZWEGEULWAWLDGMZWMUDVSVTWNVRDCUEQWL
      DGEUFUGVRVSWMWEOVTVRVSNZWLWEDEWOWFEFZWLNZNZWFBJKZEFCWSJKZBLZWEWRWFBWOWPWL
      UHZVRVSWQUIZUJWRWGBJKZTBJKZWTBWLXDXELWOWPWGTBJUMUKWRCEFWPVRXDWTLWRCVRVSWQ
      UNUOXBXCCWFBUPUQWRVRXEBLXCBURUSUTWDXAAWSEWBWSLWCWTBWBWSCJRSVAVBVCVDVEWAWK
      ADEEVSVTWBEFZWPNZWKOVRXGVSVTNZWKXFWPXHWKWIWCWGLXFWPXHHZWJWCWGBVFXIWBWFCXF
      WPXHVGXFWPXHVMXFWPVSVTVHXFWPVSVTVIVJVKVNVLQVOWDWHADEWJWCWGBWBWFCJRSVPVQ
      $.
  $}

  ${
    $d x A $.  $d x B $.
    xdivcld.1 $e |- ( ph -> A e. RR* ) $.
    xdivcld.2 $e |- ( ph -> B e. RR ) $.
    xdivcld.3 $e |- ( ph -> B =/= 0 ) $.
    $( Closure law for the extended division.  (Contributed by Thierry Arnoux,
       15-Mar-2017.) $)
    xdivcld $p |- ( ph -> ( A /e B ) e. RR* ) $=
      ( vx cxdiv co cv cxmu wceq cxr crio wcel cr cc0 wne xdivval syl3anc wreu
      xreceu riotacl syl eqeltrd ) ABCHIZCGJKIBLZGMNZMABMOZCPOZCQRZUFUHLDEFGBCS
      TAUGGMUAZUHMOAUIUJUKULDEFGBCUBTUGGMUCUDUE $.
  $}

  $( Closure law for the extended division.  (Contributed by Thierry Arnoux,
     15-Mar-2017.) $)
  xdivcl $p |- ( ( A e. RR* /\ B e. RR /\ B =/= 0 ) -> ( A /e B ) e. RR* ) $=
    ( cxr wcel cr cc0 wne w3a simp1 simp2 simp3 xdivcld ) ACDZBEDZBFGZHABMNOIMN
    OJMNOKL $.

  ${
    $d x A $.  $d x B $.  $d x C $.
    $( Relationship between division and multiplication.  (Contributed by
       Thierry Arnoux, 24-Dec-2016.) $)
    xdivmul $p |- ( ( A e. RR* /\ B e. RR* /\ ( C e. RR /\ C =/= 0 ) )
                 -> ( ( A /e C ) = B <-> ( C *e B ) = A ) ) $=
      ( vx cxr wcel cr cc0 wne wa w3a cxdiv co wceq cv cxmu crio 3adant2 eqeq1d
      3expb xdivval wreu wb simp2 xreceu oveq2 riota2 syl2anc bitr4d ) AEFZBEFZ
      CGFZCHIZJZKZACLMZBNCDOZPMZANZDEQZBNZCBPMZANZUOUPUTBUJUNUPUTNZUKUJULUMVDDA
      CUATRSUOUKUSDEUBZVCVAUCUJUKUNUDUJUNVEUKUJULUMVEDACUETRUSVCDEBUQBNURVBAUQB
      CPUFSUGUHUI $.
  $}

  ${
    $d x A $.  $d x B $.
    $( The extended real division operation when both arguments are real.
       (Contributed by Thierry Arnoux, 18-Dec-2016.) $)
    rexdiv $p |- ( ( A e. RR /\ B e. RR /\ B =/= 0 )
                                                 -> ( A /e B ) = ( A / B ) ) $=
      ( vx cr wcel w3a cmul co wceq crio cc wreu recn id syl eqeq1d syl2anc wss
      wi cxr cc0 wne cv cxdiv cdiv redivcl 3anim123i divcan2 oveq2 rspcev receu
      wrex wral wa ax-resscn rgenw riotass2 mpanl12 cxmu xdivval syl3an1 ressxr
      rexr a1i rexmul biimprd ralrimiva 3ad2ant2 xreceu syl22anc eqtr4d 3eqtr4d
      divval ) ADEZBDEZBUAUBZFZBCUCZGHZAIZCDJZVTCKJZABUDHZABUEHZVQVTCDULZVTCKLZ
      WAWBIZVQWDDEBWDGHZAIZWEABUFVQAKEZBKEZVPFZWIVNWJVOWKVPVPAMBMVPNUGZABUHOVTW
      ICWDDVRWDIVSWHAVRWDBGUIPUJQZVQWLWFWMCABUKODKRVTVTSZCDUMWEWFUNWGUOWOCDVTNU
      PVTVTCDKUQURQVQWCBVRUSHZAIZCTJZWAVNATEZVOVPWCWRIAVCZCABUTVAVQDTRZVTWQSZCD
      UMZWEWQCTLZWAWRIXAVQVBVDVOVNXCVPVOXBCDVOVRDEUNZWQVTXEWPVSABVRVEPVFVGVHWNV
      NWSVOVPXDWTCABVIVAVTWQCDTUQVJVKVQWLWDWBIWMCABVMOVL $.
  $}

  $( Relationship between division and reciprocal.  (Contributed by Thierry
     Arnoux, 5-Jul-2017.) $)
  xdivrec $p |- ( ( A e. RR* /\ B e. RR /\ B =/= 0 ) ->
                                          ( A /e B ) = ( A *e ( 1 /e B ) ) ) $=
    ( cxr wcel cr cc0 wne w3a cxdiv co c1 cxmu simp2 xmulcom syl2anc wb xdivmul
    wceq syl112anc eqtrd rexrd simp1 1xr a1i simp3 xdivcld xmulcld xmulass eqid
    syl3anc mpbii oveq2d 3eqtrd xmulrid syl mpbird ) ACDZBEDZBFGZHZABIJAKBIJZLJ
    ZRZBVBLJZARZUTVDAKLJZAUTVDVBBLJZAVABLJZLJZVFUTBCDZVBCDZVDVGRUTBUQURUSMZUAZU
    TAVAUQURUSUBZUTKBKCDZUTUCUDZVLUQURUSUEZUFZUGZBVBNOUTUQVACDZVJVGVIRVNVRVMAVA
    BUHUJUTVHKALUTVHBVALJZKUTVTVJVHWARVRVMVABNOUTVAVARZWAKRZVAUIUTVOVTURUSWBWCP
    VPVRVLVQKVABQSUKTULUMUTUQVFARVNAUNUOTUTUQVKURUSVCVEPVNVSVLVQAVBBQSUP $.

  $( A number divided by itself is one.  (Contributed by Thierry Arnoux,
     18-Dec-2016.) $)
  xdivid $p |- ( ( A e. RR /\ A =/= 0 ) -> ( A /e A ) = 1 ) $=
    ( cr wcel cc0 wne wa cxdiv co cdiv c1 wceq rexdiv 3anidm12 recn divid sylan
    cc eqtrd ) ABCZADEZFAAGHZAAIHZJSTUAUBKAALMSAQCTUBJKANAOPR $.

  $( Division into zero is zero.  (Contributed by Thierry Arnoux,
     18-Dec-2016.) $)
  xdiv0 $p |- ( ( A e. RR /\ A =/= 0 ) -> ( 0 /e A ) = 0 ) $=
    ( cr wcel cc0 wne wa cxdiv co cdiv wceq rexdiv mp3an1 recn div0 sylan eqtrd
    0re cc ) ABCZADEZFDAGHZDAIHZDDBCSTUAUBJQDAKLSARCTUBDJAMANOP $.

  $( Division into zero is zero.  (Contributed by Thierry Arnoux,
     18-Dec-2016.) $)
  xdiv0rp $p |- ( A e. RR+ -> ( 0 /e A ) = 0 ) $=
    ( crp wcel cr cc0 wne wa cxdiv co wceq rprene0 xdiv0 syl ) ABCADCAEFGEAHIEJ
    AKALM $.

  $( A positive real number divided by plus infinity is zero.
  The definition of /e needs to be extended to prove such a theorem.
  xdivrppnf @p |- ( A e. RR+ -> ( A /e +oo ) = 0 ) @=
    ? $)

  $( Membership in a closed interval of extended reals versus the same open
     interval.  (Contributed by Thierry Arnoux, 18-Dec-2016.) $)
  eliccioo $p |- ( ( A e. RR* /\ B e. RR* /\ A <_ B ) ->
    ( C e. ( A [,] B ) <-> ( C = A \/ C e. ( A (,) B ) \/ C = B ) ) ) $=
    ( cxr wcel cle wbr w3a cicc co wceq w3o wa wo wb adantl adantr eleq1 mpbird
    cioo cpr cun prunioo eleq2d biimpar elun elprg orbi2d bitrid 3orass 3orcoma
    mpbid bitr3i sylib lbicc2 ioossicc sseli ubicc2 3jaodan impbida ) ADEBDEABF
    GHZCABIJZEZCAKZCABTJZEZCBKZLZVAVCMZVFVDVGNZNZVHVICVEABUAZUBZEZVKVAVNVCVAVMV
    BCABUCUDUEVCVNVKOVAVNVFCVLEZNVCVKCVEVLUFVCVOVJVFCABVBUGUHUIPULVKVFVDVGLVHVF
    VDVGUJVFVDVGUKUMUNVAVDVCVFVGVAVDMVCAVBEZVAVPVDABUOQVDVCVPOVACAVBRPSVFVCVAVE
    VBCABUPUQPVAVGMVCBVBEZVAVQVGABURQVGVCVQOVACBVBRPSUSUT $.

  $( Elementhood in the set of nonnegative extended reals.  (Contributed by
     Thierry Arnoux, 18-Dec-2016.) $)
  elxrge02 $p |- ( A e. ( 0 [,] +oo ) <-> ( A = 0 \/ A e. RR+ \/ A = +oo ) ) $=
    ( cc0 cpnf cicc co wcel wceq cioo w3o crp cxr cle wbr wb 0xr pnfxr eliccioo
    0lepnf mp3an biid ioorp eleq2i 3orbi123i bitri ) ABCDEFZABGZABCHEZFZACGZIZU
    FAJFZUIIBKFCKFBCLMUEUJNOPRBCAQSUFUFUHUKUIUIUFTUGJAUAUBUITUCUD $.

  ${
    $d x A $.
    $( Plus infinity divided by a positive real number is plus infinity.
       (Contributed by Thierry Arnoux, 18-Dec-2016.) $)
    xdivpnfrp $p |- ( A e. RR+ -> ( +oo /e A ) = +oo ) $=
      ( vx crp wcel cpnf cxdiv co cv cxmu wceq cxr crio cc0 wa pnfxr syl cle wb
      wbr xgepnf wne w3a rprene0 jctil 3anass sylibr xdivval a1i xlemul2 mp3an1
      ancoms clt rpxr rpgt0 xmulpnf1 syl2anc adantr breq1d bitr2d xmulcl adantl
      cr sylan 3bitr3d riota5 eqtrd ) ACDZEAFGZABHZIGZEJZBKLZEVGEKDZAVBDZAMUAZU
      BZVHVLJVGVMVNVONZNVPVGVQVMAUCOUDVMVNVOUEUFBEAUGPVGVKBKEVMVGOUHVGVIKDZNZEV
      JQSZEVIQSZVKVIEJZVSWAAEIGZVJQSZVTVRVGWAWDRZVMVRVGWEOEVIAUIUJUKVSWCEVJQVGW
      CEJZVRVGAKDZMAULSWFAUMZAUNAUOUPUQURUSVSVJKDZVTVKRVGWGVRWIWHAVIUTVCVJTPVRW
      AWBRVGVITVAVDVEVF $.
  $}

  ${
    rpxdivcld.1 $e |- ( ph -> A e. RR+ ) $.
    rpxdivcld.2 $e |- ( ph -> B e. RR+ ) $.
    $( Closure law for extended division of positive reals.  (Contributed by
       Thierry Arnoux, 18-Dec-2016.) $)
    rpxdivcld $p |- ( ph -> ( A /e B ) e. RR+ ) $=
      ( cxdiv co cdiv crp cr wcel cc0 wceq rpred rpne0d rexdiv syl3anc rpdivcld
      wne eqeltrd ) ABCFGZBCHGZIABJKCJKCLSUAUBMABDNACENACEOBCPQABCDERT $.
  $}

  ${
    xrpxdivcld.1 $e |- ( ph -> A e. ( 0 [,] +oo ) ) $.
    xrpxdivcld.2 $e |- ( ph -> B e. RR+ ) $.
    $( Closure law for extended division of positive extended reals.
       (Contributed by Thierry Arnoux, 18-Dec-2016.) $)
    xrpxdivcld $p |- ( ph -> ( A /e B ) e. ( 0 [,] +oo ) ) $=
      ( cc0 wceq cxdiv co cpnf cicc wcel crp wa oveq1 xdiv0rp syl sylan9eqr w3o
      elxrge02 biimpri 3o1cs simpr adantr rpxdivcld 3o2cs xdivpnfrp 3o3cs sylib
      mpjao3dan ) ABFGZBCHIZFJKIZLZBMLZBJGZAUKNULFGZUNUKAULFCHIZFBFCHOACMLZURFG
      ECPQRUQULMLZULJGZUNUNUQUTVASULTUAZUBQAUONZUTUNVCBCAUOUCAUSUOEUDUEUQUTVAUN
      VBUFQAUPNVAUNUPAULJCHIZJBJCHOAUSVDJGECUGQRUQUTVAUNVBUHQABUMLUKUOUPSDBTUIU
      J $.
  $}

$(
  @{
    xltmul1d.1 @e |- ( ph -> A e. RR ) $@
    xltmul1d.2 @e |- ( ph -> B e. RR* ) $@
    xltmul1d.3 @e |- ( ph -> C e. ( 0 [,] +oo ) ) $@
    @( 'Less than' relationship between division and multiplication.
       (Contributed by Mario Carneiro, 28-May-2016.) @)
    xltdivmul2d @p |- ( ph -> ( ( A /e C ) < B <-> A < ( B *e C ) ) ) @=
      ? @.
  @}
$)

