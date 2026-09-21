$[ set-main.mm $]
$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Mathbox for BTernaryTau
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  First-order logic
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Auxiliary axiom schemes
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    nfan1c.1 $e |- F/ x ph $.
    nfan1c.2 $e |- ( ph -> F/ x ps ) $.
    $( Variant of ~ nfan and commuted form of ~ nfan1 .  (Contributed by
       BTernaryTau, 31-Jul-2025.) $)
    nfan1c $p |- F/ x ( ps /\ ph ) $=
      ( wa wnf nfan1 ancom nfbii mpbi ) ABFZCGBAFZCGABCDEHLMCABIJK $.
  $}

  ${
    $d x y $.
    cbvex1v.1 $e |- F/ x ph $.
    cbvex1v.2 $e |- F/ y ph $.
    cbvex1v.3 $e |- ( ph -> F/ y ps ) $.
    cbvex1v.4 $e |- ( ph -> F/ x ch ) $.
    cbvex1v.5 $e |- ( ph -> ( x = y -> ( ps -> ch ) ) ) $.
    $( Rule used to change bound variables, using implicit substitution.
       (Contributed by BTernaryTau, 31-Jul-2025.) $)
    cbvex1v $p |- ( ph -> ( E. x ps -> E. y ch ) ) $=
      ( wn wal wex nfnd weq wi equcomi con3 syl56 df-ex cbv1v con3d 3imtr4g ) A
      BKZDLZKCKZELZKBDMCEMAUGUEAUFUDEDGFACDINABEHNEDODEOABCPUFUDPEDQJBCRSUAUBBD
      TCETUC $.
  $}

  ${
    $d x z $.  $d y z $.
    dvelimalcased.1 $e |- F/ x ph $.
    dvelimalcased.2 $e |- ( -. A. x x = y -> F/ z ph ) $.
    dvelimalcased.3 $e |- ( ( ph /\ -. A. x x = y ) -> F/ x ps ) $.
    dvelimalcased.4 $e |- ( ( ph /\ -. A. x x = y ) -> F/ z th ) $.
    dvelimalcased.5 $e |- ( ( ph /\ -. A. x x = y ) ->
        ( z = x -> ( ps -> th ) ) ) $.
    dvelimalcased.6 $e |- ( ( ph /\ A. x x = y ) -> ( ch -> th ) ) $.
    dvelimalcased.7 $e |- ( ph -> A. z ps ) $.
    dvelimalcased.8 $e |- ( ph -> A. x ch ) $.
    $( Eliminate a disjoint variable condition from a universally quantified
       statement using cases.  (Contributed by BTernaryTau, 31-Jul-2025.) $)
    dvelimalcased $p |- ( ph -> A. x th ) $=
      ( wal wi wa nfan ex weq nfa1 alimd mpid wn nfv nfan1c nfna1 cbv1v pm2.61d
      ) AEFUAZEPZDEPZAULCEPZUMOAULUNUMQAULRCDEAULEHUKEUBSMUCTUDAULUEZBGPZUMNAUO
      UPUMQAUORBDGEUOAGUOGUFIUGAUOEHUKEUHSJKLUITUDUJ $.
  $}

  ${
    $d x z $.  $d y z $.
    dvelimalcasei.1 $e |- ( -. A. x x = y -> F/ x ph ) $.
    dvelimalcasei.2 $e |- ( -. A. x x = y -> F/ z ch ) $.
    dvelimalcasei.3 $e |- ( -. A. x x = y -> ( z = x -> ( ph -> ch ) ) ) $.
    dvelimalcasei.4 $e |- ( A. x x = y -> ( ps -> ch ) ) $.
    dvelimalcasei.5 $e |- A. z ph $.
    dvelimalcasei.6 $e |- A. x ps $.
    $( Eliminate a disjoint variable condition from a universally quantified
       statement using cases.  Inference form of ~ dvelimalcased .  See
       ~ axsepg2 for an example of its use.  (Contributed by BTernaryTau,
       31-Jul-2025.) $)
    dvelimalcasei $p |- A. x ch $=
      ( wal wtru nftru weq wnf adantl wi a1i wn nfvd dvelimalcased mptru ) CDMN
      ABCDEFDODEPDMZUAZNFUBUFADQNGRUFCFQNHRUFFDPACSSNIRUEBCSNJRAFMNKTBDMNLTUCUD
      $.
  $}

  ${
    $d x z $.  $d y z $.
    dvelimexcased.1 $e |- F/ x ph $.
    dvelimexcased.2 $e |- ( -. A. x x = y -> F/ z ph ) $.
    dvelimexcased.3 $e |- ( ( ph /\ -. A. x x = y ) -> F/ x ps ) $.
    dvelimexcased.4 $e |- ( ( ph /\ -. A. x x = y ) -> F/ z th ) $.
    dvelimexcased.5 $e |- ( ( ph /\ -. A. x x = y ) ->
        ( z = x -> ( ps -> th ) ) ) $.
    dvelimexcased.6 $e |- ( ( ph /\ A. x x = y ) -> ( ch -> th ) ) $.
    dvelimexcased.7 $e |- ( ph -> E. z ps ) $.
    dvelimexcased.8 $e |- ( ph -> E. x ch ) $.
    $( Eliminate a disjoint variable condition from an existentially quantified
       statement using cases.  (Contributed by BTernaryTau, 31-Jul-2025.) $)
    dvelimexcased $p |- ( ph -> E. x th ) $=
      ( wex wi wa nfan ex weq wal nfa1 eximd mpid wn nfv nfan1c cbvex1v pm2.61d
      nfna1 ) AEFUAZEUBZDEPZAUMCEPZUNOAUMUOUNQAUMRCDEAUMEHULEUCSMUDTUEAUMUFZBGP
      ZUNNAUPUQUNQAUPRBDGEUPAGUPGUGIUHAUPEHULEUKSJKLUITUEUJ $.
  $}

  ${
    $d x z $.  $d y z $.
    dvelimexcasei.1 $e |- ( -. A. x x = y -> F/ x ph ) $.
    dvelimexcasei.2 $e |- ( -. A. x x = y -> F/ z ch ) $.
    dvelimexcasei.3 $e |- ( -. A. x x = y -> ( z = x -> ( ph -> ch ) ) ) $.
    dvelimexcasei.4 $e |- ( A. x x = y -> ( ps -> ch ) ) $.
    dvelimexcasei.5 $e |- E. z ph $.
    dvelimexcasei.6 $e |- E. x ps $.
    $( Eliminate a disjoint variable condition from an existentially quantified
       statement using cases.  Inference form of ~ dvelimexcased .  See
       ~ axnulg for an example of its use.  (Contributed by BTernaryTau,
       31-Jul-2025.) $)
    dvelimexcasei $p |- E. x ch $=
      ( wex wtru nftru weq wnf adantl wi a1i wal wn nfvd dvelimexcased mptru )
      CDMNABCDEFDODEPDUAZUBZNFUCUGADQNGRUGCFQNHRUGFDPACSSNIRUFBCSNJRAFMNKTBDMNL
      TUDUE $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  ZF set theory
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( The intersection of the universal class with a class is itself.  A
     commuted form of ~ inv1 .  (Contributed by BTernaryTau, 24-Jun-2026.) $)
  inv2 $p |- ( _V i^i A ) = A $=
    ( cvv inv1 ineqcomi ) ABAACD $.

  $( There exists an element in a class excluding a singleton if and only if
     there exists an element in the original class not equal to the singleton
     element.  (Contributed by BTernaryTau, 15-Sep-2023.) $)
  exdifsn $p |- ( E. x x e. ( A \ { B } ) <-> E. x e. A x =/= B ) $=
    ( cv csn cdif wcel wex wne wa wrex eldifsn exbii df-rex bitr4i ) ADZBCEFGZA
    HPBGPCIZJZAHRABKQSAPBCLMRABNO $.


  ${
    $d w x y z $.
    $( Alternate proof of ~ axnul , proved from propositional calculus,
       ~ ax-gen , ~ ax-4 , ~ ax-6 , and ~ ax-rep .
       (Proof modification is discouraged.)  (New usage is discouraged.)
       (Contributed by BTernaryTau, 27-Mar-2026.) $)
    axnulALT2 $p |- E. x A. y -. y e. x $=
      ( vw vz wel wn wal wex wfal wa wb weq wi ax-rep fal spfalw pm2.21i ax-gen
      mto exgen mpg intnan nex nbn albii exbii mpbir ) BAEZFZBGZAHUHCDEZIAGZJZC
      HZKZBGZAHZULBALZMZBGZAHUQCIDABCNUTAUSBULURULIOIAOPSZQRTUAUJUPAUIUOBUNUHUM
      CULUKVAUBUCUDUEUFUG $.
    $( $j usage 'axnulALT2' avoids 'ax-5' 'ax-7' 'ax-8' 'ax-9' 'ax-10' 'ax-11'
       'ax-12' 'ax-13' 'ax-ext' 'ax-sep' 'ax-nul'; $)
  $}


  ${
    $d B x $.  $d C x $.  $d F x $.
    $( Condition for a function value to equal the intersection of an image
       that contains it.  (Contributed by BTernaryTau, 23-Jun-2026.) $)
    fnfvintima $p |- ( ( F Fn A /\ B C_ A /\ C e. B ) ->
        ( ( F ` C ) = |^| ( F " B ) <-> A. x e. B ( F ` C ) C_ ( F ` x ) ) ) $=
      ( wfn wss wcel w3a cfv cima cint wceq cv wral fnssintima 3adant3 imbitrid
      eqimss wb wa biimprd fnfvima intss1 syl jctird eqss imbitrrdi impbid ) EB
      FZCBGZDCHZIZDEJZECKZLZMZUNANEJGACOZUQUNUPGZUMURUNUPSUJUKUSURTULABCUNEPQZR
      UMURUSUPUNGZUAUQUMURUSVAUMUSURUTUBUMUNUOHVABCEDUCUNUOUDUEUFUNUPUGUHUI $.
  $}


  $( If an ordinal class is not a set, then it must be the proper class of all
     ordinals.  (Contributed by BTernaryTau, 9-Jun-2026.) $)
  ordprcon $p |- ( ( Ord A /\ -. A e. _V ) -> A = On ) $=
    ( word cvv wcel wn wa con0 wceq wo ordeleqon birani prcnel adantl orcnd ) A
    BZACDEZFAGDZAGHZOQRIPAJKPQEOAGLMN $.

  $( ` _om ` is either an ordinal set or the proper class of all ordinal sets,
     but not both.  This is a stronger version of ~ omon .  (Contributed by
     BTernaryTau, 25-Jan-2026.) $)
  xoromon $p |- ( _om e. On \/_ _om = On ) $=
    ( com con0 wcel wceq wo wa wn omon wi onprc prcnel ax-mp eleq1 mtbiri con2i
    wxo cvv imnan mpbi xor2 mpbir2an ) ABCZABDZPUBUCEUBUCFGZHUBUCGIUDUCUBUCUBBB
    CZBQCGUEGJBBKLABBMNOUBUCRSUBUCTUA $.
  $( $j usage 'xoromon' avoids 'ax-reg' 'ax-inf' 'ax-inf2'; $)

  $( The union (supremum) of a finite set of ordinals less than a nonzero
     ordinal class is an element of that ordinal class.  (Contributed by
     BTernaryTau, 15-Jan-2026.) $)
  fissorduni $p |- ( ( A e. Fin /\ A C_ B /\ ( Ord B /\ B =/= (/) ) ) ->
      U. A e. B ) $=
    ( cfn wcel wss word c0 wne wa w3a cuni wceq wi ord0eln0 biimpar uni0 eleq1i
    biimpri unieq con0 eleq1d syl5ibrcom 3ad2ant3 ordsson sylan2 adantrr adantr
    syl sstr 3adant1 simpl1 simpr ordunifi syl3anc ssel 3ad2ant2 syld pm2.61dne
    ex ) ACDZABEZBFZBGHZIZJZAKZBDZAGVDUTAGLZVGMZVAVDGBDZVIVBVJVCBNOVJVGVHGKZBDZ
    VLVJVKGBPQRVHVFVKBAGSUAUBUHUCVEAGHZVFADZVGVEVMVNVEVMIATEZUTVMVNVEVOVMVAVDVO
    UTVAVBVOVCVBVABTEVOBUDABTUIUEUFUJUGUTVAVDVMUKVEVMULAUMUNUSVAUTVNVGMVDABVFUO
    UPUQUR $.

  ${
    ordtypeon.1 $e |- F = OrdIso ( R , A ) $.
    $( A proper class with a set-like well-ordering is isomorphic to the proper
       class of all ordinal numbers.  (Contributed by BTernaryTau,
       9-Jun-2026.) $)
    ordtypeon $p |- ( ( R We A /\ R Se A /\ -. A e. _V ) ->
        F Isom _E , R ( On , A ) ) $=
      ( wwe wse cvv wcel wn w3a cdm wiso con0 ordtype 3adant3 wceq wb word oicl
      cep wa wf1o isof1o f1ovv 3syl notbid biimp3ar ordprcon sylancr isoeq4 syl
      mpbid ) ABEZABFZAGHZIZJZCKZATBCLZMATBCLZUMUNUSUPABCDNZOUQURMPZUSUTQUQURRU
      RGHZIZVBABCDSUMUNVDUPUMUNUAZVCUOVEUSURACUBVCUOQVAURATBCUCURACUDUEUFUGURUH
      UIURAMTBCUJUKUL $.
  $}

  ${
    $d A y $.  $d ph v x $.  $d D x y $.  $d D u v $.  $d R x y $.  $d S x y $.
    $d F x y $.  $d F u v $.  $d C u v x $.  $d S u v x $.
    fnrelpredd.1 $e |- ( ph -> F Fn A ) $.
    fnrelpredd.2 $e |- ( ph ->
        A. x e. A A. y e. A ( x R y <-> ( F ` x ) S ( F ` y ) ) ) $.
    fnrelpredd.3 $e |- ( ph -> C C_ A ) $.
    fnrelpredd.4 $e |- ( ph -> D e. A ) $.
    $( A function that preserves a relation also preserves predecessors.
       (Contributed by BTernaryTau, 16-Jul-2024.) $)
    fnrelpredd $p |- ( ph ->
        Pred ( S , ( F " C ) , ( F ` D ) ) = ( F " Pred ( R , C , D ) ) ) $=
      ( vu vv cfv wbr wceq wcel wa cima cpred crab wrex cab fvex dfpred3 elrabi
      cv anim1i reximi2 fvelimabd imbitrrid fveq2 breq1d biimpac adantll sylanb
      elrab breq1 rexlimiva jca2 biimpd adantrd wi w3a simpl a1i biimprcd simpr
      adantld 3jcad biimpri reximdv2 adantl sylcom impbid abbidv df-rab eqtr4di
      3impa syl6 eqtr4id wfun cdm wss wfn fnfun syl ssrab2 sstrid fndmd dfimafn
      sseqtrrd syl2anc eqtr4d dfpred3g sselda wral r19.21bi breq2 bibi12d rspcv
      wb breq2d adantr mpd syldan rabbidva eqtrd imaeq2d ) AIEUAZHFIPZUBZIBUIZI
      PZXMHQZBEUCZUAZIEGFUBZUAAXNNUIZIPZOUIZRZNXRUDZOUEZXSAXNYCXMHQZOXLUCZYFOXL
      HXMFIUFUGAYFYCXLSZYGTZOUEYHAYEYJOAYEYJAYEYIYGYEYIAYDNEUDZYDYDNXREYAXRSZYA
      ESZYDXQBYAEUHUJUKANDEYCIJLULZUMYDYGNXRYLYMYBXMHQZTZYDYGXQYOBYAEXOYARXPYBX
      MHXOYAIUNUOUSZYOYDYGYMYDYOYGYBYCXMHUTZUPUQURVAVBAYJYKYEAYIYKYGAYIYKYNVCVD
      YGYKYEVEYIYGYDYDNEXRYGYMYDTZYMYOYDVFYLYDTZYGYSYMYOYDYSYMVEYGYMYDVGVHYGYDY
      OYMYDYOYGYRVIVKYSYDVEYGYMYDVJVHVLYMYOYDYTYPYLYDYLYPYQVMUJWAWBVNVOVPVQVRYG
      OXLVSVTWCAIWDZXRIWEZWFXSYFRAIDWGUUAJDIWHWIAXRDUUBAXREDXQBEWJLWKADIJWLWNNO
      XRIWMWOWPAXTXRIAXTXOFGQZBEUCZXRAFDSZXTUUDRMBEGDFWQWIAUUCXQBEAXOESXODSZUUC
      XQXDZAEDXOLWRAUUFTXOCUIZGQZXPUUHIPZHQZXDZCDWSZUUGAUUMBDKWTAUUMUUGVEZUUFAU
      UEUUNMUULUUGCFDUUHFRZUUIUUCUUKXQUUHFXOGXAUUOUUJXMXPHUUHFIUNXEXBXCWIXFXGXH
      XIXJXKWP $.
  $}

  ${
    $d A x $.  $d B x y $.
    $( The cardinality function preserves predecessors.  (Contributed by
       BTernaryTau, 18-Jul-2024.) $)
    cardpred $p |- ( ( A C_ dom card /\ B e. dom card ) ->
        Pred ( _E , ( card " A ) , ( card ` B ) ) =
        ( card " Pred ( ~< , A , B ) ) ) $=
      ( vx vy ccrd cdm wss wcel wa csdm cep cv cen wbr con0 wrex cab cfv wral
      wf wfn cardf2 ffun funfnd mp1i wb epeli cardsdom2 bitr2id rgen2 a1i simpl
      fvex simpr fnrelpredd ) AEFZGZBUPHZIZCDUPABJKEDLZCLZMNDOPCQZOETZEUPUAUSCD
      UBVCEVBOEUCUDUEVAUTJNZVAERZUTERZKNZUFZDUPSCUPSUSVHCDUPUPVGVEVFHVAUPHUTUPH
      IVDVEVFUTEUMUGVAUTUHUIUJUKUQURULUQURUNUO $.
  $}

  ${
    $d A x y z $.
    $( Every nonempty class of numerable sets has a minimal element.
       (Contributed by BTernaryTau, 18-Jul-2024.) $)
    nummin $p |- ( ( A C_ dom card /\ A =/= (/) ) ->
        E. x e. A Pred ( ~< , A , x ) = (/) ) $=
      ( vy vz ccrd wss c0 wa cep cv wceq wrex wb wbr con0 ax-mp mpan wral wcel
      wn cdm wne cima cfv cpred csdm wfn cen cab wf cardf2 ffun funfnd fnimaeq0
      necon3bid biimprd imdistani fimass onssmin ssel anim12d ontri1 syl notbii
      wi epel bitr4di rgen2 r19.29r r19.26 bicom1 biimparc ralimi sylbir reximi
      sylancl adantl breq2 notbid ralbidv rexima adantr mpbid crab fvex dfpred3
      eqeq1i rabeq0 bitri rexbii sylibr ssel2 cardpred eqeq1d predss sstr bitrd
      sylancr syldan rexbidva ) BEUAZFZBGUBZHZEBUCZIAJZEUDZUEZGKZABLZBUFXFUEZGK
      ZABLZXDXBXEGUBZHZXJXBXCXNXBXNXCXBXEGBGEXAUGZXBXEGKBGKMCJZDJZUHNCOLDUIZOEU
      JZXPDCUKZXTEXSOEULUMPZXABEUNQUOUPUQXOXQXGINZTZCXERZABLZXJXOXQXRINZTZCXERZ
      DXELZYFXNYJXBXNXRXQFZCXERZYKYHMZCXERZHZDXELZYJXNYLDXELZYNDXERYPXEOFZXNYQX
      TYRYAXSOEBURPZDCXEUSQYMDCXEXEXRXESZXQXESZHZYKXQXRSZTZYHUUBXROSZXQOSZHZYKU
      UDMYRUUBUUGVEYSYRYTUUEUUAUUFXEOXRUTXEOXQUTVAPXRXQVBVCYGUUCDXQVFVDVGVHYLYN
      DXEVIVPYOYIDXEYOYKYMHZCXERYIYKYMCXEVJUUHYHCXEYMYHYKYKYHVKVLVMVNVOVCVQXBYJ
      YFMZXNXPXBUUIYBYIYEDAXABEXRXGKZYHYDCXEUUJYGYCXRXGXQIVRVSVTWAQWBWCXIYEABXI
      YCCXEWDZGKYEXHUUKGCXEIXGXFEWEWFWGYCCXEWHWIWJWKVCXBXJXMMXCXBXIXLABXBXFBSXF
      XASZXIXLMBXAXFWLXBUULHZXIEXKUCZGKZXLUUMXHUUNGBXFWMWNXBUUOXLMZUULXBXPXKXAF
      ZUUPYBXKBFXBUUQBUFXFWOXKBXAWPQXAXKEUNWRWBWQWSWTWBWC $.
  $}

  ${
    $d A x $.
    $( The Fundamental Theorem of Enumeration (see
~ https://sites.math.rutgers.edu/~~zeilberg/mamarim/mamarimPDF/enu.pdf ),
       extended to all sets.

       The expression ` U_ x e. A ( { x } X. B ) ` can be thought of as
       expressing an indexed disjoint union ` |_| x e. A B ` where each ` B `
       has its elements tagged with the set ` x ` that generated it.  See the
       comment directly before ~ undjudom for context on disjoint union as a
       representation of cardinal addition.

       This theorem is not limited to numerable sets, but it also does not
       depend on AC. See ~ 1enumcard for a version that uses the ` card `
       function, ~ 1enumkard for a version that uses the ` kard ` function ,
       and ~ 1enum for a version that uses an explicit sum of complex number
       1s.

       (Contributed by BTernaryTau, 26-Jun-2026.) $)
    1enumen $p |- ( A e. _V -> A ~~ U_ x e. A ( { x } X. 1o ) ) $=
      ( cvv wcel c1o cxp csn ciun cen xp1en ensymd iunid xpeq1i xpiundir eqtr3i
      cv breqtrdi ) BCDZBBEFZABAPGZEFHZIRSBBCJKABTHZEFSUAUBBEABLMABTENOQ $.
    $( $j usage '1enumen' avoids 'ax-ac' 'ax-ac2'; $)
  $}

  ${
    $d A x $.
    $( The Fundamental Theorem of Enumeration (see
~ https://sites.math.rutgers.edu/~~zeilberg/mamarim/mamarimPDF/enu.pdf ),
       extended to all sets.

       The expression ` U_ x e. A ( { x } X. B ) ` can be thought of as
       expressing an indexed disjoint union ` |_| x e. A B ` where each ` B `
       has its elements tagged with the set ` x ` that generated it.  See the
       comment directly before ~ undjudom for context on disjoint union as a
       representation of cardinal addition.

       This theorem does not depend on AC, but it is only meaningful for
       numerable sets.  See ~ 1enumen and ~ 1enumkard for versions that are
       meaningful for non-numerable sets, and see ~ 1enum for a version that
       uses an explicit sum of complex number 1s.

       (Contributed by BTernaryTau, 26-Jun-2026.) $)
    1enumcard $p |- ( A e. _V ->
        ( card ` A ) = ( card ` U_ x e. A ( { x } X. 1o ) ) ) $=
      ( cvv wcel cv csn c1o cxp ciun cen wbr ccrd cfv wceq 1enumen carden2b syl
      ) BCDBABAEFGHIZJKBLMRLMNABOBRPQ $.
      $( $j usage '1enumcard' avoids 'ax-ac' 'ax-ac2'; $)
  $}

  $( Value of the cumulative hierarchy of sets function at ` 1o ` .
     (Contributed by BTernaryTau, 24-Jan-2026.) $)
  r11 $p |- ( R1 ` 1o ) = 1o $=
    ( c1o cr1 cfv csuc cpw df-1o fveq2i cdm wlim wcel wceq wfun r1funlim simpri
    c0 0ellim r1sucg mp2b csn pw0 r10 pweqi df1o2 3eqtr4i 3eqtri ) ABCODZBCZOBC
    ZEZAAUFBFGBHZIZOUJJUGUIKBLUKMNUJPOQROEOSUIATUHOUAUBUCUDUE $.
  $( $j usage 'r11' avoids 'ax-rep' 'ax-reg'; $)

  $( Value of the cumulative hierarchy of sets function at ` 2o ` .
     (Contributed by BTernaryTau, 25-Jan-2026.) $)
  r12 $p |- ( R1 ` 2o ) = 2o $=
    ( c2o cr1 cfv c1o csuc cpw df-2o fveq2i wlim wcel wceq wfun r1funlim simpri
    cdm 1ellim r1sucg mp2b c0 csn cpr pwpw0 r11 df1o2 eqtri pweqi df2o2 3eqtr4i
    3eqtri ) ABCDEZBCZDBCZFZAAUJBGHBOZIZDUNJUKUMKBLUOMNUNPDQRSTZFSUPUAUMAUBULUP
    ULDUPUCUDUEUFUGUHUI $.
  $( $j usage 'r12' avoids 'ax-rep' 'ax-reg'; $)

  $( Each stage in the cumulative hierarchy is well-founded.  (Contributed by
     BTernaryTau, 19-Jan-2026.) $)
  r1wf $p |- ( R1 ` A ) e. U. ( R1 " On ) $=
    ( con0 wcel cr1 cfv cima cuni csuc cpw fvex pwid r1suc eleqtrrid r1elwf syl
    wn onwf c0 cdm wceq r1fnon fndmi eleq2i ndmfv sylnbir 0elon eqeltrdi sselid
    pm2.61i ) ABCZADEZDBFGZCZUJUKAHZDEZCUMUJUKUKIUOUKADJKALMUKUNNOUJPZBULUKQUPU
    KRBUJADSZCUKRTUQBABDUAUBUCADUDUEUFUGUHUI $.
  $( $j usage 'r1wf' avoids 'ax-reg'; $)

  $( An element of a well-founded set is well-founded.  (Contributed by
     BTernaryTau, 30-Dec-2025.) $)
  elwf $p |- ( ( A e. U. ( R1 " On ) /\ B e. A ) -> B e. U. ( R1 " On ) ) $=
    ( wcel cr1 con0 cima cuni wss elssuni uniwf sswf sylanb sylan2 ) BACADEFGZC
    ZBAGZHZBNCZBAIOPNCQRAJPBKLM $.
  $( $j usage 'elwf' avoids 'ax-rep' 'ax-reg'; $)

  $( Each set of the cumulative hierarchy is closed under membership.
     (Contributed by BTernaryTau, 30-Dec-2025.) $)
  r1elcl $p |- ( ( A e. ( R1 ` B ) /\ C e. A ) -> C e. ( R1 ` B ) ) $=
    ( cr1 cfv wcel wa crnk con0 cima cuni wi r1elwf rankelb syl rankr1ai elfvdm
    imp cdm r1fnon fndmi eleqtrdi ontr1 mpan2d adantr mpd sylan rankr1ag sylan2
    wb elwf ancoms syldan mpbird ) ABDEZFZCAFZGZCUOFZCHEZBFZURUTAHEZFZVAUPUQVCU
    PADIJKZFZUQVCLABMZCANORUPVCVALUQUPVCVBBFZVAABPUPBIFVCVGGVALUPBDSZIABDQZIDTU
    AUBUTVBBUCOUDUEUFUPUQCVDFZUSVAUJZUPVEUQVJVFACUKUGVJUPVKUPVJBVHFVKVICBUHUIUL
    UMUN $.
  $( $j usage 'r1elcl' avoids 'ax-reg'; $)

  ${
    $d A x $.
    $( Value of an alternate definition of the rank function.  Definition of
       [BellMachover] p. 478.  This variant of ~ rankval2 does not use
       Regularity, and so requires the assumption that ` A ` is in the range of
       ` R1 ` .  (Contributed by BTernaryTau, 19-Jan-2026.) $)
    rankval2b $p |- ( A e. U. ( R1 " On ) ->
        ( rank ` A ) = |^| { x e. On | A C_ ( R1 ` x ) } ) $=
      ( cr1 con0 cima cuni wcel crnk cfv csuc crab cint wss rankvalb cpw eleq2d
      cv r1suc fvex elpw2 bitrdi rabbiia inteqi eqtrdi ) BCDEFGBHIBAQZJCIZGZADK
      ZLBUECIZMZADKZLABNUHUKUGUJADUEDGZUGBUIOZGUJULUFUMBUERPBUIUECSTUAUBUCUD $.
    $( $j usage 'rankval2b' avoids 'ax-reg'; $)
  $}

  ${
    $d A x y $.
    $( The rank of a set is the supremum of the successors of the ranks of its
       members.  Exercise 9.1 of [Jech] p. 72.  Also a special case of Theorem
       7V(b) of [Enderton] p. 204.  This variant of ~ rankval4 does not use
       Regularity, and so requires the assumption that ` A ` is in the range of
       ` R1 ` .  (Contributed by BTernaryTau, 19-Jan-2026.) $)
    rankval4b $p |- ( A e. U. ( R1 " On ) ->
        ( rank ` A ) = U_ x e. A suc ( rank ` x ) ) $=
      ( vy cr1 con0 wcel crnk cfv cv wss wi rankon wral r1ord3 nfcv sylibr crab
      syl cint wceq cima cuni csuc ciun wal wa onsuci rgenw iunon mpan2 sylancr
      r1wf ssiun2 impel elwf rankidb sseldd ex alrimiv nfiu1 nffv dfssf rankssb
      mpsyl sylan ss2rabdv intss rankval2b intmin eqcomd 3sstr4d sstrd onsucssi
      mp1i rankelb imbitrdi ralrimiv iunss eqssd ) BDEUAUBZFZBGHZABAIZGHZUCZUDZ
      WAWBWFDHZGHZWFWGVTFZWABWGJZWBWHJWFULZWAWCBFZWCWGFZKZAUEWJWAWNAWAWLWMWAWLU
      FZWEDHZWGWCWAWEWFJZWPWGJZWLWAWEEFZWFEFZWQWRKWDWCLZUGZWAWSABMWTWSABXBUHABW
      EVTUIUJZWEWFNUKABWEUMUNWOWCVTFWCWPFBWCUOWCUPRUQURUSABWGABOAWFDADOABWEUTVA
      VBPBWGVCVDWAWGCIZDHJZCEQZSZWFXDJZCEQZSZWHWFWAXIXFJXGXJJWAXHXECEWAWTXDEFXH
      XEKXCWFXDNVEVFXIXFVGRWIWHXGTWAWKCWGVHVNWAXJWFWAWTXJWFTXCCWFEVIRVJVKVLWAWE
      WBJZABMWFWBJWAXKABWAWLWDWBFXKWCBVOWDWBXABLVMVPVQABWEWBVRPVS $.
    $( $j usage 'rankval4b' avoids 'ax-reg'; $)
  $}

  $( The rank of an ordinal number is itself.  (Contributed by BTernaryTau,
     3-Jul-2026.) $)
  onrankid $p |- ( A e. On <-> ( rank ` A ) = A ) $=
    ( con0 wcel cr1 cdm crnk cfv wceq r1fnon fndmi eleq2i rankonid bitr3i ) ABC
    ADEZCAFGAHNBABDIJKALM $.
  $( $j usage 'onrankid' avoids 'ax-reg'; $)

  ${
    $d B x $.  $d A x z $.
    $( If all elements in a finite well-founded set have a rank less than a
       limit ordinal, then the rank of that set is also less than the limit
       ordinal.  (Contributed by BTernaryTau, 19-Jan-2026.) $)
    rankfilimbi $p |- ( ( ( A e. Fin /\ A e. U. ( R1 " On ) ) /\
        ( A. x e. A ( rank ` x ) e. B /\ Lim B ) ) -> ( rank ` A ) e. B ) $=
      ( vz cfn wcel cr1 con0 cima cuni wa cv crnk cfv wral wlim wceq cvv adantl
      c0 csuc wrex cab wss word simpl limsuc ralbidv biimpd wb fvex sucex rgenw
      wne uniiunlem ax-mp imbitrdi impcom limord 0ellim ne0d ad2antll rankval4b
      jca w3a dfiun2 eqtrdi 3ad2ant1 abrexfi fissorduni syl3an1 eqeltrd syl3anc
      ciun 3adant1r ) BEFZBGHIJFZKZALZMNZCFZABOZCPZKZKVRDLVTUAZQABUBDUCZCUDZCUE
      ZCTUNZKZBMNZCFVRWDUFWDWGVRWCWBWGWCWBWECFZABOZWGWCWBWMWCWAWLABCVTUGUHUIWER
      FZABOWMWGUJWNABVTVSMUKULZUMADBWECRUOUPUQURSWCWJVRWBWCWHWICUSWCCTCUTVAVDVB
      VRWGWJVEWKWFJZCVRWGWKWPQZWJVQWQVPVQWKABWEVNWPABVCADBWEWOVFVGSVHVPWGWJWPCF
      ZVQVPWFEFWGWJWRADBWEVIWFCVJVKVOVLVM $.
    $( $j usage 'rankfilimbi' avoids 'ax-reg'; $)
  $}

  ${
    $d A x $.  $d B x $.
    $( The rank of a finite well-founded set is less than a limit ordinal iff
       the ranks of all of its elements are less than that limit ordinal.
       (Contributed by BTernaryTau, 22-Jan-2026.) $)
    rankfilimb $p |- ( ( A e. Fin /\ A e. U. ( R1 " On ) /\ Lim B ) ->
        ( ( rank ` A ) e. B <-> A. x e. A ( rank ` x ) e. B ) ) $=
      ( cfn wcel cr1 con0 cima cuni wlim w3a crnk cfv cv wi rankelb 3ad2ant2 wa
      wral word limord ordtr1 syl 3ad2ant3 syland expcomd ralrimdv 3impb 3com23
      rankfilimbi 3expia 3impa impbid ) BDEZBFGHIEZCJZKZBLMZCEZANZLMZCEZABSZUQU
      SVBABUQUTBEZUSVBUQVDVAUREZUSVBUOUNVDVEOUPUTBPQUPUNVEUSRVBOZUOUPCTVFCUAVAU
      RCUBUCUDUEUFUGUNUOUPVCUSOUNUORZUPVCUSVGVCUPUSVGVCUPUSABCUJUHUIUKULUM $.
    $( $j usage 'rankfilimbi' avoids 'ax-reg'; $)
  $}

  ${
    $d A w $.  $d B w $.  $d A a x $.  $d B x z $.  $d B a x y $.
    $( If all elements in a finite set appear in the cumulative hierarchy prior
       to a limit ordinal, then that set also appears in the cumulative
       hierarchy prior to the limit ordinal.  (Contributed by BTernaryTau,
       19-Jan-2026.) $)
    r1filimi $p |- ( ( A e. Fin /\ A. x e. A x e. U. ( R1 " B ) /\ Lim B ) ->
        A e. U. ( R1 " B ) ) $=
      ( va vy vz vw cfn wcel cv cr1 wral con0 cfv wi wb eluniima ax-mp biimtrid
      wrex cima cuni wlim w3a crnk wceq raleq eleq1 imbi12d imbi2d cdm r1funlim
      wfun simpli word wss limord ordsson syl sseld anim1d reximdv2 ralimdv vex
      tz9.12 sylibr syl6 vtoclg impcomd 3impib simp3 simp1 wa wex df-rex ordtr1
      rankr1ai sylani ancomsd exlimdv impcom 3adant1 rankfilimbi syl22anc fveq2
      csuc eleq2d limsuc biimpa rankidb 3ad2ant1 rspcedvdw syl3anc ) BHIZAJZKCU
      AUBZIZABLZCUCZUDZBKMUAUBZIZWSBUENZCIZBWPIZWNWRWSXBWNWSWRXBWSWQADJZLZXFXAI
      ZOZOWSWRXBOZODBHXFBUFZXIXJWSXKXGWRXHXBWQAXFBUGXFBXAUHUIUJWSXGWOEJZKNZIZEM
      TZAXFLZXHWSWQXOAXFWQXNECTZWSXOKUMZWQXQPXRKUKUCULUNZECWOKQRWSXNXNECMWSXLCI
      XLMIXNWSCMXLWSCUOZCMUPCUQZCURUSUTVAVBSVCXPXFXMIEMTZXHAEXFDVDVEXRXHYBPXSEM
      XFKQRVFVGVHVIVJZWNWRWSVKZWTWNXBWOUENZCIZABLZWSXDWNWRWSVLYCWRWSYGWNWSWRYGW
      SXTWRYGOYAXTWQYFABWQWOFJZKNIZFCTZXTYFXRWQYJPXSFCWOKQRYJYHCIZYIVMZFVNXTYFY
      IFCVOXTYLYFFXTYIYKYFYIXTYEYHIYKYFWOYHVQYEYHCVPVRVSVTSSVCUSWAWBYDABCWCWDXB
      WSXDUDZBGJZKNZIZGCTZXEYMYPBXCWFZKNZIZGYRCYNYRUFYOYSBYNYRKWEWGWSXDYRCIZXBW
      SXDUUACXCWHWIWBXBWSYTXDBWJWKWLXRXEYQPXSGCBKQRVFWM $.
    $( $j usage 'r1filimi' avoids 'ax-reg'; $)
  $}

  ${
    $d A x y $.  $d B x y $.
    $( A finite set appears in the cumulative hierarchy prior to a limit
       ordinal iff all of its elements appear in the cumulative hierarchy prior
       to that limit ordinal.  (Contributed by BTernaryTau, 22-Jan-2026.) $)
    r1filim $p |- ( ( A e. Fin /\ Lim B ) ->
        ( A e. U. ( R1 " B ) <-> A. x e. A x e. U. ( R1 " B ) ) ) $=
      ( vy cfn wcel wlim wa cr1 cima cuni cv wral cfv r1elcl expcom wb eluniima
      wrex ax-mp reximdv wfun cdm r1funlim simpli 3imtr4g com12 ralrimiv 3com23
      r1filimi 3expia impbid2 ) BEFZCGZHBICJKZFZALZUOFZABMZUPURABUQBFZUPURUTBDL
      ZINZFZDCSZUQVBFZDCSZUPURUTVCVEDCVCUTVEBVAUQOPUAIUBZUPVDQVGIUCGUDUEZDCBIRT
      VGURVFQVHDCUQIRTUFUGUHUMUNUSUPUMUSUNUPABCUJUIUKUL $.
    $( $j usage 'r1filim' avoids 'ax-reg'; $)
  $}

  $( Obsolete theorem, use ~ hffi instead.  Hereditarily finite sets are finite
     sets.  (Contributed by BTernaryTau, 30-Dec-2025.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  r1omfi $p |- U. ( R1 " _om ) C_ Fin $=
    ( vx cr1 com cima cuni cfn cv wcel chf df-hf eleq2i hffi sylbir ssriv ) ABC
    DEZFAGZOHPIHPFHIOPJKPLMN $.
  $( $j usage 'r1omfi' avoids 'ax-reg'; $)

  ${
    $d A x y $.
    $( A set is hereditarily finite iff it is finite and all of its elements
       are hereditarily finite.  (Contributed by BTernaryTau, 19-Jan-2026.) $)
    r1omhf $p |- ( A e. U. ( R1 " _om ) <->
        ( A e. Fin /\ A. x e. A x e. U. ( R1 " _om ) ) ) $=
      ( vy cr1 com cima cuni wcel cfn cv wral wa r1omfi sseli cfv wrex eluniima
      wb wlim ax-mp wfun cdm r1funlim simpli r1elcl reximi sylbir sylanb sylibr
      r19.41v ralrimiva jca limom r1filimi mp3an3 impbii ) BDEFGZHZBIHZAJZUQHZA
      BKZLURUSVBUQIBMNURVAABURUTBHZLUTCJZDOZHZCEPZVAURBVEHZCEPZVCVGDUAZURVIRVJD
      UBSUCUDZCEBDQTVIVCLVHVCLZCEPVGVHVCCEUJVLVFCEBVDUTUEUFUGUHVJVAVGRVKCEUTDQT
      UIUKULUSVBESURUMABEUNUOUP $.
    $( $j usage 'r1omhf' avoids 'ax-reg'; $)
  $}

  $( A set is a subset of the value of the cumulative hierarchy of sets
     function iff it is an element of the value at the successor.  (Contributed
     by BTernaryTau, 15-Jan-2026.) $)
  r1ssel $p |- ( B e. On -> ( A C_ ( R1 ` B ) <-> A e. ( R1 ` suc B ) ) ) $=
    ( con0 wcel csuc cr1 cfv cpw wss r1suc eleq2d fvex elpw2 bitr2di ) BCDZABEF
    GZDABFGZHZDAQIOPRABJKAQBFLMN $.
  $( $j usage 'r1ssel' avoids 'ax-reg'; $)

  ${
    $d w x y z $.
    $( Alternate proof of ~ axnul , proved from propositional calculus,
       ~ ax-gen , ~ ax-4 , ~ ax-5 , and ~ ax-inf2 .  (Contributed by
       BTernaryTau, 22-Jun-2025.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    axnulALT3 $p |- E. x A. y -. y e. x $=
      ( vz vw wel wn wal wa wex exsimpr weq wo wb ax-inf2 simpl eximii exlimiiv
      wi ) ACEZBAEFBGZHAIZTAICSTAJUASBCEDBEDAEDAKLMDGHBIRAGZHUACCABDNUAUBOPQ $.
    $( $j usage 'axnulALT3' avoids 'ax-6' 'ax-7' 'ax-8' 'ax-9' 'ax-10' 'ax-11'
       'ax-12' 'ax-13' 'ax-ext' 'ax-rep' 'ax-sep' 'ax-nul' 'ax-pow' 'ax-pr'
       'ax-un' 'ax-reg' 'ax-inf'; $)
  $}

  ${
    $d p t u v $.  $d p s w x z $.  $d p s w y z $.  $d n s t u w z $.
    $( Alternate proof of ~ axpr , proved from predicate calculus, ~ ax-rep ,
       and ~ ax-inf2 .  (Contributed by BTernaryTau, 26-Mar-2026.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    axprALT2 $p |- E. z A. w ( ( w = x \/ w = y ) -> w e. z ) $=
      ( vu vp vt vs vn vv wel wn wal wa wex weq wi elequ1 cv eximi w3a axprlem3
      wo wif wb elequ2 anbi12d cbvexvw elex2 anim2i sylbi 3ad2ant3 exlimiv ax-1
      ifptru biimprd anim12ii 19.37imv 3syl 3simpa notbid albidv cbvalvw bitrdi
      alnex anbi2i biimpi syl ifpfal jaod imbi2 syl5ibrcom alimdv mpi wrex wral
      eximdv ax-inf2 df-rex df-ral olc biimpr syl5 alimi equsalvw ralimi sylbir
      sylib sylanbr eximii r19.29r 3anass exbii sylbb2 exlimiiv ) EFKZGEKZLZGMZ
      GFKZEGKZNZGOZUAZEOZDAPZDBPZUCZDCKZQZDMZCOZFXEXIHFKZIHKZIOZXFXGUDZNZHOZUEZ
      DMZCOXLABCDIHFUBXEXTXKCXEXSXJDXEXJXSXHXRQXEXFXRXGXEXMXONZHOZXFXQQZHOXFXRQ
      XDYBEXCWPYBWSXCXMEHKZNZHOYBXBYEGHGHPWTXMXAYDGHFRGHEUFUGUHYEYAHYDXOXMIESHS
      UIUJTUKULUMYAYCHXMXFXMXOXPXMXFUNXOXPXFXOXFXGUOUPUQTXFXQHURUSXEXMXOLZNZHOZ
      XGXQQZHOXGXRQXEWPWSNZEOZYHXDYJEWPWSXCUTTYKXMXNLZIMZNZHOYHYJYNEHEHPZWPXMWS
      YMEHFRYOWSGHKZLZGMYMYOWRYQGYOWQYPEHGUFVAVBYQYLGIGIPYPXNGIHRVAVCVDUGUHYNYG
      HYNYGYMYFXMXNIVEVFVGTUKVHYGYIHXMXGXMYFXPXMXGUNYFXPXGXOXFXGVIUPUQTXGXQHURU
      SVJXIXRXHVKVLVMVQVNWSXCNZEFSZVOZXEFWSEYSVOZXCEYSVPZNZYTFYKWPWTJGKZJEKZJEP
      ZUCZUEZJMZNZGOZQEMZNUUCFFEGJVRYKUUAUULUUCWSEYSVSUULUUBUUAUULUUKEYSVPUUBUU
      KEYSVTUUKXCEYSUUJXBGUUIXAWTUUIUUFUUDQZJMXAUUHUUMJUUFUUGUUHUUDUUFUUEWAUUDU
      UGWBWCWDUUDXAJEJEGRWEWHUJTWFWGUJWIWJWSXCEYSWKWJYTWPYRNZEOXEYREYSVSXDUUNEW
      PWSXCWLWMWNWJWO $.
    $( $j usage 'axprALT2' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13' 'ax-ext'
       'ax-sep' 'ax-nul' 'ax-pow' 'ax-pr' 'ax-un' 'ax-reg' 'ax-inf'; $)
  $}

  $( Value of the cumulative hierarchy of sets function at ` _om ` .
     (Contributed by BTernaryTau, 25-Jan-2026.) $)
  r1omfv $p |- ( R1 ` _om ) = U. ( R1 " _om ) $=
    ( vx com cr1 cfv cv ciun cima cuni cvv wcel wlim wceq omex limom r1lim wfun
    mp2an cdm r1funlim simpli funiunfv ax-mp eqtri ) BCDZABAECDFZCBGHZBIJBKUDUE
    LMNABIOQCPZUEUFLUGCRKSTABCUAUBUC $.
  $( $j usage 'r1omfv' avoids 'ax-reg'; $)

  ${
    $d x y $.
    $( The rank function maps the universe onto the ordinals.  (Contributed by
       BTernaryTau, 23-Jun-2026.) $)
    rankfo $p |- rank : _V -onto-> On $=
      ( vy vx cvv con0 crnk wfo wf cfv wceq wrex wral cr1 cima cuni rankf unir1
      cv feq2i mpbi wcel vex cdm biimpi r1fnon fndmi eqcomi eleq2s eqcomd fveq2
      rankonid rspceeqv sylancr rgen dffo3 mpbir2an ) CDEFCDEGZAQZBQZEHZIBCJZAD
      KLDMNZDEGUPOVACDEPRSUTADUQDTZUQCTUQUQEHZIUTAUAVBVCUQVCUQIZUQLUBZDUQVETVDU
      QUJUCVEDDLUDUEUFUGUHBUQCUSVCUQURUQEUIUKULUMBACDEUNUO $.
  $}

  $( The rank function is a function on the universe.  (Contributed by
     BTernaryTau, 23-Jun-2026.) $)
  rankfn $p |- rank Fn _V $=
    ( cvv con0 crnk wfo wfn rankfo fofn ax-mp ) ABCDCAEFABCGH $.

  ${
    $d A x y $.
    $( If every element in a transitive class is finite, then every element is
       also hereditarily finite.  (Contributed by BTernaryTau, 24-Jan-2026.) $)
    trssfir1om $p |- ( ( Tr A /\ A C_ Fin ) -> A C_ U. ( R1 " _om ) ) $=
      ( vx vy wtr cfn wss wa cr1 com cima cuni wcel w3a weq eleq1w 3anbi1d wral
      cv wi a1d imbi12d ssel2 ancoms 3adant2 expcomd impcom 3adant3 simp2 simp3
      a1i trel 3jcad ralrimiv ralim syl5 r1omhf imbitrrdi setinds2 3expib com12
      jcad ssrdv ) ADZAEFZGZBAHIJKZBRZALZVEVGVFLZVHVCVDVIVHVCVDMZVISCRZALZVCVDM
      ZVKVFLZSZBCBCNZVJVMVIVNVPVHVLVCVDBCAOPBCVFOUAVOCVGQZVJVGELZVNCVGQZGVIVQVJ
      VRVSVJVRSVQVHVDVRVCVDVHVRAEVGUBUCUDUJVJVMCVGQVQVSVJVMCVGVJVKVGLZVLVCVDVHV
      CVTVLSZVDVCVHWAVCVTVHVLAVKVGUKUEUFUGVJVCVTVHVCVDUHTVJVDVTVHVCVDUITULUMVMV
      NCVGUNUOVACVGUPUQURUSUTVB $.
  $}

  ${
    $d H w x y z $.
    $( The class of all hereditarily finite sets is the only class with the
       property that all sets are members of it iff they are finite and all of
       their elements are members of it.  (Contributed by BTernaryTau,
       24-Jan-2026.) $)
    r1omhfb $p |- ( H = U. ( R1 " _om ) <->
        A. x ( x e. H <-> ( x e. Fin /\ A. y e. x y e. H ) ) ) $=
      ( vz vw cv wcel cfn wral wa wb wal r1omhf eleq2w2 wi wss alimi imim2i weq
      eleq1w cr1 com cima cuni wceq ralbidv anbi2d bibi12d mpbiri alrimiv biimp
      wtr simpr ralrid dftr5 sylibr simpl trssfir1om syl2anc syl biimpr imbi12d
      df-ss imbi2d ralim anim2d biimtrid adantl cbvraldva2 anbi12d syl9r sylcom
      ra4v spvv setinds2 ssrdv eqssd impbii ) CUAUBUCUDZUEZAFZCGZWAHGZBFZCGZBWA
      IZJZKZALZVTWHAVTWHWAVSGZWCWDVSGZBWAIZJZKBWAMVTWBWJWGWMACVSNVTWFWLWCVTWEWK
      BWABCVSNUFUGUHUIUJWICVSWIWBWGOZALZCVSPZWHWNAWBWGUKQWOCULZCHPZWPWOWFACIWQW
      OWFACWNWBWFOAWGWFWBWCWFUMRQUNABCUOUPWOWBWCOZALWRWNWSAWGWCWBWCWFUQRQACHVCU
      PCURUSUTWIWGWBOZALZVSCPWHWTAWBWGVAQXADVSCXADFZVSGZXBCGZOZOXAEFZVSGZXFCGZO
      ZOZDEDESZXEXIXAXKXCXGXDXHDEVSTDECTVBVDXJEXBIXAXIEXBIZXEXAXIEXBVMXLXCXBHGZ
      XHEXBIZJZXAXDXCXMXGEXBIZJXLXOEXBMXLXPXNXMXGXHEXBVEVFVGWTXOXDOADADSZWGXOWB
      XDXQWCXMWFXNADHTXQWEXHBEWAXBBESZWEXHKXQBECTVHXQXRUQVIVJADCTVBVNVKVLVOVPUT
      VQVR $.
  $}

  ${
    scotteqi.1 $e |- A = B $.
    $( Equality theorem for the Scott operation.  Inference form of ~ scotteq .
       (Contributed by BTernaryTau, 3-Jul-2026.) $)
    scotteqi $p |- Scott A = Scott B $=
      ( wceq cscott scotteq ax-mp ) ABDAEBEDCABFG $.
  $}

  ${
    $d A x y $.  $d B x y $.
    $( Membership in a Scott's trick set.  (Contributed by BTernaryTau,
       3-Jul-2026.) $)
    elscott $p |- ( A e. Scott B <->
        ( A e. B /\ A. x e. B ( rank ` A ) C_ ( rank ` x ) ) ) $=
      ( vy crnk cfv wss wral cscott wceq fveq2 sseq1d ralbidv df-scott elrab2
      cv ) DPZEFZAPEFZGZACHBEFZSGZACHDBCCIQBJZTUBACUCRUASQBEKLMDACNO $.
  $}

  ${
    $d A x y $.
    $( Alternate definition of a Scott's trick set.  (Contributed by
       BTernaryTau, 8-Jul-2026.) $)
    dfscott2 $p |- Scott A = { x e. A | ( rank ` x ) = |^| ( rank " A ) } $=
      ( vy cscott cv crnk cfv wss wral crab cima cint wceq df-scott cvv wcel wb
      wfn rankfn ssv fnfvintima mp3an12 rabbiia eqtr4i ) BDAEZFGZCEFGHCBIZABJUF
      FBKLMZABJACBNUHUGABFORBOHUEBPUHUGQSBTCOBUEFUAUBUCUD $.
  $}

  ${
    $d A x $.
    $( Alternate definition of a Scott's trick set.  (Contributed by
       BTernaryTau, 10-Jul-2026.) $)
    dfscott3 $p |- Scott A = ( A i^i ( R1 ` suc |^| ( rank " A ) ) ) $=
      ( vx cscott cv crnk cfv cima wceq cr1 cin wtru wcel wb wss cvv con0 ax-mp
      c0 wne bitr4di cint crab dfscott2 wn wa wfn rankfn fnfvima mp3an12 intss1
      csuc ssv syl ne0i cdm wfo wf rankfo fdmi ineq1i inv2 eqtri neeq1i biimpri
      imadisjlnd fimass oninton mpan ssrankr1 4syl mpbid biantrurd rankr1 eqcom
      fof vex adantl rabbi2dva mptru eqtr4i ) ACBDZEFZEAGZUAZHZBAUBZAWDUKIFZJZB
      AUCWHWFHKWEBAWGWAALZWAWGLZWEMKWIWJWDWBHZWEWIWJWAWDIFLUDZWJUEWKWIWLWJWIWDW
      BNZWLWIWBWCLZWMEOUFAONWIWNUGAULOAEWAUHUIWBWCUJUMWIARSZWCRSZWDPLZWMWLMAWAU
      NWOEAEUOZAJZRSWOWSARWSOAJAWROAOPEOPEUPOPEUQZUROPEVOQZUSUTAVAVBVCVDVEWCPNZ
      WPWQWTXBXAOPEAVFQWCVGVHWAWDBVPZVIVJVKVLWAWDXCVMTWBWDVNTVQVRVSVT $.
  $}

  ${
    $d A x $.  $d B x $.
    $( Membership in a Scott's trick set.  (Contributed by BTernaryTau,
       10-Jul-2026.) $)
    elscott2 $p |- ( A e. Scott B <->
        ( A e. B /\ ( rank ` A ) = |^| ( rank " B ) ) ) $=
      ( vx cv crnk cfv cima cint wceq cscott fveqeq2 dfscott2 elrab2 ) CDZEFEBG
      HZIAEFOICABBJNAOEKCBLM $.
  $}

  ${
    $d A x $.  $d B x $.
    $( The rank of an element in a Scott's trick set.  (Contributed by
       BTernaryTau, 8-Jul-2026.) $)
    elscottrank $p |- ( A e. Scott B -> ( rank ` A ) = |^| ( rank " B ) ) $=
      ( vx cscott wcel crnk cfv cima cint wceq fveqeq2 dfscott2 elrab2 simprbi
      cv ) ABDZEABEAFGFBHIZJZCOZFGQJRCABPSAQFKCBLMN $.
  $}

  $( Elements in a Scott's trick set have the same rank.  (Contributed by
     BTernaryTau, 9-Jul-2026.) $)
  elscottrankeq $p |- ( ( A e. Scott C /\ B e. Scott C ) ->
        ( rank ` A ) = ( rank ` B ) ) $=
    ( cscott wcel wa crnk cfv simpl simpr scottelrankd eqssd ) ACDZEZBMEZFZAGHB
    GHPCABNOIZNOJZKPCBARQKL $.

  ${
    $d A x $.  $d B x $.  $d C x $.
    $( Relationship between the ranks of an element in a Scott's trick set and
       an element in the input set.  (Contributed by BTernaryTau,
       3-Jul-2026.) $)
    elscottrankss $p |- ( ( A e. Scott B /\ C e. B ) ->
        ( rank ` A ) C_ ( rank ` C ) ) $=
      ( vx cscott wcel crnk cfv cv wss wral elscott simprbi wceq sseq2d rspccva
      fveq2 sylan ) ABEFZAGHZDIZGHZJZDBKZCBFTCGHZJZSABFUDDABLMUCUFDCBUACNUBUETU
      ACGQOPR $.
  $}

  $( If a member of the input set has the same rank as a member of the Scott's
     trick set, then it is also a member of the Scott's trick set.
     (Contributed by BTernaryTau, 10-Jul-2026.) $)
  scottrankeqel $p |- ( ( A e. Scott B /\ C e. B /\
      ( rank ` C ) = ( rank ` A ) ) -> C e. Scott B ) $=
    ( cscott wcel crnk wceq cima cint elscottrank 3ad2ant1 eqtr 3ad2antl3 mpdan
    cfv w3a wb elscott2 baib 3ad2ant2 mpbird ) ABDZEZCBEZCFOZAFOZGZPZCUBEZUEFBH
    IZGZUHUFUJGZUKUCUDULUGABJKUGUCULUKUDUEUFUJLMNUDUCUIUKQUGUIUDUKCBRSTUA $.

  $( If a member of the input set is not a member of the Scott's trick set,
     then its rank is greater than the rank of a member of the Scott's trick
     set.  (Contributed by BTernaryTau, 10-Jul-2026.) $)
  nelscottrankgt $p |- ( ( A e. Scott B /\ C e. B /\ -. C e. Scott B ) ->
      ( rank ` A ) e. ( rank ` C ) ) $=
    ( cscott wcel w3a crnk cfv wss wne elscottrankss 3adant3 wceq scottrankeqel
    wn wa 3expia necon3bd con0 rankon 3impia necomd wb onelpss mp2an sylanbrc )
    ABDZEZCBEZCUGEZOZFZAGHZCGHZIZUMUNJZUMUNEZUHUIUOUKABCKLULUNUMUHUIUKUNUMJUHUI
    PUJUNUMUHUIUNUMMUJABCNQRUAUBUMSEUNSEUQUOUPPUCATCTUMUNUDUEUF $.

  ${
    $d A x y $.
    $( Applying Scott's trick to a singleton leaves it unchanged.  (Contributed
       by BTernaryTau, 3-Jul-2026.) $)
    scottsn $p |- Scott { A } = { A } $=
      ( vx vy csn cscott cv crnk cfv wss wral crab df-scott wcel wa velsn eqtr3
      wceq syl2anb fveq2 eqimssd syl ralrimiva rabeqc eqtri ) ADZEBFZGHZCFZGHZI
      ZCUEJZBUEKUEBCUELUKBUEUFUEMZUJCUEULUHUEMZNUFUHQZUJULUFAQUHAQUNUMBAOCAOUFU
      HAPRUNUGUIUFUHGSTUAUBUCUD $.
  $}

  ${
    $d A x y $.
    $( Obsolete version of ~ scott0b as of 18-Jul-2026.  (Contributed by
       BTernaryTau, 3-Jul-2026.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    scott0bOLD $p |- ( A = (/) <-> Scott A = (/) ) $=
      ( vx vy c0 wceq crnk cfv wss wral cscott scott0OLD df-scott eqeq1i bitr4i
      cv crab ) ADEBOFGCOFGHCAIBAPZDEAJZDEBCAKRQDBCALMN $.
  $}

  ${
    $d A x $.
    $( The rank of a nonempty Scott's trick set.  (Contributed by BTernaryTau,
       8-Jul-2026.) $)
    rankscott $p |- ( A =/= (/) -> ( rank ` Scott A ) = suc |^| ( rank " A ) )
        $=
      ( vx c0 wne cv cscott wcel wex crnk cima cint csuc wceq scott0b necon3bii
      cfv n0 sylbb id scottrankd elscottrank suceqd eqtrd exlimiv syl ) ACDZBEZ
      AFZGZBHZUHIPZIAJKZLZMZUFUHCDUJACUHCANOBUHQRUIUNBUIUKUGIPZLUMUIAUGUISTUIUO
      ULUGAUAUBUCUDUE $.
  $}

  ${
    $d A x $.  $d B x $.
    $( An upper bound on the rank of a Scott's trick set.  (Contributed by
       BTernaryTau, 4-Jul-2026.) $)
    rankscottu $p |- ( A e. B -> ( rank ` Scott B ) C_ suc ( rank ` A ) ) $=
      ( vx cv cscott wcel wex crnk cfv csuc wi wa wceq id word rankon onordi c0
      wss sylbi scottrankd adantr elscottrankss ordsucsssuc mp2an sylib eqsstrd
      wb ex exlimiv neq0 con1bii scottex rankeq0 0ss sseq1 mpbiri a1d pm2.61i
      wn ) CDZBEZFZCGZABFZVBHIZAHIZJZSZKZVCVJCVCVEVIVCVELZVFVAHIZJZVHVCVFVMMVEV
      CBVAVCNUAUBVKVLVGSZVMVHSZVABAUCVLOVGOVNVOUHVLVAPQVGAPQVLVGUDUEUFUGUIUJVDU
      TZVIVEVPVBRMZVIVQVDCVBUKULVQVFRMZVIVBBUMUNVRVIRVHSVHUOVFRVHUPUQTTURUS $.
  $}

  $( Relationship between a Scott's trick set and the cumulative hierarchy.
     (Contributed by BTernaryTau, 3-Jul-2026.) $)
  scottssr1 $p |- ( A e. B -> Scott B C_ ( R1 ` suc ( rank ` A ) ) ) $=
    ( wcel cscott crnk cfv csuc wss rankscottu wb rankon onsuci scottex rankr1b
    cr1 con0 ax-mp sylibr ) ABCBDZEFAEFZGZHZSUAOFHZABIUAPCUCUBJTAKLSUABMNQR $.

  $( The Axiom of Choice implies that any set is numerable.  (Contributed by
     BTernaryTau, 3-Jul-2026.) $)
  acnum $p |- ( CHOICE -> ( A e. V -> A e. dom card ) ) $=
    ( wcel ccrd cdm wac cvv elex wceq dfac10 biimpi eleq2d imbitrrid ) ABCADEZC
    FAGCABHFNGAFNGIJKLM $.
  $( $j usage 'acnum' avoids 'ax-ac' 'ax-ac2'; $)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Ordinals 5 through 9
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $c 5o $.  $( The ordinal number 5 $)
  $c 6o $.  $( The ordinal number 6 $)
  $c 7o $.  $( The ordinal number 7 $)
  $c 8o $.  $( The ordinal number 8 $)
  $c 9o $.  $( The ordinal number 9 $)

  $( Extend the definition of a class to include the ordinal number 5. $)
  c5o $a class 5o $.

  $( Extend the definition of a class to include the ordinal number 6. $)
  c6o $a class 6o $.

  $( Extend the definition of a class to include the ordinal number 7. $)
  c7o $a class 7o $.

  $( Extend the definition of a class to include the ordinal number 8. $)
  c8o $a class 8o $.

  $( Extend the definition of a class to include the ordinal number 9. $)
  c9o $a class 9o $.

  $( Define the ordinal number 5.  (Contributed by BTernaryTau, 2-Sep-2026.) $)
  df-5o $a |- 5o = suc 4o $.

  $( Define the ordinal number 6.  (Contributed by BTernaryTau, 2-Sep-2026.) $)
  df-6o $a |- 6o = suc 5o $.

  $( Define the ordinal number 7.  (Contributed by BTernaryTau, 2-Sep-2026.) $)
  df-7o $a |- 7o = suc 6o $.

  $( Define the ordinal number 8.  (Contributed by BTernaryTau, 2-Sep-2026.) $)
  df-8o $a |- 8o = suc 7o $.

  $( Define the ordinal number 9.  (Contributed by BTernaryTau, 2-Sep-2026.) $)
  df-9o $a |- 9o = suc 8o $.

  $( Ordinal 5 is an ordinal number.  (Contributed by BTernaryTau,
     4-Sep-2026.) $)
  5on $p |- 5o e. On $=
    ( c5o c4o csuc con0 df-5o 4on onsuci eqeltri ) ABCDEBFGH $.

  $( Ordinal 6 is an ordinal number.  (Contributed by BTernaryTau,
     4-Sep-2026.) $)
  6on $p |- 6o e. On $=
    ( c6o c5o csuc con0 df-6o 5on onsuci eqeltri ) ABCDEBFGH $.

  $( Ordinal 7 is an ordinal number.  (Contributed by BTernaryTau,
     4-Sep-2026.) $)
  7on $p |- 7o e. On $=
    ( c7o c6o csuc con0 df-7o 6on onsuci eqeltri ) ABCDEBFGH $.

  $( Ordinal 8 is an ordinal number.  (Contributed by BTernaryTau,
     4-Sep-2026.) $)
  8on $p |- 8o e. On $=
    ( c8o c7o csuc con0 df-8o 7on onsuci eqeltri ) ABCDEBFGH $.

  $( Ordinal 9 is an ordinal number.  (Contributed by BTernaryTau,
     4-Sep-2026.) $)
  9on $p |- 9o e. On $=
    ( c9o c8o csuc con0 df-9o 8on onsuci eqeltri ) ABCDEBFGH $.

  $( The ordinal 5 is a natural number.  (Contributed by BTernaryTau,
     4-Sep-2026.) $)
  5onn $p |- 5o e. _om $=
    ( c5o c4o csuc com df-5o wcel 4onn peano2 ax-mp eqeltri ) ABCZDEBDFKDFGBHIJ
    $.

  $( The ordinal 6 is a natural number.  (Contributed by BTernaryTau,
     4-Sep-2026.) $)
  6onn $p |- 6o e. _om $=
    ( c6o c5o csuc com df-6o wcel 5onn peano2 ax-mp eqeltri ) ABCZDEBDFKDFGBHIJ
    $.

  $( The ordinal 7 is a natural number.  (Contributed by BTernaryTau,
     4-Sep-2026.) $)
  7onn $p |- 7o e. _om $=
    ( c7o c6o csuc com df-7o wcel 6onn peano2 ax-mp eqeltri ) ABCZDEBDFKDFGBHIJ
    $.

  $( The ordinal 8 is a natural number.  (Contributed by BTernaryTau,
     4-Sep-2026.) $)
  8onn $p |- 8o e. _om $=
    ( c8o c7o csuc com df-8o wcel 7onn peano2 ax-mp eqeltri ) ABCZDEBDFKDFGBHIJ
    $.

  $( The ordinal 9 is a natural number.  (Contributed by BTernaryTau,
     4-Sep-2026.) $)
  9onn $p |- 9o e. _om $=
    ( c9o c8o csuc com df-9o wcel 8onn peano2 ax-mp eqeltri ) ABCZDEBDFKDFGBHIJ
    $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Finitism
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d A n x $.
    $( Any proper class is literally infinite, in the sense that it contains
       subsets of arbitrarily large finite cardinality.  This proof holds
       regardless of whether the Axiom of Infinity is accepted or negated.
       (Contributed by BTernaryTau, 22-Jun-2025.) $)
    prcinf $p |- ( -. A e. _V -> A. n e. _om E. x ( x C_ A /\ x ~~ n ) ) $=
      ( cfn wcel cvv cv wss cen wbr wa wex com wral elex isinf nsyl5 ) BDEBFEAG
      ZBHRCGIJKALCMNBDOABCPQ $.
    $( $j usage 'prcinf' avoids 'ax-pow' 'ax-rep' 'ax-inf' 'ax-inf2'; $)
  $}

  ${
    $d ph u v $.  $d u v w x y z $.
    $( If all sets are finite, then the Axiom of Replacement becomes redundant.
       (Contributed by BTernaryTau, 12-Sep-2024.) $)
    fineqvrep $p |- ( Fin = _V -> ( A. w E. y A. z ( A. y ph -> z = y ) ->
        E. y A. z ( z e. y <-> E. w ( w e. x /\ A. y ph ) ) ) ) $=
      ( vu vv wal weq wex cfn cvv wel wa cv wcel cop nfv nfel2 nfan wi wb copab
      wceq wfun wmo funopab nfa1 mof albii bitr2i cima vex eleq2w2 mpbiri imafi
      sylan2 elexd nfopab nfex issetf eqabb exbii opabidw anbi2i bibi2i 3bitrri
      cab nfab dfima3 nfopab2 nfopab1 elequ1 opeq1 eleq1d anbi12d cbvexv1 opeq2
      anbi2d exbidv bitrid cbvabw eqtri eleq1i bitr4i sylibr sylanb expcom ) AC
      HZDCIUADHCJZEHZKLUDZDCMZEBMZWINZEJZUBZDHZCJZWKWIEDUCZUEZWLWSXAWIDUFZEHWKW
      IEDUGXBWJEWIDCACUHZUIUJUKXAWLNZWTBOZULZLPZWSXDXFKWLXAXEKPZXFKPWLXHXELPBUM
      BKLUNUOWTXEUPUQURWSWNEOZDOZQZWTPZNZEJZDVHZLPZXGXPCOZXOUDZCJWMXNUBZDHZCJWS
      CXOXNCDXMCEWNXLCWNCRCXKWTWIEDCXCUSSTUTVIVAXRXTCXNDXQVBVCXTWRCXSWQDXNWPWMX
      MWOEXLWIWNWIEDVDVEVCVFUJVCVGXFXOLXFFBMZFOZGOZQZWTPZNZFJZGVHXOFGWTXEVJYGXN
      GDYFDFYAYEDYADRDYDWTWIEDVKSTUTXNGRYGWNXIYCQZWTPZNZEJGDIZXNYFYJFEYAYEEYAER
      EYDWTWIEDVLSTYJFRFEIZYAWNYEYIFEBVMYLYDYHWTYBXIYCVNVOVPVQYKYJXMEYKYIXLWNYK
      YHXKWTYCXJXIVRVOVSVTWAWBWCWDWEWFWGWH $.
    $( $j usage 'fineqvrep' avoids 'ax-pow' 'ax-rep' 'ax-inf' 'ax-inf2'; $)
  $}

  ${
    $d w x z $.  $d v x y z $.
    $( If all sets are finite, then the Axiom of Power Sets becomes redundant.
       (Contributed by BTernaryTau, 12-Sep-2024.) $)
    fineqvpow $p |- ( Fin = _V ->
        E. y A. z ( A. w ( w e. z -> w e. x ) -> z e. y ) ) $=
      ( vv cfn cvv wceq cv wss wel wi wal wex wb cab wcel syl exbii sylib df-pw
      cpw vex eleq2w2 bitr3di mpbii elexd eqeltrrid elisset sseq1 eqabbw biimpr
      pwfi alimi eximi df-ss imbi1i albii ) FGHZCIZAIZJZCBKZLZCMZBNZDCKDAKLDMZV
      CLZCMZBNUSVCVBOZCMZBNZVFUSBIZEIZVAJZEPZHZBNZVLUSVPGQVRUSVPVAUBZGEVAUAUSVS
      FUSVAGQZVSFQZAUCUSVAFQVTWAAFGUDVAUMUEUFUGUHBVPGUIRVQVKBVOVBECVMVNUTVAUJUK
      STVKVEBVJVDCVCVBULUNUORVEVIBVDVHCVBVGVCDUTVAUPUQURST $.
    $( $j usage 'fineqvpow' avoids 'ax-pow' 'ax-rep' 'ax-inf' 'ax-inf2'; $)
  $}

  ${
    $d x y z $.  $d f w x $.  $d f g u v y z $.
    $( If all sets are finite, then the Axiom of Choice becomes redundant.  For
       a shorter proof using ~ ax-rep and ~ ax-pow , see ~ fineqvacALT .
       (Contributed by BTernaryTau, 21-Sep-2024.) $)
    fineqvac $p |- ( Fin = _V -> CHOICE ) $=
      ( vf vw vx vg vu vv cfn cvv wceq cv wss cdm wfn wa wex wcel c0 cun fneq2d
      anbi12d vy wal wac vex eleq2w2 mpbiri csn sseq2 dmeq exbidv weq ssid wfun
      vz fun0 funfn mpbi sseq1 fneq1 spcev mp2an wi cbvexvw ssun3 ad2antrr dmun
      0ex un0 eqtrdi eqtrid biimparc adantll syl2anc wne cop dmsnn0 elvv bitr3i
      uneq2 cxp anbi2i 19.42vv bitr4i 3ad2ant1 snssi ssequn2 sylib 3adant2 sneq
      w3a wb dmeqd dmsnop uneq2d 3ad2ant2 mpbird 3expia 3adant1 syl6an wn unss1
      adantl adantr eqsstrrd simpl eqid simpr fnunop 3ad2ant3 sylibrd snex unex
      a1i pm2.61d 3expa exlimivv sylbi pm2.61dane exlimiv findcard2 syl alrimiv
      ex df-ac sylibr ) GHIZAJZBJZKZYGYHLZMZNZAOZBUBUCYFYMBYFYHGPZYMYFYNYHHPBUD
      BGHUEUFYGCJZKZYGYOLZMZNZAOYGQKZYGQLZMZNZAOZYGUAJZKZYGUUELZMZNZAOZYGUUEUNJ
      ZUGZRZKZYGUUMLZMZNZAOZYMCUAUNYHYOQIZYSUUCAUUSYPYTYRUUBYOQYGUHUUSYQUUAYGYO
      QUISTUJCUAUKZYSUUIAUUTYPUUFYRUUHYOUUEYGUHUUTYQUUGYGYOUUEUISTUJYOUUMIZYSUU
      QAUVAYPUUNYRUUPYOUUMYGUHUVAYQUUOYGYOUUMUISTUJCBUKZYSYLAUVBYPYIYRYKYOYHYGU
      HUVBYQYJYGYOYHUISTUJQQKZQUUAMZUUDQULQUMUVDUOQUPUQUUCUVCUVDNAQVGYGQIYTUVCU
      UBUVDYGQQURUUAYGQUSTUTVAUUJUURVBUUEGPUUJDJZUUEKZUVEUUGMZNZDOUURUUIUVHADAD
      UKZUUFUVFUUHUVGYGUVEUUEURUUGYGUVEUSTVCUVHUURDUVHUURUULLZQUVHUVJQIZNUVEUUM
      KZUVEUUOMZUURUVFUVLUVGUVKUVEUUEUULVDZVEUVGUVKUVMUVFUVKUVMUVGUVKUUOUUGUVEU
      VKUUOUUGUVJRZUUGUUEUULVFZUVKUVOUUGQRUUGUVJQUUGVSUUGVHVIVJSVKVLUUQUVLUVMNA
      UVEDUDZUVIUUNUVLUUPUVMYGUVEUUMURUUOYGUVEUSTUTZVMUVHUVJQVNZNZUVHUUKEJZFJZV
      OZIZNZFOEOZUURUVTUVHUWDFOEOZNUWFUVSUWGUVHUVSUUKHHVTPUWGUUKVPEFUUKVQVRWAUV
      HUWDEFWBWCUWEUUREFUVFUVGUWDUURUVFUVGUWDWJZUWAUUGPZUURUWHUVLUWIUVMUURUVFUV
      GUVLUWDUVNWDUVGUWDUWIUVMVBUVFUVGUWDUWIUVMUVGUWDUWIWJUVMUVEUUGUWAUGZRZMZUV
      GUWIUWLUWDUWIUWLUVGUWIUWKUUGUVEUWIUWJUUGKUWKUUGIUWAUUGWEUWJUUGWFWGSVKWHUW
      DUVGUVMUWLWKUWIUWDUUOUWKUVEUWDUUOUVOUWKUVPUWDUVJUWJUUGUWDUVJUWCUGZLUWJUWD
      UULUWMUUKUWCWIZWLUWAUWBFUDZWMVIWNVJZSWOWPWQWRUVRWSUWHUVEUWMRZUUMKZUWIWTZU
      WQUUOMZUURUVFUWDUWRUVGUVFUWDNUWQUVEUULRZUUMUWDUXAUWQIUVFUWDUULUWMUVEUWNWN
      XBUVFUXAUUMKUWDUVEUUEUULXAXCXDWHUWHUWSUWQUWKMZUWTUVGUVFUWSUXBVBUWDUVGUWSU
      XBUVGUWSNZUUGUWKUVEUWQHHUWAUWBUWAHPUXCEUDXMUWBHPUXCUWOXMUVGUWSXEUWQXFUWKX
      FUVGUWSXGXHYCWOUWDUVFUWTUXBWKUVGUWDUUOUWKUWQUWPSXIXJUUQUWRUWTNAUWQUVEUWMU
      VQUWCXKXLYGUWQIUUNUWRUUPUWTYGUWQUUMURUUOYGUWQUSTUTWSXNXOXPXQXRXSXQXMXTYAY
      BBAYDYE $.
    $( $j usage 'fineqvac' avoids 'ax-pow' 'ax-rep' 'ax-inf' 'ax-inf2' 'ax-ac'
       'ax-ac2'; $)
  $}

  $( Shorter proof of ~ fineqvac using ~ ax-rep and ~ ax-pow .  (Contributed by
     BTernaryTau, 21-Sep-2024.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  fineqvacALT $p |- ( Fin = _V -> CHOICE ) $=
    ( vx cfn cvv wceq cdm wac wss ssv a1i finnum ssriv sseq1 mpbii eqssd dfac10
    ccrd cv sylibr ) BCDZPEZCDFSTCTCGSTHISBTGCTGABTAQJKBCTLMNOR $.
  $( $j usage 'fineqvacALT' avoids 'ax-inf' 'ax-inf2' 'ax-ac' 'ax-ac2'; $)

  $( If all sets are finite, then the class of all natural numbers equals the
     proper class of all ordinal numbers.  (Contributed by BTernaryTau,
     30-Dec-2025.) $)
  fineqvomon $p |- ( Fin = _V -> _om = On ) $=
    ( cfn cvv wceq com con0 cin onfin2 ineq2 inv1 eqtrdi eqtrid ) ABCZDEAFZEGLM
    EBFEABEHEIJK $.
  $( $j usage 'fineqvomon' avoids 'ax-pow' 'ax-rep' 'ax-inf' 'ax-inf2'; $)

  $( All sets are finite iff all ordinal sets are finite.  (Contributed by
     BTernaryTau, 25-Jan-2026.) $)
  fineqvomonb $p |- ( Fin = _V <-> _om = On ) $=
    ( cfn cvv wceq com con0 fineqvomon wcel wn onprc eleq1 mtbiri fineqv impbii
    sylib ) ABCZDECZFPDBGZHOPQEBGIDEBJKLNM $.
  $( $j usage 'fineqvomonb' avoids 'ax-inf' 'ax-inf2'; $)

  $( The class of all finite ordinals is a proper class iff all ordinal sets
     are finite.  (Contributed by BTernaryTau, 25-Jan-2026.) $)
  omprcomonb $p |- ( -. _om e. _V <-> _om = On ) $=
    ( com cvv wcel wn cfn wceq con0 fineqv fineqvomonb bitri ) ABCDEBFAGFHIJ $.
  $( $j usage 'omprcomonb' avoids 'ax-inf' 'ax-inf2'; $)

  ${
    $d x y z $.  $d A d w $.  $d B d w $.
    $( Lemma for ~ fineqvnttrclse .  (Contributed by BTernaryTau,
       12-Jan-2026.) $)
    fineqvnttrclselem1 $p |- ( B e. ( _om \ 1o ) ->
        U. { d e. On | ( A +o d ) = B } e. _om ) $=
      ( vw vx vy vz com c1o cdif wcel con0 cv coa wceq wa cfn syl wn c0 co crab
      cuni eldifi wss w3a eleq1 biimparc adantll 3adant2 nnarcl adantlr 3adant3
      wi wb mpbid simprd rabssdv nnon wreu oawordeu csn wex snfi mpbiri exlimiv
      reusn sylbi sylanl2 nnunifi syl2an2r oawordex sylan2 notbid biimpa ralnex
      wrex wral rabeq0 biimpri unieqd uni0 eqtrdi peano1 eqeltrdi sylbir expcom
      pm2.61dan simpl cvv csuc cmpt crdg df-oadd mpondm0 nsyl5 eldifsnneq df1o2
      cfv difeq2i eleq2s eqtr2 stoic1b syl2anr ralrimivw ex pm2.61d ) BHIJZKZAL
      KZACMZNUAZBOZCLUBZUCZHKZXIBHKZXJXPUNBHIUDXJXQXPXJXQPZABUEZXPXRXNHUEXSXNQK
      ZXPXRXMCLHXRXKLKZXMUFZAHKZXKHKZYBXLHKZYCYDPZXRXMYEYAXQXMYEXJXMYEXQXLBHUGU
      HUIUJXRYAYEYFUOZXMXJYAYGXQAXKUKULUMUPUQURXQXJBLKZXSXTBUSZXJYHPXSPXMCLUTZX
      TCABVAYJXNDMZVBZOZDVCXTXMCDLVGYMXTDYMXTYLQKYKVDXNYLQUGVEVFVHRVIXNVJVKXRXS
      SZPXMCLVQZSZXPXRYNYPXRXSYOXQXJYHXSYOUOYICABVLVMVNVOYPXMSZCLVRZXPXMCLVPYRX
      OTHYRXOTUCTYRXNTXNTOYRXMCLVSVTWAWBWCWDWEZWFRWHWGRXIXJSZXPXIYTPZYRXPUUAYQC
      LYTXLTOZBTOZSZYQXIXJYAPXJUUBXJYAWIEFFMGWJGMWKWLEMWMWSNAXKLLEFGWNWOWPUUDBH
      TVBZJXHBHTWQIUUEHWRWTXAXMUUBUUCXLBTXBXCXDXEYSRXFXG $.
    $( $j usage 'fineqvnttrclselem1' avoids 'ax-inf' 'ax-inf2'; $)
  $}

  ${
    $d B v $.  $d F d $.  $d N v $.  $d A d x $.  $d A d v $.  $d B d x $.
    fineqvnttrclselem2.1 $e |- F =
        ( v e. suc suc N |-> U. { d e. On | ( v +o d ) = B } ) $.
    $( Lemma for ~ fineqvnttrclse .  (Contributed by BTernaryTau,
       12-Jan-2026.) $)
    fineqvnttrclselem2 $p |- ( ( B e. ( _om \ 1o ) /\ N e. B /\
        A e. suc suc N ) -> ( A +o ( F ` A ) ) = B ) $=
      ( vx com wcel con0 coa co wceq cv wa cuni sylan wss syl c1o cdif csuc w3a
      crab eldifi ancoms 3adant3 oveq1 eqeq1d rabbidv unieqd fineqvnttrclselem1
      cfv elnn simp3 3ad2ant1 fvmptd3 syld3an2 wreu nnon onelon onsuc stoic3 wb
      simpl jca onsssuc mpbird word nnord ordsucss 3syl sstrd oawordeu syl21anc
      wi imp csn wex reusn unieq unisnv eqtrdi vsnid eleq2 mpbiri eqeltrd sylbi
      exlimiv oveq2 elrab sylib simprd ) CIUAUBJZECJZBEUCZUCZJZUDZBDUNZKJZBXALM
      ZCNZWTXABFOZLMZCNZFKUEZJXBXDPWTXAXHQZXHWOEIJZWPWSXAXINWOWPXJWSWOCIJZWPXJC
      IUAUFZWPXKXJECUOUGRUHWOXJWSUDABAOZXELMZCNZFKUEZQXIWRDIGXMBNZXPXHXQXOXGFKX
      QXNXFCXMBXELUIUJUKULWOXJWSUPWOXJXIIJWSBCFUMUQURUSWTXGFKUTZXIXHJZWTBKJZCKJ
      ZBCSXRWOWPWQKJZWSXTWOYAWPYBWOXKYAXLCVATZYAWPPEKJYBCEVBEVCTRZYBWRKJWSXTWQV
      CWRBVBRZVDWOWPYAWSYCUQWTBWQCWTBWQSZWSWOWPWSUPWTXTYBPZYFWSVEWOWPYBWSYGYDYB
      WSPXTYBYEYBWSVFVGVDBWQVHTVIWOWPWQCSZWSWOWPYHWOXKCVJWPYHVQXLCVKECVLVMVRUHV
      NFBCVOVPXRXHHOZVSZNZHVTXSXGFHKWAYKXSHYKXIYIXHYKXIYJQYIXHYJWBHWCWDYKYIXHJY
      IYJJHWEXHYJYIWFWGWHWJWITWHXGXDFXAKXEXANXFXCCXEXABLWKUJWLWMWN $.
    $( $j usage 'fineqvnttrclselem2' avoids 'ax-inf' 'ax-inf2'; $)
  $}

  ${
    $d F d $.  $d A x y $.  $d F x y $.  $d N a v $.  $d a x y $.
    $d B a d v $.
    fineqvnttrclselem3.1 $e |- R = { <. x , y >. | ( x e. A /\ x = suc y ) } $.
    fineqvnttrclselem3.2 $e |- A = _om $.
    fineqvnttrclselem3.3 $e |- F =
        ( v e. suc suc N |-> U. { d e. On | ( v +o d ) = B } ) $.
    $( Lemma for ~ fineqvnttrclse .  (Contributed by BTernaryTau,
       12-Jan-2026.) $)
    fineqvnttrclselem3 $p |- ( ( B e. ( _om \ 1o ) /\ N e. B ) ->
        A. a e. suc N ( F ` a ) R ( F ` suc a ) ) $=
      ( com wcel wa csuc wceq coa co c1o cdif cfv wbr w3a con0 crab cuni eqeq1d
      cv oveq1 rabbidv unieqd elelsuc adantl fineqvnttrclselem1 fvmptd3 eqeltrd
      adantr 3adant2 eleqtrrdi fineqvnttrclselem2 eldifi elnn ancoms sylan word
      syl3an3 wb peano2 nnord ordsucelsuc biimpa stoic3 syld3an3 eqtr4d 3adant3
      3syl 3adant1 3ad2ant1 syld3an2 nnacom suceqd nnasuc 3eqtr4d eqeq2d nnacan
      syl bitr3d syl3anc mpbid eleq1 eqeq1 anbi12d suceq anbi2d sylanbrc 3expia
      fvex brab ralrimiv ) ENUAUBOZHEOZPZIUJZGUCZXEQZGUCZFUDZIHQZXBXCXEXJOZXIXB
      XCXKUEZXFDOZXFXHQZRZXIXLXFNDXBXKXFNOZXCXBXKPZXFXEJUJZSTZERZJUFUGZUHZNXQCX
      ECUJZXRSTZERZJUFUGZUHZYBXJQZGNMYCXERZYFYAYIYEXTJUFYIYDXSEYCXEXRSUKUIULUMX
      KXEYHOZXBXEXJUNZUOXBYBNOXKXEEJUPUSZUQYLURUTZLVAXLXEXFSTZXGXHSTZRZXOXLYNEY
      OXKXBXCYJYNERYKCXEEGHJMVBVHXBXCXKXGYHOZYOERXBXCHNOZXKYQXBENOZXCYRENUAVCXC
      YSYRHEVDVEVFZYRXKYQYRXJNOZXJVGXKYQVIHVJZXJVKXEXJVLVRVMZVNCXGEGHJMVBVOVPXL
      XENOZXPXHNOZYPXOVIXBXCUUAXKUUDXDYRUUAYTUUBWHXKUUAUUDXEXJVDVEVNYMXBYRXCXKU
      UEXBXCYRXKYTVQXBYRXKUEZXHXGXRSTZERZJUFUGZUHZNUUFCXGYGUUJYHGNMYCXGRZYFUUIU
      UKYEUUHJUFUUKYDUUGEYCXGXRSUKUIULUMYRXKYQXBUUCVSXBYRUUJNOXKXGEJUPVTZUQUULU
      RWAUUDXPUUEUEZYNXEXNSTZRZYPXOUUMUUNYOYNUUDUUEUUNYORXPUUDUUEPZUUNXHXGSTZYO
      UUPXEXHSTZQXHXESTZQZUUNUUQUUPUURUUSXEXHWBWCXEXHWDUUEUUDUUQUUTRXHXEWDVEWEU
      UDXGNOUUEYOUUQRXEVJXGXHWBVFVPUTWFUUEUUDXPXNNOUUOXOVIXHVJXEXFXNWGVHWIWJWKA
      UJZDOZUVABUJZQZRZPXMXFUVDRZPXMXOPABXFXHFXEGWSXGGWSUVAXFRUVBXMUVEUVFUVAXFD
      WLUVAXFUVDWMWNUVCXHRZUVFXOXMUVGUVDXNXFUVCXHWOWFWPKWTWQWRXA $.
    $( $j usage 'fineqvnttrclselem3' avoids 'ax-inf' 'ax-inf2'; $)
  $}

  ${
    $d A t u $.  $d R w z $.  $d R t u $.  $d d s u $.  $d R a f n $.
    $d A w x y z $.  $d a d e n u v $.  $d a d f n u v $.  $d a d n u v x y $.
    fineqvnttrclse.1 $e |- R = { <. x , y >. | ( x e. A /\ x = suc y ) } $.
    fineqvnttrclse.2 $e |- A = _om $.
    $( A counterexample demonstrating that ~ ttrclse does not hold when all
       sets are finite.  (Contributed by BTernaryTau, 12-Jan-2026.) $)
    fineqvnttrclse $p |- ( Fin = _V -> ( R Se A /\ -. t++ ( R |` A ) Se A ) )
        $=
      ( vu vn vd vw cvv wceq cv wcel com c1o c0 wa coa con0 vt vf va vv vs cres
      ve vz cfn cttrcl wse wn crab wral cdif ominf 1onn nnfi ax-mp difinf mp2an
      wbr eleq2 mtbii wss difss sseqtrri csuc wfn cfv w3a wex wne eldifi eldifn
      wrex 0lt1o eleq1 mpbiri necon3bi nnsuc eqcom rexbii sylib syl2anc co cuni
      syl cmpt sucexg sucex mptex fineqvnttrclselem1 elexd ralrimivw eqid fnmpt
      elv a1i adantr word nnon eloni wb ordeq adantl mpbird 0elsuc simpl eqeq1d
      oveq1 rabbidv unieqd fvmptd3 csn rabbiia rabsn eqtrid unisnv eqtrdi eqtrd
      weq oa0r sucid ad2antlr oa0 oveq2 syl5ibrcom wreu 3ad2ant1 unieqi jca vex
      0elon fveq1 anbi12d sylibr cdm con3i df-se ssid mpan2 simp2 simp3 reu2eqd
      oawordeu anidms 3expia impbid bitr4d rabbidva 0ex unisn eqtri sylan mpbii
      adantlr cbvrabv mpteq2i fineqvnttrclselem3 sylan2 fneq1 breq12d 3anbi123d
      3jca ralbidv spcedv ex reximdv mpd brttrcl2 wrel relopabiv copab dmopabss
      dmeqi eqsstri relssres ttrcleq breqi rgen ssrab mpbir2an mpan wi eleqtrri
      ssexg peano1 breq2 eleq1d rspcv sylnibr eleq1w eqeq1 eqeq2d anbi2d bilani
      3syl suceq brab biimpri impbii rabbia2 cab weu eueqi euabex rabssab ssexi
      eqeltri rgenw mpbir jctil ) UIKLZCDCUFZUJZUKZULCDUKZUXNGMZUAMZUXPVBZGCUMZ
      KNZUACUNZUXQUXNOPUOZKNZULUXSQUXPVBZGCUMZKNZULUYDULUXNUYEUINZUYFOUINULPUIN
      ZUYJULUPPONUYKUQPURUSOPUTVAUIKUYEVCVDUYIUYFUYEUYHVEZUYIUYFUYLUYECVEUYGGUY
      EUNUYEOCOPVFFVGUYGGUYEUXSUYENZUXSQDUJZVBZUYGUYMUBMZHMZVHZVHZVIZQUYPVJZUXS
      LZUYRUYPVJZQLZRZUCMZUYPVJZVUFVHZUYPVJZDVBZUCUYRUNZVKZUBVLZHOVPZUYOUYMUYRU
      XSLZHOVPZVUNUYMUXSONZUXSQVMZVUPUXSOPVNZUYMUXSPNZULVURUXSOPVOVUTUXSQUXSQLV
      UTQPNVQUXSQPVRVSVTWHVUQVURRUXSUYRLZHOVPVUPHUXSWAVVAVUOHOUXSUYRWBWCWDWEUYM
      VUOVUMHOUYMVUOVUMUYMVUORZVULUDUYSUDMZIMZSWFZUXSLZITUMZWGZWIZUYSVIZQVVIVJZ
      UXSLZUYRVVIVJZQLZRZVUFVVIVJZVUHVVIVJZDVBZUCUYRUNZVKUBKVVIVVIKNVVBUDUYSVVH
      UYRUYRKNHUYQKWJWRZWKWLWSVVBVVJVVOVVSUYMVVJVUOUYMVVHKNZUDUYSUNVVJUYMVWAUDU
      YSUYMVVHOVVCUXSIWMWNWOUDUYSVVHVVIKVVIWPZWQWHWTVVBVVLVVNVVBQUYSNZUYMVVLVVB
      UYRXAZVWCVVBVWDUXSXAZUYMVWEVUOUYMUXSTNZVWEUYMVUQVWFVUSUXSXBWHZUXSXCWHWTVU
      OVWDVWEXDUYMUYRUXSXEXFXGUYRXHWHUYMVUOXIVWCUYMRZVVKQVVDSWFZUXSLZITUMZWGZUX
      SVWHUDQVVHVWLUYSVVIOVWBVVCQLZVVGVWKVWMVVFVWJITVWMVVEVWIUXSVVCQVVDSXKXJXLX
      MVWCUYMXIUYMVWLONVWCQUXSIWMXFXNUYMVWLUXSLZVWCUYMVWFVWNVWGVWFVWLUXSXOZWGUX
      SVWFVWKVWOVWFVWKIGYBZITUMVWOVWJVWPITVVDTNZVWIVVDUXSVVDYCXJXPITUXSXQXRXMGX
      SXTWHXFYAWEVVBVVMUYRVVDSWFZUXSLZITUMZWGZQUYMVVMVXALVUOUYMUDUYRVVHVXAUYSVV
      IOVWBVVCUYRLZVVGVWTVXBVVFVWSITVXBVVEVWRUXSVVCUYRVVDSXKXJXLXMUYRUYSNUYMUYR
      VVTYDWSUYRUXSIWMXNWTUYMVWFVUOVXAQLVWGVWFVUORZVXAVVDQLZITUMZWGZQVXCVWTVXEV
      XCVWSVXDITVXCVWQRVWSUXSVVDSWFZUXSLZVXDVUOVWSVXHXDVWFVWQVUOVWRVXGUXSUYRUXS
      VVDSXKXJYEVWFVWQVXDVXHXDVUOVWFVWQRZVXDVXHVXIVXHVXDUXSQSWFZUXSLZVWFVXKVWQU
      XSYFZWTVXDVXGVXJUXSVVDQUXSSYGXJYHVWFVWQVXHVXDVWFVWQVXHVKZUXSUEMZSWFZUXSLZ
      VXHVXKUETVVDQUEIYBVXOVXGUXSVXNVVDUXSSYGXJVXNQLVXOVXJUXSVXNQUXSSYGXJVWFVWQ
      VXPUETYIZVXHVWFVXQVWFVWFRUXSUXSVEVXQUXSUUAUEUXSUXSUUFUUBUUGYJVWFVWQVXHUUC
      QTNZVXMYNWSVWFVWQVXHUUDVWFVWQVXKVXHVXLYJUUEUUHUUIUUQUUJUUKXMVXFQXOZWGQVXE
      VXSVXRVXEVXSLYNITQXQUSYKQUULUUMUUNXTUUOYAYLVUOUYMUYQUXSNZVVSVUOUYQUYRNVXT
      UYQHYMYDUYRUXSUYQVCUUPABUDCUXSDVVIUYQUCUGEFUDUYSVVHVVCUGMZSWFZUXSLZUGTUMZ
      WGVVGVYDVVFVYCIUGTIUGYBVVEVYBUXSVVDVYAVVCSYGXJUURYKUUSUUTUVAUVEUYPVVILZUY
      TVVJVUEVVOVUKVVSUYSUYPVVIUVBVYEVUBVVLVUDVVNVYEVUAVVKUXSQUYPVVIYOXJVYEVUCV
      VMQUYRUYPVVIYOXJYPVYEVUJVVRUCUYRVYEVUGVVPVUIVVQDVUFUYPVVIYOVUHUYPVVIYOUVC
      UVFUVDUVGUVHUVIUVJUXSQDUBHUCUVKYQUXSQUXPUYNUXODLZUXPUYNLDUVLDYRZCVEVYFAMZ
      CNZVYHBMZVHZLZRZABDEUVMVYGVYMABUVNZYRCDVYNEUVPVYLABCUVOUVQDCUVRVAUXODUVSU
      SUVTYQUWAUYGGCUYEUWBUWCUYEUYHKUWGUWDYSUYDUYIQCNUYDUYIUWEQOCUWHFUWFUYCUYIU
      AQCUXTQLZUYBUYHKVYOUYAUYGGCUXTQUXSUXPUWIXLUWJUWKUSYSUWRUAGCUXPYTUWLUXRJMZ
      UHMZDVBZJCUMZKNZUHCUNVYTUHCVYSVYPVYQVHZLZJCUMZKVYRWUBJCCVYPCNZVYRRWUDWUBR
      ZVYRWUEWUDVYMWUDVYPVYKLZRWUEABVYPVYQDJYMUHYMZAJYBVYIWUDVYLWUFAJCUWMVYHVYP
      VYKUWNYPBUHYBZWUFWUBWUDWUHVYKWUAVYPVYJVYQUWSUWOUWPEUWTZUWQWUEWUDVYRWUDWUB
      XIVYRWUEWUIUXAYLUXBUXCWUCWUBJUXDZWUBJUXEWUJKNJWUAVYQWUGWKUXFWUBJUXGUSWUBJ
      CUXHUXIUXJUXKUHJCDYTUXLUXM $.
    $( $j usage 'fineqvnttrclse' avoids 'ax-inf' 'ax-inf2'; $)
  $}

  ${
    $d A w z $.  $d F w x y z $.
    fineqvinfep.1 $e |- A = { ( F ` (/) ) } $.
    $( A counterexample demonstrating that ~ tz9.1 does not hold when all sets
       are finite and an infinite descending ` e. ` -chain exists.
       (Contributed by BTernaryTau, 18-Feb-2026.) $)
    fineqvinfep $p |- ( ( Fin = _V /\ F : _om -1-1-> _V /\ A. x e. _om
        ( F ` suc x ) e. ( F ` x ) ) -> -. E. y ( A C_ y /\ Tr y ) ) $=
      ( vw cfn cvv wceq com cv cfv wcel wss wa wn wi c0 fveq2 eleq1d vz wf1 w3a
      csuc wral wtr vex eleq2 mpbiri 3ad2ant1 cima simp2 csn fvex snid eleqtrri
      sseldd 3simpb suceq fveq2d eleq12d rspcv trel expd com12 syl6 impd finds2
      a1i syl5 ralrimiv 3expib adantl wb wfun cdm f1fun f1dm eqimsscd funimass4
      syl2anc adantr sylibrd ominf crn wfn f1fn fnima f1ssr mpdan sylan2 ancoms
      syl f1fi mto imnani ssfi con3i imnan sylibr syld 3adant1 mt2d nexdv ) GHI
      ZJHDUBZAKZUDZDLZXGDLZMZAJUEZUCZCBKZNZXNUFZOZBXMXQXNGMZXEXFXRXLXEXRXNHMBUG
      GHXNUHUIUJXFXLXQXRPZQXEXFXLOZXQDJUKZXNNZXSXTXQFKZDLZXNMZFJUEZYBXLXQYFQXFX
      LXOXPYFXLXOXPUCZYEFJYCJMYGYEYERDLZXNMUAKZDLZXNMZYIUDZDLZXNMZYGFUAYCRIYDYH
      XNYCRDSTYCYIIYDYJXNYCYIDSTYCYLIYDYMXNYCYLDSTYGCXNYHXLXOXPULYHCMYGYHYHUMCY
      HRDUNUOEUPVIUQYGXLXPOYIJMZYKYNQZXLXOXPURYOXLXPYPYOXLYMYJMZXPYPQXKYQAYIJXG
      YIIZXIYMXJYJYRXHYLDXGYIUSUTXGYIDSVAVBXPYQYPXPYQYKYNXNYMYJVCVDVEVFVGVJVHVE
      VKVLVMXFYBYFVNZXLXFDVOJDVPZNYSJHDVQXFYTJJHDVRVSFJXNDVTWAWBWCXFYBXSQZXLXFY
      AGMZPZUUAXFUUBXFUUBOJGMZWDUUBXFUUDXFUUBJYADUBZUUDXFDWEZYANUUEXFYAUUFXFDJW
      FYAUUFIJHDWGJDWHWMVSJHYADWIWJJYADWNWKWLWOWPUUCYBXROZPUUAUUGUUBXRYBUUBXNYA
      WQWLWRYBXRWSWTWMWBXAXBXCXD $.
    $( $j usage 'fineqvinfep' avoids 'ax-inf' 'ax-inf2'; $)
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Introduce ax-regs
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d ph y z $.  $d x y z $.
    $( A strong version of the Axiom of Regularity.  It states that if there
       exists a set with property ` ph ` , then there must exist a set with
       property ` ph ` such that none of its elements have property ` ph ` .
       This axiom can be derived from the axioms of ZF set theory as shown in
       ~ axregs , but this derivation relies on ~ ax-inf2 and is thus not
       possible in a finitist context.  (Contributed by BTernaryTau,
       29-Dec-2025.) $)
    ax-regs $a |- ( E. x ph -> E. y ( A. x ( x = y -> ph ) /\
        A. z ( z e. y -> -. A. x ( x = z -> ph ) ) ) ) $.
  $}

  ${
    $d w x y z $.
    $( Derivation of ~ ax-reg from ~ ax-regs and Tarski's FOL axiom schemes.
       This demonstrates the sense in which ~ ax-regs is a stronger version of
       ~ ax-reg .  (Contributed by BTernaryTau, 30-Dec-2025.) $)
    axreg $p |- ( E. y y e. x ->
        E. y ( y e. x /\ A. z ( z e. y -> -. z e. x ) ) ) $=
      ( vw wel wex weq wi wal wn wa ax-regs elequ1 equsalvw notbii imbi2i albii
      cbvexvw anbi12i exbii 3imtr3i ) DAEZDFDBGUBHDIZCBEZDCGUBHDIZJZHZCIZKZBFBA
      EZBFUJUDCAEZJZHZCIZKZBFUBDBCLUBUJDBDBAMZRUIUOBUCUJUHUNUBUJDBUPNUGUMCUFULU
      DUEUKUBUKDCDCAMNOPQSTUA $.
    $( $j usage 'axreg' avoids 'ax-9' 'ax-10' 'ax-11' 'ax-12' 'ax-13' 'ax-ext'
       'ax-rep' 'ax-sep' 'ax-nul' 'ax-pow' 'ax-pr' 'ax-un' 'ax-reg' 'ax-inf'
       'ax-inf2' 'ax-ac' 'ax-ac2' 'df-clab' 'df-cleq' 'df-clel'; $)
  $}

  ${
    $d A w x $.  $d A w y z $.
    $( A version of ~ ax-regs with a class variable instead of a wff variable.
       Axiom D in G&#246;del, _The Consistency of the Axiom of Choice and of
       the Generalized Continuum Hypothesis with the Axioms of Set Theory_
       (1940), p. 6.  (Contributed by BTernaryTau, 30-Dec-2025.) $)
    axregscl $p |- ( E. x x e. A ->
        E. y ( y e. A /\ A. z ( z e. y -> -. z e. A ) ) ) $=
      ( vw cv wcel wex wel wn wi wal eleq1w cbvexvw weq ax-regs equsalvw notbii
      wa imbi2i albii anbi12i exbii sylib sylbi ) AFDGZAHEFDGZEHZBFDGZCBIZCFDGZ
      JZKZCLZSZBHZUFUGAEAEDMNUHEBOUGKELZUJECOUGKELZJZKZCLZSZBHUPUGEBCPVBUOBUQUI
      VAUNUGUIEBEBDMQUTUMCUSULUJURUKUGUKECECDMQRTUAUBUCUDUE $.
    $( $j usage 'axregscl' avoids 'ax-9' 'ax-10' 'ax-11' 'ax-12' 'ax-13'
       'ax-ext' 'ax-rep' 'ax-sep' 'ax-nul' 'ax-pow' 'ax-pr' 'ax-un' 'ax-reg'
       'ax-inf' 'ax-inf2' 'ax-ac' 'ax-ac2' 'df-clab' 'df-cleq'; $)
  $}

  ${
    $d A x y $.
    $( Derivation of ~ zfregs using ~ ax-regs .  (Contributed by BTernaryTau,
       30-Dec-2025.) $)
    axregszf $p |- ( A =/= (/) -> E. x e. A ( x i^i A ) = (/) ) $=
      ( vy c0 wne cv wcel wex cin wceq wrex n0 wel wn wi wal wa axregscl rexbii
      disj1 df-rex bitr2i sylib sylbi ) BDEAFZBGZAHZUEBIDJZABKZABLUGUFCAMCFBGNO
      CPZQAHZUIAACBRUIUJABKUKUHUJABCUEBTSUJABUAUBUCUD $.
    $( $j usage 'axregszf' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13' 'ax-rep'
       'ax-sep' 'ax-nul' 'ax-pow' 'ax-pr' 'ax-un' 'ax-reg' 'ax-inf' 'ax-inf2'
       'ax-ac' 'ax-ac2' 'df-clab' 'df-cleq'; $)
  $}

  ${
    $d A x y $.
    $( Set (epsilon) induction.  This version of ~ setind replaces ~ zfregs
       with ~ axregszf .  (Contributed by BTernaryTau, 30-Dec-2025.) $)
    setindregs $p |- ( A. x ( x C_ A -> x e. A ) -> A = _V ) $=
      ( vy cv wss wcel wi wal cvv cdif c0 wceq cin wn ssindif0 weq sseq1 eleq1w
      wrex imbi12d spvv biimtrrid eldifn nsyli imp nrexdv axregszf necon1bi syl
      vdif0 sylibr ) ADZBEZULBFZGZAHZIBJZKLZBILUPCDZUQMKLZCUQSZNURUPUTCUQUPUSUQ
      FZUTNUPUTUSBFZVBUTUSBEZUPVCUSBOUOVDVCGACACPUMVDUNVCULUSBQACBRTUAUBUSIBUCU
      DUEUFVAUQKCUQUGUHUIBUJUK $.
    $( $j usage 'setindregs' avoids 'ax-reg' 'ax-inf' 'ax-inf2'; $)
  $}

  ${
    $d ph y $.  $d ps x $.  $d x y $.
    setinds2regs.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    setinds2regs.2 $e |- ( A. y e. x ps -> ph ) $.
    $( Principle of set induction (or ` _E ` -induction).  If a property passes
       from all elements of ` x ` to ` x ` itself, then it holds for all
       ` x ` .  (Contributed by BTernaryTau, 31-Dec-2025.) $)
    setinds2regs $p |- ph $=
      ( cv cvv wcel vex cab cbvabv wss wi wceq setindregs ssabral sylbi eqabcri
      wral sylib mpg eqtri mpbir ) ACGZHICJACHACKBDKZHABCDELZUEUFMZUEUFIZNUFHOC
      CUFPUHAUIUHBDUETABDUEQFRACUFUGSUAUBUCSUD $.
    $( $j usage 'setinds2regs' avoids 'ax-reg' 'ax-inf' 'ax-inf2'; $)
  $}

  ${
    $d F x y $.
    $( There are no infinite descending ` e. ` -chains, proven using
       ~ ax-regs .  (Contributed by BTernaryTau, 18-Feb-2026.) $)
    noinfepfnregs $p |- ( F Fn _om -> E. x e. _om ( F ` suc x ) e/ ( F ` x ) )
        $=
      ( vy com wfn cv cima cin c0 wceq csuc cfv wnel wrex wne peano1 mpan2 wcel
      wb wa n0ii wss fnimaeq0 mtbiri neqned axregszf syl fvelimab adantr simprl
      ssid peano2 fnfvima mp3an2 sylan2 ad2ant2r ineq1 eqeq1d biimparc ad2ant2l
      wn minel syl2anc df-nel sylibr jca ex reximdv2 sylbid expimpd ancomsd imp
      rexlimddv ) BDEZCFZBDGZHZIJZAFZKZBLZVSBLZMZADNZCVPVNVPIOVRCVPNVNVPIVNVPIJ
      ZDIJZIDPUAVNDDUBZWEWFSDUKZDDBUCQUDUECVPUFUGVNVOVPRZVRTWDVNVRWIWDVNVRWIWDV
      NVRTZWIWBVOJZADNZWDVNWIWLSZVRVNWGWMWHADDVOBUHQUIWJWKWCADDWJVSDRZWKTZWNWCT
      WJWOTZWNWCWJWNWKUJWPWAWBRVAZWCWPWAVPRZWBVPHZIJZWQVNWNWRVRWKWNVNVTDRZWRVSU
      LVNWGXAWRWHDDBVTUMUNUOUPVRWKWTVNWNWKWTVRWKWSVQIWBVOVPUQURUSUTWAVPWBVBVCWA
      WBVDVEVFVGVHVIVJVKVLVM $.
    $( $j usage 'noinfepfnregs' avoids 'ax-reg' 'ax-inf' 'ax-inf2'; $)
  $}

  ${
    $d F x y $.
    $( There are no infinite descending ` e. ` -chains, proven using
       ~ ax-regs .  (Contributed by BTernaryTau, 18-Feb-2026.) $)
    noinfepregs $p |- E. x e. _om ( F ` suc x ) e/ ( F ` x ) $=
      ( vy com cres wfn cv csuc cfv wnel wrex noinfepfnregs peano2 fvresd fvres
      wcel neleq12d rexbiia wn syl sylib wbr wral fnres notbii rexnal sylbb2 c0
      weu wceq tz6.12-2 nel02 df-nel sylibr reximi pm2.61i ) BDEZDFZAGZHZBIZUSB
      IZJZADKZURUTUQIZUSUQIZJZADKVDAUQLVGVCADUSDPZVEVAVFVBVHUTDBUSMNUSDBOQRUAUR
      SZUSCGBUBCUIZSZADKZVDVIVJADUCZSVLURVMACDBUDUEVJADUFUGVKVCADVKVBUHUJZVCCUS
      BUKVNVAVBPSVCVBVAULVAVBUMUNTUOTUP $.
    $( $j usage 'noinfepregs' avoids 'ax-reg' 'ax-inf' 'ax-inf2'; $)
  $}

  ${
    $d A x y z $.  $d u w x y z $.
    tz9.1regs.1 $e |- A e. _V $.
    $( Every set has a transitive closure (the smallest transitive extension).
       This version of ~ tz9.1 depends on ~ ax-regs instead of ~ ax-reg and
       ~ ax-inf2 .  This suggests a possible answer to the third question posed
       in ~ tz9.1 , namely that the missing property is that countably infinite
       classes must obey regularity.  In ZF set theory we can prove this by
       showing that countably infinite classes are sets and thus ~ ax-reg
       applies to them directly, but in a finitist context it seems that an
       axiom like ~ ax-regs is required since countably infinite classes are
       proper classes.

       A related candidate for the missing property is the non-existence of
       infinite descending ` e. ` -chains, proven as ~ noinfep using ~ ax-reg
       and ~ ax-inf2 and as ~ noinfepregs using ~ ax-regs .  If all sets are
       finite, then the existence of such a chain implies there is a set which
       does not have a transitive closure, as shown in ~ fineqvinfep .
       (Contributed by BTernaryTau, 31-Dec-2025.) $)
    tz9.1regs $p |- E. x ( A C_ x /\ Tr x /\
        A. y ( ( A C_ y /\ Tr y ) -> x C_ y ) ) $=
      ( vz vw vu cv wss wtr wa wi wal w3a wex sseq1 albidv wral cvv wcel imbi1d
      wceq cleq1lem 3anbi13d exbidv weq cab cint cun 3simpa eximi intexab sylib
      ciun vex ralimi iunexg sylancr unexg ssun1 cuni uniun uniiun ssmin ss2iun
      rgenw ax-mp eqsstri ssun4 trint sseq2 anbi12d cbvabv eqabri simprbi triun
      treq mprg df-tr mpbi unssi mpbir ssel trss sylan9 simpr jctird crab rabab
      inteqi intminss mpan eqsstrrid ralrimiv iunss sylibr biimpi syldan ax-gen
      syl6 3pm3.2i imbi2d 3anbi123d spcegv cbvexvw imbitrdi mpisyl setinds2regs
      unss vtocl ) EHZAHZIZXLJZXKBHZIZXOJZKZXLXOIZLZBMZNZAOZCXLIZXNCXOIXQKZXSLZ
      BMZNZAOECDXKCUBZYBYHAYIXMYDYAYGXNXKCXLPYIXTYFBYIXRYEXSXQXKCXOUCUAQUDUEYCF
      HZXLIZXNYJXOIZXQKZXSLZBMZNZAOZEFEFUFZYBYPAYRXMYKYAYOXNXKYJXLPYRXTYNBYRXRY
      MXSXQXKYJXOUCUAQUDUEYQFXKRZXKFXKYKXNKZAUGZUHZUNZUIZSTZXKUUDIZUUDJZXRUUDXO
      IZLZBMZNZYCYSXKSTZUUCSTZUUEEUOZYSUULUUBSTZFXKRUUMUUNYQUUOFXKYQYTAOUUOYPYT
      AYKXNYOUJUKYTAULUMUPFXKUUBSSUQURXKUUCSSUSURUUFUUGUUJXKUUCUTUUGUUDVAZUUDIU
      UPXKVAZUUCVAZUIUUDXKUUCVBUUQUURUUDUUQUUCIUUQUUDIUUQFXKYJUNZUUCFXKVCYJUUBI
      ZFXKRUUSUUCIUUTFXKXNAYJVDVFFXKYJUUBVEVGVHUUQUUCXKVIVGUURUUCIZUURUUDIUUCJZ
      UVAUUBJZFXKRUVBUVCFXKXQUVCBUUABUUAVJXOUUATYLXQYMBUUAYTYMABABUFYKYLXNXQXLX
      OYJVKXLXOVQVLZVMVNVOVRVFFXKUUBVPVGUUCVSVTUURUUCXKVIVGWAVHUUDVSWBUUIBXPXQU
      UCXOIZUUHXRUUBXOIZFXKRUVEXRUVFFXKXRYJXKTZYMUVFXRUVGYLXQXPUVGYJXOTXQYLXKXO
      YJWCXOYJWDWEXPXQWFWGYMUUBYTASWHZUHZXOUVHUUAYTAWIWJXOSTYMUVIXOIBUOYTYMAXOS
      UVDWKWLWMWTWNFXKUUBXOWOWPXPUVEKUUHXKUUCXOXIWQWRWSXAUUEUUKXKGHZIZUVJJZXRUV
      JXOIZLZBMZNZGOYCUVPUUKGUUDSUVJUUDUBZUVKUUFUVLUUGUVOUUJUVJUUDXKVKUVJUUDVQU
      VQUVNUUIBUVQUVMUUHXRUVJUUDXOPXBQXCXDUVPYBGAGAUFZUVKXMUVLXNUVOYAUVJXLXKVKU
      VJXLVQUVRUVNXTBUVRUVMXSXRUVJXLXOPXBQXCXEXFXGXHXJ $.
    $( $j usage 'tz9.1regs' avoids 'ax-reg' 'ax-inf' 'ax-inf2'; $)
  $}

  $( The cumulative hierarchy of sets covers the universe.  This version of
     ~ unir1 replaces ~ setind with ~ setindregs .  (Contributed by
     BTernaryTau, 30-Dec-2025.) $)
  unir1regs $p |- U. ( R1 " On ) = _V $=
    ( vx cr1 con0 cima cuni wss wcel cvv wceq setindregs vex r1elss biimpri mpg
    cv wi ) AOZBCDEZFZQRGZPRHIAARJTSQAKLMN $.
  $( $j usage 'unir1regs' avoids 'ax-reg' 'ax-inf' 'ax-inf2'; $)

  ${
    $d A x y $.
    $( If every element in a transitive class is finite, then every element is
       also hereditarily finite.  This version of ~ trssfir1om replaces
       ~ setinds2 with ~ setinds2regs .  (Contributed by BTernaryTau,
       20-Jan-2026.) $)
    trssfir1omregs $p |- ( ( Tr A /\ A C_ Fin ) -> A C_ U. ( R1 " _om ) ) $=
      ( vx vy wtr cfn wss wa cr1 com cima cuni wcel w3a weq eleq1w 3anbi1d wral
      cv wi a1d imbi12d ssel2 ancoms 3adant2 expcomd impcom 3adant3 simp2 simp3
      trel 3jcad ralrimiv ralim syl5 r1omhf imbitrrdi setinds2regs 3expib com12
      a1i jcad ssrdv ) ADZAEFZGZBAHIJKZBRZALZVEVGVFLZVHVCVDVIVHVCVDMZVISCRZALZV
      CVDMZVKVFLZSZBCBCNZVJVMVIVNVPVHVLVCVDBCAOPBCVFOUAVOCVGQZVJVGELZVNCVGQZGVI
      VQVJVRVSVJVRSVQVHVDVRVCVDVHVRAEVGUBUCUDUTVJVMCVGQVQVSVJVMCVGVJVKVGLZVLVCV
      DVHVCVTVLSZVDVCVHWAVCVTVHVLAVKVGUJUEUFUGVJVCVTVHVCVDUHTVJVDVTVHVCVDUITUKU
      LVMVNCVGUMUNVACVGUOUPUQURUSVB $.
    $( $j usage 'trssfir1omregs' avoids 'ax-reg' 'ax-inf' 'ax-inf2'; $)
  $}

  ${
    $d H w x y z $.
    $( The class of all hereditarily finite sets is the only class with the
       property that all sets are members of it iff they are finite and all of
       their elements are members of it.  This version of ~ r1omhfb replaces
       ~ setinds2 with ~ setinds2regs and ~ trssfir1om with ~ trssfir1omregs .
       (Contributed by BTernaryTau, 21-Jan-2026.) $)
    r1omhfbregs $p |- ( H = U. ( R1 " _om ) <->
        A. x ( x e. H <-> ( x e. Fin /\ A. y e. x y e. H ) ) ) $=
      ( vz vw cv wcel cfn wral wa wb wal r1omhf eleq2w2 wi wss alimi imim2i weq
      eleq1w cr1 com cima cuni wceq ralbidv anbi2d bibi12d mpbiri alrimiv biimp
      wtr simpr ralrid dftr5 sylibr simpl trssfir1omregs syl2anc biimpr imbi12d
      df-ss syl imbi2d ra4v ralim anim2d biimtrid cbvraldva2 anbi12d spvv syl9r
      adantl sylcom setinds2regs ssrdv eqssd impbii ) CUAUBUCUDZUEZAFZCGZWAHGZB
      FZCGZBWAIZJZKZALZVTWHAVTWHWAVSGZWCWDVSGZBWAIZJZKBWAMVTWBWJWGWMACVSNVTWFWL
      WCVTWEWKBWABCVSNUFUGUHUIUJWICVSWIWBWGOZALZCVSPZWHWNAWBWGUKQWOCULZCHPZWPWO
      WFACIWQWOWFACWNWBWFOAWGWFWBWCWFUMRQUNABCUOUPWOWBWCOZALWRWNWSAWGWCWBWCWFUQ
      RQACHVBUPCURUSVCWIWGWBOZALZVSCPWHWTAWBWGUTQXADVSCXADFZVSGZXBCGZOZOXAEFZVS
      GZXFCGZOZOZDEDESZXEXIXAXKXCXGXDXHDEVSTDECTVAVDXJEXBIXAXIEXBIZXEXAXIEXBVEX
      LXCXBHGZXHEXBIZJZXAXDXCXMXGEXBIZJXLXOEXBMXLXPXNXMXGXHEXBVFVGVHWTXOXDOADAD
      SZWGXOWBXDXQWCXMWFXNADHTXQWEXHBEWAXBBESZWEXHKXQBECTVMXQXRUQVIVJADCTVAVKVL
      VNVOVPVCVQVR $.
    $( $j usage 'r1omhfbregs' avoids 'ax-reg' 'ax-inf' 'ax-inf2'; $)
  $}

  $( All sets are finite iff all sets are hereditarily finite.  (Contributed by
     BTernaryTau, 30-Dec-2025.) $)
  fineqvr1ombregs $p |- ( Fin = _V <-> U. ( R1 " _om ) = _V ) $=
    ( cfn cvv wceq cr1 com cima cuni fineqvomon imaeq2d unieqd unir1regs eqtrdi
    con0 wss r1omfi sseq1 mpbii vss sylib impbii ) ABCZDEFZGZBCZUAUCDMFZGBUAUBU
    EUAEMDHIJKLUDBANZUAUDUCANUFOUCBAPQARST $.
  $( $j usage 'fineqvr1ombregs' avoids 'ax-reg' 'ax-inf' 'ax-inf2'; $)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Derive ax-regs
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d ph y z $.  $d x y z $.
    $( Derivation of ~ ax-regs from the axioms of ZF set theory.  (Contributed
       by BTernaryTau, 29-Dec-2025.) $)
    axregs $p |- ( E. x ph -> E. y ( A. x ( x = y -> ph ) /\
        A. z ( z e. y -> -. A. x ( x = z -> ph ) ) ) ) $=
      ( cab c0 wne cv wcel wel wa wex wn weq wi wal wsb df-clab sb6 bitri exnal
      wral zfregs2 df-ral notbii annim anbi2ci df-an con2bii albii alnex bitr2i
      abn0 anbi12i bitr3i exbii 3bitr2i 3imtr3i ) ABEZFGDHUSIZDCJZKZDLZCUSUBZMZ
      ABLBCNAOBPZVABDNAOBPZMOZDPZKZCLZCDUSUCABUMVECHUSIZVCOZCPZMVMMZCLVKVDVNVCC
      USUDUEVMCUAVOVJCVOVLVCMZKVJVLVCUFVLVFVPVIVLABCQVFACBRABCSTVIVBMZDPVPVHVQD
      VBVHVBVAVGKVHMUTVGVAUTABDQVGADBRABDSTUGVAVGUHTUIUJVBDUKULUNUOUPUQUR $.
    $( $j usage 'axregs' avoids 'ax-regs'; $)
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  ZFC axioms with reduced distinct variable conditions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d w x y $.  $d ph w y z $.
    $( A generalization of ~ ax-sep in which ` x ` and ` z ` need not be
       distinct.  This theorem scheme bundles ~ ax-sep with the degenerate
       instance ` E. y A. z ( z e. y <-> ( z e. z /\ ph ) ) ` which is
       satisfied by the existence of the empty set.  Usage of this theorem is
       discouraged because it depends on ~ ax-13 .  (Contributed by
       BTernaryTau, 21-May-2026.)  (New usage is discouraged.) $)
    axsepg2 $p |- E. y A. x ( x e. y <-> ( x e. z /\ ph ) ) $=
      ( vw wel wa wb wal wex weq wn cv nfcvd nfeld nfvd wi anbi1d biimpd al2imi
      nfv nfnae nfcvf nfand nfbid nfald nfexd dveeq2 naecoms elequ2 bibi2d syl6
      eximdv elequ1 bibi12d syld ax-sep ax-gen ax-nul elirrv intnanr nbn biimpi
      axc11 alimi eximii dvelimalcasei spi ) BCFZBDFZAGZHZBIZCJZDVIBEFZAGZHZBIZ
      CJZDCFZDDFZAGZHZDIZCJZVNDBEDBKZDIZLZVRDCWHCUAWHVQDBDBBUBWHVIVPDWHDBMZCMZD
      BUCZWHDWJNOWHVOADWHDWIEMZWKWHDWLNOWHADPUDUEUFUGWHVNEPWHEDKZWMBIZVSVNQWMWN
      QBDBDEUHUIWNVRVMCWMVQVLBWMVQVLWMVPVKVIWMVOVJAEDBUJRUKSTUMULWGWDVMCWGWDVLD
      IVMWFWCVLDWFWCVLWFVTVIWBVKDBCUNWFWAVJADBDUNRUOSTVLDBVDUPUMVSEABCEUQURWEDV
      TLZDIWDCCDUSWOWCDWOWCWBVTWAADUTVAVBVCVEVFURVGVH $.
  $}

  ${
    $d x z $.  $d ph w y $.  $d ph w z $.  $d w x y $.
    $( A generalization of ~ ax-sep in which ` y ` and ` z ` need not be
       distinct.  This theorem scheme bundles ~ ax-sep with the degenerate
       instance ` E. y A. x ( x e. y <-> ( x e. y /\ ph ) ) ` which is
       satisfied by the existence of the empty set.  Usage of this theorem is
       discouraged because it depends on ~ ax-13 .  (Contributed by
       BTernaryTau, 3-Aug-2025.)  (New usage is discouraged.) $)
    axsepg3 $p |- E. y A. x ( x e. y <-> ( x e. z /\ ph ) ) $=
      ( vw wel wa wb wal weq wn nfv nfvd cv nfcvf nfcrd wi elequ2 biimpd alimdv
      nfand nfbid nfald bibi1d a1i anbi1d bibi2d sps ax-sep ax-nul bianfd alimi
      id eximii dvelimexcasei ) BEFZBDFZAGZHZBIZBCFZVAAGZHZBIZVAURHZBIZCDECDJZC
      IKZUSCBVHBLVHUPURCVHUPCMVHUQACVHCBDNCDOPVHACMUAUBUCVHVFEMECJZUTVFQQVHVIUS
      VEBVIUSVEVIUPVAURECBRUDSTUEVGVDVFQCVGVCVEBVGVCVEVGVBURVAVGVAUQACDBRUFUGST
      UHABEDUIVAKZBIVDCCBUJVJVCBVJVAAVJUMUKULUNUO $.
  $}

  ${
    $d ph w y $.  $d ph w z $.  $d w x z $.  $d v x y $.
    $( Alternate proof of ~ axsepg3 , derived directly from ~ ax-sep with no
       additional set theory axioms.  (Contributed by BTernaryTau, 3-Aug-2025.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    axsepg3ALT $p |- E. y A. x ( x e. y <-> ( x e. z /\ ph ) ) $=
      ( vw vv wel wa wb wal weq wn nfv nfvd wi elequ2 biimpd alimdv ax-sep wfal
      cv nfcvf nfcrd nfand nfbid nfald bibi1d a1i anbi1d bibi2d sps intnan mtoi
      fal biimp bianfd alimi eximii dvelimexcasei ) BEGZBDGZAHZIZBJZBCGZVEAHZIZ
      BJZVEVBIZBJZCDECDKZCJLZVCCBVLBMVLUTVBCVLUTCNVLVAACVLCBDUACDUBUCVLACNUDUEU
      FVLVJENECKZVDVJOOVLVMVCVIBVMVCVIVMUTVEVBECBPUGQRUHVKVHVJOCVKVGVIBVKVGVIVK
      VFVBVEVKVEVAACDBPUIUJQRUKABEDSVEBFGZTHZIZBJVHCTBCFSVPVGBVPVEAVPVEVOTVNUNU
      LVEVOUOUMUPUQURUS $.
    $( $j usage 'axsepg3ALT' avoids 'ax-nul'; $)
  $}

  ${
    $d ph w y $.  $d w x y $.  $d w y z $.
    $( A generalization of ~ ax-sep that combines ~ axsepg and ~ axsepg2 into a
       single theorem scheme.  Unlike ~ ax-sep , this scheme lacks a distinct
       variable condition for ` ph ` and ` z ` as well as for ` x ` and ` z ` .
       Usage of this theorem is discouraged because it depends on ~ ax-13 .
       (Contributed by BTernaryTau, 24-May-2026.)
       (New usage is discouraged.) $)
    axsepg4 $p |- E. y A. x ( x e. y <-> ( x e. z /\ ph ) ) $=
      ( vw wel wa wb wal wex wnf weq wn nfa1 anbi1d biimpd al2imi eximdv elequ1
      wi a1i nfvd sp dveeq2 naecoms elequ2 bibi2d syl6 syl7 bibi12d syld axsepg
      axc11 gen2 ax-nul elirrv intnanr biimpi alimi eximii ax-gen dvelimalcasei
      nbn spi ) BCFZBDFZAGZHZBIZCJZDVEBEFZAGZHZBIZCJZDIZDCFZDDFZAGZHZDIZCJZVJDB
      EVPDKDBLZDIZMZVODNUAWEVJEUBVPVOWEEDLZVJVODUCWEWFWFBIZVOVJTWFWGTBDBDEUDUEW
      GVNVICWFVMVHBWFVMVHWFVLVGVEWFVKVFAEDBUFOUGPQRUHUIWDWAVICWDWAVHDIVIWCVTVHD
      WCVTVHWCVQVEVSVGDBCSWCVRVFADBDSOUJPQVHDBUMUKRVOEDABCEULUNWBDVQMZDIWACCDUO
      WHVTDWHVTVSVQVRADUPUQVCURUSUTVAVBVD $.
  $}

  ${
    $d w z $.  $d ph w y $.  $d w x y $.
    $( A generalization of ~ ax-sep that combines ~ axsepg , ~ axsepg2 , and
       ~ axsepg3 into a single theorem scheme.  Unlike ~ ax-sep , this scheme
       lacks a distinct variable condition for ` ph ` and ` z ` , for ` x ` and
       ` z ` , and for ` y ` and ` z ` .  Usage of this theorem is discouraged
       because it depends on ~ ax-13 .  (Contributed by BTernaryTau,
       24-May-2026.)  (New usage is discouraged.) $)
    axsepg5 $p |- E. y A. x ( x e. y <-> ( x e. z /\ ph ) ) $=
      ( vw wel wa wb wal weq wn nfnae nfvd cv nfcvf nfcrd nfand elequ2 biimpd
      wi nfbid nfald bibi1d albidv a1i nfae anbi1d bibi2d alimd axsepg4 axsepg3
      sps dvelimexcasei ) BEFZBDFZAGZHZBIZBCFZUSAGZHZBIUSUPHZBIZCDECDJZCIZKZUQC
      BCDBLVFUNUPCVFUNCMVFUOACVFCBDNCDOPVFACMQUAUBVFVCEMECJZURVCTTVFVGURVCVGUQV
      BBVGUNUSUPECBRUCUDSUEVEVAVBBCDBUFVDVAVBTCVDVAVBVDUTUPUSVDUSUOACDBRUGUHSUL
      UIABEDUJABCCUKUM $.
  $}

  ${
    $d x z $.  $d y z $.
    $( A generalization of ~ ax-nul in which ` x ` and ` y ` need not be
       distinct.  This theorem scheme bundles ~ ax-nul with the degenerate
       instance ` E. x A. x -. x e. x ` which is satisfied by ~ elirrv .  Usage
       of this theorem is discouraged because it depends on ~ ax-13 .
       (Contributed by BTernaryTau, 3-Aug-2025.)
       (New usage is discouraged.) $)
    axnulg $p |- E. x A. y -. y e. x $=
      ( vz wel wn wal weq nfnae cv nfcvf nfcvd nfeld nfnd nfald nfvd wi naecoms
      dveeq2 notbid biimpd elequ2 al2imi syl6 wb elequ1 sps dral1 ax-nul elirrv
      ax-gen exgen dvelimexcasei ) BCDZEZBFZAADZEZAFZBADZEZBFZABCABGZAFZEZUNABA
      BBHVDUMAVDABICIZABJVDAVEKLMNVDVACOVDCAGZVFBFZUOVAPVFVGPBABACRQVFUNUTBVFUN
      UTVFUMUSCABUASTUBUCVCURVAUQUTABVBUQUTUDAVBUPUSABAUESUFUGTCBUHURAUQAAUIUJU
      KUL $.
  $}

  ${
    $d v x y z $.  $d v w x z $.
    $( A generalization of ~ ax-pow that combines it and ~ zfpow into a single
       theorem scheme.  Unlike ~ ax-pow , this scheme lacks a distinct variable
       condition for ` y ` and ` w ` .  (Contributed by BTernaryTau,
       26-May-2026.) $)
    axpowg $p |- E. y A. z ( A. w ( w e. z -> w e. x ) -> z e. y ) $=
      ( vv wel wi wal wex ax-pow elequ1 imbi12d cbvalvw imbi1i albii exbii mpbi
      weq ) ECFZEAFZGZEHZCBFZGZCHZBIDCFZDAFZGZDHZUCGZCHZBIABCEJUEUKBUDUJCUBUIUC
      UAUHEDEDRSUFTUGEDCKEDAKLMNOPQ $.
  $}

  ${
    $d v x y z $.  $d v w y z $.
    $( A generalization of ~ ax-pow in which ` x ` and ` w ` need not be
       distinct.  This theorem scheme bundles ~ ax-pow with the degenerate
       instance ` E. y A. z ( A. x ( x e. z -> x e. x ) -> z e. y ) ` which is
       satisfied by the existence of a set that contains all empty sets (see
       ~ axprlem1 ).  Usage of this theorem is discouraged because it depends
       on ~ ax-13 .  (Contributed by BTernaryTau, 26-May-2026.)
       (New usage is discouraged.) $)
    axpowg2 $p |- E. y A. z ( A. w ( w e. z -> w e. x ) -> z e. y ) $=
      ( vv wel wi wal wex weq wn cv nfcvd nfeld nfimd nfald nfvd equcoms al2imi
      nfv nfnae nfcvf nfexd dveeq2 naecoms imim2d imim1d alimdv eximdv syl6 ax8
      ax9v2 axc11r imim12d syld ax-pow ax-gen axprlem1 elirrv mtt ax-mp biimpri
      wb alimi imim1i eximii dvelimalcasei spi ) DCFZDAFZGZDHZCBFZGZCHZBIZAVIDE
      FZGZDHZVMGZCHZBIZACFZAAFZGZAHZVMGZCHZBIZVPADEADJZAHZKZWAABWLBTWLVTACWLCTW
      LVSVMAWLVRADADDUAWLVIVQAWLADLZCLZADUBZWLAWNMNWLAWMELZWOWLAWPMNOPWLVMAQOPU
      CWLVPEQWLEAJZWQDHZWBVPGWQWRGDADAEUDUEWRWAVOBWRVTVNCWRVLVSVMWQVKVRDWQVJVQV
      IVJVQGAEAEDULRUFSUGUHUIUJWKWHVOBWKWGVNCWKVLWFVMWKVLVKAHWFVKDAUMWJVKWEAWJW
      CVIVJWDADCUKVJWDGDADAAUKRUNSUOUGUHUIWBEEBCDUPUQWIAWCKZAHZVMGZCHWHBBCAURXA
      WGCWFWTVMWEWSAWSWEWDKWSWEVCAUSWDWCUTVAVBVDVEVDVFUQVGVH $.
  $}

  ${
    $d v w z $.  $d v x y z $.
    $( A generalization of ~ ax-pow that combines ~ axpowg and ~ axpowg2 into a
       single theorem scheme.  Unlike ~ ax-pow , this scheme lacks a distinct
       variable condition for ` y ` and ` w ` as well as for ` x ` and ` w ` .
       Usage of this theorem is discouraged because it depends on ~ ax-13 .
       (Contributed by BTernaryTau, 26-May-2026.)
       (New usage is discouraged.) $)
    axpowg3 $p |- E. y A. z ( A. w ( w e. z -> w e. x ) -> z e. y ) $=
      ( vv wel wi wal wex weq wn nfnae nfv nfcvd nfeld nfimd nfald nfvd equcoms
      cv nfcvf nfexd dveeq2 naecoms nfal ax9v2 imim2d al2imi imim1d alimdv syl6
      eximd nfae axc11r ax8 imim12d syld axpowg ax-gen axprlem1 wb elirrv ax-mp
      mtt biimpri alimi imim1i eximii dvelimalcasei spi ) DCFZDAFZGZDHZCBFZGZCH
      ZBIZAVKDEFZGZDHZVOGZCHZBIZACFZAAFZGZAHZVOGZCHZBIZVRADEADJZAHZKZWCABADBLWN
      WBACWNCMWNWAVOAWNVTADADDLWNVKVSAWNADTZCTZADUAZWNAWPNOWNAWOETZWQWNAWRNOPQW
      NVOARPQUBWNVRERWNEAJZWSDHZWDVRGWSWTGDADAEUCUDWTWCVQBWSBDWSBMUEWTWBVPCWTVN
      WAVOWSVMVTDWSVLVSVKVLVSGAEAEDUFSUGUHUIUJULUKWMWJVQBADBUMWMWIVPCWMVNWHVOWM
      VNVMAHWHVMDAUNWLVMWGAWLWEVKVLWFADCUOVLWFGDADAAUOSUPUHUQUIUJULWDEEBCDURUSW
      KAWEKZAHZVOGZCHWJBBCAUTXCWICWHXBVOWGXAAXAWGWFKXAWGVAAVBWFWEVDVCVEVFVGVFVH
      USVIVJ $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Cardinality without the Axiom of Choice
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $c kard $.

  $( Extend class definition to include the alternative cardinal size
     function. $)
  ckard $a class kard $.

  ${
    $d x y $.
    $( Define the alternative cardinal number function.  Under this definition,
       the cardinal number of a set is the set of all sets equinumerous to it
       and having the least possible rank.  Definition of [Enderton] p. 222.
       See ~ kardval for its value.  The principal theorem relating this type
       of cardinality to equinumerosity is ~ kardeng .  Our notation is from
       Enderton and differentiates this function from the standard cardinal
       size function defined in ~ df-card .  (Contributed by BTernaryTau,
       2-Jul-2026.) $)
    df-kard $a |- kard = ( x e. _V |-> Scott { y | y ~~ x } ) $.
  $}

  ${
    $d x y $.
    $( The ` kard ` class is a function on the universe.  This theorem depends
       on the Axiom of Regularity and the Axiom of Infinity, but it does not
       depend on the Axiom of Choice.  (Contributed by BTernaryTau,
       3-Jul-2026.) $)
    kardfn $p |- kard Fn _V $=
      ( vx vy cvv cv cen wbr cab cscott ckard scottex df-kard fnmpti ) ACBDADEF
      BGZHIMJABKL $.
    $( $j usage 'kardfn' avoids 'ax-ac' 'ax-ac2'; $)
  $}

  ${
    $d A x y $.
    $( The value of the ` kard ` function.  This theorem depends on the Axiom
       of Regularity and the Axiom of Infinity, but it does not depend on the
       Axiom of Choice.  See also ~ kardval2 .  (Contributed by BTernaryTau,
       3-Jul-2026.) $)
    kardval $p |- ( kard ` A ) = Scott { x | x ~~ A } $=
      ( vy cvv wcel ckard cfv cv cen wbr cab cscott wceq breq2 scotteqd df-kard
      abbidv scottex wn c0 fvmpt fvprc scott0 eqtr4di wal simpr con3i encv nsyl
      wa alrimiv ab0 sylibr eqtr4d pm2.61i ) BDEZBFGZAHZBIJZAKZLZMCBURCHZIJZAKZ
      LVADFVBBMZVDUTVEVCUSAVBBURINQOCAPUTRUAUPSZUQTLZVAVFUQTVGBFUBUCUDVFUTTVFUS
      SZAUEUTTMVFVHAVFURDEZUPUJZUSVJUPVIUPUFUGURBUHUIUKUSAULUMOUNUO $.
    $( $j usage 'kardval' avoids 'ax-ac' 'ax-ac2'; $)
  $}

  ${
    $d A x y $.
    $( The value of the ` kard ` function.  This theorem depends on the Axiom
       of Regularity and the Axiom of Infinity, but it does not depend on the
       Axiom of Choice.  See also ~ kardval .  (Contributed by BTernaryTau,
       3-Jul-2026.) $)
    kardval2 $p |- ( kard ` A ) =
        { x | ( x ~~ A /\ A. y ( y ~~ A -> ( rank ` x ) C_ ( rank ` y ) ) ) }
        $=
      ( ckard cfv cv cen wbr cab cscott crnk wss wi kardval breq1 scottab eqtri
      wal wa ) CDEAFZCGHZAIJUABFZCGHZTKEUBKELMBRSAIACNUAUCABTUBCGOPQ $.
    $( $j usage 'kardval2' avoids 'ax-ac' 'ax-ac2'; $)
  $}

  ${
    $d x y $.
    $( The ` kard ` cardinality of the empty set is the singleton of the empty
       set.  (Contributed by BTernaryTau, 3-Jul-2026.) $)
    kard0 $p |- ( kard ` (/) ) = { (/) } $=
      ( vx vy c0 cvv wcel ckard cfv csn wceq 0ex cv cen wbr cscott breq2 abbidv
      cab scotteqd wtru wb en0 velsn bitr4i a1i eqabcdv scotteqi scottsn eqtrdi
      mptru eqtri df-kard snex fvmpt ax-mp ) CDECFGCHZIJACBKZAKZLMZBQZNZUODFUQC
      IZUTUPCLMZBQZNZUOVAUSVCVAURVBBUQCUPLOPRVDUONUOVCUOVCUOISVBBUOVBUPUOEZTSVB
      UPCIVEUPUABCUBUCUDUEUIUFCUGUJUHABUKCULUMUN $.
    $( $j usage 'kard0' avoids 'ax-rep' 'ax-pow' 'ax-un' 'ax-reg' 'ax-inf'
       'ax-inf2' 'ax-ac' 'ax-ac2'; $)
  $}

  ${
    $d A x y $.  $d B x y $.
    $( Any member of the ` kard ` cardinal number of a set is equinumerous to
       the set.  Contrast with ~ cardne for ` card ` cardinals.  (Contributed
       by BTernaryTau, 3-Jul-2026.) $)
    elkarden $p |- ( A e. ( kard ` B ) -> A ~~ B ) $=
      ( vy vx ckard cfv wcel cen wbr cv crnk wss wi wal wceq breq1 fveq2 sseq1d
      wa imbi2d albidv anbi12d kardval2 elab2g ibi simpld ) ABEFZGZABHIZCJZBHIZ
      AKFZUJKFZLZMZCNZUHUIUPSZDJZBHIZUKURKFZUMLZMZCNZSUQDAUGUGURAOZUSUIVCUPURAB
      HPVDVBUOCVDVAUNUKVDUTULUMURAKQRTUAUBDCBUCUDUEUF $.
  $}

  ${
    $d A x $.
    $( Applying ` kard ` to a class yields the empty set iff the class is a
       proper class.  (Contributed by BTernaryTau, 3-Jul-2026.) $)
    kardeq0 $p |- ( ( kard ` A ) = (/) <-> -. A e. _V ) $=
      ( vx ckard cfv c0 wceq cvv wcel wn cv cen wbr cab cscott wne wex elissetv
      wi eqeng sylibr elv eximi syl abn0 scott0b necon3bii sylib kardval neeq1i
      necon2bi fvprc impbii ) ACDZEFAGHZIUNUMEUNBJZAKLZBMZNZEOZUMEOUNUQEOZUSUNU
      PBPZUTUNUOAFZBPVABAGQVBUPBVBUPRBUOAGSUAUBUCUPBUDTUQEUREUQUEUFUGUMUREBAUHU
      ITUJACUKUL $.
  $}

  ${
    $d A x $.  $d B x y $.
    $( Two sets are equinumerous iff their ` kard ` cardinal numbers are equal.
       Unlike ~ carden , this theorem does not depend on the Axiom of Choice,
       but it does depend on the Axiom of Regularity and the Axiom of Infinity.
       (Contributed by BTernaryTau, 3-Jul-2026.) $)
    kardeng $p |- ( A e. V -> ( ( kard ` A ) = ( kard ` B ) <-> A ~~ B ) ) $=
      ( vx vy ckard cfv wceq cen wbr fveqeq2 breq1 vex kardval karden vtoclbg
      cv ) DQZFGZBFGZHRBIJAFGTHABIJDACRATFKRABILERBSTDMERNEBNOP $.
    $( $j usage 'kardeng' avoids 'ax-ac' 'ax-ac2'; $)
  $}

  $( If two sets are equinumerous, then their ` kard ` cardinal numbers are
     equal.  (Contributed by BTernaryTau, 4-Jul-2026.) $)
  kardenir $p |- ( A ~~ B -> ( kard ` A ) = ( kard ` B ) ) $=
    ( cen wbr ckard cfv wceq cvv wcel wb relen brrelex1i kardeng syl ibir ) ABC
    DZAEFBEFGZPAHIQPJABCKLABHMNO $.

  $( The empty set is the only set with cardinality zero.  This is the ` kard `
     version of ~ cardeq0 .  (Contributed by BTernaryTau, 3-Jul-2026.) $)
  kard0b $p |- ( ( kard ` A ) = ( kard ` (/) ) <-> A = (/) ) $=
    ( cvv wcel ckard cfv c0 wceq wb cen wbr kardeng en0 bitrdi wn fvprc wne csn
    0nep0 kard0 neeqtrri a1i eqnetrd neneqd eleq1 mpbiri con3i 2falsed pm2.61i
    0ex ) ABCZADEZFDEZGZAFGZHUJUMAFIJUNAFBKALMUJNZUMUNUOUKULUOUKFULADOFULPUOFFQ
    ULRSTUAUBUCUNUJUNUJFBCUIAFBUDUEUFUGUH $.

  $( A singleton has cardinality one.  (Contributed by BTernaryTau,
     4-Jul-2026.) $)
  kardsn $p |- ( A e. V -> ( kard ` { A } ) = ( kard ` 1o ) ) $=
    ( wcel csn c1o cen wbr ckard cfv wceq ensn1g cvv snex kardeng ax-mp sylibr
    wb ) ABCADZEFGZRHIEHIJZABKRLCTSQAMRELNOP $.

  ${
    $d A x y $.  $d B x y $.
    $( One set dominates another iff an element in its ` kard ` cardinality
       dominates an element in the second set's ` kard ` cardinality.
       (Contributed by BTernaryTau, 4-Jul-2026.) $)
    karddom $p |- ( A ~<_ B <->
        E. x e. ( kard ` A ) E. y e. ( kard ` B ) x ~<_ y ) $=
      ( cdom wbr cv ckard cfv wrex wcel wa wex wne cvv reldom kardeq0 sylib cen
      c0 brrelex1i necon2abii n0 brrelex2i 19.42v wi simpr a1i elkarden endomtr
      ancoms ensym domentr sylan2 stoic3 3expib syl2ani eximdv biimtrrid mpan2d
      jcad df-rex imbitrrdi ancld sylibr sylan com12 syl2an rexlimivv impbii
      mpd ) CDEFZAGZBGZEFZBDHIZJZACHIZJZVLVMVRKZVQLZAMZVSVLVTAMZWBVLVRTNZWCVLCO
      KZWDCDEPUAWEVRTCQUBRAVRUCRVLVTWAAVLVTVQVLVTVNVPKZVOLZBMZVQVLVTWFBMZWHVLVP
      TNZWIVLDOKZWJCDEPUDWKVPTDQUBRBVPUCRVTWILVTWFLZBMVLWHVTWFBUEVLWLWGBVLWLWFV
      OWLWFUFVLVTWFUGUHVTVLVMCSFZVNDSFZVOWFVMCUIZVNDUIZVLWMWNVOVLWMVMDEFZWNVOWM
      VLWQVMCDUJUKWNWQDVNSFVOVNDULVMDVNUMUNUOUPUQVAURUSUTVOBVPVBVCVDURVKVQAVRVB
      VEVOVLABVRVPVTWMWNVOVLUFWFWOWPVOWMWNLVLVOWMWNVLVOWMCVNEFZWNVLWMVOWRWMCVMS
      FVOWRVMCULCVMVNUJVFUKCVNDUMUOUPVGVHVIVJ $.
  $}

  ${
    $d A x y $.  $d B x y $.
    $( One set strictly dominates another iff an element in its ` kard `
       cardinality strictly dominates an element in the second set's ` kard `
       cardinality.  (Contributed by BTernaryTau, 6-Jul-2026.) $)
    kardsdom $p |- ( A ~< B <->
        E. x e. ( kard ` A ) E. y e. ( kard ` B ) x ~< y ) $=
      ( csdm wbr cv ckard cfv wrex wcel wa wex c0 wne cvv relsdom kardeq0 sylib
      cen brrelex1i necon2abii n0 brrelex2i 19.42v wi simpr a1i elkarden ancoms
      ensdomtr ensym sdomentr sylan2 stoic3 3expib jcad eximdv biimtrrid mpan2d
      syl2ani df-rex imbitrrdi ancld sylibr sylan com12 syl2an rexlimivv impbii
      mpd ) CDEFZAGZBGZEFZBDHIZJZACHIZJZVLVMVRKZVQLZAMZVSVLVTAMZWBVLVRNOZWCVLCP
      KZWDCDEQUAWEVRNCRUBSAVRUCSVLVTWAAVLVTVQVLVTVNVPKZVOLZBMZVQVLVTWFBMZWHVLVP
      NOZWIVLDPKZWJCDEQUDWKVPNDRUBSBVPUCSVTWILVTWFLZBMVLWHVTWFBUEVLWLWGBVLWLWFV
      OWLWFUFVLVTWFUGUHVTVLVMCTFZVNDTFZVOWFVMCUIZVNDUIZVLWMWNVOVLWMVMDEFZWNVOWM
      VLWQVMCDUKUJWNWQDVNTFVOVNDULVMDVNUMUNUOUPVAUQURUSUTVOBVPVBVCVDURVKVQAVRVB
      VEVOVLABVRVPVTWMWNVOVLUFWFWOWPVOWMWNLVLVOWMWNVLVOWMCVNEFZWNVLWMVOWRWMCVMT
      FVOWRVMCULCVMVNUKVFUJCVNDUMUOUPVGVHVIVJ $.
  $}

  ${
    $d A x y $.  $d B x y $.
    $( One set is equinumerous to another iff an element in its ` kard `
       cardinality is equinumerous to an element in the second set's ` kard `
       cardinality.  See ~ kardeng for a version with equality of cardinals.
       (Contributed by BTernaryTau, 7-Jul-2026.) $)
    kardexen $p |- ( A ~~ B <->
        E. x e. ( kard ` A ) E. y e. ( kard ` B ) x ~~ y ) $=
      ( cen wbr cv ckard wrex csdm wn wral cdom wa bren2 biancomi wcel elkarden
      cfv entr 2r19.29 kardsdom notbii ralnex2 bitr4i anbi2i karddom 2rexbii wi
      bitri bianbi 3imtr4i ensym sylan ancoms stoic3 3expib com12 syl2an impbii
      rexlimivv ) CDEFZAGZBGZEFZBDHSZIACHSZIZVCVDJFZKZBVFLAVGLZVCVDMFZBVFIAVGIZ
      NVJVLNZBVFIAVGIVBVHVJVLABVGVFUAVBVKVMVBCDMFZVKVMVBVOCDJFZKZNVOVKNCDOVQVKV
      OVQVIBVFIAVGIZKVKVPVRABCDUBUCVIABVGVFUDUEUFUJABCDUGUKPVEVNABVGVFVEVJVLVCV
      DOPUHULVEVBABVGVFVCVGQVCCEFZVDDEFZVEVBUIVDVFQVCCRVDDRVEVSVTNVBVEVSVTVBVEV
      SCVDEFZVTVBVSVEWAVSCVCEFVEWAVCCUMCVCVDTUNUOCVDDTUPUQURUSVAUT $.
  $}

  $( If two sets have equal nonzero ` card ` cardinalities, then they have
     equal ` kard ` cardinalities.  This theorem does not depend on the Axiom
     of Choice.  (Contributed by BTernaryTau, 3-Jul-2026.) $)
  kardcard2a $p |- ( ( ( card ` A ) = ( card ` B ) /\ ( card ` A ) =/= (/) )
      -> ( kard ` A ) = ( kard ` B ) ) $=
    ( ccrd cfv wceq c0 wne ckard cen wbr carden2a cdm wcel csn cres fvfundmfvn0
    wa wb wfun simpld kardeng syl adantl mpbird ) ACDZBCDEZUEFGZQAHDBHDEZABIJZA
    BKUGUHUIRZUFUGACLZMZUJUGULCANOSACPTABUKUAUBUCUD $.
  $( $j usage 'kardcard2a' avoids 'ax-ac' 'ax-ac2'; $)


  $( If two sets have equal ` kard ` cardinalities, then they have equal
     ` card ` cardinalities.  This theorem does not depend on the Axiom of
     Choice.  (Contributed by BTernaryTau, 3-Jul-2026.) $)
  kardcard2b $p |- ( ( kard ` A ) = ( kard ` B ) ->
      ( card ` A ) = ( card ` B ) ) $=
    ( cvv wcel ckard cfv wceq ccrd wi cen kardeng carden2b biimtrdi wn wa fvprc
    wbr c0 eqeq1d kardeq0 biimpi eqcoms anc2li adantr adantl eqtr4d pm2.61i
    syl6 ) ACDZAEFZBEFZGZAHFZBHFZGZIUIULABJQUOABCKABLMUINZULUPBCDNZOZUOUPULUQUP
    ULRUKGUQUPUJRUKAEPSUQUKRUKRGUQBTUAUBMUCURUMRUNUPUMRGUQAHPUDUQUNRGUPBHPUEUFU
    HUG $.
  $( $j usage 'kardcard2b' avoids 'ax-ac' 'ax-ac2'; $)

  $( Two numerable sets have equal ` kard ` cardinalities iff they have equal
     ` card ` cardinalities.  This theorem does not depend on the Axiom of
     Choice.  (Contributed by BTernaryTau, 3-Jul-2026.) $)
  kardcard2 $p |- ( ( A e. dom card /\ B e. dom card ) ->
      ( ( kard ` A ) = ( kard ` B ) <-> ( card ` A ) = ( card ` B ) ) ) $=
    ( ccrd cdm wcel wa ckard cfv wceq cen wbr wb kardeng adantr carden2 bitr4d
    ) ACDZEZBQEZFAGHBGHIZABJKZACHBCHIRTUALSABQMNABOP $.
  $( $j usage 'kardcard2' avoids 'ax-ac' 'ax-ac2'; $)

  $( The Axiom of Choice implies that two sets have equal ` kard `
     cardinalities iff they have equal ` card ` cardinalities.  (Contributed by
     BTernaryTau, 3-Jul-2026.) $)
  ackardcard $p |- ( CHOICE -> ( ( A e. V /\ B e. W ) ->
      ( ( kard ` A ) = ( kard ` B ) <-> ( card ` A ) = ( card ` B ) ) ) ) $=
    ( wac wcel wa ccrd cdm ckard cfv wceq wb acnum anim12d kardcard2 syl6 ) EAC
    FZBDFZGAHIZFZBTFZGAJKBJKLAHKBHKLMERUASUBACNBDNOABPQ $.
  $( $j usage 'ackardcard' avoids 'ax-ac' 'ax-ac2'; $)

  $( Two sets have equal ` kard ` cardinalities iff they have equal ` card `
     cardinalities.  This theorem depends on the Axiom of Choice.  (Contributed
     by BTernaryTau, 3-Jul-2026.) $)
  kardcard $p |- ( ( A e. V /\ B e. W ) ->
      ( ( kard ` A ) = ( kard ` B ) <-> ( card ` A ) = ( card ` B ) ) ) $=
    ( wac wcel wa ckard cfv wceq ccrd wb wi axac3 ackardcard ax-mp ) EACFBDFGAH
    IBHIJAKIBKIJLMNABCDOP $.

  ${
    $d A x $.
    $( The ` kard ` cardinal number of a finite ordinal is finite.
       (Contributed by BTernaryTau, 3-Jul-2026.) $)
    kardnnfi $p |- ( A e. _om -> ( kard ` A ) e. Fin ) $=
      ( vx com wcel crnk cfv csuc cr1 ckard cfn con0 wceq onrankid sylib eleq1d
      nnon ibir peano2 cen wbr r1fin 3syl cv cab cscott kardval wss breq1 elabg
      enrefnn mpbird scottssr1 syl eqsstrid ssfid ) ACDZAEFZGZHFZAIFZUPUQCDZURC
      DUSJDUPVAUPUQACUPAKDUQALAPAMNOQUQRURUAUBUPUTBUCZASTZBUDZUEZUSBAUFUPAVDDZV
      EUSUGUPVFAASTZAUJVCVGBACVBAASUHUIUKAVDULUMUNUO $.
  $}

  ${
    $d A x $.
    $( The ` kard ` cardinal number of a finite set is finite.  (Contributed by
       BTernaryTau, 3-Jul-2026.) $)
    kardfi $p |- ( A e. Fin -> ( kard ` A ) e. Fin ) $=
      ( vx cfn wcel ckard cfv cv cen wbr com wrex wa wex df-rex kardeng biimprd
      isfi wceq wi biimtrid kardnnfi eleq1a syl imp a1i sylan2d exlimdv pm2.43i
      ) ACDZAEFZCDZUIABGZHIZBJKZUIUKBAQUNULJDZUMLZBMUIUKUMBJNUIUPUKBUIUMUJULEFZ
      RZUOUKUIURUMAULCOPUOURLUKSUIUOURUKUOUQCDURUKSULUAUQCUJUBUCUDUEUFUGTTUH $.
  $}

  ${
    $d A x $.
    $( An upper bound on the rank of a ` kard ` cardinal.  (Contributed by
       BTernaryTau, 4-Jul-2026.) $)
    rankkardu $p |- ( rank ` ( kard ` A ) ) C_ suc ( rank ` A ) $=
      ( vx cvv wcel ckard cfv crnk csuc wss cv cen wbr cab cscott fveq2i enrefg
      kardval breq1 c0 wceq elabg mpbird rankscottu eqsstrid wn kardeq0 rankeq0
      syl fvex 0ss sseq1 mpbiri sylbi sylbir pm2.61i ) ACDZAEFZGFZAGFHZIZUPURBJ
      ZAKLZBMZNZGFZUSUQVDGBAQOUPAVCDZVEUSIUPVFAAKLZACPVBVGBACVAAAKRUAUBAVCUCUHU
      DUPUEUQSTZUTAUFVHURSTZUTUQAEUIUGVIUTSUSIUSUJURSUSUKULUMUNUO $.
  $}

  ${
    $d A x $.
    $( The Fundamental Theorem of Enumeration (see
~ https://sites.math.rutgers.edu/~~zeilberg/mamarim/mamarimPDF/enu.pdf ),
       extended to all sets.

       The expression ` U_ x e. A ( { x } X. B ) ` can be thought of as
       expressing an indexed disjoint union ` |_| x e. A B ` where each ` B `
       has its elements tagged with the set ` x ` that generated it.  See the
       comment directly before ~ undjudom for context on disjoint union as a
       representation of cardinal addition.

       This theorem is not limited to numerable sets, but it also does not
       depend on AC. See ~ 1enumen for a version that uses equinumerosity ,
       ~ 1enumcard for a version that uses the ` card ` function, and ~ 1enum
       for a version that uses an explicit sum of complex number 1s.

       (Contributed by BTernaryTau, 4-Jul-2026.) $)
    1enumkard $p |- ( A e. _V ->
        ( kard ` A ) = ( kard ` U_ x e. A ( { x } X. 1o ) ) ) $=
      ( cvv wcel csn c1o cxp ciun cen wbr ckard cfv wceq 1enumen kardenir syl
      cv ) BCDBABAQEFGHZIJBKLRKLMABNBROP $.
    $( $j usage '1enumkard' avoids 'ax-ac' 'ax-ac2'; $)
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  G&ouml;del operations
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $c Cnv2 $.  $( Second converse $)
  $c Cnv3 $.  $( Third converse $)
  $c ~F1 $.  $( First G&ouml;del operation $)
  $c ~F2 $.  $( Second G&ouml;del operation $)
  $c ~F3 $.  $( Third G&ouml;del operation $)
  $c ~F4 $.  $( Fourth G&ouml;del operation $)
  $c ~F5 $.  $( Fifth G&ouml;del operation $)
  $c ~F6 $.  $( Sixth G&ouml;del operation $)
  $c ~F7 $.  $( Seventh G&ouml;del operation $)
  $c ~F8 $.  $( Eighth G&ouml;del operation $)
  $c ~F $.  $( Combined G&ouml;del operations $)

  $( Extend the definition of a class to include the second converse
     function. $)
  ccnv2 $a class Cnv2 $.

  $( Extend the definition of a class to include the third converse
     function. $)
  ccnv3 $a class Cnv3 $.

  $( Extend the definition of a class to include the first G&ouml;del
     operation. $)
  cgdlop1 $a class ~F1 $.

  $( Extend the definition of a class to include the second G&ouml;del
     operation. $)
  cgdlop2 $a class ~F2 $.

  $( Extend the definition of a class to include the third G&ouml;del
     operation. $)
  cgdlop3 $a class ~F3 $.

  $( Extend the definition of a class to include the fourth G&ouml;del
     operation. $)
  cgdlop4 $a class ~F4 $.

  $( Extend the definition of a class to include the fifth G&ouml;del
     operation. $)
  cgdlop5 $a class ~F5 $.

  $( Extend the definition of a class to include the sixth G&ouml;del
     operation. $)
  cgdlop6 $a class ~F6 $.

  $( Extend the definition of a class to include the seventh G&ouml;del
     operation. $)
  cgdlop7 $a class ~F7 $.

  $( Extend the definition of a class to include the eighth G&ouml;del
     operation. $)
  cgdlop8 $a class ~F8 $.

  $( Extend the definition of a class to include the combined G&ouml;del
     operations. $)
  cgdlopc $a class ~F $.

  ${
    $d w x y z $.
    $( Define a function that returns the second converse of a set.  The second
       converse of a set takes all ordered triples in the set and rotates them
       so the last argument becomes the first argument.  Based on Definition
       14.1(1) of [TakeutiZaring] p. 143.  (Contributed by BTernaryTau,
       2-Sep-2026.) $)
    df-cnv2 $a |- Cnv2 = ( w e. _V |->
        { <. <. x , y >. , z >. | <. <. z , x >. , y >. e. w } ) $.
  $}

  ${
    $d w x y z $.
    $( Define a function that returns the third converse of a set.  The third
       converse of a set takes all ordered triples in the set and swaps the
       second and third arguments.  Based on Definition 14.1(2) of
       [TakeutiZaring] p. 143.  (Contributed by BTernaryTau, 2-Sep-2026.) $)
    df-cnv3 $a |- Cnv3 = ( w e. _V |->
        { <. <. x , y >. , z >. | <. <. x , z >. , y >. e. w } ) $.
  $}

  ${
    $d x y $.
    $( Define the first G&ouml;del operation.  This function takes two
       arguments and returns the unordered pair containing both (see ~ df-pr ).
       Based on the first case of Definition 14.2 of [TakeutiZaring] p. 144.
       (Contributed by BTernaryTau, 2-Sep-2026.) $)
    df-gdlop1 $a |- ~F1 = ( x e. _V , y e. _V |-> { x , y } ) $.
  $}

  ${
    $d x y $.
    $( Define the second G&ouml;del operation.  This function takes two
       arguments and returns the intersection of the first argument with the
       membership relation (see ~ df-in and ~ df-eprel ).  The second argument
       is ignored.  Based on the second case of Definition 14.2 of
       [TakeutiZaring] p. 144.  (Contributed by BTernaryTau, 2-Sep-2026.) $)
    df-gdlop2 $a |- ~F2 = ( x e. _V , y e. _V |-> ( x i^i _E ) ) $.
  $}

  ${
    $d x y $.
    $( Define the third G&ouml;del operation.  This function takes two
       arguments and returns the first argument minus the second argument (see
       ~ df-dif ).  Based on the third case of Definition 14.2 of
       [TakeutiZaring] p. 144.  (Contributed by BTernaryTau, 2-Sep-2026.) $)
    df-gdlop3 $a |- ~F3 = ( x e. _V , y e. _V |-> ( x \ y ) ) $.
  $}

  ${
    $d x y $.
    $( Define the fourth G&ouml;del operation.  This function takes two
       arguments and returns the first argument restricted to the second
       argument (see ~ df-res ).  Based on the fourth case of Definition 14.2
       of [TakeutiZaring] p. 144.  (Contributed by BTernaryTau, 2-Sep-2026.) $)
    df-gdlop4 $a |- ~F4 = ( x e. _V , y e. _V |-> ( x |` y ) ) $.
  $}

  ${
    $d x y $.
    $( Define the fifth G&ouml;del operation.  This function takes two
       arguments and returns the intersection of the first argument with the
       domain of the second argument (see ~ df-in and ~ df-dm ).  Based on the
       fifth case of Definition 14.2 of [TakeutiZaring] p. 144.  (Contributed
       by BTernaryTau, 2-Sep-2026.) $)
    df-gdlop5 $a |- ~F5 = ( x e. _V , y e. _V |-> ( x i^i dom y ) ) $.
  $}

  ${
    $d x y $.
    $( Define the sixth G&ouml;del operation.  This function takes two
       arguments and returns the intersection of the first argument with the
       converse of the second argument (see ~ df-in and ~ df-cnv ).  Based on
       the sixth case of Definition 14.2 of [TakeutiZaring] p. 144.
       (Contributed by BTernaryTau, 2-Sep-2026.) $)
    df-gdlop6 $a |- ~F6 = ( x e. _V , y e. _V |-> ( x i^i `' y ) ) $.
  $}

  ${
    $d x y $.
    $( Define the seventh G&ouml;del operation.  This function takes two
       arguments and returns the intersection of the first argument with the
       second converse of the second argument (see ~ df-in and ~ df-cnv2 ).
       Based on the seventh case of Definition 14.2 of [TakeutiZaring] p. 144.
       (Contributed by BTernaryTau, 2-Sep-2026.) $)
    df-gdlop7 $a |- ~F7 = ( x e. _V , y e. _V |-> ( x i^i ( Cnv2 ` y ) ) ) $.
  $}

  ${
    $d x y $.
    $( Define the eighth G&ouml;del operation.  This function takes two
       arguments and returns the intersection of the first argument with the
       third converse of the second argument (see ~ df-in and ~ df-cnv3 ).
       Based on the eighth case of Definition 14.2 of [TakeutiZaring] p. 144.
       (Contributed by BTernaryTau, 2-Sep-2026.) $)
    df-gdlop8 $a |- ~F8 = ( x e. _V , y e. _V |-> ( x i^i ( Cnv3 ` y ) ) ) $.
  $}

  ${
    $d n x y $.
    $( Define the combined G&ouml;del operations.  This function takes three
       arguments and uses the first to determine which of the eight G&ouml;del
       operations ~ df-gdlop1 through ~ df-gdlop8 to apply to the second and
       third arguments.  Based on Definition 14.2 of [TakeutiZaring] p. 144.
       (Contributed by BTernaryTau, 2-Sep-2026.) $)
    df-gdlopc $a |- ~F = ( n e. ( 9o \ { (/) } ) , x e. _V , y e. _V |->
        if ( n = 1o , ( ~F1 ` <. x , y >. ) ,
        if ( n = 2o , ( ~F2 ` <. x , y >. ) ,
        if ( n = 3o , ( ~F3 ` <. x , y >. ) ,
        if ( n = 4o , ( ~F4 ` <. x , y >. ) ,
        if ( n = 5o , ( ~F5 ` <. x , y >. ) ,
        if ( n = 6o , ( ~F6 ` <. x , y >. ) ,
        if ( n = 7o , ( ~F7 ` <. x , y >. ) ,
        ( ~F8 ` <. x , y >. ) ) ) ) ) ) ) ) ) $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  The constructible universe
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $c LexOrd $.  $( Lexicographical ordering of ` On X. On ` $)
  $c _R0 $.  $( Set-like well-ordering of ` On X. On ` $)
  $c _J0 $.  $( Order isomorphism from ` On X. On ` to ` On ` $)
  $c _J $.  $( Order isomorphism from ` ( On X. On ) X. 9o ` to ` On ` $)
  $c _K1 $.  $( First argument of the ` _J ` function $)
  $c _K2 $.  $( Second argument of the ` _J ` function $)
  $c _K3 $.  $( Third argument of the ` _J ` function $)
  $c _FL $.  $( Constructible sets function $)
  $c _L $.  $( Class of constructible sets $)

  $( Extend the definition of a class to include the lexicographical ordering
     of ` On X. On ` . $)
  clexo $a class LexOrd $.

  $( Extend the definition of a class to include a set-like well-ordering of
     ` On X. On ` . $)
  cr0 $a class _R0 $.

  $( Extend the definition of a class to include the ` _R0 ` order isomorphism
     from ` On X. On ` to ` On ` . $)
  ccj0 $a class _J0 $.

  $( Extend the definition of a class to include an order isomorphism from
     ` ( On X. On ) X. 9o ` to ` On ` . $)
  cj $a class _J $.

  $( Extend the definition of a class to include the first argument of the
     ` _J ` function. $)
  ck1 $a class _K1 $.

  $( Extend the definition of a class to include the second argument of the
     ` _J ` function. $)
  ck2 $a class _K2 $.

  $( Extend the definition of a class to include the third argument of the
     ` _J ` function. $)
  ck3 $a class _K3 $.

  $( Extend the definition of a class to include the constructible sets
     function. $)
  cfnl $a class _FL $.

  $( Extend the definition of a class to include the class of all constructible
     sets. $)
  cl $a class _L $.

  ${
    $d x y $.
    $( Define the lexicographical ordering of ` On X. On ` .  Based on
       Definition 7.55 of [TakeutiZaring] p. 54.  (Contributed by BTernaryTau,
       2-Sep-2026.) $)
    df-lexo $a |- LexOrd = { <. x , y >. | ( ( x e. ( On X. On ) /\
        y e. ( On X. On ) ) /\ ( ( 1st ` x ) e. ( 1st ` y ) \/
        ( ( 1st ` x ) = ( 1st ` y ) /\ ( 2nd ` x ) e. ( 2nd ` y ) ) ) ) } $.
  $}

  ${
    $d x y $.
    $( Define a particular set-like well-ordering of ` On X. On ` using the
       lexicographical ordering ` LexOrd ` .  Based on Definition 7.57 of
       [TakeutiZaring] p. 54.  (Contributed by BTernaryTau, 2-Sep-2026.) $)
    df-r0 $a |- _R0 = { <. x , y >. | ( ( x e. ( On X. On ) /\
        y e. ( On X. On ) ) /\
        ( ( ( 1st ` x ) u. ( 2nd ` x ) ) e. ( ( 1st ` y ) u. ( 2nd ` y ) ) \/
        ( ( ( 1st ` x ) u. ( 2nd ` x ) ) = ( ( 1st ` y ) u. ( 2nd ` y ) ) /\
        x LexOrd y ) ) ) } $.
  $}

  $( Define the ` _R0 ` order isomorphism from ` On X. On ` to ` On ` .
     Equivalent to Definition 7.59 of [TakeutiZaring] p. 55.  (Contributed by
     BTernaryTau, 2-Sep-2026.) $)
  df-j0 $a |- _J0 = `' OrdIso ( _R0 , ( On X. On ) ) $.

  ${
    $d n x y $.
    $( Define an order isomorphism from ` ( On X. On ) X. 9o ` to ` On ` .
       Based on Definition 15.2 of [TakeutiZaring] p. 155.  (Contributed by
       BTernaryTau, 2-Sep-2026.) $)
    df-j $a |- _J = ( x e. On , y e. On , n e. 9o |->
        ( ( 9o .o ( _J0 ` <. x , y >. ) ) +o n ) ) $.
  $}

  ${
    $d n x y z $.
    $( Define a function that takes an ordinal and returns the first argument
       of the ordered triple ` <. x , y , n >. ` such that the ordinal equals
       ` ( J `` <. x , y , n >. ) ` .  Based on the first case of Definition
       15.7 of [TakeutiZaring] p. 156.  (Contributed by BTernaryTau,
       2-Sep-2026.) $)
    df-k1 $a |- _K1 = { <. z , x >. |
        ( x e. On /\ E. n e. 9o E. y e. On z = ( _J ` <. x , y , n >. ) ) } $.
  $}

  ${
    $d n x y z $.
    $( Define a function that takes an ordinal and returns the second argument
       of the ordered triple ` <. x , y , n >. ` such that the ordinal equals
       ` ( J `` <. x , y , n >. ) ` .  Based on the second case of Definition
       15.7 of [TakeutiZaring] p. 156.  (Contributed by BTernaryTau,
       2-Sep-2026.) $)
    df-k2 $a |- _K2 = { <. z , y >. |
        ( y e. On /\ E. n e. 9o E. x e. On z = ( _J ` <. x , y , n >. ) ) } $.
  $}

  ${
    $d n x y z $.
    $( Define a function that takes an ordinal and returns the third argument
       of the ordered triple ` <. x , y , n >. ` such that the ordinal equals
       ` ( J `` <. x , y , n >. ) ` .  Based on the third case of Definition
       15.7 of [TakeutiZaring] p. 156.  (Contributed by BTernaryTau,
       2-Sep-2026.) $)
    df-k3 $a |- _K3 = { <. z , n >. |
        ( n e. 9o /\ E. x e. On E. y e. On z = ( _J ` <. x , y , n >. ) ) } $.
  $}

  $( Define a function whose range contains all and only the constructible
     sets.  Based on Definition 15.13 of [TakeutiZaring] p. 158.  (Contributed
     by BTernaryTau, 3-Sep-2026.) $)
  df-fnl $a |- _FL = recs ( ( x e. _V |-> if ( ( _K3 ` dom x ) = (/) , ran x ,
      ( ~F ` <. ( _K3 ` dom x ) , ( x ` ( _K1 ` dom x ) ) ,
      ( x ` ( _K2 ` dom x ) ) >. ) ) ) ) $.

  $( Define the class of all constructible sets.  Definition 15.15 of
     [TakeutiZaring] p. 158.  (Contributed by BTernaryTau, 3-Sep-2026.) $)
  df-l $a |- _L = ( _FL " On ) $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Global choice
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d f x $.  $d ph x z $.  $d G f z $.
    gblacfnacd.1 $e |- ( ph -> G Fn _V ) $.
    gblacfnacd.2 $e |- ( ph -> A. z ( z =/= (/) -> ( G ` z ) e. z ) ) $.
    $( If ` G ` is a global choice function, then the Axiom of Choice (in the
       form of the right-hand side of ~ dfac4 ) holds.  Note that ` G ` must be
       a proper class by ~ fndmexb .  This means we cannot show that the
       existence of a class that behaves as a global choice function is
       sufficient because we only have existential quantifiers for sets, not
       (proper) classes.  However, if a class variant of ~ exlimiv were
       available, then it could be used alongside the closed form of this
       theorem to prove that result.  (Contributed by BTernaryTau,
       12-Dec-2024.) $)
    gblacfnacd $p |- ( ph ->
        A. x E. f ( f Fn x /\ A. z e. x ( z =/= (/) -> ( f ` z ) e. z ) ) ) $=
      ( cv wfn c0 wne cfv wcel wi wral wa wex cvv eleq1d imbi2d cres wfun fnfun
      resfunexg elvd 3syl wss fnssres sylancl 19.21bi fvres syl5ibrcom ralrimiv
      ssv jca wceq fneq1 fveq1 ralbidv anbi12d spcedv alrimiv ) ADHZBHZIZCHZJKZ
      VFVCLZVFMZNZCVDOZPZDQBAVLEVDUAZVDIZVGVFVMLZVFMZNZCVDOZPDRVMAERIZEUBZVMRMZ
      FREUCVTWABEVDRUDUEUFAVNVRAVSVDRUGVNFVDUNRVDEUHUIAVQCVDAVQVFVDMZVGVFELZVFM
      ZNZAWECGUJWBVPWDVGWBVOWCVFVFVDEUKSTULUMUOVCVMUPZVEVNVKVRVDVCVMUQWFVJVQCVD
      WFVIVPVGWFVHVOVFVFVCVMURSTUSUTVAVB $.
    $( $j usage 'gblacfnacd' avoids 'ax-ac' 'ax-ac2'; $)
  $}

  ${
    $d A x y $.
    $( Lemma for ~ onvf1od .  (Contributed by BTernaryTau, 2-Dec-2025.) $)
    onvf1odlem1 $p |- ( A e. V -> E. x e. On E. y e. ( R1 ` x ) -. y e. A ) $=
      ( wcel cv wn cr1 cfv con0 wrex cvv wex wral wceq nvel bitri sylibr rexv
      wa wb eleq1 eqcoms mtbii con2i wal eqv alex con2bii ax-1 ralrimiv tz9.13g
      eximi rgen r19.29r r19.29 reximi mpan2 3syl rexcom exancom df-rex 3bitr4i
      syl rexbii sylib ) CDEZBFZCEZGZVHAFZHIZEZTZAJKZBLKZVJBVLKZAJKZVGVJBMZVJAJ
      NZBLKZVPVGCLOZGVSWBVGWBLDEZVGDPWCVGUALCLCDUBUCUDUEWBVSWBVIBUFVSGBCUGVIBUH
      QUIRVSVTBMWAVJVTBVJVJAJVJVKJEUJUKUMVTBSRWAVMAJKZBLNZVPWDBLAVHLULUNWAWETVT
      WDTZBLKVPVTWDBLUOWFVOBLVJVMAJUPUQVDURUSVPVNBLKZAJKVRVNBALJUTWGVQAJVNBMVMV
      JTBMWGVQVJVMBVAVNBSVJBVLVBVCVEQVF $.
    $( $j usage 'onvf1odlem1' avoids 'ax-ac' 'ax-ac2'; $)
  $}

  ${
    $d A z $.  $d G z $.  $d M z $.  $d M v $.  $d A v x y $.
    onvf1odlem2.1 $e |- ( ph -> A. z ( z =/= (/) -> ( G ` z ) e. z ) ) $.
    onvf1odlem2.2 $e |- M = |^| { x e. On | E. y e. ( R1 ` x ) -. y e. A } $.
    onvf1odlem2.3 $e |- N = ( G ` ( ( R1 ` M ) \ A ) ) $.
    $( Lemma for ~ onvf1od .  (Contributed by BTernaryTau, 2-Dec-2025.) $)
    onvf1odlem2 $p |- ( ph -> ( A e. V -> N e. ( ( R1 ` M ) \ A ) ) ) $=
      ( vv wcel cr1 cfv cv c0 wn wrex cdif wne wal con0 onvf1odlem1 crab nfrab1
      cint nfcv nfint nffv nfv nfrexw wceq eleq1w notbid cbvrexvw fveq2 rexeqdv
      bitrid onminsb fveq2i rexeqi sylibr syl wex wss df-rex nss ssdif0 3bitr2i
      wi wa necon3bbii sylib fvex difexi neeq1 id eleq12d imbi12d syl2im eleq1i
      spcv imbitrrdi ) AEINZGOPZEUAZFPZWHNZHWHNADQZRUBZWKFPZWKNZVLZDUCWFWHRUBZW
      JJWFMQZENZSZMWGTZWPWFCQZENZSZCBQZOPZTZBUDTZWTBCEIUEXGWSMXFBUDUFZUHZOPZTZW
      TXFXKBWSBMXJBXIOBOUIBXHXFBUDUGUJUKWSBULUMXFWSMXETXDXIUNZXKXCWSCMXEXAWQUNX
      BWRCMEUOUPUQXLWSMXEXJXDXIOURUSUTVAWSMWGXJGXIOKVBVCVDVEWTWQWGNWSVMMVFWGEVG
      ZSWPWSMWGVHMWGEVIXMWHRWGEVJVNVKVOWOWPWJVLDWHWGEGOVPVQWKWHUNZWLWPWNWJWKWHR
      VRXNWMWIWKWHWKWHFURXNVSVTWAWDWBHWIWHLWCWE $.
    $( $j usage 'onvf1odlem2' avoids 'ax-ac' 'ax-ac2'; $)
  $}

  ${
    $d C r $.  $d G w $.  $d N r $.  $d A r u v $.  $d F r u v $.
    $d r s t w $.  $d s t w x y $.  $d r s t u v $.
    onvf1odlem3.1 $e |- M =
        |^| { x e. On | E. y e. ( R1 ` x ) -. y e. ran w } $.
    onvf1odlem3.2 $e |- N = ( G ` ( ( R1 ` M ) \ ran w ) ) $.
    onvf1odlem3.3 $e |- F = recs ( ( w e. _V |-> N ) ) $.
    onvf1odlem3.4 $e |- B =
        |^| { u e. On | E. v e. ( R1 ` u ) -. v e. ( F " A ) } $.
    onvf1odlem3.5 $e |- C = ( G ` ( ( R1 ` B ) \ ( F " A ) ) ) $.
    $( Lemma for ~ onvf1od .  The value of ` F ` at an ordinal ` A ` .
       (Contributed by BTernaryTau, 2-Dec-2025.) $)
    onvf1odlem3 $p |- ( A e. On -> ( F ` A ) = C ) $=
      ( vt con0 cfv vr vs wcel cres cvv cmpt tfr2 wceq wfun wfn fnfun resfunexg
      tfr1 ax-mp mpan crn cr1 wrex crab cint cdif cima weq eleq1w notbid adantl
      cv wn fveq2 adantr cbvrexdva2 cbvrabv rneq df-ima eqtr4di rexbidv rabbidv
      wb eleq2d eqtrid inteqd fveq2d difeq12d cbvmptv fvexi fvmpt syl eqtrd ) F
      SUCZFITIFUDZCUELUFZTZHFIWKOUGWIWJUEUCZWLHUHIUIZWIWMISUJWNIWKOUMSIUKUNIFSU
      LUOUAWJRVGZUAVGZUPZUCZVHZRUBVGZUQTZURZUBSUSZUTZUQTZWQVAZJTZHUEWKWPWJUHZXG
      GUQTZIFVBZVAZJTHXHXFXKJXHXEXIWQXJXHXDGUQXHXDDVGZXJUCZVHZDEVGZUQTZURZESUSZ
      UTGXHXCXRXHXCXLWQUCZVHZDXPURZESUSXRXBYAUBESUBEVCZWSXTRDXAXPRDVCZWSXTVRYBY
      CWRXSRDWQVDVEVFYBXAXPUHYCWTXOUQVIVJVKVLXHYAXQESXHXTXNDXPXHXSXMXHWQXJXLXHW
      QWJUPXJWPWJVMIFVNVOZVSVEVPVQVTWAPVOWBYDWCWBQVOCUAUELXGCUAVCZLKUQTZCVGZUPZ
      VAZJTXGNYEYIXFJYEYFXEYHWQYEKXDUQYEKBVGYHUCZVHZBAVGZUQTZURZASUSZUTXDMYEYOX
      CYEYOWOYHUCZVHZRXAURZUBSUSXCYNYRAUBSAUBVCZYKYQBRYMXABRVCZYKYQVRYSYTYJYPBR
      YHVDVEVFYSYMXAUHYTYLWTUQVIVJVKVLYEYRXBUBSYEYQWSRXAYEYPWRYEYHWQWOYGWPVMZVS
      VEVPVQVTWAVTWBUUAWCWBVTWDHXKJQWEWFWGWH $.
    $( $j usage 'onvf1odlem3' avoids 'ax-ac' 'ax-ac2'; $)
  $}

  ${
    $d B z $.  $d G z $.  $d G w $.  $d w x y $.  $d F t z $.  $d ph s t v $.
    $d F t u v $.  $d F r s v $.
    onvf1odlem4.1 $e |- ( ph -> A. z ( z =/= (/) -> ( G ` z ) e. z ) ) $.
    onvf1odlem4.2 $e |- M =
        |^| { x e. On | E. y e. ( R1 ` x ) -. y e. ran w } $.
    onvf1odlem4.3 $e |- N = ( G ` ( ( R1 ` M ) \ ran w ) ) $.
    onvf1odlem4.4 $e |- F = recs ( ( w e. _V |-> N ) ) $.
    onvf1odlem4.5 $e |- B =
        |^| { u e. On | E. v e. ( R1 ` u ) -. v e. ( F " t ) } $.
    onvf1odlem4.6 $e |- C = ( G ` ( ( R1 ` B ) \ ( F " t ) ) ) $.
    $( Lemma for ~ onvf1od .  If the range of ` F ` does not exist, then it
       must equal the universe.  (Contributed by BTernaryTau, 4-Dec-2025.) $)
    onvf1odlem4 $p |- ( ph -> ( -. ran F e. _V -> ran F = _V ) ) $=
      ( vs vr crn cvv wceq wcel wn cv wal wi eqv wex exnal wa crnk cfv wss wral
      con0 wrex cr1 wfn wb cmpt tfr1 fvelrnb ax-mp onvf1odlem3 adantl cima cdif
      wfun vex funimaex onvf1odlem2 eldifad adantr eqeltrd rankr1ai onvf1odlem1
      fnfun crab cint onintrab2 eleq1i bitr4i mpbi oneli fveq2 rexeqdv onnminsb
      mpi eleq2i dfral2 3imtr4g mpcom imassrn sseli ralimi syl 2fveq3 syl5ibcom
      raleqdv rexlimdva biimtrid imp df-ral sylib 19.21bi con3d rankon ssrankr1
      3syl imbitrrdi impancom ralrimiv sseq2 ralbidv rspcev mpan bndrank expcom
      exlimiv sylbir sylnbi com12 con1d ) AKUCZUDUEZYHUDUFZYIUGAYJYIFUHZYHUFZFU
      IZAYJUJZFYHUKYMUGYLUGZFULYNYLFUMYOYNFAYOYJAYOUNZUAUHZUOUPZYKUOUPZUQZUAYHU
      RZYRUBUHZUQZUAYHURZUBUSUTZYJYPYTUAYHAYQYHUFZYOYTAUUFUNZYOYKYRVAUPZUFZUGZY
      TUUGUUIYLUUGUUIYLUJZFUUGYLFUUHURZUUKFUIAUUFUULUUFHUHZKUPZYQUEZHUSUTZAUULK
      USVBZUUFUUPVCKEUDNVDRVEZHUSYQKVFVGAUUOUULHUSAUUMUSUFZUNZYLFUUNUOUPZVAUPZU
      RZUUOUULUUTUUNIVAUPZUFUVAIUFZUVCUUTUUNJUVDUUSUUNJUEABCEFGUUMIJKLMNPQRSTVH
      VIAJUVDUFUUSAJUVDKUUMVJZAUVFUDUFZJUVDUVFVKUFKVLZUVGUUQUVHUURUSKWAVGKUUMHV
      MVNVGZAGFDUVFLIJUDOSTVOWLVPVQVRUUNIVSUVEYKUVFUFZFUVBURZUVCUVAUSUFZUVEUVKI
      UVAUVJUGZFGUHZVAUPZUTZGUSUTZIUSUFZUVGUVQUVIGFUVFUDVTVGUVQUVPGUSWBWCZUSUFU
      VRUVPGWDIUVSUSSWEWFWGWHUVLUVAUVSUFUVMFUVBUTZUGUVEUVKUVPUVTGUVAUVNUVAUEUVM
      FUVOUVBUVNUVAVAWIWJWKIUVSUVASWMUVJFUVBWNWOWPUVJYLFUVBUVFYHYKKUUMWQWRWSWTX
      MUUOYLFUVBUUHUUNYQVAUOXAXCXBXDXEXFYLFUUHXGXHXIXJYRUSUFYTUUJVCYQXKYKYRFVMX
      LVGXNXOXPYSUSUFUUAUUEYKXKUUDUUAUBYSUSUUBYSUEUUCYTUAYHUUBYSYRXQXRXSXTUBUAY
      HYAXMYBYCYDYEYFYG $.
    $( $j usage 'onvf1odlem4' avoids 'ax-ac' 'ax-ac2'; $)
  $}

  ${
    $d G z $.  $d G w $.  $d ph t v $.  $d w x y $.  $d F t u v z $.
    onvf1od.1 $e |- ( ph -> A. z ( z =/= (/) -> ( G ` z ) e. z ) ) $.
    onvf1od.2 $e |- M = |^| { x e. On | E. y e. ( R1 ` x ) -. y e. ran w } $.
    onvf1od.3 $e |- N = ( G ` ( ( R1 ` M ) \ ran w ) ) $.
    onvf1od.4 $e |- F = recs ( ( w e. _V |-> N ) ) $.
    $( If ` G ` is a global choice function, then ` F ` is a bijection from the
       ordinals to the universe.  This is the ZFC version of (1 ` -> ` 2) in
       ~ https://tinyurl.com/hamkins-gblac .  (Contributed by BTernaryTau,
       5-Dec-2025.) $)
    onvf1od $p |- ( ph -> F : On -1-1-onto-> _V ) $=
      ( vt vv vu con0 cvv wcel wn wf1 crn wceq wf1o wf ccnv wfun wfn cmpt dffn2
      tfr1 mpbi cv cfv cima wral wa wrex crab cint cdif eqid onvf1odlem3 adantl
      cr1 fnfun vex funimaex mp2b onvf1odlem2 eldifbd adantr eqneltrd ralrimiva
      mpi fvex eldif mpbiran ralbii tz7.48-2 sylbir df-f1 biimpri sylancr onprc
      f1f1orn f1of1 3syl f1dmex sylan stoic1a mpan2 onvf1odlem4 dff1o5 sylanbrc
      syl mpd ) AQRFUAZFUBZRUCZQRFUDAQRFUEZFUFUGZWRFQUHZXAFERIUIMUKZQFUJULANUMZ
      FUNZFXEUOZSTZNQUPZXBAXHNQAXEQSZUQXFOUMXGSTOPUMVEUNURPQUSUTZVEUNZXGVAZGUNZ
      XGXJXFXNUCABCEOPXEXKXNFGHIKLMXKVBZXNVBZVCVDAXNXGSTXJAXNXLXGAXGRSZXNXMSXCF
      UGXQXDQFVFFXENVGVHVIAPODXGGXKXNRJXOXPVJVOVKVLVMVNXIXFRXGVASZNQUPXBXRXHNQX
      RXFRSXHXEFVPXFRXGVQVRVSNRFXDVTWAWPWRXAXBUQQRFWBWCWDZAWSRSZTZWTAQRSZTYAWEA
      XTYBAQWSFUAZXTYBAWRQWSFUDYCXSQRFWFQWSFWGWHQWSRFWIWJWKWLABCDEOPNXKXNFGHIJK
      LMXOXPWMWQQRFWNWO $.
    $( $j usage 'onvf1od' avoids 'ax-ac' 'ax-ac2'; $)
  $}

  ${
    $d R w z $.  $d R t u v $.  $d F w x y z $.  $d F u v x y $.
    $d F s t u v $.  $d F r s t u $.
    vonf1wev.1 $e |- R = { <. x , y >. | ( F ` x ) e. ( F ` y ) } $.
    $( If ` F ` maps the universe one-to-one into the ordinals, then ` R `
       well-orders the universe.  This is the ZFC version of (6 ` -> ` 3) which
       is used in place of (7 ` -> ` 3) in
       ~ https://tinyurl.com/hamkins-gblac .  Note that in NBG set theory the
       antecedent would be something like ` A. X E. F F : X -1-1-> On ` , but
       since we cannot quantify over classes, we instead consider only the case
       ` X = _V ` which is sufficient for this proof.  (Contributed by
       BTernaryTau, 11-Jun-2026.) $)
    vonf1wev $p |- ( F : _V -1-1-> On -> R We _V ) $=
      ( vw vz vt vv vu vs cvv con0 cv weq wral c0 cfv wcel fveq2 vr wf1 wfr wbr
      w3o wwe wne wn wrex wi wal wss cima f1f fimassd wa cdm f1dm ineq1d neeq1d
      inv1 ineqcomi neeq1i bitr2di biimpa imadisjlnd onssmin syl2an2r ex eleq1d
      cin vex eleq2d brab notbii ffvelcdmda elvd ontri1 syl2anc bitr4id ralbidv
      wb wfn f1fn sseq2 ralima sylancl bitr4d rexbidv wceq sseq1 rexima sylibrd
      alrimiv df-fr biantrur imbi1i albii bitr4i sylibr oneltri 3orcomb biimpri
      ssv sylib a1i f1veqaeq mpanr12 3orim123d mpd ralrimivw dfwe2 sylanbrc ) L
      MDUBZLCUCZFNZGNZCUDZFGOZXQXPCUDZUEZGLPZFLPLCUFXNHNZQUGZINZJNZCUDZUHZIYCPZ
      JYCUIZUJZHUKZXOXNYKHXNYDUANZKNZULZKDYCUMZPZUAYPUIZYJXNYDYRXNYPMULYDYPQUGY
      RXNLMDYCLMDUNZUOXNYDUPDYCXNYDDUQZYCVKZQUGZXNUUBLYCVKZQUGYDXNUUAUUCQXNYTLY
      CLMDURUSUTUUCYCQYCLYCYCVAVBVCVDVEVFUAKYPVGVHVIXNYJYFDRZYNULZKYPPZJYCUIZYR
      XNYIUUFJYCXNYIUUDYEDRZULZIYCPZUUFXNYHUUIIYCXNYHUUHUUDSZUHZUUIYGUUKANZDRZB
      NZDRZSZUUHUUPSUUKABYEYFCIVLJVLAIOUUNUUHUUPUUMYEDTVJBJOUUPUUDUUHUUOYFDTVME
      VNVOXNUUDMSZUUHMSZUUIUULWBXNUURJXNLMYFDYSVPVQXNUUSIXNLMYEDYSVPVQUUDUUHVRV
      SVTWAXNDLWCZYCLULZUUFUUJWBLMDWDZYCXDZUUEUUIKILYCDYNUUHUUDWEWFWGWHWIXNUUTU
      VAYRUUGWBUVBUVCYQUUFUAJLYCDYMUUDWJYOUUEKYPYMUUDYNWKWAWLWGWHWMWNXOUVAYDUPZ
      YJUJZHUKYLHJILCWOYKUVEHYDUVDYJUVAYDUVCWPWQWRWSWTXNYBFLXNYAGLXNXPDRZXQDRZS
      ZUVFUVGWJZUVGUVFSZUEZYAXNUVHUVJUVIUEZUVKXNUVFMSZUVGMSZUVLXNUVMFXNLMXPDYSV
      PVQXNUVNGXNLMXQDYSVPVQUVFUVGXAVSUVHUVJUVIXBXEXNUVHXRUVIXSUVJXTUVHXRUJXNXR
      UVHUUQUVFUUPSUVHABXPXQCFVLZGVLZAFOUUNUVFUUPUUMXPDTVJBGOUUPUVGUVFUUOXQDTVM
      EVNXCXFXNXPLSXQLSUVIXSUJUVOUVPLMXPXQDXGXHUVJXTUJXNXTUVJUUQUVGUUPSUVJABXQX
      PCUVPUVOAGOUUNUVGUUPUUMXQDTVJBFOUUPUVFUVGUUOXPDTVMEVNXCXFXIXJXKXKFGLCXLXM
      $.
    $( $j usage 'vonf1wev' avoids 'ax-rep' 'ax-pow' 'ax-reg' 'ax-inf' 'ax-inf2'
       'ax-ac' 'ax-ac2'; $)
  $}

  ${
    $d F x y $.
    vonf1owev.1 $e |- R = { <. x , y >. | ( F ` x ) e. ( F ` y ) } $.
    $( If ` F ` is a bijection from the universe to the ordinals, then ` R `
       well-orders the universe.  This is the ZFC version of (2 ` -> ` 3) in
       ~ https://tinyurl.com/hamkins-gblac .  (Contributed by BTernaryTau,
       6-Dec-2025.)  (Proof shortened by BTernaryTau, 11-Jun-2026.) $)
    vonf1owev $p |- ( F : _V -1-1-onto-> On -> R We _V ) $=
      ( cvv con0 wf1o wf1 wwe f1of1 vonf1wev syl ) FGDHFGDIFCJFGDKABCDELM $.
    $( $j usage 'vonf1owev' avoids 'ax-rep' 'ax-pow' 'ax-reg' 'ax-inf'
       'ax-inf2' 'ax-ac' 'ax-ac2'; $)
  $}

  ${
    $d R w z $.  $d R t u v $.  $d F w x y z $.  $d F u v x y $.
    $d F s t u v $.  $d F r s t u $.
    vonf1owevOLD.1 $e |- R = { <. x , y >. | ( F ` x ) e. ( F ` y ) } $.
    $( Obsolete version of ~ vonf1owev as of 11-Jun-2026.  (Contributed by
       BTernaryTau, 6-Dec-2025.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    vonf1owevOLD $p |- ( F : _V -1-1-onto-> On -> R We _V ) $=
      ( vw vz vt vv vu vs cvv con0 cv weq wral c0 cfv wcel fveq2 vr wfr wbr w3o
      wf1o wwe wne wn wrex wi wal wss cima f1of fimassd wa cdm cin f1odm ineq1d
      neeq1d inv1 ineqcomi neeq1i bitr2di biimpa imadisjlnd onssmin syl2an2r ex
      vex eleq1d eleq2d brab notbii ffvelcdmda elvd syl2anc bitr4id ralbidv wfn
      wb ontri1 f1ofn ssv sseq2 ralima sylancl bitr4d rexbidv wceq sseq1 rexima
      sylibrd alrimiv df-fr biantrur imbi1i albii bitr4i sylibr oneltri 3orcomb
      sylib biimpri a1i wf1 f1of1 f1veqaeq mpanr12 3orim123d ralrimivw sylanbrc
      syl mpd dfwe2 ) LMDUEZLCUBZFNZGNZCUCZFGOZXTXSCUCZUDZGLPZFLPLCUFXQHNZQUGZI
      NZJNZCUCZUHZIYFPZJYFUIZUJZHUKZXRXQYNHXQYGUANZKNZULZKDYFUMZPZUAYSUIZYMXQYG
      UUAXQYSMULYGYSQUGUUAXQLMDYFLMDUNZUOXQYGUPDYFXQYGDUQZYFURZQUGZXQUUELYFURZQ
      UGYGXQUUDUUFQXQUUCLYFLMDUSUTVAUUFYFQYFLYFYFVBVCVDVEVFVGUAKYSVHVIVJXQYMYID
      RZYQULZKYSPZJYFUIZUUAXQYLUUIJYFXQYLUUGYHDRZULZIYFPZUUIXQYKUULIYFXQYKUUKUU
      GSZUHZUULYJUUNANZDRZBNZDRZSZUUKUUSSUUNABYHYICIVKJVKAIOUUQUUKUUSUUPYHDTVLB
      JOUUSUUGUUKUURYIDTVMEVNVOXQUUGMSZUUKMSZUULUUOWBXQUVAJXQLMYIDUUBVPVQXQUVBI
      XQLMYHDUUBVPVQUUGUUKWCVRVSVTXQDLWAZYFLULZUUIUUMWBLMDWDZYFWEZUUHUULKILYFDY
      QUUKUUGWFWGWHWIWJXQUVCUVDUUAUUJWBUVEUVFYTUUIUAJLYFDYPUUGWKYRUUHKYSYPUUGYQ
      WLVTWMWHWIWNWOXRUVDYGUPZYMUJZHUKYOHJILCWPYNUVHHYGUVGYMUVDYGUVFWQWRWSWTXAX
      QYEFLXQYDGLXQXSDRZXTDRZSZUVIUVJWKZUVJUVISZUDZYDXQUVKUVMUVLUDZUVNXQUVIMSZU
      VJMSZUVOXQUVPFXQLMXSDUUBVPVQXQUVQGXQLMXTDUUBVPVQUVIUVJXBVRUVKUVMUVLXCXDXQ
      UVKYAUVLYBUVMYCUVKYAUJXQYAUVKUUTUVIUUSSUVKABXSXTCFVKZGVKZAFOUUQUVIUUSUUPX
      SDTVLBGOUUSUVJUVIUURXTDTVMEVNXEXFXQLMDXGZUVLYBUJZLMDXHUVTXSLSXTLSUWAUVRUV
      SLMXSXTDXIXJXNUVMYCUJXQYCUVMUUTUVJUUSSUVMABXTXSCUVSUVRAGOUUQUVJUUSUUPXTDT
      VLBFOUUSUVIUVJUURXSDTVMEVNXEXFXKXOXLXLFGLCXPXM $.
    $( $j usage 'vonf1owevOLD' avoids 'ax-rep' 'ax-pow' 'ax-reg' 'ax-inf'
       'ax-inf2' 'ax-ac' 'ax-ac2'; $)
  $}

  ${
    $d R w x y z $.
    wevgblacfn.1 $e |- G =
        ( z e. _V |-> U. { y e. z | A. x e. z -. x R y } ) $.
    $( If ` R ` is a well-ordering of the universe, then ` G ` is a global
       choice function.  Here ` G ` maps each set ` z ` to its minimal element
       with respect to ` R ` (except when ` z ` is the empty set, in which case
       it is mapped to the empty set, though this is only done for
       convenience).  This is the ZFC version of (3 ` -> ` 1) in
       ~ https://tinyurl.com/hamkins-gblac .  (Contributed by BTernaryTau,
       29-Jun-2025.) $)
    wevgblacfn $p |- ( R We _V ->
        ( G Fn _V /\ A. z ( z =/= (/) -> ( G ` z ) e. z ) ) ) $=
      ( vw cvv cv c0 wcel wral crab cuni wceq eleq2 eqtrdi wa wex syl wwe wi wn
      wfn wne cfv wal wbr raleq anbi12d rabbidva2 unieqd rab0 unieqi uni0 eqtri
      0ex eqeltrdi adantl wrex wreu wss w3a ssv jctl jctil 3anass sylibr sylan2
      vex wereu csn vsnid mpbiri elrabi unieq unisnv eximi reusn df-rex 3imtr4i
      eleq1 biimparc rexlimiva elexd pm2.61dane ralrimivw fnmpt sylancr eqeltrd
      jca fvmpt2 ex alrimiv ) HDUAZEHUDZCIZJUEZWQEUFZWQKZUBZCUGWOAIBIZDUHUCZAWQ
      LZBWQMZNZHKZCHLWPWOXGCHWOXGWQJWQJOZXGWOXHXFJHXHXFXCAJLZBJMZNZJXHXEXJXHXDX
      IBWQJXHXBWQKXBJKXDXIWQJXBPXCAWQJUIUJUKULXKJNJXJJXIBUMUNUOUPQUQURUSWOWRRZX
      FWQXLXFGIZOZGWQUTZXFWQKZXLXDBWQVAZXOWRWOWQHKZWQHVBZWRVCZXQWRXRXSWRRZRXTWR
      YAXRWRXSWQVDVECVJZVFXRXSWRVGVHBAHWQDHVKVIXEXMVLZOZGSXMWQKZXNRZGSXQXOYDYFG
      YDYEXNYDXMXEKZYEYDYGXMYCKGVMXEYCXMPVNXDBXMWQVOTYDXFYCNXMXEYCVPGVQQWKVRXDB
      GWQVSXNGWQVTWATXNXPGWQXNXPYEXFXMWQWBWCWDTZWEWFWGCHXFEHFWHTWOXACWOWRWTXLWS
      XFWQXLXRXPWSXFOYBYHCHXFWQEFWLWIYHWJWMWNWK $.
    $( $j usage 'wevgblacfn' avoids 'ax-rep' 'ax-pow' 'ax-un' 'ax-reg' 'ax-inf'
       'ax-inf2' 'ax-ac' 'ax-ac2'; $)
  $}

  ${
    $d R w z $.  $d F w x y z $.
    vonf1osev.1 $e |- R = { <. x , y >. | ( F ` x ) e. ( F ` y ) } $.
    $( If ` F ` is a bijection from the universe to the ordinals, then ` R ` is
       a set-like well-ordering of the universe.  This is the ZFC version of (2
       ` -> ` 4) which is used in place of (3 ` -> ` 4) in
       ~ https://tinyurl.com/hamkins-gblac .  This proof takes advantage of the
       fact that the well-order constructed in (2 ` -> ` 3) is also set-like.
       (Contributed by BTernaryTau, 8-Jun-2026.) $)
    vonf1osev $p |- ( F : _V -1-1-onto-> On -> ( R We _V /\ R Se _V ) ) $=
      ( vw vz cvv con0 wf1o wse cep cv wbr cfv wral wcel vex weq fveq2 wwe wiso
      vonf1owev wb eleq1d eleq2d brab fvex epeli bitr4i rgen2w df-isom mpbiran2
      epse isose mpbiri sylbir jca ) HIDJZHCUAHCKZABCDEUCUSHICLDUBZUTVAUSFMZGMZ
      CNZVBDOZVCDOZLNZUDZGHPFHPVHFGHHVDVEVFQZVGAMZDOZBMZDOZQVEVMQVIABVBVCCFRGRA
      FSVKVEVMVJVBDTUEBGSVMVFVEVLVCDTUFEUGVEVFVCDUHUIUJUKFGHICLDULUMVAUTILKIUNH
      ICLDUOUPUQUR $.
    $( $j usage 'vonf1osev' avoids 'ax-pow' 'ax-reg' 'ax-inf' 'ax-inf2' 'ax-ac'
       'ax-ac2'; $)
  $}

  ${
    wevonprcf1o.1 $e |- F = OrdIso ( R , A ) $.
    $( If ` R ` is a set-like well-ordering of the universe and ` A ` is a
       proper class, then ` F ` is a bijection from the ordinals to ` A ` .
       This is the ZFC version of (4 ` -> ` 5) in
       ~ https://tinyurl.com/hamkins-gblac .  (Contributed by BTernaryTau,
       9-Jun-2026.) $)
    wevonprcf1o $p |- ( ( R We _V /\ R Se _V /\ -. A e. _V ) ->
        F : On -1-1-onto-> A ) $=
      ( cvv wwe wse wcel wn w3a con0 cep wiso wf1o wss wi ssv wess ax-mp sess2
      id 3anim123i ordtypeon isof1o 3syl ) EBFZEBGZAEHIZJABFZABGZUHJKALBCMKACNU
      FUIUGUJUHUHAEOZUFUIPAQZAEBRSUKUGUJPULAEBTSUHUAUBABCDUCKALBCUDUE $.
    $( $j usage 'wevonprcf1o' avoids 'ax-pow' 'ax-reg' 'ax-inf' 'ax-inf2'
       'ax-ac' 'ax-ac2'; $)
  $}

  ${
    vonf1oonf1.1 $e |- H = ( F |` A ) $.
    $( If ` F ` is a bijection from the universe to the ordinals, then ` H `
       maps ` A ` one-to-one into the ordinals.  This is the ZFC version of (5
       ` -> ` 6) in ~ https://tinyurl.com/hamkins-gblac .  Note that in NBG set
       theory the antecedent would be something like
       ` A. X ( -. X e. _V -> E. F F : X -1-1-onto-> On ) ` , but since we
       cannot quantify over classes, we instead consider only the case
       ` X = _V ` which is sufficient for this proof.  This theorem can also be
       viewed as (2 ` -> ` 6).  (Contributed by BTernaryTau, 10-Jun-2026.) $)
    vonf1oonf1 $p |- ( F : _V -1-1-onto-> On -> H : A -1-1-> On ) $=
      ( cvv con0 wf1o cres wf1 wss f1of1 ssv f1ssres sylancl f1eq1 ax-mp sylibr
      wceq wb ) EFBGZAFBAHZIZAFCIZTEFBIAEJUBEFBKALEFABMNCUARUCUBSDAFCUAOPQ $.
    $( $j usage 'vonf1oonf1' avoids 'ax-rep' 'ax-pow' 'ax-un' 'ax-reg' 'ax-inf'
       'ax-inf2' 'ax-ac' 'ax-ac2'; $)
  $}

  ${
    $d D z $.  $d A x z $.  $d A w y $.  $d F x z $.  $d F w y $.
    vonf1oonfo.1 $e |- H =
        ( x e. On |-> if ( ( F ` x ) e. A , ( F ` x ) , D ) ) $.
    vonf1oonfo.2 $e |- D = ( F ` |^| { y e. On | ( F ` y ) e. A } ) $.
    $( If ` F ` is a bijection from the ordinals to the universe and ` A ` is
       non-empty, then ` H ` maps the ordinals onto ` A ` .  This is the ZFC
       version of (5 ` -> ` 8) in ~ https://tinyurl.com/hamkins-gblac , though
       it neglects to specify that ` A ` must be non-empty.  Note that in NBG
       set theory the antecedent would be something like
       ` A. X ( -. X e. _V -> E. F F : X -1-1-onto-> On ) ` , but since we
       cannot quantify over classes, we instead consider only the case
       ` X = _V ` which is sufficient for this proof.  This theorem can also be
       viewed as (2 ` -> ` 8).  (Contributed by BTernaryTau, 11-Jun-2026.) $)
    vonf1oonfo $p |- ( ( F : On -1-1-onto-> _V /\ A =/= (/) ) ->
        H : On -onto-> A ) $=
      ( vz vw con0 cvv wa wceq cv cfv wcel wrex elvd eleq1 wf1o wne crn wfo cif
      c0 cab rnmpt wn w3a iffalse 3ad2ant3 wex n0 19.42v f1ofo foelcdmi r19.41v
      syl biimpar reximi sylbir sylan exlimiv sylan2b crab cint nfcv nfint nffv
      nfrab1 nfel1 fveq2 eleq1d onminsb eqeltrid 3adant3 3expia iftrue pm2.61d2
      eqeltrd id syl5ibrcom rexlimdvw abssdv eqsstrid wss wral fveqeq2 f1ocnvdm
      f1ocnvfv2 rspcedvdw iftrued simpl eqtr2d reximdv syl5com ralrimiv ssabral
      ccnv expcom sylibr sseqtrrdi adantr eqssd fvex fvexi fnmpti df-fo mpbiran
      wfn ifex ) KLEUAZCUFUBZMZFUCZCNZKCFUDZXOXPCXOXPIOZAOZEPZCQZYADUEZNZAKRZIU
      GZCAIKYCFGUHZXOYEICXOYDXSCQZAKXOYHYDYCCQZXOYBYIXMXNYBUIZYIXMXNYJUJYCDCYJX
      MYCDNXNYBYADUKULXMXNDCQZYJXOBOZEPZCQZBKRZYKXNXMJOZCQZJUMZYOJCUNXMYRMXMYQM
      ZJUMYOXMYQJUOYSYOJXMYMYPNZBKRZYQYOXMKLEUDZUUAKLEUPUUBUUAJBKLEYPUQSUSUUAYQ
      MYTYQMZBKRYOYTYQBKURUUCYNBKYTYNYQYMYPCTUTVAVBVCVDVBVEYODYNBKVFZVGZEPZCHYN
      UUFCQBBUUFCBUUEEBEVHBUUDYNBKVKVIVJVLYLUUENYMUUFCYLUUEEVMVNVOVPUSVQWAVRYBY
      CYACYBYADVSYBWBWAVTXSYCCTWCWDWEWFXMCXPWGXNXMCYFXPXMYEICWHCYFWGXMYEICXMYAX
      SNZAKRYHYEXMUUGXSEWTPZEPXSNZAUUHKXTUUHXSEWIXMUUHKQIKLXSEWJSXMUUIIKLXSEWKS
      WLYHUUGYDAKUUGYHYDUUGYHMZYCYAXSUUJYBYADUUGYBYHYAXSCTUTWMUUGYHWNWOXAWPWQWR
      YEICWSXBYGXCXDXEXRFKXKXQAKYCFYBYADXTEXFDUUEEHXGXLGXHKCFXIXJXB $.
    $( $j usage 'vonf1oonfo' avoids 'ax-rep' 'ax-pow' 'ax-un' 'ax-reg' 'ax-inf'
       'ax-inf2' 'ax-ac' 'ax-ac2'; $)
  $}

  ${
    $d F u $.  $d H x y $.  $d F v w z $.  $d H u v w $.
    onvfowev.1 $e |- R = { <. x , y >. | ( H ` x ) e. ( H ` y ) } $.
    onvfowev.2 $e |- H = ( z e. _V |-> |^| ( `' F " { z } ) ) $.
    $( If ` F ` maps the ordinals onto the universe, then ` R ` well-orders the
       universe.  This is the ZFC version of (8 ` -> ` 3) in
       ~ https://tinyurl.com/hamkins-gblac .  Note that in NBG set theory the
       antecedent would be something like
       ` A. X ( X =/= (/) -> E. F F : On -onto-> X ) ` , but since we cannot
       quantify over classes, we instead consider only the case ` X = _V `
       which is sufficient for this proof.  (Contributed by BTernaryTau,
       12-Jun-2026.) $)
    onvfowev $p |- ( F : On -onto-> _V -> R We _V ) $=
      ( vv vw vu con0 cvv cv wceq csn cima cint wcel wa wfo wf1 wwe wf cfv wral
      wi ccnv wss c0 wne cdm cnvimass fofn fndmd sseqtrid crn vex forn inisegn0
      eleqtrrid sylib oninton syl2anc adantr fmptd wfun wbr wex fofun fvexd a1i
      cmpt imaeq2d inteqd adantl fvmptdv2 onint eqeltrd eleq1 syl5ibrcom jctild
      sneq mpi imp anbi12d spcedv ex wb elinisegg el2v anbi12i imbitrdi w3a weu
      exbii funeu 3adant3 3simpc wal breq2 simprbi 19.21bbi sylc 3expib exlimdv
      eu4 sylsyld ralrimivw dff13 sylanbrc vonf1wev syl ) LMEUAZMLFUBZMDUCXNMLF
      UDINZFUEZJNZFUEZOZXPXROZUGZJMUFZIMUFXOXNCMEUHZCNZPZQZRZLFXNYHLSZYEMSXNYGL
      UIYGUJUKZYIXNEULZYGLEYFUMXNLELMEUNUOZUPXNYEEUQZSYJXNYEMYMCURLMEUSZVAYEEUT
      VBYGVCVDZVEHVFXNYCIMXNYBJMXNEVGZXTKNZXPEVHZYQXREVHZTZKVIZYALMEVJXNXTYQYDX
      PPZQZSZYQYDXRPZQZSZTZKVIZUUAXNXTUUIXNXTTZUUHXQUUCSZXQUUFSZTZKMXQUUJXPFVKX
      NXTUUMXNXTUULUUKXNUULXTXSUUFSXNXSUUFRZUUFXNFCMYHVMOZXSUUNOHXNCXRYHUUNMFLX
      RMSXNJURZVLXNYIYEXROZYOVEUUQYHUUNOXNUUQYGUUFUUQYFUUEYDYEXRWCVNVOVPVQWDXNU
      UFLUIUUFUJUKZUUNUUFSXNYKUUFLEUUEUMYLUPXNXRYMSUURXNXRMYMUUPYNVAXREUTVBUUFV
      RVDVSXQXSUUFVTWAXNXQUUCRZUUCXNUUOXQUUSOHXNCXPYHUUSMFLXPMSXNIURZVLXNYIYEXP
      OZYOVEUVAYHUUSOXNUVAYGUUCUVAYFUUBYDYEXPWCVNVOVPVQWDXNUUCLUIUUCUJUKZUUSUUC
      SXNYKUUCLEUUBUMYLUPXNXPYMSUVBXNXPMYMUUTYNVAXPEUTVBUUCVRVDVSWBWEYQXQOUUDUU
      KUUGUULYQXQUUCVTYQXQUUFVTWFWGWHUUHYTKUUDYRUUGYSUUDYRWIIKEXPYQMMWJWKUUGYSW
      IJKEXRYQMMWJWKWLWPWMYPYTYAKYPYRYSYAYPYRYSWNYRIWOZYTYAYPYRUVCYSIYQXPEWQWRY
      PYRYSWSUVCYTYAUGZIJUVCYRIVIUVDJWTIWTYRYSIJXPXRYQEXAXGXBXCXDXEXFXHXIXIIJML
      FXJXKABDFGXLXM $.
    $( $j usage 'onvfowev' avoids 'ax-rep' 'ax-pow' 'ax-reg' 'ax-inf' 'ax-inf2'
       'ax-ac' 'ax-ac2'; $)
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Real and complex numbers
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Integer ordering relation.  (Contributed by BTernaryTau, 24-Sep-2023.) $)
  zltp1ne $p |- ( ( A e. ZZ /\ B e. ZZ ) ->
        ( ( A + 1 ) < B <-> ( A < B /\ B =/= ( A + 1 ) ) ) ) $=
    ( cz wcel wa c1 caddc co clt wbr cle wne cr zre peano2re ltlen sylan syl2an
    wb zltp1le anbi1d bitr4d ) ACDZBCDZEZAFGHZBIJZUFBKJZBUFLZEZABIJZUIEUCAMDZBM
    DZUGUJSZUDANBNULUFMDUMUNAOUFBPQRUEUKUHUIABTUAUB $.

  $( Positive integer ordering relation.  (Contributed by BTernaryTau,
     24-Sep-2023.) $)
  nnltp1ne $p |- ( ( A e. NN /\ B e. NN ) ->
        ( ( A + 1 ) < B <-> ( A < B /\ B =/= ( A + 1 ) ) ) ) $=
    ( cn wcel cz c1 caddc co clt wbr wne wa wb nnz zltp1ne syl2an ) ACDAEDBEDAF
    GHZBIJABIJBQKLMBCDANBNABOP $.

  $( Nonnegative integer ordering relation.  (Contributed by BTernaryTau,
     24-Sep-2023.) $)
  nn0ltp1ne $p |- ( ( A e. NN0 /\ B e. NN0 ) ->
        ( ( A + 1 ) < B <-> ( A < B /\ B =/= ( A + 1 ) ) ) ) $=
    ( cn0 wcel cz c1 caddc co clt wbr wne wa wb nn0z zltp1ne syl2an ) ACDAEDBED
    AFGHZBIJABIJBQKLMBCDANBNABOP $.


  $( A finite set is equal to its subset if they are the same size.
     (Contributed by BTernaryTau, 3-Oct-2023.) $)
  fisshasheq $p |- ( ( B e. Fin /\ A C_ B /\ ( # ` A ) = ( # ` B ) ) ->
        A = B ) $=
    ( cfn wcel wss chash cfv wceq w3a ssfi 3adant3 wi wa cen wbr hashen biimp3a
    pm3.2 3ad2ant2 expcom fisseneq 3expa sylsyld 3expb com23 3impia 3com23 mpd
    ) BCDZABEZAFGBFGHZIACDZABHZUIUJULUKBAJKUIUKUJULUMLZUIUKUJUNUIUKMZULUJUMULUO
    UJUMLZULUIUKUPULUIUKIABNOZUJUIUJMZUMULUIUKUQABPQUIULUJURLUKUIUJRSURUQUMUIUJ
    UQUMABUAUBTUCUDTUEUFUGUH $.


  ${
    $d A a $.
    $( The Fundamental Theorem of Enumeration.  According to Doron Zeilberger
       (in
~ https://sites.math.rutgers.edu/~~zeilberg/mamarim/mamarimPDF/enu.pdf ), this
       theorem was independently discovered by several anonymous cave-dwellers.

       Zeilberger also states that "While this formula is still useful after
       all these years, enumerating specific finite sets is no longer
       considered mathematics.  A genuine mathematical fact has to incorporate
       infinitely many facts".  Fortunately, theorems in Metamath are actually
       theorem schemes that correspond to an infinite number of object-language
       theorems, so this concern does not apply to us.

       See ~ 1enumen for a version that uses equinumerosity , ~ 1enumcard for a
       version that uses the ` card ` function, and ~ 1enumkard for a version
       that uses the ` kard ` function.

       (Contributed by BTernaryTau, 26-Jun-2026.) $)
    1enum $p |- ( A e. Fin -> ( # ` A ) = sum_ a e. A 1 ) $=
      ( cfn wcel c1 csu chash cfv fsumconst1 eqcomd ) ACDAEBFAGHABIJ $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Graph theory
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


  ${
    $d A e a b $.  $d B e a b $.  $d e E a b $.  $d e G a b $.  $d e V a b $.
    cplgredgex.1 $e |- V = ( Vtx ` G ) $.
    cplgredgex.2 $e |- E = ( Edg ` G ) $.
    $( Any two (distinct) vertices in a complete graph are connected to each
       other by at least one edge.  (Contributed by BTernaryTau,
       2-Oct-2023.) $)
    cplgredgex $p |- ( G e. ComplGraph -> ( ( A e. V /\ B e. ( V \ { A } ) ) ->
              E. e e. E { A , B } C_ e ) ) $=
      ( va vb ccplgr wcel csn cdif cpr cv wss wrex wa wi simp2 simp3 wceq eleq1
      w3a sneq difeq2d eleq2d anbi12d preq1 sseq1d rexbidv imbi12d anbi2d preq2
      sylan9bb wral iscplgredg ibi rsp2 syl 3ad2ant1 vtocl2d mp2and 3expib ) EK
      LZAFLZBFAMZNZLZABOZCPZQZCDRZVFVGVJUEZVGVJVNVFVGVJUAZVFVGVJUBZVOIPZFLZJPZF
      VRMZNZLZSZVRVTOZVLQZCDRZTZVGVJSZVNTZIJABFVIVPVQVRAUCZWHVGVTVILZSZAVTOZVLQ
      ZCDRZTVTBUCZWJWKWDWMWGWPWKVSVGWCWLVRAFUDWKWBVIVTWKWAVHFVRAUFUGUHUIWKWFWOC
      DWKWEWNVLVRAVTUJUKULUMWQWMWIWPVNWQWLVJVGVTBVIUDUNWQWOVMCDWQWNVKVLVTBAUOUK
      ULUMUPVFVGWHVJVFWGJWBUQIFUQZWHVFWRICJDEFKGHURUSWGIJFWBUTVAVBVCVDVE $.
  $}

  ${
    $d A e $.  $d B e $.  $d e E $.  $d e G $.  $d e V $.
    cusgredgex.1 $e |- V = ( Vtx ` G ) $.
    cusgredgex.2 $e |- E = ( Edg ` G ) $.
    $( Any two (distinct) vertices in a complete simple graph are connected to
       each other by an edge.  (Contributed by BTernaryTau, 3-Oct-2023.) $)
    cusgredgex $p |- ( G e. ComplUSGraph ->
          ( ( A e. V /\ B e. ( V \ { A } ) ) -> { A , B } e. E ) ) $=
      ( ve wcel wa wceq wex wi syl sylib chash cfv c2 adantl cvv ccusgr csn cpr
      cdif wss wrex ccplgr cusgrcplgr cplgredgex imp df-rex wne eldifsni necomd
      cv hashprg mpbid cusgr cusgrusgr usgredgppr sylan adantr eqtr4d simpl cfn
      cn0 2nn0 hashvnfin mp2an fisshasheq syl3an1 3comr 3exp sylc 3com23 3expia
      vex 3impa imdistand eximdv mpd pm3.22 eqcom anbi1i eximi eleq1 ceqsexv ex
      prex ) DUAIZAEIZBEAUBUDZIZJZABUCZCIZWJWNJZHUOZWOKZWRCIZJZHLZWPWQWTWOWRKZJ
      ZHLZXBWQWTWOWRUEZJZHLZXEWQXFHCUFZXHWJWNXIWJDUGIWNXIMDUHABHCDEFGUINUJXFHCU
      KOWQXGXDHWQWTXFXCWJWNWTXFXCMZWJWTWNXJWJWTWNXJWJWTJZWNJZWOPQZWRPQZKZXKXJXL
      XMRXNWNXMRKZXKWNABULZXPWMXQWKWMBABEAUMUNSABEWLUPUQSXKXNRKZWNWJDURIWTXRDUS
      WRCDGUTVAZVBVCXKWNVDXOXKXFXCXKXFXOXCXKWRVEIZXFXOXCXKXRXTXSWRTIRVFIXRXTMHV
      QVGWRRTVHVINWOWRVJVKVLVMVNVRVOVPVSVTWAXDXAHXDXCWTJXAWTXCWBXCWSWTWOWRWCWDO
      WENWTWPHWOABWIWRWOCWFWGOWH $.
  $}

  ${
    cusgredgex2.1 $e |- V = ( Vtx ` G ) $.
    cusgredgex2.2 $e |- E = ( Edg ` G ) $.
    $( Any two distinct vertices in a complete simple graph are connected to
       each other by an edge.  (Contributed by BTernaryTau, 4-Oct-2023.) $)
    cusgredgex2 $p |- ( G e. ComplUSGraph ->
          ( ( A e. V /\ B e. V /\ A =/= B ) -> { A , B } e. E ) ) $=
      ( wcel wne w3a csn cdif wa ccusgr cpr eldifsn necom anbi2i sylbbr anim2i
      3impb cusgredgex syl5 ) AEHZBEHZABIZJUDBEAKLHZMZDNHABOCHUDUEUFUHUEUFMZUGU
      DUGUEBAIZMUIBEAPUJUFUEBAQRSTUAABCDEFGUBUC $.
  $}


  $( Two words represent a walk if and only if their reverses also represent a
     walk.  (Contributed by BTernaryTau, 4-Dec-2023.) $)
  revwlkb $p |- ( ( F e. Word W /\ P e. Word U ) -> ( F ( Walks ` G ) P <->
    ( reverse ` F ) ( Walks ` G ) ( reverse ` P ) ) ) $=
    ( cword wcel wa cwlks cfv creverse revwlk revrev breqan12d imbitrid impbid2
    wbr ) CEFGZABFGZHZCADIJZQZCKJZAKJZUAQZACDLUEUCKJZUDKJZUAQTUBUDUCDLRSUFCUGAU
    AECMBAMNOP $.


  $( A non-trivial cycle in a simple graph has a length greater than 2.
     (Contributed by BTernaryTau, 24-Sep-2023.) $)
  usgrgt2cycl $p |- ( ( G e. USGraph /\ F ( Cycles ` G ) P /\ F =/= (/) ) ->
    2 < ( # ` F ) ) $=
    ( wcel cfv wbr c0 wne c2 clt c1 cc0 wa cn0 syl adantr cvv wb 3adant3 caddc
    cusgr ccycls w3a chash cr cwlks cycliswlk wlkcl nn0red cle relwlk brrelex1i
    nn0ge0d hasheq0 necon3bid bicomd 3syl biimpa ne0gt0d 3adant1 cumgr usgrumgr
    umgrn1cycl sylan 0nn0 nn0ltp1ne sylancr 0p1e1 breq1i neeq2i anbi2i 3ad2ant2
    co 3bitr3g mpbir2and usgrn2cycl df-2 1nn0 bitrid bitr4di ) CUADZBACUBEFZBGH
    ZUCZIBUDEZJFZKWEJFZWEIHZWDWGLWEJFZWEKHZWBWCWIWAWBWCMWEWBWEUEDWCWBWEWBBACUFE
    ZFZWENDZABCUGZABCUHZOZUIPWBLWEUJFZWCWBWLWQWNWLWEWOUMOPWBWCWELHZWBWLBQDZWCWR
    RWNBAWKCUKULWSWRWCWSWELBGBQUNUOUPUQURUSUTWAWBWJWCWACVADWBWJCVBABCVCVDSWBWAW
    GWIWJMZRWCWBLKTVMZWEJFZWIWEXAHZMZWGWTWBLNDWMXBXDRVEWPLWEVFVGXAKWEJVHVIXCWJW
    IXAKWEVHVJVKVNVLVOWAWBWHWCABCVPSWDWFWGWEKKTVMZHZMZWGWHMWBWAWFXGRWCWFXEWEJFZ
    WBXGIXEWEJVQVIWBKNDWMXHXGRVRWPKWEVFVGVSVLWHXFWGIXEWEVQVJVKVTVO $.

  ${
    usgrcyclgt2v.1 $e |- V = ( Vtx ` G ) $.
    $( A simple graph with a non-trivial cycle must have at least 3 vertices.
       (Contributed by BTernaryTau, 5-Oct-2023.) $)
    usgrcyclgt2v $p |- ( ( G e. USGraph /\ F ( Cycles ` G ) P /\ F =/= (/) ) ->
              2 < ( # ` V ) ) $=
      ( cusgr wcel ccycls cfv wbr c0 wne c2 chash cxr a1i cxnn0 xnn0xr 3ad2ant2
      cvv w3a 2re rexri cwlks cn0 cycliswlk wlkcl 4syl cvtx fvexi hashxnn0 mp2b
      nn0xnn0 usgrgt2cycl cle cpths cyclispth pthhashvtx syl xrltletrd ) CFGZBA
      CHIJZBKLZUAZMBNIZDNIZMOGVDMUBUCPVBVAVEOGZVCVBBACUDIJVEUEGVEQGVGABCUFABCUG
      VEUMVERUHSVFOGZVDDTGVFQGVHDCUIEUJDTUKVFRULPABCUNVBVAVEVFUOJZVCVBBACUPIJVI
      ABCUQABCDEURUSSUT $.
  $}


  ${
    $d V a b c $.  $d f G p a b c $.
    cusgr3cyclex.1 $e |- V = ( Vtx ` G ) $.
    $( Every complete simple graph with more than two vertices has a 3-cycle.
       (Contributed by BTernaryTau, 4-Oct-2023.) $)
    cusgr3cyclex $p |- ( ( G e. ComplUSGraph /\ 2 < ( # ` V ) ) ->
          E. f E. p ( f ( Cycles ` G ) p /\ ( # ` f ) = 3 ) ) $=
      ( va vb vc wcel cv wne w3a wrex cfv wa wex wi cpr df-3an cusgredgex2 wceq
      ccusgr ccycls wbr chash c3 c2 clt 3anass bianass cumgr cusgrusgr usgrumgr
      cedg cusgr syl 3simpc ancli biimpi an32 anbi1i anass sylbb anasss anandi3
      syl2an eqid biimtrrid anim12d syl5 3anan32 eleq1i 3anbi3i bitr3i imbitrdi
      an4 prcom pm5.3 sylib cc0 umgr3cyclex 3simpa 2eximi 3expib sylsyld sylbir
      expdimp reximdvva reximdva rexlimivw syl6 cvv cvtx fvexi hashgt23el impel
      id mpan ) BUBIZFJZGJZKZWTHJZKZXAXCKZLZHCMGCMZFCMZAJZDJZBUCNUDZXIUENUFUAZO
      ZDPAPZUGCUENUHUDZWSXHXNHCMZGCMZFCMXNWSXGXQFCWSWTCIZOZXFXNGHCCXSXACIZXCCIZ
      OZOWSXRXTYALZOXFXNQYCXRYBWSXRXTYAUIUJWSYCXFXNWSBUKIZYCXFOZYCWTXARBUNNZIZX
      AXCRYFIZXCWTRZYFIZLZOZXNWSBUOIYDBULBUMUPWSYEYKQYEYLQWSYEYGWTXCRZYFIZOZYHO
      ZYKYEYCXBXDOZOZYBXEOZOZWSYPYCYCYBOZYQXEOZYTXFYCYBXRXTYAUQURXFUUBXBXDXESUS
      UUAYQXEYTUUAYQOZXEOYRYBOZXEOYTUUCUUDXEYCYBYQUTVAYRYBXEVBVCVDVFWSYRYOYSYHY
      RXRXTOZXBOZXRYAOZXDOZOZWSYOYRUUEUUGOZYQOUUIYCUUJYQXRXTYAVEVAUUEUUGXBXDVPV
      CWSUUFYGUUHYNUUFXRXTXBLWSYGXRXTXBSWTXAYFBCEYFVGZTVHUUHXRYAXDLWSYNXRYAXDSW
      TXCYFBCEUUKTVHVIVJYSXTYAXELWSYHXTYAXESXAXCYFBCEUUKTVHVIVJYPYGYHYNLYKYGYHY
      NVKYNYJYGYHYMYIYFWTXCVQVLVMVNVOYCXFYKVRVSYDYCYKXNYDYCYKLXKXLVTXJNWTUAZLZD
      PAPXNWTXAXCAYFBCDEUUKWAUUMXMADXKXLUULWBWCUPWDWEWGWFWHWIXQXNFCXPXNGCXNXNHC
      XNWQWJWJWJWKCWLIXOXHCBWMEWNCWLFGHWOWRWP $.
  $}


  ${
    2cycl2d.1 $e |- P = <" A B A "> $.
    2cycl2d.2 $e |- F = <" J K "> $.
    2cycl2d.3 $e |- ( ph -> ( A e. V /\ B e. V ) ) $.
    2cycl2d.4 $e |- ( ph -> A =/= B ) $.
    2cycl2d.5 $e |- ( ph ->
          ( { A , B } C_ ( I ` J ) /\ { A , B } C_ ( I ` K ) ) ) $.
    2cycl2d.6 $e |- V = ( Vtx ` G ) $.
    2cycl2d.7 $e |- I = ( iEdg ` G ) $.
    2cycl2d.8 $e |- ( ph -> J =/= K ) $.
    $( Construction of a 2-cycle from two given edges in a graph.  (Contributed
       by BTernaryTau, 16-Oct-2023.) $)
    2cycl2d $p |- ( ph -> F ( Cycles ` G ) P ) $=
      ( wa wss wcel w3a simpl jccir df-3an sylibr wne necomd jca cpr cfv sseq1i
      prcom anbi2i sylib eqidd 2cycld ) ABCBDEFGHIJKLABJUAZCJUAZSZURSURUSURUBAU
      TURMURUSUCUDURUSURUEUFABCUGCBUGNABCNUHUIABCUJZHGUKTZVAIGUKZTZSVBCBUJZVCTZ
      SOVDVFVBVAVEVCBCUMULUNUOPQRABUPUQ $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Acyclic graphs
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d f g p $.  $d f G p $.  $d f V p $.
    acycgr0v.1 $e |- V = ( Vtx ` G ) $.
    $( A null graph (with no vertices) is an acyclic graph.  (Contributed by
       BTernaryTau, 11-Oct-2023.) $)
    acycgr0v $p |- ( ( G e. W /\ V = (/) ) -> G e. AcyclicGraph ) $=
      ( vf vp vg c0 wceq wcel cv ccycls cfv wbr wne wa wex wn df-br nexdv cwlks
      cacycgr br0 wss cpths cc0 chash cvv df-cycls relmptopab cycliswlk 3imtr3i
      wb cop relssi cvtx eqeq1i g0wlk0 sylbi sseqtrid breq notbid 3syl intnanrd
      ss0 mpbiri isacycgr biimpar sylan2 ) BHIZACJZEKZFKZALMZNZVLHOZPZFQZEQRZAU
      BJZVJVREVJVQFVJVOVPVJVORZVLVMHNZRZVLVMUCVJVNHUDVNHIZWAWCUMVJAUAMZVNHEFVNW
      EVLVMGKUEMNUFVMMVLUGMVMMIPGEFUHALEGFUIUJVOVLVMWENVLVMUNZVNJWFWEJVMVLAUKVL
      VMVNSVLVMWESULUOVJAUPMZHIWEHIBWGHDUQAURUSUTVNVEWDVOWBVLVMVNHVAVBVCVFVDTTV
      KVTVSEACFVGVHVI $.
  $}

  ${
    $d f G p $.  $d f V p $.
    acycgrv.1 $e |- V = ( Vtx ` G ) $.
    $( A multigraph with one vertex is an acyclic graph.  (Contributed by
       BTernaryTau, 12-Oct-2023.) $)
    acycgr1v $p |- ( ( G e. UMGraph /\ ( # ` V ) = 1 ) ->
              G e. AcyclicGraph ) $=
      ( vf vp cumgr wcel chash cfv c1 wceq wa cv wbr wal cle wne syl adantr wb
      cacycgr ccycls c0 wi w3a cc0 clt cpths cyclispth pthhashvtx breq2 3adant1
      adantl mpbid umgrn1cycl 3adant3 necomd cwlks cycliswlk nn0red 1red ltlend
      wlkcl 3ad2ant2 mpbir2and cn0 nn0lt10b cvv hasheq0 elv sylib 3com23 3expia
      3syl alrimivv isacycgr1 mpbird ) AFGZBHIZJKZLZAUAGZDMZEMZAUBINZWCUCKZUDZE
      ODOZWAWGDEVRVTWEWFVRWEVTWFVRWEVTUEZWCHIZUFKZWFWIWJJUGNZWKWIWLWJJPNZJWJQZW
      EVTWMVRWEVTLWJVSPNZWMWEWOVTWEWCWDAUHINWOWDWCAUIWDWCABCUJRSVTWOWMTWEVSJWJP
      UKUMUNULWIWJJVRWEWJJQVTWDWCAUOUPUQWEVRWLWMWNLTZVTWEWCWDAURINZWPWDWCAUSZWQ
      WJJWQWJWDWCAVCZUTWQVAVBRVDVEWEVRWLWKTZVTWEWQWJVFGWTWRWSWJVGVNVDUNWKWFTDWC
      VHVIVJVKVLVMVOVRWBWHTVTDAFEVPSVQ $.

    $( A simple graph with two vertices is an acyclic graph.  (Contributed by
       BTernaryTau, 12-Oct-2023.) $)
    acycgr2v $p |- ( ( G e. USGraph /\ ( # ` V ) = 2 ) ->
              G e. AcyclicGraph ) $=
      ( vf vp cusgr wcel chash cfv c2 wceq wa cv wbr wne wex wn cxr cvv nexdv
      cacycgr ccycls w3a clt usgrcyclgt2v 2re rexri fvexi hashxrcl ax-mp xrltne
      c0 cvtx mp3an12 neneqd syl 3expib con2d imp wb isacycgr adantr mpbird ) A
      FGZBHIZJKZLZAUAGZDMZEMZAUBINZVIULOZLZEPZDPQZVGVNDVGVMEVDVFVMQVDVMVFVDVKVL
      VFQZVDVKVLUCJVEUDNZVPVJVIABCUEVQVEJJRGVERGZVQVEJOJUFUGBSGVRBAUMCUHBSUIUJJ
      VEUKUNUOUPUQURUSTTVDVHVOUTVFDAFEVAVBVC $.
  $}

  ${
    $d f g p $.  $d f G p $.  $d f V p $.
    prclisacycgr.1 $e |- V = ( Vtx ` G ) $.
    $( A proper class (representing a null graph, see ~ vtxvalprc ) has the
       property of an acyclic graph (see also ~ acycgr0v ).  (Contributed by
       BTernaryTau, 11-Oct-2023.)  (New usage is discouraged.) $)
    prclisacycgr $p |- ( -. G e. _V ->
              -. E. f E. p ( f ( Cycles ` G ) p /\ f =/= (/) ) ) $=
      ( vg cvv wcel wn c0 wceq cv ccycls cfv wbr wa wex cvtx df-br nexdv eqtrid
      wne fvprc br0 wss cwlks cpths cc0 chash df-cycls relmptopab cop cycliswlk
      3imtr3i relssi eqeq1i g0wlk0 sylbi sseqtrid ss0 breq notbid 3syl intnanrd
      wb mpbiri syl ) BGHIZCJKZALZDLZBMNZOZVJJUBZPZDQZAQIVHCBRNZJEBRUCUAVIVPAVI
      VODVIVMVNVIVMIZVJVKJOZIZVJVKUDVIVLJUEVLJKZVRVTVEVIBUFNZVLJADVLWBVJVKFLUGN
      OUHVKNVJUINVKNKPFADGBMAFDUJUKVMVJVKWBOVJVKULZVLHWCWBHVKVJBUMVJVKVLSVJVKWB
      SUNUOVIVQJKWBJKCVQJEUPBUQURUSVLUTWAVMVSVJVKVLJVAVBVCVFVDTTVG $.
  $}

  ${
    $d x V $.  $d x G a $.  $d f G p a $.
    acycgrislfgr.1 $e |- V = ( Vtx ` G ) $.
    acycgrislfgr.2 $e |- I = ( iEdg ` G ) $.
    $( An acyclic hypergraph is a loop-free hypergraph.  (Contributed by
       BTernaryTau, 15-Oct-2023.) $)
    acycgrislfgr $p |- ( ( G e. AcyclicGraph /\ G e. UHGraph ) ->
              I : dom I --> { x e. ~P V | 2 <_ ( # ` x ) } ) $=
      ( va vf vp wcel cuhgr wa cv chash cfv wbr wex wn wceq 2eximi cacycgr crab
      cdm c2 cle cpw wf csn cedg ccycls c0 wne isacycgr biimpac wi c1 loop1cycl
      cc0 w3a 3simpa biimtrrdi exlimdv cvv vex hash1n0 mpan anim2i con3d adantl
      syl6 mpd wb lfuhgr3 mpbird ) BUAJZBKJZLZCUCUDAMNOUEPADUFUBCUGZGMZUHBUIOJZ
      GQZRZVQHMZIMZBUJOPZWCUKULZLZIQHQZRZWBVPVOWIHBKIUMUNVPWIWBUOVOVPWAWHVPWAWE
      WCNOUPSZLZIQHQZWHVPVTWLGVPVTWEWJURWDOVSSZUSZIQHQWLVSHBIUQWNWKHIWEWJWMUTTV
      AVBWKWGHIWJWFWEWCVCJWJWFHVDWCVCVEVFVGTVJVHVIVKVPVRWBVLVOABCDGEFVMVIVN $.
  $}

  ${
    $d x G $.
    $( An acyclic pseudograph is a multigraph.  (Contributed by BTernaryTau,
       15-Oct-2023.) $)
    upgracycumgr $p |- ( ( G e. UPGraph /\ G e. AcyclicGraph ) ->
              G e. UMGraph ) $=
      ( vx cupgr wcel cacycgr ciedg cfv cdm c2 cv chash cle wbr cvtx crab cumgr
      cpw wf wa eqid cuhgr anim1ci acycgrislfgr syl umgrislfupgr biimpri syldan
      upgruhgr ) ACDZAEDZAFGZHIBJKGLMBANGZQOUKRZAPDZUIUJSUJAUADZSUMUIUOUJAUHUBB
      AUKULULTZUKTZUCUDUNUIUMSBAUKULUPUQUEUFUG $.
  $}

  ${
    $d x G $.  $d f j k G p $.
    $( An acyclic multigraph is a simple graph.  (Contributed by BTernaryTau,
       17-Oct-2023.) $)
    umgracycusgr $p |- ( ( G e. UMGraph /\ G e. AcyclicGraph ) ->
              G e. USGraph ) $=
      ( vx vj vk vf vp cumgr wcel wa cfv cv chash c2 wceq wne wrex wn wex cc0
      c0 cacycgr ciedg cdm cvtx cpw crab wf1 cusgr wf umgrf ccycls wbr isacycgr
      eqid biimpa wi umgr2cycl 2ne0 neeq1 mpbiri wb cvv hasheq0 necon3bii sylib
      elv anim2i 2eximi syl con3d adantr dff15 biimpri syl2an2r isusgrs biimprd
      ex mpd ) AGHZAUAHZIZAUBJZUCZBKLJMNBAUDJZUEUFZWBUGZAUHHZVSWCWEWBUIZVTCKZWB
      JDKZWBJNWIWJOIDWCPCWCPZQZWFBWBAWDWDUNZWBUNZUJWAEKZFKAUKJULZWOTOZIZFRERZQZ
      WLVSVTWTEAGFUMUOVSWTWLUPVTVSWKWSVSWKWSVSWKIWPWOLJZMNZIZFRERWSECDAWBFWNUQX
      CWREFXBWQWPXBXASOZWQXBXDMSOURXAMSUSUTXASWOTXASNWOTNVAEWOVBVCVFVDVEVGVHVIV
      QVJVKVRWFWHWLICDWCWEWBVLVMVNVSWFWGUPVTVSWGWFBGWBAWDWMWNVOVPVKVR $.
  $}

  $( An acyclic pseudograph is a simple graph.  (Contributed by BTernaryTau,
     17-Oct-2023.) $)
  upgracycusgr $p |- ( ( G e. UPGraph /\ G e. AcyclicGraph ) ->
            G e. USGraph ) $=
    ( cupgr wcel cacycgr cumgr cusgr upgracycumgr umgracycusgr sylancom ) ABCAD
    CAECAFCAGAHI $.

  ${
    $d f G p $.  $d f V p $.
    cusgracyclt3v.1 $e |- V = ( Vtx ` G ) $.
    $( A complete simple graph is acyclic if and only if it has fewer than
       three vertices.  (Contributed by BTernaryTau, 20-Oct-2023.) $)
    cusgracyclt3v $p |- ( G e. ComplUSGraph ->
              ( G e. AcyclicGraph <-> ( # ` V ) < 3 ) ) $=
      ( vf vp ccusgr wcel chash cfv c3 clt wbr c0 wne wa wex wb cvv wceq cc0 cv
      cacycgr ccycls wn isacycgr c2 cle c1 cmin co cn0 cxnn0 3nn0 cvtx hashxnn0
      fvexi ax-mp xnn0lem1lt mp2an cxr rexri xnn0xr xrlenlt breq1i cusgr3cyclex
      3re 3m1e2 3bitr3i 3ne0 neeq1 mpbiri hasheq0 necon3bii sylib anim2i 2eximi
      ex biimtrid con1d sylbid cusgr wi cusgrusgr usgrcyclgt2v 3expib imbitrrdi
      elv syl exlimdvv con2d sylibrd impbid ) AFGZAUBGZBHIZJKLZWMWNDUAZEUAZAUCI
      LZWQMNZOZEPDPZUDZWPDAFEUEZWMWPXBWPUDZUFWOKLZWMXBJWOUGLZJUHUIUJZWOKLZXEXFJ
      UKGWOULGZXGXIQUMBRGXJBAUNCUPBRUOUQZJWOURUSJUTGWOUTGZXGXEQJVFVAXJXLXKWOVBU
      QJWOVCUSXHUFWOKVGVDVHZWMXFXBWMXFOWSWQHIZJSZOZEPDPXBDABECVEXPXADEXOWTWSXOX
      NTNZWTXOXQJTNVIXNJTVJVKXNTWQMXNTSWQMSQDWQRVLWGVMVNVOVPWHVQVRVSVTWMWPXCWNW
      MXBWPWMXAXEDEWMXAXFXEWMAWAGZXAXFWBAWCXRWSWTXFWRWQABCWDWEWHXMWFWIWJXDWKWL
      $.
  $}

  $( A path in an acyclic graph is a simple path.  (Contributed by BTernaryTau,
     21-Oct-2023.) $)
  pthacycspth $p |- ( ( G e. AcyclicGraph /\ F ( Paths ` G ) P ) ->
            F ( SPaths ` G ) P ) $=
    ( cacycgr wcel cpths cfv wbr wa cspths wo ccycls wi c0 cyclispth acycgrcycl
    wceq a1i ex adantr jcad spthcycl simplbi pthisspthorcycl adantl orim2 pm1.2
    syl6 sylc syl ) CDEZBACFGHZIZBACJGHZUNKZUNUMBACLGHZUNMUNUPKZUOUMUPULBNQZIZU
    NUMUPULURUPULMUMABCORUKUPURMULUKUPURABCPSTUAUSUNUPABCUBUCUHULUQUKABCUDUEUNU
    PUNUFUIUNUGUJ $.

  ${
    $d S f p $.  $d f G p $.
    $( The subgraph of an acyclic graph is also acyclic.  (Contributed by
       BTernaryTau, 23-Oct-2023.) $)
    acycgrsubgr $p |- ( ( G e. AcyclicGraph /\ S SubGraph G ) ->
              S e. AcyclicGraph ) $=
      ( vf vp csubgr wbr cacycgr wcel cv ccycls cfv c0 wne wa wex subgrcycl cvv
      wn wb isacycgr anim1d 2eximdv con3d subgrv simpl2im simpld 3imtr4d impcom
      syl ) ABEFZBGHZAGHZUJCIZDIZBJKFZUMLMZNZDOCOZRZUMUNAJKFZUPNZDOCOZRZUKULUJV
      BURUJVAUQCDUJUTUOUPUNAUMBPUAUBUCUJAQHZBQHZUKUSSABUDZCBQDTUEUJVDULVCSUJVDV
      EVFUFCAQDTUIUGUH $.
  $}

$( (End of BTernaryTau's mathbox.) $)
