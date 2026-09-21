$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Mixed Function/Constant operation
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c oFC $.  $( A small o with F/C subscript $)

  $( Extend class notation to include mapping of an operation to an operation
     for a function and a constant. $)
  cofc $a class oFC R $.

  ${
    $d f c x R $.
    $( Define the function/constant operation map.  The definition is designed
       so that if ` R ` is a binary operation, then ` oFC R ` is the analogous
       operation on functions and constants.  (Contributed by Thierry Arnoux,
       21-Jan-2017.) $)
    df-ofc $a |- oFC R = ( f e. _V , c e. _V |->
      ( x e. dom f |-> ( ( f ` x ) R c ) ) ) $.
  $}

  ${
    $d c f x R $.  $d c f x S $.
    $( Equality theorem for function/constant operation.  (Contributed by
       Thierry Arnoux, 30-Jan-2017.) $)
    ofceq $p |- ( R = S -> oFC R = oFC S ) $=
      ( vf vc vx wceq cvv cv cdm cfv co cmpt cmpo cofc mpteq2dv mpoeq3dv df-ofc
      oveq 3eqtr4g ) ABFZCDGGECHZIZEHUAJZDHZAKZLZMCDGGEUBUCUDBKZLZMANBNTCDGGUFU
      HTEUBUEUGUCUDABROPEACDQEBCDQS $.
  $}

  ${
    $d c f x C $.  $d c f x F $.  $d c f x R $.  $d c f x ph $.
    ofcfval.1 $e |- ( ph -> F Fn A ) $.
    ofcfval.2 $e |- ( ph -> A e. V ) $.
    ofcfval.3 $e |- ( ph -> C e. W ) $.
    ${
      ofcfval.6 $e |- ( ( ph /\ x e. A ) -> ( F ` x ) = B ) $.
      $( Value of an operation applied to a function and a constant.
         (Contributed by Thierry Arnoux, 30-Jan-2017.) $)
      ofcfval $p |- ( ph -> ( F oFC R C ) = ( x e. A |-> ( B R C ) ) ) $=
        ( vf vc co cvv wceq wa wcel cofc cdm cv cfv cmpt cmpo df-ofc a1i simprl
        dmeqd fveq1d simprr oveq12d mpteq12dv fnex syl2anc elexd eqeltrd mptexd
        wfn fndmd ovmpod eleq2d pm5.32i sylbi oveq1d mpteq12dva eqtrd ) AGEFUAZ
        PBGUBZBUCZGUDZEFPZUEZBCDEFPZUEANOGEQQBNUCZUBZVKVPUDZOUCZFPZUEZVNVIQVINO
        QQWAUFRABFNOUGUHAVPGRZVSERZSSZBVQVTVJVMWDVPGAWBWCUIZUJWDVRVLVSEFWDVKVPG
        WEUKAWBWCULUMUNAGCUTCHTGQTJKCHGUOUPAEILUQABVJVMHAVJCHACGJVAZKURUSVBABVJ
        VMCVOWFAVKVJTZSZVLDEFWHAVKCTZSVLDRAWGWIAVJCVKWFVCVDMVEVFVGVH $.
    $}

    $d x A $.
    ${
      $d x X $.
      ofcval.6 $e |- ( ( ph /\ X e. A ) -> ( F ` X ) = B ) $.
      $( Evaluate a function/constant operation at a point.  (Contributed by
         Thierry Arnoux, 31-Jan-2017.) $)
      ofcval $p |- ( ( ph /\ X e. A ) -> ( ( F oFC R C ) ` X ) = ( B R C ) ) $=
        ( vx wcel wa co cfv wceq simpr cofc cv cmpt eqidd ofcfval adantr fveq2d
        cvv oveq1d ovexd fvmptd eqtrd ) AIBOZPZIFDEUAQZRIFRZDEQZCDEQUNNINUBZFRZ
        DEQZUQBUOUHAUONBUTUCSUMANBUSDEFGHJKLAURBOPUSUDUEUFUNURISZPZUSUPDEVBURIF
        UNVATUGUIAUMTUNUPDEUJUKUNUPCDEMUIUL $.
    $}

    $( The function operation produces a function.  (Contributed by Thierry
       Arnoux, 31-Jan-2017.) $)
    ofcfn $p |- ( ph -> ( F oFC R C ) Fn A ) $=
      ( vx cofc co wfn cv cfv cmpt ovex eqid fnmpti wcel wa eqidd fneq1d mpbiri
      ofcfval ) AECDLMZBNKBKOZEPZCDMZQZBNKBUJUKUICDRUKSTABUGUKAKBUICDEFGHIJAUHB
      UAUBUIUCUFUDUE $.
  $}

  ${
    $d x y C $.  $d x y F $.  $d x y P $.  $d x y R $.  $d x y ph $.  $d y B $.
    ofcfeqd2.1 $e |- ( ( ph /\ x e. A ) -> ( F ` x ) e. B ) $.
    ofcfeqd2.2 $e |- ( ( ph /\ y e. B ) -> ( y R C ) = ( y P C ) ) $.
    ofcfeqd2.3 $e |- ( ph -> F Fn A ) $.
    ofcfeqd2.4 $e |- ( ph -> A e. V ) $.
    ofcfeqd2.5 $e |- ( ph -> C e. W ) $.
    $( Equality theorem for function/constant operation value.  (Contributed by
       Thierry Arnoux, 31-Jan-2017.) $)
    ofcfeqd2 $p |- ( ph -> ( F oFC R C ) = ( F oFC P C ) ) $=
      ( cv co cmpt wceq cfv cofc wcel wa oveq1 eqeq12d ralrimiva adantr rspcdva
      wral mpteq2dva eqidd ofcfval 3eqtr4d ) ABDBQZIUAZFHRZSBDUPFGRZSIFHUBRIFGU
      BRABDUQURAUODUCZUDZCQZFHRZVAFGRZTZUQURTCEUPVAUPTVBUQVCURVAUPFHUEVAUPFGUEU
      FAVDCEUJUSAVDCEMUGUHLUIUKABDUPFHIJKNOPUTUPULZUMABDUPFGIJKNOPVEUMUN $.
  $}

  ${
    $d c f x C $.  $d c f x F $.  $d c f x R $.
    $( General value of ` ( F oFC R C ) ` with no assumptions on functionality
       of ` F ` .  (Contributed by Thierry Arnoux, 31-Jan-2017.) $)
    ofcfval3 $p |- ( ( F e. V /\ C e. W ) -> ( F oFC R C ) =
        ( x e. dom F |-> ( ( F ` x ) R C ) ) ) $=
      ( vf vc wcel wa cvv cdm cv cfv co cmpt cofc wceq elex adantr adantl dmexg
      mptexg simpl dmeqd fveq1d simpr oveq12d mpteq12dv df-ofc ovmpoga syl3anc
      syl ) DEIZBFIZJDKIZBKIZADLZAMZDNZBCOZPZKIZDBCQZOVBRUNUPUODESTUOUQUNBFSUAU
      NVCUOUNURKIVCDEUBAURVAKUCUMTGHDBKKAGMZLZUSVENZHMZCOZPVBVDKVEDRZVHBRZJZAVF
      VIURVAVLVEDVJVKUDZUEVLVGUTVHBCVLUSVEDVMUFVJVKUGUHUIACGHUJUKUL $.
  $}

  ${
    $d z A $.  $d y z C $.  $d x y z F $.  $d x y z R $.  $d x y S $.
    $d x y T $.  $d x y z U $.  $d x y z ph $.
    ofcf.1 $e |- ( ( ph /\ ( x e. S /\ y e. T ) ) -> ( x R y ) e. U ) $.
    ofcf.2 $e |- ( ph -> F : A --> S ) $.
    ofcf.4 $e |- ( ph -> A e. V ) $.
    ofcf.5 $e |- ( ph -> C e. T ) $.
    $( The function/constant operation produces a function.  (Contributed by
       Thierry Arnoux, 30-Jan-2017.) $)
    ofcf $p |- ( ph -> ( F oFC R C ) : A --> U ) $=
      ( vz cv co wcel wral cfv cofc ffnd wa eqidd ofcfval ffvelcdmda ralrimivva
      adantr ovrspc2v syl21anc fmpt3d ) APDPQZJUAZEFRZIJEFUBRAPDUNEFJKHADGJMUCN
      OAUMDSZUDZUNUEUFUQUNGSEHSZBQCQFRISZCHTBGTZUOISADGUMJMUGAURUPOUIAUTUPAUSBC
      GHLUHUIBCGHIFUNEUJUKUL $.
  $}

  ${
    $d x A $.  $d x C $.  $d x F $.  $d x R $.  $d x ph $.
    ofcfval2.1 $e |- ( ph -> A e. V ) $.
    ofcfval2.2 $e |- ( ph -> C e. W ) $.
    ofcfval2.3 $e |- ( ( ph /\ x e. A ) -> B e. X ) $.
    ofcfval2.4 $e |- ( ph -> F = ( x e. A |-> B ) ) $.
    $( The function operation expressed as a mapping.  (Contributed by Thierry
       Arnoux, 31-Jan-2017.) $)
    ofcfval2 $p |- ( ph -> ( F oFC R C ) = ( x e. A |-> ( B R C ) ) ) $=
      ( wfn cmpt wcel wral ralrimiva eqid fnmpt fneq1d mpbird fvmpt2d ofcfval
      syl ) ABCDEFGHIAGCOBCDPZCOZADJQZBCRUHAUIBCMSBCDUGJUGTUAUFACGUGNUBUCKLABCD
      GJNMUDUE $.
  $}

  ${
    $d y A $.  $d x y B $.  $d x y C $.  $d x y F $.  $d x y R $.  $d y ph $.
    ofcfval4.1 $e |- ( ph -> F : A --> B ) $.
    ofcfval4.2 $e |- ( ph -> A e. V ) $.
    ofcfval4.3 $e |- ( ph -> C e. W ) $.
    $( The function/constant operation expressed as an operation composition.
       (Contributed by Thierry Arnoux, 31-Jan-2017.) $)
    ofcfval4 $p |- ( ph ->
                         ( F oFC R C ) = ( ( x e. B |-> ( x R C ) ) o. F ) ) $=
      ( vy cdm cv cfv co cmpt cvv wcel cofc ccom fdmd mpteq1d wceq fexd syl2anc
      ofcfval3 ffvelcdmda feqmptd eqidd oveq1 fmptco 3eqtr4d ) AMGNZMOZGPZEFQZR
      ZMCURRGEFUAQZBDBOZEFQZRZGUBAMUOCURACDGJUCUDAGSTEITUTUSUEACDHGJKUFLMEFGSIU
      HUGAMBCDUQVBURGVCACDUPGJUIAMCDGJUJAVCUKVAUQEFULUMUN $.
  $}

  ${
    $d x A $.  $d x B $.  $d x C $.  $d x R $.  $d x ph $.
    ofcc.1 $e |- ( ph -> A e. V ) $.
    ofcc.2 $e |- ( ph -> B e. W ) $.
    ofcc.3 $e |- ( ph -> C e. X ) $.
    $( Left operation by a constant on a mixed operation with a constant.
       (Contributed by Thierry Arnoux, 31-Jan-2017.) $)
    ofcc $p |- ( ph -> ( ( A X. { B } ) oFC R C ) = ( A X. { ( B R C ) } ) ) $=
      ( vx csn cxp cofc co cmpt wcel wfn fnconstg syl cv wceq fvconst2g ofcfval
      cfv sylan fconstmpt eqtr4di ) ABCMNZDEOPLBCDEPZQBUKMNALBCDEUJFHACGRZUJBSJ
      BCGTUAIKAULLUBZBRUMUJUFCUCJBCUMGUDUGUELBUKUHUI $.
  $}

  ${
    $d x A $.  $d x C $.  $d x F $.  $d x R $.  $d x ph $.
    ofcof.1 $e |- ( ph -> F : A --> B ) $.
    ofcof.2 $e |- ( ph -> A e. V ) $.
    ofcof.3 $e |- ( ph -> C e. W ) $.
    $( Relate function operation with operation with a constant.  (Contributed
       by Thierry Arnoux, 3-Oct-2018.) $)
    ofcof $p |- ( ph -> ( F oFC R C ) = ( F oF R ( A X. { C } ) ) ) $=
      ( vx cofc co cv cfv cmpt csn cxp wcel cof ffnd eqidd ofcfval wfn fnconstg
      wa syl inidm wceq fvconst2g sylan offval eqtr4d ) AFDEMNLBLOZFPZDENQFBDRS
      ZEUANALBUPDEFGHABCFIUBZJKAUOBTZUGUPUCZUDALBBUPDEBFUQGGURADHTZUQBUEKBDHUFU
      HJJBUIUTAVAUSUOUQPDUJKBDUOHUKULUMUN $.
  $}

