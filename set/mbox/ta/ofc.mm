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
      ( vf vc vx wceq cvv cv cdm co cmpt cmpt2 cofc wcel oveq mpteq2dv 3ad2ant1
      cfv mpt2eq3dva df-ofc 3eqtr4g ) ABFZCDGGECHZIZEHUCRZDHZAJZKZLCDGGEUDUEUFB
      JZKZLAMBMUBCDGGUHUJUBUCGNUHUJFUFGNUBEUDUGUIUEUFABOPQSEACDTEBCDTUA $.
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
        ( vf vc co cvv wceq wa wcel cofc cdm cv cfv cmpt cmpt2 df-ofc a1i dmeqd
        simprl fveq1d simprr oveq12d mpteq12dv wfn fnex syl2anc elex syl mptexg
        fndm eqeltrd ovmpt2d eleq2d pm5.32i sylbi oveq1d mpteq12dva eqtrd ) AGE
        FUAZPBGUBZBUCZGUDZEFPZUEZBCDEFPZUEANOGEQQBNUCZUBZVLVQUDZOUCZFPZUEZVOVJQ
        VJNOQQWBUFRABFNOUGUHAVQGRZVTERZSSZBVRWAVKVNWEVQGAWCWDUJZUIWEVSVMVTEFWEV
        LVQGWFUKAWCWDULUMUNAGCUOZCHTGQTJKCHGUPUQAEITEQTLEIURUSAVKHTVOQTAVKCHAWG
        VKCRJCGVAUSZKVBBVKVNHUTUSVCABVKVNCVPWHAVLVKTZSZVMDEFWJAVLCTZSVMDRAWIWKA
        VKCVLWHVDVEMVFVGVHVI $.
    $}

    $d x A $.
    ${
      $d x X $.
      ofcval.6 $e |- ( ( ph /\ X e. A ) -> ( F ` X ) = B ) $.
      $( Evaluate a function/constant operation at a point.  (Contributed by
         Thierry Arnoux, 31-Jan-2017.) $)
      ofcval $p |- ( ( ph /\ X e. A ) -> ( ( F oFC R C ) ` X ) = ( B R C ) ) $=
        ( vx wcel wa co cfv cvv wceq cofc cv eqidd ofcfval adantr fveq2d oveq1d
        cmpt simpr ovex a1i fvmptd eqtrd ) AIBOZPZIFDEUAQZRIFRZDEQZCDEQUONINUBZ
        FRZDEQZURBUPSAUPNBVAUHTUNANBUTDEFGHJKLAUSBOPUTUCUDUEUOUSITZPZUTUQDEVCUS
        IFUOVBUIUFUGAUNUIURSOUOUQDEUJUKULUOUQCDEMUGUM $.
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
      ( cv co cmpt wceq cofc wcel wa wral ralrimiva adantr oveq1 eqeq12d rspcva
      cfv syl2anc mpteq2dva eqidd ofcfval 3eqtr4d ) ABDBQZIUJZFHRZSBDUQFGRZSIFH
      UARIFGUARABDURUSAUPDUBZUCZUQEUBCQZFHRZVBFGRZTZCEUDZURUSTZLAVFUTAVECEMUEUF
      VEVGCUQEVBUQTVCURVDUSVBUQFHUGVBUQFGUGUHUIUKULABDUQFHIJKNOPVAUQUMZUNABDUQF
      GIJKNOPVHUNUO $.
  $}

  ${
    $d c f x C $.  $d c f x F $.  $d c f x R $.
    $( General value of ` ( F oFC R C ) ` with no assumptions on functionality
       of ` F ` .  (Contributed by Thierry Arnoux, 31-Jan-2017.) $)
    ofcfval3 $p |- ( ( F e. V /\ C e. W ) -> ( F oFC R C ) =
        ( x e. dom F |-> ( ( F ` x ) R C ) ) ) $=
      ( vf vc wcel wa cvv cdm cv cfv co cmpt cofc wceq elex adantr adantl dmexg
      mptexg simpl dmeqd fveq1d simpr oveq12d mpteq12dv df-ofc ovmpt2ga syl3anc
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
      ( vz cv co wcel wral cfv wf wfn ffn syl wa eqidd ofcfval ffvelrnda adantr
      cofc ralrimivva proplem2 syl21anc fmpt3d ) APDPQZJUAZEFRZIJEFUKRAPDUQEFJK
      HADGJUBJDUCMDGJUDUENOAUPDSZUFZUQUGUHUTUQGSEHSZBQCQFRISZCHTBGTZURISADGUPJM
      UIAVAUSOUJAVCUSAVBBCGHLULUJBCGHIFUQEUMUNUO $.
  $}

  ${
    $d x A $.  $d x C $.  $d x F $.  $d x R $.  $d x ph $.
    ofcfval2.1 $e |- ( ph -> A e. V ) $.
    ofcfval2.2 $e |- ( ph -> C e. W ) $.
    ofcfval2.3 $e |- ( ( ph /\ x e. A ) -> B e. W ) $.
    ofcfval2.4 $e |- ( ph -> F = ( x e. A |-> B ) ) $.
    $( The function operation expressed as a mapping.  (Contributed by Thierry
       Arnoux, 31-Jan-2017.) $)
    ofcfval2 $p |- ( ph -> ( F oFC R C ) = ( x e. A |-> ( B R C ) ) ) $=
      ( wfn cmpt wcel wral ralrimiva eqid fnmpt fneq1d mpbird fvmpt2d ofcfval
      syl ) ABCDEFGHIAGCNBCDOZCNZADIPZBCQUGAUHBCLRBCDUFIUFSTUEACGUFMUAUBJKABCDG
      IMLUCUD $.
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
      ( vy cv co cmpt wceq cvv wcel syl2anc cdm cfv cofc wf fdm syl mpteq1d fex
      ccom ofcfval3 ffvelrnda feqmptd eqidd oveq1 fmptco 3eqtr4d ) AMGUAZMNZGUB
      ZEFOZPZMCUTPGEFUCOZBDBNZEFOZPZGUIAMUQCUTACDGUDZUQCQJCDGUEUFUGAGRSZEISVBVA
      QAVFCHSVGJKCDHGUHTLMEFGRIUJTAMBCDUSVDUTGVEACDURGJUKAMCDGJULAVEUMVCUSEFUNU
      OUP $.
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
      cfv sylan fconstmpt syl6eqr ) ABCMNZDEOPLBCDEPZQBUKMNALBCDEUJFHACGRZUJBSJ
      BCGTUAIKAULLUBZBRUMUJUFCUCJBCUMGUDUGUELBUKUHUI $.
  $}

