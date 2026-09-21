$[ set-main.mm $]
$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Mathbox for David A. Wheeler
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#

  This is the mathbox of David A. Wheeler, _dwheeler at dwheeler dot com_ .
  Among other things, I have added a number of formal definitions for
  widely-used functions, e.g., those defined in
  ISO 80000-2:2009(E)
  _Quantities and units - Part 2: Mathematical signs and
  symbols used in the natural sciences and technology_
  and the
  _NIST Digital Library of Mathematical Functions_ ~ http://dlmf.nist.gov/ .

$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Simplify propositional expressions
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  These make it easier to manipulate some propositional expressions

$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Natural deduction
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    sbidd.1 $e |- ( ph -> [ x / x ] ps ) $.
    $( An identity theorem for substitution.  See ~ sbid .  See Remark 9.1 in
       [Megill] p. 447 (p. 15 of the preprint).  (Contributed by DAW,
       18-Feb-2017.) $)
    sbidd $p |- ( ph -> ps ) $=
      ( wsb sbid sylib ) ABCCEBDBCFG $.
  $}

  $( An identity theorem for substitution.  See ~ sbid .  See Remark 9.1 in
     [Megill] p. 447 (p. 15 of the preprint).  (Contributed by DAW,
     18-Feb-2017.) $)
  sbidd-misc $p |- ( ( ph -> [ x / x ] ps ) <-> ( ph -> ps ) ) $=
    ( wsb sbid imbi2i ) BCCDBABCEF $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Greater than, greater than or equal to
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  As a stylistic issue, set.mm prefers 'less than' instead of
  'greater than' to reduce the number of conversion steps.
  Here we formally define the widely-used relations
  'greater than' and 'greater than or equal to', so that we
  have formal definitions of them, as well as a few related theorems.

$)

  $( Define the 'greater than or equal to' predicate over the extended
     reals. $)

  $c >_ $. $( 'Greater than or equal to' relation (over extended reals). $)
  $c > $. $( 'Greater than' relation (over extended reals) $)

  $( Extend wff notation to include the 'greater than or equal to' relation,
     see ~ df-gte . $)
  cge-real $a class >_ $.
  $( Extend wff notation to include the 'greater than' relation, see
     ~ df-gt . $)
  cgt $a class > $.

  $( Define the 'greater than or equal' predicate over the reals.  Defined in
     ISO 80000-2:2009(E) operation 2-7.10.  It is used as a primitive in the
     "NIST Digital Library of Mathematical Functions" , front introduction,
     "Common Notations and Definitions" section at
     ~ http://dlmf.nist.gov/front/introduction#Sx4 .  This relation is merely
     the converse of the 'less than or equal to' relation defined by ~ df-le .

     We do not write this as ` ( x >_ y <-> y <_ x ) ` , and similarly we do
     not write `` > `` as ` ( x > y <-> y < x ) ` , because these are not
     definitional axioms as understood by mmj2 (those definitions will be
     flagged as being "potentially non-conservative").  We could write them
     this way:
     ` |- > = { <. x , y >. | ( ( x e. RR* /\ y e. RR* ) /\ y < x ) } ` and
     ` |- >_ = { <. x , y >. | ( ( x e. RR* /\ y e. RR* ) /\ y <_ x ) } ` but
     these are very complicated.  This definition of ` >_ ` , and the similar
     one for ` > ` ( ~ df-gt ), are a bit strange when you see them for the
     first time, but these definitions are much simpler for us to process and
     are clearly conservative definitions.  (My thanks to Mario Carneiro for
     pointing out this simpler approach.)  See ~ gte-lte for a more
     conventional expression of the relationship between ` < ` and ` > ` .  As
     a stylistic issue, set.mm prefers 'less than' instead of 'greater than' to
     reduce the number of conversion steps.  Thus, we discourage its use, but
     include its definition so that there _is_ a formal definition of this
     symbol.

     (Contributed by David A. Wheeler, 10-May-2015.)
     (New usage is discouraged.) $)
  df-gte $a |- >_ = `' <_ $.

  $( The 'greater than' relation is merely the converse of the 'less than or
     equal to' relation defined by ~ df-lt .  Defined in ISO 80000-2:2009(E)
     operation 2-7.12.  See ~ df-gte for a discussion on why this approach is
     used for the definition.  See ~ gt-lt and ~ gt-lth for more conventional
     expression of the relationship between ` < ` and ` > ` .

     As a stylistic issue, set.mm prefers 'less than or equal' instead of
     'greater than or equal' to reduce the number of conversion steps.  Thus,
     we discourage its use, but include its definition so that there _is_ a
     formal definition of this symbol.

     (Contributed by David A. Wheeler, 19-Apr-2015.)
     (New usage is discouraged.) $)
  df-gt $a |- > = `' < $.

  $( Simple relationship between ` <_ ` and ` >_ ` .  (Contributed by David A.
     Wheeler, 10-May-2015.)  (New usage is discouraged.) $)
  gte-lte $p |- ( ( A e. _V /\ B e. _V ) -> ( A >_ B <-> B <_ A ) ) $=
    ( cge-real wbr cle ccnv cvv wcel wa df-gte breqi brcnvg bitrid ) ABCDABEFZD
    AGHBGHIBAEDABCNJKABGGELM $.

  $( Simple relationship between ` < ` and ` > ` .  (Contributed by David A.
     Wheeler, 19-Apr-2015.)  (New usage is discouraged.) $)
  gt-lt $p |- ( ( A e. _V /\ B e. _V ) -> ( A > B <-> B < A ) ) $=
    ( cgt wbr clt ccnv cvv wcel wa df-gt breqi brcnvg bitrid ) ABCDABEFZDAGHBGH
    IBAEDABCNJKABGGELM $.

  ${
    gte-lteh.1 $e |- A e. _V $.
    gte-lteh.2 $e |- B e. _V $.
    $( Relationship between ` <_ ` and ` >_ ` using hypotheses.  (Contributed
       by David A. Wheeler, 10-May-2015.)  (New usage is discouraged.) $)
    gte-lteh $p |- ( A >_ B <-> B <_ A ) $=
      ( cge-real wbr cle ccnv df-gte breqi brcnv bitri ) ABEFABGHZFBAGFABEMIJAB
      GCDKL $.
  $}

  ${
    gt-lth.1 $e |- A e. _V $.
    gt-lth.2 $e |- B e. _V $.
    $( Relationship between ` < ` and ` > ` using hypotheses.  (Contributed by
       David A. Wheeler, 19-Apr-2015.)  (New usage is discouraged.) $)
    gt-lth $p |- ( A > B <-> B < A ) $=
      ( cgt wbr clt ccnv df-gt breqi brcnv bitri ) ABEFABGHZFBAGFABEMIJABGCDKL
      $.
  $}
  $( Simple example of ` > ` , in this case, 0 is not greater than 0.  This is
     useful as an example, and helps us gain confidence that we've correctly
     defined the symbol.  (Contributed by David A. Wheeler, 1-Jan-2017.)
     (New usage is discouraged.) $)
  ex-gt $p |- -. 0 > 0 $=
    ( cc0 cgt wbr clt 0re ltnri c0ex gt-lth mtbir ) AABCAADCAEFAAGGHI $.

  $( Simple example of ` >_ ` , in this case, 0 is greater than or equal to 0.
     This is useful as an example, and helps us gain confidence that we've
     correctly defined the symbol.  (Contributed by David A. Wheeler,
     1-Jan-2017.)  (New usage is discouraged.) $)
  ex-gte $p |- 0 >_ 0 $=
    ( cc0 cge-real wbr cle 0le0 c0ex gte-lteh mpbir ) AABCAADCEAAFFGH $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Hyperbolic trigonometric functions
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  It is a convention of set.mm to not use sinh and so on directly,
  and instead of use expansions such as ` ( cos `` ( _i x. x ) ) ` .
  However, I believe it's important to give formal definitions for
  these conventional functions as they are typically used,
  so here they are.  A few related identities are also proved.

$)

  $c sinh $. $( Hyperbolic sine function. $)
  $c cosh $. $( Hyperbolic cosine function. $)
  $c tanh $. $( Hyperbolic tangent function. $)

  $( Extend class notation to include the hyperbolic sine function, see
     ~ df-sinh . $)
  csinh $a class sinh $.
  $( Extend class notation to include the hyperbolic cosine function. see
     ~ df-cosh . $)
  ccosh $a class cosh $.
  $( Extend class notation to include the hyperbolic tangent function, see
     ~ df-tanh . $)
  ctanh $a class tanh $.

  $( Define the hyperbolic sine function (sinh).  We define it this way for
     ~ cmpt , which requires the form ` ( x e. A |-> B ) ` .  See
     ~ sinhval-named for a simple way to evaluate it.  We define this function
     by dividing by ` _i ` , which uses fewer operations than many conventional
     definitions (and thus is more convenient to use in set.mm).  See
     ~ sinh-conventional for a justification that our definition is the same as
     the conventional definition of sinh used in other sources.  (Contributed
     by David A. Wheeler, 20-Apr-2015.) $)
  df-sinh $a |- sinh = ( x e. CC |-> ( ( sin ` ( _i x. x ) ) / _i ) ) $.

  $( Define the hyperbolic cosine function (cosh).  We define it this way for
     ~ cmpt , which requires the form ` ( x e. A |-> B ) ` .  (Contributed by
     David A. Wheeler, 10-May-2015.) $)
  df-cosh $a |- cosh = ( x e. CC |-> ( cos ` ( _i x. x ) ) ) $.

  $( Define the hyperbolic tangent function (tanh).  We define it this way for
     ~ cmpt , which requires the form ` ( x e. A |-> B ) ` .  (Contributed by
     David A. Wheeler, 10-May-2015.) $)
  df-tanh $a |- tanh = ( x e. ( `' cosh " ( CC \ { 0 } ) ) |->
                       ( ( tan ` ( _i x. x ) ) / _i ) ) $.

  ${
    $d x A $.
    $( Value of the named sinh function.  Here we show the simple conversion to
       the conventional form used in set.mm, using the definition given by
       ~ df-sinh .  See ~ sinhval for a theorem to convert this further.  See
       ~ sinh-conventional for a justification that our definition is the same
       as the conventional definition of sinh used in other sources.
       (Contributed by David A. Wheeler, 20-Apr-2015.) $)
    sinhval-named $p |- ( A e. CC ->
                          ( sinh ` A ) = ( ( sin ` ( _i x. A ) ) / _i ) ) $=
      ( vx ci cv cmul co csin cfv cdiv cc csinh wceq fveq2d oveq1d df-sinh ovex
      oveq2 fvmpt ) BACBDZEFZGHZCIFCAEFZGHZCIFJKSALZUAUCCIUDTUBGSACEQMNBOUCCIPR
      $.
  $}

  ${
    $d x A $.
    $( Value of the named cosh function.  Here we show the simple conversion to
       the conventional form used in set.mm, using the definition given by
       ~ df-cosh .  See ~ coshval for a theorem to convert this further.
       (Contributed by David A. Wheeler, 10-May-2015.) $)
    coshval-named $p |- ( A e. CC -> ( cosh ` A ) = ( cos ` ( _i x. A ) ) ) $=
      ( vx ci cv cmul co ccos cfv cc ccosh wceq oveq2 fveq2d df-cosh fvex fvmpt
      ) BACBDZEFZGHCAEFZGHIJQAKRSGQACELMBNSGOP $.
  $}

  ${
    $d x A $.
    $( Value of the named tanh function.  Here we show the simple conversion to
       the conventional form used in set.mm, using the definition given by
       ~ df-tanh .  (Contributed by David A. Wheeler, 10-May-2015.) $)
    tanhval-named $p |- ( A e. ( `' cosh " ( CC \ { 0 } ) ) ->
                          ( tanh ` A ) = ( ( tan ` ( _i x. A ) ) / _i ) ) $=
      ( vx ci cv cmul co ctan cfv cdiv ccosh ccnv cc0 csn cdif cima ctanh oveq2
      cc wceq fveq2d oveq1d df-tanh ovex fvmpt ) BACBDZEFZGHZCIFCAEFZGHZCIFJKRL
      MNOPUEASZUGUICIUJUFUHGUEACEQTUABUBUICIUCUD $.
  $}

  $( Conventional definition of sinh.  Here we show that the sinh definition
     we're using has the same meaning as the conventional definition used in
     some other sources.  We choose a slightly different definition of sinh
     because it has fewer operations, and thus is more convenient to manipulate
     using set.mm.  (Contributed by David A. Wheeler, 10-May-2015.) $)
  sinh-conventional $p |- ( A e. CC ->
                 ( sinh ` A ) = ( -u _i x. ( sin ` ( _i x. A ) ) ) ) $=
    ( cc wcel csinh cfv ci cmul co csin cdiv c1 cneg sinhval-named ax-icn mulcl
    wceq mpan sincld cc0 wne ine0 divrec2 mp3an23 syl irec oveq1i a1i 3eqtrd )
    ABCZADEFAGHZIEZFJHZKFJHZUKGHZFLZUKGHZAMUIUKBCZULUNPZUIUJFBCZUIUJBCNFAOQRUQU
    SFSTURNUAUKFUBUCUDUNUPPUIUMUOUKGUEUFUGUH $.

  $( TODO: Show that tanh(x) = -i tan(ix). $)

  $( Prove that ` ( sinh `` A ) + ( cosh `` A ) = ( exp `` A ) ` using the
     conventional hyperbolic trigonometric functions.  (Contributed by David A.
     Wheeler, 27-May-2015.) $)
  sinhpcosh $p |- ( A e. CC ->
                   ( ( sinh ` A ) + ( cosh ` A ) ) = ( exp ` A ) ) $=
    ( cc wcel csinh cfv ccosh caddc co c2 ce cmul cdiv cneg cmin eqtrd 2cn 2ne0
    ci efcl a1i csin sinhval-named sinhval coshval-named coshval oveq12d cc0 wa
    ccos wne wceq addcld subcld divdir syl3an1 syl3an2 3anidm12 mpanr12 2timesd
    negcl syl nppcand addassd 3eqtr2rd oveq1d 3eqtr2d divcan3d ) ABCZADEZAFEZGH
    ZIAJEZKHZILHZVLVHVKVLAMZJEZNHZILHZVLVPGHZILHZGHZVQVSGHZILHZVNVHVIVRVJVTGVHV
    IRAKHZUAERLHVRAUBAUCOVHVJWDUIEVTAUDAUEOUFVHIBCZIUGUJZWCWAUKZPQVHWEWFUHZWGVH
    VHVSBCZWHWGVHVLVPASZVHVOBCVPBCAUTVOSVAZULVHVQBCWIWHWGVHVLVPWJWKUMZVQVSIUNUO
    UPUQURVHWBVMILVHVMVLVLGHVQVLGHVPGHWBVHVLWJUSVHVLVPVLWJWKWJVBVHVQVLVPWLWJWKV
    CVDVEVFVHVLIWJWEVHPTWFVHQTVGO $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Reciprocal trigonometric functions (sec, csc, cot)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  Define the traditional reciprocal trigonometric functions
  secant (sec), cosecant (csc), and cotangent (cos), along with
  various identities involving them.

$)

  $c sec $. $( Secant function. $)
  $c csc $. $( Cosecant function. $)
  $c cot $. $( Cotangent function. $)

  $( Extend class notation to include the secant function, see ~ df-sec . $)
  csec $a class sec $.

  $( Extend class notation to include the cosecant function, see ~ df-csc . $)
  ccsc $a class csc $.

  $( Extend class notation to include the cotangent function, see ~ df-cot . $)
  ccot $a class cot $.

  ${
    $d x y $.
    $( Define the secant function.  We define it this way for ~ cmpt , which
       requires the form ` ( x e. A |-> B ) ` .  The sec function is defined in
       ISO 80000-2:2009(E) operation 2-13.6 and "NIST Digital Library of
       Mathematical Functions" section on "Trigonometric Functions"
       ~ http://dlmf.nist.gov/4.14 .  (Contributed by David A. Wheeler,
       14-Mar-2014.) $)
    df-sec $a |- sec = ( x e. { y e. CC | ( cos ` y ) =/= 0 } |->
                       ( 1 / ( cos ` x ) ) ) $.

    $( Define the cosecant function.  We define it this way for ~ cmpt , which
       requires the form ` ( x e. A |-> B ) ` .  The csc function is defined in
       ISO 80000-2:2009(E) operation 2-13.7 and "NIST Digital Library of
       Mathematical Functions" section on "Trigonometric Functions"
       ~ http://dlmf.nist.gov/4.14 .  (Contributed by David A. Wheeler,
       14-Mar-2014.) $)
    df-csc $a |- csc = ( x e. { y e. CC | ( sin ` y ) =/= 0 } |->
                       ( 1 / ( sin ` x ) ) ) $.

    $( Define the cotangent function.  We define it this way for ~ cmpt , which
       requires the form ` ( x e. A |-> B ) ` .  The cot function is defined in
       ISO 80000-2:2009(E) operation 2-13.5 and "NIST Digital Library of
       Mathematical Functions" section on "Trigonometric Functions"
       ~ http://dlmf.nist.gov/4.14 .  (Contributed by David A. Wheeler,
       14-Mar-2014.) $)
    df-cot $a |- cot = ( x e. { y e. CC | ( sin ` y ) =/= 0 } |->
                       ( ( cos ` x ) / ( sin ` x ) ) ) $.
  $}

  ${
    $d x y A $.
    $( Value of the secant function.  (Contributed by David A. Wheeler,
       14-Mar-2014.) $)
    secval $p |- ( ( A e. CC /\ ( cos ` A ) =/= 0 ) ->
                   ( sec ` A ) = ( 1 / ( cos ` A ) ) ) $=
      ( vy vx cc wcel ccos cfv cc0 wa cv crab csec c1 cdiv co wceq fveq2 neeq1d
      wne elrab oveq2d df-sec ovex fvmpt sylbir ) ADEAFGZHSZIABJZFGZHSZBDKZEALG
      MUFNOZPUJUGBADUHAPUIUFHUHAFQRTCAMCJZFGZNOULUKLUMAPUNUFMNUMAFQUACBUBMUFNUC
      UDUE $.

    $( Value of the cosecant function.  (Contributed by David A. Wheeler,
       14-Mar-2014.) $)
    cscval $p |- ( ( A e. CC /\ ( sin ` A ) =/= 0 ) ->
                   ( csc ` A ) = ( 1 / ( sin ` A ) ) ) $=
      ( vy vx cc wcel csin cfv cc0 wa cv crab ccsc c1 cdiv co wceq fveq2 neeq1d
      wne elrab oveq2d df-csc ovex fvmpt sylbir ) ADEAFGZHSZIABJZFGZHSZBDKZEALG
      MUFNOZPUJUGBADUHAPUIUFHUHAFQRTCAMCJZFGZNOULUKLUMAPUNUFMNUMAFQUACBUBMUFNUC
      UDUE $.

    $( Value of the cotangent function.  (Contributed by David A. Wheeler,
       14-Mar-2014.) $)
    cotval $p |- ( ( A e. CC /\ ( sin ` A ) =/= 0 ) ->
                   ( cot ` A ) = ( ( cos ` A ) / ( sin ` A ) ) ) $=
      ( vy vx cc wcel csin cfv cc0 wne wa cv crab ccot ccos cdiv co wceq neeq1d
      fveq2 elrab oveq12d df-cot ovex fvmpt sylbir ) ADEAFGZHIZJABKZFGZHIZBDLZE
      AMGANGZUFOPZQUJUGBADUHAQUIUFHUHAFSRTCACKZNGZUNFGZOPUMUKMUNAQUOULUPUFOUNAN
      SUNAFSUACBUBULUFOUCUDUE $.
  $}

  $( The closure of the secant function with a complex argument.  (Contributed
     by David A. Wheeler, 14-Mar-2014.) $)
  seccl $p |- ( ( A e. CC /\ ( cos ` A ) =/= 0 ) ->
              ( sec ` A ) e. CC ) $=
    ( cc wcel ccos cfv cc0 wne wa csec c1 cdiv secval coscl adantr simpr reccld
    co eqeltrd ) ABCZADEZFGZHZAIEJTKQBALUBTSTBCUAAMNSUAOPR $.

  $( The closure of the cosecant function with a complex argument.
     (Contributed by David A. Wheeler, 14-Mar-2014.) $)
  csccl $p |- ( ( A e. CC /\ ( sin ` A ) =/= 0 ) ->
              ( csc ` A ) e. CC ) $=
    ( cc wcel csin cfv cc0 wne wa ccsc c1 cdiv cscval sincl adantr simpr reccld
    co eqeltrd ) ABCZADEZFGZHZAIEJTKQBALUBTSTBCUAAMNSUAOPR $.

  $( The closure of the cotangent function with a complex argument.
     (Contributed by David A. Wheeler, 15-Mar-2014.) $)
  cotcl $p |- ( ( A e. CC /\ ( sin ` A ) =/= 0 ) -> ( cot ` A ) e. CC ) $=
    ( cc wcel csin cfv cc0 wa ccot ccos cdiv co cotval coscl adantr sincl simpr
    wne divcld eqeltrd ) ABCZADEZFQZGZAHEAIEZUAJKBALUCUDUATUDBCUBAMNTUABCUBAONT
    UBPRS $.

  $( The closure of the secant function with a real argument.  (Contributed by
     David A. Wheeler, 15-Mar-2014.) $)
  reseccl $p |- ( ( A e. RR /\ ( cos ` A ) =/= 0 ) -> ( sec ` A ) e. RR ) $=
    ( cr wcel ccos cfv cc0 wa csec c1 cdiv co cc wceq recn secval sylan recoscl
    wne 1red redivcl syl3an1 syl3an2 3anidm12 eqeltrd ) ABCZADEZFRZGAHEZIUFJKZB
    UEALCUGUHUIMANAOPUEUGUIBCZUEUEUFBCZUGUJAQUEIBCUKUGUJUESIUFTUAUBUCUD $.

  $( The closure of the cosecant function with a real argument.  (Contributed
     by David A. Wheeler, 15-Mar-2014.) $)
  recsccl $p |- ( ( A e. RR /\ ( sin ` A ) =/= 0 ) -> ( csc ` A ) e. RR ) $=
    ( cr wcel csin cfv cc0 wa ccsc c1 cdiv co cc wceq recn cscval sylan resincl
    wne 1red redivcl syl3an1 syl3an2 3anidm12 eqeltrd ) ABCZADEZFRZGAHEZIUFJKZB
    UEALCUGUHUIMANAOPUEUGUIBCZUEUEUFBCZUGUJAQUEIBCUKUGUJUESIUFTUAUBUCUD $.

  $( The closure of the cotangent function with a real argument.  (Contributed
     by David A. Wheeler, 15-Mar-2014.) $)
  recotcl $p |- ( ( A e. RR /\ ( sin ` A ) =/= 0 ) -> ( cot ` A ) e. RR ) $=
    ( cr wcel csin cfv cc0 wne wa ccot ccos cdiv co cc wceq recn cotval resincl
    sylan recoscl redivcl syl3an1 syl3an2 3anidm12 eqeltrd ) ABCZADEZFGZHAIEZAJ
    EZUFKLZBUEAMCUGUHUJNAOAPRUEUGUJBCZUEUEUFBCZUGUKAQUEUIBCULUGUKASUIUFTUAUBUCU
    D $.

  $( The reciprocal of secant is cosine.  (Contributed by David A. Wheeler,
     14-Mar-2014.) $)
  recsec $p |- ( ( A e. CC /\ ( cos ` A ) =/= 0 ) ->
                 ( cos ` A ) = ( 1 / ( sec ` A ) ) ) $=
    ( cc wcel ccos cfv cc0 wne wa c1 csec cdiv secval oveq2d coscl recrec sylan
    co wceq eqtr2d ) ABCZADEZFGZHZIAJEZKQIIUAKQZKQZUAUCUDUEIKALMTUABCUBUFUARANU
    AOPS $.

  $( The reciprocal of cosecant is sine.  (Contributed by David A. Wheeler,
     14-Mar-2014.) $)
  reccsc $p |- ( ( A e. CC /\ ( sin ` A ) =/= 0 ) ->
               ( sin ` A ) = ( 1 / ( csc ` A ) ) ) $=
    ( cc wcel csin cfv cc0 wne wa c1 ccsc cdiv cscval oveq2d sincl recrec sylan
    co wceq eqtr2d ) ABCZADEZFGZHZIAJEZKQIIUAKQZKQZUAUCUDUEIKALMTUABCUBUFUARANU
    AOPS $.

  $( The reciprocal of cotangent is tangent.  (Contributed by David A. Wheeler,
     21-Mar-2014.) $)
  reccot $p |- ( ( A e. CC /\ ( sin ` A ) =/= 0 /\ ( cos ` A ) =/= 0 ) ->
                   ( tan ` A ) = ( 1 / ( cot ` A ) ) ) $=
    ( cc wcel csin cfv cc0 wne ccos w3a c1 cdiv co ccot ctan sincl coscl recdiv
    wceq wa sylanl1 sylanr1 3impdi 3com23 cotval 3adant3 oveq2d tanval 3eqtr4rd
    3adant2 ) ABCZADEZFGZAHEZFGZIZJUMUKKLZKLZUKUMKLZJAMEZKLANEZUJUNULUQURRZUJUN
    ULVAUJUJUNSUKBCZULVAAOUJUMBCUNVBULSVAAPUMUKQTUAUBUCUOUSUPJKUJULUSUPRUNAUDUE
    UFUJUNUTURRULAUGUIUH $.

  $( The reciprocal of tangent is cotangent.  (Contributed by David A. Wheeler,
     21-Mar-2014.) $)
  rectan $p |- ( ( A e. CC /\ ( sin ` A ) =/= 0 /\ ( cos ` A ) =/= 0 ) ->
                   ( cot ` A ) = ( 1 / ( tan ` A ) ) ) $=
    ( cc wcel csin cfv cc0 wne ccos w3a c1 cdiv co ctan ccot coscl sincl recdiv
    wceq wa sylanl1 sylanr1 3impdi tanval 3adant2 oveq2d 3adant3 3eqtr4rd
    cotval ) ABCZADEZFGZAHEZFGZIZJUJULKLZKLZULUJKLZJAMEZKLANEZUIUKUMUPUQRZUIUIU
    KSULBCZUMUTAOUIUJBCUKVAUMSUTAPUJULQTUAUBUNURUOJKUIUMURUORUKAUCUDUEUIUKUSUQR
    UMAUHUFUG $.

  $( The value of the secant function at zero is one.  (Contributed by David A.
     Wheeler, 16-Mar-2014.) $)
  sec0 $p |- ( sec ` 0 ) = 1 $=
    ( cc0 csec cfv c1 ccos cdiv co cc wcel wne wceq cos0 ax-1ne0 eqnetri secval
    0cn mp2an oveq2i 1div1e1 3eqtri ) ABCZDAECZFGZDDFGDAHIUBAJUAUCKPUBDALMNAOQU
    BDDFLRST $.

  $( Prove the tangent squared secant squared identity
     ` ( 1 + ( ( tan `` A ) ^ 2 ) ) = ( ( sec `` A ) ^ 2 ) ) ` .  (Contributed
     by David A. Wheeler, 25-May-2015.) $)
  onetansqsecsq $p |- ( ( A e. CC /\ ( cos ` A ) =/= 0 ) ->
                      ( 1 + ( ( tan ` A ) ^ 2 ) ) = ( ( sec ` A ) ^ 2 ) ) $=
    ( cc wcel cfv cc0 wne wa c1 c2 cexp co caddc cdiv wceq sqcld oveq1d syl3an2
    sylan 3anidm12 eqtrd ccos ctan csec csin wb coscl sqeq0 syl necon3bid divid
    biimpar syldan eqcomd tanval 2nn0 sincl expdiv syl3an1 mp3an3 3impb oveq12d
    cn0 divdir eqtr4d addcomd eqtr3d adantr secval ax-1cn mp3an13 oveq1i eqtrdi
    sincossq sq1 ) ABCZAUADZEFZGZHAUBDZIJKZLKZHVPIJKZMKZAUCDZIJKZVRWAWBAUDDZIJK
    ZLKZWBMKZWCVRWAWBWBMKZWGWBMKZLKZWIVRHWJVTWKLVRWJHVOVQWBEFZWJHNZVOWMVQVOWBEV
    PEVOVPBCZWBENVPENUEAUFZVPUGUHUIUKZVOWBBCZWMWNVOVPWPOZWBUJRULUMVRVTWFVPMKZIJ
    KZWKVRVSWTIJAUNPVOVQXAWKNZVOVOWOVQXBWPVOWOVQXBVOWOVQGZIVBCZXBUOVOWFBCXCXDXB
    AUPZWFVPIUQURUSUTQSTVAVOVQWMWIWLNZWQVOWMXFVOVOWRWMXFWSVOWRWMXFVOWRWMGZXFVOV
    OWGBCZXGXFVOWFXEOZVOWRXHXGXFWSWBWGWBVCURQSUTQSULVDVOWIWCNVQVOWHHWBMVOWGWBLK
    WHHVOWGWBXIWSVEAVMVFPVGTVRWEHVPMKZIJKZWCVRWDXJIJAVHPVRXKHIJKZWBMKZWCVOWOVQX
    KXMNZWPHBCXCXDXNVIUOHVPIUQVJRXLHWBMVNVKVLTVD $.

  $( Prove the tangent squared cosecant squared identity
     ` ( 1 + ( ( cot `` A ) ^ 2 ) ) = ( ( csc `` A ) ^ 2 ) ) ` .  (Contributed
     by David A. Wheeler, 27-May-2015.) $)
  cotsqcscsq $p |- ( ( A e. CC /\ ( sin ` A ) =/= 0 ) ->
                  ( 1 + ( ( cot ` A ) ^ 2 ) ) = ( ( csc ` A ) ^ 2 ) ) $=
    ( cc wcel cfv cc0 wne wa c1 c2 cexp co caddc cdiv oveq1d oveq2d wceq adantr
    sqcld 2nn0 expdiv csin ccot ccos cotval sincossq sincl wb sqne0 syl biimpar
    ccsc dividd coscl divdird jca mp3an3 anassrs 3eqtr4rd cscval ax-1cn mp3an13
    cn0 sylan sq1 oveq1i eqtrdi eqtrd eqtr4d ) ABCZAUADZEFZGZHAUBDZIJKZLKHAUCDZ
    VJMKZIJKZLKZAUKDZIJKZVLVNVQHLVLVMVPIJAUDNOVLVJIJKZVOIJKZLKZWAMKZHWAMKZVRVTV
    IWDWEPVKVIWCHWAMAUENQVLWAWAMKZWBWAMKZLKHWGLKWDVRVLWFHWGLVLWAVIWABCVKVIVJAUF
    ZRQZVIWAEFZVKVIVJBCZWJVKUGWHVJUHUIUJZULNVLWAWBWAWIVIWBBCVKVIVOAUMZRQWIWLUNV
    LVQWGHLVIVOBCZWKGVKVQWGPZVIWNWKWMWHUOWNWKVKWOWNWKVKGZIVBCZWOSVOVJITUPUQVCOU
    RVLVTHVJMKZIJKZWEVLVSWRIJAUSNVLWSHIJKZWAMKZWEVIWKVKWSXAPZWHHBCWPWQXBUTSHVJI
    TVAVCWTHWAMVDVEVFVGURVH $.

  ${
    $d x y $.
    $( Derivative of the secant function.  (Contributed by Jon Pennant,
       28-Aug-2026.) $)
    dvsec $p |- ( CC _D sec ) = ( x e. dom sec |->
                ( ( sec ` x ) x. ( tan ` x ) ) ) $=
      ( vy cc csec cdv co ccos cfv cc0 c1 cdiv cmpt cmul cneg wceq wtru a1i syl
      wcel eqtrd cv wne crab cdm ctan df-sec oveq2i csin c2 cexp cpr cnelprrecn
      cr 1cnd csn wa elrabi coscl fveq2 neeq1d elrab simprbi jca eldifsn sylibr
      cdif adantl sincl negcld ccnfld ctopn cosf feqmptd mptru dvcos eqtr3i wss
      ssrab2 eqid cnfldtopon toponrestid ccnv cima ccn ccncf coscn cncfcn mp2an
      wf ssid eleqtri cnn0opn cnima baib bicomd rabbiia mptpreima eqtr4i eleq1i
      mpbir dvmptres dvrecg mullidd sqval oveq12d negeqd mulcld mulne0d divnegd
      wb negnegd oveq1d ax-1cn eqcomd secval sylbi tanval mpteq2ia divcld fmpti
      divmuldivd fdmi eqcomi mpteq1i eqtri ) CDEFCABUAZGHZIUBZBCUCZJAUAZGHZKFZL
      ZEFZADUDZYJDHZYJUEHZMFZLZDYMCEABUFZUGYNAYIJYJUHHZNZMFZYKUIUJFZKFZNZLZYSYN
      UUGOPAJYKUUBCCYICUMCUKSPULQZPUNYJYISZYKCIUOVFZSZPUUIYKCSZYKIUBZUPUUKUUIUU
      LUUMUUIYJCSZUULYHBYJCUQZYJURZRZUUIUUNUUMYHUUMBYJCYFYJOYGYKIYFYJGUSUTVAZVB
      ZVCYKCIVDVEVGPUUIUPUUAUUIUUACSZPUUIUUNUUTUUOYJVHZRZVGVIPAYKUUBCVJVKHZUVCC
      CYIUUHUUNUULPUUPVGUUNUUBCSPUUNUUAUVAVIVGCACYKLZEFZACUUBLZOPCGEFUVEUVFGUVD
      CEGUVDOPACCGCCGWIPVLQZVMVNUGAVOVPQYICVQPYHBCVRQUVCCUVCUVCVSZVTWAZUVHYIUVC
      SZPUVJGWBUUJWCZUVCSZGUVCUVCWDFZSUUJUVCSUVLGCCWEFZUVMWFCCVQZUVOUVNUVMOCWJZ
      UVPCCUVCUVCUVCUVHUVIUVIWGWHWKWLUUJGUVCUVCWMWHYIUVKUVCYIYGUUJSZBCUCUVKYHUV
      QBCYFCSZUVQYHUVRYGCSZUVQYHXJYFURUVQUVSYHYGCIVDWNRWOWPBCYGUUJGGBCYGLOPBCCG
      UVGVMVNWQWRWSWTQXAXBVNUUGAYIYRLYSAYIUUFYRUUIUUFYLUUAYKKFZMFZYRUUIUUFUUAYK
      YKMFZKFZUWAUUIUUFUUBUWBKFZNZUWCUUIUUEUWDUUIUUCUUBUUDUWBKUUIUUBUUIUUAUVBVI
      ZXCUUIUULUUDUWBOUUQYKXDRXEXFUUIUWEUUBNZUWBKFUWCUUIUUBUWBUWFUUIYKYKUUQUUQX
      GUUIYKYKUUQUUQUUSUUSXHXIUUIUWGUUAUWBKUUIUUAUVBXKXLTTUUIUWAUWCUUIUWAJUUAMF
      ZUWBKFUWCUUIJYKUUAYKJCSUUIXMQZUUQUVBUUQUUSUUSYAUUIUWHUUAUWBKUUIUUAUVBXCXL
      TXNTUUIYLYPUVTYQMUUIYPYLUUIUUNUUMUPZYPYLOUURYJXOXPXNUUIYQUVTUUIUWJYQUVTOU
      URYJXQXPXNXETXRAYIYOYRYOYIYICDAYICYLDYTUUIJYKUWIUUQUUSXSXTYBYCYDYEYEYE $.

    $( Derivative of the cosecant function.  (Contributed by Jon Pennant,
       28-Aug-2026.) $)
    dvcsc $p |- ( CC _D csc ) = ( x e. dom csc |->
                ( -u ( csc ` x ) x. ( cot ` x ) ) ) $=
      ( vy cc ccsc cdv csin cfv cc0 cdiv cmpt ccos cmul cneg wceq wtru wcel a1i
      co c1 syl cv wne crab cexp cdm ccot df-csc oveq2i cpr cnelprrecn 1cnd csn
      c2 cr cdif wa elrabi sincl fveq2 neeq1d simprbi jca eldifsn sylibr adantl
      elrab coscl ccnfld ctopn sinf feqmptd mptru dvsin eqtr3i eqtri wss ssrab2
      wf cosf eqid cnfldtopon toponrestid ccnv cima ccn ccncf sincn ssid cncfcn
      mp2an eleqtri cnn0opn cnima wb baib bicomd rabbiia mptpreima eqtr4i mpbir
      eleq1i dvrecg mullidd sqval oveq12d negeqd ax-1cn divmuldivd oveq1d eqtrd
      dvmptres eqcomd divcld mulneg1d cscval sylbi cotval mpteq2ia fmpti eqcomi
      fdmi mpteq1i 3eqtri ) CDERCABUAZFGZHUBZBCUCZSAUAZFGZIRZJZERZAYGSYHKGZLRZY
      IUMUDRZIRZMZJZADUEZYHDGZMZYHUFGZLRZJZDYKCEABUGZUHYLYRNOASYIYMCCYGCUNCUIPO
      UJQZOUKYHYGPZYICHULUOZPZOUUGYICPZYIHUBZUPUUIUUGUUJUUKUUGYHCPZUUJYFBYHCUQZ
      YHURZTZUUGUULUUKYFUUKBYHCYDYHNYEYIHYDYHFUSUTVFZVAZVBYICHVCVDVEUUGYMCPZOUU
      GUULUURUUMYHVGZTZVEOAYIYMCVHVIGZUVACCYGUUFUULUUJOUUNVEUULUUROUUSVECACYIJZ
      ERZACYMJZNOUVCKUVDCFERUVCKFUVBCEFUVBNOACCFCCFVROVJQZVKVLUHVMVNKUVDNOACCKC
      CKVROVSQVKVLVOQYGCVPOYFBCVQQUVACUVAUVAVTZWAWBZUVFYGUVAPZOUVHFWCUUHWDZUVAP
      ZFUVAUVAWERZPUUHUVAPUVJFCCWFRZUVKWGCCVPZUVMUVLUVKNCWHZUVNCCUVAUVAUVAUVFUV
      GUVGWIWJWKWLUUHFUVAUVAWMWJYGUVIUVAYGYEUUHPZBCUCUVIYFUVOBCYDCPZUVOYFUVPYEC
      PZUVOYFWNYDURUVOUVQYFYECHVCWOTWPWQBCYEUUHFFBCYEJNOBCCFUVEVKVLWRWSXAWTQXKX
      BVLYRAYGUUCJUUDAYGYQUUCUUGYQYJMZYMYIIRZLRZUUCUUGYQYJUVSLRZMZUVTUUGYQYMYIY
      ILRZIRZMUWBUUGYPUWDUUGYNYMYOUWCIUUGYMUUTXCZUUGUUJYOUWCNUUOYIXDTXEXFUUGUWD
      UWAUUGUWAUWDUUGUWAYNUWCIRUWDUUGSYIYMYISCPUUGXGQZUUOUUTUUOUUQUUQXHUUGYNYMU
      WCIUWEXIXJXLXFXJUUGUVTUWBUUGYJUVSUUGSYIUWFUUOUUQXMZUUGYMYIUUTUUOUUQXMXNXL
      XJUUGUVRUUAUVSUUBLUUGYJYTUUGYTYJUUGUULUUKUPZYTYJNUUPYHXOXPXLXFUUGUUBUVSUU
      GUWHUUBUVSNUUPYHXQXPXLXEXJXRAYGYSUUCYSYGYGCDAYGCYJDUUEUWGXSYAXTYBVOYC $.

    $( Derivative of the cotangent function.  (Contributed by Jon Pennant,
       28-Aug-2026.) $)
    dvcot $p |- ( CC _D cot ) = ( x e. dom cot |->
                 -u ( ( csc ` x ) ^ 2 ) ) $=
      ( vy cc cdv co csin cc0 ccos cdiv cmpt cneg c2 cexp wceq wtru wcel a1i c1
      syl eqtrd ccot cv cfv wne crab cmul cmin ccsc df-cot oveq2i cr cnelprrecn
      cdm cpr elrabi coscl adantl sincl negcld ccnfld ctopn wf cosf mptru dvcos
      feqmptd eqtr3i wss ssrab2 eqid cnfldtopon toponrestid ccnv csn cdif ccncf
      cima sincn ssid cncfcn mp2an eleqtri cnn0opn cnima wb eldifsn baib bicomd
      rabbiia sinf mptpreima eqtr4i eleq1i mpbir dvmptres wa fveq2 neeq1d elrab
      ccn simprbi jca sylibr dvsin eqtri dvmptdiv mulneg1d sqval eqcomd oveq12d
      negeqd negdi2 syl2anc sincossq oveq1d ax-1cn mpbird divneg syl3anc cscval
      caddc sqcld sqne0 sylbi sqdiv mpteq2ia divcld fmpti eqcomi mpteq1i 3eqtri
      sq1 fdmi ) CUADECABUBZFUCZGUDZBCUEZAUBZHUCZYRFUCZIEZJZDEZAYQYTKZYTUFEZYSY
      SUFEZUGEZYTLMEZIEZJZAUAUMZYRUHUCZLMEZKZJZUAUUBCDABUIZUJUUCUUJNOAYSUUDYTYS
      CCYQCUKCUNPOULQZYRYQPZYSCPZOUURYRCPZUUSYPBYRCUOZYRUPZSZUQZUURUUDCPZOUURYT
      UURUUTYTCPZUVAYRURZSZUSUQOAYSUUDCUTVAUCZUVICCYQUUQUUTUUSOUVBUQZUUTUVEOUUT
      YTUVGUSUQCACYSJZDEZACUUDJZNOCHDEUVLUVMHUVKCDHUVKNOACCHCCHVBOVCQVFVDZUJAVE
      VGQYQCVHOYPBCVIQZUVICUVIUVIVJZVKVLZUVPYQUVIPZOUVRFVMCGVNVOZVQZUVIPZFUVIUV
      IWTEZPUVSUVIPUWAFCCVPEZUWBVRCCVHZUWDUWCUWBNCVSZUWECCUVIUVIUVIUVPUVQUVQVTW
      AWBWCUVSFUVIUVIWDWAYQUVTUVIYQYOUVSPZBCUEUVTYPUWFBCYNCPZUWFYPUWGYOCPZUWFYP
      WEYNURUWFUWHYPYOCGWFWGSWHWIBCYOUVSFFBCYOJNOBCCFCCFVBOWJQZVFVDWKWLWMWNQZWO
      UURYTUVSPZOUURUVFYTGUDZWPUWKUURUVFUWLUVHUURUUTUWLYPUWLBYRCYNYRNYOYTGYNYRF
      WQWRWSZXAZXBYTCGWFXCUQUVDOAYTYSCUVIUVICCYQUUQUUTUVFOUVGUQUVJCACYTJZDEZUVK
      NOUWPHUVKCFDEUWPHFUWOCDFUWONOACCFUWIVFVDUJXDVGUVNXEQUVOUVQUVPUWJWOXFVDUUJ
      AYQUUNJUUOAYQUUIUUNUURUUIRUUHIEZKZUUNUURUUIRKZUUHIEZUWRUURUUGUWSUUHIUURUU
      GUUHKZYSLMEZUGEZUWSUURUUEUXAUUFUXBUGUURUUEYTYTUFEZKUXAUURYTYTUVHUVHXGUURU
      XDUUHUURUUHUXDUURUVFUUHUXDNUVHYTXHSXIXKTUURUXBUUFUURUUSUXBUUFNUVCYSXHSXIX
      JUURUXCUUHUXBYAEZKZUWSUURUXFUXCUURUUHCPZUXBCPUXFUXCNUURYTUVHYBZUURYSUVCYB
      UUHUXBXLXMXIUURUXERUURUUTUXERNUVAYRXNSXKTTXOUURUWRUWTUURRCPZUXGUUHGUDZUWR
      UWTNUXIUURXPQZUXHUURUXJUWLUWNUURUVFUXJUWLWEUVHYTYCSXQRUUHXRXSXITUURUWQUUM
      UURUUMUWQUURUUMRYTIEZLMEZUWQUURUULUXLLMUURUUTUWLWPUULUXLNUWMYRXTYDXOUURUX
      MRLMEZUUHIEZUWQUURUXIUVFUWLUXMUXONUXKUVHUWNRYTYEXSUURUXNRUUHIUXNRNUURYLQX
      OTTXIXKTYFAYQUUKUUNUUKYQYQCUAAYQCUUAUAUUPUURYSYTUVCUVHUWNYGYHYMYIYJXEYK
      $.

  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Identities for "if"
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  Utility theorems for "if".

$)

  $( If A is not a member of B, but an "if" condition requires it, then the
     "false" branch results.  This is a simple utility to provide a slight
     shortening and simplification of proofs versus applying ~ iffalse directly
     in this case.  (Contributed by David A. Wheeler, 15-May-2015.) $)
  ifnmfalse $p |- ( A e/ B -> if ( A e. B , C , D ) = D ) $=
    ( wnel wcel wn cif wceq df-nel iffalse sylbi ) ABEABFZGMCDHDIABJMCDKL $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Other functions
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( TODO: Here are some other functions to define.

     Reciprocal and arc hyperbolic functions, per
     "NIST Digital Library of Mathematical Functions" ,
     "Hyperbolic Functions - Definitions and Periodicity" at
     ~ http://dlmf.nist.gov/4.28
     and ISO 80000-2:2009(E) operation 2-13.17 and on.
     Note that ISO names the reciprocal sinh as "arsinh" and so on
     (no letter "c"), while NIST names them "Arcsinh" and "arcsinh" and so on
     (using the letter "c") - see ~ http://dlmf.nist.gov/4.37 .
     Also, the "elementary properties" stated at ~ http://dlmf.nist.gov/4.30
     should be checked to ensure all are proven.

     Double-factorial '!!', per
     "NIST Digital Library of Mathematical Functions" , front introduction,
     "Common Notations and Definitions" section at
     ~ http://dlmf.nist.gov/front/introduction#Sx4 .

     Arithmetic mean aka average
     "NIST Digital Library of Mathematical Functions" , front introduction,
     "Common Notations and Definitions" section at
      ~ http://dlmf.nist.gov/1.2#iv .

     Geometric mean
     "NIST Digital Library of Mathematical Functions" , front introduction,
     "Common Notations and Definitions" section at
      ~ http://dlmf.nist.gov/1.2#iv .

     Harmonic mean
     "NIST Digital Library of Mathematical Functions" , front introduction,
     "Common Notations and Definitions" section at
      ~ http://dlmf.nist.gov/1.2#iv .
 $)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Logarithms generalized to arbitrary base using ` logb `
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  Most of this subsection was moved to main set.mm, section "Logarithms to an
  arbitrary base".

$)

  $( Define the value of the ` logb ` function, the logarithm generalized to an
     arbitrary base, when used in the 2-argument form ` logb <. B , X >. `
     (Contributed by David A. Wheeler, 21-Jan-2017.)  (Revised by David A.
     Wheeler, 16-Jul-2017.) $)
  logb2aval $p |- ( ( B e. ( CC \ { 0 , 1 } ) /\ X e. ( CC \ { 0 } ) )
         -> ( logb ` <. B , X >. ) = ( ( log ` X ) / ( log ` B ) ) ) $=
    ( cc cc0 c1 cpr cdif wcel csn wa cop clogb cfv co clog cdiv logbval eqtr3id
    df-ov ) ACDEFGHBCDIGHJABKLMABLNBOMAOMPNABLSABQR $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Logarithm laws generalized to an arbitrary base - log_
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  Define "log using an arbitrary base" function and then prove some of its
  properties.  This builds on previous work by Stefan O'Rear.

  This supports the notational form ` ( ( log_ `` B ) `` X ) ` ;  that looks a
  little more like traditional notation, but is different from other
  2-parameter functions.  E.g., ` ( ( log_ `` ; 1 0 ) `` ; ; 1 0 0 ) = 2 ` .

  This form is less convenient to work with inside set.mm as compared to the
  ` ( B logb X ) ` form defined separately.

$)

  $c log_ $. $( Logarithm generalized to an arbitrary base. $)

  $( Extend class notation to include the logarithm generalized to an arbitrary
     base. $)
  clog- $a class log_ $.

  ${
    $d b x $.
    $( Define the ` log_ ` operator.  This is the logarithm generalized to an
       arbitrary base.  It can be used as ` ( ( log_ `` B ) `` X ) ` for "log
       base B of X".  This formulation suggested by Mario Carneiro.
       (Contributed by David A. Wheeler, 14-Jul-2017.)
       (New usage is discouraged.) $)
    df-logbALT $a |- log_ = ( b e. ( CC \ { 0 , 1 } ) |->
                 ( x e. ( CC \ { 0 } ) |-> ( ( log ` x ) / ( log ` b ) ) ) ) $.
  $}

  $( Define the value of the ` log_ ` function, the logarithm generalized to an
     arbitrary base.  (Contributed by David A. Wheeler, 14-Jul-2017.)
  log_val $p |- ( ( B e. ( CC \ { 0 , 1 } ) /\ X e. ( CC \ { 0 } ) ) ->
                 ( ( log_ ` B ) ` X ) = ( ( log ` X ) / ( log ` B ) ) ) $= ? $.
  $)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Gottlob Frege's work: _Begriffsschrift_ and _Grundgesetze der Arithmetik_
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

Gottlob Frege's _Begriffsschrift_ (German for "concept-script")
is a book on logic published in 1879.
It was eventually recognized as a landmark work;
all work in modern formal logic is indebted to it.
"During his lifetime Frege's work made little impression.
However, the few people he did significantly influence - Husserl,
Peano, Russell, Wittgenstein, and Carnap - themselves became
enormously influential, so that indirectly he can be said to have
shaped a whole philosophical tradition...
But Frege was dead long before his importance was generally recognized ...".
[Sullivan2004] p. 659.

"From one point of view, Frege's logic _needs_ no explanation.
The system of logic he presents in _Begriffsschrift_
simply _is_ modern logic...
in _Begriffsschrift_ modern logic appears to spring forth
fully formed.
The work's list of 'firsts' is remarkable:
the first complete presentation of truth-functional propositional logic;
the first representation of generality through quantifiers and variables,
allowing the first formulation of reasoning involving multiple nested
generality; ...
(but) the _most_ remarkable feature of
_Begriffsschrift_ is that all of these arrive _at once_."
[Sullivan2004] p. 661-662.

_Begriffsschrift_ built on 9 axioms expressed
using a two-dimensional notation.
Modern notation is significantly different, though
the turnstile symbol ` |- ` is a vestige of its two-dimensional notation.
A translation challenge for us is that in our system a value must be a ` wff `
(true/false value) or a ` class ` , while in his system
some expressions could be either.
In Frege's notation "=" works with either a ` wff ` or a ` class `
and is called content identity (equivalence/identity).
For more, see statement (68) on its page 54.
We represent those comparisons as separate symbols,
class equivalence (` = `) and the biconditional (` <-> `).
In many cases Frege's "a" and "b" clearly correspond to our classes.
For example,
Frege takes as example for "a" an Ostrich and F(a) for "a can fly" and
G(a) for "a is a bird". Later he takes Hydrogen for "a" and Oxygen for
"b", and "Hydrogen is lighter than Oxygen" for f(a, b).
Note that F, G, and f take classes and produce true/false values.
However, "a" sometimes is used for true/false values instead.
For example,
page 52 statement (61) appears to read as
( ( f(c) ` -> ` a ) ` /\ A. ` a f(a) ) ` -> ` a ; in this case,
the "a" stands for a true/false value (a ` wff `).

Frege's logic supports second-order logic (in particular, it supports
second-order quantification on class variables).
In contrast, we intentionally use only a first-order formalization,
which does not have some of capabilities of a second-order system.
Therefore, our goal is to merely show that our formalization supports
all the capabilities of Frege's logic (at least his axioms) that are
consistent with being a _first-order_ system.

The following list shows the 9 axioms in a more modern notation,
along with the Metamath expressions and labels that either assume
or prove those axioms.

1. ` A -> ( B -> A ) ` ,
Proposition 1 of [Frege1879] p. 26.
We represent this as ` ( ph -> ( ps -> ph ) ) ` ,
which is our first axiom ~ ax-1 .

2.  ` ( A -> ( B -> C ) ) -> ( ( A -> B ) -> ( A -> C ) ) ` ,
Proposition 2 of [Frege1879] p. 26.
We represent this as
` ( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) ) ) ` ,
which is our second axiom ~ ax-2 .

3. ` ( D -> ( B -> A ) ) -> ( B -> ( D -> A ) ) ` ,
Proposition 8 of [Frege1879] p. 35.
We represent this as
` ( ( ph -> ( ps -> ch ) ) -> ( ps -> ( ph -> ch ) ) ) ` ,
which is proved in ~ pm2.04 .

4.  ` ( B -> A ) -> ( -. A -> -. B ) ` ,
Proposition 28 of [Frege1879] p. 43.
We represent this as ` ( ( ph -> ps ) -> ( -. ps -> -. ph ) ) ` ,
which is proved in ~ con3 .

5. ` -. -. A -> A ` ,
Proposition 31 of [Frege1879] p. 44.
We represent this as ` ( -. -. ph -> ph ) ` ,
which is proved in ~ notnotr .

6. ` A -> -. -. A ` ,
Proposition 41 of [Frege1879] p. 47.
We represent this as ` ( ph -> -. -. ph ) ` ,
which is proved in ~ notnot .

7. ` ( c = d ) -> ( ` f(c) ` = ` f(d) ` ) ` ,
Proposition 52 of [Frege1879] p. 50.
Frege's functions (as represented by f) appear to generate true/false
values in this case.
As a remark to (52), Frege wrote:
"The case where the content/value of c equals the content/value
of d, f(c) is true and f(d) is false doesn't exist. This proposition states
that c can be replaced by d if c = d. Within f(c), c could also be used in
other places, not only as argument. Therefore, c can still be occur in f(d)."
(This is a translation of _der Fall, wo der Inhalt von c gleich dem
Inhalt von d ist, wo f(c) bejaht und f(d) verneint wird, findet nicht
statt. Dieser Satz dr&uuml;ckt aus, dass man &uuml;berall statt
c d setzen k&ouml;nne,
wenn c = d ist. In f(c) kann c auch an andern als den Argumentsstellen
vorkommen. Daher kann c auch noch in f(d) enthalten sein_ .)
The last two sentences seem to mean that c as an argument of f is a free
variable in f, but could also be contained as bound variable in f.
Such bound variables are not replaced if c is substituted by d.
This is more challenging to represent exactly, but a representation
of its spirit seems adequate.
We can generally represent this as
`  ( A = B -> ( [. A / x ]. ph <-> [. B / x ]. ph ) ) ` , which is ~ dfsbcq .
Note that we can also handle the case where f produces a class;
that would be
` ( A = B -> ( F `` A ) = ( F `` B ) ) ` , which is ~ fveq2 ,

8. ` c = c ` ,
Proposition 54 of [Frege1879] p. 50.
We can represent this for wffs as
` ( ph <-> ph ) ` , which is ~ biid ,
or for classes as
` A = A ` , which is ~ eqid .
The rule ` A = A ` is also known as the law of identity, and is thought to have
originated with Aristotle (_Metaphysics_,
Zeta, 17, 1041 a, 10-20).

9. ` A. a ` f(a) ` -> ` f(c) ,
Proposition 58 of [Frege1879] p. 51.
We can represent this as
` ( A e. V -> ( A. x ph -> [. A / x ]. ph ) ) ` , which is ~ spsbc .
Note that we add the condition that the value being replaced
(c in the original and ` A ` in our translation) must itself be a set.
Frege assumed naive set theory, where everything expressable is a set.
When Bertrand Russell showed that this led to problems, by showing
"Russell's paradox" ( ~ ru ), this began the process that led to ZFC
and many other hallmarks of modern logic.

The situation is more complex regarding Frege's inference rules.
In his preface Frege claims to have used only one mode of inference,
_modus ponens_ (our ~ ax-mp ), but he later qualifies this.
In practice
"Frege is at no great pains to separate out inference rules from his
explanation of the notation and conventions governing it"
and is inexact in some of their specifications
([Sullivan2004] p. 671-672).
This makes it more difficult to map Frege's inference rules into
our representation.
The additional rules, per [Sullivan2004] p. 671-672, are:

1. Instantiation: "from a [universally quantified] judgement
&forall;a&Phi;a we can always derive an arbitrary number of
_judgements with less general content_ &Phi;(&Gamma;) by putting
something different each time in place of the gothic letter." (CN 130).
Something similar is in ~ spsbc .

2. Uniform replacement of bound variables. (CN 130).
We believe this is the same as ~ cbval .

3. Substitution: "other substitutions (than previous) are
permitted only if the concavity follows immediately
after the judgement stroke..." (CN 130).

4. Generalization: "An italic letter may always be replaced by a gothic
letter which does not yet occur in the judgement; when this is done, the
concavity must be placed immediately after the judgement stroke"
(CN 132).
We can represent this as ` |- ph => |- A. x ph ` , the rule of generalization,
which is our axiom ~ ax-gen .

5. Confinement: "... from &Gamma; ` -> ` &Phi;a we can derive
&Gamma; ` -> ` ` A. ` a &Phi;a if &Gamma; is an expression in which a
does not occur and a stands only in argument places of &Phi;a"
(CN 132).
This appears to be ~ alrimiv .

Frege's two-volume work of 1893/1903, _Grundgesetze der Arithmetik_
("Foundations of Arithmetic")
proved various fundamental propositions of arithmetic based on the
logic of _Begriffsschrift_ plus a few extra laws.
For more, see:
~ https://plato.stanford.edu/entries/frege-theorem/

Unfortunately Frege's Basic Law V in this work caused the system
to be inconsistent because it was subject to Russell's paradox.

Basic Law V
is now known as the "axiom schema of unrestricted comprehension)",
and is what cause his system to break down.
Frege used basic law V primarily to prove "Hume's Principle",
and he then used Hume's Principle from then on to prove other matters.
So while Frege didn't see the fix at the time, it appears that accepting
Hume's Principle instead of basic law V repairs his system.
~ https://plato.stanford.edu/entries/frege-theorem

Hume's Principle is ~ carden (other related theorems are
~ hasheni and the finite-set-only ~ hashen ).

$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Formally define notions such as reflexivity
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  EXPERIMENTAL.
  Several terms are used in comments but not directly defined in set.mm.  For
  example, there are proofs that a number of specific relations are reflexive,
  but there is no formal definition of what being reflexive actually *means*.
  Stating the relationships directly, instead of defining a broader property
  such as being reflexive, can reduce proof size (because the definition of
  that property does not need to be expanded later).  A disadvantage, however,
  is that there are several terms that are widely used in comments but do not
  have a clear formal definition.

  Here we define wffs that formally define some of these key terms.  The intent
  isn't to use these directly, but to instead provide a clear formal definition
  of widely-used mathematical terminology (we even use this terminology within
  the comments of set.mm itself).

  We could define these using extensible structures, but doing so appears
  overly restrictive.  These definitions don't require the use of extensible
  structures; requiring something to be in an extensible structure to use them
  is too restrictive.  Even if an extensible structure is already in use, it
  may in use for other things.  For example, in geometry, there is a
  "less-than" relation, but while the geometry itself is an extensible
  structure, we would have to build a new structure to state "the geometric
  less-than relation is transitive" (which is more work than it's probably
  worth).  By creating definitions that aren't tied to extensible structures we
  create definitions that can be applied to anything, including extensible
  structures, in whatever way we'd like.

  BJ suggests that it might be better to define these as functions.  There
  are many advantages to doing that, but they won't work for proper classes.
  I'm currently trying to also support proper classes, so I have not taken that
  approach, but if that turns out to be unreasonable then BJ's approach is
  very much worth considering.  Examples would be:
  BinRel = ` ( x e. _V |-> { r | r C_ ( x X. x ) } ) ` ,
  ReflBinRel =
  ` ( x e. _V |-> { r e. ( ` BinRel ` `` x ) | ( _I |`` x ) C_ r } ) ` ,
  and IrreflBinRel =
  ` ( x e. _V |-> { r e. ( ` BinRel
  ` `` x ) | ( r i^i ( _I |`` x ) ) = (/) } ) ` .

  For more discussion see: ~ https://github.com/metamath/set.mm/pull/1286

$)

  $c Reflexive $. $( True iff a relation is reflexive. $)

  $( Extend wff definition to include "Reflexive" applied to a class, which is
     true iff class R is a reflexive relation over the set A. See
     ~ df-reflexive .  (Contributed by David A. Wheeler, 1-Dec-2019.) $)
  wreflexive $a wff R Reflexive A $.

  ${
    $d A x $.  $d R x $.
    $( Define reflexive relation; relation ` R ` is reflexive over the set
       ` A ` iff ` A. x e. A x R x ` .  (Contributed by David A. Wheeler,
       1-Dec-2019.) $)
    df-reflexive $a |- ( R Reflexive A <->
      ( R C_ ( A X. A ) /\ A. x e. A x R x ) ) $.
  $}

  $c Irreflexive $. $( True iff a relation is irreflexive. $)

  $( Extend wff definition to include "Irreflexive" applied to a class, which
     is true iff class R is an irreflexive relation over the set A. See
     ~ df-irreflexive .  (Contributed by David A. Wheeler, 1-Dec-2019.) $)
  wirreflexive $a wff R Irreflexive A $.

  ${
    $d A x $.  $d R x $.
    $( Define irreflexive relation; relation ` R ` is irreflexive over the set
       ` A ` iff ` A. x e. A -. x R x ` .  Note that a relation can be neither
       reflexive nor irreflexive.  (Contributed by David A. Wheeler,
       1-Dec-2019.) $)
    df-irreflexive $a |- ( R Irreflexive A <->
      ( R C_ ( A X. A ) /\ A. x e. A -. x R x ) ) $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Algebra helpers
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  This is an experimental approach to make it clearer (and easier) to do basic
  algebra in set.mm.

  These little theorems support basic algebra on equations at a slightly higher
  conceptual level.  Instead of always having to "build up" equivalent
  expressions for one side of an equation, these theorems allow you to directly
  manipulate an equality.  These higher-level steps lead to easier to
  understand proofs when they can be used, as well as proofs that are slightly
  shorter (when measured in steps).

  There are disadvantages.  In particular, this approach requires many theorems
  (for many permutations to provide all of the operations).  It can also only
  handle certain cases; more complex approaches must still be approached by
  "building up" equalities as is done today.

  However, I expect that we can create enough theorems to make it worth doing.
  I'm trying this out to see if this is helpful and if the number of
  permutations is manageable.

  To commute LHS for addition, use ~ addcomli .  We might want to switch to a
  naming convention like ~ addcomli .

$)

  ${
    mvlraddi.1 $e |- A e. CC $.
    mvlraddi.2 $e |- B e. CC $.
    mvlraddi.3 $e |- ( A + B ) = C $.
    $( Move the right term in a sum on the LHS to the RHS. (Contributed by
       David A. Wheeler, 11-Oct-2018.) $)
    mvlraddi $p |- A = ( C - B ) $=
      ( caddc co cmin pncan3oi oveq1i eqtr3i ) ABGHZBIHACBIHABDEJMCBIFKL $.
  $}

  ${
    assraddsubi.1 $e |- B e. CC $.
    assraddsubi.2 $e |- C e. CC $.
    assraddsubi.3 $e |- D e. CC $.
    assraddsubi.4 $e |- A = ( ( B + C ) - D ) $.
    $( Associate RHS addition-subtraction.  (Contributed by David A. Wheeler,
       11-Oct-2018.) $)
    assraddsubi $p |- A = ( B + ( C - D ) ) $=
      ( caddc co cmin addsubassi eqtri ) ABCIJDKJBCDKJIJHBCDEFGLM $.
  $}

  ${
    joinlmuladdmuli.1 $e |- A e. CC $.
    joinlmuladdmuli.2 $e |- B e. CC $.
    joinlmuladdmuli.3 $e |- C e. CC $.
    joinlmuladdmuli.4 $e |- ( ( A x. B ) + ( C x. B ) ) = D $.
    $( Join AB+CB into (A+C) on LHS. (Contributed by David A. Wheeler,
       26-Oct-2019.) $)
    joinlmuladdmuli $p |- ( ( A + C ) x. B ) = D $=
      ( caddc co cmul wceq wtru cc wcel a1i joinlmuladdmuld mptru ) ACIJBKJDLMA
      BCDANOMEPBNOMFPCNOMGPABKJCBKJIJDLMHPQR $.
  $}

  ${
    joinlmulsubmuld.1 $e |- ( ph -> A e. CC ) $.
    joinlmulsubmuld.2 $e |- ( ph -> B e. CC ) $.
    joinlmulsubmuld.3 $e |- ( ph -> C e. CC ) $.
    joinlmulsubmuld.4 $e |- ( ph -> ( ( A x. B ) - ( C x. B ) ) = D ) $.
    $( Join AB-CB into (A-C) on LHS. (Contributed by David A. Wheeler,
       15-Oct-2018.) $)
    joinlmulsubmuld $p |- ( ph -> ( ( A - C ) x. B ) = D ) $=
      ( cmin co cmul subdird eqtrd ) ABDJKCLKBCLKDCLKJKEABDCFHGMIN $.
  $}

  ${
    joinlmulsubmuli.1 $e |- A e. CC $.
    joinlmulsubmuli.2 $e |- B e. CC $.
    joinlmulsubmuli.3 $e |- C e. CC $.
    joinlmulsubmuli.4 $e |- ( ( A x. B ) - ( C x. B ) ) = D $.
    $( Join AB-CB into (A-C) on LHS. (Contributed by David A. Wheeler,
       11-Oct-2018.) $)
    joinlmulsubmuli $p |- ( ( A - C ) x. B ) = D $=
      ( cmin co cmul subdiri eqtri ) ACIJBKJABKJCBKJIJDACBEGFLHM $.
  $}

  ${
    mvlrmuld.1 $e |- ( ph -> A e. CC ) $.
    mvlrmuld.2 $e |- ( ph -> B e. CC ) $.
    mvlrmuld.3 $e |- ( ph -> B =/= 0 ) $.
    mvlrmuld.4 $e |- ( ph -> ( A x. B ) = C ) $.
    $( Move the right term in a product on the LHS to the RHS, deduction form.
       (Contributed by David A. Wheeler, 11-Oct-2018.) $)
    mvlrmuld $p |- ( ph -> A = ( C / B ) ) $=
      ( cmul co cdiv divcan4d oveq1d eqtr3d ) ABCIJZCKJBDCKJABCEFGLAODCKHMN $.
  $}

  ${
    mvlrmuli.1 $e |- A e. CC $.
    mvlrmuli.2 $e |- B e. CC $.
    mvlrmuli.3 $e |- B =/= 0 $.
    mvlrmuli.4 $e |- ( A x. B ) = C $.
    $( Move the right term in a product on the LHS to the RHS, inference form.
       (Contributed by David A. Wheeler, 11-Oct-2018.) $)
    mvlrmuli $p |- A = ( C / B ) $=
      ( cmul co cdiv divcan4i oveq1i eqtr3i ) ABHIZBJIACBJIABDEFKNCBJGLM $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Algebra helper examples
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  Examples using the algebra helpers.

$)

  ${
    i2linesi.1 $e |- A e. CC $.
    i2linesi.2 $e |- B e. CC $.
    i2linesi.3 $e |- C e. CC $.
    i2linesi.4 $e |- D e. CC $.
    i2linesi.5 $e |- X e. CC $.
    i2linesi.6 $e |- Y = ( ( A x. X ) + B ) $.
    i2linesi.7 $e |- Y = ( ( C x. X ) + D ) $.
    i2linesi.8 $e |- ( A - C ) =/= 0 $.
    $( Solve for the intersection of two lines expressed in Y = MX+B form (note
       that the lines cannot be vertical).  Here we use inference form.  We
       just solve for X, since Y can be trivially found by using X. This is an
       example of how to use the algebra helpers.  Notice that because this
       proof uses algebra helpers, the main steps of the proof are higher level
       and easier to follow by a human reader.  (Contributed by David A.
       Wheeler, 11-Oct-2018.) $)
    i2linesi $p |- X = ( ( D - B ) / ( A - C ) ) $=
      ( cmin co subcli cmul mulcli caddc mvlraddi assraddsubi mvrladdi mvllmuli
      eqtr3i joinlmulsubmuli ) ACOPEDBOPZACGIQKNAECUGGKIAERPZCERPZUGCEIKSZDBJHQ
      UHUIDBUJJHUHBUIDTPZAEGKSHFUHBTPUKLMUEUAUBUCUFUD $.
  $}

  ${
    i2linesd.1 $e |- ( ph -> A e. CC ) $.
    i2linesd.2 $e |- ( ph -> B e. CC ) $.
    i2linesd.3 $e |- ( ph -> C e. CC ) $.
    i2linesd.4 $e |- ( ph -> D e. CC ) $.
    i2linesd.5 $e |- ( ph -> X e. CC ) $.
    i2linesd.6 $e |- ( ph -> Y = ( ( A x. X ) + B ) ) $.
    i2linesd.7 $e |- ( ph -> Y = ( ( C x. X ) + D ) ) $.
    i2linesd.8 $e |- ( ph -> ( A - C ) =/= 0 ) $.
    $( Solve for the intersection of two lines expressed in Y = MX+B form (note
       that the lines cannot be vertical).  Here we use deduction form.  We
       just solve for X, since Y can be trivially found by using X. This is an
       example of how to use the algebra helpers.  Notice that because this
       proof uses algebra helpers, the main steps of the proof are higher level
       and easier to follow by a human reader.  (Contributed by David A.
       Wheeler, 15-Oct-2018.) $)
    i2linesd $p |- ( ph -> X = ( ( D - B ) / ( A - C ) ) ) $=
      ( cmin co subcld cmul mulcld caddc mvlraddd assraddsubd mvrladdd mvllmuld
      eqtr3d joinlmulsubmuld ) ABDPQFECPQZABDHJRLOABFDUHHLJABFSQZDFSQZUHADFJLTZ
      AECKIRAUIUJECUKKIAUICUJEUAQZABFHLTIAGUICUAQULMNUFUBUCUDUGUE $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Formal methods "surprises"
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  Prove that some formal expressions using classical logic have meanings that
  might not be obvious to some lay readers.  I find these are common mistakes
  and are worth pointing out to new people.  In particular we prove
  ~ alimp-surprise , ~ empty-surprise , and ~ eximp-surprise .

$)

  ${
    alimp-surprise.1 $e |- -. E. x ph $.
    $( Demonstrate that when using "for all" and material implication the
       consequent can be both always true and always false if there is no case
       where the antecedent is true.

       Those inexperienced with formal notations of classical logic can be
       surprised with what "for all" and material implication do together when
       the implication's antecedent is never true.  This can happen, for
       example, when the antecedent is set membership but the set is the empty
       set (e.g., ` x e. M ` and ` M = (/) ` ).

       This is perhaps best explained using an example.  The sentence "All
       Martians are green" would typically be represented formally using the
       expression ` A. x ( ph -> ps ) ` .  In this expression ` ph ` is true
       iff ` x ` is a Martian and ` ps ` is true iff ` x ` is green.
       Similarly, "All Martians are not green" would typically be represented
       as ` A. x ( ph -> -. ps ) ` .  However, if there are no Martians
       ( ` -. E. x ph ` ), then both of those expressions are _true_.  That is
       surprising to the inexperienced, because the two expressions seem to be
       the opposite of each other.  The reason this occurs is because in
       classical logic the implication ` ( ph -> ps ) ` is equivalent to
       ` -. ph \/ ps ` (as proven in ~ imor ).  When ` ph ` is always false,
       ` -. ph ` is always true, and an _or_ with true is always true.

       Here are a few technical notes.  In this notation, ` ph ` and ` ps ` are
       predicates that return a true or false value and may depend on ` x ` .
       We only say _may_ because it actually doesn't matter for our proof.  In
       Metamath this simply means that we do not require that ` ph ` , ` ps ` ,
       and ` x ` be distinct (so ` x ` can be part of ` ph ` or ` ps ` ).

       In natural language the term "implies" often presumes that the
       antecedent _can_ occur in at one least circumstance _and_ that there is
       some sort of causality.  However, exactly what causality means is
       complex and situation-dependent.  Modern logic typically uses material
       implication instead; this has a rigorous definition, but it is important
       for new users of formal notation to precisely understand it.  There are
       ways to solve this, e.g., expressly stating that the antecedent exists
       (see ~ alimp-no-surprise ) or using the allsome quantifier
       ( ~ df-als ) .

       For other "surprises" for new users of classical logic, see
       ~ empty-surprise and ~ eximp-surprise .  (Contributed by David A.
       Wheeler, 17-Oct-2018.) $)
    alimp-surprise $p |- ( A. x ( ph -> ps ) /\ A. x ( ph -> -. ps ) ) $=
      ( wi wal wn wo imor albii nexr orci mpgbir pm3.2i ) ABEZCFZABGZEZCFZPAGZB
      HZCOUACABIJTBACDKZLMSTQHZCRUCCAQIJTQUBLMN $.
  $}

  $( There is no "surprise" in a for-all with implication if there exists a
     value where the antecedent is true.  This is one way to prevent for-all
     with implication from allowing anything.  For a contrast, see
     ~ alimp-surprise .  The allsome quantifier also counters this problem, see
     ~ df-als .  (Contributed by David A. Wheeler, 27-Oct-2018.) $)
  alimp-no-surprise $p |- -. ( A. x ( ph -> ps ) /\ A. x ( ph -> -. ps )
    /\ E. x ph ) $=
    ( wi wn wa wal wex pm4.82 albii alnex sylbb imnan mpbi 19.26 anbi2ci 3anass
    w3a 3anrot 3bitr2i mtbi ) ABDZABEDZFZCGZACHZFZUBCGZUCCGZUFRZUEUFEZDUGEUEAEZ
    CGUKUDULCABIJACKLUEUFMNUGUFUHUIFZFUFUHUIRUJUEUMUFUBUCCOPUFUHUIQUFUHUISTUA
    $.

  ${
    empty-surprise.1 $e |- -. E. x x e. A $.
    $( Demonstrate that when using restricted "for all" over a class the
       expression can be both always true and always false if the class is
       empty.

       Those inexperienced with formal notations of classical logic can be
       surprised with what restricted "for all" does over an empty set.  It is
       important to note that ` A. x e. A ph ` is simply an abbreviation for
       ` A. x ( x e. A -> ph ) ` (per ~ df-ral ).  Thus, if ` A ` is the empty
       set, this expression is _always_ true regardless of the value of ` ph `
       (see ~ alimp-surprise ).

       If you want the expression ` A. x e. A ph ` to not be vacuously true,
       you need to ensure that set ` A ` is inhabited (e.g., ` E. x e. A ` ).
       (Technical note:  You can also assert that ` A =/= (/) ` ; this is an
       equivalent claim in classical logic as proven in ~ n0 , but in
       intuitionistic logic the statement ` A =/= (/) ` is a weaker claim than
       ` E. x e. A ` .)

       Some materials on logic (particularly those that discuss "syllogisms")
       are based on the much older work by Aristotle, but Aristotle expressly
       excluded empty sets from his system.  Aristotle had a specific goal; he
       was trying to develop a "companion-logic" for science.  He relegates
       fictions like fairy godmothers and mermaids and unicorns to the realms
       of poetry and literature...  This is why he leaves no room for such
       nonexistent entities in his logic."  (Groarke, "Aristotle:  Logic",
       section 7.  (Existential Assumptions), _Internet Encyclopedia of
       Philosophy_, ~ http://www.iep.utm.edu/aris-log/ ).  While this made
       sense for his purposes, it is less flexible than modern (classical)
       logic which _does_ permit empty sets.  If you wish to make claims that
       require a nonempty set, you must expressly include that requirement,
       e.g., by stating ` E. x ph ` .  Examples of proofs that do this include
       ~ barbari , ~ celaront , and ~ cesaro .

       For another "surprise" for new users of classical logic, see
       ~ alimp-surprise and ~ eximp-surprise .  (Contributed by David A.
       Wheeler, 20-Oct-2018.) $)
    empty-surprise $p |- A. x e. A ph $=
      ( wral cv wcel wi wal wn alimp-surprise simpli df-ral mpbir ) ABCEBFCGZAH
      BIZPOAJHBIOABDKLABCMN $.
  $}

  ${
    empty-surprise2.1 $e |- -. E. x x e. A $.
    $( "Prove" that false is true when using a restricted "for all" over the
       empty set, to demonstrate that the expression is always true if the
       value ranges over the empty set.

       Those inexperienced with formal notations of classical logic can be
       surprised with what restricted "for all" does over an empty set.  We
       proved the general case in ~ empty-surprise .  Here we prove an extreme
       example: we "prove" that false is true.  Of course, we actually do no
       such thing (see ~ notfal ); the problem is that restricted "for all"
       works in ways that might seem counterintuitive to the inexperienced when
       given an empty set.  Solutions to this can include requiring that the
       set not be empty or by using the allsome quantifier ~ df-rals .
       (Contributed by David A. Wheeler, 20-Oct-2018.) $)
    empty-surprise2 $p |- A. x e. A F. $=
      ( wfal empty-surprise ) DABCE $.
  $}

  $( Show what implication inside "there exists" really expands to (using
     implication directly inside "there exists" is usually a mistake).

     Those inexperienced with formal notations of classical logic may use
     expressions combining "there exists" with implication.  That is usually a
     mistake, because as proven using ~ imor , such an expression can be
     rewritten using _not_ with _or_ - and that is often not what the author
     intended.  New users of formal notation who use "there exists" with an
     implication should consider if they meant "and" instead of "implies".  A
     stark example is shown in ~ eximp-surprise2 .  See also ~ alimp-surprise
     and ~ empty-surprise .  (Contributed by David A. Wheeler, 17-Oct-2018.) $)
  eximp-surprise $p |- ( E. x ( ph -> ps ) <-> E. x ( -. ph \/ ps ) ) $=
    ( wi wn wo imor exbii ) ABDAEBFCABGH $.

  ${
    eximp-surprise2.1 $e |- E. x -. ph $.
    $( Show that "there exists" with an implication is always true if there
       exists a situation where the antecedent is false.

       Those inexperienced with formal notations of classical logic may use
       expressions combining "there exists" with implication.  This is usually
       a mistake, because that combination does not mean what an inexperienced
       person might think it means.  For example, if there is some object that
       does not meet the precondition ` ph ` , then the expression
       ` E. x ( ph -> ps ) ` as a whole is always true, no matter what ` ps `
       is ( ` ps ` could even be false, ` F. ` ).  New users of formal notation
       who use "there exists" with an implication should consider if they meant
       "and" instead of "implies".  See ~ eximp-surprise , which shows what
       implication really expands to.  See also ~ empty-surprise .
       (Contributed by David A. Wheeler, 18-Oct-2018.) $)
    eximp-surprise2 $p |- E. x ( ph -> ps ) $=
      ( wi wex wn wo orc eximii eximp-surprise mpbir ) ABECFAGZBHZCFMNCDMBIJABC
      KL $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Allsome quantifier
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  These are definitions and proofs involving the "allsome"
  quantifier (aka "all some").

  In informal language, statements like
  "All Martians are green" imply that there is at least one Martian.
  But it's easy to mistranslate informal language into formal notations
  because similar statements like ` A. x ph -> ps ` do _not_
  imply that ` ph ` is ever true, leading to vacuous truths.
  See ~ alimp-surprise and ~ empty-surprise as examples of the problem.
  Some systems include a mechanism to counter this, e.g., PVS allows
  types to be appended with "+" to declare that they are nonempty.
  This section presents a different solution to the same problem.

  The "allsome" quantifier expressly includes the notion of both
  "all" and "there exists at least one" (aka some), and is defined
  to make it easier to more directly express both notions.
  The hope is that if a quantifier more directly expresses this concept,
  it will be used instead and reduce the risk of creating formal expressions
  that look okay but in fact are mistranslations.
  The term "allsome" was chosen because it's short, easy to say, and
  clearly hints at the two concepts it combines.

  I do not expect this to be used much in Metamath, because in Metamath
  there's a general policy of avoiding the use of new definitions
  unless there are very strong reasons to do so.  Instead, my goal is to
  rigorously define this quantifier and demonstrate a few
  basic properties of it.

  The syntax allows two forms that look like they would be problematic,
  but they are fine.  When applied to a top-level implication we allow
  ` AE x ( ph -> ps ) ` , and when restricted (applied to a class) we allow
  ` AE x e. A ( ph -> ps ) ` .
  The first symbol after the setvar variable must
  always be ` e. ` if it is the form applied to a class, and since
  ` e. ` cannot begin a wff, it is unambiguous.
  The ` -> ` looks like it would be a problem because ` ph ` or ` ps `
  might include implications, but any implication arrow
  ` -> ` within any wff must be surrounded by parentheses, so only the
  implication arrow of ` AE ` can follow the wff.
  The implication syntax would work fine without the parentheses, but
  I added the parentheses because it makes things clearer inside
  larger complex expressions, and it's also more consistent with
  the rest of the syntax.

  Naming: "als" is allsome.  The form restricted to a class is prefixed with
  "r", following the way set.mm names the restricted quantifiers it is built
  from: ` A. ` gives ~ df-ral and ` E. ` gives ~ df-rex , so ~ df-als (the
  general form) gives ~ df-rals (the restricted form).

  Earlier versions of this material differed, so old references may not match.
  They wrote the quantifier as an "inverted A" followed by an exclamation
  point, and they named the general form df-alsi and the restricted form
  df-alsc.  The symbol is now an "inverted A" followed by a "backwards E",
  which more readers can correctly guess without being taught it.  The
  restricted definition also changed, and the older one was a mistake; see
  ~ df-rals for what was wrong with it.

  Soundness of the two definitions below.  Definitions are required to be
  eliminable and conservative (see the section comment for ~ df-bi ).  Both
  ~ df-als and ~ df-rals meet these requirements directly, and so neither
  needs a justification theorem.

  Each is stated as a biconditional whose left side is a new syntax construct
  ( ~ wals or ~ wrals ) applied to distinct metavariables, and whose right side
  uses only constructs introduced earlier ( ` A. ` , ` E. ` , ` /\ ` , ` -> ` ,
  and the restricted quantifiers ~ df-ral and ~ df-rex ).  Any occurrence of
  the new construct can therefore be replaced by the right side, which is
  eliminability; conservativity follows, since a proof of a statement not
  mentioning ` AE ` can have every use of the definition replaced in this way.

  Note in particular that every variable occurring on the right side already
  occurs on the left side, so no dummy variable is introduced.  A justification
  theorem is needed only when that fails, that is, when a definition introduces
  a dummy variable and the choice of that variable must be shown not to matter
  (as in ~ eujust for ~ df-eu ), or when the definition cannot use ` <-> `
  because it is defining ` <-> ` itself (as in ~ bijust for ~ df-bi ).  Neither
  case arises here.  The restricted quantifier definitions ~ df-ral and
  ~ df-rex have the same shape as these and likewise need no justification.

  For more, see "The Allsome Quantifier" by David A. Wheeler at
  ~ https://dwheeler.com/essays/allsome.html
  I hope that others will eventually agree that allsome is awesome.

$)

  $c AE $. $( "inverted A" followed by "backwards E" (read: "all some"
    or more briefly "allsome") $)

  $( Extend wff definition to include "all some" applied to a top-level
     implication, which means ` ps ` is true whenever ` ph ` is true, and there
     is at least one ` x ` where ` ph ` is true.  (Contributed by David A.
     Wheeler, 20-Oct-2018.)  (Revised by David A. Wheeler, 12-Jul-2026.) $)
  wals $a wff AE x ( ph -> ps ) $.

  $( Extend wff definition to include "all some" applied to a class, which
     means ` ps ` is true whenever ` ph ` is true for ` x ` in ` A ` , and
     there is at least one ` x ` in ` A ` where ` ph ` is true.  (Contributed
     by David A. Wheeler, 20-Oct-2018.)  (Revised by David A. Wheeler,
     12-Jul-2026.) $)
  wrals $a wff AE x e. A ( ph -> ps ) $.

  $( Define "all some" applied to a top-level implication, which means ` ps `
     is true whenever ` ph ` is true and there is at least one ` x ` where
     ` ph ` is true.  (Contributed by David A. Wheeler, 20-Oct-2018.) $)
  df-als $a |- ( AE x ( ph -> ps ) <-> ( A. x ( ph -> ps ) /\ E. x ph ) ) $.

  $( Define "all some" applied to a class, which means ` ps ` is true whenever
     ` ph ` is true for ` x ` in ` A ` , and there is at least one ` x ` in
     ` A ` where ` ph ` is true.

     An older definition of the "all some" quantifier when scoped to a class,
     named df-alsc and now removed, instead applied a bare formula ` ph ` to
     the members of a class, asserting only
     ` ( A. x e. A ph /\ E. x x e. A ) ` , that is, that the formula held
     throughout ` A ` and that ` A ` had at least one member.  I've now decided
     that that was a mistake.  Its older existence conjunct ` E. x x e. A ` did
     not require any member of ` A ` to satisfy the antecedent, so if the
     formula was itself an implication, that inner implication could still be
     vacuously true, which is precisely what the allsome quantifier exists to
     prevent.  For example, the older definition meant that "among Martians,
     all tall ones are green" could be considered true if there are Martians,
     but no tall Martians.  This version of the definition instead ensures that
     claims of the form "among Martians, all tall ones are green" can only be
     true if all tall Martians are green _and_ that there is at least one tall
     Martian.  (Contributed by David A. Wheeler, 20-Oct-2018.)  (Revised by
     David A. Wheeler, 12-Jul-2026.) $)
  df-rals $a |- ( AE x e. A ( ph -> ps ) <->
      ( A. x e. A ( ph -> ps ) /\ E. x e. A ph ) ) $.

  $( The bounded "all some" form is the general form with the class membership
     folded into the antecedent.  (Contributed by David A. Wheeler,
     22-Oct-2018.)  (Revised by David A. Wheeler, 12-Jul-2026.) $)
  dfrals2 $p |- ( AE x e. A ( ph -> ps ) <->
      AE x ( ( x e. A /\ ph ) -> ps ) ) $=
    ( wi wral wrex wa wcel wal wex wrals wals df-ral impexp albii bitr4i df-rex
    cv anbi12i df-rals df-als 3bitr4i ) ABEZCDFZACDGZHCSDIZAHZBEZCJZUHCKZHABCDL
    UHBCMUEUJUFUKUEUGUDEZCJUJUDCDNUIULCUGABOPQACDRTABCDUAUHBCUBUC $.

  ${
    alsd.1 $e |- ( ph -> A. x ( ps -> ch ) ) $.
    alsd.2 $e |- ( ph -> E. x ps ) $.
    $( Introduction rule:  "all some" holds if the "for all" part holds and the
       antecedent has a witness.  This is the converse of ~ als1d and ~ als2d
       taken together, and is what lets an "all some" statement be proved
       rather than merely taken apart.  (Contributed by David A. Wheeler,
       12-Jul-2026.) $)
    alsd $p |- ( ph -> AE x ( ps -> ch ) ) $=
      ( wi wal wex wals df-als sylanbrc ) ABCGDHBDIBCDJEFBCDKL $.
  $}

  ${
    ralsd.1 $e |- ( ph -> A. x e. A ( ps -> ch ) ) $.
    ralsd.2 $e |- ( ph -> E. x e. A ps ) $.
    $( Introduction rule for "all some" restricted to a class.  This is the
       converse of ~ rals1d and ~ rals2d taken together.  (Contributed by David
       A. Wheeler, 12-Jul-2026.) $)
    ralsd $p |- ( ph -> AE x e. A ( ps -> ch ) ) $=
      ( wi wral wrex wrals df-rals sylanbrc ) ABCHDEIBDEJBCDEKFGBCDELM $.
  $}

  ${
    als1d.1 $e |- ( ph -> AE x ( ps -> ch ) ) $.
    $( Deduction rule:  Given "all some" applied to a top-level inference, you
       can extract the "for all" part.  (Contributed by David A. Wheeler,
       20-Oct-2018.) $)
    als1d $p |- ( ph -> A. x ( ps -> ch ) ) $=
      ( wi wal wex wals wa df-als sylib simpld ) ABCFDGZBDHZABCDINOJEBCDKLM $.
  $}

  ${
    als2d.1 $e |- ( ph -> AE x ( ps -> ch ) ) $.
    $( Deduction rule:  Given "all some" applied to a top-level inference, you
       can extract the "exists" part.  (Contributed by David A. Wheeler,
       20-Oct-2018.) $)
    als2d $p |- ( ph -> E. x ps ) $=
      ( wi wal wex wals wa df-als sylib simprd ) ABCFDGZBDHZABCDINOJEBCDKLM $.
  $}

  ${
    rals1d.1 $e |- ( ph -> AE x e. A ( ps -> ch ) ) $.
    $( Deduction rule:  Given "all some" applied to a class, you can extract
       the "for all" part.  (Contributed by David A. Wheeler, 20-Oct-2018.)
       (Revised by David A. Wheeler, 12-Jul-2026.) $)
    rals1d $p |- ( ph -> A. x e. A ( ps -> ch ) ) $=
      ( wi wral wrex wrals wa df-rals sylib simpld ) ABCGDEHZBDEIZABCDEJOPKFBCD
      ELMN $.
  $}

  ${
    rals2d.1 $e |- ( ph -> AE x e. A ( ps -> ch ) ) $.
    $( Deduction rule:  Given "all some" applied to a class, you can extract
       the "there exists" part.  Note that the witness must satisfy the
       antecedent ` ps ` , not merely be a member of ` A ` .  (Contributed by
       David A. Wheeler, 20-Oct-2018.)  (Revised by David A. Wheeler,
       12-Jul-2026.) $)
    rals2d $p |- ( ph -> E. x e. A ps ) $=
      ( wi wral wrex wrals wa df-rals sylib simprd ) ABCGDEHZBDEIZABCDEJOPKFBCD
      ELMN $.
  $}

  ${
    $d A x $.
    ralsn0d.1 $e |- ( ph -> AE x e. A ( ps -> ch ) ) $.
    $( Deduction rule:  Given "all some" applied to a class, the class is not
       the empty set.  (Contributed by David A. Wheeler, 23-Oct-2018.)
       (Revised by David A. Wheeler, 12-Jul-2026.) $)
    ralsn0d $p |- ( ph -> A =/= (/) ) $=
      ( wrex c0 wne rals2d rexn0 syl ) ABDEGEHIABCDEFJBDEKL $.
  $}

  $( The consequent of an "all some" is witnessed: if ` ps ` holds of every
     ` x ` satisfying ` ph ` , and some ` x ` satisfies ` ph ` , then some
     ` x ` satisfies ` ps ` .  This is the positive counterpart of
     ~ als-no-surprise , and it is the property that ordinary "for all" with
     implication lacks: from ` A. x ( ph -> ps ) ` alone nothing whatever
     follows about ` ps ` , as ~ alimp-surprise shows.  It is the reason the
     allsome quantifier says what a speaker of "all Martians are green" usually
     means.  (Contributed by David A. Wheeler, 12-Jul-2026.) $)
  alsex $p |- ( AE x ( ph -> ps ) -> E. x ps ) $=
    ( wals wi wal wex wa df-als exim imp sylbi ) ABCDABECFZACGZHBCGZABCIMNOABCJ
    KL $.

  $( The consequent of an "all some" restricted to a class is witnessed: some
     member of ` A ` satisfying ` ph ` also satisfies ` ps ` .  Restricted
     counterpart of ~ alsex .  (Contributed by David A. Wheeler,
     12-Jul-2026.) $)
  ralsex $p |- ( AE x e. A ( ph -> ps ) -> E. x e. A ps ) $=
    ( wrals wi wral wrex wa df-rals rexim imp sylbi ) ABCDEABFCDGZACDHZIBCDHZAB
    CDJNOPABCDKLM $.

  ${
    alsbii.1 $e |- ( ph <-> ch ) $.
    alsbii.2 $e |- ( ps <-> th ) $.
    $( Congruence: equivalents may be substituted inside an "all some".
       (Contributed by David A. Wheeler, 12-Jul-2026.) $)
    alsbii $p |- ( AE x ( ph -> ps ) <-> AE x ( ch -> th ) ) $=
      ( wi wal wex wa wals imbi12i albii exbii anbi12i df-als 3bitr4i ) ABHZEIZ
      AEJZKCDHZEIZCEJZKABELCDELTUCUAUDSUBEACBDFGMNACEFOPABEQCDEQR $.
  $}

  ${
    ralsbii.1 $e |- ( ph <-> ch ) $.
    ralsbii.2 $e |- ( ps <-> th ) $.
    $( Congruence for "all some" restricted to a class.  (Contributed by David
       A. Wheeler, 12-Jul-2026.) $)
    ralsbii $p |- ( AE x e. A ( ph -> ps ) <-> AE x e. A ( ch -> th ) ) $=
      ( wi wral wrex wa wrals imbi12i ralbii rexbii anbi12i df-rals 3bitr4i ) A
      BIZEFJZAEFKZLCDIZEFJZCEFKZLABEFMCDEFMUAUDUBUETUCEFACBDGHNOACEFGPQABEFRCDE
      FRS $.
  $}

  ${
    alsbid.1 $e |- F/ x ph $.
    alsbid.2 $e |- ( ph -> ( ps <-> th ) ) $.
    alsbid.3 $e |- ( ph -> ( ch <-> ta ) ) $.
    $( Deduction form of ~ alsbii .  (Contributed by David A. Wheeler,
       12-Jul-2026.) $)
    alsbid $p |- ( ph -> ( AE x ( ps -> ch ) <-> AE x ( th -> ta ) ) ) $=
      ( wi wal wex wa wals imbi12d albid exbid anbi12d df-als 3bitr4g ) ABCJZFK
      ZBFLZMDEJZFKZDFLZMBCFNDEFNAUBUEUCUFAUAUDFGABDCEHIOPABDFGHQRBCFSDEFST $.
  $}

  ${
    nfals.1 $e |- F/ x ph $.
    nfals.2 $e |- F/ x ps $.
    $( Bound-variable hypothesis builder for "all some".  (Contributed by David
       A. Wheeler, 12-Jul-2026.) $)
    nfals $p |- F/ x AE y ( ph -> ps ) $=
      ( wals wi wal wex wa df-als nfim nfal nfex nfan nfxfr ) ABDGABHZDIZADJZKC
      ABDLSTCRCDABCEFMNACDEOPQ $.
  $}

  ${
    $d x y $.
    nfrals.1 $e |- F/_ x A $.
    nfrals.2 $e |- F/ x ph $.
    nfrals.3 $e |- F/ x ps $.
    $( Bound-variable hypothesis builder for "all some" restricted to a class.
       (Contributed by David A. Wheeler, 12-Jul-2026.) $)
    nfrals $p |- F/ x AE y e. A ( ph -> ps ) $=
      ( wrals wi wral wrex wa df-rals nfim nfralw nfrexw nfan nfxfr ) ABDEIABJZ
      DEKZADELZMCABDENUAUBCTCDEFABCGHOPACDEFGQRS $.
  $}

  ${
    $d x y $.  $d x ch $.  $d x th $.  $d y ph $.  $d y ps $.
    cbvals.1 $e |- ( x = y -> ( ph <-> ch ) ) $.
    cbvals.2 $e |- ( x = y -> ( ps <-> th ) ) $.
    $( Rule used to change bound variables, using implicit substitution.
       (Contributed by David A. Wheeler, 12-Jul-2026.) $)
    cbvals $p |- ( AE x ( ph -> ps ) <-> AE y ( ch -> th ) ) $=
      ( wi wal wex wa wals weq imbi12d cbvalvw cbvexvw anbi12i df-als 3bitr4i )
      ABIZEJZAEKZLCDIZFJZCFKZLABEMCDFMUBUEUCUFUAUDEFEFNACBDGHOPACEFGQRABESCDFST
      $.
  $}

  $( Demonstrate that there is never a "surprise" when using the allsome
     quantifier, that is, it is never possible for the consequent to be both
     always true and always false.  This uses the definition of ~ df-als ; the
     proof itself builds on ~ alimp-no-surprise .  For a contrast, see
     ~ alimp-surprise .  (Contributed by David A. Wheeler, 27-Oct-2018.) $)
  als-no-surprise $p |- -. ( AE x ( ph -> ps ) /\ AE x ( ph -> -. ps ) ) $=
    ( wals wn wa wal wex w3a alimp-no-surprise anbi12i anandi3r 3ancomb 3bitr2i
    wi df-als mtbir ) ABCDZABEZCDZFZABOCGZASOCGZACHZIZABCJUAUBUDFZUCUDFZFUBUDUC
    IUERUFTUGABCPASCPKUBUDUCLUBUDUCMNQ $.

  $( Demonstrate that there is never a "surprise" when using the allsome
     quantifier restricted to a class, that is, it is never possible for the
     consequent to be both always true and always false of the members of ` A `
     that satisfy the antecedent.  This is the restricted counterpart of
     ~ als-no-surprise , and follows from it by ~ dfrals2 .  Note that this
     needs no assumption that ` A ` is nonempty, because allsome requires a
     member of ` A ` satisfying ` ph ` , and that member would have to satisfy
     both ` ps ` and ` -. ps ` .  The ordinary restricted "for all" requires no
     such member and can be vacuously true, as shown in ~ empty-surprise2 ;
     that is the point of allsome.  (Contributed by David A. Wheeler,
     12-Jul-2026.) $)
  rals-no-surprise $p |- -. ( AE x e. A ( ph -> ps ) /\
      AE x e. A ( ph -> -. ps ) ) $=
    ( wrals wn wa cv wcel wals als-no-surprise dfrals2 anbi12i mtbir ) ABCDEZAB
    FZCDEZGCHDIAGZBCJZRPCJZGRBCKOSQTABCDLAPCDLMN $.

  $( If the universal part of a restricted "all some" statement holds, then the
     statement reduces to the existence of a member of ` A ` satisfying its
     antecedent.  This is the restricted counterpart of ~ ralals .
     (Contributed by Peter Mazsa and David A. Wheeler, 20-Jul-2026.) $)
  ralrals $p |- ( A. x e. A ( ph -> ps ) ->
      ( AE x e. A ( ph -> ps ) <-> E. x e. A ph ) ) $=
    ( wrals wi wral wrex wa df-rals ibar bicomd bitrid ) ABCDEABFCDGZACDHZIZNOA
    BCDJNOPNOKLM $.

  $( If a member of ` A ` satisfying the antecedent exists, then a restricted
     "all some" statement reduces to its universal part.  This is the
     restricted counterpart of ~ rexals .  (Contributed by Peter Mazsa and
     David A. Wheeler, 20-Jul-2026.) $)
  rexrals $p |- ( E. x e. A ph ->
      ( AE x e. A ( ph -> ps ) <-> A. x e. A ( ph -> ps ) ) ) $=
    ( wrals wi wral wrex wa df-rals iba bicomd bitrid ) ABCDEABFCDGZACDHZIZONAB
    CDJONPONKLM $.

  $( An "all some" statement conjoined with the claim that at most one ` x `
     satisfies its antecedent is equivalent to the universal part conjoined
     with the claim that exactly one ` x ` satisfies the antecedent.  The "all
     some" quantifier supplies the existence of such an ` x ` and ` E* x ph `
     supplies the at-most-one part, so together they yield ` E! x ph ` .
     (Contributed by Peter Mazsa and David A. Wheeler, 20-Jul-2026.) $)
  alsanmo $p |- ( ( AE x ( ph -> ps ) /\ E* x ph ) <->
      ( A. x ( ph -> ps ) /\ E! x ph ) ) $=
    ( wals wmo wa wi wal wex weu df-als anbi1i anass df-eu bicomi anbi2i 3bitri
    ) ABCDZACEZFABGCHZACIZFZSFTUASFZFTACJZFRUBSABCKLTUASMUCUDTUDUCACNOPQ $.

  $( An "all some" statement restricted to a class, conjoined with the claim
     that at most one ` x ` in ` A ` satisfies its antecedent, is equivalent to
     the universal part conjoined with the claim that exactly one ` x ` in
     ` A ` satisfies the antecedent.  This is the restricted counterpart of
     ~ alsanmo .  (Contributed by Peter Mazsa and David A. Wheeler,
     20-Jul-2026.) $)
  ralsanmo $p |- ( ( AE x e. A ( ph -> ps ) /\ E* x e. A ph ) <->
      ( A. x e. A ( ph -> ps ) /\ E! x e. A ph ) ) $=
    ( wrals wrmo wa wi wral wrex wreu df-rals anbi1i anass bicomi anbi2i 3bitri
    reu5 ) ABCDEZACDFZGABHCDIZACDJZGZTGUAUBTGZGUAACDKZGSUCTABCDLMUAUBTNUDUEUAUE
    UDACDROPQ $.

  ${
    $d x A $.
    $( The general "all some" quantifier with class membership as its
       antecedent holds if and only if ` ph ` holds for every ` x ` in ` A `
       and some ` x ` in ` A ` satisfies ` ph ` .  (Contributed by Peter Mazsa,
       27-Nov-2018.)  (Revised by David A. Wheeler, 15-Jul-2026.) $)
    alsralrex $p |- ( AE x ( x e. A -> ph ) <->
        ( A. x e. A ph /\ E. x e. A ph ) ) $=
      ( cv wcel wals wi wal wex wa wral wrex df-als df-ral bicomi anbi1i c0 wne
      n0 bitri biimpri r19.2z sylan expcom rexn0 biimpi syl a1i impbid pm5.32i
      ) BDCEZABFUKAGBHZUKBIZJZABCKZABCLZJZUKABMUNUOUMJUQULUOUMUOULABCNOPUOUMUPU
      OUMUPUMUOUPUMCQRZUOUPURUMBCSZUAABCUBUCUDUPUMGUOUPURUMABCUEURUMUSUFUGUHUIU
      JTT $.
  $}

  ${
    $d x A $.
    $( The general "all some" quantifier with class membership as its
       antecedent holds if and only if ` ph ` holds for every ` x ` in ` A `
       and ` A ` is not empty.  (Contributed by Peter Mazsa, 28-Nov-2018.)
       (Revised by David A. Wheeler, 15-Jul-2026.) $)
    alsraln0 $p |- ( AE x ( x e. A -> ph ) <->
        ( A. x e. A ph /\ A =/= (/) ) ) $=
      ( cv wcel wals wral wa c0 wne alsralrex wi rexn0 a1i r19.2z expcom impbid
      wrex pm5.32i bitri ) BDCEABFABCGZABCRZHUACIJZHABCKUAUBUCUAUBUCUBUCLUAABCM
      NUCUAUBABCOPQST $.
  $}

  ${
    $d x A $.
    $( If ` ph ` holds for every ` x ` in ` A ` , then the general "all some"
       quantifier with class membership as its antecedent reduces to the
       assertion that some ` x ` in ` A ` satisfies ` ph ` .  See ~ ralrals for
       the restricted counterpart.  (Contributed by Peter Mazsa, 19-Dec-2018.)
       (Revised by David A. Wheeler, 15-Jul-2026.) $)
    ralals $p |- ( A. x e. A ph ->
        ( AE x ( x e. A -> ph ) <-> E. x e. A ph ) ) $=
      ( cv wcel wals wral wrex wa alsralrex ibar bicomd bitrid ) BDCEABFABCGZAB
      CHZIZNOABCJNOPNOKLM $.
  $}

  ${
    $d x A $.
    $( If some ` x ` in ` A ` satisfies ` ph ` , then the general "all some"
       quantifier with class membership as its antecedent reduces to the
       assertion that ` ph ` holds for every ` x ` in ` A ` .  See ~ rexrals
       for the restricted counterpart.  (Contributed by Peter Mazsa,
       19-Dec-2018.)  (Revised by David A. Wheeler, 15-Jul-2026.) $)
    rexals $p |- ( E. x e. A ph ->
        ( AE x ( x e. A -> ph ) <-> A. x e. A ph ) ) $=
      ( cv wcel wals wral wrex wa alsralrex iba bicomd bitrid ) BDCEABFABCGZABC
      HZIZONABCJONPONKLM $.
  $}

  ${
    $d x A $.
    $( If ` A ` is not empty, then the general "all some" quantifier with class
       membership as its antecedent reduces to the assertion that ` ph ` holds
       for every ` x ` in ` A ` .  (Contributed by Peter Mazsa, 19-Dec-2018.)
       (Revised by David A. Wheeler, 15-Jul-2026.) $)
    n0als $p |- ( A =/= (/) ->
        ( AE x ( x e. A -> ph ) <-> A. x e. A ph ) ) $=
      ( cv wcel wals wral c0 wne alsraln0 rbaib ) BDCEABFABCGCHIABCJK $.
  $}

  ${
    $d x A $.  $d x y B $.
    $( Nested general "all some" quantifiers with class membership as their
       antecedents: ` ph ` holds for every ` x ` in ` A ` and every ` y ` in
       ` B ` , and both ` A ` and ` B ` are not empty.  (Contributed by Peter
       Mazsa, 28-May-2019.)  (Revised by David A. Wheeler, 15-Jul-2026.) $)
    2alsraln0 $p |- ( AE x ( x e. A -> AE y ( y e. B -> ph ) ) <->
        ( A. x e. A A. y e. B ph /\ ( A =/= (/) /\ B =/= (/) ) ) ) $=
      ( cv wcel wals wral c0 wne wa biid alsraln0 r19.27zv pm5.32ri anass ancom
      alsbii bitri anbi2i ) BFDGZCFEGACHZBHUBACEIZEJKZLZBHZUDBDIZDJKZUELZLZUBUC
      UBUFBUBMACENSUGUFBDIZUILZUKUFBDNUMUHUELZUILZUKUIULUNUDUEBDOPUOUHUEUILZLUK
      UHUEUIQUPUJUHUEUIRUATTTT $.
  $}

  ${
    $d x y A $.
    $( Nested general "all some" quantifiers with class membership as their
       antecedents, for the same class ` A ` : ` ph ` holds for every ` x ` and
       every ` y ` in ` A ` , and ` A ` is not empty.  (Contributed by Peter
       Mazsa, 28-May-2019.)  (Revised by David A. Wheeler, 15-Jul-2026.) $)
    2alsraln0id $p |- ( AE x ( x e. A -> AE y ( y e. A -> ph ) ) <->
        ( A. x e. A A. y e. A ph /\ A =/= (/) ) ) $=
      ( cv wcel wals wral c0 wne wa 2alsraln0 pm4.24 bicomi anbi2i bitri ) BEDF
      CEDFACGBGACDHBDHZDIJZRKZKQRKABCDDLSRQRSRMNOP $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Allsome one quantifier
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  These are definitions and proofs involving the "allsome one" quantifier,
  which extends the "allsome" quantifier of the previous section in the same
  way that ` E! ` ( ~ df-eu ) extends ` E. ` .

  Some systems extend "there exists" by appending a character to it.  If a
  system provides such an extension, it should provide it for allsome as well:
  append the same character, let it modify allsome's existence conjunct, and
  change nothing else.  Appending "!" gives "allsome one", so
  ` AE! x ( ph -> ps ) ` means that ` ps ` is true whenever ` ph ` is true and
  that exactly one ` x ` satisfies ` ph ` .

  This is what the English word "the" usually does.  "The king is hungry"
  claims that a king exists, that there is only one, and that he is hungry, and
  the form ` AE! x ( ph -> ps ) ` claims exactly that kind of statement
  (specifically when ` ph ` means ` x ` is a king and ` ps ` means ` x ` is
  hungry).  English says all of that in a single phrase, and the first two have
  a dedicated word ("the") for the construct.  Many other languages have their
  own dedicated way of saying this.  Languages reserve that kind of compression
  for what their speakers need constantly, which is a good reason for a formal
  notation to be able to say it just as directly, rather than spelling it out
  afresh as a conjunction of two quantified formulas every time it comes up.
  Russell analyzed such _definite descriptions_ with this apparatus in "On
  Denoting", where his example of a phrase that appears to refer to someone but
  in fact denotes no one at all is "the present King of France", item (1) of
  [Russell1905] p. 479, France being a republic that has no king.  Write "the
  king is hungry" as ` A. x ( ph -> ps ) ` instead and only the last of those
  three claims survives.  The existence claim is silently gone, since that
  formula is vacuously true when there is no king, and the uniqueness claim is
  silently gone as well, since that formula holds just the same when there are
  five kings.  Russell reached the opposite verdict for the same example,
  remarking that every proposition of the form "the present King of France ..."
  is false, [Russell1905] p. 482.  The reason to care is the reason that
  motivates allsome, only more so; see ~ alimp-surprise and ~ empty-surprise .

  Note that this is not merely a way of writing ` E! x ( ph /\ ps ) ` .
  Reading ` ph ` as "is a king" and ` ps ` as "is hungry",
  ` E! x ( ph /\ ps ) ` says that there is exactly one hungry king, whereas
  ` AE! x ( ph -> ps ) ` says that there is exactly one king and that he is
  hungry.  The first is true in a region with five kings exactly one of whom
  is hungry; the second is false there.  Uniqueness attaches to the
  antecedent, not to the conjunction.  See ~ dfalseu2 for the exact
  relationship between the two and ~ alseueu for the one direction that does
  hold.

  Naming: "alseu" is allsome ("als", as in ~ df-als ) extended with "exactly
  one" ("eu", as in ~ df-eu ).  The form restricted to a class is prefixed
  with "r", following ~ df-rals and ~ df-reu , giving ~ df-ralseu .

  Soundness: ~ df-alseu and ~ df-ralseu are eliminable and conservative
  directly, so neither needs a justification theorem.  Definitions are required
  to be eliminable and conservative; see the section comment for ~ df-bi .
  Each is a biconditional whose left side is a new syntax construct
  ( ~ walseu or ~ wralseu ) applied to distinct metavariables, and whose right
  side uses only constructs introduced earlier ( ` A. ` , ` E! ` , ` /\ ` ,
  ` -> ` , and the restricted quantifiers ~ df-ral and ~ df-reu ), so any
  occurrence of the new construct can be replaced by the right side, which is
  eliminability.  Conservativity follows, since a proof of a statement not
  mentioning ` AE! ` can have every use of the definition replaced in this way.
  Every variable occurring on the right side already occurs on the left side,
  so no dummy variable is introduced, and introducing a dummy variable whose
  choice must be shown not to matter is the only circumstance here that would
  call for a justification theorem.

  For more, see "The Allsome Quantifier" by David A. Wheeler at
  ~ https://dwheeler.com/essays/allsome.html

$)

  $c AE! $. $( "inverted A" followed by "backwards E" followed by an
    exclamation point (read: "all some one") $)

  $( Extend wff definition to include "all some one" applied to a top-level
     implication, which means ` ps ` is true whenever ` ph ` is true, and
     exactly one ` x ` satisfies ` ph ` .  (Contributed by David A. Wheeler,
     21-Jul-2026.) $)
  walseu $a wff AE! x ( ph -> ps ) $.

  $( Extend wff definition to include "all some one" applied to a class, which
     means ` ps ` is true whenever ` ph ` is true for ` x ` in ` A ` , and
     exactly one ` x ` in ` A ` satisfies ` ph ` .  (Contributed by David A.
     Wheeler, 21-Jul-2026.) $)
  wralseu $a wff AE! x e. A ( ph -> ps ) $.

  $( Define "all some one" applied to a top-level implication, which means
     ` ps ` is true whenever ` ph ` is true and exactly one ` x ` satisfies
     ` ph ` .  (Contributed by David A. Wheeler, 21-Jul-2026.) $)
  df-alseu $a |- ( AE! x ( ph -> ps ) <-> ( A. x ( ph -> ps ) /\ E! x ph ) ) $.

  $( Define "all some one" applied to a class, which means ` ps ` is true
     whenever ` ph ` is true for ` x ` in ` A ` , and exactly one ` x ` in
     ` A ` satisfies ` ph ` .  (Contributed by David A. Wheeler,
     21-Jul-2026.) $)
  df-ralseu $a |- ( AE! x e. A ( ph -> ps ) <->
      ( A. x e. A ( ph -> ps ) /\ E! x e. A ph ) ) $.

  $( The bounded "all some one" form is the general form with the class
     membership folded into the antecedent.  This is the "all some one"
     counterpart of ~ dfrals2 .  (Contributed by David A. Wheeler,
     21-Jul-2026.) $)
  dfralseu2 $p |- ( AE! x e. A ( ph -> ps ) <->
      AE! x ( ( x e. A /\ ph ) -> ps ) ) $=
    ( wi wral wreu wa cv wcel wal weu wralseu walseu df-ral impexp albii bitr4i
    df-reu anbi12i df-ralseu df-alseu 3bitr4i ) ABEZCDFZACDGZHCIDJZAHZBEZCKZUHC
    LZHABCDMUHBCNUEUJUFUKUEUGUDEZCKUJUDCDOUIULCUGABPQRACDSTABCDUAUHBCUBUC $.

  $( "All some one" implies "all some": requiring exactly one witness is
     stronger than requiring at least one.  Any consequence of an allsome
     statement is therefore a consequence of the corresponding "all some one"
     statement, which is how ~ alseu-no-surprise is proved.  (Contributed by
     David A. Wheeler, 21-Jul-2026.) $)
  alseuals $p |- ( AE! x ( ph -> ps ) -> AE x ( ph -> ps ) ) $=
    ( wi wal weu wa wex walseu wals euex anim2i df-alseu df-als 3imtr4i ) ABDCE
    ZACFZGPACHZGABCIABCJQRPACKLABCMABCNO $.

  $( "All some one" restricted to a class implies "all some" restricted to that
     class.  Restricted counterpart of ~ alseuals .  (Contributed by David A.
     Wheeler, 21-Jul-2026.) $)
  ralseurals $p |- ( AE! x e. A ( ph -> ps ) ->
      AE x e. A ( ph -> ps ) ) $=
    ( wi wral wreu wrex wralseu wrals reurex anim2i df-ralseu df-rals 3imtr4i
    wa ) ABECDFZACDGZPQACDHZPABCDIABCDJRSQACDKLABCDMABCDNO $.

  ${
    alseud.1 $e |- ( ph -> A. x ( ps -> ch ) ) $.
    alseud.2 $e |- ( ph -> E! x ps ) $.
    $( Introduction rule:  "all some one" holds if the "for all" part holds and
       the antecedent has exactly one witness.  This is the converse of
       ~ alseu1d and ~ alseu2d taken together.  (Contributed by David A.
       Wheeler, 21-Jul-2026.) $)
    alseud $p |- ( ph -> AE! x ( ps -> ch ) ) $=
      ( wi wal weu walseu df-alseu sylanbrc ) ABCGDHBDIBCDJEFBCDKL $.
  $}

  ${
    ralseud.1 $e |- ( ph -> A. x e. A ( ps -> ch ) ) $.
    ralseud.2 $e |- ( ph -> E! x e. A ps ) $.
    $( Introduction rule for "all some one" restricted to a class.  This is the
       converse of ~ ralseu1d and ~ ralseu2d taken together.  (Contributed by
       David A. Wheeler, 21-Jul-2026.) $)
    ralseud $p |- ( ph -> AE! x e. A ( ps -> ch ) ) $=
      ( wi wral wreu wralseu df-ralseu sylanbrc ) ABCHDEIBDEJBCDEKFGBCDELM $.
  $}

  ${
    alseu1d.1 $e |- ( ph -> AE! x ( ps -> ch ) ) $.
    $( Deduction rule:  Given "all some one" applied to a top-level inference,
       you can extract the "for all" part.  (Contributed by David A. Wheeler,
       21-Jul-2026.) $)
    alseu1d $p |- ( ph -> A. x ( ps -> ch ) ) $=
      ( wi wal weu walseu wa df-alseu sylib simpld ) ABCFDGZBDHZABCDINOJEBCDKLM
      $.
  $}

  ${
    alseu2d.1 $e |- ( ph -> AE! x ( ps -> ch ) ) $.
    $( Deduction rule:  Given "all some one" applied to a top-level inference,
       you can extract the "exactly one" part.  (Contributed by David A.
       Wheeler, 21-Jul-2026.) $)
    alseu2d $p |- ( ph -> E! x ps ) $=
      ( wi wal weu walseu wa df-alseu sylib simprd ) ABCFDGZBDHZABCDINOJEBCDKLM
      $.
  $}

  ${
    ralseu1d.1 $e |- ( ph -> AE! x e. A ( ps -> ch ) ) $.
    $( Deduction rule:  Given "all some one" applied to a class, you can
       extract the "for all" part.  (Contributed by David A. Wheeler,
       21-Jul-2026.) $)
    ralseu1d $p |- ( ph -> A. x e. A ( ps -> ch ) ) $=
      ( wi wral wreu wralseu wa df-ralseu sylib simpld ) ABCGDEHZBDEIZABCDEJOPK
      FBCDELMN $.
  $}

  ${
    ralseu2d.1 $e |- ( ph -> AE! x e. A ( ps -> ch ) ) $.
    $( Deduction rule:  Given "all some one" applied to a class, you can
       extract the "exactly one" part.  Note that the witness must satisfy the
       antecedent ` ps ` , not merely be a member of ` A ` .  (Contributed by
       David A. Wheeler, 21-Jul-2026.) $)
    ralseu2d $p |- ( ph -> E! x e. A ps ) $=
      ( wi wral wreu wralseu wa df-ralseu sylib simprd ) ABCGDEHZBDEIZABCDEJOPK
      FBCDELMN $.
  $}

  ${
    alseubii.1 $e |- ( ph <-> ch ) $.
    alseubii.2 $e |- ( ps <-> th ) $.
    $( Congruence: equivalents may be substituted inside an "all some one".
       This is the "all some one" counterpart of ~ alsbii .  (Contributed by
       David A. Wheeler, 21-Jul-2026.) $)
    alseubii $p |- ( AE! x ( ph -> ps ) <-> AE! x ( ch -> th ) ) $=
      ( wi wal weu wa walseu imbi12i albii eubii anbi12i df-alseu 3bitr4i ) ABH
      ZEIZAEJZKCDHZEIZCEJZKABELCDELTUCUAUDSUBEACBDFGMNACEFOPABEQCDEQR $.
  $}

  ${
    ralseubii.1 $e |- ( ph <-> ch ) $.
    ralseubii.2 $e |- ( ps <-> th ) $.
    $( Congruence for "all some one" restricted to a class.  This is the "all
       some one" counterpart of ~ ralsbii .  (Contributed by David A. Wheeler,
       21-Jul-2026.) $)
    ralseubii $p |- ( AE! x e. A ( ph -> ps ) <->
        AE! x e. A ( ch -> th ) ) $=
      ( wi wral wreu wa wralseu imbi12i ralbii reubii anbi12i df-ralseu 3bitr4i
      ) ABIZEFJZAEFKZLCDIZEFJZCEFKZLABEFMCDEFMUAUDUBUETUCEFACBDGHNOACEFGPQABEFR
      CDEFRS $.
  $}

  ${
    $d x y $.
    nfalseu.1 $e |- F/ x ph $.
    nfalseu.2 $e |- F/ x ps $.
    $( Bound-variable hypothesis builder for "all some one".  This is the "all
       some one" counterpart of ~ nfals .  Unlike ~ nfals it requires ` x ` and
       ` y ` to be disjoint, because the corresponding builder for ` E! ` is
       ~ nfeuw , which requires it; the version without that requirement,
       ~ nfeu , depends on ~ ax-13 and its use is discouraged.  (Contributed by
       David A. Wheeler, 21-Jul-2026.) $)
    nfalseu $p |- F/ x AE! y ( ph -> ps ) $=
      ( walseu wi wal weu wa df-alseu nfim nfal nfeuw nfan nfxfr ) ABDGABHZDIZA
      DJZKCABDLSTCRCDABCEFMNACDEOPQ $.
  $}

  ${
    $d x y $.
    nfralseu.1 $e |- F/_ x A $.
    nfralseu.2 $e |- F/ x ph $.
    nfralseu.3 $e |- F/ x ps $.
    $( Bound-variable hypothesis builder for "all some one" restricted to a
       class.  This is the "all some one" counterpart of ~ nfrals .
       (Contributed by David A. Wheeler, 21-Jul-2026.) $)
    nfralseu $p |- F/ x AE! y e. A ( ph -> ps ) $=
      ( wralseu wi wral wreu wa df-ralseu nfim nfralw nfreuw nfan nfxfr ) ABDEI
      ABJZDEKZADELZMCABDENUAUBCTCDEFABCGHOPACDEFGQRS $.
  $}

  $( An "all some one" statement is equivalent to its universal part conjoined
     with the claim that exactly one ` x ` satisfies both ` ph ` and ` ps ` .
     In other words, given ` A. x ( ph -> ps ) ` , requiring exactly one ` x `
     to satisfy ` ph ` , which is what ~ df-alseu requires, and requiring
     exactly one ` x ` to satisfy ` ( ph /\ ps ) ` come to the same thing.
     Read ` ph ` as "is a king" and ` ps ` as "is hungry": if every king is
     hungry, then "there is exactly one king" and "there is exactly one hungry
     king" say the same thing, so either of them, together with "every king is
     hungry", gives "the king is hungry".

     The universal conjunct is what makes that work, and it cannot be dropped.
     ` E! x ( ph /\ ps ) ` on its own is strictly weaker than
     ` AE! x ( ph -> ps ) ` , since it is satisfied when many things are ` ph `
     and just one of those is ` ps ` , as in a region with five kings exactly
     one of whom is hungry; see ~ alseueu for the one direction that does hold
     without it.  Uniqueness attaches to the antecedent, not to the
     conjunction.  Russell's analysis of a definite description is built the
     same way: its uniqueness clause constrains the description predicate
     alone, while the predication is a separate conjunct.  See his worked
     example of "the father of Charles II was executed", [Russell1905] p. 482.
     (Contributed by David A. Wheeler, 21-Jul-2026.) $)
  dfalseu2 $p |- ( AE! x ( ph -> ps ) <->
      ( A. x ( ph -> ps ) /\ E! x ( ph /\ ps ) ) ) $=
    ( walseu wi wal weu wa df-alseu wb pm4.71 albii eubi sylbi pm5.32i bitri )
    ABCDABEZCFZACGZHRABHZCGZHABCIRSUARATJZCFSUAJQUBCABKLATCMNOP $.

  $( "The ` ph ` is ` ps ` " implies that exactly one thing is both ` ph ` and
     ` ps ` .  This is the half of ~ dfalseu2 that drops the universal
     conjunct; it does not reverse, so ` E! x ( ph /\ ps ) ` cannot be used in
     place of an "all some one" statement.  (Contributed by David A. Wheeler,
     21-Jul-2026.) $)
  alseueu $p |- ( AE! x ( ph -> ps ) -> E! x ( ph /\ ps ) ) $=
    ( walseu wi wal wa weu dfalseu2 simprbi ) ABCDABECFABGCHABCIJ $.

  $( Demonstrate that there is never a "surprise" when using the "all some one"
     quantifier, that is, it is never possible for the consequent to be both
     always true and always false.  This follows from ~ als-no-surprise by
     ~ alseuals .  For a contrast, see ~ alimp-surprise .  (Contributed by
     David A. Wheeler, 21-Jul-2026.) $)
  alseu-no-surprise $p |- -. ( AE! x ( ph -> ps ) /\
      AE! x ( ph -> -. ps ) ) $=
    ( walseu wn wa wals als-no-surprise alseuals anim12i mto ) ABCDZABEZCDZFABC
    GZAMCGZFABCHLONPABCIAMCIJK $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Miscellaneous
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  Miscellaneous proofs.

$)

  $( Prove that 5 - 4 = 1.  (Contributed by David A. Wheeler, 31-Jan-2017.) $)
  5m4e1 $p |- ( 5 - 4 ) = 1 $=
    ( c5 c4 c1 5cn 4cn ax-1cn 4p1e5 subaddrii ) ABCDEFGH $.

  $( Prove that ` 2 + 2 =/= 5 ` .  In George Orwell's "1984", Part One, Chapter
     Seven, the protagonist Winston notes that, "In the end the Party would
     announce that two and two made five, and you would have to believe it."
     ~ http://www.sparknotes.com/lit/1984/section4.rhtml .  More generally, the
     phrase ` 2 + 2 = 5 ` has come to represent an obviously false dogma one
     may be required to believe.  See the Wikipedia article for more about
     this: ~ https://en.wikipedia.org/wiki/2_%2B_2_%3D_5 .  Unsurprisingly, we
     can easily prove that this claim is false.  (Contributed by David A.
     Wheeler, 31-Jan-2017.) $)
  2p2ne5 $p |- ( 2 + 2 ) =/= 5 $=
    ( c2 caddc co c4 c5 2p2e4 4re 4lt5 ltneii eqnetri ) AABCDEFDEGHIJ $.

  $( Resolution rule.  This is the primary inference rule in some automated
     theorem provers such as prover9.  The resolution rule can be traced back
     to Davis and Putnam (1960).  (Contributed by David A. Wheeler,
     9-Feb-2017.) $)
  resolution $p |- ( ( ( ph /\ ps ) \/ ( -. ph /\ ch ) ) -> ( ps \/ ch ) ) $=
    ( wa wn simpr orim12i ) ABDBAEZCDCABFHCFG $.

  $( In classical logic all wffs are testable, that is, it is always true that
     ` ( -. ph \/ -. -. ph ) ` .  This is not necessarily true in
     intuitionistic logic.  In intuitionistic logic, if this statement is true
     for some ` ph ` , then ` ph ` is _testable_.  The proof is trivial because
     it's simply a special case of the law of the excluded middle, which is
     true in classical logic but not necessarily true in intuitionisic logic.
     (Contributed by David A. Wheeler, 5-Dec-2018.) $)
  testable $p |- ( -. ph \/ -. -. ph ) $=
    ( wn exmid ) ABC $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Theorems about algebraic numbers
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d A k n w x y $.  $d B n $.  $d C v $.  $d C w x y $.  $d C x y z $.
    $d N k n v $.  $d N k n w x y $.  $d N k n x y z $.  $d X k $.
    $d k n ph v $.  $d ph w x y $.  $d ph x y z $.
    aacllem.0 $e |- ( ph -> A e. CC ) $.
    aacllem.1 $e |- ( ph -> N e. NN0 ) $.
    aacllem.2 $e |- ( ( ph /\ n e. ( 1 ... N ) ) -> X e. CC ) $.
    aacllem.3 $e |- ( ( ph /\ k e. ( 0 ... N ) /\ n e. ( 1 ... N ) )
                       -> C e. QQ ) $.
    aacllem.4 $e |- ( ( ph /\ k e. ( 0 ... N ) ) ->
                      ( A ^ k ) = sum_ n e. ( 1 ... N ) ( C x. X ) ) $.
    $( Lemma for other theorems about ` AA ` .  (Contributed by Brendan Leahy,
       3-Jan-2020.)  (Revised by Alexander van der Vekens and David A. Wheeler,
       25-Apr-2020.) $)
    aacllem $p |- ( ph -> A e. AA ) $=
      ( wcel cfv cc0 wceq cq co cvv wa vx vw vy vv vz cB cc cv c0p csn cdif cfz
      wrex cmul csu c1 wral cmap cxp caddc cle wbr wn nn0red cn0 syl mpbid cmpt
      wf1 crn ccnfld cfrlm wi cof cgsu wf fmpttd qex ovex elmap sylibr cfn eqid
      cdr ax-mp fzfi mp2an cbs frlmfibas elmapi wfn fzfid fvexd mptex a1i eqidd
      offval2 adantll adantlr adantllr eqtrd mpteq2dva oveq2d an32s syl2anc wss
      wb qsscn cz 0z adantl qcn sylan mulcld 3syl c0ex fnconstg nfcv nfov sumex
      ffn sylan2 cen cun adantr un0 cdom ancoms syl5 wne cexp adantrr ccoe cres
      c0 ex cuz cin cima sumeq2dv cply caa ltp1d peano2nn0 ltnled clinds clindf
      clt cress cvsca 3expa clmod qdrng drngring frlmlmod qrngbas frlmsca qrng0
      crg csca c0g frlm0 islindf4 mp3an12 simpr feqmptd ffvelcdm cmulr cnfldmul
      ressmulr fconstmpt qmulcl snex xpex fsuppmptdm frlmgsum cnfldbas cnfldadd
      frlmvscafval cnfldex zq addlid addrid jca gsumress simplr gsumfsum eqtr3d
      3eqtrd qaddcl fsumcllem eqeltrd nfmpt1 nfmpt eqfnfv2f fveq1d fvmpt2 mpan2
      sylancl sylan9eq fvconst2 eqeq12d ralbidva bitrd imbi1d cdm cnzr islindf3
      drngnzr dmmpti f1eq2 anbi1i bitri wnel con34b df-nel velsn xchbinx imbi1i
      bitr4i ralbii raldifb ralnex 3bitri 3bitr3g clss cmri cuvc cpw clspn cmre
      lssmre cmrc mrclsp clvec islvec mpbir2an cacs simprd frnd sseqtrrdi uvcff
      lssacsex dif0 sseqtrri fveq2i frlmlbs lbssp eqtri pm3.2i lindsind2 mp3an1
      frn clbs ralrimiva ismri2 sylancr biimpar eqeltrid wo mptfi rnfi mreexexd
      mp2b orci rnex elpwi ssdomg mpsyl endomtr f1f1orn uvcendim ensymi domentr
      f1oen chash hashdom hashfz0 hashfz1 breq12d bitr3id imbitrid mpan2i com23
      wf1o expd expdimp adantrd rexlimdva syld impd ancomsd sylbird mt3d anim1i
      eldifsn sylbi elplyd cmin uzdisj nn0cnd pncan1 ineq1d eqcomd fconst snssi
      eqtr3id sstri fss fun mpanl2 nn0uz eleqtrdi uzsplit eqtrid uneq1d ssequn1
      eqtr2d mpbi feq23d fnimadisj nn0zd peano2zd uzid ne0i inidm neeq1i xpima2
      syl2anr uneq12d imaundir uncom eqtr2i 3eqtr4g fvun1 mp3an2 anassrs oveq1d
      anim12ci mpteq2dv coeeq reseq1d res0 reseq2d fresaunres1 fveq2 eqtr2 coe0
      3eqtr3a reseq1i elfznn0 ssriv xpssres eqtrdi syl2im necon3d impr sylanbrc
      oveq1 sumeq2sdv fvmpt fsummulc2 simpll mulassd ad2ant2lr anasss ad2ant2rl
      3eqtr4d fsumcom nfra1 nfan rspa fsummulc1 adantlrr mul02d 3eqtr3d ralrimi
      sumeq2d olci sumz adantrlr fveq1 eqeq1d rspcev sylanr1 rexlimddv elqaa
      nfv ) ABUGMZBUAUHZNZOPZUAQUUANZUIUJUKZUMZBUUBMHAOFULRZDUHZUBUHZNZCUNRZDUO
      ZOPZEUPFULRZUQZWWOUBQWWPURRZWWPOUJZUSZUJZUKZAWXDUBWXIUMZFUPUTRZFVAVBZAFWX
      KUUHVBWXLVCAFAFIVDZUUCAFWXKWXMAWXKAFVEMZWXKVEMIFUUDVFZVDUUEVGAWXJVCZWWPSD
      WWPEWXCCVHZVHZVIZWXRVJZVKQUUIRZWXCVLRZUUFNMZTZWXLAWXRWYBUUGVBZWXDWWRWXGPZ
      VMZUBWXEUQZWYDWXPAWYEWYBWWRWXRWYBUUJNZVNZRZVORZWXCWXFUSZPZWYFVMZUBWXEUQZW
      YHAWWPQWXCURRZWXRVPZWYEWYPXGZADWWPWXQWYQAWWQWWPMZTZWXCQWXQVPWXQWYQMZXUAEW
      XCCQAWYTEUHZWXCMZCQMZKUUKZVQQWXCWXQVRUPFULVSZVTWAZVQZWYBUULMZWWPWBMZWYRWY
      SWYAUUSMZWXCWBMZXUJWYAWDMZXULWYAWYAWCZUUMZWYAUUNWEZUPFWFZWYAWYBWXCWBWYBWC
      ZUUOWGZOFWFZUBWYQWYAWYIWXRWWPWXEWYBWBOWYMXUNXUMWYQWYBWHNPXUPXURWYAWYBWXCQ
      WDXUSWYAXUOUUPZWIWGZXUNXUMWYAWYBUUTNPXUPXURWYAWYBWXCWDWBXUSUUQWGZWYIWCZXU
      LXUMWYMWYBUVANPXUQXURWYAWYBWXCWBOXUSWYAXUOUURZUVBWGZXVFXUNXUKWXEWYAWWPVLR
      ZWHNPXUPXVAWYAXVHWWPQWDXVHWCXVBWIWGUVCUVDVFAWYOWYGUBWXEWWRWXEMZAWWPQWWRVP
      ZWYOWYGXGWWRQWWPWJZAXVJTZWYNWXDWYFXVLWYNXUCWYLNZXUCWYMNZPZEWXCUQZWXDXVLWY
      LWXCWKZWYMWXCWKZWYNXVPXGXVLWYLWYQMWXCQWYLVPXVQXVLWYLEWXCWXAVHZWYQXVLWYLWY
      BDWWPEWXCWWTVHZVHZVOREWXCWYADWWPWWTVHZVORZVHXVSXVLWYKXWAWYBVOXVLWYKDWWPWW
      SWXQWYIRZVHXWAXVLDWWPWWSWXQWYIWWRWXRWBSSXVLOFWLZXVLWYTTZWWQWWRWMWXQSMXWFE
      WXCCXUGWNZWOXVLDWWPQWWRAXVJUVEUVFXVLWXRWPWQXVLDWWPXWDXVTXWFXWDWXCWWSUJUSZ
      WXQUNVNRXVTXWFWWSWYQWYAWYIUNWXCQWBWXQWYBXUSXVCXVBXWFUPFWLZXVJWYTWWSQMZAWW
      PQWWQWWRUVGZWRZAWYTXUBXVJXUHWSXVEQSMUNWYAUVHNPVRQVKWYAUNSXUOUVIUVJWEUVSXW
      FEWXCWWSCUNXWHWXQWBSQXWIXWFXUDTZWWQWWRWMAWYTXUDXUEXVJXUFWTXWHEWXCWWSVHPXW
      FEWXCWWSUVKWOXWFWXQWPWQXAXBXAXCXVLEDWYQWYAWWTWXCWWPWBWBWYBWYMXUSXVCXVGXVL
      UPFWLZXWEXULXVLXUQWOXWFWXCQXVTVPXVTWYQMXWFEWXCWWTQXVLXUDWYTWWTQMZXVLXUDTZ
      WYTTZXWJXUEXWOXVLWYTXWJXUDXWLWSAXUDWYTXUEXVJAWYTXUDXUEXUFXDWTWWSCUVLXEZXD
      VQQWXCXVTVRXUGVTWAXVLDWWPXWASSXVTWYMXWAWCXWEXVTSMXWFEWXCWWTXUGWNWOWYMSMXV
      LWXCWXFXUGOUVMUVNWOUVOUVPXVLEWXCXWCWXAXWPVKXWBVORXWCWXAXWPUAWWPUGUTQXWBVK
      WYASWBOUVQUVRXUOVKSMXWPUVTWOXWPOFWLZQUGXFZXWPXHWOZXWPDWWPWWTQXWRVQOQMZXWP
      OXIMZXXBXJOUWAZWEWOZWWJUGMZOWWJUTRWWJPZWWJOUTRWWJPZTXWPXXFXXGXXHWWJUWBWWJ
      UWCUWDXKUWEXWPWWPWWTDXWSXWQWWSCXWPXVJWYTWWSUGMZAXVJXUDUWFXVJWYTTXWJXXIXWK
      WWSXLVFZXMAXUDWYTCUGMZXVJAWYTXUDXXKXUAXUDTZXUEXXKXUFCXLVFZXDWTXNZUWGUWHXB
      UWIZXVLWXCQXVSVPXVSWYQMXVLEWXCWXAQXWPUAUCWWPWWTQDXXAWWJQMUCUHZQMTWWJXXPUT
      RQMXWPWWJXXPUWJXKXWSXWRXXEUWKVQQWXCXVSVRXUGVTWAUWLWYLQWXCWJWXCQWYLYAXOOSM
      ZXVRXPWXCOSXQWEEWXCWYLWYMEWYBWYKVOEWYBXREVOXREWWRWXRWYJEWWRXREWYJXREDWWPW
      XQEWWPXREWXCCUWMUWNXSXSEWYMXRUWOUWSXVLXVOWXBEWXCXWPXVMWXAXVNOXVLXUDXVMXUC
      XVSNZWXAXVLXUCWYLXVSXXOUWPXUDWXASMXXRWXAPWWPWWTDXTEWXCWXASXVSXVSWCUWQUWRU
      WTXUDXVNOPXVLWXCOXUCXPUXAXKUXBUXCUXDUXEYBUXCUXDWYEWXRUXFZSWXRVIZWYCTZWYDX
      UJWYAUXGMZWYEXYAXGXUTXUNXYBXUPWYAUXIWEZWXRWYAWYBXVDUXHWGXXTWXSWYCXXSWWPPX
      XTWXSXGDWWPWXQWXRXWGWXRWCUXJXXSWWPSWXRUXKWEUXLUXMWYHWWRWXHUXNZWXDVCZVMZUB
      WXEUQXYEUBWXIUQWXPWYGXYFUBWXEWYGWYFVCZXYEVMXYFWXDWYFUXOXYDXYGXYEXYDWWRWXH
      MWYFWWRWXHUXPUBWXGUXQUXRUXSUXTUYAXYEUBWXEWXHUYBWXDUBWXIUYCUYDUYEAWYCWXSWX
      LAWYCWXSWXLAWYCWXTUDUHZYCVBZXYHYOYDWYBUYFNZUYGNZMZTZUDWYAWXCUYHRZVJZUYIZU
      MZWXSWXLVMZAWYCXYQAWYCTZUAUCXYJWXTXYOYOXYKWYBUYJNZWYQUEUDXYJWYQUYKNMZXYSX
      UJYUAXUTWYQXYJWYBXVCXYJWCZUYLWEZWOXUJXYTXYJUYMNZPXUTXYJYUDXYTWYBYUBXYTWCZ
      YUDWCUYNWEZXYKWCZWWJUEUHZXXPUJYDXYTNMUCYUHWWJUJZYDXYTNYUHXYTNUKUQUAWYQUQU
      EWYQUYIUQZXYSWYBUYOMZYUJYUKXUJXUNXUTXUPWYAWYBXVDUYPUYQYUKXYJWYQUYRNMYUJUA
      UCXYJXYTWYBWYQUEYUBYUFXVCVUCUYSWEWOAWXTWYQYOUKZXFWYCAWXTWYQYULAWWPWYQWXRX
      UIUYTZWYQVUDZVUAYEXYOYULXFXYSXYOWYQYULWXCWYQXYNVPZXYOWYQXFXULXUMYUOXUQXUR
      WYQWYAXYNWXCWBWYBXYNWCZXUSXVCVUBWGWXCWYQXYNVUMWEYUNVUEWOAWXTXYOYOYDZXYTNZ
      XFWYCAWXTWYQYURYUMYURXYOXYTNZWYQYUQXYOXYTXYOYFVUFXYOWYBVUNNZMZYUSWYQPXULX
      UMYVAXUQXURWYAXYNWYBWXCYUTWBXUSYUPYUTWCZVUGWGXYOYUTXYTWYQWYBXVCYVBYUEVUHW
      EVUIVUAYEXYSWXTYOYDWXTXYKWXTYFWYCAWWJWXTYUIUKXYTNMVCZUAWXTUQZWXTXYKMZWYCY
      VCUAWXTXUJXYBTWYCWWJWXTMYVCXUJXYBXUTXYCVUJWWJWXTXYTWYAWYBYUEXVDVUKVULVUOA
      YVEYVDAYUAWXTWYQXFYVEYVDXGYUCYUMUAXYJWXTXYKXYTWYQYUFYUGVUPVUQVURYBVUSWXTW
      BMZXYOWBMZVUTXYSYVFYVGXUKWXRWBMYVFXVADWWPWXQVVAWXRVVBVVDVVEWOVVCYPAXYMXYR
      UDXYPAXYHXYPMZTXYIXYRXYLYVHAXYHXYOYGVBZXYIXYRVMXYOSMYVHXYHXYOXFYVIXYNWYAW
      XCUYHVSVVFXYHXYOVVGXYHXYOSVVHVVIAYVIXYIXYRYVIXYITWXTXYOYGVBZAXYRXYIYVIYVJ
      WXTXYHXYOVVJYHAWXSYVJWXLWXSWWPWXTYCVBZAYVJWXLVMWXSWWPWXTWXRVWEYVKWWPSWXRV
      VKWWPWXTWXROFULVSVVOVFAYVKYVJWXLYVKYVJTWWPXYOYGVBZAWXLWWPWXTXYOVVJAYVLXYO
      WXCYCVBZWXLWXCXYOXYBXUMWXCXYOYCVBXYCXURWYAXYNWXCWBYUPVVLWGVVMYVLYVMTWWPWX
      CYGVBZAWXLWWPXYOWXCVVNYVNWWPVVPNZWXCVVPNZVAVBZAWXLXUKXUMYVQYVNXGXVAXURWWP
      WXCWBVVQWGAYVOWXKYVPFVAAWXNYVOWXKPIFVVRVFAWXNYVPFPIFVVSVFVVTVWAVWBVWCYIVW
      FYIVWDYIVWGYBVWHVWIVWJVWKVWLVWMVWNWWRWXIMZAXVJWWRWXGYJZTZWXDWWOYVRXVIYVST
      YVTWWRWXEWXGVWPXVIXVJYVSXVKVWOVWQAYVTWXDTTUCUGWWPWWSXXPWWQYKRZUNRZDUOZVHZ
      WWNMZBYWDNZOPZWWOAYVTYWEWXDAYVTTYWDWWMMZYWDUIYJZYWEAXVJYWHYVSXVLUCWWSQDFX
      WTXVLXHWOAWXNXVJIYEZXWLVWRZYLAXVJYVSYWIXVLYWDUIWWRWXGXVLYWDYMNZWWPYNZWWRP
      ZYWDUIPZYWMUIYMNZWWPYNZPZWYFXVLYWMWWRWXKYQNZWXFUSZYDZWWPYNZWWRXVLYWLYXAWW
      PXVLUCYXAQDYWDFYWKYWJXVLWWPYWSYDZQUGYDZYXAVPZVEUGYXAVPZXVJAYXEAXVJWWPYWSY
      RZYOPZYXEAYOYXGAYOOWXKUPVWSRZULRZYWSYRYXGOWXKVWTAYXJWWPYWSAYXIFOULAFUGMYX
      IFPAFIVXAFVXBVFXCZVXCVXGZVXDZXVJYWSUGYWTVPZYXHYXEYWSWXFYWTVPZWXFUGXFYXNYW
      SOXPVXEZWXFQUGXXCXXBWXFQXFZXJXXDOQVXFVVDZXHVXHYWSWXFUGYWTVXIWGWWPYWSQUGWW
      RYWTVXJVXKYBYHAYXEYXFXGXVJAYXCYXDVEUGYXAAVEYXJYWSYDZYXCAVEOYQNZYXSVXLAWXK
      YXTMYXTYXSPAWXKVEYXTWXOVXLVXMOWXKVXNVFVXOAYXJWWPYWSYXKVXPVXRYXDUGPZAXWTYY
      AXHQUGVXQVXSWOVXTYEVGXVLWWRYWSYSZYWTYWSYSZYDYOWXFYDZYXAYWSYSWXFXVLYYBYOYY
      CWXFXVJWWRWWPWKZYXHYYBYOPAWWPQWWRYAZYXMWWPYWSWWRVYAVYIAYYCWXFPZXVJAYWSYWS
      YRZYOYJZYYGAYWSYOYJZYYIAWXKXIMWXKYWSMYYJAFAFIVYBVYCWXKVYDYWSWXKVYEXOYYHYW
      SYOYWSVYFVYGWAYWSWXFYWSVYHVFYEVYJWWRYWTYWSVYKYYDWXFYOYDWXFYOWXFVYLWXFYFVY
      MVYNXVLUCUGYWCWWPWWQYXANZYWAUNRZDUOXVLWWPYWBYYLDXWFWWSYYKYWAUNXWFYYKWWSXV
      LYYEYXHTWYTYYKWWSPZAYXHXVJYYEYXMYYFVYSYYEYXHWYTYYMYYEYWTYWSWKZYXHWYTTYYMX
      XQYYNXPYWSOSXQWEWWPYWSWWRYWTWWQVYOVYPVYQXMVXDVYRYTVYTWUAWUBXVJAYXBWWRPZAX
      VJWWRYXGYNZYWTYXGYNZPZYYOAWWRYOYNYOYYPYYQWWRWUCAYOYXGWWRYXLWUDAYOYWTYOYNY
      YQYWTWUCAYOYXGYWTYXLWUDVXGWUIXVJYWSQYWTVPZYYRYYOYXOYXQYYSYXPYXRYWSWXFQYWT
      VXIWGWWPYWSQWWRYWTWUEVYPYBYHXAYWOYWLYWPWWPYWDUIYMWUFWUBYWNYWRWYFYWNYWRTWW
      RYWQWXGYWMWWRYWQWUGYWQVEWXFUSZWWPYNZWXGYWPYYTWWPWUHWUJWWPVEXFUUUAWXGPUAWW
      PVEWWJFWUKWULVEWXFWWPWUMWEVUIWUNYPWUOWUPWUQYWDWWMUIVWPWURYLAXVJWXDYWGYVSA
      XVJWXDTZTZYWFWWPWWSBWWQYKRZUNRZDUOZOAYWFUUUFPZUUUBAWWIUUUGHUCBYWCUUUFUGYW
      DXXPBPZWWPYWBUUUEDUUUHYWAUUUDWWSUNXXPBWWQYKWUSXCWUTYWDWCWWPUUUEDXTWVAVFYE
      UUUCUUUFWXCOEUOZOUUUCUUUFWXCWWPWWTGUNRZDUOZEUOZUUUIAXVJUUUFUUULPWXDXVLUUU
      FWWPWXCUUUJEUOZDUOUUULXVLWWPUUUEUUUMDXWFWWSWXCCGUNRZEUOZUNRZWXCWWSUUUNUNR
      ZEUOUUUEUUUMXWFWXCUUUNWWSEXWIXVJWYTXXIAXXJWRZAWYTXUDUUUNUGMXVJXXLCGXXMAXU
      DGUGMZWYTJWSXNWTWVBAWYTUUUEUUUPPXVJXUAUUUDUUUOWWSUNLXCWSXWFWXCUUUJUUUQEXW
      MWWSCGXWFXXIXUDUUURYEAWYTXUDXXKXVJXXMWTXWFAXUDUUUSAXVJWYTWVCJXMWVDYTWVHYT
      XVLWWPWXCUUUJDEXWEXWNXVLWYTXUDTZTZWWTGUUVAWWSCXVJWYTXXIAXUDXXJWVEAUUUTXXK
      XVJAWYTXUDXXKXXMWVFWSXNAXUDUUUSXVJWYTJWVGXNWVIXAYLUUUCWXCUUUKOEUUUCUUUKOP
      ZEWXCAUUUBEAEWWHXVJWXDEXVJEWWHWXBEWXCWVJWVKWVKUUUCXUDUUVBUUUCXUDTWXAGUNRZ
      OGUNRZUUUKOUUUBXUDUUVCUUVDPZAWXDXUDUUVEXVJWXDXUDTWXAOGUNWXBEWXCWVLVYRWRWR
      AXVJXUDUUVCUUUKPWXDXWPWWPWWTGDXWSAXUDUUUSXVJJWSXXNWVMWVNAXUDUUVDOPUUUBAXU
      DTGJWVOWSWVPYPWVQWVRXAWXCUFYQNXFZXUMVUTUUUIOPXUMUUVFXURWVSWXCEUFWVTWEWUNX
      AWWAWWLYWGUAYWDWWNWWJYWDPWWKYWFOBWWJYWDWWBWWCWWDXEWWEWWFBUAWWGWUR $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Other results
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  Results not easily categorized.

$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Examples
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  These should be moved into the "examples" section.  These exist to prove
  specific concrete examples of definitions; examples make definitions easier
  to understand, and proving them means that the examples are justifiably
  correct.

$)

$( (End of David A. Wheeler's mathbox.) $)
