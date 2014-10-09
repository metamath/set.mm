$( hol.mm  7-Oct-2014 $)

$(
                      PUBLIC DOMAIN DEDICATION

This file is placed in the public domain per the Creative Commons Public
Domain Dedication. http://creativecommons.org/licenses/publicdomain/

Mario Carneiro - email: di.gama at gmail.com

$)

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
                           Foundations
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

  $c wff class set $.  $( Not used; for mmj2 compatibility $)

  $( Declare the primitive constant symbols for lambda calculus. $)
  $c var $.   $( Typecode for variables (syntax) $)
  $c hol_type $. $( Typecode for types (syntax) $)
  $c term $.  $( Typecode for terms (syntax) $)
  $c : $.     $( Typecode for "type of x is y" expressions (logical) $)
  $c |- $.    $( Typecode for theorems (logical) $)
  $c |= $.    $( Context separator $)
  $c bool $.  $( Boolean type $)
  $c ind $.   $( 'Individual' type $)
  $c -> $.    $( Function type $)
  $c ( $.     $( Open parenthesis $)
  $c ) $.     $( Close parenthesis $)
  $c , $.     $( Context comma $)
  $c \ $.     $( Lambda expression $)
  $c = $.     $( Equality term $)
  $c T. $.    $( Truth term $)
  $c [ $.     $( Infix operator $)
  $c ] $.     $( Infix operator $)

  $v al $.  $( Greek alpha $)
  $v be $.  $( Greek beta $)
  $v ga $.  $( Greek gamma $)
  $v de $.  $( Greek delta $)

  $v x y z f g p q $.  $( Bound variables $)
  $v A B C F R S T $.  $( Term variables $)

  $( Let variable ` al ` be a type. $)
  hal $f hol_type al $.
  $( Let variable ` be ` be a type. $)
  hbe $f hol_type be $.
  $( Let variable ` ga ` be a type. $)
  hga $f hol_type ga $.
  $( Let variable ` de ` be a type. $)
  hde $f hol_type de $.

  $( Let variable ` x ` be a var. $)
  vx $f var x $.
  $( Let variable ` y ` be a var. $)
  vy $f var y $.
  $( Let variable ` z ` be a var. $)
  vz $f var z $.
  $( Let variable ` f ` be a var. $)
  vf $f var f $.
  $( Let variable ` g ` be a var. $)
  vg $f var g $.
  $( Let variable ` p ` be a var. $)
  vp $f var p $.
  $( Let variable ` q ` be a var. $)
  vq $f var q $.
  
  $( Let variable ` A ` be a term. $)
  ta $f term A $.
  $( Let variable ` B ` be a term. $)
  tb $f term B $.
  $( Let variable ` C ` be a term. $)
  tc $f term C $.
  $( Let variable ` F ` be a term. $)
  tf $f term F $.
  $( Let variable ` R ` be a term. $)
  tr $f term R $.
  $( Let variable ` S ` be a term. $)
  ts $f term S $.
  $( Let variable ` T ` be a term. $)
  tt $f term T $.

  $( A var is a term. $)
  tv $a term x $.

  $( The type of all functions from type ` al ` to type ` be ` . $)
  ht $a hol_type ( al -> be ) $.
  $( The type of booleans (true and false). $)
  hb $a hol_type bool $.
  $( The type of individuals. $)
  hi $a hol_type ind $.

  $( A combination (function application). $)
  kc $a term ( F T ) $.
  $( A lambda abstraction. $)
  kl $a term \ x T $.
  $( The equality term. $)
  ke $a term = $.
  $( Truth term. $)
  kt $a term T. $.
  $( Infix operator. $)
  kbr $a term [ A F B ] $.
  $( Type operator. $)
  kty $a term : A al $.
  $( Context operator. $)
  kct $a term ( A , B ) $.

  $( Internal axiom for mmj2 use. $)
  wffMMJ2 $a wff A |= B $.

  ${
    idi.1 $e |- R |= A $.
    $( The identity inference. $)
    idi $p |- R |= A $=
      (  ) C $.
      $( [9-Oct-2014] $)
  $}

  ${               
    ax-id.1 $e |- T. |= : R bool $.
    $( The identity inference. $)
    ax-id $a |- R |= R $.

    $( The identity inference. $)
    id $p |- R |= R $=
      ( ax-id ) ABC $.
      $( [7-Oct-2014] $)
  $}

  ${
    ax-syl.1 $e |- R |= S $.
    ax-syl.2 $e |- S |= T $.
    $( Syllogism inference. $)
    ax-syl $a |- R |= T $.

    $( Syllogism inference. $)
    syl $p |- R |= T $=
      ( ax-syl ) ABCDEF $.
      $( [8-Oct-2014] $)
  $}

  ${
    ax-jca.1 $e |- R |= S $.
    ax-jca.2 $e |- R |= T $.
    $( Join common antecedents. $)
    ax-jca $a |- R |= ( S , T ) $.

    $( Syllogism inference. $)
    jca $p |- R |= ( S , T ) $=
      ( ax-jca ) ABCDEF $.
      $( [8-Oct-2014] $)
  $}

  ${
    syl2anc.1 $e |- R |= S $.
    syl2anc.2 $e |- R |= T $.
    syl2anc.3 $e |- ( S , T ) |= A $.
    $( Syllogism inference. $)
    syl2anc $p |- R |= A $=
      ( kct jca syl ) BCDHABCDEFIGJ $.
      $( [7-Oct-2014] $)
  $}

  ${
    ax-simpld.1 $e |- R |= ( S , T ) $.
    $( Extract an assumption from the context. $)
    ax-simpld $a |- R |= S $.

    $( Extract an assumption from the context. $)
    simpld $p |- R |= S $=
      ( ax-simpld ) ABCDE $.
      $( [8-Oct-2014] $)

    $( Extract an assumption from the context. $)
    ax-simprd $a |- R |= T $.

    $( Extract an assumption from the context. $)
    simprd $p |- R |= T $=
      ( ax-simprd ) ABCDE $.
      $( [8-Oct-2014] $)
  $}

  ${
    ax-trud.1 $e |- T. |= : R bool $.
    $( Change an empty context into any context. $)
    ax-trud $a |- R |= T. $.

    $( Change an empty context into any context. $)
    trud $p |- R |= T. $=
      ( ax-trud ) ABC $.
      $( [7-Oct-2014] $)

    ax-a1i.2 $e |- T. |= A $.
    $( Change an empty context into any context. $)
    a1i $p |- R |= A $=
      ( kt ax-trud syl ) BEABCFDG $.
      $( [7-Oct-2014] $)
  $}

  ${
    ax-cb.1 $e |- R |= A $.
    $( A context has type boolean. (This is also not strictly necessary, as we
       can just keep the type hypotheses, but it simplifies many theorems and
       a simple structural induction argument shows that this is always true.)
       $)
    ax-cb1 $a |- T. |= : R bool $.

    $( A theorem has type boolean. $)
    ax-cb2 $a |- R |= : A bool $.
  $}

  ${
    a1s.1 $e |- R |= B $.
    a1s.2 $e |- T. |= A $.
    $( Change an empty context into any context. $)
    a1s $p |- R |= A $=
      ( ax-cb1 a1i ) ACBCDFEG $.
      $( [7-Oct-2014] $)
  $}

  ${
    mpdan.1 $e |- R |= : T bool $.
    mpdan.2 $e |- R |= S $.
    mpdan.3 $e |- ( R , S ) |= T $.
    $( Modus ponens deduction. $)
    mpdan $p |- R |= T $=
      ( hb kty ax-cb1 id syl2anc ) CAABAGCHADIJEFK $.
      $( [8-Oct-2014] $)
  $}

  $( The type of a type predicate. $)
  wtt $a |- T. |= : : T al bool $.

  $( Truth type. $)
  wtru $p |- T. |= : T. bool $=
    ( ta hb kty kt wtt ax-cb1 ) BBACCDBAEF $.

  ${
    wtti.1 $e |- R |= A $.
    $( The type of a type predicate. $)
    wtti $p |- R |= : : T al bool $=
      ( hb kty wtt a1s ) FADGGBCEADHI $.
      $( [8-Oct-2014] $)
  $}

  ${
    simpl.1 $e |- T. |= : ( R , S ) bool $.
    $( Extract an assumption from the context. $)
    simpl $p |- ( R , S ) |= R $=
      ( kct ax-id simpld ) ABDZABGCEF $.
      $( [8-Oct-2014] $)

    $( Extract an assumption from the context. $)
    simpr $p |- ( R , S ) |= S $=
      ( kct ax-id simprd ) ABDZABGCEF $.
      $( [8-Oct-2014] $)
  $}

  ${
    syldan.1 $e |- ( R , S ) |= T $.
    syldan.2 $e |- ( R , T ) |= A $.
    $( Syllogism inference. $)
    syldan $p |- ( R , S ) |= A $=
      ( kct ax-cb1 simpl syl2anc ) ABCGZBDBCDKEHIEFJ $.
      $( [8-Oct-2014] $)
  $}

  $( The equality function has type ` al -> al -> bool ` , i.e. it is
     polymorphic over all types, but the left and right type must agree. $)
  weq $a |- T. |= : = ( al -> ( al -> bool ) ) $.

  $( Reflexivity of equality. $)
  ax-refl $a |- : A al |= ( ( = A ) A ) $.

  ${
    ax-eqmp.1 $e |- R |= A $.
    ax-eqmp.2 $e |- R |= ( ( = A ) B ) $.
    $( Modus ponens for equality. $)
    ax-eqmp $a |- R |= B $.
  $}

  $( Deduce the type of equivalent terms. (This is not strictly necessary, as
     no theorem can have non-well-typed equality, but it allows us to derive
     the types of newly defined symbols, rather than having to add the types
     as more axioms.) $)
  ax-typeq $a |- ( ( = A ) B ) |= ( ( = : A al ) : B al ) $.

  ${
    ax-ded.1 $e |- ( R , S ) |= T $.
    ax-ded.2 $e |- ( R , T ) |= S $.
    $( Deduction theorem for equality. $)
    ax-ded $a |- R |= ( ( = S ) T ) $.
  $}

  $( The type of a context. $)
  wctg $a |- : S bool |= ( ( = : T bool ) : ( S , T ) bool ) $.

  ${
    wct.1 $e |- R |= : S bool $.
    wct.2 $e |- R |= : T bool $.
    $( The type of a context. $)
    wct $p |- R |= : ( S , T ) bool $=
      ( hb kty kct ke kc wctg syl ax-eqmp ) FCGZFBCHGZAEAFBGINJOJDBCKLM $.
      $( [8-Oct-2014] $)
  $}

  $( Equality theorem for combination. $)
  ax-ceq $a |- ( ( ( = F ) T ) , ( ( = A ) B ) ) |=
    ( ( = ( F A ) ) ( T B ) ) $.

  ${
    eqcomx.1 $e |- R |= : A al $.
    eqcomx.2 $e |- R |= ( ( = A ) B ) $.
    $( Commutativity of equality. $)
    eqcomx $p |- R |= ( ( = B ) A ) $=
      ( hbe ke kc kty ax-refl syl kt hb ht weq a1s ax-ceq syl2anc ax-eqmp )
      HBIZBIZHCIZBIZDDABJZUBEABKLZHUBIUDIDHUAIUCIZUBUGDHHIHIZUACIUHUEDEMGGNOOZH
      JUHGPUIHKLQFBCHHRSUFBBUAUCRST $.
      $( [7-Oct-2014] $)
  $}

  ${
    mpbirx.1 $e |- R |= A $.
    mpbirx.2 $e |- R |= ( ( = B ) A ) $.
    $( Deduction from equality inference. $)
    mpbirx $p |- R |= B $=
      ( hb kty ax-cb2 wtt a1s ke kc ax-typeq syl eqcomx ax-eqmp ) ABCDFBACFAGZ
      FBGZCACDHFRQCFRGACDFBIJCKBLALKRLQLEFBAMNOPEOP $.
      $( [7-Oct-2014] $)
  $}

  ${
    wctrr.1 $e |- R |= : ( S , T ) bool $.
    wctrr.2 $e |- R |= : S bool $.
    $( Reverse closure of the type of a context. $)
    wctrr $p |- R |= : T bool $=
      ( hb kct kty ke kc wctg syl mpbirx ) FBCGHZFCHZADAFBHIOJNJEBCKLM $.
      $( [8-Oct-2014] $)
  $}

  ${
    ancoms.1 $e |- ( R , S ) |= T $.
    $( Swap the two elements of a context. $)
    ancoms $p |- ( S , R ) |= T $=
      ( kct kt ax-cb1 wctrr wctrl wct simpr simpl syl2anc ) CBAEABBAFBAFABCABED
      GZHFABNIJZKBAOLDM $.
      $( [8-Oct-2014] $)
  $}

  ${
    wcti.1 $e |- R |= : S bool $.
    $( Type of a context, where the typehood of the second argument is
       dependent on the first argument. $)
    wcti $a |- T. |= : ( R , S ) bool $.

    $( Type of a context, where the typehood of the first argument is
       dependent on the second argument. $)
    wctri $p |- T. |= : ( S , R ) bool $=
      ( hb kty kct kt wcti wctg mpbirx wtt wct id ancoms syl ax-eqmp ) DBEZDAEZ
      FZDBAFEGGRQFZSDABFETGABCHABIJQRSSGQRDBKDAKLMNOBAIP $.
      $( [9-Oct-2014] $)
  $}

  ${
    adantr.1 $e |- R |= T $.
    adantr.2 $e |- R |= : S bool $.
    $( Extract an assumption from the context. $)
    adantr $p |- ( R , S ) |= T $=
      ( kct wcti simpl syl ) ABFACABABEGHDI $.
      $( [8-Oct-2014] $)

    $( Extract an assumption from the context. $)
    adantl $p |- ( S , R ) |= T $=
      ( adantr ancoms ) ABCABCDEFG $.
      $( [8-Oct-2014] $)
  $}

  ${
    ct1.1 $e |- R |= S $.
    ct1.2 $e |- R |= : T bool $.
    $( Introduce a right conjunct. $)
    ct1 $p |- ( R , T ) |= ( S , T ) $=
      ( kct adantr wcti simpr jca ) ACFBCACBDEGACACEHIJ $.

    $( Introduce a left conjunct. $)
    ct2 $p |- ( T , R ) |= ( T , S ) $=
      ( kct wctri simpl adantl jca ) CAFCBCAACEGHACBDEIJ $.
  $}

  ${
    sylan.1 $e |- R |= S $.
    sylan.2 $e |- ( S , T ) |= A $.
    $( Syllogism inference. $)
    sylan $p |- ( R , T ) |= A $=
      ( kct hb kty kt ax-cb1 wctrr a1s ct1 syl ) BDGCDGZABCDEHDICBEJCDAPFKLMNFO
      $.
      $( [8-Oct-2014] $)
  $}

  ${
    an32s.1 $e |- ( ( R , S ) , T ) |= A $.
    $( Commutation identity for context. $)
    an32s $p |- ( ( R , T ) , S ) |= A $=
      ( kct kt ax-cb1 wctrl wctrr wct simpl hb kty a1i adantr simpr jca syl2anc
      ) ABDFZCFZBCFZDUABCTCBBDGBDGBCGUBDAUBDFEHZIZIGUBDUCJKZLMCNTUEGBCUDJZOZPTC
      GTCUEUFKQRTCDBDUEQUGPES $.
      $( [8-Oct-2014] $)

    $( Associativity for context. $)
    anasss $p |- ( R , ( S , T ) ) |= A $=
      ( kct kt ax-cb1 wctrl id ancoms sylan an32s ) CDFBAACBDACBFBCFZDBCNNGNDAN
      DFEHIJKELMK $.
      $( [8-Oct-2014] $)
  $}

  ${
    anassrs.1 $e |- ( R , ( S , T ) ) |= A $.
    $( Associativity for context. $)
    anassrs $p |- ( ( R , S ) , T ) |= A $=
      ( kct kt ax-cb1 wctrl wctrr wct simpl hb kty a1i adantr simpr ct1 syl2anc
      ) ABCFZDFBCDFZTDBBCGBCGBUAABUAFEHZIGCDGBUAUBJZIKZLMDNTUDGCDUCJOZPTCDBCUDQ
      UERES $.
      $( [8-Oct-2014] $)
  $}

  ${
    wctrl.1 $e |- R |= : ( S , T ) bool $.
    wctrl.2 $e |- R |= : T bool $.
    $( Reverse closure of the type of a context. $)
    wctrl $p |- R |= : S bool $=
      ( hb kct kty ke kc wcti simpr simprd simpld anassrs an32s anasss ax-typeq
      jca ax-ded syl ax-eqmp wctrr ) ACBFBCGZHZFCBGZHZADAIUDJUFJIUEJUGJAUDUFAUD
      GZCBUHBCAUDAUDDKLZMUHBCUINSUDACBUDABCUDABCUIOPQTFUDUFRUAUBEUC $.
      $( [8-Oct-2014] $)
  $}

  $( The type of a combination. $)
  wcg $a |- ( : F ( al -> be ) , : T al ) |= : ( F T ) be $.

  $( The type of a lambda abstraction. $)
  wlg $a |- ( : x al , : T be ) |= : \ x T ( al -> be ) $.

  ${
    wc.1 $e |- R |= : F ( al -> be ) $.
    wc.2 $e |- R |= : T al $.
    $( The type of a combination. $)
    wc $p |- R |= : ( F T ) be $=
      ( kc kty ht wcg syl2anc ) BCEHIDABJCIAEIFGABCEKL $.
      $( [8-Oct-2014] $)
  $}

  ${
    wl.1 $e |- R |= : x al $.
    wl.2 $e |- R |= : T be $.
    $( The type of a lambda abstraction. $)
    wl $p |- R |= : \ x T ( al -> be ) $=
      ( ht kl kty tv wlg syl2anc ) ABHCEIJDACKJBEJFGABCELM $.
  $}

  $( Axiom of beta-substitution. $)
  ax-beta $a |- ( : x al , : A be ) |= ( ( = ( \ x A x ) ) A ) $.

  $( Distribution of combination over substitution. $)
  ax-distrc $a |- ( ( : x al , : F ( be -> ga ) ) , ( : A be , : B al ) ) |=
    ( ( = ( \ x ( F A ) B ) ) ( ( \ x F B ) ( \ x A B ) ) ) $.

  ${
    $d x R $.
    ax-abs.1 $e |- ( R , : x al ) |= ( ( = A ) B ) $.
    $( Equality theorem for abstraction. $)
    ax-abs $a |- ( R , : x al ) |= ( ( = \ x A ) \ x B ) $.
  $}

  ${
    $d y B $.
    $( Distribution of lambda abstraction over substitution. $)
    ax-distrl $a |- ( ( : x al , : y be ) , ( : A ga , : B al ) ) |=
      ( ( = ( \ x \ y A B ) ) \ y ( \ x A B ) ) $.
  $}

  $( Tautology is provable. $)
  tru $p |- T. |= T. $=
     ( kt wtru id ) ABC $.
    $( [7-Oct-2014] $)

  $( Infix operator. This is a simple metamath way of cleaning up the syntax
     of all these infix operators to make them a bit more readable than the
     curried representation. $)
  df-i $a |- T. |= ( ( = [ A F B ] ) ( ( F A ) B ) ) $.

  ${
    dfi1.1 $e |- R |= [ A F B ] $.
    $( Forward direction of ~ df-i . $)
    dfi1 $p |- R |= ( ( F A ) B ) $=
      ( kbr kc ke df-i a1s ax-eqmp ) ABCFZCAGBGZDEHLGMGLDEABCIJK $.
      $( [8-Oct-2014] $)
  $}

  ${
    dfi2.1 $e |- R |= ( ( F A ) B ) $.
    $( Reverse direction of ~ df-i . $)
    dfi2 $p |- R |= [ A F B ] $=
      ( kc kbr ke df-i a1s mpbirx ) CAFBFZABCGZDEHMFLFLDEABCIJK $.
      $( [8-Oct-2014] $)
  $}

  ${
    mpbi.1 $e |- R |= A $.
    mpbi.2 $e |- R |= [ A = B ] $.
    $( Deduction from equality inference. $)
    mpbi $p |- R |= B $=
      ( ke dfi1 ax-eqmp ) ABCDABFCEGH $.
      $( [7-Oct-2014] $)
  $}

  ${
    wov.1 $e |- R |= : F ( al -> ( be -> ga ) ) $.
    wov.2 $e |- R |= : A al $.
    wov.3 $e |- R |= : B be $.
    $( Type of an infix operator. $)
    wov $p |- R |= : [ A F B ] ga $=
      ( kc kty kbr ht wc ke kt df-i ax-typeq syl a1s mpbirx ) CFDKZEKZLZCDEFMZ
      LZGBCUCGEABCNFGDHIOJOPUGKUEKZADLGIQPUFKUDKUHDEFRCUFUDSTUAUB $.
      $( [7-Oct-2014] $)
  $}

  ${
    weqi.1 $e |- R |= : A al $.
    weqi.2 $e |- R |= : B al $.
    $( Type of an equality. $)
    weqi $p |- R |= : [ A = B ] bool $=
      ( hb ke ht kty weq a1s wov ) AAGBCHDAAGIIHJABJDEAKLEFM $.
      $( [8-Oct-2014] $)
  $}

  ${
    eqid.1 $e |- R |= : A al $.
    $( Reflexivity of equality. $)
    eqid $p |- R |= [ A = A ] $=
      ( ke kty kc ax-refl syl dfi2 ) BBECCABFEBGBGDABHIJ $.
      $( [7-Oct-2014] $)

    eqtypri.2 $e |- R |= [ B = A ] $.
    eqtypri $p |- R |= : B al $=
      ( kty ke kc dfi1 ax-typeq syl mpbirx ) ABGZACGZDEDHCIBIHOINICBHDFJACBKLM
      $.
      $( [7-Oct-2014] $)
  $}

  ${
    ded.1 $e |- R |= : S bool $.
    ded.2 $e |- R |= : T bool $.
    ded.3 $e |- ( R , S ) |= T $.
    ded.4 $e |- ( R , T ) |= S $.
    $( Deduction theorem for equality. $)
    ded $p |- R |= [ S = T ] $=
      ( ke ax-ded dfi2 ) BCHAABCFGIJ $.
      $( [7-Oct-2014] $)
  $}

  ${
    eqtru.1 $e |- R |= A $.
    $( If a statement is provable, then it is equivalent to truth. $)
    eqtru $p |- R |= [ T. = A ] $=
      ( kt hb kty wtru a1s ax-cb2 adantr kct wcti simpr tru ded ) BDAEDFABCGHZA
      BCIZBDACPJDABAKBABAQLMNHO $.
      $( [8-Oct-2014] $)
  $}

  ${
    eqcomi.1 $e |- R |= : A al $.
    eqcomi.2 $e |- R |= [ A = B ] $.
    $( Commutativity of equality. $)
    eqcomi $p |- R |= [ B = A ] $=
      ( ke dfi1 eqcomx dfi2 ) CBGDABCDEBCGDFHIJ $.
      $( [7-Oct-2014] $)

    eqtypi $p |- R |= : B al $=
      ( eqcomi eqtypri ) ABCDEABCDEFGH $.
      $( [7-Oct-2014] $)
  $}

  ${
    mpbir.1 $e |- R |= A $.
    mpbir.2 $e |- R |= [ B = A ] $.
    $( Deduction from equality inference. $)
    mpbir $p |- R |= B $=
      ( ke dfi1 mpbirx ) ABCDBAFCEGH $.
      $( [7-Oct-2014] $)
  $}

  ${
    ceq12.1 $e |- R |= : F ( al -> be ) $.
    ceq12.2 $e |- R |= : A al $.
    ${
      ceq12.3 $e |- R |= [ F = T ] $.
      ${
        ceq12.4 $e |- R |= [ A = B ] $.
        $( Equality theorem for combination. $)
        ceq12 $p |- R |= [ ( F A ) = ( T B ) ] $=
          ( kc ke kbr ht kty df-i a1s ax-eqmp ax-ceq syl2anc dfi2 ) ECLZGDLZ
          MFMUCLUDLFMELGLZMCLDLZEGMNZUEFJMUGLUELABOEPZFHEGMQRSCDMNZUFFKMUILUFLU
          HFHCDMQRSCDEGTUAUB $.
          $( [7-Oct-2014] $)
      $}
  
      $( Equality theorem for combination. $)
      ceq1 $p |- R |= [ ( F A ) = ( T A ) ] $=
        ( eqid ceq12 ) ABCCDEFGHIACEHJK $.
        $( [7-Oct-2014] $)
    $}

    ceq2.3 $e |- R |= [ A = B ] $.
    $( Equality theorem for combination. $)
    ceq2 $p |- R |= [ ( F A ) = ( F B ) ] $=
      ( ht eqid ceq12 ) ABCDEFEGHABJEFGKIL $.
      $( [7-Oct-2014] $)
  $}

  ${
    $d x R $.
    leq.1 $e |- ( R , : x al ) |= [ A = B ] $.
    $( Equality theorem for lambda abstraction. $)
    leq $p |- ( R , : x al ) |= [ \ x A = \ x B ] $=
      ( kl ke tv kty kct dfi1 ax-abs dfi2 ) BCGBDGHEABIJKZABCDECDHOFLMN $.
      $( [8-Oct-2014] $)
  $}

  ${
    beta.1 $e |- R |= : x al $.
    beta.2 $e |- R |= : A be $.
    $( Axiom of beta-substitution. $)
    beta $p |- R |= [ ( \ x A x ) = A ] $=
      ( kl tv kc ke kty ax-beta syl2anc dfi2 ) CDHCIZJZDKEKQJDJEAPLBDLFGABCDMNO
      $.
      $( [8-Oct-2014] $)
  $}

  ${
    distrc.1 $e |- R |= : x al $.
    distrc.2 $e |- R |= : F ( be -> ga ) $.
    distrc.3 $e |- R |= : A be $.
    distrc.4 $e |- R |= : B al $.
    $( Distribution of combination over substitution. $)
    distrc $p |- R |= [ ( \ x ( F A ) B ) = ( ( \ x F B ) ( \ x A B ) ) ] $=
      ( kc kl ke tv kty ht kct jca ax-distrc syl2anc dfi2 ) DGEMNFMZDGNFMDENFMM
      ZOHOUDMUEMHADPQZBCRGQZSBEQZAFQZSHUFUGIJTHUHUIKLTABCDEFGUAUBUC $.
      $( [8-Oct-2014] $)
  $}

  ${
    $d y B $.
    distrl.1 $e |- R |= : x al $.
    distrl.2 $e |- ( R , : y be ) |= : A ga $.
    distrl.3 $e |- R |= : B al $.
    $( Distribution of lambda abstraction over substitution. $)
    distrl $p |- ( R , : y be ) |= [ ( \ x \ y A B ) = \ y ( \ x A B ) ] $=
      ( kl kc ke tv kty kct wtti ct1 adantr jca ax-distrl syl2anc dfi2 ) DEFLLG
      MZEDFLGMLZNHBEOZPZQZNUEMUFMUIADOPZUHQCFPZAGPZQHUJUHIBUJHUGIRZSUIUKULJHUHU
      LKUMTUAABCDEFGUBUCUD $.
      $( [8-Oct-2014] $)
  $}

  ${
    eqtri.1 $e |- R |= : A al $.
    eqtri.2 $e |- R |= [ A = B ] $.
    eqtri.3 $e |- R |= [ B = C ] $.
    $( Transitivity of equality. $)
    eqtri $p |- R |= [ A = C ] $=
      ( ke kc dfi1 hb ht kty weq a1s wc eqtypi ceq2 mpbi dfi2 ) BDIEIBJZCJUBDJEB
      CIEGKALCDUBEAALMZIEBAUCMINABNEFAOPFQABCEFGRHSTUA $.
      $( [7-Oct-2014] $)
  $}

  ${
    3eqtr4i.1 $e |- R |= : A al $.
    3eqtr4i.2 $e |- R |= [ A = B ] $.
    3eqtr4i.3 $e |- R |= [ S = A ] $.
    3eqtr4i.4 $e |- R |= [ T = B ] $.
    $( Transitivity of equality. $)
    3eqtr4i $p |- R |= [ S = T ] $=
      ( eqtypri eqtypi eqcomi eqtri ) AEBFDABEDGIKIABCFDGHAFCDACFDABCDGHLJKJMNN
      $.
      $( [7-Oct-2014] $)
  $}

  ${
    oveq.1 $e |- R |= : F ( al -> ( be -> ga ) ) $.
    oveq.2 $e |- R |= : A al $.
    oveq.3 $e |- R |= : B be $.
    ${
      oveq123.4 $e |- R |= [ F = S ] $.
      oveq123.5 $e |- R |= [ A = C ] $.
      oveq123.6 $e |- R |= [ B = T ] $.
      $( Equality theorem for binary operation. $)
      oveq123 $p |- R |= [ [ A F B ] = [ C S T ] ] $=
        ( kc kbr wc ke ht ceq12 kty df-i a1s dfi2 3eqtr4i ) CGDQZEQZIFQZJQZHDEGR
        ZFJIRZBCUHHEABCUAZGHDKLSZMSBCEJUHHUJUOMAUNDFGHIKLNOUBPUBULUITHTULQUIQAD
        UCZHLDEGUDUEUFUMUKTHTUMQUKQUPHLFJIUDUEUFUG $.
        $( [7-Oct-2014] $)
    $}

    ${
      oveq1.4 $e |- R |= [ A = C ] $.
      $( Equality theorem for binary operation. $)
      oveq1 $p |- R |= [ [ A F B ] = [ C F B ] ] $=
        ( ht eqid oveq123 ) ABCDEFGHGEIJKABCMMGHINLBEHKNO $.
        $( [7-Oct-2014] $)

      oveq12.5 $e |- R |= [ B = T ] $.
      $( Equality theorem for binary operation. $)
      oveq12 $p |- R |= [ [ A F B ] = [ C F T ] ] $=
        ( ht eqid oveq123 ) ABCDEFGHGIJKLABCOOGHJPMNQ $.
        $( [7-Oct-2014] $)
    $}
  
    ${
      oveq2.4 $e |- R |= [ B = T ] $.
      $( Equality theorem for binary operation. $)
      oveq2 $p |- R |= [ [ A F B ] = [ A F T ] ] $=
        ( eqid oveq12 ) ABCDEDFGHIJKADGJMLN $.
        $( [7-Oct-2014] $)
    $}
  
    ${
      oveq.4 $e |- R |= [ F = S ] $.
      $( Equality theorem for binary operation. $)
      oveq $p |- R |= [ [ A F B ] = [ A S B ] ] $=
        ( eqid oveq123 ) ABCDEDFGHEIJKLADGJMBEGKMN $.
        $( [7-Oct-2014] $)
    $}
  $}

  $( ` x ` is bound in ` \ x A ` . $)
  ax-hbl1 $a |- ( ( : A be , : B al ) , : x al ) |=
    [ ( \ x \ x A B ) = \ x A ] $.

  ${
    hbl1.1 $e |- ( R , : x al ) |= : A be $.
    $( Inference form of ~ ax-17 . $)
    hbl1 $p |- ( R , ( : x al , : B al ) ) |= [ ( \ x \ x A B ) = \ x A ] $=
      ( kl kc ke kbr tv kty kct kt wtt wct simpl adantl syl2anc ax-cb1 wctrl hb
      a1i simpr jca ax-hbl1 ) CCDHZHEIUHJKFACLZMZAEMZNZNZBDMZUKNUJUMUNUKUNUMFUJ
      FULOFULOFUJUNFUJNGUAAUIPZUBZOUJUKUOAEPQZQRULFUJUJUKUQRUCFMULUQUPUDZSZGTUL
      FUKUJUKUQUEURSUFUSABCDEUGT $.
      $( [8-Oct-2014] $)
  $}

  ${
    $d x A $.
    $( If ` x ` does not appear in ` A ` , then any substitution to ` A `
       yields ` A ` again, i.e. ` \ x A ` is a constant function. $)
    ax-17 $a |- ( ( : A be , : B al ) , : x al ) |= [ ( \ x A B ) = A ] $.

    a17i.1 $e |- R |= : A be $.
    $( Inference form of ~ ax-17 . $)
    a17i $p |- ( R , ( : x al , : B al ) ) |= [ ( \ x A B ) = A ] $=
      ( kl kc ke kbr tv kty kct hb kt wtt wct a1s adantl adantr simpr jca simpl
      ax-cb1 ax-17 syl2anc ) CDHEIDJKFACLZMZAEMZNZNZBDMZUJNUIULUMUJFUKUMGOUKMUM
      FGPUIUJAUHQAEQRZSUAUKFUJUIUJUNUBZOFMUJUKUOUMFGUESZTUCUKFUIUIUJUNUDUPTABCD
      EUFUG $.
      $( [8-Oct-2014] $)
  $}

  ${
    $d x R $.
    hbxfr.1 $e |- ( R , : x al ) |= : T be $.
    hbxfr.2 $e |- ( R , : x al ) |= [ T = A ] $.
    hbxfr.3 $e |- ( R , ( : x al , : B al ) ) |= [ ( \ x A B ) = A ] $.
    $( Transfer a hypothesis builder to an equivalent expression. $)
    hbxfr $p |- ( R , ( : x al , : B al ) ) |= [ ( \ x T B ) = T ] $=
      ( kl kc kty kct kt wtt wct syl2anc ke kbr tv simpl hb ax-cb1 wctrl adantl
      a1i eqtypi wl simpr wc leq ceq1 3eqtr4i ) BCDKZELZDFACUAZMZAEMZNZNZCGKZEL
      GABUOVAEABCVADUTFURURUSOURUSAUQPZAEPQZUBUCFMUTVDOFURBGMZFURNZHUDVCUEZUGZU
      FZBDMVAFURFUTOFUTVGVDQZUBZVIBGDVFHIUHRUIUTFUSURUSVDUJVHUFZUKUPDSTVAFUTVKF
      UTVJUJJRABEVBVAUOABCVAGVIVEVAFURVKVIHRUIVLVBUOSTVAFURVKVIACGDFIULRUMGDSTV
      AFURVKVIIRUN $.
      $( [8-Oct-2014] $)
  $}

  ${
    $d x R $.
    hbth.1 $e |- ( R , : x al ) |= A $.
    $( Hypothesis builder for a theorem. $)
    hbth $p |- ( R , ( : x al , : B al ) ) |= [ ( \ x A B ) = A ] $=
      ( hb kt tv kty kct ax-cb2 ax-cb1 wtru a1i eqtru eqcomi wtt wctrl a17i
      hbxfr ) AGBHDECCEABIZJZKZFLGHCUDGHJZUDCUDFMZNOCUDFPQAGBHDEUEEHEUCUFAUBRSN
      OTUA $.
      $( [8-Oct-2014] $)
  $}

  ${
    $d x R $.
    hbc.1 $e |- ( R , : x al ) |= : F ( be -> ga ) $.
    hbc.2 $e |- ( R , : x al ) |= : A be $.
    hbc.3 $e |- ( R , ( : x al , : B al ) ) |= [ ( \ x F B ) = F ] $.
    hbc.4 $e |- ( R , ( : x al , : B al ) ) |= [ ( \ x A B ) = A ] $.
    $( Hypothesis builder for combination. $)
    hbc $p |- ( R , ( : x al , : B al ) ) |= [ ( \ x ( F A ) B ) = ( F A ) ] $=
      ( kc kl kty kct kt wtt wct wc tv simpl hb ax-cb1 wctrl a1i adantl syl2anc
      ht wl simpr distrc eqtypri ceq12 eqtri ) CDGEMZNZFMDGNZFMZDENFMZMUPHADUAZ
      OZAFOZPZPZACUQVEFACDVEUPVDHVBVBVCQVBVCAVARZAFRSZUBUCHOVDVGQHVBBCUIZGOZHVB
      PIUDVFUEZUFZUGZBCGVEEVIVEHVBHVDQHVDVJVGSUBZVLIUHZBEOVEHVBVMVLJUHZTUJVDHVC
      VBVCVGUKVKUGZTABCDEFGVEVLVNVOVPULBCUTEUSVEGAVHURVEFAVHDVEGVLVNUJVPTBEUTVE
      VOLUMKLUNUO $.
      $( [8-Oct-2014] $)
  $}

  ${
    $d x R $.
    hbov.1 $e |- ( R , : x al ) |= : F ( be -> ( ga -> de ) ) $.
    hbov.2 $e |- ( R , : x al ) |= : A be $.
    hbov.3 $e |- ( R , : x al ) |= : C ga $.
    hbov.4 $e |- ( R , ( : x al , : B al ) ) |= [ ( \ x F B ) = F ] $.
    hbov.5 $e |- ( R , ( : x al , : B al ) ) |= [ ( \ x A B ) = A ] $.
    hbov.6 $e |- ( R , ( : x al , : B al ) ) |= [ ( \ x C B ) = C ] $.
    $( Hypothesis builder for binary operation. $)
    hbov $p |- ( R , ( : x al , : B al ) ) |=
      [ ( \ x [ A F C ] B ) = [ A F C ] ] $=
      ( kc kbr kty ke tv kct wov ht kt df-i dfi2 a1s wc hbc hbxfr ) ADEIFQZHQZG
      JFHIRZBCDFHIJAEUASUBZKLMUCUNUMTRBCDUDZUDISUOKUNUMTUEFHIUFUGUHACDEHGULJBUP
      IUOFKLUIMABUPEFGIJKLNOUJPUJUK $.
      $( [8-Oct-2014] $)
  $}

  ${
    $d x y R $.
    hbl.1 $e |- ( R , ( : x al , : y be ) ) |= : A ga $.
    hbl.2 $e |- ( ( R , : y be ) , ( : x al , : B al ) ) |=
      [ ( \ x A B ) = A ] $.
    $( Hypothesis builder for lambda abstraction. $)
    hbl $p |- ( ( R , : y be ) , ( : x al , : B al ) ) |=
      [ ( \ x \ y A B ) = \ y A ] $=
      ( kl kc ke kbr tv kty kct kt wtt wct ht simpl hb ax-cb1 wctrl adantl wtti
      a1i simpr ct1 simpld simprd adantr syl2anc wl wc distrl an32s leq eqtri )
      DEFKZKZGLZVAMNHADOZPZAGPZQZBEOZPZBCUAZVCEDFKGLZKVAHVGQZVIQZAVJVBVMGAVJDVM
      VAVMVEVIVLVEVIVGHVEVEVFRVEVFAVDSZAGSTZUBUCHPVGVORHVEVIQZCFPZHVPQIUDRVEVIV
      NBVHSTUEZUHZUFZBVFVLVHVGHVFVEVFVOUIVSUFZUGZUJZUKBCEVMFVMVEVIWCULVQVMHVPVL
      VIHHVGRHVGVRVOTUBWBUMWCIUNZUOUOVLVIVFWAWBUMUPABCDEFGVLVTWDWAUQBEVKFVLVKFM
      NHVIVGJURUSUTUR $.
      $( [8-Oct-2014] $)
  $}

  ${
    $d x y R $.
    ax-inst.1 $e |- ( R , S ) |= A $.
    ax-inst.2 $e |- ( R , ( : x al , : y al ) ) |= [ ( \ x B y ) = B ] $.
    ax-inst.3 $e |- ( R , ( : x al , : y al ) ) |= [ ( \ x T y ) = T ] $.
    ax-inst.4 $e |- ( ( R , : x al ) , [ x = C ] ) |= [ A = B ] $.
    ax-inst.5 $e |- ( ( R , : x al ) , [ x = C ] ) |= [ S = T ] $.
    $( Instantiate a theorem with a new term.  The second and third hypotheses
       are the HOL equivalent of set.mm "effectively not free in" predicate
       (see set.mm's ax-17). $)
    ax-inst $a |- ( R , T ) |= B $.
  $}

  ${
    $d x y R $.
    insti.1 $e |- R |= A $.
    insti.2 $e |- R |= : C al $.
    insti.3 $e |- R |= : B bool $.
    insti.4 $e |- ( R , ( : x al , : y al ) ) |= [ ( \ x B y ) = B ] $.
    insti.5 $e |- ( ( R , : x al ) , [ x = C ] ) |= [ A = B ] $.
    $( Instantiate a theorem with a new term. $)
    insti $p |- R |= B $=
      ( kt hb kty wtru a1s tv kct ke ax-cb1 tru a1i a17i kbr eqid ax-inst mpdan
      adantr ) GMEJMGDGHUAUBUCABCDEFGMMGMDHNMOZDGHPQZUIKANBMCRGUKUDLNMGABRZOSUL
      FTUESZUJDETUEUMLPQUFUGUH $.
      $( [8-Oct-2014] $)
  $}

  ${
    $d x y R $.
    clf.1 $e |- ( R , : x al ) |= : A be $.
    clf.2 $e |- ( R , : x al ) |= : B be $.
    clf.3 $e |- ( R , : x al ) |= : C al $.
    clf.4 $e |- ( ( R , : x al ) , [ x = C ] ) |= [ A = B ] $.
    clf.5 $e |- ( R , ( : x al , : y al ) ) |= [ ( \ x B y ) = B ] $.
    clf.6 $e |- ( R , ( : x al , : y al ) ) |= [ ( \ x C y ) = C ] $.
    $( Evaluate a lambda expression. $)
    clf $p |- ( R , : x al ) |= [ ( \ x A C ) = B ] $=
      ( tv kc ke kbr kty hb kl kct ax-cb1 simpr beta ht weq a1s wl wc wtt wctrl
      kt a1i a17i hbl1 hbc hbov hbth weqi adantr ceq2 oveq12 wtti eqid ax-inst
      ) ACDCEUAZCOZPZEQRVGGPZFQRGHAVHSZVKABCEHVKUBZHVKBESZVLIUCZUDZIUEABBTCVJDO
      ZFQHBBTUFUFZQSZVMVLIBUGZUHABVGVLGABCVLEVOIUIZKUJJAVQCQVPHVRHUMHVKVNAVHUKU
      LVSUNUOAABCGVPVGHVTKABCEVPHIUPNUQMURACVKVPHVOUSBBTVIEVJQVLVHGQRZUBZFVREFQ
      RZWBLVSUHABVGWBVHABCWBEVLWAVKVOAVHGVLVOKUTZVAZVLWAVMIWDVAZUIZWEUJWFABVHGV
      GWBWGWEVLWAWCWBLUCUDVBLVCTVKWBAWCWBVHLVDVEVF $.
      $( [8-Oct-2014] $)
  $}

  ${
    $d x y R $.  $d x B $.  $d x C $.
    cl.1 $e |- ( R , : x al ) |= : A be $.
    cl.2 $e |- R |= : C al $.
    cl.3 $e |- R |= : B be $.
    cl.4 $e |- ( ( R , : x al ) , [ x = C ] ) |= [ A = B ] $.
    $( Evaluate a lambda expression. $)
    cl $p |- ( R , : x al ) |= [ ( \ x A C ) = B ] $=
      ( vy tv kty hb wtt a1s adantr a17i clf ) ABCLDEFGHGACMZNZBENJOUBNAFNZGIAU
      APQZRGUBUCIUDRKABCELMZGJSAACFUEGIST $.
      $( [8-Oct-2014] $)
  $}

  ${
    $d x y R $.  $d x B $.  $d x C $.
    ovl.1 $e |- ( R , ( : x al , : y be ) ) |= : A ga $.
    ovl.2 $e |- ( R , : y be ) |= : B ga $.
    ovl.3 $e |- R |= : C ga $.
    ovl.4 $e |- R |= : S al $.
    ovl.5 $e |- R |= : T be $.
    ovl.6 $e |- ( ( R , ( : x al , : y be ) ) , [ x = S ] ) |= [ A = B ] $.
    ovl.7 $e |- ( ( R , ( : x al , : y be ) ) , [ y = T ] ) |= [ B = C ] $.
    $( Evaluate a lambda expression in a binary operation. $)
    ovl $p |- ( R , ( : x al , : y be ) ) |= [ [ S \ x \ y A T ] = C ] $=
      ( kty adantr kl kbr kc tv kct ht kt wtt wct simpl ax-cb1 a1i adantl simpr
      hb wl wtti wov ke df-i dfi2 a1s anassrs wc distrl ceq1 anasss eqtri an32s
      weqi syldan id sylan cl ) CJKDEFUAZUAZUBZEDFUAZJUCZUAZKUCZHIADUDZSZBEUDZS
      ZUEZUEZABCJKVPWGABCUFZDWGVOWFIWCWCWEUGWCWEAWBUHZBWDUHZUIZUJUOISWFWKCHSZIN
      UKZULZUMBCEWGFWFIWEWCWEWKUNWNUMLUPUPIWFAJSZOIWCWEAWLIWBNUQZBWLIWDNUQZUIZT
      IWFBKSZPWRTURZCVQVPJUCZKUCZWAWGWTVQXBUSUBCFSZWGLVQXBUSUGJKVPUTVAVBXBWAUSU
      BIWCWEBCKXAIWCUEZWEUEZVTAWHVPXEJAWHDXEVOXDWEWCIWCUGIWCWMWIUIZUNZUOWESXDXF
      WJULZTZBCEXEFXDWEXCXEXCIWCWELVCZUKUNZXJUPUPXDWEWOIWCWOOWPTZXHTZVDXDWEWSIW
      CWSPWPTZXHTZABCDEFJXDXGXJXLVEVFVGVHWAHUSUBIWCWEBCEVSHKXDACVRXEJACDXEFXIXJ
      UPXMVDZXNIWCWLNWPTCVSGHXEWDKUSUBZUEXEXQCVSSXPBWDKXEXKXOVJZTXEXQVSGUSUBZXS
      IWEWCACDFGJIWEUEZXCIWCWEXJVIIWEWOOWQTZCGSIWEWEIWEWOXTYAUKUNMVKFGUSUBXTWCU
      EWGWBJUSUBWGIWCWEWGIWCWEWGXCWGLUKVLVCZVIQVMVNVIXRTGHUSUBXEWGXQYBRVMVHVNVG
      VH $.
      $( [8-Oct-2014] $)
  $}

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
                 Add propositional calculus definitions
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

  $c F. $.   $( Contradiction term $)
  $c /\ $.   $( Conjunction term $)
  $c ~ $.    $( Negation term $)
  $c ==> $.  $( Implication term $)
  $c ! $.    $( For all term $)
  $c ? $.    $( There exists term $)
  $c \/ $.   $( Disjunction term $)
  $c ?! $.   $( There exists unique term $)

  $( Contradiction term. $)
  tfal $a term F. $.
  $( Conjunction term. $)
  tan $a term /\ $.
  $( Negation term. $)
  tne $a term ~ $.
  $( Implication term. $)
  tim $a term ==> $.
  $( For all term. $)
  tal $a term ! $.
  $( There exists term. $)
  tex $a term ? $.
  $( Disjunction term. $)
  tor $a term \/ $.
  $( There exists unique term. $)
  teu $a term ?! $.

  ${
    $d f p q x y $.
    $( Define the for all operator. $)
    df-al $a |- ( : p ( al -> bool ) , : x al ) |=
      [ ! = \ p [ p = \ x T. ] ] $.

    $( Define the constant false. $)
    df-fal $a |- : p bool |= [ F. = ( ! \ p p ) ] $.

    $( Define the 'and' operator. $)
    df-an $a |- ( ( : p bool , : q bool ) ,
      : f ( bool -> ( bool -> bool ) ) ) |=
        [ /\ = \ p \ q [ \ f [ p f q ] = \ f [ T. f T. ] ] ] $.

    $( Define the implication operator. $)
    df-im $a |- ( : p bool , : q bool ) |=
      [ ==> = \ p \ q [ [ p /\ q ] = p ] ] $.

    $( Define the negation operator. $)
    df-not $a |- : p bool |= [ ~ = \ p [ p ==> F. ] ] $.

    $( Define the existence operator. $)
    df-ex $a |- ( ( : p ( al -> bool ) , : q bool ) , : x al ) |=
      [ ? = \ p ( ! \ q [ ( ! \ x [ ( p x ) ==> q ] ) ==> q ] ) ] $.

    $( Define the 'or' operator. $)
    df-or $a |- ( ( : p bool , : q bool ) , : x bool ) |=
      [ \/ = \ p \ q ( ! \ x [ [ p ==> x ] ==> [ [ q ==> x ] ==> x ] ] ) ] $.

    $( Define the 'exists unique' operator. $)
    df-eu $a |- ( ( : x al , : y al ) , : p ( al -> bool ) ) |=
      [ ?! = \ p ( ? \ y ( ! \ x [ ( p x ) = [ x = y ] ] ) ) ] $.
  $}

  ${
    ax-ex.1 $e |- R |= : x al $.
    ax-ex.2 $e |- R |= : A al $.
    $( Axiom of existence. This is a modified version of Metamath's ax-9 for
       type theory. One way to interpret this is that the set variables ` x `
       range over the entire domain of the type ` al ` , so any term which has
       type ` al ` is equal to some value for a set variable of type ` al ` .
       $)
    ax-ex $a |- R |= [ [ \ x [ x = A ] = \ x F. ] = F. ] $.
  $}

  ${
    $d x R $.  $d x A $.
    ax-type.1 $e |- ( R , : x al ) |= A $.
    $( Types are non-empty, so we can eliminate an assumption that a dummy
       variable ` x ` has type ` al ` as long as it is not present in the
       theorem. $)
    ax-type $a |- R |= A $.
  $}

  ${
    $d x A $.
    typei.1 $e |- : x al |= A $.
    $( Inference form of ~ ax-type . $)
    typei $p |- T. |= A $=
      ( kt tv kty hb wtt wtru a1i adantl ax-type ) ABCEABFZGZECDHEGOANIJKLM $.
      $( [8-Oct-2014] $)
  $}

  ${
    $( For all type. $)
    wal $p |- T. |= : ! ( ( al -> bool ) -> bool ) $=
      ( vp vx hb ht tal kty tv kt kl ke kbr kct wtt wct simpl simpr wtru a1s wl
      weqi df-al eqtypri ax-type typei ) ADEZBUFDEZFGZACUHUFBHZGZUGBUICIJZKLZJF
      UJACHZGZMZUFDBUOULUJUNIUJUNUFUINAUMNOZPZUFUIUKUOUQADCUOIUJUNUPQZDIGUNUOUR
      RSTUATACBUBUCUDUE $.
      $( [8-Oct-2014] $)

    $( Contradiction type. $)
    wfal $p |- T. |= : F. bool $=
      ( vx hb tfal kty tal tv kl kc ht wtt wal a1i id wl df-fal eqtypri typei
      wc ) BABCDBEAAFZGZHCBSDZBBIZBEUATUBBIEDUABSJZBKLBBAUASUAUCMZUDNRAOPQ $.
      $( [8-Oct-2014] $)

    $( Conjunction type. $)
    wan $p |- T. |= : /\ ( bool -> ( bool -> bool ) ) $=
      ( vp vq vf hb ht tan kty tv kct kbr kl kt wtt wct a1s adantr simpr wov wl
      ax-type ke simpl wtru weqi df-an eqtypri typei ) DADDDEZEZFGZDBUJDAHZGZUI
      CUJULDBHZGZIZUIABCUKUMCHZJZKZCLLUPJZKZUAJZKZKFUOUIUPGZIZDUHAVDVBUOVCULULU
      NLULUNDUKMDUMMNZUBZDVCGULUOVFUIUPMZOZPZDDBVDVAUOVCUNULUNVEQVHPZUIDEURUTVD
      UIDCVDUQUOVCLUOVCVEVGNQZDDDUKUMUPVDVKVIVJRSUIDCVDUSVKDDDLLUPVDVKDLGVCVDVK
      UCOZVLRSUDSSCABUEUFTTUG $.
      $( [8-Oct-2014] $)

    $( Implication type. $)
    wim $p |- T. |= : ==> ( bool -> ( bool -> bool ) ) $=
      ( vp vq hb ht tim kty tv tan kbr ke kl kct wtt wct simpl ax-cb1 simpr wan
      kt wl a1s wov weqi df-im eqtypri ax-type typei ) CACCCDZDZEFZCBUJCAGZFZUI
      ABUKBGZHIZUKJIZKZKEULCUMFZLZCUHAURUPULUQSULUQCUKMCUMMNOZCCBURUOULUQULURUS
      PQZCUNUKURCCCUKUMHURUIHFUQURUTRUAUSUTUBUSUCTTABUDUEUFUG $.
      $( [8-Oct-2014] $)

    $( Negation type. $)
    wnot $p |- T. |= : ~ ( bool -> bool ) $=
      ( vx hb ht tne kty tv tfal tim kbr kl wtt wim a1s wfal wov df-not eqtypri
      id wl typei ) BABBCZDEUAAAFZGHIZJDBUBEZBBAUDUCUDBUBKRZBBBUBGHUDBUACHEUDUD
      UELMUEBGEUDUDUENMOSAPQT $.
      $( [8-Oct-2014] $)

    $( There exists type. $)
    wex $p |- T. |= : ? ( ( al -> bool ) -> bool ) $=
      ( vp vq vx hb ht tex kty tv kct tal kc tim kbr kl wtt adantr a1s wc wl kt
      wct simpl wtti wal simpr wim ax-cb1 wov df-ex eqtypri ax-type typei ) AEF
      ZBUNEFZGHZECUPUNBIZHZADUPURECIZHZJZUOBKCKDUQDIZLZUSMNZOZLZUSMNZOZLZOGVAAV
      BHZJZUNEBVKVIVAVJURURUTUAURUTUNUQPEUSPUBZUCZAURVAVBVMUDZQZEEFZEKVKVHVPEFK
      HURVKVOEUEREECVKVGVAVJUTURUTVLUFVNQZEEEVFUSMVKVAVJEVPFMHZVRURVAVMUGRVNQUN
      EKVKVEUOKHURVKVOAUERAEDVKVDVAVJURVKVOUHUFZEEEVCUSMVKVRURVKVOUGRAEUQVKVBVO
      VSSVQUITSVQUITSTADBCUJUKULULUM $.
      $( [8-Oct-2014] $)

    $( Disjunction type. $)
    wor $p |- T. |= : \/ ( bool -> ( bool -> bool ) ) $=
      ( vp vq vx hb ht tor kty tv kct tal tim kbr kl wtt adantr a1s wov ax-type
      simpr wl kc kt wct simpl wtti wal ax-cb1 wim wc df-or eqtypri typei ) DAD
      DDEZEZFGZDBUODAHZGZDCUOUQDBHZGZIZUNABJCUPCHZKLZURVAKLZVAKLZKLZMZUAZMZMFUT
      DVAGZIZDUMAVJVHUTVIUQUQUSUBUQUSDUPNDURNUCZUDZDUQUTVAVLUEZOZDDBVJVGUTVIUSU
      QUSVKSVMOZUMDJVJVFUMDEJGUQVJVNDUFPDDCVJVEUTVIUQVJVNUGSZDDDVBVDKVJUNKGUQVJ
      VNUHPZDDDUPVAKVJVQVNVPQDDDVCVAKVJVQDDDURVAKVJVQVOVPQVPQQTUITTCABUJUKRRUL
      $.
      $( [8-Oct-2014] $)

    $( There exists unique type. $)
    weu $p |- T. |= : ?! ( ( al -> bool ) -> bool ) $=
      ( vx vy vp hb ht teu kty tv kct tex tal kc ke kbr kl wtt simpr wc wl wtti
      kt wct wcti wex a1s adantr wal simpl weqi df-eu eqtypri ax-type typei ) A
      BAEFZEFZGHZACUQABIZHZUODUQUSACIZHZJZUPDKCLBDIZURMZURUTNOZNOZPZMZPZMZPGVBU
      OVCHZJZUOEDVLVJVBVKVBVKUOVAVBVCUSVAUBUSVAAURQAUTQUCZRZUAZUDRZUOEKVLVIUPKH
      VKVLVPAUEUFAECVLVHVBVKVAVNVOUGZUOELVLVGUPLHVKVLVPAUHUFAEBVLVFVBVKUSUSVAVM
      UIVOUGZEVDVEVLAEVCVLURVPVRSAURUTVLVRVQUJUJTSTSTABCDUKULUMUMUN $.
      $( [8-Oct-2014] $)
  $}

  ${
    axex.1 $e |- R |= : x al $.
    axex.2 $e |- R |= : A al $.
    $( Axiom of existence ~ ax-ex , using abbreviations. $)
    axex $p |- R |= ( ? \ x [ x = A ] ) $=
      ? $.
  $}

  ${  
    alval.1 $e |- R |= : x al $.
    alval.2 $e |- R |= : F ( al -> bool ) $.
    $( Value of the for all predicate. $)
    alval $p |- R |= [ ( ! F ) = [ F = \ x T. ] ] $=
      ( vf hb ht tal kc kt kl ke kbr tv kty kct adantr a1s wtti wc ax-cb1 simpr
      wal df-al syl2anc ceq1 weq wtru wl wov weqi oveq1 cl eqtri ax-type ) AHIZ
      GJCKZCBLMZNOZNODHUSGGPZUTNOZMZCKVADURVBQZRZURHJVFCURHIZJQURCQZVFDVEVHFURA
      BPQZDVBEUAZSZAUETZVKUBURHCJVFVDVLVKJVDNOVFVEVIDVEVHVFVKUCUDZDVEVIEVJSZABG
      UFUGUHURHGVCVACDURURHVBUTNVFURVGINQZVHVFVKURUIZTZVMAHBVFLVNHLQZVHVFVKUJTU
      KULFURCUTDFAHBDLEVRVIDEUJTUKZUMURURHVBUTCNVFVBCNOZRZVOVEWAVFVTVEVMURURHVB
      CNVFVQVMVKULZSZVPTWCVFVTURUTQZDVEWDVSVJSWBSVFVTVEWAWCUCUDUNUOUPUQ $.
      $( [8-Oct-2014] $)
  $}

  ${
    imval.1 $e |- R |= : A bool $.
    $( Value of negation. $)
    notval $p |- R |= [ ( ~ A ) = [ A ==> F. ] ] $=
      ( vp hb tne kc tfal tim kbr ke kty kct wtti adantr a1s ax-cb1 wim simpr
      ht tv kl wnot wc df-not kt a1i adantl ceq1 wfal wov weqi oveq1 cl ax-type
      eqtri ) EDFAGZAHIJZKJBEUQDDUAZHIJZUBZAGURBEUSLZMZEEFVCAEETZFLEALZVCBVBVEC
      EVEBUSCNZOZUCPZVGUDEEAFVCVAVHVGVBBFVAKJDUEEBLZVBEVIUFUSVEBCQZNVJUGUHUIEED
      UTURABEEEUSHIVCEVDTILZVEVCVGRPBVBVEVCVGQSZBVBEHLZVMVEBCUJPZVFOUKCEEEAHIBV
      KVEBCRPCVNUKEEEUSHAIVCUSAKJZMZVKVBVPVCVOVBVLEUSAVCVLVGULOZRPZVQVMVKVPVRUJ
      PVCVOVBVPVQQSUMUNUPUO $.
      $( [8-Oct-2014] $)

    imval.2 $e |- R |= : B bool $.
    $( Value of the implication. $)
    imval $p |- R |= [ [ A ==> B ] = [ [ A /\ B ] = A ] ] $=
      ( vp vq hb tim kbr tan ke kty kct simpr adantr a1s wov wan weqi tv ax-cb1
      kl ht kt wtt wct wtti wim df-im syl2anc oveq anasss a1i syldan weq oveq12
      oveq1 oveq2 ovl anassrs eqtri ax-type ) HFABIJZABKJZALJZLJZCHGVGCHFUAZMZN
      ZHVDABFGVHGUAZKJZVHLJZUCUCZJZVFVJHVKMZNZHHHABIVQHHHUDUDZIMVIVQVJVPVICVIUE
      CVIHAMZCDUBZHVHUFUGZOZHVIVJVKWBUHZPZUIQZVJVPVSCVIVSDHVSCVHDUHZPZWCPZVJVPH
      BMZCVIWIEWFPWCPZRHHHABIVQVNWEWHWJIVNLJVQVIVPWDVJVPUEVJVPWAHVKUFZUGOZFGUJU
      KULVOVFLJCVIVPHHHFGVMAVKKJZALJVFCABHVLVHCVIVPNZNZHHHVHVKKWOVRKMZVPWOVPCVI
      VPWLUMZSQVICVIVPWDUMZWQRWRTHWMACVPNZHHHAVKKWSWPVPWSCVPUECVPVTWKUGOZSQCVPV
      SDHVPMCVTWKUNPZWTRVSCVPVPWTXAUOTHVEACHHHABKCWPVSCDSQDERDTDEHHHVLVHWMLWOVH
      ALJZNZAVRLMZVIXCWOXBVIWRHVHAWOWRVSCWNVIWRWGUOZTZPZHUPZQHHHVHVKKXCWPVIXCXG
      SQZXGWOXBVPWQXFPZRXGHHHVHVKAKXCXIXGXJWOXBVIXCXGUBOZURXKUQHHHWMAVELWOVKBLJ
      ZNZXDVSXMWOXLVSXEHVKBWOWQWICVIVPWJUMTZPZXHQZWOXLHWMMHHHAVKKWOWPVIWOWRSQXE
      WQRXNPXOHHHAVKKXMBWPVSXMXOSQXOWOXLVPWQXNPWOXLXDXMXPUBOUSURUTVAVBVCVC $.
      $( [9-Oct-2014] $)

    ${
      orval.3 $e |- R |= : x bool $.
      $( Value of the disjunction. $)
      orval $p |- R |= [ [ A \/ B ] =
        ( ! \ x [ [ A ==> x ] ==> [ [ B ==> x ] ==> x ] ] ) ] $=
        ( hb kbr tal tim ke kty kct adantr a1s wov ax-cb1 simpr wct vp vq tv kl
        tor kc ht wtti wor jca df-or syl2anc oveq wal wim anasss wl wc kt sylan
        wtt ct1 weqi simpld simpl a1i simprd oveq1 leq ceq2 oveq2 anassrs eqtri
        wcti ovl ax-type ) HUABCUEIZJABAUCZKIZCVRKIZVRKIZKIZUDZUFZLIZDHUBWEDHUA
        UCZMZNZHVQBCUAUBJAWFVRKIZUBUCZVRKIZVRKIZKIZUDZUFZUDUDZIZWDWHHWJMZNZHHHB
        CUEWSHHHUGZUGZUEMZHBMZWSWHWRXCDWGXCEHXCDWFEUHZOZHXCWHWJXEUHZOZUIPZXGWHW
        RHCMZDWGXIFXDOXFOZQZHHHBCUEWSWPXHXGXJUEWPLIWSWGWRNZHVRMZWSWGWRWHWRWGDWG
        XCWHXERSXFOZWHWRHVQMWSXKRSZUJWHWRXMDWGXMGXDOXFOAUAUBUKULUMWQWDLIDWGWRHH
        HUAUBWOJAVSWLKIZUDZUFZWDDBCWTHJDXLNZWNWTHUGJMZXMXSDXLXMGDWGWRXDHXCDWJEU
        HZTZOZHUNZPHHAXSWMYCHHHWIWLKXSXAKMZXMXSYCUOPZHHHWFVRKXSYFWGDWGWRXNUPZYC
        QHHHWKVRKXSYFHHHWJVRKXSYFWRDWGWRXOUPZYCQYCQQUQURWTHJDWRNZXQDWRXTXTXCDEX
        TXBUSUIYDPZPZYAOZHHAYIXPDWRXMGYAOZHHHVSWLKYIYEXTYIYLUOPZDWRHVSMHHHBVRKD
        YEXCDEUOPZEGQZYAOHHHWKVRKYIYNHHHWJVRKYIYNWRDXCXINZWRDXCXIEFUJZYQWRUSYQW
        RUSXCXIHBVAZHCVATZHWJVAZTSZUTYMQYMQQUQURWTHJDWCYKHHADWBGHHHVSWAKDYOYPHH
        HVTVRKDYOHHHCVRKDYOFGQGQQUQUREFWOXRLIXSWFBLIZNXCXLNZUUCNZXMXSUUDUUCDXCX
        LEYBVBHWFBXSYGDXLXCEYBOVCZVBXSUUCXMYCUUFOWTHWNXQJUUEXMNZXTUUGYEUUGYEWGU
        UGUUEXMWGUUDUUCWGUUDWGWRXCXLUSXCXLYSUSWGWRHWFVAUUATTSZVDZHWFBUUDUUIXCXL
        WGUUDUUIRVEVCZOZHWGUUEVRUUKUHZOZUOPZRZYDVFHHAUUGWMUUEXMUUOSZHHHWIWLKUUG
        UUNHHHWFVRKUUGUUNUUMUUPQZHHHWKVRKUUGUUNHHHWJVRKUUGUUNUUEXMWRUUDUUCWRUUD
        WGWRUUHVGUUJOUULOUUPQUUPQZQUQHAWMXPUUEHHHWIWLVSKUUGUUNUUQUURHHHWFVRBKUU
        GUUNUUMUUPUUEXMUUCUUDUUCWGUUEUUKRSUULOVHVHVIVJULXRWDLIXSWJCLIZNYQWRNZUU
        SNZXMXSUUTUUSXSYQWRDXLYQYRYBOZYHUJHWJCXSYHXSXCXIUVBVGVCZVBXSUUSXMYCUVCO
        WTHXQWCJUVAXMNZXTXMUVDUVAXMUVAXMHWRUVAVRUUTUUSWRUUBHWJCUUTUUBYQWRXIXCXI
        YTSHWRMYQYTUUAVFZOVCZOZUHZVNZSZYJPHHAUVDXPUVJHHHVSWLKUVDYEUVDUVIUOVFZHH
        HBVRKUVDUVKUVAXMXCUUTUUSXCYQWRXCXCXIYTVEUVEOUVFOUVHOUVJQZHHHWKVRKUVDUVK
        HHHWJVRKUVDUVKUVAXMWRUVGUVHOZUVJQZUVJQZQUQHAXPWBUVAHHHVSWLKUVDWAYEXMUVD
        UVAXMUSUVAXMHXMMUVAUVHRZHVRVATSZUOPZUVLUVOHHHWKVRVTKUVDUVRUVNUVQHHHWJVR
        CKUVDUVRUVMUVQUVAXMUUSUUTUUSUVPSUVHOVHVHVKVIVJULVOVLVMVPVP $.
        $( [9-Oct-2014] $)
    $}

    anval.3 $e |- R |= : f ( bool -> ( bool -> bool ) ) $.
    $( Value of the conjunction. $)
    anval $p |- R |= [ [ A /\ B ] = [ \ f [ A f B ] = \ f [ T. f T. ] ] ] $=
      ( hb kbr kt ke kty kct wct a1i adantr simpr simpld wov wl vp vq tan tv kl
      ax-cb1 wtt wan wtti jca ct1 simpl a1s wcti ax-simprd ax-syl anassrs df-an
      ht syl2anc oveq simprd wtru weqi weq anasss an32s oveq1 leq oveq2 ovl syl
      eqtri ax-type ) HUABCUCIZABCAUDZIZUEZAJJVPIZUEZKIZKIZDHUBWBDHUAUDZLZMZHVO
      BCUAUBAWCUBUDZVPIZUEZVTKIZUEUEZIZWAWEHWFLZMZHHHBCUCWMHHHUSUSZUCLWMJWEWLJD
      WDHBLZDEUFZHWCUGZNZHWFUGZNZUHOZWEWLWODWDWOEHWODWCEUIZPHWDWEWFDWDWRQZUIZPZ
      HCLZDWDWLDWDWLMZMZWOXFMZWNVPLZMZXGMZXFDXKXGDXIXJDWOXFEFUJGUJDWDWLXBHWLLZD
      WPWSONUKZXLWOXFXLXIXJXKXGXKXGHXGLZWOXKXIXJWOWOXFJWOXFHBUGHCUGNZULZHXJLZXI
      XPWNVPUGZOZPZJWDWLWQWSNZUMUNZULZRZUOZUPUQZSHHHBCUCWMWJXAXEYGUCWJKIWMXGXJW
      MWDWLWEWLWDXCXDPWEWLWTQUJWEWLXJDWDXJGXBPXDPAUAUBURUTVAWKWAKIZDWDWLXHXLYHX
      NHHHUAUBWIABWFVPIZUEZVTKIWAXKBCWNHUSZWHVTXLWNHAXLWGXLXIXJYDVBZHHHWCWFVPXL
      YLWDXLXIXGYEXKXGWOXLXLWOXFYERZUFQZXIXGMZWDWLXIXGJXIXGXPYBNQZRZUTXLWDWLYNV
      BZSTWNHAXLVSYLHHHJJVPXLYLHJLZXLYCVCOZYTSTVDYKYJVTXKWLMZWNHAUUAYIXKWLXJXIX
      JJXIXJXPXSNZQZXMXKUUBWSOZPZHHHBWFVPUUAUUEXKWLWOYAUUDPXKWLXJUUAUUEUFQSTXKW
      LYKVTLWNHAXKVSUUCHHHJJVPXKUUCYSXKUUBVCOZUUFSTZUUDPVDYKVRVTXKWNHAXKVQUUCHH
      HBCVPXKUUCYAXIXJXFWOXFXPQZXTPZSTUUGVDYAUUIYKYKHWHVTYJKXLWCBKIZMZYKYKHUSUS
      KLZUUJUUKXLUUJXLUUJHWCBXLXLWDWLXKXGJXKXGUUBYBNZQRXLWOXFXLXIXJXKXGUUMULRRV
      DUNQZYKVEZUMWNHAUUKWGUUKXIXJUUKXKXGXLUUJUUJUUKUUNUFZULZRVBZHHHWCWFVPUUKUU
      RUUKWDWLUUKXKXGUUQVBZRUUKWDWLUUSVBSTWNHAUUKVSUURHHHJJVPUUKUURYSUUKUUPVCOZ
      UUTSTWHYJKIZXKXGUUJUVAXIXGUUJMZXJWNAWGYIXIUVBMZHHHWCWFBVPUVCXJMZUVCXJWDUV
      DUVDWDWLUVCXJXGXGXIXGUUJYOUUJXGYPHWCBYOYQXIXGWOXQXOXIXPYBOZPZVDPVFZXRXGUV
      CUVGXSUMPZRZUFQUVIUVDWDWLUVHVBUUJXIXJUVBUUJXKXGUUJUUNVFVGVHVIVGUQVHYKYKHY
      JVTVRKXLWFCKIZMZUULWOUVKXLUVJWOYMHWFCXLYRYFVDZPZUUOUMWNHAUVKYIXLUVJXJYLUV
      LPZHHHBWFVPUVKUVNUVMXLUVJWLYRUVLPSTWNHAUVKVSUVNHHHJJVPUVKUVNYSWOUVKUVMVCU
      MZUVOSTYJVRKIZXKXGUVJUVPXIXGUVJMZXJWNAYIVQXIUVQMZHHHBWFVPUVRXJMZCUVRXJWOU
      VSUVRXJWOWOXIXGUVJYOUVJWOUVFHWFCYOYOWDWLYPVBZXIXGXFUUHUVEPVDZPVFZXRWOUVRU
      WBXSUMZPZUFQUWDUVRXJWLWLXIXGUVJYOUVJWLUVTUWAPVFUWCPUVJXIXJUVQUVJXKXGUVJXL
      UVJWOUVKUVMUFQVFVGVJVIVGUQVHVKVLUQVMVNVN $.
      $( [9-Oct-2014] $)
  $}

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
                       Add logical axioms (set theory)
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

  $c 1-1 $.   $( One-to-one function $)
  $c onto $.  $( Onto function $)
  $c @ $.     $( Indefinite descriptor $)

  $( One-to-one function. $)
  tf11 $a term 1-1 $.
  $( Onto function. $)
  tfo $a term onto $.
  $( Indefinite descriptor. $)
  tat $a term @ $.

  $( Define a one-to-one function. $)
  df-f11 $a |- ( : f ( al -> be ) , ( : x al , : y al ) ) |= [ 1-1 =
    \ f ( ! \ x ( ! \ y [ [ ( f x ) = ( f y ) ] ==> [ x = y ] ] ) ) ] $.

  $( Define an onto function. $)
  df-fo $a |- ( : f ( al -> be ) , ( : x al , : y be ) ) |= [ onto =
    \ f ( ! \ y ( ? \ x [ y = ( f x ) ] ) ) ] $.

  $( The eta-axiom: a function is determined by its values. $)
  ax-eta $a |- : f ( al -> be ) |=
    ( ! \ f [ \ x ( f x ) = f ] ) $.

  $( Defining property of the indefinite descriptor: it selects an element from
     any type. This is equivalent to global choice in ZF. $)
  ax-ac $a |- ( : p ( al -> bool ) , : x al ) |=
    ( ! \ p ( ! \ x [ ( p x ) ==> ( p ( @ p ) ) ] ) ) $.

  $( The axiom of infinity: the set of "individuals" is not Dedekind-finite.
     Using the axiom of choice to come, we can show that this is equivalent
     to an embedding of the natural numbers in ` ind ` . $)
  ax-inf $a |- : f ( ind -> ind ) |=
    ( ? \ f [ ( 1-1 f ) /\ ( ~ ( onto f ) ) ] ) $.

