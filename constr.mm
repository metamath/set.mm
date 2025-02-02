$[ set.mm $]

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Constructible numbers
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  This section defines the set of constructible points as complex numbers which
  can be drawn starting from two points (we take ` 0 ` and ` 1 ` ), and taking
  intersections of circles and lines.

  We initially define two sets:
  <UL>
  <LI>geometrically, by recursively adding the intersection points : this is
    ` Constr ` .</LI>
  <LI>algebraically, by using field extensions : this is ` ConstrAlg ` . </LI>
  </UL>

  We then proceed by showing that those two sets are equal.

  This construction is useful for proving the impossibility of doubling the
  cube ( ~ imp2cube ), and of angle trisection ( ~ imp3ang )
$)

  $( All algebraic numbers admit a minimal polynomial.  $)
  $( minplyeu $p |- ( ph -> E! p e. ( Monic1p ` E ) A. q e. ( Monic1p ` E ) (  -> p = q ) ) $)

  $( Use infval $)
  $( minplyf $)

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Degree of a field extension
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    fldextdgirred.b $e |- B = ( Base ` F ) $.
    fldextdgirred.0 $e |- .0. = ( 0g ` F ) $.
    fldextdgirred.d $e |- D = ( deg1 ` F ) $.
    fldextdgirred.o $e |- O = ( F evalSub1 E ) $.
    fldextdgirred.m $e |- M = ( Poly1 ` F ) $.
    fldextdgirred.k $e |- K = ( F |`s E ) $.
    fldextdgirred.l $e |- L = ( F |`s ( F fldGen ( E u. { Z } ) ) ) $.
    fldextdgirred.f $e |- ( ph -> F e. Field ) $.
    fldextdgirred.e $e |- ( ph -> E e. ( SubDRing ` F ) ) $.
    fldextdgirred.p $e |- ( ph -> P e. dom O ) $.
    fldextdgirred.1 $e |- ( ph -> P e. ( Irred ` M ) ) $.
    fldextdgirred.z $e |- ( ph -> Z e. ( B \ E ) ) $.
    fldextdgirred.2 $e |- ( ph -> ( ( O ` P ) ` Z ) = .0. ) $.
    $( If ` Z ` is the root of an irreducible polynomial ` P ` over a field
       ` K ` , then the degree of the field extension ` [ K [ Z ] : K ] ` is
       the degree of the polynomial ` P ` . $)
    fldextdgirred $p |- ( ph -> ( L [:] K ) = ( D ` P ) ) $= ? $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Quadratic field extensions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $c /FldExt2 $.

  $( Extend class notation with the quadratic field extension relation. $)
  cfldext2 $a class /FldExt2 $.

  ${
    $d e f $.
    $( Define the quadratic field extension relation.  Quadratic field
       extensions are field extensions of degree 2.  $)
    df-fldext2 $a |- /FldExt2 = { <. e , f >. | ( e /FldExt f /\ ( e [:] f ) = 2 ) } $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Chain
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $c Chain $.

  $( Extend class notation with the (finite) chain builder function. $)
  cchn $a class Chain $.

  ${
    $d r c n $.
    $( Define the (finite) chain builder function.  A chain is defined to be a
      sequence of objects, whereas each object is in a given relation with the
      next one. $)
    df-chn $a |- Chain = ( r e. _V |-> { c e. Word dom r |
      A. n e. ( dom c \ { 0 } ) ( c ` ( n - 1 ) ) r ( c ` n ) } ) $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Constructible points
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $c Constr $.

  $( Extend class notation with the set of geometrically constructible points. $)
  cconstr $a class Constr $.

  $( Define the set of geometrically constructible points, by recursively adding
     the line-line, line-circle and circle-circle intersections constructions
     using points in a previous iteration. $)
  df-constr $a |- Constr = ( rec ( ( s e. _V |-> { x e. CC |
    ( E. a e. s E. b e. s E. c e. s E. d e. s E. t e. RR E. r e. RR ( x = ( a + ( t x. ( b - a ) ) ) /\ x = ( c + ( r x. ( d - c ) ) ) /\ -. ( Im ` ( ( * ` ( b - a ) ) x. ( d - c ) ) ) = 0 )
     \/ E. a e. s E. b e. s E. c e. s E. e e. s E. f e. s E. t e. RR ( x = ( a + ( t x. ( b - a ) ) ) /\ ( abs ` ( x - c ) ) = ( abs ` ( e - f ) ) )
     \/ E. a e. s E. b e. s E. c e. s E. d e. s E. e e. s E. f e. s E. t e. RR ( -. a = d /\ ( abs ` ( x - a ) ) = ( abs ` ( b - c ) ) /\ ( abs ` ( x - d ) ) = ( abs ` ( e - f ) ) ) )
      } ) , { 0 , 1 } ) " _om ) $.

  ${
    constrtow2.b $e |- B = ( Base ` F ) $.
    constrtow2.q $e |- Q = ( CCfld |`s QQ ) $.
    constrtow2.a $e |- ( ph -> A e. Constr ) $.
    constrtow2.f $e |- ( ph -> F e. Field ) $.
    constrtow2.1 $e |- ( ph -> A e. B ) $.
    $( If an algebraically constructible point ` A ` is in a field ` F ` , then
       there is a tower of quadratic field extensions from ` QQ ` to ` F ` . $)
    constrtow2 $p |- ( ph -> E. t e. ( Chain ` `' /FldExt2 ) ( ( t ` 0 ) = Q
      /\ ( lastS ` t ) = F ) ) $= ? $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Impossible constructions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( Impossibility of doubling the cube.  This is expressed by stating that the
    cubic root of 2, which is the side length of a cube of volume ` 2 ` ,  is
    not constructible. $)
  imp2cube $p |- -. ( 2 ^c ( 1 / 3 ) ) e. Constr $= ? $.

  $( Impossibility of trisecting angles.  This is expressed by stating that the
     cosine of an angle of ` ( _pi / 9 ) ` which would be the third of the
     constructible angle ` ( _pi / 3 ) ` , is not constructible. $)
  imp3ang $p |- -. ( cos ` ( _pi / 9 ) ) e. Constr $= ? $.
