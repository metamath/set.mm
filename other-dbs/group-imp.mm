  $c |- wff term * ' ( ) = $.
  $v x y z w t u v $.

  tx $f term x $.
  ty $f term y $.
  tz $f term z $.
  tw $f term w $.
  tt $f term t $.
  tu $f term u $.
  tv $f term v $.

  tmul $a term ( x * y ) $.
  tinv $a term x ' $.

  weq $a wff x = y $.

  ax-eqid $a |- x = x $.

  ${
     ax-sb.1 $e |- x = y $.

     ax-inveq $a |- x ' = y ' $.

     ${
	ax-muleq.2 $e |- z = w $.

	ax-muleq12 $a |- ( x * z ) = ( y * w ) $.
     $}

     ${
        ax-eqsb.2 $e |- x = z $.

	ax-eqsb $a |- y = z $.
     $}
  $}

  ${
     ax-gp.1 $e |- ( ( x * y ) * z ) = ( ( x * u ) * w ) $.

     ax-gp $a |- ( u * ( w * z ' ) ) = y $.
  $}

  ${
     eqcom.1 $e |- x = y $.

     eqcom $p |- y = x $=
       tx ty tx eqcom.1 tx ax-eqid ax-eqsb $.
       $( [?] $) $( [5-Jan-2011] $)
  $}

  ${
     eqtr.1 $e |- x = y $.
     eqtr.2 $e |- y = z $.

     eqtr $p |- x = z $=
       ty tx tz tx ty eqtr.1 eqcom eqtr.2 ax-eqsb $.
       $( [?] $) $( [5-Jan-2011] $)

    ${
       3eqtr.3 $e |- z = w $.

       3eqtr $p |- x = w $=
         tx ty tw eqtr.1 ty tz tw eqtr.2 3eqtr.3 eqtr eqtr $.
         $( [?] $) $( [5-Jan-2011] $)
    $}
  $}

  ${
     eqtr4.1 $e |- y = x $.
     eqtr4.2 $e |- z = x $.

     eqtr4 $p |- y = z $=
       ty tx tz eqtr4.1 tz tx eqtr4.2 eqcom eqtr $.
       $( [?] $) $( [5-Jan-2011] $)
  $}

  ${
     muleq.1 $e |- x = y $.

     muleq1 $p |- ( x * z ) = ( y * z ) $=
       tx ty tz tz muleq.1 tz ax-eqid ax-muleq12 $.
       $( [?] $) $( [5-Jan-2011] $)

     muleq2 $p |- ( z * x ) = ( z * y ) $=
       tz tz tx ty tz ax-eqid muleq.1 ax-muleq12 $.
       $( [?] $) $( [5-Jan-2011] $)
  $}

  ${
     3eqtr4.1 $e |- x = y $.
     3eqtr4.2 $e |- z = x $.
     3eqtr4.3 $e |- w = y $.

     3eqtr4 $p |- z = w $=
       tz tx ty tw 3eqtr4.2 3eqtr4.1 tw ty 3eqtr4.3 eqcom 3eqtr $.
       $( [?] $) $( [5-Jan-2011] $)
  $}

  rid $p |- ( x * ( y * y ' ) ) = x $=
    tz tx ty ty tx tz tx tmul ty tmul ax-eqid ax-gp $.
    $( [?] $) $( [5-Jan-2011] $)

  inv1 $p |- ( x * x ' ) = ( y * y ' ) $=
    tx tx tinv tmul tz tz tinv tmul tz tz tinv tmul tinv tmul tmul tx tx tinv
    tmul ty ty tinv tmul tx tx tinv tmul tz tz tinv tmul rid tz ty ty tinv tmul
    tz tz tinv tmul tz tz tinv tmul tx tx tinv tmul tz ty ty tinv tmul tmul tz
    tx tx tinv tmul tmul tz tz tinv tmul tz tz ty ty tinv tmul tmul tz tx tx
    tinv tmul tmul tz ty rid tz tx rid eqtr4 muleq1 ax-gp ax-eqsb $.
    $( [?] $) $( [5-Jan-2011] $)

  invinv1 $p |- ( x * x ' ) ' = ( y * y ' ) $=
    tx tx tinv tmul tinv tz tz tinv tmul tmul tx tx tinv tmul tinv ty ty tinv
    tmul tx tx tinv tmul tinv tz rid tx tx tinv tmul ty ty tinv tmul tz tz tx
    tx tinv tmul tinv tx tx tinv tmul ty ty tinv tmul tmul tx tx tinv tmul tx
    tx tinv tmul tinv tmul tz tx tx tinv tmul ty ty tinv tmul tmul tx tx tinv
    tmul tx tx tinv tmul tx tx tinv tmul tinv tmul tx tx tinv tmul ty rid tx tx
    tx tinv tmul inv1 eqtr muleq1 ax-gp ax-eqsb $.
    $( [?] $) $( [5-Jan-2011] $)

  id1 $p |- ( ( x * x ' ) * y ) = y $=
    tx tx tinv tmul ty tz tz tinv tmul tinv tmul tmul tx tx tinv tmul ty tmul
    ty ty tz tz tinv tmul tinv tmul ty tx tx tinv tmul ty tz tz tinv tmul tinv
    tmul ty tz tz tinv tmul tmul ty tz tz tinv tmul tinv tz tz tinv tmul ty tz
    tz invinv1 muleq2 ty tz rid eqtr muleq2 tz ty tz tz tinv tmul ty tx tx tinv
    tmul tz ty tmul tz ty tmul tz tz tinv tmul tmul tz tx tx tinv tmul tmul ty
    tmul tz ty tmul tz rid tz tx tx tinv tmul tmul tz ty tz tx rid muleq1 eqtr4
    ax-gp ax-eqsb $.
    $( [?] $) $( [5-Jan-2011] $)


  ${
     axgp2.1 $e |- ( y * z ) = ( u * w ) $.

     axgp2 $p |- ( u * ( w * z ' ) ) = y $=
       tx tx tinv tmul ty tz tw tu ty tz tmul tu tw tmul tx tx tinv tmul ty
       tmul tz tmul tx tx tinv tmul tu tmul tw tmul axgp2.1 tx tx tinv tmul ty
       tmul ty tz tx ty id1 muleq1 tx tx tinv tmul tu tmul tu tw tx tu id1
       muleq1 3eqtr4 ax-gp $.
       $( [?] $) $( [7-Jan-2011] $)
  $}

  dblinv $p |- x ' ' = x $=
    tz tz tinv tmul tx tx tinv tmul tx tinv tinv tmul tmul tx tinv tinv tx tz
    tz tinv tmul tx tx tinv tmul tx tinv tinv tmul tmul tx tx tinv tmul tx tinv
    tinv tmul tx tinv tinv tz tx tx tinv tmul tx tinv tinv tmul id1 tx tx tinv
    tinv id1 eqtr tx tx tinv tx tx tinv tmul tz tz tinv tmul tz tz tinv tmul tx
    tx tinv tmul tmul tx tx tinv tmul tz tx tx tinv tmul id1 eqcom axgp2
    ax-eqsb $.
    $( [?] $) $( [7-Jan-2011] $)
  
  id $p |- ( ( x ' * x ) * y ) = y $=
    tx tinv tx tinv tinv tmul ty tmul tx tinv tx tmul ty tmul ty tx tinv tx
    tinv tinv tmul tx tinv tx tmul ty tx tinv tinv tx tx tinv tx dblinv muleq2
    muleq1 tx tinv ty id1 ax-eqsb $.
    $( [?] $) $( [7-Jan-2011] $)

  inv $p |- ( x ' * x ) = ( y ' * y ) $=
    tx tinv tx tmul tx tinv tx tinv tinv tmul ty tinv ty tinv tinv tmul ty tinv
    ty tmul tx tinv tx tinv tinv tmul tx tinv tx tmul tx tinv tinv tx tx tinv
    tx dblinv muleq2 eqcom tx tinv ty tinv inv1 ty tinv tinv ty ty tinv ty
    dblinv muleq2 3eqtr $.
    $( [?] $) $( [7-Jan-2011] $)

  assoc $p |- ( x * ( y * z ) ) = ( ( x * y ) * z ) $=
    tx ty tz tinv tinv tmul tmul tx ty tz tmul tmul tx ty tmul tz tmul ty tz
    tinv tinv tmul ty tz tmul tx tz tinv tinv tz ty tz dblinv muleq2 muleq2 tx
    ty tmul tz tmul tz tinv ty tx tx ty tmul tz tmul tw tw tinv tmul tz tinv
    tmul tmul tx ty tmul tz tmul tz tinv tmul tx ty tmul tw tw tinv tmul tz
    tinv tmul tz tinv tx ty tmul tz tmul tw tz tinv id1 muleq2 tw tw tinv tmul
    tx ty tmul tz tw tw tinv tmul tx ty tmul tz tmul tw tw tinv tmul tx ty tmul
    tmul tz tmul tx ty tmul tz tmul tw tw tinv tmul tx ty tmul tz tmul tmul tw
    tw tinv tmul tmul tw tw tinv tmul tx ty tmul tmul tx ty tmul tz tw tx ty
    tmul id1 muleq1 tw tw tinv tmul tx ty tmul tz tmul tmul tx ty tmul tz tmul
    tw tw tinv tmul tx ty tmul tz tmul tmul tw tw tinv tmul tmul tw tx ty tmul
    tz tmul id1 tw tw tinv tmul tx ty tmul tz tmul tmul tw tw tinv tmul tmul tw
    tw tinv tmul tx ty tmul tz tmul tmul tw tw tinv tmul tx ty tmul tz tmul
    tmul tw rid eqcom ax-eqsb eqtr ax-gp ax-eqsb axgp2 ax-eqsb $.
    $( [?] $) $( [5-Jan-2011] $)
