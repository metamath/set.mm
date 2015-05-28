  $c |- wff term + ' ( ) = $.
  $v x y z w t u v $.

  tx $f term x $.
  ty $f term y $.
  tz $f term z $.
  tw $f term w $.
  tt $f term t $.
  tu $f term u $.
  tv $f term v $.

  tpl $a term ( x + y ) $.
  tinv $a term x ' $.

  weq $a wff x = y $.

  ax-eqid $a |- x = x $.

  ${
     ax-sb.1 $e |- x = y $.

     ax-inveq $a |- x ' = y ' $.

     ${
	ax-pleq.2 $e |- z = w $.

	ax-pleq12 $a |- ( x + z ) = ( y + w ) $.
     $}

     ${
        ax-eqsb.2 $e |- x = z $.

	ax-eqsb $a |- y = z $.
     $}
  $}

  ${
     ax-abgp.1 $e |- ( x + y ) = ( z + w ) $.

     ax-abgp $a |- ( ( y ' + z ) + w ) = x $.
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
     pleq.1 $e |- x = y $.

     pleq1 $p |- ( x + z ) = ( y + z ) $=
       tx ty tz tz pleq.1 tz ax-eqid ax-pleq12 $.
       $( [?] $) $( [5-Jan-2011] $)

     pleq2 $p |- ( z + x ) = ( z + y ) $=
       tz tz tx ty tz ax-eqid pleq.1 ax-pleq12 $.
       $( [?] $) $( [5-Jan-2011] $)
  $}

  ${
     3eqtr3.1 $e |- x = y $.
     3eqtr3.2 $e |- x = z $.
     3eqtr3.3 $e |- y = w $.

     3eqtr3 $p |- z = w $=
       tz tx ty tw tx tz 3eqtr3.2 eqcom 3eqtr3.1 3eqtr3.3 3eqtr $.
       $( [?] $) $( [6-Jan-2011] $)
  $}

  lem1 $p |- ( ( x ' + y ) + x ) = y $=
    ty tx ty tx ty tx tpl ax-eqid ax-abgp $.
    $( [?] $) $( [6-Jan-2011] $)

  lem2 $p |- ( ( x ' + y ) + z ) = ( x ' + ( y + z ) ) $=
    tx tinv ty tz tpl tpl tx ty tz tx ty tz tpl lem1 ax-abgp $.
    $( [?] $) $( [6-Jan-2011] $)

  inv $p |- ( x ' + x ) = ( y ' + y ) $=
    ty tinv tx tinv tpl ty tpl tx tpl tx tinv tx tpl ty tinv ty tpl ty tinv tx
    tinv tpl ty tpl tx tinv tx ty tx tinv lem1 pleq1 ty tinv tx tinv tpl ty tpl
    tx tpl ty tinv tx tinv ty tpl tpl tx tpl ty tinv tx tinv ty tpl tx tpl tpl
    ty tinv ty tpl ty tinv tx tinv tpl ty tpl ty tinv tx tinv ty tpl tpl tx ty
    tx tinv ty lem2 pleq1 ty tx tinv ty tpl tx lem2 tx tinv ty tpl tx tpl ty ty
    tinv tx ty lem1 pleq2 3eqtr ax-eqsb $.
    $( [?] $) $( [6-Jan-2011] $)

  id $p |- ( ( x ' + x ) + y ) = y $=
    tx tinv tx tpl ty tpl ty tinv ty tpl ty tpl ty tx tinv tx tpl ty tinv ty
    tpl ty tx ty inv pleq1 ty ty lem1 eqtr $.
    $( [?] $) $( [6-Jan-2011] $)

  com $p |- ( x + y ) = ( y + x ) $=
    ty tinv ty tpl tx tpl ty tpl ty tinv ty tx tpl tpl ty tpl tx ty tpl ty tx
    tpl ty tinv ty tpl tx tpl ty tinv ty tx tpl tpl ty ty ty tx lem2 pleq1 ty
    tinv ty tpl tx tpl tx ty ty tx id pleq1 ty ty tx tpl lem1 3eqtr3 $.
    $( [?] $) $( [6-Jan-2011] $)

  dblneg $p |- x ' ' = x $=
    tx tinv tinv tx tinv tpl tx tpl tx tinv tinv tx tx tinv tinv tx tinv tpl tx
    tpl tx tinv tinv tx tinv tx tpl tpl tx tinv tx tpl tx tinv tinv tpl tx tinv
    tinv tx tinv tx tinv tx lem2 tx tinv tinv tx tinv tx tpl com tx tx tinv
    tinv id 3eqtr tx tinv tx id ax-eqsb $.
    $( [?] $) $( [6-Jan-2011] $)

  assoc $p |- ( ( x + y ) + z ) = ( x + ( y + z ) ) $=
    tx tinv tinv ty tpl tz tpl tx tinv tinv ty tz tpl tpl tx ty tpl tz tpl tx
    ty tz tpl tpl tx tinv ty tz lem2 tx tinv tinv ty tpl tx ty tpl tz tx tinv
    tinv tx ty tx dblneg pleq1 pleq1 tx tinv tinv tx ty tz tpl tx dblneg pleq1
    3eqtr3 $.
    $( [?] $) $( [6-Jan-2011] $)
