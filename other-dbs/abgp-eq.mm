  $c |- term + i ( ) = $.
  $v x y z w t u v $.

  tx $f term x $.
  ty $f term y $.
  tz $f term z $.
  tw $f term w $.
  tt $f term t $.
  tu $f term u $.
  tv $f term v $.

  tpl $a term ( x + y ) $.
  tinv $a term i x $.

  ax-eqid $a |- x = x $.

  ${
     ax-sb.1 $e |- x = y $.

     ax-inveq $a |- i x = i y $.

     ${
	ax-pleq.2 $e |- z = w $.

	ax-pleq12 $a |- ( x + z ) = ( y + w ) $.
     $}

     ${
        ax-eqsb.2 $e |- x = z $.

	ax-eqsb $a |- y = z $.
     $}
  $}

  ax-abgp $a |- ( ( ( x + y ) + z ) + i ( x + z ) ) = y $.

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

  lem1 $p |- ( ( x + y ) + i ( ( ( z + x ) + u ) + y ) ) = i ( z + u ) $=
    tz tx tpl tu tpl tz tu tpl tinv tpl ty tpl tz tx tpl tu tpl ty tpl tinv tpl
    tx ty tpl tz tx tpl tu tpl ty tpl tinv tpl tz tu tpl tinv tz tx tpl tu tpl
    tz tu tpl tinv tpl ty tpl tx ty tpl tz tx tpl tu tpl ty tpl tinv tz tx tpl
    tu tpl tz tu tpl tinv tpl tx ty tz tx tu ax-abgp pleq1 pleq1 tz tx tpl tu
    tpl tz tu tpl tinv ty ax-abgp ax-eqsb $.
    $( [?] $) $( [6-Jan-2011] $)

  lem2 $p |- ( x + i ( ( y + x ) + i ( y + z ) ) ) = z $=
    ty tx tpl tz tpl ty tz tpl tinv tpl ty tx tpl ty tz tpl tinv tpl tinv tpl
    tx ty tx tpl ty tz tpl tinv tpl tinv tpl tz ty tx tpl tz tpl ty tz tpl tinv
    tpl tx ty tx tpl ty tz tpl tinv tpl tinv ty tx tz ax-abgp pleq1 ty tx tpl
    tz ty tz tpl tinv ax-abgp ax-eqsb $.
    $( [?] $) $( [6-Jan-2011] $)

  lem3 $p |- ( ( x + i ( y + z ) ) + i x ) = i ( y + z ) $=
    tx ty tz tpl tinv tpl ty tx tpl tz tpl ty tz tpl tinv tpl tinv tpl tx ty tz
    tpl tinv tpl tx tinv tpl ty tz tpl tinv ty tx tpl tz tpl ty tz tpl tinv tpl
    tinv tx tinv tx ty tz tpl tinv tpl ty tx tpl tz tpl ty tz tpl tinv tpl tx
    ty tx tz ax-abgp ax-inveq pleq2 tx ty tz tpl tinv ty tz lem1 ax-eqsb $.
    $( [?] $) $( [6-Jan-2011] $)

  lem4 $p |- i ( x + ( y + i ( ( x + y ) + z ) ) ) = z $=
    ty tx ty tpl tz tpl tinv tpl tx ty tpl ty tx ty tpl tz tpl tinv tpl tpl tx
    ty tpl tz tpl tinv tpl tinv tpl tx ty tx ty tpl tz tpl tinv tpl tpl tinv tz
    ty tx ty tpl tz tpl tinv tx ty tx ty tpl tz tpl tinv tpl lem1 ty tx ty tpl
    tz tpl tinv tpl tx ty tpl tz lem2 ax-eqsb $.
    $( [?] $) $( [6-Jan-2011] $)

  lem5 $p |- i ( ( x + ( y + z ) ) + i ( x + u ) ) = i ( y + ( z + i u ) ) $=
    ty tz ty tz tpl tx ty tz tpl tpl tx tu tpl tinv tpl tinv tpl tinv tpl tpl
    tinv tx ty tz tpl tpl tx tu tpl tinv tpl tinv ty tz tu tinv tpl tpl tinv ty
    tz tx ty tz tpl tpl tx tu tpl tinv tpl tinv lem4 ty tz ty tz tpl tx ty tz
    tpl tpl tx tu tpl tinv tpl tinv tpl tinv tpl tpl ty tz tu tinv tpl tpl tz
    ty tz tpl tx ty tz tpl tpl tx tu tpl tinv tpl tinv tpl tinv tpl tz tu tinv
    tpl ty ty tz tpl tx ty tz tpl tpl tx tu tpl tinv tpl tinv tpl tinv tu tinv
    tz ty tz tpl tx ty tz tpl tpl tx tu tpl tinv tpl tinv tpl tu ty tz tpl tx
    tu lem2 ax-inveq pleq2 pleq2 ax-inveq ax-eqsb $.
    $( [?] $) $( [6-Jan-2011] $)

  lem6 $p |- ( x + i ( ( y + x ) + z ) ) = i ( y + z ) $=
    ty tx tpl tz tpl ty tz tpl tinv tpl ty tx tpl tz tpl tinv tpl tx ty tx tpl
    tz tpl tinv tpl ty tz tpl tinv ty tx tpl tz tpl ty tz tpl tinv tpl tx ty tx
    tpl tz tpl tinv ty tx tz ax-abgp pleq1 ty tx tpl tz tpl ty tz lem3 ax-eqsb
    $.
    $( [?] $) $( [6-Jan-2011] $)

  lem7 $p |- i ( ( x + y ) + i ( x + z ) ) = ( z + i y ) $=
    ty tx ty tpl tx tz tpl tinv tpl tinv tpl ty tinv tpl tx ty tpl tx tz tpl
    tinv tpl tinv tz ty tinv tpl ty tx ty tpl tx tz tpl tinv lem3 ty tx ty tpl
    tx tz tpl tinv tpl tinv tpl tz ty tinv ty tx tz lem2 pleq1 ax-eqsb $.
    $( [?] $) $( [6-Jan-2011] $)

  lem8 $p |- i ( x + i y ) = ( y + i x ) $=
    tz tx tz tpl ty tinv tpl tinv tpl tz tx tpl tz ty tpl tinv tpl tinv tx ty
    tinv tpl tinv ty tx tinv tpl tz tx tz tpl tx tz tx tpl tz ty tpl tinv tpl
    tinv tpl tinv tpl tinv tpl tz tx tz tpl ty tinv tpl tinv tpl tz tx tpl tz
    ty tpl tinv tpl tinv tx tz tpl tx tz tx tpl tz ty tpl tinv tpl tinv tpl
    tinv tpl tinv tx tz tpl ty tinv tpl tinv tz tx tz tpl tx tz tx tpl tz ty
    tpl tinv tpl tinv tpl tinv tpl tx tz tpl ty tinv tpl tx tz tx tpl tz ty tpl
    tinv tpl tinv tpl tinv ty tinv tx tz tpl tx tz tx tpl tz ty tpl tinv tpl
    tinv tpl ty tx tz ty lem2 ax-inveq pleq2 ax-inveq pleq2 tz tx tz tx tpl tz
    ty tpl tinv tpl tinv lem2 ax-eqsb tz tx ty tinv lem6 tz tx ty lem7 3eqtr3
    $.
    $( [?] $) $( [6-Jan-2011] $)

  lem9 $p |- ( ( x + y ) + i x ) = y $=
    tx tx ty tpl tinv tpl tinv tx ty tpl tx tinv tpl ty tx tx ty tpl lem8 tx tz
    tx tz tpl ty tpl tinv tpl tpl tinv tx tx ty tpl tinv tpl tinv ty tx tz tx
    tz tpl ty tpl tinv tpl tpl tx tx ty tpl tinv tpl tz tx tz tpl ty tpl tinv
    tpl tx ty tpl tinv tx tz tx ty lem6 pleq2 ax-inveq tx tz ty lem4 ax-eqsb
    ax-eqsb $.
    $( [?] $) $( [6-Jan-2011] $)

  lem10 $p |- ( x + ( y + i x ) ) = y $=
    tx tz ty tx tinv tpl tpl tz tinv tpl tpl tx ty tx tinv tpl tpl ty tz ty tx
    tinv tpl tpl tz tinv tpl ty tx tinv tpl tx tz ty tx tinv tpl lem9 pleq2 tx
    tz tz ty tx tinv tpl tpl tinv tpl tinv tpl tx tz ty tx tinv tpl tpl tz tinv
    tpl tpl ty tz tz ty tx tinv tpl tpl tinv tpl tinv tz ty tx tinv tpl tpl tz
    tinv tpl tx tz tz ty tx tinv tpl tpl lem8 pleq2 tx tz tz tz ty tpl tpl tz
    tx tpl tinv tpl tinv tpl tinv tpl tx tz tz ty tx tinv tpl tpl tinv tpl tinv
    tpl ty tz tz tz ty tpl tpl tz tx tpl tinv tpl tinv tpl tinv tz tz ty tx
    tinv tpl tpl tinv tpl tinv tx tz tz tz ty tpl tpl tz tx tpl tinv tpl tinv
    tpl tz tz ty tx tinv tpl tpl tinv tpl tz tz ty tpl tpl tz tx tpl tinv tpl
    tinv tz ty tx tinv tpl tpl tinv tz tz tz ty tx lem5 pleq2 ax-inveq pleq2 tz
    ty tpl tz tz ty tpl tpl tz tx tpl tinv tpl tinv tpl tz tz tz ty tpl tpl tz
    tx tpl tinv tpl tinv tpl tinv tpl tx tz tz tz ty tpl tpl tz tx tpl tinv tpl
    tinv tpl tinv tpl ty tz ty tpl tz tz ty tpl tpl tz tx tpl tinv tpl tinv tpl
    tx tz tz tz ty tpl tpl tz tx tpl tinv tpl tinv tpl tinv tz ty tpl tz tx
    lem2 pleq1 tz ty tz tz ty tpl tpl tz tx tpl tinv tpl tinv ax-abgp ax-eqsb
    ax-eqsb ax-eqsb ax-eqsb $.
    $( [?] $) $( [6-Jan-2011] $)

  lem11 $p |- ( ( x + y ) + i ( x + z ) ) = ( y + i z ) $=
    tx tz tpl tx ty tpl tinv tpl tinv tx ty tpl tx tz tpl tinv tpl ty tz tinv
    tpl tx tz tpl tx ty tpl lem8 tx tz ty lem7 ax-eqsb $.
    $( [?] $) $( [6-Jan-2011] $)

  lem12 $p |- ( ( x + i y ) + y ) = x $=
    tz tx tpl tz ty tpl tinv tpl ty tpl tx ty tinv tpl ty tpl tx tz tx tpl tz
    ty tpl tinv tpl tx ty tinv tpl ty tz tx ty lem11 pleq1 tz tx tpl tz tz tz
    tpl ty tpl tinv tpl tpl ty tpl tz tx tpl tz ty tpl tinv tpl ty tpl tx tz tx
    tpl tz tz tz tpl ty tpl tinv tpl tpl tz tx tpl tz ty tpl tinv tpl ty tz tz
    tz tpl ty tpl tinv tpl tz ty tpl tinv tz tx tpl tz tz ty lem6 pleq2 pleq1
    tz tx tpl tz tz tz tpl ty tpl tinv tpl tpl tz tz tz tz tpl ty tpl tinv tpl
    tpl tinv tpl tz tx tpl tz tz tz tpl ty tpl tinv tpl tpl ty tpl tx tz tz tz
    tz tpl ty tpl tinv tpl tpl tinv ty tz tx tpl tz tz tz tpl ty tpl tinv tpl
    tpl tz tz ty lem4 pleq2 tz tx tz tz tz tpl ty tpl tinv tpl ax-abgp ax-eqsb
    ax-eqsb ax-eqsb $.
    $( [?] $) $( [6-Jan-2011] $)

  com $p |- ( x + y ) = ( y + x ) $=
    ty tx tpl ty tinv tpl ty tpl tx ty tpl ty tx tpl ty tx tpl ty tinv tpl tx
    ty ty tx lem9 pleq1 ty tx tpl ty lem12 ax-eqsb $.
    $( [?] $) $( [6-Jan-2011] $)

  id $p |- ( ( i x + x ) + y ) = y $=
    tx tinv tx tpl ty tpl ty tx tinv tx tpl tpl ty tx tx tinv tpl tpl ty tx
    tinv tx tpl ty com tx tinv tx tpl tx tx tinv tpl ty tx tinv tx com pleq2 ty
    tx tx tinv tpl tinv tpl ty tx tx tinv tpl tpl ty tx tx tinv tpl tinv tx tx
    tinv tpl ty tx tx lem8 pleq2 tz ty tpl tz tx tx tinv tpl tpl tinv tpl tx tx
    tinv ty tinv tpl tpl tinv ty tx tx tinv tpl tinv tpl ty tz tx tx tinv tpl
    tpl tz ty tpl tinv tpl tinv tz ty tpl tz tx tx tinv tpl tpl tinv tpl tx tx
    tinv ty tinv tpl tpl tinv tz tx tx tinv tpl tpl tz ty tpl lem8 tz tx tx
    tinv ty lem5 ax-eqsb tz ty tx tx tinv tpl lem11 tx tz tx tinv tpl tz ty tpl
    tinv tpl tpl tinv tx tx tinv ty tinv tpl tpl tinv ty tx tz tx tinv tpl tz
    ty tpl tinv tpl tpl tx tx tinv ty tinv tpl tpl tz tx tinv tpl tz ty tpl
    tinv tpl tx tinv ty tinv tpl tx tz tx tinv ty lem11 pleq2 ax-inveq tx tz tz
    tpl tz tx tpl tinv tpl tz ty tpl tinv tpl tpl tinv tx tz tx tinv tpl tz ty
    tpl tinv tpl tpl tinv ty tx tz tz tpl tz tx tpl tinv tpl tz ty tpl tinv tpl
    tpl tx tz tx tinv tpl tz ty tpl tinv tpl tpl tz tz tpl tz tx tpl tinv tpl
    tz ty tpl tinv tpl tz tx tinv tpl tz ty tpl tinv tpl tx tz tz tpl tz tx tpl
    tinv tpl tz tx tinv tpl tz ty tpl tinv tz tz tx lem11 pleq1 pleq2 ax-inveq
    tx tz tx tpl tz tz tpl tinv tpl tinv tz ty tpl tinv tpl tpl tinv tx tz tz
    tpl tz tx tpl tinv tpl tz ty tpl tinv tpl tpl tinv ty tx tz tx tpl tz tz
    tpl tinv tpl tinv tz ty tpl tinv tpl tpl tx tz tz tpl tz tx tpl tinv tpl tz
    ty tpl tinv tpl tpl tz tx tpl tz tz tpl tinv tpl tinv tz ty tpl tinv tpl tz
    tz tpl tz tx tpl tinv tpl tz ty tpl tinv tpl tx tz tx tpl tz tz tpl tinv
    tpl tinv tz tz tpl tz tx tpl tinv tpl tz ty tpl tinv tz tx tpl tz tz tpl
    lem8 pleq1 pleq2 ax-inveq tx tz tx tpl tz tz tpl tinv tpl tinv tx tz tx tpl
    tz tz tpl tinv tpl tinv tpl ty tpl tinv tpl tpl tinv tx tz tx tpl tz tz tpl
    tinv tpl tinv tz ty tpl tinv tpl tpl tinv ty tx tz tx tpl tz tz tpl tinv
    tpl tinv tx tz tx tpl tz tz tpl tinv tpl tinv tpl ty tpl tinv tpl tpl tx tz
    tx tpl tz tz tpl tinv tpl tinv tz ty tpl tinv tpl tpl tz tx tpl tz tz tpl
    tinv tpl tinv tx tz tx tpl tz tz tpl tinv tpl tinv tpl ty tpl tinv tpl tz
    tx tpl tz tz tpl tinv tpl tinv tz ty tpl tinv tpl tx tx tz tx tpl tz tz tpl
    tinv tpl tinv tpl ty tpl tinv tz ty tpl tinv tz tx tpl tz tz tpl tinv tpl
    tinv tx tz tx tpl tz tz tpl tinv tpl tinv tpl ty tpl tz ty tpl tx tz tx tpl
    tz tz tpl tinv tpl tinv tpl tz ty tx tz tz lem2 pleq1 ax-inveq pleq2 pleq2
    ax-inveq tx tz tx tpl tz tz tpl tinv tpl tinv ty lem4 ax-eqsb ax-eqsb
    ax-eqsb ax-eqsb 3eqtr3 ax-eqsb 3eqtr $.
    $( [?] $) $( [6-Jan-2011] $)

  inv $p |- ( i x + x ) = ( i y + y ) $=
    tx tinv tx tpl tx tx tinv tpl ty ty tinv tpl ty tinv ty tpl tx tinv tx com
    tx tx tinv tpl tinv tz tz tpl tinv ty tpl tz tz tpl tinv ty tpl tinv tpl tx
    tx tinv tpl ty ty tinv tpl tz tz tpl tinv ty tpl tx tz tz tpl tinv tpl tx
    tinv tpl ty tpl tinv tpl tx tx tinv tpl tinv tz tz tpl tinv ty tpl tz tz
    tpl tinv ty tpl tinv tpl tz tz tpl tinv ty tx tx tinv lem1 tx tz tz tpl
    tinv tpl tx tinv tpl ty tpl tinv tz tz tpl tinv ty tpl tinv tz tz tpl tinv
    ty tpl tx tz tz tpl tinv tpl tx tinv tpl ty tpl tz tz tpl tinv ty tpl tx tz
    tz tpl tinv tpl tx tinv tpl tz tz tpl tinv ty tx tz tz lem3 pleq1 ax-inveq
    pleq2 ax-eqsb tx tx lem8 tz tz tpl tinv ty ty lem11 3eqtr3 ty ty tinv com
    3eqtr $.
    $( [?] $) $( [6-Jan-2011] $)

  assoc $p |- ( x + ( y + z ) ) = ( ( x + y ) + z ) $=
    tx ty tz tpl tpl tx tz ty tpl tpl tz tx ty tpl tpl tx ty tpl tz tpl ty tz
    tpl tz ty tpl tx ty tz com pleq2 tx tz tx ty tpl tpl tx tinv tpl tpl tx tz
    ty tpl tpl tz tx ty tpl tpl tz tx ty tpl tpl tx tinv tpl tz ty tpl tx tz tx
    ty tinv tinv tpl tpl tx tinv tpl tz tx ty tpl tpl tx tinv tpl tz ty tpl tz
    tx ty tinv tinv tpl tpl tz tx ty tpl tpl tx tinv tx ty tinv tinv tpl tx ty
    tpl tz ty tinv tinv ty tx ty ty tinv tinv tpl ty tinv tpl ty tinv tinv ty
    ty ty tinv tinv lem9 ty ty tinv lem12 ax-eqsb pleq2 pleq2 pleq1 ty tinv tz
    ty tpl tpl tx ty tinv tinv tpl tpl tx tinv tpl tz tx ty tinv tinv tpl tpl
    tx tinv tpl tz ty tpl ty tinv tz ty tpl tpl tx ty tinv tinv tpl tpl tz tx
    ty tinv tinv tpl tpl tx tinv ty tinv tz ty tpl tpl tz tx ty tinv tinv tpl
    ty tinv tz ty tinv tinv tpl tpl ty tinv tz ty tpl tpl tz tz ty tinv tinv
    tpl tz ty tpl ty tinv ty tinv tinv ty tz ty ty tinv tinv tpl ty tinv tpl ty
    tinv tinv ty ty ty tinv tinv lem9 ty ty tinv lem12 ax-eqsb pleq2 pleq2 ty
    tinv tz lem10 ax-eqsb pleq1 pleq1 ty tinv tz ty tpl tpl tw tx tpl tw ty
    tinv tpl tinv tpl tpl tx tinv tpl ty tinv tz ty tpl tpl tx ty tinv tinv tpl
    tpl tx tinv tpl tz ty tpl ty tinv tz ty tpl tpl tw tx tpl tw ty tinv tpl
    tinv tpl tpl ty tinv tz ty tpl tpl tx ty tinv tinv tpl tpl tx tinv tw tx
    tpl tw ty tinv tpl tinv tpl tx ty tinv tinv tpl ty tinv tz ty tpl tpl tw tx
    ty tinv lem11 pleq2 pleq1 ty tinv tz ty tpl tpl tw ty tinv tpl tw tx tpl
    tinv tpl tinv tpl tx tinv tpl ty tinv tz ty tpl tpl tw tx tpl tw ty tinv
    tpl tinv tpl tpl tx tinv tpl tz ty tpl ty tinv tz ty tpl tpl tw ty tinv tpl
    tw tx tpl tinv tpl tinv tpl ty tinv tz ty tpl tpl tw tx tpl tw ty tinv tpl
    tinv tpl tpl tx tinv tw ty tinv tpl tw tx tpl tinv tpl tinv tw tx tpl tw ty
    tinv tpl tinv tpl ty tinv tz ty tpl tpl tw ty tinv tpl tw tx tpl lem8 pleq2
    pleq1 ty tinv tz ty tpl tpl tw ty tinv tpl tw tx tpl tinv tpl tinv tpl ty
    tinv tw ty tinv tpl tw tx tpl tinv tpl tinv tpl tinv tpl ty tinv tz ty tpl
    tpl tw ty tinv tpl tw tx tpl tinv tpl tinv tpl tx tinv tpl tz ty tpl ty
    tinv tw ty tinv tpl tw tx tpl tinv tpl tinv tpl tinv tx tinv ty tinv tz ty
    tpl tpl tw ty tinv tpl tw tx tpl tinv tpl tinv tpl ty tinv tw ty tinv tpl
    tw tx tpl tinv tpl tinv tpl tx ty tinv tw tx lem2 ax-inveq pleq2 ty tinv tz
    ty tpl tw ty tinv tpl tw tx tpl tinv tpl tinv ax-abgp ax-eqsb ax-eqsb
    ax-eqsb ax-eqsb ax-eqsb pleq2 tx tz tx ty tpl tpl lem10 ax-eqsb tz tx ty
    tpl com 3eqtr $.
    $( [?] $) $( [6-Jan-2011] $)

$( $t

   latexdef "(" as "(";
   latexdef ")" as ")";
   latexdef "+" as "+";
   latexdef "i" as "{ \rm i }";
   latexdef "=" as "=";
   latexdef "|-" as "\vdash";
   latexdef "term" as "{ \rm term }";
   latexdef "x" as "x";
   latexdef "y" as "y";
   latexdef "z" as "z";
   latexdef "w" as "w";
   latexdef "t" as "t";
   latexdef "u" as "u";
   latexdef "v" as "v";

   althtmldef "(" as "( ";
   althtmldef ")" as " )";
   althtmldef "+" as " + ";
   althtmldef "i" as "i ";
   althtmldef "=" as " = ";
   althtmldef "|-" as "&#8866; ";
   althtmldef "term" as "term ";
   althtmldef "x" as "x";
   althtmldef "y" as "y";
   althtmldef "z" as "z";
   althtmldef "w" as "w";
   althtmldef "t" as "t";
   althtmldef "u" as "u";
   althtmldef "v" as "v";
$)
