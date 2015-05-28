  $c |- term * i ( ) = $.
  $v x y z w t u v $.

  tx $f term x $.
  ty $f term y $.
  tz $f term z $.
  tw $f term w $.
  tt $f term t $.
  tu $f term u $.
  tv $f term v $.

  tmul $a term ( x * y ) $.
  tinv $a term i x $.

  ax-eqid $a |- x = x $.

  ${
     ax-sb.1 $e |- x = y $.

     ax-inveq $a |- i x = i y $.

     ${
	ax-muleq.2 $e |- z = w $.

	ax-muleq12 $a |- ( x * z ) = ( y * w ) $.
     $}

     ${
        ax-eqsb.2 $e |- x = z $.

	ax-eqsb $a |- y = z $.
     $}
  $}

  ax-group $a |- ( x * i ( y * ( ( ( z * i z ) * i ( w * y ) ) * x ) ) ) = w $.

  ${
     eqcom.1 $e |- x = y $.

     eqcom $p |- y = x $=
       ( ax-eqid ax-eqsb ) ABACADE $.
       $( [?] $) $( [5-Jan-2011] $)
  $}

  ${
     eqtr.1 $e |- x = y $.
     eqtr.2 $e |- y = z $.

     eqtr $p |- x = z $=
       ( eqcom ax-eqsb ) BACABDFEG $.
       $( [?] $) $( [5-Jan-2011] $)

    ${
       3eqtr.3 $e |- z = w $.

       3eqtr $p |- x = w $=
         ( eqtr ) ABDEBCDFGHH $.
         $( [?] $) $( [5-Jan-2011] $)
    $}
  $}

  ${
     muleq.1 $e |- x = y $.

     muleq1 $p |- ( x * z ) = ( y * z ) $=
       ( ax-eqid ax-muleq12 ) ABCCDCEF $.
       $( [?] $) $( [5-Jan-2011] $)

     muleq2 $p |- ( z * x ) = ( z * y ) $=
       ( ax-eqid ax-muleq12 ) CCABCEDF $.
       $( [?] $) $( [5-Jan-2011] $)
  $}

  ${
     3eqtr3.1 $e |- x = y $.
     3eqtr3.2 $e |- x = z $.
     3eqtr3.3 $e |- y = w $.

     3eqtr3 $p |- z = w $=
       ( eqcom 3eqtr ) CABDACFHEGI $.
       $( [?] $) $( [6-Jan-2011] $)
  $}

$( $t

   latexdef "(" as "(";
   latexdef ")" as ")";
   latexdef "*" as "\cdot";
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
   althtmldef "*" as " &middot; ";
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
