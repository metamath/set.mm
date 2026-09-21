$[ set-main.mm $]
$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Mathbox for Mario Carneiro
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Predicate calculus with all distinct variables
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x y z $.
    $( Distinct variable version of ~ ax-11 .  (Contributed by Mario Carneiro,
       14-Aug-2015.) $)
    ax-7d $a |- ( A. x A. y ph -> A. y A. x ph ) $.

    $( Distinct variable version of ~ ax-7 .  (Contributed by Mario Carneiro,
       14-Aug-2015.) $)
    ax-8d $a |- ( x = y -> ( x = z -> y = z ) ) $.

    $( Distinct variable version of ~ ax-6 , equal variables case.
       (Contributed by Mario Carneiro, 14-Aug-2015.) $)
    ax-9d1 $a |- -. A. x -. x = x $.

    $( Distinct variable version of ~ ax-6 , distinct variables case.
       (Contributed by Mario Carneiro, 14-Aug-2015.) $)
    ax-9d2 $a |- -. A. x -. x = y $.

    $( Distinct variable version of ~ axc11n .  (Contributed by Mario Carneiro,
       14-Aug-2015.) $)
    ax-10d $a |- ( A. x x = y -> A. y y = x ) $.

    $( Distinct variable version of ~ ax-12 .  (Contributed by Mario Carneiro,
       14-Aug-2015.) $)
    ax-11d $a |- ( x = y -> ( A. y ph -> A. x ( x = y -> ph ) ) ) $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Miscellaneous stuff
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    quartfull.a $e |- ( ph -> A e. CC ) $.
    quartfull.b $e |- ( ph -> B e. CC ) $.
    quartfull.c $e |- ( ph -> C e. CC ) $.
    quartfull.d $e |- ( ph -> D e. CC ) $.
    quartfull.x $e |- ( ph -> X e. CC ) $.
    quartfull.t0 $e |- ( ph -> ( ( ( ( ( -u ( 2 x. ( ( B - ( ( 3 / 8 ) x. ( A ^
      2 ) ) ) ^ 3 ) ) - ( ; 2 7 x. ( ( ( C - ( ( A x. B ) / 2 ) ) + ( ( A ^ 3 )
      / 8 ) ) ^ 2 ) ) ) + ( ; 7 2 x. ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) x. (
      ( D - ( ( C x. A ) / 4 ) ) + ( ( ( ( A ^ 2 ) x. B ) / ; 1 6 ) - ( ( 3 / ;
      ; 2 5 6 ) x. ( A ^ 4 ) ) ) ) ) ) ) + ( sqrt ` ( ( ( ( -u ( 2 x. ( ( B - (
      ( 3 / 8 ) x. ( A ^ 2 ) ) ) ^ 3 ) ) - ( ; 2 7 x. ( ( ( C - ( ( A x. B ) /
      2 ) ) + ( ( A ^ 3 ) / 8 ) ) ^ 2 ) ) ) + ( ; 7 2 x. ( ( B - ( ( 3 / 8 ) x.
      ( A ^ 2 ) ) ) x. ( ( D - ( ( C x. A ) / 4 ) ) + ( ( ( ( A ^ 2 ) x. B ) /
      ; 1 6 ) - ( ( 3 / ; ; 2 5 6 ) x. ( A ^ 4 ) ) ) ) ) ) ) ^ 2 ) - ( 4 x. ( (
      ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) ^ 2 ) + ( ; 1 2 x. ( ( D - ( ( C x.
      A ) / 4 ) ) + ( ( ( ( A ^ 2 ) x. B ) / ; 1 6 ) - ( ( 3 / ; ; 2 5 6 ) x. (
      A ^ 4 ) ) ) ) ) ) ^ 3 ) ) ) ) ) / 2 ) ^c ( 1 / 3 ) ) =/= 0 ) $.
    quartfull.m0 $e |- ( ph -> -u ( ( ( ( 2 x. ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) )
      ) ) + ( ( ( ( ( -u ( 2 x. ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) ^ 3 ) ) -
      ( ; 2 7 x. ( ( ( C - ( ( A x. B ) / 2 ) ) + ( ( A ^ 3 ) / 8 ) ) ^ 2 ) ) )
      + ( ; 7 2 x. ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) x. ( ( D - ( ( C x. A )
      / 4 ) ) + ( ( ( ( A ^ 2 ) x. B ) / ; 1 6 ) - ( ( 3 / ; ; 2 5 6 ) x. ( A ^
      4 ) ) ) ) ) ) ) + ( sqrt ` ( ( ( ( -u ( 2 x. ( ( B - ( ( 3 / 8 ) x. ( A ^
      2 ) ) ) ^ 3 ) ) - ( ; 2 7 x. ( ( ( C - ( ( A x. B ) / 2 ) ) + ( ( A ^ 3 )
      / 8 ) ) ^ 2 ) ) ) + ( ; 7 2 x. ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) x. (
      ( D - ( ( C x. A ) / 4 ) ) + ( ( ( ( A ^ 2 ) x. B ) / ; 1 6 ) - ( ( 3 / ;
      ; 2 5 6 ) x. ( A ^ 4 ) ) ) ) ) ) ) ^ 2 ) - ( 4 x. ( ( ( ( B - ( ( 3 / 8 )
      x. ( A ^ 2 ) ) ) ^ 2 ) + ( ; 1 2 x. ( ( D - ( ( C x. A ) / 4 ) ) + ( ( (
      ( A ^ 2 ) x. B ) / ; 1 6 ) - ( ( 3 / ; ; 2 5 6 ) x. ( A ^ 4 ) ) ) ) ) ) ^
      3 ) ) ) ) ) / 2 ) ^c ( 1 / 3 ) ) ) + ( ( ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 )
      ) ) ^ 2 ) + ( ; 1 2 x. ( ( D - ( ( C x. A ) / 4 ) ) + ( ( ( ( A ^ 2 ) x.
      B ) / ; 1 6 ) - ( ( 3 / ; ; 2 5 6 ) x. ( A ^ 4 ) ) ) ) ) ) / ( ( ( ( ( -u
      ( 2 x. ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) ^ 3 ) ) - ( ; 2 7 x. ( ( ( C
      - ( ( A x. B ) / 2 ) ) + ( ( A ^ 3 ) / 8 ) ) ^ 2 ) ) ) + ( ; 7 2 x. ( ( B
      - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) x. ( ( D - ( ( C x. A ) / 4 ) ) + ( ( ( (
      A ^ 2 ) x. B ) / ; 1 6 ) - ( ( 3 / ; ; 2 5 6 ) x. ( A ^ 4 ) ) ) ) ) ) ) +
      ( sqrt ` ( ( ( ( -u ( 2 x. ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) ^ 3 ) ) -
      ( ; 2 7 x. ( ( ( C - ( ( A x. B ) / 2 ) ) + ( ( A ^ 3 ) / 8 ) ) ^ 2 ) ) )
      + ( ; 7 2 x. ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) x. ( ( D - ( ( C x. A )
      / 4 ) ) + ( ( ( ( A ^ 2 ) x. B ) / ; 1 6 ) - ( ( 3 / ; ; 2 5 6 ) x. ( A ^
      4 ) ) ) ) ) ) ) ^ 2 ) - ( 4 x. ( ( ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) ^
      2 ) + ( ; 1 2 x. ( ( D - ( ( C x. A ) / 4 ) ) + ( ( ( ( A ^ 2 ) x. B ) /
      ; 1 6 ) - ( ( 3 / ; ; 2 5 6 ) x. ( A ^ 4 ) ) ) ) ) ) ^ 3 ) ) ) ) ) / 2 )
      ^c ( 1 / 3 ) ) ) ) / 3 ) =/= 0 ) $.
    $( The quartic equation, written out in full.  This actually makes a fairly
       good Metamath stress test.  Note that the length of this formula could
       be shortened significantly if the intermediate expressions were expanded
       and simplified, but it's not like this theorem will be used anyway.
       (Contributed by Mario Carneiro, 6-May-2015.) $)
    quartfull $p |- ( ph -> ( ( ( ( X ^ 4 ) + ( A x. ( X ^ 3 ) ) ) + ( ( B x. (
      X ^ 2 ) ) + ( ( C x. X ) + D ) ) ) = 0 <-> ( ( X = ( ( -u ( A / 4 ) - ( (
      sqrt ` -u ( ( ( ( 2 x. ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) ) + ( ( ( ( (
      -u ( 2 x. ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) ^ 3 ) ) - ( ; 2 7 x. ( ( (
      C - ( ( A x. B ) / 2 ) ) + ( ( A ^ 3 ) / 8 ) ) ^ 2 ) ) ) + ( ; 7 2 x. ( (
      B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) x. ( ( D - ( ( C x. A ) / 4 ) ) + ( ( (
      ( A ^ 2 ) x. B ) / ; 1 6 ) - ( ( 3 / ; ; 2 5 6 ) x. ( A ^ 4 ) ) ) ) ) ) )
      + ( sqrt ` ( ( ( ( -u ( 2 x. ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) ^ 3 ) )
      - ( ; 2 7 x. ( ( ( C - ( ( A x. B ) / 2 ) ) + ( ( A ^ 3 ) / 8 ) ) ^ 2 ) )
      ) + ( ; 7 2 x. ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) x. ( ( D - ( ( C x. A
      ) / 4 ) ) + ( ( ( ( A ^ 2 ) x. B ) / ; 1 6 ) - ( ( 3 / ; ; 2 5 6 ) x. ( A
      ^ 4 ) ) ) ) ) ) ) ^ 2 ) - ( 4 x. ( ( ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) )
      ^ 2 ) + ( ; 1 2 x. ( ( D - ( ( C x. A ) / 4 ) ) + ( ( ( ( A ^ 2 ) x. B )
      / ; 1 6 ) - ( ( 3 / ; ; 2 5 6 ) x. ( A ^ 4 ) ) ) ) ) ) ^ 3 ) ) ) ) ) / 2
      ) ^c ( 1 / 3 ) ) ) + ( ( ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) ^ 2 ) + ( ;
      1 2 x. ( ( D - ( ( C x. A ) / 4 ) ) + ( ( ( ( A ^ 2 ) x. B ) / ; 1 6 ) -
      ( ( 3 / ; ; 2 5 6 ) x. ( A ^ 4 ) ) ) ) ) ) / ( ( ( ( ( -u ( 2 x. ( ( B -
      ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) ^ 3 ) ) - ( ; 2 7 x. ( ( ( C - ( ( A x. B )
      / 2 ) ) + ( ( A ^ 3 ) / 8 ) ) ^ 2 ) ) ) + ( ; 7 2 x. ( ( B - ( ( 3 / 8 )
      x. ( A ^ 2 ) ) ) x. ( ( D - ( ( C x. A ) / 4 ) ) + ( ( ( ( A ^ 2 ) x. B )
      / ; 1 6 ) - ( ( 3 / ; ; 2 5 6 ) x. ( A ^ 4 ) ) ) ) ) ) ) + ( sqrt ` ( ( (
      ( -u ( 2 x. ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) ^ 3 ) ) - ( ; 2 7 x. ( (
      ( C - ( ( A x. B ) / 2 ) ) + ( ( A ^ 3 ) / 8 ) ) ^ 2 ) ) ) + ( ; 7 2 x. (
      ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) x. ( ( D - ( ( C x. A ) / 4 ) ) + ( (
      ( ( A ^ 2 ) x. B ) / ; 1 6 ) - ( ( 3 / ; ; 2 5 6 ) x. ( A ^ 4 ) ) ) ) ) )
      ) ^ 2 ) - ( 4 x. ( ( ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) ^ 2 ) + ( ; 1 2
      x. ( ( D - ( ( C x. A ) / 4 ) ) + ( ( ( ( A ^ 2 ) x. B ) / ; 1 6 ) - ( (
      3 / ; ; 2 5 6 ) x. ( A ^ 4 ) ) ) ) ) ) ^ 3 ) ) ) ) ) / 2 ) ^c ( 1 / 3 ) )
      ) ) / 3 ) ) / 2 ) ) + ( sqrt ` ( ( -u ( ( ( sqrt ` -u ( ( ( ( 2 x. ( B -
      ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) ) + ( ( ( ( ( -u ( 2 x. ( ( B - ( ( 3 / 8 )
      x. ( A ^ 2 ) ) ) ^ 3 ) ) - ( ; 2 7 x. ( ( ( C - ( ( A x. B ) / 2 ) ) + (
      ( A ^ 3 ) / 8 ) ) ^ 2 ) ) ) + ( ; 7 2 x. ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 )
      ) ) x. ( ( D - ( ( C x. A ) / 4 ) ) + ( ( ( ( A ^ 2 ) x. B ) / ; 1 6 ) -
      ( ( 3 / ; ; 2 5 6 ) x. ( A ^ 4 ) ) ) ) ) ) ) + ( sqrt ` ( ( ( ( -u ( 2 x.
      ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) ^ 3 ) ) - ( ; 2 7 x. ( ( ( C - ( ( A
      x. B ) / 2 ) ) + ( ( A ^ 3 ) / 8 ) ) ^ 2 ) ) ) + ( ; 7 2 x. ( ( B - ( ( 3
      / 8 ) x. ( A ^ 2 ) ) ) x. ( ( D - ( ( C x. A ) / 4 ) ) + ( ( ( ( A ^ 2 )
      x. B ) / ; 1 6 ) - ( ( 3 / ; ; 2 5 6 ) x. ( A ^ 4 ) ) ) ) ) ) ) ^ 2 ) - (
      4 x. ( ( ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) ^ 2 ) + ( ; 1 2 x. ( ( D -
      ( ( C x. A ) / 4 ) ) + ( ( ( ( A ^ 2 ) x. B ) / ; 1 6 ) - ( ( 3 / ; ; 2 5
      6 ) x. ( A ^ 4 ) ) ) ) ) ) ^ 3 ) ) ) ) ) / 2 ) ^c ( 1 / 3 ) ) ) + ( ( ( (
      B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) ^ 2 ) + ( ; 1 2 x. ( ( D - ( ( C x. A )
      / 4 ) ) + ( ( ( ( A ^ 2 ) x. B ) / ; 1 6 ) - ( ( 3 / ; ; 2 5 6 ) x. ( A ^
      4 ) ) ) ) ) ) / ( ( ( ( ( -u ( 2 x. ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) )
      ^ 3 ) ) - ( ; 2 7 x. ( ( ( C - ( ( A x. B ) / 2 ) ) + ( ( A ^ 3 ) / 8 ) )
      ^ 2 ) ) ) + ( ; 7 2 x. ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) x. ( ( D - (
      ( C x. A ) / 4 ) ) + ( ( ( ( A ^ 2 ) x. B ) / ; 1 6 ) - ( ( 3 / ; ; 2 5 6
      ) x. ( A ^ 4 ) ) ) ) ) ) ) + ( sqrt ` ( ( ( ( -u ( 2 x. ( ( B - ( ( 3 / 8
      ) x. ( A ^ 2 ) ) ) ^ 3 ) ) - ( ; 2 7 x. ( ( ( C - ( ( A x. B ) / 2 ) ) +
      ( ( A ^ 3 ) / 8 ) ) ^ 2 ) ) ) + ( ; 7 2 x. ( ( B - ( ( 3 / 8 ) x. ( A ^ 2
      ) ) ) x. ( ( D - ( ( C x. A ) / 4 ) ) + ( ( ( ( A ^ 2 ) x. B ) / ; 1 6 )
      - ( ( 3 / ; ; 2 5 6 ) x. ( A ^ 4 ) ) ) ) ) ) ) ^ 2 ) - ( 4 x. ( ( ( ( B -
      ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) ^ 2 ) + ( ; 1 2 x. ( ( D - ( ( C x. A ) / 4
      ) ) + ( ( ( ( A ^ 2 ) x. B ) / ; 1 6 ) - ( ( 3 / ; ; 2 5 6 ) x. ( A ^ 4 )
      ) ) ) ) ) ^ 3 ) ) ) ) ) / 2 ) ^c ( 1 / 3 ) ) ) ) / 3 ) ) / 2 ) ^ 2 ) - (
      ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) / 2 ) ) + ( ( ( ( C - ( ( A x. B ) / 2
      ) ) + ( ( A ^ 3 ) / 8 ) ) / 4 ) / ( ( sqrt ` -u ( ( ( ( 2 x. ( B - ( ( 3
      / 8 ) x. ( A ^ 2 ) ) ) ) + ( ( ( ( ( -u ( 2 x. ( ( B - ( ( 3 / 8 ) x. ( A
      ^ 2 ) ) ) ^ 3 ) ) - ( ; 2 7 x. ( ( ( C - ( ( A x. B ) / 2 ) ) + ( ( A ^ 3
      ) / 8 ) ) ^ 2 ) ) ) + ( ; 7 2 x. ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) x.
      ( ( D - ( ( C x. A ) / 4 ) ) + ( ( ( ( A ^ 2 ) x. B ) / ; 1 6 ) - ( ( 3 /
      ; ; 2 5 6 ) x. ( A ^ 4 ) ) ) ) ) ) ) + ( sqrt ` ( ( ( ( -u ( 2 x. ( ( B -
      ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) ^ 3 ) ) - ( ; 2 7 x. ( ( ( C - ( ( A x. B )
      / 2 ) ) + ( ( A ^ 3 ) / 8 ) ) ^ 2 ) ) ) + ( ; 7 2 x. ( ( B - ( ( 3 / 8 )
      x. ( A ^ 2 ) ) ) x. ( ( D - ( ( C x. A ) / 4 ) ) + ( ( ( ( A ^ 2 ) x. B )
      / ; 1 6 ) - ( ( 3 / ; ; 2 5 6 ) x. ( A ^ 4 ) ) ) ) ) ) ) ^ 2 ) - ( 4 x. (
      ( ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) ^ 2 ) + ( ; 1 2 x. ( ( D - ( ( C
      x. A ) / 4 ) ) + ( ( ( ( A ^ 2 ) x. B ) / ; 1 6 ) - ( ( 3 / ; ; 2 5 6 )
      x. ( A ^ 4 ) ) ) ) ) ) ^ 3 ) ) ) ) ) / 2 ) ^c ( 1 / 3 ) ) ) + ( ( ( ( B -
      ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) ^ 2 ) + ( ; 1 2 x. ( ( D - ( ( C x. A ) / 4
      ) ) + ( ( ( ( A ^ 2 ) x. B ) / ; 1 6 ) - ( ( 3 / ; ; 2 5 6 ) x. ( A ^ 4 )
      ) ) ) ) ) / ( ( ( ( ( -u ( 2 x. ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) ^ 3
      ) ) - ( ; 2 7 x. ( ( ( C - ( ( A x. B ) / 2 ) ) + ( ( A ^ 3 ) / 8 ) ) ^ 2
      ) ) ) + ( ; 7 2 x. ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) x. ( ( D - ( ( C
      x. A ) / 4 ) ) + ( ( ( ( A ^ 2 ) x. B ) / ; 1 6 ) - ( ( 3 / ; ; 2 5 6 )
      x. ( A ^ 4 ) ) ) ) ) ) ) + ( sqrt ` ( ( ( ( -u ( 2 x. ( ( B - ( ( 3 / 8 )
      x. ( A ^ 2 ) ) ) ^ 3 ) ) - ( ; 2 7 x. ( ( ( C - ( ( A x. B ) / 2 ) ) + (
      ( A ^ 3 ) / 8 ) ) ^ 2 ) ) ) + ( ; 7 2 x. ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 )
      ) ) x. ( ( D - ( ( C x. A ) / 4 ) ) + ( ( ( ( A ^ 2 ) x. B ) / ; 1 6 ) -
      ( ( 3 / ; ; 2 5 6 ) x. ( A ^ 4 ) ) ) ) ) ) ) ^ 2 ) - ( 4 x. ( ( ( ( B - (
      ( 3 / 8 ) x. ( A ^ 2 ) ) ) ^ 2 ) + ( ; 1 2 x. ( ( D - ( ( C x. A ) / 4 )
      ) + ( ( ( ( A ^ 2 ) x. B ) / ; 1 6 ) - ( ( 3 / ; ; 2 5 6 ) x. ( A ^ 4 ) )
      ) ) ) ) ^ 3 ) ) ) ) ) / 2 ) ^c ( 1 / 3 ) ) ) ) / 3 ) ) / 2 ) ) ) ) ) \/ X
      = ( ( -u ( A / 4 ) - ( ( sqrt ` -u ( ( ( ( 2 x. ( B - ( ( 3 / 8 ) x. ( A
      ^ 2 ) ) ) ) + ( ( ( ( ( -u ( 2 x. ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) ^
      3 ) ) - ( ; 2 7 x. ( ( ( C - ( ( A x. B ) / 2 ) ) + ( ( A ^ 3 ) / 8 ) ) ^
      2 ) ) ) + ( ; 7 2 x. ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) x. ( ( D - ( (
      C x. A ) / 4 ) ) + ( ( ( ( A ^ 2 ) x. B ) / ; 1 6 ) - ( ( 3 / ; ; 2 5 6 )
      x. ( A ^ 4 ) ) ) ) ) ) ) + ( sqrt ` ( ( ( ( -u ( 2 x. ( ( B - ( ( 3 / 8 )
      x. ( A ^ 2 ) ) ) ^ 3 ) ) - ( ; 2 7 x. ( ( ( C - ( ( A x. B ) / 2 ) ) + (
      ( A ^ 3 ) / 8 ) ) ^ 2 ) ) ) + ( ; 7 2 x. ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 )
      ) ) x. ( ( D - ( ( C x. A ) / 4 ) ) + ( ( ( ( A ^ 2 ) x. B ) / ; 1 6 ) -
      ( ( 3 / ; ; 2 5 6 ) x. ( A ^ 4 ) ) ) ) ) ) ) ^ 2 ) - ( 4 x. ( ( ( ( B - (
      ( 3 / 8 ) x. ( A ^ 2 ) ) ) ^ 2 ) + ( ; 1 2 x. ( ( D - ( ( C x. A ) / 4 )
      ) + ( ( ( ( A ^ 2 ) x. B ) / ; 1 6 ) - ( ( 3 / ; ; 2 5 6 ) x. ( A ^ 4 ) )
      ) ) ) ) ^ 3 ) ) ) ) ) / 2 ) ^c ( 1 / 3 ) ) ) + ( ( ( ( B - ( ( 3 / 8 ) x.
      ( A ^ 2 ) ) ) ^ 2 ) + ( ; 1 2 x. ( ( D - ( ( C x. A ) / 4 ) ) + ( ( ( ( A
      ^ 2 ) x. B ) / ; 1 6 ) - ( ( 3 / ; ; 2 5 6 ) x. ( A ^ 4 ) ) ) ) ) ) / ( (
      ( ( ( -u ( 2 x. ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) ^ 3 ) ) - ( ; 2 7 x.
      ( ( ( C - ( ( A x. B ) / 2 ) ) + ( ( A ^ 3 ) / 8 ) ) ^ 2 ) ) ) + ( ; 7 2
      x. ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) x. ( ( D - ( ( C x. A ) / 4 ) ) +
      ( ( ( ( A ^ 2 ) x. B ) / ; 1 6 ) - ( ( 3 / ; ; 2 5 6 ) x. ( A ^ 4 ) ) ) )
      ) ) ) + ( sqrt ` ( ( ( ( -u ( 2 x. ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) ^
      3 ) ) - ( ; 2 7 x. ( ( ( C - ( ( A x. B ) / 2 ) ) + ( ( A ^ 3 ) / 8 ) ) ^
      2 ) ) ) + ( ; 7 2 x. ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) x. ( ( D - ( (
      C x. A ) / 4 ) ) + ( ( ( ( A ^ 2 ) x. B ) / ; 1 6 ) - ( ( 3 / ; ; 2 5 6 )
      x. ( A ^ 4 ) ) ) ) ) ) ) ^ 2 ) - ( 4 x. ( ( ( ( B - ( ( 3 / 8 ) x. ( A ^
      2 ) ) ) ^ 2 ) + ( ; 1 2 x. ( ( D - ( ( C x. A ) / 4 ) ) + ( ( ( ( A ^ 2 )
      x. B ) / ; 1 6 ) - ( ( 3 / ; ; 2 5 6 ) x. ( A ^ 4 ) ) ) ) ) ) ^ 3 ) ) ) )
      ) / 2 ) ^c ( 1 / 3 ) ) ) ) / 3 ) ) / 2 ) ) - ( sqrt ` ( ( -u ( ( ( sqrt `
      -u ( ( ( ( 2 x. ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) ) + ( ( ( ( ( -u ( 2
      x. ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) ^ 3 ) ) - ( ; 2 7 x. ( ( ( C - (
      ( A x. B ) / 2 ) ) + ( ( A ^ 3 ) / 8 ) ) ^ 2 ) ) ) + ( ; 7 2 x. ( ( B - (
      ( 3 / 8 ) x. ( A ^ 2 ) ) ) x. ( ( D - ( ( C x. A ) / 4 ) ) + ( ( ( ( A ^
      2 ) x. B ) / ; 1 6 ) - ( ( 3 / ; ; 2 5 6 ) x. ( A ^ 4 ) ) ) ) ) ) ) + (
      sqrt ` ( ( ( ( -u ( 2 x. ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) ^ 3 ) ) - (
      ; 2 7 x. ( ( ( C - ( ( A x. B ) / 2 ) ) + ( ( A ^ 3 ) / 8 ) ) ^ 2 ) ) ) +
      ( ; 7 2 x. ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) x. ( ( D - ( ( C x. A ) /
      4 ) ) + ( ( ( ( A ^ 2 ) x. B ) / ; 1 6 ) - ( ( 3 / ; ; 2 5 6 ) x. ( A ^ 4
      ) ) ) ) ) ) ) ^ 2 ) - ( 4 x. ( ( ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) ^ 2
      ) + ( ; 1 2 x. ( ( D - ( ( C x. A ) / 4 ) ) + ( ( ( ( A ^ 2 ) x. B ) / ;
      1 6 ) - ( ( 3 / ; ; 2 5 6 ) x. ( A ^ 4 ) ) ) ) ) ) ^ 3 ) ) ) ) ) / 2 ) ^c
      ( 1 / 3 ) ) ) + ( ( ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) ^ 2 ) + ( ; 1 2
      x. ( ( D - ( ( C x. A ) / 4 ) ) + ( ( ( ( A ^ 2 ) x. B ) / ; 1 6 ) - ( (
      3 / ; ; 2 5 6 ) x. ( A ^ 4 ) ) ) ) ) ) / ( ( ( ( ( -u ( 2 x. ( ( B - ( (
      3 / 8 ) x. ( A ^ 2 ) ) ) ^ 3 ) ) - ( ; 2 7 x. ( ( ( C - ( ( A x. B ) / 2
      ) ) + ( ( A ^ 3 ) / 8 ) ) ^ 2 ) ) ) + ( ; 7 2 x. ( ( B - ( ( 3 / 8 ) x. (
      A ^ 2 ) ) ) x. ( ( D - ( ( C x. A ) / 4 ) ) + ( ( ( ( A ^ 2 ) x. B ) / ;
      1 6 ) - ( ( 3 / ; ; 2 5 6 ) x. ( A ^ 4 ) ) ) ) ) ) ) + ( sqrt ` ( ( ( (
      -u ( 2 x. ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) ^ 3 ) ) - ( ; 2 7 x. ( ( (
      C - ( ( A x. B ) / 2 ) ) + ( ( A ^ 3 ) / 8 ) ) ^ 2 ) ) ) + ( ; 7 2 x. ( (
      B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) x. ( ( D - ( ( C x. A ) / 4 ) ) + ( ( (
      ( A ^ 2 ) x. B ) / ; 1 6 ) - ( ( 3 / ; ; 2 5 6 ) x. ( A ^ 4 ) ) ) ) ) ) )
      ^ 2 ) - ( 4 x. ( ( ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) ^ 2 ) + ( ; 1 2
      x. ( ( D - ( ( C x. A ) / 4 ) ) + ( ( ( ( A ^ 2 ) x. B ) / ; 1 6 ) - ( (
      3 / ; ; 2 5 6 ) x. ( A ^ 4 ) ) ) ) ) ) ^ 3 ) ) ) ) ) / 2 ) ^c ( 1 / 3 ) )
      ) ) / 3 ) ) / 2 ) ^ 2 ) - ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) / 2 ) ) +
      ( ( ( ( C - ( ( A x. B ) / 2 ) ) + ( ( A ^ 3 ) / 8 ) ) / 4 ) / ( ( sqrt `
      -u ( ( ( ( 2 x. ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) ) + ( ( ( ( ( -u ( 2
      x. ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) ^ 3 ) ) - ( ; 2 7 x. ( ( ( C - (
      ( A x. B ) / 2 ) ) + ( ( A ^ 3 ) / 8 ) ) ^ 2 ) ) ) + ( ; 7 2 x. ( ( B - (
      ( 3 / 8 ) x. ( A ^ 2 ) ) ) x. ( ( D - ( ( C x. A ) / 4 ) ) + ( ( ( ( A ^
      2 ) x. B ) / ; 1 6 ) - ( ( 3 / ; ; 2 5 6 ) x. ( A ^ 4 ) ) ) ) ) ) ) + (
      sqrt ` ( ( ( ( -u ( 2 x. ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) ^ 3 ) ) - (
      ; 2 7 x. ( ( ( C - ( ( A x. B ) / 2 ) ) + ( ( A ^ 3 ) / 8 ) ) ^ 2 ) ) ) +
      ( ; 7 2 x. ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) x. ( ( D - ( ( C x. A ) /
      4 ) ) + ( ( ( ( A ^ 2 ) x. B ) / ; 1 6 ) - ( ( 3 / ; ; 2 5 6 ) x. ( A ^ 4
      ) ) ) ) ) ) ) ^ 2 ) - ( 4 x. ( ( ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) ^ 2
      ) + ( ; 1 2 x. ( ( D - ( ( C x. A ) / 4 ) ) + ( ( ( ( A ^ 2 ) x. B ) / ;
      1 6 ) - ( ( 3 / ; ; 2 5 6 ) x. ( A ^ 4 ) ) ) ) ) ) ^ 3 ) ) ) ) ) / 2 ) ^c
      ( 1 / 3 ) ) ) + ( ( ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) ^ 2 ) + ( ; 1 2
      x. ( ( D - ( ( C x. A ) / 4 ) ) + ( ( ( ( A ^ 2 ) x. B ) / ; 1 6 ) - ( (
      3 / ; ; 2 5 6 ) x. ( A ^ 4 ) ) ) ) ) ) / ( ( ( ( ( -u ( 2 x. ( ( B - ( (
      3 / 8 ) x. ( A ^ 2 ) ) ) ^ 3 ) ) - ( ; 2 7 x. ( ( ( C - ( ( A x. B ) / 2
      ) ) + ( ( A ^ 3 ) / 8 ) ) ^ 2 ) ) ) + ( ; 7 2 x. ( ( B - ( ( 3 / 8 ) x. (
      A ^ 2 ) ) ) x. ( ( D - ( ( C x. A ) / 4 ) ) + ( ( ( ( A ^ 2 ) x. B ) / ;
      1 6 ) - ( ( 3 / ; ; 2 5 6 ) x. ( A ^ 4 ) ) ) ) ) ) ) + ( sqrt ` ( ( ( (
      -u ( 2 x. ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) ^ 3 ) ) - ( ; 2 7 x. ( ( (
      C - ( ( A x. B ) / 2 ) ) + ( ( A ^ 3 ) / 8 ) ) ^ 2 ) ) ) + ( ; 7 2 x. ( (
      B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) x. ( ( D - ( ( C x. A ) / 4 ) ) + ( ( (
      ( A ^ 2 ) x. B ) / ; 1 6 ) - ( ( 3 / ; ; 2 5 6 ) x. ( A ^ 4 ) ) ) ) ) ) )
      ^ 2 ) - ( 4 x. ( ( ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) ^ 2 ) + ( ; 1 2
      x. ( ( D - ( ( C x. A ) / 4 ) ) + ( ( ( ( A ^ 2 ) x. B ) / ; 1 6 ) - ( (
      3 / ; ; 2 5 6 ) x. ( A ^ 4 ) ) ) ) ) ) ^ 3 ) ) ) ) ) / 2 ) ^c ( 1 / 3 ) )
      ) ) / 3 ) ) / 2 ) ) ) ) ) ) \/ ( X = ( ( -u ( A / 4 ) + ( ( sqrt ` -u ( (
      ( ( 2 x. ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) ) + ( ( ( ( ( -u ( 2 x. ( ( B
      - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) ^ 3 ) ) - ( ; 2 7 x. ( ( ( C - ( ( A x. B
      ) / 2 ) ) + ( ( A ^ 3 ) / 8 ) ) ^ 2 ) ) ) + ( ; 7 2 x. ( ( B - ( ( 3 / 8
      ) x. ( A ^ 2 ) ) ) x. ( ( D - ( ( C x. A ) / 4 ) ) + ( ( ( ( A ^ 2 ) x. B
      ) / ; 1 6 ) - ( ( 3 / ; ; 2 5 6 ) x. ( A ^ 4 ) ) ) ) ) ) ) + ( sqrt ` ( (
      ( ( -u ( 2 x. ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) ^ 3 ) ) - ( ; 2 7 x. (
      ( ( C - ( ( A x. B ) / 2 ) ) + ( ( A ^ 3 ) / 8 ) ) ^ 2 ) ) ) + ( ; 7 2 x.
      ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) x. ( ( D - ( ( C x. A ) / 4 ) ) + (
      ( ( ( A ^ 2 ) x. B ) / ; 1 6 ) - ( ( 3 / ; ; 2 5 6 ) x. ( A ^ 4 ) ) ) ) )
      ) ) ^ 2 ) - ( 4 x. ( ( ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) ^ 2 ) + ( ; 1
      2 x. ( ( D - ( ( C x. A ) / 4 ) ) + ( ( ( ( A ^ 2 ) x. B ) / ; 1 6 ) - (
      ( 3 / ; ; 2 5 6 ) x. ( A ^ 4 ) ) ) ) ) ) ^ 3 ) ) ) ) ) / 2 ) ^c ( 1 / 3 )
      ) ) + ( ( ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) ^ 2 ) + ( ; 1 2 x. ( ( D -
      ( ( C x. A ) / 4 ) ) + ( ( ( ( A ^ 2 ) x. B ) / ; 1 6 ) - ( ( 3 / ; ; 2 5
      6 ) x. ( A ^ 4 ) ) ) ) ) ) / ( ( ( ( ( -u ( 2 x. ( ( B - ( ( 3 / 8 ) x. (
      A ^ 2 ) ) ) ^ 3 ) ) - ( ; 2 7 x. ( ( ( C - ( ( A x. B ) / 2 ) ) + ( ( A ^
      3 ) / 8 ) ) ^ 2 ) ) ) + ( ; 7 2 x. ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) )
      x. ( ( D - ( ( C x. A ) / 4 ) ) + ( ( ( ( A ^ 2 ) x. B ) / ; 1 6 ) - ( (
      3 / ; ; 2 5 6 ) x. ( A ^ 4 ) ) ) ) ) ) ) + ( sqrt ` ( ( ( ( -u ( 2 x. ( (
      B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) ^ 3 ) ) - ( ; 2 7 x. ( ( ( C - ( ( A x.
      B ) / 2 ) ) + ( ( A ^ 3 ) / 8 ) ) ^ 2 ) ) ) + ( ; 7 2 x. ( ( B - ( ( 3 /
      8 ) x. ( A ^ 2 ) ) ) x. ( ( D - ( ( C x. A ) / 4 ) ) + ( ( ( ( A ^ 2 ) x.
      B ) / ; 1 6 ) - ( ( 3 / ; ; 2 5 6 ) x. ( A ^ 4 ) ) ) ) ) ) ) ^ 2 ) - ( 4
      x. ( ( ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) ^ 2 ) + ( ; 1 2 x. ( ( D - (
      ( C x. A ) / 4 ) ) + ( ( ( ( A ^ 2 ) x. B ) / ; 1 6 ) - ( ( 3 / ; ; 2 5 6
      ) x. ( A ^ 4 ) ) ) ) ) ) ^ 3 ) ) ) ) ) / 2 ) ^c ( 1 / 3 ) ) ) ) / 3 ) ) /
      2 ) ) + ( sqrt ` ( ( -u ( ( ( sqrt ` -u ( ( ( ( 2 x. ( B - ( ( 3 / 8 ) x.
      ( A ^ 2 ) ) ) ) + ( ( ( ( ( -u ( 2 x. ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) )
      ) ^ 3 ) ) - ( ; 2 7 x. ( ( ( C - ( ( A x. B ) / 2 ) ) + ( ( A ^ 3 ) / 8 )
      ) ^ 2 ) ) ) + ( ; 7 2 x. ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) x. ( ( D -
      ( ( C x. A ) / 4 ) ) + ( ( ( ( A ^ 2 ) x. B ) / ; 1 6 ) - ( ( 3 / ; ; 2 5
      6 ) x. ( A ^ 4 ) ) ) ) ) ) ) + ( sqrt ` ( ( ( ( -u ( 2 x. ( ( B - ( ( 3 /
      8 ) x. ( A ^ 2 ) ) ) ^ 3 ) ) - ( ; 2 7 x. ( ( ( C - ( ( A x. B ) / 2 ) )
      + ( ( A ^ 3 ) / 8 ) ) ^ 2 ) ) ) + ( ; 7 2 x. ( ( B - ( ( 3 / 8 ) x. ( A ^
      2 ) ) ) x. ( ( D - ( ( C x. A ) / 4 ) ) + ( ( ( ( A ^ 2 ) x. B ) / ; 1 6
      ) - ( ( 3 / ; ; 2 5 6 ) x. ( A ^ 4 ) ) ) ) ) ) ) ^ 2 ) - ( 4 x. ( ( ( ( B
      - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) ^ 2 ) + ( ; 1 2 x. ( ( D - ( ( C x. A ) /
      4 ) ) + ( ( ( ( A ^ 2 ) x. B ) / ; 1 6 ) - ( ( 3 / ; ; 2 5 6 ) x. ( A ^ 4
      ) ) ) ) ) ) ^ 3 ) ) ) ) ) / 2 ) ^c ( 1 / 3 ) ) ) + ( ( ( ( B - ( ( 3 / 8
      ) x. ( A ^ 2 ) ) ) ^ 2 ) + ( ; 1 2 x. ( ( D - ( ( C x. A ) / 4 ) ) + ( (
      ( ( A ^ 2 ) x. B ) / ; 1 6 ) - ( ( 3 / ; ; 2 5 6 ) x. ( A ^ 4 ) ) ) ) ) )
      / ( ( ( ( ( -u ( 2 x. ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) ^ 3 ) ) - ( ;
      2 7 x. ( ( ( C - ( ( A x. B ) / 2 ) ) + ( ( A ^ 3 ) / 8 ) ) ^ 2 ) ) ) + (
      ; 7 2 x. ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) x. ( ( D - ( ( C x. A ) / 4
      ) ) + ( ( ( ( A ^ 2 ) x. B ) / ; 1 6 ) - ( ( 3 / ; ; 2 5 6 ) x. ( A ^ 4 )
      ) ) ) ) ) ) + ( sqrt ` ( ( ( ( -u ( 2 x. ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 )
      ) ) ^ 3 ) ) - ( ; 2 7 x. ( ( ( C - ( ( A x. B ) / 2 ) ) + ( ( A ^ 3 ) / 8
      ) ) ^ 2 ) ) ) + ( ; 7 2 x. ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) x. ( ( D
      - ( ( C x. A ) / 4 ) ) + ( ( ( ( A ^ 2 ) x. B ) / ; 1 6 ) - ( ( 3 / ; ; 2
      5 6 ) x. ( A ^ 4 ) ) ) ) ) ) ) ^ 2 ) - ( 4 x. ( ( ( ( B - ( ( 3 / 8 ) x.
      ( A ^ 2 ) ) ) ^ 2 ) + ( ; 1 2 x. ( ( D - ( ( C x. A ) / 4 ) ) + ( ( ( ( A
      ^ 2 ) x. B ) / ; 1 6 ) - ( ( 3 / ; ; 2 5 6 ) x. ( A ^ 4 ) ) ) ) ) ) ^ 3 )
      ) ) ) ) / 2 ) ^c ( 1 / 3 ) ) ) ) / 3 ) ) / 2 ) ^ 2 ) - ( ( B - ( ( 3 / 8
      ) x. ( A ^ 2 ) ) ) / 2 ) ) - ( ( ( ( C - ( ( A x. B ) / 2 ) ) + ( ( A ^ 3
      ) / 8 ) ) / 4 ) / ( ( sqrt ` -u ( ( ( ( 2 x. ( B - ( ( 3 / 8 ) x. ( A ^ 2
      ) ) ) ) + ( ( ( ( ( -u ( 2 x. ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) ^ 3 )
      ) - ( ; 2 7 x. ( ( ( C - ( ( A x. B ) / 2 ) ) + ( ( A ^ 3 ) / 8 ) ) ^ 2 )
      ) ) + ( ; 7 2 x. ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) x. ( ( D - ( ( C x.
      A ) / 4 ) ) + ( ( ( ( A ^ 2 ) x. B ) / ; 1 6 ) - ( ( 3 / ; ; 2 5 6 ) x. (
      A ^ 4 ) ) ) ) ) ) ) + ( sqrt ` ( ( ( ( -u ( 2 x. ( ( B - ( ( 3 / 8 ) x. (
      A ^ 2 ) ) ) ^ 3 ) ) - ( ; 2 7 x. ( ( ( C - ( ( A x. B ) / 2 ) ) + ( ( A ^
      3 ) / 8 ) ) ^ 2 ) ) ) + ( ; 7 2 x. ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) )
      x. ( ( D - ( ( C x. A ) / 4 ) ) + ( ( ( ( A ^ 2 ) x. B ) / ; 1 6 ) - ( (
      3 / ; ; 2 5 6 ) x. ( A ^ 4 ) ) ) ) ) ) ) ^ 2 ) - ( 4 x. ( ( ( ( B - ( ( 3
      / 8 ) x. ( A ^ 2 ) ) ) ^ 2 ) + ( ; 1 2 x. ( ( D - ( ( C x. A ) / 4 ) ) +
      ( ( ( ( A ^ 2 ) x. B ) / ; 1 6 ) - ( ( 3 / ; ; 2 5 6 ) x. ( A ^ 4 ) ) ) )
      ) ) ^ 3 ) ) ) ) ) / 2 ) ^c ( 1 / 3 ) ) ) + ( ( ( ( B - ( ( 3 / 8 ) x. ( A
      ^ 2 ) ) ) ^ 2 ) + ( ; 1 2 x. ( ( D - ( ( C x. A ) / 4 ) ) + ( ( ( ( A ^ 2
      ) x. B ) / ; 1 6 ) - ( ( 3 / ; ; 2 5 6 ) x. ( A ^ 4 ) ) ) ) ) ) / ( ( ( (
      ( -u ( 2 x. ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) ^ 3 ) ) - ( ; 2 7 x. ( (
      ( C - ( ( A x. B ) / 2 ) ) + ( ( A ^ 3 ) / 8 ) ) ^ 2 ) ) ) + ( ; 7 2 x. (
      ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) x. ( ( D - ( ( C x. A ) / 4 ) ) + ( (
      ( ( A ^ 2 ) x. B ) / ; 1 6 ) - ( ( 3 / ; ; 2 5 6 ) x. ( A ^ 4 ) ) ) ) ) )
      ) + ( sqrt ` ( ( ( ( -u ( 2 x. ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) ^ 3 )
      ) - ( ; 2 7 x. ( ( ( C - ( ( A x. B ) / 2 ) ) + ( ( A ^ 3 ) / 8 ) ) ^ 2 )
      ) ) + ( ; 7 2 x. ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) x. ( ( D - ( ( C x.
      A ) / 4 ) ) + ( ( ( ( A ^ 2 ) x. B ) / ; 1 6 ) - ( ( 3 / ; ; 2 5 6 ) x. (
      A ^ 4 ) ) ) ) ) ) ) ^ 2 ) - ( 4 x. ( ( ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) )
      ) ^ 2 ) + ( ; 1 2 x. ( ( D - ( ( C x. A ) / 4 ) ) + ( ( ( ( A ^ 2 ) x. B
      ) / ; 1 6 ) - ( ( 3 / ; ; 2 5 6 ) x. ( A ^ 4 ) ) ) ) ) ) ^ 3 ) ) ) ) ) /
      2 ) ^c ( 1 / 3 ) ) ) ) / 3 ) ) / 2 ) ) ) ) ) \/ X = ( ( -u ( A / 4 ) + (
      ( sqrt ` -u ( ( ( ( 2 x. ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) ) + ( ( ( ( (
      -u ( 2 x. ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) ^ 3 ) ) - ( ; 2 7 x. ( ( (
      C - ( ( A x. B ) / 2 ) ) + ( ( A ^ 3 ) / 8 ) ) ^ 2 ) ) ) + ( ; 7 2 x. ( (
      B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) x. ( ( D - ( ( C x. A ) / 4 ) ) + ( ( (
      ( A ^ 2 ) x. B ) / ; 1 6 ) - ( ( 3 / ; ; 2 5 6 ) x. ( A ^ 4 ) ) ) ) ) ) )
      + ( sqrt ` ( ( ( ( -u ( 2 x. ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) ^ 3 ) )
      - ( ; 2 7 x. ( ( ( C - ( ( A x. B ) / 2 ) ) + ( ( A ^ 3 ) / 8 ) ) ^ 2 ) )
      ) + ( ; 7 2 x. ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) x. ( ( D - ( ( C x. A
      ) / 4 ) ) + ( ( ( ( A ^ 2 ) x. B ) / ; 1 6 ) - ( ( 3 / ; ; 2 5 6 ) x. ( A
      ^ 4 ) ) ) ) ) ) ) ^ 2 ) - ( 4 x. ( ( ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) )
      ^ 2 ) + ( ; 1 2 x. ( ( D - ( ( C x. A ) / 4 ) ) + ( ( ( ( A ^ 2 ) x. B )
      / ; 1 6 ) - ( ( 3 / ; ; 2 5 6 ) x. ( A ^ 4 ) ) ) ) ) ) ^ 3 ) ) ) ) ) / 2
      ) ^c ( 1 / 3 ) ) ) + ( ( ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) ^ 2 ) + ( ;
      1 2 x. ( ( D - ( ( C x. A ) / 4 ) ) + ( ( ( ( A ^ 2 ) x. B ) / ; 1 6 ) -
      ( ( 3 / ; ; 2 5 6 ) x. ( A ^ 4 ) ) ) ) ) ) / ( ( ( ( ( -u ( 2 x. ( ( B -
      ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) ^ 3 ) ) - ( ; 2 7 x. ( ( ( C - ( ( A x. B )
      / 2 ) ) + ( ( A ^ 3 ) / 8 ) ) ^ 2 ) ) ) + ( ; 7 2 x. ( ( B - ( ( 3 / 8 )
      x. ( A ^ 2 ) ) ) x. ( ( D - ( ( C x. A ) / 4 ) ) + ( ( ( ( A ^ 2 ) x. B )
      / ; 1 6 ) - ( ( 3 / ; ; 2 5 6 ) x. ( A ^ 4 ) ) ) ) ) ) ) + ( sqrt ` ( ( (
      ( -u ( 2 x. ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) ^ 3 ) ) - ( ; 2 7 x. ( (
      ( C - ( ( A x. B ) / 2 ) ) + ( ( A ^ 3 ) / 8 ) ) ^ 2 ) ) ) + ( ; 7 2 x. (
      ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) x. ( ( D - ( ( C x. A ) / 4 ) ) + ( (
      ( ( A ^ 2 ) x. B ) / ; 1 6 ) - ( ( 3 / ; ; 2 5 6 ) x. ( A ^ 4 ) ) ) ) ) )
      ) ^ 2 ) - ( 4 x. ( ( ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) ^ 2 ) + ( ; 1 2
      x. ( ( D - ( ( C x. A ) / 4 ) ) + ( ( ( ( A ^ 2 ) x. B ) / ; 1 6 ) - ( (
      3 / ; ; 2 5 6 ) x. ( A ^ 4 ) ) ) ) ) ) ^ 3 ) ) ) ) ) / 2 ) ^c ( 1 / 3 ) )
      ) ) / 3 ) ) / 2 ) ) - ( sqrt ` ( ( -u ( ( ( sqrt ` -u ( ( ( ( 2 x. ( B -
      ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) ) + ( ( ( ( ( -u ( 2 x. ( ( B - ( ( 3 / 8 )
      x. ( A ^ 2 ) ) ) ^ 3 ) ) - ( ; 2 7 x. ( ( ( C - ( ( A x. B ) / 2 ) ) + (
      ( A ^ 3 ) / 8 ) ) ^ 2 ) ) ) + ( ; 7 2 x. ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 )
      ) ) x. ( ( D - ( ( C x. A ) / 4 ) ) + ( ( ( ( A ^ 2 ) x. B ) / ; 1 6 ) -
      ( ( 3 / ; ; 2 5 6 ) x. ( A ^ 4 ) ) ) ) ) ) ) + ( sqrt ` ( ( ( ( -u ( 2 x.
      ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) ^ 3 ) ) - ( ; 2 7 x. ( ( ( C - ( ( A
      x. B ) / 2 ) ) + ( ( A ^ 3 ) / 8 ) ) ^ 2 ) ) ) + ( ; 7 2 x. ( ( B - ( ( 3
      / 8 ) x. ( A ^ 2 ) ) ) x. ( ( D - ( ( C x. A ) / 4 ) ) + ( ( ( ( A ^ 2 )
      x. B ) / ; 1 6 ) - ( ( 3 / ; ; 2 5 6 ) x. ( A ^ 4 ) ) ) ) ) ) ) ^ 2 ) - (
      4 x. ( ( ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) ^ 2 ) + ( ; 1 2 x. ( ( D -
      ( ( C x. A ) / 4 ) ) + ( ( ( ( A ^ 2 ) x. B ) / ; 1 6 ) - ( ( 3 / ; ; 2 5
      6 ) x. ( A ^ 4 ) ) ) ) ) ) ^ 3 ) ) ) ) ) / 2 ) ^c ( 1 / 3 ) ) ) + ( ( ( (
      B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) ^ 2 ) + ( ; 1 2 x. ( ( D - ( ( C x. A )
      / 4 ) ) + ( ( ( ( A ^ 2 ) x. B ) / ; 1 6 ) - ( ( 3 / ; ; 2 5 6 ) x. ( A ^
      4 ) ) ) ) ) ) / ( ( ( ( ( -u ( 2 x. ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) )
      ^ 3 ) ) - ( ; 2 7 x. ( ( ( C - ( ( A x. B ) / 2 ) ) + ( ( A ^ 3 ) / 8 ) )
      ^ 2 ) ) ) + ( ; 7 2 x. ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) x. ( ( D - (
      ( C x. A ) / 4 ) ) + ( ( ( ( A ^ 2 ) x. B ) / ; 1 6 ) - ( ( 3 / ; ; 2 5 6
      ) x. ( A ^ 4 ) ) ) ) ) ) ) + ( sqrt ` ( ( ( ( -u ( 2 x. ( ( B - ( ( 3 / 8
      ) x. ( A ^ 2 ) ) ) ^ 3 ) ) - ( ; 2 7 x. ( ( ( C - ( ( A x. B ) / 2 ) ) +
      ( ( A ^ 3 ) / 8 ) ) ^ 2 ) ) ) + ( ; 7 2 x. ( ( B - ( ( 3 / 8 ) x. ( A ^ 2
      ) ) ) x. ( ( D - ( ( C x. A ) / 4 ) ) + ( ( ( ( A ^ 2 ) x. B ) / ; 1 6 )
      - ( ( 3 / ; ; 2 5 6 ) x. ( A ^ 4 ) ) ) ) ) ) ) ^ 2 ) - ( 4 x. ( ( ( ( B -
      ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) ^ 2 ) + ( ; 1 2 x. ( ( D - ( ( C x. A ) / 4
      ) ) + ( ( ( ( A ^ 2 ) x. B ) / ; 1 6 ) - ( ( 3 / ; ; 2 5 6 ) x. ( A ^ 4 )
      ) ) ) ) ) ^ 3 ) ) ) ) ) / 2 ) ^c ( 1 / 3 ) ) ) ) / 3 ) ) / 2 ) ^ 2 ) - (
      ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) / 2 ) ) - ( ( ( ( C - ( ( A x. B ) / 2
      ) ) + ( ( A ^ 3 ) / 8 ) ) / 4 ) / ( ( sqrt ` -u ( ( ( ( 2 x. ( B - ( ( 3
      / 8 ) x. ( A ^ 2 ) ) ) ) + ( ( ( ( ( -u ( 2 x. ( ( B - ( ( 3 / 8 ) x. ( A
      ^ 2 ) ) ) ^ 3 ) ) - ( ; 2 7 x. ( ( ( C - ( ( A x. B ) / 2 ) ) + ( ( A ^ 3
      ) / 8 ) ) ^ 2 ) ) ) + ( ; 7 2 x. ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) x.
      ( ( D - ( ( C x. A ) / 4 ) ) + ( ( ( ( A ^ 2 ) x. B ) / ; 1 6 ) - ( ( 3 /
      ; ; 2 5 6 ) x. ( A ^ 4 ) ) ) ) ) ) ) + ( sqrt ` ( ( ( ( -u ( 2 x. ( ( B -
      ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) ^ 3 ) ) - ( ; 2 7 x. ( ( ( C - ( ( A x. B )
      / 2 ) ) + ( ( A ^ 3 ) / 8 ) ) ^ 2 ) ) ) + ( ; 7 2 x. ( ( B - ( ( 3 / 8 )
      x. ( A ^ 2 ) ) ) x. ( ( D - ( ( C x. A ) / 4 ) ) + ( ( ( ( A ^ 2 ) x. B )
      / ; 1 6 ) - ( ( 3 / ; ; 2 5 6 ) x. ( A ^ 4 ) ) ) ) ) ) ) ^ 2 ) - ( 4 x. (
      ( ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) ^ 2 ) + ( ; 1 2 x. ( ( D - ( ( C
      x. A ) / 4 ) ) + ( ( ( ( A ^ 2 ) x. B ) / ; 1 6 ) - ( ( 3 / ; ; 2 5 6 )
      x. ( A ^ 4 ) ) ) ) ) ) ^ 3 ) ) ) ) ) / 2 ) ^c ( 1 / 3 ) ) ) + ( ( ( ( B -
      ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) ^ 2 ) + ( ; 1 2 x. ( ( D - ( ( C x. A ) / 4
      ) ) + ( ( ( ( A ^ 2 ) x. B ) / ; 1 6 ) - ( ( 3 / ; ; 2 5 6 ) x. ( A ^ 4 )
      ) ) ) ) ) / ( ( ( ( ( -u ( 2 x. ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) ^ 3
      ) ) - ( ; 2 7 x. ( ( ( C - ( ( A x. B ) / 2 ) ) + ( ( A ^ 3 ) / 8 ) ) ^ 2
      ) ) ) + ( ; 7 2 x. ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) x. ( ( D - ( ( C
      x. A ) / 4 ) ) + ( ( ( ( A ^ 2 ) x. B ) / ; 1 6 ) - ( ( 3 / ; ; 2 5 6 )
      x. ( A ^ 4 ) ) ) ) ) ) ) + ( sqrt ` ( ( ( ( -u ( 2 x. ( ( B - ( ( 3 / 8 )
      x. ( A ^ 2 ) ) ) ^ 3 ) ) - ( ; 2 7 x. ( ( ( C - ( ( A x. B ) / 2 ) ) + (
      ( A ^ 3 ) / 8 ) ) ^ 2 ) ) ) + ( ; 7 2 x. ( ( B - ( ( 3 / 8 ) x. ( A ^ 2 )
      ) ) x. ( ( D - ( ( C x. A ) / 4 ) ) + ( ( ( ( A ^ 2 ) x. B ) / ; 1 6 ) -
      ( ( 3 / ; ; 2 5 6 ) x. ( A ^ 4 ) ) ) ) ) ) ) ^ 2 ) - ( 4 x. ( ( ( ( B - (
      ( 3 / 8 ) x. ( A ^ 2 ) ) ) ^ 2 ) + ( ; 1 2 x. ( ( D - ( ( C x. A ) / 4 )
      ) + ( ( ( ( A ^ 2 ) x. B ) / ; 1 6 ) - ( ( 3 / ; ; 2 5 6 ) x. ( A ^ 4 ) )
      ) ) ) ) ^ 3 ) ) ) ) ) / 2 ) ^c ( 1 / 3 ) ) ) ) / 3 ) ) / 2 ) ) ) ) ) ) )
      ) ) $=
      ( cdiv co c2 cexp cmul cmin eqidd c3 c8 caddc c4 c1 c6 cdc c5 cneg c7 cfv
      csqrt ccxp quart ) ABCDECUAUBNOBPQOZROSOZDBCROPNOSOBUAQOUBNOUCOZEDBROUDNO
      SOUOCROUEUFUGNOUAPUHUGUFUGNOBUDQOROSOUCOZPUPROPUPUAQOROUIPUJUGUQPQOROSOUJ
      PUGUPURROROUCOZUSPQOUDUPPQOUEPUGURROUCOZUAQOROSOULUKZUCOPNOUEUANOUMOZUCOU
      TVBNOUCOUANOUIZULUKPNOZVBUTBUDNOUIZVDPQOUIUPPNOSOZUQUDNOVDNOZUCOULUKZVFVG
      SOULUKZVCUSVAFGHIJKAVETAUPTAUQTAURTAUTTAUSTAVATAVDTAVCTAVBTLMAVHTAVITUN
      $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Derangements and the Subfactorial
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d f g h m n s x y z A $.  $d b c f g x y F $.  $d c f g h k m n x y z N $.
    $d b k m n $.  $d b c f g h s x y z B $.  $d b c x y C $.  $d b c x y ph $.
    $d n D $.  $d c f n x y K $.  $d b f g x y M $.  $d m n x y S $.  $d f V $.
    $( Lemma for derangements.  (Contributed by Mario Carneiro,
       19-Jan-2015.) $)
    deranglem $p |- ( A e. Fin ->
      { f | ( f : A -1-1-onto-> A /\ ph ) } e. Fin ) $=
      ( cfn wcel cv wf1o wa cab cmap co mapfi wf adantr elmapg imbitrrid abssdv
      wss f1of ssfi syl2anc anidms ) BDEZBBCFZGZAHZCIZDEZUCUCHZBBJKZDEUGUJRUHBB
      LUIUFCUJUFUDUJEUIBBUDMZUEUKABBUDSNBBUDDDOPQUJUGTUAUB $.

    derang.d $e |- D = ( x e. Fin |-> ( # ` { f | ( f : x -1-1-onto-> x /\
      A. y e. x ( f ` y ) =/= y ) } ) ) $.
    $( Define the derangement function, which counts the number of bijections
       from a set to itself such that no element is mapped to itself.
       (Contributed by Mario Carneiro, 19-Jan-2015.) $)
    derangval $p |- ( A e. Fin -> ( D ` A ) =
      ( # ` { f | ( f : A -1-1-onto-> A /\ A. y e. A ( f ` y ) =/= y ) } ) ) $=
      ( cv wf1o cfv wne wral wa cab chash cfn wceq f1oeq2 f1oeq3 bitrd raleq
      anbi12d abbidv fveq2d fvex fvmpt ) ACAGZUFEGZHZBGZUGIUIJZBUFKZLZEMZNICCUG
      HZUJBCKZLZEMZNIODUFCPZUMUQNURULUPEURUHUNUKUOURUHCUFUGHUNUFCUFUGQUFCCUGRSU
      JBUFCTUAUBUCFUQNUDUE $.

    $( The derangement number is a function from finite sets to nonnegative
       integers.  (Contributed by Mario Carneiro, 19-Jan-2015.) $)
    derangf $p |- D : Fin --> NN0 $=
      ( cfn cn0 cv wf1o cfv wne wral cab chash wcel deranglem hashcl syl fmpti
      wa ) AFGAHZUADHZIBHZUBJUCKBUALZTDMZNJZCEUAFOUEFOUFGOUDUADPUEQRS $.

    $( The derangement number of the empty set.  (Contributed by Mario
       Carneiro, 19-Jan-2015.) $)
    derang0 $p |- ( D ` (/) ) = 1 $=
      ( c0 cfv cv wf1o wne wral wa cab chash csn c1 wcel wceq ax-mp cvv cfn 0fi
      derangval ral0 biantru eqid f1o00 mpbiran2 bitr3i abbii eqtr4i fveq2i 0ex
      df-sn hashsng 3eqtri ) FCGZFFDHZIZBHZURGUTJZBFKZLZDMZNGZFOZNGZPFUAQUQVERU
      BABFCDEUCSVDVFNVDURFRZDMVFVCVHDVCUSVHVBUSVABUDUEUSVHFFRFUFFURUGUHUIUJDFUN
      UKULFTQVGPRUMFTUOSUP $.

    $( The derangement number of a singleton.  (Contributed by Mario Carneiro,
       19-Jan-2015.) $)
    derangsn $p |- ( A e. V -> ( D ` { A } ) = 0 ) $=
      ( wcel csn cfv c0 chash cc0 cv wf1o wne wral wa wceq syl cab cfn snfi wss
      derangval ax-mp wf f1of adantr snidg ffvelcdm syl2anr simpr fveq2 neeq12d
      wn id rspcva syl2an nelsn pm2.21dd abssdv ss0 fveq2d eqtrid hash0 eqtrdi
      ex ) CFHZCIZDJZKLJZMVIVKVJVJENZOZBNZVMJZVOPZBVJQZRZEUAZLJZVLVJUBHVKWASCUC
      ABVJDEGUEUFVIVTKLVIVTKUDVTKSVIVSEKVIVSVMKHZVIVSRZCVMJZVJHZWBVSVJVJVMUGZCV
      JHZWEVIVNWFVRVJVJVMUHUICFUJZVJVJCVMUKULWCWDCPZWEUPVIWGVRWIVSWHVNVRUMVQWIB
      CVJVOCSZVPWDVOCVOCVMUNWJUQUOURUSWDCUTTVAVHVBVTVCTVDVEVFVG $.

    $( One half of ~ derangen .  (Contributed by Mario Carneiro,
       22-Jan-2015.) $)
    derangenlem $p |- ( ( A ~~ B /\ B e. Fin ) -> ( D ` A ) <_ ( D ` B ) ) $=
      ( vs cfn wcel wa cv wf1o cfv wne wral ccom syl2anc wceq syl vg vh cen wbr
      vz cab chash cle cdom wex bren birani deranglem adantl wi f1oco ad2ant2lr
      ccnv f1ocnv ad2antlr coass fveq1i wf simprl fvco3 sylan eqtrid ffvelcdmda
      f1of simplrr fveq2 id neeq12d rspcv sylc eqnetrd simpllr f1ocnvfv necon3d
      necomd mpd ralrimiva cbvralvw sylib jca vex f1oeq1 neeq1d ralbidv anbi12d
      ex fveq1 elab cnvex 3imtr4g wb anbi12i wfo wfn f1ofo adantrr f1ofn simplr
      coex simprrl cocan2 syl3anc wf1 f1of1 simprll cocan1 bitrd biimtrid dom2d
      exlimdv mp2d enfii ancoms hashdom mpbird derangval 3brtr4d ) CDUCUDZDIJZK
      ZCCFLZMZBLZYFNZYHOZBCPZKZFUFZUGNZDDYFMZYJBDPZKZFUFZUGNZCENZDENZUHYEYNYSUH
      UDZYMYRUIUDZYECDHLZMZHUJZYRIJZUUCYCUUFYDCDHUKULYDUUGYCYPDFUMUNZYEUUEUUGUU
      CUOZHYEUUEUUIYEUUEKZUAUBYMYRUUDUALZQZUUDURZQZUUDUBLZQZUUMQZIUUJCCUUKMZYHU
      UKNZYHOZBCPZKZDDUUNMZYHUUNNZYHOZBDPZKZUUKYMJZUUNYRJUUJUVBUVGUUJUVBKZUVCUV
      FUVICDUULMZDCUUMMZUVCUUEUURUVJYEUVACCDUUDUUKUPUQZUUEUVKYEUVBCDUUDUSZUTZDC
      DUULUUMUPRUVIUELZUUNNZUVOOZUEDPUVFUVIUVQUEDUVIUVODJZKZUVPUVOUUKUUMQZNZUUD
      NZUVOUVSUVPUVOUUDUVTQZNZUWBUVOUUNUWCUUDUUKUUMVAVBUVIDCUVTVCZUVRUWDUWBSUVI
      DCUVTMZUWEUVIUURUVKUWFUUJUURUVAVDUVNDCCUUKUUMUPRDCUVTVITZDCUVOUUDUVTVEVFV
      GUVSUVOUUMNZUWAOUWBUVOOUVSUWAUWHUVSUWAUWHUUKNZUWHUVIDCUUMVCZUVRUWAUWISUVI
      UVKUWJUVNDCUUMVITZDCUVOUUKUUMVEVFUVSUWHCJUVAUWIUWHOZUVIDCUVOUUMUWKVHUUJUU
      RUVAUVRVJUUTUWLBUWHCYHUWHSZUUSUWIYHUWHYHUWHUUKVKUWMVLVMVNVOVPVTUVSUWBUVOU
      WHUWAUVSUUEUWACJUWBUVOSUWHUWASUOYEUUEUVBUVRVQUVIDCUVOUVTUWGVHCDUWAUVOUUDV
      RRVSWAVPWBUVQUVEUEBDUVOYHSZUVPUVDUVOYHUVOYHUUNVKUWNVLVMWCWDWEWKYLUVBFUUKU
      AWFZYFUUKSZYGUURYKUVACCYFUUKWGUWPYJUUTBCUWPYIUUSYHYHYFUUKWLWHWIWJWMZYQUVG
      FUUNUULUUMUUDUUKHWFZUWOXDUUDUWRWNXDYFUUNSZYOUVCYPUVFDDYFUUNWGUWSYJUVEBDUW
      SYIUVDYHYHYFUUNWLWHWIWJWMWOUVHUUOYMJZKUVBCCUUOMZYHUUONZYHOZBCPZKZKZUUJUUN
      UUQSZUUKUUOSZWPZUVHUVBUWTUXEUWQYLUXEFUUOUBWFYFUUOSZYGUXAYKUXDCCYFUUOWGUXJ
      YJUXCBCUXJYIUXBYHYHYFUUOWLWHWIWJWMWQUUJUXFUXIUUJUXFKZUXGUULUUPSZUXHUXKDCU
      UMWRZUULCWSZUUPCWSZUXGUXLWPUXKUVKUXMUUEUVKYEUXFUVMUTDCUUMWTTUXKUVJUXNUUJU
      VBUVJUXEUVLXACDUULXBTUXKCDUUPMZUXOUXKUUEUXAUXPYEUUEUXFXCUUJUVBUXAUXDXEZCC
      DUUDUUOUPRCDUUPXBTDCUUMUULUUPXFXGUXKCDUUDXHZCCUUKVCZCCUUOVCZUXLUXHWPUUEUX
      RYEUXFCDUUDXIUTUXKUURUXSUUJUURUVAUXEXJCCUUKVITUXKUXAUXTUXQCCUUOVITCCDUUDU
      UKUUOXKXGXLWKXMXNWKXOXPYEYMIJZUUGUUBUUCWPYECIJZUYAYDYCUYBCDXQXRZYKCFUMTUU
      HYMYRIXSRXTYEUYBYTYNSUYCABCEFGYATYDUUAYSSYCABDEFGYAUNYB $.

    $( The derangement number is a cardinal invariant, i.e. it only depends on
       the size of a set and not on its contents.  (Contributed by Mario
       Carneiro, 22-Jan-2015.) $)
    derangen $p |- ( ( A ~~ B /\ B e. Fin ) -> ( D ` A ) = ( D ` B ) ) $=
      ( cen wbr cfn wcel wa cfv cle derangenlem syl2anc cn0 ffvelcdmi cr nn0re
      wceq ensym adantr enfi biimpar derangf syl adantl letri3 syl2an mpbir2and
      wb ) CDHIZDJKZLZCEMZDEMZUAZUPUQNIZUQUPNIZABCDEFGOUODCHIZCJKZUTUMVAUNCDUBU
      CUMVBUNCDUDUEZABDCEFGOPUOUPQKZUQQKZURUSUTLULZUOVBVDVCJQCEABEFGUFZRUGUNVEU
      MJQDEVGRUHVDUPSKUQSKVFVEUPTUQTUPUQUIUJPUK $.

    subfac.n $e |- S = ( n e. NN0 |-> ( D ` ( 1 ... n ) ) ) $.
    $( The subfactorial is defined as the number of derangements (see
       ~ derangval ) of the set ` ( 1 ... N ) ` .  (Contributed by Mario
       Carneiro, 21-Jan-2015.) $)
    subfacval $p |- ( N e. NN0 -> ( S ` N ) = ( D ` ( 1 ... N ) ) ) $=
      ( c1 cv cfz co cfv cn0 wceq oveq2 fveq2d fvex fvmpt ) FGJFKZLMZCNJGLMZCNO
      DUAGPUBUCCUAGJLQRIUCCST $.

    $( Write the derangement number in terms of the subfactorial.  (Contributed
       by Mario Carneiro, 22-Jan-2015.) $)
    derangen2 $p |- ( A e. Fin -> ( D ` A ) = ( S ` ( # ` A ) ) ) $=
      ( cfn wcel chash cfv c1 cfz co cn0 wceq syl mpancom subfacval cen hashfz1
      hashcl wbr wb fzfid hashen mpbid derangen eqtr2d ) CJKZCLMZEMZNUMOPZDMZCD
      MZULUMQKZUNUPRCUDZABDEFGUMHIUASUOCUBUEZULUPUQRULUOLMUMRZUTULURVAUSUMUCSUO
      JKULVAUTUFULNUMUGUOCUHTUIABUOCDFHUJTUK $.

    $( The subfactorial is a function from nonnegative integers to nonnegative
       integers.  (Contributed by Mario Carneiro, 19-Jan-2015.) $)
    subfacf $p |- S : NN0 --> NN0 $=
      ( c1 cv cfz co cfv cn0 wcel wral wf cfn fzfi derangf ffvelcdmi ax-mp fmpt
      rgenw mpbi ) IFJZKLZCMZNOZFNPNNDQUIFNUGROUIIUFSRNUGCABCEGTUAUBUDFNNUHDHUC
      UE $.

    $( The subfactorial is less than the factorial.  (Contributed by Mario
       Carneiro, 19-Jan-2015.) $)
    subfaclefac $p |- ( N e. NN0 -> ( S ` N ) <_ ( ! ` N ) ) $=
      ( wcel c1 cv cfv wa cab chash cfa cle cfn syl cn0 cfz co wf1o wne wbr wss
      wral anidm abbii fzfid deranglem eqeltrrid simpl ss2abi ssdomg wb hashdom
      cdom mpisyl syl2anc mpbird subfacval wceq derangval eqtrd hashfac hashfz1
      fveq2d eqtr2d 3brtr4d ) GUAJZKGUBUCZVMELZUDZBLZVNMVPUEBVMUHZNZEOZPMZVOEOZ
      PMZGDMZGQMZRVLVTWBRUFZVSWAUSUFZVLWASJZVSWAUGWFVLWAVOVONZEOZSWHVOEVOUIUJVL
      VMSJZWISJVLKGUKZVOVMEULTUMZVRVOEVOVQUNUOVSWASUPUTVLVSSJZWGWEWFUQVLWJWMWKV
      QVMEULTWLVSWASURVAVBVLWCVMCMZVTABCDEFGHIVCVLWJWNVTVDWKABVMCEHVETVFVLWBVMP
      MZQMZWDVLWJWBWPVDWKVMEVGTVLWOGQGVHVIVJVK $.

    $( The subfactorial at zero.  (Contributed by Mario Carneiro,
       19-Jan-2015.) $)
    subfac0 $p |- ( S ` 0 ) = 1 $=
      ( cc0 cfv c1 cfz co c0 cn0 wcel wceq 0nn0 subfacval ax-mp fveq2i derang0
      fz10 3eqtri ) IDJZKILMZCJZNCJKIOPUEUGQRABCDEFIGHSTUFNCUCUAABCEGUBUD $.

    $( The subfactorial at one.  (Contributed by Mario Carneiro,
       19-Jan-2015.) $)
    subfac1 $p |- ( S ` 1 ) = 0 $=
      ( c1 cfv cfz co csn cc0 cn0 wcel wceq 1nn0 subfacval ax-mp cz fzsn fveq2i
      1z derangsn 3eqtri ) IDJZIIKLZCJZIMZCJZNIOPZUGUIQRABCDEFIGHSTUHUJCIUAPUHU
      JQUDIUBTUCULUKNQRABICEOGUETUF $.

    ${
      subfacp1lem.a $e |- A = { f |
        ( f : ( 1 ... ( N + 1 ) ) -1-1-onto-> ( 1 ... ( N + 1 ) ) /\
          A. y e. ( 1 ... ( N + 1 ) ) ( f ` y ) =/= y ) } $.
      ${
        subfacp1lem1.n $e |- ( ph -> N e. NN ) $.
        subfacp1lem1.m $e |- ( ph -> M e. ( 2 ... ( N + 1 ) ) ) $.
        subfacp1lem1.x $e |- M e. _V $.
        subfacp1lem1.k $e |- K = ( ( 2 ... ( N + 1 ) ) \ { M } ) $.
        $( Lemma for ~ subfacp1 .  The set ` K ` together with ` { 1 , M } `
           partitions the set ` 1 ... ( N + 1 ) ` .  (Contributed by Mario
           Carneiro, 23-Jan-2015.) $)
        subfacp1lem1 $p |- ( ph ->
          ( ( K i^i { 1 , M } ) = (/) /\
            ( K u. { 1 , M } ) = ( 1 ... ( N + 1 ) ) /\
            ( # ` K ) = ( N - 1 ) ) ) $=
          ( c1 wcel cpr cin c0 wceq cun caddc co cfz chash cfv cmin cv disj wne
          wn wo wa csn cdif cle wbr eldifi elfzle1 clt 1lt2 1re 2re ltnlei mpbi
          breq2 mtbiri necon2ai 3syl eldifsni jca eleq2s neanior sylib vex elpr
          c2 sylnibr mprgbir a1i uncom cz 1z ax-mp uneq1i undif1 eqtr2i uneq12i
          fzsn df-pr equncomi uneq2i unass eqtr4i 3eqtr4i wss snssd df-2 oveq1i
          ssequn2 eqtrdi uneq2d peano2nnd nnuz eleqtrdi eluzfz1 fzsplit eqtr3id
          cuz cn eqtr4d oveq2i cfn fzfi diffi eqeltri hashun mp3an fveq2d neeq1
          syl vtoclga necomd cvv wb 1ex hashprg mp2an oveq2d 3eqtr3a cn0 nnnn0d
          prfi hashfz1 eqtr3d nncnd 2cnd hashcl nn0cni subadd2d mpbird pnpcan2d
          cc 1cnd 3jca ) AISJUAZUBUCUDZIUUJUEZSKSUFUGZUHUGZUDIUIUJZKSUKUGZUDUUK
          AUUKBULZUUJTZUOBIBIUUJUMUUQITZUUQSUDZUUQJUDUPZUURUUSUUQSUNZUUQJUNZUQZ
          UVAUOUVDUUQWAUUMUHUGZJURZUSZIUUQUVGTZUVBUVCUVHUUQUVETZWAUUQUTVAZUVBUU
          QUVEUVFVBUUQWAUUMVCZUVJUUQSUUTUVJWASUTVAZSWAVDVAUVLUOVESWAVFVGVHVIUUQ
          SWAUTVJVKVLZVMUUQUVEJVNVORVPUUQSUUQJVQVRUUQSJBVSVTWBWCZWDAUULSSUHUGZU
          VEUVFUEZUEZUUNSURZIUVFUEZUEUVSUVRUEZUVQUULUVRUVSWEUVOUVRUVPUVSSWFTUVO
          UVRUDWGSWMWHUVSUVGUVFUEUVPIUVGUVFRWIUVEUVFWJWKWLUULIUVFUVRUEZUEUVTUUJ
          UWAIUUJUVRUVFSJWNWOWPIUVFUVRWQWRWSAUVQUVOSSUFUGZUUMUHUGZUEZUUNAUVPUWC
          UVOAUVPUVEUWCAUVFUVEWTUVPUVEUDAJUVEPXAUVFUVEXDVRWAUWBUUMUHXBXCXEXFAUU
          MSXMUJZTSUUNTUUNUWDUDAUUMXNUWEAKOXGZXHXISUUMXJSSUUMXKVMXOXLZAUUMWAUKU
          GZUUMUWBUKUGUUOUUPWAUWBUUMUKXBXPAUWHUUOUDUUOWAUFUGZUUMUDAUUNUIUJZUWIU
          UMAUULUIUJZUUOUUJUIUJZUFUGZUWJUWIIXQTZUUJXQTUUKUWKUWMUDIUVGXQRUVEXQTU
          VGXQTWAUUMXRUVEUVFXSWHXTZSJYQUVNIUUJYAYBAUULUUNUIUWGYCAUWLWAUUOUFASJU
          NZUWLWAUDZAJSAJUVETJSUNZPUVBUWRBJUVEUUQJSYDUVIUVJUVBUVKUVMYEYFYEYGSYH
          TJYHTUWPUWQYIYJQSJYHYHYKYLVRYMYNAUUMYOTUWJUUMUDAUUMUWFYPUUMYRYEYSAUUM
          WAUUOAUUMUWFYTAUUAUUOUUGTAUUOUWNUUOYOTUWOIUUBWHUUCWDUUDUUEAKSSAKOYTAU
          UHZUWSUUFYNUUI $.

        ${
          subfacp1lem2.5 $e |- F =
            ( G u. { <. 1 , M >. , <. M , 1 >. } ) $.
          subfacp1lem2.6 $e |- ( ph -> G : K -1-1-onto-> K ) $.
          $( Lemma for ~ subfacp1 .  Properties of a bijection on ` K `
             augmented with the two-element flip to get a bijection on
             ` K u. { 1 , M } ` .  (Contributed by Mario Carneiro,
             23-Jan-2015.) $)
          subfacp1lem2a $p |- ( ph ->
            ( F : ( 1 ... ( N + 1 ) ) -1-1-onto-> ( 1 ... ( N + 1 ) ) /\
              ( F ` 1 ) = M /\ ( F ` M ) = 1 ) ) $=
            ( c1 caddc co cfz wf1o cfv wceq cpr cun cop cin c0 cz cvv f1oprswap
            wcel mp2an a1i chash cmin subfacp1lem1 simp1d f1oun syl22anc simp2d
            1z wb f1oeq1 ax-mp f1oeq2 bitr3id f1oeq3 bitrd syl mpbid csn f1ofun
            wfun wss cdm snsspr1 ssun2 sseqtrri sstri 1ex snid eleqtrri funssfv
            dmsnop mp3an23 fvsn eqtrdi snsspr2 3jca ) AUCMUCUDUEUFUEZWQIUGZUCIU
            HZLUILIUHZUCUIAKUCLUJZUKZXBJUCLULZLUCULZUJZUKZUGZWRAKKJUGXAXAXEUGZK
            XAUMUNUIZXIXGUBXHAUCUOURLUPURXHVHSUCLUOUPUQUSUTAXIXBWQUIZKVAUHMUCVB
            UEUIZABCDEFGHKLMNOPQRSTVCZVDZXMKKXAXAJXEVEVFAXJXGWRVIAXIXJXKXLVGXJX
            GWQXBIUGZWRXGXBXBIUGZXJXNIXFUIXOXGVIUAXBXBIXFVJVKXBWQXBIVLVMXBWQWQI
            VNVOVPVQZAWSUCXCVRZUHZLAIVTZWSXRUIZAWRXSXPWQWQIVSVPZXSXQIWAUCXQWBZU
            RXTXQXEIXCXDWCXEXFIXEJWDUAWEZWFUCUCVRYBUCWGWHUCLSWKWIUCIXQWJWLVPUCL
            WGSWMWNAWTLXDVRZUHZUCAXSWTYEUIZYAXSYDIWALYDWBZURYFYDXEIXCXDWOYCWFLL
            VRYGLSWHLUCWGWKWILIYDWJWLVPLUCSWGWMWNWP $.

          $( Lemma for ~ subfacp1 .  Properties of a bijection on ` K `
             augmented with the two-element flip to get a bijection on
             ` K u. { 1 , M } ` .  (Contributed by Mario Carneiro,
             23-Jan-2015.) $)
          subfacp1lem2b $p |- ( ( ph /\ X e. K ) -> ( F ` X ) = ( G ` X ) ) $=
            ( wcel wa wfun wss cdm cfv wceq caddc cfz wf1o subfacp1lem2a simp1d
            c1 co f1ofun syl adantr cop cpr cun ssun1 sseqtrri a1i f1odm eleq2d
            biimpar funssfv syl3anc ) ANKUDZUEZIUFZJIUGZNJUHZUDZNIUINJUIUJAVNVL
            AUPMUPUKUQULUQZVRIUMZVNAVSUPIUILUJLIUIUPUJABCDEFGHIJKLMOPQRSTUAUBUC
            UNUOVRVRIURUSUTVOVMJJUPLVALUPVAVBZVCIJVTVDUBVEVFAVQVLAVPKNAKKJUMVPK
            UJUCKKJVGUSVHVINIJVJVK $.
        $}

        ${
          subfacp1lem3.b $e |- B = { g e. A |
            ( ( g ` 1 ) = M /\ ( g ` M ) = 1 ) } $.
          subfacp1lem3.c $e |- C = { f | ( f : K -1-1-onto-> K /\
            A. y e. K ( f ` y ) =/= y ) } $.
          $( Lemma for ~ subfacp1 .  In ~ subfacp1lem6 we cut up the set of all
             derangements on ` 1 ... ( N + 1 ) ` first according to the value
             at ` 1 ` , and then by whether or not
             ` ( f `` ( f `` 1 ) ) = 1 ` .  In this lemma, we show that the
             subset of all ` N + 1 ` derangements that satisfy this for fixed
             ` M = ( f `` 1 ) ` is in bijection with ` N - 1 ` derangements, by
             simply dropping the ` x = 1 ` and ` x = M ` points from the
             function to get a derangement on
             ` K = ( 1 ... ( N - 1 ) ) \ { 1 , M } ` .  (Contributed by Mario
             Carneiro, 23-Jan-2015.) $)
          subfacp1lem3 $p |- ( ph -> ( # ` B ) = ( S ` ( N - 1 ) ) ) $=
            ( vb vc chash cfv c1 cmin co cvv cv cres cmpt wcel cfn wss cfz wf1o
            caddc wne wral wa cab fzfi deranglem ax-mp eqeltri wceq ssrab3 ssfi
            mp2an elexi cop cpr cun eqid wfo fveq1 eqeq1d anbi12d elrab2 bilani
            cdif weq simpld vex f1oeq1 neeq1d ralbidv elab2 wf simprbi 3syl wfn
            wb f1ofn syl cin c0 simp2d sseqtrid adantr fnssresd simprd eqeltrdi
            1ex fveq2 eleq1d ralpr sylanbrc fvres ralbiia sylibr fveqeq2 rspcev
            sylancr eqeq2 rexbidv eqcom eqtrid simp1d syl2anc mpbid ralbidva cn
            c2 eqnetrd simp3d id neeq12d ralunb adantrr adantrl eqeq12d bitr4di
            wrex eqtr4d eqeq2d eqfnfv a1i ccnv sylib f1of1 df-f1 fnresdm mpbird
            wfun wf1 f1ofo ssun2 subfacp1lem1 prid2 prid1 bitrid rexbiia ralbii
            ffnfv dffo3 resdif syl3anc uncom incom reseq2 f1oeq1d f1oeq2 f1oeq3
            3bitrd ssun1 ssralv sylc resex sylan9eq subfacp1lem2a subfacp1lem2b
            uneqdifeq r19.21bi ralrimiva cuz elfzuz eluz2b3 raleqtrdv prex unex
            necomd jca biantrud raleqdv 3bitr3rd bitrdi f1o2d hasheqf1od fveq2i
            3bitr4d csn diffi derangval derangen2 3eqtr2ri fveq2d eqtr3id eqtrd
            ) AEUFUGFUFUGZNUHUIUJZHUGZAEFUKUDEUDULZLUMZUNZEUKUOAEUPDUPUOEDUQEUP
            UODUHNUHUTUJZURUJZUXJIULZUSZCULZUXKUGZUXMVAZCUXJVBZVCZIVDZUPQUXJUPU
            OUXRUPUOUHUXIVEUXPUXJIVFVGVHUHJULZUGZMVIZMUXSUGZUHVIZVCZJDEUBVJDEVK
            VLVMUUAAUDUEEFUXGUEULZUHMVNZMUHVNZVOZVPZUXHUXHVQAUXFEUOZVCZLLUXGUSZ
            UXMUXFUGZUXMVAZCLVBZUXGFUOUYKUXJUHMVOZWDZUYQUXFUYQUMZUSZUYLUYKUXFUU
            BUUHZUXJUXJUXFUXJUMZVRZUYPUYPUXFUYPUMZVRZUYSUYKUXJUXJUXFUSZUXJUXJUX
            FUUIZUYTUYKVUEUYNCUXJVBZUYKUXFDUOZVUEVUGVCZUYKVUHUHUXFUGZMVIZMUXFUG
            ZUHVIZVCZUYJVUHVUNVCAUYDVUNJUXFDEJUDWEZUYAVUKUYCVUMVUOUXTVUJMUHUXSU
            XFVSVTVUOUYBVULUHMUXSUXFVSVTWAUBWBWCZWFUXQVUIIUXFDUDWGZIUDWEZUXLVUE
            UXPVUGUXJUXJUXKUXFWHVURUXOUYNCUXJVURUXNUYMUXMUXMUXKUXFVSWIWJWAQWKUU
            CZWFZUXJUXJUXFUUDVUFUXJUXJUXFWLUYTUXJUXJUXFUUEWMWNUYKUXJUXJVUAUSZVU
            BUYKVVAVUEVUTUYKUXFUXJWOZVUAUXFVIVVAVUEWPUYKVUEVVBVUTUXJUXJUXFWQWRZ
            UXJUXFUUFUXJUXJVUAUXFWHWNUUGUXJUXJVUAUUJWRUYKUYPUYPVUCWLZBULZUXMVUC
            UGZVIZCUYPYQZBUYPVBZVUDUYKVUCUYPWOVVEVUCUGZUYPUOZBUYPVBZVVDUYKUXJUY
            PUXFVVCAUYPUXJUQZUYJALUYPVPZUYPUXJUYPLUUKALUYPWSZWTVIZVVNUXJVIZLUFU
            GZUXDVIZABCDGHIKLMNOPQRSTUAUULZXAZXBZXCXDUYKVVEUXFUGZUYPUOZBUYPVBZV
            VLUYKVUJUYPUOZVULUYPUOZVWEUYKVUJMUYPUYKVUKVUMUYKVUHVUNVUPXEZWFZUHMT
            UUMZXFUYKVULUHUYPUYKVUKVUMVWHXEZUHMXGUUNZXFVWDVWFVWGBUHMXGTVVEUHVIZ
            VWCVUJUYPVVEUHUXFXHXIVVEMVIZVWCVULUYPVVEMUXFXHXIXJXKVVKVWDBUYPVVEUY
            PUOVVJVWCUYPVVEUYPUXFXLXIXMXNBUYPUYPVUCUURXKUYKUYMVVEVIZCUYPYQZBUYP
            VBZVVIUYKUYMUHVIZCUYPYQZUYMMVIZCUYPYQZVWQUYKMUYPUOVUMVWSVWJVWKVWRVU
            MCMUYPUXMMUHUXFXOXPXQUYKUHUYPUOVUKVXAVWLVWIVWTVUKCUHUYPUXMUHMUXFXOX
            PXQVWPVWSVXABUHMXGTVWMVWOVWRCUYPVVEUHUYMXRXSVWNVWOVWTCUYPVVEMUYMXRX
            SXJXKVVHVWPBUYPVVGVWOCUYPVVGVVFVVEVIUXMUYPUOZVWOVVEVVFXTVXBVVFUYMVV
            EUXMUYPUXFXLVTUUOUUPUUQXNCBUYPUYPVUCUUSXKUXJUYPUXJUYPUXFUUTUVAUYKUY
            QLVIZUYSUYLWPAVXCUYJAUYPLVPZUXJVIZVXCAVXDVVNUXJUYPLUVBVWAYAAVVMUYPL
            WSZWTVIVXEVXCWPVWBAVXFVVOWTUYPLUVCAVVPVVQVVSVVTYBYAUYPLUXJUVPYCYDXC
            VXCUYSUYQUYQUXGUSLUYQUXGUSUYLVXCUYQUYQUYRUXGUYQLUXFUVDUVEUYQLUYQUXG
            UVFUYQLLUXGUVGUVHWRYDUYKLUXJUQZVUGUYOAVXGUYJAVVNLUXJLUYPUVIVWAXBZXC
            UYKVUEVUGVUSXEUYNCLUXJUVJUVKLLUXKUSZUXOCLVBZVCZUYLUYOVCIUXGFUXFLVUQ
            UVLUXKUXGVIZVXIUYLVXJUYOLLUXKUXGWHVXLUXOUYNCLVXLUXMLUOZVCUXNUYMUXMV
            XLVXMUXNUXMUXGUGZUYMUXMUXKUXGVSUXMLUXFXLZUVMWIYEWAUCWKXKAUYEFUOZVCZ
            UYIDUOZUHUYIUGZMVIZMUYIUGZUHVIZVCZUYIEUOVXQUXJUXJUYIUSZUXMUYIUGZUXM
            VAZCUXJVBZVXRVXQVYDVXTVYBVXQBCDGHIKUYIUYELMNOPQANYFUOVXPRXCZAMYGUXI
            URUJZUOZVXPSXCZTUAUYIVQZVXQLLUYEUSZUXMUYEUGZUXMVAZCLVBZVXPVYMVYPVCZ
            AVXKVYQIUYEFUEWGZIUEWEZVXIVYMVXJVYPLLUXKUYEWHVYSUXOVYOCLVYSUXNVYNUX
            MUXMUXKUYEVSWIWJWAUCWKWCZWFZUVNZYBZVXQVYFCVVNUXJVXQVYFCLVBVYFCUYPVB
            ZVYFCVVNVBVXQVYFCLVXQVXMVCZVYEVYNUXMVXQBCDGHIKUYIUYELMNUXMOPQVYHVYK
            TUAVYLWUAUVOZVXQVYOCLVXQVYMVYPVYTXEUVQYHUVRVXQVXSUHVAZVYAMVAZWUDVXQ
            VXSMUHVXQVYDVXTVYBWUBXAZAMUHVAZVXPAVYJMYGUVSUGUOZWUJSMYGUXIUVTWUKMY
            FUOWUJMUWAWMWNXCZYHVXQVYAUHMVXQVYDVXTVYBWUBYIZVXQMUHWULUWEYHVYFWUGW
            UHCUHMXGTUXMUHVIZVYEVXSUXMUHUXMUHUYIXHZWUNYJYKUXMMVIZVYEVYAUXMMUXMM
            UYIXHZWUPYJYKXJXKVYFCLUYPYLXKAVVQVXPVWAXCUWBUXQVYDVYGVCIUYIDUYEUYHV
            YRUYFUYGUWCUWDUXKUYIVIZUXLVYDUXPVYGUXJUXJUXKUYIWHWURUXOVYFCUXJWURUX
            NVYEUXMUXMUXKUYIVSWIWJWAQWKXKVXQVXTVYBWUIWUMUWFUYDVYCJUYIDEUXSUYIVI
            ZUYAVXTUYCVYBWUSUXTVXSMUHUXSUYIVSVTWUSUYBVYAUHMUXSUYIVSVTWAUBWBXKAU
            YJVXPVCZVCZUYMVYEVIZCUXJVBZVYNVXNVIZCLVBZUXFUYIVIZUYEUXGVIZWVAWVCUY
            MVYNVIZCLVBZWVEWVAWVBCLVBZWVBCVVNVBZWVIWVCWVAWVJWVJWVBCUYPVBZVCWVKW
            VAWVLWVJWVAVUJVXSVIZVULVYAVIZWVLWVAVUJMVXSAUYJVUKVXPVWIYMAVXPVXTUYJ
            WUIYNYRWVAVULUHVYAAUYJVUMVXPVWKYMAVXPVYBUYJWUMYNYRWVBWVMWVNCUHMXGTW
            UNUYMVUJVYEVXSUXMUHUXFXHWUOYOWUPUYMVULVYEVYAUXMMUXFXHWUQYOXJXKUWGWV
            BCLUYPYLYPAVXPWVJWVIWPUYJVXQWVBWVHCLWUEVYEVYNUYMWUFYSYEYNWVAWVBCVVN
            UXJAVVQWUTVWAXCUWHUWIWVDWVHCLVXMWVDVYNUYMVIWVHVXMVXNUYMVYNVXOYSVYNU
            YMXTUWJXMYPWVAVVBUYIUXJWOZWVFWVCWPAUYJVVBVXPVVCYMZWVAVYDWVOAVXPVYDU
            YJWUCYNUXJUXJUYIWQWRCUXJUXFUYIYTYCWVAUYELWOZUXGLWOWVGWVEWPWVAVYMWVQ
            AVXPVYMUYJWUAYNLLUYEWQWRWVAUXJLUXFWVPAVXGWUTVXHXCXDCLUYEUXGYTYCUWNU
            WKUWLAUXCVVRHUGZUXEUXCVXKIVDZUFUGZLGUGZWVRFWVSUFUCUWMLUPUOZWWAWVTVI
            LVYIMUWOZWDZUPUAVYIUPUOWWDUPUOYGUXIVEVYIWWCUWPVGVHZBCLGIOUWQVGWWBWW
            AWVRVIWWEBCLGHIKOPUWRVGUWSAVVRUXDHAVVPVVQVVSVVTYIUWTUXAUXB $.
        $}

        ${
          subfacp1lem5.b $e |- B = { g e. A |
            ( ( g ` 1 ) = M /\ ( g ` M ) =/= 1 ) } $.
          subfacp1lem5.f $e |- F =
            ( ( _I |` K ) u. { <. 1 , M >. , <. M , 1 >. } ) $.
          $( Lemma for ~ subfacp1 .  The function ` F ` , which swaps ` 1 `
             with ` M ` and leaves all other elements alone, is a bijection of
             order ` 2 ` , i.e. it is its own inverse.  (Contributed by Mario
             Carneiro, 19-Jan-2015.) $)
          subfacp1lem4 $p |- ( ph -> `' F = F ) $=
            ( c1 caddc co cfz ccnv wf1o wfn cfv wceq cid cres a1i subfacp1lem2a
            f1oi simp1d f1ocnv f1ofn 3syl syl cv wcel wa cpr wo cun cin c0 cmin
            chash subfacp1lem1 simp2d eleq2d biimpar sylib subfacp1lem2b fvresi
            elun adantl eqtrd fveq2d elpr simp3d 2fveq3 eqeq12d syl5ibrcom jaod
            vex id imp sylan2b jaodan syldan wi adantr f1of ffvelcdmda f1ocnvfv
            wf syl2anc mpd eqfnfvd ) ABUDNUDUEUFUGUFZKUHZKAXEXEKUIZXEXEXFUIXFXE
            UJAXGUDKUKZMULZMKUKZUDULZABCDFGHJKUMLUNZLMNOPQRSTUAUCLLXLUIALUQUOZU
            PZURZXEXEKUSXEXEXFUTVAAXGKXEUJXOXEXEKUTVBABVCZXEVDZVEZXPKUKZKUKZXPU
            LZXPXFUKXSULZAXQXPLVDZXPUDMVFZVDZVGZYAXRXPLYDVHZVDZYFAYHXQAYGXEXPAL
            YDVIVJULYGXEULLVLUKNUDVKUFULABCDFGHJLMNOPQRSTUAVMVNVOVPXPLYDVTVQAYC
            YAYEAYCVEZXTXSXPYIXSXPKYIXSXPXLUKZXPABCDFGHJKXLLMNXPOPQRSTUAUCXMVRY
            CYJXPULALXPVSWAWBZWCYKWBYEAXPUDULZXPMULZVGZYAXPUDMBWJWDAYNYAAYLYAYM
            AYAYLXHKUKZUDULAYOXJUDAXHMKAXGXIXKXNVNZWCAXGXIXKXNWEZWBYLXTYOXPUDXP
            UDKKWFYLWKWGWHAYAYMXJKUKZMULAYRXHMAXJUDKYQWCYPWBYMXTYRXPMXPMKKWFYMW
            KWGWHWIWLWMWNWOXRXGXSXEVDYAYBWPAXGXQXOWQAXEXEXPKAXGXEXEKXAXOXEXEKWR
            VBWSXEXEXSXPKWTXBXCXD $.

          subfacp1lem5.c $e |- C = { f | ( f : ( 2 ... ( N + 1 ) ) -1-1-onto->
      ( 2 ... ( N + 1 ) ) /\ A. y e. ( 2 ... ( N + 1 ) ) ( f ` y ) =/= y ) } $.
          $( Lemma for ~ subfacp1 .  In ~ subfacp1lem6 we cut up the set of all
             derangements on ` 1 ... ( N + 1 ) ` first according to the value
             at ` 1 ` , and then by whether or not
             ` ( f `` ( f `` 1 ) ) = 1 ` .  In this lemma, we show that the
             subset of all ` N + 1 ` derangements with
             ` ( f `` ( f `` 1 ) ) =/= 1 ` for fixed ` M = ( f `` 1 ) ` is in
             bijection with derangements of ` 2 ... ( N + 1 ) ` , because
             pre-composing with the function ` F ` swaps ` 1 ` and ` M ` and
             turns the function into a bijection with ` ( f `` 1 ) = 1 ` and
             ` ( f `` x ) =/= x ` for all other ` x ` , so dropping the point
             at ` 1 ` yields a derangement on the ` N ` remaining points.
             (Contributed by Mario Carneiro, 23-Jan-2015.) $)
          subfacp1lem5 $p |- ( ph -> ( # ` B ) = ( S ` N ) ) $=
            ( vb vc chash cfv cvv cv ccom c2 c1 caddc co cfz cres wcel cfn wf1o
            wss wne wral cab fzfi ax-mp eqeltri wceq mp2an a1i cop csn cun cdif
            ccnv wfun wfo wf1 cid weq fveq1 eqeq1d neeq1d anbi12d elrab2 bilani
            wa simpld vex f1oeq1 ralbidv elab2 sylib f1oco syl2an2r f1of1 wf wb
            wfn f1ofn f1ofo syl 1ex cn nnuz eleqtrdi adantr syl2anc f1of fvco3d
            cuz simprd fveq2d 3eqtrd eqtrd f1oeq1d syl3anc 1z cin c0 wn sylancl
            sselid ad2antrr neeqtrrd fveq2 neeq12d syl5ibrcom adantrr necomd wi
            eqnetrd f1ocnvfv necon3d mpd sylanbrc funssfv adantrl cmin elexi cz
            cmpt deranglem ssrab3 ssfi eqid subfacp1lem2a df-f1 simprbi fnresdm
            f1oi simp1d 3syl 4syl mpbird f1osn peano2nnd eluzfz1 fnressn simp3d
            opeq2d sneqd mpbiri resdif fzsplit fzsn 1p1e2 uneq12i eqtr2di snssd
            oveq1i incom cle wbr clt 1lt2 1re 2re ltnlei mpbi elfzle1 mto mpbir
            disjsn eqtri mpbid reseq2 f1oeq2 f1oeq3 eqsstrri simpr subfacp1lem4
            uneqdifeq 3bitrd fzp1ss fveq1d sseli r19.21bi sylan2 eleq2i eldifsn
            bitri subfacp1lem2b fvresi sylan2br adantlr expr pm2.61dne ffvelcdm
            adantl syl2an ralrimiva cpr fex prex unex coex resex fvres sylan9eq
            difexg ralbidva f1oun mpanr12 bitrd biimpa syldan fvco3 wo eleqtrrd
            sylancr sylan elun nelne2 simp2d f1ofun ssun1 snid eleqtrri mp3an23
            cdm dmsnop fvsn eqtrdi 3netr4d elsni imp ssun2 f1odm eleq2d biimpar
            ffvelcdmd jaodan ffvelcdmda snex id rspcdva jca cocan1 coass coeq1d
            fcod f1ococnv1 eqtr3d fcoi2 eqtr3id eqtr4d eqeq12d sylibr biantrurd
            ralsn ralunb bitr4di eqcomd adantlrl raleqdv eqfnfv fnssres 3bitr4d
            3bitr3rd eqcom bitrdi 3bitr3d hasheqf1od derangen2 derangval fveq2i
            f1o2d eqtr4di eluzp1p1 df-2 eleqtrrdi nncnd 2cnd 1cnd subsubd 2m1e1
            hashfz oveq2i cc ax-1cn pncan eqtrid 3eqtr2d ) AEUHUIFUHUIZOHUIZAEF
            UJUFELUFUKZULZUMOUNUOUPZUQUPZURZUUCZEUJUSAEUTDUTUSEDVBEUTUSDUNVXJUQ
            UPZVXNIUKZVAZCUKZVXOUIZVXQVCZCVXNVDZWHZIVEZUTRVXNUTUSVYBUTUSUNVXJVF
            VXTVXNIUUDVGVHUNJUKZUIZNVIZNVYCUIZUNVCZWHZJDEUCUUEDEUUFVJUUAVKAUFUG
            EFVXLLUNUNVLZVMZUGUKZVNZULZVXMVXMUUGAVXHEUSZWHZVXKVXKVXLVAZVXQVXIUI
            ZVXQVCZCVXKVDZVXLFUSVYOVXNUNVMZVOZWUAVXIWUAURZVAZVYPVYOVXIVPVQZVXNV
            XNVXIVXNURZVRZVYTVYTVXIVYTURZVRZWUCVYOVXNVXNVXIVAZVXNVXNVXIVSZWUDAV
            XNVXNLVAZVYNVXNVXNVXHVAZWUIAWUKUNLUIZNVIZNLUIZUNVIZABCDGHIKLVTMURZM
            NOPQRSTUAUBUDMMWUQVAZAMUULZVKZUUHZUUMZVYOWULVXQVXHUIZVXQVCZCVXNVDZV
            YOVXHDUSZWULWVEWHZVYOWVFUNVXHUIZNVIZNVXHUIZUNVCZWHZVYNWVFWVLWHAVYHW
            VLJVXHDEJUFWAZVYEWVIVYGWVKWVMVYDWVHNUNVYCVXHWBWCWVMVYFWVJUNNVYCVXHW
            BWDWEUCWFWGZWIVYAWVGIVXHDUFWJZIUFWAZVXPWULVXTWVEVXNVXNVXOVXHWKWVPVX
            SWVDCVXNWVPVXRWVCVXQVXQVXOVXHWBWDWLWERWMWNZWIZVXNVXNVXNLVXHWOWPZVXN
            VXNVXIWQWUJVXNVXNVXIWRZWUDVXNVXNVXIUUIUUJUUNVYOVXNVXNWUEVAZWUFVYOWW
            AWUIWVSVYOWUIVXIVXNWTZWUEVXIVIWWAWUIWSWVSVXNVXNVXIXAZVXNVXIUUKVXNVX
            NWUEVXIWKUUOUUPVXNVXNWUEXBXCVYOVYTVYTWUGVAZWUHVYOWWDVYTVYTVYJVAZUNU
            NXDXDUUQZVYOVYTVYTWUGVYJVYOWUGUNUNVXIUIZVLZVMZVYJVYOWWBUNVXNUSZWUGW
            WIVIVYOWUIWWBWVSWWCXCZAWWJVYNAVXJUNXLUIZUSWWJAVXJXEWWLAOSUURZXFXGUN
            VXJUUSXCZXHZVXNUNVXIUUTXIVYOWWHVYIVYOWWGUNUNVYOWWGWVHLUIWUOUNVYOVXN
            VXNUNLVXHVYOWULVXNVXNVXHWRZWVRVXNVXNVXHXJXCZWWOXKVYOWVHNLVYOWVIWVKV
            YOWVFWVLWVNXMZWIXNAWUPVYNAWUKWUNWUPWVAUVAZXHZXOZUVBUVCXPXQUVDVYTVYT
            WUGXBXCVXNVYTVXNVYTVXIUVEXRVYOWUAVXKVIZWUCVYPWSAWXBVYNAVYTVXKVNZVXN
            VIZWXBAVXNUNUNUQUPZUNUNUOUPZVXJUQUPZVNZWXCAWWJVXNWXHVIWWNUNUNVXJUVF
            XCWXEVYTWXGVXKUNUUBUSZWXEVYTVIXSUNUVGVGWXFUMVXJUQUVHUVLZUVIUVJZAVYT
            VXNVBVYTVXKXTZYAVIZWXDWXBWSAUNVXNWWNUVKWXLVXKVYTXTZYAVYTVXKUVMWXNYA
            VIUNVXKUSZYBZWXOUMUNUVNUVOZUNUMUVPUVOWXQYBUVQUNUMUVRUVSUVTUWAUNUMVX
            JUWBUWCZVXKUNUWEUWDUWFZVYTVXKVXNUWNYCUWGXHWXBWUCWUAWUAVXLVAVXKWUAVX
            LVAVYPWXBWUAWUAWUBVXLWUAVXKVXIUWHXQWUAVXKWUAVXLUWIWUAVXKVXKVXLUWJUW
            OXCUWGVYOVYRCVXKVYOVXQVXKUSZWHZVYQWVCLUIZVXQWYAVXNVXNVXQLVXHVYOWWPW
            XTWWQXHWYAVXKVXNVXQVXKWXGVXNWXJWXIWXGVXNVBXSUNVXJUWPVGUWKZVYOWXTUWL
            YDXKWYAVXQLVPZUIZWVCVCWYBVXQVCWYAWYEVXQLUIZWVCAWYEWYFVIZVYNWXTAVXQW
            YDLABCDEGHIJKLMNOPQRSTUAUBUCUDUWMZUWQZYEWYAWVCWYFWYAWVCWYFVCZVXQNWY
            AWYJVXQNVIZWVJWUOVCZVYOWYLWXTVYOWVJUNWUOVYOWVIWVKWWRXMWWTYFXHWYKWVC
            WVJWYFWUOVXQNVXHYGVXQNLYGZYHYIVYOWXTVXQNVCZWYJVYOWXTWYNWHZWHWVCVXQW
            YFVYOWXTWVDWYNWXTVYOVXQVXNUSZWVDVXKVXNVXQWYCUWRZVYOWVDCVXNVYOWULWVE
            WVQXMUWSUWTYJAWYOWYFVXQVIZVYNWYOAVXQMUSZWYRWYSVXQVXKNVMZVOZUSWYOMXU
            AVXQUBUXAVXQVXKNUXBUXCAWYSWHWYFVXQWUQUIZVXQABCDGHIKLWUQMNOVXQPQRSTU
            AUBUDWUTUXDWYSXUBVXQVIAMVXQUXEUXKXPUXFZUXGYFUXHUXIYKYMWYAWYBVXQWYEW
            VCVYOWUKWXTWVCVXNUSZWYBVXQVIWYEWVCVIYLAWUKVYNWVBXHVYOWWPWYPXUDWXTWW
            QWYQVXNVXNVXQVXHUXJUXLVXNVXNWVCVXQLYNWPYOYPYMUXMVXKVXKVXOVAZVXSCVXK
            VDZWHZVYPVYSWHIVXLFVXIVXKLVXHLWUQUNNVLZNUNVLZUXNZVNUJUDWUQXUJMMWUQW
            RZMUJUSWUQUJUSWURXUKWUSMMWUQXJVGMXUAUJUBVXKUTUSZXUAUJUSUMVXJVFZVXKW
            YTUTUYBVGVHMMUJWUQUXOVJXUHXUIUXPUXQVHZWVOUXRUXSVXOVXLVIZXUEVYPXUFVY
            SVXKVXKVXOVXLWKXUOVXSVYRCVXKXUOWXTWHVXRVYQVXQXUOWXTVXRVXQVXLUIZVYQV
            XQVXOVXLWBVXQVXKVXIUXTZUYAWDUYCWEUEWMYQAVYKFUSZWHZVYMDUSZUNVYMUIZNV
            IZNVYMUIZUNVCZWHZVYMEUSXUSVXNVXNVYMVAZVXQVYMUIZVXQVCZCVXNVDZXUTAWUK
            XURVXNVXNVYLVAZXVFWVBAXURWXCWXCVYLVAZXVJXUSWWEVXKVXKVYKVAZXVKWWFXUS
            XVLVXQVYKUIZVXQVCZCVXKVDZXURXVLXVOWHZAXUGXVPIVYKFUGWJZIUGWAZXUEXVLX
            UFXVOVXKVXKVXOVYKWKXVRVXSXVNCVXKXVRVXRXVMVXQVXQVXOVYKWBWDWLWEUEWMWG
            ZWIZWWEXVLWHWXMWXMXVKWXSWXSVYTVYTVXKVXKVYJVYKUYDUYEUYLZAXVKXVJAWXDX
            VKXVJWSWXKWXDXVKVXNWXCVYLVAXVJWXCVXNWXCVYLUWIWXCVXNVXNVYLUWJUYFXCUY
            GUYHZVXNVXNVXNLVYLWOWPXUSXVHCVXNXUSWYPWHZXVGVXQVYLUIZLUIZVXQXUSVXNV
            XNVYLWRZWYPXVGXWEVIXUSXVJXWFXWBVXNVXNVYLXJXCZVXNVXNVXQLVYLUYIUYMXWC
            WYEXWDVCXWEVXQVCXWCWYEWYFXWDAWYGXURWYPWYIYEXUSWYPVXQVYTUSZWXTUYJZWY
            FXWDVCZXWCVXQWXCUSXWIXWCVXQVXNWXCXUSWYPUWLAWXDXURWYPWXKYEUYKVXQVYTV
            XKUYNWNXUSXWHXWJWXTXUSXWHXWJXUSXWJXWHWUMUNVYLUIZVCXUSNUNWUMXWKANUNV
            CZXURANVXKUSZWXPXWLTWXRNUNVXKUYOYCXHAWUNXURAWUKWUNWUPWVAUYPZXHZXUSX
            WKUNVYJUIZUNXUSVYLVQZXWKXWPVIZXUSXVKXWQXWAWXCWXCVYLUYQXCZXWQVYJVYLV
            BUNVYJVUBZUSXWRVYJVYKUYRUNVYTXWTUNXDUYSUNUNXDVUCUYTUNVYLVYJYRVUAXCU
            NUNXDXDVUDVUEZVUFXWHWYFWUMXWDXWKXWHVXQUNLVXQUNVUGZXNXWHVXQUNVYLXXBX
            NYHYIVUHXUSWXTWHZXWDWYFXXCXWDXVMWYFXXCXWQVYKVYLVBZVXQVYKVUBZUSZXWDX
            VMVIZXUSXWQWXTXWSXHXXDXXCVYKVYJVUIZVKXUSXXFWXTXUSXXEVXKVXQXUSXVLXXE
            VXKVIXVTVXKVXKVYKVUJXCZVUKVULVXQVYLVYKYRXRZXXCXVMWYFVCZVXQNXXCXXKWY
            KNVYKUIZWUOVCXXCXXLUNWUOXUSXXLUNVCZWXTXUSXXLVXKUSWXPXXMXUSVXKVXKNVY
            KXUSXVLVXKVXKVYKWRXVTVXKVXKVYKXJXCAXWMXURTXHZVUMZWXRXXLUNVXKUYOYCXH
            AWUPXURWXTWWSYEYFWYKXVMXXLWYFWUOVXQNVYKYGZWYMYHYIXUSWXTWYNXXKXUSWYO
            WHXVMVXQWYFXUSWXTXVNWYNXUSXVNCVXKXUSXVLXVOXVSXMZUWSYJAWYOWYRXURXUCU
            XGYFUXHUXIYMYKVUNUYHYMXWCXWEVXQWYEXWDXUSWUKWYPXWDVXNUSXWEVXQVIWYEXW
            DVIYLAWUKXURWVBXHXUSVXNVXNVXQVYLXWGVUOVXNVXNXWDVXQLYNWPYOYPYMUXMVYA
            XVFXVIWHIVYMDLVYLXUNVYJVYKVYIVUPXVQUXQUXRVXOVYMVIZVXPXVFVXTXVIVXNVX
            NVXOVYMWKXXRVXSXVHCVXNXXRVXRXVGVXQVXQVXOVYMWBWDWLWERWMYQXUSXVBXVDXU
            SXVAXWKLUIWUMNXUSVXNVXNUNLVYLXWGAWWJXURWWNXHXKXUSXWKUNLXXAXNXWOXOXU
            SXVCXXLLUIZUNXUSXVCNVYLUIZLUIXXSXUSVXNVXNNLVYLXWGANVXNUSXURAVXKVXNN
            WYCTYDXHXKXUSXXTXXLLXUSXWQXXDNXXEUSXXTXXLVIXWSXXDXUSXXHVKXUSNVXKXXE
            XXNXXIUYKNVYLVYKYRXRXNXPXUSUNWYDUIZXXLVCXXSUNVCXUSXYANXXLAXYANVIXUR
            AXYAWUMNAUNWYDLWYHUWQXWNXPXHXUSXXLNXUSXVNXXLNVCCVXKNWYKXVMXXLVXQNXX
            PWYKVUQYHXXQXXNVURYKYMXUSXXSUNXYAXXLAWUKXURXXLVXNUSXXSUNVIXYAXXLVIY
            LWVBXUSVXKVXNXXLWYCXXOYDVXNVXNXXLUNLYNWPYOYPYMVUSVYHXVEJVYMDEVYCVYM
            VIZVYEXVBVYGXVDXYBVYDXVANUNVYCVYMWBWCXYBVYFXVCUNNVYCVYMWBWDWEUCWFYQ
            AVYNXURWHZWHZLVXIULZVYMVIZVXIVYLVIZVXHVYMVIVYKVXLVIZXYDVXNVXNLVSZWV
            TXWFXYFXYGWSXYDWUKXYIAWUKXYCWVBXHZVXNVXNLWQXCXYDVXNVXNVXNLVXHXYDWUK
            VXNVXNLWRXYJVXNVXNLXJXCAVYNWWPXURWWQYJZVVCAXURXWFVYNXWGYSVXNVXNVXNL
            VXIVYLVUTXRXYDXYEVXHVYMXYDXYELLULZVXHULZVXHLLVXHVVAXYDXYMVTVXNURZVX
            HULZVXHXYDXYLXYNVXHAXYLXYNVIXYCAWYDLULZXYLXYNAWYDLLWYHVVBAWUKXYPXYN
            VIWVBVXNVXNLVVDXCVVEXHVVBXYDWWPXYOVXHVIXYKVXNVXNVXHVVFXCXPVVGWCXYDX
            YGVXLVYKVIZXYHXYDVYQXWDVIZCVXNVDZXUPXVMVIZCVXKVDZXYGXYQXYDXYRCVXKVD
            ZXYRCWXCVDZYUAXYSXYDYUBXYRCVYTVDZYUBWHYUCXYDYUDYUBXYDWWGXWKVIZYUDXY
            DWWGUNXWKAVYNWWGUNVIXURWXAYJAXURXWKUNVIVYNXXAYSVVHXYRYUECUNXDVXQUNV
            IVYQWWGXWDXWKVXQUNVXIYGVXQUNVYLYGVVIVVLVVJVVKXYRCVYTVXKVVMVVNXYDXYR
            XYTCVXKXYDWXTWHZVYQXUPXWDXVMYUFXUPVYQWXTXUPVYQVIXYDXUQUXKVVOAXURWXT
            XXGVYNXXJVVPVVIUYCXYDXYRCWXCVXNAWXDXYCWXKXHVVQVWAXYDWWBVYLVXNWTZXYG
            XYSWSAVYNWWBXURWWKYJZXYDXVJYUGAXURXVJVYNXWBYSVXNVXNVYLXAXCCVXNVXIVY
            LVVRXIXYDVXLVXKWTZVYKVXKWTZXYQYUAWSXYDWWBVXKVXNVBYUIYUHWYCVXNVXKVXI
            VVSYCXYDXVLYUJAXURXVLVYNXVTYSVXKVXKVYKXAXCCVXKVXLVYKVVRXIVVTVXLVYKV
            WBVWCVWDVWIVWEAVXFVXKUHUIZHUIZVXGXULYULVXFVIXUMXULVXKGUIZYULVXFBCVX
            KGHIKPQVWFXULYUMXUGIVEZUHUIVXFBCVXKGIPVWGFYUNUHUEVWHVWJVVEVGAYUKOHA
            YUKVXJUMYTUPUNUOUPZVXJUMUNYTUPZYTUPZOAVXJUMXLUIZUSYUKYUOVIAVXJWXFXL
            UIZYURAOWWLUSVXJYUSUSAOXEWWLSXFXGUNOVWKXCUMWXFXLVWLVWHVWMUMVXJVWSXC
            AVXJUMUNAVXJWWMVWNAVWOAVWPVWQAYUQVXJUNYTUPZOYUPUNVXJYTVWRVWTAOVXAUS
            UNVXAUSYUTOVIAOSVWNVXBOUNVXCYCVXDVXEXNVVGXP $.
        $}
      $}

      $( Lemma for ~ subfacp1 .  By induction, we cut up the set of all
         derangements on ` N + 1 ` according to the ` N ` possible values of
         ` ( f `` 1 ) ` (since ` ( f `` 1 ) =/= 1 ` ), and for each set for
         fixed ` M = ( f `` 1 ) ` , the subset of derangements with
         ` ( f `` M ) = 1 ` has size ` S ( N - 1 ) ` (by ~ subfacp1lem3 ),
         while the subset with ` ( f `` M ) =/= 1 ` has size ` S ( N ) ` (by
         ~ subfacp1lem5 ).  Adding it all up yields the desired equation
         ` N ( S ( N ) + S ( N - 1 ) ) ` for the number of derangements on
         ` N + 1 ` .  (Contributed by Mario Carneiro, 22-Jan-2015.) $)
      subfacp1lem6 $p |- ( N e. NN ->
        ( S ` ( N + 1 ) ) = ( N x. ( ( S ` N ) + ( S ` ( N - 1 ) ) ) ) ) $=
        ( vg wcel c1 caddc co cfv chash wceq wi vm vz vh cfz crab cmin cmul cn0
        cn cv peano2nn nnnn0d subfacval syl wf1o wne wa cab cfn fzfid derangval
        wral fveq2i eqtr4di wss wf cuz nnuz eleqtrdi eluzfz1 f1of adantr expcom
        ss2abdv weq fveq1 cbvabv 3sstr4g ssabral sylib sylibr fveq2d 3eqtrd cc0
        eleq1 csn oveq2 ax-mp eqtrdi eleq2d elsn rabbidv oveq1d eqeq12d imbi12d
        oveq1 imbi2d c0 wn fveq2 neeq12d neeq1d bitr3id rabeq0 ffvelcdmi nn0cnd
        id ex cun wo unrab cin ssrab2 ssfi mp2an inrab rgenw mpbir eqtri hashun
        wb mp3an cc nncn ad2antlr ax-1cn sylancl mpbi c2 cop mpd eqeq1d anbi12d
        eqid cbvrabv f1oeq1 cbvralvw ralbidv bitrid a2d syl2im eleq1d rabid2 cz
        ffvelcdm elfz1end 1z fzsn fvex bitrdi 1m1e0 hash0 rspcv adantld subfacf
        df-ne nnnn0 nnm1nn0 nn0addcld mul02d 3eqtr4a a1d simplr sylancom imim1d
        peano2fzr elfzp1 fzfi eqeltri fzp1disj inelcm sylan2br necon2bi addsubd
        deranglem a1i subcl ad2antrr adddird mullidd exmidne orcom biantru andi
        bitri rabbii eqtr4i simpr necon3ai adantl imnan cid cdif cres cpr nnne0
        simpll eqeq2i 0cn addcan2 mp3an23 necon3bbid mpbird elfzp12 biimpa df-2
        0p1e1 ord oveq1i eleqtrrdi ovex subfacp1lem5 subfacp1lem3 eqtrid eqtr4d
        oveq12d oveq2d imbitrrid syld nnind mpcom pncan ) HUIMZHNOPZEQZNLUJZQZN
        UYDUDPZMZLCUEZRQZUYDNUFPZHEQZHNUFPZEQZOPZUGPZHUYPUGPUYCUYEUYHDQZCRQZUYK
        UYCUYDUHMUYEUYRSUYCUYDHUKZULABDEFGUYDIJUMUNUYCUYRUYHUYHFUJZUOZBUJZVUAQZ
        VUCUPZBUYHVBZUQZFURZRQZUYSUYCUYHUSMZUYRVUISUYCNUYDUTABUYHDFIVAUNCVUHRKV
        CVDUYCCUYJRUYCUYILCVBZCUYJSUYCCUYILURZVEVUKUYCVUHNVUAQZUYHMZFURCVULUYCV
        UGVUNFUYCNUYHMZVUGUYHUYHVUAVFZVUNUYCUYDNVGQZMZVUOUYCUYDUIVUQUYTVHVIZNUY
        DVJUNZVUBVUPVUFUYHUYHVUAVKVLVUPVUOVUNUYHUYHNVUAUUEVMUUAVNKUYIVUNLFLFVOZ
        UYGVUMUYHNUYFVUAVPZUUBVQVRUYILCVSVTUYILCUUCWAWBWCUYCUYDUYHMZUYKUYQSZUYC
        UYDUIMZVVCUYTUYDUUFVTVVEUYCVVCVVDTZUYTUYCAUJZUYHMZUYGNVVGUDPZMZLCUEZRQZ
        VVGNUFPZUYPUGPZSZTZTUYCVUOUYGNSZLCUEZRQZWDUYPUGPZSZTZTUYCUAUJZUYHMZUYGN
        VWCUDPZMZLCUEZRQZVWCNUFPZUYPUGPZSZTZTUYCVWCNOPZUYHMZUYGNVWMUDPZMZLCUEZR
        QZVWMNUFPZUYPUGPZSZTZTUYCVVFTAUAUYDVVGNSZVVPVWBUYCVXCVVHVUOVVOVWAVVGNUY
        HWEVXCVVLVVSVVNVVTVXCVVKVVRRVXCVVJVVQLCVXCVVJUYGNWFZMVVQVXCVVIVXDUYGVXC
        VVINNUDPZVXDVVGNNUDWGNUUDMVXEVXDSUUGNUUHWHWIWJUYGNNUYFUUIZWKUUJWLWBVXCV
        VMWDUYPUGVXCVVMNNUFPWDVVGNNUFWPUUKWIWMWNWOWQAUAVOZVVPVWLUYCVXGVVHVWDVVO
        VWKVVGVWCUYHWEVXGVVLVWHVVNVWJVXGVVKVWGRVXGVVJVWFLCVXGVVIVWEUYGVVGVWCNUD
        WGWJWLWBVXGVVMVWIUYPUGVVGVWCNUFWPWMWNWOWQVVGVWMSZVVPVXBUYCVXHVVHVWNVVOV
        XAVVGVWMUYHWEVXHVVLVWRVVNVWTVXHVVKVWQRVXHVVJVWPLCVXHVVIVWOUYGVVGVWMNUDW
        GWJWLWBVXHVVMVWSUYPUGVVGVWMNUFWPWMWNWOWQVVGUYDSZVVPVVFUYCVXIVVHVVCVVOVV
        DVVGUYDUYHWEVXIVVLUYKVVNUYQVXIVVKUYJRVXIVVJUYILCVXIVVIUYHUYGVVGUYDNUDWG
        WJWLWBVXIVVMUYLUYPUGVVGUYDNUFWPWMWNWOWQUYCVWAVUOUYCWRRQWDVVSVVTUULUYCVV
        RWRRUYCVVQWSZLCVBZVVRWRSUYCCVXJLURZVEVXKUYCVUHVUMNUPZFURCVXLUYCVUGVXMFU
        YCVUFVXMVUBUYCVUOVUFVXMTVUTVUEVXMBNUYHVUCNSZVUDVUMVUCNVUCNVUAWTVXNXGXAU
        UMUNUUNVNKVXJVXMLFVXJUYGNUPVVAVXMUYGNUUPVVAUYGVUMNVVBXBXCVQVRVXJLCVSVTV
        VQLCXDWAWBUYCUYPUYCUYPUYCUYMUYOUYCHUHMUYMUHMHUUQUHUHHEABDEFGIJUUOZXEUNU
        YCUYNUHMUYOUHMHUURUHUHUYNEVXOXEUNUUSZXFUUTUVAUVBVWCUIMZUYCVWLVXBUYCVXQV
        WLVXBTUYCVXQUQZVWLVWNVWKTVXBVXRVWNVWDVWKVXRVWNVWDVXRVWNVWCVUQMZVWDVXRVW
        NUQZVWCUIVUQUYCVXQVWNUVCVHVIZVWCNUYDUVFUVDXHUVEVXRVWNVWKVXAVXRVWNVWKVXA
        TVWKVXAVXTVWHUYGVWMSZLCUEZRQZOPZVWJVYDOPZSVWHVWJVYDOWPVXTVWRVYEVWTVYFVX
        TVWRVWGVYCXIZRQZVYEVXTVWQVYGRVXTVWQVWFVYBXJZLCUEVYGVXTVWPVYILCVXTVXSVWP
        VYIYAVYAUYGNVWCUVGUNWLVWFVYBLCXKVDWBVWGUSMZVYCUSMZVWGVYCXLZWRSVYHVYESCU
        SMZVWGCVEVYJCVUHUSKVUJVUHUSMNUYDUVHVUFUYHFUVOWHUVIZVWFLCXMCVWGXNXOVYMVY
        CCVEVYKVYNVYBLCXMCVYCXNXOVYLVWFVYBUQZLCUEZWRVWFVYBLCXPVYPWRSVYOWSZLCVBV
        YQLCVWEVWMWFZXLZWRSVYQNVWCUVJVYOVYSWRVYBVWFUYGVYRMVYSWRUPUYGVWMVXFWKUYG
        VWEVYRUVKUVLUVMWHXQVYOLCXDXRXSVWGVYCXTYBWIVXTVWTVWINOPZUYPUGPVWJNUYPUGP
        ZOPVYFVXTVWSVYTUYPUGVXTVWCNNVXQVWCYCMZUYCVWNVWCYDZYEZNYCMZVXTYFUVPZWUFU
        VNWMVXTVWINUYPVXTWUBWUEVWIYCMWUDYFVWCNUVQYGWUFVXTUYPUYCUYPUHMVXQVWNVXPU
        VRXFZUVSVXTWUAVYDVWJOVXTWUAUYPVYDVXTUYPWUGUVTVXTVYDVYBVWMUYFQZNUPZUQZLC
        UEZRQZVYBWUHNSZUQZLCUEZRQZOPZUYPVYDWUKWUOXIZRQZWUQVYCWURRVYCWUJWUNXJZLC
        UEWURVYBWUTLCVYBVYBWUIWUMXJZUQWUTWVAVYBWUMWUIXJWVAWUHNUWAWUMWUIUWBYHUWC
        VYBWUIWUMUWDUWEUWFWUJWUNLCXKUWGVCWUKUSMZWUOUSMZWUKWUOXLZWRSWUSWUQSVYMWU
        KCVEWVBVYNWUJLCXMCWUKXNXOVYMWUOCVEWVCVYNWUNLCXMCWUOXNXOWVDWUJWUNUQZLCUE
        ZWRWUJWUNLCXPWVFWRSWVEWSZLCVBWVGLCWUJWUNWSZTWVGWUIWVHVYBWUNWUHNVYBWUMUW
        HUWIUWJWUJWUNUWKYHXQWVELCXDXRXSWUKWUOXTYBXSVXTWULUYMWUPUYOOVXTABCWUKYIU
        YDUDPZWVIUYFUOZUBUJZUYFQZWVKUPZUBWVIVBZUQZLURDEFUCGUWLWVIVYRUWMZUWNNVWM
        YJVWMNYJUWOXIZWVPVWMHIJKUYCVXQVWNUWQZVXTVWMNNOPZUYDUDPZWVIVXTVWMNSZWSZV
        WMWVTMZVXQWWBUYCVWNVXQWWBVWCWDUPVWCUWPVXQWWAVWCWDWWAVWMWDNOPZSZVXQVWCWD
        SZWWDNVWMUXGUWRVXQWUBWWEWWFYAZWUCWUBWDYCMWUEWWGUWSYFVWCWDNUWTUXAUNXCUXB
        UXCYEVXTWWAWWCVXRVWNWWAWWCXJZVXRVURVWNWWHYAUYCVURVXQVUSVLVWMNUYDUXDUNUX
        EUXHYKYIWVSUYDUDUXFUXIUXJZVWCNOUXKZWVPYNZWUJNUCUJZQZVWMSZVWMWWLQZNUPZUQ
        LUCCLUCVOZVYBWWNWUIWWPWWQUYGWWMVWMNUYFWWLVPYLZWWQWUHWWONVWMUYFWWLVPZXBY
        MYOWVQYNWVOWVIWVIVUAUOZVUEBWVIVBZUQLFVVAWVJWWTWVNWXAWVIWVIUYFVUAYPWVNVU
        CUYFQZVUCUPZBWVIVBVVAWXAWVMWXCUBBWVIUBBVOZWVLWXBWVKVUCWVKVUCUYFWTWXDXGX
        AZYQVVAWXCVUEBWVIVVAWXBVUDVUCVUCUYFVUAVPXBZYRYSYMVQUXLVXTABCWUOWVPWVPUY
        FUOZWVMUBWVPVBZUQZLURDEFUCGWVPVWMHIJKWVRWWIWWJWWKWUNWWNWWONSZUQLUCCWWQV
        YBWWNWUMWXJWWRWWQWUHWWONWWSYLYMYOWXIWVPWVPVUAUOZVUEBWVPVBZUQLFVVAWXGWXK
        WXHWXLWVPWVPUYFVUAYPWXHWXCBWVPVBVVAWXLWVMWXCUBBWVPWXEYQVVAWXCVUEBWVPWXF
        YRYSYMVQUXMUXPUXNUXOUXQWCWNUXRXHYTUXSVMYTUXTUYAYKUYCUYLHUYPUGUYCHYCMWUE
        UYLHSHYDYFHNUYBYGWMWC $.
    $}

    $( A two-term recurrence for the subfactorial.  This theorem allows to
       forget the combinatorial definition of the derangement number in favor
       of the recursive definition provided by this theorem and ~ subfac0 ,
       ~ subfac1 .  (Contributed by Mario Carneiro, 23-Jan-2015.) $)
    subfacp1 $p |- ( N e. NN ->
      ( S ` ( N + 1 ) ) = ( N x. ( ( S ` N ) + ( S ` ( N - 1 ) ) ) ) ) $=
      ( vg vz c1 co cv wf1o cfv wne wral wa weq caddc cfz cab f1oeq1 id neeq12d
      fveq2 cbvralvw fveq1 neeq1d ralbidv bitrid anbi12d cbvabv subfacp1lem6 )
      ABLGLUAMUBMZUPJNZOZKNZUQPZUSQZKUPRZSZJUCCDEFGHIVCUPUPENZOZBNZVDPZVFQZBUPR
      ZSJEJETZURVEVBVIUPUPUQVDUDVBVFUQPZVFQZBUPRVJVIVAVLKBUPKBTZUTVKUSVFUSVFUQU
      GVMUEUFUHVJVLVHBUPVJVKVGVFVFUQVDUIUJUKULUMUNUO $.

    $( A closed-form expression for the subfactorial.  (Contributed by Mario
       Carneiro, 23-Jan-2015.) $)
    subfacval2 $p |- ( N e. NN0 -> ( S ` N ) =
      ( ( ! ` N ) x. sum_ k e. ( 0 ... N ) ( ( -u 1 ^ k ) / ( ! ` k ) ) ) ) $=
      ( wcel cfv cfa cc0 cfz co c1 cmul wceq caddc vm cn0 cneg cv cexp cdiv csu
      wa fveq2 subfac0 eqtrdi fac0 sumeq1d oveq12d eqeq12d fv0p1e1 subfac1 fac1
      oveq2 oveq1 0p1e1 oveq2d anbi12d fvoveq1 cz cc 0z ax-1cn exp0 ax-mp div1i
      neg1cn fsum1 mp2an oveq2i 1t1e1 eqtr2i wtru nn0uz 1e0p1 cr neg1rr reexpcl
      exp1 mpan faccl nndivred recnd adantl 0nn0 pm3.2i 1pneg1e0 fsump1i simpri
      a1i mptru mul01i wi simpr oveq12 ancoms cmin nn0p1nn subfacp1 nn0cn pncan
      cn sylancl fveq2d eqtrd peano2nn0 nncnd fzfid elfznn0 fsumcl expcl nnne0d
      syl sylancr divcld adddid cuz eleqtrdi fsump1 facp1 mulcomd oveq1d nn0cnd
      mulassd 3eqtrd div12d divcan3d mulcld negsub eqtr3d expp1 3eqtr4d addassd
      id divcan2d add32d eqcomd mulridd adddird imbitrrid jcad nn0ind simpld )
      HUBKHDLZHMLZNHOPZQUCZFUDZUEPZUUMMLZUFPZFUGZRPZSZHQTPZDLZUUTMLZNUUTOPZUUPF
      UGZRPZSZAUDZDLZUVGMLZNUVGOPZUUPFUGZRPZSZUVGQTPZDLZUVNMLZNUVNOPZUUPFUGZRPZ
      SZUHQQNNOPZUUPFUGZRPZSZNQNQOPZUUPFUGZRPZSZUHUAUDZDLZUWIMLZNUWIOPZUUPFUGZR
      PZSZUWIQTPZDLZUWPMLZNUWPOPZUUPFUGZRPZSZUHZUXBUWPQTPZDLZUXDMLZNUXDOPZUUPFU
      GZRPZSZUHUUSUVFUHAUAHUVGNSZUVMUWDUVTUWHUXKUVHQUVLUWCUXKUVHNDLQUVGNDUIABCD
      EGIJUJUKUXKUVIQUVKUWBRUXKUVINMLZQUVGNMUIULUKUXKUVJUWAUUPFUVGNNOUSUMUNUOUX
      KUVONUVSUWGUXKUVOQDLNDUVGUPABCDEGIJUQUKUXKUVPQUVRUWFRUXKUVPQMLZQMUVGUPURU
      KUXKUVQUWEUUPFUXKUVNQNOUXKUVNNQTPQUVGNQTUTVAUKVBUMUNUOVCUVGUWISZUVMUWOUVT
      UXBUXNUVHUWJUVLUWNUVGUWIDUIUXNUVIUWKUVKUWMRUVGUWIMUIUXNUVJUWLUUPFUVGUWINO
      USUMUNUOUXNUVOUWQUVSUXAUVGUWIQDTVDUXNUVPUWRUVRUWTRUVGUWIQMTVDUXNUVQUWSUUP
      FUXNUVNUWPNOUVGUWIQTUTVBUMUNUOVCUVGUWPSZUVMUXBUVTUXJUXOUVHUWQUVLUXAUVGUWP
      DUIUXOUVIUWRUVKUWTRUVGUWPMUIUXOUVJUWSUUPFUVGUWPNOUSUMUNUOUXOUVOUXEUVSUXIU
      VGUWPQDTVDUXOUVPUXFUVRUXHRUVGUWPQMTVDUXOUVQUXGUUPFUXOUVNUXDNOUVGUWPQTUTVB
      UMUNUOVCUVGHSZUVMUUSUVTUVFUXPUVHUUIUVLUURUVGHDUIUXPUVIUUJUVKUUQRUVGHMUIUX
      PUVJUUKUUPFUVGHNOUSUMUNUOUXPUVOUVAUVSUVEUVGHQDTVDUXPUVPUVBUVRUVDRUVGHQMTV
      DUXPUVQUVCUUPFUXPUVNUUTNOUVGHQTUTVBUMUNUOVCUWDUWHUWCQQRPQUWBQQRNVEKQVFKZU
      WBQSZVGVHUUPQFNUUMNSZUUPQQUFPQUXSUUNQUUOQUFUXSUUNUULNUEPZQUUMNUULUEUSUULV
      FKZUXTQSVLUULVIVJUKUXSUUOUXLQUUMNMUIULUKUNQVHVKUKVMVNZVOVPVQUWGQNRPNUWFNQ
      RQUBKZUWFNSZUYCUYDUHVRUUPUULQNFNNQUBVSVTUUMQSZUUPUULQUFPUULUYEUUNUULUUOQU
      FUYEUUNUULQUEPZUULUUMQUULUEUSUYAUYFUULSVLUULWDVJUKUYEUUOUXMQUUMQMUIURUKUN
      UULVLVKUKUUMUBKZUUPVFKZVRUYGUUPUYGUUNUUOUULWAKUYGUUNWAKWBUULUUMWCWEUUMWFW
      GWHZWINUBKZUXRUHVRUYJUXRWJUYBWKWOQUULTPNSVRWLWOWMWPWNVOQVHWQVQWKUWIUBKZUX
      CUXBUXJUXCUXBWRUYKUWOUXBWSWOUXCUXJUYKUWPUWQUWJTPZRPZUWPUXAUWNTPZRPZSUXCUY
      LUYNUWPRUXBUWOUYLUYNSUWQUXAUWJUWNTWTXAVBUYKUXEUYMUXIUYOUYKUXEUWPUWQUWPQXB
      PZDLZTPZRPZUYMUYKUWPXGKUXEUYSSUWIXCZABCDEGUWPIJXDXRUYKUYRUYLUWPRUYKUYQUWJ
      UWQTUYKUYPUWIDUYKUWIVFKUXQUYPUWISUWIXEVHUWIQXFXHXIVBVBXJUYKUXFUWTUULUXDUE
      PZUXFUFPZTPZRPZUWPUWKUXDRPZUWMRPZUULUWPUEPZTPZRPZUXIUYOUYKVUDUXFUWTRPZUXF
      VUBRPZTPUWPVUERPZUWMRPZVUGUXDRPZTPZVUATPZVUIUYKUXFUWTVUBUYKUXFUYKUXDUBKZU
      XFXGKUYKUWPUBKZVUQUWIXKZUWPXKXRZUXDWFXRZXLZUYKUWSUUPFUYKNUWPXMUYKUUMUWSKZ
      UHUYGUYHVVCUYGUYKUUMUWPXNWIUYIXRZXOUYKVUAUXFUYKUYAVUQVUAVFKVLVUTUULUXDXPX
      SZVVBUYKUXFVVAXQZXTYAUYKVUJVUOVUKVUATUYKVUJUXFUWMVUGUWRUFPZTPZRPUXFUWMRPZ
      UXFVVGRPZTPVUOUYKUWTVVHUXFRUYKUUPVVGFNUWIUYKUWIUBNYBLZUYKYSVSYCVVDUUMUWPS
      UUNVUGUUOUWRUFUUMUWPUULUEUSUUMUWPMUIUNYDZVBUYKUXFUWMVVGVVBUYKUWLUUPFUYKNU
      WIXMUYKUUMUWLKZUHUYGUYHVVMUYGUYKUUMUWIXNWIUYIXRXOZUYKVUGUWRUYKUYAVURVUGVF
      KVLVUSUULUWPXPXSZUYKUWRUYKVURUWRXGKVUSUWPWFXRZXLZUYKUWRVVPXQZXTZYAUYKVVIV
      UMVVJVUNTUYKUXFVULUWMRUYKUXFUWRUXDRPZUWPUWKRPZUXDRPVULUYKVURUXFVVTSVUSUWP
      YEXRZUYKUWRVWAUXDRUYKUWRUWKUWPRPZVWAUWIYEZUYKUWKUWPUYKUWKUWIWFXLZUYKUWPUY
      TXLZYFXJYGUYKUWPUWKUXDVWFVWEUYKUXDVUTYHZYIYJYGUYKVVJVUGUXFUWRUFPZRPVUNUYK
      UXFVUGUWRVVBVVOVVQVVRYKUYKVWHUXDVUGRUYKVWHVVTUWRUFPUXDUYKUXFVVTUWRUFVWBYG
      UYKUXDUWRVWGVVQVVRYLXJVBXJUNYJUYKVUAUXFVVEVVBVVFYTUNUYKVUMVUNVUATPZTPUWPV
      UFRPZUWPVUGRPZTPVUPVUIUYKVUMVWJVWIVWKTUYKUWPVUEUWMVWFUYKUWKUXDVWEVWGYMZVV
      NYIUYKVUNVUGUULRPZTPZVUGUWPRPZVWIVWKUYKVUGUXDUULTPZRPVWNVWOUYKVUGUXDUULVV
      OVWGUYAUYKVLWOYAUYKVWPUWPVUGRUYKVWPUXDQXBPZUWPUYKUXDVFKUXQVWPVWQSVWGVHUXD
      QYNXHUYKUWPVFKUXQVWQUWPSVWFVHUWPQXFXHXJVBYOUYKVUAVWMVUNTUYKUYAVURVUAVWMSV
      LVUSUULUWPYPXSVBUYKUWPVUGVWFVVOYFYQUNUYKVUMVUNVUAUYKVULUWMUYKUWPVUEVWFVWL
      YMVVNYMUYKVUGUXDVVOVWGYMVVEYRUYKUWPVUFVUGVWFUYKVUEUWMVWLVVNYMVVOYAYQYJUYK
      UXHVUCUXFRUYKUUPVUBFNUWPUYKUWPUBVVKVUSVSYCUYKUUMUXGKZUHUYGUYHVWRUYGUYKUUM
      UXDXNWIUYIXRUUMUXDSUUNVUAUUOUXFUFUUMUXDUULUEUSUUMUXDMUIUNYDVBUYKUYNVUHUWP
      RUYKUWRUWMRPZVUGTPZUWNTPVWSUWNTPZVUGTPUYNVUHUYKVWSVUGUWNUYKUWRUWMVVQVVNYM
      VVOUYKUWKUWMVWEVVNYMUUAUYKUXAVWTUWNTUYKUXAUWRVVHRPVWSUWRVVGRPZTPVWTUYKUWT
      VVHUWRRVVLVBUYKUWRUWMVVGVVQVVNVVSYAUYKVXBVUGVWSTUYKVUGUWRVVOVVQVVRYTVBYJY
      GUYKVUFVXAVUGTUYKVUFUWRUWKTPZUWMRPVXAUYKVUEVXCUWMRUYKVUEVWCUWKQRPZTPVXCUY
      KUWKUWPQVWEVWFUXQUYKVHWOYAUYKVWCUWRVXDUWKTUYKUWRVWCVWDUUBUYKUWKVWEUUCUNXJ
      YGUYKUWRUWKUWMVVQVWEVVNUUDXJYGYQVBYQUOUUEUUFUUGUUH $.

    $( The subfactorial converges rapidly to ` N ! / _e ` .  This is part of
       Metamath 100 proof #88.  (Contributed by Mario Carneiro,
       23-Jan-2015.) $)
    subfaclim $p |- ( N e. NN ->
      ( abs ` ( ( ( ! ` N ) / _e ) - ( S ` N ) ) ) < ( 1 / N ) ) $=
      ( vk wcel cfv cdiv co c1 caddc cmul cn0 syl cc0 cn cfa cmin cabs cc nnnn0
      ceu faccl nncnd wne ere recni epos divcl mp3an23 subfacf ffvelcdmi nn0cnd
      gt0ne0ii subcld abscld peano2nn peano2nnd nnred nnmulcld nndivred nnrecre
      cuz cneg cv cexp csu cle wbr cmpt eqid neg1cn a1i absnegi abs1 eqtri 1le1
      ax-1cn eqbrtri eftlub wa wceq nnnn0d eluznn0 sylan eftval sumeq2dv fveq2d
      oveq1i cz nnzd 1exp eqtrid oveq1d recnd mullidd eqtrd 3brtr3d cr wb eftcl
      clt mpan cli cdm eftlcvg sylancr isumcl nngt0d lemul2 syl112anc mpbid cfz
      cseq subfacval2 nncn pncan sylancl oveq2d sumeq1d eqtr4d divrec ce oveq2i
      df-e efneg ax-mp adantl 3eqtrd mulcld nnne0d adddird nnre nngt0 jca efval
      3eqtr2i nn0uz mp2an isumsplit fzfid elfznn0 fsumcl adddid subaddd absmuld
      0nn0 mpbird nn0ge0d absidd facp1 mulassd divcan5d divassd 3eqtr3d 3brtr4d
      eqtr2d nnmulcl mpancom ltp1d mulcomd oveq12d breqtrrd lt2mul2div syl22anc
      addassd 1red lelttrd ) GUAKZGUBLZUGMNZGDLZUCNZUDLZGOPNZOPNZUVTUVTQNZMNZOG
      MNZUVNUVRUVNUVPUVQUVNUVOUEKZUVPUEKZUVNUVOUVNGRKZUVOUAKGUFZGUHSZUIZUWEUGUE
      KZUGTUJZUWFUGUKULZUGUKUMUSZUVOUGUNUOSZUVNUVQUVNUWGUVQRKUWHRRGDABCDEFHIUPU
      QSURZUTVAUVNUWAUWBUVNUWAUVNUVTGVBZVCZVDZUVNUVTUVTUWQUWQVEZVFGVGUVNUVOUVTV
      HLZOVIZJVJZVKNUXCUBLMNZJVLZUDLZQNZUVOUWAUVTUBLZUVTQNZMNZQNZUVSUWCVMUVNUXF
      UXJVMVNZUXGUXKVMVNZUVNUXAUXCFRUXBFVJZVKNUXNUBLZMNVOZLZJVLZUDLUXBUDLZUVTVK
      NZUXJQNZUXFUXJVMUVNUXBJFUXPFRUXSUXNVKNUXOMNVOZFRUXTUXHMNOUWAMNUXNVKNQNVOZ
      UVTUXPVPZUYBVPUYCVPUWQUXBUEKZUVNVQVRUXSOVMVNUVNUXSOOVMUXSOUDLOOWCVSVTWAZW
      BWDVRWEUVNUXRUXEUDUVNUXAUXQUXDJUVNUXCUXAKZWFZUXCRKZUXQUXDWGZUVNUVTRKZUYGU
      YIUVNUVTUWQWHZUXCUVTWIWJZUXBFUXPUXCUYDWKZSZWLWMUVNUYAOUXJQNUXJUVNUXTOUXJQ
      UVNUXTOUVTVKNZOUXSOUVTVKUYFWNUVNUVTWOKUYPOWGUVNUVTUWQWPZUVTWQSWRWSUVNUXJU
      VNUXJUVNUWAUXIUWSUVNUXHUVTUVNUYKUXHUAKUYLUVTUHSUWQVEZVFZWTXAXBXCUVNUXFXDK
      UXJXDKUVOXDKTUVOXGVNUXLUXMXEUVNUXEUVNUXDJUXPUVTUXAUXAVPZUYQUYOUYHUYIUXDUE
      KZUYMUYEUYIVUAVQUXBUXCXFZXHZSUVNUYEUYKPUXPUVTXSXIXJZKVQUYLUXBFUXPUVTUYDXK
      XLXMZVAUYSUVNUVOUWIVDZUVNUVOUWIXNUXFUXJUVOXOXPXQUVNUVSUVOUXEQNZUDLUVOUDLZ
      UXFQNUXGUVNUVRVUGUDUVNUVRVUGWGUVQVUGPNZUVPWGUVNVUIUVOTUVTOUCNZXRNZUXDJVLZ
      QNZVUGPNZUVPUVNUVQVUMVUGPUVNUVQUVOTGXRNZUXDJVLZQNZVUMUVNUWGUVQVUQWGUWHABC
      DEJFGHIXTSUVNVULVUPUVOQUVNVUKVUOUXDJUVNVUJGTXRUVNGUEKOUEKZVUJGWGGYAZWCGOY
      BYCYDYEYDYFWSUVNUVPUVOOUGMNZQNZUVOVULUXEPNZQNVUNUVNUWEUVPVVAWGZUWJUWEUWKU
      WLVVCUWMUWNUVOUGYGUOSUVNVUTVVBUVOQUVNVUTRUXDJVLZVVBVUTOOYHLZMNZUXBYHLZVVD
      UGVVEOMYJYIVURVVGVVFWGWCOYKYLUYEVVGVVDWGVQUXBJUUAYLUUBUVNUXDJUXPTUVTUXARU
      UCUYTUYLUYIUYJUVNUYNYMUYIVUAUVNVUCYMPUXPTXSVUDKZUVNUYETRKVVHVQUULUXBFUXPT
      UYDXKUUDVRUUEWRYDUVNUVOVULUXEUWJUVNVUKUXDJUVNTVUJUUFUVNUXCVUKKZWFUYEUYIVU
      AVQVVIUYIUVNUXCVUJUUGYMVUBXLUUHVUEUUIYNYFUVNUVPUVQVUGUWOUWPUVNUVOUXEUWJVU
      EYOUUJUUMWMUVNUVOUXEUWJVUEUUKUVNVUHUVOUXFQUVNUVOVUFUVNUVOUVNUVOUWIWHUUNUU
      OWSYNUVNUVOUWAQNZUVOUWBQNZMNVVJUXIMNUWCUXKUVNVVKUXIVVJMUVNUXIUVOUVTQNZUVT
      QNVVKUVNUXHVVLUVTQUVNUWGUXHVVLWGUWHGUUPSWSUVNUVOUVTUVTUWJUVNUVTUWQUIZVVMU
      UQUVBYDUVNUWAUWBUVOUVNUWAUWRUIZUVNUWBUWTUIZUWJUVNUWBUWTYPUVNUVOUWIYPUURUV
      NUVOUWAUXIUWJVVNUVNUXIUYRUIUVNUXIUYRYPUUSUUTUVAUVNUWAGQNZOUWBQNZXGVNZUWCU
      WDXGVNZUVNVVPVVPOPNZVVQXGUVNVVPUVNVVPUWAUAKUVNVVPUAKUWRUWAGUVCUVDVDUVEUVN
      VVQUWBGUVTQNZOUVTQNZPNZVVTUVNUWBVVOXAUVNGOUVTVUSVURUVNWCVRZVVMYQUVNVWCUVT
      GQNZUVTPNZVVTUVNVWAVWEVWBUVTPUVNGUVTVUSVVMUVFUVNUVTVVMXAUVGUVNVVTVWEOGQNZ
      PNZOPNVWEGPNZOPNVWFUVNVVPVWHOPUVNUVTOGVVMVWDVUSYQWSUVNVWHVWIOPUVNVWGGVWEP
      UVNGVUSXAYDWSUVNVWEGOUVNUVTGVVMVUSYOVUSVWDUVKYNYFYNUVHUVNUWAXDKGXDKZTGXGV
      NZWFOXDKUWBXDKZTUWBXGVNZWFZVVRVVSXEUWSUVNVWJVWKGYRGYSYTUVNUVLUVNUWBUAKZVW
      NUWTVWOVWLVWMUWBYRUWBYSYTSUWAGOUWBUVIUVJXQUVM $.

    $( Another closed form expression for the subfactorial.  The expression
       ` |_ `` ( x + 1 / 2 ) ` is a way of saying "rounded to the nearest
       integer".  (Contributed by Mario Carneiro, 23-Jan-2015.) $)
    subfacval3 $p |- ( N e. NN -> ( S ` N ) =
      ( |_ ` ( ( ( ! ` N ) / _e ) + ( 1 / 2 ) ) ) ) $=
      ( wcel cfv ceu co c1 c2 caddc wbr clt cr cc0 cn cfa cdiv cfl wceq cle cn0
      nnnn0 subfacf ffvelcdmi syl nn0zd zred crp faccl nnred epr sylancl halfre
      rerpdivcl readdcl cmin cabs wa cuz wo elnn1uz2 fac1 eqtrdi oveq1d subfac1
      fveq2 oveq12d rpreccl ax-mp rpre recni subid1i fveq2d rpge0 absid egt2lt3
      mp2an c3 simpli 2re ere 2pos epos ltrecii mpbi eqbrtrdi cc resubcld recnd
      eluz2nn abscld nnrecred subfaclim eluzle nnre nngt0 lerec mpanl12 syl2anc
      a1i wb mpbid ltletrd jaoi sylbi absdifltd simpld ltsubaddd ltled ltadd1dd
      simprd addassd ax-1cn 2halves oveq2i breqtrd cz flbi mpbir2and eqcomd ) G
      UAJZGUBKZLUCMZNOUCMZPMZUDKZGDKZYGYLYMUEZYMYKUFQZYKYMNPMZRQZYGYMYKYGYMYGYM
      YGGUGJZYMUGJGUHZUGUGGDABCDEFHIUIUJUKULZUMZYGYISJZYJSJZYKSJZYGYHSJLUNJZUUB
      YGYHYGYRYHUAJYSGUOUKUPUQYHLUTURZUSYIYJVAURZYGYMYJVBMYIRQZYMYKRQYGUUHYIYMY
      JPMZRQZYGYIYMVBMZVCKZYJRQZUUHUUJVDYGGNUEZGOVEKJZVFUUMGVGUUNUUMUUOUUNUULNL
      UCMZYJRUUNUULUUPVCKZUUPUUNUUKUUPVCUUNUUKUUPTVBMUUPUUNYIUUPYMTVBUUNYHNLUCU
      UNYHNUBKNGNUBVLVHVIVJUUNYMNDKTGNDVLABCDEFHIVKVIVMUUPUUPUUPUNJZUUPSJZUUEUU
      RUQLVNVOZUUPVPVOZVQVRVIVSUUSTUUPUFQZUUQUUPUEUVAUURUVBUUTUUPVTVOUUPWAWCVIO
      LRQZUUPYJRQUVCLWDRQWBWEOLWFWGWHWIWJWKWLUUOUULNGUCMZYJUUOUUKUUOYGUUKWMJGWP
      ZYGUUKYGYIYMUUFUUAWNWOUKWQUUOGUVEWRUUCUUOUSXFUUOYGUULUVDRQUVEABCDEFGHIWSU
      KUUOOGUFQZUVDYJUFQZOGWTUUOYGUVFUVGXGZUVEYGGSJZTGRQZUVHGXAGXBOSJTORQUVIUVJ
      VDUVHWFWHOGXCXDXEUKXHXIXJXKYGYIYMYJUUFUUAUUCYGUSXFZXLXHZXMYGYMYJYIUUAUVKU
      UFXNXHXOYGYKUUIYJPMZYPRYGYIUUIYJUUFYGYMSJUUCUUISJUUAUSYMYJVAURUVKYGUUHUUJ
      UVLXQXPYGUVMYMYJYJPMZPMYPYGYMYJYJYGYMUUAWOYGYJUVKWOZUVOXRUVNNYMPNWMJUVNNU
      EXSNXTVOYAVIYBYGUUDYMYCJYNYOYQVDXGUUGYTYKYMYDXEYEYF $.
  $}

  ${
    $d f m x y A $.  $d m n x y D $.
    derangfmla.d $e |- D = ( x e. Fin |-> ( # ` { f | ( f : x -1-1-onto-> x /\
      A. y e. x ( f ` y ) =/= y ) } ) ) $.
    $( The derangements formula, which expresses the number of derangements of
       a finite nonempty set in terms of the factorial.  The expression
       ` |_ `` ( x + 1 / 2 ) ` is a way of saying "rounded to the nearest
       integer".  This is part of Metamath 100 proof #88.  (Contributed by
       Mario Carneiro, 23-Jan-2015.) $)
    derangfmla $p |- ( ( A e. Fin /\ A =/= (/) ) ->
      ( D ` A ) = ( |_ ` ( ( ( ! ` ( # ` A ) ) / _e ) + ( 1 / 2 ) ) ) ) $=
      ( vn vm cfn wcel c0 wne cfv cn0 c1 cv cfz co cdiv wceq chash cmpt cfa ceu
      wa c2 caddc cfl oveq2 fveq2d cbvmptv derangen2 adantr cn hashnncl biimpar
      subfacval3 syl eqtrd ) CIJZCKLZUEZCDMZCUAMZGNOGPZQRZDMZUBZMZVDUCMUDSROUFS
      RUGRUHMZUTVCVITVAABCDVHEHFGHNVGOHPZQRZDMVEVKTVFVLDVEVKOQUIUJUKZULUMVBVDUN
      JZVIVJTUTVNVACUOUPABDVHEHVDFVMUQURUS $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  The Erd&#337;s-Szekeres theorem
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x y A $.  $d y F $.  $d y O $.  $d x S $.  $d y X $.
    erdszelem1.1 $e |- S = { y e. ~P ( 1 ... A ) | ( ( F |` y )
        Isom < , O ( y , ( F " y ) ) /\ A e. y ) } $.
    $( Lemma for ~ erdsze .  (Contributed by Mario Carneiro, 22-Jan-2015.) $)
    erdszelem1 $p |- ( X e. S <-> ( X C_ ( 1 ... A )
        /\ ( F |` X ) Isom < , O ( X , ( F " X ) ) /\ A e. X ) ) $=
      ( c1 cfz co cpw wcel cima clt cres wiso wa wceq wb syl wss w3a ovex elpw2
      anbi1i cv reseq2 isoeq1 isoeq4 imaeq2 isoeq5 3bitrd anbi12d elrab2 3anass
      eleq2 3bitr4i ) FHBIJZKZLZFDFMZNEDFOZPZBFLZQZQFURUAZVEQFCLVFVCVDUBUTVFVEF
      URHBIUCUDUEAUFZDVGMZNEDVGOZPZBVGLZQVEAFUSCVGFRZVJVCVKVDVLVJVGVHNEVBPZFVHN
      EVBPZVCVLVIVBRVJVMSVGFDUGVGVHNEVBVIUHTVGVHFNEVBUIVLVHVARVNVCSVGFDUJFVHVAN
      EVBUKTULVGFBUPUMGUNVFVCVDUOUQ $.

    $( Lemma for ~ erdsze .  (Contributed by Mario Carneiro, 22-Jan-2015.) $)
    erdszelem2 $p |- ( ( # " S ) e. Fin /\ ( # " S ) C_ NN ) $=
      ( vx chash cima cfn wcel cn wss cres c1 cv clt wiso mp2an cvv wfo cfz cpw
      co fzfi pwfi mpbi wa crab ssrab2 eqsstri ssfi wfun cdm cn0 cpnf csn hashf
      cun ffun ax-mp ssv fdmi sseqtrri fores fofi cfv wral funimass4 erdszelem1
      wf wb w3a c0 wne 3ad2ant3 simp1 sylancr hashnncl syl mpbird sylbi mprgbir
      ne0i pm3.2i ) HCIZJKZWFLMZCJKZCWFHCNZUAZWGOBUBUDZUCZJKZCWMMWIWLJKZWNOBUEZ
      WLUFUGCAPZDWQIQEDWQNRBWQKUHZAWMUIWMFWRAWMUJUKWMCULSHUMZCHUNZMZWKTUOUPUQUS
      ZHVKWSURTXBHUTVAZCTWTCVBTXBHURVCVDZCHVESCWFWJVFSWHGPZHVGLKZGCWSXAWHXFGCVH
      VLXCXDGCLHVISXECKXEWLMZXEDXEIQEDXENRZBXEKZVMZXFABCDEXEFVJXJXFXEVNVOZXIXGX
      KXHXEBWDVPXJXEJKZXFXKVLXJWOXGXLWPXGXHXIVQWLXEULVRXEVSVTWAWBWCWE $.
  $}

  ${
    $d f w x y z B $.  $d f m n s w x y z F $.  $d n s x y I $.  $d f s z K $.
    $d f s w x y z A $.  $d n s x y J $.  $d f s w x y z O $.  $d m s x y R $.
    $d a b m n s w x y z N $.  $d a b f m n s w x y z ph $.  $d m s x y S $.
    $d a b m s w z T $.
    erdsze.n $e |- ( ph -> N e. NN ) $.
    erdsze.f $e |- ( ph -> F : ( 1 ... N ) -1-1-> RR ) $.
    ${
      erdszelem.k $e |- K = ( x e. ( 1 ... N ) |->
        sup ( ( # " { y e. ~P ( 1 ... x ) | ( ( F |` y )
          Isom < , O ( y , ( F " y ) ) /\ x e. y ) } ) , RR , < ) ) $.
      $( Lemma for ~ erdsze .  (Contributed by Mario Carneiro, 22-Jan-2015.) $)
      erdszelem3 $p |- ( A e. ( 1 ... N ) -> ( K ` A ) =
        sup ( ( # " { y e. ~P ( 1 ... A ) | ( ( F |` y )
          Isom < , O ( y , ( F " y ) ) /\ A e. y ) } ) , RR , < ) ) $=
        ( chash cv cima clt wcel c1 cfz co cr cres wiso wa crab csup wceq oveq2
        cpw pweqd eleq1 anbi2d rabeqbidv imaeq2d supeq1d ltso supex fvmpt ) BDL
        CMZEURNOHEURUAUBZBMZURPZUCZCQUTRSZUHZUDZNZTOUELUSDURPZUCZCQDRSZUHZUDZNZ
        TOUEQGRSFUTDUFZTVFVLOVMVEVKLVMVBVHCVDVJVMVCVIUTDQRUGUIVMVAVGUSUTDURUJUK
        ULUMUNKTVLOUOUPUQ $.

      erdszelem.o $e |- O Or RR $.
      $( Lemma for ~ erdsze .  (Contributed by Mario Carneiro, 22-Jan-2015.) $)
      erdszelem4 $p |- ( ( ph /\ A e. ( 1 ... N ) ) -> { A } e.
        { y e. ~P ( 1 ... A ) | ( ( F |` y )
          Isom < , O ( y , ( F " y ) ) /\ A e. y ) } ) $=
        ( c1 wcel wa wss clt adantl wbr cr cfz co csn cima cres wiso cv crab cn
        cpw elfznn elfz1end sylib snssd cfv wi wb elsni breqan12d cuz fzssuz cz
        wral uzssz zssre sstri simpr adantr sselid pm2.21d sylbid ralrimivva wf
        ltnrd wf1 f1f syl wor ltso soss mp2 soisores mpanl12 syl2anc snidg eqid
        mpbird erdszelem1 syl3anbrc ) ADMGUAUBZNZOZDUCZMDUAUBZPWMEWMUDQHEWMUEUF
        ZDWMNZWMCUGZEWQUDQHEWQUEUFDWQNOCWNUJUHZNWLDWNWLDUINZDWNNWKWSADGUKRDULUM
        UNWLWOBUGZWQQSZWTEUOWQEUOHSZUPZCWMVCBWMVCZWLXCBCWMWMWLWTWMNZWQWMNZOZOZX
        ADDQSZXBXGXAXIUQWLXEXFWTDWQDQWTDURWQDURUSRXHXIXBXHDXHWJTDWJMUTUOZTMGVAX
        JVBTMVDVEVFVFZWLWKXGAWKVGZVHVIVNVJVKVLWLWJTEVMZWMWJPZWOXDUQZAXMWKAWJTEV
        OXMJWJTEVPVQVHWLDWJXLUNWJQVRZTHVRXMXNOXOWJTPTQVRXPXKVSWJTQVTWALBCWMWJTQ
        HEWBWCWDWGWKWPADWJWERCDWREHWMWRWFWHWI $.

      $( Lemma for ~ erdsze .  (Contributed by Mario Carneiro, 22-Jan-2015.) $)
      erdszelem5 $p |- ( ( ph /\ A e. ( 1 ... N ) ) -> ( K ` A ) e. ( # "
        { y e. ~P ( 1 ... A ) | ( ( F |` y )
          Isom < , O ( y , ( F " y ) ) /\ A e. y ) } ) ) $=
        ( c1 cfz co wcel chash clt cr c0 wa cfv cv cima cres wiso cpw crab csup
        wceq erdszelem3 adantl wne cdm cin csn cvv snex cn0 cpnf cun hashf fdmi
        eleqtrri erdszelem4 inelcm sylancr imadisj necon3bii sylibr cfn cn eqid
        wss erdszelem2 simpli simpri nnssre sstri wor ltso fisupcl mpan mp3an13
        w3a syl eqeltrd ) ADMGNOPZUAZDFUBZQCUCZEWKUDRHEWKUEUFDWKPUACMDNOUGUHZUD
        ZSRUIZWMWHWJWNUJAABCDEFGHIJKUKULWIWMTUMZWNWMPZWIQUNZWLUOZTUMZWOWIDUPZWQ
        PWTWLPWSWTUQWQDURUQUSUTUPVAQVBVCVDABCDEFGHIJKLVEWTWQWLVFVGWMTWRTQWLVHVI
        VJWMVKPZWOWMSVNZWPXAWMVLVNZCDWLEHWLVMVOZVPWMVLSXAXCXDVQVRVSSRVTXAWOXBWE
        WPWASWMRWBWCWDWFWG $.

      $( Lemma for ~ erdsze .  (Contributed by Mario Carneiro, 22-Jan-2015.) $)
      erdszelem6 $p |- ( ph -> K : ( 1 ... N ) --> NN ) $=
        ( c1 cfz co cv cima clt wcel wa cn vz chash cres wiso cpw crab csup cvv
        cr ltso supex a1i cmpt wceq cfv cfn erdszelem2 simpri erdszelem5 sselid
        wss eqid fmpt2d ) ABUALFMNZUBCOZDVEPQGDVEUCUDZBOZVERSCLVGMNUEUFPZUIQUGZ
        TEUHVIUHRAVGVDRSUIVHQUJUKULEBVDVIUMUNAJULAUAOZVDRSUBVFVJVERSCLVJMNUEUFZ
        PZTVJEUOVLUPRVLTVACVJVKDGVKVBUQURABCVJDEFGHIJKUSUTVC $.

      erdszelem.a $e |- ( ph -> A e. ( 1 ... N ) ) $.
      ${
        erdszelem7.r $e |- ( ph -> R e. NN ) $.
        erdszelem7.m $e |- ( ph -> -. ( K ` A ) e. ( 1 ... ( R - 1 ) ) ) $.
        $( Lemma for ~ erdsze .  (Contributed by Mario Carneiro,
           22-Jan-2015.) $)
        erdszelem7 $p |- ( ph -> E. s e. ~P ( 1 ... N )
          ( R <_ ( # ` s ) /\ ( F |` s ) Isom < , O ( s , ( F " s ) ) ) ) $=
          ( chash wcel c1 cv cfv wceq cima clt cres wiso wa cfz co cpw crab cle
          wrex wbr wfun cvv cn0 cpnf csn wf hashf ffun ax-mp erdszelem5 fvelima
          cun mpdan sylancr wss w3a wi eqid erdszelem1 simprl1 cuz elfzuz3 3syl
          fzss2 adantr sstrd velpw sylibr wn cmin cz wb cn erdszelem6 ffvelcdmd
          nnuz eleqtrdi nnz peano2zm elfz5 syl2anc nnltlem1 bitr4d mtbid cr cfn
          erdszelem2 simpri nnssre sselid lenltd mpbird simprr breqtrrd simprl2
          nnred sstri jca32 expr sylan2b expimpd reximdv2 mpd ) AJUAZRUBZDGUBZU
          CZJCUAZFYCUDUEIFYCUFUGDYCSUHCTDUIUJZUKULZUNZEXTUMUOZXSFXSUDUEIFXSUFUG
          ZUHZJTHUIUJZUKZUNARUPZYARYEUDZSZYFUQURUSUTVGZRVAYLVBUQYORVCVDADYJSZYN
          OABCDFGHIKLMNVEVHZJYAYERVFVIAYBYIJYEYKAXSYESZYBXSYKSZYIUHZYRAXSYDVJZY
          HDXSSZVKZYBYTVLCDYEFIXSYEVMZVNAUUCYBYTAUUCYBUHZUHZYSYGYHUUFXSYJVJYSUU
          FXSYDYJUUAYHUUBYBAVOAYDYJVJZUUEAYPHDVPUBSUUGODTHVQDTHVSVRVTWAJYJWBWCU
          UFEYAXTUMAEYAUMUOZUUEAUUHYAEUEUOZWDAYATETWEUJZUIUJSZUUIQAUUKYAUUJUMUO
          ZUUIAYATVPUBZSUUJWFSZUUKUULWGAYAWHUUMAYJWHDGABCFGHIKLMNWIOWJZWKWLAEWH
          SZEWFSUUNPEWMEWNVRYATUUJWOWPAYAWHSUUPUUIUULWGUUOPYAEWQWPWRWSAEYAAEPXK
          AYMWTYAYMWHWTYMXASYMWHVJCDYEFIUUDXBXCXDXLYQXEXFXGVTAUUCYBXHXIUUAYHUUB
          YBAXJXMXNXOXPXQXR $.
      $}

      erdszelem.b $e |- ( ph -> B e. ( 1 ... N ) ) $.
      erdszelem.l $e |- ( ph -> A < B ) $.
      $( Lemma for ~ erdsze .  (Contributed by Mario Carneiro, 22-Jan-2015.) $)
      erdszelem8 $p |- ( ph ->
        ( ( K ` A ) = ( K ` B ) -> -. ( F ` A ) O ( F ` B ) ) ) $=
        ( wbr wcel c1 cr vf vw vz cfv cv chash wceq cima clt cres wa cfz co cpw
        wiso crab wrex wne wi wfun cvv cn0 cpnf csn hashf ffun ax-mp erdszelem5
        cun wf mpdan fvelima sylancr wss w3a eqid erdszelem1 fzfid simplr1 ssfi
        cfn syl2anc hashcl syl nn0red cle csup c0 wral erdszelem2 simpri nnssre
        caddc cn sstri a1i cz elfzelzd elfznn nnred ltled eluz2 syl3anbrc fzss2
        cuz ad2antrr sstrd elfz1end sylib snssd simplr2 wb wf1 f1f elfzuz3 3syl
        unssd wor fzssuz soisores mpanl12 mpbid sselda elfzle2 ad3antrrr lenltd
        adantr fvres adantl ffvelcdmd mp2and elsni syl5ibrcom ralrimiv sylanbrc
        wn imbi2d ralunb ralrimiva mpbird uzssz zssre ltso soss r19.21bi sselid
        simplr3 simpr isorel breqan12d bitrd syl12anc mtbid simplr mpan syl3anc
        mp2 a1d fveq2d breq2d elfzelz zred syldan pm2.21d breq1d imbi1d ralbidv
        sotr2 ssun2 snssg mpbiri cdm vex snex unex fdmi eleqtrri funfvima mp2an
        ne0d simpli fimaxre2 sylancl ltnled ssneldd hashunsng eqeltrrd syl31anc
        nsyl suprub erdszelem3 breqtrrd erdszelem6 nnnn0d nn0ltp1le ltned neeq1
        ex syl5ibcom sylan2b rexlimdva mpd necon2bd ) ADFUDZEFUDZIQZDGUDZEGUDZA
        UAUEZUFUDZUXGUGZUACUEZFUXLUHUIIFUXLUJUOZDUXLRUKCSDULUMZUNUPZUQZUXFUXGUX
        HURZUSZAUFUTZUXGUFUXOUHRZUXPVAVBVCVDVIZUFVJUXSVEVAUYAUFVFVGZADSHULUMZRZ
        UXTNABCDFGHIJKLMVHVKUAUXGUXOUFVLVMAUXKUXRUAUXOUXIUXORAUXIUXNVNZUXIFUXIU
        HZUIIFUXIUJZUOZDUXIRZVOZUXKUXRUSCDUXOFIUXIUXOVPVQAUYJUKZUXFUXJUXHURZUSU
        XKUXRUYKUXFUYLUYKUXFUKZUXJUXHUYMUXJUYMUXIWARZUXJVBRZUYMUXNWARUYEUYNUYMS
        DVRUYEUYHUYIAUXFVSZUXNUXIVTWBZUXIWCWDZWEUYMUXJUXHUIQZUXJSWMUMZUXHWFQZUY
        MUYTUFUXMEUXLRUKCSEULUMZUNUPZUHZTUIWGZUXHWFUYMVUDTVNZVUDWHURUBUEZUCUEZW
        FQUBVUDWIUCTUQZUYTVUDRUYTVUEWFQVUFUYMVUDWNTVUDWARZVUDWNVNZCEVUCFIVUCVPZ
        WJZWKWLWOWPZUYMVUDUXIEVDZVIZUFUDZUYMVUPVUCRZVUQVUDRZUYMVUPVUBVNVUPFVUPU
        HUIIFVUPUJUOZEVUPRZVURUYMUXIVUOVUBUYMUXIUXNVUBUYPAUXNVUBVNZUYJUXFAEDXEU
        DZRZVVBADWQREWQRDEWFQVVDADSHNWRAESHOWRADEADAUYDDWNRZNDHWSZWDWTZAEAEUYCR
        ZEWNRZOEHWSWDZWTZPXADEXBXCDSEXDWDXFXGUYMEVUBAEVUBRZUYJUXFAVVIVVLVVJEXHX
        IXFZXJXQZUYMVUTVUHVUGUIQZVUHFUDZVUGFUDZIQZUSZUBVUPWIZUCVUPWIZUYMVVTUCUX
        IWIVVTUCVUOWIVWAUYMVVTUCUXIUYMVUHUXIRZUKZVVSUBUXIWIZVVSUBVUOWIVVTUYMVWD
        UCUXIUYMUYHVWDUCUXIWIZUYEUYHUYIAUXFXKZUYMUYCTFVJZUXIUYCVNZUYHVWEXLZAVWG
        UYJUXFAUYCTFXMVWGKUYCTFXNWDXFZUYMUXIUXNUYCUYPAUXNUYCVNZUYJUXFAUYDHVVCRV
        WKNDSHXODSHXDXPXFXGZUYCUIXRZTIXRZVWGVWHUKVWIUYCTVNTUIXRVWMUYCSXEUDZTSHX
        SVWOWQTSUUAUUBWOWOZUUCUYCTUIUUDUUQZMUCUBUXIUYCTUIIFXTYAWBYBUUEVWCVVSUBV
        UOVWCVVSVUGVUORZVVOVVPUXEIQZUSVWCVWSVVOVWCUXDVVPIQZYPZUXFVWSVWCDVUHUIQZ
        VWTVWCVUHDWFQZVXBYPVWCVUHUXNRVXCUYMUXIUXNVUHUYPYCVUHSDYDWDVWCVUHDVWCUYC
        TVUHVWPUYMUXIUYCVUHVWLYCZUUFVWCDVWCUYDVVEAUYDUYJUXFVWBNYEZVVFWDWTYFYBVW
        CUYHUYIVWBVXBVWTXLUYMUYHVWBVWFYGUYMUYIVWBUYEUYHUYIAUXFUUGYGUYMVWBUUHUYH
        UYIVWBUKZUKVXBDUYGUDZVUHUYGUDZIQZVWTUXIUYFDVUHUIIUYGUUIVXFVXIVWTXLUYHUY
        IVWBVXGUXDVXHVVPIDUXIFYHVUHUXIFYHUUJYIUUKUULUUMUYKUXFVWBUUNVWCVVPTRZUXD
        TRZUXETRZVXAUXFUKVWSUSZVWCUYCTVUHFUYMVWGVWBVWJYGZVXDYJVWCUYCTDFVXNVXEYJ
        VWCUYCTEFVXNUYMVVHVWBAVVHUYJUXFOXFZYGYJVWNVXJVXKVXLVOVXMMTVVPUXDUXEIUVH
        UUOUUPYKUURVWRVVRVWSVVOVWRVVQUXEVVPIVWRVUGEFVUGEYLUUSUUTYQYMYNVVSUBUXIV
        UOYRYOYSUYMVVTUCVUOUYMVVTVUHVUORZEVUGUIQZVVRUSZUBVUPWIUYMVXRUBVUPUYMVUG
        VUPRZUKVXQVVRUYMVXSVUGVUBRZVXQYPZUYMVUPVUBVUGVVNYCUYMVXTUKZVUGEWFQZVYAV
        XTVYCUYMVUGSEYDYIVYBVUGEVXTVUGTRUYMVXTVUGVUGSEUVAUVBYIAETRUYJUXFVXTVVKY
        EYFYBUVCUVDYSVXPVVSVXRUBVUPVXPVVOVXQVVRVXPVUHEVUGUIVUHEYLUVEUVFUVGYMYNV
        VTUCUXIVUOYRYOUYMVWGVUPUYCVNZVUTVWAXLZVWJUYMUXIVUOUYCVWLUYMEUYCVXOXJXQV
        WMVWNVWGVYDUKVYEVWQMUCUBVUPUYCTUIIFXTYAWBYTUYMVVAVUOVUPVNZVUOUXIUVIUYMV
        VLVVAVYFXLVVMEVUPVUBUVJWDUVKCEVUCFIVUPVULVQXCUXSVUPUFUVLZRVURVUSUSUYBVU
        PVAVYGUXIVUOUAUVMEUVNUVOVAUYAUFVEUVPUVQVUCVUPUFUVRUVSWDZUVTUYMVUFVUJVUI
        VUNVUJVUKVUMUWAUCUBVUDUWBUWCUYMVUQUYTVUDUYMUYNEUXIRYPZVUQUYTUGZUYQUYMUX
        IUXNEUYPAEUXNRZYPUYJUXFAEDWFQZVYKADEUIQVYLYPPADEVVGVVKUWDYBESDYDUWIXFUW
        EUYMVVHUYNVYIUKVYJUSVXOUXIEUYCUWFWDYKVYHUWGUCUBVUDUYTUWJUWHAUXHVUEUGZUY
        JUXFAVVHVYMOABCEFGHIJKLUWKWDXFUWLUYMUYOUXHVBRUYSVUAXLUYRUYMUXHAUXHWNRUY
        JUXFAUYCWNEGABCFGHIJKLMUWMOYJXFUWNUXJUXHUWOWBYTUWPUWRUXKUYLUXQUXFUXJUXG
        UXHUWQYQUWSUWTUXAUXBUXC $.
    $}

    ${
      erdszelem.i $e |- I = ( x e. ( 1 ... N ) |->
        sup ( ( # " { y e. ~P ( 1 ... x ) | ( ( F |` y )
          Isom < , < ( y , ( F " y ) ) /\ x e. y ) } ) , RR , < ) ) $.
      erdszelem.j $e |- J = ( x e. ( 1 ... N ) |->
        sup ( ( # " { y e. ~P ( 1 ... x ) | ( ( F |` y )
          Isom < , `' < ( y , ( F " y ) ) /\ x e. y ) } ) , RR , < ) ) $.
      erdszelem.t $e |- T = ( n e. ( 1 ... N ) |->
        <. ( I ` n ) , ( J ` n ) >. ) $.
      $( Lemma for ~ erdsze .  (Contributed by Mario Carneiro, 22-Jan-2015.) $)
      erdszelem9 $p |- ( ph -> T : ( 1 ... N ) -1-1-> ( NN X. NN ) ) $=
        ( cn cfv wceq wcel wa cr vz vw va vb c1 cfz co cxp wf cv wi wf1 cop clt
        wral ltso erdszelem6 ffvelcdmda ccnv gtso opelxpi fmptd fveq2 eqeqan12d
        syl2anc eqeq12 imbi12d eqcom bitrdi wss elfzelz ssriv a1i biidd cle wbr
        zred w3a simpr1 opeq12d opex syl simpr2 eqeq12d fvex opth wne wn sselid
        fvmpt simpr3 leltned wo adantr f1fveq syl12anc bitr4di necon3bid bitr4d
        wb biimpa f1f ad2antrr ffvelcdmd lttri2d mpbid simpr erdszelem8 anim12d
        ioran brcnv notbii anbi2i bitr4i imbitrrdi ex sylbird necon4ad biimtrid
        mt2d sylbid imbitrdi wlogle ralrimivva dff13 sylanbrc ) AUEIUFUGZOOUHZD
        UIUAUJZDPZUBUJZDPZQZYIYKQZUKZUBYGUOUAYGUOYGYHDULAEYGEUJZGPZYPHPZUMZYHDA
        YPYGRSYQORYRORYSYHRAYGOYPGABCFGIUNJKLUPUQURAYGOYPHABCFHIUNUSZJKMUTUQURY
        QYROOVAVENVBAYOUAUBYGYGAUCUJZDPZUDUJZDPZQZUUAUUCQZUKYOYOUAUBUCUDYGUUAYI
        QZUUCYKQZSUUEYMUUFYNUUGUUHUUBYJUUDYLUUAYIDVCUUCYKDVCVDUUAYIUUCYKVFVGUUA
        YKQZUUCYIQZSZUUEYMUUFYNUUKUUEYLYJQYMUUIUUJUUBYLUUDYJUUAYKDVCUUCYIDVCVDY
        LYJVHVIUUKUUFYKYIQZYNUUAYKUUCYIVFYKYIVHZVIVGYGTVJAUAYGTYIYGRZYIYIUEIVKV
        QZVLZVMAUUNYKYGRZSSYOVNAUUNUUQYIYKVOVPZVRZSZYMUULYNUUTYMYIGPZYIHPZUMZYK
        GPZYKHPZUMZQZUULUUTYJUVCYLUVFUUTUUNYJUVCQAUUNUUQUURVSZEYIYSUVCYGDYPYIQY
        QUVAYRUVBYPYIGVCYPYIHVCVTNUVAUVBWAWJWBUUTUUQYLUVFQAUUNUUQUURWCZEYKYSUVF
        YGDYPYKQYQUVDYRUVEYPYKGVCYPYKHVCVTNUVDUVEWAWJWBWDUVGUVAUVDQZUVBUVEQZSZU
        UTUULUVAUVBUVDUVEYIGWEYIHWEWFUUTUVLYKYIUUTYKYIWGZYIYKUNVPZUVLWHZUUTYIYK
        UUTUUNYITRUVHUUOWBUUTYGTYKUUPUVIWIAUUNUUQUURWKWLZUUTUVNUVOUUTUVNSZUVLYI
        FPZYKFPZUNVPZUVSUVRUNVPZWMZUVQUVRUVSWGZUWBUUTUVNUWCUUTUVNUVMUWCUVPUUTUV
        RUVSYKYIUUTUVRUVSQZYNUULUUTYGTFULZUUNUUQUWDYNWTAUWEUUSKWNUVHUVIYGTYIYKF
        WOWPUUMWQWRWSXAUVQUVRUVSUVQYGTYIFAYGTFUIZUUSUVNAUWEUWFKYGTFXBWBXCZUUTUU
        NUVNUVHWNZXDUVQYGTYKFUWGUUTUUQUVNUVIWNZXDXEXFUVQUVLUVTWHZUVRUVSYTVPZWHZ
        SZUWBWHZUVQUVJUWJUVKUWLUVQBCYIYKFGIUNAIORUUSUVNJXCZAUWEUUSUVNKXCZLUPUWH
        UWIUUTUVNXGZXHUVQBCYIYKFHIYTUWOUWPMUTUWHUWIUWQXHXIUWNUWJUWAWHZSUWMUVTUW
        AXJUWLUWRUWJUWKUWAUVRUVSUNYIFWEYKFWEXKXLXMXNXOXTXPXQXRXSYAUUMYBYCYDUAUB
        YGYHDYEYF $.

      erdszelem.r $e |- ( ph -> R e. NN ) $.
      erdszelem.s $e |- ( ph -> S e. NN ) $.
      erdszelem.m $e |- ( ph -> ( ( R - 1 ) x. ( S - 1 ) ) < N ) $.
      $( Lemma for ~ erdsze .  (Contributed by Mario Carneiro, 22-Jan-2015.) $)
      erdszelem10 $p |- ( ph -> E. m e. ( 1 ... N )
        ( -. ( I ` m ) e. ( 1 ... ( R - 1 ) ) \/
          -. ( J ` m ) e. ( 1 ... ( S - 1 ) ) ) ) $=
        ( vs cv cfv c1 cmin co cfz cxp wcel wn wrex wo crn wss csdm wbr cdom wi
        cfn fzfi xpfi mp2an ssdomg ax-mp domnsym syl cen chash cmul wceq hashxp
        clt cn cn0 nnm1nn0 hashfz1 oveq12d eqtrid nnnn0d 3brtr4d fzfid hashsdom
        3syl wb sylancr mpbid wf1 wf1o erdszelem9 f1f1orn ovex sdomentr syl2anc
        f1oen nsyl3 wex nss df-rex bitr4i sylib wfn f1fn eleq1 notbid rexrn cop
        wa fveq2 opeq12d opex fvmpt adantl eleq1d opelxp bitrdi ianor rexbidva
        ) AGUBZFUCZUDDUDUEUFZUGUFZUDEUDUEUFZUGUFZUHZUIZUJZGUDLUGUFZUKZXRJUCZYAU
        IZUJXRKUCZYCUIZUJULZGYGUKAUAUBZYDUIZUJZUAFUMZUKZYHAYQYDUNZUJZYRYSYDYQUO
        UPZAYSYQYDUQUPZUUAUJYDUSUIZYSUUBURYAUSUIZYCUSUIZUUCUDXTUTZUDYBUTZYAYCVA
        VBZYQYDUSVCVDYQYDVEVFAYDYGUOUPZYGYQVGUPZUUAAYDVHUCZYGVHUCZVLUPZUUIAXTYB
        VIUFZLUUKUULVLTAUUKYAVHUCZYCVHUCZVIUFZUUNUUDUUEUUKUUQVJUUFUUGYAYCVKVBAU
        UOXTUUPYBVIADVMUIXTVNUIUUOXTVJRDVOXTVPWCAEVMUIYBVNUIUUPYBVJSEVOYBVPWCVQ
        VRALVNUIUULLVJALMVSLVPVFVTAUUCYGUSUIUUMUUIWDUUHAUDLWAYDYGWBWEWFAYGVMVMU
        HZFWGZYGYQFWHUUJABCFHIJKLMNOPQWIZYGUURFWJYGYQFUDLUGWKWNWCYDYGYQWLWMWOYT
        YNYQUIYPXGUAWPYRUAYQYDWQYPUAYQWRWSWTAUUSFYGXAYRYHWDUUTYGUURFXBYPYFUAGYG
        FYNXSVJYOYEYNXSYDXCXDXEWCWFAYFYMGYGAXRYGUIZXGZYFYJYLXGZUJYMUVBYEUVCUVBY
        EYIYKXFZYDUIUVCUVBXSUVDYDUVAXSUVDVJAHXRHUBZJUCZUVEKUCZXFUVDYGFUVEXRVJUV
        FYIUVGYKUVEXRJXHUVEXRKXHXIQYIYKXJXKXLXMYIYKYAYCXNXOXDYJYLXPXOXQWF $.

      $( Lemma for ~ erdsze .  (Contributed by Mario Carneiro, 22-Jan-2015.) $)
      erdszelem11 $p |- ( ph -> E. s e. ~P ( 1 ... N )
      ( ( R <_ ( # ` s ) /\ ( F |` s ) Isom < , < ( s , ( F " s ) ) ) \/
        ( S <_ ( # ` s ) /\ ( F |` s ) Isom < , `' < ( s , ( F " s ) ) ) ) ) $=
        ( vm cv chash cfv cle wbr cima clt cres wiso wa c1 cfz co cpw wrex ccnv
        wo cmin wcel wn erdszelem10 cn adantr wf1 ltso simprl simprr erdszelem7
        cr expr gtso orim12d rexlimdva mpd r19.43 sylibr ) ADLUBZUCUDZUEUFVRHVR
        UGZUHUHHVRUIZUJUKZLULKUMUNZUOZUPZEVSUEUFVRVTUHUHUQZWAUJUKZLWDUPZURZWBWG
        URLWDUPAUAUBZIUDULDULUSUNUMUNUTVAZWJJUDULEULUSUNUMUNUTVAZURZUAWCUPWIABC
        DEFUAGHIJKMNOPQRSTVBAWMWIUAWCAWJWCUTZUKWKWEWLWHAWNWKWEAWNWKUKZUKBCWJDHI
        KUHLAKVCUTZWOMVDAWCVJHVEZWONVDOVFAWNWKVGADVCUTWORVDAWNWKVHVIVKAWNWLWHAW
        NWLUKZUKBCWJEHJKWFLAWPWRMVDAWQWRNVDPVLAWNWLVGAEVCUTWRSVDAWNWLVHVIVKVMVN
        VOWBWGLWDVPVQ $.
    $}

    erdsze.r $e |- ( ph -> R e. NN ) $.
    erdsze.s $e |- ( ph -> S e. NN ) $.
    erdsze.l $e |- ( ph -> ( ( R - 1 ) x. ( S - 1 ) ) < N ) $.
    $( The Erd&#337;s-Szekeres theorem.  For any injective sequence ` F ` on
       the reals of length at least ` ( R - 1 ) x. ( S - 1 ) + 1 ` , there is
       either a subsequence of length at least ` R ` on which ` F ` is
       increasing (i.e. a ` < , < ` order isomorphism) or a subsequence of
       length at least ` S ` on which ` F ` is decreasing (i.e. a ` < , ``' < `
       order isomorphism, recalling that ` ``' < ` is the "greater than"
       relation).  This is part of Metamath 100 proof #73.  (Contributed by
       Mario Carneiro, 22-Jan-2015.) $)
    erdsze $p |- ( ph -> E. s e. ~P ( 1 ... N )
    ( ( R <_ ( # ` s ) /\ ( F |` s ) Isom < , < ( s , ( F " s ) ) ) \/
      ( S <_ ( # ` s ) /\ ( F |` s ) Isom < , `' < ( s , ( F " s ) ) ) ) ) $=
      ( vx vy vz vw chash cima clt wiso wa vn c1 cfz co cv cres wel cpw crab cr
      csup cmpt cfv ccnv cop weq wceq wb reseq2 isoeq1 syl isoeq4 imaeq2 isoeq5
      3bitrd elequ2 anbi12d cbvrabv oveq2 pweqd elequ1 anbi2d rabeqbidv imaeq2d
      eqtrid supeq1d cbvmptv eqid erdszelem11 ) ALMBCUAUBEUCUDZUAUEZNVTPOUEZDWB
      QZRRDWBUFZSZNOUGZTZOUBNUEZUCUDZUHZUIZQZUJRUKZULZUMWANVTPWBWCRRUNZWDSZWFTZ
      OWJUIZQZUJRUKZULZUMUOULZUADWNXAEFGHNLVTWMPMUEZDXCQZRRDXCUFZSZLMUGZTZMUBLU
      EZUCUDZUHZUIZQZUJRUKNLUPZUJWLXMRXNWKXLPXNWKXFNMUGZTZMWJUIXLWGXPOMWJOMUPZW
      EXFWFXOXQWEWBWCRRXESZXCWCRRXESZXFXQWDXEUQZWEXRURWBXCDUSZWBWCRRXEWDUTVAWBW
      CXCRRXEVBXQWCXDUQZXSXFURWBXCDVCZXCWCXDRRXEVDVAVEOMNVFZVGVHXNXPXHMWJXKXNWI
      XJWHXIUBUCVIVJZXNXOXGXFNLMVKZVLVMVOVNVPVQNLVTWTPXCXDRWOXESZXGTZMXKUIZQZUJ
      RUKXNUJWSYJRXNWRYIPXNWRYGXOTZMWJUIYIWQYKOMWJXQWPYGWFXOXQWPWBWCRWOXESZXCWC
      RWOXESZYGXQXTWPYLURYAWBWCRWOXEWDUTVAWBWCXCRWOXEVBXQYBYMYGURYCXCWCXDRWOXEV
      DVAVEYDVGVHXNYKYHMWJXKYEXNXOXGYGYFVLVMVOVNVPVQXBVRIJKVS $.
  $}

  ${
    $d f s t A $.  $d f s t F $.  $d s t x y G $.  $d f s t R $.  $d f s t S $.
    $d f s t x y N $.  $d f s t x y ph $.
    erdsze2.r $e |- ( ph -> R e. NN ) $.
    erdsze2.s $e |- ( ph -> S e. NN ) $.
    erdsze2.f $e |- ( ph -> F : A -1-1-> RR ) $.
    erdsze2.a $e |- ( ph -> A C_ RR ) $.
    ${
      erdsze2lem.n $e |- N = ( ( R - 1 ) x. ( S - 1 ) ) $.
      erdsze2lem.l $e |- ( ph -> N < ( # ` A ) ) $.
      $( Lemma for ~ erdsze2 .  (Contributed by Mario Carneiro,
         22-Jan-2015.) $)
      erdsze2lem1 $p |- ( ph -> E. f ( f : ( 1 ... ( N + 1 ) ) -1-1-> A /\
        f Isom < , < ( ( 1 ... ( N + 1 ) ) , ran f ) ) ) $=
        ( c1 co clt wcel syl wb cr vs caddc cfz cv cen wbr wss wf1 crn wiso wex
        wa cdom cfn chash cfv cle wceq cn0 cmin cmul nnm1nn0 nn0mulcld eqeltrid
        cn peano2nn0 hashfz1 adantr hashcl nn0ltp1le syl2an mpbid eqbrtrd fzfid
        3syl simpr hashdom syl2anc isinffi cvv reex ssexg sylancl brdomg mpbird
        wn pm2.61dan domeng wor simprr ltso soss mpisyl simprl enfi fz1iso wf1o
        sstrd isof1o adantl hashen eqtr3d oveq2d f1oeq2d f1of1 simplrr f1ss wfo
        f1ofo forn isoeq5 4syl isoeq4 jca ex eximdv mpd exlimddv ) ANGNUBOZUCOZ
        UAUDZUEUFZYABUGZULZXTBEUDZUHZXTYEUIZPPYEUJZULZEUKZUAAXTBUMUFZYDUAUKZABU
        NQZYKAYMULZXTUOUPZBUOUPZUQUFZYKYNYOXSYPUQAYOXSURZYMAGUSQZXSUSQYRAGCNUTO
        ZDNUTOZVAOUSLAYTUUAACVEQYTUSQHCVBRADVEQUUAUSQIDVBRVCVDZGVFXSVGVOZVHYNGY
        PPUFZXSYPUQUFZAUUDYMMVHAYSYPUSQUUDUUESYMUUBBVIGYPVJVKVLVMYNXTUNQZYMYQYK
        SYNNXSVNAYMVPXTBUNVQVRVLAYMWFZULZYKYFEUKZUUHUUGUUFUUIAUUGVPUUHNXSVNBXTE
        VSVRUUHBVTQZYKUUISAUUJUUGABTUGZTVTQUUJKWABTVTWBWCZVHXTBVTEWDRWEWGAUUJYK
        YLSUULUAXTBVTWHRVLAYDULZNYAUOUPZUCOZYAPPYEUJZEUKZYJUUMYAPWIZYAUNQZUUQUU
        MYATUGTPWIUURUUMYABTAYBYCWJAUUKYDKVHWRWKYATPWLWMUUMUUFUUSUUMNXSVNZUUMYB
        UUFUUSSAYBYCWNZXTYAWORVLZYAPEWPVRUUMUUPYIEUUMUUPYIUUMUUPULZYFYHUVCXTYAY
        EUHZYCYFUVCXTYAYEWQZUVDUVCUUOYAYEWQZUVEUUPUVFUUMUUOYAPPYEWSWTZUVCUUOXTY
        AYEUVCUUNXSNUCUUMUUNXSURUUPUUMYOUUNXSUUMYOUUNURZYBUVAUUMUUFUUSUVHYBSUUT
        UVBXTYAXAVRWEAYRYDUUCVHXBVHXCZXDVLXTYAYEXERAYBYCUUPXFXTYABYEXGVRUVCUUOY
        GPPYEUJZYHUVCUVJUUPUUMUUPVPUVCUVFUUOYAYEXHYGYAURUVJUUPSUVGUUOYAYEXIUUOY
        AYEXJUUOYGYAPPYEXKXLWEUVCUUOXTURUVJYHSUVIUUOYGXTPPYEXMRVLXNXOXPXQXR $.

      erdsze2lem.g $e |- ( ph -> G : ( 1 ... ( N + 1 ) ) -1-1-> A ) $.
      erdsze2lem.i $e |- ( ph ->
        G Isom < , < ( ( 1 ... ( N + 1 ) ) , ran G ) ) $.
      $( Lemma for ~ erdsze2 .  (Contributed by Mario Carneiro,
         22-Jan-2015.) $)
      erdsze2lem2 $p |- ( ph -> E. s e. ~P A
      ( ( R <_ ( # ` s ) /\ ( F |` s ) Isom < , < ( s , ( F " s ) ) ) \/
        ( S <_ ( # ` s ) /\ ( F |` s ) Isom < , `' < ( s , ( F " s ) ) ) ) ) $=
        ( clt wiso wcel syl vt vx vy cv chash cfv cle ccom cima cres wa ccnv wo
        wbr c1 caddc co cfz cpw wrex cn0 cn cmin cmul nnm1nn0 nn0mulcld nn0p1nn
        eqeltrid cr wf1 f1co syl2anc nn0red ltp1d eqbrtrrid erdsze wss wi velpw
        crn imassrn wf f1f frnd sstrid cvv wb reex sylancl elpw2g mpbird adantr
        ssexg wceq cen vex f1imaen sylan fzfid simpr ssfi hashen breq2d biimprd
        cfn enfii wral ad2antrr simprl sseldd simprr isorel syl12anc ralrimivva
        biimpd wor elfznn nnred ssriv ltso soss mpisyl soisores syl22anc isocnv
        a1i isotr resco coeq1i coass isoeq1 isoeq5 bitrdi sylibd anim12d isoeq4
        ex ax-mp 3bitrd anbi12d cid wf1o f1ores f1ococnv2 coeq2d coires1 eqtrdi
        eqtri eqtrid imaco orim12d fveq2 reseq2 imaeq2 orbi12d rspcev rexlimdva
        syl6an sylan2b mpd ) ACUAUDZUEUFZUGUNZUVAEFUHZUVAUIZQQUVDUVAUJZRZUKZDUV
        BUGUNZUVAUVEQQULZUVFRZUKZUMZUAUOGUOUPUQZURUQZUSZUTCHUDZUEUFZUGUNZUVQEUV
        QUIZQQEUVQUJZRZUKZDUVRUGUNZUVQUVTQUVJUWARZUKZUMZHBUSZUTZACDUVDUVNUAAGVA
        SUVNVBSAGCUOVCUQZDUOVCUQZVDUQZVAMAUWJUWKACVBSUWJVASICVETADVBSUWKVASJDVE
        TVFVHZGVGTABVIEVJUVOBFVJZUVOVIUVDVJKOUVOBVIEFVKVLIJAUWLGUVNQMAGAGUWMVMV
        NVOVPAUVMUWIUAUVPUVAUVPSAUVAUVOVQZUVMUWIVRUAUVOVSAUWOUKZFUVAUIZUWHSZUVM
        CUWQUEUFZUGUNZUWQEUWQUIZQQEUWQUJZRZUKZDUWSUGUNZUWQUXAQUVJUXBRZUKZUMZUWI
        AUWRUWOAUWRUWQBVQZAUWQFVTZBFUVAWAAUVOBFAUWNUVOBFWBZOUVOBFWCTZWDWEABWFSZ
        UWRUXIWGABVIVQZVIWFSUXMLWHBVIWFWMWIUWQBWFWJTWKWLUWPUVHUXDUVLUXGUWPUVCUW
        TUVGUXCUWPUWTUVCUWPUWSUVBCUGUWPUWSUVBWNZUWQUVAWOUNZAUWNUWOUXPOUVOBUVAFU
        AWPWQWRZUWPUWQXESZUVAXESZUXOUXPWGUWPUXSUXPUXRUWPUVOXESUWOUXSUWPUOUVNWSA
        UWOWTZUVOUVAXAVLZUXQUWQUVAXFVLUYAUWQUVAXBVLWKZXCXDUWPUVGUWQUVEQQUVFFUVA
        UJZULZUHZRZUXCUWPUWQUVAQQUYDRZUVGUYFVRUWPUVAUWQQQUYCRZUYGUWPUYHUBUDZUCU
        DZQUNZUYIFUFUYJFUFQUNZVRZUCUVAXGUBUVAXGZUWPUYMUBUCUVAUVAUWPUYIUVASZUYJU
        VASZUKZUKZUYKUYLUYRUVOUXJQQFRZUYIUVOSUYJUVOSUYKUYLWGAUYSUWOUYQPXHUYRUVA
        UVOUYIUWPUWOUYQUXTWLZUWPUYOUYPXIXJUYRUVAUVOUYJUYTUWPUYOUYPXKXJUVOUXJUYI
        UYJQQFXLXMXOXNUWPUVOQXPZBQXPZUXKUWOUYHUYNWGUWPUVOVIVQZVIQXPZVUAVUCUWPUA
        UVOVIUVAUVOSUVAUVAUVNXQXRXSYFXTUVOVIQYAYBUWPUXNVUDVUBAUXNUWOLWLXTBVIQYA
        YBAUXKUWOUXLWLUXTUBUCUVAUVOBQQFYCYDWKUVAUWQQQUYCYETZUYGUVGUYFUWQUVAUVEQ
        QQUVFUYDYGYQTUWPUYFUWQUVEQQUXBRZUXCUWPUYEUXBWNZUYFVUFWGUWPUYEEUYCUYDUHZ
        UHZUXBUYEEUYCUHZUYDUHVUIUVFVUJUYDEFUVAYHYIEUYCUYDYJUUHUWPVUIEUUAUWQUJZU
        HUXBUWPVUHVUKEUWPUVAUWQUYCUUBZVUHVUKWNAUWNUWOVULOUVOBUVAFUUCWRUVAUWQUYC
        UUDTUUEEUWQUUFUUGUUIZUWQUVEQQUXBUYEYKTUVEUXAWNZVUFUXCWGEFUVAUUJZUWQUVEU
        XAQQUXBYLYRYMYNYOUWPUVIUXEUVKUXFUWPUXEUVIUWPUWSUVBDUGUYBXCXDUWPUVKUWQUV
        EQUVJUYERZUXFUWPUYGUVKVUPVRVUEUYGUVKVUPUWQUVAUVEQQUVJUVFUYDYGYQTUWPVUPU
        WQUVEQUVJUXBRZUXFUWPVUGVUPVUQWGVUMUWQUVEQUVJUXBUYEYKTVUNVUQUXFWGVUOUWQU
        VEUXAQUVJUXBYLYRYMYNYOUUKUWGUXHHUWQUWHUVQUWQWNZUWCUXDUWFUXGVURUVSUWTUWB
        UXCVURUVRUWSCUGUVQUWQUEUULZXCVURUWBUVQUVTQQUXBRZUWQUVTQQUXBRZUXCVURUWAU
        XBWNZUWBVUTWGUVQUWQEUUMZUVQUVTQQUXBUWAYKTUVQUVTUWQQQUXBYPVURUVTUXAWNZVV
        AUXCWGUVQUWQEUUNZUWQUVTUXAQQUXBYLTYSYTVURUWDUXEUWEUXFVURUVRUWSDUGVUSXCV
        URUWEUVQUVTQUVJUXBRZUWQUVTQUVJUXBRZUXFVURVVBUWEVVFWGVVCUVQUVTQUVJUXBUWA
        YKTUVQUVTUWQQUVJUXBYPVURVVDVVGUXFWGVVEUWQUVTUXAQUVJUXBYLTYSYTUUOUUPUURU
        USUUQUUT $.
    $}

    erdsze2.l $e |- ( ph -> ( ( R - 1 ) x. ( S - 1 ) ) < ( # ` A ) ) $.
    $( Generalize the statement of the Erd&#337;s-Szekeres theorem ~ erdsze to
       "sequences" indexed by an arbitrary subset of ` RR ` , which can be
       infinite.  This is part of Metamath 100 proof #73.  (Contributed by
       Mario Carneiro, 22-Jan-2015.) $)
    erdsze2 $p |- ( ph -> E. s e. ~P A
      ( ( R <_ ( # ` s ) /\ ( F |` s ) Isom < , < ( s , ( F " s ) ) ) \/
        ( S <_ ( # ` s ) /\ ( F |` s ) Isom < , `' < ( s , ( F " s ) ) ) ) ) $=
      ( vf c1 cmin co clt wiso wa wbr adantr caddc cfz cv wf1 crn chash cfv cle
      cmul cima cres ccnv wo cpw wrex eqid erdsze2lem1 cn wcel cr simprl simprr
      wss erdsze2lem2 exlimddv ) AMCMNODMNOUIOZMUAOUBOZBLUCZUDZVGVHUEPPVHQZRZCF
      UCZUFUGZUHSVLEVLUJZPPEVLUKZQRDVMUHSVLVNPPULVOQRUMFBUNUOLABCDLEVFGHIJVFUPZ
      KUQAVKRBCDEVHVFFACURUSVKGTADURUSVKHTABUTEUDVKITABUTVCVKJTVPAVFBUFUGPSVKKT
      AVIVJVAAVIVJVBVDVE $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Euler's partition theorem
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $(
  @{
    eulerpartlemm.f @e |- F = ( x e. NN0 , y e. { z e. NN | -. 2 || z } |->
      ( ( 2 ^ x ) x. y ) ) @.
    @( Lemma for ~ eulerpart .  The function ` F ` that decomposes a number
       into its "odd" and "even" parts, which is to say the largest power of
       two and largest odd divisor of a number, is a bijection from
       pairs of a positive integer and an odd number to positive integers. @)
    eulerpartlemm @p |- F : ( NN0 X. { z e. NN | -. 2 || z } ) -1-1-onto->
      NN ) @=
      ( cn0 cn cmap co wcel ccnv cima cfn cv cfv cmul csu wceq wa wf nn0ex nnex
      w3a elmap anbi1i cnveq eleq1d fveq1 oveq1d sumeq2sdv eqeq1d elrab2 3anass
      imaeq1d anbi12d 3bitr4i ) AGHIJZKZALZHMZNKZHDOZAPZVCQJZDRZESZTZTHGAUAZVHT
      ABKVIVBVGUDUSVIVHGHAUBUCUEUFCOZLZHMZNKZHVCVJPZVCQJZDRZESZTVHCAURBVJASZVMV
      BVQVGVRVLVANVRVKUTHVJAUGUOUHVRVPVFEVRHVOVEDVRVNVDVCQVCVJAUIUJUKULUPFUMVIV
      BVGUNUQ @.
      @( [26-Jan-2015] @)
  @}

  @{
    eulerpart.p @e |- P = { f e. ( NN0 ^m NN ) | ( ( `' f " NN ) e. Fin /\
      sum_ k e. NN ( ( f ` k ) x. k ) = N ) } @.
    @( Lemma for ~ eulerpart . @)
    eulerpartleme @p |- ( A e. P <-> ( A : NN --> NN0 /\ ( `' A " NN ) e. Fin
      /\ sum_ k e. NN ( ( A ` k ) x. k ) = N ) ) @=
      ( cn0 cn cmap co wcel ccnv cima cfn cv cfv cmul csu wceq wa wf nn0ex nnex
      w3a elmap anbi1i cnveq eleq1d fveq1 oveq1d sumeq2sdv eqeq1d elrab2 3anass
      imaeq1d anbi12d 3bitr4i ) AGHIJZKZALZHMZNKZHDOZAPZVCQJZDRZESZTZTHGAUAZVHT
      ABKVIVBVGUDUSVIVHGHAUBUCUEUFCOZLZHMZNKZHVCVJPZVCQJZDRZESZTVHCAURBVJASZVMV
      BVQVGVRVLVANVRVKUTHVJAUGUOUHVRVPVFEVRHVOVEDVRVNVDVCQVCVJAUIUJUKULUPFUMVIV
      BVGUNUQ @.
      @( [26-Jan-2015] @)

    @( Lemma for ~ eulerpart .  The set of all partitions of ` N ` is
       finite. @)
    eulerpartlemb @p |- P e. Fin @=
      ( vx cn c1 co wcel cc0 wa wceq adantl cn0 cle wbr syl wi adantr vg vy cfz
      cv csn cif cixp cfn wss wtru fzfid fzfi snfi ifcli a1i wn eldifn iffalse
      cdif eqimss 3syl ixpfi2 mptru ccnv cima cfv cmul csu w3a eulerpartleme
      wfn wf wral ffn 3ad2ant1 cr simp1 ffvelcdm sylan nn0re idiALT remulc
      syl2anc cdm cnvimass fdm sseqtrid cc sselda adantlr syldan nnnn0 nn0mulcl
      nn0cn simpl nnre cvv nn0supp suppssrOLD oveq1d eldifi nncn mul02 eqtrd
      cuz eqimssi sumss
      nnuz nn0sscn caddc nn0addcl simpr 0nn0 fsumcllem eqeltrrd eleq1 syl5ibcom
      3impia nn0ge0 nnge1 lemulge11 syl22anc fveq2 oveq12d simprr fsumge1 eldif
      id expr ralrimiva eqeq1d rspccva sylan2br fsumge0 breqtrd eleqtrdi elfz5
      wb eleqtrrd syld adantrr eqbrtrd pm2.61d 3adantl3 simpl3 letrd nn0uz nn0z
      cz mpbird iftrue lemulge12 syl21anc letr syl3anc syl5 sylibrd con3d elnn0
      mpan2d sylib ord imp fvex elsn sylibr pm2.61dan vex elixp sylanbrc sylbi
      wo ssriv ssfi mp2an ) FGFUDZHDUCIZJZKDUCIZKUEZUFZUGZUHJZAUWBUIAUHJUWCUJFG
      UWAUVQKUJHDUKUWAUHJUJUVPGJZLUVRUVSUVTUHKDULKUMUNUOUJUVPGUVQUSJZLUVRUPZUWA
      UVTMZUWAUVTUIUWEUWFUJUVPGUVQUQNUVRUVSUVTURZUWAUVTUTVAVBVCUAAUWBUAUDZAJGOU
      WIVLZUWIVDZGVEZUHJZGCUDZUWIVFZUWNVGIZCVHZDMZVIZUWIUWBJZUWIABCDEVJUWSUWIGV
      KZUVPUWIVFZUWAJZFGVMUWTUWJUWMUXAUWRGOUWIVNVOUWSUXCFGUWSUWDLZUVRUXCUXDUVRL
      UXBUVSUWAUXDUXBUVSJZUVRUXDUXEUXBDPQZUXDUXBUXBUVPVGIZDUXDUXBOJZUXBVPJZUWSU
      WJUWDUXHUWJUWMUWRVQGOUVPUWIVRVSZUXBVTRZUXDUXIUVPVPJZUXGVPJZUXDUXISUXKWAUX
      DUXLSUWDUXLUWSUVPWPNZWAZUXBUVPWBWCZUXDDOJZDVPJZUWSUXQUWDUWJUWMUWRUXQUWJUW
      MLZUWQOJUWRUXQUXSUWLUWPCVHZUWQOUXSUWLGUWPCHUXSUWIWDZUWLGUWIGWEUWJUYAGMUWM
      GOUWIWFTWGZUXSUWNUWLJZLZUWPOJZUWPWHJUYDUWOOJZUWNOJZUYEUXSUYCUWNGJZUYFUXSU
      WLGUWNUYBWIZUWJUYHUYFUWMGOUWNUWIVRWJWKUYDUYHUYGUYIUWNWLRUWOUWNWMWCZUWPWNR
      UXSUWNGUWLUSZJZLZUWPKUWNVGIZKUYMUWOKUWNVGUXSGOUWIUWLUWNKUWJUWMWOUXSUWKWQU
      VTUSVEZUWLMZUYOUWLUIUWJUYPUWMUWIGWRTUYOUWLUTRWSWTUYMUYHUWNWHJUYNKMUYLUYHU
      XSUWNGUWLXANUWNXBUWNXCVAXDZGHXEVFZUIUXSGUYRXHXFUOXGZUXSFUBUWLUWPOCOWHUIUX
      SXIUOUVPOJZUBUDZOJLUVPVUAXJIOJUXSUVPVUAXKNUWJUWMXLZUYJKOJUXSXMUOXNXOUWQDO
      XPXQXRTZDVTRZUXDUXIUXLKUXBPQZHUVPPQZUXBUXGPQUXKUXNUXDUXHVUEUXDUXHSUXJWAUX
      BXSRUWDVUFUWSUVPXTNUXBUVPYAYBUXDUXGUWQDPUWJUWMUWDUXGUWQPQUWRUXSUWDLZUXGUX
      TUWQPVUGUVPUWLJZUXGUXTPQZUXSUWDVUHVUIUXSUWDVUHLZLUWLUWPUXGCUVPUXSUWMVUJVU
      BTUXSUYCUWPVPJZVUJUYDUYEVUKUYJUWPVTZRWJUXSUYCKUWPPQZVUJUYDUYEVUMUYJUWPXSZ
      RWJUWNUVPMZUWOUXBUWNUVPVGUWNUVPUWIYCVUOYHYDZUXSUWDVUHYEYFYIUXSUWDVUHUPZVU
      IUXSUWDVUQLZLUXGKUXTPVURUXSUVPUYKJZUXGKMZUVPGUWLYGUXSUWPKMZCUYKVMVUSVUTUX
      SVVACUYKUYQYJVVAVUTCUVPUYKVUOUWPUXGKVUPYKYLVSYMUXSUWDKUXTPQVUQVUGUWLUWPCU
      XSUWMUWDVUBTVUGUYCLZUYEVUKUXSUYCUYEUWDUYJWJZVULRVVBUYEVUMVVCVUNRYNUUAUUBY
      IUUCUXSUXTUWQMUWDUYSTYOUUDUWJUWMUWRUWDUUEYOZUUFUXDUXBKXEVFZJDUUIJZUXEUXFY
      RUXDUXBOVVEUXJUUGYPUXDUXQVVFVUCDUUHRZUXBKDYQWCUUJTUVRUWAUVSMUXDUVRUVSUVTU
      UKNYSUXDUWFLZUXBUVTUWAVVHUXBKMZUXBUVTJUXDUWFVVIUXDUWFUXBGJZUPVVIUXDVVJUVR
      UXDVVJUVPDPQZUVRVVJHUXBPQZUXDVVKUXBXTUXDVVLUVPUXGPQZVVKUXDUXLUXIKUVPPQZVV
      LVVMSUXNUXKUXDUYTVVNUWDUYTUWSUVPWLNUVPXSRUXLUXILVVNVVLVVMUVPUXBUULYIUUMUX
      DVVMUXGDPQZVVKVVDUXDUXLUXMUXRVVMVVOLVVKSUXOUXDUXMSUXPWAUXDUXRSVUDWAUVPUXG
      DUUNUUOUUTYTUUPUXDUVPUYRJVVFUVRVVKYRUXDUVPGUYRUWSUWDXLXHYPVVGUVPHDYQWCUUQ
      UURUXDVVJVVIUXDUXHVVJVVIUVLUXJUXBUUSUVAUVBYTUVCUXBKUVPUWIUVDUVEUVFUWFUWGU
      XDUWHNYSUVGYJFGUWAUWIUAUVHUVIUVJUVKUVMUWBAUVNUVO @.
      @( [26-Jan-2015] @)

    eulerpart.o @e |- O = { g e. P | A. n e. ( `' g " NN ) -. 2 || n } @.
    eulerpart.d @e |- D = { g e. P | A. n e. NN ( g ` n ) <_ 1 } @.
    @{
      eulerpart.f @e |- F = ( x e. ( ~P NN0 i^i Fin ) |->
        sum_ y e. x ( 2 ^ y ) ) @.
      @( Lemma for ~ eulerpart . @)
      eulerpartlemi @p |- ( A e. P -> { t e. NN |
      E. n e. ( `' F ` ( A ` t ) ) ( ( 2 ^ n ) x. t ) = M } C_ ( 1 ... M ) ) @=
        ( wcel cn0 c2 cv cexp co cmul wceq cfv ccnv wrex c1 cfz wi cn wral crab
        wss wa cle wbr cr cc0 nnre ad2antlr 2nn cpw cfn cin inss1 eulerpartleme
        wf cima csu simp1bi ffvelcdm wf1o ackbijnn f1ocnv f1of mp2b ffvelcdmi
        syl
        sylan sselid elpwi sselda nnexpcl sylancr simplr nnnn0 nn0ge0 lemulge12
        3syl nnge1 syl22anc cuz cz wb eleqtrdi nnmulcl syl2anc nnz elfz5 mpbird
        nnuz oveq2 eleq2d syl5ibcom rexlimdva ralrimiva rabss sylibr ) DFSZUAJU
        BZUCUDZCUBZUEUDZLUFZJXODUGZKUHZUGZUIZXOUJLUKUDZSZULZCUMUNYACUMUOYBUPXLY
        DCUMXLXOUMSZUQZXQYCJXTYFXMXTSZUQZXOUJXPUKUDZSZXQYCYHYJXOXPURUSZYHXOUTSZ
        XNUTSZVAXOURUSZUJXNURUSZYKYEYLXLYGXOVBVCYHXNUMSZYMYHUAUMSXMTSYPVDYFXTTX
        MYFXTTVEZSXTTUPYFYQVFVGZYQXTYQVFVHYFXRTSZXTYRSXLUMTDVJZYEYSXLYTDUHUMVKV
        FSUMIUBZDUGUUAUEUDIVLMUFDFGIMOVIVMUMTXODVNWBTYRXRXSYRTKVOTYRXSVOTYRXSVJ
        ABKRVPYRTKVQTYRXSVRVSVTWAWCXTTWDWAWEUAXMWFWGZXNVBWAYHYEXOTSYNXLYEYGWHZX
        OWIXOWJWLYHYPYOUUBXNWMWAXOXNWKWNYHXOUJWOUGZSXPWPSZYJYKWQYHXOUMUUDUUCXDW
        RYHXPUMSZUUEYHYPYEUUFUUBUUCXNXOWSWTXPXAWAXOUJXPXBWTXCXQYIYBXOXPLUJUKXEX
        FXGXHXIYACUMYBXJXK @.
        @( [26-Jan-2015] @)

      eulerpart.g @e |- G = ( o e. P |-> ( m e. NN |-> ( # `
     { t e. NN | E. n e. ( `' F ` ( o ` t ) ) ( ( 2 ^ n ) x. t ) = m } ) ) ) @.
      @( Lemma for ~ eulerpart . @)
      eulerpartlemf @p |- ( A e. P -> ( G ` A ) = ( m e. NN |-> ( # `
     { t e. NN | E. n e. ( `' F ` ( A ` t ) ) ( ( 2 ^ n ) x. t ) = m } ) ) ) @=
        ( cn c2 cv cexp co cmul wceq cfv ccnv wrex crab chash cmpt fveq1 fveq2d
        rexeqdv rabbidv mpteq2dv nnex mptex fvmpt ) LDJUBUCKUDUEUFCUDZUGUFJUDUH
        ZKVCLUDZUIZMUJZUIZUKZCUBULZUMUIZUNJUBVDKVCDUIZVGUIZUKZCUBULZUMUIZUNFNVE
        DUHZJUBVKVPVQVJVOUMVQVIVNCUBVQVDKVHVMVQVFVLVGVCVEDUOUPUQURUPUSUAJUBVPUT
        VAVB @.
        @( [26-Jan-2015] @)

      @( Lemma for ~ eulerpart . @)
      eulerpartlema @p |- G : P --> P @=
        ? @.

      @( Lemma for ~ eulerpart . @)
      eulerpartlemh @p |- ( G |` O ) : O --> D @=
        ? @.

      @( Lemma for ~ eulerpart . @)
      eulerpartlemc @p |- ( G |` O ) : O -1-1-> D @=
        ? @.

      @( Lemma for ~ eulerpart . @)
      eulerpartlemg @p |- ( G |` O ) : O -1-1-onto-> D @=
        ? @.

      eulerpart.h @e |- H = ( d e. P |-> ( m e. NN |-> if ( 2 || m , 0 ,
    sum_ n e. NN0 ( ( d ` ( ( 2 ^ n ) x. m ) ) x. ( ( 2 ^ n ) x. m ) ) ) ) ) @.
      @( Lemma for ~ eulerpart . @)
      eulerpartlemj @p |- H : P --> O @=
        ? @.

      @( Lemma for ~ eulerpart . @)
      eulerpartlemk @p |- ( H |` D ) : D -1-1-> O @=
        ? @.

      @( Lemma for ~ eulerpart . @)
      eulerpartleml @p |- ( H |` D ) : D -1-1-onto-> O @=
        ? @.

    @}

    @( Euler's theorem on partitions, also known as a special case of
       Glaisher's theorem. Let ` P ` be the set of all partitions of ` N ` ,
       represented as multisets of positive integers, which is to say functions
       from ` NN ` to ` NN0 ` where the value of the function represents the
       number of repetitions of an individual element, and the sum of all the
       elements with repetition equals ` N ` . Then the set ` O ` of all
       partitions that only consist of odd numbers and the set ` D ` of all
       partitions which have no repeated elements have the same cardinality. @)
    eulerpart @p |- ( N e. NN0 -> ( # ` O ) = ( # ` D ) ) @=
      ? @.
  @}
  $)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  The Kuratowski closure-complement theorem
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    kur14lem1.a $e |- A C_ X $.
    kur14lem1.c $e |- ( X \ A ) e. T $.
    kur14lem1.k $e |- ( K ` A ) e. T $.
    $( Lemma for ~ kur14 .  (Contributed by Mario Carneiro, 17-Feb-2015.) $)
    kur14lem1 $p |- ( N = A ->
      ( N C_ X /\ { ( X \ N ) , ( K ` N ) } C_ T ) ) $=
      ( wceq wss cdif cfv cpr sseq1 mpbiri difeq2 fveq2 preq12d wcel prssi jca
      mp2an eqsstrdi ) DAIZDEJZEDKZDCLZMZBJUDUEAEJFDAENOUDUHEAKZACLZMZBUDUFUIUG
      UJDAEPDACQRUIBSUJBSUKBJGHUIUJBTUBUCUA $.
  $}

  ${
    $d s x A $.  $d s x K $.  $d s x y T $.  $d s x y X $.
    kur14lem.j $e |- J e. Top $.
    kur14lem.x $e |- X = U. J $.
    kur14lem.k $e |- K = ( cls ` J ) $.
    kur14lem.i $e |- I = ( int ` J ) $.
    kur14lem.a $e |- A C_ X $.
    $( Lemma for ~ kur14 .  Write interior in terms of closure and complement:
       ` i A = c k c A ` where ` c ` is complement and ` k ` is closure.
       (Contributed by Mario Carneiro, 11-Feb-2015.) $)
    kur14lem2 $p |- ( I ` A ) = ( X \ ( K ` ( X \ A ) ) ) $=
      ( cnt cfv cdif ccl ctop wcel wss wceq ntrval2 fveq1i difeq2i 3eqtr4i
      mp2an ) ACKLZLZEEAMZCNLZLZMZABLEUFDLZMCOPAEQUEUIRFJACEGSUCABUDITUJUHEUFDU
      GHTUAUB $.

    $( Lemma for ~ kur14 .  A closure is a subset of the base set.
       (Contributed by Mario Carneiro, 11-Feb-2015.) $)
    kur14lem3 $p |- ( K ` A ) C_ X $=
      ( cfv ccl fveq1i ctop wcel wss clsss3 mp2an eqsstri ) ADKACLKZKZEADTHMCNO
      AEPUAEPFJACEGQRS $.

    $( Lemma for ~ kur14 .  Complementation is an involution on the set of
       subsets of a topology.  (Contributed by Mario Carneiro, 11-Feb-2015.) $)
    kur14lem4 $p |- ( X \ ( X \ A ) ) = A $=
      ( wss cdif wceq dfss4 mpbi ) AEKEEALLAMJAENO $.

    $( Lemma for ~ kur14 .  Closure is an idempotent operation in the set of
       subsets of a topology.  (Contributed by Mario Carneiro, 11-Feb-2015.) $)
    kur14lem5 $p |- ( K ` ( K ` A ) ) = ( K ` A ) $=
      ( ccl cfv ctop wcel wss wceq clsidm mp2an fveq1i fveq12i 3eqtr4i ) ACKLZL
      ZUBLZUCADLZDLUECMNAEOUDUCPFJACEGQRUEUCDUBHADUBHSZTUFUA $.

    kur14lem.b $e |- B = ( X \ ( K ` A ) ) $.
    $( Lemma for ~ kur14 .  If ` k ` is the complementation operator and ` k `
       is the closure operator, this expresses the identity
       ` k c k A = k c k c k c k A ` for any subset ` A ` of the topological
       space.  This is the key result that lets us cut down long enough
       sequences of ` c k c k ... ` that arise when applying closure and
       complement repeatedly to ` A ` , and explains why we end up with a
       number as large as ` 1 4 ` , yet no larger.  (Contributed by Mario
       Carneiro, 11-Feb-2015.) $)
    kur14lem6 $p |- ( K ` ( I ` ( K ` B ) ) ) = ( K ` B ) $=
      ( cfv wss cdif eqsstri fveq1i clsss mp3an 3sstr4i ccl ctop wcel kur14lem3
      difss cnt ntrss2 mp2an kur14lem5 sseqtri kur14lem2 fveq2i difeq2i 3eqtr2i
      eqtr3i sscon ax-mp eqssi ) BEMZCMZEMZUSVAUSEMZUSUTDUAMZMZUSVCMZVAVBDUBUCZ
      USFNZUTUSNVDVENGBCDEFGHIJBFAEMZOZFLFVHUEPZUDZUTUSDUFMZMZUSUSCVLJQVFVGVMUS
      NGVKUSDFHUGUHPUSUTDFHRSUTEVCIQZUSEVCIQTBCDEFGHIJVJUIUJBVCMZVDUSVAVFUTFNBU
      TNVOVDNGUTFFUSOZEMZOZFUSCDEFGHIJVKUKZFVQUEPVIVRBUTVQVHNVIVRNVPVCMZVHVCMZV
      QVHVFVHFNZVPVHNVTWANGACDEFGHIJKUDZVPVHVLMZVHVPFVIEMZOVHCMWDUSWEFBVIELULUM
      VHCDEFGHIJWCUKVHCVLJQUNVFWBWDVHNGWCVHDFHUGUHPVHVPDFHRSVPEVCIQVHEMVHWAACDE
      FGHIJKUIVHEVCIQUOTVQVHFUPUQLVSTUTBDFHRSBEVCIQVNTUR $.

    kur14lem.c $e |- C = ( K ` ( X \ A ) ) $.
    kur14lem.d $e |- D = ( I ` ( K ` A ) ) $.
    kur14lem.t $e |- T = ( ( ( { A , ( X \ A ) , ( K ` A ) } u.
      { B , C , ( I ` A ) } ) u. { ( K ` B ) , D , ( K ` ( I ` A ) ) } ) u.
      ( { ( I ` C ) , ( K ` D ) , ( I ` ( K ` B ) ) } u.
      { ( K ` ( I ` C ) ) , ( I ` ( K ` ( I ` A ) ) ) } ) ) $.
    $( Lemma for ~ kur14 : main proof.  The set ` T ` here contains all the
       distinct combinations of ` k ` and ` c ` that can arise, and we prove
       here that applying ` k ` or ` c ` to any element of ` T ` yields another
       element of ` T ` .  In operator shorthand, we have
       ` T = { A , c A , k A `
       ` , c k A , k c A , c k c A , k c k A , c k c k A , k c k c A , `
       ` c k c k c A , k c k c k A , c k c k c k A , k c k c k c A , `
       ` c k c k c k c A } ` .  From the identities ` c c A = A ` and
       ` k k A = k A ` , we can reduce any operator combination containing two
       adjacent identical operators, which is why the list only contains
       alternating sequences.  The reason the sequences don't keep going after
       a certain point is due to the identity ` k c k A = k c k c k c k A ` ,
       proved in ~ kur14lem6 .  (Contributed by Mario Carneiro,
       11-Feb-2015.) $)
    kur14lem7 $p |- ( N e. T ->
      ( N C_ X /\ { ( X \ N ) , ( K ` N ) } C_ T ) ) $=
      ( cdif wss cfv cpr wa ctp cun wcel wo elun w3o eltpi ssun1 sseqtrri sstri
      wceq ctop topopn ax-mp elexi difss ssexi tpid2 sselii kur14lem1 kur14lem4
      fvex tpid3 tpid1 eqeltri ssun2 kur14lem3 eqsstri eqeltrri kur14lem5 3jaoi
      syl difeq2i eqtri kur14lem2 eqtr4i fveq2i 3eqtr4i eqtr3i jaoi sylbi prid1
      kur14lem6 elpri prid2 eleq2s ) IJUAJITIHUBUCEUAUDZIAJATZAHUBZUEZBCAFUBZUE
      ZUFZBHUBZDWOHUBZUEZUFZCFUBZDHUBZWRFUBZUEZXBHUBZWSFUBZUCZUFZUFZEIXJUGIXAUG
      ZIXIUGZUHWKIXAXIUIXKWKXLXKIWQUGZIWTUGZUHWKIWQWTUIXMWKXNXMIWNUGZIWPUGZUHWK
      IWNWPUIXOWKXPXOIAUOZIWLUOZIWMUOZUJWKIAWLWMUKXQWKXRXSAEHIJOWNEWLWNWQEWNWPU
      LWQXAEWQWTULXAXJEXAXIULSUMZUNZUNZAWLWMWLJJGGUPUGJGUGKGJLUQURUSZJAUTZVAVBV
      CWNEWMYBAWLWMAHVFVGVCZVDWLEHIJYDJWLTAEAFGHJKLMNOVEWNEAYBAWLWMAJYCOVAVHVCV
      ICWLHUBZEQWPECWPWQEWPWNVJYAUNZBCWOCJYCCYFJQWLFGHJKLMNYDVKVLZVAVBVCZVMVDWM
      EHIJAFGHJKLMNOVKZBJWMTZEPWPEBYGBCWOBJYCBYKJPJWMUTVLZVAVHVCVMWMHUBWMEAFGHJ
      KLMNOVNYEVIVDVOVPXPIBUOZICUOZIWOUOZUJWKIBCWOUKYMWKYNYOBEHIJYLJBTZWMEYPJYK
      TWMBYKJPVQWMFGHJKLMNYJVEVRYEVIWTEWRWTXAEWTWQVJXTUNZWRDWSBHVFVHVCZVDCEHIJY
      HJCTZWOEYSJYFTZWOCYFJQVQAFGHJKLMNOVSZVTZWPEWOYGBCWOAFVFVGVCVICHUBZCEYFHUB
      YFUUCCWLFGHJKLMNYDVNCYFHQWAQWBYIVIVDWOEHIJWOYTJUUAJYFUTVLZJWOTZCEJYSTUUEC
      YSWOJUUBVQCFGHJKLMNYHVEWCYIVIWTEWSYQWRDWSWOHVFVGVCZVDVOVPWDWEXNIWRUOZIDUO
      ZIWSUOZUJWKIWRDWSUKUUGWKUUHUUIWREHIJBFGHJKLMNYLVKZDJWRTZEWMFUBZJYKHUBZTZD
      UUKWMFGHJKLMNYJVSZRWRUUMJBYKHPWAVQWBZWTEDYQWRDWSDJYCDUUNJDUULUUNRUUOVRJUU
      MUTVLZVAVBVCVMWRHUBWREBFGHJKLMNYLVNYRVIVDDEHIJUUQJDTZWREUURJUUKTWRDUUKJUU
      PVQWRFGHJKLMNUUJVEVRYRVIXEEXCXEXIEXEXHULXIXJEXIXAVJSUMZUNZXBXCXDDHVFVBVCZ
      VDWSEHIJWOFGHJKLMNUUDVKZXBJWSTZEXBJYSHUBZTZUVCCFGHJKLMNYHVSZUVDWSJYSWOHUU
      BWAVQVRZXEEXBUUTXBXCXDCFVFVHVCVMWSHUBWSEWOFGHJKLMNUUDVNUUFVIVDVOVPWDWEXLI
      XEUGZIXHUGZUHWKIXEXHUIUVHWKUVIUVHIXBUOZIXCUOZIXDUOZUJWKIXBXCXDUKUVJWKUVKU
      VLXBEHIJXBUVEJUVFJUVDUTVLZJXBTZWSEUVNJUVCTWSXBUVCJUVGVQWSFGHJKLMNUVBVEVRU
      UFVIXHEXFXHXIEXHXEVJUUSUNZXFXGXBHVFWFVCZVDXCEHIJDFGHJKLMNUUQVKZJXCTZXDEUV
      RJUUKHUBZTZXDXCUVSJDUUKHUUPWAVQWRFGHJKLMNUUJVSZVTZXEEXDUUTXBXCXDWRFVFVGVC
      VIXCHUBXCEDFGHJKLMNUUQVNUVAVIVDXDEHIJXDUVTJUWAJUVSUTVLJXDTZXCEJUVRTUWCXCU
      VRXDJUWBVQXCFGHJKLMNUVQVEWCUVAVIXDHUBWREABFGHJKLMNOPWGYRVIVDVOVPUVIIXFUOZ
      IXGUOZUHWKIXFXGWHUWDWKUWEXFEHIJXBFGHJKLMNUVMVKZJXFTZXGEUWGJUVCHUBZTZXGXFU
      WHJXBUVCHUVGWAVQWSFGHJKLMNUVBVSZVTZXHEXGUVOXFXGWSFVFWIVCVIXFHUBXFEXBFGHJK
      LMNUVMVNUVPVIVDXGEHIJXGUWIJUWJJUWHUTVLJXGTZXFEJUWGTUWLXFUWGXGJUWKVQXFFGHJ
      KLMNUWFVEWCUVPVIXGHUBWSEWLWOFGHJKLMNYDUUAWGUUFVIVDWDVPWDWEWDWESWJ $.

    $( Lemma for ~ kur14 .  Show that the set ` T ` contains at most ` 1 4 `
       elements.  (It could be less if some of the operators take the same
       value for a given set, but Kuratowski showed that this upper bound of
       ` 1 4 ` is tight in the sense that there exist topological spaces and
       subsets of these spaces for which all ` 1 4 ` generated sets are
       distinct, and indeed the real numbers form such a topological space.)
       (Contributed by Mario Carneiro, 11-Feb-2015.) $)
    kur14lem8 $p |- ( T e. Fin /\ ( # ` T ) <_ ; 1 4 ) $=
      ( cfv ctp cdif cun cpr c9 c5 c1 c4 c6 eqid hashtplei 3nn0 3p3e6 hashunlei
      cdc c3 6nn0 6p3e9 c2 hashprlei 2nn0 3p2e5 9nn0 5nn0 9p5e14 ) AIAUAZAHSZTZ
      BCAFSZTZUBZBHSZDVHHSZTZUBZCFSZDHSZVKFSZTZVOHSZVLFSZUCZUBZEUDUEUFUGUNRVJVM
      VNUHUOUDVNUIVGVIVJUOUOUHVJUIAVEVFUJBCVHUJUKUKULUMVKDVLUJUPUKUQUMVRWAWBUOU
      RUEWBUIVOVPVQUJVSVTUSUKUTVAUMVBVCVDUM $.

    kur14lem.s $e |- S = |^| { x e. ~P ~P X |
      ( A e. x /\ A. y e. x { ( X \ y ) , ( K ` y ) } C_ x ) } $.
    $( Lemma for ~ kur14 .  Since the set ` T ` is closed under closure and
       complement, it contains the minimal set ` S ` as a subset, so ` S ` also
       has at most ` 1 4 ` elements.  (Indeed ` S = T ` , and it's not hard to
       prove this, but we don't need it for this proof.)  (Contributed by Mario
       Carneiro, 11-Feb-2015.) $)
    kur14lem9 $p |- ( S e. Fin /\ ( # ` S ) <_ ; 1 4 ) $=
      ( vs c1 c4 cdc cv wcel cdif cfv cpr wss wral wa cpw crab cint wi elintrab
      vex ctp cun ssun1 sseqtrri sstri topopn ax-mp elexi ssexi tpid1 kur14lem7
      ctop sselii simprd simpld elpw2 sylibr ssriv mpbir eleq2 sseq2 raleqbi1dv
      rgen pwex wceq anbi12d imbi12d rspccv mp2ani sylbi eqsstri kur14lem8 1nn0
      mpi 4nn0 deccl hashsslei ) HGUDUEUFGCAUGZUHZLBUGZUIWTKUJUKZWRULZBWRUMZUNZ
      ALUOZUOZUPUQZHUBUCXGHUCUGZXGUHXDXHWRUHZURZAXFUMZXHHUHZXDAXHXFUCUTUSXKCHUH
      ZXAHULZBHUMZXLCLCUIZCKUJZVAZHCXRXRDECIUJZVAZVBZHXRXTVCYAYADKUJZFXSKUJZVAZ
      VBZHYAYDVCYEYEEIUJZFKUJYBIUJVAYFKUJYCIUJUKVBZVBHYEYGVCUAVDVEVECXPXQCLLJJV
      LUHLJUHMJLNVFVGVHZQVIVJVMXNBHWTHUHZWTLULZXNCDEFHIJKWTLMNOPQRSTUAVKZVNWCXK
      HXFUHZXMXOUNZXLURZYLHXEULBHXEYIYJWTXEUHYIYJXNYKVOWTLYHVPVQVRHXELYHWDVPVSX
      JYNAHXFWRHWEZXDYMXIXLYOWSXMXCXOWRHCVTXBXNBWRHWRHXAWAWBWFWRHXHVTWGWHWNWIWJ
      VRWKCDEFHIJKLMNOPQRSTUAWLUDUEWMWOWPWQ $.
  $}

  ${
    $d x y A $.  $d x y J $.  $d x y K $.  $d x y X $.
    kur14lem10.j $e |- J e. Top $.
    kur14lem10.x $e |- X = U. J $.
    kur14lem10.k $e |- K = ( cls ` J ) $.
    kur14lem10.s $e |- S = |^| { x e. ~P ~P X |
      ( A e. x /\ A. y e. x { ( X \ y ) , ( K ` y ) } C_ x ) } $.
    kur14lem10.a $e |- A C_ X $.
    $( Lemma for ~ kur14 .  Discharge the set ` T ` .  (Contributed by Mario
       Carneiro, 11-Feb-2015.) $)
    kur14lem10 $p |- ( S e. Fin /\ ( # ` S ) <_ ; 1 4 ) $=
      ( cfv cdif cnt ctp cun cpr eqid kur14lem9 ) ABCGCFMZNZGCNZFMZUAEOMZMZDCUC
      UAPUBUDCUEMZPQUBFMZUFUGFMZPQUDUEMZUFFMUHUEMPUJFMUIUEMRQQZUEEFGHIJUESLUBSU
      DSUFSUKSKT $.
  $}

  ${
    $d x y A $.  $d x y J $.  $d x X $.
    kur14.x $e |- X = U. J $.
    kur14.k $e |- K = ( cls ` J ) $.
    kur14.s $e |- S = |^| { x e. ~P ~P X |
      ( A e. x /\ A. y e. x { ( X \ y ) , ( K ` y ) } C_ x ) } $.
    $( Kuratowski's closure-complement theorem.  There are at most 14 sets
       which can be obtained by the application of the closure and complement
       operations to a set in a topological space.  (Contributed by Mario
       Carneiro, 11-Feb-2015.) $)
    kur14 $p |- ( ( J e. Top /\ A C_ X ) ->
      ( S e. Fin /\ ( # ` S ) <_ ; 1 4 ) ) $=
      ( wss ctop wcel cfn chash cfv cle wa c0 cpw c1 c4 cdc wbr cif cv cdif cpr
      wral crab cint csn cuni ccl wceq eleq1 anbi1d inteqd eqtrid eleq1d fveq2d
      rabbidv breq1d anbi12d unieq pweqd sseq2d cvv sn0top elimel ax-mp bitr4di
      uniexg elpw2 ifbid difeq1d fveq2 fveq1d preq12d sseq1d ralbidv eqid 0elpw
      rabeqbidv elpwi kur14lem10 dedth2h ancoms ) CGKZELMZDNMZDOPZUAUBUCZQUDZRZ
      WIWJWOWICSUEZAUFZMZGBUFZUGZWSFPZUHZWQKZBWQUIZRZAGTZTZUJZUKZNMZXIOPZWMQUDZ
      RCWJESULZUEZUMZTZMZCSUEZWQMZXOWSUGZWSXNUNPZPZUHZWQKZBWQUIZRZAXPTZUJZUKZNM
      ZYIOPZWMQUDZRCESXMCWPUOZWKXJWNXLYMDXINYMDCWQMZXDRZAXGUJZUKXIJYMYPXHYMYOXE
      AXGYMYNWRXDCWPWQUPUQVBURUSZUTYMWLXKWMQYMDXIOYQVAVCVDEXNUOZXJYJXLYLYRXIYIN
      YRXHYHYRXEYFAXGYGYRXFXPYRGXOYRGEUMXOHEXNVEUSZVFVFYRWRXSXDYEYRWPXRWQYRWIXQ
      CSYRWICXOKXQYRGXOCYSVGCXOXNLMXOVHMEXMLVIVJZXNLVMVKVNVLVOUTYRXCYDBWQYRXBYC
      WQYRWTXTXAYBYRGXOWSYSVPYRWSFYAYRFEUNPYAIEXNUNVQUSVRVSVTWAVDWDURZUTYRXKYKW
      MQYRXIYIOUUAVAVCVDABXRYIXNYAXOYTXOWBYAWBYIWBXRXPMXRXOKCSXPXOWCVJXRXOWEVKW
      FWGWH $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Retracts and sections
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c Retr $.

  $( Extend class notation with the retract relation. $)
  cretr $a class Retr $.

  ${
    $d j k r s $.
    $( Define the set of retractions on two topological spaces.  We say that
       ` R ` is a retraction from ` J ` to ` K ` . or ` R e. ( J Retr K ) ` iff
       there is an ` S ` such that ` R : J --> K , S : K --> J ` are continuous
       functions called the retraction and section respectively, and their
       composite ` R o. S ` is homotopic to the identity map.  If a retraction
       exists, we say ` J ` is a retract of ` K ` .  (This terminology is
       borrowed from HoTT and appears to be nonstandard, although it has
       similaries to the concept of retract in the category of topological
       spaces and to a deformation retract in general topology.)  Two
       topological spaces that are retracts of each other are called homotopy
       equivalent.  (Contributed by Mario Carneiro, 11-Feb-2015.) $)
    df-retr $a |- Retr = ( j e. Top , k e. Top |-> { r e. ( j Cn k ) |
   E. s e. ( k Cn j ) ( ( r o. s ) ( j Htpy j ) ( _I |` U. j ) ) =/= (/) } ) $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Path-connected and simply connected spaces
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c PConn $.
  $c SConn $.

  $( Extend class notation with the class of path-connected topologies. $)
  cpconn $a class PConn $.

  $( Extend class notation with the class of simply connected topologies. $)
  csconn $a class SConn $.

  ${
    $d f j x y $.
    $( Define the class of path-connected topologies.  A topology is
       path-connected if there is a path (a continuous function from the closed
       unit interval) that goes from ` x ` to ` y ` for any points ` x , y ` in
       the space.  (Contributed by Mario Carneiro, 11-Feb-2015.) $)
    df-pconn $a |- PConn = { j e. Top | A. x e. U. j A. y e. U. j
                    E. f e. ( II Cn j ) ( ( f ` 0 ) = x /\ ( f ` 1 ) = y ) } $.

    $( Define the class of simply connected topologies.  A topology is simply
       connected if it is path-connected and every loop (continuous path with
       identical start and endpoint) is contractible to a point (path-homotopic
       to a constant function).  (Contributed by Mario Carneiro,
       11-Feb-2015.) $)
    df-sconn $a |- SConn = { j e. PConn | A. f e. ( II Cn j ) ( ( f ` 0 ) =
            ( f ` 1 ) -> f ( ~=ph ` j ) ( ( 0 [,] 1 ) X. { ( f ` 0 ) } ) ) } $.
  $}

  ${
    $d f x y A $.  $d f y B $.  $d f j x y J $.  $d j x y X $.
    ispconn.1 $e |- X = U. J $.
    $( The property of being a path-connected topological space.  (Contributed
       by Mario Carneiro, 11-Feb-2015.) $)
    ispconn $p |- ( J e. PConn <-> ( J e. Top /\ A. x e. X A. y e. X
      E. f e. ( II Cn J ) ( ( f ` 0 ) = x /\ ( f ` 1 ) = y ) ) ) $=
      ( vj cc0 cv cfv wceq c1 wa cii ccn co wrex cuni wral raleqbidv ctop unieq
      cpconn eqtr4di oveq2 rexeqdv df-pconn elrab2 ) HCIZJAIKLUIJBIKMZCNGIZOPZQ
      ZBUKRZSZAUNSUJCNDOPZQZBESZAESGDUAUCUKDKZUOURAUNEUSUNDREUKDUBFUDZUSUMUQBUN
      EUTUSUJCULUPUKDNOUEUFTTABCGUGUH $.

    $( The property of being a path-connected topological space.  (Contributed
       by Mario Carneiro, 11-Feb-2015.) $)
    pconncn $p |- ( ( J e. PConn /\ A e. X /\ B e. X ) ->
      E. f e. ( II Cn J ) ( ( f ` 0 ) = A /\ ( f ` 1 ) = B ) ) $=
      ( vx vy cpconn wcel cc0 cv cfv wceq c1 wa wrex wral eqeq2 rexbidv cii ccn
      co ctop ispconn simprbi anbi1d anbi2d rspc2v syl5com 3impib ) DIJZAEJZBEJ
      ZKCLZMZANZOUOMZBNZPZCUADUBUCZQZULUPGLZNZURHLZNZPZCVAQZHERGERZUMUNPVBULDUD
      JVIGHCDEFUEUFVHVBUQVFPZCVAQGHABEEVCANZVGVJCVAVKVDUQVFVCAUPSUGTVEBNZVJUTCV
      AVLVFUSUQVEBURSUHTUIUJUK $.
  $}

  ${
    $d f F $.  $d f j x y J $.
    $( A simply connected space is a topology.  (Contributed by Mario Carneiro,
       11-Feb-2015.) $)
    pconntop $p |- ( J e. PConn -> J e. Top ) $=
      ( vf vx vy cpconn wcel ctop cc0 cv cfv wceq c1 wa cii wrex cuni wral eqid
      ccn co ispconn simplbi ) AEFAGFHBIZJCIKLUCJDIKMBNASTODAPZQCUDQCDBAUDUDRUA
      UB $.

    $( The property of being a simply connected topological space.
       (Contributed by Mario Carneiro, 11-Feb-2015.) $)
    issconn $p |- ( J e. SConn <-> ( J e. PConn /\ A. f e. ( II Cn J )
     ( ( f ` 0 ) = ( f ` 1 ) ->
       f ( ~=ph ` J ) ( ( 0 [,] 1 ) X. { ( f ` 0 ) } ) ) ) ) $=
      ( vj cc0 cv cfv c1 wceq cicc co csn cxp cphtpc wbr wi cii ccn wral cpconn
      csconn oveq2 fveq2 breqd imbi2d raleqbidv df-sconn elrab2 ) DAEZFZGUHFHZU
      HDGIJUIKLZCEZMFZNZOZAPULQJZRUJUHUKBMFZNZOZAPBQJZRCBSTULBHZUOUSAUPUTULBPQU
      AVAUNURUJVAUMUQUHUKULBMUBUCUDUEACUFUG $.

    $( A simply connected space is path-connected.  (Contributed by Mario
       Carneiro, 11-Feb-2015.) $)
    sconnpconn $p |- ( J e. SConn -> J e. PConn ) $=
      ( vf csconn wcel cpconn cc0 cv cfv c1 wceq cicc co csn cxp cphtpc wbr cii
      wi ccn wral issconn simplbi ) ACDAEDFBGZHZIUCHJUCFIKLUDMNAOHPRBQASLTBAUAU
      B $.

    $( A simply connected space is a topology.  (Contributed by Mario Carneiro,
       11-Feb-2015.) $)
    sconntop $p |- ( J e. SConn -> J e. Top ) $=
      ( csconn wcel cpconn ctop sconnpconn pconntop syl ) ABCADCAECAFAGH $.

    $( A closed path in a simply connected space is contractible to a point.
       (Contributed by Mario Carneiro, 11-Feb-2015.) $)
    sconnpht $p |- ( ( J e. SConn /\ F e. ( II Cn J ) /\ ( F ` 0 ) =
            ( F ` 1 ) ) -> F ( ~=ph ` J ) ( ( 0 [,] 1 ) X. { ( F ` 0 ) } ) ) $=
      ( vf csconn wcel cii ccn co cc0 cfv c1 wceq cicc csn cxp cphtpc cpconn wi
      wbr fveq1 cv wral issconn eqeq12d xpeq2d breq12d imbi12d rspccv simplbiim
      id sneqd 3imp ) BDEZAFBGHZEZIAJZKAJZLZAIKMHZUPNZOZBPJZSZUMBQEICUAZJZKVDJZ
      LZVDUSVENZOZVBSZRZCUNUBUOURVCRZRCBUCVKVLCAUNVDALZVGURVJVCVMVEUPVFUQIVDATZ
      KVDATUDVMVDAVIVAVBVMUJVMVHUTUSVMVEUPVNUKUEUFUGUHUIUL $.
  $}

  ${
    $d f g u v x y F $.  $d g u v x y J $.  $d f g u v x y K $.  $d g u v X $.
    $d g u v x y Y $.
    cnpconn.2 $e |- Y = U. K $.
    $( An image of a path-connected space is path-connected.  (Contributed by
       Mario Carneiro, 24-Mar-2015.) $)
    cnpconn $p |- ( ( J e. PConn /\ F : X -onto-> Y /\ F e. ( J Cn K ) ) ->
                                                                K e. PConn ) $=
      ( vf vx vy vu vv vg wcel cc0 cv cfv wceq c1 wa wral cpconn wfo ccn co w3a
      ctop cii wrex cntop2 3ad2ant3 cuni pconncn 3expb 3ad2antl1 simprl simpll3
      eqid ccom cnco syl2anc cicc wf iiuni cnf syl 0elunit fvco3 sylancl fveq2d
      simprrl eqtrd 1elunit simprrr fveq1 anbi12d syl12anc rexlimddv ralrimivva
      eqeq1d rspcev crn forn 3ad2ant2 dffo2 sylanbrc eqeq2 anbi2d rexbidv cbvfo
      wb ralbidv mpbid anbi1d ispconn ) BUAMZDEAUBZABCUCUDMZUEZCUFMZNGOZPZHOZQZ
      RWTPZIOZQZSZGUGCUCUDZUHZIETZHETZCUAMWQWOWSWPABCUIUJWRXAJOZAPZQZXFSZGXHUHZ
      IETZJBUKZTZXKWRXNXDKOZAPZQZSZGXHUHZKXRTZJXRTXSWRYDJKXRXRWRXLXRMZXTXRMZSZS
      ZNLOZPZXLQZRYJPZXTQZSZYDLUGBUCUDZWOWPYHYOLYPUHZWQWOYFYGYQXLXTLBXRXRUQZULU
      MUNYIYJYPMZYOSZSZAYJURZXHMZNUUBPZXMQZRUUBPZYAQZYDUUAYSWQUUCYIYSYOUOZWOWPW
      QYHYTUPYJAUGBCUSUTUUAUUDYKAPZXMUUANRVAUDZXRYJVBZNUUJMUUDUUIQUUAYSUUKUUHYJ
      UGBUUJXRVCYRVDVEZVFUUJXRNAYJVGVHUUAYKXLAYIYSYLYNVJVIVKUUAUUFYMAPZYAUUAUUK
      RUUJMUUFUUMQUULVLUUJXRRAYJVGVHUUAYMXTAYIYSYLYNVMVIVKYCUUEUUGSGUUBXHWTUUBQ
      ZXNUUEYBUUGUUNXAUUDXMNWTUUBVNVSUUNXDUUFYARWTUUBVNVSVOVTVPVQVRWRYEXQJXRWRX
      REAUBZYEXQWJWRXREAVBZAWAEQZUUOWQWOUUPWPABCXREYRFVDUJWPWOUUQWQDEAWBWCXREAW
      DWEZYDXPKIXREAYAXEQZYCXOGXHUUSYBXFXNYAXEXDWFWGWHWIVEWKWLWRUUOXSXKWJUURXQX
      JJHXREAXMXBQZXPXIIEUUTXOXGGXHUUTXNXCXFXMXBXAWFWMWHWKWIVEWLHIGCEFWNWE $.
  $}

  ${
    $d a b f x y J $.  $d f g h t u v w x y z R $.  $d f g h t u v w x y z S $.
    $d f g i t x y z A $.  $d f g i t x y z F $.  $d g i t x y z V $.
    $( A path-connected space is connected.  (Contributed by Mario Carneiro,
       11-Feb-2015.) $)
    pconnconn $p |- ( J e. PConn -> J e. Conn ) $=
      ( vx vy va vb vf wcel cv c0 wne wceq wa wex cc0 cfv c1 cii syl2anc adantr
      simplrr cpconn cconn cin w3a cun cuni wral df-3an anbi12i exdistrv bitr4i
      wi n0 ccn wrex simpll simprll simplrl elunii simprlr eqid pconncn syl3anc
      co wn adantl cicc wf iiuni iiconn a1i cdif ccld simprr eqtrid wss elssuni
      uncom wb syl incom uneqdifeq mpbid ctop pconntop ad3antrrr opncld 0elunit
      eqeltrrd eqeltrd conncn 1elunit ffvelcdm sylancl inelcm pm2.21ddne neqned
      expr pm2.01d rexlimddv exp32 exlimdvv biimtrid ralrimivva ctopon toptopon
      impd sylib dfconn2 mpbird ) AUAGZAUBGZBHZIJZCHZIJZXMXOUCZIKZUDZXMXOUEZAUF
      ZJZULZCAUGBAUGZXKYCBCAAXSXNXPLZXRLXKXMAGZXOAGZLZLZYBXNXPXRUHYIYEXRYBYEDHZ
      XMGZEHZXOGZLZEMDMZYIXRYBULZYEYKDMZYMEMZLYOXNYQXPYRDXMUMEXOUMUIYKYMDEUJUKY
      IYNYPDEYIYNXRYBYIYNXRLZLZNFHZOZYJKZPUUAOZYLKZLZYBFQAUNVDZYTXKYJYAGZYLYAGZ
      UUFFUUGUOXKYHYSUPYTYKYFUUHYIYKYMXRUQZXKYFYGYSURZYJXMAUSRYTYMYGUUIYIYKYMXR
      UTZXKYFYGYSTZYLXOAUSRYJYLFAYAYAVAZVBVCYTUUAUUGGZUUFLZLZXTYAUUQXTYAKZYTUUP
      UURUURVEZYTUUPUURLZLZUUSXQIYIYNXRUUTTZUVAYLXMGYMXQIJUVAUUDYLXMUUTUUEYTUUO
      UUCUUEUURTVFUVANPVGVDZXMUUAVHPUVCGUUDXMGUVANXMUUAQAUVCVIQUBGUVAVJVKYTUUOU
      UFUURUQYTYFUUTUUKSUVAYAXOVLZXMAVMOZUVAXOXMUEZYAKZUVDXMKZUVAUVFXTYAXOXMVRY
      TUUPUURVNVOUVAXOYAVPZXOXMUCZIKUVGUVHVSUVAYGUVIYTYGUUTUUMSZXOAVQVTUVAUVJXQ
      IXOXMWAUVBVOXOXMYAWBRWCUVAAWDGZYGUVDUVEGXKUVLYHYSUUTAWEZWFUVKXOAYAUUNWGRW
      INUVCGUVAWHVKUVAUUBYJXMUUTUUCYTUUOUUCUUEUURURVFYTYKUUTUUJSWJWKWLUVCXMPUUA
      WMWNWIYTYMUUTUULSYLXMXOWORWPWRWSWQWTXAXBXCXGXCXDXKAYAXEOGZXLYDVSXKUVLUVNU
      VMAYAUUNXFXHBCAYAXIVTXJ $.

    $( The topological product of two path-connected spaces is path-connected.
       (Contributed by Mario Carneiro, 12-Feb-2015.) $)
    txpconn $p |- ( ( R e. PConn /\ S e. PConn ) -> ( R tX S ) e. PConn ) $=
      ( vf vu vv vz vw vg vh vt wcel wa co cc0 cv cfv wceq c1 wrex wral vx ctop
      vy cpconn ctx cii ccn cuni pconntop txtop syl2an cxp cop w3a eqid pconncn
      an6 anim12i sylbir reeanv sylibr cicc cmpt iiuni txcnmpt ad2antrl 0elunit
      fveq2 opeq12d opex fvmpt ax-mp simprrl simpld simprrr eqtrid simprd fveq1
      1elunit eqeq1d rspcev syl12anc expr rexlimdvva mpd 3expa ralrimivva eqeq2
      anbi12d anbi2d rexbidv ralxp anbi1d 2ralbidv bitrid txuni raleqbidv mpbid
      raleqdv ispconn sylanbrc ) AUDKZBUDKZLZABUEMZUBKZNCOZPZDOZQZRXGPZEOZQZLZC
      UFXEUGMZSZEXEUHZTZDXQTZXEUDKXBAUBKZBUBKZXFXCAUIZBUIZABUJUKXDXPEAUHZBUHZUL
      ZTZDYFTZXSXDXHUAOZUCOZUMZQZXKFOZGOZUMZQZLZCXOSZGYETFYDTZUCYETUAYDTYHXDYSU
      AUCYDYEXDYIYDKZYJYEKZLZLYRFGYDYEXDUUBYMYDKZYNYEKZLZYRXDUUBUUEUNZNHOZPZYIQ
      ZRUUGPZYMQZLZNIOZPZYJQZRUUMPZYNQZLZLZIUFBUGMZSHUFAUGMZSZYRUUFUULHUVASZUUR
      IUUTSZLZUVBUUFXBYTUUCUNZXCUUAUUDUNZLUVEXBYTUUCXCUUAUUDUQUVFUVCUVGUVDYIYMH
      AYDYDUOZUPYJYNIBYEYEUOZUPURUSUULUURHIUVAUUTUTVAUUFUUSYRHIUVAUUTUUFUUGUVAK
      UUMUUTKLZUUSYRUUFUVJUUSLLZJNRVBMZJOZUUGPZUVMUUMPZUMZVCZXOKZNUVQPZYKQZRUVQ
      PZYOQZYRUVJUVRUUFUUSJABUFUUGUUMUVQUVLVDUVQUOZVEVFUVKUVSUUHUUNUMZYKNUVLKUV
      SUWDQVGJNUVPUWDUVLUVQUVMNQUVNUUHUVOUUNUVMNUUGVHUVMNUUMVHVIUWCUUHUUNVJVKVL
      UVKUUHYIUUNYJUVKUUIUUKUUFUVJUULUURVMZVNUVKUUOUUQUUFUVJUULUURVOZVNVIVPUVKU
      WAUUJUUPUMZYORUVLKUWAUWGQVSJRUVPUWGUVLUVQUVMRQUVNUUJUVOUUPUVMRUUGVHUVMRUU
      MVHVIUWCUUJUUPVJVKVLUVKUUJYMUUPYNUVKUUIUUKUWEVQUVKUUOUUQUWFVQVIVPYQUVTUWB
      LCUVQXOXGUVQQZYLUVTYPUWBUWHXHUVSYKNXGUVQVRVTUWHXKUWAYORXGUVQVRVTWIWAWBWCW
      DWEWFWGWGYGYSDUAUCYDYEYGXJYPLZCXOSZGYETFYDTXIYKQZYSXPUWJEFGYDYEXLYOQZXNUW
      ICXOUWLXMYPXJXLYOXKWHWJWKWLUWKUWJYRFGYDYEUWKUWIYQCXOUWKXJYLYPXIYKXHWHWMWK
      WNWOWLVAXDYGXRDYFXQXBXTYAYFXQQXCYBYCABYDYEUVHUVIWPUKZXDXPEYFXQUWMWSWQWRDE
      CXEXQXQUOWTXA $.

    $( The topological product of a collection of path-connected spaces is
       path-connected.  The proof uses the axiom of choice.  (Contributed by
       Mario Carneiro, 17-Feb-2015.) $)
    ptpconn $p |- ( ( A e. V /\ F : A --> PConn ) -> ( Xt_ ` F ) e. PConn ) $=
      ( vf vx vt vz vi wcel cpconn wa cfv cc0 cv wceq c1 cii wral cmpt fveq2 vy
      vg wf cpt ctop ccn co wrex cuni wss pconntop ssriv fss mpan2 pttop sylan2
      cid wfn wex fvi ad2antrr eleq2d biimpa simplr ffvelcdmda cixp simprl eqid
      ptuni adantr eleqtrrd elixp simprd r19.21bi simprr pconncn syl3anc df-rex
      vex sylib syldan ralrimiva fvex eleq1 fveq1 eqeq1d anbi12d ac6s2 syl cicc
      ctopon iitopon simplll biimpar oveq2d eleq12d fveq1d eqeq12d sylan simpld
      a1i rspccva iiuni cnf feqmptd eqeltrrd ptcn mpteq2dva cvv mptexg mpteq2dv
      0elunit fvmptg sylancr dffn5 3eqtr4d 1elunit syl12anc exlimddv ralrimivva
      rspcev ispconn sylanbrc ) ACIZAJBUCZKZBUDLZUEIZMDNZLZENZOZPYILZUANZOZKZDQ
      YGUFUGZUHZUAYGUIZREYSRYGJIYEYDAUEBUCZYHYEJUEUJYTEJUEYKUKULAJUEBUMUNZABCUO
      UPYFYREUAYSYSYFYKYSIZYNYSIZKZKZUBNZAUQLZURZFNZUUFLZQUUIBLZUFUGZIZMUUJLZUU
      IYKLZOZPUUJLZUUIYNLZOZKZKZFUUGRZKZYRUBUUEYIUULIZYJUUOOZYMUUROZKZKZDUSZFUU
      GRUVCUBUSUUEUVIFUUGUUEUUIUUGIZUUIAIZUVIUUEUVJUVKUUEUUGAUUIYDUUGAOZYEUUDAC
      UTVAZVBVCUUEUVKKZUVGDUULUHZUVIUVNUUKJIUUOUUKUIZIZUURUVPIZUVOUUEAJUUIBYDYE
      UUDVDZVEUUEUVQFAUUEYKAURZUVQFARZUUEYKFAUVPVFZIUVTUWAKUUEYKYSUWBYFUUBUUCVG
      YFUWBYSOZUUDYEYDYTUWCUUAFABYGCYGVHZVIUPVJZVKFAUVPYKEVSVLVTZVMVNUUEUVRFAUU
      EYNAURZUVRFARZUUEYNUWBIUWGUWHKUUEYNYSUWBYFUUBUUCVOUWEVKFAUVPYNUAVSVLVTZVM
      VNUUOUURDUUKUVPUVPVHVPVQUVGDUULVRVTWAWBUVHUVAFDUUGUBAUQWCYIUUJOZUVDUUMUVG
      UUTYIUUJUULWDUWJUVEUUPUVFUUSUWJYJUUNUUOMYIUUJWEWFUWJYMUUQUURPYIUUJWEWFWGW
      GWHWIUUEUVCKZGMPWJUGZHAGNZHNZUUFLZLZSZSZYQIMUWRLZYKOZPUWRLZYNOZYRUWKGUWPH
      BAQYGCUWLUWDQUWLWKLIUWKWLXAYDYEUUDUVCWMZUWKYEYTUUEYEUVCUVSVJUUAWIUWKUWNAI
      ZKZUWOGUWLUWPSQUWNBLZUFUGZUXEGUWLUXFUIZUWOUXEUWOUXGIZUWLUXHUWOUCUXEUXIMUW
      OLZUWNYKLZOZPUWOLZUWNYNLZOZKZUWKUXDUWNUUGIZUXIUXPKZUWKUXQUXDUWKUUGAUWNUUE
      UVLUVCUVMVJVBWNUWKUVBUXQUXRUUEUUHUVBVOUVAUXRFUWNUUGUUIUWNOZUUMUXIUUTUXPUX
      SUUJUWOUULUXGUUIUWNUUFTZUXSUUKUXFQUFUUIUWNBTWOWPUXSUUPUXLUUSUXOUXSUUNUXJU
      UOUXKUXSMUUJUWOUXTWQUUIUWNYKTWRUXSUUQUXMUURUXNUXSPUUJUWOUXTWQUUIUWNYNTWRW
      GWGXBWSWAZWTZUWOQUXFUWLUXHXCUXHVHXDWIXEUYBXFXGUWKHAUXJSZHAUXKSZUWSYKUWKHA
      UXJUXKUXEUXLUXOUXEUXIUXPUYAVMZWTXHUWKMUWLIUYCXIIZUWSUYCOXLUWKYDUYFUXCHAUX
      JCXJWIGMUWQUYCUWLXIUWRUWMMOHAUWPUXJUWMMUWOTXKUWRVHZXMXNUWKUVTYKUYDOUUEUVT
      UVCUUEUVTUWAUWFWTVJHAYKXOVTXPUWKHAUXMSZHAUXNSZUXAYNUWKHAUXMUXNUXEUXLUXOUY
      EVMXHUWKPUWLIUYHXIIZUXAUYHOXQUWKYDUYJUXCHAUXMCXJWIGPUWQUYHUWLXIUWRUWMPOHA
      UWPUXMUWMPUWOTXKUYGXMXNUWKUWGYNUYIOUUEUWGUVCUUEUWGUWHUWIWTVJHAYNXOVTXPYPU
      WTUXBKDUWRYQYIUWROZYLUWTYOUXBUYKYJUWSYKMYIUWRWEWFUYKYMUXAYNPYIUWRWEWFWGYA
      XRXSXTEUADYGYSYSVHYBYC $.
  $}

  ${
    $d f x y z A $.  $d f g h s u w x y z J $.
    $( The indiscrete topology (or trivial topology) on any set is
       path-connected.  (Contributed by Mario Carneiro, 7-Jul-2015.)  (Revised
       by Mario Carneiro, 14-Aug-2015.) $)
    indispconn $p |- { (/) , A } e. PConn $=
      ( vf vx vy vz c0 wcel cc0 cv cfv wceq c1 wa cii co cuni wral cicc cun cvv
      cpr cpconn ctop ccn wrex indistop cif cmpt wf simpl 0ex n0i wn csn prprc2
      unieqd unisn eqtrdi nsyl2 adantr uniprg sylancr uncom eqtri eleqtrd simpr
      cmap un0 ifcld fmpttd ovex elmapg sylancl mpbird iitopon cnindis eleqtrrd
      wb ctopon 0elunit iftrue eqid vex fvmpt mp1i 1elunit ax-1ne0 neeq1 mpbiri
      wne ifnefalse fveq1 eqeq1d anbi12d rspcev syl12anc rgen2 ispconn mpbir2an
      syl ) FAUAZUBGXAUCGHBIZJZCIZKZLXBJZDIZKZMZBNXAUDOZUEZDXAPZQCXLQAUFXKCDXLX
      LXDXLGZXGXLGZMZEHLROZEIZHKZXDXGUGZUHZXJGHXTJZXDKZLXTJZXGKZXKXOXTAXPVGOZXJ
      XOXTYEGZXPAXTUIZXOEXPXSAXOXSAGXQXPGXOXRXDXGAXOXDXLAXMXNUJXOXLFASZAXOFTGAT
      GZXLYHKUKXMYIXNXMXLFKYIXLXDULYIUMZXLFUNZPFYJXAYKFAUOUPFUKUQURUSUTZFATTVAV
      BYHAFSAFAVCAVHVDURZVEXOXGXLAXMXNVFYMVEVIUTVJXOYIXPTGYFYGVRYLHLRVKAXPXTTTV
      LVMVNXONXPVSJGYIXJYEKVOYLANTXPVPVBVQHXPGYBXOVTEHXSXDXPXTXRXDXGWAXTWBZCWCW
      DWELXPGYDXOWFELXSXGXPXTXQLKZXQHWJZXSXGKYOYPLHWJWGXQLHWHWIXQHXDXGWKWTYNDWC
      WDWEXIYBYDMBXTXJXBXTKZXEYBXHYDYQXCYAXDHXBXTWLWMYQXFYCXGLXBXTWLWMWNWOWPWQC
      DBXAXLXLWBWRWS $.

    $( A connected and locally path-connected space is path-connected.
       (Contributed by Mario Carneiro, 7-Jul-2015.) $)
    connpconn $p |- ( ( J e. Conn /\ J e. N-Locally PConn ) -> J e. PConn ) $=
      ( vf vx vy vz vu vw vg wcel wa cc0 cv cfv wceq c1 adantr wss fveq1 eqeq1d
      wrex vs vh cconn cpconn cnlly ctop cii ccn co cuni wral conntop crab eqid
      simpll ccld cin inss1 wel crest w3a cpw simplr ad2antrr topopn syl simprr
      wi nlly2i syl3anc simprr1 weq eqeq2 rexbidv elrab simprbi simprr3 simprr2
      anbi2d simprll sseldd elpwi ad2antrl restuni syl2anc eleqtrd pconncn cpco
      simplrl ad2antlr cnrest2r simprl simplrr simprd simprrl eqtr4d pcocn pco0
      simpld eqtrd simprrr anbi12d rspcev syl12anc rexlimddv anassrs rexlimdvaa
      pco1 ralrimiva sstrd jctild cbvrexvw ssrab 3imtr4g syl5 reximdv rexlimdva
      jca expr mpd wb ssrab2 isclo2 sylancl mpbird sselid c0 wne cicc csn simpr
      cxp ctopon iitopon a1i toptopon sylib cnconst2 fvconst2 mp1i rabn0 sylibr
      0elunit vex 1elunit rspc2ev syl112anc inss2 connclo eqcomd rabid2 ispconn
      sylanbrc ) AUCIZAUDUEIZJZAUFIZKBLZMZCLZNZOUURMZDLZNZJZBUGAUHUIZTZDAUJZUKZ
      CUVHUKAUDIUUNUUQUUOAULZPUUPUVICUVHUUPUUTUVHIZJZUVHUVGDUVHUMZNUVIUVLUVMUVH
      UVLUVMAUVHUVHUNZUUNUUOUVKUOUVLAAUPMZUQZAUVMAUVOURUVLUVMUVPIZEFUSZGLZUVMIZ
      FLZUVMQZVHZGUWAUKZJZFATZEUVHUKZUVLUWFEUVHUUPUVKELZUVHIZUWFUUPUVKUWIJZJZUV
      RUWAUALZQZAUWLUTUIZUDIZVAZFATZUAUVHVBZTZUWFUWKUUOUVHAIZUWIUWSUUNUUOUWJVCU
      WKUUQUWTUUNUUQUUOUWJUVJVDZAUVHUVNVEVFUUPUVKUWIVGFUDUWHUVHAUAVIVJUWKUWQUWF
      UAUWRUWKUWLUWRIZJUWPUWEFAUWKUXBUWPUWEUWKUXBUWPJZJZUVRUWDUVRUWMUWOUXBUWKVK
      UXDUWCGUWAUVTUVAUVBUVSNZJZBUVFTZUXDGFUSZJZUWBUVTUVSUVHIUXGUVGUXGDUVSUVHDG
      VLZUVEUXFBUVFUXJUVDUXEUVAUVCUVSUVBVMVSVNVOVPUXIKHLZMZUUTNZOUXKMZUVSNZJZHU
      VFTZUWAUVHQZUVGDUWAUKZJUXGUWBUXIUXQUXSUXRUXIUXPUXSHUVFUXDUXHUXKUVFIZUXPJZ
      UXSUXDUXHUYAJZJUVGDUWAUXDUYBDFUSZUVGUXDUYBUYCJZJZKUBLZMZUVSNZOUYFMZUVCNZJ
      ZUVGUBUGUWNUHUIZUYEUWOUVSUWNUJZIUVCUYMIUYKUBUYLTUXDUWOUYDUVRUWMUWOUXBUWKV
      QPUYEUVSUWLUYMUYEUWAUWLUVSUXDUWMUYDUVRUWMUWOUXBUWKVRZPZUXDUXHUYAUYCVTWAUY
      EUUQUWLUVHQZUWLUYMNUWKUUQUXCUYDUXAVDZUXDUYPUYDUXBUYPUWKUWPUWLUVHWBZWCPUWL
      AUVHUVNWDWEZWFUYEUVCUWLUYMUYEUWAUWLUVCUYOUXDUYBUYCVGWAUYSWFUVSUVCUBUWNUYM
      UYMUNWGVJUYEUYFUYLIZUYKJZJZUXKUYFAWHMUIZUVFIKVUCMZUUTNZOVUCMZUVCNZUVGVUBU
      XKUYFAUYDUXTUXDVUAUXHUXTUXPUYCWIWJZVUBUYLUVFUYFVUBUUQUYLUVFQUYEUUQVUAUYQP
      UWLUGAWKVFUYEUYTUYKWLWAZVUBUXNUVSUYGVUBUXMUXOUYDUXPUXDVUAUXHUXTUXPUYCWMWJ
      ZWNUYEUYTUYHUYJWOWPWQVUBVUDUXLUUTVUBUXKUYFAVUHVUIWRVUBUXMUXOVUJWSWTVUBVUF
      UYIUVCVUBUXKUYFAVUHVUIXHUYEUYTUYHUYJXAWTUVEVUEVUGJBVUCUVFUURVUCNZUVAVUEUV
      DVUGVUKUUSVUDUUTKUURVUCRSVUKUVBVUFUVCOUURVUCRSXBXCXDXEXFXIXFXGUXIUWAUWLUV
      HUXDUWMUXHUYNPUXIUXBUYPUWKUXBUWPUXHWIUYRVFXJXKUXFUXPBHUVFBHVLZUVAUXMUXEUX
      OVULUUSUXLUUTKUURUXKRSVULUVBUXNUVSOUURUXKRSXBXLUVGDUVHUWAXMXNXOXIXRXSXPXQ
      XTXFXIUVLUUQUVMUVHQUVQUWGYAUUNUUQUUOUVKUVJVDZUVGDUVHYBEFGUVMAUVHUVNYCYDYE
      ZYFUVLUVGDUVHTZUVMYGYHUVLUVKKOYIUIZUUTYJYLZUVFIZKVUQMZUUTNZOVUQMZUUTNZVUO
      UUPUVKYKZUVLUGVUPYMMIZAUVHYMMIZUVKVURVVDUVLYNYOUVLUUQVVEVUMAUVHUVNYPYQVVC
      UUTUGAVUPUVHYRVJKVUPIVUTUVLUUCVUPUUTKCUUDZYSYTOVUPIVVBUVLUUEVUPUUTOVVFYSY
      TUVEVUTVVBJUVAUVBUUTNZJDBUUTVUQUVHUVFDCVLUVDVVGUVAUVCUUTUVBVMVSUURVUQNZUV
      AVUTVVGVVBVVHUUSVUSUUTKUURVUQRSVVHUVBVVAUUTOUURVUQRSXBUUFUUGUVGDUVHUUAUUB
      UVLUVPUVOUVMAUVOUUHVUNYFUUIUUJUVGDUVHUUKYQXICDBAUVHUVNUULUUM $.
  $}

  ${
    $d f h x y $.  $d f h y A $.  $d f P $.  $d f Q $.  $d f S $.
    $d f h y B $.  $d f h y J $.  $d f T $.  $d f h y X $.
    pconnpi1.x $e |- X = U. J $.
    $( A quotient of a path-connected space is path-connected.  (Contributed by
       Mario Carneiro, 24-Mar-2015.) $)
    qtoppconn $p |- ( ( J e. PConn /\ F Fn X ) -> ( J qTop F ) e. PConn ) $=
      ( cpconn pconntop cqtop co cuni eqid cnpconn qtopcmplem ) EABCDBFABBAGHZC
      MIZNJKL $.

    pconnpi1.p $e |- P = ( J pi1 A ) $.
    pconnpi1.q $e |- Q = ( J pi1 B ) $.
    pconnpi1.s $e |- S = ( Base ` P ) $.
    pconnpi1.t $e |- T = ( Base ` Q ) $.
    $( All fundamental groups in a path-connected space are isomorphic.
       (Contributed by Mario Carneiro, 12-Feb-2015.) $)
    pconnpi1 $p |- ( ( J e. PConn /\ A e. X /\ B e. X ) -> P ~=g Q ) $=
      ( wcel cv cfv c1 co cpi1 eqid vf vh vx vy cpconn w3a cc0 wceq wa cgic wbr
      cii ccn pconncn cbs cuni cphtpc cec cicc cmin cmpt cpco cop crn cgim ctop
      ctopon simpl1 pconntop syl toptopon sylib simprl fveq2d cbvmptv pi1xfrgim
      oveq2 simprrl oveq2d eqtr4di simprrr oveq12d eleqtrd brgici rexlimddv ) G
      UENZAHNZBHNZUFZUGUAOZPZAUHZQWJPZBUHZUIZCDUJUKZUAULGUMRZABUAGHIUNWIWJWQNZW
      OUIZUIZUBGWKSRZUOPZUPUBOZGUQPZURUCUGQUSRZQUCOZUTRZWJPZVAZXCWJGVBPZRXJRXDU
      RVCVAVDZCDVERZNWPWTXKXAGWMSRZVERXLWTUDXBXAXMUBWJXKXIGHXATXMTXBTXKTWTGVFNZ
      GHVGPNWTWFXNWFWGWHWSVHGVIVJGHIVKVLWIWRWOVMUCUDXEXHQUDOZUTRZWJPXFXOUHXGXPW
      JXFXOQUTVQVNVOVPWTXACXMDVEWTXAGASRCWTWKAGSWIWRWLWNVRVSJVTWTXMGBSRDWTWMBGS
      WIWRWLWNWAVSKVTWBWCCDXKWDVJWE $.
  $}

  ${
    $d x G $.  $d x J $.
    sconnpht2.1 $e |- ( ph -> J e. SConn ) $.
    sconnpht2.2 $e |- ( ph -> F e. ( II Cn J ) ) $.
    sconnpht2.3 $e |- ( ph -> G e. ( II Cn J ) ) $.
    sconnpht2.4 $e |- ( ph -> ( F ` 0 ) = ( G ` 0 ) ) $.
    sconnpht2.5 $e |- ( ph -> ( F ` 1 ) = ( G ` 1 ) ) $.
    $( Any two paths in a simply connected space with the same start and end
       point are path-homotopic.  (Contributed by Mario Carneiro,
       12-Feb-2015.) $)
    sconnpht2 $p |- ( ph -> F ( ~=ph ` J ) G ) $=
      ( vx cc0 c1 co cfv csn cxp wbr wcel wceq eqtr4d cicc cmin cmpt cphtpc cii
      cv cpco csconn ccn w3a eqid pcorevcl simp1d simp2d pcocn pco0 pco1 simp3d
      syl sconnpht syl3anc sneqd xpeq2d breqtrd pcophtb mpbid ) ABJKLUAMZLJUFUB
      MCNUCZDUGNMZVGKBNZOZPZDUDNZQBCVMQAVIVGKVINZOZPZVLVMADUHRVIUEDUIMZRVNLVINZ
      SVIVPVMQEABVHDFAVHVQRZKVHNZLCNZSZLVHNZKCNZSZACVQRVSWBWEUJGJCVHDVHUKZULUSZ
      UMZALBNWAVTIAVSWBWEWGUNTUOAVNVJVRABVHDFWHUPZAVRWCVJABVHDFWHUQAVJWDWCHAVSW
      BWEWGURTTTVIDUTVAAVOVKVGAVNVJWIVBVCVDAJVLBCVHDWFVLUKFGHIVEVF $.
  $}

  ${
    $d f x J $.  $d f x X $.  $d f x Y $.
    sconnpi1.1 $e |- X = U. J $.
    $( A path-connected topological space is simply connected iff its
       fundamental group is trivial.  (Contributed by Mario Carneiro,
       12-Feb-2015.) $)
    sconnpi1 $p |- ( ( J e. PConn /\ Y e. X ) ->
                           ( J e. SConn <-> ( Base ` ( J pi1 Y ) ) ~~ 1o ) ) $=
      ( vx vf wcel wa co cfv c1o cen wbr csn cc0 wceq c1 eqid syl2anc syl cv wb
      cpconn csconn cpi1 cbs c0g cphtpc cec cii wrex ctop sconntop adantl simpl
      ccn ctopon toptopon sylib simpr elpi1 cicc cxp wer phtpcer simpllr simplr
      simprl simprr eqtr4d sconnpht syl3anc sneqd xpeq2d breqtrd erthi ad2antrr
      a1i pi1id eqtrd velsn eqeq1 bitrid syl5ibrcom rexlimdva sylbid ssrdv cgrp
      expimpd pi1grp grpidcl snssd eqssd fvex ensn1 eqbrtrdi adantll wi simplll
      simpll pconntop wf iiuni cnf 0elunit ffvelcdm sylancl eqidd eqcomd elpi1i
      wral w3a pcoptcl simp1d simp2d simp3d cgic pconnpi1 gicen en1eqsn eleqtrd
      entr elsni erth mpbird expr ralrimiva issconn sylanbrc impbida ) AUCGZCBG
      ZHZAUDGZACUEIZUFJZKLMZYLYNYQYKYLYNHZYPYOUGJZNZKLYRYPYTYREYPYTYREUAZYPGZOF
      UAZJZCPZQUUCJZCPZHZUUAUUCAUHJZUIZPZHZFUJAUPIZUKZUUAYTGZYRAULGZYLUUBUUNUBY
      NUUPYLAUMUNZYLYNUOZUUPYLHZYPFUUAYOABCYORZYPRZUUSUUPABUQJGZUUPYLUOABDURZUS
      UUPYLUTVASYRUULUUOFUUMYRUUCUUMGZHZUUHUUKUUOUVEUUHHZUUOUUKUUJYSPZUVFUUJOQV
      BIZCNZVCZUUIUIZYSUVFUUCUVJUUIUUMUUMUUIVDZUVFAVEZVRUVFUUCUVHUUDNZVCZUVJUUI
      UVFYNUVDUUDUUFPZUUCUVOUUIMZYLYNUVDUUHVFYRUVDUUHVGUVFUUDCUUFUVEUUEUUGVHZUV
      EUUEUUGVIVJUUCAVKVLUVFUVNUVIUVHUVFUUDCUVRVMVNVOVPYRUVKYSPZUVDUUHYRUVBYLUV
      SYRUUPUVBUUQUVCUSZUURYOABCUVJUUTUVJRVSSVQVTUUOUUAYSPUUKUVGEYSWAUUAUUJYSWB
      WCWDWIWEWFWGYRYSYPYRYOWHGZYSYPGYRUVBYLUWAUVTUURYOABCUUTWJSYPYOYSUVAYSRWKT
      WLWMYSYOUGWNWOWPWQYMYQHZYKUVPUVQWRZFUUMXKYNYKYLYQWTUWBUWCFUUMUWBUVDUVPUVQ
      UWBUVDUVPHZHZUVQUUJUVOUUIUIZPZUWEUUJUWFNZGUWGUWEUUJAUUDUEIZUFJZUWHUWEUWJU
      UCUWIABUUDUWIRZUWJRZUWEUUPUVBUWEYKUUPYKYLYQUWDWSZAXATUVCUSZUWEUVHBUUCXBZO
      UVHGUUDBGZUWEUVDUWOUWBUVDUVPVHZUUCUJAUVHBXCDXDTXEUVHBOUUCXFXGZUWQUWEUUDXH
      UWEUUDUUFUWBUVDUVPVIXIXJUWEUWFUWJGUWJKLMZUWJUWHPUWEUWJUVOUWIABUUDUWKUWLUW
      NUWRUWEUVOUUMGZOUVOJUUDPZQUVOJUUDPZUWEUVBUWPUWTUXAUXBXLUWNUWRUVOABUUDUVOR
      XMSZXNUWEUWTUXAUXBUXCXOUWEUWTUXAUXBUXCXPXJUWEUWJYPLMZYQUWSUWEUWIYOXQMZUXD
      UWEYKUWPYLUXEUWMUWRYKYLYQUWDVFUUDCUWIYOUWJYPABDUWKUUTUWLUVAXRVLUWJYPUWIYO
      UWLUVAXSTYMYQUWDVGUWJYPKYBSUWFUWJXTSYAUUJUWFYCTUWEUUCUVOUUIUUMUVLUWEUVMVR
      UWQYDYEYFYGFAYHYIYJ $.
  $}

  ${
    $d s x y G $.  $d s x y H $.  $d s x y ph $.  $d s x y R $.  $d s x y S $.
    $d x A $.  $d x B $.  $d s x F $.
    txsconn.1 $e |- ( ph -> R e. Top ) $.
    txsconn.2 $e |- ( ph -> S e. Top ) $.
    txsconn.3 $e |- ( ph -> F e. ( II Cn ( R tX S ) ) ) $.
    txsconn.5 $e |- A = ( ( 1st |` ( U. R X. U. S ) ) o. F ) $.
    txsconn.6 $e |- B = ( ( 2nd |` ( U. R X. U. S ) ) o. F ) $.
    txsconn.7 $e |- ( ph ->
      G e. ( A ( PHtpy ` R ) ( ( 0 [,] 1 ) X. { ( A ` 0 ) } ) ) ) $.
    txsconn.8 $e |- ( ph ->
      H e. ( B ( PHtpy ` S ) ( ( 0 [,] 1 ) X. { ( B ` 0 ) } ) ) ) $.
    $( Lemma for ~ txsconn .  (Contributed by Mario Carneiro, 9-Mar-2015.) $)
    txsconnlem $p |- ( ph ->
      F ( ~=ph ` ( R tX S ) ) ( ( 0 [,] 1 ) X. { ( F ` 0 ) } ) ) $=
      ( co cc0 c1 cfv wceq vx vy vs cii ctx ccn wcel cicc csn cxp cphtpy c0 wne
      cphtpc wbr cmpt fconstmpt cuni ctopon iitopon a1i ctop eqid sylib txtopon
      toptopon syl2anc wf cnf2 syl3anc 0elunit ffvelcdm sylancl cnmptc eqeltrid
      cop cmpo wfn c1st cres ccom tx1cn cnco iiuni cnf syl phtpycn sseldd iitop
      cv txunii ffn 3syl fnov eqeltrrd c2nd tx2cn cnmpt2t chtpy phtpyhtpy htpyi
      simpld fveq1i fvco3 sylan eqtrid fvres 3eqtrd opeq12d simpr oveq12 ovmpoa
      wa opex 1st2nd2 3eqtr4d simprd fvex fvconst2 adantl adantr 1elunit phtpyi
      eqtrd sylancr isphtpy2d ne0d isphtpc syl3anbrc ) AFUDDEUEPZUFPZUGZQRUHPZQ
      FSZUIUJZYKUGFYOYJUKSPZULUMFYOYJUNSUOKAYOUAYMYNUPYKUAYMYNUQAUAYNUDYJYMDURZ
      EURZUJZUDYMUSSUGZAUTVAZADYQUSSUGZEYRUSSUGZYJYSUSSUGZADVBUGUUBIDYQYQVCZVFV
      DZAEVBUGUUCJEYRYRVCZVFVDZDEYQYRVEVGZAYMYSFVHZQYMUGZYNYSUGZAYTUUDYLUUJUUAU
      UIKFUDYJYMYSVIVJZVKYMYSQFVLVMZVNVOZAYPUAUBYMYMUAWJZUBWJZGPZUUPUUQHPZVPZVQ
      ZAFYOUVAYJUCKUUOAUAUBUURUUSUDUDDEYMYMUUAUUAAGUAUBYMYMUURVQZUDUDUEPZDUFPZA
      GYMYMUJZVRZGUVBTAGUVDUGUVEYQGVHUVFABYMQBSZUIUJZDUKSPZUVDGABUVHDABVSYSVTZF
      WAZUDDUFPZLAYLUVJYJDUFPUGZUVKUVLUGKAUUBUUCUVMUUFUUHDEYQYRWBVGFUVJUDYJDWCV
      GVOZAUVHUAYMUVGUPUVLUAYMUVGUQAUAUVGUDDYMYQUUAUUFAYMYQBVHZUUKUVGYQUGABUVLU
      GUVOUVNBUDDYMYQWDUUEWEWFVKYMYQQBVLVMVNVOZWGNWHZGUVCDUVEYQUDUDYMYMWIWIWDWD
      WKZUUEWEUVEYQGWLWMUAUBYMYMGWNVDUVQWOAHUAUBYMYMUUSVQZUVCEUFPZAHUVEVRZHUVST
      AHUVTUGUVEYRHVHUWAACYMQCSZUIUJZEUKSPZUVTHACUWCEACWPYSVTZFWAZUDEUFPZMAYLUW
      EYJEUFPUGZUWFUWGUGKAUUBUUCUWHUUFUUHDEYQYRWQVGFUWEUDYJEWCVGVOZAUWCUAYMUWBU
      PUWGUAYMUWBUQAUAUWBUDEYMYRUUAUUHAYMYRCVHZUUKUWBYRUGACUWGUGUWJUWICUDEYMYRW
      DUUGWEWFVKYMYRQCVLVMVNVOZWGOWHZHUVCEUVEYRUVRUUGWEUVEYRHWLWMUAUBYMYMHWNVDU
      WLWOWRAUCWJZYMUGZXMZUWMQGPZUWMQHPZVPZUWMFSZVSSZUWSWPSZVPZUWMQUVAPZUWSUWOU
      WPUWTUWQUXAUWOUWPUWMBSZUWSUVJSZUWTUWOUWPUXDTZUWMRGPZUWMUVHSZTZAUWMBUVHGUD
      DYMUUAUVNUVPAUVIBUVHUDDWSPPGABUVHDUVNUVPWTNWHXAZXBUWOUXDUWMUVKSZUXEUWMBUV
      KLXCAUUJUWNUXKUXETUUMYMYSUWMUVJFXDXEXFUWOUWSYSUGZUXEUWTTAUUJUWNUXLUUMYMYS
      UWMFVLXEZUWSYSVSXGWFXHUWOUWQUWMCSZUWSUWESZUXAUWOUWQUXNTZUWMRHPZUWMUWCSZTZ
      AUWMCUWCHUDEYMUUAUWIUWKAUWDCUWCUDEWSPPHACUWCEUWIUWKWTOWHXAZXBUWOUXNUWMUWF
      SZUXOUWMCUWFMXCAUUJUWNUYAUXOTUUMYMYSUWMUWEFXDXEXFUWOUXLUXOUXATUXMUWSYSWPX
      GWFXHXIUWOUWNUUKUXCUWRTAUWNXJZVKUAUBUWMQYMYMUUTUWRUVAUUPUWMTZUUQQTXMUURUW
      PUUSUWQUUPUWMUUQQGXKUUPUWMUUQQHXKXIUVAVCZUWPUWQXNXLVMUWOUXLUWSUXBTUXMUWSY
      QYRXOWFXPUWOUXGUXQVPZYNVSSZYNWPSZVPZUWMRUVAPZUWMYOSZUWOUXGUYFUXQUYGUWOUXG
      UXHUVGUYFUWOUXFUXIUXJXQUWNUXHUVGTAYMUVGUWMQBXRXSXTAUVGUYFTUWNAUVGQUVKSZUY
      FQBUVKLXCAUYKYNUVJSZUYFAUUJUUKUYKUYLTUUMVKYMYSQUVJFXDVMAUULUYLUYFTUUNYNYS
      VSXGWFYDXFYAZXHUWOUXQUXRUWBUYGUWOUXPUXSUXTXQUWNUXRUWBTAYMUWBUWMQCXRXSXTAU
      WBUYGTUWNAUWBQUWFSZUYGQCUWFMXCAUYNYNUWESZUYGAUUJUUKUYNUYOTUUMVKYMYSQUWEFX
      DVMAUULUYOUYGTUUNYNYSWPXGWFYDXFYAZXHXIUWOUWNRYMUGZUYIUYETUYBYBUAUBUWMRYMY
      MUUTUYEUVAUYCUUQRTXMUURUXGUUSUXQUUPUWMUUQRGXKUUPUWMUUQRHXKXIUYDUXGUXQXNXL
      VMUWOUYJYNUYHUWNUYJYNTAYMYNUWMQFXRXSXTUWOUULYNUYHTAUULUWNUUNYAYNYQYRXOWFZ
      YDXPUWOQUWMGPZQUWMHPZVPZUYHQUWMUVAPZYNUWOUYSUYFUYTUYGUWOUYSUVGUYFUWOUYSUV
      GTZRUWMGPZRBSZTZAUWMBUVHGDUVNUVPNYCZXBUYMYDUWOUYTUWBUYGUWOUYTUWBTZRUWMHPZ
      RCSZTZAUWMCUWCHEUWIUWKOYCZXBUYPYDXIUWOUUKUWNVUBVUATVKUYBUAUBQUWMYMYMUUTVU
      AUVAUUPQTUUQUWMTZXMUURUYSUUSUYTUUPQUUQUWMGXKUUPQUUQUWMHXKXIUYDUYSUYTXNXLY
      EUYRXPUWOVUDVUIVPZRFSZVSSZVUOWPSZVPZRUWMUVAPZVUOUWOVUDVUPVUIVUQUWOVUDVUEV
      UPUWOVUCVUFVUGXQAVUEVUPTUWNAVUEVUOUVJSZVUPAVUERUVKSZVUTRBUVKLXCAUUJUYQVVA
      VUTTUUMYBYMYSRUVJFXDVMXFAVUOYSUGZVUTVUPTAUUJUYQVVBUUMYBYMYSRFVLVMZVUOYSVS
      XGWFYDYAYDUWOVUIVUJVUQUWOVUHVUKVULXQAVUJVUQTUWNAVUJVUOUWESZVUQAVUJRUWFSZV
      VDRCUWFMXCAUUJUYQVVEVVDTUUMYBYMYSRUWEFXDVMXFAVVBVVDVUQTVVCVUOYSWPXGWFYDYA
      YDXIUWOUYQUWNVUSVUNTYBUYBUAUBRUWMYMYMUUTVUNUVAUUPRTVUMXMUURVUDUUSVUIUUPRU
      UQUWMGXKUUPRUUQUWMHXKXIUYDVUDVUIXNXLYEUWOVVBVUOVURTAVVBUWNVVCYAVUOYQYRXOW
      FXPYFYGFYOYJYHYI $.
  $}

  ${
    $d f g h R $.  $d f g h S $.
    $( The topological product of two simply connected spaces is simply
       connected.  (Contributed by Mario Carneiro, 12-Feb-2015.) $)
    txsconn $p |- ( ( R e. SConn /\ S e. SConn ) -> ( R tX S ) e. SConn ) $=
      ( vf vg vh wcel wa co cc0 cfv c1 wceq cxp cii ccn wex ctopon eqid syl2anc
      sylib csconn ctx cpconn cv cicc csn cphtpc wbr wi wral sconnpconn txpconn
      syl2an c1st cuni cres ccom cphtpy c2nd c0 wne simpll simprl ctop sconntop
      w3a ad2antrr toptopon ad2antlr tx1cn simprr fveq2d wf iitopon a1i txtopon
      cnco cnf2 syl3anc 0elunit sylancl 1elunit 3eqtr4d sconnpht isphtpc simp3d
      fvco3 n0 simplr tx2cn exdistrv adantr txsconnlem ex biimtrrid mp2and expr
      exlimdvv ralrimiva issconn sylanbrc ) AUAFZBUAFZGZABUBHZUCFZICUDZJZKXGJZL
      ZXGIKUEHZXHUFMXEUGJUHZUIZCNXEOHZUJXEUAFXBAUCFBUCFXFXCAUKBUKABULUMXDXMCXNX
      DXGXNFZXJXLXDXOXJGZGZDUDZUNAUOZBUOZMZUPZXGUQZXKIYCJZUFMZAURJHZFZDPZEUDZUS
      YAUPZXGUQZXKIYKJZUFMZBURJHZFZEPZXLXQYFUTVAZYHXQYCNAOHZFZYEYRFZYQXQYCYEAUG
      JUHZYSYTYQVFXQXBYSYDKYCJZLUUAXBXCXPVBXQXOYBXEAOHFZYSXDXOXJVCZXQAXSQJFZBXT
      QJFZUUCXQAVDFZUUEXBUUGXCXPAVEVGZAXSXSRVHTZXQBVDFZUUFXCUUJXBXPBVEVIZBXTXTR
      VHTZABXSXTVJSXGYBNXEAVQSXQXHYBJZXIYBJZYDUUBXQXHXIYBXDXOXJVKZVLXQXKYAXGVMZ
      IXKFZYDUUMLXQNXKQJFZXEYAQJFZXOUUPUURXQVNVOXQUUEUUFUUSUUIUULABXSXTVPSUUDXG
      NXEXKYAVRVSZVTXKYAIYBXGWGWAXQUUPKXKFZUUBUUNLUUTWBXKYAKYBXGWGWAWCYCAWDVSYC
      YEAWETWFDYFWHTXQYNUTVAZYPXQYKNBOHZFZYMUVCFZUVBXQYKYMBUGJUHZUVDUVEUVBVFXQX
      CUVDYLKYKJZLUVFXBXCXPWIXQXOYJXEBOHFZUVDUUDXQUUEUUFUVHUUIUULABXSXTWJSXGYJN
      XEBVQSXQXHYJJZXIYJJZYLUVGXQXHXIYJUUOVLXQUUPUUQYLUVILUUTVTXKYAIYJXGWGWAXQU
      UPUVAUVGUVJLUUTWBXKYAKYJXGWGWAWCYKBWDVSYKYMBWETWFEYNWHTYHYPGYGYOGZEPDPXQX
      LYGYODEWKXQUVKXLDEXQUVKXLXQUVKGYCYKABXGXRYIXQUUGUVKUUHWLXQUUJUVKUUKWLXQXO
      UVKUUDWLYCRYKRXQYGYOVCXQYGYOVKWMWNWRWOWPWQWSCXEWTXA $.
  $}

  ${
    $d t z u v J $.  $d f s x y z K $.  $d f s t x y z ph $.  $d t x z S $.
    $d x y u v $.
    cvxpconn.1 $e |- ( ph -> S C_ CC ) $.
    cvxpconn.2 $e |- ( ( ph /\ ( x e. S /\ y e. S /\ t e. ( 0 [,] 1 ) ) ) ->
      ( ( t x. x ) + ( ( 1 - t ) x. y ) ) e. S ) $.
    cvxpconn.3 $e |- J = ( TopOpen ` CCfld ) $.
    cvxpconn.4 $e |- K = ( J |`t S ) $.
    $( A convex subset of the complex numbers is path-connected.  (Contributed
       by Mario Carneiro, 12-Feb-2015.)  Avoid ~ ax-mulf .  (Revised by GG,
       19-Apr-2025.) $)
    cvxpconn $p |- ( ph -> K e. PConn ) $=
      ( wcel cc0 wceq c1 co cc cmul caddc a1i vf vu vv ctop cv cfv cii ccn wrex
      wa cuni wral cpconn crest cvv cnfldtop cnex ssexg sylancl resttop sylancr
      wss eqeltrid cicc cmin cmpt dfii3 ctopon cnfldtopon cnmptid sselda cnmptc
      unitsscn cmpo ctx mpomulcn oveq12 cnmpt12 adantrl ccncf cncfcn1 eleqtrrdi
      1cnd subcncf eleqtrdi adantr simprl sseldd addcn cnmpt12f cnmpt1res wb wi
      3exp2 com23 imp42 fmpttd cnrest2 mp3an2i mpbid oveq2i 0elunit oveq1 oveq2
      crn frnd 1m0e1 eqtrdi oveq1d oveq12d eqid ovex fvmpt ax-mp mul02d mullidd
      addlidd eqtrd eqtrid 1elunit 1m1e0 addridd eqeq1d anbi12d rspcev syl12anc
      fveq1 ralrimivva resttopon toponuni raleqdv raleqbidv ispconn sylanbrc
      syl ) AGUDLMUAUEZUFZCUEZNZOYPUFZBUEZNZUJZUAUGGUHPZUIZBGUKZULZCUUFULZGUMLA
      GFEUNPZUDKAFUDLEUOLZUUIUDLFJUPAEQVBZQUOLUUJHUQEQUOURUSEFUOUTVAVCAUUEBEULZ
      CEULUUHAUUECBEEAYRELZUUAELZUJZUJZDMOVDPZDUEZUUARPZOUURVEPZYRRPZSPZVFZUUDL
      MUVCUFZYRNZOUVCUFZUUANZUUEUUPUVCUGUUIUHPZUUDUUPUVCUGFUHPLZUVCUVHLZUUPDUVB
      FUGFQUUQFJVGFQVHUFLZUUPFJVIZTZUUQQVBUUPVMTUUPDUUSUVASFFFFQUVMAUUNDQUUSVFF
      FUHPZLUUMAUUNUJZDUBUCUURUUAUBUEZUCUEZRPZUUSFFFFQQQUVKUVOUVLTZUVODFQUVSVJU
      VODUUAFFQQUVSUVSAEQUUAHVKZVLUVSUVSUBUCQQUVRVNFFVOPFUHPZLZUVOUBUCFJVPZTUVP
      UURUVQUUARVQVRVSUUPDUBUCUUTYRUVRUVAFFFFQQQUVMADQUUTVFZUVNLUUOAUWDQQVTPZUV
      NADOUURQADQOVFUVNUWEADOFFQQUVKAUVLTZUWFAWCVLFJWAZWBADQUURVFUVNUWEADFQUWFV
      JUWGWBWDUWGWEWFUUPDYRFFQQUVMUVMUUPEQYRAUUKUUOHWFZAUUMUUNWGWHZVLUVMUVMUWBU
      UPUWCTUVPUUTUVQYRRVQVRSUWALUUPFJWITWJWKUVKUUPUVCXEEVBUUKUVIUVJWLUVLUUPUUQ
      EUVCUUPDUUQUVBEAUUMUUNUURUUQLZUVBELZAUUNUUMUWJUWKWMAUUNUUMUWJUWKIWNWOWPWQ
      XFUWHEUVCUGFQWRWSWTGUUIUGUHKXAWBUUPUVDMUUARPZOYRRPZSPZYRMUUQLUVDUWNNXBDMU
      VBUWNUUQUVCUURMNZUUSUWLUVAUWMSUURMUUARXCUWOUUTOYRRUWOUUTOMVEPOUURMOVEXDXG
      XHXIXJUVCXKZUWLUWMSXLXMXNUUPUWNMYRSPYRUUPUWLMUWMYRSUUPUUAAUUNUUAQLUUMUVTV
      SZXOUUPYRUWIXPXJUUPYRUWIXQXRXSUUPUVFOUUARPZMYRRPZSPZUUAOUUQLUVFUWTNXTDOUV
      BUWTUUQUVCUURONZUUSUWRUVAUWSSUUROUUARXCUXAUUTMYRRUXAUUTOOVEPMUUROOVEXDYAX
      HXIXJUWPUWRUWSSXLXMXNUUPUWTUUAMSPUUAUUPUWRUUAUWSMSUUPUUAUWQXPUUPYRUWIXOXJ
      UUPUUAUWQYBXRXSUUCUVEUVGUJUAUVCUUDYPUVCNZYSUVEUUBUVGUXBYQUVDYRMYPUVCYGYCU
      XBYTUVFUUAOYPUVCYGYCYDYEYFYHAUULUUGCEUUFAGEVHUFZLEUUFNAGUUIUXCKAUVKUUKUUI
      UXCLUVLHEFQYIVAVCEGYJYOZAUUEBEUUFUXDYKYLWTCBUAGUUFUUFXKYMYN $.
    $( $j usage 'cvxpconn' avoids 'ax-mulf'; $)

    $d t u v K $.  $d y S $.  $d f u v $.  $d ph u v $.
    $( A convex subset of the complex numbers is simply connected.
       (Contributed by Mario Carneiro, 12-Feb-2015.)  Avoid ~ ax-mulf .
       (Revised by GG, 19-Apr-2025.) $)
    cvxsconn $p |- ( ph -> K e. SConn ) $=
      ( vz wcel cc0 c1 co cii cmul caddc cc vf vs vu vv cpconn cv cfv wceq cicc
      csn cxp cphtpc wbr wi ccn wral csconn cvxpconn wa cphtpy c0 simprl ctopon
      wne cuni w3a ctop pconntop syl adantr toptopon2 sylib wf eqid cnf 0elunit
      iiuni ffvelcdm sylancl pcoptcl syl2anc simp1d cmin cmpo ctx crest iitopon
      a1i cnfldtopon wss unitsscn cnmpt2nd cnmpt2res resttopon sylancr eqeltrid
      dfii3 toponuni eleqtrrd sseldd cnmpt2c mpomulcn cnmpt22 cnmpt22f cnmpt1st
      oveq12 ax-1cn subcn cnfldtop cnrest2r oveq2i eleqtrdi sselid cnmpt21f crn
      ax-mp addcn oveq2 oveq1d eleq1d oveq2d 3exp2 imp42 an32s ralrimivva simpr
      weq eqtrdi simpl fveq2d oveq12d ovex ovmpoa mul02d mullidd 3eqtrd 1elunit
      wb 3eqtr3d eqtrd ad2ant2rl ffvelcdmd rspc2dv fmpo cnrest2 mpbid eleqtrrdi
      frnd mp3an2i 1m0e1 toponunii ffvelcdmda addlidd 1m1e0 addridd fvex adantl
      eqtr4d pncan3 subcl adddird simplrr isphtpy2d ne0d isphtpc syl3anbrc expr
      fvconst2 ralrimiva issconn sylanbrc ) AGUEMZNUAUFZUGZOUVMUGZUHZUVMNOUIPZU
      VNUJUKZGULUGUMZUNZUAQGUOPZUPGUQMABCDEFGHIJKURZAUVTUAUWAAUVMUWAMZUVPUVSAUW
      CUVPUSZUSZUWCUVRUWAMZUVMUVRGUTUGPZVAVDUVSAUWCUVPVBZUWEUWFNUVRUGUVNUHZOUVR
      UGUVNUHZUWEGGVEZVCUGMZUVNUWKMZUWFUWIUWJVFUWEGVGMZUWLAUWNUWDAUVLUWNUWBGVHV
      IVJGVKVLUWEUVQUWKUVMVMZNUVQMZUWMUWEUWCUWOUWHUVMQGUVQUWKVQUWKVNVOVIZVPUVQU
      WKNUVMVRVSZUVRGUWKUVNUVRVNVTWAWBZUWEUWGLDUVQUVQDUFZUVNRPZOUWTWCPZLUFZUVMU
      GZRPZSPZWDZUWEUVMUVRUXGGUBUWHUWSUWEUXGQQWEPZFEWFPZUOPZUXHGUOPUWEUXGUXHFUO
      PMZUXGUXJMZUWELDUXAUXESQQFFFUVQUVQQUVQVCUGMUWEWGWHZUXMUWELDUCUDUWTUVNUCUF
      ZUDUFZRPZUXAQQFFFTUVQUVQTUXMUXMUWELDUWTFQFFQUVQTUVQTFJWQZFTVCUGMZUWEFJWIZ
      WHZUVQTWJUWEWKWHZUXQUXTUYAUWELDFFTTUXTUXTWLWMZUWELDUVNQQFUVQUVQTUXMUXMUXT
      UWEETUVNAETWJZUWDHVJZUWEUVNUWKEUWRAEUWKUHZUWDAGEVCUGZMUYEAGUXIUYFKAUXRUYC
      UXIUYFMUXSHEFTWNWOWPEGWRVIVJZWSZWTZXAUXTUXTUCUDTTUXPWDFFWEPFUOPZMUWEUCUDF
      JXBWHZUXNUWTUXOUVNRXFXCUWELDUCUDUXBUXDUXPUXEQQFFFTUVQUVQTUXMUXMUWELDOUWTW
      CQQFFFUVQUVQUXMUXMUWELDOQQFUVQUVQTUXMUXMUXTOTMZUWEXGWHXAUYBWCUYJMUWEFJXHW
      HXDUWELDUXCUVMQQQFUVQUVQUXMUXMUWELDQQUVQUVQUXMUXMXEUWEQUXIUOPZQFUOPZUVMFV
      GMUYMUYNWJFJXIEQFXJXPUWEUVMUWAUYMUWHGUXIQUOKXKXLXMZXNUXTUXTUYKUXNUXBUXOUX
      DRXFXCSUYJMUWEFJXQWHXDUXRUWEUXGXOEWJUYCUXKUXLYRUXSUWEUVQUVQUKZEUXGUWEUXFE
      MZDUVQUPLUVQUPUYPEUXGVMUWEUYQLDUVQUVQUWEUXCUVQMZUWTUVQMZUSZUSZUWTBUFZRPZU
      XBCUFZRPZSPZEMZUYQUXAVUESPZEMBCUVNUXDEEVUBUVNUHZVUFVUHEVUIVUCUXAVUESVUBUV
      NUWTRXRXSXTVUDUXDUHZVUHUXFEVUJVUEUXEUXASVUDUXDUXBRXRYAXTAUYSVUGCEUPBEUPUW
      DUYRAUYSUSVUGBCEEAVUBEMZVUDEMZUSUYSVUGAVUKVULUYSVUGAVUKVULUYSVUGIYBYCYDYE
      UUAUWEUVNEMUYTUYHVJVUAUXDUWKEVUAUVQUWKUXCUVMUWEUWOUYTUWQVJUWEUYRUYSVBUUBU
      WEUYEUYTUYGVJWSUUCYELDUVQUVQUXFEUXGUXGVNZUUDVLUUHUYDEUXGUXHFTUUEUUIUUFGUX
      IUXHUOKXKUUGUWEUBUFZUVQMZUSZVUNNUXGPZNUVNRPZOVUNUVMUGZRPZSPZNVUSSPVUSVUPV
      UOUWPVUQVVAUHUWEVUOYFZVPLDVUNNUVQUVQUXFVVAUXGLUBYGZUWTNUHZUSZUXAVURUXEVUT
      SVVEUWTNUVNRVVCVVDYFZXSVVEUXBOUXDVUSRVVEUXBONWCPOVVEUWTNOWCVVFYAUUJYHVVEU
      XCVUNUVMVVCVVDYIYJYKYKVUMVURVUTSYLYMVSVUPVURNVUTVUSSVUPUVNUWEUVNTMVUOUYIV
      JZYNVUPVUSUWEUVQTVUNUVMUWEUVMUYNMUVQTUVMVMUYOUVMQFUVQTVQTFUXSUUKVOVIUULZY
      OYKVUPVUSVVHUUMYPVUPVUNOUXGPZOUVNRPZNVUSRPZSPZUVNNSPZVUNUVRUGZVUPVUOOUVQM
      ZVVIVVLUHVVBYQLDVUNOUVQUVQUXFVVLUXGVVCUWTOUHZUSZUXAVVJUXEVVKSVVQUWTOUVNRV
      VCVVPYFZXSVVQUXBNUXDVUSRVVQUXBOOWCPNVVQUWTOOWCVVRYAUUNYHVVQUXCVUNUVMVVCVV
      PYIYJYKYKVUMVVJVVKSYLYMVSVUPVVJUVNVVKNSVUPUVNVVGYOZVUPVUSVVHYNYKVUPVVMUVN
      VVNVUPUVNVVGUUOVUOVVNUVNUHUWEUVQUVNVUNNUVMUUPUVHUUQUURYPVUPNVUNUXGPZVUNUV
      NRPZOVUNWCPZUVNRPZSPZUVNVUPUWPVUOVVTVWDUHVPVVBLDNVUNUVQUVQUXFVWDUXGUXCNUH
      ZDUBYGZUSZUXAVWAUXEVWCSVWGUWTVUNUVNRVWEVWFYFZXSVWGUXBVWBUXDUVNRVWGUWTVUNO
      WCVWHYAVWGUXCNUVMVWEVWFYIYJYKYKVUMVWAVWCSYLYMWOVUPVUNVWBSPZUVNRPVVJVWDUVN
      VUPVWIOUVNRVUPVUNTMZUYLVWIOUHVUPUVQTVUNWKVVBXMZXGVUNOUUSVSXSVUPVUNVWBUVNV
      WKVUPUYLVWJVWBTMXGVWKOVUNUUTWOVVGUVAVVSYSZYTVUPOVUNUXGPZVWAVWBUVORPZSPZUV
      OVUPVVOVUOVWMVWOUHYQVVBLDOVUNUVQUVQUXFVWOUXGUXCOUHZVWFUSZUXAVWAUXEVWNSVWQ
      UWTVUNUVNRVWPVWFYFZXSVWQUXBVWBUXDUVORVWQUWTVUNOWCVWRYAVWQUXCOUVMVWPVWFYIY
      JYKYKVUMVWAVWNSYLYMWOVUPVWDUVNVWOUVOVWLVUPVWCVWNVWASVUPUVNUVOVWBRAUWCUVPV
      UOUVBZYAYAVWSYSYTUVCUVDUVMUVRGUVEUVFUVGUVIUAGUVJUVK $.
    $( $j usage 'cvxsconn' avoids 'ax-mulf'; $)
  $}

  ${
    $d t J $.  $d t x y K $.  $d t x y P $.  $d t x y R $.  $d t x y S $.
    blsconn.j $e |- J = ( TopOpen ` CCfld ) $.
    blsconn.s $e |- S = ( P ( ball ` ( abs o. - ) ) R ) $.
    blsconn.k $e |- K = ( J |`t S ) $.
    $( An open ball in the complex numbers is simply connected.  (Contributed
       by Mario Carneiro, 12-Feb-2015.) $)
    blsconn $p |- ( ( P e. CC /\ R e. RR* ) -> K e. SConn ) $=
      ( vx vy vt cc wcel cxr wa cabs cmin ccom cfv cv cbl co cxmet cnxmet blssm
      wss mp3an1 eqsstrid blcvx cvxsconn ) ALMZBNMZOZIJKCDEUMCABPQRZUASUBZLGUNL
      UCSMUKULUOLUFUDUNABLUEUGUHITJTABCKTGUIFHUJ $.
  $}

  ${
    $d r u x y J $.
    cnllysconn.j $e |- J = ( TopOpen ` CCfld ) $.
    $( The topology of the complex numbers is locally simply connected.
       (Contributed by Mario Carneiro, 2-Mar-2015.) $)
    cnllysconn $p |- J e. Locally SConn $=
      ( vy vu vx vr csconn wcel cv crest co wa wrex wral cfv wss crp cc syl3anc
      cnxmet clly ctop cpw cin cnfldtop cabs cmin cxmet cnfldtopn mopni2 mp3an1
      ccom cbl cxr a1i ctopon cnfldtopon simpll toponss sylancr simplr ad2antrl
      sseldd rpxr blopn simprr elpw2 sylibr elind simprl blcntr blsconn syl2anc
      vex eqid eleq2 oveq2 eleq1d anbi12d rspcev syl12anc rexlimddv rgen2 islly
      wceq mpbir2an ) AGUAHAUBHCIZDIZHZAWHJKZGHZLZDAEIZUCZUDZMZCWMNEANABUEWPECA
      WMWMAHZWGWMHZLZWGFIZUFUGULZUMOKZWMPZWPFQXARUHOHZWQWRXCFQMTFWMXAWGARABUIZU
      JUKWSWTQHZXCLZLZXBWOHWGXBHZAXBJKZGHZWPXHAWNXBXHXDWGRHZWTUNHZXBAHXDXHTUOZX
      HWMRWGXHARUPOHWQWMRPABUQWQWRXGURWMARUSUTWQWRXGVAVCZXFXMWSXCWTVDVBZXAWGWTA
      RXEVESXHXCXBWNHWSXFXCVFXBWMEVNVGVHVIXHXDXLXFXIXNXOWSXFXCVJXAWGWTRVKSXHXLX
      MXKXOXPWGWTXBAXJBXBVOXJVOVLVMWLXIXKLDXBWOWHXBWEZWIXIWKXKWHXBWGVPXQWJXJGWH
      XBAJVQVRVSVTWAWBWCECDGAWDWF $.
  $}

  ${
    $d s t w x y z A $.  $d s t w x y z J $.
    resconn.1 $e |- J = ( ( topGen ` ran (,) ) |`t A ) $.
    $( A subset of ` RR ` is simply connected iff it is connected.
       (Contributed by Mario Carneiro, 9-Mar-2015.) $)
    resconn $p |- ( A C_ RR -> ( J e. SConn <-> J e. Conn ) ) $=
      ( vx vy vt cr wcel wa co adantr cc cv c1 cmul caddc wral oveq2 cle wbr vz
      vw vs wss csconn cconn cpconn sconnpconn pconnconn syl ccnfld ctopn crest
      cfv wceq cioo crn ctg eqid rerest eqtr4di simpl ax-resscn sstrdi cc0 cicc
      w3a cmin df-3an weq oveqan12d eleq1d ralbidv unitssre sstri sselid simpr2
      simpr sseldd mulcld ax-1cn subcl sylancr simpr1 nncan oveq1d oveq2d iirev
      addcomd eqtr4d adantl eleq1i reconn bitrid biimpa r19.21bi anasss simplll
      3adantr3 remulcld resubcl readdcld pncan3 sylancl adddird mullidd 3eqtr3d
      1re recnd elicc01 sylib simp3d wb subge0 mpbird simplr3 lemul2ad leadd2dd
      eqbrtrrd simp2d leadd1dd breqtrd elicc2 syl2anc mpbir3and ralrimiva oveq1
      oveq12d rspcv sylc eqeltrd cbvralvw wloglei sylan2b cvxsconn eqeltrrd ex
      impbid2 ) AGUDZBUEHZBUFHZYTBUGHUUABUHBUIUJYSUUAYTYSUUAIZUKULUNZAUMJZBUEYS
      UUDBUOUUAYSUUDUPUQURUNZAUMJZBAUUEUUCUUCUSZUUEUSUTCVAKUUBDEFAUUCUUDUUBAGLY
      SUUAVBZVCVDZDMZAHZEMZAHZFMZVENVFJZHZVGUUBUUKUUMIZUUPIUUNUUJOJZNUUNVHJZUUL
      OJZPJZAHZUUKUUMUUPVIUUBUUQUUPUVBUUBUUQIUVBFUUOUUBUUNUAMZOJZUUSUBMZOJZPJZA
      HZFUUOQUVBFUUOQZUUNUULOJZUUSUUJOJZPJZAHZFUUOQZDEUAUBAUADVJZUBEVJZIZUVHUVB
      FUUOUVQUVGUVAAUVOUVPUVDUURUVFUUTPUVCUUJUUNORUVEUULUUSORVKVLVMUAEVJZUBDVJZ
      IZUVHUVMFUUOUVTUVGUVLAUVRUVSUVDUVJUVFUVKPUVCUULUUNORUVEUUJUUSORVKVLVMUUHU
      UBUUKUUMUUJUULSTZVGZIZUCMZUULOJZNUWDVHJZUUJOJZPJZAHZUCUUOQUVNUWCUWIUCUUOU
      WCUWDUUOHZIZUWHUWGNUWFVHJZUULOJZPJZAUWKUWHUWGUWEPJUWNUWKUWEUWGUWKUWDUULUW
      KUUOLUWDUUOGLVNVCVOUWCUWJVRVPZUWCUULLHZUWJUWCALUULUUBALUDUWBUUIKZUUBUUKUU
      MUWAVQZVSZKVTUWKUWFUUJUWKNLHZUWDLHZUWFLHWAUWONUWDWBWCUWCUUJLHZUWJUWCALUUJ
      UWQUUBUUKUUMUWAWDZVSZKVTWIUWKUWMUWEUWGPUWKUWLUWDUULOUWKUWTUXAUWLUWDUOWAUW
      ONUWDWEWCWFWGWJUWKUWFUUOHZUVIUWNAHZUWJUXEUWCUWDWHWKUWCUVIUWJUWCUVBFUUOUWC
      UUPIZUUJUULVFJZAUVAUWCUXHAUDZUUPUUBUUKUUMUXIUWAUUBUUKUUMUXIUUBUUKIUXIEAUU
      BUXIEAQZDAYSUUAUXJDAQZUUAUUFUFHYSUXKBUUFUFCWLDEAWMWNWOWPWPWQWSKUXGUVAUXHH
      ZUVAGHZUUJUVASTZUVAUULSTZUXGUURUUTUXGUUNUUJUXGUUOGUUNVNUWCUUPVRZVPZUXGAGU
      UJYSUUAUWBUUPWRZUWCUUKUUPUXCKVSZWTZUXGUUSUULUXGNGHZUUNGHZUUSGHXHUXQNUUNXA
      WCZUXGAGUULUXRUWCUUMUUPUWRKVSZWTZXBUXGUURUVKPJZUUJUVASUXGUUNUUSPJZUUJOJNU
      UJOJUYFUUJUXGUYGNUUJOUXGUUNLHUWTUYGNUOUXGUUNUXQXIZWAUUNNXCXDZWFUXGUUNUUSU
      UJUYHUXGUUSUYCXIZUWCUXBUUPUXDKZXEUXGUUJUYKXFXGUXGUVKUUTUURUXGUUSUUJUYCUXS
      WTUYEUXTUXGUUJUULUUSUXSUYDUYCUXGVEUUSSTZUUNNSTZUXGUYBVEUUNSTZUYMUXGUUPUYB
      UYNUYMVGUXPUUNXJXKZXLUXGUYAUYBUYLUYMXMXHUXQNUUNXNWCXOUUKUUMUWAUUBUUPXPZXQ
      XRXSUXGUVAUVJUUTPJZUULSUXGUURUVJUUTUXTUXGUUNUULUXQUYDWTUYEUXGUUJUULUUNUXS
      UYDUXQUXGUYBUYNUYMUYOXTUYPXQYAUXGUYGUULOJNUULOJUYQUULUXGUYGNUULOUYIWFUXGU
      UNUUSUULUYHUYJUWCUWPUUPUWSKZXEUXGUULUYRXFXGYBUXGUUJGHUULGHUXLUXMUXNUXOVGX
      MUXSUYDUUJUULUVAYCYDYEVSYFZKUVBUXFFUWFUUOUUNUWFUOZUVAUWNAUYTUURUWGUUTUWMP
      UUNUWFUUJOYGUYTUUSUWLUULOUUNUWFNVHRWFYHVLYIYJYKYFUWIUVMUCFUUOUCFVJZUWHUVL
      AVUAUWEUVJUWGUVKPUWDUUNUULOYGVUAUWFUUSUUJOUWDUUNNVHRWFYHVLYLXKUYSYMWPWQYN
      UUGUUDUSYOYPYQYR $.
  $}

  ${
    $d x y A $.  $d x y B $.
    $( An open interval is simply connected.  (Contributed by Mario Carneiro,
       9-Mar-2015.) $)
    ioosconn $p |- ( ( topGen ` ran (,) ) |`t ( A (,) B ) ) e. SConn $=
      ( vx vy cv cicc co cioo wss wral crn ctg cfv crest csconn iccssioo2 rgen2
      wcel cr wb ioossre cconn eqid resconn reconn bitr2d ax-mp mpbi ) CEZDEZFG
      ABHGZIZDUKJCUKJZHKLMUKNGZORZULCDUKUKABUIUJPQUKSIZUMUOTABUAUPUOUNUBRUMUKUN
      UNUCUDCDUKUEUFUGUH $.
  $}

  $( A closed interval is simply connected.  (Contributed by Mario Carneiro,
     9-Mar-2015.) $)
  iccsconn $p |- ( ( A e. RR /\ B e. RR ) ->
                         ( ( topGen ` ran (,) ) |`t ( A [,] B ) ) e. SConn ) $=
    ( cr wcel wa cioo crn ctg cfv cicc co crest csconn cconn iccconn wb iccssre
    wss eqid resconn syl mpbird ) ACDBCDEZFGHIABJKZLKZMDZUENDZABOUCUDCRUFUGPABQ
    UDUEUESTUAUB $.

  $( The real numbers are simply connected.  (Contributed by Mario Carneiro,
     9-Mar-2015.) $)
  retopsconn $p |- ( topGen ` ran (,) ) e. SConn $=
    ( cioo crn ctg cfv cmnf cpnf co crest csconn ctop wcel wceq retop cr ioomax
    cuni uniretop eqtri restid ax-mp ioosconn eqeltrri ) ABCDZEFAGZHGZUCIUCJKUE
    UCLMUCJUDUDNUCPOQRSTEFUAUB $.

  ${
    $d a b u v x y z A $.  $d a b u v x y z B $.
    $( A closed interval is locally simply connected.  (Contributed by Mario
       Carneiro, 10-Mar-2015.) $)
    iccllysconn $p |- ( ( A e. RR /\ B e. RR ) ->
                 ( ( topGen ` ran (,) ) |`t ( A [,] B ) ) e. Locally SConn ) $=
      ( vz vx vy vu vv cr wcel wa cv co wss cioo crest csconn wrex wral cxr wb
      va vb cicc cin crn ctg cfv w3a clly simprl simprr sselid tg2 syl2anc wceq
      inss1 wi cxp cpw wf wfn ioof ffn ovelrn mp2b simprrr sstrid ineq1d oveq2d
      simprrl ioossre cconn eqid resconn reconn bitrd ax-mp mpbi ssralv ralimdv
      ioosconn syld mp1i inss2 iccconn iccssre syl mpbid ad2antrr mpsyl 2ralbii
      ssin r19.26-2 bitr3i sylanbrc sstri eqeltrd 3jca exp32 rexlimdvw biimtrid
      sylibr reximdvai ctb retopbas bastg ssrexv syl6 mpd ralrimivva ctop retop
      cvv ovex subislly mp2an ) AHIBHIJZCKZABUCLZUDZDKZMZEKZXRIZNUEZUFUGZXTOLZP
      IZUHZCYFQZEYAXSUDZRDYFRZYFXSOLZPUIIZXQYJDEYFYKXQYAYFIZYCYKIZJZJZYDXRYAMZJ
      ZCYEQZYJYRYOYCYAIUUAXQYOYPUJYRYKYAYCYAXSUPXQYOYPUKULCYAYEYCUMUNYRUUAYICYE
      QZYJYRYTYICYEXRYEIZXRUAKZUBKZNLZUOZUBSQZUASQZYRYTYIUQZSSURZHUSZNUTNUUKVAU
      UCUUITVBUUKUULNVCUAUBSSXRNVDVEYRUUHUUJUASYRUUGUUJUBSYRUUGYTYIYRUUGYTJZJZY
      BYDYHUUNXTXRYAXRXSUPYRUUGYDYSVFVGYRUUGYDYSVJUUNYGYFUUFXSUDZOLZPUUNXTUUOYF
      OUUNXRUUFXSYRUUGYTUJVHVIUUNFKGKUCLZUUOMZGUUORFUUORZUUPPIZUUNUUQUUFMZGUUOR
      ZFUUORZUUQXSMZGUUORZFUUORZUUSUVAGUUFRZFUUFRZUVCUUNYFUUFOLZPIZUVHUUDUUEWAU
      UFHMZUVJUVHTUUDUUEVKZUVKUVJUVIVLIUVHUUFUVIUVIVMVNFGUUFVOVPVQVRUUOUUFMZUVH
      UVCUQUUFXSUPZUVMUVHUVBFUUFRUVCUVMUVGUVBFUUFUVAGUUOUUFVSVTUVBFUUOUUFVSWBVQ
      WCUUOXSMZUUNUVDGXSRZFXSRZUVFUUFXSWDXQUVQYQUUMXQYMVLIZUVQABWEXQXSHMUVRUVQT
      ABWFFGXSVOWGWHWIUVOUVQUVEFXSRUVFUVOUVPUVEFXSUVDGUUOXSVSVTUVEFUUOXSVSWBWJU
      USUVAUVDJZGUUORFUUORUVCUVFJUVSUURFGUUOUUOUUQUUFXSWLWKUVAUVDFGUUOUUOWMWNWO
      UUOHMZUUTUUSTUUOUUFHUVNUVLWPUVTUUTUUPVLIUUSUUOUUPUUPVMVNFGUUOVOVPVQXBWQWR
      WSWTWTXAXCYEXDIYEYFMUUBYJUQXEYEXDXFYICYEYFXGVEXHXIXJYFXKIXSXMIYNYLTXLABUC
      XNDECPXSYFXMXOXPXB $.

    $( The real numbers are locally simply connected.  (Contributed by Mario
       Carneiro, 10-Mar-2015.) $)
    rellysconn $p |- ( topGen ` ran (,) ) e. Locally SConn $=
      ( vy vz vx va vb cioo csconn wcel wel cv crest co wa cpw wrex wss ctb cxr
      wral rexlimivw crn ctg cfv clly cin retop tg2 retopbas bastg ax-mp simprl
      ctop sselid simprrr velpw sylibr elind simprrl wceq cxp cr wf wfn wb ioof
      ffn ovelrn mp2b oveq2 ioosconn eqeltrdi sylbi ad2antrl jca32 reximdv2 mpd
      ex rgen2 islly mpbir2an ) FUAZUBUCZGUDHWBULHABIZWBBJZKLZGHZMZBWBCJZNZUEZO
      ZAWHSCWBSUFWKCAWBWHWHWBHACIMZWCWDWHPZMZBWAOWKBWHWAAJUGWLWNWGBWAWJWLWDWAHZ
      WNMZWDWJHZWGMWLWPMZWQWCWFWRWBWIWDWRWAWBWDWAQHWAWBPUHWAQUIUJWLWOWNUKUMWRWM
      WDWIHWLWOWCWMUNBWHUOUPUQWLWOWCWMURWOWFWLWNWOWDDJZEJZFLZUSZEROZDROZWFRRUTZ
      VANZFVBFXEVCWOXDVDVEXEXFFVFDERRWDFVGVHXCWFDRXBWFERXBWEWBXAKLGWDXAWBKVIWSW
      TVJVKTTVLVMVNVQVOVPVRCABGWBVSVT $.
  $}

  $( The unit interval is simply connected.  (Contributed by Mario Carneiro,
     9-Mar-2015.) $)
  iisconn $p |- II e. SConn $=
    ( cii cioo crn ctg cfv cc0 c1 cicc crest csconn dfii2 wcel 0re 1re iccsconn
    co cr mp2an eqeltri ) ABCDEFGHPIPZJKFQLGQLTJLMNFGORS $.

  $( The unit interval is locally simply connected.  (Contributed by Mario
     Carneiro, 10-Mar-2015.) $)
  iillysconn $p |- II e. Locally SConn $=
    ( cii cioo crn ctg cfv cc0 c1 cicc crest csconn clly dfii2 wcel iccllysconn
    co cr 0re 1re mp2an eqeltri ) ABCDEFGHOIOZJKZLFPMGPMUAUBMQRFGNST $.

  $( The unit interval is locally connected.  (Contributed by Mario Carneiro,
     6-Jul-2015.) $)
  iinllyconn $p |- II e. N-Locally Conn $=
    ( vx csconn cnlly cconn cii wss wcel cpconn sconnpconn pconnconn syl nllyss
    cv ssriv ax-mp clly llyssnlly iillysconn sselii ) BCZDCZEBDFTUAFABDAMZBGUBH
    GUBDGUBIUBJKNBDLOBPTEBQRSS $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Covering maps
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c CovMap $.

  $( Extend class notation with the class of covering maps. $)
  ccvm $a class CovMap $.

  ${
    $d c j f x k s u v $.
    $( Define the class of covering maps on two topological spaces.  A function
       ` f : c --> j ` is a covering map if it is continuous and for every
       point ` x ` in the target space there is a neighborhood ` k ` of ` x `
       and a decomposition ` s ` of the preimage of ` k ` as a disjoint union
       such that ` f ` is a homeomorphism of each set ` u e. s ` onto ` k ` .
       (Contributed by Mario Carneiro, 13-Feb-2015.) $)
    df-cvm $a |- CovMap = ( c e. Top , j e. Top |-> { f e. ( c Cn j ) |
      A. x e. U. j E. k e. j ( x e. k /\ E. s e. ( ~P c \ { (/) } )
       ( U. s = ( `' f " k ) /\ A. u e. s
         ( A. v e. ( s \ { u } ) ( u i^i v ) = (/) /\
           ( f |` u ) e. ( ( c |`t u ) Homeo ( j |`t k ) ) ) ) ) } ) $.

    $( Lemma for covering maps.  (Contributed by Mario Carneiro,
       13-Feb-2015.) $)
    fncvm $p |- CovMap Fn ( Top X. Top ) $=
      ( vc vj vx vk vs vf vu vv ctop cv wcel cuni wceq c0 cdif wral crest co wa
      csn ccnv cima cin cres chmeo cpw wrex crab ccvm df-cvm ovex rabex fnmpoi
      ccn ) ABIICJDJZKEJZLFJZUAUOUBMGJZHJUCNMHUPURTOPUQURUDAJZURQRBJZUOQRUERKSG
      UPPSEUSUFNTOUGSDUTUGCUTLPZFUSUTUNRZUHUICHGFBDEAUJVAFVBUSUTUNUKULUM $.
  $}

  ${
    $d a b c d f j k s u v x $.  $d a b c f j k s u x C $.  $d c f j x X $.
    $d a b c f k s u x F $.  $d a b c f j k s u x J $.
    iscvm.1 $e |- S = ( k e. J |->
      { s e. ( ~P C \ { (/) } ) | ( U. s = ( `' F " k ) /\
        A. u e. s ( A. v e. ( s \ { u } ) ( u i^i v ) = (/) /\
           ( F |` u ) e. ( ( C |`t u ) Homeo ( J |`t k ) ) ) ) } ) $.
    $( Change bound variables in the set of even coverings.  (Contributed by
       Mario Carneiro, 17-Feb-2015.) $)
    cvmscbv $p |- S = ( a e. J |->
      { b e. ( ~P C \ { (/) } ) | ( U. b = ( `' F " a ) /\
        A. c e. b ( A. d e. ( b \ { c } ) ( c i^i d ) = (/) /\
           ( F |` c ) e. ( ( C |`t c ) Homeo ( J |`t a ) ) ) ) } ) $=
      ( cv wceq c0 wral crest co wa cuni ccnv cima cin csn cdif cres chmeo wcel
      cpw crab cmpt weq unieq eqeq1d ineq2 cbvralvw sneq ineq1 raleqbidv bitrid
      difeq2d reseq2 oveq2 oveq1d eleq12d anbi12d difeq1 raleqdv anbi1d cbvrabv
      imaeq2 eqeq2d oveq2d eleq2d anbi2d ralbidv rabbidv eqtrid cbvmptv eqtri
      raleqbi1dv ) DEGHNZUAZFUBZENZUCZOZBNZANZUDZPOZAWCWIUEZUFZQZFWIUGZCWIRSZGW
      FRSZUHSZUIZTZBWCQZTZHCUJPUEUFZUKZULIGJNZUAZWEINZUCZOZKNZLNZUDZPOZLXFXKUEZ
      UFZQZFXKUGZCXKRSZGXHRSZUHSZUIZTZKXFQZTZJXDUKZULMEIGXEYFEIUMZXEXGWGOZXQXRX
      SWRUHSZUIZTZKXFQZTZJXDUKYFXCYMHJXDHJUMZWHYHXBYLYNWDXGWGWCXFUNUOXBXNLWCXOU
      FZQZYJTZKWCQYNYLXAYQBKWCBKUMZWOYPWTYJWOWIXLUDZPOZLWNQYRYPWLYTALWNALUMWKYS
      PWJXLWIUPUOUQYRYTXNLWNYOYRWMXOWCWIXKURVBYRYSXMPWIXKXLUSUOUTVAYRWPXRWSYIWI
      XKFVCYRWQXSWRUHWIXKCRVDVEVFVGUQYQYKKWCXFYNYPXQYJYNXNLYOXPWCXFXOVHVIVJWBVA
      VGVKYGYMYEJXDYGYHXJYLYDYGWGXIXGWFXHWEVLVMYGYKYCKXFYGYJYBXQYGYIYAXRYGWRXTX
      SUHWFXHGRVDVNVOVPVQVGVRVSVTWA $.

    iscvm.2 $e |- X = U. J $.
    $( The property of being a covering map.  (Contributed by Mario Carneiro,
       13-Feb-2015.) $)
    iscvm $p |- ( F e. ( C CovMap J ) <->
      ( ( C e. Top /\ J e. Top /\ F e. ( C Cn J ) ) /\ A. x e. X E. k e. J
        ( x e. k /\ ( S ` k ) =/= (/) ) ) ) $=
      ( vf ctop wcel wa co cv wrex wral vc vj ccn cfv wne w3a ccvm anass df-3an
      anbi1i cuni ccnv cima wceq cin csn cdif cres crest chmeo cpw crab elmpocl
      c0 df-cvm oveq12 simpr unieqd eqtr4di simpl pweqd difeq1d oveq1 oveqan12d
      eleq2d anbi2d ralbidv rexeqbidv raleqbidv rabeqbidv ovex rabex ovmpoa cvv
      id pwexg adantr difexg rabexg fvmpt2 syl2anr neeq1d rabn0 bitrdi rexbidva
      cnveq imaeq1d eqeq2d reseq1 eleq1d anbi12d rexbidv elrab bitr4di biadanii
      3syl bitr4d 3bitr4ri ) DNOZHNOZPZGDHUCQZOZPZARFRZOZXOEUDZVDUEZPZFHSZAITZP
      XKXMYAPZPXIXJXMUFZYAPGDHUGQZOZXKXMYAUHYCXNYAXIXJXMUIUJYEXKYBUAUBNNXPJRZUK
      ZMRZULZXOUMZUNZCRZBRUOVDUNBYFYLUPUQTZYHYLURZUARZYLUSQZUBRZXOUSQZUTQZOZPZC
      YFTZPZJYOVAZVDUPZUQZSZPZFYQSZAYQUKZTZMYOYQUCQZVBZDHUGGABCMUBFJUAVEZVCXKYE
      GXPYKYMYNDYLUSQZHXOUSQZUTQZOZPZCYFTZPZJDVAZUUEUQZSZPZFHSZAITZMXLVBZOZYBXK
      YDUVHGUAUBDHNNUUMUVHUGYODUNZYQHUNZPZUUKUVGMUULXLYODYQHUCVFUVLUUIUVFAUUJIU
      VLUUJHUKIUVLYQHUVJUVKVGZVHLVIUVLUUHUVEFYQHUVMUVLUUGUVDXPUVLUUCUVAJUUFUVCU
      VLUUDUVBUUEUVLYODUVJUVKVJVKVLUVLUUBUUTYKUVLUUAUUSCYFUVLYTUURYMUVLYSUUQYNU
      VJUVKYPUUOYRUUPUTYODYLUSVMYQHXOUSVMVNVOVPVQVPVRVPVRVSVTUUNUVGMXLDHUCWAWBW
      CVOXKYBXMXPYGGULZXOUMZUNZYMGYLURZUUQOZPZCYFTZPZJUVCSZPZFHSZAITZPUVIXKYAUW
      EXMXKXTUWDAIXKXSUWCFHXKXOHOZPZXRUWBXPUWGXRUWAJUVCVBZVDUEUWBUWGXQUWHVDUWFU
      WFUWHWDOZXQUWHUNXKUWFWEXKUVBWDOZUVCWDOUWIXIUWJXJDNWFWGUVBUUEWDWHUWAJUVCWD
      WIXFFHUWHWDEKWJWKWLUWAJUVCWMWNVPWOVQVPUVGUWEMGXLYHGUNZUVFUWDAIUWKUVEUWCFH
      UWKUVDUWBXPUWKUVAUWAJUVCUWKYKUVPUUTUVTUWKYJUVOYGUWKYIUVNXOYHGWPWQWRUWKUUS
      UVSCYFUWKUURUVRYMUWKYNUVQUUQYHGYLWSWTVPVQXAXBVPXBVQXCXDXGXEXH $.
  $}

  ${
    $d k s u v x C $.  $d k s u x F $.  $d k s u x J $.
    $( Reverse closure for a covering map.  (Contributed by Mario Carneiro,
       11-Feb-2015.) $)
    cvmtop1 $p |- ( F e. ( C CovMap J ) -> C e. Top ) $=
      ( ccvm co wcel ctop c0 wceq wa n0i cxp fncvm fndmi ndmov nsyl2 simpld ) B
      ACDEZFZAGFZCGFZSRHITUAJRBKACGDGGLDMNOPQ $.

    $( Reverse closure for a covering map.  (Contributed by Mario Carneiro,
       13-Feb-2015.) $)
    cvmtop2 $p |- ( F e. ( C CovMap J ) -> J e. Top ) $=
      ( ccvm co wcel ctop c0 wceq wa n0i cxp fncvm fndmi ndmov nsyl2 simprd ) B
      ACDEZFZAGFZCGFZSRHITUAJRBKACGDGGLDMNOPQ $.

    $( A covering map is a continuous function.  (Contributed by Mario
       Carneiro, 13-Feb-2015.) $)
    cvmcn $p |- ( F e. ( C CovMap J ) -> F e. ( C Cn J ) ) $=
      ( vx vk vs vu vv co wcel ctop cv cuni wceq c0 csn cdif wral crest wa ccvm
      ccn w3a ccnv cima cin cres chmeo cpw crab cmpt cfv wne wrex iscvm simplbi
      eqid simp3d ) BACUAIJZAKJZCKJZBACUBIJZUSUTVAVBUCDLELZJVCECFLZMBUDVCUENGLZ
      HLUFONHVDVEPQRBVEUGAVESICVCSIUHIJTGVDRTFAUIOPQUJUKZULOUMTECUNDCMZRDHGAVFE
      BCVGFVFUQVGUQUOUPUR $.
  $}

  ${
    $d a b k s t u v w x y z C $.  $d a b k s t u v w x y z F $.  $d k x y P $.
    $d a b k s t u v w x y z J $.  $d t w x y z S $.  $d k s t u v w x y z U $.
    $d s u v x z T $.  $d a b k s t u v w x y z V $.  $d v W $.  $d x y z X $.
    $d t u v w x y z A $.  $d t v w x y z B $.
    cvmcov.1 $e |- S = ( k e. J |->
      { s e. ( ~P C \ { (/) } ) | ( U. s = ( `' F " k ) /\
        A. u e. s ( A. v e. ( s \ { u } ) ( u i^i v ) = (/) /\
           ( F |` u ) e. ( ( C |`t u ) Homeo ( J |`t k ) ) ) ) } ) $.
    ${
      cvmcov.2 $e |- X = U. J $.
      $( Property of a covering map.  In order to make the covering property
         more manageable, we define here the set ` S ( k ) ` of all even
         coverings of an open set ` k ` in the range.  Then the covering
         property states that every point has a neighborhood which has an even
         covering.  (Contributed by Mario Carneiro, 13-Feb-2015.) $)
      cvmcov $p |- ( ( F e. ( C CovMap J ) /\ P e. X ) ->
        E. x e. J ( P e. x /\ ( S ` x ) =/= (/) ) ) $=
        ( co wcel wa cv c0 wrex wceq ccvm cfv wne wral ctop ccn w3a iscvm eleq1
        simprbi anbi1d rexbidv rspcv mpan9 nfv cuni ccnv cima cin csn cdif cres
        crest chmeo crab cmpt nfmpt1 nfcxfr nfcv nffv nfne eleq2w fveq2 anbi12d
        cpw nfan neeq1d cbvrexw sylibr ) HDIUANOZEJOZPEGQZOZWBFUBZRUCZPZGISZEAQ
        ZOZWHFUBZRUCZPZAISVTWHWBOZWEPZGISZAJUDZWAWGVTDUEOIUEOHDIUFNOUGWPABCDFGH
        IJKLMUHUJWOWGAEJWHETZWNWFGIWQWMWCWEWHEWBUIUKULUMUNWLWFAGIWIWKGWIGUOGWJR
        GWHFGFGIKQZUPHUQWBURTCQZBQUSRTBWRWSUTVAUDHWSVBDWSVCNIWBVCNVDNOPCWRUDPKD
        VORUTVAVEZVFLGIWTVGVHGWHVIVJGRVIVKVPWFAUOWHWBTZWIWCWKWEAGEVLXAWJWDRWHWB
        FVMVQVNVRVS $.
    $}

    $( Reverse closure for an even covering.  (Contributed by Mario Carneiro,
       11-Feb-2015.) $)
    cvmsrcl $p |- ( T e. ( S ` U ) -> U e. J ) $=
      ( wcel cv wceq c0 csn cdif wral crest co cfv cdm cuni ccnv cima cin chmeo
      cres wa cpw crab dmmptss elfvdm sselid ) EFDUALDUBIFGIJMZUCHUDGMZUENBMZAM
      UFONAUOUQPQRHUQUHCUQSTIUPSTUGTLUIBUORUIJCUJOPQUKDKULEFDUMUN $.

    $( One direction of ~ cvmsval .  (Contributed by Mario Carneiro,
       13-Feb-2015.) $)
    cvmsi $p |- ( T e. ( S ` U ) ->
      ( U e. J /\ ( T C_ C /\ T =/= (/) ) /\ ( U. T = ( `' F " U ) /\
        A. u e. T ( A. v e. ( T \ { u } ) ( u i^i v ) = (/) /\
           ( F |` u ) e. ( ( C |`t u ) Homeo ( J |`t U ) ) ) ) ) ) $=
      ( wcel c0 wa wceq cv cdif wral crest co cfv wss cuni ccnv cima cres chmeo
      wne cin csn cvmsrcl crab imaeq2 eqeq2d oveq2 oveq2d eleq2d anbi2d ralbidv
      cpw anbi12d rabbidv fvmptss2 sseli unieq eqeq1d difeq1 raleqdv raleqbi1dv
      anbi1d elrab sylib simpld eldifsn elpwi anim1i syl simprd 3jca ) EFDUAZLZ
      FILECUBZEMUHZNZEUCZHUDZFUEZOZBPZAPUIMOZAEWIUJZQZRZHWIUFZCWISTZIFSTZUGTZLZ
      NZBERZNZABCDEFGHIJKUKWAECUTZLZWCNZWDWAEXBMUJQZLZXDWAXFXAWAEJPZUCZWGOZWJAX
      GWKQZRZWRNZBXGRZNZJXEULZLXFXANVTXOEGIXHWFGPZUEZOZXKWNWOIXPSTZUGTZLZNZBXGR
      ZNZJXEULXOFDXPFOZYDXNJXEYEXRXIYCXMYEXQWGXHXPFWFUMUNYEYBXLBXGYEYAWRXKYEXTW
      QWNYEXSWPWOUGXPFISUOUPUQURUSVAVBKVCVDXNXAJEXEXGEOZXIWHXMWTYFXHWEWGXGEVEVF
      XLWSBXGEYFXKWMWRYFWJAXJWLXGEWKVGVHVJVIVAVKVLZVMEXBMVNVLXCWBWCECVOVPVQWAXF
      XAYGVRVS $.

    $( Elementhood in the set ` S ` of all even coverings of an open set in
       ` J ` . ` S ` is an even covering of ` U ` if it is a nonempty
       collection of disjoint open sets in ` C ` whose union is the preimage of
       ` U ` , such that each set ` u e. S ` is homeomorphic under ` F ` to
       ` U ` .  (Contributed by Mario Carneiro, 13-Feb-2015.) $)
    cvmsval $p |- ( C e. V -> ( T e. ( S ` U ) <->
      ( U e. J /\ ( T C_ C /\ T =/= (/) ) /\ ( U. T = ( `' F " U ) /\
        A. u e. T ( A. v e. ( T \ { u } ) ( u i^i v ) = (/) /\
           ( F |` u ) e. ( ( C |`t u ) Homeo ( J |`t U ) ) ) ) ) ) ) $=
      ( wcel c0 wa wceq cv wral co cvv cfv wss wne cuni ccnv cima cin cdif cres
      csn crest chmeo w3a cvmsi 3anass cpw crab pwexg difexg rabexg 3syl imaeq2
      id eqeq2d oveq2 oveq2d eleq2d anbi2d ralbidv anbi12d rabbidv fvmptg unieq
      syl2anr eqeq1d difeq1 raleqdv anbi1d raleqbi1dv elrab elpw2g adantr bitrd
      eldifsn wb bitrid biimprd expimpd biimtrid impbid2 ) CJMZEFDUAZMZFIMZECUB
      ZENUCZOZEUDZHUEZFUFZPZBQZAQUGNPZAEXBUJZUHZRZHXBUIZCXBUKSZIFUKSZULSZMZOZBE
      RZOZUMZABCDEFGHIKLUNXOWNWQXNOZOWKWMWNWQXNUOWKWNXPWMWKWNOZWMXPXQWMEKQZUDZW
      TPZXCAXRXDUHZRZXKOZBXRRZOZKCUPZNUJZUHZUQZMZXPXQWLYIEWNWNYITMZWLYIPWKWNVCW
      KYFTMYHTMYKCJURYFYGTUSYEKYHTUTVAGFXSWSGQZUFZPZYBXGXHIYLUKSZULSZMZOZBXRRZO
      ZKYHUQYIITDYLFPZYTYEKYHUUAYNXTYSYDUUAYMWTXSYLFWSVBVDUUAYRYCBXRUUAYQXKYBUU
      AYPXJXGUUAYOXIXHULYLFIUKVEVFVGVHVIVJVKLVLVNVGYJEYHMZXNOXQXPYEXNKEYHXREPZX
      TXAYDXMUUCXSWRWTXREVMVOYCXLBXREUUCYBXFXKUUCXCAYAXEXREXDVPVQVRVSVJVTXQUUBW
      QXNUUBEYFMZWPOXQWQEYFNWDXQUUDWOWPWKUUDWOWEWNECJWAWBVRWFVRWFWCWGWHWIWJ $.

    $( An even covering is a subset of the topology of the domain (i.e. a
       collection of open sets).  (Contributed by Mario Carneiro,
       11-Feb-2015.) $)
    cvmsss $p |- ( T e. ( S ` U ) -> T C_ C ) $=
      ( cfv wcel c0 wa wceq cv wral crest co wss cuni ccnv cima cdif cres chmeo
      wne cin csn cvmsi simp2d simpld ) EFDLMZECUAZENUHZUNFIMUOUPOEUBHUCFUDPBQZ
      AQUINPAEUQUJUERHUQUFCUQSTIFSTUGTMOBEROABCDEFGHIJKUKULUM $.

    $( An even covering is nonempty.  (Contributed by Mario Carneiro,
       11-Feb-2015.) $)
    cvmsn0 $p |- ( T e. ( S ` U ) -> T =/= (/) ) $=
      ( cfv wcel c0 wa wceq cv wral crest co wss cuni ccnv cima cdif cres chmeo
      wne cin csn cvmsi simp2d simprd ) EFDLMZECUAZENUHZUNFIMUOUPOEUBHUCFUDPBQZ
      AQUINPAEUQUJUERHUQUFCUQSTIFSTUGTMOBEROABCDEFGHIJKUKULUM $.

    $( An even covering of ` U ` has union equal to the preimage of ` U ` by
       ` F ` .  (Contributed by Mario Carneiro, 11-Feb-2015.) $)
    cvmsuni $p |- ( T e. ( S ` U ) -> U. T = ( `' F " U ) ) $=
      ( cfv wcel wceq cv c0 wral crest co wa cuni ccnv cima cin cdif cres chmeo
      csn wss wne cvmsi simp3d simpld ) EFDLMZEUAHUBFUCNZBOZAOUDPNAEUPUHUEQHUPU
      FCUPRSIFRSUGSMTBEQZUNFIMECUIEPUJTUOUQTABCDEFGHIJKUKULUM $.

    $( An even covering of ` U ` is a disjoint union.  (Contributed by Mario
       Carneiro, 13-Feb-2015.) $)
    cvmsdisj $p |- ( ( T e. ( S ` U ) /\ A e. T /\ B e. T ) ->
      ( A = B \/ ( A i^i B ) = (/) ) ) $=
      ( wcel wceq cin c0 wne wa wral cfv w3a wn df-ne wi cv csn cdif cres crest
      co chmeo cuni ccnv cima wss cvmsi simp3d simprd simpl ralimi sneq difeq2d
      ineq1 eqeq1d raleqbidv rspccva sylan necom eldifsn biimpri sylan2b rspccv
      syl ineq2 syl2im expd 3impia biimtrrid orrd ) GHFUANZCGNZDGNZUBZCDOZCDPZQ
      OZWEUCCDRZWDWGCDUDWAWBWCWHWGUEWAWBSZWCWHWGWICAUFZPZQOZAGCUGZUHZTZWCWHSDWN
      NZWGWABUFZWJPZQOZAGWQUGZUHZTZBGTZWBWOWAXBJWQUIEWQUJUKKHUJUKULUKNZSZBGTZXC
      WAGUMJUNHUOOZXFWAHKNGEUPGQRSXGXFSABEFGHIJKLMUQURUSXEXBBGXBXDUTVAVNXBWOBCG
      WQCOZWSWLAXAWNXHWTWMGWQCVBVCXHWRWKQWQCWJVDVEVFVGVHWHWCDCRZWPCDVIWPWCXISDG
      CVJVKVLWLWGADWNWJDOWKWFQWJDCVOVEVMVPVQVRVSVT $.

    $( Every element of an even covering of ` U ` is homeomorphic to ` U ` via
       ` F ` .  (Contributed by Mario Carneiro, 13-Feb-2015.) $)
    cvmshmeo $p |- ( ( T e. ( S ` U ) /\ A e. T ) ->
      ( F |` A ) e. ( ( C |`t A ) Homeo ( J |`t U ) ) ) $=
      ( wcel cv crest co chmeo wral wceq wa cfv cres cin c0 cdif cuni ccnv cima
      csn wss wne cvmsi simp3d simprd simpr ralimi reseq2 oveq2 eleq12d rspccva
      syl oveq1d sylan ) FGEUAMZIBNZUBZDVEOPZJGOPZQPZMZBFRZCFMICUBZDCOPZVHQPZMZ
      VDVEANUCUDSAFVEUIUERZVJTZBFRZVKVDFUFIUGGUHSZVRVDGJMFDUJFUDUKTVSVRTABDEFGH
      IJKLULUMUNVQVJBFVPVJUOUPVAVJVOBCFVECSZVFVLVIVNVECIUQVTVGVMVHQVECDOURVBUSU
      TVC $.

    $( ` F ` , localized to an element of an even covering of ` U ` , is a
       bijection.  (Contributed by Mario Carneiro, 14-Feb-2015.) $)
    cvmsf1o $p |- ( ( F e. ( C CovMap J ) /\ T e. ( S ` U ) /\ A e. T ) ->
      ( F |` A ) : A -1-1-onto-> U ) $=
      ( co wcel cfv crest ctopon cuni wss ctop ccvm w3a cres chmeo wf1o cvmtop1
      3ad2ant1 eqid toptopon sylib cvmsss 3ad2ant2 sseldd elssuni syl resttopon
      simp3 syl2anc cvmtop2 cvmsrcl cvmshmeo 3adant1 hmeof1o2 syl3anc ) IDJUAMN
      ZFGEONZCFNZUBZDCPMZCQONZJGPMZGQONZICUCZVIVKUDMNZCGVMUEVHDDRZQONZCVOSZVJVH
      DTNZVPVEVFVRVGDIJUFUGDVOVOUHUIUJVHCDNVQVHFDCVFVEFDSVGABDEFGHIJKLUKULVEVFV
      GUQUMCDUNUOCDVOUPURVHJJRZQONZGVSSZVLVHJTNZVTVEVFWBVGDIJUSUGJVSVSUHUIUJVHG
      JNZWAVFVEWCVGABDEFGHIJKLUTULGJUNUOGJVSUPURVFVGVNVEABCDEFGHIJKLVAVBVMVIVKC
      GVCVD $.

    $( The sets of an even covering are clopen in the subspace topology on
       ` T ` .  (Contributed by Mario Carneiro, 14-Feb-2015.) $)
    cvmscld $p |- ( ( F e. ( C CovMap J ) /\ T e. ( S ` U ) /\ A e. T ) ->
      A e. ( Clsd ` ( C |`t ( `' F " U ) ) ) ) $=
      ( vx wcel cuni wss wceq syl2anc cin c0 ccvm co cfv w3a ccnv cima csn cdif
      crest ccld ctop cvmtop1 3ad2ant1 cvmsuni 3ad2ant2 cvmsss eqsstrrd restuni
      unissd eqid difeq1d cun unisng 3ad2ant3 uneq2d uniun undif1 simp3 ssequn2
      snssd sylib eqtrid unieqd eqtrd eqtr3id eqtr3d difss unissi sseqtrid ciun
      wb cv uniiun ineq2i incom iunin2 3eqtr4i wa wne eldifsn wn nesym cvmsdisj
      wo 3expa ord biimtrid impr sylan2b iuneq2dv 3adant1 iun0 eqtrdi uneqdifeq
      mpbid uniexg eqeltrrd resttop elssuni adantl adantr sseqtrd dfss2 elrestr
      cvv sselda syl3anc ex ssrdv ssdifssd uniopn opncld ) IDJUAUBNZFGEUCZNZCFN
      ZUDZDIUEGUFZUIUBZOZFCUGZUHZOZUHZCYIUJUCZYGYHYMUHZYNCYGYHYJYMYGDUKNZYHDOZP
      YHYJQYCYEYQYFDIJULUMZYGYHFOZYRYEYCYTYHQZYFABDEFGHIJKLUNUOZYGFDYEYCFDPYFAB
      DEFGHIJKLUPUOZUSUQYHDYRYRUTURRVAYGYMCVBZYHQZYPCQZYGYMYKOZVBZUUDYHYGUUGCYM
      YFYCUUGCQYECFVCVDVEYGUUHYLYKVBZOZYHYLYKVFYGUUJYTYHYGUUIFYGUUIFYKVBZFFYKVG
      YGYKFPUUKFQYGCFYCYEYFVHVJYKFVIVKVLVMUUBVNVOVPYGYMYHPYMCSZTQUUEUUFWAYGYTYM
      YHYLFFYKVQVRUUBVSYGUULMYLCMWBZSZVTZTCYMSCMYLUUMVTZSUULUUOYMUUPCMYLWCWDYMC
      WEMYLCUUMWFWGYGUUOMYLTVTZTYEYFUUOUUQQYCYEYFWHZMYLUUNTUUMYLNUURUUMFNZUUMCW
      IZWHUUNTQZUUMFCWJUURUUSUUTUVAUUTCUUMQZWKUURUUSWHZUVAUUMCWLUVCUVBUVAYEYFUU
      SUVBUVAWNABCUUMDEFGHIJKLWMWOWPWQWRWSWTXAMYLXBXCVLYMCYHXDRXEVPYGYIUKNZYMYI
      NZYNYONYGYQYHXONZUVDYSYGYTYHXOUUBYEYCYTXONYFFYDXFUOXGZYHDXOXHRZYGUVDYLYIP
      UVEUVHYGFYIYKYGMFYIYGUUSUUMYINYGUUSWHZUUMYHSZUUMYIUVIUUMYHPUVJUUMQUVIUUMY
      TYHUUSUUMYTPYGUUMFXIXJYGUUAUUSUUBXKXLUUMYHXMVKUVIYQUVFUUMDNUVJYINYGYQUUSY
      SXKYGUVFUUSUVGXKYGFDUUMUUCXPUUMYHDUKXOXNXQXGXRXSXTYLYIYARYMYIYJYJUTYBRXG
      $.

    $( An open subset of an evenly covered set is evenly covered.  (Contributed
       by Mario Carneiro, 7-Jul-2015.) $)
    cvmsss2 $p |- ( ( F e. ( C CovMap J ) /\ V e. J /\ V C_ U ) ->
      ( ( S ` U ) =/= (/) -> ( S ` V ) =/= (/) ) ) $=
      ( vy vz vt c0 wcel co wss wa wceq vx vw va vb cfv wne cv wex ccvm n0 ccnv
      w3a cima cin cmpt crn cuni csn cdif wral cres crest chmeo simpl2 wel ctop
      simpl1 cvmtop1 syl adantr cvmsss adantl cvmcn cnima syl2anc inopn syl3anc
      sselda ccn fmpttd frnd cvmsn0 cdm dmmptg inex1g mprg eqeq1i dm0rn0 bitr3i
      cvv necon3bii sylib jca cpw inss2 wb elpw2g mpbiri sspwuni simpl3 cvmsuni
      imass2 sseqtrrd wrex eqid ineq1 rspceeqv mpan2 ad2antrl vex inex1 elrnmpt
      ax-mp sylibr simprr simplr elind rspcev rexlimdvaa eluni2 3imtr4g eqelssd
      eleq2 mpd eldifsn wi weq wn equcoms necon3ai simpllr simpr cvmsdisj inss1
      wo ord sseq0 eqeq1d biimtrid restabs syl56 neeq1 ineq2 inindir syl5ibrcom
      mpan eqtr4di imbi12d rexlimdva ralrimiv resabs1 cvmshmeo adantll sseqtrid
      impd elssuni restuni hmeores eqeltrrid a1i incom cnvresima eqtr4i imaeq2i
      wf1o cvmsf1o f1ofo foimacnv eqtrid oveq2d cvmtop2 cvmsrcl oveq12d eleqtrd
      eqtrd ralrimiva rgenw cbvmptv sneq difeq2d raleqbidv reseq2 oveq2 eleq12d
      wfo oveq1d anbi12d ralrnmptw cvmscbv cvmsval mpbir3and ne0d ex exlimdv )
      EDUEZOUFUAUGZUWOPZUAUHGCHUIQPZIHPZIERZULZIDUEZOUFZUAUWOUJUXAUWQUXCUAUXAUW
      QUXCUXAUWQSZUXBLUWPLUGZGUKZIUMZUNZUOZUPZUXDUXJUXBPZUWSUXJCRZUXJOUFZSZUXJU
      QZUXGTZUBUGZMUGZUNZOTZMUXJUXQURZUSZUTZGUXQVAZCUXQVBQZHIVBQZVCQZPZSZUBUXJU
      TZSZUWRUWSUWTUWQVDZUXDUXLUXMUXDUWPCUXIUXDLUWPUXHCUXDLUAVEZSZCVFPZUXECPUXG
      CPZUXHCPUXDUYOUYMUXDUWRUYOUWRUWSUWTUWQVGZCGHVHVIZVJUXDUWPCUXEUWQUWPCRUXAA
      BCDUWPEFGHJKVKVLZVRUXDUYPUYMUXDGCHVSQPZUWSUYPUXDUWRUYTUYQCGHVMVIUYLIGCHVN
      VOVJZUXEUXGCVPVQVTWAUXDUWPOUFZUXMUWQVUBUXAABCDUWPEFGHJKWBVLUWPOUXJOUWPOTU
      XIWCZOTUXJOTVUCUWPOUXHWJPVUCUWPTLUWPLUWPUXHWJWDUXEUXGUWPWEWFWGUXIWHWIWKWL
      WMUXDUXPUYJUXDMUXOUXGUXDUXJUXGWNZRUXOUXGRUXDUWPVUDUXIUXDLUWPUXHVUDUYNUXHV
      UDPZUXHUXGRZUXEUXGWOUYNUYPVUEVUFWPVUAUXHUXGCWQVIWRVTWAUXJUXGWSWLUXDUXRUXG
      PZSZUXRUWPUQZPZUXRUXOPZUXDUXGVUIUXRUXDUXGUXFEUMZVUIUXDUWTUXGVULRUWRUWSUWT
      UWQWTZIEUXFXBVIUWQVUIVULTUXAABCDUWPEFGHJKXAVLXCVRVUHMNVEZNUWPXDMUBVEZUBUX
      JXDZVUJVUKVUHVUNVUPNUWPVUHNUAVEZVUNSZSZNUGZUXGUNZUXJPZUXRVVAPZVUPVUSVVAUX
      HTLUWPXDZVVBVUQVVDVUHVUNVUQVVAVVATVVDVVAXELVUTUWPUXHVVAVVAUXEVUTUXGXFZXGX
      HXIVVAWJPZVVBVVDWPVUTUXGNXJXKZLUWPUXHVVAUXIWJUXIXEZXLXMXNVUSVUTUXGUXRVUHV
      UQVUNXOUXDVUGVURXPXQVUOVVCUBVVAUXJUXQVVAUXRYCXRVOXSNUXRUWPXTUBUXRUXJXTYAY
      DYBUXDVVAUXRUNZOTZMUXJVVAURZUSZUTZGVVAVAZCVVAVBQZUYFVCQZPZSZNUWPUTZUYJUXD
      VVRNUWPUXDVUQSZVVMVVQVVTVVJMVVLUXRVVLPUXRUXJPZUXRVVAUFZSVVTVVJUXRUXJVVAYE
      VVTVWAVWBVVJVWAUXRUXHTZLUWPXDZVVTVWBVVJYFZUXRWJPVWAVWDWPMXJLUWPUXHUXRUXIW
      JVVHXLXMVVTVWCVWELUWPVVTUYMSZVWEVWCUXHVVAUFZVUTUXEUNZUXGUNZOTZYFVWGNLYGZY
      HVWFVWHOTZVWJVWKUXHVVAUXHVVATLNVVEYIYJVWFVWKVWLVWFUWQVUQUYMVWKVWLYOUXAUWQ
      VUQUYMYKUXDVUQUYMXPVVTUYMYLABVUTUXECDUWPEFGHJKYMVQYPVWIVWHRVWLVWJVWHUXGYN
      VWIVWHYQUUFUUAVWCVWBVWGVVJVWJUXRUXHVVAUUBVWCVVIVWIOVWCVVIVVAUXHUNVWIUXRUX
      HVVAUUCVUTUXEUXGUUDUUGYRUUHUUEUUIYSUUOYSUUJVVTVVNCVUTVBQZVVAVBQZHEVBQZGVU
      TVAZVVAUMZVBQZVCQZVVPVVTVVNVWPVVAVAZVWSVVAVUTRZVWTVVNTVUTUXGYNZGVVAVUTUUK
      XMVVTVWPVWMVWOVCQPZVVAVWMUQZRVWTVWSPUWQVUQVXCUXAABVUTCDUWPEFGHJKUULUUMVVT
      VUTVVAVXDVXBVVTUYOVUTCUQZRZVUTVXDTUXDUYOVUQUYRVJZVVTVUTCPVXFUXDUWPCVUTUYS
      VRVUTCUUPVIVUTCVXEVXEXEUUQVOUUNVWPVWMVWOVXDVVAVXDXEUURVOUUSVVTVWNVVOVWRUY
      FVCVVTUYOVXAVUQVWNVVOTVXGVXAVVTVXBUUTUXDVUQYLZVVAVUTCVFUWPYTVQVVTVWRVWOIV
      BQZUYFVVTVWQIVWOVBVVTVWQVWPVWPUKIUMZUMZIVVAVXJVWPVVAUXGVUTUNVXJVUTUXGUVAV
      UTIGUVBUVCUVDVVTVUTEVWPUWEZUWTVXKITVVTVUTEVWPUVEZVXLVVTUWRUWQVUQVXMUXDUWR
      VUQUYQVJUXAUWQVUQXPVXHABVUTCDUWPEFGHJKUVFVQVUTEVWPUVGVIUXDUWTVUQVUMVJVUTE
      IVWPUVHVOUVIUVJUXDVXIUYFTZVUQUXDHVFPZUWTEHPZVXNUXDUWRVXOUYQCGHUVKVIVUMUWQ
      VXPUXAABCDUWPEFGHJKUVLVLIEHVFHYTVQVJUVOUVMUVNWMUVPVVFNUWPUTUYJVVSWPVVFNUW
      PVVGUVQUYIVVRNUBUWPVVAUXIWJLNUWPUXHVVAVVEUVRUXQVVATZUYCVVMUYHVVQVXQUXTVVJ
      MUYBVVLVXQUYAVVKUXJUXQVVAUVSUVTVXQUXSVVIOUXQVVAUXRXFYRUWAVXQUYDVVNUYGVVPU
      XQVVAGUWBVXQUYEVVOUYFVCUXQVVACVBUWCUWFUWDUWGUWHXMXNWMUXDUYOUXKUWSUXNUYKUL
      WPUYRMUBCDUXJIUCGHVFUDABCDFGHJUCUDUBMKUWIUWJVIUWKUWLUWMUWNYS $.

    $( The covering map property can be restricted to an open subset.
       (Contributed by Mario Carneiro, 7-Jul-2015.) $)
    cvmcov2 $p |- ( ( F e. ( C CovMap J ) /\ U e. J /\ P e. U ) ->
      E. x e. ~P U ( P e. x /\ ( S ` x ) =/= (/) ) ) $=
      ( vy wcel cv cfv c0 wne wa adantr ccvm co w3a wrex cuni simp1 simp3 simp2
      cpw elunii syl2anc eqid cvmcov cin wss inss2 vex inex1 elpw mpbir simprrl
      a1i elind simprrr ctop cvmtop2 syl simprl inopn syl3anc inss1 cvmsss2 mpd
      wi wceq eleq2 fveq2 neeq1d anbi12d rspcev syl12anc rexlimddv ) IDJUAUBNZG
      JNZEGNZUCZEMOZNZWGFPQRZSZEAOZNZWKFPZQRZSZAGUIZUDZMJWFWCEJUEZNZWJMJUDWCWDW
      EUFZWFWEWDWSWCWDWEUGZWCWDWEUHZEGJUJUKMBCDEFHIJWRKLWRULUMUKWFWGJNZWJSZSZWG
      GUNZWPNZEXFNZXFFPZQRZWQXGXEXGXFGUOWGGUPXFGWGGMUQURUSUTVBXEWGGEWFXCWHWIVAW
      FWEXDXATVCXEWIXJWFXCWHWIVDXEWCXFJNZXFWGUOZWIXJVNWFWCXDWTTZXEJVENZXCWDXKXE
      WCXNXMDIJVFVGWFXCWJVHWFWDXDXBTWGGJVIVJXLXEWGGVKVBBCDFWGHIJXFKLVLVJVMWOXHX
      JSAXFWPWKXFVOZWLXHWNXJWKXFEVPXOWMXIQWKXFFVQVRVSVTWAWB $.

    cvmseu.1 $e |- B = U. C $.
    $( Every element in ` U. T ` is a member of a unique element of ` T ` .
       (Contributed by Mario Carneiro, 14-Feb-2015.) $)
    cvmseu $p |- ( ( F e. ( C CovMap J ) /\
      ( T e. ( S ` U ) /\ A e. B /\ ( F ` A ) e. U ) ) -> E! x e. T A e. x ) $=
      ( vz wcel wa wceq c0 ccvm co cfv w3a wrex wral wreu cuni ccnv cima simpr2
      cv wi simpr3 ccn wf wfn cvmcn adantr eqid cnf ffn elpreima 4syl mpbir2and
      wb simpr1 cvmsuni syl eleqtrrd eluni2 sylib cin wne inelcm cvmsdisj 3expb
      wo sylan ord necon1ad syl5 ralrimivva eleq2w reu4 sylanbrc ) KFLUAUBQZHIG
      UCQZDEQZDKUCIQZUDZRZDAULZQZAHUEZWNDPULZQZRZWMWPSZUMZPHUFAHUFWNAHUGWLDHUHZ
      QWOWLDKUIIUJZXAWLDXBQZWIWJWGWHWIWJUKWGWHWIWJUNWLKFLUOUBQZELUHZKUPKEUQXCWI
      WJRVFWGXDWKFKLURUSKFLEXEOXEUTVAEXEKVBEDIKVCVDVEWLWHXAXBSWGWHWIWJVGZBCFGHI
      JKLMNVHVIVJADHVKVLWLWTAPHHWRWMWPVMZTVNWLWMHQZWPHQZRZRZWSDWMWPVOXKWSXGTXKW
      SXGTSZWLWHXJWSXLVRZXFWHXHXIXMBCWMWPFGHIJKLMNVPVQVSVTWAWBWCWNWQAPHAPDWDWEW
      F $.

    ${
      cvmsiota.2 $e |- W = ( iota_ x e. T A e. x ) $.
      $( Identify the unique element of ` T ` containing ` A ` .  (Contributed
         by Mario Carneiro, 14-Feb-2015.) $)
      cvmsiota $p |- ( ( F e. ( C CovMap J ) /\
        ( T e. ( S ` U ) /\ A e. B /\ ( F ` A ) e. U ) ) ->
          ( W e. T /\ A e. W ) ) $=
        ( wcel cfv wa ccvm co w3a crab crio wreu cvmseu riotacl2 eqeltrid eleq2
        cv syl cbvrabv elrab2 sylib ) KFLUAUBRHIGSRDERDKSIRUCTZMDAUKZRZAHUDZRMH
        RDMRZTUPMURAHUEZUSQUPURAHUFVAUSRABCDEFGHIJKLNOPUGURAHUHULUIDBUKZRZUTBMH
        USVBMDUJURVCABHUQVBDUJUMUNUO $.
    $}

    $( Lemma for ~ cvmopn .  (Contributed by Mario Carneiro, 7-May-2015.) $)
    cvmopnlem $p |- ( ( F e. ( C CovMap J ) /\ A e. C ) -> ( F " A ) e. J ) $=
      ( vx vy co wcel wa cv wss adantr vz vt vw ccvm cima wrex wral cfv c0 cuni
      wne simpll wf ccn cvmcn cnf syl elssuni sseqtrrdi adantl sselda ffvelcdmd
      eqid cvmcov syl2anc wex n0 crio crest cres wceq inss2 resima2 ax-mp chmeo
      cin simprr simprl cvmsiota syl13anc cvmshmeo ctop cvmtop1 simpllr elrestr
      simpld syl3anc hmeoima eqeltrrid cvmtop2 ad2antrr ad2antll restopn2 mpbid
      wb cvmsrcl wfn ffnd inss1 sstrid simplr simprd elind fnfvima imass2 eleq2
      mp1i sseq1 anbi12d rspcev syl12anc exlimdv biimtrid expimpd rexlimdvw mpd
      expr ralrimiva eleq1 anbi1d rexbidv ralima mpbird eltop2 ) HEIUDOPZCEPZQZ
      HCUEZIPZMRZNRZPZYKYHSZQZNIUFZMYHUGZYGYPUARZHUHZYKPZYMQZNIUFZUACUGZYGUUAUA
      CYGYQCPZQZYRUBRZPZUUEFUHZUIUKZQZUBIUFZUUAUUDYEYRIUJZPUUJYEYFUUCULZUUDDUUK
      YQHYGDUUKHUMZUUCYGHEIUNOPZUUMYEUUNYFEHIUOTHEIDUUKLUUKVCZUPUQZTYGCDYQYFCDS
      ZYEYFCEUJDCEURLUSZUTZVAZVBUBABEYRFGHIUUKJKUUOVDVEUUDUUIUUAUBIUUDUUFUUHUUA
      UUHUCRZUUGPZUCVFUUDUUFQZUUAUCUUGVGUVCUVBUUAUCUUDUUFUVBUUAUUDUUFUVBQZQZHCY
      QYJPMUVAVHZVPZUEZIPZYRUVHPZUVHYHSZUUAUVEUVIUVHUUESZUVEUVHIUUEVIOZPZUVIUVL
      QZUVEUVHHUVFVJZUVGUEZUVMUVGUVFSUVQUVHVKCUVFVLHUVGUVFVMVNUVEUVPEUVFVIOZUVM
      VOOPZUVGUVRPZUVQUVMPUVEUVBUVFUVAPZUVSUUDUUFUVBVQZUVEUWAYQUVFPZUVEYEUVBYQD
      PZUUFUWAUWCQUUDYEUVDUULTZUWBUUDUWDUVDUUTTUUDUUFUVBVRMABYQDEFUVAUUEGHIUVFJ
      KLUVFVCVSVTZWFZABUVFEFUVAUUEGHIJKWAVEUVEEWBPZUWAYFUVTUVEYEUWHUWEEHIWCUQUW
      GYEYFUUCUVDWDZCUVFEWBUVAWEWGUVGUVPUVRUVMWHVEWIUVEIWBPZUUEIPZUVNUVOWOYGUWJ
      UUCUVDYEUWJYFEHIWJTZWKUVBUWKUUDUUFABEFUVAUUEGHIJKWPWLUUEUVHIWMVEWNWFUVEHD
      WQZUVGDSYQUVGPUVJYGUWMUUCUVDYGDUUKHUUPWRZWKUVEUVGCDCUVFWSZUVEYFUUQUWIUURU
      QWTUVECUVFYQYGUUCUVDXAUVEUWAUWCUWFXBXCDUVGHYQXDWGUVGCSUVKUVEUWOUVGCHXEXGY
      TUVJUVKQNUVHIYKUVHVKYSUVJYMUVKYKUVHYRXFYKUVHYHXHXIXJXKXQXLXMXNXOXPXRYGUWM
      UUQYPUUBWOUWNUUSYOUUAMUADCHYJYRVKZYNYTNIUWPYLYSYMYJYRYKXSXTYAYBVEYCYGUWJY
      IYPWOUWLMNYHIYDUQYC $.

    cvmfolem.2 $e |- X = U. J $.
    $( Lemma for ~ cvmfo .  (Contributed by Mario Carneiro, 13-Feb-2015.) $)
    cvmfolem $p |- ( F e. ( C CovMap J ) -> F : B -onto-> X ) $=
      ( vx vy vz wcel cv cfv wa vw vt ccvm co wf wceq wrex wral wfo ccn cnf syl
      cvmcn c0 wne cvmcov ex wex n0 cvmsn0 ad2antll sylib cres ccnv wss simprlr
      cuni cvmsss simprr sseldd elssuni sseqtrrdi simpll cvmsf1o syl3anc f1ocnv
      wf1o f1of simprll ffvelcdmd f1ocnvfv2 syl2anc fvres eqtr3d fveq2 rspceeqv
      3syl expr exlimdv biimtrid expimpd rexlimdva syld ralrimiv dffo3 sylanbrc
      mpd ) GDHUCUDQZCIGUEZNRZORZGSZUFOCUGZNIUHCIGUIWRGDHUJUDQWSDGHUMGDHCILMUKU
      LWRXCNIWRWTIQZWTPRZQZXEESZUNUOZTZPHUGZXCWRXDXJPABDWTEFGHIJKMUPUQWRXIXCPHW
      RXEHQZTZXFXHXCXHUARZXGQZUAURXLXFTZXCUAXGUSXOXNXCUAXLXFXNXCXLXFXNTZTZUBRZX
      MQZUBURZXCXQXMUNUOZXTXNYAXLXFABDEXMXEFGHJKUTVAUBXMUSVBXQXSXCUBXLXPXSXCXLX
      PXSTZTZWTGXRVCZVDZSZCQWTYFGSZUFXCYCXRCYFYCXRDVGZCYCXRDQXRYHVEYCXMDXRYCXNX
      MDVEXLXFXNXSVFZABDEXMXEFGHJKVHULXLXPXSVIZVJXRDVKULLVLYCXEXRWTYEYCXRXEYDVQ
      ZXEXRYEVQXEXRYEUEYCWRXNXSYKWRXKYBVMYIYJABXRDEXMXEFGHJKVNVOZXRXEYDVPXEXRYE
      VRWGXLXFXNXSVSZVTZVJYCYFYDSZWTYGYCYKXFYOWTUFYLYMXRXEWTYDWAWBYCYFXRQYOYGUF
      YNYFXRGWCULWDOYFCXBYGWTXAYFGWEWFWBWHWIWQWHWIWJWKWLWMWNONCIGWOWP $.
  $}

  ${
    $d u v A $.  $d k s u v C $.  $d k s u v F $.  $d k s u v J $.
    $( A covering map is an open map.  (Contributed by Mario Carneiro,
       7-May-2015.) $)
    cvmopn $p |- ( ( F e. ( C CovMap J ) /\ A e. C ) -> ( F " A ) e. J ) $=
      ( vv vu vk vs cuni cv ccnv wceq c0 csn cdif wral crest co wa eqid cin cpw
      cima cres chmeo wcel crab cmpt cvmopnlem ) EFABIZBGDHJZICKGJZUCLFJZEJUAML
      EUKUMNOPCUMUDBUMQRDULQRUERUFSFUKPSHBUBMNOUGUHZGCDHUNTUJTUI $.
  $}

  ${
    $d a b f g k m r s u v w C $.  $d f g G $.  $d a b k m r s t u v w y z J $.
    $d b v w B $.  $d a f g m s t x y z K $.  $d a b k m r s t u v w x y z M $.
    $d a m s t x y z N $.  $d f g x O $.  $d a f g m s t x y z ph $.  $d x Q $.
    $d a b f g k m r s t u v w y z F $.  $d a b m s t y z S $.  $d k s u v U $.
    $d f g P $.  $d x R $.  $d s u v T $.  $d u v W $.  $d a m s t x y z Y $.
    cvmliftmo.b $e |- B = U. C $.
    cvmliftmo.y $e |- Y = U. K $.
    cvmliftmo.f $e |- ( ph -> F e. ( C CovMap J ) ) $.
    cvmliftmo.k $e |- ( ph -> K e. Conn ) $.
    cvmliftmo.l $e |- ( ph -> K e. N-Locally Conn ) $.
    cvmliftmo.o $e |- ( ph -> O e. Y ) $.
    ${
      cvmliftmoi.m $e |- ( ph -> M e. ( K Cn C ) ) $.
      cvmliftmoi.n $e |- ( ph -> N e. ( K Cn C ) ) $.
      cvmliftmoi.g $e |- ( ph -> ( F o. M ) = ( F o. N ) ) $.
      cvmliftmoi.p $e |- ( ph -> ( M ` O ) = ( N ` O ) ) $.
      ${
        cvmliftmolem.1 $e |- S = ( k e. J |->
          { s e. ( ~P C \ { (/) } ) | ( U. s = ( `' F " k ) /\
            A. u e. s ( A. v e. ( s \ { u } ) ( u i^i v ) = (/) /\
               ( F |` u ) e. ( ( C |`t u ) Homeo ( J |`t k ) ) ) ) } ) $.
        ${
          cvmliftmolem.2 $e |- ( ( ph /\ ps ) -> T e. ( S ` U ) ) $.
          cvmliftmolem.3 $e |- ( ( ph /\ ps ) -> W e. T ) $.
          cvmliftmolem.4 $e |- ( ( ph /\ ps ) -> I C_ ( `' M " W ) ) $.
          cvmliftmolem.5 $e |- ( ( ph /\ ps ) -> ( K |`t I ) e. Conn ) $.
          cvmliftmolem.6 $e |- ( ( ph /\ ps ) -> X e. I ) $.
          cvmliftmolem.7 $e |- ( ( ph /\ ps ) -> Q e. I ) $.
          cvmliftmolem.8 $e |- ( ( ph /\ ps ) -> R e. I ) $.
          cvmliftmolem.9 $e |- ( ( ph /\ ps ) -> ( F ` ( M ` X ) ) e. U ) $.
          $( Lemma for ~ cvmliftmo .  (Contributed by Mario Carneiro,
             10-Mar-2015.) $)
          cvmliftmolem1 $p |- ( ( ph /\ ps ) ->
            ( Q e. dom ( M i^i N ) -> R e. dom ( M i^i N ) ) ) $=
            ( vx wa cv cfv wceq crab wcel cin cres ccom adantr fveq1d ccnv cima
            cdm sseldd wfn wb ccn co wf cnf ffnd elpreima simprbda syldan fvco3
            syl sylan 3eqtr3d simplbda fvres crest cuni eqid cconn wss cnvimass
            fssdm sstrd cnrest syl2anc ctopon ctop ccvm cvmtop1 toptopon df-ima
            crn sylib elssuni cvmsuni sseqtrd imass2 cnveqd cnvco 3eqtr3g imaco
            imaeq1d wfun ffund fdmd sseqtrrd funimass3 eqsstrrid cvmcn sseqtrid
            mpbird cnrest2 syl3anc mpbid eqeltrrd eqeq12d elrab3 3imtr4d eleq2d
            cvv fveq2 dfss2 topopn ssexd cvmsss elrestr cvmscld conntop restuni
            ccld eleqtrd simpr eqeltrd feq2d ffvelcdmd 3eqtr4d wf1 wf1o cvmsf1o
            conncn f1of1 f1fveq syl12anc ex fndmin ) ABVDZGVCVEZQVFZUVFRVFZVGZV
            CUBVHZVIZHUVJVIZGQRVJVQZVIHUVMVIUVEGQVFZGRVFZVGZHQVFZHRVFZVGZUVKUVL
            UVEUVPUVSUVEUVPVDZUVQMTVKZVFZUVRUWAVFZVGZUVSUVTUVQMVFZUVRMVFZUWBUWC
            UVEUWEUWFVGUVPUVEHMQVLZVFZHMRVLZVFZUWEUWFUVEHUWGUWIAUWGUWIVGBULVMZV
            NABHUBVIZUWHUWEVGZABHQVOZTVPZVIZUWLUVENUWOHUQVAVRZAUWPUWLUVQTVIZAQU
            BVSZUWPUWLUWRVDVTAUBEQAQPFWAWBZVIUBEQWCZUJQPFUBEUEUDWDWJZWEZUBHTQWF
            WJZWGWHZAUXAUWLUWMUXBUBEHMQWIWKWHABUWLUWJUWFVGZUXEAUBERWCZUWLUXFARU
            WTVIZUXGUKRPFUBEUEUDWDWJZUBEHMRWIWKWHWLVMUVTUWRUWBUWEVGUVEUWRUVPABU
            WPUWRUWQAUWPUWLUWRUXDWMWHVMZUVQTMWNWJUVTUVRTVIZUWCUWFVGUVTHRNVKZVFZ
            UVRTUVTHNVIZUXMUVRVGUVEUXNUVPVAVMZHNRWNWJUVTNTHUXLUVTNTUXLWCPNWOWBZ
            WPZTUXLWCUVTGTUXLUXPFMVOZKVPZWOWBZUXQUXQWQUVEUXPWRVIUVPURVMUVEUXLUX
            PUXTWAWBVIZUVPUVEUXLUXPFWAWBVIZUYAUVEUXHNUBWSZUYBAUXHBUKVMUVENUWOUB
            UQAUWOUBWSBAUBEUWOQQTWTUXBXAVMXBZNRPFUBUEXCXDUVEFEXEVFVIZUXLXKZUXSW
            SUXSEWSUYBUYAVTUVEFXFVIZUYEUVEMFOXGWBVIZUYGAUYHBUFVMZFMOXHWJZFEUDXI
            XLUVEUYFRNVPZUXSRNXJUVEUYKUXSWSZNRVOZUXSVPZWSZUVENUWNUXSVPZUYNUVENU
            WOUYPUQUVETUXSWSZUWOUYPWSUVETJWPZUXSUVETJVIZTUYRWSUPTJXMWJUVEJKIVFV
            IZUYRUXSVGUOCDFIJKLMOUCUNXNWJXOZTUXSUWNXPWJXBUVEUWNUXRVLZKVPUYMUXRV
            LZKVPUYPUYNUVEVUBVUCKUVEUWGVOUWIVOVUBVUCUVEUWGUWIUWKXQMQXRMRXRXSYAU
            WNUXRKXTUYMUXRKXTXSXOUVERYBNRVQZWSUYLUYOVTUVEUBERAUXGBUXIVMZYCUVENU
            BVUDUYDUVEUBERVUEYDYENUXSRYFXDYJYGUVEMVQZUXSEMKWTAVUFEVGBAEOWPZMAMF
            OWAWBVIZEVUGMWCAUYHVUHUFFMOYHWJMFOEVUGUDVUGWQWDWJYDVMYIZUXSUXLUXPFE
            YKYLYMVMUVETUXTVIUVPUVETUXSVJZTUXTUVEUYQVUJTVGVUATUXSUUAXLUVEUYGUXS
            YSVITFVIVUJUXTVIUYJUVEUXSEFUVEUYGEFVIUYJFEUDUUBWJVUIUUCUVEJFTUVEUYT
            JFWSUOCDFIJKLMOUCUNUUDWJUPVRTUXSFXFYSUUEYLYNVMUVETUXTUUIVFVIZUVPUVE
            UYHUYTUYSVUKUYIUOUPCDTFIJKLMOUCUNUUFYLVMUVEGUXQVIUVPUVEGNUXQUTUVEPX
            FVIZUYCNUXQVGZAVULBAPWRVIVULUGPUUGWJVMUYDNPUBUEUUHXDZUUJVMUVTGUXLVF
            ZUVOTUVTGNVIZVUOUVOVGUVEVUPUVPUTVMGNRWNWJUVTUVNUVOTUVEUVPUUKUVEUVNT
            VIZUVPABGUWOVIZVUQUVENUWOGUQUTVRZAVURGUBVIZVUQAUWSVURVUTVUQVDVTUXCU
            BGTQWFWJZWMWHVMYNUULUUSUVTNUXQTUXLUVEVUMUVPVUNVMUUMYJUXOUUNYNZUVRTM
            WNWJUUOUVTTKUWAUUPZUWRUXKUWDUVSVTUVEVVCUVPUVETKUWAUUQZVVCUVEUYHUYTU
            YSVVDUYIUOUPCDTFIJKLMOUCUNUURYLTKUWAUUTWJVMUXJVVBTKUVQUVRUWAUVAUVBY
            MUVCUVEVUTUVKUVPVTABVURVUTVUSAVURVUTVUQVVAWGWHUVIUVPVCGUBUVFGVGUVGU
            VNUVHUVOUVFGQYTUVFGRYTYOYPWJUVEUWLUVLUVSVTUXEUVIUVSVCHUBUVFHVGUVGUV
            QUVHUVRUVFHQYTUVFHRYTYOYPWJYQUVEUVMUVJGAUVMUVJVGZBAUWSRUBVSVVEUXCAU
            BERUXIWEVCUBQRUVDXDVMZYRUVEUVMUVJHVVFYRYQ $.
        $}

        $( Lemma for ~ cvmliftmo .  (Contributed by Mario Carneiro,
           10-Mar-2015.) $)
        cvmliftmolem2 $p |- ( ph -> M = N ) $=
          ( vx vy vz va vt vb ccn co wcel wf wfn cnf ffn 3syl cv wceq crab wral
          cfv cin cdm ccld inss1 wb wa wrex wne ccvm cuni adantr syl ffvelcdmda
          c0 cvmcn eqid syldan cvmcov syl2anc wi wex n0 wss crest w3a ccnv crio
          cconn cima cpw cnlly simprrr cvmsss simprll simprrl cvmsiota syl13anc
          ffvelcdmd simpld sseldd cnima simprd mpbir2and nlly2i syl3anc simprr1
          elpreima simplrr adantl adantrr simplll ad2antll elpwid cvmliftmolem1
          simplr3 simplr2 adantrrr impbid ralrimiva jca expr reximdva rexlimdva
          anassrs mpd exlimdv biimtrid expimpd ctop conntop fndmin ssrab2 fveq2
          eqsstrdi sselid isclo mpbird eqeq12d elrab sylanbrc ne0d inss2 eqtr3d
          eleqtrrd connclo rabid2 sylib r19.21bi eqfnfvd ) AUGNKLAKJEUMUNZUOZND
          KUPZKNUQZUBKJENDQPURZNDKUSZUTZALUUOUONDLUPLNUQZUCLJENDQPURNDLUSUTZAUG
          VAZKVEZUVDLVEZVBZUGNANUVGUGNVCZVBUVGUGNVDAKLVFVGZNUVHAUVIJNQSAJJVHVEZ
          VFZJUVIJUVJVIAUVIUVKUOZUVDUHVAZUOZUVDUVIUOZUIVAZUVIUOZVJZUIUVMVDZVKZU
          HJVLZUGNVDZAUWAUGNAUVDNUOZVKZUVEHVEZUJVAZUOZUWFFVEZVSVMZVKZUJIVLZUWAU
          WDHEIVNUNUOZUWEIVOZUOZUWKAUWLUWCRVPAUWCUVEDUOZUWNANDUVDKAUUPUUQUBUUSV
          QZVRADUWMUVEHAUWLHEIUMUNUODUWMHUPREHIVTHEIDUWMPUWMWAZURUTVRWBUJBCEUWE
          FGHIUWMOUFUWQWCWDUWDUWJUWAUJIAUWCUWFIUOZUWJUWAWEAUWCUWRVKZVKZUWGUWIUW
          AUWIUKVAZUWHUOZUKWFUWTUWGVKZUWAUKUWHWGUXCUXBUWAUKUWTUWGUXBUWAAUWSUWGU
          XBVKZUWAAUWSUXDVKZVKZUVNUVMOVAZWHZJUXGWIUNWMUOZWJZUHJVLZOKWKUVEULVAUO
          ULUXAWLZWNZWOZVLZUWAUXFJWMWPUOZUXMJUOZUVDUXMUOZUXOAUXPUXETVPUXFUUPUXL
          EUOUXQAUUPUXEUBVPUXFUXAEUXLUXFUXBUXAEWHAUWSUWGUXBWQZBCEFUXAUWFGHIOUFW
          RVQUXFUXLUXAUOZUVEUXLUOZUXFUWLUXBUWOUWGUXTUYAVKAUWLUXERVPUXSUXFNDUVDK
          AUUQUXEUWPVPZAUWCUWRUXDWSZXCAUWSUWGUXBWTZULBCUVEDEFUXAUWFGHIUXLOUFPUX
          LWAXAXBZXDZXEUXLKJEXFWDUXFUXRUWCUYAUYCUXFUXTUYAUYEXGUXFUUQUURUXRUWCUY
          AVKVJUYBUUTNUVDUXLKXLUTXHUHWMUVDUXMJOXIXJUXFUXKUWAOUXNUXFUXGUXNUOZVKU
          XJUVTUHJUXFUYGUVMJUOZUXJUVTWEUXFUYGUYHVKZUXJUVTUXFUYIUXJVKZVKZUVNUVSU
          VNUXHUXIUYIUXFXKUYKUVRUIUVMUXFUYJUVPUVMUOZUVRAUXEUYJUYLVKZUVRAUXEUYMV
          KZVKZUVOUVQAUYNBCDEUVDUVPFUXAUWFGHUXGIJKLMUXLUVDNOPQRSTUAUBUCUDUEUFUY
          NUXBAUWSUWGUXBUYMXMXNZAUXEUXTUYMUYFXOZUYOUXGUXMUYMUYGAUXEUYGUYHUXJUYL
          XPXQXRZUYMUXIAUXEUVNUXHUXIUYIUYLXTXQZUYOUVMUXGUVDUYMUXHAUXEUVNUXHUXIU
          YIUYLYAXQZAUXEUYJUVNUYLUXEUYJVKUVNAUVNUXHUXIUYIUXEXKXNYBXEZVUAUYOUVMU
          XGUVPUYTAUXEUYJUYLWQXEZAUXEUWGUYMUYDXOZXSAUYNBCDEUVPUVDFUXAUWFGHUXGIJ
          KLMUXLUVDNOPQRSTUAUBUCUDUEUFUYPUYQUYRUYSVUAVUBVUAVUCXSYCYIYIYDYEYFYIY
          GYHYJYIYFYKYLYMYIYHYJYDAJYNUOZUVINWHUVLUWBVJAJWMUOVUDSJYOVQAUVIUVHNAU
          URUVBUVIUVHVBUVAUVCUGNKLYPWDZUVGUGNYQYSUGUHUIUVIJNQUUAWDUUBZYTAUVIMAM
          UVHUVIAMNUOMKVEZMLVEZVBZMUVHUOUAUEUVGVUIUGMNUVDMVBUVEVUGUVFVUHUVDMKYR
          UVDMLYRUUCUUDUUEVUEUUIUUFAUVKUVJUVIJUVJUUGVUFYTUUJVUEUUHUVGUGNUUKUULU
          UMUUN $.
      $}

      $( A lift of a continuous function from a connected and locally connected
         space over a covering map is unique when it exists.  (Contributed by
         Mario Carneiro, 10-Mar-2015.) $)
      cvmliftmoi $p |- ( ph -> M = N ) $=
        ( vw vr vk vs vu vv vb vm cv cuni ccnv cima wceq cin csn cdif wral cres
        c0 crest co chmeo wcel wa cpw crab cmpt eqid cvmscbv cvmliftmolem2 ) AU
        AUBBCUCEUDUIZUJDUKUCUIZULUMUEUIZUFUIUNUSUMUFVKVMUOUPUQDVMURCVMUTVAEVLUT
        VAVBVAVCVDUEVKUQVDUDCVEUSUOUPVFVGZUGDEFGHIJUHKLMNOPQRSTUFUECVNUCDEUDUGU
        HUBUAVNVHVIVJ $.
    $}

    cvmliftmo.g $e |- ( ph -> G e. ( K Cn J ) ) $.
    cvmliftmo.p $e |- ( ph -> P e. B ) $.
    cvmliftmo.e $e |- ( ph -> ( F ` P ) = ( G ` O ) ) $.
    $( A lift of a continuous function from a connected and locally connected
       space over a covering map is unique when it exists.  (Contributed by
       Mario Carneiro, 10-Mar-2015.)  (Revised by NM, 17-Jun-2017.) $)
    cvmliftmo $p |- ( ph ->
        E* f e. ( K Cn C ) ( ( F o. f ) = G /\ ( f ` O ) = P ) ) $=
      ( vg cv ccom wceq cfv wa weq wi ccn co wral wrmo wcel ccvm ad2antrr cconn
      cnlly simplrl simplrr simprll simprrl simprlr simprrr cvmliftmoi ex coeq2
      eqtr4d ralrimivva eqeq1d fveq1 anbi12d rmo4 sylibr ) AFEUBZUCZGUDZJVNUEZD
      UDZUFZFUAUBZUCZGUDZJVTUEZDUDZUFZUFZEUAUGZUHZUAICUIUJZUKEWIUKVSEWIULAWHEUA
      WIWIAVNWIUMZVTWIUMZUFZUFZWFWGWMWFUFZBCFHIVNVTJKLMAFCHUNUJUMWLWFNUOAIUPUMW
      LWFOUOAIUPUQUMWLWFPUOAJKUMWLWFQUOAWJWKWFURAWJWKWFUSWNVOGWAWMVPVRWEUTWMVSW
      BWDVAVGWNVQDWCWMVPVRWEVBWMVSWBWDVCVGVDVEVHVSWEEUAWIWGVPWBVRWDWGVOWAGVNVTF
      VFVIWGVQWCDJVNVTVJVIVKVLVM $.
  $}

  ${
    $d b v y z B $.  $d a b c f g j k m n s t u v w x y z F $.  $d n y z L $.
    $d f y K $.  $d a b c j k m s u v x y z M $.  $d b f g k m n u v x z P $.
    $d a b c f g j k n s u v y z C $.  $d a f g j n s x y z ph $.  $d z ps $.
    $d b c k m n u v x y z N $.  $d a b f g j k n s u v x z S $.  $d a j X $.
    $d a b f g j k m n s t u v w x y z G $.  $d a b c j k m s u v x y z T $.
    $d a b c f g j k n s u v x z J $.  $d b c k m n u v x y z Q $.
    $d k m x z W $.
    cvmliftlem.1 $e |- S = ( k e. J |->
      { s e. ( ~P C \ { (/) } ) | ( U. s = ( `' F " k ) /\
        A. u e. s ( A. v e. ( s \ { u } ) ( u i^i v ) = (/) /\
           ( F |` u ) e. ( ( C |`t u ) Homeo ( J |`t k ) ) ) ) } ) $.
    cvmliftlem.b $e |- B = U. C $.
    cvmliftlem.x $e |- X = U. J $.
    cvmliftlem.f $e |- ( ph -> F e. ( C CovMap J ) ) $.
    cvmliftlem.g $e |- ( ph -> G e. ( II Cn J ) ) $.
    cvmliftlem.p $e |- ( ph -> P e. B ) $.
    cvmliftlem.e $e |- ( ph -> ( F ` P ) = ( G ` 0 ) ) $.
    ${
      cvmliftlem.n $e |- ( ph -> N e. NN ) $.
      cvmliftlem.t $e |- ( ph ->
        T : ( 1 ... N ) --> U_ j e. J ( { j } X. ( S ` j ) ) ) $.
      cvmliftlem.a $e |- ( ph -> A. k e. ( 1 ... N )
        ( G " ( ( ( k - 1 ) / N ) [,] ( k / N ) ) ) C_ ( 1st ` ( T ` k ) ) ) $.
      cvmliftlem.l $e |- L = ( topGen ` ran (,) ) $.
      ${
        cvmliftlem1.m $e |- ( ( ph /\ ps ) -> M e. ( 1 ... N ) ) $.
        $( Lemma for ~ cvmlift .  In ~ cvmliftlem15 , we picked an ` N ` large
           enough so that the sections ` ( G " [ ( k - 1 ) / N , k / N ] ) `
           are all contained in an even covering, and the function ` T `
           enumerates these even coverings.  So ` 1st `` ( T `` M ) ` is a
           neighborhood of ` ( G " [ ( M - 1 ) / N , M / N ] ) ` , and
           ` 2nd `` ( T `` M ) ` is an even covering of ` 1st `` ( T `` M ) ` ,
           which is to say a disjoint union of open sets in ` C ` whose image
           is ` 1st `` ( T `` M ) ` .  (Contributed by Mario Carneiro,
           14-Feb-2015.) $)
        cvmliftlem1 $p |- ( ( ph /\ ps ) ->
          ( 2nd ` ( T ` M ) ) e. ( S ` ( 1st ` ( T ` M ) ) ) ) $=
          ( wa cfv c1st c2nd cop csn cxp ciun wcel wrel wceq relxp rgenw reliun
          cv wral mpbir c1 co wf adantr ffvelcdmd 1st2nd sylancr eqeltrrd fveq2
          cfz opeliunxp2 simprbi syl ) ABULZPIUMZUNUMZWCUOUMZUPZJNJVFZUQZWGHUMZ
          URZUSZUTZWEWDHUMZUTZWBWCWFWKWBWKVAZWCWKUTWCWFVBWOWJVAZJNVGWPJNWHWIVCV
          DJNWJVEVHWBVIQVRVJZWKPIAWQWKIVKBUHVLUKVMZWCWKVNVOWRVPWLWDNUTWNJNWIWDW
          EWMWGWDHVQVSVTWA $.

        cvmliftlem3.3 $e |- W = ( ( ( M - 1 ) / N ) [,] ( M / N ) ) $.
        $( Lemma for ~ cvmlift . ` W = [ ( k - 1 ) / N , k / N ] ` is a subset
           of ` [ 0 , 1 ] ` for each ` M e. ( 1 ... N ) ` .  (Contributed by
           Mario Carneiro, 16-Feb-2015.) $)
        cvmliftlem2 $p |- ( ( ph /\ ps ) -> W C_ ( 0 [,] 1 ) ) $=
          ( wa c1 cmin co cdiv cicc cc0 cr wcel cle wbr wss 0red clt cfz elfznn
          1red cn syl nnred peano2rem cn0 nnm1nn0 adantr nngt0d divge0 syl22anc
          nn0ge0d cmul elfzle2 nncnd mulridd breqtrrd ledivmul syl112anc mpbird
          wb iccss eqsstrid ) ABUNZRPUOUPUQZQURUQZPQURUQZUSUQZUTUOUSUQZUMWMUTVA
          VBUOVAVBZUTWOVCVDZWPUOVCVDZWQWRVEWMVFWMVJZWMWNVAVBZUTWNVCVDQVAVBZUTQV
          GVDZWTWMPVAVBZXCWMPWMPUOQVHUQVBZPVKVBZULPQVIVLZVMZPVNVLWMWNWMXHWNVOVB
          XIPVPVLWAWMQAQVKVBBUHVQZVMZWMQXKVRZWNQVSVTWMXAPQUOWBUQZVCVDZWMPQXNVCW
          MXGPQVCVDULPUOQWCVLWMQWMQXKWDWEWFWMXFWSXDXEXAXOWJXJXBXLXMPUOQWGWHWIUT
          UOWOWPWKVTWL $.

        cvmliftlem3.m $e |- ( ( ph /\ ps ) -> A e. W ) $.
        $( Lemma for ~ cvmlift .  Since ` 1st `` ( T `` M ) ` is a neighborhood
           of ` ( G " W ) ` , every element ` A e. W ` satisfies
           ` ( G `` A ) e. ( 1st `` ( T `` M ) ) ` .  (Contributed by Mario
           Carneiro, 16-Feb-2015.) $)
        cvmliftlem3 $p |- ( ( ph /\ ps ) ->
          ( G ` A ) e. ( 1st ` ( T ` M ) ) ) $=
          ( wa cima cfv c1st c1 cfz co wcel cmin cdiv cicc wss wral adantr wceq
          cv oveq1 oveq1d oveq12d eqtr4di imaeq2d 2fveq3 sseq12d rspcv sylc cdm
          wfun wi cc0 wf cii ccn iiuni cnf syl ffund cvmliftlem2 fdmd funfvima2
          sseqtrrd syl2anc mpd sseldd ) ABUPZNSUQZQJURUSURZENURZWSQUTRVAVBZVCNL
          VKZUTVDVBZRVEVBZXDRVEVBZVFVBZUQZXDJURUSURZVGZLXCVHZWTXAVGZUMAXLBUKVIX
          KXMLQXCXDQVJZXIWTXJXAXNXHSNXNXHQUTVDVBZRVEVBZQRVEVBZVFVBSXNXFXPXGXQVF
          XNXEXORVEXDQUTVDVLVMXDQRVEVLVNUNVOVPXDQUSJVQVRVSVTWSESVCZXBWTVCZUOWSN
          WBSNWAZVGXRXSWCWSWDUTVFVBZTNAYATNWEZBANWFOWGVBVCYBUFNWFOYATWHUDWIWJVI
          ZWKWSSYAXTABCDFGHIJKLMNOPQRSTUAUBUCUDUEUFUGUHUIUJUKULUMUNWLWSYATNYCWM
          WOSENWNWPWQWR $.
      $}

      cvmliftlem.q $e |- Q = seq 0 ( ( x e. _V , m e. NN |->
        ( z e. ( ( ( m - 1 ) / N ) [,] ( m / N ) ) |->
          ( `' ( F |` ( iota_ b e. ( 2nd ` ( T ` m ) )
            ( x ` ( ( m - 1 ) / N ) ) e. b ) ) ` ( G ` z ) ) ) ) ,
          ( ( _I |` NN ) u. { <. 0 , { <. 0 , P >. } >. } ) ) $.
      $( Lemma for ~ cvmlift .  The function ` Q ` will be our lifted path,
         defined piecewise on each section ` [ ( M - 1 ) / N , M / N ] ` for
         ` M e. ( 1 ... N ) ` .  For ` M = 0 ` , it is a "seed" value which
         makes the rest of the recursion work, a singleton function mapping
         ` 0 ` to ` P ` .  (Contributed by Mario Carneiro, 15-Feb-2015.) $)
      cvmliftlem4 $p |- ( Q ` 0 ) = { <. 0 , P >. } $=
        ( cc0 cfv cop csn cid cn cres cun cvv cv c1 cmin co cdiv cicc wcel c2nd
        crio ccnv cmpt cmpo cseq fveq1i cz wceq seq1 ax-mp eqtri wfn cin fnresi
        0z c0 wa c0ex snex fnsn 0nnn disjsn mpbir snid pm3.2i fvun2 mp3an fvsn
        wn ) UOIUPZUOUOUOHUQZURZUQURZUPZXCXAUOUSUTVAZXDVBZUPZXEXAUOBNVCUTCNVDZV
        EVFVGSVHVGZXISVHVGVIVGCVDPUPOXJBVDUPUBVDVJUBXIKUPVKUPVLVAVMUPVNVOZXGUOV
        PZUPZXHUOIXLUNVQUOVRVJXMXHVSWFXKXGUOVTWAWBXFUTWCXDUOURZWCUTXNWDWGVSZUOX
        NVJZWHXHXEVSUTWEUOXCWIXBWJZWKXOXPXOUOUTVJWTWLUTUOWMWNUOWIWOWPUTXNXFXDUO
        WQWRWBUOXCWIXQWSWB $.

      ${
        cvmliftlem5.3 $e |- W = ( ( ( M - 1 ) / N ) [,] ( M / N ) ) $.
        $( Lemma for ~ cvmlift .  Definition of ` Q ` at a successor.  This is
           a function defined on ` W ` as ` ``' ( T |`` I ) o. G ` where ` I `
           is the unique covering set of ` 2nd `` ( T `` M ) ` that contains
           ` Q ( M - 1 ) ` evaluated at the last defined point, namely
           ` ( M - 1 ) / N ` (note that for ` M = 1 ` this is using the seed
           value ` Q ( 0 ) ( 0 ) = P ` ).  (Contributed by Mario Carneiro,
           15-Feb-2015.) $)
        cvmliftlem5 $p |- ( ( ph /\ M e. NN ) -> ( Q ` M ) = ( z e. W |->
            ( `' ( F |` ( iota_ b e. ( 2nd ` ( T ` M ) )
        ( ( Q ` ( M - 1 ) ) ` ( ( M - 1 ) / N ) ) e. b ) ) ` ( G ` z ) ) ) ) $=
          ( cn wcel wa cfv c1 cmin co cid cres cc0 cop csn cun cvv cv cdiv cicc
          c2nd crio ccnv cmpt cmpo cseq cz caddc cuz wceq 0z simpr 1e0p1 fveq2i
          nnuz eqtri eleqtrdi seqm1 sylancr fveq1i oveq1i 3eqtr4g cin c0 disjsn
          wn 0nnn mpbir fnresi c0ex snex fnsn fvun1 mp3an12 fvresi adantl eqtrd
          oveq2d fvexd oveq1d oveq12d eqtr4di fveq2d fveq12d eleq1d riotaeqbidv
          simpl reseq2d cnveqd fveq1d mpteq12dv eqid eqeltri mptex ovmpoa sylan
          wfn ovex 3eqtrd ) ASURUSZUTZSIVAZSVBVCVDZIVAZSVEURVFZVGVGHVHZVIZVHVIZ
          VJZVAZBNVKURCNVLZVBVCVDZTVMVDZUUETVMVDZVNVDZCVLPVAZOUUGBVLZVAZUDVLZUS
          ZUDUUEKVAZVOVAZVPZVFZVQZVAZVRZVSZVDZYRSUVBVDZCUAUUJOYQTVMVDZYRVAZUUMU
          SZUDSKVAZVOVAZVPZVFZVQZVAZVRZYOSUVBUUCVGVTZVAZYQUVOVAZUUDUVBVDZYPUVCY
          OVGWAUSSVGVBWBVDZWCVAZUSUVPUVRWDWEYOSURUVTAYNWFZURVBWCVAUVTWIVBUVSWCW
          GWHWJWKUVBUUCVGSWLWMSIUVOUPWNYRUVQUUDUVBYQIUVOUPWNWOWPYOUUDSYRUVBYOUU
          DSYSVAZSYOURVGVIZWQWRWDZYNUUDUWBWDZUWDVGURUSWTXAURVGWSXBUWAYSURYKUUBU
          WCYKUWDYNUTUWEURXCVGUUAXDYTXEXFURUWCYSUUBSXGXHWMYNUWBSWDAURSXIXJXKXLA
          YRVKUSYNUVDUVNWDAYQIXMBNYRSVKURUVAUVNUVBUUKYRWDZUUESWDZUTZCUUIUUTUAUV
          MUWHUUIUVESTVMVDZVNVDZUAUWHUUGUVEUUHUWIVNUWHUUFYQTVMUWHUUESVBVCUWFUWG
          WFZXNXNZUWHUUESTVMUWKXNXOUQXPUWHUUJUUSUVLUWHUURUVKUWHUUQUVJOUWHUUNUVG
          UDUUPUVIUWHUUOUVHVOUWHUUESKUWKXQXQUWHUULUVFUUMUWHUUGUVEUUKYRUWFUWGYAU
          WLXRXSXTYBYCYDYEUVBYFCUAUVMUAUWJVKUQUVEUWIVNYLYGYHYIYJYM $.

        ${
          cvmliftlem6.1 $e |- ( ( ph /\ ps ) -> M e. ( 1 ... N ) ) $.
          cvmliftlem6.2 $e |- ( ( ph /\ ps ) ->
            ( ( Q ` ( M - 1 ) ) ` ( ( M - 1 ) / N ) ) e.
              ( `' F " { ( G ` ( ( M - 1 ) / N ) ) } ) ) $.
          $( Lemma for ~ cvmlift .  Induction step for ~ cvmliftlem7 .
             Assuming that ` Q ( M - 1 ) ` is defined at ` ( M - 1 ) / N ` and
             is a preimage of ` G ( ( M - 1 ) / N ) ` , the next segment
             ` Q ( M ) ` is also defined and is a function on ` W ` which is a
             lift ` G ` for this segment.  This follows explicitly from the
             definition ` Q ( M ) = ``' ( F |`` I ) o. G ` since ` G ` is in
             ` 1st `` ( F `` M ) ` for the entire interval so that
             ` ``' ( F |`` I ) ` maps this into ` I ` and ` F o. Q ` maps back
             to ` G ` .  (Contributed by Mario Carneiro, 16-Feb-2015.) $)
          cvmliftlem6 $p |- ( ( ph /\ ps ) ->
            ( ( Q ` M ) : W --> B /\ ( F o. ( Q ` M ) ) = ( G |` W ) ) ) $=
            ( vy wa cfv wf ccom cres wceq cv cmin cdiv wcel c2nd crio ccnv cmpt
            c1 cuni wss c1st cfz adantrr cvmliftlem1 cvmsss syl ccvm adantr csn
            co cima wfn wb ccn cvmcn cnf 3syl fniniseg mpbid simpld simprd cicc
            ffn cxr cle wbr cr cn elfznn nnred peano2rem nndivred rexrd clt cc0
            ltm1d nngt0d ltdiv1 syl112anc syl3anc eleqtrrdi cvmliftlem3 eqeltrd
            lbicc2 eqid cvmsiota syl13anc sseldd elssuni sseqtrrdi wf1o cvmsf1o
            ltled f1ocnv f1of simprr ffvelcdmd anassrs fmpttd fvres feqmptd cii
            cvmliftlem5 syldan feq1d f1ocnvfv2 syl2anc 3eqtr2rd mpteq2dva fveq2
            mpbird fmptco iiuni cvmliftlem2 fssresd 3eqtr4d jca ) ABVBZUBGTJVCZ
            VDZPUUQVEZQUBVFZVGUUPUURUBGDUBDVHZQVCZPTVPVIWHZUAVJWHZUVCJVCVCZUEVH
            VKUETLVCZVLVCZVMZVFZVNZVCZVOZVDUUPDUBUVKGABUVAUBVKZUVKGVKABUVMVBZVB
            ZUVHGUVKUVOUVHHVQZGUVOUVHHVKUVHUVPVRUVOUVGHUVHUVOUVGUVFVSVCZKVCVKZU
            VGHVRAUVNEFGHIKLMNPQRSTUAUCUDUFUGUHUIUJUKULUMUNUOUPABTVPUAVTWHVKZUV
            MUSWAZWBZEFHKUVGUVQNPRUDUFWCWDUVOUVHUVGVKZUVEUVHVKZUVOPHRWEWHVKZUVR
            UVEGVKZUVEPVCZUVQVKUWBUWCVBAUWDUVNUIWFZUWAUVOUWEUWFUVDQVCZVGZUVOUVE
            PVNUWHWGWIVKZUWEUWIVBZABUWJUVMUTWAUVOGUCPVDZPGWJUWJUWKWKUVOUWDPHRWL
            WHVKZUWLUWGHPRWMZPHRGUCUGUHWNZWOGUCPXAGUWHUVEPWPWOWQZWRUVOUWFUWHUVQ
            UVOUWEUWIUWPWSAUVNEFUVDGHIKLMNPQRSTUAUBUCUDUFUGUHUIUJUKULUMUNUOUPUV
            TURUVOUVDUVDTUAVJWHZWTWHZUBUVOUVDXBVKUWQXBVKUVDUWQXCXDUVDUWRVKUVOUV
            DUVOUVCUAUVOTXEVKZUVCXEVKZUVOTUVOUVSTXFVKZUVTTUAXGZWDXHZTXIWDZAUAXF
            VKUVNUMWFZXJZXKUVOUWQUVOTUAUXCUXEXJZXKUVOUVDUWQUXFUXGUVOUVCTXLXDZUV
            DUWQXLXDZUVOTUXCXNUVOUWTUWSUAXEVKXMUAXLXDUXHUXIWKUXDUXCUVOUAUXEXHUV
            OUAUXEXOUVCTUAXPXQWQYKUVDUWQYBXRURXSXTYAUEEFUVEGHKUVGUVQNPRUVHUDUFU
            GUVHYCYDYEWRZYFUVHHYGWDUGYHUVOUVQUVHUVBUVJUVOUVHUVQUVIYIZUVQUVHUVJY
            IUVQUVHUVJVDUVOUWDUVRUWBUXKUWGUWAUXJEFUVHHKUVGUVQNPRUDUFYJXRZUVHUVQ
            UVIYLUVQUVHUVJYMWOAUVNEFUVAGHIKLMNPQRSTUAUBUCUDUFUGUHUIUJUKULUMUNUO
            UPUVTURABUVMYNZXTZYOZYFYPZYQUUPUBGUUQUVLABUXAUUQUVLVGUUPUVSUXAUSUXB
            WDACDEFGHIJKLMNOPQRSTUAUBUCUDUEUFUGUHUIUJUKULUMUNUOUPUQURUUAUUBZUUC
            UUIUUPDUBUVKPVCZVODUBUVAUUTVCZVOUUSUUTUUPDUBUXRUXSABUVMUXRUXSVGUVOU
            XSUVBUVKUVIVCZUXRUVOUVMUXSUVBVGUXMUVAUBQYRWDUVOUXKUVBUVQVKUXTUVBVGU
            XLUXNUVHUVQUVBUVIUUDUUEUVOUVKUVHVKUXTUXRVGUXOUVKUVHPYRWDUUFYPUUGUUP
            DVAUBGUVKVAVHZPVCUXRUUQPUXPUXQUUPVAGUCPAUWLBAUWDUWMUWLUIUWNUWOWOWFY
            SUYAUVKPUUHUUJUUPDUBUCUUTUUPXMVPWTWHZUCUBQAUYBUCQVDZBAQYTRWLWHVKUYC
            UJQYTRUYBUCUUKUHWNWDWFABEFGHIKLMNPQRSTUAUBUCUDUFUGUHUIUJUKULUMUNUOU
            PUSURUULUUMYSUUNUUO $.
        $}

        $( Lemma for ~ cvmlift .  Prove by induction that every ` Q ` function
           is well-defined (we can immediately follow this theorem with
           ~ cvmliftlem6 to show functionality and lifting of ` Q ` ).
           (Contributed by Mario Carneiro, 14-Feb-2015.) $)
        cvmliftlem7 $p |- ( ( ph /\ M e. ( 1 ... N ) ) ->
          ( ( Q ` ( M - 1 ) ) ` ( ( M - 1 ) / N ) ) e.
            ( `' F " { ( G ` ( ( M - 1 ) / N ) ) } ) ) $=
          ( vy vn c1 cfz co wcel cmin cc0 cdiv cfv ccnv cima wa caddc fzssp1 cc
          csn wceq nncnd adantr ax-1cn npcan sylancl oveq2d sseqtrid cz elfzelz
          simpr wb nnzd elfzm1b syl2anr mpbid sseldd elfznn0 adantl cv wi eleq1
          fveq2 oveq1 fveq12d fvoveq1 sneqd imaeq2d eleq12d imbi12d cvmliftlem4
          cn0 imbi2d cop a1i nnne0d div0d fvsng sylancr eqtrd fveq2d eqtr4d wfn
          0nn0 ccn ccvm cvmcn syl cnf fniniseg mpbir2and cuz eleqtrdi cicc cres
          wf cle wbr cn syl2anc oveq1d cxr nndivred rexrd cr clt ffn eqeltrd id
          3syl a1d nn0uz peano2fzr ex ccom eqid simprlr elfzle2 simprll nn0p1nn
          imim1d elfz5 mpbird simprr nn0cnd 3eltr4d cvmliftlem6 simpld peano2re
          pncan nn0red ltp1d nnred nngt0d ltdiv1 syl112anc ltled ubicc2 syl3anc
          nnuz eleqtrrd ffvelcdmd simprd reseq2d feq2d fvco3 fvres 3eqtr3d expr
          fveq1d animpimp2impd nn0ind impd mpcom syldan ) ASUTTVAVBZVCZSUTVDVBZ
          VETVAVBZVCZUWLTVFVBZUWLIVGZVGZOVHZUWOPVGZVNZVIZVCZAUWKVJZVETUTVDVBZVA
          VBZUWMUWLUXCVEUXDUTVKVBZVAVBUXEUWMVEUXDVLUXCUXFTVEVAUXCTVMVCZUTVMVCZU
          XFTVOAUXGUWKATULVPZVQVRTUTVSVTWAWBUXCUWKUWLUXEVCZAUWKWEUWKSWCVCTWCVCZ
          UWKUXJWFASUTTWDATULWGZSTWHWIWJWKUWLXFVCZAUWNVJUXBUWNUXMAUWLTWLWMUXMAU
          WNUXBAURWNZUWMVCZUXNTVFVBZUXNIVGZVGZUWRUXPPVGZVNZVIZVCZWOZWOAVEUWMVCZ
          VETVFVBZVEIVGZVGZUWRUYEPVGZVNZVIZVCZWOZWOAUSWNZUWMVCZUYMTVFVBZUYMIVGZ
          VGZUWRUYOPVGZVNZVIZVCZWOZWOAUYMUTVKVBZUWMVCZVUCTVFVBZVUCIVGZVGZUWRVUE
          PVGZVNZVIZVCZWOZWOAUWNUXBWOZWOURUSUWLUXNVEVOZUYCUYLAVUNUXOUYDUYBUYKUX
          NVEUWMWPVUNUXRUYGUYAUYJVUNUXPUYEUXQUYFUXNVEIWQUXNVETVFWRWSVUNUXTUYIUW
          RVUNUXSUYHUXNVETPVFWTXAXBXCXDXGUXNUYMVOZUYCVUBAVUOUXOUYNUYBVUAUXNUYMU
          WMWPVUOUXRUYQUYAUYTVUOUXPUYOUXQUYPUXNUYMIWQUXNUYMTVFWRWSVUOUXTUYSUWRV
          UOUXSUYRUXNUYMTPVFWTXAXBXCXDXGUXNVUCVOZUYCVULAVUPUXOVUDUYBVUKUXNVUCUW
          MWPVUPUXRVUGUYAVUJVUPUXPVUEUXQVUFUXNVUCIWQUXNVUCTVFWRWSVUPUXTVUIUWRVU
          PUXSVUHUXNVUCTPVFWTXAXBXCXDXGUXNUWLVOZUYCVUMAVUQUXOUWNUYBUXBUXNUWLUWM
          WPVUQUXRUWQUYAUXAVUQUXPUWOUXQUWPUXNUWLIWQUXNUWLTVFWRWSVUQUXTUWTUWRVUQ
          UXSUWSUXNUWLTPVFWTXAXBXCXDXGAUYKUYDAUYGHUYJAUYGVEVEHXHVNZVGZHAUYEVEUY
          FVURUYFVURVOAABCDEFGHIJKLMNOPQRTUBUCUDUEUFUGUHUIUJUKULUMUNUOUPXEXIATU
          XIATULXJXKZWSAVEXFVCHFVCZVUSHVOXRUJVEHXFFXLXMXNAHUYJVCZVVAHOVGZUYHVOZ
          UJAVVCVEPVGUYHUKAUYEVEPVUTXOXPAOFXQZVVBVVAVVDVJWFAOGQXSVBVCZFUBOYJVVE
          AOGQXTVBVCVVFUHGOQYAYBOGQFUBUFUGYCFUBOUUAUUDZFUYHHOYDYBYEUUBUUEUYMXFV
          CZAVUBVUDVUKVUAAVVHVJZVUDUYNVUAVVIUYMVEYFVGZVCZVUDUYNWOVVHVVKAVVHUYMX
          FVVJVVHUUCUUFYGWMVVKVUDUYNUYMVETUUGUUHYBUUOAVVHVUDVJZVUAVUKAVVLVUAVJZ
          VJZVUKVUGFVCZVUGOVGZVUHVOZVVNVUCUTVDVBZTVFVBZVUEYHVBZFVUEVUFVVNVVTFVU
          FYJZOVUFUUIZPVVTYIZVOZAVVMBCDEFGHIJKLMNOPQRVUCTVVTUBUCUDUEUFUGUHUIUJU
          KULUMUNUOUPVVTUUJVVNVUCUWJVCZVUCTYKYLZVVNVUDVWFAVVHVUDVUAUUKVUCVETUUL
          YBVVNVUCUTYFVGZVCUXKVWEVWFWFVVNVUCYMVWGVVNVVHVUCYMVCAVVHVUDVUAUUMZUYM
          UUNYBUVNYGAUXKVVMUXLVQVUCUTTUUPYNUUQVVNUYQUYTVVSVVRIVGZVGUWRVVSPVGZVN
          ZVIAVVLVUAUURVVNVVSUYOVWIUYPVVNVVRUYMIVVNUYMVMVCUXHVVRUYMVOVVNUYMVWHU
          USVRUYMUTUVDVTZXOVVNVVRUYMTVFVWLYOZWSVVNVWKUYSUWRVVNVWJUYRVVNVVSUYOPV
          WMXOXAXBUUTUVAZUVBZVVNVUEUYOVUEYHVBZVVTVVNUYOYPVCVUEYPVCUYOVUEYKYLVUE
          VWPVCZVVNUYOVVNUYMTVVNUYMVWHUVEZATYMVCVVMULVQZYQZYRVVNVUEVVNVUCTVVNUY
          MYSVCZVUCYSVCZVWRUYMUVCYBZVWSYQZYRVVNUYOVUEVWTVXDVVNUYMVUCYTYLZUYOVUE
          YTYLZVVNUYMVWRUVFVVNVXAVXBTYSVCVETYTYLVXEVXFWFVWRVXCVVNTVWSUVGVVNTVWS
          UVHUYMVUCTUVIUVJWJUVKUYOVUEUVLUVMZVVNVVSUYOVUEYHVWMYOZUVOUVPVVNVUEVWB
          VGZVUEPVWPYIZVGZVVPVUHVVNVUEVWBVXJVVNVWBVWCVXJVVNVWAVWDVWNUVQVVNVVTVW
          PPVXHUVRXNUWDVVNVWPFVUFYJZVWQVXIVVPVOVVNVWAVXLVWOVVNVVTVWPFVUFVXHUVSW
          JVXGVWPFVUEOVUFUVTYNVVNVWQVXKVUHVOVXGVUEVWPPUWAYBUWBVVNVVEVUKVVOVVQVJ
          WFAVVEVVMVVGVQFVUHVUGOYDYBYEUWCUWEUWFUWGUWHUWI $.

        $( Lemma for ~ cvmlift .  The functions ` Q ` are continuous functions
           because they are defined as ` ``' ( F |`` I ) o. G ` where ` G ` is
           continuous and ` ( F |`` I ) ` is a homeomorphism.  (Contributed by
           Mario Carneiro, 16-Feb-2015.) $)
        cvmliftlem8 $p |- ( ( ph /\ M e. ( 1 ... N ) ) ->
          ( Q ` M ) e. ( ( L |`t W ) Cn C ) ) $=
          ( c1 cfz co wcel wa cfv cv cmin cdiv c2nd crio cres ccnv crest ccn cn
          cmpt wceq elfznn cvmliftlem5 sylan2 ccvm ctop adantr cvmtop1 cnrest2r
          wss 3syl c1st cr ctopon cioo crn ctg retopon eqeltri cicc cvmliftlem2
          cc0 simpr unitssre sstrdi resttopon sylancr cii eqid iitopon wf iiuni
          a1i cnf syl feqmptd eqeltrrd cnmpt1res dfii2 oveq1i cvv retop restabs
          eqtr4i ovexd syl3anc eqtrid oveq1d eleqtrd wb cvmtop2 toptopon simprl
          sylib simprr cvmliftlem3 anassrs mpbid simpld cxr wbr nnred rexrd clt
          nndivred eqeltrd fmpttd frnd cuni cvmliftlem1 cvmsrcl elssuni cnrest2
          sseqtrrdi chmeo csn cima cvmliftlem7 wfn cvmcn fniniseg simprd adantl
          ffn cle peano2rem ltm1d nngt0d ltdiv1 syl112anc ltled lbicc2 cvmsiota
          eleqtrrdi syl13anc cvmshmeo syl2anc hmeocnvcn cnmpt11f sseldd ) ASURT
          USUTVAZVBZSIVCZCUACVDZPVCZOSURVEUTZTVFUTZUVTIVCVCZUDVDVAUDSKVCZVGVCZV
          HZVIZVJZVCVNZRUAVKUTZGVLUTZUVOASVMVAZUVQUWHVOSTVPZABCDEFGHIJKLMNOPQRS
          TUAUBUCUDUEUFUGUHUIUJUKULUMUNUOUPUQVQVRUVPUWIGUWEVKUTZVLUTZUWJUWHUVPO
          GQVSUTVAZGVTVAUWNUWJWDAUWOUVOUHWAZGOQWBUWEUWIGWCWEUVPCUVSUWGUWIQUWCWF
          VCZVKUTZUWMUAUVPRWGWHVCZVAUAWGWDUWIUAWHVCVARWIWJWKVCZUWSUOWLWMUVPUAWP
          URWNUTZWGAUVODEFGHJKLMOPQRSTUAUBUCUEUFUGUHUIUJUKULUMUNUOAUVOWQZUQWOZW
          RWSUARWGWTXAUVPCUAUVSVNZUWIQVLUTZVAZUXDUWIUWRVLUTVAZUVPUXDXBUAVKUTZQV
          LUTUXEUVPCUVSXBUXHQUXAUAUXHXCXBUXAWHVCVAUVPXDXGUXCUVPPCUXAUVSVNXBQVLU
          TZUVPCUXAUBPUVPPUXIVAZUXAUBPXEAUXJUVOUIWAZPXBQUXAUBXFUGXHXIXJUXKXKXLU
          VPUXHUWIQVLUVPUXHRUXAVKUTZUAVKUTZUWIXBUXLUAVKXBUWTUXAVKUTUXLXMRUWTUXA
          VKUOXNXRXNUVPRVTVAZUAUXAWDUXAXOVAUXMUWIVOUXNUVPRUWTVTUOXPWMXGUXCUVPWP
          URWNXSUAUXARVTXOXQXTYAYBYCUVPQUBWHVCVAZUXDWJUWQWDUWQUBWDUXFUXGYDUVPQV
          TVAZUXOUVPUWOUXPUWPGOQYEXIQUBUGYFYHUVPUAUWQUXDUVPCUAUVSUWQAUVOUVRUAVA
          ZUVSUWQVAAUVOUXQVBDEUVRFGHJKLMOPQRSTUAUBUCUEUFUGUHUIUJUKULUMUNUOAUVOU
          XQYGUQAUVOUXQYIYJYKUUAUUBUVPUWQQUUCZUBUVPUWDUWQJVCVAZUWQQVAUWQUXRWDAU
          VODEFGHJKLMOPQRSTUBUCUEUFUGUHUIUJUKULUMUNUOUXBUUDZDEGJUWDUWQMOQUCUEUU
          EUWQQUUFWEUGUUHUWQUXDUWIQUBUUGXTYLUVPUWFUWMUWRUUIUTVAZUWGUWRUWMVLUTVA
          UVPUXSUWEUWDVAZUYAUXTUVPUYBUWBUWEVAZUVPUWOUXSUWBFVAZUWBOVCZUWQVAUYBUY
          CVBUWPUXTUVPUYDUYEUWAPVCZVOZUVPUWBOVJUYFUUJUUKVAZUYDUYGVBZABCDEFGHIJK
          LMNOPQRSTUAUBUCUDUEUFUGUHUIUJUKULUMUNUOUPUQUULUVPFUBOXEZOFUUMUYHUYIYD
          UVPUWOOGQVLUTVAUYJUWPGOQUUNOGQFUBUFUGXHWEFUBOUURFUYFUWBOUUOWEYLZYMUVP
          UYEUYFUWQUVPUYDUYGUYKUUPAUVODEUWAFGHJKLMOPQRSTUAUBUCUEUFUGUHUIUJUKULU
          MUNUOUXBUQUVPUWAUWASTVFUTZWNUTZUAUVPUWAYNVAUYLYNVAUWAUYLUUSYOUWAUYMVA
          UVPUWAUVPUVTTUVPSWGVAZUVTWGVAZUVPSUVOUWKAUWLUUQYPZSUUTXIZATVMVAUVOULW
          AZYSZYQUVPUYLUVPSTUYPUYRYSZYQUVPUWAUYLUYSUYTUVPUVTSYRYOZUWAUYLYRYOZUV
          PSUYPUVAUVPUYOUYNTWGVAWPTYRYOVUAVUBYDUYQUYPUVPTUYRYPUVPTUYRUVBUVTSTUV
          CUVDYLUVEUWAUYLUVFXTUQUVHYJYTUDDEUWBFGJUWDUWQMOQUWEUCUEUFUWEXCUVGUVIY
          MDEUWEGJUWDUWQMOQUCUEUVJUVKUWFUWMUWRUVLXIUVMUVNYT $.
      $}

      $( Lemma for ~ cvmlift .  The ` Q ( M ) ` functions are defined on almost
         disjoint intervals, but they overlap at the edges.  Here we show that
         at these points the ` Q ` functions agree on their common domain.
         (Contributed by Mario Carneiro, 14-Feb-2015.) $)
      cvmliftlem9 $p |- ( ( ph /\ M e. ( 1 ... N ) ) ->
          ( ( Q ` M ) ` ( ( M - 1 ) / N ) ) =
          ( ( Q ` ( M - 1 ) ) ` ( ( M - 1 ) / N ) ) ) $=
        ( c1 cfz co wcel wa cmin cdiv cfv cv c2nd crio cres ccnv cicc cmpt wceq
        cvv cn elfznn eqid cvmliftlem5 sylan2 simpr fveq2d cxr cle wbr cr nnred
        adantl peano2rem syl adantr rexrd clt ltm1d cc0 nngt0d ltdiv1 syl112anc
        nndivred wb mpbid ltled lbicc2 syl3anc fvmptd ccvm c1st cvmliftlem1 csn
        fvexd cima cvmliftlem7 wf wfn ccn cvmcn cnf 3syl fniniseg simpld simprd
        cvmliftlem3 eqeltrd cvmsiota syl13anc fvres eqtrd wf1o cvmsf1o f1ocnvfv
        ffn wi syl2anc mpd ) ASUPTUQURUSZUTZSUPVAURZTVBURZSIVCZVCYOPVCZOYOYNIVC
        VCZUCVDUSUCSKVCZVEVCZVFZVGZVHZVCZYRYMCYOCVDZPVCZUUCVCZUUDYOSTVBURZVIURZ
        YPVLYLASVMUSZYPCUUIUUGVJVKSTVNZABCDEFGHIJKLMNOPQRSTUUIUAUBUCUDUEUFUGUHU
        IUJUKULUMUNUOUUIVOZVPVQYMUUEYOVKZUTZUUFYQUUCUUNUUEYOPYMUUMVRVSVSYMYOVTU
        SUUHVTUSYOUUHWAWBYOUUIUSYMYOYMYNTYMSWCUSZYNWCUSZYMSYLUUJAUUKWEWDZSWFWGZ
        ATVMUSYLUKWHZWPZWIYMUUHYMSTUUQUUSWPZWIYMYOUUHUUTUVAYMYNSWJWBZYOUUHWJWBZ
        YMSUUQWKYMUUPUUOTWCUSWLTWJWBUVBUVCWQUURUUQYMTUUSWDYMTUUSWMYNSTWNWOWRWSY
        OUUHWTXAZYMYQUUCXGXBYMYRUUBVCZYQVKZUUDYRVKZYMUVEYROVCZYQYMYRUUAUSZUVEUV
        HVKYMUUAYTUSZUVIYMOGQXCURUSZYTYSXDVCZJVCUSZYRFUSZUVHUVLUSUVJUVIUTAUVKYL
        UGWHZAYLDEFGHJKLMOPQRSTUAUBUDUEUFUGUHUIUJUKULUMUNAYLVRZXEZYMUVNUVHYQVKZ
        YMYROVHYQXFXHUSZUVNUVRUTZABCDEFGHIJKLMNOPQRSTUUIUAUBUCUDUEUFUGUHUIUJUKU
        LUMUNUOUULXIYMFUAOXJZOFXKUVSUVTWQYMUVKOGQXLURUSUWAUVOGOQXMOGQFUAUEUFXNX
        OFUAOYHFYQYROXPXOWRZXQYMUVHYQUVLYMUVNUVRUWBXRZAYLDEYOFGHJKLMOPQRSTUUIUA
        UBUDUEUFUGUHUIUJUKULUMUNUVPUULUVDXSXTUCDEYRFGJYTUVLMOQUUAUBUDUEUUAVOYAY
        BZXRZYRUUAOYCWGUWCYDYMUUAUVLUUBYEZUVIUVFUVGYIYMUVKUVMUVJUWFUVOUVQYMUVJU
        VIUWDXQDEUUAGJYTUVLMOQUBUDYFXAUWEUUAUVLYRYQUUBYGYJYKYD $.

      cvmliftlem.k $e |- K = U_ k e. ( 1 ... N ) ( Q ` k ) $.
      ${
        cvmliftlem10.1 $e |- ( ch <-> ( ( n e. NN /\ ( n + 1 ) e. ( 1 ... N ) )
          /\ ( U_ k e. ( 1 ... n ) ( Q ` k ) e.
            ( ( L |`t ( 0 [,] ( n / N ) ) ) Cn C ) /\ ( F o.
        U_ k e. ( 1 ... n ) ( Q ` k ) ) = ( G |` ( 0 [,] ( n / N ) ) ) ) ) ) $.
        $( Lemma for ~ cvmlift .  The function ` K ` is going to be our
           complete lifted path, formed by unioning together all the ` Q `
           functions (each of which is defined on one segment
           ` [ ( M - 1 ) / N , M / N ] ` of the interval).  Here we prove by
           induction that ` K ` is a continuous function and a lift of ` G ` by
           applying ~ cvmliftlem6 , ~ cvmliftlem7 (to show it is a function and
           a lift), ~ cvmliftlem8 (to show it is continuous), and ~ cvmliftlem9
           (to show that different ` Q ` functions agree on the intersection of
           their domains, so that the pasting lemma ~ paste gives that ` K ` is
           well-defined and continuous).  (Contributed by Mario Carneiro,
           14-Feb-2015.) $)
        cvmliftlem10 $p |- ( ph ->
          ( K e. ( ( L |`t ( 0 [,] ( N / N ) ) ) Cn C ) /\
            ( F o. K ) = ( G |` ( 0 [,] ( N / N ) ) ) ) ) $=
          ( vy c1 cfz co wcel cc0 cdiv cicc crest ccn ccom cres wceq wa eluzfz2
          cfv cn syl wi cv ciun caddc eleq1 csn oveq2 eqtrdi fveq2 iunxsn oveq1
          iuneq1d oveq2d oveq1d eleq12d coeq2d reseq2d eqeq12d imbi2d cmin eqid
          anbi12d imbi12d cvmliftlem8 mpdan nncnd simpr cvmliftlem7 cvmliftlem6
          eleqtrd wf simprd eqtrd jca adantl cuni cr wss ccld 0re nnred iccssre
          nndivred sylancr simpld icccld eleqtrrdi cun a1i cle wbr clt wb mpbid
          syl3anc syl2anc ctop eqtr3d feq2d syldan cxr rexrd cvv cuz nnuz cz 1z
          eleqtrdi fzsn ax-mp 1ex eqtr4di eluzfz1 1m1e0 oveq1i nnne0d div0d a1d
          eqtrid elnnuz biimpi peano2fzr ex imim1d simplbi elfznn adantr fveq2i
          cioo crn ctg ssun1 nnnn0d nn0ge0d nngt0d divge0 syl22anc ltp1d ltdiv1
          syl112anc ltled w3a elicc2 mpbir3and iccsplit sseqtrrid unieqi eqtr4i
          uniretop restcldi ssun2 eqeltri restuni cin simprbi cnf mpbird ax-1cn
          retop pncan sylancl cop wfun cdm ffund ssiun2s peano2rem ltm1d ubicc2
          fdmd eleqtrrd funssfv fveq2d fveq12d cvmliftlem9 3eqtr2d opeq2d sneqd
          cc wfn ffnd 0xr fnressn lbicc2 3eqtr4d df-icc xrmaxle xrlemin iftrued
          cif ixxin oveq12d iccid 3eqtrd fresaun fzsuc iunxun ovex uneq2i eqtri
          eqtr2di feq1d reseq1d fresaunres1 restabs 3eltr4d fresaunres2 uneq12d
          paste coundi resundi 3eqtr2rd sylan2br expr animpimp2impd nnind mpcom
          3eqtr4g mpd ) AUBVAUBVBVCZVDZTUAVEUBUBVFVCZVGVCZVHVCZHVIVCZVDZQTVJZRV
          UTVKZVLZVMZAUBVAUUAVOZVDZVURAUBVPVVHUMUUBUUEZVAUBVNVQUBVPVDZAVURVVGVR
          ZUMAUTVSZVUQVDZNVAVVMVBVCZNVSZJVOZVTZUAVEVVMUBVFVCZVGVCZVHVCZHVIVCZVD
          ZQVVRVJZRVVTVKZVLZVMZVRZVRAVAVUQVDZVAJVOZUAVEVAUBVFVCZVGVCZVHVCZHVIVC
          ZVDZQVWJVJZRVWLVKZVLZVMZVRZVRAPVSZVUQVDZNVAVXAVBVCZVVQVTZUAVEVXAUBVFV
          CZVGVCZVHVCZHVIVCZVDZQVXDVJZRVXFVKZVLZVMZVRZVRAVXAVAWAVCZVUQVDZNVAVXO
          VBVCZVVQVTZUAVEVXOUBVFVCZVGVCZVHVCZHVIVCZVDZQVXRVJZRVXTVKZVLZVMZVRZVR
          AVVLVRUTPUBVVMVAVLZVWHVWTAVYIVVNVWIVWGVWSVVMVAVUQWBVYIVWCVWOVWFVWRVYI
          VVRVWJVWBVWNVYIVVRNVAWCZVVQVTVWJVYINVVOVYJVVQVYIVVOVAVAVBVCZVYJVVMVAV
          AVBWDVAUUCVDVYKVYJVLUUDVAUUFUUGWEWINVAVVQVWJUUHVVPVAJWFWGWEZVYIVWAVWM
          HVIVYIVVTVWLUAVHVYIVVSVWKVEVGVVMVAUBVFWHWJZWJWKWLVYIVWDVWPVWEVWQVYIVV
          RVWJQVYLWMVYIVVTVWLRVYMWNWOWSWTWPVVMVXAVLZVWHVXNAVYNVVNVXBVWGVXMVVMVX
          AVUQWBVYNVWCVXIVWFVXLVYNVVRVXDVWBVXHVYNNVVOVXCVVQVVMVXAVAVBWDWIZVYNVW
          AVXGHVIVYNVVTVXFUAVHVYNVVSVXEVEVGVVMVXAUBVFWHWJZWJWKWLVYNVWDVXJVWEVXK
          VYNVVRVXDQVYOWMVYNVVTVXFRVYPWNWOWSWTWPVVMVXOVLZVWHVYHAVYQVVNVXPVWGVYG
          VVMVXOVUQWBVYQVWCVYCVWFVYFVYQVVRVXRVWBVYBVYQNVVOVXQVVQVVMVXOVAVBWDWIZ
          VYQVWAVYAHVIVYQVVTVXTUAVHVYQVVSVXSVEVGVVMVXOUBVFWHWJZWJWKWLVYQVWDVYDV
          WEVYEVYQVVRVXRQVYRWMVYQVVTVXTRVYSWNWOWSWTWPVVMUBVLZVWHVVLAVYTVVNVURVW
          GVVGVVMUBVUQWBVYTVWCVVCVWFVVFVYTVVRTVWBVVBVYTVVRNVUQVVQVTTVYTNVVOVUQV
          VQVVMUBVAVBWDWIURUUIZVYTVWAVVAHVIVYTVVTVUTUAVHVYTVVSVUSVEVGVVMUBUBVFW
          HWJZWJWKWLVYTVWDVVDVWEVVEVYTVVRTQWUAWMVYTVVTVUTRWUBWNWOWSWTWPAVWSVWIA
          VWOVWRAVWJUAVAVAWQVCZUBVFVCZVWKVGVCZVHVCZHVIVCZVWNAVWIVWJWUGVDAVVIVWI
          VVJVAUBUUJVQZACDEFGHIJKLMNOQRSUAVAUBWUEUCUDUEUFUGUHUIUJUKULUMUNUOUPUQ
          WUEWRZXAXBAWUFVWMHVIAWUEVWLUAVHAWUDVEVWKVGAWUDVEUBVFVCVEWUCVEUBVFUUKU
          ULAUBAUBUMXCAUBUMUUMUUNUUPWKZWJWKXGAVWPRWUEVKZVWQAWUEGVWJXHZVWPWUKVLZ
          AVWIWULWUMVMWUHAVWICDEFGHIJKLMNOQRSUAVAUBWUEUCUDUEUFUGUHUIUJUKULUMUNU
          OUPUQWUIAVWIXDACDEFGHIJKLMNOQRSUAVAUBWUEUCUDUEUFUGUHUIUJUKULUMUNUOUPU
          QWUIXEXFXBXIAWUEVWLRWUJWNXJXKUUOVXAVPVDZAVXNVXPVYGVXMAWUNVMZVXPVXBVXM
          WUOVXAVVHVDZVXPVXBVRWUNWUPAWUNWUPVXAUUQUURZXLWUPVXPVXBVXAVAUBUUSZUUTV
          QUVAAWUNVXPVMZVXMVYGWUSVXMVMABVYGUSABVMZVYCVYFWUTVXFVXEVXSVGVCZVXRVYA
          HVYAXMZGWVBWRUGWUTVXTXNXOZVXFUAXPVOZVDVXFVXTXOZVXFVYAXPVOZVDWUTVEXNVD
          ZVXSXNVDZWVCXQWUTVXOUBWUTVXOWUTVXPVXOVPVDWUTWUNVXPBWUSABWUSVXMUSUVBZX
          LXIZVXOUBUVCVQXRZAVVKBUMUVDZXTZVEVXSXSYAZWUTVXFUVFUVGUVHVOZXPVOZWVDWU
          TWVGVXEXNVDZVXFWVPVDXQWUTVXAUBWUTVXABWUNABWUNVXPWVIYBXLZXRZWVLXTZVEVX
          EYCYAUAWVOXPUPUVEZYDWUTVXFWVAYEZVXFVXTVXFWVAUVIWUTWVGWVHVXEVXTVDZVXTW
          WBVLWVGWUTXQYFWVMWUTWWCWVQVEVXEYGYHZVXEVXSYGYHZWVTWUTVXAXNVDZVEVXAYGY
          HUBXNVDZVEUBYIYHZWWDWVSWUTVXAWUTVXAWVRUVJUVKWUTUBWVLXRZWUTUBWVLUVLZVX
          AUBUVMUVNZWUTVXEVXSWVTWVMWUTVXAVXOYIYHZVXEVXSYIYHZWUTVXAWVSUVOWUTWWFV
          XOXNVDWWGWWHWWLWWMYJWVSWVKWWIWWJVXAVXOUBUVPUVQYKUVRZWUTWVGWVHWWCWVQWW
          DWWEUVSYJXQWVMVEVXSVXEUVTYAUWAVEVXSVXEUWBYLZUWCZVXTVXFUAXNXNWVOXMUAXM
          UWFUAWVOUPUWDUWEZUWGYLWUTWVCWVAWVDVDWVAVXTXOZWVAWVFVDWVNWUTWVAWVPWVDW
          UTWVQWVHWVAWVPVDWVTWVMVXEVXSYCYMWWAYDWUTWWBWVAVXTWVAVXFUWHWWOUWCZVXTW
          VAUAXNWWQUWGYLWUTVXTWWBWVBWWOWUTUAYNVDZWVCVXTWVBVLUAWVOYNUPUWPUWIZWVN
          VXTUAXNWWQUWJYAYOZWUTWWBGVXRXHZWVBGVXRXHWUTWWBGVXDVXOJVOZYEZXHZWXCWUT
          VXFGVXDXHZWVAGWXDXHZVXDVXFWVAUWKZVKZWXDWXIVKZVLZWXFWUTWXGVXGXMZGVXDXH
          ZWUTVXIWXNWUTVXIVXLBVXMABWUSVXMUSUWLXLZYBZVXDVXGHWXMGWXMWRUGUWMVQZWUT
          VXFWXMGVXDWUTWWTVXFXNXOZVXFWXMVLWXAWUTWVGWVQWXRXQWVTVEVXEXSYAVXFUAXNW
          WQUWJYAYPUWNZWUTVXOVAWQVCZUBVFVCZVXSVGVCZGWXDXHZWXHWUTWYCQWXDVJZRWYBV
          KZVLZABVXPWYCWYFVMWVJAVXPCDEFGHIJKLMNOQRSUAVXOUBWYBUCUDUEUFUGUHUIUJUK
          ULUMUNUOUPUQWYBWRZAVXPXDACDEFGHIJKLMNOQRSUAVXOUBWYBUCUDUEUFUGUHUIUJUK
          ULUMUNUOUPUQWYGXEXFYQZYBWUTWYBWVAGWXDWUTWYAVXEVXSVGWUTWXTVXAUBVFWUTVX
          AUXPVDVAUXPVDWXTVXAVLWUTVXAWVRXCUWOVXAVAUWQUWRZWKZWKZYPYKZWUTVXDVXEWC
          ZVKZWXDWYMVKZWXJWXKWUTVXEVXEVXDVOZUWSZWCZVXEVXEWXDVOZUWSZWCZWYNWYOWUT
          WYQWYTWUTWYPWYSVXEWUTWYPVXEVXAJVOZVOZWYAWXTJVOZVOZWYSWUTVXDUWTXUBVXDX
          OZVXEXUBUXAZVDWYPXUCVLWUTWXMGVXDWXQUXBWUTVXAVXCVDZXUFWUTWUPXUHWUTWUNW
          UPWVRWUQVQZVAVXAVNVQNVXCVVQVXAXUBVVPVXAJWFUXCVQWUTVXEVXAVAWQVCZUBVFVC
          ZVXEVGVCZXUGWUTXUKYRVDVXEYRVDZXUKVXEYGYHVXEXULVDWUTXUKWUTXUJUBWUTWWFX
          UJXNVDZWVSVXAUXDVQZWVLXTZYSWUTVXEWVTYSZWUTXUKVXEXUPWVTWUTXUJVXAYIYHZX
          UKVXEYIYHZWUTVXAWVSUXEWUTXUNWWFWWGWWHXURXUSYJXUOWVSWWIWWJXUJVXAUBUVPU
          VQYKUVRXUKVXEUXFYLWUTXULGXUBWUTXULGXUBXHZQXUBVJRXULVKVLZABVXBXUTXVAVM
          WUTWUPVXPVXBXUIWVJWURYMAVXBCDEFGHIJKLMNOQRSUAVXAUBXULUCUDUEUFUGUHUIUJ
          UKULUMUNUOUPUQXULWRZAVXBXDACDEFGHIJKLMNOQRSUAVXAUBXULUCUDUEUFUGUHUIUJ
          UKULUMUNUOUPUQXVBXEXFYQYBUXGUXHVXEVXDXUBUXIYLWUTWYAVXEXUDXUBWUTWXTVXA
          JWYIUXJWYJUXKWUTWYAWXDVOZXUEWYSABVXPXVCXUEVLWVJACDEFGHIJKLMNOQRSUAVXO
          UBUCUDUEUFUGUHUIUJUKULUMUNUOUPUQUXLYQWUTWYAVXEWXDWYJUXJYOUXMUXNUXOWUT
          VXDVXFUXQVXEVXFVDZWYNWYRVLWUTVXFGVXDWXSUXRWUTVEYRVDZXUMWWDXVDXVEWUTUX
          SYFZXUQWWKVEVXEUXFYLVXFVXEVXDUXTYMWUTWXDWVAUXQVXEWVAVDZWYOXUAVLWUTWVA
          GWXDWYLUXRWUTXUMVXSYRVDZWWEXVGXUQWUTVXSWVMYSZWWNVXEVXSUYAYLWVAVXEWXDU
          XTYMUYBWUTWXIWYMVXDWUTWXIWWDVXEVEUYGZWWEVXEVXSUYGZVGVCZVXEVXEVGVCZWYM
          WUTXVEXUMXUMXVHWXIXVLVLXVFXUQXUQXVICUTDVEVXEVXEVXSYGYGVGCUTDUYCVEVXED
          VSZUYDXVNVXEVXSUYEUYHUVNWUTXVJVXEXVKVXEVGWUTWWDVXEVEWWKUYFWUTWWEVXEVX
          SWWNUYFUYIWUTXUMXVMWYMVLXUQVXEUYJVQUYKZWNWUTWXIWYMWXDXVOWNUYBZVXFWVAG
          VXDWXDUYLYLWUTWWBGWXEVXRWUTVXRNVXCVXOWCZYEZVVQVTZWXEWUTNVXQXVRVVQWUTW
          UPVXQXVRVLXUIVAVXAUYMVQWIXVSVXDNXVQVVQVTZYEWXENVXCXVQVVQUYNXVTWXDVXDN
          VXOVVQWXDVXAVAWAUYOVVPVXOJWFWGUYPUYQUYRZUYSYKWUTWWBWVBGVXRWXBYPYKWUTV
          XDVXHVXRVXFVKZVYAVXFVHVCZHVIVCWXPWUTWXEVXFVKZXWBVXDWUTWXEVXRVXFXWAUYT
          WUTWXGWXHWXLXWDVXDVLWXSWYLXVPVXFWVAGVXDWXDVUAYLYOWUTXWCVXGHVIWUTWWTWV
          EVXTYTVDZXWCVXGVLWWTWUTWXAYFZWWPXWEWUTVEVXSVGUYOYFZVXFVXTUAYNYTVUBYLW
          KVUCWUTWXDUAWVAVHVCZHVIVCZVXRWVAVKZVYAWVAVHVCZHVIVCWUTWXDUAWYBVHVCZHV
          IVCZXWIABVXPWXDXWMVDWVJACDEFGHIJKLMNOQRSUAVXOUBWYBUCUDUEUFUGUHUIUJUKU
          LUMUNUOUPUQWYGXAYQWUTXWLXWHHVIWUTWYBWVAUAVHWYKWJWKXGWUTWXEWVAVKZXWJWX
          DWUTWXEVXRWVAXWAUYTWUTWXGWXHWXLXWNWXDVLWXSWYLXVPVXFWVAGVXDWXDVUDYLYOW
          UTXWKXWHHVIWUTWWTWWRXWEXWKXWHVLXWFWWSXWGWVAVXTUAYNYTVUBYLWKVUCVUFWUTV
          YERWWBVKZQWXEVJZVYDWUTVXTWWBRWWOWNWUTVXJWYDYEVXKRWVAVKZYEXWPXWOWUTVXJ
          VXKWYDXWQWUTVXIVXLWXOXIWUTWYDWYEXWQWUTWYCWYFWYHXIWUTWYBWVARWYKWNXJVUE
          QVXDWXDVUGRVXFWVAVUHVUOWUTWXEVXRQXWAWMVUIXKVUJVUKVULVUMVUNVUP $.
      $}

      $( Lemma for ~ cvmlift .  (Contributed by Mario Carneiro,
         14-Feb-2015.) $)
      cvmliftlem11 $p |- ( ph -> ( K e. ( II Cn C ) /\ ( F o. K ) = G ) ) $=
        ( vn cii ccn co wcel ccom wceq cc0 cdiv cicc crest cres cv cn caddc cfz
        c1 wa cfv ciun biid cvmliftlem10 simpld crn ctg a1i nncnd nnne0d dividd
        oveq2d oveq12d dfii2 eqtr4di oveq1d eleqtrd simprd reseq2d wf wfn iiuni
        cioo cnf ffn fnresdm 4syl 3eqtrd jca ) ARURGUSUTZVAORVBZPVCARSVDTTVEUTZ
        VFUTZVGUTZGUSUTZXDARXIVAZXEPXGVHZVCZAUQVIZVJVAXMVMVKUTVMTVLUTVAVNMVMXMV
        LUTMVIIVOVPZSVDXMTVEUTVFUTZVGUTGUSUTVAOXNVBPXOVHVCVNVNZBCDEFGHIJKLMNUQO
        PQRSTUAUBUCUDUEUFUGUHUIUJUKULUMUNUOUPXPVQVRZVSAXHURGUSAXHWQVTWAVOZVDVMV
        FUTZVGUTURASXRXGXSVGSXRVCAUNWBAXFVMVDVFATATUKWCATUKWDWEWFZWGWHWIWJWKAXE
        XKPXSVHZPAXJXLXQWLAXGXSPXTWMAPURQUSUTVAXSUAPWNPXSWOYAPVCUHPURQXSUAWPUFW
        RXSUAPWSXSPWTXAXBXC $.

      $( Lemma for ~ cvmlift .  The initial value of ` K ` is ` P ` because
         ` Q ( 1 ) ` is a subset of ` K ` which takes value ` P ` at ` 0 ` .
         (Contributed by Mario Carneiro, 16-Feb-2015.) $)
      cvmliftlem13 $p |- ( ph -> ( K ` 0 ) = P ) $=
        ( cc0 cfv c1 cop csn wfun wss cdm wcel wceq cicc co cii wf cvmliftlem11
        ccn ccom simpld iiuni cnf syl ffund cfz cv ciun cuz cn eleqtrdi eluzfz1
        nnuz fveq2 ssiun2s sseqtrrdi cmin cxr cle wbr 0xr a1i nnrecred rexrd cr
        cdiv 1red 0le1 nnred nngt0d divge0 syl22anc lbicc2 syl3anc 1m1e0 oveq1i
        clt nncnd nnne0d div0d eqtrid oveq1d eleqtrrd cres wa simpr cvmliftlem7
        eqid cvmliftlem6 mpdan fdmd cvmliftlem9 fveq2d fveq2i cvmliftlem4 eqtri
        funssfv fveq12d 3eqtr3d cn0 0nn0 fvsng sylancr 3eqtrd ) AUQRURZUQUSIURZ
        URZUQUQHUTVAZURZHARVBYSRVCUQYSVDZVEYRYTVFAUQUSVGVHZFRARVIGVLVHVEZUUDFRV
        JAUUEORVMPVFABCDEFGHIJKLMNOPQRSTUAUBUCUDUEUFUGUHUIUJUKULUMUNUOUPVKVNRVI
        GUUDFVOUEVPVQVRAYSMUSTVSVHZMVTZIURZWAZRAUSUUFVEZYSUUIVCATUSWBURZVEUUJAT
        WCUUKUKWFWDUSTWEVQZMUUFUUHUSYSUUGUSIWGWHVQUPWIAUQUSUSWJVHZTWSVHZUSTWSVH
        ZVGVHZUUCAUQUQUUOVGVHZUUPAUQWKVEZUUOWKVEUQUUOWLWMZUQUUQVEUURAWNWOAUUOAT
        UKWPWQAUSWRVEUQUSWLWMZTWRVEUQTXJWMUUSAWTUUTAXAWOATUKXBATUKXCUSTXDXEUQUU
        OXFXGAUUNUQUUOVGAUUNUQTWSVHUQUUMUQTWSXHXIATATUKXKATUKXLXMXNZXOXPAUUPFYS
        AUUPFYSVJZOYSVMPUUPXQVFZAUUJUVBUVCXRUULAUUJBCDEFGHIJKLMNOPQSUSTUUPUAUBU
        CUDUEUFUGUHUIUJUKULUMUNUOUUPYAZAUUJXSABCDEFGHIJKLMNOPQSUSTUUPUAUBUCUDUE
        UFUGUHUIUJUKULUMUNUOUVDXTYBYCVNYDXPUQRYSYJXGAUUNYSURZUUNUUMIURZURZYTUUB
        AUUJUVEUVGVFUULABCDEFGHIJKLMNOPQSUSTUAUBUCUDUEUFUGUHUIUJUKULUMUNUOYEYCA
        UUNUQYSUVAYFAUUNUQUVFUUAUVFUUAVFAUVFUQIURUUAUUMUQIXHYGABCDEFGHIJKLMNOPQ
        STUAUBUCUDUEUFUGUHUIUJUKULUMUNUOYHYIWOUVAYKYLAUQYMVEHFVEUUBHVFYNUIUQHYM
        FYOYPYQ $.

      $( Lemma for ~ cvmlift .  Putting the results of ~ cvmliftlem11 ,
         ~ cvmliftlem13 and ~ cvmliftmo together, we have that ` K ` is a
         continuous function, satisfies ` F o. K = G ` and ` K ( 0 ) = P ` ,
         and is equal to any other function which also has these properties, so
         it follows that ` K ` is the unique lift of ` G ` .  (Contributed by
         Mario Carneiro, 16-Feb-2015.) $)
      cvmliftlem14 $p |- ( ph ->
          E! f e. ( II Cn C ) ( ( F o. f ) = G /\ ( f ` 0 ) = P ) ) $=
        ( cv ccom wceq cc0 cfv wa cii ccn co wrex wrmo wreu cvmliftlem11 simpld
        simprd cvmliftlem13 coeq2 eqeq1d fveq1 anbi12d rspcev syl12anc c1 iiuni
        wcel cicc cconn iiconn cnlly iinllyconn 0elunit cvmliftmo reu5 sylanbrc
        a1i ) APLURZUSZQUTZVAWMVBZHUTZVCZLVDGVEVFZVGZWRLWSVHWRLWSVIASWSWBZPSUSZ
        QUTZVASVBZHUTZWTAXAXCABCDEFGHIJKMNOPQRSTUAUBUCUDUEUFUGUHUIUJUKULUMUNUOU
        PUQVJZVKAXAXCXFVLABCDEFGHIJKMNOPQRSTUAUBUCUDUEUFUGUHUIUJUKULUMUNUOUPUQV
        MWRXCXEVCLSWSWMSUTZWOXCWQXEXGWNXBQWMSPVNVOXGWPXDHVAWMSVPVOVQVRVSAFGHLPQ
        RVDVAVAVTWCVFZUFWAUHVDWDWBAWEWLVDWDWFWBAWGWLVAXHWBAWHWLUIUJUKWIWRLWSWJW
        K $.
    $}

    $( Lemma for ~ cvmlift .  Discharge the assumptions of ~ cvmliftlem14 .
       The set of all open subsets ` u ` of the unit interval such that
       ` G " u ` is contained in an even covering of some open set in ` J ` is
       a cover of ` II ` by the definition of a covering map, so by the
       Lebesgue number lemma ~ lebnumii , there is a subdivision of the closed
       unit interval into ` N ` equal parts such that each part is entirely
       contained within one such open set of ` J ` .  Then using finite choice
       ~ ac6sfi to uniformly select one such subset and one even covering of
       each subset, we are ready to finish the proof with ~ cvmliftlem14 .
       (Contributed by Mario Carneiro, 14-Feb-2015.) $)
    cvmliftlem15 $p |- ( ph ->
        E! f e. ( II Cn C ) ( ( F o. f ) = G /\ ( f ` 0 ) = P ) ) $=
      ( vn vj vx vg vz vy vw vt vc va vm vb cv cmin cdiv cicc wss cima cfv wrex
      c1 co cii crab cfz wral cn ccom wceq cc0 wa ccn wreu cuni ssrab2 wcel wne
      c0 ccnv ad2antrr simprl cnima syl2anc simplr simprrl wf wfn iiuni cnf syl
      ffn elpreima 3syl mpbir2and simprrr crn cin wfun funimacnv inss1 eqsstrdi
      wb ffun ralrimivw r19.2z eleq2 imaeq2 sseq1d rexbidv anbi12d rspcev sylib
      ex sylancr csn cxp ciun c1st weq cop vex sseq2d fveq2 c2nd crio cres cmpt
      cvv cmpo cseq ax-mp eqid 2fveq3 eleq1d eqtrid reseq2d cnveqd fveq1d oveq1
      syl12anc adantr ffvelcdmda cvmcov reximddv r19.42v rexbii rexcom elunirab
      ccvm 3bitr4i ssrdv uniss sseqtrrdi eqssd lebnumii wex cfn 2rexbidv rexrab
      mp1i fzfi op1std rexiunxp imass2 sstr2 reximdv biimtrrid impcom rexlimivw
      wi sylbi ralimi ac6sfi cid cun cioo ctg sneq xpeq12d cbviunv feq3 cbvmptv
      simprr cbvriotavw riotabidv mpteq2dv oveq1d oveq12d riotaeqbidv mpteq12dv
      fveq1 fveq2d cbvmpov seqeq2 cvmliftlem14 exlimdv syl5 rexlimdva mpd ) AIU
      NZVBUOVCUBUNZUPVCUXAUXBUPVCUQVCZBUNZURZBKCUNZUSZUCUNZURZNUXHGUTZVAZUCLVAZ
      CVDVEZVAZIVBUXBVFVCZVGZUBVHVAZJHUNZVIKVJVKUXRUTFVJVLHVDEVMVCVNZAUXMVDURZV
      KVBUQVCZUXMVOZVJUXQUXLCVDVPZAUYAUYBAUDUYAUYBAUDUNZUYAVQZUYDUYBVQZAUYEVLZU
      YDUXFVQZUXKVLZCVDVAZUCLVAZUYFUYGUYDKUTZUXHVQZUXJVSVRZVLZUYJUCLUYGUXHLVQZU
      YOVLZVLZKVTUXHUSZVDVQZUYDUYSVQZKUYSUSZUXHURZNUXJVAZUYJUYRKVDLVMVCVQZUYPUY
      TAVUEUYEUYQSWAUYGUYPUYOWBUXHKVDLWCWDUYRVUAUYEUYMAUYEUYQWEUYGUYPUYMUYNWFUY
      RUYAMKWGZKUYAWHVUAUYEUYMVLXCAVUFUYEUYQAVUEVUFSKVDLUYAMWIQWJWKZWAZUYAMKWLU
      YAUYDUXHKWMWNWOUYRUYNVUCNUXJVGVUDUYGUYPUYMUYNWPUYRVUCNUXJUYRVUBUXHKWQZWRZ
      UXHUYRVUFKWSVUBVUJVJVUHUYAMKXDUXHKWTWNUXHVUIXAXBXEVUCNUXJXFWDUYIVUAVUDVLC
      UYSVDUXFUYSVJZUYHVUAUXKVUDUXFUYSUYDXGVUKUXIVUCNUXJVUKUXGVUBUXHUXFUYSKXHXI
      XJXKXLUUAUYGJELUUJVCVQZUYLMVQUYOUCLVAAVULUYERUUBAUYAMUYDKVUGUUCUCBCEUYLGI
      JLMNOQUUDWDUUEUYIUCLVAZCVDVAUYHUXLVLZCVDVAUYKUYFVUMVUNCVDUYHUXKUCLUUFUUGU
      YIUCCLVDUUHUXLCUYDVDUUIUUKXMXNUULAUYBVDVOZUYAUXTUYBVUOURAUYCUXMVDUUMUVAWI
      UUNUUOBUXMIUBUUPXOAUXPUXSUBVHUXPUXOUCLUXHXPZUXJXQZXRZUEUNZWGZKUXCUSZUXAVU
      SUTZXSUTZURZIUXOVGZVLZUEUUQZAUXBVHVQZVLZUXSUXPUXOUURVQVVAUXFXSUTZURZCVURV
      AZIUXOVGVVGVBUXBUVBUXNVVLIUXOUXNKUXDUSZUXHURZNUXJVAUCLVAZUXEVLZBVDVAVVLUX
      LVVOUXEBCVDCBXTZUXIVVNUCNLUXJVVQUXGVVMUXHUXFUXDKXHXIUUSUUTVVPVVLBVDUXEVVO
      VVLVVOVVMVVJURZCVURVAUXEVVLVVRVVNCUCNLUXJUXFUXHNUNZYAVJVVJUXHVVMUXHVVSUXF
      UCYBNYBUVCYCUVDUXEVVRVVKCVURUXEVVAVVMURVVRVVKUVKUXCUXDKUVEVVAVVMVVJUVFWKU
      VGUVHUVIUVJUVLUVMVVKVVDICUXOVURUEUXFVVBVJVVJVVCVVAUXFVVBXSYDYCUVNXOVVIVVF
      UXSUEVVIVVFUXSVVIVVFVLZUDUFBCDEFUGUHYIVHUIUHUNZVBUOVCZUXBUPVCZVWAUXBUPVCZ
      UQVCZUIUNZKUTJVWCUGUNZUTZUJUNZVQZUJVWAVUSUTYEUTZYFZYGZVTZUTZYHZYJZUVOVHYG
      VKVKFYAXPYAXPUVPZVKYKZGVUSHUKIULJKLIUXOUXAVWSUTXRZUVQWQUVRUTZUXBMNUMOPQAV
      ULVVHVVFRWAAVUEVVHVVFSWAAFDVQVVHVVFTWAAFJUTVKKUTVJVVHVVFUAWAAVVHVVFWEVVTV
      UTUXOUKLUKUNZXPZVXBGUTZXQZXRZVUSWGZVVIVUTVVEWBVURVXFVJVUTVXGXCUCUKLVUQVXE
      UCUKXTVUPVXCUXJVXDUXHVXBUVSUXHVXBGYDUVTUWAVURVXFUXOVUSUWBYLXMVVIVUTVVEUWD
      VXAYMVWQUDULYIVHUFULUNZVBUOVCZUXBUPVCZVXHUXBUPVCZUQVCZUFUNZKUTZJVXJUYDUTZ
      UMUNZVQZUMVXHVUSUTYEUTZYFZYGZVTZUTZYHZYJZVJVWSVYDVWRVKYKVJUGUHUDULYIVHVWP
      VYCUFVWEVXNJVWCUYDUTZVXPVQZUMVWKYFZYGZVTZUTZYHZUGUDXTZVWPUFVWEVXNVWNUTZYH
      VYKUIUFVWEVWOVYMVWFVXMVWNKYNUWCVYLUFVWEVYMVYJVYLVXNVWNVYIVYLVWMVYHVYLVWLV
      YGJVYLVWLVWHVXPVQZUMVWKYFVYGVWJVYNUJUMVWKVWIVXPVWHXGUWEVYLVYNVYFUMVWKVYLV
      WHVYEVXPVWCVWGUYDUWLYOUWFYPYQYRYSUWGYPUHULXTZUFVWEVYJVXLVYBVYOVWCVXJVWDVX
      KUQVYOVWBVXIUXBUPVWAVXHVBUOYTUWHZVWAVXHUXBUPYTUWIVYOVXNVYIVYAVYOVYHVXTVYO
      VYGVXSJVYOVYFVXQUMVWKVXRVWAVXHYEVUSYNVYOVYEVXOVXPVYOVWCVXJUYDVYPUWMYOUWJY
      QYRYSUWKUWNVWQVYDVWRVKUWOYLVWTYMUWPXNUWQUWRUWSUWT $.
  $}

  $(
  @{
    iscvm2.1 @e |- X = U. J @.
    iscvm2.2 @e |- A = { j e. Top | E. y
      E. g e. ( ( j tX ~P y ) Homeo ( C |`t ( `' F " U. j ) ) )
       ( g o. ( F |` ( `' F " U. j ) ) ) = ( 1st |` ( U. j X. y ) ) } @.
    @{
      iscvm2.s @e |- S = ( k e. J |->
        { s e. ( ~P C \ { (/) } ) | ( U. s = ( `' F " k ) /\
          A. u e. s ( A. v e. ( s \ { u } ) ( u i^i v ) = (/) /\
             ( F |` u ) e. ( ( C |`t u ) Homeo ( J |`t k ) ) ) ) } ) @.
      @( An alternative characterization of covering maps using the
         ` Locally A `
         predicate. A continuous function ` F ` is a covering map iff ` J ` is
         locally evenly covered, where " ` x ` is evenly covered" means that
         ` ``' F " x ` is homeomorphic to the product of ` x ` with a discrete
         space, and such that ` F ` looks like the first projection function
         under this homeomorphism. @)
      iscvm2lem @p |- ( ( C e. Top /\ J e. Top /\ F e. ( C Cn J ) ) ->
        ( F e. ( C CovMap J ) <-> J e. Locally A ) ) @=
        ? @.
        @( [13-Feb-2015] @)
    @}

    @( An alternative characterization of covering maps using the ` Locally A `
       predicate. A continuous function ` F ` is a covering map iff ` J ` is
       locally evenly covered, where " ` x ` is evenly covered" means that
       ` ``' F " x ` is homeomorphic to the product of ` x ` with a discrete
       space, and such that ` F ` looks like the first projection function
       under this homeomorphism. @)
    iscvm2 @p |- ( ( C e. Top /\ J e. Top /\ F e. ( C Cn J ) ) ->
      ( F e. ( C CovMap J ) <-> J e. Locally A ) ) @=
      ? @.
      @( [13-Feb-2015] @)
  @}
  $)

  ${
    $d a b c d f k s u v C $.  $d a b c d f G $.  $d a b c d f P $.  $d a X $.
    $d a b c d f k s u v F $.  $d a b c d f k s u v J $.  $d b c d f B $.
    cvmlift.1 $e |- B = U. C $.
    $( One of the important properties of covering maps is that any path ` G `
       in the base space "lifts" to a path ` f ` in the covering space such
       that ` F o. f = G ` , and given a starting point ` P ` in the covering
       space this lift is unique.  The proof is contained in ~ cvmliftlem1 thru
       ~ cvmliftlem15 .  (Contributed by Mario Carneiro, 16-Feb-2015.) $)
    cvmlift $p |- ( ( ( F e. ( C CovMap J ) /\ G e. ( II Cn J ) ) /\
      ( P e. B /\ ( F ` P ) = ( G ` 0 ) ) ) ->
        E! f e. ( II Cn C ) ( ( F o. f ) = G /\ ( f ` 0 ) = P ) ) $=
      ( vd vc vk vs vu vv va co wcel wa wceq cv ccvm cii ccn cfv cuni ccnv cima
      vb cc0 cin c0 csn cdif wral cres crest chmeo cpw crab cmpt cvmscbv simpll
      eqid simplr simprl simprr cvmliftlem15 ) EBGUAPQZFUBGUCPQZRZCAQZCEUDUIFUD
      SZRZRIJABCKGLTZUEEUFKTZUGSMTZNTUJUKSNVNVPULUMUNEVPUOBVPUPPGVOUPPUQPQRMVNU
      NRLBURUKULUMUSUTZDOEFGGUEZUHNMBVQKEGLOUHJIVQVCVAHVRVCVHVIVMVBVHVIVMVDVJVK
      VLVEVJVKVLVFVG $.

    cvmfo.2 $e |- X = U. J $.
    $( A covering map is an onto function.  (Contributed by Mario Carneiro,
       13-Feb-2015.) $)
    cvmfo $p |- ( F e. ( C CovMap J ) -> F : B -onto-> X ) $=
      ( vd vc vk vs vu vv va vb cv wceq c0 csn co cuni ccnv cima cdif wral cres
      cin crest chmeo wcel wa cpw crab cmpt eqid cvmscbv cvmfolem ) HIABJDKPZUA
      CUBJPZUCQLPZMPUGRQMURUTSUDUECUTUFBUTUHTDUSUHTUITUJUKLURUEUKKBULRSUDUMUNZN
      CDEOMLBVAJCDKNOIHVAUOUPFGUQ $.
  $}

  ${
    $d g B $.  $d f g C $.  $d f g F $.  $d f g G $.  $d g H $.  $d f g P $.
    $d g J $.
    cvmliftiota.b $e |- B = U. C $.
    cvmliftiota.h $e |- H =
      ( iota_ f e. ( II Cn C ) ( ( F o. f ) = G /\ ( f ` 0 ) = P ) ) $.
    cvmliftiota.f $e |- ( ph -> F e. ( C CovMap J ) ) $.
    cvmliftiota.g $e |- ( ph -> G e. ( II Cn J ) ) $.
    cvmliftiota.p $e |- ( ph -> P e. B ) $.
    cvmliftiota.e $e |- ( ph -> ( F ` P ) = ( G ` 0 ) ) $.
    $( Write out a function ` H ` that is the unique lift of ` F ` .
       (Contributed by Mario Carneiro, 16-Feb-2015.) $)
    cvmliftiota $p |- ( ph ->
        ( H e. ( II Cn C ) /\ ( F o. H ) = G /\ ( H ` 0 ) = P ) ) $=
      ( vg wceq cc0 cfv wcel cv ccom wa cii ccn co crab crio coeq2 eqeq1d fveq1
      w3a anbi12d cbvriotavw eqtri wreu ccvm cvmlift syl22anc riotacl2 eqeltrid
      syl elrab 3anass bitr4i sylib ) AHFPUAZUBZGQZRVGSZDQZUCZPUDCUEUFZUGZTZHVM
      TZFHUBZGQZRHSZDQZULZAHVLPVMUHZVNHFEUAZUBZGQZRWCSZDQZUCZEVMUHWBKWHVLEPVMWC
      VGQZWEVIWGVKWIWDVHGWCVGFUIUJWIWFVJDRWCVGUKUJUMUNUOAVLPVMUPZWBVNTAFCIUQUFT
      GUDIUEUFTDBTDFSRGSQWJLMNOBCDPFGIJURUSVLPVMUTVBVAVOVPVRVTUCZUCWAVLWKPHVMVG
      HQZVIVRVKVTWLVHVQGVGHFUIUJWLVJVSDRVGHUKUJUMVCVPVRVTVDVEVF $.
  $}

  ${
    $d t u x y z $.  $d u y z M $.
    $( Lemma for ~ cvmlift2 .  (Contributed by Mario Carneiro, 1-Jun-2015.) $)
    cvmlift2lem1 $p |- ( A. y e. ( 0 [,] 1 ) E. u e. ( ( nei ` II ) ` { y } )
        ( ( u X. { x } ) C_ M <-> ( u X. { t } ) C_ M ) ->
      ( ( ( 0 [,] 1 ) X. { x } ) C_ M ->
        ( ( 0 [,] 1 ) X. { t } ) C_ M ) ) $=
      ( vz cv csn cxp wss wb cii cfv wral cop wcel iitop mpan adantl vex cc0 c1
      cnei wrex cicc co wi wa biimp ctop iiuni neii1 xpss1 syl simpl sstrd snss
      ssnei sylibr vsnid opelxpi sylancl ssel syl5com embantd rexlimdva ralimdv
      syl5 com12 dfss3 eleq1 ralxp opeq2 eleq1d ralsn ralbii 3bitri imbitrrdi
      weq ) CGZAGHZIZEJZVTDGZHZIZEJZKZCBGZHZLUCMMZUDZBUAUBUEUFZNZWMWAIZEJZWIWDO
      ZEPZBWMNZWMWEIZEJZWPWNWSWPWLWRBWMWPWHWRCWKWHWCWGUGWPVTWKPZUHZWRWCWGUIXCWC
      WGWRXCWBWOEXCVTWMJZWBWOJXBXDWPLUJPZXBXDQWJLVTWMUKULRSVTWMWAUMUNWPXBUOUPXC
      WQWFPZWGWRXCWIVTPZWDWEPXFXCWJVTJZXGXBXHWPXEXBXHQWJLVTURRSWIVTBTUQUSDUTWIW
      DVTWEVAVBWFEWQVCVDVEVHVFVGVIXAFGZEPZFWTNWIVTOZEPZCWENZBWMNWSFWTEVJXJXLFBC
      WMWEXIXKEVKVLXMWRBWMXLWRCWDDTCDVSXKWQEVTWDWIVMVNVOVPVQVR $.
  $}

  ${
    $d c d k s A $.  $d c d k s F $.  $d x H $.  $d c d k s J $.  $d c d s T $.
    $d c d k s x C $.  $d x K $.  $d x M $.  $d x ph $.  $d c d x W $.
    cvmlift2lem9a.b $e |- B = U. C $.
    cvmlift2lem9a.y $e |- Y = U. K $.
    cvmlift2lem9a.s $e |- S = ( k e. J |->
      { s e. ( ~P C \ { (/) } ) | ( U. s = ( `' F " k ) /\
        A. c e. s ( A. d e. ( s \ { c } ) ( c i^i d ) = (/) /\
           ( F |` c ) e. ( ( C |`t c ) Homeo ( J |`t k ) ) ) ) } ) $.
    cvmlift2lem9a.f $e |- ( ph -> F e. ( C CovMap J ) ) $.
    cvmlift2lem9a.h $e |- ( ph -> H : Y --> B ) $.
    cvmlift2lem9a.g $e |- ( ph -> ( F o. H ) e. ( K Cn J ) ) $.
    cvmlift2lem9a.k $e |- ( ph -> K e. Top ) $.
    cvmlift2lem9a.1 $e |- ( ph -> X e. Y ) $.
    cvmlift2lem9a.2 $e |- ( ph -> T e. ( S ` A ) ) $.
    cvmlift2lem9a.3 $e |- ( ph -> ( W e. T /\ ( H ` X ) e. W ) ) $.
    cvmlift2lem9a.4 $e |- ( ph -> M C_ Y ) $.
    cvmlift2lem9a.6 $e |- ( ph -> ( H " M ) C_ W ) $.
    $( Lemma for ~ cvmlift2 and ~ cvmlift3 .  (Contributed by Mario Carneiro,
       9-Jul-2015.) $)
    cvmlift2lem9a $p |- ( ph -> ( H |` M ) e. ( ( K |`t M ) Cn C ) ) $=
      ( vx crest co ccn cres ctop wcel wss ccvm cvmtop1 syl cnrest2r wf ccnv cv
      cima wral wfn ffnd fnssres syl2anc df-ima eqsstrrid df-f sylanbrc wa ccom
      crn wf1 wceq wf1o cfv simpld cvmsf1o syl3anc adantr f1of1 ctopon toptopon
      sylib cvmsss toponss resttopon sylan f1imacnv imaeq2d imaco cnvco eqtr4di
      sseldd cores resco cnveqd eqtr3id imaeq1d eqtr3d cnrest restopn2 simprbda
      resima2 wb cvmopn eqeltrd cnima ralrimiva iscn mpbir2and ) AKLULUMZDMULUM
      ZUNUMZXRDUNUMZILUOZADUPUQZXTYAURAHDJUSUMUQZYCUBDHJUTVAZMXRDVBVAAYBXTUQZLM
      YBVCZYBVDZUKVEZVFZXRUQZUKXSVGZAYBLVHZYBVRZMURZYGAIOVHLOURZYMAOCIUCVIUIOLI
      VJVKAYNILVFMILVLUJVMZLMYBVNVOAYKUKXSAYIXSUQZVPZYJHIVQZLUOZVDZHMUOZYIVFZVF
      ZXRYSYHUUCVDZUUDVFZVFZYJUUEYSUUGYIYHYSMBUUCVSZYIMURZUUGYIVTYSMBUUCWAZUUIA
      UUKYRAYDFBEWBUQZMFUQZUUKUBUGAUUMNIWBMUQUHWCZRQMDEFBGHJPUAWDWEWFMBUUCWGVAA
      XSMWHWBUQZYRUUJADCWHWBUQZMCURZUUOAYCUUPYEDCSWIWJZAUUPMDUQZUUQUURAFDMAUULF
      DURUGRQDEFBGHJPUAWKVAUUNWTZMDCWLVKMDCWMVKZYIXSMWLWNZMBYIUUCWOVKWPYSUUHYHU
      UFVQZUUDVFUUEYHUUFUUDWQYSUVCUUBUUDYSUVCUUCYBVQZVDUUBUUCYBWRYSUVDUUAAUVDUU
      AVTYRAUVDHYBVQZUUAAYOUVDUVEVTYQHYBMXAVAHILXBWSWFXCXDXEXDXFYSUUAXRJUNUMUQZ
      UUDJUQUUEXRUQAUVFYRAYTKJUNUMUQYPUVFUDUILYTKJOTXGVKWFYSUUDHYIVFZJYSUUJUUDU
      VGVTUVBHYIMXJVAYSYDYIDUQZUVGJUQAYDYRUBWFAYRUVHUUJAYCUUSYRUVHUUJVPXKYEUUTM
      YIDXHVKXIYIDHJXLVKXMUUDUUAXRJXNVKXMXOAXRLWHWBUQZUUOYFYGYLVPXKAKOWHWBUQZYP
      UVIAKUPUQUVJUEKOTWIWJUILKOWMVKUVAUKYBXRXSLMXPVKXQWT $.
  $}

  ${
    $d b c d f g h k m s u v w x y z F $.  $d a b f g m n r t u v w x y z ph $.
    $d a t v x A $.  $d a b c d k r s u x y z M $.  $d b f m t u v w x y z S $.
    $d b c d f g k m s u v w x y z J $.  $d b c d s u v T $.  $d m n u w z U $.
    $d a b c f g h k m t u v w x y z G $.  $d m n u w V $.  $d c d m n u v W $.
    $d b c f u v w x y z H $.  $d a b c d f k m t u v w x y z X $.  $d z Z $.
    $d a b c d f g h k m r s t u v w x y z C $.  $d f g h k u v x y z P $.
    $d b c d v w x y z B $.  $d a b c d f k m t u v w x y z Y $.
    cvmlift2.b $e |- B = U. C $.
    cvmlift2.f $e |- ( ph -> F e. ( C CovMap J ) ) $.
    cvmlift2.g $e |- ( ph -> G e. ( ( II tX II ) Cn J ) ) $.
    cvmlift2.p $e |- ( ph -> P e. B ) $.
    cvmlift2.i $e |- ( ph -> ( F ` P ) = ( 0 G 0 ) ) $.
    ${
      cvmlift2.h $e |- H = ( iota_ f e. ( II Cn C )
      ( ( F o. f ) = ( z e. ( 0 [,] 1 ) |-> ( z G 0 ) ) /\ ( f ` 0 ) = P ) ) $.
      $( Lemma for ~ cvmlift2 .  (Contributed by Mario Carneiro,
         7-May-2015.) $)
      cvmlift2lem2 $p |- ( ph -> ( H e. ( II Cn C ) /\
        ( F o. H ) = ( z e. ( 0 [,] 1 ) |-> ( z G 0 ) ) /\ ( H ` 0 ) = P ) ) $=
        ( cc0 co cii cfv c1 cicc cv cmpt ctopon wcel iitopon a1i cnmptid cnmptc
        0elunit cnmpt12f wceq oveq1 eqid ovex fvmpt ax-mp eqtr4di cvmliftiota )
        ACDEFGBQUAUBRZBUCZQHRZUDZIJKPLABVBQHSSSJVASVAUETUFAUGUHZABSVAVEUIABQSSV
        AVAVEVEQVAUFZAUKUHUJMULNAEGTQQHRZQVDTZOVFVHVGUMUKBQVCVGVAVDVBQQHUNVDUOQ
        QHUPUQURUSUT $.

      ${
        cvmlift2lem3.1 $e |- K = ( iota_ f e. ( II Cn C ) ( ( F o. f ) =
     ( z e. ( 0 [,] 1 ) |-> ( X G z ) ) /\ ( f ` 0 ) = ( H ` X ) ) ) $.
        $( Lemma for ~ cvmlift2 .  (Contributed by Mario Carneiro,
           7-May-2015.) $)
        cvmlift2lem3 $p |- ( ( ph /\ X e. ( 0 [,] 1 ) ) ->
      ( K e. ( II Cn C ) /\ ( F o. K ) = ( z e. ( 0 [,] 1 ) |-> ( X G z ) ) /\
        ( K ` 0 ) = ( H ` X ) ) ) $=
          ( cii cc0 c1 cicc co wcel wa cv cmpt ccvm adantr ctopon iitopon simpr
          cfv a1i cnmptc cnmptid ctx ccn cnmpt12f ccom wceq cvmlift2lem2 simp1d
          wf iiuni cnf syl ffvelcdmda 0elunit oveq2 eqid ovex fvmpt mp1i simp2d
          fveq1d oveq1 sylan9eq fvco3 sylan 3eqtr2rd cvmliftiota ) ALUAUBUCUDZU
          EZUFZCDLIUNZFGBWDLBUGZHUDZUHZKJMSAGDJUIUDUEWENUJWFBLWHHTTTJWDTWDUKUNU
          EWFULUOZWFBLTTWDWDWKWKAWEUMUPWFBTWDWKUQAHTTURUDJUSUDUEWEOUJUTAWDCLIAI
          TDUSUDUEZWDCIVEZAWLGIVAZBWDWHUAHUDZUHZVBZUAIUNEVBZABCDEFGHIJMNOPQRVCZ
          VDITDWDCVFMVGVHZVIWFUAWJUNZLUAHUDZLWNUNZWGGUNZUAWDUEXAXBVBWFVJBUAWIXB
          WDWJWHUALHVKWJVLLUAHVMZVNVOAWEXCLWPUNXBALWNWPAWLWQWRWSVPVQBLWOXBWDWPW
          HLUAHVRWPVLXEVNVSAWMWEXCXDVBWTWDCLGIVTWAWBWC $.
      $}

      $d a b c d f g m n r t u v w x y z K $.
      cvmlift2.k $e |- K = ( x e. ( 0 [,] 1 ) , y e. ( 0 [,] 1 ) |->
          ( ( iota_ f e. ( II Cn C ) ( ( F o. f ) =
     ( z e. ( 0 [,] 1 ) |-> ( x G z ) ) /\ ( f ` 0 ) = ( H ` x ) ) ) ` y ) ) $.
      $( Lemma for ~ cvmlift2 .  (Contributed by Mario Carneiro,
         1-Jun-2015.) $)
      cvmlift2lem4 $p |- ( ( X e. ( 0 [,] 1 ) /\ Y e. ( 0 [,] 1 ) ) ->
      ( X K Y ) = ( ( iota_ f e. ( II Cn C ) ( ( F o. f ) =
     ( z e. ( 0 [,] 1 ) |-> ( X G z ) ) /\ ( f ` 0 ) = ( H ` X ) ) ) ` Y ) ) $=
        ( cc0 c1 cicc co cv ccom cmpt wceq cfv wa cii ccn oveq1 mpteq2dv eqeq2d
        crio fveq2 anbi12d riotabidv fveq1d fvex ovmpo ) BCNOUCUDUEUFZVECUGZIHU
        GZUHZDVEBUGZDUGZJUFZUIZUJZUCVGUKZVIKUKZUJZULZHUMFUNUFZURZUKOVHDVENVJJUF
        ZUIZUJZVNNKUKZUJZULZHVRURZUKMVFWFUKVINUJZVFVSWFWGVQWEHVRWGVMWBVPWDWGVLW
        AVHWGDVEVKVTVINVJJUOUPUQWGVOWCVNVINKUSUQUTVAVBVFOWFUSUBOWFVCVD $.

      $( Lemma for ~ cvmlift2 .  (Contributed by Mario Carneiro,
         7-May-2015.) $)
      cvmlift2lem5 $p |- ( ph -> K : ( ( 0 [,] 1 ) X. ( 0 [,] 1 ) ) --> B ) $=
        ( cv ccom cc0 c1 cicc co cmpt wceq cfv wa cii ccn crio wcel wral cxp wf
        w3a eqid cvmlift2lem3 adantrr simp1d iiuni cnf syl ffvelcdmd ralrimivva
        simprr fmpo sylib ) ACUAZIHUAZUBDUCUDUEUFZBUAZDUAJUFUGZUHUCVLUIVNKUIZUH
        UJHUKFULUFZUMZUIZEUNZCVMUOBVMUOVMVMUPEMUQAVTBCVMVMAVNVMUNZVKVMUNZUJUJZV
        MEVKVRWCVRVQUNZVMEVRUQWCWDIVRUBVOUHZUCVRUIVPUHZAWAWDWEWFURWBADEFGHIJKLV
        RVNNOPQRSVRUSUTVAVBVRUKFVMEVCNVDVEAWAWBVHVFVGBCVMVMVSEMTVIVJ $.

      $( Lemma for ~ cvmlift2 .  (Contributed by Mario Carneiro,
         7-May-2015.) $)
      cvmlift2lem6 $p |- ( ( ph /\ X e. ( 0 [,] 1 ) ) ->
        ( K |` ( { X } X. ( 0 [,] 1 ) ) ) e.
          ( ( ( II tX II ) |`t ( { X } X. ( 0 [,] 1 ) ) ) Cn C ) ) $=
        ( vu vv cc0 c1 cicc co wcel wa csn cxp cres ccom cmpt wceq cfv cii crio
        cv ccn cmpo ctx crest wfn wf cvmlift2lem5 adantr ffnd sylib reseq1d wss
        fnov simpr snssd ssid resmpo sylancl elsni 3ad2ant2 oveq1d simp1r simp3
        w3a cvmlift2lem4 syl2anc mpoeq3dva eqid ctopon iitopon a1i cvmlift2lem3
        eqtrd cnmpt2nd simp1d cnmpt21f cnmpt2res ctop cvv iitop snex ovex mp4an
        txrest oveq1i eleqtrrdi eqeltrd ) ANUDUEUFUGZUHZUIZMNUJZXGUKZULZUBUCXJX
        GUCUSZIHUSZUMDXGNDUSJUGUNZUOUDXNUPNKUPZUOUIHUQFUTUGZURZUPZVAZUQUQVBUGXK
        VCUGZFUTUGZXIXLUBUCXGXGUBUSZXMMUGZVAZXKULZXTXIMYEXKXIMXGXGUKZVDMYEUOXIY
        GEMAYGEMVEXHABCDEFGHIJKLMOPQRSTUAVFVGVHUBUCXGXGMVLVIVJXIYFUBUCXJXGYDVAZ
        XTXIXJXGVKXGXGVKZYFYHUOXINXGAXHVMVNZXGVOZUBUCXGXGXJXGYDVPVQXIUBUCXJXGYD
        XSXIYCXJUHZXMXGUHZWCZYDNXMMUGZXSYNYCNXMMYLXIYCNUOYMYCNVRVSVTYNXHYMYOXSU
        OAXHYLYMWAXIYLYMWBABCDEFGHIJKLMNXMOPQRSTUAWDWEWLWFWLWLXIXTUQXJVCUGZUQXG
        VCUGZVBUGZFUTUGYBXIUBUCXSUQYPFUQYQXGXGXJXGYPWGUQXGWHUPUHXIWIWJZYJYQWGYS
        YIXIYKWJXIUBUCXMXRUQUQUQFXGXGYSYSXIUBUCUQUQXGXGYSYSWMXIXRXQUHIXRUMXOUOU
        DXRUPXPUOADEFGHIJKLXRNOPQRSTXRWGWKWNWOWPYAYRFUTUQWQUHZYTXJWRUHXGWRUHYAY
        RUOWSWSNWTUDUEUFXAXJXGUQUQWQWQWRWRXCXBXDXEXF $.

      $( Lemma for ~ cvmlift2 .  (Contributed by Mario Carneiro,
         7-May-2015.) $)
      cvmlift2lem7 $p |- ( ph -> ( F o. K ) = G ) $=
        ( vw cc0 c1 cicc co cv ccom cmpt wceq cfv wa cii ccn crio cmpo wcel w3a
        cvmlift2lem3 adantrr simp2d fveq1d wf simp1d iiuni cnf syl simprr fvco3
        eqid syl2anc oveq2 ovex fvmpt 3eqtr3d mpoeq3dva ffvelcdmd a1i cuni ccvm
        3impb cvmcn 3syl feqmptd fveq2 fmpoco cxp wfn ctx iitop txunii ffn fnov
        sylib 3eqtr4d ) ABCUBUCUDUEZWOCUFZIHUFZUGDWOBUFZDUFZJUEZUHZUIUBWQUJWRKU
        JZUIUKHULFUMUEZUNZUJZIUJZUOBCWOWOWRWPJUEZUOZIMUGJABCWOWOXFXGAWRWOUPZWPW
        OUPZXFXGUIAXIXJUKUKZWPIXDUGZUJZWPXAUJZXFXGXKWPXLXAXKXDXCUPZXLXAUIZUBXDU
        JXBUIZAXIXOXPXQUQXJADEFGHIJKLXDWRNOPQRSXDVIURUSZUTVAXKWOEXDVBZXJXMXFUIX
        KXOXSXKXOXPXQXRVCXDULFWOEVDNVEVFZAXIXJVGZWOEWPIXDVHVJXKXJXNXGUIYADWPWTX
        GWOXAWSWPWRJVKXAVIWRWPJVLVMVFVNVTVOABCUAWOWOEXEUAUFZIUJXFMIXKWOEWPXDXTY
        AVPMBCWOWOXEUOUIATVQAUAELVRZIAIFLVSUEUPIFLUMUEUPEYCIVBOFILWAIFLEYCNYCVI
        ZVEWBWCYBXEIWDWEAJWOWOWFZWGZJXHUIAJULULWHUEZLUMUEUPYEYCJVBYFPJYGLYEYCUL
        ULWOWOWIWIVDVDWJYDVEYEYCJWKWBBCWOWOJWLWMWN $.

      $( Lemma for ~ cvmlift2 .  (Contributed by Mario Carneiro,
         9-Mar-2015.) $)
      cvmlift2lem8 $p |- ( ( ph /\ X e. ( 0 [,] 1 ) ) ->
          ( X K 0 ) = ( H ` X ) ) $=
        ( cc0 c1 cicc co wcel wa ccom cmpt wceq cfv cii crio simpr cvmlift2lem4
        cv ccn 0elunit sylancl eqid cvmlift2lem3 simp3d eqtrd ) ANUBUCUDUEZUFZU
        GZNUBMUEZUBIHUPZUHDVDNDUPJUEUIZUJUBVHUKNKUKZUJUGHULFUQUEZUMZUKZVJVFVEUB
        VDUFVGVMUJAVEUNURABCDEFGHIJKLMNUBOPQRSTUAUOUSVFVLVKUFIVLUHVIUJVMVJUJADE
        FGHIJKLVLNOPQRSTVLUTVAVBVC $.

      ${
        $d a S $.
        cvmlift2lem10.s $e |- S = ( k e. J |->
          { s e. ( ~P C \ { (/) } ) | ( U. s = ( `' F " k ) /\
            A. c e. s ( A. d e. ( s \ { c } ) ( c i^i d ) = (/) /\
               ( F |` c ) e. ( ( C |`t c ) Homeo ( J |`t k ) ) ) ) } ) $.
        ${
          cvmlift2lem9.1 $e |- ( ph -> ( X G Y ) e. M ) $.
          cvmlift2lem9.2 $e |- ( ph -> T e. ( S ` M ) ) $.
          cvmlift2lem9.3 $e |- ( ph -> U e. II ) $.
          cvmlift2lem9.4 $e |- ( ph -> V e. II ) $.
          cvmlift2lem9.5 $e |- ( ph -> ( II |`t U ) e. Conn ) $.
          cvmlift2lem9.6 $e |- ( ph -> ( II |`t V ) e. Conn ) $.
          cvmlift2lem9.7 $e |- ( ph -> X e. U ) $.
          cvmlift2lem9.8 $e |- ( ph -> Y e. V ) $.
          cvmlift2lem9.9 $e |- ( ph -> ( U X. V ) C_ ( `' G " M ) ) $.
          cvmlift2lem9.10 $e |- ( ph -> Z e. V ) $.
          cvmlift2lem9.11 $e |- ( ph -> ( K |` ( U X. { Z } ) ) e.
            ( ( ( II tX II ) |`t ( U X. { Z } ) ) Cn C ) ) $.
          cvmlift2lem9.w $e |- W = ( iota_ b e. T ( X K Y ) e. b ) $.
          $( Lemma for ~ cvmlift2 .  (Contributed by Mario Carneiro,
             1-Jun-2015.) $)
          cvmlift2lem9 $p |- ( ph ->
           ( K |` ( U X. V ) ) e. ( ( ( II tX II ) |`t ( U X. V ) ) Cn C ) ) $=
            ( vm vn cii ctx co cxp cop iitop ccn eqeltrd ctop wcel a1i wss cuni
            iiuni elssuni syl sseldd opelxpi syl2anc wa cfv fovcdmd df-ov sylib
            wf wceq cima csn cres snidg ovres crest ccnv eqid cconn snex adantr
            cvv txrest syl22anc cpw iitopon restsn2 sylancr c0 cpr pwsn eqeltri
            indisconn eqeltrdi txconn xpss2 snssd xpss1 restuni sseqtrd syl3anc
            crn df-ima imass2 3syl eqtr3id mpbird sstrd eqsstrrid cnrest2 mpbid
            wb eleqtrd conncn feq2d cc0 c1 cicc txunii cvmlift2lem5 ccom txtopi
            cvmlift2lem7 sseqtrrdi fvco3 fveq1d eqtr3d fveq2i cvmsiota syl13anc
            ccvm 3eqtr4g eleq1i anbi2i xpss12 cv ad2antrl simprr ctopon adantrr
            wral sselda cvmlift2lem6 syldan cnrest resabs1d ovex restabs oveq1d
            3eltr3d cvmtop1 toptopon simprl imaco cnvco cnveqd imaeq1d sseqtrrd
            xpex wfun cdm ffund fdmd funimass3 cnvimass cnf fdm sseqtrid cvmsss
            cvmcn simpld cvmsuni cvmsrcl restopn2 mpbir2and ccld cvmscld eqtr4d
            cnima mpdan simprd eqeltrrd ralrimivva funimassov cvmlift2lem9a ) A
            REFHILMQPVJVJVKVLZJSVMZTUAUBVNZUUAUUBUUCVLZUXNVMZUDUFUGUHVJVJUXNUXN
            VOVOWCWCUUDZUOUIABCDEFGKMNOPQUHUIUJUKULUMUNUUEZAMQUUFZNUXKPVPVLABCD
            EFGKMNOPQUHUIUJUKULUMUNUUHZUJVQUXKVRVSZAVJVJVOVOUUGZVTZAUAUXNVSZUBU
            XNVSUXMUXOVSZAJUXNUAAJVJVSZJUXNWAZURUYEJVJWBZUXNJVJWDWCUUIWEZVBWFZA
            SUXNUBASVJVSZSUXNWAZUSUYJSUYGUXNSVJWDWCUUIZWEZVCWFZUAUBUXNUXNWGWHZU
            QATIVSZUAUBQVLZTVSZWIZUYPUXMQWJZTVSZWIAMFPUUPVLVSZIRHWJVSZUYQEVSUYQ
            MWJZRVSUYSUIUQAUAUBEUXNUXNQUXQUYIUYNWKAVUDUAUBNVLZRAUYTMWJZUXMNWJZV
            UDVUEAUXMUXRWJZVUFVUGAUXOEQWNUYDVUHVUFWOUXQUYOUXOEUXMMQUUJWHAUXMUXR
            NUXSUUKUULUYQUYTMUAUBQWLZUUMUAUBNWLUUQUPVQUEUGUFUYQEFHIRLMPTUDUOUHV
            GUUNUUOZUYRVUAUYPUYQUYTTVUIUURUUSWMAUYFUYKUXLUXOWAUYHUYMJUXNSUXNUUT
            WHZAQUXLWPZTWAZVHUVAZVIUVAZQVLZTVSZVISUVFVHJUVFZAVUQVHVIJSAVUNJVSZV
            UOSVSZWIZWIZVUNVUOQVUNWQZSVMZWRZVLZVUPTVVBVUNVVCVSZVUTVVFVUPWOVUSVV
            GAVUTVUNJWSUVBZAVUSVUTUVCZVUNVUOVVCSQWTWHVVBVUNVUOTVVCSVVEVVBVVDTVV
            EWNUXKVVDXAVLZWBZTVVEWNVVBVUNUCVNZTVVEVVJFMXBZRWPZXAVLZVVKVVKXCVVBV
            VJVJVVCXAVLZVJSXAVLZVKVLZXDVVBVJVRVSZVVSVVCXGVSZUYJVVJVVRWOVVSVVBVO
            VTZVWAVVTVVBVUNXEZVTAUYJVVAUSXFVVCSVJVJVRVRXGVJXHXIVVBVVPXDVSVVQXDV
            SZVVRXDVSVVBVVPVVCXJZXDVVBVJUXNUVDWJVSZVUNUXNVSZVVPVWDWOXKAVUSVWFVU
            TAJUXNVUNUYHUVGUVEZVUNVJUXNXLXMVWDXNVVCXOXDVUNXPVVCXRXQXSAVWCVVAVAX
            FVVPVVQXTWHVQVVBVVEVVJFVPVLZVSZVVEVVJVVOVPVLVSZVVBQVVCUXNVMZWRZVVDW
            RZUXKVWKXAVLZVVDXAVLZFVPVLZVVEVWHVVBVWLVWNFVPVLVSZVVDVWNWBZWAVWMVWP
            VSAVVAVWFVWQVWGABCDEFGKMNOPQVUNUHUIUJUKULUMUNUVHUVIVVBVVDVWKVWRVVBU
            YKVVDVWKWAZAUYKVVAUYMXFSUXNVVCYAWEZVVBUXTVWKUXOWAZVWKVWRWOUYAVVBVVC
            UXNWAVXAVVBVUNUXNVWGYBVVCUXNUXNYCWEZVWKUXKUXOUXPYDXMYEVVDVWLVWNFVWR
            VWRXCUVJWHVVBQVVDVWKVWTUVKVVBVWOVVJFVPVVBUXTVWSVWKXGVSZVWOVVJWOUXTV
            VBUYAVTVWTVXCVVBVVCUXNVWBUUAUUBUUCUVLZUWDVTVVDVWKUXKVRXGUVMYFUVNUVO
            VVBFEUVDWJVSZVVEYGZVVNWAVVNEWAZVWIVWJYQVVBFVRVSZVXEAVXHVVAAVUBVXHUI
            FMPUVPWEZXFFEUHUVQZWMVVBVXFQVVDWPZVVNQVVDYHVVBVXKVULVVNVVBVVCJWAVVD
            UXLWAVXKVULWAVVBVUNJAVUSVUTUVRZYBVVCJSYCVVDUXLQYIYJAVULVVNWAZVVAAVX
            MUXLQXBZVVNWPZWAZAUXLNXBZRWPZVXOVDAVXOVXNVVMUUFZRWPVXRVXNVVMRUVSAVX
            SVXQRAVXSUXRXBVXQMQUVTAUXRNUXSUWAYKUWBYKUWCAQUWEZUXLQUWFZWAZVXMVXPY
            QAUXOEQUXQUWGZAUXLUXOVYAVUKAUXOEQUXQUWHUWCZUXLVVNQUWIWHYLZXFYMYNAVX
            GVVAAMUWFZVVNEMRUWJAMFPVPVLVSZEPWBZMWNVYFEWOAVUBVYGUIFMPUWOWEZMFPEV
            YHUHVYHXCUWKEVYHMUWLYJUWMZXFVVNVVEVVJFEYOYFYPATVVOVSZVVAAVYKTFVSZTV
            VNWAZAIFTAVUCIFWAUQUGUFFHIRLMPUDUOUWNWEAUYPUYRVUJUWPZWFATIWBZVVNAUY
            PTVYOWAVYNTIWDWEAVUCVYOVVNWOUQUGUFFHIRLMPUDUOUWQWEYEAVXHVVNFVSZVYKV
            YLVYMWIYQVXIAVYGRPVSZVYPVYIAVUCVYQUQUGUFFHIRLMPUDUOUWRWERMFPUXDWHVV
            NTFUWSWHUWTZXFATVVOUXAWJVSZVVAAVUBVUCUYPVYSUIUQVYNUGUFTFHIRLMPUDUOU
            XBYFZXFVVBVVLVVDVVKVVBVVGUCSVSZVVLVVDVSVVHAWUAVVAVEXFZVUNUCVVCSWGWH
            VVBUXTVVDUXOWAVVDVVKWOUYAVVBVVDVWKUXOVWTVXBYMVVDUXKUXOUXPYDXMZYRVVB
            VVLVVEWJZVUNUCQJUCWQZVMZWRZVLZTVVBWUDVUNUCVVEVLZWUHVUNUCVVEWLVVBWUI
            VUNUCQVLZWUHVVBVVGWUAWUIWUJWOVVHWUBVUNUCVVCSQWTWHVVBVUSUCWUEVSZWUHW
            UJWOVXLAWUKVVAAWUAWUKVEUCSWSWEZXFZVUNUCJWUEQWTWHUXCYKVVBVUNUCTJWUEW
            UGAWUFTWUGWNZVVAAWUNUXKWUFXAVLZWBZTWUGWNAUAUCVNZTWUGWUOVVOWUPWUPXCA
            WUOVJJXAVLZVJWUEXAVLZVKVLZXDAVVSVVSUYEWUEXGVSZWUOWUTWOVVSAVOVTZWVBU
            RWVAAUCXEVTJWUEVJVJVRVRVJXGXHXIAWURXDVSWUSXDVSWUTXDVSUTAWUSWUEXJZXD
            AVWEUCUXNVSWUSWVCWOXKASUXNUCUYMVEWFZUCVJUXNXLXMWVCXNWUEXOXDUCXPWUEX
            RXQXSWURWUSXTWHVQAWUGWUOFVPVLVSZWUGWUOVVOVPVLVSZVFAVXEWUGYGZVVNWAVX
            GWVEWVFYQAVXHVXEVXIVXJWMZAWVGQWUFWPZVVNQWUFYHAWVIVULVVNAWUESWAWUFUX
            LWAWVIVULWAAUCSVEYBWUESJYAWUFUXLQYIYJVYEYMYNVYJVVNWUGWUOFEYOYFYPVYR
            VYTAWUQWUFWUPAUAJVSZWUKWUQWUFVSVBWULUAUCJWUEWGWHAUXTWUFUXOWAZWUFWUP
            WOUYAAUYFWUEUXNWAWVKUYHAUCUXNWVDYBJUXNWUEUXNUUTWHWUFUXKUXOUXPYDXMZY
            RAWUQWUGWJZUAUCQUAWQZSVMZWRZVLZTAWVMUAUCWUGVLZWVQUAUCWUGWLAWVRUAUCQ
            VLZWVQAWVJWUKWVRWVSWOVBWULUAUCJWUEQWTWHAUAWVNVSZWUAWVQWVSWOAWVJWVTV
            BUAJWSWEZVEUAUCWVNSQWTWHUXCYKAUAUCTWVNSWVPAWVOTWVPWNUXKWVOXAVLZWBZT
            WVPWNAUXMTWVPWWBVVOWWCWWCXCAWWBVJWVNXAVLZVVQVKVLZXDAVVSVVSWVNXGVSZU
            YJWWBWWEWOWVBWVBWWFAUAXEZVTUSWVNSVJVJVRVRXGVJXHXIAWWDXDVSVWCWWEXDVS
            AWWDWVNXJZXDAVWEUYCWWDWWHWOXKUYIUAVJUXNXLXMWWHXNWVNXOXDUAXPWVNXRXQX
            SVAWWDVVQXTWHVQAWVPWWBFVPVLZVSZWVPWWBVVOVPVLVSZAQWVNUXNVMZWRZWVOWRZ
            UXKWWLXAVLZWVOXAVLZFVPVLZWVPWWIAWWMWWOFVPVLVSZWVOWWOWBZWAWWNWWQVSAU
            YCWWRUYIABCDEFGKMNOPQUAUHUIUJUKULUMUNUVHUXEAWVOWWLWWSAUYJUYKWVOWWLW
            AZUSUYLSUXNWVNYAYJZAUXTWWLUXOWAZWWLWWSWOUYAAWVNUXNWAWXBAUAUXNUYIYBW
            VNUXNUXNYCWEWWLUXKUXOUXPYDXMYEWVOWWMWWOFWWSWWSXCUVJWHAQWVOWWLWXAUVK
            AWWPWWBFVPAUXTWWTWWLXGVSZWWPWWBWOUYBWXAWXCAWVNUXNWWGVXDUWDVTWVOWWLU
            XKVRXGUVMYFUVNUVOAVXEWVPYGZVVNWAVXGWWJWWKYQWVHAWXDQWVOWPZVVNQWVOYHA
            WXEVULVVNAWVNJWAZWVOUXLWAZWXEVULWAAUAJVBYBZWVNJSYCZWVOUXLQYIYJVYEYM
            YNVYJVVNWVPWWBFEYOYFYPVYRVYTAUXMWVOWWCAWVTUBSVSZUXMWVOVSWWAVCUAUBWV
            NSWGWHAUXTWVOUXOWAWVOWWCWOUYAAWVOUXLUXOAWXFWXGWXHWXIWEVUKYMWVOUXKUX
            OUXPYDXMZYRAUXMWVPWJZUYQTAWXLUAUBWVPVLZUYQUAUBWVPWLAWVTWXJWXMUYQWOW
            WAVCUAUBWVNSQWTWHYKAUYPUYRVUJUXFVQYSAWVOWWCTWVPWXKYTYLWWAVEWKVQYSAW
            UFWUPTWUGWVLYTYLXFVXLWUMWKVQYSVVBVVDVVKTVVEWUCYTYLVVHVVIWKUXGUXHAVX
            TVYBVUMVURYQVYCVYDVHVIJSTQUXIWHYLUXJ $.
        $}

        cvmlift2lem10.1 $e |- ( ph -> X e. ( 0 [,] 1 ) ) $.
        cvmlift2lem10.2 $e |- ( ph -> Y e. ( 0 [,] 1 ) ) $.
        $( Lemma for ~ cvmlift2 .  (Contributed by Mario Carneiro,
           1-Jun-2015.) $)
        cvmlift2lem10 $p |- ( ph -> E. u e. II E. v e. II ( X e. u /\ Y e. v /\
            ( E. w e. v ( K |` ( u X. { w } ) ) e.
              ( ( ( II tX II ) |`t ( u X. { w } ) ) Cn C ) ->
       ( K |` ( u X. v ) ) e. ( ( ( II tX II ) |`t ( u X. v ) ) Cn C ) ) ) ) $=
          ( vm vt va vb cop cfv cv wcel c0 wne wa wrex csn cxp cii ctx co crest
          cres ccn wi w3a ccvm cuni cc0 c1 cicc iitop iiuni txunii eqid cnf syl
          wf opelxpd ffvelcdmd cvmcov syl2anc wex n0 ccnv cima wss csconn eleq1
          wceq opelxp bitrdi anbi1d 2rexbidv wral adantr cvmsrcl ad2antll cnima
          ctop eltx mp2an sylib simprl wfn elpreima 3syl mpbir2and rspcdva clly
          wb ffn iillysconn simplrl simprll llyi mp3an2i simplrr simprlr reeanv
          simpl2 a1i simpr2 simp3 reximdv mpd cpconn cconn sconnpconn pconnconn
          ex simprl1 simprr1 xpss12 sstrd anim12i jca2 biimtrrid mp2and simp3l1
          3jcad rexlimdvva simp3l2 simpl1l df-ov simpl1r simpld eqeltrid simprd
          crio simpl2l simpl2r simp3rl simp3rr simp3l3 simprr cvmlift2lem9 3jca
          rexlimdvaa 3expia reximdvva expr exlimdv biimtrid expimpd rexlimdvw )
          ASTURZOUSZUNUTZVAZUVRKUSZVBVCZVDZUNQVEZSGUTZVAZTFUTZVAZRUWDEUTZVFVGZV
          LVHVHVIVJZUWIVKVJIVMVJVAZEUWFVERUWDUWFVGZVLUWJUWLVKVJIVMVJVAZVNZVOZFV
          HVEGVHVEZANIQVPVJVAZUVQQVQZVAUWCUEAVRVSVTVJZUWSVGZUWRUVPOAOUWJQVMVJVA
          ZUWTUWROWGZUFOUWJQUWTUWRVHVHUWSUWSWAWAWBWBWCUWRWDZWEWFZASTUWSUWSULUMW
          HZWIUNUCUBIUVQKMNQUWRUAUKUXCWJWKAUWBUWPUNQAUVSUWAUWPUWAUOUTZUVTVAZUOW
          LAUVSVDZUWPUOUVTWMUXHUXGUWPUOAUVSUXGUWPAUVSUXGVDZVDZUWEUWGUWLOWNUVRWO
          ZWPZVOZVHUWDVKVJZWQVAZVHUWFVKVJZWQVAZVDZVDZFVHVEZGVHVEZUWPUXJSUPUTZVA
          ZTUQUTZVAZVDZUYBUYDVGZUXKWPZVDZUQVHVEUPVHVEZUYAUXJDUTZUYGVAZUYHVDZUQV
          HVEUPVHVEZUYJDUXKUVPUYKUVPWSZUYMUYIUPUQVHVHUYOUYLUYFUYHUYOUYLUVPUYGVA
          UYFUYKUVPUYGWRSTUYBUYDWTXAXBXCUXJUXKUWJVAZUYNDUXKXDZUXJUXAUVRQVAZUYPA
          UXAUXIUFXEUXGUYRAUVSUCUBIKUXFUVRMNQUAUKXFXGUVROUWJQXHWKVHXIVAZUYSUYPU
          YQXTWAWAUPUQUXKVHVHXIXIDXJXKXLUXJUVPUXKVAZUVPUWTVAZUVSAVUAUXIUXEXEAUV
          SUXGXMUXJUXBOUWTXNUYTVUAUVSVDXTAUXBUXIUXDXEUWTUWROYAUWTUVPUVROXOXPXQX
          RUXJUYIUYAUPUQVHVHUXJUYBVHVAZUYDVHVAZVDVDZUYIUYAVUDUYIVDZUWDUYBWPZUWE
          UXOVOZGVHVEZUWFUYDWPZUWGUXQVOZFVHVEZUYAVHWQXSVAZVUEVUBUYCVUHYBUXJVUBV
          UCUYIYCVUDUYCUYEUYHYDGWQSUYBVHYEYFVULVUEVUCUYEVUKYBUXJVUBVUCUYIYGVUDU
          YCUYEUYHYHFWQTUYDVHYEYFVUHVUKVDVUGVUJVDZFVHVEZGVHVEVUEUYAVUGVUJGFVHVH
          YIVUEVUNUXTGVHVUEVUMUXSFVHVUEVUMUXMUXRVUEVUMUWEUWGUXLVUMUWEVNVUEVUFUW
          EUXOVUJYJYKVUMUWGVNVUEVUGVUIUWGUXQYLYKVUEVUMUXLVUEVUMVDZUWLUYGUXKVUOV
          UFVUIUWLUYGWPVUFUWEUXOVUJVUEUUAVUIUWGUXQVUGVUEUUBUWDUYBUWFUYDUUCWKVUD
          UYFUYHVUMYGUUDYTUUJVUGUXOVUJUXQVUFUWEUXOYMVUIUWGUXQYMUUEUUFYNYNUUGUUH
          YTUUKYOUXJUXSUWOGFVHVHUXJUWDVHVAZUWFVHVAZVDZUXSUWOUXJVURUXSVOZUWEUWGU
          WNUWEUWGUXLUXRUXJVURUUIZUWEUWGUXLUXRUXJVURUULZVUSUWKUWMEUWFVUSUWHUWFV
          AZUWKVDZVDZBCDHIJKUXFUWDLMNOPQRUVRUWFSTRVJUYDVAUQUXFUUSZSTUWHUAUQUBUC
          UDVVDAUWQAUXIVURUXSVVCUUMZUEWFVVDAUXAVVFUFWFVVDAJHVAVVFUGWFVVDAJNUSVR
          VROVJWSVVFUHWFUIUJUKVVDSTOVJUVQUVRSTOUUNVVDUVSUXGAUXIVURUXSVVCUUOZUUP
          UUQVVDUVSUXGVVGUURVUPVUQUXJUXSVVCUUTVUPVUQUXJUXSVVCUVAVVDUXOUXNYPVAUX
          NYQVAVUSUXOVVCUXOUXQUXMUXJVURUVBXEUXNYRUXNYSXPVVDUXQUXPYPVAUXPYQVAVUS
          UXQVVCUXOUXQUXMUXJVURUVCXEUXPYRUXPYSXPVUSUWEVVCVUTXEVUSUWGVVCVVAXEVUS
          UXLVVCUWEUWGUXLUXRUXJVURUVDXEVUSVVBUWKXMVUSVVBUWKUVEVVEWDUVFUVHUVGUVI
          UVJYOUVKUVLUVMUVNUVOYO $.
      $}

      ${
        cvmlift2.m $e |- M = { z e. ( ( 0 [,] 1 ) X. ( 0 [,] 1 ) ) |
          K e. ( ( ( II tX II ) CnP C ) ` z ) } $.
        ${
          cvmlift2lem11.1 $e |- ( ph -> U e. II ) $.
          cvmlift2lem11.2 $e |- ( ph -> V e. II ) $.
          cvmlift2lem11.3 $e |- ( ph -> Y e. V ) $.
          cvmlift2lem11.4 $e |- ( ph -> Z e. V ) $.
          cvmlift2lem11.5 $e |- ( ph -> ( E. w e. V
     ( K |` ( U X. { w } ) ) e. ( ( ( II tX II ) |`t ( U X. { w } ) ) Cn C ) ->
       ( K |` ( U X. V ) ) e. ( ( ( II tX II ) |`t ( U X. V ) ) Cn C ) ) ) $.
          $( Lemma for ~ cvmlift2 .  (Contributed by Mario Carneiro,
             1-Jun-2015.) $)
          cvmlift2lem11 $p |- ( ph ->
              ( ( U X. { Y } ) C_ M -> ( U X. { Z } ) C_ M ) ) $=
            ( csn cxp wss wa cv cii ctx ccnp cfv wcel cc0 cicc crab adantr cuni
            co c1 elssuni iiuni sseqtrrdi elunii eleqtrrdi syl2anc snssd xpss12
            syl cres crest ccn wrex wf wral cvmlift2lem5 fssresd simpr sseqtrdi
            sseldd ssrab simprbi r19.21bi ctopon iitopon txtopon mp2an cnpresti
            toponunii syl3anc ralrimiva wb resttopon sylancr ctop ccvm toptopon
            cvmtop1 sylib cncnp mpbir2and wceq sneq xpeq2d oveq2d oveq1d rspcev
            reseq2d eleq12d imp syldan xpss2 txtopi restuni sseqtrd sselda eqid
            iitop cncnpi cnt a1i txopn syl22anc isopn3i sseqtrrd cnprest mpbird
            ad2antrr ssrabdv ex ) AIRUMZUNZPUOZISUMZUNZPUOAUUBUPZUUDODUQZURURUS
            VHZGUTVHVAVBZDVCVIVDVHZUUIUNZVEZPUUEUUHDUUJUUDUUEIUUIUOZUUCUUIUOUUD
            UUJUOUUEIURVBZUULAUUMUUBUHVFZUUMIURVGZUUIIURVJVKVLVRZUUESUUIASUUIVB
            ZUUBASQVBZQURVBZUUQUKUIUURUUSUPSUUOUUISQURVMVKVNVOVFVPIUUIUUCUUIVQV
            OUUEUUFUUDVBZUPZUUHOIQUNZVSZUUFUUGUVBVTVHZGUTVHVAVBZUVAUVCUVDGWAVHV
            BZUUFUVDVGZVBUVEUUEUVFUUTAUUBOIEUQZUMZUNZVSZUUGUVJVTVHZGWAVHZVBZEQW
            BZUVFUUERQVBZOUUAVSZUUGUUAVTVHZGWAVHZVBZUVOAUVPUUBUJVFZUUEUVTUUAFUV
            QWCZUVQUUFUVRGUTVHVAVBZDUUAWDZUUEUUJFUUAOAUUJFOWCZUUBABCDFGHJKLMNOT
            UAUBUCUDUEUFWEZVFUUEUULYTUUIUOUUAUUJUOZUUPUUERUUIUUEQUUIRUUEUUSQUUI
            UOZAUUSUUBUIVFZUUSQUUOUUIQURVJVKVLVRZUWAWIVPIUUIYTUUIVQVOZWFUUEUWCD
            UUAUUEUUFUUAVBZUPUWGUWLUUHUWCUUEUWGUWLUWKVFUUEUWLWGUUEUUHDUUAUUEUUA
            UUKUOZUUHDUUAWDZUUEUUAPUUKAUUBWGUGWHUWMUWGUWNUUHDUUJUUAWJWKVRWLUUAU
            UFOUUGGUUJUUJUUGURUUIWMVAVBZUWOUUGUUJWMVAVBZWNWNURURUUIUUIWOWPZWRZW
            QWSWTUUEUVRUUAWMVAVBZGFWMVAVBZUVTUWBUWDUPXAUUEUWPUWGUWSUWQUWKUUAUUG
            UUJXBXCUUEGXDVBZUWTAUXAUUBAKGNXEVHVBUXAUAGKNXGVRVFGFTXFXHDUVQUVRGUU
            AFXIVOXJUVNUVTERQUVHRXKZUVKUVQUVMUVSUXBUVJUUAOUXBUVIYTIUVHRXLXMZXQU
            XBUVLUVRGWAUXBUVJUUAUUGVTUXCXNXOXRXPVOAUVOUVFULXSXTVFUUEUUDUVGUUFUU
            EUUDUVBUVGUUEUUCQUOUUDUVBUOUUESQAUURUUBUKVFVPUUCQIYAVRZUUEUUGXDVBZU
            VBUUJUOZUVBUVGXKURURYGYGYBZUUEUULUWHUXFUUPUWJIUUIQUUIVQVOZUVBUUGUUJ
            UWRYCXCYDYEUUFUVCUVDGUVGUVGYFYHVOUVAUXEUXFUUFUVBUUGYIVAVAZVBUWEUUHU
            VEXAUXEUVAUXGYJUUEUXFUUTUXHVFUUEUUDUXIUUFUUEUUDUVBUXIUXDUUEUXEUVBUU
            GVBZUXIUVBXKUXGUUEURXDVBZUXKUUMUUSUXJUXKUUEYGYJZUXLUUNUWIIQURURXDXD
            YKYLUVBUUGYMXCYNYEAUWEUUBUUTUWFYQUVBUUFOUUGGUUJFUWRTYOYLYPYRUGVLYS
            $.
        $}

        $d c ph $.
        cvmlift2.a $e |- A =
          { a e. ( 0 [,] 1 ) | ( ( 0 [,] 1 ) X. { a } ) C_ M } $.
        cvmlift2.s $e |- S = { <. r , t >. |
          ( t e. ( 0 [,] 1 ) /\ E. u e. ( ( nei ` II ) ` { r } )
            ( ( u X. { a } ) C_ M <-> ( u X. { t } ) C_ M ) ) } $.
        $( Lemma for ~ cvmlift2 .  (Contributed by Mario Carneiro,
           1-Jun-2015.) $)
        cvmlift2lem12 $p |- ( ph -> K e. ( ( II tX II ) Cn C ) ) $=
          ( vv vb vw vk vs vc vd cii ctx co ccn wcel cc0 cxp ccnp cfv wral crab
          cv wss csn ciun wceq iiuni a1i cin wb wa wrex ctop iitop copab sylibr
          wel vex adantl jca df-xp mp2an cop cres crest wi w3a cuni cdif adantr
          c0 cmpt eqid simprr simprl cvmlift2lem10 simplrl simplrr syl22anc wal
          eleqtrrdi syl2anr ad3antrrr sneq xpeq2d reseq2d oveq2d oveq1d eleq12d
          simpr biimtrid cvmlift2lem11 impbid syl2anc sseq12i ssopab2bw opelxpi
          weq bitri rexlimdvva mpd eleq1d ralrimiva sylib cvmlift2lem1 syl cmpo
          ex elrab2 ctopon iitopon cvv sylancr c1 wf cvmlift2lem5 iunid xpiundi
          cicc xpeq2i eqtr3i cconn iiconn ccld inss1 cnt ccmp iicmp txtopi cnei
          neiss2 mpan snss a1d rexlimiv simpl ssopab2i 3sstr4i txunii ccnv cima
          ntropn chmeo cpw ccvm elunii opnneip syl3anc simplr2 cbvrexvw simplr3
          txopn rspe ssntr simpr1 simpr2 sseldd opeq2 ralsn anassrs dfss3 eleq1
          alrimivv ralxp txtube ntrss2 mpan2 ralcom 3bitr2i ralimi bicom rexbii
          sstr r2al ralbii reqabi baib ad3antlr elssuni sseqtrrdi sselda sseq1d
          sylbi bibi12d imbitrrid ralimdva anim2d reximdva ssrab2 eqsstri isclo
          syl5 sselid 0elunit wrel relxp opelxp id df-3an wfn ffnd fnov reseq1d
          snssd resmpo cvmlift2lem8 sylan syldan elsni eqeq1d syl5ibrcom 3impia
          mpoeq3dva 3eqtrd cnmpt1st ccom cvmlift2lem2 simp1d cnmpt21f cnmpt2res
          simplll snex txrest mp4an oveq1i eqeltrd rspcev xpss12 restuni cncnpi
          eleqtrd expcom isopn3i eleqtrrd cnprest sylibrd embantd expimpd fveq2
          eleq2d sylanbrc opeq2d relssdv ne0d connclo eqtr3di eqsstrid sseqtrdi
          inss2 rabid2 iunss ssrab simprbi txtopon cvmtop1 toptopon mpbir2and
          cncnp ) AQURURUSUTZIVAUTVBZVCUUAUUFUTZVWHVDZHQUUBZQDVIZVWFIVEUTZVFZVB
          ZDVWIVGZABCDHIJLMNOPQUAUBUCUDUEUFUGUUCZAVWIVWNDVWIVHZVJZVWOAVWIRVWQAV
          WITVWHVWHTVIZVKZVDZVLZRVWHTVWHVWTVLZVDVWIVXBVXCVWHVWHTVWHUUDUUGTVWHVW
          TVWHUUEUUHAVXARVJZTVWHVGZVXBRVJAVWHVXDTVWHVHZVMVXEAGVWHVXFAGURVWHVNUR
          UUIVBAUUJVOAURURUUKVFZVPZURGURVXGUULATUKWDZVWSGVBZFVIZGVBZVQZFUKVIZVG
          ZVRZUKURVSZTVWHVGZGVXHVBZAVXQTVWHAVWSVWHVBZVRZVXIVWHVXNVDZKVWFUUMVFZV
          FZVJZVRZUKURVSVXQVYAUKVWSURURVYDVWHVWHVNVNURUUNVBVYAUUOVOURVTVBZVYAWA
          VOVYDVWFVBZVYAVWFVTVBZKVWIVJZVYHURURWAWAUUPZVXKVWHVBZEVIZVWTVDRVJZVYM
          VXKVKZVDRVJZVQZESVIZVKZURUUQVFVFZVSZVRZSFWBZVYRVWHVBZVYLVRZSFWBKVWIWU
          BWUESFWUBWUDVYLWUAWUDVYLVYQWUDEVYTVYMVYTVBZWUDVYQWUFVYSVWHVJZWUDVYGWU
          FWUGWAVYSURVYMVWHVNUURUUSVYRVWHSWEUUTWCUVAUVBWFVYLWUAUVCWGUVDUJSFVWHV
          WHWHUVEZKVWFVWIURURVWHVWHWAWAVNVNUVFZUVIWIVOVYAULVIZUMVIZWJZVYDVBZUMV
          WTVGZULVWHVGZVXAVYDVJZVYAWUNULVWHAVXTWUJVWHVBZWUNAVXTWUQVRZVRZWUJVWSW
          JZVYDVBZWUNWUSULEWDZVXIQVYMWUKVKZVDZWKZVWFWVDWLUTZIVAUTZVBZUMVXNVSZQV
          YMVXNVDZWKZVWFWVJWLUTZIVAUTVBZWMZWNZUKURVSEURVSWVAWUSBCDUMUKEHIJUNPUO
          VIZWOMUVGUNVIZUVHVMUPVIZUQVIVPWRVMUQWVPWVRVKZWPVGMWVRWKIWVRWLUTPWVQWL
          UTUVJUTVBVRUPWVPVGVRUOIUVKWRVKWPVHWSZLUNMNOPQWUJVWSUOUPUQUAAMIPUVLUTV
          BZWURUBWQZANVWFPVAUTVBZWURUCWQZAJHVBZWURUDWQZAJMVFVCVCNUTVMZWURUEWQZU
          FUGWVTWTZAVXTWUQXAAVXTWUQXBXCWUSWVOWVAEUKURURWUSVYMURVBZVXNURVBZVRZVR
          ZWVOWVAWWMWVOVRZWVJVYDWUTWWNVYIVYJWVJVWFVBZWVJKVJZWVJVYDVJVYIWWNVYKVO
          VYJWWNWUHVOWWNVYGVYGWWJWWKWWOVYGWWNWAVOZWWQWUSWWJWWKWVOXDZWUSWWJWWKWV
          OXEZVYMVXNURURVTVTUVSZXFWWNSEWDZFUKWDZVRZWUBWMZFXGSXGZWWPWWNWXDSFWWNW
          XCWUBWWNWXCVRZVYLWUAWXCWXBWWKVYLWWNWXAWXBXQWWSWXBWWKVRVXKURWOZVWHVXKV
          XNURUVMVNXHXIWXFWUFVYQWUAWXFVYGWWJWXAWUFVYGWXFWAVOWWNWWJWXCWWRWQZWWNW
          XAWXBXBVYRURVYMUVNUVOWXFVYNVYPWXFBCDUPHIJVYMLMNOPQRVXNVWSVXKUAWUSWWAW
          WLWVOWXCWWBXJZWUSWWCWWLWVOWXCWWDXJZWUSWWEWWLWVOWXCWWFXJZWUSWWGWWLWVOW
          XCWWHXJZUFUGUHWXHWWNWWKWXCWWSWQZWVBVXIWVNWWMWXCUVPZWWNWXAWXBXAZQVYMWV
          SVDZWKZVWFWXPWLUTZIVAUTZVBZUPVXNVSWVIWXFWVMWXTWVHUPUMVXNUPUMYEZWXQWVE
          WXSWVGWYAWXPWVDQWYAWVSWVCVYMWVRWUKXKXLZXMWYAWXRWVFIVAWYAWXPWVDVWFWLWY
          BXNXOXPUVQWVBVXIWVNWWMWXCUVRXRZXSWXFBCDUPHIJVYMLMNOPQRVXNVXKVWSUAWXIW
          XJWXKWXLUFUGUHWXHWXMWXOWXNWYCXSXTVYQEVYTUVTYAWGYOUWJWWPWXCSFWBZWUCVJW
          XEWVJWYDKWUCSFVYMVXNWHUJYBWXCWUBSFYCYFWCKVWFWVJVWIWUIUWAXFWWNWVBVXIWU
          TWVJVBWWMWVBVXIWVNUWBWWMWVBVXIWVNUWCWUJVWSVYMVXNYDYAUWDYOYGYHWUMWVAUM
          VWSTWEUMTYEWULWUTVYDWUKVWSWUJUWEYIUWFWCUWGYJWUPVYMVYDVBZEVXAVGWUOEVXA
          VYDUWHWYEWUMEULUMVWHVWTVYMWULVYDUWIUWKYFWCAVXTXQUWLVYAVYFVXPUKURVYAWW
          KVRZVYEVXOVXIVYEWUBSVWHVGZFVXNVGZWYFVXOVYEVYBKVJZWYHVYEVYDKVJZWYIVYIV
          YJWYJVYKWUHKVWFVWIWUIUWMWIVYBVYDKUWTUWNWYIWUDWXBVRZSFWBZWUCVJZWYHVYBW
          YLKWUCSFVWHVXNWHUJYBWYMWYKWUBWMFXGSXGWUBFVXNVGSVWHVGWYHWYKWUBSFYCWUBS
          FVWHVXNUXAWUBSFVWHVXNUWOUWPYFYKWYFWYGVXMFVXNWYGVXMWYFWXBVRZVXDVWHVYOV
          DZRVJZVQZWYGWUASVWHVGZWYQWUBWUASVWHVYLWUAXQUWQWYRVXDWYPTSEFRYLWYRVYPV
          YNVQZEVYTVSZSVWHVGWYPVXDWMWUAWYTSVWHVYQWYSEVYTVYNVYPUWRUWSUXBFSETRYLU
          XJXTYMWYNVXJVXDVXLWYPVXTVXJVXDVQAWWKWXBVXJVXTVXDVXDTGVWHUIUXCUXDUXEWY
          NVYLVXLWYPVQWYFVXNVWHVXKWWKVXNVWHVJZVYAWWKVXNWXGVWHVXNURUXFVNUXGZWFUX
          HVXLVYLWYPVXDWYPTVXKVWHGTFYEZVXAWYORXUCVWTVYOVWHVWSVXKXKXLUXIUIYPUXDY
          MUXKUXLUXMUXSUXNUXOYHYJVYGGVWHVJVXSVXRVQWAGVXFVWHUIVXDTVWHUXPUXQTUKFG
          URVWHVNUXRWIWCZUXTAGVCAVCVWHVBZVWHVCVKZVDZRVJZVCGVBXUEAUYAVOZASTXUGRX
          UGUYBAVWHXUFUYCVOVYRVWSWJZXUGVBWUDVWSXUFVBZVRAXUJRVBZVYRVWSVWHXUFUYDA
          WUDXUKXULAWUDVRZXULXUKVYRVCWJZRVBZXUMXUNVWIVBZQXUNVWLVFZVBZXUOWUDWUDX
          UEXUPAWUDUYEXUIVYRVCVWHVWHYDXIXUMWXAVCVXNVBZWVNWNZUKURVSEURVSXURXUMBC
          DUMUKEHIJWVTLUNMNOPQVYRVCUOUPUQUAAWWAWUDUBWQAWWCWUDUCWQAWWEWUDUDWQAWW
          GWUDUEWQUFUGWWIAWUDXQXUEXUMUYAVOXCXUMXUTXUREUKURURXUTWXAXUSVRZWVNVRXU
          MWWLVRZXURWXAXUSWVNUYFXVBXVAWVNXURXVBXVAVRZWVIWVMXURXVCXUSQVYMXUFVDZW
          KZVWFXVDWLUTZIVAUTZVBZWVIXVBWXAXUSXAXVCXVEULUMVYMXUFWUJOVFZYNZXVGXVCX
          VEULUMVWHVWHWUJWUKQUTZYNZXVDWKZULUMVYMXUFXVKYNZXVJXVCQXVLXVDXVCQVWIUY
          GQXVLVMXVCVWIHQAVWJWUDWWLXVAVWPXJZUYHULUMVWHVWHQUYIYKUYJXVCVYMVWHVJZX
          UFVWHVJZXVMXVNVMXVCWWJXVPXUMWWJWWKXVAXDZWWJVYMWXGVWHVYMURUXFVNUXGYMZA
          XVQWUDWWLXVAAVCVWHXUIUYKXJZULUMVWHVWHVYMXUFXVKUYLYAXVCULUMVYMXUFXVKXV
          IXVCWVBWUKXUFVBZXVKXVIVMZXVCWVBVRXWBXWAWUJVCQUTZXVIVMZXVCWVBWUQXWDXVC
          VYMVWHWUJXVSUXHXVCAWUQXWDAWUDWWLXVAVUHZABCDHIJLMNOPQWUJUAUBUCUDUEUFUG
          UYMUYNUYOXWAXVKXWCXVIXWAWUKVCWUJQWUKVCUYPXNUYQUYRUYSUYTVUAXVCXVJURVYM
          WLUTZURXUFWLUTZUSUTZIVAUTXVGXVCULUMXVIURXWFIURXWGXUFVWHVYMVWHXWFWTURV
          WHYQVFVBZXVCYRVOZXVSXWGWTXWJXVTXVCULUMWUJOURURURIVWHVWHXWJXWJXVCULUMU
          RURVWHVWHXWJXWJVUBXVCAOURIVAUTVBZXWEAXWKMOVUCDVWHVWKVCNUTWSVMVCOVFJVM
          ADHIJLMNOPUAUBUCUDUEUFVUDVUEYMVUFVUGXVFXWHIVAVYGVYGVYMYSVBXUFYSVBXVFX
          WHVMWAWAEWEVCVUIVYMXUFURURVTVTYSYSVUJVUKVULXHVUMWVHXVHUMVCVXNWUKVCVMZ
          WVEXVEWVGXVGXWLWVDXVDQXWLWVCXUFVYMWUKVCXKXLZXMXWLWVFXVFIVAXWLWVDXVDVW
          FWLXWMXNXOXPVUNYAXVCWVMWVKXUNWVLIVEUTVFVBZXURXVCXUNWVLWOZVBZWVMXWNWMX
          VCXUNWVJXWOXVAXUNWVJVBXVBVYRVCVYMVXNYDWFZXVCVYIWVJVWIVJZWVJXWOVMVYKXV
          CXVPXUAXWRXVSXVCWWKXUAXUMWWJWWKXVAXEZXUBYMVYMVWHVXNVWHVUOYAZWVJVWFVWI
          WUIVUPYTVURWVMXWPXWNXUNWVKWVLIXWOXWOWTVUQVUSYMXVCVYIXWRXUNWVJVYCVFZVB
          VWJXURXWNVQVYIXVCVYKVOXWTXVCXUNWVJXXAXWQXVCVYIWWOXXAWVJVMVYKXVCVYGVYG
          WWJWWKWWOVYGXVCWAVOZXXBXVRXWSWWTXFWVJVWFVUTYTVVAXVOWVJXUNQVWFIVWIHWUI
          UAVVBXFVVCVVDVVEXRYGYHVWNXURDXUNVWIRVWKXUNVMVWMXUQQVWKXUNVWLVVFVVGUHY
          PVVHXUKXUJXUNRXUKVWSVCVYRVWSVCUYPVVIYIUYRVVEXRVVJVXDXUHTVCVWHGVWSVCVM
          ZVXAXUGRXXCVWTXUFVWHVWSVCXKXLUXIUIYPVVHVVKAVXHVXGGURVXGVVPXUDUXTVVLUI
          VVMVXDTVWHVVQYKTVWHVXARVVRWCVVNUHVVOVWRVWIVWIVJVWOVWNDVWIVWIVVSVVTYMA
          VWFVWIYQVFVBZIHYQVFVBZVWGVWJVWOVRVQXWIXWIXXDYRYRURURVWHVWHVWAWIAIVTVB
          ZXXEAWWAXXFUBIMPVWBYMIHUAVWCYKDQVWFIVWIHVWEYTVWD $.
      $}

      $( Lemma for ~ cvmlift2 .  (Contributed by Mario Carneiro,
         7-May-2015.) $)
      cvmlift2lem13 $p |- ( ph -> E! g e. ( ( II tX II ) Cn C )
        ( ( F o. g ) = G /\ ( 0 g 0 ) = P ) ) $=
        ( vu vt va vd vv vb vc vr cv ccom wceq cc0 co wa cii ctx wrex wrmo wreu
        ccn wcel c1 cicc csn cxp ccnp cfv crab wss cnei copab weq fveq2 cbvrabv
        wb eleq2d xpeq2d sseq1d simpr eleq1d xpeq1 bibi12d cbvrexvw simpl sneqd
        sneq fveq2d bibi2d rexeqbidv bitrid cbvopabv cvmlift2lem12 cvmlift2lem7
        anbi12d 0elunit cvmlift2lem8 mpan2 cmpt cvmlift2lem2 simp3d eqtrd coeq2
        eqeq1d rspcev syl12anc cop iitop iiuni txunii cconn iiconn txconn mp2an
        oveq a1i cnlly iinllyconn txnlly opelxpi eqtrdi cvmliftmo eqeq1i anbi2i
        df-ov rmobii sylibr reu5 sylanbrc ) AJIUJZUKZKULZUMUMYJUNZGULZUOZIUPUPU
        QUNZFVAUNZURZYOIYQUSZYOIYQUTANYQVBJNUKZKULZUMUMNUNZGULZYRABCDUBUCUMVCVD
        UNZDUJZVEZVFZNUDUJZYPFVGUNZVHZVBZUDUUDUUDVFZVIZVJZDUUDVIEFGUEUJZUUDVBZU
        FUJZUGUJZVEZVFZUUMVJZUUQUUOVEZVFZUUMVJZVPZUFUHUJZVEZUPVKVHZVHZURZUOZUHU
        EVLHJKLMNUUMUIUGOPQRSTUAUUKNUUEUUIVHZVBUDDUULUDDVMUUJUVLNUUHUUEUUIVNVQV
        OUUNUUDUUSVFZUUMVJDUGUUDDUGVMZUUGUVMUUMUVNUUFUUSUUDUUEUURWGVRVSVOUVKUCU
        JZUUDVBZUBUJZUUSVFZUUMVJZUVQUVOVEZVFZUUMVJZVPZUBUIUJZVEZUVHVHZURZUOUHUE
        UIUCUHUIVMZUEUCVMZUOZUUPUVPUVJUWGUWJUUOUVOUUDUWHUWIVTZWAUVJUVSUVQUVBVFZ
        UUMVJZVPZUBUVIURUWJUWGUVEUWNUFUBUVIUFUBVMZUVAUVSUVDUWMUWOUUTUVRUUMUUQUV
        QUUSWBVSUWOUVCUWLUUMUUQUVQUVBWBVSWCWDUWJUWNUWCUBUVIUWFUWJUVGUWEUVHUWJUV
        FUWDUWHUWIWEWFWHUWJUWMUWBUVSUWJUWLUWAUUMUWJUVBUVTUVQUWJUUOUVOUWKWFVRVSW
        IWJWKWOWLWMABCDEFGHJKLMNOPQRSTUAWNAUUBUMLVHZGAUMUUDVBZUUBUWPULWPABCDEFG
        HJKLMNUMOPQRSTUAWQWRALUPFVAUNVBJLUKDUUDUUEUMKUNWSULUWPGULADEFGHJKLMOPQR
        STWTXAXBYOUUAUUCUOINYQYJNULZYLUUAYNUUCUWRYKYTKYJNJXCXDUWRYMUUBGUMUMYJNX
        OXDWOXEXFAYLUMUMXGZYJVHZGULZUOZIYQUSYSAEFGIJKMYPUWSUULOUPUPUUDUUDXHXHXI
        XIXJPYPXKVBZAUPXKVBZUXDUXCXLXLUPUPXMXNXPYPXKXQZVBZAUPUXEVBZUXGUXFXRXRXK
        UPUPBCBUJCUJXMXSXNXPUWSUULVBZAUWQUWQUXHWPWPUMUMUUDUUDXTXNXPQRAGJVHUMUMK
        UNUWSKVHSUMUMKYEYAYBYOUXBIYQYNUXAYLYMUWTGUMUMYJYEYCYDYFYGYOIYQYHYI $.
    $}

    $( A two-dimensional version of ~ cvmlift .  There is a unique lift of
       functions on the unit square ` II tX II ` which commutes with the
       covering map.  (Contributed by Mario Carneiro, 1-Jun-2015.) $)
    cvmlift2 $p |- ( ph -> E! f e. ( ( II tX II ) Cn C )
      ( ( F o. f ) = G /\ ( 0 f 0 ) = P ) ) $=
      ( vz vg cv cc0 co wceq cfv vx vy vh vw vu vv vk ccom c1 cicc cmpt cii ccn
      crio cmpo coeq2 oveq1 cbvmptv a1i eqeq12d fveq1 eqeq1d anbi12d cbvriotavw
      oveq2 mpteq2dv eqeq2d fveq2 riotabidv eqtrid fveq1d cbvmpov cvmlift2lem13
      wa ) AUAUBNBCDOEFGFUCPZUHZUDQUIUJRZUDPZQGRZUKZSZQVOTZDSZVNZUCULCUMRZUNZHU
      EUFVQVQUFPZFUGPZUHZUDVQUEPZVRGRZUKZSZQWHTZWJWFTZSZVNZUGWEUNZTZUOIJKLMWDFO
      PZUHZNVQNPZQGRZUKZSZQWTTZDSZVNUCOWEVOWTSZWAXEWCXGXHVPXAVTXDVOWTFUPVTXDSXH
      UDNVQVSXCVRXBQGUQURUSUTXHWBXFDQVOWTVAVBVCVDUEUFUAUBVQVQWSUBPZXANVQUAPZXBG
      RZUKZSZXFXJWFTZSZVNZOWEUNZTWGXQTWJXJSZWGWRXQXRWRXANVQWJXBGRZUKZSZXFWOSZVN
      ZOWEUNXQWQYCUGOWEWHWTSZWMYAWPYBYDWIXAWLXTWHWTFUPWLXTSYDUDNVQWKXSVRXBWJGVE
      URUSUTYDWNXFWOQWHWTVAVBVCVDXRYCXPOWEXRYAXMYBXOXRXTXLXAXRNVQXSXKWJXJXBGUQV
      FVGXRWOXNXFWJXJWFVHVGVCVIVJVKWGXIXQVHVLVM $.
  $}

  ${
    $d f s x A $.  $d f s x B $.  $d f h s x F $.  $d f g h J $.  $d g h s M $.
    $d f g h s x C $.  $d f g h s x G $.  $d f g h s x H $.  $d g h s ph $.
    $d g h s N $.  $d f h x P $.
    cvmliftpht.b $e |- B = U. C $.
    cvmliftpht.m $e |- M =
      ( iota_ f e. ( II Cn C ) ( ( F o. f ) = G /\ ( f ` 0 ) = P ) ) $.
    cvmliftpht.n $e |- N =
      ( iota_ f e. ( II Cn C ) ( ( F o. f ) = H /\ ( f ` 0 ) = P ) ) $.
    cvmliftpht.f $e |- ( ph -> F e. ( C CovMap J ) ) $.
    cvmliftpht.p $e |- ( ph -> P e. B ) $.
    cvmliftpht.e $e |- ( ph -> ( F ` P ) = ( G ` 0 ) ) $.
    ${
      cvmliftphtlem.g $e |- ( ph -> G e. ( II Cn J ) ) $.
      cvmliftphtlem.h $e |- ( ph -> H e. ( II Cn J ) ) $.
      cvmliftphtlem.k $e |- ( ph -> K e. ( G ( PHtpy ` J ) H ) ) $.
      cvmliftphtlem.a $e |- ( ph -> A e. ( ( II tX II ) Cn C ) ) $.
      cvmliftphtlem.c $e |- ( ph -> ( F o. A ) = K ) $.
      cvmliftphtlem.0 $e |- ( ph -> ( 0 A 0 ) = P ) $.
      $( Lemma for ~ cvmliftpht .  (Contributed by Mario Carneiro,
         6-Jul-2015.) $)
      cvmliftphtlem $p |- ( ph -> A e. ( M ( PHtpy ` C ) N ) ) $=
        ( vs vx cii ccn co wcel ccom wceq cc0 cfv cvmliftiota simp1d c1 phtpy01
        simpld eqtrd cv cmpt wral wa cop cxp wf iitop iiuni cnf 0elunit opelxpi
        syl mpan2 fvco3 syl2an adantr fveq1d eqtr3d df-ov fveq2i 3eqtr4g ctopon
        crio a1i mpteq2dva fovcdm mp3an3 sylan eqidd eqid feqmptd fveq2 3eqtr4d
        fmptco wreu wb cnmptc cnmpt12f cvmlift syl22anc coeq2 eqeq1d fveq1 ovex
        oveq1 fvmpt ax-mp eqtrdi anbi12d riota2 syl2anc eqtrid cvv mpteqb ovexd
        mpbi2and mprg sylib r19.21bi 1elunit simprd csn cconn ffvelcdm cnconst2
        sylancl syl3anc mpan fconstmpt eqtr4di mp3an2 fcoconst oveq2 cvmliftmoi
        fvex fvconst2 rspcv mpsyl cicc ctx txunii cphtpy chtpy phtpyhtpy sseldd
        iitopon htpyi cuni ccvm cvmcn cnmptid cnlly iinllyconn cvmtop1 toptopon
        iiconn ctop phtpyi simp3d fveq2d eqtr4d simp2d 3eqtrd eqeq12d isphtpy2d
        wfn ffnd ) ALMBDUFALUHDUIUJZUKZGLULZHUMZUNLUOZEUMZACDEFGHLJNOQTRSUPZUQZ
        AMUVJUKZGMULIUMUNMUOEUMACDEFGIMJNPQUARAEGUOZUNHUOZUNIUOZSAUVTUWAUMURHUO
        ZURIUOUMAHIKJTUAUBUSUTVAZUPUQZUCAUFVBZUNBUJZUWELUOZUMZUFUNURUUAUJZAUFUW
        IUWFVCZUFUWIUWGVCZUMZUWHUFUWIVDZALUWJUWKALGFVBZULZHUMZUNUWNUOZEUMZVEZFU
        VJWEZUWJOAGUWJULZHUMZUNUNBUJZEUMZUWTUWJUMZAUFUWIUWFGUOZVCUFUWIUWEHUOZVC
        UXAHAUFUWIUXFUXGAUWEUWIUKZVEZUXFUWEUNKUJZUXGUXIUWEUNVFZBUOZGUOZUXKKUOZU
        XFUXJUXIUXKGBULZUOZUXMUXNAUWIUWIVGZCBVHZUXKUXQUKZUXPUXMUMUXHABUHUHUUBUJ
        ZDUIUJUKUXRUCBUXTDUXQCUHUHUWIUWIVIVIVJVJUUCNVKVNZUXHUNUWIUKZUXSVLUWEUNU
        WIUWIVMVOUXQCUXKGBVPVQUXIUXKUXOKAUXOKUMUXHUDVRZVSVTUWFUXLGUWEUNBWAWBUWE
        UNKWAWCUXIUXJUXGUMZUWEURKUJZUWEIUOZUMZAUWEHIKUHJUWIUHUWIWDUOUKZAUUHWFZT
        UAAHIJUUDUOUJHIUHJUUEUJUJKAHIJTUAUUFUBUUGUUIZUTVAWGAUFUGUWICUWFUGVBZGUO
        ZUXFUWJGAUXRUXHUWFCUKZUYAUXRUXHUYBUYMVLUWEUNCUWIUWIBWHWIWJAUWJWKAUGCJUU
        JZGAGDJUIUJUKZCUYNGVHAGDJUUKUJUKZUYOQDGJUULVNGDJCUYNNUYNWLZVKVNZWMZUYKU
        WFGWNWPAUFUWIUYNHAHUHJUIUJZUKZUWIUYNHVHTHUHJUWIUYNVJUYQVKVNWMWOUEAUWJUV
        JUKUWSFUVJWQZUXBUXDVEZUXEWRAUFUWEUNBUHUHUHDUWIUYIAUFUHUWIUYIUUMZAUFUNUH
        UHUWIUWIUYIUYIUYBAVLWFZWSZUCWTAUYPVUAECUKZUVSUVTUMZVUBQTRSCDEFGHJNXAXBU
        WSVUCFUVJUWJUWNUWJUMZUWPUXBUWRUXDVUIUWOUXAHUWNUWJGXCXDVUIUWQUXCEVUIUWQU
        NUWJUOZUXCUNUWNUWJXEUYBVUJUXCUMVLUFUNUWFUXCUWIUWJUWEUNUNBXGUWJWLUNUNBXF
        ZXHXIXJXDXKXLXMXRXNAUFUWICLAUVKUWICLVHZUVQLUHDUWICVJNVKVNZWMVTUWFXOUKUW
        LUWMWRUFUWIUFUWIUWFUWGXOXPUXHUWEUNBXQXSXTZYAAUWEURBUJZUWEMUOZUMZUFUWIAU
        FUWIVUOVCZUFUWIVUPVCZUMZVUQUFUWIVDZAMVURVUSAMUWOIUMZUWRVEZFUVJWEZVURPAG
        VURULZIUMZUNURBUJZEUMZVVDVURUMZAUFUWIVUOGUOZVCUFUWIUYFVCVVEIAUFUWIVVJUY
        FUXIVVJUYEUYFUXIUWEURVFZBUOZGUOZVVKKUOZVVJUYEUXIVVKUXOUOZVVMVVNAUXRVVKU
        XQUKZVVOVVMUMUXHUYAUXHURUWIUKZVVPYBUWEURUWIUWIVMVOUXQCVVKGBVPVQUXIVVKUX
        OKUYCVSVTVUOVVLGUWEURBWAWBUWEURKWAWCUXIUYDUYGUYJYCVAWGAUFUGUWICVUOUYLVV
        JVURGAUXRUXHVUOCUKZUYAUXRUXHVVQVVRYBUWEURCUWIUWIBWHWIWJAVURWKUYSUYKVUOG
        WNWPAUFUWIUYNIAIUYTUKZUWIUYNIVHUAIUHJUWIUYNVJUYQVKVNWMWOAVVGUVNEVVQAUNU
        WEBUJZUVNUMZUFUWIVDZVVGUVNUMZYBAUFUWIVVTVCZUFUWIUVNVCZUMZVWBAVWDUWIUVNY
        DVGZVWEACDGJUHVWDVWGUNUWINVJQUHYEUKAUURWFZUHYEUUNUKAUUOWFZVUEAUFUNUWEBU
        HUHUHDUWIUYIVUFVUDUCWTAUYHDCWDUOUKZUVNCUKZVWGUVJUKUYIADUUSUKZVWJAUYPVWL
        QDGJUUPVNDCNUUQXTZAVULUYBVWKVUMVLUWICUNLYFYHZUVNUHDUWICYGYIAUFUWIVVTGUO
        ZVCZUWIUVNGUOZYDVGZGVWDULGVWGULZAVWPUFUWIVWQVCVWRAUFUWIVWOVWQUXIUNUWEKU
        JZUVTVWOVWQUXIVWTUVTUMZURUWEKUJZUWBUMZAUWEHIKJTUAUBUUTZUTUXIUNUWEVFZBUO
        ZGUOZVXEKUOZVWOVWTUXIVXEUXOUOZVXGVXHAUXRVXEUXQUKZVXIVXGUMUXHUYAUYBUXHVX
        JVLUNUWEUWIUWIVMYJUXQCVXEGBVPVQUXIVXEUXOKUYCVSVTVVTVXFGUNUWEBWAWBUNUWEK
        WAWCUXIVWQUVSUVTUXIUVNEGAUVOUXHAUVKUVMUVOUVPUVAZVRUVBAVUHUXHSVRVAWOWGUF
        UWIVWQYKYLAUFUGUWICVVTUYLVWOVWDGAUXRUXHVVTCUKZUYAUXRUYBUXHVXLVLUNUWECUW
        IUWIBWHYMWJAVWDWKUYSUYKVVTGWNWPAGCUVHZVWKVWSVWRUMACUYNGUYRUVIZVWNGUWICU
        VNYNXMWOAUXCUVNUNVWDUOZUNVWGUOZAUXCEUVNUEVXKUVCUYBVXOUXCUMVLUFUNVVTUXCU
        WIVWDUWEUNUNBYOVWDWLVUKXHXIUYBVXPUVNUMVLUWIUVNUNUNLYQYRXIWCYPUFUWIUVNYK
        XJVVTXOUKVWFVWBWRUFUWIUFUWIVVTUVNXOXPUXHUNUWEBXQXSXTZVWAVWCUFURUWIUWEUR
        UMZVVTVVGUVNUWEURUNBYOXDYSYTVXKVAAVURUVJUKVVCFUVJWQZVVFVVHVEZVVIWRAUFUW
        EURBUHUHUHDUWIUYIVUDAUFURUHUHUWIUWIUYIUYIVVQAYBWFWSZUCWTAUYPVVSVUGUVSUW
        AUMVXSQUARUWCCDEFGIJNXAXBVVCVXTFUVJVURUWNVURUMZVVBVVFUWRVVHVYBUWOVVEIUW
        NVURGXCXDVYBUWQVVGEVYBUWQUNVURUOZVVGUNUWNVURXEUYBVYCVVGUMVLUFUNVUOVVGUW
        IVURUWEUNURBXGVURWLUNURBXFXHXIXJXDXKXLXMXRXNAUFUWICMAUVRUWICMVHUWDMUHDU
        WICVJNVKVNWMVTVUOXOUKVUTVVAWRUFUWIUFUWIVUOVUPXOXPUXHUWEURBXQXSXTYAAVWAU
        FUWIVXQYAAURUWEBUJZURLUOZUMZUFUWIAUFUWIVYDVCZUFUWIVYEVCZUMZVYFUFUWIVDZA
        VYGUWIVYEYDVGZVYHACDGJUHVYGVYKUNUWINVJQVWHVWIVUEAUFURUWEBUHUHUHDUWIUYIV
        YAVUDUCWTAUYHVWJVYECUKZVYKUVJUKUYIVWMAVULVVQVYLVUMYBUWICURLYFYHZVYEUHDU
        WICYGYIAUFUWIVYDGUOZVCZUWIVYEGUOZYDVGZGVYGULGVYKULZAVYOUFUWIVYPVCVYQAUF
        UWIVYNVYPUXIVYNVXBUWBVYPUXIURUWEVFZBUOZGUOZVYSKUOZVYNVXBUXIVYSUXOUOZWUA
        WUBAUXRVYSUXQUKZWUCWUAUMUXHUYAVVQUXHWUDYBURUWEUWIUWIVMYJUXQCVYSGBVPVQUX
        IVYSUXOKUYCVSVTVYDVYTGURUWEBWAWBURUWEKWAWCUXIVXAVXCVXDYCUXIURUVLUOZUWBV
        YPUXIURUVLHAUVMUXHAUVKUVMUVOUVPUVDVRVSUXIVULVVQWUEVYPUMAVULUXHVUMVRYBUW
        ICURGLVPYHVTUVEWGUFUWIVYPYKYLAUFUGUWICVYDUYLVYNVYGGAUXRUXHVYDCUKZUYAUXR
        VVQUXHWUFYBURUWECUWIUWIBWHYMWJAVYGWKUYSUYKVYDGWNWPAVXMVYLVYRVYQUMVXNVYM
        GUWICVYEYNXMWOAURUNBUJZVYEUNVYGUOZUNVYKUOZVVQAUWMWUGVYEUMZYBVUNUWHWUJUF
        URUWIVXRUWFWUGUWGVYEUWEURUNBXGUWEURLWNUVFYSYTUYBWUHWUGUMVLUFUNVYDWUGUWI
        VYGUWEUNURBYOVYGWLURUNBXFXHXIUYBWUIVYEUMVLUWIVYEUNURLYQYRXIWCYPUFUWIVYE
        YKXJVYDXOUKVYIVYJWRUFUWIUFUWIVYDVYEXOXPUXHURUWEBXQXSXTYAUVG $.
    $}

    cvmliftpht.g $e |- ( ph -> G ( ~=ph ` J ) H ) $.
    $( If ` G ` and ` H ` are path-homotopic, then their lifts ` M ` and ` N `
       are also path-homotopic.  (Contributed by Mario Carneiro,
       6-Jul-2015.) $)
    cvmliftpht $p |- ( ph -> M ( ~=ph ` C ) N ) $=
      ( co cc0 vg vh cii ccn wcel cphtpy cfv c0 wne cphtpc wbr ccom w3a isphtpc
      wceq sylib simp1d cvmliftiota simp2d c1 wa phtpc01 simpld eqtrd cv simp3d
      syl wex n0 wreu wrex ccvm adantr phtpycn sselda cicc 0elunit simpr phtpyi
      mpan2 eqtr4d cvmlift2 reurex ad2antrr simplr simprl simprrl cvmliftphtlem
      ctx simprrr ne0d rexlimddv exlimddv syl3anbrc ) AJUCCUDSZUEZKWOUEZJKCUFUG
      SZUHUIZJKCUJUGUKAWPFJULGUOTJUGDUOABCDEFGJILMOAGUCIUDSZUEZHWTUEZGHIUFUGSZU
      HUIZAGHIUJUGUKZXAXBXDUMRGHIUNUPZUQZPQURUQAWQFKULHUOTKUGDUOABCDEFHKILNOAXA
      XBXDXFUSZPADFUGZTGUGZTHUGZQAXJXKUOZUTGUGZUTHUGUOZAXEXLXNVARGHIVBVGVCVDURU
      QAUAVEZXCUEZWSUAAXDXPUAVHAXAXBXDXFVFUAXCVIUPAXPVAZFUBVEZULXOUOZTTXRSDUOZV
      AZWSUBUCUCWISZCUDSZXQYAUBYCVJYAUBYCVKXQBCDUBFXOILAFCIVLSUEZXPOVMAXCYBIUDS
      XOAGHIXGXHVNVOADBUEZXPPVMXQXIXJTTXOSZAXIXJUOZXPQVMXQYFXJUOZUTTXOSXMUOZXQT
      TUTVPSUEYHYIVAVQXQTGHXOIAXAXPXGVMAXBXPXHVMAXPVRVSVTVCWAWBYAUBYCWCVGXQXRYC
      UEZYAVAZVAZWRXRYLXRBCDEFGHIXOJKLMNAYDXPYKOWDAYEXPYKPWDAYGXPYKQWDAXAXPYKXG
      WDAXBXPYKXHWDAXPYKWEXQYJYAWFXQYJXSXTWGXQYJXSXTWJWHWKWLWMJKCUNWN $.
  $}

  ${
    $d b c d f k s w z A $.  $d f g w z I $.  $d a b c d f g k s u v w x y J $.
    $d a b c d f g h k n s u v w x y z F $.  $d f g h n x y M $.  $d f g w N $.
    $d a b c d f g h m n t v w x y z H $.  $d f g w Q $.  $d a b f m t v x S $.
    $d a b d f g h u v w x y z B $.  $d g w R $.  $d a b c d f g h n w x z X $.
    $d a b c d f g h k m n t u v w x y z G $.  $d b c d s T $.  $d f g x z Z $.
    $d a b c d f g h k m n s t u v w x y z C $.  $d a f h m n t v w x y ph $.
    $d a b c f g h m n t u v w x y z K $.  $d a b c d f g h n u v w x z P $.
    $d a b c f g h n u v w x z O $.  $d a f g h m t u v w x y z Y $.
    $d c d f h n x y W $.
    cvmlift3.b $e |- B = U. C $.
    cvmlift3.y $e |- Y = U. K $.
    cvmlift3.f $e |- ( ph -> F e. ( C CovMap J ) ) $.
    cvmlift3.k $e |- ( ph -> K e. SConn ) $.
    cvmlift3.l $e |- ( ph -> K e. N-Locally PConn ) $.
    cvmlift3.o $e |- ( ph -> O e. Y ) $.
    cvmlift3.g $e |- ( ph -> G e. ( K Cn J ) ) $.
    cvmlift3.p $e |- ( ph -> P e. B ) $.
    cvmlift3.e $e |- ( ph -> ( F ` P ) = ( G ` O ) ) $.
    ${
      cvmlift3lem1.1 $e |- ( ph -> M e. ( II Cn K ) ) $.
      cvmlift3lem1.2 $e |- ( ph -> ( M ` 0 ) = O ) $.
      cvmlift3lem1.3 $e |- ( ph -> N e. ( II Cn K ) ) $.
      cvmlift3lem1.4 $e |- ( ph -> ( N ` 0 ) = O ) $.
      cvmlift3lem1.5 $e |- ( ph -> ( M ` 1 ) = ( N ` 1 ) ) $.
      $( Lemma for ~ cvmlift3 .  (Contributed by Mario Carneiro,
         6-Jul-2015.) $)
      cvmlift3lem1 $p |- ( ph ->
        ( ( iota_ g e. ( II Cn C )
          ( ( F o. g ) = ( G o. M ) /\ ( g ` 0 ) = P ) ) ` 1 ) =
        ( ( iota_ g e. ( II Cn C )
          ( ( F o. g ) = ( G o. N ) /\ ( g ` 0 ) = P ) ) ` 1 ) ) $=
        ( cc0 cv ccom wceq cfv wa cii ccn co crio cphtpc wbr eqid fveq2d eqtr4d
        c1 cicc wf wcel iiuni cnf syl 0elunit fvco3 sylancl phtpcco2 cvmliftpht
        sconnpht2 phtpc01 simprd ) AUHFEUIZUJZGJUJZUKUHVRULDUKZUMEUNCUOUPZUQZUL
        UHVSGKUJZUKWAUMEWBUQZULUKZVCWCULVCWEULUKZAWCWECURULUSWFWGUMABCDEFVTWDHW
        CWENWCUTWEUTPUAADFULZUHJULZGULZUHVTULZAWHLGULWJUBAWILGUDVAVBAUHVCVDUPZM
        JVEZUHWLVFWKWJUKAJUNIUOUPVFWMUCJUNIWLMVGOVHVIVJWLMUHGJVKVLVBAGJKIHAJKIQ
        UCUEAWILUHKULUDUFVBUGVOTVMVNWCWECVPVIVQ $.
    $}

    $( Lemma for ~ cvmlift2 .  (Contributed by Mario Carneiro, 6-Jul-2015.) $)
    cvmlift3lem2 $p |- ( ( ph /\ X e. Y ) -> E! z e. B E. f e. ( II Cn K )
      ( ( f ` 0 ) = O /\ ( f ` 1 ) = X /\ ( ( iota_ g e. ( II Cn C )
        ( ( F o. g ) = ( G o. f ) /\ ( g ` 0 ) = P ) ) ` 1 ) = z ) ) $=
      ( va vh vw wcel wa cc0 cv cfv wceq cii ccn wrex ccom crio w3a wreu cpconn
      c1 co csconn adantr sconnpconn simpr pconncn syl3anc wi wral cicc wf eqid
      syl ccvm ad2antrr simprl syl2anc simprrl fveq2d iiuni cnf 0elunit sylancl
      cnco fvco3 3eqtr4rd cvmliftiota simp1d 1elunit simprrr eqidd fveq1 eqeq1d
      ffvelcdm eqeq2d anbi1d riotabidv fveq1d 3anbi123d rspcev syl13anc ad4antr
      coeq2 cnlly simprr1 simprr2 cvmlift3lem1 eqtrd rexlimdvaa ralrimiva eqeq2
      eqtr4d simprr3 3anbi3d rexbidv eqeq1 imbi2d ralbidv anbi12d syl12anc reu8
      cbvrexvw bitrid sylibr mpd ) AMNUGZUHZUIUDUJZUKZLULZVAYIUKZMULZUHZUDUMKUN
      VBZUOZUIFUJZUKZLULZVAYQUKZMULZVAHGUJZUPZIYQUPZULZUIUUBUKEULZUHZGUMDUNVBZU
      QZUKZBUJZULZURZFYOUOZBCUSZYHKUTUGZLNUGZYGYPYHKVCUGZUUPAUURYGRVDKVEVNAUUQY
      GTVDAYGVFLMUDKNPVGVHYHYNUUOUDYOYHYIYOUGZYNUHZUHZUUNUIUEUJZUKZLULZVAUVBUKZ
      MULZVAUUCIUVBUPZULZUUFUHZGUUHUQZUKZUFUJZULZURZUEYOUOZUUKUVLULZVIZUFCVJZUH
      ZBCUOZUUOUVAVAUUCIYIUPZULZUUFUHZGUUHUQZUKZCUGZYSUUAUUJUWEULZURZFYOUOZUVOU
      WEUVLULZVIZUFCVJZUVTUVAUIVAVKVBZCUWDVLZVAUWMUGUWFUVAUWDUUHUGZUWNUVAUWOHUW
      DUPUWAULUIUWDUKEULUVACDEGHUWAUWDJOUWDVMAHDJVOVBUGZYGUUTQVPUVAUUSIKJUNVBUG
      ZUWAUMJUNVBUGYHUUSYNVQZAUWQYGUUTUAVPYIIUMKJWEVRAECUGZYGUUTUBVPUVAYJIUKZLI
      UKZUIUWAUKZEHUKZUVAYJLIYHUUSYKYMVSZVTUVAUWMNYIVLZUIUWMUGUXBUWTULUVAUUSUXE
      UWRYIUMKUWMNWAPWBVNWCUWMNUIIYIWFWDAUXCUXAULZYGUUTUCVPWGWHWIUWDUMDUWMCWAOW
      BVNWJUWMCVAUWDWOWDUVAUUSYKYMUWEUWEULZUWIUWRUXDYHUUSYKYMWKZUVAUWEWLUWHYKYM
      UXGURFYIYOYQYIULZYSYKUUAYMUWGUXGUXIYRYJLUIYQYIWMWNUXIYTYLMVAYQYIWMWNUXIUU
      JUWEUWEUXIVAUUIUWDUXIUUGUWCGUUHUXIUUEUWBUUFUXIUUDUWAUUCYQYIIXDWPWQWRWSWNW
      TXAXBUVAUWKUFCUVAUVLCUGZUHZUVNUWJUEYOUXKUVBYOUGZUVNUHZUHZUWEUVKUVLUXNCDEG
      HIJKYIUVBLNOPAUWPYGUUTUXJUXMQXCAUURYGUUTUXJUXMRXCAKUTXEUGYGUUTUXJUXMSXCAU
      UQYGUUTUXJUXMTXCAUWQYGUUTUXJUXMUAXCAUWSYGUUTUXJUXMUBXCAUXFYGUUTUXJUXMUCXC
      UVAUUSUXJUXMUWRVPUVAYKUXJUXMUXDVPUXKUXLUVNVQUVDUVFUVMUXLUXKXFUXNYLMUVEUVA
      YMUXJUXMUXHVPUVDUVFUVMUXLUXKXGXMXHUVDUVFUVMUXLUXKXNXIXJXKUVSUWIUWLUHBUWEC
      UUKUWEULZUUNUWIUVRUWLUXOUUMUWHFYOUXOUULUWGYSUUAUUKUWEUUJXLXOXPUXOUVQUWKUF
      CUXOUVPUWJUVOUUKUWEUVLXQXRXSXTXAYAUUNUVOBUFCUUNUVDUVFUVKUUKULZURZUEYOUOUV
      PUVOUUMUXQFUEYOYQUVBULZYSUVDUUAUVFUULUXPUXRYRUVCLUIYQUVBWMWNUXRYTUVEMVAYQ
      UVBWMWNUXRUUJUVKUUKUXRVAUUIUVJUXRUUGUVIGUUHUXRUUEUVHUUFUXRUUDUVGUUCYQUVBI
      XDWPWQWRWSWNWTYCUVPUXQUVNUEYOUVPUXPUVMUVDUVFUUKUVLUVKXLXOXPYDYBYEXJYF $.

    ${
      cvmlift3.h $e |- H = ( x e. Y |-> ( iota_ z e. B E. f e. ( II Cn K )
        ( ( f ` 0 ) = O /\ ( f ` 1 ) = x /\ ( ( iota_ g e. ( II Cn C )
          ( ( F o. g ) = ( G o. f ) /\ ( g ` 0 ) = P ) ) ` 1 ) = z ) ) ) $.
      $( Lemma for ~ cvmlift2 .  (Contributed by Mario Carneiro,
         6-Jul-2015.) $)
      cvmlift3lem3 $p |- ( ph -> H : Y --> B ) $=
        ( cc0 cv cfv wceq c1 ccom wa cii ccn co crio w3a wrex wcel cvmlift3lem2
        wreu riotacl syl fmptd ) ABOUFGUGZUHNUIUJVEUHBUGZUIUJIHUGZUKJVEUKUIUFVG
        UHFUIULHUMEUNUOUPUHCUGUIUQGUMMUNUOURZCDUPZDKAVFOUSULVHCDVAVIDUSACDEFGHI
        JLMNVFOPQRSTUAUBUCUDUTVHCDVBVCUEVD $.

      $( Lemma for ~ cvmlift2 .  (Contributed by Mario Carneiro,
         6-Jul-2015.) $)
      cvmlift3lem4 $p |- ( ( ph /\ X e. Y ) -> ( ( H ` X ) = A <-> E. f e.
    ( II Cn K ) ( ( f ` 0 ) = O /\ ( f ` 1 ) = X /\ ( ( iota_ g e. ( II Cn C )
      ( ( F o. g ) = ( G o. f ) /\ ( g ` 0 ) = P ) ) ` 1 ) = A ) ) ) $=
        ( wcel wa cfv wceq cc0 cv c1 ccom cii ccn co crio w3a wrex cvmlift3lem3
        ffvelcdmda eleq1 syl5ibcom wi cicc wf eqid ccvm ad2antrr simprl syl2anc
        cnco simprr fveq2d iiuni cnf 0elunit fvco3 sylancl 3eqtr4rd cvmliftiota
        simp1d 1elunit ffvelcdm expr a1dd 3impd rexlimdva eqeq2 3anbi2d rexbidv
        syl wb riotabidv riotaex adantl eqeq1d wreu cvmlift3lem2 3anbi3d riota2
        fvmpt sylan2 bitr4d expcom pm5.21ndd ) APQUHZUIZDEUHZPLUJZDUKZULHUMZUJZ
        OUKZUNXNUJZPUKZUNJIUMZUOKXNUOZUKULXSUJGUKUIIUPFUQURZUSZUJZDUKZUTZHUPNUQ
        URZVAZXJXLEUHXMXKAQEPLABCEFGHIJKLMNOQRSTUAUBUCUDUEUFUGVBVCXLDEVDVEXJYEX
        KHYFXJXNYFUHZUIZXPXRYDXKYIXPYDXKVFZXRXJYHXPYJXJYHXPUIZUIZYCEUHZYDXKYLUL
        UNVGURZEYBVHZUNYNUHYMYLYBYAUHZYOYLYPJYBUOXTUKULYBUJGUKYLEFGIJXTYBMRYBVI
        AJFMVJURUHXIYKTVKYLYHKNMUQURUHZXTUPMUQURUHXJYHXPVLZAYQXIYKUDVKXNKUPNMVN
        VMAGEUHXIYKUEVKYLXOKUJZOKUJZULXTUJZGJUJZYLXOOKXJYHXPVOVPYLYNQXNVHZULYNU
        HUUAYSUKYLYHUUCYRXNUPNYNQVQSVRWNVSYNQULKXNVTWAAUUBYTUKXIYKUFVKWBWCWDYBU
        PFYNEVQRVRWNWEYNEUNYBWFWAYCDEVDVEWGWHWIWJXKXJXMYGWOXKXJUIXMXPXRYCCUMZUK
        ZUTZHYFVAZCEUSZDUKZYGXJXMUUIWOXKXJXLUUHDXIXLUUHUKABPXPXQBUMZUKZUUEUTZHY
        FVAZCEUSUUHQLUUJPUKZUUMUUGCEUUNUULUUFHYFUUNUUKXRXPUUEUUJPXQWKWLWMWPUGUU
        GCEWQXDWRWSWRXJXKUUGCEWTYGUUIWOACEFGHIJKMNOPQRSTUAUBUCUDUEUFXAUUGYGCEDU
        UDDUKZUUFYEHYFUUOUUEYDXPXRUUDDYCWKXBWMXCXEXFXGXH $.

      $( Lemma for ~ cvmlift2 .  (Contributed by Mario Carneiro,
         6-Jul-2015.) $)
      cvmlift3lem5 $p |- ( ph -> ( F o. H ) = G ) $=
        ( vy vw cv cfv cmpt ccom wcel wa cc0 wceq c1 cii ccn crio w3a wrex eqid
        co cvmlift3lem4 df-3an ccvm ad3antrrr simplr cnco syl2anc simprl fveq2d
        mpbii cicc wf iiuni cnf syl 0elunit sylancl 3eqtr4rd cvmliftiota simp2d
        fveq1d simp1d 1elunit simprr 3eqtr3d fveqeq2 syl5ibcom expimpd biimtrid
        fvco3 rexlimdva mpd mpteq2dva cvmlift3lem3 ffvelcdmda feqmptd cuni 3syl
        eqtrd cvmcn fveq2 fmptco 3eqtr4d ) AUFOUFUHZKUIZIUIZUJUFOXGJUIZUJIKUKJA
        UFOXIXJAXGOULZUMZUNGUHZUIZNUOZUPXMUIZXGUOZUPIHUHZUKJXMUKZUOUNXRUIFUOUMH
        UQEURVCZUSZUIZXHUOZUTZGUQMURVCZVAZXIXJUOZXLXHXHUOYFXHVBABCXHDEFGHIJKLMN
        XGOPQRSTUAUBUCUDUEVDVMXLYDYGGYEYDXOXQUMZYCUMXLXMYEULZUMZYGXOXQYCVEYJYHY
        CYGYJYHUMZYBIUIZXJUOYCYGYKUPIYAUKZUIZUPXSUIZYLXJYKUPYMXSYKYAXTULZYMXSUO
        ZUNYAUIFUOZYKDEFHIXSYALPYAVBAIELVFVCULZXKYIYHRVGYKYIJMLURVCULZXSUQLURVC
        ULXLYIYHVHZAYTXKYIYHUBVGXMJUQMLVIVJAFDULXKYIYHUCVGYKXNJUIZNJUIZUNXSUIZF
        IUIZYKXNNJYJXOXQVKVLYKUNUPVNVCZOXMVOZUNUUFULUUDUUBUOYKYIUUGUUAXMUQMUUFO
        VPQVQVRZVSUUFOUNJXMWMVTAUUEUUCUOXKYIYHUDVGWAWBZWCWDYKUUFDYAVOZUPUUFULZY
        NYLUOYKYPUUJYKYPYQYRUUIWEYAUQEUUFDVPPVQVRWFUUFDUPIYAWMVTYKYOXPJUIZXJYKU
        UGUUKYOUULUOUUHWFUUFOUPJXMWMVTYKXPXGJYJXOXQWGVLXBWHYBXHXJIWIWJWKWLWNWOW
        PAUFUGODXHUGUHZIUIXIKIAODXGKABCDEFGHIJKLMNOPQRSTUAUBUCUDUEWQZWRAUFODKUU
        NWSAUGDLWTZIAYSIELURVCULDUUOIVOREILXCIELDUUOPUUOVBZVQXAWSUUMXHIXDXEAUFO
        UUOJAYTOUUOJVOUBJMLOUUOQUUPVQVRWSXF $.

      cvmlift3lem7.s $e |- S = ( k e. J |->
        { s e. ( ~P C \ { (/) } ) | ( U. s = ( `' F " k ) /\
          A. c e. s ( A. d e. ( s \ { c } ) ( c i^i d ) = (/) /\
             ( F |` c ) e. ( ( C |`t c ) Homeo ( J |`t k ) ) ) ) } ) $.
      ${
        cvmlift3lem7.1 $e |- ( ph -> ( G ` X ) e. A ) $.
        cvmlift3lem7.2 $e |- ( ph -> T e. ( S ` A ) ) $.
        cvmlift3lem7.3 $e |- ( ph -> M C_ ( `' G " A ) ) $.
        cvmlift3lem7.w $e |- W = ( iota_ b e. T ( H ` X ) e. b ) $.
        ${
          cvmlift3lem6.x $e |- ( ph -> X e. M ) $.
          cvmlift3lem6.z $e |- ( ph -> Z e. M ) $.
          cvmlift3lem6.q $e |- ( ph -> Q e. ( II Cn K ) ) $.
          cvmlift3lem6.r $e |- R = ( iota_ g e. ( II Cn C )
            ( ( F o. g ) = ( G o. Q ) /\ ( g ` 0 ) = P ) ) $.
          cvmlift3lem6.1 $e |- ( ph ->
            ( ( Q ` 0 ) = O /\ ( Q ` 1 ) = X /\ ( R ` 1 ) = ( H ` X ) ) ) $.
          cvmlift3lem6.n $e |- ( ph -> N e. ( II Cn ( K |`t M ) ) ) $.
          cvmlift3lem6.2 $e |- ( ph ->
            ( ( N ` 0 ) = X /\ ( N ` 1 ) = Z ) ) $.
          cvmlift3lem6.i $e |- I = ( iota_ g e. ( II Cn C )
            ( ( F o. g ) = ( G o. N ) /\ ( g ` 0 ) = ( H ` X ) ) ) $.
          $( Lemma for ~ cvmlift3 .  (Contributed by Mario Carneiro,
             9-Jul-2015.) $)
          cvmlift3lem6 $p |- ( ph -> ( H ` Z ) e. W ) $=
            ( cfv c1 wceq cc0 cv ccom wa cii ccn co crio w3a cpco wcel ctop wss
            crest syl sseldd simp2d simpld eqtr4d pcocn pco0 simp1d pco1 simprd
            eqtrd syl2anc fveq2d wf iiuni cnf 0elunit fvco3 sylancl cvmliftiota
            cnco 3eqtr4rd ccnv cima cnvimass fssdm sstrd fveq1d simp3d copco wb
            cuni coeq2 eqeq1d fveq1 syl13anc mpbird ctopon toptopon sylib rnco2
            a1i crn syl3anc frnd wfun cdm ffund eqeltrd wrex sconntop cicc eqid
            csconn cnrest2r cvmlift3lem3 cvmlift3lem5 eqtr3d oveq12d ccvm cvmcn
            3eqtr4d wreu cvmlift syl22anc anbi12d riota2 mpbi2and eqeq2d anbi1d
            ffvelcdmd riotabidv 3anbi123d rspcev cvmlift3lem4 mpdan cconn rneqd
            iiconn cvmtop1 3eqtr3g iitopon resttopon cnf2 sstrdi funimass3 fdmd
            eqsstrd sseqtrrd mpbid cnrest2 cvmsss elssuni cvmsuni sseqtrd cnima
            cvmsiota cvmsrcl restopn2 mpbir2and cvmscld conncn 1elunit ffvelcdm
            ccld ) AUGQVOZVPRVOZUDAUWQUWRVQZVRLVSZVOZUCVQZVPUWTVOZUGVQZVPOMVSZV
            TZPUWTVTZVQZVRUXEVOZGVQZWAZMWBFWCWDZWEZVOZUWRVQZWFZLWBTWCWDZUUAZAHU
            BTWGVOWDZUXQWHZVRUXSVOZUCVQZVPUXSVOZUGVQZVPUXFPUXSVTZVQZUXJWAZMUXLW
            EZVOZUWRVQZUXRAHUBTVIAWBTUAWKWDZWCWDZUXQUBATWIWHZUYLUXQWJATUUEWHUYM
            UOTUUBWLZUAWBTUUFWLVLWMZAVPHVOZUEVRUBVOZAVRHVOZUCVQZUYPUEVQZVPIVOZU
            EQVOZVQZVKWNAUYQUEVQZVPUBVOZUGVQZVMWOZWPZWQZAUYAUYRUCAHUBTVIUYOWRAU
            YSUYTVUCVKWSZXBZAUYCVUEUGAHUBTVIUYOWTAVUDVUFVMXAXBAUYIVPIRFWGVOWDZV
            OUWRAVPUYHVULAOVULVTZUYEVQZVRVULVOZGVQZUYHVULVQZAOIVTZORVTZSWGVOZWD
            PHVTZPUBVTZVUTWDVUMUYEAVURVVAVUSVVBVUTAIUXLWHZVURVVAVQZVRIVOZGVQZAE
            FGMOVVAISULVJUNAHUXQWHZPTSWCWDWHZVVAWBSWCWDZWHVIURHPWBTSXLXCUSAUYRP
            VOZUCPVOZVRVVAVOZGOVOZAUYRUCPVUJXDAVRVPUUCWDZUFHXEZVRVVNWHZVVLVVJVQ
            AVVGVVOVIHWBTVVNUFXFUMXGWLXHVVNUFVRPHXIXJUTXMXKZWNARUXLWHZVUSVVBVQZ
            VRRVOZVUBVQZAEFVUBMOVVBRSULVNUNAUBUXQWHZVVHVVBVVIWHUYOURUBPWBTSXLXC
            AUFEUEQABCEFGLMOPQSTUCUFULUMUNUOUPUQURUSUTVAUUGZAUAUFUEAUAPXNDXOZUF
            VEAUFSYCZVWDPPDXPZAVVHUFVWEPXEURPTSUFVWEUMVWEUUDZXGWLZXQXRZVGWMZUVB
            ZAUYQPVOZUEPVOZVRVVBVOZVUBOVOZAUYQUEPVUGXDAVVNUFUBXEZVVPVWNVWLVQAVW
            BVWPUYOUBWBTVVNUFXFUMXGWLXHVVNUFVRPUBXIXJAUEOQVTZVOZVWOVWMAUFEQXEUE
            UFWHVWRVWOVQVWCVWJUFEUEOQXIXCAUEVWQPABCEFGLMOPQSTUCUFULUMUNUOUPUQUR
            USUTVAUUHXSUUIZXMXKZWNZUUJAIROFSAVVCVVDVVFVVQWSZAVVRVVSVWAVWTWSZAVU
            AVUBVVTAUYSUYTVUCVKXTAVVRVVSVWAVWTXTZWPZAOFSUUKWDWHZOFSWCWDWHZUNFOS
            UULWLZYAAHUBPTSVIUYOVUHURYAUUMAVUOVVEGAIRFVXBVXCWRAVVCVVDVVFVVQXTXB
            AVULUXLWHUYGMUXLUUNZVUNVUPWAZVUQYBAIRFVXBVXCVXEWQAVXFUYEVVIWHZGEWHV
            VMVRUYEVOZVQVXIUNAUXTVVHVXKVUIURUXSPWBTSXLXCUSAUYAPVOZVVKVXLVVMAUYA
            UCPVUKXDAVVNUFUXSXEZVVPVXLVXMVQAUXTVXNVUIUXSWBTVVNUFXFUMXGWLXHVVNUF
            VRPUXSXIXJUTXMEFGMOUYESULUUOUUPUYGVXJMUXLVULUXEVULVQZUYFVUNUXJVUPVX
            OUXFVUMUYEUXEVULOYDYEVXOUXIVUOGVRUXEVULYFYEUUQUURXCUUSXSAIRFVXBVXCW
            TXBUXPUYBUYDUYJWFLUXSUXQUWTUXSVQZUXBUYBUXDUYDUXOUYJVXPUXAUYAUCVRUWT
            UXSYFYEVXPUXCUYCUGVPUWTUXSYFYEVXPUXNUYIUWRVXPVPUXMUYHVXPUXKUYGMUXLV
            XPUXHUYFUXJVXPUXGUYEUXFUWTUXSPYDUUTUVAUVCXSYEUVDUVEYGAUGUFWHUWSUXRY
            BAUAUFUGVWIVHWMABCUWREFGLMOPQSTUCUGUFULUMUNUOUPUQURUSUTVAUVFUVGYHAV
            VNUDRXEVPVVNWHUWRUDWHAVRUDRWBFOXNDXOZWKWDZVVNXFWBUVHWHAUVJYMAVVRRWB
            VXRWCWDWHZVXCAFEYIVOWHZRYNZVXQWJZVXQEWJVVRVXSYBAFWIWHZVXTAVXFVYCUNF
            OSUVKWLZFEULYJYKAOVYAXOZDWJZVYBAVYEPUBYNZXOZDAVUSYNVVBYNVYEVYHAVUSV
            VBVXAUVIORYLPUBYLUVLAVYHDWJZVYGVWDWJZAVYGUAVWDAVVNUAUBAWBVVNYIVOWHZ
            UYKUAYIVOWHZUBUYLWHVVNUAUBXEVYKAUVMYMATUFYIVOWHZUAUFWJVYLAUYMVYMUYN
            TUFUMYJYKVWIUATUFUVNXCVLUBWBUYKVVNUAUVOYOYPVEXRZAPYQVYGPYRZWJVYIVYJ
            YBAUFVWEPVWHYSAVYGVWDVYOVYNVWFUVPVYGDPUVQXCYHUVSAOYQVYAOYRZWJVYFVYB
            YBAEVWEOAVXGEVWEOXEVXHOFSEVWEULVWGXGWLZYSAVYAEVYPAVVNERAVVRVVNERXEV
            XCRWBFVVNEXFULXGWLYPAEVWEOVYQUVRUVTVYADOUVQXCUWAAEVWEVXQOODXPVYQXQV
            XQRWBFEUWBYOUWAAUDVXRWHZUDFWHZUDVXQWJZAKFUDAKDJVOWHZKFWJVDUKUJFJKDN
            OSUHVBUWCWLAUDKWHZVUBUDWHZAVXFWUAVUBEWHVWODWHWUBWUCWAUNVDVWKAVWOVWM
            DVWSVCYTUIUKUJVUBEFJKDNOSUDUHVBULVFUWHYGZWOZWMAUDKYCZVXQAWUBUDWUFWJ
            WUEUDKUWDWLAWUAWUFVXQVQVDUKUJFJKDNOSUHVBUWEWLUWFAVYCVXQFWHZVYRVYSVY
            TWAYBVYDAVXGDSWHZWUGVXHAWUAWUHVDUKUJFJKDNOSUHVBUWIWLDOFSUWGXCVXQUDF
            UWJXCUWKAVXFWUAWUBUDVXRUWPVOWHUNVDWUEUKUJUDFJKDNOSUHVBUWLYOVVPAXHYM
            AVVTVUBUDVXDAWUBWUCWUDXAYTUWMUWNVVNUDVPRUWOXJYT $.
        $}

        cvmlift3lem7.7 $e |- ( ph -> ( K |`t M ) e. PConn ) $.
        cvmlift3lem7.4 $e |- ( ph -> V e. K ) $.
        cvmlift3lem7.5 $e |- ( ph -> V C_ M ) $.
        cvmlift3lem7.6 $e |- ( ph -> X e. V ) $.
        $( Lemma for ~ cvmlift3 .  (Contributed by Mario Carneiro,
           9-Jul-2015.) $)
        cvmlift3lem7 $p |- ( ph -> H e. ( ( K CnP C ) ` X ) ) $=
          ( vy vh va vn ccnp cfv wcel cres crest cuni cvmlift3lem3 cvmlift3lem5
          ccn ccom eqeltrd csconn ctop sconntop syl ccnv cima cdm cnvimass wceq
          co wf eqid cnf fdm 3syl sseqtrid sstrd sseldd ccvm wa ffvelcdmd fvco3
          syl2anc fveq1d eqtr3d cvmsiota syl13anc wss cv wral cc0 cii crio wrex
          c1 w3a cvmlift3lem4 mpbii mpdan adantr weq fveq1 eqeq1d eqeq2d anbi1d
          coeq2 riotabidv anbi12d cbvriotavw eqtr4di 3anbi123d cbvrexvw restuni
          sylib cpconn ad3antrrr wb mpbird syl22anc eleqtrd eleq2d biimpa cnlly
          pconncn syl3anc reeanv simpllr simplrl simprl simplrr cvmlift3lem6 ex
          simprr rexlimdvva biimtrrid mp2and ralrimiva wfun ffund fdmd sseqtrrd
          funimass4 cvmlift2lem9a cncnpi cnt ssntr cnprest ) AOUBQFVKWKVLVMZORV
          NZUBQRVOWKZFVKWKVLVMZAUVJUVKFVSWKVMUBUVKVPZVMZUVLADEFHILMOPQRUAUBUCUD
          UFUGUHUIURUJABCEFGJKMNOPQSUCUHUIUJUKULUMUNUOUPUQVQZAMOVTZNQPVSWKZABCE
          FGJKMNOPQSUCUHUIUJUKULUMUNUOUPUQVRZUNWAAQWBVMZQWCVMZUKQWDWEZARUCUBARN
          WFDWGZUCVAANWHZUWBUCNDWIANUVQVMZUCPVPZNWLUWCUCWJUNNQPUCUWEUIUWEWMWNUC
          UWENWOWPWQWRZATRUBVEVFWSZWSZUTAMFPWTWKVMZIDHVLVMZUBOVLZEVMUWKMVLZDVMU
          AIVMUWKUAVMXAUJUTAUCEUBOUVOUWHXBAUWLUBNVLZDAUBUVPVLZUWLUWMAUCEOWLZUBU
          CVMZUWNUWLWJUVOUWHUCEUBMOXCXDAUBUVPNUVRXEXFUSWAUEUGUFUWKEFHIDLMPUAUDU
          RUHVBXGXHUWFAORWGUAXIZVGXJZOVLUAVMZVGRXKZAUWSVGRAUWRRVMZXAZXLVHXJZVLZ
          SWJZXPUXCVLZUBWJZXPMVIXJZVTZNUXCVTZWJZXLUXHVLZGWJZXAZVIXMFVSWKZXNZVLZ
          UWKWJZXQZVHXMQVSWKZXOZXLVJXJZVLUBWJXPUYBVLUWRWJXAZVJXMUVKVSWKZXOZUWSU
          XBXLJXJZVLZSWJZXPUYFVLZUBWJZXPMKXJZVTZNUYFVTZWJZXLUYKVLZGWJZXAZKUXOXN
          ZVLZUWKWJZXQZJUXTXOZUYAAVUBUXAAUWPVUBUWHAUWPXAUWKUWKWJVUBUWKWMABCUWKE
          FGJKMNOPQSUBUCUHUIUJUKULUMUNUOUPUQXRXSXTYAVUAUXSJVHUXTJVHYBZUYHUXEUYJ
          UXGUYTUXRVUCUYGUXDSXLUYFUXCYCYDVUCUYIUXFUBXPUYFUXCYCYDVUCUYSUXQUWKVUC
          XPUYRUXPVUCUYRUYLUXJWJZUYPXAZKUXOXNUXPVUCUYQVUEKUXOVUCUYNVUDUYPVUCUYM
          UXJUYLUYFUXCNYGYEYFYHUXNVUEVIKUXOVIKYBZUXKVUDUXMUYPVUFUXIUYLUXJUXHUYK
          MYGZYDVUFUXLUYOGXLUXHUYKYCZYDYIYJZYKXEYDYLYMYOUXBUVKYPVMZUVNUWRUVMVMZ
          UYEAVUJUXAVCYAAUVNUXAAUBRUVMUWGAUVTRUCXIZRUVMWJUWAUWFRQUCUIYNXDZUUAZY
          AAUXAVUKARUVMUWRVUMUUBUUCUBUWRVJUVKUVMUVMWMZUUEUUFUYAUYEXAUXSUYCXAZVJ
          UYDXOVHUXTXOUXBUWSUXSUYCVHVJUXTUYDUUGUXBVUPUWSVHVJUXTUYDUXBUXCUXTVMZU
          YBUYDVMZXAZXAZVUPUWSVUTVUPXABCDEFGUXCUXPHIJKLMNOUXINUYBVTZWJZUXLUWKWJ
          ZXAZVIUXOXNPQRUYBSUAUBUCUWRUDUEUFUGUHUIAUWIUXAVUSVUPUJYQAUVSUXAVUSVUP
          UKYQAQYPUUDVMUXAVUSVUPULYQASUCVMUXAVUSVUPUMYQAUWDUXAVUSVUPUNYQAGEVMUX
          AVUSVUPUOYQAGMVLSNVLWJUXAVUSVUPUPYQUQURAUWMDVMUXAVUSVUPUSYQAUWJUXAVUS
          VUPUTYQARUWBXIUXAVUSVUPVAYQVBAUBRVMUXAVUSVUPUWGYQAUXAVUSVUPUUHUXBVUQV
          URVUPUUIVUIVUTUXSUYCUUJUXBVUQVURVUPUUKVUTUXSUYCUUNVVDUYLVVAWJZUYOUWKW
          JZXAVIKUXOVUFVVBVVEVVCVVFVUFUXIUYLVVAVUGYDVUFUXLUYOUWKVUHYDYIYJUULUUM
          UUOUUPUUQUURAOUUSROWHZXIUWQUWTYRAUCEOUVOUUTARUCVVGUWFAUCEOUVOUVAUVBVG
          RUAOUVCXDYSUVDVUNUBUVJUVKFUVMVUOUVEXDAUVTVULUBRQUVFVLVLZVMUWOUVIUVLYR
          UWAUWFATVVHUBAUVTVULTQVMTRXITVVHXIUWAUWFVDVERQTUCUIUVGYTVFWSUVORUBOQF
          UCEUIUHUVHYTYS $.
      $}

      $( Lemma for ~ cvmlift2 .  (Contributed by Mario Carneiro,
         6-Jul-2015.) $)
      cvmlift3lem8 $p |- ( ph -> H e. ( K Cn C ) ) $=
        ( vy va vt vv vm vb ccn co wcel wf cv ccnp cfv wral cvmlift3lem3 wa wne
        c0 wrex ccvm cuni adantr eqid cnf syl ffvelcdmda cvmcov syl2anc wex wss
        n0 crest cpconn w3a ccnv cpw cnlly ad2antrr simprr cvmsrcl cnima simplr
        cima simprl wfn wb ffn elpreima 4syl mpbir2and nlly2i syl3anc ad3antrrr
        crio csconn simprll elpwid simprr3 simprlr simprr2 simprr1 cvmlift3lem7
        wceq rexlimdvva mpd exlimdv biimtrid expimpd rexlimdvw ralrimiva ctopon
        expr ctop sconntop toptopon sylib cvmtop1 cncnp ) AMOEURUSUTZQDMVAZMULV
        BZOEVCUSVDUTZULQVEZABCDEFHIKLMNOPQUAUBUCUDUEUFUGUHUIUJVFAYMULQAYLQUTZVG
        ZYLLVDZUMVBZUTZYRGVDZVIVHZVGZUMNVJZYMYPKENVKUSUTZYQNVLZUTUUCAUUDYOUCVMA
        QUUEYLLALONURUSUTZQUUELVAZUGLONQUUEUBUUEVNZVOZVPVQUMTSEYQGJKNUUERUKUUHV
        RVSYPUUBYMUMNYPYSUUAYMUUAUNVBZYTUTZUNVTYPYSVGZYMUNYTWBUULUUKYMUNYPYSUUK
        YMYPYSUUKVGZVGZYLUOVBZUTZUUOUPVBZWAZOUUQWCUSWDUTZWEZUOOVJUPLWFYRWNZWGZV
        JZYMUUNOWDWHUTZUVAOUTZYLUVAUTZUVCAUVDYOUUMUEWIUUNUUFYRNUTZUVEAUUFYOUUMU
        GWIZUUNUUKUVGYPYSUUKWJZTSEGUUJYRJKNRUKWKVPYRLONWLVSUUNUVFYOYSAYOUUMWMYP
        YSUUKWOZUUNUUFUUGLQWPUVFYOYSVGWQUVHUUIQUUELWRQYLYRLWSWTXAUOWDYLUVAOUPXB
        XCUUNUUTYMUPUOUVBOUUNUUQUVBUTZUUOOUTZVGZUUTYMUUNUVMUUTVGZVGZBCYRDEFGUUJ
        HIJKLMNOUUQPUUOYLMVDUQVBUTUQUUJXEZYLQRUQSTUAUBAUUDYOUUMUVNUCXDAOXFUTZYO
        UUMUVNUDXDAUVDYOUUMUVNUEXDAPQUTYOUUMUVNUFXDAUUFYOUUMUVNUGXDAFDUTYOUUMUV
        NUHXDAFKVDPLVDXNYOUUMUVNUIXDUJUKUUNYSUVNUVJVMUUNUUKUVNUVIVMUVOUUQUVAUUN
        UVKUVLUUTXGXHUVPVNUUPUURUUSUVMUUNXIUUNUVKUVLUUTXJUUPUURUUSUVMUUNXKUUPUU
        RUUSUVMUUNXLXMYCXOXPYCXQXRXSXTXPYAAOQYBVDUTZEDYBVDUTZYJYKYNVGWQAOYDUTZU
        VRAUVQUVTUDOYEVPOQUBYFYGAEYDUTZUVSAUUDUWAUCEKNYHVPEDUAYFYGULMOEQDYIVSXA
        $.

      $( Lemma for ~ cvmlift2 .  (Contributed by Mario Carneiro,
         7-May-2015.) $)
      cvmlift3lem9 $p |- ( ph ->
                    E. f e. ( K Cn C ) ( ( F o. f ) = G /\ ( f ` O ) = P ) ) $=
        ( ccn co wcel ccom wceq cfv cv wa wrex cvmlift3lem8 cvmlift3lem5 cc0 c1
        cii crio w3a cicc csn cxp ctopon iitopon a1i ctop sconntop syl toptopon
        csconn sylib syl3anc 0elunit fvconst2g sylancl 1elunit sneqd xpeq2d wfn
        cnconst2 ccvm cuni wf cvmcn eqid cnf 4syl fcoconst syl2anc ffnd 3eqtr4d
        ffn wreu wb cvmtop1 cvmtop2 ffvelcdmd eqeltrd 3eqtr4rd cvmlift syl22anc
        fveq1d coeq2 eqeq1d fveq1 riota2 mpbi2and eqtrd eqeq2d anbi1d riotabidv
        anbi12d 3anbi123d rspcev syl13anc cvmlift3lem4 mpdan mpbird syl12anc )
        AMOEULUMZUNKMUOZLUPZPMUQZFUPZKHURZUOZLUPZPYMUQZFUPZUSZHYHUTABCDEFGHIJKL
        MNOPQRSTUAUBUCUDUEUFUGUHUIUJUKVAABCDEFHIKLMNOPQUAUBUCUDUEUFUGUHUIUJVBAY
        LVCYMUQZPUPZVDYMUQZPUPZVDKIURZUOZLYMUOZUPZVCUUCUQZFUPZUSZIVEEULUMZVFZUQ
        ZFUPZVGZHVEOULUMZUTZAVCVDVHUMZPVIVJZUUOUNZVCUURUQZPUPZVDUURUQZPUPZVDUUD
        LUURUOZUPZUUHUSZIUUJVFZUQZFUPZUUPAVEUUQVKUQUNZOQVKUQUNZPQUNZUUSUVJAVLVM
        ZAOVNUNZUVKAOVRUNUVNUDOVOVPOQUBVQVSUFPVEOUUQQWHVTAUVLVCUUQUNZUVAUFWAUUQ
        PVCQWBWCAUVLVDUUQUNZUVCUFWDUUQPVDQWBWCAUVHVDUUQFVIVJZUQZFAVDUVGUVQAKUVQ
        UOZUVDUPZVCUVQUQZFUPZUVGUVQUPZAUUQFKUQZVIZVJZUUQPLUQZVIZVJZUVSUVDAUWEUW
        HUUQAUWDUWGUIWEWFAKDWGZFDUNZUVSUWFUPAKENWIUMUNZKENULUMUNDNWJZKWKUWJUCEK
        NWLKENDUWMUAUWMWMZWNDUWMKWTWOUHKUUQDFWPWQALQWGUVLUVDUWIUPAQUWMLALONULUM
        UNQUWMLWKUGLONQUWMUBUWNWNVPZWRUFLUUQQPWPWQZWSAUWKUVOUWBUHWAUUQFVCDWBWCA
        UVQUUJUNZUVFIUUJXAZUVTUWBUSZUWCXBAUVJEDVKUQUNZUWKUWQUVMAEVNUNZUWTAUWLUX
        AUCEKNXCVPEDUAVQVSUHFVEEUUQDWHVTAUWLUVDVENULUMZUNUWKUWDVCUVDUQZUPUWRUCA
        UVDUWIUXBUWPAUVJNUWMVKUQUNZUWGUWMUNZUWIUXBUNUVMANVNUNZUXDAUWLUXFUCEKNXD
        VPNUWMUWNVQVSAQUWMPLUWOUFXEZUWGVENUUQUWMWHVTXFUHAVCUWIUQZUWGUXCUWDAUXEU
        VOUXHUWGUPUXGWAUUQUWGVCUWMWBWCAVCUVDUWIUWPXJUIXGDEFIKUVDNUAXHXIUVFUWSIU
        UJUVQUUCUVQUPZUVEUVTUUHUWBUXIUUDUVSUVDUUCUVQKXKXLUXIUUGUWAFVCUUCUVQXMXL
        XTXNWQXOXJAUWKUVPUVRFUPUHWDUUQFVDDWBWCXPUUNUVAUVCUVIVGHUURUUOYMUURUPZYT
        UVAUUBUVCUUMUVIUXJYSUUTPVCYMUURXMXLUXJUUAUVBPVDYMUURXMXLUXJUULUVHFUXJVD
        UUKUVGUXJUUIUVFIUUJUXJUUFUVEUUHUXJUUEUVDUUDYMUURLXKXQXRXSXJXLYAYBYCAUVL
        YLUUPXBUFABCFDEFHIKLMNOPPQUAUBUCUDUEUFUGUHUIUJYDYEYFYRYJYLUSHMYHYMMUPZY
        OYJYQYLUXKYNYILYMMKXKXLUXKYPYKFPYMMXMXLXTYBYG $.
    $}

    $( A general version of ~ cvmlift .  If ` K ` is simply connected and
       weakly locally path-connected, then there is a unique lift of functions
       on ` K ` which commutes with the covering map.  (Contributed by Mario
       Carneiro, 9-Jul-2015.) $)
    cvmlift3 $p |- ( ph ->
        E! f e. ( K Cn C ) ( ( F o. f ) = G /\ ( f ` O ) = P ) ) $=
      ( vx vz vk vs vc vd vg va vb vv vu cv ccom wceq cfv wa ccn wrex wrmo wreu
      co cuni ccnv cima cin c0 csn cdif wral cres crest chmeo wcel cpw crab cc0
      cmpt cii crio w3a weq eqeq2 3anbi3d rexbidv cbvriotavw fveq1 eqeq1d coeq2
      c1 anbi12d eqeq2d anbi1d riotabidv eqtrid fveq1d 3anbi123d 3anbi2d bitrid
      cbvrexvw cbvmptv eqid cvmscbv cvmlift3lem9 csconn cpconn cconn sconnpconn
      pconnconn 3syl cnlly ssriv nllyss ax-mp sselid cvmliftmo reu5 sylanbrc
      wss ) AFEULZUMGUNJXSUODUNUPZEICUQVAZURXTEYAUSXTEYAUTAUAUBBCDUCHUDULZVBFVC
      UCULZVDUNUEULZUFULZVEVFUNUFYBYDVGVHVIFYDVJCYDVKVAHYCVKVAVLVAVMUPUEYBVIUPU
      DCVNVFVGVHVOVQZEUGUHFGUHKVPYDUOZJUNZWIYDUOZUHULZUNZWIFYEUMZGYDUMZUNZVPYEU
      OZDUNZUPZUFVRCUQVAZVSZUOZUIULZUNZVTZUEVRIUQVAZURZUIBVSZVQHIJKUIUJUKLMNOPQ
      RSTUHUAKUUFVPXSUOZJUNZWIXSUOZUAULZUNZWIFUGULZUMZGXSUMZUNZVPUULUOZDUNZUPZU
      GYRVSZUOZUBULZUNZVTZEUUDURZUBBVSZUHUAWAZUUFYHYKYTUVAUNZVTZUEUUDURZUBBVSUV
      EUUEUVIUIUBBUIUBWAZUUCUVHUEUUDUVJUUBUVGYHYKUUAUVAYTWBWCWDWEUVFUVIUVDUBBUV
      IUUHUUIYJUNZUVBVTZEUUDURUVFUVDUVHUVLUEEUUDUEEWAZYHUUHYKUVKUVGUVBUVMYGUUGJ
      VPYDXSWFWGUVMYIUUIYJWIYDXSWFWGUVMYTUUTUVAUVMWIYSUUSUVMYSUUMYMUNZUUQUPZUGY
      RVSUUSYQUVOUFUGYRUFUGWAZYNUVNYPUUQUVPYLUUMYMYEUULFWHWGUVPYOUUPDVPYEUULWFW
      GWJWEUVMUVOUURUGYRUVMUVNUUOUUQUVMYMUUNUUMYDXSGWHWKWLWMWNWOWGWPWSUVFUVLUVC
      EUUDUVFUVKUUKUUHUVBYJUUJUUIWBWQWDWRWMWNWTUFUECYFUCFHUDUHUIUJUKYFXAXBXCABC
      DEFGHIJKLMNAIXDVMIXEVMIXFVMOIXGIXHXIAXEXJZXFXJZIXEXFXRUVQUVRXRUAXEXFUUJXH
      XKXEXFXLXMPXNQRSTXOXTEYAXPXQ $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Normal numbers
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d n A $.  $d n B $.  $d k n N $.  $d n R $.
    snmlff.f $e |- F = ( n e. NN |-> ( ( # ` { k e. ( 1 ... n ) |
      ( |_ ` ( ( A x. ( R ^ k ) ) mod R ) ) = B } ) / n ) ) $.
    $( The function ` F ` from ~ snmlval is a mapping from positive integers to
       real numbers in the range ` [ 0 , 1 ] ` .  (Contributed by Mario
       Carneiro, 6-Apr-2015.) $)
    snmlff $p |- F : NN --> ( 0 [,] 1 ) $=
      ( cn cc0 c1 co cv cmul cfv wceq wcel cr cle wbr cfn cicc cexp cmo cfl cfz
      crab chash cdiv cn0 wss ssrab2 ssfi sylancl hashcl nn0red nndivre mpancom
      fzfid syl clt nn0ge0d nnre nngt0 divge0 syl22anc ssdomg mpisyl wb hashdom
      cdom syl2anc mpbird nnnn0 hashfz1 breqtrd nncn mulridd breqtrrd syl112anc
      1red ledivmul elicc01 syl3anbrc fmpti ) EHIJUAKZACDLUBKMKCUCKUDNBOZDJELZU
      EKZUFZUGNZWGUHKZFGWGHPZWKQPZIWKRSZWKJRSZWKWEPWJQPZWLWMWLWJWLWITPZWJUIPWLW
      HTPZWIWHUJZWQWLJWGURZWFDWHUKZWHWIULUMZWIUNUSZUOZWJWGUPUQWLWPIWJRSWGQPZIWG
      UTSZWNXDWLWJXCVAWGVBZWGVCZWJWGVDVEWLWOWJWGJMKZRSZWLWJWGXIRWLWJWHUGNZWGRWL
      WJXKRSZWIWHVJSZWLWRWSXMWTXAWIWHTVFVGWLWQWRXLXMVHXBWTWIWHTVIVKVLWLWGUIPXKW
      GOWGVMWGVNUSVOWLWGWGVPVQVRWLWPJQPXEXFWOXJVHXDWLVTXGXHWJJWGWAVSVLWKWBWCWD
      $.

    $( The function ` F ` from ~ snmlval maps ` N ` to the relative density of
       ` B ` in the first ` N ` digits of the digit string of ` A ` in base
       ` R ` .  (Contributed by Mario Carneiro, 6-Apr-2015.) $)
    snmlfval $p |- ( N e. NN -> ( F ` N ) = ( ( # ` { k e. ( 1 ... N ) |
      ( |_ ` ( ( A x. ( R ^ k ) ) mod R ) ) = B } ) / N ) ) $=
      ( cv cexp co cmul cmo cfv wceq c1 cfz crab chash cdiv cfl cn oveq2 fveq2d
      rabeqdv id oveq12d ovex fvmpt ) EGACDIJKLKCMKUANBOZDPEIZQKZRZSNZUKTKUJDPG
      QKZRZSNZGTKUBFUKGOZUNUQUKGTURUMUPSURUJDULUOUKGPQUCUEUDURUFUGHUQGTUHUI $.
  $}

  ${
    $d b k n x A $.  $d b k n B $.  $d b F $.  $d b k n r x R $.
    snml.s $e |- S = ( r e. ( ZZ>= ` 2 ) |->
      { x e. RR | A. b e. ( 0 ... ( r - 1 ) ) ( n e. NN |-> ( ( # `
      { k e. ( 1 ... n ) | ( |_ ` ( ( x x. ( r ^ k ) ) mod r ) ) = b } )
        / n ) ) ~~> ( 1 / r ) } ) $.
    $( The property " ` A ` is simply normal in base ` R ` ".  A number is
       simply normal if each digit ` 0 <_ b < R ` occurs in the base- ` R `
       digit string of ` A ` with frequency ` 1 / R ` (which is consistent with
       the expectation in an infinite random string of numbers selected from
       ` 0 ... R - 1 ` ).  (Contributed by Mario Carneiro, 6-Apr-2015.) $)
    snmlval $p |- ( A e. ( S ` R ) <-> ( R e. ( ZZ>= ` 2 ) /\ A e. RR /\
      A. b e. ( 0 ... ( R - 1 ) ) ( n e. NN |-> ( ( # `
      { k e. ( 1 ... n ) | ( |_ ` ( ( A x. ( R ^ k ) ) mod R ) ) = b } )
        / n ) ) ~~> ( 1 / R ) ) ) $=
      ( cfv cr cn cv co cmul cmo cfl wceq c1 cdiv c2 cuz wcel wa cexp cfz chash
      crab cmpt cli wbr cc0 cmin wral w3a oveq1 oveq2d oveq12d fveqeq2d rabbidv
      id fveq2d oveq1d mpteq2dv oveq2 breq12d raleqbidv reex rabex fvmpt eleq2d
      fvoveq1d eqeq1d breq1d ralbidv elrab bitrdi pm5.32i dmmptss elfvdm sselid
      cdm pm4.71ri 3anass 3bitr4i ) CUAUBJZUCZBCDJZUCZUDWGBKUCZFLBCEMZUENZONZCP
      NQJZHMZRZESFMZUFNZUHZUGJZWQTNZUIZSCTNZUJUKZHULCSUMNZUFNZUNZUDZUDWIWGWJXGU
      OWGWIXHWGWIBFLAMZWLONZCPNZQJZWORZEWRUHZUGJZWQTNZUIZXCUJUKZHXFUNZAKUHZUCXH
      WGWHXTBGCFLXIGMZWKUENZONZYAPNZQJWORZEWRUHZUGJZWQTNZUIZSYATNZUJUKZHULYASUM
      NZUFNZUNZAKUHZXTWFDYACRZYNXSAKYPYKXRHYMXFYPYLXEULUFYACSUMUPUQYPYIXQYJXCUJ
      YPFLYHXPYPYGXOWQTYPYFXNUGYPYEXMEWRYPYDXKWOQYPYCXJYACPYPYBWLXIOYACWKUEUPUQ
      YPVAURUSUTVBVCVDYACSTVEVFVGUTIXSAKVHVIVJVKXSXGABKXIBRZXRXDHXFYQXQXBXCUJYQ
      FLXPXAYQXOWTWQTYQXNWSUGYQXMWPEWRYQXLWNWOYQXJWMCQPXIBWLOUPVLVMUTVBVCVDVNVO
      VPVQVRWIWGWIDWBWFCGWFYODIVSBCDVTWAWCWGWJXGWDWE $.

    ${
      snml.f $e |- F = ( n e. NN |-> ( ( # `
        { k e. ( 1 ... n ) | ( |_ ` ( ( A x. ( R ^ k ) ) mod R ) ) = B } )
          / n ) ) $.
      $( If ` A ` is simply normal, then the function ` F ` of relative density
         of ` B ` in the digit string converges to ` 1 / R ` , i.e. the set of
         occurrences of ` B ` in the digit string has natural density
         ` 1 / R ` .  (Contributed by Mario Carneiro, 6-Apr-2015.) $)
      snmlflim $p |- ( ( A e. ( S ` R ) /\ B e. ( 0 ... ( R - 1 ) ) ) ->
        F ~~> ( 1 / R ) ) $=
        ( cfv wcel cn cv co wceq c1 cdiv cexp cmul cmo cfl cfz crab cli wbr cc0
        chash cmpt cmin wral c2 cuz snmlval simp3bi eqeq2 rabbidv fveq2d oveq1d
        cr mpteq2dv eqtr4di breq1d rspccva sylan ) BDEMNZGOBDFPUAQUBQDUCQUDMZJP
        ZRZFSGPZUEQZUFZUJMZVLTQZUKZSDTQZUGUHZJUIDSULQUEQZUMZCVTNHVRUGUHZVHDUNUO
        MNBVBNWAABDEFGIJKUPUQVSWBJCVTVJCRZVQHVRUGWCVQGOVICRZFVMUFZUJMZVLTQZUKHW
        CGOVPWGWCVOWFVLTWCVNWEUJWCVKWDFVMVJCVIURUSUTVAVCLVDVEVFVG $.
    $}

  $(
    @( Almost all numbers (in the sense of Lebesgue measure) are simply normal
       in base ` R ` . @)
    snmlnul @p |- ( R e. ( ZZ>= ` 2 ) -> ( vol* ` ( RR \ ( S ` R ) ) ) = 0 ) @=
      ? @.

    @( Almost all numbers (in the sense of Lebesgue measure) are normal
       in every base. @)
    nmlnul @p |- ( vol* ` ( RR \ { x e. RR | A. r e. ( ZZ>= ` 2 ) A. n e. NN0
      A. k e. NN ( x x. ( r ^ n ) ) e. ( S ` ( r ^ k ) ) } ) ) = 0 @=
      ( cfv cn0 cn co wcel cr crab covol wral cc0 wceq wbr syl c2 cuz cexp cmul
      cv wn ciun cdif wrex wa iunrab a1i iuneq2dv eqtrdi iuneq2i wtru wb rexnal
      rexbii bitri tru biantrur 3bitri rabbiia difrab rgenw rabid2 mpbir eqcomi
      difeq1i 3eqtr2i 3eqtri fveq2i cdom wss cvv fvex clt eluz2b2 simplbi ssriv
      c1 ssdomg mp2 ssrab2 iunss cen nn0ennn endom ax-mp nnex domrefg difss crp
      cdiv ad2antrr simplr nnexpcl syl2anc nnrp simpr adantr nnre remulcl eldif
      baibr cc recnd mulcom eleq1d bitrd rabbidva nnnn0 adantl exp0 nnz simprbi
      cz 0z nngt0 ltexp2a syl32anc eqbrtrrd sylanbrc snmlnul 0re ovolsca oveq1d
      eqeltrdi wne nncn nnne0 div0 3eqtrd jca ralrimiva ovoliunnul sylancr rgen
      mp2an eqtr3i ) EUAUBHZDICJAUEZEUEZDUEZUCKZUDKZUUDCUEZUCKZBHZLZUFZAMNZUGZU
      GZUGZOHZMUUKCJPZDIPZEUUBPZAMNZUHZOHQUUPUVBOUUPEUUBUULCJUIZDIUIZAMNZUGUVDE
      UUBUIZAMNZUVBEUUBUUOUVEUUDUUBLZUUODIUVCAMNZUGUVEUVHDIUUNUVIUUNUVIRUVHUUEI
      LZUJZUULCAJMUKULUMUVCDAIMUKUNUOUVDEAUUBMUKUVGUPUUTUFZUJZAMNUPAMNZUVAUHUVB
      UVFUVMAMUVFUVMUQUUCMLZUVFUUSUFZEUUBUIUVLUVMUVDUVPEUUBUVDUURUFZDIUIUVPUVCU
      VQDIUUKCJURUSUURDIURUTUSUUSEUUBURUPUVLVAVBVCULVDUPUUTAMVEUVNMUVAMUVNMUVNR
      UPAMPUPAMVAVFUPAMVGVHVIVJVKVLVMUUBJVNSZUUOMVOZUUOOHQRZUJZEUUBPUUQQRUUBVPL
      UUBJVOUVRUAUBVQEUUBJUVHUUDJLZWBUUDVRSZUUDVSZVTZWAUUBJVPWCWDUWAEUUBUVHUVSU
      VTUVSUVHUVSUUNMVOZDIPUWFDIUWFUUMMVOZCJPUWGCJUULAMWEZVFCJUUMMWFVHZVFDIUUNM
      WFVHULUVHIJVNSZUWFUUNOHQRZUJZDIPUVTIJWGSUWJWHIJWIWJUVHUWLDIUVKUWFUWKUWFUV
      KUWIULUVKJJVNSZUWGUUMOHZQRZUJZCJPUWKJVPLUWMWKJVPWLWJUVKUWPCJUVKUUHJLZUJZU
      WGUWOUWGUWRUWHULUWRUWNMUUJUHZOHZUUFWOKQUUFWOKZQUWRAUWSUUMUUFUWSMVOUWRMUUJ
      WMULUWRUUFJLZUUFWNLUWRUWBUVJUXBUVHUWBUVJUWQUWEWPZUVHUVJUWQWQUUDUUEWRWSZUU
      FWTTUWRUULUUFUUCUDKZUWSLZAMUWRUVOUJZUULUUGUWSLZUXFUXGUUGMLZUULUXHUQUXGUVO
      UUFMLZUXIUWRUVOXAZUXGUXBUXJUWRUXBUVOUXDXBUUFXCTZUUCUUFXDWSUXHUXIUULUUGMUU
      JXEXFTUXGUUGUXEUWSUXGUUCXGLUUFXGLZUUGUXERUXGUUCUXKXHUXGUUFUXLXHUUCUUFXIWS
      XJXKXLUWRUWTQMUWRUUIUUBLZUWTQRUWRUUIJLZWBUUIVRSUXNUWRUWBUUHILZUXOUXCUWQUX
      PUVKUUHXMXNUUDUUHWRWSUWRUUDQUCKZWBUUIVRUWRUUDXGLUXQWBRUWRUUDUWRUWBUUDMLZU
      XCUUDXCTZXHUUDXOTUWRUXRQXRLZUUHXRLZUWCQUUHVRSZUXQUUIVRSUXSUXTUWRXSULUWQUY
      AUVKUUHXPXNUVHUWCUVJUWQUVHUWBUWCUWDXQWPUWQUYBUVKUUHXTXNUUDQUUHYAYBYCUUIVS
      YDAUUIBCDEFGYETZYFYIYGUWRUWTQUUFWOUYCYHUWRUXMUUFQYJZUXAQRUWRUXBUXMUXDUUFY
      KTUWRUXBUYDUXDUUFYLTUUFYMWSYNYOYPJUUMCYQYRYOYPIUUNDYQYRYOYSUUBUUOEYQYTUUA
      @.
      @( [8-Apr-2015] @)

    @( Since almost all numbers are normal in every base, there must exist a
       normal number. @)
    nmlex @p |- E. x e. RR A. r e. ( ZZ>= ` 2 ) A. n e. NN0
      A. k e. NN ( x x. ( r ^ n ) ) e. ( S ` ( r ^ k ) ) @=
      ( cv cexp co cfv wcel wral cr c0 cdif covol cpnf mpbi eqtrdi cmul cn0 cuz
      cn c2 crab wne wrex cc0 nmlnul 0re eqeltri wceq wnel pnfnre df-nel difeq2
      wn dif0 fveq2d ovolre eleq1d mtbiri necon2ai ax-mp rabn0 ) AHEHZDHIJUAJVG
      CHIJBKLCUDMDUBMEUEUCKMZANUFZOUGZVHANUHNVIPZQKZNLZVJVLUINABCDEFGUJUKULVMVI
      OVIOUMZVMRNLZRNUNVOURUORNUPSVNVLRNVNVLNQKRVNVKNQVNVKNOPNVIONUQNUSTUTVATVB
      VCVDVEVHANVFS @.
      @( [6-Apr-2015] @)
  $)
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Compactification
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $(
  @{
    @d k n s S @.
    alextop.1 @e |- X = U. J @.
    alextop.2 @e |- O = ~P U. X @.
    alextop.3 @e |- K = ( J u. { x | E. y e. J ( x = ( y u. { O } ) /\
                        ( J |`t ( X \ y ) ) e. Comp ) } ) @.
    @( The domain of the Alexandroff extension. @)
    alexuni @p |- ( J e. Top -> ( X u. { O } ) = U. K ) @=
      ? @.

    @( The Alexandroff extension is a compactification of the original
       topology. @)
    alextop @p |- ( J e. Top -> K e. Comp ) @=
      ? @.
  @}
  $)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Godel-sets of formulas - part 1
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Introduce new constant symbols. $)
  $c e.g $. $( Godel-set of membership $)
  $c |g $. $( Godel-set for Sheffer stroke $)
  $c A.g $. $( Godel-set of universal quantification $)
  $c Fmla $. $( Formula predicate $)
  $c Sat $. $( Satisfaction predicate $)
  $c SatE $. $( Satisfaction predicate $)
  $c |= $. $( Proves relation $)

  $( The Godel-set of membership. $)
  cgoe $a class e.g $.

  $( The Godel-set for the Sheffer stroke. $)
  cgna $a class |g $.

  $( The Godel-set of universal quantification.  (Note that this is not a
     wff.) $)
  cgol $a class A.g N U $.

  $( The satisfaction function. $)
  csat $a class Sat $.

  $( The formula set predicate. $)
  cfmla $a class Fmla $.

  $( The ` e. ` -satisfaction function. $)
  csate $a class SatE $.

  $( The "proves" relation. $)
  cprv $a class |= $.

  $( Define the Godel-set of membership.  Here the arguments
     ` x = <. N , P >. ` correspond to v_N and v_P , so ` ( (/) e.g 1o ) `
     actually means v_0 ` e. ` v_1 , not ` 0 e. 1 ` .  (Contributed by Mario
     Carneiro, 14-Jul-2013.) $)
  df-goel $a |- e.g = ( x e. ( _om X. _om ) |-> <. (/) , x >. ) $.

  $( Define the Godel-set for the Sheffer stroke NAND. Here the arguments
     ` x = <. U , V >. ` are also Godel-sets corresponding to smaller formulas.
     (Contributed by Mario Carneiro, 14-Jul-2013.) $)
  df-gona $a |- |g = ( x e. ( _V X. _V ) |-> <. 1o , x >. ) $.

  $( Define the Godel-set of universal quantification.  Here ` N e. _om `
     corresponds to v_N , and ` U ` represents another formula, and this
     expression is ` [ A. x ph ] = A.g N U ` where ` x ` is the ` N ` -th
     variable, ` U = [ ph ] ` is the code for ` ph ` .  Note that this is a
     _class_ expression, not a wff.  (Contributed by Mario Carneiro,
     14-Jul-2013.) $)
  df-goal $a |- A.g N U = <. 2o , <. N , U >. >. $.

  ${
    $d a e f i j m u v x y z $.
    $( Define the satisfaction predicate. This recursive construction builds up
       a function over wff codes (see ~ satff ) and simultaneously defines the
       set of assignments to all variables from ` M ` that makes the coded wff
       true in the model ` M ` , where ` e. ` is interpreted as the binary
       relation ` E ` on ` M ` .

       The interpretation of the statement ` S e. ( ( ( M Sat E ) `` n ) `` U )
       ` is that for the model ` <. M , E >. ` , ` S : _om --> M ` is a
       valuation of the variables (v_0 ` = ( S `` (/) ) ` , v_1 ` = ( S `` 1o
       ) ` , etc.) and ` U ` is a code for a wff using ` e. , -/\ , A. ` that
       is true under the assignment ` S ` . The function is defined by finite
       recursion; ` ( ( M Sat E ) `` n ) ` only operates on wffs of depth at
       most ` n e. _om ` , and ` ( ( M Sat E ) `` _om ) = U_ n e. _om
       ( ( M Sat E ) `` n ) ` operates on all wffs.

       The coding scheme for the wffs is defined so that <HTML><ul>
       <li>v<sub>i</sub> ` e. ` v<sub>j</sub> is coded as
       ` <. (/) , <. i , j >. >. ` ,</li>
       <li> ` ( ph -/\ ps ) ` is coded as ` <. 1o , <. ph , ps >. >. ` ,
       and</li>
       <li> ` A. ` v<sub>i</sub> ` ph ` is coded as
       ` <. 2o , <. i , ph >. >. ` .</li></ul></HTML>

       (Contributed by Mario Carneiro, 14-Jul-2013.) $)
    df-sat $a |- Sat = ( m e. _V , e e. _V |->
       ( rec ( ( f e. _V |-> ( f u.
           { <. x , y >. | E. u e. f ( E. v e. f
      ( x = ( ( 1st ` u ) |g ( 1st ` v ) ) /\
        y = ( ( m ^m _om ) \ ( ( 2nd ` u ) i^i ( 2nd ` v ) ) ) ) \/ E. i e. _om
      ( x = A.g i ( 1st ` u ) /\
        y = { a e. ( m ^m _om ) | A. z e. m ( { <. i , z >. } u.
          ( a |` ( _om \ { i } ) ) ) e. ( 2nd ` u ) } ) ) } ) ) ,
           { <. x , y >. | E. i e. _om E. j e. _om
      ( x = ( i e.g j ) /\
        y = { a e. ( m ^m _om ) | ( a ` i ) e ( a ` j ) } ) } )
         |` suc _om ) ) $.
  $}

  ${
    $d m u $.
    $( A simplified version of the satisfaction predicate, using the standard
       membership relation and eliminating the extra variable ` n ` .
       (Contributed by Mario Carneiro, 14-Jul-2013.) $)
    df-sate $a |- SatE = ( m e. _V , u e. _V |->
       ( ( ( m Sat ( _E i^i ( m X. m ) ) ) ` _om ) ` u ) ) $.
  $}

  $( Define the predicate which defines the set of valid Godel formulas.  The
     parameter ` n ` defines the maximum height of the formulas: the set
     ` ( Fmla `` (/) ) ` is all formulas of the form ` x e. y ` (which in our
     coding scheme is the set ` ( { (/) } X. ( _om X. _om ) ) ` ; see ~ df-sat
     for the full coding scheme), see ~ fmla0 , and each extra level adds to
     the complexity of the formulas in ` ( Fmla `` n ) ` , see ~ fmlasuc .
     Remark: it is sufficient to have atomic formulas of the form ` x e. y `
     only, because equations (formulas of the form ` x = y ` ), which are
     required as (atomic) formulas, can be introduced as a defined notion in
     terms of ` e.g ` , see ~ df-goeq .
     ` ( Fmla `` _om ) = U_ n e. _om ( Fmla `` n ) ` is the set of all valid
     formulas, see ~ fmla .  (Contributed by Mario Carneiro, 14-Jul-2013.) $)
  df-fmla $a |- Fmla = ( n e. suc _om |-> dom ( ( (/) Sat (/) ) ` n ) ) $.

  ${
    $d m u $.
    $( Define the "proves" relation on a set.  A wff is true in a model ` M `
       if for every valuation ` s e. ( M ^m _om ) ` , the interpretation of the
       wff using the membership relation on ` M ` is true.  Since ` |= ` is
       defined in terms of the interpretations making the given formula true,
       it is not defined on the empty "model" ` M = (/) ` , since there are no
       interpretations.  In particular, the empty set on the LHS of ` |= `
       should not be interpreted as the empty model.  Statement ~ prv0 shows
       that our definition yields ` (/) |= U ` for all formulas, though of
       course the formula ` E. x x = x ` is not satisfied on the empty model.
       (Contributed by Mario Carneiro, 14-Jul-2013.) $)
    df-prv $a |- |= = { <. m , u >. | ( m SatE u ) = ( m ^m _om ) } $.
  $}

$( --- theorems for ` ( I e.g J ) ` , ` ( A |g B ) ` and ` A.g M A ` --- $)

  ${
    $d I x $.  $d J x $.
    $( A "Godel-set of membership".  The variables are identified by their
       indices (which are natural numbers), and the membership v_i ` e. ` v_j
       is coded as ` <. (/) , <. i , j >. >. ` .  (Contributed by AV,
       15-Sep-2023.) $)
    goel $p |- ( ( I e. _om /\ J e. _om )
                 -> ( I e.g J ) = <. (/) , <. I , J >. >. ) $=
      ( vx com wcel wa cgoe co cop cfv c0 df-ov cxp cvv cmpt wceq df-goel opeq2
      cv a1i adantl opelxpi opex fvmptd eqtrid ) ADEBDEFZABGHABIZGJKUGIZABGLUFC
      UGKCSZIZUHDDMZGNGCUKUJOPUFCQTUIUGPUJUHPUFUIUGKRUAABDDUBUHNEUFKUGUCTUDUE
      $.
  $}

  $( A "Godel-set of membership" is a member of a doubled Cartesian product.
     (Contributed by AV, 16-Sep-2023.) $)
  goelel3xp $p |- ( ( I e. _om /\ J e. _om )
                    -> ( I e.g J ) e. ( _om X. ( _om X. _om ) ) ) $=
    ( com wcel wa cgoe co c0 cop cxp goel peano1 a1i opelxpi opelxpd eqeltrd )
    ACDBCDEZABFGHABIZICCCJZJABKQHRCSHCDQLMABCCNOP $.

  $( Two "Godel-set of membership" codes for two variables are equal iff the
     two corresponding variables are equal.  (Contributed by AV,
     8-Oct-2023.) $)
  goeleq12bg $p |- ( ( ( M e. _om /\ N e. _om ) /\ ( I e. _om /\ J e. _om ) )
                   -> ( ( I e.g J ) = ( M e.g N ) <-> ( I = M /\ J = N ) ) ) $=
    ( com wcel wa cgoe co wceq c0 cop goel eqeqan12rd 0ex opex opth biantrur wb
    eqid opthg adantl bitr3id bitrid bitrd ) CEFDEFGZAEFBEFGZGZABHIZCDHIZJKABLZ
    LZKCDLZLZJZACJBDJGZUGUFUIULUJUNABMCDMNUOKKJZUKUMJZGZUHUPKUKKUMOABPQUSURUHUP
    UQURKTRUGURUPSUFABCDEEUAUBUCUDUE $.

  ${
    $d A x $.  $d B x $.
    $( The "Godel-set for the Sheffer stroke NAND" for two formulas ` A ` and
       ` B ` .  (Contributed by AV, 16-Oct-2023.) $)
    gonafv $p |- ( ( A e. V /\ B e. W )
                   -> ( A |g B ) = <. 1o , <. A , B >. >. ) $=
      ( vx wcel wa cgna co cop cfv c1o df-ov cvv cxp wceq opelvvg opeq2 df-gona
      cv opex fvmpt syl eqtrid ) ACFBDFGZABHIABJZHKZLUFJZABHMUEUFNNOZFUGUHPABCD
      QEUFLETZJUHUIHUJUFLRESLUFUAUBUCUD $.
  $}

  ${
    goaleq12d.1 $e |- ( ph -> M = N ) $.
    goaleq12d.2 $e |- ( ph -> A = B ) $.
    $( Equality of the "Godel-set of universal quantification".  (Contributed
       by AV, 18-Sep-2023.) $)
    goaleq12d $p |- ( ph -> A.g M A = A.g N B ) $=
      ( cgol c2o cop wceq df-goal a1i opeq12d opeq2d eqcomi eqtrd ) ABDHZIDBJZJ
      ZCEHZRTKABDLMATIECJZJZUAASUBIADEBCFGNOUCUAKAUAUCCELPMQQ $.
  $}

  $( The Godel-set for the Sheffer stroke NAND is not equal to the Godel-set of
     universal quantification.  (Contributed by AV, 21-Oct-2023.) $)
  gonanegoal $p |- ( a |g b ) =/= A.g i u $=
    ( cv cgna co cgol wne c1o c2o wceq cop wa wn 1one2o neii intnanr cvv gonafv
    el2v df-goal eqeq12i 1oex opex opth bitri necon3abii mpbir ) CEZDEZFGZAEZBE
    ZHZIJKLZUJUKMZUNUMMZLZNZOUPUSJKPQRUTULUOULUOLJUQMZKURMZLUTULVAUOVBULVALCDUJ
    UKSSTUAUMUNUBUCJUQKURUDUJUKUEUFUGUHUI $.

$( --- theorems for ` ( M Sat E ) ` --- $)

  ${
    $d E a e f i j m u v x y $.  $d M a e f i j m u v x y z $.  $d V e m $.
    $d W e m $.
    $( The satisfaction predicate as function over wff codes in the model ` M `
       and the binary relation ` E ` on ` M ` .  (Contributed by AV,
       14-Sep-2023.) $)
    satf $p |- ( ( M e. V /\ E e. W )
                -> ( M Sat E ) = ( rec ( ( f e. _V |-> ( f u.
           { <. x , y >. | E. u e. f ( E. v e. f
      ( x = ( ( 1st ` u ) |g ( 1st ` v ) ) /\
        y = ( ( M ^m _om ) \ ( ( 2nd ` u ) i^i ( 2nd ` v ) ) ) ) \/ E. i e. _om
      ( x = A.g i ( 1st ` u ) /\
        y = { a e. ( M ^m _om ) | A. z e. M ( { <. i , z >. } u.
          ( a |` ( _om \ { i } ) ) ) e. ( 2nd ` u ) } ) ) } ) ) ,
           { <. x , y >. | E. i e. _om E. j e. _om
      ( x = ( i e.g j ) /\
        y = { a e. ( M ^m _om ) | ( a ` i ) E ( a ` j ) } ) } )
         |` suc _om ) ) $=
      ( wcel wa cvv cv wceq com wrex vm ve c1st cfv cgna co cmap c2nd cdif cgol
      cin cop csn cres cun wral crab wo copab cmpt cgoe wbr crdg csuc csat cmpo
      df-sat oveq1 adantr difeq1d eqeq2d anbi2d rexbidv simpl raleqdv rabeqbidv
      a1i orbi12d opabbidv uneq2d mpteq2dv breq adantl 2rexbidv rdgeq12 syl2anc
      wb reseq1d elex wfun rdgfun omex sucex resfunexg sylancr ovmpod ) JKNZILN
      ZOZUAUBJIPPFPFQZAQZEQZUCUDZDQZUCUDUEUFRZBQZUAQZSUGUFZXBUHUDZXDUHUDUKZUIZR
      ZOZDWTTZXAXCGQZUJRZXFXOCQULUMMQZSXOUMUIUNUOXINZCXGUPZMXHUQZRZOZGSTZURZEWT
      TZABUSZUOZUTZXAXOHQZVAUFRZXFXOXQUDZYIXQUDZUBQZVBZMXHUQZRZOZHSTGSTZABUSZVC
      ZSVDZUNZFPWTXEXFJSUGUFZXJUIZRZOZDWTTZXPXFXRCJUPZMUUCUQZRZOZGSTZURZEWTTZAB
      USZUOZUTZYJXFYKYLIVBZMUUCUQZRZOZHSTGSTZABUSZVCZUUAUNZVEPVEUAUBPPUUBVFRWSA
      BCDEUBFGHUAMVGVQXGJRZYMIRZOZUUBUVERWSUVHYTUVDUUAUVHYHUUQRYSUVCRYTUVDRUVHF
      PYGUUPUVHYFUUOWTUVHYEUUNABUVHYDUUMEWTUVHXNUUGYCUULUVHXMUUFDWTUVHXLUUEXEUV
      HXKUUDXFUVHXHUUCXJUVFXHUUCRUVGXGJSUGVHVIZVJVKVLVMUVHYBUUKGSUVHYAUUJXPUVHX
      TUUIXFUVHXSUUHMXHUUCUVIUVHXRCXGJUVFUVGVNVOVPVKVLVMVRVMVSVTWAUVHYRUVBABUVH
      YQUVAGHSSUVHYPUUTYJUVHYOUUSXFUVHYNUURMXHUUCUVIUVGYNUURWGUVFYKYLYMIWBWCVPV
      KVLWDVSYSUVCYHUUQWEWFWHWCWQJPNWRJKWIVIWRIPNWQILWIWCWSUVDWJUUAPNZUVEPNUVCU
      UQWKUVJWSSWLWMVQUVDUUAPWNWOWP $.
  $}

  ${
    $d E a f i j u v x y $.  $d M a f i j u v x y z $.
    $( The satisfaction predicate for wff codes in the model ` M ` and the
       binary relation ` E ` on ` M ` at an element of the successor of
       ` _om ` .  (Contributed by AV, 22-Sep-2023.) $)
    satfsucom $p |- ( ( M e. V /\ E e. W /\ N e. suc _om )
                 -> ( ( M Sat E ) ` N )
              = ( rec ( ( f e. _V |-> ( f u.
           { <. x , y >. | E. u e. f ( E. v e. f
      ( x = ( ( 1st ` u ) |g ( 1st ` v ) ) /\
        y = ( ( M ^m _om ) \ ( ( 2nd ` u ) i^i ( 2nd ` v ) ) ) ) \/ E. i e. _om
      ( x = A.g i ( 1st ` u ) /\
        y = { a e. ( M ^m _om ) | A. z e. M ( { <. i , z >. } u.
          ( a |` ( _om \ { i } ) ) ) e. ( 2nd ` u ) } ) ) } ) ) ,
           { <. x , y >. | E. i e. _om E. j e. _om
      ( x = ( i e.g j ) /\
        y = { a e. ( M ^m _om ) | ( a ` i ) E ( a ` j ) } ) } ) ` N ) ) $=
      ( wcel com cfv cv wceq wrex csuc w3a csat co cvv c1st cgna cmap c2nd cdif
      cin wa cgol cop csn cres cun wral crab wo copab cmpt cgoe wbr crdg fveq1d
      satf 3adant3 fvres 3ad2ant3 eqtrd ) JLOZIMOZKPUAZOZUBKJIUCUDZQZKFUEFRZARZ
      ERZUFQZDRZUFQUGUDSBRZJPUHUDZVTUIQZWBUIQUKUJSULDVRTVSWAGRZUMSWCWFCRUNUONRZ
      PWFUOUJUPUQWEOCJURNWDUSSULGPTUTEVRTABVAUQVBVSWFHRZVCUDSWCWFWGQWHWGQIVDNWD
      USSULHPTGPTABVAVEZVNUPZQZKWIQZVLVMVQWKSVOVLVMULKVPWJABCDEFGHIJLMNVGVFVHVO
      VLWKWLSVMKVNWIVIVJVK $.

    $( The satisfaction predicate for wff codes in the model ` M ` and the
       binary relation ` E ` on ` M ` is a function over ` suc _om ` .
       (Contributed by AV, 6-Oct-2023.) $)
    satfn $p |- ( ( M e. V /\ E e. W ) -> ( M Sat E ) Fn suc _om ) $=
      ( vf vx vu vv vy vi vz va vj wa co com cv cfv wceq wrex wcel csat wfn cvv
      csuc c1st cgna cmap c2nd cin cdif cgol cop csn cres cun wral crab wo cmpt
      copab cgoe wbr crdg con0 rdgfnon a1i word wss ordom mpbi ordsson fnssresd
      ordsuc mp1i satf fneq1d mpbird ) BCUAADUANZBAUBOZPUEZUCEUDEQZFQZGQZUFRZHQ
      ZUFRUGOSIQZBPUHOZWDUIRZWFUIRUJUKSNHWBTWCWEJQZULSWGWJKQUMUNLQZPWJUNUKUOUPW
      IUAKBUQLWHURSNJPTUSGWBTFIVAUPUTZWCWJMQZVBOSWGWJWKRWMWKRAVCLWHURSNMPTJPTFI
      VAZVDZWAUOZWAUCVSVEWAWOWOVEUCVSWNWLVFVGWAVHZWAVEVIVSPVHWQVJPVNVKWAVLVOVMV
      SWAVTWPFIKHGEJMABCDLVPVQVR $.

    $d E a f i j n u v x y $.  $d M n z $.  $d V n $.  $d W n $.
    $( The satisfaction predicate for wff codes in the model ` M ` and the
       binary relation ` E ` on ` M ` at omega ( ` _om ` ).  (Contributed by
       AV, 6-Oct-2023.) $)
    satom $p |- ( ( M e. V /\ E e. W ) -> ( ( M Sat E ) ` _om )
                                         = U_ n e. _om ( ( M Sat E ) ` n ) ) $=
      ( vf vx vu vv vy vi va wcel wa com co cfv cv wceq wrex csat cvv c1st cgna
      vz vj cmap c2nd cin cdif cgol cop csn cres cun wral crab wo cmpt cgoe wbr
      copab crdg csuc ciun satf fveq1d omex sucid fvres mp1i wlim pm3.2i adantr
      limom rdglim2a elelsuc adantl fvresd eqtr2d iuneq2dv eqtrd 3eqtrd ) CDMBE
      MNZOCBUAPZQOFUBFRZGRZHRZUCQZIRZUCQUDPSJRZCOUGPZWHUHQZWJUHQUIUJSNIWFTWGWIK
      RZUKSWKWNUERULUMLRZOWNUMUJUNUOWMMUECUPLWLUQSNKOTURHWFTGJVBUOUSZWGWNUFRZUT
      PSWKWNWOQWQWOQBVALWLUQSNUFOTKOTGJVBZVCZOVDZUNZQZOWSQZAOARZWEQZVEZWDOWEXAG
      JUEIHFKUFBCDELVFZVGOWTMXBXCSWDOVHVIOWTWSVJVKWDXCAOXDWSQZVEZXFOUBMZOVLZNXC
      XISWDXJXKVHVOVMAWROUBWPVPVKWDAOXHXEWDXDOMZNZXEXDXAQZXHWDXEXNSXLWDXDWEXAXG
      VGVNXMXDWTWSXLXDWTMWDXDOVQVRVSVTWAWBWC $.
  $}

  ${
    $d E a f i j u v x y $.  $d M a f i j u v x y z $.
    satfvsucom.s $e |- S = ( M Sat E ) $.
    $( The satisfaction predicate as function over wff codes at a successor of
       ` _om ` .  (Contributed by AV, 22-Sep-2023.) $)
    satfvsucom $p |- ( ( M e. V /\ E e. W /\ N e. suc _om ) -> ( S ` N )
           = ( rec ( ( f e. _V |-> ( f u. { <. x , y >. | E. u e. f ( E. v e. f
      ( x = ( ( 1st ` u ) |g ( 1st ` v ) ) /\
        y = ( ( M ^m _om ) \ ( ( 2nd ` u ) i^i ( 2nd ` v ) ) ) ) \/ E. i e. _om
      ( x = A.g i ( 1st ` u ) /\
        y = { a e. ( M ^m _om ) | A. z e. M ( { <. i , z >. } u.
          ( a |` ( _om \ { i } ) ) ) e. ( 2nd ` u ) } ) ) } ) ) ,
           { <. x , y >. | E. i e. _om E. j e. _om
      ( x = ( i e.g j ) /\
        y = { a e. ( M ^m _om ) | ( a ` i ) E ( a ` j ) } ) } ) ` N ) ) $=
      ( com cfv cv wceq wcel csuc w3a cvv c1st cgna co cmap c2nd cdif wrex cgol
      cin wa cop csn cres cun wral crab wo cmpt cgoe wbr crdg csat satf 3adant3
      copab eqtrid fveq1d fvres 3ad2ant3 eqtrd ) KMUAZJNUAZLQUBZUAZUCZLFRLGUDGS
      ZASZESZUERZDSZUERUFUGTBSZKQUHUGZWBUIRZWDUIRUMUJTUNDVTUKWAWCHSZULTWEWHCSUO
      UPOSZQWHUPUJUQURWGUACKUSOWFUTTUNHQUKVAEVTUKABVIURVBWAWHISZVCUGTWEWHWIRWJW
      IRJVDOWFUTTUNIQUKHQUKABVIVEZVQUQZRZLWKRZVSLFWLVSFKJVFUGZWLPVOVPWOWLTVRABC
      DEGHIJKMNOVGVHVJVKVRVOWMWNTVPLVQWKVLVMVN $.
  $}

  ${
    $d E a f i j m n u v x y z $.  $d M a f i j m n u v x y z $.
    satfv0.s $e |- S = ( M Sat E ) $.
    $( The value of the satisfaction predicate as function over wff codes at
       ` (/) ` .  (Contributed by AV, 8-Oct-2023.) $)
    satfv0 $p |- ( ( M e. V /\ E e. W ) -> ( S ` (/) )
              = { <. x , y >. | E. i e. _om E. j e. _om ( x = ( i e.g j )
                  /\ y = { a e. ( M ^m _om ) | ( a ` i ) E ( a ` j ) } ) } ) $=
      ( vz wcel wa cfv cvv cv wceq com wrex vf vu vv vm vn c0 c1st cgna co cmap
      c2nd cin cdif cgol cop csn cres cun wral crab wo copab cmpt cgoe wbr crdg
      csuc peano1 elelsuc satfvsucom mpd3an3 goelel3xp eleq1 syl5ibrcom adantrd
      mp1i cxp pm4.71d 2rexbiia r19.41vv ancom 3bitri opabbii omex xpex wmo cab
      xpexg wi oveq1 eqeq2d fveq2 breq1d rabbidv anbi12d oveq2 breq2d cbvrex2vw
      wal wb eqeq1 adantl goeleq12bg eqcomd breqan12d biimtrdi imp eqeq12 exp4b
      adantr sylbid impd com23 expimpd rexlimdvva rexlimivv sylbi gen2 2rexbidv
      anbi2d mo4 mpbir moabex opabex3d mp2an eqeltri rdg0 eqtrdi ) GHMZFIMZNZUF
      COZUFUAPUAQZAQZUBQZUGOZUCQZUGOUHUIRBQZGSUJUIZYOUKOZYQUKOULUMRNUCYMTYNYPDQ
      ZUNRYRUUALQZUOUPJQZSUUAUPUMUQURYTMLGUSJYSUTRNDSTVAUBYMTABVBURVCZYNUUAEQZV
      DUIZRZYRUUAUUCOZUUEUUCOZFVEZJYSUTZRZNZESTDSTZABVBZVFOZUUOYIYJUFSVGMZYLUUP
      RUFSMUUQYKVHUFSVIVPABLUCUBCUADEFGUFHIJKVJVKUUOUUDUUOYNSSSVQZVQZMZUUNNZABV
      BZPUUNUVAABUUNUUMUUTNZESTDSTUUNUUTNUVAUUMUVCDESSUUASMUUESMNZUUMUUTUVDUUGU
      UTUULUVDUUTUUGUUFUUSMUUAUUEVLYNUUFUUSVMVNVOVRVSUUMUUTDESSVTUUNUUTWAWBWCSP
      MZUURPMZUVBPMWDSSWDWDWEUVEUVFNZUUNABUUSPSUURPPWHUUNBWFZUUNBWGPMUVGUUTNUVH
      UUNUUGUUBUUKRZNZESTDSTZNYRUUBRZWIZLWSBWSUVMBLUUNUVKUVLUUNYNUDQZUEQZVDUIZR
      ZYRUVNUUCOZUVOUUCOZFVEZJYSUTZRZNZUESTUDSTUVKUVLWIZUUMUWCYNUVNUUEVDUIZRZYR
      UVRUUIFVEZJYSUTZRZNDEUDUESSUUAUVNRZUUGUWFUULUWIUWJUUFUWEYNUUAUVNUUEVDWJWK
      UWJUUKUWHYRUWJUUJUWGJYSUWJUUHUVRUUIFUUAUVNUUCWLZWMWNWKWOUUEUVORZUWFUVQUWI
      UWBUWLUWEUVPYNUUEUVOUVNVDWPWKUWLUWHUWAYRUWLUWGUVTJYSUWLUUIUVSUVRFUUEUVOUU
      CWLZWQWNWKWOWRUWCUWDUDUESSUVNSMUVOSMNZUVKUWCUVLUWNUVJUWCUVLWIZDESSUWNUVDN
      ZUUGUVIUWOUWPUUGNZUWCUVIUVLUWQUVQUWBUVIUVLWIZUWQUVQUUFUVPRZUWBUWRWIZUUGUV
      QUWSWTUWPYNUUFUVPXAXBUWPUWSUWTWIUUGUWPUWSUWBUVIUVLUWPUWSNUVLUWBUVINUWAUUK
      RZUWPUWSUXAUWPUWSUWJUWLNZUXAUUAUUEUVNUVOXCUXBUVTUUJJYSUWJUWLUVRUUHUVSUUIF
      UWJUUHUVRUWKXDUWLUUIUVSUWMXDXEWNXFXGYRUWAUUBUUKXHVNXIXJXKXLXMXNXOXMXPXQXG
      XRUUNUVKBLUVLUUMUVJDESSUVLUULUVIUUGYRUUBUUKXAXTXSYAYBUUNBYCVPYDYEYFYGYH
      $.

    $d N u v x y $.  $d S u v x $.  $d V u y $.  $d W u y $.
    $( Lemma 1 for ~ satfvsuc .  (Contributed by AV, 8-Oct-2023.) $)
    satfvsuclem1 $p |- ( ( M e. V /\ E e. W /\ N e. _om )
                -> { <. x , y >. | ( E. u e. ( S ` N ) ( E. v e. ( S ` N )
                     ( x = ( ( 1st ` u ) |g ( 1st ` v ) )
                    /\ y = ( ( M ^m _om ) \ ( ( 2nd ` u ) i^i ( 2nd ` v ) ) ) )
                 \/ E. i e. _om ( x = A.g i ( 1st ` u )
                    /\ y = { a e. ( M ^m _om ) | A. z e. M ( { <. i , z >. } u.
                   ( a |` ( _om \ { i } ) ) ) e. ( 2nd ` u ) } ) )
                    /\ y e. ~P ( M ^m _om ) ) } e. _V ) $=
      ( wcel com cv wa cvv cab w3a c1st cfv cgna co wceq cmap c2nd cin cdif cop
      wrex cgol csn cres cun wral crab wo cpw copab ancom opabbii ovex pwex a1i
      fvex unab abrexex simpl reximi ss2abi ssexi omex unex ralrimiva abrexex2g
      eqeltrri sylancr opabex3rd eqeltrid ) IKOHLOJPOUAZAQZEQZUBUCZDQZUBUCUDUEZ
      UFZBQZIPUGUEZWDUHUCZWFUHUCUIUJUFZRZDJFUCZULZWCWEGQZUMZUFZWIWPCQUKUNMQPWPU
      NUJUOUPWKOCIUQMWJURUFZRZGPULZUSZEWNULZWIWJUTZOZRZABVAXEXCRZABVASXFXGABXCX
      EVBVCWBXCABXDSXDSOWBWJIPUGVDVEVFWBXERZWNSOXBATZSOZEWNUQXCATSOJFVGZXHXJEWN
      XJXHWDWNORWOATZXAATZUPXISWOXAAVHXLXMXLWHDWNULZATDAWNWGXKVIWOXNAWMWHDWNWHW
      LVJVKVLVMXMWRGPULZATGAPWQVNVIXAXOAWTWRGPWRWSVJVKVLVMVOVRVFVPXBEAWNSSVQVSV
      TWA $.

    $( Lemma 2 for ~ satfvsuc .  (Contributed by AV, 8-Oct-2023.) $)
    satfvsuclem2 $p |- ( ( M e. V /\ E e. W /\ N e. _om )
                       -> { <. x , y >. | E. u e. ( S ` N ) ( E. v e. ( S ` N )
                     ( x = ( ( 1st ` u ) |g ( 1st ` v ) )
                    /\ y = ( ( M ^m _om ) \ ( ( 2nd ` u ) i^i ( 2nd ` v ) ) ) )
                 \/ E. i e. _om ( x = A.g i ( 1st ` u )
                    /\ y = { a e. ( M ^m _om ) | A. z e. M ( { <. i , z >. } u.
                   ( a |` ( _om \ { i } ) ) ) e. ( 2nd ` u ) } ) ) } e. _V ) $=
      ( wcel com cv cfv wa wrex w3a c1st cgna wceq cmap c2nd cin cdif cgol cres
      co cop csn cun wral crab copab cpw cvv r19.41v orbi12i ovex difelpw ax-mp
      wo eleq1 mpbiri pm4.71i bianass rexbii rabelpw andir 3bitr4i satfvsuclem1
      bitri opabbii eqeltrid ) IKOHLOJPOUAAQZEQZUBRZDQZUBRUCUKUDZBQZIPUEUKZVSUF
      RZWAUFRUGZUHZUDZSZDJFRZTZVRVTGQZUIUDZWCWLCQULUMMQPWLUMUHUJUNWEOCIUOZMWDUP
      ZUDZSZGPTZVEZEWJTZABUQWTWCWDURZOZSZABUQUSWTXCABWTWSXBSZEWJTXCWSXDEWJWIXBS
      ZDWJTZWQXBSZGPTZVEWKXBSZWRXBSZVEWSXDXFXIXHXJWIXBDWJUTWQXBGPUTVAWKXFWRXHWI
      XEDWJWHWHXBWBWHXBWHXBWGXAOZWDUSOZXKIPUEVBZWDWFUSVCVDWCWGXAVFVGVHVIVJWQXGG
      PWPWPXBWMWPXBWPXBWOXAOZXLXNXMWNMWDUSVKVDWCWOXAVFVGVHVIVJVAWKWRXBVLVMVJWSX
      BEWJUTVOVPABCDEFGHIJKLMNVNVQ $.

    $d N f $.  $d S f y $.  $d V f $.  $d W f $.
    $( The value of the satisfaction predicate as function over wff codes at a
       successor.  (Contributed by AV, 10-Oct-2023.) $)
    satfvsuc $p |- ( ( M e. V /\ E e. W /\ N e. _om ) -> ( S ` suc N )
         = ( ( S ` N ) u. { <. x , y >. | E. u e. ( S ` N ) ( E. v e. ( S ` N )
                     ( x = ( ( 1st ` u ) |g ( 1st ` v ) )
                    /\ y = ( ( M ^m _om ) \ ( ( 2nd ` u ) i^i ( 2nd ` v ) ) ) )
             \/ E. i e. _om ( x = A.g i ( 1st ` u ) /\
                       y = { a e. ( M ^m _om ) | A. z e. M ( { <. i , z >. } u.
                       ( a |` ( _om \ { i } ) ) ) e. ( 2nd ` u ) } ) ) } ) ) $=
      ( wcel com cfv cvv cv wceq vf vj w3a csuc c1st cgna co cmap c2nd cin cdif
      wa wrex cgol cop csn cres cun wral crab wo copab cmpt cgoe peano2 elelsuc
      wbr crdg satfvsucom syl3an3 con0 nnon 3ad2ant3 rdgsuc eqcomd fveq2d rexeq
      syl eqid id orbi1d rexeqbi1dv opabbidv uneq12d fvexd satfvsuclem2 syl2anc
      unexg fvmptd3 eqtrd 3eqtrd ) IKOZHLOZJPOZUCZJUDZFQZWPUARUASZASZESZUEQZDSZ
      UEQUFUGTBSZIPUHUGZWTUIQZXBUIQUJUKTULZDWRUMZWSXAGSZUNTXCXHCSUOUPMSZPXHUPUK
      UQURXEOCIUSMXDUTTULGPUMZVAZEWRUMZABVBZURZVCZWSXHUBSZVDUGTXCXHXIQXPXIQHVGM
      XDUTTULUBPUMGPUMABVBZVHZQZJXRQZXOQZJFQZXFDYBUMZXJVAZEYBUMZABVBZURZWNWLWMW
      PPUDZOZWQXSTWNWPPOYIJVEWPPVFVRABCDEFUAGUBHIWPKLMNVIVJWOJVKOZXSYATWNWLYJWM
      JVLVMXQJXOVNVRWOYAYBXOQYGWOXTYBXOWOYBXTWNWLWMJYHOYBXTTJPVFABCDEFUAGUBHIJK
      LMNVIVJVOVPWOUAYBXNYGRXORXOVSWRYBTZWRYBXMYFYKVTYKXLYEABXKYDEWRYBYKXGYCXJX
      FDWRYBVQWAWBWCWDWOJFWEZWOYBROYFROYGROYLABCDEFGHIJKLMNWFYBYFRRWHWGWIWJWK
      $.
  $}

  ${
    $d E b $.  $d I a b z $.  $d J a b z $.  $d M b z $.  $d N a b z $.
    $( Lemma for ~ satfv1 .  (Contributed by AV, 9-Nov-2023.) $)
    satfv1lem $p |- ( ( N e. _om /\ I e. _om /\ J e. _om )
                      -> { a e. ( M ^m _om ) |
                   A. z e. M ( { <. N , z >. } u. ( a |` ( _om \ { N } ) ) )
                             e. { b e. ( M ^m _om ) | ( b ` I ) E ( b ` J ) } }
             = { a e. ( M ^m _om ) | A. z e. M if- ( I = N ,
                 if- ( J = N , z E z , z E ( a ` J ) ) ,
                 if- ( J = N , ( a ` I ) E z , ( a ` I ) E ( a ` J ) ) ) } ) $=
      ( com wcel cres cfv wbr cmap wceq wa wb cvv adantr adantl w3a cv cop cdif
      csn cun co crab wral wif fveq1 breq12d elrab a1i cin wf 3ad2ant1 ad2antrr
      elex fsnd elmapex simpld snex elmapd adantll mpbird elmapi difssd fssresd
      simpr omex difexi res0 eqtr4i disjdif reseq2i 3eqtr4i elmapresaun syl3anc
      c0 uncom difsnid eqtr2id oveq2d eleqtrrd ibar bicomd simpll1 eqid fvsnun1
      fveq2 breq2d ifptru bibi12d wn wne neqne simpll3 anim12ci eldifsn fvsnun2
      sylibr ifpfal bitrd pm2.61ian breq1d simpll2 adantrl ralbidva rabbidva
      mpdan ) FIJZCIJZDIJZUAZFAUBZUCUEZGUBZIFUEZUDZKZUFZCHUBZLZDYCLZBMZHEINUGZU
      HJZAEUICFOZDFOZXPXPBMZXPDXRLZBMZUJZYJCXRLZXPBMZYOYLBMZUJZUJZAEUIGYGXOXRYG
      JZPZYHYSAEUUAXPEJZPZYHYBYGJZCYBLZDYBLZBMZPZYSYHUUHQUUCYFUUGHYBYGYCYBOYDUU
      EYEUUFBCYCYBUKDYCYBUKULUMUNUUCUUDUUHYSQUUCYBEXSXTUFZNUGZYGUUCXQEXSNUGJZYA
      EXTNUGJZXQXSXTUOZKZYAUUMKZOZYBUUJJUUCUUKXSEXQUPZUUCFXPREXOFRJZYTUUBXLXMUU
      RXNFIUSUQURUUAUUBVJZUTYTUUBUUKUUQQXOYTUUBPZEXSXQRRYTERJZUUBYTUVAIRJXREIVA
      VBZSXSRJUUTFVCUNVDVEVFUUAUULUUBYTUULXOYTUULXTEYAUPYTIEXTXRXREIVGYTIXSVHVI
      YTEXTYARRUVBXTRJYTIXSVKVLUNVDVFTSUUPUUCXQVTKZYAVTKZUUNUUOUVCVTUVDXQVMYAVM
      VNUUMVTXQXSIVOZVPUUMVTYAUVEVPVQUNXSXTEXQYAVRVSUUCIUUIENXOIUUIOZYTUUBXLXMU
      VFXNXLUUIXTXSUFIXSXTWAIFWBWCUQURWDWEUUCUUDPZUUHUUGYSUVGUUGUUHUUDUUGUUHQUU
      CUUDUUGWFTWGYIUVGUUGYSQZYIUVGPUVHFYBLZUUFBMZYNQZUVGUVKYIYJUVGUVKYJUVGPUVK
      UVIUVIBMZYKQZUVGUVMYJUVGUVIXPUVIXPBUUCUVIXPOZUUDUUCFXPIXRYBIEXLXMXNYTUUBW
      HZUUSYBWIZWJSZUVQULTYJUVKUVMQUVGYJUVJUVLYNYKYJUUFUVIUVIBDFYBWKZWLYJYKYMWM
      WNSVFYJWOZUVGPZUVJYMYNUVTUVIXPUUFYLBUVGUVNUVSUVQTUVTFXPIDXRYBIEUVGXLUVSUU
      CXLUUDUVOSZTUVGUUBUVSUUCUUBUUDUUSSZTUVPUVTXNDFWPZPDXTJUVSUWCUVGXNDFWQUUCX
      NUUDXLXMXNYTUUBWRSWSDIFWTXBXAZULUVSYMYNQUVGUVSYNYMYJYKYMXCWGSXDXETYIUVHUV
      KQUVGYIUUGUVJYSYNYIUUEUVIUUFBCFYBWKXFYIYNYRWMWNSVFYIWOZUVGPZUUGYRYSYJUWFU
      UGYRQZYJUWFPUWGUUEUVIBMZYPQZUWFUWIYJUWFUUEYOUVIXPBUWFFXPICXRYBIEUVGXLUWEU
      WATUVGUUBUWEUWBTUVPUWFXMCFWPZPCXTJUWEUWJUVGXMCFWQUUCXMUUDXLXMXNYTUUBXGSWS
      CIFWTXBXAZUVGUVNUWEUVQTULTYJUWGUWIQUWFYJUUGUWHYRYPYJUUFUVIUUEBUVRWLYJYPYQ
      WMWNSVFUVSUWFPZUUGYQYRUWLUUEYOUUFYLBUWFUUEYOOUVSUWKTUVSUVGUUFYLOUWEUWDXHU
      LUVSYQYRQUWFUVSYRYQYJYPYQXCWGSXDXEUWEYRYSQUVGUWEYSYRYIYNYRXCWGSXDXEXDXKXD
      XIXJ $.
  $}

  ${
    $d E a b c d e i j k l x y $.  $d E a b e i j n o x y z $.
    $d E a b c d e k l p x y $.  $d M a b c d e i j k l x y $.
    $d M a b e i j n o x y z $.  $d M a b c d e k l p x y $.
    $d S b e o p x y $.  $d V b e o x y $.  $d W b e o x y $.
    $d n o p x y z $.
    satfv1.s $e |- S = ( M Sat E ) $.
    $( The value of the satisfaction predicate as function over wff codes of
       height 1.  (Contributed by AV, 9-Nov-2023.) $)
    satfv1 $p |- ( ( M e. V /\ E e. W ) -> ( S ` 1o ) = ( ( S ` (/) )
           u. { <. x , y >. | E. i e. _om E. j e. _om ( E. k e. _om E. l e. _om
                   ( x = ( ( i e.g j ) |g ( k e.g l ) )
                  /\ y = { a e. ( M ^m _om ) | ( -. ( a ` i ) E ( a ` j )
                                              \/ -. ( a ` k ) E ( a ` l ) ) } )
             \/ E. n e. _om ( x = A.g n ( i e.g j ) /\
                              y = { a e. ( M ^m _om ) | A. z e. M if- ( i = n ,
         if- ( j = n , z E z , z E ( a ` j ) ) ,
         if- ( j = n , ( a ` i ) E z , ( a ` i ) E ( a ` j ) ) ) } ) ) } ) ) $=
      ( vb wa wceq com wrex vo vp ve vc vd wcel c1o cfv c0 csuc cv c1st cgna co
      cmap c2nd cin cdif cgol cop csn cres cun wral crab wo copab cgoe wn df-1o
      wbr wif fveq2i a1i peano1 satfvsuc mp3an3 wex satfv0 op1std oveq1d eqeq2d
      rexeqdv eqid op2ndd ineq1d difeq2d anbi12d rexbidv eqidd goaleq12d eleq2d
      vex ralbidv rabbidv orbi12d rexopabb bitrdi oveq2d ineq2d orbi1d r19.41vv
      anbi2d 2exbidv wb oveq1 ineq1 bi2anan9 id nfrab1 nfeq2 eleq2 rabbid oveq2
      adantl wi adantr ineq2 inrab difeq2i rabbii reximi sylbir exlimivv biimpd
      fveq1 anim2d reximdva orim12d reximia cvv ovex rabex pm3.2i bicomi 2exbii
      eqeq1 2ex2rexrot bitri sylibr notrab ianor 3eqtri eqtrdi biimpa simpr w3a
      simpll simplr breq12d cbvrabv eleq2i ralbii eqtrid syl3anc sylbid expimpd
      satfv1lem eqcomi eqeq2i biimpi anim2i spc2ev sylancr eqcomd jctil spc2egv
      imp mpsyl ex impbii bitrd opabbidv uneq2d 3eqtrd ) JKUFZILUFZQZUGDUHZUIUJ
      ZDUHZUIDUHZAUKZUAUKZULUHZUBUKZULUHZUMUNZRZBUKZJSUOUNZUWDUPUHZUWFUPUHZUQZU
      RZRZQZUBUWBTZUWCUWEHUKZUSZRZUWJUWSCUKZUTVAMUKZSUWSVAURVBVCZUWLUFZCJVDZMUW
      KVEZRZQZHSTZVFZUAUWBTZABVGZVCZUWBUWCEUKZFUKZVHUNZGUKZNUKZVHUNZUMUNZRZUWJU
      XOUXCUHZUXPUXCUHZIVKZVIUXRUXCUHUXSUXCUHIVKZVIVFZMUWKVEZRZQZNSTZGSTZUWCUXQ
      UWSUSZRZUWJUXOUWSRUXPUWSRZUXBUXBIVKUXBUYDIVKVLUYOUYCUXBIVKUYEVLVLCJVDMUWK
      VEZRZQZHSTZVFZFSTZESTZABVGZVCUVSUWARUVRUGUVTDVJVMVNUVPUVQUISUFUWAUXNRVOAB
      CUBUADHIJUIKLMOVPVQUVRUXMVUCUWBUVRUXLVUBABUVRUXLUCUKZUXQRZPUKZUYEMUWKVEZR
      ZQZFSTESTZUWCVUDUWGUMUNZRZUWJUWKVUFUWMUQZURZRZQZUBUWBTZUWCVUDUWSUSZRZUWJU
      XDVUFUFZCJVDZMUWKVEZRZQZHSTZVFZQZPVRUCVRZVUBUVRUXLUXKUAVUJUCPVGZTVVHUVRUX
      KUAUWBVVIUCPDEFIJKLMOVSWCVUJUXKVVFUCPUAVVIVVIWDUWDVUDVUFUTRZUWRVUQUXJVVEV
      VJUWQVUPUBUWBVVJUWIVULUWPVUOVVJUWHVUKUWCVVJUWEVUDUWGUMVUDVUFUWDUCWMZPWMZV
      TZWAWBVVJUWOVUNUWJVVJUWNVUMUWKVVJUWLVUFUWMVUDVUFUWDVVKVVLWEZWFWGWBWHWIVVJ
      UXIVVDHSVVJUXAVUSUXHVVCVVJUWTVURUWCVVJUWEVUDUWSUWSVVJUWSWJVVMWKWBVVJUXGVV
      BUWJVVJUXFVVAMUWKVVJUXEVUTCJVVJUWLVUFUXDVVNWLWNWOWBWHWIWPWQWRUVRVVHVUJUDU
      KZUXTRZUEUKZUYFMUWKVEZRZQZNSTGSTZUWCVUDVVOUMUNZRZUWJUWKVUFVVQUQZURZRZQZQZ
      UEVRUDVRZVVEVFZQZPVRUCVRZVUBUVRVVGVWKUCPUVRVVFVWJVUJUVRVUQVWIVVEUVRVUQVUP
      UBVWAUDUEVGZTVWIUVRVUPUBUWBVWMUDUEDGNIJKLMOVSWCVWAVUPVWGUDUEUBVWMVWMWDUWF
      VVOVVQUTRZVULVWCVUOVWFVWNVUKVWBUWCVWNUWGVVOVUDUMVVOVVQUWFUDWMZUEWMZVTWSWB
      VWNVUNVWEUWJVWNVUMVWDUWKVWNUWMVVQVUFVVOVVQUWFVWOVWPWEWTWGWBWHWQWRXAXCXDVW
      LVUBVWKVUBUCPVWKVUIVWJQZFSTZESTZVUBVUIVWJEFSSXBZVWRVUAESUXOSUFZVWQUYTFSVX
      AUXPSUFZQZVUIVWJUYTVXCVUIQZVWJVWAUWCUXQVVOUMUNZRZUWJUWKVUGVVQUQZURZRZQZQZ
      UEVRUDVRZUYNUWJUXDVUGUFZCJVDZMUWKVEZRZQZHSTZVFZUYTVUIVWJVXSXEVXCVUIVWIVXL
      VVEVXRVUIVWHVXKUDUEVUIVWGVXJVWAVUEVWCVXFVUHVWFVXIVUEVWBVXEUWCVUDUXQVVOUMX
      FWBVUHVWEVXHUWJVUHVWDVXGUWKVUFVUGVVQXGWGWBXHXCXDVUIVVDVXQHSVUEVUSUYNVUHVV
      CVXPVUEVURUYMUWCVUEVUDUXQUWSUWSVUEUWSWJVUEXIWKWBVUHVVBVXOUWJVUHVVAVXNMUWK
      MVUFVUGUYEMUWKXJXKVUHVUTVXMCJVUFVUGUXDXLWNXMWBXHWIWPZXOVXDVXLUYLVXRUYSVXL
      UYLXPVXDVXKUYLUDUEVXKVVTVXJQZNSTZGSTZUYLVVTVXJGNSSXBZVYBUYKGSVYAUYJNSVVTV
      XJUYJVVTVXFUYBVXIUYIVVTVXEUYAUWCVVPVXEUYARVVSVVOUXTUXQUMXNZXQWBVVSVXIUYIX
      EVVPVVSVXHUYHUWJVVSVXHUWKVUGVVRUQZURZUYHVVSVXGVYFUWKVVQVVRVUGXRWGZVYGUWKU
      YEUYFQZMUWKVEZURVYIVIZMUWKVEUYHVYFVYJUWKUYEUYFMUWKXSXTVYIMUWKUUAVYKUYGMUW
      KUYEUYFUUBYAUUCZUUDWBXOWHUUEYBYBYCYDVNVXCVXRUYSXPVUIVXCVXQUYRHSVXCUWSSUFZ
      QZVXPUYQUYNVYNVXPUYQVYNVXOUYPUWJVYNVYMVXAVXBVXOUYPRVXCVYMUUFVXAVXBVYMUUHV
      XAVXBVYMUUIVYMVXAVXBUUGVXOUXDUXOVUFUHZUXPVUFUHZIVKZPUWKVEZUFZCJVDZMUWKVEU
      YPVXNVYTMUWKVXMVYSCJVUGVYRUXDUYEVYQMPUWKUXCVUFRUYCVYOUYDVYPIUXOUXCVUFYFUX
      PUXCVUFYFUUJUUKUULUUMYACIUXOUXPJUWSMPUURUUNUUOZWBYEYGYHXQYIUUPUUQYHYJYCYD
      VUBVWQPVRUCVRZFSTZESTZVWLVUAWUCESVXAUYTWUBFSVXCUYTWUBUXQYKUFZVUGYKUFZQVXC
      UYTQZUXQUXQRZVUGVUGRZQZVXSQZWUBWUEWUFUXOUXPVHYLUYEMUWKJSUOYLZYMYNWUGVXSWU
      JVXCUYTVXSVXCUYLVXLUYSVXRUYLVXLXPVXCUYLVYAUEVRUDVRZNSTZGSTZVXLUYKWUNGSUYJ
      WUMNSUYJUXTUXTRZVVRVVRRZQZUYBUWJVYGRZQZWUMWUPWUQUXTWDVVRWDYNUYIWUSUYBUYIW
      USUYHVYGUWJVYGUYHVYLUUSUUTUVAUVBVYAWURWUTQUDUEUXTVVRUXRUXSVHYLUYFMUWKWULY
      MVVTVVTWURVXJWUTVVPVVPWUPVVSVVSWUQVVOUXTUXTYQVVQVVRVVRYQXHVVPVXFUYBVVSVXI
      WUSVVPVXEUYAUWCVYEWBVVSVXHVYGUWJVYHWBXHWHUVCUVDYBYBVXLVYCUEVRUDVRWUOVXKVY
      CUDUEVYCVXKVYDYOYPVYAUDUEGNSSYRYSYTVNVXCUYRVXQHSVYNUYQVXPUYNVYNUYQVXPVYNU
      YPVXOUWJVYNVXOUYPWUAUVEWBYEYGYHYIUVHWUHWUIUXQWDVUGWDYNUVFVWQWUKUCPUXQVUGY
      KYKVUIVUIWUJVWJVXSVUEVUEWUHVUHVUHWUIVUDUXQUXQYQVUFVUGVUGYQXHVXTWHUVGUVIUV
      JYHYJVWLVWSPVRUCVRWUDVWKVWSUCPVWSVWKVWTYOYPVWQUCPEFSSYRYSYTUVKWRUVLUVMUVN
      UVO $.
  $}

  ${
    $d A a b $.  $d B a b $.  $d E a b $.  $d E i k u v x y z $.  $d M a b $.
    $d M i k u v x y z $.  $d S b $.  $d S a u v x y $.  $d V a b $.
    $d V u y $.  $d W a b $.  $d W u y $.
    satfsschain.s $e |- S = ( M Sat E ) $.
    $( The binary relation of a satisfaction predicate as function over wff
       codes is an increasing chain (with respect to inclusion).  (Contributed
       by AV, 15-Oct-2023.) $)
    satfsschain $p |- ( ( ( M e. V /\ E e. W ) /\ ( A e. _om /\ B e. _om ) )
                        -> ( B C_ A -> ( S ` B ) C_ ( S ` A ) ) ) $=
      ( vb com wcel wa wss cfv wi cv wceq fveq2 sseq2d imbi2d va vx vu vv vy vi
      vk vz csuc weq ssidd a1i pm2.27 adantl simpr c1st cgna cmap c2nd cin cdif
      co wrex cgol cop csn cres wral crab wo copab ssun1 simpl simplll satfvsuc
      cun syl2an23an sseqtrrid adantr sstrd ex syld com23 findsg impcom ) AJKBJ
      KZLZEFKZDGKZLZBAMZBCNZACNZMZOWGWKWJWNWGWKWJWNOZWJWLIPZCNZMZOWJWLWLMZOZWJW
      LUAPZCNZMZOZWJWLXAUIZCNZMZOWOIUAABWPBQZWRWSWJXHWQWLWLWPBCRSTIUAUJZWRXCWJX
      IWQXBWLWPXACRSTWPXEQZWRXGWJXJWQXFWLWPXECRSTWPAQZWRWNWJXKWQWMWLWPACRSTWTWF
      WJWLUKULXAJKZWFLBXAMZLZWJXDXGXNWJXDXGOXNWJLZXDXCXGWJXDXCOXNWJXCUMUNXOXCXG
      XOXCLWLXBXFXOXCUOXOXBXFMXCXOXBUBPZUCPZUPNZUDPZUPNUQVBQUEPZEJURVBZXQUSNZXS
      USNUTVAQLUDXBVCXPXRUFPZVDQXTYCUGPVEVFUHPJYCVFVAVGVPYBKUGEVHUHYAVIQLUFJVCV
      JUCXBVCUBUEVKZVPZXBXFXBYDVLWJWHWIXNXLXFYEQWHWIVMWHWIUOXLWFXMWJVNUBUEUGUDU
      CCUFDEXAFGUHHVOVQVRVSVTWAWBWAWCWDWAWCWE $.
  $}

  ${
    $d A s $.  $d B s $.  $d E a i s u v x y z $.  $d M a i s u v x y z $.
    $d N s u v x y $.  $d S s u v y x $.  $d V s u x y $.  $d W s u x y $.
    satfvsucsuc.s $e |- S = ( M Sat E ) $.
    satfvsucsuc.a $e |- A = ( ( M ^m _om )
                              \ ( ( 2nd ` u ) i^i ( 2nd ` v ) ) ) $.
    satfvsucsuc.b $e |- B = { a e. ( M ^m _om ) | A. z e. M ( { <. i , z >. }
                             u. ( a |` ( _om \ { i } ) ) ) e. ( 2nd ` u ) } $.
    $( The satisfaction predicate as function over wff codes of height
       ` ( N + 1 ) ` , expressed by the minimally necessary satisfaction
       predicates as function over wff codes of height ` N ` .  (Contributed by
       AV, 21-Oct-2023.) $)
    satfvsucsuc $p |- ( ( M e. V /\ E e. W /\ N e. _om )
                        -> ( S ` suc suc N ) = ( ( S ` suc N ) u.
         { <. x , y >. | ( E. u e. ( ( S ` suc N ) \ ( S ` N ) )
                          ( E. v e. ( S ` suc N )
                                ( x = ( ( 1st ` u ) |g ( 1st ` v ) ) /\ y = A )
                         \/ E. i e. _om ( x = A.g i ( 1st ` u ) /\ y = B ) )
                 \/ E. u e. ( S ` N ) E. v e. ( ( S ` suc N ) \ ( S ` N ) )
                     ( x = ( ( 1st ` u ) |g ( 1st ` v ) ) /\ y = A ) ) } ) ) $=
      ( wrex wo vs wcel com w3a csuc cfv cv c1st cgna co wceq cmap c2nd cdif wa
      cin cgol cop csn cres cun wral crab copab peano2 satfvsuc syl3an3 wex orc
      a1i eqeq2i anbi2i rexbii orbi12i bicomi wss 3simpa ancri 3ad2ant3 sssucid
      wi jca satfsschain imp syl2an2r undif eqcomd rexeqdv bitrdi bitrid r19.43
      sylib rexun syl adantr rexbidv orbi1d orbi1i or32 bitri animorr wb eleq2d
      eleq1 adantl elun opabidw orbi2i eqcomi orbi2d mpbird orcd ex simplr olcd
      bitrd jaod sylbid expimpd 2eximdv 19.45v exbii difss ssrexv ax-mp 2rexbii
      imbitrdi reximi imbitrrdi anim2d orim2d impbid elopab 3bitr4g eqrdv eqtrd
      ) KMUBZJNUBZLUCUBZUDZLUEZUEHUFZUUAHUFZAUGZEUGZUHUFZDUGZUHUFUIUJUKZBUGZKUC
      ULUJZUUEUMUFZUUGUMUFUPUNZUKZUOZDUUCSZUUDUUFIUGZUQUKZUUIUUPCUGURUSOUGUCUUP
      USUNUTVAUUKUBCKVBOUUJVCZUKZUOZIUCSZTZEUUCSZABVDZVAZUUCUUHUUIFUKZUOZDUUCSZ
      UUQUUIGUKZUOZIUCSZTZEUUCLHUFZUNZSZUVGDUVNSZEUVMSZTZABVDZVAZYSYQYRUUAUCUBZ
      UUBUVEUKLVEZABCDEHIJKUUAMNOPVFVGYTUAUVEUVTYTUAUGZUUCUBZUWCUUDUUIURZUKZUVC
      UOZBVHAVHZTZUWDUWFUVRUOZBVHZAVHZTZUWCUVEUBZUWCUVTUBZYTUWIUWMYTUWDUWMUWHUW
      DUWMWAYTUWDUWLVIVJYTUWHUWDUWJTZBVHZAVHZUWMYTUWGUWPABYTUWFUVCUWPYTUWFUOZUV
      CUVLEUVMSZUVOTZUWPUVCUVLEUUCSZUWSUXAUXBUVCUVLUVBEUUCUVHUUOUVKUVAUVGUUNDUU
      CUVFUUMUUHFUULUUIQVKVLZVMUVJUUTIUCUVIUUSUUQGUURUUIRVKVLVMVNVMZVOUWSUXBUVL
      EUVMUVNVAZSUXAUWSUVLEUUCUXEUWSUXEUUCUWSUVMUUCVPZUXEUUCUKZYTYQYRUOZUWAYSUO
      ZUOZUWFLUUAVPZUXFYTUXHUXIYQYRYSVQYSYQUXIYRYSUWAUWBVRVSWBZUXKUWSLVTZVJUXJU
      XKUXFUUALHJKMNPWCWDZWEUVMUUCWFZWLWGWHUVLEUVMUVNWMWIWJUWSUWTUWPUVOUWSUWTUV
      GDUVMSZUVKTZEUVMSZUVQTZUWPUWTUVHEUVMSZUVKEUVMSZTZUWSUXSUVHUVKEUVMWKUWSUYB
      UXPUVPTZEUVMSZUYATZUXSUWSUXTUYDUYAUWSUVHUYCEUVMUWSUVHUVGDUXESUYCUWSUVGDUU
      CUXEUWSUXEUUCUWSUXFUXGYTUXFUWFYTUXJUXKUOUXFYTUXJUXKUXLUXKYTUXMVJWBUXNWNZW
      OUXOWLWGWHUVGDUVMUVNWMWIWPWQUYEUXPEUVMSZUVQTZUYATZUXSUYDUYHUYAUXPUVPEUVMW
      KWRUYIUYGUYATZUVQTUXSUYGUVQUYAWSUYJUXRUVQUXRUYJUXPUVKEUVMWKVOWRWTWTWIWJUW
      SUXRUWPUVQUWSUXRUWPUWSUXRUOZUWDUWJUYKUWDUWEUVMUBZUXRTZUWSUXRUYLXAUWSUWDUY
      MXBUXRUWSUWDUYLUUNDUVMSZUVATZEUVMSZTZUYMUWSUWDUWCUVMUYPABVDZVAZUBZUYQYTUW
      DUYTXBUWFYTUUCUYSUWCABCDEHIJKLMNOPVFXCWOUWSUYTUWEUYSUBZUYQUWFUYTVUAXBYTUW
      CUWEUYSXDXEVUAUYLUWEUYRUBZTUYQUWEUVMUYRXFVUBUYPUYLUYPABXGXHWTWIXPUWSUYPUX
      RUYLUYPUXRXBUWSUYOUXQEUVMUYNUXPUVAUVKUUNUVGDUVMUUMUVFUUHUULFUUIFUULQXIVKV
      LVMUUTUVJIUCUUSUVIUUQUURGUUIGUURRXIVKVLVMVNVMVJXJXPWOXKXLXMUWSUVQUWPUWSUV
      QUOZUWJUWDVUCUWFUVRYTUWFUVQXNUWSUVQUVOXAWBXOXMXQXRUWSUVOUWPUWSUVOUOZUWJUW
      DVUDUWFUVRYTUWFUVOXNUVOUVRUWSUVOUVQVIXEWBXOXMXQXRXSXTUWRUWDUWKTZAVHUWMUWQ
      VUEAUWDUWJBYAYBUWDUWKAYAWTYGXQYTUWLUWHUWDYTUWJUWGABYTUVRUVCUWFYTUVOUVCUVQ
      YTUVOUXBUVCUVOUXBWAZYTUVNUUCVPZVUFUUCUVMYCZUVLEUVNUUCYDYEVJUXDYGYTUVQUUOE
      UUCSZUVAEUUCSZTZUVCYTUVQVUKYTUVQUOZVUIVUJVULUUNDUVNSZEUUCSZVUIYTUVQVUNYTU
      VQUVPEUUCSZVUNYTUXFUVQVUOWAUYFUVPEUVMUUCYDWNUVGUUNEDUUCUVNUXCYFYGWDVUMUUO
      EUUCVUGVUMUUOWAVUHUUNDUVNUUCYDYEYHWNXLXMUUOUVAEUUCWKYIXQYJXTYKYLUWNUWDUWC
      UVDUBZTUWIUWCUUCUVDXFVUPUWHUWDUVCABUWCYMXHWTUWOUWDUWCUVSUBZTUWMUWCUUCUVSX
      FVUQUWLUWDUVRABUWCYMXHWTYNYOYP $.
  $}

  ${
    $d A i u v x y $.  $d B i u v x y $.  $d E f i u v x y z $.
    $d M f i u v x y z $.  $d N u v x y $.  $d P v x y $.  $d S u v x y $.
    $d V u y $.  $d W u y $.
    satfbrsuc.s $e |- S = ( M Sat E ) $.
    satfbrsuc.p $e |- P = ( S ` N ) $.
    $( The binary relation of a satisfaction predicate as function over wff
       codes at a successor.  (Contributed by AV, 13-Oct-2023.) $)
    satfbrsuc $p |- ( ( ( M e. V /\ E e. W ) /\ N e. _om
                          /\ ( A e. X /\ B e. Y ) )
                        -> ( A ( S ` suc N ) B <-> ( A P B \/ E. u e. P
             ( E. v e. P ( A = ( ( 1st ` u ) |g ( 1st ` v ) )
                  /\ B = ( ( M ^m _om ) \ ( ( 2nd ` u ) i^i ( 2nd ` v ) ) ) )
            \/ E. i e. _om ( A = A.g i ( 1st ` u ) /\ B = {
                  f e. ( M ^m _om ) | A. z e. M ( { <. i , z >. }
                    u. ( f |` ( _om \ { i } ) ) ) e. ( 2nd ` u ) } ) ) ) ) ) $=
      ( wceq wrex vx vy wcel wa com w3a csuc cfv wbr cv c1st cgna cmap c2nd cin
      co cdif cgol cop csn cres wral crab wo copab satfvsuc 3expa 3adant3 breqd
      cun wb brun eqcomi breqi a1i eqeq1 bi2anan9 rexbidv orbi12d rexeqi orbi1i
      rexeqbii opabbii brabga bitrid 3ad2ant3 bitrd ) KMUCZJNUCZUDZLUEUCZDOUCEP
      UCUDZUFZDELUGGUHZUIDELGUHZUAUJZCUJZUKUHZBUJZUKUHULUPZSZUBUJZKUEUMUPZWQUNU
      HZWSUNUHUOUQZSZUDZBWOTZWPWRIUJZURZSZXBXIAUJUSUTHUJUEXIUTUQVAVJXDUCAKVBHXC
      VCZSZUDZIUETZVDZCWOTZUAUBVEZVJZUIZDEFUIZDWTSZEXESZUDZBFTZDXJSZEXLSZUDZIUE
      TZVDZCFTZVDZWMWNXSDEWJWKWNXSSZWLWHWIWKYMUAUBABCGIJKLMNHQVFVGVHVIWLWJXTYLV
      KWKXTDEWOUIZDEXRUIZVDWLYLDEWOXRVLWLYNYAYOYKYNYAVKWLDEWOFFWORVMZVNVOXGBFTZ
      XOVDZCFTZYKUAUBDEXROPWPDSZXBESZUDZYRYJCFUUBYQYEXOYIUUBXGYDBFYTXAYBUUAXFYC
      WPDWTVPXBEXEVPVQVRUUBXNYHIUEYTXKYFUUAXMYGWPDXJVPXBEXLVPVQVRVSVRXQYSUAUBXP
      YRCWOFYPXHYQXOXGBWOFYPVTWAWBWCWDVSWEWFWG $.
  $}

  ${
    $d E a i j u v x y z $.  $d E a b u v x y $.  $d M a i j u v x y z $.
    $d M b $.  $d N a $.  $d V a b u y $.  $d W a b u y $.
    $( The value of the satisfaction predicate as function over wff codes at a
       natural number is a relation.  (Contributed by AV, 12-Oct-2023.) $)
    satfrel $p |- ( ( M e. V /\ E e. W /\ N e. _om )
                    -> Rel ( ( M Sat E ) ` N ) ) $=
      ( va vx vi vy wcel com co cfv wrel wa cv wi wceq releqd wrex vb csat csuc
      vj vu vv vz c0 fveq2 imbi2d weq cgoe cmap crab copab relopabv eqid satfv0
      wbr mpbiri pm2.27 c1st cgna c2nd cin cdif cgol cop csn cres wral wo simpr
      cun relun sylanblrc satfvsuc ad4ant123 exp31 com23 syld com13 finds com12
      mpbird 3impia ) BDJZAEJZCKJZCBAUBLZMZNZWIWGWHOZWLWMFPZWJMZNZQWMUHWJMZNZQW
      MUAPZWJMZNZQZWMWSUCZWJMZNZQWMWLQFUACWNUHRZWPWRWMXFWOWQWNUHWJUISUJFUAUKZWP
      XAWMXGWOWTWNWSWJUISUJWNXCRZWPXEWMXHWOXDWNXCWJUISUJWNCRZWPWLWMXIWOWKWNCWJU
      ISUJWMWRGPZHPZUDPZULLRIPZXKWNMXLWNMAUSFBKUMLZUNROUDKTHKTZGIUOZNXOGIUPWMWQ
      XPGIWJHUDABDEFWJUQZURSUTWMXBWSKJZXEWMXBXAXRXEQWMXAVAWMXRXAXEWMXRXAXEWMXRO
      ZXAOZXEWTXJUEPZVBMZUFPZVBMVCLRXMXNYAVDMZYCVDMVEVFROUFWTTXJYBXKVGRXMXKUGPV
      HVIWNKXKVIVFVJVNYDJUGBVKFXNUNROHKTVLUEWTTZGIUOZVNZNZXTXAYFNYHXSXAVMYEGIUP
      WTYFVOVPXTXDYGWGWHXRXDYGRXAGIUGUFUEWJHABWSDEFXQVQVRSWEVSVTWAWBWCWDWF $.
  $}

  ${
    $d E a b i r s u v $.  $d F a b i r s u v $.  $d M a b i r s u v $.
    $d N a b i r s u v $.  $d V a b i r s u v $.  $d W a b i r s u v $.
    $d Y a b i r s u v $.  $d a b i r s u v x $.
    $( Lemma for ~ satfdm .  (Contributed by AV, 12-Oct-2023.) $)
    satfdmlem $p |- ( ( ( M e. V /\ E e. W /\ Y e. _om )
                         /\ dom ( ( M Sat E ) ` Y ) = dom ( ( N Sat F ) ` Y ) )
                      -> ( E. u e. ( ( M Sat E ) ` Y )
               ( E. v e. ( ( M Sat E ) ` Y ) x = ( ( 1st ` u ) |g ( 1st ` v ) )
              \/ E. i e. _om x = A.g i ( 1st ` u ) )
                           -> E. a e. ( ( N Sat F ) ` Y )
              ( E. b e. ( ( N Sat F ) ` Y ) x = ( ( 1st ` a ) |g ( 1st ` b ) )
             \/ E. i e. _om x = A.g i ( 1st ` a ) ) ) ) $=
      ( vs wcel cfv wceq wa cv c1st vr com w3a csat co cdm cgna wrex cgol wo wi
      wrel satfrel adantr 1stdm sylan wb eleq2 adantl cop wex fvex eldm2g ax-mp
      cvv ad4antr sylancom ad5antlr vex op1std eqcomd ad3antlr oveqan12d eqeq2d
      simpr biimpd rspcimedv ex exlimdv biimtrid sylbid mpd rexlimdva goaleq12d
      eqidd reximdv orim12d ) GIOEJOKUBOUCZKGEUDUEPZUFZKHFUDUEPZUFZQZRZASZCSZTP
      ZBSZTPZUGUEZQZBWIUHZWOWQDSZUIZQZDUBUHZUJZWOLSZTPZMSZTPZUGUEZQZMWKUHZWOXIX
      CUIZQZDUBUHZUJZLWKUHZCWIWNWPWIOZRZWQWJOZXGXSUKZWNWIULZXTYBWHYDWMEGKIJUMUN
      ZWPWIUOUPYAYBWQWLOZYCWNYBYFUQZXTWMYGWHWJWLWQURUSUNYFWQNSZUTZWKOZNVAZYAYCW
      QVEOYFYKUQWPTVBZNWQWKVEVCVDYAYJYCNYAYJYCYAYJRZXRXGLYIWKYAYJVOYMXHYIQZRZXB
      XNXFXQYOXAXNBWIYOWRWIOZRZWSWJOZXAXNUKZYOYPYDYRWNYDXTYJYNYPYEVFWRWIUOVGYQY
      RWSWLOZYSWMYRYTUQWHXTYJYNYPWJWLWSURVHYTWSUASZUTZWKOZUAVAZYQYSWSVEOYTUUDUQ
      WRTVBZUAWSWKVEVCVDYQUUCYSUAYQUUCYSYQUUCRZXMXAMUUBWKYQUUCVOUUFXJUUBQZRZXAX
      MUUHWTXLWOUUFUUGWQXIWSXKUGYNWQXIQYMYPUUCYNXIWQWQYHXHYLNVIVJVKZVLUUGXKWSWS
      UUAXJUUEUAVIVJVKVMVNVPVQVRVSVTWAWBWCYOXEXPDUBYNXEXPUKYMYNXEXPYNXDXOWOYNWQ
      XIXCXCYNXCWEUUIWDVNVPUSWFWGVQVRVSVTWAWBWC $.

    $d E a b i u v y $.  $d E f w x $.  $d E i m u v x $.  $d E n x $.
    $d F a b i u v z $.  $d F a b f m $.  $d F x y z $.  $d F n $.  $d M m w $.
    $d M n $.  $d M i u v f w x $.  $d M w x y $.  $d N m f z $.  $d N n $.
    $d N x y z $.  $d V n $.  $d V w x y $.  $d W n $.  $d W w x y $.
    $d X a b i u v $.  $d X n $.  $d X x y z $.  $d Y n $.  $d Y x y z $.
    $( The domain of the satisfaction predicate as function over wff codes does
       not depend on the model ` M ` and the binary relation ` E ` on ` M ` .
       (Contributed by AV, 13-Oct-2023.) $)
    satfdm $p |- ( ( ( M e. V /\ E e. W ) /\ ( N e. X /\ F e. Y ) )
                   -> A. n e. _om
                      dom ( ( M Sat E ) ` n ) = dom ( ( N Sat F ) ` n ) ) $=
      ( vx vu vv vz vw vi cfv wceq com wrex wex vy va vf vm vb wcel wa csat cdm
      cv co wi c0 csuc fveq2 dmeqd eqeq12d imbi2d weq cgoe wbr cmap cab rexcom4
      crab rexbii ovex rabex isseti 2th anbi2i 19.42v 3bitr4i bitri abbii copab
      3bitr3ri eqid satfv0 dmopab eqtrdi adantr adantl 3eqtr4a pm2.27 c1st cgna
      c2nd cin cdif cgol cop csn cres cun wral wo simpr w3a simprl simpl df-3an
      satfdmlem sylan simprr eqcomd syl2an impbid difexi biantru bicomi orbi12i
      sylanbrc id 3bitr4g 19.43 3bitr3g abbidv 3eqtr4g uneq12d dmun wb satfvsuc
      syl2an23an mpbird ex syld com23 finds impcom ralrimiva ) DFUFZBGUFZUGZEHU
      FZCIUFZUGZUGZAUJZDBUHUKZPZUIZYSECUHUKZPZUIZQZARYSRUFYRUUFYRJUJZYTPZUIZUUG
      UUCPZUIZQZULYRUMYTPZUIZUMUUCPZUIZQZULYRUAUJZYTPZUIZUURUUCPZUIZQZULZYRUURU
      NZYTPZUIZUVEUUCPZUIZQZULYRUUFULJUAYSUUGUMQZUULUUQYRUVKUUIUUNUUKUUPUVKUUHU
      UMUUGUMYTUOUPUVKUUJUUOUUGUMUUCUOUPUQURJUAUSZUULUVCYRUVLUUIUUTUUKUVBUVLUUH
      UUSUUGUURYTUOUPUVLUUJUVAUUGUURUUCUOUPUQURUUGUVEQZUULUVJYRUVMUUIUVGUUKUVIU
      VMUUHUVFUUGUVEYTUOUPUVMUUJUVHUUGUVEUUCUOUPUQURJAUSZUULUUFYRUVNUUIUUBUUKUU
      EUVNUUHUUAUUGYSYTUOUPUVNUUJUUDUUGYSUUCUOUPUQURYRUUGKUJZLUJZUTUKQZUURUVOUB
      UJZPZUVPUVRPZBVAZUBDRVBUKZVEZQZUGZLRSZKRSZUATZJVCZUVQMUJZUVSUVTCVAZUBERVB
      UKZVEZQZUGZLRSZKRSZMTZJVCZUUNUUPUWHUWRJUWHUWPMTZKRSZUWRUWHUWOMTZLRSZKRSZU
      XAUWEUATZLRSZKRSUWFUATZKRSUXDUWHUXFUXGKRUWELUARVDVFUXFUXCKRUXEUXBLRUVQUWD
      UATZUGUVQUWNMTZUGUXEUXBUXHUXIUVQUXHUXIUAUWCUWAUBUWBDRVBVGZVHVIMUWMUWKUBUW
      LERVBVGZVHVIVJVKUVQUWDUAVLUVQUWNMVLVMVFVFUWFKUARVDVQUXCUWTKRUWOLMRVDVFVNU
      WPKMRVDVNVOYNUUNUWIQYQYNUUNUWGJUAVPZUIUWIYNUUMUXLJUAYTKLBDFGUBYTVRZVSUPUW
      GJUAVTWAWBYQUUPUWSQYNYQUUPUWQJMVPZUIUWSYQUUOUXNJMUUCKLCEHIUBUUCVRZVSUPUWQ
      JMVTWAWCWDUURRUFZYRUVDUVJUXPYRUVDUVJULUXPYRUGZUVDUVCUVJYRUVDUVCULUXPYRUVC
      WEWCUXQUVCUVJUXQUVCUGZUVJUUSUUGUVOWFPZUVPWFPWGUKQZNUJZUWBUVOWHPZUVPWHPWIZ
      WJZQZUGZLUUSSZUUGUXSOUJZWKQZUYAUYHUCUJWLWMUDUJRUYHWMWJWNWOZUYBUFUCDWPZUDU
      WBVEZQZUGZORSZWQZKUUSSZJNVPZWOZUIZUVAUUGUVRWFPZUEUJZWFPWGUKQZUWJUWLUVRWHP
      ZVUBWHPWIZWJZQZUGZUEUVASZUUGVUAUYHWKQZUWJUYJVUDUFUCEWPZUDUWLVEZQZUGZORSZW
      QZUBUVASZJMVPZWOZUIZQZUXRUUTUYRUIZWOUVBVURUIZWOUYTVUTUXRUUTUVBVVBVVCUXQUV
      CWRUXRUYQNTZJVCVUQMTZJVCVVBVVCUXRVVDVVEJUXRUXTUYENTZUGZLUUSSZUYIUYMNTZUGZ
      ORSZWQZKUUSSZVUCVUGMTZUGZUEUVASZVUJVUMMTZUGZORSZWQZUBUVASZVVDVVEUXRUXTLUU
      SSZUYIORSZWQZKUUSSZVUCUEUVASZVUJORSZWQZUBUVASZVVMVWAUXRVWEVWIUXQYLYMUXPWS
      ZUVCVWEVWIULUXQYNUXPVWJUXPYNYQWTUXPYRXAZYLYMUXPXBXMJLKOBCDEFGUURUBUEXCXDU
      XQYOYPUXPWSZUVBUUTQVWIVWEULUVCUXQYQUXPVWLUXPYNYQXEVWKYOYPUXPXBXMUVCUUTUVB
      UVCXNXFJUEUBOCBEDHIUURKLXCXGXHVVLVWDKUUSVVHVWBVVKVWCVVGUXTLUUSUXTVVGVVFUX
      TNUYDUWBUYCUXJXIVIXJXKVFVVJUYIORUYIVVJVVIUYINUYLUYKUDUWBUXJVHVIXJXKVFXLVF
      VVTVWHUBUVAVVPVWFVVSVWGVVOVUCUEUVAVUCVVOVVNVUCMVUFUWLVUEUXKXIVIXJXKVFVVRV
      UJORVUJVVRVVQVUJMVULVUKUDUWLUXKVHVIXJXKVFXLVFXOVVMUYPNTZKUUSSVVDVVLVWMKUU
      SVVLUYGNTZUYONTZWQZVWMVVHVWNVVKVWOVVHUYFNTZLUUSSVWNVVGVWQLUUSVWQVVGUXTUYE
      NVLXKVFUYFLNUUSVDVNVVKUYNNTZORSVWOVVJVWRORVWRVVJUYIUYMNVLXKVFUYNONRVDVNXL
      VWMVWPUYGUYONXPXKVNVFUYPKNUUSVDVNVWAVUPMTZUBUVASVVEVVTVWSUBUVAVVTVUIMTZVU
      OMTZWQZVWSVVPVWTVVSVXAVVPVUHMTZUEUVASVWTVVOVXCUEUVAVXCVVOVUCVUGMVLXKVFVUH
      UEMUVAVDVNVVSVUNMTZORSVXAVVRVXDORVXDVVRVUJVUMMVLXKVFVUNOMRVDVNXLVWSVXBVUI
      VUOMXPXKVNVFVUPUBMUVAVDVNXQXRUYQJNVTVUQJMVTXSXTUUSUYRYAUVAVURYAXSUXQUVJVV
      AYBUVCUXQUVGUYTUVIVUTUXQUVFUYSYRYLYMUXPUXPUVFUYSQYNYLYQYLYMXAWBYNYMYQYLYM
      WRWBVWKJNUCLKYTOBDUURFGUDUXMYCYDUPUXQUVHVUSYRYOYPUXPUXPUVHVUSQYNYOYPWTYNY
      OYPXEVWKJMUCUEUBUUCOCEUURHIUDUXOYCYDUPUQWBYEYFYGYFYHYIYJYK $.
  $}

  ${
    $d E a b f i j u v x y z $.  $d E n $.  $d M a b f i j u v x y z $.
    $d M n $.  $d N a n $.  $d V a b u y $.  $d V n $.  $d W a b u y $.
    $d W n $.  $d b i j n u v x y $.
    $( The range of the satisfaction predicate as function over wff codes in
       any model ` M ` and any binary relation ` E ` on ` M ` for a natural
       number ` N ` is a subset of the power set of all mappings from the
       natural numbers into the model ` M ` .  (Contributed by AV,
       13-Oct-2023.) $)
    satfrnmapom $p |- ( ( M e. V /\ E e. W /\ N e. _om )
                        -> ran ( ( M Sat E ) ` N ) C_ ~P ( M ^m _om ) ) $=
      ( va vx vi vj vy vu wcel com cfv crn cv wi wa wceq wrex vn vb vf w3a csat
      vv vz co cmap cpw csuc fveq2 rneqd eleq2d imbi1d imbi2d weq cgoe wbr crab
      c0 copab eqid satfv0 wex cab rnopab eleq2i vex eqeq1 anbi2d 2rexbidv elab
      exbidv cvv ovex ssrab2 elpwi2 eleq1 mpbiri adantl rexlimivv exlimiv sylbi
      a1i biimtrid sylbid c1st cgna c2nd cin cdif cgol cop csn cres cun wral wo
      wb satfvsuc 3expa rnun eqtrdi rexbidv orbi12d orbi2i bitrdi expcom adantr
      elun bitri imp simpr difss rexlimiva rexlimiv jaoi jaod exp31 finds com12
      3impia ssrdv ) BDLZAELZCMLZUDUACBAUEUHZNZOZBMUIUHZUJZYEYFYGUAPZYJLZYMYLLZ
      QZYGYEYFRZYPYQYMFPZYHNZOZLZYOQZQYQYMVAYHNZOZLZYOQZQYQYMUBPZYHNZOZLZYOQZQZ
      YQYMUUGUKZYHNZOZLZYOQZQYQYPQFUBCYRVASZUUBUUFYQUURUUAUUEYOUURYTUUDYMUURYSU
      UCYRVAYHULUMUNUOUPFUBUQZUUBUUKYQUUSUUAUUJYOUUSYTUUIYMUUSYSUUHYRUUGYHULUMU
      NUOUPYRUUMSZUUBUUQYQUUTUUAUUPYOUUTYTUUOYMUUTYSUUNYRUUMYHULUMUNUOUPYRCSZUU
      BYPYQUVAUUAYNYOUVAYTYJYMUVAYSYIYRCYHULUMUNUOUPYQUUEYMGPZHPZIPZURUHSZJPZUV
      CUCPZNUVDUVGNAUSZUCYKUTZSZRZIMTHMTZGJVBZOZLZYOYQUUDUVNYMYQUUCUVMGJYHHIABD
      EUCYHVCZVDUMUNUVOYMUVLGVEZJVFZLZYQYOUVNUVRYMUVLGJVGVHUVSYOQYQUVSUVEYMUVIS
      ZRZIMTHMTZGVEZYOUVQUWCJYMUAVIZJUAUQZUVLUWBGUWEUVKUWAHIMMUWEUVJUVTUVEUVFYM
      UVIVJVKVLVNVMUWBYOGUWAYOHIMMUWAYOQUVCMLZUVDMLRUVTYOUVEUVTYOUVIYLLUVIYKVOB
      MUIVPZUVHUCYKVQVRYMUVIYLVSVTWAWEWBWCWDWEWFWGUUGMLZUULYQUUQUWHUULRZYQRZUUP
      UUJUVBKPZWHNZUFPZWHNWIUHSZYMYKUWKWJNZUWMWJNWKZWLZSZRZUFUUHTZUVBUWLUVCWMSZ
      YMUVCUGPWNWOYRMUVCWOWLWPWQUWOLUGBWRZFYKUTZSZRZHMTZWSZKUUHTZGVEZWSZYOUWIYQ
      UUPUXJWTZUWHYQUXKQUULYQUWHUXKYQUWHRZUUPYMUUIUWNUVFUWQSZRZUFUUHTZUXAUVFUXC
      SZRZHMTZWSZKUUHTZGJVBZOZWQZLZUXJUXLUUOUYCYMUXLUUOUUHUYAWQZOUYCUXLUUNUYEYE
      YFUWHUUNUYESGJUGUFKYHHABUUGDEFUVPXAXBUMUUHUYAXCXDUNUYDUUJYMUYBLZWSUXJYMUU
      IUYBXKUYFUXIUUJUYFYMUXTGVEZJVFZLUXIUYBUYHYMUXTGJVGVHUYGUXIJYMUWDUWEUXTUXH
      GUWEUXSUXGKUUHUWEUXOUWTUXRUXFUWEUXNUWSUFUUHUWEUXMUWRUWNUVFYMUWQVJVKXEUWEU
      XQUXEHMUWEUXPUXDUXAUVFYMUXCVJVKXEXFXEVNVMXLXGXLXHXIXJXMUWJUUJYOUXIUWIYQUU
      KUWHUULXNXMUXIYOQUWJUXHYOGUXGYOKUUHUXGYOQUWKUUHLUWTYOUXFUWSYOUFUUHUWSYOUW
      MUUHLUWRYOUWNUWRYOUWQYLLUWQYKVOUWGYKUWPXOVRYMUWQYLVSVTWAWAXPUXEYOHMUXEYOQ
      UWFUXDYOUXAUXDYOUXCYLLUXCYKVOUWGUXBFYKVQVRYMUXCYLVSVTWAWEXQXRWEXQWCWEXSWG
      XTYAYBYCYD $.
  $}

  ${
    $d E f i j k l x y z $.  $d M f i j k l x y z $.
    $( The value of the satisfaction predicate as function over wff codes at
       ` (/) ` is a function.  (Contributed by AV, 15-Oct-2023.) $)
    satfv0fun $p |- ( ( M e. V /\ E e. W ) -> Fun ( ( M Sat E ) ` (/) ) ) $=
      ( vx vi vj vy vf vz vk vl wcel wa co cfv cv wceq com wrex csat wfun copab
      c0 cgoe wbr cmap wmo funopab weq wi wal oveq1 eqeq2d fveq2 breq1d rabbidv
      crab anbi12d oveq2 breq2d cbvrex2vw eqtr2 goeleq12bg adantr eqcomd adantl
      breq12d eqeq12 syl5ibrcom expd biimtrdi syl5 imp4a com34 rexlimdvva com23
      impd rexlimivv sylbi imp gen2 eqeq1 anbi2d 2rexbidv mo4 mpbir mpgbir eqid
      satfv0 funeqd mpbiri ) BCMADMNZUDBAUAOZPZUBEQZFQZGQZUEOZRZHQZWQIQZPZWRXBP
      ZAUFZIBSUGOZURZRZNZGSTFSTZEHUCZUBZXLXJHUHZEXJEHUIXMXJWTJQZXGRZNZGSTFSTZNH
      JUJZUKZJULHULXSHJXJXQXRXJWPKQZLQZUEOZRZXAXTXBPZYAXBPZAUFZIXFURZRZNZLSTKST
      XQXRUKZXIYIWPXTWRUEOZRZXAYDXDAUFZIXFURZRZNFGKLSSFKUJZWTYLXHYOYPWSYKWPWQXT
      WRUEUMUNYPXGYNXAYPXEYMIXFYPXCYDXDAWQXTXBUOZUPUQUNUSGLUJZYLYCYOYHYRYKYBWPW
      RYAXTUEUTUNYRYNYGXAYRYMYFIXFYRXDYEYDAWRYAXBUOZVAUQUNUSVBYIYJKLSSXTSMYASMN
      ZXQYIXRYTXPYIXRUKZFGSSYTWQSMWRSMNNZWTXOUUAUUBWTYIXOXRUUBWTYCYHXOXRUKZUUBW
      TYCYHUUCUKZWTYCNWSYBRZUUBUUDWPWSYBVCUUBUUEYPYRNZUUDWQWRXTYAVDUUFYHXOXRUUF
      XRYHXONYGXGRUUFYFXEIXFUUFYDXCYEXDAUUFXCYDYPXCYDRYRYQVEVFUUFXDYEYRXDYERYPY
      SVGVFVHUQXAYGXNXGVIVJVKVLVMVKVNVOVRVPVQVSVTWAWBXJXQHJXRXIXPFGSSXRXHXOWTXA
      XNXGWCWDWEWFWGWHWMWOXKEHWNFGABCDIWNWIWJWKWL $.
  $}

$( --- theorems for ` ( (/) Sat (/) ) ` --- $)

  ${
    $d a f i j u v x y z $.
    $( The satisfaction predicate as function over wff codes in the empty model
       with an empty binary relation.  (Contributed by AV, 14-Sep-2023.) $)
    satf0 $p |- ( (/) Sat (/) ) = ( rec ( ( f e. _V |-> ( f u.
                  { <. x , y >. | ( y = (/) /\ E. u e. f
                                ( E. v e. f x = ( ( 1st ` u ) |g ( 1st ` v ) )
                               \/ E. i e. _om x = A.g i ( 1st ` u ) ) ) } ) ) ,
                  { <. x , y >. | ( y = (/) /\ E. i e. _om E. j e. _om
                                               x = ( i e.g j ) ) } )
                                    |` suc _om ) $=
      ( va c0 co cvv cv cfv wceq com wa wrex crab copab eqtri vz csat c1st cgna
      cmap c2nd cin cdif cgol cop csn cres cun wcel wral wo cmpt cgoe crdg csuc
      wbr 0ex satf mp2an wne peano1 ne0ii map0b ax-mp 0dif eqeq2i anbi2i rexbii
      difeq1i r19.41v bitri rabeqi orbi12i andir bicomi 3bitri biancomi opabbii
      rab0 uneq2i mpteq2i 2rexbii r19.41vv rdgeq12 reseq1i ) IIUBJZEKELZALZDLZU
      CMZCLZUCMUDJNZBLZIOUEJZWNUFMZWPUFMUGZUHZNZPZCWLQZWMWOFLZUINZWRXFUALUJUKHL
      ZOXFUKUHULUMWTUNUAIUOZHWSRZNZPZFOQZUPZDWLQZABSZUMZUQZWMXFGLZURJNZWRXFXHMX
      SXHMIVAZHWSRZNZPZGOQFOQZABSZUSZOUTZULZEKWLWRINZWQCWLQZXGFOQZUPZDWLQZPZABS
      ZUMZUQZYJXTGOQFOQZPZABSZUSZYHULIKUNZUUCWKYINVBVBABUACDEFGIIKKHVCVDYGUUBYH
      XRYRNYFUUANYGUUBNEKXQYQXPYPWLXOYOABXOYJYNXOYKYJPZYLYJPZUPZDWLQYMYJPZDWLQY
      NYJPXNUUFDWLXEUUDXMUUEXEWQYJPZCWLQUUDXDUUHCWLXCYJWQXBIWRXBIXAUHIWSIXAOIVE
      WSINIOVFVGOVHVIZVNXAVJTVKVLVMWQYJCWLVOVPXMXGYJPZFOQUUEXLUUJFOXKYJXGXJIWRX
      JXIHIRIXIHWSIUUIVQXIHWDTVKVLVMXGYJFOVOVPVRVMUUFUUGDWLUUGUUFYKYLYJVSVTVMYM
      YJDWLVOWAWBWCWEWFYEYTABYEYJYSYEXTYJPZGOQFOQYSYJPYDUUKFGOOYCYJXTYBIWRYBYAH
      IRIYAHWSIUUIVQYAHWDTVKVLWGXTYJFGOOWHVPWBWCYFUUAXRYRWIVDWJT $.
  $}

  ${
    $d f i j u v x y $.
    $( The satisfaction predicate as function over wff codes in the empty model
       with an empty binary relation at a successor of ` _om ` .  (Contributed
       by AV, 14-Sep-2023.) $)
    satf0sucom $p |- ( N e. suc _om -> ( ( (/) Sat (/) ) ` N )
              = ( rec ( ( f e. _V |-> ( f u.
                  { <. x , y >. | ( y = (/) /\ E. u e. f
                                ( E. v e. f x = ( ( 1st ` u ) |g ( 1st ` v ) )
                               \/ E. i e. _om x = A.g i ( 1st ` u ) ) ) } ) ) ,
                  { <. x , y >. | ( y = (/) /\ E. i e. _om E. j e. _om
                                               x = ( i e.g j ) ) } ) ` N ) ) $=
      ( com csuc wcel c0 co cfv cv wceq c1st wrex wa copab csat cvv cgna wo cun
      cgol cmpt cgoe crdg cres satf0 fveq1i fvres eqtrid ) HIJZKHLLUAMZNHEUBEOZ
      BOLPZAOZDOQNZCOQNUCMPCUQRUSUTFOZUFPFIRUDDUQRSABTUEUGURUSVAGOUHMPGIRFIRSAB
      TUIZUOUJZNHVBNHUPVCABCDEFGUKULHUOVBUMUN $.

    $( The value of the satisfaction predicate as function over wff codes in
       the empty model with an empty binary relation at ` (/) ` .  (Contributed
       by AV, 14-Sep-2023.) $)
    satf00 $p |- ( ( (/) Sat (/) ) ` (/) ) = { <. x , y >. | ( y = (/)
                              /\ E. i e. _om E. j e. _om x = ( i e.g j ) ) } $=
      ( vf vu vv c0 co cfv cvv cv wceq c1st wrex com wa copab wcel omex csat wo
      cgna cgol cun cmpt cgoe crdg csuc peano1 elelsuc satf0sucom mp2b cxp xpex
      xpexg simpl goelel3xp eleq1 syl5ibrcom rexlimivv ad2antll mpbiri ad2antrl
      opabex2 mp2an rdg0 eqtri ) HHHUAIJZHEKELZBLZHMZALZFLNJZGLNJUCIMGVJOVMVNCL
      ZUDMCPOUBFVJOQABRUEUFZVLVMVODLZUGIZMZDPOCPOZQZABRZUHJZWBHPSZHPUISVIWCMUJH
      PUKABGFECDHULUMWBVPPKSZPPUNZKSZWBKSTPPTTUOWEWGQZWAABPWFUNZPKKPWFKKUPWEWGU
      QVTVMWISZWHVLVSWJCDPPVOPSVQPSQWJVSVRWISVOVQURVMVRWIUSUTVAVBVLVKPSZWHVTVLW
      KWDUJVKHPUSVCVDVEVFVGVH $.
  $}

  ${
    $d B x $.  $d C x $.  $d U u x y $.  $d V u y $.  $d W u y $.
    $d X u x y $.  $d Y u v x y $.  $d Z u w x y $.
    $( Lemma for ~ satf0suc , ~ sat1el2xp and ~ fmlasuc0 .  (Contributed by AV,
       19-Sep-2023.) $)
    satf0suclem $p |- ( ( X e. U /\ Y e. V /\ Z e. W )
                     -> { <. x , y >. | ( y = (/) /\ E. u e. X
                          ( E. v e. Y x = B \/ E. w e. Z x = C ) ) } e. _V ) $=
      ( wcel c0 wceq wrex com cvv cab cv wo wa copab peano1 eleq1 mpbiri adantr
      w3a pm4.71ri opabbii omex a1i wral simp1 cun unab abrexexg 3ad2ant2 unexg
      3ad2ant3 syl2anc eqeltrrid ralrimivw abrexex2g opabex3rd wss simpr anim2i
      ssopab2i ssexd eqeltrid ) KHNZLINZMJNZUIZBUAZOPZAUAZFPDLQZVSGPCMQZUBZEKQZ
      UCZABUDVQRNZWDUCZABUDZSWDWFABWDWEVRWEWCVRWEORNUEVQORUFUGUHUJUKVPWGWEWCUCZ
      ABUDZSVPWCABRSRSNVPULUMVPWCATSNZWEVPVMWBATZSNZEKUNWJVMVNVOUOVPWLEKVPWKVTA
      TZWAATZUPZSVTWAAUQVPWMSNZWNSNZWOSNVNVMWPVODALFIURUSVOVMWQVNCAMGJURVAWMWNS
      SUTVBVCVDWBEAKHSVEVBUHVFWGWIVGVPWFWHABWDWCWEVRWCVHVIVJUMVKVL $.
  $}

  ${
    $d f i j u v x y $.  $d N f u v x y $.  $d S f u v x y $.
    satf0suc.s $e |- S = ( (/) Sat (/) ) $.
    $( The value of the satisfaction predicate as function over wff codes in
       the empty model and the empty binary relation at a successor.
       (Contributed by AV, 19-Sep-2023.) $)
    satf0suc $p |- ( N e. _om -> ( S ` suc N )
                = ( ( S ` N ) u. { <. x , y >. | ( y = (/) /\ E. u e. ( S ` N )
                         ( E. v e. ( S ` N ) x = ( ( 1st ` u ) |g ( 1st ` v ) )
                        \/ E. i e. _om x = A.g i ( 1st ` u ) ) ) } ) ) $=
      ( vf vj com wcel cfv c0 co cvv cv wceq wrex wa csuc csat c1st cgna wo cun
      cgol copab cmpt cgoe crdg fveq1i omsucelsucb satf0sucom sylbi con0 rdgsuc
      a1i nnon syl elelsuc eqcomi eqtr3di fveq2d eqidd orbi1d rexeqbi1dv anbi2d
      id rexeq opabbidv uneq12d adantl fvex omex satf0suclem unex fvmptd 3eqtrd
      mp3an ) GKLZGUAZEMZWBNNUBOZMZWBIPIQZBQNRZAQZDQUCMZCQUCMUDOZRZCWFSZWHWIFQZ
      UGZRFKSZUEZDWFSZTZABUHZUFZUIZWGWHWMJQUJORJKSFKSTABUHZUKZMZGEMZWGWKCXESZWO
      UEZDXESZTZABUHZUFZWCWERWAWBEWDHULURWAWBKUAZLWEXDRGUMABCDIFJWBUNUOWAXDGXCM
      ZXAMZXEXAMXKWAGUPLXDXNRGUSXBGXAUQUTWAXMXEXAWAGWDMZXMXEWAGXLLXOXMRGKVAABCD
      IFJGUNUTGWDEEWDHVBULVCVDWAIXEWTXKPXAPWAXAVEWFXERZWTXKRWAXPWFXEWSXJXPVIXPW
      RXIABXPWQXHWGWPXGDWFXEXPWLXFWOWKCWFXEVJVFVGVHVKVLVMXEPLZWAGEVNZURXKPLWAXE
      XJXRXQXQKPLXJPLXRXRVOABFCDWJWNPPPXEXEKVPVTVQURVRVSVS $.
  $}

  ${
    $d i j x y z $.  $d N x y $.  $d S x y z $.  $d X x y z $.  $d a b i u v $.
    $d u v x z $.  $d a b x z $.  $d S u v $.  $d S a b $.  $d X a b $.
    satf0op.s $e |- S = ( (/) Sat (/) ) $.
    $( An element of a value of the satisfaction predicate as function over wff
       codes in the empty model and the empty binary relation expressed as
       ordered pair.  (Contributed by AV, 19-Sep-2023.) $)
    satf0op $p |- ( N e. _om -> ( X e. ( S ` N )
                                   <-> E. x ( X = <. x , (/) >.
                                         /\ <. x , (/) >. e. ( S ` N ) ) ) ) $=
      ( vy vi va vb cv cfv wcel c0 wceq wa wex wb eleq2d com wrex vz vj vu csuc
      vv cop fveq2 anbi2d exbidv bibi12d cgoe co copab csat fveq1i satf00 eqtri
      weq eleq2i elopab opeq2 adantr eqeq2d biimpd impcom anim1i adantl vex 0ex
      eqidd eqeq1 2rexbidv bi2anan9r opelopaba bitri sylibr jca exlimiv anbi12d
      anbi1d spcev sylan2b impbii exbii 3bitri c1st cgna cgol cun satf0suc elun
      wo a1i orbi2d 3bitrd simpr wi opeq1 rexbidv orbi12d cbvexvw bitr4di 19.43
      andi bicomi bitr3i bitrdi orbi2i bicomd ex finds ) DFJZBKZLZDAJZMUFZNZXPX
      MLZOZAPZQDMBKZLZXQXPYALZOZAPZQDUAJZBKZLZXQXPYGLZOZAPZQZDYFUDZBKZLZXQXPYNL
      ZOZAPZQZDCBKZLZXQXPYTLZOZAPZQFUACXLMNZXNYBXTYEUUEXMYADXLMBUGZRUUEXSYDAUUE
      XRYCXQUUEXMYAXPUUFRUHUIUJFUAURZXNYHXTYKUUGXMYGDXLYFBUGZRUUGXSYJAUUGXRYIXQ
      UUGXMYGXPUUHRUHUIUJXLYMNZXNYOXTYRUUIXMYNDXLYMBUGZRUUIXSYQAUUIXRYPXQUUIXMY
      NXPUUJRUHUIUJXLCNZXNUUAXTUUDUUKXMYTDXLCBUGZRUUKXSUUCAUUKXRUUBXQUUKXMYTXPU
      ULRUHUIUJYBDUUEXOGJZUBJUKULZNZUBSTGSTZOZAFUMZLDXOXLUFZNZUUQOZFPZAPYEYAUUR
      DYAMMMUNULZKZUURMBUVCEUOZAFGUBUPUQUSUUQAFDUTUVBYDAUVBYDUVAYDFUVAXQYCUUQUU
      TXQUUQUUTXQUUQUUSXPDUUEUUSXPNUUPXLMXOVAZVBVCVDVEUVAMMNZUUPOZYCUUQUVHUUTUU
      EUVGUUPUUEMVJVFVGYCXPYFMNZXLUUNNZUBSTGSTZOZFUAUMZLUVHYAUVMXPYAUVDUVMUVEFU
      AGUBUPUQUSUVLUVHFUAXOMAVHZVIUVIUVIUVGFAURZUVKUUPYFMMVKUVOUVJUUOGUBSSXLXOU
      UNVKVLVMVNVOZVPVQVRYCXQUVHUVBUVPUVAXQUVHOFMVIUUEUUTXQUUQUVHUUEUUSXPDUVFVC
      UUEUUEUVGUUPXLMMVKVTVSWAWBWCWDWEYFSLZYLYSUVQYLOZYOYHDHJZIJZUFZNZUVTMNZUVS
      UCJWFKZUEJWFKWGULZNZUEYGTZUVSUWDUUMWHZNZGSTZWLZUCYGTZOZOZIPZHPZWLZXQYIUVG
      XOUWENZUEYGTZXOUWHNZGSTZWLZUCYGTZOZWLZOZAPZYRUVQYOUWQQYLUVQYODYGUWMHIUMZW
      IZLZYHDUXHLZWLZUWQUVQYNUXIDHIUEUCBGYFEWJZRUXJUXLQUVQDYGUXHWKWMUVQUXKUWPYH
      UXKUWPQUVQUWMHIDUTWMWNWOVBUVRUWQYKXQUXDOZAPZWLZUXGUVRYHYKUWPUXOUVQYLWPUVQ
      UWPUXOQYLUVQUWPDUVSMUFZNZUVGUWLOZOZHPZUXOUWPUYAQUVQUWOUXTHUWOUXTUWNUXTIUW
      NUXRUXSUWMUWBUXRUWCUWBUXRWQUWLUWCUWBUXRUWCUWAUXQDUVTMUVSVAVCZVDVBVEUWNUVG
      UWLUWNMVJUWMUWLUWBUWCUWLWPVGVQVQVRUWNUXTIMVIUWCUWBUXRUWMUXSUYBUWCUWCUVGUW
      LUVTMMVKZVTVSWAWCWDWMUXNUXTAHAHURZXQUXRUXDUXSUYDXPUXQDXOUVSMWRVCUYDUXCUWL
      UVGUYDUXBUWKUCYGUYDUWSUWGUXAUWJUYDUWRUWFUEYGXOUVSUWEVKWSUYDUWTUWIGSXOUVSU
      WHVKWSWTWSUHVSXAXBVBWTUXPYJUXNWLZAPUXGYJUXNAXCUYEUXFAUXFUYEXQYIUXDXDXEWDX
      FXGUVQUXGYRQYLUVQYRUXGUVQYQUXFAUVQYPUXEXQUVQYPXPUXILZUXEUVQYNUXIXPUXMRUYF
      YIXPUXHLZWLUXEXPYGUXHWKUYGUXDYIUWMUXDHIXOMUVNVIUWCUWCUVGHAURZUWLUXCUYCUYH
      UWKUXBUCYGUYHUWGUWSUWJUXAUYHUWFUWRUEYGUVSXOUWEVKWSUYHUWIUWTGSUVSXOUWHVKWS
      WTWSVMVNXHVOXGUHUIXIVBWOXJXK $.
  $}

  ${
    $d i j x y $.  $d i u v x y z $.  $d N x $.
    $( The value of the satisfaction predicate as function over wff codes in
       the empty model and the empty binary relation does not contain the empty
       set.  (Contributed by AV, 19-Sep-2023.) $)
    satf0n0 $p |- ( N e. _om -> (/) e/ ( ( (/) Sat (/) ) ` N ) ) $=
      ( vx vy vi vj vz vu vv com wcel c0 co wn cv wceq fveq2 eleq2d notbid wrex
      cfv csat wnel csuc weq cgoe wa copab 0nelopab satf00 mtbir c1st cgna cgol
      eleq2i wo simpr ioran sylanblrc cun eqid satf0suc adantr bitrdi mtbird ex
      elun finds df-nel sylibr ) AIJKAKKUALZTZJZMZKVKUBKBNZVJTZJZMKKVJTZJZMKCNZ
      VJTZJZMZKVSUCZVJTZJZMZVMBCAVNKOZVPVRWGVOVQKVNKVJPQRBCUDZVPWAWHVOVTKVNVSVJ
      PQRVNWCOZVPWEWIVOWDKVNWCVJPQRVNAOZVPVLWJVOVKKVNAVJPQRVRKVSKOVNDNZENUELOEI
      SDISUFZBCUGZJWLBCUHVQWMKBCDEUIUNUJVSIJZWBWFWNWBUFZWEWAKFNKOVNGNUKTZHNUKTU
      LLOHVTSVNWPWKUMODISUOGVTSUFZBFUGZJZUOZWOWBWSMWTMWNWBUPWQBFUHWAWSUQURWOWEK
      VTWRUSZJWTWOWDXAKWNWDXAOWBBFHGVJDVSVJUTVAVBQKVTWRVFVCVDVEVGKVKVHVI $.
  $}

  ${
    $d N w x $.  $d a b f i j u v w x $.  $d a b r s t u v $.
    $d a b f i u v w x y $.  $d e r s u v $.  $d f i j u v w x z $.
    $d i j s u v $.  $d i s t u v y $.  $d t u v w x y z $.
    $( The first component of an element of the value of the satisfaction
       predicate as function over wff codes in the empty model with an empty
       binary relation is a member of a doubled Cartesian product.
       (Contributed by AV, 17-Sep-2023.) $)
    sat1el2xp $p |- ( N e. _om -> A. w e. ( ( (/) Sat (/) ) ` N )
                            E. a E. b ( 1st ` w ) e. ( _om X. ( a X. b ) ) ) $=
      ( vx vz vi vu vv cv cfv com wcel wex c0 wceq wrex wa cvv wi vy vj vt c1st
      vf vs vr ve cxp csat co wral csuc fveq2 raleqdv cgoe copab eqeq1 2rexbidv
      c2nd anbi2d anbi1d elopabi cop goel eqeq2d omex pm3.2i peano1 a1i opelxpi
      opelxpd xpeq12 xpeq2d eleq2d spc2egv mpsyl eleq1 2exbidv sylbid rexlimivv
      syl5ibrcom adantl syl satf00 eleq2s rgen cgna cgol wo cun cmpt satf0sucom
      crdg omsucelsucb sylbi adantr con0 nnon rdgsuc elelsuc eqcomd eqidd rexeq
      fveq2d orbi1d rexeqbi1dv opabbidv uneq12d fvexd satf0suclem syl3anc unexg
      id syl2anc fvmptd 3eqtrd elun bitrdi eleq1d rspccv rspcva exlimivv expcom
      eqtrd sels eleq2w cbvexvw vex c1o df-ov df-gona ex com23 exlimiv rexlimdv
      com24 c2o jaod rexbidv opeq2 opelvvg fvmptd3 eqtrid eqeltrd exlimdv com14
      opex 1onn syld w3a df-goal ancoms eqeltrid 3adant3 wb 3ad2ant3 mpbird a1d
      2onn impcomd rexlimiv orbi12d syl11 ralrimdv cbvralvw imbitrrdi finds
      3exp ) AJZUDKZLCJZDJZUIZUIZMZDNCNZAEJZOOUJUKZKZULUVQAOUVSKZULUVQAUAJZUVSK
      ZULZUVQAUWBUMZUVSKZULZUVQABUVSKZULEUABUVROPUVQAUVTUWAUVROUVSUNUOUVRUWBPUV
      QAUVTUWCUVRUWBUVSUNUOUVRUWEPUVQAUVTUWFUVRUWEUVSUNUOUVRBPUVQAUVTUWHUVRBUVS
      UNUOUVQAUWAUVQUVJFJZOPZUVRGJZUBJZUPUKZPZUBLQGLQZRZEFUQZUWAUVJUWQMUVJUTKZO
      PZUVKUWMPZUBLQGLQZRZUVQUWPUWJUXARUXBEFUVJUVRUVKPZUWOUXAUWJUXCUWNUWTGUBLLU
      VRUVKUWMURUSVAUWIUWRPUWJUWSUXAUWIUWROURVBVCUXAUVQUWSUWTUVQGUBLLUWKLMZUWLL
      MRZUWTUVKOUWKUWLVDZVDZPZUVQUXEUWMUXGUVKUWKUWLVEVFUXEUVQUXHUXGUVOMZDNCNZLS
      MZUXKRUXEUXGLLLUIZUIZMZUXJUXKUXKVGVGVHUXEOUXFLUXLOLMUXEVIVJUWKUWLLLVKVLUX
      IUXNCDLLSSUVLLPZUVMLPRZUVOUXMUXGUXPUVNUXLLUVLLUVMLVMVNVOVPVQUXHUVPUXICDUV
      KUXGUVOVRVSWBVTWAWCWDEFGUBWEWFWGUWBLMZUWDUCJZUDKZUVOMZDNCNZUCUWFULUWGUXQU
      WDUYAUCUWFUXQUWDUXRUWFMZUYATUXQUWDRZUYBUXRUWCMZUXRUWJUVRHJZUDKZIJZUDKZWHU
      KZPZIUWCQZUVRUYFUWKWIZPZGLQZWJZHUWCQZRZEFUQZMZWJZUYAUYCUYBUXRUWCUYRWKZMUY
      TUYCUWFVUAUXRUYCUWFUWEUESUEJZUWJUYJIVUBQZUYNWJZHVUBQZRZEFUQZWKZWLZUWQWNZK
      ZVUAUXQUWFVUKPZUWDUXQUWELUMZMVULUWBWOEFIHUEGUBUWEWMWPWQUYCVUKUWBVUJKZVUIK
      ZUWCVUIKZVUAUXQVUKVUOPZUWDUXQUWBWRMVUQUWBWSUWQUWBVUIWTWDWQUXQVUOVUPPUWDUX
      QVUNUWCVUIUXQUWCVUNUXQUWBVUMMUWCVUNPUWBLXAEFIHUEGUBUWBWMWDXBXEWQUYCUEUWCV
      UHVUASVUISUYCVUIXCVUBUWCPZVUHVUAPUYCVURVUBUWCVUGUYRVURXNVURVUFUYQEFVURVUE
      UYPUWJVUDUYOHVUBUWCVURVUCUYKUYNUYJIVUBUWCXDXFXGVAXHXIWCUYCUWBUVSXJZUYCUWC
      SMZUYRSMZVUASMVUSUYCVUTVUTUXKVVAVUSVUSUXKUYCVGVJEFGIHUYIUYLSSSUWCUWCLXKXL
      UWCUYRSSXMXOXPXQYEVOUXRUWCUYRXRXSUYCUYDUYAUYSUWDUYDUYATUXQUVQUYAAUXRUWCUV
      JUXRPZUVPUXTCDVVBUVKUXSUVOUVJUXRUDUNXTVSZYAWCUXRUTKZOPZUXSUYIPZIUWCQZUXSU
      YLPZGLQZWJZHUWCQZRZUYCUYAUYSVVKUYCUYATZVVEVVJVVMHUWCUYEUWCMZVVGVVMVVIVVNV
      VFVVMIUWCUYCUYGUWCMZVVFVVNUYAUWDVVOVVFVVNUYATTZTUXQUWDVVOUYHUFJZMZUFNZVVP
      VVOUWDVVSVVOUWDRUYHUVOMZDNCNZVVSUVQVWAAUYGUWCUVJUYGPZUVPVVTCDVWBUVKUYHUVO
      UVJUYGUDUNXTVSYBVVTVVSCDUFUYHUVOYFYCWDYDUWDVVNVVFVVSUYAVVNUWDVVFVVSUYATTZ
      VVNUWDRZUYFVVQMZUFNZVWCVWDUYFUVOMZDNCNZVWFUVQVWHAUYEUWCUVJUYEPZUVPVWGCDVW
      IUVKUYFUVOUVJUYEUDUNXTVSYBVWGVWFCDUFUYFUVOYFYCWDZVWFUYFUGJZMZUGNVWCVWEVWL
      UFUGUFUGUYFYGYHVWLVWCUGVWLVVSVVFUYAVWLVVRVVFUYATZUFVWLVVRVWMVWLVVRRZUYAVV
      FUYIUVOMZDNCNZVWKSMZVVQSMZRVWNUYILVWKVVQUIZUIZMZVWPVWQVWRUGYIUFYIZVHVWNUY
      IYJUYFUYHVDZVDZVWTVWNUYIVXCWHKVXDUYFUYHWHYKVWNUHVXCYJUHJZVDVXDSSUIWHSUHYL
      VXEVXCYJUUAUYFUYHVWKVVQUUBVXDSMVWNYJVXCUUHVJUUCUUDVWNYJVXCLVWSYJLMVWNUUIV
      JUYFUYHVWKVVQVKVLUUEVWOVXACDVWKVVQSSUVLVWKPUVMVVQPZRZUVOVWTUYIVXGUVNVWSLU
      VLVWKUVMVVQVMVNVOVPVQVVFUXTVWOCDUXSUYIUVOVRVSWBYMUUFYNYOWPWDYDYQUUJWCUUGY
      PVVNVVHVVMGLVVNUYCVVHUXDUYAVVNUWDUXQVVHUXDUYATTZVVNUWDUXQVXHTZVWDVWFVXIVW
      JVWEVXIUFVWEVXHUXQVWEUXDVVHUYAVWEUXDVVHUYAUXKVWRRVWEUXDVVHUUKZUXSLLVVQUIZ
      UIZMZUYAUXKVWRVGVXBVHVXJVXMUYLVXLMZVWEUXDVXNVVHVWEUXDRZUYLYRUWKUYFVDZVDVX
      LUYFUWKUULVXOYRVXPLVXKYRLMVXOUUTVJUXDVWEVXPVXKMUWKUYFLVVQVKUUMVLUUNUUOVVH
      VWEVXMVXNUUPUXDUXSUYLVXLVRUUQUURUXTVXMCDLVVQSSUXOVXFRZUVOVXLUXSVXQUVNVXKL
      UVLLUVMVVQVMVNVOVPVQUVIYNUUSYOWDYMUVAYQYPYSUVBWCUYQUWJVVKRVVLEFUXRUVRUXSP
      ZUYPVVKUWJVXRUYOVVJHUWCVXRUYKVVGUYNVVIVXRUYJVVFIUWCUVRUXSUYIURYTVXRUYMVVH
      GLUVRUXSUYLURYTUVCYTVAUWIVVDPUWJVVEVVKUWIVVDOURVBVCUVDYSVTYMUVEUVQUYAAUCU
      WFVVCUVFUVGUVH $.
  $}

$( --- theorems for ` ( Fmla `` N ) ` --- $)

  ${
    $d N n $.
    $( The valid Godel formulas of height ` N ` is the domain of the value of
       the satisfaction predicate as function over wff codes in the empty model
       with an empty binary relation at ` N ` .  (Contributed by AV,
       15-Sep-2023.) $)
    fmlafv $p |- ( N e. suc _om
                   -> ( Fmla ` N ) = dom ( ( (/) Sat (/) ) ` N ) ) $=
      ( vn com csuc wcel cv c0 csat co cfv cdm cfmla cvv cmpt df-fmla a1i fveq2
      wceq dmeqd adantl id fvex dmex fvmptd ) ACDZEZBABFZGGHIZJZKZAUHJZKZUELMLB
      UEUJNRUFBOPUGARZUJULRUFUMUIUKUGAUHQSTUFUAULMEUFUKAUHUBUCPUD $.
  $}

  ${
    $d f i j n u v x y $.
    $( The set of all valid Godel formulas.  (Contributed by AV,
       20-Sep-2023.) $)
    fmla $p |- ( Fmla ` _om ) = U_ n e. _om ( Fmla ` n ) $=
      ( vf vy vx vu vv vi vj com cfmla cfv cv c0 co cdm ciun cvv wcel wceq wrex
      csuc csat cmpt df-fmla fveq1i omex eqidd fveq2 dmeqd adantl fvex dmex a1i
      sucidg fvmptd ax-mp c1st cgna cgol wo wa copab cgoe crdg sucid satf0sucom
      cun wlim limom rdglim2a mp2an eqtri dmeqi dmiun elelsuc fmlafv syl eqtr2d
      iuneq2i 3eqtri ) IJKIAIUAZALZMMUBNZKZOZUCZKZIWCKZOZAIWBJKZPZIJWFAUDUEIQRZ
      WGWISUFWLAIWEWIWAWFQWLWFUGWBISZWEWISWLWMWDWHWBIWCUHUIUJIQUNWIQRWLWHIWCUKU
      LUMUOUPWIAIWBBQBLZCLMSZDLZELUQKZFLUQKURNSFWNTWPWQGLZUSSGITUTEWNTVADCVBVGU
      CZWOWPWRHLVCNSHITGITVADCVBZVDZKZPZOAIXBOZPWKWHXCWHIXAKZXCIWARWHXESIUFVEDC
      FEBGHIVFUPWLIVHXEXCSUFVIAWTIQWSVJVKVLVMAIXBVNAIXDWJWBIRZWJWEXDXFWBWARZWJW
      ESWBIVOZWBVPVQXFWDXBXFXGWDXBSXHDCFEBGHWBVFVQUIVRVSVTVT $.
  $}

  ${
    $d i j x y $.
    $( The valid Godel formulas of height 0 is the set of all formulas of the
       form v_i ` e. ` v_j ("Godel-set of membership") coded as
       ` <. (/) , <. i , j >. >. ` .  (Contributed by AV, 14-Sep-2023.) $)
    fmla0 $p |- ( Fmla ` (/) ) = { x e. _V | E. i e. _om E. j e. _om
                                             x = ( i e.g j ) } $=
      ( vy c0 cfmla cfv csat co cdm cv wceq cgoe com wrex wa copab wcel wex cab
      cvv crab csuc peano1 elelsuc fmlafv mp2b satf00 0ex isseti 19.41v mpbiran
      dmeqi abbii dmopab rabab 3eqtr4i 3eqtri ) EFGZEEEHIGZJZDKELZAKBKCKMILCNOB
      NOZPZADQZJZVCAUAUBZENRENUCRUSVALUDENUEEUFUGUTVEADBCUHUMVDDSZATVCATVFVGVHV
      CAVHVBDSVCDEUIUJVBVCDUKULUNVDADUOVCAUPUQUR $.
  $}

  ${
    $d i j x y z $.
    $( The valid Godel formulas of height 0 is the set of all formulas of the
       form v_i ` e. ` v_j ("Godel-set of membership") coded as
       ` <. (/) , <. i , j >. >. ` .  (Contributed by AV, 15-Sep-2023.) $)
    fmla0xp $p |- ( Fmla ` (/) ) = ( { (/) } X. ( _om X. _om ) ) $=
      ( vx vi vj vy vz c0 cv wceq com wrex cxp wcel wb cop wa eqeq2d wex adantr
      elxpi adantl cfmla cfv cgoe co cvv crab cab csn fmla0 rabab goel 2rexbiia
      eqabcb 0ex a1i opelxpi opelxpd eleq1 syl5ibrcom rexlimivv elsni opeq1d wi
      snid simprr simpl opeq2 eqtrd jca ex 2eximdv r2ex imbitrrdi sylbid impcom
      syl5com exlimivv syl impbii bitri mpgbir 3eqtri ) FUAUBAGZBGZCGZUCUDZHZCI
      JBIJZAUEUFWHAUGZFUHZIIKZKZABCUIWHAUJWIWLHWHWCWLLZMAWHAWLUMWHWCFWDWENZNZHZ
      CIJBIJZWMWGWPBCIIWDILWEILOZWFWOWCWDWEUKPULWQWMWPWMBCIIWRWMWPWOWLLWRFWNWJW
      KFWJLWRFUNVDUOWDWEIIUPUQWCWOWLURUSUTWMWCDGZEGZNZHZWSWJLZWTWKLZOZOZEQDQWQD
      EWCWJWKSXFWQDEXEXBWQXEXBWCFWTNZHZWQXCXBXHMXDXCXAXGWCXCWSFWTWSFVAVBPRXDXHW
      QVCXCXDWTWNHZWROZCQBQZXHWQBCWTIISXHXKWRWPOZCQBQWQXHXJXLBCXHXJXLXHXJOZWRWP
      XHXIWRVEXMWCXGWOXHXJVFXJXGWOHZXHXIXNWRWTWNFVGRTVHVIVJVKWPBCIIVLVMVPTVNVOV
      QVRVSVTWAWB $.
  $}

  ${
    $d N f u v x y $.  $d N n $.  $d f i j u v x y $.
    $( The valid Godel formulas of height ` ( N + 1 ) ` .  (Contributed by AV,
       18-Sep-2023.) $)
    fmlasuc0 $p |- ( N e. _om -> ( Fmla ` suc N )
                      = ( ( Fmla ` N ) u. { x | E. u e. ( ( (/) Sat (/) ) ` N )
           ( E. v e. ( ( (/) Sat (/) ) ` N ) x = ( ( 1st ` u ) |g ( 1st ` v ) )
          \/ E. i e. _om x = A.g i ( 1st ` u ) ) } ) ) $=
      ( vf vy com wcel cfv c0 cdm cvv cv wceq wrex wa copab cun cab vj vn cfmla
      csuc csat co c1st cgna cgol wo cmpt cgoe df-fmla fveq2 omsucelsucb biimpi
      crdg dmeqd fvex dmex a1i fvmptd3 satf0sucom syl con0 rdgsuc eqtrd elelsuc
      nnon eqcomd fveq2d eqidd id rexeq orbi1d rexeqbi1dv anbi2d uneq12d adantl
      opabbidv peano1 eleq1 mpbiri pm4.71ri opabbii omex wral unab abrexex unex
      adantr eqeltrri ralrimiva abrexex2g opabex3rd ax-mp simpr anim2i ssopab2i
      sylancr ssexi eqeltrid fvmptd dmun eqtrdi fmlafv wex dmopab isseti 19.41v
      unexg 0ex mpbiran abbii 3eqtrd ) EHIZEUDZUCJXQKKUEUFZJZLZEFMFNZGNZKOZANZC
      NZUGJZBNUGJUHUFZOZBYAPZYDYFDNZUIZODHPZUJZCYAPZQZAGRZSZUKZYCYDYJUANULUFOUA
      HPDHPQAGRZUQZJZYRJZLZEUCJZYHBEXRJZPZYLUJZCUUEPZATZSZXPUBXQUBNZXRJZLXTHUDZ
      UCMUBUMUUKXQOUULXSUUKXQXRUNURXPXQUUMIZEUOUPZXTMIXPXSXQXRUSUTVAVBXPXSUUBXP
      XSXQYTJZUUBXPUUNXSUUPOUUOAGBCFDUAXQVCVDXPEVEIUUPUUBOEVIYSEYRVFVDVGURXPUUC
      UUELZYCUUHQZAGRZLZSZUUJXPUUCUUEUUSSZLUVAXPUUBUVBXPUUBUUEYRJUVBXPUUAUUEYRX
      PEUUMIZUUAUUEOEHVHZUVCUUEUUAAGBCFDUAEVCVJVDVKXPFUUEYQUVBMYRMXPYRVLYAUUEOZ
      YQUVBOXPUVEYAUUEYPUUSUVEVMUVEYOUURAGUVEYNUUHYCYMUUGCYAUUEUVEYIUUFYLYHBYAU
      UEVNVOVPVQVTVRVSUUEMIZXPEXRUSZVAXPUVFUUSMIUVBMIUVGXPUUSYBHIZUURQZAGRZMUUR
      UVIAGUURUVHYCUVHUUHYCUVHKHIWAYBKHWBWCWKWDWEUVJMIXPUVJUVHUUHQZAGRZHMIZUVLM
      IWFUVMUUHAGHMUVMVMUVMUVHQZUVFUUGATZMIZCUUEWGUUIMIUVGUVNUVPCUUEUVPUVNYEUUE
      IQUUFATZYLATZSUVOMUUFYLAWHUVQUVRBAUUEYGUVGWIDAHYKWFWIWJWLVAWMUUGCAUUEMMWN
      WTWOWPUVIUVKAGUURUUHUVHYCUUHWQWRWSXAVAXBUUEUUSMMXKWTXCVGURUUEUUSXDXEXPUUQ
      UUDUUTUUIXPUUDUUQXPUVCUUDUUQOUVDEXFVDVJXPUUTUURGXGZATZUUIUUTUVTOXPUURAGXH
      VAUVSUUHAUVSYCGXGUUHGKXLXIYCUUHGXJXMXNXEVRVGXO $.

    ${
      $d F i j u v x y z $.
      $( A class is a valid Godel formula of height ` N ` iff it is the first
         component of a member of the value of the satisfaction predicate as
         function over wff codes in the empty model with an empty binary
         relation at ` N ` .  (Contributed by AV, 19-Sep-2023.) $)
      fmlafvel $p |- ( N e. _om -> ( F e. ( Fmla ` N )
                            <-> <. F , (/) >. e. ( ( (/) Sat (/) ) ` N ) ) ) $=
        ( vx vy vi vj vu cvv wcel com cfmla cfv c0 wb cv wceq fveq2 eleq2d wrex
        wa vz vv cop csat co csuc bibi12d imbi2d cgoe crab eqeq1 2rexbidv elrab
        wi weq eqidd simpr jca anim2i ex impbid2 bitrid fmla0 eleq2i a1i satf00
        copab 0ex bi2anan9r opelopabga mpan2 3bitr4d c1st cgna cgol wo cab eqid
        bitrd biantrur bicomi rexbidv orbi12d elabg adantl orbi2d satf0suc elun
        cun bitrdi ad2antrr fmlasuc0 imp orbi1d 3bitrd exp31 finds com12 prcnel
        3bitr4rd wn adantr opprc1 satf0n0 df-nel sylib eqneltrd 2falsed pm2.61i
        wnel ) AHIZBJIZABKLZIZAMUCZBMMUDUEZLZIZNZUNXLXKXSXKACOZKLZIZXOXTXPLZIZN
        ZUNXKAMKLZIZXOMXPLZIZNZUNXKADOZKLZIZXOYKXPLZIZNZUNZXKAYKUFZKLZIZXOYRXPL
        ZIZNZUNXKXSUNCDBXTMPZYEYJXKUUDYBYGYDYIUUDYAYFAXTMKQRUUDYCYHXOXTMXPQRUGU
        HCDUOZYEYPXKUUEYBYMYDYOUUEYAYLAXTYKKQRUUEYCYNXOXTYKXPQRUGUHXTYRPZYEUUCX
        KUUFYBYTYDUUBUUFYAYSAXTYRKQRUUFYCUUAXOXTYRXPQRUGUHXTBPZYEXSXKUUGYBXNYDX
        RUUGYAXMAXTBKQRUUGYCXQXOXTBXPQRUGUHXKAXTEOZFOUIUEZPZFJSEJSZCHUJZIZMMPZA
        UUIPZFJSEJSZTZYGYIUUMXKUUPTZXKUUQUUKUUPCAHXTAPZUUJUUOEFJJXTAUUIUKULZUMX
        KUURUUQUURUUNUUPUURMUPXKUUPUQURXKUUQUURUUQUUPXKUUNUUPUQUSUTVAVBYGUUMNXK
        YFUULACEFVCVDVEXKYIXOYKMPZUUKTZCDVGZIZUUQXKYHUVCXOYHUVCPXKCDEFVFVERXKMH
        IZUVDUUQNVHUVBUUQCDAMHHUVAUVAUUNUUSUUKUUPYKMMUKUUTVIVJVKVSVLYKJIZYQXKUU
        CUVFYQTZXKTZYOXOUAOZMPZXTGOVMLZUBOVMLVNUEZPZUBYNSZXTUVKUUHVOZPZEJSZVPZG
        YNSZTZCUAVGZIZVPZYOAUVSCVQZIZVPZUUBYTUVHUWBUWEYOXKUWBUWENUVGXKUUNAUVLPZ
        UBYNSZAUVOPZEJSZVPZGYNSZTZUWLUWBUWEUWMUWLNXKUWLUWMUUNUWLMVRVTWAVEXKUVEU
        WBUWMNVHUVTUWMCUAAMHHUVJUVJUUNUUSUVSUWLUVIMMUKUUSUVRUWKGYNUUSUVNUWHUVQU
        WJUUSUVMUWGUBYNXTAUVLUKWBUUSUVPUWIEJXTAUVOUKWBWCWBZVIVJVKUVSUWLCAHUWNWD
        VLWEWFUVFUUBUWCNYQXKUVFUUBXOYNUWAWIZIUWCUVFUUAUWOXOCUAUBGXPEYKXPVRWGRXO
        YNUWAWHWJWKUVHYTAYLUWDWIZIZYMUWEVPZUWFUVFYTUWQNYQXKUVFYSUWPACUBGEYKWLRW
        KUWQUWRNUVHAYLUWDWHVEUVHYMYOUWEUVGXKYPUVFYQUQWMWNWOWTWPWQWRXKXAZXLXSUWS
        XLTZXNXRUWSXNXAXLAXMWSXBUWTXOMXQUWSXOMPXLAMXCXBXLMXQIXAZUWSXLMXQXJUXABX
        DMXQXEXFWEXGXHUTXI $.
    $}

    $d N i u v x y $.  $d N v w x y z $.  $d i w u z $.
    $( The valid Godel formulas of height ` ( N + 1 ) ` , expressed by the
       valid Godel formulas of height ` N ` .  (Contributed by AV,
       20-Sep-2023.) $)
    fmlasuc $p |- ( N e. _om -> ( Fmla ` suc N ) = ( ( Fmla ` N ) u.
               { x | E. u e. ( Fmla ` N ) ( E. v e. ( Fmla ` N ) x = ( u |g v )
                                         \/ E. i e. _om x = A.g i u ) } ) ) $=
      ( vy vz vw wcel cfv cv cgna co wceq c0 wrex wa wi eqeq2d wb com csuc c1st
      cfmla csat cgol wo cab cun fmlasuc0 cop wex satf0op fveq2 oveq2d cbvrexvw
      eqid orbi1i w3a fmlafvel biimprd adantld imp vex 0ex op1std eleq1d mpbird
      ad2antrl 3adant3 oveq1 rexbidv eqidd goaleq12d orbi12d adantl oveq2 simpr
      id adantr rspcedvd exp31 exlimdv sylbid oveq1d imbi12d orim1d 3impia 3exp
      rexlimdv syl7bi biimpa biimpd rexlimdva2 impbid abbidv uneq2d eqtrd ) EUA
      IZEUBUDJEUDJZAKZFKZUCJZGKZUCJZLMZNZGEOOUEMZJZPZXAXCDKZUFZNZDUAPZUGZFXIPZA
      UHZUIWTXACKZBKZLMZNZBWTPZXAXRXKUFZNZDUAPZUGZCWTPZAUHZUIAGFDEUJWSXQYHWTWSX
      PYGAWSXPYGWSXOYGFXIWSXBXIIXBXDOUKZNZYIXIIZQZGULZXOYGRGXHEXBXHUQZUMXOXAXCH
      KZUCJZLMZNZHXIPZXNUGZWSYMYGXJYSXNXGYRGHXIXDYONZXFYQXAUUAXEYPXCLXDYOUCUNUO
      SUPURWSYLYTYGRGWSYLYTYGWSYLYTUSZYFXAXCXSLMZNZBWTPZXNUGZCXCWTWSYLXCWTIZYTW
      SYLQZUUGXDWTIZWSYLUUIWSYKUUIYJWSUUIYKXDEUTVAVBVCYJUUGUUITWSYKYJXCXDWTXDOX
      BGVDVEVFZVGVIVHVJXRXCNZYFUUFTUUBUUKYBUUEYEXNUUKYAUUDBWTUUKXTUUCXAXRXCXSLV
      KSVLUUKYDXMDUAUUKYCXLXAUUKXRXCXKXKUUKXKVMUUKVSVNSVLVOVPWSYLYTUUFUUHYSUUEX
      NUUHYSUUERZXAXDYPLMZNZHXIPZXAXDXSLMZNZBWTPZRZWSUUSYLWSUUNUURHXIWSYOXIIYOX
      BOUKZNZUUTXIIZQZFULUUNUURRZFXHEYOYNUMWSUVCUVDFWSUVCUUNUURWSUVCQZUUNQZUUQU
      UNBYPWTUVEYPWTIZUUNUVEUVGXBWTIZWSUVCUVHWSUVBUVHUVAWSUVHUVBXBEUTVAVBVCUVAU
      VGUVHTWSUVBUVAYPXBWTXBOYOFVDVEVFVGVIVHVTXSYPNZUUQUUNTUVFUVIUUPUUMXAXSYPXD
      LVQSVPUVEUUNVRWAWBWCWDWJVTYJUULUUSTWSYKYJYSUUOUUEUURYJYRUUNHXIYJYQUUMXAYJ
      XCXDYPLUUJWESVLYJUUDUUQBWTYJUUCUUPXAYJXCXDXSLUUJWESVLWFVIVHWGWHWAWIWCWKWD
      WJWSYFXPCWTWSXRWTIZQZYFQZXOXAXRXELMZNZGXIPZYEUGZFXROUKZXIUVKUVQXIIZYFWSUV
      JUVRXREUTWLVTXBUVQNZXOUVPTUVLUVSXJUVOXNYEUVSXGUVNGXIUVSXFUVMXAUVSXCXRXELX
      ROXBCVDVEVFZWESVLUVSXMYDDUAUVSXLYCXAUVSXCXRXKXKUVSXKVMUVTVNSVLVOVPUVKYFUV
      PUVKYBUVOYEUVKYAUVOBWTUVKXSWTIZQZYAQZUVNYAGXSOUKZXIUWBUWDXIIZYAUVKUWAUWEW
      SUWAUWERUVJWSUWAUWEXSEUTWMVTVCVTXDUWDNZUVNYATUWCUWFUVMXTXAUWFXEXSXRLXSOXD
      BVDVEVFUOSVPUWBYAVRWAWNWGVCWAWNWOWPWQWR $.

    $d n x y $.  $d i j k l m n o p q x y z $.
    $( The valid Godel formulas of height 1 is the set of all formulas of the
       form ` ( a |g b ) ` and ` A.g k a ` with atoms ` a ` , ` b ` of the form
       ` x e. y ` .  (Contributed by AV, 20-Sep-2023.) $)
    fmla1 $p |- ( Fmla ` 1o ) = ( ( { (/) } X. ( _om X. _om ) )
                                  u. { x | E. i e. _om E. j e. _om E. k e. _om
                               ( E. l e. _om x = ( ( i e.g j ) |g ( k e.g l ) )
                                 \/ x = A.g k ( i e.g j ) ) } ) $=
      ( vp vq cv cgna co wceq wrex com wo cgoe wcel cvv eqeq2d rexbidv wb vy vz
      vm vn vo c1o cfmla cfv c0 csuc cgol cab cun csn cxp fveq2i peano1 fmlasuc
      df-1o ax-mp fmla0xp crab fmla0 rexeqi wi eqeq1 2rexbidv elrab oveq1 eqidd
      weq goaleq12d orbi12d elrab2 oveq2 biimpcd reximdv com12 simplbiim orim1i
      id rexlimiv r19.43 sylibr biimtrdi oveq1d cbvrex2vw oveq2d cbvrexvw ne0ii
      wa wne r19.44zv ovexd simpl adantl simpr rspcedvd ad3antrrr elrabd adantr
      sylanbrc ex imp rexlimdva biimtrrid biimtrid rexlimivv sylbi impbii bitri
      orim12d abbii uneq12i 3eqtri ) UFUGUHUIUJZUGUHZUIUGUHZAHZFHZGHZIJZKZGXRLZ
      XSXTDHZUKZKZDMLZNZFXRLZAULZUMZUIUNMMUOUOZXSBHZCHZOJZYEEHZOJZIJZKZEMLZXSYP
      YEUKZKZNZDMLZCMLZBMLZAULZUMUFXPUGUSUPUIMPXQYLKUQAGFDUIURUTXRYMYKUUHVAYJUU
      GAYJYIFUAHZYPKZCMLBMLZUAQVBZLZUUGYIFXRUULUABCVCVDUUMUUGYIUUGFUULXTUULPXTQ
      PXTYPKZCMLZBMLZYIUUGVEUUKUUPUAXTQUAFVKUUJUUNBCMMUUIXTYPVFVGVHYIUUPUUGYIUU
      OUUFBMYIUUNUUECMUUNYIUUEUUNYIXSYPYAIJZKZGXRLZUUCDMLZNZUUEUUNYDUUSYHUUTUUN
      YCUURGXRUUNYBUUQXSXTYPYAIVIRSUUNYGUUCDMUUNYFUUBXSUUNXTYPYEYEUUNYEVJUUNWAV
      LRSVMUVAUUADMLZUUTNUUEUUSUVBUUTUURUVBGXRYAXRPYAQPYAYRKZEMLZDMLZUURUVBVEUB
      HZYRKZEMLDMLUVEUBYAQXRUBGVKUVGUVCDEMMUVFYAYRVFVGUBDEVCVNUURUVEUVBUURUVDUU
      ADMUURUVCYTEMUVCUURYTUVCUUQYSXSYAYRYPIVORVPVQVQVRVSWBVTUUAUUCDMWCWDWEVRVQ
      VQVRVSWBUUGXSUCHZUDHZOJZYRIJZKZEMLZXSUVJYEUKZKZNZDMLZUDMLUCMLUUMUUEUVQXSU
      VHYOOJZYRIJZKZEMLZXSUVRYEUKZKZNZDMLBCUCUDMMBUCVKZUUDUWDDMUWEUUAUWAUUCUWCU
      WEYTUVTEMUWEYSUVSXSUWEYPUVRYRIYNUVHYOOVIZWFRSUWEUUBUWBXSUWEYPUVRYEYEUWEYE
      VJUWFVLRVMSCUDVKZUWDUVPDMUWGUWAUVMUWCUVOUWGUVTUVLEMUWGUVSUVKXSUWGUVRUVJYR
      IYOUVIUVHOVOZWFRSUWGUWBUVNXSUWGUVRUVJYEYEUWGYEVJUWHVLRVMSWGUVQUUMUCUDMMUV
      QXSUVJUEHZYQOJZIJZKZEMLZXSUVJUWIUKZKZNZUEMLUVHMPZUVIMPZWKZUUMUVPUWPDUEMDU
      EVKZUVMUWMUVOUWOUWTUVLUWLEMUWTUVKUWKXSUWTYRUWJUVJIYEUWIYQOVIWHRSUWTUVNUWN
      XSUWTUVJUVJYEUWIUWTWAUWTUVJVJVLRZVMWIUWSUWPUUMUEMUWPUWLUWONZEMLZUWSUWIMPZ
      WKZUUMMUIWLUXCUWPTUIMUQWJUWLUWOEMWMUTUXEUXBUUMEMUXEYQMPZWKZUXBUUMUXGUXBWK
      ZYIXSUVJYAIJZKZGXRLZUVODMLZNZFUVJUULUXHUUKUVJYPKZCMLZBMLZUAUVJQUUIUVJKUUJ
      UXNBCMMUUIUVJYPVFVGUXHUVHUVIOWNUWSUXPUXDUXFUXBUWSUXOUVJUVRKZCMLZBUVHMUWQU
      WRWOUWEUXOUXRTUWSUWEUXNUXQCMUWEYPUVRUVJUWFRSWPUWSUXQUVJUVJKZCUVIMUWQUWRWQ
      UWGUXQUXSTUWSUWGUVRUVJUVJUWHRWPUWSUVJVJWRWRWSWTXTUVJKZYIUXMTUXHUXTYDUXKYH
      UXLUXTYCUXJGXRUXTYBUXIXSXTUVJYAIVIRSUXTYGUVODMUXTYFUVNXSUXTXTUVJYEYEUXTYE
      VJUXTWAVLRSVMWPUXGUXBUXMUXGUWLUXKUWOUXLUXGUWLUXKUXGUWLWKZUXJUWLGUWJXRUXGU
      WJXRPZUWLUXGUWJQPUWJYPKZCMLZBMLZUYBUXGUWIYQOWNUXGUYDUWJUWIYOOJZKZCMLZBUWI
      MUXEUXDUXFUWSUXDWQXAZBUEVKZUYDUYHTUXGUYJUYCUYGCMUYJYPUYFUWJYNUWIYOOVIRSWP
      UXGUYGUWJUWJKZCYQMUXEUXFWQCEVKZUYGUYKTUXGUYLUYFUWJUWJYOYQUWIOVORWPUXGUWJV
      JWRWRUUPUYEFUWJQXRXTUWJKUUNUYCBCMMXTUWJYPVFVGFBCVCVNXBXAYAUWJKZUXJUWLTUYA
      UYMUXIUWKXSYAUWJUVJIVORWPUXGUWLWQWRXCUXGUWOUXLUXGUWOWKZUVOUWODUWIMUXGUXDU
      WOUYIXAUWTUVOUWOTUYNUXAWPUXGUWOWQWRXCXLXDWRXCXEXFXEXGXHXIXJXKXMXNXO $.
  $}

  ${
    $d F f i u v $.  $d N f i u v $.
    $( The characterization of a Godel formula of height at least 1.
       (Contributed by AV, 14-Oct-2023.) $)
    isfmlasuc $p |- ( ( N e. _om /\ F e. V ) -> ( F e. ( Fmla ` suc N )
                      <-> ( F e. ( Fmla ` N ) \/ E. u e. ( Fmla ` N )
                            ( E. v e. ( Fmla ` N ) F = ( u |g v )
                           \/ E. i e. _om F = A.g i u ) ) ) ) $=
      ( vf com wcel wa csuc cfmla cfv cv wceq wrex wo wb eqeq1 rexbidv cgna cab
      co cgol cun fmlasuc adantr eleq2d elun orbi12d elabg adantl orbi2d 3bitrd
      a1i ) EHIZDFIZJZDEKLMZIDELMZGNZBNZANUAUCZOZAUTPZVAVBCNUDZOZCHPZQZBUTPZGUB
      ZUEZIZDUTIZDVKIZQZVNDVCOZAUTPZDVFOZCHPZQZBUTPZQURUSVLDUPUSVLOUQGABCEUFUGU
      HVMVPRURDUTVKUIUOURVOWBVNUQVOWBRUPVJWBGDFVADOZVIWABUTWCVEVRVHVTWCVDVQAUTV
      ADVCSTWCVGVSCHVADVFSTUJTUKULUMUN $.
  $}

  ${
    $d N i u v x $.
    $( The Godel formulas of height ` N ` are a subset of the Godel formulas of
       height ` N + 1 ` .  (Contributed by AV, 20-Oct-2023.) $)
    fmlasssuc $p |- ( N e. _om -> ( Fmla ` N ) C_ ( Fmla ` suc N ) ) $=
      ( vx vu vv vi com wcel cfmla cfv cv cgna co wceq wrex cgol cab csuc ssun1
      wo cun fmlasuc sseqtrrid ) AFGAHIZBJZCJZDJKLMDUCNUDUEEJOMEFNSCUCNBPZTUCAQ
      HIUCUFRBDCEAUAUB $.
  $}

  ${
    $d N x $.  $d i j u v x y $.
    $( The empty set is not a Godel formula of any height.  (Contributed by AV,
       21-Oct-2023.) $)
    fmlaomn0 $p |- ( N e. _om -> (/) e/ ( Fmla ` N ) ) $=
      ( vx vi vj vu vv com wcel c0 cfmla cfv wn wceq fveq2 eleq2d wrex wral cop
      cv wa vy wnel csuc notbid weq cvv cgoe wne 0ex opex pm3.2i a1i necom opnz
      co bitri sylibr neneqd goel eqeq2d mtbird rgen2 ralnex2 mpbi intnan fmla0
      crab eleq2i eqeq1 2rexbidv elrab mtbir cgna cgol wo simpr c1o 1oex nesymi
      gonafv adantll mtbiri ralrimiva c2o 2oex df-goal eqeq2i jca adantr ralnex
      opnzi anbi12i ioran bitr4i ralbii sylib sylanbrc cab fmlasuc elun rexbidv
      wb cun orbi12d elab orbi2i bitrdi ex finds df-nel ) AGHIAJKZHZLZIXKUBIBSZ
      JKZHZLIIJKZHZLIUASZJKZHZLZIXSUCZJKZHZLZXMBUAAXNIMZXPXRYGXOXQIXNIJNOUDBUAU
      EZXPYAYHXOXTIXNXSJNOUDXNYCMZXPYEYIXOYDIXNYCJNOUDXNAMZXPXLYJXOXKIXNAJNOUDX
      RIUFHZICSZDSZUGUOZMZDGPCGPZTZYPYKYOLZDGQCGQYPLYRCDGGYLGHZYMGHTZYOIIYLYMRZ
      RZMYTIUUBYTYKUUAUFHZTZIUUBUHZUUDYTYKUUCUIYLYMUJUKULUUEUUBIUHUUDIUUBUMIUUA
      UNUPUQURYTYNUUBIYLYMUSUTVAVBYOCDGGVCVDVEXRIXNYNMZDGPCGPZBUFVGZHYQXQUUHIBC
      DVFVHUUGYPBIUFYGUUFYOCDGGXNIYNVIVJVKUPVLXSGHZYBYFUUIYBTZYEYAIESZFSZVMUOZM
      ZFXTPZIUUKYLVNZMZCGPZVOZEXTPZVOZUUJYBUUTLZUVALUUIYBVPUUJUUNLZFXTQZUUQLZCG
      QZTZEXTQZUVBUUIUVHYBUUIUVGEXTUUIUUKXTHZTZUVDUVFUVJUVCFXTUVJUULXTHZTZUUNIV
      QUUKUULRZRZMUVNIVQUVMVRUUKUULUJWKVSUVLUUMUVNIUVIUVKUUMUVNMUUIUUKUULXTXTVT
      WAUTWBWCUVJUVECGUVEUVJYSTUUQIWDYLUUKRZRZMUVPIWDUVOWEYLUUKUJWKVSUUPUVPIUUK
      YLWFWGVLULWCWHWCWIUVHUUSLZEXTQUVBUVGUVQEXTUVGUUOLZUURLZTUVQUVDUVRUVFUVSUU
      NFXTWJUUQCGWJWLUUOUURWMWNWOUUSEXTWJUPWPYAUUTWMWQUUIYEUVAXBYBUUIYEIXTXNUUM
      MZFXTPZXNUUPMZCGPZVOZEXTPZBWRZXCZHZUVAUUIYDUWGIBFECXSWSOUWHYAIUWFHZVOUVAI
      XTUWFWTUWIUUTYAUWEUUTBIUIYGUWDUUSEXTYGUWAUUOUWCUURYGUVTUUNFXTXNIUUMVIXAYG
      UWBUUQCGXNIUUPVIXAXDXAXEXFUPXGWIVAXHXIIXKXJUQ $.
  $}

  $( The empty set is not a Godel formula.  (Contributed by AV,
     19-Nov-2023.) $)
  fmlan0 $p |- (/) e/ ( Fmla ` _om ) $=
    ( vx c0 com cfmla wnel cv wcel wrex wn fmlaomn0 df-nel sylib nrex ciun fmla
    cfv eleq2i eliun bitri xchbinx mpbir ) BCDPZEZBAFZDPZGZACHZIUFACUDCGBUEEUFI
    UDJBUEKLMUCBUBGZUGBUBKUHBACUENZGUGUBUIBAOQABCUERSTUA $.

  ${
    $d A i j x $.  $d B i j x $.
    $( The "Godel-set of NAND" is a Godel formula of at least height 1.
       (Contributed by AV, 21-Oct-2023.) $)
    gonan0 $p |- ( ( A |g B ) e. ( Fmla ` N ) -> N =/= (/) ) $=
      ( vi vj vx cgna cfmla wcel c0 wceq cvv wa wn c1o cop cv com wrex mtbiri
      co cfv cgoe wral 1n0 neii intnanr 1oex opex opth mtbir goel rgen2 ralnex2
      eqeq2d mpbi intnan eqeq1 2rexbidv fmla0 elrab2 gonafv eleq1d cdm wrel cxp
      cmpt wss eqid dmmptss relxp relss df-gona dmeqi releqi mpbir ovprc peano1
      mp2 wnel fmlaomn0 ax-mp neli eleq1 syl pm2.61i fveq2 eleq2d necon2ai ) AB
      GUAZCHUBZIZCJCJKZWLWJJHUBZIZALIBLIMZWONZWPWOOABPZPZWNIZWTWSLIZWSDQZEQZUCU
      AZKZERSDRSZMXFXAXENZERUDDRUDXFNXGDERRXBRIXCRIMZXEWSJXBXCPZPZKZXKOJKZWRXIK
      ZMXLXMOJUEUFUGOWRJXIUHABUIUJUKXHXDXJWSXBXCULUOTUMXEDERRUNUPUQFQZXDKZERSDR
      SXFFWSLWNXNWSKXOXEDERRXNWSXDURUSFDEUTVAUKWPWJWSWNABLLVBVCTWPNWJJKZWQABGGV
      DZVEFLLVFZOXNPZVGZVDZVEZYAXRVHXRVEYBFXRXSXTXTVIVJLLVKYAXRVLVSXQYAGXTFVMVN
      VOVPVQXPWOJWNIJWNJRIJWNVTVRJWAWBWCWJJWNWDTWEWFWMWKWNWJCJHWGWHTWI $.

    $d A i j k x $.
    $( The "Godel-set of universal quantification" is a Godel formula of at
       least height 1.  (Contributed by AV, 22-Oct-2023.) $)
    goaln0 $p |- ( A.g i A e. ( Fmla ` N ) -> N =/= (/) ) $=
      ( vk vj vx cv cfmla cfv wcel c0 wceq c2o cop cvv com wrex wa wn wral cgol
      df-goal cgoe co 2on0 neii intnanr 2oex opex opth mtbir goel eqeq2d mtbiri
      rgen2 ralnex2 intnan eqeq1 2rexbidv fmla0 elrab2 eqneltri eleq2d necon2ai
      mpbi fveq2 ) ABGZUAZCHIZJZCKCKLZVJVHKHIZJVHMVGANZNZVLAVGUBVNVLJVNOJZVNDGZ
      EGZUCUDZLZEPQDPQZRVTVOVSSZEPTDPTVTSWADEPPVPPJVQPJRZVSVNKVPVQNZNZLZWEMKLZV
      MWCLZRWFWGMKUEUFUGMVMKWCUHVGAUIUJUKWBVRWDVNVPVQULUMUNUOVSDEPPUPVEUQFGZVRL
      ZEPQDPQVTFVNOVLWHVNLWIVSDEPPWHVNVRURUSFDEUTVAUKVBVKVIVLVHCKHVFVCUNVD $.

    $d N i u v $.  $d a b i u v x $.
    $( Lemma for ~ gonar (induction step).  (Contributed by AV,
       21-Oct-2023.) $)
    gonarlem $p |- ( N e. _om -> ( ( ( a |g b ) e. ( Fmla ` suc N )
                        -> ( a e. ( Fmla ` suc N ) /\ b e. ( Fmla ` suc N ) ) )
                     -> ( ( a |g b ) e. ( Fmla ` suc suc N )
         -> ( a e. ( Fmla ` suc suc N ) /\ b e. ( Fmla ` suc suc N ) ) ) ) ) $=
      ( vu vv vi com wcel cv cgna co wa wi wceq wrex wb cvv c1o cop rexlimdva
      csuc cfmla cfv wo peano2 ovexd isfmlasuc syl2anc adantr wss fmlasssuc syl
      cgol sseld anim12d com12 imim2i com23 impcom gonafv el2v a1i eqeq12d 1oex
      opex opth bitrdi adantll vex eleq1w equcoms bi2anan9 biimtrdi sylbi com13
      adantl impl sylbid wne gonanegoal eqneqall mpi jaod ex ) AGHZBIZCIZJKZAUA
      ZUBUCZHZWFWJHZWGWJHZLZMZWHWIUAUBUCZHZWFWPHZWGWPHZLZMWEWOLZWQWKWHDIZEIZJKZ
      NZEWJOZWHXBFIZUMZNZFGOZUDZDWJOZUDZWTWEWQXMPZWOWEWIGHZWHQHXNAUEZWEWFWGJUFE
      DFWHWIQUGUHUIXAWKWTXLWOWEWKWTMWOWKWEWTWNWEWTMZWKWEWNWTWEWLWRWMWSWEWJWPWFW
      EXOWJWPUJXPWIUKULZUNWEWJWPWGXRUNUOUPZUQURUSWEXLWTMWOWEXKWTDWJWEXBWJHZLZXF
      WTXJYAXEWTEWJYAXCWJHZLXERRNZWFWGSZXBXCSZNZLZWTXTYBXEYGPWEXTYBLZXERYDSZRYE
      SZNYGYHWHYIXDYJWHYINZYHYKBCWFWGQQUTVAVBXBXCWJWJUTVCRYDRYEVDWFWGVEVFVGVHWE
      XTYBYGWTMYGYHWEWTYFYHXQMZYCYFWFXBNZWGXCNZLZYLWFWGXBXCBVICVIVFYOYHWNXQYMXT
      WLYNYBWMXTWLPDBDBWJVJVKYBWMPECECWJVJVKVLXSVMVNVPVOVQVRTYAXIWTFGXIWTMYAXGG
      HLXIWHXHVSWTDFBCVTWTWHXHWAWBVBTWCTUIWCVRWD $.

    $d N x $.  $d a b i j x $.  $d a b c d $.  $d a b i u v x $.  $d d x $.
    $( If the "Godel-set of NAND" applied to classes is a Godel formula, the
       classes are also Godel formulas.  Remark:  The reverse is not valid for
       ` A ` or ` B ` being of the same height as the "Godel-set of NAND".
       (Contributed by AV, 21-Oct-2023.) $)
    gonar $p |- ( ( N e. _om /\ ( a |g b ) e. ( Fmla ` N ) )
                  -> ( a e. ( Fmla ` N ) /\ b e. ( Fmla ` N ) ) ) $=
      ( vx vu vi vj com wcel cv cfmla cfv wa c0 wceq wrex wi eleq2d anbi12d c1o
      vd vc vv cgna co wne gonan0 adantl csuc nnsuc suceq fveq2d imbi12d wo cvv
      cgol wb peano1 ovex isfmlasuc mp2an cgoe eqeq1 2rexbidv elrab2 cop gonafv
      fmla0 el2v a1i goel eqeq12d 1oex opex opth eqneqall adantr sylbi biimtrdi
      1n0 mpi rexlimdva rexlimiv vex simpl equcomd eleq1d simpr fmlasssuc ax-mp
      wss sseli anim12i com12 sylbid gonanegoal jaod jaoi gonarlem finds mpbird
      fveq2 rexlimiva syl impancom mpd ) AHIZBJZCJZUDUEZAKLZIZMANUFZXHXKIZXIXKI
      ZMZXLXMXGXHXIAUGUHXGXMXLXPXGXMMADJZUIZOZDHPXLXPQZDAUJXSXTDHXQHIZXSMXTXJXR
      KLZIZXHYBIZXIYBIZMZQZYAYGXSXJUAJZUIZKLZIZXHYJIZXIYJIZMZQXJNUIZKLZIZXHYPIZ
      XIYPIZMZQXJUBJZUIZKLZIZXHUUCIZXIUUCIZMZQXJUUBUIZKLZIZXHUUIIZXIUUIIZMZQYGU
      AUBXQYHNOZYKYQYNYTUUNYJYPXJUUNYIYOKYHNUKULZRUUNYLYRYMYSUUNYJYPXHUUORUUNYJ
      YPXIUUORSUMYHUUAOZYKUUDYNUUGUUPYJUUCXJUUPYIUUBKYHUUAUKULZRUUPYLUUEYMUUFUU
      PYJUUCXHUUQRUUPYJUUCXIUUQRSUMYHUUBOZYKUUJYNUUMUURYJUUIXJUURYIUUHKYHUUBUKU
      LZRUURYLUUKYMUULUURYJUUIXHUUSRUURYJUUIXIUUSRSUMYHXQOZYKYCYNYFUUTYJYBXJUUT
      YIXRKYHXQUKULZRUUTYLYDYMYEUUTYJYBXHUVARUUTYJYBXIUVARSUMYQXJNKLZIZXJEJZUCJ
      ZUDUEZOZUCUVBPZXJUVDFJZUPZOZFHPZUNZEUVBPZUNZYTNHIZXJUOIZYQUVOUQURXHXIUDUS
      UCEFXJNUOUTVAUVCYTUVNUVCUVQXJUVIGJZVBUEZOZGHPZFHPZMYTXQUVSOZGHPFHPUWBDXJU
      OUVBXQXJOUWCUVTFGHHXQXJUVSVCVDDFGVHVEUWBYTUVQUWAYTFHUVIHIZUVTYTGHUWDUVRHI
      MZUVTTXHXIVFZVFZNUVIUVRVFZVFZOZYTUWEXJUWGUVSUWIXJUWGOZUWEUWKBCXHXIUOUOVGV
      IZVJUVIUVRVKVLUWJTNOZUWFUWHOZMYTTUWFNUWHVMXHXIVNZVOUWMYTUWNUWMTNUFYTVTYTT
      NVPWAVQVRVSWBWCUHVRUVMYTEUVBUVDUVBIZUVHYTUVLUWPUVGYTUCUVBUWPUVEUVBIZMZUVG
      UWGTUVDUVEVFZVFZOZYTUWRXJUWGUVFUWTUWKUWRUWLVJUVDUVEUVBUVBVGVLUXAUWRYTUXAU
      WRXHUVBIZXIUVBIZMZYTUXATTOZUWFUWSOZMUWRUXDUQZTUWFTUWSVMUWOVOUXFUXGUXEUXFX
      HUVDOZXIUVEOZMZUXGXHXIUVDUVEBWDCWDVOUXJUWPUXBUWQUXCUXJUVDXHUVBUXJBEUXHUXI
      WEWFWGUXJUVEXIUVBUXJCUCUXHUXIWHWFWGSVRUHVRUXBYRUXCYSUVBYPXHUVPUVBYPWKURNW
      IWJZWLUVBYPXIUXKWLWMVSWNWOWBUWPUVKYTFHUVKYTQUWPUWDMUVKXJUVJUFYTEFBCWPYTXJ
      UVJVPWAVJWBWQWCWRVRUUABCWSWTVQXSXTYGUQYAXSXLYCXPYFXSXKYBXJAXRKXBZRXSXNYDX
      OYEXSXKYBXHUXLRXSXKYBXIUXLRSUMUHXAXCXDXEXF $.

    $d N j u v $.
    $( Lemma for ~ goalr (induction step).  (Contributed by AV,
       22-Oct-2023.) $)
    goalrlem $p |- ( N e. _om
                  -> ( ( A.g i a e. ( Fmla ` suc N ) -> a e. ( Fmla ` suc N ) )
                       -> ( A.g i a e. ( Fmla ` suc suc N )
                            -> a e. ( Fmla ` suc suc N ) ) ) ) $=
      ( vu vv vj com wcel cv cgol csuc wi wa wceq wrex cvv c2o adantr rexlimdva
      cop cfmla cfv cgna co wo wb peano2 df-goal opex eqeltri isfmlasuc sylancl
      wss fmlasssuc syl sseld com12 imim2i com23 impcom wne gonanegoal eqneqall
      mpi eqcoms a1i eqeq12i 2oex opth bitri weq vex biimtrdi impcomd simplbiim
      eleq1w jaod sylbid ex ) BGHZCIZAIZJZBKZUAUBZHZWAWEHZLZWCWDKUAUBZHZWAWIHZL
      VTWHMZWJWFWCDIZEIZUCUDZNZEWEOZWCWMFIZJZNZFGOZUEZDWEOZUEZWKVTWJXDUFZWHVTWD
      GHZWCPHXEBUGZWCQWBWATZTZPWAWBUHZQXHUIUJEDFWCWDPUKULRWLWFWKXCWHVTWFWKLWHWF
      VTWKWGVTWKLZWFVTWGWKVTWEWIWAVTXFWEWIUMXGWDUNUOUPUQZURUSUTVTXCWKLWHVTXBWKD
      WEVTWMWEHZMZWQWKXAXNWPWKEWEWPWKLXNWNWEHMWKWOWCWOWCNWOWCVAWKCADEVBWKWOWCVC
      VDVEVFSXNWTWKFGXNWTWKLWRGHWTXNWKWTQQNZXHWRWMTZNZXNWKLZWTXIQXPTZNXOXQMWCXI
      WSXSXJWMWRUHVGQXHQXPVHWBWAUIVIVJXQAFVKCDVKZXRWBWAWRWMAVLCVLVIXTXMVTWKXTXM
      WGXKXMWGUFWMWADCWEVPVEXLVMVNVOVOUQRSVQSRVQVRVS $.

    $d N n $.  $d a i n x $.  $d a i x y $.  $d a i j k u v x $.
    $( If the "Godel-set of universal quantification" applied to a class is a
       Godel formula, the class is also a Godel formula.  Remark:  The reverse
       is not valid for ` A ` being of the same height as the "Godel-set of
       universal quantification".  (Contributed by AV, 22-Oct-2023.) $)
    goalr $p |- ( ( N e. _om /\ A.g i a e. ( Fmla ` N ) )
                  -> a e. ( Fmla ` N ) ) $=
      ( vu vv vk vj com wcel cv cfmla cfv wa c0 wceq wrex wi eleq2d c2o cop wne
      vn vx vy cgol goaln0 adantl csuc nnsuc suceq fveq2d imbi12d cgna co wo wb
      cvv peano1 df-goal opex eqeltri isfmlasuc mp2an cgoe eqeq1 2rexbidv fmla0
      elrab2 a1i goel eqeq12d 2oex opth 2on0 eqneqall mpi adantr sylbi biimtrdi
      rexlimdva rexlimiv simplbiim gonanegoal eqcoms vex eleq1w fmlasssuc ax-mp
      eqeq12i wss sseli com12 biimtrid jaod jaoi goalrlem finds fveq2 rexlimiva
      mpbird syl impancom mpd ) BHIZCJZAJZUEZBKLZIZMBNUAZXEXHIZXIXJXDXEABUFUGXD
      XJXIXKXDXJMBUBJZUHZOZUBHPXIXKQZUBBUIXNXOUBHXLHIZXNMXOXGXMKLZIZXEXQIZQZXPX
      TXNXGUCJZUHZKLZIZXEYCIZQXGNUHZKLZIZXEYGIZQXGUDJZUHZKLZIZXEYLIZQXGYKUHZKLZ
      IZXEYPIZQXTUCUDXLYANOZYDYHYEYIYSYCYGXGYSYBYFKYANUJUKZRYSYCYGXEYTRULYAYJOZ
      YDYMYEYNUUAYCYLXGUUAYBYKKYAYJUJUKZRUUAYCYLXEUUBRULYAYKOZYDYQYEYRUUCYCYPXG
      UUCYBYOKYAYKUJUKZRUUCYCYPXEUUDRULYAXLOZYDXRYEXSUUEYCXQXGUUEYBXMKYAXLUJUKZ
      RUUEYCXQXEUUFRULYHXGNKLZIZXGDJZEJZUMUNZOZEUUGPZXGUUIFJZUEZOZFHPZUOZDUUGPZ
      UOZYINHIZXGUQIZYHUUTUPURXGSXFXETZTZUQXEXFUSZSUVCUTVAEDFXGNUQVBVCUUHYIUUSU
      UHUVBXGUUNGJZVDUNZOZGHPZFHPZYIYAUVGOZGHPFHPUVJUCXGUQUUGYAXGOUVKUVHFGHHYAX
      GUVGVEVFUCFGVGVHUVIYIFHUUNHIZUVHYIGHUVLUVFHIMZUVHUVDNUUNUVFTZTZOZYIUVMXGU
      VDUVGUVOXGUVDOUVMUVEVIUUNUVFVJVKUVPSNOZUVCUVNOZMYISUVCNUVNVLXFXEUTZVMUVQY
      IUVRUVQSNUAYIVNYISNVOVPVQVRVSVTWAWBUURYIDUUGUUIUUGIZUUMYIUUQUVTUULYIEUUGU
      ULYIQUVTUUJUUGIMYIUUKXGUUKXGOUUKXGUAYICADEWCYIUUKXGVOVPWDVIVTUVTUUPYIFHUU
      PUVDSUUNUUITZTZOZUVTUVLMYIXGUVDUUOUWBUVEUUIUUNUSWIUVTUWCYIQUVLUWCUVTYIUWC
      SSOUVCUWAOZUVTYIQZSUVCSUWAVLUVSVMUWDXFUUNOXEUUIOUWEXFXEUUNUUIAWECWEVMUWEU
      UIXEUUIXEOUVTXEUUGIYIDCUUGWFUUGYGXEUVAUUGYGWJURNWGWHWKVSWDWBWBWLVQWMVTWNW
      AWOVRAYJCWPWQVQXNXOXTUPXPXNXIXRXKXSXNXHXQXGBXMKWRZRXNXHXQXEUWFRULUGWTWSXA
      XBXC $.
  $}

  ${
    $d i j k u v x $.
    $( The set of valid Godel formulas of height 0 is disjoint with the
       formulas constructed from Godel-sets for the Sheffer stroke NAND and
       Godel-set of universal quantification.  (Contributed by AV,
       20-Oct-2023.) $)
    fmla0disjsuc $p |- ( ( Fmla ` (/) ) i^i { x | E. u e. ( Fmla ` (/) )
                                       ( E. v e. ( Fmla ` (/) ) x = ( u |g v )
                                      \/ E. i e. _om x = A.g i u ) } ) = (/) $=
      ( vj vk c0 cv wceq wrex com wo cab wa wn wcel wral cop c1o c2o cfmla cgna
      cfv co cgol cin cgoe cvv crab fmla0 rabab eqtri ineq1i inab eqeq2d nesymi
      goel 1n0 intnanr gonafv el2v eqeq2i opex opth bitri mtbir mtbiri biimtrdi
      0ex eqeq1 adantr ralrimivw 2on0 orci notbii ianor mpbir df-goal ralrimiva
      imp bitrdi ralnex anbi12i ioran bitr4i ralbii sylib ex rexlimdva rexlimiv
      jca imori abf ) GUAUCZAHZCHZBHZUBUDZIZBWNJZWOWPDHZUEZIZDKJZLZCWNJZAMZUFWO
      EHZFHZUGUDZIZFKJZEKJZAMZXGUFZGWNXNXGWNXMAUHUIXNAEFUJXMAUKULUMXOXMXFNZAMGX
      MXFAUNXPAXPOXMOXFOZLXMXQXLXQEKXHKPZXKXQFKXRXIKPNZXKXQXSXKNZWSOZBWNQZXCOZD
      KQZNZCWNQZXQXTYECWNXTWPWNPZNZYBYDYHYABWNXTYAYGXSXKYAXSXKWOGXHXIRZRZIZYAXS
      XJYJWOXHXIUQUOZYKWSYJWRIZYMGSIZYIWPWQRZIZNZYNYPSGURUPUSYMYJSYORZIYQWRYRYJ
      WRYRICBWPWQUHUHUTVAVBGYISYOVIXHXIVCZVDVEVFWOYJWRVJVGVHVTVKVLYHYCDKYHYCXAK
      PXTYCYGXSXKYCXSXKYKYCYLYKXCYJTXAWPRZRZIZUUBOZGTIZOZYIYTIZOZLZUUEUUGTGVMUP
      VNUUCUUDUUFNZOUUHUUBUUIGYITYTVIYSVDVOUUDUUFVPVEVQYKXCYJXBIUUBWOYJXBVJXBUU
      AYJWPXAVRVBWAVGVHVTVKVKVSWKVSYFXEOZCWNQXQYEUUJCWNYEWTOZXDOZNUUJYBUUKYDUUL
      WSBWNWBXCDKWBWCWTXDWDWEWFXECWNWBVEWGWHWIWJWLXMXFVPVQWMULUL $.
  $}

  ${
    $d N a b f i j u v $.  $d N f i u v x $.
    $( The valid Godel formulas of height ` ( N + 1 ) ` is disjoint with the
       difference ` ( ( Fmla `` suc suc N ) \ ( Fmla `` suc N ) ) ` , expressed
       by formulas constructed from Godel-sets for the Sheffer stroke NAND and
       Godel-set of universal quantification based on the valid Godel formulas
       of height ` ( N + 1 ) ` .  (Contributed by AV, 20-Oct-2023.) $)
    fmlasucdisj $p |- ( N e. _om -> ( ( Fmla ` suc N ) i^i
               { x | ( E. u e. ( ( Fmla ` suc N ) \ ( Fmla ` N ) )
                          ( E. v e. ( Fmla ` suc N ) x = ( u |g v )
                         \/ E. i e. _om x = A.g i u )
                   \/ E. u e. ( Fmla ` N )
                            E. v e. ( ( Fmla ` suc N ) \ ( Fmla ` N ) )
                               x = ( u |g v ) ) } ) = (/) ) $=
      ( va vb vj com wcel cv wn wceq wrex wo wral wa ralrimivw notbid ralbidv
      vf csuc cfmla cfv cgna co cgol cdif cab cin c0 vex eqeq1 rexbidv 2rexbidv
      orbi12d elab gonar elndif adantr intnanrd syl ex con2d impl c1o elneeldif
      cop necomd ancoms neneqd orcd ianor opth xchnxbir sylibr olcd gonafv el2v
      wne cvv eqeq12i 1oex opex bitri ralrimiva adantl gonanegoal neii sylanbrc
      a1i r19.26 jca eleq1 anbi12d syl5ibrcom rexlimdva imp nesymi 2oex df-goal
      goalr c2o wb eqcoms syl5ibcom jaod intnand sylnibr isfmlasuc ioran ralnex
      elvd anbi12i bitr4i ralbii bitr2i anbi2i bitrdi sylibrd biimtrid ralrimiv
      disjr ) EIJZUAKZEUBUCUDZJZLZUAAKZCKZBKZUEUFZMZBYFNZYIYJDKZUGZMZDINZOZCYFE
      UCUDZUHZNZYMBUUANCYTNZOZAUIZPYFUUEUJUKMYDYHUAUUEYEUUEJYEYLMZBYFNZYEYPMZDI
      NZOZCUUANZUUFBUUANZCYTNZOZYDYHUUDUUNAYEUAULYIYEMZUUBUUKUUCUUMUUOYSUUJCUUA
      UUOYNUUGYRUUIUUOYMUUFBYFYIYEYLUMZUNUUOYQUUHDIYIYEYPUMUNUPUNUUOYMUUFCBYTUU
      AUUPUOUPUQYDUUNYEYTJZLZYEFKZGKZUEUFZMZLZGYTPZYEUUSHKZUGZMZLZHIPZQZFYTPZQZ
      YHYDUUKUVLUUMYDUUJUVLCUUAYDYJUUAJZQZUUGUVLUUIUVNUUFUVLBYFUVNYKYFJZQZUVLUU
      FYLYTJZLZYLUVAMZLZGYTPZYLUVFMZLZHIPZQZFYTPZQZUVPUVRUWFYDUVMUVOUVRYDUVQUVM
      UVOQZYDUVQUWHLZYDUVQQZYJYTJZYKYTJZQZUWIECBURZUWMUVMUVOUWKUVMLZUWLYJYTYFUS
      ZUTVAVBVCVDVEUVPUWAFYTPZUWDFYTPZUWFUVNUWQUVOUVMUWQYDUVMUWAFYTUVMUUSYTJZQZ
      UVTGYTUWTVFVFMZLZYJYKVHZUUSUUTVHZMZLZOZUVTUWTUXFUXBUWTYJUUSMZLZYKUUTMZLZO
      ZUXFUWTUXIUXKUWTYJUUSUWSUVMYJUUSVTUWSUVMQUUSYJYTYFUUSYJVGVIVJVKZVLUXHUXJQ
      UXLUXEUXHUXJVMYJYKUUSUUTCULZBULVNVOZVPVQUXAUXEQZUXGUVSUXAUXEVMUVSVFUXCVHZ
      VFUXDVHZMUXPYLUXQUVAUXRYLUXQMCBYJYKWAWAVRVSUVAUXRMFGUUSUUTWAWAVRVSWBVFUXC
      VFUXDWCYJYKWDVNWEZVOVPRWFWGUTUVPUWDFYTUVPUWCHIUWCUVPYLUVFFHCBWHWIZWKRRUWA
      UWDFYTWLZWJWMUUFUURUVRUVKUWFUUFUUQUVQYEYLYTWNSUUFUVJUWEFYTUUFUVDUWAUVIUWD
      UUFUVCUVTGYTUUFUVBUVSYEYLUVAUMSTUUFUVHUWCHIUUFUVGUWBYEYLUVFUMSTWOTWOWPWQU
      VNUUHUVLDIUVNYOIJZQZYPYTJZLZYPUVAMZLZGYTPZYPUVFMZLZHIPZQZFYTPZQZUUHUVLUYC
      UYEUYMUVNUYEUYBYDUVMUYEYDUYDUVMYDUYDUWOYDUYDQUWKUWODECXBUWPVBVCVDWRUTUYCU
      YHFYTPUYKFYTPZUYMUYCUYHFYTUYCUYGGYTUYGUYCUVAYPCDFGWHWSWKRRUVNUYOUYBUVMUYO
      YDUVMUYKFYTUWTUYJHIUWTXCXCMZLZYOYJVHZUVEUUSVHZMZLZOZUYJUWTVUAUYQUWTYOUVEM
      ZLZUXIOZVUAUWTUXIVUDUXMVQVUCUXHQVUEUYTVUCUXHVMYOYJUVEUUSDULUXNVNVOVPVQXCU
      YRVHZXCUYSVHZMZVUBUYIUYPUYTQVUBVUHUYPUYTVMXCUYRXCUYSWTYOYJWDVNVOYPVUFUVFV
      UGYJYOXAUUSUVEXAWBVOVPRWFWGUTUYHUYKFYTWLWJWMUYNUVLXDYPYEYPYEMZUYEUURUYMUV
      KVUIUYDUUQYPYEYTWNSVUIUYLUVJFYTVUIUYHUVDUYKUVIVUIUYGUVCGYTVUIUYFUVBYPYEUV
      AUMSTVUIUYJUVHHIVUIUYIUVGYPYEUVFUMSTWOTWOXEXFWQXGWQYDUULUVLCYTYDUWKQZUUFU
      VLBUUAVUJYKUUAJZQZUWGUUFUVLVULUVRUWFYDUWKVUKUVRYDUVQUWKVUKQZYDUVQVUMLZUWJ
      UWMVUNUWNUWMVUKUWKUWLVUKLUWKYKYTYFUSWGXHVBVCVDVEVULUWQUWRUWFVUKUWQVUJVUKU
      WAFYTVUKUVTGYTVUKUUTYTJZQZUXPUVSVUPUXEUXAVUPUXLUXFVUPUXKUXIVUPYKUUTVUOVUK
      YKUUTVTVUOVUKQUUTYKYTYFUUTYKVGVIVJVKVQUXOVPXHUXSXIWFRWGVULUWDFYTVULUWCHIU
      WCVULUXTWKRRUYAWJWMUWGUVLXDYLYEYLYEMZUVRUURUWFUVKVUQUVQUUQYLYEYTWNSVUQUWE
      UVJFYTVUQUWAUVDUWDUVIVUQUVTUVCGYTVUQUVSUVBYLYEUVAUMSTVUQUWCUVHHIVUQUWBUVG
      YLYEUVFUMSTWOTWOXEXFWQWQXGYDYHUUQUVBGYTNZUVGHINZOZFYTNZOZLZUVLYDYGVVBYDYG
      VVBXDUAGFHYEEWAXJXMSVVCUURVVALZQUVLUUQVVAXKVVDUVKUURUVKVUTLZFYTPVVDUVJVVE
      FYTUVJVURLZVUSLZQVVEUVDVVFUVIVVGUVBGYTXLUVGHIXLXNVURVUSXKXOXPVUTFYTXLXQXR
      WEXSXTYAYBUAYFUUEYCVP $.
  $}

  ${
    $d E n $.  $d M n $.  $d N n $.  $d V n $.  $d W n $.
    $( The domain of the satisfaction predicate as function over wff codes in
       any model ` M ` and any binary relation ` E ` on ` M ` for a natural
       number ` N ` is the set of valid Godel formulas of height ` N ` .
       (Contributed by AV, 13-Oct-2023.) $)
    satfdmfmla $p |- ( ( M e. V /\ E e. W /\ N e. _om )
                       -> dom ( ( M Sat E ) ` N ) = ( Fmla ` N ) ) $=
      ( vn wcel com csat co cfv cdm c0 wceq wa cvv 0ex syl fveq2 dmeqd cfmla cv
      w3a wral pm3.2i jctr 3adant3 satfdm wi eqeq12d rspcv 3ad2ant3 mpd elelsuc
      csuc fmlafv eqtr4d ) BDGZAEGZCHGZUCZCBAIJZKZLZCMMIJZKZLZCUAKZVAFUBZVBKZLZ
      VIVEKZLZNZFHUDZVDVGNZVAURUSOZMPGZVROZOZVOURUSVTUTVQVSVRVRQQUEUFUGFAMBMDEP
      PUHRUTURVOVPUIUSVNVPFCHVICNZVKVDVMVGWAVJVCVICVBSTWAVLVFVICVESTUJUKULUMVAC
      HUOGZVHVGNUTURWBUSCHUNULCUPRUQ $.
  $}

  $( Lemma for ~ satffunlem1lem1 and ~ satffunlem2lem1 .  (Contributed by AV,
     27-Oct-2023.) $)
  satffunlem $p |- ( ( ( Fun Z /\ ( s e. Z /\ r e. Z )
                                /\ ( u e. Z /\ v e. Z ) )
             /\ ( x = ( ( 1st ` s ) |g ( 1st ` r ) )
                  /\ y = ( ( M ^m _om ) \ ( ( 2nd ` s ) i^i ( 2nd ` r ) ) ) )
             /\ ( x = ( ( 1st ` u ) |g ( 1st ` v ) )
                  /\ w = ( ( M ^m _om ) \ ( ( 2nd ` u ) i^i ( 2nd ` v ) ) ) ) )
                      -> y = w ) $=
    ( cv wcel wa c1st cfv wceq c2nd wi c1o cop cvv wfun w3a cgna co com cin weq
    cmap cdif eqtr2 fvex gonafv mp2an eqeq12i 1oex opex opth anbi2i funfv1st2nd
    3bitri ex anim12d fveq2 eqcoms adantr eqeq1d adantl anbi12d anbi1d ad2ant2r
    ad2ant2l ineq12d biimtrdi com12 syl2and expd 3imp1 difeq2d wb eqeq12 mpbird
    a1i exp43 adantld biimtrid syl5 com35 impd com24 3imp ) GUAZHJZGKZIJZGKZLZE
    JZGKZDJZGKZLZUBZAJZWLMNZWNMNZUCUDZOZBJZFUEUHUDZWLPNZWNPNZUFZUIZOZLXCWQMNZWS
    MNZUCUDZOZCJZXIWQPNZWSPNZUFZUIZOZLZBCUGZXBXGXNYEYFQXBYEXNXGYFXBXRYDXNXGYFQQ
    XBXRXGXNYDYFXBXRXGXNYDYFQQZXRXGLXQXFOZXBYGXCXQXFUJYHRROZXOXDOZXPXEOZLZLZXBY
    GYHRXOXPSZSZRXDXESZSZOYIYNYPOZLYMXQYOXFYQXOTKXPTKXQYOOWQMUKZWSMUKZXOXPTTULU
    MXDTKXETKXFYQOWLMUKWNMUKXDXETTULUMUNRYNRYPUOXOXPUPUQYRYLYIXOXPXDXEYSYTUQURU
    TXBYLYGYIXBYLXNYDYFXBYLLZXNYDLZLYFXMYCOZUUAUUCUUBUUAXLYBXIWKWPXAYLXLYBOZWKW
    PXAYLUUDQZWKWPXDGNZXJOZXEGNZXKOZLZXAXOGNZXTOZXPGNZYAOZLZUUEWKWMUUGWOUUIWKWM
    UUGGWLUSVAWKWOUUIGWNUSVAVBWKWRUULWTUUNWKWRUULGWQUSVAWKWTUUNGWSUSVAVBUUJUUOL
    ZUUEQWKYLUUPUUDYLUUPUUKXJOZUUMXKOZLZUUOLZUUDYLUUJUUSUUOYLUUGUUQUUIUURYLUUFU
    UKXJYJUUFUUKOZYKUVAXDXOXDXOGVCVDVEVFYLUUHUUMXKYKUUHUUMOZYJUVBXEXPXEXPGVCVDV
    GVFVHVIUUTXJXTXKYAUUQUULXJXTOUURUUNUUKXJXTUJVJUURUUNXKYAOUUQUULUUMXKYAUJVKV
    LVMVNWBVOVPVQVRVEUUBYFUUCVSUUAXHXMXSYCVTVGWAWCWDWEWFVPWGWHWIWHWJ $.

  ${
    $d E i j s u x y z $.  $d E i r s u x y z $.  $d E j s u v x y z $.
    $d M i j s u x y z $.  $d M i r s u x y z $.  $d M j s u v x y z $.
    $d N i j s u x y z $.  $d N i r s u x y z $.  $d N j s u v x y z $.
    $d f i j s u y z $.  $d f i r s u y z $.  $d f j s u v y z $.
    $d i j k s u y z $.  $d k r s u v y z $.
    $( Lemma for ~ satffunlem1 .  (Contributed by AV, 17-Oct-2023.) $)
    satffunlem1lem1 $p |- ( Fun ( ( M Sat E ) ` N )
                        -> Fun { <. x , y >. | E. u e. ( ( M Sat E ) ` N )
             ( E. v e. ( ( M Sat E ) ` N ) ( x = ( ( 1st ` u ) |g ( 1st ` v ) )
                    /\ y = ( ( M ^m _om ) \ ( ( 2nd ` u ) i^i ( 2nd ` v ) ) ) )
            \/ E. i e. _om ( x = A.g i ( 1st ` u )
                    /\ y = { f e. ( M ^m _om ) | A. k e. M ( { <. i , k >. }
                      u. ( f |` ( _om \ { i } ) ) ) e. ( 2nd ` u ) } ) ) } ) $=
      ( cfv cv c1st wceq com wa cop wcel wi c2o vz vs vr vj csat wfun cgna cmap
      co c2nd cin cdif wrex cgol csn cres cun wral crab wmo wal copab oveqan12d
      wo fveq2 eqeq2d ineqan12d difeq2d anbi12d cbvrexdva simpr goaleq12d opeq1
      adantr sneqd sneq reseq2d uneq12d adantl eleq12d ralbidv rabbidv cbvrexvw
      orbi12d simp-4l anim1i ad2antrr satffunlem eqcomd syl3anc rexlimdva eqeq1
      w3a 3exp c1o df-goal cvv fvex gonafv eqeq12i 2oex opex opth wne 1one2o wn
      mp2an df-ne pm2.21 sylbi ax-mp eqcoms biimtrdi impd a1i jaod com23 wb vex
      com12 anbi2i 3bitri bitrdi funfv1st2nd ex fveqeq2 eqtr2 eqeq12 syl5ibrcom
      simpl exp4b syl com24 impcom com13 syl6 imp anbi2d rexbidv sylibr adantld
      syld sylbid com34 biimtrid alrimivv mo4 alrimiv funopab ) JIHUEUIKZUFZALZ
      DLZMKZCLZMKZUGUIZNZBLZIOUHUIZUUMUJKZUUOUJKZUKZULZNZPZCUUJUMZUULUUNFLZUNZN
      ZUUSUVHGLZQZUOZELZOUVHUOZULZUPZUQZUVARZGIURZEUUTUSZNZPZFOUMZVDZDUUJUMZBUT
      ZAVAUWFABVBUFUUKUWGAUUKUWFUURUALZUVDNZPZCUUJUMZUVJUWHUWANZPZFOUMZVDZDUUJU
      MZPUUSUWHNZSZUAVABVAUWGUUKUWRBUAUUKUWFUWPUWQUWFUULUBLZMKZUCLZMKZUGUIZNZUU
      SUUTUWSUJKZUXAUJKZUKZULZNZPZUCUUJUMZUULUWTUDLZUNZNZUUSUXLUVKQZUOZUVNOUXLU
      OZULZUPZUQZUXERZGIURZEUUTUSZNZPZUDOUMZVDZUBUUJUMUUKUWPUWQSZUWEUYGDUBUUJUU
      MUWSNZUVGUXKUWDUYFUYIUVFUXJCUCUUJUYIUUOUXANZPZUURUXDUVEUXIUYKUUQUXCUULUYI
      UYJUUNUWTUUPUXBUGUUMUWSMVEZUUOUXAMVEVCVFUYKUVDUXHUUSUYKUVCUXGUUTUYIUYJUVA
      UXEUVBUXFUUMUWSUJVEZUUOUXAUJVEVGVHVFVIVJUYIUWCUYEFUDOUYIUVHUXLNZPZUVJUXNU
      WBUYDUYOUVIUXMUULUYOUUNUWTUVHUXLUYIUYNVKUYIUUNUWTNZUYNUYLVNVLVFUYOUWAUYCU
      USUYOUVTUYBEUUTUYOUVSUYAGIUYOUVRUXTUVAUXEUYNUVRUXTNUYIUYNUVMUXPUVQUXSUYNU
      VLUXOUVHUXLUVKVMVOUYNUVPUXRUVNUYNUVOUXQOUVHUXLVPVHVQVRVSUYIUVAUXENZUYNUYM
      VNVTWAWBVFVIVJWDWCUUKUYGUYHUBUUJUUKUWSUUJRZPZUXKUYHUYFUYSUXJUYHUCUUJUYSUX
      AUUJRZPZUWPUXJUWQVUAUWOUXJUWQSZDUUJVUAUUMUUJRZPZUWKVUBUWNVUDUWJVUBCUUJVUD
      UUOUUJRZPUUKVUCVUEPZUYRUYTPZUWJVUBSUUKUYRUYTVUCVUEWEVUDVUCVUEVUAVUCVKWFVU
      AVUGVUCVUEUYSUYRUYTUUKUYRVKWFWGUUKVUFVUGWMZUWJUXJUWQVUHUWJUXJWMUWHUUSAUAB
      UCUBIUUJDCWHWIWNWJWKVUDUWMVUBFOUWMVUBSVUDUVHORZPUVJVUBUWLUVJUXDUXIUWQUVJU
      XDUVIUXCNZUXIUWQSZUULUVIUXCWLVUJTUVHUUNQZQZWOUWTUXBQZQZNZVUKUVIVUMUXCVUOU
      UNUVHWPZUWTWQRUXBWQRUXCVUONUWSMWRUXAMWRUWTUXBWQWQWSXGWTVUPTWONZVULVUNNZPV
      UKTVULWOVUNXAUVHUUNXBZXCVURVUKVUSVUKWOTWOTXDZWOTNZVUKSZXEVVAVVBXFZVVCWOTX
      HZVVBVUKXIXJXKXLVNXJXJXMXNVNXOWKXPWKXQWKUYSUYEUYHUDOUYSUXLORZPZUWPUYEUWQV
      VGUWOUYEUWQSZDUUJVVGVUCPZUWKVVHUWNVVIUWJVVHCUUJUWJVVHSVVIVUEPUURVVHUWIUYE
      UURUWQUXNUURUWQSUYDUXNUURUXMUUQNZUWQUULUXMUUQWLVVJTUXLUWTQZQZWOUUNUUPQZQZ
      NZUWQUXMVVLUUQVVNUWTUXLWPZUUNWQRUUPWQRUUQVVNNUUMMWRZUUOMWRUUNUUPWQWQWSXGW
      TVVOVURVVKVVMNZPUWQTVVKWOVVMXAUXLUWTXBXCVURUWQVVRUWQWOTVVAVVBUWQSZXEVVAVV
      DVVSVVEVVBUWQXIXJXKXLVNXJXJXMVNXTVNXOWKVVIUWMVVHFOVVIVUIPZUVJUWLVVHVVTUVJ
      UYEUWLUWQVVTUVJUYEUWLUWQSZSVVTUVJPZUXNUYDVWAVWBUXNTTNZUYNUYPPZPZUYDVWASZU
      VJUXNVWEXRVVTUVJUXNUVIUXMNZVWEUULUVIUXMWLVWGVUMVVLNVWCVULVVKNZPVWEUVIVUMU
      XMVVLVUQVVPWTTVULTVVKXAVUTXCVWHVWDVWCUVHUUNUXLUWTFXSVVQXCYAYBYCVSVVIVWEVW
      FSVUIUVJVVIVWDVWFVWCVVGVUCVWDVWFSZUYSVUCVWISZVVFUUKUYRVWJUUKUYRUWTUUJKZUX
      ENZVWJUUKUYRVWLUUJUWSYDYEUUKVUCVWLVWIUUKVUCUUNUUJKUVANZVWLVWISUUKVUCVWMUU
      JUUMYDYEVWDVWLVWMVWFUYPUYNVWLVWMVWFSSUYPVWMVWLUYNVWFUYPVWMVWKUVANZVWLUYNV
      WFSZSUUNUWTUVAUUJYFVWNVWLVWOVWNVWLPUYQVWOVWKUVAUXEYGUYQUYNUYDUWLUWQUYQUYN
      PZUWQUYDUWLPUYCUWANVWPUYBUVTEUUTVWPUYAUVSGIVWPUXTUVRUXEUVAUYNUXTUVRNZUYQV
      WQUXLUVHUXLUVHNZUXPUVMUXSUVQVWRUXOUVLUXLUVHUVKVMVOVWRUXRUVPUVNVWRUXQUVOOU
      XLUVHVPVHVQVRXLVSVWPUVAUXEUYQUYNYJWIVTWAWBUUSUYCUWHUWAYHYIYKYLYEXMYMYNYOY
      PXQUUBYQVNYQUUAWGUUCXNYEUUDXNWKXPWKXQWKXPWKUUEXNUUFUWFUWPBUAUWQUWEUWODUUJ
      UWQUVGUWKUWDUWNUWQUVFUWJCUUJUWQUVEUWIUURUUSUWHUVDWLYRYSUWQUWCUWMFOUWQUWBU
      WLUVJUUSUWHUWAWLYRYSWDYSUUGYTUUHUWFABUUIYT $.
  $}

  ${
    $d E f g i u v x y $.  $d M f g i u v x y $.  $d V f g i u v x $.
    $d W f g i u v x $.  $d j x y $.
    $( Lemma 2 for ~ satffunlem1 .  (Contributed by AV, 23-Oct-2023.) $)
    satffunlem1lem2 $p |- ( ( M e. V /\ E e. W )
                         -> ( dom ( ( M Sat E ) ` (/) )
                          i^i dom { <. x , y >. | E. u e. ( ( M Sat E ) ` (/) )
           ( E. v e. ( ( M Sat E ) ` (/) ) ( x = ( ( 1st ` u ) |g ( 1st ` v ) )
                    /\ y = ( ( M ^m _om ) \ ( ( 2nd ` u ) i^i ( 2nd ` v ) ) ) )
          \/ E. i e. _om ( x = A.g i ( 1st ` u )
                    /\ y = { f e. ( M ^m _om ) | A. j e. M ( { <. i , j >. }
              u. ( f |` ( _om \ { i } ) ) ) e. ( 2nd ` u ) } ) ) } ) = (/) ) $=
      ( vg wcel wa c0 cfv cv wceq com wrex csat co cdm c1st cgna cmap c2nd cdif
      cin cgol cop csn cres cun wral crab wo copab cab peano1 satfdmfmla mp3an3
      cfmla cvv ovex difexi a1i ralrimiva rabex jca dmopab2rex syl wrel satfrel
      1stdm sylan w3a eqcomd adantr eleqtrrd wb oveq1 eqeq2d eqidd id goaleq12d
      rexbidv orbi12d adantl ad4ant13 oveq2 simpr rspcedvd rexlimdva orim1d imp
      ex wi releldm2 eleq2d bitr3d r19.41v eqcoms biimpa reximdv biimtrrid expd
      bitrd sylbid rexlimdv sylbird expimpd reximdva impbid abbidv fmla0disjsuc
      eqtrd ineq12d eqtrdi ) IJMZHKMZNZOIHUAUBPZUCZAQZDQZUDPZCQZUDPZUEUBZRZBQZI
      SUFUBZYFUGPZYHUGPUIZUHZRNCYCTYEYGFQZUJZRZYLYQGQUKULEQZSYQULUHUMUNYNMGIUOZ
      EYMUPZRNFSTUQDYCTABURUCZUIOVCPZYEYTLQZUEUBZRZLUUDTZYEYTYQUJZRZFSTZUQZEUUD
      TZAUSZUIOYBYDUUDUUCUUNXTYAOSMZYDUUDRUTHIOJKVAZVBZYBUUCYKCYCTZYSFSTZUQZDYC
      TZAUSZUUNYBYPVDMZCYCUOZUUBVDMZFSUOZNZDYCUOUUCUVBRYBUVGDYCYBYFYCMZNZUVDUVF
      UVIUVCCYCUVCUVIYHYCMZNZYMYOISUFVEZVFVGVHUVIUVEFSUVEUVIYQSMNUUAEYMUVLVIVGV
      HVJVHABCDYJYPYRUUBYCFSYCVDVDVKVLYBUVAUUMAYBUVAUUMYBUUTUUMDYCUVIUUTUUMUVIU
      UTNZUULYEYGUUEUEUBZRZLUUDTZUUSUQZEYGUUDUVIYGUUDMUUTUVIYGYDUUDYBYCVMZUVHYG
      YDMXTYAUUOUVRUTHIOJKVNVBZYFYCVOVPYBUUDYDRZUVHXTYAUUOUVTUTXTYAUUOVQYDUUDUU
      PVRVBZVSVTVSYTYGRZUULUVQWAUVMUWBUUHUVPUUKUUSUWBUUGUVOLUUDUWBUUFUVNYEYTYGU
      UEUEWBWCWGUWBUUJYSFSUWBUUIYRYEUWBYTYGYQYQUWBYQWDUWBWEWFWCWGWHWIUVIUUTUVQU
      VIUURUVPUUSUVIYKUVPCYCUVKYKUVPUVKYKNZUVOYKLYIUUDYBUVJYIUUDMUVHYKYBUVJNYIY
      DUUDYBUVRUVJYIYDMUVSYHYCVOVPYBUVTUVJUWAVSVTWJUUEYIRZUVOYKWAUWCUWDUVNYJYEU
      UEYIYGUEWKZWCWIUVKYKWLWMWQWNWOWPWMWQWNYBUULUVAEUUDYBYTUUDMZYGYTRZDYCTZUUL
      UVAWRYBYTYDMZUWHUWFYBUVRUWIUWHWAUVSDYCYTWSVLYBYDUUDYTUUQWTXAYBUWHUULUVAUW
      HUULNUWGUULNZDYCTYBUVAUWGUULDYCXBYBUWJUUTDYCUVIUWGUULUUTUVIUWGNZUULUVQUUT
      UWGUVQUULWAUVIUWGUVPUUHUUSUUKUWGUVOUUGLUUDUWGUVNUUFYEYGYTUUEUEWBWCWGUWGYS
      UUJFSUWGYRUUIYEUWGYGYTYQYQUWGYQWDUWGWEWFWCWGWHWIUWKUVPUURUUSUVIUVPUURWRZU
      WGYBUWLUVHYBUVOUURLUUDYBUUEUUDMZYIUUERZCYCTZUVOUURWRYBUWMUUEYDMZUWOYBUUDY
      DUUEYBYDUUDUUQVRWTYBUVRUWPUWOWAUVSCYCUUEWSVLXHYBUWOUVOUURUWOUVONUWNUVONZC
      YCTYBUURUWNUVOCYCXBYBUWQYKCYCUWQYKWRYBUWNUVOYKUWNUVNYJYEUVNYJRUUEYIUWEXCW
      CXDVGXEXFXGXIXJVSVSWOXKXLXMXFXGXKXJXNXOXQXRALEFXPXS $.
  $}

  ${
    $d A j s w y $.  $d A r s w y $.  $d B j s w y $.  $d B r s w y $.
    $d M i u $.  $d M u v $.  $d N i j s u w x y $.  $d N i r s u w x y $.
    $d N j s u v w x y $.  $d S i j s u w x y $.  $d S i r s u w x y $.
    $d S j s u v w x y $.  $d a i j s u $.  $d a j s u v $.  $d i j s u z $.
    $d r s u v w x y $.  $d v z $.
    satffunlem2lem1.s $e |- S = ( M Sat E ) $.
    satffunlem2lem1.a $e |- A = ( ( M ^m _om )
                              \ ( ( 2nd ` u ) i^i ( 2nd ` v ) ) ) $.
    satffunlem2lem1.b $e |- B = { a e. ( M ^m _om ) | A. z e. M
            ( { <. i , z >. } u. ( a |` ( _om \ { i } ) ) ) e. ( 2nd ` u ) } $.
    $( Lemma 1 for ~ satffunlem2 .  (Contributed by AV, 28-Oct-2023.) $)
    satffunlem2lem1 $p |- ( ( Fun ( S ` suc N ) /\ ( S ` N ) C_ ( S ` suc N ) )
                 -> Fun { <. x , y >. | ( E. u e. ( ( S ` suc N ) \ ( S ` N ) )
        ( E. v e. ( S ` suc N ) ( x = ( ( 1st ` u ) |g ( 1st ` v ) ) /\ y = A )
       \/ E. i e. _om ( x = A.g i ( 1st ` u ) /\ y = B ) )
                 \/ E. u e. ( S ` N ) E. v e. ( ( S ` suc N ) \ ( S ` N ) )
                       ( x = ( ( 1st ` u ) |g ( 1st ` v ) ) /\ y = A ) ) } ) $=
      ( wa wceq wi adantr vw vs vr vj csuc cfv wfun wss c1st cgna wrex cgol com
      cv co wo cdif wmo wal copab cmap c2nd cin cop csn cres cun wcel wral crab
      simpl fveq2d simpr oveq12d eqeq2d ineq12d difeq2d anbi12d cbvrexdva fveq2
      eqtrid goaleq12d eqeq2i opeq1 sneq reseq2d uneq12d adantl eleq12d ralbidv
      rabbidv bitrid orbi12d cbvrexvw oveqan12d ineqan12d orbi12i eldifi anim1i
      sneqd ad2antrr 3jca syl3an 3exp com23 rexlimdva eqeq1 c1o c2o fvex gonafv
      cvv mp2an df-goal eqeq12i opex opth sylbi biimtrdi a1i jaod ssel ad3antlr
      com12 impcom ad2antll jca rexlimdvva 2oex funfv1st2nd eqcomd impd simplll
      ex imp adantrd impancom anbi2d rexbidv sylibr id biimpi anim2i satffunlem
      w3a simp-5l 1oex 1one2o wn df-ne pm2.21 ax-mp simp-4l eqcoms rexlimivw wb
      wne vex anbi2i 3bitri bitrdi fveqeq2 eqtr2 eqtr4di syl5ibrcom exp4b com24
      eqeq12 syl com13 syl56 3syld adantld sylbid com34 simprl syl3anc rexlimdv
      exp32 expdimp rexlimdvv biimtrid alrimivv 2rexbidv mo4 alrimiv funopab )
      LUEHUFZUGZLHUFZUWHUHZQZAUNZEUNZUIUFZDUNZUIUFZUJUOZRZBUNZFRZQZDUWHUKZUWMUW
      OIUNZULZRZUWTGRZQZIUMUKZUPZEUWHUWJUQZUKZUXBDUXKUKZEUWJUKZUPZBURZAUSUXOABU
      TUGUWLUXPAUWLUXOUWSUAUNZFRZQZDUWHUKZUXFUXQGRZQZIUMUKZUPZEUXKUKZUXSDUXKUKZ
      EUWJUKZUPZQUWTUXQRZSZUAUSBUSUXPUWLUYJBUAUWLUXOUYHUYIUXOUWMUBUNZUIUFZUCUNZ
      UIUFZUJUOZRZUWTKUMVAUOZUYKVBUFZUYMVBUFZVCZUQZRZQZUCUWHUKZUWMUYLUDUNZULZRZ
      UWTVUECUNZVDZVEZMUNZUMVUEVEZUQZVFZVGZUYRVHZCKVIZMUYQVJZRZQZUDUMUKZUPZUBUX
      KUKZVUCUCUXKUKZUBUWJUKZUPUWLUYHUYISZUXLVVCUXNVVEUXJVVBEUBUXKUWNUYKRZUXCVU
      DUXIVVAVVGUXBVUCDUCUWHVVGUWPUYMRZQZUWSUYPUXAVUBVVIUWRUYOUWMVVIUWOUYLUWQUY
      NUJVVIUWNUYKUIVVGVVHVKZVLVVIUWPUYMUIVVGVVHVMZVLVNVOVVIFVUAUWTVVIFUYQUWNVB
      UFZUWPVBUFZVCZUQZVUAOVVIVVNUYTUYQVVIVVLUYRVVMUYSVVIUWNUYKVBVVJVLVVIUWPUYM
      VBVVKVLVPVQWAVOVRVSVVGUXHVUTIUDUMVVGUXDVUERZQZUXFVUGUXGVUSVVQUXEVUFUWMVVQ
      UWOUYLUXDVUEVVGVVPVMVVGUWOUYLRZVVPUWNUYKUIVTZTWBVOUXGUWTUXDVUHVDZVEZVUKUM
      UXDVEZUQZVFZVGZVVLVHZCKVIZMUYQVJZRVVQVUSGVWHUWTPWCVVQVWHVURUWTVVQVWGVUQMU
      YQVVQVWFVUPCKVVQVWEVUOVVLUYRVVPVWEVUORVVGVVPVWAVUJVWDVUNVVPVVTVUIUXDVUEVU
      HWDWTVVPVWCVUMVUKVVPVWBVULUMUXDVUEWEVQWFWGZWHVVGVVLUYRRZVVPUWNUYKVBVTZTWI
      WJWKVOWLVRVSWMWNUXMVVDEUBUWJVVGUXBVUCDUCUXKVVIUWSUYPUXAVUBVVIUWRUYOUWMVVG
      VVHUWOUYLUWQUYNUJVVSUWPUYMUIVTWOVOUXAUWTVVORVVIVUBFVVOUWTOWCVVIVVOVUAUWTV
      VIVVNUYTUYQVVGVVHVVLUYRVVMUYSVWKUWPUYMVBVTWPVQVOWLVRVSWNWQUWLVVCVVFVVEUWL
      VVBVVFUBUXKUWLUYKUXKVHZQZVUDVVFVVAVWMVUCVVFUCUWHVWMUYMUWHVHZQZUYHVUCUYIVW
      OUYEVUCUYISZUYGVWOUYDVWPEUXKVWOUWNUXKVHZQZUXTVWPUYCVWRUXSVWPDUWHVWRUWPUWH
      VHZQZVUCUXSUYIVWTVUCUXSUYIVWTUWIUYKUWHVHZVWNQZUWNUWHVHZVWSQZUUEZVUCVUCUXS
      UWSUXQVVORZQZUYIVWTUWIVXBVXDUWIUWKVWLVWNVWQVWSUUFVWOVXBVWQVWSVWMVXAVWNVWL
      VXAUWLUYKUWHUWJWRZWHWSZXAVWRVXCVWSVWQVXCVWOUWNUWHUWJWRZWHWSXBVUCUUAZUXRVX
      FUWSUXRVXFFVVOUXQOWCUUBUUCZABUADEKUWHUBUCUUDZXCXDXEXFVWRUYBVWPIUMUYBVWPSV
      WRUXDUMVHZQUXFVWPUYAVUCUXFUYIUYPUXFUYISVUBUYPUXFUYOUXERZUYIUWMUYOUXEXGVXO
      XHUYLUYNVDZVDZXIUXDUWOVDZVDZRZUYIUYOVXQUXEVXSUYLXLVHUYNXLVHUYOVXQRUYKUIXJ
      UYMUIXJUYLUYNXLXLXKXMUWOUXDXNZXOVXTXHXIRZVXPVXRRZQUYIXHVXPXIVXRUUGUYLUYNX
      PXQVYBUYIVYCXHXIUUQZVYBUYISZUUHVYDVYBUUIVYEXHXIUUJVYBUYIUUKXRUULZTXRXRXSZ
      TYDTXTXFYAXFVWOUXSVWPEDUWJUXKVWOUWNUWJVHZUWPUXKVHZQZQZVUCUXSUYIVYKVUCUXSU
      YIVYKVXEVUCVUCUXSVXGUYIVYKUWIVXBVXDUWIUWKVWLVWNVYJUUMVWOVXBVYJVXITVYKVXCV
      WSVYJVWOVXCVYHVWOVXCSVYIVWOVYHVXCUWKVYHVXCSZUWIVWLVWNUWJUWHUWNYBZYCYDTYEV
      YIVWSVWOVYHUWPUWHUWJWRZYFYGXBVXKVXLVXMXCXDXEYHYAXEXFVWMVUTVVFUDUMVWMVUEUM
      VHZQZUYHVUTUYIVYPUYEVUTUYISZUYGVYPUYDVYQEUXKVYPVWQQZUXTVYQUYCUXTVYQSVYRUX
      SVYQDUWHUWSVYQUXRVUTUWSUYIVUGUWSUYISVUSVUGUWSVUFUWRRZUYIUWMVUFUWRXGVYSXIV
      UEUYLVDZVDZXHUWOUWQVDZVDZRZUYIVUFWUAUWRWUCUYLVUEXNZUWOXLVHUWQXLVHUWRWUCRU
      WNUIXJZUWPUIXJUWOUWQXLXLXKXMXOWUDXIXHRZVYTWUBRZQUYIXIVYTXHWUBYIVUEUYLXPXQ
      WUGUYIWUHUYIXHXIVYFUUNTXRXRXSTYDTZUUOXTVYRUYBVYQIUMVYRVXNQZUXFUYAVYQWUJUX
      FVUTUYAUYIWUJUXFVUTUYAUYISZSWUJUXFQZVUGVUSWUKWULVUGXIXIRZVVPVVRQZQZVUSWUK
      SZUXFVUGWUOUUPWUJUXFVUGUXEVUFRZWUOUWMUXEVUFXGWUQVXSWUARWUMVXRVYTRZQWUOUXE
      VXSVUFWUAVYAWUEXOXIVXRXIVYTYIUXDUWOXPXQWURWUNWUMUXDUWOVUEUYLIUURWUFXQUUSU
      UTUVAWHVYRWUOWUPSVXNUXFVYRWUNWUPWUMVYPVWQWUNWUPSZVWMVWQWUSSZVYOUWLVWLWUTU
      WLVWLVXAUYLUWHUFZUYRRZWUTVWLVXASUWLVXHXTUWIVXAWVBSUWKUWIVXAWVBUWHUYKYJYNT
      UWLVWQWVBWUSVWQVXCUWLUWOUWHUFVVLRZWVBWUSSVXJUWIVXCWVCSUWKUWIVXCWVCUWHUWNY
      JYNTWUNWVBWVCWUPVVRVVPWVBWVCWUPSSVVRWVCWVBVVPWUPVVRWVCWVAVVLRZWVBVVPWUPSZ
      SUWOUYLVVLUWHUVBWVDWVBWVEWVDWVBQVWJWVEWVAVVLUYRUVCVWJVVPVUSUYAUYIVWJVVPQZ
      UYIVUSUYAQVURGRWVFVURVWHGWVFVUQVWGMUYQWVFVUPVWFCKWVFVUOVWEUYRVVLVVPVUOVWE
      RVWJVVPVWEVUOVWIYKWHWVFVVLUYRVWJVVPVKYKWIWJWKPUVDUWTVURUXQGUVHUVEUVFUVIYN
      XSUVGYEUVJUVKXEUVLYOTYOUVMXAUVNYLYNUVOYLXFYAXFVYPUYFVYQEUWJVYPVYHQZUXSVYQ
      DUXKUXSVYQSWVGVYIQWUIXTXFXFYAXEXFYAXFUWLVUCVVFUBUCUWJUXKUWLUYKUWJVHZUYMUX
      KVHZQZQZVUCVVFWVKVUCQZUYEUYIUYGWVLUYDUYIEUXKWVLVWQQZUXTUYIUYCWVMUXSUYIDUW
      HWVLVWQVWSUXSUYISZWVKVWQVWSQZVUCWVNWVKWVOQZVUCUXSUYIWVPVUCUXSQZQVXEVUCVXG
      UYIWVPVXEWVQWVPUWIVXBVXDUWIUWKWVJWVOYMWVKVXBWVOWVKVXAVWNUWLWVJVXAUWKWVJVX
      ASUWIUWKWVHVXAWVIUWJUWHUYKYBYPWHYOWVIVWNUWLWVHUYMUWHUWJWRYFYGZTWVOVXDWVKV
      WQVXCVWSVXJWSWHXBTWVPVUCUXSUVPUXSVXGWVPVUCVXLYFVXMUVQUVSYQUVTUVRWVMUYBUYI
      IUMVUCUYBUYISZWVKVWQVXNUYPWVSVUBUYPUXFUYIUYAVYGYPTYCXFYAXFWVLUXSUYIEDUWJU
      XKWVKVYJVUCWVNWVKVYJQZVUCUXSUYIWVTVXEVUCVUCUXSVXGUYIWVTUWIVXBVXDUWIUWKWVJ
      VYJYMWVKVXBVYJWVRTWVTVXCVWSVYJWVKVXCVYHWVKVXCSVYIWVKVYHVXCUWLVYLWVJUWKVYL
      UWIVYMWHTYDTYEVYIVWSWVKVYHVYNYFYGXBVXKVXLVXMXCXDYQUWAYAYNYHYAUWBYLUWCUXOU
      YHBUAUYIUXLUYEUXNUYGUYIUXJUYDEUXKUYIUXCUXTUXIUYCUYIUXBUXSDUWHUYIUXAUXRUWS
      UWTUXQFXGYRZYSUYIUXHUYBIUMUYIUXGUYAUXFUWTUXQGXGYRYSWMYSUYIUXBUXSEDUWJUXKW
      WAUWDWMUWEYTUWFUXOABUWGYT $.
  $}

  ${
    $d A x y z $.  $d B x y z $.  $d C x y z $.  $d D x y z $.  $d I i x y z $.
    $d S u v x y z $.  $d U u v x y z $.  $d W z $.  $d X z $.
    $( The domain of an ordered pair class abstraction with three nested
       restricted existential quantifiers with differences.  (Contributed by
       AV, 25-Oct-2023.) $)
    dmopab3rexdif $p |- ( ( A. u e. U ( A. v e. U B e. X /\ A. i e. I D e. W )
             /\ S C_ U ) -> dom { <. x , y >. | ( E. u e. ( U \ S )
               ( E. v e. U ( x = A /\ y = B ) \/ E. i e. I ( x = C /\ y = D ) )
              \/ E. u e. S E. v e. ( U \ S ) ( x = A /\ y = B ) ) }
             = { x | ( E. u e. ( U \ S ) ( E. v e. U x = A \/ E. i e. I x = C )
                    \/ E. u e. S E. v e. ( U \ S ) x = A ) } ) $=
      ( wral wa wceq wrex wo wex vz wcel wss cdif copab cdm cab rexcom4 orbi12i
      cv 19.43 bitr4i rexbii bitri wb wi difssd ssralv syl impcom simpl exlimiv
      elisset bicomd exbidv syl5ibrcom impbid2 ralrexbid adantr orbi12d adantrd
      ibar adantl ralimdv syld bitr3id cvv weq eqeq1 rexbidv 2rexbidv dmopabelb
      anbi1d elv vex elab 3bitr4g eqrdv ) FNUBZCJOZHMUBZKLOZPZDJOZIJUCZPZUAAUJZ
      EQZBUJZFQZPZCJRZWQGQZWSHQZPZKLRZSZDJIUDZRZXACXHRDIRZSZABUEUFZWRCJRZXCKLRZ
      SZDXHRZWRCXHRDIRZSZAUGZWPUAUJZEQZWTPZCJRZXTGQZXDPZKLRZSZDXHRZYBCXHRZDIRZS
      ZBTZYACJRZYDKLRZSZDXHRZYACXHRZDIRZSZXTXLUBZXTXSUBYLYBBTZCJRZYEBTZKLRZSZDX
      HRZUUACXHRZDIRZSZWPYSUUIYHBTZYJBTZSYLUUFUUJUUHUUKUUFYGBTZDXHRUUJUUEUULDXH
      UUEYCBTZYFBTZSUULUUBUUMUUDUUNYBCBJUHYEKBLUHUIYCYFBUKULUMYGDBXHUHUNUUHYIBT
      ZDIRUUKUUGUUODIYBCBXHUHUMYIDBIUHUNUIYHYJBUKULWPUUFYPUUHYRWPWMDXHOZUUFYPUO
      WOWNUUPWOXHJUCZWNUUPUPWOJIUQZWMDXHJURUSUTWMUUEYODXHWMUUBYMUUDYNWJUUBYMUOW
      LWIUUAYACJWIUUAYAYBYABYAWTVAVBWIUUAYAWTBTBFNVCYAYBWTBYAWTYBYAWTVLVDVEVFVG
      ZVHVIWLUUDYNUOWJWKUUCYDKLWKUUCYDYEYDBYDXDVAVBWKUUCYDXDBTBHMVCYDYEXDBYDXDY
      EYDXDVLVDVEVFVGVHVMVJVHUSWPWICXHOZDIOZUUHYRUOWOWNUVAWOWNWMDIOUVAWMDIJURWO
      WMUUTDIWOWJUUTWLWOUUQWJUUTUPUURWICXHJURUSVKVNVOUTUUTUUGYQDIWIUUAYACXHUUSV
      HVHUSVJVPYTYLUOUAXKYKABVQXTAUAVRZXIYHXJYJUVBXGYGDXHUVBXBYCXFYFUVBXAYBCJUV
      BWRYAWTWQXTEVSZWCZVTUVBXEYEKLUVBXCYDXDWQXTGVSZWCVTVJVTUVBXAYBDCIXHUVDWAVJ
      WBWDXRYSAXTUAWEUVBXPYPXQYRUVBXOYODXHUVBXMYMXNYNUVBWRYACJUVCVTUVBXCYDKLUVE
      VTVJVTUVBWRYADCIXHUVCWAVJWFWGWH $.
  $}

  ${
    $d A i x y $.  $d B x y $.  $d E f g i u v x $.  $d E t v $.  $d E u w $.
    $d M a $.  $d M f g i u v x $.  $d M t v $.  $d M u w $.
    $d N f g i u v x $.  $d N t v $.  $d N u w $.  $d N i u v x y $.
    $d S f g i u v x $.  $d S t v $.  $d S u w $.  $d S i u v x y $.
    $d V f g i u v x $.  $d V t v $.  $d V u w $.  $d W f g i u v x $.
    $d W t v $.  $d W u w $.
    satffunlem2lem2.s $e |- S = ( M Sat E ) $.
    satffunlem2lem2.a $e |- A = ( ( M ^m _om )
                              \ ( ( 2nd ` u ) i^i ( 2nd ` v ) ) ) $.
    satffunlem2lem2.b $e |- B = { a e. ( M ^m _om ) | A. z e. M
            ( { <. i , z >. } u. ( a |` ( _om \ { i } ) ) ) e. ( 2nd ` u ) } $.
    $( Lemma 2 for ~ satffunlem2 .  (Contributed by AV, 27-Oct-2023.) $)
    satffunlem2lem2 $p |- ( ( ( N e. _om /\ ( M e. V /\ E e. W ) )
                              /\ Fun ( S ` suc N ) ) -> ( dom ( S ` suc N )
                i^i dom { <. x , y >. | ( E. u e. ( ( S ` suc N ) \ ( S ` N ) )
        ( E. v e. ( S ` suc N ) ( x = ( ( 1st ` u ) |g ( 1st ` v ) ) /\ y = A )
       \/ E. i e. _om ( x = A.g i ( 1st ` u ) /\ y = B ) )
            \/ E. u e. ( S ` N ) E. v e. ( ( S ` suc N ) \ ( S ` N ) )
               ( x = ( ( 1st ` u ) |g ( 1st ` v ) ) /\ y = A ) ) } ) = (/) ) $=
      ( wcel wa vf vg vw vt com csuc cfv wfun cv c1st cgna co wceq wrex cgol wo
      cdm cdif copab cin cfmla c0 csat fveq1i dmeqi simprl simprr peano2 adantr
      cab w3a 3jca satfdmfmla syl eqtrid cvv wral cmap c2nd ovex difexi eqeltri
      wss a1i ralrimiva cop csn jca ad2antrr satfsschain mpisyl syl2anc fveqeq2
      simpr wb adantl eqidd rspcedvd funeldmdif mpbird ex eleq2i eqcomd 3imtr4d
      difeq12d eleq2d imp oveq1 eqeq2d rexbidv id goaleq12d orbi12d wrel releqi
      satfrel sylibr 1stdm sylan eleqtrrd rexlimdva2 orim1d orim12d releldmdifi
      wi sylbid eqcomi rexeqi r19.41v releldm2 bitrd reximdv biimtrid biimtrrid
      expd rexlimdv sylbird expimpd syld eqtrd cres rabex2 simplr ancri sssucid
      dmopab3rexdif funeqi bilani 3sstr3g difeq12i simpl ad4ant13 r19.29an eqid
      cun oveq2 eqcoms biimpa reximdva biimpcd com23 impbid ineq12d fmlasucdisj
      abbidv ) LUESZKMSZJNSZTZTZLUFZHUGZUHZTZUVLUQZAUIZEUIZUJUGZDUIZUJUGZUKULZU
      MZBUIZFUMTZDUVLUNUVPUVRIUIZUOZUMZUWCGUMTIUEUNUPEUVLLHUGZURZUNUWDDUWIUNEUW
      HUNUPABUSUQZUTUVKVAUGZUVPUAUIZUBUIZUKULZUMZUBUWKUNZUVPUWLUWEUOZUMZIUEUNZU
      PZUAUWKLVAUGZURZUNZUWOUBUXBUNZUAUXAUNZUPZAVJZUTZVBUVNUVOUWKUWJUXGUVNUVOUV
      KKJVCULZUGZUQZUWKUVLUXJUVKHUXIPVDZVEUVJUXKUWKUMZUVMUVJUVGUVHUVKUESZVKZUXM
      UVJUVGUVHUXNUVFUVGUVHVFZUVFUVGUVHVGZUVFUXNUVILVHZVIVLZJKUVKMNVMZVNZVIZVOZ
      UVNUWJUWBDUVLUNZUWGIUEUNZUPZEUWIUNZUWBDUWIUNZEUWHUNZUPZAVJZUXGUVNFVPSZDUV
      LVQZGVPSZIUEVQZTZEUVLVQUWHUVLWCZUWJUYKUMUVNUYPEUVLUVNUVQUVLSTZUYMUYOUYRUY
      LDUVLUYLUYRUVSUVLSZTFKUEVRULZUVQVSUGZUVSVSUGUTZURVPQUYTVUBKUEVRVTZWAWBWDW
      EUYRUYNIUEUYNUYRUWEUESTUWECUIWFWGOUIUEUWEWGURUUAUUOVUASCKVQOUYTGRVUCUUBWD
      WEWHWEUVNUVIUXNUVFTZTZLUVKWCZUYQUVNUVIVUDUVFUVIUVMUUCUVFVUDUVIUVMUVFUXNUX
      RUUDWIWHZLUUEZUVKLHJKMNPWJWKZABDEUWAFUWFGUWHUVLIUEVPVPUUFWLUVNUYJUXFAUVNU
      YJUXFUVNUYGUXCUYIUXEUVNUYFUXCEUWIUVNUVQUWISZTZUYFTZUWTUVPUVRUWMUKULZUMZUB
      UWKUNZUYEUPZUAUVRUXBVUKUVRUXBSZUYFUVNVUJVUQUVNUVQUXJLUXIUGZURZSZUVRUXKVUR
      UQZURZSZVUJVUQUVNVUTVVCUVNVUTTZVVCUCUIZUJUGUVRUMZUCVUSUNZVVDVVFUVRUVRUMZU
      CUVQVUSUVNVUTWNVVEUVQUMVVFVVHWOVVDVVEUVQUVRUJWMWPVVDUVRWQWRVVDUXJUHZVURUX
      JWCZTZVVCVVGWOUVNVVKVUTUVNVVIVVJUVMVVIUVJUVLUXJUXLUUGUUHUVNUWHUVLVURUXJVU
      ILHUXIPVDZUXLUUIWHZVIUCUXJVURUVRWSVNWTXAVUJVUTWOUVNUWIVUSUVQUVLUXJUWHVURU
      XLVVLUUJZXBWDUVNUXBVVBUVRUVNUWKUXKUXAVVAUVNUXKUWKUYBXCUVJUXAVVAUMUVMUVJVV
      AUXAUVJUVGUVHUVFVKZVVAUXAUMZUVJUVGUVHUVFUXPUXQUVFUVIUUKVLZJKLMNVMZVNXCZVI
      XEXFXDXGVIUWLUVRUMZUWTVUPWOVULVVTUWPVUOUWSUYEVVTUWOVUNUBUWKVVTUWNVUMUVPUW
      LUVRUWMUKXHXIZXJVVTUWRUWGIUEVVTUWQUWFUVPVVTUWLUVRUWEUWEVVTUWEWQVVTXKXLXIX
      JXMWPVUKUYFVUPVUKUYDVUOUYEVUKUWBVUODUVLVUKUYSTZUWBTZVUNUWBUBUVTUWKUVNUYSU
      VTUWKSVUJUWBUVNUYSTUVTUVOUWKUVNUVLXNZUYSUVTUVOSUVNUXJXNZVWDUVNUXOVWEUVNUV
      GUVHUXNUVJUVGUVMUXPVIUVJUVHUVMUXQVIUVFUXNUVIUVMUXRWIVLJKUVKMNXPVNZUVLUXJU
      XLXOXQUVSUVLXRXSUVNUWKUVOUMUYSUVNUVOUWKUYCXCVIXTUULUWMUVTUMZVUNUWBWOZVWCV
      WGVUMUWAUVPUWMUVTUVRUKUUPZXIZWPVWBUWBWNWRYAYBXGWRYAUVNUYHUXEEUWHUVNUVQUWH
      SZTZUYHTZUXDVUNUBUXBUNZUAUVRUXAVWLUVRUXASUYHVWLUVRUWHUQZUXAUVNUWHXNZVWKUV
      RVWOSUVNVURXNZVWPUVNVVOVWQUVJVVOUVMVVQVIZJKLMNXPZVNUWHVURVVLXOXQUVQUWHXRX
      SUVNUXAVWOUMVWKUVNVWOUXAUVNVWOVVAUXAUWHVURVVLVEUVNVVOVVPVWRVVRVNZVOXCVIXT
      VIVVTUXDVWNWOVWMVVTUWOVUNUBUXBVWAXJWPVWLUWBVWNDUWIVWLUVSUWISZTZUWBTZVUNUW
      BUBUVTUXBVXBUVTUXBSZUWBVWLVXAVXDUVNVXAVXDYEVWKUVNUVSVUSSZUVTVVBSZVXAVXDUV
      NVXEVXFUVNVXETZVXFUDUIZUJUGUVTUMZUDVUSUNZVXGVXIUVTUVTUMZUDUVSVUSUVNVXEWNV
      XHUVSUMVXIVXKWOVXGVXHUVSUVTUJWMWPVXGUVTWQWRVXGVVKVXFVXJWOUVNVVKVXEVVMVIUD
      UXJVURUVTWSVNWTXAVXAVXEWOUVNUWIVUSUVSVVNXBWDUVJVXDVXFWOUVMUVJUXBVVBUVTUVJ
      UWKUXKUXAVVAUVJUXKUWKUYAXCVVSXEXFVIXDVIXGVIVWGVWHVXCVWJWPVXBUWBWNWRUUMWRY
      AYCUVNUXCUYGUXEUYIUVNUWTUYGUAUXBUVNUWLUXBSZUVRUWLUMZEVUSUNZUWTUYGYEZUVNVX
      LUWLVVBSZVXNUVNUXBVVBUWLUVNUWKUXKUXAVVAUVNUXOUWKUXKUMUVJUXOUVMUXSVIZUXOUX
      KUWKUXTXCVNUVNVVAUXAVWTXCZXEZXFUVNVWEVVJVXPVXNYEVWFUVNVUEVUFVVJVUGVUHUVKL
      UXIJKMNUXIUUNWJWKZEUXJVURUWLYDWLYFVXNVXMEUWIUNZUVNVXOVXMEVUSUWIUWIVUSVVNY
      GZYHUVNVYAUWTUYGVYAUWTTVXMUWTTZEUWIUNUVNUYGVXMUWTEUWIYIUVNVYCUYFEUWIVUKVX
      MUWTUYFVUKVXMTZUWTVUPUYFVXMVUPUWTWOVUKVXMVUOUWPUYEUWSVXMVUNUWOUBUWKVXMVUM
      UWNUVPUVRUWLUWMUKXHXIZXJVXMUWGUWRIUEVXMUWFUWQUVPVXMUVRUWLUWEUWEVXMUWEWQVX
      MXKXLXIXJXMWPVYDVUOUYDUYEUVNVUOUYDYEVUJVXMUVNVUNUYDUBUWKUVNUWMUWKSZUVTUWM
      UMZDUXJUNZVUNUYDYEUVNVYFUWMUXKSZVYHUVNUWKUXKUWMUVNUXKUWKUVNUXOUXMVXQUXTVN
      XCXFUVNVWEVYIVYHWOVWFDUXJUWMYJVNYKUVNVYHVUNUYDVYHVUNTVYGVUNTZDUXJUNZUVNUY
      DVYGVUNDUXJYIVYKVYJDUVLUNUVNUYDVYJDUXJUVLUVKUXIHHUXIPYGVDYHUVNVYJUWBDUVLV
      YJUWBYEUVNVYGVUNUWBVYGVUMUWAUVPVUMUWAUMUWMUVTVWIUUQXIZUURWDYLYMYNYOYFYPWI
      YBYQYRUUSYNYOYMYSYPUVNUXDUYIUAUXAUVNUWLUXASZVXMEVURUNZUXDUYIYEUVNVYMUWLVV
      ASZVYNUVNUXAVVAUWLVXRXFUVNVWQVYOVYNWOUVJVWQUVMUVJVVOVWQVVQVWSVNVIEVURUWLY
      JVNYKUVNVYNUXDUYIVYNUXDTVXMUXDTZEVURUNZUVNUYIVXMUXDEVURYIVYQVYPEUWHUNUVNU
      YIVYPEVURUWHUWHVURVVLYGYHUVNVYPUYHEUWHUVNVXMUXDUYHUVNVXMTUXDVWNUYHVXMVWNU
      XDWOUVNVXMVUNUWOUBUXBVYEXJWPUVNVWNUYHYEVXMUVNVUNUYHUBUXBUVNUWMUXBSZVYGDVU
      SUNZVUNUYHYEZUVNVYRUWMVVBSZVYSUVNUXBVVBUWMVXSXFUVNVWEVVJWUAVYSYEVWFVXTDUX
      JVURUWMYDWLYFVYSVYGDUWIUNZUVNVYTVYGDVUSUWIVYBYHUVNVUNWUBUYHUVNVUNWUBUYHYE
      UVNVUNTVYGUWBDUWIVUNVYGUWBYEUVNVYGVUNUWBVYLUUTWPYLXAUVAYMYSYPVIYQYRYLYMYN
      YOYFYPYCUVBUVEYTUVCUVFUXHVBUMUVIUVMAUBUAILUVDWIYT $.
  $}

  ${
    $d E f i j u v x y $.  $d M f i j u v x y $.  $d V f i u v x y $.
    $d W f i u v x y $.
    $( Lemma 1 for ~ satffun : induction basis.  (Contributed by AV,
       28-Oct-2023.) $)
    satffunlem1 $p |- ( ( M e. V /\ E e. W )
                        -> Fun ( ( M Sat E ) ` suc (/) ) ) $=
      ( vx vu vv vy vi vj vf wcel wa c0 co cfv wfun cv wceq com cin cop csn cun
      csuc csat c1st cgna cmap c2nd cdif wrex cgol cres wral wo copab satfv0fun
      crab cdm satffunlem1lem1 syl satffunlem1lem2 funun syl21anc eqid satfvsuc
      peano1 mp3an3 funeqd mpbird ) BCLZADLZMZNUEBAUFOZPZQNVOPZERZFRZUGPZGRZUGP
      UHOSHRZBTUIOZVSUJPZWAUJPUAUKSMGVQULVRVTIRZUMSWBWEJRUBUCKRTWEUCUKUNUDWDLJB
      UOKWCUSSMITULUPFVQULEHUQZUDZQZVNVQQZWFQZVQUTWFUTUANSWHABCDURZVNWIWJWKEHGF
      KIJABNVAVBEHGFKIJABCDVCVQWFVDVEVNVPWGVLVMNTLVPWGSVHEHJGFVOIABNCDKVOVFVGVI
      VJVK $.

    $d N i u v x y $.
    $( Lemma 2 for ~ satffun : induction step.  (Contributed by AV,
       28-Oct-2023.) $)
    satffunlem2 $p |- ( ( N e. _om /\ ( M e. V /\ E e. W ) )
                        -> ( Fun ( ( M Sat E ) ` suc N )
                             -> Fun ( ( M Sat E ) ` suc suc N ) ) ) $=
      ( vx vu vv vy vi vj vf com wcel wa cfv wfun cv wceq wrex csuc csat co cin
      c1st cgna cmap c2nd cdif cgol cop csn cres cun wral wo copab cdm c0 simpr
      crab wss wi peano2 ancri adantr sssucid a1i eqid satfsschain imp syl21anc
      satffunlem2lem1 expcom satffunlem2lem2 funun simpl satfvsucsuc syl2an23an
      syl wb funeqd mpbird ex ) CMNZBDNZAENZOZOZCUAZBAUBUCZPZQZWJUAWKPZQZWIWMOZ
      WOWLFRZGRZUEPZHRZUEPUFUCSIRZBMUGUCZWRUHPZWTUHPUDUIZSOZHWLTWQWSJRZUJSXAXFK
      RUKULLRMXFULUIUMUNXCNKBUOLXBVAZSOJMTUPGWLCWKPZUIZTXEHXITGXHTUPFIUQZUNZQZW
      PWMXJQZWLURXJURUDUSSXLWIWMUTWIWMXMWIXHWLVBZWMXMVCWIWHWJMNZWEOZCWJVBZXNWEW
      HUTWEXPWHWEXOCVDVEVFXQWICVGVHWHXPOXQXNWJCWKABDEWKVIZVJVKVLWMXNXMFIKHGXDXG
      WKJABCLXRXDVIZXGVIZVMVNVTVKFIKHGXDXGWKJABCDELXRXSXTVOWLXJVPVLWIWOXLWAWMWI
      WNXKWHWFWGWEWEWNXKSWFWGVQWFWGUTWEWHVQFIKHGXDXGWKJABCDELXRXSXTVRVSWBVFWCWD
      $.
  $}

  ${
    $d E n x y $.  $d M n x y $.  $d N n $.  $d V n x y $.  $d W n x y $.
    $( The value of the satisfaction predicate as function over wff codes at a
       natural number is a function.  (Contributed by AV, 28-Oct-2023.) $)
    satffun $p |- ( ( M e. V /\ E e. W /\ N e. _om )
                    -> Fun ( ( M Sat E ) ` N ) ) $=
      ( vn vx vy c0 wceq wcel com cfv wfun wi funeqd csuc suceq fveq2d imbi2d
      w3a csat co satfv0fun 3adant3 fveq2 imbitrrid wn wa wne df-ne cv wrex weq
      nnsuc satffunlem1 pm2.27 satffunlem2 expcom com23 syld com13 finds adantr
      wb adantl mpbird rexlimiva syl sylbir 3impia com12 pm2.61i ) CIJZBDKZAEKZ
      CLKZUAZCBAUBUCZMZNZOVRWAVNIVSMZNZVOVPWCVQABDEUDUEVNVTWBCIVSUFPUGVRVNUHZWA
      VOVPVQWDWAOWDVQVOVPUIZWAWDCIUJZVQWEWAOZOCIUKVQWFWGVQWFUICFULZQZJZFLUMWGFC
      UOWJWGFLWHLKZWJUIWGWEWIVSMZNZOZWKWNWJWEGULZQZVSMZNZOWEIQZVSMZNZOWEHULZQZV
      SMZNZOZWEXCQZVSMZNZOWNGHWHWOIJZWRXAWEXJWQWTXJWPWSVSWOIRSPTGHUNZWRXEWEXKWQ
      XDXKWPXCVSWOXBRSPTWOXCJZWRXIWEXLWQXHXLWPXGVSWOXCRSPTGFUNZWRWMWEXMWQWLXMWP
      WIVSWOWHRSPTABDEUPWEXFXBLKZXIWEXFXEXNXIOWEXEUQWEXNXEXIXNWEXEXIOABXBDEURUS
      UTVAVBVCVDWJWGWNVEWKWJWAWMWEWJVTWLCWIVSUFPTVFVGVHVIUSVJVBVKVLVM $.
  $}

  $( The satisfaction predicate as function over wff codes in the model ` M `
     and the binary relation ` E ` on ` M ` .  (Contributed by AV,
     28-Oct-2023.) $)
  satff $p |- ( ( M e. V /\ E e. W /\ N e. _om )
                -> ( ( M Sat E ) ` N ) : ( Fmla ` N ) --> ~P ( M ^m _om ) ) $=
    ( wcel com w3a csat co cfv cfmla wfn crn cmap cpw wss wf wfun sylanbrc wceq
    cdm satffun satfdmfmla df-fn satfrnmapom df-f ) BDFAEFCGFHZCBAIJKZCLKZMZUIN
    BGOJPZQUJULUIRUHUISUIUBUJUAUKABCDEUCABCDEUDUIUJUETABCDEUFUJULUIUGT $.

  ${
    $d E x y $.  $d M x y $.  $d V x y $.  $d W x y $.
    $( The satisfaction predicate as function over wff codes in the model ` M `
       and the binary relation ` E ` on ` M ` .  (Contributed by AV,
       29-Oct-2023.) $)
    satfun $p |- ( ( M e. V /\ E e. W )
             -> ( ( M Sat E ) ` _om ) : ( Fmla ` _om ) --> ~P ( M ^m _om ) ) $=
      ( vx vy wcel wa com cfmla cfv co wf cv ciun wss wral wbr adantl wb cpw wo
      cmap csat satff 3expa csdm cen w3o entric wpss nnsdomo pm3.22 anim2i eqid
      pssss satfsschain imp syl2an orcd ex sylbid weq ssid fveq2 sseqtrrid olcd
      nneneq biimtrdi impel 3jaod mpd expr ralrimiv jca ralrimiva fvex fiun syl
      ancoms satom wceq fmla a1i feq12d mpbird ) BCGZADGZHZIJKZBIUCLUAZIBAUDLZK
      ZMEIENZJKZOZWKEIWNWLKZOZMZWIWOWKWQMZWQFNZWLKZPZXBWQPZUBZFIQZHZEIQWSWIXGEI
      WIWNIGZHZWTXFWGWHXHWTABWNCDUEUFXIXEFIWIXHXAIGZXEWIXHXJHZHZWNXAUGRZWNXAUHR
      ZXAWNUGRZUIZXEXKXPWIWNXAIIUJSXLXMXEXNXOXLXMWNXAUKZXEXKXMXQTWIWNXAULSXLXQX
      EXLXQHXCXDXLWIXJXHHZHZWNXAPZXCXQXKXRWIXHXJUMUNWNXAUPXSXTXCXAWNWLABCDWLUOZ
      UQURUSUTVAVBXLXNEFVCZXEXKXNYBTWIWNXAVHSYBXDXCYBXBXBWQXBVDWNXAWLVEZVFVGVIX
      LXOXAWNUKZXEXKXOYDTZWIXJXHYEXAWNULVTSXLYDXEXLYDHXDXCXLXAWNPXDYDWNXAWLABCD
      YAUQXAWNUPVJVGVAVBVKVLVMVNVOVPEFIWQXBWOWKYCWNWLVQVRVSWIWJWPWKWMWREABCDWAW
      JWPWBWIEWCWDWEWF $.
  $}

  $( An element of the value of the satisfaction predicate as function over wff
     codes in the model ` M ` and the binary relation ` E ` on ` M ` at the
     code ` U ` for a wff using ` e. , -/\ , A. ` is a valuation
     ` S : _om --> M ` of the variables (v_0 ` = ( S `` (/) ) ` , v_1
     ` = ( S `` 1o ) ` , etc.) so that ` U ` is true under the assignment
     ` S ` .  (Contributed by AV, 29-Oct-2023.) $)
  satfvel $p |- ( ( ( M e. V /\ E e. W ) /\ U e. ( Fmla ` _om )
                    /\ S e. ( ( ( M Sat E ) ` _om ) ` U ) )
                 -> S : _om --> M ) $=
    ( wcel wa com cfmla cfv csat co wf cmap cpw wi satfun ffvelcdm syl wss fvex
    elpw ssel elmapi syl6 sylbi ex 3imp ) DEGCFGHZBIJKZGZABIDCLMKZKZGZIDANZUJUK
    DIOMZPZUMNZULUOUPQZQCDEFRUSULUTUSULHUNURGZUTUKURBUMSVAUNUQUAZUTUNUQBUMUBUCV
    BUOAUQGUPUNUQAUDADIUEUFUGTUHTUI $.

  ${
    $d E a i j x y $.  $d M a i j x y $.  $d X a i j x y $.
    satfv0fv.s $e |- S = ( M Sat E ) $.
    $( The value of the satisfaction predicate as function over a wff code at
       ` (/) ` .  (Contributed by AV, 2-Nov-2023.) $)
    satfv0fvfmla0 $p |- ( ( M e. V /\ E e. W /\ X e. ( Fmla ` (/) ) )
                          -> ( ( S ` (/) ) ` X ) = { a e. ( M ^m _om ) |
                                       ( a ` ( 1st ` ( 2nd ` X ) ) )
                                     E ( a ` ( 2nd ` ( 2nd ` X ) ) ) } ) $=
      ( vx vi vj wcel c0 cfv c2nd c1st com wceq wa wrex cfmla w3a wfun wbr cmap
      vy cv crab cop csat satfv0fun fveq1i funeqi sylibr 3adant3 cgoe copab cvv
      fmla0 eleq2i eqeq1 2rexbidv elrab bitri simpr goel eqeq2d 2fveq3 0ex opex
      co wb op2nd fveq2i vex op1st eqtri eqtrdi fveq2d breq12d biimtrdi rabbidv
      imp ex reximdva reximia simplbiim 3ad2ant3 simp3 ovex bi2anan9 opelopabga
      jca rabex sylancl mpbird satfv0 eleq2d funopfv sylc ) CDLZBELZFMUANZLZUBZ
      MANZUCZFFONZPNZGUGZNZXHONZXJNZBUDZGCQUEVKZUHZUIZXFLZFXFNXPRXAXBXGXDXAXBSZ
      MCBUJVKZNZUCXGBCDEUKXFYAMAXTHULUMUNUOXEXRXQIUGZJUGZKUGZUPVKZRZUFUGZYCXJNZ
      YDXJNZBUDZGXOUHZRZSZKQTJQTZIUFUQZLZXEYPFYERZXPYKRZSZKQTZJQTZXDXAUUAXBXDFU
      RLZYQKQTZJQTZUUAXDFYFKQTJQTZIURUHZLUUBUUDSXCUUFFIJKUSUTUUEUUDIFURYBFRZYFY
      QJKQQYBFYEVAZVBVCVDUUCYTJQYCQLZYQYSKQUUIYDQLSZYQYSUUJYQSZYQYRUUJYQVEUUKXN
      YJGXOUUJYQXNYJVLZUUJYQFMYCYDUIZUIZRZUULUUJYEUUNFYCYDVFVGUUOXKYHXMYIBUUOXI
      YCXJUUOXIUUNONZPNZYCFUUNPOVHUUQUUMPNYCUUPUUMPMUUMVIYCYDVJVMZVNYCYDJVOZKVO
      ZVPVQVRVSUUOXLYDXJUUOXLUUPONZYDFUUNOOVHUVAUUMONYDUUPUUMOUURVNYCYDUUSUUTVM
      VQVRVSVTWAWCWBWMWDWEWFWGWHXEXDXPURLYPUUAVLXAXBXDWIXNGXOCQUEWJWNYNUUAIUFFX
      PXCURUUGYGXPRZSYMYSJKQQUUGYFYQUVBYLYRUUHYGXPYKVAWKVBWLWOWPXAXBXRYPVLXDXSX
      FYOXQIUFAJKBCDEGHWQWRUOWPFXPXFWSWT $.
  $}

$( --- theorems for ` ( M SatE U ) ` --- $)

  ${
    $d M m u $.  $d U m u $.  $d V m u $.  $d W m u $.
    $( The simplified satisfaction predicate as function over wff codes in the
       model ` M ` at the code ` U ` .  (Contributed by AV, 30-Oct-2023.) $)
    satefv $p |- ( ( M e. V /\ U e. W ) -> ( M SatE U )
                       = ( ( ( M Sat ( _E i^i ( M X. M ) ) ) ` _om ) ` U ) ) $=
      ( vm vu wcel wa cvv cv com cep cxp cin csat co cfv csate wceq adantr cmpo
      df-sate a1i sqxpeqd ineq2d oveq12d fveq1d simpr fveq12d adantl elex fvexd
      id ovmpod ) BCGZADGZHZEFBAIIFJZKEJZLUSUSMZNZOPZQZQZAKBLBBMZNZOPZQZQZRIREF
      IIVDUASUQFEUBUCUSBSZURASZHZVDVISUQVLURAVCVHVJVCVHSVKVJKVBVGVJUSBVAVFOVJUM
      ZVJUTVELVJUSBVMUDUEUFUGTVJVKUHUIUJUOBIGUPBCUKTUPAIGUOADUKUJUQAVHULUN $.
  $}

  $( The simplified satisfaction predicate for any wff code over an empty
     model.  (Contributed by AV, 6-Oct-2023.)  (Revised by AV, 5-Nov-2023.) $)
  sate0 $p |- ( U e. V -> ( (/) SatE U )
                          = ( ( ( (/) Sat (/) ) ` _om ) ` U ) ) $=
    ( wcel c0 csate co com cep cxp cin csat cfv cvv wceq 0ex satefv mpan ineq2i
    xp0 fveq1i in0 eqtri oveq2i eqtrdi ) ABCZDAEFZAGDHDDIZJZKFZLZLZAGDDKFZLZLDM
    CUEUFUKNOADMBPQAUJUMGUIULUHDDKUHHDJDUGDHDSRHUAUBUCTTUD $.

  $( The simplified satisfaction predicate as function over wff codes over an
     empty model.  (Contributed by AV, 30-Oct-2023.) $)
  satef $p |- ( ( M e. V /\ U e. ( Fmla ` _om ) /\ S e. ( M SatE U ) )
                  -> S : _om --> M ) $=
    ( wcel com cfmla cfv csate co w3a cep cxp cin cvv wa csat adantr syl simpr
    wf satefv eleq2d simpl incom sqxpexg inex1g eqeltrid jca 3jca sylbid 3impia
    ex satfvel ) CDEZBFGHZEZACBIJZEZKUOLCCMZNZOEZPZUQABFCVAQJHHZEZKZFCAUAUOUQUS
    VFUOUQPZUSVEVFVGURVDABCDUPUBUCVGVEVFVGVEPVCUQVEVGVCVEVGUOVBUOUQUDVGVAUTLNZO
    LUTUEVGUTOEZVHOEUOVIUQCDUFRUTLOUGSUHUIRVGUQVEUOUQTRVGVETUJUMUKULABVACDOUNS
    $.

  $( A simplified satisfaction predicate as function over wff codes over an
     empty model is an empty set.  (Contributed by AV, 31-Oct-2023.) $)
  sate0fv0 $p |- ( U e. ( Fmla ` _om )
                   -> ( S e. ( (/) SatE U ) -> S = (/) ) ) $=
    ( com cfmla cfv wcel c0 csate co wceq cvv 0ex satef mp3an1 f00 simplbi syl6
    wf ex ) BCDEFZAGBHIFZCGARZAGJZTUAUBGKFTUAUBLABGKMNSUBUCCGJCAOPQ $.

  ${
    $d M a i $.  $d V a i $.  $d X a x y $.
    $( The simplified satisfaction predicate for wff codes of height 0.
       (Contributed by AV, 4-Nov-2023.) $)
    satefvfmla0 $p |- ( ( M e. V /\ X e. ( Fmla ` (/) ) )
                        -> ( M SatE X ) = { a e. ( M ^m _om ) |
                                           ( a ` ( 1st ` ( 2nd ` X ) ) )
                                        e. ( a ` ( 2nd ` ( 2nd ` X ) ) ) } ) $=
      ( vi vx vy wcel c0 cfv wa com cep c2nd cv cvv wceq syl adantr eqtrd cfmla
      csate co cxp cin csat c1st cmap crab satefv incom sqxpexg inex1g eqeltrid
      ciun ancli satom fveq1d wfun cdm cpw wf satfun ffund eqcomd funeqd mpbird
      peano1 a1i satfdmfmla mpd3an23 eleq2d biimpa fviunfun syl3anc simpl simpr
      eqid wbr satfv0fvfmla0 wb wi elmapi cop csn wex fmla0xp eleq2i elxp bitri
      xp1st ad2antll vex op2ndd fveq2d eleq1d exlimivv sylbi ffvelcdmd xp2nd ex
      jca impcom brinxp bicomd fvex epeli bitrdi rabbidva ) ABHZCIUAJZHZKZACUBU
      CCLAMAAUDZUEZUFUCZJZJZCNJZUGJZDOZJZXSNJZYAJZHZDALUHUCZUIZCABXKUJXMXRCIXPJ
      ZJZYGXMXRCELEOXPJUOZJZYIXMCXQYJXMXJXOPHZKZXQYJQXJYMXLXJYLXJXOXNMUEZPMXNUK
      XJXNPHYNPHABULXNMPUMRUNZUPSZEXOABPUQRZURXMYJUSZILHZCYHUTZHZYKYIQXMYRXQUSX
      MLUAJZYFVAZXQXMYMUUBUUCXQVBYPXOABPVCRVDXMYJXQXMXQYJYQVEVFVGYSXMVHVIXJXLUU
      AXJXKYTCXJYTXKXJYLYSYTXKQYOYSXJVHVIXOAIBPVJVKVEVLVMYJEXPLICYJVRVNVOTXMYIY
      BYDXOVSZDYFUIZYGXMXJYLXLYIUUEQXJXLVPXJYLXLYOSXJXLVQXPXOABPCDXPVRVTVOXMUUD
      YEDYFXMYAYFHZKZUUDYBYDMVSZYEUUGYBAHZYDAHZKZUUDUUHWAUUFXMUUKUUFLAYAVBZXMUU
      KWBYAALWCUULXMUUKUULXMKZUUIUUJUUMLAXTYAUULXMVPZXLXTLHZUULXJXLCFOZGOZWDQZU
      UPIWEZHZUUQLLUDZHZKZKZGWFFWFZUUOXLCUUSUVAUDZHUVEXKUVFCWGWHFGCUUSUVAWIWJZU
      VDUUOFGUVDUUOUUQUGJZLHZUVBUVIUURUUTUUQLLWKWLUURUUOUVIWAUVCUURXTUVHLUURXSU
      UQUGUUPUUQCFWMGWMWNZWOWPSVGWQWRWLWSUUMLAYCYAUUNXLYCLHZUULXJXLUVEUVKUVGUVD
      UVKFGUVDUVKUUQNJZLHZUVBUVMUURUUTUUQLLWTWLUURUVKUVMWAUVCUURYCUVLLUURXSUUQN
      UVJWOWPSVGWQWRWLWSXBXARXCUUKUUHUUDYBYDAAMXDXERYBYDYCYAXFXGXHXITTT $.
  $}

  ${
    $d A a b x $.  $d B a b x $.  $d M a $.  $d S a $.  $d V a $.
    sategoelfvb.s $e |- E = ( M SatE ( A e.g B ) ) $.
    $( Characterization of a valuation ` S ` of a simplified satisfaction
       predicate for a Godel-set of membership.  (Contributed by AV,
       5-Nov-2023.) $)
    sategoelfvb $p |- ( ( M e. V /\ ( A e. _om /\ B e. _om ) )
         -> ( S e. E <-> ( S e. ( M ^m _om ) /\ ( S ` A ) e. ( S ` B ) ) ) ) $=
      ( va vb wcel com wa c2nd cfv c1st c0 wceq wrex cop fveq2d vx cmap co cgoe
      cv crab csate cfmla cvv ovexd simpl wb opeq1 opeq2d eqeq2d rexbidv adantl
      simpr opeq2 eqidd rspcedvd goel eqeqan12d 2rexbidva mpbird eqeq1 2rexbidv
      fmla0 elrab2 sylanbrc satefvfmla0 sylan2 eqtrid eleq2d fveq1 elrab bitrdi
      eleq12d 0ex opex op2nd fveq2i op1stg eqtrd op2ndg anbi2d bitrd ) EFJZAKJZ
      BKJZLZLZCDJZCEKUBUCZJZABUDUCZMNZONZCNZWQMNZCNZJZLZWOACNZBCNZJZLWLWMCWRHUE
      ZNZWTXGNZJZHWNUFZJXCWLDXKCWLDEWPUGUCZXKGWKWHWPPUHNZJZXLXKQWKWPUIJWPXGIUEZ
      UDUCZQZIKRHKRZXNWKABUDUJWKXRPABSZSZPXGXOSZSZQZIKRZHKRWKYDXTPAXOSZSZQZIKRZ
      HAKWIWJUKXGAQZYDYHULWKYIYCYGIKYIYBYFXTYIYAYEPXGAXOUMUNUOUPUQWKYGXTXTQZIBK
      WIWJURXOBQZYGYJULWKYKYFXTXTYKYEXSPXOBAUSUNUOUQWKXTUTVAVAWKXQYCHIKKWKXGKJX
      OKJLWPXTXPYBABVBZXGXOVBVCVDVEUAUEZXPQZIKRHKRXRUAWPUIXMYMWPQYNXQHIKKYMWPXP
      VFVGUAHIVHVIVJEFWPHVKVLVMVNXJXBHCWNXGCQXHWSXIXAWRXGCVOWTXGCVOVRVPVQWLXBXF
      WOWKXBXFULWHWKWSXDXAXEWKWRACWKWRXTMNZONZAWKWQYOOWKWPXTMYLTZTWKYPXSONAYOXS
      OPXSVSABVTWAZWBABKKWCVMWDTWKWTBCWKWTYOMNZBWKWQYOMYQTWKYSXSMNBYOXSMYRWBABK
      KWEVMWDTVRUQWFWG $.

    $( Condition of a valuation ` S ` of a simplified satisfaction predicate
       for a Godel-set of membership:  The sets in model ` M ` corresponding to
       the variables ` A ` and ` B ` under the assignment of ` S ` are in a
       membership relation in ` M ` .  (Contributed by AV, 5-Nov-2023.) $)
    sategoelfv $p |- ( ( M e. V /\ ( A e. _om /\ B e. _om ) /\ S e. E )
                       -> ( S ` A ) e. ( S ` B ) ) $=
      ( wcel com wa cfv cmap co sategoelfvb simpr biimtrdi 3impia ) EFHZAIHBIHJ
      ZCDHZACKBCKHZRSJTCEILMHZUAJUAABCDEFGNUBUAOPQ $.

    $d M x $.  $d Z x $.
    ex-sategoelel.s $e |- S = ( x e. _om
                          |-> if ( x = A , Z , if ( x = B , ~P Z , (/) ) ) ) $.
    $( Example of a valuation of a simplified satisfaction predicate for a
       Godel-set of membership.  (Contributed by AV, 5-Nov-2023.) $)
    ex-sategoelel $p |- ( ( ( M e. WUni /\ Z e. M )
                        /\ ( A e. _om /\ B e. _om /\ A =/= B ) ) -> S e. E ) $=
      ( cwun wcel wa com wceq c0 cif ifcld adantr cvv adantl wne w3a cmap co wf
      cfv cv cpw simpr simpl wunpw wun0 fmptd omex a1i elmapd mpbird pwidg cmpt
      iftrue simpr1 fvmptd eqeq1 ifbid ifbieq2d necom ifnefalse sylbi sylan9eqr
      3ad2ant3 simpr2 0ex eqid iftruei eqtrdi 3eltr4d 3simpa sategoelfvb syl2an
      pwexg wb mpbir2and ) FJKZGFKZLZBMKZCMKZBCUAZUBZLZDEKZDFMUCUDKZBDUFZCDUFZK
      ZWJWLMFDUEWJAMAUGZBNZGWPCNZGUHZOPZPZFDWJXAFKZWPMKWEXBWIWEWQGWTFWCWDUIZWEW
      RWSOFWEGFWCWDUJZXCUKWEFXDULQQRRIUMWJFMDJSWEWCWIXDRMSKWJUNUOUPUQWJGWSWMWNW
      EGWSKZWIWDXEWCGFURTRWJABXAGMDFDAMXAUSNWJIUOZWQXAGNWJWQGWTUTTWEWFWGWHVAWEW
      DWIXCRVBWJWNCCNZWSOPZWSWJACXAXHMDSXFWRWJXACBNZGXHPZXHWRWQXIWTXHGWPCBVCWRW
      RXGWSOWPCCVCVDVEWIXJXHNZWEWHWFXKWGWHCBUAXKBCVFCBGXHVGVHVJTVIWEWFWGWHVKWEX
      HSKWIWEXGWSOSWDWSSKWCGFVTTOSKWEVLUOQRVBXGWSOCVMVNVOVPWEWCWFWGLWKWLWOLWAWI
      XDWFWGWHVQBCDEFJHVRVSWB $.

    $( Instance of ~ sategoelfv for the example of a valuation of a simplified
       satisfaction predicate for a Godel-set of membership.  (Contributed by
       AV, 5-Nov-2023.) $)
    ex-sategoel $p |- ( ( ( M e. WUni /\ Z e. M )
                          /\ ( A e. _om /\ B e. _om /\ A =/= B ) )
                        -> ( S ` A ) e. ( S ` B ) ) $=
      ( cwun wcel wa com wne w3a cfv simpll 3simpa adantl ex-sategoelel syl3anc
      sategoelfv ) FJKZGFKZLZBMKZCMKZBCNZOZLUCUFUGLZDEKBDPCDPKUCUDUIQUIUJUEUFUG
      UHRSABCDEFGHITBCDEFJHUBUA $.
  $}

  ${
    $d I i j k n $.  $d J j k n $.  $d K k n $.  $d L n $.  $d X i j k n x $.
    satfv1fvfmla1.x $e |- X = ( ( I e.g J ) |g ( K e.g L ) ) $.
    ${
      $d E a i j k l x y $.  $d E a i j n x y z $.  $d I a l x y $.  $d I z $.
      $d J a i x y z $.  $d J l $.  $d K a i j l x y $.  $d L a i j k l x y $.
      $d M a i j k l x y $.  $d M a i j n x y z $.  $d V i j k l x y $.
      $d W i j k l x y $.  $d X l y $.
      $( The value of the satisfaction predicate at two Godel-sets of
         membership combined with a Godel-set for NAND. (Contributed by AV,
         17-Nov-2023.) $)
      satfv1fvfmla1 $p |- ( ( ( M e. V /\ E e. W ) /\ ( I e. _om /\ J e. _om )
                              /\ ( K e. _om /\ L e. _om ) )
                 -> ( ( ( M Sat E ) ` 1o ) ` X )
                    = { a e. ( M ^m _om ) | ( -. ( a ` I ) E ( a ` J )
                                           \/ -. ( a ` K ) E ( a ` L ) ) } ) $=
        ( vn wcel wa com co cfv wceq wrex eqeq2d vx vi vj vk vl vy w3a c1o csat
        vz wfun cv wbr wn wo cmap crab cop simpl 1onn a1i 3jca 3ad2ant1 satffun
        simpr syl c0 cgoe cgna cgol weq wif wral copab cun simp2l simp2r simp3l
        simp3r eqid pm3.2i oveq1 oveq2d fveq2 breq1d notbid orbi2d oveq2 breq2d
        rabbidv anbi12d rspc2ev syl3anc orcd oveq1d orbi1d 2rexbidv eqidd eqeq1
        goaleq12d biidd ifpbi23d ifpbi123d ralbidv rexbidv orbi12d cvv wb ovexi
        ovex rabex bi2anan9 opelopabga sylancl mpbird olcd sylibr satfv1 eleq2d
        elun funopfv sylc ) FGMZAHMZNZBOMZCOMZNZDOMZEOMZNZUGZUHFAUIPZQZUKZIBJUL
        ZQZCYPQZAUMZUNZDYPQZEYPQZAUMZUNZUOZJFOUPPZUQZURZYNMZIYNQUUGRYLYCYDUHOMZ
        UGZYOYEYHUUKYKYEYCYDUUJYCYDUSYCYDVEUUJYEUTVAVBVCAFUHGHVDVFYLUUIUUHVGYMQ
        ZUAULZUBULZUCULZVHPZUDULZUEULZVHPZVIPZRZUFULZUUNYPQZUUOYPQZAUMZUNZUUQYP
        QZUURYPQZAUMZUNZUOZJUUFUQZRZNZUEOSUDOSZUUMUUPLULZVJZRZUVBUBLVKZUCLVKZUJ
        ULZUWAAUMZUWAUVDAUMZVLZUVTUVCUWAAUMZUVEVLZVLZUJFVMZJUUFUQZRZNZLOSZUOZUC
        OSUBOSZUAUFVNZVOZMZYLUUHUULMZUUHUWOMZUOUWQYLUWSUWRYLUWSIUUTRZUUGUVLRZNZ
        UEOSUDOSZIUVQRZUUGUWIRZNZLOSZUOZUCOSUBOSZYLYFYGIBCVHPZUUSVIPZRZUUGYTUVJ
        UOZJUUFUQZRZNZUEOSUDOSZIUXJUVPVJZRZUUGBUVPRZCUVPRZUWBUWAYRAUMZVLZUYAYQU
        WAAUMZYSVLZVLZUJFVMZJUUFUQZRZNZLOSZUOZUXIYEYFYGYKVPYEYFYGYKVQYLUXQUYKYL
        YIYJIUXJDEVHPZVIPZRZUUGUUGRZNZUXQYEYHYIYJVRYEYHYIYJVSUYQYLUYOUYPKUUGVTW
        AVAUXPUYQIUXJDUURVHPZVIPZRZUUGYTUUAUVHAUMZUNZUOZJUUFUQZRZNUDUEDEOOUUQDR
        ZUXLUYTUXOVUEVUFUXKUYSIVUFUUSUYRUXJVIUUQDUURVHWBWCTVUFUXNVUDUUGVUFUXMVU
        CJUUFVUFUVJVUBYTVUFUVIVUAVUFUVGUUAUVHAUUQDYPWDWEWFWGWJTWKUURERZUYTUYOVU
        EUYPVUGUYSUYNIVUGUYRUYMUXJVIUUREDVHWHWCTVUGVUDUUGUUGVUGVUCUUEJUUFVUGVUB
        UUDYTVUGVUAUUCVUGUVHUUBUUAAUUREYPWDWIWFWGWJTWKWLWMWNUXHUYLIBUUOVHPZUUSV
        IPZRZUUGYQUVDAUMZUNZUVJUOZJUUFUQZRZNZUEOSUDOSZIVUHUVPVJZRZUUGUXTUWDUVTU
        YDVUKVLZVLZUJFVMZJUUFUQZRZNZLOSZUOUBUCBCOOUUNBRZUXCVUQUXGVVFVVGUXBVUPUD
        UEOOVVGUWTVUJUXAVUOVVGUUTVUIIVVGUUPVUHUUSVIUUNBUUOVHWBZWOTVVGUVLVUNUUGV
        VGUVKVUMJUUFVVGUVFVULUVJVVGUVEVUKVVGUVCYQUVDAUUNBYPWDZWEZWFWPWJTWKWQVVG
        UXFVVELOVVGUXDVUSUXEVVDVVGUVQVURIVVGUUPVUHUVPUVPVVGUVPWRVVHWTTVVGUWIVVC
        UUGVVGUWHVVBJUUFVVGUWGVVAUJFVVGUVSUWDUWFUXTUWDVUTUUNBUVPWSVVGUWDXAVVGUV
        TUWEUVEUYDVUKVVGUVCYQUWAAVVIWEVVJXBXCXDWJTWKXEXFUUOCRZVUQUXQVVFUYKVVKVU
        PUXPUDUEOOVVKVUJUXLVUOUXOVVKVUIUXKIVVKVUHUXJUUSVIUUOCBVHWHZWOTVVKVUNUXN
        UUGVVKVUMUXMJUUFVVKVULYTUVJVVKVUKYSVVKUVDYRYQAUUOCYPWDZWIZWFWPWJTWKWQVV
        KVVEUYJLOVVKVUSUXSVVDUYIVVKVURUXRIVVKVUHUXJUVPUVPVVKUVPWRVVLWTTVVKVVCUY
        HUUGVVKVVBUYGJUUFVVKVVAUYFUJFVVKUXTUWDVUTUYCUYEVVKUVTUWBUWCUYAUWBUYBUUO
        CUVPWSZVVKUWBXAVVKUVDYRUWAAVVMWIXCVVKUVTUYDVUKUYAUYDYSVVOVVKUYDXAVVNXCX
        BXDWJTWKXEXFWLWMYLIXGMZUUGXGMUWSUXIXHVVPYLIUXJUYMVIKXIVAUUEJUUFFOUPXJXK
        UWNUXIUAUFIUUGXGXGUUMIRZUVBUUGRZNZUWMUXHUBUCOOVVSUVOUXCUWLUXGVVSUVNUXBU
        DUEOOVVQUVAUWTVVRUVMUXAUUMIUUTWSUVBUUGUVLWSXLWQVVSUWKUXFLOVVQUVRUXDVVRU
        WJUXEUUMIUVQWSUVBUUGUWIWSXLXEXFWQXMXNXOXPUUHUULUWOXTXQYEYHUUIUWQXHYKYEY
        NUWPUUHUAUFUJYMUBUCUDLAFGHJUEYMVTXRXSVCXOIUUGYNYAYB $.
    $}

    $( Two Godel-sets of membership combined with a Godel-set for NAND is a
       Godel formula of height 1.  (Contributed by AV, 17-Nov-2023.) $)
    2goelgoanfmla1 $p |- ( ( ( I e. _om /\ J e. _om )
                          /\ ( K e. _om /\ L e. _om ) )
                           -> X e. ( Fmla ` 1o ) ) $=
      ( vi vj vk vn com wcel cv cgoe co cgna wceq wrex wo eqeq2d vx wa csn cgol
      c0 cxp cab cun c1o cfmla cfv simpll simplr simprl simprr wb oveq2d adantl
      oveq2 a1i rspcedvd orcd oveq1 oveq1d rexbidv goaleq12d orbi12d id rspc3ev
      eqidd syl31anc ovexi eqeq1 2rexbidv elab sylibr olcd elun fmla1 eleqtrrdi
      ) AKLZBKLZUBZCKLZDKLZUBZUBZEUEUCKKUFUFZUAMZGMZHMZNOZIMZJMZNOZPOZQZJKRZWIW
      LWMUDZQZSZIKRZHKRGKRZUAUGZUHZUIUJUKWGEWHLZEXDLZSEXELWGXGXFWGEWPQZJKRZEWSQ
      ZSZIKRZHKRGKRZXGWGWAWBWDEABNOZCWNNOZPOZQZJKRZEXNCUDZQZSZXMWAWBWFULWAWBWFU
      MWCWDWEUNWGXRXTWGXQEXNCDNOZPOZQZJDKWCWDWEUOWNDQZXQYDUPWGYEXPYCEYEXOYBXNPW
      NDCNUSUQTURYDWGFUTVAVBXKYAEAWKNOZWOPOZQZJKRZEYFWMUDZQZSEXNWOPOZQZJKRZEXNW
      MUDZQZSGHIABCKKKWJAQZXIYIXJYKYQXHYHJKYQWPYGEYQWLYFWOPWJAWKNVCZVDTVEYQWSYJ
      EYQWLYFWMWMYQWMVJYRVFTVGWKBQZYIYNYKYPYSYHYMJKYSYGYLEYSYFXNWOPWKBANUSZVDTV
      EYSYJYOEYSYFXNWMWMYSWMVJYTVFTVGWMCQZYNXRYPXTUUAYMXQJKUUAYLXPEUUAWOXOXNPWM
      CWNNVCUQTVEUUAYOXSEUUAXNXNWMCUUAVHUUAXNVJVFTVGVIVKXCXMUAEEXNYBPFVLWIEQZXB
      XLGHKKUUBXAXKIKUUBWRXIWTXJUUBWQXHJKWIEWPVMVEWIEWSVMVGVEVNVOVPVQEWHXDVRVPU
      AGHIJVSVT $.

    $d I a $.  $d J a $.  $d K a $.  $d L a $.  $d M a i $.  $d V a i $.
    $( The simplified satisfaction predicate at two Godel-sets of membership
       combined with a Godel-set for NAND. (Contributed by AV, 17-Nov-2023.) $)
    satefvfmla1 $p |- ( ( M e. V /\ ( I e. _om /\ J e. _om )
                                 /\ ( K e. _om /\ L e. _om ) ) -> ( M SatE X )
                   = { a e. ( M ^m _om ) | ( -. ( a ` I ) e. ( a ` J )
                                          \/ -. ( a ` K ) e. ( a ` L ) ) } ) $=
      ( wcel com wa co cep cfv c1o cvv syl wbr wi vi w3a csate cxp cin cv wn wo
      csat cmap crab wceq cgoe cgna ovexi jctr satefv ciun sqxpexg inex2g ancli
      3ad2ant1 satom fveq1d wfun cdm cfmla wf satfun ffund eqcomd funeqd mpbird
      cpw 1onn a1i 2goelgoanfmla1 3adant1 satfdmfmla mpd3an23 eleqtrrd fviunfun
      eqid syl3anc eqtrd satfv1fvfmla1 syl3an1 elmapi ffvelcdm ex anim12d com12
      brin 3ad2ant2 imp brxp sylibr biantrud fvex epeli bitr3di bitrid 3ad2ant3
      notbid orbi12d rabbidva 3eqtrd ) EFJZAKJZBKJZLZCKJZDKJZLZUBZEGUCMZGKENEEU
      DZUEZUIMZOZOZGPXSOZOZAHUFZOZBYDOZJZUGZCYDOZDYDOZJZUGZUHZHEKUJMZUKZXOXHGQJ
      ZLZXPYAULXHXKYQXNXHYPGABUMMCDUMMUNIUOUPVBGEFQUQRXOYAGUAKUAUFXSOURZOZYCXOG
      XTYRXOXHXRQJZLZXTYRULXHXKUUAXNXHYTXHXQQJYTEFUSXQNQUTRZVAZVBZUAXREFQVCRZVD
      XOYRVEZPKJZGYBVFZJYSYCULXOUUFXTVEXOKVGOZYNVNZXTXOUUAUUIUUJXTVHUUDXREFQVIR
      VJXOYRXTXOXTYRUUEVKVLVMUUGXOVOVPXOGPVGOZUUHXKXNGUUKJXHABCDGIVQVRXHXKUUHUU
      KULZXNXHYTUUGUULUUBUUGXHVOVPXREPFQVSVTVBWAYRUAXSKPGYRWCWBWDWEXOYCYEYFXRSZ
      UGZYIYJXRSZUGZUHZHYNUKZYOXHUUAXKXNYCUURULUUCXRABCDEFQGHIWFWGXOUUQYMHYNXOY
      DYNJZLZUUNYHUUPYLUUTUUMYGUUMYEYFNSZYEYFXQSZLZUUTYGYEYFNXQWMUUTUVAUVCYGUUT
      UVBUVAUUTYEEJZYFEJZLZUVBXOUUSUVFXKXHUUSUVFTXNUUSXKUVFUUSXIUVDXJUVEUUSKEYD
      VHZXIUVDTYDEKWHZUVGXIUVDKEAYDWIWJRUUSUVGXJUVETUVHUVGXJUVEKEBYDWIWJRWKWLWN
      WOYEYFEEWPWQWRYEYFBYDWSWTXAXBXDUUTUUOYKUUOYIYJNSZYIYJXQSZLZUUTYKYIYJNXQWM
      UUTUVIUVKYKUUTUVJUVIUUTYIEJZYJEJZLZUVJXOUUSUVNXNXHUUSUVNTXKUUSXNUVNUUSXLU
      VLXMUVMUUSUVGXLUVLTUVHUVGXLUVLKECYDWIWJRUUSUVGXMUVMTUVHUVGXMUVMKEDYDWIWJR
      WKWLXCWOYIYJEEWPWQWRYIYJDYDWSWTXAXBXDXEXFWEXG $.
  $}

  ${
    $d Z x $.
    ex-sategoelelomsuc.s $e |- S = ( x e. _om
                                     |-> if ( x = 2o , Z , suc Z ) ) $.
    $( Example of a valuation of a simplified satisfaction predicate over the
       ordinal numbers as model for a Godel-set of membership using the
       properties of a successor: ` ( S `` 2o ) = Z e. suc Z = ( S `` 2o ) ` .
       Remark: the indices ` 1o ` and ` 2o ` are intentionally reversed to
       distinguish them from elements of the model: ` ( 2o e.g 1o ) ` should
       not be confused with ` 2o e. 1o ` , which is false.  (Contributed by AV,
       19-Nov-2023.) $)
    ex-sategoelelomsuc $p |- ( Z e. _om -> S e. ( _om SatE ( 2o e.g 1o ) ) ) $=
      ( com wcel c2o c1o co cfv wceq cvv omex adantl 2onn fvmptd 1onn wa pm3.2i
      a1i cgoe csate cmap wf cv csuc id peano2 ifcld adantr fmptd elmapd mpbird
      cif sucidg cmpt iftrue 1one2o neii mtbiri iffalsed 3eltr4d wb sategoelfvb
      eqeq1 eqid mp1i mpbir2and ) CEFZBEGHUAIUBIZFZBEEUCIFZGBJZHBJZFZVIVLEEBUDV
      IAEAUEZGKZCCUFZUNZEBVIVSEFVPEFVIVQCVREVIUGZCUHZUIUJDUKVIEEBLLELFZVIMTZWCU
      LUMVICVRVMVNCEUOVIAGVSCEBEBAEVSUPKVIDTZVQVSCKVIVQCVRUQNGEFZVIOTVTPVIAHVSV
      REBEWDVPHKZVSVRKVIWFVQCVRWFVQHGKHGURUSVPHGVEUTVANHEFZVIQTWAPVBWBWEWGRZRVK
      VLVORVCVIWBWHMWEWGOQSSGHBVJELVJVFVDVGVH $.
  $}

  ${
    ex-sategoelel12.s $e |- S = ( x e. _om |-> if ( x = 2o , 1o , 2o ) ) $.
    $( Example of a valuation of a simplified satisfaction predicate over a
       proper pair (of ordinal numbers) as model for a Godel-set of membership
       using the properties of a successor:
       ` ( S `` 2o ) = 1o e. 2o = ( S `` 2o ) ` .  Remark: the indices ` 1o `
       and ` 2o ` are intentionally reversed to distinguish them from elements
       of the model: ` ( 2o e.g 1o ) ` should not be confused with
       ` 2o e. 1o ` , which is false.  (Contributed by AV, 19-Nov-2023.) $)
    ex-sategoelel12 $p |- S e. ( { 1o , 2o } SatE ( 2o e.g 1o ) ) $=
      ( c1o c2o cpr co wcel com cfv wa wceq 1oex mpbir 2onn fvmptg mp2an pm3.2i
      1onn cvv cgoe csate cmap wf cv cif prid1 2oex prid2 ifcli fmpti prex omex
      elmap csuc sucid df-2o eleqtrri iftrue 1one2o neii eqeq1 iffalsed 3eltr4i
      a1i mtbiri wb eqid sategoelfvb ) BDEFZEDUAGUBGZHZBVJIUCGHZEBJZDBJZHZKZVMV
      PVMIVJBUDAIVJAUEZELZDEUFZBCVTVJHVRIHVSDEVJDEMUGDEUHUIUJVEUKVJIBDEULZUMUNN
      DEVNVODDUOEDMUPUQUREIHZDIHZVNDLOSAEVTDIIBVSDEUSCPQWCWBVOELSOADVTEIIBVRDLZ
      VSDEWDVSDELDEUTVAVRDEVBVFVCCPQVDRVJTHWBWCKVLVQVGWAWBWCOSREDBVKVJTVKVHVIQN
      $.
  $}

$( --- theorems for ` M |= U ` --- $)

  ${
    $d M m u $.  $d U m u $.
    $( The "proves" relation on a set.  A wff encoded as ` U ` is true in a
       model ` M ` iff for every valuation ` s e. ( M ^m _om ) ` , the
       interpretation of the wff using the membership relation on ` M ` is
       true.  (Contributed by AV, 5-Nov-2023.) $)
    prv $p |- ( ( M e. V /\ U e. W )
                -> ( M |= U <-> ( M SatE U ) = ( M ^m _om ) ) ) $=
      ( vm vu cv csate co com cmap wceq cprv oveq12 simpl oveq1d eqeq12d df-prv
      wa brabga ) EGZFGZHIZUAJKIZLBAHIZBJKIZLEFBAMCDUABLZUBALZSZUCUEUDUFUABUBAH
      NUIUABJKUGUHOPQFERT $.
  $}

  ${
    $d A a $.  $d B a $.  $d M a $.  $d V a $.
    $( The wff ` ( A e. B -/\ B e. A ) ` encoded as ` ( ( A e.g B ) `
       ` |g ( B e.g A ) ) ` is true in any model ` M ` .  This is the model
       theoretic proof of ~ elnanel .  (Contributed by AV, 5-Nov-2023.) $)
    elnanelprv $p |- ( ( M e. V /\ A e. _om /\ B e. _om )
                       -> M |= ( ( A e.g B ) |g ( B e.g A ) ) ) $=
      ( va wcel com w3a cgoe co cgna cprv wbr csate cmap wceq cfv wn wa cvv a1i
      cv crab simp1 3simpc pm3.22 3adant1 eqid satefvfmla1 syl3anc wnan elnanel
      wo nanor mpbi rabeqc eqtrdi wb ovex prv sylancl mpbird ) CDFZAGFZBGFZHZCA
      BIJZBAIJZKJZLMZCVINJZCGOJZPZVFVKAEUBZQZBVNQZFZRVPVOFZRUMZEVLUCZVLVFVCVDVE
      SVEVDSZVKVTPVCVDVEUDZVCVDVEUEVDVEWAVCVDVEUFUGABBACDVIEVIUHUIUJVSEVLVSVNVL
      FVQVRUKVSVOVPULVQVRUNUOUAUPUQVFVCVITFVJVMURWBVGVHKUSVICDTUTVAVB $.
  $}

  ${
    $d U x $.
    $( Every wff encoded as ` U ` is true in an "empty model" ( ` M = (/) ` ).
       Since ` |= ` is defined in terms of the interpretations making the given
       formula true, it is not defined on the "empty model", since there are no
       interpretations.  In particular, the empty set on the LHS of ` |= `
       should not be interpreted as the empty model, because ` E. x x = x ` is
       not satisfied on the empty model.  (Contributed by AV, 19-Nov-2023.) $)
    prv0 $p |- ( U e. ( Fmla ` _om ) -> (/) |= U ) $=
      ( vx com cfmla cfv wcel c0 cprv wbr csate co wceq csat sate0 cv wn peano1
      wa cvv 0ex wal wf n0ii intnan a1i f00 sylnibr pm3.2i satfvel mp3an1 mtand
      alrimiv eq0 sylibr eqtrd cmap prv mpan wne ne0ii map0b mp1i eqeq2d mpbird
      wb bitrd ) ACDEZFZGAHIZGAJKZGLZVHVJACGGMKEEZGAVGNVHBOZVLFZPZBUAVLGLVHVOBV
      HVNCGVMUBZVHVMGLZCGLZRZVPVSPVHVRVQGCQUCUDUECVMUFUGGSFZVTRVHVNVPVTVTTTUHVM
      AGGSSUIUJUKULBVLUMUNUOVHVIVJGCUPKZLZVKVTVHVIWBVETAGSVGUQURVHWAGVJCGUSWAGL
      VHGCQUTCVAVBVCVFVD $.
  $}

  ${
    $d I a $.  $d J a $.  $d V a $.  $d X a $.
    $( No wff encoded as a Godel-set of membership is true in a model with only
       one element.  (Contributed by AV, 19-Nov-2023.) $)
    prv1n $p |- ( ( I e. _om /\ J e. _om /\ X e. V )
                  -> -. { X } |= ( I e.g J ) ) $=
      ( va com wcel co c0 wceq cxp mp1i cvv wa wb c2nd cfv c1st fveq2d eqtrd cv
      w3a csn cgoe cprv wbr cmap wex wn eqid omex snex xpex eqeq1 pm3.2i elmapg
      spcev fconst2g 3ad2ant3 bitrd exbidv mpbird neq0 sylibr eqcom sylnib ovex
      wf csate prv crab cfmla cop goel 0ex snid opelxpi opelxpd eqeltrd fmla0xp
      a1i eleqtrrdi 3adant3 satefvfmla0 sylancr opex op2nd eqtrdi op1stg op2ndg
      eleq12d rabbidv wi elmapi elirr fvconst 3ad2antr1 3ad2antr2 mtbiri ex syl
      wral impcom ralrimiva rabeq0 eqeq1d mtbird ) AFGZBFGZDCGZUBZDUCZABUDHZUEU
      FZIXLFUGHZJZXKXOIJZXPXKEUAZXOGZEUHZXQUIXKXTXRFXLKZJZEUHZYAYAJZYCXKYAUJYBY
      DEYAFXLUKDULZUMXRYAYAUNUQLXKXSYBEXKXSFXLXRVHZYBXLMGZFMGZNXSYFOXKYGYHYEUKU
      OXLFXRMMUPLXJXHYFYBOXIFDCXRURUSUTVAVBEXOVCVDXOIVEVFXKXNXLXMVIHZXOJZXPYGXM
      MGZNXNYJOXKYGYKYEABUDVGUOXMXLMMVJLXKYIIXOXKYIXMPQZRQZXRQZYLPQZXRQZGZEXOVK
      ZIXKYGXMIVLQZGZYIYRJYEXHXIYTXJXHXINZXMIUCZFFKZKZYSUUAXMIABVMZVMZUUDABVNZU
      UAIUUEUUBUUCIUUBGUUAIVOVPWAABFFVQVRVSVTWBWCXLMXMEWDWEXKYRAXRQZBXRQZGZEXOV
      KZIXHXIYRUUKJXJUUAYQUUJEXOUUAYNUUHYPUUIUUAYMAXRUUAYMUUERQAUUAYLUUERUUAYLU
      UFPQUUEUUAXMUUFPUUGSIUUEVOABWFWGWHZSABFFWITSUUAYOBXRUUAYOUUEPQBUUAYLUUEPU
      ULSABFFWJTSWKWLWCXKUUJUIZEXOXBUUKIJXKUUMEXOXSXKUUMXSYFXKUUMWMXRXLFWNYFXKU
      UMYFXKNZUUJDDGDWOUUNUUHDUUIDYFXIXHUUHDJXJFDAXRWPWQYFXHXIUUIDJXJFDBXRWPWRW
      KWSWTXAXCXDUUJEXOXEVDTTXFUTXG $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Godel-sets of formulas - part 2
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Introduce new constant symbols. $)
  $c =g $. $( Godel-set of equality $)
  $c /\g $. $( Godel-set of conjunction $)
  $c -.g $. $( Godel-set of negation $)
  $c ->g $. $( Godel-set of implication $)
  $c <->g $. $( Godel-set of equivalence $)
  $c \/g $. $( Godel-set of disjunction $)
  $c E.g $. $( Godel-set of existential quantification $)

  $( The Godel-set of negation.  (Note that this is not a wff.) $)
  cgon $a class -.g U $.

  $( The Godel-set of conjunction. $)
  cgoa $a class /\g $.

  $( The Godel-set of implication. $)
  cgoi $a class ->g $.

  $( The Godel-set of disjunction. $)
  cgoo $a class \/g $.

  $( The Godel-set of equivalence. $)
  cgob $a class <->g $.

  $( The Godel-set of equality. $)
  cgoq $a class =g $.

  $( The Godel-set of existential quantification.  (Note that this is not a
     wff.) $)
  cgox $a class E.g N U $.

  $( Define the Godel-set of negation.  Here the argument ` U ` is also a
     Godel-set corresponding to smaller formulas.  Note that this is a _class_
     expression, not a wff.  (Contributed by Mario Carneiro, 14-Jul-2013.) $)
  df-gonot $a |- -.g U = ( U |g U ) $.

  ${
    $d u v w $.
    $( Define the Godel-set of conjunction.  Here the arguments ` U ` and ` V `
       are also Godel-sets corresponding to smaller formulas.  (Contributed by
       Mario Carneiro, 14-Jul-2013.) $)
    df-goan $a |- /\g = ( u e. _V , v e. _V |-> -.g ( u |g v ) ) $.

    $( Define the Godel-set of implication.  Here the arguments ` U ` and ` V `
       are also Godel-sets corresponding to smaller formulas.  Note that this
       is a _class_ expression, not a wff.  (Contributed by Mario Carneiro,
       14-Jul-2013.) $)
    df-goim $a |- ->g = ( u e. _V , v e. _V |-> ( u |g -.g v ) ) $.

    $( Define the Godel-set of disjunction.  Here the arguments ` U ` and ` V `
       are also Godel-sets corresponding to smaller formulas.  Note that this
       is a _class_ expression, not a wff.  (Contributed by Mario Carneiro,
       14-Jul-2013.) $)
    df-goor $a |- \/g = ( u e. _V , v e. _V |-> ( -.g u ->g v ) ) $.

    $( Define the Godel-set of equivalence.  Here the arguments ` U ` and ` V `
       are also Godel-sets corresponding to smaller formulas.  Note that this
       is a _class_ expression, not a wff.  (Contributed by Mario Carneiro,
       14-Jul-2013.) $)
    df-gobi $a |- <->g = ( u e. _V , v e. _V |->
                           ( ( u ->g v ) /\g ( v ->g u ) ) ) $.

    $( Define the Godel-set of equality.  Here the arguments
       ` x = <. N , P >. ` correspond to v_N and v_P , so ` ( (/) =g 1o ) `
       actually means v_0 ` = ` v_1 , not ` 0 = 1 ` .  Here we use the trick
       mentioned in ~ ax-ext to introduce equality as a defined notion in terms
       of ` e.g ` .  The expression ` suc ( u u. v ) = ` max ` ( u , v ) + 1 `
       here is a convenient way of getting a dummy variable distinct from ` u `
       and ` v ` .  (Contributed by Mario Carneiro, 14-Jul-2013.) $)
    df-goeq $a |- =g = ( u e. _om , v e. _om |-> [_ suc ( u u. v ) / w ]_
                         A.g w ( ( w e.g u ) <->g ( w e.g v ) ) ) $.
  $}

  $( Define the Godel-set of existential quantification.  Here ` N e. _om `
     corresponds to v_N , and ` U ` represents another formula, and this
     expression is ` [ E. x ph ] = E.g N U ` where ` x ` is the ` N ` -th
     variable, ` U = [ ph ] ` is the code for ` ph ` .  Note that this is a
     _class_ expression, not a wff.  (Contributed by Mario Carneiro,
     14-Jul-2013.) $)
  df-goex $a |- E.g N U = -.g A.g N -.g U $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Models of ZF
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Introduce new constant symbols. $)
  $c AxExt $. $( The Axiom of Extensionality $)
  $c AxRep $. $( The Axiom Scheme of Replacement $)
  $c AxPow $. $( The Axiom of Power Sets $)
  $c AxUn $. $( The Axiom of Unions $)
  $c AxReg $. $( The Axiom of Regularity $)
  $c AxInf $. $( The Axiom of Infinity $)
  $c ZF $. $( The set of models of ZF $)

  $( The Axiom of Extensionality. $)
  cgze $a class AxExt $.

  $( The Axiom Scheme of Replacement. $)
  cgzr $a class AxRep $.

  $( The Axiom of Power Sets. $)
  cgzp $a class AxPow $.

  $( The Axiom of Unions. $)
  cgzu $a class AxUn $.

  $( The Axiom of Regularity. $)
  cgzg $a class AxReg $.

  $( The Axiom of Infinity. $)
  cgzi $a class AxInf $.

  $( The set of models of ZF. $)
  cgzf $a class ZF $.

  $( The Godel-set version of the Axiom of Extensionality.  (Contributed by
     Mario Carneiro, 14-Jul-2013.) $)
  df-gzext $a |- AxExt =
    ( A.g 2o ( ( 2o e.g (/) ) <->g ( 2o e.g 1o ) ) ->g ( (/) =g 1o ) ) $.

  $( The Godel-set version of the Axiom Scheme of Replacement.  Since this is a
     scheme and not a single axiom, it manifests as a function on wffs, each
     giving rise to a different axiom.  (Contributed by Mario Carneiro,
     14-Jul-2013.) $)
  df-gzrep $a |- AxRep = ( u e. ( Fmla ` _om ) |->
    ( A.g 3o E.g 1o A.g 2o ( A.g 1o u ->g ( 2o =g 1o ) ) ->g A.g 1o A.g 2o
      ( ( 2o e.g 1o ) <->g E.g 3o ( ( 3o e.g (/) ) /\g A.g 1o u ) ) ) ) $.

  $( The Godel-set version of the Axiom of Power Sets.  (Contributed by Mario
     Carneiro, 14-Jul-2013.) $)
  df-gzpow $a |- AxPow =
    E.g 1o A.g 2o ( A.g 1o ( ( 1o e.g 2o ) <->g ( 1o e.g (/) ) ) ->g
                    ( 2o e.g 1o ) ) $.

  $( The Godel-set version of the Axiom of Unions.  (Contributed by Mario
     Carneiro, 14-Jul-2013.) $)
  df-gzun $a |- AxUn =
    E.g 1o A.g 2o ( E.g 1o ( ( 2o e.g 1o ) /\g ( 1o e.g (/) ) ) ->g
                    ( 2o e.g 1o ) ) $.

  $( The Godel-set version of the Axiom of Regularity.  (Contributed by Mario
     Carneiro, 14-Jul-2013.) $)
  df-gzreg $a |- AxReg = ( E.g 1o ( 1o e.g (/) ) ->g
      E.g 1o ( ( 1o e.g (/) ) /\g
               A.g 2o ( ( 2o e.g 1o ) ->g -.g ( 2o e.g (/) ) ) ) ) $.

  $( The Godel-set version of the Axiom of Infinity.  (Contributed by Mario
     Carneiro, 14-Jul-2013.) $)
  df-gzinf $a |- AxInf = E.g 1o ( ( (/) e.g 1o ) /\g A.g 2o ( ( 2o e.g 1o ) ->g
      E.g (/) ( ( 2o e.g (/) ) /\g ( (/) e.g 1o ) ) ) ) $.

  ${
    $d m u $.
    $( Define the class of all (transitive) models of ZF. (Contributed by Mario
       Carneiro, 14-Jul-2013.) $)
    df-gzf $a |- ZF = { m | ( ( Tr m /\ m |= AxExt /\ m |= AxPow ) /\
                              ( m |= AxUn /\ m |= AxReg /\ m |= AxInf ) /\
                              A. u e. ( Fmla ` _om ) m |= ( AxRep ` u ) ) } $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Metamath formal systems
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  This is a formalization of Appendix C of the Metamath book, which describes
  the mathematical representation of a formal system, of which set.mm (this
  file) is one.

$)

  $c mCN $.
  $c mVR $.
  $c mType $.
  $c mTC $.
  $c mAx $.
  $c mVT $.
  $c mREx $.
  $c mEx $.
  $c mDV $.
  $c mVars $.
  $c mRSubst $.
  $c mSubst $.
  $c mVH $.
  $c mPreSt $.
  $c mStRed $.
  $c mStat $.
  $c mFS $.
  $c mCls $.
  $c mPPSt $.
  $c mThm $.

  $( The set of constants. $)
  cmcn $a class mCN $.

  $( The set of variables. $)
  cmvar $a class mVR $.

  $( The type function. $)
  cmty $a class mType $.

  $( The set of variable typecodes. $)
  cmvt $a class mVT $.

  $( The set of typecodes. $)
  cmtc $a class mTC $.

  $( The set of axioms. $)
  cmax $a class mAx $.

  $( The set of raw expressions. $)
  cmrex $a class mREx $.

  $( The set of expressions. $)
  cmex $a class mEx $.

  $( The set of distinct variables. $)
  cmdv $a class mDV $.

  $( The variables in an expression. $)
  cmvrs $a class mVars $.

  $( The set of raw substitutions. $)
  cmrsub $a class mRSubst $.

  $( The set of substitutions. $)
  cmsub $a class mSubst $.

  $( The set of variable hypotheses. $)
  cmvh $a class mVH $.

  $( The set of pre-statements. $)
  cmpst $a class mPreSt $.

  $( The reduct of a pre-statement. $)
  cmsr $a class mStRed $.

  $( The set of statements. $)
  cmsta $a class mStat $.

  $( The set of formal systems. $)
  cmfs $a class mFS $.

  $( The closure of a set of statements. $)
  cmcls $a class mCls $.

  $( The set of provable pre-statements. $)
  cmpps $a class mPPSt $.

  $( The set of theorems. $)
  cmthm $a class mThm $.

  $( Define the set of constants in a Metamath formal system.  (Contributed by
     Mario Carneiro, 14-Jul-2016.) $)
  df-mcn $a |- mCN = Slot 1 $.

  $( Define the set of variables in a Metamath formal system.  (Contributed by
     Mario Carneiro, 14-Jul-2016.) $)
  df-mvar $a |- mVR = Slot 2 $.

  $( Define the type function in a Metamath formal system.  (Contributed by
     Mario Carneiro, 14-Jul-2016.) $)
  df-mty $a |- mType = Slot 3 $.

  $( Define the set of typecodes in a Metamath formal system.  (Contributed by
     Mario Carneiro, 14-Jul-2016.) $)
  df-mtc $a |- mTC = Slot 4 $.

  $( Define the set of axioms in a Metamath formal system.  (Contributed by
     Mario Carneiro, 14-Jul-2016.) $)
  df-mmax $a |- mAx = Slot 5 $.

  $( Define the set of variable typecodes in a Metamath formal system.
     (Contributed by Mario Carneiro, 14-Jul-2016.) $)
  df-mvt $a |- mVT = ( t e. _V |-> ran ( mType ` t ) ) $.

  $( Define the set of "raw expressions", which are expressions without a
     typecode attached.  (Contributed by Mario Carneiro, 14-Jul-2016.) $)
  df-mrex $a |- mREx = ( t e. _V |-> Word ( ( mCN ` t ) u. ( mVR ` t ) ) ) $.

  $( Define the set of expressions, which are strings of constants and
     variables headed by a typecode constant.  (Contributed by Mario Carneiro,
     14-Jul-2016.) $)
  df-mex $a |- mEx = ( t e. _V |-> ( ( mTC ` t ) X. ( mREx ` t ) ) ) $.

  ${
    $d a c d e f h m o p s t v x y z $.
    $( Define the set of distinct variable conditions, which are pairs of
       distinct variables.  (Contributed by Mario Carneiro, 14-Jul-2016.) $)
    df-mdv $a |- mDV = ( t e. _V |->
      ( ( ( mVR ` t ) X. ( mVR ` t ) ) \ _I ) ) $.

    $( Define the set of variables in an expression.  (Contributed by Mario
       Carneiro, 14-Jul-2016.) $)
    df-mvrs $a |- mVars = ( t e. _V |-> ( e e. ( mEx ` t ) |->
        ( ran ( 2nd ` e ) i^i ( mVR ` t ) ) ) ) $.

    $( Define a substitution of raw expressions given a mapping from variables
       to expressions.  (Contributed by Mario Carneiro, 14-Jul-2016.) $)
    df-mrsub $a |- mRSubst = ( t e. _V |->
      ( f e. ( ( mREx ` t ) ^pm ( mVR ` t ) ) |-> ( e e. ( mREx ` t ) |->
        ( ( freeMnd ` ( ( mCN ` t ) u. ( mVR ` t ) ) ) gsum
    ( ( v e. ( ( mCN ` t ) u. ( mVR ` t ) ) |->
      if ( v e. dom f , ( f ` v ) , <" v "> ) ) o. e ) ) ) ) ) $.

    $( Define a substitution of expressions given a mapping from variables to
       expressions.  (Contributed by Mario Carneiro, 14-Jul-2016.) $)
    df-msub $a |- mSubst = ( t e. _V |->
      ( f e. ( ( mREx ` t ) ^pm ( mVR ` t ) ) |-> ( e e. ( mEx ` t ) |->
        <. ( 1st ` e ) , ( ( ( mRSubst ` t ) ` f ) ` ( 2nd ` e ) ) >. ) ) ) $.

    $( Define the mapping from variables to their variable hypothesis.
       (Contributed by Mario Carneiro, 14-Jul-2016.) $)
    df-mvh $a |- mVH = ( t e. _V |->
      ( v e. ( mVR ` t ) |-> <. ( ( mType ` t ) ` v ) , <" v "> >. ) ) $.

    $( Define the set of all pre-statements.  (Contributed by Mario Carneiro,
       14-Jul-2016.) $)
    df-mpst $a |- mPreSt = ( t e. _V |-> ( ( { d e. ~P ( mDV ` t ) | `' d = d }
      X. ( ~P ( mEx ` t ) i^i Fin ) ) X. ( mEx ` t ) ) ) $.

    $( Define the reduct of a pre-statement.  (Contributed by Mario Carneiro,
       14-Jul-2016.) $)
    df-msr $a |- mStRed = ( t e. _V |-> ( s e. ( mPreSt ` t ) |->
       [_ ( 2nd ` ( 1st ` s ) ) / h ]_ [_ ( 2nd ` s ) / a ]_
       <. ( ( 1st ` ( 1st ` s ) ) i^i
 [_ U. ( ( mVars ` t ) " ( h u. { a } ) ) / z ]_ ( z X. z ) ) , h , a >. ) ) $.

    $( Define the set of all statements.  (Contributed by Mario Carneiro,
       14-Jul-2016.) $)
    df-msta $a |- mStat = ( t e. _V |-> ran ( mStRed ` t ) ) $.

    $( Define the set of all formal systems.  (Contributed by Mario Carneiro,
       14-Jul-2016.) $)
    df-mfs $a |- mFS = { t |
      ( ( ( ( mCN ` t ) i^i ( mVR ` t ) ) = (/) /\
          ( mType ` t ) : ( mVR ` t ) --> ( mTC ` t ) ) /\
        ( ( mAx ` t ) C_ ( mStat ` t ) /\
          A. v e. ( mVT ` t ) -. ( `' ( mType ` t ) " { v } ) e. Fin ) ) } $.

    $( Define the closure of a set of statements relative to a set of
       disjointness constraints.  (Contributed by Mario Carneiro,
       14-Jul-2016.) $)
    df-mcls $a |- mCls = ( t e. _V |->
      ( d e. ~P ( mDV ` t ) , h e. ~P ( mEx ` t ) |->
        |^| { c | ( ( h u. ran ( mVH ` t ) ) C_ c /\
          A. m A. o A. p ( <. m , o , p >. e. ( mAx ` t ) ->
            A. s e. ran ( mSubst ` t )
      ( ( ( s " ( o u. ran ( mVH ` t ) ) ) C_ c /\
      A. x A. y ( x m y ->
        ( ( ( mVars ` t ) ` ( s ` ( ( mVH ` t ) ` x ) ) ) X.
          ( ( mVars ` t ) ` ( s ` ( ( mVH ` t ) ` y ) ) ) ) C_ d ) ) ->
        ( s ` p ) e. c ) ) ) } ) ) $.

    $( Define the set of provable pre-statements.  (Contributed by Mario
       Carneiro, 14-Jul-2016.) $)
    df-mpps $a |- mPPSt = ( t e. _V |-> { <. <. d , h >. , a >. |
      ( <. d , h , a >. e. ( mPreSt ` t ) /\ a e. ( d ( mCls ` t ) h ) ) } ) $.

    $( Define the set of theorems.  (Contributed by Mario Carneiro,
       14-Jul-2016.) $)
    df-mthm $a |- mThm = ( t e. _V |->
      ( `' ( mStRed ` t ) " ( ( mStRed ` t ) " ( mPPSt ` t ) ) ) ) $.
  $}

  ${
    $d t T $.
    mvtval.f $e |- V = ( mVT ` T ) $.
    mvtval.y $e |- Y = ( mType ` T ) $.
    $( The set of variable typecodes.  (Contributed by Mario Carneiro,
       18-Jul-2016.) $)
    mvtval $p |- V = ran Y $=
      ( vt cmvt cfv cmty crn cvv wcel wceq cv fveq2 rneqd df-mvt fvex c0 fvprc
      rnex fvmpt wn rn0 eqcomi 3eqtr4a pm2.61i rneqi 3eqtr4i ) AGHZAIHZJZBCJAKL
      ZUJULMFAFNZIHZJULKGUNAMUOUKUNAIOPFQUKAIRUAUBUMUCZSSJZUJULUQSUDUEAGTUPUKSA
      ITPUFUGDCUKEUHUI $.
  $}

  ${
    $d t C $.  $d t T $.  $d t V $.
    mrexval.c $e |- C = ( mCN ` T ) $.
    mrexval.v $e |- V = ( mVR ` T ) $.
    mrexval.r $e |- R = ( mREx ` T ) $.
    $( The set of "raw expressions", which are expressions without a typecode,
       that is, just sequences of constants and variables.  (Contributed by
       Mario Carneiro, 18-Jul-2016.) $)
    mrexval $p |- ( T e. W -> R = Word ( C u. V ) ) $=
      ( vt wcel cmrex cfv cun cword cvv wceq cmcn cmvar fveq2 eqtr4di wrdeq syl
      elex cv uneq12d df-mrex fvex unex wrdexi fvmpt3i eqtrid ) CEJZBCKLZADMZNZ
      HULCOJUMUOPCEUCICIUDZQLZUPRLZMZNZUOOKUPCPZUSUNPUTUOPVAUQAURDVAUQCQLAUPCQS
      FTVAURCRLDUPCRSGTUEUSUNUAUBIUFUSUQURUPQUGUPRUGUHUIUJUBUK $.
  $}

  ${
    $d t K $.  $d t R $.  $d t T $.
    mexval.k $e |- K = ( mTC ` T ) $.
    mexval.e $e |- E = ( mEx ` T ) $.
    ${
      mexval.r $e |- R = ( mREx ` T ) $.
      $( The set of expressions, which are pairs whose first element is a
         typecode, and whose second element is a raw expression.  (Contributed
         by Mario Carneiro, 18-Jul-2016.) $)
      mexval $p |- E = ( K X. R ) $=
        ( vt cmex cfv cxp cvv wceq cmtc cmrex fveq2 eqtr4di fvex c0 fvprc cv wn
        wcel xpeq12d df-mex xpex fvmpt3i xp0 eqcomi eqtrid xpeq2d 3eqtr4a eqtri
        pm2.61i ) CBIJZDAKZFBLUCZUOUPMHBHUAZNJZUROJZKUPLIURBMZUSDUTAVAUSBNJDURB
        NPEQVAUTBOJZAURBOPGQUDHUEUSUTURNRURORUFUGUQUBZSDSKZUOUPVDSDUHUIBITVCASD
        VCAVBSGBOTUJUKULUNUM $.
    $}

    mexval2.c $e |- C = ( mCN ` T ) $.
    mexval2.v $e |- V = ( mVR ` T ) $.
    $( The set of expressions, which are pairs whose first element is a
       typecode, and whose second element is a list of constants and variables.
       (Contributed by Mario Carneiro, 18-Jul-2016.) $)
    mexval2 $p |- E = ( K X. Word ( C u. V ) ) $=
      ( cvv wcel cun cword cxp cfv eqtrid c0 cmex fvprc cmtc wceq cmrex mrexval
      eqid mexval xpeq2d wn 0xp eqcomi xpeq1d 3eqtr4a pm2.61i ) BJKZCDAELMZNZUA
      UMCDBUBOZNUOUPBCDFGUPUDZUEUMUPUNDAUPBEJHIUQUCUFPUMUGZQQUNNZCUOUSQUNUHUIUR
      CBROQGBRSPURDQUNURDBTOQFBTSPUJUKUL $.
  $}

  ${
    $d t T $.  $d t V $.
    mdvval.v $e |- V = ( mVR ` T ) $.
    mdvval.d $e |- D = ( mDV ` T ) $.
    $( The set of disjoint variable conditions, which are pairs of distinct
       variables.  (This definition differs from appendix C, which uses
       unordered pairs instead.  We use ordered pairs, but all sets of disjoint
       variable conditions of interest will be symmetric, so it does not
       matter.)  (Contributed by Mario Carneiro, 18-Jul-2016.) $)
    mdvval $p |- D = ( ( V X. V ) \ _I ) $=
      ( vt cmdv cfv cxp cid cdif cvv wcel wceq cv cmvar fveq2 difeq1d c0 fvprc
      eqtr4di sqxpeqd df-mdv fvex xpex difexg fvmpt3i 0dif eqcomi eqtrid xpeq2d
      ax-mp wn xp0 eqtrdi 3eqtr4a pm2.61i eqtri ) ABGHZCCIZJKZEBLMZUSVANFBFOZPH
      ZVDIZJKZVALGVCBNZVEUTJVGVDCVGVDBPHZCVCBPQDUAUBRFUCVELMVFLMVDVDVCPUDZVIUEV
      EJLUFULUGVBUMZSSJKZUSVAVKSJUHUIBGTVJUTSJVJUTCSISVJCSCVJCVHSDBPTUJUKCUNUOR
      UPUQUR $.
  $}

  ${
    $d e t E $.  $d e t T $.  $d e t V $.  $d e X $.
    mvrsval.v $e |- V = ( mVR ` T ) $.
    mvrsval.e $e |- E = ( mEx ` T ) $.
    mvrsval.w $e |- W = ( mVars ` T ) $.
    $( The set of variables in an expression.  (Contributed by Mario Carneiro,
       18-Jul-2016.) $)
    mvrsval $p |- ( X e. E -> ( W ` X ) = ( ran ( 2nd ` X ) i^i V ) ) $=
      ( ve vt wcel cv c2nd cfv cin cvv wceq cmex cmvar fveq2 cmpt elfvex eleq2s
      crn cmvrs eqtr4di ineq2d mpteq12dv df-mvrs syl eqtrid rneqd ineq1d adantl
      mptfvmpt id fvex rnex inex1 a1i fvmptd ) EBKZIEILZMNZUDZCOZEMNZUDZCOZBDPV
      BDAUENZIBVFUAZHVBAPKZVJVKQVLEARNZBEARUBGUCIJVFRUEIJLZRNZVEVNSNZOZUABPAAVN
      AQZIVOVQBVFVRVOVMBVNARTGUFVRVPCVEVRVPASNCVNASTFUFUGUHJIUIGUOUJUKVCEQZVFVI
      QVBVSVEVHCVSVDVGVCEMTULUMUNVBUPVIPKVBVHCVGEMUQURUSUTVA $.

    $( The set of variables in an expression is a finite subset of ` V ` .
       (Contributed by Mario Carneiro, 18-Jul-2016.) $)
    mvrsfpw $p |- ( X e. E -> ( W ` X ) e. ( ~P V i^i Fin ) ) $=
      ( wcel cfv c2nd crn cin cpw cfn mvrsval wss inss2 cc0 eqid a1i chash cfzo
      co wfo fzofi wfn cmcn cun cword wf cmtc cxp xp2nd mexval2 eleq2s wrdf ffn
      3syl dffn4 sylib fofi sylancr inss1 ssfi sylancl elfpw sylanbrc eqeltrd )
      EBIZEDJEKJZLZCMZCNOMZABCDEFGHPVJVMCQZVMOIZVMVNIVOVJVLCRUAVJVLOIZVMVLQVPVJ
      SVKUBJZUCUDZOIVSVLVKUEZVQSVRUFVJVKVSUGZVTVJVKAUHJZCUIZUJZIZVSWCVKUKWAWEEA
      ULJZWDUMBEWFWDUNWBABWFCWFTGWBTFUOUPWCVKUQVSWCVKURUSVSVKUTVAVSVLVKVBVCVLCV
      DVLVMVEVFVMCVGVHVI $.
  $}

  ${
    $d e f v A $.  $d e f t v C $.  $d e f v F $.  $d e f t v R $.  $d e v X $.
    $d e f t G $.  $d e f t v T $.  $d e f t v V $.
    mrsubffval.c $e |- C = ( mCN ` T ) $.
    mrsubffval.v $e |- V = ( mVR ` T ) $.
    mrsubffval.r $e |- R = ( mREx ` T ) $.
    mrsubffval.s $e |- S = ( mRSubst ` T ) $.
    ${
      mrsubffval.g $e |- G = ( freeMnd ` ( C u. V ) ) $.
      $( The substitution of some variables for expressions in a raw
         expression.  (Contributed by Mario Carneiro, 18-Jul-2016.) $)
      mrsubffval $p |- ( T e. W -> S = ( f e. ( R ^pm V ) |-> ( e e. R |->
        ( G gsum ( ( v e. ( C u. V ) |->
          if ( v e. dom f , ( f ` v ) , <" v "> ) ) o. e ) ) ) ) ) $=
        ( cfv cpm co cv cmpt vt wcel cmrsub cun cdm cs1 cif ccom cgsu wceq elex
        cvv cmrex cmvar cmcn cfrmd fveq2 eqtr4di oveq12d uneq12d fveq2d mpteq1d
        coeq1d mpteq12dv df-mrsub ovex mptex fvmpt syl eqtrid ) EJUBZDEUCPZGCIQ
        RZFCHABIUDZASZGSZUEUBVOVPPVOUFUGZTZFSZUHZUIRZTZTZNVKEULUBVLWCUJEJUKUAEG
        UASZUMPZWDUNPZQRZFWEWDUOPZWFUDZUPPZAWIVQTZVSUHZUIRZTZTWCULUCWDEUJZGWGWN
        VMWBWOWECWFIQWOWEEUMPCWDEUMUQMURZWOWFEUNPIWDEUNUQLURZUSWOFWEWMCWAWPWOWJ
        HWLVTUIWOWJVNUPPHWOWIVNUPWOWHBWFIWOWHEUOPBWDEUOUQKURWQUTZVAOURWOWKVRVSW
        OAWIVNVQWRVBVCUSVDVDAUAFGVEGVMWBCIQVFVGVHVIVJ $.

      $( The substitution of some variables for expressions in a raw
         expression.  (Contributed by Mario Carneiro, 18-Jul-2016.) $)
      mrsubfval $p |- ( ( F : A --> R /\ A C_ V ) -> ( S ` F ) = ( e e. R |->
        ( G gsum ( ( v e. ( C u. V ) |->
          if ( v e. A , ( F ` v ) , <" v "> ) ) o. e ) ) ) ) $=
        ( cvv wcel cfv cmpt c0 vf wf wss wa cun cv cs1 cif ccom cgsu co wceq wi
        cdm cpm mrsubffval adantr dmeq ad2antrl sylan9eqr eleq2d simpr ifbieq1d
        fdm fveq1d mpteq2dv coeq1d oveq2d cmrex fvexi a1i cmvar simprl syl22anc
        simprr elpm2r mptex fvmptd ex wn 0fv cmrsub fvprc eqtrid mpteq1d eqtrdi
        mpt0 3eqtr4a a1d pm2.61i ) FPQZBDHUBZBJUCZUDZHERZGDIACJUEZAUFZBQZWQHRZW
        QUGZUHZSZGUFZUIZUJUKZSZULZUMWKWNXGWKWNUDZUAHGDIAWPWQUAUFZUNZQZWQXIRZWTU
        HZSZXCUIZUJUKZSZXFDJUOUKZEPWKEUAXRXQSULWNACDEFGUAIJPKLMNOUPUQXHXIHULZUD
        ZGDXPXEXTXOXDIUJXTXNXBXCXTAWPXMXAXTXKWRXLWSWTXTXJBWQXSXHXJHUNZBXIHURWLY
        ABULWKWMBDHVDUSUTVAXTWQXIHXHXSVBVEVCVFVGVHVFXHDPQZJPQZWLWMHXRQYBXHDFVIM
        VJZVKYCXHJFVLLVJVKWKWLWMVMWKWLWMVODJBHPPVPVNXFPQXHGDXEYDVQVKVRVSWKVTZXG
        WNYEHTRTWOXFHWAYEHETYEEFWBRTNFWBWCWDVEYEXFGTXESTYEGDTXEYEDFVIRTMFVIWCWD
        WEGXEWGWFWHWIWJ $.

      $( The substitution of some variables for expressions in a raw
         expression.  (Contributed by Mario Carneiro, 18-Jul-2016.) $)
      mrsubval $p |- ( ( F : A --> R /\ A C_ V /\ X e. R ) ->
        ( ( S ` F ) ` X ) = ( G gsum ( ( v e. ( C u. V ) |->
          if ( v e. A , ( F ` v ) , <" v "> ) ) o. X ) ) ) $=
        ( ve wcel cv cfv cgsu wf wss w3a cun cs1 cif cmpt ccom co cvv mrsubfval
        wceq 3adant3 wa simpr coeq2d oveq2d simp3 ovexd fvmptd ) BDGUAZBIUBZJDQ
        ZUCZPJHACIUDARZBQVEGSVEUEUFUGZPRZUHZTUIZHVFJUHZTUIDGESZUJVAVBVKPDVIUGUL
        VCABCDEFPGHIKLMNOUKUMVDVGJULZUNZVHVJHTVMVGJVFVDVLUOUPUQVAVBVCURVDHVJTUS
        UT $.
    $}

    $( The value of a substituted singleton.  (Contributed by Mario Carneiro,
       18-Jul-2016.) $)
    mrsubcv $p |- ( ( F : A --> R /\ A C_ V /\ X e. ( C u. V ) ) ->
      ( ( S ` F ) ` <" X "> ) = if ( X e. A , ( F ` X ) , <" X "> ) ) $=
      ( vv wcel cs1 cfv cgsu wceq cvv cmcn wf wss cun w3a cfrmd cv cmpt ccom co
      cword simp3 s1cld wo elun elfvex eleq2s cmvar jaoi sylbi 3ad2ant3 mrexval
      cif eleqtrrd eqid mrsubval syld3an3 wa simpl1 ffvelcdmda ad2antrr eleqtrd
      syl wn simplr ifclda fmpttd s1co syl2anc eleq1 fveq2 s1eq ifbieq12d s1cli
      fvex elexi ifex fvmpt s1eqd eqtrd oveq2d ffvelcdmd eqeltrrd fvexi frmdbas
      cbs unex ax-mp eqcomi gsumws1 3eqtrd ) ACFUAZAGUBZHBGUCZNZUDZHOZFDPPZXCUE
      PZMXCMUFZANZXIFPZXIOZVBZUGZXFUHZQUIZXHHANZHFPZXFVBZOZQUIZXSXAXBXDXFCNXGXP
      RXEXFXCUJZCXEHXCXAXBXDUKZULXEESNZCYBRZXDXAYDXBXDHBNZHGNZUMYDHBGUNYFYDYGYD
      HETPBHETUOIUPYDHEUQPGHEUQUOJUPURUSUTBCEGSIJKVAVLZVCMABCDEFXHGXFIJKLXHVDZV
      EVFXEXOXTXHQXEXOHXNPZOZXTXEXDXCYBXNUAXOYKRYCXEMXCXMYBXEXIXCNZVGZXJXKXLYBY
      MXJVGXKCYBYMACXIFXAXBXDYLVHVIXEYEYLXJYHVJVKYMXJVMZVGXIXCXEYLYNVNULVOVPZXC
      YBHXNVQVRXEYJXSXDXAYJXSRXBMHXMXSXCXNXIHRXJXQXKXLXRXFXIHAVSXIHFVTXIHWAWBXN
      VDXQXRXFHFWDXFSUJHWCWEWFWGUTZWHWIWJXEXSYBNYAXSRXEYJXSYBYPXEXCYBHXNYOYCWKW
      LYBXSXHXHWOPZYBXCSNYQYBRBGBETIWMGEUQJWMWPYQXCXHSYIYQVDWNWQWRWSVLWT $.
  $}

  ${
    $d e f g v x R $.  $d e f g v x T $.  $d e f g v x V $.  $d e f g v W $.
    $d f g v S $.
    mrsubvr.v $e |- V = ( mVR ` T ) $.
    mrsubvr.r $e |- R = ( mREx ` T ) $.
    mrsubvr.s $e |- S = ( mRSubst ` T ) $.
    $( The value of a substituted variable.  (Contributed by Mario Carneiro,
       18-Jul-2016.) $)
    mrsubvr $p |- ( ( F : A --> R /\ A C_ V /\ X e. A ) ->
      ( ( S ` F ) ` <" X "> ) = ( F ` X ) ) $=
      ( wf wss wcel w3a cs1 cfv cif cmcn cun wceq ssun2 simp2 simp3 sseldd eqid
      sselid mrsubcv syld3an3 iftrue 3ad2ant3 eqtrd ) ABEKZAFLZGAMZNZGOZECPPZUN
      GEPZUPQZURULUMUNGDRPZFSZMUQUSTUOFVAGFUTUAUOAFGULUMUNUBULUMUNUCUDUFAUTBCDE
      FGUTUEHIJUGUHUNULUSURTUMUNURUPUIUJUK $.

    $( A substitution is a function from ` R ` to ` R ` .  (Contributed by
       Mario Carneiro, 18-Jul-2016.) $)
    mrsubff $p |- ( T e. W -> S : ( R ^pm V ) --> ( R ^m R ) ) $=
      ( vf ve vv wcel co wf cfv cv cmpt wa cvv eqid cpm cmap cmcn cun cfrmd cdm
      cs1 ccom cgsu cword cmnd fvex cmvar fvexi unex frmdmnd mp1i simpr mrexval
      cif ad2antrr eleqtrd wss elpmi simpld ad3antlr ffvelcdmda wn simplr s1cld
      wceq ifclda fmpttd wrdco syl2anc cbs frmdbas ax-mp gsumwcl eleqtrrd cmrex
      eqcomi elmap sylibr mrsubffval feq1d mpbird ) CELZADUAMZAAUBMZBNWIWJIWIJA
      CUCOZDUDZUEOZKWLKPZIPZUFZLZWNWOOZWNUGZUTZQZJPZUHZUIMZQZQZNWHIWIXEWJWHWOWI
      LZRZAAXENXEWJLXHJAXDAXHXBALZRZXDWLUJZAXJWMUKLZXCXKUJLZXDXKLWLSLZXLXJWKDCU
      CULDCUMFUNUOZWLWMSWMTZUPUQXJXBXKLWLXKXANXMXJXBAXKXHXIURWHAXKVKZXGXIWKACDE
      WKTZFGUSVAZVBXJKWLWTXKXJWNWLLZRZWQWRWSXKYAWQRWRAXKYAWPAWNWOXGWPAWONZWHXIX
      TXGYBWPDVCADWOVDVEVFVGXJXQXTWQXSVAVBYAWQVHZRWNWLXJXTYCVIVJVLVMWLXKXAXBVNV
      OXKWMXCWMVPOZXKXNYDXKVKXOYDWLWMSXPYDTVQVRWBVSVOXSVTVMAAXEACWAGUNZYEWCWDVM
      WHWIWJBXFKWKABCJIWMDEXRFGHXPWEWFWG $.

    $( Although it is defined for partial mappings of variables, every partial
       substitution is a substitution on some complete mapping of the
       variables.  (Contributed by Mario Carneiro, 18-Jul-2016.) $)
    mrsubrn $p |- ran S = ( S " ( R ^m V ) ) $=
      ( vf vx ve vv co cvv wcel wss cfv wa cif cmpt wceq crn cmap cima cpm wral
      wfn cv wf mrsubff ffnd cdm cs1 cmcn cun cfrmd ccom cgsu eleq1w fveq2 s1eq
      ifbieq12d eqid fvex cword s1cli elexi fvmpt adantl ifeq1da eqtr4di simprd
      ifex ifan elpmi sseld pm4.71rd bicomd ifbid eqtr2d mpteq2dv coeq1d oveq2d
      mrsubfval simpld adantr ffvelcdmda elun2 ad2antlr s1cld mrexval ad3antrrr
      syl eleqtrrd ifclda fmpttd ssid sylancl 3eqtr4d mapsspm cmrex fvexi cmvar
      wn a1i elmap sylibr fnfvima syl3anc eqeltrd ralrimiva ffnfv sylanbrc frnd
      c0 cmrsub rnfvprc 0ss eqsstrdi pm2.61i imassrn eqssi ) BUAZBADUBLZUCZCMNZ
      YBYDOYEADUDLZYDBYEBYFUFZHUGZBPZYDNZHYFUEYFYDBUHYEYFAAUBLBABCDMEFGUIUJZYEY
      JHYFYEYHYFNZQZYIIDIUGZYHUKZNZYNYHPZYNULZRZSZBPZYDYMJACUMPZDUNZUOPZKUUCKUG
      ZYONZUUEYHPZUUEULZRZSZJUGZUPZUQLZSZJAUUDKUUCUUEDNZUUEYTPZUUHRZSZUUKUPZUQL
      ZSZYIUUAYMJAUUMUUTYMUULUUSUUDUQYMUUJUURUUKYMKUUCUUIUUQYMUUQUUOUUFQZUUGUUH
      RZUUIYMUUQUUOUUIUUHRUVCYMUUOUUPUUIUUHUUOUUPUUITYMIUUEYSUUIDYTYNUUETYPUUFY
      QYRUUGUUHIKYOURYNUUEYHUSYNUUEUTVAYTVBUUFUUGUUHUUEYHVCUUHMVDUUEVEVFVLVGVHV
      IUUOUUFUUGUUHVMVJYMUVBUUFUUGUUHYMUUFUVBYMUUFUUOYMYODUUEYMYOAYHUHZYODOZYLU
      VDUVEQZYEADYHVNVHZVKVOVPVQVRVSVTWAWBVTYMUVFYIUUNTUVGKYOUUBABCJYHUUDDUUBVB
      ZEFGUUDVBZWCWLYMDAYTUHZDDOUUAUVATYMIDYSAYMYNDNZQZYPYQYRAUVLYOAYNYHYMUVDUV
      KYMUVDUVEUVGWDWEWFUVLYPXCZQZYRUUCVDZAUVNYNUUCUVKYNUUCNYMUVMYNDUUBWGWHWIYE
      AUVOTYLUVKUVMUUBACDMUVHEFWJWKWMWNWOZDWPKDUUBABCJYTUUDDUVHEFGUVIWCWQWRYMYG
      YCYFOZYTYCNZUUAYDNYEYGYLYKWEUVQYMADWSXDYMUVJUVRUVPADYTACWTFXADCXBEXAXEXFY
      FYCBYTXGXHXIXJHYFYDBXKXLXMYEXCYBXNYDXOCBGXPYDXQXRXSBYCXTYA $.

    $( When restricted to complete mappings, the substitution-producing
       function is one-to-one.  (Contributed by Mario Carneiro,
       18-Jul-2016.) $)
    mrsubff1 $p |- ( T e. W ->
      ( S |` ( R ^m V ) ) : ( R ^m V ) -1-1-> ( R ^m R ) ) $=
      ( vf vg vv wcel cmap co wf cv cfv wceq wral wa wi wf1 cpm mrsubff mapsspm
      cres wss a1i fssresd cs1 fveq1 simplrl elmapi ssidd simpr mrsubvr syl3anc
      syl simplrr eqeq12d imbitrid ralrimdva wb eqeqan12d adantl wfn ffn eqfnfv
      fvres syl2an 3imtr4d ralrimivva dff13 sylanbrc ) CELZADMNZAAMNZBVPUFZOIPZ
      VRQZJPZVRQZRZVSWARZUAZJVPSIVPSVPVQVRUBVOADUCNZVQVPBABCDEFGHUDVPWFUGVOADUE
      UHUIVOWEIJVPVPVOVSVPLZWAVPLZTZTZVSBQZWABQZRZKPZVSQZWNWAQZRZKDSZWCWDWJWMWQ
      KDWMWNUJZWKQZWSWLQZRWJWNDLZTZWQWSWKWLUKXCWTWOXAWPXCDAVSOZDDUGZXBWTWORXCWG
      XDVOWGWHXBULVSADUMZURXCDUNZWJXBUOZDABCVSDWNFGHUPUQXCDAWAOZXEXBXAWPRXCWHXI
      VOWGWHXBUSWAADUMZURXGXHDABCWADWNFGHUPUQUTVAVBWIWCWMVCVOWGWHVTWKWBWLVSVPBV
      IWAVPBVIVDVEWIWDWRVCZVOWGXDXIXKWHXFXJXDVSDVFWADVFXKXIDAVSVGDAWAVGKDVSWAVH
      VJVJVEVKVLIJVPVQVRVMVN $.

    $( When restricted to complete mappings, the substitution-producing
       function is bijective to the set of all substitutions.  (Contributed by
       Mario Carneiro, 18-Jul-2016.) $)
    mrsubff1o $p |- ( T e. W ->
      ( S |` ( R ^m V ) ) : ( R ^m V ) -1-1-onto-> ran S ) $=
      ( wcel cmap co cres crn wf1o wf1 mrsubff1 f1f1orn syl wceq wb cima df-ima
      mrsubrn eqtri f1oeq3 ax-mp sylibr ) CEIZADJKZBUILZMZUJNZUIBMZUJNZUHUIAAJK
      ZUJOULABCDEFGHPUIUOUJQRUMUKSUNULTUMBUIUAUKABCDFGHUCBUIUBUDUMUKUIUJUEUFUG
      $.
  $}

  ${
    $d c f r v x y C $.  $d f r v x y R $.  $d c f x y S $.  $d f r v x y T $.
    $d c f r v w x y F $.  $d c f r v w x y V $.  $d r v x y W $.  $d f v X $.
    $d f v Y $.
    mrsubccat.s $e |- S = ( mRSubst ` T ) $.
    $( The value of the substituted empty string.  (Contributed by Mario
       Carneiro, 18-Jul-2016.) $)
    mrsub0 $p |- ( F e. ran S -> ( F ` (/) ) = (/) ) $=
      ( vf vv crn wcel cvv cv cfv wceq cmrex cmvar cmap co c0 wf eqid cgsu wrex
      n0i cmrsub rnfvprc nsyl2 wfun cima cpm mrsubff ffun mrsubrn eleq2i biimpi
      3syl fvelima syl2anc wa cmcn cun cfrmd cs1 cif cmpt ccom wss elmapi ssidd
      adantl cword mrexval adantr eleqtrrid mrsubval syl3anc oveq2i frmd0 gsum0
      wrd0 co02 eqtri eqtrdi fveq1 eqeq1d syl5ibcom rexlimdva sylc ) CAGZHZBIHZ
      EJZAKZCLZEBMKZBNKZOPZUAZQCKZQLZWHWGQLWIWGCUBUCBADUDUEZWHAUFZCAWOUGZHZWPWH
      WIWMWNUHPZWMWMOPZARWTWSWMABWNIWNSZWMSZDUIXCXDAUJUNWHXBWGXACWMABWNXEXFDUKU
      LUMECWOAUOUPWIWLWREWOWIWJWOHZUQZQWKKZQLWLWRXHXIBURKZWNUSZUTKZFXKFJZWNHXMW
      JKXMVAVBVCZQVDZTPZQXHWNWMWJRZWNWNVEQWMHXIXPLXGXQWIWJWMWNVFVHXHWNVGXHQXKVI
      ZWMXKVRWIWMXRLXGXJWMBWNIXJSZXEXFVJVKVLFWNXJWMABWJXLWNQXSXEXFDXLSZVMVNXPXL
      QTPQXOQXLTXNVSVOXLQXKXLXTVPVQVTWAWLXIWQQQWKCWBWCWDWEWF $.

    mrsubccat.r $e |- R = ( mREx ` T ) $.
    $( A substitution is a function.  (Contributed by Mario Carneiro,
       18-Jul-2016.) $)
    mrsubf $p |- ( F e. ran S -> F : R --> R ) $=
      ( crn wcel cmap co wf cvv cmvar cfv cpm wss c0 wceq n0i cmrsub nsyl2 eqid
      rnfvprc mrsubff frn 3syl id sseldd elmapi syl ) DBGZHZDAAIJZHAADKULUKUMDU
      LCLHZACMNZOJZUMBKUKUMPULUKQRUNUKDSTCBEUCUAABCUOLUOUBFEUDUPUMBUEUFULUGUHDA
      AUIUJ $.

    $( Substitution distributes over concatenation.  (Contributed by Mario
       Carneiro, 18-Jul-2016.) $)
    mrsubccat $p |- ( ( F e. ran S /\ X e. R /\ Y e. R ) ->
      ( F ` ( X ++ Y ) ) = ( ( F ` X ) ++ ( F ` Y ) ) ) $=
      ( vv wcel cconcat co cfv wceq wa cvv eqid syl2anc cgsu syl3anc vf cv cmap
      crn cmvar wrex wi wfun cima cpm wf c0 n0i rnfvprc nsyl2 mrsubff ffun 3syl
      cmrsub mrsubrn eleq2i biimpi fvelima cmcn cun cfrmd cs1 cmpt cplusg cword
      ccom simprl elfvex eleq2s mrexval eleqtrd simprr elmapi adantr ffvelcdmda
      cmrex ad2antrr wn simplr s1cld ifclda fmpttd ccatco oveq2d cmnd fvex unex
      cif frmdmnd mp1i wrdco cbs frmdbas eqcomi gsumccat gsumwcl frmdadd 3eqtrd
      ax-mp wss ssidd eleqtrrd mrsubval oveq12d 3eqtr4d fveq1 eqeq12d syl5ibcom
      ccatcl ex com23 rexlimiv syl 3impib ) DBUDZJZEAJZFAJZEFKLZDMZEDMZFDMZKLZN
      ZYAUAUBZBMZDNZUAACUEMZUCLZUFZYBYCOZYIUGZYABUHZDBYNUIZJZYOYACPJZAYMUJLZAAU
      CLZBUKYRYAXTULNUUAXTDUMUSCBGUNUOABCYMPYMQZHGUPUUBUUCBUQURYAYTXTYSDABCYMUU
      DHGUTVAVBUADYNBVCRYLYQUAYNYJYNJZYPYLYIUUEYPYLYIUGUUEYPOZYDYKMZEYKMZFYKMZK
      LZNYLYIUUFCVDMZYMVEZVFMZIUULIUBZYMJZUUNYJMZUUNVGZWMZVHZYDVKZSLZUUMUUSEVKZ
      SLZUUMUUSFVKZSLZKLZUUGUUJUUFUVAUUMUVBUVDKLZSLZUVCUVEUUMVIMZLZUVFUUFUUTUVG
      UUMSUUFEUULVJZJZFUVKJZUULUVKUUSUKZUUTUVGNUUFEAUVKUUEYBYCVLZUUFYBUUAAUVKNZ
      UVOUUAECWAMAECWAVMHVNUUKACYMPUUKQZUUDHVOURZVPZUUFFAUVKUUEYBYCVQZUVRVPZUUF
      IUULUURUVKUUFUUNUULJZOZUUOUUPUUQUVKUWCUUOOUUPAUVKUWCYMAUUNYJUUFYMAYJUKZUW
      BUUEUWDYPYJAYMVRVSZVSVTUUFUVPUWBUUOUVRWBVPUWCUUOWCZOUUNUULUUFUWBUWFWDWEWF
      WGZUULUVKEFUUSWHTWIUUFUUMWJJZUVBUVKVJZJZUVDUWIJZUVHUVJNUULPJZUWHUUFUUKYMC
      VDWKCUEWKWLZUULUUMPUUMQZWNWOZUUFUVLUVNUWJUVSUWGUULUVKUUSEWPRZUUFUVMUVNUWK
      UWAUWGUULUVKUUSFWPRZUVKUVIUUMUVBUVDUUMWQMZUVKUWLUWRUVKNUWMUWRUULUUMPUWNUW
      RQWRXDWSZUVIQZWTTUUFUVCUVKJZUVEUVKJZUVJUVFNUUFUWHUWJUXAUWOUWPUVKUUMUVBUWS
      XARUUFUWHUWKUXBUWOUWQUVKUUMUVDUWSXARUVKUVIUULUUMUVCUVEUWNUWSUWTXBRXCUUFUW
      DYMYMXEZYDAJUUGUVANUWEUUFYMXFZUUFYDUVKAUUFUVLUVMYDUVKJUVSUWAUULEFXNRUVRXG
      IYMUUKABCYJUUMYMYDUVQUUDHGUWNXHTUUFUUHUVCUUIUVEKUUFUWDUXCYBUUHUVCNUWEUXDU
      VOIYMUUKABCYJUUMYMEUVQUUDHGUWNXHTUUFUWDUXCYCUUIUVENUWEUXDUVTIYMUUKABCYJUU
      MYMFUVQUUDHGUWNXHTXIXJYLUUGYEUUJYHYDYKDXKYLUUHYFUUIYGKEYKDXKFYKDXKXIXLXMX
      OXPXQXRXS $.

    mrsubcn.v $e |- V = ( mVR ` T ) $.
    mrsubcn.c $e |- C = ( mCN ` T ) $.
    $( A substitution does not change the value of constant substrings.
       (Contributed by Mario Carneiro, 18-Jul-2016.) $)
    mrsubcn $p |- ( ( F e. ran S /\ X e. ( C \ V ) ) ->
      ( F ` <" X "> ) = <" X "> ) $=
      ( vf wcel cfv wceq cmap co cvv wf adantr crn cv wrex cdif cs1 wfun cpm c0
      cima cmrsub rnfvprc nsyl2 mrsubff ffun 3syl mrsubrn eleq2i biimpi fvelima
      n0i syl2anc wa cif wss cun elmapi adantl ssidd eldifi syl mrsubcv syl3anc
      elun1 wn eldifn iffalsed eqtrd fveq1 eqeq1d syl5ibcom rexlimdva mpan9 ) E
      CUAZMZLUBZCNZEOZLBFPQZUCZGAFUDMZGUEZENZWKOZWDCUFZECWHUIZMZWIWDDRMZBFUGQZB
      BPQZCSWNWDWCUHOWQWCEUTUJDCHUKULBCDFRJIHUMWRWSCUNUOWDWPWCWOEBCDFJIHUPUQURL
      EWHCUSVAWJWGWMLWHWJWEWHMZVBZWKWFNZWKOWGWMXAXBGFMZGWENZWKVCZWKXAFBWESZFFVD
      GAFVEMZXBXEOWTXFWJWEBFVFVGXAFVHWJXGWTWJGAMXGGAFVIGAFVMVJTFABCDWEFGKJIHVKV
      LXAXCXDWKWJXCVNWTGAFVOTVPVQWGXBWLWKWKWFEVRVSVTWAWB $.

    $( Characterization of the substitutions as functions from expressions to
       expressions that distribute under concatenation and map constants to
       themselves.  (The constant part uses ` ( C \ V ) ` because we don't know
       that ` C ` and ` V ` are disjoint until we get to ~ ismfs .)
       (Contributed by Mario Carneiro, 18-Jul-2016.) $)
    elmrsubrn $p |- ( T e. W -> ( F e. ran S <-> ( F : R --> R /\
      A. c e. ( C \ V ) ( F ` <" c "> ) = <" c "> /\
      A. x e. R A. y e. R ( F ` ( x ++ y ) ) =
        ( ( F ` x ) ++ ( F ` y ) ) ) ) ) $=
      ( vv wcel cfv wceq co c0 vw vr crn wf cv cs1 cdif wral cconcat w3a mrsubf
      mrsubcn ralrimiva mrsubccat 3expb ralrimivva 3jca cmpt cun cfrmd cif ccom
      wa cgsu cword mrexval adantr s1eq fveq2d eqid fvex fvmpt adantl wn difun2
      eleq2i eldif bitr3i simpr2 eqeq12d rspccva sylan2br anassrs eqcomd ifeqda
      weq sylan mpteq2dva coeq1d oveq2d mpteq12dv wss elun2 simplr1 simpr s1cld
      ad2antrr eleqtrrd ffvelcdmd cbvmptv fmptd ssid mrsubfval sylancl cmnd cvv
      sylan2 cmhm cvrmd cmcn fvexi cmvar unex frmdmnd a1i eleqtrd fmpttd cplusg
      ax-mp simpr1 feq23d mpbid simpr3 simprl simprr cbs frmdbas eqcomi frmdadd
      wb syl2anc ffvelcdm ad2ant2lr ad2ant2l 2ralbidva chash caddc fveq2 eqtrdi
      cc0 raleqdv raleqbidv bitr3d 3ad2antr1 cn0 wrd0 lencl nn0cnd 0cnd addridd
      eleqtrrid fvoveq1 oveq1d oveq2 ccatidid rspc2va syl21anc ccatlen addcanad
      3eqtrrd hasheq0 sylib pm3.2i frmd0 ismhm mpbiran syl3anbrc fcompt vrmdval
      syl vrmdf mpan mpteq2ia frmdup3lem syl32anc 3eqtr4rd cpm wfn cmap mrsubff
      ffnd cmrex elpm2r mpanl12 fnfvelrn eqeltrd ex impbid2 ) FIPZGEUCZPZDDGUDZ
      JUEZUFZGQZUWNRZJCHUGZUHZAUEZBUEZUISZGQZUWSGQZUWTGQZUISZRZBDUHADUHZUJZUWKU
      WLUWRUXGDEFGKLUKUWKUWPJUWQCDEFGHUWMKLMNULUMUWKUXFABDDUWKUWSDPZUWTDPZUXFDE
      FGUWSUWTKLUNUOUPUQUWIUXHUWKUWIUXHVCZGUAHUAUEZUFZGQZURZEQZUWJUXKUBDCHUSZUT
      QZOUXQOUEZHPZUXSUXOQZUXSUFZVAZURZUBUEZVBZVDSZURZUBUXQVEZUXROUXQUYBGQZURZU
      YEVBZVDSZURZUXPGUXKUBDUYGUYIUYMUWIDUYIRZUXHCDFHINMLVFZVGZUXKUYFUYLUXRVDUX
      KUYDUYKUYEUXKOUXQUYCUYJUXKUXSUXQPZVCZUXTUYAUYBUYJUXTUYAUYJRUYSUAUXSUXNUYJ
      HUXOUAOWFUXMUYBGUXLUXSVHVIZUXOVJUYBGVKVLVMUYSUXTVNZVCUYJUYBUXKUYRVUAUYJUY
      BRZUYRVUAVCZUXKUXSUWQPZVUBVUDUXSUXQHUGZPVUCVUEUWQUXSCHVOVPUXSUXQHVQVRUXKU
      WRVUDVUBUWIUWLUWRUXGVSUWPVUBJUXSUWQJOWFZUWOUYJUWNUYBVUFUWNUYBGUWMUXSVHZVI
      VUGVTWAWGWBWCWDWEWHWIWJWKUXKHDUXOUDZHHWLZUXPUYHRUXKOHUYJDUXOUXTUXKUYRUYJD
      PUXSHCWMUYSDDUYBGUWLUWRUXGUWIUYRWNUYSUYBUYIDUYSUXSUXQUXKUYRWOWPUWIUYOUXHU
      YRUYPWQZWRWSZXGUAOHUXNUYJUYTWTXAZHXBZOHCDEFUBUXOUXRHNMLKUXRVJZXCXDUXKUXRX
      EPZUXQXFPZUXQUYIUYKUDGUXRUXRXHSPZGUXQXIQZVBZUYKRGUYNRVUOUXKVUPVUOCHCFXJNX
      KHFXLMXKZXMZUXQUXRXFVUNXNXSZXOVUPUXKVVAXOUXKOUXQUYJUYIUYSUYJDUYIVUKVUJXPX
      QUXKUYIUYIGUDZUWSUWTUXRXRQZSZGQZUXCUXDVVDSZRZBUYIUHZAUYIUHZTGQZTRZVUQUXKU
      WLVVCUWIUWLUWRUXGXTUXKDDUYIUYIGUYQUYQYAYBZUXKUXGVVJUWIUWLUWRUXGYCZUWIUWRU
      WLUXGVVJYJUXGUWIUWLVCZVVHBDUHZADUHUXGVVJVVOVVHUXFABDDVVOUXIUXJVCZVCZVVFUX
      BVVGUXEVVRVVEUXAGVVRUWSUYIPUWTUYIPVVEUXARVVRUWSDUYIVVOUXIUXJYDVVOUYOVVQUW
      IUYOUWLUYPVGZVGZXPVVRUWTDUYIVVOUXIUXJYEVVTXPUYIVVDUXQUXRUWSUWTVUNUXRYFQZU
      YIVUPVWAUYIRVVAVWAUXQUXRXFVUNVWAVJYGXSYHZVVDVJZYIYKVIVVRUXCUYIPUXDUYIPVVG
      UXERVVRUXCDUYIUWLUXIUXCDPUWIUXJDDUWSGYLYMVVTXPVVRUXDDUYIUWLUXJUXDDPUWIUXI
      DDUWTGYLYNVVTXPUYIVVDUXQUXRUXCUXDVUNVWBVWCYIYKVTYOVVOVVPVVIADUYIVVSVVOVVH
      BDUYIVVSUUAUUBUUCUUDYBUXKVVKYPQZYTRZVVLUXKVWDVWDYTUXKVWDUXKVVKUYIPZVWDUUE
      PUXKVVCTUYIPVWFVVMUXQUUFZUYIUYITGYLXDZUXQVVKUUGUVJUUHZVWIUXKUUIUXKVWDYTYQ
      SVWDVVKVVKUISZYPQZVWDVWDYQSZUXKVWDVWIUUJUXKVVKVWJYPUXKTDPZVWMUXGVVKVWJRZU
      XKTUYIDVWGUYQUUKZVWOVVNUXFVWNTUWTUISZGQZVVKUXDUISZRABTTDDUWSTRZUXBVWQUXEV
      WRUWSTUWTGUIUULVWSUXCVVKUXDUIUWSTGYRUUMVTUWTTRZVWQVVKVWRVWJVWTVWPTGVWTVWP
      TTUISTUWTTTUIUUNUUOYSVIVWTUXDVVKVVKUIUWTTGYRWJVTUUPUUQVIUXKVWFVWFVWKVWLRV
      WHVWHUXQUXQVVKVVKUURYKUUTUUSVVKXFPVWEVVLYJTGVKVVKXFUVAXSUVBVUQVUOVUOVCVVC
      VVJVVLUJVUOVUOVVBVVBUVCABUYIUYIVVDVVDUXRUXRGTTVWBVWBVWCVWCUXQUXRVUNUVDZVX
      AUVEUVFUVGUXKVUSOUXQUXSVURQZGQZURZUYKUXKVVCUXQUYIVURUDZVUSVXDRVVMVUPVXEVV
      AVURUXQXFVURVJZUVKXSOGVURUXQUYIUYIUVHXDOUXQVXCUYJUYRVXBUYBGVUPUYRVXBUYBRV
      VAUXSVURUXQXFVXFUVIUVLVIUVMYSUBUYKUYIVURGUXRUXQUXRXFVUNVWBVXFUVNUVOUVPUXK
      EDHUVQSZUVRZUXOVXGPZUXPUWJPUWIVXHUXHUWIVXGDDUVSSEDEFHIMLKUVTUWAVGUXKVUHVU
      IVXIVULVUMDXFPHXFPVUHVUIVCVXIDFUWBLXKVUTDHHUXOXFXFUWCUWDXDVXGUXOEUWEYKUWF
      UWGUWH $.
  $}

  ${
    $d c v x y z F $.  $d c v x y z S $.  $d c v x y z T $.  $d v x y z V $.
    $d c x y G $.  $d v x X $.
    mrsubco.s $e |- S = ( mRSubst ` T ) $.
    $( The composition of two substitutions is a substitution.  (Contributed by
       Mario Carneiro, 18-Jul-2016.) $)
    mrsubco $p |- ( ( F e. ran S /\ G e. ran S ) -> ( F o. G ) e. ran S ) $=
      ( vc vx vy wcel wa cfv wf cv wceq cconcat co adantr syl2anc syl fvco3 crn
      ccom cmrex cs1 cmcn cmvar cdif wral eqid mrsubf adantl cword eldifi elun1
      fco cun s1cld cvv c0 cmrsub rnfvprc nsyl2 mrexval eleqtrrd mrsubcn fveq2d
      n0i adantll adantlr 3eqtrd ralrimiva mrsubccat 3expb simpll simprl simprr
      ffvelcdmd syl3anc eleqtrd ccatcl oveq12d 3eqtr4d ralrimivva w3a elmrsubrn
      eqtrd wb mpbir3and ) CAUAZIZDWIIZJZCDUBZWIIZBUCKZWOWMLZFMZUDZWMKZWRNZFBUE
      KZBUFKZUGZUHZGMZHMZOPZWMKZXEWMKZXFWMKZOPZNZHWOUHGWOUHZWLWOWOCLZWOWODLZWPW
      JXNWKWOABCEWOUIZUJQWKXOWJWOABDEXPUJUKZWOWOWOCDUORWLWTFXCWLWQXCIZJZWSWRDKZ
      CKZWRCKZWRXSXOWRWOIWSYANWLXOXRXQQXSWRXAXBUPZULZWOXSWQYCXRWQYCIZWLXRWQXAIY
      EWQXAXBUMWQXAXBUNSUKUQXSBURIZWOYDNZWLYFXRWJYFWKWJWIUSNYFWICVGUTBAEVAVBQZQ
      XAWOBXBURXAUIZXBUIZXPVCZSVDWOWOWRCDTRXSXTWRCWKXRXTWRNWJXAWOABDXBWQEXPYJYI
      VEVHVFWJXRYBWRNWKXAWOABCXBWQEXPYJYIVEVIVJVKWLXLGHWOWOWLXEWOIZXFWOIZJZJZXG
      DKZCKZXEDKZCKZXFDKZCKZOPZXHXKYOYQYRYTOPZCKZUUBYOYPUUCCWKYNYPUUCNZWJWKYLYM
      UUEWOABDXEXFEXPVLVMVHVFYOWJYRWOIYTWOIUUDUUBNWJWKYNVNYOWOWOXEDWLXOYNXQQZWL
      YLYMVOZVQYOWOWOXFDUUFWLYLYMVPZVQWOABCYRYTEXPVLVRWFYOXOXGWOIXHYQNUUFYOXGYD
      WOYOXEYDIXFYDIXGYDIYOXEWOYDUUGWLYGYNWLYFYGYHYKSQZVSYOXFWOYDUUHUUIVSYCXEXF
      VTRUUIVDWOWOXGCDTRYOXIYSXJUUAOYOXOYLXIYSNUUFUUGWOWOXECDTRYOXOYMXJUUANUUFU
      UHWOWOXFCDTRWAWBWCWLYFWNWPXDXMWDWGYHGHXAWOABWMXBURFEXPYJYIWESWH $.

    mrsubvrs.v $e |- V = ( mVR ` T ) $.
    mrsubvrs.r $e |- R = ( mREx ` T ) $.
    $( The set of variables in a substitution is the union, indexed by the
       variables in the original expression, of the variables in the
       substitution to that variable.  (Contributed by Mario Carneiro,
       18-Jul-2016.) $)
    mrsubvrs $p |- ( ( F e. ran S /\ X e. R ) -> ( ran ( F ` X ) i^i V ) =
      U_ x e. ( ran X i^i V ) ( ran ( F ` <" x "> ) i^i V ) ) $=
      ( crn wcel cfv cin ciun wceq cun c0 ineq1d eqtrdi vv vy vz cs1 cmcn cword
      cv cvv n0i cmrsub rnfvprc nsyl2 mrexval syl eleq2d wi cconcat fveq2 rneqd
      eqid co rneq rn0 iuneq1d 0iun eqeq12d imbi2d mrsub0 wa uneq1 simpl simprl
      adantr eleqtrrd simprr s1cld mrsubccat syl3anc wf mrsubf ffvelcdmd ccatrn
      0in eleqtrd syl2anc eqtrd indir csn s1rn ad2antll uneq2d iunxun wss simpr
      snssd dfss2 sylib vex s1eq fveq2d iunxsn incom disjsn bilanri eqtrid cdif
      wn eldif biimpri sylan difun2 eleqtrdi mrsubcn pm2.61dan imbitrrid expcom
      3eqtr4a a2d wrdind com12 sylbid imp ) ECKZLZGBLZGEMZKZFNZAGKZFNZAUGZUDZEM
      ZKZFNZOZPZYDYEGDUEMZFQZUFZLZYQYDBYTGYDDUHLZBYTPZYDYCRPUUBYCEUIUJDCHUKULYR
      BDFUHYRUTZIJUMUNZUOUUAYDYQYDUAUGZEMZKZFNZAUUFKZFNZYOOZPZUPYDREMZKZFNZRPZU
      PYDUBUGZEMZKZFNZAUURKZFNZYOOZPZUPYDUURUCUGZUDZUQVAZEMZKZFNZAUVHKZFNZYOOZP
      ZUPYDYQUPUAUBUCGYSUUFRPZUUMUUQYDUVPUUIUUPUULRUVPUUHUUOFUVPUUGUUNUUFREURUS
      SUVPUULARYOOZRUVPAUUKRYOUVPUUKRFNZRUVPUUJRFUVPUUJRKZRUUFRVBVCTSFWCZTVDAYO
      VEZTVFVGUUFUURPZUUMUVEYDUWBUUIUVAUULUVDUWBUUHUUTFUWBUUGUUSUUFUUREURUSSUWB
      AUUKUVCYOUWBUUJUVBFUUFUURVBSVDVFVGUUFUVHPZUUMUVOYDUWCUUIUVKUULUVNUWCUUHUV
      JFUWCUUGUVIUUFUVHEURUSSUWCAUUKUVMYOUWCUUJUVLFUUFUVHVBSVDVFVGUUFGPZUUMYQYD
      UWDUUIYHUULYPUWDUUHYGFUWDUUGYFUUFGEURUSSUWDAUUKYJYOUWDUUJYIFUUFGVBSVDVFVG
      YDUUPUVRRYDUUORFYDUUOUVSRYDUUNRCDEHVHUSVCTSUVTTUURYTLZUVFYSLZVIZYDUVEUVOY
      DUWGUVEUVOUPUVEUVOYDUWGVIZUVAUVGEMZKZFNZQZUVDUWKQZPUVAUVDUWKVJUWHUVKUWLUV
      NUWMUWHUVKUUTUWJQZFNUWLUWHUVJUWNFUWHUVJUUSUWIUQVAZKZUWNUWHUVIUWOUWHYDUURB
      LUVGBLUVIUWOPYDUWGVKZUWHUURYTBYDUWEUWFVLZYDUUCUWGUUEVMZVNZUWHUVGYTBUWHUVF
      YSYDUWEUWFVOZVPZUWSVNZBCDEUURUVGHJVQVRUSUWHUUSYTLUWIYTLUWPUWNPUWHUUSBYTUW
      HBBUUREYDBBEVSUWGBCDEHJVTVMZUWTWAUWSWDUWHUWIBYTUWHBBUVGEUXDUXCWAUWSWDYSUU
      SUWIWBWEWFSUUTUWJFWGTUWHUVNUVDAUVFWHZFNZYOOZQZUWMUWHUVNAUVCUXFQZYOOUXHUWH
      AUVMUXIYOUWHUVMUVBUXEQZFNUXIUWHUVLUXJFUWHUVLUVBUVGKZQZUXJUWHUWEUVGYTLUVLU
      XLPUWRUXBYSUURUVGWBWEUWHUXKUXEUVBUWFUXKUXEPZYDUWEUVFYSWIWJZWKWFSUVBUXEFWG
      TVDAUVCUXFYOWLTUWHUXGUWKUVDUWHUVFFLZUXGUWKPUWHUXOVIZUXGAUXEYOOUWKUXPAUXFU
      XEYOUXPUXEFWMUXFUXEPUXPUVFFUWHUXOWNWOUXEFWPWQVDAUVFYOUWKUCWRYKUVFPZYNUWJF
      UXQYMUWIUXQYLUVGEYKUVFWSWTUSSXATUWHUXOXGZVIZUVQRUXGUWKUWAUXSAUXFRYOUXSUXF
      FUXENZRUXEFXBUXTRPUXRUWHFUVFXCXDXEZVDUXSUWKUXFRUXSUWJUXEFUXSUWJUXKUXEUXSU
      WIUVGUXSYDUVFYRFXFZLUWIUVGPUWHYDUXRUWQVMUXSUVFYSFXFZUYBUWHUWFUXRUVFUYCLZU
      XAUYDUWFUXRVIUVFYSFXHXIXJYRFXKXLYRBCDEFUVFHJIUUDXMWEUSUWHUXMUXRUXNVMWFSUY
      AWFXQXNWKWFVFXOXPXRXSXTYAYB $.
  $}

  ${
    $d e f t E $.  $d e f t O $.  $d e f t R $.  $d e f t T $.  $d e f t V $.
    $d e f A $.  $d e f F $.  $d e X $.
    msubffval.v $e |- V = ( mVR ` T ) $.
    msubffval.r $e |- R = ( mREx ` T ) $.
    msubffval.s $e |- S = ( mSubst ` T ) $.
    msubffval.e $e |- E = ( mEx ` T ) $.
    ${
      msubffval.o $e |- O = ( mRSubst ` T ) $.
      $( A substitution applied to an expression.  (Contributed by Mario
         Carneiro, 18-Jul-2016.) $)
      msubffval $p |- ( T e. W -> S = ( f e. ( R ^pm V ) |-> ( e e. E |->
        <. ( 1st ` e ) , ( ( O ` f ) ` ( 2nd ` e ) ) >. ) ) ) $=
        ( vt cpm cfv cmpt fveq2 eqtr4di wcel cvv co cv c1st c2nd cop wceq cmsub
        elex cmrex cmvar cmex cmrsub oveq12d fveq1d opeq2d mpteq12dv ovex mptex
        df-msub fvmpt eqtrid syl ) CIUACUBUAZBEAHPUCZDFDUDZUEQZVGUFQZEUDZGQZQZU
        GZRZRZUHCIUJVEBCUIQVOLOCEOUDZUKQZVPULQZPUCZDVPUMQZVHVIVJVPUNQZQZQZUGZRZ
        RVOUBUIVPCUHZEVSWEVFVNWFVQAVRHPWFVQCUKQAVPCUKSKTWFVRCULQHVPCULSJTUOWFDV
        TWDFVMWFVTCUMQFVPCUMSMTWFWCVLVHWFVIWBVKWFVJWAGWFWACUNQGVPCUNSNTUPUPUQUR
        URODEVAEVFVNAHPUSUTVBVCVD $.

      $( A substitution applied to an expression.  (Contributed by Mario
         Carneiro, 18-Jul-2016.) $)
      msubfval $p |- ( ( F : A --> R /\ A C_ V ) -> ( S ` F ) = ( e e. E |->
      <. ( 1st ` e ) , ( ( O ` F ) ` ( 2nd ` e ) ) >. ) ) $=
        ( vf cvv wcel wa cfv c0 wf wss cv c1st c2nd cop cmpt wceq cpm msubffval
        wi adantr simplr fveq2d fveq1d opeq2d mpteq2dva cmrex pm3.2i a1i elpm2r
        co fvexi cmvar sylan cmex mptex fvmptd ex 0fv eqtr4i cmsub fvprc eqtrid
        wn mpt0 mpteq1d 3eqtr4a a1d pm2.61i ) DPQZABGUAAIUBRZGCSZEFEUCZUDSZWDUE
        SZGHSZSZUFZUGZUHZUKWAWBWKWAWBRZOGEFWEWFOUCZHSZSZUFZUGZWJBIUIVBZCPWACOWR
        WQUGUHWBBCDEOFHIPJKLMNUJULWLWMGUHZRZEFWPWIWTWDFQZRZWOWHWEXBWFWNWGXBWMGH
        WLWSXAUMUNUOUPUQWABPQZIPQZRZWBGWRQXEWAXCXDBDURKVCIDVDJVCUSUTBIAGPPVAVEW
        JPQWLEFWIFDVFMVCVGUTVHVIWAVOZWKWBXFGTSZETWIUGZWCWJXGTXHGVJEWIVPVKXFGCTX
        FCDVLSTLDVLVMVNUOXFEFTWIXFFDVFSTMDVFVMVNVQVRVSVT $.

      $( A substitution applied to an expression.  (Contributed by Mario
         Carneiro, 18-Jul-2016.) $)
      msubval $p |- ( ( F : A --> R /\ A C_ V /\ X e. E ) ->
      ( ( S ` F ) ` X ) = <. ( 1st ` X ) , ( ( O ` F ) ` ( 2nd ` X ) ) >. ) $=
        ( ve wcel c1st cfv c2nd fveq2d wf wss w3a cv cop cvv cmpt wceq msubfval
        3adant3 wa simpr opeq12d simp3 opex a1i fvmptd ) ABFUAZAHUBZIEPZUCZOIOU
        DZQRZVBSRZFGRZRZUEZIQRZISRZVERZUEZEFCRZUFURUSVLOEVGUGUHUTABCDOEFGHJKLMN
        UIUJVAVBIUHZUKZVCVHVFVJVNVBIQVAVMULZTVNVDVIVEVNVBISVOTTUMURUSUTUNVKUFPV
        AVHVJUOUPUQ $.

      $( A substitution applied to an expression.  (Contributed by Mario
         Carneiro, 18-Jul-2016.) $)
      msubrsub $p |- ( ( F : A --> R /\ A C_ V /\ X e. E ) ->
        ( 2nd ` ( ( S ` F ) ` X ) ) = ( ( O ` F ) ` ( 2nd ` X ) ) ) $=
        ( wf cfv c1st c2nd wceq fvex wss wcel w3a cop msubval op2ndd syl ) ABFO
        AHUAIEUBUCIFCPPZIQPZIRPZFGPZPZUDSUHRPULSABCDEFGHIJKLMNUEUIULUHIQTUJUKTU
        FUG $.
    $}

    $( The type of a substituted expression is the same as the original type.
       (Contributed by Mario Carneiro, 18-Jul-2016.) $)
    msubty $p |- ( ( F : A --> R /\ A C_ V /\ X e. E ) ->
      ( 1st ` ( ( S ` F ) ` X ) ) = ( 1st ` X ) ) $=
      ( wf wss wcel w3a cfv c1st wceq fvex c2nd cmrsub cop eqid msubval op1std
      syl ) ABFMAGNHEOPHFCQQZHRQZHUAQZFDUBQZQZQZUCSUHRQUISABCDEFUKGHIJKLUKUDUEU
      IUMUHHRTUJULTUFUG $.
  $}

  ${
    $d e f g E $.  $d e f g O $.  $d e g T $.
    elmsubrn.e $e |- E = ( mEx ` T ) $.
    elmsubrn.o $e |- O = ( mRSubst ` T ) $.
    elmsubrn.s $e |- S = ( mSubst ` T ) $.
    $( Characterization of substitution in terms of raw substitution, without
       reference to the generating functions.  (Contributed by Mario Carneiro,
       18-Jul-2016.) $)
    elmsubrn $p |- ran S = ran ( f e. ran O |-> ( e e. E |->
      <. ( 1st ` e ) , ( f ` ( 2nd ` e ) ) >. ) ) $=
      ( vg cvv wcel crn cv cfv cop cmpt wceq co c0 c1st c2nd ccom cpm msubffval
      cmrex cmvar eqid wfn cmap mrsubff ffnd fnfvelrn sylan feqmptd eqidd fveq1
      opeq2d mpteq2dv fmptco eqtr4d rneqd cres rnco wss ssid resmpt ax-mp rneqi
      eqtri eqtrdi wn eqcomi cmsub fvprc eqtrid rnfvprc mpteq1d 3eqtr4a pm2.61i
      mpt0 cmrsub ) BKLZAMZDFMZCECNZUAOZWFUBOZDNZOZPZQZQZMZRWCWDWMFUCZMZWNWCAWO
      WCAJBUFOZBUGOZUDSZCEWGWHJNZFOZOZPZQZQWOWQABCJEFWRKWRUHZWQUHZIGHUEWCJDWSWE
      XAWLXDFWMWCFWSUIWTWSLXAWELWCWSWQWQUJSZFWQFBWRKXEXFHUKZULWSWTFUMUNWCJWSXGF
      XHUOWCWMUPWIXARZCEWKXCXIWJXBWGWHWIXAUQURUSUTVAVBWPWMWEVCZMWNWMFVDXJWMWEWE
      VEXJWMRWEVFDWEWEWLVGVHVIVJVKWCVLZAWMXKTDTWLQZAWMXLTDWLWAVMXKABVNOTIBVNVOV
      PXKDWETWLWBBFHVQVRVSVBVT $.
  $}

  ${
    $d e f E $.  $d e f g R $.  $d f g S $.  $d e f g T $.  $d e f g V $.
    $d e f W $.
    msubff.v $e |- V = ( mVR ` T ) $.
    msubff.r $e |- R = ( mREx ` T ) $.
    msubff.s $e |- S = ( mSubst ` T ) $.
    $( Although it is defined for partial mappings of variables, every partial
       substitution is a substitution on some complete mapping of the
       variables.  (Contributed by Mario Carneiro, 18-Jul-2016.) $)
    msubrn $p |- ran S = ( S " ( R ^m V ) ) $=
      ( vf ve vg crn co cvv wcel wss cfv cv cmpt eqid wa cmap cima cpm cmex cop
      c1st c2nd cmrsub msubffval rneqd wceq wrex wfun mrsubff adantr ffund ffnd
      wf wfn fnfvelrn sylan mrsubrn eleqtrdi fvelima syl2anc elmapi adantl ssid
      msubfval sylancl mptex fnmpti fneq1d mpbiri mapsspm simpr fnfvima syl3anc
      a1i eqeltrrd adantlr fveq1 opeq2d mpteq2dv eleq1d syl5ibcom rexlimdva mpd
      fvex fmpttd frnd eqsstrd wn c0 cmsub rnfvprc 0ss eqsstrdi pm2.61i imassrn
      eqssi ) BKZBADUALZUBZCMNZXBXDOXEXBHADUCLZICUDPZIQZUFPZXHUGPZHQZCUHPZPZPZU
      EZRZRZKXDXEBXQABCIHXGXLDMEFGXGSZXLSZUIZUJXEXFXDXQXEHXFXPXDXEXKXFNZTZJQZXL
      PZXMUKZJXCULZXPXDNZYBXLUMXMXLXCUBZNYFYBXFAAUALZXLXEXFYIXLURYAAXLCDMEFXSUN
      ZUOUPYBXMXLKZYHXEXLXFUSYAXMYKNXEXFYIXLYJUQXFXKXLUTVAAXLCDEFXSVBVCJXMXCXLV
      DVEYBYEYGJXCYBYCXCNZTIXGXIXJYDPZUEZRZXDNZYEYGXEYLYPYAXEYLTZYCBPZYOXDYQDAY
      CURZDDOYRYOUKYLYSXEYCADVFVGDVHDABCIXGYCXLDEFGXRXSVIVJYQBXFUSZXCXFOZYLYRXD
      NXEYTYLXEYTXQXFUSHXFXPXQIXGXOCUDWIVKXQSVLXEXFBXQXTVMVNUOUUAYQADVOVSXEYLVP
      XFXCBYCVQVRVTWAYEYOXPXDYEIXGYNXOYEYMXNXIXJYDXMWBWCWDWEWFWGWHWJWKWLXEWMXBW
      NXDWOCBGWPXDWQWRWSBXCWTXA $.

    msubff.e $e |- E = ( mEx ` T ) $.
    $( A substitution is a function from ` E ` to ` E ` .  (Contributed by
       Mario Carneiro, 18-Jul-2016.) $)
    msubff $p |- ( T e. W -> S : ( R ^pm V ) --> ( E ^m E ) ) $=
      ( vf ve wcel co cmap wf cv cfv cmpt wa cpm c1st c2nd cmrsub cop cxp xp1st
      cmtc eqid mexval eleq2s adantl mrsubff ffvelcdmda elmapi syl xp2nd syl2an
      ffvelcdm opelxp eleqtrrdi fmpttd cmex fvexi elmap sylibr msubffval mpbird
      sylanbrc feq1d ) CFMZAEUANZDDONZBPVLVMKVLLDLQZUBRZVNUCRZKQZCUDRZRZRZUEZSZ
      SZPVKKVLWBVMVKVQVLMTZDDWBPWBVMMWDLDWADWDVNDMZTZWACUHRZAUFZDWFVOWGMZVTAMZW
      AWHMWEWIWDWIVNWHDVNWGAUGACDWGWGUIJHUJZUKULWDAAVSPZVPAMZWJWEWDVSAAONZMWLVK
      VLWNVQVRAVRCEFGHVRUIZUMUNVSAAUOUPWMVNWHDVNWGAUQWKUKAAVPVSUSURVOVTWGAUTVIW
      KVAVBDDWBDCVCJVDZWPVEVFVBVKVLVMBWCABCLKDVREFGHIJWOVGVJVH $.
  $}

  ${
    $d f g F $.  $d f g G $.  $d f g S $.  $d f g h x y T $.
    msubco.s $e |- S = ( mSubst ` T ) $.
    $( The composition of two substitutions is a substitution.  (Contributed by
       Mario Carneiro, 18-Jul-2016.) $)
    msubco $p |- ( ( F e. ran S /\ G e. ran S ) -> ( F o. G ) e. ran S ) $=
      ( vx vf vy vg vh crn wcel cfv cv cop cmpt wceq wrex ccom eqid cmex cmrsub
      c1st c2nd elmsubrn eleq2i fvex mptex elrnmpti bitri reeanv cmtc cmrex cxp
      wa simpr mexval eleqtrdi xp1st wf mrsubf ad2antlr xp2nd ffvelcdmd opelxpi
      syl syl2anc eleqtrrdi eqidd op1std op2ndd fveq2d opeq12d fmptco mpteq2dva
      fvco3 opeq2d mrsubco fveq1 mpteq2dv elrnmpt1s sylancl eqeltrd coeq1 coeq2
      eqtr4d cvv sylan9eq eleq1d syl5ibrcom rexlimivv sylbir syl2anb ) CAKZLZCF
      BUAMZFNZUCMZWQUDMZGNZMZOZPZQZGBUBMZKZRZDHWPHNZUCMZXHUDMZINZMZOZPZQZIXFRZC
      DSZWNLZDWNLZWOCGXFXCPZKZLXGWNYACABFGWPXEWPTZXETZEUEUFGXFXCCXTXTTFWPXBBUAU
      GZUHUIUJXSDIXFXNPZKZLXPWNYFDABHIWPXEYBYCEUEUFIXFXNDYEYETHWPXMYDUHUIUJXGXP
      UOXDXOUOZIXFRGXFRXRXDXOGIXFXFUKYGXRGIXFXFWTXFLZXKXFLZUOZXRYGXCXNSZWNLYJYK
      HWPXIXJWTXKSZMZOZPZWNYJYKHWPXIXLWTMZOZPYOYJHFWPWPXMXBYQXNXCYJXHWPLZUOZXMB
      ULMZBUMMZUNZWPYSXIYTLZXLUUALXMUUBLYSXHUUBLZUUCYSXHWPUUBYJYRUPUUABWPYTYTTY
      BUUATZUQZURZXHYTUUAUSVFYSUUAUUAXJXKYIUUAUUAXKUTZYHYRUUAXEBXKYCUUEVAVBZYSU
      UDXJUUALZUUGXHYTUUAVCVFZVDXIXLYTUUAVEVGUUFVHYJXNVIYJXCVIWQXMQZWRXIXAYPXIX
      LWQXHUCUGZXJXKUGZVJUULWSXLWTXIXLWQUUMUUNVKVLVMVNYJHWPYNYQYSYMYPXIYSUUHUUJ
      YMYPQUUIUUKUUAUUAXJWTXKVPVGVQVOWFYJYOJXFHWPXIXJJNZMZOZPZPZKZWNYJYLXFLYOWG
      LYOUUTLXEBWTXKYCVRHWPYNYDUHJXFUURYOYLUUSWGUUSTUUOYLQZHWPUUQYNUVAUUPYMXIXJ
      UUOYLVSVQVTWAWBABHJWPXEYBYCEUEVHWCYGXQYKWNXDXOXQXCDSYKCXCDWDDXNXCWEWHWIWJ
      WKWLWM $.

    msubf.e $e |- E = ( mEx ` T ) $.
    $( A substitution is a function.  (Contributed by Mario Carneiro,
       18-Jul-2016.) $)
    msubf $p |- ( F e. ran S -> F : E --> E ) $=
      ( crn wcel cmap co wf cvv cmrex cfv cmvar cpm wss c0 wceq eqid n0i msubff
      cmsub rnfvprc nsyl2 frn 3syl id sseldd elmapi syl ) DAGZHZDCCIJZHCCDKUMUL
      UNDUMBLHZBMNZBONZPJZUNAKULUNQUMULRSUOULDUAUCBAEUDUEUPABCUQLUQTUPTEFUBURUN
      AUFUGUMUHUIDCCUJUK $.
  $}

  ${
    $d t v T $.  $d t v V $.  $d v X $.  $d t v Y $.
    mvhfval.v $e |- V = ( mVR ` T ) $.
    mvhfval.y $e |- Y = ( mType ` T ) $.
    mvhfval.h $e |- H = ( mVH ` T ) $.
    $( Value of the function mapping variables to their corresponding variable
       expressions.  (Contributed by Mario Carneiro, 18-Jul-2016.) $)
    mvhfval $p |- H = ( v e. V |-> <. ( Y ` v ) , <" v "> >. ) $=
      ( vt cmvh cfv cv cop cmpt cvv wceq cmvar cmty fveq2 c0 cs1 eqtr4di fveq1d
      wcel opeq1d mpteq12dv df-mvh mptfvmpt wn mpt0 eqcomi fvprc eqtrid mpteq1d
      3eqtr4a pm2.61i eqtri ) CBJKZADALZEKZUSUAZMZNZHBOUDZURVCPAIVBQJAILZQKZUSV
      ERKZKZVAMZNDOBBVEBPZAVFVIDVBVJVFBQKZDVEBQSFUBVJVHUTVAVJUSVGEVJVGBRKEVEBRS
      GUBUCUEUFAIUGFUHVDUIZTATVBNZURVCVMTAVBUJUKBJULVLADTVBVLDVKTFBQULUMUNUOUPU
      Q $.

    $( Value of the function mapping variables to their corresponding variable
       expressions.  (Contributed by Mario Carneiro, 18-Jul-2016.) $)
    mvhval $p |- ( X e. V -> ( H ` X ) = <. ( Y ` X ) , <" X "> >. ) $=
      ( vv cv cfv cs1 cop wceq fveq2 s1eq opeq12d mvhfval opex fvmpt ) IDIJZEKZ
      UALZMDEKZDLZMCBUADNUBUDUCUEUADEOUADPQIABCEFGHRUDUEST $.
  $}

  ${
    $d d D $.  $d t E $.  $d d t T $.  $d d t V $.
    mpstval.v $e |- V = ( mDV ` T ) $.
    mpstval.e $e |- E = ( mEx ` T ) $.
    mpstval.p $e |- P = ( mPreSt ` T ) $.
    $( A pre-statement is an ordered triple, whose first member is a symmetric
       set of disjoint variable conditions, whose second member is a finite set
       of expressions, and whose third member is an expression.  (Contributed
       by Mario Carneiro, 18-Jul-2016.) $)
    mpstval $p |- P =
      ( ( { d e. ~P V | `' d = d } X. ( ~P E i^i Fin ) ) X. E ) $=
      ( vt cmpst cfv cv wceq cpw crab cfn cxp cmdv cmex c0 ccnv cin cvv eqtr4di
      wcel fveq2 pweqd rabeqdv ineq1d xpeq12d fvexi pwex rabex inex1 xpex fvmpt
      df-mpst wn xp0 eqcomi fvprc eqtrid xpeq2d 3eqtr4a pm2.61i eqtri ) ABJKZEL
      ZUAVHMZEDNZOZCNZPUBZQZCQZHBUCUEZVGVOMIBVIEILZRKZNZOZVQSKZNZPUBZQZWAQVOUCJ
      VQBMZWDVNWACWEVTVKWCVMWEVIEVSVJWEVRDWEVRBRKDVQBRUFFUDUGUHWEWBVLPWEWACWEWA
      BSKZCVQBSUFGUDZUGUIUJWGUJIEUQVNCVKVMVIEVJDDBRFUKULUMVLPCCBSGUKZULUNUOWHUO
      UPVPURZTVNTQZVGVOWJTVNUSUTBJVAWICTVNWICWFTGBSVAVBVCVDVEVF $.

    $( Property of being a pre-statement.  (Contributed by Mario Carneiro,
       18-Jul-2016.) $)
    elmpst $p |- ( <. D , H , A >. e. P <->
      ( ( D C_ V /\ `' D = D ) /\ ( H C_ E /\ H e. Fin ) /\ A e. E ) ) $=
      ( vd cop ccnv wceq cpw cfn cxp wcel wa bitri crab cin wss cotp w3a opelxp
      cv cnveq id eqeq12d elrab cmdv fvexi elpw2 anbi1i anbi12i mpstval eleq12i
      elfpw df-ot df-3an 3bitr4i ) BFLZALZKUGZMZVENZKGOZUAZEOPUBZQZEQZRZBGUCZBM
      ZBNZSZFEUCFPRSZSZAERZSZBFAUDZCRVQVRVTUEVMVCVKRZVTSWAVCAVKEUFWCVSVTWCBVIRZ
      FVJRZSVSBFVIVJUFWDVQWEVRWDBVHRZVPSVQVGVPKBVHVEBNZVFVOVEBVEBUHWGUIUJUKWFVN
      VPBGGDULHUMUNUOTFEUSUPTUOTWBVDCVLBFAUTCDEGKHIJUQURVQVRVTVAVB $.
  $}

  ${
    $d a h s z A $.  $d a h s z D $.  $d a h s z H $.  $d a h s t z P $.
    $d a h s t T $.  $d t z V $.  $d a h s z Z $.
    msrfval.v $e |- V = ( mVars ` T ) $.
    msrfval.p $e |- P = ( mPreSt ` T ) $.
    msrfval.r $e |- R = ( mStRed ` T ) $.
    $( Value of the reduct of a pre-statement.  (Contributed by Mario Carneiro,
       18-Jul-2016.) $)
    msrfval $p |- R = ( s e. P |->
       [_ ( 2nd ` ( 1st ` s ) ) / h ]_ [_ ( 2nd ` s ) / a ]_
       <. ( ( 1st ` ( 1st ` s ) ) i^i
          [_ U. ( V " ( h u. { a } ) ) / z ]_ ( z X. z ) ) , h , a >. ) $=
      ( vt cmsr cfv cv csb cmpt cmpst cmvrs c0 c1st c2nd csn cun cima cuni cotp
      cxp cin cvv wcel wceq fveq2 eqtr4di imaeq1d unieqd ineq2d oteq1d csbeq2dv
      csbeq1d mpteq12dv df-msr mptfvmpt wn eqcomi fvprc mpteq1d 3eqtr4a pm2.61i
      mpt0 eqtrid eqtri ) CDMNZGBEGOZUANZUBNZHVNUBNZVOUANZAFEOZHOZUCUDZUEZUFZAO
      ZWDUHZPZUIZVSVTUGZPZPZQZKDUJUKZVMWKULGLWJRMGLOZRNZEVPHVQVRAWMSNZWAUEZUFZW
      EPZUIZVSVTUGZPZPZQBUJDDWMDULZGWNXBBWJXCWNDRNZBWMDRUMJUNXCEVPXAWIXCHVQWTWH
      XCWSWGVSVTXCWRWFVRXCAWQWCWEXCWPWBXCWOFWAXCWODSNFWMDSUMIUNUOUPUTUQURUSUSVA
      ALEGHVBJVCWLVDZTGTWJQZVMWKXFTGWJVJVEDMVFXEGBTWJXEBXDTJDRVFVKVGVHVIVL $.

    msrval.z $e |- Z = U. ( V " ( H u. { A } ) ) $.
    $( Value of the reduct of a pre-statement.  (Contributed by Mario Carneiro,
       18-Jul-2016.) $)
    msrval $p |- ( <. D , H , A >. e. P -> ( R ` <. D , H , A >. ) =
       <. ( D i^i ( Z X. Z ) ) , H , A >. ) $=
      ( vs wcel c1st cfv c2nd cvv wceq wa vh va vz cotp cv csn cun cima cxp csb
      cuni cin cmpt msrfval a1i fvexd simpllr fveq2d cmex cmdv ccnv eqid elmpst
      cfn wss simp1bi simpld ad3antrrr fvex ssex simp2bi simprd simp3bi syl3anc
      ot1stg eqtrd cmvrs fvexi imaexg ax-mp uniex id simplr ot2ndg 3eqtrd simpr
      syl ot3rdg sneqd uneq12d imaeq2d unieqd eqtr4di sylan9eqr sqxpeqd ineq12d
      csbied oteq123d otex fvmptd ) BFAUDZCNZMXAUAMUEZOPZQPZUBXCQPZXDOPZUCGUAUE
      ZUBUEZUFZUGZUHZUKZUCUEZXNUIZUJZULZXHXIUDZUJZUJZBHHUIZULZFAUDZCDRDMCXTUMSX
      BUCCDEUAGMUBIJKUNUOXBXCXASZTZUAXEXSYCRYEXDQUPYEXHXESZTZUBXFXRYCRYGXCQUPYG
      XIXFSZTZXQYBXHFXIAYIXGBXPYAYIXGXAOPZOPZBYIXDYJOYIXCXAOXBYDYFYHUQZURZURYIB
      RNZFVDNZAEUSPZNZYKBSYIBEUTPZVEZYNXBYSYDYFYHXBYSBVABSZXBYSYTTZFYPVEZYOTZYQ
      ABCEYPFYRYRVBYPVBJVCZVFVGVHBYREUTVIVJWGZXBYOYDYFYHXBUUBYOXBUUAUUCYQUUDVKV
      LVHZXBYQYDYFYHXBUUAUUCYQUUDVMVHZBFARVDYPVOVNVPYIUCXMXOYARXMRNYIXLGRNXLRNG
      EVQIVRGXKRVSVTWAUOYIXNXMSZTXNHUUHYIXNXMHUUHWBYIXMGFAUFZUGZUHZUKHYIXLUUKYI
      XKUUJGYIXHFXJUUIYIXHXEYJQPZFYEYFYHWCYIXDYJQYMURYIYNYOYQUULFSUUEUUFUUGBFAR
      VDYPWDVNWEZYIXIAYIXIXFXAQPZAYGYHWFYIXCXAQYLURYIYQUUNASUUGBFAYPWHWGWEZWIWJ
      WKWLLWMWNWOWQWPUUMUUOWRWQWQXBWBYCRNXBYBFAWSUOWT $.
  $}

  ${
    $d a h s z P $.  $d s R $.  $d a d h s z T $.
    mpstssv.p $e |- P = ( mPreSt ` T ) $.
    $( A pre-statement is an ordered triple.  (Contributed by Mario Carneiro,
       18-Jul-2016.) $)
    mpstssv $p |- P C_ ( ( _V X. _V ) X. _V ) $=
      ( vd cv ccnv wceq cmdv cfv cpw crab cmex cfn cin cxp cvv eqid mpstval wss
      xpss ssv xpss12 mp2an eqsstri ) ADEZFUEGDBHIZJKZBLIZJMNZOZUHOZPPOZPOZABUH
      UFDUFQUHQCRUJULSUHPSUKUMSUGUITUHUAUJULUHPUBUCUD $.

    $( Decompose a pre-statement into a triple of values.  (Contributed by
       Mario Carneiro, 18-Jul-2016.) $)
    mpst123 $p |- ( X e. P -> X =
      <. ( 1st ` ( 1st ` X ) ) , ( 2nd ` ( 1st ` X ) ) , ( 2nd ` X ) >. ) $=
      ( wcel cvv cxp c1st cfv c2nd cotp wceq mpstssv sseli 1st2nd2 xp1st opeq1d
      cop syl eqtrd df-ot eqtr4di ) CAECFFGZFGZEZCCHIZHIZUFJIZCJIZKZLAUDCABDMNU
      ECUGUHRZUIRZUJUECUFUIRULCUCFOUEUFUKUIUEUFUCEUFUKLCUCFPUFFFOSQTUGUHUIUAUBS
      $.

    $( The elements of a pre-statement are sets.  (Contributed by Mario
       Carneiro, 18-Jul-2016.) $)
    mpstrcl $p |- ( <. D , H , A >. e. P ->
      ( D e. _V /\ H e. _V /\ A e. _V ) ) $=
      ( cotp cop cvv cxp w3a df-ot mpstssv sseli eqeltrrid opelxp anbi1i df-3an
      wcel wa 3bitr4i sylib ) BEAGZCSZBEHZAHZIIJZIJZSZBISZEISZAISZKZUDUFUCUHBEA
      LCUHUCCDFMNOUEUGSZULTUJUKTZULTUIUMUNUOULBEIIPQUEAUGIPUJUKULRUAUB $.

    msrf.r $e |- R = ( mStRed ` T ) $.
    $( The reduct of a pre-statement is a pre-statement.  (Contributed by Mario
       Carneiro, 18-Jul-2016.) $)
    msrf $p |- R : P --> P $=
      ( vs vh va vz cv cfv wcel csb cin cotp eqid wceq wss ccnv wa wf wral c1st
      wfn c2nd cmvrs csn cun cima cuni otex csbex msrfval fnmpti mpst123 fveq2d
      cxp eqeltrrd msrval syl eqtrd cmdv cmex cfn inss1 w3a elmpst sylib simp1d
      simpld sstrid cnvin simprd a1i ineq12d eqtrid jca simp2d simp3d syl3anbrc
      id cnvxp eqeltrd rgen ffnfv mpbir2an ) AABUABAUDFJZBKZALZFAUBFAGWGUCKZUEK
      ZHWGUEKZWJUCKZICUFKZGJZHJZUGUHUIUJIJZWQUQMNZWOWPOZMZMBGWKWTHWLWSWRWOWPUKU
      LULIABCGWNFHWNPZDEUMUNWIFAWGALZWHWMWNWKWLUGUHUIUJZXCUQZNZWKWLOZAXBWHWMWKW
      LOZBKZXFXBWGXGBACWGDUOZUPXBXGALZXHXFQXBWGXGAXIXBWAURZWLWMABCWKWNXCXADEXCP
      USUTVAXBXECVBKZRZXESZXEQZTWKCVCKZRWKVDLTZWLXPLZXFALXBXMXOXBXEWMXLWMXDVEXB
      WMXLRZWMSZWMQZXBXSYATZXQXRXBXJYBXQXRVFXKWLWMACXPWKXLXLPZXPPZDVGVHZVIZVJVK
      XBXNXTXDSZNXEWMXDVLXBXTWMYGXDXBXSYAYFVMYGXDQXBXCXCWBVNVOVPVQXBYBXQXRYEVRX
      BYBXQXRYEVSWLXEACXPWKXLYCYDDVGVTWCWDFAABWEWF $.

    $( If ` X ` and ` Y ` have the same reduct, then one is a pre-statement iff
       the other is.  (Contributed by Mario Carneiro, 18-Jul-2016.) $)
    msrrcl $p |- ( ( R ` X ) = ( R ` Y ) -> ( X e. P <-> Y e. P ) ) $=
      ( cfv wceq wcel wi msrf ffvelcdmi a1i eleq1 imbitrrid c0 cvv cxp ndmfvrcl
      wb wa fdmi 0nelxp mpstssv sseli mto adantl biimpa syl 2thd ex pm5.21ndd )
      DBHZEBHZIZUNAJZDAJZEAJZURUQKUPAADBABCFGLZMNUSUQUPUOAJZAAEBUTMUNUOAOZPUPUQ
      URUSUAUPUQUBZURUSUQURUPDAABAABUTUCZQAJQRRSZRSZJVERUDAVFQACFUEUFUGZTUHVCVA
      USUPUQVAVBUIEAABVDVGTUJUKULUM $.
  $}

  ${
    $d s t R $.  $d s t T $.  $d s X $.
    mstaval.r $e |- R = ( mStRed ` T ) $.
    mstaval.s $e |- S = ( mStat ` T ) $.
    $( Value of the set of statements.  (Contributed by Mario Carneiro,
       18-Jul-2016.) $)
    mstaval $p |- S = ran R $=
      ( vt cmsta cfv crn wcel wceq cv cmsr fveq2 eqtr4di rneqd df-msta c0 fvprc
      cvv fvexi rnex fvmpt wn rn0 eqcomi eqtrid 3eqtr4a pm2.61i eqtri ) BCGHZAI
      ZECTJZUKULKFCFLZMHZIULTGUNCKZUOAUPUOCMHZAUNCMNDOPFQAACMDUAUBUCUMUDZRRIZUK
      ULUSRUEUFCGSURARURAUQRDCMSUGPUHUIUJ $.

    $( The reduct of a statement is itself.  (Contributed by Mario Carneiro,
       18-Jul-2016.) $)
    msrid $p |- ( X e. S -> ( R ` X ) = X ) $=
      ( vs cfv wceq wcel eqid c1st c2nd cin cotp fveq2d id eqeltrrd msrval syl
      crn cv cmpst wrex wf wfn wb msrf ffn fvelrnb mp2b cmvrs csn cun cima cuni
      cxp mpst123 eqtrd ffvelcdmi inass inidm ineq2i eqtri oteq1d 3eqtr4d fveq2
      a1i eqeq12d syl5ibcom rexlimiv sylbi mstaval eleq2s ) DAHZDIZDAUAZBDVQJZG
      UBZAHZDIZGCUCHZUDZVPWBWBAUEAWBUFVRWCUGWBACWBKZEUHZWBWBAUIGWBDAUJUKWAVPGWB
      VSWBJZVTAHZVTIWAVPWFVSLHZLHZCULHZWHMHZVSMHZUMUNUOUPZWMUQZNZWKWLOZAHZWPWGV
      TWFWQWOWNNZWKWLOZWPWFWPWBJWQWSIWFVTWPWBWFVTWIWKWLOZAHZWPWFVSWTAWBCVSWDURZ
      PWFWTWBJXAWPIWFVSWTWBXBWFQRWLWIWBACWKWJWMWJKZWDEWMKZSTUSZWBWBVSAWEUTRWLWO
      WBACWKWJWMXCWDEXDSTWFWRWOWKWLWRWOIWFWRWIWNWNNZNWOWIWNWNVAXFWNWIWNVBVCVDVH
      VEUSWFVTWPAXEPXEVFWAWGVOVTDVTDAVGWAQVIVJVKVLABCEFVMVN $.

    msrfo.p $e |- P = ( mPreSt ` T ) $.
    $( The reduct of a pre-statement is a statement.  (Contributed by Mario
       Carneiro, 18-Jul-2016.) $)
    msrfo $p |- R : P -onto-> S $=
      ( wfo crn wfn wf msrf ffn ax-mp dffn4 mpbi wceq wb mstaval foeq3 mpbir )
      ACBHZABIZBHZBAJZUDAABKUEABDGELAABMNABOPCUCQUBUDRBCDEFSCUCABTNUA $.
  $}

  ${
    mstapst.p $e |- P = ( mPreSt ` T ) $.
    mstapst.s $e |- S = ( mStat ` T ) $.
    $( A statement is a pre-statement.  (Contributed by Mario Carneiro,
       18-Jul-2016.) $)
    mstapst $p |- S C_ P $=
      ( cmsr cfv crn eqid mstaval wf wss msrf frn ax-mp eqsstri ) BCFGZHZAQBCQI
      ZEJAAQKRALAQCDSMAAQNOP $.

    elmsta.v $e |- V = ( mVars ` T ) $.
    elmsta.z $e |- Z = U. ( V " ( H u. { A } ) ) $.
    $( Property of being a statement.  (Contributed by Mario Carneiro,
       18-Jul-2016.) $)
    elmsta $p |- ( <. D , H , A >. e. S <->
                   ( <. D , H , A >. e. P /\ D C_ ( Z X. Z ) ) ) $=
      ( cotp wcel wss c1st cfv wceq syl cvv cxp wa mstapst cin cmsr eqid msrval
      sseli msrid eqtr3d fveq2d inss1 mpstrcl simp1d ssexg simp2d simp3d ot1stg
      w3a sylancr syl3anc 3eqtr3d inss2 eqsstrrdi jca adantr dfss2 bilani eqtrd
      crn oteq1d wfn wf msrf ffn ax-mp simpl fnfvelrn eqeltrrd eleqtrrdi impbii
      mstaval ) BFAMZDNZWCCNZBHHUAZOZUBZWDWEWGDCWCCDEIJUCUHZWDBBWFUDZWFWDWJFAMZ
      PQZPQZWCPQZPQZWJBWDWLWNPWDWKWCPWDWCEUEQZQZWKWCWDWEWQWKRZWIABCWPEFGHKIWPUF
      ZLUGZSWPDEWCWSJUIUJUKUKWDWJTNZFTNZATNZWMWJRWDWJBOBTNZXABWFULWDXDXBXCWDWEX
      DXBXCUSZWIABCEFIUMSZUNWJBTUOUTWDXDXBXCXFUPWDXDXBXCXFUQWJFATTTURVAWDXEWOBR
      XFBFATTTURSVBBWFVCVDVEWHWCWPVJZDWHWQWCXGWHWQWKWCWEWRWGWTVFWHWJBFAWGWJBRWE
      BWFVGVHVKVIWHWPCVLZWEWQXGNCCWPVMXHCWPEIWSVNCCWPVOVPWEWGVQCWCWPVRUTVSWPDEW
      SJWBVTWA $.
  $}

  ${
    $d t A $.  $d t C $.  $d t v F $.  $d t K $.  $d t S $.  $d t v T $.
    $d t V $.  $d t Y $.
    ismfs.c $e |- C = ( mCN ` T ) $.
    ismfs.v $e |- V = ( mVR ` T ) $.
    ismfs.y $e |- Y = ( mType ` T ) $.
    ismfs.f $e |- F = ( mVT ` T ) $.
    ismfs.k $e |- K = ( mTC ` T ) $.
    ismfs.a $e |- A = ( mAx ` T ) $.
    ismfs.s $e |- S = ( mStat ` T ) $.
    $( A formal system is a tuple ` <. mCN , mVR , mType , mVT , mTC , mAx >. `
       such that: ` mCN ` and ` mVR ` are disjoint; ` mType ` is a function
       from ` mVR ` to ` mVT ` ; ` mVT ` is a subset of ` mTC ` ; ` mAx ` is a
       set of statements; and for each variable typecode, there are infinitely
       many variables of that type.  (Contributed by Mario Carneiro,
       18-Jul-2016.) $)
    ismfs $p |- ( T e. W -> ( T e. mFS <->
      ( ( ( C i^i V ) = (/) /\ Y : V --> K ) /\ ( A C_ S /\
          A. v e. F -. ( `' Y " { v } ) e. Fin ) ) ) ) $=
      ( cfv fveq2 eqtr4di vt cv cmcn cmvar cin c0 wceq cmtc cmty wf wa cmax wss
      cmsta ccnv csn cima wcel wn cmvt wral cmfs ineq12d eqeq1d feq123d anbi12d
      cfn sseq12d cnveqd imaeq1d eleq1d notbid raleqbidv df-mfs elab2g ) UAUBZU
      CRZVPUDRZUEZUFUGZVRVPUHRZVPUIRZUJZUKZVPULRZVPUNRZUMZWBUOZAUBUPZUQZVGURZUS
      ZAVPUTRZVAZUKZUKCHUEZUFUGZHGJUJZUKZBDUMZJUOZWIUQZVGURZUSZAFVAZUKZUKUAEVBI
      VPEUGZWDWSWOXFXGVTWQWCWRXGVSWPUFXGVQCVRHXGVQEUCRCVPEUCSKTXGVREUDRHVPEUDSL
      TZVCVDXGVRHWAGWBJXGWBEUIRJVPEUISMTZXHXGWAEUHRGVPEUHSOTVEVFXGWGWTWNXEXGWEB
      WFDXGWEEULRBVPEULSPTXGWFEUNRDVPEUNSQTVHXGWLXDAWMFXGWMEUTRFVPEUTSNTXGWKXCX
      GWJXBVGXGWHXAWIXGWBJXIVIVJVKVLVMVFVFAUAVNVO $.
  $}

  ${
    $d v T $.
    mfsdisj.c $e |- C = ( mCN ` T ) $.
    mfsdisj.v $e |- V = ( mVR ` T ) $.
    $( The constants and variables of a formal system are disjoint.
       (Contributed by Mario Carneiro, 18-Jul-2016.) $)
    mfsdisj $p |- ( T e. mFS -> ( C i^i V ) = (/) ) $=
      ( vv cmfs wcel cin c0 wceq cmtc cfv cmty wf cmax cmsta wss wa eqid cv csn
      ccnv cima cfn wn cmvt wral ismfs ibi simplld ) BGHZACIJKZCBLMZBNMZOZBPMZB
      QMZRUOUCFUAUBUDUEHUFFBUGMZUHSZULUMUPSUTSFUQAURBUSUNCGUODEUOTUSTUNTUQTURTU
      IUJUK $.
  $}

  ${
    $d v T $.
    mtyf2.v $e |- V = ( mVR ` T ) $.
    mvtf2.k $e |- K = ( mTC ` T ) $.
    mtyf2.y $e |- Y = ( mType ` T ) $.
    $( The type function maps variables to typecodes.  (Contributed by Mario
       Carneiro, 18-Jul-2016.) $)
    mtyf2 $p |- ( T e. mFS -> Y : V --> K ) $=
      ( vv cmfs wcel cmcn cfv cin c0 wceq wf cmax cmsta wa eqid wss ccnv cv csn
      cima cfn wn cmvt wral ismfs ibi simplrd ) AIJZAKLZCMNOZCBDPZAQLZARLZUADUB
      HUCUDUEUFJUGHAUHLZUISZUMUOUPSUTSHUQUNURAUSBCIDUNTEGUSTFUQTURTUJUKUL $.
  $}

  ${
    mtyf.v $e |- V = ( mVR ` T ) $.
    mtyf.f $e |- F = ( mVT ` T ) $.
    mtyf.y $e |- Y = ( mType ` T ) $.
    $( The type function maps variables to variable typecodes.  (Contributed by
       Mario Carneiro, 18-Jul-2016.) $)
    mtyf $p |- ( T e. mFS -> Y : V --> F ) $=
      ( cmfs wcel crn wf cmtc cfv wfo eqid mtyf2 wfn ffn dffn4 sylib fof mvtval
      3syl wceq wb feq3 ax-mp sylibr ) AHIZCDJZDKZCBDKZUICALMZDKZCUJDNZUKAUMCDE
      UMOGPUNDCQUOCUMDRCDSTCUJDUAUCBUJUDULUKUEABDFGUBBUJCDUFUGUH $.
  $}

  ${
    mvtss.f $e |- F = ( mVT ` T ) $.
    mvtss.k $e |- K = ( mTC ` T ) $.
    $( The set of variable typecodes is a subset of all typecodes.
       (Contributed by Mario Carneiro, 18-Jul-2016.) $)
    mvtss $p |- ( T e. mFS -> F C_ K ) $=
      ( cmfs wcel cmty cfv crn eqid mvtval cmvar mtyf2 frnd eqsstrid ) AFGZBAHI
      ZJCABRDRKZLQAMIZCRACTRTKESNOP $.
  $}

  ${
    $d v T $.
    maxsta.a $e |- A = ( mAx ` T ) $.
    maxsta.s $e |- S = ( mStat ` T ) $.
    $( An axiom is a statement.  (Contributed by Mario Carneiro,
       18-Jul-2016.) $)
    maxsta $p |- ( T e. mFS -> A C_ S ) $=
      ( vv cmfs wcel cmcn cfv cmvar cin c0 wceq cmtc cmty wf wa wss eqid cv csn
      ccnv cima cfn wn cmvt wral ismfs ibi simprld ) CGHZCIJZCKJZLMNUNCOJZCPJZQ
      RZABSZUPUCFUAUBUDUEHUFFCUGJZUHZULUQURUTRRFAUMBCUSUOUNGUPUMTUNTUPTUSTUOTDE
      UIUJUK $.
  $}

  ${
    $d v F $.  $d v T $.  $d v X $.  $d v Y $.
    mvtinf.f $e |- F = ( mVT ` T ) $.
    mvtinf.y $e |- Y = ( mType ` T ) $.
    $( Each variable typecode has infinitely many variables.  (Contributed by
       Mario Carneiro, 18-Jul-2016.) $)
    mvtinf $p |- ( ( T e. mFS /\ X e. F ) -> -. ( `' Y " { X } ) e. Fin ) $=
      ( vv cmfs wcel ccnv cv csn cima cfn wn wral cfv wceq wa eqid cmvar cin c0
      cmcn cmtc wf cmax cmsta wss ismfs ibi simprrd sneq imaeq2d eleq1d rspccva
      notbid sylan ) AHIZDJZGKZLZMZNIZOZGBPZCBIUTCLZMZNIZOZUSAUDQZAUAQZUBUCRVLA
      UEQZDUFSZAUGQZAUHQZUIZVFUSVNVQVFSSGVOVKVPABVMVLHDVKTVLTFEVMTVOTVPTUJUKULV
      EVJGCBVACRZVDVIVRVCVHNVRVBVGUTVACUMUNUOUQUPUR $.
  $}

  ${
    $d f g r v R $.  $d f g r v S $.  $d f g r v T $.  $d f g r v V $.
    msubff1.v $e |- V = ( mVR ` T ) $.
    msubff1.r $e |- R = ( mREx ` T ) $.
    msubff1.s $e |- S = ( mSubst ` T ) $.
    ${
      msubff1.e $e |- E = ( mEx ` T ) $.
      $( When restricted to complete mappings, the substitution-producing
         function is one-to-one.  (Contributed by Mario Carneiro,
         18-Jul-2016.) $)
      msubff1 $p |- ( T e. mFS ->
        ( S |` ( R ^m V ) ) : ( R ^m V ) -1-1-> ( E ^m E ) ) $=
        ( vf vg vv cmfs wcel co wf cfv wceq wa wb vr cmap cres cv wi wf1 msubff
        wral cpm wss mapsspm a1i fssresd cmrsub wfn eqid mrsubff simplrl sselid
        ad2antrr ffvelcdmd elmapi ffn 3syl simplrr cmty c2nd c1st fveq1d adantr
        cop syl ssidd cmtc cxp mtyf2 ad3antrrr opelxpi mexval eleqtrrdi msubval
        sylancom syl3anc 3eqtr3d fvex opth simprbi op2nd fveq2i 3eqtr3g eqfnfvd
        vex mrsubff1 f1fveq sylan eqeqan12d adantl bitr3d mpbird expr ralrimdva
        fvres eqfnfv syl2an 3imtr4d ralrimivva dff13 sylanbrc ) CMNZAEUBOZDDUBO
        ZBXJUCZPJUDZXLQZKUDZXLQZRZXMXORZUEZKXJUHJXJUHXJXKXLUFXIAEUIOZXKXJBABCDE
        MFGHIUGXJXTUJXIAEUKZULUMXIXSJKXJXJXIXMXJNZXOXJNZSZSZXMBQZXOBQZRZLUDZXMQ
        YIXOQRZLEUHZXQXRYEYHYJLEYEYIENZYHYJYEYLYHSZSZYIXMXOYNXRXMCUNQZQZXOYOQZR
        ZYNUAAYPYQYNYPAAUBOZNAAYPPYPAUOYNXTYSXMYOXIXTYSYOPYDYMAYOCEMFGYOUPZUQUT
        ZYNXJXTXMYAXIYBYCYMURZUSVAYPAAVBAAYPVCVDYNYQYSNAAYQPYQAUOYNXTYSXOYOUUAY
        NXJXTXOYAXIYBYCYMVEZUSVAYQAAVBAAYQVCVDYNUAUDZANZSZYICVFQZQZUUDVKZVGQZYP
        QZUUJYQQZUUDYPQUUDYQQUUFUUIVHQZUUKVKZUUMUULVKZRZUUKUULRZUUFUUIYFQZUUIYG
        QZUUNUUOUUFUUIYFYGYEYLYHUUEVEVIUUFEAXMPZEEUJZUUIDNZUURUUNRUUFYBUUTYNYBU
        UEUUBVJXMAEVBZVLUUFEVMZUUFUUICVNQZAVOZDYNUUEUUHUVENUUIUVFNUUFEUVEYIUUGX
        IEUVEUUGPYDYMUUECUVEEUUGFUVEUPZUUGUPVPVQYEYLYHUUEURVAUUHUUDUVEAVRWBACDU
        VEUVGIGVSVTZEABCDXMYOEUUIFGHIYTWAWCUUFEAXOPZUVAUVBUUSUUORUUFYCUVIYNYCUU
        EUUCVJXOAEVBZVLUVDUVHEABCDXOYOEUUIFGHIYTWAWCWDUUPUUMUUMRUUQUUMUUKUUMUUL
        UUIVHWEUUJYPWEWFWGVLUUJUUDYPUUHUUDYIUUGWEUAWLWHZWIUUJUUDYQUVKWIWJWKYEXR
        YRTYMYEXMYOXJUCZQZXOUVLQZRZXRYRXIXJYSUVLUFYDUVOXRTAYOCEMFGYTWMXJYSXMXOU
        VLWNWOYDUVOYRTXIYBYCUVMYPUVNYQXMXJYOXBXOXJYOXBWPWQWRVJWSVIWTXAYDXQYHTXI
        YBYCXNYFXPYGXMXJBXBXOXJBXBWPWQYDXRYKTZXIYBUUTUVIUVPYCUVCUVJUUTXMEUOXOEU
        OUVPUVIEAXMVCEAXOVCLEXMXOXCXDXDWQXEXFJKXJXKXLXGXH $.
    $}

    $( When restricted to complete mappings, the substitution-producing
       function is bijective to the set of all substitutions.  (Contributed by
       Mario Carneiro, 18-Jul-2016.) $)
    msubff1o $p |- ( T e. mFS ->
      ( S |` ( R ^m V ) ) : ( R ^m V ) -1-1-onto-> ran S ) $=
      ( cmfs wcel cmap co cres crn wf1o cmex cfv wf1 eqid msubff1 f1f1orn eqtri
      syl wceq wb cima msubrn df-ima f1oeq3 ax-mp sylibr ) CHIZADJKZBULLZMZUMNZ
      ULBMZUMNZUKULCOPZURJKZUMQUOABCURDEFGURRSULUSUMTUBUPUNUCUQUOUDUPBULUEUNABC
      DEFGUFBULUGUAUPUNULUMUHUIUJ $.
  $}

  ${
    $d v E $.  $d v w H $.  $d v w T $.  $d v w V $.
    mvhf.v $e |- V = ( mVR ` T ) $.
    mvhf.e $e |- E = ( mEx ` T ) $.
    mvhf.h $e |- H = ( mVH ` T ) $.
    $( The function mapping variables to variable expressions is a function.
       (Contributed by Mario Carneiro, 18-Jul-2016.) $)
    mvhf $p |- ( T e. mFS -> H : V --> E ) $=
      ( vv cmfs wcel cv cmty cfv cs1 cop wa cmtc cmrex cxp eqid ffvelcdmda cmcn
      mtyf2 cun cword elun2 adantl wceq mrexval adantr eleqtrrd opelxpi syl2anc
      s1cld mexval eleqtrrdi mvhfval fmptd ) AIJZHDHKZALMZMZUTNZOZBCUSUTDJZPZVD
      AQMZARMZSZBVFVBVGJVCVHJVDVIJUSDVGUTVAAVGDVAEVGTZVATZUCUAVFVCAUBMZDUDZUEZV
      HVFUTVMVEUTVMJUSUTDVLUFUGUNUSVHVNUHVEVLVHADIVLTEVHTZUIUJUKVBVCVGVHULUMVHA
      BVGVJFVOUOUPHACDVAEVKGUQUR $.

    $( The function mapping variables to variable expressions is one-to-one.
       (Contributed by Mario Carneiro, 18-Jul-2016.) $)
    mvhf1 $p |- ( T e. mFS -> H : V -1-1-> E ) $=
      ( vv vw wcel cv cfv wceq wral wa cs1 cop wb mvhval adantl cmfs wf wi mvhf
      wf1 cmty eqid eqeqan12d fvex cword s1cli elexi opth simprbi s111 imbitrid
      cvv sylbid ralrimivva dff13 sylanbrc ) AUAJZDBCUBHKZCLZIKZCLZMZVCVEMZUCZI
      DNHDNDBCUEABCDEFGUDVBVIHIDDVBVCDJZVEDJZOZOZVGVCAUFLZLZVCPZQZVEVNLZVEPZQZM
      ZVHVLVGWARVBVJVKVDVQVFVTACDVCVNEVNUGZGSACDVEVNEWBGSUHTWAVPVSMZVMVHWAVOVRM
      WCVOVPVRVSVCVNUIVPUQUJVCUKULUMUNVLWCVHRVBDVCVEUOTUPURUSHIDBCUTVA $.
  $}

  ${
    $d e f x E $.  $d f x F $.  $d e f H $.  $d e f x T $.  $d e f x X $.
    $d f x V $.
    msubvrs.s $e |- S = ( mSubst ` T ) $.
    msubvrs.e $e |- E = ( mEx ` T ) $.
    msubvrs.v $e |- V = ( mVars ` T ) $.
    msubvrs.h $e |- H = ( mVH ` T ) $.
    $( The set of variables in a substitution is the union, indexed by the
       variables in the original expression, of the variables in the
       substitution to that variable.  (Contributed by Mario Carneiro,
       18-Jul-2016.) $)
    msubvrs $p |- ( ( T e. mFS /\ F e. ran S /\ X e. E ) -> ( V ` ( F ` X ) ) =
      U_ x e. ( V ` X ) ( V ` ( F ` ( H ` x ) ) ) ) $=
      ( ve wcel crn cfv wceq c2nd eqid syl vf cmfs cv ciun c1st cop cmpt cmrsub
      wrex wi elmsubrn eleq2i cmex fvexi mptex elrnmpti bitri w3a cmvar cin cs1
      wa cmrex simp2 cmtc cxp simp3 mexval eleqtrdi xp2nd mrsubvrs fveq2 2fveq3
      syl2anc opeq12d opex fvmpt3i fveq2d xp1st mrsubf eleq2s ffvelcdmd opelxpi
      wf eleqtrrdi mvrsval fvex op2nd a1i rneqd ineq1d 3eqtrd iuneq1d cmty mvhf
      3ad2ant1 inss2 sseli ffvelcdm syl2an adantl mvhval cvv cword s1cli op1std
      elexi op2ndd eqtrd simpl1 mtyf2 adantr cmcn elun2 s1cld eleqtrrd iuneq2dv
      mrexval 3eqtr4d fveq1 iuneq2d eqeq12d syl5ibrcom com23 rexlimdva biimtrid
      cun 3expia 3imp ) CUBNZEBOZNZHDNZHEPZGPZAHGPZAUCZFPZEPZGPZUDZQZYLEMDMUCZU
      EPZUUCRPUAUCZPZUFZUGZQZUACUHPZOZUIZYJYMUUBUJZYLEUAUUKUUHUGZOZNUULYKUUOEBC
      MUADUUJJUUJSZIUKULUAUUKUUHEUUNUUNSMDUUGDCUMJUNUOUPUQYJUUIUUMUAUUKYJUUEUUK
      NZVBYMUUIUUBYJUUQYMUUIUUBUJYJUUQYMURZUUBUUIHUUHPZGPZAYPYRUUHPZGPZUDZQUURH
      RPZUUEPZOZCUSPZUTZAUVDOZUVGUTZYQVAZUUEPZOZUVGUTZUDZUUTUVCUURUUQUVDCVCPZNZ
      UVHUVOQYJUUQYMVDZUURHCVEPZUVPVFZNZUVQUURHDUVTYJUUQYMVGZUVPCDUVSUVSSZJUVPS
      ZVHZVIZHUVSUVPVJZTAUVPUUJCUUEUVGUVDUUPUVGSZUWDVKVNUURUUTHUEPZUVEUFZGPZUWJ
      RPZOZUVGUTZUVHUURUUSUWJGUURYMUUSUWJQUWBMHUUGUWJDUUHUUCHQUUDUWIUUFUVEUUCHU
      EVLUUCHUUERVMVOUUHSZUUDUUFVPZVQTVRUURUWJDNUWKUWNQUURUWJUVTDUURUWIUVSNZUVE
      UVPNUWJUVTNUURUWAUWQUWFHUVSUVPVSTUURUVPUVPUVDUUEUURUUQUVPUVPUUEWDZUVRUVPU
      UJCUUEUUPUWDVTTZUURYMUVQUWBUVQHUVTDUWGUWEWATWBUWIUVEUVSUVPWCVNUWEWECDUVGG
      UWJUWHJKWFTUURUWMUVFUVGUURUWLUVEUWLUVEQUURUWIUVEHUEWGUVDUUEWGWHWIWJWKWLUU
      RUVCAUVJUVBUDUVOUURAYPUVJUVBUURYMYPUVJQUWBCDUVGGHUWHJKWFTWMUURAUVJUVBUVNU
      URYQUVJNZVBZUVBYQCWNPZPZUVLUFZGPZUXDRPZOZUVGUTZUVNUXAUVAUXDGUXAUVAYRUEPZY
      RRPZUUEPZUFZUXDUXAYRDNZUVAUXLQUURUVGDFWDZYQUVGNZUXMUWTYJUUQUXNYMCDFUVGUWH
      JLWOWPUVJUVGYQUVIUVGWQWRZUVGDYQFWSWTMYRUUGUXLDUUHUUCYRQUUDUXIUUFUXKUUCYRU
      EVLUUCYRUUERVMVOUWOUWPVQTUXAUXIUXCUXKUVLUXAYRUXCUVKUFQZUXIUXCQUXAUXOUXQUW
      TUXOUURUXPXAZCFUVGYQUXBUWHUXBSZLXBTZUXCUVKYRYQUXBWGZUVKXCXDYQXEXGZXFTUXAU
      XJUVKUUEUXAUXQUXJUVKQUXTUXCUVKYRUYAUYBXHTVRVOXIVRUXAUXDDNUXEUXHQUXAUXDUVT
      DUXAUXCUVSNUVLUVPNUXDUVTNUXAUVGUVSYQUXBUXAYJUVGUVSUXBWDYJUUQYMUWTXJZCUVSU
      VGUXBUWHUWCUXSXKTUXRWBUXAUVPUVPUVKUUEUURUWRUWTUWSXLUXAUVKCXMPZUVGYGZXDZUV
      PUXAYQUYEUXAUXOYQUYENUXRYQUVGUYDXNTXOUXAYJUVPUYFQUYCUYDUVPCUVGUBUYDSUWHUW
      DXRTXPWBUXCUVLUVSUVPWCVNUWEWECDUVGGUXDUWHJKWFTUXAUXGUVMUVGUXAUXFUVLUXFUVL
      QUXAUXCUVLUYAUVKUUEWGWHWIWJWKWLXQXIXSUUIYOUUTUUAUVCUUIYNUUSGHEUUHXTVRUUIA
      YPYTUVBUUIYSUVAGYREUUHXTVRYAYBYCYHYDYEYFYI $.
  $}

  ${
    $d d h t D $.  $d c d h m o p s t v E $.  $d a b c d h m o p s t v x z H $.
    $d c d h m o p s t v x y B $.  $d m o p s t v x C $.  $d c m o p s x y L $.
    $d c d h m o p s t A $.  $d m o p s x y O $.  $d a b c d h s t v x y z S $.
    $d a b m o p s x y M $.  $d c m o p s x y P $.  $d c d h m o p s t x y T $.
    $d a b c d h m o p s v x y ph $.  $d c m o p s v Q $.  $d c d h t v x V $.
    $d a b c m o p s x z W $.  $d c m o p s x y X $.  $d c m o p s x y Y $.
    $d a b c d h m o p s t v x y z K $.
    mclsval.d $e |- D = ( mDV ` T ) $.
    mclsval.e $e |- E = ( mEx ` T ) $.
    mclsval.c $e |- C = ( mCls ` T ) $.
    $( Reverse closure for the closure function.  (Contributed by Mario
       Carneiro, 18-Jul-2016.) $)
    mclsrcl $p |- ( A e. ( K C B ) -> ( T e. _V /\ K C_ D /\ B C_ E ) ) $=
      ( vt vd vh wcel cvv wss c0 cmcls cfv cv vc vm vo vp vs vx vy co n0i fvprc
      wceq wn eqtrid oveqd 0ov eqtrdi nsyl2 wa cmdv cpw wi fveq2 eqtr4di eleq2d
      cmex fvex elpw2 sseq2d bitrid anbi12d imbi12d cmvh crn cun cotp cmax cima
      wbr cmvrs cxp wal cmsub wral cab cint cmpo vex mpoex df-mcls fvmpt2 mp2an
      pwex elmpocl vtoclg mpcom simpld simprd 3jca ) AGBCUHZNZEONZGDPZBFPZWTWSQ
      UKXAWSAUIXAULZWSGBQUHQXDCQGBXDCERSZQJERUJUMUNGBUOUPUQZWTXBXCXAWTXBXCURZXF
      AGBKTZRSZUHZNZGXHUSSZUTZNZBXHVESZUTZNZURZVAWTXGVAKEOXHEUKZXKWTXRXGXSXJWSA
      XSXICGBXSXIXECXHERVBJVCUNVDXSXNXBXQXCXNGXLPXSXBGXLXHUSVFZVGXSXLDGXSXLEUSS
      DXHEUSVBHVCVHVIXQBXOPXSXCBXOXHVEVFZVGXSXOFBXSXOEVESFXHEVEVBIVCVHVIVJVKLMX
      MXPMTXHVLSZVMZVNUATZPUBTZUCTZUDTZVOXHVPSNUETZYFYCVNVQYDPUFTZUGTZYEVRYIYBS
      YHSXHVSSZSYJYBSYHSYKSVTLTPVAUGWAUFWAURYGYHSYDNVAUEXHWBSVMWCVAUDWAUCWAUBWA
      URUAWDWEZGBXIAXHONLMXMXPYLWFZONXIYMUKKWGLMXMXPYLXLXTWLXOYAWLWHKOYMORUFUGK
      MUBUCUEUDUALWIWJWKWMWNWOZWPWTXBXCYNWQWR $.

    mclsval.1 $e |- ( ph -> T e. mFS ) $.
    mclsval.2 $e |- ( ph -> K C_ D ) $.
    mclsval.3 $e |- ( ph -> B C_ E ) $.
    ${
      mclsval.h $e |- H = ( mVH ` T ) $.
      mclsval.a $e |- A = ( mAx ` T ) $.
      mclsval.s $e |- S = ( mSubst ` T ) $.
      mclsval.v $e |- V = ( mVars ` T ) $.
      $( Lemma for ~ mclsssv .  (Contributed by Mario Carneiro,
         18-Jul-2016.) $)
      mclsssvlem $p |- ( ph -> |^| { c | ( ( B u. ran H ) C_ c /\
            A. m A. o A. p ( <. m , o , p >. e. A ->
              A. s e. ran S ( ( ( s " ( o u. ran H ) ) C_ c /\
       A. x A. y ( x m y ->
         ( ( V ` ( s ` ( H ` x ) ) ) X. ( V ` ( s ` ( H ` y ) ) ) ) C_ K ) ) ->
         ( s ` p ) e. c ) ) ) } C_ E ) $=
        ( crn cun cv wss cotp wcel cima wbr cfv cxp wi wal wral cint cmvar cmfs
        wa cab eqid mvhf syl frnd unssd msubf cmpst cmsta maxsta mstapst sstrdi
        wf sselda ccnv cfn elmpst simp3bi ffvelcdm syl2anr ralrimiva ex alrimiv
        wceq a1d alrimivv cmex fvexi sseq2 anbi1d imbi12d ralbidv imbi2d albidv
        eleq2 2albidv anbi12d elab sylanbrc intss1 ) ALEMUIZUJZRUKZULZJUKZKUKZQ
        UKZUMZDUNZPUKZXKXFUJUOZXHULZBUKZCUKZXJUPXRMUQXOUQOUQXSMUQXOUQOUQURNULUS
        CUTBUTZVEZXLXOUQZXHUNZUSZPHUIZVAZUSZQUTZKUTJUTZVEZRVFZUNZYKVBLULAXGLULZ
        XNXPLULZXTVEZYBLUNZUSZPYEVAZUSZQUTZKUTJUTZYLAEXFLUDAIVCUQZLMAIVDUNZUUBL
        MVRUBILMUUBUUBVGTUEVHVIVJVKAYTJKAYSQAXNYRAXNVEZYQPYEUUDXOYEUNZVEYPYOUUE
        LLXOVRXLLUNZYPUUDHILXOUGTVLUUDXMIVMUQZUNZUUFADUUGXMADIVNUQZUUGAUUCDUUIU
        LUBDUUIIUFUUIVGZVOVIUUGUUIIUUGVGZUUJVPVQVSUUHXJGULXJVTXJWIVEXKLULXKWAUN
        VEUUFXLXJUUGILXKGSTUUKWBWCVILLXLXOWDWEWJWFWGWHWKYJYMUUAVERLLIWLTWMXHLWI
        ZXIYMYIUUAXHLXGWNUULYHYTJKUULYGYSQUULYFYRXNUULYDYQPYEUULYAYOYCYPUULXQYN
        XTXHLXPWNWOXHLYBWTWPWQWRWSXAXBXCXDLYKXEVI $.

      $( The function mapping variables to variable expressions is one-to-one.
         (Contributed by Mario Carneiro, 18-Jul-2016.) $)
      mclsval $p |- ( ph -> ( K C B ) = |^| { c | ( ( B u. ran H ) C_ c /\
            A. m A. o A. p ( <. m , o , p >. e. A ->
              A. s e. ran S ( ( ( s " ( o u. ran H ) ) C_ c /\
       A. x A. y ( x m y ->
         ( ( V ` ( s ` ( H ` x ) ) ) X. ( V ` ( s ` ( H ` y ) ) ) ) C_ K ) ) ->
         ( s ` p ) e. c ) ) ) } ) $=
        ( vd vh vt cpw cv crn cun wss cotp wcel cima wbr cfv cxp wi wal wa wral
        cab cint cvv cmcls cmpo cmfs wceq elex cmdv cmex cmvh cmvrs cmsub fveq2
        eqtr4di pweqd rneqd uneq2d sseq1d eleq2d imaeq2d fveq1d fveq12d xpeq12d
        fveq2d imbi2d 2albidv anbi12d imbi1d raleqbidv albidv abbidv mpoeq123dv
        cmax imbi12d inteqd df-mcls fvexi pwex mpoex fvmpt eqtrid simprr uneq1d
        3syl simprl sseq2d anbi2d ralbidv elpw2 sylibr mclsssvlem ssex ovmpod
        syl ) AUIUJNEGULZLULZUJUMZMUNZUOZRUMZUPZJUMZKUMZQUMZUQZDURZPUMZYJYEUOZU
        SZYGUPZBUMZCUMZYIUTZYRMVAZYNVAZOVAZYSMVAZYNVAZOVAZVBZUIUMZUPZVCZCVDBVDZ
        VEZYKYNVAYGURZVCZPHUNZVFZVCZQVDZKVDJVDZVEZRVGZVHZEYEUOZYGUPZYMYQYTUUGNU
        PZVCZCVDBVDZVEZUUMVCZPUUOVFZVCZQVDZKVDJVDZVEZRVGZVHZFVIAFIVJVAZUIUJYBYC
        UVBVKZUAAIVLURIVIURUVQUVRVMUBIVLVNUKIUIUJUKUMZVOVAZULZUVSVPVAZULZYDUVSV
        QVAZUNZUOZYGUPZYLUVSWTVAZURZYNYJUWEUOZUSZYGUPZYTYRUWDVAZYNVAZUVSVRVAZVA
        ZYSUWDVAZYNVAZUWOVAZVBZUUHUPZVCZCVDBVDZVEZUUMVCZPUVSVSVAZUNZVFZVCZQVDZK
        VDJVDZVEZRVGZVHZVKUVRVIVJUVSIVMZUIUJUWAUWCUXNYBYCUVBUXOUVTGUXOUVTIVOVAG
        UVSIVOVTSWAWBUXOUWBLUXOUWBIVPVALUVSIVPVTTWAWBUXOUXMUVAUXOUXLUUTRUXOUWGY
        HUXKUUSUXOUWFYFYGUXOUWEYEYDUXOUWDMUXOUWDIVQVAMUVSIVQVTUEWAZWCZWDWEUXOUX
        JUURJKUXOUXIUUQQUXOUWIYMUXHUUPUXOUWHDYLUXOUWHIWTVADUVSIWTVTUFWAWFUXOUXE
        UUNPUXGUUOUXOUXFHUXOUXFIVSVAHUVSIVSVTUGWAWCUXOUXDUULUUMUXOUWLYQUXCUUKUX
        OUWKYPYGUXOUWJYOYNUXOUWEYEYJUXQWDWGWEUXOUXBUUJBCUXOUXAUUIYTUXOUWTUUGUUH
        UXOUWPUUCUWSUUFUXOUWNUUBUWOOUXOUWOIVRVAOUVSIVRVTUHWAZUXOUWMUUAYNUXOYRUW
        DMUXPWHWKWIUXOUWRUUEUWOOUXRUXOUWQUUDYNUXOYSUWDMUXPWHWKWIWJWEWLWMWNWOWPX
        AWQWMWNWRXBWSBCUKUJJKPQRUIXCUIUJYBYCUVBGGIVOSXDZXELLIVPTXDZXEXFXGXKXHAU
        UHNVMZYDEVMZVEVEZUVAUVOUYCUUTUVNRUYCYHUVDUUSUVMUYCYFUVCYGUYCYDEYEAUYAUY
        BXIXJWEUYCUURUVLJKUYCUUQUVKQUYCUUPUVJYMUYCUUNUVIPUUOUYCUULUVHUUMUYCUUKU
        VGYQUYCUUJUVFBCUYCUUIUVEYTUYCUUHNUUGAUYAUYBXLXMWLWMXNWOXOWLWQWMWNWRXBAN
        GUPNYBURUCNGUXSXPXQAELUPEYCURUDELUXTXPXQAUVPLUPUVPVIURABCDEFGHIJKLMNOPQ
        RSTUAUBUCUDUEUFUGUHXRUVPLUXTXSYAXT $.
    $}

    $( The closure of a set of expressions is a set of expressions.
       (Contributed by Mario Carneiro, 18-Jul-2016.) $)
    mclsssv $p |- ( ph -> ( K C B ) C_ E ) $=
      ( vc vm vo vp cfv cv wal vs vx vy co cmvh crn cun wss cotp cmax wcel cima
      wbr cmvrs cxp wi wa cmsub wral cab cint eqid mclsval mclsssvlem eqsstrd )
      AGBCUDBEUERZUFZUGNSZUHOSZPSZQSZUIEUJRZUKUASZVJVGUGULVHUHUBSZUCSZVIUMVNVFR
      VMREUNRZRVOVFRVMRVPRUOGUHUPUCTUBTUQVKVMRVHUKUPUAEURRZUFUSUPQTPTOTUQNUTVAF
      AUBUCVLBCDVQEOPFVFGVPUAQNHIJKLMVFVBZVLVBZVQVBZVPVBZVCAUBUCVLBCDVQEOPFVFGV
      PUAQNHIJKLMVRVSVTWAVDVE $.

    ${
      ssmclslem.h $e |- H = ( mVH ` T ) $.
      $( Lemma for ~ ssmcls .  (Contributed by Mario Carneiro, 18-Jul-2016.) $)
      ssmclslem $p |- ( ph -> ( B u. ran H ) C_ ( K C B ) ) $=
        ( vc cv wss cfv wal vm vo vp vs vx vy crn cun cotp cmax wcel cima cmvrs
        wbr cxp wi wa cmsub wral cab cint simpl a1i alrimiv ssintab sylibr eqid
        co mclsval sseqtrrd ) ABGUGZUHZVLPQZRZUAQZUBQZUCQZUIEUJSZUKUDQZVPVKUHUL
        VMRUEQZUFQZVOUNVTGSVSSEUMSZSWAGSVSSWBSUOHRUPUFTUETUQVQVSSVMUKUPUDEURSZU
        GUSUPUCTUBTUATZUQZPUTVAZHBCVHAWEVNUPZPTVLWFRAWGPWGAVNWDVBVCVDWEPVLVEVFA
        UEUFVRBCDWCEUAUBFGHWBUDUCPIJKLMNOVRVGWCVGWBVGVIVJ $.

      vhmcls.v $e |- V = ( mVR ` T ) $.
      vhmcls.3 $e |- ( ph -> X e. V ) $.
      $( All variable hypotheses are in the closure.  (Contributed by Mario
         Carneiro, 18-Jul-2016.) $)
      vhmcls $p |- ( ph -> ( H ` X ) e. ( K C B ) ) $=
        ( wcel crn cfv ssmclslem unssbd wfn cmfs mvhf ffn 3syl fnfvelrn syl2anc
        co wf sseldd ) AGUAZHBCULZJGUBZABUOUPABCDEFGHKLMNOPQUCUDAGIUEZJITUQUOTA
        EUFTIFGUMURNEFGIRLQUGIFGUHUISIJGUJUKUN $.
    $}

    $( The original expressions are also in the closure.  (Contributed by Mario
       Carneiro, 18-Jul-2016.) $)
    ssmcls $p |- ( ph -> B C_ ( K C B ) ) $=
      ( cmvh cfv crn co eqid ssmclslem unssad ) ABENOZPGBCQABCDEFUAGHIJKLMUARST
      $.

    ${
      ss2mcls.4 $e |- ( ph -> X C_ K ) $.
      ss2mcls.5 $e |- ( ph -> Y C_ B ) $.
      $( The closure is monotonic under subsets of the original set of
         expressions and the set of disjoint variable conditions.  (Contributed
         by Mario Carneiro, 18-Jul-2016.) $)
      ss2mcls $p |- ( ph -> ( X C Y ) C_ ( K C B ) ) $=
        ( cfv wss wal vc vm vo vp vs vx vy cmvh crn cun cotp cmax wcel cima wbr
        cv cmvrs cxp wi wa cmsub wral cab cint unss1 sstr2 3syl syl5com 2alimdv
        co imim2d anim2d imim1d ralimdv alimdv anim12d ss2abdv intss sstrd eqid
        syl mclsval 3sstr4d ) AIEUHRZUIZUJZUAUPZSZUBUPZUCUPZUDUPZUKEULRZUMZUEUP
        ZWJWEUJUNWGSZUFUPZUGUPZWIUOZWPWDRWNREUQRZRWQWDRWNRWSRURZHSZUSZUGTUFTZUT
        ZWKWNRWGUMZUSZUEEVARZUIZVBZUSZUDTZUCTUBTZUTZUAVCZVDZBWEUJZWGSZWMWOWRWTG
        SZUSZUGTUFTZUTZXEUSZUEXHVBZUSZUDTZUCTUBTZUTZUAVCZVDZHICVJGBCVJAYHXNSXOY
        ISAYGXMUAAXQWHYFXLAIBSWFXPSXQWHUSQIBWEVEWFXPWGVFVGAYEXKUBUCAYDXJUDAYCXI
        WMAYBXFUEXHAXDYAXEAXCXTWOAXBXSUFUGAXAXRWRAHGSXAXRPWTHGVFVHVKVIVLVMVNVKV
        OVIVPVQYHXNVRWAAUFUGWLICDXGEUBUCFWDHWSUEUDUAJKLMAHGDPNVSAIBFQOVSWDVTZWL
        VTZXGVTZWSVTZWBAUFUGWLBCDXGEUBUCFWDGWSUEUDUAJKLMNOYJYKYLYMWBWC $.
    $}

    mclsax.a $e |- A = ( mAx ` T ) $.
    mclsax.l $e |- L = ( mSubst ` T ) $.
    mclsax.v $e |- V = ( mVR ` T ) $.
    mclsax.h $e |- H = ( mVH ` T ) $.
    mclsax.w $e |- W = ( mVars ` T ) $.
    ${
      mclsax.4 $e |- ( ph -> <. M , O , P >. e. A ) $.
      mclsax.5 $e |- ( ph -> S e. ran L ) $.
      mclsax.6 $e |- ( ( ph /\ x e. O ) -> ( S ` x ) e. ( K C B ) ) $.
      mclsax.7 $e |- ( ( ph /\ v e. V ) -> ( S ` ( H ` v ) ) e. ( K C B ) ) $.
      mclsax.8 $e |- ( ( ph /\ ( x M y /\ a e. ( W ` ( S ` ( H ` x ) ) ) /\
        b e. ( W ` ( S ` ( H ` y ) ) ) ) ) -> a K b ) $.
      $( The closure is closed under axiom application.  (Contributed by Mario
         Carneiro, 18-Jul-2016.) $)
      mclsax $p |- ( ph -> ( S ` P ) e. ( K C B ) ) $=
        ( vc vm vo vp vs vz cfv crn cun cv wss cotp wcel cima wbr cxp wi wal wa
        wral cab cint co abid intss1 sylbir sseq1d imbitrrid sstr2 com12 anim1d
        mclsval imim1d ralimdv imim2d alimdv 2alimdv adantl cmpst cvv w3a cmsta
        sylcom eqid mstapst cmfs maxsta sseldd sselid mpstrcl simp1 simp2 simp3
        wceq oteq123d eleq1d uneq1d imaeq2d breqd imbi1d 2albidv anbi12d fveq2d
        syl imbi12d ralbidv spc3gv 3syl wo elun ralrimiva wf wfn mvhf ffn fveq2
        wb ralrn mpbird r19.21bi sseqtrrd sylibr fveq1 jaodan sylan2b cdm msubf
        wfun ffund ccnv elmpst sylib simp2d simpld fdmd unssd funimass4 syl2anc
        cfn frnd 3exp2 imp4b ralrimivv dfss3 eleq1 df-br bitr4di ralxp bitri ex
        cop alrimivv jca imaeq1 xpeq12d imbi2d rspcv mpid embantd 3syld alrimiv
        fvex elintab eleqtrrd ) AIJVDZFMVEZVFURVGZVHZUSVGZUTVGZVAVGZVIZEVJZVBVG
        ZUWGUWCVFZVKZUWDVHZBVGZCVGZUWFVLZUWOMVDZUWKVDZSVDZUWPMVDZUWKVDZSVDZVMZN
        VHZVNZCVOBVOZVPZUWHUWKVDZUWDVJZVNZVBOVEZVQZVNZVAVOZUTVOUSVOZVPZURVRZVSZ
        NFGVTZAUXQUWBUWDVJZVNZURVOUWBUXSVJAUYBURAUXQUWJUWMUXTVHZUXGVPZUXJVNZVBU
        XLVQZVNZVAVOZUTVOUSVOZPQIVIZEVJZUWKQUWCVFZVKZUXTVHZUWOUWPPVLZUXEVNZCVOB
        VOZVPZIUWKVDZUWDVJZVNZVBUXLVQZVNZUYAAUXQUXTUWDVHZUYIUXQVUDAUXSUWDVHZUXQ
        UWDUXRVJVUEUXQURWAUWDUXRWBWCAUXTUXSUWDABCEFGHOKUSUTLMNSVBVAURUBUCUDUEUF
        UGUKUHUIULWIZWDWEUXPVUDUYIVNUWEVUDUXPUYIVUDUXOUYHUSUTVUDUXNUYGVAVUDUXMU
        YFUWJVUDUXKUYEVBUXLVUDUYDUXHUXJVUDUYCUWNUXGUYCVUDUWNUWMUXTUWDWFWGWHWJWK
        WLWMWNWGWOWTAUYJKWPVDZVJZPWQVJQWQVJIWQVJWRUYIVUCVNAKWSVDZVUGUYJVUGVUIKV
        UGXAZVUIXAZXBAEVUIUYJAKXCVJZEVUIVHUEEVUIKUHVUKXDYAUMXEXFZIPVUGKQVUJXGUY
        GVUCUSUTVAPQIWQWQWQUWFPXKZUWGQXKZUWHIXKZWRZUWJUYKUYFVUBVUQUWIUYJEVUQUWF
        PUWGQUWHIVUNVUOVUPXHZVUNVUOVUPXIZVUNVUOVUPXJZXLXMVUQUYEVUAVBUXLVUQUYDUY
        RUXJUYTVUQUYCUYNUXGUYQVUQUWMUYMUXTVUQUWLUYLUWKVUQUWGQUWCVUSXNXOWDVUQUXF
        UYPBCVUQUWQUYOUXEVUQUWFPUWOUWPVURXPXQXRXSVUQUXIUYSUWDVUQUWHIUWKVUTXTXMY
        BYCYBYDYEAUYKVUBUYAUMAVUBJUYLVKZUXTVHZUYOUWRJVDZSVDZUXAJVDZSVDZVMZNVHZV
        NZCVOBVOZVPZUYAAVVBVVJAVVBUWOJVDZUXTVJZBUYLVQZAVVMBUYLUWOUYLVJAUWOQVJZU
        WOUWCVJZYFVVMUWOQUWCYGAVVOVVMVVPUOAVVMBUWCAVVMBUWCVQZDVGMVDZJVDZUXTVJZD
        RVQZAVVTDRUPYHARLMYIZMRYJVVQVWAYNAVULVWBUEKLMRUJUCUKYKYAZRLMYLVVMVVTBDR
        MUWOVVRXKVVLVVSUXTUWOVVRJYMXMYOYEYPYQUUAUUBYHAJUUEUYLJUUCZVHVVBVVNYNALL
        JAJUXLVJZLLJYIUNOKLJUIUCUUDYAZUUFAQUWCVWDAQLVWDAQLVHZQUUPVJZAPHVHPUUGPX
        KVPZVWGVWHVPZILVJZAVUHVWIVWJVWKWRVUMIPVUGKLQHUBUCVUJUUHUUIUUJUUKALLJVWF
        UULZYRAUWCLVWDARLMVWCUUQVWLYRUUMBUYLUXTJUUNUUOYPAVVIBCAUYOVVHAUYOVPZTVG
        ZUAVGZNVLZUAVVFVQTVVDVQZVVHVWMVWPTUAVVDVVFAUYOVWNVVDVJZVWOVVFVJZVWPAUYO
        VWRVWSVWPUQUURUUSUUTVVHVCVGZNVJZVCVVGVQVWQVCVVGNUVAVXAVWPVCTUAVVDVVFVWT
        VWNVWOUVHZXKVXAVXBNVJVWPVWTVXBNUVBVWNVWONUVCUVDUVEUVFYSUVGUVIUVJAVWEVUB
        VVKUYAVNZVNUNVUAVXCVBJUXLUWKJXKZUYRVVKUYTUYAVXDUYNVVBUYQVVJVXDUYMVVAUXT
        UWKJUYLUVKWDVXDUYPVVIBCVXDUXEVVHUYOVXDUXDVVGNVXDUWTVVDUXCVVFVXDUWSVVCSU
        WRUWKJYTXTVXDUXBVVESUXAUWKJYTXTUVLWDUVMXRXSVXDUYSUWBUWDIUWKJYTXMYBUVNYA
        UVOUVPUVQUVRUXQURUWBIJUVSUVTYSVUFUWA $.
    $}

    mclsind.4 $e |- ( ph -> B C_ Q ) $.
    mclsind.5 $e |- ( ( ph /\ v e. V ) -> ( H ` v ) e. Q ) $.
    mclsind.6 $e |- ( ( ph /\ ( <. m , o , p >. e. A /\
      s e. ran L /\ ( s " ( o u. ran H ) ) C_ Q ) /\
      A. x A. y ( x m y ->
       ( ( W ` ( s ` ( H ` x ) ) ) X. ( W ` ( s ` ( H ` y ) ) ) ) C_ K ) )
    -> ( s ` p ) e. Q ) $.
    $( Induction theorem for closure: any other set ` Q ` closed under the
       axioms and the hypotheses contains all the elements of the closure.
       (Contributed by Mario Carneiro, 18-Jul-2016.) $)
    mclsind $p |- ( ph -> ( K C B ) C_ Q ) $=
      ( vc co crn cun cv wss cotp wcel cima wbr cfv cxp wi wal wa wral cab cint
      mclsval cin ssind wfn cmfs mvhf syl ffnd ffvelcdmda elind ralrimiva ffnfv
      wf sylanbrc frnd unssd inss2 sstrdi w3a cmap cmrex cpm adantr eqid msubff
      frn 3syl simpr2 sseldd elmapi cmpst cmsta maxsta mstapst simpr1 ccnv wceq
      id elmpst simp3bi ffvelcdmd 3adant3 3exp 3expd imp31 syl5 impd ex alrimiv
      cfn alrimivv fvexi inex1 sseq2 anbi1d eleq2 imbi12d ralbidv imbi2d albidv
      cmex 2albidv anbi12d elab intss1 eqsstrd ) AOFGUPFNUQZURZUOUSZUTZKUSZLUSZ
      TUSZVAZEVBZSUSZUUDYSURVCZUUAUTZBUSZCUSZUUCVDUUKNVEUUHVERVEUULNVEUUHVERVEV
      FOUTVGCVHBVHZVIZUUEUUHVEZUUAVBZVGZSPUQZVJZVGZTVHZLVHKVHZVIZUOVKZVLZIABCEF
      GHPJKLMNORSTUOUAUBUCUDUEUFUJUGUHUKVMAUVEMIVNZIAUVFUVDVBZUVEUVFUTAYTUVFUTZ
      UUGUUIUVFUTZUUMVIZUUOUVFVBZVGZSUURVJZVGZTVHZLVHKVHZUVGAFYSUVFAFMIUFULVOAQ
      UVFNANQVPDUSZNVEZUVFVBZDQVJQUVFNWEAQMNAJVQVBZQMNWEUDJMNQUIUBUJVRVSZVTAUVS
      DQAUVQQVBVIMIUVRAQMUVQNUWAWAUMWBWCDQUVFNWDWFWGWHAUVOKLAUVNTAUUGUVMAUUGVIZ
      UVLSUURUWBUUHUURVBZVIZUVIUUMUVKUVIUUIIUTZUWDUUMUVKVGZUVIUUIUVFIUVIXJMIWIZ
      WJAUUGUWCUWEUWFVGAUUGUWCUWEUWFAUUGUWCUWEWKZUUMUVKAUWHUUMWKMIUUOAUWHUUOMVB
      UUMAUWHVIZMMUUEUUHUWIUUHMMWLUPZVBMMUUHWEUWIUURUWJUUHUWIUVTJWMVEZQWNUPZUWJ
      PWEUURUWJUTAUVTUWHUDWOZUWKPJMQVQUIUWKWPUHUBWQUWLUWJPWRWSAUUGUWCUWEWTXAUUH
      MMXBVSUWIUUFJXCVEZVBZUUEMVBZUWIEUWNUUFUWIEJXDVEZUWNUWIUVTEUWQUTUWMEUWQJUG
      UWQWPZXEVSUWNUWQJUWNWPZUWRXFWJAUUGUWCUWEXGXAUWOUUCHUTUUCXHUUCXIVIUUDMUTUU
      DYBVBVIUWPUUEUUCUWNJMUUDHUAUBUWSXKXLVSXMXNUNWBXOXPXQXRXSWCXTYAYCUVCUVHUVP
      VIUOUVFMIMJYMUBYDYEUUAUVFXIZUUBUVHUVBUVPUUAUVFYTYFUWTUVAUVOKLUWTUUTUVNTUW
      TUUSUVMUUGUWTUUQUVLSUURUWTUUNUVJUUPUVKUWTUUJUVIUUMUUAUVFUUIYFYGUUAUVFUUOY
      HYIYJYKYLYNYOYPWFUVFUVDYQVSUWGWJYR $.
  $}

  ${
    $d a d h A $.  $d a d h t x C $.  $d a d h t x P $.  $d a d h t x T $.
    $d a d h D $.  $d a d h H $.
    mppsval.p $e |- P = ( mPreSt ` T ) $.
    mppsval.j $e |- J = ( mPPSt ` T ) $.
    ${
      mppsval.c $e |- C = ( mCls ` T ) $.
      $( Lemma for ~ mppspst .  (Contributed by Mario Carneiro,
         18-Jul-2016.) $)
      mppspstlem $p |- { <. <. d , h >. , a >. |
        ( <. d , h , a >. e. P /\ a e. ( d C h ) ) } C_ P $=
        ( vx cv cotp wcel co wa coprab cop wceq wex cab df-oprab eqeq2i biimpri
        df-ot eleq1d biimpar adantrr exlimiv exlimivv abssi eqsstri ) GLZDLZFLZ
        MZBNZUOUMUNAONZPZGDFQKLZUMUNRUORZSZUSPZFTZDTGTZKUABUSGDFKUBVEKBVDUTBNZG
        DVCVFFVBUQVFURVBVFUQVBUTUPBUTUPSVBUPVAUTUMUNUOUEUCUDUFUGUHUIUJUKUL $.

      $( Definition of a provable pre-statement, essentially just a
         reorganization of the arguments of df-mcls .  (Contributed by Mario
         Carneiro, 18-Jul-2016.) $)
      mppsval $p |- J = { <. <. d , h >. , a >. |
        ( <. d , h , a >. e. P /\ a e. ( d C h ) ) } $=
        ( vt vx cmpps cfv cv wcel wa cmpst c0 wex cotp co coprab cvv wceq cmcls
        fveq2 eqtr4di eleq2d oveqd anbi12d df-mpps fvexi mppspstlem ssexi fvmpt
        oprabbidv wn fvprc cop cab df-oprab wne elfvex eleq2s ad2antrl exlimivv
        abn0 sylbi necon1bi eqtrid eqtr4d pm2.61i eqtri ) ECMNZGOZDOZFOZUAZBPZV
        RVPVQAUBZPZQZGDFUCZICUDPZVOWDUEKCVSKOZRNZPZVRVPVQWFUFNZUBZPZQZGDFUCWDUD
        MWFCUEZWLWCGDFWMWHVTWKWBWMWGBVSWMWGCRNZBWFCRUGHUHUIWMWJWAVRWMWIAVPVQWMW
        ICUFNAWFCUFUGJUHUJUIUKUQKDFGULWDBBCRHUMABCDEFGHIJUNUOUPWEURZVOSWDCMUSWO
        WDLOVPVQUTVRUTUEZWCQZFTDTZGTZLVAZSWCGDFLVBWEWTSWTSVCWSLTWEWSLVHWRWELGWQ
        WEDFVTWEWPWBWEVSWNBVSCRVDHVEVFVGVGVIVJVKVLVMVN $.

      $( Definition of a provable pre-statement, essentially just a
         reorganization of the arguments of df-mcls .  (Contributed by Mario
         Carneiro, 18-Jul-2016.) $)
      elmpps $p |- ( <. D , H , A >. e. J <->
        ( <. D , H , A >. e. P /\ A e. ( D C H ) ) ) $=
        ( vd vh va cotp wcel cop cv wa cvv wceq co coprab df-ot mppsval eleq12i
        cxp oprabss sseli mpstssv eqeltrrid adantr opelxp w3a simp1 simp2 simp3
        wb oteq123d eleq1d oveq12d eleq12d anbi12d eloprabga 3expa sylanb sylbi
        pm5.21nii bitri ) CFANZGOCFPZAPZKQZLQZMQZNZDOZVNVLVMBUAZOZRZKLMUBZOZVID
        OZACFBUAZOZRZVIVKGVTCFAUCZBDELGMKHIJUDUEWAVKSSUFZSUFZOZWEVTWHVKVSKLMUGU
        HWBWIWDWBVKVIWHWFDWHVIDEHUIUHUJUKWIVJWGOZASOZRWAWEUQZVJAWGSULWJCSOZFSOZ
        RWKWLCFSSULWMWNWKWLVSWEKLMCFASSSVLCTZVMFTZVNATZUMZVPWBVRWDWRVOVIDWRVLCV
        MFVNAWOWPWQUNZWOWPWQUOZWOWPWQUPZURUSWRVNAVQWCXAWRVLCVMFBWSWTUTVAVBVCVDV
        EVFVGVH $.
    $}

    $( A provable pre-statement is a pre-statement.  (Contributed by Mario
       Carneiro, 18-Jul-2016.) $)
    mppspst $p |- J C_ P $=
      ( vd vh va cv cotp wcel cmcls cfv co wa coprab mppsval mppspstlem eqsstri
      eqid ) CFIZGIZHIZJAKUCUAUBBLMZNKOFGHPAUDABGCHFDEUDTZQUDABGCHFDEUERS $.
  $}

  ${
    $d t x J $.  $d t x R $.  $d t x T $.  $d x X $.  $d x Y $.
    mthmval.r $e |- R = ( mStRed ` T ) $.
    mthmval.j $e |- J = ( mPPSt ` T ) $.
    mthmval.u $e |- U = ( mThm ` T ) $.
    $( A theorem is a pre-statement, whose reduct is also the reduct of a
       provable pre-statement.  Unlike the difference between pre-statement and
       statement, this application of the reduct is not necessarily trivial:
       there are theorems that are not themselves provable but are provable
       once enough "dummy variables" are introduced.  (Contributed by Mario
       Carneiro, 18-Jul-2016.) $)
    mthmval $p |- U = ( `' R " ( R " J ) ) $=
      ( vt cmthm cfv ccnv cima cvv wcel wceq cmsr cmpps fveq2 eqtr4di c0 cnveqd
      cv imaeq12d df-mthm fvex cnvex imaexg ax-mp fvmpt3i wn 0ima eqcomi eqtrid
      fvprc cnv0 eqtrdi imaeq1d 3eqtr4a pm2.61i eqtri ) CBIJZAKZADLZLZGBMNZVAVD
      OHBHUBZPJZKZVGVFQJZLZLZVDMIVFBOZVHVBVJVCVLVGAVLVGBPJZAVFBPRESZUAVLVGAVIDV
      NVLVIBQJDVFBQRFSUCUCHUDVHMNVKMNVGVFPUEUFVHVJMUGUHUIVEUJZTTVCLZVAVDVPTVCUK
      ULBIUNVOVBTVCVOVBTKTVOATVOAVMTEBPUNUMUAUOUPUQURUSUT $.

    $( A theorem is a pre-statement, whose reduct is also the reduct of a
       provable pre-statement.  (Contributed by Mario Carneiro,
       18-Jul-2016.) $)
    elmthm $p |- ( X e. U <-> E. x e. J ( R ` x ) = ( R ` X ) ) $=
      ( wcel ccnv cima cmpst cfv wa cv wceq wrex wb ax-mp mthmval eleq2i wfn wf
      eqid msrf ffn elpreima wss mppspst fvelimab mp2an anbi2i msrrcl syl5ibcom
      sseli rexlimiv pm4.71ri bitr4i 3bitri ) FDJFBKBELZLZJZFCMNZJZFBNZVAJZOZAP
      ZBNVFQZAERZDVBFBCDEGHIUAUBBVDUCZVCVHSVDVDBUDVLVDBCVDUEZGUFVDVDBUGTZVDFVAB
      UHTVHVEVKOVKVGVKVEVLEVDUIVGVKSVNVDCEVMHUJZAVDEVFBUKULUMVKVEVJVEAEVIEJVIVD
      JVJVEEVDVIVOUPVDBCVIFVMGUNUOUQURUSUT $.

    $( A statement whose reduct is the reduct of a provable pre-statement is a
       theorem.  (Contributed by Mario Carneiro, 18-Jul-2016.) $)
    mthmi $p |- ( ( X e. J /\ ( R ` X ) = ( R ` Y ) ) -> Y e. U ) $=
      ( vx wcel cfv wceq wa cv wrex fveqeq2 rspcev elmthm sylibr ) EDKEALFALZMZ
      NJOZALUAMZJDPFCKUDUBJEDUCEUAAQRJABCDFGHIST $.
  $}

  ${
    mthmsta.u $e |- U = ( mThm ` T ) $.
    mthmsta.s $e |- S = ( mPreSt ` T ) $.
    $( A theorem is a pre-statement.  (Contributed by Mario Carneiro,
       18-Jul-2016.) $)
    mthmsta $p |- U C_ S $=
      ( cmsr cfv ccnv cmpps cima eqid mthmval cdm cnvimass msrf sseqtri eqsstri
      fdmi ) CBFGZHSBIGZJZJZASBCTSKZTKDLUBSMASUANAASASBEUCORPQ $.
  $}

  ${
    $d x J $.  $d x U $.
    mppsthm.j $e |- J = ( mPPSt ` T ) $.
    mppsthm.u $e |- U = ( mThm ` T ) $.
    $( A provable pre-statement is a theorem.  (Contributed by Mario Carneiro,
       18-Jul-2016.) $)
    mppsthm $p |- J C_ U $=
      ( vx cv wcel cmsr cfv wceq eqid mthmi mpan2 ssriv ) FCBFGZCHPAIJZJZRKPBHR
      LQABCPPQLDEMNO $.
  $}

  ${
    $d x R $.  $d x T $.  $d x U $.  $d x Y $.
    mthmb.r $e |- R = ( mStRed ` T ) $.
    mthmb.u $e |- U = ( mThm ` T ) $.
    $( Lemma for ~ mthmb .  (Contributed by Mario Carneiro, 18-Jul-2016.) $)
    mthmblem $p |- ( ( R ` X ) = ( R ` Y ) -> ( X e. U -> Y e. U ) ) $=
      ( vx wcel cmpst cfv cmpps cima wa wceq ccnv eqid mthmval eleq2i ax-mp wfn
      wb wf msrf ffn elpreima bitri eleq1 wrex wfun ffun fvelima mpan rexlimiva
      cv mthmi syl biimtrdi adantld biimtrid ) DCIZDBJKZIZDAKZABLKZMZIZNZVDEAKZ
      OZECIZVADAPVFMZIZVHCVLDABCVEFVEQZGRSAVBUAZVMVHUBVBVBAUCZVOVBABVBQFUDZVBVB
      AUETVBDVFAUFTUGVJVGVKVCVJVGVIVFIZVKVDVIVFUHVRHUOZAKVIOZHVEUIZVKAUJZVRWAVP
      WBVQVBVBAUKTHVIVEAULUMVTVKHVEABCVEVSEFVNGUPUNUQURUSUT $.

    $( If two statements have the same reduct then one is a theorem iff the
       other is.  (Contributed by Mario Carneiro, 18-Jul-2016.) $)
    mthmb $p |- ( ( R ` X ) = ( R ` Y ) -> ( X e. U <-> Y e. U ) ) $=
      ( cfv wceq wcel mthmblem wi eqcoms impbid ) DAHZEAHZIDCJZECJZABCDEFGKRQLP
      OABCEDFGKMN $.
  $}

  ${
    $d x A $.  $d x C $.  $d x H $.  $d x J $.  $d x M $.  $d x R $.  $d x T $.
    $d x U $.
    mthmpps.r $e |- R = ( mStRed ` T ) $.
    mthmpps.j $e |- J = ( mPPSt ` T ) $.
    mthmpps.u $e |- U = ( mThm ` T ) $.
    mthmpps.d $e |- D = ( mDV ` T ) $.
    mthmpps.v $e |- V = ( mVars ` T ) $.
    mthmpps.z $e |- Z = U. ( V " ( H u. { A } ) ) $.
    mthmpps.m $e |- M = ( C u. ( D \ ( Z X. Z ) ) ) $.
    $( Given a theorem, there is an explicitly definable witnessing provable
       pre-statement for the provability of the theorem.  (However, this
       pre-statement requires infinitely many disjoint variable conditions,
       which is sometimes inconvenient.)  (Contributed by Mario Carneiro,
       18-Jul-2016.) $)
    mthmpps $p |- ( T e. mFS -> ( <. C , H , A >. e. U <->
      ( <. M , H , A >. e. J /\
        ( R ` <. M , H , A >. ) = ( R ` <. C , H , A >. ) ) ) ) $=
      ( wcel wceq vx cmfs cotp cfv wa cmpst cmcls co wss ccnv cmex cfn cxp cdif
      cun w3a eqid mthmsta simpr sselid elmpst sylib simp1d simpld difssd unssd
      eqsstrid simprd cnvdif cmvar cid cnvxp cnvi difeq12i eqtri mdvval 3eqtr4i
      cnveqi a1i uneq12d cnvun 3eqtr4g jca simp2d simp3d syl3anbrc cv wrex c1st
      elmthm simpll adantr cin c2nd csn cima cuni mppspst simprl mpst123 fveq2d
      syl simprr eqtr3d eqeltrrd msrval 3eqtr3d fvex inex1 sneqd imaeq2d unieqd
      otth eqtr4di sqxpeqd ineq2d inss1 eqsstrrdi eqidd oteq123d simp1bi ssdifd
      eqtrd unss12 syl2anc inundif eqcomi 3sstr4g ss2mcls elmpps simprbi sseldd
      ssidd rexlimddv sylanbrc ineq1i indir c0 disjdifr 0ss eqsstri mpbi 3eqtri
      ssequn2 oteq1d 3eqtr4d ex mthmi impbid1 ) EUBSZBGAUCZFSZIGAUCZHSZUUMDUDZU
      UKDUDZTZUEZUUJUULUURUUJUULUEZUUNUUQUUSUUMEUFUDZSZAIGEUGUDZUHZSZUUNUUSICUI
      ZIUJZITZUEGEUKUDZUIZGULSZUEZAUVHSZUVAUUSUVEUVGUUSIBCKKUMZUNZUOZCRUUSBUVNC
      UUSBCUIZBUJZBTZUUSUVPUVRUEZUVKUVLUUSUUKUUTSZUVSUVKUVLUPUUSFUUTUUKUUTEFNUU
      TUQZURUUJUULUSZUTZABUUTEUVHGCOUVHUQZUWAVAVBZVCZVDUUSCUVMVEVFVGZUUSUVQUVNU
      JZUOZUVOUVFIUUSUVQBUWHUVNUUSUVPUVRUWFVHUWHUVNTUUSUWHCUJZUVMUJZUNUVNCUVMVI
      UWJCUWKUVMEVJUDZUWLUMZVKUNZUJZUWNUWJCUWOUWMUJZVKUJZUNUWNUWMVKVIUWPUWMUWQV
      KUWLUWLVLVMVNVOCUWNCEUWLUWLUQOVPZVRUWRVQKKVLVNVOVSVTUVFUVOUJUWIIUVORVRBUV
      NWAVORWBWCUUSUVSUVKUVLUWEWDZUUSUVSUVKUVLUWEWEAIUUTEUVHGCOUWDUWAVAWFZUUSUA
      WGZDUDZUUPTZUVDUAHUUSUULUXCUAHWHUWBUADEFHUUKLMNWJVBUUSUXAHSZUXCUEZUEZUXAW
      IUDZWIUDZGUVBUHZUVCAUXFGUVBCEUVHIUXHGOUWDUVBUQZUUJUULUXEWKUUSUVEUXEUWGWLU
      USUVIUXEUUSUVIUVJUWSVDWLUXFUXHUVMWMZUXHUVMUNZUOZUVOUXHIUXFUXKBUIUXLUVNUIU
      XMUVOUIUXFUXKBUVMWMZBUXFUXHJUXGWNUDZUXAWNUDZWOZUOZWPZWQZUXTUMZWMZUXNUXKUX
      FUYBUXNTZUXOGTZUXPATZUXFUYBUXOUXPUCZUXNGAUCZTUYCUYDUYEUPUXFUXHUXOUXPUCZDU
      DZUUPUYFUYGUXFUXBUYIUUPUXFUXAUYHDUXFUXAUUTSUXAUYHTUXFHUUTUXAUUTEHUWAMWRUU
      SUXDUXCWSZUTZUUTEUXAUWAWTXBZXAUUSUXDUXCXCXDUXFUYHUUTSUYIUYFTUXFUXAUYHUUTU
      YLUYKXEUXPUXHUUTDEUXOJUXTPUWALUXTUQXFXBUUSUUPUYGTZUXEUUSUVTUYMUWCABUUTDEG
      JKPUWALQXFXBZWLXGUYBUXOUXNGUXPAUXHUYAUXGWIXHXIUXGWNXHUXAWNXHXMVBZVCUXFUYA
      UVMUXHUXFUXTKUXFUXTJGAWOZUOZWPZWQKUXFUXSUYRUXFUXRUYQJUXFUXOGUXQUYPUXFUYCU
      YDUYEUYOWDZUXFUXPAUXFUYCUYDUYEUYOWEZXJVTXKXLQXNXOXPXDBUVMXQXRUXFUXHCUVMUX
      FUXHGAUCZUUTSZUXHCUIZUXFUXAVUAUUTUXFUXAUYHVUAUYLUXFUXHUXHUXOGUXPAUXFUXHXS
      UYSUYTXTYCZUYKXEVUBVUCUXHUJUXHTZVUBVUCVUEUEUVKUVLAUXHUUTEUVHGCOUWDUWAVAYA
      VDXBYBUXKBUXLUVNYDYEUXMUXHUXHUVMYFYGRYHUXFGYMYIUXFVUAHSZAUXISZUXFUXAVUAHV
      UDUYJXEVUFVUBVUGAUVBUXHUUTEGHUWAMUXJYJYKXBYLYNAUVBIUUTEGHUWAMUXJYJYOUUSIU
      VMWMZGAUCZUYGUUOUUPUUSVUHUXNGAVUHUXNTUUSVUHUVOUVMWMUXNUVNUVMWMZUOZUXNIUVO
      UVMRYPBUVNUVMYQVUJUXNUIVUKUXNTVUJYRUXNUVMCYSUXNYTUUAVUJUXNUUDUUBUUCVSUUEU
      USUVAUUOVUITUWTAIUUTDEGJKPUWALQXFXBUYNUUFWCUUGDEFHUUMUUKLMNUUHUUI $.
  $}

  $(
  @{
    mclsppsfi.r @e |- R = ( mStRed ` T ) @.
    mclsppsfi.j @e |- J = ( mPPSt ` T ) @.
    mclsppsfi.u @e |- C = ( mCls ` T ) @.
    @( Any theorem has a proof using a _finite_ number of disjoint variable
       conditions and using only finitely many of the provided hypotheses, to
       reach the same conclusion.  This variation on ~ mclsppsfi also allows
       specifying a subset ` B ` of the hypotheses that will not be dropped.
       (Contributed by Mario Carneiro, 18-Jul-2016.) @)
    mclsppsfi2 @p |- ( ( T e. mFS /\ A e. ( D C H ) /\ B e. ( ~P H i^i Fin ) )
    -> E. d e. Fin E. h e. ( ~P H i^i Fin ) ( B C_ h /\ <. d , h , A >. e. J /\
                       ( R ` <. d , h , A >. ) = ( R ` <. D , h , A >. ) ) ) @=
      ? @.
      @( [18-Jul-2016] @)

    @( Any theorem has a proof using a _finite_ number of disjoint variable
       conditions and using only finitely many of the provided hypotheses, to
       reach the same conclusion.  (Contributed by Mario Carneiro,
       18-Jul-2016.) @)
    mclsppsfi @p |- ( ( T e. mFS /\ A e. ( D C H ) ) ->
              E. d e. Fin E. h e. ( ~P H i^i Fin ) ( <. d , h , A >. e. J /\
                       ( R ` <. d , h , A >. ) = ( R ` <. D , h , A >. ) ) ) @=
      ( wcel wa c0 cv wss cotp cfn wrex cmfs co cfv wceq w3a cpw cin 0fi elfpw
      0ss mpbir2an mclsppsfi2 mp3an3 3simpc reximi syl ) EUAMZACGBUBMZNOFPZQZIP
      USARZHMZVADUCCUSARDUCUDZUEZFGUFSUGZTZISTZVBVCNZFVETZISTUQUROVEMZVGVJOGQOS
      MGUJUHOGUIUKAOBCDEFGHIJKLULUMVFVIISVDVHFVEUTVBVCUNUOUOUP @.
      @( [18-Jul-2016] @)
  @}

  @{
    mthmppsfi.r @e |- R = ( mStRed ` T ) @.
    mthmppsfi.j @e |- J = ( mPPSt ` T ) @.
    mthmppsfi.u @e |- U = ( mThm ` T ) @.
    @( Any theorem has a proof using a _finite_ number of disjoint variable
       conditions.  (Unlike ~ mclsppsfi , we do not need to prove that there is
       a finite subset of the hypotheses because ` H ` is already finite.)
       (Contributed by Mario Carneiro, 18-Jul-2016.) @)
    mthmppsfi @p |- ( ( T e. mFS /\ <. D , H , A >. e. U ) ->
                    E. d e. Fin ( <. d , H , A >. e. J /\
                       ( R ` <. d , H , A >. ) = ( R ` <. D , H , A >. ) ) ) @=
      ( vx wcel cotp wa cfv wceq cfn wss eqid vh cmfs cv wrex simpr elmthm c1st
      sylib w3a cpw cin cmcls co simpll cmpst mppspst simprl sselid mpst123 syl
      c2nd eqidd csn cun cima cuni fveq2d simprr eqtr3d eqeltrrd msrval mthmsta
      cmvrs simplr 3eqtr3d fvex inex1 otth simp2d simp3d oteq123d eqtrd simprbi
      cxp elmpps ssid a1i cmex cmdv ccnv elmpst simprd elfpw mclsppsfi2 syl3anc
      sylanbrc wi simpld eqssd oteq2d eleq1d adantr eqeq12d anbi12d biimpd expr
      expd 3impd rexlimdva reximdv mpd ) DUBMZBFANZEMZOZLUCZCPZXMCPZQZLGUDZHUC
      ZFANZGMZYBCPZXRQZOZHRUDZXOXNXTXLXNUELCDEGXMIJKUFUHXOXSYGLGXOXPGMZXSYGXOYH
      XSOZOZFUAUCZSZYAYKANZGMZYMCPZXPUGPZUGPZYKANZCPZQZUIZUAFUJRUKZUDZHRUDZYGYJ
      XLAYQFDULPZUMMZFUUBMZUUDXLXNYIUNYJYQFANZGMZUUFYJXPUUHGYJXPYQYPVAPZXPVAPZN
      ZUUHYJXPDUOPZMXPUULQYJGUUMXPUUMDGUUMTZJUPXOYHXSUQZURZUUMDXPUUNUSUTZYJYQYQ
      UUJFUUKAYJYQVBYJYQDVMPZUUJUUKVCVDVEVFZUUSWDZUKZBUURFAVCVDVEVFZUVBWDUKZQZU
      UJFQZUUKAQZYJUVAUUJUUKNZUVCFANZQUVDUVEUVFUIYJUULCPZXRUVGUVHYJXQUVIXRYJXPU
      ULCUUQVGXOYHXSVHZVIYJUULUUMMUVIUVGQYJXPUULUUMUUQUUPVJUUKYQUUMCDUUJUURUUSU
      URTZUUNIUUSTVKUTYJXMUUMMZXRUVHQYJEUUMXMUUMDEKUUNVLXLXNYIVNURZABUUMCDFUURU
      VBUVKUUNIUVBTVKUTVOUVAUUJUVCFUUKAYQUUTYPUGVPVQYPVAVPXPVAVPVRUHZVSYJUVDUVE
      UVFUVNVTWAWBZUUOVJUUIUUHUUMMUUFAUUEYQUUMDFGUUNJUUETZWEWCUTYJFFSZFRMZUUGUV
      QYJFWFWGYJFDWHPZSZUVRYJBDWIPZSBWJBQOZUVTUVROZAUVSMZYJUVLUWBUWCUWDUIUVMABU
      UMDUVSFUWAUWATUVSTUUNWKUHVSWLFFWMWPAFUUEYQCDUAFGHIJUVPWNWOYJUUCYFHRYJUUAY
      FUAUUBYJYKUUBMZOYLYNYTYFYJUWEYLYNYTYFWQWQYJUWEYLOZOZYNYTYFUWGYNYTOYFUWGYN
      YCYTYEUWGYMYBGUWGYKFYAAUWGYKFUWGYKFSZYKRMZUWGUWEUWHUWIOYJUWEYLUQYKFWMUHWR
      YJUWEYLVHWSZWTZXAUWGYOYDYSXRUWGYMYBCUWKVGUWGYSUUHCPZXRUWGYRUUHCUWGYKFYQAU
      WJWTVGYJUWLXRQUWFYJXQUWLXRYJXPUUHCUVOVGUVJVIXBWBXCXDXEXGXFXHXIXJXKXFXIXK
      @.
      @( [18-Jul-2016] @)
  @}
  $)

  ${
    $d m o p s t u v E $.  $d a b c m o p s t u v w x y z H $.  $d c t v z V $.
    $d a b c d m o p s t u v x y K $.  $d a b c d m o p s u v w x y z T $.
    $d a b c d m o p s v w x y z L $.  $d a b c d m o p s t u v x y S $.
    $d a b c d m o p s t v x y B $.  $d a b c m o p s u v w x y z W $.
    $d a b c m o p s t v x y z C $.  $d a b m o p s v w x y z M $.
    $d m o p s v w x z O $.  $d a b c d t u v x y ph $.
    mclspps.d $e |- D = ( mDV ` T ) $.
    mclspps.e $e |- E = ( mEx ` T ) $.
    mclspps.c $e |- C = ( mCls ` T ) $.
    mclspps.1 $e |- ( ph -> T e. mFS ) $.
    mclspps.2 $e |- ( ph -> K C_ D ) $.
    mclspps.3 $e |- ( ph -> B C_ E ) $.
    mclspps.j $e |- J = ( mPPSt ` T ) $.
    mclspps.l $e |- L = ( mSubst ` T ) $.
    mclspps.v $e |- V = ( mVR ` T ) $.
    mclspps.h $e |- H = ( mVH ` T ) $.
    mclspps.w $e |- W = ( mVars ` T ) $.
    mclspps.4 $e |- ( ph -> <. M , O , P >. e. J ) $.
    mclspps.5 $e |- ( ph -> S e. ran L ) $.
    mclspps.6 $e |- ( ( ph /\ x e. O ) -> ( S ` x ) e. ( K C B ) ) $.
    mclspps.7 $e |- ( ( ph /\ v e. V ) -> ( S ` ( H ` v ) ) e. ( K C B ) ) $.
    mclspps.8 $e |- ( ( ph /\ ( x M y /\ a e. ( W ` ( S ` ( H ` x ) ) ) /\
      b e. ( W ` ( S ` ( H ` y ) ) ) ) ) -> a K b ) $.
    ${
      mclsppslem.9 $e |- ( ph -> <. m , o , p >. e. ( mAx ` T ) ) $.
      mclsppslem.10 $e |- ( ph -> s e. ran L ) $.
      mclsppslem.11 $e |- ( ph ->
        ( s " ( o u. ran H ) ) C_ ( `' S " ( K C B ) ) ) $.
      mclsppslem.12 $e |- ( ph -> A. z A. w ( z m w ->
        ( ( W ` ( s ` ( H ` z ) ) ) X. ( W ` ( s ` ( H ` w ) ) ) ) C_ M ) ) $.
      $( The closure is closed under application of provable pre-statements.
         (Compare ~ mclsax .)  This theorem is what justifies the treatment of
         theorems as "equivalent" to axioms once they have been proven: the
         composition of one theorem in the proof of another yields a theorem.
         (Contributed by Mario Carneiro, 18-Jul-2016.) $)
      mclsppslem $p |- ( ph -> ( s ` p ) e. ( `' S " ( K C B ) ) ) $=
        ( vc vd vt vu cv cfv ccnv co cima wcel crn wf msubf syl wss wceq wa cfn
        cotp cmpst w3a cmax cmsta cmfs eqid maxsta mstapst sstrdi sseldd elmpst
        sylib simp3d ffvelcdmd ccom syl2anc msubco wfn fco ffnd adantr cun wfun
        fvco3 cdm wb ffund simpld 3syl elpreima simplbda wbr wrex cxp cid ssbrd
        ciun imp fveq2d msubvrs syl3anc eqtrd eleq2d eliun bitrdi wi wal breq12
        brxp cvv simpl simpr biimtrrid vex simp2bi mvhf frn unssd fdmd sseqtrrd
        funimass3 mpbid cnvco imaeq1i imaco eqtri unssad sselda unssbd fnfvelrn
        sseqtrrdi sylan simp1d cdif mdvval eqsstri simprd anbi12d reeanv simpll
        difss xpeq12d sseq1d imbi12d spc2gv el2v 3anbi123d anbi2d imbi1d vtocl2
        ffn 3exp2 imp4b rexlimdvva sylbid exp4b 3imp2 mclsax eqeltrrd mpbir2and
        ) AUEVLZUDVLZVMZKVNZRGHVOZVPZVQZUWIOVQZUWIKVMZUWKVQZAOOUWGUWHAUWHSVRZVQ
        ZOOUWHVSZVESLOUWHUOUIVTWAZAMVLZIWBZUXAVNUXAWCZWDZNVLZOWBZUXEWEVQZWDZUWG
        OVQZAUXAUXEUWGWFZLWGVMZVQZUXDUXHUXIWHALWIVMZUXKUXJAUXMLWJVMZUXKALWKVQZU
        XMUXNWBUKUXMUXNLUXMWLZUXNWLZWMWAUXKUXNLUXKWLZUXQWNWOVDWPZUWGUXAUXKLOUXE
        IUHUIUXRWQZWRZWSZWTAUWGKUWHXAZVMZUWOUWKAUWSUXIUYDUWOWCUWTUYBOOUWGKUWHXJ
        XBAVHVIVJUXMGHIUWGUYCLOPRSUXAUXEUBUCUFUGUHUIUJUKULUMUXPUOUPUQURVDAKUWQV
        QZUWRUYCUWQVQUTVESLKUWHUOXCXBAVHVLZUXEVQZWDUYCOXDZUYFUYCVNZUWKVPZVQZUYF
        UYCVMUWKVQZAUYHUYGAOOUYCAOOKVSZUWSOOUYCVSAUYEUYMUTSLOKUOUIVTWAZUWTOOOKU
        WHXEXBXFZXGAUXEUYJUYFAUXEPVRZUYJAUXEUYPXHZUWHVNZUWLVPZUYJAUWHUYQVPUWLWB
        ZUYQUYSWBZVFAUWHXIUYQUWHXKZWBUYTVUAXLAOOUWHUWTXMAUYQOVUBAUXEUYPOAUXFUXG
        AUXLUXHUXSUXLUXDUXHUXIUXTUUAWAXNAUXOUBOPVSZUYPOWBUKLOPUBUPUIUQUUBZUBOPU
        UCXOUUDAOOUWHUWTUUEUUFUYQUWLUWHUUGXBUUHUYJUYRUWJXAZUWKVPUYSUYIVUEUWKKUW
        HUUIUUJUYRUWJUWKUUKUULUUQZUUMUUNUYHUYKUYFOVQUYLOUYFUWKUYCXPXQXBAVJVLZUB
        VQZWDZUYHVUGPVMZUYJVQZVUJUYCVMUWKVQZAUYHVUHUYOXGVUIUYPUYJVUJAUYPUYJWBVU
        HAUXEUYPUYJVUFUUOXGAPUBXDZVUHVUJUYPVQAUXOVUCVUMUKVUDUBOPUVQXOUBVUGPUUPU
        URWPUYHVUKVUJOVQVULOVUJUWKUYCXPXQXBAUYFVIVLZUXAXRZUFVLZUYFPVMZUYCVMZUCV
        MZVQZUGVLZVUNPVMZUYCVMZUCVMZVQZVUPVVARXRZAVUOVUTVVEVVFAVUOWDZVUTVVEWDVU
        PVKVLZPVMZKVMZUCVMZVQZVKVUQUWHVMZUCVMZXSZVVAFVLZPVMZKVMZUCVMZVQZFVVBUWH
        VMZUCVMZXSZWDZVVFVVGVUTVVOVVEVWCVVGVUTVUPVKVVNVVKYCZVQVVOVVGVUSVWEVUPVV
        GVUSVVMKVMZUCVMZVWEVVGVURVWFUCVVGUWSVUQOVQVURVWFWCAUWSVUOUWTXGZVVGUBOUY
        FPAVUCVUOAUXOVUCUKVUDWAXGZVVGUYFUBVQZVUNUBVQZVVGUYFVUNUBUBXTZXRZVWJVWKW
        DAVUOVWMAUXAVWLUYFVUNAUXAIVWLAUXBUXCAUXDUXHUXIUYAUUSXNIVWLYAUUTVWLILUBU
        PUHUVAVWLYAUVGUVBWOYBYDUYFVUNUBUBYOWRZXNWTZOOVUQKUWHXJXBYEVVGUXOUYEVVMO
        VQVWGVWEWCAUXOVUOUKXGZAUYEVUOUTXGZVVGOOVUQUWHVWHVWOWTVKSLOKPUCVVMUOUIUR
        UQYFYGYHYIVKVUPVVNVVKYJYKVVGVVEVVAFVWBVVSYCZVQVWCVVGVVDVWRVVAVVGVVDVWAK
        VMZUCVMZVWRVVGVVCVWSUCVVGUWSVVBOVQVVCVWSWCVWHVVGUBOVUNPVWIVVGVWJVWKVWNU
        VCWTZOOVVBKUWHXJXBYEVVGUXOUYEVWAOVQVWTVWRWCVWPVWQVVGOOVVBUWHVWHVXAWTFSL
        OKPUCVWAUOUIURUQYFYGYHYIFVVAVWBVVSYJYKUVDVWDVVLVVTWDZFVWBXSVKVVNXSVVGVV
        FVVLVVTVKFVVNVWBUVEVVGVXBVVFVKFVVNVWBVVGVVHVVNVQVVPVWBVQWDZWDAVVHVVPTXR
        ZVXBVVFYLAVUOVXCUVFVVGVXCVXDVXCVVHVVPVVNVWBXTZXRVVGVXDVVHVVPVVNVWBYOVVG
        VXETVVHVVPAVUOVXETWBZADVLZEVLZUXAXRZVXGPVMZUWHVMZUCVMZVXHPVMZUWHVMZUCVM
        ZXTZTWBZYLZEYMDYMZVUOVXFYLZVGVXSVXTYLVHVIVXRVXTDEUYFVUNYPYPVXGUYFWCZVXH
        VUNWCZWDZVXIVUOVXQVXFVXGUYFVXHVUNUXAYNVYCVXPVXETVYCVXLVVNVXOVWBVYCVXKVV
        MUCVYCVXJVUQUWHVYCVXGUYFPVYAVYBYQYEYEYEVYCVXNVWAUCVYCVXMVVBUWHVYCVXHVUN
        PVYAVYBYRYEYEYEUVHUVIUVJUVKUVLWAYDYBYSYDAVXDVVLVVTVVFAVXDVVLVVTVVFABVLZ
        CVLZTXRZVUPVYDPVMZKVMZUCVMZVQZVVAVYEPVMZKVMZUCVMZVQZWHZWDZVVFYLAVXDVVLV
        VTWHZWDZVVFYLBCVVHVVPVKYTFYTVYDVVHWCZVYEVVPWCZWDZVYPVYRVVFWUAVYOVYQAWUA
        VYFVXDVYJVVLVYNVVTVYDVVHVYEVVPTYNWUAVYIVVKVUPWUAVYHVVJUCWUAVYGVVIKWUAVY
        DVVHPVYSVYTYQYEYEYEYIWUAVYMVVSVVAWUAVYLVVRUCWUAVYKVVQKWUAVYEVVPPVYSVYTY
        RYEYEYEYIUVMUVNUVOVCUVPUVRUVSXBUVTYSUWAUWBUWCUWDUWEAKOXDUWMUWNUWPWDXLAO
        OKUYNXFOUWIUWKKXPWAUWF $.
    $}

    $d m o p s w z ph $.
    $( The closure is closed under application of provable pre-statements.
       (Compare ~ mclsax .)  This theorem is what justifies the treatment of
       theorems as "equivalent" to axioms once they have been proven: the
       composition of one theorem in the proof of another yields a theorem.
       (Contributed by Mario Carneiro, 18-Jul-2016.) $)
    mclspps $p |- ( ph -> ( S ` P ) e. ( K C B ) ) $=
      ( vz vw vm vo vs vp wfn ccnv co cima wcel cfv crn msubf syl ffnd cmax wss
      wf wceq cfn cotp cmpst w3a eqid mppspst sselid elmpst sylib simp1d simpld
      wa simp2d cv wral ralrimiva wfun wb ffund fdmd sseqtrrd funimass5 syl2anc
      cdm mpbird cmfs mvhf ffvelcdmda elpreima adantr mpbir2and cun wbr cxp wal
      3ad2ant1 3ad2antl1 simp21 simp22 simp23 mclsppslem mclsind elmpps simprbi
      wi simp3 sseldd simplbda ) AIKVDZHIVENEFVFZVGZVHZHIVIYGVHZAKKIAIOVJZVHZKK
      IVPUNOJKIUIUCVKVLZVMZAPQFVFZYHHAURUSDJVNVIZQFGYHJUTVAKLPORSVBVCUBUCUDUEAP
      GVOZPVEPVQZAYQYRWIZQKVOZQVRVHZWIZHKVHZAPQHVSZJVTVIZVHZYSUUBUUCWAAMUUEUUDU
      UEJMUUEWBZUHWCUMWDHPUUEJKQGUBUCUUGWEWFZWGWHAYTUUAAYSUUBUUCUUHWJWHZYPWBUIU
      JUKULAQYHVOZBWKZIVIYGVHZBQWLZAUULBQUOWMAIWNQIXAZVOUUJUUMWOAKKIYMWPAQKUUNU
      UIAKKIYMWQWRBQYGIWSWTXBADWKZRVHZWIUUOLVIZYHVHZUUQKVHZUUQIVIYGVHZARKUUOLAJ
      XCVHZRKLVPUEJKLRUJUCUKXDVLXEUPAUURUUSUUTWIWOZUUPAYFUVBYNKUUQYGIXFVLXGXHAU
      TWKZVAWKZVCWKVSYPVHZVBWKZYKVHZUVFUVDLVJXIVGYHVOZWAZURWKZUSWKZUVCXJUVJLVIU
      VFVISVIUVKLVIUVFVISVIXKPVOYBUSXLURXLZWABCURUSDEFGHIJUTVAKLMNOPQRSVBVCTUAU
      BUCUDAUVIUVAUVLUEXMAUVINGVOUVLUFXMAUVIEKVOUVLUGXMUHUIUJUKULAUVIUUDMVHZUVL
      UMXMAUVIYLUVLUNXMAUVIUUKQVHUULUVLUOXNAUVIUUPUUTUVLUPXNAUVIUUKCWKZPXJTWKZU
      UKLVIIVISVIVHUAWKZUVNLVIIVISVIVHWAUVOUVPNXJUVLUQXNAUVEUVGUVHUVLXOAUVEUVGU
      VHUVLXPAUVEUVGUVHUVLXQAUVIUVLYCXRXSAUVMHYOVHZUMUVMUUFUVQHFPUUEJQMUUGUHUDX
      TYAVLYDYFYIUUCYJKHYGIXFYEWT $.
  $}

  $(
  @{
    mthmco.d @e |- D = ( mDV ` T ) @.
    mthmco.e @e |- E = ( mEx ` T ) @.
    mthmco.1 @e |- ( ph -> T e. mFS ) @.
    mthmco.2 @e |- ( ph -> K C_ D ) @.
    mthmco.3 @e |- ( ph -> B C_ E ) @.
    mthmco.j @e |- U = ( mThm ` T ) @.
    mthmco.l @e |- L = ( mSubst ` T ) @.
    mthmco.v @e |- V = ( mVR ` T ) @.
    mthmco.h @e |- H = ( mVH ` T ) @.
    mthmco.w @e |- W = ( mVars ` T ) @.
    mthmco.4 @e |- ( ph -> <. M , O , P >. e. U ) @.
    mthmco.5 @e |- ( ph -> S e. ran L ) @.
    mthmco.6 @e |- ( ( ph /\ x e. O ) ->
      <. K , B , ( S ` x ) >. e. U ) @.
    mthmco.7 @e |- ( ( ph /\ v e. V ) ->
      <. K , B , ( S ` ( H ` v ) ) >. e. U ) @.
    mthmco.8 @e |- ( ( ph /\ ( x M y /\ a e. ( W ` ( S ` ( H ` x ) ) ) /\
      b e. ( W ` ( S ` ( H ` y ) ) ) ) ) -> a K b ) @.
    @( The application of a theorem to a collection of theorems is a theorem.
       (Compare ~ mclsax .)  This is what justifies the treatment of
       theorems as "equivalent" to axioms once they have been proven: the
       composition of one theorem in the proof of another yields a theorem.

       This theorem has a similar statement to ~ mclspps , but deals with the
       elimination of dummy variables instead of raw composition. The
       assumption ~ mfsinf that there are enough variables of each type is
       essential for this proof. @)
    mthmco @p |- ( ph -> <. K , B , ( S ` P ) >. e. U ) @=
      ? @.
  @}
  $)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Grammatical formal systems
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c m0St $.
  $c mSA $.
  $c mWGFS $.
  $c mSyn $.
  $c mESyn $.
  $c mGFS $.
  $c mTree $.
  $c mST $.
  $c mSAX $.
  $c mUFS $.

  $( Mapping expressions to statements. $)
  cm0s $a class m0St $.

  $( The set of syntax axioms. $)
  cmsa $a class mSA $.

  $( The set of weakly grammatical formal systems. $)
  cmwgfs $a class mWGFS $.

  $( The syntax typecode function. $)
  cmsy $a class mSyn $.

  $( The syntax typecode function for expressions. $)
  cmesy $a class mESyn $.

  $( The set of grammatical formal systems. $)
  cmgfs $a class mGFS $.

  $( The set of proof trees. $)
  cmtree $a class mTree $.

  $( The set of syntax trees. $)
  cmst $a class mST $.

  $( The indexing set for a syntax axiom. $)
  cmsax $a class mSAX $.

  $( The set of unambiguous formal systems. $)
  cmufs $a class mUFS $.

  $( Define a function mapping expressions to statements.  (Contributed by
     Mario Carneiro, 14-Jul-2016.) $)
  df-m0s $a |- m0St = ( a e. _V |-> <. (/) , (/) , a >. ) $.

  ${
    $d a c d e h m o p r s t x y $.
    $( Define the set of syntax axioms.  (Contributed by Mario Carneiro,
       14-Jul-2016.) $)
    df-msa $a |- mSA = ( t e. _V |-> { a e. ( mEx ` t ) |
      ( ( m0St ` a ) e. ( mAx ` t ) /\ ( 1st ` a ) e. ( mVT ` t ) /\
        Fun ( `' ( 2nd ` a ) |` ( mVR ` t ) ) ) } ) $.

    $( Define the set of weakly grammatical formal systems.  (Contributed by
       Mario Carneiro, 14-Jul-2016.) $)
    df-mwgfs $a |- mWGFS = { t e. mFS | A. d A. h A. a
      ( ( <. d , h , a >. e. ( mAx ` t ) /\ ( 1st ` a ) e. ( mVT ` t ) ) ->
        E. s e. ran ( mSubst ` t ) a e. ( s " ( mSA ` t ) ) ) } $.

    $( Define the syntax typecode function.  (Contributed by Mario Carneiro,
       14-Jul-2016.) $)
    df-msyn $a |- mSyn = Slot 6 $.

    $( Define the syntax typecode function for expressions.  (Contributed by
       Mario Carneiro, 12-Jun-2023.) $)
    df-mesyn $a |- mESyn = ( t e. _V |->
      ( c e. ( mTC ` t ) , e e. ( mREx ` t ) |->
        ( ( ( mSyn ` t ) ` c ) m0St e ) ) ) $.

    $( Define the set of grammatical formal systems.  (Contributed by Mario
       Carneiro, 12-Jun-2023.) $)
    df-mgfs $a |- mGFS = { t e. mWGFS |
      ( ( mSyn ` t ) : ( mTC ` t ) --> ( mVT ` t ) /\
        A. c e. ( mVT ` t ) ( ( mSyn ` t ) ` c ) = c /\
        A. d A. h A. a ( <. d , h , a >. e. ( mAx ` t ) ->
          A. e e. ( h u. { a } )
            ( ( mESyn ` t ) ` e ) e. ( mPPSt ` t ) ) ) } $.

    $( Define the set of proof trees.  (Contributed by Mario Carneiro,
       14-Jul-2016.) $)
    df-mtree $a |- mTree = ( t e. _V |->
      ( d e. ~P ( mDV ` t ) , h e. ~P ( mEx ` t ) |->
        |^| { r | ( A. e e. ran ( mVH ` t ) e r <. ( m0St ` e ) , (/) >. /\
          A. e e. h e r <. ( ( mStRed ` t ) ` <. d , h , e >. ) , (/) >. /\
        A. m A. o A. p ( <. m , o , p >. e. ( mAx ` t ) ->
            A. s e. ran ( mSubst ` t ) ( A. x A. y ( x m y ->
        ( ( ( mVars ` t ) ` ( s ` ( ( mVH ` t ) ` x ) ) ) X.
          ( ( mVars ` t ) ` ( s ` ( ( mVH ` t ) ` y ) ) ) ) C_ d ) ->
           ( { ( s ` p ) } X. X_ e e. ( o u. ( ( mVH ` t ) "
        U. ( ( mVars ` t ) " ( o u. { p } ) ) ) ) ( r " { ( s ` e ) } ) ) C_ r
      ) ) ) } ) ) $.

    $( Define the function mapping syntax expressions to syntax trees.
       (Contributed by Mario Carneiro, 14-Jul-2016.) $)
    df-mst $a |- mST = ( t e. _V |->
      ( ( (/) ( mTree ` t ) (/) ) |` ( ( mEx ` t ) |` ( mVT ` t ) ) ) ) $.

    $( Define the indexing set for a syntax axiom's representation in a tree.
       (Contributed by Mario Carneiro, 14-Jul-2016.) $)
    df-msax $a |- mSAX = ( t e. _V |->
      ( p e. ( mSA ` t ) |-> ( ( mVH ` t ) " ( ( mVars ` t ) ` p ) ) ) ) $.
  $}

  $( Define the set of unambiguous formal systems.  (Contributed by Mario
     Carneiro, 14-Jul-2016.) $)
  df-mufs $a |- mUFS = { t e. mGFS | Fun ( mST ` t ) } $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Models of formal systems
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c mUV $.
  $c mVL $.
  $c mVSubst $.
  $c mFresh $.
  $c mFRel $.
  $c mEval $.
  $c mMdl $.
  $c mUSyn $.
  $c mGMdl $.
  $c mItp $.
  $c mFromItp $.

  $( The universe of a model. $)
  cmuv $a class mUV $.

  $( The set of valuations. $)
  cmvl $a class mVL $.

  $( Substitution for a valuation. $)
  cmvsb $a class mVSubst $.

  $( The freshness relation of a model. $)
  cmfsh $a class mFresh $.

  $( The set of freshness relations. $)
  cmfr $a class mFRel $.

  $( The evaluation function of a model. $)
  cmevl $a class mEval $.

  $( The set of models. $)
  cmdl $a class mMdl $.

  $( The syntax function applied to elements of the model. $)
  cusyn $a class mUSyn $.

  $( The set of models in a grammatical formal system. $)
  cgmdl $a class mGMdl $.

  $( The interpretation function of the model. $)
  cmitp $a class mItp $.

  $( The evaluation function derived from the interpretation. $)
  cmfitp $a class mFromItp $.

  $( Define the universe of a model.  (Contributed by Mario Carneiro,
     14-Jul-2016.) $)
  df-muv $a |- mUV = Slot 7 $.

  $( Define the freshness relation of a model.  (Contributed by Mario Carneiro,
     14-Jul-2016.) $)
  df-mfsh $a |- mFresh = Slot ; 1 9 $.

  $( Define the evaluation function of a model.  (Contributed by Mario
     Carneiro, 14-Jul-2016.) $)
  df-mevl $a |- mEval = Slot ; 2 0 $.

  ${
    $d a c d e f g h i m n p r s t u v w x y z $.
    $( Define the set of valuations.  (Contributed by Mario Carneiro,
       14-Jul-2016.) $)
    df-mvl $a |- mVL = ( t e. _V |-> X_ v e. ( mVR ` t )
      ( ( mUV ` t ) " { ( ( mType ` t ) ` v ) } ) ) $.

    $( Define substitution applied to a valuation.  (Contributed by Mario
       Carneiro, 14-Jul-2016.) $)
    df-mvsb $a |- mVSubst = ( t e. _V |-> { <. <. s , m >. , x >. |
      ( ( s e. ran ( mSubst ` t ) /\ m e. ( mVL ` t ) ) /\
         A. v e. ( mVR ` t ) m dom ( mEval ` t ) ( s ` ( ( mVH ` t ) ` v ) ) /\
      x = ( v e. ( mVR ` t ) |->
        ( m ( mEval ` t ) ( s ` ( ( mVH ` t ) ` v ) ) ) ) ) } ) $.

    $( Define the set of freshness relations.  (Contributed by Mario Carneiro,
       14-Jul-2016.) $)
    df-mfrel $a |- mFRel = ( t e. _V |->
      { r e. ~P ( ( mUV ` t ) X. ( mUV ` t ) ) | ( `' r = r /\
        A. c e. ( mVT ` t ) A. w e. ( ~P ( mUV ` t ) i^i Fin )
          E. v e. ( ( mUV ` t ) " { c } ) w C_ ( r " { v } ) ) } ) $.

    $( Define the set of models of a formal system.  (Contributed by Mario
       Carneiro, 14-Jul-2016.) $)
    df-mdl $a |- mMdl = { t e. mFS |
      [. ( mUV ` t ) / u ]. [. ( mEx ` t ) / x ].
      [. ( mVL ` t ) / v ]. [. ( mEval ` t ) / n ]. [. ( mFresh ` t ) / f ].
   ( ( u C_ ( ( mTC ` t ) X. _V ) /\ f e. ( mFRel ` t ) /\
       n e. ( u ^pm ( v X. ( mEx ` t ) ) ) ) /\ A. m e. v
  ( ( A. e e. x ( n " { <. m , e >. } ) C_ ( u " { ( 1st ` e ) } ) /\
      A. y e. ( mVR ` t ) <. m , ( ( mVH ` t ) ` y ) >. n ( m ` y ) /\
      A. d A. h A. a ( <. d , h , a >. e. ( mAx ` t ) ->
        ( ( A. y A. z ( y d z -> ( m ` y ) f ( m ` z ) ) /\
            h C_ ( dom n " { m } ) ) -> m dom n a ) ) ) /\
    ( A. s e. ran ( mSubst ` t ) A. e e. ( mEx ` t )
        A. y ( <. s , m >. ( mVSubst ` t ) y ->
        ( n " { <. m , ( s ` e ) >. } ) = ( n " { <. y , e >. } ) ) /\
      A. p e. v A. e e. x
        ( ( m |` ( ( mVars ` t ) ` e ) ) = ( p |` ( ( mVars ` t ) ` e ) ) ->
          ( n " { <. m , e >. } ) = ( n " { <. p , e >. } ) ) /\
      A. y e. u A. e e. x ( ( m " ( ( mVars ` t ) ` e ) ) C_ ( f " { y } ) ->
          ( n " { <. m , e >. } ) C_ ( f " { y } ) ) ) ) ) } $.

    $( Define the syntax typecode function for the model universe.
       (Contributed by Mario Carneiro, 14-Jul-2016.) $)
    df-musyn $a |- mUSyn = ( t e. _V |-> ( v e. ( mUV ` t ) |->
      <. ( ( mSyn ` t ) ` ( 1st ` v ) ) , ( 2nd ` v ) >. ) ) $.

    $( Define the set of models of a grammatical formal system.  (Contributed
       by Mario Carneiro, 14-Jul-2016.) $)
    df-gmdl $a |- mGMdl = { t e. ( mGFS i^i mMdl ) |
     ( A. c e. ( mTC ` t ) ( ( mUV ` t ) " { c } ) C_
          ( ( mUV ` t ) " { ( ( mSyn ` t ) ` c ) } ) /\
       A. v e. ( mUV ` c ) A. w e. ( mUV ` c ) ( v ( mFresh ` t ) w <->
          v ( mFresh ` t ) ( ( mUSyn ` t ) ` w ) ) /\
       A. m e. ( mVL ` t ) A. e e. ( mEx ` t )
          ( ( mEval ` t ) " { <. m , e >. } ) =
          ( ( ( mEval ` t ) " { <. m , ( ( mESyn ` t ) ` e ) >. } ) i^i
            ( ( mUV ` t ) " { ( 1st ` e ) } ) ) ) } $.

    $( Define the interpretation function for a model.  (Contributed by Mario
       Carneiro, 14-Jul-2016.) $)
    df-mitp $a |- mItp = ( t e. _V |-> ( a e. ( mSA ` t ) |->
      ( g e. X_ i e. ( ( mVars ` t ) ` a )
          ( ( mUV ` t ) " { ( ( mType ` t ) ` i ) } ) |->
        ( iota x E. m e. ( mVL ` t ) ( g = ( m |` ( ( mVars ` t ) ` a ) ) /\
          x = ( m ( mEval ` t ) a ) ) ) ) ) ) $.

    $( Define a function that produces the evaluation function, given the
       interpretation function for a model.  (Contributed by Mario Carneiro,
       14-Jul-2016.) $)
    df-mfitp $a |- mFromItp = ( t e. _V |-> ( f e. X_ a e. ( mSA ` t )
    ( ( ( mUV ` t ) " { ( ( 1st ` t ) ` a ) } ) ^m
        X_ i e. ( ( mVars ` t ) ` a )
          ( ( mUV ` t ) " { ( ( mType ` t ) ` i ) } ) ) |->
    ( iota_ n e. ( ( mUV ` t ) ^pm ( ( mVL ` t ) X. ( mEx ` t ) ) )
      A. m e. ( mVL ` t )
        ( A. v e. ( mVR ` t ) <. m , ( ( mVH ` t ) ` v ) >. n ( m ` v ) /\
          A. e A. a A. g ( e ( mST ` t ) <. a , g >. ->
            <. m , e >. n ( f ` ( i e. ( ( mVars ` t ) ` a ) |->
              ( m n ( g ` ( ( mVH ` t ) ` i ) ) ) ) ) ) /\
          A. e e. ( mEx ` t ) ( n " { <. m , e >. } ) =
            ( ( n " { <. m , ( ( mESyn ` t ) ` e ) >. } ) i^i
              ( ( mUV ` t ) " { ( 1st ` e ) } ) ) ) ) ) ) $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Splitting fields
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Introduce new constant symbols. $)
  $c cplMetSp $. $( Completion of a metric space $)
  $c HomLimB $. $( Direct limit auxiliaries $)
  $c HomLim $. $( Direct limit structure $)
  $c polyFld $. $( Polynomial extension field $)
  $c splitFld1 $. $( Splitting field for a polynomial auxiliary $)
  $c splitFld $. $( Splitting field for a polynomial $)
  $c polySplitLim $. $( Splitting field for a sequence of polynomials $)

  $( Completion of a metric space. $)
  ccpms $a class cplMetSp $.

  $( Embeddings for a direct limit. $)
  chlb $a class HomLimB $.

  $( Direct limit structure. $)
  chlim $a class HomLim $.

  $( Polynomial extension field. $)
  cpfl $a class polyFld $.

  $( Splitting field for a single polynomial (auxiliary). $)
  csf1 $a class splitFld1 $.

  $( Splitting field for a finite set of polynomials. $)
  csf $a class splitFld $.

  $( Splitting field for a sequence of polynomials. $)
  cpsl $a class polySplitLim $.

  ${
    $d e f g j n p q r s v w x y z $.
    $( A function which completes the given metric space.  (Contributed by
       Mario Carneiro, 2-Dec-2014.) $)
    df-cplmet $a |- cplMetSp = ( w e. _V |->
      [_ ( ( w ^s NN ) |`s ( Cau ` ( dist ` w ) ) ) / r ]_
      [_ ( Base ` r ) / v ]_ [_ { <. f , g >. | ( { f , g } C_ v /\
        A. x e. RR+ E. j e. ZZ ( f |` ( ZZ>= ` j ) ) :
          ( ZZ>= ` j ) --> ( ( g ` j ) ( ball ` ( dist ` w ) ) x ) ) } / e ]_
      ( ( r /s e ) sSet { <. ( dist ` ndx ) , { <. <. x , y >. , z >. |
        E. p e. v E. q e. v ( ( x = [ p ] e /\ y = [ q ] e ) /\
          ( p oF ( dist ` r ) q ) ~~> z ) } >. } ) ) $.

    $( The input to this function is a sequence (on ` NN ` ) of homomorphisms
       ` F ( n ) : R ( n ) --> R ( n + 1 ) ` .  The resulting structure is the
       direct limit of the direct system so defined.  This function returns the
       pair ` <. S , G >. ` where ` S ` is the terminal object and ` G ` is a
       sequence of functions such that ` G ( n ) : R ( n ) --> S ` and
       ` G ( n ) = F ( n ) o. G ( n + 1 ) ` .  (Contributed by Mario Carneiro,
       2-Dec-2014.) $)
    df-homlimb $a |- HomLimB = ( f e. _V |->
     [_ U_ n e. NN ( { n } X. dom ( f ` n ) ) / v ]_
     [_ |^| { s | ( s Er v /\ ( x e. v |-> <. ( ( 1st ` x ) + 1 ) ,
          ( ( f ` ( 1st ` x ) ) ` ( 2nd ` x ) ) >. ) C_ s ) } / e ]_
    <. ( v /. e ) , ( n e. NN |->
       ( x e. dom ( f ` n ) |-> [ <. n , x >. ] e ) ) >. ) $.

    $( The input to this function is a sequence (on ` NN ` ) of structures
       ` R ( n ) ` and homomorphisms ` F ( n ) : R ( n ) --> R ( n + 1 ) ` .
       The resulting structure is the direct limit of the direct system so
       defined, and maintains any structures that were present in the original
       objects.  TODO: generalize to directed sets?  (Contributed by Mario
       Carneiro, 2-Dec-2014.) $)
    df-homlim $a |- HomLim = ( r e. _V , f e. _V |->
     [_ ( HomLimB ` f ) / e ]_ [_ ( 1st ` e ) / v ]_ [_ ( 2nd ` e ) / g ]_
    ( { <. ( Base ` ndx ) , v >. ,
        <. ( +g ` ndx ) , U_ n e. NN ran ( x e. dom ( g ` n ) ,
        y e. dom ( g ` n ) |-> <. <. ( ( g ` n ) ` x ) , ( ( g ` n ) ` y ) >. ,
          ( ( g ` n ) ` ( x ( +g ` ( r ` n ) ) y ) ) >. ) >. ,
        <. ( .r ` ndx ) , U_ n e. NN ran ( x e. dom ( g ` n ) ,
        y e. dom ( g ` n ) |-> <. <. ( ( g ` n ) ` x ) , ( ( g ` n ) ` y ) >. ,
          ( ( g ` n ) ` ( x ( .r ` ( r ` n ) ) y ) ) >. ) >. } u.
      { <. ( TopOpen ` ndx ) , { s e. ~P v |
           A. n e. NN ( `' ( g ` n ) " s ) e. ( TopOpen ` ( r ` n ) ) } >. ,
        <. ( dist ` ndx ) , U_ n e. NN ran ( x e. dom ( ( g ` n ) ` n ) ,
        y e. dom ( ( g ` n ) ` n ) |-> <. <. ( ( g ` n ) ` x ) ,
             ( ( g ` n ) ` y ) >. , ( x ( dist ` ( r ` n ) ) y ) >. ) >. ,
        <. ( le ` ndx ) , U_ n e. NN ( `' ( g ` n ) o.
           ( ( le ` ( r ` n ) ) o. ( g ` n ) ) ) >. } ) ) $.
  $}

  ${
    $d c f g i n p q r s t z $.
    $( Define the field extension that augments a field with the root of the
       given irreducible polynomial, and extends the norm if one exists and the
       extension is unique.  (Contributed by Mario Carneiro, 2-Dec-2014.)
       (Revised by Thierry Arnoux and Steven Nguyen, 21-Jun-2025.) $)
    df-plfl $a |- polyFld = ( r e. _V , p e. _V |-> [_ ( Poly1 ` r ) / s ]_
      [_ ( ( RSpan ` s ) ` { p } ) / i ]_
      [_ ( c e. ( Base ` r ) |->
           [ ( c ( .s ` s ) ( 1r ` s ) ) ] ( s ~QG i ) ) / f ]_
      <. [_ ( s /s ( s ~QG i ) ) / t ]_ ( ( t toNrmGrp ( iota_ n e.
        ( AbsVal ` t ) ( n o. f ) = ( norm ` r ) ) ) sSet <. ( le ` ndx ) ,
          [_ ( z e. ( Base ` t ) |->
            ( iota_ q e. z ( q ( rem1p ` r ) p ) = q ) ) / g ]_
          ( `' g o. ( ( le ` s ) o. g ) ) >. ) , f >. ) $.
  $}

  ${
    $d ph x y $.  $d ps y $.  $d ch x $.  $d X x $.  $d B x $.  $d A x y $.
    rexxfr3d.s $e |- ( x = X -> ( ps <-> ch ) ) $.
    rexxfr3d.x $e |- ( ph -> ( x e. A <-> E. y e. B x = X ) ) $.
    rexxfr3d.a $e |- ( ph -> X e. V ) $.
    $( Transfer existential quantification from a variable ` x ` to another
       variable ` y ` contained in expression ` A ` .  (Contributed by SN,
       20-Jun-2025.) $)
    rexxfr3d $p |- ( ph -> ( E. x e. A ps <-> E. y e. B ch ) ) $=
      ( wcel cv adantr wceq wb adantl rexxfr2d ) ABCDEIFGHAIHMENGMLOKDNIPBCQAJR
      S $.
  $}

  ${
    $d ph x y $.  $d ps y $.  $d ch x $.  $d X x $.  $d B x $.
    rexxfr3dALT.s $e |- ( x = X -> ( ps <-> ch ) ) $.
    rexxfr3dALT.x $e |- ( ph -> ( x e. A <-> E. y e. B x = X ) ) $.
    rexxfr3dALT.a $e |- ( ph -> X e. V ) $.
    $( Longer proof of ~ rexxfr3d using ~ ax-11 instead of ~ ax-12 , without
       the disjoint variable condition ` A x y ` .  (Contributed by SN,
       19-Jun-2025.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    rexxfr3dALT $p |- ( ph -> ( E. x e. A ps <-> E. y e. B ch ) ) $=
      ( wrex cv wceq wex wa wcel rexbii bitr3i anbi1d pm5.32i exbidv df-rex syl
      r19.41v bitr4di 19.41v rexcom4 3bitr4g elisset biantrurd rexbidv bitr4d )
      ABDFMZDNZIOZDPZCQZEGMZCEGMAUPFRZBQZDPUQCQZEGMZDPZUOUTAVBVDDAVBUQEGMZBQZVD
      AVAVFBKUAVDUQBQZEGMVGVHVCEGUQBCJUBSUQBEGUFTUGUCBDFUDUTVCDPZEGMVEVIUSEGUQC
      DUHSVCEDGUITUJACUSEGAURCAIHRURLDIHUKUEULUMUN $.
  $}

  ${
    rspssbasd.k $e |- K = ( RSpan ` R ) $.
    rspssbasd.b $e |- B = ( Base ` R ) $.
    rspssbasd.r $e |- ( ph -> R e. Ring ) $.
    rspssbasd.g $e |- ( ph -> G C_ B ) $.
    $( The span of a set of ring elements is a set of ring elements.
       (Contributed by SN, 19-Jun-2025.) $)
    rspssbasd $p |- ( ph -> ( K ` G ) C_ B ) $=
      ( cfv clidl wcel wss crg eqid rspcl syl2anc lidlss syl ) ADEJZCKJZLZTBMAC
      NLDBMUBHIBCUADEFGUAOZPQBTUACGUCRS $.
  $}

  ${
    $d B i x y z $.  $d R i y $.  $d I i y z $.  $d M i y $.  $d X x z $.
    $d ph i x y z $.  $d .~ i x $.  $d .+ i y z $.  $d .x. i y $.
    ellcsrspsn.b $e |- B = ( Base ` R ) $.
    ellcsrspsn.p $e |- .+ = ( +g ` R ) $.
    ellcsrspsn.t $e |- .x. = ( .r ` R ) $.
    ellcsrspsn.e $e |- .~ = ( R ~QG I ) $.
    ellcsrspsn.u $e |- U = ( R /s .~ ) $.
    ellcsrspsn.i $e |- I = ( ( RSpan ` R ) ` { M } ) $.
    ellcsrspsn.r $e |- ( ph -> R e. Ring ) $.
    ellcsrspsn.m $e |- ( ph -> M e. B ) $.
    ellcsrspsn.x $e |- ( ph -> X e. ( Base ` U ) ) $.
    $( Membership in a left coset in a quotient of a ring by the span of a
       singleton (that is, by the ideal generated by an element).  This
       characterization comes from ~ eqglact and ~ elrspsn .  (Contributed by
       SN, 19-Jun-2025.) $)
    ellcsrspsn $p |- ( ph -> E. x e. B ( X = [ x ] .~ /\
      X = { z | E. y e. B z = ( x .+ ( y .x. M ) ) } ) ) $=
      ( vi cv cec wceq wrex co cab wa cbs cfv wcel crg wb quselbas syl2anc cmpt
      mpbid cima cgrp wss ringgrpd csn crsp eqid snssd rspssbasd eqsstrid simpr
      adantr eqglact syl3anc cvv vex elimampt oveq2 eqeq2d eleq2i elrspsn ovexd
      a1i bitrid rexxfr3d bitrd eqabdv eqtrd eqeq1 syl5ibrcom ancld reximdva
      mpd ) AMBUDZGUEZUFZBEUGZWOMDUDZWMCUDZLIUHZFUHZUFZCEUGZDUIZUFZUJZBEUGAMJUK
      ULZUMZWPUBAHUNUMZXGXGWPUOTUBBEGKJHUNXFMQRNUPUQUSAWOXEBEAWMEUMZUJZWOXDXJXD
      WOWNXCUFXJWNUCEWMUCUDZFUHZURZKUTZXCXJHVAUMZKEVBZXIWNXNUFAXOXIAHTVCVKAXPXI
      AKLVDZHVEULZULZESAEHXQXRXRVFZNTALEUAVGVHVIVKZAXIVJUCWMFGHEKNQOVLVMXJXBDXN
      XJWQXNUMWQXLUFZUCKUGXBXJUCEXLWQKXMVNXMVFWQVNUMXJDVOWBYAVPXJYBXAUCCKEVNWSX
      KWSUFZXLWTWQXKWSWMFVQVRAXKKUMZYCCEUGZUOXIYDXKXSUMZAYEKXSXKSVSAXHLEUMYFYEU
      OTUACEHIXKXRLNPXTVTUQWCVKXJWRLIWAWDWEWFWGMWNXCWHWIWJWKWL $.
  $}

  ${
    $d ph p q $.  $d B p q $.  $d D p q $.  $d F p q $.  $d G p q $.
    $d .+ p q $.  $d P p q $.  $d R p q $.  $d .xb p q $.
    ply1divalg3.p $e |- P = ( Poly1 ` R ) $.
    ply1divalg3.d $e |- D = ( deg1 ` R ) $.
    ply1divalg3.b $e |- B = ( Base ` P ) $.
    ply1divalg3.m $e |- .+ = ( +g ` P ) $.
    ply1divalg3.t $e |- .xb = ( .r ` P ) $.
    ply1divalg3.c $e |- C = ( Unic1p ` R ) $.
    ply1divalg3.r $e |- ( ph -> R e. Ring ) $.
    ply1divalg3.f $e |- ( ph -> F e. B ) $.
    ply1divalg3.g $e |- ( ph -> G e. C ) $.
    $( Uniqueness of polynomial remainder: convert the subtraction in
       ~ ply1divalg2 to addition.  (Contributed by SN, 20-Jun-2025.) $)
    ply1divalg3 $p |-
      ( ph -> E! q e. B ( D ` ( F .+ ( q .xb G ) ) ) < ( D ` G ) ) $=
      ( vp cminusg cfv csg clt wbr wreu cui c0g eqid wcel uc1pcl syl wne uc1pn0
      cv co cco1 uc1pldg ply1divalg2 wa cgrp crg ply1ring ringgrpd adantr simpr
      grpinvcld wceq wf1o f1ofveu sylan eqcom reubii sylibr oveq1 oveq2d fveq2d
      grpinvf1o breq1d reuxfr1ds ringcld grpsubval syl2an2r ringmneg1 grpinvinv
      mpbid eqtrd reubidva ) AIKUPZEUBUCZUCZJHUQZEUDUCZUQZDUCZJDUCZUEUFZKBUGZIW
      JJHUQZFUQZDUCZWQUEUFZKBUGAIUAUPZJHUQZWNUQZDUCZWQUEUFZUABUGWSABDEGHGUHUCZI
      JWNEUIUCZUALMNWNUJZXJUJZPRSAJCUKZJBUKZTBCEGJLNQULUMZAXMJXJUNTCEGJXJLXLQUO
      UMAXMWQJURUCUCXIUKTCDGXIJMXIUJZQUSUMXPUTAXHWRUAKWLBBAWJBUKZVAZBEWKWJNWKUJ
      ZAEVBUKZXQAEAGVCUKEVCUKZREGLVDUMZVEZVFAXQVGZVHZAXDBUKZVAWLXDVIZKBUGZXDWLV
      IZKBUGABBWKVJYFYHABEWKNXSYCVSKBBXDWKVKVLYIYGKBXDWLVMVNVOYIXGWPWQUEYIXFWOD
      YIXEWMIWNXDWLJHVPVQVRVTWAWGAWRXCKBXRWPXBWQUEXRWOXADXRWOIWMWKUCZFUQZXAAIBU
      KXQWMBUKWOYKVISXRBEHWLJNPAYAXQYBVFZYEAXNXQXOVFZWBBFEWKWNIWMNOXSXKWCWDXRYJ
      WTIFXRYJWTWKUCZWKUCZWTXRWMYNWKXRBEHWKWJJNPXSYLYDYMWEVRAXTXQWTBUKYOWTVIYCX
      RBEHWJJNPYLYDYMWBBEWKWTNXSWFWDWHVQWHVRVTWIWG $.
  $}

  ${
    $d ph p q s t y z $.  $d P p q s t y z $.  $d I p q s y z $.  $d D p q s $.
    $d F p q s t y z $.  $d R q s $.  $d Z p q s z $.
    r1peuqus.p $e |- P = ( Poly1 ` R ) $.
    r1peuqus.i $e |- I = ( ( RSpan ` P ) ` { F } ) $.
    r1peuqus.t $e |- T = ( P /s ( P ~QG I ) ) $.
    r1peuqus.q $e |- Q = ( Base ` T ) $.
    r1peuqus.n $e |- N = ( Unic1p ` R ) $.
    r1peuqus.d $e |- D = ( deg1 ` R ) $.
    r1peuqus.r $e |- ( ph -> R e. Domn ) $.
    r1peuqus.f $e |- ( ph -> F e. N ) $.
    r1peuqus.z $e |- ( ph -> Z e. Q ) $.
    $( Uniqueness of polynomial remainder in terms of a quotient structure in
       the sense of the right hand side of ~ r1pid2 .  (Contributed by SN,
       21-Jun-2025.) $)
    r1peuqusdeg1 $p |- ( ph -> E! q e. Z ( D ` q ) < ( D ` F ) ) $=
      ( vp vz vy vs vt cv cfv clt wbr wreu cbs wrex cqg co cec cmulr cplusg cab
      wceq eqid cdomn wcel crg ply1domn syl domnring uc1pcl eleqtrdi ellcsrspsn
      adantr simpr ply1divalg3 cvv ovexd eqidd weq oveq2d eqeq2d rspcev syl2anc
      wa oveq1 eqeq1 rexbidv elabd simplrr eleqtrrd wrmo simprr sselda cbvrexvw
      eqimssd bitrdi elabg ibi wi wral eqtr2 w3a cgrp wb ringgrpd simpr2 simpr3
      ringcld simpr1 grplcan syl13anc c0g simplr2 simplr3 csn cdif wne eldifsnd
      uc1pn0 ad2antrr domnrcan ex sylbid 3exp2 syl5 ralrimivva rmo4 sylibr reu5
      imp43 sylanbrc fveq2 breq1d reuxfr1ds mpbird reximdva mpd id rexlimivw )
      AKUFZBUGZGBUGZUHUIZKJUJZUACUKUGZULZUUAAJUAUFZCHUMUNZUOUSZJUBUFZUUDUCUFZGC
      UPUGZUNZCUQUGZUNZUSZUCUUBULZUBURZUSZWAZUAUUBULUUCAUAUCUBUUBUUKUUECUUIFHGJ
      UUBUTZUUKUTZUUIUTZUUEUTNMACVAVBZCVCVBZAEVAVBZUVARCELVDVEZCVFVEZAGIVBZGUUB
      VBZSUUBICEGLUURPVGVEZAJDFUKUGTOVHVIAUUQUUAUAUUBAUUDUUBVBZWAZUUQUUAUVJUUQW
      AZUUAUUDUDUFZGUUIUNZUUKUNZBUGZYSUHUIZUDUUBUJZUVJUVQUUQUVJUUBIBCUUKEUUIUUD
      GUDLQUURUUSUUTPAEVCVBZUVIAUVCUVRREVFVEVJAUVIVKAUVFUVISVJVLVJUVKYTUVPKUDUV
      NJUUBUVKUVLUUBVBZWAZUVNUUOJUVTUUNUVNUULUSZUCUUBULZUBUVNVMUVTUUDUVMUUKVNUV
      TUVSUVNUVNUSZUWBUVKUVSVKUVTUVNVOUWAUWCUCUVLUUBUCUDVPZUULUVNUVNUWDUUJUVMUU
      DUUKUUHUVLGUUIWBVQZVRVSVTUUGUVNUSUUMUWAUCUUBUUGUVNUULWCWDWEUVJUUFUUPUVSWF
      WGUVKYQJVBZWAZYQUVNUSZUDUUBULZUWHUDUUBWHZUWHUDUUBUJUWGYQUUOVBZUWIUVKJUUOY
      QUVKJUUOUVJUUFUUPWIWLWJUWKUWIUUNUWIUBYQUUOUBKVPZUUNYQUULUSZUCUUBULUWIUWLU
      UMUWMUCUUBUUGYQUULWCWDUWMUWHUCUDUUBUWDUULUVNYQUWEVRWKWMWNWOVEUVJUWJUUQUWF
      UVJUWHYQUUDUEUFZGUUIUNZUUKUNZUSZWAZUDUEVPZWPZUEUUBWQUDUUBWQUWJUVJUWTUDUEU
      UBUUBUWRUVNUWPUSZUVJUVSUWNUUBVBZWAWAUWSYQUVNUWPWRAUVIUVSUXBUXAUWSWPZAUVIU
      VSUXBUXCAUVIUVSUXBWSZWAZUXAUVMUWOUSZUWSUXECWTVBZUVMUUBVBUWOUUBVBUVIUXAUXF
      XAAUXGUXDACUVEXBVJUXEUUBCUUIUVLGUURUUTAUVBUXDUVEVJZAUVIUVSUXBXCAUVGUXDUVH
      VJZXEUXEUUBCUUIUWNGUURUUTUXHAUVIUVSUXBXDUXIXEAUVIUVSUXBXFUUBUUKCUVMUWOUUD
      UURUUSXGXHUXEUXFUWSUXEUXFWAUUBCUUIUVLUWNCXIUGZGUURUXJUTZUUTUVIUVSUXBAUXFX
      JUVIUVSUXBAUXFXKAGUUBUXJXLXMVBUXDUXFAGUUBUXJUVHAUVFGUXJXNSICEGUXJLUXKPXPV
      EXOXQAUVAUXDUXFUVDXQUXEUXFVKXRXSXTYAYGYBYCUWHUWQUDUEUUBUWSUVNUWPYQUWSUVMU
      WOUUDUUKUVLUWNGUUIWBVQVRYDYEXQUWHUDUUBYFYHUWHYRUVOYSUHYQUVNBYIYJYKYLXSYMY
      NUUAUUAUAUUBUUAYOYPVE $.
  $}

  ${
    $d f b g h j m p r s t $.
    $( Temporary construction for the splitting field of a polynomial.  The
       inputs are a field ` r ` and a polynomial ` p ` that we want to split,
       along with a tuple ` j ` in the same format as the output.  The output
       is a tuple ` <. S , F >. ` where ` S ` is the splitting field and ` F `
       is an injective homomorphism from the original field ` r ` .

       The function works by repeatedly finding the smallest monic irreducible
       factor, and extending the field by that factor using the ` polyFld `
       construction.  We keep track of a total order in each of the splitting
       fields so that we can pick an element definably without needing global
       choice.  (Contributed by Mario Carneiro, 2-Dec-2014.) $)
    df-sfl1 $a |- splitFld1 = ( r e. _V , j e. _V |-> ( p e. ( Poly1 ` r ) |->
        ( rec ( ( s e. _V , f e. _V |-> [_ ( Poly1 ` s ) / m ]_
        [_ { g e. ( ( Monic1p ` s ) i^i ( Irred ` m ) ) |
             ( g ( ||r ` m ) ( p o. f ) /\ 1 < ( s deg1 g ) ) } / b ]_
        if ( ( ( p o. f ) = ( 0g ` m ) \/ b = (/) ) , <. s , f >. ,
          [_ ( glb ` b ) / h ]_ [_ ( s polyFld h ) / t ]_
          <. ( 1st ` t ) , ( f o. ( 2nd ` t ) ) >. ) ) , j ) `
        ( card ` ( 1 ... ( r deg1 p ) ) ) ) ) ) $.
  $}

  ${
    $d e f g p r x $.
    $( Define the splitting field of a finite collection of polynomials, given
       a total ordered base field.  The output is a tuple ` <. S , F >. ` where
       ` S ` is the totally ordered splitting field and ` F ` is an injective
       homomorphism from the original field ` r ` .  (Contributed by Mario
       Carneiro, 2-Dec-2014.) $)
    df-sfl $a |- splitFld = ( r e. _V , p e. _V |->
        ( iota x E. f ( f Isom < , ( lt ` r ) ( ( 1 ... ( # ` p ) ) , p ) /\
          x = ( seq 0 ( ( e e. _V , g e. _V |->
            ( ( r splitFld1 e ) ` g ) ) , ( f u.
        { <. 0 , <. r , ( _I |` ( Base ` r ) ) >. >. } ) ) `
          ( # ` p ) ) ) ) ) $.
  $}

  ${
    $d e f g p q r s x $.
    $( Define the direct limit of an increasing sequence of fields produced by
       pasting together the splitting fields for each sequence of polynomials.
       That is, given a ring ` r ` , a strict order on ` r ` , and a sequence
       ` p : NN --> ( ~P r i^i Fin ) ` of finite sets of polynomials to split,
       we construct the direct limit system of field extensions by splitting
       one set at a time and passing the resulting construction to ` HomLim ` .
       (Contributed by Mario Carneiro, 2-Dec-2014.) $)
    df-psl $a |- polySplitLim = ( r e. _V ,
      p e. ( ( ~P ( Base ` r ) i^i Fin ) ^m NN ) |->
    [_ ( 1st o. seq 0 ( ( g e. _V , q e. _V |->
      [_ ( 1st ` g ) / e ]_ [_ ( 1st ` e ) / s ]_
      [_ ( s splitFld ran ( x e. q |-> ( x o. ( 2nd ` g ) ) ) ) / f ]_
        <. f , ( ( 2nd ` g ) o. ( 2nd ` f ) ) >. ) ,
        ( p u. { <. 0 , <. <. r , (/) >. ,
          ( _I |` ( Base ` r ) ) >. >. } ) ) ) / f ]_
      ( ( 1st o. ( f shift 1 ) ) HomLim ( 2nd o. f ) ) ) $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  <i>p</i>-adic number fields
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Introduce new constant symbols. $)
  $c ZRing $. $( Integral elements of a ring $)
  $c GF $. $( Galois finite field $)
  $c GF_oo $. $( Galois limit field $)
  $c ~Qp $. $( Equivalence relation for Qp $)
  $c /Qp $. $( Representative of equivalence relation $)
  $c Qp $. $( p-adic rational numbers $)
  $c Zp $. $( p-adic integers $)
  $c _Qp $. $( Algebraic completion of Qp $)
  $c Cp $. $( Metric completion of _Qp $)

  $( Integral elements of a ring. $)
  czr $a class ZRing $.

  $( Galois finite field. $)
  cgf $a class GF $.

  $( Galois limit field. $)
  cgfo $a class GF_oo $.

  $( Equivalence relation for ~ df-qp . $)
  ceqp $a class ~Qp $.

  $( Equivalence relation representatives for ~ df-qp . $)
  crqp $a class /Qp $.

  $( The set of ` p ` -adic rational numbers. $)
  cqp $a class Qp $.

  $( The set of ` p ` -adic integers.  (Not to be confused with ~ czn .) $)
  czp $a class Zp $.

  $( Algebraic completion of the ` p ` -adic rational numbers. $)
  cqpa $a class _Qp $.

  $( Metric completion of ` _Qp ` . $)
  ccp $a class Cp $.

  ${
    $d b d f g h k n p r s x y $.
    $( Define the subring of integral elements in a ring.  (Contributed by
       Mario Carneiro, 2-Dec-2014.) $)
    df-zrng $a |- ZRing = ( r e. _V |->
      ( r IntgRing ran ( ZRHom ` r ) ) ) $.

    $( Define the Galois finite field of order ` p ^ n ` .  (Contributed by
       Mario Carneiro, 2-Dec-2014.) $)
    df-gf $a |- GF = ( p e. Prime , n e. NN |-> [_ ( Z/nZ ` p ) / r ]_
    ( 1st ` ( r splitFld { [_ ( Poly1 ` r ) / s ]_ [_ ( var1 ` r ) / x ]_
        ( ( ( p ^ n ) ( .g ` ( mulGrp ` s ) ) x ) ( -g ` s ) x ) } ) ) ) $.

    $( Define the Galois field of order ` p ^ +oo ` , as a direct limit of the
       Galois finite fields.  (Contributed by Mario Carneiro, 2-Dec-2014.) $)
    df-gfoo $a |- GF_oo = ( p e. Prime |-> [_ ( Z/nZ ` p ) / r ]_
      ( r polySplitLim ( n e. NN |->
      { [_ ( Poly1 ` r ) / s ]_ [_ ( var1 ` r ) / x ]_
        ( ( ( p ^ n ) ( .g ` ( mulGrp ` s ) ) x ) ( -g ` s ) x ) } ) ) ) $.

    $( Define an equivalence relation on ` ZZ ` -indexed sequences of integers
       such that two sequences are equivalent iff the difference is equivalent
       to zero, and a sequence is equivalent to zero iff the sum
       ` sum_ k <_ n f ( k ) ( p ^ k ) ` is a multiple of ` p ^ ( n + 1 ) ` for
       every ` n ` .  (Contributed by Mario Carneiro, 2-Dec-2014.) $)
    df-eqp $a |- ~Qp = ( p e. Prime |->
      { <. f , g >. | ( { f , g } C_ ( ZZ ^m ZZ ) /\
       A. n e. ZZ sum_ k e. ( ZZ>= ` -u n ) ( ( ( f ` -u k ) - ( g ` -u k ) ) /
        ( p ^ ( k + ( n + 1 ) ) ) ) e. ZZ ) } ) $.

    $( There is a unique element of ` ( ZZ ^m ( 0 ... ( p - 1 ) ) ) ` ` ~Qp `
       -equivalent to any element of ` ( ZZ ^m ZZ ) ` , if the sequences are
       zero for sufficiently large negative values; this function selects that
       element.  (Contributed by Mario Carneiro, 2-Dec-2014.) $)
    df-rqp $a |- /Qp = ( p e. Prime |-> ( ~Qp i^i [_ { f e. ( ZZ ^m ZZ ) |
      E. x e. ran ZZ>= ( `' f " ( ZZ \ { 0 } ) ) C_ x } / y ]_
        ( y X. ( y i^i ( ZZ ^m ( 0 ... ( p - 1 ) ) ) ) ) ) ) $.

    $( Define the ` p ` -adic completion of the rational numbers, as a normed
       field structure with a total order (that is not compatible with the
       operations).  (Contributed by Mario Carneiro, 2-Dec-2014.)  (Revised by
       AV, 10-Oct-2021.) $)
    df-qp $a |- Qp = ( p e. Prime |->
        [_ { h e. ( ZZ ^m ( 0 ... ( p - 1 ) ) ) |
          E. x e. ran ZZ>= ( `' h " ( ZZ \ { 0 } ) ) C_ x } / b ]_
  ( ( { <. ( Base ` ndx ) , b >. ,
        <. ( +g ` ndx ) ,
          ( f e. b , g e. b |-> ( ( /Qp ` p ) ` ( f oF + g ) ) ) >. ,
        <. ( .r ` ndx ) ,
          ( f e. b , g e. b |-> ( ( /Qp ` p ) ` ( n e. ZZ |->
           sum_ k e. ZZ ( ( f ` k ) x. ( g ` ( n - k ) ) ) ) ) ) >. } u.
      { <. ( le ` ndx ) , { <. f , g >. | ( { f , g } C_ b /\
        sum_ k e. ZZ ( ( f ` -u k ) x. ( ( p + 1 ) ^ -u k ) ) <
        sum_ k e. ZZ ( ( g ` -u k ) x. ( ( p + 1 ) ^ -u k ) ) ) } >. } )
        toNrmGrp ( f e. b |-> if ( f = ( ZZ X. { 0 } ) , 0 ,
        ( p ^ -u inf ( ( `' f " ( ZZ \ { 0 } ) ) , RR , < ) ) ) ) ) ) $.

    $( Define the ` p ` -adic integers, as a subset of the ` p ` -adic
       rationals.  (Contributed by Mario Carneiro, 2-Dec-2014.) $)
    df-zp $a |- Zp = ( ZRing o. Qp ) $.

    $( Define the completion of the ` p ` -adic rationals.  Here we simply
       define it as the splitting field of a dense sequence of polynomials
       (using as the ` n ` -th set the collection of polynomials with degree
       less than ` n ` and with coefficients ` < ( p ^ n ) ` ).  Krasner's
       lemma will then show that all monic polynomials have splitting fields
       isomorphic to a sufficiently close Eisenstein polynomial from the list,
       and unramified extensions are generated by the polynomial
       ` x ^ ( p ^ n ) - x ` , which is in the list.  Thus, every finite
       extension of ` Qp ` is a subfield of this field extension, so it is
       algebraically closed.  (Contributed by Mario Carneiro, 2-Dec-2014.) $)
    df-qpa $a |- _Qp = ( p e. Prime |-> [_ ( Qp ` p ) / r ]_
      ( r polySplitLim ( n e. NN |-> { f e. ( Poly1 ` r ) |
        ( ( r deg1 f ) <_ n /\ A. d e. ran ( coe1 ` f )
          ( `' d " ( ZZ \ { 0 } ) ) C_ ( 0 ... n ) ) } ) ) ) $.

    $( Define the metric completion of the algebraic completion of the ` p `
       -adic rationals.  (Contributed by Mario Carneiro, 2-Dec-2014.) $)
    df-cp $a |- Cp = ( cplMetSp o. _Qp ) $.
  $}

  $( TODO list $)

  $( change *mpt2* -> *mpo* $)
  $( use more symbol variables like .+ $)
  $( Uniform spaces $)
  $( Characterization of perfectly normal spaces $)
  $( Hausdorff quotient $)
  $( add mpt2mptf, fmpt2i $)

$( (End of Mario Carneiro's mathbox.) $)
