$( big-unifier.mm - Version of 30-Aug-2008

                           ~~ PUBLIC DOMAIN ~~
This work is waived of all rights, including copyright, according to the CC0
Public Domain Dedication.  http://creativecommons.org/publicdomain/zero/1.0/

Norman Megill - http://metamath.org $)

$(

This file (big-unifier.mm) is a unification and substitution test for
Metamath verifiers, where small input expressions blow up to thousands
of symbols.  It is a translation of William McCune's "big-unifier.in"
for the OTTER theorem prover:

    http://www-unix.mcs.anl.gov/AR/award-2003/big-unifier.in
    http://www-unix.mcs.anl.gov/AR/award-2003/big-unifier.out

    Description:  "Examples of complicated substitutions in condensed
        detachment.  These occur in Larry Wos's proofs that XCB is a single
        axiom for EC."
$)


 $c wff |- e ( , ) $.
 $v x y z w v u v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 $.

  wx $f wff x $. wy $f wff y $. wz $f wff z $. ww $f wff w $.
  wv $f wff v $. wu $f wff u $. wv1 $f wff v1 $. wv2 $f wff v2 $.
  wv3 $f wff v3 $. wv4 $f wff v4 $. wv5 $f wff v5 $. wv6 $f wff v6 $.
  wv7 $f wff v7 $. wv8 $f wff v8 $. wv9 $f wff v9 $. wv10 $f wff v10 $.
  wv11 $f wff v11 $.

 $( The binary connective of the language "EC". $)
 wi $a wff e ( x , y ) $.

 ${
   ax-mp.1 $e |- x $.
   ax-mp.2 $e |- e ( x , y ) $.
   $( The inference rule. $)
   ax-mp $a |- y $.
 $}

 $( The first axiom. $)
 ax-maj $a |- e ( e ( e ( e ( e ( x , e ( y , e ( e ( e ( e ( e ( z , e (
   e ( e ( z , u ) , e ( v , u ) ) , v ) ) , e ( e ( w , e ( e ( e ( w , v6
   ) , e ( v7 , v6 ) ) , v7 ) ) , y ) ) , v8 ) , e ( v9 , v8 ) ) , v9 ) ) )
   , x ) , v10 ) , e ( v11 , v10 ) ) , v11 ) $.

 $( The second axiom. $)
 ax-min $a |- e ( e ( e ( e ( e ( e ( x , e ( e ( y , e ( e ( e ( y , z )
   , e ( u , z ) ) , u ) ) , x ) ) , e ( v , e ( e ( e ( v , w ) , e ( v6 ,
   w ) ) , v6 ) ) ) , v7 ) , v8 ) , e ( v7 , v8 ) ) , e ( v9 , e ( e ( e (
   v9 , v10 ) , e ( v11 , v10 ) ) , v11 ) ) ) $.

 $( A 3-step proof that applies ~ ax-mp to the two axioms.  The proof was
    saved in compressed format with "save proof theorem1 /compressed" in
    the metamath program. $)
 theorem1 $p |- e ( e ( e ( x , e ( y , e ( e ( e ( y , z ) , e ( u , z ) )
   , u ) ) ) , v ) , e ( x , v ) ) $=
   ( wi ax-min ax-maj ax-mp ) ABBCFECFFEFFZFZKDFADFFZAFZFJMFFZKNJFFNFZFAO
   FFZMPAFFZFPFQPFZFLRFFLNKMJAJNQPLAPGPMKBADCEOARLHI $.

 $( This is the same as ~ theorem1 , except that the proof is saved in
    uncompressed format with "save proof theorem1u /normal" in the metamath
    program.  Note the size difference in the compressed vs. uncompressed
    proofs. $)
 theorem1u $p |- e ( e ( e ( x , e ( y , e ( e ( e ( y , z ) , e ( u , z ) )
   , u ) ) ) , v ) , e ( x , v ) ) $=
   wx wy wy wz wi wu wz wi wi wu wi wi wi wx wy wy wz wi wu wz wi wi wu wi wi
   wi wv wi wx wv wi wi wx wi wi wy wy wz wi wu wz wi wi wu wi wi wx wy wy wz
   wi wu wz wi wi wu wi wi wi wv wi wx wv wi wi wx wi wi wi wx wy wy wz wi wu
   wz wi wi wu wi wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wx wy wy wz wi
   wu wz wi wi wu wi wi wi wv wi wx wv wi wi wx wi wi wy wy wz wi wu wz wi wi
   wu wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wv wi wx wv wi wi wx wi wi
   wi wy wy wz wi wu wz wi wi wu wi wi wi wi wx wy wy wz wi wu wz wi wi wu wi
   wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wv wi wx wv wi wi wx wi wi wy
   wy wz wi wu wz wi wi wu wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wv wi
   wx wv wi wi wx wi wi wi wi wi wx wx wy wy wz wi wu wz wi wi wu wi wi wi wx
   wy wy wz wi wu wz wi wi wu wi wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi
   wv wi wx wv wi wi wx wi wi wy wy wz wi wu wz wi wi wu wi wi wx wy wy wz wi
   wu wz wi wi wu wi wi wi wv wi wx wv wi wi wx wi wi wi wy wy wz wi wu wz wi
   wi wu wi wi wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wx wy wy wz wi wu
   wz wi wi wu wi wi wi wv wi wx wv wi wi wx wi wi wy wy wz wi wu wz wi wi wu
   wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wv wi wx wv wi wi wx wi wi wi
   wi wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wv wi wx wv wi wi wx wi wx
   wy wy wz wi wu wz wi wi wu wi wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi
   wv wi wx wv wi wi wx wi wi wy wy wz wi wu wz wi wi wu wi wi wx wy wy wz wi
   wu wz wi wi wu wi wi wi wv wi wx wv wi wi wx wi wi wi wx wy wy wz wi wu wz
   wi wi wu wi wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wx wy wy wz wi wu
   wz wi wi wu wi wi wi wv wi wx wv wi wi wx wi wi wy wy wz wi wu wz wi wi wu
   wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wv wi wx wv wi wi wx wi wi wi
   wy wy wz wi wu wz wi wi wu wi wi wi wi wx wy wy wz wi wu wz wi wi wu wi wi
   wi wx wy wy wz wi wu wz wi wi wu wi wi wi wv wi wx wv wi wi wx wi wi wy wy
   wz wi wu wz wi wi wu wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wv wi wx
   wv wi wi wx wi wi wi wi wi wx wx wy wy wz wi wu wz wi wi wu wi wi wi wx wy
   wy wz wi wu wz wi wi wu wi wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wv
   wi wx wv wi wi wx wi wi wy wy wz wi wu wz wi wi wu wi wi wx wy wy wz wi wu
   wz wi wi wu wi wi wi wv wi wx wv wi wi wx wi wi wi wy wy wz wi wu wz wi wi
   wu wi wi wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wx wy wy wz wi wu wz
   wi wi wu wi wi wi wv wi wx wv wi wi wx wi wi wy wy wz wi wu wz wi wi wu wi
   wi wx wy wy wz wi wu wz wi wi wu wi wi wi wv wi wx wv wi wi wx wi wi wi wi
   wi wi wx wi wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wx wy wy wz wi wu
   wz wi wi wu wi wi wi wv wi wx wv wi wi wx wi wi wy wy wz wi wu wz wi wi wu
   wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wv wi wx wv wi wi wx wi wi wi
   wx wy wy wz wi wu wz wi wi wu wi wi wi wx wy wy wz wi wu wz wi wi wu wi wi
   wi wx wy wy wz wi wu wz wi wi wu wi wi wi wv wi wx wv wi wi wx wi wi wy wy
   wz wi wu wz wi wi wu wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wv wi wx
   wv wi wi wx wi wi wi wy wy wz wi wu wz wi wi wu wi wi wi wi wx wy wy wz wi
   wu wz wi wi wu wi wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wv wi wx wv
   wi wi wx wi wi wy wy wz wi wu wz wi wi wu wi wi wx wy wy wz wi wu wz wi wi
   wu wi wi wi wv wi wx wv wi wi wx wi wi wi wi wi wx wx wy wy wz wi wu wz wi
   wi wu wi wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wx wy wy wz wi wu wz
   wi wi wu wi wi wi wv wi wx wv wi wi wx wi wi wy wy wz wi wu wz wi wi wu wi
   wi wx wy wy wz wi wu wz wi wi wu wi wi wi wv wi wx wv wi wi wx wi wi wi wy
   wy wz wi wu wz wi wi wu wi wi wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi
   wx wy wy wz wi wu wz wi wi wu wi wi wi wv wi wx wv wi wi wx wi wi wy wy wz
   wi wu wz wi wi wu wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wv wi wx wv
   wi wi wx wi wi wi wi wi wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wv wi
   wx wv wi wi wx wi wx wy wy wz wi wu wz wi wi wu wi wi wi wx wy wy wz wi wu
   wz wi wi wu wi wi wi wv wi wx wv wi wi wx wi wi wy wy wz wi wu wz wi wi wu
   wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wv wi wx wv wi wi wx wi wi wi
   wx wy wy wz wi wu wz wi wi wu wi wi wi wx wy wy wz wi wu wz wi wi wu wi wi
   wi wx wy wy wz wi wu wz wi wi wu wi wi wi wv wi wx wv wi wi wx wi wi wy wy
   wz wi wu wz wi wi wu wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wv wi wx
   wv wi wi wx wi wi wi wy wy wz wi wu wz wi wi wu wi wi wi wi wx wy wy wz wi
   wu wz wi wi wu wi wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wv wi wx wv
   wi wi wx wi wi wy wy wz wi wu wz wi wi wu wi wi wx wy wy wz wi wu wz wi wi
   wu wi wi wi wv wi wx wv wi wi wx wi wi wi wi wi wx wx wy wy wz wi wu wz wi
   wi wu wi wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wx wy wy wz wi wu wz
   wi wi wu wi wi wi wv wi wx wv wi wi wx wi wi wy wy wz wi wu wz wi wi wu wi
   wi wx wy wy wz wi wu wz wi wi wu wi wi wi wv wi wx wv wi wi wx wi wi wi wy
   wy wz wi wu wz wi wi wu wi wi wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi
   wx wy wy wz wi wu wz wi wi wu wi wi wi wv wi wx wv wi wi wx wi wi wy wy wz
   wi wu wz wi wi wu wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wv wi wx wv
   wi wi wx wi wi wi wi wi wi wx wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi
   wx wy wy wz wi wu wz wi wi wu wi wi wi wv wi wx wv wi wi wx wi wi wy wy wz
   wi wu wz wi wi wu wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wv wi wx wv
   wi wi wx wi wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wx wy wy wz wi wu
   wz wi wi wu wi wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wv wi wx wv wi
   wi wx wi wi wy wy wz wi wu wz wi wi wu wi wi wx wy wy wz wi wu wz wi wi wu
   wi wi wi wv wi wx wv wi wi wx wi wi wi wy wy wz wi wu wz wi wi wu wi wi wi
   wi wx wy wy wz wi wu wz wi wi wu wi wi wi wx wy wy wz wi wu wz wi wi wu wi
   wi wi wv wi wx wv wi wi wx wi wi wy wy wz wi wu wz wi wi wu wi wi wx wy wy
   wz wi wu wz wi wi wu wi wi wi wv wi wx wv wi wi wx wi wi wi wi wi wx wx wy
   wy wz wi wu wz wi wi wu wi wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wx
   wy wy wz wi wu wz wi wi wu wi wi wi wv wi wx wv wi wi wx wi wi wy wy wz wi
   wu wz wi wi wu wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wv wi wx wv wi
   wi wx wi wi wi wy wy wz wi wu wz wi wi wu wi wi wi wi wx wy wy wz wi wu wz
   wi wi wu wi wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wv wi wx wv wi wi
   wx wi wi wy wy wz wi wu wz wi wi wu wi wi wx wy wy wz wi wu wz wi wi wu wi
   wi wi wv wi wx wv wi wi wx wi wi wi wi wi wi wi wi wx wy wy wz wi wu wz wi
   wi wu wi wi wi wv wi wx wv wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wv
   wi wx wv wi wi wx wi wx wy wy wz wi wu wz wi wi wu wi wi wi wx wy wy wz wi
   wu wz wi wi wu wi wi wi wv wi wx wv wi wi wx wi wi wy wy wz wi wu wz wi wi
   wu wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wv wi wx wv wi wi wx wi wi
   wi wx wy wy wz wi wu wz wi wi wu wi wi wi wx wy wy wz wi wu wz wi wi wu wi
   wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wv wi wx wv wi wi wx wi wi wy
   wy wz wi wu wz wi wi wu wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wv wi
   wx wv wi wi wx wi wi wi wy wy wz wi wu wz wi wi wu wi wi wi wi wx wy wy wz
   wi wu wz wi wi wu wi wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wv wi wx
   wv wi wi wx wi wi wy wy wz wi wu wz wi wi wu wi wi wx wy wy wz wi wu wz wi
   wi wu wi wi wi wv wi wx wv wi wi wx wi wi wi wi wi wx wx wy wy wz wi wu wz
   wi wi wu wi wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wx wy wy wz wi wu
   wz wi wi wu wi wi wi wv wi wx wv wi wi wx wi wi wy wy wz wi wu wz wi wi wu
   wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wv wi wx wv wi wi wx wi wi wi
   wy wy wz wi wu wz wi wi wu wi wi wi wi wx wy wy wz wi wu wz wi wi wu wi wi
   wi wx wy wy wz wi wu wz wi wi wu wi wi wi wv wi wx wv wi wi wx wi wi wy wy
   wz wi wu wz wi wi wu wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wv wi wx
   wv wi wi wx wi wi wi wi wi wi wx wi wi wx wy wy wz wi wu wz wi wi wu wi wi
   wi wx wy wy wz wi wu wz wi wi wu wi wi wi wv wi wx wv wi wi wx wi wi wy wy
   wz wi wu wz wi wi wu wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wv wi wx
   wv wi wi wx wi wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wx wy wy wz wi
   wu wz wi wi wu wi wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wv wi wx wv
   wi wi wx wi wi wy wy wz wi wu wz wi wi wu wi wi wx wy wy wz wi wu wz wi wi
   wu wi wi wi wv wi wx wv wi wi wx wi wi wi wy wy wz wi wu wz wi wi wu wi wi
   wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wx wy wy wz wi wu wz wi wi wu
   wi wi wi wv wi wx wv wi wi wx wi wi wy wy wz wi wu wz wi wi wu wi wi wx wy
   wy wz wi wu wz wi wi wu wi wi wi wv wi wx wv wi wi wx wi wi wi wi wi wx wx
   wy wy wz wi wu wz wi wi wu wi wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi
   wx wy wy wz wi wu wz wi wi wu wi wi wi wv wi wx wv wi wi wx wi wi wy wy wz
   wi wu wz wi wi wu wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wv wi wx wv
   wi wi wx wi wi wi wy wy wz wi wu wz wi wi wu wi wi wi wi wx wy wy wz wi wu
   wz wi wi wu wi wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wv wi wx wv wi
   wi wx wi wi wy wy wz wi wu wz wi wi wu wi wi wx wy wy wz wi wu wz wi wi wu
   wi wi wi wv wi wx wv wi wi wx wi wi wi wi wi wi wi wi wi wx wy wy wz wi wu
   wz wi wi wu wi wi wi wv wi wx wv wi wi wx wy wy wz wi wu wz wi wi wu wi wi
   wi wx wy wy wz wi wu wz wi wi wu wi wi wi wv wi wx wv wi wi wx wi wi wy wy
   wz wi wu wz wi wi wu wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wv wi wx
   wv wi wi wx wi wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wx wy wy wz wi
   wu wz wi wi wu wi wi wi wv wi wx wv wi wi wx wi wy wy wz wi wu wz wi wi wu
   wi wi wx wy wy wz wi wu wz wi wi wu wi wi wx wy wy wz wi wu wz wi wi wu wi
   wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wv wi wx wv wi wi wx wi wi wy
   wy wz wi wu wz wi wi wu wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wv wi
   wx wv wi wi wx wi wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wv wi wx wv
   wi wi wx wi wx wy wy wz wi wu wz wi wi wu wi wi wi wx wy wy wz wi wu wz wi
   wi wu wi wi wi wv wi wx wv wi wi wx wi wi wy wy wz wi wu wz wi wi wu wi wi
   wx wy wy wz wi wu wz wi wi wu wi wi wi wv wi wx wv wi wi wx wi wi wi wx wy
   wy wz wi wu wz wi wi wu wi wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wx
   wy wy wz wi wu wz wi wi wu wi wi wi wv wi wx wv wi wi wx wi wi wy wy wz wi
   wu wz wi wi wu wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wv wi wx wv wi
   wi wx wi wi wi wy wy wz wi wu wz wi wi wu wi wi wi wi wx wy wy wz wi wu wz
   wi wi wu wi wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wv wi wx wv wi wi
   wx wi wi wy wy wz wi wu wz wi wi wu wi wi wx wy wy wz wi wu wz wi wi wu wi
   wi wi wv wi wx wv wi wi wx wi wi wi wi wi wx wx wy wy wz wi wu wz wi wi wu
   wi wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wx wy wy wz wi wu wz wi wi
   wu wi wi wi wv wi wx wv wi wi wx wi wi wy wy wz wi wu wz wi wi wu wi wi wx
   wy wy wz wi wu wz wi wi wu wi wi wi wv wi wx wv wi wi wx wi wi wi wy wy wz
   wi wu wz wi wi wu wi wi wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wx wy
   wy wz wi wu wz wi wi wu wi wi wi wv wi wx wv wi wi wx wi wi wy wy wz wi wu
   wz wi wi wu wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wv wi wx wv wi wi
   wx wi wi wi wi wi wi wx wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wx wy
   wy wz wi wu wz wi wi wu wi wi wi wv wi wx wv wi wi wx wi wi wy wy wz wi wu
   wz wi wi wu wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wv wi wx wv wi wi
   wx wi wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wx wy wy wz wi wu wz wi
   wi wu wi wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wv wi wx wv wi wi wx
   wi wi wy wy wz wi wu wz wi wi wu wi wi wx wy wy wz wi wu wz wi wi wu wi wi
   wi wv wi wx wv wi wi wx wi wi wi wy wy wz wi wu wz wi wi wu wi wi wi wi wx
   wy wy wz wi wu wz wi wi wu wi wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi
   wv wi wx wv wi wi wx wi wi wy wy wz wi wu wz wi wi wu wi wi wx wy wy wz wi
   wu wz wi wi wu wi wi wi wv wi wx wv wi wi wx wi wi wi wi wi wx wx wy wy wz
   wi wu wz wi wi wu wi wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wx wy wy
   wz wi wu wz wi wi wu wi wi wi wv wi wx wv wi wi wx wi wi wy wy wz wi wu wz
   wi wi wu wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wv wi wx wv wi wi wx
   wi wi wi wy wy wz wi wu wz wi wi wu wi wi wi wi wx wy wy wz wi wu wz wi wi
   wu wi wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wv wi wx wv wi wi wx wi
   wi wy wy wz wi wu wz wi wi wu wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi
   wv wi wx wv wi wi wx wi wi wi wi wi wi wx wy wy wz wi wu wz wi wi wu wi wi
   wi wv wi wx wv wi wi wx wx wy wy wz wi wu wz wi wi wu wi wi wi wx wy wy wz
   wi wu wz wi wi wu wi wi wi wv wi wx wv wi wi wx wi wi wy wy wz wi wu wz wi
   wi wu wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wv wi wx wv wi wi wx wi
   wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wx wy wy wz wi wu wz wi wi wu
   wi wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wv wi wx wv wi wi wx wi wi
   wy wy wz wi wu wz wi wi wu wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wv
   wi wx wv wi wi wx wi wi wi wy wy wz wi wu wz wi wi wu wi wi wi wi wx wy wy
   wz wi wu wz wi wi wu wi wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wv wi
   wx wv wi wi wx wi wi wy wy wz wi wu wz wi wi wu wi wi wx wy wy wz wi wu wz
   wi wi wu wi wi wi wv wi wx wv wi wi wx wi wi wi wi wi wx wx wy wy wz wi wu
   wz wi wi wu wi wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wx wy wy wz wi
   wu wz wi wi wu wi wi wi wv wi wx wv wi wi wx wi wi wy wy wz wi wu wz wi wi
   wu wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wv wi wx wv wi wi wx wi wi
   wi wy wy wz wi wu wz wi wi wu wi wi wi wi wx wy wy wz wi wu wz wi wi wu wi
   wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wv wi wx wv wi wi wx wi wi wy
   wy wz wi wu wz wi wi wu wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wv wi
   wx wv wi wi wx wi wi wi wi wi wi ax-min wx wy wy wz wi wu wz wi wi wu wi wi
   wi wx wy wy wz wi wu wz wi wi wu wi wi wi wv wi wx wv wi wi wx wi wi wy wy
   wz wi wu wz wi wi wu wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wv wi wx
   wv wi wi wx wi wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wx wy wy wz wi
   wu wz wi wi wu wi wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wv wi wx wv
   wi wi wx wi wi wy wy wz wi wu wz wi wi wu wi wi wx wy wy wz wi wu wz wi wi
   wu wi wi wi wv wi wx wv wi wi wx wi wi wi wy wy wz wi wu wz wi wi wu wi wi
   wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wx wy wy wz wi wu wz wi wi wu
   wi wi wi wv wi wx wv wi wi wx wi wi wy wy wz wi wu wz wi wi wu wi wi wx wy
   wy wz wi wu wz wi wi wu wi wi wi wv wi wx wv wi wi wx wi wi wi wi wi wx wx
   wy wy wz wi wu wz wi wi wu wi wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi
   wx wy wy wz wi wu wz wi wi wu wi wi wi wv wi wx wv wi wi wx wi wi wy wy wz
   wi wu wz wi wi wu wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wv wi wx wv
   wi wi wx wi wi wi wy wy wz wi wu wz wi wi wu wi wi wi wi wx wy wy wz wi wu
   wz wi wi wu wi wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wv wi wx wv wi
   wi wx wi wi wy wy wz wi wu wz wi wi wu wi wi wx wy wy wz wi wu wz wi wi wu
   wi wi wi wv wi wx wv wi wi wx wi wi wi wi wi wi wx wy wy wz wi wu wz wi wi
   wu wi wi wi wv wi wx wv wi wi wx wi wx wy wy wz wi wu wz wi wi wu wi wi wi
   wy wx wv wz wu wx wy wy wz wi wu wz wi wi wu wi wi wi wx wy wy wz wi wu wz
   wi wi wu wi wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wv wi wx wv wi wi
   wx wi wi wy wy wz wi wu wz wi wi wu wi wi wx wy wy wz wi wu wz wi wi wu wi
   wi wi wv wi wx wv wi wi wx wi wi wi wy wy wz wi wu wz wi wi wu wi wi wi wi
   wx wy wy wz wi wu wz wi wi wu wi wi wi wx wy wy wz wi wu wz wi wi wu wi wi
   wi wv wi wx wv wi wi wx wi wi wy wy wz wi wu wz wi wi wu wi wi wx wy wy wz
   wi wu wz wi wi wu wi wi wi wv wi wx wv wi wi wx wi wi wi wi wx wx wy wy wz
   wi wu wz wi wi wu wi wi wi wv wi wx wv wi wi wx wi wx wy wy wz wi wu wz wi
   wi wu wi wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wv wi wx wv wi wi wx
   wi wi wy wy wz wi wu wz wi wi wu wi wi wx wy wy wz wi wu wz wi wi wu wi wi
   wi wv wi wx wv wi wi wx wi wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wx
   wy wy wz wi wu wz wi wi wu wi wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi
   wv wi wx wv wi wi wx wi wi wy wy wz wi wu wz wi wi wu wi wi wx wy wy wz wi
   wu wz wi wi wu wi wi wi wv wi wx wv wi wi wx wi wi wi wy wy wz wi wu wz wi
   wi wu wi wi wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wx wy wy wz wi wu
   wz wi wi wu wi wi wi wv wi wx wv wi wi wx wi wi wy wy wz wi wu wz wi wi wu
   wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wv wi wx wv wi wi wx wi wi wi
   wi wi wx wx wy wy wz wi wu wz wi wi wu wi wi wi wx wy wy wz wi wu wz wi wi
   wu wi wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wv wi wx wv wi wi wx wi
   wi wy wy wz wi wu wz wi wi wu wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi
   wv wi wx wv wi wi wx wi wi wi wy wy wz wi wu wz wi wi wu wi wi wi wi wx wy
   wy wz wi wu wz wi wi wu wi wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wv
   wi wx wv wi wi wx wi wi wy wy wz wi wu wz wi wi wu wi wi wx wy wy wz wi wu
   wz wi wi wu wi wi wi wv wi wx wv wi wi wx wi wi wi wi wi wi wx wi wi wx wy
   wy wz wi wu wz wi wi wu wi wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wv
   wi wx wv wi wi wx wi wi wy wy wz wi wu wz wi wi wu wi wi wx wy wy wz wi wu
   wz wi wi wu wi wi wi wv wi wx wv wi wi wx wi wi wi wx wy wy wz wi wu wz wi
   wi wu wi wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wx wy wy wz wi wu wz
   wi wi wu wi wi wi wv wi wx wv wi wi wx wi wi wy wy wz wi wu wz wi wi wu wi
   wi wx wy wy wz wi wu wz wi wi wu wi wi wi wv wi wx wv wi wi wx wi wi wi wy
   wy wz wi wu wz wi wi wu wi wi wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi
   wx wy wy wz wi wu wz wi wi wu wi wi wi wv wi wx wv wi wi wx wi wi wy wy wz
   wi wu wz wi wi wu wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wv wi wx wv
   wi wi wx wi wi wi wi wi wx wx wy wy wz wi wu wz wi wi wu wi wi wi wx wy wy
   wz wi wu wz wi wi wu wi wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wv wi
   wx wv wi wi wx wi wi wy wy wz wi wu wz wi wi wu wi wi wx wy wy wz wi wu wz
   wi wi wu wi wi wi wv wi wx wv wi wi wx wi wi wi wy wy wz wi wu wz wi wi wu
   wi wi wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wx wy wy wz wi wu wz wi
   wi wu wi wi wi wv wi wx wv wi wi wx wi wi wy wy wz wi wu wz wi wi wu wi wi
   wx wy wy wz wi wu wz wi wi wu wi wi wi wv wi wx wv wi wi wx wi wi wi wi wi
   wi wi wx wy wy wz wi wu wz wi wi wu wi wi wi wv wi wx wv wi wi ax-maj ax-mp
   $.

$(

This comment holds a simple typesetting definition file so that HTML
pages can be created with "show statement theorem1/html" in the
metamath program.

$t
htmldef "(" as " ( ";
htmldef ")" as " ) ";
htmldef "e" as " e ";
htmldef "wff" as " wff ";
htmldef "|-" as " |- ";
htmldef "," as " , ";
htmldef "x" as " x ";
htmldef "y" as " y ";
htmldef "z" as " z ";
htmldef "w" as " w ";
htmldef "v" as " v ";
htmldef "u" as " u ";
htmldef "v1" as " v1 ";
htmldef "v2" as " v2 ";
htmldef "v3" as " v3 ";
htmldef "v4" as " v4 ";
htmldef "v5" as " v5 ";
htmldef "v6" as " v6 ";
htmldef "v7" as " v7 ";
htmldef "v8" as " v8 ";
htmldef "v9" as " v9 ";
htmldef "v10" as " v10 ";
htmldef "v11" as " v11 ";
$)
