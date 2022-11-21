$( demo0.mm  1-Jan-04 $)

$(
                           ~~ PUBLIC DOMAIN ~~
This work is waived of all rights, including copyright, according to the CC0
Public Domain Dedication.  http://creativecommons.org/publicdomain/zero/1.0/

Norman Megill - email: nm at alum.mit.edu

$)


$( This file is the introductory formal system example described
   in Chapter 2 of the Meamath book. $)

$( Declare the constant symbols we will use $)
    $c 0 + = -> ( ) term wff |- $.
$( Declare the metavariables we will use $)
    $v t r s P Q $.
$( Specify properties of the metavariables $)
    tt $f term t $.
    tr $f term r $.
    ts $f term s $.
    wp $f wff P $.
    wq $f wff Q $.
$( Define "term" (part 1) $)
    tze $a term 0 $.
$( Define "term" (part 2) $)
    tpl $a term ( t + r ) $.
$( Define "wff" (part 1) $)
    weq $a wff t = r $.
$( Define "wff" (part 2) $)
    wim $a wff ( P -> Q ) $.
$( State axiom a1 $)
    a1 $a |- ( t = r -> ( t = s -> r = s ) ) $.
$( State axiom a2 $)
    a2 $a |- ( t + 0 ) = t $.
    ${
       min $e |- P $.
       maj $e |- ( P -> Q ) $.
$( Define the modus ponens inference rule $)
       mp  $a |- Q $.
    $}
$( Prove a theorem $)
    th1 $p |- t = t $=
  $( Here is its proof: $)
       tt tze tpl tt weq tt tt weq tt a2 tt tze tpl
       tt weq tt tze tpl tt weq tt tt weq wim tt a2
       tt tze tpl tt tt a1 mp mp
     $.

