$( This is the Metamath database ql.mm. $)

$( Metamath is a formal language and associated computer program for
   archiving, verifying, and studying mathematical proofs, created by Norman
   Dwight Megill (1950--2021).  For more information, visit
   https://us.metamath.org and
   https://github.com/metamath/set.mm, and feel free to ask questions at
   https://groups.google.com/group/metamath. $)

$( The database ql.mm was created by Norman Megill on 9-Aug-1997. $)


$( !
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
    Metamath source file for logic, set theory, numbers, and Hilbert space
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#

                           ~~ PUBLIC DOMAIN ~~
This work is waived of all rights, including copyright, according to the CC0
Public Domain Dedication.  http://creativecommons.org/publicdomain/zero/1.0/

Norman Megill

$)


$( placeholder
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
        AUQL - Algebraic Unified Quantum Logic of Mladen Pavicic
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)


$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
        Ortholattices
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Basic syntax and axioms
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Declare the primitive constant symbols. $)
  $c ( $.  $( Left parenthesis $)
  $c ) $.  $( Right parenthesis $)
  $c = $. $( Equality (read:  'equals') $)
  $c == $. $( Biconditional (read:  'equivalent') $)
  $c v $. $( Disjunction (read:  'or') $)
  $c ^ $. $( Conjuction (read:  'and') $)
  $c 1 $. $( True constant (upside down ' ) (read:  'true') $)
  $c 0 $. $( False constant ( ' ) (read:  'false') $)
  $c ' $. $( Orthocomplement $)
  $c wff $. $( Well-formed formula symbol (read:  'the following symbol
               sequence is a wff') $)
  $c term $. $( Term $)
  $c |- $. $( Turnstile (read:  'the following symbol sequence is provable' or
              'a proof exists for') $)

  $( $j
     syntax 'wff' 'term';
     syntax '|-' as 'wff';
     unambiguous 'klr 5';
  $)

  $( Relations as operations $)
  $c C $. $( Commutes relation or commutator operation $)
  $c =< $.  $( Less-than-or-equal-to $)
  $c =<2 $.  $( Less-than-or-equal-to analogue for terms $)
  $c ->0 $. $( Right arrow (read:  'implies') $)
  $c ->1 $. $( Right arrow (read:  'implies') $)
  $c ->2 $. $( Right arrow (read:  'implies') $)
  $c ->3 $. $( Right arrow (read:  'implies') $)
  $c ->4 $. $( Right arrow (read:  'implies') $)
  $c ->5 $. $( Right arrow (read:  'implies') $)
  $c ==0 $. $( Classical identity $)
  $c ==1 $. $( Asymmetrical identity $)
  $c ==2 $. $( Asymmetrical identity $)
  $c ==3 $. $( Asymmetrical identity $)
  $c ==4 $. $( Asymmetrical identity $)
  $c ==5 $. $( Asymmetrical identity $)
  $c ==OA $. $( Orthoarguesian identity $)
  $c , $.  $( Comma $)
  $c <->3 $. $( Biconditional (read:  'equivalent') $)
  $c <->1 $. $( Biconditional (read:  'equivalent') $)
  $c u3 $. $( Disjunction (read:  'or') $)
  $c ^3 $. $( Conjuction (read:  'and') $)

  $( Introduce some variable names we will use to terms. $)
  $v a $.
  $v b $.
  $v c $.
  $v d $.
  $v e $.
  $v f $.
  $v g $.
  $v h $.
  $v j $.
  $v k $.
  $v l $.

  $v i $.
  $v m $.
  $v n $.
  $v p $.
  $v q $.
  $v r $.
  $v t $.
  $v u $.
  $v w $.
  $v x $.
  $v y $.
  $v z $.

  $v a0 a1 a2 b0 b1 b2 c0 c1 c2 p0 p1 p2 $.

  $(
     Specify some variables that we will use to represent terms.
     The fact that a variable represents a wff is relevant only to a theorem
     referring to that variable, so we may use $f hypotheses.  The symbol
     ` term ` specifies that the variable that follows it represents a term.
  $)

  $( Let variable ` a ` be a term. $)
  wva $f term a $.
  $( Let variable ` b ` be a term. $)
  wvb $f term b $.
  $( Let variable ` c ` be a term. $)
  wvc $f term c $.
  $( Let variable ` d ` be a term. $)
  wvd $f term d $.
  $( Let variable ` e ` be a term. $)
  wve $f term e $.
  $( Let variable ` f ` be a term. $)
  wvf $f term f $.
  $( Let variable ` g ` be a term. $)
  wvg $f term g $.
  $( Let variable ` h ` be a term. $)
  wvh $f term h $.
  $( Let variable ` j ` be a term. $)
  wvj $f term j $.
  $( Let variable ` k ` be a term. $)
  wvk $f term k $.
  $( Let variable ` l ` be a term. $)
  wvl $f term l $.

  $( Let variable ` i ` be a term. $)
  wvi $f term i $.
  $( Let variable ` m ` be a term. $)
  wvm $f term m $.
  $( Let variable ` n ` be a term. $)
  wvn $f term n $.
  $( Let variable ` p ` be a term. $)
  wvp $f term p $.
  $( Let variable ` q ` be a term. $)
  wvq $f term q $.
  $( Let variable ` r ` be a term. $)
  wvr $f term r $.
  $( Let variable ` t ` be a term. $)
  wvt $f term t $.
  $( Let variable ` u ` be a term. $)
  wvu $f term u $.
  $( Let variable ` w ` be a term. $)
  wvw $f term w $.
  $( Let variable ` x ` be a term. $)
  wvx $f term x $.
  $( Let variable ` y ` be a term. $)
  wvy $f term y $.
  $( Let variable ` z ` be a term. $)
  wvz $f term z $.

  $( Let variable ` a0 ` be a term. $)
  wva0 $f term a0 $.
  $( Let variable ` a1 ` be a term. $)
  wva1 $f term a1 $.
  $( Let variable ` a2 ` be a term. $)
  wva2 $f term a2 $.
  $( Let variable ` b0 ` be a term. $)
  wvb0 $f term b0 $.
  $( Let variable ` b1 ` be a term. $)
  wvb1 $f term b1 $.
  $( Let variable ` b2 ` be a term. $)
  wvb2 $f term b2 $.
  $( Let variable ` c0 ` be a term. $)
  wvc0 $f term c0 $.
  $( Let variable ` c1 ` be a term. $)
  wvc1 $f term c1 $.
  $( Let variable ` c2 ` be a term. $)
  wvc2 $f term c2 $.
  $( Let variable ` p0 ` be a term. $)
  wvp0 $f term p0 $.
  $( Let variable ` p1 ` be a term. $)
  wvp1 $f term p1 $.
  $( Let variable ` p2 ` be a term. $)
  wvp2 $f term p2 $.

  $(
     Recursively define terms and wffs.
  $)

  $( If ` a ` and ` b ` are terms, ` a = b ` is a wff. $)
  wb $a wff a = b $.
  $( If ` a ` and ` b ` are terms, ` a =< b ` is a wff. $)
  wle $a wff a =< b $.
  $( If ` a ` and ` b ` are terms, ` a C b ` is a wff. $)
  wc $a wff a C b $.

  $( If ` a ` is a term, so is ` a ' ` . $)
  wn $a term a ' $.
  $( If ` a ` and ` b ` are terms, so is ` ( a == b ) ` . $)
  tb $a term ( a == b ) $.
  $( If ` a ` and ` b ` are terms, so is ` ( a v b ) ` . $)
  wo $a term ( a v b ) $.
  $( If ` a ` and ` b ` are terms, so is ` ( a ^ b ) ` . $)
  wa $a term ( a ^ b ) $.
$(
  @( If ` a ` and ` b ` are terms, so is ` ( a ' b ) ` . @)
  wp @a term ( a ' b ) @.
$)
  $( The logical true constant is a term. $)
  wt $a term 1 $.
  $( The logical false constant is a term. $)
  wf $a term 0 $.
  $( If ` a ` and ` b ` are terms, so is ` ( a =<2 b ) ` . $)
  wle2 $a term ( a =<2 b ) $.

  $( If ` a ` and ` b ` are terms, so is ` ( a ->0 b ) ` . $)
  wi0 $a term ( a ->0 b ) $.
  $( If ` a ` and ` b ` are terms, so is ` ( a ->1 b ) ` . $)
  wi1 $a term ( a ->1 b ) $.
  $( If ` a ` and ` b ` are terms, so is ` ( a ->2 b ) ` . $)
  wi2 $a term ( a ->2 b ) $.
  $( If ` a ` and ` b ` are terms, so is ` ( a ->3 b ) ` . $)
  wi3 $a term ( a ->3 b ) $.
  $( If ` a ` and ` b ` are terms, so is ` ( a ->4 b ) ` . $)
  wi4 $a term ( a ->4 b ) $.
  $( If ` a ` and ` b ` are terms, so is ` ( a ->5 b ) ` . $)
  wi5 $a term ( a ->5 b ) $.
  $( If ` a ` and ` b ` are terms, so is ` ( a ==0 b ) ` . $)
  wid0 $a term ( a ==0 b ) $.
  $( If ` a ` and ` b ` are terms, so is ` ( a ==1 b ) ` . $)
  wid1 $a term ( a ==1 b ) $.
  $( If ` a ` and ` b ` are terms, so is ` ( a ==2 b ) ` . $)
  wid2 $a term ( a ==2 b ) $.
  $( If ` a ` and ` b ` are terms, so is ` ( a ==3 b ) ` . $)
  wid3 $a term ( a ==3 b ) $.
  $( If ` a ` and ` b ` are terms, so is ` ( a ==4 b ) ` . $)
  wid4 $a term ( a ==4 b ) $.
  $( If ` a ` and ` b ` are terms, so is ` ( a ==5 b ) ` . $)
  wid5 $a term ( a ==5 b ) $.
  $( If ` a ` and ` b ` are terms, so is ` ( a <->3 b ) ` . $)
  wb3 $a term ( a <->3 b ) $.
  $( If ` a ` and ` b ` are terms, so is ` ( a <->3 b ) ` . $)
  wb1 $a term ( a <->1 b ) $.
  $( If ` a ` and ` b ` are terms, so is ` ( a u3 b ) ` . $)
  wo3 $a term ( a u3 b ) $.
  $( If ` a ` and ` b ` are terms, so is ` ( a ^3 b ) ` . $)
  wan3 $a term ( a ^3 b ) $.
  $( If ` a ` , ` b ` , and ` c ` are terms, so is ` ( a == c ==OA b ) ` . $)
  wid3oa $a term ( a == c ==OA b ) $.
  $( If ` a ` , ` b ` , ` c ` , and ` d ` are terms, so is
     ` ( a == c , d ==OA b ) ` . $)
  wid4oa $a term ( a == c , d ==OA b ) $.
  $( If ` a ` and ` b ` are terms, so is ` C ( a , b ) ` . $)
  wcmtr $a term C ( a , b ) $.

  $( Axiom for ortholattices.  (Contributed by NM, 9-Aug-1997.) $)
  ax-a1 $a |- a = a ' ' $.

  $( Axiom for ortholattices.  (Contributed by NM, 9-Aug-1997.) $)
  ax-a2 $a |- ( a v b ) = ( b v a ) $.

  $( Axiom for ortholattices.  (Contributed by NM, 9-Aug-1997.) $)
  ax-a3 $a |- ( ( a v b ) v c ) = ( a v ( b v c ) ) $.

  $( Axiom for ortholattices.  (Contributed by NM, 9-Aug-1997.) $)
  ax-a4 $a |- ( a v ( b v b ' ) ) = ( b v b ' ) $.

  $(
  ax-a5 $a |- ( a v ( a ' v b ' ) ' ) = a $.
  $)

  $( Axiom for ortholattices.  (Contributed by NM, 9-Aug-1997.) $)
  ax-a5 $a |- ( a v ( a ' v b ) ' ) = a $.

  $(
  df-b $a |- ( a == b ) =
           ( ( a ' ' v b ' ' ) ' v ( a ' v b ' ) ' ) $.
  $)

  ${
    r1.1 $e |- a = b $.
    $( Inference rule for ortholattices.  (Contributed by NM, 9-Aug-1997.) $)
    ax-r1 $a |- b = a $.
  $}

  ${
    r2.1 $e |- a = b $.
    r2.2 $e |- b = c $.
    $( Inference rule for ortholattices.  (Contributed by NM, 9-Aug-1997.) $)
    ax-r2 $a |- a = c $.
  $}

  $( Axiom ~ax-r3 is the orthomodular axiom and will be introduced
     when we start to use it. $)
  ${
    r4.1 $e |- a = b $.
    $( Inference rule for ortholattices.  (Contributed by NM, 9-Aug-1997.) $)
    ax-r4 $a |- a ' = b ' $.
  $}

  ${
    r5.1 $e |- a = b $.
    $( Inference rule for ortholattices.  (Contributed by NM, 9-Aug-1997.) $)
    ax-r5 $a |- ( a v c ) = ( b v c ) $.
  $}

  $( Define biconditional.  (Contributed by NM, 9-Aug-1997.) $)
  df-b $a |- ( a == b ) = ( ( a ' v b ' ) ' v ( a v b ) ' ) $.

  $( Define conjunction.  (Contributed by NM, 9-Aug-1997.) $)
  df-a $a |- ( a ^ b ) = ( a ' v b ' ) ' $.

  $( Define true.  (Contributed by NM, 9-Aug-1997.) $)
  df-t $a |- 1 = ( a v a ' ) $.

  $( Define false.  (Contributed by NM, 9-Aug-1997.) $)
  df-f $a |- 0 = 1 ' $.

  $( Define classical conditional.  (Contributed by NM, 31-Oct-1998.) $)
  df-i0 $a |- ( a ->0 b ) = ( a ' v b ) $.

  $( Define Sasaki (Mittelstaedt) conditional.  (Contributed by NM,
     23-Nov-1997.) $)
  df-i1 $a |- ( a ->1 b ) = ( a ' v ( a ^ b ) ) $.

  $( Define Dishkant conditional.  (Contributed by NM, 23-Nov-1997.) $)
  df-i2 $a |- ( a ->2 b ) = ( b v ( a ' ^ b ' ) ) $.

  $( Define Kalmbach conditional.  (Contributed by NM, 2-Nov-1997.) $)
  df-i3 $a |- ( a ->3 b ) = ( ( ( a ' ^ b ) v ( a ' ^ b ' ) ) v
                ( a ^ ( a ' v b ) ) ) $.

  $( Define non-tollens conditional.  (Contributed by NM, 23-Nov-1997.) $)
  df-i4 $a |- ( a ->4 b ) = ( ( ( a ^ b ) v ( a ' ^ b ) ) v
                ( ( a ' v b ) ^ b ' ) ) $.

  $( Define relevance conditional.  (Contributed by NM, 23-Nov-1997.) $)
  df-i5 $a |- ( a ->5 b ) = ( ( ( a ^ b ) v ( a ' ^ b ) ) v
                ( a ' ^ b ' ) ) $.

  $( Define classical identity.  (Contributed by NM, 7-Feb-1999.) $)
  df-id0 $a |- ( a ==0 b ) = ( ( a ' v b ) ^ ( b ' v a ) ) $.

  $( Define asymmetrical identity (for "Non-Orthomodular Models..." paper).
     (Contributed by NM, 7-Feb-1999.) $)
  df-id1 $a |- ( a ==1 b ) = ( ( a v b ' ) ^ ( a ' v ( a ^ b ) ) ) $.

  $( Define asymmetrical identity (for "Non-Orthomodular Models..." paper).
     (Contributed by NM, 7-Feb-1999.) $)
  df-id2 $a |- ( a ==2 b ) = ( ( a v b ' ) ^ ( b v ( a ' ^ b ' ) ) ) $.

  $( Define asymmetrical identity (for "Non-Orthomodular Models..." paper).
     (Contributed by NM, 7-Feb-1999.) $)
  df-id3 $a |- ( a ==3 b ) = ( ( a ' v b ) ^ ( a v ( a ' ^ b ' ) ) ) $.

  $( Define asymmetrical identity (for "Non-Orthomodular Models..." paper).
     (Contributed by NM, 7-Feb-1999.) $)
  df-id4 $a |- ( a ==4 b ) = ( ( a ' v b ) ^ ( b ' v ( a ^ b ) ) ) $.

  $( Defined disjunction.  (Contributed by NM, 2-Nov-1997.) $)
  df-o3 $a |- ( a u3 b ) = ( a ' ->3 ( a ' ->3 b ) ) $.

  $( Defined conjunction.  (Contributed by NM, 2-Nov-1997.) $)
  df-a3 $a |- ( a ^3 b ) = ( a ' u3 b ' ) ' $.

  $( Defined biconditional.  (Contributed by NM, 2-Nov-1997.) $)
  df-b3 $a |- ( a <->3 b ) = ( ( a ->3 b ) ^ ( b ->3 a ) ) $.

  $( The 3-variable orthoarguesian identity term.  (Contributed by NM,
     22-Sep-1998.) $)
  df-id3oa $a |- ( a == c ==OA b ) = ( ( ( a ->1 c ) ^ ( b ->1 c ) )
     v ( ( a ' ->1 c ) ^ ( b ' ->1 c ) ) ) $.

  $( The 4-variable orthoarguesian identity term.  (Contributed by NM,
     28-Nov-1998.) $)
  df-id4oa $a |- ( a == c , d ==OA b ) = ( ( a == d ==OA b ) v
                    ( ( a == d ==OA c ) ^ ( b == d ==OA c ) ) ) $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Basic lemmas
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Identity law.  (Contributed by NM, 9-Aug-1997.) $)
  id $p |- a = a $=
    ( wn ax-a1 ax-r1 ax-r2 ) AABBZAACZAFGDE $.

  $( Justification of definition ~ df-t of true ( ` 1 ` ).  This shows that the
     definition is independent of the variable used to define it.  (Contributed
     by NM, 9-Aug-1997.) $)
  tt $p |- ( a v a ' ) = ( b v b ' ) $=
    ( wn wo ax-a4 ax-r1 ax-a2 ax-r2 ) AACDZIBBCDZDZJIJIDZKLIJAEFJIGHIBEH $.

  ${
    cm.1 $e |- a = b $.
    $( Commutative inference rule for ortholattices.  (Contributed by NM,
       26-May-2008.) $)
    cm $p |- b = a $=
      ( ax-r1 ) ABCD $.
  $}

  ${
    tr.1 $e |- a = b $.
    tr.2 $e |- b = c $.
    $( Transitive inference rule for ortholattices.  (Contributed by NM,
       26-May-2008.) $)
    tr $p |- a = c $=
      ( ax-r2 ) ABCDEF $.
  $}

  ${
    3tr1.1 $e |- a = b $.
    3tr1.2 $e |- c = a $.
    3tr1.3 $e |- d = b $.
    $( Transitive inference useful for introducing definitions.  (Contributed
       by NM, 10-Aug-1997.) $)
    3tr1 $p |- c = d $=
      ( ax-r1 ax-r2 ) CADFABDEDBGHII $.
  $}

  ${
    3tr2.1 $e |- a = b $.
    3tr2.2 $e |- a = c $.
    3tr2.3 $e |- b = d $.
    $( Transitive inference useful for eliminating definitions.  (Contributed
       by NM, 10-Aug-1997.) $)
    3tr2 $p |- c = d $=
      ( ax-r1 3tr1 ) ABCDEACFHBDGHI $.
  $}

  ${
    3tr.1 $e |- a = b $.
    3tr.2 $e |- b = c $.
    3tr.3 $e |- c = d $.
    $( Triple transitive inference.  (Contributed by NM, 20-Sep-1998.) $)
    3tr $p |- a = d $=
      ( ax-r2 ) ACDABCEFHGH $.
  $}

  ${
    con1.1 $e |- a ' = b ' $.
    $( Contraposition inference.  (Contributed by NM, 10-Aug-1997.) $)
    con1 $p |- a = b $=
      ( wn ax-r4 ax-a1 3tr1 ) ADZDBDZDABHICEAFBFG $.
  $}

  ${
    con2.1 $e |- a = b ' $.
    $( Contraposition inference.  (Contributed by NM, 10-Aug-1997.) $)
    con2 $p |- a ' = b $=
      ( wn ax-r4 ax-a1 ax-r1 ax-r2 ) ADBDZDZBAICEBJBFGH $.
  $}

  ${
    con3.1 $e |- a ' = b $.
    $( Contraposition inference.  (Contributed by NM, 10-Aug-1997.) $)
    con3 $p |- a = b ' $=
      ( wn ax-a1 ax-r4 ax-r2 ) AADZDBDAEHBCFG $.
  $}

  ${
    con4.1 $e |- a = b $.
    $( Contraposition inference.  (Contributed by NM, 26-May-2008.)  (Revised
       by NM, 31-Mar-2011.) $)
    con4 $p |- a ' = b ' $=
      ( ax-r4 ) ABCD $.
  $}

  ${
    lor.1 $e |- a = b $.
    $( Inference introducing disjunct to left.  (Contributed by NM,
       10-Aug-1997.) $)
    lor $p |- ( c v a ) = ( c v b ) $=
      ( wo ax-r5 ax-a2 3tr1 ) ACEBCECAECBEABCDFCAGCBGH $.

    $( Inference introducing disjunct to right.  (Contributed by NM,
       26-May-2008.)  (Revised by NM, 31-Mar-2011.) $)
    ror $p |- ( a v c ) = ( b v c ) $=
      ( ax-r5 ) ABCDE $.
  $}

  ${
    2or.1 $e |- a = b $.
    2or.2 $e |- c = d $.
    $( Join both sides with disjunction.  (Contributed by NM, 10-Aug-1997.) $)
    2or $p |- ( a v c ) = ( b v d ) $=
      ( wo lor ax-r5 ax-r2 ) ACGADGBDGCDAFHABDEIJ $.
  $}

  $( Commutative law.  (Contributed by NM, 27-May-2008.)  (Revised by NM,
     31-Mar-2011.) $)
  orcom $p |- ( a v b ) = ( b v a ) $=
    ( ax-a2 ) ABC $.

  $( Commutative law.  (Contributed by NM, 10-Aug-1997.) $)
  ancom $p |- ( a ^ b ) = ( b ^ a ) $=
    ( wn wo wa ax-a2 ax-r4 df-a 3tr1 ) ACZBCZDZCKJDZCABEBAELMJKFGABHBAHI $.

  $( Associative law.  (Contributed by NM, 27-May-2008.)  (Revised by NM,
     31-Mar-2011.) $)
  orass $p |- ( ( a v b ) v c ) = ( a v ( b v c ) ) $=
    ( ax-a3 ) ABCD $.

  $( Associative law.  (Contributed by NM, 12-Aug-1997.) $)
  anass $p |- ( ( a ^ b ) ^ c ) = ( a ^ ( b ^ c ) ) $=
    ( wa wn wo ax-a3 df-a con2 ax-r5 lor 3tr1 ax-r4 ) ABDZEZCEZFZEAEZBCDZEZFZEN
    CDASDQUARBEZFZPFRUBPFZFQUARUBPGOUCPNUCABHIJTUDRSUDBCHIKLMNCHASHL $.

  ${
    lan.1 $e |- a = b $.
    $( Introduce conjunct on left.  (Contributed by NM, 10-Aug-1997.) $)
    lan $p |- ( c ^ a ) = ( c ^ b ) $=
      ( wn wo wa ax-r4 lor df-a 3tr1 ) CEZAEZFZELBEZFZECAGCBGNPMOLABDHIHCAJCBJK
      $.
  $}

  ${
    ran.1 $e |- a = b $.
    $( Introduce conjunct on right.  (Contributed by NM, 10-Aug-1997.) $)
    ran $p |- ( a ^ c ) = ( b ^ c ) $=
      ( wa lan ancom 3tr1 ) CAECBEACEBCEABCDFACGBCGH $.
  $}

  ${
    2an.1 $e |- a = b $.
    2an.2 $e |- c = d $.
    $( Conjoin both sides of hypotheses.  (Contributed by NM, 10-Aug-1997.) $)
    2an $p |- ( a ^ c ) = ( b ^ d ) $=
      ( wa lan ran ax-r2 ) ACGADGBDGCDAFHABDEIJ $.
  $}

  $( Swap disjuncts.  (Contributed by NM, 27-Aug-1997.) $)
  or12 $p |- ( a v ( b v c ) ) = ( b v ( a v c ) ) $=
    ( wo ax-a2 ax-r5 ax-a3 3tr2 ) ABDZCDBADZCDABCDDBACDDIJCABEFABCGBACGH $.

  $( Swap conjuncts.  (Contributed by NM, 27-Aug-1997.) $)
  an12 $p |- ( a ^ ( b ^ c ) ) = ( b ^ ( a ^ c ) ) $=
    ( wa ancom ran anass 3tr2 ) ABDZCDBADZCDABCDDBACDDIJCABEFABCGBACGH $.

  $( Swap disjuncts.  (Contributed by NM, 27-Aug-1997.) $)
  or32 $p |- ( ( a v b ) v c ) = ( ( a v c ) v b ) $=
    ( wo ax-a2 lor ax-a3 3tr1 ) ABCDZDACBDZDABDCDACDBDIJABCEFABCGACBGH $.

  $( Swap conjuncts.  (Contributed by NM, 27-Aug-1997.) $)
  an32 $p |- ( ( a ^ b ) ^ c ) = ( ( a ^ c ) ^ b ) $=
    ( wa ancom lan anass 3tr1 ) ABCDZDACBDZDABDCDACDBDIJABCEFABCGACBGH $.

  $( Swap disjuncts.  (Contributed by NM, 27-Aug-1997.) $)
  or4 $p |- ( ( a v b ) v ( c v d ) ) = ( ( a v c ) v ( b v d ) ) $=
    ( wo or12 lor ax-a3 3tr1 ) ABCDEZEZEACBDEZEZEABEJEACELEKMABCDFGABJHACLHI $.

  $( Rearrange disjuncts.  (Contributed by NM, 4-Mar-2006.) $)
  or42 $p |- ( ( a v b ) v ( c v d ) ) = ( ( a v d ) v ( b v c ) ) $=
    ( wo ax-a2 lor or4 ax-r2 ) ABEZCDEZEJDCEZEADEBCEEKLJCDFGABDCHI $.

  $( Swap conjuncts.  (Contributed by NM, 27-Aug-1997.) $)
  an4 $p |- ( ( a ^ b ) ^ ( c ^ d ) ) = ( ( a ^ c ) ^ ( b ^ d ) ) $=
    ( wa an12 lan anass 3tr1 ) ABCDEZEZEACBDEZEZEABEJEACELEKMABCDFGABJHACLHI $.

  $( Disjunction expressed with conjunction.  (Contributed by NM,
     10-Aug-1997.) $)
  oran $p |- ( a v b ) = ( a ' ^ b ' ) ' $=
    ( wn wo wa ax-a1 2or df-a ax-r4 3tr1 ) ACZCZBCZCZDZOCZCABDKMEZCOFALBNAFBFGQ
    PKMHIJ $.

  $( Conjunction expressed with disjunction.  (Contributed by NM,
     12-Aug-1997.) $)
  anor1 $p |- ( a ^ b ' ) = ( a ' v b ) ' $=
    ( wn wa wo df-a ax-a1 ax-r1 lor ax-r4 ax-r2 ) ABCZDACZLCZEZCMBEZCALFOPNBMBN
    BGHIJK $.

  $( Conjunction expressed with disjunction.  (Contributed by NM,
     12-Aug-1997.) $)
  anor2 $p |- ( a ' ^ b ) = ( a v b ' ) ' $=
    ( wn wa wo df-a ax-a1 ax-r1 ax-r5 ax-r4 ax-r2 ) ACZBDLCZBCZEZCANEZCLBFOPMAN
    AMAGHIJK $.

  $( Conjunction expressed with disjunction.  (Contributed by NM,
     15-Dec-1997.) $)
  anor3 $p |- ( a ' ^ b ' ) = ( a v b ) ' $=
    ( wn wa wo oran ax-r1 con3 ) ACBCDZABEZJICABFGH $.

  $( Disjunction expressed with conjunction.  (Contributed by NM,
     15-Dec-1997.) $)
  oran1 $p |- ( a v b ' ) = ( a ' ^ b ) ' $=
    ( wn wo wa anor2 ax-r1 con3 ) ABCDZACBEZJICABFGH $.

  $( Disjunction expressed with conjunction.  (Contributed by NM,
     15-Dec-1997.) $)
  oran2 $p |- ( a ' v b ) = ( a ^ b ' ) ' $=
    ( wn wo wa anor1 ax-r1 con3 ) ACBDZABCEZJICABFGH $.

  $( Disjunction expressed with conjunction.  (Contributed by NM,
     15-Dec-1997.) $)
  oran3 $p |- ( a ' v b ' ) = ( a ^ b ) ' $=
    ( wn wo wa df-a ax-r1 con3 ) ACBCDZABEZJICABFGH $.

  $( Biconditional expressed with others.  (Contributed by NM, 10-Aug-1997.) $)
  dfb $p |- ( a == b ) = ( ( a ^ b ) v ( a ' ^ b ' ) ) $=
    ( tb wn wo wa df-b df-a ax-r1 oran con2 2or ax-r2 ) ABCADZBDZEDZABEZDZEABFZ
    NOFZEABGPSRTSPABHIQTABJKLM $.

  $( Negated biconditional.  (Contributed by NM, 30-Aug-1997.) $)
  dfnb $p |- ( a == b ) ' = ( ( a v b ) ^ ( a ' v b ' ) ) $=
    ( wa wn wo tb oran con2 ancom ax-r2 dfb ax-r4 df-a ax-r1 2an 3tr1 ) ABCZADZ
    BDZCZEZDZTDZQDZCZABFZDABEZRSEZCUBUDUCCZUEUAUIQTGHUDUCIJUFUAABKLUGUCUHUDABGU
    DUHQUHABMHNOP $.

  $( Commutative law.  (Contributed by NM, 10-Aug-1997.) $)
  bicom $p |- ( a == b ) = ( b == a ) $=
    ( wa wn wo tb ancom 2or dfb 3tr1 ) ABCZADZBDZCZEBACZMLCZEABFBAFKONPABGLMGHA
    BIBAIJ $.

  ${
    lbi.1 $e |- a = b $.
    $( Introduce biconditional to the left.  (Contributed by NM,
       10-Aug-1997.) $)
    lbi $p |- ( c == a ) = ( c == b ) $=
      ( wa wn wo tb lan ax-r4 2or dfb 3tr1 ) CAEZCFZAFZEZGCBEZOBFZEZGCAHCBHNRQT
      ABCDIPSOABDJIKCALCBLM $.
  $}

  ${
    rbi.1 $e |- a = b $.
    $( Introduce biconditional to the right.  (Contributed by NM,
       10-Aug-1997.) $)
    rbi $p |- ( a == c ) = ( b == c ) $=
      ( tb lbi bicom 3tr1 ) CAECBEACEBCEABCDFACGBCGH $.
  $}

  ${
    2bi.1 $e |- a = b $.
    2bi.2 $e |- c = d $.
    $( Join both sides with biconditional.  (Contributed by NM,
       10-Aug-1997.) $)
    2bi $p |- ( a == c ) = ( b == d ) $=
      ( tb lbi rbi ax-r2 ) ACGADGBDGCDAFHABDEIJ $.
  $}

  $( Alternate defintion of "false".  (Contributed by NM, 10-Aug-1997.) $)
  dff2 $p |- 0 = ( a v a ' ) ' $=
    ( wf wt wn wo df-f df-t ax-r4 ax-r2 ) BCDAADEZDFCJAGHI $.

  $( Alternate defintion of "false".  (Contributed by NM, 29-Aug-1997.) $)
  dff $p |- 0 = ( a ^ a ' ) $=
    ( wf wn wo wa dff2 ancom anor2 ax-r2 ax-r1 ) BAACZDCZAKEZAFMLMKAELAKGAAHIJI
    $.

  $( Disjunction with 0.  (Contributed by NM, 10-Aug-1997.) $)
  or0 $p |- ( a v 0 ) = a $=
    ( wf wo wn dff2 ax-a2 ax-r4 ax-r2 lor ax-a5 ) ABCAADZACZDZCABMABAKCZDMAENLA
    KFGHIAAJH $.

  $( Disjunction with 0.  (Contributed by NM, 26-Nov-1997.) $)
  or0r $p |- ( 0 v a ) = a $=
    ( wf wo ax-a2 or0 ax-r2 ) BACABCABADAEF $.

  $( Disjunction with 1.  (Contributed by NM, 10-Aug-1997.) $)
  or1 $p |- ( a v 1 ) = 1 $=
    ( wt wo wn df-t lor ax-a4 ax-r2 ax-r1 ) ABCZAADCZBJAKCKBKAAEZFAAGHBKLIH $.

  $( Disjunction with 1.  (Contributed by NM, 26-Nov-1997.) $)
  or1r $p |- ( 1 v a ) = 1 $=
    ( wt wo ax-a2 or1 ax-r2 ) BACABCBBADAEF $.

  $( Conjunction with 1.  (Contributed by NM, 10-Aug-1997.) $)
  an1 $p |- ( a ^ 1 ) = a $=
    ( wt wa wn wo df-a wf df-f ax-r1 lor or0 ax-r2 con2 ) ABCADZBDZEZDAABFPAPNG
    ENOGNGOHIJNKLML $.

  $( Conjunction with 1.  (Contributed by NM, 26-Nov-1997.) $)
  an1r $p |- ( 1 ^ a ) = a $=
    ( wt wa ancom an1 ax-r2 ) BACABCABADAEF $.

  $( Conjunction with 0.  (Contributed by NM, 10-Aug-1997.) $)
  an0 $p |- ( a ^ 0 ) = 0 $=
    ( wf wa wn wo df-a wt or1 df-f con2 lor 3tr1 ax-r2 ) ABCADZBDZEZDBABFPBNGEG
    PONHOGNBGIJZKQLJM $.

  $( Conjunction with 0.  (Contributed by NM, 26-Nov-1997.) $)
  an0r $p |- ( 0 ^ a ) = 0 $=
    ( wf wa ancom an0 ax-r2 ) BACABCBBADAEF $.

  $( Idempotent law.  (Contributed by NM, 10-Aug-1997.) $)
  oridm $p |- ( a v a ) = a $=
    ( wo wn wf ax-a1 or0 ax-r1 ax-r4 ax-r2 lor ax-a5 ) AABAACZDBZCZBAANAALCNAEL
    MMLLFGHIJADKI $.

  $( Idempotent law.  (Contributed by NM, 10-Aug-1997.) $)
  anidm $p |- ( a ^ a ) = a $=
    ( wa wn wo df-a oridm con2 ax-r2 ) AABACZIDZCAAAEJAIFGH $.

  $( Distribution of disjunction over disjunction.  (Contributed by NM,
     27-Aug-1997.) $)
  orordi $p |- ( a v ( b v c ) ) =
               ( ( a v b ) v ( a v c ) ) $=
    ( wo oridm ax-r1 ax-r5 or4 ax-r2 ) ABCDZDAADZJDABDACDDAKJKAAEFGAABCHI $.

  $( Distribution of disjunction over disjunction.  (Contributed by NM,
     27-Aug-1997.) $)
  orordir $p |- ( ( a v b ) v c ) =
               ( ( a v c ) v ( b v c ) ) $=
    ( wo oridm ax-r1 lor or4 ax-r2 ) ABDZCDJCCDZDACDBCDDCKJKCCEFGABCCHI $.

  $( Distribution of conjunction over conjunction.  (Contributed by NM,
     27-Aug-1997.) $)
  anandi $p |- ( a ^ ( b ^ c ) ) =
               ( ( a ^ b ) ^ ( a ^ c ) ) $=
    ( wa anidm ax-r1 ran an4 ax-r2 ) ABCDZDAADZJDABDACDDAKJKAAEFGAABCHI $.

  $( Distribution of conjunction over conjunction.  (Contributed by NM,
     27-Aug-1997.) $)
  anandir $p |- ( ( a ^ b ) ^ c ) =
               ( ( a ^ c ) ^ ( b ^ c ) ) $=
    ( wa anidm ax-r1 lan an4 ax-r2 ) ABDZCDJCCDZDACDBCDDCKJKCCEFGABCCHI $.

  $( Identity law.  (Contributed by NM, 10-Aug-1997.) $)
  biid $p |- ( a == a ) = 1 $=
    ( wa wn wo tb wt anidm 2or dfb df-t 3tr1 ) AABZACZMBZDAMDAAEFLANMAGMGHAAIAJ
    K $.

  $( Identity law.  (Contributed by NM, 10-Aug-1997.) $)
  1b $p |- ( 1 == a ) = a $=
    ( wt tb wa wn wo dfb wf ancom df-f ax-r1 lan ax-r2 2or an1 an0 or0 ) BACBAD
    ZBEZAEZDZFZABAGUBAHFZAUBABDZTHDZFUCRUDUAUEBAIUATSDUESTISHTHSJKLMNUDAUEHAOTP
    NMAQMM $.

  ${
    bi1.1 $e |- a = b $.
    $( Identity inference.  (Contributed by NM, 30-Aug-1997.) $)
    bi1 $p |- ( a == b ) = 1 $=
      ( tb wt rbi biid ax-r2 ) ABDBBDEABBCFBGH $.
  $}

  ${
    1bi.1 $e |- a = b $.
    $( Identity inference.  (Contributed by NM, 30-Aug-1997.) $)
    1bi $p |- 1 = ( a == b ) $=
      ( tb wt bi1 ax-r1 ) ABDEABCFG $.
  $}

  $( Absorption law.  (Contributed by NM, 11-Aug-1997.) $)
  orabs $p |- ( a v ( a ^ b ) ) = a $=
    ( wa wo wn df-a lor ax-a5 ax-r2 ) AABCZDAAEBEZDEZDAJLAABFGAKHI $.

  $( Absorption law.  (Contributed by NM, 11-Aug-1997.) $)
  anabs $p |- ( a ^ ( a v b ) ) = a $=
    ( wo wa wn ax-a1 ax-r5 lan df-a ax-r2 ax-a5 con2 ) AABCZDZAEZOEZBCZECZEZANA
    QDSMQAAPBAFGHAQIJRAOBKLJ $.

  $( Contraposition law.  (Contributed by NM, 10-Aug-1997.) $)
  conb $p |- ( a == b ) = ( a ' == b ' ) $=
    ( wa wn wo tb ax-a2 ax-a1 2an lor ax-r2 dfb 3tr1 ) ABCZADZBDZCZEZQODZPDZCZE
    ZABFOPFRQNEUBNQGNUAQASBTAHBHIJKABLOPLM $.

  ${
    leoa.1 $e |- ( a v c ) = b $.
    $( Relation between two methods of expressing "less than or equal to".
       (Contributed by NM, 11-Aug-1997.) $)
    leoa $p |- ( a ^ b ) = a $=
      ( wa wo ax-r1 lan anabs ax-r2 ) ABEAACFZEABKAKBDGHACIJ $.
  $}

  ${
    leao.1 $e |- ( c ^ b ) = a $.
    $( Relation between two methods of expressing "less than or equal to".
       (Contributed by NM, 11-Aug-1997.) $)
    leao $p |- ( a v b ) = b $=
      ( wo wa ax-a2 ax-r1 ancom ax-r2 lor orabs ) ABEZBBCFZEZBMBAEOABGANBACBFZN
      PADHNPBCIHJKJBCLJ $.
  $}

  $( Mittelstaedt implication.  (Contributed by NM, 12-Aug-1997.) $)
  mi $p |- ( ( a v b ) == b ) = ( b v ( a ' ^ b ' ) ) $=
    ( wo tb wa wn dfb ancom ax-a2 lan anabs ax-r2 oran con2 ran anass anidm 2or
    ) ABCZBDSBEZSFZBFZEZCBAFZUBEZCSBGTBUCUETBSEZBSBHUFBBACZEBSUGBABIJBAKLLUCUDU
    BUBEZEZUEUCUEUBEUIUAUEUBSUEABMNOUDUBUBPLUHUBUDUBQJLRL $.

  $( Dishkant implication.  (Contributed by NM, 12-Aug-1997.) $)
  di $p |- ( ( a ^ b ) == a ) = ( a ' v ( a ^ b ) ) $=
    ( wn wo tb wa conb ax-a1 ax-r1 rbi mi ax-r2 ancom df-a 2an lor 3tr1 ) BCZAC
    ZDZCZAEZSRCZSCZFZDZABFZAESUGDUBUACZSEZUFUAAGUITSEUFUHTSTUHTHIJRSKLLUGUAAUGB
    AFZUAABMZBANLJUGUESUGUJUEUKBUCAUDBHAHOLPQ $.

  $( Lemma in proof of Thm. 1 of Pavicic 1987.  (Contributed by NM,
     12-Aug-1997.) $)
  omlem1 $p |- ( ( a v ( a ' ^ ( a v b ) ) ) v ( a v b ) ) =
               ( a v b ) $=
    ( wn wo wa ax-a2 ax-a3 3tr1 ax-r2 ax-r1 oridm ax-r5 ancom 2or orabs 3tr2 )
    AACZABDZEZDZADBDZRADZSDZTRDZRUDRTDUAUCTRFTABGZRASGHUEUCRRQEZDRUBRSUFUBAADZB
    DZRUHUBUHARDUBAABGARFIJUGABAKLIQRMNRQOIP $.

  $( Lemma in proof of Thm. 1 of Pavicic 1987.  (Contributed by NM,
     12-Aug-1997.) $)
  omlem2 $p |- ( ( a v b ) ' v ( a v ( a ' ^ ( a v b ) ) ) ) = 1 $=
    ( wo wn wa wt ax-a2 anor2 2or ax-a3 ax-r1 df-t 3tr1 ) ABCZDZACZADNEZCZAOCZS
    DZCOAQCCZFPSQTOAGANHIRUAOAQJKSLM $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Relationship analogues (ordering; commutation)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Define "less than or equal to" analogue.  (Contributed by NM,
     27-Aug-1997.) $)
  df-le $a |- ( a =<2 b ) = ( ( a v b ) == b ) $.

  $( Since we don't have strong BMP in AUQL, we must add extra definitions
     to eliminate the middle = .  $)
  ${
    df-le1.1 $e |- ( a v b ) = b $.
    $( Define "less than or equal to".  See ~ df-le2 for the other direction.
       (Contributed by NM, 27-Aug-1997.) $)
    df-le1 $a |- a =< b $.
  $}

  ${
    df-le2.1 $e |- a =< b $.
    $( Define "less than or equal to".  See ~ df-le1 for the other direction.
       (Contributed by NM, 27-Aug-1997.) $)
    df-le2 $a |- ( a v b ) = b $.
  $}

  ${
    df-c1.1 $e |- a = ( ( a ^ b ) v ( a ^ b ' ) ) $.
    $( Define "commutes".  See ~ df-c2 for the other direction.  (Contributed
       by NM, 27-Aug-1997.) $)
    df-c1 $a |- a C b $.
  $}

  ${
    df-c2.1 $e |- a C b $.
    $( Define "commutes".  See ~ df-c1 for the other direction.  (Contributed
       by NM, 27-Aug-1997.) $)
    df-c2 $a |- a = ( ( a ^ b ) v ( a ^ b ' ) ) $.
  $}

  $( Define "commutator".  (Contributed by NM, 24-Jan-1999.) $)
  df-cmtr $a |- C ( a , b ) = ( ( ( a ^ b ) v ( a ^ b ' ) ) v
             ( ( a ' ^ b ) v ( a ' ^ b ' ) ) ) $.

  ${
    df2le1.1 $e |- ( a ^ b ) = a $.
    $( Alternate definition of "less than or equal to".  (Contributed by NM,
       27-Aug-1997.) $)
    df2le1 $p |- a =< b $=
      ( leao df-le1 ) ABABACDE $.
  $}

  ${
    df2le2.1 $e |- a =< b $.
    $( Alternate definition of "less than or equal to".  (Contributed by NM,
       27-Aug-1997.) $)
    df2le2 $p |- ( a ^ b ) = a $=
      ( df-le2 leoa ) ABBABCDE $.
  $}

  ${
    letr.1 $e |- a =< b $.
    letr.2 $e |- b =< c $.
    $( Transitive law for "less than or equal to".  (Contributed by NM,
       27-Aug-1997.) $)
    letr $p |- a =< c $=
      ( wa wo df-le2 ax-r5 ax-r1 ax-a3 3tr2 lan anabs ax-r2 df2le1 ) ACACFAABCG
      ZGZFACRAQABGZCGZCRTQSBCABDHIJBCEHABCKLMAQNOP $.
  $}

  ${
    bltr.1 $e |- a = b $.
    bltr.2 $e |- b =< c $.
    $( Transitive inference.  (Contributed by NM, 28-Aug-1997.) $)
    bltr $p |- a =< c $=
      ( wo ax-r5 df-le2 ax-r2 df-le1 ) ACACFBCFCABCDGBCEHIJ $.
  $}

  ${
    lbtr.1 $e |- a =< b $.
    lbtr.2 $e |- b = c $.
    $( Transitive inference.  (Contributed by NM, 28-Aug-1997.) $)
    lbtr $p |- a =< c $=
      ( wa ax-r1 lan df2le2 ax-r2 df2le1 ) ACACFABFACBABCEGHABDIJK $.
  $}

  ${
    le3tr1.1 $e |- a =< b $.
    le3tr1.2 $e |- c = a $.
    le3tr1.3 $e |- d = b $.
    $( Transitive inference useful for introducing definitions.  (Contributed
       by NM, 27-Aug-1997.) $)
    le3tr1 $p |- c =< d $=
      ( bltr ax-r1 lbtr ) CBDCABFEHDBGIJ $.
  $}

  ${
    le3tr2.1 $e |- a =< b $.
    le3tr2.2 $e |- a = c $.
    le3tr2.3 $e |- b = d $.
    $( Transitive inference useful for eliminating definitions.  (Contributed
       by NM, 27-Aug-1997.) $)
    le3tr2 $p |- c =< d $=
      ( ax-r1 le3tr1 ) ABCDEACFHBDGHI $.
  $}

  ${
    bile.1 $e |- a = b $.
    $( Biconditional to "less than or equal to".  (Contributed by NM,
       27-Aug-1997.) $)
    bile $p |- a =< b $=
      ( wo ax-r5 oridm ax-r2 df-le1 ) ABABDBBDBABBCEBFGH $.
  $}

  $( An ortholattice inequality, corresponding to a theorem provable in Hilbert
     space.  Part of Definition 2.1 p. 2092, in M. Pavicic and N. Megill,
     "Quantum and Classical Implicational Algebras with Primitive Implication",
     _Int.  J. of Theor.  Phys_. 37, 2091-2098 (1998).  (Contributed by NM,
     3-Feb-2002.) $)
  qlhoml1a $p |- a =< a ' ' $=
    ( wn ax-a1 bile ) AABBACD $.

  $( An ortholattice inequality, corresponding to a theorem provable in Hilbert
     space.  (Contributed by NM, 3-Feb-2002.) $)
  qlhoml1b $p |- a ' ' =< a $=
    ( wn ax-a1 ax-r1 bile ) ABBZAAFACDE $.

  ${
    lebi.1 $e |- a =< b $.
    lebi.2 $e |- b =< a $.
    $( "Less than or equal to" to biconditional.  (Contributed by NM,
       27-Aug-1997.) $)
    lebi $p |- a = b $=
      ( wo df-le2 ax-r1 ax-a2 ax-r2 ) AABEZBABAEZJKABADFGBAHIABCFI $.
  $}

  $( Anything is less than or equal to 1.  (Contributed by NM, 30-Aug-1997.) $)
  le1 $p |- a =< 1 $=
    ( wt or1 df-le1 ) ABACD $.

  $( 0 is less than or equal to anything.  (Contributed by NM, 30-Aug-1997.) $)
  le0 $p |- 0 =< a $=
    ( wf wo ax-a2 or0 ax-r2 df-le1 ) BABACABCABADAEFG $.

  $( Identity law for "less than or equal to".  (Contributed by NM,
     24-Dec-1998.) $)
  leid $p |- a =< a $=
    ( id bile ) AAABC $.

  ${
    le.1 $e |- a =< b $.
    $( Add disjunct to right of l.e.  (Contributed by NM, 27-Aug-1997.) $)
    ler $p |- a =< ( b v c ) $=
      ( wo ax-a3 ax-r1 df-le2 ax-r5 ax-r2 df-le1 ) ABCEZALEZABEZCEZLOMABCFGNBCA
      BDHIJK $.

    $( Add disjunct to right of l.e.  (Contributed by NM, 11-Nov-1997.) $)
    lerr $p |- a =< ( c v b ) $=
      ( wo ler ax-a2 lbtr ) ABCECBEABCDFBCGH $.

    $( Add conjunct to left of l.e.  (Contributed by NM, 27-Aug-1997.) $)
    lel $p |- ( a ^ c ) =< b $=
      ( wa an32 df2le2 ran ax-r2 df2le1 ) ACEZBKBEABEZCEKACBFLACABDGHIJ $.

    $( Add disjunct to right of both sides.  (Contributed by NM,
       27-Aug-1997.) $)
    leror $p |- ( a v c ) =< ( b v c ) $=
      ( wo orordir ax-r1 df-le2 ax-r5 ax-r2 df-le1 ) ACEZBCEZLMEZABEZCEZMPNABCF
      GOBCABDHIJK $.

    $( Add conjunct to right of both sides.  (Contributed by NM,
       27-Aug-1997.) $)
    leran $p |- ( a ^ c ) =< ( b ^ c ) $=
      ( wa anandir ax-r1 df2le2 ran ax-r2 df2le1 ) ACEZBCEZLMEZABEZCEZLPNABCFGO
      ACABDHIJK $.

    $( Contrapositive for l.e.  (Contributed by NM, 27-Aug-1997.) $)
    lecon $p |- b ' =< a ' $=
      ( wn wa wo ax-a2 oran df-le2 3tr2 con3 df2le1 ) BDZADZMNEZBBAFABFODBBAGBA
      HABCIJKL $.
  $}

  ${
    lecon1.1 $e |- a ' =< b ' $.
    $( Contrapositive for l.e.  (Contributed by NM, 7-Nov-1997.) $)
    lecon1 $p |- b =< a $=
      ( wn lecon ax-a1 le3tr1 ) BDZDADZDBAIHCEBFAFG $.
  $}

  ${
    lecon2.1 $e |- a ' =< b $.
    $( Contrapositive for l.e.  (Contributed by NM, 19-Dec-1998.) $)
    lecon2 $p |- b ' =< a $=
      ( wn ax-a1 lbtr lecon1 ) ABDZADBHDCBEFG $.
  $}

  ${
    lecon3.1 $e |- a =< b ' $.
    $( Contrapositive for l.e.  (Contributed by NM, 19-Dec-1998.) $)
    lecon3 $p |- b =< a ' $=
      ( wn lecon lecon2 lecon1 ) ADZBBDZHAICEFG $.
  $}

  $( L.e. absorption.  (Contributed by NM, 27-Aug-1997.) $)
  leo $p |- a =< ( a v b ) $=
    ( wo anabs df2le1 ) AABCABDE $.

  $( L.e. absorption.  (Contributed by NM, 11-Nov-1997.) $)
  leor $p |- a =< ( b v a ) $=
    ( wo leo ax-a2 lbtr ) AABCBACABDABEF $.

  $( L.e. absorption.  (Contributed by NM, 27-Aug-1997.) $)
  lea $p |- ( a ^ b ) =< a $=
    ( wa wo ax-a2 orabs ax-r2 df-le1 ) ABCZAIADAIDAIAEABFGH $.

  $( L.e. absorption.  (Contributed by NM, 11-Nov-1997.) $)
  lear $p |- ( a ^ b ) =< b $=
    ( wa ancom lea bltr ) ABCBACBABDBAEF $.

  $( L.e. absorption.  (Contributed by NM, 8-Jul-2000.) $)
  leao1 $p |- ( a ^ b ) =< ( a v c ) $=
    ( wa wo lea leo letr ) ABDAACEABFACGH $.

  $( L.e. absorption.  (Contributed by NM, 8-Jul-2000.) $)
  leao2 $p |- ( b ^ a ) =< ( a v c ) $=
    ( wa wo lear leo letr ) BADAACEBAFACGH $.

  $( L.e. absorption.  (Contributed by NM, 8-Jul-2000.) $)
  leao3 $p |- ( a ^ b ) =< ( c v a ) $=
    ( wa wo lea leor letr ) ABDACAEABFACGH $.

  $( L.e. absorption.  (Contributed by NM, 8-Jul-2000.) $)
  leao4 $p |- ( b ^ a ) =< ( c v a ) $=
    ( wa wo lear leor letr ) BADACAEBAFACGH $.

  ${
    lel.1 $e |- a =< b $.
    $( Add disjunct to left of both sides.  (Contributed by NM,
       25-Oct-1997.) $)
    lelor $p |- ( c v a ) =< ( c v b ) $=
      ( wo leror ax-a2 le3tr1 ) ACEBCECAECBEABCDFCAGCBGH $.

    $( Add conjunct to left of both sides.  (Contributed by NM,
       25-Oct-1997.) $)
    lelan $p |- ( c ^ a ) =< ( c ^ b ) $=
      ( wa leran ancom le3tr1 ) ACEBCECAECBEABCDFCAGCBGH $.
  $}

  ${
    le2.1 $e |- a =< b $.
    le2.2 $e |- c =< d $.
    $( Disjunction of 2 l.e.'s.  (Contributed by NM, 25-Oct-1997.) $)
    le2or $p |- ( a v c ) =< ( b v d ) $=
      ( wo leror lelor letr ) ACGBCGBDGABCEHCDBFIJ $.

    $( Conjunction of 2 l.e.'s.  (Contributed by NM, 25-Oct-1997.) $)
    le2an $p |- ( a ^ c ) =< ( b ^ d ) $=
      ( wa leran lelan letr ) ACGBCGBDGABCEHCDBFIJ $.
  $}

  ${
    lel2.1 $e |- a =< b $.
    lel2.2 $e |- c =< b $.
    $( Disjunction of 2 l.e.'s.  (Contributed by NM, 11-Nov-1997.) $)
    lel2or $p |- ( a v c ) =< b $=
      ( wo le2or oridm lbtr ) ACFBBFBABCBDEGBHI $.

    $( Conjunction of 2 l.e.'s.  (Contributed by NM, 11-Nov-1997.) $)
    lel2an $p |- ( a ^ c ) =< b $=
      ( wa le2an anidm lbtr ) ACFBBFBABCBDEGBHI $.
  $}

  ${
    ler2.1 $e |- a =< b $.
    ler2.2 $e |- a =< c $.
    $( Disjunction of 2 l.e.'s.  (Contributed by NM, 11-Nov-1997.) $)
    ler2or $p |- a =< ( b v c ) $=
      ( wo oridm ax-r1 le2or bltr ) AAAFZBCFKAAGHABACDEIJ $.

    $( Conjunction of 2 l.e.'s.  (Contributed by NM, 11-Nov-1997.) $)
    ler2an $p |- a =< ( b ^ c ) $=
      ( wa anidm ax-r1 le2an bltr ) AAAFZBCFKAAGHABACDEIJ $.
  $}

  $( Half of distributive law.  (Contributed by NM, 28-Aug-1997.) $)
  ledi $p |- ( ( a ^ b ) v ( a ^ c ) ) =< ( a ^ ( b v c ) ) $=
    ( wa wo anidm ax-r1 lea le2or oridm lbtr ancom bltr le2an ) ABDZACDZEZQQDZA
    BCEZDRQQFGQAQSQAAEAOAPAABHACHIAJKOBPCOBADBABLBAHMPCADCACLCAHMINM $.

  $( Half of distributive law.  (Contributed by NM, 30-Nov-1998.) $)
  ledir $p |- ( ( b ^ a ) v ( c ^ a ) ) =< ( ( b v c ) ^ a ) $=
    ( wa wo ledi ancom 2or le3tr1 ) ABDZACDZEABCEZDBADZCADZELADABCFMJNKBAGCAGHL
    AGI $.

  $( Half of distributive law.  (Contributed by NM, 28-Aug-1997.) $)
  ledio $p |- ( a v ( b ^ c ) ) =< ( ( a v b ) ^ ( a v c ) ) $=
    ( wa wo anidm ax-r1 leo le2an bltr ax-a2 lbtr le2or oridm ) ABCDZEABEZACEZD
    ZRERARORAAADZRSAAFGAPAQABHACHIJBPCQBBAEPBAHBAKLCCAEQCAHCAKLIMRNL $.

  $( Half of distributive law.  (Contributed by NM, 30-Nov-1998.) $)
  ledior $p |- ( ( b ^ c ) v a ) =< ( ( b v a ) ^ ( c v a ) ) $=
    ( wa wo ledio ax-a2 2an le3tr1 ) ABCDZEABEZACEZDJAEBAEZCAEZDABCFJAGMKNLBAGC
    AGHI $.

  $( Commutation with 0.  Kalmbach 83 p. 20.  (Contributed by NM,
     27-Aug-1997.) $)
  comm0 $p |- a C 0 $=
    ( wf wo wa wn ax-a2 or0 ax-r2 ax-r1 an0 wt df-f con2 lan an1 2or df-c1 ) AB
    ABACZABDZABEZDZCZRARABCABAFAGHIUBRSBUAAAJUAAKDATKABKLMNAOHPIHQ $.

  $( Commutation with 1.  Kalmbach 83 p. 20.  (Contributed by NM,
     27-Aug-1997.) $)
  comm1 $p |- 1 C a $=
    ( wt wn wo wa df-t ancom an1 ax-r2 2or ax-r1 df-c1 ) BABAACZDZBAEZBMEZDZAFQ
    NOAPMOABEABAGAHIPMBEMBMGMHIJKIL $.

  ${
    lecom.1 $e |- a =< b $.
    $( Comparable elements commute.  Beran 84 2.3(iii) p. 40.  (Contributed by
       NM, 30-Aug-1997.) $)
    lecom $p |- a C b $=
      ( wn wa wo orabs ax-r1 df2le2 ax-r5 ax-r2 df-c1 ) ABAAABDZEZFZABEZNFOAAMG
      HAPNPAABCIHJKL $.
  $}

  ${
    bctr.1 $e |- a = b $.
    bctr.2 $e |- b C c $.
    $( Transitive inference.  (Contributed by NM, 30-Aug-1997.) $)
    bctr $p |- a C c $=
      ( wa wn wo df-c2 ran 2or 3tr1 df-c1 ) ACBBCFZBCGZFZHAACFZAOFZHBCEIDQNRPAB
      CDJABODJKLM $.
  $}

  ${
    cbtr.1 $e |- a C b $.
    cbtr.2 $e |- b = c $.
    $( Transitive inference.  (Contributed by NM, 30-Aug-1997.) $)
    cbtr $p |- a C c $=
      ( wa wn wo df-c2 lan ax-r4 2or ax-r2 df-c1 ) ACAABFZABGZFZHACFZACGZFZHABD
      IORQTBCAEJPSABCEKJLMN $.
  $}

  ${
    comcom2.1 $e |- a C b $.
    $( Commutation equivalence.  Kalmbach 83 p. 23.  Does not use OML.
       (Contributed by NM, 27-Aug-1997.) $)
    comcom2 $p |- a C b ' $=
      ( wn wa wo df-c2 ax-a1 lan ax-r5 ax-r2 ax-a2 df-c1 ) ABDZAANDZEZANEZFZQPF
      AABEZQFRABCGSPQBOABHIJKPQLKM $.
  $}

  $( Commutation law.  Does not use OML. (Contributed by NM, 30-Aug-1997.) $)
  comorr $p |- a C ( a v b ) $=
    ( wo leo lecom ) AABCABDE $.

  $( Commutation law.  Does not use OML. (Contributed by NM, 30-Aug-1997.) $)
  coman1 $p |- ( a ^ b ) C a $=
    ( wa lea lecom ) ABCAABDE $.

  $( Commutation law.  Does not use OML. (Contributed by NM, 9-Nov-1997.) $)
  coman2 $p |- ( a ^ b ) C b $=
    ( wa ancom coman1 bctr ) ABCBACBABDBAEF $.

  $( Identity law for commutation.  Does not use OML. (Contributed by NM,
     9-Nov-1997.) $)
  comid $p |- a C a $=
    ( wo comorr oridm cbtr ) AAABAAACADE $.

  ${
    distlem.1 $e |- ( a ^ ( b v c ) ) =< b $.
    $( Distributive law inference (uses OL only).  (Contributed by NM,
       17-Nov-1998.) $)
    distlem $p |- ( a ^ ( b v c ) ) = ( ( a ^ b ) v ( a ^ c ) ) $=
      ( wo wa lea ler2an leo letr ledi lebi ) ABCEZFZABFZACFZEZNOQNABAMGDHOPIJA
      BCKL $.
  $}

  ${
    str.1 $e |- a =< ( b v c ) $.
    str.2 $e |- ( a ^ ( b v c ) ) =< b $.
    $( Strengthening rule.  (Contributed by NM, 18-Nov-1998.) $)
    str $p |- a =< b $=
      ( wo wa id bile ler2an letr ) AABCFZGBAALAAAHIDJEK $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Commutator (ortholattice theorems)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Commutative law for commutator.  (Contributed by NM, 24-Jan-1999.) $)
  cmtrcom $p |- C ( a , b ) = C ( b , a ) $=
    ( wa wn wo wcmtr ancom 2or or4 ax-r2 df-cmtr 3tr1 ) ABCZABDZCZEZADZBCZQNCZE
    ZEZBACZBQCZENACZNQCZEEZABFBAFUAUBUDEZUCUEEZEUFPUGTUHMUBOUDABGANGHRUCSUEQBGQ
    NGHHUBUDUCUEIJABKBAKL $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Weak "orthomodular law" in ortholattices.
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  All theorems here do not require R3 and are true in all ortholattices.

$)

  $( Weak A1.  (Contributed by NM, 27-Sep-1997.) $)
  wa1 $p |- ( a == a ' ' ) = 1 $=
    ( wn ax-a1 bi1 ) AABBACD $.

  $( Weak A2.  (Contributed by NM, 27-Sep-1997.) $)
  wa2 $p |- ( ( a v b ) == ( b v a ) ) = 1 $=
    ( wo ax-a2 bi1 ) ABCBACABDE $.

  $( Weak A3.  (Contributed by NM, 27-Sep-1997.) $)
  wa3 $p |- ( ( ( a v b ) v c ) == ( a v ( b v c ) ) ) = 1 $=
    ( wo ax-a3 bi1 ) ABDCDABCDDABCEF $.

  $( Weak A4.  (Contributed by NM, 27-Sep-1997.) $)
  wa4 $p |- ( ( a v ( b v b ' ) ) == ( b v b ' ) ) = 1 $=
    ( wn wo ax-a4 bi1 ) ABBCDZDGABEF $.

  $( Weak A5.  (Contributed by NM, 27-Sep-1997.) $)
  wa5 $p |- ( ( a v ( a ' v b ' ) ' ) == a ) = 1 $=
    ( wn wo ax-a5 bi1 ) AACBCZDCDAAGEF $.

  $( Weak A6.  (Contributed by NM, 12-Jul-1998.) $)
  wa6 $p |- ( ( a == b ) == ( ( a ' v b ' ) ' v ( a v b ) ' ) )
             = 1 $=
    ( tb wn wo df-b bi1 ) ABCADBDEDABEDEABFG $.

  ${
    wr1.1 $e |- ( a == b ) = 1 $.
    $( Weak R1.  (Contributed by NM, 2-Sep-1997.) $)
    wr1 $p |- ( b == a ) = 1 $=
      ( tb wt bicom ax-r2 ) BADABDEBAFCG $.
  $}

  ${
    wr3.1 $e |- ( 1 == a ) = 1 $.
    $( Weak R3.  (Contributed by NM, 2-Sep-1997.) $)
    wr3 $p |- a = 1 $=
      ( wt tb 1b ax-r1 ax-r2 ) ACADZCHAAEFBG $.
  $}

  ${
    wr4.1 $e |- ( a == b ) = 1 $.
    $( Weak R4.  (Contributed by NM, 2-Sep-1997.) $)
    wr4 $p |- ( a ' == b ' ) = 1 $=
      ( wn tb wt conb ax-r1 ax-r2 ) ADBDEZABEZFKJABGHCI $.
  $}

  $( Absorption law.  (Contributed by NM, 27-Sep-1997.) $)
  wa5b $p |- ( ( a v ( a ^ b ) ) == a ) = 1 $=
    ( wa wo orabs bi1 ) AABCDAABEF $.

  $( Absorption law.  (Contributed by NM, 27-Sep-1997.) $)
  wa5c $p |- ( ( a ^ ( a v b ) ) == a ) = 1 $=
    ( wo wa anabs bi1 ) AABCDAABEF $.

  $( Contraposition law.  (Contributed by NM, 27-Sep-1997.) $)
  wcon $p |- ( ( a == b ) == ( a ' == b ' ) ) = 1 $=
    ( tb wn conb bi1 ) ABCADBDCABEF $.

  $( Commutative law.  (Contributed by NM, 27-Sep-1997.) $)
  wancom $p |- ( ( a ^ b ) == ( b ^ a ) ) = 1 $=
    ( wa ancom bi1 ) ABCBACABDE $.

  $( Associative law.  (Contributed by NM, 27-Sep-1997.) $)
  wanass $p |- ( ( ( a ^ b ) ^ c ) == ( a ^ ( b ^ c ) ) ) = 1 $=
    ( wa anass bi1 ) ABDCDABCDDABCEF $.

  ${
    wwbmp.1 $e |- a = 1 $.
    wwbmp.2 $e |- ( a == b ) = 1 $.
    $( Weak weak equivalential detachment (WBMP).  (Contributed by NM,
       2-Sep-1997.) $)
    wwbmp $p |- b = 1 $=
      ( wt tb rbi ax-r1 ax-r2 wr3 ) BEBFZABFZELKAEBCGHDIJ $.
  $}

  ${
    wwbmpr.1 $e |- b = 1 $.
    wwbmpr.2 $e |- ( a == b ) = 1 $.
    $( Weak weak equivalential detachment (WBMP).  (Contributed by NM,
       24-Sep-1997.) $)
    wwbmpr $p |- a = 1 $=
      ( wr1 wwbmp ) BACABDEF $.
  $}

  ${
    wcon1.1 $e |- ( a ' == b ' ) = 1 $.
    $( Weak contraposition.  (Contributed by NM, 24-Sep-1997.) $)
    wcon1 $p |- ( a == b ) = 1 $=
      ( tb wn wt conb ax-r2 ) ABDAEBEDFABGCH $.
  $}

  ${
    wcon2.1 $e |- ( a == b ' ) = 1 $.
    $( Weak contraposition.  (Contributed by NM, 24-Sep-1997.) $)
    wcon2 $p |- ( a ' == b ) = 1 $=
      ( wn tb wt conb ax-a1 rbi ax-r1 ax-r2 ) ADZBEZABDZEZFMLDZNEZOLBGOQAPNAHIJ
      KCK $.
  $}

  ${
    wcon3.1 $e |- ( a ' == b ) = 1 $.
    $( Weak contraposition.  (Contributed by NM, 24-Sep-1997.) $)
    wcon3 $p |- ( a == b ' ) = 1 $=
      ( wn tb wt ax-a1 ax-r1 lbi ax-r2 wcon1 ) ABDZADZLDZEMBEFNBMBNBGHICJK $.
  $}

  ${
    wlem3.1.1 $e |- ( a v b ) = b $.
    wlem3.1.2 $e |- ( b ' v a ) = 1 $.
    $( Weak analogue to lemma used in proof of Thm. 3.1 of Pavicic 1993.
       (Contributed by NM, 2-Sep-1997.) $)
    wlem3.1 $p |- ( a == b ) = 1 $=
      ( tb wn wo wt wa dfb leoa oran ax-r1 ax-r2 con3 2or ax-a2 ) ABEZBFZAGZHRA
      BIZAFSIZGZTABJUCASGTUAAUBSABBCKUBBUBFZABGZBUEUDABLMCNOPASQNNDN $.
  $}

  $( Theorem structurally similar to orthomodular law but does not require R3.
     (Contributed by NM, 2-Sep-1997.) $)
  woml $p |- ( ( a v ( a ' ^ ( a v b ) ) ) == ( a v b ) ) = 1 $=
    ( wn wo wa omlem1 omlem2 wlem3.1 ) AACABDZEDIABFABGH $.

  ${
    wwoml2.1 $e |- a =< b $.
    $( Weak orthomodular law.  (Contributed by NM, 2-Sep-1997.) $)
    wwoml2 $p |- ( ( a v ( a ' ^ b ) ) == b ) = 1 $=
      ( wn wa wo tb wt df-le2 ax-r1 lan lor rbi lbi woml 3tr2 ) AADZBEZFZABFZGA
      QTEZFZTGSBGHSUBTRUAABTQTBABCIZJKLMTBSUCNABOP $.
  $}

  ${
    wwoml3.1 $e |- a =< b $.
    wwoml3.2 $e |- ( b ^ a ' ) = 0 $.
    $( Weak orthomodular law.  (Contributed by NM, 2-Sep-1997.) $)
    wwoml3 $p |- ( a == b ) = 1 $=
      ( wf wo tb wn wa wt ax-r1 ancom ax-r2 lor rbi or0 wwoml2 3tr2 ) AEFZBGAAH
      ZBIZFZBGABGJSUBBEUAAEBTIZUAUCEDKBTLMNOSABAPOABCQR $.
  $}

  ${
    wwcomd.1 $e |- a ' C b $.
    $( Commutation dual (weak).  Kalmbach 83 p. 23.  (Contributed by NM,
       2-Sep-1997.) $)
    wwcomd $p |- a = ( ( a v b ) ^ ( a v b ' ) ) $=
      ( wo wn wa df-c2 oran ax-a2 anor2 ax-r1 con3 2an ax-r4 3tr1 ax-r2 con1 )
      AABDZABEZDZFZAEZUBBFZUBSFZDZUAEZUBBCGUDUCDUDEZUCEZFZEUEUFUDUCHUCUDIUAUIRU
      GTUHABHTUCUCTEABJKLMNOPQ $.
  $}

  ${
    wwcom3ii.1 $e |- b ' C a $.
    $( Lemma 3(ii) (weak) of Kalmbach 83 p. 23.  (Contributed by NM,
       2-Sep-1997.) $)
    wwcom3ii $p |- ( a ^ ( a ' v b ) ) = ( a ^ b ) $=
      ( wa wn wo wwcomd lan anass ax-r1 ax-a2 anabs ax-r2 2an ) ABDZAAEZBFZDZOA
      BAFZBPFZDZDZRBUAABACGHUBASDZTDZRUDUBASTIJUCATQUCAABFZDASUEABAKHABLMBPKNMM
      J $.
  $}

  ${
    wwfh.1 $e |- b C a $.
    wwfh.2 $e |- c C a $.
    $( Foulis-Holland Theorem (weak).  (Contributed by NM, 3-Sep-1997.) $)
    wwfh1 $p |- ( ( a ^ ( b v c ) ) == ( ( a ^ b ) v ( a ^ c ) ) )
               = 1 $=
      ( wo wa tb wn wf df-a ax-r1 con3 ax-r2 2an ax-a1 bctr wwcom3ii anandi lan
      wt bicom ledi ancom 2or con2 anass 3tr1 an12 oran dff an0 wwoml3 ) ABCFZG
      ZABGZACGZFZHURUOHUAUOURUBURUOABCUCUOURIZGZAUNBIZCIZGZGZGZJUTUNAGZAIZVAFZV
      GVBFZGZGZVEUOVFUSVJAUNUDURVJURVHIZVIIZFZVJIUPVLUQVMABKACKUEVNVJVJVNIVHVIK
      LMNUFOVKUNAVCGZGZVEVKUNAVJGZGVPUNAVJUGVQVOUNAVHGZAVIGZGAVAGZAVBGZGVQVOVRV
      TVSWAAVAVAIZBABWBBPLDQRAVBVBIZCACWCCPLEQROAVHVISAVAVBSUHTNUNAVCUINNVEAJGJ
      VDJAVDUNUNIZGZJVCWDUNVCUNUNVCIBCUJLMTJWEUNUKLNTAULNNUMN $.
  $}

  ${
    wwfh2.1 $e |- a C b $.
    wwfh2.2 $e |- c ' C a $.
    $( Foulis-Holland Theorem (weak).  (Contributed by NM, 3-Sep-1997.) $)
    wwfh2 $p |- ( ( b ^ ( a v c ) ) == ( ( b ^ a ) v ( b ^ c ) ) )
               = 1 $=
      ( wo wa tb wt bicom wn wf con2 ran ax-r2 lan an4 ax-r1 wwcom3ii anass dff
      ledi oran df-a ax-r4 ax-a1 bctr ancom ax-r5 comcom2 an12 3tr1 an0 wwoml3
      ) BACFZGZBAGZBCGZFZHUSUPHIUPUSJUSUPBACUBUPUSKZGZAKZCBURKZGZGZGZLVAVBCGZVD
      GZVFVAVBUOGZVDGZVHVAVBBGZUOVCGZGZVJVAUPBKVBFZVCGZGZVMUTVOUPUSVOUSUQKZVCGZ
      KVOKUQURUCVRVOVQVNVCUQVNBAUDMNUEOMPVPBVNGZVLGVMBUOVNVCQVSVKVLVSBVBGVKBVBV
      BKZABAVTAUFZRDUGSBVBUHONOOVBBUOVCQOVIVGVDVIVBVTCFZGVGUOWBVBAVTCWAUIPVBCCK
      AEUJSONOVBCVDTOVFVBLGLVELVBBCVCGGZURVCGZVELWDWCBCVCTRCBVCUKURUAULPVBUMOOU
      NO $.
  $}

  ${
    wwfh3.1 $e |- b ' C a $.
    wwfh3.2 $e |- c ' C a $.
    $( Foulis-Holland Theorem (weak).  (Contributed by NM, 3-Sep-1997.) $)
    wwfh3 $p |- ( ( a v ( b ^ c ) ) == ( ( a v b ) ^ ( a v c ) ) )
               = 1 $=
      ( wa wo tb wn wt conb oran df-a con2 lan ax-r4 ax-r2 2or 2bi comcom2
      wwfh1 ) ABCFZGZABGZACGZFZHZAIZBIZCIZGZFZUHUIFZUHUJFZGZHZJUGUCIZUFIZHUPUCU
      FKUQULURUOUCULUCUHUBIZFZIULIAUBLUTULUSUKUHUBUKBCMNOPQNUFUOUFUDIZUEIZGZIUO
      IUDUEMVCUOVAUMVBUNUDUMABLNUEUNACLNRPQNSQUHUIUJUIADTUJAETUAQ $.
  $}

  ${
    wwfh4.1 $e |- a ' C b $.
    wwfh4.2 $e |- c C a $.
    $( Foulis-Holland Theorem (weak).  (Contributed by NM, 3-Sep-1997.) $)
    wwfh4 $p |- ( ( b v ( a ^ c ) ) == ( ( b v a ) ^ ( b v c ) ) )
               = 1 $=
      ( wa wo tb wn wt conb oran df-a con2 lan ax-r4 ax-r2 2or 2bi comcom2 bctr
      ax-a1 ax-r1 wwfh2 ) BACFZGZBAGZBCGZFZHZBIZAIZCIZGZFZUKULFZUKUMFZGZHZJUJUF
      IZUIIZHUSUFUIKUTUOVAURUFUOUFUKUEIZFZIUOIBUELVCUOVBUNUKUEUNACMNOPQNUIURUIU
      GIZUHIZGZIURIUGUHMVFURVDUPVEUQUGUPBALNUHUQBCLNRPQNSQULUKUMULBDTUMIZAVGCAC
      VGCUBUCEUATUDQ $.
  $}

  $( Weak OM-like absorption law for ortholattices.  (Contributed by NM,
     8-Nov-1998.) $)
  womao $p |- ( a ' ^ ( a v ( a ' ^ ( a v b ) ) ) ) =
                                ( a ' ^ ( a v b ) ) $=
    ( wn wo wa lea lear leo lel2or letr ler2an leor lebi ) ACZANABDZEZDZEZPRNON
    QFRQONQGAOPABHNOGIJKPNQNOFPALKM $.

  $( Weak OM-like absorption law for ortholattices.  (Contributed by NM,
     8-Nov-1998.) $)
  womaon $p |- ( a ^ ( a ' v ( a ^ ( a ' v b ) ) ) ) =
                                 ( a ^ ( a ' v b ) ) $=
    ( wn wo wa lea lear leo lel2or letr ler2an leor lebi ) AACZANBDZEZDZEZPRAOA
    QFRQOAQGNOPNBHAOGIJKPAQAOFPNLKM $.

  $( Weak OM-like absorption law for ortholattices.  (Contributed by NM,
     8-Nov-1998.) $)
  womaa $p |- ( a ' v ( a ^ ( a ' v ( a ^ b ) ) ) ) =
                                ( a ' v ( a ^ b ) ) $=
    ( wn wa wo leo lear lel2or lea leor ler2an letr lebi ) ACZANABDZEZDZEZPNPQN
    OFAPGHNRONQFOQROAPABIONJKQNJLHM $.

  $( Weak OM-like absorption law for ortholattices.  (Contributed by NM,
     8-Nov-1998.) $)
  womaan $p |- ( a v ( a ' ^ ( a v ( a ' ^ b ) ) ) ) =
                                 ( a v ( a ' ^ b ) ) $=
    ( wn wa wo leo lear lel2or lea leor ler2an letr lebi ) AACZANBDZEZDZEZPAPQA
    OFNPGHAROAQFOQRONPNBIOAJKQAJLHM $.

  $( Absorption law for ortholattices.  (Contributed by NM, 13-Nov-1998.) $)
  anorabs2 $p |- ( a ^ ( b v ( a ^ ( b v c ) ) ) ) =
                                 ( a ^ ( b v c ) ) $=
    ( wo wa lea lear leo lel2or letr ler2an leor lebi ) ABABCDZEZDZEZOQANAPFQPN
    APGBNOBCHANGIJKOAPANFOBLKM $.

  $( Absorption law for ortholattices.  (Contributed by NM, 8-Nov-1998.) $)
  anorabs $p |- ( a ' ^ ( b v ( a ' ^ ( a v b ) ) ) ) =
                                  ( a ' ^ ( a v b ) ) $=
    ( wn wo wa anorabs2 ax-a2 lan lor 3tr1 ) ACZBKBADZEZDZEMKBKABDZEZDZEPKBAFQN
    KPMBOLKABGHZIHRJ $.

  $( Axiom KA2a in Pavicic and Megill, 1998 (Contributed by NM, 9-Nov-1998.) $)
  ska2a $p |- ( ( ( a v c ) == ( b v c ) ) ==
              ( ( c v a ) == ( c v b ) ) ) = 1 $=
    ( wo tb ax-a2 2bi bi1 ) ACDZBCDZECADZCBDZEIKJLACFBCFGH $.

  $( Axiom KA2b in Pavicic and Megill, 1998 (Contributed by NM, 9-Nov-1998.) $)
  ska2b $p |- ( ( ( a v c ) == ( b v c ) ) ==
              ( ( a ' ^ c ' ) ' == ( b ' ^ c ' ) ' ) ) = 1 $=
    ( wo tb wn wa oran 2bi bi1 ) ACDZBCDZEAFCFZGFZBFMGFZEKNLOACHBCHIJ $.

  $( Lemma for KA4 soundness (OR version) - uses OL only.  (Contributed by NM,
     25-Oct-1997.) $)
  ka4lemo $p |- ( ( a v b ) v ( ( a v c ) == ( b v c ) ) ) = 1 $=
    ( wo tb wt le1 wn df-t wa ax-a2 lbtr lelor leror oran con2 ax-r1 ax-r2 bltr
    2an leo ax-a3 ledio le3tr1 dfb anor1 anandir ax-r5 ax-r4 3tr1 lor letr lebi
    ) ABDZACDZBCDZEZDZFURGFUNCDZUSHZDZURUSIVAUNABJZCDZDZUTDZURUSVDUTCVCUNCCVBDZ
    VCCVBUACVBKLMNVEUNVCUTDZDURUNVCUTUBVGUQUNVGUOUPJZUTDZUQVCVHUTVFCADZCBDZJVCV
    HCABUCVBCKUOVJUPVKACKBCKTUDNUQVIUQVHUOHZUPHZJZDVIUOUPUEVNUTVHVNAHZCHZJZBHZV
    PJZJZUTVLVQVMVSUOVQACOPUPVSBCOPTVOVRJZVPJZWAHZCDZHVTUTWACUFWBVTVOVRVPUGQUSW
    DUNWCCABOUHUIUJRUKRQLMSULSUM $.

  $( Lemma for KA4 soundness (AND version) - uses OL only.  (Contributed by NM,
     25-Oct-1997.) $)
  ka4lem $p |- ( ( a ^ b ) ' v ( ( a ^ c ) == ( b ^ c ) ) ) = 1 $=
    ( wa wn tb wo wt df-a con2 2bi conb ax-r1 ax-r2 2or ka4lemo ) ABDZEZACDZBCD
    ZFZGAEZBEZGZUBCEZGZUCUEGZFZGHRUDUAUHQUDABIJUAUFEZUGEZFZUHSUITUJACIBCIKUHUKU
    FUGLMNOUBUCUEPN $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
 Kalmbach axioms (soundness proofs) that are true in all ortholattices
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    sklem.1 $e |- a =< b $.
    $( Soundness lemma.  (Contributed by NM, 30-Aug-1997.) $)
    sklem $p |- ( a ' v b ) = 1 $=
      ( wn wo wt or12 df-t ax-r5 ax-r1 ax-a3 ax-a2 3tr2 ax-r2 df-le2 lor or1 )
      ADZABEZEZBFEZRBEZFTAUBEZUARABGAREZBEZFBEZUCUAUFUEFUDBAHIJARBKFBLMNSBRABCO
      PBQM $.
  $}

  $( Soundness theorem for Kalmbach's quantum propositional logic axiom KA1.
     (Contributed by NM, 30-Aug-1997.) $)
  ska1 $p |- ( a == a ) = 1 $=
    ( biid ) AB $.

  $( Soundness theorem for Kalmbach's quantum propositional logic axiom KA3.
     (Contributed by NM, 30-Aug-1997.) $)
  ska3 $p |- ( ( a == b ) ' v ( a ' == b ' ) ) = 1 $=
    ( wn tb wo wt conb ax-r4 lor ax-a2 df-t 3tr1 ) ACBCDZABDZCZEMMCZEOMEFOPMNMA
    BGHIOMJMKL $.

  $( Soundness theorem for Kalmbach's quantum propositional logic axiom KA5.
     (Contributed by NM, 30-Aug-1997.) $)
  ska5 $p |- ( ( a ^ b ) == ( b ^ a ) ) = 1 $=
    ( wa ancom bi1 ) ABCBACABDE $.

  $( Soundness theorem for Kalmbach's quantum propositional logic axiom KA6.
     (Contributed by NM, 30-Aug-1997.) $)
  ska6 $p |- ( ( a ^ ( b ^ c ) ) == ( ( a ^ b ) ^ c ) ) = 1 $=
    ( wa anass ax-r1 bi1 ) ABCDDZABDCDZIHABCEFG $.

  $( Soundness theorem for Kalmbach's quantum propositional logic axiom KA7.
     (Contributed by NM, 30-Aug-1997.) $)
  ska7 $p |- ( ( a ^ ( a v b ) ) == a ) = 1 $=
    ( wo wa anabs bi1 ) AABCDAABEF $.

  $( Soundness theorem for Kalmbach's quantum propositional logic axiom KA8.
     (Contributed by NM, 30-Aug-1997.) $)
  ska8 $p |- ( ( a ' ^ a ) == ( ( a ' ^ a ) ^ b ) ) = 1 $=
    ( wn wa wf an0 ax-r1 ancom ax-r2 dff ran 3tr2 bi1 ) ACZADZOBDZEEBDZOPEBEDZQ
    REBFGBEHIEANDOAJANHIZEOBSKLM $.

  $( Soundness theorem for Kalmbach's quantum propositional logic axiom KA9.
     (Contributed by NM, 30-Aug-1997.) $)
  ska9 $p |- ( a == a ' ' ) = 1 $=
    ( wn ax-a1 bi1 ) AABBACD $.

  $( Soundness theorem for Kalmbach's quantum propositional logic axiom KA10.
     (Contributed by NM, 30-Aug-1997.) $)
  ska10 $p |- ( ( a v b ) ' == ( a ' ^ b ' ) ) = 1 $=
    ( wo wn wa oran con2 bi1 ) ABCZDADBDEZIJABFGH $.

  $( Soundness theorem for Kalmbach's quantum propositional logic axiom KA11.
     (Contributed by NM, 30-Aug-1997.)  (Revised by NM, 2-Sep-1997.) $)
  ska11 $p |- ( ( a v ( a ' ^ ( a v b ) ) ) == ( a v b ) ) = 1 $=
    ( woml ) ABC $.

  $( Soundness theorem for Kalmbach's quantum propositional logic axiom KA12.
     (Contributed by NM, 30-Aug-1997.) $)
  ska12 $p |- ( ( a == b ) == ( b == a ) ) = 1 $=
    ( tb bicom bi1 ) ABCBACABDE $.

  $( Soundness theorem for Kalmbach's quantum propositional logic axiom KA13.
     (Contributed by NM, 30-Aug-1997.) $)
  ska13 $p |- ( ( a == b ) ' v ( a ' v b ) ) = 1 $=
    ( tb wn wo wa ledio lea letr ancom bltr leror dfb ax-a2 le3tr1 sklem ) ABCZ
    ADZBEZABFZRBDZFEZBREZQSUBTREZUCUBUDTUAEZFUDTRUAGUDUEHITBRTBAFBABJBAHKLIABMR
    BNOP $.

  ${
    skr0.1 $e |- a = 1 $.
    skr0.2 $e |- ( a ' v b ) = 1 $.
    $( Soundness theorem for Kalmbach's quantum propositional logic axiom KR0.
       (Contributed by NM, 30-Aug-1997.) $)
    skr0 $p |- b = 1 $=
      ( wn wo wt wf ax-a2 or0 ax-r1 ax-r4 df-f ax-r2 ax-r5 3tr1 ) BAEZBFZGBHFZH
      BFBRBHISBBJKQHBQGEZHAGCLHTMKNOPDN $.
  $}

  $( Lemma for 2-variable WOML proof.  (Contributed by NM, 11-Nov-1998.) $)
  wlem1 $p |- ( ( a == b ) ' v ( ( a ->1 b ) ^ ( b ->1 a ) ) ) = 1 $=
    ( tb wn wi1 wa wo wt le1 df-t ax-a2 ax-r2 dfb ledio df-i1 ancom ax-r5 ax-r1
    2an bltr lbtr lelor lebi ) ABCZDZABEZBAEZFZGZHUIIHUEUDGZUIHUDUEGUJUDJUDUEKL
    UDUHUEUDABFZADZBDZFGZUHABMUNUKULGZUKUMGZFZUHUKULUMNUHUQUFUOUGUPUFULUKGUOABO
    ULUKKLUGUMBAFZGZUPBAOUSURUMGUPUMURKURUKUMBAPQLLSRUATUBTUC $.

  $( Soundness theorem for Kalmbach's quantum propositional logic axiom KA15.
     (Contributed by NM, 2-Nov-1997.) $)
  ska15 $p |- ( ( a ->3 b ) ' v ( a ' v b ) ) = 1 $=
    ( wi3 wn wo wa df-i3 ax-a2 lea lear le2or bltr oridm lbtr sklem ) ABCZADZBE
    ZPQBFZQBDZFZEZARFZEZRABGUDRRERUBRUCRUBUASERSUAHUAQSBQTIQBJKLARJKRMNLO $.

  ${
    skmp3.1 $e |- a = 1 $.
    skmp3.2 $e |- ( a ->3 b ) = 1 $.
    $( Soundness proof for KMP3.  (Contributed by NM, 2-Nov-1997.) $)
    skmp3 $p |- b = 1 $=
      ( wi3 wn wo ska15 skr0 ) ABCABEAFBGDABHII $.
  $}

  ${
    lei3.1 $e |- a =< b $.
    $( L.e. to Kalmbach implication.  (Contributed by NM, 3-Nov-1997.) $)
    lei3 $p |- ( a ->3 b ) = 1 $=
      ( wn wa wo wi3 wt ax-a3 ax-a2 ancom lecon df2le2 ax-r2 sklem lan an1 3tr1
      2or anor2 con2 lor df-i3 df-t ) ADZBEZUEBDZEZFAUEBFZEZFZUFUFDZFZABGHUKUFU
      HUJFZFUMUFUHUJIUNULUFUGAFAUGFZUNULUGAJUHUGUJAUHUGUEEUGUEUGKUGUEABCLMNUJAH
      EAUIHAABCOPAQNSUFUOABTUARUBNABUCUFUDR $.
  $}

  $( E2 - OL theorem proved by EQP (Contributed by NM, 14-Nov-1998.) $)
  mccune2 $p |- ( a v ( ( a ' ^ ( ( a v b ' ) ^ ( a v b ) ) ) v (
                a ' ^ ( ( a ' ^ b ) v ( a ' ^ b ' ) ) ) ) ) = 1 $=
    ( wn wo wa wt ax-a3 ax-r1 anor2 lear lel2or id bile ler2an lebi anor3 oran3
    lea 2or ax-r2 ax-a2 lor df-t 3tr1 ) AABCZDZABDZEZCZAUIDZCZDZDZUJUKDZAACZUHE
    ZUOUOBEZUOUEEZDZEZDZDFUNUMAUIUKGHVAULAVAUKUIDULUPUKUTUIAUHIUTUSUIUTUSUOUSJU
    SUOUSUQUOURUOBRUOUERKUSUSUSLMNOUSUFCZUGCZDUIUQVBURVCABIABPSUFUGQTTSUKUIUATU
    BUJUCUD $.

  $( E3 - OL theorem proved by EQP (Contributed by NM, 14-Nov-1998.) $)
  mccune3 $p |- ( ( ( ( a ' ^ b ) v ( a ' ^ b ' ) ) v ( a ^ ( a '
                v b ) ) ) ' v ( a ' v b ) ) = 1 $=
    ( wn wa wo wi3 wt df-i3 ax-r1 ax-r4 ax-r5 ska15 ax-r2 ) ACZBDNBCDEANBEZDEZC
    ZOEABFZCZOEGQSOPRRPABHIJKABLM $.

  $( Equivalence for Kalmbach implication.  (Contributed by NM, 9-Nov-1997.) $)
  i3n1 $p |- ( a ' ->3 b ' ) = ( ( ( a ^ b ' ) v ( a ^ b ) ) v
                ( a ' ^ ( a v b ' ) ) ) $=
    ( wn wi3 wa wo df-i3 ax-a1 ran 2an 2or ax-r5 lan ax-r1 ax-r2 ) ACZBCZDPCZQE
    ZRQCZEZFZPRQFZEZFZAQEZABEZFZPAQFZEZFZPQGUKUEUHUBUJUDUFSUGUAARQAHZIARBTULBHJ
    KUIUCPARQULLMKNO $.

  $( Equivalence for Kalmbach implication.  (Contributed by NM, 9-Nov-1997.) $)
  ni31 $p |- ( a ->3 b ) ' = ( ( ( a v b ' ) ^ ( a v b ) ) ^
                ( a ' v ( a ^ b ' ) ) ) $=
    ( wi3 wn wo wa df-i3 oran anor2 con2 ax-r1 2an ax-r4 ax-r2 df-a anor1 lor )
    ABCZABDZEZABEZFZADZASFZEZFZRUCBFZUCSFZEZAUCBEZFZEZUFDZABGULUIDZUKDZFZDUMUIU
    KHUPUFUNUBUOUEUIUBUIUGDZUHDZFZDUBDUGUHHUSUBUQTURUAUGTABIJUAURABHKLMNJUKUEUK
    UCUJDZEZDUEDAUJOVAUEUTUDUCUDUTABPKQMNJLMNNJ $.

  $( Identity for Kalmbach implication.  (Contributed by NM, 2-Nov-1997.) $)
  i3id $p |- ( a ->3 a ) = 1 $=
    ( wn wa wo wi3 wt wf ancom dff ax-r1 ax-r2 anidm 2or ax-a2 or0 df-t lan an1
    df-i3 3tr1 ) ABZACZUAUACZDZAUAADZCZDZAUADZAAEFUGUEUHUDUAUFAUDUAGDZUAUDGUADU
    IUBGUCUAUBAUACZGUAAHGUJAIJKUALMGUANKUAOKUFAFCAUEFAUEUHFUAANZFUHAPZJKQARKMUK
    KAASULT $.

  ${
    li3.1 $e |- a = b $.
    $( Introduce Kalmbach implication to the left.  (Contributed by NM,
       2-Nov-1997.) $)
    li3 $p |- ( c ->3 a ) = ( c ->3 b ) $=
      ( wn wa wo wi3 lan ax-r4 2or lor df-i3 3tr1 ) CEZAFZOAEZFZGZCOAGZFZGOBFZO
      BEZFZGZCOBGZFZGCAHCBHSUEUAUGPUBRUDABODIQUCOABDJIKTUFCABODLIKCAMCBMN $.
  $}

  ${
    ri3.1 $e |- a = b $.
    $( Introduce Kalmbach implication to the right.  (Contributed by NM,
       2-Nov-1997.) $)
    ri3 $p |- ( a ->3 c ) = ( b ->3 c ) $=
      ( wn wa wo wi3 ax-r4 ran 2or ax-r5 2an df-i3 3tr1 ) AEZCFZPCEZFZGZAPCGZFZ
      GBEZCFZUCRFZGZBUCCGZFZGACHBCHTUFUBUHQUDSUEPUCCABDIZJPUCRUIJKABUAUGDPUCCUI
      LMKACNBCNO $.
  $}

  ${
    2i3.1 $e |- a = b $.
    2i3.2 $e |- c = d $.
    $( Join both sides with Kalmbach implication.  (Contributed by NM,
       2-Nov-1997.) $)
    2i3 $p |- ( a ->3 c ) = ( b ->3 d ) $=
      ( wi3 li3 ri3 ax-r2 ) ACGADGBDGCDAFHABDEIJ $.
  $}

  ${
    ud1lem0a.1 $e |- a = b $.
    $( Introduce ` ->1 ` to the left.  (Contributed by NM, 23-Nov-1997.) $)
    ud1lem0a $p |- ( c ->1 a ) = ( c ->1 b ) $=
      ( wn wa wo wi1 lan lor df-i1 3tr1 ) CEZCAFZGMCBFZGCAHCBHNOMABCDIJCAKCBKL
      $.

    $( Introduce ` ->1 ` to the right.  (Contributed by NM, 23-Nov-1997.) $)
    ud1lem0b $p |- ( a ->1 c ) = ( b ->1 c ) $=
      ( wn wa wo wi1 ax-r4 ran 2or df-i1 3tr1 ) AEZACFZGBEZBCFZGACHBCHNPOQABDIA
      BCDJKACLBCLM $.
  $}

  ${
    ud1lem0ab.1 $e |- a = b $.
    ud1lem0ab.2 $e |- c = d $.
    $( Join both sides of hypotheses with ` ->1 ` .  (Contributed by NM,
       19-Dec-1998.) $)
    ud1lem0ab $p |- ( a ->1 c ) = ( b ->1 d ) $=
      ( wi1 ud1lem0b ud1lem0a ax-r2 ) ACGBCGBDGABCEHCDBFIJ $.
  $}

  ${
    ud2lem0a.1 $e |- a = b $.
    $( Introduce ` ->2 ` to the left.  (Contributed by NM, 23-Nov-1997.) $)
    ud2lem0a $p |- ( c ->2 a ) = ( c ->2 b ) $=
      ( wn wa wo wi2 ax-r4 lan 2or df-i2 3tr1 ) ACEZAEZFZGBNBEZFZGCAHCBHABPRDOQ
      NABDIJKCALCBLM $.

    $( Introduce ` ->2 ` to the right.  (Contributed by NM, 23-Nov-1997.) $)
    ud2lem0b $p |- ( a ->2 c ) = ( b ->2 c ) $=
      ( wn wa wo wi2 ax-r4 ran lor df-i2 3tr1 ) CAEZCEZFZGCBEZOFZGACHBCHPRCNQOA
      BDIJKACLBCLM $.
  $}

  ${
    ud3lem0a.1 $e |- a = b $.
    $( Introduce Kalmbach implication to the left.  (Contributed by NM,
       23-Nov-1997.) $)
    ud3lem0a $p |- ( c ->3 a ) = ( c ->3 b ) $=
      ( li3 ) ABCDE $.

    $( Introduce Kalmbach implication to the right.  (Contributed by NM,
       23-Nov-1997.) $)
    ud3lem0b $p |- ( a ->3 c ) = ( b ->3 c ) $=
      ( ri3 ) ABCDE $.
  $}

  ${
    ud4lem0a.1 $e |- a = b $.
    $( Introduce ` ->4 ` to the left.  (Contributed by NM, 23-Nov-1997.) $)
    ud4lem0a $p |- ( c ->4 a ) = ( c ->4 b ) $=
      ( wa wn wo wi4 lan 2or lor ax-r4 2an df-i4 3tr1 ) CAEZCFZAEZGZQAGZAFZEZGC
      BEZQBEZGZQBGZBFZEZGCAHCBHSUEUBUHPUCRUDABCDIABQDIJTUFUAUGABQDKABDLMJCANCBN
      O $.

    $( Introduce ` ->4 ` to the right.  (Contributed by NM, 23-Nov-1997.) $)
    ud4lem0b $p |- ( a ->4 c ) = ( b ->4 c ) $=
      ( wa wn wo wi4 ran ax-r4 2or ax-r5 df-i4 3tr1 ) ACEZAFZCEZGZPCGZCFZEZGBCE
      ZBFZCEZGZUCCGZTEZGACHBCHRUEUAUGOUBQUDABCDIPUCCABDJZIKSUFTPUCCUHLIKACMBCMN
      $.
  $}

  ${
    ud5lem0a.1 $e |- a = b $.
    $( Introduce ` ->5 ` to the left.  (Contributed by NM, 23-Nov-1997.) $)
    ud5lem0a $p |- ( c ->5 a ) = ( c ->5 b ) $=
      ( wa wn wo wi5 lan 2or ax-r4 df-i5 3tr1 ) CAEZCFZAEZGZOAFZEZGCBEZOBEZGZOB
      FZEZGCAHCBHQUBSUDNTPUAABCDIABODIJRUCOABDKIJCALCBLM $.

    $( Introduce ` ->5 ` to the right.  (Contributed by NM, 23-Nov-1997.) $)
    ud5lem0b $p |- ( a ->5 c ) = ( b ->5 c ) $=
      ( wa wn wo wi5 ran ax-r4 2or df-i5 3tr1 ) ACEZAFZCEZGZOCFZEZGBCEZBFZCEZGZ
      UAREZGACHBCHQUCSUDNTPUBABCDIOUACABDJZIKOUARUEIKACLBCLM $.
  $}

  $( Correspondence between Sasaki and Dishkant conditionals.  (Contributed by
     NM, 25-Nov-1998.) $)
  i1i2 $p |- ( a ->1 b ) = ( b ' ->2 a ' ) $=
    ( wn wa wo wi1 wi2 ax-a1 2an ancom ax-r2 lor df-i1 df-i2 3tr1 ) ACZABDZEPBC
    ZCZPCZDZEABFRPGQUAPQTSDUAATBSAHBHITSJKLABMRPNO $.

  $( Correspondence between Sasaki and Dishkant conditionals.  (Contributed by
     NM, 7-Feb-1999.) $)
  i2i1 $p |- ( a ->2 b ) = ( b ' ->1 a ' ) $=
    ( wn wi2 wi1 ax-a1 ud2lem0b ud2lem0a i1i2 3tr1 ) ABCZCZDACZCZLDABDKMEANLAFG
    BLABFHKMIJ $.

  $( Correspondence between Sasaki and Dishkant conditionals.  (Contributed by
     NM, 28-Feb-1999.) $)
  i1i2con1 $p |- ( a ->1 b ' ) = ( b ->2 a ' ) $=
    ( wn wi1 wi2 i1i2 ax-a1 ax-r1 ud2lem0b ax-r2 ) ABCZDKCZACZEBMEAKFLBMBLBGHIJ
    $.

  $( Correspondence between Sasaki and Dishkant conditionals.  (Contributed by
     NM, 28-Feb-1999.) $)
  i1i2con2 $p |- ( a ' ->1 b ) = ( b ' ->2 a ) $=
    ( wn wi1 wi2 i1i2 ax-a1 ax-r1 ud2lem0a ax-r2 ) ACZBDBCZKCZELAEKBFMALAMAGHIJ
    $.

  $( Correspondence between Kalmbach and non-tollens conditionals.
     (Contributed by NM, 7-Feb-1999.) $)
  i3i4 $p |- ( a ->3 b ) = ( b ' ->4 a ' ) $=
    ( wn wa wi3 wi4 ax-a2 ancom ax-a1 ran ax-r2 2or ax-r5 2an df-i3 df-i4 3tr1
    wo ) ACZBDZSBCZDZRZASBRZDZRUASDZUACZSDZRZUGSRZSCZDZRABEUASFUCUIUEULUCUBTRUI
    TUBGUBUFTUHSUAHTBSDUHSBHBUGSBIZJKLKUEUDADULAUDHUDUJAUKUDBSRUJSBGBUGSUMMKAIN
    KLABOUASPQ $.

  $( Correspondence between Kalmbach and non-tollens conditionals.
     (Contributed by NM, 7-Feb-1999.) $)
  i4i3 $p |- ( a ->4 b ) = ( b ' ->3 a ' ) $=
    ( wi4 wn wi3 ax-a1 ud4lem0a ud4lem0b ax-r2 i3i4 ax-r1 ) ABCZADZDZBDZDZCZOME
    ZLAPCQBPABFGANPAFHIRQOMJKI $.

  $( Converse of ` ->5 ` .  (Contributed by NM, 7-Feb-1999.) $)
  i5con $p |- ( a ->5 b ) = ( b ' ->5 a ' ) $=
    ( wa wn wo wi5 ancom ax-a2 ax-a1 ran ax-r2 2an 2or ax-a3 3tr1 df-i5 ) ABCZA
    DZBCZEZRBDZCZEZUARCZUADZRCZEUERDZCZEZABFUARFUBTEUDUFUHEZEUCUIUBUDTUJRUAGTSQ
    EUJQSHSUFQUHSBRCUFRBGBUERBIZJKQBACUHABGBUEAUGUKAILKMKMTUBHUDUFUHNOABPUARPO
    $.

  $( Antecedent of 0 on Sasaki conditional.  (Contributed by NM,
     24-Dec-1998.) $)
  0i1 $p |- ( 0 ->1 a ) = 1 $=
    ( wf wi1 wn wa wo wt df-i1 ax-a2 df-f con2 lor ax-r2 or1 3tr ) BACBDZBAEZFZ
    QGFZGBAHRQPFSPQIPGQBGJKLMQNO $.

  $( Antecedent of 1 on Sasaki conditional.  (Contributed by NM,
     24-Dec-1998.) $)
  1i1 $p |- ( 1 ->1 a ) = a $=
    ( wt wi1 wn wa wo df-i1 wf df-f ax-r1 ancom an1 ax-r2 2or ax-a2 or0 ) BACBD
    ZBAEZFZABAGSHAFZAQHRAHQIJRABEABAKALMNTAHFAHAOAPMMM $.

  $( Identity law for Sasaki conditional.  (Contributed by NM, 25-Dec-1998.) $)
  i1id $p |- ( a ->1 a ) = 1 $=
    ( wi1 wn wa wo wt df-i1 ax-a2 anidm lor df-t 3tr1 ax-r2 ) AABACZAADZEZFAAGN
    AEANEPFNAHOANAIJAKLM $.

  $( Identity law for Dishkant conditional.  (Contributed by NM,
     26-Jun-2003.) $)
  i2id $p |- ( a ->2 a ) = 1 $=
    ( wi2 wn wa wo wt df-i2 anidm lor df-t ax-r1 ax-r2 ) AABAACZMDZEZFAAGOAMEZF
    NMAMHIFPAJKLL $.

  $( Lemma for unified disjunction.  (Contributed by NM, 23-Nov-1997.) $)
  ud1lem0c $p |- ( a ->1 b ) ' = ( a ^ ( a ' v b ' ) ) $=
    ( wi1 wn wo wa df-i1 df-a ax-r1 lor ax-r4 ax-r2 con3 con2 ) ABCZAADZBDEZFZO
    PABFZEZRDABGTRRTDZRPQDZEZDUAAQHUCTUBSPSUBABHIJKLIMLN $.

  $( Lemma for unified disjunction.  (Contributed by NM, 23-Nov-1997.) $)
  ud2lem0c $p |- ( a ->2 b ) ' = ( b ' ^ ( a v b ) ) $=
    ( wi2 wn wo wa df-i2 oran ax-r1 lan ax-r4 ax-r2 con2 ) ABCZBDZABEZFZNBADOFZ
    EZQDZABGSORDZFZDTBRHUBQUAPOPUAABHIJKLLM $.

  $( Lemma for unified disjunction.  (Contributed by NM, 22-Nov-1997.) $)
  ud3lem0c $p |- ( a ->3 b ) ' = ( ( ( a v b ' ) ^ ( a v b ) ) ^
                ( a ' v ( a ^ b ' ) ) ) $=
    ( ni31 ) ABC $.

  $( Lemma for unified disjunction.  (Contributed by NM, 23-Nov-1997.) $)
  ud4lem0c $p |- ( a ->4 b ) ' = ( ( ( a ' v b ' ) ^ ( a v b ' ) ) ^
                ( ( a ^ b ' ) v b ) ) $=
    ( wi4 wn wo wa df-i4 oran df-a con2 anor2 2an ax-r4 ax-r2 anor1 ax-r1 ax-r5
    ) ABCZADZBDZEZATEZFZATFZBEZFZRABFZSBFZEZSBEZTFZEZUFDZABGULUIDZUKDZFZDUMUIUK
    HUPUFUNUCUOUEUIUCUIUGDZUHDZFZDUCDUGUHHUSUCUQUAURUBUGUAABIJUHUBABKJLMNJUKUEU
    KUJDZBEZDUEDUJBOVAUEUTUDBUDUTABOPQMNJLMNNJ $.

  $( Lemma for unified disjunction.  (Contributed by NM, 23-Nov-1997.) $)
  ud5lem0c $p |- ( a ->5 b ) ' = ( ( ( a ' v b ' ) ^ ( a v b ' ) ) ^
                ( a v b ) ) $=
    ( wi5 wn wo wa df-i5 oran df-a con2 anor2 2an ax-r4 ax-r2 ax-r1 ) ABCZADZBD
    ZEZAREZFZABEZFZPABFZQBFZEZQRFZEZUCDZABGUHUFDZUGDZFZDUIUFUGHULUCUJUAUKUBUFUA
    UFUDDZUEDZFZDUADUDUEHUOUAUMSUNTUDSABIJUETABKJLMNJUBUKABHOLMNNJ $.

  $( Pavicic binary logic ax-a1 analog.  (Contributed by NM, 5-Nov-1997.) $)
  bina1 $p |- ( a ->3 a ' ' ) = 1 $=
    ( wi3 wn i3id ax-a1 li3 bi1 wwbmp ) AABZAACCZBZADIKAJAAEFGH $.

  $( Pavicic binary logic ax-a2 analog.  (Contributed by NM, 5-Nov-1997.) $)
  bina2 $p |- ( a ' ' ->3 a ) = 1 $=
    ( wi3 wn i3id ax-a1 ri3 bi1 wwbmp ) AABZACCZABZADIKAJAAEFGH $.

  $( Pavicic binary logic ax-a3 analog.  (Contributed by NM, 5-Nov-1997.) $)
  bina3 $p |- ( a ->3 ( a v b ) ) = 1 $=
    ( wo leo lei3 ) AABCABDE $.

  $( Pavicic binary logic ax-a4 analog.  (Contributed by NM, 5-Nov-1997.) $)
  bina4 $p |- ( b ->3 ( a v b ) ) = 1 $=
    ( wo leo ax-a2 lbtr lei3 ) BABCZBBACHBADBAEFG $.

  $( Pavicic binary logic ax-a5 analog.  (Contributed by NM, 5-Nov-1997.) $)
  bina5 $p |- ( b ->3 ( a v a ' ) ) = 1 $=
    ( wn wo wt le1 df-t lbtr lei3 ) BAACDZBEJBFAGHI $.

  ${
    wql1lem.1 $e |- ( a ->1 b ) = 1 $.
    $( Classical implication inferred from Sakaki implication.  (Contributed by
       NM, 5-Dec-1998.) $)
    wql1lem $p |- ( a ' v b ) = 1 $=
      ( wn wo wt le1 wi1 ax-r1 wa df-i1 lear lelor bltr lebi ) ADZBEZFQGFABHZQR
      FCIRPABJZEQABKSBPABLMNNO $.
  $}

  ${
    wql2lem.1 $e |- ( a ->2 b ) = 1 $.
    $( Classical implication inferred from Dishkant implication.  (Contributed
       by NM, 6-Dec-1998.) $)
    wql2lem $p |- ( a ' v b ) = 1 $=
      ( wn wo wt le1 wa wi2 df-i2 ax-a2 3tr2 lea leror bltr lebi ) ADZBEZFRGFQB
      DZHZBEZRABIBTEFUAABJCBTKLTQBQSMNOP $.
  $}

  ${
    wql2lem2.1 $e |- ( ( a v c ) ->2 ( b v c ) ) = 1 $.
    $( Lemma for ` ->2 ` WQL axiom.  (Contributed by NM, 6-Dec-1998.) $)
    wql2lem2 $p |- ( ( a v ( b v c ) ) ' v ( b v c ) ) = 1 $=
      ( wo wn wi2 wt df-i2 anor3 ax-a3 ax-r1 orordir ax-r2 ax-r4 lor ax-a2 3tr
      wa ) ABCEZEZFZTEZACEZTGZHUEUCUETUDFTFSZETUBEUCUDTIUFUBTUFUDTEZFZUBUDTJUBU
      HUAUGUAABECEZUGUIUAABCKLABCMNOLNPTUBQRLDN $.
  $}

  ${
    wql2lem3.1 $e |- ( a ->2 b ) = 1 $.
    $( Lemma for ` ->2 ` WQL axiom.  (Contributed by NM, 6-Dec-1998.) $)
    wql2lem3 $p |- ( ( a ^ b ' ) ->2 a ' ) = 1 $=
      ( wn wa wi2 wo wt df-i2 oran2 ax-r1 ran ancom lor wql2lem omlem2 skr0 3tr
      ax-r2 ) ABDEZADZFUATDZUADZEZGUAUCUABGZEZGZHTUAIUDUFUAUDUEUCEUFUBUEUCUEUBA
      BJKLUEUCMSNUEUGABCOUABPQR $.
  $}

  ${
    wql2lem4.1 $e |- ( ( ( a ^ b ' ) v ( a ^ b ) ) ->2
                     ( a ' v ( a ^ b ) ) ) = 1 $.
    wql2lem4.2 $e |- ( ( a ->1 b ) v ( a ^ b ' ) ) = 1 $.
    $( Lemma for ` ->2 ` WQL axiom.  (Contributed by NM, 6-Dec-1998.) $)
    wql2lem4 $p |- ( a ->1 b ) = 1 $=
      ( wi1 wn wa wo wt df-i1 id ax-a2 ax-r5 ax-r1 3tr wql2lem2 skr0 ) ABEZAFZA
      BGZHZUAIABJZUAKABFGZUAHZUAUDUAUCHZRUCHZIUCUALUFUERUAUCUBMNDOUCSTCPQO $.
  $}

  ${
    wql2lem5.1 $e |- ( a ->2 b ) = 1 $.
    $( Lemma for ` ->2 ` WQL axiom.  (Contributed by NM, 6-Dec-1998.) $)
    wql2lem5 $p |- ( ( b ' ^ ( a v b ) ) ->2 a ' ) = 1 $=
      ( wn wo wa wi2 wt anor3 oran3 ud2lem0c ax-r5 ran ancom an1 3tr ax-r4 3tr2
      ax-r2 lor df-i2 df-t 3tr1 ) ADZBDABEFZDUDDZFZEUDUFEUEUDGHUGUFUDUGUEUDEZDU
      FUEUDIUHUDABGZDZUDEUIAFZDUHUDUIAJUJUEUDABKLUKAUKHAFAHFAUIHACMHANAOPQRQSTU
      EUDUAUDUBUC $.
  $}

  ${
    wql1.1 $e |- ( a ->1 b ) = 1 $.
    wql1.2 $e |- ( ( a v c ) ->1 ( b v c ) ) = 1 $.
    wql1.3 $e |- c = b $.
    $( The 2nd hypothesis is the first ` ->1 ` WQL axiom.  We show it implies
       the WOM law.  (Contributed by NM, 5-Dec-1998.) $)
    wql1 $p |- ( a ->2 b ) = 1 $=
      ( wi2 wn wa wo wt df-i2 anor3 lor ax-a2 wi1 oridm ax-r2 ud1lem0a ax-r1
      ud1lem0b 3tr2 wql1lem 3tr ) ABGBAHBHIZJBABJZHZJZKABLUEUGBABMNUHUGBJKBUGOU
      FBACJZBPZUIBCJZPZUFBPKULUJUKBUIUKBBJBCBBFNBQRSTUIUFBCBAFNUAEUBUCRUD $.
  $}

  ${
    oaidlem1.1 $e |- ( a ^ b ) =< c $.
    $( Lemma for OA identity-like law.  (Contributed by NM, 22-Jan-1999.) $)
    oaidlem1 $p |- ( a ' v ( b ->1 c ) ) = 1 $=
      ( wn wi1 wo wa df-i1 lor oran3 ax-r5 ax-a3 lear ler2an sklem 3tr2 ax-r2
      wt ) AEZBCFZGTBEZBCHZGZGZSUAUDTBCIJTUBGZUCGABHZEZUCGUESUFUHUCABKLTUBUCMUG
      UCUGBCABNDOPQR $.
  $}

  ${
    womle2a.1 $e |- ( a ^ ( a ->2 b ) ) =<
                   ( ( a ->2 b ) ' v ( a ->1 b ) ) $.
    $( An equivalent to the WOM law.  (Contributed by NM, 24-Jan-1999.) $)
    womle2a $p |- ( ( a ->2 b ) ' v ( a ->1 b ) ) = 1 $=
      ( wi2 wn wi1 wo wa wt or4 oridm df-i1 ax-r5 or32 3tr1 ax-r2 2or ax-a2 lor
      oran3 3tr2 le1 df-t leror bltr lebi ) ABDZEZABFZGZUJAUGHZEZGZIUHUHGZUIAEZ
      GZGUJUHUOGZGUJUMUHUHUIUOJUNUHUPUIUHKUPUOABHZGZUOGZUIUIUSUOABLZMUOUOGZURGU
      SUTUIVBUOURUOKMUOURUONVAOPQUQULUJUQUOUHGULUHUORAUGTPSUAUMIUMUBIUKULGUMUKU
      CUKUJULCUDUEUFP $.
  $}

  ${
    womle2b.1 $e |- ( ( a ->2 b ) ' v ( a ->1 b ) ) = 1 $.
    $( An equivalent to the WOM law.  (Contributed by NM, 24-Jan-1999.) $)
    womle2b $p |- ( a ^ ( a ->2 b ) ) =<
                   ( ( a ->2 b ) ' v ( a ->1 b ) ) $=
      ( wi2 wa wt wn wi1 wo le1 ax-r1 lbtr ) AABDZEZFMGABHIZNJOFCKL $.
  $}

  ${
    womle3b.1 $e |- ( ( a ->1 b ) ' v ( a ->2 b ) ) = 1 $.
    $( Implied by the WOM law.  (Contributed by NM, 27-Jan-1999.) $)
    womle3b $p |- ( a ^ ( a ->1 b ) ) =<
                   ( ( a ->1 b ) ' v ( a ->2 b ) ) $=
      ( wi1 wa wt wn wi2 wo le1 ax-r1 lbtr ) AABDZEZFMGABHIZNJOFCKL $.
  $}

  ${
    womle.1 $e |- ( a ^ ( a ->1 b ) ) = ( a ^ ( a ->2 b ) ) $.
    $( An equality implying the WOM law.  (Contributed by NM, 24-Jan-1999.) $)
    womle $p |- ( ( a ->2 b ) ' v ( a ->1 b ) ) = 1 $=
      ( wi2 wa wi1 wn wo ax-r1 lear bltr leor letr womle2a ) ABAABDZEZABFZOGZQH
      PAQEZQSPCIAQJKQRLMN $.
  $}

  $( Lemma for "Non-Orthomodular Models..." paper.  (Contributed by NM,
     7-Feb-1999.) $)
  nomb41 $p |- ( a ==4 b ) = ( b ==1 a ) $=
    ( wn wo wa wid4 wid1 ax-a2 ancom lor 2an df-id4 df-id1 3tr1 ) ACZBDZBCZABEZ
    DZEBODZQBAEZDZEABFBAGPTSUBOBHRUAQABIJKABLBAMN $.

  $( Lemma for "Non-Orthomodular Models..." paper.  (Contributed by NM,
     7-Feb-1999.) $)
  nomb32 $p |- ( a ==3 b ) = ( b ==2 a ) $=
    ( wn wo wa wid3 wid2 ax-a2 ancom lor 2an df-id3 df-id2 3tr1 ) ACZBDZAOBCZEZ
    DZEBODZAQOEZDZEABFBAGPTSUBOBHRUAAOQIJKABLBAMN $.

  $( Lemma for "Non-Orthomodular Models..." paper.  (Contributed by NM,
     7-Feb-1999.) $)
  nomcon0 $p |- ( a ==0 b ) = ( b ' ==0 a ' ) $=
    ( wn wo wa wid0 ax-a2 ax-a1 ax-r5 ax-r2 2an df-id0 3tr1 ) ACZBDZBCZADZEPCZN
    DZNCZPDZEABFPNFOSQUAOBNDSNBGBRNBHIJQAPDUAPAGATPAHIJKABLPNLM $.

  $( Lemma for "Non-Orthomodular Models..." paper.  (Contributed by NM,
     7-Feb-1999.) $)
  nomcon1 $p |- ( a ==1 b ) = ( b ' ==2 a ' ) $=
    ( wn wo wa wid1 wid2 ax-a2 ax-a1 lor ax-r2 ancom 2an df-id1 df-id2 3tr1 ) A
    BCZDZACZABEZDZEQSCZDZSQCZUBEZDZEABFQSGRUCUAUFRQADUCAQHAUBQAIZJKTUESTBAEUEAB
    LBUDAUBBIUGMKJMABNQSOP $.

  $( Lemma for "Non-Orthomodular Models..." paper.  (Contributed by NM,
     7-Feb-1999.) $)
  nomcon2 $p |- ( a ==2 b ) = ( b ' ==1 a ' ) $=
    ( wn wo wa wid2 wid1 ax-a2 ax-a1 lor ax-r2 ancom 2or 2an df-id2 df-id1 3tr1
    ) ABCZDZBACZREZDZERTCZDZRCZRTEZDZEABFRTGSUDUBUGSRADUDARHAUCRAIJKBUEUAUFBITR
    LMNABORTPQ $.

  $( Lemma for "Non-Orthomodular Models..." paper.  (Contributed by NM,
     7-Feb-1999.) $)
  nomcon3 $p |- ( a ==3 b ) = ( b ' ==4 a ' ) $=
    ( wid2 wn wid1 wid3 wid4 nomcon2 nomb32 nomb41 3tr1 ) BACADZBDZEABFMLGBAHAB
    IMLJK $.

  $( Lemma for "Non-Orthomodular Models..." paper.  (Contributed by NM,
     7-Feb-1999.) $)
  nomcon4 $p |- ( a ==4 b ) = ( b ' ==3 a ' ) $=
    ( wid1 wn wid2 wid4 wid3 nomcon1 nomb41 nomb32 3tr1 ) BACADZBDZEABFMLGBAHAB
    IMLJK $.

  $( Lemma for "Non-Orthomodular Models..." paper.  (Contributed by NM,
     7-Feb-1999.) $)
  nomcon5 $p |- ( a == b ) = ( b ' == a ' ) $=
    ( tb wn bicom conb ax-r2 ) ABCBACBDADCABEBAFG $.

  $( Part of Lemma 3.3(14) from "Non-Orthomodular Models..." paper.
     (Contributed by NM, 7-Feb-1999.) $)
  nom10 $p |- ( a ->0 ( a ^ b ) ) = ( a ->1 b ) $=
    ( wn wa wo wi0 wi1 id df-i0 df-i1 3tr1 ) ACABDZEZMALFABGMHALIABJK $.

  $( Part of Lemma 3.3(14) from "Non-Orthomodular Models..." paper.
     (Contributed by NM, 7-Feb-1999.) $)
  nom11 $p |- ( a ->1 ( a ^ b ) ) = ( a ->1 b ) $=
    ( wn wa wo wi1 anass ax-r1 anidm ran ax-r2 lor df-i1 3tr1 ) ACZAABDZDZEOPEA
    PFABFQPOQAADZBDZPSQAABGHRABAIJKLAPMABMN $.

  $( Part of Lemma 3.3(14) from "Non-Orthomodular Models..." paper.
     (Contributed by NM, 7-Feb-1999.) $)
  nom12 $p |- ( a ->2 ( a ^ b ) ) = ( a ->1 b ) $=
    ( wa wn wo wi2 wi1 oran ax-r1 orabs ax-r2 con3 lor ax-a2 df-i2 df-i1 3tr1 )
    ABCZADZRDCZEZSREZARFABGUARSEUBTSRTATDZAREZAUDUCARHIABJKLMRSNKAROABPQ $.

  $( Part of Lemma 3.3(14) from "Non-Orthomodular Models..." paper.
     (Contributed by NM, 7-Feb-1999.) $)
  nom13 $p |- ( a ->3 ( a ^ b ) ) = ( a ->1 b ) $=
    ( wn wa wo wi3 wi1 oran ax-r1 orabs ax-r2 con3 lor df-le2 ax-r5 womaa df-i3
    lea df-i1 3tr1 ) ACZABDZDZUAUBCDZEZAUAUBEZDZEZUFAUBFABGUHUAUGEUFUEUAUGUEUCU
    AEUAUDUAUCUDAUDCZAUBEZAUJUIAUBHIABJKLMUCUAUAUBRNKOABPKAUBQABST $.

  $( Part of Lemma 3.3(14) from "Non-Orthomodular Models..." paper.
     (Contributed by NM, 7-Feb-1999.) $)
  nom14 $p |- ( a ->4 ( a ^ b ) ) = ( a ->1 b ) $=
    ( wa wn wi4 wi1 ax-a2 anass ax-r1 anidm ran ax-r2 lor lear df-le2 3tr ax-r5
    wo leo lea lbtr lel2or lecon ler2an lelor lebi df-i4 df-i1 3tr1 ) AABCZCZAD
    ZUJCZRZULUJRZUJDZCZRZUOAUJEABFURUJUQRZUJULRZUOUNUJUQUNUMUKRUMUJRUJUKUMGUKUJ
    UMUKAACZBCZUJVBUKAABHIVAABAJKLMUMUJULUJNOPQUSUTUJUTUQUJULSUQUOUTUOUPTULUJGU
    AUBULUQUJULUOUPULUJSUJAABTUCUDUEUFUJULGPAUJUGABUHUI $.

  $( Part of Lemma 3.3(14) from "Non-Orthomodular Models..." paper.
     (Contributed by NM, 7-Feb-1999.) $)
  nom15 $p |- ( a ->5 ( a ^ b ) ) = ( a ->1 b ) $=
    ( wa wn wo wi5 wi1 anass ax-r1 anidm ran ax-r2 ax-r5 ax-a2 df-le2 3tr oran3
    lear lan anabs 2or df-i5 df-i1 3tr1 ) AABCZCZADZUECZEZUGUEDZCZEZUGUEEZAUEFA
    BGULUEUGEUMUIUEUKUGUIUEUHEUHUEEUEUFUEUHUFAACZBCZUEUOUFAABHIUNABAJKLMUEUHNUH
    UEUGUEROPUKUGUGBDZEZCZUGURUKUQUJUGABQSIUGUPTLUAUEUGNLAUEUBABUCUD $.

  $( Part of Lemma 3.3(14) from "Non-Orthomodular Models..." paper.
     (Contributed by NM, 7-Feb-1999.) $)
  nom20 $p |- ( a ==0 ( a ^ b ) ) = ( a ->1 b ) $=
    ( wn wa wo wid0 wi1 lea leor letr lelor ax-a3 ax-r1 oran3 ax-r5 lbtr df2le2
    ax-r2 df-id0 df-i1 3tr1 ) ACZABDZEZUCCZAEZDUDAUCFABGUDUFUDUBBCZAEZEZUFUCUHU
    BUCAUHABHAUGIJKUIUBUGEZAEZUFUKUIUBUGALMUJUEAABNORPQAUCSABTUA $.

  $( Part of Lemma 3.3(14) from "Non-Orthomodular Models..." paper.
     (Contributed by NM, 7-Feb-1999.) $)
  nom21 $p |- ( a ==1 ( a ^ b ) ) = ( a ->1 b ) $=
    ( wa wn wo wid1 wi1 ancom oran3 lor ax-r2 anidm ran ax-r1 anass 2an lea leo
    or12 letr lelor df2le2 3tr2 df-id1 df-i1 3tr1 ) AABCZDZEZADZAUGCZEZCZUJUGEZ
    AUGFABGUJABDZEZEZUNCUNUQCUMUNUQUNHUQUIUNULUQAUJUOEZEUIUJAUOSURUHAABIJKUGUKU
    JUGAACZBCZUKUTUGUSABALMNAABOKJPUNUQUGUPUJUGAUPABQAUORTUAUBUCAUGUDABUEUF $.

  $( Part of Lemma 3.3(14) from "Non-Orthomodular Models..." paper.
     (Contributed by NM, 7-Feb-1999.) $)
  nom22 $p |- ( a ==2 ( a ^ b ) ) = ( a ->1 b ) $=
    ( wa wn wid2 wi1 oran3 lor ax-r1 or12 ax-r2 ax-a2 lan anabs ax-r5 2an ancom
    wo lea leo letr lelor df2le2 3tr df-id2 df-i1 3tr1 ) AABCZDZRZUHADZUICZRZCZ
    UKUHRZAUHEABFUNUKABDZRZRZUOCUOURCUOUJURUMUOUJAUKUPRZRZURUTUJUSUIAABGZHIAUKU
    PJKUMULUHRUOUHULLULUKUHULUKUSCZUKVBULUSUIUKVAMIUKUPNKOKPURUOQUOURUHUQUKUHAU
    QABSAUPTUAUBUCUDAUHUEABUFUG $.

  $( Part of Lemma 3.3(14) from "Non-Orthomodular Models..." paper.
     (Contributed by NM, 7-Feb-1999.) $)
  nom23 $p |- ( a ==3 ( a ^ b ) ) = ( a ->1 b ) $=
    ( wn wa wo wid3 wi1 wt le1 df-t anabs ax-r1 oran3 lan ax-r2 lor lbtr df2le2
    df-id3 df-i1 3tr1 ) ACZABDZEZAUBUCCZDZEZDUDAUCFABGUDUGUDHUGUDIHAUBEUGAJUBUF
    AUBUBUBBCZEZDZUFUJUBUBUHKLUIUEUBABMNOPOQRAUCSABTUA $.

  $( Part of Lemma 3.3(14) from "Non-Orthomodular Models..." paper.
     (Contributed by NM, 7-Feb-1999.) $)
  nom24 $p |- ( a ==4 ( a ^ b ) ) = ( a ->1 b ) $=
    ( wn wa wo wid4 wi1 leo leror oran3 anidm ran ax-r1 anass ax-r2 lbtr df2le2
    2or df-id4 df-i1 3tr1 ) ACZABDZEZUCCZAUCDZEZDUDAUCFABGUDUGUDUBBCZEZUCEUGUBU
    IUCUBUHHIUIUEUCUFABJUCAADZBDZUFUKUCUJABAKLMAABNORPQAUCSABTUA $.

  $( Part of Lemma 3.3(14) from "Non-Orthomodular Models..." paper.
     (Contributed by NM, 7-Feb-1999.) $)
  nom25 $p |- ( a == ( a ^ b ) ) = ( a ->1 b ) $=
    ( wa wn wo tb wi1 anass ax-r1 anidm ran ax-r2 oran3 lan anabs 2or ax-a2 dfb
    df-i1 3tr1 ) AABCZCZADZUADZCZEZUCUAEZAUAFABGUFUAUCEUGUBUAUEUCUBAACZBCZUAUIU
    BAABHIUHABAJKLUEUCUCBDZEZCZUCULUEUKUDUCABMNIUCUJOLPUAUCQLAUARABST $.

  $( Part of Lemma 3.3(14) from "Non-Orthomodular Models..." paper.
     (Contributed by NM, 7-Feb-1999.) $)
  nom30 $p |- ( ( a ^ b ) ==0 a ) = ( a ->1 b ) $=
    ( wa wid0 wi1 wn wo ancom df-id0 3tr1 nom20 ax-r2 ) ABCZADZAMDZABEMFAGZAFMG
    ZCQPCNOPQHMAIAMIJABKL $.

  $( Part of Lemma 3.3(14) from "Non-Orthomodular Models..." paper.
     (Contributed by NM, 7-Feb-1999.) $)
  nom31 $p |- ( ( a ^ b ) ==1 a ) = ( a ->1 b ) $=
    ( wa wid1 wid4 wi1 nomb41 ax-r1 nom24 ax-r2 ) ABCZADZAKEZABFMLAKGHABIJ $.

  $( Part of Lemma 3.3(14) from "Non-Orthomodular Models..." paper.
     (Contributed by NM, 7-Feb-1999.) $)
  nom32 $p |- ( ( a ^ b ) ==2 a ) = ( a ->1 b ) $=
    ( wa wid2 wid3 wi1 nomb32 ax-r1 nom23 ax-r2 ) ABCZADZAKEZABFMLAKGHABIJ $.

  $( Part of Lemma 3.3(14) from "Non-Orthomodular Models..." paper.
     (Contributed by NM, 7-Feb-1999.) $)
  nom33 $p |- ( ( a ^ b ) ==3 a ) = ( a ->1 b ) $=
    ( wa wid3 wid2 wi1 nomb32 nom22 ax-r2 ) ABCZADAJEABFJAGABHI $.

  $( Part of Lemma 3.3(14) from "Non-Orthomodular Models..." paper.
     (Contributed by NM, 7-Feb-1999.) $)
  nom34 $p |- ( ( a ^ b ) ==4 a ) = ( a ->1 b ) $=
    ( wa wid4 wid1 wi1 nomb41 nom21 ax-r2 ) ABCZADAJEABFJAGABHI $.

  $( Part of Lemma 3.3(14) from "Non-Orthomodular Models..." paper.
     (Contributed by NM, 7-Feb-1999.) $)
  nom35 $p |- ( ( a ^ b ) == a ) = ( a ->1 b ) $=
    ( wa tb wi1 bicom nom25 ax-r2 ) ABCZADAIDABEIAFABGH $.

  $( Part of Lemma 3.3(15) from "Non-Orthomodular Models..." paper.
     (Contributed by NM, 7-Feb-1999.) $)
  nom40 $p |- ( ( a v b ) ->0 b ) = ( a ->2 b ) $=
    ( wn wa wi0 wi1 wo wi2 nom10 ax-a2 ax-a1 ancom anor3 ax-r2 ax-r1 df-i0 3tr1
    2or i2i1 ) BCZTACZDZEZTUAFABGZBEZABHTUAIUDCZBGZTCZUBGZUEUCUGBUFGUIUFBJBUHUF
    UBBKUBUFUBUATDUFTUALABMNORNUDBPTUBPQABSQ $.

  $( Part of Lemma 3.3(15) from "Non-Orthomodular Models..." paper.
     (Contributed by NM, 7-Feb-1999.) $)
  nom41 $p |- ( ( a v b ) ->1 b ) = ( a ->2 b ) $=
    ( wn wo wi2 wi1 wa ancom anor3 ax-r2 ud2lem0a ax-r1 nom12 i1i2 i2i1 3tr1 )
    BCZABDZCZEZQACZFZRBFABETQQUAGZEZUBUDTUCSQUCUAQGSQUAHABIJKLQUAMJRBNABOP $.

  $( Part of Lemma 3.3(15) from "Non-Orthomodular Models..." paper.
     (Contributed by NM, 7-Feb-1999.) $)
  nom42 $p |- ( ( a v b ) ->2 b ) = ( a ->2 b ) $=
    ( wn wo wi1 wi2 wa ancom anor3 ax-r2 ud1lem0a ax-r1 nom11 i2i1 3tr1 ) BCZAB
    DZCZEZPACZEZQBFABFSPPTGZEZUAUCSUBRPUBTPGRPTHABIJKLPTMJQBNABNO $.

  $( Part of Lemma 3.3(15) from "Non-Orthomodular Models..." paper.
     (Contributed by NM, 7-Feb-1999.) $)
  nom43 $p |- ( ( a v b ) ->3 b ) = ( a ->2 b ) $=
    ( wn wo wi4 wi1 wi3 wi2 wa ancom anor3 ax-r2 ud4lem0a ax-r1 nom14 i3i4 i2i1
    3tr1 ) BCZABDZCZEZSACZFZTBGABHUBSSUCIZEZUDUFUBUEUASUEUCSIUASUCJABKLMNSUCOLT
    BPABQR $.

  $( Part of Lemma 3.3(15) from "Non-Orthomodular Models..." paper.
     (Contributed by NM, 7-Feb-1999.) $)
  nom44 $p |- ( ( a v b ) ->4 b ) = ( a ->2 b ) $=
    ( wn wo wi3 wi1 wi4 wi2 wa ancom anor3 ax-r2 ud3lem0a ax-r1 nom13 i4i3 i2i1
    3tr1 ) BCZABDZCZEZSACZFZTBGABHUBSSUCIZEZUDUFUBUEUASUEUCSIUASUCJABKLMNSUCOLT
    BPABQR $.

  $( Part of Lemma 3.3(15) from "Non-Orthomodular Models..." paper.
     (Contributed by NM, 7-Feb-1999.) $)
  nom45 $p |- ( ( a v b ) ->5 b ) = ( a ->2 b ) $=
    ( wn wo wi5 wi1 wi2 ancom anor3 ax-r2 ud5lem0a ax-r1 nom15 i5con i2i1 3tr1
    wa ) BCZABDZCZEZRACZFZSBEABGUARRUBQZEZUCUEUAUDTRUDUBRQTRUBHABIJKLRUBMJSBNAB
    OP $.

  $( Part of Lemma 3.3(15) from "Non-Orthomodular Models..." paper.
     (Contributed by NM, 7-Feb-1999.) $)
  nom50 $p |- ( ( a v b ) ==0 b ) = ( a ->2 b ) $=
    ( wn wo wid0 wi1 wi2 wa ancom anor3 ax-r2 lor ax-r4 ax-r5 ax-r1 df-id0 3tr1
    2an nom20 nomcon0 i2i1 ) BCZABDZCZEZUBACZFZUCBEABGUEUBUBUFHZEZUGUBCZUDDZUDC
    ZUBDZHZUJUHDZUHCZUBDZHZUEUIURUNUOUKUQUMUHUDUJUHUFUBHUDUBUFIABJKZLUPULUBUHUD
    USMNROUBUDPUBUHPQUBUFSKUCBTABUAQ $.

  $( Part of Lemma 3.3(15) from "Non-Orthomodular Models..." paper.
     (Contributed by NM, 7-Feb-1999.) $)
  nom51 $p |- ( ( a v b ) ==1 b ) = ( a ->2 b ) $=
    ( wn wo wid2 wi1 wid1 wi2 wa ancom anor3 ax-r2 ax-r1 lor lan 2or 2an df-id2
    ax-r4 3tr1 nom22 nomcon1 i2i1 ) BCZABDZCZEZUDACZFZUEBGABHUGUDUDUHIZEZUIUDUF
    CZDZUFUDCZULIZDZIUDUJCZDZUJUNUQIZDZIUGUKUMURUPUTULUQUDUFUJUJUFUJUHUDIZUFUDU
    HJABKZLMZSNUFUJUOUSVCULUQUNUFUJUFVAUJVAUFVBMUHUDJLSOPQUDUFRUDUJRTUDUHUALUEB
    UBABUCT $.

  $( Part of Lemma 3.3(15) from "Non-Orthomodular Models..." paper.
     (Contributed by NM, 7-Feb-1999.) $)
  nom52 $p |- ( ( a v b ) ==2 b ) = ( a ->2 b ) $=
    ( wn wo wid1 wi1 wid2 wi2 wa ancom anor3 ax-r2 ax-r1 ax-r4 lor lan 2an 3tr1
    df-id1 nom21 nomcon2 i2i1 ) BCZABDZCZEZUCACZFZUDBGABHUFUCUCUGIZEZUHUCUECZDZ
    UCCZUCUEIZDZIUCUICZDZUMUCUIIZDZIUFUJULUQUOUSUKUPUCUEUIUIUEUIUGUCIUEUCUGJABK
    LMZNOUNURUMUEUIUCUTPOQUCUESUCUISRUCUGTLUDBUAABUBR $.

  $( Part of Lemma 3.3(15) from "Non-Orthomodular Models..." paper.
     (Contributed by NM, 7-Feb-1999.) $)
  nom53 $p |- ( ( a v b ) ==3 b ) = ( a ->2 b ) $=
    ( wn wo wid4 wi1 wid3 wi2 wa ancom anor3 ax-r2 ax-r1 lor lan 2or 2an df-id4
    ax-r4 3tr1 nom24 nomcon3 i2i1 ) BCZABDZCZEZUDACZFZUEBGABHUGUDUDUHIZEZUIUDCZ
    UFDZUFCZUDUFIZDZIULUJDZUJCZUDUJIZDZIUGUKUMUQUPUTUFUJULUJUFUJUHUDIUFUDUHJABK
    LMZNUNURUOUSUFUJVASUFUJUDVAOPQUDUFRUDUJRTUDUHUALUEBUBABUCT $.

  $( Part of Lemma 3.3(15) from "Non-Orthomodular Models..." paper.
     (Contributed by NM, 7-Feb-1999.) $)
  nom54 $p |- ( ( a v b ) ==4 b ) = ( a ->2 b ) $=
    ( wn wo wid3 wi1 wid4 wi2 wa ancom anor3 ax-r2 lor ax-r4 lan 2an 3tr1 ax-r1
    df-id3 nom23 nomcon4 i2i1 ) BCZABDZCZEZUCACZFZUDBGABHUFUCUCUGIZEZUHUJUFUCCZ
    UIDZUCUKUICZIZDZIUKUEDZUCUKUECZIZDZIUJUFULUPUOUSUIUEUKUIUGUCIUEUCUGJABKLZMU
    NURUCUMUQUKUIUEUTNOMPUCUISUCUESQRUCUGTLUDBUAABUBQ $.

  $( Part of Lemma 3.3(15) from "Non-Orthomodular Models..." paper.
     (Contributed by NM, 7-Feb-1999.) $)
  nom55 $p |- ( ( a v b ) == b ) = ( a ->2 b ) $=
    ( wn wa tb wi1 wo wi2 nom25 conb bicom ancom anor3 ax-r2 ax-r1 lbi 3tr i2i1
    3tr1 ) BCZTACZDZEZTUAFABGZBEZABHTUAIUEUDCZTETUFEUCUDBJUFTKUFUBTUBUFUBUATDUF
    TUALABMNOPQABRS $.

  $( Part of Lemma 3.3(15) from "Non-Orthomodular Models..." paper.
     (Contributed by NM, 7-Feb-1999.) $)
  nom60 $p |- ( b ==0 ( a v b ) ) = ( a ->2 b ) $=
    ( wo wid0 wi2 wn wa ancom df-id0 3tr1 nom50 ax-r2 ) BABCZDZMBDZABEBFMCZMFBC
    ZGQPGNOPQHBMIMBIJABKL $.

  $( Part of Lemma 3.3(15) from "Non-Orthomodular Models..." paper.
     (Contributed by NM, 7-Feb-1999.) $)
  nom61 $p |- ( b ==1 ( a v b ) ) = ( a ->2 b ) $=
    ( wo wid1 wid4 wi2 nomb41 ax-r1 nom54 ax-r2 ) BABCZDZKBEZABFMLKBGHABIJ $.

  $( Part of Lemma 3.3(15) from "Non-Orthomodular Models..." paper.
     (Contributed by NM, 7-Feb-1999.) $)
  nom62 $p |- ( b ==2 ( a v b ) ) = ( a ->2 b ) $=
    ( wo wid2 wid3 wi2 nomb32 ax-r1 nom53 ax-r2 ) BABCZDZKBEZABFMLKBGHABIJ $.

  $( Part of Lemma 3.3(15) from "Non-Orthomodular Models..." paper.
     (Contributed by NM, 7-Feb-1999.) $)
  nom63 $p |- ( b ==3 ( a v b ) ) = ( a ->2 b ) $=
    ( wo wid3 wid2 wi2 nomb32 nom52 ax-r2 ) BABCZDJBEABFBJGABHI $.

  $( Part of Lemma 3.3(15) from "Non-Orthomodular Models..." paper.
     (Contributed by NM, 7-Feb-1999.) $)
  nom64 $p |- ( b ==4 ( a v b ) ) = ( a ->2 b ) $=
    ( wo wid4 wid1 wi2 nomb41 nom51 ax-r2 ) BABCZDJBEABFBJGABHI $.

  $( Part of Lemma 3.3(15) from "Non-Orthomodular Models..." paper.
     (Contributed by NM, 7-Feb-1999.) $)
  nom65 $p |- ( b == ( a v b ) ) = ( a ->2 b ) $=
    ( wo tb wi2 bicom nom55 ax-r2 ) BABCZDIBDABEBIFABGH $.

  $( Lemma for proof of Mayet 8-variable "full" equation from 4-variable
     Godowski equation.  (Contributed by NM, 19-Nov-1999.) $)
  go1 $p |- ( ( a ^ b ) ^ ( a ->1 b ' ) ) = 0 $=
    ( wa wn wi1 wo wf df-i1 lan lear lelor lelan oran3 dff ax-r1 ax-r2 lbtr le0
    lebi ) ABCZABDZEZCTADZAUACZFZCZGUBUETAUAHIUFGUFTUCUAFZCZGUEUGTUDUAUCAUAJKLU
    HTTDZCZGUGUITABMIGUJTNOPQUFRSP $.

  $( Lemma for disjunction of ` ->2 ` .  (Contributed by NM, 5-Jul-2000.) $)
  i2or $p |- ( ( a ->2 c ) v ( b ->2 c ) ) =< ( ( a ^ b ) ->2 c ) $=
    ( wi2 wo wa wn df-i2 lea lecon leran lelor bltr lear lel2or ax-r1 lbtr ) AC
    DZBCDZECABFZGZCGZFZEZTCDZRUDSRCAGZUBFZEUDACHUGUCCUFUAUBTAABIJKLMSCBGZUBFZEU
    DBCHUIUCCUHUAUBTBABNJKLMOUEUDTCHPQ $.

  $( Lemma for disjunction of ` ->1 ` .  (Contributed by NM, 5-Jul-2000.) $)
  i1or $p |- ( ( c ->1 a ) v ( c ->1 b ) ) =< ( c ->1 ( a v b ) ) $=
    ( wi1 wo wn wa df-i1 leo lelan lelor bltr leor lel2or ax-r1 lbtr ) CADZCBDZ
    ECFZCABEZGZEZCTDZQUBRQSCAGZEUBCAHUDUASATCABIJKLRSCBGZEUBCBHUEUASBTCBAMJKLNU
    CUBCTHOP $.

  $( "Less than" analogue is equal to ` ->2 ` implication.  (Contributed by NM,
     28-Jan-2002.) $)
  lei2 $p |- ( a =<2 b ) = ( a ->2 b ) $=
    ( wo tb wn wa wle2 wi2 mi df-le df-i2 3tr1 ) ABCBDBAEBEFCABGABHABIABJABKL
    $.

  $( Relevance implication is less than or equal to Sasaki implication.
     (Contributed by NM, 26-Jun-2003.) $)
  i5lei1 $p |- ( a ->5 b ) =< ( a ->1 b ) $=
    ( wa wn wi5 wi1 ax-a3 ax-a2 ax-r2 lea lel2or leror bltr df-i5 df-i1 le3tr1
    wo ) ABCZADZBCZQSBDZCZQZSRQZABEABFUCTUBQZRQZUDUCRUEQUFRTUBGRUEHIUESRTSUBSBJ
    SUAJKLMABNABOP $.

  $( Relevance implication is less than or equal to Dishkant implication.
     (Contributed by NM, 26-Jun-2003.) $)
  i5lei2 $p |- ( a ->5 b ) =< ( a ->2 b ) $=
    ( wa wn wo wi5 wi2 lear lel2or leror df-i5 df-i2 le3tr1 ) ABCZADZBCZEZOBDCZ
    EBREABFABGQBRNBPABHOBHIJABKABLM $.

  $( Relevance implication is less than or equal to Kalmbach implication.
     (Contributed by NM, 26-Jun-2003.) $)
  i5lei3 $p |- ( a ->5 b ) =< ( a ->3 b ) $=
    ( wa wn wo wi5 wi3 leor lelan leror df-i5 ax-a3 ax-r2 df-i3 ax-a2 le3tr1 )
    ABCZADZBCZRBDCZEZEZARBEZCZUAEZABFZABGZQUDUABUCABRHIJUFQSETEUBABKQSTLMUGUAUD
    EUEABNUAUDOMP $.

  $( Relevance implication is less than or equal to non-tollens implication.
     (Contributed by NM, 26-Jun-2003.) $)
  i5lei4 $p |- ( a ->5 b ) =< ( a ->4 b ) $=
    ( wa wn wo wi5 wi4 leo leran lelor df-i5 df-i4 le3tr1 ) ABCADZBCEZNBDZCZEON
    BEZPCZEABFABGQSONRPNBHIJABKABLM $.

  $( Quantum identity is less than classical identity.  (Contributed by NM,
     4-Mar-2006.) $)
  id5leid0 $p |- ( a == b ) =< ( a ==0 b ) $=
    ( wa wn wo tb wid0 ax-a2 lea lear le2or ler2an bltr dfb df-id0 le3tr1 ) ABC
    ZADZBDZCZEZRBEZSAEZCZABFABGUATQEZUDQTHUEUBUCTRQBRSIABJKTSQARSJABIKLMABNABOP
    $.

  ${
    id5id0.1 $e |- ( a == b ) = 1 $.
    $( Show that classical identity follows from quantum identity in OL.
       (Contributed by NM, 4-Mar-2006.) $)
    id5id0 $p |- ( a ==0 b ) = 1 $=
      ( tb wid0 id5leid0 sklem skr0 ) ABDZABEZCIJABFGH $.
  $}

  ${
    k1-6.1 $e |- x = ( ( x ^ c ) v ( x ^ c ' ) ) $.
    $( Statement (6) in proof of Theorem 1 of Kalmbach, _Orthomodular
       Lattices_, p. 21.  (Contributed by NM, 26-May-2008.) $)
    k1-6 $p |- ( x ' ^ c ) = ( ( x ' v c ' ) ^ c ) $=
      ( wn wa wo anor3 cm con4 oran3 oran2 2an 3tr1 ran anass ancom ax-a2 anabs
      lan 3tr ) BDZAEUAADZFZUAAFZEZAEUCUDAEZEUCAEUAUEABAEZBUBEZFZDZUGDZUHDZEZUA
      UEUMUJUGUHGHBUICIUCUKUDULBAJBAKLMNUCUDAOUFAUCUFAUDEAAUAFZEAUDAPUDUNAUAAQS
      AUARTST $.
  $}

  ${
    k1-7.1 $e |- x = ( ( x ^ c ) v ( x ^ c ' ) ) $.
    $( Statement (7) in proof of Theorem 1 of Kalmbach, _Orthomodular
       Lattices_, p. 21.  (Contributed by NM, 26-May-2008.) $)
    k1-7 $p |- ( x ' ^ c ' ) = ( ( x ' v c ) ^ c ' ) $=
      ( wn wa wo anor3 cm ax-a1 lan ror orcom 3tr con4 oran3 oran2 2an 3tr1 ran
      lor anass tr ancom ax-a2 anabs ) BDZADZEUFUGDZFZUFUGFZEZUGEZUFAFZUJUGEZEZ
      UMUGEUFUKUGBUGEZBUHEZFZDZUPDZUQDZEZUFUKVBUSUPUQGHBURBBAEZUPFUQUPFURCVCUQU
      PAUHBAIZJKUQUPLMNUIUTUJVABUGOBUGPQRSULUMUJEZUGEZUOVFULVEUKUGUMUIUJAUHUFVD
      TSSHUMUJUGUAUBUNUGUMUNUGUJEUGUGUFFZEUGUJUGUCUJVGUGUFUGUDJUGUFUEMJM $.
  $}

  ${
    k1-8a.1 $e |- x ' = ( ( x ' ^ c ) v ( x ' ^ c ' ) ) $.
    k1-8a.2 $e |- x =< c $.
    k1-8a.3 $e |- y =< c ' $.
    $( First part of statement (8) in proof of Theorem 1 of Kalmbach,
       _Orthomodular Lattices_, p. 21.  (Contributed by NM, 27-May-2008.) $)
    k1-8a $p |- x = ( ( x v y ) ^ c ) $=
      ( wo wa leo ler2an wn lelor leran ax-a1 ror ran k1-6 tr cm df2le2 lbtr
      3tr lebi ) BBCGZAHZBUDABCIEJUEBAKZGZAHZBUDUGACUFBFLMUHBKZKZUFGZAHZBAHZBUG
      UKABUJUFBNZOPUMULUMUJAHULBUJAUNPAUIDQRSBAETUBUAUC $.
  $}

  ${
    k1-8b.1 $e |- y ' = ( ( y ' ^ c ) v ( y ' ^ c ' ) ) $.
    k1-8b.2 $e |- x =< c $.
    k1-8b.3 $e |- y =< c ' $.
    $( Second part of statement (8) in proof of Theorem 1 of Kalmbach,
       _Orthomodular Lattices_, p. 21.  (Contributed by NM, 27-May-2008.) $)
    k1-8b $p |- y = ( ( x v y ) ^ c ' ) $=
      ( wo wn wa ax-a1 lan ror orcom 3tr lbtr k1-8a ran tr ) CCBGZAHZIBCGZTITCB
      CHZUBAIZUBTIZGUBTHZIZUDGUDUFGDUCUFUDAUEUBAJZKLUFUDMNFBAUEEUGOPSUATCBMQR
      $.
  $}

  ${
    k1-2.1 $e |- x = ( ( x ^ c ) v ( x ^ c ' ) ) $.
    k1-2.2 $e |- y = ( ( y ^ c ) v ( y ^ c ' ) ) $.
    k1-2.3 $e |- ( ( x ^ c ) v ( y ^ c ) ) ' = ( ( ( ( x ^ c )
         v ( y ^ c ) ) ' ^ c ) v ( ( ( x ^ c ) v ( y ^ c ) ) ' ^ c ' ) ) $.
    $( Statement (2) in proof of Theorem 1 of Kalmbach, _Orthomodular
       Lattices_, p. 21.  (Contributed by NM, 27-May-2008.) $)
    k1-2 $p |- ( ( x v y ) ^ c ) = ( ( x ^ c ) v ( y ^ c ) ) $=
      ( wo wa wn 2or or4 ax-r2 ran lear lel2or k1-8a ax-r1 tr ) BCGZAHBAHZCAHZG
      ZBAIZHZCUCHZGZGZAHZUBSUGASTUDGZUAUEGZGUGBUICUJDEJTUDUAUEKLMUBUHAUBUFFTAUA
      BANCANOUDUCUEBUCNCUCNOPQR $.
  $}

  ${
    k1-3.1 $e |- x = ( ( x ^ c ) v ( x ^ c ' ) ) $.
    k1-3.2 $e |- y = ( ( y ^ c ) v ( y ^ c ' ) ) $.
    k1-3.3 $e |- ( ( x ^ c ' ) v ( y ^ c ' ) ) ' = ( ( ( ( x ^ c ' )
     v ( y ^ c ' ) ) ' ^ c ) v ( ( ( x ^ c ' ) v ( y ^ c ' ) ) ' ^ c ' ) ) $.
    $( Statement (3) in proof of Theorem 1 of Kalmbach, _Orthomodular
       Lattices_, p. 21.  (Contributed by NM, 27-May-2008.) $)
    k1-3 $p |- ( ( x v y ) ^ c ' ) = ( ( x ^ c ' ) v ( y ^ c ' ) ) $=
      ( wo wn wa 2or or4 ax-r2 ran lear lel2or k1-8b ax-r1 tr ) BCGZAHZIBAIZCAI
      ZGZBTIZCTIZGZGZTIZUFSUGTSUAUDGZUBUEGZGUGBUICUJDEJUAUDUBUEKLMUFUHAUCUFFUAA
      UBBANCANOUDTUEBTNCTNOPQR $.
  $}

  ${
    k1-4.1 $e |- ( x ' ^ ( x v c ' ) ) =
        ( ( ( x ' ^ ( x v c ' ) ) ^ c ) v ( ( x ' ^ ( x v c ' ) ) ^ c ' ) ) $.
    k1-4.2 $e |- x =< c $.
    $( Statement (4) in proof of Theorem 1 of Kalmbach, _Orthomodular
       Lattices_, p. 21.  (Contributed by NM, 27-May-2008.) $)
    k1-4 $p |- ( x v ( x ' ^ c ) ) = c $=
      ( wn wa wo oran1 lan cm anor3 an32 dff 3tr1 leao4 df2le2 df-le2 ax-r4 3tr
      wf tr 2or or0r 3tr2 con1 ) BBEZAFZGZAUFUGEZFZUFBAEZGZFZUHEUKUMUJULUIUFBAH
      ZIJBUGKUMUMAFZUMUKFZGTUKGUKCUOTUPUKUGULFUGUIFUOTULUIUGUNIUFULALUGMNUPUFUK
      FZULFUQUKUFULUKLUQULUKUFBOPUQBAGZEUKBAKURABADQRUASUBUKUCSUDUE $.
  $}

  ${
    k1-5.1 $e |- ( x ' ^ ( x v c ) ) =
        ( ( ( x ' ^ ( x v c ) ) ^ c ) v ( ( x ' ^ ( x v c ) ) ^ c ' ) ) $.
    k1-5.2 $e |- x =< c ' $.
    $( Statement (5) in proof of Theorem 1 of Kalmbach, _Orthomodular
       Lattices_, p. 21.  (Contributed by NM, 27-May-2008.) $)
    k1-5 $p |- ( x v ( x ' ^ c ' ) ) = c ' $=
      ( wn wo wa ax-a1 lor lan orcom ran 2an 2or tr 3tr2 k1-4 ) AEZBBEZBAFZGZUA
      AGZUARGZFZSBREZFZGZUGRGZUGUEGZFZCTUFSAUEBAHZIJZUDUCUBFUJUBUCKUCUHUBUIUAUG
      RULLUAUGAUEULUKMNOPDQ $.
  $}

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
          Weakly orthomodular lattices
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Weak orthomodular law
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    ax-wom.1 $e |- ( a ' v ( a ^ b ) ) = 1 $.
    $( 2-variable WOML rule.  (Contributed by NM, 13-Nov-1998.) $)
    ax-wom $a |- ( b v ( a ' ^ b ' ) ) = 1 $.
  $}

  ${
    2vwomr2.1 $e |- ( b v ( a ' ^ b ' ) ) = 1 $.
    $( 2-variable WOML rule.  (Contributed by NM, 13-Nov-1998.) $)
    2vwomr2 $p |- ( a ' v ( a ^ b ) ) = 1 $=
      ( wn wa wo wt ancom ax-a1 2an ax-r2 lor 2or ax-r1 ax-wom ) ADZABEZFPBDZDZ
      PDZEZFGQUAPQBAEUAABHBSATBIZAIJKLRPSRPEZFZBPREZFZGUFUDBSUEUCUBPRHMNCKOK $.
  $}

  ${
    2vwomr1a.1 $e |- ( a ->1 b ) = 1 $.
    $( 2-variable WOML rule.  (Contributed by NM, 13-Nov-1998.) $)
    2vwomr1a $p |- ( a ->2 b ) = 1 $=
      ( wi2 wn wa wo wt df-i2 wi1 df-i1 ax-r1 ax-r2 ax-wom ) ABDBAEZBEFGHABIABO
      ABFGZABJZHQPABKLCMNM $.
  $}

  ${
    2vwomr2a.1 $e |- ( a ->2 b ) = 1 $.
    $( 2-variable WOML rule.  (Contributed by NM, 13-Nov-1998.) $)
    2vwomr2a $p |- ( a ->1 b ) = 1 $=
      ( wi1 wn wa wo wt df-i1 wi2 df-i2 ax-r1 ax-r2 2vwomr2 ) ABDAEZABFGHABIABB
      OBEFGZABJZHQPABKLCMNM $.
  $}

  ${
    2vwomlem.1 $e |- ( a ->2 b ) = 1 $.
    2vwomlem.2 $e |- ( b ->2 a ) = 1 $.
    $( Lemma from 2-variable WOML rule.  (Contributed by NM, 13-Nov-1998.) $)
    2vwomlem $p |- ( a == b ) = 1 $=
      ( tb wa wn wo wt dfb wf df-f ax-r1 wi2 anor3 ax-r2 lor df-i2 3tr 3tr2 ran
      anor2 ancom ax-r4 anabs anass oran 2an lan or0 le1 2vwomr2 lea leo ler2an
      oran3 lelor bltr lebi ax-wom ) ABEABFZAGZBGZFZHZIABJVEKHVEVBVEGZFZHVEIKVG
      VEKIGZVGLAABHZGZHZGZVBVIFZVHVGVMVLAVIUBMVKIVKAVCVBFZHZBANZIVJVNAVJVDVNVDV
      JABOMVBVCUCPQVPVOBARMDSUDVMVBVBVCHZFZVIFVBVQVIFZFVGVBVRVIVRVBVBVCUEMUAVBV
      QVIUFVSVFVBVSVAGZVDGZFVFVQVTVIWAABUPABUGUHVAVDOPUISTPQVEUJAVEVBAVEFZHZIWC
      UKIVBVAHZWCWDIABBVDHZABNZIWFWEABRMCPULMVAWBVBVAAVEABUMVAVDUNUOUQURUSUTTP
      $.
  $}

  ${
    wr5-2v.1 $e |- ( a == b ) = 1 $.
    $( WOML derived from 2-variable axioms.  (Contributed by NM,
       11-Nov-1998.) $)
    wr5-2v $p |- ( ( a v c ) == ( b v c ) ) = 1 $=
      ( wo wi2 wn wa wt df-i2 ax-r1 anandir anass ax-r2 3tr2 wi1 df-i1 bltr le1
      lebi anor3 lan 2an lor tb wlem1 skr0 lea leo lelan 2vwomr1a lear 2vwomlem
      lelor ) ACEZBCEZUOUPFUPUOGZUPGZHZEZIUOUPJUPAGZURHZEZAUPFZUTIVDVCAUPJKVBUS
      UPVABGZHCGZHZVAVFHZVEVFHZHVBUSVAVEVFLVGVAVIHVBVAVEVFMVIURVABCUAZUBNVHUQVI
      URACUAZVJUCOUDAUPAUPPVAAUPHZEZIAUPQIVMIVMIVAABHZEZVMIABPZVOIVPIVPBAPZHZVP
      VRIABUEVRDABUFUGKZVPVQUHRVPSTABQNVNVLVABUPABCUIUJUNRVMSTKNUKONUPUOFUOURUQ
      HZEZIUPUOJUOVEUQHZEZBUOFZWAIWDWCBUOJKWBVTUOVEVAHVFHZVIVHHWBVTVEVAVFLWEVEV
      HHWBVEVAVFMVHUQVEVKUBNVIURVHUQVJVKUCOUDBUOBUOPVEBUOHZEZIBUOQIWGIWGIVEBAHZ
      EZWGIVQWIIVQIVRVQVSVPVQULRVQSTBAQNWHWFVEAUOBACUIUJUNRWGSTKNUKONUM $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Weakly orthomodular lattices
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    wom3.1 $e |- ( a == b ) = 1 $.
    $( Weak orthomodular law for study of weakly orthomodular lattices.
       (Contributed by NM, 13-Nov-1998.) $)
    wom3 $p |- a =< ( ( a v c ) == ( b v c ) ) $=
      ( wt wo tb le1 wr5-2v ax-r1 bile letr ) AEACFBCFGZAHEMMEABCDIJKL $.
  $}

  ${
    wlor.1 $e |- ( a == b ) = 1 $.
    $( Weak orthomodular law.  (Contributed by NM, 24-Sep-1997.) $)
    wlor $p |- ( ( c v a ) == ( c v b ) ) = 1 $=
      ( wo tb wt ax-a2 2bi wr5-2v ax-r2 ) CAEZCBEZFACEZBCEZFGLNMOCAHCBHIABCDJK
      $.
  $}

  ${
    wran.1 $e |- ( a == b ) = 1 $.
    $( Weak orthomodular law.  (Contributed by NM, 24-Sep-1997.) $)
    wran $p |- ( ( a ^ c ) == ( b ^ c ) ) = 1 $=
      ( wa tb wn wo wt df-a 2bi wr4 wr5-2v ax-r2 ) ACEZBCEZFAGZCGZHZGZBGZRHZGZF
      IOTPUCACJBCJKSUBQUARABDLMLN $.
  $}

  ${
    wlan.1 $e |- ( a == b ) = 1 $.
    $( Weak orthomodular law.  (Contributed by NM, 24-Sep-1997.) $)
    wlan $p |- ( ( c ^ a ) == ( c ^ b ) ) = 1 $=
      ( wa tb wt ancom 2bi wran ax-r2 ) CAEZCBEZFACEZBCEZFGLNMOCAHCBHIABCDJK $.
  $}

  ${
    wr2.1 $e |- ( a == b ) = 1 $.
    wr2.2 $e |- ( b == c ) = 1 $.
    $( Inference rule of AUQL. (Contributed by NM, 24-Sep-1997.) $)
    wr2 $p |- ( a == c ) = 1 $=
      ( tb wa wn wo wt dfb rbi wr1 wran wr5-2v ax-r2 wwbmp wr4 wlor wwbmpr ) AC
      FZACGZBHZCHZGZIZBCFZUFEUGUFFBCGZUEIZUFFJUGUIUFBCKLUHUBUEBACABDMNOPQUAUFFU
      BAHZUDGZIZUFFJUAULUFACKLUKUEUBUJUCUDABDRNSPT $.
  $}

  ${
    w2or.1 $e |- ( a == b ) = 1 $.
    w2or.2 $e |- ( c == d ) = 1 $.
    $( Join both sides with disjunction.  (Contributed by NM, 13-Oct-1997.) $)
    w2or $p |- ( ( a v c ) == ( b v d ) ) = 1 $=
      ( wo wlor wr5-2v wr2 ) ACGADGBDGCDAFHABDEIJ $.
  $}

  ${
    w2an.1 $e |- ( a == b ) = 1 $.
    w2an.2 $e |- ( c == d ) = 1 $.
    $( Join both sides with conjunction.  (Contributed by NM, 13-Oct-1997.) $)
    w2an $p |- ( ( a ^ c ) == ( b ^ d ) ) = 1 $=
      ( wa wlan wran wr2 ) ACGADGBDGCDAFHABDEIJ $.
  $}

  ${
    w3tr1.1 $e |- ( a == b ) = 1 $.
    w3tr1.2 $e |- ( c == a ) = 1 $.
    w3tr1.3 $e |- ( d == b ) = 1 $.
    $( Transitive inference useful for introducing definitions.  (Contributed
       by NM, 13-Oct-1997.) $)
    w3tr1 $p |- ( c == d ) = 1 $=
      ( wr1 wr2 ) CADFABDEDBGHII $.
  $}

  ${
    w3tr2.1 $e |- ( a == b ) = 1 $.
    w3tr2.2 $e |- ( a == c ) = 1 $.
    w3tr2.3 $e |- ( b == d ) = 1 $.
    $( Transitive inference useful for eliminating definitions.  (Contributed
       by NM, 13-Oct-1997.) $)
    w3tr2 $p |- ( c == d ) = 1 $=
      ( wr1 w3tr1 ) ABCDEACFHBDGHI $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Relationship analogues (ordering; commutation) in WOML
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    wleoa.1 $e |- ( ( a v c ) == b ) = 1 $.
    $( Relation between two methods of expressing "less than or equal to".
       (Contributed by NM, 27-Sep-1997.) $)
    wleoa $p |- ( ( a ^ b ) == a ) = 1 $=
      ( wa wo wr1 wlan wa5c wr2 ) ABEAACFZEABKAKBDGHACIJ $.
  $}

  ${
    wleao.1 $e |- ( ( c ^ b ) == a ) = 1 $.
    $( Relation between two methods of expressing "less than or equal to".
       (Contributed by NM, 27-Sep-1997.) $)
    wleao $p |- ( ( a v b ) == b ) = 1 $=
      ( wo wa wa2 wr1 wancom wr2 wlor wa5b ) ABEZBBCFZEZBMBAEOABGANBACBFZNPADHN
      PBCIHJKJBCLJ $.
  $}

  ${
    wdf-le1.1 $e |- ( ( a v b ) == b ) = 1 $.
    $( Define "less than or equal to" analogue for ` == ` analogue of ` = ` .
       (Contributed by NM, 27-Sep-1997.) $)
    wdf-le1 $p |- ( a =<2 b ) = 1 $=
      ( wle2 wo tb wt df-le ax-r2 ) ABDABEBFGABHCI $.
  $}

  ${
    wdf-le2.1 $e |- ( a =<2 b ) = 1 $.
    $( Define "less than or equal to" analogue for ` == ` analogue of ` = ` .
       (Contributed by NM, 27-Sep-1997.) $)
    wdf-le2 $p |- ( ( a v b ) == b ) = 1 $=
      ( wo tb wle2 wt df-le ax-r1 ax-r2 ) ABDBEZABFZGLKABHICJ $.
  $}

  ${
    wom4.1 $e |- ( a =<2 b ) = 1 $.
    $( Orthomodular law.  Kalmbach 83 p. 22.  (Contributed by NM,
       13-Oct-1997.) $)
    wom4 $p |- ( ( a v ( a ' ^ b ) ) == b ) = 1 $=
      ( wn wo wa woml wdf-le2 wlan wlor w3tr2 ) AADZABEZFZEMALBFZEBABGNOAMBLABC
      HZIJPK $.
  $}

  ${
    wom5.1 $e |- ( a =<2 b ) = 1 $.
    wom5.2 $e |- ( ( b ^ a ' ) == 0 ) = 1 $.
    $( Orthomodular law.  Kalmbach 83 p. 22.  (Contributed by NM,
       13-Oct-1997.) $)
    wom5 $p |- ( a == b ) = 1 $=
      ( wf wo wn wa wr1 ancom bi1 wr2 wlor or0 wom4 w3tr2 ) AEFZAAGZBHZFABESAEB
      RHZSTEDITSBRJKLMQAANKABCOP $.
  $}

  ${
    wcomlem.1 $e |- ( a == ( ( a ^ b ) v ( a ^ b ' ) ) ) = 1 $.
    $( Analogue of commutation is symmetric.  Similar to Kalmbach 83 p. 22.
       (Contributed by NM, 27-Jan-2002.) $)
    wcomlem $p |- ( b == ( ( b ^ a ) v ( b ^ a ' ) ) ) = 1 $=
      ( wa wn ax-a2 bi1 wran ancom wr2 anabs wlan df-a anor1 w2or wr4 wr1 anass
      wo wlor wcon2 w3tr1 orabs wdf-le1 wom4 w3tr2 ) ABDZUGEZBDZSZUGAEZBDZSZBBA
      DZBUKDZSUMUJULUIUGUKBEZSZUKBSZBDZDZUQBDULUIUSBUQUSBBUKSZDZBUSVABDZVBURVAB
      URVAUKBFGHVCVBVABIGJVBBBUKKGJLULUQURDZBDZUTUKVDBUKUQEZUREZSZEZVDAVHAUGAUP
      DZSVHCUGVFVJVGUGVFABMGZVJVGABNGOJPVDVIVDVIUQURMGQJHVEUTUQURBRGJUHUQBUGUQV
      KUAHUBTQUGBUGBUGBSZBUGSZBVLVMUGBFGVMBUNSZBUGUNBUGUNABIGZTVNBBAUCGJJUDUEUG
      UNULUOVOULUOUKBIGOUF $.
  $}

  ${
    wdf-c1.1 $e |- ( a == ( ( a ^ b ) v ( a ^ b ' ) ) ) = 1 $.
    $( Show that commutator is a 'commutes' analogue for ` == ` analogue of
       ` = ` .  (Contributed by NM, 27-Jan-2002.) $)
    wdf-c1 $p |- C ( a , b ) = 1 $=
      ( wcmtr wa wn wo cmtrcom df-cmtr df-t bi1 wcomlem ax-a1 ax-r5 ax-a2 ax-r2
      wt lan wr2 w2or wr3 3tr ) ABDBADBAEBAFZEGZBFZAEUEUCEGZGZQABHBAIUGQBUEGZUG
      QUHBJKBUDUEUFABCLAUEAABEZAUEEZGZUJAUEFZEZGZCUKUNUKUMUJGUNUIUMUJBULABMRNUM
      UJOPKSLTSUAUB $.
  $}

  ${
    wdf-c2.1 $e |- C ( a , b ) = 1 $.
    $( Show that commutator is a 'commutes' analogue for ` == ` analogue of
       ` = ` .  (Contributed by NM, 27-Jan-2002.) $)
    wdf-c2 $p |- ( a == ( ( a ^ b ) v ( a ^ b ' ) ) ) = 1 $=
      ( wa wn wo tb wt le1 lea lel2or lelor wcmtr ax-r1 df-cmtr ax-r2 dfb ancom
      2an anabs df2le2 anandi oran3 oran2 anor3 lan anidm 3tr2 2or le3tr1 lebi
      ) AABDZABEZDZFZGZHUPIUOAEZBDZUQUMDZFZFZUOUQFZHUPUTUQUOURUQUSUQBJUQUMJKLHA
      BMZVAVCHCNABOPUPAUODZUQUOEZDZFVBAUOQVDUOVFUQVDUOADUOAUORUOAULAUNABJAUMJKU
      APUQUQUMFZUQBFZDZDUQVGDZUQVHDZDZVFUQUQVGVHUBVIVEUQVIULEZUNEZDVEVGVMVHVNAB
      UCABUDSULUNUEPUFVLUQUQDUQVJUQVKUQUQUMTUQBTSUQUGPUHUIPUJUK $.
  $}

  ${
    wdf2le1.1 $e |- ( ( a ^ b ) == a ) = 1 $.
    $( Alternate definition of "less than or equal to".  (Contributed by NM,
       27-Sep-1997.) $)
    wdf2le1 $p |- ( a =<2 b ) = 1 $=
      ( wleao wdf-le1 ) ABABACDE $.
  $}

  ${
    wdf2le2.1 $e |- ( a =<2 b ) = 1 $.
    $( Alternate definition of "less than or equal to".  (Contributed by NM,
       27-Sep-1997.) $)
    wdf2le2 $p |- ( ( a ^ b ) == a ) = 1 $=
      ( wdf-le2 wleoa ) ABBABCDE $.
  $}

  $( L.e. absorption.  (Contributed by NM, 27-Sep-1997.) $)
  wleo $p |- ( a =<2 ( a v b ) ) = 1 $=
    ( wo wa5c wdf2le1 ) AABCABDE $.

  $( L.e. absorption.  (Contributed by NM, 27-Sep-1997.) $)
  wlea $p |- ( ( a ^ b ) =<2 a ) = 1 $=
    ( wa wo wa2 wa5b wr2 wdf-le1 ) ABCZAIADAIDAIAEABFGH $.

  $( Anything is less than or equal to 1.  (Contributed by NM, 27-Sep-1997.) $)
  wle1 $p |- ( a =<2 1 ) = 1 $=
    ( wt wo or1 bi1 wdf-le1 ) ABABCBADEF $.

  $( 0 is less than or equal to anything.  (Contributed by NM, 11-Oct-1997.) $)
  wle0 $p |- ( 0 =<2 a ) = 1 $=
    ( wf wle2 wo tb wt df-le ax-a2 or0 ax-r2 bi1 ) BACBADZAEFBAGLALABDABAHAIJKJ
    $.

  ${
    wle.1 $e |- ( a =<2 b ) = 1 $.
    $( Add disjunct to right of l.e.  (Contributed by NM, 13-Oct-1997.) $)
    wler $p |- ( a =<2 ( b v c ) ) = 1 $=
      ( wo wle2 tb wt df-le ax-a3 ax-r1 rbi ax-r2 wr5-2v ) ABCEZFAOEZOGZHAOIQAB
      EZCEZOGHPSOSPABCJKLRBCRBGZABFZHUATABIKDMNMM $.

    $( Add conjunct to left of l.e.  (Contributed by NM, 13-Oct-1997.) $)
    wlel $p |- ( ( a ^ c ) =<2 b ) = 1 $=
      ( wa an32 bi1 wdf2le2 wran wr2 wdf2le1 ) ACEZBLBEZABEZCEZLMOACBFGNACABDHI
      JK $.

    $( Add disjunct to right of both sides.  (Contributed by NM,
       13-Oct-1997.) $)
    wleror $p |- ( ( a v c ) =<2 ( b v c ) ) = 1 $=
      ( wo orordir bi1 wr1 wdf-le2 wr5-2v wr2 wdf-le1 ) ACEZBCEZMNEZABEZCEZNQOQ
      OABCFGHPBCABDIJKL $.

    $( Add conjunct to right of both sides.  (Contributed by NM,
       13-Oct-1997.) $)
    wleran $p |- ( ( a ^ c ) =<2 ( b ^ c ) ) = 1 $=
      ( wa anandir bi1 wr1 wdf2le2 wran wr2 wdf2le1 ) ACEZBCEZMNEZABEZCEZMQOQOA
      BCFGHPACABDIJKL $.

    $( Contrapositive for l.e.  (Contributed by NM, 13-Oct-1997.) $)
    wlecon $p |- ( b ' =<2 a ' ) = 1 $=
      ( wn wa wo ax-a2 bi1 oran wdf-le2 w3tr2 wcon3 wdf2le1 ) BDZADZNOEZBBAFZAB
      FZPDZBQRBAGHQSBAIHABCJKLM $.
  $}

  ${
    wletr.1 $e |- ( a =<2 b ) = 1 $.
    wletr.2 $e |- ( b =<2 c ) = 1 $.
    $( Transitive law for l.e.  (Contributed by NM, 13-Oct-1997.) $)
    wletr $p |- ( a =<2 c ) = 1 $=
      ( wa wo wdf-le2 wr5-2v wr1 ax-a3 bi1 w3tr2 wlan anabs wr2 wdf2le1 ) ACACF
      AABCGZGZFZACSARABGZCGZCSUBRUABCABDHIJBCEHUBSABCKLMNTAAROLPQ $.
  $}

  ${
    wbltr.1 $e |- ( a == b ) = 1 $.
    wbltr.2 $e |- ( b =<2 c ) = 1 $.
    $( Transitive inference.  (Contributed by NM, 13-Oct-1997.) $)
    wbltr $p |- ( a =<2 c ) = 1 $=
      ( wo wr5-2v wdf-le2 wr2 wdf-le1 ) ACACFBCFCABCDGBCEHIJ $.
  $}

  ${
    wlbtr.1 $e |- ( a =<2 b ) = 1 $.
    wlbtr.2 $e |- ( b == c ) = 1 $.
    $( Transitive inference.  (Contributed by NM, 13-Oct-1997.) $)
    wlbtr $p |- ( a =<2 c ) = 1 $=
      ( wa wr1 wlan wdf2le2 wr2 wdf2le1 ) ACACFABFACBABCEGHABDIJK $.
  $}

  ${
    wle3tr1.1 $e |- ( a =<2 b ) = 1 $.
    wle3tr1.2 $e |- ( c == a ) = 1 $.
    wle3tr1.3 $e |- ( d == b ) = 1 $.
    $( Transitive inference useful for introducing definitions.  (Contributed
       by NM, 13-Oct-1997.) $)
    wle3tr1 $p |- ( c =<2 d ) = 1 $=
      ( wbltr wr1 wlbtr ) CBDCABFEHDBGIJ $.
  $}

  ${
    wle3tr2.1 $e |- ( a =<2 b ) = 1 $.
    wle3tr2.2 $e |- ( a == c ) = 1 $.
    wle3tr2.3 $e |- ( b == d ) = 1 $.
    $( Transitive inference useful for eliminating definitions.  (Contributed
       by NM, 13-Oct-1997.) $)
    wle3tr2 $p |- ( c =<2 d ) = 1 $=
      ( wr1 wle3tr1 ) ABCDEACFHBDGHI $.
  $}

  ${
    wbile.1 $e |- ( a == b ) = 1 $.
    $( Biconditional to l.e.  (Contributed by NM, 13-Oct-1997.) $)
    wbile $p |- ( a =<2 b ) = 1 $=
      ( wo wr5-2v oridm bi1 wr2 wdf-le1 ) ABABDBBDZBABBCEJBBFGHI $.
  $}

  ${
    wlebi.1 $e |- ( a =<2 b ) = 1 $.
    wlebi.2 $e |- ( b =<2 a ) = 1 $.
    $( L.e. to biconditional.  (Contributed by NM, 13-Oct-1997.) $)
    wlebi $p |- ( a == b ) = 1 $=
      ( wo wdf-le2 wr1 ax-a2 bi1 wr2 ) AABEZBABAEZKLABADFGLKBAHIJABCFJ $.
  $}

  ${
    wle2.1 $e |- ( a =<2 b ) = 1 $.
    wle2.2 $e |- ( c =<2 d ) = 1 $.
    $( Disjunction of 2 l.e.'s.  (Contributed by NM, 13-Oct-1997.) $)
    wle2or $p |- ( ( a v c ) =<2 ( b v d ) ) = 1 $=
      ( wo wleror ax-a2 bi1 wle3tr1 wletr ) ACGBCGZBDGZABCEHCBGZDBGZMNCDBFHMOBC
      IJNPBDIJKL $.

    $( Conjunction of 2 l.e.'s.  (Contributed by NM, 13-Oct-1997.) $)
    wle2an $p |- ( ( a ^ c ) =<2 ( b ^ d ) ) = 1 $=
      ( wa wleran ancom bi1 wle3tr1 wletr ) ACGBCGZBDGZABCEHCBGZDBGZMNCDBFHMOBC
      IJNPBDIJKL $.
  $}

  $( Half of distributive law.  (Contributed by NM, 13-Oct-1997.) $)
  wledi $p |- ( ( ( a ^ b ) v ( a ^ c ) ) =<2
        ( a ^ ( b v c ) ) ) = 1 $=
    ( wa wo anidm bi1 wr1 wlea wle2or oridm wlbtr ancom wbltr wle2an ) ABDZACDZ
    EZRRDZABCEZDSRSRRFGHRARTRAAEZAPAQAABIACIJUAAAKGLPBQCPBADZBPUBABMGBAINQCADZC
    QUCACMGCAINJON $.

  $( Half of distributive law.  (Contributed by NM, 13-Oct-1997.) $)
  wledio $p |- ( ( a v ( b ^ c ) ) =<2
       ( ( a v b ) ^ ( a v c ) ) ) = 1 $=
    ( wa wo anidm bi1 wr1 wleo wle2an wbltr ax-a2 wlbtr wle2or oridm ) ABCDZEAB
    EZACEZDZSEZSASPSAAADZSUAAUAAAFGHAQARABIACIJKBQCRBBAEZQBAIUBQBALGMCCAEZRCAIU
    CRCALGMJNTSSOGM $.

  $( Commutation with 0.  Kalmbach 83 p. 20.  (Contributed by NM,
     13-Oct-1997.) $)
  wcom0 $p |- C ( a , 0 ) = 1 $=
    ( wf wa wn wo comm0 df-c2 bi1 wdf-c1 ) ABAABCABDCEABAFGHI $.

  $( Commutation with 1.  Kalmbach 83 p. 20.  (Contributed by NM,
     13-Oct-1997.) $)
  wcom1 $p |- C ( 1 , a ) = 1 $=
    ( wt wa wn wo comm1 df-c2 bi1 wdf-c1 ) BABBACBADCEBAAFGHI $.

  ${
    wlecom.1 $e |- ( a =<2 b ) = 1 $.
    $( Comparable elements commute.  Beran 84 2.3(iii) p. 40.  (Contributed by
       NM, 13-Oct-1997.) $)
    wlecom $p |- C ( a , b ) = 1 $=
      ( wn wa wo orabs bi1 wr1 wdf2le2 wr5-2v wr2 wdf-c1 ) ABAAABDZEZFZABEZOFPA
      PAANGHIAQOQAABCJIKLM $.
  $}

  ${
    wbctr.1 $e |- ( a == b ) = 1 $.
    wbctr.2 $e |- C ( b , c ) = 1 $.
    $( Transitive inference.  (Contributed by NM, 13-Oct-1997.) $)
    wbctr $p |- C ( a , c ) = 1 $=
      ( wa wn wo wdf-c2 wran w2or w3tr1 wdf-c1 ) ACBBCFZBCGZFZHAACFZAOFZHBCEIDQ
      NRPABCDJABODJKLM $.
  $}

  ${
    wcbtr.1 $e |- C ( a , b ) = 1 $.
    wcbtr.2 $e |- ( b == c ) = 1 $.
    $( Transitive inference.  (Contributed by NM, 13-Oct-1997.) $)
    wcbtr $p |- C ( a , c ) = 1 $=
      ( wa wn wo wdf-c2 wlan wr4 w2or wr2 wdf-c1 ) ACAABFZABGZFZHACFZACGZFZHABD
      IORQTBCAEJPSABCEKJLMN $.
  $}

  $( Weak commutation law.  (Contributed by NM, 13-Oct-1997.) $)
  wcomorr $p |- C ( a , ( a v b ) ) = 1 $=
    ( wo wleo wlecom ) AABCABDE $.

  $( Weak commutation law.  (Contributed by NM, 13-Oct-1997.) $)
  wcoman1 $p |- C ( ( a ^ b ) , a ) = 1 $=
    ( wa wlea wlecom ) ABCAABDE $.

  ${
    wcomcom.1 $e |- C ( a , b ) = 1 $.
    $( Commutation is symmetric.  Kalmbach 83 p. 22.  (Contributed by NM,
       13-Oct-1997.) $)
    wcomcom $p |- C ( b , a ) = 1 $=
      ( wcmtr wt cmtrcom ax-r2 ) BADABDEBAFCG $.

    $( Commutation equivalence.  Kalmbach 83 p. 23.  (Contributed by NM,
       13-Oct-1997.) $)
    wcomcom2 $p |- C ( a , b ' ) = 1 $=
      ( wn wa wo wdf-c2 ax-a1 bi1 wlan wr5-2v wr2 ax-a2 wdf-c1 ) ABDZAAODZEZAOE
      ZFZRQFZAABEZRFSABCGUAQRBPABPBHIJKLSTQRMILN $.

    $( Commutation equivalence.  Kalmbach 83 p. 23.  (Contributed by NM,
       13-Oct-1997.) $)
    wcomcom3 $p |- C ( a ' , b ) = 1 $=
      ( wn wcomcom wcomcom2 ) BADBAABCEFE $.

    $( Commutation equivalence.  Kalmbach 83 p. 23.  (Contributed by NM,
       13-Oct-1997.) $)
    wcomcom4 $p |- C ( a ' , b ' ) = 1 $=
      ( wn wcomcom3 wcomcom2 ) ADBABCEF $.

    $( Commutation dual.  Kalmbach 83 p. 23.  (Contributed by NM,
       13-Oct-1997.) $)
    wcomd $p |- ( a == ( ( a v b ) ^ ( a v b ' ) ) ) = 1 $=
      ( wn wa wo wcomcom4 wdf-c2 wcon3 oran bi1 wcon2 w2an wr1 wr2 ) AADZBDZEZP
      QDEZFZDZABFZAQFZEZATPQABCGHIUARDZSDZEZUDTUGTUGDRSJKLUDUGUBUEUCUFUBUEABJKU
      CUFAQJKMNOO $.

    $( Lemma 3(ii) of Kalmbach 83 p. 23.  (Contributed by NM, 13-Oct-1997.) $)
    wcom3ii $p |- ( ( a ^ ( a ' v b ) ) == ( a ^ b ) ) = 1 $=
      ( wa wn wo wcomcom wcomd wlan anass bi1 wr1 ax-a2 anabs wr2 w2an ) ABDZAA
      EZBFZDZQABAFZBRFZDZDZTBUCABAABCGHIUDAUADZUBDZTUFUDUFUDAUAUBJKLUEAUBSUEAAB
      FZDZAUAUGAUAUGBAMKIUHAABNKOUBSBRMKPOOL $.
  $}

  ${
    wcomcom5.1 $e |- C ( a ' , b ' ) = 1 $.
    $( Commutation equivalence.  Kalmbach 83 p. 23.  (Contributed by NM,
       13-Oct-1997.) $)
    wcomcom5 $p |- C ( a , b ) = 1 $=
      ( wn wa wo wcomcom4 wdf-c2 ax-a1 bi1 w2an w2or w3tr1 wdf-c1 ) ABADZDZPBDZ
      DZEZPRDZEZFAABEZAQEZFPROQCGHAPAIJZUBSUCUAAPBRUDBRBIJKAPQTUDQTQIJKLMN $.
  $}

  ${
    wcomdr.1 $e |- ( a == ( ( a v b ) ^ ( a v b ' ) ) ) = 1 $.
    $( Commutation dual.  Kalmbach 83 p. 23.  (Contributed by NM,
       13-Oct-1997.) $)
    wcomdr $p |- C ( a , b ) = 1 $=
      ( wn wa wo df-a bi1 oran wcon2 w2or wr4 wr2 wdf-c1 wcomcom5 ) ABADZBDZAPQ
      EZPQDEZFZAABFZAQFZEZTDZCUCUADZUBDZFZDZUDUCUHUAUBGHUGTUERUFSUARUARDABIHJUB
      SUBSDAQIHJKLMMJNO $.
  $}

  ${
    wcom3i.1 $e |- ( ( a ^ ( a ' v b ) ) == ( a ^ b ) ) = 1 $.
    $( Lemma 3(i) of Kalmbach 83 p. 23.  (Contributed by NM, 13-Oct-1997.) $)
    wcom3i $p |- C ( a , b ) = 1 $=
      ( wn wa anor1 bi1 wcon2 wran ancom wr2 wlor wlea wom4 ax-a2 w3tr2 wdf-c1
      wo ) ABABDZEZTDZAEZRTABEZRZAUCTRZUBUCTUBAADBRZEZUCUBUFAEZUGUAUFATUFTUFDAB
      FGHIUHUGUFAJGKCKLTAASMNUDUETUCOGPQ $.
  $}

  ${
    wfh.1 $e |- C ( a , b ) = 1 $.
    wfh.2 $e |- C ( a , c ) = 1 $.
    $( Weak structural analog of Foulis-Holland Theorem.  (Contributed by NM,
       13-Oct-1997.) $)
    wfh1 $p |- ( ( a ^ ( b v c ) ) ==
               ( ( a ^ b ) v ( a ^ c ) ) ) = 1 $=
      ( wa wo wledi wn bi1 df-a wr1 wcon3 wr2 w2an wcomcom2 wcom3ii anandi wlan
      wf ancom w2or wcon2 anass w3tr1 an12 oran dff an0 wom5 ) ABFZACFZGZABCGZF
      ZUMUOABCHUOUMIZFZAUNBIZCIZFZFZFZTUQUNAFZAIZURGZVDUSGZFZFZVBUOVCUPVGUOVCAU
      NUAJUMVGUMVEIZVFIZGZVGIUKVIULVJUKVIABKJULVJACKJUBVKVGVGVKIZVGVLVEVFKJLMNU
      COVHUNAUTFZFZVBVHUNAVGFZFZVNVHVPUNAVGUDJVOVMUNAVEFZAVFFZFZAURFZAUSFZFZVOV
      MVQVTVRWAAURABDPQAUSACEPQOVOVSAVEVFRJVMWBAURUSRJUESNVNVBUNAUTUFJNNVBATFZT
      VATAVAUNUNIZFZTUTWDUNUTUNUNUTIZUNWFBCUGJLMSTWETWEUNUHJLNSWCTAUIJNNUJL $.

    $( Weak structural analog of Foulis-Holland Theorem.  (Contributed by NM,
       13-Oct-1997.) $)
    wfh2 $p |- ( ( b ^ ( a v c ) ) ==
               ( ( b ^ a ) v ( b ^ c ) ) ) = 1 $=
      ( wa wo wledi wn wf oran bi1 wcon2 wran wr2 wlan an4 wcom3ii anass wr1
      df-a wr4 wcomcom wcomcom2 ancom ax-a1 wr5-2v wcomcom3 an12 dff w3tr1 wom5
      an0 ) BAFZBCFZGZBACGZFZUPURBACHURUPIZFZAIZCBUOIZFZFZFZJUTVACFZVCFZVEUTVAU
      QFZVCFZVGUTVABFZUQVBFZFZVIUTURBIVAGZVBFZFZVLUSVNURUPVNUPUNIZVBFZIZVNIUPVR
      UNUOKLVQVNVPVMVBUNVMUNVMIBAUALMNUBOMPVOBVMFZVKFZVLVOVTBUQVMVBQLVSVJVKVSBV
      AFZVJBVABAABDUCUDRWAVJBVAUELONOOVLVIVABUQVBQLOVHVFVCVHVAVAIZCGZFVFUQWCVAA
      WBCAWBAUFLUGPVACACEUHRONOVGVEVACVCSLOVEVAJFZJVDJVABCVBFFZUOVBFZVDJWFWEWFW
      EBCVBSLTVDWECBVBUILJWFUOUJLUKPWDJVAUMLOOULT $.

    $( Weak structural analog of Foulis-Holland Theorem.  (Contributed by NM,
       13-Oct-1997.) $)
    wfh3 $p |- ( ( a v ( b ^ c ) ) ==
               ( ( a v b ) ^ ( a v c ) ) ) = 1 $=
      ( wa wo wn wcomcom4 wfh1 anor2 bi1 df-a wr1 wlor wr4 wr2 oran w2an w3tr2
      wcon1 ) ABCFZGZABGZACGZFZAHZBHZCHZGZFZUGUHFZUGUIFZGZUCHZUFHZUGUHUIABDIACE
      IJUKAUJHZGZHZUOUKUSAUJKLURUCUQUBAUBUQUBUQBCMLNOPQUNULHZUMHZFZHZUPUNVCULUM
      RLVBUFUFVBUDUTUEVAUDUTABRLUEVAACRLSNPQTUA $.

    $( Weak structural analog of Foulis-Holland Theorem.  (Contributed by NM,
       13-Oct-1997.) $)
    wfh4 $p |- ( ( b v ( a ^ c ) ) ==
               ( ( b v a ) ^ ( b v c ) ) ) = 1 $=
      ( wa wo wn wcomcom4 wfh2 anor2 bi1 df-a wr1 wlor wr4 wr2 oran w2an w3tr2
      wcon1 ) BACFZGZBAGZBCGZFZBHZAHZCHZGZFZUGUHFZUGUIFZGZUCHZUFHZUHUGUIABDIACE
      IJUKBUJHZGZHZUOUKUSBUJKLURUCUQUBBUBUQUBUQACMLNOPQUNULHZUMHZFZHZUPUNVCULUM
      RLVBUFUFVBUDUTUEVAUDUTBARLUEVABCRLSNPQTUA $.

    $( Thm. 4.2 Beran p. 49.  (Contributed by NM, 10-Nov-1998.) $)
    wcom2or $p |- C ( a , ( b v c ) ) = 1 $=
      ( wo wa wn wcomcom wdf-c2 ancom 2or bi1 wr2 w2or or4 wfh1 wcomcom3 wdf-c1
      wr1 ) BCFZAUAAUAABGZACGZFZAHZBGZUECGZFZFZUAAGZUAUEGZFZUAUBUFFZUCUGFZFZUIB
      UMCUNBBAGZBUEGZFZUMBAABDIJURUMUPUBUQUFBAKBUEKLMNCCAGZCUEGZFZUNCAACEIJVAUN
      USUCUTUGCAKCUEKLMNOUOUIUBUFUCUGPMNULUIUJUDUKUHUJAUAGZUDUJVBUAAKMABCDEQNUK
      UEUAGZUHUKVCUAUEKMUEBCABDRACERQNOTNSI $.

    $( Thm. 4.2 Beran p. 49.  (Contributed by NM, 10-Nov-1998.) $)
    wcom2an $p |- C ( a , ( b ^ c ) ) = 1 $=
      ( wa wn wo wcomcom4 wcom2or df-a con2 ax-r1 bi1 wcbtr wcomcom5 ) ABCFZAGZ
      BGZCGZHZQGZRSTABDIACEIJUAUBUBUAQUABCKLMNOP $.
  $}

  $( Negated biconditional (distributive form) (Contributed by NM,
     13-Oct-1997.) $)
  wnbdi $p |- ( ( a == b ) ' ==
             ( ( ( a v b ) ^ a ' ) v ( ( a v b ) ^ b ' ) ) ) = 1 $=
    ( tb wn wo wa dfnb bi1 wcomorr wcomcom wcomcom2 ax-a2 wcbtr wfh1 wr2 ) ABCD
    ZABEZADZBDZEFZQRFQSFEPTABGHQRSQAAQABIJKQBBQBBAEZQBAIUAQBALHMJKNO $.

  $( Lemma for KA14 soundness.  (Contributed by NM, 25-Oct-1997.) $)
  wlem14 $p |- ( ( ( a ^ b ' ) v a ' ) ' v
            ( ( a ^ b ' ) v ( ( a ' ^ ( ( a v b ' ) ^ ( a v b ) ) )
               v ( a ' ^ ( ( a v b ' ) ^ ( a v b ) ) ' ) ) ) ) = 1 $=
    ( wn wa wo wt df-t ax-r1 ax-a2 bi1 wwbmpr wlan anidm wr1 wleo wle2an wlecom
    wbltr wcomcom3 wlor wcomcom4 wfh1 an1 w3tr2 ) ABCZDZACZEZCZUFUGAUEEZABEZDZD
    UGULCZDEZEZEUIUHEZUPUHUIEZFUQUHGHUPUQUIUHIJKUOUHUIUNUGUFUGULUMEZDUGFDZUNUGU
    RFUGURFFURULGHJLUGULUMAULAULAAADZULUTAUTAAMJNAUJAUKAUEOABOPRQZSAULVAUAUBUSU
    GUGUCJUDTTK $.

  ${
    wr5.1 $e |- ( a == b ) = 1 $.
    $( Proof of weak orthomodular law from weaker-looking equivalent, ~ wom3 ,
       which in turn is derived from ~ ax-wom .  (Contributed by NM,
       25-Oct-1997.) $)
    wr5 $p |- ( ( a v c ) == ( b v c ) ) = 1 $=
      ( wr5-2v ) ABCDE $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Kalmbach axioms (soundness proofs) that require WOML
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( >>>Remove "id" when bug is fixed. $)
  $( Soundness theorem for Kalmbach's quantum propositional logic axiom KA2.
     (Contributed by NM, 10-Nov-1998.) $)
  ska2 $p |- ( ( a == b ) ' v ( ( b == c ) ' v ( a == c ) ) ) = 1 $=
    ( wn wo wa wt ax-a3 ax-r1 ax-a2 or12 lor ax-r2 wcomorr bi1 wcomcom wcomcom2
    bltr ancom wr2 tb dfnb dfb 2or id le1 df-t oran3 leor le2or lelor letr lebi
    orordi wcbtr wfh4 or1 ran an1 or32 w2or wlor orordir anor3 wcom2or oran leo
    wwbmpr wr5-2v wcomcom3 wfh1 wwbmp ax-r5 ledi leror ) ABUADZBCUADZACUAZEZEAB
    EZADZBDZEFZBCEZWBCDZEZFZACFZWAWEFZEZEZEZGVPWCVSWKABUBVQWGVRWJBCUBACUCUDUDWL
    WCWGEZWJEZGWNWLWCWGWJHIWNWNGWNUEWNGWNUFGVTWAFZWBVTFZEZWBWDFZWDWEFZEZEZWJEZW
    NGWOWPWREZWSEZEZWJEZXBXFGWOWBVTWDEZFZWSEZEZWJEZXFXKWJXJEZGXJWJJXLWOWJXIEZEZ
    GWJWOXIKXNWOWHWIWBEZWSEZEZEZXRWHWOXPEZEZGWOWHXPKXTWHWIWBWOEZWBWSEZEZEZEZGXS
    YDWHXSXOWOWSEZEZYDWOXOWSKYGWIWBYFEZEYDWIWBYFHYHYCWIWBWOWSUNLMMLYEWHWIWBWAEZ
    WFEZEZEZYLWIWHYJEZEZGWHWIYJKYNGYNUFGYMYNGWHWAWEEZEZYMGWHWHDZEZYPWHUGYPYRYOY
    QWHACUHLIMYOYJWHWAYIWEWFWAWBUIWEWBUIUJUKRYMWIUIULUMMYDYKWHYCYJWIYAYIYBWFYAW
    BVTEZYIFZYIVTWBWAVTBBVTBBAEZVTBANUUAVTBAJOUOZPQVTAAVTABNPQUPYTYIYTGYIFZYIYS
    GYIYSAWBBEZEZGWBABKUUEAGEGUUDGAUUDBWBEZGWBBJGUUFBUGIZMLAUQMMURUUCYIGFYIGYIS
    YIUSMMOTYBWBWDEZWFFZWFWDWBWEWDBBWDBCNZPQWDCCWDCCBEZWDCBNUUKWDCBJZOUOPQUPUUI
    WFUUIGWFFZWFUUHGWFUUHWDWBEZGWBWDJUUNUUFCEZGBCWBUTUUOCUUFEZGUUFCJUUPCGEGUUFG
    CUUGLCUQMMMMURUUMWFGFWFGWFSWFUSMMOTVAVBVBVHMMXMXQWOXMWHWIXIEZEZXQXMUURWHWIX
    IHOUUQXPWHUUQWIXHEZWSEZXPUUQUUTUUTUUQWIXHWSHIOUUSXOWSUUSWIXGWBFZEZXOUUSUVBX
    HUVAWIWBXGSLOUVBWIXGEZXOFZXOXGWIWBXGACEZDZWIXGUVEUVEXGUVEUVEBEZXGUVEBNUVGXG
    UVGVTUUKEXGACBVCUUKWDVTUULLMOUOPQUVFWIWIUVFACVDIOUOXGBBXGBVTWDUUBUUJVEPQUPU
    VDXOUVDGXOFZXOUVCGXOUVCGUVCUFGWIUVEEZUVCGWIWIDZEUVIWIUGUVJUVEWIUVEUVJACVFIL
    MUVEXGWIAVTCWDABVGCBUIUJUKRUMURUVHXOGFXOGXOSXOUSMMOTTVITVBTVBVHMMXJXEWJXIXD
    WOXHXCWSWBVTWDBVTUUBVJBWDUUJVJVKVIVBVIVLIXEXAWJXEWQWREZWSEZXAXEWOXCEZWSEZUV
    LUVNXEWOXCWSHIUVMUVKWSUVKUVMWOWPWRHIVMMWQWRWSHMVMMXAWMWJWQWCWTWGWQWOVTWBFZE
    WCWPUVOWOWBVTSLVTWAWBVNRWTWDWBFZWSEWGWRUVPWSWBWDSVMWDWBWEVNRUJVORUMMMM $.

  $( Soundness theorem for Kalmbach's quantum propositional logic axiom KA4.
     (Contributed by NM, 9-Nov-1998.) $)
  ska4 $p |- ( ( a == b ) ' v ( ( a ^ c ) == ( b ^ c ) ) ) = 1 $=
    ( tb wn wa wo wt 2or ax-a2 le1 df-t lor ax-r1 ax-r2 lea lecon leror wcomcom
    wcomcom2 dfnb dfb ax-a3 oran le2an bltr lebi ran ancom an1 3tr anandir lear
    oran3 ax-r5 ler2an lelor wlea wleo wletr wlecom wlbtr wcom2an wcomorr wcbtr
    bi1 wcom2or wfh4 wlor wwbmpr ) ABDEZACFZBCFZDZGABGZAEZBEZGZFZVLVMFZVLEZVMEZ
    FZGZGWDVSGZHVKVSVNWDABUAVLVMUBIVSWDJWEVTWCVSGZGZHVTWCVSUCWGVTWCVOGZWCVRGZFZ
    GZWKVTWIGZHWJWIVTWJHWIFWIHFWIWHHWIWHHWHKHVPVQFZVOGZWHHWMWMEZGZWNWMLWNWPVOWO
    WMABUDMNOWMWCVOVPWAVQWBVLAACPQVMBBCPQUERUFUGUHHWIUIWIUJUKMWLHWLKHVTCEZVRGZG
    ZWLHABFZCFZXAEZGWSXALXAVTXBWRABCULXBVRWQGZWRXCXBXCWTEZWQGXBVRXDWQABUNUOWTCU
    NONVRWQJOIOWRWIVTWQWCVRWQWAWBVLCACUMQVMCBCUMQUPRUQUFUGOWFWJVTVOWCVRVOWAWBVO
    VLVLVOVLVOVLAVOACURABUSUTVASTVOVMVMVOVMVOVMBVOBCURBBAGZVOBAUSXEVOBAJVFZVBUT
    VASTVCVOVPVQVOAAVOABVDSTVOBBVOBXEVOBAVDXFVESTVGVHVIVJOUK $.

  $( Weak orthomodular law for study of weakly orthomodular lattices.
     (Contributed by NM, 13-Nov-1998.) $)
  wom2 $p |- a =< ( ( a == b ) ' v ( ( a v c ) == ( b v c ) ) ) $=
    ( wt tb wn wo le1 wa conb ax-r4 oran 2bi ax-r1 ax-r2 2or ska4 lbtr ) ADABEZ
    FZACGZBCGZEZGZAHUDDUDAFZBFZEZFZUECFZIZUFUIIZEZGDTUHUCULSUGABJKUCUJFZUKFZEZU
    LUAUMUBUNACLBCLMULUOUJUKJNOPUEUFUIQONR $.

  $( 3-variable version of weakly orthomodular law.  It is proved from a
     weaker-looking equivalent, ~ wom2 , which in turn is proved from
     ~ ax-wom .  (Contributed by NM, 25-Oct-1997.) $)
  ka4ot $p |- ( ( a == b ) ' v ( ( a v c ) == ( b v c ) ) ) = 1 $=
    ( tb wn wo wt le1 wom2 bicom ax-r4 2or lbtr le2or oridm leror ka4lemo ax-a3
    lor ax-r2 le3tr2 lebi ) ABDZEZACFZBCFZDZFZGUHHABFZUGFUHUGFZGUHUIUHUGUIUHUHF
    UHAUHBUHABCIBBADZEZUFUEDZFUHBACIULUDUMUGUKUCBAJKUFUEJLMNUHOMPABCQUJUDUGUGFZ
    FUHUDUGUGRUNUGUDUGOSTUAUB $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Weak orthomodular law variants
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Variant of weakly orthomodular law.  (Contributed by NM, 14-Nov-1998.) $)
  woml6 $p |- ( ( a ->1 b ) ' v ( a ->2 b ) ) = 1 $=
    ( wn wo wa wt df-a lor ax-r2 ax-r1 2or ax-a2 ancom wcomorr wcomcom wcomcom3
    bi1 wcomcom5 df-t 3tr wi1 wi2 df-i1 ax-r4 df-i2 ax-r5 ax-a3 tb wcbtr wr5-2v
    1b wfh4 or12 or1 ran an1 anor3 wr2 wr1 3tr2 ) ABUAZCZABUBZDAACZBCZDZEZBVDVE
    EZDZDZFVBVGVCVIVBVDVFCZDZCZVGVAVLVAVDABEZDVLABUCVNVKVDABGHIUDVGVMAVFGJIABUE
    KVGBDZVHDBVFAEZDZVHDZVJFVOVQVHVOBVGDVQVGBLVGVPBAVFMHIUFVGBVHUGVRFVRUHZFVSVR
    VRUKJVRFVRBVFDZBADZEZVHDZFVQWBVHVFBAVFBVFVEVEVFVEVEVDDZVFVEVDNWDVFVEVDLQUIO
    PRVFAVFVDVDVFVDVENOPRULUJWCFWCABDZWECZDZFWBWEVHWFWBWAFEZWAWEWBFWAEWHVTFWAVT
    VDBVEDZDZVDFDZFBVDVEUMWKWJFWIVDBSHJVDUNTUOFWAMIWAUPBALTABUQKFWGWESJIQURUSIU
    TI $.

  $( Variant of weakly orthomodular law.  (Contributed by NM, 14-Nov-1998.) $)
  woml7 $p |- ( ( ( a ->2 b ) ^ ( b ->2 a ) ) ' v ( a == b ) ) = 1 $=
    ( wi2 wa wn tb wo wt df-i2 ax-a2 ax-r2 ancom ax-r5 3tr 2an wcoman1 wcomcom3
    bi1 wcomcom5 wr2 ax-r4 id dfb 2or 1b ax-r1 df-t wa2 wbctr wfh3 wr4 wr5-2v )
    ABCZBACZDZEZABFZGAEZBEZDZAGZUTBGZDZEZABDZUTGZGZHVGFZHUPVDUQVFUPVDVDUOVCUOVB
    VADVCUMVBUNVAUMBUTGVBABIBUTJKUNAUSURDZGVIAGVABAIAVIJVIUTAUSURLMNOVBVALKUAVD
    UBKABUCUDVHVGVGUEUFHVFEZVFGZVGHVKHVFVJGVKVFUGVFVJJKRVJVDVFVFVCVFUTVEGVCVEUT
    UHUTABUTAUTURURUSPQSUTBUTUSUTVIUSUTVIURUSLRUSURPUIQSUJTUKULTN $.

  ${
    ortha.1 $e |- a =< b ' $.
    $( Property of orthogonality.  (Contributed by NM, 10-Mar-2002.) $)
    ortha $p |- ( a ^ b ) = 0 $=
      ( wa wf wn lecon3 lelan dff ax-r1 lbtr le0 lebi ) ABDZENAAFZDZEBOAABCGHEP
      AIJKNLM $.
  $}


$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
        Orthomodular lattices
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Orthomodular law
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    r3.1 $e |- ( c v c ' ) = ( ( a ' v b ' ) ' v ( a v b ) ' ) $.
    $( Orthomodular law - when added to an ortholattice, it makes the
       ortholattice an orthomodular lattice.  See ~ r3a for a more compact
       version.  (Contributed by NM, 12-Aug-1997.) $)
    ax-r3 $a |- a = b $.
  $}

  ${
    r3a.1 $e |- 1 = ( a == b ) $.
    $( Orthomodular law restated.  (Contributed by NM, 12-Aug-1997.) $)
    r3a $p |- a = b $=
      ( wt tb wn wo df-t df-b 3tr2 ax-r3 ) ABADABEAAFZGLBFGFABGFGCAHABIJK $.
  $}

  ${
    wed.1 $e |- a = b $.
    wed.2 $e |- ( a == b ) = ( c == d ) $.
    $( Weak equivalential detachment (WBMP).  (Contributed by NM,
       10-Aug-1997.) $)
    wed $p |- c = d $=
      ( wt tb 1bi ax-r2 r3a ) CDGABHCDHABEIFJK $.
  $}

  ${
    r3b.1 $e |- ( c v c ' ) = ( a == b ) $.
    $( Orthomodular law from weak equivalential detachment (WBMP).
       (Contributed by NM, 10-Aug-1997.) $)
    r3b $p |- a = b $=
      ( wt tb wn wo df-t ax-r2 1b wed ) EABFZABECCGHMCIDJMKL $.
  $}

  ${
    lem3.1.1 $e |- ( a v b ) = b $.
    lem3.1.2 $e |- ( b ' v a ) = 1 $.
    $( Lemma used in proof of Thm. 3.1 of Pavicic 1993.  (Contributed by NM,
       12-Aug-1997.) $)
    lem3.1 $p |- a = b $=
      ( tb wt wlem3.1 ax-r1 r3a ) ABABEFABCDGHI $.

    $( Lemma used in proof of Thm. 3.1 of Pavicic 1993.  (Contributed by NM,
       12-Aug-1997.) $)
    lem3a.1 $p |- ( a v b ) = a $=
      ( wo lem3.1 ax-r1 lor oridm ax-r2 ) ABEAAEABAAABABCDFGHAIJ $.
  $}

  $( Orthomodular law.  Compare Thm. 1 of Pavicic 1987.  (Contributed by NM,
     12-Aug-1997.) $)
  oml $p |- ( a v ( a ' ^ ( a v b ) ) ) = ( a v b ) $=
    ( wn wo wa omlem1 omlem2 lem3.1 ) AACABDZEDIABFABGH $.

  $( Orthomodular law.  (Contributed by NM, 2-Nov-1997.) $)
  omln $p |- ( a ' v ( a ^ ( a ' v b ) ) ) = ( a ' v b ) $=
    ( wn wo wa ax-a1 ran lor oml ax-r2 ) ACZAKBDZEZDKKCZLEZDLMOKANLAFGHKBIJ $.

  $( Orthomodular law.  (Contributed by NM, 7-Nov-1997.) $)
  omla $p |- ( a ^ ( a ' v ( a ^ b ) ) ) = ( a ^ b ) $=
    ( wn wa wo df-a ax-r1 lor ax-r4 ax-r2 omln con2 3tr1 con1 ) AACZABDZEZDZPOQ
    CZEZOBCZEZRCPCTOAUBDZEUBSUCOUCSUCOUBCZEZCSAUBFUEQUDPOPUDABFZGHIJGHAUAKJRTAQ
    FLPUBUFLMN $.

  $( Orthomodular law.  (Contributed by NM, 7-Nov-1997.) $)
  omlan $p |- ( a ' ^ ( a v ( a ' ^ b ) ) ) = ( a ' ^ b ) $=
    ( wn wa wo ax-a1 ax-r5 lan omla ax-r2 ) ACZAKBDZEZDKKCZLEZDLMOKANLAFGHKBIJ
    $.

  $( Orthomodular law.  (Contributed by NM, 16-Nov-1997.) $)
  oml5 $p |- ( ( a ^ b ) v ( ( a ^ b ) ' ^ ( b v c ) ) )
             = ( b v c ) $=
    ( wa wn wo oml ax-a3 ancom lor orabs ax-r2 ax-r5 or12 3tr2 lan 3tr1 ) ABDZR
    EZBCFZDZFZBRFZCFZTRSRTFZDZFUEUBUDRTGUAUFRTUESUDBRCFFZTUEBRCHZUCBCUCBBADZFBR
    UIBABIJBAKLMZBRCNZOPJUDUGUEUHUKLQUJL $.

  $( Orthomodular law.  (Contributed by NM, 16-Nov-1997.) $)
  oml5a $p |- ( ( a v b ) ^ ( ( a v b ) ' v ( b ^ c ) ) )
              = ( b ^ c ) $=
    ( wo wn wa omla anass ax-a2 lan anabs ax-r2 ran an12 3tr2 lor 3tr1 ) ABDZRE
    ZBCFZDZFZBRFZCFZTRSRTFZDZFUEUBUDRTGUAUFRTUESUDBRCFFZTUEBRCHZUCBCUCBBADZFBRU
    IBABIJBAKLMZBRCNZOPJUDUGUEUHUKLQUJL $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Relationship analogues using OML (ordering; commutation)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    oml2.1 $e |- a =< b $.
    $( Orthomodular law.  Kalmbach 83 p. 22.  (Contributed by NM,
       27-Aug-1997.) $)
    oml2 $p |- ( a v ( a ' ^ b ) ) = b $=
      ( wn wo wa oml df-le2 lan lor 3tr2 ) AADZABEZFZEMALBFZEBABGNOAMBLABCHZIJP
      K $.
  $}

  ${
    oml3.1 $e |- a =< b $.
    oml3.2 $e |- ( b ^ a ' ) = 0 $.
    $( Orthomodular law.  Kalmbach 83 p. 22.  (Contributed by NM,
       27-Aug-1997.) $)
    oml3 $p |- a = b $=
      ( wf wo wn wa ax-r1 ancom ax-r2 lor or0 oml2 3tr2 ) AEFAAGZBHZFABEQAEBPHZ
      QREDIBPJKLAMABCNO $.
  $}

  ${
    comcom.1 $e |- a C b $.
    $( Commutation is symmetric.  Kalmbach 83 p. 22.  (Contributed by NM,
       27-Aug-1997.) $)
    comcom $p |- b C a $=
      ( wa wn wo ax-a2 ran ancom ax-r2 anabs df-c2 df-a anor1 ax-r4 ax-r1 anass
      lan 2or lor con2 3tr1 orabs df-le1 oml2 3tr2 df-c1 ) BAABDZUHEZBDZFZUHAEZ
      BDZFZBBADZBULDZFUNUKUMUJUHULBEZFZULBFZBDZDZURBDUMUJUTBURUTBBULFZDZBUTVBBD
      VCUSVBBULBGHVBBIJBULKJRUMURUSDZBDVAULVDBULUREZUSEZFZEZVDAVGAUHAUQDZFVGABC
      LUHVEVIVFABMZABNSJOVDVHURUSMPJHURUSBQJUIURBUHURVJUAHUBTPUHBUHBUHBFBUHFZBU
      HBGVKBUOFBUHUOBABIZTBAUCJJUDUEUHUOUMUPVLULBISUFUG $.

    $( Commutation equivalence.  Kalmbach 83 p. 23.  (Contributed by NM,
       27-Aug-1997.) $)
    comcom3 $p |- a ' C b $=
      ( wn comcom comcom2 ) BADBAABCEFE $.

    $( Commutation equivalence.  Kalmbach 83 p. 23.  (Contributed by NM,
       27-Aug-1997.) $)
    comcom4 $p |- a ' C b ' $=
      ( wn comcom3 comcom2 ) ADBABCEF $.

    $( Commutation dual.  Kalmbach 83 p. 23.  (Contributed by NM,
       27-Aug-1997.) $)
    comd $p |- a = ( ( a v b ) ^ ( a v b ' ) ) $=
      ( wn wa wo comcom4 df-c2 con3 oran con2 2an ax-r1 ax-r2 ) AADZBDZEZOPDEZF
      ZDZABFZAPFZEZASOPABCGHITQDZRDZEZUCSUFQRJKUCUFUAUDUBUEABJAPJLMNN $.

    $( Lemma 3(ii) of Kalmbach 83 p. 23.  (Contributed by NM, 27-Aug-1997.) $)
    com3ii $p |- ( a ^ ( a ' v b ) ) = ( a ^ b ) $=
      ( wa wn wo comcom comd lan anass ax-r1 ax-a2 anabs ax-r2 2an ) ABDZAAEZBF
      ZDZPABAFZBQFZDZDZSBUBABAABCGHIUCATDZUADZSUEUCATUAJKUDAUARUDAABFZDATUFABAL
      IABMNBQLONNK $.
  $}

  ${
    comcom5.1 $e |- a ' C b ' $.
    $( Commutation equivalence.  Kalmbach 83 p. 23.  (Contributed by NM,
       27-Aug-1997.) $)
    comcom5 $p |- a C b $=
      ( wn wa wo comcom4 df-c2 ax-a1 2an 2or 3tr1 df-c1 ) ABADZDZOBDZDZEZOQDZEZ
      FAABEZAPEZFOQNPCGHAIZUARUBTAOBQUCBIJAOPSUCPIJKLM $.
  $}

  ${
    comcom6.1 $e |- a ' C b $.
    $( Commutation equivalence.  Kalmbach 83 p. 23.  (Contributed by NM,
       26-Nov-1997.) $)
    comcom6 $p |- a C b $=
      ( wn comcom2 comcom5 ) ABADBCEF $.
  $}

  ${
    comcom7.1 $e |- a C b ' $.
    $( Commutation equivalence.  Kalmbach 83 p. 23.  (Contributed by NM,
       26-Nov-1997.) $)
    comcom7 $p |- a C b $=
      ( wn comcom3 comcom5 ) ABABDCEF $.
  $}

  $( Commutation law.  (Contributed by NM, 9-Nov-1997.) $)
  comor1 $p |- ( a v b ) C a $=
    ( wo comorr comcom ) AABCABDE $.

  $( Commutation law.  (Contributed by NM, 9-Nov-1997.) $)
  comor2 $p |- ( a v b ) C b $=
    ( wo ax-a2 comor1 bctr ) ABCBACBABDBAEF $.

  $( Commutation law.  (Contributed by NM, 26-Nov-1997.) $)
  comorr2 $p |- b C ( a v b ) $=
    ( wo comor2 comcom ) ABCBABDE $.

  $( Commutation law.  (Contributed by NM, 26-Nov-1997.) $)
  comanr1 $p |- a C ( a ^ b ) $=
    ( wa coman1 comcom ) ABCAABDE $.

  $( Commutation law.  (Contributed by NM, 26-Nov-1997.) $)
  comanr2 $p |- b C ( a ^ b ) $=
    ( wa coman2 comcom ) ABCBABDE $.

  ${
    comdr.1 $e |- a = ( ( a v b ) ^ ( a v b ' ) ) $.
    $( Commutation dual.  Kalmbach 83 p. 23.  (Contributed by NM,
       27-Aug-1997.) $)
    comdr $p |- a C b $=
      ( wn wa wo df-a oran con2 2or ax-r4 ax-r2 df-c1 comcom5 ) ABADZBDZAOPEZOP
      DEZFZAABFZAPFZEZSDZCUBTDZUADZFZDUCTUAGUFSUDQUERTQABHIUARAPHIJKLLIMN $.
  $}

  ${
    com3i.1 $e |- ( a ^ ( a ' v b ) ) = ( a ^ b ) $.
    $( Lemma 3(i) of Kalmbach 83 p. 23.  (Contributed by NM, 28-Aug-1997.) $)
    com3i $p |- a C b $=
      ( wn wa wo anor1 con2 ran ancom ax-r2 lor lea oml2 ax-a2 3tr2 df-c1 ) ABA
      BDZEZSDZAEZFSABEZFAUBSFUAUBSUAAADBFZEZUBUAUCAEUDTUCASUCABGHIUCAJKCKLSAARM
      NSUBOPQ $.
  $}

  ${
    df2c1.1 $e |- a = ( ( a v b ) ^ ( a v b ' ) ) $.
    $( Dual 'commutes' analogue for ` == ` analogue of ` = ` .  (Contributed by
       NM, 20-Sep-1998.) $)
    df2c1 $p |- a C b $=
      ( wn wa wo df-a anor3 2or ax-r1 ax-r4 ax-r2 con2 df-c1 comcom5 ) ABADZBDZ
      APQEZPQDEZFZAABFZAQFZEZTDZCUCUADZUBDZFZDUDUAUBGUGTTUGRUESUFABHAQHIJKLLMNO
      $.
  $}

  ${
    fh.1 $e |- a C b $.
    fh.2 $e |- a C c $.
    $( Foulis-Holland Theorem.  (Contributed by NM, 29-Aug-1997.) $)
    fh1 $p |- ( a ^ ( b v c ) ) = ( ( a ^ b ) v ( a ^ c ) ) $=
      ( wa wo ledi wn ancom df-a ax-r1 con3 ax-r2 2an comcom2 com3ii anandi lan
      wf 2or con2 anass 3tr1 an12 oran dff an0 oml3 ) ABFZACFZGZABCGZFZULUNABCH
      UNULIZFZAUMBIZCIZFZFZFZTUPUMAFZAIZUQGZVCURGZFZFZVAUNVBUOVFAUMJULVFULVDIZV
      EIZGZVFIUJVHUKVIABKACKUAVJVFVFVJIVDVEKLMNUBOVGUMAUSFZFZVAVGUMAVFFZFVLUMAV
      FUCVMVKUMAVDFZAVEFZFAUQFZAURFZFVMVKVNVPVOVQAUQABDPQAURACEPQOAVDVERAUQURRU
      DSNUMAUSUENNVAATFTUTTAUTUMUMIZFZTUSVRUMUSUMUMUSIBCUFLMSTVSUMUGLNSAUHNNUIL
      $.

    $( Foulis-Holland Theorem.  (Contributed by NM, 29-Aug-1997.) $)
    fh2 $p |- ( b ^ ( a v c ) ) = ( ( b ^ a ) v ( b ^ c ) ) $=
      ( wa wo ledi wn wf oran df-a con2 ran ax-r2 lan an4 com3ii anass ax-r1
      ax-r4 comcom comcom2 ancom ax-a1 ax-r5 comcom3 an12 dff 3tr1 an0 oml3 ) B
      AFZBCFZGZBACGZFZUOUQBACHUQUOIZFZAIZCBUNIZFZFZFZJUSUTCFZVBFZVDUSUTUPFZVBFZ
      VFUSUTBFZUPVAFZFZVHUSUQBIUTGZVAFZFZVKURVMUQUOVMUOUMIZVAFZIVMIUMUNKVPVMVOV
      LVAUMVLBALMNUAOMPVNBVLFZVJFVKBUPVLVAQVQVIVJVQBUTFVIBUTBAABDUBUCRBUTUDONOO
      UTBUPVAQOVGVEVBVGUTUTIZCGZFVEUPVSUTAVRCAUEUFPUTCACEUGRONOUTCVBSOVDUTJFJVC
      JUTBCVAFFZUNVAFZVCJWAVTBCVASTCBVAUHUNUIUJPUTUKOOULT $.

    $( Foulis-Holland Theorem.  (Contributed by NM, 29-Aug-1997.) $)
    fh3 $p |- ( a v ( b ^ c ) ) = ( ( a v b ) ^ ( a v c ) ) $=
      ( wa wo comcom4 fh1 anor2 df-a ax-r1 lor ax-r4 ax-r2 oran 2an 3tr2 con1
      wn ) ABCFZGZABGZACGZFZATZBTZCTZGZFZUFUGFZUFUHFZGZUBTZUETZUFUGUHABDHACEHIU
      JAUITZGZTUNAUIJUQUBUPUAAUAUPBCKLMNOUMUKTZULTZFZTUOUKULPUTUEUEUTUCURUDUSAB
      PACPQLNORS $.

    $( Foulis-Holland Theorem.  (Contributed by NM, 29-Aug-1997.) $)
    fh4 $p |- ( b v ( a ^ c ) ) = ( ( b v a ) ^ ( b v c ) ) $=
      ( wa wo comcom4 fh2 anor2 df-a ax-r1 lor ax-r4 ax-r2 oran 2an 3tr2 con1
      wn ) BACFZGZBAGZBCGZFZBTZATZCTZGZFZUFUGFZUFUHFZGZUBTZUETZUGUFUHABDHACEHIU
      JBUITZGZTUNBUIJUQUBUPUABUAUPACKLMNOUMUKTZULTZFZTUOUKULPUTUEUEUTUCURUDUSBA
      PBCPQLNORS $.

    $( Foulis-Holland Theorem.  (Contributed by NM, 23-Nov-1997.) $)
    fh1r $p |- ( ( b v c ) ^ a ) = ( ( b ^ a ) v ( c ^ a ) ) $=
      ( wo wa fh1 ancom 2or 3tr1 ) ABCFZGABGZACGZFLAGBAGZCAGZFABCDEHLAIOMPNBAIC
      AIJK $.

    $( Foulis-Holland Theorem.  (Contributed by NM, 23-Nov-1997.) $)
    fh2r $p |- ( ( a v c ) ^ b ) = ( ( a ^ b ) v ( c ^ b ) ) $=
      ( wo wa fh2 ancom 2or 3tr1 ) BACFZGBAGZBCGZFLBGABGZCBGZFABCDEHLBIOMPNABIC
      BIJK $.

    $( Foulis-Holland Theorem.  (Contributed by NM, 23-Nov-1997.) $)
    fh3r $p |- ( ( b ^ c ) v a ) = ( ( b v a ) ^ ( c v a ) ) $=
      ( wa wo fh3 ax-a2 2an 3tr1 ) ABCFZGABGZACGZFLAGBAGZCAGZFABCDEHLAIOMPNBAIC
      AIJK $.

    $( Foulis-Holland Theorem.  (Contributed by NM, 23-Nov-1997.) $)
    fh4r $p |- ( ( a ^ c ) v b ) = ( ( a v b ) ^ ( c v b ) ) $=
      ( wa wo fh4 ax-a2 2an 3tr1 ) BACFZGBAGZBCGZFLBGABGZCBGZFABCDEHLBIOMPNABIC
      BIJK $.

    $( Foulis-Holland Theorem.  (Contributed by NM, 20-Sep-1998.) $)
    fh2c $p |- ( b ^ ( c v a ) ) = ( ( b ^ c ) v ( b ^ a ) ) $=
      ( wo wa fh2 ax-a2 lan 3tr1 ) BACFZGBAGZBCGZFBCAFZGNMFABCDEHOLBCAIJNMIK $.

    $( Foulis-Holland Theorem.  (Contributed by NM, 20-Sep-1998.) $)
    fh4c $p |- ( b v ( c ^ a ) ) = ( ( b v c ) ^ ( b v a ) ) $=
      ( wa wo fh4 ancom lor 3tr1 ) BACFZGBAGZBCGZFBCAFZGNMFABCDEHOLBCAIJNMIK $.

    $( Foulis-Holland Theorem.  (Contributed by NM, 10-Mar-2002.) $)
    fh1rc $p |- ( ( c v b ) ^ a ) = ( ( c ^ a ) v ( b ^ a ) ) $=
      ( wo wa fh1r ax-a2 ran 3tr1 ) BCFZAGBAGZCAGZFCBFZAGNMFABCDEHOLACBIJNMIK
      $.

    $( Foulis-Holland Theorem.  (Contributed by NM, 20-Sep-1998.) $)
    fh2rc $p |- ( ( c v a ) ^ b ) = ( ( c ^ b ) v ( a ^ b ) ) $=
      ( wo wa fh2r ax-a2 ran 3tr1 ) ACFZBGABGZCBGZFCAFZBGNMFABCDEHOLBCAIJNMIK
      $.

    $( Foulis-Holland Theorem.  (Contributed by NM, 6-Aug-2001.) $)
    fh3rc $p |- ( ( c ^ b ) v a ) = ( ( c v a ) ^ ( b v a ) ) $=
      ( wa wo fh3r ancom ax-r5 3tr1 ) BCFZAGBAGZCAGZFCBFZAGNMFABCDEHOLACBIJNMIK
      $.

    $( Foulis-Holland Theorem.  (Contributed by NM, 20-Sep-1998.) $)
    fh4rc $p |- ( ( c ^ a ) v b ) = ( ( c v b ) ^ ( a v b ) ) $=
      ( wa wo fh4r ancom ax-r5 3tr1 ) ACFZBGABGZCBGZFCAFZBGNMFABCDEHOLBCAIJNMIK
      $.

    $( Thm. 4.2 Beran p. 49.  (Contributed by NM, 7-Nov-1997.) $)
    com2or $p |- a C ( b v c ) $=
      ( wo wa wn comcom df-c2 ancom 2or ax-r2 or4 fh1 comcom3 ax-r1 df-c1 ) BCF
      ZASASABGZACGZFZAHZBGZUCCGZFZFZSAGZSUCGZFZSTUDFZUAUEFZFUGBUKCULBBAGZBUCGZF
      UKBAABDIJUMTUNUDBAKBUCKLMCCAGZCUCGZFULCAACEIJUOUAUPUECAKCUCKLMLTUDUAUENMU
      JUGUHUBUIUFUHASGUBSAKABCDEOMUIUCSGUFSUCKUCBCABDPACEPOMLQMRI $.

    $( Thm. 4.2 Beran p. 49.  (Contributed by NM, 7-Nov-1997.) $)
    com2an $p |- a C ( b ^ c ) $=
      ( wa wn wo comcom4 com2or df-a con2 ax-r1 cbtr comcom5 ) ABCFZAGZBGZCGZHZ
      PGZQRSABDIACEIJUATPTBCKLMNO $.
  $}

  $( Commutation theorem for Sasaki implication.  (Contributed by NM,
     25-Oct-1998.) $)
  combi $p |- a C ( a == b ) $=
    ( wa wn wo tb comanr1 comcom6 com2or dfb ax-r1 cbtr ) AABCZADZBDZCZEZABFZAM
    PABGAPNOGHIRQABJKL $.

  $( Negated biconditional (distributive form) (Contributed by NM,
     30-Aug-1997.) $)
  nbdi $p |- ( a == b ) ' =
             ( ( ( a v b ) ^ a ' ) v ( ( a v b ) ^ b ' ) ) $=
    ( tb wn wo wa dfnb comorr comcom comcom2 ax-a2 cbtr fh1 ax-r2 ) ABCDABEZADZ
    BDZEFOPFOQFEABGOPQOAAOABHIJOBBOBBAEOBAHBAKLIJMN $.

  $( Orthomodular law.  (Contributed by NM, 25-Oct-1997.) $)
  oml4 $p |- ( ( a == b ) ^ a ) =< b $=
    ( tb wa ancom wn wo dfb lan coman1 comcom comcom2 comcom5 fh1 or0 ran anass
    wf ax-r2 3tr2 anidm ax-r1 an0 dff 2or lea bltr ) ABCZADZBADZBUIAUHDZUJUHAEU
    KAABDZAFZBFZDZGZDZUJUHUPAABHIUQAULDZAUODZGZUJAULUOULAABJKAUOUMUOUOUMUMUNJKL
    MNULRGULUTUJULOULURRUSULAADZBDZURVBULVAABAUAPUBAABQSRAUMDZUNDZUSUNRDRUNDRVD
    UNREUNUCRVCUNAUDPTAUMUNQSUEABETSSSBAUFUG $.

  $( Orthomodular law.  (Contributed by NM, 3-Jan-1999.) $)
  oml6 $p |- ( a v ( b ^ ( a ' v b ' ) ) ) = ( a v b ) $=
    ( wn wo wa comor1 comcom7 comor2 fh4c df-t ax-r5 ax-a2 or1 ax-r2 ax-a3 3tr2
    wt ax-r1 lan an1 3tr ) ABACZBCZDZEDABDZAUDDZEUEQEUEUDABUDAUBUCFGUDBUBUCHGIU
    FQUEQUFQUCDZAUBDZUCDQUFQUHUCAJKUGUCQDQQUCLUCMNAUBUCOPRSUETUA $.

  ${
    gsth.1 $e |- a C b $.
    gsth.2 $e |- b C c $.
    gsth.3 $e |- a C ( b ^ c ) $.
    $( Gudder-Schelp's Theorem.  Beran, p. 262, Thm. 4.1.  (Contributed by NM,
       20-Sep-1998.) $)
    gsth $p |- ( a ^ b ) C c $=
      ( wa wo wn comcom fh4rc comcom2 lan fh1r ran lea ancom wf ax-r1 3tr lecom
      2an an4 an32 comd leo letr coman2 com2or df2le2 fh1 anass dff an0 lor or0
      cbtr ax-r2 2or ax-a2 lelan bltr df-le2 3tr2 df2c1 ) ABGZCVFCHZVFCIZHZGZVF
      VJACHZBCHZGZAVHHZBVHHZGZGVKVNGZVLVOGZGZVFVGVMVIVPBCAEABDJZKBVHABCELVTKUBV
      KVLVNVOUCVQBGVKBGZVNGZVSVFVKVNBUDBVRVQBCEUEMWBVFCBGZHZVNGVFVNGZWCVNGZHZVF
      WAWDVNBACVTENOVNVFWCVFVNVFVNVFAVNABPAVHUFUGZUAJVNBCGZWCWIVNWIAVHAWIFJZWIC
      BCUHLZUIJBCQUQNWGVFWIAGZHWLVFHVFWEVFWFWLVFVNWHUJWFWIVNGWLWIVHGZHZWLWCWIVN
      CBQOWIAVHWJWKUKWNWLRHWLWMRWLWMBCVHGZGBRGRBCVHULWORBRWOCUMSMBUNTUOWLUPURTU
      SVFWLUTWLVFWLAWIGVFWIAQWIBABCPVAVBVCTTVDTSVE $.
  $}

  ${
    gsth2.1 $e |- b C c $.
    gsth2.2 $e |- a C ( b ^ c ) $.
    $( Stronger version of Gudder-Schelp's Theorem.  Beran, p. 263, Thm. 4.2.
       (Contributed by NM, 20-Sep-1998.) $)
    gsth2 $p |- ( a ^ b ) C c $=
      ( wa wn comcom ancom ax-a2 ran ax-r2 comor2 comcom7 comcom2 coman1 com2or
      wo df-a cbtr gsth bctr lor ax-r4 ax-r1 com2an omla ) CABFZCBBGZBAFZRZFZUH
      CBUKBCDHCUKCBUIAGZRZFZUKGZUOCUOUMUIRZBFZCUOUNBFURBUNIUNUQBUIUMJKLUQBCUQBU
      MUIMNDBCFZUQUSUMUIUSAAUSEHOUSBBCPOQHUAUBHUOUIUNGZRZGZUPBUNSUPVBUKVAUJUTUI
      BASUCUDUELTNUFULUJUHBAUGBAILTH $.
  $}

  ${
    gstho.1 $e |- b C c $.
    gstho.2 $e |- a C ( b v c ) $.
    $( "OR" version of Gudder-Schelp's Theorem.  (Contributed by NM,
       19-Oct-1998.) $)
    gstho $p |- ( a v b ) C c $=
      ( wo wn wa anor3 ax-r1 comcom4 cbtr gsth2 bctr comcom5 ) ABFZCPGZAGZBGZHZ
      CGZTQABIJRSUABCDKRBCFZGZSUAHZAUBEKUDUCBCIJLMNO $.
  $}

  ${
    gt1.1 $e |- a = ( b v c ) $.
    gt1.2 $e |- b =< d $.
    gt1.3 $e |- c =< d ' $.
    $( Part of Lemma 1 from Gaisi Takeuti, "Quantum Set Theory".  (Contributed
       by NM, 2-Dec-1998.) $)
    gt1 $p |- a C d $=
      ( wo lecom comcom wn comcom7 com2or bctr ) ABCHZDEDODBCBDBDFIJCDCDCDKGILJ
      MJN $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Commutator (orthomodular lattice theorems)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    cmtr1com.1 $e |- C ( a , b ) = 1 $.
    $( Commutator equal to 1 commutes.  Theorem 2.11 of Beran, p. 86.
       (Contributed by NM, 24-Jan-1999.) $)
    cmtr1com $p |- a C b $=
      ( wa wn wo lea lel2or df-le2 le1 wcmtr df-cmtr ax-a2 3tr2 leror bltr lebi
      wt lem3.1 ax-r1 df-c1 ) ABABDZABEZDZFZAUEAUEAUBAUDABGAUCGHIAEZUEFZRUGJRUF
      BDZUFUCDZFZUEFZUGABKUEUJFRUKABLCUEUJMNUJUFUEUHUFUIUFBGUFUCGHOPQSTUA $.
  $}

  ${
    comcmtr1.1 $e |- a C b $.
    $( Commutation implies commutator equal to 1.  Theorem 2.11 of Beran,
       p. 86.  (Contributed by NM, 24-Jan-1999.) $)
    comcmtr1 $p |- C ( a , b ) = 1 $=
      ( wa wn wo wcmtr wt df-c2 comcom3 2or ax-r1 df-cmtr df-t 3tr1 ) ABDABEZDF
      ZAEZBDRPDFZFZARFZABGHUATAQRSABCIRBABCJIKLABMANO $.
  $}

  ${
    i0cmtrcom.1 $e |- ( a ->0 C ( a , b ) ) = 1 $.
    $( Commutator element ` ->0 ` commutator implies commutation.  (Contributed
       by NM, 24-Jan-1999.) $)
    i0cmtrcom $p |- a C b $=
      ( wa wn wo lea lel2or df-le2 wcmtr wi0 df-cmtr lor ax-r1 ax-a2 ax-r2 or12
      wt 3tr df-i0 3tr1 lem3.1 df-c1 ) ABABDZABEZDZFZAUGAUGAUDAUFABGAUEGHIAEZUG
      FZAABJZKZRUHUGUHBDZUHUEDZFZFZFZUHUJFZUIUKUQUPUJUOUHABLMNUIUGUHFZUGUHUNFZF
      ZUPUHUGOUTURUSUHUGUSUNUHFUHUHUNOUNUHULUHUMUHBGUHUEGHIPMNUGUHUNQSAUJTUACPU
      BNUC $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Kalmbach conditional
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Kalmbach implication and biconditional.  (Contributed by NM,
     5-Nov-1997.) $)
  i3bi $p |- ( ( a ->3 b ) ^ ( b ->3 a ) ) = ( a == b ) $=
    ( wn wa wo lea leo ax-a2 letr ancom lecom comcom2 comcom bctr wf ax-r2 bltr
    ax-r1 lan 2or wi3 tb anor2 lbtr le3tr1 le2or oridm fh2 cbtr fh1 ran an4 dff
    anor1 2an anidm an12 con2 an0 anandi coman1 an32 or0 lor oran con3 fh3 3tr2
    anass df-i3 or32 dfb 3tr1 ) ACZBCZDZVNBDZAVNBEZDZEZEZVPVOADZBVOAEZDZEZEZDZA
    BDZVPEZABUAZBAUAZDABUBVPVTWEDZEVPWHEWGWIWLWHVPWLVTWBDZVTWDDZEZWHWBVTWDWBBVN
    EZCZVTBAUCZVTWQVTWPVTWPVTWPWPEWPVQWPVSWPVQVNWPVNBFVNVRWPVNBGVNBHUDIVRADZVRV
    SWPVRAFZAVRJZBVNHZUEUFWPUGUDKLMNWBWQWDWRWDWQWDWPWDWPWDBWPBWCFZBVNGIKLMNUHWO
    OWHEZWHWMOWNWHWMWBVTDZOVTWBJXEWBVQDZWBVSDZEZOWBVQVSWBWCCZVQWBWCWBWCWBVOWCVO
    AFVOAGIKLVQXIVQBVNDZXIVNBJZBAUNPZRZUIWBVRCZVSWBAVODZXNVOAJZABUNPVSXNVSVRVSV
    RVSWSVRXAWTQKLMNUJXHOOEOXFOXGOXFXOVQDZOWBXOVQXPUKXQAVNDZVOBDZDZOAVOVNBULXTO
    ODZOYAXTOXROXSAUMZOBVODZXSBUMZBVOJPUOROUPPPPXGAWBVRDZDZOWBAVRUQYFAODZOYGYFO
    YEAOWBWBCZDYEWBUMYHVRWBYHWPVRWBWPWRURXBPSPSRAUSZPPTOUGPPPWNWDVTDZWHVTWDJYJW
    DVQDZWDVSDZEZWHVQWDVSVQXIWDXLWDXIWDWCWDWCWDWCBDWCBWCJWCBFQKLMNVQAVOEZCZVSAB
    UCVSYOVSYNVSYNVSAYNAVRFZAVOGIKLMNUHYMYLYKEZWHYKYLHYQWHOEZWHYLWHYKOYLBADZWCV
    RDDZWHBWCAVRULYTYSWCDZYSVRDZDZWHYSWCVRUTUUCYSYSDZWHUUAYSUUBYSUUAYSVODZYSADZ
    EZYSYSVOAYSBBAVAZLYSWHABAJZABVANZUJUUGYSOEZYSUUGOYSEZUUKUUEOUUFYSUUEYCADZOB
    AVOVBUUMAYCDZOYCAJUUNYGOYGUUNOYCAYDSRYIPPPUUFBAADZDYSBAAVIUUOABAUPSPTOYSHZP
    YSVCZPPUUBYSVNDZYSBDZEZYSYSVNBYSAUUJLUUHUJUUTUUKYSUUTUULUUKUUROUUSYSUURBXRD
    ZOBAVNVIUVABODZOUVBUVAOXRBYBSRBUSZPPUUSBBDZADYSBABVBUVDBABUPUKPTUUPPUUQPPUO
    UUDYSWHYSUPUUIPPPPYKUVBOYKBWCVQDZDZUVBBWCVQVIUVBUVFOUVEBOWCXIDUVEWCUMXIVQWC
    XMSPSRPUVCPTWHVCZPPPPTXDYRWHOWHHUVGPPPVDVPVTWEVPBAEZCZVTVPVOVNDZUVIVNVOJUVJ
    UVHUVHUVJCBAVERVFPVTUVIVTUVHVTUVHVQBVSAVQXJBXKBVNFQYPUFKLMNVPABEZCZWEVPUVKU
    VKVPCABVERVFWEUVLWEUVKWEUVKWBAWDBWBXOAXPAVOFQXCUFKLMNVGVPWHHVHWJWAWKWFWJVQV
    PEVSEZWAABVJUVMVTVPEWAVQVPVSVKVTVPHPPWKWBUVJEWDEZWFBAVJUVNWEUVJEZWFWBUVJWDV
    KUVOWEVPEWFUVJVPWEVOVNJVDWEVPHPPPUOABVLVM $.

  $( Kalmbach implication OR builder.  (Contributed by NM, 26-Dec-1997.) $)
  i3or $p |- ( ( a == b ) ' v ( ( a v c ) ->3 ( b v c ) ) ) = 1 $=
    ( tb wn wo wi3 wt le1 ka4ot ax-r1 wa i3bi lea bltr lelor lebi ) ABDEZACFZBC
    FZGZFZHUBIHRSTDZFZUBUDHABCJKUCUARUCUATSGZLZUAUFUCSTMKUAUENOPOQ $.

  $( Alternate definition for Kalmbach implication.  (Contributed by NM,
     7-Nov-1997.) $)
  df2i3 $p |- ( a ->3 b ) = ( ( a ' ^ b ' ) v ( ( a ' v b ) ^
                ( a v ( a ' ^ b ) ) ) ) $=
    ( wi3 wn wa wo df-i3 ax-a3 coman1 comcom comcom2 comcom5 comorr fh4 lea leo
    or12 letr lan ax-r2 df-le2 ancom ax-a2 lor ) ABCADZBEZUEBDEZFAUEBFZEZFZUGUH
    AUFFZEZFZABGUJUFUGUIFFZUMUFUGUIHUNUGUFUIFZFUMUFUGUIQUOULUGUOUFAFZUFUHFZEZUL
    AUFUHAUFUEUFUFUEUEBIJKLAUHUEUHUEBMKLNURUPUHEZULUQUHUPUFUHUFUEUHUEBOUEBPRUAS
    USUHUPEULUPUHUBUPUKUHUFAUCSTTTUDTTT $.

  $( Alternate Kalmbach conditional.  (Contributed by NM, 6-Aug-2001.) $)
  dfi3b $p |- ( a ->3 b ) =
            ( ( a ' v b ) ^ ( ( a v ( a ' ^ b ' ) ) v ( a ' ^ b ) ) ) $=
    ( wn wa wo wi3 ax-a2 ax-a3 oridm ax-r1 anidm ran anass ax-r2 lan 2or com2an
    ancom fh1 3tr1 an12 lea leo letr df2le2 comor1 comcom7 comor2 coman1 coman2
    comcom2 fh1r df-i3 com2or ) ACZBDZUOBCZDZEAUOBEZDZEZUSAUREZDZUSUPDZEZABFUSV
    BUPEDUOUPDZBUPDZEZUSADZUSURDZEZEZVKVHEVAVEVHVKGVAUPURUTEZEVLUPURUTHUPVHVMVK
    UPUPUPEZVHVNUPUPIJUPVFUPVGUPUOUODZBDVFUOVOBVOUOUOKJLUOUOBMNUPUOBBDZDVGBVPUO
    VPBBKJOUOBBUANPNVMVJVIEVKURVJUTVIURURUSDZVJVQURURUSURUOUSUOUQUBUOBUCUDUEJUR
    USRNAUSRPVJVIGNPNVCVKVDVHUSAURUSAUOBUFZUGZUSUOUQVRUSBUOBUHZUKQZSUPUOBUOBUIU
    OBUJULPTABUMUSVBUPUSAURVSWAUNUSUOBVRVTQST $.

  $( Alternate non-tollens conditional.  (Contributed by NM, 6-Aug-2001.) $)
  dfi4b $p |- ( a ->4 b ) =
            ( ( a ' v b ) ^ ( ( b ' v ( b ^ a ' ) ) v ( b ^ a ) ) ) $=
    ( wi4 wn wi3 wo wa i4i3 dfi3b ax-a2 ax-a1 ax-r5 ax-r2 ran lor 2an 2or ax-r1
    or32 ) ABCBDZADZEZUABFZTBUAGZFZBAGZFZGZABHUBTDZUAFZTUIUADZGZFUIUAGZFZGZUHTU
    AIUHUOUCUJUGUNUCBUAFUJUABJBUIUABKZLMUGTUMFZULFUNUEUQUFULUDUMTBUIUAUPNOBUIAU
    KUPAKPQTUMULSMPRMM $.

  $( Equivalence for Kalmbach implication.  (Contributed by NM, 9-Nov-1997.) $)
  i3n2 $p |- ( a ' ->3 b ' ) = ( ( a ^ b ) v ( ( a v b ' ) ^
                ( a ' v ( a ^ b ' ) ) ) ) $=
    ( wn wi3 wa wo df2i3 ax-a1 2an ax-r5 ran lor 2or ax-r1 ax-r2 ) ACZBCZDPCZQC
    ZEZRQFZPRQEZFZEZFZABEZAQFZPAQEZFZEZFZPQGUKUEUFTUJUDARBSAHZBHIUGUAUIUCARQULJ
    UHUBPARQULKLIMNO $.

  $( Equivalence for Kalmbach implication.  (Contributed by NM, 9-Nov-1997.) $)
  ni32 $p |- ( a ->3 b ) ' = ( ( a v b ) ^ ( ( a ^ b ' ) v
                ( a ' ^ ( a v b ' ) ) ) ) $=
    ( wi3 wo wn wa df2i3 oran anor1 con2 ax-r1 anor2 lan ax-r4 ax-r2 2an ) ABCZ
    ABDZABEZFZAEZASDZFZDZFZQUASFZUABDZAUABFZDZFZDZUEEZABGUKUFEZUJEZFZEULUFUJHUO
    UEUEUORUMUDUNABHUDTEZUCEZFZEUNTUCHURUJUJURUGUPUIUQUPUGTUGABIJKUIUAUHEZFZEUQ
    AUHHUTUCUSUBUAUHUBABLJMNOPKNOPKNOOJ $.

  $( Theorem for Kalmbach implication.  (Contributed by NM, 9-Nov-1997.) $)
  oi3ai3 $p |- ( ( a ^ b ) v ( a ->3 b ) ' ) =
                 ( ( a v b ) ^ ( a ' ->3 b ' ) ) $=
    ( wa wo wn wi3 lea leo letr lecom coman1 ancom comcom2 com2an com2or df-le2
    bctr fh3 ax-a3 ax-r2 ax-r1 ax-a2 ax-r5 2an ni32 lor i3n1 lan 3tr1 ) ABCZABD
    ZABEZCZAEZAULDZCZDZCZDZUKUMUJDZUPDZCZUJABFEZDUKUNULFZCUSUJUKDZUJUQDZCVBUJUK
    UQUJUKUJAUKABGABHIZJUJUMUPUJAULABKZUJBUJBACBABLBAKQMZNUJUNUOUJAVHMUJAULVHVI
    ONORVEUKVFVAUJUKVGPVFUJUMDZUPDZVAVKVFUJUMUPSUAVJUTUPUJUMUBUCTUDTVCURUJABUEU
    FVDVAUKABUGUHUI $.

  ${
    i3lem.1 $e |- ( a ->3 b ) = 1 $.
    $( Lemma for Kalmbach implication.  (Contributed by NM, 7-Nov-1997.) $)
    i3lem1 $p |- ( ( a ' ^ b ) v ( a ' ^ b ' ) ) = a ' $=
      ( wn wa wo wt coman1 comcom comorr comcom3 com2an anass ax-r1 anidm ax-r2
      fh1 ran anabs omlan 2or ax-a2 wi3 df2i3 lan an1 ) ADZBEZUGBDZEZFZUGGEZUGU
      KUGUJUGBFZAUHFZEZFZEZULUQUKUQUGUJEZUGUOEZFZUKUGUJUOUJUGUGUIHIUGUMUNUGBJAU
      NAUHJKLQUTUJUHFUKURUJUSUHURUGUGEZUIEZUJVBURUGUGUIMNVAUGUIUGORPUSUGUMEZUNE
      ZUHVDUSUGUMUNMNVDUGUNEUHVCUGUNUGBSRABTPPUAUJUHUBPPNUPGUGUPABUCZGVEUPABUDN
      CPUEPUGUFP $.

    $( Lemma for Kalmbach implication.  (Contributed by NM, 7-Nov-1997.) $)
    i3lem2 $p |- a C b $=
      ( wn wa wo i3lem1 ax-r1 df-c1 comcom2 comcom5 ) ABADZBLBLBELBDEFLABCGHIJK
      $.

    $( Lemma for Kalmbach implication.  (Contributed by NM, 7-Nov-1997.) $)
    i3lem3 $p |- ( ( a ' v b ) ^ b ' ) = ( a ' ^ b ' ) $=
      ( wn wa omlan ancom ax-a2 ax-a3 ax-r1 i3lem1 lor orabs ax-r2 2or 3tr2 lan
      wo 3tr1 ) BDZBTADZEZRZEZUBUABRZTEZUATEZBUAFUFTUEEUDUETGUEUCTUEBUARZUCUABH
      BUABEZUGRZRZBUIRZUGRZUHUCUMUKBUIUGIJUJUABABCKLULBUGUBULBBUAEZRBUIUNBUABGL
      BUAMNUATGZOPNQNUOS $.

    $( Lemma for Kalmbach implication.  (Contributed by NM, 7-Nov-1997.) $)
    i3lem4 $p |- ( a ' v b ) = 1 $=
      ( wn wo wa wt i3lem1 ax-r5 ax-r1 omln wi3 df-i3 ax-r2 3tr2 ) ADZAPBEZFZEZ
      PBFPBDFEZREZQGUASTPRABCHIJABKUAABLZGUBUAABMJCNO $.
  $}

  $( Commutation theorem.  (Contributed by NM, 9-Nov-1997.) $)
  comi31 $p |- a C ( a ->3 b ) $=
    ( wn wa wo wi3 coman1 comcom comcom2 comcom5 com2or df-i3 ax-r1 cbtr ) AACZ
    BDZOBCZDZEZAOBEZDZEZABFZASUAAPRAPOPPOOBGHIJARORROOQGHIJKUAAATGHKUCUBABLMN
    $.

  ${
    com2i3.1 $e |- a C b $.
    com2i3.2 $e |- a C c $.
    $( Commutation theorem.  (Contributed by NM, 9-Nov-1997.) $)
    com2i3 $p |- a C ( b ->3 c ) $=
      ( wn wa wo wi3 comcom2 com2an com2or df-i3 ax-r1 cbtr ) ABFZCGZPCFZGZHZBP
      CHZGZHZBCIZATUBAQSAPCABDJZEKAPRUEACEJKLABUADAPCUEELKLUDUCBCMNO $.
  $}

  ${
    comi32.1 $e |- a C b $.
    $( Commutation theorem.  (Contributed by NM, 9-Nov-1997.) $)
    comi32 $p |- a C ( b ->3 a ) $=
      ( comid com2i3 ) ABACADE $.
  $}

  $( Lemma 4 of Kalmbach p. 240.  (Contributed by NM, 5-Nov-1997.) $)
  lem4 $p |- ( a ->3 ( a ->3 b ) ) = ( a ' v b ) $=
    ( wi3 wn wa wo df-i3 lan oridm lecom comcom wf ancom ax-r2 ax-r1 3tr2 orabs
    lea lor 2or le2or lbtr comcom3 fh1 anass dff df2le2 orordi or32 ax-r5 ax-r4
    an0 or0 oran con2 oml2 ax-a3 omln ) AABCZCADZUSEZUTUSDEZFZAUTUSFZEZFZUTBFZA
    USGVFUTAVGEZFZVGVCUTVEVHVCUTBEZUTBDZEZFZVMDZUTEZFUTVAVMVBVOVAUTVMVHFZEZVMUS
    VPUTABGZHVQUTVMEZUTVHEZFZVMUTVMVHVMUTVMUTVMUTUTFZUTVJUTVLUTUTBRUTVKRUAUTIZU
    BZJKAVHVHAVHAAVGRJKUCUDWAVSLFZVMVTLVSUTAEZVGEVGWFEZVTLWFVGMUTAVGUEWGVGLEZLW
    HWGLWFVGLAUTEWFAUFAUTMNHOVGULNPSWEVSVMVSUMVSVMUTEVMUTVMMVMUTWDUGNNNNNAUSFZD
    AVMFZDZVBVOWIWJWIAVPFZWJUSVPAVRSWLWJAVHFZFZWJAVMVHUHWNWJAFZWJWMAWJAVGQSWOAA
    FZVMFWJAVMAUIWPAVMAIUJNNNNUKWIVBAUSUNUOWKUTVNEZVOWJWQAVMUNUOUTVNMNPTVMUTWDU
    PNVDVGAVDVIVGVDUTVPFZVIUSVPUTVRSWRUTVMFZVHFZVIWTWRUTVMVHUQOWSUTVHWSUTVJFZUT
    VLFZFZUTUTVJVLUHXCWBUTXAUTXBUTUTBQUTVKQTWCNNUJNNABURZNHTXDNN $.

  ${
    i0i3.1 $e |- ( a ' v b ) = 1 $.
    $( Translation to Kalmbach implication.  (Contributed by NM,
       9-Nov-1997.) $)
    i0i3 $p |- ( a ->3 ( a ->3 b ) ) = 1 $=
      ( wi3 wn wo wt lem4 ax-r2 ) AABDDAEBFGABHCI $.
  $}

  ${
    i3i0.1 $e |- ( a ->3 ( a ->3 b ) ) = 1 $.
    $( Translation from Kalmbach implication.  (Contributed by NM,
       9-Nov-1997.) $)
    i3i0 $p |- ( a ' v b ) = 1 $=
      ( wn wo wi3 wt lem4 ax-r1 ax-r2 ) ADBEZAABFFZGLKABHICJ $.
  $}

  $( Soundness proof for KA14.  (Contributed by NM, 3-Nov-1997.) $)
  ska14 $p |- ( ( a ' v b ) ->3 ( a ->3 ( a ->3 b ) ) ) = 1 $=
    ( wn wo wi3 wt lem4 ax-r1 ri3 i3id ax-r2 ) ACBDZAABEEZEMMEFLMMMLABGHIMJK $.

  ${
    i3le.1 $e |- ( a ->3 b ) = 1 $.
    $( L.e. to Kalmbach implication.  (Contributed by NM, 7-Nov-1997.) $)
    i3le $p |- a =< b $=
      ( wn wt wa ancom wo i3lem3 i3lem4 ran 3tr2 an1 df2le1 lecon1 ) BABDZADZEP
      FZPEFPQFZPEPGQBHZPFQPFRSABCITEPABCJKQPGLPMLNO $.
  $}

  $( Biconditional implies Kalmbach implication.  (Contributed by NM,
     9-Nov-1997.) $)
  bii3 $p |- ( ( a == b ) ->3 ( a ->3 b ) ) = 1 $=
    ( tb wi3 wa i3bi ax-r1 lea bltr lei3 ) ABCZABDZKLBADZEZLNKABFGLMHIJ $.

  ${
    binr1.1 $e |- ( a ->3 b ) = 1 $.
    $( Pavicic binary logic ~ ax-r1 analog.  (Contributed by NM,
       7-Nov-1997.) $)
    binr1 $p |- ( b ' ->3 a ' ) = 1 $=
      ( wn i3le lecon lei3 ) BDADABABCEFG $.
  $}

  ${
    binr2.1 $e |- ( a ->3 b ) = 1 $.
    binr2.2 $e |- ( b ->3 c ) = 1 $.
    $( Pavicic binary logic ~ ax-r2 analog.  (Contributed by NM,
       7-Nov-1997.) $)
    binr2 $p |- ( a ->3 c ) = 1 $=
      ( i3le letr lei3 ) ACABCABDFBCEFGH $.
  $}

  ${
    binr3.1 $e |- ( a ->3 c ) = 1 $.
    binr3.2 $e |- ( b ->3 c ) = 1 $.
    $( Pavicic binary logic ~ ax-r3 analog.  (Contributed by NM,
       7-Nov-1997.) $)
    binr3 $p |- ( ( a v b ) ->3 c ) = 1 $=
      ( wo i3le le2or oridm lbtr lei3 ) ABFZCLCCFCACBCACDGBCEGHCIJK $.
  $}

  $( Theorem for Kalmbach implication.  (Contributed by NM, 7-Nov-1997.) $)
  i31 $p |- ( a ->3 1 ) = 1 $=
    ( wt wi3 wn wo df-t li3 bina3 ax-r2 ) ABCAAADZEZCBBKAAFGAJHI $.

  ${
    i3aa.1 $e |- a = 1 $.
    $( Add antecedent.  (Contributed by NM, 7-Nov-1997.) $)
    i3aa $p |- ( b ->3 a ) = 1 $=
      ( wi3 wt i31 li3 bi1 wwbmpr ) BADZBEDZBFJKAEBCGHI $.
  $}

  $( Antecedent absorption.  (Contributed by NM, 16-Nov-1997.) $)
  i3abs1 $p |- ( a ->3 ( a ->3 ( a ->3 b ) ) ) = ( a ->3 ( a ->3 b ) ) $=
    ( wn wa wo wi3 orordi orabs 2or oridm ax-r2 ax-r5 ax-a3 omln 3tr2 df-i3 lor
    lem4 3tr1 ) ACZTBDZTBCZDZEZATBEZDZEZEZUEAAABFZFZFZUJTUDEZUFETUFEUHUEULTUFUL
    TUAEZTUCEZEZTTUAUCGUOTTETUMTUNTTBHTUBHITJKKLTUDUFMABNOUKTUIEUHAUIRUIUGTABPQ
    KABRS $.

  ${
    i3abs2.1 $e |- ( a ->3 ( a ->3 ( a ->3 b ) ) ) = 1 $.
    $( Antecedent absorption.  (Contributed by NM, 9-Nov-1997.) $)
    i3abs2 $p |- ( a ->3 ( a ->3 b ) ) = 1 $=
      ( wi3 i3abs1 bi1 wwbmp ) AAABDDZDZHCIHABEFG $.
  $}

  $( Antecedent absorption.  (Contributed by NM, 19-Nov-1997.) $)
  i3abs3 $p |- ( ( a ->3 b ) ->3 ( ( a ->3 b ) ->3 a ) ) =
              ( ( a ->3 b ) ->3 a ) $=
    ( wi3 wn wo wa wt df-t lan an1 comi31 comcom comcom3 comcom4 fh1 3tr2 ax-r1
    wf ax-a2 ax-r2 comid comcom2 dff ax-r5 or0 2or fh4 ancom lem4 df-i3 3tr1
    ran ) ABCZDZAEZUNAFUNADZFEZUMUOFZEZUMUMACZCUTUSUOUSUNUMAFZEZUOUQUNURVAUNUQU
    NGFUNAUPEZFUNUQGVCUNAHIUNJUNAUPUMAAUMABKLZMUMAVDNOPQURUMUNFZVAEZVAUMUNAUMUM
    UMUAUBZVDORVAEVAREVFVARVASRVEVAUMUCUDVAUEPTUFVBUNUMEZUOFZUOUMUNAVGVDUGVIUOG
    FZUOVIGUOFVJVHGUOVHUMUNEZGUNUMSGVKUMHQTULGUOUHTUOJTTTQUMAUIUMAUJUK $.

  $( Commutative law for conjunction with Kalmbach implication.  (Contributed
     by NM, 7-Nov-1997.) $)
  i3orcom $p |- ( ( a v b ) ->3 ( b v a ) ) = 1 $=
    ( wo wi3 i3id ax-a2 ri3 bi1 wwbmp ) BACZJDZABCZJDZJEKMJLJBAFGHI $.

  $( Commutative law for disjunction with Kalmbach implication.  (Contributed
     by NM, 7-Nov-1997.) $)
  i3ancom $p |- ( ( a ^ b ) ->3 ( b ^ a ) ) = 1 $=
    ( wa wi3 i3id ancom ri3 bi1 wwbmp ) BACZJDZABCZJDZJEKMJLJBAFGHI $.

  ${
    bi3tr.1 $e |- a = b $.
    bi3tr.2 $e |- ( b ->3 c ) = 1 $.
    $( Transitive inference.  (Contributed by NM, 7-Nov-1997.) $)
    bi3tr $p |- ( a ->3 c ) = 1 $=
      ( wi3 ri3 bi1 wwbmpr ) ACFZBCFZEJKABCDGHI $.
  $}

  ${
    i3btr.1 $e |- ( a ->3 b ) = 1 $.
    i3btr.2 $e |- b = c $.
    $( Transitive inference.  (Contributed by NM, 7-Nov-1997.) $)
    i3btr $p |- ( a ->3 c ) = 1 $=
      ( wi3 li3 bi1 wwbmp ) ABFZACFZDJKBCAEGHI $.
  $}

  ${
    i33tr1.1 $e |- ( a ->3 b ) = 1 $.
    i33tr1.2 $e |- c = a $.
    i33tr1.3 $e |- d = b $.
    $( Transitive inference useful for introducing definitions.  (Contributed
       by NM, 7-Nov-1997.) $)
    i33tr1 $p |- ( c ->3 d ) = 1 $=
      ( bi3tr ax-r1 i3btr ) CBDCABFEHDBGIJ $.
  $}

  ${
    i33tr2.1 $e |- ( a ->3 b ) = 1 $.
    i33tr2.2 $e |- a = c $.
    i33tr2.3 $e |- b = d $.
    $( Transitive inference useful for eliminating definitions.  (Contributed
       by NM, 7-Nov-1997.) $)
    i33tr2 $p |- ( c ->3 d ) = 1 $=
      ( ax-r1 i33tr1 ) ABCDEACFHBDGHI $.
  $}

  ${
    i3con1.1 $e |- ( a ' ->3 b ' ) = 1 $.
    $( Contrapositive.  (Contributed by NM, 7-Nov-1997.) $)
    i3con1 $p |- ( b ->3 a ) = 1 $=
      ( wn binr1 ax-a1 i33tr1 ) BDZDADZDBAIHCEBFAFG $.
  $}

  ${
    i3ror.1 $e |- ( a ->3 b ) = 1 $.
    $( WQL (Weak Quantum Logic) rule.  (Contributed by NM, 7-Nov-1997.) $)
    i3ror $p |- ( ( a v c ) ->3 ( b v c ) ) = 1 $=
      ( wo bina3 binr2 bina4 binr3 ) ACBCEZABJDBCFGBCHI $.
  $}

  ${
    i3lor.1 $e |- ( a ->3 b ) = 1 $.
    $( WQL (Weak Quantum Logic) rule.  (Contributed by NM, 7-Nov-1997.) $)
    i3lor $p |- ( ( c v a ) ->3 ( c v b ) ) = 1 $=
      ( wo i3orcom i3ror binr2 ) CAEACEZCBEZCAFIBCEJABCDGBCFHH $.
  $}

  ${
    i32or.1 $e |- ( a ->3 b ) = 1 $.
    i32or.2 $e |- ( c ->3 d ) = 1 $.
    $( WQL (Weak Quantum Logic) rule.  (Contributed by NM, 7-Nov-1997.) $)
    i32or $p |- ( ( a v c ) ->3 ( b v d ) ) = 1 $=
      ( wo i3ror i3lor binr2 ) ACGBCGBDGABCEHCDBFIJ $.
  $}

  ${
    i3ran.1 $e |- ( a ->3 b ) = 1 $.
    $( WQL (Weak Quantum Logic) rule.  (Contributed by NM, 7-Nov-1997.) $)
    i3ran $p |- ( ( a ^ c ) ->3 ( b ^ c ) ) = 1 $=
      ( wn wo wa binr1 i3ror df-a i33tr1 ) AEZCEZFZEBEZMFZEACGBCGPNOLMABDHIHACJ
      BCJK $.
  $}

  ${
    i3lan.1 $e |- ( a ->3 b ) = 1 $.
    $( WQL (Weak Quantum Logic) rule.  (Contributed by NM, 7-Nov-1997.) $)
    i3lan $p |- ( ( c ^ a ) ->3 ( c ^ b ) ) = 1 $=
      ( wa i3ran ancom i33tr1 ) ACEBCECAECBEABCDFCAGCBGH $.
  $}

  ${
    i32an.1 $e |- ( a ->3 b ) = 1 $.
    i32an.2 $e |- ( c ->3 d ) = 1 $.
    $( WQL (Weak Quantum Logic) rule.  (Contributed by NM, 7-Nov-1997.) $)
    i32an $p |- ( ( a ^ c ) ->3 ( b ^ d ) ) = 1 $=
      ( wa i3ran i3lan binr2 ) ACGBCGBDGABCEHCDBFIJ $.
  $}

  ${
    i3ri3.1 $e |- ( a ->3 b ) = 1 $.
    i3ri3.2 $e |- ( b ->3 a ) = 1 $.
    $( WQL (Weak Quantum Logic) rule.  (Contributed by NM, 7-Nov-1997.) $)
    i3ri3 $p |- ( ( a ->3 c ) ->3 ( b ->3 c ) ) = 1 $=
      ( wi3 i3le lebi ri3 bile lei3 ) ACFZBCFZLMABCABABDGBAEGHIJK $.
  $}

  ${
    i3li3.1 $e |- ( a ->3 b ) = 1 $.
    i3li3.2 $e |- ( b ->3 a ) = 1 $.
    $( WQL (Weak Quantum Logic) rule.  (Contributed by NM, 7-Nov-1997.) $)
    i3li3 $p |- ( ( c ->3 a ) ->3 ( c ->3 b ) ) = 1 $=
      ( wi3 i3le lebi li3 bile lei3 ) CAFZCBFZLMABCABABDGBAEGHIJK $.
  $}

  ${
    i32i3.1 $e |- ( a ->3 b ) = 1 $.
    i32i3.2 $e |- ( b ->3 a ) = 1 $.
    i32i3.3 $e |- ( c ->3 d ) = 1 $.
    i32i3.4 $e |- ( d ->3 c ) = 1 $.
    $( WQL (Weak Quantum Logic) rule.  (Contributed by NM, 7-Nov-1997.) $)
    i32i3 $p |- ( ( a ->3 c ) ->3 ( b ->3 d ) ) = 1 $=
      ( wi3 i3le lebi 2i3 bile lei3 ) ACIZBDIZOPABCDABABEJBAFJKCDCDGJDCHJKLMN
      $.
  $}

  ${
    i0i3tr.1 $e |- ( a ->3 ( a ->3 b ) ) = 1 $.
    i0i3tr.2 $e |- ( b ->3 c ) = 1 $.
    $( Transitive inference.  (Contributed by NM, 9-Nov-1997.) $)
    i0i3tr $p |- ( a ->3 ( a ->3 c ) ) = 1 $=
      ( wn wo i3i0 i3lor skmp3 i0i3 ) ACAFZBGLCGABDHBCLEIJK $.
  $}

  ${
    i3i0tr.1 $e |- ( a ->3 b ) = 1 $.
    i3i0tr.2 $e |- ( b ->3 ( b ->3 c ) ) = 1 $.
    $( Transitive inference.  (Contributed by NM, 9-Nov-1997.) $)
    i3i0tr $p |- ( a ->3 ( a ->3 c ) ) = 1 $=
      ( wn wo i3i0 binr1 i3ror skmp3 i0i3 ) ACBFZCGAFZCGBCEHMNCABDIJKL $.
  $}

  $( Theorem for Kalmbach implication.  (Contributed by NM, 16-Nov-1997.) $)
  i3th1 $p |- ( a ->3 ( a ->3 ( b ->3 a ) ) ) = 1 $=
    ( wn wi3 wo wa wt df2i3 lor ax-a3 anor1 ax-a2 anor2 ax-r1 ax-r2 ancom orabs
    lem4 ax-r5 3tr1 con2 2an oml5 3tr2 df-t ) ACZBADZEUFBCZUFFZUHAEZBUHAFZEZFZE
    ZEZAAUGDDGUGUNUFBAHIAUGRGUFUIEZUMEZUOUFBEZURCZEZUFUMEZGUQURAUHFZEUFBVBEZEZU
    TVAUFBVBJVBUSURABKIVDUFUFBFZEZUMEZVAVGVDVGUFVEUMEZEVDUFVEUMJVHVCUFVHVEVECZV
    CFZEVCUMVJVEUJVIULVCUJAUHEZVIUHALVIVKVEVKABMUANOUKVBBUHAPIUBIUFBVBUCOIONVFU
    FUMUFBQSOUDURUEUPUFUMUPUFUFUHFZEUFUIVLUFUHUFPIUFUHQOSTUFUIUMJOT $.

  $( Theorem for Kalmbach implication.  (Contributed by NM, 7-Nov-1997.) $)
  i3th2 $p |- ( a ->3 ( b ->3 ( b ->3 a ) ) ) = 1 $=
    ( wi3 wn wo wt lem4 li3 bina4 ax-r2 ) ABBACCZCABDZAEZCFKMABAGHLAIJ $.

  $( Theorem for Kalmbach implication.  (Contributed by NM, 7-Nov-1997.) $)
  i3th3 $p |- ( a ' ->3 ( a ->3 ( a ->3 b ) ) ) = 1 $=
    ( wn wi3 wo wt lem4 li3 bina3 ax-r2 ) ACZAABDDZDKKBEZDFLMKABGHKBIJ $.

  $( Theorem for Kalmbach implication.  (Contributed by NM, 7-Nov-1997.) $)
  i3th4 $p |- ( a ->3 ( b ->3 b ) ) = 1 $=
    ( wt wi3 i31 i3id ax-r1 li3 rbi wed ) ACDZCABBDZDZCAEKMCCLALCBFGHIJ $.

  $( Theorem for Kalmbach implication.  (Contributed by NM, 16-Nov-1997.) $)
  i3th5 $p |- ( ( a ->3 b ) ->3 ( a ->3 ( a ->3 b ) ) ) = 1 $=
    ( wi3 wn wa wo ax-a2 lea lear le2or bltr oridm lbtr df-i3 lem4 le3tr1 lei3
    ) ABCZARCZADZBEZTBDZEZFZATBFZEZFZUERSUGUEUEFUEUDUEUFUEUDUCUAFUEUAUCGUCTUABT
    UBHTBIJKAUEIJUELMABNABOPQ $.

  $( Theorem for Kalmbach implication.  (Contributed by NM, 16-Nov-1997.) $)
  i3th6 $p |- ( ( a ->3 ( a ->3 ( a ->3 b ) ) ) ->3 ( a ->3 ( a ->3 b ) ) )
             = 1 $=
    ( wi3 tb i3abs1 bi1 bii3 skmp3 ) AAABCCZCZIDJICJIABEFJIGH $.

  $( Theorem for Kalmbach implication.  (Contributed by NM, 19-Nov-1997.) $)
  i3th7 $p |- ( a ->3 ( ( a ->3 b ) ->3 a ) ) = 1 $=
    ( wi3 wn wo leor lem4 ax-r1 i3abs3 ax-r2 lbtr lei3 ) AABCZACZAMDZAEZNAOFPMN
    CZNQPMAGHABIJKL $.

  $( Theorem for Kalmbach implication.  (Contributed by NM, 19-Nov-1997.) $)
  i3th8 $p |- ( ( a ->3 b ) ' ->3 ( ( a ->3 b ) ->3 a ) ) = 1 $=
    ( wi3 wn wo leo lem4 ax-r1 i3abs3 ax-r2 lbtr lei3 ) ABCZDZMACZNNAEZONAFPMOC
    ZOQPMAGHABIJKL $.

  $( Theorem for Kalmbach implication.  (Contributed by NM, 9-Nov-1997.) $)
  i3con $p |- ( ( a ->3 b ) ->3 ( ( a ->3 b ) ->3 ( b ' ->3 a ' ) ) )
              = 1 $=
    ( wn wo wt ax-a2 com2an com2or fh4 ax-a3 ancom lor orabs ax-r2 comcom3 df-t
    wa comcom ax-r1 2an wi3 ni32 i3n1 2or comor2 comcom2 or12 lea bltr leo letr
    comor1 df-le2 comorr or1 ax-r5 or4 coman2 anor1 con2 coman1 anor2 df-a 3tr1
    an1 i0i3 ) ABUAZBCZACZUAZVGCZVJDZEEQZEVLABDZAVHQZVIAVHDZQZDZQZBVIQZBAQZDZVH
    BVIDZQZDZDZVMVKVSVJWEABUBBAUCUDWFWEVSDZVMVSWEFWGWEVNDZWEVRDZQVMVNWEVRVNWBWD
    VNVTWAVNBVIABUEZVNAABULZUFZGVNBAWJWKGHVNVHWCVNBWJUFZVNBVIWJWLHGHVNVOVQVNAVH
    WKWMGVNVIVPWLVNAVHWKWMHGHIWHEWIEWHWBWDVNDZDZEWBWDVNJWOWDWBVNDZDZEWBWDVNUGWQ
    WNEWPVNWDWPVTWAVNDZDZVNVTWAVNJWSVTVNDZVNWRVNVTWAVNWAAVNWAABQABAKABUHUIABUJU
    KUMLWTVNVTDZVNVTVNFXAABVTDZDVNABVTJXBBABVIMLNNNNLWNVNWDDZEWDVNFXCVNVHDZVNWC
    DZQZEVHVNWCBVNVNBWJROBWCBVIUNOZIXFVMEXDEXEEXDABVHDZDZEABVHJXIAEDEXHEAEXHBPS
    LAUONNXEBADZWCDZEVNXJWCABFUPXKBBDZAVIDZDZEBABVIUQXNXLEDEXMEXLEXMAPSLXLUONNN
    TEVEZNNNNNNWIWBWDVRDZDZEWBWDVRJXQWAVIBQZDZVHVQDZDZEWBXSXPXTWBWAVTDXSVTWAFVT
    XRWABVIKLNXPWDVODZVQDZXTYCXPWDVOVQJSYBVHVQYBVOWDDZVHWDVOFYDVOVHDZVOWCDZQZVH
    VHVOWCVOVHAVHURRXGIYGVHEQVHYEVHYFEYEVHVODZVHVOVHFYHVHVHAQZDVHVOYIVHAVHKLVHA
    MNNYFVOVOCZDZEWCYJVOWCVIBDZYJBVIFYJYLVOYLABUSUTSNLEYKVOPSNTVHVENNNUPNUDYAWA
    VHDZXRVQDZDZEWAXRVHVQUQYOYMVIDZEYNVIYMYNXRVIDZXRVPDZQZVIVIXRVPXRVIVIBVARAVP
    AVHUNOIYSVIEQVIYQVIYREYQVIXRDVIXRVIFVIBMNYRXRXRCZDZEVPYTXRYTVPXRVPABVBUTSLE
    UUAXRPSNTVIVENNLWAVHVIDZDWAWACZDYPEUUBUUCWAUUCUUBWAUUBBAVCUTSLWAVHVIJWAPVDN
    NNNTNNNXONVF $.

  $( Lemma for Kalmbach implication OR builder.  (Contributed by NM,
     11-Nov-1997.) $)
  i3orlem1 $p |- ( ( a v c ) ^ ( ( a v c ) ' v ( b v c ) ) ) =<
                 ( ( a v c ) ->3 ( b v c ) ) $=
    ( wo wn wa wi3 leor df-i3 ax-r1 lbtr ) ACDZLEZBCDZDFZMNFMNEFDZODZLNGZOPHRQL
    NIJK $.

  $( Lemma for Kalmbach implication OR builder.  (Contributed by NM,
     11-Nov-1997.) $)
  i3orlem2 $p |- ( a ^ b ) =< ( ( a v c ) ->3 ( b v c ) ) $=
    ( wa wo wi3 leo le2an wn leor ledi letr i3orlem1 ) ABDACEZBCEZDZNOFZANBOACG
    BCGHPNNIZOEDZQPNRDZPESPTJNROKLABCMLL $.

  $( Lemma for Kalmbach implication OR builder.  (Contributed by NM,
     11-Nov-1997.) $)
  i3orlem3 $p |- c =< ( ( a v c ) ->3 ( b v c ) ) $=
    ( wo wn wi3 ax-a2 lan anabs ax-r2 ax-r1 leor lelor le2an bltr i3orlem1 letr
    wa ) CACDZSEZBCDZDZRZSUAFCCTCDZRZUCUECUECCTDZRCUDUFCTCGHCTIJKCSUDUBCALCUATC
    BLMNOABCPQ $.

  $( Lemma for Kalmbach implication OR builder.  (Contributed by NM,
     11-Nov-1997.) $)
  i3orlem4 $p |- ( ( a v c ) ' ^ ( b v c ) ) =<
                 ( ( a v c ) ->3 ( b v c ) ) $=
    ( wo wn wa wi3 leo ler df-i3 ax-r1 lbtr ) ACDZEZBCDZFZPNOEFZDZMNODFZDZMOGZP
    RSPQHIUATMOJKL $.

  $( Lemma for Kalmbach implication OR builder.  (Contributed by NM,
     11-Nov-1997.) $)
  i3orlem5 $p |- ( ( a ' ^ b ' ) ^ c ' ) =<
                 ( ( a v c ) ->3 ( b v c ) ) $=
    ( wo wn wa wi3 leo anandir oran con2 ax-r1 2an ax-r2 df2i3 le3tr1 ) ACDZEZB
    CDZEZFZUARSDQRSFDFZDAEZBEZFCEZFZQSGUAUBHUFUCUEFZUDUEFZFUAUCUDUEIUGRUHTRUGQU
    GACJKLTUHSUHBCJKLMNQSOP $.

  $( Lemma for Kalmbach implication OR builder.  (Contributed by NM,
     11-Nov-1997.) $)
  i3orlem6 $p |- ( ( a ->3 b ) ' v ( ( a v c ) ->3 ( b v c ) ) ) =
   ( ( ( a v b ) ^ ( a ' ->3 b ' ) ) v ( ( a v c ) ->3 ( b v c ) ) ) $=
    ( wa wi3 wn wo ax-a3 ax-r1 i3orlem2 lerr df-le2 oi3ai3 ax-r5 3tr2 ) ABDZABE
    FZACGBCGEZGZGZPQGZRGZSABGAFBFEDZRGUBTPQRHIPSPRQABCJKLUAUCRABMNO $.

  $( Lemma for Kalmbach implication OR builder.  (Contributed by NM,
     11-Nov-1997.) $)
  i3orlem7 $p |- ( a ^ b ' ) =<
         ( ( a ->3 b ) ' v ( ( a v c ) ->3 ( b v c ) ) ) $=
    ( wn wa wo wi3 lea leo letr ler2an ler i3n1 lan comor1 comcom2 com2an ax-r1
    com2or lbtr comor2 fh1 ax-r2 i3orlem6 ) ABDZEZABFZADZUEGZEZACFBCFGZFZABGDUK
    FZUFUJUKUFUGUFABEZFZEZUGUHAUEFZEZEZFZUJUFUPUSUFUGUOUFAUGAUEHABIJUFUNIKLUJUT
    UJUGUOURFZEUTUIVAUGABMNUGUOURUGUFUNUGAUEABOZUGBABUAZPZQUGABVBVCQSUGUHUQUGAV
    BPUGAUEVBVDSQUBUCRTLUMULABCUDRT $.

  $( Lemma for Kalmbach implication OR builder.  (Contributed by NM,
     11-Nov-1997.) $)
  i3orlem8 $p |- ( ( ( a v b ) ^ ( a v b ' ) ) ^ a ' ) =<
         ( ( a ->3 b ) ' v ( ( a v c ) ->3 ( b v c ) ) ) $=
    ( wo wn wa wi3 anass ancom lan ax-r2 leor bltr comor1 comcom2 com2an com2or
    i3n1 ax-r1 lbtr comor2 fh1 ler i3orlem6 ) ABDZABEZDZFAEZFZUEUHUFGZFZACDBCDG
    ZDZABGEULDZUIUKULUIUEAUFFZABFZDZFZUEUHUGFZFZDZUKUIUTVAUIUEUGUHFZFUTUEUGUHHV
    BUSUEUGUHIJKUTURLMUKVAUKUEUQUSDZFVAUJVCUEABRJUEUQUSUEUOUPUEAUFABNZUEBABUAZO
    ZPUEABVDVEPQUEUHUGUEAVDOUEAUFVDVFQPUBKSTUCUNUMABCUDST $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Unified disjunction
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Lemma for unified disjunction.  (Contributed by NM, 23-Nov-1997.) $)
  ud1lem1 $p |- ( ( a ->1 b ) ->1 ( b ->1 a ) ) =
              ( a v ( a ' ^ b ' ) ) $=
    ( wi1 wn wa df-i1 ud1lem0c 2an 2or ancom lor lan coman1 comcom2 coman2 fh3r
    wo ax-r1 ax-r2 wt or12 comcom comorr comcom5 fh4r orabs df-a df-t an1 ax-a2
    ) ABCZBACZCUKDZUKULEZQZAADZBDZEZQZUKULFUOAUPUQQZEZUPABEZQZUQBAEZQZEZQZUSUMV
    AUNVFABGUKVCULVEABFBAFHIVGVAURVBQZQZUSVFVHVAVFVCUQVBQZEZVHVEVJVCVDVBUQBAJKL
    VHVKVBUPUQVBAABMZNVBBABONPRSKVIURVAVBQZQZUSVAURVBUAVNURAVBQZUTVBQZEZQZUSVMV
    QURAVBUTVBAVLUBAUTUPUTUPUQUCNUDUEKVRURAQUSVQAURVQATEAVOAVPTABUFVPUTUTDZQZTV
    BVSUTABUGKTVTUTUHRSHAUISKURAUJSSSSSS $.

  $( Lemma for unified disjunction.  (Contributed by NM, 23-Nov-1997.) $)
  ud1lem2 $p |- ( ( a v ( a ' ^ b ' ) ) ->1 a ) = ( a v b ) $=
    ( wn wa wo wi1 df-i1 comid comcom3 comor1 fh3 wt ancom ax-a2 df-t ax-r1 lan
    ax-r2 oran 3tr an1 ax-r4 con2 ax-r5 oml ) AACZBCDZEZAFUHCZUHADEUIUHEZUIAEZD
    ZABEZUHAGUIUHAUHUHUHHIUHAAUGJIKULUKUJDUKLDZUMUJUKMUJLUKUJUHUIEZLUIUHNLUOUHO
    PRQUNUKUFUMDZAEZUMUKUAUIUPAUHUPUHUFUGCZDZCUPCAUGSUSUPURUMUFUMURABSPQUBRUCUD
    UQAUPEUMUPANABUERTTT $.

  $( Lemma for unified disjunction.  (Contributed by NM, 23-Nov-1997.) $)
  ud1lem3 $p |- ( ( a ->1 b ) ->1 ( a v b ) ) = ( a v b ) $=
    ( wi1 wo wn wa df-i1 ud1lem0c con3 ran 2or comid comcom2 df-t ax-r1 lan an1
    wt comorr ax-r2 comor1 comor2 com2or com2an comcom ancom comcom5 fh4r ax-a2
    fh3 or4 lor or1 ax-a3 oridm ax-r5 ) ABCZABDZCUQEZUQURFZDZURUQURGVAAAEZBEZDZ
    FZVEEZURFZDZURUSVEUTVGABHZUQVFURUQVEVIIJKVHVEVFDZVEURDZFZURVEVFURVEVEVELMUR
    VEURAVDABUAZURVBVCURAVMMURBABUBMUCUDUEUJVLVKVJFZURVJVKUFVNVKRFZURVJRVKRVJVE
    NOPVOVKURVKQVKAURDZVDURDZFZURAURVDABSAVDVBVDVBVCSMUGUHVRVPRFZURVQRVPVQURVDD
    ZRVDURUIVTAVBDZBVCDZDZRABVBVCUKWCWARDRWBRWARWBBNOULWAUMTTTPVSVPURVPQVPAADZB
    DZURWEVPAABUNOWDABAUOUPTTTTTTTTTT $.

  $( Lemma for unified disjunction.  (Contributed by NM, 22-Nov-1997.) $)
  ud2lem1 $p |- ( ( a ->2 b ) ->2 ( b ->2 a ) ) =
              ( a v ( a ' ^ b ' ) ) $=
    ( wi2 wn wa wo df-i2 ud2lem0c 2an 2or wf ancom lor dff oran ax-r1 lan ax-r2
    anandir ax-a2 ran or0 ) ABCZBACZCUDUCDZUDDZEZFZAADZBDZEZFZUCUDGUHAUJUIEZFZU
    JABFZEZUIBAFZEZEZFZULUDUNUGUSBAGUEUPUFURABHBAHIJUTULKFULUNULUSKUMUKAUJUILMK
    USKUMUQEZUSKUMUMDZEVAUMNVBUQUMUQVBBAOPQRVAUJUQEZUREUSUJUIUQSVCUPURUQUOUJBAT
    QUARRPJULUBRRR $.

  $( Lemma for unified disjunction.  (Contributed by NM, 23-Nov-1997.) $)
  ud2lem2 $p |- ( ( a v ( a ' ^ b ' ) ) ->2 a ) = ( a v b ) $=
    ( wn wa wi2 df-i2 oran con2 ax-r1 lor anor2 con3 ax-r2 ran an32 anidm oml
    wo ) AACZBCDZRZAEAUACZSDZRZABRZUAAFUDASUEDZRUEUCUFAUCUAARZCZUFUHUCUGUCUAAGH
    ZIUHUCUFUIUCUFSDZUFUBUFSUAUFUAAUECZRZUFCTUKAUKTUETABGHIJULUFUFULCAUEKILMHNU
    JSSDZUEDUFSUESOUMSUESPNMMMMJABQMM $.

  $( Lemma for unified disjunction.  (Contributed by NM, 23-Nov-1997.) $)
  ud2lem3 $p |- ( ( a ->2 b ) ->2 ( a v b ) ) = ( a v b ) $=
    ( wi2 wo wn wa df-i2 ud2lem0c ran lor coman2 comcom comid comcom2 fh3 ancom
    wt df-t ax-r1 ax-r2 2an an1 orabs ) ABCZABDZCUEUDEZUEEZFZDZUEUDUEGUIUEBEZUE
    FZUGFZDZUEUHULUEUFUKUGABHIJUMUEUKDZUEUGDZFZUEUEUKUGUKUEUJUEKLUEUEUEMNOUPUEU
    EUJFZDZQFZUEUNURUOQUKUQUEUJUEPJQUOUERSUAUSURUEURUBUEUJUCTTTTT $.

  $( Lemma for unified disjunction.  (Contributed by NM, 27-Nov-1997.) $)
  ud3lem1a $p |- ( ( a ->3 b ) ' ^ ( b ->3 a ) ) = ( a ^ b ' ) $=
    ( wn wa wo 2an comor2 comor1 com2an comcom2 com2or comcom anass ancom ax-r2
    wf lan ax-r1 dff an0 ud3lem0c comanr2 comcom3 coman2 coman1 comanr1 comcom6
    wi3 df-i3 fh2 comcom7 ax-a2 anabs lea leo ler2an letr df2le2 an32 oran con3
    ran an0r 2or or0 fh2r or0r anor1 ) ABUHCZBAUHZDABCZEZABEZDZACZAVKDZEZDZVKAD
    ZVKVODZEZBVKAEZDZEZDZVPVIVRVJWDABUABAUIFWEVRWADZVRWCDZEZVPWAVRWCWAVNVQWAVLV
    MVLWAVLVSVTVLVKAAVKGZAVKHZIVLVKVOWIVLAWJJIKLVMWAVMVSVTVMVKAVMBABGJZABHZIVMV
    KVOWKVMAWLJIKLIWAVOVPVOWAVOVSVTAVSVKAUBUCVKVOUBKLVPWAVPVSVTVPVKAAVKUDZAVKUE
    ZIVPVKVOWMVPAWNJZIKLKIWABWBBWABVSVTBVSVKAUFUGBVTVKVOUFUGKLWBWAWBVSVTWBVKAVK
    AHZVKAGZIWBVKVOWPWBAWQJIKLIUJWHVPPEZVPWFVPWGPWFVRVSDZVRVTDZEZVPVSVRVTVSVNVQ
    VSVLVMVSAVKVKAUDZVKAUEZKVSABXBVSBXCUKKIVSVOVPVSAXBJZVSAVKXBXCIKIVSVKVOXCXDI
    UJXAWRVPWSVPWTPWSVNVQVSDZDZVPVNVQVSMXFVNVPDZVPXEVPVNXEVSVQDZVPVQVSNXHVPVPVO
    EZDVPVSVPVQXIVKANVOVPULZFVPVOUMOOQXGVPVNDVPVNVPNVPVNVPAVNAVKUNAVLVMAVKUOABU
    OUPUQUROOOWTVNVTDZVQDZPVNVQVTUSXLPVQDPXKPVQXKVLVMVTDZDZPVLVMVTMXNVLPDPXMPVL
    XMBAEZXOCZDZPVMXOVTXPABULVTXOXOVTCBAUTRVAFPXQXOSROQVLTOOVBVQVCOOVDVPVEZOOWG
    VNVQWCDZDZPVNVQWCMXTVNPDPXSPVNXSVQBDZWBDZPYBXSVQBWBMRYBBVODZWBDZPYAYCWBYAXI
    BDZYCVQXIBXJVBYEVPBDZVOBDZEZYCVPBVOVPBWMUKWOVFYHPYCEYCYFPYGYCYFAVKBDZDZPAVK
    BMYJAPDPYIPAYIBVKDZPVKBNPYKBSROQATOOVOBNVDYCVGOOOVBYDYCYCCZDZPWBYLYCWBYCYCW
    BCBAVHRVAQPYMYCSROOOQVNTOOVDXROOO $.

  $( Lemma for unified disjunction.  (Contributed by NM, 27-Nov-1997.) $)
  ud3lem1b $p |- ( ( a ->3 b ) ' ^ ( b ->3 a ) ' ) = 0 $=
    ( wi3 wn wa wo ud3lem0c 2an an32 comor2 comcom7 ancom ax-a2 lan ax-r2 ax-r1
    wf dff anass ran an12 comor1 comcom2 com2an fh1 anabs anor1 anidm fh1r oran
    2or or0 ) ABCDZBACDZEABDZFZABFZEZADZAUOEZFZEZBUSFZBAFZEZUOBUSEZFZEZEZQUMVBU
    NVHABGBAGHVIURVHEZVAEZQURVAVHIVKUOVDEZVCEZVAEZQVJVMVAVJUPVHEZUQEZVMUPUQVHIV
    PUOVCEZVDEZUQEZVMVOVRUQVOVEUPVGEZEZVRUPVEVGUAWAVEUOEZVRVTUOVEVTUPUOEZUPVFEZ
    FZUOUPUOVFAUOJZUPBUSUPBWFKUPAAUOUBUCUDUEWEUOQFUOWCUOWDQWCUOUOAFZEZUOWCUOUPE
    WHUPUOLUPWGUOAUOMZNOUOAUFOWDWGWGDZEZQUPWGVFWJWIBAUGHQWKWGRPOUKUOULOONWBUOVE
    EZVRVEUOLVRWLUOVCVDSPOOOTVSVRVDEZVMUQVDVRABMNWMVQVDVDEZEZVMVQVDVDSWOVRVMWNV
    DVQVDUHNUOVCVDIOOOOOTVNVLVCVAEZEZQVLVCVASWQVLUSEZQWPUSVLWPUSBFZVAEZUSVCWSVA
    BUSMTWTVAWSEZUSWSVALXAUSWSEZUTWSEZFZUSWSUSUTUSBUBZWSAUOWSAXEKWSBUSBJUCUDUIX
    DUSQFUSXBUSXCQUSBUFXCWSUTEZQUTWSLXFWSWSDZEZQUTXGWSABUGNQXHWSRPOOUKUSULOOOON
    WRUOUSEZVDEZQUOVDUSIXJXIXIDZEZQVDXKXIBAUJNQXLXIRPOOOOOOO $.

  $( Lemma for unified disjunction.  (Contributed by NM, 27-Nov-1997.) $)
  ud3lem1c $p |- ( ( a ->3 b ) ' v ( b ->3 a ) ) = ( a v b ' ) $=
    ( wn wo wa 2or coman2 coman1 com2or comcom7 com2an comcom ax-a2 ax-r2 ax-a3
    wt ax-r1 df-t lor or1 ud3lem0c comorr2 comcom6 comor2 comor1 comorr comcom3
    wi3 df-i3 fh4r comcom2 lea lel2or leor letr lear lbtr or12 ancom oran ax-r5
    df-le2 or1r 2an an1 fh4 ran an1r anor1 ) ABUHCZBAUHZDABCZDZABDZEZACZAVLEZDZ
    EZVLAEZVLVPEZDZBVLADZEZDZDZVMVJVSVKWEABUABAUIFWFVOWEDZVRWEDZEZVMVOWEVRVOWBW
    DVOVTWAVTVOVTVMVNVTAVLVLAGZVLAHZIVTABWJVTBWKJIKLWAVOWAVMVNWAAVLWAAVLVPGJZVL
    VPHZIWAABWLWABWMJIKLIVOBWCBVOBVMVNBVMAVLUBUCABUBKLWCVOWCVMVNWCAVLVLAUDZVLAU
    EZIWCABWNWCBWOJZIKLKIVOVPVQVPVOVPVMVNAVMAVLUFUGAVNABUFUGKLVQVOVQVMVNVQAVLAV
    LHZAVLGZIVQABWQVQBWRJIKLIUJWIVMPEZVMWGVMWHPWGVMWEDZVNWEDZEZVMVMWEVNVMWBWDVM
    VTWAVMVLAAVLUDZAVLUEZKVMVLVPXCVMAXDUKKIVMBWCVMBXCJZVMVLAXCXDIKIVMABXDXEIUJX
    BWSVMWTVMXAPWTWEVMDVMVMWEMWEVMWBVMWDWBVLVMVTVLWAVLAULVLVPULUMVLAUNUOWDWCVMB
    WCUPVLAMUQUMVBNXAWBVNWDDDZPVNWBWDURXFWBVNDZWDDZPXHXFWBVNWDOQXHPWDDPXGPWDXGV
    TWAVNDZDZPVTWAVNOXJVTPDPXIPVTXIVPVLEZXKCZDZPWAXKVNXLVLVPUSABUTFPXMXKRQNSVTT
    NNVAWDVCNNNVDVMVEZNNWHWBVRWDDZDZPVRWBWDURXPWBPDPXOPWBXOVQVPDZWCBEZDZPVRXQWD
    XRVPVQMBWCUSFXSVQVPXRDZDZPVQVPXROYAVQVPBDZDZPXTYBVQXTVPWCDZYBEZYBWCVPBWCAWN
    UKWPVFYEPYBEYBYDPYBYDWCVPDZPVPWCMYFVLAVPDZDZPVLAVPOYHVLPDPYGPVLPYGARQSVLTNN
    NVGYBVHNNSYCYBVQDZPVQYBMYIYBYBCZDZPVQYJYBABVISPYKYBRQNNNNNSWBTNNVDXNNNN $.

  $( Lemma for unified disjunction.  (Contributed by NM, 27-Nov-1997.) $)
  ud3lem1d $p |- ( ( a ->3 b ) ^ ( ( a ->3 b ) ' v ( b ->3 a ) ) ) =
              ( ( a ' ^ b ' ) v ( a ^ ( a ' v b ) ) ) $=
    ( wi3 wn wo wa df-i3 ud3lem1c 2an comor1 comcom2 comor2 comcom7 com2an fh1r
    com2or an32 ax-r2 2or wf anabs ran ancom anor2 lan dff ax-r1 lear leor letr
    df2le2 or0r ax-r5 ) ABCZUNDBACEZFADZBFZUPBDZFZEZAUPBEZFZEZAUREZFZUSVBEZUNVC
    UOVDABGABHIVEUTVDFZVBVDFZEZVFVDUTVBVDUQUSVDUPBVDAAURJZKZVDBAURLZMZNZVDUPURV
    KVLNZPVDAVAVJVDUPBVKVMPNOVIUQVDFZUSVDFZEZVBEVFVGVRVHVBVDUQUSVNVOOVHAVDFZVAF
    VBAVAVDQVSAVAAURUAUBRSVRUSVBVRTUSEUSVPTVQUSVPVDUQFZTUQVDUCVTVDVDDZFZTUQWAVD
    ABUDUETWBVDUFUGRRUSVDUSURVDUPURUHURAUIUJUKSUSULRUMRRR $.

  $( Lemma for unified disjunction.  (Contributed by NM, 27-Nov-1997.) $)
  ud3lem1 $p |- ( ( a ->3 b ) ->3 ( b ->3 a ) ) =
              ( a v ( a ' ^ b ' ) ) $=
    ( wi3 wn wa wo df-i3 wf ud3lem1a ud3lem1b 2or ax-r2 ud3lem1d coman1 comcom2
    or0 coman2 wt ax-a2 lor comcom7 com2or fh3 orabs anor1 df-t ax-r1 or12 3tr1
    2an an1 ) ABCZBACZCULDZUMEZUNUMDEZFZULUNUMFEZFZAADZBDZEZFZULUMGUSAVAEZVBAUT
    BFZEZFZFZVCUQVDURVGUQVDHFVDUOVDUPHABIABJKVDPLABMKVBVDVFFZFVBAFVHVCVIAVBVIVD
    AFZVDVEFZEZAVDAVEAVANZVDUTBVDAVMOVDBAVAQUAUBUCVLAREAVJAVKRVJAVDFAVDASAVAUDL
    VKVEVDFZRVDVESVNVEVEDZFZRVDVOVEABUETRVPVEUFUGLLUJAUKLLTVDVBVFUHAVBSUILL $.

  $( Lemma for unified disjunction.  (Contributed by NM, 23-Nov-1997.) $)
  ud3lem2 $p |- ( ( a v ( a ' ^ b ' ) ) ->3 a ) = ( a v b ) $=
    ( wn wa wo wi3 oran ax-r1 con3 lor anor2 ax-r2 ax-a2 wf ran lan dff 2or or0
    ancom ud3lem0b df-i3 ax-a3 ax-a1 an32 anidm ax-r5 2an oml comorr fh2r anabs
    comcom2 anass an0 ) AACZBCDZEZAFUPABEZDZCZAFZUSURVAAURAUSCZEZVAUQVCAUQUSUSU
    QCABGHIJVDUTUTVDCAUSKHIZLUAVBVACZADZVFUPDZEVAVFAEZDZEZUSVAAUBVKVGVHVJEZEZUS
    VGVHVJUCVMVLVGEZUSVGVLMVNUSNEUSVLUSVGNVLAUTEZUSVLUTAEZVOVHUTVJAVHUTUPDZUTVQ
    VHUTVFUPUTUDZOHVQUPUPDZUSDUTUPUSUPUEVSUPUSUPUFOLLVJVDVPDZAVTVJVDVAVPVIVEUTV
    FAVRUGUHHVTVDUSDZAVPUSVDVPVOUSUTAMZABUIZLPWAAUSDZVCUSDZEZAAUSVCABUJZAUSWGUM
    UKWFANEAWDAWENABULWEUSVCDZNVCUSTNWHUSQHLRASLLLLRWBLWCLVGAVFDZNVFATWIAUTDZNW
    JWIUTVFAVRPHWJAUPDZUSDZNWLWJAUPUSUNHWLUSWKDZNWKUSTWMUSNDZNWNWMNWKUSAQPHUSUO
    LLLLLRUSSLLLLL $.

  $( Lemma for unified disjunction.  (Contributed by NM, 27-Nov-1997.) $)
  ud3lem3a $p |- ( ( a ->3 b ) ' ^ ( a v b ) ) = ( a ->3 b ) ' $=
    ( wi3 wn wo wa ud3lem0c lea lear letr bltr df2le2 ) ABCDZABEZMABDZEZNFZADAO
    FEZFZNABGSQNQRHPNIJKL $.

  $( Lemma for unified disjunction.  (Contributed by NM, 27-Nov-1997.) $)
  ud3lem3b $p |- ( ( a ->3 b ) ' ^ ( a v b ) ' ) = 0 $=
    ( wi3 wn wo wa wf ud3lem0c ran an32 anass dff ax-r1 lan an0 ax-r2 an0r ) AB
    CDZABEZDZFABDZEZSFZADAUAFEZFZTFZGRUETABHIUFUCTFZUDFZGUCUDTJUHGUDFGUGGUDUGUB
    STFZFZGUBSTKUJUBGFGUIGUBGUISLMNUBOPPIUDQPPP $.

  $( Lemma for unified disjunction.  (Contributed by NM, 27-Nov-1997.) $)
  ud3lem3c $p |- ( ( a ->3 b ) ' v ( a v b ) ) = ( a v b ) $=
    ( wi3 wn wo wa ud3lem0c an32 ancom ax-r2 ax-r5 ax-a2 orabs ) ABCDZABEZEOABD
    ZEZADAPFEZFZFZOEZONTONQOFRFZTABGUBSOFTQORHSOIJJKUAOTEOTOLOSMJJ $.

  $( Lemma for unified disjunction.  (Contributed by NM, 27-Nov-1997.) $)
  ud3lem3d $p |- ( ( a ->3 b ) ^ ( ( a ->3 b ) ' v ( a v b ) ) ) =
              ( ( a ' ^ b ) v ( a ^ ( a ' v b ) ) ) $=
    ( wi3 wn wo wa ud3lem3c 2an comor1 comcom2 comor2 com2an com2or fh1r coman1
    df-i3 wf letr df2le2 ax-r2 comcom7 coman2 fh2r lear leor oran lan dff ax-r1
    2or or0 ax-r5 lea leo lor ) ABCZUPDABEZEZFADZBFZUSBDZFZEZAUSBEZFZEZUQFZUTVE
    EZUPVFURUQABPABGHVGVCUQFZVEUQFZEZVHUQVCVEUQUTVBUQUSBUQAABIZJZABKZLUQUSVAVMU
    QBVNJLMUQAVDVLUQUSBVMVNMLNVKUTVJEVHVIUTVJVIUTUQFZVBUQFZEZUTUTUQVBUTABUTAUSB
    OZUAUSBUBZMUTUSVAVRUTBVSJLUCVQUTQEUTVOUTVPQUTUQUTBUQUSBUDBAUERSVPVBVBDZFZQU
    QVTVBABUFUGQWAVBUHUITUJUTUKTTULVJVEUTVEUQVEAUQAVDUMABUNRSUOTTT $.

  $( Lemma for unified disjunction.  (Contributed by NM, 27-Nov-1997.) $)
  ud3lem3 $p |- ( ( a ->3 b ) ->3 ( a v b ) ) = ( a v b ) $=
    ( wi3 wo wn wa ax-r2 2or coman1 comcom7 coman2 comcom2 com2or com2an comcom
    wf comorr wt ax-r1 lor df-i3 ud3lem3a ud3lem0c ud3lem3b or0 ud3lem3d comor1
    comor2 comcom3 fh4r ax-a3 anor2 df-t ax-r5 or1r ax-a2 lear leor letr lel2or
    lea leo df-le2 2an an1r or12 df-a anor1 ax-r4 or1 an1 ) ABCZABDZCVLEZVMFZVN
    VMEFZDZVLVNVMDFZDZVMVLVMUAVSABEZDZVMFZAEZAVTFZDZFZWCBFZAWCBDZFZDZDZVMVQWFVR
    WJVQWFPDWFVOWFVPPVOVNWFABUBABUCGABUDHWFUEGABUFHWKWBWJDZWEWJDZFZVMWBWJWEWBWG
    WIWGWBWGWAVMWGAVTWGAWCBIJZWGBWCBKZLMWGABWOWPMNOWBAWHAWBAWAVMAVTQZABQZNOWHWB
    WHWAVMWHAVTWHAWCBUGJZWHBWCBUHZLMWHABWSWTMNONMWBWCWDWCWBWCWAVMAWAWQUIAVMWRUI
    NOWDWBWDWAVMWDAVTAVTIZAVTKZMWDABXAWDBXBJMNOMUJWNVMRFVMWLVMWMRWLWAWJDZVMWJDZ
    FZVMWAWJVMWAWGWIWAWCBWAAAVTUGZLZWABAVTUHJZNWAAWHXFWAWCBXGXHMNMWAABXFXHMUJXE
    RVMFVMXCRXDVMXCWAWGDZWIDZRXJXCWAWGWIUKSXJRWIDRXIRWIXIWAWAEZDZRWGXKWAABULTRX
    LWAUMSGUNWIUOGGXDWJVMDVMVMWJUPWJVMWGVMWIWGBVMWCBUQBAURUSWIAVMAWHVAABVBUSUTV
    CGVDVMVEGGWMWGWEWIDZDZRWEWGWIVFXNWGRDRXMRWGXMWEWEEZDZRWIXOWEWIWCWHEZDZEXOAW
    HVGXRWEXQWDWCWDXQABVHSTVIGTRXPWEUMSGTWGVJGGVDVMVKGGGG $.

  $( Lemma for unified disjunction.  (Contributed by NM, 24-Nov-1997.) $)
  ud4lem1a $p |- ( ( a ->4 b ) ^ ( b ->4 a ) ) =
              ( ( a ^ b ) v ( a ' ^ b ' ) ) $=
    ( wa wn wo coman2 comcom com2or coman1 comcom2 com2an comcom3 ancom 2or lan
    wf dff ax-r1 an0 ax-r2 wi4 df-i4 2an comcom5 fh2r ax-a2 ran fh1 an4 lor fh3
    or0 3tr2 an12 an32 anass anor2 con3 fh2 lecon lelan oran anor1 ax-r4 le3tr1
    lea con2 le0 lebi leo le2an df2le2 ) ABUAZBAUAZCABCZADZBCZEZVPBEZBDZCZEZBAC
    ZVTACZEZVTAEZVPCZEZCZVOVPVTCZEZVMWBVNWHABUBBAUBUCWIVRWHCZWAWHCZEWKVRWHWAVRW
    EWGVRWCWDVRBABVRBVOVQVOBABFZGZVQBVPBFGZHGZAVRAVOVQVOAABIZGZAVQVPVQVQVPVPBIG
    ZJUDHGZKVRVTAVTVRVTVOVQBVOWOLBVQWPLHGZXAKHVRWFVPVRVTAXBXAHVPVRVPVOVQAVOWSLW
    THGZKHVRVSVTVRVPBXCWQHVRBWQJZKUEWLVOWMWJWLVOPEZVOWLVRVOAVTCZEZAVTEZVPCZEZCZ
    XEWHXJVRWEXGWGXIWCVOWDXFBAMVTAMZNWFXHVPVTAUFUGNOXKVRXGCZVRXICZEXEVRXGXIVRVO
    XFVRABXAWQKVRAVTXAXBKHVRXHVPVRAVTXAXDHXCKUHXMVOXNPVOVQXFCZEXEXMVOXOPVOXOVPA
    CZBVTCZCZPVPBAVTUIXRXPPCPXQPXPPXQBQROXPSTTUJVOVQXFVOVPBVOAWRJZWNKZVOAVTWRVO
    BWNJZKUKVOULZUMXNVOXICZVQXICZEZPVOXIVQVOXHVPVOAVTWRYAHXSKXTUEYEPPEPYCPYDPYC
    XHVOVPCZCZPVOXHVPUNYGXHPCPYFPXHYFAVPCZBCZPABVPUOYIBYHCZPYHBMYJBPCPYHPBPYHAQ
    ROBSTTTOXHSTTVQXHCZVPCVPYKCZYDPYKVPMVQXHVPUPYLVPPCPYKPVPYKVQVQDZCZPXHYMVQXH
    VQVQXHDABUQRUROPYNVQQRTOVPSTUMNPULTTNTTYBTWMWAWECZWAWGCZEZWJWEWAWGWEVSVTWEV
    PBVPWEAWEAWCWDWCABAFGZWDAVTAFGZHZLGBWEBWCWDWCBBAIGZBWDVTWDWDVTVTAIGZJUDHGHV
    TWEVTWCWDBWCUUALUUBHGZKWEWFVPWEVTAUUCAWEYTGHVPWEVPWCWDAWCYRLAWDYSLHGKUSYQPW
    JEZWJYOPYPWJYOPWAVSWCDZCZDZCWAWADZCYOPUUGUUHWAWAUUFVTUUEVSWCBBAVFUTVAUTVAWE
    UUGWAWEWDWCEZUUGWCWDUFUUIWDDZUUECZDUUGWDWCVBUUKUUFUUJVSUUEWDVSWDXFVSDXLABVC
    TVGUGVDTTOWAQVEYOVHVIYPVSWFCZVTVPCZCZWJVSVTWFVPUIUUNUUMWJUUNUUMUULCZUUMUULU
    UMMUUOUUMWFVSCZCUUMUULUUPUUMVSWFMOUUMUUPVTWFVPVSVTAVJVPBVJVKVLTTVTVPMTTNUUD
    WJPEWJPWJUFWJULTTTNTT $.

  $( Lemma for unified disjunction.  (Contributed by NM, 25-Nov-1997.) $)
  ud4lem1b $p |- ( ( a ->4 b ) ' ^ ( b ->4 a ) ) =
              ( a ^ b ' ) $=
    ( wn wa wo coman2 comcom2 coman1 com2or comcom com2an comcom5 wf an32 ax-r2
    dff ancom an0 2or lan wi4 ud4lem0c df-i4 2an comor2 comor1 comcom3 fh2 df-a
    ax-a2 ax-r1 ran lea leor letr lear leo ler2an bltr 3tr1 or0 anass fh2r an12
    df2le2 anor1 ) ABUACZBAUAZDACZBCZEZAVJEZDZAVJDZBEZDZBADZVJADZEZVJAEZVIDZEZD
    ZVNVGVPVHWBABUBBAUCUDWCVPVSDZVPWADZEZVNVSVPWAVSVMVOVSVKVLVKVSVKVQVRVQVKVQVI
    VJVQABAFZGVQBBAHZGZIZJVRVKVRVIVJVRAVJAFZGVJAHZIJIJVLVSVLVQVRVQVLVQAVJWGWIIZ
    JVLVJAAVJUEAVJUFKIJKVSVNBVNVSVNVQVRVNBAVNBVNVJAVJFZUGLZAVJHZKVNVJAWNWPKIJBV
    SBVQVRVQBWHJBVRVJVRVRVJWLJGLIJIKVSVTVIVTVSVTVQVRVTBAVTBVTVJVJAUFZUGLVJAUEZK
    VTVJAWQWRKIJVSAAVSAVQVRVQAWGJVRAWKJIJGKUHWFVNMEZVNWDVNWEMWDVPVQDZVPVRDZEZVN
    VQVPVRVQVMVOVQVKVLWJWMKVQVNBVQAVJWGWIKWHIKVQVJAWIWGKUHXBWSVNXBMVNEWSWTMXAVN
    WTVMVQDZVODZMVMVOVQNXDMVODZMXCMVOXCVKVQDZVLDZMVKVLVQNXGMVLDZMXFMVLXFVJVIEZX
    ICZDZMVKXIVQXJVIVJUJBAUIUDMXKXIPUKOULXHVLMDMMVLQVLROOOULXEVOMDMMVOQVOROOOVR
    VPDVRXAVNVRVPVRVMVOVRVKVLVRVJVKVJAUMVJVIUNUOVRAVLVJAUPAVJUQUOURVRVNVOVJAQVN
    BUQUSURVEVPVRQAVJQUTSMVNUJOVNVAZOOWEVMVOWADZDZMVMVOWAVBXNVMMDMXMMVMXMVNWADZ
    BWADZEZMVNWABVNVTVIVNVJAWNWPIVNAWPGKWOVCXQMMEMXOMXPMXOVTVNVIDZDZMVNVTVIVDXS
    VTMDMXRMVTXRAVIDZVJDZMAVJVINYAVJXTDZMXTVJQYBVJMDMXTMVJMXTAPUKTVJROOOTVTROOV
    TBVIDZDVTVTCZDXPMYCYDVTBAVFTBVTVIVDVTPUTSMVAOOTVMROOSXLOOO $.

  $( Lemma for unified disjunction.  (Contributed by NM, 25-Nov-1997.) $)
  ud4lem1c $p |- ( ( a ->4 b ) ' v ( b ->4 a ) ) =
              ( a v b ' ) $=
    ( wn wo wa comor2 comcom3 comcom5 comor1 com2an com2or comcom coman1 coman2
    comcom2 wt ax-a2 ax-a3 ax-r2 or1 ud4lem0c df-i4 comorr fh4r df-a df-t ax-r1
    wi4 2or lor 3tr2 ax-r5 lear lel2or leo letr lea lbtr 2an ancom an1 or32 or4
    df-le2 fh4 anor2 con2 3tr1 ) ABUHCZBAUHZDACZBCZDZAVLDZEZAVLEZBDZEZBAEZVLAEZ
    DZVLADZVKEZDZDZVNVIVRVJWDABUABAUBUIWEVOWDDZVQWDDZEZVNVOWDVQVOWAWCWAVOWAVMVN
    VMWAVMVSVTVMBAVMBVMVLVKVLFZGHVMAVMVKVKVLIZGHZJVMVLAWIWKJKLVNWAVNVSVTVNBAVNB
    VNVLAVLFZGHAVLIZJVNVLAWLWMJKLJLVOWBVKWBVOWBVMVNWBVKVLWBAVLAFOZVLAIZKZWBAVLW
    BAWBVKWNGHWOKJLVKVOVKVMVNVKVLUCAVNAVLUCGJLJKVOVPBVPVOVPVMVNVPVKVLVPAAVLMZOA
    VLNZKVPAVLWQWRKJLVOBVOVLVLVOVLVMVNVMVLWILVNVLWLLJLGHKUDWHVNPEZVNWFVNWGPWFVM
    WDDZVNWDDZEZVNVMWDVNVMWAWCVMVSVTVSVMVSVKVLVSABANOVSBBAMOKLVTVMVTVKVLVTAVLAN
    OVLAMKLKVMWBVKWBVMWPLWJJKVNVMVNVKVLVNAWMOWLKLUDXBPVNEZVNWTPXAVNVMWADZWCDPWC
    DZWTPXDPWCVMVSDZVTDVTXFDZXDPXFVTQVMVSVTRXGVTPDPXFPVTXFVLVKDZXHCZDZPVMXHVSXI
    VKVLQBAUEUIPXJXHUFUGSUJVTTSUKULVMWAWCRXEWCPDPPWCQWCTSUKXAWDVNDVNVNWDQWDVNWA
    VNWCWAAVNVSAVTBAUMVLAUMUNAVLUOUPWCWBVNWBVKUQVLAQURUNVDSUSXCWSVNPVNUTVNVAZSS
    SWGWDVQDZPVQWDQXLVSVPDZPDZPXLWAVQDZWCDZXNWAWCVQVBXPXMVTBDZDZWCDZXNXOXRWCVSV
    TVPBVCULXSXMXQWCDZDXNXMXQWCRXTPXMVTBWCDZDVTVTCZDXTPYAYBVTYABWBDZBVKDZEZYBWB
    BVKWBBWBVLWOGHWNVEYEPYBEZYBYCPYDYBBVLDZADPADZYCPYGPAPYGBUFUGULBVLARYHAPDPPA
    QATSUKYBYDVTYDBAVFVGUGUSYFYBPEYBPYBUTYBVASSSUJVTBWCRVTUFVHUJSSSXMTSSUSXKSSS
    $.

  $( Lemma for unified disjunction.  (Contributed by NM, 25-Nov-1997.) $)
  ud4lem1d $p |- ( ( ( a ->4 b ) ' v ( b ->4 a ) ) ^ ( b ->4 a ) ' ) =
              ( ( ( a ' v b ' ) ^ ( a ' v b ) ) ^ a ) $=
    ( wi4 wn wo ud4lem1c ud4lem0c 2an an12 ax-a2 comor2 comcom3 comcom5 comcom2
    wa comor1 com2an fh1 wf ax-r2 anor1 dff ax-r1 ancom anabs 2or or0 ) ABCDBAC
    ZEZUHDZOABDZEZUKADZEZBUMEZOZBUMOZAEZOZOZUMUKEZUMBEZOZAOZUIULUJUSABFBAGHUTUP
    ULUROZOVDULUPURIUPVCVEAUNVAUOVBUKUMJBUMJHVEULUQOZULAOZEZAULUQAULBUMULBULUKA
    UKKLMULAAUKPZNQVIRVHSAEZAVFSVGAVFUKAEZVKDZOZSULVKUQVLAUKJBAUAHSVMVKUBUCTVGA
    ULOAULAUDAUKUETUFVJASEASAJAUGTTTHTT $.

  $( Lemma for unified disjunction.  (Contributed by NM, 25-Nov-1997.) $)
  ud4lem1 $p |- ( ( a ->4 b ) ->4 ( b ->4 a ) ) =
              ( a v ( a ' ^ b ' ) ) $=
    ( wi4 wa 2or lor coman1 comcom comcom3 com2or comcom2 comcom5 comorr com2an
    wn wo ax-r2 wt ax-a2 or1 df-i4 ud4lem1a ud4lem1b ud4lem1d ancom fh4 or4 lea
    ax-a3 lel2or leor letr df-le2 coman2 comor1 or32 df-a con2 ax-r1 df-t ax-r5
    comor2 anor1 3tr1 2an an1 ) ABCZBACZCVGVHDZVGOZVHDZPZVJVHPVHODZPZAAOZBOZDZP
    ZVGVHUAVNABDZVQPZAVPDZPZVOVPPZVOBPZDZADZPZVRVLWBVMWFVIVTVKWAABUBABUCEABUDEW
    GWBAPZWBWEPZDZVRWGWBAWEDZPWJWFWKWBWEAUEFAWBWEAWBVOWBVOVTWAVOVSVQAVSVSAABGZH
    IVQVOVOVPGHJAWAWAAAVPGHIJKLAWEVOWEVOWCWDVOVPMVOBMNKLUFQWJVRRDVRWHVRWIRWHVQA
    PZVRWHVTWAAPPZWMVTWAAUIWNVSWAPZWMPWMVSVQWAAUGWOWMWOAWMVSAWAABUHAVPUHUJAVQUK
    ULUMQQVQASQWIRRDZRWIWBWCPZWBWDPZDWPWCWBWDWCVTWAWCVSVQVSWCVSVOVPVSAWLKVSBABU
    NKJHWCVOVPVOVPUOZVOVPVBZNJWCAVPWCAWCVOWSILWTNJWCVOBWSWCBWCVPWTILJUFWQRWRRWQ
    VTWCPZWAPZRVTWAWCUPXBRWAPZRXARWAXAVSWCPZVQPZRVSVQWCUPXERVQPZRXDRVQXDVSVSOZP
    ZRWCXGVSXGWCVSWCABUQURUSFRXHVSUTUSQVAXFVQRPRRVQSVQTQQQVAXCWARPRRWASWATQQQWR
    VTWAWDPZPZRVTWAWDUIXJVTRPRXIRVTWDWAPWDWDOZPXIRWAXKWDABVCFWAWDSWDUTVDFVTTQQV
    EQRVFQVEVRVFQQQQ $.

  $( Lemma for unified disjunction.  (Contributed by NM, 23-Nov-1997.) $)
  ud4lem2 $p |- ( ( a v ( a ' ^ b ' ) ) ->4 a ) = ( a v b ) $=
    ( wn wa wo wi4 df-i4 wf ancom anabs ax-r2 oran con2 ran ax-r1 lan 2or ax-r5
    con3 wt anass dff an0 or0 lor anor2 comid comorr fh3r or32 oridm df-t ax-a2
    comcom2 2an an1 oml ) AACZBCDZEZAFUTADZUTCZADZEZVBAEZURDZEZABEZUTAGVGAURVHD
    ZEVHVDAVFVIVDAHEAVAAVCHVAAUTDAUTAIAUSJKVCURUSCZDZADZHVBVKAUTVKAUSLMNVLAVKDZ
    HVKAIVMAURDZVJDZHVOVMAURVJUAOVOVJVNDZHVNVJIVPVJHDZHVQVPHVNVJAUBPOVJUCKKKKKQ
    AUDKVFURVEDVIVEURIVEVHURVEVIAEZVHVBVIAUTVIUTAVHCZEZVICUSVSAUSVHVHVJABLOSUEV
    TVIVIVTCAVHUFOSKMRVRURAEZVHAEZDZVHAURVHAAAUGUNABUHUIWCVHTDZVHWCWBWADWDWAWBI
    WBVHWATWBAAEZBEVHABAUJWEABAUKRKTWATAUREWAAULAURUMKOUOKVHUPKKKPKQABUQKK $.

  $( Lemma for unified disjunction.  (Contributed by NM, 23-Nov-1997.) $)
  ud4lem3a $p |- ( ( a ->4 b ) ' ^ ( a v b ) ) = ( a ->4 b ) ' $=
    ( wn wo wa wi4 anass lea leror df2le2 lan ax-r2 ud4lem0c ran 3tr1 ) ACBCZDA
    PDEZAPEZBDZEZABDZEZTABFCZUAEUCUBQSUAEZETQSUAGUDSQSUARABAPHIJKLUCTUAABMZNUEO
    $.

  $( Lemma for unified disjunction.  (Contributed by NM, 23-Nov-1997.) $)
  ud4lem3b $p |- ( ( a ->4 b ) ' v ( a v b ) ) = ( a v b ) $=
    ( wi4 wn wo wa ud4lem0c comcom2 com2or com2an fh3r wt ax-a2 or4 ax-r1 ax-r2
    lor or1 2an an1 ax-r5 comor1 comor2 df-t lea leror df-le2 ancom ) ABCDZABEZ
    EADZBDZEZAULEZFZAULFZBEZFZUJEZUJUIURUJABGUAUSUOUJEZUQUJEZFZUJUJUOUQUJUMUNUJ
    UKULUJAABUBZHUJBABUCZHZIZUJAULVCVEIZJUJUPBUJAULVCVEJVDIKVBLUJFZUJUTLVAUJUTL
    LFZLUTUMUJEZUNUJEZFVIUJUMUNVFVGKVJLVKLVJUJUMEZLUMUJMVLAUKEZBULEZEZLABUKULNV
    OVMLEZLVPVOLVNVMBUDZQOVMRPPPVKUJUNEZLUNUJMVRAAEZVNEZLABAULNVTVSLEZLWAVTLVNV
    SVQQOVSRPPPSPLTPUQUJUPABAULUEUFUGSVHUJLFUJLUJUHUJTPPPP $.

  $( Lemma for unified disjunction.  (Contributed by NM, 23-Nov-1997.) $)
  ud4lem3 $p |- ( ( a ->4 b ) ->4 ( a v b ) ) = ( a v b ) $=
    ( wi4 wo wa wn df-i4 ud4lem3a lor comid comcom2 comor1 comor2 com2an com2or
    wf comcom wt ax-r2 ax-r1 bctr fh4r ancom ax-a2 ud4lem3b 2an an1 ran dff 2or
    df-t or0 ) ABCZABDZCUMUNEZUMFZUNEZDZUPUNDZUNFZEZDZUNUMUNGVBUNPDUNURUNVAPURU
    OUPDZUNUQUPUOABHIVCUMUPDZUNUPDZEZUNUMUPUNUMUMUMJKUMABEZAFZBEZDZVHBDZBFZEZDZ
    UNABGUNVNUNVJVMUNVGVIUNABABLZABMZNUNVHBUNAVOKZVPNOUNVKVLUNVHBVQVPOUNBVPKNOQ
    UAUBVFVEVDEZUNVDVEUCVRUNREUNVEUNVDRVEUSUNUNUPUDABUEZSRVDUMUKTUFUNUGSSSSVAUN
    UTEZPUSUNUTVSUHPVTUNUITSUJUNULSS $.

  $( Lemma for unified disjunction.  (Contributed by NM, 27-Nov-1997.) $)
  ud5lem1a $p |- ( ( a ->5 b ) ^ ( b ->5 a ) ) =
                 ( ( a ^ b ) v ( a ' ^ b ' ) ) $=
    ( wa wo lan coman2 comcom2 coman1 com2an comcom com2or wf anass ax-r1 ancom
    fh1r an0 ax-r2 2or or0 wi5 wn df-i5 2an ax-a2 fh2 comcom3 comcom5 dff anidm
    an12 lor ran ) ABUAZBAUAZCABCZAUBZBCZDZUQBUBZCZDZBACZUTACZDZUTUQCZDZCZUPVAD
    ZUNVBUOVGABUCBAUCUDVHVBVFVEDZCZVIVGVJVBVEVFUEEVKVBVFCZVBVECZDZVIVFVBVEVFUSV
    AVFUPURUPVFUPUTUQUPBABFGZUPAABHZGIJZURVFURUTUQURBUQBFGUQBHIJZKVFUQUTUTUQFZU
    TUQHZIZKVFVCVDVCVFVCUTUQVCBBAHZGZVCABAFZGZIJVDVFVDUTUQUTAHZVDAUTAFZGZIJKUFV
    NVAUPDVIVLVAVMUPVLUSVFCZVAVFCZDZVAVFUSVAVFUPURVFABVFAVFUQVSUGUHVFBVFUTVTUGU
    HZIVFUQBVSWLIKWAPWKLVADZVAWILWJVAWIUPVFCZURVFCZDZLVFUPURVQVRPWPLLDZLWNLWOLW
    NABVFCZCZLABVFMWSABUTCZUQCZCZLWRXAAXAWRBUTUQMNZEXBALCZLXALAXAUQWTCZLWTUQOXE
    UQLCZLWTLUQLWTBUINZEUQQZRRZEAQZRRRWOUQWRCZLUQBVFMXKUQXACZLWRXAUQXCEXLXFLXAL
    UQXIEXHRRRSLTZRRWJVAVACVAVFVAVAUTUQOEVAUJRSWMVALDVALVAUEVATRRRVMVBVCCZVBVDC
    ZDZUPVCVBVDVCUSVAVCUPURVCABWDWBIZVCUQBWEWBIZKZVCUQUTWEWCIZKVCUTAWCWDIUFXPUS
    VCCZUSVDCZDZUPXNYAXOYBXNYAVAVCCZDZYAVCUSVAXSXTPYEYALDZYAYDLYAYDUQUTVCCZCZLU
    QUTVCMYHXFLYGLUQYGBVDCZLYIYGBUTAUKNYIWTACZLYJYIBUTAMNYJAWTCZLWTAOYKXDLWTLAX
    GEXJRRRZREXHRRULYATZRRXOYBVAVDCZDZYBVDUSVAVDUPURVDABWGVDBVDUTWFUGUHZIVDUQBW
    HYPIZKVDUQUTWHWFIPYOYBLDYBYNLYBYNVDVACZLVAVDOYRUTAVACZCZLUTAVAMYTUTLCZLYSLU
    TYSAUQCZUTCZLUUCYSAUQUTMNUUCUTUUBCZLUUBUTOUUDUUALUUBLUTLUUBAUINZEUTQZRRREUU
    FRRRULYBTRRSYCYFUPYBLYAYBUPVDCZURVDCZDZLVDUPURUPVDUPUTAVOVPIJYQPUUIWQLUUGLU
    UHLUUGAYICZLABVDMUUJXDLYILAYLEXJRRUUHUQYICZLUQBVDMUUKXFLYILUQYLEXHRRSXMRRUL
    YFYAUPYMYAUPVCCZURVCCZDZUPVCUPURXQXRPUUNUPLDUPUULUPUUMLUULUPUPCUPVCUPUPBAOE
    UPUJRUUMVCURCZLURVCOUUOBAURCZCZLBAURMUUQBLCZLUUPLBUUPUURLUUPUUBBCZUURUUSUUP
    AUQBMNUUSLBCUURUUBLBUUEUMLBORRBQZREUUTRRRSUPTRRRRRRSVAUPUERRRR $.

  $( Lemma for unified disjunction.  (Contributed by NM, 27-Nov-1997.) $)
  ud5lem1b $p |- ( ( a ->5 b ) ' ^ ( b ->5 a ) ) = ( a ^ b ' ) $=
    ( wi5 wn wa wo ax-a2 ax-r2 2an coman2 coman1 com2or comcom7 com2an wf ax-r1
    fh2 dff comcom2 an32 ud5lem0c df-i5 anass oran con3 lan an0 df-a ran ler2an
    an0r lea leor letr lear leo df2le2 ancom 3tr1 2or or0r ) ABCDZBACZEADZBDZFZ
    AVEFZEZABFZEZVEVDEZBAEZVEAEZFZFZEZAVEEZVBVJVCVOABUAVCVNVKFVOBAUBVNVKGHIVPVJ
    VKEZVJVNEZFZVQVKVJVNVKVHVIVKVFVGVKVDVEVEVDJZVEVDKZLVKAVEVKAWAMZWBLNVKABWCVK
    BWBMZLNVKVLVMVKBAWDWCNVKVEAWBWCNLQVTOVQFZVQVROVSVQVRVHVIVKEZEZOVHVIVKUCWGVH
    OEOWFOVHWFBAFZWHDZEZOVIWHVKWIABGVKWHWHVKDBAUDPUEIOWJWHRPHUFVHUGHHVSVJVLEZVJ
    VMEZFZVQVLVJVMVLVHVIVLVFVGVLVDVEVLABAJZSVLBBAKZSZLVLAVEWNWPLNVLABWNWOLNVLVE
    AWPWNNQWMWEVQWKOWLVQWKVHVLEZVIEZOVHVIVLTWROVIEOWQOVIWQVFVLEZVGEZOVFVGVLTWTO
    VGEOWSOVGWSVEVDFZXADZEZOVFXAVLXBVDVEGBAUHIOXCXARPHUIVGUKHHUIVIUKHHVMVJEVMWL
    VQVMVJVMVHVIVMVEVHVEAULVEVFVGVEVDUMVEAUMUJUNVMAVIVEAUOABUPUNUJUQVJVMURAVEUR
    USUTVQVAZHHUTXDHHH $.

  $( Lemma for unified disjunction.  (Contributed by NM, 26-Nov-1997.) $)
  ud5lem1c $p |- ( ( a ->5 b ) ' ^ ( b ->5 a ) ' ) =
                 ( ( ( a v b ) ^ ( a v b ' ) ) ^
                 ( ( a ' v b ) ^ ( a ' v b ' ) ) ) $=
    ( wi5 wn wa wo ud5lem0c ax-a2 2an ax-r2 an4 ancom anidm ran anass ax-r1 ) A
    BCDZBACDZEADZBDZFZATFZEZABFZEZUASBFZEZUDEZEZUDUBEUFUAEZEZQUERUHABGRTSFZBSFZ
    EZBAFZEUHBAGUNUGUOUDULUAUMUFTSHBSHIBAHIJIUIUCUGEZUDUDEZEZUKUCUDUGUDKURUQUPE
    ZUKUPUQLUSUDUBUJEZEZUKUQUDUPUTUDMUPUAUAEZUBUFEZEZUTUAUBUAUFKVDVCUAEZUTVDUAV
    CEVEVBUAVCUAMNUAVCLJUBUFUAOJJIUKVAUDUBUJOPJJJJ $.

  $( Lemma for unified disjunction.  (Contributed by NM, 27-Nov-1997.) $)
  ud5lem1 $p |- ( ( a ->5 b ) ->5 ( b ->5 a ) ) =
              ( a v b ' ) $=
    ( wa wn wo coman1 coman2 com2or comcom2 com2an comcom comcom7 comor1 comor2
    wi5 fh4 wt lor ax-r1 ax-r2 df-i5 ud5lem1a ud5lem1b ud5lem1c or32 ax-a3 oran
    2or df-t or1 ax-r5 or1r lea leo letr lear leor lel2or df-le2 2an an1r anor1
    con3 df-a an1 ) ABOZBAOZOVFVGCZVFDZVGCZEZVIVGDCZEZABDZEZVFVGUAVMABCZADZVNCZ
    EZAVNCZEZABEZVOCZVQBEZVQVNEZCZCZEZVOVKWAVLWGVHVSVJVTABUBABUCUHABUDUHWHWAWCE
    ZWAWFEZCZVOWCWAWFWCVSVTWCVPVRVPWCVPWBVOVPABABFZABGZHVPAVNWLVPBWMIHJKVRWCVRW
    BVOVRABVRAVQVNFLZVRBVQVNGZLHVRAVNWNWOHJKHVTWCVTWBVOVTABAVNFZVTBAVNGZLHVTAVN
    WPWQHJKHWCWDWEWDWCWDWBVOWDABWDAVQBMZLZVQBNZHWDAVNWSWDBWTIZHJKWEWCWEWBVOWEAB
    WEAVQVNMLZWEBVQVNNZLHWEAVNXBXCHJKJPWKVOQCVOWIVOWJQWIWAWBEZWAVOEZCZVOWBWAVOW
    BVSVTWBVPVRWBABABMZABNZJWBVQVNWBAXGIWBBXHIZJHWBAVNXGXIJHWBAVNXGXIHPXFQVOCVO
    XDQXEVOXDVSWBEZVTEZQVSVTWBUEXKQVTEZQXJQVTXJVPVRWBEZEZQVPVRWBUFXNVPQEQXMQVPX
    MVRVRDZEZQWBXOVRABUGRQXPVRUISTRVPUJTTUKVTULZTTWAVOVSVOVTVPVOVRVPAVOABUMAVNU
    NZUOVRVNVOVQVNUPVNAUQUOURVTAVOAVNUMXRUOURUSUTVOVATTWJWAWDEZWAWEEZCZQWDWAWEW
    DVSVTWDVPVRWDABWSWTJWDVQVNWRXAJHWDAVNWSXAJHWDVQVNWRXAHPYAQQCQXSQXTQXSVSVTWD
    EZEZQVSVTWDUFYCVSQEQYBQVSYBVTVTDZEZQWDYDVTWDVTVTWDDABVBSVCRQYEVTUISTRVSUJTT
    XTVSWEEZVTEZQVSVTWEUEYGXLQYFQVTYFVPWEEZVREZQVPVRWEUEYIQVREQYHQVRYHVPVPDZEZQ
    WEYJVPWEVPVPWEDABVDSVCRQYKVPUISTUKVRULTTUKXQTTUTQVETTUTVOVETTTT $.

  $( Lemma for unified disjunction.  (Contributed by NM, 10-Apr-2012.) $)
  ud5lem2 $p |- ( ( a v b ' ) ->5 a ) = ( a v ( a ' ^ b ) ) $=
    ( wn wo wi5 wa df-i5 ax-a3 ancom anabs ax-r2 ax-a2 wf anor2 ax-r1 ran anidm
    an32 dff 2or lan an0 or0 ) ABCZDZAEUEAFZUECZAFZDUGACZFZDZAUIBFZDZUEAGUKUFUH
    UJDZDUMUFUHUJHUFAUNULUFAUEFAUEAIAUDJKUNUJUHDZULUHUJLUOULMDULUJULUHMUJULUIFZ
    ULUGULUIULUGABNOZPUPUIUIFZBFULUIBUIRURUIBUIQPKKUHULAFZMUGULAUQPUSUIAFZBFZMU
    IBARVABUTFZMUTBIVBBMFMUTMBUTAUIFZMUIAIMVCASOKUABUBKKKKTULUCKKTKK $.

  $( Lemma for unified disjunction.  (Contributed by NM, 27-Nov-1997.) $)
  ud5lem3a $p |- ( ( a ->5 b ) ^ ( a v ( a ' ^ b ) ) ) =
                 ( ( a ^ b ) v ( a ' ^ b ) ) $=
    ( wn wa wo ran comanr1 comcom6 com2or fh1r ax-r2 ancom anass ax-r1 dff an0r
    wf 2or or0 com2an wi5 df-i5 fh2 an32 anidm coman1 comcom7 comcom2 ax-a2 lan
    coman2 anabs an4 an0 lor ) ABUAZAACZBDZEZDABDZUREZUQBCZDZEZUSDZVAUPVDUSABUB
    FVEVDADZVDURDZEZVAAVDURAVAVCAUTURABGZAURUQBGHZIZAVCUQVBGHZIVJUCVHUTVAURDZVC
    URDZEZEVAVFUTVGVOVFVAADZVCADZEZUTAVAVCVKVLJVRUTQEZUTVPUTVQQVPUTADZURADZEZUT
    AUTURVIVJJWBVSUTVTUTWAQVTAADZBDUTABAUDWCABAUEFKWAAURDZQURALWDAUQDZBDZQWFWDA
    UQBMNWFQBDQWEQBQWEAONZFBPKKKRUTSZKKVQAVCDZQVCALWIWEVBDZQWJWIAUQVBMNWJQVBDQW
    EQVBWGFVBPKKKRWHKKURVAVCURUTURURABURAUQBUFZUGUQBUKZTURUQBWKWLTIURUQVBWKURBW
    LUHTJRVOURUTVOURQEURVMURVNQVMURVADZURVAURLWMURURUTEZDURVAWNURUTURUIUJURUTUL
    KKVNUQUQDZVBBDZDZQUQVBUQBUMWQWOQDQWPQWOWPBVBDZQVBBLQWRBONKUJWOUNKKRURSKUOKK
    K $.

  $( Lemma for unified disjunction.  (Contributed by NM, 26-Nov-1997.) $)
  ud5lem3b $p |- ( ( a ->5 b ) ' ^ ( a v ( a ' ^ b ) ) ) =
                ( a ^ ( a ' v b ' ) ) $=
    ( wi5 wn wa wo ud5lem0c ran comorr comcom6 com2an comanr1 anass ancom anabs
    fh2 wf ax-r2 lan an32 anor2 dff ax-r1 an0 an0r 2or or0 ) ABCDZAADZBEZFZEUIB
    DZFZAULFZEZABFZEZUKEZAUMEZUHUQUKABGHURUQAEZUQUJEZFZUSAUQUJAUOUPAUMUNAUMUIUL
    IJAULIKABIKAUJUIBLJPVBUSQFUSUTUSVAQUTUOUPAEZEZUSUOUPAMVDUOAEZUSVCAUOVCAUPEA
    UPANABORSVEUMUNAEZEZUSUMUNAMVGUMAEUSVFAUMVFAUNEAUNANAULORSUMANRRRRVAUOUJEZU
    PEZQUOUPUJTVIQUPEQVHQUPVHUMUNUJEZEZQUMUNUJMVKUMQEQVJQUMVJUNUNDZEZQUJVLUNABU
    ASQVMUNUBUCRSUMUDRRHUPUERRUFUSUGRRR $.

  $( Lemma for unified disjunction.  (Contributed by NM, 26-Nov-1997.) $)
  ud5lem3c $p |- ( ( a ->5 b ) ' ^ ( a v ( a ' ^ b ) ) ' ) =
                 ( ( ( a v b ) ^ ( a v b ' ) ) ^ a ' ) $=
    ( wi5 wn wa wo ud5lem0c oran con2 anor2 lan ax-r2 2an an4 ancom anabs anidm
    an32 ran anass ax-r1 ) ABCDZAADZBEZFZDZEUCBDZFZAUGFZEZABFZEZUCUIEZEZUKUIEUC
    EZUBULUFUMABGUFUCUDDZEZUMUEUQAUDHIUPUIUCUDUIABJIKLMUNUJUMEZUKEZUOUJUKUMRUSU
    KUIUCEZEZUOUSUTUKEVAURUTUKURUHUCEZUIUIEZEZUTUHUIUCUINVDUMUTVBUCVCUIVBUCUHEU
    CUHUCOUCUGPLUIQMUCUIOLLSUTUKOLUOVAUKUIUCTUALLL $.

  $( Lemma for unified disjunction.  (Contributed by NM, 26-Nov-1997.) $)
  ud5lem3 $p |- ( ( a ->5 b ) ->5 ( a v ( a ' ^ b ) ) ) = ( a v b ) $=
    ( wi5 wn wa wo 2or fh4 ax-a2 orabs ax-r2 ax-r1 con3 lor df-t 2an an1 com2or
    wt comcom2 df-i5 ud5lem3a ud5lem3b ud5lem3c or4 comanr1 comorr comcom6 df-a
    ax-a3 coman1 comcom7 coman2 com2an fh3 comor1 comor2 fh3r oridm ancom anabs
    or12 anor2 oml ) ABCZAADZBEZFZCVEVHEZVEDZVHEZFZVJVHDEZFZABFZVEVHUAVNABEZVGF
    ZAVFBDZFZEZFZVOAVRFZEZVFEZFZVOVLWAVMWDVIVQVKVTABUBABUCGABUDGWEVQVTWDFFZVOVQ
    VTWDUJWFVPVTFZVGWDFZFZVOVPVGVTWDUEWIAVFVOEZFVOWGAWHWJWGVPAFZVPVSFZEZAAVPVSA
    BUFAVSVFVRUGUHHWMASEAWKAWLSWKAVPFAVPAIABJKWLVPVPDZFZSVSWNVPVSVPVPVSDABUILMN
    SWOVPOLKPAQKKWHVGWCFZVGVFFZEZWJVGWCVFVGVOWBVGABVGAVFBUKZULZVFBUMZRVGAVRWTVG
    BXATRUNWSUOWRVOVFEWJWPVOWQVFWPVGVOFZVGWBFZEZVOVOVGWBVOVFBVOAABUPZTZABUQZUNV
    OAVRXEVOBXGTRHXDVOSEVOXBVOXCSXBVFVOFZBVOFZEZVOVOVFBXFXGURXJVOVFFZVOEZVOXHXK
    XIVOVFVOIXIABBFZFVOBABVBXMBABUSNKPXLVOXKEVOXKVOUTVOVFVAKKKXCVGVGDZFZSWBXNVG
    WBVGVGWBDABVCLMNSXOVGOLKPVOQKKWQVFVGFVFVGVFIVFBJKPVOVFUTKKGABVDKKKKK $.

  $( Unified disjunction for Sasaki implication.  (Contributed by NM,
     23-Nov-1997.) $)
  ud1 $p |- ( a v b ) =
            ( ( a ->1 b ) ->1 ( ( ( a ->1 b ) ->1 ( b ->1 a ) ) ->1 a ) ) $=
    ( wi1 wo wn wa ud1lem1 ud1lem0b ud1lem2 ax-r2 ud1lem0a ud1lem3 ax-r1 ) ABCZ
    NBACCZACZCZABDZQNRCRPRNPAAEBEFDZACROSAABGHABIJKABLJM $.

  $( Unified disjunction for Dishkant implication.  (Contributed by NM,
     23-Nov-1997.) $)
  ud2 $p |- ( a v b ) =
            ( ( a ->2 b ) ->2 ( ( ( a ->2 b ) ->2 ( b ->2 a ) ) ->2 a ) ) $=
    ( wi2 wo wn wa ud2lem1 ud2lem0b ud2lem2 ax-r2 ud2lem0a ud2lem3 ax-r1 ) ABCZ
    NBACCZACZCZABDZQNRCRPRNPAAEBEFDZACROSAABGHABIJKABLJM $.

  $( Unified disjunction for Kalmbach implication.  (Contributed by NM,
     23-Nov-1997.) $)
  ud3 $p |- ( a v b ) =
            ( ( a ->3 b ) ->3 ( ( ( a ->3 b ) ->3 ( b ->3 a ) ) ->3 a ) ) $=
    ( wi3 wo wn wa ud3lem1 ud3lem0b ud3lem2 ax-r2 ud3lem0a ud3lem3 ax-r1 ) ABCZ
    NBACCZACZCZABDZQNRCRPRNPAAEBEFDZACROSAABGHABIJKABLJM $.

  $( Unified disjunction for non-tollens implication.  (Contributed by NM,
     23-Nov-1997.) $)
  ud4 $p |- ( a v b ) =
            ( ( a ->4 b ) ->4 ( ( ( a ->4 b ) ->4 ( b ->4 a ) ) ->4 a ) ) $=
    ( wi4 wo wn wa ud4lem1 ud4lem0b ud4lem2 ax-r2 ud4lem0a ud4lem3 ax-r1 ) ABCZ
    NBACCZACZCZABDZQNRCRPRNPAAEBEFDZACROSAABGHABIJKABLJM $.

  $( Unified disjunction for relevance implication.  (Contributed by NM,
     23-Nov-1997.) $)
  ud5 $p |- ( a v b ) =
            ( ( a ->5 b ) ->5 ( ( ( a ->5 b ) ->5 ( b ->5 a ) ) ->5 a ) ) $=
    ( wi5 wo wn wa ud5lem1 ud5lem0b ud5lem2 ax-r2 ud5lem0a ud5lem3 ax-r1 ) ABCZ
    NBACCZACZCZABDZQNAAEBFDZCRPSNPABEDZACSOTAABGHABIJKABLJM $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Lemmas for unified implication study
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Lemma for Sasaki implication study.  Equation 4.10 of [MegPav2000] p. 23.
     This is the second part of the equation.  (Contributed by NM,
     14-Dec-1997.) $)
  u1lemaa $p |- ( ( a ->1 b ) ^ a ) = ( a ^ b ) $=
    ( wi1 wa wn wo df-i1 ran comid comcom2 comanr1 fh1r ax-a2 anidm ax-r2 ancom
    wf an32 dff ax-r1 2or or0 ) ABCZADAEZABDZFZADZUEUCUFAABGHUGUDADZUEADZFZUEAU
    DUEAAAIJABKLUJUEQFZUEUJUIUHFUKUHUIMUIUEUHQUIAADZBDUEABARULABANHOUHAUDDZQUDA
    PQUMASTOUAOUEUBOOO $.

  $( Lemma for Dishkant implication study.  (Contributed by NM,
     14-Dec-1997.) $)
  u2lemaa $p |- ( ( a ->2 b ) ^ a ) = ( a ^ b ) $=
    ( wi2 wa wn wo df-i2 ran ax-a2 coman1 comcom7 coman2 fh2r ancom anass ax-r1
    wf dff lan ax-r2 an0 2or or0 ) ABCZADBAEZBEZDZFZADZABDZUDUHAABGHUIUGBFZADZU
    JUHUKABUGIHULUGADZBADZFZUJUGABUGAUEUFJKUGBUEUFLKMUOUNUMFZUJUMUNIUPUJQFUJUNU
    JUMQBANUMAUGDZQUGANUQAUEDZUFDZQUSUQAUEUFOPUSUFURDZQURUFNUTUFQDQURQUFQURARPS
    UFUATTTTUBUJUCTTTTT $.

  $( Lemma for Kalmbach implication study.  (Contributed by NM,
     14-Dec-1997.) $)
  u3lemaa $p |- ( ( a ->3 b ) ^ a ) = ( a ^ ( a ' v b ) ) $=
    ( wi3 wa wn wo df-i3 ran comanr1 comcom6 wf ancom anass ax-r1 lan an0 ax-r2
    fh1r 2or or0 com2or comid comorr com2an dff an32 anidm ax-a2 ) ABCZADAEZBDZ
    UJBEZDZFZAUJBFZDZFZADZUPUIUQAABGHURUNADZUPADZFZUPAUNUPAUKUMAUKUJBIJZAUMUJUL
    IJZUAAAUOAUBAUOUJBUCJUDRVAKUPFZUPUSKUTUPUSUKADZUMADZFZKAUKUMVBVCRVGKKFKVEKV
    FKVEAUKDZKUKALVHAUJDZBDZKVJVHAUJBMNVJBVIDZKVIBLVKBKDKVIKBKVIAUENZOBPQQQQVFA
    UMDZKUMALVMVIULDZKVNVMAUJULMNVNULVIDZKVIULLVOULKDKVIKULVLOULPQQQQSKTQQUTAAD
    ZUODUPAUOAUFVPAUOAUGHQSVDUPKFUPKUPUHUPTQQQQ $.

  $( Lemma for non-tollens implication study.  (Contributed by NM,
     14-Dec-1997.) $)
  u4lemaa $p |- ( ( a ->4 b ) ^ a ) = ( a ^ b ) $=
    ( wi4 wa wn wo df-i4 ran comanr1 com2or comcom comanr2 wf ax-r2 ancom anass
    ax-r1 dff lan 2or comcom6 comcom3 comcom2 com2an fh2r fh1r an32 anidm anor1
    an0 or0 ) ABCZADABDZAEZBDZFZUNBFZBEZDZFZADZUMULUTAABGHVAUPADZUSADZFZUMUPAUS
    AUPAUMUOABIZAUOUNBIZUAZJKUPUQURUPUNBUNUPUNUMUOAUMVEUBVFJKBUPBUMUOABLUNBLJKZ
    JUPBVHUCUDUEVDUMMFZUMVBUMVCMVBUMADZUOADZFZUMAUMUOVEVGUFVLVIUMVJUMVKMVJAADZB
    DUMABAUGVMABAUHHNVKAUODZMUOAOVNAUNDZBDZMVPVNAUNBPQVPBVODZMVOBOVQBMDMVOMBMVO
    ARQSBUJNNNNTUMUKZNNVCUQURADZDZMUQURAPVTUQUQEZDZMVSWAUQVSAURDWAURAOABUINSMWB
    UQRQNNTVRNNN $.

  $( Lemma for relevance implication study.  (Contributed by NM,
     14-Dec-1997.) $)
  u5lemaa $p |- ( ( a ->5 b ) ^ a ) = ( a ^ b ) $=
    ( wi5 wa wn wo df-i5 ran comanr1 comcom6 fh1r wf an32 ax-r2 ancom ax-r1 lan
    an0 2or anass com2or anidm dff or0 fh4 ax-a2 orabs fh1 ) ABCZADABDZAEZBDZFZ
    UKBEZDZFZADZUJUIUPAABGHUQUMADZUOADZFZUJAUMUOAUJULABIZAULUKBIJZUAAUOUKUNIJZK
    UTUJAUODZFZUJURUJUSVDURUJADZULADZFZUJAUJULVAVBKVHUJLFZUJVFUJVGLVFAADZBDZUJA
    BAMVJABAUBHZNVGUKADZBDZLUKBAMVNBVMDZLVMBOVOBLDLVMLBVMAUKDZLVPVMAUKOPLVPAUCZ
    PNQBRNNNSUJUDZNNUOAOSVEUJAFZUJUOFZDZUJAUJUOVAVCUEWAAVTDZUJVSAVTVSAUJFAUJAUF
    ABUGNHWBAUJDZVDFZUJAUJUOVAVCUHWDVIUJWCUJVDLWCVKUJVKWCAABTPVLNVDVPUNDZLWEVDA
    UKUNTPWEUNVPDZLVPUNOWFUNLDZLWGWFLVPUNVQQPUNRNNNSVRNNNNNNN $.

  $( Lemma for Sasaki implication study.  (Contributed by NM, 14-Dec-1997.) $)
  u1lemana $p |- ( ( a ->1 b ) ^ a ' ) = a ' $=
    ( wi1 wn wa wo df-i1 ran ancom anabs ax-r2 ) ABCZADZEMABEZFZMEZMLOMABGHPMOE
    MOMIMNJKK $.

  $( Lemma for Dishkant implication study.  (Contributed by NM,
     14-Dec-1997.) $)
  u2lemana $p |- ( ( a ->2 b ) ^ a ' ) =
               ( ( a ' ^ b ) v ( a ' ^ b ' ) ) $=
    ( wi2 wn wa wo df-i2 ran ax-a2 coman1 coman2 comcom7 fh2r anidm ax-r2 ancom
    an32 2or ) ABCZADZEBTBDZEZFZTEZTBEZUBFZSUCTABGHUDUBBFZTEZUFUCUGTBUBIHUHUBTE
    ZBTEZFZUFUBTBTUAJUBBTUAKLMUKUBUEFUFUIUBUJUEUITTEZUAEUBTUATQULTUATNHOBTPRUBU
    EIOOOO $.

  $( Lemma for Kalmbach implication study.  (Contributed by NM,
     14-Dec-1997.) $)
  u3lemana $p |- ( ( a ->3 b ) ^ a ' ) =
               ( ( a ' ^ b ) v ( a ' ^ b ' ) ) $=
    ( wi3 wn wa wo df-i3 ran comanr1 com2or comid comcom3 comorr com2an fh1r wf
    lea lel2or df2le2 ax-r2 an32 ancom dff ax-r1 lan an0 2or or0 ) ABCZADZEUJBE
    ZUJBDZEZFZAUJBFZEZFZUJEZUNUIUQUJABGHURUNUJEZUPUJEZFZUNUJUNUPUJUKUMUJBIUJULI
    JUJAUOAAAKLUJBMNOVAUNPFUNUSUNUTPUNUJUKUJUMUJBQUJULQRSUTAUJEZUOEZPAUOUJUAVCU
    OVBEZPVBUOUBVDUOPEPVBPUOPVBAUCUDUEUOUFTTTUGUNUHTTT $.

  $( Lemma for non-tollens implication study.  (Contributed by NM,
     14-Dec-1997.) $)
  u4lemana $p |- ( ( a ->4 b ) ^ a ' ) =
               ( ( a ' ^ b ) v ( a ' ^ b ' ) ) $=
    ( wi4 wn wa wo df-i4 comanr1 comcom3 com2or comcom comor1 com2an comanr2 wf
    ran an32 ancom ax-r2 2or comcom7 comor2 fh2r fh1r dff ax-r1 lan anidm ax-a2
    an0 or0 leo df2le2 id ) ABCZADZEABEZUPBEZFZUPBFZBDZEZFZUPEZURUPVAEZFZUOVCUP
    ABGPVDUSUPEZVBUPEZFZVFUSUPVBUPUSUPUQURAUQABHIZUPBHZJKUSUTVAUTUSUTUQURUTABUT
    AUPBLZUAUPBUBZMUTUPBVLVMMJKVAUSVAUQURBUQABNIBURUPBNIJKMUCVIVFVFVGURVHVEVGUQ
    UPEZURUPEZFZURUPUQURVJVKUDVPOURFZURVNOVOURVNAUPEZBEZOABUPQVSBVREZOVRBRVTBOE
    OVROBOVRAUEUFUGBUJSSSVOUPUPEZBEURUPBUPQWAUPBUPUHPSTVQUROFUROURUIURUKSSSVHUT
    UPEZVAEVEUTVAUPQWBUPVAWBUPUTEUPUTUPRUPUTUPBULUMSPSTVFUNSSS $.

  $( Lemma for relevance implication study.  (Contributed by NM,
     14-Dec-1997.) $)
  u5lemana $p |- ( ( a ->5 b ) ^ a ' ) =
               ( ( a ' ^ b ) v ( a ' ^ b ' ) ) $=
    ( wi5 wn wa wo df-i5 ran comanr1 comcom3 com2or fh1r ax-a2 an32 anidm ax-r2
    wf ancom dff 2or lan ax-r1 an0 or0 ) ABCZADZEABEZUFBEZFZUFBDZEZFZUFEZUHUKFZ
    UEULUFABGHUMUIUFEZUKUFEZFUNUFUIUKUFUGUHAUGABIJZUFBIZKUFUJILUOUHUPUKUOUGUFEZ
    UHUFEZFZUHUFUGUHUQURLVAUTUSFZUHUSUTMVBUHQFUHUTUHUSQUTUFUFEZBEUHUFBUFNVCUFBU
    FOZHPUSAUFEZBEZQABUFNVFBVEEZQVEBRVGBQEZQVHVGQVEBASUAUBBUCPPPTUHUDPPPUPVCUJE
    UKUFUJUFNVCUFUJVDHPTPP $.

  $( Lemma for Sasaki implication study.  Equation 4.10 of [MegPav2000] p. 23.
     This is the second part of the equation.  (Contributed by NM,
     14-Dec-1997.) $)
  u1lemab $p |- ( ( a ->1 b ) ^ b ) = ( ( a ^ b ) v ( a ' ^ b ) ) $=
    ( wi1 wa wn wo df-i1 ran ax-a2 coman2 coman1 comcom2 fh2r ax-r2 anass anidm
    lan ax-r5 ) ABCZBDAEZABDZFZBDZUATBDZFZSUBBABGHUCUABDZUDFZUEUCUATFZBDUGUBUHB
    TUAIHUABTABJUAAABKLMNUFUAUDUFABBDZDUAABBOUIBABPQNRNN $.

  $( Lemma for Dishkant implication study.  (Contributed by NM,
     14-Dec-1997.) $)
  u2lemab $p |- ( ( a ->2 b ) ^ b ) = b $=
    ( wi2 wa wn wo df-i2 ran ancom anabs ax-r2 ) ABCZBDBAEBEDZFZBDZBLNBABGHOBND
    BNBIBMJKK $.

  $( Lemma for Kalmbach implication study.  (Contributed by NM,
     14-Dec-1997.) $)
  u3lemab $p |- ( ( a ->3 b ) ^ b ) = ( ( a ^ b ) v ( a ' ^ b ) ) $=
    ( wi3 wa wn wo df-i3 comanr2 com2or comcom coman1 comcom7 coman2 com2an lan
    wf anass ax-r2 2or ax-a2 ran comcom6 fh2r fh1r anidm an32 dff ax-r1 an0 or0
    ancom anabs ) ABCZBDAEZBDZUNBEZDZFZAUNBFZDZFZBDZABDZUOFZUMVABABGUAVBURBDZUT
    BDZFZVDURBUTBURBUOUQUNBHZBUQUNUPHUBZIJUTURUTUOUQUOUTUOAUSUOAUNBKZLUOUNBVJUN
    BMINJUQUTUQAUSUQAUNUPKZLUQUNBVKUQBUNUPMLINJIJUCVGUOVCFVDVEUOVFVCVEUOBDZUQBD
    ZFZUOBUOUQVHVIUDVNUOPFUOVLUOVMPVLUNBBDZDUOUNBBQVOBUNBUEORVMUOUPDZPUNUPBUFVP
    UNBUPDZDZPUNBUPQVRUNPDPVQPUNPVQBUGUHOUNUIRRRSUOUJRRVFAUSBDZDVCAUSBQVSBAVSBU
    SDZBUSBUKVTBBUNFZDBUSWABUNBTOBUNULRRORSUOVCTRRR $.

  $( Lemma for non-tollens implication study.  (Contributed by NM,
     14-Dec-1997.) $)
  u4lemab $p |- ( ( a ->4 b ) ^ b ) = ( ( a ^ b ) v ( a ' ^ b ) ) $=
    ( wi4 wa wn wo df-i4 comanr2 com2or comcom6 fh1r wf lear lel2or df2le2 an32
    ran anass dff ax-r2 lan ax-r1 an0 2or or0 ) ABCZBDABDZAEZBDZFZUHBFZBEZDZFZB
    DZUJUFUNBABGQUOUJBDZUMBDZFZUJBUJUMBUGUIABHUHBHIBUMUKULHJKURUJLFUJUPUJUQLUJB
    UGBUIABMUHBMNOUQUKBDULDZLUKULBPUSUKBULDZDZLUKBULRVAUKLDZLVBVALUTUKBSUAUBUKU
    CTTTUDUJUETTT $.

  $( Lemma for relevance implication study.  (Contributed by NM,
     14-Dec-1997.) $)
  u5lemab $p |- ( ( a ->5 b ) ^ b ) = ( ( a ^ b ) v ( a ' ^ b ) ) $=
    ( wi5 wa wn wo df-i5 comanr2 com2or comcom6 fh1r wf lear lel2or df2le2 an32
    ran anass dff ax-r2 lan ax-r1 an0 2or or0 ) ABCZBDABDZAEZBDZFZUHBEZDZFZBDZU
    JUFUMBABGQUNUJBDZULBDZFZUJBUJULBUGUIABHUHBHIBULUHUKHJKUQUJLFUJUOUJUPLUJBUGB
    UIABMUHBMNOUPUIUKDZLUHUKBPURUHBUKDZDZLUHBUKRUTUHLDZLVAUTLUSUHBSUAUBUHUCTTTU
    DUJUETTT $.

  $( Lemma for Sasaki implication study.  (Contributed by NM, 14-Dec-1997.) $)
  u1lemanb $p |- ( ( a ->1 b ) ^ b ' ) = ( a ' ^ b ' ) $=
    ( wi1 wn wa wo df-i1 ran ax-a2 coman2 comcom2 coman1 wf anass dff lan ax-r1
    fh2r an0 ax-r2 lor or0 ) ABCZBDZEADZABEZFZUDEZUEUDEZUCUGUDABGHUHUFUEFZUDEZU
    IUGUJUDUEUFIHUKUFUDEZUIFZUIUFUDUEUFBABJKUFAABLKRUMUIULFZUIULUIIUNUIMFUIULMU
    IULABUDEZEZMABUDNUPAMEZMUQUPMUOABOPQASTTUAUIUBTTTTT $.

  $( Lemma for Dishkant implication study.  (Contributed by NM,
     14-Dec-1997.) $)
  u2lemanb $p |- ( ( a ->2 b ) ^ b ' ) = ( a ' ^ b ' ) $=
    ( wi2 wn wa wo df-i2 ran comid comcom3 comanr2 fh1r ax-a2 anass anidm ax-r2
    wf lan dff ax-r1 2or or0 ) ABCZBDZEBADZUDEZFZUDEZUFUCUGUDABGHUHBUDEZUFUDEZF
    ZUFUDBUFBBBIJUEUDKLUKUJUIFZUFUIUJMULUFQFUFUJUFUIQUJUEUDUDEZEUFUEUDUDNUMUDUE
    UDORPQUIBSTUAUFUBPPPP $.

  $( Lemma for Kalmbach implication study.  (Contributed by NM,
     14-Dec-1997.) $)
  u3lemanb $p |- ( ( a ->3 b ) ^ b ' ) = ( a ' ^ b ' ) $=
    ( wn wa wo comanr2 com2or comcom coman1 comcom7 coman2 com2an fh2r wf anass
    lan ax-r2 dff ax-r1 2or wi3 df-i3 ran comcom3 comcom2 ax-a2 anidm an0 ancom
    or0 an32 anor1 ) ABUAZBCZDACZBDZUOUNDZEZAUOBEZDZEZUNDZUQUMVAUNABUBUCVBURUND
    ZUTUNDZEZUQURUNUTUNURUNUPUQBUPUOBFUDUOUNFGHUTURUTUPUQUPUTUPAUSUPAUOBIZJUPUO
    BVFUOBKZGLHUQUTUQAUSUQAUOUNIZJUQUOBVHUQBUOUNKJGLHGHMVEUQNEZUQVCUQVDNVCUPUND
    ZUQUNDZEZUQUPUNUQUPBVGUEZUPUOUNVFVMLMVLVKVJEZUQVJVKUFVNVIUQVKUQVJNVKUOUNUND
    ZDUQUOUNUNOVOUNUOUNUGPQVJUOBUNDZDZNUOBUNOVQUONDZNVRVQNVPUOBRPSUOUHQQTUQUJZQ
    QQVDAUNDZUSDZNAUSUNUKWAUSVTDZNVTUSUIWBUSUSCZDZNVTWCUSABULPNWDUSRSQQQTVSQQQ
    $.

  $( Lemma for non-tollens implication study.  (Contributed by NM,
     14-Dec-1997.) $)
  u4lemanb $p |- ( ( a ->4 b ) ^ b ' ) = ( ( a ' v b ) ^ b ' ) $=
    ( wi4 wn wa wo df-i4 ran comanr2 comcom3 com2or fh1r wf anass lan ax-r2 an0
    ax-r1 2or or0 comorr2 comid com2an ax-a2 anidm dff ) ABCZBDZEABEZADZBEZFZUJ
    BFZUHEZFZUHEZUNUGUOUHABGHUPULUHEZUNUHEZFZUNUHULUNUHUIUKBUIABIJZBUKUJBIJZKUH
    UMUHBUMUJBUAJUHUBUCLUSURUQFZUNUQURUDVBUNMFUNURUNUQMURUMUHUHEZEUNUMUHUHNVCUH
    UMUHUEOPUQUIUHEZUKUHEZFZMUHUIUKUTVALVFMMFMVDMVEMVDABUHEZEZMABUHNVHAMEZMVIVH
    MVGABUFZORAQPPVEUJVGEZMUJBUHNVKUJMEZMVLVKMVGUJVJORUJQPPSMTPPSUNTPPPP $.

  $( Lemma for relevance implication study.  (Contributed by NM,
     14-Dec-1997.) $)
  u5lemanb $p |- ( ( a ->5 b ) ^ b ' ) = ( a ' ^ b ' ) $=
    ( wi5 wn wa wo df-i5 ran comanr2 comcom3 com2or fh1r wf anass lan ax-r2 an0
    ax-r1 2or or0 ax-a2 anidm dff ) ABCZBDZEABEZADZBEZFZUGUEEZFZUEEZUJUDUKUEABG
    HULUIUEEZUJUEEZFZUJUEUIUJUEUFUHBUFABIJZBUHUGBIJZKUGUEILUOUNUMFZUJUMUNUAURUJ
    MFUJUNUJUMMUNUGUEUEEZEUJUGUEUENUSUEUGUEUBOPUMUFUEEZUHUEEZFZMUEUFUHUPUQLVBMM
    FMUTMVAMUTABUEEZEZMABUENVDAMEZMVEVDMVCABUCZORAQPPVAUGVCEZMUGBUENVGUGMEZMVHV
    GMVCUGVFORUGQPPSMTPPSUJTPPPP $.

  $( Lemma for Sasaki implication study.  (Contributed by NM, 14-Dec-1997.) $)
  u1lemoa $p |- ( ( a ->1 b ) v a ) = 1 $=
    ( wi1 wo wn wa wt df-i1 ax-r5 ax-a2 ax-a3 ax-r1 df-t lor or1 ax-r2 ) ABCZAD
    AEZABFZDZADZGQTAABHIUAATDZGTAJUBARDZSDZGUDUBARSKLUDSUCDZGUCSJUESGDZGUFUEGUC
    SAMNLSOPPPPP $.

  $( Lemma for Dishkant implication study.  (Contributed by NM,
     14-Dec-1997.) $)
  u2lemoa $p |- ( ( a ->2 b ) v a ) = 1 $=
    ( wi2 wo wn wa wt df-i2 ax-r5 ax-a2 ax-a3 ax-r1 oran lor df-t ax-r2 ) ABCZA
    DBAEBEFZDZADZGQSAABHITASDZGSAJUAABDZRDZGUCUAABRKLUCRUBDZGUBRJUDRREZDZGUBUER
    ABMNGUFROLPPPPP $.

  $( Lemma for Kalmbach implication study.  (Contributed by NM,
     15-Dec-1997.) $)
  u3lemoa $p |- ( ( a ->3 b ) v a ) =
              ( a v ( ( a ' ^ b ) v ( a ' ^ b ' ) ) ) $=
    ( wi3 wo wn wa df-i3 ax-r5 ax-a3 lea df-le2 lor ax-a2 ax-r2 ) ABCZADAEZBFPB
    EFDZAPBDZFZDZADZAQDZOTAABGHUAQSADZDZUBQSAIUDQADUBUCAQSAARJKLQAMNNN $.

  $( Lemma for non-tollens implication study.  (Contributed by NM,
     15-Dec-1997.) $)
  u4lemoa $p |- ( ( a ->4 b ) v a ) = 1 $=
    ( wi4 wo wa wn df-i4 ax-r5 ax-a3 comor1 comcom7 comor2 ax-a2 df-t ax-r2 lor
    wt ax-r1 or1 ancom comcom2 fh4r or32 ran an1 anor1 ) ABCZADABEZAFZBEZDZUIBD
    ZBFZEZDZADZQUGUOAABGHUPUKUNADZDZQUKUNAIURUKUMADZDZQUQUSUKUQULADZUSEZUSULAUM
    ULAUIBJKULBUIBLUAUBVBQUSEZUSVAQUSVAUIADZBDZQUIBAUCVEBVDDZQVDBMVFBQDZQVGVFQV
    DBQAUIDVDANAUIMOPRBSOOOUDVCUSQEUSQUSTUSUEOOOPUTUHUJUSDZDZQUHUJUSIVIUHQDQVHQ
    UHVHUSUJDZQUJUSMVJUSUSFZDZQUJVKUSUJBUIEVKUIBTBAUFOPQVLUSNROOPUHSOOOOO $.

  $( Lemma for relevance implication study.  (Contributed by NM,
     15-Dec-1997.) $)
  u5lemoa $p |- ( ( a ->5 b ) v a ) =
              ( a v ( ( a ' ^ b ) v ( a ' ^ b ' ) ) ) $=
    ( wi5 wo wa wn df-i5 ax-r5 ax-a2 ax-a3 lor ax-r1 orabs ax-r2 ) ABCZADABEZAF
    ZBEZDQBFEZDZADZARSDZDZOTAABGHUAATDZUCTAIUDAPUBDZDZUCTUEAPRSJKUFAPDZUBDZUCUH
    UFAPUBJLUGAUBABMHNNNN $.

  $( Lemma for Sasaki implication study.  (Contributed by NM, 15-Dec-1997.) $)
  u1lemona $p |- ( ( a ->1 b ) v a ' ) = ( a ' v ( a ^ b ) ) $=
    ( wi1 wn wo wa df-i1 ax-r5 or32 oridm ax-r2 ) ABCZADZEMABFZEZMEZOLOMABGHPMM
    EZNEOMNMIQMNMJHKK $.

  $( Lemma for Dishkant implication study.  (Contributed by NM,
     15-Dec-1997.) $)
  u2lemona $p |- ( ( a ->2 b ) v a ' ) = ( a ' v b ) $=
    ( wi2 wn wo wa df-i2 ax-r5 ax-a3 ax-a2 lea df-le2 ax-r2 ) ABCZADZEBOBDZFZEZ
    OEZOBEZNROABGHSBQOEZEZTBQOIUBUABETBUAJUAOBQOOPKLHMMM $.

  $( Lemma for Kalmbach implication study.  (Contributed by NM,
     15-Dec-1997.) $)
  u3lemona $p |- ( ( a ->3 b ) v a ' ) = ( a ' v b ) $=
    ( wi3 wn wo wa df-i3 ax-r5 or32 lea lel2or df-le2 omln ax-r2 ) ABCZADZEPBFZ
    PBDZFZEZAPBEZFZEZPEZUAOUCPABGHUDTPEZUBEZUATUBPIUFPUBEUAUEPUBTPQPSPBJPRJKLHA
    BMNNN $.

  $( Lemma for non-tollens implication study.  (Contributed by NM,
     15-Dec-1997.) $)
  u4lemona $p |- ( ( a ->4 b ) v a ' ) = ( a ' v b ) $=
    ( wi4 wn wo wa df-i4 ax-r5 ax-a3 lea df-le2 lor ax-r2 comor1 comcom7 comor2
    or32 com2an wt ax-r1 com2or comcom2 fh4 lear leor letr leo lel2or df-a con3
    df-t 2an an1 ) ABCZADZEABFZUOBFZEZUOBEZBDZFZEZUOEZUSUNVBUOABGHVCURUOEZVAEZU
    SURVAUOQVEUPUOEZVAEZUSVDVFVAVDUPUQUOEZEVFUPUQUOIVHUOUPUQUOUOBJKLMHVGVFUSEZV
    FUTEZFZUSUSVFUTUSUPUOUSABUSAUOBNZOUOBPZRVLUAUSBVMUBUCVKUSSFUSVIUSVJSVFUSUPU
    SUOUPBUSABUDBUOUEUFUOBUGUHKVJUPUOUTEZEZSUPUOUTIVOUPUPDZEZSVNVPUPVNUPUPVNDAB
    UITUJLSVQUPUKTMMULUSUMMMMMM $.

  $( Lemma for relevance implication study.  (Contributed by NM,
     15-Dec-1997.) $)
  u5lemona $p |- ( ( a ->5 b ) v a ' ) = ( a ' v ( a ^ b ) ) $=
    ( wi5 wn wo wa df-i5 ax-r5 ax-a3 lea lel2or df-le2 lor ax-a2 ax-r2 ) ABCZAD
    ZEABFZQBFZEQBDZFZEZQEZQREZPUBQABGHUCRSUAEZEZQEZUDUBUFQRSUAIHUGRUEQEZEZUDRUE
    QIUIRQEUDUHQRUEQSQUAQBJQTJKLMRQNOOOO $.

  $( Lemma for Sasaki implication study.  (Contributed by NM, 15-Dec-1997.) $)
  u1lemob $p |- ( ( a ->1 b ) v b ) = ( a ' v b ) $=
    ( wi1 wo wn wa df-i1 ax-r5 or32 ax-a2 lear leor letr df-le2 ax-r2 ) ABCZBDA
    EZABFZDZBDZQBDZPSBABGHTUARDZUAQRBIUBRUADUAUARJRUARBUAABKBQLMNOOO $.

  $( Lemma for Dishkant implication study.  (Contributed by NM,
     15-Dec-1997.) $)
  u2lemob $p |- ( ( a ->2 b ) v b ) = ( ( a ' ^ b ' ) v b ) $=
    ( wi2 wo wn wa df-i2 ax-r5 or32 ax-a2 oridm lor ax-r2 ) ABCZBDBAEBEFZDZBDZO
    BDZNPBABGHQBBDZODZRBOBITOSDRSOJSBOBKLMMM $.

  $( Lemma for Kalmbach implication study.  (Contributed by NM,
     15-Dec-1997.) $)
  u3lemob $p |- ( ( a ->3 b ) v b ) = ( a ' v b ) $=
    ( wi3 wo wn wa df-i3 ax-r5 or32 lear df-le2 ax-r2 2or comor2 comor1 comcom2
    ancom wt lor ax-r1 com2an com2or comcom7 fh4 or12 oridm ax-a2 lea letr oran
    leo con2 df-t 2an an1 ) ABCZBDAEZBFZUQBEZFZDZAUQBDZFZDZBDZVBUPVDBABGHVEVABD
    ZVCDZVBVAVCBIVGBUTDZVBAFZDZVBVFVHVCVIVFURBDZUTDVHURUTBIVKBUTURBUQBJKHLAVBQM
    VJVHVBDZVHADZFZVBVBVHAVBBUTUQBNZVBUQUSUQBOZVBBVOPUAUBVBAVPUCUDVNVBRFVBVLVBV
    MRVLBVBDZUTDZVBBUTVBIVRVBUTDZVBVQVBUTVQUQBBDZDVBBUQBUEVTBUQBUFSLHVSUTVBDVBV
    BUTUGUTVBUTUQVBUQUSUHUQBUKUIKLLLVMBADZUTDZRBUTAIWBWAWAEZDZRUTWCWAUTUSUQFZWC
    UQUSQWCWEWAWEBAUJULTLSRWDWAUMTLLUNVBUOLLLLL $.

  $( Lemma for non-tollens implication study.  (Contributed by NM,
     15-Dec-1997.) $)
  u4lemob $p |- ( ( a ->4 b ) v b ) = ( a ' v b ) $=
    ( wi4 wo wa wn df-i4 ax-r5 or32 lear lel2or df-le2 comorr2 comid comcom2 wt
    fh3 or12 oridm ax-r2 lor df-t ax-r1 2an an1 ) ABCZBDABEZAFZBEZDZUHBDZBFZEZD
    ZBDZUKUFUNBABGHUOUJBDZUMDZUKUJUMBIUQBUMDZUKUPBUMUJBUGBUIABJUHBJKLHURBUKDZBU
    LDZEZUKBUKULUHBMBBBNOQVAUKPEUKUSUKUTPUSUHBBDZDUKBUHBRVBBUHBSUATPUTBUBUCUDUK
    UETTTTT $.

  $( Lemma for relevance implication study.  (Contributed by NM,
     15-Dec-1997.) $)
  u5lemob $p |- ( ( a ->5 b ) v b ) = ( ( a ' ^ b ' ) v b ) $=
    ( wi5 wo wa wn df-i5 ax-r5 ax-a3 lear lel2or leor letr df-le2 ax-r2 ) ABCZB
    DABEZAFZBEZDZRBFEZDZBDZUABDZPUBBABGHUCTUDDUDTUABITUDTBUDQBSABJRBJKBUALMNOO
    $.

  $( Lemma for Sasaki implication study.  (Contributed by NM, 15-Dec-1997.) $)
  u1lemonb $p |- ( ( a ->1 b ) v b ' ) = 1 $=
    ( wi1 wn wo wa wt df-i1 ax-r5 or32 df-a lor df-t ax-r1 ax-r2 ) ABCZBDZEADZA
    BFZEZQEZGPTQABHIUARQEZSEZGRSQJUCUBUBDZEZGSUDUBABKLGUEUBMNOOO $.

  $( Lemma for Dishkant implication study.  (Contributed by NM,
     15-Dec-1997.) $)
  u2lemonb $p |- ( ( a ->2 b ) v b ' ) = 1 $=
    ( wi2 wn wo wa wt df-i2 ax-r5 or32 ax-a2 df-t lor ax-r1 or1 ax-r2 ) ABCZBDZ
    EBADRFZEZREZGQTRABHIUABREZSEZGBSRJUCSUBEZGUBSKUDSGEZGUEUDGUBSBLMNSOPPPP $.

  $( Lemma for Kalmbach implication study.  (Contributed by NM,
     15-Dec-1997.) $)
  u3lemonb $p |- ( ( a ->3 b ) v b ' ) = 1 $=
    ( wi3 wn wo wa df-i3 ax-r5 or32 ax-a3 lear df-le2 lor ax-r2 ancom 2or ax-r1
    wt df-t or1 comor1 comor2 com2an comcom2 com2or comcom7 fh4 ax-a2 anor1 2an
    con2 an1 ) ABCZBDZEADZBFZUOUNFZEZAUOBEZFZEZUNEZRUMVAUNABGHVBURUNEZUTEZRURUT
    UNIVDUPUNEZUSAFZEZRVCVEUTVFVCUPUQUNEZEVEUPUQUNJVHUNUPUQUNUOUNKLMNAUSOPVGVEU
    SEZVEAEZFZRUSVEAUSUPUNUSUOBUOBUAZUOBUBZUCUSBVMUDUEUSAVLUFUGVKRRFRVIRVJRVIUP
    UNUSEZEZRUPUNUSJVOUPRERVNRUPVNUSUNEZRUNUSUHVPUOBUNEZEZRUOBUNJVRUORERVQRUORV
    QBSQMUOTNNNMUPTNNVJUPUNAEZEZRUPUNAJVTUPUPDZEZRVSWAUPWAVSUPVSUPBUOFVSDUOBOBA
    UINUKQMRWBUPSQNNUJRULNNNNN $.

  $( Lemma for non-tollens implication study.  (Contributed by NM,
     15-Dec-1997.) $)
  u4lemonb $p |- ( ( a ->4 b ) v b ' ) =
               ( ( ( a ^ b ) v ( a ' ^ b ) ) v b ' ) $=
    ( wi4 wn wo wa df-i4 ax-r5 ax-a3 lear df-le2 lor ax-r2 ) ABCZBDZEABFADZBFEZ
    PBEZOFZEZOEZQOEZNTOABGHUAQSOEZEUBQSOIUCOQSOROJKLMM $.

  $( Lemma for relevance implication study.  (Contributed by NM,
     15-Dec-1997.) $)
  u5lemonb $p |- ( ( a ->5 b ) v b ' ) =
               ( ( ( a ^ b ) v ( a ' ^ b ) ) v b ' ) $=
    ( wi5 wn wo wa df-i5 ax-r5 ax-a3 lear df-le2 lor ax-r2 ) ABCZBDZEABFADZBFEZ
    POFZEZOEZQOEZNSOABGHTQROEZEUAQROIUBOQROPOJKLMM $.

  $( Lemma for Sasaki implication study.  (Contributed by NM, 15-Dec-1997.) $)
  u1lemnaa $p |- ( ( a ->1 b ) ' ^ a ) = ( a ^ ( a ' v b ' ) ) $=
    ( wi1 wn wa wo anor2 u1lemona ax-r4 df-a lor ax-r1 ax-r2 ) ABCZDAENADZFZDZA
    OBDFZEZNAGQOABEZFZDZSPUAABHISUBSORDZFZDZUBARJUBUEUAUDTUCOABJKILMLMM $.

  $( Lemma for Dishkant implication study.  (Contributed by NM,
     15-Dec-1997.) $)
  u2lemnaa $p |- ( ( a ->2 b ) ' ^ a ) = ( a ^ b ' ) $=
    ( wi2 wn wa wo anor2 u2lemona ax-r4 ax-r2 anor1 ax-r1 ) ABCZDAEZADZBFZDZABD
    EZNMOFZDQMAGSPABHIJRQABKLJ $.

  $( Lemma for Kalmbach implication study.  (Contributed by NM,
     15-Dec-1997.) $)
  u3lemnaa $p |- ( ( a ->3 b ) ' ^ a ) = ( a ^ b ' ) $=
    ( wi3 wn wa wo anor2 anor1 u3lemona ax-r4 ax-r1 ax-r2 ) ABCZDAEMADZFZDZABDE
    ZMAGQPQNBFZDZPABHPSORABIJKLKL $.

  $( Lemma for non-tollens implication study.  (Contributed by NM,
     15-Dec-1997.) $)
  u4lemnaa $p |- ( ( a ->4 b ) ' ^ a ) = ( a ^ b ' ) $=
    ( wi4 wn wa wo anor2 u4lemona ax-r4 anor1 ax-r1 ax-r2 ) ABCZDAEMADZFZDZABDE
    ZMAGPNBFZDZQORABHIQSABJKLL $.

  $( Lemma for relevance implication study.  (Contributed by NM,
     15-Dec-1997.) $)
  u5lemnaa $p |- ( ( a ->5 b ) ' ^ a ) = ( a ^ ( a ' v b ' ) ) $=
    ( wi5 wn wa wo anor2 u5lemona ax-r4 anor1 ax-r1 df-a con2 lan ax-r2 ) ABCZD
    AEPADZFZDZAQBDFZEZPAGSQABEZFZDZUARUCABHIUDAUBDZEZUAUFUDAUBJKUETAUBTABLMNOOO
    $.

  $( Lemma for Sasaki implication study.  (Contributed by NM, 15-Dec-1997.) $)
  u1lemnana $p |- ( ( a ->1 b ) ' ^ a ' ) = 0 $=
    ( wi1 wn wa wt wf wo anor3 u1lemoa ax-r4 ax-r2 df-f ax-r1 ) ABCZDADEZFDZGPO
    AHZDQOAIRFABJKLGQMNL $.

  $( Lemma for Dishkant implication study.  (Contributed by NM,
     15-Dec-1997.) $)
  u2lemnana $p |- ( ( a ->2 b ) ' ^ a ' ) = 0 $=
    ( wi2 wn wa wt wf wo anor3 u2lemoa ax-r4 ax-r2 df-f ax-r1 ) ABCZDADEZFDZGPO
    AHZDQOAIRFABJKLGQMNL $.

  $( Lemma for Kalmbach implication study.  (Contributed by NM,
     16-Dec-1997.) $)
  u3lemnana $p |- ( ( a ->3 b ) ' ^ a ' ) =
                ( a ' ^ ( ( a v b ) ^ ( a v b ' ) ) ) $=
    ( wi3 wn wa wo u3lemoa ax-a2 anor3 anor2 2or oran3 ax-r2 lor oran 3tr2 con1
    oran1 ) ABCZDADZEZTABFZABDZFZEZEZSAFZAUEDZFZUADUFDUGATBEZTUCEZFZFUIABGULUHA
    ULUKUJFZUHUJUKHUMUBDZUDDZFUHUKUNUJUOABIABJKUBUDLMMNMSAOAUERPQ $.

  $( Lemma for non-tollens implication study.  (Contributed by NM,
     15-Dec-1997.) $)
  u4lemnana $p |- ( ( a ->4 b ) ' ^ a ' ) = 0 $=
    ( wi4 wn wa wt wf wo anor3 u4lemoa ax-r4 ax-r2 df-f ax-r1 ) ABCZDADEZFDZGPO
    AHZDQOAIRFABJKLGQMNL $.

  $( Lemma for relevance implication study.  (Contributed by NM,
     16-Dec-1997.) $)
  u5lemnana $p |- ( ( a ->5 b ) ' ^ a ' ) =
                ( a ' ^ ( ( a v b ) ^ ( a v b ' ) ) ) $=
    ( wi5 wn wa wo u5lemoa ax-a2 anor3 anor2 2or oran3 ax-r2 lor oran 3tr2 con1
    oran1 ) ABCZDADZEZTABFZABDZFZEZEZSAFZAUEDZFZUADUFDUGATBEZTUCEZFZFUIABGULUHA
    ULUKUJFZUHUJUKHUMUBDZUDDZFUHUKUNUJUOABIABJKUBUDLMMNMSAOAUERPQ $.

  $( Lemma for Sasaki implication study.  (Contributed by NM, 16-Dec-1997.) $)
  u1lemnab $p |- ( ( a ->1 b ) ' ^ b ) = 0 $=
    ( wi1 wn wa wf wo wt u1lemonb oran1 df-f con2 ax-r1 3tr2 con1 ) ABCZDBEZFPB
    DGHQDFDZABIPBJRHFHKLMNO $.

  $( Lemma for Dishkant implication study.  (Contributed by NM,
     16-Dec-1997.) $)
  u2lemnab $p |- ( ( a ->2 b ) ' ^ b ) = 0 $=
    ( wi2 wn wa wf wo wt u2lemonb oran1 df-f con2 ax-r1 3tr2 con1 ) ABCZDBEZFPB
    DGHQDFDZABIPBJRHFHKLMNO $.

  $( Lemma for Kalmbach implication study.  (Contributed by NM,
     16-Dec-1997.) $)
  u3lemnab $p |- ( ( a ->3 b ) ' ^ b ) = 0 $=
    ( wi3 wn wa wf wo wt u3lemonb oran1 df-f con2 ax-r1 3tr2 con1 ) ABCZDBEZFPB
    DGHQDFDZABIPBJRHFHKLMNO $.

  $( Lemma for non-tollens implication study.  (Contributed by NM,
     16-Dec-1997.) $)
  u4lemnab $p |- ( ( a ->4 b ) ' ^ b ) =
               ( ( ( a v b ' ) ^ ( a ' v b ' ) ) ^ b ) $=
    ( wi4 wn wa u4lemonb ax-a2 anor2 df-a 2or oran3 ax-r2 ax-r5 oran1 3tr2 con1
    wo ) ABCZDBEZABDZQZADZTQZEZBEZRTQZUDDZTQZSDUEDUFABEZUBBEZQZTQUHABFUKUGTUKUJ
    UIQZUGUIUJGULUADZUCDZQUGUJUMUIUNABHABIJUAUCKLLMLRBNUDBKOP $.

  $( Lemma for relevance implication study.  (Contributed by NM,
     16-Dec-1997.) $)
  u5lemnab $p |- ( ( a ->5 b ) ' ^ b ) =
               ( ( ( a v b ' ) ^ ( a ' v b ' ) ) ^ b ) $=
    ( wi5 wn wa u5lemonb ax-a2 anor2 df-a 2or oran3 ax-r2 ax-r5 oran1 3tr2 con1
    wo ) ABCZDBEZABDZQZADZTQZEZBEZRTQZUDDZTQZSDUEDUFABEZUBBEZQZTQUHABFUKUGTUKUJ
    UIQZUGUIUJGULUADZUCDZQUGUJUMUIUNABHABIJUAUCKLLMLRBNUDBKOP $.

  $( Lemma for Sasaki implication study.  (Contributed by NM, 16-Dec-1997.) $)
  u1lemnanb $p |- ( ( a ->1 b ) ' ^ b ' ) = ( a ^ b ' ) $=
    ( wi1 wn wa wo u1lemob oran oran2 3tr2 con1 ) ABCZDBDZEZAMEZLBFADBFNDODABGL
    BHABIJK $.

  $( Lemma for Dishkant implication study.  (Contributed by NM,
     16-Dec-1997.) $)
  u2lemnanb $p |- ( ( a ->2 b ) ' ^ b ' ) = ( ( a v b ) ^ b ' ) $=
    ( wi2 wn wa wo u2lemob anor3 ax-r5 ax-r2 oran oran2 3tr2 con1 ) ABCZDBDZEZA
    BFZPEZOBFZRDZBFZQDSDTADPEZBFUBABGUCUABABHIJOBKRBLMN $.

  $( Lemma for Kalmbach implication study.  (Contributed by NM,
     16-Dec-1997.) $)
  u3lemnanb $p |- ( ( a ->3 b ) ' ^ b ' ) = ( a ^ b ' ) $=
    ( wi3 wn wa wo u3lemob oran oran2 3tr2 con1 ) ABCZDBDZEZAMEZLBFADBFNDODABGL
    BHABIJK $.

  $( Lemma for non-tollens implication study.  (Contributed by NM,
     16-Dec-1997.) $)
  u4lemnanb $p |- ( ( a ->4 b ) ' ^ b ' ) = ( a ^ b ' ) $=
    ( wi4 wn wa wo u4lemob oran oran2 3tr2 con1 ) ABCZDBDZEZAMEZLBFADBFNDODABGL
    BHABIJK $.

  $( Lemma for relevance implication study.  (Contributed by NM,
     16-Dec-1997.) $)
  u5lemnanb $p |- ( ( a ->5 b ) ' ^ b ' ) = ( ( a v b ) ^ b ' ) $=
    ( wi5 wn wa wo u5lemob anor3 ax-r5 ax-r2 oran oran2 3tr2 con1 ) ABCZDBDZEZA
    BFZPEZOBFZRDZBFZQDSDTADPEZBFUBABGUCUABABHIJOBKRBLMN $.

  $( Lemma for Sasaki implication study.  (Contributed by NM, 16-Dec-1997.) $)
  u1lemnoa $p |- ( ( a ->1 b ) ' v a ) = a $=
    ( wi1 wn wo wa anor1 ax-r1 u1lemana ax-r2 con1 ) ABCZDAEZAMDZLADZFZOPNLAGHA
    BIJK $.

  $( Lemma for Dishkant implication study.  (Contributed by NM,
     16-Dec-1997.) $)
  u2lemnoa $p |- ( ( a ->2 b ) ' v a ) = ( ( a v b ) ^ ( a v b ' ) ) $=
    ( wi2 wn wo wa u2lemana ax-a2 anor3 anor2 2or ax-r2 anor1 oran3 3tr2 con1 )
    ABCZDAEZABEZABDZEZFZQADZFZSDZUADZEZRDUBDUDUCBFZUCTFZEZUGABGUJUIUHEUGUHUIHUI
    UEUHUFABIABJKLLQAMSUANOP $.

  $( Lemma for Kalmbach implication study.  (Contributed by NM,
     16-Dec-1997.) $)
  u3lemnoa $p |- ( ( a ->3 b ) ' v a ) = ( ( a v b ) ^ ( a v b ' ) ) $=
    ( wi3 wn wo wa u3lemana ax-a2 anor3 anor2 2or ax-r2 anor1 oran3 3tr2 con1 )
    ABCZDAEZABEZABDZEZFZQADZFZSDZUADZEZRDUBDUDUCBFZUCTFZEZUGABGUJUIUHEUGUHUIHUI
    UEUHUFABIABJKLLQAMSUANOP $.

  $( Lemma for non-tollens implication study.  (Contributed by NM,
     16-Dec-1997.) $)
  u4lemnoa $p |- ( ( a ->4 b ) ' v a ) = ( ( a v b ) ^ ( a v b ' ) ) $=
    ( wi4 wn wo wa u4lemana ax-a2 anor3 anor2 2or ax-r2 anor1 oran3 3tr2 con1 )
    ABCZDAEZABEZABDZEZFZQADZFZSDZUADZEZRDUBDUDUCBFZUCTFZEZUGABGUJUIUHEUGUHUIHUI
    UEUHUFABIABJKLLQAMSUANOP $.

  $( Lemma for relevance implication study.  (Contributed by NM,
     16-Dec-1997.) $)
  u5lemnoa $p |- ( ( a ->5 b ) ' v a ) = ( ( a v b ) ^ ( a v b ' ) ) $=
    ( wi5 wn wo wa u5lemana ax-a2 anor3 anor2 2or ax-r2 anor1 oran3 3tr2 con1 )
    ABCZDAEZABEZABDZEZFZQADZFZSDZUADZEZRDUBDUDUCBFZUCTFZEZUGABGUJUIUHEUGUHUIHUI
    UEUHUFABIABJKLLQAMSUANOP $.

  $( Lemma for Sasaki implication study.  (Contributed by NM, 16-Dec-1997.) $)
  u1lemnona $p |- ( ( a ->1 b ) ' v a ' ) = ( a ' v b ' ) $=
    ( wi1 wn wo wa u1lemaa df-a 3tr2 con1 ) ABCZDADZEZLBDEZKAFABFMDNDABGKAHABHI
    J $.

  $( Lemma for Dishkant implication study.  (Contributed by NM,
     16-Dec-1997.) $)
  u2lemnona $p |- ( ( a ->2 b ) ' v a ' ) = ( a ' v b ' ) $=
    ( wi2 wn wo wa u2lemaa df-a 3tr2 con1 ) ABCZDADZEZLBDEZKAFABFMDNDABGKAHABHI
    J $.

  $( Lemma for Kalmbach implication study.  (Contributed by NM,
     16-Dec-1997.) $)
  u3lemnona $p |- ( ( a ->3 b ) ' v a ' ) = ( a ' v ( a ^ b ' ) ) $=
    ( wi3 wn wo wa u3lemaa oran2 lan ax-r2 df-a anor1 3tr2 con1 ) ABCZDADZEZPAB
    DFZEZOAFZARDZFZQDSDTAPBEZFUBABGUCUAAABHIJOAKARLMN $.

  $( Lemma for non-tollens implication study.  (Contributed by NM,
     16-Dec-1997.) $)
  u4lemnona $p |- ( ( a ->4 b ) ' v a ' ) = ( a ' v b ' ) $=
    ( wi4 wn wo wa u4lemaa df-a 3tr2 con1 ) ABCZDADZEZLBDEZKAFABFMDNDABGKAHABHI
    J $.

  $( Lemma for relevance implication study.  (Contributed by NM,
     16-Dec-1997.) $)
  u5lemnona $p |- ( ( a ->5 b ) ' v a ' ) = ( a ' v b ' ) $=
    ( wi5 wn wo wa u5lemaa df-a 3tr2 con1 ) ABCZDADZEZLBDEZKAFABFMDNDABGKAHABHI
    J $.

  $( Lemma for Sasaki implication study.  (Contributed by NM, 16-Dec-1997.) $)
  u1lemnob $p |- ( ( a ->1 b ) ' v b ) = ( a v b ) $=
    ( wi1 wn wo wa u1lemanb anor1 anor3 3tr2 con1 ) ABCZDBEZABEZLBDZFADOFMDNDAB
    GLBHABIJK $.

  $( Lemma for Dishkant implication study.  (Contributed by NM,
     16-Dec-1997.) $)
  u2lemnob $p |- ( ( a ->2 b ) ' v b ) = ( a v b ) $=
    ( wi2 wn wo wa u2lemanb anor1 anor3 3tr2 con1 ) ABCZDBEZABEZLBDZFADOFMDNDAB
    GLBHABIJK $.

  $( Lemma for Kalmbach implication study.  (Contributed by NM,
     16-Dec-1997.) $)
  u3lemnob $p |- ( ( a ->3 b ) ' v b ) = ( a v b ) $=
    ( wi3 wn wo wa u3lemanb anor1 anor3 3tr2 con1 ) ABCZDBEZABEZLBDZFADOFMDNDAB
    GLBHABIJK $.

  $( Lemma for non-tollens implication study.  (Contributed by NM,
     16-Dec-1997.) $)
  u4lemnob $p |- ( ( a ->4 b ) ' v b ) = ( ( a ^ b ' ) v b ) $=
    ( wi4 wn wo wa u4lemanb oran2 ran ax-r2 anor1 anor3 3tr2 con1 ) ABCZDBEZABD
    ZFZBEZOQFZRDZQFZPDSDTADBEZQFUBABGUCUAQABHIJOBKRBLMN $.

  $( Lemma for relevance implication study.  (Contributed by NM,
     16-Dec-1997.) $)
  u5lemnob $p |- ( ( a ->5 b ) ' v b ) = ( a v b ) $=
    ( wi5 wn wo wa u5lemanb anor1 anor3 3tr2 con1 ) ABCZDBEZABEZLBDZFADOFMDNDAB
    GLBHABIJK $.

  $( Lemma for Sasaki implication study.  (Contributed by NM, 16-Dec-1997.) $)
  u1lemnonb $p |- ( ( a ->1 b ) ' v b ' ) =
                ( ( a v b ' ) ^ ( a ' v b ' ) ) $=
    ( wi1 wn wo wa u1lemab ax-a2 anor2 df-a 2or ax-r2 oran3 3tr2 con1 ) ABCZDBD
    ZEZAQEZADZQEZFZPBFZSDZUADZEZRDUBDUCABFZTBFZEZUFABGUIUHUGEUFUGUHHUHUDUGUEABI
    ABJKLLPBJSUAMNO $.

  $( Lemma for Dishkant implication study.  (Contributed by NM,
     16-Dec-1997.) $)
  u2lemnonb $p |- ( ( a ->2 b ) ' v b ' ) = b ' $=
    ( wi2 wn wo wa df-a ax-r1 u2lemab ax-r2 con3 ) ABCZDBDEZBMDZLBFZBONLBGHABIJ
    K $.

  $( Lemma for Kalmbach implication study.  (Contributed by NM,
     16-Dec-1997.) $)
  u3lemnonb $p |- ( ( a ->3 b ) ' v b ' ) =
                ( ( a v b ' ) ^ ( a ' v b ' ) ) $=
    ( wi3 wn wo wa u3lemab ax-a2 anor2 df-a 2or ax-r2 oran3 3tr2 con1 ) ABCZDBD
    ZEZAQEZADZQEZFZPBFZSDZUADZEZRDUBDUCABFZTBFZEZUFABGUIUHUGEUFUGUHHUHUDUGUEABI
    ABJKLLPBJSUAMNO $.

  $( Lemma for non-tollens implication study.  (Contributed by NM,
     16-Dec-1997.) $)
  u4lemnonb $p |- ( ( a ->4 b ) ' v b ' ) =
                ( ( a v b ' ) ^ ( a ' v b ' ) ) $=
    ( wi4 wn wo wa u4lemab ax-a2 anor2 df-a 2or ax-r2 oran3 3tr2 con1 ) ABCZDBD
    ZEZAQEZADZQEZFZPBFZSDZUADZEZRDUBDUCABFZTBFZEZUFABGUIUHUGEUFUGUHHUHUDUGUEABI
    ABJKLLPBJSUAMNO $.

  $( Lemma for relevance implication study.  (Contributed by NM,
     16-Dec-1997.) $)
  u5lemnonb $p |- ( ( a ->5 b ) ' v b ' ) =
                ( ( a v b ' ) ^ ( a ' v b ' ) ) $=
    ( wi5 wn wo wa u5lemab ax-a2 anor2 df-a 2or ax-r2 oran3 3tr2 con1 ) ABCZDBD
    ZEZAQEZADZQEZFZPBFZSDZUADZEZRDUBDUCABFZTBFZEZUFABGUIUHUGEUFUGUHHUHUDUGUEABI
    ABJKLLPBJSUAMNO $.

  $( Commutation theorem for Sasaki implication.  (Contributed by NM,
     14-Dec-1997.) $)
  u1lemc1 $p |- a C ( a ->1 b ) $=
    ( wn wa wo wi1 comid comcom2 comanr1 com2or df-i1 ax-r1 cbtr ) AACZABDZEZAB
    FZANOAAAGHABIJQPABKLM $.

  $( Commutation theorem for Dishkant implication.  (Contributed by NM,
     14-Dec-1997.) $)
  u2lemc1 $p |- b C ( a ->2 b ) $=
    ( wn wa wo wi2 comid comanr2 comcom6 com2or df-i2 ax-r1 cbtr ) BBACZBCZDZEZ
    ABFZBBPBGBPNOHIJRQABKLM $.

  $( Commutation theorem for Kalmbach implication.  (Contributed by NM,
     14-Dec-1997.) $)
  u3lemc1 $p |- a C ( a ->3 b ) $=
    ( comi31 ) ABC $.

  $( Commutation theorem for non-tollens implication.  (Contributed by NM,
     14-Dec-1997.) $)
  u4lemc1 $p |- b C ( a ->4 b ) $=
    ( wa wn wo wi4 comanr2 com2or comorr2 comid comcom2 com2an df-i4 ax-r1 cbtr
    ) BABCZADZBCZEZQBEZBDZCZEZABFZBSUBBPRABGQBGHBTUAQBIBBBJKLHUDUCABMNO $.

  $( Commutation theorem for relevance implication.  (Contributed by NM,
     14-Dec-1997.) $)
  u5lemc1 $p |- a C ( a ->5 b ) $=
    ( wa wn wo wi5 comanr1 comcom6 com2or df-i5 ax-r1 cbtr ) AABCZADZBCZEZNBDZC
    ZEZABFZAPRAMOABGAONBGHIARNQGHITSABJKL $.

  $( Commutation theorem for relevance implication.  (Contributed by NM,
     14-Dec-1997.) $)
  u5lemc1b $p |- b C ( a ->5 b ) $=
    ( wa wn wo wi5 comanr2 com2or comcom6 df-i5 ax-r1 cbtr ) BABCZADZBCZEZNBDZC
    ZEZABFZBPRBMOABGNBGHBRNQGIHTSABJKL $.

  ${
    ulemc2.1 $e |- a C b $.
    ulemc2.2 $e |- a C c $.
    $( Commutation theorem for Sasaki implication.  (Contributed by NM,
       14-Dec-1997.) $)
    u1lemc2 $p |- a C ( b ->1 c ) $=
      ( wn wa wo wi1 comcom2 com2an com2or df-i1 ax-r1 cbtr ) ABFZBCGZHZBCIZAPQ
      ABDJABCDEKLSRBCMNO $.

    $( Commutation theorem for Dishkant implication.  (Contributed by NM,
       14-Dec-1997.) $)
    u2lemc2 $p |- a C ( b ->2 c ) $=
      ( wn wa wo wi2 comcom2 com2an com2or df-i2 ax-r1 cbtr ) ACBFZCFZGZHZBCIZA
      CREAPQABDJACEJKLTSBCMNO $.

    $( Commutation theorem for Kalmbach implication.  (Contributed by NM,
       14-Dec-1997.) $)
    u3lemc2 $p |- a C ( b ->3 c ) $=
      ( com2i3 ) ABCDEF $.

    $( Commutation theorem for non-tollens implication.  (Contributed by NM,
       14-Dec-1997.) $)
    u4lemc2 $p |- a C ( b ->4 c ) $=
      ( wa wn wo wi4 com2an comcom2 com2or df-i4 ax-r1 cbtr ) ABCFZBGZCFZHZQCHZ
      CGZFZHZBCIZASUBAPRABCDEJAQCABDKZEJLATUAAQCUEELACEKJLUDUCBCMNO $.

    $( Commutation theorem for relevance implication.  (Contributed by NM,
       14-Dec-1997.) $)
    u5lemc2 $p |- a C ( b ->5 c ) $=
      ( wa wn wo wi5 com2an comcom2 com2or df-i5 ax-r1 cbtr ) ABCFZBGZCFZHZQCGZ
      FZHZBCIZASUAAPRABCDEJAQCABDKZEJLAQTUDACEKJLUCUBBCMNO $.
  $}

  ${
    ulemc3.1 $e |- a C b $.
    $( Commutation theorem for Sasaki implication.  (Contributed by NM,
       14-Dec-1997.) $)
    u1lemc3 $p |- a C ( b ->1 a ) $=
      ( comid u1lemc2 ) ABACADE $.

    $( Commutation theorem for Dishkant implication.  (Contributed by NM,
       14-Dec-1997.) $)
    u2lemc3 $p |- a C ( b ->2 a ) $=
      ( u2lemc1 ) BAD $.

    $( Commutation theorem for Kalmbach implication.  (Contributed by NM,
       14-Dec-1997.) $)
    u3lemc3 $p |- a C ( b ->3 a ) $=
      ( comi32 ) ABCD $.

    $( Commutation theorem for non-tollens implication.  (Contributed by NM,
       14-Dec-1997.) $)
    u4lemc3 $p |- a C ( b ->4 a ) $=
      ( u4lemc1 ) BAD $.

    $( Commutation theorem for relevance implication.  (Contributed by NM,
       14-Dec-1997.) $)
    u5lemc3 $p |- a C ( b ->5 a ) $=
      ( u5lemc1b ) BAD $.

    $( Commutation theorem for Sasaki implication.  (Contributed by NM,
       11-Jan-1998.) $)
    u1lemc5 $p |- a C ( a ->1 b ) $=
      ( u1lemc1 ) ABD $.

    $( Commutation theorem for Dishkant implication.  (Contributed by NM,
       11-Jan-1998.) $)
    u2lemc5 $p |- a C ( a ->2 b ) $=
      ( comid u2lemc2 ) AABADCE $.

    $( Commutation theorem for Kalmbach implication.  (Contributed by NM,
       11-Jan-1998.) $)
    u3lemc5 $p |- a C ( a ->3 b ) $=
      ( comi31 ) ABD $.

    $( Commutation theorem for non-tollens implication.  (Contributed by NM,
       11-Jan-1998.) $)
    u4lemc5 $p |- a C ( a ->4 b ) $=
      ( comid u4lemc2 ) AABADCE $.

    $( Commutation theorem for relevance implication.  (Contributed by NM,
       11-Jan-1998.) $)
    u5lemc5 $p |- a C ( a ->5 b ) $=
      ( u5lemc1 ) ABD $.

    $( Lemma for Sasaki implication study.  (Contributed by NM,
       24-Dec-1997.) $)
    u1lemc4 $p |- ( a ->1 b ) = ( a ' v b ) $=
      ( wi1 wn wa wo df-i1 comid comcom2 fh4 ancom wt ax-a2 ax-r1 ax-r2 lan an1
      df-t ) ABDAEZABFGZTBGZABHUATAGZUBFZUBATBAAAIJCKUDUBUCFZUBUCUBLUEUBMFUBUCM
      UBUCATGZMTANMUFASOPQUBRPPPP $.

    $( Lemma for Dishkant implication study.  (Contributed by NM,
       24-Dec-1997.) $)
    u2lemc4 $p |- ( a ->2 b ) = ( a ' v b ) $=
      ( wi2 wn wa wo df-i2 comcom3 comcom4 fh4 ax-a2 df-t ax-r1 2an an1 ax-r2
      wt ) ABDBAEZBEZFGZSBGZABHUABSGZBTGZFZUBSBTABCIABCJKUEUBRFUBUCUBUDRBSLRUDB
      MNOUBPQQQ $.

    $( Lemma for Kalmbach implication study.  (Contributed by NM,
       24-Dec-1997.) $)
    u3lemc4 $p |- ( a ->3 b ) = ( a ' v b ) $=
      ( wi3 wn wa wo df-i3 comcom3 comcom4 fh1 ax-r1 df-t lan ax-r2 comid ax-a2
      wt an1 wf comcom2 dff lor or0 2or fh4 ancom ) ABDAEZBFUHBEZFGZAUHBGZFZGZU
      KABHUMUHABFZGZUKUJUHULUNUJUHBUIGZFZUHUQUJUHBUIABCIABCJKLUQUHRFUHUPRUHRUPB
      MLNUHSOOULAUHFZUNGZUNAUHBAAAPUAZCKUSUNURGZUNURUNQVAUNTGUNURTUNTURAUBLUCUN
      UDOOOUEUOUHAGZUKFZUKAUHBUTCUFVCUKVBFZUKVBUKUGVDUKRFUKVBRUKVBAUHGZRUHAQRVE
      AMLONUKSOOOOO $.

    $( Lemma for non-tollens implication study.  (Contributed by NM,
       24-Dec-1997.) $)
    u4lemc4 $p |- ( a ->4 b ) = ( a ' v b ) $=
      ( wi4 wa wn wo df-i4 comid comcom2 fh2r ax-r1 ancom wt df-t lan an1 ax-r2
      comcom4 wf comcom3 dff lor or0 2or fh4 ax-a2 2an ) ABDABEAFZBEGZUIBGZBFZE
      ZGZUKABHUNBUIULEZGZUKUJBUMUOUJAUIGZBEZBURUJABUICAAAIJKLURBUQEZBUQBMUSBNEB
      UQNBNUQAOLPBQRRRUMUOBULEZGZUOUIULBABCSZABCUAZKVAUOTGUOUTTUOTUTBUBLUCUOUDR
      RUEUPBUIGZBULGZEZUKUIBULVCVBUFVFUKNEUKVDUKVENBUIUGNVEBOLUHUKQRRRR $.

    $( Lemma for relevance implication study.  (Contributed by NM,
       24-Dec-1997.) $)
    u5lemc4 $p |- ( a ->5 b ) = ( a ' v b ) $=
      ( wi5 wa wn wo df-i5 comid comcom2 fh2r ax-r1 ancom wt df-t lan an1 ax-r2
      ax-r5 comcom3 comcom4 fh4 ax-a2 2an ) ABDABEAFZBEGZUEBFZEZGZUEBGZABHUIBUH
      GZUJUFBUHUFAUEGZBEZBUMUFABUECAAAIJKLUMBULEZBULBMUNBNEBULNBNULAOLPBQRRRSUK
      BUEGZBUGGZEZUJUEBUGABCTABCUAUBUQUJNEUJUOUJUPNBUEUCNUPBOLUDUJQRRRR $.
  $}

  $( Commutation theorem for Sasaki implication.  (Contributed by NM,
     19-Mar-1999.) $)
  u1lemc6 $p |- ( a ->1 b ) C ( a ' ->1 b ) $=
    ( wi1 wn wo wa lea ax-a1 lbtr leo letr ud1lem0c df-i1 le3tr1 lecom comcom6
    ) ABCZADZBCZQDZSARBDEZFZRDZRBFZEZTSUBUCUEUBAUCAUAGAHIUCUDJKABLRBMNOP $.

  $( Commutation theorem for ` ->1 ` and ` ->2 ` .  (Contributed by NM,
     5-Jul-2000.) $)
  comi12 $p |- ( a ->1 b ) C ( c ->2 a ) $=
    ( wi1 wn wa wo wi2 df-i1 lea leo letr lecom comcom anor3 cbtr comcom7 df-i2
    ax-r1 bctr ) ABDAEZABFZGZCAHZABIUCACEUAFZGZUDUCUFUCUAUEEZFZUFEUHUCUHUCUHUAU
    CUAUGJUAUBKLMNAUEOPQUDUFCARSPT $.

  ${
    i1com.1 $e |- b =< ( a ->1 b ) $.
    $( Commutation expressed with ` ->1 ` .  (Contributed by NM,
       1-Dec-1999.) $)
    i1com $p |- a C b $=
      ( wi1 wa wn wo ancom df2le2 u1lemab 2or ax-r2 3tr2 df-c1 comcom ) BABABAB
      DZEPBEZBBAEZBAFZEZGZBPHBPCIQABEZSBEZGUAABJUBRUCTABHSBHKLMNO $.
  $}

  ${
    comi1.1 $e |- a C b $.
    $( Commutation expressed with ` ->1 ` .  (Contributed by NM,
       1-Dec-1999.) $)
    comi1 $p |- b =< ( a ->1 b ) $=
      ( wa wn wo wi1 ancom ax-r5 ax-a2 ax-r2 lear leror bltr comcom df-c2 df-i1
      le3tr1 ) BADZBAEZDZFZTABDZFZBABGUBUAUCFZUDUBUCUAFUESUCUABAHIUCUAJKUATUCBT
      LMNBAABCOPABQR $.
  $}

  ${
    ulemle1.1 $e |- a =< b $.
    $( L.e. to Sasaki implication.  (Contributed by NM, 11-Jan-1998.) $)
    u1lemle1 $p |- ( a ->1 b ) = 1 $=
      ( wi1 wn wo wt lecom u1lemc4 sklem ax-r2 ) ABDAEBFGABABCHIABCJK $.

    $( L.e. to Dishkant implication.  (Contributed by NM, 11-Jan-1998.) $)
    u2lemle1 $p |- ( a ->2 b ) = 1 $=
      ( wi2 wn wo wt lecom u2lemc4 sklem ax-r2 ) ABDAEBFGABABCHIABCJK $.

    $( L.e. to Kalmbach implication.  (Contributed by NM, 11-Jan-1998.) $)
    u3lemle1 $p |- ( a ->3 b ) = 1 $=
      ( wi3 wn wo wt lecom u3lemc4 sklem ax-r2 ) ABDAEBFGABABCHIABCJK $.

    $( L.e. to non-tollens implication.  (Contributed by NM, 11-Jan-1998.) $)
    u4lemle1 $p |- ( a ->4 b ) = 1 $=
      ( wi4 wn wo wt lecom u4lemc4 sklem ax-r2 ) ABDAEBFGABABCHIABCJK $.

    $( L.e. to relevance implication.  (Contributed by NM, 11-Jan-1998.) $)
    u5lemle1 $p |- ( a ->5 b ) = 1 $=
      ( wi5 wn wo wt lecom u5lemc4 sklem ax-r2 ) ABDAEBFGABABCHIABCJK $.
  $}

  ${
    u1lemle2.1 $e |- ( a ->1 b ) = 1 $.
    $( Sasaki implication to l.e.  (Contributed by NM, 11-Jan-1998.) $)
    u1lemle2 $p |- a =< b $=
      ( wa wf wo wt wn anidm ran ax-r1 anass ax-r2 dff 2or ax-a2 coman1 comcom2
      lan fh2 wi1 df-i1 or0 an1 3tr2 df2le1 ) ABABDZEFZAGDZUGAUHAAHZUGFZDZUIUHA
      UGDZAUJDZFZULUGUMEUNUGAADZBDZUMUQUGUPABAIJKAABLMANOULUOULAUGUJFZDUOUKURAU
      JUGPSUGAUJABQZUGAUSRTMKMUKGAUKABUAZGUTUKABUBKCMSMUGUCAUDUEUF $.
  $}

  ${
    u2lemle2.1 $e |- ( a ->2 b ) = 1 $.
    $( Dishkant implication to l.e.  (Contributed by NM, 11-Jan-1998.) $)
    u2lemle2 $p |- a =< b $=
      ( wa wf wo wt ax-a2 lan coman1 comcom7 coman2 fh2 ancom anass ax-r1 ax-r2
      wn dff 3tr2 an0 ax-r5 wi2 df-i2 or0 an1 df2le1 ) ABABDZEFZAGDZUHAUIABARZB
      RZDZFZDZUJUOUIUOAUMBFZDZUIUNUPABUMHIUQAUMDZUHFZUIUMABUMAUKULJKUMBUKULLKMU
      SEUHFUIUREUHAUKDZULDULUTDZUREUTULNAUKULOVAULEDEUTEULEUTASPIULUAQTUBEUHHQQ
      QPUNGAUNABUCZGVBUNABUDPCQIQUHUEAUFTUG $.
  $}

  ${
    u3lemle2.1 $e |- ( a ->3 b ) = 1 $.
    $( Kalmbach implication to l.e.  (Contributed by NM, 11-Jan-1998.) $)
    u3lemle2 $p |- a =< b $=
      ( i3le ) ABCD $.
  $}

  ${
    u4lemle2.1 $e |- ( a ->4 b ) = 1 $.
    $( Non-tollens implication to l.e.  (Contributed by NM, 11-Jan-1998.) $)
    u4lemle2 $p |- a =< b $=
      ( wa wn wo wt ax-r1 ax-r2 comanr1 com2or comcom com2an comanr2 comcom3 wf
      lan anass dff 3tr2 wi4 df-i4 comcom6 comor1 comcom7 fh2 fh1 anidm ran an0
      comor2 ancom 2or or0 anor1 an12 3tr1 an1 df2le1 ) ABAABDZAEZBDZFZVABFZBEZ
      DZFZDZAGDUTAVGGAVGABUAZGVIVGABUBHCIQVHAVCDZAVFDZFZUTVCAVFAVCAUTVBABJZAVBV
      ABJUCZKLVCVDVEVDVCVDUTVBVDABVDAVABUDZUEVABUKZMVDVABVOVPMKLVEVCVEUTVBBUTAB
      NOBVBVABNOKLMUFVLUTPFZUTVJUTVKPVJAUTDZAVBDZFZUTAUTVBVMVNUGVTVQUTVQVTUTVRP
      VSUTAADZBDZVRWBUTWAABAUHUIHAABRIPAVADZBDZVSBPDBWCDPWDPWCBASQBUJBWCULTAVAB
      RIUMHUTUNZIIVDAVEDZDVDVDEZDVKPWFWGVDABUOQAVDVEUPVDSUQUMWEIIAURTUS $.
  $}

  ${
    u5lemle2.1 $e |- ( a ->5 b ) = 1 $.
    $( Relevance implication to l.e.  (Contributed by NM, 11-Jan-1998.) $)
    u5lemle2 $p |- a =< b $=
      ( wa wn wo wt wi5 ax-r1 ax-r2 lan comanr1 comcom6 fh1 wf anass ancom 3tr2
      an0 2or df-i5 com2or anidm ran dff or0 an1 df2le1 ) ABAABDZAEZBDZFZUJBEZD
      ZFZDZAGDUIAUOGAUOABHZGUQUOABUAICJKUPAULDZAUNDZFZUIAULUNAUIUKABLZAUKUJBLMZ
      UBAUNUJUMLMNUTUIOFZUIURUIUSOURAUIDZAUKDZFZUIAUIUKVAVBNVFVCUIVDUIVEOVDAADZ
      BDZUIVHVDAABPIVGABAUCUDJAUJDZBDBVIDZVEOVIBQAUJBPVJBODOVIOBOVIAUEZIKBSJRTU
      IUFZJJVIUMDUMVIDZUSOVIUMQAUJUMPVMUMODZOVNVMOVIUMVKKIUMSJRTVLJJAUGRUH $.
  $}

  $( Sasaki implication and biconditional.  (Contributed by NM,
     17-Jan-1998.) $)
  u1lembi $p |- ( ( a ->1 b ) ^ ( b ->1 a ) ) = ( a == b ) $=
    ( wn wa wo wi1 tb ax-a2 2an coman1 comcom2 coman2 fh3 ax-r1 ax-r2 df-i1 lor
    ancom dfb 3tr1 ) ACZABDZEZBCZUBEZDZUBUAUDDEZABFZBAFZDABGUFUBUAEZUBUDEZDZUGU
    CUJUEUKUAUBHUDUBHIUGULUBUAUDUBAABJKUBBABLKMNOUHUCUIUEABPUIUDBADZEUEBAPUMUBU
    DBARQOIABST $.

  $( Dishkant implication and biconditional.  (Contributed by NM,
     17-Jan-1998.) $)
  u2lembi $p |- ( ( a ->2 b ) ^ ( b ->2 a ) ) = ( a == b ) $=
    ( wn wa wo wi2 tb ancom coman1 comcom7 coman2 ax-r1 ax-r2 df-i2 lor 2an dfb
    fh3r 3tr1 ) BACZBCZDZEZAUBEZDZABDUBEZABFZBAFZDABGUEUDUCDZUFUCUDHUFUIUBABUBA
    TUAIJUBBTUAKJRLMUGUCUHUDABNUHAUATDZEUDBANUJUBAUATHOMPABQS $.

  $( Dishkant implication expressed with biconditional.  (Contributed by NM,
     20-Nov-1998.) $)
  i2bi $p |- ( a ->2 b ) = ( b v ( a == b ) ) $=
    ( wi2 tb wo wn wa leor lelor df-i2 dfb lor le3tr1 leo lbtr u2lembi lea bltr
    ax-r1 lel2or lebi ) ABCZBABDZEZBAFBFGZEZBABGZUEEZEUBUDUEUHBUEUGHIABJZUCUHBA
    BKLMBUBUCBUFUBBUENUBUFUISOUCUBBACZGZUBUKUCABPSUBUJQRTUA $.

  $( Kalmbach implication and biconditional.  (Contributed by NM,
     17-Jan-1998.) $)
  u3lembi $p |- ( ( a ->3 b ) ^ ( b ->3 a ) ) = ( a == b ) $=
    ( i3bi ) ABC $.

  $( Non-tollens implication and biconditional.  (Contributed by NM,
     17-Jan-1998.) $)
  u4lembi $p |- ( ( a ->4 b ) ^ ( b ->4 a ) ) = ( a == b ) $=
    ( wi4 wa wn wo tb ud4lem1a dfb ax-r1 ax-r2 ) ABCBACDABDAEBEDFZABGZABHMLABIJ
    K $.

  $( Relevance implication and biconditional.  (Contributed by NM,
     17-Jan-1998.) $)
  u5lembi $p |- ( ( a ->5 b ) ^ ( b ->5 a ) ) = ( a == b ) $=
    ( wi5 wa wn wo tb u5lemc1b comcom com2an comcom2 wf ancom df-i5 ax-r2 anabs
    fh1 2an lan 2or u5lemc1 com2or ax-a3 u5lemanb u5lemaa an4 dff ax-r1 an0 or0
    anandi ax-a2 id dfb 3tr1 ) ABCZBADZBEZADZFZURAEZDZFZDZABDZVAURDZFZUPBACZDAB
    GVDUPUTDZUPVBDZFZVGUPUTVBUPUQUSUPBABUPABHIZAUPABUAIZJZUPURAUPBVLKZVMJZUBUPU
    RVAVOUPAVMKJQVKVGVGVIVEVJVFVIUPUQDZUPUSDZFZVEUPUQUSVNVPQVSVELFVEVQVEVRLVQUQ
    UPDZVEUPUQMVTVEVEVABDZVFFZFZDVEUQVEUPWCBAMUPVEWAFZVFFZWCABNZVEWAVFUCORVEWBP
    OOVRUPURDZUPADZDZLUPURAUKWIVFVEDZLWGVFWHVEABUDABUERWJVEVFDZLVFVEMWKAVADZBUR
    DZDZLABVAURUFWNWLLDLWMLWLLWMBUGUHSWLUIOOOOOTVEUJOOVJVBUPDZVFUPVBMWOVFVFWDFZ
    DVFVBVFUPWPURVAMUPWEWPWFWDVFULORVFWDPOOTVGUMOOVHVCUPBANSABUNUO $.

  $( Sasaki/Dishkant implication and biconditional.  Equation 4.14 of
     [MegPav2000] p. 23.  The variable i in the paper is set to 1, and j is set
     to 2.  (Contributed by NM, 2-Mar-2000.) $)
  u12lembi $p |- ( ( a ->1 b ) ^ ( b ->2 a ) ) = ( a == b ) $=
    ( wi1 wn wa wo wi2 tb u1lemc1 comcom lear leo df-i1 ax-r1 lbtr letr u1lemaa
    lecom fh1 lan an12 u1lemana ancom 3tr 2or ax-r2 df-i2 dfb 3tr1 ) ABCZABDZAD
    ZEZFZEZABEZULUKEZFZUJBAGZEABHUOUJAEZUJUMEZFURUJAUMAUJABIJUMUJUMUJUMULUJUKUL
    KULULUPFZUJULUPLUJVBABMNOPRJSUTUPVAUQABQVAUKUJULEZEUMUQUJUKULUAVCULUKABUBTU
    KULUCUDUEUFUSUNUJBAUGTABUHUI $.

  $( Dishkant/Sasaki implication and biconditional.  (Contributed by NM,
     3-Mar-2000.) $)
  u21lembi $p |- ( ( a ->2 b ) ^ ( b ->1 a ) ) = ( a == b ) $=
    ( wi2 wn wa wo wi1 u2lemc1 comcom3 comanr1 fh2 u2lemanb u2lemab anass ancom
    tb ran 3tr2 2or ax-a2 3tr df-i1 lan dfb 3tr1 ) ABCZBDZBAEZFZEZABEZADUGEZFZU
    FBAGZEABPUJUFUGEZUFUHEZFULUKFUMUGUFUHBUFABHIBUHBAJIKUOULUPUKABLUFBEZAEUHUPU
    KUQBAABMQUFBANBAORSULUKTUAUNUIUFBAUBUCABUDUE $.

  $( Commutation theorem for biimplication.  (Contributed by NM,
     19-Sep-1998.) $)
  ublemc1 $p |- a C ( a == b ) $=
    ( combi ) ABC $.

  $( Commutation theorem for biimplication.  (Contributed by NM,
     19-Sep-1998.) $)
  ublemc2 $p |- b C ( a == b ) $=
    ( tb ublemc1 bicom cbtr ) BBACABCBADBAEF $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Some proofs contributed by Josiah Burroughs
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( This theorem continues the line of proofs such as ~ u1lemnaa ,
     ~ ud1lem0b , ~ u1lemnanb , etc.  (Contributed by Josiah Burroughs,
     26-May-2004.) $)
  u1lemn1b $p |- ( a ->1 b ) = ( ( a ->1 b ) ' ->1 b ) $=
    ( wi1 wf wo wn wa ax-a1 u1lemnab ax-r1 2or or0 df-i1 3tr1 ) ABCZDEZOFZFZQBG
    ZEOQBCORDSOHSDABIJKPOOLJQBMN $.

  $( A 3-variable formula.  (Contributed by Josiah Burroughs, 26-May-2004.) $)
  u1lem3var1 $p |- ( ( ( a ->1 c ) ^ ( b ->1 c ) ) ' v
               ( ( ( a ->1 c ) ' ->1 c ) ^ ( ( b ->1 c ) ' ->1 c ) ) ) = 1 $=
    ( wi1 wa wn wo wt ax-a2 u1lemn1b 2an ax-r1 lor df-t 3tr1 ) ACDZBCDZEZFZRGRS
    GSPFCDZQFCDZEZGHSRIUBRSRUBPTQUAACJBCJKLMRNO $.

  ${
    oi3oa3lem1.1 $e |- 1 = ( b == a ) $.
    $( An attempt at the OA3 conjecture, which is true if ` ( a == b ) = 1 ` .
       (Contributed by Josiah Burroughs, 27-May-2004.) $)
    oi3oa3lem1 $p |- ( ( ( a ->1 c ) ^ ( b ->1 c ) ) v ( a ^ b ) ) = 1 $=
      ( wi1 wa wo wt r3a ud1lem0b lan 2or anidm u1lemoa 3tr ) ACEZBCEZFZABFZGPP
      FZAAFZGPAGHRTSUAQPPBACBADIZJKBAAUBKLTPUAAPMAMLACNO $.
  $}

  ${
    oi3oa3.1 $e |- 1 = ( b == a ) $.
    $( An attempt at the OA3 conjecture, which is true if ` ( a == b ) = 1 ` .
       (Contributed by Josiah Burroughs, 27-May-2004.) $)
    oi3oa3 $p |- ( ( ( a ->1 c ) ^ ( b ->1 c ) ) v
                  ( ( ( ( a ->1 c ) ^
                    ( ( ( a ->1 c ) ^ ( b ->1 c ) ) v ( a ^ b ) ) ) ->1 c ) ^
                    ( ( ( b ->1 c ) ^
                    ( ( ( a ->1 c ) ^ ( b ->1 c ) ) v ( a ^ b ) ) ) ->1 c )
                     ) ) = 1 $=
      ( wi1 wa wo oi3oa3lem1 lan an1 ax-r2 ud1lem0b 2an lor ax-a2 r3a 1bi 3tr
      wt ) ACEZBCEZFZTUBABFGZFZCEZUAUCFZCEZFZGUBTCEZUACEZFZGUKUBGSUHUKUBUEUIUGU
      JUDTCUDTSFTUCSTABCDHZITJKLUFUACUFUASFUAUCSUAULIUAJKLMNUBUKOTUACUATBACBADP
      LQHR $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        More lemmas for unified implication
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $(
  u1lem0 $p |- ( b ' ->1 a ' ) = ( a ->2 b ) $=
?$.

  u2lem0 $p |- ( b ' ->2 a ' ) = ( a ->1 b ) $=
?$.

  u3lem0 $p |- ( b ' ->3 a ' ) = ( a ->4 b ) $=
?$.

  u4lem0 $p |- ( b ' ->4 a ' ) = ( a ->3 b ) $=
?$.

  u5lem0 $p |- ( b ' ->5 a ' ) = ( a ->5 b ) $=
?$.
  $)

  $( Lemma for unified implication study.  (Contributed by NM, 14-Dec-1997.) $)
  u1lem1 $p |- ( ( a ->1 b ) ->1 a ) = a $=
    ( wi1 wn wo u1lemc1 comcom u1lemc4 u1lemnoa ax-r2 ) ABCZACKDAEAKAAKABFGHABI
    J $.

  $( Lemma for unified implication study.  (Contributed by NM, 14-Dec-1997.) $)
  u2lem1 $p |- ( ( a ->2 b ) ->2 a ) = a $=
    ( wi2 wn wa wo df-i2 wf ud2lem0c ran an32 ax-a2 ax-r2 lan dff ax-r1 lor or0
    oran ) ABCZACATDZADZEZFZATAGUDAHFAUCHAUCBDZABFZEZUBEZHUAUGUBABIJUHUEUBEZUFE
    ZHUEUFUBKUJUIUIDZEZHUFUKUIUFBAFUKABLBASMNHULUIOPMMMQARMM $.

  $( Lemma for unified implication study.  (Contributed by NM, 14-Dec-1997.) $)
  u3lem1 $p |- ( ( a ->3 b ) ->3 a ) = ( ( a v b ) ^ ( a v b ' ) ) $=
    ( wi3 wn wo wa comi31 comcom u3lemc4 u3lemnoa ax-r2 ) ABCZACLDAEABEABDEFLAA
    LABGHIABJK $.

  $( Lemma for unified implication study.  (Contributed by NM, 16-Dec-1997.) $)
  u4lem1 $p |- ( ( a ->4 b ) ->4 a ) =
          ( ( ( ( a ^ b ) v ( a ^ b ' ) ) v a ' ) ^
          ( ( a v b ) ^ ( a v b ' ) ) ) $=
    ( wi4 wa wn wo u4lemaa 2or comanr1 com2or comcom3 comorr com2an fh4 lea leo
    df-i4 letr df-le2 ax-r2 u4lemnaa ran ancom lor comor1 comor2 comcom2 lel2or
    u4lemnoa 2an lan id ) ABCZACUMADZUMEZADZFZUOAFZAEZDZFZABDZABEZDZFZUSFZABFZA
    VCFZDZDZUMAQVAVEVIUSDZFZVJUQVEUTVKUNVBUPVDABGABUAHURVIUSABUIUBHVLVEUSVIDZFZ
    VJVKVMVEVIUSUCUDVNVFVEVIFZDZVJUSVEVIAVEAVBVDABIAVCIJKAVIAVGVHABLAVCLMKNVPVJ
    VJVOVIVFVOVEVGFZVEVHFZDVIVGVEVHVGVBVDVGABABUEZABUFZMVGAVCVSVGBVTUGZMJVGAVCV
    SWAJNVQVGVRVHVEVGVEAVGVBAVDABOAVCOUHZABPRSVEVHVEAVHWBAVCPRSUJTUKVJULTTTTT
    $.

  $( Lemma for unified implication study.  (Contributed by NM, 16-Dec-1997.) $)
  u5lem1 $p |- ( ( a ->5 b ) ->5 a ) = ( ( a v b ) ^ ( a v b ' ) ) $=
    ( wi5 wn wo wa u5lemc1 comcom u5lemc4 u5lemnoa ax-r2 ) ABCZACLDAEABEABDEFLA
    ALABGHIABJK $.

  $( Lemma for unified implication study.  (Contributed by NM, 16-Dec-1997.) $)
  u1lem1n $p |- ( ( a ->1 b ) ->1 a ) ' = a ' $=
    ( wi1 u1lem1 ax-r4 ) ABCACAABDE $.

  $( Lemma for unified implication study.  (Contributed by NM, 16-Dec-1997.) $)
  u2lem1n $p |- ( ( a ->2 b ) ->2 a ) ' = a ' $=
    ( wi2 u2lem1 ax-r4 ) ABCACAABDE $.

  $( Lemma for unified implication study.  (Contributed by NM, 16-Dec-1997.) $)
  u3lem1n $p |- ( ( a ->3 b ) ->3 a ) ' =
                ( ( a ' ^ b ) v ( a ' ^ b ' ) ) $=
    ( wi3 wn wa wo u3lem1 ancom df-a anor2 anor3 2or ax-r4 ax-r1 ax-r2 con2 ) A
    BCACZADZBEZRBDZEZFZQABFZATFZEZUBDZABGUEUDUCEZUFUCUDHUGUDDZUCDZFZDZUFUDUCIUF
    UKUBUJSUHUAUIABJABKLMNOOOP $.

  $( Lemma for unified implication study.  (Contributed by NM, 16-Dec-1997.) $)
  u4lem1n $p |- ( ( a ->4 b ) ->4 a ) ' =
          ( ( ( ( a ' v b ) ^ ( a ' v b ' ) ) ^ a ) v
          ( ( a ' ^ b ) v ( a ' ^ b ' ) ) ) $=
    ( wa wn wo wi4 oran1 df-a anor1 2or ax-r4 ax-r1 ax-r2 ancom ran anor2 anor3
    2an u4lem1 oran 3tr1 ) ABCZABDZCZEZADZEZABEZAUCEZCZCZDUFBEZUFUCEZCZACZDZUFB
    CZUFUCCZEZDZCZDABFAFZDUOUSEUKVAUGUPUJUTUGUEDZACZDUPUEAGVDUOVCUNAVCUMULCZUNV
    CUMDZULDZEZDZVEUEVHUBVFUDVGABHABIJKVEVIUMULHLMUMULNMOKMUJUIUHCZUTUHUINVJUID
    ZUHDZEZDZUTUIUHHUTVNUSVMUQVKURVLABPABQJKLMMRKVBUKABSKUOUSTUA $.

  $( Lemma for unified implication study.  (Contributed by NM, 16-Dec-1997.) $)
  u5lem1n $p |- ( ( a ->5 b ) ->5 a ) ' =
                ( ( a ' ^ b ) v ( a ' ^ b ' ) ) $=
    ( wi5 wn wa wo u5lem1 ancom df-a anor2 anor3 2or ax-r4 ax-r1 ax-r2 con2 ) A
    BCACZADZBEZRBDZEZFZQABFZATFZEZUBDZABGUEUDUCEZUFUCUDHUGUDDZUCDZFZDZUFUDUCIUF
    UKUBUJSUHUAUIABJABKLMNOOOP $.

  $( Lemma for unified implication study.  (Contributed by NM, 16-Dec-1997.) $)
  u1lem2 $p |- ( ( ( a ->1 b ) ->1 a ) ->1 a ) = 1 $=
    ( wi1 wn wa wo wt df-i1 u1lem1n u1lem1 ran anidm ax-r2 2or ax-a2 df-t ax-r1
    ) ABCACZACRDZRAEZFZGRAHUAADZAFZGSUBTAABITAAEARAAABJKALMNUCAUBFZGUBAOGUDAPQM
    MM $.

  $( Lemma for unified implication study.  (Contributed by NM, 16-Dec-1997.) $)
  u2lem2 $p |- ( ( ( a ->2 b ) ->2 a ) ->2 a ) = 1 $=
    ( wi2 wn wa wo wt df-i2 u2lem1n ran anidm ax-r2 lor df-t ax-r1 ) ABCACZACAP
    DZADZEZFZGPAHTARFZGSRASRRERQRRABIJRKLMGUAANOLL $.

  $( Lemma for unified implication study.  (Contributed by NM, 24-Dec-1997.) $)
  u3lem2 $p |- ( ( ( a ->3 b ) ->3 a ) ->3 a ) =
               ( a v ( ( a ' ^ b ) v ( a ' ^ b ' ) ) ) $=
    ( wi3 wn wo comi31 comid u3lemc2 comcom u3lemc4 u3lem1n ax-r5 ax-a2 ax-r2
    wa ) ABCZACZACQDZAEZAADZBOTBDOEZEZQAAQAPAABFAGHIJSUAAEUBRUAAABKLUAAMNN $.

  $( Lemma for unified implication study.  (Contributed by NM, 24-Dec-1997.) $)
  u4lem2 $p |- ( ( ( a ->4 b ) ->4 a ) ->4 a ) =
               ( a v ( ( a ' ^ b ) v ( a ' ^ b ' ) ) ) $=
    ( wn wo wa u4lemc1 comcom u4lemc4 u4lem1n ax-r5 ax-a3 lear leor letr df-le2
    wi4 ax-a2 ax-r2 ) ABPZAPZAPTCZADZAACZBEUCBCZEDZDZTAATSAFGHUBUCBDUCUDDEZAEZU
    EDZADZUFUAUIAABIJUJUHUEADZDZUFUHUEAKULUKUFUHUKUHAUKUGALAUEMNOUEAQRRRR $.

  $( Lemma for unified implication study.  (Contributed by NM, 24-Dec-1997.) $)
  u5lem2 $p |- ( ( ( a ->5 b ) ->5 a ) ->5 a ) =
               ( a v ( ( a ' ^ b ) v ( a ' ^ b ' ) ) ) $=
    ( wi5 wn wo wa u5lemc1b comcom u5lemc4 u5lem1n ax-r5 ax-a2 ax-r2 ) ABCZACZA
    CODZAEZAADZBFRBDFEZEZOAAONAGHIQSAETPSAABJKSALMM $.

  $( Lemma for unified implication study.  (Contributed by NM, 17-Dec-1997.) $)
  u1lem3 $p |- ( a ->1 ( b ->1 a ) ) =
               ( a ' v ( ( a ^ b ) v ( a ^ b ' ) ) ) $=
    ( wi1 wn wa wo df-i1 ancom 2or u1lemab ax-r1 ax-r2 lor id ) ABACZCADZAOEZFZ
    PABEZABDZEZFZFZAOGRUCUCQUBPUBQUBOAEZQUBBAEZTAEZFZUDSUEUAUFABHATHIUDUGBAJKLO
    AHLKMUCNLL $.

  $( Lemma for unified implication study.  (Contributed by NM, 17-Dec-1997.) $)
  u2lem3 $p |- ( a ->2 ( b ->2 a ) ) = 1 $=
    ( wi2 wn wa wo wt df-i2 u2lemc1 comcom3 comcom4 fh4 u2lemonb df-t ax-r1 2an
    an1 ax-r2 ) ABACZCSADZSDZEFZGASHUBSTFZSUAFZEZGTSUAASBAIZJASUFKLUEGGEGUCGUDG
    BAMGUDSNOPGQRRR $.

  $( Lemma for unified implication study.  (Contributed by NM, 17-Dec-1997.) $)
  u3lem3 $p |- ( a ->3 ( b ->3 a ) ) =
               ( a v ( ( a ' ^ b ) v ( a ' ^ b ' ) ) ) $=
    ( wi3 wn wa df-i3 ancom u3lemanb ax-r2 u3lemnanb 2or ax-a2 u3lemonb lan an1
    wo wt ) ABACZCADZREZSRDZEZPZASRPZEZPZASBEZSBDZEZPZPZARFUFUJAPUKUCUJUEAUCUHS
    EZBSEZPZUJTULUBUMTRSEULSRGBAHIUBUASEUMSUAGBAJIKUNUIUGPUJULUIUMUGUHSGBSGKUIU
    GLIIUEAQEAUDQAUDRSPQSRLBAMINAOIKUJALII $.

  $( Lemma for unified implication study.  (Contributed by NM, 17-Dec-1997.) $)
  u4lem3 $p |- ( a ->4 ( b ->4 a ) ) =
               ( a ' v ( ( a ^ b ) v ( a ^ b ' ) ) ) $=
    ( wi4 wn wo wa u4lemc1 u4lemc4 ax-a2 u4lemonb ancom 2or ax-r5 ax-r2 ) ABACZ
    CADZOEZPABFZABDZFZEZEZAOBAGHQOPEZUBPOIUCBAFZSAFZEZPEZUBBAJUGUAPEUBUFUAPUDRU
    ETBAKSAKLMUAPINNNN $.

  $( Lemma for unified implication study.  (Contributed by NM, 17-Dec-1997.) $)
  u5lem3 $p |- ( a ->5 ( b ->5 a ) ) =
               ( a ' v ( ( a ^ b ) v ( a ^ b ' ) ) ) $=
    ( wi5 wn wo wa u5lemc1b u5lemc4 ax-a2 u5lemonb ancom 2or ax-r5 ax-r2 ) ABAC
    ZCADZOEZPABFZABDZFZEZEZAOBAGHQOPEZUBPOIUCBAFZSAFZEZPEZUBBAJUGUAPEUBUFUAPUDR
    UETBAKSAKLMUAPINNNN $.

  $( Lemma for unified implication study.  (Contributed by NM, 17-Dec-1997.) $)
  u3lem3n $p |- ( a ->3 ( b ->3 a ) ) ' =
               ( a ' ^ ( ( a v b ) ^ ( a v b ' ) ) ) $=
    ( wi3 wn wo wa u3lem3 ax-a2 anor3 anor2 2or oran3 ax-r2 lor oran1 con2 ) AB
    ACCZADZABEZABDZEZFZFZQARBFZRTFZEZEZUCDZABGUGAUBDZEUHUFUIAUFUEUDEZUIUDUEHUJS
    DZUADZEUIUEUKUDULABIABJKSUALMMNAUBOMMP $.

  $( Lemma for unified implication study.  (Contributed by NM, 17-Dec-1997.) $)
  u4lem3n $p |- ( a ->4 ( b ->4 a ) ) ' =
               ( a ^ ( ( a ' v b ) ^ ( a ' v b ' ) ) ) $=
    ( wi4 wn wo wa u4lem3 ax-a2 anor1 df-a 2or oran3 ax-r2 lor con2 ) ABACCZAAD
    ZBEZQBDZEZFZFZPQABFZASFZEZEZUBDZABGUFQUADZEUGUEUHQUEUDUCEZUHUCUDHUIRDZTDZEU
    HUDUJUCUKABIABJKRTLMMNAUALMMO $.

  $( Lemma for unified implication study.  (Contributed by NM, 17-Dec-1997.) $)
  u5lem3n $p |- ( a ->5 ( b ->5 a ) ) ' =
               ( a ^ ( ( a ' v b ) ^ ( a ' v b ' ) ) ) $=
    ( wi5 wn wo wa u5lem3 ax-a2 anor1 df-a 2or oran3 ax-r2 lor con2 ) ABACCZAAD
    ZBEZQBDZEZFZFZPQABFZASFZEZEZUBDZABGUFQUADZEUGUEUHQUEUDUCEZUHUCUDHUIRDZTDZEU
    HUDUJUCUKABIABJKRTLMMNAUALMMO $.

  $( Lemma for unified implication study.  (Contributed by NM, 11-Jan-1998.) $)
  u1lem4 $p |- ( a ->1 ( a ->1 ( b ->1 a ) ) ) = ( a ->1 ( b ->1 a ) ) $=
    ( wi1 wn wa wo df-i1 comid comcom2 u1lemc1 fh4 wt ax-a2 df-t ax-r1 u1lemona
    ax-r2 ancom lor lan u1lem3 coman1 coman2 fh2 anass anidm ran ax-r5 2an an1
    ) AABACZCZCADZAULEFZULAULGUNUMAFZUMULFZEZULAUMULAAAHIAUKJKUQLULEZULUOLUPULU
    OAUMFZLUMAMLUSANOQUPULUMFZULUMULMUTUMAUKEZFZULAUKPVBUMABDZABEZFZEZFZULVAVFU
    MUKVEAUKVCBAEZFVEBAGVHVDVCBARSQTSULVGULUMVDAVCEZFZFVGABUAVJVFUMVFVJVFAVDVCF
    ZEZVJVEVKAVCVDMTVLAVDEZVIFVJVDAVCABUBVDBABUCIUDVMVDVIVMAAEZBEZVDVOVMAABUEOV
    NABAUFUGQUHQQOSQOQQQUIURULLEULLULRULUJQQQQ $.

  $( Lemma for unified implication study.  (Contributed by NM, 21-Jan-1998.) $)
  u3lem4 $p |- ( a ->3 ( a ->3 ( b ->3 a ) ) ) = 1 $=
    ( wi3 wn wo wt lem4 ax-a2 u3lemonb ax-r2 ) AABACZCCADZKEZFAKGMKLEFLKHBAIJJ
    $.

  $( Lemma for unified implication study.  (Contributed by NM, 18-Dec-1997.) $)
  u4lem4 $p |- ( a ->4 ( a ->4 ( b ->4 a ) ) ) = ( a ->4 ( b ->4 a ) ) $=
    ( wi4 wa wn wo df-i4 comid comcom2 comanr1 com2or comcom ax-r1 df-t lan an1
    wt ax-r2 wf ax-r5 u4lem3 bctr fh2r comcom4 comcom3 fh1r dff lor or0 2or fh3
    ancom or32 oridm ) AABACCZCAUODAEZUODFZUPUOFUOEZDZFZUOAUOGUTUOUPURDZFZUOUQU
    OUSVAUQAUPFZUODZUOVDUQAUOUPUOAUOUPABDZABEZDZFZFZAABUAZAVIAUPVHAAAHIZAVEVGAB
    JAVFJKKLUBZLVKUCMVDUOVCDZUOVCUOULVMUOQDUOVCQUOQVCANMOUOPRRRUSVAUOURDZFZVAUR
    UPUOUOAVLUDUOUOUOHZUEUFVOVASFVAVNSVASVNUOUGMUHVAUIRRUJVBUOUPFZUOVBVQUOURFZD
    ZVQUOUPURUOAVLIUOUOVPIUKVSVQQDVQVRQVQQVRUONMOVQPRRVQVIUPFZUOUOVIUPVJTVTUPUP
    FZVHFZUOUPVHUPUMWBVIUOWAUPVHUPUNTUOVIVJMRRRRRR $.

  $( Lemma for unified implication study.  (Contributed by NM, 24-Dec-1997.) $)
  u5lem4 $p |- ( a ->5 ( a ->5 ( b ->5 a ) ) ) = ( a ->5 ( b ->5 a ) ) $=
    ( wi5 wn wo u5lemc1 u5lemc4 wa u5lem3 lor ax-a3 ax-r1 oridm ax-r5 ax-r2 ) A
    ABACZCZCADZQEZQAQAPFGSRRABHABDHEZEZEZQQUARABIZJUBRREZTEZQUEUBRRTKLUEUAQUDRT
    RMNQUAUCLOOOO $.

  $( Lemma for unified implication study.  (Contributed by NM, 20-Dec-1997.) $)
  u1lem5 $p |- ( a ->1 ( a ->1 b ) ) = ( a ->1 b ) $=
    ( wi1 wn wa wo df-i1 ancom u1lemaa ax-r2 lor ax-r1 ) AABCZCADZAMEZFZMAMGPNA
    BEZFZMOQNOMAEQAMHABIJKMRABGLJJ $.

  $( Lemma for unified implication study.  (Contributed by NM, 20-Dec-1997.) $)
  u2lem5 $p |- ( a ->2 ( a ->2 b ) ) = ( a ->2 b ) $=
    ( wi2 wn wa wo df-i2 wf ancom u2lemnana ax-r2 lor or0 ) AABCZCNADZNDZEZFZNA
    NGRNHFNQHNQPOEHOPIABJKLNMKK $.

  $( Lemma for unified implication study.  (Contributed by NM, 24-Dec-1997.) $)
  u3lem5 $p |- ( a ->3 ( a ->3 b ) ) = ( a ' v b ) $=
    ( wi3 wn wo comi31 u3lemc4 ax-a2 u3lemona ax-r2 ) AABCZCADZKEZLBEZAKABFGMKL
    ENLKHABIJJ $.

  $( Lemma for unified implication study.  (Contributed by NM, 26-Dec-1997.) $)
  u4lem5 $p |- ( a ->4 ( a ->4 b ) ) = ( ( a ' ^ b ' ) v b ) $=
    ( wi4 wa wn wo ancom ax-r2 2or ax-a3 ax-r1 ax-a2 2an comcom7 com2an comanr2
    wf com2or wt lor df-i4 u4lemaa u4lemana u4lemona ud4lem0c anass comor1 fh1r
    comor2 comcom2 leor df2le2 lan dff or0 comcom6 comorr2 fh4 or32 lear lel2or
    oran2 df-le2 ax-r5 or4 oran3 df-t or1 oran1 an1 ) AABCZCAVKDZAEZVKDZFZVMVKF
    ZVKEZDZFZVMBEZDZBFZAVKUAVSABDZVMBDZFZWAFZBVMVTFZAVTFZDZDZFZWBVOWFVRWJVOWCWD
    WAFZFZWFVLWCVNWLVLVKADWCAVKGABUBHVNVKVMDWLVMVKGABUCHIWFWMWCWDWAJKHVRVMBFZWI
    AVTDZBFZDZDZWJVPWNVQWQVPVKVMFWNVMVKLABUDHABUEMWRWQWNDZWJWNWQGWSWIWPWNDZDZWJ
    WIWPWNUFXAWIBDWJWTBWIWTWOWNDZBWNDZFZBWNWOBWNAVTWNAVMBUGNWNBVMBUIZUJOXEUHXDX
    CXBFZBXBXCLXFBQFBXCBXBQBWNBVMUKULXBWOWOEZDZQWNXGWOABVBUMQXHWOUNKHIBUOHHHUMW
    IBGHHHHIWKWFBFZWFWIFZDZWBBWFWIBWEWABWCWDABPVMBPRBWAVMVTPUPRBWIVTWGWHVMVTUQA
    VTUQOUPURXKBWAFZSDZWBXIXLXJSXIWEBFZWAFXLWEWABUSXNBWAWEBWCBWDABUTVMBUTVAVCVD
    HXJWFWGFZWFWHFZDZSWGWFWHWGWEWAWGWCWDWGABWGAVMVTUGZNZWGBVMVTUIZNZOWGVMBXRYAO
    RWGVMVTXRXTORWGAVTXSXTRURXQSSDSXOSXPSXOWEWGFWAFZSWEWAWGUSYBWEWGWAFFZSWEWGWA
    JYCWCWGFZWLFZSWCWDWGWAVEYEWLYDFZSYDWLLYFWLSFSYDSWLYDWCWCEZFZSWGYGWCABVFTSYH
    WCVGKHTWLVHHHHHHXPWEWAWHFFZSWEWAWHJYIWCWAFZWDWHFZFZSWCWDWAWHVEYLYJSFSYKSYJY
    KWDWDEZFZSWHYMWDABVITSYNWDVGKHTYJVHHHHMSVJHHMXMXLWBXLVJBWALHHHHH $.

  $( Lemma for unified implication study.  (Contributed by NM, 20-Dec-1997.) $)
  u5lem5 $p |- ( a ->5 ( a ->5 b ) ) = ( a ' v ( a ^ b ) ) $=
    ( wi5 wa wn wo df-i5 u5lemc1 comcom comcom2 fh1r ax-r1 ancom df-t lan ax-r2
    wt an1 ax-r5 comcom3 comcom4 fh4 u5lemona ) AABCZCAUDDAEZUDDFZUEUDEZDZFZUEA
    BDFZAUDGUIUDUHFZUJUFUDUHUFAUEFZUDDZUDUMUFUDAUEAUDABHZIZUDAUOJKLUMUDULDZUDUL
    UDMUPUDQDUDULQUDQULANLOUDRPPPSUKUDUEFZUDUGFZDZUJUEUDUGAUDUNTAUDUNUAUBUSUQQD
    ZUJURQUQQURUDNLOUTUQUJUQRABUCPPPPP $.

  $( Lemma for unified implication study.  (Contributed by NM, 20-Dec-1997.) $)
  u4lem5n $p |- ( a ->4 ( a ->4 b ) ) ' = ( ( a v b ) ^ b ' ) $=
    ( wi4 wo wn wa u4lem5 anor3 ax-r5 ax-r2 oran2 con2 ) AABCCZABDZBEZFZMNEZBDZ
    PEMAEOFZBDRABGSQBABHIJNBKJL $.

  $( Lemma for unified implication study.  (Contributed by NM, 24-Dec-1997.) $)
  u3lem6 $p |- ( a ->3 ( a ->3 ( a ->3 b ) ) ) = ( a ->3 ( a ->3 b ) ) $=
    ( wi3 wn wo comi31 u3lemc4 u3lem5 lor ax-a3 ax-r1 oridm ax-r5 ax-r2 ) AAABC
    ZCZCADZPEZPAPAOFGRQQBEZEZPPSQABHZITQQEZBEZPUCTQQBJKUCSPUBQBQLMPSUAKNNNN $.

  $( Lemma for unified implication study.  (Contributed by NM, 26-Dec-1997.) $)
  u4lem6 $p |- ( a ->4 ( a ->4 ( a ->4 b ) ) ) = ( a ->4 b ) $=
    ( wi4 wa wn wo lan comcom7 fh2 ax-a2 ancom ax-r1 ax-r2 lor ax-r5 2an com2an
    wf wt com2or df-i4 u4lem5 coman1 coman2 anass dff an0 3tr2 or0 anidm ran id
    2or or12 comor1 comcom2 fh3r ax-a3 oridm df-t or1 an1 u4lem5n fh4 lear leor
    comor2 letr lea lel2or leo df-le2 or32 anor3 comorr2 comcom3 comanr2 df2le2
    3tr1 ) AAABCZCZCAWADZAEZWADZFZWCWAFZWAEZDZFZVTAWAUAWIABDZWCBEZDZWCBDZFZFZWC
    BFZABFZWKDZDZFZVTWEWOWHWSWEWOWOWBWJWDWNWBAWLBFZDZWJWAXAAABUBZGXBAWLDZWJFZWJ
    WLABWLAWCWKUCZHWLBWCWKUDHZIXEWJXDFZWJXDWJJXHWJRFWJXDRWJAWCDZWKDWKXIDZXDRXIW
    KKAWCWKUEXJWKRDRXIRWKRXIAUFLGWKUGMUHNWJUIMMMMWDWCXADZWNWAXAWCXCGXKWCWLDZWMF
    WNWLWCBXFXGIXLWLWMXLWCWCDZWKDZWLXNXLWCWCWKUELXMWCWKWCUJUKMOMMUMWOULMWHWSWSW
    FWPWGWRWFWCXAFZWPWAXAWCXCNXOWLWPFZWPWCWLBUNXPWCWPFZWKWPFZDZWPWPWCWKWCBUOZWP
    BWCBVGZUPZUQXSWPSDWPXQWPXRSXQWCWCFZBFZWPYDXQWCWCBURLYCWCBWCUSOMXRWCWKBFZFZS
    WKWCBUNYFWCSFSYESWCYEBWKFZSWKBJSYGBUTLMNWCVAMMPWPVBMMMMABVCPWSULMUMWTWOWPFZ
    WOWRFZDZVTWPWOWRWPWJWNWPABWPAXTHZYAQWPWLWMWPWCWKXTYBQWPWCBXTYAQTTWPWQWKWPAB
    YKYATYBQVDYJWPWKWJWMFZFZDZVTYHWPYIYMWOWPWJWPWNWJBWPABVEZBWCVFZVHWNWCWPWLWCW
    MWCWKVIWCBVIVJWCBVKVHVJVLYIWOWQFZWOWKFZDZYMWQWOWKWQWJWNWQABABUOZABVGZQWQWLW
    MWQWCWKWQAYTUPZWQBUUAUPZQWQWCBUUBUUAQTTUUCVDYSSYMDZYMYQSYRYMYQWJWQFZWNFZSWJ
    WNWQVMUUEWLFZWMFSWMFZUUFSUUGSWMUUGWJWQWLFZFZSWJWQWLURUUJWJSFSUUISWJUUIWQWQE
    ZFZSWLUUKWQABVNNSUULWQUTLMNWJVAMMOUUEWLWMURUUHWMSFSSWMJWMVAMUHMYRWLYLFZWKFZ
    YMWOUUMWKWJWLWMUNOWLWKFZYLFYMUUNYMUUOWKYLWLWKWCWKVEVLOWLYLWKVMYMULVSMPUUDYM
    SDYMSYMKYMVBMMMPYNWPWKDZWPYLDZFZVTWKWPYLBWPWCBVOVPBYLBWJWMABVQWCBVQTVPIUUPY
    LFYLUUPFUURVTUUPYLJUUQYLUUPUUQYLWPDYLWPYLKYLWPYLBWPWJBWMYOWCBVEVJYPVHVRMNAB
    UAVSMMMMM $.

  $( Lemma for unified implication study.  (Contributed by NM, 20-Dec-1997.) $)
  u5lem6 $p |- ( a ->5 ( a ->5 ( a ->5 b ) ) ) = ( a ->5 ( a ->5 b ) ) $=
    ( wi5 wa wn wo df-i5 ancom u5lemc1 comcom comcom2 fh1r df-t ax-r1 lan ax-r2
    wt an1 3tr2 ax-r5 comcom3 comcom4 fh4 u5lem5 oridm or32 3tr1 ) AAABCZCZCAUI
    DAEZUIDFZUJUIEZDZFZUIAUIGUNUIUMFZUIUKUIUMAUJFZUIDUIUPDZUKUIUPUIHUIAUJAUIAUH
    IZJZUIAUSKLUQUIQDUIUPQUIQUPAMNOUIRPSTUOUIUJFZUIULFZDZUIUJUIULAUIURUAAUIURUB
    UCVBUTQDZUIVAQUTQVAUIMNOVCUTUIUTRUTUJABDZFZUJFZUIUIVEUJABUDZTUJUJFZVDFVEVFU
    IVHUJVDUJUETUJVDUJUFVGUGPPPPPP $.

  $( Lemma for unified implication study.  (Contributed by NM, 20-Dec-1997.) $)
  u24lem $p |- ( ( a ->2 b ) ^ ( a ->4 b ) ) = ( a ->5 b ) $=
    ( wi2 wi4 wa wn wo wi5 df-i2 u4lemc1 comanr2 comcom6 fh2r ancom ax-r2 anass
    ran ax-r1 2or id u4lemanb lan anabs comanr1 com2or fh1 u4lemab ax-r5 df2le2
    fh4r leor ax-a3 lear df-le2 lor df-i5 ) ABCZABDZEBAFZBFZEZGZUREZABHZUQVBURA
    BIQVCBUREZVAUREZGZVDBURVAABJZBVAUSUTKLMVGVEUTUSEZGZVDVEVEVFVIVEURBEZVEBURNZ
    URBNOVFUSUTUREZEZVIUSUTURPVNUSUSBGZUTEZEZVIVMVPUSVMURUTEVPUTURNABUAOUBVQUSV
    OEZUTEZVIVSVQUSVOUTPRVSVAVIVRUSUTUSBUCQUSUTNOOOOSVJBVIGURVIGZEZVDBVIURBVIUT
    USUDLZVHUJWABVTEZVIVTEZGZVDBVTVIBURVIVHWBUEWBMWEABEUSBEGZBVIEZGZVIGZVDWCWHW
    DVIWCVEWGGZWHBURVIVHWBUFWJWHWHVEWFWGVEVKWFVLABUGOUHWHTOOVIVTVIURUKUISWIWFWG
    VIGZGZVDWFWGVIULWLWFVAGZVDWKVAWFWKVIVAWGVIBVIUMUNUTUSNOUOWMVDVDVDWMABUPRVDT
    OOOOOOOOO $.

  $( Implication lemma.  (Contributed by NM, 17-Nov-1998.) $)
  u12lem $p |- ( ( a ->1 b ) v ( a ->2 b ) ) = ( a ->0 b ) $=
    ( wi1 wn wa wo wi2 wi0 orordi u1lemob df-i1 ax-r5 or32 orabs ax-r2 2or bile
    id lear lelor lel2or leo lebi df-i2 lor df-i0 3tr1 ) ABCZBADZBDZEZFZFZUIBFZ
    UHABGZFABHUMUHBFZUHUKFZFZUNUHBUKIURUNUIABEZFZFZUNUPUNUQUTABJUQUTUKFZUTUHUTU
    KABKLVBUIUKFZUSFUTUIUSUKMVCUIUSUIUJNLOOPVAUNUNUNUTUNUNUNRQUSBUIABSTUAUNUTUB
    UCOOUOULUHABUDUEABUFUG $.

  $( Lemma for unified implication study.  (Contributed by NM, 24-Dec-1997.) $)
  u1lem7 $p |- ( a ->1 ( a ' ->1 b ) ) = 1 $=
    ( wn wi1 wa wo wt df-i1 ax-a1 ran ancom u1lemana ax-r2 lor df-t ax-r1 ) AAC
    ZBDZDQAREZFZGARHTQQCZFZGSUAQSUAREZUAAUARAIJUCRUAEUAUARKQBLMMNGUBQOPMM $.

  $( Lemma for unified implication study.  (Contributed by NM, 24-Dec-1997.) $)
  u2lem7 $p |- ( a ->2 ( a ' ->2 b ) ) =
              ( ( ( a ^ b ' ) v ( a ' ^ b ' ) ) v b ) $=
    ( wn wi2 wa df-i2 ax-a1 ax-r1 ran lor ax-r2 ancom u2lemnaa 2or ax-a3 ax-a2
    wo ) AACZBDZDSRSCZEZQZABCZEZRUCEZQZBQZASFUBBUDQZUEQZUGSUHUAUESBRCZUCEZQUHRB
    FUKUDBUJAUCAUJAGHIJKUATREUERTLRBMKNUIBUFQUGBUDUEOBUFPKKK $.

  $( Lemma for unified implication study.  (Contributed by NM, 24-Dec-1997.) $)
  u3lem7 $p |- ( a ->3 ( a ' ->3 b ) ) =
              ( a ' v ( ( a ^ b ) v ( a ^ b ' ) ) ) $=
    ( wn wi3 wo comi31 comcom6 u3lemc4 df-i3 lor or12 ax-a1 ran 2or ax-r1 orabs
    wa ax-a2 ax-r2 ) AACZBDZDTUAEZTABQZABCZQZEZEZAUAAUATBFGHUBTTCZBQZUHUDQZEZTU
    HBEZQZEZEZUGUAUNTTBIJUOUKTUMEZEZUGTUKUMKUQUFTEUGUKUFUPTUFUKUCUIUEUJAUHBALZM
    AUHUDURMNOTULPNUFTRSSSS $.

  $( Lemma for unified implication study.  (Contributed by NM, 24-Dec-1997.) $)
  u2lem7n $p |- ( a ->2 ( a ' ->2 b ) ) ' =
              ( ( ( a v b ) ^ ( a ' v b ) ) ^ b ' ) $=
    ( wn wi2 wo wa u2lem7 ax-a2 anor3 anor1 2or ax-r2 oran3 ax-r5 oran2 con2 )
    AACZBDDZABEZQBEZFZBCZFZRAUBFZQUBFZEZBEZUCCZABGUGUACZBEUHUFUIBUFSCZTCZEZUIUF
    UEUDEULUDUEHUEUJUDUKABIABJKLSTMLNUABOLLP $.

  $( Lemma used in study of orthoarguesian law.  (Contributed by NM,
     27-Dec-1998.) $)
  u1lem8 $p |- ( ( a ->1 b ) ^ ( a ' ->1 b ) ) =
               ( ( a ^ b ) v ( a ' ^ b ) ) $=
    ( wi1 wn wa df-i1 ax-a1 ax-r5 ax-r1 2an comor1 comcom2 coman1 coman2 com2an
    wo ax-r2 com2or comcom fh1r omlan lea leo letr df2le2 2or ax-a2 3tr ) ABCZA
    DZBCZEUJABEZPZAUJBEZPZEUJUOEZULUOEZPZULUNPZUIUMUKUOABFUKUJDZUNPZUOUJBFUOVAA
    UTUNAGHIQJUOUJULUOAAUNKLULUOULAUNABMZULUJBULAVBLABNORSTURUNULPUSUPUNUQULABU
    AULUOULAUOABUBAUNUCUDUEUFUNULUGQUH $.

  $( Lemma used in study of orthoarguesian law.  Equation 4.11 of [MegPav2000]
     p. 23.  This is the first part of the inequality.  (Contributed by NM,
     28-Dec-1998.) $)
  u1lem9a $p |- ( a ' ->1 b ) ' =< a ' $=
    ( wn wi1 wa wo df-i1 ax-r4 anor1 ax-r1 ax-r2 lea bltr ) ACZBDZCZNNBEZCZEZNP
    NCQFZCZSOTNBGHSUANQIJKNRLM $.

  $( Lemma used in study of orthoarguesian law.  Equation 4.11 of [MegPav2000]
     p. 23.  This is the second part of the inequality.  (Contributed by NM,
     27-Dec-1998.) $)
  u1lem9b $p |- a ' =< ( a ->1 b ) $=
    ( wn wa wo wi1 leo df-i1 ax-r1 lbtr ) ACZKABDZEZABFZKLGNMABHIJ $.

  $( Lemma used in study of orthoarguesian law.  (Contributed by NM,
     27-Dec-1998.) $)
  u1lem9ab $p |- ( a ' ->1 b ) ' =< ( a ->1 b ) $=
    ( wn wi1 u1lem9a u1lem9b letr ) ACZBDCHABDABEABFG $.

  $( Lemma used in study of orthoarguesian law.  (Contributed by NM,
     28-Dec-1998.) $)
  u1lem11 $p |- ( ( a ' ->1 b ) ->1 b ) = ( a ->1 b ) $=
    ( wn wi1 wa ud1lem0c ax-a1 ax-r1 ax-r5 lan 3tr comanr1 com2or comcom com2an
    wo ax-r2 wt lor df-i1 u1lemab ran 2or comcom3 comor1 comor2 comcom7 comcom2
    ax-a2 fh3r or32 ax-a3 orabs 3tr2 or12 anor2 df-t or1 2an an1 3tr1 ) ACZBDZC
    ZVCBEZPZVBABEZPZVCBDABDVFVBABCZPZEZVGVBBEZPZPVBVMPZVJVMPZEZVHVDVKVEVMVDVBVB
    CZVIPZEVKVBBFVRVJVBVQAVIAVQAGZHIJQVEVLVQBEZPVTVLPZVMVBBUAVLVTUIVMWAVGVTVLAV
    QBVSUBIHKUCVMVBVJVBVMVBVGVLAVGABLUDVBBLMNVJVMVJVGVLVJABAVIUEZVJBAVIUFUGZOVJ
    VBBVJAWBUHWCOMNUJVPVHREVHVNVHVORVHVLPVBVLPZVGPVNVHVBVGVLUKVBVGVLULWDVBVGVBB
    UMIUNVOVGVJVLPZPVGRPRVJVGVLUOWERVGWEVJVJCZPZRVLWFVJABUPSRWGVJUQHQSVGURKUSVH
    UTQKVCBTABTVA $.

  $( Lemma used in study of orthoarguesian law.  Equation 4.12 of [MegPav2000]
     p. 23.  (Contributed by NM, 28-Dec-1998.) $)
  u1lem12 $p |- ( ( a ->1 b ) ->1 b ) = ( a ' ->1 b ) $=
    ( wi1 wn ax-a1 ud1lem0b u1lem11 ax-r2 ) ABCZBCADZDZBCZBCJBCILBAKBAEFFJBGH
    $.

  $( Lemma for unified implication study.  (Contributed by NM, 24-Dec-1997.) $)
  u2lem8 $p |- ( a ' ->2 ( a ->2 ( a ' ->2 b ) ) ) =
               ( a ->2 ( a ' ->2 b ) ) $=
    ( wn wi2 wa wo df-i2 wf u2lem7 ax-a1 ax-r1 u2lem7n 2an an12 anass anor1 lan
    dff ax-r2 an0 2or or0 ) ACZAUCBDDZDUDUCCZUDCZEZFZUDUCUDGUHABCZEZUCUIEFBFZHF
    ZUDUDUKUGHABIZUGAABFZUCBFZEZUIEZEZHUEAUFUQAUEAJKABLMURUPUJEZHAUPUINUSUNUOUJ
    EZEZHUNUOUJOVAUNHEHUTHUNUTUOUOCZEZHUJVBUOABPQHVCUORKSQUNTSSSSUAULUKUDUKUBUD
    UKUMKSSS $.

  $( Lemma for unified implication study.  (Contributed by NM, 24-Dec-1997.) $)
  u3lem8 $p |- ( a ' ->3 ( a ->3 ( a ' ->3 b ) ) ) = 1 $=
    ( wn wi3 wo wt comi31 comcom3 u3lemc4 wa ax-a1 ax-r1 u3lem7 2or ax-a3 ax-a2
    df-t lor or1 ax-r2 ) ACZAUABDZDZDUACZUCEZFUAUCAUCAUBGHIUEAUAABJABCJEZEZEZFU
    DAUCUGAUDAKLABMNUHAUAEZUFEZFUJUHAUAUFOLUJUFUIEZFUIUFPUKUFFEFUIFUFFUIAQLRUFS
    TTTTT $.

  $( Lemma for unified implication study.  (Contributed by NM, 24-Dec-1997.) $)
  u3lem9 $p |- ( a ->3 ( a ->3 ( a ' ->3 b ) ) ) =
               ( a ->3 ( a ' ->3 b ) ) $=
    ( wn wi3 wo comi31 u3lemc4 wa u3lem7 lor ax-a3 ax-r1 oridm ax-r5 ax-r2 ) AA
    ACZBDZDZDPREZRARAQFGSPPABHABCHEZEZEZRRUAPABIZJUBPPEZTEZRUEUBPPTKLUEUARUDPTP
    MNRUAUCLOOOO $.

  $( Lemma for unified implication study.  (Contributed by NM, 17-Jan-1998.) $)
  u3lem10 $p |- ( a ->3 ( a ' ^ ( a v b ) ) ) = a ' $=
    ( wn wo wi3 df-i3 anass ax-r1 anidm ran ax-r2 anor3 lor oran1 lan omlan 2or
    wa wt orabs comanr1 comorr comcom3 fh4r df-t 2an an1 ancom ) AACZABDZRZEUIU
    KRZUIUKCZRZDZAUIUKDZRZDZUIAUKFURUIUIARZDUIUOUIUQUSUOUKUIBCZRZDZUIULUKUNVAUL
    UIUIRZUJRZUKVDULUIUIUJGHVCUIUJUIIJKUNUIAVADZRVAUMVEUIVEUMVEAUJCZDUMVAVFAABL
    ZMAUJNKHOAUTPKQVBUIVADZUJVADZRZUIUIVAUJUIUTUAAUJABUBUCUDVJUISRUIVHUIVISUIUT
    TVIUJVFDZSVAVFUJVGMSVKUJUEHKUFUIUGKKKUQAUIRUSUPUIAUIUJTOAUIUHKQUIATKK $.

  $(
  u3lem10a $p |- ( a ->3 ( ( a ->3 b ) ->3 ( b ->3 a ) ) ' ) = a ' $=
?$.
  $)

  $( Lemma for unified implication study.  (Contributed by NM, 18-Jan-1998.) $)
  u3lem11 $p |- ( a ->3 ( b ' ^ ( a v b ) ) ) = ( a ->3 b ' ) $=
    ( wn wo wa wi3 df-i3 lan lor ax-r5 wf anass ax-r1 ax-a2 ax-r2 ran 2or ancom
    3tr1 wt ax-a1 oran dff anor3 oran1 coman1 coman2 comcom7 fh2 anidm or0 df-t
    ax-a3 or1 3tr2 an1 comor1 comcom2 comor2 fh4 id ) ABCZABDZEZFACZVDEZVEVDCZE
    ZDZAVEVDDZEZDZAVBFZAVDGVEVBEZVEBEZDZAVEVBDZEZDVNVEVBCZEZDZVRDVLVMVPWAVRVOVT
    VNBVSVEBUAHIJVIVPVKVRVIKVPDZVPVFKVHVPVNVCEZVNVNCZEVFKVCWDVNABUBHWCVFVEVBVCL
    MVNUCSVHVEVNBDZEZVPVGWEVEWEVGWEBVCCZDZVGWEWGBDWHVNWGBABUDJWGBNOBVCUEOMHWFVE
    VNEZVODVPVNVEBVEVBUFVNBVEVBUGUHUIWIVNVOWIVEVEEZVBEZVNWKWIVEVEVBLMWJVEVBVEUJ
    POJOOQWBVPKDVPKVPNVPUKOOAVEVCDZVQEZEVRVKVRWMVQAWMTVQEZVQWLTVQVEADZBDTBDZWLT
    WOTBWOAVEDZTVEANTWQAULMOJVEABUMWPBTDTTBNBUNOUOPWNVQTEVQTVQRVQUPOOHVJWMAVJVE
    VCVBEZDWMVDWRVEVBVCRIVCVEVBVCAABUQURVCBABUSURUTOHVRVASQAVBGSO $.

  $( Lemma for unified implication study.  (Contributed by NM, 18-Jan-1998.) $)
  u3lem11a $p |- ( a ->3 ( ( b ->3 a ) ->3 ( a ->3 b ) ) ' ) =
              ( a ->3 b ' ) $=
    ( wi3 wn wo wa ud3lem1 ancom anor3 ax-r2 lor oran1 con2 ud3lem0a u3lem11 )
    ABACABCCZDZCABDZABEZFZCARCQTAPTPBRADZFZEZTDZBAGUCBSDZEUDUBUEBUBUARFUERUAHAB
    IJKBSLJJMNABOJ $.

  $( Lemma for unified implication study.  (Contributed by NM, 18-Jan-1998.) $)
  u3lem12 $p |- ( a ->3 ( a ->3 b ' ) ) ' = ( a ^ b ) $=
    ( wn wi3 wo wa lem4 ax-r4 df-a ax-r1 ax-r2 ) AABCZDDZCACLEZCZABFZMNALGHPOAB
    IJK $.

  $( Lemma for unified implication study.  (Contributed by NM, 18-Jan-1998.) $)
  u3lem13a $p |- ( a ->3 ( a ->3 b ' ) ' ) = ( a ->1 b ) $=
    ( wn wi3 wa wo ancom ax-r2 ax-a1 ax-r1 lan 2or comanr1 comorr ax-a2 lea lor
    wt comcom2 wf wi1 df-i3 u3lemnana u3lemana com2or com2an fh4r lel2or df-le2
    comcom3 anor2 anor3 oran3 df-t 2an an1 comid comi31 fh1 dff u3lemnaa df-i1
    or0 ) AABCZDZCZDACZVFEZVGVFCZEZFZAVGVFFEZFZABUAZAVFUBVMVGAVDCZEZFZVNVKVGVLV
    PVKVGAVDFZAVOFZEZEZVGVDEZVGVOEZFZFZVGVHWAVJWDVHVFVGEWAVGVFGAVDUCHVJVGVEEZWD
    VIVEVGVEVIVEIJKWFVEVGEWDVGVEGAVDUDHHLWEVGWDFZVTWDFZEZVGVGWDVTVGWBWCVGVDMVGV
    OMUEAVTAVRVSAVDNAVONUFUJUGWIVGREVGWGVGWHRWGWDVGFVGVGWDOWDVGWBVGWCVGVDPVGVOP
    UHUIHWHVTVTCZFZRWDWJVTWDVRCZVSCZFZWJWDWMWLFWNWBWMWCWLAVDUKAVDULLWMWLOHVRVSU
    MHQRWKVTUNJHUOVGUPHHHVLAVGEZAVFEZFZVPAVGVFAAAUQSAVEAVDURSUSWQTVPFZVPWOTWPVP
    TWOAUTJWPVFAEVPAVFGAVDVAHLWRVPTFVPTVPOVPVCHHHLVQVGABEZFZVNVPWSVGVOBABVOBIJK
    QVNWTABVBJHHH $.

  $( Lemma for unified implication study.  (Contributed by NM, 19-Jan-1998.) $)
  u3lem13b $p |- ( ( a ->3 b ' ) ->3 a ' ) = ( a ->1 b ) $=
    ( wn wa wo ax-r1 lan ax-r2 2or comanr1 comcom3 com2an com2or ax-a2 lea letr
    leo wf comcom wt wi3 wi1 df-i3 u3lemnana u3lemnaa comorr fh4r coman1 coman2
    ax-a1 comcom7 fh3r df-le2 2an u3lemnona comi31 fh2 u3lemana anandi u3lemanb
    id u3lemaa an4 ancom dff an0 or0 comanr2 comcom2 comorr2 lel2or anor3 anor2
    oran3 lor df-t an1 df-i1 ud1lem0a ) ABCZUAZACZUAWACZWBDZWCWBCZDZEZWAWCWBEZD
    ZEZABUBZWAWBUCWJWBAVTCZDZEZAVTEZAWLEZDZDZWBVTDZWBWLDZEZEZWKWGWRWIXAWGWBWQDZ
    WMEZWRWDXCWFWMAVTUDWFWCADWMWEAWCAWEAUJFGAVTUEHIXDWNWQWMEZDZWRWBWMWQAWMAWLJK
    ZAWQAWOWPAVTUFAWLUFLZKUGXFWNWOWMEZWPWMEZDZDZWRXEXKWNWMWOWPWMAVTAWLUHZWMVTAW
    LUIZUKMWMAWLXMXNMULGXLWRWRXKWQWNXKWQWQXIWOXJWPXIWMWOEWOWOWMNWMWOWMAWOAWLOZA
    VTQPUMHXJWMWPEWPWPWMNWMWPWMAWPXOAWLQPUMHUNWQVAHGWRVAHHHHWIWAWNDZXAWHWNWAAVT
    UOGXPWAWBDZWAWMDZEZXAWBWAWMAWAAVTUPKXGUQXSXAREXAXQXAXRRAVTURXRWAADZWAWLDZDZ
    RWAAWLUSYBAWBVTEZDZWTDZRXTYDYAWTAVTVBAVTUTUNYEAWBDZYCWLDZDZRAYCWBWLVCYHYGYF
    DZRYFYGVDYIYGRDRYFRYGRYFAVEFGYGVFHHHHHIXAVGHHHIXBWNXAEZWQXAEZDZWKWNXAWQXAWN
    XAWBWMWBXAWBWSWTWBVTJWBWLJMSZXAAWLXAAYMUKWLXAWLWSWTVTWSWBVTVHKWBWLVHMSLMSWQ
    WNWQWBWMWQAAWQXHSZVIWQAWLYNWLWQWLWOWPVTWOAVTVJKAWLVJLSLMSUGYLWNTDZWKYJWNYKT
    YJXAWNEZWNWNXANYPWNWNXAWNXAWBWNWSWBWTWBVTOWBWLOVKWBWMQPUMWNVAHHYKWQWQCZEZTX
    AYQWQXAWTWSEZYQWSWTNYSWOCZWPCZEYQWTYTWSUUAAVTVLAVTVMIWOWPVNHHVOTYRWQVPFHUNY
    OWNWKWNVQWNAWLUBZWKUUBWNAWLVRFWLBABWLBUJFVSHHHHHH $.

  $( Lemma for unified implication study.  (Contributed by NM, 19-Jan-1998.) $)
  u3lem14a $p |- ( a ->3 ( ( b ->3 a ' ) ->3 b ' ) ) =
          ( a ->3 ( b ->3 a ) ) $=
    ( wn wi3 u3lem13b ud3lem0a wa wo df-i3 ancom u1lemanb ax-r2 u1lemnanb ax-a2
    wi1 2or wt u1lemonb lan an1 u3lem3 ax-r1 id ) ABACZDBCZDZDABAOZDZABADDZUFUG
    ABAEFUHUDUGGZUDUGCZGZHZAUDUGHZGZHZUIAUGIUPUDBGZUDUEGZHZAHZUIUMUSUOAUMUEUDGZ
    BUDGZHZUSUJVAULVBUJUGUDGVAUDUGJBAKLULUKUDGVBUDUKJBAMLPVCVBVAHUSVAVBNVBUQVAU
    RBUDJUEUDJPLLUOAQGAUNQAUNUGUDHQUDUGNBARLSATLPUTAUSHZUIUSANVDUIUIUIVDABUAUBU
    IUCLLLLL $.

  $( Used to prove ` ->1 ` "add antecedent" rule in ` ->3 ` system.
     (Contributed by NM, 19-Jan-1998.) $)
  u3lem14aa $p |- ( a ->3 ( a ->3 ( ( b ->3 a ' ) ->3 b ' ) ) ) = 1 $=
    ( wn wi3 wt u3lem14a ud3lem0a i3th1 ax-r2 ) AABACDBCDDZDAABADDZDEJKAABFGABH
    I $.

  $( Used to prove ` ->1 ` "add antecedent" rule in ` ->3 ` system.
     (Contributed by NM, 19-Jan-1998.) $)
  u3lem14aa2 $p |- ( a ->3 ( a ->3 ( b ->3 ( b ->3 a ' ) ' ) ) ) = 1 $=
    ( wn wi3 wt wi1 u3lem13a u3lem13b ax-r1 ax-r2 ud3lem0a u3lem14aa ) AABBACDZ
    CDZDZDAAMBCDZDZDEOQANPANBAFZPBAGPRBAHIJKKABLJ $.

  $( Used to prove ` ->1 ` modus ponens rule in ` ->3 ` system.  (Contributed
     by NM, 19-Jan-1998.) $)
  u3lem14mp $p |- ( ( a ->3 b ' ) ' ->3 ( a ->3 ( a ->3 b ) ) ) = 1 $=
    ( wn wo wa lear ax-a1 ax-r1 lbtr lelor letr ud3lem0c u3lem5 le3tr1 u3lemle1
    wi3 ) ABCZPCZAABPPZAQCZDAQDEZACZATEZDZEZUBBDZRSUEUDUFUAUDFUCBUBUCTBATFBTBGH
    IJKAQLABMNO $.

  $( Lemma for Kalmbach implication.  (Contributed by NM, 7-Aug-2001.) $)
  u3lem15 $p |- ( ( a ->3 b ) ^ ( a v b ) )
                 = ( ( a ' v b ) ^ ( a v ( a ' ^ b ) ) ) $=
    ( wi3 wo wa wn dfi3b ran anass comor1 comcom2 comor2 com2an com2or fh1r lan
    wf ax-r2 2or 3tr leao4 lecom comcom anabs oran dff ax-r1 or0 df2le2 ) ABCZA
    BDZEAFZBDZAULBFZEZDZULBEZDZEZUKEUMURUKEZEUMAUQDZEUJUSUKABGHUMURUKIUTVAUMUTU
    PUKEZUQUKEZDVAUKUPUQUKAUOABJZUKULUNUKAVDKUKBABLKMZNUQUKUQUKBULAUAZUBUCOVBAV
    CUQVBAUKEZUOUKEZDAQDAUKAUOVDVEOVGAVHQABUDVHUOUOFZEZQUKVIUOABUEPQVJUOUFUGRSA
    UHTUQUKVFUISRPT $.

  $( Possible axiom for Kalmbach implication system.  (Contributed by NM,
     21-Jan-1998.) $)
  u3lemax4 $p |- ( ( a ->3 b ) ->3 ( ( a ->3 b ) ->3 ( ( b ->3 a )
      ->3 ( ( b ->3 a )
     ->3 ( ( c ->3 ( c ->3 a ) ) ->3 ( c ->3 ( c ->3 b ) ) ) ) ) ) ) = 1 $=
    ( wi3 wn wo wt lem4 2i3 lor ax-r2 tb wa u3lembi ax-r4 ax-r1 conb ancom bltr
    anor1 oran3 ax-r5 ax-a3 le1 ska4 2bi 2or lea lelor lebi 3tr2 ) ABDZULBADZUM
    CCADDZCCBDDZDZDDZDDULEZUQFZGULUQHUSURUMEZCEZAFZVABFZDZFZFZGUQVEURUQUTUPFVEU
    MUPHUPVDUTUNVBUOVCCAHCBHIJKJURUTFZVDFABLZEZVDFZVFGVGVIVDVGULUMMZEVIULUMUAVK
    VHABNOKUBURUTVDUCVJGVJUDGVIVBVCLZFZVJGAEZBEZLZEZVNCMZVOCMZLZFZVMWAGVNVOCUEP
    VMWAVIVQVLVTVHVPABQOVLVBEZVCEZLZVTVBVCQVTWDVRWBVSWCVRCVNMWBVNCRCATKVSCVOMWC
    VOCRCBTKUFPKUGPKVLVDVIVLVDVCVBDZMZVDWFVLVBVCNPVDWEUHSUISUJUKKK $.

  $( Possible axiom for Kalmbach implication system.  (Contributed by NM,
     23-Jan-1998.) $)
  u3lemax5 $p |- ( ( a ->3 b ) ->3 ( ( a ->3 b )
      ->3 ( ( b ->3 a ) ->3 ( ( b ->3 a )
      ->3 ( ( b ->3 c ) ->3 ( ( b ->3 c )
      ->3 ( ( c ->3 b ) ->3 ( ( c ->3 b )
      ->3 ( a ->3 c ) ) ) ) ) ) ) ) ) = 1 $=
    ( wi3 wn wo wt lem4 tb lor ax-a3 ax-r1 oran3 u3lembi ax-r4 ax-r2 ax-r5 bltr
    wa lelor le1 ska2 lea lebi ) ABDZUEBADZUFBCDZUGCBDZUHACDZDDZDDZDDZDDUEEZULF
    ZGUEULHUNUMUFEZBCIZEZUIFZFZFZGULUSUMULUOUKFUSUFUKHUKURUOUKUGEZUJFZURUGUJHVB
    VAUHEZUIFZFZURUJVDVAUHUIHJVEVAVCFZUIFZURVGVEVAVCUIKLVFUQUIVFUGUHSZEUQUGUHMV
    HUPBCNOPQPPPJPJUTUMUOFZURFZGVJUTUMUOURKLVJABIZEZURFZGVIVLURVIUEUFSZEVLUEUFM
    VNVKABNOPQVMGVMUAGVLUQACIZFZFZVMVQGABCUBLVPURVLVOUIUQVOUICADZSZUIVSVOACNLUI
    VRUCRTTRUDPPPP $.

  $( Equivalence to biconditional.  (Contributed by NM, 5-Jul-2000.) $)
  bi1o1a $p |- ( a == b ) =
                 ( ( a ->1 ( a ^ b ) ) ^ ( ( a v b ) ->1 a ) ) $=
    ( wn wa wo tb wi1 lea leo letr ax-r1 leid ler2an lear lebi ax-r2 3tr1 df-i1
    wf 2or lecom comcom comor1 comcom7 fh1 dfb ax-a2 dff ancom ax-r5 or0r comid
    df2le2 comcom2 comanr1 fh1r 3tr lor anor3 2an ) ACZABDZEZVABCZDZDZVCADZEZVC
    VEAEZDZABFZAVBGZABEZAGZDVJVHVCVEAVEVCVEVCVEVAVCVAVDHVAVBIJZUAUBVCAVAVBUCUDU
    EKVKVBVEEVEVBEVHABUFVBVEUGVEVFVBVGVEVFVEVCVEVOVELMVCVENOSVBADZEZVAADZVPEVBV
    GSVRVPSAVADVRAUHAVAUIPUJVBVPVQVPVBVBAABHZUMKVQVPVPUKKPAVAVBAAAULUNABUOUPQTU
    QVLVCVNVIVLVAAVBDZEVCAVBRVTVBVAVTVBAVBNVBAVBVSVBLMOURPVNVMCZVMADZEVIVMARWAV
    EWBAVEWAABUSKWBAVMANAVMAABIALMOTPUTQ $.

  $( Equivalence to biconditional.  (Contributed by NM, 8-Jul-2000.) $)
  biao $p |- ( a == b ) = ( ( a ^ b ) == ( a v b ) ) $=
    ( wa wn wo tb leao1 df2le2 ax-r1 anor3 lecon df-le1 ler2an lear df-le2 lebi
    oridm ax-r2 2or dfb 3tr1 ) ABCZADBDCZEUBABEZCZUBDZUDDZCZEABFUBUDFUBUEUCUHUE
    UBUBUDABBGZHIUCUGUHABJUGUHUGUFUGUBUDUIKUGUGUGQLMUHUGUHUGUFUGNOLPRSABTUBUDTU
    A $.

  $( Equivalence to ` ->2 ` .  (Contributed by NM, 5-Jul-2000.) $)
  i2i1i1 $p |- ( a ->2 b ) =
               ( ( a ->1 ( a v b ) ) ^ ( ( a v b ) ->1 b ) ) $=
    ( wn wa wo wi2 wi1 an1r ax-r1 df-i2 anabs ax-a2 ax-r2 df-i1 df-t 3tr1 anor3
    wt lor leor leid ler2an lear lebi 2or 3tr 2an ) BACZBCDZEZRUJDZABFAABEZGZUL
    BGZDUKUJUJHIABJUMRUNUJUHAULDZEZAUHEZUMRUPUHAEUQUOAUHABKSUHALMAULNAOPUNULCZU
    LBDZEZUIBEZUJULBNVAUTUIURBUSABQBUSBULBBATBUAUBULBUCUDUEIUIBLUFUGP $.

  $( An absorption law for ` ->1 ` .  (Contributed by NM, 21-Feb-2002.) $)
  i1abs $p |- ( ( a ->1 b ) ' v ( a ^ b ) ) = a $=
    ( wi1 wn wa wo ud1lem0c ax-r5 comanr1 comorr comcom6 fh4r wt orabs df-a lor
    df-t ax-r1 ax-r2 2an an1 3tr ) ABCDZABEZFAADZBDZFZEZUDFAUDFZUGUDFZEZAUCUHUD
    ABGHAUDUGABIAUGUEUFJKLUKAMEAUIAUJMABNUJUGUGDZFZMUDULUGABOPMUMUGQRSTAUASUB
    $.

  $( Part of an attempt to crack a potential Kalmbach axiom.  (Contributed by
     NM, 29-Dec-1997.) $)
  test $p |- ( ( ( c v ( a ' v b ' ) ) ^ ( c ' ^ ( c v ( a ^ b ) ) ) )
             v ( ( c ' ^ ( a ^ b ) ) v ( c ^ ( c ' v ( a ^ b ) ) ) ) )
            = ( ( c v ( a ^ b ) ) ^ ( c ' v ( a ^
                                                   b ) ) ) $=
    ( wn wo wa oran3 lor ax-r5 comor1 comor2 com2an com2or wt ax-a3 ax-r1 ax-a2
    comcom7 ax-r2 2an ran comcom2 fh4r anor2 df-t or1 leor df-le2 coman1 comcom
    lelan fh3 oml or12 orabs ancom an1 ) CADBDEZEZCDZCABFZEZFZFZUTVAFZCUTVAEZFZ
    EZECVADZEZVCFZVHEZVBVFFZVDVKVHUSVJVCURVICABGHUAIVLVJVHEZVCVHEZFZVMVJVHVCVJV
    EVGVJUTVAVJCCVIJZUBZVJVACVIKRZLVJCVFVQVJUTVAVRVSMLMVJUTVBVRVJCVAVQVSMLUCVPN
    VMFZVMVNNVOVMVNVJVEEZVGEZNWBVNVJVEVGOPWBVGWAEZNWAVGQWCVGNENWANVGWAVJVJDZEZN
    VEWDVJCVAUDHNWEVJUEPSHVGUFSSSVOVCVEEZVGEZVMWGVOVCVEVGOPWGVCVGEZVMWFVCVGWFVE
    VCEVCVCVEQVEVCVAVBUTVACUGUKUHSIWHVCCEZVCVFEZFVMVCCVFVCCUTVBUIRVFVCVFUTVBUTV
    AJZVFCVAVFCWKRUTVAKMLUJULWIVBWJVFWICVCEVBVCCQCVAUMSWJUTVCVAEEZVFVCUTVAUNWLU
    TVCEZVAEZVFWNWLUTVCVAOPWMUTVAUTVBUOISSTSSSTVTVMNFVMNVMUPVMUQSSSS $.

  $( Part of an attempt to crack a potential Kalmbach axiom.  (Contributed by
     NM, 29-Dec-1997.) $)
  test2 $p |- ( a v b ) =<
           ( ( a == b ) ' v ( ( c v ( a ^ b ) ) ^ ( c ' v ( a ^
                                                   b ) ) ) ) $=
    ( wo tb wn wa dfnb anidm 2or comor1 comor2 com2an comcom2 com2or fh4r ax-r2
    wt ax-r1 leor ax-a2 lea leo letr df-le2 df-a lor df-t 2an le2an lelor bltr
    an1 ) ABDZABEFZABGZUPGZDZUOCUPDZCFZUPDZGZDURUNURUNAFZBFZDZGZUPDZUNUOVFUQUPA
    BHUPIJVGUNUPDZVEUPDZGZUNUNUPVEUNABABKZABLZMUNVCVDUNAVKNUNBVLNOPVJUNRGUNVHUN
    VIRVHUPUNDUNUNUPUAUPUNUPAUNABUBABUCUDUEQVIVEVEFZDZRUPVMVEABUFUGRVNVEUHSQUIU
    NUMQQQSUQVBUOUPUSUPVAUPCTUPUTTUJUKUL $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                         Some 3-variable theorems
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( A 3-variable theorem.  Equivalent to OML. (Contributed by NM,
     18-Oct-1998.) $)
  3vth1 $p |- ( ( a ->2 b ) ^ ( b v c ) ' ) =< ( a ->2 c ) $=
    ( wn wa wo wi2 anor3 lan ax-r1 anass ax-r2 ancom omlan lear bltr leran leor
    letr df-i2 lor ran le3tr1 ) BBDZADZEZFZBCFDZEZCUECDZEZFZABGZUHEACGUIUKULUIU
    GUDEZUJEZUKUIUGUDUJEZEZUOUQUIUPUHUGBCHIJUOUQUGUDUJKJLUNUEUJUNUFUEUNUDUGEUFU
    GUDMBUENLUDUEOPQPUKCRSUMUGUHUMBUEUDEZFUGABTURUFBUEUDMUALUBACTUC $.

  $( A 3-variable theorem.  Equivalent to OML. (Contributed by NM,
     18-Oct-1998.) $)
  3vth2 $p |- ( ( a ->2 b ) ^ ( b v c ) ' ) =
              ( ( a ->2 c ) ^ ( b v c ) ' ) $=
    ( wi2 wo wn wa 3vth1 lear ler2an ax-a2 ax-r4 lan bltr lebi ) ABDZBCEZFZGZAC
    DZRGZSTRABCHPRIJUAPRUATCBEZFZGPRUCTQUBBCKLMACBHNTRIJO $.

  $( A 3-variable theorem.  Equivalent to OML. (Contributed by NM,
     18-Oct-1998.) $)
  3vth3 $p |- ( ( a ->2 c ) v ( ( a ->2 b ) ^ ( b v c ) ' ) ) =
              ( a ->2 c ) $=
    ( wi2 wo wn wa ax-a2 3vth1 df-le2 ax-r2 ) ACDZABDBCEFGZEMLELLMHMLABCIJK $.

  $( A 3-variable theorem.  (Contributed by NM, 18-Oct-1998.) $)
  3vth4 $p |- ( ( a ->2 b ) ' ->2 ( b v c ) ) =
              ( ( a ->2 c ) ' ->2 ( b v c ) ) $=
    ( wo wi2 wn wa 3vth2 ax-a1 ran 3tr2 lor df-i2 3tr1 ) BCDZABEZFZFZOFZGZDOACE
    ZFZFZSGZDQOEUBOETUDOPSGUASGTUDABCHPRSPIJUAUCSUAIJKLQOMUBOMN $.

  $( A 3-variable theorem.  (Contributed by NM, 18-Oct-1998.) $)
  3vth5 $p |- ( ( a ->2 b ) ' ->2 ( b v c ) ) =
            ( c v ( ( a ->2 b ) ^ ( c ->2 b ) ) ) $=
    ( wo wn wi2 ax-a3 or12 comorr comcom2 fh3 ax-r1 oridm ax-r5 ax-r2 ancom lor
    wa 2an df-i2 anor3 ax-a1 ran 3tr1 ) BCDZBAEBEZRZDZUEEZRZDZCUHBCEZUFRZDZRZDZ
    ABFZEZUEFZCUQCBFZRZDUKBCUJDDZUPBCUJGVBCBUJDZDUPBCUJHVCUOCVCBUHDZBUIDZRUOBUH
    UIBUGIBUEBCIJKVDUHVEUNVDBBDZUGDZUHVGVDBBUGGLVFBUGBMNOUIUMBUMUIUMUFULRUIULUF
    PBCUAOLQSOQOOUSUEUREZUIRZDZUKURUETUKVJUJVIUEUHVHUIUHUQVHUQUHABTZLUQUBOUCQLO
    VAUOCUQUHUTUNVKCBTSQUD $.

  $( A 3-variable theorem.  (Contributed by NM, 18-Oct-1998.) $)
  3vth6 $p |- ( ( a ->2 b ) ' ->2 ( b v c ) ) =
            ( ( ( a ->2 b ) ^ ( c ->2 b ) ) v
              ( ( a ->2 c ) ^ ( b ->2 c ) ) ) $=
    ( wi2 wn wo wa oridm ax-r1 3vth4 3vth5 ax-a2 ax-r2 2or or4 leo df-i2 ler2an
    lbtr df-le2 lor ud2lem0a ax-r5 ) ABDZEBCFZDZUFUFFZUDCBDZGZACDZBCDZGZFZUGUFU
    FHIUGUFUJEZUEDZFZUMUFUOUFABCJUAUPCUIFZBULFZFZUMUFUQUOURABCKUOUNCBFZDURUEUTU
    NBCLUBACBKMNUSUTUMFZUMCUIBULOVAUEUMFZUMUTUEUMCBLUCVBBUIFZCULFZFUMBCUIULOVCU
    IVDULBUIBUDUHBBAEZBEZGZFZUDBVGPUDVHABQISBBCEZVFGZFZUHBVJPUHVKCBQISRTCULCUJU
    KCCVEVIGZFZUJCVLPUJVMACQISCCVFVIGZFZUKCVNPUKVOBCQISRTNMMMMMM $.

  $( A 3-variable theorem.  (Contributed by NM, 18-Oct-1998.) $)
  3vth7 $p |- ( ( a ->2 b ) ' ->2 ( b v c ) ) =
                ( a ->2 ( b v c ) ) $=
    ( wi2 wa wo wn df-i2 2an anass ax-r1 anor3 lan an32 3tr lor comanr2 comcom6
    3tr2 ax-r2 anidm an4 fh3 3vth5 ax-a3 or12 3tr1 ) CABDZCBDZEZFCBAGZBCFZGZEZF
    ZFZUHGULDAULDZUJUOCUJBUKBGZEZFZBCGZUREZFZEZUOUHUTUIVCABHCBHIUOVDUOBUSVBEZFV
    DUNVEBUNUKVAEZUREZVFURUREZEZVEUKURVAEZEZUSVAEZUNVGVLVKUKURVAJKVJUMUKBCLMUKU
    RVANSVIVGVHURVFURUAMKUKVAURURUBOPBUSVBBUSUKURQRBVBVAURQRUCTKTPABCUDUQULUNFB
    CUNFFUPAULHBCUNUEBCUNUFOUG $.

  $( A 3-variable theorem.  (Contributed by NM, 18-Oct-1998.) $)
  3vth8 $p |- ( a ->2 ( b v c ) ) =
            ( ( ( a ->2 b ) ^ ( c ->2 b ) ) v
              ( ( a ->2 c ) ^ ( b ->2 c ) ) ) $=
    ( wo wi2 wn wa 3vth7 ax-r1 3vth6 ax-r2 ) ABCDZEZABEZFLEZNCBEGACEBCEGDOMABCH
    IABCJK $.

  $( A 3-variable theorem.  (Contributed by NM, 16-Nov-1998.) $)
  3vth9 $p |- ( ( a v b ) ->1 ( c ->2 b ) ) =
                ( ( b v c ) ->2 ( a ->2 b ) ) $=
    ( wo wn wi2 wa wi1 anor3 ax-r1 df-i2 lan 2or df-i1 ud2lem0c 2an ax-r2 ancom
    anandi lor anass or32 comanr1 comcom6 comorr2 or12 oridm ax-r5 ax-a2 3tr1
    fh3 ) ABDZEZULCBFZGZDAEBEZGZULBCEZUPGZDZGZDZULUNHBCDZABFZFZUMUQUOVAUQUMABIJ
    UNUTULCBKLMULUNNVEBUQDZUPURGZULGZDZVBVEVDVCEZVDEZGZDVIVCVDKVDVFVLVHABKVLVGU
    PULGZGZVHVJVGVKVMVGVJBCIJABOPVNUPURULGGZVHVOVNUPURULSJVHVOUPURULUAJQQMQVIBV
    HDZUQDZVBBUQVHUBVQVAUQDVBVPVAUQVPBVGDZBULDZGZVABVGULBVGUPURUCUDABUEUKVTUTUL
    GVAVRUTVSULVGUSBUPURRTVSABBDZDULBABUFWABABUGTQPUTULRQQUHVAUQUIQQQUJ $.

  $( 3-variable commutation theorem.  (Contributed by NM, 19-Mar-1999.) $)
  3vcom $p |- ( ( a ->1 c ) v ( b ->1 c ) ) C
              ( ( a ' ->1 c ) ^ ( b ' ->1 c ) ) $=
    ( wn wi1 wa wo oran3 ax-r1 u1lem9ab le2or lecom bctr comcom6 comcom ) ADCEZ
    BDCEZFZACEZBCEZGZRUARDZPDZQDZGZUAUEUBPQHIUEUAUCSUDTACJBCJKLMNO $.

  ${
    3vded11.1 $e |- b =< ( c ->1 ( b ->1 a ) ) $.
    $( A 3-variable theorem.  Experiment with weak deduction theorem.
       (Contributed by NM, 25-Oct-1998.) $)
    3vded11 $p |- c =< ( b ->1 a ) $=
      ( wi1 wt le1 wn wa df-t ancom anor2 ax-r2 lor ax-r1 ax-a3 3tr df-i1 lbtr
      wo leo lelan lelor lel2or bltr lebi u1lemle2 ) CBAEZCUHEZFUIGFBCHZCBHZIZT
      ZTZUIFBUJTZUOHZTZUOULTZUNUOJURUQULUPUOULUKCIUPCUKKBCLMNOBUJULPQBUIUMDUMUJ
      CUHIZTZUIULUSUJUKUHCUKUKBAIZTZUHUKVAUAUHVBBAROSUBUCUIUTCUHROSUDUEUFUG $.
  $}

  ${
    3vded12.1 $e |- ( a ^ ( c ->1 a ) ) =< ( c ->1 ( b ->1 a ) ) $.
    3vded12.2 $e |- c =< a $.
    $( A 3-variable theorem.  Experiment with weak deduction theorem.
       (Contributed by NM, 25-Oct-1998.) $)
    3vded12 $p |- c =< ( b ->1 a ) $=
      ( wi1 wt le1 wn wo df-t wa an1 ax-r1 u1lemle1 lan ax-r2 bltr lecon leo
      df-i1 lbtr letr lel2or lebi u1lemle2 ) CBAFZCUGFZGUHHGAAIZJUHAKAUHUIAACAF
      ZLZUHAAGLZUKULAAMNUKULUJGACAEOPNQDRUICIZUHCAESUMUMCUGLZJZUHUMUNTUHUOCUGUA
      NUBUCUDRUEUF $.
  $}

  ${
    3vded13.1 $e |- ( b ^ ( c ->1 a ) ) =< ( c ->1 ( b ->1 a ) ) $.
    3vded13.2 $e |- c =< a $.
    $( A 3-variable theorem.  Experiment with weak deduction theorem.
       (Contributed by NM, 25-Oct-1998.) $)
    3vded13 $p |- c =< ( b ->1 a ) $=
      ( wi1 wa wt an1 ax-r1 u1lemle1 lan ax-r2 bltr 3vded11 ) ABCBBCAFZGZCBAFFB
      BHGZQRBBIJHPBPHCAEKJLMDNO $.
  $}

  ${
    3vded21.1 $e |- c =< ( ( a ->0 b ) ->0 ( c ->2 b ) ) $.
    3vded21.2 $e |- c =< ( a ->0 b ) $.
    $( A 3-variable theorem.  Experiment with weak deduction theorem.
       (Contributed by NM, 31-Oct-1998.) $)
    3vded21 $p |- c =< b $=
      ( wf wo wa wn wi0 df-i0 lbtr lor ax-r2 2or ax-a2 3tr comor2 comcom2 anabs
      wi2 ax-r4 df-i2 anor3 ler2an leror ax-a3 oridm lecom comcom comid fh1 or0
      com2or ax-r1 dff ran ancom ax-r5 3tr2 leran com2an fh1r an32 anass le3tr2
      lan an0 ) CBFGZBCCBGZHBAIZBGZVJIZHZGZVJHZCVICVOVJCVLBVMGZVLIZGZHZVOCVLVSC
      ABJZVLEABKZLZCWACBUAZJZVSDWEWAIZWDGVRVQGVSWAWDKWFVRWDVQWAVLWBUBWDBCIBIHZG
      VQCBUCWGVMBCBUDMNOVRVQPQLUEVTVLVQHZVLVRHZGZVOVLVQVRVLBVMVKBRZVLVJVJVLVJVL
      VJVLBGZVLCVLBWCUFWLVKBBGZGVLVKBBUGWMBVKBUHMNLUIZUJSZUNVLVLVLUKSULVLBHZVNG
      ZFGWQWJVOWQUMWQWHFWIWHWQVLBVMWKWOULUOVLUPOWPBVNWPBVKGZBHBWRHBVLWRBVKBPUQW
      RBURBVKTQUSUTNLVACBTVPBVJHZVNVJHZGVIVJBVNCBRVJVLVMWNVJVJVJUKSVBVCWSBWTFWS
      BBCGZHBVJXABCBPVGBCTNWTVLVJHVMHVLVJVMHZHZFVLVMVJVDVLVJVMVEXCVLFHZFXDXCFXB
      VLVJUPVGUOVLVHNQONVFBUML $.
  $}

  ${
    3vded22.1 $e |- c =< ( C ( a , b ) v C ( c , b ) ) $.
    3vded22.2 $e |- c =< a $.
    3vded22.3 $e |- c =< ( a ->0 b ) $.
    $( A 3-variable theorem.  Experiment with weak deduction theorem.
       (Contributed by NM, 31-Oct-1998.) $)
    3vded22 $p |- c =< b $=
      ( wn wa wo wi0 wcmtr df-cmtr or4 ax-r2 lear lel2or leran le2or bltr df-i0
      wi2 lecon lelor leror letr or12 ax-r4 anor1 ax-r1 df-i2 2or oridm 3vded21
      3tr1 lbtr ) ABCCBABGZHZCGZUPHZIZIZVAIZABJZCBUAZJZCABKZCBKZIVBDVFVAVGVAVFA
      BHZAGZBHZIZUQVIUPHZIZIZVAVFVHUQIVJVLIIVNABLVHUQVJVLMNVKBVMUTVHBVJABOVIBOP
      VLUSUQVIURUPCAEUBQUCRSVGCBHZURBHZIZCUPHZUSIZIZVAVGVOVRIVPUSIIVTCBLVOVRVPU
      SMNVQBVSUTVOBVPCBOURBOPVRUQUSCAUPEQUDRSRUEVEVBVEVCGZVDIZVBVCVDTUQBUSIZIVA
      WBVBUQBUSUFWAUQVDWCWAVIBIZGZUQVCWDABTUGUQWEABUHUINCBUJUKVAULUNNUIUOFUM $.
  $}

  ${
    3vded3.1 $e |- ( c ->0 C ( a , c ) ) = 1 $.
    3vded3.2 $e |- ( c ->0 a ) = 1 $.
    3vded3.3 $e |- ( c ->0 ( a ->0 b ) ) = 1 $.
    $( A 3-variable theorem.  Experiment with weak deduction theorem.
       (Contributed by NM, 24-Jan-1999.) $)
    3vded3 $p |- ( c ->0 b ) = 1 $=
      ( wi0 wn wo wt df-i0 wa wcmtr lor 3tr1 ax-r2 ax-r1 wf ancom 3tr2 cmtrcom
      ax-a3 i0cmtrcom comcom4 comid comcom3 fh1 lan dff or0 an1 orabs ax-r5 3tr
      comcom ) CBGCHZBIZCABGZGZJCBKUPAHZIZBIZUPUTBIZIZUQUSUPUTBUBVBUQVAUPBVAUPU
      PUTLZIUPUTVEUPUTJLZUTUPLZUTVEUTUPAIZLVGUTALZIZVFVGUTUPAUPUTCACACCAMZGZCAC
      MZGZJUPVKIUPVMIVLVNVKVMUPCAUANCVKKCVMKODPUCUDUOAAAUEUFUGVHJUTVHCAGZJVOVHC
      AKQEPUHVJVGRIZVGVPVJRVIVGRAUTLVIAUIAUTSPNQVGUJPTUTUKUTUPSTNUPUTULPUMQUSUP
      URIVDCURKURVCUPABKNPOFUN $.
  $}

  $( Orthoarguesian-like law with ` ->1 ` instead of ` ->0 ` but true in all
     OMLs.  (Contributed by NM, 1-Nov-1998.) $)
  1oa $p |- ( ( a ->2 b ) ^
              ( ( b v c ) ->1 ( ( a ->2 b ) ^ ( a ->2 c ) ) ) )
               =< ( a ->2 c ) $=
    ( wn wa wo wi2 lear an12 lerr lan ax-r1 coman1 bctr comcom2 df-i2 2an anass
    wf ax-r2 wi1 bltr leid letr df-i1 fh2c anor3 comid comcom3 comanr2 fh1r dff
    lel2or anidm 2or ax-a2 or0 3tr ran 3tr2 lea lecom fh3 coman2 oran cbtr 3tr1
    com2an le3tr1 ) ADZBDZCDZEZEZBCFZFZVNBVJVKEZFZFZEZVNCVJVLEZFZFZEZWBABGZVOWE
    ACGZEZUAZEZWFWDWCWBVTWCHVNWBWBVNVKWAEZWBVJVKVLIZWJWACVKWAHJZUBWBUCUMUDWIWEV
    ODZVOWGEZFZEWEWMEZWEWNEZFZWDWHWOWEVOWGUEKWNWEWMWNWEVOWFEZEZWEWTWNWEVOWFILWE
    WSMNWNVOVOWGMOUFWRVNVOVRWBEZEZFZWDWPVNWQXBWPVRVMEZVNWEVRWMVMABPZVMWMBCUGLQV
    RVKEZVLEVQVLEZXDVNXFVQVLXFBVKEZVQVKEZFSVQFZVQVKBVQBBBUHUIVJVKUJUKXHSXIVQSXH
    BULLXIVJVKVKEZEVQVJVKVKRXKVKVJVKUNKTUOXJVQSFVQSVQUPVQUQTURUSVRVKVLRVJVKVLRZ
    UTTWQVOWEWGEZEXBWEVOWGIXMXAVOXMWEWEEZWFEZXAXOXMWEWEWFRLXNVRWFWBXNWEVRWEUNXE
    TACPZQTKTUOVPVNXAFZEVPVSWCEZEXCWDXQXRVPVNVRWBVNXGVRXGVNXLLXGVRXGVQBVQVLVAJV
    BNZVNWJWBWKWJWBWLVBNZVCKVNVOXAVNVMDZVOVNVMVJVMVDOVOYABCVELVFVNVRWBXSXTVHVCV
    PVSWCRVGTURXPVI $.

  $( Orthoarguesian-like OM law.  (Contributed by NM, 30-Dec-1998.) $)
  1oai1 $p |- ( ( a ->1 c ) ^
              ( ( a ^ b ) ' ->1 ( ( a ->1 c ) ^ ( b ->1 c ) ) ) )
               =< ( b ->1 c ) $=
    ( wn wi2 wo wa wi1 1oa i1i2 oran3 ax-r1 2an ud1lem0ab le3tr1 ) CDZADZEZQBDZ
    FZRPSEZGZHZGUAACHZABGDZUDBCHZGZHZGUFPQSIUDRUHUCACJZUETUGUBTUEABKLUDRUFUAUIB
    CJZMNMUJO $.

  $( Orthoarguesian-like OM law.  (Contributed by NM, 28-Feb-1999.) $)
  2oai1u $p |- ( ( a ->1 c ) ^
  ( ( ( a ->1 c ) ^ ( b ->1 c ) ) ' ->2 ( ( a ' ->1 c ) ^ ( b ' ->1 c ) ) ) )
               =< ( b ->1 c ) $=
    ( wn wi1 wa wi2 1oai1 u1lem11 2an ax-r1 ud1lem0a i1i2con2 ax-r2 le3tr2 ) AD
    CEZCEZPBDCEZFZDZQRCEZFZEZFUAACEZUDBCEZFZDSGZFUEPRCHQUDUCUGACIZUCTUFEZUGUIUC
    UFUBTUBUFQUDUAUEUHBCIZJKLKSUFMNJUJO $.

  $( OML analog to orthoarguesian law of Godowski/Greechie, Eq.  III with
     ` ->1 ` instead of ` ->0 ` .  (Contributed by NM, 1-Nov-1998.) $)
  1oaiii $p |- ( ( a ->2 b ) ^
              ( ( b v c ) ->1 ( ( a ->2 b ) ^ ( a ->2 c ) ) ) ) =
     ( ( a ->2 c ) ^ ( ( b v c ) ->1 ( ( a ->2 b ) ^ ( a ->2 c ) ) ) ) $=
    ( wi2 wo wa wi1 anass anidm lan ax-r2 ax-r1 leran bltr ancom ud1lem0a ax-a2
    1oa ud1lem0b ran lebi ) ABDZBCEZUBACDZFZGZFZUDUFFZUGUGUFFZUHUIUGUIUBUFUFFZF
    UGUBUFUFHUJUFUBUFIZJKLUGUDUFABCRMNUHUDCBEZUDUBFZGZFZUFFZUGUPUHUPUDUNUFFZFUH
    UDUNUFHUQUFUDUQUJUFUNUFUFUNULUEGUFUMUEULUDUBOPULUCUECBQSKTUKKJKLUOUBUFACBRM
    NUA $.

  $( OML analog to orthoarguesian law of Godowski/Greechie, Eq.  II with
     ` ->1 ` instead of ` ->0 ` .  (Contributed by NM, 1-Nov-1998.) $)
  1oaii $p |- ( b ' ^ ( ( a ->2 b ) v ( ( a ->2 c ) ^ ( ( b v c )
                ->1 ( ( a ->2 b ) ^ ( a ->2 c ) ) ) ) ) ) =< a ' $=
    ( wn wi2 wo wi1 orabs 1oaiii lor df-i2 ancom ax-r2 3tr2 lan omlan lear bltr
    wa ) BDZABEZACEZBCFUAUBSGZSZFZSZTADZSZUGUFTBUHFZSUHUEUITUAUAUCSZFUAUEUIUAUC
    HUJUDUAABCIJUABUGTSZFUIABKUKUHBUGTLJMNOBUGPMTUGQR $.

  $( Lemma for OA-like stuff with ` ->2 ` instead of ` ->0 ` .  (Contributed by
     NM, 15-Nov-1998.) $)
  2oalem1 $p |- ( ( a ->2 b ) ' v ( ( b v c ) v ( ( a ->2 b ) ^
         ( a ->2 c ) ) ) ) = 1 $=
    ( wi2 wn wo wa wt or12 df-i2 2an lor or32 ax-a2 lan ax-r5 ax-r2 anor3 ax-r1
    3tr ud2lem0c 2or oml 3tr1 ax-a3 oran lear bltr leo letr lecom comcom le3tr2
    comcom6 fh3 df-t or1 anidm 3tr2 ) ABDZEZBCFZUTACDZGZFFVBVAVDFZFVBBEZABFZGZB
    AEZVFGZFZCVICEZGZFZGZFZFZHVAVBVDIVEVPVBVAVHVDVOABUAUTVKVCVNABJACJKUBLVBVHFZ
    VOFVGCFZVOFZVQHVRVSVOVRBVHFZCFVSBCVHMWAVGCBVFBAFZGZFWBWAVGBAUCVHWCBVGWBVFAB
    NZOLWDUDPQPVBVHVOUEVTVSVKFZVSVNFZGHHGHVSVKVNVKVSVKVSVKEZVSWGVGVSWGVHVGVHWGV
    HVFVJEZGWGVGWHVFABUFOBVJRQSVFVGUGUHVGCUIUJUKUNULVNVSVNVSVNEZVSVLACFZGZWJBFZ
    WIVSWKWJWLVLWJUGWJBUIUJWKVLVMEZGWIWJWMVLACUFOCVMRQACBMUMUKUNULUOWEHWFHWEBVS
    VJFZFBHFZHVSBVJIWNHBWNVGVJFZCFCWPFZHVGCVJMWPCNWQCHFZHWPHCWPVGVGEZFZHVJWSVGA
    BRLHWTVGUPSQLCUQZQTLBUQZTWFCVSVMFZFWRHVSCVMIXCHCXCBWJFZVMFBWJVMFZFZHVSXDVMV
    SWLXDABCMWJBNQPBWJVMUEXFWOHXEHBXEWJWJEZFZHVMXGWJACRLHXHWJUPSQLXBQTLXATKHURT
    UST $.

  $( OA-like theorem with ` ->2 ` instead of ` ->0 ` .  (Contributed by NM,
     15-Nov-1998.) $)
  2oath1 $p |- ( ( a ->2 b ) ^
              ( ( b v c ) ->2 ( ( a ->2 b ) ^ ( a ->2 c ) ) ) ) =
              ( ( a ->2 b ) ^ ( a ->2 c ) ) $=
    ( wi2 wo wa wn df-i2 lan coman1 comorr2 comcom2 anor3 ax-r1 fh2 anass ax-r2
    cbtr wf wt anidm ran oran lor 2oalem1 ax-r4 df-a df-f 3tr1 2or or0 3tr ) AB
    DZBCEZUMACDZFZDZFUMUPUNGUPGFZEZFUMUPFZUMURFZEZUPUQUSUMUNUPHIUPUMURUMUOJUPUN
    UPEZGZURUPVCUNUPKLURVDUNUPMNROVBUPSEUPUTUPVASUTUMUMFZUOFZUPVFUTUMUMUOPNVEUM
    UOUMUAUBQUMGZURGZEZGTGVASVITVIVGVCEZTVJVIVCVHVGUNUPUCUDNABCUEQUFUMURUGUHUIU
    JUPUKQUL $.

  $( Orthoarguesian-like OM law.  (Contributed by NM, 30-Dec-1998.) $)
  2oath1i1 $p |- ( ( a ->1 c ) ^
              ( ( a ^ b ) ' ->2 ( ( a ->1 c ) ^ ( b ->1 c ) ) ) )
               = ( ( a ->1 c ) ^ ( b ->1 c ) ) $=
    ( wn wi2 wo wa wi1 2oath1 i1i2 2an ud2lem0a oran3 ax-r1 ud2lem0b ax-r2 3tr1
    ) CDZADZEZSBDZFZTRUAEZGZEZGUDACHZABGDZUFBCHZGZEZGUIRSUAIUFTUJUEACJZUJUGUDEU
    EUIUDUGUFTUHUCUKBCJKZLUGUBUDUBUGABMNOPKULQ $.

  $( Orthoarguesian-like OM law.  (Contributed by NM, 28-Feb-1999.) $)
  1oath1i1u $p |- ( ( a ->1 c ) ^
  ( ( ( a ->1 c ) ^ ( b ->1 c ) ) ' ->1 ( ( a ' ->1 c ) ^ ( b ' ->1 c ) ) ) )
               = ( ( a ->1 c ) ^ ( b ->1 c ) ) $=
    ( wn wi1 wa wi2 2oath1i1 u1lem11 2an ud2lem0a i1i2con2 ax-r1 ax-r2 3tr2 ) A
    DCEZCEZPBDCEZFZDZQRCEZFZGZFUBACEZUDBCEZFZDSEZFUFPRCHQUDUCUGACIZUCTUFGZUGUBU
    FTQUDUAUEUHBCIJZKUGUIUFSLMNJUJO $.

  $( Relation for studying OA. (Contributed by NM, 18-Nov-1998.) $)
  oale $p |- ( ( a ->2 b ) ^
      ( ( b v c ) v ( ( a ->2 b ) ^ ( a ->2 c ) ) ) ' ) =< ( a ->2 c ) $=
    ( wi2 wo wa wn df-i2 lan coman1 comanr2 comcom6 fh2 anass ax-r1 anidm ax-r2
    ran anor3 2or ax-a2 3tr 2oath1 df-le1 lear letr ) ABDZBCEZUGACDZFZEGZFZUJUI
    ULUJULUJEZUGUHUJDZFZUJUOUMUOUGUJUHGZUJGZFZEZFUGUJFZUGURFZEZUMUNUSUGUHUJHIUJ
    UGURUGUIJUJURUPUQKLMVBUJULEUMUTUJVAULUTUGUGFZUIFZUJVDUTUGUGUINOVCUGUIUGPRQU
    RUKUGUHUJSITUJULUAQUBOABCUCQUDUGUIUEUF $.

  ${
    oaeqv.1 $e |- ( ( a ->2 b ) ^
              ( ( b v c ) ' v ( ( a ->2 b ) ^ ( a ->2 c ) ) ) )
               =< ( ( b v c ) ->2 ( ( a ->2 b ) ^ ( a ->2 c ) ) ) $.
    $( Weakened OA implies OA).  (Contributed by NM, 16-Nov-1998.) $)
    oaeqv $p |- ( ( a ->2 b ) ^
              ( ( b v c ) ' v ( ( a ->2 b ) ^ ( a ->2 c ) ) ) )
               =< ( a ->2 c ) $=
      ( wi2 wo wn wa lea ler2an 2oath1 lbtr lear letr ) ABEZBCFZGOACEZHZFZHZRQT
      OPREZHRTOUAOSIDJABCKLOQMN $.
  $}

  ${
    3vroa.1 $e |- ( ( a ->2 b ) ^
              ( ( b v c ) ->0 ( ( a ->2 b ) ^ ( a ->2 c ) ) ) ) = 1 $.
    $( OA-like inference rule (requires OM only).  (Contributed by NM,
       13-Nov-1998.) $)
    3vroa $p |- ( a ->2 c ) = 1 $=
      ( wi2 wn wa wo wt df-i2 or12 oridm lor le1 wi0 ax-r1 lea bltr lebi ax-r2
      ran ancom an1 3tr lear df-i0 anor3 ax-r5 le3tr2 u2lemle2 lecon leran 3tr2
      leror ) ACEZCAFZCFZGZHZIACJZCURURHZHURUSHZUSICURURKVAURCURLMVBURABEZUOGZH
      ZIVEVBVDUSURVDUOIGZUOUSVDIUOGVFVCIUOVCIVCNIVCBCHZVDOZGZVCVIIDPVCVHQRSZUAI
      UOUBTUOUCUTUDMPVEIVENIBFZUQGZVDHZVEIVMVIVHIVMVCVHUEDVHVGFZVDHZVMVGVDUFVMV
      OVLVNVDBCUGUHPTUIVMNSVLURVDVKUPUQABABVJUJUKULUNRSTUMT $.
  $}

  $( Lemma for Mladen's OML. (Contributed by NM, 4-Nov-1998.) $)
  mlalem $p |- ( ( a == b ) ^ ( b ->1 c ) ) =< ( a ->1 c ) $=
    ( wa wn wo tb wi1 comcom3 anass ax-r1 3tr bltr ax-r2 lear letr lel2or df-i1
    wf leo comanr2 comanr1 fh2 dff lan an0 le0 an12 an4 leor lea dfb 2an coman1
    lecom coman2 com2or oran3 cbtr comcom7 fh2rc le3tr1 ) ABDZBEZBCDZFZDZAEZVDD
    ZVFDZFZVHACDZFZABGZBCHZDZACHVGVMVJVGVCVDDZVCVEDZFVMVDVCVEBVCABUAIBVEBCUBIUC
    VQVMVRVQSVMVQABVDDZDASDSABVDJVSSASVSBUDKUEAUFLVMUGMVRBBDZVLDZVMVRABVEDDBAVE
    DDZWAABVEJABVEUHWBBADVEDZWAWCWBBAVEJKBABCUINLWAVLVMVTVLOVLVHUJPMQMVJVHVDVFD
    ZDZVMVHVDVFJWEVHVMVHWDUKVHVLTPMQVPVCVIFZVFDVKVNWFVOVFABULBCRUMVIVFVCVIVFVIV
    DVFVHVDOVDVETPUOVIVCVIVHVDFVCEVIVHVDVHVDUNVHVDUPUQABURUSUTVANACRVB $.

  $( Mladen's OML. (Contributed by NM, 4-Nov-1998.) $)
  mlaoml $p |- ( ( a == b ) ^ ( b == c ) ) =< ( a == c ) $=
    ( wi1 wa tb u1lembi ran mlalem bltr ancom an32 3tr le2an an12 id 3tr1 anass
    anandi anandir 3tr2 2an le3tr2 ) ABDZBADZEZBCDZEZUECBDZEZUGEZEZACDZCADZEABF
    ZBCFZEZACFUHUMUKUNUHUOUGEUMUFUOUGABGZHABCIJUKCBFZUEEZUNUKUIUEEZUGEUIUGEZUEE
    UTUJVAUGUEUIKHUIUEUGLVBUSUECBGHMCBAIJNULUHUIEZUFUGUIEZEUQUFUJEZUGEUFUIEZUGE
    ULVCVEVFUGUEUDUIEEZUDUJEVEVFUEUDUIOVEUEUDEZUJEVEVGUFVHUJUDUEKHVEPUEUDUISQUD
    UEUIRQHUFUJUGTUFUIUGLUAUFUGUIRUFUOVDUPURBCGUBMACGUC $.

  $( 4-variable transitive law for equivalence.  (Contributed by NM,
     26-Jun-2003.) $)
  eqtr4 $p |- ( ( ( a == b ) ^ ( b == c ) ) ^ ( c == d ) ) =< ( a == d ) $=
    ( tb wa mlaoml leran letr ) ABEBCEFZCDEZFACEZKFADEJLKABCGHACDGI $.

  ${
    sac.1 $e |- ( a ->1 c ) = ( b ->1 c ) $.
    $( Theorem showing "Sasaki complement" is an operation.  (Contributed by
       NM, 3-Jan-1999.) $)
    sac $p |- ( a ' ->1 c ) = ( b ' ->1 c ) $=
      ( wi1 wn ud1lem0b u1lem12 3tr2 ) ACEZCEBCEZCEAFCEBFCEJKCDGACHBCHI $.
  $}

  ${
    sa5.1 $e |- ( a ->1 c ) =< ( b ->1 c ) $.
    $( Possible axiom for a "Sasaki algebra" for orthoarguesian lattices.
       (Contributed by NM, 3-Jan-1999.) $)
    sa5 $p |- ( b ' ->1 c ) =< ( ( a ' ->1 c ) v c ) $=
      ( wn wa wo wi1 leor ax-a2 lan ax-r5 oml6 ax-r1 ud1lem0c le3tr2 letr ax-a1
      3tr df-i1 lecon lea leror bltr orabs ancom 3tr2 ax-a3 ax-r2 lel2or le3tr1
      2or lear ) BEZEZUNCFZGAEZEZUQCFZGZCGZUNCHUQCHZCGUOVAUPBACGZUOVABCBGZVCBCI
      VDBUNCEZGZFZCGZVCVHVDVHBVEUNGZFZCGCVJGVDVGVJCVFVIBUNVEJKLVJCJCBMSNVGACVGA
      UQVEGZFZABCHZEACHZEVGVLVNVMDUABCOACOPAVKUBQUCUDQBRVCURUSCGZGZVAAURCVOARCC
      UQFZGVQCGCVOCVQJCUQUEVQUSCCUQUFLUGULVAVPURUSCUHNUIPUPCVAUNCUMCUTIQUJUNCTV
      BUTCUQCTLUK $.
  $}

$(
lattice (((-xIy)vy)Iy)=(x2y)
lattice "((xIw)v(yIw))<((((-xIw)^(-yIw))Iw)vw)"
lattice "((((-xIw)vw)Iw)^(((-yIw)vw)Iw))<((((-xIw)v(-yIw))Iw)vw)"
lattice "(((-xIw)^(-yIw))Iw)<((xIw)v(yIw))"
lattice "(((-xIw)v(-yIw))Iw)<(((xIw)^(yIw))vw)"
a' v b' =< (a ^ b)' v 0
(a v 0)' ^ (b v 0)' =< (a ^ b)' v 0
(a ^ b)' =< a' v b'
(a v b)' =< (a' ^ b') v 0
$)
  $( Lemma for attempt at Sasaki algebra.  (Contributed by NM, 4-Jan-1999.) $)
  salem1 $p |- ( ( ( a ' ->1 b ) v b ) ->1 b ) = ( a ->2 b ) $=
    ( wn wi1 wo wi2 u1lemob ax-r4 anor1 ax-r1 ax-r2 ran ax-a2 ancom anabs df-i1
    wa 3tr 2or df-i2 3tr1 ) ACZBDBEZCZUCBQZEZBUBBCQZEZUCBDABFUFUGBEUHUDUGUEBUDU
    BCZBEZCZUGUCUJUBBGZHUGUKUBBIJKUEUJBQZBBUIEZQZBUCUJBULLUMUNBQUOUJUNBUIBMLUNB
    NKBUIORSUGBMKUCBPABTUA $.

  $( Weak DeMorgan's law for attempt at Sasaki algebra.  (Contributed by NM,
     4-Jan-1999.) $)
  sadm3 $p |- ( ( ( a ' ->1 c ) ^ ( b ' ->1 c ) ) ->1 c ) =<
              ( ( a ->1 c ) v ( b ->1 c ) ) $=
    ( wn wi1 wa wo oran3 ax-r1 u1lem9a bltr an32 lea leo or32 lbtr u1lemab letr
    le2or df-i1 ax-a1 bile leran lel2or lelor 2or le3tr1 ) ADZCEZBDZCEZFZDZULCF
    ZGZUHACFZGZUJBCFZGZGZULCEACEZBCEZGUOUQUJGZUTUOUHUJGZUICFZGVCUMVDUNVEUMUIDZU
    KDZGZVDVHUMUIUKHIVFUHVGUJACJBCJSKUNVEUKFVEUIUKCLVEUKMKSVDVCVEVDVDUPGVCVDUPN
    UHUJUPOPVEUQVCVEUHCFZUHDZCFZGUQUHCQVIUHVKUPUHCMVJACVJAAVJAUAIUBUCSKUQUJNRUD
    RUJUSUQUJURNUERULCTVAUQVBUSACTBCTUFUG $.

  $( Weak DeMorgan's law for attempt at Sasaki algebra. $)
$(
  sadm1 $p |- ( ( a ->1 c ) v ( b ->1 c ) ) =<
              ( ( ( ( a ' ->1 c ) ^ ( b ' ->1 c ) ) ->1 c ) v c ) $=
?$.
$)

  $( Weak DeMorgan's law for attempt at Sasaki algebra. $)
$(
  sadm2 $p |- ( ( ( ( a ' ->1 c ) v c ) ->1 c ) ^
                  ( ( ( b ' ->1 c ) v c ) ->1 c ) ) =<
              ( ( ( ( a ' ->1 c ) v ( b ' ->1 c ) ) ->1 c ) v c ) $=
?$.
$)

  $( Weak DeMorgan's law for attempt at Sasaki algebra. $)
$(
  sadm4 $p |- ( ( ( a ' ->1 c ) v ( b ' ->1 c ) ) ->1 c ) =<
              ( ( ( a ->1 c ) ^ ( b ->1 c ) ) v c ) $=
?$.
$)

  $( Chained biconditional.  (Contributed by NM, 2-Mar-2000.) $)
  bi3 $p |- ( ( a == b ) ^ ( b == c ) ) =
            ( ( ( a ^ b ) ^ c ) v ( ( a ' ^ b ' ) ^ c ' ) ) $=
    ( tb wa wn wo ax-r1 lan leo letr lecom comcom7 wf anass 3tr ax-r2 ran ancom
    2or wi1 wi2 dfb u12lembi 2an df-i1 lear coman1 coman2 fh2rc comanr2 comcom3
    com2an comanr1 fh2 dff an0 anidm or0r comcom an4 an0r 3tr2 or0 df-i2 le3tr1
    an32 lea bltr oran lbtr fh2r u2lemab u2lemanb an12 ) ABDZBCDZEABEZAFZBFZEZG
    ZBCUAZCBUBZEZEZVRCEZWACFZEZGZVPWBVQWEABUCWEVQBCUDHUEWBWCEZWDEWGWAGZWDEZWFWJ
    WKWLWDWKWBVTBCEZGZEVRWOEZWAWOEZGWLWCWOWBBCUFIWAWOVRWAWOWAVTWOVSVTUGVTWNJKLW
    AABWAAVSVTUHMWABVSVTUIZMUMUJWPWGWQWAWPVRVTEZVRWNEZGNWGGWGVTVRWNBVRABUKULBWN
    BCUNULZUOWSNWTWGWSABVTEZEZANEZNABVTOXDXCNXBABUPZIHAUQPWTVRBEZCEZWGXGWTVRBCO
    HXFVRCXFABBEZEVRABBOXHBABURIQRQTWGUSPWQWAVTEZWAWNEZGWANGWAVTWAWNWAVTWRUTXAU
    OXIWAXJNXIVSVTVTEZEWAVSVTVTOXKVTVSVTURIQXJVSBEVTCEZEVSBXLEZEZNVSVTBCVAVSBXL
    OXNVSNENXMNVSXBCEZNCEZXMNXPXONXBCXERHBVTCOCVBVCIVSUQQPTWAVDPTPRWBWCWDOWMWGW
    DEZWAWDEZGWJWGWDWAWGWDACEZBEZBWHVTEZGZWGWDXTBYBXSBUGBYAJKABCVGCBVEVFLWGWAWG
    WAFZWGABGZYCWGAYDWGAWNEAABCOAWNVHVIABJKABVJVKLMVLXQWGXRWIXQVRCWDEEXSBWDEZEZ
    WGVRCWDOABCWDVAYFXTWGYEBXSYEWDBEBBWDSCBVMQIACBVGQPXRVSVTWDEZEVSYAEZWIVSVTWD
    OYGYAVSYGWDVTEYAVTWDSCBVNQIYHWHWAEWIVSWHVTVOWHWASQPTQVCQ $.

  $( Chained biconditional.  (Contributed by NM, 25-Jun-2003.) $)
  bi4 $p |- ( ( ( a == b ) ^ ( b == c ) ) ^ ( c == d ) ) =
            ( ( ( ( a ^ b ) ^ c ) ^ d ) v
            ( ( ( a ' ^ b ' ) ^ c ' ) ^ d ' ) ) $=
    ( tb wa wn wo ax-r1 lan lecom leao4 lbtr wf anass 3tr ax-r2 ran 2or ancom
    wi1 wi2 bi3 u12lembi df-i1 leao2 oran2 comcom comcom6 fh2rc comanr2 comcom3
    2an comanr1 fh2 dff an0 anidm or0r an4 an0r 3tr2 or0 u2lemab df2le1 comcom7
    an32 bltr fh2r u2lemanb an12 ) ABEBCEFZCDEZFABFZCFZAGBGFZCGZFZHZCDUAZDCUBZF
    ZFZVODFZVRDGZFZHZVLVSVMWBABCUCWBVMCDUDIUMVSVTFZWAFWDVRHZWAFZWCWGWHWIWAWHVSV
    QCDFZHZFVOWLFZVRWLFZHWIVTWLVSCDUEJVRWLVOVRWLVQVPWKUFKVRVOVOVRGZVOWOVOVPGZCH
    ZWOCVNWPLVPCUGZMKUHUIUJWMWDWNVRWMVOVQFZVOWKFZHNWDHWDVQVOWKCVOVNCUKULCWKCDUN
    ULZUOWSNWTWDWSVNCVQFZFZVNNFZNVNCVQOXDXCNXBVNCUPZJIVNUQPWTVOCFZDFZWDXGWTVOCD
    OIXFVODXFVNCCFZFVOVNCCOXHCVNCURJQRQSWDUSPWNVRVQFZVRWKFZHVRNHVRVQVRWKVPVQUKX
    AUOXIVRXJNXIVPVQVQFZFVRVPVQVQOXKVQVPVQURJQXJVPCFVQDFZFVPCXLFZFZNVPVQCDUTVPC
    XLOXNVPNFNXMNVPXBDFZNDFZXMNXPXONXBDXERICVQDODVAVBJVPUQQPSVRVCPSPRVSVTWAOWJW
    DWAFZVRWAFZHWGWDWAVRWDWAWDWAXQVODWAFFVNDFZCWAFZFZWDVODWAOVNCDWAUTYAXSCFZWDX
    TCXSXTWACFCCWATDCVDQJVNDCVGQPZVEKWDVRWDWOWDWQWOWDYBWQVNCDVGCXSWPLVHWRMKVFVI
    XQWDXRWFYCXRVPVQWAFZFVPWEVQFZFZWFVPVQWAOYDYEVPYDWAVQFYEVQWATDCVJQJYFWEVRFWF
    VPWEVQVKWEVRTQPSQVBQ $.

  $( Implicational product with 3 variables.  Theorem 3.20 of "Equations,
     states, and lattices..." paper.  (Contributed by NM, 3-Mar-2000.) $)
  imp3 $p |- ( ( a ->2 b ) ^ ( b ->1 c ) ) =
             ( ( a ' ^ b ' ) v ( b ^ c ) ) $=
    ( wi2 wi1 wa wn wo df-i1 lan u2lemc1 comcom3 comanr1 fh2 u2lemanb ancom lea
    u2lem3 u2lemle2 letr df2le2 ax-r2 2or 3tr ) ABDZBCEZFUEBGZBCFZHZFUEUGFZUEUH
    FZHAGUGFZUHHUFUIUEBCIJUGUEUHBUEABKLBUHBCMLNUJULUKUHABOUKUHUEFUHUEUHPUHUEUHB
    UEBCQBUEBARSTUAUBUCUD $.

  $( Disjunction of biconditionals.  (Contributed by NM, 5-Jul-2000.) $)
  orbi $p |- ( ( a == c ) v ( b == c ) ) =
      ( ( ( a ->2 c ) v ( b ->2 c ) ) ^ ( ( c ->1 a ) v ( c ->1 b ) ) ) $=
    ( tb wo wa wn wi2 2or ax-a2 ax-a3 lor ax-r2 ax-r5 leo letr lecom comcom 3tr
    bctr wi1 dfb ancom imp3 ax-r1 df-i1 lear comi12 fh4rc df-le2 lan 3tr2 df-i2
    lea anor1 cbtr comcom7 fh4 orordi 3tr1 or12 2an ) ACDZBCDZEACFZAGZCGZFZEZBC
    FZBGVGFZEZEVLVIEZACHZBCHZEZCAUAZCBUAZEZFZVCVIVDVLACUBBCUBIVIVLJVMVJVKVIEZEV
    JVOVHEZVGCAFZEZFZEZVTVJVKVIKWAWEVJVKVEEZVHEVOVQFZVHEZWAWEWGWHVHWGVKWCEZWHVE
    WCVKACUCLWHWJBCAUDUEMNVKVEVHKWIWBVQVHEZFWEVQVHVOVQWDVHCAUFZVHWDVHWDVHVGWDVF
    VGUGVGWCOPZQRTCABUHUIWKWDWBWKWDVHEVHWDEWDVQWDVHWLNWDVHJVHWDWMUJSUKMULLWFVJW
    BEZVJWDEZFVTWBVJWDWBCVKVHEZEZVJWBCVKEZVHEZWQVOWRVHBCUMZNCVKVHKZMZVJWQVJWQVJ
    CWQBCUGZCWPOZPQRTWBWQWDXBWQWDWQCWCGZFZWDGXFWQXFWQXFCWQCXEUNXDPQRCWCUOUPUQTU
    RWNVPWOVSVJVOEZVHEWSWNVPXGWRVHXGVJWREWRVOWRVJWTLVJWRVJCWRXCCVKOPUJMNVJVOVHK
    WSWQVPXAWRCVHEZEXHWREWQVPWRXHJCVKVHUSVNXHVOWRACUMWTIUTMULWOVGVJWCEEZVSVJVGW
    CVAVGVJEZWDEWDXJEXIVSXJWDJVGVJWCUSVQWDVRXJWLVRVGCBFZEXJCBUFXKVJVGCBUCLMIUTM
    VBMSS $.

  $( Disjunction of biconditionals.  (Contributed by NM, 5-Jul-2000.) $)
  orbile $p |- ( ( a == c ) v ( b == c ) ) =<
      ( ( ( a ^ b ) ->2 c ) ^ ( c ->1 ( a v b ) ) ) $=
    ( tb wo wi2 wi1 wa orbi i2or i1or le2an bltr ) ACDBCDEACFBCFEZCAGCBGEZHABHC
    FZCABEGZHABCINPOQABCJABCKLM $.

  ${
    mlaconj4.1 $e |- ( ( d == e ) ^ ( ( e ' ^ c ' ) v ( d ^ c ) ) ) =<
                     ( d == c ) $.
    mlaconj4.2 $e |- d = ( a v b ) $.
    mlaconj4.3 $e |- e = ( a ^ b ) $.
    $( For 4GO proof of Mladen's conjecture, that it follows from Eq.  (3.30)
       in OA-GO paper.  (Contributed by NM, 8-Jul-2000.) $)
    mlaconj4 $p |- ( ( a == b ) ^ ( ( a == c ) v ( b == c ) ) ) =<
                   ( a == c ) $=
      ( tb wo wa wn ax-r2 lbtr ran 2or ax-r1 anass comcom7 wf biao bile wi2 wi1
      bicom orbile imp3 le2an 2bi ax-r4 lan 2an lea 3tr1 rbi ler2an coman1 bctr
      ancom an32 coman2 com2an com2or fh2c anor3 comanr1 fh2rc leao1 df2le2 dff
      comcom3 oran an0r 3tr2 or0 3tr an4 anidm or0r dfb lor mlaoml bltr letr
      bi3 ) ABIZACIZBCIZJZKABJZABKZIZWKLZCLZKZCWJKZJZKZWGWFWLWIWQWFWLWFWKWJIZWL
      ABUAZWKWJUEMUBWIWKCUCCWJUDKWQABCUFWKCWJUGNUHWRDEIZELZWNKZDCKZJZKZWGXFWRXA
      WLXEWQDWJEWKGHUIZXCWOXDWPXBWMWNEWKHUJOXDCDKWPDCUSDWJCGUKMPULQXFWFWJCIZKZW
      GXFWFXHXFXAWFXAXEUMWLWSXAWFWJWKUEXGWTUNNXFDCIXHFDWJCGUONUPXIWFWHKZWGWKALZ
      BLZKZJZWJCKZXMWNKZJZKZWKCKZXPJZXIXJXRXNXOKZXNXPKZJXTXPXNXOXPWKXMXPABXPXKX
      LWNKZKZAXKXLWNRYDAXKYCUQSURZXPXKWNKZXLKZBXKXLWNUTYGBYFXLVASURZVBXMWNUQVCX
      PWJCXPABYEYHVCXPCXMWNVASVBVDYAXSYBXPYAWKXOKZXMXOKZJXSTJXSXMXOWKXMWJLZXOAB
      VEZWJXOWJCVFVKURXMABXMAXKXLUQSXMBXKXLVASVBZVGYIXSYJTYIWKWJKZCKZXSYOYIWKWJ
      CRQYNWKCWKWJABBVHVIOMXMWJKZCKZTCKZYJTYRYQTYPCTXMXMLZKZYPXMVJYPYTWJYSXMABV
      LUKQMOQXMWJCRCVMVNPXSVOVPYBWKXPKZXMXPKZJTXPJXPXMXPWKXMWNVFYMVGUUATUUBXPUU
      AAXMKZBWNKZKZTUUDKZTABXMWNVQUUFUUETUUCUUDTXLKAXKKZXLKTUUCTUUGXLAVJOXLVMAX
      KXLRVNOQUUDVMVPUUBXMXMKZWNKZXPUUIUUBXMXMWNRQUUHXMWNXMVROMPXPVSVPPMWFXNXHX
      QABVTXHXOYKWNKZJZXQWJCVTXQUUKXPUUJXOXMYKWNYLOWAQMULABCWEUNABCWBWCWDWCWD
      $.
  $}

  $( For 5GO proof of Mladen's conjecture.  (Contributed by NM,
     20-Jan-2002.) $)
  mlaconj $p |- ( ( a == b ) ^ ( ( a == c ) v ( b == c ) ) ) =<
     ( ( ( ( a ->1 ( a ^ b ) ) ^ ( ( a ^ b ) ->1 ( ( a ^ b ) v c ) ) ) ^
              ( ( ( ( a ^ b ) v c ) ->1 c ) ^ ( c ->1 ( a v b ) ) ) ) ^
                ( ( a v b ) ->1 a ) ) $=
    ( tb wo wa wi2 wi1 orbile lelan ancom ran anass ax-r2 3tr lan bi1o1a i2i1i1
    id 3tr1 2an lbtr ) ABDZACDBCDEZFUCABFZCGZCABEZHZFZFZAUEHZUEUECEZHZFZULCHZUH
    FZFUGAHZFZUDUIUCABCIJUKUQFZUMUOFZUHFZFZUNUPUQFZFZUJURUKUQVAFZFUKUMVCFZFVBVD
    VEVFUKVEVAUQFUMUPFZUQFVFUQVAKVAVGUQVAVAVGUTUTUHUTSLUMUOUHMNLUMUPUQMOPUKUQVA
    MUKUMVCMTUCUSUIVAABQUFUTUHUECRLUAUNUPUQMTUB $.

  ${
    mlaconj2.1 $e |- ( ( ( ( a ->1 ( a ^ b ) ) ^
                    ( ( a ^ b ) ->1 ( ( a ^ b ) v c ) ) ) ^
              ( ( ( ( a ^ b ) v c ) ->1 c ) ^ ( c ->1 ( a v b ) ) ) ) ^
                ( ( a v b ) ->1 a ) ) =< ( a == c ) $.
    $( For 5GO proof of Mladen's conjecture.  Hypothesis is 5GO law
       consequence.  (Contributed by NM, 6-Jul-2000.) $)
    mlaconj2 $p |- ( ( a == b ) ^ ( ( a == c ) v ( b == c ) ) ) =<
                   ( a == c ) $=
      ( tb wo wa wi1 mlaconj letr ) ABEACEZBCEFGAABGZHLLCFZHGMCHCABFZHGGNAHGKAB
      CIDJ $.
  $}

  $( Equivalence to chained biconditional.  (Contributed by NM, 3-Mar-2000.) $)
  $( [Appears not to be a theorem.]
  bi3eq $p |- ( ( a == b ) ^ ( ( a ^ c ) v ( b ' ^ c ' ) ) ) =
              ( ( a == c ) ^ ( b == c ) ) $=
    ( u1lembi ran ax-r1 anass wn lea wa leo df-i1 lbtr letr lecom lear lecon
    comcom7 fh2c u1lemab id ax-r2 u1lemana 2or lan bi3 bicom ) ??????????DEF???
    ???GZ?????????????????BHZCHZI???UIBAJK????LFMNO???????UIUJP??ACPQNORS??????
    ??????UHFZ????????TE?UAZUBUB???UK????????UCEULUBUBUDULUBUBUE???????????UB??
    ???UFFUB?????UGUEUBUBUBUB $.
  $)

  $( Complemented antecedent lemma.  (Contributed by NM, 6-Aug-2001.) $)
  i1orni1 $p |- ( ( a ->1 b ) v ( a ' ->1 b ) ) = 1 $=
    ( wi1 wn wo wa wt df-i1 ax-a1 ax-r5 ax-r1 ax-r2 lor orordi u1lemoa or1r ) A
    BCZADZBCZEQARBFZEZEZGSUAQSRDZTEZUARBHUAUDAUCTAIJKLMUBQAEZQTEZEZGQATNUGGUFEG
    UEGUFABOJUFPLLL $.

  ${
    negant.1 $e |- ( a ->1 c ) = ( b ->1 c ) $.
    $( Lemma for negated antecedent identity.  (Contributed by NM,
       6-Aug-2001.) $)
    negantlem1 $p |- a C ( b ->1 c ) $=
      ( wi1 wn wa wo leo df-i1 ax-r1 ax-r2 lbtr lecom comcom6 ) ABCEZAFZPQQACGZ
      HZPQRISACEZPTSACJKDLMNO $.

    $( Lemma for negated antecedent identity.  (Contributed by NM,
       6-Aug-2001.) $)
    negantlem2 $p |- a =< ( b ' ->1 c ) $=
      ( wn wi1 wo leo wa wt i1orni1 lan ax-r1 an1 u1lemc6 negantlem1 ancom lear
      bltr letr comcom fh4rc 3tr1 u1lemaa 3tr2 ler2an ax-a1 leror u1lemab ax-r2
      lea lbtr df-i1 le3tr1 leid lel2or ) AABEZCFZGZURAURHUSABCFZIZURGZURUSJIZU
      SUTURGZIZUSVBVEVCVDJUSBCKLMVCUSUSNMUTURABCOAUTABCDPUAUBUCVAURURVACUTIZURV
      ACUTVAACIZCAACFZIVHAIVAVGAVHQVHUTADLACUDUEACRSAUTRUFBCIZUQCIZGZUQEZVJGVFU
      RVIVLVJVIBVLBCUKBUGULUHVFUTCIVKCUTQBCUIUJUQCUMUNTURUOUPST $.

    $( Lemma for negated antecedent identity.  (Contributed by NM,
       6-Aug-2001.) $)
    negantlem3 $p |- ( a ' ^ c ) =< ( b ' ->1 c ) $=
      ( wn wa wi1 wo leo df-i1 ax-r1 ax-r2 lbtr leran leror u1lemab ax-a1 ax-r5
      lea le3tr1 letr ) AEZCFBCGZCFZBEZCGZUBUCCUBUBACFZHZUCUBUGIUHACGZUCUIUHACJ
      KDLMNBCFZUECFZHBUKHZUDUFUJBUKBCSOBCPUFUEEZUKHZULUECJULUNBUMUKBQRKLTUA $.

    $( Lemma for negated antecedent identity.  (Contributed by NM,
       6-Aug-2001.) $)
    negantlem4 $p |- ( a ' ->1 c ) =< ( b ' ->1 c ) $=
      ( wn wi1 wa wo df-i1 ax-a1 ax-r5 ax-r1 ax-r2 negantlem2 negantlem3 lel2or
      bltr ) AEZCFZARCGZHZBECFZSREZTHZUARCIUAUDAUCTAJKLMAUBTABCDNABCDOPQ $.

    $( Negated antecedent identity.  (Contributed by NM, 6-Aug-2001.) $)
    negant $p |- ( a ' ->1 c ) = ( b ' ->1 c ) $=
      ( wn wi1 negantlem4 ax-r1 lebi ) AECFBECFABCDGBACACFBCFDHGI $.

    $( Negated antecedent identity.  (Contributed by NM, 6-Aug-2001.) $)
    negantlem5 $p |- ( a ' ^ c ' ) = ( b ' ^ c ' ) $=
      ( wi1 wn wa ran u1lemanb 3tr2 ) ACEZCFZGBCEZLGAFLGBFLGKMLDHACIBCIJ $.

    $( Negated antecedent identity.  (Contributed by NM, 6-Aug-2001.) $)
    negantlem6 $p |- ( a ^ c ' ) = ( b ^ c ' ) $=
      ( wn wa negant negantlem5 ax-a1 ran 3tr1 ) AEZEZCEZFBEZEZNFANFBNFLOCABCDG
      HAMNAIJBPNBIJK $.

    $( Negated antecedent identity.  (Contributed by NM, 6-Aug-2001.) $)
    negantlem7 $p |- ( a v c ) = ( b v c ) $=
      ( wo wn wa negantlem5 anor3 3tr2 con1 ) ACEZBCEZAFCFZGBFNGLFMFABCDHACIBCI
      JK $.

    $( Negated antecedent identity.  (Contributed by NM, 6-Aug-2001.) $)
    negantlem8 $p |- ( a ' v c ) = ( b ' v c ) $=
      ( wn wa wo negantlem6 ax-r4 oran2 3tr1 ) ACEZFZEBLFZEAECGBECGMNABCDHIACJB
      CJK $.

    $( Negated antecedent identity.  (Contributed by NM, 6-Aug-2001.) $)
    negant0 $p |- ( a ' ->0 c ) = ( b ' ->0 c ) $=
      ( wn wo wi0 negantlem7 ax-a1 ax-r5 3tr2 df-i0 3tr1 ) AEZEZCFZBEZEZCFZNCGQ
      CGACFBCFPSABCDHAOCAIJBRCBIJKNCLQCLM $.

    $( Negated antecedent identity.  (Contributed by NM, 6-Aug-2001.) $)
    negant2 $p |- ( a ' ->2 c ) = ( b ' ->2 c ) $=
      ( wn wa wo wi2 negantlem6 ax-a1 ran 3tr2 lor df-i2 3tr1 ) CAEZEZCEZFZGCBE
      ZEZRFZGPCHTCHSUBCARFBRFSUBABCDIAQRAJKBUARBJKLMPCNTCNO $.

    $( Negated antecedent identity.  (Contributed by NM, 6-Aug-2001.) $)
    negantlem9 $p |- ( a ->3 c ) =< ( b ->3 c ) $=
      ( wn wa wo wi3 leor wi1 df-i1 ax-a1 ax-r5 ax-r1 leo bltr letr ler2an lbtr
      ax-r2 leao4 sac 3tr2 leror leao1 negantlem8 negantlem5 ler lear lel df-i3
      lel2or dfi3b le3tr1 ) AEZCFZUOCEZFZGZAUOCGZFZGBEZCGZBVBUQFZGZVBCFZGZFZACH
      BCHUSVHVAUPVHURUPVCVGCUOVBUAUPAUPGZVGUPAIVIBVFGZVGUOCJZVBCJZVIVJABCDUBVKU
      OEZUPGZVIUOCKVIVNAVMUPALMNTVLVBEZVFGZVJVBCKVJVPBVOVFBLMNTUCZBVEVFBVDOUDZP
      QRURVCVGURUTVCUOUQCUEABCDUFZSURVDVGABCDUGVDVEVFVDBIUHPRULVAVCVGVAUTVCAUTU
      IVSSAVGUTAVJVGAVIVJAUPOVQSVRQUJRULACUKBCUMUN $.

    $( Negated antecedent identity.  (Contributed by NM, 6-Aug-2001.) $)
    negant3 $p |- ( a ' ->3 c ) = ( b ' ->3 c ) $=
      ( wn wi3 sac negantlem9 wi1 ax-r1 lebi ) AEZCFBEZCFLMCABCDGZHMLCLCIMCINJH
      K $.

    $( Lemma for negated antecedent identity.  (Contributed by NM,
       6-Aug-2001.) $)
    negantlem10 $p |- ( a ->4 c ) =< ( b ->4 c ) $=
      ( wa wn wo wi4 leao4 wi1 leor df-i1 ax-r1 lbtr lear ler2an ran ancom bltr
      ax-r2 u1lemab 2or ax-a2 lor ax-a3 letr negant ax-a1 lel2or lea negantlem8
      leao2 ler df-i4 dfi4b le3tr1 ) ACEZAFZCEZGZURCGZCFZEZGBFZCGZVBCVDEZGZCBEZ
      GZEZACHBCHUTVJVCUQVJUSUQVEVICAVDIUQACJZCEZVIUQVKCUQURUQGZVKUQURKVKVMACLMN
      ACOPVLBCJZCEZVIVKVNCDQVOBCEZVDCEZGZVIBCUAVRVBVRGZVIVRVBKVSVBVFVHGZGZVIVRV
      TVBVRVHVFGVTVPVHVQVFBCRVDCRUBVHVFUCTUDVIWAVBVFVHUEMZTNSSUFPUSVEVICURVDIUS
      URCJZCEZVIUSWCCUSURFZUSGZWCUSWEKWCWFURCLMNURCOPWDVDCJZCEZVIWCWGCABCDUGQWH
      VQVDFZCEZGZVIVDCUAWKVBWKGZVIWKVBKWLWAVIWAWLVTWKVBVFVQVHWJCVDRVHVPWJCBRBWI
      CBUHQTUBUDMWBTNSSUFPUIVCVEVIVCVAVEVAVBUJABCDUKNVCVGVHVBVAVFULUMPUIACUNBCU
      OUP $.

    $( Negated antecedent identity.  (Contributed by NM, 6-Aug-2001.) $)
    negant4 $p |- ( a ' ->4 c ) = ( b ' ->4 c ) $=
      ( wn wi4 sac negantlem10 wi1 ax-r1 lebi ) AEZCFBEZCFLMCABCDGZHMLCLCIMCINJ
      HK $.

    $( Negated antecedent identity.  (Contributed by NM, 6-Aug-2001.) $)
    negant5 $p |- ( a ' ->5 c ) = ( b ' ->5 c ) $=
      ( wn wi2 wi4 wa wi5 negant2 negant4 2an u24lem 3tr2 ) AEZCFZOCGZHBEZCFZRC
      GZHOCIRCIPSQTABCDJABCDKLOCMRCMN $.
  $}

  ${
    neg3ant.1 $e |- ( a ->3 c ) = ( b ->3 c ) $.
    $( Lemma for negated antecedent identity.  (Contributed by NM,
       7-Aug-2001.) $)
    neg3antlem1 $p |- ( a ^ c ) =< ( b ->1 c ) $=
      ( wa wi1 wn wo leo wi3 ran u3lemab 3tr2 u1lemab ax-r1 ax-r2 lbtr lea letr
      ) ACEZBCFZCEZUATTAGCEZHZUBTUCIUDBCEBGCEHZUBACJZCEBCJZCEUDUEUFUGCDKACLBCLM
      UBUEBCNOPQUACRS $.

    $( Lemma for negated antecedent identity.  (Contributed by NM,
       7-Aug-2001.) $)
    neg3antlem2 $p |- a ' =< ( b ->1 c ) $=
      ( wn wa wo leor wi3 u3lemab 3tr2 lbtr leao1 lel2or letr ax-r2 ax-r1 wf wt
      ran wi1 df-i3 u3lemanb anor3 con1 ler2an u3lem15 lear oran2 lan anor1 lor
      anor2 oran1 le3tr2 lecon1 leo ax-r5 u3lemob comor1 comcom7 comor2 comcom2
      lel com2an fh1r anabs dff 2or or0 3tr ler id ax-a2 orabs 3tr1 df-t coman1
      2an an1 coman2 com2or fh3 df-i1 le3tr1 ) AEZCFZWFACEZGZFZGZBEZBCFZGZWFBCU
      AWGWNWJWGWMWLCFZGZWNWGACFZWGGZWPWGWQHACIZCFBCIZCFWRWPWSWTCDTACJBCJKLWMWNW
      OWMWLHWLCWMMNOWJWLWMWJWLBWHFZGZWLCGZFZWLWJXBXCXBWJBXCFZAWGGZXBEZWJEZXEWFC
      GZXFFZXFXEWSACGZFXJXEWSXKXEWOWLWHFZGZXEGZWSXEXMHWSXNWSWTXNDBCUBPQLXEBCGZX
      KBXCCMXKXOXKXOWFWHFZXLXKEXOEWSWHFWTWHFXPXLWSWTWHDTACUCBCUCKACUDBCUDKUEQLU
      FACUGLXIXFUHOXEBXAEZFXGXCXQBBCUIZUJBXAUKPXFAWIEZGXHWGXSAACUMULAWIUNPUOUPW
      FXCWIWFXIXCWFCUQWSCGWTCGXIXCWSWTCDURACUSBCUSKLVDUFXDWLXCFZXAXCFZGWLRGWLXC
      WLXAWLCUTZXCBWHXCBYBVAXCCWLCVBVCVEVFXTWLYARWLCVGYAXAXQFZRXCXQXAXRUJRYCXAV
      HQPVIWLVJVKLVLNWFSFZWGWFGZWGWIGZFWFWKWFYESYFWFWFWFYEWFVMZYGYEWFWGGWFWGWFV
      NWFCVOPVPSWGWGEZGZYFWGVQYFYIWIYHWGACUNULQPVSYDWFWFVTQWGWFWIWFCVRZWGAWHWGA
      YJVAWGCWFCWAVCWBWCVPBCWDWE $.

    $( Lemma for negated antecedent identity.  (Contributed by NM,
       7-Aug-2001.) $)
    neg3ant1 $p |- ( a ->1 c ) = ( b ->1 c ) $=
      ( wn wa wi1 neg3antlem2 neg3antlem1 lel2or df-i1 lbtr wi3 ax-r1 lebi 3tr1
      wo ) AEZACFZQZBEZBCFZQZACGZBCGZTUCTUEUCRUESABCDHABCDIJBCKZLUCUDTUAUDUBBAC
      ACMBCMDNZHBACUGIJACKZLOUHUFP $.
  $}

  ${
    elimcons.1 $e |- ( a ->1 c ) = ( b ->1 c ) $.
    elimcons.2 $e |- ( a ^ c ) =< ( b v c ' ) $.
    $( Lemma for consequent elimination law.  (Contributed by NM,
       3-Mar-2002.) $)
    elimconslem $p |- a =< ( b v c ' ) $=
      ( wn wo wa wt df-t lecon oran3 ax-r1 lbtr bltr df-a wi1 df-i1 3tr2 lor
      lelor lelan an1 comor1 comcom7 lecom comcom6 fh2c le3tr2 ax-r4 3tr1 leror
      lear letr ax-a2 leao1 df-le2 ax-r2 ) ABCFZGZBBFZUSGZHZGZUTAAUTHZVCGZVDAVE
      AAFZUSGZHZGZVFAIHAUTVHGZHAVJIVKAIUTUTFZGVKUTJVLVHUTVLACHZFZVHVMUTEKVHVNAC
      LMNUAOUBAUCVHAUTVHAVGUSUDUEVHUTVHFZUTVOVMUTVMVOACPZMEOUFUGUHUIVIVCVEVGVOG
      ZFVAVBFZGZFVIVCVQVSVGVMGZVABCHZGZVQVSACQBCQVTWBDACRBCRSVMVOVGVPTWAVRVABCP
      TSUJAVHPBVBPUKTNVEUTVCAUTUMULUNVDVCUTGUTUTVCUOVCUTBVBUSUPUQURN $.

    $( Consequent elimination law.  (Contributed by NM, 3-Mar-2002.) $)
    elimcons $p |- a =< b $=
      ( wn wo wa df-t elimconslem leror bltr wi1 df-i1 3tr2 anor2 lor df-a lbtr
      wt lelan an1 comor1 comcom2 lecom comcom3 comcom le3tr2 negant ax-r1 3tr1
      fh2 ax-r4 ax-r5 lear lelor letr lea df-le2 lecon1 ) BABFZAFZACFZGZHZVBGZV
      BVAVEVAVBHZGZVFVAVABVCGZHZVGGZVHVATHVAVIVBGZHVAVKTVLVATAVBGVLAIAVIVBABCDE
      JZKLUAVAUBVIVAVBVIBBVCUCUDVBVIAVIAVIVMUEUFUGULUHVJVEVGVAFZVIFZGZFVBFZVDFZ
      GZFVJVEVPVSVSVPVQVBCHZGZVNVACHZGZVSVPVBCMVACMWAWCABCDUIVBCNVACNOVTVRVQACP
      QWBVOVNBCPQOUJUMVAVIRVBVDRUKUNSVGVBVEVAVBUOUPUQVEVBVBVDURUSSUT $.
  $}

  ${
    elimcons2.1 $e |- ( a ->1 c ) = ( b ->1 c ) $.
    elimcons2.2 $e |- ( a ^ ( c ^ ( b ->1 c ) ) ) =<
                   ( b v ( c ' v ( a ->1 c ) ' ) ) $.
    $( Consequent elimination law.  (Contributed by NM, 12-Mar-2002.) $)
    elimcons2 $p |- a =< b $=
      ( wi1 wa wn ax-r1 df-i1 ax-r2 lan anass leor df2le2 3tr ax-r4 lor ax-a2
      wo ud1lem0c ax-a3 lea df-le2 ax-r5 le3tr2 elimcons ) ABCDACBCFZGZGZBCHZAC
      FZHZTZTZACGZBUKTZEUJACAHZUPTZGZGZUPUSGZUPUIUTAUHUSCUHULUSULUHDIACJKLLVBVA
      ACUSMIUPUSUPURNOPUOBBBHUKTZGZUKTZTZBVDTZUKTZUQUNVEBUNUKVDTVEUMVDUKUMUHHVD
      ULUHDQBCUAKRUKVDSKRVHVFBVDUKUBIVGBUKVGVDBTBBVDSVDBBVCUCUDKUEPUFUG $.
  $}

  $( Lemma for biconditional commutation law.  (Contributed by NM,
     1-Dec-1999.) $)
  comanblem1 $p |- ( ( a == c ) ^ ( b == c ) ) =
                ( ( ( a v c ) ' v ( ( a ^ b ) ^ c ) ) ^ ( b ->1 c ) ) $=
    ( wi1 wa tb wo wn u1lembi 2an df-i1 comanr1 comcom3 ax-r1 ax-r2 lan ran 3tr
    ancom wf an4 an32 fh3 lea leor bltr letr lecom com2an comcom coman2 comcom2
    fh2c coman1 fh2rc anass dff an0 lor or0 anor3 bctr anandi leran df2le2 lear
    2or df-le2 3tr2 ) ACDZCADZEZBCDZCBDZEZEVJVMEVKVNEZEZACFZBCFZEACGHZABEZCEZGZ
    VMEZVJVKVMVNUAVLVRVOVSACIBCIJVQVJVPEZVMEWDVJVMVPUBWEWCVMWEVJCHZCAEZCBEZEZGZ
    EAHZACEZGZWJEZWCVPWJVJVPWFWGGZWFWHGZEZWJVKWOVNWPCAKCBKJWJWQWFWGWHCWGCALMZCW
    HCBLMZUCNOPVJWMWJACKQWNWMWFEZWMWIEZGWCWIWMWFWIWMWIWGWMWGWHUDWGWLWMCASWLWKUE
    UFUGUHWFWIWFWGWHWRWSUIUJUMWTVTXAWBWTWKWFEZWLWFEZGXBTGZVTWLWFWKWLCACUKULWLAA
    CUNULZUOXCTXBXCACWFEZEZATEZTACWFUPXHXGTXFACUQPNAURRUSXDXBVTXBUTACVAORXAWKWI
    EZWLWIEZGWKWBEZWBGWBWLWIWKWLWGWIACSWGWHLVBXEUOXIXKXJWBWIWBWKWICWAEZWBXLWICA
    BVCNCWASOZPXJWLWBEWBWLEWBWIWBWLXMPWLWBSWBWLWAACABUDVDVERVGXKWBWKWBVFVHRVGOR
    QOVI $.

  $( Lemma for biconditional commutation law.  (Contributed by NM,
     1-Dec-1999.) $)
  comanblem2 $p |- ( ( a ^ b ) ^ ( ( a == c ) ^ ( b == c ) ) ) =
                   ( ( a ^ b ) ^ c ) $=
    ( wa tb wn wo dfb 2an wf comanr1 comcom6 fh1 anass ax-r1 anidm ran dff 3tr2
    ax-r2 lan an0r 2or or0 3tr an4 anandir 3tr1 ) ABDZACEZBCEZDZDUIACDZAFZCFZDZ
    GZBCDZBFZUODZGZDZDZUICDZULVBUIUJUQUKVAACHBCHIUAAUQDZBVADZDUMURDVCVDVEUMVFUR
    VEAUMDZAUPDZGUMJGUMAUMUPACKAUPUNUOKLMVGUMVHJVGAADZCDZUMVJVGAACNOVIACAPQTAUN
    DZUODZJUODZVHJVMVLJVKUOARQOAUNUONUOUBZSUCUMUDUEVFBURDZBUTDZGURJGURBURUTBCKB
    UTUSUOKLMVOURVPJVOBBDZCDZURVRVOBBCNOVQBCBPQTBUSDZUODZVMVPJVMVTJVSUOBRQOBUSU
    ONVNSUCURUDUEIABUQVAUFABCUGUHT $.

  $( Biconditional commutation law.  (Contributed by NM, 1-Dec-1999.) $)
  comanb $p |- ( a ^ b ) C ( ( a == c ) ^ ( b == c ) ) $=
    ( wa tb wo wn wi1 lea leo lecon leror comanblem1 df-i1 comanblem2 lor ax-r2
    letr le3tr1 i1com ) ABDZACEBCEDZACFZGZUACDZFZBCHZDZUAGZUEFZUBUAUBHZUHUFUJUF
    UGIUDUIUEUAUCUAAUCABIACJRKLRABCMUKUIUAUBDZFUJUAUBNULUEUIABCOPQST $.

  $( Biconditional commutation law.  (Contributed by NM, 1-Dec-1999.) $)
  comanbn $p |- ( a ' ^ b ' ) C ( ( a == c ) ^ ( b == c ) ) $=
    ( wn wa tb comanb conb 2an ax-r1 cbtr ) ADZBDZELCDZFZMNFZEZACFZBCFZEZLMNGTQ
    ROSPACHBCHIJK $.

  ${
    mhlem.1 $e |- ( a v b ) =< ( c v d ) ' $.
    $( Lemma for Lemma 7.1 of Kalmbach, p. 91.  (Contributed by NM,
       10-Mar-2002.) $)
    mhlemlem1 $p |- ( ( ( a v b ) v c ) ^ ( a v ( c v d ) ) ) = ( a v c ) $=
      ( wo wa leo ler lecom wn letr comcom7 fh2 ancom ax-a3 anabs 3tr wf 2or
      lan comor1 lecon3 fh1rc ortha or0r ax-r2 ) ABFZCFZACDFZFGUIAGZUIUJGZFACFA
      UIUJAUIAUHCABHZIJAUJAUJKZAUHUNUMELJMNUKAULCUKAUIGAABCFZFZGAUIAOUIUPAABCPU
      AAUOQRULUHUJGZCUJGZFSCFCUJCUHCDUBUJUHUJUHKUHUJEUCJMUDUQSURCUHUJEUECDQTCUF
      RTUG $.

    $( Lemma for Lemma 7.1 of Kalmbach, p. 91.  (Contributed by NM,
       10-Mar-2002.) $)
    mhlemlem2 $p |- ( ( ( a v b ) v d ) ^ ( b v ( c v d ) ) ) = ( b v d ) $=
      ( wo wa ax-a2 ax-r5 lor 2an wn ax-r4 le3tr1 mhlemlem1 ax-r2 ) ABFZDFZBCDF
      ZFZGBAFZDFZBDCFZFZGBDFRUBTUDQUADABHISUCBCDHJKBADCQSLUAUCLEBAHUCSDCHMNOP
      $.

    $( Lemma 7.1 of Kalmbach, p. 91.  (Contributed by NM, 10-Mar-2002.) $)
    mhlem $p |- ( ( a v c ) ^ ( b v d ) ) = ( ( a ^ b ) v ( c ^ d ) ) $=
      ( wo wa comor1 comor2 com2an wn lecom comcom7 leao1 letr comcom 3tr ax-r2
      3tr1 wf fh1r fh2rc 2or lerr fh3 id mhlemlem1 mhlemlem2 ancom ax-a2 df-le2
      2an an4 lor ax-r1 or12 lan leor fh3r lecon3 com2or ax-a3 ax-r5 le2an lbtr
      leo fh2 ortha or0 df2le2 lear leid ler2an lebi ) ACFZBDFZGZABGZABFZGZCDFZ
      VSGZVRCDGZGZFZFZWAWCGZFZVRWCFVQVTWBFZWDFZWGFZWHVRWAFZVSGZWLWCGZFZWIWDWGFZ
      FVQWKWMWIWNWPVSVRWAVSABABHABIJZVSWAVSWAKZELMZUAWAWCVRWACDCDHCDIJVRWAVRWAV
      RWRVRVSWRABBNZEOLMZPUBUCVQWLVSWCFZGZWOVRWAWCVSFZGFZWLVRXDFZGZVQXCVRWAXDXA
      VRXDVRVSWCWTUDLUEZVQVSCFZAWAFZGZVSDFZBWAFZGZGZXEVQVQVQXOVQUFZXPXKVOXNVPAB
      CDEUGABCDEUHULSXOXIXLGZXJXMGZGXRXQGZXEXIXJXLXMUMXQXRUIXCXGXSXEXBXFWLXBXDW
      CVRVSFZFZXFVSWCUJYAXDXTVSWCVRVSWTUKUNUOWCVRVSUPQUQZXCXSWLXRXBXQWAABAWAAWA
      AWRAVSWRABVFEOLMPBWABWABWRBVSWRBAUREOLMPUSVSCDCVSCVSCVSKZCWAYCCDVFVSWAEUT
      ZOLMPDVSDVSDYCDWAYCDCURYDOLMPUEULUOXHSQRYBSVSWLWCVSVRWAWQWSVAWCVSWCVSWCYC
      WCWAYCCDDNZYDOLMPVGRWIWDWGVBSWJWFWGVTWBWDVBVCRWFVRWGWCWFVTTFVTVRWETVTWEVS
      WAGZTWDWBFWBWEYFWDWBWDYFWBVRVSWCWAWTYEVDVSWAUIZVEUKWBWDUJYGSVSWAEVHRUNVTV
      IVRVSWTVJQWGWCWAWCVKWCWAWCYEWCVLVMVNUCR $.
  $}

  ${
    mhlem1.1 $e |- a C b $.
    mhlem1.2 $e |- c C b $.
    $( Lemma for Marsden-Herman distributive law.  (Contributed by NM,
       10-Mar-2002.) $)
    mhlem1 $p |- ( ( a v b ) ^ ( b ' v c ) ) = ( ( a ^ b ' ) v ( b ^ c ) ) $=
      ( wo wn wa wt lan comcom2 fh1 ax-a2 wf comcom lor ax-r1 3tr comcom6 ax-r5
      df-t an1 comor2 comid comcom3 fh1r dff or0 ancom anabs 2or comorr comanr2
      3tr2 ran fh2rc leao2 df2le2 ax-r2 or0r ) ABFZBGZCFZHAVBHZBFZVCHZVDBVCHZFZ
      VDBCHZFVAVEVCVAIHVABVBFZHZVAVEIVJVABUAJVAUBVKVABHZVAVBHZFVMVLFVEVABVBABUC
      ZVABVNKLVLVMMVMVDVLBVMVDBVBHZFZVDNFZVDVBABAVBABDKOBBBUDZUEUFVQVPNVOVDBUGZ
      PQVDUHRVLBVAHBBAFZHBVABUIVAVTBABMJBAUJRUKRUNUOVFVDVCHZVGFVHBVCVDBVCVBCULS
      BVDAVBUMSUPWAVDVGVDVCVBACUQURTUSVGVIVDVGVOVIFZNVIFZVIBVBCBBVRKCBEOLWCWBNV
      OVIVSTQVIUTRPR $.
  $}

  ${
    mh.1 $e |- a C c $.
    mh.2 $e |- a C d $.
    mh.3 $e |- b C c $.
    mh.4 $e |- b C d $.
    $( Lemma for Marsden-Herman distributive law.  (Contributed by NM,
       10-Mar-2002.) $)
    mhlem2 $p |- ( ( ( a v c ) ^ ( c ' v b ' ) ) ^
                     ( ( b v d ) ^ ( a ' v d ' ) ) ) =
                 ( ( ( a ^ c ' ) ^ ( b ^ d ' ) ) v
                     ( ( c ^ b ' ) ^ ( d ^ a ' ) ) ) $=
      ( wo wn wa comcom3 mhlem1 ax-a2 ax-r2 2an leao2 leao3 ler2an oran2 lel2or
      lan anor3 lbtr mhlem ) ACICJZBJZIKZBDIZAJZDJZIZKZKAUFKZCUGKZIZBUKKZDUJKZI
      ZKUNUQKUOURKIUHUPUMUSACUGEBCGLMUMUIUKUJIZKUSULUTUIUJUKNUBBDUJHADFLMOPUNUQ
      UOURUNUQIUFBIZUKAIZKZUOURIJZUNVCUQUNVAVBUFABQAUFUKRSUQVAVBBUKUFRUKBAQSUAV
      CUOJZURJZKVDVAVEVBVFCBTDATPUOURUCOUDUEO $.

    $( Marsden-Herman distributive law.  Lemma 7.2 of Kalmbach, p. 91.
       (Contributed by NM, 10-Mar-2002.) $)
    mh $p |- ( ( a v c ) ^ ( b v d ) )
               = ( ( ( a ^ b ) v ( a ^ d ) ) v ( ( c ^ b ) v ( c ^ d ) ) ) $=
      ( wa wo leao1 leao2 ler2an leao4 lel2or wn ax-r1 ax-r2 lea ax-a3 leao3 wf
      anass an4 mhlem2 le2an leo letr leor bltr leran anor3 ax-a2 or12 3tr 3tr1
      lor ax-r4 oran3 2an ran lan dff le3tr1 le0 lebi oml3 ) ABIZADIZJZCBIZCDIZ
      JZJZACJZBDJZIZVNVQVJVQVMVHVQVIVHVOVPABCKBADLMVIVOVPADCKDABNMOVKVQVLVKVOVP
      CBAUABCDLMVLVOVPCDAUADCBNMOOVQVNPZIZUBVQCPZBPZJZAPZDPZJZIZVHVLJZPZIZIZWGW
      HIZVSUBWJVQWFIZWHIZWKWMWJVQWFWHUCQWLWGWHWLAVTIZBWDIZIZCWAIZDWCIZIZJZWGWLV
      OWBIVPWEIIWTVOVPWBWEUDABCDEFGHUERWPWGWSWPVHWGWNAWOBAVTSBWDSUFVHVLUGUHWSVL
      WGWQCWRDCWASDWCSUFVLVHUIUHOUJUKUJVRWIVQVKVIJZWGJZPZXAPZWHIZVRWIXEXCXAWGUL
      QVNXBVNVMVJJZXBVJVMUMVKVLVJJZJVKVIWGJZJXFXBXGXHVKXGVHVLVIJJZWGVIJZXHVLVHV
      IUNXJXIVHVLVITQWGVIUMUOUQVKVLVJTVKVIWGTUPRURWFXDWHWFVKPZVIPZIXDWBXKWEXLCB
      USADUSUTVKVIULRVAUPVBWGVCVDVSVEVFVGQ $.
  $}

  ${
    marsden.1 $e |- a C b $.
    marsden.2 $e |- b C c $.
    marsden.3 $e |- c C d $.
    marsden.4 $e |- d C a $.
    $( Lemma for Marsden-Herman distributive law.  (Contributed by NM,
       26-Feb-2002.) $)
    marsdenlem1 $p |- ( ( a v b ) ^ ( a ' v d ' ) )
                      = ( ( a ' ^ ( a v b ) ) v ( d ' ^ ( a v b ) ) ) $=
      ( wo wn wa ancom comorr comcom3 comcom4 comcom fh2r ax-r2 ) ABIZAJZDJZIZK
      UBSKTSKUASKISUBLTSUAASABMNUATDAHOPQR $.

    $( Lemma for Marsden-Herman distributive law.  (Contributed by NM,
       26-Feb-2002.) $)
    marsdenlem2 $p |- ( ( c v d ) ^ ( b ' v c ' ) )
                      = ( ( ( b ' ^ c ) v ( c ' ^ d ) ) v ( b ' ^ d ) ) $=
      ( wo wn wa ancom comorr comcom3 comcom4 comcom fh2 wf ax-r2 3tr fh2rc dff
      comcom6 comid comcom2 ax-r5 ax-r1 or0r 2or or32 ) CDIZBJZCJZIZKUNUKKULUKK
      ZUMUKKZIZULCKZUMDKZIULDKZIZUKUNLUMUKULCUKCDMNULUMBCFOPZUAUQURUTIZUSIVAUOV
      CUPUSCULDCULVBUCGQUPUMCKZUSIZRUSIZUSCUMDCCCUDUEGQVFVERVDUSRCUMKVDCUBCUMLS
      UFUGUSUHTUIURUTUSUJST $.

    $( Lemma for Marsden-Herman distributive law.  (Contributed by NM,
       26-Feb-2002.) $)
    marsdenlem3 $p |- ( ( ( b ' ^ c ) v ( c ' ^ d ) ) ^ ( b ^ d ' ) ) = 0 $=
      ( wn wa wo wf lea lecom comcom7 comcom an4 dff ax-r1 3tr lecon lear oran2
      lel lerr lbtr fh1r ancom ax-r2 ran an0r lan an0 2or or0 ) BIZCJZCIZDJZKBD
      IZJZJUQVAJZUSVAJZKLLKLVAUQUSUQVAUQVAUQVAIZUPVDCVABBUTMUAUDNOPUSVAUSVAUSVD
      USUPDKVDUSDUPURDUBUEBDUCUFNOPUGVBLVCLVBUPBJZCUTJZJLVFJLUPCBUTQVELVFVEBUPJ
      ZLUPBUHLVGBRSUIUJVFUKTVCURBJZDUTJZJVHLJLURDBUTQVILVHLVIDRSULVHUMTUNLUOT
      $.

    $( Lemma for Marsden-Herman distributive law.  (Contributed by NM,
       26-Feb-2002.) $)
    marsdenlem4 $p |- ( ( ( a ' ^ b ) v ( a ^ d ' ) ) ^ ( b ' ^ d ) ) = 0 $=
      ( wn wa wo wf lbtr lecom comcom7 ancom lan an4 dff 3tr leao3 fh1r an0 2or
      oran1 leao4 oran2 ax-r1 ax-r2 or0 ) AIZBJZADIZJZKBIZDJZJULUPJZUNUPJZKLLKL
      UPULUNUPULUPULIZUPAUOKUSUODAUAABUEMNOUPUNUPUNIZUPUKDKUTDUOUKUFADUGMNOUBUQ
      LURLUQULDUOJZJUKDJZBUOJZJZLUPVAULUODPQUKBDUORVDVBLJZLVEVDLVCVBBSQUHVBUCUI
      TURAUOJZUMDJZJVFLJLAUMUODRVGLVFVGDUMJZLUMDPLVHDSUHUIQVFUCTUDLUJT $.

    $( Marsden-Herman distributive law.  Corollary 3.3 of Beran, p. 259.
       (Contributed by NM, 10-Mar-2002.) $)
    mh2 $p |- ( ( a v b ) ^ ( c v d ) )
               = ( ( ( a ^ c ) v ( a ^ d ) ) v ( ( b ^ c ) v ( b ^ d ) ) ) $=
      ( comcom mh ) ACBDEDAHIBCFIGJ $.
  $}

  $( Lemma for OML proof of Mladen's conjecture, (Contributed by NM,
     10-Mar-2002.) $)
  mlaconjolem $p |- ( ( a == c ) v ( b == c ) ) =<
                   ( ( c ^ ( a v b ) ) v ( c ' ^ ( a ' v b ' ) ) ) $=
    ( tb wo wa wi2 wi1 wn orbile df-i2 oran3 ran lor ax-r1 ax-r2 df-i1 2an 3tr
    ancom comor1 comcom2 leao1 lecom comcom fh1 omlan df2le2 2or ax-a2 lbtr ) A
    CDBCDEABFZCGZCABEZHZFZCUNFZCIZAIBIEZFZEZABCJUPCUSURFZEZURUQEZFVCURFZVCUQFZE
    ZVAUMVCUOVDUMCULIZURFZEZVCULCKVCVJVBVICUSVHURABLMNOPCUNQRVCURUQVCCCVBUAUBUQ
    VCUQVCCUNVBUCZUDUEUFVGUTUQEVAVEUTVFUQVECUTEZURFURVLFUTVCVLURVBUTCUSURTNMVLU
    RTCUSUGSVFUQVCFUQVCUQTUQVCVKUHPUIUTUQUJPSUK $.

  $( OML proof of Mladen's conjecture.  (Contributed by NM, 10-Mar-2002.) $)
  mlaconjo $p |- ( ( a == b ) ^ ( ( a == c ) v ( b == c ) ) ) =<
                   ( a == c ) $=
    ( tb wo wa wn dfb le2an lea leao1 lbtr lecom comcom7 lor ax-r2 an12 lan dff
    wf bile mlaconjolem le2or oran leor df-a oran1 lear oran3 ax-r1 an0 3tr or0
    mh ax-r5 or0r 2or le3tr1 letr ) ABDZACDZBCDEZFABFZAGZBGZFZEZCABEZFZCGZVDVEE
    ZFZEZFZVAUTVGVBVMUTVGABHUAABCUBIVCVIFZVFVLFZEZACFZVDVJFZEVNVAVOVRVPVSVCAVIC
    ABJCVHJIVFVDVLVJVDVEJVJVKJIUCVNVOVCVLFZEZVFVIFZVPEZEVQVCVIVFVLVCVFVCVFGZVCV
    HWDABBKABUDZLMNVCVLVCVLGZVCCVCEZWFVCCUEWGCVKGZEZWFVCWHCABUFOCVKUGZPLMNVIVFV
    IWDVIVHWDCVHUHWELMNVIVLVIWFVIWIWFCVHWHKWJLMNUNWAVOWCVPWAVOTEVOVTTVOVTVJVCVK
    FZFVJTFTVCVJVKQWKTVJWKVCVCGZFZTVKWLVCABUIRTWMVCSUJPRVJUKULOVOUMPWCTVPEVPWBT
    VPWBCVFVHFZFCTFTVFCVHQWNTCWNVFWDFZTVHWDVFWERTWOVFSUJPRCUKULUOVPUPPUQPACHURU
    S $.

  $( Distributive law for identity.  (Contributed by NM, 17-Mar-2002.) $)
  distid $p |- ( ( a == b ) ^ ( ( a == c ) v ( b == c ) ) ) =
             ( ( ( a == b ) ^ ( a == c ) ) v ( ( a == b ) ^ ( b == c ) ) ) $=
    ( tb wo wa lea mlaconjo ler2an bicom ax-a2 2an bltr ler2or ledi lebi ) ABDZ
    ACDZBCDZEZFZQRFZQSFZEUAUBUCUAQRQTGZABCHIUAQSUDUABADZSREZFSQUETUFABJRSKLBACH
    MINQRSOP $.

  $( Corollary of Marsden-Herman Lemma.  (Contributed by NM, 26-Jun-2003.) $)
  mhcor1 $p |- ( ( ( ( a ->1 b ) ^ ( b ->2 c ) ) ^
                    ( c ->1 d ) ) ^ ( d ->2 a ) ) =
       ( ( ( a == b ) ^ ( b == c ) ) ^ ( c == d ) ) $=
    ( wa wn wo tb anass ancom ax-r2 lbtr lecom comcom7 wf ran lan 3tr ax-r1 2or
    wi2 wi1 imp3 2an leao3 oran comcom leao2 mh2 an4 3tr1 dff an0r 3tr2 an0 or0
    or0r ax-a2 bi4 ) BCUAZCDUBZEZABUBZEZDAUAZEZABEZCEDEZAFZBFZEZCFZEDFZEZGZVCUT
    EVAEZVEEABHBCHECDHEVFVBVCVEEZEVJVLEZCDEZGZVMVIEZVGGZEZVOVBVCVEIVBVTVQWBBCDU
    CVQVEVCEWBVCVEJDABUCKUDWCVRWAEZVRVGEZGZVSWAEZVSVGEZGZGVNVHGVOVRVSWAVGVSVRVS
    VRVSVRFZVSBCGZWJCDBUEBCUFZLMNUGVSWAVSWAFZVSDAGZWMDCAUHDAUFZLMNVGWAVGWAVGWMV
    GWNWMABDUEWOLMNUGVGVRVGWJVGWKWJBACUHWLLMNUIWFVNWIVHWFVNOGVNWDVNWEOVLVMEZVKE
    ZVKWPEWDVNWPVKJWDVLVJEZWAEWPVJVIEZEWQVRWRWAVJVLJPVLVJVMVIUJWSVKWPVJVIJQRVKV
    LVMIUKWEVGVREABVREZEZOVRVGJABVRIXAAOEOWTOABVJEZVLEZOVLEZWTOXDXCOXBVLBULPSBV
    JVLIVLUMUNQAUOKRTVNUPKWIOVHGVHWGOWHVHWGCDWAEZECOEOCDWAIXEOCXEDVMEZVIEZOXGXE
    DVMVIISOXGOOVIEZXGXHOVIUMSOXFVIDULPKSKQCUORWHVGVSEZVHVSVGJVHXIVGCDISKTVHUQK
    TVNVHURRRVPVDVEVPVCVBEVDVCUTVAIVCVBJKPABCDUSUK $.

  $( Equation (3.29) of "Equations, states, and lattices..." paper.  This shows
     that it holds in all OMLs, not just 4GO. (Contributed by NM,
     22-Jun-2003.) $)
  oago3.29 $p |- ( ( a ->1 b ) ^ ( ( b ->2 c ) ^ ( c ->1 a ) ) )
                 =< ( a == c ) $=
    ( wi1 wi2 wa tb anass i2id 2an ax-r1 an1 mhcor1 3tr2 lear bicom lbtr bltr
    wt ) ABDZBCEZCADZFFZABGBCGFZCAGZFZACGZUCSFZTUAFUBFZAAEZFZUCUFUKUHUIUCUJSTUA
    UBHAIJKUCLABCAMNUFUEUGUDUEOCAPQR $.

  $( 4-variable extension of Equation (3.21) of "Equations, states, and
     lattices..." paper.  This shows that it holds in all OMLs, not just 4GO.
     (Contributed by NM, 26-Jun-2003.) $)
  oago3.21x $p |- ( ( ( ( a ->5 b ) ^ ( b ->5 c ) ) ^
                    ( c ->5 d ) ) ^ ( d ->5 a ) ) =
       ( ( ( a == b ) ^ ( b == c ) ) ^ ( c == d ) ) $=
    ( wi5 wa tb wi1 wi2 i5lei1 i5lei2 le2an mhcor1 lbtr eqtr4 u5lembi ax-r1 lea
    leid bltr bicom ler2an letr lebi ) ABEZBCEZFZCDEZFZDAEZFZABGZBCGZFZCDGZFZUK
    ABHZBCIZFZCDHZFZDAIZFUPUIVAUJVBUGUSUHUTUEUQUFURABJBCKLCDJLDAKLABCDMNUPUPDAG
    ZFUKUPUPVCUPSUPADGVCABCDOADUANUBUPUIVCUJUNUGUOUHULUEUMUFULUEBAEZFZUEVEULABP
    QUEVDRTUMUFCBEZFZUFVGUMBCPQUFVFRTLUOUHDCEZFZUHVIUOCDPQUHVHRTLVCUJADEZFZUJVK
    VCDAPQUJVJRTLUCUD $.

  ${
    cancel.1 $e |- ( ( d v ( a ->1 c ) ) ->1 c ) = ( ( d v ( b ->1 c ) ) ->1 c
        ) $.
    $( Lemma for cancellation law eliminating ` ->1 ` consequent.  (Contributed
       by NM, 21-Feb-2002.) $)
    cancellem $p |- ( d v ( a ->1 c ) ) =< ( d v ( b ->1 c ) ) $=
      ( wi1 wo wn i1abs ax-r1 leo df-i1 ax-r2 lbtr lecon2 ran 3tr lel2or bltr
      wa leor lear ler2an coman2 coman1 comcom2 fh2rc 3tr1 leao4 lerr lor ax-r4
      id an12 anor1 lan anor3 ancom anass le3tr1 lea lel letr ) DACFGZVDCFZHZVD
      CTZGZDBCFZGZVHVDVDCIJVFVJVGVJVEVJHZVKVJCTZGZVEVKVLKVEVMVEVJCFZVMEVJCLZMJN
      OVGVNCTZVJVGVNCVGVDHZVGGZVNVGVQUAVRVEVNVEVRVDCLJEMNVDCUBUCVPVKCTZVLCTZGZV
      JVMCTWAVPWAVLCVKVJCUDVLVJVJCUEUFUGVNVMCVOPWAUMUHVSVJVTDHZBCTZHZTZWCTZDBHZ
      WCGZGZVSVJWFWHDWCWEWGUIUJVSWEBTZCTWFVKWJCVKWIHZBWETZWJVJWIVIWHDBCLUKZULWL
      WKWLWBBWDTZTWBWHHZTWKBWBWDUNWNWOWBBWCUOUPDWHUQQJBWEURQPWEBCUSMWMUTVLVJCVJ
      CVAVBRSVCRS $.

    $( Cancellation law eliminating ` ->1 ` consequent.  (Contributed by NM,
       21-Feb-2002.) $)
    cancel $p |- ( d v ( a ->1 c ) ) = ( d v ( b ->1 c ) ) $=
      ( wi1 wo cancellem ax-r1 lebi ) DACFGZDBCFGZABCDEHBACDKCFLCFEIHJ $.
  $}

  ${
    kb10iii.1 $e |- b ' =< ( a ->1 c ) $.
    $( Exercise 10(iii) of Kalmbach p. 30 (in a rewritten form).  (Contributed
       by NM, 9-Jan-2004.) $)
    kb10iii $p |- c ' =< ( a ->1 b ) $=
      ( wi1 wn wo wa ud1lem0c omln u1lem9b lel2or bltr lelan ancom lbtr u1lemaa
      womaon le3tr2 lear letr lecon2 ) ABEZCUCFAAFZBFZGZHZCABIUGACHZCAUDUGGZHZA
      CEZAHZUGUHUJAUKHULUIUKAUIUFUKAUEJUDUKUEACKDLMNAUKOPAUERACQSACTUAMUB $.
  $}

  ${
    e2ast2.1 $e |- a =< b ' $.
    e2ast2.2 $e |- c =< d ' $.
    e2ast2.3 $e |- a =< c ' $.
    $( Show that the E*_2 derivative on p. 23 of Mayet, "Equations holding in
       Hilbert lattices" IJTP 2006, holds in all OMLs.  (Contributed by NM,
       24-Jun-2006.) $)
    e2ast2 $p |- ( ( a v b ) ^ ( c v d ) ) =< ( ( b v d ) v ( a v c ) ' ) $=
      ( wo wa wn leror lecon3 lecom comcom df-le2 ax-r2 ax-r1 lor ax-a3 ax-r5
      le2an comcom2 fh4c lan anor3 leao4 com2or fh4 or32 lear 3tr2 df2le2 ax-a2
      2an ancom 3tr 3tr1 lbtr ) ABHZCDHZICJZBHZAJZDHZIZBDHACHJZHZUSVBUTVDAVABGK
      CVCDACGLKUABDVCHZVAIZHZBDVFHZHVEVGVIVKBVIDVCVAIZHZVKVMVIVMVHDVAHZIVIVADVC
      DVADVACDFLZMNZVAAAVAAVAGMNUBZUCVNVAVHDVAVOOUDPQVLVFDACUERPRVEBVCIZVIHZVJV
      SVEVSVRVHHZVRVAHZIVDVBIVEVHVRVAVRVHVRVHVCBDUFMNVAVHVADVCVPVQUGNUHVTVDWAVB
      VRDHVCHVRVCHZDHVTVDVRDVCUIVRDVCSWBVCDVRVCBVCUJOTUKWABVAHVBVRBVABVCABELULZ
      TBVAUMPUNVDVBUOUPQVRBVIWCTPBDVFSUQUR $.
  $}

  ${
    e2ast.1 $e |- a =< b ' $.
    e2ast.2 $e |- c =< d ' $.
    e2ast.3 $e |- r =< a ' $.
    e2ast.4 $e |- a =< c ' $.
    e2ast.5 $e |- c =< r ' $.
    $( Lemma towards a possible proof that E*_2 on p. 23 of Mayet, "Equations
       holding in Hilbert lattices" IJTP 2006, holds in all OMLs.  (Contributed
       by NM, 25-Jun-2006.) $)
    e2astlem1 $p |- ( ( ( a v b ) ^ ( c v d ) ) ^ ( ( a v c ) v r ) ) =
                   ( ( a v ( b ^ ( c v r ) ) ) ^ ( c v ( d ^ ( a v r ) ) ) ) $=
      ( wo wa ler lecom wn comcom7 fh2r df2le2 wf ax-r2 leo ax-a3 comcom com2or
      anandir lan fh2 lecon3 ortha ax-r5 or0r 3tr 2or leor or32 fh2c lor or0
      2an ) ABKZCDKZLACKZEKZLUTVCLZVAVCLZLABCEKZLZKZCDAEKZLZKZLUTVAVCUEVDVHVEVK
      VDAVCLZBVCLZKVHAVCBAVCAVBEACUAMZNABABOFNPZQVLAVMVGAVCVNRVMBAVFKZLZSVGKZVG
      VCVPBACEUBUFVQBALZVGKVRABVFVOACEACACOINPZEAEAEAOHNPUCUDUGVSSVGBAABFUHUIUJ
      TVGUKULUMTVECVCLZDVCLZKVKCVCDCVCCVBECAUNMZNCDCDOGNPZQWACWBVJCVCWCRWBDVICK
      ZLVJDCLZKZVJVCWEDACEUOUFCDVIWDCAEACVTUCCECEOJNPUDUPWGVJSKVJWFSVJDCCDGUHUI
      UQVJURTULUMTUST $.

    $( Show that E*_2 on p. 23 of Mayet, "Equations holding in Hilbert
       lattices" IJTP 2006, holds in all OMLs. $)
$(
    e2ast $p |- ( ( ( a v b ) ^ ( c v d ) ) ^ ( ( a v c ) v r ) ) =<
                ( ( b v d ) v r ) $=
      ( wo wa wn ax-a3 comor1 bctr comcom3 comcom7 comorr2 comcom6 com2an mh2
      ax-r2 lbtr wf anass ax-r1 anor3 ran ancom dff lan an0 an0r le0 bltr
      lel2or letr ) ABKCDKLACKEKLZBEKZCKZMZDEBMZKZLZLZVBCEAKMZLZLZKZBVELZBVHLZK
      ZKZBDKEKZUS?VN??VBBKVEVHKLVN?VBBVEVHVABVABECKZKBBECNBVPOPQBDVDBD?RBVDEVCS
      TUA??UBUCUDVJVOVMVFVOVI?VIUEVOVIVBCLZVGLZUEVRVIVBCVGUFUGVRUEVGLUEVQUEVGVQ
      UTMZCMZLZCLZUEWBVQWAVBCUTCUHUIUGWBVSVTCLZLZUEVSVTCUFWDVSUELUEWCUEVSWCCVTL
      ZUEVTCUJUEWECUKUGUCULVSUMUCUCUCUIVGUNUCUCVOUOUPUQVKVOVL??UQUQUR $.
$)
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
   OML Lemmas for studying Godowski equations.
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    govar.1 $e |- a =< b ' $.
    govar.2 $e |- b =< c ' $.
    $( Lemma for converting n-variable Godowski equations to 2n-variable
       equations.  (Contributed by NM, 19-Nov-1999.) $)
    govar $p |- ( ( a v b ) ^ ( a ->2 c ) ) =< ( b v c ) $=
      ( wo wi2 wa wn df-i2 lan ax-a2 ran lecom comcom7 comcom comcom2 lor 3tr
      wf com2an com2or fh2r ax-r2 coman1 fh2c dff ax-r1 anass an0r 3tr2 or0 lea
      coman2 lear le2or bltr ) ABFZACGZHZBCAIZCIZHZFZHZACHZFZBCFUTURVDHZVEAVDHZ
      FZVGUSVDURACJKVHBAFZVDHVJURVKVDABLMBVDABCVCBCBVBENZOBVAVBBAABABABIDNOPZQV
      LUAUBVMUCUDVIVFVEVIVFAVCHZFVFTFVFVCACVCAVAVBUEOVCCVAVBUNOUFVNTVFAVAHZVBHZ
      TVBHZVNTVQVPTVOVBAUGMUHAVAVBUIVBUJUKRVFULSRSVEBVFCBVDUMACUOUPUQ $.

    $( Lemma for converting n-variable to 2n-variable Godowski equations.
       (Contributed by NM, 19-Nov-1999.) $)
    govar2 $p |- ( a v b ) =< ( c ->2 a ) $=
      ( wo wn wa wi2 lecon3 ler2an lelor df-i2 ax-r1 lbtr ) ABFACGZAGZHZFZCAIZB
      RABPQEABDJKLTSCAMNO $.

    ${
      gon2n.3 $e |- ( ( c ->2 a ) ^ d ) =< ( a ->2 c ) $.
      gon2n.4 $e |- e =< d $.
      $( Lemma for converting n-variable to 2n-variable Godowski equations.
         (Contributed by NM, 19-Nov-1999.) $)
      gon2n $p |- ( ( a v b ) ^ e ) =< ( b v c ) $=
        ( wo wa wi2 lea govar2 le2an letr ler2an govar ) ABJZEKZSACLZKBCJTSUASE
        MTCALZDKUASUBEDABCFGNIOHPQABCFGRP $.
    $}
  $}

  ${
    go2n4.1 $e |- a =< b ' $.
    go2n4.2 $e |- b =< c ' $.
    go2n4.3 $e |- c =< d ' $.
    go2n4.4 $e |- d =< e ' $.
    go2n4.5 $e |- e =< f ' $.
    go2n4.6 $e |- f =< g ' $.
    go2n4.7 $e |- g =< h ' $.
    go2n4.8 $e |- h =< a ' $.
    ${
      go2n4.9 $e |- ( ( ( c ->2 a ) ^ ( a ->2 g ) ) ^
                  ( ( g ->2 e ) ^ ( e ->2 c ) ) ) =< ( a ->2 c ) $.
      $( 8-variable Godowski equation derived from 4-variable one.  The last
         hypothesis is the 4-variable Godowski equation.  (Contributed by NM,
         19-Nov-1999.) $)
      go2n4 $p |- ( ( ( a v b ) ^ ( c v d ) ) ^
                ( ( e v f ) ^ ( g v h ) ) ) =< ( b v c ) $=
        ( wo wa wi2 anass ancom lan ax-r2 an32 ax-r1 bltr govar2 le2an gon2n )
        ABRZCDRZSEFRZGHRZSZSZUKUOULSZSZBCRUPUKULUOSZSURUKULUOUAUSUQUKULUOUBUCUD
        ABCGETZAGTZSZECTZSZUQIJCATZVDSZVEVASUTVCSZSZACTVHVFVHVEVAVGSZSVFVEVAVGU
        AVIVDVEVIVGVASVDVAVGUBUTVCVAUEUDUCUDUFQUGUOVBULVCUMUTUNVAEFGMNUHGHAOPUH
        UICDEKLUHUIUJUG $.
    $}

    ${
      gomaex4.9 $e |- ( ( ( a ->2 g ) ^ ( g ->2 e ) ) ^ ( (
                        e ->2 c ) ^ ( c ->2 a ) ) ) =< ( g ->2 a ) $.
      gomaex4.10 $e |- ( ( ( e ->2 c ) ^ ( c ->2 a ) ) ^ ( (
                        a ->2 g ) ^ ( g ->2 e ) ) ) =< ( c ->2 e ) $.
      $( Proof of Mayet Example 4 from 4-variable Godowski equation.  R. Mayet,
         "Equational bases for some varieties of orthomodular lattices related
         to states," Algebra Universalis 23 (1986), 167-195.  (Contributed by
         NM, 19-Nov-1999.) $)
      gomaex4 $p |- ( ( ( ( a v b ) ^ ( c v d ) ) ^
 ( ( e v f ) ^ ( g v h ) ) ) ^ ( ( a v h ) ->1 ( d v e ) ' ) ) = 0 $=
        ( wo wa wn wi1 wf go2n4 an4 ancom ran ax-r2 3tr ax-a2 le3tr1 lan ler2an
        2an bltr leran go1 lbtr le0 lebi ) ABSZCDSZTZEFSZGHSZTZTZAHSZDESZUAUBZT
        ZUCVKVHVITZVJTUCVGVLVJVGVHVIVEVATZVBVDTZTZHASVGVHGHABCDEFOPIJKLMNQUDVGV
        AVDTZVBVETZTZVEVBTZVPTZVOVAVBVDVEUEVRVQVPTVTVPVQUFVQVSVPVBVEUFUGUHVEVBV
        AVDUEUIAHUJUKVGVNVMTZVIVGVAVETZVDVBTZTZVOWAVGVCVEVDTZTWBVNTWDVFWEVCVDVE
        UFULVAVBVEVDUEVNWCWBVBVDUFULUIWBVMWCVNVAVEUFVDVBUFUNVMVNUFUICDEFGHABKLM
        NOPIJRUDUOUMUPVHVIUQURVKUSUT $.
    $}
  $}

  ${
    go2n6.1 $e |- g =< h ' $.
    go2n6.2 $e |- h =< i ' $.
    go2n6.3 $e |- i =< j ' $.
    go2n6.4 $e |- j =< k ' $.
    go2n6.5 $e |- k =< m ' $.
    go2n6.6 $e |- m =< n ' $.
    go2n6.7 $e |- n =< u ' $.
    go2n6.8 $e |- u =< w ' $.
    go2n6.9 $e |- w =< x ' $.
    go2n6.10 $e |- x =< y ' $.
    go2n6.11 $e |- y =< z ' $.
    go2n6.12 $e |- z =< g ' $.
    go2n6.13 $e |- ( ( ( i ->2 g ) ^ ( g ->2 y ) ) ^
                     ( ( ( y ->2 w ) ^ ( w ->2 n ) ) ^
                       ( ( n ->2 k ) ^ ( k ->2 i ) ) ) ) =< ( g ->2 i ) $.
    $( 12-variable Godowski equation derived from 6-variable one.  The last
       hypothesis is the 6-variable Godowski equation.  (Contributed by NM,
       29-Nov-1999.) $)
    go2n6 $p |- ( ( ( g v h ) ^ ( i v j ) ) ^
                  ( ( ( k v m ) ^ ( n v u ) ) ^
                    ( ( w v x ) ^ ( y v z ) ) ) ) =< ( h v i ) $=
      ( wo anass ancom lan 3tr ran ax-r2 ax-r1 3tr2 3tr1 wi2 govar2 le2an gon2n
      wa bltr ) ABUFZECUFZUTDFUFZGHUFZUTZIJUFZKLUFZUTZUTZUTZVBVHVGVEUTZVDVCUTZU
      TZUTZUTZBEUFVKVBVHUTVNUTZVPVBVCVJUTZUTVPVKVQVRVOVBVCVFUTZVIUTZVNVHUTZVRVO
      WAVTWAVSVGUTZVHUTVTVNWBVHVNVGVEVMUTZUTVGVSUTWBVGVEVMUGWCVSVGWCVEVCVDUTZUT
      WDVEUTVSVMWDVEVDVCUHUIVEWDUHVCVDVEUGUJUIVGVSUHUJUKVSVGVHUGULUMVCVFVIUGVNV
      HUHUNUIVBVCVJUGVBVHVNUGZUOWEULABEAKUPZKIUPZIGUPZUTZGDUPZDEUPZUTZUTZUTZVOM
      NEAUPZWNUTZWOWFUTWMUTZAEUPWQWPWOWFWMUGUMUEVAVHWFVNWMKLAUCUDUQVLWIVMWLVGWG
      VEWHIJKUAUBUQGHISTUQURVDWJVCWKDFGQRUQECDOPUQURURURUSVA $.
  $}

  ${
    gomaex3h1.1 $e |- a =< b ' $.
    gomaex3h1.12 $e |- g = a $.
    gomaex3h1.13 $e |- h = b $.
    $( Hypothesis for Godowski 6-var -> Mayet Example 3.  (Contributed by NM,
       29-Nov-1999.) $)
    gomaex3h1 $p |- g =< h ' $=
      ( wn ax-r4 le3tr1 ) ABHCDHEFDBGIJ $.
  $}

  ${
    gomaex3h2.2 $e |- b =< c ' $.
    gomaex3h2.13 $e |- h = b $.
    gomaex3h2.14 $e |- i = c $.
    $( Hypothesis for Godowski 6-var -> Mayet Example 3.  (Contributed by NM,
       29-Nov-1999.) $)
    gomaex3h2 $p |- h =< i ' $=
      ( wn ax-r4 le3tr1 ) ABHCDHEFDBGIJ $.
  $}

  ${
    gomaex3h3.14 $e |- i = c $.
    gomaex3h3.15 $e |- j = ( c v d ) ' $.
    $( Hypothesis for Godowski 6-var -> Mayet Example 3.  (Contributed by NM,
       29-Nov-1999.) $)
    gomaex3h3 $p |- i =< j ' $=
      ( wo wn leo ax-a1 lbtr ax-r4 le3tr1 ) AABGZHZHZDCHANPABINJKECOFLM $.
  $}

  ${
    gomaex3h4.11 $e |- r = ( ( p ' ->1 q ) ' ^ ( c v d ) ) $.
    gomaex3h4.15 $e |- j = ( c v d ) ' $.
    gomaex3h4.16 $e |- k = r $.
    $( Hypothesis for Godowski 6-var -> Mayet Example 3.  (Contributed by NM,
       29-Nov-1999.) $)
    gomaex3h4 $p |- j =< k ' $=
      ( wo wn wi1 wa lear bltr lecon ax-r4 le3tr1 ) ABKZLGLCDLGTGELFMLZTNTHUATO
      PQIDGJRS $.
  $}

  ${
    gomaex3h5.11 $e |- r = ( ( p ' ->1 q ) ' ^ ( c v d ) ) $.
    gomaex3h5.16 $e |- k = r $.
    gomaex3h5.17 $e |- m = ( p ' ->1 q ) $.
    $( Hypothesis for Godowski 6-var -> Mayet Example 3.  (Contributed by NM,
       29-Nov-1999.) $)
    gomaex3h5 $p |- k =< m ' $=
      ( wn wi1 wo wa lea bltr ax-r4 le3tr1 ) GEKFLZKZCDKGTABMZNTHTUAOPIDSJQR $.
  $}

  ${
    gomaex3h6.17 $e |- m = ( p ' ->1 q ) $.
    gomaex3h6.18 $e |- n = ( p ' ->1 q ) ' $.
    $( Hypothesis for Godowski 6-var -> Mayet Example 3.  (Contributed by NM,
       29-Nov-1999.) $)
    gomaex3h6 $p |- m =< n ' $=
      ( wn wi1 leid ax-a1 lbtr ax-r4 le3tr1 ) CGDHZNGZGZABGNNPNINJKEBOFLM $.
  $}

  ${
    gomaex3h7.18 $e |- n = ( p ' ->1 q ) ' $.
    gomaex3h7.19 $e |- u = ( p ' ^ q ) $.
    $( Hypothesis for Godowski 6-var -> Mayet Example 3.  (Contributed by NM,
       29-Nov-1999.) $)
    gomaex3h7 $p |- n =< u ' $=
      ( wn wi1 wa wo leor df-i1 ax-r1 lbtr lecon ax-r4 le3tr1 ) BGZCHZGRCIZGADG
      TSTRGZTJZSTUAKSUBRCLMNOEDTFPQ $.
  $}

  ${
    gomaex3h8.19 $e |- u = ( p ' ^ q ) $.
    gomaex3h8.20 $e |- w = q ' $.
    $( Hypothesis for Godowski 6-var -> Mayet Example 3.  (Contributed by NM,
       29-Nov-1999.) $)
    gomaex3h8 $p |- u =< w ' $=
      ( wn wa lear ax-a1 lbtr ax-r4 le3tr1 ) AGZBHZBGZGZCDGOBQNBIBJKEDPFLM $.
  $}

  ${
    gomaex3h9.20 $e |- w = q ' $.
    gomaex3h9.21 $e |- x = q $.
    $( Hypothesis for Godowski 6-var -> Mayet Example 3.  (Contributed by NM,
       29-Nov-1999.) $)
    gomaex3h9 $p |- w =< x ' $=
      ( wn leid ax-r4 le3tr1 ) AFZJBCFJGDCAEHI $.
  $}

  ${
    gomaex3h10.10 $e |- q = ( ( e v f ) ->1 ( b v c ) ' ) ' $.
    gomaex3h10.21 $e |- x = q $.
    gomaex3h10.22 $e |- y = ( e v f ) ' $.
    $( Hypothesis for Godowski 6-var -> Mayet Example 3.  (Contributed by NM,
       29-Nov-1999.) $)
    gomaex3h10 $p |- x =< y ' $=
      ( wo wn wa lea wi1 df-i1 ax-r4 ax-r1 ax-r2 le3tr1 anor1 ax-a1 ) ECDKZLZLZ
      FGLUCUCABKLZMZLZMZUCEUEUCUHNEUCUFOZLZUIHUKUDUGKZLZUIUJULUCUFPQUIUMUCUGUAR
      SSUCUEUCUBRTIGUDJQT $.
  $}

  ${
    gomaex3h11.22 $e |- y = ( e v f ) ' $.
    gomaex3h11.23 $e |- z = f $.
    $( Hypothesis for Godowski 6-var -> Mayet Example 3.  (Contributed by NM,
       29-Nov-1999.) $)
    gomaex3h11 $p |- y =< z ' $=
      ( wo wn leor lecon ax-r4 le3tr1 ) ABGZHBHCDHBMBAIJEDBFKL $.
  $}

  ${
    gomaex3h12.6 $e |- f =< a ' $.
    gomaex3h12.12 $e |- g = a $.
    gomaex3h12.23 $e |- z = f $.
    $( Hypothesis for Godowski 6-var -> Mayet Example 3.  (Contributed by NM,
       29-Nov-1999.) $)
    gomaex3h12 $p |- z =< g ' $=
      ( wn ax-r4 le3tr1 ) BAHDCHEGCAFIJ $.
  $}

  ${
    gomaex3lem1.3 $e |- c =< d ' $.
    $( Lemma for Godowski 6-var -> Mayet Example 3.  (Contributed by NM,
       29-Nov-1999.) $)
    gomaex3lem1 $p |- ( c v ( c v d ) ' ) = d ' $=
      ( wn wa wo comid comcom2 lecom fh3 anor3 lor wt ancom df-le2 df-t 2an an1
      ax-r1 3tr 3tr2 ) AADZBDZEZFAUBFZAUCFZEZAABFDZFUCAUBUCAAAGHAUCCIJUDUHAABKL
      UGUFUEEZUCMEZUCUEUFNUJUIUCUFMUEUFUCAUCCOSAPQSUCRTUA $.
  $}

  ${
    gomaex3lem2.5 $e |- e =< f ' $.
    $( Lemma for Godowski 6-var -> Mayet Example 3.  (Contributed by NM,
       29-Nov-1999.) $)
    gomaex3lem2 $p |- ( ( e v f ) ' v f ) = e ' $=
      ( wo wn wt lecon3 lecom comid comcom2 fh3r anor3 ax-r5 ax-r1 anabs df2le1
      wa leid lel2or ax-r2 lebi df-t ax-a2 2an 3tr1 an1 ) ABDEZBDZAEZFQZUIUIBEZ
      QZBDZUIBDZUKBDZQUHUJBUIUKBUIABCGZHBBBIJKUMUHULUGBABLMNUIUNFUOUIUNUIUNUIBO
      PUIUIBUIRUPSUAFBUKDUOBUBBUKUCTUDUEUIUFT $.
  $}

  $( Lemma for Godowski 6-var -> Mayet Example 3.  (Contributed by NM,
     29-Nov-1999.) $)
  gomaex3lem3 $p |- ( ( p ' ->1 q ) ' v ( p ' ^ q ) ) = p ' $=
    ( wn wi1 wa wo anor1 ax-r1 df-i1 ax-r4 3tr1 ax-r5 coman1 comid comcom2 fh3r
    id wt orabs ax-r2 ax-a2 df-t 2an an1 3tr ) ACZBDZCZUFBEZFUFUICZEZUIFUFUIFZU
    JUIFZEZUFUHUKUIUFCUIFZCZUKUHUKUKUPUFUIGHUGUOUFBIJUKQKLUIUFUJUFBMUIUIUINOPUN
    UFREUFULUFUMRUFBSUMUIUJFZRUJUIUARUQUIUBHTUCUFUDTUE $.

  ${
    gomaex3lem4.9 $e |- p = ( ( a v b ) ->1 ( d v e ) ' ) ' $.
    $( Lemma for Godowski 6-var -> Mayet Example 3.  (Contributed by NM,
       29-Nov-1999.) $)
    gomaex3lem4 $p |- ( ( a v b ) ^ ( d v e ) ' ) =< p ' $=
      ( wo wn wa leor wi1 ax-a1 df-i1 ax-r1 ax-r4 3tr1 lbtr ) ABGZCDGHZIZRHZTGZ
      EHZTUAJRSKZUDHZHUBUCUDLUDUBRSMNEUEFOPQ $.
  $}

  ${
    gomaex3lem5.1 $e |- a =< b ' $.
    gomaex3lem5.2 $e |- b =< c ' $.
    gomaex3lem5.3 $e |- c =< d ' $.
    gomaex3lem5.5 $e |- e =< f ' $.
    gomaex3lem5.6 $e |- f =< a ' $.
    gomaex3lem5.8 $e |- ( ( ( i ->2 g ) ^ ( g ->2 y ) ) ^
                     ( ( ( y ->2 w ) ^ ( w ->2 n ) ) ^
                       ( ( n ->2 k ) ^ ( k ->2 i ) ) ) ) =< ( g ->2 i ) $.
    gomaex3lem5.9 $e |- p = ( ( a v b ) ->1 ( d v e ) ' ) ' $.
    gomaex3lem5.10 $e |- q = ( ( e v f ) ->1 ( b v c ) ' ) ' $.
    gomaex3lem5.11 $e |- r = ( ( p ' ->1 q ) ' ^ ( c v d ) ) $.
    gomaex3lem5.12 $e |- g = a $.
    gomaex3lem5.13 $e |- h = b $.
    gomaex3lem5.14 $e |- i = c $.
    gomaex3lem5.15 $e |- j = ( c v d ) ' $.
    gomaex3lem5.16 $e |- k = r $.
    gomaex3lem5.17 $e |- m = ( p ' ->1 q ) $.
    gomaex3lem5.18 $e |- n = ( p ' ->1 q ) ' $.
    gomaex3lem5.19 $e |- u = ( p ' ^ q ) $.
    gomaex3lem5.20 $e |- w = q ' $.
    gomaex3lem5.21 $e |- x = q $.
    gomaex3lem5.22 $e |- y = ( e v f ) ' $.
    gomaex3lem5.23 $e |- z = f $.
    $( Lemma for Godowski 6-var -> Mayet Example 3.  (Contributed by NM,
       29-Nov-1999.) $)
    gomaex3lem5 $p |- ( ( ( g v h ) ^ ( i v j ) ) ^
                  ( ( ( k v m ) ^ ( n v u ) ) ^
                    ( ( w v x ) ^ ( y v z ) ) ) ) =< ( h v i ) $=
      ( gomaex3h1 gomaex3h2 gomaex3h3 gomaex3h4 gomaex3h5 gomaex3h10 gomaex3h11
      gomaex3h6 gomaex3h7 gomaex3h8 gomaex3h9 gomaex3h12 go2n6 ) GHIJKLMQRSTUAA
      BGHUBUKULVCBCHKUCULUMVDCDIKUMUNVECDIJNOPUJUNUOVFCDJLNOPUJUOUPVGLMNOUPUQVJ
      MNOQUQURVKNOQRURUSVLORSUSUTVMBCEFOSTUIUTVAVHEFTUAVAVBVIAFGUAUFUKVBVNUGVO
      $.

    $( Lemma for Godowski 6-var -> Mayet Example 3.  (Contributed by NM,
       29-Nov-1999.) $)
    gomaex3lem6 $p |- ( ( ( a v b ) ^ ( c v ( c v d ) ' ) ) ^
                  ( ( ( r v ( p ' ->1 q ) ) ^ ( ( p ' ->1 q ) '
                     v ( p ' ^ q ) ) ) ^
                    ( ( q ' v q ) ^ ( ( e v f ) ' v f ) ) ) ) =< ( b v c ) $=
      ( wo wa wn wi1 gomaex3lem5 2or 2an le3tr2 ) GHVCZKIVCZVDZJLVCZMQVCZVDZRSV
      CZTUAVCZVDZVDZVDHKVCABVCZCCDVCVEZVCZVDZPNVEZOVFZVCZWFVEZWEOVDZVCZVDZOVEZO
      VCZEFVCVEZFVCZVDZVDZVDBCVCABCDEFGHIJKLMNOPQRSTUAUBUCUDUEUFUGUHUIUJUKULUMU
      NUOUPUQURUSUTVAVBVGVMWDVTWQVKWAVLWCGAHBUKULVHKCIWBUMUNVHVIVPWKVSWPVNWGVOW
      JJPLWFUOUPVHMWHQWIUQURVHVIVQWMVRWORWLSOUSUTVHTWNUAFVAVBVHVIVIVIHBKCULUMVH
      VJ $.

    $( Lemma for Godowski 6-var -> Mayet Example 3.  (Contributed by NM,
       29-Nov-1999.) $)
    gomaex3lem7 $p |- ( ( ( a v b ) ^ d ' ) ^
                  ( ( ( r v ( p ' ->1 q ) ) ^ p ' ) ^ e ' ) ) =< ( b v c ) $=
      ( wo wn wa wi1 gomaex3lem1 gomaex3lem3 ancom gomaex3lem2 ax-a2 df-t ax-r1
      lan wt ax-r2 2an an1 3tr gomaex3lem6 bltr ) ABVCZDVDZVEZPNVDZOVFZVCZWEVEZ
      EVDZVEZVEZWBCCDVCVDVCZVEZWGWFVDWEOVEVCZVEZOVDZOVCZEFVCVDFVCZVEZVEZVEZBCVC
      XAWKWMWDWTWJWLWCWBCDUDVGVNWOWHWSWIWNWEWGNOVHVNWSWRWQVEWIVOVEWIWQWRVIWRWIW
      QVOEFUEVJWQOWPVCZVOWPOVKVOXBOVLVMVPVQWIVRVSVQVQVMABCDEFGHIJKLMNOPQRSTUAUB
      UCUDUEUFUGUHUIUJUKULUMUNUOUPUQURUSUTVAVBVTWA $.

    $( Lemma for Godowski 6-var -> Mayet Example 3.  (Contributed by NM,
       29-Nov-1999.) $)
    gomaex3lem8 $p |- ( ( ( a v b ) ^ ( d v e ) ' ) ^
                  ( ( r v ( p ' ->1 q ) ) ^ p ' ) ) =< ( b v c ) $=
      ( wo wn wa wi1 an32 anor3 lan ran an4 3tr2 gomaex3lem7 bltr ) ABVCZDEVCVD
      ZVEZPNVDZOVFVCVRVEZVEZVODVDZVEVSEVDZVEVEZBCVCVOWAWBVEZVEZVSVEVOVSVEWDVEVT
      WCVOWDVSVGWEVQVSWDVPVODEVHVIVJVOVSWAWBVKVLABCDEFGHIJKLMNOPQRSTUAUBUCUDUEU
      FUGUHUIUJUKULUMUNUOUPUQURUSUTVAVBVMVN $.

    $( Lemma for Godowski 6-var -> Mayet Example 3.  (Contributed by NM,
       29-Nov-1999.) $)
    gomaex3lem9 $p |- ( ( ( a v b ) ^ ( d v e ) ' ) ^
                  ( r v ( p ' ->1 q ) ) ) =< ( b v c ) $=
      ( wo wn wi1 ancom gomaex3lem4 df2le2 ax-r1 lan an12 3tr gomaex3lem8 bltr
      wa ) ABVCDEVCVDVOZPNVDZOVEVCZVOZVPVRVQVOVOZBCVCVSVRVPVOVRVPVQVOZVOVTVPVRV
      FVPWAVRWAVPVPVQABDENUHVGVHVIVJVRVPVQVKVLABCDEFGHIJKLMNOPQRSTUAUBUCUDUEUFU
      GUHUIUJUKULUMUNUOUPUQURUSUTVAVBVMVN $.

    $( Lemma for Godowski 6-var -> Mayet Example 3.  (Contributed by NM,
       29-Nov-1999.) $)
    gomaex3lem10 $p |- ( ( ( a v b ) ^ ( d v e ) ' ) ^
                  ( r v ( p ' ->1 q ) ) ) =< ( ( b v c ) v ( e v f ) ' ) $=
      ( wo wn wa wi1 gomaex3lem9 leo letr ) ABVCDEVCVDVEPNVDOVFVCVEBCVCZVJEFVCV
      DZVCABCDEFGHIJKLMNOPQRSTUAUBUCUDUEUFUGUHUIUJUKULUMUNUOUPUQURUSUTVAVBVGVJV
      KVHVI $.
  $}

  ${
    gomaex3.1 $e |- a =< b ' $.
    gomaex3.2 $e |- b =< c ' $.
    gomaex3.3 $e |- c =< d ' $.
    gomaex3.5 $e |- e =< f ' $.
    gomaex3.6 $e |- f =< a ' $.
    gomaex3.8 $e |- ( ( ( i ->2 g ) ^ ( g ->2 y ) ) ^
                     ( ( ( y ->2 w ) ^ ( w ->2 n ) ) ^
                       ( ( n ->2 k ) ^ ( k ->2 i ) ) ) ) =< ( g ->2 i ) $.
    gomaex3.9 $e |- p = ( ( a v b ) ->1 ( d v e ) ' ) ' $.
    gomaex3.10 $e |- q = ( ( e v f ) ->1 ( b v c ) ' ) ' $.
    gomaex3.11 $e |- r = ( ( p ' ->1 q ) ' ^ ( c v d ) ) $.
    gomaex3.12 $e |- g = a $.
    gomaex3.14 $e |- i = c $.
    gomaex3.16 $e |- k = r $.
    gomaex3.18 $e |- n = ( p ' ->1 q ) ' $.
    gomaex3.20 $e |- w = q ' $.
    gomaex3.22 $e |- y = ( e v f ) ' $.
    $( Proof of Mayet Example 3 from 6-variable Godowski equation.  R. Mayet,
       "Equational bases for some varieties of orthomodular lattices related to
       states," Algebra Universalis 23 (1986), 167-195.  (Contributed by NM,
       27-May-2000.) $)
    gomaex3 $p |- ( ( ( a v b ) ^ ( d v e ) ' ) ^
                  ( ( ( ( a v b ) ->1 ( d v e ) ' ) ->1
                      ( ( e v f ) ->1 ( b v c ) ' ) ' ) ' ->1 ( c v d ) ) )
                   =< ( ( b v c ) v ( e v f ) ' ) $=
      ( wo wn wa wi1 df-i1 ax-a2 con2 ud1lem0ab ax-a1 ax-r2 ax-r4 ran 2or ax-r1
      lan id gomaex3lem10 bltr ) ABUKZDEUKULZUMZVIVJUNZEFUKZBCUKZULUNULZUNZULZC
      DUKZUNZUMVKMKULZLUNZUKZUMVNVMULUKVSWBVKVSVQULZVQVRUMZUKZWBVQVRUOWBWEWBWAM
      UKWEMWAUPWAWCMWDWAVPWCVTVLLVOKVLUBUQUCURZVPUSUTMWAULZVRUMWDUDWGVQVRWAVPWF
      VAVBUTVCUTVDUTVEABCDEFGBVRULZHIWAJKLMVTLUMZNLOFPQRSTUAUBUCUDUEBVFUFWHVFUG
      WAVFUHWIVFUILVFUJFVFVGVH $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
   OML Lemmas for studying orthoarguesian laws
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    oas.1 $e |- ( a ' ^ ( a v b ) ) =< c $.
    $( "Strengthening" lemma for studying the orthoarguesian law.  (Contributed
       by NM, 25-Dec-1998.) $)
    oas $p |- ( ( a ->1 c ) ^ ( a v b ) ) =< c $=
      ( wi1 wo wa oml ax-r1 lea ler2an lelor bltr lelan u1lemc1 lbtr letr ax-r2
      wn lear comanr1 comcom6 fh2 u1lemaa ancom leo df-i1 df2le2 2or lel2or ) A
      CEZABFZGZACGZASZCGZFZCUMUKAUPFZGZUQULURUKULAUOULGZFZURVAULABHIUTUPAUTUOCU
      OULJDKLMNUSUKAGZUKUPGZFUQAUKUPACOAUPUOCUAUBUCVBUNVCUPACUDVCUPUKGUPUKUPUEU
      PUKUPUOUKUOCJUOUOUNFZUKUOUNUFUKVDACUGIPQUHRUIRPUNCUPACTUOCTUJQ $.
  $}

  ${
    oasr.1 $e |- ( ( a ->1 c ) ^ ( a v b ) ) =< c $.
    $( Reverse of ~ oas lemma for studying the orthoarguesian law.
       (Contributed by NM, 28-Dec-1998.) $)
    oasr $p |- ( a ' ^ ( a v b ) ) =< c $=
      ( wn wo wa wi1 u1lem9b leran letr ) AEZABFZGACHZMGCLNMACIJDK $.
  $}

  ${
    oat.1 $e |- ( a ' ^ ( a v b ) ) =< c $.
    $( Transformation lemma for studying the orthoarguesian law.  (Contributed
       by NM, 26-Dec-1998.) $)
    oat $p |- b =< ( a ' ->1 c ) $=
      ( wn wa wo wi1 leor oml ax-r1 lea lelor bltr letr ax-a1 ax-r5 df-i1 ax-r2
      ler2an lbtr ) BAAEZCFZGZUBCHZBABGZUDBAIUFAUBUFFZGZUDUHUFABJKUGUCAUGUBCUBU
      FLDTMNOUDUBEZUCGZUEAUIUCAPQUEUJUBCRKSUA $.
  $}

  ${
    oatr.1 $e |- b =< ( a ' ->1 c ) $.
    $( Reverse transformation lemma for studying the orthoarguesian law.
       (Contributed by NM, 26-Dec-1998.) $)
    oatr $p |- ( a ' ^ ( a v b ) ) =< c $=
      ( wn wo wa leo df-i1 ax-a1 ax-r5 ax-r1 ax-r2 lbtr lel2or lelan omlan lear
      wi1 letr ) AEZABFZGZUACGZCUCUAAUDFZGUDUBUEUAAUEBAUDHBUACSZUEDUFUAEZUDFZUE
      UACIUEUHAUGUDAJKLMNOPACQNUACRT $.
  $}

  ${
    oau.1 $e |- ( a ^ ( ( a ->1 c ) v b ) ) =< c $.
    $( Transformation lemma for studying the orthoarguesian law.  (Contributed
       by NM, 28-Dec-1998.) $)
    oau $p |- b =< ( a ->1 c ) $=
      ( wi1 wo ax-a2 wa lea ler2an u1lemaa ax-r1 lelor wt u1lemc1 comcom comorr
      lbtr fh3 ax-r2 u1lemoa ax-a3 oridm ax-r5 2an ancom an1 3tr orabs leo lebi
      le3tr2 df-le1 ) BACEZBUNFUNBFZUNBUNGUOUNUNAUOHZFZUNUNAHZFUOUNUPURUNUPACHZ
      URUPACAUOIDJURUSACKLRMUQUNAFZUNUOFZHNUOHZUOUNAUOAUNACOPUNBQSUTNVAUOACUAVA
      UNUNFZBFZUOVDVAUNUNBUBLVCUNBUNUCUDTUEVBUONHUONUOUFUOUGTUHUNAUIULUNBUJUKTU
      M $.
  $}

  ${
    oaur.1 $e |- b =< ( a ->1 c ) $.
    $( Transformation lemma for studying the orthoarguesian law.  (Contributed
       by NM, 28-Dec-1998.) $)
    oaur $p |- ( a ^ ( ( a ->1 c ) v b ) ) =< c $=
      ( wi1 wo wa leid lel2or lelan ancom u1lemaa ax-r2 lbtr lear letr ) AACEZB
      FZGZACGZCSAQGZTRQAQQBQHDIJUAQAGTAQKACLMNACOP $.
  $}

  ${
    oaidlem2.1 $e |- ( ( d v ( ( a ->1 c ) ^ ( b ->1 c ) ) ) ' v
              ( ( a ->1 c ) ->1 ( b ->1 c ) ) ) = 1 $.
    $( Lemma for identity-like OA law.  (Contributed by NM, 22-Jan-1999.) $)
    oaidlem2 $p |- ( ( a ->1 c ) ^
              ( d v ( ( a ->1 c ) ^ ( b ->1 c ) ) ) )
               =< ( b ->1 c ) $=
      ( wi1 wa wo anidm ax-r1 ran anass ax-r2 leor lelan bltr df-le2 wn ax-a3
      wt ax-a2 oran3 ax-r5 df-i1 lor 3tr2 lem3.1 bile lear letr ) ACFZDUKBCFZGZ
      HZGZUMULUOUMUMUOUMUOUMUOUMUKUMGZUOUMUKUKGZULGUPUKUQULUQUKUKIJKUKUKULLMUMU
      NUKUMDNOPQUNRZUKRZHZUMHURUSUMHZHZUORZUMHTURUSUMSUTVCUMUTUSURHVCURUSUAUKUN
      UBMUCVBURUKULFZHZTVEVBVDVAURUKULUDUEJEMUFUGJUHUKULUIUJ $.
  $}

  ${
    oaidlem2g.1 $e |- ( ( c v ( a ^ b ) ) ' v
              ( a ->1 b ) ) = 1 $.
    $( Lemma for identity-like OA law (generalized).  (Contributed by NM,
       18-Feb-2002.) $)
    oaidlem2g $p |- ( a ^
              ( c v ( a ^ b ) ) )
               =< b $=
      ( wa wo anidm ax-r1 ran anass ax-r2 leor lelan bltr df-le2 wn ax-a3 ax-a2
      wt oran3 ax-r5 wi1 df-i1 lor 3tr2 lem3.1 bile lear letr ) ACABEZFZEZUJBUL
      UJUJULUJULUJULUJAUJEZULUJAAEZBEUMAUNBUNAAGHIAABJKUJUKAUJCLMNOUKPZAPZFZUJF
      UOUPUJFZFZULPZUJFSUOUPUJQUQUTUJUQUPUOFUTUOUPRAUKTKUAUSUOABUBZFZSVBUSVAURU
      OABUCUDHDKUEUFHUGABUHUI $.
  $}

  ${
    oa6v4v.1 $e |- ( ( ( a v b ) ^ ( c v d ) ) ^ ( e v f ) ) =<
                   ( b v ( a ^ ( c v ( ( ( a v c ) ^ ( b v d ) ) ^
   ( ( ( a v e ) ^ ( b v f ) ) v ( ( c v e ) ^ ( d v f ) ) ) ) ) ) ) $.
    oa6v4v.2 $e |- e = 0 $.
    oa6v4v.3 $e |- f = 1 $.
    $( 6-variable OA to 4-variable OA. (Contributed by NM, 29-Nov-1998.) $)
    oa6v4v $p |- ( ( a v b ) ^ ( c v d ) ) =< ( b v ( a ^ ( c v
                   ( ( a v c ) ^ ( b v d ) ) ) ) ) $=
      ( wo wa wt wf 2or ax-r2 lan an1 lor or0 or1 or0r 2an an32 anidm le3tr2
      ran ) ABJCDJKZEFJZKZBACACJZBDJZKZAEJZBFJZKZCEJZDFJZKZJZKZJZKZJUGBACULJZKZ
      JGUIUGLKUGUHLUGUHMLJLEMFLHINLUAOPUGQOVBVDBVAVCAUTULCUTULUJKZULUSUJULUOAUR
      CUOALKAUMAUNLUMAMJAEMAHRASOUNBLJLFLBIRBTOUBAQOURCLKCUPCUQLUPCMJCEMCHRCSOU
      QDLJLFLDIRDTOUBCQONPVEUJUJKZUKKULUJUKUJUCVFUJUKUJUDUFOORPRUE $.
  $}

  ${
    oa4v3v.1 $e |- d =< b ' $.
    oa4v3v.2 $e |- e =< c ' $.
    oa4v3v.3 $e |- ( ( d v b ) ^ ( e v c ) ) =< ( b v ( d ^ ( e v
                   ( ( d v e ) ^ ( b v c ) ) ) ) ) $.
    oa4v3v.4 $e |- d = ( a ->2 b ) ' $.
    oa4v3v.5 $e |- e = ( a ->2 c ) ' $.
    $( 4-variable OA to 3-variable OA (Godowski/Greechie Eq.  IV).
       (Contributed by NM, 28-Nov-1998.) $)
    oa4v3v $p |- ( b ' ^ ( ( a ->2 b ) v ( ( a ->2 c ) ^ ( ( b v c ) '
                v ( ( a ->2 b ) ^ ( a ->2 c ) ) ) ) ) ) =<
              ( ( b ' ^ ( a ->2 b ) ) v ( c ' ^ ( a ->2 c ) ) ) $=
      ( wn wi2 wa wo ax-a2 lor oran1 3tr 2an ax-r2 anor3 ancom 2or oran3 le3tr2
      lan anor1 lecon1 ) BKZABLZMZCKACLZMZNZUIUJULBCNZKUJULMZNZMZNZMZDBNZECNZMZ
      BDEDENZUOMZNZMZNZUNKZUTKZHVCUKKZUMKZMVIVAVKVBVLVABDNBUJKZNVKDBODVMBIPBUJQ
      RVBCENCULKZNVLECOEVNCJPCULQRSUKUMUATVHBUSKZNVJVGVOBVGVMURKZMVODVMVFVPIVFV
      NUQKZNVPEVNVEVQJVEUOVDMUOUPKZMVQVDUOUBVDVRUOVDVMVNNVRDVMEVNIJUCUJULUDTUFU
      OUPUGRUCULUQUDTSUJURUATPBUSQTUEUH $.
  $}

  ${
    oal42.1 $e |- ( b ' ^ ( ( a ->2 b ) v ( ( a ->2 c ) ^ ( ( b v c ) '
                v ( ( a ->2 b ) ^ ( a ->2 c ) ) ) ) ) ) =<
              ( ( b ' ^ ( a ->2 b ) ) v ( c ' ^ ( a ->2 c ) ) ) $.
    $( Derivation of Godowski/Greechie Eq.  II from Eq.  IV. (Contributed by
       NM, 25-Nov-1998.) $)
    oal42 $p |- ( b ' ^ ( ( a ->2 b ) v ( ( a ->2 c ) ^ ( ( b v c ) '
                v ( ( a ->2 b ) ^ ( a ->2 c ) ) ) ) ) ) =< a ' $=
      ( wn wi2 wo wa ancom u2lemanb ax-r2 2or lbtr lea lel2or letr ) BEZABFZACF
      ZBCGERSHGHGHZAEZQHZUACEZHZGZUATQRHZUCSHZGUEDUFUBUGUDUFRQHUBQRIABJKUGSUCHU
      DUCSIACJKLMUBUAUDUAQNUAUCNOP $.
  $}

  ${
    oa23.1 $e |- ( c ' ^ ( ( a ->2 c ) v ( ( a ->2 b ) ^ ( ( c v b ) '
                v ( ( a ->2 c ) ^ ( a ->2 b ) ) ) ) ) ) =< a ' $.
    $( Derivation of OA from Godowski/Greechie Eq.  II. (Contributed by NM,
       25-Nov-1998.) $)
    oa23 $p |- ( ( a ->2 b ) ^
              ( ( b v c ) ' v ( ( a ->2 b ) ^ ( a ->2 c ) ) ) )
               =< ( a ->2 c ) $=
      ( wi2 wo wn wa ax-a2 ax-r4 ancom 2or lan ax-r5 wt ax-a3 ax-r1 oridm ax-r2
      u2lemonb 2an an1 comorr u2lemc1 comcom comcom2 fh3 3tr1 lea ler2an le3tr1
      u2lemanb lelor orabs lbtr bltr leo lebi 3tr df-le1 ) ABEZBCFZGZVAACEZHZFZ
      HZVDVGVDFVACBFZGZVDVAHZFZHZVDFVDVLFZVDVGVLVDVFVKVAVCVIVEVJVBVHBCIJVAVDKLM
      NVLVDIVMVDVMVDVMCGZHZFZVDVMOHZVDVMFZVDVNFZHZVMVPVTVQVRVMVSOVRVDVDFZVLFZVM
      WBVRVDVDVLPQWAVDVLVDRNSACTUAQVQVMVMUBQVDVMVNVDVLUCVDCCVDACUDUEUFUGUHVPVDV
      DVNHZFVDVOWCVDVNVMHZAGZVNHVOWCWDWEVNDVNVMUIUJVMVNKACULUKUMVDVNUNUOUPVDVLU
      QURUSUT $.
  $}

  ${
    oa4lem1.1 $e |- a =< b ' $.
    oa4lem1.2 $e |- c =< d ' $.
    $( Lemma for 3-var to 4-var OA. (Contributed by NM, 27-Nov-1998.) $)
    oa4lem1 $p |- ( a v b ) =< ( ( a v c ) ' ->2 b ) $=
      ( wo wn wa wi2 leo ax-a1 lbtr ler2an lelor ax-a2 df-i2 le3tr1 ) BAGBACGZH
      ZHZBHZIZGABGTBJAUCBAUAUBASUAACKSLMENOABPTBQR $.

    $( Lemma for 3-var to 4-var OA. (Contributed by NM, 27-Nov-1998.) $)
    oa4lem2 $p |- ( c v d ) =< ( ( a v c ) ' ->2 d ) $=
      ( wo wn wa wi2 leor ax-a1 lbtr ler2an lelor ax-a2 df-i2 le3tr1 ) DCGDACGZ
      HZHZDHZIZGCDGTDJCUCDCUAUBCSUACAKSLMFNOCDPTDQR $.

    $( Lemma for 3-var to 4-var OA. (Contributed by NM, 27-Nov-1998.) $)
    oa4lem3 $p |- ( ( a v b ) ^ ( c v d ) ) =< ( ( b v d ) ' v
            ( ( ( a v c ) ' ->2 b ) ^ ( ( a v c ) ' ->2 d ) ) ) $=
      ( wo wa wn wi2 oa4lem1 oa4lem2 le2an leor letr ) ABGZCDGZHACGIZBJZRDJZHZB
      DGIZUAGPSQTABCDEFKABCDEFLMUAUBNO $.
  $}

  ${
    $( Substitutions into OA distributive law. $)
    distoa.1 $e |- d = ( a ->2 b ) $.
    distoa.2 $e |- e = ( ( b v c ) ->1 ( ( a ->2 b ) ^ ( a ->2 c ) ) ) $.
    distoa.3 $e |- f = ( ( b v c ) ->2 ( ( a ->2 b ) ^ ( a ->2 c ) ) ) $.
    $( Satisfaction of distributive law hypothesis.  (Contributed by NM,
       29-Nov-1998.) $)
    distoah1 $p |- d =< ( a ->2 b ) $=
      ( wi2 bile ) DABJGK $.

    $( Satisfaction of distributive law hypothesis.  (Contributed by NM,
       29-Nov-1998.) $)
    distoah2 $p |- e =< ( ( b v c ) ->0 ( ( a ->2 b ) ^ ( a ->2 c ) ) ) $=
      ( wo wi2 wa wi1 wi0 leo ax-r1 u12lem le3tr2 ) BCJZABKACKLZMZUASTKZJESTNUA
      UBOEUAHPSTQR $.

    $( Satisfaction of distributive law hypothesis.  (Contributed by NM,
       29-Nov-1998.) $)
    distoah3 $p |- f =< ( ( b v c ) ->0 ( ( a ->2 b ) ^ ( a ->2 c ) ) ) $=
      ( wo wi2 wa wi1 wi0 leor ax-r1 u12lem le3tr2 ) BCJZABKACKLZKZSTMZUAJFSTNU
      AUBOFUAIPSTQR $.

    $( Satisfaction of distributive law hypothesis.  (Contributed by NM,
       29-Nov-1998.) $)
    distoah4 $p |- ( d ^ ( a ->2 c ) ) =< f $=
      ( wi2 wa wo wn leo ran df-i2 ax-r2 le3tr1 ) ABJZACJZKZUABCLZMUAMKZLZDTKFU
      AUCNDSTGOFUBUAJUDIUBUAPQR $.

    ${
      $( OA distributive law as hypothesis. $)
      distoa.4 $e |- ( d ^ ( e v f ) ) = ( ( d ^ e ) v ( d ^ f ) ) $.
      $( Derivation in OM of OA, assuming OA distributive law ~ oadistd .
         (Contributed by NM, 29-Nov-1998.) $)
      distoa $p |- ( ( a ->2 b ) ^
              ( ( b v c ) ' v ( ( a ->2 b ) ^ ( a ->2 c ) ) ) )
               =< ( a ->2 c ) $=
        ( wi2 wo wa wi1 wn 1oa 2oath1 2or 2an ax-r2 lear bltr le2or 3tr2 u12lem
        ax-r1 wi0 df-i0 lan oridm le3tr2 ) ABKZBCLZULACKZMZNZMZULUMUOKZMZLZUNUN
        LULUMOUOLZMZUNUQUNUSUNABCPUSUOUNABCQULUNUAUBUCUTULUPURLZMZVBVDUTDEFLZMD
        EMZDFMZLVDUTJDULVEVCGEUPFURHIRSVFUQVGUSDULEUPGHSDULFURGISRUDUFVCVAULVCU
        MUOUGVAUMUOUEUMUOUHTUITUNUJUK $.
    $}
  $}

  ${
    oa3to4lem.1 $e |- a ' =< b $.
    oa3to4lem.2 $e |- c ' =< d $.
    oa3to4lem.3 $e |- g = ( ( a ^ b ) v ( c ^ d ) ) $.
    $( Lemma for orthoarguesian law (Godowski/Greechie 3-variable to 4-variable
       proof).  (Contributed by NM, 19-Dec-1998.) $)
    oa3to4lem1 $p |- b =< ( a ->1 g ) $=
      ( wn wa wo wi1 leor comid comcom3 wt ax-r2 ran ax-r1 lbtr lecom fh3 ancom
      df-t ax-a2 an1 3tr2 anidm anass lor leo lelan lelor letr ud1lem0a df-i1 )
      BAIZAABJZCDJZKZJZKZAELZBUQAURJZKZVBBUQBKZVEBUQMVFUQURKZVEVGVFVGUQAKZVFJZV
      FUQABAAANOUQBFUAUBPVFJVFPJVIVFPVFUCPVHVFPAUQKVHAUDAUQUEQRVFUFUGQSURVDUQUR
      AAJZBJZVDVKURVJABAUHRSAABUIQUJQTVDVAUQURUTAURUSUKULUMUNVCVBVCAUTLVBEUTAHU
      OAUTUPQST $.

    $( Lemma for orthoarguesian law (Godowski/Greechie 3-variable to 4-variable
       proof).  (Contributed by NM, 19-Dec-1998.) $)
    oa3to4lem2 $p |- d =< ( c ->1 g ) $=
      ( wn wa wo wi1 leor comid comcom3 wt ax-r2 ran ax-r1 lbtr lecom fh3 ancom
      df-t ax-a2 an1 3tr2 anidm anass lor lelan lelor letr ud1lem0a df-i1 ) DCI
      ZCABJZCDJZKZJZKZCELZDUPCURJZKZVADUPDKZVDDUPMVEUPURKZVDVFVEVFUPCKZVEJZVEUP
      CDCCCNOUPDGUAUBPVEJVEPJVHVEPVEUCPVGVEPCUPKVGCUDCUPUEQRVEUFUGQSURVCUPURCCJ
      ZDJZVCVJURVICDCUHRSCCDUIQUJQTVCUTUPURUSCURUQMUKULUMVBVAVBCUSLVAEUSCHUNCUS
      UOQST $.

    $( Lemma for orthoarguesian law (Godowski/Greechie 3-variable to 4-variable
       proof).  (Contributed by NM, 19-Dec-1998.) $)
    oa3to4lem3 $p |- ( a ^ ( b v ( d ^ ( ( a ^ c ) v ( b ^ d ) ) ) ) )
                      =< ( a ^ ( ( a ->1 g ) v ( ( c ->1 g ) ^ ( ( a ^ c ) v
                        ( ( a ->1 g ) ^ ( c ->1 g ) ) ) ) ) ) $=
      ( wa wo wi1 oa3to4lem1 oa3to4lem2 le2an lelor le2or lelan ) BDACIZBDIZJZI
      ZJAEKZCEKZRUBUCIZJZIZJABUBUAUFABCDEFGHLZDUCTUEABCDEFGHMZSUDRBUBDUCUGUHNON
      PQ $.

    ${
      $( Godowski/Greechie 3-variable OA as hypothesis $)
      oa3to4lem.oa3 $e |- ( a ^ ( ( a ->1 g ) v ( ( c ->1 g ) ^ ( ( a ^ c ) v
                        ( ( a ->1 g ) ^ ( c ->1 g ) ) ) ) ) )
                          =< ( ( a ^ g ) v ( c ^ g ) ) $.
      $( Lemma for orthoarguesian law (Godowski/Greechie 3-variable to
         4-variable proof).  (Contributed by NM, 19-Dec-1998.) $)
      oa3to4lem4 $p |- ( a ^ ( b v ( d ^ ( ( a ^ c ) v ( b ^ d ) ) ) ) )
               =< g $=
        ( wa wo wi1 oa3to4lem3 lear lel2or letr ) ABDACJZBDJKJKJAAELZCELZQRSJKJ
        KJZEABCDEFGHMTAEJZCEJZKEIUAEUBAENCENOPP $.
    $}
  $}

  ${
    oa3to4lem5.1 $e |- ( ( a v b ) ^ ( c v d ) ) =< ( a v ( b ^ ( d v
                   ( ( a v c ) ^ ( b v d ) ) ) ) ) $.
    $( Lemma for orthoarguesian law (Godowski/Greechie 3-variable to 4-variable
       proof).  (Contributed by NM, 19-Dec-1998.) $)
    oa3to4lem5 $p |- ( ( b v a ) ^ ( d v c ) ) =< ( a v ( b ^ ( d v
                   ( ( b v d ) ^ ( a v c ) ) ) ) ) $=
      ( wo wa ax-a2 2an ancom lor lan le3tr1 ) ABFZCDFZGABDACFZBDFZGZFZGZFBAFZD
      CFZGABDQPGZFZGZFEUANUBOBAHDCHIUETAUDSBUCRDQPJKLKM $.
  $}

  ${
    oa3to4lem6.oa4.1 $e |- a =< b ' $.
    oa3to4lem6.oa4.2 $e |- c =< d ' $.
    $( Variable substitutions to make into the 4-variable OA. $)
    oa3to4lem6.3 $e |- g = ( ( a ' ^ b ' ) v ( c ' ^ d ' ) ) $.
    oa3to4lem6.4 $e |- e = a ' $.
    oa3to4lem6.5 $e |- f = c ' $.
    $( Godowski/Greechie 3-variable OA as hypothesis $)
    oa3to4lem6.oa3 $e |- ( e ^ ( ( e ->1 g ) v ( ( f ->1 g ) ^ ( ( e ^ f ) v
                        ( ( e ->1 g ) ^ ( f ->1 g ) ) ) ) ) )
                          =< ( ( e ^ g ) v ( f ^ g ) ) $.
    $( Orthoarguesian law (Godowski/Greechie 3-variable to 4-variable).  The
       first 2 hypotheses are those for 4-OA. The next 3 are variable
       substitutions into 3-OA. The last is the 3-OA. The proof uses OM logic
       only.  (Contributed by NM, 19-Dec-1998.) $)
    oa3to4lem6 $p |- ( ( a v b ) ^ ( c v d ) ) =< ( a v ( b ^ ( d v
                   ( ( a v c ) ^ ( b v d ) ) ) ) ) $=
      ( wo wa wn 2an 2or anor3 ax-r2 lecon3 lecon id wi1 ud1lem0ab le3tr2 oran3
      oa3to4lem4 lan lor lecon1 ) ABDACNZBDNZOZNZOZNZABNZCDNZOZAPZBPZDPZVACPZOZ
      VBVCOZNZOZNZOZVAVBOZVDVCOZNZUQPZUTPZVAVBVDVCVMBVAABHUAUBDVDCDIUAUBVMUCEEG
      UDZFGUDZEFOZVPVQOZNZOZNZOEGOZFGOZNVAVAVMUDZVDVMUDZVEWEWFOZNZOZNZOVAVMOZVD
      VMOZNMEVAWBWJKVPWEWAWIEVAGVMKJUEZVQWFVTWHFVDGVMLJUEZVRVEVSWGEVAFVDKLQVPWE
      VQWFWMWNQRQRQWCWKWDWLEVAGVMKJQFVDGVMLJQRUFUHVJVAUPPZOVNVIWOVAVIVBUOPZNWOV
      HWPVBVHVCUNPZOWPVGWQVCVGULPZUMPZNWQVEWRVFWSACSBDSRULUMUGTUIDUNSTUJBUOUGTU
      IAUPSTVMURPZUSPZNVOVKWTVLXAABSCDSRURUSUGTUFUK $.
  $}

  ${
    oa3to4.oa4.1 $e |- a =< b ' $.
    oa3to4.oa4.2 $e |- c =< d ' $.
    $( Variable substitutions to make into the 4-variable OA. $)
    oa3to4.3 $e |- g = ( ( b ' ^ a ' ) v ( d ' ^ c ' ) ) $.
    oa3to4.4 $e |- e = b ' $.
    oa3to4.5 $e |- f = d ' $.
    $( Godowski/Greechie 3-variable OA as hypothesis $)
    oa3to4.oa3 $e |- ( e ^ ( ( e ->1 g ) v ( ( f ->1 g ) ^ ( ( e ^ f ) v
                        ( ( e ->1 g ) ^ ( f ->1 g ) ) ) ) ) )
                          =< ( ( e ^ g ) v ( f ^ g ) ) $.
    $( Orthoarguesian law (Godowski/Greechie 3-variable to 4-variable).  The
       first 2 hypotheses are those for 4-OA. The next 3 are variable
       substitutions into 3-OA. The last is the 3-OA. The proof uses OM logic
       only.  (Contributed by NM, 19-Dec-1998.) $)
    oa3to4 $p |- ( ( a v b ) ^ ( c v d ) ) =< ( b v ( a ^ ( c v
                   ( ( a v c ) ^ ( b v d ) ) ) ) ) $=
      ( lecon3 oa3to4lem6 oa3to4lem5 ) BADCBADCEFGABHNCDINJKLMOP $.
  $}

  ${
    oa6todual.1 $e |- ( ( ( a ' v b ' ) ^ ( c ' v d ' ) ) ^ ( e ' v f ' ) )
             =< ( b ' v ( a ' ^ ( c ' v ( ( ( a ' v c ' ) ^ ( b ' v d ' )
             ) ^ ( ( ( a ' v e ' ) ^ ( b ' v f ' ) ) v ( ( c ' v e ' ) ^
             ( d ' v f ' ) ) ) ) ) ) ) $.
    $( Conventional to dual 6-variable OA law.  (Contributed by NM,
       22-Dec-1998.) $)
    oa6todual $p |- ( b ^ ( a v ( c ^ ( ( ( a ^ c ) v ( b ^ d ) ) v
   ( ( ( a ^ e ) v ( b ^ f ) ) ^ ( ( c ^ e ) v ( d ^ f ) ) ) ) ) ) )
      =< ( ( ( a ^ b ) v ( c ^ d ) ) v ( e ^ f ) ) $=
      ( wn wo wa lecon ax-a1 df-a 2or oran3 ax-r2 2an anor3 le3tr1 ) BHZAHZCHZU
      AUBIZTDHZIZJZUAEHZIZTFHZIZJZUBUGIZUDUIIZJZIZJZIZJZIZHZUATIZUBUDIZJZUGUIIZ
      JZHZBACACJZBDJZIZAEJZBFJZIZCEJZDFJZIZJZIZJZIZJZABJZCDJZIZEFJZIZVEUSGKVTTH
      ZURHZJUTBWFVSWGBLVSUAHZUQHZIWGAWHVRWIALVRUBHZUPHZJWICWJVQWKCLVQUFHZUOHZIW
      KVIWLVPWMVIUCHZUEHZIWLVGWNVHWOACMBDMNUCUEOPVPUKHZUNHZJWMVLWPVOWQVLUHHZUJH
      ZIWPVJWRVKWSAEMBFMNUHUJOPVOULHZUMHZIWQVMWTVNXACEMDFMNULUMOPQUKUNRPNUFUOOP
      QUBUPRPNUAUQOPQTURRPWEVCHZVDHZIVFWCXBWDXCWCVAHZVBHZIXBWAXDWBXEABMCDMNVAVB
      OPEFMNVCVDOPS $.
  $}

  ${
    oa6fromdual.1 $e |- ( b ' ^ ( a ' v ( c ' ^ ( ( ( a ' ^ c ' ) v ( b '
                    ^ d ' ) ) v ( ( ( a ' ^ e ' ) v ( b ' ^ f ' ) ) ^ (
                    ( c ' ^ e ' ) v ( d ' ^ f ' ) ) ) ) ) ) )
            =< ( ( ( a ' ^ b ' ) v ( c ' ^ d ' ) ) v ( e ' ^ f ' ) ) $.
    $( Dual to conventional 6-variable OA law.  (Contributed by NM,
       22-Dec-1998.) $)
    oa6fromdual $p |- ( ( ( a v b ) ^ ( c v d ) ) ^ ( e v f ) ) =<
                   ( b v ( a ^ ( c v ( ( ( a v c ) ^ ( b v d ) ) ^
   ( ( ( a v e ) ^ ( b v f ) ) v ( ( c v e ) ^ ( d v f ) ) ) ) ) ) ) $=
      ( wn wa wo lecon oran 2an anor3 ax-r2 ax-a1 2or oran3 le3tr1 ) AHZBHZIZCH
      ZDHZIZJZEHZFHZIZJZHZUATUCTUCIZUAUDIZJZTUGIZUAUHIZJZUCUGIZUDUHIZJZIZJZIZJZ
      IZHZABJZCDJZIZEFJZIZBACACJZBDJZIZAEJZBFJZIZCEJZDFJZIZJZIZJZIZJZVEUJGKVKUF
      HZUIHZIUKVIWFVJWGVIUBHZUEHZIWFVGWHVHWIABLCDLMUBUENOEFLMUFUINOWEUAHZVDHZJV
      FBWJWDWKBPWDTHZVCHZIWKAWLWCWMAPWCUCHZVBHZJWMCWNWBWOCPWBUNHZVAHZIWOVNWPWAW
      QVNULHZUMHZIWPVLWRVMWSACLBDLMULUMNOWAUQHZUTHZJWQVQWTVTXAVQUOHZUPHZIWTVOXB
      VPXCAELBFLMUOUPNOVTURHZUSHZIXAVRXDVSXECELDFLMURUSNOQUQUTROMUNVANOQUCVBROM
      TVCNOQUAVDROS $.
  $}

  ${
    oa6fromdualn.1 $e |- ( b ^ ( a v ( c ^ ( ( ( a ^ c ) v ( b ^ d ) ) v
   ( ( ( a ^ e ) v ( b ^ f ) ) ^ ( ( c ^ e ) v ( d ^ f ) ) ) ) ) ) )
      =< ( ( ( a ^ b ) v ( c ^ d ) ) v ( e ^ f ) ) $.
    $( Dual to conventional 6-variable OA law.  (Contributed by NM,
       24-Dec-1998.) $)
    oa6fromdualn $p |- ( ( ( a ' v b ' ) ^ ( c ' v d ' ) ) ^ ( e ' v f ' ) )
             =< ( b ' v ( a ' ^ ( c ' v ( ( ( a ' v c ' ) ^ ( b ' v d ' )
             ) ^ ( ( ( a ' v e ' ) ^ ( b ' v f ' ) ) v ( ( c ' v e ' ) ^
             ( d ' v f ' ) ) ) ) ) ) ) $=
      ( wn wa wo ax-a1 2an 2or le3tr2 oa6fromdual ) AHZBHZCHZDHZEHZFHZBACACIZBD
      IZJZAEIZBFIZJZCEIZDFIZJZIZJZIZJZIABIZCDIZJZEFIZJQHZPHZRHZUTVAIZUSSHZIZJZU
      TTHZIZUSUAHZIZJZVAVFIZVCVHIZJZIZJZIZJZIUTUSIZVAVCIZJZVFVHIZJGBUSUNVQBKZAU
      TUMVPAKZCVAULVOCKZUDVEUKVNUBVBUCVDAUTCVAWCWDLBUSDVCWBDKZLMUGVJUJVMUEVGUFV
      IAUTEVFWCEKZLBUSFVHWBFKZLMUHVKUIVLCVAEVFWDWFLDVCFVHWEWGLMLMLMLUQVTURWAUOV
      RUPVSAUTBUSWCWBLCVADVCWDWELMEVFFVHWFWGLMNO $.
  $}

  ${
    $( Substitutions into 6-variable OA law. $)
    oa6to4.1 $e |- b ' = ( a ->1 g ) ' $.
    oa6to4.2 $e |- d ' = ( c ->1 g ) ' $.
    oa6to4.3 $e |- f ' = ( e ->1 g ) ' $.
    $( Satisfaction of 6-variable OA law hypothesis.  (Contributed by NM,
       22-Dec-1998.) $)
    oa6to4h1 $p |- a ' =< b ' ' $=
      ( wn wa wo leo wi1 df-i1 ax-r4 ax-r2 ax-r1 con3 lbtr ) AKZUBAGLZMZBKZKUBU
      CNUDUEUEUDKZUEAGOZKUFHUGUDAGPQRSTUA $.

    $( Satisfaction of 6-variable OA law hypothesis.  (Contributed by NM,
       22-Dec-1998.) $)
    oa6to4h2 $p |- c ' =< d ' ' $=
      ( wn wa wo leo wi1 df-i1 ax-r4 ax-r2 ax-r1 con3 lbtr ) CKZUBCGLZMZDKZKUBU
      CNUDUEUEUDKZUECGOZKUFIUGUDCGPQRSTUA $.

    $( Satisfaction of 6-variable OA law hypothesis.  (Contributed by NM,
       22-Dec-1998.) $)
    oa6to4h3 $p |- e ' =< f ' ' $=
      ( wn wa wo leo wi1 df-i1 ax-r4 ax-r2 ax-r1 con3 lbtr ) EKZUBEGLZMZFKZKUBU
      CNUDUEUEUDKZUEEGOZKUFJUGUDEGPQRSTUA $.

    ${
      $( 6-variable OA law as hypothesis. $)
      oa6to4.oa6 $e |- ( ( ( a ' v b ' ) ^ ( c ' v d ' ) )
                  ^ ( e ' v f ' ) )
             =< ( b ' v ( a ' ^ ( c ' v ( ( ( a ' v c ' ) ^ ( b ' v d ' )
             ) ^ ( ( ( a ' v e ' ) ^ ( b ' v f ' ) ) v ( ( c ' v e ' ) ^
             ( d ' v f ' ) ) ) ) ) ) ) $.
      $( Derivation of 4-variable proper OA law, assuming 6-variable OA law.
         (Contributed by NM, 22-Dec-1998.) $)
      oa6to4 $p |- ( ( a ->1 g ) ^ ( a v ( c ^ ( (
                     ( a ^ c ) v ( ( a ->1 g ) ^ ( c ->1 g ) ) ) v
                 ( ( ( a ^ e ) v ( ( a ->1 g ) ^ ( e ->1 g ) ) ) ^
                   ( ( c ^ e ) v ( ( c ->1 g ) ^ ( e ->1 g ) ) ) ) ) ) ) )
               =< ( ( ( a ^ g ) v ( c ^ g ) ) v ( e ^ g ) ) $=
        ( wa wo wi1 con1 2an lor 2or lan ancom oa6todual u1lemaa 3tr le3tr2 ) B
        ACACLZBDLZMZAELZBFLZMZCELZDFLZMZLZMZLZMZLABLZCDLZMZEFLZMAGNZACUEVBCGNZL
        ZMZUHVBEGNZLZMZUKVCVFLZMZLZMZLZMZLAGLZCGLZMZEGLZMABCDEFKUABVBUQVNBVBHOZ
        UPVMAUOVLCUGVEUNVKUFVDUEBVBDVCVSDVCIOZPQUJVHUMVJUIVGUHBVBFVFVSFVFJOZPQU
        LVIUKDVCFVFVTWAPQPRSQPUTVQVAVRURVOUSVPURAVBLVBALVOBVBAVSSAVBTAGUBUCUSCV
        CLVCCLVPDVCCVTSCVCTCGUBUCRVAEVFLVFELVRFVFEWASEVFTEGUBUCRUD $.
    $}
  $}

  ${
    oa4b.1 $e |- ( ( a ->1 g ) ^ ( a v ( c ^ ( (
                   ( a ^ c ) v ( ( a ->1 g ) ^ ( c ->1 g ) ) ) v
               ( ( ( a ^ e ) v ( ( a ->1 g ) ^ ( e ->1 g ) ) ) ^
                 ( ( c ^ e ) v ( ( c ->1 g ) ^ ( e ->1 g ) ) ) ) ) ) ) )
             =< ( ( ( a ^ g ) v ( c ^ g ) ) v ( e ^ g ) ) $.
    $( Derivation of 4-OA law variant.  (Contributed by NM, 22-Dec-1998.) $)
    oa4b $p |- ( ( a ->1 g ) ^ ( a v ( c ^ ( (
                   ( a ^ c ) v ( ( a ->1 g ) ^ ( c ->1 g ) ) ) v
               ( ( ( a ^ e ) v ( ( a ->1 g ) ^ ( e ->1 g ) ) ) ^
                 ( ( c ^ e ) v ( ( c ->1 g ) ^ ( e ->1 g ) ) ) ) ) ) ) )
             =< g $=
      ( wi1 wa wo lear lel2or letr ) ADFZABABGLBDFZGHACGLCDFZGHBCGMNGHGHGHGADGZ
      BDGZHZCDGZHDEQDRODPADIBDIJCDIJK $.
  $}

  ${
    oa4to6lem.1 $e |- a ' =< b $.
    oa4to6lem.2 $e |- c ' =< d $.
    oa4to6lem.3 $e |- e ' =< f $.
    oa4to6lem.4 $e |- g = ( ( ( a ^ b ) v ( c ^ d ) ) v ( e ^ f ) ) $.
    $( Lemma for orthoarguesian law (4-variable to 6-variable proof).
       (Contributed by NM, 18-Dec-1998.) $)
    oa4to6lem1 $p |- b =< ( a ->1 g ) $=
      ( wn wa wo wi1 wt ax-r2 ran ax-r1 lbtr leor comid comcom3 lecom fh3 ancom
      df-t ax-a2 an1 3tr2 anidm anass lor ax-a3 lelan lelor letr ud1lem0a df-i1
      leo ) BALZAABMZCDMZNEFMZNZMZNZAGOZBVAAVBMZNZVGBVABNZVJBVAUAVKVAVBNZVJVLVK
      VLVAANZVKMZVKVAABAAAUBUCVABHUDUEPVKMVKPMVNVKPVKUFPVMVKPAVANVMAUGAVAUHQRVK
      UIUJQSVBVIVAVBAAMZBMZVIVPVBVOABAUKRSAABULQUMQTVIVFVAVBVEAVBVBVCVDNZNZVEVB
      VQUTVEVRVBVCVDUNSTUOUPUQVHVGVHAVEOVGGVEAKURAVEUSQST $.

    $( Lemma for orthoarguesian law (4-variable to 6-variable proof).
       (Contributed by NM, 18-Dec-1998.) $)
    oa4to6lem2 $p |- d =< ( c ->1 g ) $=
      ( wa wo wi1 leor wt ax-r2 ran ax-r1 lbtr wn comid comcom3 lecom fh3 ancom
      df-t ax-a2 an1 3tr2 anidm anass lor or32 lelan lelor letr ud1lem0a df-i1
      ) DCUAZCABLZCDLZMEFLZMZLZMZCGNZDUTCVBLZMZVFDUTDMZVIDUTOVJUTVBMZVIVKVJVKUT
      CMZVJLZVJUTCDCCCUBUCUTDIUDUEPVJLVJPLVMVJPVJUFPVLVJPCUTMVLCUGCUTUHQRVJUIUJ
      QSVBVHUTVBCCLZDLZVHVOVBVNCDCUKRSCCDULQUMQTVHVEUTVBVDCVBVAVCMZVBMVDVBVPOVA
      VCVBUNTUOUPUQVGVFVGCVDNVFGVDCKURCVDUSQST $.

    $( Lemma for orthoarguesian law (4-variable to 6-variable proof).
       (Contributed by NM, 18-Dec-1998.) $)
    oa4to6lem3 $p |- f =< ( e ->1 g ) $=
      ( wa wo wi1 leor wt ax-r2 ran ax-r1 lbtr wn comid comcom3 lecom fh3 ancom
      df-t ax-a2 an1 3tr2 anidm anass lor lelan lelor letr ud1lem0a df-i1 ) FEU
      AZEABLCDLMZEFLZMZLZMZEGNZFUSEVALZMZVDFUSFMZVGFUSOVHUSVAMZVGVIVHVIUSEMZVHL
      ZVHUSEFEEEUBUCUSFJUDUEPVHLVHPLVKVHPVHUFPVJVHPEUSMVJEUGEUSUHQRVHUIUJQSVAVF
      USVAEELZFLZVFVMVAVLEFEUKRSEEFULQUMQTVFVCUSVAVBEVAUTOUNUOUPVEVDVEEVBNVDGVB
      EKUQEVBURQST $.

    $( Lemma for orthoarguesian law (4-variable to 6-variable proof).
       (Contributed by NM, 18-Dec-1998.) $)
    oa4to6lem4 $p |- ( b ^ ( a v ( c ^ ( ( ( a ^ c ) v ( b ^ d ) ) v
   ( ( ( a ^ e ) v ( b ^ f ) ) ^ ( ( c ^ e ) v ( d ^ f ) ) ) ) ) ) )
     =< ( ( a ->1 g ) ^ ( a v ( c ^ (
         ( ( a ^ c ) v ( ( a ->1 g ) ^ ( c ->1 g ) ) ) v
       ( ( ( a ^ e ) v ( ( a ->1 g ) ^ ( e ->1 g ) ) ) ^
         ( ( c ^ e ) v ( ( c ->1 g ) ^ ( e ->1 g ) ) ) ) ) ) ) ) $=
      ( wi1 wa wo oa4to6lem1 oa4to6lem2 le2an lelor oa4to6lem3 le2or lelan ) BA
      GLZACACMZBDMZNZAEMZBFMZNZCEMZDFMZNZMZNZMZNACUCUBCGLZMZNZUFUBEGLZMZNZUIUOU
      RMZNZMZNZMZNABCDEFGHIJKOZUNVEAUMVDCUEUQULVCUDUPUCBUBDUOVFABCDEFGHIJKPZQRU
      HUTUKVBUGUSUFBUBFURVFABCDEFGHIJKSZQRUJVAUIDUOFURVGVHQRQTUARQ $.

    ${
      $( Proper 4-variable OA as hypothesis $)
      oa4to6lem.oa4 $e |- ( ( a ->1 g ) ^ ( a v ( c ^ ( (
                       ( a ^ c ) v ( ( a ->1 g ) ^ ( c ->1 g ) ) ) v
                   ( ( ( a ^ e ) v ( ( a ->1 g ) ^ ( e ->1 g ) ) ) ^
                     ( ( c ^ e ) v ( ( c ->1 g ) ^ ( e ->1 g ) ) ) ) ) ) ) )
                 =< g $.
      $( Lemma for orthoarguesian law (4-variable to 6-variable proof).
         (Contributed by NM, 19-Dec-1998.) $)
      oa4to6dual $p |- ( b ^ ( a v ( c ^ ( ( ( a ^ c ) v ( b ^ d ) ) v
      ( ( ( a ^ e ) v ( b ^ f ) ) ^ ( ( c ^ e ) v ( d ^ f ) ) ) ) ) ) )
               =< g $=
        ( wa wo wi1 oa4to6lem4 letr ) BACACMZBDMNAEMZBFMNCEMZDFMNMNMNMAGOZACRUA
        CGOZMNSUAEGOZMNTUBUCMNMNMNMGABCDEFGHIJKPLQ $.
    $}
  $}

  ${
    oa4to6.oa6.1 $e |- a =< b ' $.
    oa4to6.oa6.2 $e |- c =< d ' $.
    oa4to6.oa6.3 $e |- e =< f ' $.
    $( Variable substitutions to make into the 4-variable OA. $)
    oa4to6.4 $e |- g =
                ( ( ( a ' ^ b ' ) v ( c ' ^ d ' ) ) v ( e ' ^ f ' ) ) $.
    oa4to6.5 $e |- h = a ' $.
    oa4to6.6 $e |- j = c ' $.
    oa4to6.7 $e |- k = e ' $.
    $( Proper 4-variable OA as hypothesis $)
    oa4to6.oa4 $e |- ( ( h ->1 g ) ^ ( h v ( j ^ ( (
                     ( h ^ j ) v ( ( h ->1 g ) ^ ( j ->1 g ) ) ) v
                 ( ( ( h ^ k ) v ( ( h ->1 g ) ^ ( k ->1 g ) ) ) ^
                   ( ( j ^ k ) v ( ( j ->1 g ) ^ ( k ->1 g ) ) ) ) ) ) ) )
               =< g $.
    $( Orthoarguesian law (4-variable to 6-variable proof).  The first 3
       hypotheses are those for 6-OA. The next 4 are variable substitutions
       into 4-OA. The last is the 4-OA. The proof uses OM logic only.
       (Contributed by NM, 19-Dec-1998.) $)
    oa4to6 $p |- ( ( ( a v b ) ^ ( c v d ) ) ^ ( e v f ) ) =<
                   ( b v ( a ^ ( c v ( ( ( a v c ) ^ ( b v d ) ) ^
   ( ( ( a v e ) ^ ( b v f ) ) v ( ( c v e ) ^ ( d v f ) ) ) ) ) ) ) $=
      ( wa wo lecon3 lecon wi1 ud1lem0ab 2an 2or le3tr2 oa4to6dual oa6fromdual
      wn id ) ABCDEFAUJZBUJZCUJZDUJZEUJZFUJZULUMSUNUOSTUPUQSTZBULABKUAUBDUNCDLU
      AUBFUPEFMUAUBURUKHGUCZHIHISZUSIGUCZSZTZHJSZUSJGUCZSZTZIJSZVAVESZTZSZTZSZT
      ZSGULURUCZULUNULUNSZVOUNURUCZSZTZULUPSZVOUPURUCZSZTZUNUPSZVQWASZTZSZTZSZT
      ZSURRUSVOVNWJHULGURONUDZHULVMWIOIUNVLWHPVCVSVKWGUTVPVBVRHULIUNOPUEUSVOVAV
      QWKIUNGURPNUDZUEUFVGWCVJWFVDVTVFWBHULJUPOQUEUSVOVEWAWKJUPGURQNUDZUEUFVHWD
      VIWEIUNJUPPQUEVAVQVEWAWLWMUEUFUEUFUEUFUENUGUHUI $.
  $}

  ${
    oa4btoc.1 $e |- ( ( a ->1 g ) ^ ( a v ( c ^ ( (
                   ( a ^ c ) v ( ( a ->1 g ) ^ ( c ->1 g ) ) ) v
               ( ( ( a ^ e ) v ( ( a ->1 g ) ^ ( e ->1 g ) ) ) ^
                 ( ( c ^ e ) v ( ( c ->1 g ) ^ ( e ->1 g ) ) ) ) ) ) ) )
             =< g $.
    $( Derivation of 4-OA law variant.  (Contributed by NM, 22-Dec-1998.) $)
    oa4btoc $p |- ( a ' ^ ( a v ( c ^ ( (
                   ( a ^ c ) v ( ( a ->1 g ) ^ ( c ->1 g ) ) ) v
               ( ( ( a ^ e ) v ( ( a ->1 g ) ^ ( e ->1 g ) ) ) ^
                 ( ( c ^ e ) v ( ( c ->1 g ) ^ ( e ->1 g ) ) ) ) ) ) ) )
             =< g $=
      ( wn wa wi1 wo leo df-i1 ax-r1 lbtr leid lelor lelan le2an letr ) AFZABAB
      GADHZBDHZGIZACGTCDHZGIBCGUAUCGIGZIZGZIZGTUGGDSTUGUGSSADGZIZTSUHJTUIADKLMU
      FUFAUEUEBUDUDUBUDNOPOQER $.
  $}

  ${
    oa4ctob.1 $e |- ( a ' ^ ( a v ( c ^ ( (
                   ( a ^ c ) v ( ( a ->1 g ) ^ ( c ->1 g ) ) ) v
               ( ( ( a ^ e ) v ( ( a ->1 g ) ^ ( e ->1 g ) ) ) ^
                 ( ( c ^ e ) v ( ( c ->1 g ) ^ ( e ->1 g ) ) ) ) ) ) ) )
             =< g $.
    $( Derivation of 4-OA law variant.  (Contributed by NM, 22-Dec-1998.) $)
    oa4ctob $p |- ( ( a ->1 g ) ^ ( a v ( c ^ ( (
                   ( a ^ c ) v ( ( a ->1 g ) ^ ( c ->1 g ) ) ) v
               ( ( ( a ^ e ) v ( ( a ->1 g ) ^ ( e ->1 g ) ) ) ^
                 ( ( c ^ e ) v ( ( c ->1 g ) ^ ( e ->1 g ) ) ) ) ) ) ) )
             =< g $=
      ( wa wi1 wo oas ) ABABFADGZBDGZFHACFJCDGZFHBCFKLFHFHFDEI $.
  $}

  ${
    oa4ctod.1 $e |- ( a ' ^ ( a v ( b ^ ( (
                   ( a ^ b ) v ( ( a ->1 d ) ^ ( b ->1 d ) ) ) v
               ( ( ( a ^ c ) v ( ( a ->1 d ) ^ ( c ->1 d ) ) ) ^
                 ( ( b ^ c ) v ( ( b ->1 d ) ^ ( c ->1 d ) ) ) ) ) ) ) )
             =< d $.
    $( Derivation of 4-OA law variant.  (Contributed by NM, 24-Dec-1998.) $)
    oa4ctod $p |- ( b ^ ( (
                   ( a ^ b ) v ( ( a ->1 d ) ^ ( b ->1 d ) ) ) v
               ( ( ( a ^ c ) v ( ( a ->1 d ) ^ ( c ->1 d ) ) ) ^
                 ( ( b ^ c ) v ( ( b ->1 d ) ^ ( c ->1 d ) ) ) ) ) )
             =< ( a ' ->1 d ) $=
      ( wa wi1 wo oat ) ABABFADGZBDGZFHACFJCDGZFHBCFKLFHFHFDEI $.
  $}

  ${
    oa4dtoc.1 $e |- ( b ^ ( (
                   ( a ^ b ) v ( ( a ->1 d ) ^ ( b ->1 d ) ) ) v
               ( ( ( a ^ c ) v ( ( a ->1 d ) ^ ( c ->1 d ) ) ) ^
                 ( ( b ^ c ) v ( ( b ->1 d ) ^ ( c ->1 d ) ) ) ) ) )
             =< ( a ' ->1 d ) $.
    $( Derivation of 4-OA law variant.  (Contributed by NM, 24-Dec-1998.) $)
    oa4dtoc $p |- ( a ' ^ ( a v ( b ^ ( (
                   ( a ^ b ) v ( ( a ->1 d ) ^ ( b ->1 d ) ) ) v
               ( ( ( a ^ c ) v ( ( a ->1 d ) ^ ( c ->1 d ) ) ) ^
                 ( ( b ^ c ) v ( ( b ->1 d ) ^ ( c ->1 d ) ) ) ) ) ) ) )
             =< d $=
      ( wa wi1 wo oatr ) ABABFADGZBDGZFHACFJCDGZFHBCFKLFHFHFDEI $.
  $}

  $( Lemma commuting terms.  (Contributed by NM, 24-Dec-1998.) $)
  oa4dcom $p |- ( b ^ ( (
                   ( a ^ b ) v ( ( a ->1 d ) ^ ( b ->1 d ) ) ) v
               ( ( ( a ^ c ) v ( ( a ->1 d ) ^ ( c ->1 d ) ) ) ^
                 ( ( b ^ c ) v ( ( b ->1 d ) ^ ( c ->1 d ) ) ) ) ) )
                 = ( b ^ ( (
                   ( b ^ a ) v ( ( b ->1 d ) ^ ( a ->1 d ) ) ) v
               ( ( ( b ^ c ) v ( ( b ->1 d ) ^ ( c ->1 d ) ) ) ^
                 ( ( a ^ c ) v ( ( a ->1 d ) ^ ( c ->1 d ) ) ) ) ) ) $=
    ( wa wi1 wo ancom 2or lan ) ABEZADFZBDFZEZGZACELCDFZEGZBCEMPEGZEZGBAEZMLEZG
    ZRQEZGBOUBSUCKTNUAABHLMHIQRHIJ $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
   5OA law
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    oa8to5.1 $e |- ( ( ( a ' v b ' ) ^ ( c ' v d ' ) ) ^
           ( ( e ' v f ' ) ^ ( g ' v h ' ) ) ) =< ( b ' v ( a ' ^ ( c ' v
               ( ( ( ( a ' v c ' ) ^ ( b ' v d ' ) ) ^
                   ( ( ( a ' v g ' ) ^ ( b ' v h ' ) ) v
                     ( ( c ' v g ' ) ^ ( d ' v h ' ) ) ) )
              ^ ( ( ( ( a ' v e ' ) ^ ( b ' v f ' ) ) ^
                      ( ( ( a ' v g ' ) ^ ( b ' v h ' ) ) v
                        ( ( e ' v g ' ) ^ ( f ' v h ' ) ) ) )
                 v ( ( ( c ' v e ' ) ^ ( d ' v f ' ) ) ^
                      ( ( ( c ' v g ' ) ^ ( d ' v h ' ) ) v
                      ( ( e ' v g ' ) ^ ( f ' v h ' ) ) ) ) ) ) ) ) ) $.
    $( Conventional to dual 8-variable OA law.  (Contributed by NM,
       8-May-2000.) $)
    oa8todual $p |- ( b ^ ( a v ( c ^
               ( ( ( ( a ^ c ) v ( b ^ d ) ) v
                   ( ( ( a ^ g ) v ( b ^ h ) ) ^
                     ( ( c ^ g ) v ( d ^ h ) ) ) )
              v ( ( ( ( a ^ e ) v ( b ^ f ) ) v
                      ( ( ( a ^ g ) v ( b ^ h ) ) ^
                        ( ( e ^ g ) v ( f ^ h ) ) ) )
                 ^ ( ( ( c ^ e ) v ( d ^ f ) ) v
                      ( ( ( c ^ g ) v ( d ^ h ) ) ^
                      ( ( e ^ g ) v ( f ^ h ) ) ) ) ) ) ) ) )
             =< ( ( ( a ^ b ) v ( c ^ d ) ) v
                ( ( e ^ f ) v ( g ^ h ) ) ) $=
      ( wn wo wa lecon ax-a1 df-a 2or oran3 ax-r2 2an anor3 le3tr1 ) BJZAJZCJZU
      CUDKZUBDJZKZLZUCGJZKZUBHJZKZLZUDUIKZUFUKKZLZKZLZUCEJZKZUBFJZKZLZUMUSUIKZV
      AUKKZLZKZLZUDUSKZUFVAKZLZUPVFKZLZKZLZKZLZKZJZUCUBKZUDUFKZLZUSVAKZUIUKKZLZ
      LZJZBACACLZBDLZKZAGLZBHLZKZCGLZDHLZKZLZKZAELZBFLZKZWMEGLZFHLZKZLZKZCELZDF
      LZKZWPXDLZKZLZKZLZKZLZABLZCDLZKZEFLZGHLZKZKZWFVRIMXPUBJZVQJZLVSBYDXOYEBNX
      OUCJZVPJZKYEAYFXNYGANXNUDJZVOJZLYGCYHXMYICNXMURJZVNJZKYIWRYJXLYKWRUHJZUQJ
      ZKYJWJYLWQYMWJUEJZUGJZKYLWHYNWIYOACOBDOPUEUGQRWQUMJZUPJZLYMWMYPWPYQWMUJJZ
      ULJZKYPWKYRWLYSAGOBHOPUJULQRZWPUNJZUOJZKYQWNUUAWOUUBCGODHOPUNUOQRZSUMUPTR
      PUHUQQRXLVHJZVMJZLYKXFUUDXKUUEXFVCJZVGJZKUUDXAUUFXEUUGXAUTJZVBJZKUUFWSUUH
      WTUUIAEOBFOPUTVBQRXEYPVFJZLUUGWMYPXDUUJYTXDVDJZVEJZKUUJXBUUKXCUULEGOFHOPV
      DVEQRZSUMVFTRPVCVGQRXKVKJZVLJZKUUEXIUUNXJUUOXIVIJZVJJZKUUNXGUUPXHUUQCEODF
      OPVIVJQRXJYQUUJLUUOWPYQXDUUJUUCUUMSUPVFTRPVKVLQRSVHVMTRPURVNQRSUDVOTRPUCV
      PQRSUBVQTRYCWBJZWEJZKWGXSUURYBUUSXSVTJZWAJZKUURXQUUTXRUVAABOCDOPVTWAQRYBW
      CJZWDJZKUUSXTUVBYAUVCEFOGHOPWCWDQRPWBWEQRUA $.

    ${
      $( Substitutions into 8-variable 5OA law. $)
      oa8to5.2 $e |- b ' = ( a ->1 j ) ' $.
      oa8to5.3 $e |- d ' = ( c ->1 j ) ' $.
      oa8to5.4 $e |- f ' = ( e ->1 j ) ' $.
      oa8to5.5 $e |- h ' = ( g ->1 j ) ' $.
      $( Orthoarguesian law 5OA converted from 8 to 5 variables.  (Contributed
         by NM, 8-May-2000.) $)
      oa8to5 $p |- ( ( a ->1 j ) ^ ( a v ( c ^ (
                ( ( ( a ^ c ) v ( ( a ->1 j ) ^ ( c ->1 j ) ) ) v
                ( ( ( a ^ g ) v ( ( a ->1 j ) ^ ( g ->1 j ) ) )
                ^ ( ( c ^ g ) v ( ( c ->1 j ) ^ ( g ->1 j ) ) ) ) )
                v (
                ( ( ( a ^ e ) v ( ( a ->1 j ) ^ ( e ->1 j ) ) ) v
                ( ( ( a ^ g ) v ( ( a ->1 j ) ^ ( g ->1 j ) ) )
                ^ ( ( e ^ g ) v ( ( e ->1 j ) ^ ( g ->1 j ) ) ) ) )
                ^
                ( ( ( c ^ e ) v ( ( c ->1 j ) ^ ( e ->1 j ) ) ) v
                ( ( ( c ^ g ) v ( ( c ->1 j ) ^ ( g ->1 j ) ) )
                ^ ( ( e ^ g ) v ( ( e ->1 j ) ^ ( g ->1 j ) ) ) ) ) ) ) )
                ) )
                 =< ( ( ( a ^ j ) v ( c ^ j ) ) v
                      ( ( e ^ j ) v ( g ^ j ) ) ) $=
        ( wa wo 2an lor 2or lan wi1 oa8todual con1 ancom u1lemaa 3tr le3tr2 ) B
        ACACOZBDOZPZAGOZBHOZPZCGOZDHOZPZOZPZAEOZBFOZPZUMEGOZFHOZPZOZPZCEOZDFOZP
        ZUPVDOZPZOZPZOZPZOABOZCDOZPZEFOZGHOZPZPAIUAZACUHWBCIUAZOZPZUKWBGIUAZOZP
        ZUNWCWFOZPZOZPZUSWBEIUAZOZPZWHVBWMWFOZPZOZPZVGWCWMOZPZWJWQOZPZOZPZOZPZO
        AIOZCIOZPZEIOZGIOZPZPABCDEFGHJUBBWBVOXGBWBKUCZVNXFAVMXECURWLVLXDUJWEUQW
        KUIWDUHBWBDWCXNDWCLUCZQRUMWHUPWJULWGUKBWBHWFXNHWFNUCZQRZUOWIUNDWCHWFXOX
        PQRZQSVFWSVKXCVAWOVEWRUTWNUSBWBFWMXNFWMMUCZQRUMWHVDWQXQVCWPVBFWMHWFXSXP
        QRZQSVIXAVJXBVHWTVGDWCFWMXOXSQRUPWJVDWQXRXTQSQSTRQVRXJWAXMVPXHVQXIVPAWB
        OWBAOXHBWBAXNTAWBUDAIUEUFVQCWCOWCCOXIDWCCXOTCWCUDCIUEUFSVSXKVTXLVSEWMOW
        MEOXKFWMEXSTEWMUDEIUEUFVTGWFOWFGOXLHWFGXPTGWFUDGIUEUFSSUG $.
    $}
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
   "Godowski/Greechie" form of proper 4-OA
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    oa4to4u.1 $e |- ( ( e ->1 d ) ^ ( e v ( f ^ ( (
                     ( e ^ f ) v ( ( e ->1 d ) ^ ( f ->1 d ) ) ) v
                 ( ( ( e ^ g ) v ( ( e ->1 d ) ^ ( g ->1 d ) ) ) ^
                   ( ( f ^ g ) v ( ( f ->1 d ) ^ ( g ->1 d ) ) ) ) ) ) ) )
               =< ( ( ( e ^ d ) v ( f ^ d ) ) v ( g ^ d ) ) $.
    $( Substitutions into 4-variable OA law. $)
    oa4to4u.2 $e |- e = ( a ' ->1 d ) $.
    oa4to4u3 $e |- f = ( b ' ->1 d ) $.
    oa4to4u.4 $e |- g = ( c ' ->1 d ) $.
    $( A "universal" 4-OA. The hypotheses are the standard proper 4-OA and
       substitutions into it.  (Contributed by NM, 28-Dec-1998.) $)
    oa4to4u $p |- ( ( a ->1 d ) ^ ( ( a ' ->1 d ) v ( ( b ' ->1 d ) ^ ( (
     ( ( a ->1 d ) ^ ( b ->1 d ) ) v ( ( a ' ->1 d ) ^ ( b ' ->1 d ) ) ) v
 ( ( ( ( a ->1 d ) ^ ( c ->1 d ) ) v ( ( a ' ->1 d ) ^ ( c ' ->1 d ) ) ) ^
   ( ( ( b ->1 d ) ^ ( c ->1 d ) ) v ( ( b ' ->1 d ) ^ ( c ' ->1 d ) ) ) )
    ) ) ) ) =< ( ( ( ( a ->1 d ) ^ ( a ' ->1 d ) ) v
                   ( ( b ->1 d ) ^ ( b ' ->1 d ) ) ) v
                   ( ( c ->1 d ) ^ ( c ' ->1 d ) ) ) $=
      ( wn wi1 wa wo 2an 2or ran ax-a2 ax-r2 ud1lem0b u1lem11 ax-r5 lan u1lemab
      le3tr2 lor u1lem8 ax-a1 3tr ax-r1 ) ALZDMZDMZUMBLZDMZUMUPNZUNUPDMZNZOZUMC
      LZDMZNZUNVBDMZNZOZUPVBNZURVDNZOZNZOZNZOZNZUMDNZUPDNZOZVBDNZOZADMZUMUPVTBD
      MZNZUQOZVTCDMZNZVCOZWAWDNZVGOZNZOZNZOZNVTUMNZWAUPNZOZWDVBNZOEDMZEFEFNZWQF
      DMZNZOZEGNZWQGDMZNZOZFGNZWSXCNZOZNZOZNZOZNEDNZFDNZOZGDNZOVNVSHWQUNXLVMEUM
      DIUAZEUMXKVLIFUPXJVKJXAUTXIVJWRUQWTUSEUMFUPIJPWQUNWSURXQFUPDJUAZPQXEVFXHV
      IXBVCXDVEEUMGVBIKPWQUNXCVDXQGVBDKUAZPQXFVGXGVHFUPGVBJKPWSURXCVDXRXSPQPQPQ
      PXOVQXPVRXMVOXNVPEUMDIRFUPDJRQGVBDKRQUFUNVTVMWLADUBZVLWKUMVKWJUPUTWCVJWIU
      TUSUQOWCUQUSSUSWBUQUNVTURWAXTBDUBZPUCTVFWFVIWHVFVEVCOWFVCVESVEWEVCUNVTVDW
      DXTCDUBZPUCTVIVHVGOWHVGVHSVHWGVGURWAVDWDYAYBPUCTPQUDUGPVQWOVRWPVOWMVPWNVO
      ULDNZULLZDNZOZWMULDUEWMYFWMADNZYCOYCYGOYFADUHYGYCSYGYEYCAYDDAUIRUGUJUKTVP
      UODNZUOLZDNZOZWNUODUEWNYKWNBDNZYHOYHYLOYKBDUHYLYHSYLYJYHBYIDBUIRUGUJUKTQV
      RVADNZVALZDNZOZWPVADUEWPYPWPCDNZYMOYMYQOYPCDUHYQYMSYQYOYMCYNDCUIRUGUJUKTQ
      UF $.

    $( A weaker-looking "universal" proper 4-OA. (Contributed by NM,
       29-Dec-1998.) $)
    oa4to4u2 $p |- ( ( a ->1 d ) ^ ( ( a ' ->1 d ) v ( ( b ' ->1 d ) ^ ( (
     ( ( a ->1 d ) ^ ( b ->1 d ) ) v ( ( a ' ->1 d ) ^ ( b ' ->1 d ) ) ) v
 ( ( ( ( a ->1 d ) ^ ( c ->1 d ) ) v ( ( a ' ->1 d ) ^ ( c ' ->1 d ) ) ) ^
   ( ( ( b ->1 d ) ^ ( c ->1 d ) ) v ( ( b ' ->1 d ) ^ ( c ' ->1 d ) ) ) )
    ) ) ) ) =< d $=
      ( wi1 wn wa wo oa4to4u u1lem8 lear lel2or bltr letr ) ADLZAMZDLZBMZDLZUBB
      DLZNUDUFNOUBCDLZNUDCMZDLZNOUGUHNUFUJNONONONUBUDNZUGUFNZOZUHUJNZODABCDEFGH
      IJKPUMDUNUKDULUKADNZUCDNZODADQUODUPADRUCDRSTULBDNZUEDNZODBDQUQDURBDRUEDRS
      TSUNCDNZUIDNZODCDQUSDUTCDRUIDRSTSUA $.
  $}

  ${
    oa4uto4g.1 $e |- ( ( b ' ->1 d ) ^ ( ( b ' ' ->1 d ) v
                      ( ( a ' ' ->1 d ) ^ ( (
     ( ( b ' ->1 d ) ^ ( a ' ->1 d ) ) v ( ( b ' ' ->1 d ) ^
          ( a ' ' ->1 d ) ) ) v
 ( ( ( ( b ' ->1 d ) ^ ( c ' ->1 d ) ) v ( ( b ' ' ->1 d ) ^
          ( c ' ' ->1 d ) ) ) ^
   ( ( ( a ' ->1 d ) ^ ( c ' ->1 d ) ) v ( ( a ' ' ->1 d ) ^
          ( c ' ' ->1 d ) ) ) ) ) ) ) ) =< d $.

    $( Expression involving 4th variable. $)
    oa4uto4g.4 $e |- h =
               ( ( ( a ^ c ) v ( ( a ->1 d ) ^ ( c ->1 d ) ) ) ^
                 ( ( b ^ c ) v ( ( b ->1 d ) ^ ( c ->1 d ) ) ) ) $.
    $( Derivation of "Godowski/Greechie" 4-variable proper OA law variant from
       "universal" variant ~ oa4to4u2 .  (Contributed by NM, 28-Dec-1998.) $)
    oa4uto4g $p |- ( ( a ->1 d ) ^ ( (
             ( a ^ b ) v ( ( a ->1 d ) ^ ( b ->1 d ) ) ) v h ) )
             =< ( b ->1 d ) $=
      ( wi1 wa wo ancom 2or lan lor wn u1lem9a lecon1 le2an leror 2an bltr letr
      ax-r5 le2or lelan lelor ax-a1 ud1lem0b ax-r2 oau ) BADHZABIZUKBDHZIZJZEJZ
      IZDBUMUQJZIBUMUKBAIZUMUKIZJZEJZIZJZIZDURVDBUQVCUMUPVBUKUOVAEULUSUNUTABKUK
      UMKLUCMNMVEBOZDHZUMUKVGAOZDHZIZUTJZVICOZDHZIZUKCDHZIZJZVGVMIZUMVOIZJZIZJZ
      IZJZIZDBVGVDWDVGBBDPQZVCWCUMVBWBUKVAVKEWAUSVJUTBVGAVIWFVIAADPQZRSEACIZVPJ
      ZBCIZVSJZIWAGWIVQWKVTWHVNVPAVICVMWGVMCCDPQZRSWJVRVSBVGCVMWFWLRSRUAUDUEUFR
      WEVGVFOZDHZVHOZDHZVJWNWPIZJZVRWNVLOZDHZIZJZVNWPWTIZJZIZJZIZJZIDWDXHVGUMWN
      WCXGBWMDBUGUHZUKWPWBXFAWODAUGUHZVKWRWAXEUTWQVJUMWNUKWPXIXJTNWAVTVQIXEVQVT
      KVTXBVQXDVSXAVRUMWNVOWTXICWSDCUGUHZTNVPXCVNUKWPVOWTXJXKTNTUILTLMFUAUBUAUJ
      $.
  $}

  ${
    oa4gto4u.1 $e |- ( ( e ->1 d ) ^ ( (
             ( e ^ f ) v ( ( e ->1 d ) ^ ( f ->1 d ) ) ) v
         ( ( ( e ^ g ) v ( ( e ->1 d ) ^ ( g ->1 d ) ) ) ^
           ( ( f ^ g ) v ( ( f ->1 d ) ^ ( g ->1 d ) ) ) ) ) )
             =< ( f ->1 d ) $.
    $( Substitutions into 4-variable OA law. $)
    oa4gto4u.2 $e |- f = ( a ->1 d ) $.
    oa4gto4u3 $e |- e = ( b ->1 d ) $.
    oa4gto4u.4 $e |- g = ( c ->1 d ) $.
    $( A "universal" 4-OA derived from the Godowski/Greechie form.  The
       hypotheses are the Godowski/Greechie form of the proper 4-OA and
       substitutions into it.  (Contributed by NM, 30-Dec-1998.) $)
    oa4gto4u $p |- ( ( a ->1 d ) ^ ( ( a ' ->1 d ) v ( ( b ' ->1 d ) ^ ( (
     ( ( a ->1 d ) ^ ( b ->1 d ) ) v ( ( a ' ->1 d ) ^ ( b ' ->1 d ) ) ) v
 ( ( ( ( a ->1 d ) ^ ( c ->1 d ) ) v ( ( a ' ->1 d ) ^ ( c ' ->1 d ) ) ) ^
   ( ( ( b ->1 d ) ^ ( c ->1 d ) ) v ( ( b ' ->1 d ) ^ ( c ' ->1 d ) ) ) )
    ) ) ) ) =< d $=
      ( wi1 wn wa wo ud1lem0b u1lem12 ax-r2 2an 2or ancom ax-r1 oaur bltr ) ADL
      ZAMDLZBMDLZUEBDLZNZUFUGNZOZUECDLZNZUFCMDLZNZOZUHULNZUGUNNZOZNZOZNZOZNZFFD
      LZEDLZEFNZVFVENZOZEGNZVFGDLZNZOZFGNZVEVKNZOZNZOZNZOZNZDWAVDFUEVTVCIVEUFVS
      VBVEUEDLUFFUEDIPADQRZVFUGVRVAVFUHDLUGEUHDJPBDQRZVIUKVQUTVGUIVHUJVGFENUIEF
      UAFUEEUHIJSRVHVEVFNUJVFVEUAVEUFVFUGWBWCSRTVQVPVMNUTVMVPUAVPUPVMUSVNUMVOUO
      FUEGULIKSVEUFVKUNWBVKULDLUNGULDKPCDQRZSTVJUQVLUREUHGULJKSVFUGVKUNWCWDSTSR
      TSTSUBFVSDHUCUD $.
  $}

  ${
    oa4uto4.1 $e |- ( ( a ->1 d ) ^ ( ( a ' ->1 d ) v ( ( b ' ->1 d ) ^ ( (
     ( ( a ->1 d ) ^ ( b ->1 d ) ) v ( ( a ' ->1 d ) ^ ( b ' ->1 d ) ) ) v
 ( ( ( ( a ->1 d ) ^ ( c ->1 d ) ) v ( ( a ' ->1 d ) ^ ( c ' ->1 d ) ) ) ^
   ( ( ( b ->1 d ) ^ ( c ->1 d ) ) v ( ( b ' ->1 d ) ^ ( c ' ->1 d ) ) ) )
    ) ) ) ) =< d $.
    $( Derivation of standard 4-variable proper OA law from "universal" variant
       ~ oa4to4u2 .  (Contributed by NM, 30-Dec-1998.) $)
    oa4uto4 $p |- ( ( a ->1 d ) ^ ( a v ( b ^ ( (
                     ( a ^ b ) v ( ( a ->1 d ) ^ ( b ->1 d ) ) ) v
                 ( ( ( a ^ c ) v ( ( a ->1 d ) ^ ( c ->1 d ) ) ) ^
                   ( ( b ^ c ) v ( ( b ->1 d ) ^ ( c ->1 d ) ) ) ) ) ) ) )
               =< d $=
      ( wi1 wa wo wn u1lem9a lecon1 ax-a2 le2an lelor bltr le2or lelan letr ) A
      DFZABABGZSBDFZGZHZACGZSCDFZGZHZBCGZUAUEGZHZGZHZGZHZGSAIDFZBIDFZUBUOUPGZHZ
      UFUOCIDFZGZHZUIUPUSGZHZGZHZGZHZGDUNVGSAUOUMVFUOAADJKZBUPULVEUPBBDJKZUCURU
      KVDUCUBTHURTUBLTUQUBAUOBUPVHVIMNOUGVAUJVCUGUFUDHVAUDUFLUDUTUFAUOCUSVHUSCC
      DJKZMNOUJUIUHHVCUHUILUHVBUIBUPCUSVIVJMNOMPMPQER $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
   Some 3-OA inferences (derived under OM)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Lemma for 3-OA(2).  Equivalence with substitution into 4-OA. (Contributed
     by NM, 24-Dec-1998.) $)
  oa3-2lema $p |- ( ( a ->1 c ) ^ ( a v ( b ^ ( (
                       ( a ^ b ) v ( ( a ->1 c ) ^ ( b ->1 c ) ) ) v
                   ( ( ( a ^ 0 ) v ( ( a ->1 c ) ^ ( 0 ->1 c ) ) ) ^
                     ( ( b ^ 0 ) v ( ( b ->1 c ) ^ ( 0 ->1 c ) ) ) ) ) ) ) )
                 = ( ( a ->1 c ) ^ ( a v ( b ^ ( ( a ^ b ) v (
                    ( a ->1 c ) ^ ( b ->1 c ) ) ) ) ) ) $=
    ( wa wi1 wo wf ax-a3 an0 ax-r5 ax-a2 wt or0 0i1 lan an1 3tr 2an lor ax-r2
    oridm ) ABABDZACEZBCEZDZFZAGDZUCGCEZDZFZBGDZUDUHDZFZDZFZDZFABUFDZFUCUPUQAUO
    UFBUOUBUEUNFZFUFUBUEUNHURUEUBURUEUEFUEUNUEUEUJUCUMUDUJGUIFUIGFZUCUGGUIAIJGU
    IKUSUIUCLDUCUIMUHLUCCNZOUCPQQUMGULFULGFZUDUKGULBIJGULKVAULUDLDUDULMUHLUDUTO
    UDPQQRSUEUATSTOSO $.

  $( Lemma for 3-OA(2).  Equivalence with substitution into 4-OA. (Contributed
     by NM, 24-Dec-1998.) $)
  oa3-2lemb $p |- ( ( a ->1 c ) ^ ( a v ( b ^ ( (
                       ( a ^ b ) v ( ( a ->1 c ) ^ ( b ->1 c ) ) ) v
                   ( ( ( a ^ c ) v ( ( a ->1 c ) ^ ( c ->1 c ) ) ) ^
                     ( ( b ^ c ) v ( ( b ->1 c ) ^ ( c ->1 c ) ) ) ) ) ) ) )
                 = ( ( a ->1 c ) ^ ( a v ( b ^ ( ( a ^ b ) v (
                    ( a ->1 c ) ^ ( b ->1 c ) ) ) ) ) ) $=
    ( wa wi1 wo ax-a3 wt i1id lan an1 ax-r2 lor wn or12 oridm df-i1 3tr1 2an )
    ABABDZACEZBCEZDZFZACDZUACCEZDZFZBCDZUBUFDZFZDZFZDZFABUDDZFUAUNUOAUMUDBUMTUC
    ULFZFUDTUCULGUPUCTUPUCUCFUCULUCUCUHUAUKUBUHUEUAFZUAUGUAUEUGUAHDUAUFHUACIZJU
    AKLMUEANZUEFZFZUTUQUAVAUSUEUEFZFUTUEUSUEOVBUEUSUEPMLUAUTUEACQZMVCRLUKUIUBFZ
    UBUJUBUIUJUBHDUBUFHUBURJUBKLMUIBNZUIFZFZVFVDUBVGVEUIUIFZFVFUIVEUIOVHUIVEUIP
    MLUBVFUIBCQZMVIRLSMUCPLMLJMJ $.

  $( Lemma for 3-OA(6).  Equivalence with substitution into 4-OA. (Contributed
     by NM, 24-Dec-1998.) $)
  oa3-6lem $p |- ( ( a ->1 c ) ^ ( a v ( b ^ ( (
                       ( a ^ b ) v ( ( a ->1 c ) ^ ( b ->1 c ) ) ) v
                   ( ( ( a ^ 1 ) v ( ( a ->1 c ) ^ ( 1 ->1 c ) ) ) ^
                     ( ( b ^ 1 ) v ( ( b ->1 c ) ^ ( 1 ->1 c ) ) ) ) ) ) ) )
                 = ( ( a ->1 c ) ^ ( a v ( b ^ ( (
                  ( a ' ->1 c ) ^ ( b ' ->1 c ) ) v (
                    ( a ->1 c ) ^ ( b ->1 c ) ) ) ) ) ) $=
    ( wa wi1 wo wt wn an1 lan u1lemab ax-r2 2or ax-a3 ax-r1 orabs ax-r5 3tr 2an
    lor 1i1 or32 leo le2an df-le2 ax-a1 df-i1 ) ABABDZACEZBCEZDZFZAGDZUIGCEZDZF
    ZBGDZUJUNDZFZDZFZDZFABAHZCEZBHZCEZDZUKFZDZFUIVBVIAVAVHBVAULAVCCDZFZBVECDZFZ
    DZFUHVNFZUKFVHUTVNULUPVKUSVMUPAACDZVJFZFZAVPFZVJFZVKUMAUOVQAIUOUICDVQUNCUIC
    UAZJACKLMVTVRAVPVJNOVSAVJACPQRUSBBCDZVLFZFZBWBFZVLFZVMUQBURWCBIURUJCDWCUNCU
    JWAJBCKLMWFWDBWBVLNOWEBVLBCPQRSTUHUKVNUBVOVGUKVOVNVGUHVNAVKBVMAVJUCBVLUCUDU
    EVKVDVMVFVKVCHZVJFZVDAWGVJAUFQVDWHVCCUGOLVMVEHZVLFZVFBWIVLBUFQVFWJVECUGOLSL
    QRJTJ $.

  $( Lemma for 3-OA(3).  Equivalence with substitution into 6-OA dual.
     (Contributed by NM, 24-Dec-1998.) $)
  oa3-3lem $p |- ( a ' ^ ( a v ( b ^ ( ( ( a ^ b ) v ( a '
                  ^ b ' ) ) v ( ( ( a ^ 1 ) v ( a ' ^ c ) ) ^
                   ( ( b ^ 1 ) v ( b ' ^ c ) ) ) ) ) ) ) =
               ( a ' ^ ( a v ( b ^
               ( ( a == b ) v ( ( a ' ->1 c ) ^ ( b ' ->1 c ) ) ) ) ) ) $=
    ( wa wn wo wt tb wi1 dfb ax-r1 an1 ax-a1 ax-r2 ax-r5 df-i1 2an 2or lan lor
    ) ABABDAEZBEZDFZAGDZUACDZFZBGDZUBCDZFZDZFZDZFABABHZUACIZUBCIZDZFZDZFUAULURA
    UKUQBUCUMUJUPUMUCABJKUFUNUIUOUFUAEZUEFZUNUDUSUEUDAUSALAMNOUNUTUACPKNUIUBEZU
    HFZUOUGVAUHUGBVABLBMNOUOVBUBCPKNQRSTS $.

  $( Lemma for 3-OA(1).  Equivalence with substitution into 6-OA dual.
     (Contributed by NM, 25-Dec-1998.) $)
  oa3-1lem $p |- ( 1 ^ ( 0 v ( a ^ ( ( ( 0 ^ a ) v ( 1 ^ ( a ->1 c ) )
       ) v ( ( ( 0 ^ b ) v ( 1 ^ ( b ->1 c ) ) ) ^ ( ( a ^ b ) v
        ( ( a ->1 c ) ^ ( b ->1 c ) ) ) ) ) ) ) )
       = ( a ^ ( ( a ->1 c ) v ( ( b ->1 c ) ^
               ( ( a ^ b ) v ( ( a ->1 c ) ^ ( b ->1 c ) ) ) ) ) ) $=
    ( wt wf wa wi1 wo ancom an1 ax-a2 or0 an0 ax-r2 2or 3tr ax-r5 ran lor lan )
    DEAEAFZDACGZFZHZEBFZDBCGZFZHZABFUBUFFHZFZHZFZHZFUMDFUMAUBUFUIFZHZFZDUMIUMJU
    MULEHULUPEULKULLUKUOAUKUBUJHUOUDUBUJUDEUBHUBEHUBUAEUCUBUAAEFEEAIAMNUCUBDFUB
    DUBIUBJNOEUBKUBLPQUJUNUBUHUFUIUHUGUEHUFEHUFUEUGKUGUFUEEUGUFDFUFDUFIUFJNUEBE
    FEEBIBMNOUFLPRSNTPP $.

  $( Lemma for 3-OA(4).  Equivalence with substitution into 6-OA dual.
     (Contributed by NM, 25-Dec-1998.) $)
  oa3-4lem $p |- ( a ' ^ ( a v ( b ^ ( ( ( a ^ b ) v ( a '
                  ^ b ' ) ) v ( ( ( a ^ c ) v ( a ' ^ 1 ) ) ^
                   ( ( b ^ c ) v ( b ' ^ 1 ) ) ) ) ) ) ) =
               ( a ' ^ ( a v ( b ^
               ( ( a == b ) v ( ( a ->1 c ) ^ ( b ->1 c ) ) ) ) ) ) $=
    ( wa wn wo wt tb wi1 dfb ax-a2 df-i1 an1 lor 3tr1 2an 2or ax-r1 lan ) ABABD
    AEZBEZDFZACDZTGDZFZBCDZUAGDZFZDZFZDZFABABHZACIZBCIZDZFZDZFTUKUQAUJUPBUPUJUL
    UBUOUIABJUMUEUNUHTUCFUCTFUMUETUCKACLUDTUCTMNOUAUFFUFUAFUNUHUAUFKBCLUGUAUFUA
    MNOPQRSNS $.

  $( Lemma for 3-OA(5).  Equivalence with substitution into 6-OA dual.
     (Contributed by NM, 25-Dec-1998.) $)
  oa3-5lem $p |- ( ( a ->1 c ) ^ ( a v ( c ^ ( ( ( a ^ c ) v (
          ( a ->1 c ) ^ 1 ) ) v ( ( ( a ^ b ) v ( ( a ->1 c ) ^
      ( b ->1 c ) ) ) ^ ( ( c ^ b ) v ( 1 ^ ( b ->1 c ) ) ) ) ) ) ) ) =
          ( ( a ->1 c ) ^ ( a v ( c ^ ( ( a ->1 c ) v ( ( b ->1 c ) ^
          ( ( a ^ b ) v ( ( a ->1 c ) ^ ( b ->1 c ) ) ) ) ) ) ) ) $=
    ( wa wi1 wt wo or12 oridm lor ax-r2 an1 df-i1 3tr1 ancom ax-r5 3tr lan 2or
    wn ) ACACDZACEZFDZGZABDUBBCEZDGZCBDZFUEDZGZDZGZDZGACUBUEUFDZGZDZGUBULUOAUKU
    NCUDUBUJUMUAATZUAGZGZUQUDUBURUPUAUAGZGUQUAUPUAHUSUAUPUAIJKUCUQUAUCUBUQUBLAC
    MZKJUTNUJUFUEDUMUIUEUFUGBTZBCDZGZGZVCUIUEVDVAUGVBGZGVCUGVAVBHVEVBVAVEVBVBGV
    BUGVBVBCBOPVBIKJKUHVCUGUHUEFDUEVCFUEOUELBCMZQJVFNRUFUEOKSRJR $.

  $( Lemma for a "universal" 3-OA. Equivalence with substitution into 6-OA
     dual.  (Contributed by NM, 26-Dec-1998.) $)
  oa3-u1lem $p |- ( 1 ^ ( c v ( ( a ' ->1 c ) ^ ( ( ( c ^ ( a ' ->1 c ) )
                 v ( 1 ^ ( a ->1 c ) ) ) v ( ( ( c ^ ( b ' ->1 c ) ) v ( 1
                 ^ ( b ->1 c ) ) ) ^ ( ( ( a ' ->1 c ) ^ ( b ' ->1 c ) ) v
                 ( ( a ->1 c ) ^ ( b ->1 c ) ) ) ) ) ) ) ) =
                 ( c v ( ( a ' ->1 c ) ^ ( ( a ->1 c ) v ( ( b ->1 c ) ^ (
                 ( ( a ->1 c ) ^ ( b ->1 c ) ) v ( ( a ' ->1 c ) ^ ( b ' ->1
                  c ) ) ) ) ) ) ) $=
    ( wt wn wi1 wa wo ancom an1 lea leo letr leor lel2or df-le2 u1lemab lor 3tr
    2or ax-a1 ax-r1 ran df-i1 3tr1 ax-a2 2an lan ) DCAEZCFZCUJGZDACFZGZHZCBEZCF
    ZGZDBCFZGZHZUJUPGZULURGZHZGZHZGZHZGVGDGVGCUJULURVBVAHZGZHZGZHDVGIVGJVFVKCVE
    VJUJUNULVDVIUICGZACGZHZUIVMHZHVOUNULVNVOVLVOVMVLUIVOUICKUIVMLMVMUINOPUKVNUM
    VOUKUJCGVLUIEZCGZHVNCUJIUICQVQVMVLVPACAVPAUAUBUCRSUMULDGULVODULIULJACUDZSTV
    RUEUTURVCVHUOCGZBCGZHZUOVTHZHWBUTURWAWBVSWBVTVSUOWBUOCKUOVTLMVTUONOPUQWAUSW
    BUQUPCGVSUOEZCGZHWACUPIUOCQWDVTVSWCBCBWCBUAUBUCRSUSURDGURWBDURIURJBCUDZSTWE
    UEVAVBUFUGTUHRS $.

  $( Lemma for a "universal" 3-OA. Equivalence with substitution into 6-OA
     dual.  (Contributed by NM, 27-Dec-1998.) $)
  oa3-u2lem $p |- ( ( a ->1 c ) ^ ( ( a ' ->1 c ) v ( c ^ (
                  ( ( ( a ' ->1 c ) ^ c ) v ( ( a ->1 c ) ^ 1 ) ) v (
                  ( ( ( a ' ->1 c ) ^ ( b ' ->1 c ) ) v ( ( a ->1 c ) ^
                  ( b ->1 c ) ) ) ^ ( ( c ^ ( b ' ->1 c ) ) v
                  ( 1 ^ ( b ->1 c ) ) ) ) ) ) ) ) =
                  ( ( a ->1 c ) ^ ( ( a ' ->1 c ) v ( c ^ ( ( a ->1 c ) v
                  ( ( b ->1 c ) ^ ( ( ( a ->1 c ) ^ ( b ->1 c ) ) v
                  ( ( a ' ->1 c ) ^ ( b ' ->1 c ) ) ) ) ) ) ) ) $=
    ( wn wi1 wa wt u1lemab an1 2or lea ax-a1 ax-r1 leid leran le2or ax-r2 ancom
    wo bltr df-i1 lbtr df-le2 ax-a2 2an lan lor ) ADZCEZCUICFZACEZGFZSZUIBDZCEZ
    FZUKBCEZFZSZCUOFZGUQFZSZFZSZFZSUICUKUQURUPSZFZSZFZSUKVEVIUIVDVHCUMUKVCVGUMU
    HCFZUHDZCFZSZUKSUKUJVMULUKUHCHUKIJVMUKVMUHACFZSZUKVJUHVLVNUHCKVKACVKAAAVKAL
    MANTOPUKVOACUAMUBUCQVCVBUSFVGUSVBRVBUQUSVFVBUNCFZUNDZCFZSZUQSUQUTVSVAUQUTUO
    CFVSCUORUNCHQVAUQGFUQGUQRUQIQJVSUQVSUNBCFZSZUQVPUNVRVTUNCKVQBCVQBBBVQBLMBNT
    OPUQWABCUAMUBUCQUPURUDUEQJUFUGUF $.

  ${
    oa3-6to3.1 $e |- ( ( a ->1 c ) ^ ( a v ( b ^ ( (
                  ( a ' ->1 c ) ^ ( b ' ->1 c ) ) v (
                    ( a ->1 c ) ^ ( b ->1 c ) ) ) ) ) ) =< c $.
    $( Derivation of 3-OA variant (3) from (6).  (Contributed by NM,
       24-Dec-1998.) $)
    oa3-6to3 $p |- ( a ' ^ ( a v ( b ^
               ( ( a == b ) v ( ( a ' ->1 c ) ^ ( b ' ->1 c ) ) ) ) ) )
                =< c $=
      ( wn tb wi1 wa wo wt oa3-3lem ax-r1 leid wf df-f bltr ax-r2 dff 2or or0
      le0 ancom an1 ax-a2 oa3-6lem oa4to6dual ) AEZABABFUGCGBEZCGHZIHIHZUGABABH
      ZUGUHHIAJHZUGCHIBJHZUHCHIHIHIHZCUNUJABCKLAUGBUHJCCUGMUHMJEZNCNUOOLCUAPCJC
      HZAUGHZBUHHZIZIZUSUPIUTCUTCNICUPCUSNUPCJHCJCUBCUCQUSNNIZNVAUSNUQNURARBRSL
      NTQSCTQLUPUSUDQACGZABUKVBBCGZHZIULVBJCGZHIUMVCVEHIHIHIHVBABUIVDIHIHCABCUE
      DPUFP $.
  $}

  ${
    oa3-2to4.1 $e |- ( ( a ->1 c ) ^ ( a v ( b ^ ( ( a ^ b ) v (
                    ( a ->1 c ) ^ ( b ->1 c ) ) ) ) ) ) =< c $.
    $( Derivation of 3-OA variant (4) from (2).  (Contributed by NM,
       24-Dec-1998.) $)
    oa3-2to4 $p |- ( a ' ^ ( a v ( b ^
               ( ( a == b ) v ( ( a ->1 c ) ^ ( b ->1 c ) ) ) ) ) )
                =< c $=
      ( wn tb wi1 wa wo wt oa3-4lem ax-r1 leid le1 wf dff 2or or0 ax-r2 bltr
      an1 ax-a2 oa3-2lemb oa4to6dual ) AEZABABFACGZBCGZHZIHIHZUEABABHZUEBEZHIAC
      HZUEJHIBCHZUKJHIHIHIHZCUNUIABCKLAUEBUKCJCUEMUKMCENCCJHZAUEHZBUKHZIZIZURUO
      IUSCUSCOICUOCUROCUAUROOIZOUTUROUPOUQAPBPQLORSQCRSLUOURUBSUFABUJUHIZULUFCC
      GZHIUMUGVBHIHIHIHUFABVAHIHCABCUCDTUDT $.
  $}

  ${
    oa3-2wto2.1 $e |- ( a ' ^ ( a v ( b ^ ( ( a ^ b ) v (
                    ( a ->1 c ) ^ ( b ->1 c ) ) ) ) ) ) =< c $.
    $( Derivation of 3-OA variant from weaker version.  (Contributed by NM,
       25-Dec-1998.) $)
    oa3-2wto2 $p |- ( ( a ->1 c ) ^ ( a v ( b ^ ( ( a ^ b ) v (
                    ( a ->1 c ) ^ ( b ->1 c ) ) ) ) ) ) =< c $=
      ( wa wi1 wo oas ) ABABEACFBCFEGECDH $.
  $}

  ${
    oa3-2to2s.1 $e |- ( ( a ->1 d ) ^ ( a v ( b ^ ( ( a ^ b ) v (
                    ( a ->1 d ) ^ ( b ->1 d ) ) ) ) ) ) =< d $.
    $( Substitution into weaker version. $)
    oa3-2to2s.2 $e |- d = ( ( a ^ c ) v ( b ^ c ) ) $.
    $( Derivation of 3-OA variant from weaker version.  (Contributed by NM,
       25-Dec-1998.) $)
    oa3-2to2s $p |- ( ( a ->1 c ) ^ ( a v ( b ^ ( ( a ^ b ) v (
                    ( a ->1 c ) ^ ( b ->1 c ) ) ) ) ) ) =<
        ( ( a ^ c ) v ( b ^ c ) ) $=
      ( wi1 wa wo wf wn id leo df-i1 ax-r1 ax-a1 ax-r2 lbtr 2an wt or0 lan omla
      2or an1 0i1 oa3-2lema bltr oa4to6 oa6to4 ancom an0 lor le3tr2 ) ACGZABABH
      ZUOBCGZHIZAJHZUOJCGZHIBJHZUQUTHIHIHIHACHZBCHZIZJCHZIZUOABURHIHVDAUOBUQJUT
      CUOKZLUQKZLUTKZLAKZVGBKZVHJKZVIDABJVJVJVBIZVGKZVJVBMVMUOVNUOVMACNZOUOPZQR
      VKVKVCIZVHKZVKVCMVQUQVRUQVQBCNZOUQPZQRVLVLVEIZVIKZVLVEMWAUTWBUTWAJCNOUTPZ
      QRDDJIZVJKZVNHZVKKZVRHZIZVLKZWBHZIWDDDUAODWIJWKDVDWIFVBWFVCWHVBAUOHZWFWLV
      BWLAVMHVBUOVMAVOUBACUCQOAWEUOVNAPZVPSQVCBUQHZWHWNVCWNBVQHVCUQVQBVSUBBCUCQ
      OBWGUQVRBPZVTSQUDQJJTHZWKWPJJUEOJWJTWBJPZTUTWBUTTCUFOWCQSQUDQWMWOWQADGZAB
      UPWRBDGZHIZUSWRJDGZHIVAWSXAHIHIHIHWRABWTHIHDABDUGEUHUIUJABCUGVFVDJIVDVEJV
      DVECJHJJCUKCULQUMVDUAQUN $.
  $}

  ${
    oa3-u1.1 $e |- ( ( c ->1 c ) ^ ( c v ( ( a ' ->1 c ) ^
                     ( ( ( c ^ ( a ' ->1 c ) ) v ( ( c ->1 c ) ^
                     ( ( a ' ->1 c ) ->1 c ) ) ) v ( ( ( c ^ ( b ' ->1 c ) )
                     v ( ( c ->1 c ) ^ ( ( b ' ->1 c ) ->1 c ) ) ) ^ ( (
                     ( a ' ->1 c ) ^ ( b ' ->1 c ) ) v
                     ( ( ( a ' ->1 c ) ->1 c ) ^ ( ( b ' ->1 c ) ->1 c ) ) )
                      ) ) ) ) ) =< c $.
    $( Derivation of a "universal" 3-OA. The hypothesis is a substitution
       instance of the proper 4-OA. (Contributed by NM, 27-Dec-1998.) $)
    oa3-u1 $p |- ( c v ( ( a ' ->1 c ) ^ ( ( a ->1 c ) v
                 ( ( b ->1 c ) ^ ( ( ( a ->1 c ) ^ ( b ->1
                 c ) ) v ( ( a ' ->1 c ) ^ ( b ' ->1
                  c ) ) ) ) ) ) ) =< c $=
      ( wn wi1 wa wo wt oa3-u1lem ax-r1 u1lem9ab ax-a2 lear lel2or df-le2 ax-r2
      ancom u1lem8 2or le1 an1 3tr oa4to6dual leid letr bltr ) CAEZCFZACFZBCFZU
      JUKGZUIBEZCFZGZHGHGHZICUICUIGIUJGHCUNGIUKGHUOULHGHGHGZCUQUPABCJKUQCCCIUIU
      JUNUKCCEUAACLBCLCCBCGZUMCGZHZHZCIGZUIUJGZHZUNUKGZHZVACVAUTCHCCUTMUTCURCUS
      BCNUMCNOPQKVFVAVDCVEUTVDCACGZUHCGZHZHVICHCVBCVCVICUBVCUJUIGVIUIUJRACSQTCV
      IMVICVGCVHACNUHCNOPUCVEUKUNGUTUNUKRBCSQTKQDUDCUEUFUG $.
  $}

  ${
    oa3-u2.1 $e |- ( ( ( a ' ->1 c ) ->1 c ) ^ ( ( a ' ->1 c
 ) v ( c ^ ( ( ( ( a ' ->1 c ) ^ c ) v ( ( ( a ' ->1 c ) ->1 c ) ^ ( c ->1
 c ) ) ) v ( ( ( ( a ' ->1 c ) ^ ( b ' ->1 c ) ) v ( ( ( a ' ->1 c ) ->1 c )
 ^ ( ( b ' ->1 c ) ->1 c ) ) ) ^ ( ( c ^ ( b ' ->1 c ) ) v ( ( c ->1 c ) ^
                    ( ( b ' ->1 c ) ->1 c ) ) ) ) ) ) ) ) =< c $.
    $( Derivation of a "universal" 3-OA. The hypothesis is a substitution
       instance of the proper 4-OA. (Contributed by NM, 27-Dec-1998.) $)
    oa3-u2 $p |- ( ( a ->1 c ) ^ ( ( a ' ->1 c ) v ( c ^ ( ( a ->1 c ) v
                  ( ( b ->1 c ) ^ ( ( ( a ->1 c ) ^ ( b ->1 c ) ) v
                  ( ( a ' ->1 c ) ^ ( b ' ->1 c ) ) ) ) ) ) ) ) =< c $=
      ( wi1 wn wa wo wt oa3-u2lem ax-r1 u1lem9ab le1 or32 ancom u1lem8 2or lear
      ax-r2 lel2or an1 df-le2 3tr oa4to6dual bltr ) ACEZAFZCEZCUFBCEZUFUIGZUHBF
      ZCEZGZHGHGHGZUFUHCUHCGUFIGHUMUJHCULGIUIGHGHGHGZCUOUNABCJKUHUFCIULUICACLCF
      MBCLUHUFGZCIGZHULUIGZHZCUSUPURHZUQHACGZUGCGZHZBCGZUKCGZHZHZCHCUPUQURNUTVG
      UQCUPVCURVFUPUFUHGVCUHUFOACPSURUIULGVFULUIOBCPSQCUAQVGCVCCVFVACVBACRUGCRT
      VDCVEBCRUKCRTTUBUCKDUDUE $.
  $}

  ${
    oa3-1to5.1 $e |- ( ( a ->1 c ) ^
              ( ( a ^ b ) v ( ( a ->1 c ) ^ ( b ->1 c ) ) ) )
               =< ( b ->1 c ) $.
    $( Derivation of an equivalent of the second "universal" 3-OA U2 from an
       equivalent of the first "universal" 3-OA U1.  This shows that U2 is
       redundant in a system containg U1.  The hypothesis is theorem ~ oal1 .
       (Contributed by NM, 1-Jan-1999.) $)
    oa3-1to5 $p |- ( c ^ ( ( b ->1 c ) v ( ( a ->1 c ) ^
              ( ( a ^ b ) v ( ( a ->1 c ) ^ ( b ->1 c ) ) ) ) ) )
               =< ( b ' ->1 c ) $=
      ( wi1 wa wo wn leid lel2or lelan ax-a1 ran ax-r5 ax-a2 ax-r2 u1lemab 3tr1
      ancom lbtr lear letr ) CBCEZACEZABFUDUCFGFZGZFZCBHZCEZFZUIUGCUCFZUJUFUCCU
      CUCUEUCIDJKUCCFZUICFZUKUJBCFZUHCFZGZUOUHHZCFZGZULUMUPURUOGUSUNURUOBUQCBLM
      NURUOOPBCQUHCQRCUCSCUISRTCUIUAUB $.
  $}

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
   Derivation of 4-variable proper OA from OA distributive law
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$( In this section, we postulate a temporary axiom (intended not to
   be used outside of this section) for the OA distributive law, and derive
   from it the proper 4-OA.  This shows that the OA distributive law
   implies the proper 4-OA (and therefore the 6-OA). $)

  ${
    oad.1 $e |- e =
                ( ( ( a ^ c ) v ( ( a ->1 d ) ^ ( c ->1 d ) ) ) ^
                  ( ( b ^ c ) v ( ( b ->1 d ) ^ ( c ->1 d ) ) ) ) $.
    oad.2 $e |- f =
                ( ( ( a ^ b ) v ( ( a ->1 d ) ^ ( b ->1 d ) ) ) v e ) $.
    oad.3 $e |- h =< ( a ->1 d ) $.
    oad.4 $e |- j =< f $.
    oad.5 $e |- k =< f $.
    oad.6 $e |- ( h ^ ( b ->1 d ) ) =< k $.
    $( OA Distributive law.  In this section, we postulate this temporary axiom
       (intended not to be used outside of this section) for the OA
       distributive law, and derive from it the 6-OA, in theorem ~ d6oa .  This
       together with the derivation of the distributive law in theorem
       ~ 4oadist shows that the OA distributive law is equivalent to the 6-OA.
       (Contributed by NM, 30-Dec-1998.) $)
    ax-oadist $a |- ( h ^ ( j v k ) ) = ( ( h ^ j ) v ( h ^ k ) ) $.
  $}

  ${
    d3oa.1 $e |- f =
                ( ( a ^ b ) v ( ( a ->1 c ) ^ ( b ->1 c ) ) ) $.
    $( Derivation of 3-OA from OA distributive law.  (Contributed by NM,
       30-Dec-1998.) $)
    d3oa $p |- ( ( a ->1 c ) ^ f ) =< ( b ->1 c ) $=
      ( wi1 wa wn wi2 wo lear bltr le2or id leid ax-r1 leo letr ax-r2 lbtr bile
      1oai1 2oath1i1 df-i1 ax-a1 df-i2 ax-a2 lea ax-oadist wi0 u12lem df-i0 lan
      ax-r5 oridm le3tr2 ) ACFZABGZHZUQBCFZGZFZGZUQUSVAIZGZJZUTUTJUQDGZUTVCUTVE
      UTABCUBVEVAUTABCUCUQUTKLMVFUQVBVDJZGZVGVIVFABACAAGUQUQGJBAGUTUQGJGZURVAJZ
      VJJZUQVBVDVJNVLNUQOVBVKVLVBUSHZUSVAGZJVKUSVAUDVMURVNVAVMURURVMURUEZPZUAUS
      VAKMLVKVJQZRVDVKVLVDVMVAHZGZVAJZVKVDVAVSJZVTUSVAUFZVAVSUGSVSURVAVAVSVMURV
      MVRUHVPTVAOMLVQRVAWAVDVAVSQVDWAWBPTUIPVHDUQVHVKDVHVMVAJZVKVHUSVAUJWCUSVAU
      KUSVAULSVKWCURVMVAVOUNPSDVKEPSUMSUTUOUP $.
  $}

  ${
    d4oa.2 $e |- e =
                ( ( a ^ b ) v ( ( a ->1 d ) ^ ( b ->1 d ) ) ) $.
    d4oa.1 $e |- f =
                ( ( ( a ^ c ) v ( ( a ->1 d ) ^ ( c ->1 d ) ) ) ^
                  ( ( b ^ c ) v ( ( b ->1 d ) ^ ( c ->1 d ) ) ) ) $.
    $( Variant of proper 4-OA proved from OA distributive law.  (Contributed by
       NM, 30-Dec-1998.) $)
    d4oa $p |- ( ( a ->1 d ) ^ ( e v f ) ) =< ( b ->1 d ) $=
      ( wi1 wo wa lan id 2or leor ax-r1 ax-r2 d3oa bltr ancom ax-a2 anass leran
      leid leo lbtr ax-oadist letr lel2or ) ADIZEFJZKZUJFKZUJEKZJZBDIZULUJFEJZK
      UOUKUQUJEFUALABCDACKUJCDIZKJZBCKZUPURKZJZKZUKUJFEVCMEABKZUJUPKZJZFVCGHNUJ
      UDFEOEFUEVEVFEVEVDOEVFGPUFUGQUMUPUNUMURVBKZUPUMUJUSKZVBKZVGUMUJVCKZVIFVCU
      JHLVIVJUJUSVBUBPQVHURVBACDUSUSMRUCSCBDVBUTCBKVAURUPKBCTUPURTNRUHABDEGRUIS
      $.
  $}

  ${
    d6oa.1 $e |- a =< b ' $.
    d6oa.2 $e |- c =< d ' $.
    d6oa.3 $e |- e =< f ' $.
    $( Derivation of 6-variable orthoarguesian law from OA distributive law.
       (Contributed by NM, 30-Dec-1998.) $)
    d6oa $p |- ( ( ( a v b ) ^ ( c v d ) ) ^ ( e v f ) ) =<
                   ( b v ( a ^ ( c v ( ( ( a v c ) ^ ( b v d ) ) ^
   ( ( ( a v e ) ^ ( b v f ) ) v ( ( c v e ) ^ ( d v f ) ) ) ) ) ) ) $=
      ( wn wa wo id wi1 d4oa oa4gto4u oa4uto4 oa4to6 ) ABCDEFAJZBJKCJZDJKLEJZFJ
      KLZSTUAGHIUBMSMTMUAMSTUAUBSTUAUBTUBNZSUBNZUAUBNZUCUDUEUBUCUDKUCUBNZUDUBNZ
      KLZUCUEKUFUEUBNZKLUDUEKUGUIKLKZUHMUJMOUDMUCMUEMPQR $.
  $}

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
                  Orthoarguesian laws
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$( R. Godowski and R. Greechie, Demonstratio Mathematica 17, 241 (1984) $)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        3-variable orthoarguesian law
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( 3-variable consequence of the orthoarguesion law.  (Contributed by NM,
     20-Jul-1999.) $)
  ax-3oa $a |- ( ( a ->1 c ) ^
              ( ( a ^ b ) v ( ( a ->1 c ) ^ ( b ->1 c ) ) ) )
               =< ( b ->1 c ) $.

  $( Orthoarguesian law - ` ->2 ` version.  (Contributed by NM,
     20-Jul-1999.) $)
  oal2 $p |- ( ( a ->2 b ) ^
              ( ( b v c ) ' v ( ( a ->2 b ) ^ ( a ->2 c ) ) ) )
               =< ( a ->2 c ) $=
    ( wn wi1 wa wo wi2 ax-3oa i2i1 anor3 ax-r1 2an 2or le3tr1 ) BDZADZEZPCDZFZR
    SQEZFZGZFUAABHZBCGDZUDACHZFZGZFUFPSQIUDRUHUCABJZUETUGUBTUEBCKLUDRUFUAUIACJZ
    MNMUJO $.

  $( Orthoarguesian law - ` ->1 ` version derived from ` ->1 ` version.
     (Contributed by NM, 25-Nov-1998.) $)
  oal1 $p |- ( ( a ->1 c ) ^
              ( ( a ^ b ) v ( ( a ->1 c ) ^ ( b ->1 c ) ) ) )
               =< ( b ->1 c ) $=
    ( wn wi2 wo wa wi1 oal2 i1i2 df-a 2an 2or le3tr1 ) CDZADZEZPBDZFDZQOREZGZFZ
    GTACHZABGZUCBCHZGZFZGUEOPRIUCQUGUBACJZUDSUFUAABKUCQUETUHBCJZLMLUIN $.

  $( Orthoarguesian law.  Godowski/Greechie, Eq.  III. (Contributed by NM,
     22-Sep-1998.) $)
  oaliii $p |- ( ( a ->2 b ) ^
              ( ( b v c ) ' v ( ( a ->2 b ) ^ ( a ->2 c ) ) ) ) =
     ( ( a ->2 c ) ^ ( ( b v c ) ' v ( ( a ->2 b ) ^ ( a ->2 c ) ) ) ) $=
    ( wi2 wo wn wa anass anidm lan ax-r2 ax-r1 oal2 leran ax-a2 ax-r4 ancom 2or
    bltr ran lebi ) ABDZBCEZFZUBACDZGZEZGZUEUGGZUHUHUGGZUIUJUHUJUBUGUGGZGUHUBUG
    UGHUKUGUBUGIZJKLUHUEUGABCMNSUIUECBEZFZUEUBGZEZGZUGGZUHURUIURUEUPUGGZGUIUEUP
    UGHUSUGUEUSUKUGUPUGUGUNUDUOUFUMUCCBOPUEUBQRTULKJKLUQUBUGACBMNSUA $.

  $( Orthoarguesian law.  Godowski/Greechie, Eq.  II. This proof references
     ~ oaliii only.  (Contributed by NM, 22-Sep-1998.) $)
  oalii $p |- ( b ' ^ ( ( a ->2 b ) v ( ( a ->2 c ) ^ ( ( b v c ) '
                v ( ( a ->2 b ) ^ ( a ->2 c ) ) ) ) ) ) =< a ' $=
    ( wn wi2 wo wa orabs oaliii lor df-i2 ancom ax-r2 3tr2 lan omlan lear bltr
    ) BDZABEZACEZBCFDTUAGFZGZFZGZSADZGZUFUESBUGFZGUGUDUHSTTUBGZFTUDUHTUBHUIUCTA
    BCIJTBUFSGZFUHABKUJUGBUFSLJMNOBUFPMSUFQR $.

  $( Orthoarguesian law.  Godowski/Greechie, Eq.  IV. (Contributed by NM,
     25-Nov-1998.) $)
  oaliv $p |- ( b ' ^ ( ( a ->2 b ) v ( ( a ->2 c ) ^ ( ( b v c ) '
                v ( ( a ->2 b ) ^ ( a ->2 c ) ) ) ) ) ) =<
              ( ( b ' ^ ( a ->2 b ) ) v ( c ' ^ ( a ->2 c ) ) ) $=
    ( wn wi2 wo lea oalii ler2an df-i2 ancom lor ax-r2 lan omlan ax-r1 lbtr leo
    wa letr ) BDZABEZACEZBCFDUBUCSFSFZSZUAUBSZUFCDUCSZFUEUAADZSZUFUEUAUHUAUDGAB
    CHIUFUIUFUABUIFZSUIUBUJUAUBBUHUASZFUJABJUKUIBUHUAKLMNBUHOMPQUFUGRT $.

  $( OA theorem.  (Contributed by NM, 12-Oct-1998.) $)
  oath1 $p |- ( ( a ->2 b ) ^
              ( ( b v c ) ' v ( ( a ->2 b ) ^ ( a ->2 c ) ) ) ) =
              ( ( a ->2 b ) ^ ( a ->2 c ) ) $=
    ( wi2 wo wn wa oaliii lan anidm ax-r1 anandir 3tr1 ax-a2 anabs 3tr ) ABDZBC
    EFZQACDZGZEZGZTUAGZTTREZGTUBUBGZUBSUAGZGUBUCUBUFUBABCHIUEUBUBJKQSUALMUAUDTR
    TNITROP $.

  $( Lemma.  (Contributed by NM, 16-Oct-1998.) $)
  oalem1 $p |- ( ( b v c ) v ( ( b v c ) ' ^ ( ( a ->2 b )
                v ( ( a ->2 c ) ^ ( ( b v c ) '
                v ( ( a ->2 b ) ^ ( a ->2 c ) ) ) ) ) ) ) =<
                ( a ->2 ( b v c ) ) $=
    ( wo wn wi2 wa anidm ran ax-r1 anor3 an32 ax-r2 3tr2 anass oalii lelan bltr
    ancom lbtr lelor df-i2 ) BCDZUCEZABFZACFZUDUEUFGDGDZGZDUCAEZUDGZDZAUCFZUHUJ
    UCUHUDUIGZUJUHUDBEZGZUGGZUMUDUOUGUNCEZGZUNUNGZUQGZUDUOUTURUSUNUQUNHIJBCKZUT
    URUNGUOUNUNUQLURUDUNVAIMNIUPUDUNUGGZGUMUDUNUGOVBUIUDABCPQRRUDUISTUAULUKAUCU
    BJT $.

  $( Lemma.  (Contributed by NM, 16-Oct-1998.) $)
  oalem2 $p |- ( ( a ->2 b )
                v ( ( a ->2 c ) ^ ( ( b v c ) '
                v ( ( a ->2 b ) ^ ( a ->2 c ) ) ) ) ) =
                ( a ->2 b ) $=
    ( wi2 wo wn wa ax-a2 ax-r4 ancom 2or lan oath1 ax-r2 lor orabs 3tr ) ABDZAC
    DZBCEZFZRSGZEZGZERSRGZERUBERUDUERUDSCBEZFZUEEZGUEUCUHSUAUGUBUETUFBCHIRSJKLA
    CBMNOUEUBRSRJORSPQ $.

  ${
    oadist2a.1 $e |- ( d v ( ( b v c ) ->2 ( ( a ->2 b ) ^ ( a ->2 c ) ) ) )
                 =< ( ( b v c ) ->0 ( ( a ->2 b ) ^ ( a ->2 c ) ) ) $.
    $( Distributive inference derived from OA. (Contributed by NM,
       17-Nov-1998.) $)
    oadist2a $p |- ( ( a ->2 b ) ^
        ( d v ( ( b v c ) ->2 ( ( a ->2 b ) ^ ( a ->2 c ) ) ) ) ) =
  ( ( ( a ->2 b ) ^ d ) v
    ( ( a ->2 b ) ^ ( ( b v c ) ->2 ( ( a ->2 b ) ^ ( a ->2 c ) ) ) ) ) $=
      ( wi2 wo wa ax-a2 lan wi0 bltr lelan wn df-i0 oath1 ax-r2 leo df-i2 ax-r1
      lbtr letr distlem ) ABFZDBCGZUDACFHZFZGZHUDUGDGZHZUDDHZUDUGHZGZUHUIUDDUGI
      JUJULUKGUMUDUGDUJUDUEUFKZHZUGUIUNUDUIUHUNUGDIELMUOUFUGUOUDUENZUFGZHUFUNUQ
      UDUEUFOJABCPQUFUFUPUFNHZGZUGUFURRUGUSUEUFSTUALUBUCULUKIQQ $.
  $}

  ${
    oadist2b.1 $e |- d =<
                     ( ( b v c ) ->0 ( ( a ->2 b ) ^ ( a ->2 c ) ) ) $.
    $( Distributive inference derived from OA. (Contributed by NM,
       17-Nov-1998.) $)
    oadist2b $p |- ( ( a ->2 b ) ^
        ( d v ( ( b v c ) ->2 ( ( a ->2 b ) ^ ( a ->2 c ) ) ) ) ) =
  ( ( ( a ->2 b ) ^ d ) v
    ( ( a ->2 b ) ^ ( ( b v c ) ->2 ( ( a ->2 b ) ^ ( a ->2 c ) ) ) ) ) $=
      ( wo wi2 wa wi1 wi0 u12lem ax-r1 lbtr leor lel2or oadist2a ) ABCDDBCFZABG
      ACGHZGZFQRIZSFZQRJZDUASDUBUAEUAUBQRKZLMSTNOUCMP $.
  $}

  ${
    oadist2.1 $e |- ( d v ( ( b v c ) ->2 ( ( a ->2 b ) ^ ( a ->2 c ) ) ) )
                 = ( ( b v c ) ->0 ( ( a ->2 b ) ^ ( a ->2 c ) ) ) $.
    $( Distributive inference derived from OA. (Contributed by NM,
       17-Nov-1998.) $)
    oadist2 $p |- ( ( a ->2 b ) ^
        ( d v ( ( b v c ) ->2 ( ( a ->2 b ) ^ ( a ->2 c ) ) ) ) ) =
  ( ( ( a ->2 b ) ^ d ) v
    ( ( a ->2 b ) ^ ( ( b v c ) ->2 ( ( a ->2 b ) ^ ( a ->2 c ) ) ) ) ) $=
      ( wo wi2 wa wi0 bile oadist2a ) ABCDDBCFZABGACGHZGFLMIEJK $.
  $}

  $( Distributive law derived from OA. (Contributed by NM, 17-Nov-1998.) $)
  oadist12 $p |- ( ( a ->2 b ) ^
        ( ( ( b v c ) ->1 ( ( a ->2 b ) ^ ( a ->2 c ) ) ) v
          ( ( b v c ) ->2 ( ( a ->2 b ) ^ ( a ->2 c ) ) ) ) ) =
  ( ( ( a ->2 b ) ^ ( ( b v c ) ->1 ( ( a ->2 b ) ^ ( a ->2 c ) ) ) ) v
    ( ( a ->2 b ) ^ ( ( b v c ) ->2 ( ( a ->2 b ) ^ ( a ->2 c ) ) ) ) ) $=
    ( wo wi2 wa wi1 u12lem oadist2 ) ABCBCDZABEACEFZGJKHI $.

  ${
    oacom.1 $e |- d C ( ( b v c ) ->0 ( ( a ->2 b ) ^ ( a ->2 c ) ) ) $.
    oacom.2 $e |- ( d ^ ( ( b v c ) ->0 ( ( a ->2 b ) ^ ( a ->2 c ) ) ) )
           C ( a ->2 b ) $.
    $( Commutation law requiring OA. (Contributed by NM, 19-Nov-1998.) $)
    oacom $p |- d C ( ( a ->2 b ) ^ ( a ->2 c ) ) $=
      ( wi2 wo wa wi0 comcom ancom bctr gsth2 wn df-i0 lan oath1 ax-r2 cbtr ) D
      ABGZBCHZUAACGIZJZIZUCUEDUAUDDDUDEKUDDIZUAUFDUDIUAUDDLFMKNKUEUAUBOUCHZIUCU
      DUGUAUBUCPQABCRST $.
  $}

  ${
    oacom2.1 $e |- d =<
       ( ( a ->2 b ) ^ ( ( b v c ) ->0 ( ( a ->2 b ) ^ ( a ->2 c ) ) ) ) $.
    $( Commutation law requiring OA. (Contributed by NM, 19-Nov-1998.) $)
    oacom2 $p |- d C ( ( a ->2 b ) ^ ( a ->2 c ) ) $=
      ( wo wi2 wa wi0 lear letr lecom lea oacom ) ABCDDBCFABGZACGHIZDOPHZPEOPJK
      LDPHZORDODPMDQOEOPMKKLN $.
  $}

  ${
    oacom3.1 $e |- ( d ^ ( a ->2 b ) )
           C ( ( b v c ) ->0 ( ( a ->2 b ) ^ ( a ->2 c ) ) ) $.
    oacom3.2 $e |- d C ( a ->2 b ) $.
    $( Commutation law requiring OA. (Contributed by NM, 19-Nov-1998.) $)
    oacom3 $p |- d C ( ( a ->2 b ) ^ ( a ->2 c ) ) $=
      ( wo wi2 wa wi0 comcom ancom bctr gsth2 wn df-i0 ran oath1 3tr cbtr ) DBC
      GZABHZACHIZJZUBIZUCUEDUDUBDDUBFKUBDIZUDUFDUBIUDUBDLEMKNKUEUAOUCGZUBIUBUGI
      UCUDUGUBUAUCPQUGUBLABCRST $.
  $}

  ${
    oagen1.1 $e |- d =< ( ( b v c ) ->0 ( ( a ->2 b ) ^ ( a ->2 c ) ) ) $.
    $( "Generalized" OA. (Contributed by NM, 19-Nov-1998.) $)
    oagen1 $p |- ( ( a ->2 b ) ^
              ( d v ( ( a ->2 b ) ^ ( a ->2 c ) ) ) ) =
              ( ( a ->2 b ) ^ ( a ->2 c ) ) $=
      ( wi2 wa wo wn wi0 df-i0 lbtr leror ax-a3 oridm lor ax-r2 lelan oath1 lea
      leor ler2an lebi ) ABFZDUDACFZGZHZGZUFUHUDBCHZIZUFHZGUFUGUKUDUGUKUFHZUKDU
      KUFDUIUFJUKEUIUFKLMULUJUFUFHZHUKUJUFUFNUMUFUJUFOPQLRABCSLUFUDUGUDUETUFDUA
      UBUC $.
  $}

  ${
    oagen1b.1 $e |- d =< ( a ->2 b ) $.
    oagen1b.2 $e |- e =< ( ( b v c ) ->0 ( ( a ->2 b ) ^ ( a ->2 c ) ) ) $.
    $( "Generalized" OA. (Contributed by NM, 21-Nov-1998.) $)
    oagen1b $p |- ( d ^ ( e v ( ( a ->2 b ) ^ ( a ->2 c ) ) ) ) =
              ( d ^ ( a ->2 c ) ) $=
      ( wi2 wa wo oagen1 lan anass ax-r1 df2le2 ran ax-r2 3tr2 ) DABHZESACHZIZJ
      ZIZIZDUAIZDUBIZDTIZUCUADABCEGKLUDDSIZUBIZUFUIUDDSUBMNUHDUBDSFOZPQUEUHTIZU
      GUKUEDSTMNUHDTUJPQR $.
  $}

  ${
    oagen2.1 $e |- d =< ( ( b v c ) ->0 ( ( a ->2 b ) ^ ( a ->2 c ) ) ) $.
    $( "Generalized" OA. (Contributed by NM, 19-Nov-1998.) $)
    oagen2 $p |- ( ( a ->2 b ) ^ d ) =< ( a ->2 c ) $=
      ( wi2 wa wo wn wi0 df-i0 lbtr lelan oal2 letr ) ABFZDGPBCHZIPACFZGZHZGRDT
      PDQSJTEQSKLMABCNO $.
  $}

  ${
    oagen2b.1 $e |- d =< ( a ->2 b ) $.
    oagen2b.2 $e |- e =< ( ( b v c ) ->0 ( ( a ->2 b ) ^ ( a ->2 c ) ) ) $.
    $( "Generalized" OA. (Contributed by NM, 21-Nov-1998.) $)
    oagen2b $p |- ( d ^ e ) =< ( a ->2 c ) $=
      ( wa wi2 leran oagen2 letr ) DEHABIZEHACIDMEFJABCEGKL $.
  $}

  $( Mladen's OA (Contributed by NM, 20-Nov-1998.) $)
  mloa $p |- ( ( a == b ) ^ ( ( b == c ) v ( ( b v ( a == b ) )
         ^ ( c v ( a == c ) ) ) ) ) =< ( c v ( a == c ) ) $=
    ( wi2 wa wn wo tb lea ax-a3 or12 anor3 ax-r2 leo df-i2 ax-r1 lbtr le2an 2an
    i2bi ax-r5 id bile lel2or lelor bltr oal2 letr u2lembi dfb 2or le3tr2 ) ABD
    ZBADZEZBCEZBFZCFZEZGZUMACDZEZGZEZVAABHZBCHZBVEGZCACHGZEZGZEVHVDUMBCGFZVBGZE
    VAUOUMVCVLUMUNIVCVKUPVBGZGZVLVCUPUSVBGGZVNUPUSVBJVOUSVMGVNUPUSVBKUSVKVMBCLU
    AMMVMVBVKUPVBVBBUMCVABBAFZUQEZGZUMBVQNUMVRABOPQCCVPUREZGZVACVSNVAVTACOPQRVB
    VBVBUBUCUDUEUFRABCUGUHUOVEVCVJABUIUTVFVBVIVFUTBCUJPUMVGVAVHABTACTZSUKSWAUL
    $.

  ${
    oadist.1 $e |- d =< ( ( b v c ) ->0 ( ( a ->2 b ) ^ ( a ->2 c ) ) ) $.
    $( Distributive law derived from OAL. (Contributed by NM, 20-Nov-1998.) $)
    oadist $p |- ( ( a ->2 b ) ^
              ( d v ( ( a ->2 b ) ^ ( a ->2 c ) ) ) ) =
              ( ( ( a ->2 b ) ^ d ) v ( ( a ->2 b ) ^
              ( ( a ->2 b ) ^ ( a ->2 c ) ) ) ) $=
      ( wi2 wa oagen1 bile anidm ax-r1 ran anass ax-r2 leor bltr letr ledi lebi
      wo ) ABFZDUAACFZGZTGZUADGZUAUCGZTZUDUCUGUDUCABCDEHIUCUFUGUCUAUAGZUBGUFUAU
      HUBUHUAUAJKLUAUAUBMNUFUEOPQUADUCRS $.
  $}

  ${
    oadistb.2 $e |- d =< ( a ->2 b ) $.
    oadistb.1 $e |- e =< ( ( b v c ) ->0 ( ( a ->2 b ) ^ ( a ->2 c ) ) ) $.
    $( Distributive law derived from OAL. (Contributed by NM, 20-Nov-1998.) $)
    oadistb $p |- ( d ^
              ( e v ( ( a ->2 b ) ^ ( a ->2 c ) ) ) ) =
              ( ( d ^ e ) v ( d ^
              ( ( a ->2 b ) ^ ( a ->2 c ) ) ) ) $=
      ( wi2 wa wo df2le2 ran ax-r1 anass oagen1 lan ax-r2 leor bltr ledi lebi )
      DEABHZACHIZJZIZDEIZDUCIZJZUEUGUHUEDUBIZUDIZUGUJUEUIDUDDUBFKLMUJDUBUDIZIUG
      DUBUDNUKUCDABCEGOPQQUGUFRSDEUCTUA $.
  $}

  ${
    oadistc0.1 $e |- d =< ( ( a ->2 b ) ^ ( a ->2 c ) ) $.
    $( Note: inference of 2nd hyp. from 1st may be an OM theorem. $)
    oadistc0.2 $e |- ( ( a ->2 c ) ^
                        ( ( a ->2 b ) ^ ( ( b v c ) ' v d ) ) ) =<
                      ( ( ( a ->2 b ) ^ ( b v c ) ' ) v d ) $.
    $( Pre-distributive law.  (Contributed by NM, 30-Nov-1998.) $)
    oadistc0 $p |- ( ( a ->2 b ) ^ ( ( b v c ) ' v d ) ) =
                   ( ( ( a ->2 b ) ^ ( b v c ) ' ) v d ) $=
      ( wi2 wo wn wa ancom lelor lelan oal2 letr df2le2 ax-r2 ax-r1 bltr ledior
      ax-a2 lea df-le2 ran lbtr lebi ) ABGZBCHIZDHZJZUGUHJDHZUJACGZUJJZUKUMUJUM
      UJULJUJULUJKUJULUJUGUHUGULJZHZJULUIUOUGDUNUHELMABCNOPQRFSUKUGDHZUIJUJDUGU
      HTUPUGUIUPDUGHUGUGDUADUGDUNUGEUGULUBOUCQUDUEUF $.
  $}

  ${
    oadistc.1 $e |- d =< ( ( a ->2 b ) ^ ( a ->2 c ) ) $.
    oadistc.2 $e |- ( ( a ->2 b ) ^ ( ( b v c ) ' v d ) ) =<
                        ( ( ( a ->2 b ) ^ ( b v c ) ' ) v d ) $.
    $( Distributive law.  (Contributed by NM, 21-Nov-1998.) $)
    oadistc $p |- ( ( a ->2 b ) ^ ( ( b v c ) ' v d ) ) =
             ( ( ( a ->2 b ) ^ ( b v c ) ' ) v ( ( a ->2 b ) ^ d ) ) $=
      ( wi2 wo wn wa lea letr df2le2 ax-r1 ancom ax-r2 lor lbtr ledi lebi ) ABG
      ZBCHIZDHJZUAUBJZUADJZHZUCUDDHUFFDUEUDDDUAJZUEUGDDUADUAACGZJUAEUAUHKLMNDUA
      OPQRUAUBDST $.
  $}

  ${
    oadistd.1 $e |- d =< ( a ->2 b ) $.
    oadistd.2 $e |- e =< ( ( b v c ) ->0 ( ( a ->2 b ) ^ ( a ->2 c ) ) ) $.
    oadistd.3 $e |- f =< ( ( b v c ) ->0 ( ( a ->2 b ) ^ ( a ->2 c ) ) ) $.
    oadistd.4 $e |- ( d ^ ( a ->2 c ) ) =< f $.
    $( OA distributive law.  (Contributed by NM, 21-Nov-1998.) $)
    oadistd $p |- ( d ^ ( e v f ) ) = ( ( d ^ e ) v ( d ^ f ) ) $=
      ( wo wa wi2 lbtr df2le2 ax-r1 lan ax-r2 bltr letr le2or oridm lelan df-i0
      wi0 wn leo oagen1b lear an32 lea leor ledi lebi ) DEFKZLZDELZDFLZKZUPURUS
      UPUPDACMZLZLZURUPUPDBCKZABMUTLZUEZLZLZVBVGUPUPVFUOVEDUOVEVEKVEEVEFVEHIUAV
      EUBNUCOPVFVAUPVFDVCUFZVDKZLVAVEVIDVCVDUDZQABCDVHGVHVIVEVHVDUGVEVIVJPNUHRQ
      RVBVAURUPVAUIVAURUTLZURVAVAFLZVKVLVAVAFJOPDUTFUJRURUTUKSTSURUQULTDEFUMUN
      $.
  $}

  $( Alternate form for the 3-variable orthoarguesion law.  (Contributed by NM,
     27-May-2004.) $)
  3oa2 $p |- ( ( a ->1 c ) ^
              ( ( ( a ->1 c ) ^ ( b ->1 c ) ) v
                 ( ( a ' ->1 c ) ^ ( b ' ->1 c ) ) ) )
               =< ( b ->1 c ) $=
    ( wn wi1 wa wo ax-3oa u1lem11 ax-a2 2an ax-r5 ax-r2 le3tr2 ) ADCEZCEZOBDCEZ
    FZPQCEZFZGZFSACEZUBBCEZFZRGZFUCOQCHPUBUAUEACIZUATRGUERTJTUDRPUBSUCUFBCIZKLM
    KUGN $.

  $( 3-variable orthoarguesion law expressed with the 3OA identity
     abbreviation.  (Contributed by NM, 27-May-2004.) $)
  3oa3 $p |- ( ( a ->1 c ) ^ ( a == c ==OA b ) ) =< ( b ->1 c ) $=
    ( wi1 wid3oa wa wn wo df-id3oa lan 3oa2 bltr ) ACDZABCEZFMMBCDZFAGCDBGCDFHZ
    FONPMABCIJABCKL $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        4-variable orthoarguesian law
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    oal4.1 $e |- a =< b ' $.
    oal4.2 $e |- c =< d ' $.
    $( Orthoarguesian law (4-variable version).  (Contributed by NM,
       1-Dec-1998.) $)
    ax-oal4 $a |- ( ( a v b ) ^ ( c v d ) ) =< ( b v ( a ^ ( c v
                   ( ( a v c ) ^ ( b v d ) ) ) ) ) $.
  $}

  $( 4-variable OA closed equational form.  (Contributed by NM, 1-Dec-1998.) $)
  oa4cl $p |- ( ( a v ( b ^ a ' ) ) ^ ( c v ( d ^ c ' ) ) ) =<
              ( ( b ^ a ' ) v ( a ^ ( c v
              ( ( a v c ) ^ ( ( b ^ a ' ) v ( d ^ c ' ) ) ) ) ) ) $=
    ( wn wa wo leor oran2 lbtr ax-oal4 ) ABAEFZCDCEFZABEZAGLEANHBAIJCDEZCGMECOH
    DCIJK $.

  $( Derivation of 3-variable OA from 4-variable OA. (Contributed by NM,
     28-Nov-1998.) $)
  oa43v $p |- ( ( a ->2 b ) ^
            ( ( b v c ) ' v ( ( a ->2 b ) ^ ( a ->2 c ) ) ) )
             =< ( a ->2 c ) $=
    ( wi2 wn wo wa ud2lem0c lea bltr ax-oal4 id oa4v3v oal42 oa23 ) ABCACBACBAC
    DEZABDEZPCEZACFZGRACHRSIJZQBEZABFZGUAABHUAUBIJZPCQBTUCKPLQLMNO $.

  ${
    oa3moa3.1 $e |- a =< b ' $.
    oa3moa3.2 $e |- c =< d ' $.
    oa3moa3.3 $e |- d =< e ' $.
    oa3moa3.4 $e |- e =< c ' $.
    $( 4-variable 3OA to 5-variable Mayet's 3OA. (Contributed by NM,
       3-Apr-2009.)  (Revised by NM, 31-Mar-2011.) $)
    oa3moa3 $p |- ( ( a v b ) ^ ( ( c v d ) v e ) ) =< ( a v ( ( ( b ^ ( c v
         ( ( b v c ) ^ ( ( a v d ) v e ) ) ) ) ^ ( d v ( ( b v d ) ^ ( ( a v
          c ) v e ) ) ) ) ^ ( e v ( ( b v e ) ^ ( ( a v c ) v d ) ) ) ) ) $=
      ( wo wa lecon3 wn lel2or lan lor lel lecom comcom7 comcom ax-a2 ax-a3 2an
      ax-oal4 orass le3tr1 ror tr ler2an fh3 cm anandi lbtr ax-r1 anass 3tr1 )
      ABJZCDJZEJZKZABCBCJZADJEJZKZJZKZJZABDBDJZACJZEJZKZJZEBEJZVHDJZKZJZKZKZJZK
      ZAVEVKKVOKZJZUTVFVRBAJZCDEJZJZKABCVAAWCJZKZJZKZJUTVFBACWCABFLZWCCDCMECDGL
      INLUDUQWBUSWDABUAZCDEUBUCVEWHAVDWGBVCWFCVBWEVAADEUEOPOPUFUTABVKKZJZABVOKZ
      JZKZVRUTWLWNWBDCEJZJZKABDVGAWPJZKZJZKZJUTWLBADWPWIWPDCDMEGDEHLNLUDUQWBUSW
      QWJUSDCJZEJWQURXBECDUAUGDCEUEUHUCWKXAAVKWTBVJWSDVIWRVGACEUEOPOPUFWBEURJZK
      ABEVLAURJZKZJZKZJUTWNBAEURWIURECEMDECILHNLUDUQWBUSXCWJUREUAUCWMXGAVOXFBVN
      XEEVMXDVLACDUBOPOPUFUIWOAWKWMKZJZVRXIWOAWKWMWKAWKAWKAMZBXJVKWIQRSTWMAWMAW
      MXJBXJVOWIQRSTUJUKXHVQAVQXHBVKVOULUKPUHUMUIVSAVEVQKZJZWAXLVSAVEVQVEAVEAVE
      XJBXJVDWIQRSTVQAVQAVQXJBXJVPWIQRSTUJUNXKVTABVDVPKKZVEVPKZXKVTXNXMBVDVPUOU
      KXMXKBVDVPULUNVEVKVOUOUPPUHUM $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
         6-variable orthoarguesian law
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    oal6.1 $e |- a =< b ' $.
    oal6.2 $e |- c =< d ' $.
    oal6.3 $e |- e =< f ' $.
    $( Orthoarguesian law (6-variable version).  (Contributed by NM,
       29-Nov-1998.) $)
    ax-oa6 $a |- ( ( ( a v b ) ^ ( c v d ) ) ^ ( e v f ) ) =<
                   ( b v ( a ^ ( c v ( ( ( a v c ) ^ ( b v d ) ) ^
   ( ( ( a v e ) ^ ( b v f ) ) v ( ( c v e ) ^ ( d v f ) ) ) ) ) ) ) $.
  $}

  ${
    oa64v.1 $e |- a =< b ' $.
    oa64v.2 $e |- c =< d ' $.
    $( Derivation of 4-variable OA from 6-variable OA. (Contributed by NM,
       29-Nov-1998.) $)
    oa64v $p |- ( ( a v b ) ^ ( c v d ) ) =< ( b v ( a ^ ( c v
                   ( ( a v c ) ^ ( b v d ) ) ) ) ) $=
      ( wf wt wn le0 ax-oa6 id oa6v4v ) ABCDGHABCDGHEFHIJKGLHLM $.
  $}

  $( Derivation of 3-variable OA from 6-variable OA. (Contributed by NM,
     28-Nov-1998.) $)
  oa63v $p |- ( ( a ->2 b ) ^
            ( ( b v c ) ' v ( ( a ->2 b ) ^ ( a ->2 c ) ) ) )
             =< ( a ->2 c ) $=
    ( wi2 wn wo wa ud2lem0c lea bltr oa64v id oa4v3v oal42 oa23 ) ABCACBACBACDE
    ZABDEZPCEZACFZGRACHRSIJZQBEZABFZGUAABHUAUBIJZPCQBTUCKPLQLMNO $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        The proper 4-variable orthoarguesian law
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( The proper 4-variable OA law.  (Contributed by NM, 20-Jul-1999.) $)
  ax-4oa $a |- ( ( a ->1 d ) ^ ( (
             ( a ^ b ) v ( ( a ->1 d ) ^ ( b ->1 d ) ) ) v
             ( ( ( a ^ c ) v ( ( a ->1 d ) ^ ( c ->1 d ) ) ) ^
                 ( ( b ^ c ) v ( ( b ->1 d ) ^ ( c ->1 d ) ) ) ) ) )
             =< ( b ->1 d ) $.

  $( The proper 4-variable OA law.  (Contributed by NM, 20-Jul-1999.) $)
  axoa4 $p |- ( a ' ^ ( a v ( b ^
               ( ( ( a ^ b ) v ( ( a ->1 d ) ^ ( b ->1 d ) ) ) v (
                 ( ( a ^ c ) v ( ( a ->1 d ) ^ ( c ->1 d ) ) ) ^
                 ( ( b ^ c ) v ( ( b ->1 d ) ^ ( c ->1 d ) ) ) ) ) ) ) ) =<
                 d $=
    ( wn wa wi1 wo u1lem9b leran ax-4oa id oa4gto4u oa4uto4 letr ) AEZABABFADGZ
    BDGZFHACFQCDGZFHBCFRSFHFHFHZFQTFDPQTADIJABCDABCDRQSRQSDKQLRLSLMNO $.

  $( Proper 4-variable OA law variant.  (Contributed by NM, 22-Dec-1998.) $)
  axoa4b $p |- ( ( a ->1 d ) ^ ( a v ( b ^
               ( ( ( a ^ b ) v ( ( a ->1 d ) ^ ( b ->1 d ) ) ) v (
                 ( ( a ^ c ) v ( ( a ->1 d ) ^ ( c ->1 d ) ) ) ^
                 ( ( b ^ c ) v ( ( b ->1 d ) ^ ( c ->1 d ) ) ) ) ) ) ) ) =<
                 d $=
    ( axoa4 oa4ctob ) ABCDABCDEF $.

  ${
    oa6.1 $e |- a =< b ' $.
    oa6.2 $e |- c =< d ' $.
    oa6.3 $e |- e =< f ' $.
    $( Derivation of 6-variable orthoarguesian law from 4-variable version.
       (Contributed by NM, 18-Dec-1998.) $)
    oa6 $p |- ( ( ( a v b ) ^ ( c v d ) ) ^ ( e v f ) ) =<
                   ( b v ( a ^ ( c v ( ( ( a v c ) ^ ( b v d ) ) ^
   ( ( ( a v e ) ^ ( b v f ) ) v ( ( c v e ) ^ ( d v f ) ) ) ) ) ) ) $=
      ( wn wa wo id axoa4b oa4to6 ) ABCDEFAJZBJKCJZDJKLEJZFJKLZPQRGHISMPMQMRMPQ
      RSNO $.
  $}

  $( Proper 4-variable OA law variant.  (Contributed by NM, 22-Dec-1998.) $)
  axoa4a $p |- ( ( a ->1 d ) ^ ( a v ( b ^
               ( ( ( a ^ b ) v ( ( a ->1 d ) ^ ( b ->1 d ) ) ) v (
                 ( ( a ^ c ) v ( ( a ->1 d ) ^ ( c ->1 d ) ) ) ^
                 ( ( b ^ c ) v ( ( b ->1 d ) ^ ( c ->1 d ) ) ) ) ) ) ) ) =<
                 ( ( ( a ^ d ) v ( b ^ d ) ) v ( c ^ d ) ) $=
    ( wi1 wn id wa wo leo df-i1 ax-r1 ax-a1 ax-r2 lbtr oa6 oa6to4 ) AADEZBBDEZC
    CDEZDRFZGSFZGTFZGAFZUABFZUBCFZUCUDUDADHZIZUAFZUDUGJUHRUIRUHADKLRMNOUEUEBDHZ
    IZUBFZUEUJJUKSULSUKBDKLSMNOUFUFCDHZIZUCFZUFUMJUNTUOTUNCDKLTMNOPQ $.

  $( Proper 4-variable OA law variant.  (Contributed by NM, 24-Dec-1998.) $)
  axoa4d $p |- ( a ^ ( (
                   ( a ^ b ) v ( ( a ->1 d ) ^ ( b ->1 d ) ) ) v
               ( ( ( a ^ c ) v ( ( a ->1 d ) ^ ( c ->1 d ) ) ) ^
                 ( ( b ^ c ) v ( ( b ->1 d ) ^ ( c ->1 d ) ) ) ) ) )
             =< ( b ' ->1 d ) $=
    ( wa wi1 wo wn oa4dcom ax-r1 axoa4 oa4ctod bltr ) AABEADFZBDFZEGACENCDFZEGZ
    BCEOPEGZEGEZABAEONEGRQEGEZBHDFTSBACDIJBACDBACDKLM $.

  ${
    4oa.1 $e |- e =
                ( ( ( a ^ c ) v ( ( a ->1 d ) ^ ( c ->1 d ) ) ) ^
                  ( ( b ^ c ) v ( ( b ->1 d ) ^ ( c ->1 d ) ) ) ) $.
    $( Generalized "alpha" expression. $)
    4oa.2 $e |- f =
                ( ( ( a ^ b ) v ( ( a ->1 d ) ^ ( b ->1 d ) ) ) v e ) $.
    $( Variant of proper 4-OA. (Contributed by NM, 29-Dec-1998.) $)
    4oa $p |- ( ( a ->1 d ) ^ f ) =< ( b ->1 d ) $=
      ( wi1 wa wo lan wn axoa4a id oa4to4u2 oa4uto4g bltr ) ADIZFJSABJSBDIZJKEK
      ZJTFUASHLABCDEBMZAMZCMZDUBMDIZUCMDIZUDMDIZUEUFUGDNUEOUFOUGOPGQR $.

    $( Proper OA analog to Godowski/Greechie, Eq.  III. (Contributed by NM,
       29-Dec-1998.) $)
    4oaiii $p |- ( ( a ->1 d ) ^ f ) = ( ( b ->1 d ) ^ f ) $=
      ( wi1 wa 4oa lear ler2an wo ancom ax-r2 2or ax-r5 lebi ) ADIZFJZBDIZFJZUA
      UBFABCDEFGHKTFLMUCTFBACDEFEACJTCDIZJNZBCJUBUDJNZJUFUEJGUEUFOPFABJZTUBJZNZ
      ENBAJZUBTJZNZENHUIULEUGUJUHUKABOTUBOQRPKUBFLMS $.

    $( Proper 4-OA theorem.  (Contributed by NM, 29-Dec-1998.) $)
    4oath1 $p |- ( ( a ->1 d ) ^ f ) = ( ( a ->1 d ) ^ ( b ->1 d ) ) $=
      ( wi1 wa wo 4oaiii lan or32 ax-r2 2an anidm ax-r1 anandir 3tr1 ax-a2 3tr
      anabs ) ADIZFJZUDBDIZJZABJZEKZUGKZJZUGUGUIKZJUGUEUEJZUDUJJZUFUJJZJZUEUKUM
      UEUFFJZJUPUEUQUEABCDEFGHLMUEUNUQUOFUJUDFUHUGKEKUJHUHUGENOZMFUJUFURMPOUMUE
      UEQRUDUFUJSTUJULUGUIUGUAMUGUIUCUB $.

    ${
      4oagen1.1 $e |- g =< f $.
      $( "Generalized" 4-OA. (Contributed by NM, 29-Dec-1998.) $)
      4oagen1 $p |- ( ( a ->1 d ) ^
              ( g v ( ( a ->1 d ) ^ ( b ->1 d ) ) ) ) =
              ( ( a ->1 d ) ^ ( b ->1 d ) ) $=
        ( wi1 wa wo or32 ax-r2 lbtr leror ax-a3 oridm lor ax-r1 4oath1 lea leor
        lelan ler2an lebi ) ADKZGUHBDKZLZMZLZUJULUHFLUJUKFUHUKABLZEMZUJMZUJMZFG
        UOUJGFUOJFUMUJMEMUOIUMUJENOZPQUPUNUJUJMZMZFUNUJUJRUSUOFURUJUNUJSTFUOUQU
        AOOPUEABCDEFHIUBPUJUHUKUHUIUCUJGUDUFUG $.
    $}

    ${
      4oagen1b.1 $e |- g =< f $.
      4oagen1b.2 $e |- h =< ( a ->1 d ) $.
      $( "Generalized" OA. (Contributed by NM, 29-Dec-1998.) $)
      4oagen1b $p |- ( h ^ ( g v ( ( a ->1 d ) ^ ( b ->1 d ) ) ) ) =
              ( h ^ ( b ->1 d ) ) $=
        ( wi1 wa wo 4oagen1 anass ax-r1 ran ax-r2 lan df2le2 3tr2 ) HADMZGUDBDM
        ZNZOZNZNZHUFNZHUGNZHUENZUHUFHABCDEFGIJKPUAUIHUDNZUGNZUKUNUIHUDUGQRUMHUG
        HUDLUBZSTUJUMUENZULUPUJHUDUEQRUMHUEUOSTUC $.
    $}

    ${
      4oadist.1 $e |- h =< ( a ->1 d ) $.
      4oadist.2 $e |- j =< f $.
      4oadist.3 $e |- k =< f $.
      4oadist.4 $e |- ( h ^ ( b ->1 d ) ) =< k $.
      $( OA Distributive law.  This is equivalent to the 6-variable OA law, as
         shown by theorem ~ d6oa .  (Contributed by NM, 29-Dec-1998.) $)
      4oadist $p |- ( h ^ ( j v k ) ) = ( ( h ^ j ) v ( h ^ k ) ) $=
        ( wo wa wi1 ax-r1 ax-r2 le2or oridm lbtr lelan df2le2 or32 lan 4oagen1b
        leo lear an32 lea bltr letr leor ledi lebi ) GHIPZQZGHQZGIQZPZUSVAVBUSU
        SGBDRZQZQZVAUSUSGFQZQZVEVGUSUSVFURFGURFFPFHFIFMNUAFUBUCUDUESVFVDUSVFGAB
        QZEPZADRVCQZPZQVDFVKGFVHVJPEPVKKVHVJEUFTZUGABCDEFVIGJKVIVKFVIVJUIFVKVLS
        UCLUHTUGTVEVDVAUSVDUJVDVAVCQZVAVDVDIQZVMVNVDVDIOUESGVCIUKTVAVCULUMUNUMV
        AUTUOUNGHIUPUQ $.
    $}
  $}


$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
        Other stronger-than-OML laws
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        New state-related equation
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( This is the simplest known example of an equation implied by the set of
     Mayet--Godowski equations that is independent from all Godowski equations.
     It was discovered by Norman Megill and Mladen Pavicic between 1997 and
     August 2003.  This is Equation (54) in

     Mladen Pavicic, Norman D. Megill, _Quantum Logic and Quantum Computation_,
     in _Handbook of Quantum Logic and Quantum Structures_, Volume _Quantum
     Structures_, Elsevier, Amsterdam, 2007, pp. 751--787.
     ~ https://arxiv.org/abs/0812.3072

     and Equation (15) in

     Mladen Pavicic, Brendan D. McKay, Norman D. Megill, Kresimir Fresl, _Graph
     Approach to Quantum Systems_, Journal of Mathematical Physics, Volume 51,
     Issue 10, October 2010. ~ https://arxiv.org/abs/1004.0776

     (Contributed by NM, 1-Jan-1998.) $)
  ax-newstateeq $a |- ( ( ( a ->1 b ) ->1 ( c ->1 b ) ) ^
                    ( ( a ->1 c ) ^ ( b ->1 a ) ) ) =< ( c ->1 a ) $.


$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
        Contributions of Roy Longton
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Roy's first section
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    lem3.3.2.1 $e |- a = 1 $.
    lem3.3.2.2 $e |- ( a ->0 b ) = 1 $.
    $( Equation 3.2 of [PavMeg1999] p. 9.  (Contributed by Roy F. Longton,
       27-Jun-2005.)  (Revised by Roy F. Longton, 3-Jul-2005.) $)
    lem3.3.2 $p |- b = 1 $=
      ( wn wo wi0 wt df-i0 ax-r1 ax-r2 skr0 ) ABCAEBFZABGZHNMABIJDKL $.
  $}

  $( Define asymmetrical identity (for "Non-Orthomodular Models..." paper).
     (Contributed by Roy F. Longton, 27-Jun-2005.) $)
  df-id5 $a |- ( a ==5 b ) = ( ( a ^ b ) v ( a ' ^ b ' ) ) $.

  $( Define biconditional for ` ->1 ` .  (Contributed by Roy F. Longton,
     27-Jun-2005.) $)
  df-b1 $a |- ( a <->1 b ) = ( ( a ->1 b ) ^ ( b ->1 a ) ) $.

  $( Lemma for ~ lem3.3.3 .  (Contributed by Roy F. Longton, 27-Jun-2005.)
     (Revised by Roy F. Longton, 3-Jul-2005.) $)
  lem3.3.3lem1 $p |- ( a ==5 b ) =< ( a ->1 b ) $=
    ( wa wn wo wid5 wi1 ax-a2 lea leror bltr df-id5 df-i1 le3tr1 ) ABCZADZBDZCZ
    EZPOEZABFABGSROETORHRPOPQIJKABLABMN $.

  $( Lemma for ~ lem3.3.3 .  (Contributed by Roy F. Longton, 27-Jun-2005.)
     (Revised by Roy F. Longton, 3-Jul-2005.) $)
  lem3.3.3lem2 $p |- ( a ==5 b ) =< ( b ->1 a ) $=
    ( wa wn wo wid5 wi1 lear leror ax-a2 ancom lor le3tr1 df-id5 df-i1 ) ABCZAD
    ZBDZCZEZRBACZEZABFBAGSPERPETUBSRPQRHIPSJUAPRBAKLMABNBAOM $.

  $( Lemma for ~ lem3.3.3 .  (Contributed by Roy F. Longton, 27-Jun-2005.)
     (Revised by Roy F. Longton, 3-Jul-2005.) $)
  lem3.3.3lem3 $p |- ( a ==5 b ) =< ( ( a ->1 b ) ^ ( b ->1 a ) ) $=
    ( wid5 wi1 lem3.3.3lem1 lem3.3.3lem2 ler2an ) ABCABDBADABEABFG $.

  $( Equation 3.3 of [PavMeg1999] p. 9.  (Contributed by Roy F. Longton,
     27-Jun-2005.)  (Revised by Roy F. Longton, 3-Jul-2005.) $)
  lem3.3.3 $p |- ( ( a ==5 b ) ->0 ( a <->1 b ) ) = 1 $=
    ( wid5 wb1 wi0 wn wo wi1 wa wt df-i0 df-b1 lor lem3.3.3lem3 sklem 3tr ) ABC
    ZABDZEQFZRGSABHBAHIZGJQRKRTSABLMQTABNOP $.

  ${
    lem3.3.4.1 $e |- ( b ->2 a ) = 1 $.
    $( Equation 3.4 of [PavMeg1999] p. 9.  (Contributed by Roy F. Longton,
       28-Jun-2005.)  (Revised by Roy F. Longton, 3-Jul-2005.) $)
    lem3.3.4 $p |- ( a ->2 ( a ==5 b ) ) = ( a ==5 b ) $=
      ( wid5 wi2 wn wa wo df-i2 df-id5 ax-r4 lan anor3 ax-r1 ax-r2 lor 3tr1 3tr
      wf wt oran3 oran 2an anabs ran anass con2 ancom oran1 con3 df-f 3tr2 or0r
      ax-a2 ) AABDZEUOAFZUOFZGZHZSUOHZUOAUOIUSUOSHUTURSUOURUPABGZUPBFZGZHZFZGUP
      UPVBHZABHZGZGZSUQVEUPUOVDABJKLVEVHUPVEVAFZVCFZGZVHVLVEVAVCMNVJVFVKVGVFVJA
      BUANVGVKABUBZNUCOLUPVFGZVGGUPVGGZVISVNUPVGUPVBUDUEUPVFVGUFBAEZFTFVOSVPTCK
      VOVPAVGFZHZAVBUPGZHVOFZVPVQVSAVQVCVSVGVCVMUGUPVBUHOPVRVTAVGUINBAIQUJUKQUL
      RPUOSUNOUOUMR $.
  $}

  ${
    lem3.3.5lem.1 $e |- 1 =< a $.
    $( A fundamental property in quantum logic.  Lemma for ~ lem3.3.5 .
       (Contributed by Roy F. Longton, 28-Jun-2005.)  (Revised by Roy F.
       Longton, 3-Jul-2005.) $)
    lem3.3.5lem $p |- a = 1 $=
      ( wt le1 lebi ) ACADBE $.
  $}

  ${
    lem3.3.5.1 $e |- ( a ==5 b ) = 1 $.
    $( Equation 3.5 of [PavMeg1999] p. 9.  (Contributed by Roy F. Longton,
       28-Jun-2005.)  (Revised by Roy F. Longton, 3-Jul-2005.) $)
    lem3.3.5 $p |- ( a ->1 ( b v c ) ) = 1 $=
      ( wo wi1 wb1 wn wa wt df-b1 lea bltr df-i1 lbtr leo lelan lelor letr wid5
      lem3.3.3 lem3.3.2 ax-r1 le3tr1 lem3.3.5lem ) ABCEZFZABGZAHZAUFIZEZJUGUHUI
      ABIZEZUKUHABFZUMUHUNBAFZIUNABKUNUOLMABNOULUJUIBUFABCPQRSUHJABTUHDABUAUBUC
      AUFNUDUE $.
  $}

  $( Equation 3.6 of [PavMeg1999] p. 9.  (Contributed by Roy F. Longton,
     28-Jun-2005.)  (Revised by Roy F. Longton, 3-Jul-2005.) $)
  lem3.3.6 $p |- ( a ->2 ( b v c ) ) = ( ( a v c ) ->2 ( b v c ) ) $=
    ( wo wn wa wi2 anor3 ax-r1 lan anandir anass 2an 3tr2 ax-r2 lor df-i2 3tr1
    ) BCDZAEZSEZFZDSACDZEZUAFZDASGUCSGUBUESUBTBEZCEZFZFZUEUAUHTUHUABCHZIJTUFFUG
    FTUGFZUHFUIUETUFUGKTUFUGLUKUDUHUAACHUJMNOPASQUCSQR $.

  $( Equation 3.7 of [PavMeg1999] p. 9.  The variable i in the paper is set to
     0, and this is the first part of the equation.  (Contributed by Roy F.
     Longton, 28-Jun-2005.)  (Revised by Roy F. Longton, 3-Jul-2005.) $)
  lem3.3.7i0e1 $p |- ( a ->0 ( a ^ b ) ) = ( a ==0 ( a ^ b ) ) $=
    ( wn wa wo wi0 wid0 or1 ax-r1 lan an1 df-t lor 3tr2 ax-a2 ax-a3 ax-r5 oran3
    wt 3tr df-i0 df-id0 3tr1 ) ACZABDZEZUFUECZAEZDZAUEFAUEGUFUFBCZUDEZAEZDZUFUD
    UJEZAEZDUIUFUFUJAUDEZEZDZUFUJUDAEZEZDUMUFSDUFUJSEZDUFURSVAUFVASUJHIJUFKVAUQ
    UFSUPUJALMJNUQUTUFUPUSUJAUDOMJUTULUFULUTUJUDAPIJTULUOUFUKUNAUJUDOQJUOUHUFUN
    UGAABRQJTAUEUAAUEUBUC $.

  $( Equation 3.7 of [PavMeg1999] p. 9.  The variable i in the paper is set to
     0, and this is the second part of the equation.  (Contributed by Roy F.
     Longton, 28-Jun-2005.)  (Revised by Roy F. Longton, 3-Jul-2005.) $)
  lem3.3.7i0e2 $p |- ( a ==0 ( a ^ b ) ) = ( ( a ^ b ) ==0 a ) $=
    ( wn wa wo wid0 ancom df-id0 3tr1 ) ACABDZEZJCAEZDLKDAJFJAFKLGAJHJAHI $.

  $( Equation 3.7 of [PavMeg1999] p. 9.  The variable i in the paper is set to
     0, and this is the third part of the equation.  (Contributed by Roy F.
     Longton, 28-Jun-2005.)  (Revised by Roy F. Longton, 3-Jul-2005.) $)
  lem3.3.7i0e3 $p |- ( a ->0 ( a ^ b ) ) = ( a ->1 b ) $=
    ( nom10 ) ABC $.

  $( Equation 3.7 of [PavMeg1999] p. 9.  The variable i in the paper is set to
     1, and this is the first part of the equation.  (Contributed by Roy F.
     Longton, 3-Jul-2005.) $)
  lem3.3.7i1e1 $p |- ( a ->1 ( a ^ b ) ) = ( a ==1 ( a ^ b ) ) $=
    ( wn wa wo wi1 wid1 or1r ax-r1 ran an1r df-t ax-r5 3tr2 ax-a3 oran3 lor 3tr
    wt df-i1 df-id1 3tr1 ) ACZAABDZDEZAUDCZEZUEDZAUDFAUDGUEAUCEZBCZEZUEDZAUCUJE
    ZEZUEDUHSUEDSUJEZUEDUEULSUOUEUOSUJHIJUEKUOUKUESUIUJALMJNUKUNUEAUCUJOJUNUGUE
    UMUFAABPQJRAUDTAUDUAUB $.

  $( Equation 3.7 of [PavMeg1999] p. 9.  The variable i in the paper is set to
     1, and this is the second part of the equation.  (Contributed by Roy F.
     Longton, 28-Jun-2005.)  (Revised by Roy F. Longton, 3-Jul-2005.) $)
  lem3.3.7i1e2 $p |- ( a ==1 ( a ^ b ) ) = ( ( a ^ b ) ==1 a ) $=
    ( wa wn wo wid1 oran3 ax-r1 lor ran ax-a3 wt df-t ax-r5 anass ax-a2 lan 3tr
    or1r df-id1 an1r anidm an1 ancom 3tr1 ) AABCZDZEZADZAUFCZEZCZUFUIEZUGUFACZE
    ZCZAUFFUFAFULAUIBDZEZEZUKCAUIEZUQEZUKCZUPUHUSUKUGURAURUGABGHIJUSVAUKVAUSAUI
    UQKHJVBLUQEZUKCLUKCZUPVAVCUKUTLUQLUTAMHNJVCLUKUQSJVDUKUIAACZBCZEZUPUKUAUJVF
    UIVFUJAABOZHIVGUIUFEZUMUGABACZCZEZCZUPVFUFUIVEABAUBZJIVIUMUGVFEZCZUMUGUJEZC
    VMVIUMUFUGEZCZUMUGUFEZCVPVIUMUMLCZVSUIUFPWAUMUMUCHLVRUMUFMQRVRVTUMUFUGPQVTV
    OUMUFVFUGAVEBVEAVNHJIQRVOVQUMVFUJUGVHIQVQVLUMUJVKUGUFVJAABUDQIQRVLUOUMVKUNU
    GUNVKABAOHIQRRRRAUFTUFATUE $.

  $( Equation 3.7 of [PavMeg1999] p. 9.  The variable i in the paper is set to
     1, and this is the third part of the equation.  (Contributed by Roy F.
     Longton, 28-Jun-2005.)  (Revised by Roy F. Longton, 3-Jul-2005.) $)
  lem3.3.7i1e3 $p |- ( a ->1 ( a ^ b ) ) = ( a ->1 b ) $=
    ( nom11 ) ABC $.

  $( Equation 3.7 of [PavMeg1999] p. 9.  The variable i in the paper is set to
     2, and this is the first part of the equation.  (Contributed by Roy F.
     Longton, 28-Jun-2005.)  (Revised by Roy F. Longton, 3-Jul-2005.) $)
  lem3.3.7i2e1 $p |- ( a ->2 ( a ^ b ) ) = ( a ==2 ( a ^ b ) ) $=
    ( wa wn wo wi2 wid2 or1r ax-r1 ran an1r df-t ax-r5 3tr2 ax-a3 oran3 lor 3tr
    wt df-i2 df-id2 3tr1 ) ABCZADZUCDZCEZAUEEZUFCZAUCFAUCGUFAUDEZBDZEZUFCZAUDUJ
    EZEZUFCUHSUFCSUJEZUFCUFULSUOUFUOSUJHIJUFKUOUKUFSUIUJALMJNUKUNUFAUDUJOJUNUGU
    FUMUEAABPQJRAUCTAUCUAUB $.

  $( Equation 3.7 of [PavMeg1999] p. 9.  The variable i in the paper is set to
     2, and this is the second part of the equation.  (Contributed by Roy F.
     Longton, 3-Jul-2005.) $)
  lem3.3.7i2e2 $p |- ( a ==2 ( a ^ b ) ) = ( ( a ^ b ) ==2 a ) $=
    ( wa wn wo wid2 oran3 ax-r1 lor ran ax-a3 wt df-t ax-r5 anor3 ax-r4 lan 3tr
    ax-r2 df-id2 or1r an1r orabs an1 lea df-le2 3tr1 ) AABCZDZEZUHADZUICZEZCZUH
    UKEZAUIUKCZEZCZAUHFUHAFUNAUKBDZEZEZUMCAUKEZUSEZUMCZURUJVAUMUIUTAUTUIABGHIJV
    AVCUMVCVAAUKUSKHJVDLUSEZUMCLUMCZURVCVEUMVBLUSLVBAMZHNJVELUMUSUAJVFUMUHAUHEZ
    DZEZURUMUBULVIUHAUHOIVJUOURVIUKUHVHAABUCPIUOUOVBCZUOAUHAEZDZEZCURUOUOLCZVKV
    OUOUOUDHLVBUOVGQSVBVNUOUKVMAAVLVLAUHAABUEUFHPIQVNUQUOVMUPAUPVMUHAOHIQRSRRRA
    UHTUHATUG $.

  $( Equation 3.7 of [PavMeg1999] p. 9.  The variable i in the paper is set to
     2, and this is the third part of the equation.  (Contributed by Roy F.
     Longton, 28-Jun-2005.)  (Revised by Roy F. Longton, 3-Jul-2005.) $)
  lem3.3.7i2e3 $p |- ( a ->2 ( a ^ b ) ) = ( a ->1 b ) $=
    ( nom12 ) ABC $.

  $( Equation 3.7 of [PavMeg1999] p. 9.  The variable i in the paper is set to
     3, and this is the first part of the equation.  (Contributed by Roy F.
     Longton, 28-Jun-2005.)  (Revised by Roy F. Longton, 3-Jul-2005.) $)
  lem3.3.7i3e1 $p |- ( a ->3 ( a ^ b ) ) = ( a ==3 ( a ^ b ) ) $=
    ( wn wa wo wi3 wid3 anass ax-r1 ax-r5 ancom ran wf dff ax-r4 wt lan 3tr lor
    an0r or0r anor3 orabs womaa an1 df-t ax-r2 df-i3 df-id3 3tr1 ) ACZABDZDZUKU
    LCDZEZAUKULEZDZEZUPAUNEZDZAULFAULGURUKADZBDZUNEZUQEAUKDZBDZUNEZUQEZUTUOVCUQ
    UMVBUNVBUMUKABHIJJVCVFUQVBVEUNVAVDBUKAKLJJVGMBDZUNEZUQEMUNEZUQEZUTVFVIUQVEV
    HUNVDMBMVDANILJJVIVJUQVHMUNBTJJVKUNUQEZUTVJUNUQUNUAJVLAULEZCZUQEUKUQEZUTUNV
    NUQAULUBZJVNUKUQVMAABUCZOJVOUPAUKEZDZUPAVNEZDUTVOUPUPPDZVSABUDWAUPUPUEIPVRU
    PAUFQRVRVTUPUKVNAAVMVMAVQIOSQVTUSUPVNUNAUNVNVPISQRRUGRRAULUHAULUIUJ $.

  $( Equation 3.7 of [PavMeg1999] p. 9.  The variable i in the paper is set to
     3, and this is the second part of the equation.  (Contributed by Roy F.
     Longton, 28-Jun-2005.)  (Revised by Roy F. Longton, 3-Jul-2005.) $)
  lem3.3.7i3e2 $p |- ( a ==3 ( a ^ b ) ) = ( ( a ^ b ) ==3 a ) $=
    ( wn wa wo wid3 wt anor3 lor lan orabs ax-r4 df-t ax-r1 an1 ax-a2 3tr ax-r5
    ran df-id3 lea df-le2 an1r ax-r2 or1 ax-a3 oran3 3tr1 ) ACZABDZEZAUIUJCZDZE
    ZDZULAEZUJULUIDZEZDZAUJFUJAFUOBCZUIEZAEZURDZUIUTEZAEZURDUSUOUTAUIEZEZURDZUT
    UIAEZEZURDVCUOGURDZUTGEZURDVHUOURVKUOUJUIEZUJUJAEZCZEURUOUKAAUJEZCZEZDUKVFD
    ZVMUNVRUKUMVQAAUJHIJVRVFUKVQUIAVPAABKLIJVSUKGDUKVMVFGUKGVFAMZNJUKOUIUJPQQUI
    VOUJAVNVNAUJAABUAUBNLIVOUQUJUQVOUJAHNIQVKURURUCNUDGVLURVLGUTUENSVLVGURGVFUT
    VTISQVGVJURVFVIUTAUIPISVJVBURVBVJUTUIAUFNSQVBVEURVAVDAUTUIPRSVEUPURVDULAABU
    GRSQAUJTUJATUH $.

  $( Equation 3.7 of [PavMeg1999] p. 9.  The variable i in the paper is set to
     3, and this is the third part of the equation.  (Contributed by Roy F.
     Longton, 28-Jun-2005.)  (Revised by Roy F. Longton, 3-Jul-2005.) $)
  lem3.3.7i3e3 $p |- ( a ->3 ( a ^ b ) ) = ( a ->1 b ) $=
    ( nom13 ) ABC $.

  $( Equation 3.7 of [PavMeg1999] p. 9.  The variable i in the paper is set to
     4, and this is the first part of the equation.  (Contributed by Roy F.
     Longton, 28-Jun-2005.)  (Revised by Roy F. Longton, 3-Jul-2005.) $)
  lem3.3.7i4e1 $p |- ( a ->4 ( a ^ b ) ) = ( a ==4 ( a ^ b ) ) $=
    ( wa wn wo wi4 wid4 lear lea ler2an lebi ax-r5 wt wf lor lel2or leo 3tr lan
    ax-r1 leid lecon ortha or0 leor lerr an1 sklem df-i4 df-id4 3tr1 ) AABCZCZA
    DZULCZEZUNULEZULDZCZEZUQURUMEZCZAULFAULGUTULUOEZUSEZUQURULEZCZVBUPVCUSUMULU
    OUMULAULHZULAULABIZULUAZJZKLLVDUQUQMCZVFVDULNEZUSEULUSEZUQVCVLUSUONULUNULUL
    AVHUBZUCOLVLULUSULUDLVMUQULUQUSULUNUEUQURIPUNVMULUNUSULUNUQURUNULQVNJUFULUS
    QPKRVKUQUQUGTMVEUQVEMULULVIUHTSRVEVAUQULUMURULUMVJVGKOSRAULUIAULUJUK $.

  $( Equation 3.7 of [PavMeg1999] p. 9.  The variable i in the paper is set to
     4, and this is the second part of the equation.  (Contributed by Roy F.
     Longton, 28-Jun-2005.)  (Revised by Roy F. Longton, 3-Jul-2005.) $)
  lem3.3.7i4e2 $p |- ( a ==4 ( a ^ b ) ) = ( ( a ^ b ) ==4 a ) $=
    ( wn wa wo wid4 wt lear lea leid ler2an lebi lor lan sklem an1 df2le2 ax-r1
    3tr df-id4 an1r ax-r2 ran 3tr1 ) ACZABDZEZUFCZAUFDZEZDZUHAEZUEUFADZEZDZAUFF
    UFAFUKUGUHUFEZDUGGDZUOUJUPUGUIUFUHUIUFAUFHUFAUFABIZUFJZKLMNUPGUGUFUFUSONUQU
    GGUNDZUOUGPUGUNUTUFUMUEUMUFUFAURQRMUTUNUNUARUBGULUNULGUFAURORUCSSAUFTUFATUD
    $.

  $( Equation 3.7 of [PavMeg1999] p. 9.  The variable i in the paper is set to
     4, and this is the third part of the equation.  (Contributed by Roy F.
     Longton, 28-Jun-2005.)  (Revised by Roy F. Longton, 3-Jul-2005.) $)
  lem3.3.7i4e3 $p |- ( a ->4 ( a ^ b ) ) = ( a ->1 b ) $=
    ( nom14 ) ABC $.

  $( Equation 3.7 of [PavMeg1999] p. 9.  The variable i in the paper is set to
     5, and this is the first part of the equation.  (Contributed by Roy F.
     Longton, 28-Jun-2005.)  (Revised by Roy F. Longton, 3-Jul-2005.) $)
  lem3.3.7i5e1 $p |- ( a ->5 ( a ^ b ) ) = ( a ==5 ( a ^ b ) ) $=
    ( wa wn wo wi5 wid5 wf lear lea leid ler2an lebi lecon ortha 2or or0 df2le2
    ax-r5 ax-r1 3tr df-i5 df-id5 3tr1 ) AABCZCZADZUECZEZUGUEDZCZEZUFUKEZAUEFAUE
    GULUEHEZUKEUEUGEUMUIUNUKUFUEUHHUFUEAUEIZUEAUEABJZUEKLZMUGUEUEAUPNZOPSUNUEUK
    UGUEQUGUJURRZPUEUFUGUKUEUFUQUOMUKUGUSTPUAAUEUBAUEUCUD $.

  $( Equation 3.7 of [PavMeg1999] p. 9.  The variable i in the paper is set to
     5, and this is the second part of the equation.  (Contributed by Roy F.
     Longton, 28-Jun-2005.)  (Revised by Roy F. Longton, 3-Jul-2005.) $)
  lem3.3.7i5e2 $p |- ( a ==5 ( a ^ b ) ) = ( ( a ^ b ) ==5 a ) $=
    ( wa wn wo wid5 ancom 2or ax-r1 df-id5 3tr1 ) AABCZCZADZLDZCZEZLACZONCZEZAL
    FLAFTQRMSPLAGONGHIALJLAJK $.

  $( Equation 3.7 of [PavMeg1999] p. 9.  The variable i in the paper is set to
     5, and this is the third part of the equation.  (Contributed by Roy F.
     Longton, 28-Jun-2005.)  (Revised by Roy F. Longton, 3-Jul-2005.) $)
  lem3.3.7i5e3 $p |- ( a ->5 ( a ^ b ) ) = ( a ->1 b ) $=
    ( nom15 ) ABC $.

$(
  lem3.3.8i0e1 $p |- ( ( a v b ) ->0 b ) = ( ( a v b ) ==0 b ) $= ? $.

  lem3.3.8i0e2 $p |- ( ( a v b ) ==0 b ) = ( b ==0 ( a v b ) ) $= ? $.

  lem3.3.8i0e3 $p |- ( ( a v b ) ->0 b ) = ( a ->2 b ) $=
    wva wvb nom40 $.

  lem3.3.8i1e1 $p |- ( ( a v b ) ->1 b ) = ( ( a v b ) ==1 b ) $= ? $.

  lem3.3.8i1e2 $p |- ( ( a v b ) ==1 b ) = ( b ==1 ( a v b ) ) $= ? $.

  lem3.3.8i1e3 $p |- ( ( a v b ) ->1 b ) = ( a ->2 b ) $=
    wva wvb nom41 $.

  lem3.3.8i2e1 $p |- ( ( a v b ) ->2 b ) = ( ( a v b ) ==2 b ) $= ? $.

  lem3.3.8i2e2 $p |- ( ( a v b ) ==2 b ) = ( b ==2 ( a v b ) ) $= ? $.

  lem3.3.8i2e3 $p |- ( ( a v b ) ->2 b ) = ( a ->2 b ) $=
    wva wvb nom42 $.

  lem3.3.8i3e1 $p |- ( ( a v b ) ->3 b ) = ( ( a v b ) ==3 b ) $= ? $.

  lem3.3.8i3e2 $p |- ( ( a v b ) ==3 b ) = ( b ==3 ( a v b ) ) $= ? $.

  lem3.3.8i3e3 $p |- ( ( a v b ) ->3 b ) = ( a ->2 b ) $= ? $.

  lem3.3.8i4e1 $p |- ( ( a v b ) ->4 b ) = ( ( a v b ) ==4 b ) $= ? $.

  lem3.3.8i4e2 $p |- ( ( a v b ) ==4 b ) = ( b ==4 ( a v b ) ) $= ? $.

  lem3.3.8i4e3 $p |- ( ( a v b ) ->4 b ) = ( a ->2 b ) $= ? $.

  lem3.3.8i5e1 $p |- ( ( a v b ) ->5 b ) = ( ( a v b ) ==5 b ) $= ? $.

  lem3.3.8i5e2 $p |- ( ( a v b ) ==5 b ) = ( b ==5 ( a v b ) ) $= ? $.

  lem3.3.8i5e3 $p |- ( ( a v b ) ->5 b ) = ( a ->2 b ) $= ? $.
$)
  $( [28-Jun-05] $)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Roy's second section
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Equation 3.9 of [PavMeg1999] p. 9.  (Contributed by Roy F. Longton,
     3-Jul-2005.) $)
  lem3.4.1 $p |- ( ( a ->1 b ) ->0 ( a ->2 b ) ) = 1 $=
    ( wi1 wi2 wi0 wn wo wt df-i0 woml6 ax-r2 ) ABCZABDZELFMGHLMIABJK $.
    $( [3-Jul-05] $) $( [28-Jun-05] $)

  $( lem3.4.2 is 2vwomr1a and 2vwomr2a $)

  ${
    lem3.4.3.1 $e |- ( a ->2 b ) = 1 $.
    $( Equation 3.11 of [PavMeg1999] p. 9.  (Contributed by Roy F. Longton,
       29-Jun-2005.)  (Revised by Roy F. Longton, 3-Jul-2005.) $)
    lem3.4.3 $p |- ( a ->2 ( a ==5 b ) ) = 1 $=
      ( wid5 wi1 wt 2vwomr2a ax-r1 wn wa wo anidm ran lea lel leran ler2an bltr
      ler df-i1 df-id5 lan lbtr lelor le3tr1 lem3.3.5lem 2vwomr1a ) AABDZAUHEZF
      ABEZUIUJFABCGHAIZABJZKUKAUHJZKUJUIULUMUKULAULUKBIJZKZJZUMULAAJZBJZUPAUQBU
      QAALHMURAUOUQABAANZOURULUNUQABUSPSQRUOUHAUHUOABUAHUBUCUDABTAUHTUERUFUG $.
  $}

  ${
    lem3.4.4.1 $e |- ( a ->2 b ) = 1 $.
    lem3.4.4.2 $e |- ( b ->2 a ) = 1 $.
    $( Equation 3.12 of [PavMeg1999] p. 9.  (Contributed by Roy F. Longton,
       29-Jun-2005.)  (Revised by Roy F. Longton, 3-Jul-2005.) $)
    lem3.4.4 $p |- ( a ==5 b ) = 1 $=
      ( wid5 wi2 wt lem3.3.4 ax-r1 lem3.4.3 ax-r2 ) ABEZALFZGMLABDHIABCJK $.
  $}

  ${
    lem3.4.5.1 $e |- ( a ==5 b ) = 1 $.
    $( Equation 3.13 of [PavMeg1999] p. 9.  (Contributed by Roy F. Longton,
       29-Jun-2005.)  (Revised by Roy F. Longton, 3-Jul-2005.) $)
    lem3.4.5 $p |- ( a ->2 ( b v c ) ) = 1 $=
      ( wo lem3.3.5 2vwomr1a ) ABCEABCDFG $.
  $}

  ${
    lem3.4.6.1 $e |- ( a ==5 b ) = 1 $.
    $( Equation 3.14 of [PavMeg1999] p. 9.  (Contributed by Roy F. Longton,
       29-Jun-2005.)  (Revised by Roy F. Longton, 3-Jul-2005.) $)
    lem3.4.6 $p |- ( ( a v c ) ==5 ( b v c ) ) = 1 $=
      ( wo wi2 wt lem3.3.6 ax-r1 lem3.4.5 ax-r2 wid5 wa wn df-id5 ancom 2or 3tr
      lem3.4.4 ) ACEZBCEZTUAFZAUAFZGUCUBABCHIABCDJKUATFZBTFZGUEUDBACHIBACBALBAM
      ZBNZANZMZEZGBAOUJABMZUHUGMZEZABLZGUFUKUIULBAPUGUHPQUNUMABOIDRKJKS $.
  $}

$(
  @( Lemma intended for ~ thm3.8i1 . @)
  thm3.8i1lem @p |- ( a ==1 b ) = ( ( b ->0 a ) ^ ( a ->1 b ) ) @=
    wva wvb wn wo wva wn wva wvb wa wo wa wvb wn wva wo wva wn wva wvb wa wo wa
    wva wvb wid1 wvb wva wi0 wva wvb wi1 wa wva wvb wn wo wvb wn wva wo wva wn
    wva wvb wa wo wva wvb wn ax-a2 ran wva wvb df-id1 wvb wva wi0 wvb wn wva wo
    wva wvb wi1 wva wn wva wvb wa wo wvb wva df-i0 wva wvb df-i1 2an 3tr1 @.
    @( [31-Mar-2011] @) @( [30-Jun-05] @)

@{
  thm3.8i1.1 @e |- ( a ==1 b ) = 1 @.
  thm3.8i1 @p |- ( ( a v c ) ==1 ( b v c ) ) = 1 @= ? @.
@}

@{
  thm3.8i2.1 @e |- ( a ==2 b ) = 1 @.
  thm3.8i2 @p |- ( ( a v c ) ==2 ( b v c ) ) = 1 @= ? @.
@}

@{
  thm3.8i3.1 @e |- ( a ==3 b ) = 1 @.
  thm3.8i3 @p |- ( ( a v c ) ==3 ( b v c ) ) = 1 @= ? @.
@}

@{
  thm3.8i4.1 @e |- ( a ==4 b ) = 1 @.
  thm3.8i4 @p |- ( ( a v c ) ==4 ( b v c ) ) = 1 @= ? @.
@}

@{
  thm3.8i5.1 @e |- ( a ==5 b ) = 1 @.
  thm3.8i5 @p |- ( ( a v c ) ==5 ( b v c ) ) = 1 @=
    wva wvb wvc thm3.8i5.1 lem3.4.6 @.
    @( [31-Mar-2011] @) @( [29-Jun-05] @)
@}
  $)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Roy's third section
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( lem4.6.1 is u1lemaa $)

  $( Equation 4.10 of [MegPav2000] p. 23.  This is the first part of the
     equation.  (Contributed by Roy F. Longton, 29-Jun-2005.)  (Revised by Roy
     F. Longton, 3-Jul-2005.) $)
  lem4.6.2e1 $p |- ( ( a ->1 b ) ^ ( a ' ->1 b ) ) = ( ( a ->1 b ) ^ b ) $=
    ( wi1 wn wa wo df-i1 2an ax-a1 ax-r1 ax-r5 lan comcom fh1 lor coman1 coman2
    ancom ran 3tr comorr comcom6 leao1 lecom comcom7 com2an anass anidm comcom2
    omla orabs fh3 ax-a2 lear df-le2 ) ABCZADZBCZEUQABEZFZUQDZUQBEZFZEZUTBEZUPB
    EUPUTURVCABGZUQBGHVDUTAVBFZEUTAEZUTVBEZFZVEVCVGUTVAAVBAVAAIJKLUTAVBAUTAUTUQ
    USUAUBMVBUTVBUTUQBUSUCUDMNVJAUTEZVIFUSVIFZVEVHVKVIUTARKVKUSVIABUJKVLUSVBUTE
    ZFUSVBUQEZVBUSEZFZFZVEVIVMUSUTVBROVMVPUSVBUQUSUQBPZVBABVBAVRUEUQBQUFNOVQUSB
    UQEZUQEZVOFZFUSBUQUQEZEZVOFZFZVEVPWAUSVNVTVOVBVSUQUQBRSKOWAWDUSVTWCVOBUQUQU
    GKOWEUSVSVOFZFUSVBVOFZFZVEWDWFUSWCVSVOWBUQBUQUHLKOWFWGUSVSVBVOBUQRKOWHUSVBF
    USUQFZUSBFZEVEWGVBUSVBUSUKOUSUQBUSAABPUIABQULWIUTWJBUSUQUMUSBABUNUOHTTTTTTU
    TUPBUPUTVFJST $.

  $( Equation 4.10 of [MegPav2000] p. 23.  This is the second part of the
     equation.  (Contributed by Roy F. Longton, 1-Jul-2005.) $)
  lem4.6.2e2 $p |- ( ( a ->1 b ) ^ b ) = ( ( a ^ b ) v ( a ' ^ b ) ) $=
    ( u1lemab ) ABC $.

  $( Equation 4.11 of [MegPav2000] p. 23.  This is the first part of the
     equation.  (Contributed by Roy F. Longton, 1-Jul-2005.) $)
  lem4.6.3le1 $p |- ( a ' ->1 b ) ' =< a ' $=
    ( u1lem9a ) ABC $.

  $( Equation 4.11 of [MegPav2000] p. 23.  This is the second part of the
     equation.  (Contributed by Roy F. Longton, 1-Jul-2005.) $)
  lem4.6.3le2 $p |- a ' =< ( a ->1 b ) $=
    ( u1lem9b ) ABC $.

  $( Equation 4.12 of [MegPav2000] p. 23.  (Contributed by Roy F. Longton,
     1-Jul-2005.) $)
  lem4.6.4 $p |- ( ( a ->1 b ) ->1 b ) = ( a ' ->1 b ) $=
    ( u1lem12 ) ABC $.

  $( Equation 4.13 of [MegPav2000] p. 23.  (Contributed by Roy F. Longton,
     1-Jul-2005.) $)
  lem4.6.5 $p |- ( ( a ->1 b ) ' ->1 b ) = ( a ->1 b ) $=
    ( wi1 wn u1lemn1b ax-r1 ) ABCZGDBCABEF $.

  $( Equation 4.14 of [MegPav2000] p. 23.  The variable i in the paper is set
     to 0, and j is set to 1.  (Contributed by Roy F. Longton, 1-Jul-2005.) $)
  lem4.6.6i0j1 $p |- ( ( a ->0 b ) v ( a ->1 b ) ) = ( a ->0 b ) $=
    ( wn wo wa wi0 wi1 leid lear lelor lel2or leo lebi df-i0 df-i1 2or 3tr1 ) A
    CZBDZRABEZDZDZSABFZABGZDUCUBSSSUASHTBRABIJKSUALMUCSUDUAABNZABOPUEQ $.

  $( Equation 4.14 of [MegPav2000] p. 23.  The variable i in the paper is set
     to 0, and j is set to 2.  (Contributed by Roy F. Longton, 1-Jul-2005.) $)
  lem4.6.6i0j2 $p |- ( ( a ->0 b ) v ( a ->2 b ) ) = ( a ->0 b ) $=
    ( wn wo wa wi0 wi2 leid leor leao1 lel2or leo lebi df-i0 df-i2 2or 3tr1 ) A
    CZBDZBRBCZEZDZDZSABFZABGZDUDUCSSSUBSHBSUABRIRTBJKKSUBLMUDSUEUBABNZABOPUFQ
    $.

  $( Equation 4.14 of [MegPav2000] p. 23.  The variable i in the paper is set
     to 0, and j is set to 3.  (Contributed by Roy F. Longton, 1-Jul-2005.) $)
  lem4.6.6i0j3 $p |- ( ( a ->0 b ) v ( a ->3 b ) ) = ( a ->0 b ) $=
    ( wn wo wa wi0 wi3 leid leao1 lel2or lear leo lebi df-i0 df-i3 2or 3tr1 ) A
    CZBDZRBEZRBCZEZDZASEZDZDZSABFZABGZDUGUFSSSUESHUCSUDTSUBRBBIRUABIJASKJJSUELM
    UGSUHUEABNZABOPUIQ $.

  $( Equation 4.14 of [MegPav2000] p. 23.  The variable i in the paper is set
     to 0, and j is set to 4.  (Contributed by Roy F. Longton, 1-Jul-2005.) $)
  lem4.6.6i0j4 $p |- ( ( a ->0 b ) v ( a ->4 b ) ) = ( a ->0 b ) $=
    ( wn wo wi0 wi4 leid leao4 leao1 lel2or lea leo lebi df-i0 df-i4 2or 3tr1
    wa ) ACZBDZABRZSBRZDZTBCZRZDZDZTABEZABFZDUHUGTTTUFTGUCTUEUATUBBASHSBBIJTUDK
    JJTUFLMUHTUIUFABNZABOPUJQ $.

  $( Equation 4.14 of [MegPav2000] p. 23.  The variable i in the paper is set
     to 1, and j is set to 0.  (Contributed by Roy F. Longton, 1-Jul-2005.) $)
  lem4.6.6i1j0 $p |- ( ( a ->1 b ) v ( a ->0 b ) ) = ( a ->0 b ) $=
    ( wn wa wo wi1 wi0 lear lelor df-le2 df-i1 df-i0 2or 3tr1 ) ACZABDZEZOBEZER
    ABFZABGZETQRPBOABHIJSQTRABKABLZMUAN $.

  $( Equation 4.14 of [MegPav2000] p. 23.  The variable i in the paper is set
     to 1, and j is set to 2.  (Contributed by Roy F. Longton, 1-Jul-2005.) $)
  lem4.6.6i1j2 $p |- ( ( a ->1 b ) v ( a ->2 b ) ) = ( a ->0 b ) $=
    ( u12lem ) ABC $.

  $( Equation 4.14 of [MegPav2000] p. 23.  The variable i in the paper is set
     to 1, and j is set to 3.  (Contributed by Roy F. Longton, 1-Jul-2005.) $)
  lem4.6.6i1j3 $p |- ( ( a ->1 b ) v ( a ->3 b ) ) = ( a ->0 b ) $=
    ( wn wa wo wi1 wi3 ler lecom lea lel2or ax-a3 ax-a2 ran ax-r1 wt lor df-le2
    ax-r5 3tr wi0 leo comcom6 comcom lear lelor ax-a4 df-le1 lem3.3.5lem orordi
    fh3 an1r ax-r2 3tr2 df-i1 df-i3 2or df-i0 3tr1 ) ACZABDZEZUTBDZUTBCZDZEZAUT
    BEZDZEZEZVGABFZABGZEABUAVBVFEZVHEVMAEZVMVGEZDZVJVGVMAVGAVMAVMUTVMUTVBVFUTVA
    UBHIUCUDVMVGVBVGVFVABUTABUEZUFVFUTBVCUTVEUTBJUTVDJKHZKIUKVBVFVHLVPAVMEZVODA
    VBEZVFEZVODZVGVNVSVOVMAMNVSWAVOWAVSAVBVFLONWBAUTEZVAEZVFEZVODPVODZVGWAWEVOV
    TWDVFWDVTAUTVALOSNWEPVOWEPWDVFPWCVAPWCPAUGUHHHUINWFVOVFVBEZVGEZVGVOULVMWGVG
    VBVFMSWHVFVBVGEZEZVGVFVBVGLWJVFUTVABEZEZEVFVGEVGWIWLVFWLWIUTVABUJOQWLVGVFWK
    BUTVABVQRQQVFVGVRRTUMTTTUNVKVBVLVIABUOABUPUQABURUS $.

  $( Equation 4.14 of [MegPav2000] p. 23.  The variable i in the paper is set
     to 2, and j is set to 0.  (Contributed by Roy F. Longton, 1-Jul-2005.) $)
  lem4.6.6i2j0 $p |- ( ( a ->2 b ) v ( a ->0 b ) ) = ( a ->0 b ) $=
    ( wn wa wo wi2 wi0 leor leao1 lel2or df-le2 df-i2 df-i0 2or 3tr1 ) BACZBCZD
    ZEZPBEZETABFZABGZEUBSTBTRBPHPQBIJKUASUBTABLABMZNUCO $.

  $( Equation 4.14 of [MegPav2000] p. 23.  The variable i in the paper is set
     to 2, and j is set to 1.  (Contributed by Roy F. Longton, 1-Jul-2005.) $)
  lem4.6.6i2j1 $p |- ( ( a ->2 b ) v ( a ->1 b ) ) = ( a ->0 b ) $=
    ( wn wa wo wi2 wi1 wi0 leor leao1 lel2or lear lelor leo lerr ler lebi df-i2
    df-i1 2or df-i0 3tr1 ) BACZBCZDZEZUCABDZEZEZUCBEZABFZABGZEABHUIUJUFUJUHBUJU
    EBUCIUCUDBJKUGBUCABLMKUCUIBUCUHUFUCUGNOBUFUHBUENPKQUKUFULUHABRABSTABUAUB $.

  $( Equation 4.14 of [MegPav2000] p. 23.  The variable i in the paper is set
     to 2, and j is set to 4.  (Contributed by Roy F. Longton, 1-Jul-2005.) $)
  lem4.6.6i2j4 $p |- ( ( a ->2 b ) v ( a ->4 b ) ) = ( a ->0 b ) $=
    ( wn wa wo wi2 wi4 wi0 ax-a2 ax-r5 ax-a3 ax-r1 lor ancom lan oml 3tr lel2or
    ax-r2 leao1 leao4 leid leor lerr lebi df-i2 df-i4 2or df-i0 3tr1 ) BACZBCZD
    ZEZABDZUKBDZEZUKBEZULDZEZEZURABFZABGZEABHVAUMBEZUTEUMBUTEZEZURUNVDUTBUMIJUM
    BUTKVFUMBUQEZUSEZEUMUQBEZUSEZEZURVEVHUMVHVEBUQUSKLMVHVJUMVGVIUSBUQIJMVKUMUQ
    BUSEZEZEUMUQUREZEZURVJVMUMUQBUSKMVMVNUMVLURUQVLBULURDZEBULBUKEZDZEZURUSVPBU
    RULNMVPVRBURVQULUKBIOMVSVQURBUKPBUKISQMMVOURUMURVNUKULBTUQURURUOURUPBAUKUAU
    KBBTRURUBRRURVNUMURUQUCUDUEQQQVBUNVCUTABUFABUGUHABUIUJ $.

  $( Equation 4.14 of [MegPav2000] p. 23.  The variable i in the paper is set
     to 3, and j is set to 0.  (Contributed by Roy F. Longton, 1-Jul-2005.) $)
  lem4.6.6i3j0 $p |- ( ( a ->3 b ) v ( a ->0 b ) ) = ( a ->0 b ) $=
    ( wn wa wi3 wi0 ax-a3 ax-r1 lor ax-a2 omln ax-r2 ax-r5 leid leor lel2or leo
    wo leao1 3tr lebi df-le2 df-i3 df-i0 2or 3tr1 ) ACZBDZUGBCZDZRZAUGBRZDZRZUL
    RZULABEZABFZRUQUOUKUMULRZRUKUMUGRZBRZRZULUKUMULGURUTUKUTURUMUGBGHIVAUKULBRZ
    RUKULRULUTVBUKUSULBUSUGUMRULUMUGJABKLMIVBULUKVBULULULBULNBUGOPULBQUAIUKULUH
    ULUJUGBBSUGUIBSPUBTTUPUNUQULABUCABUDZUEVCUF $.

  $( Equation 4.14 of [MegPav2000] p. 23.  The variable i in the paper is set
     to 3, and j is set to 1.  (Contributed by Roy F. Longton, 1-Jul-2005.) $)
  lem4.6.6i3j1 $p |- ( ( a ->3 b ) v ( a ->1 b ) ) = ( a ->0 b ) $=
    ( wn wa wo wi3 wi1 wi0 ax-a3 ax-r1 ax-a2 omln ax-r2 ax-r5 leao1 lel2or leid
    lor leao4 leo lerr lebi 3tr df-i3 df-i1 2or df-i0 3tr1 ) ACZBDZUIBCZDZEZAUI
    BEZDZEZUIABDZEZEZUNABFZABGZEABHUSUMUOUREZEUMUOUIEZUQEZEZUNUMUOURIVBVDUMVDVB
    UOUIUQIJRVEUMUNUQEZEZUNVDVFUMVCUNUQVCUIUOEUNUOUIKABLMNRVGUNUMUNVFUJUNULUIBB
    OUIUKBOPUNUNUQUNQBAUISPPUNVFUMUNUQTUAUBMUCUTUPVAURABUDABUEUFABUGUH $.

  $( Equation 4.14 of [MegPav2000] p. 23.  The variable i in the paper is set
     to 4, and j is set to 0.  (Contributed by Roy F. Longton, 2-Jul-2005.) $)
  lem4.6.6i4j0 $p |- ( ( a ->4 b ) v ( a ->0 b ) ) = ( a ->0 b ) $=
    ( wa wn wo wi4 wi0 leao4 leao1 lel2or lea df-le2 df-i4 df-i0 2or 3tr1 ) ABC
    ZADZBCZEZRBEZBDZCZEZUAEUAABFZABGZEUFUDUATUAUCQUASBARHRBBIJUAUBKJLUEUDUFUAAB
    MABNZOUGP $.

  $( Equation 4.14 of [MegPav2000] p. 23.  The variable i in the paper is set
     to 4, and j is set to 2.  (Contributed by Roy F. Longton, 2-Jul-2005.) $)
  lem4.6.6i4j2 $p |- ( ( a ->4 b ) v ( a ->2 b ) ) = ( a ->0 b ) $=
    ( wa wn wi4 wi2 wi0 ax-a3 ax-r1 ax-a2 ancom lor leor oml2 ax-r5 ax-r2 leao1
    wo 3tr lel2or leao4 leid leo lerr lebi df-i4 df-i2 2or df-i0 3tr1 ) ABCZADZ
    BCZRZULBRZBDZCZRZBULUPCZRZRZUOABEZABFZRABGVAUNUQUTRZRUNUOUSRZRZUOUNUQUTHVDV
    EUNVDUQBRZUSRZVEVHVDUQBUSHIVGUOUSVGBUQRBUPUOCZRUOUQBJUQVIBUOUPKLBUOBULMNSOP
    LVFUOUNUOVEUKUOUMBAULUAULBBQTUOUOUSUOUBULUPBQTTUOVEUNUOUSUCUDUESVBURVCUTABU
    FABUGUHABUIUJ $.

  ${
    com3iia.1 $e |- a C b $.
    $( The dual of ~ com3ii .  (Contributed by Roy F. Longton, 2-Jul-2005.) $)
    com3iia $p |- ( a v ( a ' ^ b ) ) = ( a v b ) $=
      ( wn wa wo comid comcom2 fh3 lear ax-a4 df-le1 leid ler2an lebi ax-r2 ) A
      ADZBEFAQFZABFZEZSAQBAAAGHCITSRSJSRSSRSAKLSMNOP $.
  $}

$(
  @( Note: This theorem is unfinished. This is the progress that I was able
      to make. @)
  lem4.6.6i4j3 @p |- ( ( a ->4 b ) v ( a ->3 b ) ) = ( a ->0 b ) @=
    wva wvb wa wva wn wvb wa wo wva wn wvb wo wvb wn wa wo wva wn wvb wa wva wn
    wvb wn wa wo wva wva wn wvb wo wa wo wo wva wn wvb wo wva wvb wi4 wva wvb
    wi3 wo wva wvb wi0 wva wvb wa wva wn wvb wa wo wva wn wvb wo wvb wn wa wo
    wva wn wvb wa wva wn wvb wn wa wo wva wva wn wvb wo wa wo wo wva wvb wa wva
    wn wvb wo wva wn wvb wa wvb wn wo wa wo wva wn wvb wn wa wva wn wvb wa wva
    wo wva wn wvb wo wa wo wo wva wn wvb wo wva wvb wa wva wn wvb wa wo wva wn
    wvb wo wvb wn wa wo wva wvb wa wva wn wvb wo wva wn wvb wa wvb wn wo wa wo
    wva wn wvb wa wva wn wvb wn wa wo wva wva wn wvb wo wa wo wva wn wvb wn wa
    wva wn wvb wa wva wo wva wn wvb wo wa wo wva wvb wa wva wn wvb wa wo wva wn
    wvb wo wvb wn wa wo wva wvb wa wva wn wvb wa wva wn wvb wo wvb wn wa wo wo
    wva wvb wa wva wn wvb wa wva wn wvb wo wo wva wn wvb wa wvb wn wo wa wo wva
    wvb wa wva wn wvb wo wva wn wvb wa wvb wn wo wa wo wva wvb wa wva wn wvb wa
    wva wn wvb wo wvb wn wa ax-a3 wva wn wvb wa wva wn wvb wo wvb wn wa wo wva
    wn wvb wa wva wn wvb wo wo wva wn wvb wa wvb wn wo wa wva wvb wa wva wn wvb
    wa wva wn wvb wo wvb wn wva wn wvb wa wva wn wvb wo wva wn wvb wvb leao1
    lecom wva wn wvb wa wvb wva wn wvb coman2 comcom2 fh3 lor wva wn wvb wa wva
    wn wvb wo wo wva wn wvb wa wvb wn wo wa wva wn wvb wo wva wn wvb wa wvb wn
    wo wa wva wvb wa wva wn wvb wa wva wn wvb wo wo wva wn wvb wo wva wn wvb wa
    wvb wn wo wva wn wvb wa wva wn wvb wo wva wn wvb wvb leao1 df-le2 ran lor
    3tr wva wn wvb wa wva wn wvb wn wa wo wva wva wn wvb wo wa wo wva wn wvb wn
    wa wva wn wvb wa wo wva wva wn wvb wo wa wo wva wn wvb wn wa wva wn wvb wa
    wva wva wn wvb wo wa wo wo wva wn wvb wn wa wva wn wvb wa wva wo wva wn wvb
    wo wa wo wva wn wvb wa wva wn wvb wn wa wo wva wn wvb wn wa wva wn wvb wa
    wo wva wva wn wvb wo wa wva wn wvb wa wva wn wvb wn wa ax-a2 ax-r5 wva wn
    wvb wn wa wva wn wvb wa wva wva wn wvb wo wa ax-a3 wva wn wvb wa wva wva wn
    wvb wo wa wo wva wn wvb wa wva wo wva wn wvb wo wa wva wn wvb wn wa wva wn
    wvb wa wva wva wn wvb wo wa wo wva wn wvb wa wva wo wva wn wvb wa wva wn
    wvb wo wo wa wva wn wvb wa wva wo wva wn wvb wo wa wva wn wvb wa wva wva wn
    wvb wo wva wva wn wvb wa wva wva wn wvb wa wva wn wvb comanr1 comcom6
    comcom wva wn wvb wa wva wn wvb wo wva wn wvb wvb leao1 lecom fh3 wva wn
    wvb wa wva wn wvb wo wo wva wn wvb wo wva wn wvb wa wva wo wva wn wvb wa
    wva wn wvb wo wva wn wvb wvb leao1 df-le2 lan ax-r2 lor 3tr 2or wva wvb wa
    wva wn wvb wo wva wn wvb wa wvb wn wo wa wo wva wn wvb wn wa wva wn wvb wa
    wva wo wva wn wvb wo wa wo wo wva wvb wa wva wn wvb wo wva wn wvb wa wvb wn
    wo wa wo wva wn wvb wo wva wn wvb wa wva wo wa wva wn wvb wn wa wo wo wva
    wn wvb wo wva wn wvb wn wa wva wn wvb wa wva wo wva wn wvb wo wa wo wva wn
    wvb wo wva wn wvb wa wva wo wa wva wn wvb wn wa wo wva wvb wa wva wn wvb wo
    wva wn wvb wa wvb wn wo wa wo wva wn wvb wn wa wva wn wvb wa wva wo wva wn
    wvb wo wa wo wva wn wvb wn wa wva wn wvb wo wva wn wvb wa wva wo wa wo wva
    wn wvb wo wva wn wvb wa wva wo wa wva wn wvb wn wa wo wva wn wvb wa wva wo
    wva wn wvb wo wa wva wn wvb wo wva wn wvb wa wva wo wa wva wn wvb wn wa wva
    wn wvb wa wva wo wva wn wvb wo ancom lor wva wn wvb wn wa wva wn wvb wo wva
    wn wvb wa wva wo wa ax-a2 ax-r2 lor wva wvb wa wva wn wvb wo wva wn wvb wa
    wvb wn wo wa wo wva wn wvb wo wva wn wvb wa wva wo wa wva wn wvb wn wa wo
    wo wva wvb wa wva wn wvb wo wva wn wvb wa wvb wn wo wa wva wn wvb wo wva wn
    wvb wa wva wo wa wva wn wvb wn wa wo wo wo wva wn wvb wo wva wvb wa wva wn
    wvb wo wva wn wvb wa wvb wn wo wa wva wn wvb wo wva wn wvb wa wva wo wa wva
    wn wvb wn wa wo ax-a3 wva wvb wa wva wn wvb wo wva wn wvb wa wvb wn wo wa
    wva wn wvb wo wva wn wvb wa wva wo wa wva wn wvb wn wa wo wo wo wva wvb wa
    wva wn wvb wo wva wn wvb wa wvb wn wo wva wn wvb wa wva wo wo wa wva wn wvb
    wn wa wo wo wva wn wvb wo wva wn wvb wo wva wn wvb wa wvb wn wo wa wva wn
    wvb wo wva wn wvb wa wva wo wa wva wn wvb wn wa wo wo wva wn wvb wo wva wn
    wvb wa wvb wn wo wva wn wvb wa wva wo wo wa wva wn wvb wn wa wo wva wvb wa
    wva wn wvb wo wva wn wvb wa wvb wn wo wa wva wn wvb wo wva wn wvb wa wva wo
    wa wva wn wvb wn wa wo wo wva wn wvb wo wva wn wvb wa wvb wn wo wa wva wn
    wvb wo wva wn wvb wa wva wo wa wo wva wn wvb wn wa wo wva wn wvb wo wva wn
    wvb wa wvb wn wo wva wn wvb wa wva wo wo wa wva wn wvb wn wa wo wva wn wvb
    wo wva wn wvb wa wvb wn wo wa wva wn wvb wo wva wn wvb wa wva wo wa wo wva
    wn wvb wn wa wo wva wn wvb wo wva wn wvb wa wvb wn wo wa wva wn wvb wo wva
    wn wvb wa wva wo wa wva wn wvb wn wa wo wo wva wn wvb wo wva wn wvb wa wvb
    wn wo wa wva wn wvb wo wva wn wvb wa wva wo wa wva wn wvb wn wa ax-a3 ax-r1
    wva wn wvb wo wva wn wvb wa wvb wn wo wa wva wn wvb wo wva wn wvb wa wva wo
    wa wo wva wn wvb wo wva wn wvb wa wvb wn wo wva wn wvb wa wva wo wo wa wva
    wn wvb wn wa wva wn wvb wo wva wn wvb wa wvb wn wo wva wn wvb wa wva wo wo
    wa wva wn wvb wo wva wn wvb wa wvb wn wo wa wva wn wvb wo wva wn wvb wa wva
    wo wa wo wva wn wvb wo wva wn wvb wa wvb wn wo wva wn wvb wa wva wo wva wn
    wvb wo wva wn wvb wa wvb wn wva wn wvb wa wva wn wvb wo wva wn wvb wa wva
    wn wvb wo wva wn wvb wvb leao1 lecom comcom wva wn wvb wo wvb wva wn wvb
    comor2 comcom2 com2or wva wn wvb wo wva wn wvb wa wva wva wn wvb wa wva wn
    wvb wo wva wn wvb wa wva wn wvb wo wva wn wvb wvb leao1 lecom comcom wva wn
    wvb wo wva wva wn wvb comor1 comcom7 com2or fh1 ax-r1 ax-r5 ax-r2 lor wva
    wvb wa wva wn wvb wo wva wn wvb wa wvb wn wo wva wn wvb wa wva wo wo wa wva
    wn wvb wn wa wo wo wva wvb wa wva wn wvb wn wa wva wn wvb wo wva wn wvb wa
    wvb wn wo wva wn wvb wa wva wo wo wa wo wo wva wn wvb wo wva wn wvb wo wva
    wn wvb wa wvb wn wo wva wn wvb wa wva wo wo wa wva wn wvb wn wa wo wva wn
    wvb wn wa wva wn wvb wo wva wn wvb wa wvb wn wo wva wn wvb wa wva wo wo wa
    wo wva wvb wa wva wn wvb wo wva wn wvb wa wvb wn wo wva wn wvb wa wva wo wo
    wa wva wn wvb wn wa ax-a2 lor wva wvb wa wva wn wvb wn wa wva wn wvb wo wva
    wn wvb wa wvb wn wo wva wn wvb wa wva wo wo wa wo wo wva wvb wa wva wn wvb
    wn wa wo wva wn wvb wo wva wn wvb wa wvb wn wo wva wn wvb wa wva wo wo wa
    wo wva wn wvb wo wva wvb wa wva wn wvb wn wa wo wva wn wvb wo wva wn wvb wa
    wvb wn wo wva wn wvb wa wva wo wo wa wo wva wvb wa wva wn wvb wn wa wva wn
    wvb wo wva wn wvb wa wvb wn wo wva wn wvb wa wva wo wo wa wo wo wva wvb wa
    wva wn wvb wn wa wva wn wvb wo wva wn wvb wa wvb wn wo wva wn wvb wa wva wo
    wo wa ax-a3 ax-r1 wva wvb wa wva wn wvb wn wa wo wva wn wvb wo wva wn wvb
    wa wvb wn wo wva wn wvb wa wva wo wo wa wo wva wvb wa wva wn wvb wn wa wo
    wva wn wvb wo wva wn wvb wa wvb wn wva wo wo wa wo wva wn wvb wo wva wn wvb
    wo wva wn wvb wa wvb wn wo wva wn wvb wa wva wo wo wa wva wn wvb wo wva wn
    wvb wa wvb wn wva wo wo wa wva wvb wa wva wn wvb wn wa wo wva wn wvb wa wvb
    wn wo wva wn wvb wa wva wo wo wva wn wvb wa wvb wn wva wo wo wva wn wvb wo
    wva wn wvb wa wvb wn wva wo wo wva wn wvb wa wvb wn wo wva wn wvb wa wva wo
    wo wva wn wvb wa wvb wn wva orordi ax-r1 lan lor wva wvb wa wva wn wvb wn
    wa wo wva wn wvb wo wva wn wvb wa wvb wn wva wo wo wa wo wva wvb wa wva wn
    wvb wn wa wo wva wn wvb wo wva wn wvb wa wva wvb wn wo wo wa wo wva wn wvb
    wo wva wn wvb wo wva wn wvb wa wvb wn wva wo wo wa wva wn wvb wo wva wn wvb
    wa wva wvb wn wo wo wa wva wvb wa wva wn wvb wn wa wo wva wn wvb wa wvb wn
    wva wo wo wva wn wvb wa wva wvb wn wo wo wva wn wvb wo wvb wn wva wo wva
    wvb wn wo wva wn wvb wa wvb wn wva ax-a2 lor lan lor ? ax-r2 ax-r2 ax-r2
    ax-r2 ax-r2 ax-r2 ax-r2 ax-r2 wva wvb wi4 wva wvb wa wva wn wvb wa wo wva
    wn wvb wo wvb wn wa wo wva wvb wi3 wva wn wvb wa wva wn wvb wn wa wo wva
    wva wn wvb wo wa wo wva wvb df-i4 wva wvb df-i3 2or wva wvb df-i0 3tr1 @.
    @( [31-Mar-2011] @) @( [2-Jul-05] @)

  lem4.6.6i1j4 @p |- ( ( a ->1 b ) v ( a ->4 b ) ) = ( a ->0 b ) @= ? @.

  lem4.6.6i2j3 @p |- ( ( a ->2 b ) v ( a ->3 b ) ) = ( a ->0 b ) @= ? @.

  lem4.6.6i3j2 @p |- ( ( a ->3 b ) v ( a ->2 b ) ) = ( a ->0 b ) @= ? @.

  lem4.6.6i3j4 @p |- ( ( a ->3 b ) v ( a ->4 b ) ) = ( a ->0 b ) @= ? @.

  lem4.6.6i4j1 @p |- ( ( a ->4 b ) v ( a ->1 b ) ) = ( a ->0 b ) @= ? @.
$)

  ${
    lem4.6.7.1 $e |- a ' =< b $.
    $( Equation 4.15 of [MegPav2000] p. 23.  (Contributed by Roy F. Longton,
       3-Jul-2005.) $)
    lem4.6.7 $p |- b =< ( a ->1 b ) $=
      ( wn wa wo wi1 wt leid sklem ax-r1 df-le2 ax-a3 ler2an lel2or leran leao2
      2an le1 ler lebi ax-r2 comid comcom3 lecom fh3 3tr1 df-le1 df-i1 lbtr ) B
      ADZABEZFZABGZBUMHBEZUKAFZUKBFZEBUMFZUMHUPBUQUPHAAAIJKUQBUKBCLKRURBUKFZULF
      ZUOUTURBUKULMKUTUOUSUOULBUOUKBHBBSBINUKHBUKSCNOAHBASPOUOUSULBHUKQTUAUBUKA
      BAAAUCUDUKBCUEUFUGUHUNUMABUIKUJ $.
  $}

$( $t

/* The '$t' token indicates the beginning of the typesetting definition
section, embedded in a Metamath comment.  There may only be one per
source file, and the typesetting section ends with the end of the
Metamath comment.  The typesetting section uses C-style comment
delimiters.  */

/* These are the LaTeX and HTML definitions in the order the tokens are
introduced in $c or $v statements.  See HELP TEX or HELP HTML in the
Metamath program. */

/* Definitions for LaTeX output of various Metamath commands */
/* (LaTeX definitions have not been written for this file.) */

/* Definitions for HTML output of various Metamath commands. */

/* Title */
htmltitle "Quantum Logic Explorer";

/* Home page link */
htmlhome '<A HREF="mmql.html"><FONT SIZE=-2 FACE=sans-serif>' +
    '<IMG SRC="l46-7icon.gif" BORDER=0 ALT=' +
    '"[Lattice L46-7]Home Page" HEIGHT=32 WIDTH=32 ALIGN=MIDDLE>' +
    'Home</FONT></A>';

/* Optional file where bibliographic references are kept */
htmlbibliography "mmql.html";

/* Variable color key */
htmlvarcolor '<FONT COLOR="#CC4400">term</FONT>';

/* GIF and Symbol Font HTML directories */
htmldir "../qlegif/";
althtmldir "../qleuni/";

/* Symbol definitions */
htmldef "a" as "<IMG SRC='_ba.gif' WIDTH=9 HEIGHT=19 ALT='a' ALIGN=TOP>";
htmldef "b" as "<IMG SRC='_bb.gif' WIDTH=8 HEIGHT=19 ALT='b' ALIGN=TOP>";
htmldef "c" as "<IMG SRC='_bc.gif' WIDTH=7 HEIGHT=19 ALT='c' ALIGN=TOP>";
htmldef "d" as "<IMG SRC='_bd.gif' WIDTH=9 HEIGHT=19 ALT='d' ALIGN=TOP>";
htmldef "e" as "<IMG SRC='_be.gif' WIDTH=8 HEIGHT=19 ALT='e' ALIGN=TOP>";
htmldef "f" as "<IMG SRC='_bf.gif' WIDTH=9 HEIGHT=19 ALT='f' ALIGN=TOP>";
htmldef "g" as "<IMG SRC='_bg.gif' WIDTH=9 HEIGHT=19 ALT='g' ALIGN=TOP>";
htmldef "h" as "<IMG SRC='_bh.gif' WIDTH=10 HEIGHT=19 ALT='h' ALIGN=TOP>";
htmldef "i" as "<IMG SRC='_browni.gif' WIDTH=6 HEIGHT=19 ALT='i' ALIGN=TOP>";
htmldef "j" as "<IMG SRC='_bj.gif' WIDTH=7 HEIGHT=19 ALT='j' ALIGN=TOP>";
htmldef "k" as "<IMG SRC='_bk.gif' WIDTH=9 HEIGHT=19 ALT='k' ALIGN=TOP>";
htmldef "l" as "<IMG SRC='_bl.gif' WIDTH=6 HEIGHT=19 ALT='l' ALIGN=TOP>";
htmldef "m" as "<IMG SRC='_bm.gif' WIDTH=14 HEIGHT=19 ALT='m' ALIGN=TOP>";
htmldef "n" as "<IMG SRC='_bn.gif' WIDTH=10 HEIGHT=19 ALT='n' ALIGN=TOP>";
htmldef "p" as "<IMG SRC='_bp.gif' WIDTH=10 HEIGHT=19 ALT='p' ALIGN=TOP>";
htmldef "q" as "<IMG SRC='_bq.gif' WIDTH=8 HEIGHT=19 ALT='q' ALIGN=TOP>";
htmldef "r" as "<IMG SRC='_br.gif' WIDTH=8 HEIGHT=19 ALT='r' ALIGN=TOP>";
htmldef "t" as "<IMG SRC='_bt.gif' WIDTH=7 HEIGHT=19 ALT='t' ALIGN=TOP>";
htmldef "u" as "<IMG SRC='_bu.gif' WIDTH=10 HEIGHT=19 ALT='u' ALIGN=TOP>";
htmldef "w" as "<IMG SRC='_bw.gif' WIDTH=12 HEIGHT=19 ALT='w' ALIGN=TOP>";
htmldef "x" as "<IMG SRC='_bx.gif' WIDTH=10 HEIGHT=19 ALT='x' ALIGN=TOP>";
htmldef "y" as "<IMG SRC='_by.gif' WIDTH=9 HEIGHT=19 ALT='y' ALIGN=TOP>";
htmldef "z" as "<IMG SRC='_bz.gif' WIDTH=9 HEIGHT=19 ALT='z' ALIGN=TOP>";
htmldef "(" as "<IMG SRC='lp.gif' WIDTH=5 HEIGHT=19 ALT='(' ALIGN=TOP>";
htmldef ")" as "<IMG SRC='rp.gif' WIDTH=5 HEIGHT=19 ALT=')' ALIGN=TOP>";
htmldef "=" as " <IMG SRC='eq.gif' WIDTH=12 HEIGHT=19 ALT='=' ALIGN=TOP> ";
htmldef "==" as " <IMG SRC='equiv.gif' WIDTH=12 HEIGHT=19 ALT='=='" +
  " ALIGN=TOP> ";
htmldef "v" as " <IMG SRC='cup.gif' WIDTH=10 HEIGHT=19 ALT='v' ALIGN=TOP> ";
htmldef "^" as " <IMG SRC='cap.gif' WIDTH=10 HEIGHT=19 ALT='^' ALIGN=TOP> ";
htmldef "0" as "<IMG SRC='0.gif' WIDTH=8 HEIGHT=19 ALT='0' ALIGN=TOP>";
htmldef "1" as "<IMG SRC='1.gif' WIDTH=7 HEIGHT=19 ALT='1' ALIGN=TOP>";
/* htmldef "-" as "<IMG SRC='shortminus.gif' WIDTH=8 HEIGHT=19 ALT='-'" +
  " ALIGN=TOP>"; */
/* htmldef "_|_" as " <IMG SRC='perp.gif' WIDTH=11 HEIGHT=19 ALT='_|_'" +
  " ALIGN=TOP> "; */
htmldef "'" as "<IMG SRC='supperp.gif' WIDTH=9 HEIGHT=19 ALT=" +
   '"' + "'" + '"' + " ALIGN=TOP>";
htmldef "wff" as "<IMG SRC='_wff.gif' WIDTH=24 HEIGHT=19 ALT='wff'" +
  " ALIGN=TOP> ";
htmldef "term" as "<IMG SRC='_term.gif' WIDTH=32 HEIGHT=19 ALT='term'" +
  " ALIGN=TOP> ";
/* Mladen wants the turnstile to go away 2/9/02 */
/*htmldef "|-" as "<IMG SRC='_vdash.gif' WIDTH=10 HEIGHT=19 ALT='|-'" +
  " ALIGN=TOP> ";*/
htmldef "|-" as "";
htmldef "C" as " <IMG SRC='cc.gif' WIDTH=12 HEIGHT=19 ALT='C' ALIGN=TOP> ";
htmldef "," as "<IMG SRC='comma.gif' WIDTH=4 HEIGHT=19 ALT=',' ALIGN=TOP> ";
htmldef "=<" as " <IMG SRC='le.gif' WIDTH=11 HEIGHT=19 ALT='=&lt;'" +
  " ALIGN=TOP> ";
htmldef "=<2" as " <IMG SRC='_le2.gif' WIDTH=17 HEIGHT=19 ALT='=&lt;2'" +
  " ALIGN=TOP> ";
htmldef "->0" as " <IMG SRC='_to0.gif' WIDTH=21 HEIGHT=19 ALT='-&gt;0'" +
  " ALIGN=TOP> ";
htmldef "->1" as " <IMG SRC='_to1.gif' WIDTH=19 HEIGHT=19 ALT='-&gt;1'" +
  " ALIGN=TOP> ";
htmldef "->2" as " <IMG SRC='_to2.gif' WIDTH=21 HEIGHT=19 ALT='-&gt;2'" +
  " ALIGN=TOP> ";
htmldef "->3" as " <IMG SRC='_to3.gif' WIDTH=21 HEIGHT=19 ALT='-&gt;3'" +
  " ALIGN=TOP> ";
htmldef "->4" as " <IMG SRC='_to4.gif' WIDTH=20 HEIGHT=19 ALT='-&gt;4'" +
  " ALIGN=TOP> ";
htmldef "->5" as " <IMG SRC='_to5.gif' WIDTH=20 HEIGHT=19 ALT='-&gt;5'" +
  " ALIGN=TOP> ";
htmldef "<->1" as " <IMG SRC='_bi1.gif' WIDTH=19 HEIGHT=19" +
  " ALT='&lt;-&gt;1' ALIGN=TOP> ";
htmldef "<->3" as " <IMG SRC='_bi3.gif' WIDTH=21 HEIGHT=19" +
  " ALT='&lt;-&gt;3' ALIGN=TOP> ";
htmldef "u3" as " <IMG SRC='_cup3.gif' WIDTH=16 HEIGHT=19 ALT='u3'" +
  " ALIGN=TOP> ";
htmldef "^3" as " <IMG SRC='_cap3.gif' WIDTH=16 HEIGHT=19 ALT='^3'" +
  " ALIGN=TOP> ";
htmldef "==0" as " <IMG SRC='_equiv0.gif' WIDTH=18 HEIGHT=19 ALT='==0'" +
  " ALIGN=TOP> ";
htmldef "==1" as " <IMG SRC='_equiv1.gif' WIDTH=16 HEIGHT=19 ALT='==1'" +
  " ALIGN=TOP> ";
htmldef "==2" as " <IMG SRC='_equiv2.gif' WIDTH=18 HEIGHT=19 ALT='==2'" +
  " ALIGN=TOP> ";
htmldef "==3" as " <IMG SRC='_equiv3.gif' WIDTH=18 HEIGHT=19 ALT='==3'" +
  " ALIGN=TOP> ";
htmldef "==4" as " <IMG SRC='_equiv4.gif' WIDTH=18 HEIGHT=19 ALT='==4'" +
  " ALIGN=TOP> ";
htmldef "==5" as " <IMG SRC='_equiv5.gif' WIDTH=18 HEIGHT=19 ALT='==5'" +
  " ALIGN=TOP> ";
htmldef "==OA" as " <IMG SRC='_oa.gif' WIDTH=26 HEIGHT=19 ALT='==OA'" +
  " ALIGN=TOP> ";
/*
htmldef "==u" as '<FONT FACE="Symbol"> &#186;</FONT ><I><SUB>u</SUB> </I>';
htmldef "u.u" as '<FONT FACE="Symbol"> &#218;</FONT ><I><SUB>u</SUB> </I>';
htmldef "^u" as '<FONT FACE="Symbol"> &#217;</FONT ><I><SUB>u</SUB> </I>';
htmldef "-u" as '<FONT FACE="Symbol"> &#216;</FONT ><I><SUB>u</SUB> </I>';
htmldef "=<u" as '<FONT FACE="Symbol"> &#163;</FONT ><I><SUB>u</SUB> </I>';
htmldef "=" as '<FONT FACE="Symbol"> = </FONT>';
*/

/* Definitions for Unicode version */
althtmldef "a" as '<I><FONT COLOR="#CC4400">a</FONT></I>';
althtmldef "b" as '<I><FONT COLOR="#CC4400">b</FONT></I>';
althtmldef "c" as '<I><FONT COLOR="#CC4400">c</FONT></I>';
althtmldef "d" as '<I><FONT COLOR="#CC4400">d</FONT></I>';
althtmldef "e" as '<I><FONT COLOR="#CC4400">e</FONT></I>';
althtmldef "f" as '<I><FONT COLOR="#CC4400">f</FONT></I>';
althtmldef "g" as '<I><FONT COLOR="#CC4400">g</FONT></I>';
althtmldef "h" as '<I><FONT COLOR="#CC4400">h</FONT></I>';
althtmldef "i" as '<I><FONT COLOR="#CC4400">i</FONT></I>';
althtmldef "j" as '<I><FONT COLOR="#CC4400">j</FONT></I>';
althtmldef "k" as '<I><FONT COLOR="#CC4400">k</FONT></I>';
althtmldef "l" as '<I><FONT COLOR="#CC4400">l</FONT></I>';
althtmldef "m" as '<I><FONT COLOR="#CC4400">m</FONT></I>';
althtmldef "n" as '<I><FONT COLOR="#CC4400">n</FONT></I>';
althtmldef "p" as '<I><FONT COLOR="#CC4400">p</FONT></I>';
althtmldef "q" as '<I><FONT COLOR="#CC4400">q</FONT></I>';
althtmldef "r" as '<I><FONT COLOR="#CC4400">r</FONT></I>';
althtmldef "t" as '<I><FONT COLOR="#CC4400">t</FONT></I>';
althtmldef "u" as '<I><FONT COLOR="#CC4400">u</FONT></I>';
althtmldef "w" as '<I><FONT COLOR="#CC4400">w</FONT></I>';
althtmldef "x" as '<I><FONT COLOR="#CC4400">x</FONT></I>';
althtmldef "y" as '<I><FONT COLOR="#CC4400">y</FONT></I>';
althtmldef "z" as '<I><FONT COLOR="#CC4400">z</FONT></I>';
althtmldef "a0" as '<I><FONT COLOR="#CC4400">a<SUB>0</SUB></FONT></I>';
althtmldef "a1" as '<I><FONT COLOR="#CC4400">a<SUB>1</SUB></FONT></I>';
althtmldef "a2" as '<I><FONT COLOR="#CC4400">a<SUB>2</SUB></FONT></I>';
althtmldef "b0" as '<I><FONT COLOR="#CC4400">b<SUB>0</SUB></FONT></I>';
althtmldef "b1" as '<I><FONT COLOR="#CC4400">b<SUB>1</SUB></FONT></I>';
althtmldef "b2" as '<I><FONT COLOR="#CC4400">b<SUB>2</SUB></FONT></I>';
althtmldef "c0" as '<I><FONT COLOR="#CC4400">c<SUB>0</SUB></FONT></I>';
althtmldef "c1" as '<I><FONT COLOR="#CC4400">c<SUB>1</SUB></FONT></I>';
althtmldef "c2" as '<I><FONT COLOR="#CC4400">c<SUB>2</SUB></FONT></I>';
althtmldef "p0" as '<I><FONT COLOR="#CC4400">p<SUB>0</SUB></FONT></I>';
althtmldef "p1" as '<I><FONT COLOR="#CC4400">p<SUB>1</SUB></FONT></I>';
althtmldef "p2" as '<I><FONT COLOR="#CC4400">p<SUB>2</SUB></FONT></I>';
htmldef "a0" as '<I><FONT COLOR="#CC4400">a<SUB>0</SUB></FONT></I>';
htmldef "a1" as '<I><FONT COLOR="#CC4400">a<SUB>1</SUB></FONT></I>';
htmldef "a2" as '<I><FONT COLOR="#CC4400">a<SUB>2</SUB></FONT></I>';
htmldef "b0" as '<I><FONT COLOR="#CC4400">b<SUB>0</SUB></FONT></I>';
htmldef "b1" as '<I><FONT COLOR="#CC4400">b<SUB>1</SUB></FONT></I>';
htmldef "b2" as '<I><FONT COLOR="#CC4400">b<SUB>2</SUB></FONT></I>';
htmldef "c0" as '<I><FONT COLOR="#CC4400">c<SUB>0</SUB></FONT></I>';
htmldef "c1" as '<I><FONT COLOR="#CC4400">c<SUB>1</SUB></FONT></I>';
htmldef "c2" as '<I><FONT COLOR="#CC4400">c<SUB>2</SUB></FONT></I>';
htmldef "p0" as '<I><FONT COLOR="#CC4400">p<SUB>0</SUB></FONT></I>';
htmldef "p1" as '<I><FONT COLOR="#CC4400">p<SUB>1</SUB></FONT></I>';
htmldef "p2" as '<I><FONT COLOR="#CC4400">p<SUB>2</SUB></FONT></I>';
althtmldef "(" as '(';
althtmldef ")" as ')';
althtmldef "=" as ' = '; /* &equals; */
althtmldef "==" as ' &equiv; ';
althtmldef "v" as ' &cup; ';
althtmldef "^" as ' &cap; ';
althtmldef "1" as '1';
althtmldef "0" as '0';
/* althtmldef "-" as ' - '; */
/* althtmldef "'" as '&#8869;'; */
althtmldef "'" as '<SUP>&#8869;</SUP> ';
althtmldef "wff" as '<FONT COLOR="#00CC00">wff&nbsp; </FONT>';
althtmldef "term" as '<FONT COLOR="#00CC00">term&nbsp; </FONT>';
/* Mladen wants the turnstile to go away 2/9/02 */
/*althtmldef "|-" as '<FONT COLOR="#00CC00">|-&nbsp; </FONT>';*/
althtmldef "|-" as '';
althtmldef "C" as '<I> C </I>';
althtmldef "," as ', ';
althtmldef "=<" as ' &le; ';
althtmldef "=<2" as ' &le;<SUB>2 </SUB>';
althtmldef "->0" as ' &rarr;<SUB>0 </SUB>';
althtmldef "->1" as ' &rarr;<SUB>1 </SUB>';
althtmldef "->2" as ' &rarr;<SUB>2 </SUB>';
althtmldef "->3" as ' &rarr;<SUB>3 </SUB>';
althtmldef "->4" as ' &rarr;<SUB>4 </SUB>';
althtmldef "->5" as ' &rarr;<SUB>5 </SUB>';
althtmldef "<->1" as ' &harr;<SUB>1 </SUB> ';
althtmldef "<->3" as ' &harr;<SUB>3 </SUB> ';
althtmldef "u3" as ' &cup;<SUB>3 </SUB> ';
althtmldef "^3" as ' &cap;<SUB>3 </SUB> ';
althtmldef "==0" as ' &equiv;<SUB>0 </SUB> ';
althtmldef "==1" as ' &equiv;<SUB>1 </SUB>';
althtmldef "==2" as ' &equiv;<SUB>2 </SUB>';
althtmldef "==3" as ' &equiv;<SUB>3 </SUB>';
althtmldef "==4" as ' &equiv;<SUB>4 </SUB>';
althtmldef "==5" as ' &equiv;<SUB>5 </SUB>';
althtmldef "==OA" as ' &equiv;<SUB>OA </SUB>';
/*
althtmldef "==u" as ' &equiv;<I><SUB>u</SUB> </I>';
althtmldef "u.u" as ' &middot;<I><SUB>u</SUB> </I>';
althtmldef "^u" as ' &cap;<I><SUB>u</SUB> </I>';
althtmldef "-u" as ' &minus;<I><SUB>u</SUB> </I>';
althtmldef "=<u" as ' &le;<I><SUB>u</SUB> </I>';
althtmldef "=" as ' = ';
*/
/* End of Unicode defintions */

latexdef "a" as "a";
latexdef "b" as "b";
latexdef "c" as "c";
latexdef "d" as "d";
latexdef "e" as "e";
latexdef "f" as "f";
latexdef "g" as "g";
latexdef "h" as "h";
latexdef "i" as "i";
latexdef "j" as "j";
latexdef "k" as "k";
latexdef "l" as "l";
latexdef "m" as "m";
latexdef "n" as "n";
latexdef "p" as "p";
latexdef "q" as "q";
latexdef "r" as "r";
latexdef "t" as "t";
latexdef "u" as "u";
latexdef "w" as "w";
latexdef "x" as "x";
latexdef "y" as "y";
latexdef "z" as "z";
latexdef "(" as "(";
latexdef ")" as ")";
latexdef "=" as "=";
latexdef "==" as "\equiv ";
latexdef "v" as "\vee ";
latexdef "^" as "\wedge ";
latexdef "0" as "0";
latexdef "1" as "1";
latexdef "'" as "'";
latexdef "wff" as "\mathrm{wff}";
latexdef "term" as "\mathrm{term}";
latexdef "|-" as "\vdash";
latexdef "C" as "C";
latexdef "," as ",";
latexdef "=<" as "\le ";
latexdef "=<2" as "\le_2";
latexdef "->0" as "\to_0";
latexdef "->1" as "\to_1";
latexdef "->2" as "\to_2";
latexdef "->3" as "\to_3";
latexdef "->4" as "\to_4";
latexdef "->5" as "\to_5";
latexdef "<->1" as "\leftrightarrow_1";
latexdef "<->3" as "\leftrightarrow_3";
latexdef "u3" as "\vee_3";
latexdef "^3" as "\wedge_3";
latexdef "==0" as "\equiv_0";
latexdef "==1" as "\equiv_1";
latexdef "==2" as "\equiv_2";
latexdef "==3" as "\equiv_3";
latexdef "==4" as "\equiv_4";
latexdef "==5" as "\equiv_5";
latexdef "==OA" as "\equiv_\mathrm{OA}";
latexdef "a0" as "a_0";
latexdef "a1" as "a_1";
latexdef "a2" as "a_2";
latexdef "b0" as "b_0";
latexdef "b1" as "b_1";
latexdef "b2" as "b_2";
latexdef "c0" as "c_0";
latexdef "c1" as "c_1";
latexdef "c2" as "c_2";
latexdef "p0" as "p_0";
latexdef "p1" as "p_1";
latexdef "p2" as "p_2";

/* End of typesetting definition section */
$)

$( 456789012345 (79-character line to adjust text window width) 567890123456 $)


$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
        Weakly distributive ortholattices (WDOL)
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        WDOL law
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( The WDOL (weakly distributive ortholattice) axiom.  (Contributed by NM,
     4-Mar-2006.) $)
  ax-wdol $a |- ( ( a == b ) v ( a == b ' ) ) = 1 $.

  $( Any two variables (weakly) commute in a WDOL. (Contributed by NM,
     4-Mar-2006.) $)
  wdcom $p |- C ( a , b ) = 1 $=
    ( wcmtr wa wn wo wt df-cmtr or42 tb dfb ax-a1 lan ax-r1 lor 2or ax-wdol 3tr
    ax-r2 ) ABCABDZABEZDZFAEZBDZUCUADZFFTUEFZUBUDFZFZGABHTUBUDUEIUHABJZAUAJZFZG
    UKUHUIUFUJUGABKUJUBUCUAEZDZFUGAUAKUMUDUBUDUMBULUCBLMNOSPNABQSR $.

  ${
    wdwom.1 $e |- ( a ' v ( a ^ b ) ) = 1 $.
    $( Prove 2-variable WOML rule in WDOL. This will make all WOML theorems
       available to us.  The proof does not use ~ ax-r3 or ~ ax-wom .  Since
       this is the same as ~ ax-wom , from here on we will freely use those
       theorems invoking ~ ax-wom .  (Contributed by NM, 4-Mar-2006.) $)
    wdwom $p |- ( b v ( a ' ^ b ' ) ) = 1 $=
      ( wn wa wo wi2 wt df-i2 ax-r1 le1 wi5 df-i5 wi1 df-i1 ax-r2 wql1lem wcmtr
      or4 anor1 lor ax-r5 or12 df-cmtr 3tr1 wdcom skr0 i5lei2 bltr lebi ) BADZB
      DZEZFZABGZHUOUNABIJUOHUOKHABLZUOUPHUPABEZUKBEZFZUMFZHABMUKBFZUTABABNUKUQF
      HABOCPQVADZUTFZABRZHUSVBUMFFZUQAULEZFZURUMFZFZVCVDVEUQVBFZVHFVIUQURVBUMSV
      JVGVHVBVFUQVFVBABTJUAUBPVBUSUMUCABUDUEABUFPUGPJABUHUIUJP $.
  $}

  $( Prove the weak distributive law in WDOL. This is our first WDOL theorem
     making use of ~ ax-wom , which is justified by ~ wdwom .  (Contributed by
     NM, 4-Mar-2006.) $)
  wddi1 $p |- ( ( a ^ ( b v c ) ) == ( ( a ^ b ) v ( a ^ c ) ) ) = 1 $=
    ( wdcom wfh1 ) ABCABDACDE $.

  $( The weak distributive law in WDOL. (Contributed by NM, 5-Mar-2006.) $)
  wddi2 $p |- ( ( ( a v b ) ^ c ) == ( ( a ^ c ) v ( b ^ c ) ) ) = 1 $=
    ( wo wa wancom wddi1 w2or wr2 ) ABDZCECJEZACEZBCEZDZJCFKCAEZCBEZDNCABGOLPMC
    AFCBFHII $.

  $( The weak distributive law in WDOL. (Contributed by NM, 5-Mar-2006.) $)
  wddi3 $p |- ( ( a v ( b ^ c ) ) ==
             ( ( a v b ) ^ ( a v c ) ) ) = 1 $=
    ( wdcom wfh3 ) ABCABDACDE $.

  $( The weak distributive law in WDOL. (Contributed by NM, 5-Mar-2006.) $)
  wddi4 $p |- ( ( ( a ^ b ) v c ) ==
             ( ( a v c ) ^ ( b v c ) ) ) = 1 $=
    ( wa wo wa2 wddi3 w2an wr2 ) ABDZCECJEZACEZBCEZDZJCFKCAEZCBEZDNCABGOLPMCAFC
    BFHII $.

  ${
    wdid0id5.1 $e |- ( a ==0 b ) = 1 $.
    $( Show that quantum identity follows from classical identity in a WDOL.
       (Contributed by NM, 5-Mar-2006.) $)
    wdid0id5 $p |- ( a == b ) = 1 $=
      ( tb wa wn wo wt dfb wid0 df-id0 ax-r1 ax-r2 wa4 wleoa wancom wddi3 w3tr1
      wr1 wa2 wr2 w2an wddi4 wwbmp ) ABDABEAFZBFZEZGZHABIUEBGZUFAGZEZUHUKABJZHU
      LUKABKLCMUJUIEAUGGZBUGGZEUKUHUJUMUIUNAUFGZAUEGZUOEZUJUMUOUOUPEZUQURUOUOUP
      UPUOANOSUOUPPUAUFATAUEUFQRBUEGZUSBUFGZEZUIUNVAUSUSUTUTUSBNOSUEBTBUEUFQRUB
      UIUJPABUGUCRUDM $.

    $( Show a quantum identity that follows from classical identity in a WDOL.
       (Contributed by NM, 5-Mar-2006.) $)
    wdid0id1 $p |- ( a ==1 b ) = 1 $=
      ( wid1 wn wo wa wt df-id1 wid0 df-id0 ax-r1 ax-r2 wancom wa2 wlan wa4 wr2
      wleoa wr1 wddi3 w2an biid w3tr1 wwbmp ) ABDABEZFZAEZABGFZGZHABIUHBFZUFAFZ
      GZUJUMABJZHUNUMABKLCMUMUIUGGUMUJUKUIULUGUKUHAFZUKGZUIUPUKUPUKUOGZUKUOUKNU
      QUKAUHFZGUKUOURUKUHAOPUKURURUKAQSRRTUIUPUHABUATRUFAOUBUMUCUGUINUDUEM $.

    $( Show a quantum identity that follows from classical identity in a WDOL.
       (Contributed by NM, 5-Mar-2006.) $)
    wdid0id2 $p |- ( a ==2 b ) = 1 $=
      ( wid2 wn wo wa df-id2 wid0 df-id0 ax-r1 ax-r2 wancom wa2 wa4 wleoa wddi3
      wt wr1 w3tr1 w2an wr2 wwbmp ) ABDABEZFZBAEZUDGFZGZRABHUFBFZUDAFZGZUHUKABI
      ZRULUKABJKCLUKUJUIGUHUIUJMUJUEUIUGUDANBUFFZUMBUDFZGZUIUGUOUMUMUNUNUMBOPSU
      FBNBUFUDQTUAUBUCL $.

    $( Show a quantum identity that follows from classical identity in a WDOL.
       (Contributed by NM, 5-Mar-2006.) $)
    wdid0id3 $p |- ( a ==3 b ) = 1 $=
      ( wid3 wn wo wa wt df-id3 df-id0 ax-r1 ax-r2 wa4 wleoa wr1 wancom wr2 wa2
      wid0 wddi3 w3tr1 wlan wwbmp ) ABDAEZBFZAUDBEZGFZGZHABIUEUFAFZGZUHUJABSZHU
      KUJABJKCLUIUGUEAUFFZAUDFZULGZUIUGULULUMGZUNUOULULUMUMULAMNOULUMPQUFARAUDU
      FTUAUBUCL $.

    $( Show a quantum identity that follows from classical identity in a WDOL.
       (Contributed by NM, 5-Mar-2006.) $)
    wdid0id4 $p |- ( a ==4 b ) = 1 $=
      ( wid4 wn wo wa wt df-id4 wid0 df-id0 ax-r1 ax-r2 wddi3 wa2 wa4 wleoa wr2
      wlan wr1 wwbmp ) ABDAEBFZBEZABGFZGZHABIUBUCAFZGZUEUGABJZHUHUGABKLCMUFUDUB
      UDUFUDUFUCBFZGZUFUCABNUJUFBUCFZGUFUIUKUFUCBOSUFUKUKUFBPQRRTSUAM $.

    $( Show WDOL analog of WOM law.  (Contributed by NM, 5-Mar-2006.) $)
    wdka4o $p |- ( ( a v c ) ==0 ( b v c ) ) = 1 $=
      ( wo wdid0id5 wr5 id5id0 ) ACEBCEABCABDFGH $.
  $}

  $( The weak distributive law in WDOL. (Contributed by NM, 5-Mar-2006.) $)
  wddi-0 $p |- ( ( a ^ ( b v c ) ) ==0 ( ( a ^ b ) v ( a ^ c ) ) ) = 1 $=
    ( wo wa wddi1 id5id0 ) ABCDEABEACEDABCFG $.

  $( The weak distributive law in WDOL. (Contributed by NM, 5-Mar-2006.) $)
  wddi-1 $p |- ( ( a ^ ( b v c ) ) ==1 ( ( a ^ b ) v ( a ^ c ) ) ) = 1 $=
    ( wo wa wddi-0 wdid0id1 ) ABCDEABEACEDABCFG $.

  $( The weak distributive law in WDOL. (Contributed by NM, 5-Mar-2006.) $)
  wddi-2 $p |- ( ( a ^ ( b v c ) ) ==2 ( ( a ^ b ) v ( a ^ c ) ) ) = 1 $=
    ( wo wa wddi-0 wdid0id2 ) ABCDEABEACEDABCFG $.

  $( The weak distributive law in WDOL. (Contributed by NM, 5-Mar-2006.) $)
  wddi-3 $p |- ( ( a ^ ( b v c ) ) ==3 ( ( a ^ b ) v ( a ^ c ) ) ) = 1 $=
    ( wo wa wddi-0 wdid0id3 ) ABCDEABEACEDABCFG $.

  $( The weak distributive law in WDOL. (Contributed by NM, 5-Mar-2006.) $)
  wddi-4 $p |- ( ( a ^ ( b v c ) ) ==4 ( ( a ^ b ) v ( a ^ c ) ) ) = 1 $=
    ( wo wa wddi-0 wdid0id4 ) ABCDEABEACEDABCFG $.

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
        Modular ortholattices (MOL)
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Modular law
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( The modular law axiom.  (Contributed by NM, 15-Mar-2010.) $)
  ax-ml $a |- ( ( a v b ) ^ ( a v c ) ) =< ( a v ( b ^ ( a v c ) ) ) $.

  $( Modular law in equational form.  (Contributed by NM, 15-Mar-2010.)
     (Revised by NM, 31-Mar-2011.) $)
  ml $p |- ( a v ( b ^ ( a v c ) ) ) = ( ( a v b ) ^ ( a v c ) ) $=
    ( wo wa leo ler2an leor leran lel2or ax-ml lebi ) ABACDZEZDABDZMEZAPNAOMABF
    ACFGBOMBAHIJABCKL $.

  $( Dual of modular law.  (Contributed by NM, 15-Mar-2010.)  (Revised by NM,
     31-Mar-2011.) $)
  mldual $p |- ( a ^ ( b v ( a ^ c ) ) ) = ( ( a ^ b ) v ( a ^ c ) ) $=
    ( wa wo wn anor3 cm oran3 lan ax-r1 tr lor ml 2an 3tr 3tr2 con1 ) ABACDZEZD
    ZABDZSEZAFZTFZEZUBFZSFZDZUAFUCFUFUDBFZUDCFZEZDZEUDUJEZULDUIUEUMUDUEUJUHDZUM
    UOUEBSGHUMUOULUHUJACIZJKLMUDUJUKNUNUGULUHABIUPOPATIUBSGQR $.

  ${
    mli.1 $e |- c =< a $.
    $( Inference version of modular law.  (Contributed by NM, 1-Apr-2012.) $)
    ml2i $p |- ( c v ( b ^ a ) ) = ( ( c v b ) ^ a ) $=
      ( wo wa ml df-le2 lan lor 3tr2 ) CBCAEZFZECBEZLFCBAFZENAFCBAGMOCLABCADHZI
      JLANPIK $.

    $( Inference version of modular law.  (Contributed by NM, 1-Apr-2012.) $)
    mli $p |- ( ( a ^ b ) v c ) = ( a ^ ( b v c ) ) $=
      ( wa wo ancom ror orcom ml2i 3tr ran ) ABEZCFZCBFZAEZBCFZAEAQENBAEZCFCRFP
      MRCABGHRCIABCDJKOQACBILQAGK $.
  $}

  ${
    mlduali.1 $e |- a =< c $.
    $( Inference version of dual of modular law.  (Contributed by NM,
       1-Apr-2012.) $)
    mldual2i $p |- ( c ^ ( b v a ) ) = ( ( c ^ b ) v a ) $=
      ( wa wo mldual lear leid ler2an lebi lor lan 3tr2 ) CBCAEZFZECBEZOFCBAFZE
      QAFCBAGPRCOABOACAHACADAIJKZLMOAQSLN $.

    $( Inference version of dual of modular law.  (Contributed by NM,
       1-Apr-2012.) $)
    mlduali $p |- ( ( a v b ) ^ c ) = ( a v ( b ^ c ) ) $=
      ( wo wa ax-a2 ran ancom mldual2i 3tr ror orcom ) ABEZCFZCBFZAEZBCFZAEAREO
      BAEZCFCSFQNSCABGHSCIABCDJKPRACBILRAMK $.
  $}

  $( Form of modular law that swaps two terms.  (Contributed by NM,
     1-Apr-2012.) $)
  ml3le $p |- ( a v ( b ^ ( c v a ) ) ) =< ( a v ( c ^ ( b v a ) ) ) $=
    ( wo wa lear lelor or12 oridm lor orcom 3tr lbtr leor lel2or ler2an mlduali
    leao1 ) ABCADZEZDZACDZBADZEACUCEDUAUBUCUAASDZUBTSABSFGUDCAADZDSUBACAHUEACAI
    JCAKLMAUCTABNZBSAROPACUCUFQM $.

  $( Form of modular law that swaps two terms.  (Contributed by NM,
     1-Apr-2012.) $)
  ml3 $p |- ( a v ( b ^ ( c v a ) ) ) = ( a v ( c ^ ( b v a ) ) ) $=
    ( wo wa ml3le lebi ) ABCADEDACBADEDABCFACBFG $.

  $( Part of von Neumann's lemma.  Lemma 9, Kalmbach p. 96 (Contributed by NM,
     15-Mar-2010.)  (Revised by NM, 31-Mar-2011.) $)
  vneulem1 $p |- ( ( ( x v y ) v u ) ^ w )
      = ( ( ( x v y ) v u ) ^ ( ( u v w ) ^ w ) ) $=
    ( wo wa leor leid ler2an lear lebi lan ) BABEZBFZCDEAEBNBMBBAGBHIMBJKL $.

  $( Part of von Neumann's lemma.  Lemma 9, Kalmbach p. 96 (Contributed by NM,
     15-Mar-2010.)  (Revised by NM, 31-Mar-2011.) $)
  vneulem2 $p |- ( ( ( x v y ) v u ) ^ ( ( u v w ) ^ w ) )
      = ( ( ( ( x v y ) ^ ( u v w ) ) v u ) ^ w ) $=
    ( wo wa anass cm ax-a2 ran ml orcom 3tr tr ) CDEZAEZABEZBFFZPQFZBFZOQFZAEZB
    FTRPQBGHSUBBSAOEZQFZAUAEZUBPUCQOAIJUEUDAOBKHAUALMJN $.

  ${
    vneulem3.1 $e |- ( ( x v y ) ^ ( u v w ) ) = 0 $.
    $( Part of von Neumann's lemma.  Lemma 9, Kalmbach p. 96 (Contributed by
       NM, 15-Mar-2010.)  (Revised by NM, 31-Mar-2011.) $)
    vneulem3 $p |- ( ( ( ( x v y ) ^ ( u v w ) ) v u ) ^ w ) = ( u ^ w ) $=
      ( wo wa wf ror or0r tr ran ) CDFABFGZAFZABNHAFAMHAEIAJKL $.

    $( Part of von Neumann's lemma.  Lemma 9, Kalmbach p. 96 (Contributed by
       NM, 15-Mar-2010.)  (Revised by NM, 31-Mar-2011.) $)
    vneulem4 $p |- ( ( ( x v y ) v u ) ^ w ) = ( u ^ w ) $=
      ( wo wa vneulem1 vneulem2 vneulem3 3tr ) CDFZAFZBGMABFZBGGLNGAFBGABGABCDH
      ABCDIABCDEJK $.
  $}

  $( Part of von Neumann's lemma.  Lemma 9, Kalmbach p. 96 (Contributed by NM,
     15-Mar-2010.)  (Revised by NM, 31-Mar-2011.) $)
  vneulem5 $p |- ( ( ( x v y ) v u ) ^ ( ( x v y ) v w ) )
        = ( ( x v y ) v ( ( ( x v y ) v u ) ^ w ) ) $=
    ( wo wa ancom ml cm lor 3tr ) CDEZAEZLBEZFNMFZLBMFZEZLMBFZEMNGQOLBAHIPRLBMG
    JK $.

  ${
    vneulem6.1 $e |- ( ( a v b ) ^ ( c v d ) ) = 0 $.
    $( Part of von Neumann's lemma.  Lemma 9, Kalmbach p. 96 (Contributed by
       NM, 15-Mar-2010.)  (Revised by NM, 31-Mar-2011.) $)
    vneulem6 $p |- ( ( ( a v b ) v d ) ^ ( ( b v c ) v d ) )
         = ( ( c ^ a ) v ( b v d ) ) $=
      ( wo wa orcom ror or32 tr 2an vneulem5 leor ax-a2 leao3 bltr lel2or leror
      ler ax-r2 ran wf vneulem4 lerr leao2 leo ler2an lebi ) ABFZDFZBCFZDFZGZCA
      GZBDFZFZUNUPUPAFZCGZFZUQUNURUPCFZGUTUKURUMVAUKBAFZDFZURUJVBDABHIBADJKBCDJ
      LACBDMUAUPUQUSUPUONUSDCGZUQUSVCCGVDURVCCBDAJUBDCBAVBDCFZGUJCDFZGUCVBUJVEV
      FBAODCOLEKUDKVDUPUODCBPUEQRQUQUKUMUOUKUPUOUJDACBUFTBUJDBANSRUOUMUPUOULDCA
      BPTBULDBCUGSRUHUI $.

    $( Part of von Neumann's lemma.  Lemma 9, Kalmbach p. 96 (Contributed by
       NM, 31-Mar-2011.) $)
    vneulem7 $p |- ( ( c ^ a ) v ( b v d ) ) = ( b v d ) $=
      ( wa wo wf leao2 leao1 ler2an lbtr le0 lebi ror or0r tr ) CAFZBDGZGHSGSRH
      SRHRABGZCDGZFHRTUAACBICADJKELRMNOSPQ $.

    $( Part of von Neumann's lemma.  Lemma 9, Kalmbach p. 96 (Contributed by
       NM, 31-Mar-2011.) $)
    vneulem8 $p |- ( ( ( a v b ) v d ) ^ ( ( b v c ) v d ) ) = ( b v d ) $=
      ( wo wa vneulem6 vneulem7 tr ) ABFDFBCFDFGCAGBDFZFKABCDEHABCDEIJ $.

    $( Part of von Neumann's lemma.  Lemma 9, Kalmbach p. 96 (Contributed by
       NM, 31-Mar-2011.) $)
    vneulem9 $p |- ( ( ( a v b ) v d ) ^ ( ( a v b ) v c ) )
         = ( ( c ^ d ) v ( a v b ) ) $=
      ( wo wa ancom vneulem5 ax-r2 orcom vneulem4 ror 3tr ) ABFZDFZOCFZGZOQDGZF
      ZSOFCDGZOFRQPGTPQHCDABIJOSKSUAOCDABELMN $.

    $( Part of von Neumann's lemma.  Lemma 9, Kalmbach p. 96 (Contributed by
       NM, 31-Mar-2011.) $)
    vneulem10 $p |- ( ( ( a v b ) v c ) ^ ( ( a v c ) v d ) ) = ( a v c ) $=
      ( wo wa ax-a2 ax-r5 or32 2an wf orcom tr vneulem8 ) ABFZCFZACFZDFZGBAFZCF
      ZADFCFZGRQUASUBPTCABHIACDJKBADCTDCFZGPCDFZGLTPUCUDBAMDCMKENON $.

    $( Part of von Neumann's lemma.  Lemma 9, Kalmbach p. 96 (Contributed by
       NM, 31-Mar-2011.) $)
    vneulem11 $p |- ( ( ( b v c ) v d ) ^ ( ( a v c ) v d ) )
         = ( ( c v d ) v ( a ^ b ) ) $=
      ( wo wa ax-a3 orcom tr ax-a2 ror or32 2an wf ancom vneulem9 3tr ) BCFDFZA
      CFZDFZGCDFZBFZUBAFZGABGZUBFUBUEFSUCUAUDSBUBFUCBCDHBUBIJUACAFZDFUDTUFDACKL
      CADMJNCDABUBABFZGUGUBGOUBUGPEJQUEUBIR $.
  $}

  $( Part of von Neumann's lemma.  Lemma 9, Kalmbach p. 96 (Contributed by NM,
     31-Mar-2011.) $)
  vneulem12 $p |- ( ( ( c ^ d ) v ( a v b ) ) ^ ( ( c v d ) v ( a ^ b ) ) )
          = ( ( c ^ d ) v ( ( a v b ) ^ ( ( c v d ) v ( a ^ b ) ) ) ) $=
    ( wa wo ml cm orass leao1 df-le2 ror tr lan lor 3tr2 ) CDEZABFZFZQCDFZABEZF
    ZFZEZQRUCEZFZSUBEQRUBEZFUFUDQRUBGHUCUBSUCQTFZUAFZUBUIUCQTUAIHUHTUAQTCDDJKLM
    ZNUEUGQUCUBRUJNOP $.

  ${
    vneulem13.1 $e |- ( ( a v b ) ^ ( c v d ) ) = 0 $.
    $( Part of von Neumann's lemma.  Lemma 9, Kalmbach p. 96 (Contributed by
       NM, 31-Mar-2011.) $)
    vneulem13 $p |- ( ( c ^ d ) v ( ( a v b ) ^ ( ( c v d ) v ( a ^ b ) ) ) )
           = ( ( c ^ d ) v ( a ^ b ) ) $=
      ( wo wa leao1 leid ler2an lear lebi lor lan mldual wf 2or or0r tr 3tr ) A
      BFZCDFZABGZFZGZUCCDGUEUAUBUAUCGZFZGUAUBGZUFFZUCUDUGUAUCUFUBUCUFUCUAUCABBH
      UCIJZUAUCKZLMNUAUBUCOUIPUCFUCUHPUFUCEUFUCUKUJLQUCRSTM $.

    $( Part of von Neumann's lemma.  Lemma 9, Kalmbach p. 96 (Contributed by
       NM, 31-Mar-2011.) $)
    vneulem14 $p |- ( ( ( c ^ d ) v ( a v b ) ) ^ ( ( c v d ) v ( a ^ b ) ) )
           = ( ( c ^ d ) v ( a ^ b ) ) $=
      ( wa wo vneulem12 vneulem13 tr ) CDFZABGZGCDGABFZGZFKLNFGKMGABCDHABCDEIJ
      $.

    $( Part of von Neumann's lemma.  Lemma 9, Kalmbach p. 96 (Contributed by
       NM, 31-Mar-2011.) $)
    vneulem15 $p |- ( ( a v c ) ^ ( b v d ) )
        = ( ( ( ( a v b ) v c ) ^ ( ( a v c ) v d ) )
           ^ ( ( ( a v b ) v d ) ^ ( ( b v c ) v d ) ) ) $=
      ( wo wa vneulem10 vneulem8 2an cm ) ABFZCFACFZDFGZLDFBCFDFGZGMBDFZGNMOPAB
      CDEHABCDEIJK $.

    $( Part of von Neumann's lemma.  Lemma 9, Kalmbach p. 96 (Contributed by
       NM, 31-Mar-2011.) $)
    vneulem16 $p |- ( ( ( ( a v b ) v c ) ^ ( ( a v c ) v d ) )
           ^ ( ( ( a v b ) v d ) ^ ( ( b v c ) v d ) ) )
        = ( ( a ^ b ) v ( c ^ d ) ) $=
      ( wo wa ancom an4 vneulem9 vneulem11 2an tr vneulem14 orcom 3tr ) ABFZCFZ
      ACFDFZGZQDFZBCFDFZGZGUCTGZCDGZQFZCDFABGZFZGZUGUEFZTUCHUDUARGZUBSGZGUIUAUB
      RSIUKUFULUHABCDEJABCDEKLMUIUEUGFUJABCDENUEUGOMP $.
  $}

  ${
    vneulem.1 $e |- ( ( a v b ) ^ ( c v d ) ) = 0 $.
    $( von Neumann's modular law lemma.  Lemma 9, Kalmbach p. 96 (Contributed
       by NM, 31-Mar-2011.) $)
    vneulem $p |- ( ( a v c ) ^ ( b v d ) ) = ( ( a ^ b ) v ( c ^ d ) ) $=
      ( wo wa vneulem15 vneulem16 tr ) ACFZBDFGABFZCFKDFGLDFBCFDFGGABGCDGFABCDE
      HABCDEIJ $.
  $}

  ${
    vneulemexp.1 $e |- ( ( a v b ) ^ ( c v d ) ) = 0 $.
    $( Expanded version of ~ vneulem .  (Contributed by NM, 31-Mar-2011.) $)
    vneulemexp $p |- ( ( a v c ) ^ ( b v d ) ) = ( ( a ^ b ) v ( c ^ d ) ) $=
      ( wo wa or32 2an orcom ror tr ancom ml cm 3tr ran ler2an lebi wf lor leor
      ax-a2 ax-r5 ax-r2 leid lear anass or0r leao3 lerr bltr lel2or leao2 leror
      lan ler leo leao1 lbtr le0 an4 ax-a3 orass df-le2 3tr2 mldual 2or ) ACFZB
      DFZGZABFZCFZVIDFZGZVLDFZBCFZDFZGZGZABGZCDGZFZVTVKVOVIVSVJVOBAFZCFZADFZCFZ
      GZVIVMWEVNWGVLWDCABUCUDACDHIWHDBGZVIFZVIWHWJWHVIVIBFZDGZFZWJWHWKVNGZWMWEW
      KWGVNWEVMWKWDVLCBAJZKABCHLADCHIWNVNWKGZVIDWKGZFZWMWKVNMWRWPVIDBNOWQWLVIDW
      KMUAPUEVIWJWLVIWIUBWLWBWJWLVMDGZWBWKVMDACBHQWSVMCDFZDGZGZVLWTGZCFZDGZWBDX
      AVMDXADWTDDCUBDUFRWTDUGSUPXBVMWTGZDGZXEXGXBVMWTDUHOXFXDDXFCVLFZWTGZCXCFZX
      DVMXHWTVLCUCQXJXICVLDNOCXCJPQLXDCDXDTCFCXCTCEKCUILQPZLWBVIWICDAUJUKULUMUL
      WJWEWGWIWEVIWIWDCBDAUNZUQAWDCABUBUOUMWIWGVIWIWFCDBAUJUQAWFCADURUOUMRSWJTV
      IFVIWITVIWITWIWDDCFZGZTWIWDXMXLDBCUSRXNXCTWDVLXMWTWODCJIELZUTWIVASKVIUILL
      LVSCAGZVJFZVJVSXQVSVJVJAFZCGZFZXQVSXRVJCFZGZXTVPXRVRYAVPWDDFZXRVLWDDABJKB
      ADHLBCDHIYBYAXRGZVJCXRGZFZXTXRYAMYFYDVJCANOYEXSVJCXRMUAPUEVJXQXSVJXPUBXSD
      CGZXQXSYCCGZYGXRYCCBDAHQYHYCXMCGZGZXNDFZCGZYGCYIYCCYICXMCCDUBCUFRXMCUGSUP
      YJYCXMGZCGZYLYNYJYCXMCUHOYMYKCYMDWDFZXMGZDXNFZYKYCYOXMWDDUCQYQYPDWDCNODXN
      JPQLYKDCYKTDFDXNTDXOKDUILQPLYGVJXPDCBUJUKULUMULXQVPVRXPVPVJXPVLDACBUNZUQB
      VLDBAUBZUOUMXPVRVJXPVQDCABUJUQBVQDBCURUOUMRSXQTVJFVJXPTVJXPTXPXCTXPVLWTYR
      CADUSREUTXPVASKVJUILLIOVTVSVOGZWBVLFZWTWAFZGZWCVOVSMYTVPVMGZVRVNGZGUUCVPV
      RVMVNVBUUDUUAUUEUUBUUDVLWSFZWSVLFUUAUUDVMVPGZUUFVPVMMUUGUUDVLDVMGZFZUUFVM
      VPMUUIUUDVLDCNOUUHWSVLDVMMUAPUEVLWSJWSWBVLXKKPUUEWTBFZWTAFZGZWAWTFZUUBVRU
      UJVNUUKVRBWTFUUJBCDVCBWTJLVNCAFZDFUUKVIUUNDACUCKCADHLIUULWTUUKBGZFZUUOWTF
      UUMUULUUKUUJGZUUPUUJUUKMUUQUULWTBUUKGZFZUUPUUKUUJMUUSUULWTBANOUURUUOWTBUU
      KMUAPUEWTUUOJUUOWAWTUUOUUKVLBGZGZWTVLGZAFZBGZWABUUTUUKBUUTBVLBYSBUFRVLBUG
      SUPUVAUUKVLGZBGZUVDUVFUVAUUKVLBUHOUVEUVCBUVEAWTFZVLGZAUVBFZUVCUUKUVGVLWTA
      UCQUVIUVHAWTBNOAUVBJPQLUVCABUVCTAFAUVBTAUVBXCTWTVLMELKAUILQPKPWAWTJPILUUC
      WBWAFZWCUUCWBVLUUBGZFZUVJUUAWBUUBFZGZWBVLUVMGZFZUUCUVLUVPUVNWBVLUUBNOUVMU
      UBUUAUVMWBWTFZWAFZUUBUVRUVMWBWTWAVDOUVQWTWAWBWTCDDUSVEKLZUPUVOUVKWBUVMUUB
      VLUVSUPUAVFUVKWAWBUVKVLWTVLWAGZFZGXCUVTFZWAUUBUWAVLWAUVTWTWAUVTWAVLWAABBU
      SWAUFRZVLWAUGZSUAUPVLWTWAVGUWBTWAFWAXCTUVTWAEUVTWAUWDUWCSVHWAUILPUALWBWAJ
      LPL $.
  $}

  $( Lemma for ~ l42mod ..  (Contributed by NM, 8-Apr-2012.) $)
  l42modlem1 $p |- ( ( ( a v b ) v d ) ^ ( ( a v b ) v e ) ) =
                              ( ( a v b ) v ( ( a v d ) ^ ( b v e ) ) ) $=
    ( wo wa leo ml2i ancom tr lor cm orass or12 2an lerr 3tr 3tr1 ) ABDEZBACEZE
    ZFZEZABTSFZEZEZABEZCEZUGDEZFZUGUDEUFUCUEUBAUEUASFUBSTBBDGHUASIJKLUJUAASEZFU
    KUAFZUCUHUAUIUKUHABCEEUAABCMABCNJABDMOUAUKIUCULUASAATBACGPHLQABUDMR $.

  $( Lemma for ~ l42mod ..  (Contributed by NM, 8-Apr-2012.) $)
  l42modlem2 $p |- ( ( ( ( a v b ) ^ c ) v d ) ^ e ) =<
         ( ( ( a v b ) v d ) ^ ( ( a v b ) v e ) ) $=
    ( wo wa lea leror leor le2an ) ABFZCGZDFLDFELEFMLDLCHIELJK $.

  $( An equation that fails in OML L42 when converted to a Hilbert space
     equation.  (Contributed by NM, 8-Apr-2012.) $)
  l42mod $p |- ( ( ( ( a v b ) ^ c ) v d ) ^ e )
               =< ( ( a v b ) v ( ( a v d ) ^ ( b v e ) ) ) $=
    ( wo wa l42modlem2 l42modlem1 lbtr ) ABFZCGDFEGKDFKEFGKADFBEFGFABCDEHABDEIJ
    $.

  $( Expansion by modular law.  (Contributed by NM, 10-Apr-2012.) $)
  modexp $p |- ( a ^ ( b v c ) ) = ( a ^ ( b v ( c ^ ( a v b ) ) ) ) $=
    ( wo wa anass anabs ran ancom leor mlduali tr lan 3tr2 ) AABDZEZBCDZEAOQEZE
    AQEABCOEDZEAOQFPAQABGHRSARQOESOQIBCOBAJKLMN $.

  $( Experimental expansion of l42mod.
  l42modexp $p |- ( ( ( a v b ) v d ) ^ ( ( a v b ) v e ) ) =
                              ( ( a v b ) v ( ( a v d ) ^ ( b v e ) ) ) $=
    ( l42modlem1 modexp id tr lor lan cm ) ???????E???????????????FZ?????????L?
    ????????L?????????L?????????L?????????L?????????L?????????L?GHIJHIJHIJHIJHI
    JHIJHIJHIKHH $.
  $)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Arguesian law
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    arg.1 $e |- ( ( a0 v b0 ) ^ ( a1 v b1 ) ) =< ( a2 v b2 ) $.
    $( The Arguesian law as an axiom.  (Contributed by NM, 1-Apr-2012.) $)
    ax-arg $a |- ( ( a0 v a1 ) ^ ( b0 v b1 ) )
       =< ( ( ( a0 v a2 ) ^ ( b0 v b2 ) ) v ( ( a1 v a2 ) ^ ( b1 v b2 ) ) ) $.
  $}

  ${
    dp15lema.1 $e |- d = ( a2 v ( a0 ^ ( a1 v b1 ) ) ) $.
    dp15lema.2 $e |- p0 = ( ( a1 v b1 ) ^ ( a2 v b2 ) ) $.
    dp15lema.3 $e |- e = ( b0 ^ ( a0 v p0 ) ) $.
    $( Part of proof (1)=>(5) in Day/Pickering 1982.  (Contributed by NM,
       1-Apr-2012.) $)
    dp15lema $p |- ( ( a0 v e ) ^ ( a1 v b1 ) ) =< ( d v b2 ) $=
      ( wo wa lor tr ran wt leran cm lan le1 lelor an1r orass oridm ror 3tr lea
      orcom mlduali lear leror bltr or32 lbtr letr ) CBMZDGMZNCFCUSEHMZNZMZNZMZ
      USNZAHMZURVDUSBVCCBFCIMZNVCLVGVBFIVACKOUAPOQVECRVBNZMZUSNZVFVDVIUSVCVHCFR
      VBFUBSUCSVJUTCUSNZMZVFVJVAVKMZVLVJVACMZUSNVMVIVNUSVICVBMZCCMZVAMZVNVHVBCV
      BUDOVQVOCCVAUETVQVBVNVPCVACUFUGCVAUJPUHQVACUSUSUTUIUKPVAUTVKUSUTULUMUNVLE
      VKMZHMZVFEHVKUOVFVSAVRHJUGTPUPUQUN $.

    $( Part of proof (1)=>(5) in Day/Pickering 1982.  (Contributed by NM,
       1-Apr-2012.) $)
    dp15lemb $p |- ( ( a0 v a1 ) ^ ( e v b1 ) )
          =< ( ( ( a0 v d ) ^ ( e v b2 ) ) v ( ( a1 v d ) ^ ( b1 v b2 ) ) ) $=
      ( dp15lema ax-arg ) CDABGHABCDEFGHIJKLMN $.

    $( Part of proof (1)=>(5) in Day/Pickering 1982.  (Contributed by NM,
       10-Apr-2012.) $)
    dp15lemc $p |- ( ( a0 v a1 ) ^ ( ( b0 ^ ( a0 v p0 ) ) v b1 ) )
          =< ( ( ( a0 v ( a2 v ( a0 ^ ( a1 v b1 ) ) ) )
               ^ ( ( b0 ^ ( a0 v p0 ) ) v b2 ) )
         v ( ( a1 v ( a2 v ( a0 ^ ( a1 v b1 ) ) ) ) ^ ( b1 v b2 ) ) ) $=
      ( wo wa dp15lemb ror lan lor 2an ran 2or le3tr2 ) CDMZBGMZNCAMZBHMZNZDAMZ
      GHMZNZMUCFCIMNZGMZNCECDGMNMZMZUKHMZNZDUMMZUINZMABCDEFGHIJKLOUDULUCBUKGLPQ
      UGUPUJURUEUNUFUOAUMCJRBUKHLPSUHUQUIAUMDJRTUAUB $.

    $( Part of proof (1)=>(5) in Day/Pickering 1982.  (Contributed by NM,
       1-Apr-2012.) $)
    dp15lemd $p |- ( ( ( a0 v ( a2 v ( a0 ^ ( a1 v b1 ) ) ) )
               ^ ( ( b0 ^ ( a0 v p0 ) ) v b2 ) )
         v ( ( a1 v ( a2 v ( a0 ^ ( a1 v b1 ) ) ) ) ^ ( b1 v b2 ) ) )
          = ( ( ( a0 v a2 )
               ^ ( ( b0 ^ ( a0 v p0 ) ) v b2 ) )
         v ( ( ( a1 v a2 ) v ( a0 ^ ( a1 v b1 ) ) ) ^ ( b1 v b2 ) ) ) $=
      ( wo wa or12 orabs lor orcom 3tr ran orass cm 2or ) CECDGMZNZMZMZFCIMNHMZ
      NCEMZUHNDUFMZGHMZNZDEMUEMZUKNZUGUIUHUGECUEMZMECMUICEUEOUOCECUDPQECRSTUNUL
      UMUJUKDEUEUATUBUC $.

    $( Part of proof (1)=>(5) in Day/Pickering 1982.  (Contributed by NM,
       1-Apr-2012.) $)
    dp15leme $p |- ( ( ( a0 v a2 )
               ^ ( ( b0 ^ ( a0 v p0 ) ) v b2 ) )
         v ( ( ( a1 v a2 ) v ( a0 ^ ( a1 v b1 ) ) ) ^ ( b1 v b2 ) ) )
          =< ( ( ( a0 v a2 )
               ^ ( ( b0 ^ ( a0 v p0 ) ) v b2 ) )
         v ( ( ( a1 v a2 ) v ( b1 ^ ( a0 v a1 ) ) ) ^ ( b1 v b2 ) ) ) $=
      ( wo wa ax-a2 lan 2or orass tr lelor ml3le bltr cm ror lbtr leran ) DEMZC
      DGMZNZMZGHMZNUGGCDMNZMZUKNCEMFCIMNHMNUJUMUKUJEDULMZMZUMUJEDCGDMZNZMZMZUOU
      JEDMZUQMUSUGUTUIUQDEOUHUPCDGOPQEDUQRSURUNEDCGUATUBUOUTULMZUMVAUOEDULRUCUT
      UGULEDOUDSUEUFT $.

    $( Part of proof (1)=>(5) in Day/Pickering 1982.  (Contributed by NM,
       1-Apr-2012.) $)
    dp15lemf $p |- ( ( ( a0 v a2 )
               ^ ( ( b0 ^ ( a0 v p0 ) ) v b2 ) )
         v ( ( ( a1 v a2 ) v ( b1 ^ ( a0 v a1 ) ) ) ^ ( b1 v b2 ) ) )
      =< ( ( ( a1 v a2 )
               ^ ( b1 v b2 ) )
         v ( ( ( a0 v a2 ) ^ ( b0 v b2 ) ) v ( b1 ^ ( a0 v a1 ) ) ) ) $=
      ( wo wa lea leror lelan leao1 mldual2i ancom 3tr2 bile le2or or12 lbtr
      ror ) CEMZFCIMZNZHMZNZDEMZGCDMZNZMZGHMZNZMUGFHMZNZULUPNZUNMZMUTUSUNMMUKUS
      UQVAUJURUGUIFHFUHOPQUQVAUPUONUPULNZUNMUQVAUNULUPGUMHRSUPUOTVBUTUNUPULTUFU
      AUBUCUSUTUNUDUE $.

    dp15lemg.4 $e |- c0 = ( ( a1 v a2 ) ^ ( b1 v b2 ) ) $.
    dp15lemg.5 $e |- c1 = ( ( a0 v a2 ) ^ ( b0 v b2 ) ) $.
    $( Part of proof (1)=>(5) in Day/Pickering 1982.  (Contributed by NM,
       1-Apr-2012.) $)
    dp15lemg $p |- ( ( ( a1 v a2 )
               ^ ( b1 v b2 ) )
         v ( ( ( a0 v a2 ) ^ ( b0 v b2 ) ) v ( b1 ^ ( a0 v a1 ) ) ) )
      = ( ( c0 v c1 ) v ( b1 ^ ( a0 v a1 ) ) ) $=
      ( wo wa ror cm 2or orass tr ) DEQGHQRZCEQFHQRZGCDQRZQZQZIJUFQZQZIJQUFQZUJ
      UHIUDUIUGOJUEUFPSUATUKUJIJUFUBTUC $.

    $( Part of proof (1)=>(5) in Day/Pickering 1982.  (Contributed by NM,
       2-Apr-2012.) $)
    dp15lemh $p |- ( ( a0 v a1 ) ^ ( ( b0 ^ ( a0 v p0 ) ) v b1 ) )
                  =< ( ( c0 v c1 ) v ( b1 ^ ( a0 v a1 ) ) ) $=
      ( wo wa lbtr letr dp15lemc dp15lemd dp15leme dp15lemf dp15lemg ) CDQZFCKQ
      RZGQRZDEQZGHQZRCEQZFHQRGUFRZQQZIJQULQUHUKUGHQZRZUIULQUJRQZUMUHUOUICDGQRZQ
      UJRQZUPUHCEUQQZQUNRDUSQUJRQURABCDEFGHKLMNUAABCDEFGHKLMNUBSABCDEFGHKLMNUCT
      ABCDEFGHKLMNUDTABCDEFGHIJKLMNOPUES $.
  $}

  ${
    dp15.1 $e |- c0 = ( ( a1 v a2 ) ^ ( b1 v b2 ) ) $.
    dp15.2 $e |- c1 = ( ( a0 v a2 ) ^ ( b0 v b2 ) ) $.
    dp15.3 $e |- p0 = ( ( a1 v b1 ) ^ ( a2 v b2 ) ) $.
    $( Part of theorem from Alan Day and Doug Pickering, "A note on the
       Arguesian lattice identity," Studia Sci.  Math.  Hungar. 19:303-305
       (1982).  (1)=>(5) (Contributed by NM, 1-Apr-2012.) $)
    dp15 $p |- ( ( a0 v a1 ) ^ ( ( b0 ^ ( a0 v p0 ) ) v b1 ) )
                  =< ( ( c0 v c1 ) v ( b1 ^ ( a0 v a1 ) ) ) $=
      ( wo wa id dp15lemh ) CABEMNMZDAIMNZABCDEFGHIQOLROJKP $.
  $}

  ${
    dp53lem.1 $e |- c0 = ( ( a1 v a2 ) ^ ( b1 v b2 ) ) $.
    dp53lem.2 $e |- c1 = ( ( a0 v a2 ) ^ ( b0 v b2 ) ) $.
    dp53lem.3 $e |- c2 = ( ( a0 v a1 ) ^ ( b0 v b1 ) ) $.
    dp53lem.4 $e |- p0 = ( ( a1 v b1 ) ^ ( a2 v b2 ) ) $.
    dp53lem.5 $e |- p = ( ( ( a0 v b0 ) ^ ( a1 v b1 ) ) ^ ( a2 v b2 ) ) $.
    $( Part of proof (5)=>(3) in Day/Pickering 1982.  (Contributed by NM,
       2-Apr-2012.) $)
    dp53lema $p |- ( b1 v ( b0 ^ ( a0 v p0 ) ) )
       =< ( b1 v ( ( a0 v a1 ) ^ ( c0 v c1 ) ) ) $=
      ( wo wa lbtr letr leo lor lan lear lea lelor cm bltr ler2an leor mldual2i
      ax-a3 ancom ror tr dp15 orcom leid lel2or ) FFBCQZHIQZRZQZEBKQZRZFVBUAZVE
      UTVEFQZRZVCQZVCVEVHFQZVIVEVGUTFQZRZVJVEVGVKVEFUAVEEBCFQZDGQZRZQZRZVKVDVPE
      KVOBOUBUCVQVPVKEVPUDVPBVMQZVKVOVMBVMVNUEUFVKVRBCFULUGSTUHUIVLVGUTRZFQVJFU
      TVGFVEUJUKVSVHFVGUTUMUNUOSFVCVHVFUFTVHVCVCVHVBFQZVCVHVBFUTRZQZVTVHUTVAWAQ
      ZRWBVHUTWCUTVGUEBCDEFGHIKLMOUPUIWAVAUTFUTUDUKSWAFVBFUTUEUFTVBFUQSVCURUSTU
      S $.

    $( Part of proof (5)=>(3) in Day/Pickering 1982.  (Contributed by NM,
       2-Apr-2012.) $)
    dp53lemb $p |- ( b0 ^ ( b1 v ( c2 ^ ( c0 v c1 ) ) ) )
        = ( b0 ^ ( b1 v ( ( a0 v a1 ) ^ ( c0 v c1 ) ) ) ) $=
      ( wo wa ran 3tr an32 tr lor leor ml2i ancom lan anass cm anabs ) EFJHIQZR
      ZQZREEFQZFBCQZUKRZQZRZRZEUNRZUQRZEUQRUMUREUMFUPUNRZQUQUNRURULVBFULUOUNRZU
      KRVBJVCUKNSUOUNUKUAUBUCUNUPFFEUDUEUQUNUFTUGVAUSEUNUQUHUIUTEUQEFUJST $.

    $( Part of proof (5)=>(3) in Day/Pickering 1982.  (Contributed by NM,
       2-Apr-2012.) $)
    dp53lemc $p |- ( b0 ^ ( ( ( a0 ^ b0 ) v b1 ) v ( c2 ^ ( c0 v c1 ) ) ) )
        = ( b0 ^ ( b1 v ( c2 ^ ( c0 v c1 ) ) ) ) $=
      ( wa wo leo le2an or32 orcom cm lbtr lerr ler2an df-le2 lor 3tr lan ) BEQ
      ZFRJHIRZQZRZFUMRZEUNUKUMRZFRFUPRUOUKFUMUAUPFUBUPUMFUKUMUKJULUKBCRZEFRZQZJ
      BUQEURBCSEFSTJUSNUCUDUKIHUKBDRZEGRZQZIBUTEVABDSEGSTIVBMUCUDUEUFUGUHUIUJ
      $.

    $( Part of proof (5)=>(3) in Day/Pickering 1982.  (Contributed by NM,
       3-Apr-2012.) $)
    dp53lemd $p |- ( b0 ^ ( a0 v p0 ) )
        =< ( b0 ^ ( ( ( a0 ^ b0 ) v b1 ) v ( c2 ^ ( c0 v c1 ) ) ) ) $=
      ( wo wa lea leor dp53lema letr ler2an dp53lemc dp53lemb tr cm lbtr ) EBKQ
      ZRZEFBCQHIQZRQZRZEBERFQJUKRZQRZUJEULEUISUJFUJQULUJFTABCDEFGHIJKLMNOPUAUBU
      CUOUMUOEFUNQRUMABCDEFGHIJKLMNOPUDABCDEFGHIJKLMNOPUEUFUGUH $.

    $( Part of proof (5)=>(3) in Day/Pickering 1982.  (Contributed by NM,
       3-Apr-2012.) $)
    dp53leme $p |- ( b0 ^ ( a0 v p0 ) )
        =< ( a0 v ( b0 ^ ( b1 v ( c2 ^ ( c0 v c1 ) ) ) ) ) $=
      ( wo wa dp53lemd orcom orass tr lan lear mldual2i 3tr lea leror bltr letr
      ) EBKQREBERZFQJHIQRZQZRZBEFULQZRZQZABCDEFGHIJKLMNOPSUNUKUPQZUQUNEUOUKQZRU
      PUKQURUMUSEUMUKUOQUSUKFULUAUKUOTUBUCUKUOEBEUDUEUPUKTUFUKBUPBEUGUHUIUJ $.

    $( Part of proof (5)=>(3) in Day/Pickering 1982.  (Contributed by NM,
       3-Apr-2012.) $)
    dp53lemf $p |- ( a0 v p )
        =< ( a0 v ( b0 ^ ( b1 v ( c2 ^ ( c0 v c1 ) ) ) ) ) $=
      ( wo wa leo lbtr anass tr lan cm leao4 bltr lea orcom ler2an mldual2i ror
      ancom lelor letr dp53leme df-le2 lel2or ) BBEFJHIQRQRZQZABURSZAEBKQZRZUSQ
      ZUSAVBBQZVCAVAEBQZRZVDABEQZCFQZDGQZRZRZVFAVGVHRVIRVKPVGVHVIUAUBVKVAVEVKVG
      KRZVAVLVKKVJVGOUCUDKVGBUEUFVKVGVEVGVJUGBEUHTUIUFVFVAERZBQVDBEVABKSUJVMVBB
      VAEULUKUBTBUSVBUTUMUNVBUSABCDEFGHIJKLMNOPUOUPTUQ $.

    $( Part of proof (5)=>(3) in Day/Pickering 1982.  (Contributed by NM,
       2-Apr-2012.) $)
    dp53lemg $p |- p
        =< ( a0 v ( b0 ^ ( b1 v ( c2 ^ ( c0 v c1 ) ) ) ) ) $=
      ( wo wa leor dp53lemf letr ) ABAQBEFJHIQRQRQABSABCDEFGHIJKLMNOPTUA $.
  $}

  ${
    dp53.1 $e |- c0 = ( ( a1 v a2 ) ^ ( b1 v b2 ) ) $.
    dp53.2 $e |- c1 = ( ( a0 v a2 ) ^ ( b0 v b2 ) ) $.
    dp53.3 $e |- c2 = ( ( a0 v a1 ) ^ ( b0 v b1 ) ) $.
    dp53.4 $e |- p = ( ( ( a0 v b0 ) ^ ( a1 v b1 ) ) ^ ( a2 v b2 ) ) $.
    $( Part of theorem from Alan Day and Doug Pickering, "A note on the
       Arguesian lattice identity," Studia Sci.  Math.  Hungar. 19:303-305
       (1982).  (5)=>(3) (Contributed by NM, 2-Apr-2012.) $)
    dp53 $p |- p =< ( a0 v ( b0 ^ ( b1 v ( c2 ^ ( c0 v c1 ) ) ) ) ) $=
      ( wo wa id dp53lemg ) ABCDEFGHIJCFODGOPZKLMSQNR $.
  $}

  ${
    dp35lem.1 $e |- c0 = ( ( a1 v a2 ) ^ ( b1 v b2 ) ) $.
    dp35lem.2 $e |- c1 = ( ( a0 v a2 ) ^ ( b0 v b2 ) ) $.
    dp35lem.3 $e |- c2 = ( ( a0 v a1 ) ^ ( b0 v b1 ) ) $.
    dp35lem.4 $e |- p0 = ( ( a1 v b1 ) ^ ( a2 v b2 ) ) $.
    dp35lem.5 $e |- p = ( ( ( a0 v b0 ) ^ ( a1 v b1 ) ) ^ ( a2 v b2 ) ) $.
    $( Part of proof (3)=>(5) in Day/Pickering 1982.  (Contributed by NM,
       12-Apr-2012.) $)
    dp35lemg $p |- p
        =< ( a0 v ( b0 ^ ( b1 v ( c2 ^ ( c0 v c1 ) ) ) ) ) $=
      ( dp53 ) ABCDEFGHIJLMNPQ $.

    $( Part of proof (3)=>(5) in Day/Pickering 1982.  (Contributed by NM,
       12-Apr-2012.) $)
    dp35lemf $p |- ( a0 v p )
        =< ( a0 v ( b0 ^ ( b1 v ( c2 ^ ( c0 v c1 ) ) ) ) ) $=
      ( wo wa leo dp35lemg lel2or ) BBEFJHIQRQRZQABUBSABCDEFGHIJKLMNOPTUA $.

    $( Part of proof (3)=>(5) in Day/Pickering 1982.  (Contributed by NM,
       12-Apr-2012.) $)
    dp35leme $p |- ( b0 ^ ( a0 v p0 ) )
        =< ( a0 v ( b0 ^ ( b1 v ( c2 ^ ( c0 v c1 ) ) ) ) ) $=
      ( wo wa lor ancom leor bile le2an anass cm leo mlduali 3tr1 dp35lemf bltr
      tr letr ) EBKQZRBEQZBCFQZDGQZRZQZRZBEFJHIQRQRQZEUNUMUREBUAUMURKUQBOSUBUCU
      SBAQZUTBUQUNRZQZBUNUORUPRZQUSVAVBVDBVBUNUQRZVDUQUNTVDVEUNUOUPUDUEUKSUSURU
      NRVCUNURTBUQUNBEUFUGUKAVDBPSUHABCDEFGHIJKLMNOPUIUJUL $.

    $( Part of proof (3)=>(5) in Day/Pickering 1982.  (Contributed by NM,
       12-Apr-2012.) $)
    dp35lemd $p |- ( b0 ^ ( a0 v p0 ) )
        =< ( b0 ^ ( ( ( a0 ^ b0 ) v b1 ) v ( c2 ^ ( c0 v c1 ) ) ) ) $=
      ( wo wa lea ler2an dp35leme mldual2i lel2or ancom bile lear le2or cm lbtr
      orass bltr letr ) EBKQZRZEBEFJHIQRZQZRZQZRZEBERZFQUOQZRZUNEUREUMSABCDEFGH
      IJKLMNOPUATUSEBRZUQQZVBUQBEEUPSZUBVDEVAVCEUQEBSVEUCVDUTUPQZVAVCUTUQUPVCUT
      EBUDUEEUPUFUGVAVFUTFUOUJUHUITUKUL $.

    $( Part of proof (3)=>(5) in Day/Pickering 1982.  (Contributed by NM,
       2-Apr-2012.) $)
    dp35lemc $p |- ( b0 ^ ( ( ( a0 ^ b0 ) v b1 ) v ( c2 ^ ( c0 v c1 ) ) ) )
        = ( b0 ^ ( b1 v ( c2 ^ ( c0 v c1 ) ) ) ) $=
      ( wa wo leo le2an or32 orcom cm lbtr lerr ler2an df-le2 lor 3tr lan ) BEQ
      ZFRJHIRZQZRZFUMRZEUNUKUMRZFRFUPRUOUKFUMUAUPFUBUPUMFUKUMUKJULUKBCRZEFRZQZJ
      BUQEURBCSEFSTJUSNUCUDUKIHUKBDRZEGRZQZIBUTEVABDSEGSTIVBMUCUDUEUFUGUHUIUJ
      $.

    $( Part of proof (3)=>(5) in Day/Pickering 1982.  (Contributed by NM,
       2-Apr-2012.) $)
    dp35lemb $p |- ( b0 ^ ( b1 v ( c2 ^ ( c0 v c1 ) ) ) )
        = ( b0 ^ ( b1 v ( ( a0 v a1 ) ^ ( c0 v c1 ) ) ) ) $=
      ( wo wa ran 3tr an32 tr lor leor ml2i ancom lan anass cm anabs ) EFJHIQZR
      ZQZREEFQZFBCQZUKRZQZRZRZEUNRZUQRZEUQRUMUREUMFUPUNRZQUQUNRURULVBFULUOUNRZU
      KRVBJVCUKNSUOUNUKUAUBUCUNUPFFEUDUEUQUNUFTUGVAUSEUNUQUHUIUTEUQEFUJST $.

    $( Part of proof (3)=>(5) in Day/Pickering 1982.  (Contributed by NM,
       12-Apr-2012.) $)
    dp35lembb $p |- ( b0 ^ ( a0 v p0 ) )
        =< ( b0 ^ ( b1 v ( ( a0 v a1 ) ^ ( c0 v c1 ) ) ) ) $=
      ( wo wa dp35lemd dp35lemc dp35lemb tr lbtr ) EBKQREBERFQJHIQZRZQRZEFBCQUD
      RQRZABCDEFGHIJKLMNOPSUFEFUEQRUGABCDEFGHIJKLMNOPTABCDEFGHIJKLMNOPUAUBUC $.

    $( Part of proof (3)=>(5) in Day/Pickering 1982.  (Contributed by NM,
       12-Apr-2012.) $)
    dp35lema $p |- ( b1 v ( b0 ^ ( a0 v p0 ) ) )
       =< ( b1 v ( ( a0 v a1 ) ^ ( c0 v c1 ) ) ) $=
      ( wo wa leo dp35lembb lear letr lel2or ) FFBCQHIQRZQZEBKQRZFUDSUFEUERUEAB
      CDEFGHIJKLMNOPTEUEUAUBUC $.

    $( Part of proof (3)=>(5) in Day/Pickering 1982.  (Contributed by NM,
       12-Apr-2012.) $)
    dp35lem0 $p |- ( ( a0 v a1 ) ^ ( ( b0 ^ ( a0 v p0 ) ) v b1 ) )
                  =< ( ( c0 v c1 ) v ( b1 ^ ( a0 v a1 ) ) ) $=
      ( wo wa orcom letr leid bltr dp35lema lelan id lea mldual2i tr ancom lbtr
      ror lear lelor ) BCQZEBKQRZFQZRZFUNRZUNHIQZRZQZUSURQZUQUNFUTQZRZVAUPVCUNU
      PFUOQZVCUPVEVEUOFSVEUAUBABCDEFGHIJKLMNOPUCTUDVDUNFRZUTQZVAVDVDVGVDUEUTFUN
      UNUSUFUGUHVFURUTUNFUIUKUHUJVAURUSQVBUTUSURUNUSULUMURUSSUJT $.
  $}

  ${
    dp35.1 $e |- c0 = ( ( a1 v a2 ) ^ ( b1 v b2 ) ) $.
    dp35.2 $e |- c1 = ( ( a0 v a2 ) ^ ( b0 v b2 ) ) $.
    dp35.3 $e |- p0 = ( ( a1 v b1 ) ^ ( a2 v b2 ) ) $.
    $( Part of theorem from Alan Day and Doug Pickering, "A note on the
       Arguesian lattice identity," Studia Sci.  Math.  Hungar. 19:303-305
       (1982).  (3)=>(5) (Contributed by NM, 12-Apr-2012.) $)
    dp35 $p |- ( ( a0 v a1 ) ^ ( ( b0 ^ ( a0 v p0 ) ) v b1 ) )
                  =< ( ( c0 v c1 ) v ( b1 ^ ( a0 v a1 ) ) ) $=
      ( wo wa id dp35lem0 ) ADMBEMNCFMNZABCDEFGHABMDEMNZIJKROLQOP $.
  $}

  ${
    dp34.1 $e |- c0 = ( ( a1 v a2 ) ^ ( b1 v b2 ) ) $.
    dp34.2 $e |- c1 = ( ( a0 v a2 ) ^ ( b0 v b2 ) ) $.
    dp34.3 $e |- c2 = ( ( a0 v a1 ) ^ ( b0 v b1 ) ) $.
    dp34.4 $e |- p = ( ( ( a0 v b0 ) ^ ( a1 v b1 ) ) ^ ( a2 v b2 ) ) $.
    $( Part of theorem from Alan Day and Doug Pickering, "A note on the
       Arguesian lattice identity," Studia Sci.  Math.  Hungar. 19:303-305
       (1982).  (3)=>(4) (Contributed by NM, 3-Apr-2012.) $)
    dp34 $p |- p =< ( ( a0 v b1 ) v ( c2 ^ ( c0 v c1 ) ) ) $=
      ( wo wa dp53 lear lelor letr orass cm lbtr ) ABFJHIOPZOZOZBFOUDOZABEUEPZO
      UFABCDEFGHIJKLMNQUHUEBEUERSTUGUFBFUDUAUBUC $.
  $}

  ${
    dp41lem.1 $e |- c0 = ( ( a1 v a2 ) ^ ( b1 v b2 ) ) $.
    dp41lem.2 $e |- c1 = ( ( a0 v a2 ) ^ ( b0 v b2 ) ) $.
    dp41lem.3 $e |- c2 = ( ( a0 v a1 ) ^ ( b0 v b1 ) ) $.
    dp41lem.4 $e |- p = ( ( ( a0 v b0 ) ^ ( a1 v b1 ) ) ^ ( a2 v b2 ) ) $.
    dp41lem.5 $e |- p2 = ( ( a0 v b0 ) ^ ( a1 v b1 ) ) $.
    dp41lem.6 $e |- p2 =< ( a2 v b2 ) $.
    $( Part of proof (4)=>(1) in Day/Pickering 1982.  (Contributed by NM,
       3-Apr-2012.) $)
    dp41lema $p |- ( ( a0 v b0 ) ^ ( a1 v b1 ) )
         =< ( ( a0 v b1 ) v ( c2 ^ ( c0 v c1 ) ) ) $=
      ( wo wa cm bltr df2le2 tr dp34 ) BERCFRSZABFRJHIRSRUEUEDGRZSZAUGUEUEUFUEK
      UFKUEPTQUAUBTAUGOTUCABCDEFGHIJLMNOUDUA $.

    $( Part of proof (4)=>(1) in Day/Pickering 1982.  (Contributed by NM,
       3-Apr-2012.) $)
    dp41lemb $p |- c2
          = ( ( c2 ^ ( ( a0 v b0 ) v b1 ) ) ^ ( ( a0 v a1 ) v b1 ) ) $=
      ( wo wa tr ancom leor leror leo le2an bltr df2le2 cm anass ) JJBERZFRZBCR
      ZFRZSZSZJUKSUMSZUOJJUNJEFRZULSZUNJULUQSURNULUQUATUQUKULUMEUJFEBUBUCULFUDU
      EUFUGUHUPUOJUKUMUIUHT $.

    $( Part of proof (4)=>(1) in Day/Pickering 1982.  (Contributed by NM,
       4-Apr-2012.) $)
    dp41lemc0 $p |- ( ( ( a0 v b0 ) v b1 ) ^ ( ( a0 v a1 ) v b1 ) )
          = ( ( a0 v b1 ) v ( ( a0 v b0 ) ^ ( a1 v b1 ) ) ) $=
      ( wo wa tr ax-a2 ror or32 lan ancom leor ler mldual2i leo 3tr orass orcom
      ) BERZFRZBCRZFRZSZUMCFRZSZBRZFRZUSBFRZRVBUSRUQURBRZUNSZVCUMSZFRVAUQUNVCSV
      DUPVCUNUPCBRZFRVCUOVFFBCUAUBCBFUCTUDUNVCUETFUMVCFURBFCUFUGUHVEUTFVEUMVCSU
      TVCUMUEBURUMBEUIUHTUBUJUSBFUKUSVBULUJ $.

    $( Part of proof (4)=>(1) in Day/Pickering 1982.  (Contributed by NM,
       3-Apr-2012.) $)
    dp41lemc $p |- ( ( c2 ^ ( ( a0 v b0 ) v b1 ) ) ^ ( ( a0 v a1 ) v b1 ) )
          =< ( c2 ^ ( ( a0 v b1 ) v ( c2 ^ ( c0 v c1 ) ) ) ) $=
      ( wo wa bltr anass dp41lemc0 leo dp41lema lel2or lelan ) JBERZFRZSBCRFRZS
      JUHUISZSJBFRZJHIRSZRZSJUHUIUAUJUMJUJUKUGCFRSZRUMABCDEFGHIJKLMNOPQUBUKUMUN
      UKULUCABCDEFGHIJKLMNOPQUDUETUFT $.

    $( Part of proof (4)=>(1) in Day/Pickering 1982.  (Contributed by NM,
       3-Apr-2012.) $)
    dp41lemd $p |- ( c2 ^ ( ( a0 v b1 ) v ( c2 ^ ( c0 v c1 ) ) ) )
          = ( c2 ^ ( ( c0 v c1 ) v ( c2 ^ ( a0 v b1 ) ) ) ) $=
      ( wo wa ancom mldual lor lea ml2i ax-a2 lan 3tr ) JBFRZJHIRZSZRSJUHSZUJRU
      KUIJSZRZJUIUKRZSZJUHUIUAUJULUKJUITUBUMUKUIRZJSJUPSUOJUIUKJUHUCUDUPJTUPUNJ
      UKUIUEUFUGUG $.

    $( Part of proof (4)=>(1) in Day/Pickering 1982.  (Contributed by NM,
       3-Apr-2012.) $)
    dp41leme $p |- ( c2 ^ ( ( c0 v c1 ) v ( c2 ^ ( a0 v b1 ) ) ) )
        =< ( ( c0 v c1 ) v ( ( a0 ^ ( b0 v b1 ) ) v ( b1 ^ ( a0 v a1 ) ) ) ) $=
      ( wo wa lor mldual ran anass leor mldual2i orcom ancom 3tr lan leao1 lear
      tr leror bltr ) JHIRZJBFRZSZRSZJUOSZBEFRZSZFBCRZSZRZRZUOVDRURUSUQRVEJUOUP
      UAUQVDUSUQVBUTSZUPSVBUTUPSZSZVDJVFUPNUBVBUTUPUCVHVBFVARZSVBFSZVARZVDVGVIV
      BVGUTBSZFRFVLRVIFBUTFEUDUEVLFUFVLVAFUTBUGTUHUIVAFVBBUTCUJUEVKVAVJRVDVJVAU
      FVJVCVAVBFUGTULUHUHTULUSUOVDJUOUKUMUN $.

    $( Part of proof (4)=>(1) in Day/Pickering 1982.  (Contributed by NM,
       3-Apr-2012.) $)
    dp41lemf $p |- ( ( c0 v c1 ) v
                        ( ( a0 ^ ( b0 v b1 ) ) v ( b1 ^ ( a0 v a1 ) ) ) )
       = ( ( ( b1 v b2 ) ^ ( ( a1 v a2 ) v ( b1 ^ ( a0 v a1 ) ) ) )
                v ( ( a0 v a2 ) ^ ( ( b0 v b2 ) v ( a0 ^ ( b0 v b1 ) ) ) ) ) $=
      ( wo wa tr orcom lor or4 ancom ror 2or leao1 mli 3tr ) HIRZBEFRZSZFBCRZSZ
      RZRUJUNULRZRZFGRZCDRZSZUNRZBDRZEGRZSZULRZRZURUSUNRSZVBVCULRSZRUOUPUJULUNU
      AUBUQHUNRZIULRZRVFHIUNULUCVIVAVJVEHUTUNHUSURSUTLUSURUDTUEIVDULMUEUFTVAVGV
      EVHURUSUNFUMGUGUHVBVCULBUKDUGUHUFUI $.

    $( Part of proof (4)=>(1) in Day/Pickering 1982.  (Contributed by NM,
       3-Apr-2012.) $)
    dp41lemg $p |- ( ( ( b1 v b2 ) ^ ( ( a1 v a2 ) v ( b1 ^ ( a0 v a1 ) ) ) )
                v ( ( a0 v a2 ) ^ ( ( b0 v b2 ) v ( a0 ^ ( b0 v b1 ) ) ) ) )
       = ( ( ( b1 v b2 ) ^ ( ( a1 v a2 ) v ( a0 ^ ( a1 v b1 ) ) ) )
                v ( ( a0 v a2 ) ^ ( ( b0 v b2 ) v ( b1 ^ ( a0 v b0 ) ) ) ) ) $=
      ( wo wa or32 ml3 orcom lan lor tr ror 3tr 2or ) FGRZCDRZFBCRSZRZSUIUJBCFR
      ZSZRZSBDRZEGRZBEFRZSZRZSUPUQFBERSZRZSULUOUIULCUKRZDRCUNRZDRUOCDUKTVCVDDVC
      CBFCRZSZRVDCFBUAVFUNCVEUMBFCUBUCUDUEUFCUNDTUGUCUTVBUPUTEUSRZGREVARZGRVBEG
      USTVGVHGVGEBFERZSZRVHUSVJEURVIBEFUBUCUDEBFUAUEUFEVAGTUGUCUH $.

    $( Part of proof (4)=>(1) in Day/Pickering 1982.  "By CP(a,b)".
       (Contributed by NM, 3-Apr-2012.) $)
    dp41lemh $p |- ( ( ( b1 v b2 ) ^ ( ( a1 v a2 ) v ( a0 ^ ( a1 v b1 ) ) ) )
                v ( ( a0 v a2 ) ^ ( ( b0 v b2 ) v ( b1 ^ ( a0 v b0 ) ) ) ) )
       =< ( ( ( b1 v b2 ) ^ ( ( a1 v a2 ) v ( a0 ^ ( a2 v b2 ) ) ) )
                v ( ( a0 v a2 ) ^ ( ( b0 v b2 ) v ( b1 ^ ( a2 v b2 ) ) ) ) ) $=
      ( wo wa ler2an lea leo leran cm bltr letr lelor lelan lear leao3 le2or )
      FGRZCDRZBCFRZSZRZSULUMBDGRZSZRZSBDRZEGRZFBERZSZRZSUTVAFUQSZRZSUPUSULUOURU
      MUOBUQBUNUAUOVBUNSZUQBVBUNBEUBUCVGKUQKVGPUDQUEZUFTUGUHVDVFUTVCVEVAVCFUQFV
      BUAVCVGUQVCVBUNFVBUIFVBCUJTVHUFTUGUHUK $.

    $( Part of proof (4)=>(1) in Day/Pickering 1982.  (Contributed by NM,
       3-Apr-2012.) $)
    dp41lemj $p |- ( ( ( b1 v b2 ) ^ ( ( a1 v a2 ) v ( a0 ^ ( a2 v b2 ) ) ) )
                v ( ( a0 v a2 ) ^ ( ( b0 v b2 ) v ( b1 ^ ( a2 v b2 ) ) ) ) )
       = ( ( ( b1 v b2 ) ^ ( ( a1 v a2 ) v ( b2 ^ ( a0 v a2 ) ) ) )
                v ( ( a0 v a2 ) ^ ( ( b0 v b2 ) v ( a2 ^ ( b1 v b2 ) ) ) ) ) $=
      ( wo wa orass ax-a2 lan lor ml3 tr 3tr1 2or ) FGRZCDRZBDGRZSZRZSUHUIGBDRZ
      SZRZSUMEGRZFUJSZRZSUMUPDUHSZRZSULUOUHCDUKRZRCDUNRZRULUOVAVBCVADBGDRZSZRVB
      UKVDDUJVCBDGUAUBUCDBGUDUEUCCDUKTCDUNTUFUBURUTUMEGUQRZREGUSRZRURUTVEVFEGFD
      UDUCEGUQTEGUSTUFUBUG $.

    $( Part of proof (4)=>(1) in Day/Pickering 1982.  (Contributed by NM,
       3-Apr-2012.) $)
    dp41lemk $p |- ( ( ( b1 v b2 ) ^ ( ( a1 v a2 ) v ( b2 ^ ( a0 v a2 ) ) ) )
                v ( ( a0 v a2 ) ^ ( ( b0 v b2 ) v ( a2 ^ ( b1 v b2 ) ) ) ) )
       = ( ( c0 v ( b2 ^ ( a0 v a2 ) ) ) v ( c1 v ( a2 ^ ( b1 v b2 ) ) ) ) $=
      ( wo wa tr leao3 mldual2i ancom ror cm 2or ) FGRZCDRZGBDRZSZRSZHUJRZUIEGR
      ZDUGSZRSZIUNRZUKUGUHSZUJRZULUJUHUGGUIFUAUBULURHUQUJHUHUGSUQLUHUGUCTUDUETU
      OUIUMSZUNRZUPUNUMUIDUGBUAUBUPUTIUSUNMUDUETUF $.

    $( Part of proof (4)=>(1) in Day/Pickering 1982.  (Contributed by NM,
       3-Apr-2012.) $)
    dp41leml $p |- ( ( c0 v ( b2 ^ ( a0 v a2 ) ) )
                  v ( c1 v ( a2 ^ ( b1 v b2 ) ) ) )
       = ( c0 v c1 ) $=
      ( wo wa orcom or4 ancom leor lelan bltr leran le2or 2or cm tr lbtr df-le2
      3tr ) HGBDRZSZRIDFGRZSZRRHIRZUOUQRZRUSURRURHUOIUQUAURUSTUSURUSUNEGRZSZCDR
      ZUPSZRZURUOVAUQVCUOUNGSVAGUNUBGUTUNGEUCUDUEDVBUPDCUCUFUGVDIHRZURVEVDIVAHV
      CMLUHUIIHTUJUKULUM $.

    $( Part of proof (4)=>(1) in Day/Pickering 1982.  (Contributed by NM,
       3-Apr-2012.) $)
    dp41lemm $p |- c2 =< ( c0 v c1 ) $=
      ( wo wa lbtr dp41lemb dp41lemc dp41lemd dp41leme dp41lemf dp41lemg tr 3tr
      bltr letr dp41lemh dp41lemj dp41lemk dp41leml ) JFGRZCDRZBDGRZSRSBDRZEGRZ
      FUQSRSRZHIRZJUOUPBCFRSRSURUSFBERZSRSRZUTJVABEFRSZFBCRZSZRRZVCJJVAJBFRZSRS
      ZVGJJVHJVASRSZVIJJVBFRSVEFRSVJABCDEFGHIJKLMNOPQUAABCDEFGHIJKLMNOPQUBUIABC
      DEFGHIJKLMNOPQUCTABCDEFGHIJKLMNOPQUDUJVGUOUPVFRSURUSVDRSRVCABCDEFGHIJKLMN
      OPQUEABCDEFGHIJKLMNOPQUFUGTABCDEFGHIJKLMNOPQUKUJUTUOUPGURSZRSURUSDUOSZRSR
      HVKRIVLRRVAABCDEFGHIJKLMNOPQULABCDEFGHIJKLMNOPQUMABCDEFGHIJKLMNOPQUNUHT
      $.
  $}

  ${
    dp41.1 $e |- c0 = ( ( a1 v a2 ) ^ ( b1 v b2 ) ) $.
    dp41.2 $e |- c1 = ( ( a0 v a2 ) ^ ( b0 v b2 ) ) $.
    dp41.3 $e |- c2 = ( ( a0 v a1 ) ^ ( b0 v b1 ) ) $.
    dp41.4 $e |- p2 = ( ( a0 v b0 ) ^ ( a1 v b1 ) ) $.
    dp41.5 $e |- p2 =< ( a2 v b2 ) $.
    $( Part of theorem from Alan Day and Doug Pickering, "A note on the
       Arguesian lattice identity," Studia Sci.  Math.  Hungar. 19:303-305
       (1982).  (4)=>(1) (Contributed by NM, 3-Apr-2012.) $)
    dp41 $p |- c2 =< ( c0 v c1 ) $=
      ( wo wa id dp41lemm ) ADPBEPQCFPQZABCDEFGHIJKLMTRNOS $.
  $}

  ${
    dp32.1 $e |- c0 = ( ( a1 v a2 ) ^ ( b1 v b2 ) ) $.
    dp32.2 $e |- c1 = ( ( a0 v a2 ) ^ ( b0 v b2 ) ) $.
    dp32.3 $e |- c2 = ( ( a0 v a1 ) ^ ( b0 v b1 ) ) $.
    dp32.4 $e |- p = ( ( ( a0 v b0 ) ^ ( a1 v b1 ) ) ^ ( a2 v b2 ) ) $.
    $( Part of theorem from Alan Day and Doug Pickering, "A note on the
       Arguesian lattice identity," Studia Sci.  Math.  Hungar. 19:303-305
       (1982).  (3)=>(2) (Contributed by NM, 4-Apr-2012.) $)
    dp32 $p |- p =< ( ( a0 ^ ( a1 v ( c2 ^ ( c0 v c1 ) ) ) )
                    v ( b0 ^ ( b1 v ( c2 ^ ( c0 v c1 ) ) ) ) ) $=
      ( wo wa ancom tr orcom ler2an dp53 2an leao1 mldual2i mldual cm lbtr lerr
      leao2 ml2i lea df-le2 ran 3tr ror ) ABEFJHIOZPZOZPZOZEBCUQOZPZOZPZVBUSOZA
      UTVCABCDEFGHIJKLMNUAAEFGBCDHIJHCDOZFGOZPVGVFPKVFVGQRIBDOZEGOZPZVIVHPLVHVI
      QRJBCOZEFOZPZVLVKPMVKVLQRABEOZCFOZPZDGOZPEBOZFCOZPZGDOZPNVPVTVQWAVNVRVOVS
      BESCFSUBDGSUBRUATVDUTEPZVBOUSVBOVEVBEUTBVAUSUCUDWBUSVBWBEUTPEBPZUSOZUSUTE
      QEBURUEWDWCEOZURPUSUREWCWCUQFWCJUPWCVMJWCVKVLBECUIEBFUCTJVMMUFUGWCIHWCVJI
      WCVHVIBEDUIEBGUCTIVJLUFUGUHTUHUJWEEURWCEEBUKULUMRUNUOUSVBSUNUG $.
  $}

  ${
    dp23.1 $e |- c0 = ( ( a1 v a2 ) ^ ( b1 v b2 ) ) $.
    dp23.2 $e |- c1 = ( ( a0 v a2 ) ^ ( b0 v b2 ) ) $.
    dp23.3 $e |- c2 = ( ( a0 v a1 ) ^ ( b0 v b1 ) ) $.
    dp23.4 $e |- p = ( ( ( a0 v b0 ) ^ ( a1 v b1 ) ) ^ ( a2 v b2 ) ) $.
    $( Part of theorem from Alan Day and Doug Pickering, "A note on the
       Arguesian lattice identity," Studia Sci.  Math.  Hungar. 19:303-305
       (1982).  (2)=>(3) (Contributed by NM, 4-Apr-2012.) $)
    dp23 $p |- p =< ( a0 v ( b0 ^ ( b1 v ( c2 ^ ( c0 v c1 ) ) ) ) ) $=
      ( wo wa dp32 lea leror letr ) ABCJHIOPZOZPZEFUAOPZOBUDOABCDEFGHIJKLMNQUCB
      UDBUBRST $.
  $}

  ${
    xdp41.c0 $e |- c0 = ( ( a1 v a2 ) ^ ( b1 v b2 ) ) $.
    xdp41.c1 $e |- c1 = ( ( a0 v a2 ) ^ ( b0 v b2 ) ) $.
    xdp41.c2 $e |- c2 = ( ( a0 v a1 ) ^ ( b0 v b1 ) ) $.
    xdp41.p $e |- p = ( ( ( a0 v b0 ) ^ ( a1 v b1 ) ) ^ ( a2 v b2 ) ) $.
    xdp41.p2 $e |- p2 = ( ( a0 v b0 ) ^ ( a1 v b1 ) ) $.
    xdp41.1 $e |- p2 =< ( a2 v b2 ) $.
    $( Part of proof (4)=>(1) in Day/Pickering 1982.  (Contributed by NM,
       3-Apr-2012.) $)
    xdp41 $p |- c2 =< ( c0 v c1 ) $=
      ( wo wa tr ancom leor leror leo le2an bltr df2le2 cm anass ax-a2 ror or32
      lan ler mldual2i 3tr orass orcom dp34 lel2or mldual lor lea ml2i lbtr ran
      lelan leao1 lear letr or4 2or mli ml3 leran ler2an lelor leao3 le2or 3tr1
      df-le2 ) JFGRZCDRZBDGRZSZRZSZBDRZEGRZFWDSZRZSZRZHIRZJWBWCBCFRZSZRZSZWHWIF
      BERZSZRZSZRZWMJWNBEFRZSZFBCRZSZRZRZXCJJWNJBFRZSZRZSZXIJJXJJWNSZRZSZXMJJWS
      FRZSXFFRZSZXPJJXQXRSZSZXSYAJJXTJXDXFSZXTJXFXDSZYBNXFXDUATXDXQXFXREWSFEBUB
      UCXFFUDUEUFUGUHXSYAJXQXRUIZUHTXSYAXPYDXTXOJXTXJWSWOSZRZXOXTYEBRZFRZYEXJRY
      FXTWOBRZXQSZYIWSSZFRYHXTXQYISYJXRYIXQXRCBRZFRYIXFYLFBCUJUKCBFULTUMXQYIUAT
      FWSYIFWOBFCUBUNUOYKYGFYKWSYISYGYIWSUABWOWSBEUDZUOTUKUPYEBFUQYEXJURUPXJXOY
      EXJXNUDYEAXOYEYEWDSZAYNYEYEWDYEKWDKYEPUHQUFZUGUHAYNOUHTABCDEFGHIJLMNOUSUF
      UTUFVGUFUFXPXKXNRXKWNJSZRZXMJXJWNVAXNYPXKJWNUAVBYQXKWNRZJSJYRSXMJWNXKJXJV
      CVDYRJUAYRXLJXKWNUJUMUPUPVEXMXNXHRZXIXMXNXKRYSJWNXJVAXKXHXNXKYCXJSXFXDXJS
      ZSZXHJYCXJNVFXFXDXJUIUUAXFFXERZSXFFSZXERZXHYTUUBXFYTXDBSZFRFUUERUUBFBXDFE
      UBUOUUEFURUUEXEFXDBUAVBUPUMXEFXFBXDCVHUOUUDXEUUCRXHUUCXEURUUCXGXEXFFUAVBT
      UPUPVBTXNWNXHJWNVIUCUFVJXIWBWCXGRZSZWHWIXERZSZRZXCXIWNXGXERZRZWBWCSZXGRZW
      HWISZXERZRZUUJXHUUKWNXEXGURVBUULHXGRZIXERZRUUQHIXGXEVKUURUUNUUSUUPHUUMXGH
      WCWBSZUUMLWCWBUATZUKIUUOXEMUKVLTUUNUUGUUPUUIWBWCXGFXFGVHVMWHWIXEBXDDVHVMV
      LUPUUGWRUUIXBUUFWQWBUUFCXGRZDRCWPRZDRWQCDXGULUVBUVCDUVBCBFCRZSZRUVCCFBVNU
      VEWPCUVDWOBFCURUMVBTUKCWPDULUPUMUUHXAWHUUHEXERZGREWTRZGRXAEGXEULUVFUVGGUV
      FEBFERZSZRUVGXEUVIEXDUVHBEFURUMVBEBFVNTUKEWTGULUPUMVLTVEWRWGXBWLWQWFWBWPW
      EWCWPBWDBWOVCWPYEWDBWSWOYMVOYOVJVPVQVGXAWKWHWTWJWIWTFWDFWSVCWTYEWDWTWSWOF
      WSVIFWSCVRVPYOVJVPVQVGVSVJWMWBWCGWHSZRZSZWHWIDWBSZRZSZRHUVJRZIUVMRZRZWNWG
      UVLWLUVOWFUVKWBCDWERZRCDUVJRZRWFUVKUVSUVTCUVSDBGDRZSZRUVTWEUWBDWDUWABDGUJ
      UMVBDBGVNTVBCDWEUQCDUVJUQVTUMWKUVNWHEGWJRZREGUVMRZRWKUVNUWCUWDEGFDVNVBEGW
      JUQEGUVMUQVTUMVLUVLUVPUVOUVQUVLUUMUVJRZUVPUVJWCWBGWHFVRUOUVPUWEHUUMUVJUVA
      UKUHTUVOUUOUVMRZUVQUVMWIWHDWBBVRUOUVQUWFIUUOUVMMUKUHTVLUVRWNUVJUVMRZRUWGW
      NRWNHUVJIUVMVKWNUWGURUWGWNUWGUUOUUTRZWNUVJUUOUVMUUTUVJWHGSUUOGWHUAGWIWHGE
      UBVGUFDWCWBDCUBVOVSUWHIHRZWNUWIUWHIUUOHUUTMLVLUHIHURTVEWAUPUPVE $.
  $}

  ${
    xdp15.d $e |- d = ( a2 v ( a0 ^ ( a1 v b1 ) ) ) $.
    xdp15.p0 $e |- p0 = ( ( a1 v b1 ) ^ ( a2 v b2 ) ) $.
    xdp15.e $e |- e = ( b0 ^ ( a0 v p0 ) ) $.
    xdp15.c0 $e |- c0 = ( ( a1 v a2 ) ^ ( b1 v b2 ) ) $.
    xdp15.c1 $e |- c1 = ( ( a0 v a2 ) ^ ( b0 v b2 ) ) $.
    $( Part of proof (1)=>(5) in Day/Pickering 1982.  (Contributed by NM,
       11-Apr-2012.) $)
    xdp15 $p |- ( ( a0 v a1 ) ^ ( ( b0 ^ ( a0 v p0 ) ) v b1 ) )
                  =< ( ( c0 v c1 ) v ( b1 ^ ( a0 v a1 ) ) ) $=
      ( wo wa tr ror lor lan ran wt le1 leran lelor an1r orass cm oridm 3tr lea
      orcom mlduali lear leror bltr or32 lbtr letr ax-arg 2an le3tr2 or12 orabs
      2or ax-a2 ml3le lelan leao1 mldual2i ancom 3tr2 bile le2or ) CDQZFCKQZRZG
      QZRZDEQZGHQZRZCEQZFHQZRZGVQRZQZQZIJQWHQZWAWEVSHQZRZWBWHQZWCRZQZWJWAWMWBCD
      GQZRZQZWCRZQZWPWACEWRQZQZWLRZDXBQZWCRZQZXAVQBGQZRCAQZBHQZRZDAQZWCRZQWAXGC
      DABGHCBQZWQRCFCWQEHQZRZQZRZQZWQRZAHQZXNXSWQBXRCBVSXRNVRXQFKXPCMUAUBSUAUCX
      TCUDXQRZQZWQRZYAXSYCWQXRYBCFUDXQFUEUFUGUFYDXOWRQZYAYDXPWRQZYEYDXPCQZWQRYF
      YCYGWQYCCXQQZCCQZXPQZYGYBXQCXQUHUAYJYHCCXPUIUJYJXQYGYICXPCUKTCXPUNSULUCXP
      CWQWQXOUMUOSXPXOWRWQXOUPUQURYEXBHQZYAEHWRUSYAYKAXBHLTUJSUTVAURVBXHVTVQBVS
      GNTUBXKXDXMXFXIXCXJWLAXBCLUABVSHNTVCXLXEWCAXBDLUAUCVGVDXDWMXFWTXCWEWLXCEC
      WRQZQECQWECEWRVEYLCECWQVFUAECUNULUCWTXFWSXEWCDEWRUIUCUJVGUTWTWOWMWSWNWCWS
      EDWHQZQZWNWSEDCGDQZRZQZQZYNWSEDQZYPQYRWBYSWRYPDEVHWQYOCDGVHUBVGEDYPUISYQY
      MEDCGVIUGURYNYSWHQZWNYTYNEDWHUIUJYSWBWHEDVHTSUTUFUGVAWPWGWDWHQZQWJWMWGWOU
      UAWLWFWEVSFHFVRUMUQVJWOUUAWCWNRWCWBRZWHQWOUUAWHWBWCGVQHVKVLWCWNVMUUBWDWHW
      CWBVMTVNVOVPWGWDWHVEUTVAWJIJWHQZQZWKUUDWJIWDUUCWIOJWGWHPTVGUJWKUUDIJWHUIU
      JSUT $.
  $}

  ${
    xdp53.1 $e |- c0 = ( ( a1 v a2 ) ^ ( b1 v b2 ) ) $.
    xdp53.2 $e |- c1 = ( ( a0 v a2 ) ^ ( b0 v b2 ) ) $.
    xdp53.3 $e |- c2 = ( ( a0 v a1 ) ^ ( b0 v b1 ) ) $.
    xdp53.4 $e |- p0 = ( ( a1 v b1 ) ^ ( a2 v b2 ) ) $.
    xdp53.5 $e |- p = ( ( ( a0 v b0 ) ^ ( a1 v b1 ) ) ^ ( a2 v b2 ) ) $.
    $( Part of proof (5)=>(3) in Day/Pickering 1982.  (Contributed by NM,
       11-Apr-2012.) $)
    xdp53 $p |- p
        =< ( a0 v ( b0 ^ ( b1 v ( c2 ^ ( c0 v c1 ) ) ) ) ) $=
      ( wo wa leo lbtr leor anass tr lan cm leao4 bltr lea orcom mldual2i ancom
      ler2an ror lelor letr lor lear ax-a3 dp15 leid lel2or or32 le2an lerr 3tr
      df-le2 ran an32 ml2i anabs orass leror ) ABAQBEFJHIQZRZQZRZQZABUABVQABVPS
      ZAEBKQZRZVQQZVQAVTBQZWAAVSEBQZRZWBABEQZCFQZDGQZRZRZWDAWEWFRWGRWIPWEWFWGUB
      UCWIVSWCWIWEKRZVSWJWIKWHWEOUDUEKWEBUFUGWIWEWCWEWHUHBEUITULUGWDVSERZBQWBBE
      VSBKSUJWKVTBVSEUKUMUCTBVQVTVRUNUOVTVQVTEBERZFQVNQZRZVQVTEFBCQZVMRZQZRZWNV
      TEWQEVSUHVTFVTQWQVTFUAFWQVTFWPSZVTWOVTFQZRZWQQZWQVTXAFQZXBVTWTWOFQZRZXCVT
      WTXDVTFSVTEBWHQZRZXDVSXFEKWHBOUPUDXGXFXDEXFUQXFBWFQZXDWHWFBWFWGUHUNXDXHBC
      FURUETUOUGULXEWTWORZFQXCFWOWTFVTUAUJXIXAFWTWOUKUMUCTFWQXAWSUNUOXAWQWQXAWP
      FQZWQXAWPFWORZQZXJXAWOVMXKQZRXLXAWOXMWOWTUHBCDEFGHIKLMOUSULXKVMWOFWOUQUJT
      XKFWPFWOUHUNUOWPFUITWQUTVAUOVAUOULWNWRWNVPWRWMVOEWMWLVNQZFQFXNQVOWLFVNVBX
      NFUIXNVNFWLVNWLJVMWLWOEFQZRZJBWOEXOBCSEFSVCJXPNUETWLIHWLBDQZEGQZRZIBXQEXR
      BDSEGSVCIXSMUETVDULVFUPVEUDVPEXOWQRZRZEXORZWQRZWRVOXTEVOFWPXORZQWQXORXTVN
      YDFVNXPVMRYDJXPVMNVGWOXOVMVHUCUPXOWPFFEUAVIWQXOUKVEUDYCYAEXOWQUBUEYBEWQEF
      VJVGVEUCUETWNWLVPQZVQWNEVOWLQZRVPWLQYEWMYFEWMWLVOQYFWLFVNVKWLVOUIUCUDWLVO
      EBEUQUJVPWLUIVEWLBVPBEUHVLUGUOVFTVAUO $.
  $}

  ${
    xxdp.1 $e |- p2 =< ( a2 v b2 ) $.
    xxdp.c0 $e |- c0 = ( ( a1 v a2 ) ^ ( b1 v b2 ) ) $.
    xxdp.c1 $e |- c1 = ( ( a0 v a2 ) ^ ( b0 v b2 ) ) $.
    xxdp.c2 $e |- c2 = ( ( a0 v a1 ) ^ ( b0 v b1 ) ) $.
    xxdp.d $e |- d = ( a2 v ( a0 ^ ( a1 v b1 ) ) ) $.
    xxdp.e $e |- e = ( b0 ^ ( a0 v p0 ) ) $.
    xxdp.p $e |- p = ( ( ( a0 v b0 ) ^ ( a1 v b1 ) ) ^ ( a2 v b2 ) ) $.
    xxdp.p0 $e |- p0 = ( ( a1 v b1 ) ^ ( a2 v b2 ) ) $.
    xxdp.p2 $e |- p2 = ( ( a0 v b0 ) ^ ( a1 v b1 ) ) $.
    $( Part of proof (4)=>(1) in Day/Pickering 1982.  (Contributed by NM,
       3-Apr-2012.) $)
    xxdp41 $p |- c2 =< ( c0 v c1 ) $=
      ( wo wa ancom tr leor leror leo le2an bltr df2le2 cm anass ax-a2 ror or32
      lan ler mldual2i 3tr orass orcom dp34 lel2or mldual lor lea ml2i lbtr ran
      lelan leao1 lear letr or4 2or mli ml3 leran ler2an lelor leao3 le2or 3tr1
      df-le2 ) LHIUDZEFUDZDFIUDZUEZUDZUEZDFUDZGIUDZHWJUEZUDZUEZUDZJKUDZLWHWIDEH
      UDZUEZUDZUEZWNWOHDGUDZUEZUDZUEZUDZWSLWTDGHUDZUEZHDEUDZUEZUDZUDZXILLWTLDHU
      DZUEZUDZUEZXOLLXPLWTUEZUDZUEZXSLLXEHUDZUEXLHUDZUEZYBLLYCYDUEZUEZYEYGLLYFL
      XJXLUEZYFLXLXJUEZYHRXLXJUFUGXJYCXLYDGXEHGDUHUIXLHUJUKULUMUNYEYGLYCYDUOZUN
      UGYEYGYBYJYFYALYFXPXEXAUEZUDZYAYFYKDUDZHUDZYKXPUDYLYFXADUDZYCUEZYOXEUEZHU
      DYNYFYCYOUEYPYDYOYCYDEDUDZHUDYOXLYRHDEUPUQEDHURUGUSYCYOUFUGHXEYOHXADHEUHU
      TVAYQYMHYQXEYOUEYMYOXEUFDXAXEDGUJZVAUGUQVBYKDHVCYKXPVDVBXPYAYKXPXTUJYKCYA
      YKYKWJUEZCYTYKYKWJYKNWJNYKUCUNOULZUMUNCYTUAUNUGCDEFGHIJKLPQRUAVEULVFULVMU
      LULYBXQXTUDXQWTLUEZUDZXSLXPWTVGXTUUBXQLWTUFVHUUCXQWTUDZLUELUUDUEXSLWTXQLX
      PVIVJUUDLUFUUDXRLXQWTUPUSVBVBVKXSXTXNUDZXOXSXTXQUDUUELWTXPVGXQXNXTXQYIXPU
      EXLXJXPUEZUEZXNLYIXPRVLXLXJXPUOUUGXLHXKUDZUEXLHUEZXKUDZXNUUFUUHXLUUFXJDUE
      ZHUDHUUKUDUUHHDXJHGUHVAUUKHVDUUKXKHXJDUFVHVBUSXKHXLDXJEVNVAUUJXKUUIUDXNUU
      IXKVDUUIXMXKXLHUFVHUGVBVBVHUGXTWTXNLWTVOUIULVPXOWHWIXMUDZUEZWNWOXKUDZUEZU
      DZXIXOWTXMXKUDZUDZWHWIUEZXMUDZWNWOUEZXKUDZUDZUUPXNUUQWTXKXMVDVHUURJXMUDZK
      XKUDZUDUVCJKXMXKVQUVDUUTUVEUVBJUUSXMJWIWHUEZUUSPWIWHUFUGZUQKUVAXKQUQVRUGU
      UTUUMUVBUUOWHWIXMHXLIVNVSWNWOXKDXJFVNVSVRVBUUMXDUUOXHUULXCWHUULEXMUDZFUDE
      XBUDZFUDXCEFXMURUVHUVIFUVHEDHEUDZUEZUDUVIEHDVTUVKXBEUVJXADHEVDUSVHUGUQEXB
      FURVBUSUUNXGWNUUNGXKUDZIUDGXFUDZIUDXGGIXKURUVLUVMIUVLGDHGUDZUEZUDUVMXKUVO
      GXJUVNDGHVDUSVHGDHVTUGUQGXFIURVBUSVRUGVKXDWMXHWRXCWLWHXBWKWIXBDWJDXAVIXBY
      KWJDXEXAYSWAUUAVPWBWCVMXGWQWNXFWPWOXFHWJHXEVIXFYKWJXFXEXAHXEVOHXEEWDWBUUA
      VPWBWCVMWEVPWSWHWIIWNUEZUDZUEZWNWOFWHUEZUDZUEZUDJUVPUDZKUVSUDZUDZWTWMUVRW
      RUWAWLUVQWHEFWKUDZUDEFUVPUDZUDWLUVQUWEUWFEUWEFDIFUDZUEZUDUWFWKUWHFWJUWGDF
      IUPUSVHFDIVTUGVHEFWKVCEFUVPVCWFUSWQUVTWNGIWPUDZUDGIUVSUDZUDWQUVTUWIUWJGIH
      FVTVHGIWPVCGIUVSVCWFUSVRUVRUWBUWAUWCUVRUUSUVPUDZUWBUVPWIWHIWNHWDVAUWBUWKJ
      UUSUVPUVGUQUNUGUWAUVAUVSUDZUWCUVSWOWNFWHDWDVAUWCUWLKUVAUVSQUQUNUGVRUWDWTU
      VPUVSUDZUDUWMWTUDWTJUVPKUVSVQWTUWMVDUWMWTUWMUVAUVFUDZWTUVPUVAUVSUVFUVPWNI
      UEUVAIWNUFIWOWNIGUHVMULFWIWHFEUHWAWEUWNKJUDZWTUWOUWNKUVAJUVFQPVRUNKJVDUGV
      KWGVBVBVK $.

    $( Part of proof (1)=>(5) in Day/Pickering 1982.  (Contributed by NM,
       11-Apr-2012.) $)
    xxdp15 $p |- ( ( a0 v a1 ) ^ ( ( b0 ^ ( a0 v p0 ) ) v b1 ) )
                  =< ( ( c0 v c1 ) v ( b1 ^ ( a0 v a1 ) ) ) $=
      ( wo wa lor lan tr ran wt le1 leran lelor an1r orass cm oridm ror 3tr lea
      orcom mlduali lear leror bltr or32 lbtr letr ax-arg 2an le3tr2 or12 orabs
      2or ax-a2 ml3le lelan leao1 mldual2i ancom 3tr2 bile le2or ) DEUDZGDMUDZU
      EZHUDZUEZEFUDZHIUDZUEZDFUDZGIUDZUEZHWDUEZUDZUDZJKUDWOUDZWHWLWFIUDZUEZWIWO
      UDZWJUEZUDZWQWHWTWIDEHUDZUEZUDZWJUEZUDZXCWHDFXEUDZUDZWSUEZEXIUDZWJUEZUDZX
      HWDBHUDZUEDAUDZBIUDZUEZEAUDZWJUEZUDWHXNDEABHIDBUDZXDUEDGDXDFIUDZUEZUDZUEZ
      UDZXDUEZAIUDZYAYFXDBYEDBWFYETWEYDGMYCDUBUFUGUHUFUIYGDUJYDUEZUDZXDUEZYHYFY
      JXDYEYIDGUJYDGUKULUMULYKYBXEUDZYHYKYCXEUDZYLYKYCDUDZXDUEYMYJYNXDYJDYDUDZD
      DUDZYCUDZYNYIYDDYDUNUFYQYODDYCUOUPYQYDYNYPDYCDUQURDYCVAUHUSUIYCDXDXDYBUTV
      BUHYCYBXEXDYBVCVDVEYLXIIUDZYHFIXEVFYHYRAXIISURUPUHVGVHVEVIXOWGWDBWFHTURUG
      XRXKXTXMXPXJXQWSAXIDSUFBWFITURVJXSXLWJAXIESUFUIVNVKXKWTXMXGXJWLWSXJFDXEUD
      ZUDFDUDWLDFXEVLYSDFDXDVMUFFDVAUSUIXGXMXFXLWJEFXEUOUIUPVNVGXGXBWTXFXAWJXFF
      EWOUDZUDZXAXFFEDHEUDZUEZUDZUDZUUAXFFEUDZUUCUDUUEWIUUFXEUUCEFVOXDUUBDEHVOU
      GVNFEUUCUOUHUUDYTFEDHVPUMVEUUAUUFWOUDZXAUUGUUAFEWOUOUPUUFWIWOFEVOURUHVGUL
      UMVHXCWNWKWOUDZUDWQWTWNXBUUHWSWMWLWFGIGWEUTVDVQXBUUHWJXAUEWJWIUEZWOUDXBUU
      HWOWIWJHWDIVRVSWJXAVTUUIWKWOWJWIVTURWAWBWCWNWKWOVLVGVHWQJKWOUDZUDZWRUUKWQ
      JWKUUJWPPKWNWOQURVNUPWRUUKJKWOUOUPUHVG $.

    $( Part of proof (5)=>(3) in Day/Pickering 1982.  (Contributed by NM,
       11-Apr-2012.) $)
    xxdp53 $p |- p
        =< ( a0 v ( b0 ^ ( b1 v ( c2 ^ ( c0 v c1 ) ) ) ) ) $=
      ( wo wa leor leo anass tr lan cm leao4 bltr lea orcom lbtr mldual2i ancom
      ler2an ror lelor letr lor lear ax-a3 dp15 leid lel2or or32 le2an lerr 3tr
      df-le2 ran an32 ml2i anabs orass leror ) CDCUDDGHLJKUDZUEZUDZUEZUDZCDUFDW
      DCDWCUGZCGDMUDZUEZWDUDZWDCWGDUDZWHCWFGDUDZUEZWICDGUDZEHUDZFIUDZUEZUEZWKCW
      LWMUEWNUEWPUAWLWMWNUHUIWPWFWJWPWLMUEZWFWQWPMWOWLUBUJUKMWLDULUMWPWLWJWLWOU
      NDGUOUPUSUMWKWFGUEZDUDWIDGWFDMUGUQWRWGDWFGURUTUIUPDWDWGWEVAVBWGWDWGGDGUEZ
      HUDWAUDZUEZWDWGGHDEUDZVTUEZUDZUEZXAWGGXDGWFUNWGHWGUDXDWGHUFHXDWGHXCUGZWGX
      BWGHUDZUEZXDUDZXDWGXHHUDZXIWGXGXBHUDZUEZXJWGXGXKWGHUGWGGDWOUDZUEZXKWFXMGM
      WODUBVCUJXNXMXKGXMVDXMDWMUDZXKWOWMDWMWNUNVAXKXODEHVEUKUPVBUMUSXLXGXBUEZHU
      DXJHXBXGHWGUFUQXPXHHXGXBURUTUIUPHXDXHXFVAVBXHXDXDXHXCHUDZXDXHXCHXBUEZUDZX
      QXHXBVTXRUDZUEXSXHXBXTXBXGUNDEFGHIJKMPQUBVFUSXRVTXBHXBVDUQUPXRHXCHXBUNVAV
      BXCHUOUPXDVGVHVBVHVBUSXAXEXAWCXEWTWBGWTWSWAUDZHUDHYAUDWBWSHWAVIYAHUOYAWAH
      WSWAWSLVTWSXBGHUDZUEZLDXBGYBDEUGGHUGVJLYCRUKUPWSKJWSDFUDZGIUDZUEZKDYDGYED
      FUGGIUGVJKYFQUKUPVKUSVMVCVLUJWCGYBXDUEZUEZGYBUEZXDUEZXEWBYGGWBHXCYBUEZUDX
      DYBUEYGWAYKHWAYCVTUEYKLYCVTRVNXBYBVTVOUIVCYBXCHHGUFVPXDYBURVLUJYJYHGYBXDU
      HUKYIGXDGHVQVNVLUIUKUPXAWSWCUDZWDXAGWBWSUDZUEWCWSUDYLWTYMGWTWSWBUDYMWSHWA
      VRWSWBUOUIUJWSWBGDGVDUQWCWSUOVLWSDWCDGUNVSUMVBVMUPVHVB $.

    $( Part of proof (4)=>(5) in Day/Pickering 1982.  (Contributed by NM,
       11-Apr-2012.) $)
    xdp45lem $p |- ( ( a0 v a1 ) ^ ( ( b0 ^ ( a0 v p0 ) ) v b1 ) )
                  =< ( ( c0 v c1 ) v ( b1 ^ ( a0 v a1 ) ) ) $=
      ( wo wa ax-a2 2an ancom tr leor leror leo le2an bltr df2le2 cm anass or32
      ror lan ler mldual2i 3tr orass orcom lor ran wt le1 leran lelor oridm lea
      an1r mlduali lear lbtr letr id dp34 lel2or lelan mldual leao1 or4 2or mli
      ml2i ml3 ler2an leao3 le2or 3tr1 df-le2 le3tr2 or12 orabs ml3le 3tr2 bile
      ) DEUDZGDMUDZUEZHUDZUEZEFUDZHIUDZUEZDFUDZGIUDZUEZHXAUEZUDZUDZJKUDXLUDZXEX
      IXCIUDZUEZXFXLUDZXGUEZUDZXNXEXQXFDEHUDZUEZUDZXGUEZUDZXTXEDFYBUDZUDZXPUEZE
      YFUDZXGUEZUDZYEXABHUDZUEZDAUDZBIUDZUEZEAUDZXGUEZUDZXEYKYMYOYNEAIUDZUEZUDZ
      UEZYQXGBYTUEZUDZUEZUDZYSYMYOYNEDBUDZUEZUDZUEZYQXGBYAUEZUDZUEZUDZUUGYMYSEH
      BUDZUEZBEDUDZUEZUDZUDZUUOYMYMYSYMEBUDZUEZUDZUEZUVAYMYMUVBYMYSUEZUDZUEZUVE
      YMYMYABUDZUEUURBUDZUEZUVHYMYMUVIUVJUEZUEZUVKUVMYMYMUVLYMUUPUURUEZUVLYMUUR
      UUPUEZUVNXAUURYLUUPDEUFBHUFUGZUURUUPUHUIUUPUVIUURUVJHYABHEUJUKUURBULUMUNU
      OUPUVKUVMYMUVIUVJUQZUPUIUVKUVMUVHUVQUVLUVGYMUVLUVBYAUUHUEZUDZUVGUVLUVREUD
      ZBUDZUVRUVBUDUVSUVLUUHEUDZUVIUEZUWBYAUEZBUDUWAUVLUVIUWBUEUWCUVJUWBUVIUVJX
      ABUDUWBUURXABEDUFUSDEBURUIUTUVIUWBUHUIBYAUWBBUUHEBDUJVAVBUWDUVTBUWDYAUWBU
      EUVTUWBYAUHEUUHYAEHULZVBUIUSVCUVREBVDUVRUVBVEVCUVBUVGUVRUVBUVFULUVRUVRYTU
      EZUVGUVRUWFUWFUWFUVRUVRYTUVRUUHYAUEZYTUWGUVRUUHYAUHUPUWGDGDYAFIUDZUEZUDZU
      EZUDZYAUEZYTUUHUWLYABUWKDBXCUWKTXBUWJGMUWIDUBVFUTUIVFVGUWMDVHUWJUEZUDZYAU
      EZYTUWLUWOYAUWKUWNDGVHUWJGVIVJVKVJUWPUWHYBUDZYTUWPUWIYBUDZUWQUWPUWIDUDZYA
      UEUWRUWOUWSYAUWODUWJUDZDDUDZUWIUDZUWSUWNUWJDUWJVNVFUXBUWTDDUWIVDUPUXBUWJU
      WSUXADUWIDVLUSDUWIVEUIVCVGUWIDYAYAUWHVMVOUIUWIUWHYBYAUWHVPUKUNUWQYFIUDZYT
      FIYBURYTUXCAYFISUSUPUIVQVRUNUNZUOUPUWFUWFUWFVSZUPUIUWFEDAHBIYPYRYMYPVSZYR
      VSZXAUURYLUUPDEVEBHVEUGUXEVTUNWAUNWBUNUNUVHUVCUVFUDUVCYSYMUEZUDZUVEYMUVBY
      SWCUVFUXHUVCYMYSUHVFUXIUVCYSUDZYMUEYMUXJUEUVEYMYSUVCYMUVBVMWHUXJYMUHUXJUV
      DYMUVCYSUFUTVCVCVQUVEUVFUUTUDZUVAUVEUVFUVCUDUXKYMYSUVBWCUVCUUTUVFUVCUVOUV
      BUEUURUUPUVBUEZUEZUUTYMUVOUVBUVPVGUURUUPUVBUQUXMUURBUUQUDZUEUURBUEZUUQUDZ
      UUTUXLUXNUURUXLUUPEUEZBUDBUXQUDUXNBEUUPBHUJVBUXQBVEUXQUUQBUUPEUHVFVCUTUUQ
      BUUREUUPDWDVBUXPUUQUXOUDUUTUXOUUQVEUXOUUSUUQUURBUHVFUIVCVCVFUIUVFYSUUTYMY
      SVPUKUNVRUVAYOYNUUSUDZUEZYQXGUUQUDZUEZUDZUUOUVAYSUUSUUQUDZUDZYOYNUEZUUSUD
      ZYRUUQUDZUDZUYBUUTUYCYSUUQUUSVEVFUYDYPUUSUDZUYGUDUYHYPYRUUSUUQWEUYIUYFUYG
      UYGYPUYEUUSYPYPUYEUXFYNYOUHUIZUSYRYRUUQUXGUSWFUIUYFUXSUYGUYAYOYNUUSBUURIW
      DWGYQXGUUQEUUPAWDWGWFVCUXSUUKUYAUUNUXRUUJYOUXRDUUSUDZAUDDUUIUDZAUDUUJDAUU
      SURUYKUYLAUYKDEBDUDZUEZUDUYLDBEWIUYNUUIDUYMUUHEBDVEUTVFUIUSDUUIAURVCUTUXT
      UUMYQUXTHUUQUDZIUDHUULUDZIUDUUMHIUUQURUYOUYPIUYOHEYLUEZUDUYPUUQUYQHUUPYLE
      HBVEUTVFHEBWIUIUSHUULIURVCUTWFUIVQUUKUUCUUNUUFUUJUUBYOUUIUUAYNUUIEYTEUUHV
      MUUIUVRYTEYAUUHUWEVJUXDVRWJVKWBUUMUUEYQUULUUDXGUULBYTBYAVMUULUVRYTUULYAUU
      HBYAVPBYADWKWJUXDVRWJVKWBWLVRUUGYOYNIYQUEZUDZUEZYQXGAYOUEZUDZUEZUDYPUYRUD
      ZYRVUAUDZUDZYSUUCUYTUUFVUCUUBUYSYODAUUAUDZUDDAUYRUDZUDUUBUYSVUGVUHDVUGAEI
      AUDZUEZUDVUHUUAVUJAYTVUIEAIUFUTVFAEIWIUIVFDAUUAVDDAUYRVDWMUTUUEVUBYQHIUUD
      UDZUDHIVUAUDZUDUUEVUBVUKVULHIBAWIVFHIUUDVDHIVUAVDWMUTWFUYTVUDVUCVUEUYTUYE
      UYRUDZVUDUYRYNYOIYQBWKVBVUDVUMYPUYEUYRUYJUSUPUIVUCVUEVUEVUAXGYQAYOEWKVBVU
      EVUEYRYRVUAUXGUSUPUIWFVUFYSUYRVUAUDZUDVUNYSUDYSYPUYRYRVUAWEYSVUNVEVUNYSVU
      NYRYPUDZYSUYRYRVUAYPUYRYQIUEYRIYQUHIXGYQIHUJWBUNAYNYOADUJVJWLVUOVUOYSVUOV
      UOYRYRYPYPUXGUXFWFUPYRYPVEUIVQWNVCVCVQYLXDXABXCHTUSUTYPYHYRYJYNYGYOXPAYFD
      SVFBXCITUSUGYQYIXGAYFESVFVGWFWOYHXQYJYDYGXIXPYGFDYBUDZUDFDUDXIDFYBWPVUPDF
      DYAWQVFFDVEVCVGYDYJYCYIXGEFYBVDVGUPWFVQYDXSXQYCXRXGYCFEXLUDZUDZXRYCFEDHEU
      DZUEZUDZUDZVURYCFEUDZVUTUDVVBXFVVCYBVUTEFUFYAVUSDEHUFUTWFFEVUTVDUIVVAVUQF
      EDHWRVKUNVURVVCXLUDZXRVVDVURFEXLVDUPVVCXFXLFEUFUSUIVQVJVKVRXTXKXHXLUDZUDX
      NXQXKXSVVEXPXJXIXCGIGXBVMUKWBXSVVEXGXRUEXGXFUEZXLUDXSVVEXLXFXGHXAIWDVBXGX
      RUHVVFXHXLXGXFUHUSWSWTWLXKXHXLWPVQVRXNJKXLUDZUDZXOVVHXNJXHVVGXMPKXKXLQUSW
      FUPXOVVHJKXLVDUPUIVQ $.

    $( Part of proof (4)=>(5) in Day/Pickering 1982.  Proof before putting in
       id's, ancom/orcom/2an (why?)   (Contributed by NM,
       11-Apr-2012.) $)
$(
    xdp45lemtest $p |- ( ( a0 v a1 ) ^ ( ( b0 ^ ( a0 v p0 ) ) v b1 ) )
                  =< ( ( c0 v c1 ) v ( b1 ^ ( a0 v a1 ) ) ) $=
      ( wo wa ancom tr leor leror leo le2an bltr df2le2 cm anass ax-a2 ror
      or32 lan ler mldual2i 3tr orass orcom lor ran le1 leran lelor an1r oridm
      lea mlduali lear lbtr letr dp34 lel2or lelan mldual ml2i leao1 or4 2or
      mli ml3 ler2an leao3 le2or 3tr1 df-le2 2an le3tr2 or12 orabs ml3le 3tr2
      bile ) DEUDZGDMUDZUEZHUDZUEZEFUDZHIUDZUEZDFUDZGIUDZUEZHWSUEZUDZUDZJKUDXJU
      DZXCXGXAIUDZUEZXDXJUDZXEUEZUDZXLXCXOXDDEHUDZUEZUDZXEUEZUDZXRXCDFXTUDZUDZX
      NUEZEYDUDZXEUEZUDZYCWSBHUDZUEDAUDZBIUDZUEZEAUDZXEUEZUDXCYI???????????????
      ???????????????????UFZUGZ?????????UHZUI??UJZUKULUMUN?????UOZUNUG???YT????
      ????????????????????????UPZUQ???URZUGUSYPUG??????YRUTVA??????YP???YSVAUGU
      QVB???VCZ??VDZVB???YS????????????????UNZ????????????T??????UBVEUSUGVEVF??
      ???????????VGVHVIVH????????????????????VJVE??UUCUN???????VKUQUUDUGVBVF???
      ??VLZVMUG?????VNZUIZUL???UUB?????SUQUNUGVOVPULULZUMUNUUEUG??????????????V
      QULVRULVSULUL???????VTZ???YPVEZ???????UUFWAYP???UUAUSZVBVBVO??????UUJ????
      ???????VFYT??????????????YRVAUUDUUKVBUS??????WBZVA???UUDUUKUGVBVBVEUGUUHU
      LVP??????????UUDVE???????WCZ???????YQUQZ????UQZWDUG???????UUMWEZUUQWDVB??
      ?????????UUB?????????WFZ??????UUDUSVEZUGUQUUBVBUS???????UUB??????UUSUURUG
      UQUUBVBUSWDUGVO?????????????UUF??????YSVHUUIVPWGVIVS?????????UUF??????UUG
      ???WHZWGUUIVPWGVIVSWIVP????????????????????????UULVEUURUGVEUUCUUCWJUS????
      ??????UURVEUUCUUCWJUSWD??????????UUTVAZ??UUOUNUG???UVA??UUPUNUGWD????UUNU
      UD????????????YP???YRVSUL???YRVHWI???????????WDUNUUDUGVOWKVBVBVOYJXBWSBXA
      HTUQUSYMYFYOYHYKYEYLXNAYDDSVEBXAITUQWLYNYGXEAYDESVEVFWDWMYFXOYHYBYEXGXNYE
      FDXTUDZUDFDUDXGDFXTWNUVBDFDXSWOVEFDVDVBVFYBYHYAYGXEEFXTVCVFUNWDVOYBXQXOYA
      XPXEYAFEXJUDZUDZXPYAFEDHEUDZUEZUDZUDZUVDYAFEUDZUVFUDUVHXDUVIXTUVFEFUPXSUV
      EDEHUPUSWDFEUVFVCUGUVGUVCFEDHWPVIULUVDUVIXJUDZXPUVJUVDFEXJVCUNUVIXDXJFEUP
      UQUGVOVHVIVPXRXIXFXJUDZUDXLXOXIXQUVKXNXHXGXAGIGWTVLUIVSXQUVKXEXPUEXEXDUEZ
      XJUDXQUVKXJXDXEHWSIWBVAXEXPUFUVLXFXJXEXDUFUQWQWRWIXIXFXJWNVOVPXLJKXJUDZUD
      ZXMUVNXLJXFUVMXKPKXIXJQUQWDUNXMUVNJKXJVCUNUGVO $.
$)

    $( Part of proof (4)=>(3) in Day/Pickering 1982.  (Contributed by NM,
       11-Apr-2012.) $)
    xdp43lem $p |- p
        =< ( a0 v ( b0 ^ ( b1 v ( c2 ^ ( c0 v c1 ) ) ) ) ) $=
      ( wo wa leor leo anass tr lan cm leao4 bltr lea orcom lbtr mldual2i ancom
      ler2an ror lelor letr lor lear ax-a3 ax-a2 2an leror le2an df2le2 ler 3tr
      or32 orass ran wt le1 leran an1r oridm mlduali id dp34 lel2or mldual ml2i
      lelan leao1 or4 2or mli ml3 leao3 le2or 3tr1 df-le2 or12 orabs ml3le 3tr2
      le3tr2 bile leid lerr an32 anabs ) CDCUDDGHLJKUDZUEZUDZUEZUDZCDUFDXKCDXJU
      GZCGDMUDZUEZXKUDZXKCXNDUDZXOCXMGDUDZUEZXPCDGUDZEHUDZFIUDZUEZUEZXRCXSXTUEY
      AUEYCUAXSXTYAUHUIYCXMXQYCXSMUEZXMYDYCMYBXSUBUJUKMXSDULUMYCXSXQXSYBUNDGUOU
      PUSUMXRXMGUEZDUDXPDGXMDMUGUQYEXNDXMGURUTUIUPDXKXNXLVAVBXNXKXNGDGUEZHUDXHU
      DZUEZXKXNGHDEUDZXGUEZUDZUEZYHXNGYKGXMUNZXNHXNUDYKXNHUFHYKXNHYJUGZXNYIXNHU
      DZUEZYKUDZYKXNYPHUDZYQXNYOYIHUDZUEZYRXNYOYSXNHUGXNGDYBUDZUEZYSXMUUAGMYBDU
      BVCUJZUUBUUAYSGUUAVDUUADXTUDZYSYBXTDXTYAUNZVAYSUUDDEHVEUKUPVBUMUSYTYOYIUE
      ZHUDYRHYIYOHXNUFUQUUFYPHYOYIURUTUIUPHYKYPYNVAVBYPYKYKYPYJHUDZYKYPYJHYIUEZ
      UDZUUGYPYIXGUUHUDZUEUUIYPYIUUJYIYOUNYPEFUDZHIUDZUEZDFUDZGIUDZUEZUUHUDZUDZ
      UUJYPUUNXNIUDZUEZUUKUUHUDZUULUEZUDZUURYPUUTUUKDXTUEZUDZUULUEZUDZUVCYPDFUV
      DUDZUDZUUSUEZEUVHUDZUULUEZUDZUVGYIBHUDZUEZDAUDZBIUDZUEZEAUDZUULUEZUDZYPUV
      MUVOUVQUVPEAIUDZUEZUDZUEZUVSUULBUWBUEZUDZUEZUDZUWAUVOUVQUVPEDBUDZUEZUDZUE
      ZUVSUULBXTUEZUDZUEZUDZUWIUVOUWAEHBUDZUEZBEDUDZUEZUDZUDZUWQUVOUVOUWAUVOEBU
      DZUEZUDZUEZUXCUVOUVOUXDUVOUWAUEZUDZUEZUXGUVOUVOXTBUDZUEUWTBUDZUEZUXJUVOUV
      OUXKUXLUEZUEZUXMUXOUVOUVOUXNUVOUWRUWTUEZUXNUVOUWTUWRUEZUXPYIUWTUVNUWRDEVF
      BHVFVGZUWTUWRURUIUWRUXKUWTUXLHXTBHEUFVHUWTBUGVIUMVJUKUXMUXOUVOUXKUXLUHZUK
      UIUXMUXOUXJUXSUXNUXIUVOUXNUXDXTUWJUEZUDZUXIUXNUXTEUDZBUDZUXTUXDUDUYAUXNUW
      JEUDZUXKUEZUYDXTUEZBUDUYCUXNUXKUYDUEUYEUXLUYDUXKUXLYIBUDUYDUWTYIBEDVFUTDE
      BVMUIUJUXKUYDURUIBXTUYDBUWJEBDUFVKUQUYFUYBBUYFXTUYDUEUYBUYDXTUREUWJXTEHUG
      ZUQUIUTVLUXTEBVNUXTUXDUOVLUXDUXIUXTUXDUXHUGUXTUXTUWBUEZUXIUXTUYHUYHUYHUXT
      UXTUWBUXTUWJXTUEZUWBUYIUXTUWJXTURUKUYIDUUBUDZXTUEZUWBUWJUYJXTBUUBDBXNUUBT
      UUCUIVCVOUYKDVPUUAUEZUDZXTUEZUWBUYJUYMXTUUBUYLDGVPUUAGVQVRVAVRUYNYAUVDUDZ
      UWBUYNYBUVDUDZUYOUYNYBDUDZXTUEUYPUYMUYQXTUYMDUUAUDZDDUDZYBUDZUYQUYLUUADUU
      AVSVCUYTUYRDDYBVNUKUYTUUAUYQUYSDYBDVTUTDYBUOUIVLVOYBDXTUUEWAUIYBYAUVDXTYA
      VDVHUMUYOUVHIUDZUWBFIUVDVMUWBVUAAUVHISUTUKUIUPVBUMUMZVJUKUYHUYHUYHWBZUKUI
      UYHEDAHBIUVRUVTUVOUVRWBZUVTWBZYIUWTUVNUWRDEUOBHUOVGVUCWCUMWDUMWGUMUMUXJUX
      EUXHUDUXEUWAUVOUEZUDZUXGUVOUXDUWAWEUXHVUFUXEUVOUWAURVCVUGUXEUWAUDZUVOUEUV
      OVUHUEUXGUVOUWAUXEUVOUXDUNWFVUHUVOURVUHUXFUVOUXEUWAVFUJVLVLUPUXGUXHUXBUDZ
      UXCUXGUXHUXEUDVUIUVOUWAUXDWEUXEUXBUXHUXEUXQUXDUEUWTUWRUXDUEZUEZUXBUVOUXQU
      XDUXRVOUWTUWRUXDUHVUKUWTBUWSUDZUEUWTBUEZUWSUDZUXBVUJVULUWTVUJUWREUEZBUDBV
      UOUDVULBEUWRBHUFUQVUOBUOVUOUWSBUWREURVCVLUJUWSBUWTEUWRDWHUQVUNUWSVUMUDUXB
      VUMUWSUOVUMUXAUWSUWTBURVCUIVLVLVCUIUXHUWAUXBUVOUWAVDVHUMVBUXCUVQUVPUXAUDZ
      UEZUVSUULUWSUDZUEZUDZUWQUXCUWAUXAUWSUDZUDZUVQUVPUEZUXAUDZUVTUWSUDZUDZVUTU
      XBVVAUWAUWSUXAUOVCVVBUVRUXAUDZVVEUDVVFUVRUVTUXAUWSWIVVGVVDVVEVVEUVRVVCUXA
      UVRUVRVVCVUDUVPUVQURUIZUTUVTUVTUWSVUEUTWJUIVVDVUQVVEVUSUVQUVPUXABUWTIWHWK
      UVSUULUWSEUWRAWHWKWJVLVUQUWMVUSUWPVUPUWLUVQVUPDUXAUDZAUDDUWKUDZAUDUWLDAUX
      AVMVVIVVJAVVIDEBDUDZUEZUDVVJDBEWLVVLUWKDVVKUWJEBDUOUJVCUIUTDUWKAVMVLUJVUR
      UWOUVSVURHUWSUDZIUDHUWNUDZIUDUWOHIUWSVMVVMVVNIVVMHEUVNUEZUDVVNUWSVVOHUWRU
      VNEHBUOUJVCHEBWLUIUTHUWNIVMVLUJWJUIUPUWMUWEUWPUWHUWLUWDUVQUWKUWCUVPUWKEUW
      BEUWJUNUWKUXTUWBEXTUWJUYGVRVUBVBUSVAWGUWOUWGUVSUWNUWFUULUWNBUWBBXTUNUWNUX
      TUWBUWNXTUWJBXTVDBXTDWMUSVUBVBUSVAWGWNVBUWIUVQUVPIUVSUEZUDZUEZUVSUULAUVQU
      EZUDZUEZUDUVRVVPUDZUVTVVSUDZUDZUWAUWEVVRUWHVWAUWDVVQUVQDAUWCUDZUDDAVVPUDZ
      UDUWDVVQVWEVWFDVWEAEIAUDZUEZUDVWFUWCVWHAUWBVWGEAIVFUJVCAEIWLUIVCDAUWCVNDA
      VVPVNWOUJUWGVVTUVSHIUWFUDZUDHIVVSUDZUDUWGVVTVWIVWJHIBAWLVCHIUWFVNHIVVSVNW
      OUJWJVVRVWBVWAVWCVVRVVCVVPUDZVWBVVPUVPUVQIUVSBWMUQVWBVWKUVRVVCVVPVVHUTUKU
      IVWAVWCVWCVVSUULUVSAUVQEWMUQVWCVWCUVTUVTVVSVUEUTUKUIWJVWDUWAVVPVVSUDZUDVW
      LUWAUDUWAUVRVVPUVTVVSWIUWAVWLUOVWLUWAVWLUVTUVRUDZUWAVVPUVTVVSUVRVVPUVSIUE
      UVTIUVSURIUULUVSIHUFWGUMAUVPUVQADUFVRWNVWMVWMUWAVWMVWMUVTUVTUVRUVRVUEVUDW
      JUKUVTUVRUOUIUPWPVLVLUPUVNYOYIBXNHTUTUJUVRUVJUVTUVLUVPUVIUVQUUSAUVHDSVCBX
      NITUTVGUVSUVKUULAUVHESVCVOWJXAUVJUUTUVLUVFUVIUUNUUSUVIFDUVDUDZUDFDUDUUNDF
      UVDWQVWNDFDXTWRVCFDUOVLVOUVFUVLUVEUVKUULEFUVDVNVOUKWJUPUVFUVBUUTUVEUVAUUL
      UVEFEUUHUDZUDZUVAUVEFEDHEUDZUEZUDZUDZVWPUVEFEUDZVWRUDVWTUUKVXAUVDVWREFVFX
      TVWQDEHVFUJWJFEVWRVNUIVWSVWOFEDHWSVAUMVWPVXAUUHUDZUVAVXBVWPFEUUHVNUKVXAUU
      KUUHFEVFUTUIUPVRVAVBUVCUUPUUMUUHUDZUDUURUUTUUPUVBVXCUUSUUOUUNXNGIYMVHWGUV
      BVXCUULUVAUEUULUUKUEZUUHUDUVBVXCUUHUUKUULHYIIWHUQUULUVAURVXDUUMUUHUULUUKU
      RUTWTXBWNUUPUUMUUHWQUPVBUURJKUUHUDZUDZUUJVXFUURJUUMVXEUUQPKUUPUUHQUTWJUKU
      UJVXFJKUUHVNUKUIUPUSUUHXGYIHYIVDUQUPUUHHYJHYIUNVAVBYJHUOUPYKXCWDVBWDVBUSY
      HYLYHXJYLYGXIGYGYFXHUDZHUDHVXGUDXIYFHXHVMVXGHUOVXGXHHYFXHYFLXGYFYIGHUDZUE
      ZLDYIGVXHDEUGGHUGVILVXIRUKUPYFKJYFUUPKDUUNGUUODFUGGIUGVIKUUPQUKUPXDUSWPVC
      VLUJXJGVXHYKUEZUEZGVXHUEZYKUEZYLXIVXJGXIHYJVXHUEZUDYKVXHUEVXJXHVXNHXHVXIX
      GUEVXNLVXIXGRVOYIVXHXGXEUIVCVXHYJHHGUFWFYKVXHURVLUJVXMVXKGVXHYKUHUKVXLGYK
      GHXFVOVLUIUKUPYHYFXJUDZXKYHGXIYFUDZUEXJYFUDVXOYGVXPGYGYFXIUDVXPYFHXHVNYFX
      IUOUIUJYFXIGDGVDUQXJYFUOVLYFDXJDGUNVHUMVBWPUPWDVB $.
  $}

  ${
    xxxdp.c0 $e |- c0 = ( ( a1 v a2 ) ^ ( b1 v b2 ) ) $.
    xxxdp.c1 $e |- c1 = ( ( a0 v a2 ) ^ ( b0 v b2 ) ) $.
    xxxdp.c2 $e |- c2 = ( ( a0 v a1 ) ^ ( b0 v b1 ) ) $.
    xxxdp.d $e |- d = ( a2 v ( a0 ^ ( a1 v b1 ) ) ) $.
    xxxdp.e $e |- e = ( b0 ^ ( a0 v p0 ) ) $.
    xxxdp.p $e |- p = ( ( ( a0 v b0 ) ^ ( a1 v b1 ) ) ^ ( a2 v b2 ) ) $.
    xxxdp.p0 $e |- p0 = ( ( a1 v b1 ) ^ ( a2 v b2 ) ) $.
    xxxdp.p2 $e |- p2 = ( ( a0 v b0 ) ^ ( a1 v b1 ) ) $.
    $( Part of proof (4)=>(5) in Day/Pickering 1982.  (Contributed by NM,
       11-Apr-2012.) $)
    xdp45 $p |- ( ( a0 v a1 ) ^ ( ( b0 ^ ( a0 v p0 ) ) v b1 ) )
                  =< ( ( c0 v c1 ) v ( b1 ^ ( a0 v a1 ) ) ) $=
      ( wo wa ax-a2 2an ancom tr leor leror leo le2an bltr df2le2 cm anass or32
      ror lan ler mldual2i 3tr orass orcom lor ran wt le1 leran lelor oridm lea
      an1r mlduali lear lbtr letr id dp34 lel2or lelan mldual leao1 or4 2or mli
      ml2i ml3 ler2an leao3 le2or 3tr1 df-le2 le3tr2 or12 orabs ml3le 3tr2 bile
      ) DEUCZGDMUCZUDZHUCZUDZEFUCZHIUCZUDZDFUCZGIUCZUDZHWTUDZUCZUCZJKUCXKUCZXDX
      HXBIUCZUDZXEXKUCZXFUDZUCZXMXDXPXEDEHUCZUDZUCZXFUDZUCZXSXDDFYAUCZUCZXOUDZE
      YEUCZXFUDZUCZYDWTBHUCZUDZDAUCZBIUCZUDZEAUCZXFUDZUCZXDYJYLYNYMEAIUCZUDZUCZ
      UDZYPXFBYSUDZUCZUDZUCZYRYLYNYMEDBUCZUDZUCZUDZYPXFBXTUDZUCZUDZUCZUUFYLYREH
      BUCZUDZBEDUCZUDZUCZUCZUUNYLYLYRYLEBUCZUDZUCZUDZUUTYLYLUVAYLYRUDZUCZUDZUVD
      YLYLXTBUCZUDUUQBUCZUDZUVGYLYLUVHUVIUDZUDZUVJUVLYLYLUVKYLUUOUUQUDZUVKYLUUQ
      UUOUDZUVMWTUUQYKUUODEUEBHUEUFZUUQUUOUGUHUUOUVHUUQUVIHXTBHEUIUJUUQBUKULUMU
      NUOUVJUVLYLUVHUVIUPZUOUHUVJUVLUVGUVPUVKUVFYLUVKUVAXTUUGUDZUCZUVFUVKUVQEUC
      ZBUCZUVQUVAUCUVRUVKUUGEUCZUVHUDZUWAXTUDZBUCUVTUVKUVHUWAUDUWBUVIUWAUVHUVIW
      TBUCUWAUUQWTBEDUEURDEBUQUHUSUVHUWAUGUHBXTUWABUUGEBDUIUTVAUWCUVSBUWCXTUWAU
      DUVSUWAXTUGEUUGXTEHUKZVAUHURVBUVQEBVCUVQUVAVDVBUVAUVFUVQUVAUVEUKUVQUVQYSU
      DZUVFUVQUWEUWEUWEUVQUVQYSUVQUUGXTUDZYSUWFUVQUUGXTUGUOUWFDGDXTFIUCZUDZUCZU
      DZUCZXTUDZYSUUGUWKXTBUWJDBXBUWJSXAUWIGMUWHDUAVEUSUHVEVFUWLDVGUWIUDZUCZXTU
      DZYSUWKUWNXTUWJUWMDGVGUWIGVHVIVJVIUWOUWGYAUCZYSUWOUWHYAUCZUWPUWOUWHDUCZXT
      UDUWQUWNUWRXTUWNDUWIUCZDDUCZUWHUCZUWRUWMUWIDUWIVMVEUXAUWSDDUWHVCUOUXAUWIU
      WRUWTDUWHDVKURDUWHVDUHVBVFUWHDXTXTUWGVLVNUHUWHUWGYAXTUWGVOUJUMUWPYEIUCZYS
      FIYAUQYSUXBAYEIRURUOUHVPVQUMUMZUNUOUWEUWEUWEVRZUOUHUWEEDAHBIYOYQYLYOVRZYQ
      VRZWTUUQYKUUODEVDBHVDUFUXDVSUMVTUMWAUMUMUVGUVBUVEUCUVBYRYLUDZUCZUVDYLUVAY
      RWBUVEUXGUVBYLYRUGVEUXHUVBYRUCZYLUDYLUXIUDUVDYLYRUVBYLUVAVLWGUXIYLUGUXIUV
      CYLUVBYRUEUSVBVBVPUVDUVEUUSUCZUUTUVDUVEUVBUCUXJYLYRUVAWBUVBUUSUVEUVBUVNUV
      AUDUUQUUOUVAUDZUDZUUSYLUVNUVAUVOVFUUQUUOUVAUPUXLUUQBUUPUCZUDUUQBUDZUUPUCZ
      UUSUXKUXMUUQUXKUUOEUDZBUCBUXPUCUXMBEUUOBHUIVAUXPBVDUXPUUPBUUOEUGVEVBUSUUP
      BUUQEUUODWCVAUXOUUPUXNUCUUSUXNUUPVDUXNUURUUPUUQBUGVEUHVBVBVEUHUVEYRUUSYLY
      RVOUJUMVQUUTYNYMUURUCZUDZYPXFUUPUCZUDZUCZUUNUUTYRUURUUPUCZUCZYNYMUDZUURUC
      ZYQUUPUCZUCZUYAUUSUYBYRUUPUURVDVEUYCYOUURUCZUYFUCUYGYOYQUURUUPWDUYHUYEUYF
      UYFYOUYDUURYOYOUYDUXEYMYNUGUHZURYQYQUUPUXFURWEUHUYEUXRUYFUXTYNYMUURBUUQIW
      CWFYPXFUUPEUUOAWCWFWEVBUXRUUJUXTUUMUXQUUIYNUXQDUURUCZAUCDUUHUCZAUCUUIDAUU
      RUQUYJUYKAUYJDEBDUCZUDZUCUYKDBEWHUYMUUHDUYLUUGEBDVDUSVEUHURDUUHAUQVBUSUXS
      UULYPUXSHUUPUCZIUCHUUKUCZIUCUULHIUUPUQUYNUYOIUYNHEYKUDZUCUYOUUPUYPHUUOYKE
      HBVDUSVEHEBWHUHURHUUKIUQVBUSWEUHVPUUJUUBUUMUUEUUIUUAYNUUHYTYMUUHEYSEUUGVL
      UUHUVQYSEXTUUGUWDVIUXCVQWIVJWAUULUUDYPUUKUUCXFUUKBYSBXTVLUUKUVQYSUUKXTUUG
      BXTVOBXTDWJWIUXCVQWIVJWAWKVQUUFYNYMIYPUDZUCZUDZYPXFAYNUDZUCZUDZUCYOUYQUCZ
      YQUYTUCZUCZYRUUBUYSUUEVUBUUAUYRYNDAYTUCZUCDAUYQUCZUCUUAUYRVUFVUGDVUFAEIAU
      CZUDZUCVUGYTVUIAYSVUHEAIUEUSVEAEIWHUHVEDAYTVCDAUYQVCWLUSUUDVUAYPHIUUCUCZU
      CHIUYTUCZUCUUDVUAVUJVUKHIBAWHVEHIUUCVCHIUYTVCWLUSWEUYSVUCVUBVUDUYSUYDUYQU
      CZVUCUYQYMYNIYPBWJVAVUCVULYOUYDUYQUYIURUOUHVUBVUDVUDUYTXFYPAYNEWJVAVUDVUD
      YQYQUYTUXFURUOUHWEVUEYRUYQUYTUCZUCVUMYRUCYRYOUYQYQUYTWDYRVUMVDVUMYRVUMYQY
      OUCZYRUYQYQUYTYOUYQYPIUDYQIYPUGIXFYPIHUIWAUMAYMYNADUIVIWKVUNVUNYRVUNVUNYQ
      YQYOYOUXFUXEWEUOYQYOVDUHVPWMVBVBVPYKXCWTBXBHSURUSYOYGYQYIYMYFYNXOAYEDRVEB
      XBISURUFYPYHXFAYEERVEVFWEWNYGXPYIYCYFXHXOYFFDYAUCZUCFDUCXHDFYAWOVUODFDXTW
      PVEFDVDVBVFYCYIYBYHXFEFYAVCVFUOWEVPYCXRXPYBXQXFYBFEXKUCZUCZXQYBFEDHEUCZUD
      ZUCZUCZVUQYBFEUCZVUSUCVVAXEVVBYAVUSEFUEXTVURDEHUEUSWEFEVUSVCUHVUTVUPFEDHW
      QVJUMVUQVVBXKUCZXQVVCVUQFEXKVCUOVVBXEXKFEUEURUHVPVIVJVQXSXJXGXKUCZUCXMXPX
      JXRVVDXOXIXHXBGIGXAVLUJWAXRVVDXFXQUDXFXEUDZXKUCXRVVDXKXEXFHWTIWCVAXFXQUGV
      VEXGXKXFXEUGURWRWSWKXJXGXKWOVPVQXMJKXKUCZUCZXNVVGXMJXGVVFXLOKXJXKPURWEUOX
      NVVGJKXKVCUOUHVP $.

    $( Part of proof (4)=>(3) in Day/Pickering 1982.  (Contributed by NM,
       11-Apr-2012.) $)
    xdp43 $p |- p
        =< ( a0 v ( b0 ^ ( b1 v ( c2 ^ ( c0 v c1 ) ) ) ) ) $=
      ( wo wa leor leo anass tr lan cm leao4 bltr lea orcom lbtr mldual2i ancom
      ler2an ror lelor letr lor lear ax-a3 ax-a2 2an leror le2an df2le2 ler 3tr
      or32 orass ran wt le1 leran an1r oridm mlduali id dp34 lel2or mldual ml2i
      lelan leao1 or4 2or mli ml3 leao3 le2or 3tr1 df-le2 or12 orabs ml3le 3tr2
      le3tr2 bile leid lerr an32 anabs ) CDCUCDGHLJKUCZUDZUCZUDZUCZCDUEDXJCDXIU
      FZCGDMUCZUDZXJUCZXJCXMDUCZXNCXLGDUCZUDZXOCDGUCZEHUCZFIUCZUDZUDZXQCXRXSUDX
      TUDYBTXRXSXTUGUHYBXLXPYBXRMUDZXLYCYBMYAXRUAUIUJMXRDUKULYBXRXPXRYAUMDGUNUO
      URULXQXLGUDZDUCXODGXLDMUFUPYDXMDXLGUQUSUHUODXJXMXKUTVAXMXJXMGDGUDZHUCXGUC
      ZUDZXJXMGHDEUCZXFUDZUCZUDZYGXMGYJGXLUMZXMHXMUCYJXMHUEHYJXMHYIUFZXMYHXMHUC
      ZUDZYJUCZYJXMYOHUCZYPXMYNYHHUCZUDZYQXMYNYRXMHUFXMGDYAUCZUDZYRXLYTGMYADUAV
      BUIZUUAYTYRGYTVCYTDXSUCZYRYAXSDXSXTUMZUTYRUUCDEHVDUJUOVAULURYSYNYHUDZHUCY
      QHYHYNHXMUEUPUUEYOHYNYHUQUSUHUOHYJYOYMUTVAYOYJYJYOYIHUCZYJYOYIHYHUDZUCZUU
      FYOYHXFUUGUCZUDUUHYOYHUUIYHYNUMYOEFUCZHIUCZUDZDFUCZGIUCZUDZUUGUCZUCZUUIYO
      UUMXMIUCZUDZUUJUUGUCZUUKUDZUCZUUQYOUUSUUJDXSUDZUCZUUKUDZUCZUVBYODFUVCUCZU
      CZUURUDZEUVGUCZUUKUDZUCZUVFYHBHUCZUDZDAUCZBIUCZUDZEAUCZUUKUDZUCZYOUVLUVNU
      VPUVOEAIUCZUDZUCZUDZUVRUUKBUWAUDZUCZUDZUCZUVTUVNUVPUVOEDBUCZUDZUCZUDZUVRU
      UKBXSUDZUCZUDZUCZUWHUVNUVTEHBUCZUDZBEDUCZUDZUCZUCZUWPUVNUVNUVTUVNEBUCZUDZ
      UCZUDZUXBUVNUVNUXCUVNUVTUDZUCZUDZUXFUVNUVNXSBUCZUDUWSBUCZUDZUXIUVNUVNUXJU
      XKUDZUDZUXLUXNUVNUVNUXMUVNUWQUWSUDZUXMUVNUWSUWQUDZUXOYHUWSUVMUWQDEVEBHVEV
      FZUWSUWQUQUHUWQUXJUWSUXKHXSBHEUEVGUWSBUFVHULVIUJUXLUXNUVNUXJUXKUGZUJUHUXL
      UXNUXIUXRUXMUXHUVNUXMUXCXSUWIUDZUCZUXHUXMUXSEUCZBUCZUXSUXCUCUXTUXMUWIEUCZ
      UXJUDZUYCXSUDZBUCUYBUXMUXJUYCUDUYDUXKUYCUXJUXKYHBUCUYCUWSYHBEDVEUSDEBVLUH
      UIUXJUYCUQUHBXSUYCBUWIEBDUEVJUPUYEUYABUYEXSUYCUDUYAUYCXSUQEUWIXSEHUFZUPUH
      USVKUXSEBVMUXSUXCUNVKUXCUXHUXSUXCUXGUFUXSUXSUWAUDZUXHUXSUYGUYGUYGUXSUXSUW
      AUXSUWIXSUDZUWAUYHUXSUWIXSUQUJUYHDUUAUCZXSUDZUWAUWIUYIXSBUUADBXMUUASUUBUH
      VBVNUYJDVOYTUDZUCZXSUDZUWAUYIUYLXSUUAUYKDGVOYTGVPVQUTVQUYMXTUVCUCZUWAUYMY
      AUVCUCZUYNUYMYADUCZXSUDUYOUYLUYPXSUYLDYTUCZDDUCZYAUCZUYPUYKYTDYTVRVBUYSUY
      QDDYAVMUJUYSYTUYPUYRDYADVSUSDYAUNUHVKVNYADXSUUDVTUHYAXTUVCXSXTVCVGULUYNUV
      GIUCZUWAFIUVCVLUWAUYTAUVGIRUSUJUHUOVAULULZVIUJUYGUYGUYGWAZUJUHUYGEDAHBIUV
      QUVSUVNUVQWAZUVSWAZYHUWSUVMUWQDEUNBHUNVFVUBWBULWCULWFULULUXIUXDUXGUCUXDUV
      TUVNUDZUCZUXFUVNUXCUVTWDUXGVUEUXDUVNUVTUQVBVUFUXDUVTUCZUVNUDUVNVUGUDUXFUV
      NUVTUXDUVNUXCUMWEVUGUVNUQVUGUXEUVNUXDUVTVEUIVKVKUOUXFUXGUXAUCZUXBUXFUXGUX
      DUCVUHUVNUVTUXCWDUXDUXAUXGUXDUXPUXCUDUWSUWQUXCUDZUDZUXAUVNUXPUXCUXQVNUWSU
      WQUXCUGVUJUWSBUWRUCZUDUWSBUDZUWRUCZUXAVUIVUKUWSVUIUWQEUDZBUCBVUNUCVUKBEUW
      QBHUEUPVUNBUNVUNUWRBUWQEUQVBVKUIUWRBUWSEUWQDWGUPVUMUWRVULUCUXAVULUWRUNVUL
      UWTUWRUWSBUQVBUHVKVKVBUHUXGUVTUXAUVNUVTVCVGULVAUXBUVPUVOUWTUCZUDZUVRUUKUW
      RUCZUDZUCZUWPUXBUVTUWTUWRUCZUCZUVPUVOUDZUWTUCZUVSUWRUCZUCZVUSUXAVUTUVTUWR
      UWTUNVBVVAUVQUWTUCZVVDUCVVEUVQUVSUWTUWRWHVVFVVCVVDVVDUVQVVBUWTUVQUVQVVBVU
      CUVOUVPUQUHZUSUVSUVSUWRVUDUSWIUHVVCVUPVVDVURUVPUVOUWTBUWSIWGWJUVRUUKUWREU
      WQAWGWJWIVKVUPUWLVURUWOVUOUWKUVPVUODUWTUCZAUCDUWJUCZAUCUWKDAUWTVLVVHVVIAV
      VHDEBDUCZUDZUCVVIDBEWKVVKUWJDVVJUWIEBDUNUIVBUHUSDUWJAVLVKUIVUQUWNUVRVUQHU
      WRUCZIUCHUWMUCZIUCUWNHIUWRVLVVLVVMIVVLHEUVMUDZUCVVMUWRVVNHUWQUVMEHBUNUIVB
      HEBWKUHUSHUWMIVLVKUIWIUHUOUWLUWDUWOUWGUWKUWCUVPUWJUWBUVOUWJEUWAEUWIUMUWJU
      XSUWAEXSUWIUYFVQVUAVAURUTWFUWNUWFUVRUWMUWEUUKUWMBUWABXSUMUWMUXSUWAUWMXSUW
      IBXSVCBXSDWLURVUAVAURUTWFWMVAUWHUVPUVOIUVRUDZUCZUDZUVRUUKAUVPUDZUCZUDZUCU
      VQVVOUCZUVSVVRUCZUCZUVTUWDVVQUWGVVTUWCVVPUVPDAUWBUCZUCDAVVOUCZUCUWCVVPVWD
      VWEDVWDAEIAUCZUDZUCVWEUWBVWGAUWAVWFEAIVEUIVBAEIWKUHVBDAUWBVMDAVVOVMWNUIUW
      FVVSUVRHIUWEUCZUCHIVVRUCZUCUWFVVSVWHVWIHIBAWKVBHIUWEVMHIVVRVMWNUIWIVVQVWA
      VVTVWBVVQVVBVVOUCZVWAVVOUVOUVPIUVRBWLUPVWAVWJUVQVVBVVOVVGUSUJUHVVTVWBVWBV
      VRUUKUVRAUVPEWLUPVWBVWBUVSUVSVVRVUDUSUJUHWIVWCUVTVVOVVRUCZUCVWKUVTUCUVTUV
      QVVOUVSVVRWHUVTVWKUNVWKUVTVWKUVSUVQUCZUVTVVOUVSVVRUVQVVOUVRIUDUVSIUVRUQIU
      UKUVRIHUEWFULAUVOUVPADUEVQWMVWLVWLUVTVWLVWLUVSUVSUVQUVQVUDVUCWIUJUVSUVQUN
      UHUOWOVKVKUOUVMYNYHBXMHSUSUIUVQUVIUVSUVKUVOUVHUVPUURAUVGDRVBBXMISUSVFUVRU
      VJUUKAUVGERVBVNWIWTUVIUUSUVKUVEUVHUUMUURUVHFDUVCUCZUCFDUCUUMDFUVCWPVWMDFD
      XSWQVBFDUNVKVNUVEUVKUVDUVJUUKEFUVCVMVNUJWIUOUVEUVAUUSUVDUUTUUKUVDFEUUGUCZ
      UCZUUTUVDFEDHEUCZUDZUCZUCZVWOUVDFEUCZVWQUCVWSUUJVWTUVCVWQEFVEXSVWPDEHVEUI
      WIFEVWQVMUHVWRVWNFEDHWRUTULVWOVWTUUGUCZUUTVXAVWOFEUUGVMUJVWTUUJUUGFEVEUSU
      HUOVQUTVAUVBUUOUULUUGUCZUCUUQUUSUUOUVAVXBUURUUNUUMXMGIYLVGWFUVAVXBUUKUUTU
      DUUKUUJUDZUUGUCUVAVXBUUGUUJUUKHYHIWGUPUUKUUTUQVXCUULUUGUUKUUJUQUSWSXAWMUU
      OUULUUGWPUOVAUUQJKUUGUCZUCZUUIVXEUUQJUULVXDUUPOKUUOUUGPUSWIUJUUIVXEJKUUGV
      MUJUHUOURUUGXFYHHYHVCUPUOUUGHYIHYHUMUTVAYIHUNUOYJXBWCVAWCVAURYGYKYGXIYKYF
      XHGYFYEXGUCZHUCHVXFUCXHYEHXGVLVXFHUNVXFXGHYEXGYELXFYEYHGHUCZUDZLDYHGVXGDE
      UFGHUFVHLVXHQUJUOYEKJYEUUOKDUUMGUUNDFUFGIUFVHKUUOPUJUOXCURWOVBVKUIXIGVXGY
      JUDZUDZGVXGUDZYJUDZYKXHVXIGXHHYIVXGUDZUCYJVXGUDVXIXGVXMHXGVXHXFUDVXMLVXHX
      FQVNYHVXGXFXDUHVBVXGYIHHGUEWEYJVXGUQVKUIVXLVXJGVXGYJUGUJVXKGYJGHXEVNVKUHU
      JUOYGYEXIUCZXJYGGXHYEUCZUDXIYEUCVXNYFVXOGYFYEXHUCVXOYEHXGVMYEXHUNUHUIYEXH
      GDGVCUPXIYEUNVKYEDXIDGUMVGULVAWOUOWCVA $.
  $}

  ${
    3dp.c0 $e |- c0 = ( ( a1 v a1 ) ^ ( b1 v b1 ) ) $.
    3dp.c1 $e |- c1 = ( ( a0 v a1 ) ^ ( b0 v b1 ) ) $.
    3dp.c2 $e |- c2 = ( ( a0 v a1 ) ^ ( b0 v b1 ) ) $.
    3dp.d $e |- d = ( a1 v ( a0 ^ ( a1 v b1 ) ) ) $.
    3dp.e $e |- e = ( b0 ^ ( a0 v p0 ) ) $.
    3dp.p $e |- p = ( ( ( a0 v b0 ) ^ ( a1 v b1 ) ) ^ ( a1 v b1 ) ) $.
    3dp.p0 $e |- p0 = ( ( a1 v b1 ) ^ ( a1 v b1 ) ) $.
    3dp.p2 $e |- p2 = ( ( a0 v b0 ) ^ ( a1 v b1 ) ) $.
    $( "3OA" version of ~ xdp43 .  Changed ` a2 ` to ` a1 ` and ` b2 ` to
       ` b1 ` .  (Contributed by NM, 11-Apr-2012.) $)
    3dp43 $p |- p
        =< ( a0 v ( b0 ^ ( b1 v ( c2 ^ ( c0 v c1 ) ) ) ) ) $=
      ( wo wa leor leo anass tr lan cm leao4 bltr lea orcom lbtr mldual2i ancom
      ler2an ror lelor letr lor lear ax-a3 ax-a2 2an leror le2an df2le2 ler 3tr
      or32 orass ran wt le1 leran an1r oridm mlduali id dp34 lel2or mldual ml2i
      lelan leao1 or4 2or mli ml3 leao3 le2or 3tr1 df-le2 or12 orabs ml3le 3tr2
      le3tr2 bile leid lerr an32 anabs ) CDCUADFGJHIUAZUBZUAZUBZUAZCDUCDXHCDXGU
      DZCFDKUAZUBZXHUAZXHCXKDUAZXLCXJFDUAZUBZXMCDFUAZEGUAZXQUBZUBZXOCXPXQUBXQUB
      XSRXPXQXQUEUFXSXJXNXSXPKUBZXJXTXSKXRXPSUGUHKXPDUIUJXSXPXNXPXRUKDFULUMUPUJ
      XOXJFUBZDUAXMDFXJDKUDUNYAXKDXJFUOUQUFUMDXHXKXIURUSXKXHXKFDFUBZGUAXEUAZUBZ
      XHXKFGDEUAZXDUBZUAZUBZYDXKFYGFXJUKZXKGXKUAYGXKGUCGYGXKGYFUDZXKYEXKGUAZUBZ
      YGUAZYGXKYLGUAZYMXKYKYEGUAZUBZYNXKYKYOXKGUDXKFDXRUAZUBZYOXJYQFKXRDSUTUGZY
      RYQYOFYQVAYQDXQUAZYOXRXQDXQXQUKZURYOYTDEGVBUHUMUSUJUPYPYKYEUBZGUAYNGYEYKG
      XKUCUNUUBYLGYKYEUOUQUFUMGYGYLYJURUSYLYGYGYLYFGUAZYGYLYFGYEUBZUAZUUCYLYEXD
      UUDUAZUBUUEYLYEUUFYEYKUKYLEEUAZGGUAZUBZYEFGUAZUBZUUDUAZUAZUUFYLYLUUGUUDUA
      ZUUHUBZUAZUUMYLYLUUGDXQUBZUAZUUHUBZUAZUUPYLDEUUQUAZUAZYKUBZEUVAUAZUUHUBZU
      AZUUTYEBGUAZUBZDAUAZUVGUBZEAUAZUUHUBZUAZYLUVFUVHUVGUVIEAGUAZUBZUAZUBZUVKU
      UHBUVNUBZUAZUBZUAZUVMUVHUVGUVIEDBUAZUBZUAZUBZUVKUUHBXQUBZUAZUBZUAZUWAUVHU
      VMEGBUAZUBZBEDUAZUBZUAZUAZUWIUVHUVHUVMUVHEBUAZUBZUAZUBZUWOUVHUVHUWPUVHUVM
      UBZUAZUBZUWSUVHUVHXQBUAZUBUWLBUAZUBZUXBUVHUVHUXCUXDUBZUBZUXEUXGUVHUVHUXFU
      VHUWJUWLUBZUXFUVHUWLUWJUBZUXHYEUWLUVGUWJDEVCBGVCVDZUWLUWJUOUFUWJUXCUWLUXD
      GXQBGEUCVEUWLBUDVFUJVGUHUXEUXGUVHUXCUXDUEZUHUFUXEUXGUXBUXKUXFUXAUVHUXFUWP
      XQUWBUBZUAZUXAUXFUXLEUAZBUAZUXLUWPUAUXMUXFUWBEUAZUXCUBZUXPXQUBZBUAUXOUXFU
      XCUXPUBUXQUXDUXPUXCUXDYEBUAUXPUWLYEBEDVCUQDEBVJUFUGUXCUXPUOUFBXQUXPBUWBEB
      DUCVHUNUXRUXNBUXRXQUXPUBUXNUXPXQUOEUWBXQEGUDZUNUFUQVIUXLEBVKUXLUWPULVIUWP
      UXAUXLUWPUWTUDUXLUXLUVNUBZUXAUXLUXTUXTUXTUXLUXLUVNUXLUWBXQUBZUVNUYAUXLUWB
      XQUOUHUYADYRUAZXQUBZUVNUWBUYBXQBYRDBXKYRQYSUFUTVLUYCDVMYQUBZUAZXQUBZUVNUY
      BUYEXQYRUYDDFVMYQFVNVOURVOUYFXQUUQUAZUVNUYFXRUUQUAZUYGUYFXRDUAZXQUBUYHUYE
      UYIXQUYEDYQUAZDDUAZXRUAZUYIUYDYQDYQVPUTUYLUYJDDXRVKUHUYLYQUYIUYKDXRDVQUQD
      XRULUFVIVLXRDXQUUAVRUFXRXQUUQXQXQVAVEUJUYGUVAGUAZUVNEGUUQVJUVNUYMAUVAGPUQ
      UHUFUMUSUJUJZVGUHUXTUXTUXTVSZUHUFUXTEDAGBGUVJUVLUVHUVJVSZUVLVSZYEUWLUVGUW
      JDEULBGULVDUYOVTUJWAUJWDUJUJUXBUWQUWTUAUWQUVMUVHUBZUAZUWSUVHUWPUVMWBUWTUY
      RUWQUVHUVMUOUTUYSUWQUVMUAZUVHUBUVHUYTUBUWSUVHUVMUWQUVHUWPUKWCUYTUVHUOUYTU
      WRUVHUWQUVMVCUGVIVIUMUWSUWTUWNUAZUWOUWSUWTUWQUAVUAUVHUVMUWPWBUWQUWNUWTUWQ
      UXIUWPUBUWLUWJUWPUBZUBZUWNUVHUXIUWPUXJVLUWLUWJUWPUEVUCUWLBUWKUAZUBUWLBUBZ
      UWKUAZUWNVUBVUDUWLVUBUWJEUBZBUABVUGUAVUDBEUWJBGUCUNVUGBULVUGUWKBUWJEUOUTV
      IUGUWKBUWLEUWJDWEUNVUFUWKVUEUAUWNVUEUWKULVUEUWMUWKUWLBUOUTUFVIVIUTUFUWTUV
      MUWNUVHUVMVAVEUJUSUWOUVGUVIUWMUAZUBZUVKUUHUWKUAZUBZUAZUWIUWOUVMUWMUWKUAZU
      AZUVGUVIUBZUWMUAZUVLUWKUAZUAZVULUWNVUMUVMUWKUWMULUTVUNUVJUWMUAZVUQUAVURUV
      JUVLUWMUWKWFVUSVUPVUQVUQUVJVUOUWMUVJUVJVUOUYPUVIUVGUOUFZUQUVLUVLUWKUYQUQW
      GUFVUPVUIVUQVUKUVGUVIUWMBUWLGWEWHUVKUUHUWKEUWJAWEWHWGVIVUIUWEVUKUWHVUHUWD
      UVGVUHDUWMUAZAUADUWCUAZAUAUWDDAUWMVJVVAVVBAVVADEBDUAZUBZUAVVBDBEWIVVDUWCD
      VVCUWBEBDULUGUTUFUQDUWCAVJVIUGVUJUWGUVKVUJGUWKUAZGUAGUWFUAZGUAUWGGGUWKVJV
      VEVVFGVVEGEUVGUBZUAVVFUWKVVGGUWJUVGEGBULUGUTGEBWIUFUQGUWFGVJVIUGWGUFUMUWE
      UVQUWHUVTUWDUVPUVGUWCUVOUVIUWCEUVNEUWBUKUWCUXLUVNEXQUWBUXSVOUYNUSUPURWDUW
      GUVSUVKUWFUVRUUHUWFBUVNBXQUKUWFUXLUVNUWFXQUWBBXQVABXQDWJUPUYNUSUPURWDWKUS
      UWAUVGUVIGUVKUBZUAZUBZUVKUUHAUVGUBZUAZUBZUAUVJVVHUAZUVLVVKUAZUAZUVMUVQVVJ
      UVTVVMUVPVVIUVGDAUVOUAZUADAVVHUAZUAUVPVVIVVQVVRDVVQAEGAUAZUBZUAVVRUVOVVTA
      UVNVVSEAGVCUGUTAEGWIUFUTDAUVOVKDAVVHVKWLUGUVSVVLUVKGGUVRUAZUAGGVVKUAZUAUV
      SVVLVWAVWBGGBAWIUTGGUVRVKGGVVKVKWLUGWGVVJVVNVVMVVOVVJVUOVVHUAZVVNVVHUVIUV
      GGUVKBWJUNVVNVWCUVJVUOVVHVUTUQUHUFVVMVVOVVOVVKUUHUVKAUVGEWJUNVVOVVOUVLUVL
      VVKUYQUQUHUFWGVVPUVMVVHVVKUAZUAVWDUVMUAUVMUVJVVHUVLVVKWFUVMVWDULVWDUVMVWD
      UVLUVJUAZUVMVVHUVLVVKUVJVVHUVKGUBUVLGUVKUOGUUHUVKGGUCWDUJAUVIUVGADUCVOWKV
      WEVWEUVMVWEVWEUVLUVLUVJUVJUYQUYPWGUHUVLUVJULUFUMWMVIVIUMUVGYKYEBXKGQUQZUG
      UVJUVCUVLUVEUVIUVBUVGYKAUVADPUTVWFVDUVKUVDUUHAUVAEPUTVLWGWRUVCYLUVEUUSUVB
      YEYKUVBEDUUQUAZUAUWLYEDEUUQWNVWGDEDXQWOUTEDULVIVLUUSUVEUURUVDUUHEEUUQVKVL
      UHWGUMUUSUUOYLUURUUNUUHUUREEUUDUAZUAZUUNUUREEDGEUAZUBZUAZUAZVWIUURUUGVWKU
      AVWMUUGUUGUUQVWKEEVCZXQVWJDEGVCUGWGEEVWKVKUFVWLVWHEEDGWPURUJVWIUUNUUNUUNV
      WIEEUUDVKUHUUGUUGUUDVWNUQUFUMVOURUSUUPUUKUUIUUDUAZUAUUMYLUUKUUOVWOYKUUJYE
      XKFGYIVEWDUUOVWOUUHUUNUBUUHUUGUBZUUDUAUUOVWOUUDUUGUUHGYEGWEUNUUHUUNUOVWPU
      UIUUDUUHUUGUOUQWQWSWKUUKUUIUUDWNUMUSUUMHIUUDUAZUAZUUFVWRUUMHUUIVWQUULMIUU
      KUUDNUQWGUHUUFVWRHIUUDVKUHUFUMUPUUDXDYEGYEVAUNUMUUDGYFGYEUKURUSYFGULUMYGW
      TWAUSWAUSUPYDYHYDXGYHYCXFFYCYBXEUAZGUAGVWSUAXFYBGXEVJVWSGULVWSXEGYBXEYBJX
      DYBUUKJDYEFUUJDEUDFGUDVFZJUUKOUHUMYBIHYBUUKIVWTIUUKNUHUMXAUPWMUTVIUGXGFUU
      JYGUBZUBZFUUJUBZYGUBZYHXFVXAFXFGYFUUJUBZUAYGUUJUBVXAXEVXEGXEUUKXDUBVXEJUU
      KXDOVLYEUUJXDXBUFUTUUJYFGGFUCWCYGUUJUOVIUGVXDVXBFUUJYGUEUHVXCFYGFGXCVLVIU
      FUHUMYDYBXGUAZXHYDFXFYBUAZUBXGYBUAVXFYCVXGFYCYBXFUAVXGYBGXEVKYBXFULUFUGYB
      XFFDFVAUNXGYBULVIYBDXGDFUKVEUJUSWMUMWAUS $.
  $}

  ${
    oadp35lem.1 $e |- c0 = ( ( a1 v a2 ) ^ ( b1 v b2 ) ) $.
    oadp35lem.2 $e |- c1 = ( ( a0 v a2 ) ^ ( b0 v b2 ) ) $.
    oadp35lem.3 $e |- c2 = ( ( a0 v a1 ) ^ ( b0 v b1 ) ) $.
    oadp35lem.4 $e |- p0 = ( ( a1 v b1 ) ^ ( a2 v b2 ) ) $.
    oadp35lem.5 $e |- p = ( ( ( a0 v b0 ) ^ ( a1 v b1 ) ) ^ ( a2 v b2 ) ) $.
    $( Part of proof (3)=>(5) in Day/Pickering 1982.  (Contributed by NM,
       12-Jul-2015.) $)
    oadp35lemg $p |- p
        =< ( a0 v ( b0 ^ ( b1 v ( c2 ^ ( c0 v c1 ) ) ) ) ) $=
      ( dp53 ) ABCDEFGHIJLMNPQ $.

    $( Part of proof (3)=>(5) in Day/Pickering 1982.  (Contributed by NM,
       12-Jul-2015.) $)
    oadp35lemf $p |- ( a0 v p )
        =< ( a0 v ( b0 ^ ( b1 v ( c2 ^ ( c0 v c1 ) ) ) ) ) $=
      ( wo wa leo oadp35lemg lel2or ) BBEFJHIQRQRZQABUBSABCDEFGHIJKLMNOPTUA $.

    $( Part of proof (3)=>(5) in Day/Pickering 1982. $)
$(
    oadp35leme $p |- ( b0 ^ ( a0 v p0 ) )
        =< ( a0 v ( b0 ^ ( b1 v ( c2 ^ ( c0 v c1 ) ) ) ) ) $=
      ? $.
$)

    $( Part of proof (3)=>(5) in Day/Pickering 1982. $)
$(
    oadp35lemd $p |- ( b0 ^ ( a0 v p0 ) )
        =< ( b0 ^ ( ( ( a0 ^ b0 ) v b1 ) v ( c2 ^ ( c0 v c1 ) ) ) ) $=
      ? $.
$)

    $( Part of proof (3)=>(5) in Day/Pickering 1982.  (Contributed by NM,
       12-Jul-2015.) $)
    oadp35lemc $p |- ( b0 ^ ( ( ( a0 ^ b0 ) v b1 ) v ( c2 ^ ( c0 v c1 ) ) ) )
        = ( b0 ^ ( b1 v ( c2 ^ ( c0 v c1 ) ) ) ) $=
      ( wa wo leo le2an or32 orcom cm lbtr lerr ler2an df-le2 lor 3tr lan ) BEQ
      ZFRJHIRZQZRZFUMRZEUNUKUMRZFRFUPRUOUKFUMUAUPFUBUPUMFUKUMUKJULUKBCRZEFRZQZJ
      BUQEURBCSEFSTJUSNUCUDUKIHUKBDRZEGRZQZIBUTEVABDSEGSTIVBMUCUDUEUFUGUHUIUJ
      $.

    $( Part of proof (3)=>(5) in Day/Pickering 1982. $)
$(
    oadp35lemb $p |- ( b0 ^ ( b1 v ( c2 ^ ( c0 v c1 ) ) ) )
        = ( b0 ^ ( b1 v ( ( a0 v a1 ) ^ ( c0 v c1 ) ) ) ) $=
      ? $.
$)

    $( Part of proof (3)=>(5) in Day/Pickering 1982. $)
$(
    oadp35lembb $p |- ( b0 ^ ( a0 v p0 ) )
        =< ( b0 ^ ( b1 v ( ( a0 v a1 ) ^ ( c0 v c1 ) ) ) ) $=
      ( wo wa oadp35lemd oadp35lemc oadp35lemb tr lbtr )
      EBKQREBERFQJHIQZRZQRZEFBCQUD
      RQRZABCDEFGHIJKLMNOPSUFEFUEQRUGABCDEFGHIJKLMNOPTABCDEFGHIJKLMNOPUAUBUC $.
$)

    $( Part of proof (3)=>(5) in Day/Pickering 1982. $)
$(
    oadp35lema $p |- ( b1 v ( b0 ^ ( a0 v p0 ) ) )
       =< ( b1 v ( ( a0 v a1 ) ^ ( c0 v c1 ) ) ) $=
    ( wo wa leo oadp35lembb lear letr lel2or ) FFBCQHIQRZQZEBKQRZFUDSUFEUERUEAB
      CDEFGHIJKLMNOPTEUEUAUBUC $.
$)

    $( Part of proof (3)=>(5) in Day/Pickering 1982. $)
$(
    oadp35lem0 $p |- ( ( a0 v a1 ) ^ ( ( b0 ^ ( a0 v p0 ) ) v b1 ) )
                  =< ( ( c0 v c1 ) v ( b1 ^ ( a0 v a1 ) ) ) $=
      ? $.
$)
  $}

  ${
    oadp35.1 $e |- c0 = ( ( a1 v a2 ) ^ ( b1 v b2 ) ) $.
    oadp35.2 $e |- c1 = ( ( a0 v a2 ) ^ ( b0 v b2 ) ) $.
    oadp35.3 $e |- p0 = ( ( a1 v b1 ) ^ ( a2 v b2 ) ) $.
    $( Part of theorem from Alan Day and Doug Pickering, "A note on the
       Arguesian lattice identity," Studia Sci.  Math.  Hungar. 19:303-305
       (1982).  (3)=>(5) (Contributed by NM, 12-Apr-2012.) $)
    oadp35 $p |- ( ( a0 v a1 ) ^ ( ( b0 ^ ( a0 v p0 ) ) v b1 ) )
                  =< ( ( c0 v c1 ) v ( b1 ^ ( a0 v a1 ) ) ) $=
      ( wo wa id dp35lem0 ) ADMBEMNCFMNZABCDEFGHABMDEMNZIJKROLQOP $.
  $}

  $( A modular law experiment.  (Contributed by NM, 21-Apr-2012.) $)
  testmod $p |- ( ( ( c v a ) v ( ( b v c ) ^ ( d v a ) ) )
             ^ ( a v ( b ^ ( d v ( ( a v c ) ^ ( b v d ) ) ) ) ) )
     = ( ( b ^ ( ( ( ( a v c ) v ( ( b v c
            ) ^ ( d v a ) ) ) ^ d ) v ( ( a v c ) ^ ( b v d ) ) ) ) v a ) $=
    ( wo wa leao1 mli orass ran tr lan ror an12 leo orcom or32 2an 3tr cm ) BAC
    EZBCEDAEFZEZDFUABDEZFZEZFZAEZCAEUBEZABDUEEZFZEZFZUHACUBEZEZUKFZAEZUOUKAEZFU
    MUHBUOUJFZFZAEUQUGUTAUFUSBUFUCUJFUSUCDUEUAUDUBGHUCUOUJACUBIJKLMUTUPABUOUJNM
    KUOUKAAUNOHUOUIURULUOUNAEUIAUNPCUBAQKUKAPRST $.

  $( A modular law experiment.  (Contributed by NM, 21-Apr-2012.) $)
  testmod1 $p |- ( ( ( c v a ) v ( ( b v c ) ^ ( d v a ) ) )
             ^ ( a v ( b ^ ( d v ( ( a v c ) ^ ( b v d ) ) ) ) ) )
     = ( a v ( b ^ ( ( ( a v c ) ^ ( b v d ) )
         v ( d ^ ( ( a v c ) v ( ( b v c ) ^ ( d v a ) ) ) ) ) ) ) $=
    ( wo wa testmod orcom ancom lor tr lan ) CAEBCEDAEFZEABDACEZBDEFZEFEFBNMEZD
    FZOEZFZAEZABODPFZEZFZEZABCDGTASEUDSAHSUCARUBBROQEUBQOHQUAOPDIJKLJKK $.

  $( A modular law experiment.  (Contributed by NM, 21-Apr-2012.) $)
  testmod2 $p |- ( ( a v b ) ^ ( a v ( c v d ) ) )
     = ( a v ( b ^ ( ( ( a v c ) ^ ( b v d ) )
         v ( d ^ ( ( a v c ) v ( ( b v c ) ^ ( d v a ) ) ) ) ) ) ) $=
    ( wo wa orass lan cm leo ler mlduali leor df2le2 ran anass ancom orcom lor
    tr ler2an an32 mldual2i ror lea leror l42modlem1 2an leao1 ) ABEZACDEEZFZAB
    ACEZDEZFZEZABUMBDEZFZDUMBCEZDAEZFZEZFEZFZEULUJUNFZUPVEULUNUKUJACDGHIABUNAUM
    DACJKLTUOVDAUOBUQUMBEZFZUNFZFZVDUOBVGFZUNFZVIVKUOVJBUNBVGBUQVFBDJBUMMUANOIB
    VGUNPTVHVCBVHURDEZVBFZVCVHVLUNVFFZFZVMVHVLUNFZVFFZVOVHVLVFFZVQVHUQUNFZVFFVR
    UQVFUNUBVSVLVFVSUQUMFZDEVLDUMUQDBMUCVTURDUQUMQUDTOTVQVRVPVLVFVLUNURUMDUMUQU
    EUFNOITVLUNVFPTVNVBVLVNUMADEZCBEZFZEVBACDBUGWCVAUMWCUTUSFVAWAUTWBUSADRCBRUH
    UTUSQTSTHTURDVBUMUQVAUILTHTST $.

  $( A modular law experiment.  (Contributed by NM, 21-Apr-2012.) $)
  testmod2expanded $p |- ( ( a v b ) ^ ( a v ( c v d ) ) )
     = ( a v ( b ^ ( ( ( a v c ) ^ ( b v d ) )
         v ( d ^ ( ( a v c ) v ( ( b v c ) ^ ( d v a ) ) ) ) ) ) ) $=
    ( wo wa orass lan cm leo ler mlduali leor df2le2 ran lor anass ancom orcom
    tr ler2an an32 mldual2i ror lea leror l42modlem1 2an leao1 ) ABEZACDEEZFZAB
    ACEZBDEZFZDEZUMBCEZDAEZFZEZFZFZEZABUODUTFEZFZEULABUPUMADEZCBEZFZEZFZFZEZVCU
    LABUPUMDEZUMBEZFZFZFZEZVLULABUPVNFZFZEZVRULABUNUMFZDEZVNFZFZEZWAULABUNVMFZV
    NFZFZEZWFULABUNVNFZVMFZFZEZWJULABWKFZVMFZEZWNULABVMFZEZWQULUJVMFZWSWTULVMUK
    UJACDGHIABVMAUMDACJKLTWRWPAWPWRWOBVMBWKBUNVNBDJBUMMUANOIPTWPWMABWKVMQPTWMWI
    AWLWHBUNVNVMUBHPTWIWEAWHWDBWGWCVNDUMUNDBMUCOHPTWEVTAWDVSBWCUPVNWBUODUNUMRUD
    OHPTVTVQAVSVPBVSUPVMFZVNFZVPXBVSXAUPVNUPVMUOUMDUMUNUEUFNOIUPVMVNQTHPTVQVKAV
    PVJBVOVIUPACDBUGHHPTVKVBAVJVABVIUTUPVHUSUMVHURUQFUSVFURVGUQADSCBSUHURUQRTPH
    HPTVBVEAVAVDBUODUTUMUNUSUILHPT $.

  $( A modular law experiment.  (Contributed by NM, 21-Apr-2012.) $)
  testmod3 $p |- ( ( ( c v a ) v ( ( b v c ) ^ ( d v a ) ) )
             ^ ( a v ( b ^ ( d v ( ( a v c ) ^ ( b v d ) ) ) ) ) )
      = ( a v ( ( ( c v a ) v ( ( b v c ) ^ ( d v
              a ) ) ) ^ ( b ^ ( d v ( ( a v c ) ^ ( b v d ) ) ) ) ) ) $=
    ( wo wa orcom leor ler mli tr lan cm ) ACAEZBCEDAEFZEZBDACEBDEFEFZFZEZPAQEZ
    FZSPQAEZFZUASRAEUCARGPQAANOACHIJKUBTPQAGLKM $.

  $( A modular law experiment.  (Contributed by NM, 22-Apr-2012.) $)
$(
  testmod4 $p |- ( ( ( c v a ) v ( ( b v c ) ^ ( d v a ) ) )
             ^ ( a v ( b ^ ( d v ( ( a v c ) ^ ( b v d ) ) ) ) ) )
      = ( a v ( ( ( c v a ) v ( ( b v c ) ^ ( d v
              a ) ) ) ^ ( b ^ ( d v ( ( a v c ) ^ ( b v d ) ) ) ) ) ) $=
    ( wvx wvr wvy wvq wvp wo wa leo id lor lan lear lea lelor ax-a3 cm lbtr
    letr bltr ler2an leor mldual2i ancom ror tr orcom leid lel2or lebi ) CAJBCJ
    DAJKJZABDACJBDJKJKZJKEFAGJZHKZJZKZAUNUOKJZ?UTUSUTGFAJZIKZJZUS?VCUS?USVAUSGJ
    ZKZVCJZVCUSVEGJZVFUSVDVAGJZKZVGUSVDVHUSGLUSUSVHURUREUQUQFUQMNOUSURVHEURPURF
    UPJZVHUQUPFUPHQRVHVJFAGSTUAUBUCUDVIVDVAKZGJVGGVAVDGUSUEUFVKVEGVDVAUGUHUIUAG
    VCVEGVBLRUBVEVCVCVEVBGJZVCVEVBGVAKZJZVLVEVAIVMJZKVNVEVAVOVAVDQ?UDVMIVAGVAPU
    FUAVMGVBGVAQRUBVBGUJUAVCUKULUBUMUITUI $.
$)
