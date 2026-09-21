$[ set-main.mm $]
$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Mathbox for Adrian Ducourtial
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Propositional calculus
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Biconditional version of Curry's paradox.  If some proposition ` ph `
     amounts to the self-referential statement "This very statement is
     equivalent to ` ps ` ", then ` ps ` is true.  See ~ bj-currypara in BJ's
     mathbox for the classical version.  (Contributed by Adrian Ducourtial,
     18-Mar-2025.) $)
  currybi $p |- ( ( ph <-> ( ph <-> ps ) ) -> ps ) $=
    ( wb biid biass biimpri mpbii ) AABCCZAACZBADIBCHAABEFG $.

  $( Suppose ` ph ` , ` ps ` are distinct atomic propositional formulas, and
     let ` _G ` be the smallest class of formulas for which ` T. e. _G ` and
     ` ( ch -> ph ) ` , ` ( ch -> ps ) e. _G ` for ` ch e. _G ` .  The present
     theorem is then an element of ` _G ` , and the implications occurring in
     the theorem are in one-to-one correspondence with the formulas in ` _G `
     up to logical equivalence.  In particular, the theorem itself is
     equivalent to ` T. e. _G ` .  (Contributed by Adrian Ducourtial,
     2-Oct-2025.) $)
  antnest $p |- ( ( ( ( ( ( T. -> ph ) -> ps ) -> ps ) -> ph ) -> ps ) -> ps )
    $=
    ( wtru wi wn simplim conax1 mtod syl syl11 mptru pm2.65i notnotri ) CADZBDZ
    BDZADZBDZBDZSEZATADOECATNBFTOBRBGZTQEZPTQBUARBFHZPAFIHJKTUBAEUCPAGILM $.

  $( Lemma for ~ antnestlaw3 .  (Contributed by Adrian Ducourtial,
     5-Dec-2025.) $)
  antnestlaw3lem $p |- ( -. ( ( ( ph -> ps ) -> ch ) -> ch ) -> -. ( ( ( ph ->
    ch ) -> ps ) -> ps ) ) $=
    ( wi wn conax1 simplim mtod syl jcnd pm2.21d ) ABDZCDZCDEZACDZBDBNOBNACNLEZ
    ANLCMCFZMCGHZABGIQJKNPBERABFIJ $.

  $( A law of nested antecedents.  The converse direction is a subschema of
     ~ pm2.27 .  (Contributed by Adrian Ducourtial, 5-Dec-2025.) $)
  antnestlaw1 $p |- ( ( ( ( ph -> ps ) -> ps ) -> ps ) <-> ( ph -> ps ) ) $=
    ( wi wn pm2.21 conax1 jcnd con4i pm2.27 impbii ) ABCZBCZBCZKKMKDLBKBEABFGHK
    BIJ $.

  $( A law of nested antecedents.  (Contributed by Adrian Ducourtial,
     5-Dec-2025.) $)
  antnestlaw2 $p |- ( ( ( ( ph -> ps ) -> ps ) -> ch ) <-> ( ( ( ph -> ch ) ->
    ps ) -> ch ) ) $=
    ( wi wn pm2.27 pm2.21 simplim sylcom a1dd pm2.61i conax1 jcnd con4i syl5com
    a1d con3 syl6 pm2.521g2 mpd mpdd jcn a1i impbii ) ABDZBDZCDZACDZBDZCDZUJUGU
    JEZUFCAUKUFDAUFUKABFPAEZUKBUEULUKUHBULUHUKACGPUICHIJKUICLMNUGUJUGEZCEZUKUFC
    LZUMUIUNUKDZUMUHUEBUMUHULUEUMUNUHULUOACQOABGRUFCUHSUAUIUPDUMUICUBUCTTNUD $.

  $( A law of nested antecedents.  Compare with ~ looinv .  (Contributed by
     Adrian Ducourtial, 5-Dec-2025.) $)
  antnestlaw3 $p |- ( ( ( ( ph -> ps ) -> ch ) -> ch ) <-> ( ( ( ph -> ch ) ->
    ps ) -> ps ) ) $=
    ( wi antnestlaw3lem con4i impbii ) ABDCDCDZACDBDBDZIHACBEFHIABCEFG $.

  $( Alternative proof of ~ antnest from the valid schema
     ` ( ( ( ( T. -> ph ) -> ph ) -> ps ) -> ps ) ` using laws of nested
     antecedents.  Our proof uses only the laws ~ antnestlaw1 and
     ~ antnestlaw3 .  (Contributed by Adrian Ducourtial, 5-Dec-2025.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  antnestALT $p |- ( ( ( ( ( ( T. -> ph ) -> ps ) -> ps ) -> ph ) -> ps ) -> ps
    ) $=
    ( wtru wi pm2.27 syl mptru antnestlaw3 antnestlaw1 imbi1i bitr4i bitri mpbi
    ) CADZADZBDBDZNBDZBDZADBDBDZPCOPCAEOBEFGPRBDZADZADZSPQADZADUBNABHUAUCATQANB
    IJJKRBAHLM $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Clone theory
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Token for the function of the class of operations on a set. $)
  $c CloneOp $.

  $( Syntax for the function of the class of operations on a set. $)
  ccloneop $a class CloneOp $.

  ${
    $d a n x $.
    $( Define the function that sends a set to the class of clone-theoretic
       operations on the set.  For convenience, we take an operation on ` a `
       to be a function on finite sequences of elements of ` a ` (rather than
       tuples) with values in ` a ` .  Following line 6 of [Szendrei] p. 11,
       the arity ` n ` of an operation (here, the length of the sequences at
       which the operation is defined) is always finite and nonzero, whence
       ` n ` is taken to be a nonzero finite ordinal.  (Contributed by Adrian
       Ducourtial, 3-Apr-2025.) $)
    df-cloneop $a |- CloneOp = ( a e. _V |-> { x | E. n e. ( _om \ 1o ) x e. (
                  a ^m ( a ^m n ) ) } ) $.
  $}

  $( Token for the function of projections on sets. $)
  $c prj $.

  $( Syntax for the function of projections on sets. $)
  cprj $a class prj $.

  ${
    $d a i n x $.
    $( Define the function that, for a set ` a ` , arity ` n ` , and index
       ` i ` , returns the ` i ` -th ` n ` -ary projection on ` a ` .  This is
       the ` n ` -ary operation on ` a ` that, for any sequence of ` n `
       elements of ` a ` , returns the element having index ` i ` .
       (Contributed by Adrian Ducourtial, 3-Apr-2025.) $)
    df-prj $a |- prj = ( a e. _V |-> ( n e. ( _om \ 1o ) , i e. n |-> ( x e. (
              a ^m n ) |-> ( x ` i ) ) ) ) $.
  $}

  $( Token for the function of superpositions. $)
  $c suppos $.

  $( Syntax for the function of superpositions. $)
  csuppos $a class suppos $.

  ${
    $d a f g i m n x $.
    $( Define the function that, when given an ` n ` -ary operation ` f ` and
       ` n ` many ` m ` -ary operations ` ( g `` (/) ) ` , ...,
       ` ( g `` U. n ) ` , returns the superposition of ` f ` with the
       ` ( g `` i ) ` , itself another ` m ` -ary operation on ` a ` .  Given
       ` x ` (a sequence of ` m ` arguments in ` a ` ), the superposition
       effectively applies each of the ` ( g `` i ) ` to ` x ` , then applies
       ` f ` to the resulting sequence of ` n ` function values.  This can be
       seen as a generalized version of function composition; see paragraph 3
       of [Szendrei] p. 11.  (Contributed by Adrian Ducourtial, 3-Apr-2025.) $)
    df-suppos $a |- suppos = ( a e. _V |-> ( n e. ( _om \ 1o ) , m e. ( _om \
                   1o ) |-> ( f e. ( a ^m ( a ^m n ) ) , g e. ( ( a ^m ( a ^m m
                   ) ) ^m n ) |-> ( x e. ( a ^m m ) |-> ( f ` ( i e. n |-> ( (
                   g ` i ) ` x ) ) ) ) ) ) ) $.
  $}

$( (End of Adrian Ducourtial's mathbox.) $)
