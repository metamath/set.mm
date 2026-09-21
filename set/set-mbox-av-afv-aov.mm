$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Alternative definitions of function and operation values
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  The current definition of the value ` ( F `` A ) ` of a function ` F ` at an
  argument ` A ` (see ~ df-fv ) assures that this value is always a set, see
  ~ fex .  This is because this definition can be applied to any classes ` F `
  and ` A ` , and evaluates to the empty set when it is not meaningful (as
  shown by ~ ndmfv and ~ fvprc ).

  Although it is very convenient for many theorems on functions and their
  proofs, there are some cases in which from ` ( F `` A ) = (/) ` alone it
  cannot be decided/derived whether ` ( F `` A ) ` is meaningful ( ` F ` is
  actually a function which is defined for ` A ` and really has the function
  value ` (/) ` at ` A ` ) or not.  Therefore, additional assumptions are
  required, such as ` (/) e/ ran F ` , ` (/) e. ran F ` or
  ` Fun F /\ A e. dom F ` (see, for example, ~ ndmfvrcl ).

  To avoid such an ambiguity, an alternative definition ` ( F ''' A ) ` (see
  ~ df-afv ) would be possible which evaluates to the universal class
  ( ` ( F ''' A ) = _V ` ) if it is not meaningful (see ~ afvnfundmuv ,
  ~ ndmafv , ~ afvprc and ~ nfunsnafv ), and which corresponds to the current
  definition ( ` ( F `` A ) = ( F ''' A ) ` ) if it is (see ~ afvfundmfveq ).
  That means ` ( F ''' A ) = _V -> ( F `` A ) = (/) ` (see ~ afvpcfv0 ), but
  ` ( F `` A ) = (/) -> ( F ''' A ) = _V ` is not generally valid.

  In the theory of partial functions, it is a common case that ` F ` is not
  defined at ` A ` , which also would result in ` ( F ''' A ) = _V ` .  In this
  context we say ` ( F ''' A ) ` "is not defined" instead of "is not
  meaningful".

  With this definition the following intuitive equivalence holds:
  ` ( F ''' A ) e. _V ` <-> " ` ( F ''' A ) ` is meaningful/defined".

  An interesting question would be if ` ( F `` A ) ` could be replaced by
  ` ( F ''' A ) ` in most of the theorems based on function values.  If we look
  at the (currently 19) proofs using the definition ~ df-fv of ` ( F `` A ) `,
  we see that analogues for the following 8 theorems can be proven using the
  alternative definition: ~ fveq1 -> ~ afveq1 , ~ fveq2 -> ~ afveq2 ,
  ~ nffv -> ~ nfafv , ~ csbfv12 -> csbafv12g , ~ fvres -> ~ afvres ,
  ~ rlimdm -> ~ rlimdmafv , ~ tz6.12-1 -> ~ tz6.12-1-afv , ~ fveu -> ~ afveu .

  Three theorems proved by directly using ~ df-fv are within a mathbox
  ( ~ fvsb ) or not used ( ~ isumclim3 , ~ avril1 ).

  However, the remaining 8 theorems proved by directly using ~ df-fv are used
  more or less often:

  * ~ fvex : used in about 1750 proofs.

  * ~ tz6.12-1 : root theorem of many theorems which have not a strict
  analogue, and which are used many times: ~ fvprc (used in about 127 proofs),
  ~ tz6.12i (used - indirectly via ~ fvbr0 and ~ fvrn0 - in 18 proofs, and in
  ~ fvclss used in ~ fvclex used in ~ fvresex , which is not used!), ~ dcomex
  (used in 4 proofs), ~ ndmfv (used in 86 proofs) and ~ nfunsn (used by ~ dffv2
  which is not used).

  * ~ fv2 : only used by ~ elfv , which is only used by ~ fv3 , which is not
  used.

  * ~ dffv3 : used by ~ dffv4 (the previous "df-fv"), which now is only used in
  deprecated (usage discouraged) theorems or within mathboxes
  ( ~ csbfv12gALTVD ), by ~ shftval (itself used in 9
  proofs), by ~ dffv5 (mathbox) and by ~ fvco2 , which has the analogue
  ~ afvco2 .

  * ~ fvopab5 : used only by ~ ajval (not used) and by ~ adjval (used -
  indirectly - in 9 proofs).

  * ~ zsum : used (via ~ isum , ~ sum0 and ~ fsumsers ) in more than 90 proofs.

  * ~ isumshft : used in ~ pserdv2 and (via ~ logtayl ) 4 other proofs.

  * ~ ovtpos : used in 14 proofs.

  As a result of this analysis we can say that the current definition of a
  function value is crucial for Metamath and cannot be exchanged easily with an
  alternative definition. While ~ fv2 , ~ dffv3 , ~ fvopab5 , ~ zsum ,
  ~ isumshft and ~ ovtpos are not critical or are, hopefully, also valid for
  the alternative definition, ~ fvex and ~ tz6.12-1 (and the theorems based on
  them) are essential for the current definition of function values.

  With the same arguments, an alternative definition of operation values
  ` (( A O B )) ` could be meaningful to avoid ambiguities, see ~ df-aov .

  For additional details, see
  ~ https://groups.google.com/g/metamath/c/cteNUppB6A4 .

$)

$( *** Definition moved to the front so that the text above will appear
   in the html output! *** $)

  $c defAt $. $( "defined at" predicate $)
  $c ''' $. $( Threefold straight apostrophe (function value symbol) $)
  $c (( $.  $( Double left parenthesis $)
  $c )) $.  $( Double right parenthesis $)

  $( Extend the definition of a wff to include the "defined at" predicate.
     Read:  "(the function) ` F ` is defined at (the argument) ` A ` ".  In a
     previous version, the token "def@" was used.  However, since the @ is used
     (informally) as a replacement for $ in commented out sections that may be
     deleted some day.  While there is no violation of any standard to use the
     @ in a token, it could make the search for such commented-out sections
     slightly more difficult.  (See remark of Norman Megill at
     ~ https://groups.google.com/g/metamath/c/cteNUppB6A4 ). $)
  wdfat $a wff F defAt A $.

  $( Extend the definition of a class to include the value of a function.
     Read:  "the value of ` F ` at ` A ` " or " ` F ` of ` A ` ".  In a
     previous version, the symbol " ' " was used.  However, since the
     similarity with the symbol ` `` ` used for the current definition of a
     function's value (see ~ df-fv ), which, by the way, was intended to
     visualize that in many cases ` `` ` and " ' " are exchangeable, makes
     reading the theorems, especially those which use both definitions as
     ~ dfafv2 , very difficult, 3 apostrophes ` ''' ` are used now so that it's
     easier to distinguish from ~ df-fv and ~ df-ima .  And not three backticks
     ( three times ` `` ` ) since that would be annoying to escape in a
     comment.  (See remark of Norman Megill and Gerard Lang at
     ~ https://groups.google.com/g/metamath/c/cteNUppB6A4 ). $)
  cafv $a class ( F ''' A ) $.

  $( Extend class notation to include the value of an operation ` F ` (such as
     ` + ` ) for two arguments ` A ` and ` B ` .  Note that the syntax is
     simply three class symbols in a row surrounded by a pair of parentheses in
     contrast to the current definition, see ~ df-ov . $)
  caov $a class (( A F B )) $.

  $( Definition of the predicate that determines if some class ` F ` is defined
     as function for an argument ` A ` or, in other words, if the function
     value for some class ` F ` for an argument ` A ` is defined.  We say that
     ` F ` is defined at ` A ` if a ` F ` is a function restricted to the
     member ` A ` of its domain.  (Contributed by Alexander van der Vekens,
     25-May-2017.) $)
  df-dfat $a |- ( F defAt A <-> ( A e. dom F /\ Fun ( F |` { A } ) ) ) $.

  ${
    $d x A $.  $d x F $.
    $( Alternative definition of the value of a function, ` ( F ''' A ) ` ,
       also known as function application.  In contrast to ` ( F `` A ) = (/) `
       (see ~ df-fv and ~ ndmfv ), ` ( F ''' A ) = _V ` if F is not defined for
       A!  (Contributed by Alexander van der Vekens, 25-May-2017.)  (Revised by
       BJ/AV, 25-Aug-2022.) $)
    df-afv $a |- ( F ''' A ) = ( iota' x A F x ) $.
  $}

  $( Define the value of an operation.  In contrast to ~ df-ov , the
     alternative definition for a function value (see ~ df-afv ) is used.  By
     this, the value of the operation applied to two arguments is the universal
     class if the operation is not defined for these two arguments.  There are
     still no restrictions of any kind on what those class expressions may be,
     although only certain kinds of class expressions - a binary operation
     ` F ` and its arguments ` A ` and ` B ` - will be useful for proving
     meaningful theorems.  (Contributed by Alexander van der Vekens,
     26-May-2017.) $)
  df-aov $a |- (( A F B )) = ( F ''' <. A , B >. ) $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Restricted quantification (extension)
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d X x $.  $d A x $.  $d ph x $.  $d th x $.
    ralbinrald.1 $e |- ( ph -> X e. A ) $.
    ralbinrald.2 $e |- ( x e. A -> x = X ) $.
    ralbinrald.3 $e |- ( x = X -> ( ps <-> th ) ) $.
    $( Elemination of a restricted universal quantification under certain
       conditions.  (Contributed by Alexander van der Vekens, 2-Aug-2017.) $)
    ralbinrald $p |- ( ph -> ( A. x e. A ps <-> th ) ) $=
      ( wral cv wceq wb adantl rspcdv wcel wa bicomd syl biimpd ralrimdva
      impbid ) ABDEJCABCDFEGDKZFLZBCMAINOACBDEAUCEPZQCBUECBMZAUEUDUFHUDBCIRSNTU
      AUB $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  The universal class (extension)
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( If a class is the universal class it doesn't belong to any class,
     generalization of ~ nvel .  (Contributed by Alexander van der Vekens,
     26-May-2017.) $)
  nvelim $p |- ( A = _V -> -. A e. B ) $=
    ( cvv wceq wcel nvel wb eleq1 eqcoms mtbii ) ACDCBEZABEZBFKLGCACABHIJ $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Introduce the Axiom of Power Sets (extension)
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( If a statement holds for all sets, there is not a unique set for which the
     statement holds.  (Contributed by Alexander van der Vekens,
     28-Nov-2017.) $)
  alneu $p |- ( A. x ph -> -. E! x ph ) $=
    ( weu wal wn wex eunex exnal sylib con2i ) ABCZABDZKAEBFLEABGABHIJ $.

  ${
    $d A y $.  $d V y $.
    $( If there is a unique second component in an ordered pair contained in a
       given set, the first component must be a set.  (Contributed by Alexander
       van der Vekens, 29-Nov-2017.) $)
    eu2ndop1stv $p |- ( E! y <. A , y >. e. V -> A e. _V ) $=
      ( cv cop wcel wex weu cvv euex wi nfeu1 nfcv nfel1 wn wa c0 opprc1 eleq1d
      nfim wal ax-5 alneu syl biimtrdi impcom wb eubidv notbid adantl mpbird ex
      con4d exlimi mpcom ) BADZEZCFZAGURAHZBIFZURAJURUSUTKAUSUTAURALABIABMNTURU
      TUSURUTOZUSOZURVAPVBQCFZAHZOZVAURVEVAURVCVEVAUQQCBUPRSZVCVCAUAVEVCAUBVCAU
      CUDUEUFVAVBVEUGURVAUSVDVAURVCAVFUHUIUJUKULUMUNUO $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Predicate "defined at"
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    dfateq12d.1 $e |- ( ph -> F = G ) $.
    dfateq12d.2 $e |- ( ph -> A = B ) $.
    $( Equality deduction for "defined at".  (Contributed by Alexander van der
       Vekens, 26-May-2017.) $)
    dfateq12d $p |- ( ph -> ( F defAt A <-> G defAt B ) ) $=
      ( cdm wcel cres wfun wa wdfat dmeqd eleq12d sneqd reseq12d funeqd df-dfat
      csn anbi12d 3bitr4g ) ABDHZIZDBTZJZKZLCEHZIZECTZJZKZLBDMCEMAUDUIUGULABCUC
      UHGADEFNOAUFUKADEUEUJFABCGPQRUABDSCESUB $.
  $}

  ${
    nfdfat.1 $e |- F/_ x F $.
    nfdfat.2 $e |- F/_ x A $.
    $( Bound-variable hypothesis builder for "defined at".  To prove a
       deduction version of this theorem is not easily possible because many
       deduction versions for bound-variable hypothesis builder for constructs
       the definition of "defined at" is based on are not available (e.g., for
       Fun/Rel, dom, ` C_ ` , etc.).  (Contributed by Alexander van der Vekens,
       26-May-2017.) $)
    nfdfat $p |- F/ x F defAt A $=
      ( wdfat cdm wcel csn cres wfun wa df-dfat nfdm nfel nfsn nfres nffun nfan
      nfxfr ) BCFBCGZHZCBIZJZKZLABCMUBUEAABUAEACDNOAUDACUCDABEPQRST $.
  $}

  ${
    $d x y A $.  $d x y F $.
    $( Alternate definition of the predicate "defined at" not using the ` Fun `
       predicate.  (Contributed by Alexander van der Vekens, 22-Jul-2017.)
       (Proof shortened by Peter Mazsa, 2-Oct-2022.) $)
    dfdfat2 $p |- ( F defAt A <-> ( A e. dom F /\ E! y A F y ) ) $=
      ( vx wdfat cdm wcel csn cres wfun wbr weu wral df-dfat wrel relres dffun8
      wa cv eubidv mpbiran anbi2i wb cvv brres elv a1i ralbidv eldmressnsn wceq
      eldmressn velsn biimpri breq1 anbi2d mpbirand ralbinrald pm5.32i 3bitri
      bitrd ) BCEBCFGZCBHZIZJZRVADSZASZVCKZALZDVCFZMZRVABVFCKZALZRBCNVDVJVAVDVC
      OVJCVBPDAVCQUAUBVAVJVLVAVJVEVBGZVEVFCKZRZALZDVIMVLVAVHVPDVIVAVGVOAVGVOUCZ
      VAVQAVBVEVFCUDUEUFUGTUHVAVPVLDVIBBCUIBVECUKVEBUJZVOVKAVRVOVMVKVMVRDBULUMV
      RVNVKVMVEBVFCUNUOUPTUQUTURUS $.
  $}

  $( A function is defined at any element of its domain.  (Contributed by AV,
     2-Sep-2022.) $)
  fundmdfat $p |- ( ( Fun F /\ A e. dom F ) -> F defAt A ) $=
    ( wfun cdm wcel wa csn cres wdfat funres anim1ci df-dfat sylibr ) BCZABDEZF
    OBAGZHCZFABINQOPBJKABLM $.

  $( A function is not defined at a proper class.  (Contributed by AV,
     1-Sep-2022.) $)
  dfatprc $p |- ( -. A e. _V -> -. F defAt A ) $=
    ( cvv wcel wn cdm csn cres wfun wo wdfat prcnel orcd ianor df-dfat xchnxbir
    wa sylibr ) ACDEZABFZDZEZBAGHIZEZJZABKZESUBUDATLMUAUCQUEUFUAUCNABOPR $.

  $( The value of a function ` F ` at a set ` A ` is in the range of the
     function ` F ` if ` F ` is defined at ` A ` .  (Contributed by AV,
     1-Sep-2022.) $)
  dfatelrn $p |- ( F defAt A -> ( F ` A ) e. ran F ) $=
    ( wdfat cdm wcel csn cres wfun cfv crn df-dfat funressndmfvrn ancoms sylbi
    wa ) ABCABDEZBAFGHZOABIBJEZABKQPRABLMN $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Alternative definition of the value of a function
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d x A $.  $d x F $.
    $( Alternative definition of ` ( F ''' A ) ` using ` ( F `` A ) ` directly.
       (Contributed by Alexander van der Vekens, 22-Jul-2017.)  (Revised by AV,
       25-Aug-2022.) $)
    dfafv2 $p |- ( F ''' A ) = if ( F defAt A , ( F ` A ) , _V ) $=
      ( vx cdm wcel cv wbr weu wa cfv cvv cif caiota wdfat cafv wceq wtru sylib
      cio wn df-fv simprr reuaiotaiota eqtrid eubrdm ancri con3i adantl aiotavb
      eqcomd ifeqda mptru wb dfdfat2 ifbi ax-mp df-afv 3eqtr4ri ) ABDEZACFBGZCH
      ZIZABJZKLZUTCMZABNZVCKLZABOVDVEPQVBVCKVEQVBIZVCUTCSZVECABUAVHVAVIVEPQUSVA
      UBUTCUCRUDQVBTZIZVEKVKVATZVEKPVJVLQVAVBVAUSABCUEUFUGUHUTCUIRUJUKULVFVBUMV
      GVDPCABUNVFVBVCKUOUPCABUQUR $.
  $}

  ${
    afveq12d.1 $e |- ( ph -> F = G ) $.
    afveq12d.2 $e |- ( ph -> A = B ) $.
    $( Equality deduction for function value, analogous to ~ fveq12d .
       (Contributed by Alexander van der Vekens, 26-May-2017.) $)
    afveq12d $p |- ( ph -> ( F ''' A ) = ( G ''' B ) ) $=
      ( wdfat cfv cvv cif cafv dfateq12d fveq12d ifbieq1d dfafv2 3eqtr4g ) ABDH
      ZBDIZJKCEHZCEIZJKBDLCELARTSUAJABCDEFGMABCDEFGNOBDPCEPQ $.
  $}

  $( Equality theorem for function value, analogous to ~ fveq1 .  (Contributed
     by Alexander van der Vekens, 22-Jul-2017.) $)
  afveq1 $p |- ( F = G -> ( F ''' A ) = ( G ''' A ) ) $=
    ( wceq id eqidd afveq12d ) BCDZAABCHEHAFG $.

  $( Equality theorem for function value, analogous to ~ fveq1 .  (Contributed
     by Alexander van der Vekens, 22-Jul-2017.) $)
  afveq2 $p |- ( A = B -> ( F ''' A ) = ( F ''' B ) ) $=
    ( wceq eqidd id afveq12d ) ABDZABCCHCEHFG $.

  ${
    nfafv.1 $e |- F/_ x F $.
    nfafv.2 $e |- F/_ x A $.
    $( Bound-variable hypothesis builder for function value, analogous to
       ~ nffv .  To prove a deduction version of this analogous to ~ nffvd is
       not easily possible because a deduction version of ~ nfdfat cannot be
       shown easily.  (Contributed by Alexander van der Vekens,
       26-May-2017.) $)
    nfafv $p |- F/_ x ( F ''' A ) $=
      ( cafv wdfat cfv cvv cif dfafv2 nfdfat nffv nfcv nfif nfcxfr ) ABCFBCGZBC
      HZIJBCKQARIABCDELABCDEMAINOP $.
  $}

  ${
    $d A y $.  $d B y $.  $d F y $.  $d x y $.
    $( Move class substitution in and out of a function value, analogous to
       ~ csbfv12 , with a direct proof proposed by Mario Carneiro, analogous to
       ~ csbov123 .  (Contributed by Alexander van der Vekens, 23-Jul-2017.) $)
    csbafv12g $p |- ( A e. V -> [_ A / x ]_ ( F ''' B )
                                = ( [_ A / x ]_ F ''' [_ A / x ]_ B ) ) $=
      ( vy cv cafv csb csbeq1 afveq12d eqeq12d vex nfcsb1v nfafv csbeq1a csbief
      wceq weq vtoclg ) AFGZCDHZIZAUACIZAUADIZHZRABUBIZABCIZABDIZHZRFBEUABRZUCU
      GUFUJAUABUBJUKUDUHUEUIAUABDJAUABCJKLAUAUBUFFMAUDUEAUADNAUACNOAFSCUDDUEAUA
      DPAUACPKQT $.
  $}

  $( If a class is a function restricted to a member of its domain, then the
     function value for this member is equal for both definitions.
     (Contributed by Alexander van der Vekens, 25-May-2017.) $)
  afvfundmfveq $p |- ( F defAt A -> ( F ''' A ) = ( F ` A ) ) $=
    ( wdfat cafv cfv cvv cif dfafv2 iftrue eqtrid ) ABCZABDKABEZFGLABHKLFIJ $.

  $( If a set is not in the domain of a class or the class is not a function
     restricted to the set, then the function value for this set is the
     universe.  (Contributed by Alexander van der Vekens, 26-May-2017.) $)
  afvnfundmuv $p |- ( -. F defAt A -> ( F ''' A ) = _V ) $=
    ( wdfat wn cafv cfv cvv cif dfafv2 iffalse eqtrid ) ABCZDABELABFZGHGABILMGJ
    K $.

  $( The value of a class outside its domain is the universe, compare with
     ~ ndmfv .  (Contributed by Alexander van der Vekens, 25-May-2017.) $)
  ndmafv $p |- ( -. A e. dom F -> ( F ''' A ) = _V ) $=
    ( wdfat cdm wcel cafv cvv wceq cres wfun df-dfat simplbi afvnfundmuv nsyl5
    csn ) ABCZABDEZABFGHPQBAOIJABKLABMN $.

  $( If the function value of a class for an argument is a set, the argument is
     contained in the domain of the class.  (Contributed by Alexander van der
     Vekens, 25-May-2017.) $)
  afvvdm $p |- ( ( F ''' A ) e. B -> A e. dom F ) $=
    ( cdm wcel cafv wn cvv wceq ndmafv nvelim syl con4i ) ACDEZACFZBEZNGOHIPGAC
    JOBKLM $.

  $( If the restriction of a class to a singleton is not a function, its value
     is the universe, compare with ~ nfunsn .  (Contributed by Alexander van
     der Vekens, 25-May-2017.) $)
  nfunsnafv $p |- ( -. Fun ( F |` { A } ) -> ( F ''' A ) = _V ) $=
    ( wdfat csn cres wfun cafv cvv wceq wcel df-dfat simprbi afvnfundmuv nsyl5
    cdm ) ABCZBADEFZABGHIPABOJQABKLABMN $.

  $( If the function value of a class for an argument is a set, the class
     restricted to the singleton of the argument is a function.  (Contributed
     by Alexander van der Vekens, 25-May-2017.) $)
  afvvfunressn $p |- ( ( F ''' A ) e. B -> Fun ( F |` { A } ) ) $=
    ( csn cres wfun cafv wcel wn cvv wceq nfunsnafv nvelim syl con4i ) CADEFZAC
    GZBHZPIQJKRIACLQBMNO $.

  $( A function's value at a proper class is the universe, compare with
     ~ fvprc .  (Contributed by Alexander van der Vekens, 25-May-2017.) $)
  afvprc $p |- ( -. A e. _V -> ( F ''' A ) = _V ) $=
    ( cvv wcel wn cdm cafv wceq prcnel ndmafv syl ) ACDEABFZDEABGCHALIABJK $.

  $( If a function's value at an argument is a set, the argument is also a set.
     (Contributed by Alexander van der Vekens, 25-May-2017.) $)
  afvvv $p |- ( ( F ''' A ) e. B -> A e. _V ) $=
    ( cvv wcel cafv wn wceq afvprc nvelim syl con4i ) ADEZACFZBEZMGNDHOGACINBJK
    L $.

  $( If the value of the alternative function at an argument is the universe,
     the function's value at this argument is the empty set.  (Contributed by
     Alexander van der Vekens, 25-May-2017.) $)
  afvpcfv0 $p |- ( ( F ''' A ) = _V -> ( F ` A ) = (/) ) $=
    ( cafv cvv wceq wdfat cfv cif c0 dfafv2 eqeq1i wa wn wo eqcom eqif fveqvfvv
    bitri eqcoms sylbi adantl wne cdm wcel cres wfun fvfundmfvn0 df-dfat sylibr
    csn necon1bi adantr jaoi ) ABCZDEABFZABGZDHZDEZUPIEZUNUQDABJKURUODUPEZLZUOM
    ZDDEZLZNZUSURDUQEVEUQDOUODUPDPRVAUSVDUTUSUOUSUPDAIBQSUAVBUSVCUOUPIUPIUBABUC
    UDBAUJUEUFLUOABUGABUHUIUKULUMTT $.

  $( The value of the alternative function at a set as argument equals the
     function's value at this argument.  (Contributed by Alexander van der
     Vekens, 25-May-2017.) $)
  afvnufveq $p |- ( ( F ''' A ) =/= _V -> ( F ''' A ) = ( F ` A ) ) $=
    ( cafv cfv wceq cvv wdfat afvfundmfveq afvnfundmuv nsyl5 necon1ai ) ABCZABD
    EZLFABGMLFEABHABIJK $.

  $( The value of the alternative function at a set as argument equals the
     function's value at this argument.  (Contributed by Alexander van der
     Vekens, 25-May-2017.) $)
  afvvfveq $p |- ( ( F ''' A ) e. B -> ( F ''' A ) = ( F ` A ) ) $=
    ( cafv wcel cvv wne cfv wceq nvelim necon2ai afvnufveq syl ) ACDZBEZNFGNACH
    IONFNBJKACLM $.

  $( If the value of the alternative function at an argument is the empty set,
     the function's value at this argument is the empty set.  (Contributed by
     Alexander van der Vekens, 25-May-2017.) $)
  afv0fv0 $p |- ( ( F ''' A ) = (/) -> ( F ` A ) = (/) ) $=
    ( cafv cvv wcel c0 wceq cfv wi 0ex eleq1a ax-mp afvvfveq eqeq1 biimpd mpcom
    syl ) ABCZDEZRFGZABHZFGZFDETSIJFDRKLSRUAGZTUBIADBMUCTUBRUAFNOQP $.

  $( If the function's value at an argument is not the empty set, it equals the
     value of the alternative function at this argument.  (Contributed by
     Alexander van der Vekens, 25-May-2017.) $)
  afvfvn0fveq $p |- ( ( F ` A ) =/= (/) -> ( F ''' A ) = ( F ` A ) ) $=
    ( cfv wne wdfat cafv wceq cdm wcel csn cres wfun fvfundmfvn0 df-dfat sylibr
    c0 wa afvfundmfveq syl ) ABCZPDZABEZABFTGUAABHIBAJKLQUBABMABNOABRS $.

  $( The function's value at an argument is an element of a set if and only if
     the value of the alternative function at this argument is an element of
     that set, if the set does not contain the empty set.  (Contributed by
     Alexander van der Vekens, 25-May-2017.) $)
  afv0nbfvbi $p |- ( (/) e/ B -> ( ( F ''' A ) e. B <-> ( F ` A ) e. B ) ) $=
    ( c0 wnel cafv wcel cfv wceq afvvfveq eleq1 biimpd mpcom wi wa wne cdm cres
    csn wfun elnelne2 ancoms fvfundmfvn0 wdfat df-dfat afvfundmfveq sylbir 4syl
    wb eqcoms ex pm2.43d impbid2 ) DBEZACFZBGZACHZBGZUOUQIZUPURABCJUSUPURUOUQBK
    LMUNURUPUNURURUPNZUNUROUQDPZACQGCASRTOZUSUTURUNVAUQDBUAUBACUCVBACUDUSACUEAC
    UFUGUSURUPURUPUIUQUOUQUOBKUJLUHUKULUM $.

  $( The function's value at an argument is the empty set if and only if the
     value of the alternative function at this argument is either the empty set
     or the universe.  (Contributed by Alexander van der Vekens,
     25-May-2017.) $)
  afvfv0bi $p |- ( ( F ` A ) = (/)
                     <-> ( ( F ''' A ) = (/) \/ ( F ''' A ) = _V ) ) $=
    ( cfv c0 wceq cvv wo wn wa ioran wi wne df-ne afvnufveq sylbir eqeq1 notbid
    cafv biimpd syl impcom sylbi con4i afv0fv0 afvpcfv0 jaoi impbii ) ABCZDEZAB
    RZDEZUJFEZGZUMUIUMHUKHZULHZIUIHZUKULJUOUNUPUOUJUHEZUNUPKUOUJFLUQUJFMABNOUQU
    NUPUQUKUIUJUHDPQSTUAUBUCUKUIULABUDABUEUFUG $.

  ${
    $d A x $.  $d F x $.
    $( The value of a function at a unique point, analogous to ~ fveu .
       (Contributed by Alexander van der Vekens, 29-Nov-2017.) $)
    afveu $p |- ( E! x A F x -> ( F ''' A ) = U. { x | A F x } ) $=
      ( cvv wcel cv wbr weu cafv cab cuni wceq df-br eubii eu2ndop1stv sylbi wa
      cop cdm wi wex euex eldmg syl5ibrcom impcom dfdfat2 cfv afvfundmfveq fveu
      wdfat sylan9eq ex sylbir expcom pm2.43a adantl mpd mpancom ) BDEZBAFZCGZA
      HZBCIZVAAJKZLZVBBUTRCEZAHUSVAVFABUTCMNABCOPUSVBQBCSEZVEVBUSVGVBVGUSVAAUAV
      AAUBABCDUCUDUEVBVGVETUSVGVBVEVGVBVBVETZVGVBQBCUJZVHABCUFVIVBVEVIVBVCBCUGV
      DBCUHABCUIUKULUMUNUOUPUQUR $.
  $}

  $( Equivalence of function value and binary relation, analogous to
     ~ fnbrfvb .  (Contributed by Alexander van der Vekens, 25-May-2017.) $)
  fnbrafvb $p |- ( ( F Fn A /\ B e. A ) ->
                   ( ( F ''' B ) = C <-> B F C ) ) $=
    ( wfn wcel wa cafv wceq cfv wbr cdm csn cres wfun wi fndm wb eleq2 syl imp
    eqcoms biimpd snssi adantl fnssresb adantr fnfun wdfat df-dfat afvfundmfveq
    wss mpbird sylbir syl2anc eqeq1d fnbrfvb bitrd ) DAEZBAFZGZBDHZCIBDJZCIBCDK
    VAVBVCCVABDLZFZDBMZNZOZVBVCIZUSUTVEUSVDAIZUTVEPADQVJUTVEUTVERAVDAVDBSUBUCTU
    AVAVGVFEZVHVAVKVFAULZUTVLUSBAUDUEUSVKVLRUTAVFDUFUGUMVFVGUHTVEVHGBDUIVIBDUJB
    DUKUNUOUPABCDUQUR $.

  $( Equivalence of function value and ordered pair membership, analogous to
     ~ fnopfvb .  (Contributed by Alexander van der Vekens, 25-May-2017.) $)
  fnopafvb $p |- ( ( F Fn A /\ B e. A ) ->
                   ( ( F ''' B ) = C <-> <. B , C >. e. F ) ) $=
    ( wfn wcel wa cafv wceq wbr cop fnbrafvb df-br bitrdi ) DAEBAFGBDHCIBCDJBCK
    DFABCDLBCDMN $.

  $( Equivalence of function value and binary relation, analogous to
     ~ funbrfvb .  (Contributed by Alexander van der Vekens, 25-May-2017.) $)
  funbrafvb $p |- ( ( Fun F /\ A e. dom F ) ->
                   ( ( F ''' A ) = B <-> A F B ) ) $=
    ( wfun cdm wfn wcel cafv wceq wbr wb funfn fnbrafvb sylanb ) CDCCEZFAOGACHB
    IABCJKCLOABCMN $.

  $( Equivalence of function value and ordered pair membership, analogous to
     ~ funopfvb .  (Contributed by Alexander van der Vekens, 25-May-2017.) $)
  funopafvb $p |- ( ( Fun F /\ A e. dom F ) ->
                   ( ( F ''' A ) = B <-> <. A , B >. e. F ) ) $=
    ( wfun cdm wfn wcel cafv wceq cop wb funfn fnopafvb sylanb ) CDCCEZFAOGACHB
    IABJCGKCLOABCMN $.

  $( The second argument of a binary relation on a function is the function's
     value, analogous to ~ funbrfv .  (Contributed by Alexander van der Vekens,
     25-May-2017.) $)
  funbrafv $p |- ( Fun F -> ( A F B -> ( F ''' A ) = B ) ) $=
    ( wfun wbr cafv wceq wi wrel funrel wa cdm releldm funbrafvb biimprd expcom
    wcel syl ex pm2.43i com14 com13 ) CDZABCEZACFBGZHZUCCIZUCUFHZCJUDUCUGUEUDUC
    UGUEHHUGUDUCUDUEUGUDUHUGUDKACLQZUHABCMUCUIUFUCUIKUEUDABCNOPRSUATUBRT $.

  ${
    $d x y A $.  $d x y B $.  $d x y F $.
    $( Function value in terms of a binary relation, analogous to ~ funbrfv2b .
       (Contributed by Alexander van der Vekens, 25-May-2017.) $)
    funbrafv2b $p |- ( Fun F ->
                       ( A F B <-> ( A e. dom F /\ ( F ''' A ) = B ) ) ) $=
      ( wfun wbr wcel wa cafv wceq wrel wi funrel releldm ex pm4.71rd funbrafvb
      cdm syl pm5.32da bitr4d ) CDZABCEZACQFZUBGUCACHBIZGUAUBUCUACJZUBUCKCLUEUB
      UCABCMNROUAUCUDUBABCPST $.

    $( Representation of a function in terms of its values, analogous to
       ~ dffn5 (only one direction of implication!).  (Contributed by Alexander
       van der Vekens, 25-May-2017.) $)
    dfafn5a $p |- ( F Fn A -> F = ( x e. A |-> ( F ''' x ) ) ) $=
      ( vy wfn cv wcel cafv wceq wa copab cmpt wrel fnrel dfrel4v sylib fnbr ex
      wbr pm4.71rd eqcom fnbrafvb bitrid pm5.32da bitr4d opabbidv eqtrd eqtr4di
      df-mpt ) CBEZCAFZBGZDFZUKCHZIZJZADKZABUNLUJCUKUMCSZADKZUQUJCMCUSIBCNADCOP
      UJURUPADUJURULURJUPUJURULUJURULBUKUMCQRTUJULUOURUOUNUMIUJULJURUMUNUABUKUM
      CUBUCUDUEUFUGADBUNUIUH $.

    $( Representation of a function in terms of its values, analogous to
       ~ dffn5 (only if it is assumed that the function value for each x is a
       set).  (Contributed by Alexander van der Vekens, 25-May-2017.) $)
    dfafn5b $p |- ( A. x e. A ( F ''' x ) e. V
                    -> ( F Fn A <-> F = ( x e. A |-> ( F ''' x ) ) ) ) $=
      ( cv cafv wcel wral cmpt wceq dfafn5a eqid fnmpt fneq1 syl5ibrcom impbid2
      wfn ) AECFZDGABHZCBQZCABRIZJZABCKSTUBUABQABRUADUALMBCUANOP $.

    $( The range of a function expressed as a collection of the function's
       values, analogous to ~ fnrnfv .  (Contributed by Alexander van der
       Vekens, 25-May-2017.) $)
    fnrnafv $p |- ( F Fn A -> ran F = { y | E. x e. A y = ( F ''' x ) } ) $=
      ( wfn crn cv cafv cmpt wceq wrex cab dfafn5a rneqd eqid rnmpt eqtrdi ) DC
      EZDFACAGDHZIZFBGSJACKBLRDTACDMNABCSTTOPQ $.

    $( A member of a function's range is a value of the function, analogous to
       ~ fvelrnb with the additional requirement that the member must be a set.
       (Contributed by Alexander van der Vekens, 25-May-2017.) $)
    afvelrnb $p |- ( ( F Fn A /\ B e. V )
                     -> ( B e. ran F <-> E. x e. A ( F ''' x ) = B ) ) $=
      ( vy wfn wcel wa crn cv cafv wceq wrex cab fnrnafv adantr eleq2d wb eqeq1
      eqcom bitrdi rexbidv elabg adantl bitrd ) DBGZCEHZIZCDJZHCFKZAKDLZMZABNZF
      OZHZULCMZABNZUIUJUOCUGUJUOMUHAFBDPQRUHUPURSUGUNURFCEUKCMZUMUQABUSUMCULMUQ
      UKCULTCULUAUBUCUDUEUF $.

    $( A member of a function's range is a value of the function, only one
       direction of implication of ~ fvelrnb .  (Contributed by Alexander van
       der Vekens, 1-Jun-2017.) $)
    afvelrnb0 $p |- ( F Fn A
                      -> ( B e. ran F -> E. x e. A ( F ''' x ) = B ) ) $=
      ( vy wfn crn wcel cv cafv wceq wrex cab fnrnafv eleq2d eqeq1 eqcom bitrdi
      rexbidv elabg ibi biimtrdi ) DBFZCDGZHCEIZAIDJZKZABLZEMZHZUFCKZABLZUCUDUI
      CAEBDNOUJULUHULECUIUECKZUGUKABUMUGCUFKUKUECUFPCUFQRSTUAUB $.

    $( Alternate definition of the image of a function, analogous to
       ~ dfimafn .  (Contributed by Alexander van der Vekens, 25-May-2017.) $)
    dfaimafn $p |- ( ( Fun F /\ A C_ dom F ) ->
                  ( F " A ) = { y | E. x e. A ( F ''' x ) = y } ) $=
      ( wfun cdm wss wa cima cv wbr wrex cab cafv wceq dfima2 wcel wb funbrafvb
      ssel ex syl9r imp31 rexbidva abbidv eqtr4id ) DEZCDFZGZHZDCIAJZBJZDKZACLZ
      BMUKDNULOZACLZBMABDCPUJUPUNBUJUOUMACUGUIUKCQZUOUMRZUIUQUKUHQZUGURCUHUKTUG
      USURUKULDSUAUBUCUDUEUF $.

    $( Alternate definition of the image of a function as an indexed union of
       singletons of function values, analogous to ~ dfimafn2 .  (Contributed
       by Alexander van der Vekens, 25-May-2017.) $)
    dfaimafn2 $p |- ( ( Fun F /\ A C_ dom F ) ->
                   ( F " A ) = U_ x e. A { ( F ''' x ) } ) $=
      ( vy wfun cdm wss wa cima cv cafv wceq cab ciun csn wrex dfaimafn eqtr4di
      iunab wcel df-sn eqcom abbii eqtri a1i iuneq2i ) CEBCFGHZCBIZABAJZCKZDJZL
      ZDMZNZABUJOZNUGUHULABPDMUNADBCQULADBSRABUOUMUOUMLUIBTUOUKUJLZDMUMDUJUAUPU
      LDUKUJUBUCUDUEUFR $.

    $( Function value in an image, analogous to ~ fvelima .  (Contributed by
       Alexander van der Vekens, 25-May-2017.) $)
    afvelima $p |- ( ( Fun F /\ A e. ( F " B ) ) ->
                  E. x e. B ( F ''' x ) = A ) $=
      ( wfun cima wcel cafv wceq wrex wbr elimag ibi funbrafv reximdv syl5 imp
      cv ) DEZBDCFZGZARZDHBIZACJZUAUBBDKZACJZSUDUAUFABDCTLMSUEUCACUBBDNOPQ $.
  $}

  $( A function's value belongs to its range, analogous to ~ fvelrn .
     (Contributed by Alexander van der Vekens, 25-May-2017.) $)
  afvelrn $p |- ( ( Fun F /\ A e. dom F ) -> ( F ''' A ) e. ran F ) $=
    ( wfun cdm wcel wa cfv cafv crn wdfat wceq csn funres anim1i ancomd df-dfat
    cres sylibr afvfundmfveq eqcomd syl fvelrn eqeltrrd ) BCZABDEZFZABGZABHZBIU
    FABJZUGUHKUFUEBALZQCZFUIUFUKUEUDUKUEUJBMNOABPRUIUHUGABSTUAABUBUC $.

  $( A function's value belongs to its range, analogous to ~ fnfvelrn .
     (Contributed by Alexander van der Vekens, 25-May-2017.) $)
  fnafvelrn $p |- ( ( F Fn A /\ B e. A ) -> ( F ''' B ) e. ran F ) $=
    ( cafv crn wcel afvelrn funfni ) BCDCEFABCBCGH $.

  $( A function's value belongs to its codomain, analogous to ~ ffvelcdm .
     (Contributed by Alexander van der Vekens, 25-May-2017.) $)
  fafvelcdm $p |- ( ( F : A --> B /\ C e. A ) -> ( F ''' C ) e. B ) $=
    ( wf wcel wa cafv crn wfn ffn fnafvelrn sylan wi frn sseld adantr mpd ) ABD
    EZCAFZGCDHZDIZFZUABFZSDAJTUCABDKACDLMSUCUDNTSUBBUAABDOPQR $.

  ${
    $d x y A $.  $d x y B $.  $d x y F $.
    $( A function maps to a class to which all values belong, analogous to
       ~ ffnfv .  (Contributed by Alexander van der Vekens, 25-May-2017.) $)
    ffnafv $p |- ( F : A --> B
                   <-> ( F Fn A /\ A. x e. A ( F ''' x ) e. B ) ) $=
      ( vy wf wfn cv cafv wcel wral wa ffn fafvelcdm ralrimiva jca crn wss wceq
      simpl wrex afvelrnb0 nfra1 nfv wi eleq1 biimpcd syl6 rexlimd sylan9 ssrdv
      rsp df-f sylanbrc impbii ) BCDFZDBGZAHZDIZCJZABKZLZUPUQVABCDMUPUTABBCURDN
      OPVBUQDQZCRUPUQVATVBEVCCUQEHZVCJUSVDSZABUAVAVDCJZABVDDUBVAVEVFABUTABUCVFA
      UDVAURBJUTVEVFUEUTABULVEUTVFUSVDCUFUGUHUIUJUKBCDUMUNUO $.
  $}

  $( The value of a restricted function, analogous to ~ fvres .  (Contributed
     by Alexander van der Vekens, 22-Jul-2017.) $)
  afvres $p |- ( A e. B -> ( ( F |` B ) ''' A ) = ( F ''' A ) ) $=
    ( cdm wcel cres wfun wa cafv wceq eqcomd funeqd biimpd anim12d impcom wdfat
    cfv df-dfat afvfundmfveq cvv csn cin biimpri dmres eleqtrrdi snssi resabs1d
    elin ex sylbir syl fvres adantl adantr 3eqtrd wn wi pm3.4 sylbi com12 con3d
    eleq2s afvnfundmuv sylnbir eqtrd pm2.61ian ) ACDZEZCAUAZFZGZHZABEZACBFZIZAC
    IZJVLVMHZVOAVNQZACQZVPVQAVNDZEZVNVIFZGZHZVOVRJZVMVLWDVMVHWAVKWCVMVHWAVMVHHZ
    ABVGUBZVTAWGEZWFABVGUHZUCCBUDZUEUIVMVKWCVMVJWBVMWBVJVMCVIBABUFUGZKLMNOWDAVN
    PZWEAVNRZAVNSUJUKVMVRVSJVLABCULUMVLVSVPJVMVLVPVSVLACPZVPVSJACRZACSUJKUNUOVL
    UPZVMHZVOTVPWQWDUPZVOTJZVMWPWRVMWDVLVMWAVHWCVKWAVMVHVMVHUQZAWGVTWHWFWTWIVMV
    HURUSWJVBUTVMWCVKVMWBVJWKLMNVAOWDWLWSWMAVNVCVDUKWPTVPJVMWPVPTVLWNVPTJWOACVC
    VDKUNVEVF $.

  ${
    $d x y A $.  $d x y F $.
    $( Function value.  Theorem 6.12(1) of [TakeutiZaring] p. 27, analogous to
       ~ tz6.12 .  (Contributed by Alexander van der Vekens, 29-Nov-2017.) $)
    tz6.12-afv $p |- ( ( <. A , y >. e. F /\ E! y <. A , y >. e. F )
                        -> ( F ''' A ) = y ) $=
      ( vx cvv wcel cv cop weu wa cafv wceq wi wbr simpl com12 adantl sylbir ex
      syl cfv cdm csn cres wfun vex df-br bilanri breldmg syl3anc wral velsn wb
      a1i breq1 bitr3id eqcoms eubidv biimpd sylbi ralrimiv wfn fnres fnfun jca
      impr wdfat df-dfat afvfundmfveq tz6.12 eqtrd eu2ndop1stv pm2.24d pm2.61i
      wn ) BEFZBAGZHCFZVRAIZJZBCKZVQLZMVPVTWBVPVTJZWABCUAZVQWCBCUBFZCBUCZUDZUEZ
      JZWAWDLZVPVRVSWIVPVRJZWEVSWIMWKVPVQEFZBVQCNZWEVPVROWLWKAUFUNWMVRVPBVQCUGZ
      UHBVQEECUIUJWEVSWIWEVSJZWEWHWEVSOWODGZVQCNZAIZDWFUKZWHWOWRDWFVSWPWFFZWRMW
      EWTVSWRWTWPBLZVSWRMDBULXAVSWRXAVRWQAVRWQUMBWPVRWMBWPLWQWNBWPVQCUOUPUQURUS
      UTPQVAWSWGWFVBWHDAWFCVCWFWGVDRTVESTVFWIBCVGWJBCVHBCVIRTVTWDVQLVPABCVJQVKS
      VTVPVOZWBVSXBWBMVRVSVPWBABCVLVMQPVN $.

    $( Function value (Theorem 6.12(1) of [TakeutiZaring] p. 27, analogous to
       ~ tz6.12-1 .  (Contributed by Alexander van der Vekens, 29-Nov-2017.) $)
    tz6.12-1-afv $p |- ( ( A F y /\ E! y A F y ) -> ( F ''' A ) = y ) $=
      ( cv wbr cop wcel weu cafv wceq df-br eubii tz6.12-afv syl2anb ) BADZCEZB
      OFCGZQAHBCIOJPAHBOCKZPQARLABCMN $.
  $}

  $( Domains of a function composition, analogous to ~ dmfco .  (Contributed by
     Alexander van der Vekens, 23-Jul-2017.) $)
  dmfcoafv $p |- ( ( Fun G /\ A e. dom G ) ->
                   ( A e. dom ( F o. G ) <-> ( G ''' A ) e. dom F ) ) $=
    ( wfun cdm wcel wa ccom cfv cafv dmfco cres wceq funres anim2i ancoms wdfat
    csn df-dfat afvfundmfveq sylbir syl eqcomd eleq1d bitrd ) CDZACEFZGZABCHEFA
    CIZBEZFACJZUJFABCKUHUIUKUJUHUKUIUHUGCARZLDZGZUKUIMZUGUFUNUFUMUGULCNOPUNACQU
    OACSACTUAUBUCUDUE $.

  $( Value of a function composition, analogous to ~ fvco2 .  (Contributed by
     Alexander van der Vekens, 23-Jul-2017.) $)
  afvco2 $p |- ( ( G Fn A /\ X e. A ) -> ( ( F o. G ) ''' X ) =
                 ( F ''' ( G ''' X ) ) ) $=
    ( wcel wa cafv cfv cdm cres wfun wceq adantl imp wdfat df-dfat afvfundmfveq
    wi wn cvv wfn ccom csn fvco2 simpll wb df-fn eleq2 eqcoms biimpd jca sylanb
    syl mpbird funcoressn sylbir syl2anc adantr 3eqtr4d wo funfni bicomd notbid
    dmfco ianor ndmafv syl6com funressnfv afvnfundmuv sylnbir nsyl4 com12 con1d
    ex jaoi sylbi eqcomd eqtrd pm2.61ian eqidd fnfun funresd afveq12d ) CAUAZDA
    EZFZDBCUBZGZDCHZBGZDCGZBGWIBIEZBWIUCJKZFZWFWHWJLWNWFFZDWGHZWIBHZWHWJWFWPWQL
    WNABCDUDMWODWGIEZWGDUCZJKZWHWPLZWOWRWLWLWMWFUEWOCKZDCIZEZFZWRWLUFZWFXEWNWDX
    BXCALZFZWEXECAUGZXHWEFXBXDXBXGWEUEXHWEXDXGWEXDRZXBXGWEXDWEXDUFAXCAXCDUHUIUJ
    MZNUKULMDBCVDZUMUNABCDUOWRWTFZDWGOZXADWGPZDWGQUPUQWNWJWQLZWFWNWIBOZXPWIBPZW
    IBQUPURUSWNSZWFFWHTWJXSWFWHTLZXSWLSZWMSZUTWFXTRZWLWMVEYAYCYBWFYAWRSZXTWFYAY
    DWFWLWRWFWRWLXFADCXLVAVBVCUJDWGVFVGWFYBXTWFXTWMXTSWFWMXMWFWMRXTXMWFWMABCDVH
    VNXMXNXTXODWGVIVJVKVLVMVLVOVPNXSTWJLWFXSWJTWNXQWJTLXRWIBVIVJVQURVRVSWFWIWKB
    BWFBVTWFWKWIWFXDCWSJKZWKWILZWDWEXDWDXHXJXIXKVPNWDYEWEWDWSCACWAWBURXDYEFDCOY
    FDCPDCQUPUQVQWCVR $.

  ${
    $d F w x y z $.  $d ph w x y z $.
    rlimdmafv.1 $e |- ( ph -> F : A --> CC ) $.
    rlimdmafv.2 $e |- ( ph -> sup ( A , RR* , < ) = +oo ) $.
    $( Two ways to express that a function has a limit, analogous to ~ rlimdm .
       (Contributed by Alexander van der Vekens, 27-Nov-2017.) $)
    rlimdmafv $p |- ( ph -> ( F e. dom ~~>r <-> F ~~>r ( ~~>r ''' F ) ) ) $=
      ( vx vy vz vw crli wcel wbr cv wex wa wceq cvv weq breq2 adantr cdm eldmg
      cafv ibi simpr cfv wdfat weu rlimrel brrelex1i adantl vex breldmg syl3anc
      a1i wi wal biimprd spimevw cc wf cxr clt csup cpnf simprl simprr alrimivv
      rlimuni ex eu4 sylanbrc dfdfat2 afvfundmfveq syl df-fv wb expr syl5ibrcom
      cio impbid iota5 elvd eqtrid eqtrd breqtrrd exlimdv syl5 releldmi impbid1
      ) ACJUAZKZCCJUCZJLZWLCFMZJLZFNZAWNWLWQFCJWKUBUDAWPWNFAWPWNAWPOZCWOWMJAWPU
      EZWRWMCJUFZWOWRCJUGZWMWTPWRWLCGMZJLZGUHZXAWRCQKZWOQKZWPWLWPXEACWOJUIUJUKX
      FWRFULUOWSCWOQQJUMUNWRXCGNZXCCHMZJLZOZGHRZUPZHUQGUQXDWPXGAWPXCGFGFRXCWPXB
      WOCJSURUSUKWRXLGHWRXJXKWRXJOBXBXHCWRBUTCVAZXJAXMWPDTTWRBVBVCVDVEPZXJAXNWP
      ETTWRXCXIVFWRXCXIVGVIVJVHXCXIGHXBXHCJSVKVLGCJVMVLCJVNVOWRWTCIMZJLZIVTZWOI
      CJVPWRXQWOPFWRXPIWOQWRXPIFRZVQXFWRXPXRAWPXPXRAWPXPOZOBXOWOCAXMXSDTAXNXSET
      AWPXPVGAWPXPVFVIVRWRXPXRWPWSXOWOCJSVSWATWBWCWDWEWFVJWGWHCWMJUIWIWJ $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Alternative definition of the value of an operation
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    aoveq123d.1 $e |- ( ph -> F = G ) $.
    aoveq123d.2 $e |- ( ph -> A = B ) $.
    aoveq123d.3 $e |- ( ph -> C = D ) $.
    $( Equality deduction for operation value, analogous to ~ oveq123d .
       (Contributed by Alexander van der Vekens, 26-May-2017.) $)
    aoveq123d $p |- ( ph -> (( A F C )) = (( B G D )) ) $=
      ( cop cafv caov opeq12d afveq12d df-aov 3eqtr4g ) ABDKZFLCEKZGLBDFMCEGMAR
      SFGHABCDEIJNOBDFPCEGPQ $.
  $}

  ${
    nfaov.2 $e |- F/_ x A $.
    nfaov.3 $e |- F/_ x F $.
    nfaov.4 $e |- F/_ x B $.
    $( Bound-variable hypothesis builder for operation value, analogous to
       ~ nfov .  To prove a deduction version of this analogous to ~ nfovd is
       not quickly possible because many deduction versions for bound-variable
       hypothesis builder for constructs the definition of alternative
       operation values is based on are not available (see ~ nfafv ).
       (Contributed by Alexander van der Vekens, 26-May-2017.) $)
    nfaov $p |- F/_ x (( A F B )) $=
      ( caov cop cafv df-aov nfop nfafv nfcxfr ) ABCDHBCIZDJBCDKAODFABCEGLMN $.
  $}

  ${
    $d x y $.  $d y A $.  $d y B $.  $d y C $.  $d y F $.
    $( Move class substitution in and out of an operation.  (Contributed by
       Alexander van der Vekens, 26-May-2017.) $)
    csbaovg $p |- ( A e. D -> [_ A / x ]_ (( B F C )) =
           (( [_ A / x ]_ B [_ A / x ]_ F [_ A / x ]_ C )) ) $=
      ( vy caov csb wceq csbeq1 aoveq123d eqeq12d vex nfcsb1v nfaov weq csbeq1a
      cv csbief vtoclg ) AGSZCDFHZIZAUBCIZAUBDIZAUBFIZHZJABUCIZABCIZABDIZABFIZH
      ZJGBEUBBJZUDUIUHUMAUBBUCKUNUEUJUFUKUGULAUBBFKAUBBCKAUBBDKLMAUBUCUHGNAUEUF
      UGAUBCOAUBFOAUBDOPAGQCUEDUFFUGAUBFRAUBCRAUBDRLTUA $.
  $}

  $( If a class is a function restricted to an ordered pair of its domain, then
     the value of the operation on this pair is equal for both definitions.
     (Contributed by Alexander van der Vekens, 26-May-2017.) $)
  aovfundmoveq $p |- ( F defAt <. A , B >. -> (( A F B )) = ( A F B ) ) $=
    ( cop wdfat cafv cfv caov co afvfundmfveq df-aov df-ov 3eqtr4g ) ABDZCENCFN
    CGABCHABCINCJABCKABCLM $.

  $( If an ordered pair is not in the domain of a class or the class is not a
     function restricted to the ordered pair, then the operation value for this
     pair is the universal class.  (Contributed by Alexander van der Vekens,
     26-May-2017.) $)
  aovnfundmuv $p |- ( -. F defAt <. A , B >. -> (( A F B )) = _V ) $=
    ( cop wdfat wn caov cafv cvv df-aov afvnfundmuv eqtrid ) ABDZCEFABCGMCHIABC
    JMCKL $.

  $( The value of an operation outside its domain, analogous to ~ ndmafv .
     (Contributed by Alexander van der Vekens, 26-May-2017.) $)
  ndmaov $p |- ( -. <. A , B >. e. dom F -> (( A F B )) = _V ) $=
    ( cop cdm wcel wn caov cafv cvv df-aov ndmafv eqtrid ) ABDZCEFGABCHNCIJABCK
    NCLM $.

  $( The value of an operation outside its domain, analogous to ~ ndmovg .
     (Contributed by Alexander van der Vekens, 26-May-2017.) $)
  ndmaovg $p |- ( ( dom F = ( R X. S ) /\ -. ( A e. R /\ B e. S ) )
              -> (( A F B )) = _V ) $=
    ( cdm cxp wceq wcel wa wn cop caov cvv opelxp eleq2 eqcoms bitr3id notbid
    wb biimpa ndmaov syl ) EFZCDGZHZACIBDIJZKZJABLZUDIZKZABEMNHUFUHUKUFUGUJUGUI
    UEIZUFUJABCDOULUJTUEUDUEUDUIPQRSUAABEUBUC $.

  $( If the operation value of a class for an ordered pair is a set, the
     ordered pair is contained in the domain of the class.  (Contributed by
     Alexander van der Vekens, 26-May-2017.) $)
  aovvdm $p |- ( (( A F B )) e. C -> <. A , B >. e. dom F ) $=
    ( caov wcel cop cafv cdm df-aov eleq1i afvvdm sylbi ) ABDEZCFABGZDHZCFODIFN
    PCABDJKOCDLM $.

  $( If the restriction of a class to a singleton is not a function, its
     operation value is the universal class.  (Contributed by Alexander van der
     Vekens, 26-May-2017.) $)
  nfunsnaov $p |- ( -. Fun ( F |` { <. A , B >. } ) -> (( A F B )) = _V ) $=
    ( cop csn cres wfun wn caov cafv cvv df-aov nfunsnafv eqtrid ) CABDZEFGHABC
    IOCJKABCLOCMN $.

  $( If the operation value of a class for an argument is a set, the class
     restricted to the singleton of the argument is a function.  (Contributed
     by Alexander van der Vekens, 26-May-2017.) $)
  aovvfunressn $p |- ( (( A F B )) e. C -> Fun ( F |` { <. A , B >. } ) ) $=
    ( caov wcel cop cafv csn cres wfun df-aov eleq1i afvvfunressn sylbi ) ABDEZ
    CFABGZDHZCFDQIJKPRCABDLMQCDNO $.

  ${
    aovprc.1 $e |- Rel dom F $.
    $( The value of an operation when the one of the arguments is a proper
       class, analogous to ~ ovprc .  (Contributed by Alexander van der Vekens,
       26-May-2017.) $)
    aovprc $p |- ( -. ( A e. _V /\ B e. _V ) -> (( A F B )) = _V ) $=
      ( cvv wcel wa wn caov cop cafv df-aov wceq df-br brrelex12i sylbir ndmafv
      cdm wbr nsyl5 eqtrid ) AEFBEFGZHABCIABJZCKZEABCLUCCRZFZUBUDEMUFABUESUBABU
      ENABUEDOPUCCQTUA $.

    $( Reverse closure for an operation value, analogous to ~ afvvv .  In
       contrast to ~ ovrcl , elementhood of the operation's value in a set is
       required, not containing an element.  (Contributed by Alexander van der
       Vekens, 26-May-2017.) $)
    aovrcl $p |- ( (( A F B )) e. C -> ( A e. _V /\ B e. _V ) ) $=
      ( caov wcel cop cafv cvv wa df-aov eleq1i cdm afvvdm wbr df-br brrelex12i
      sylbir syl sylbi ) ABDFZCGABHZDIZCGZAJGBJGKZUBUDCABDLMUEUCDNZGZUFUCCDOUHA
      BUGPUFABUGQABUGERSTUA $.
  $}

  $( If the alternative value of the operation on an ordered pair is the
     universal class, the operation's value at this ordered pair is the empty
     set.  (Contributed by Alexander van der Vekens, 26-May-2017.) $)
  aovpcov0 $p |- ( (( A F B )) = _V -> ( A F B ) = (/) ) $=
    ( cop cafv cvv wceq cfv c0 caov co afvpcfv0 df-aov eqeq1i df-ov 3imtr4i ) A
    BDZCEZFGQCHZIGABCJZFGABCKZIGQCLTRFABCMNUASIABCONP $.

  $( The alternative value of the operation on an ordered pair equals the
     operation's value at this ordered pair.  (Contributed by Alexander van der
     Vekens, 26-May-2017.) $)
  aovnuoveq $p |- ( (( A F B )) =/= _V -> (( A F B )) = ( A F B ) ) $=
    ( caov cvv wne cop cafv co wceq df-aov neeq1i afvnufveq df-ov 3eqtr4g sylbi
    cfv ) ABCDZEFABGZCHZEFZRABCIZJRTEABCKZLUATSCQRUBSCMUCABCNOP $.

  $( The alternative value of the operation on an ordered pair equals the
     operation's value on this ordered pair.  (Contributed by Alexander van der
     Vekens, 26-May-2017.) $)
  aovvoveq $p |- ( (( A F B )) e. C -> (( A F B )) = ( A F B ) ) $=
    ( caov wcel cop cafv co wceq df-aov eleq1i cfv afvvfveq df-ov 3eqtr4g sylbi
    ) ABDEZCFABGZDHZCFZRABDIZJRTCABDKZLUATSDMRUBSCDNUCABDOPQ $.

  $( If the alternative value of the operation on an ordered pair is the empty
     set, the operation's value at this ordered pair is the empty set.
     (Contributed by Alexander van der Vekens, 26-May-2017.) $)
  aov0ov0 $p |- ( (( A F B )) = (/) -> ( A F B ) = (/) ) $=
    ( cop cafv c0 wceq cfv caov co afv0fv0 df-aov eqeq1i df-ov 3imtr4i ) ABDZCE
    ZFGPCHZFGABCIZFGABCJZFGPCKSQFABCLMTRFABCNMO $.

  $( If the operation's value at an argument is not the empty set, it equals
     the value of the alternative operation at this argument.  (Contributed by
     Alexander van der Vekens, 26-May-2017.) $)
  aovovn0oveq $p |- ( ( A F B ) =/= (/) -> (( A F B )) = ( A F B ) ) $=
    ( co c0 wne cop cfv caov wceq df-ov neeq1i afvfvn0fveq df-aov 3eqtr4g sylbi
    cafv ) ABCDZEFABGZCHZEFZABCIZRJRTEABCKZLUASCQTUBRSCMABCNUCOP $.

  $( The operation's value on an ordered pair is an element of a set if and
     only if the alternative value of the operation on this ordered pair is an
     element of that set, if the set does not contain the empty set.
     (Contributed by Alexander van der Vekens, 26-May-2017.) $)
  aov0nbovbi $p |- ( (/) e/ C -> ( (( A F B )) e. C <-> ( A F B ) e. C ) ) $=
    ( c0 wnel cop cafv wcel cfv caov co afv0nbfvbi df-aov eleq1i df-ov 3bitr4g
    ) ECFABGZDHZCIRDJZCIABDKZCIABDLZCIRCDMUASCABDNOUBTCABDPOQ $.

  $( The operation's value on an ordered pair is the empty set if and only if
     the alternative value of the operation on this ordered pair is either the
     empty set or the universal class.  (Contributed by Alexander van der
     Vekens, 26-May-2017.) $)
  aovov0bi $p |- ( ( A F B ) = (/)
                     <-> ( (( A F B )) = (/) \/ (( A F B )) = _V ) ) $=
    ( co c0 wceq cop cfv cafv cvv wo caov eqeq1i afvfv0bi df-aov bicomi orbi12i
    df-ov 3bitri ) ABCDZEFABGZCHZEFUACIZEFZUCJFZKABCLZEFZUFJFZKTUBEABCRMUACNUDU
    GUEUHUGUDUFUCEABCOZMPUHUEUFUCJUIMPQS $.

  $( --------------------------- $)

  ${
    $d x A $.  $d x y B $.  $d x y C $.  $d y D $.  $d x y F $.  $d x y S $.
    $( A frequently used special case of ~ rspc2ev for operation values,
       analogous to ~ rspceov .  (Contributed by Alexander van der Vekens,
       26-May-2017.) $)
    rspceaov $p |- ( ( C e. A /\ D e. B /\ S = (( C F D )) ) ->
                 E. x e. A E. y e. B S = (( x F y )) ) $=
      ( cv caov wceq eqidd id aoveq123d eqeq2d rspc2ev ) GAIZBIZHJZKGEFHJZKGERH
      JZKABEFCDQEKZSUAGUBQERRHHUBHLUBMUBRLNORFKZUATGUCEERFHHUCHLUCELUCMNOP $.
  $}

  $( Equivalence of operation value and ordered triple membership, analogous to
     ~ fnopfvb .  (Contributed by Alexander van der Vekens, 26-May-2017.) $)
  fnotaovb $p |- ( ( F Fn ( A X. B ) /\ C e. A /\ D e. B ) ->
                   ( (( C F D )) = R <-> <. C , D , R >. e. F ) ) $=
    ( cxp wfn wcel w3a cop cafv wceq caov cotp wb wa opelxpi fnopafvb sylan2
    3impb df-aov eqeq1i df-ot eleq1i 3bitr4g ) FABGZHZCAIZDBIZJCDKZFLZEMZUKEKZF
    IZCDFNZEMCDEOZFIUHUIUJUMUOPZUIUJQUHUKUGIURCDABRUGUKEFSTUAUPULECDFUBUCUQUNFC
    DEUDUEUF $.

  ${
    $d x y w A $.  $d x y w B $.  $d x y w C $.  $d x y w F $.
    $( An operation maps to a class to which all values belong, analogous to
       ~ ffnov .  (Contributed by Alexander van der Vekens, 26-May-2017.) $)
    ffnaov $p |- ( F : ( A X. B ) --> C <-> ( F Fn ( A X. B ) /\
         A. x e. A A. y e. B (( x F y )) e. C ) ) $=
      ( vw cxp wf wfn cv cafv wcel wral wa caov ffnafv cop wceq afveq2 eqtr4di
      df-aov eleq1d ralxp anbi2i bitri ) CDHZEFIFUGJZGKZFLZEMZGUGNZOUHAKZBKZFPZ
      EMZBDNACNZOGUGEFQULUQUHUKUPGABCDUIUMUNRZSZUJUOEUSUJURFLUOUIURFTUMUNFUBUAU
      CUDUEUF $.
  $}

  ${
    $d x y A $.  $d y B $.  $d x y C $.  $d x y F $.  $d x y R $.  $d x y S $.
    faovcl.1 $e |- F : ( R X. S ) --> C $.
    $( Closure law for an operation, analogous to ~ fovcl .  (Contributed by
       Alexander van der Vekens, 26-May-2017.) $)
    faovcl $p |- ( ( A e. R /\ B e. S ) -> (( A F B )) e. C ) $=
      ( vx vy wcel wa cv caov wral cxp wceq eqidd id aoveq123d eleq1d wf ffnaov
      wfn simprbi ax-mp rspc2v mpi ) ADJBEJKHLZILZFMZCJZIENHDNZABFMZCJZDEOZCFUA
      ZULGUPFUOUCULHIDECFUBUDUEUKUNAUIFMZCJHIABDEUHAPZUJUQCURUHAUIUIFFURFQURRUR
      UIQSTUIBPZUQUMCUSAAUIBFFUSFQUSAQUSRSTUFUG $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x y C $.  $d x y V $.
    aovmpt4g.3 $e |- F = ( x e. A , y e. B |-> C ) $.
    $( Value of a function given by the maps-to notation, analogous to
       ~ ovmpt4g .  (Contributed by Alexander van der Vekens, 26-May-2017.) $)
    aovmpt4g $p |- ( ( x e. A /\ y e. B /\ C e. V ) -> (( x F y )) = C ) $=
      ( cv wcel w3a caov co cop cdm csn cres wfun wceq wa cxp wi dmmpog opelxpi
      eleq2 imbitrrid syl impcom 3impa mpofun funres ax-mp df-dfat aovfundmoveq
      wdfat sylbir sylancl ovmpt4g eqtrd ) AIZCJZBIZDJZEGJZKZUTVBFLZUTVBFMZEVEU
      TVBNZFOZJZFVHPZQRZVFVGSZVAVCVDVJVDVAVCTZVJVDVICDUAZSZVNVJUBABCDEFGHUCVNVJ
      VPVHVOJUTVBCDUDVIVOVHUEUFUGUHUIFRVLABCDEFHUJVKFUKULVJVLTVHFUOVMVHFUMUTVBF
      UNUPUQABCDEFGHURUS $.
  $}

  ${
    $d x y S $.  $d x y F $.
    aoprssdm.1 $e |- ( ( x e. S /\ y e. S ) -> (( x F y )) e. S ) $.
    $( Domain of closure of an operation.  In contrast to ~ oprssdm , no
       additional property for S ( ` -. (/) e. S ` ) is required!  (Contributed
       by Alexander van der Vekens, 26-May-2017.) $)
    aoprssdm $p |- ( S X. S ) C_ dom F $=
      ( cxp cdm relxp cv wcel wa opelxp cafv caov df-aov eqeltrrid afvvdm sylbi
      cop syl relssi ) ABCCFZDGZCCHAIZBIZSZUBJUDCJUECJKZUFUCJZUDUECCLUGUFDMZCJU
      HUGUIUDUEDNCUDUEDOEPUFCDQTRUA $.
  $}

  ${
    ndmaov.1 $e |- dom F = ( S X. S ) $.
    ${
      ndmaovcl.2 $e |- ( ( A e. S /\ B e. S ) -> (( A F B )) e. S ) $.
      ndmaovcl.3 $e |- (( A F B )) e. _V $.
      $( The "closure" of an operation outside its domain, when the operation's
         value is a set in contrast to ~ ndmovcl where it is required that the
         domain contains the empty set ( ` (/) e. S ` ).  (Contributed by
         Alexander van der Vekens, 26-May-2017.) $)
      ndmaovcl $p |- (( A F B )) e. S $=
        ( wcel wa caov cop cxp opelxp cdm eqcomi eleq2i cvv wn wceq ndmaov vprc
        eleq1 biimpd pm2.21i syl6com mpsyl sylnbi sylnbir pm2.61i ) ACHBCHIZABD
        JZCHZFUJABKZCCLZHZULABCCMUOUMDNZHZULUNUPUMUPUNEOPUKQHZUQRUKQSZULGABDTUS
        URQQHZULUSURUTUKQQUBUCUTULUAUDUEUFUGUHUI $.
    $}

    $( Reverse closure law, in contrast to ~ ndmovrcl where it is required that
       the operation's domain doesn't contain the empty set
       ( ` -. (/) e. S ` ), no additional asumption is required.  (Contributed
       by Alexander van der Vekens, 26-May-2017.) $)
    ndmaovrcl $p |- ( (( A F B )) e. S -> ( A e. S /\ B e. S ) ) $=
      ( caov wcel cop cdm wa aovvdm cxp opelxp biimpi eleq2s syl ) ABDFCGABHZDI
      ZGACGBCGJZABCDKSQCCLZRQTGSABCCMNEOP $.

    $( Any operation is commutative outside its domain, analogous to
       ~ ndmovcom .  (Contributed by Alexander van der Vekens, 26-May-2017.) $)
    ndmaovcom $p |- ( -. ( A e. S /\ B e. S ) -> (( A F B )) = (( B F A )) ) $=
      ( wcel wa wn caov cvv cop cdm wceq cxp opelxp eqcomi eleq2i bitr3i ndmaov
      sylnbi ancom 3bitr2i eqtr4d ) ACFZBCFZGZHABDIZJBADIZUFABKZDLZFZUGJMUFUICC
      NZFUKABCCOULUJUIUJULEPZQRABDSTUFBAKZUJFZUHJMUFUEUDGUNULFUOUDUEUABACCOULUJ
      UNUMQUBBADSTUC $.

    $( Any operation is associative outside its domain.  In contrast to
       ~ ndmovass where it is required that the operation's domain doesn't
       contain the empty set ( ` -. (/) e. S ` ), no additional assumption is
       required.  (Contributed by Alexander van der Vekens, 26-May-2017.) $)
    ndmaovass $p |- ( -. ( A e. S /\ B e. S /\ C e. S ) ->
                      (( (( A F B )) F C )) = (( A F (( B F C )) )) ) $=
      ( wcel caov cvv cop wceq wa eleq2i opelxp bitri aovvdm sylbi syl ndmaov
      wi w3a cdm cxp df-3an simplbi2 imp nsyl5 3anass biimpri a1d expcom impcom
      wn pm2.43i eqtr4d ) ADGZBDGZCDGZUAZUMABEHZCEHZIABCEHZEHZUTCJZEUBZGZUSVAIK
      VFUTDGZURLZUSVFVDDDUCZGVHVEVIVDFMUTCDDNOVGURUSVGABJZVEGZURUSTZABDEPVKUPUQ
      LZVLVKVJVIGVMVEVIVJFMABDDNOUSVMURUPUQURUDUEQRUFQUTCESUGAVBJZVEGZUSVCIKVOU
      SVOUPVBDGZLZVOUSTZVOVNVIGVQVEVIVNFMAVBDDNOVPUPVRVPBCJZVEGZUPVRTZBCDEPVTUQ
      URLZWAVTVSVIGWBVEVIVSFMBCDDNOUPWBVRUPWBLZUSVOUSWCUPUQURUHUIUJUKQRULQUNAVB
      ESUGUO $.

    ${
      ndmaov.6 $e |- dom G = ( S X. S ) $.
      $( Any operation is distributive outside its domain.  In contrast to
         ~ ndmovdistr where it is required that the operation's domain doesn't
         contain the empty set ( ` -. (/) e. S ` ), no additional assumption is
         required.  (Contributed by Alexander van der Vekens, 26-May-2017.) $)
      ndmaovdistr $p |- ( -. ( A e. S /\ B e. S /\ C e. S ) ->
          (( A G (( B F C )) )) = (( (( A G B )) F (( A G C )) )) ) $=
        ( wcel caov cvv cop cdm wa eleq2i opelxp bitri wi aovvdm sylbi w3a wceq
        wn cxp 3anass simplbi2com impcom ndmaov nsyl5 simpll simprr simplr 3jca
        syl ex syl11 imp eqtr4d ) ADIZBDIZCDIZUAZUCABCEJZFJZKABFJZACFJZEJZAVCLZ
        FMZIZVBVDKUBVJUSVCDIZNZVBVJVHDDUDZIVLVIVMVHHOAVCDDPQVKUSVBVKBCLZEMZIZUS
        VBRZBCDESVPUTVANZVQVPVNVMIVRVOVMVNGOBCDDPQVBUSVRUSUTVAUEUFTUNUGTAVCFUHU
        IVEVFLZVOIZVBVGKUBVTVEDIZVFDIZNZVBVTVSVMIWCVOVMVSGOVEVFDDPQWAWBVBWAABLZ
        VIIZWBVBRZABDFSWEUSUTNZWFWEWDVMIWGVIVMWDHOABDDPQACLZVIIZWGVBWBWIUSVANZW
        GVBRWIWHVMIWJVIVMWHHOACDDPQWJWGVBWJWGNUSUTVAUSVAWGUJWJUSUTUKUSVAWGULUMU
        OTACDFSUPTUNUQTVEVFEUHUIUR $.
    $}
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Alternative definitions of function values (2)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  In the following, a second approach is followed to define function values
  alternately to ~ df-afv .

  The current definition of the value ` ( F `` A ) ` of a function ` F ` at an
  argument ` A ` (see ~ df-fv ) assures that this value is always a set, see
  ~ fex .  This is because this definition can be applied to any classes ` F `
  and ` A ` , and evaluates to the empty set when it is not meaningful (as
  shown by ~ ndmfv and ~ fvprc ). "` ( F `` A ) ` is meaningful" means "the
  class ` F ` regarded as function is defined at the argument ` A `" in this
  context. This is also expressed by ` F defAt A `, see ~ df-dfat .  In the
  theory of partial functions, it is a common case that ` F ` is not defined at
  ` A `.

  Although it is very convenient for many theorems on functions and their
  proofs, there are some cases in which from ` ( F `` A ) = (/) ` alone it
  cannot be decided/derived whether ` ( F `` A ) ` is meaningful ( ` F ` is
  actually a function which is defined for ` A ` and really has the function
  value ` (/) ` at ` A ` ) or not.  Therefore, additional assumptions are
  required, such as ` (/) e/ ran F ` , ` (/) e. ran F ` , ` F defAt A ` , or
  ` Fun F /\ A e. dom F ` (see, for example, ~ ndmfvrcl ).

  To avoid such an ambiguity, an alternative definition ` ( F '''' A ) ` (see
  ~ df-afv2 ) would be possible which evaluates to a set not belonging to the
  range of ` F ` ( ` ( F '''' A ) = ~P U. ran F ` ) if it is not meaningful
  (see ~ ndfatafv2 ).  We say "` ( F '''' A ) ` is not defined (or undefined)"
  if ` ( F '''' A ) ` is not in the range of ` F ` (` ( F '''' A ) e/ ran F `).
  Because of ~ afv2ndefb , this is equivalent to ` ( ( F '''' A ) = `
  ` ~P U. ran F `.  If ` ( F '''' A ) ` is in the range of ` F `
  (` ( F '''' A ) e. ran F `), we say that "` ( F '''' A ) ` is defined".

  If ` ran F ` is a set, we can use the symbol ` Undef ` to express that
  ` ( F '''' A ) ` is not defined: ` ( F '''' A ) = ( Undef `` ran F ) ` (see
  ~ ndfatafv2undef ).  We could have used this symbol directly to define the
  alternate value of a function, which would have the advantage that
  ` ( F '''' A ) ` would always be a set.  But first this symbol is defined
  using the original function value, which would not make it possible to
  replace the original definition by the alternate definition, and second we
  would have to assume that ` ran F e. _V ` in most of the theorems.

  To summarize,  that means ` ( F '''' A ) e/ ran F -> ( F `` A ) = (/) ` (see
  ~ afv2ndeffv0 ), but ` ( F `` A ) = (/) -> ( F '''' A ) e/ ran F ` is not
  generally valid, see ~ afv2fv0 .

  The alternate definition, however, corresponds to the current definition
  (` ( F `` A ) = ( F '''' A ) ` ) if the function ` F ` is defined at ` A `
  (see ~ dfatafv2eqfv ).

  With this definition the following intuitive equivalence holds:
  ` ( F defAt A <-> ( F '''' A ) e. ran F ) `, see ~ dfatafv2rnb .

  An interesting question would be if ` ( F `` A ) ` could be replaced by
  ` ( F ''' A ) ` in most of the theorems based on function values.  If we look
  at the (currently 24) proofs using the definition ~ df-fv of ` ( F `` A ) `,
  we see that analogues for the following 7 theorems can be proven using the
  alternative definition: ~ fveq1 -> ~ afv2eq1 , ~ fveq2 -> ~ afv2eq2 ,
  ~ nffv -> ~ nfafv2 , ~ csbfv12 -> csbafv212g , ~ rlimdm -> ~ rlimdmafv2 ,
  ~ tz6.12-1 -> ~ tz6.12-1-afv2 , ~ fveu -> ~ afv2eu .

  Six theorems proved by directly using ~ df-fv are within a mathbox
  ( ~ fvsb , ~ uncov ) or not used ( ~ rlimdmafv , ~ avril1 ) or experimental
  ( ~ dfafv2 , ~ dfafv22 ).

  However, the remaining 11 theorems proved by directly using ~ df-fv are used
  more or less often:

  * ~ fvex : used in about 1600 proofs:  Only if the function is defined at the
    argument, or the range of the function/class is a set, analog theorems can
    be proven ( ~ dfatafv2ex resp. ~ afv2ex ).  All of these 1600 proofs have
    to be checked if one of these two theorems can be used instead of ~ fvex .

  * ~ fvres : used in about 400 proofs : Only if the function is defined at the
    argument, an analog theorem can be proven ( ~ afv2res ).  In the undefined
    case such a theorem cannot exist (without additional assumptions), because
    the range of ` ( F |`` B ) ` is mostly different from the range of ` F `,
    and therefore also the "undefined" values are different.  All of these 400
    proofs have to be checked if ~ afv2res can be used instead of ~ fvres .

  * ~ tz6.12-2 (-> ~ tz6.12-2-afv2 ): root theorem of many theorems which
    have not a strict analogue, and which are used many times:

  ** ~ fvprc (-> ~ afv2prc ), used in 193 proofs,

  ** ~ tz6.12i (-> ~ tz6.12i-afv2 ), used - indirectly via ~ fvbr0 and ~ fvrn0
     - in 19 proofs, and in ~ fvclss used in ~ fvclex used in ~ fvresex (which
     is not used!) and in ~ dcomex (used in 4 proofs),

  ** ~ ndmfv (-> ndmafv2nrn ), used in 124 proofs

  ** ~ nfunsn (-> nfunsnafv2 ), used by ~ fvfundmfvn0 (used in 3 proofs),
     and ~ dffv2 (not used)

  ** ~ funpartfv , ~ setrec2lem1 (mathboxes)

  * ~ fv2 : only used by ~ elfv , which is only used by ~ fv3 , which is not
    used.

  * ~ dffv3 (-> dfafv23 ): used by ~ dffv4 (the previous "df-fv"), which now is
    only used in mathboxes ( ~ csbfv12gALTVD ), by ~ shftval (itself used in 11
    proofs), by ~ dffv5 (mathbox) and by ~ fvco2 (-> ~ afv2co2 ).

  * ~ fvopab5 : used only by ~ ajval (not used) and by ~ adjval , which is used
    in ~ adjval2 (not used) and in ~ adjbdln (used in 7 proofs).

  * ~ zsum : used (via ~ isum , ~ sum0 , ~ sumss and ~ fsumsers )
             in 76 proofs.

  * ~ isumshft : used in ~ pserdv2 (used in ~ logtayl , ~ binomcxplemdvsum ) ,
      ~ eftlub (used in 4 proofs), ~ binomcxplemnotnn0 (used in ~ binomcxp
      only) and ~ logtayl (used in 4 proofs).

  * ~ ovtpos : used in 16 proofs.

  * ~ zprod : used in 3 proofs: ~ iprod , ~ zprodn0 and ~ prodss

  * ~ iprodclim3 : not used!

  As a result of this analysis we can say that the current definition of a
  function value is crucial for Metamath and cannot be exchanged easily with an
  alternative definition.  While ~ fv2 , ~ dffv3 , ~ fvopab5 , ~ zsum ,
  ~ isumshft , ~ ovtpos and ~ zprod are not critical or are, hopefully, also
  valid for the alternative definition, ~ fvex , ~ fvres and ~ tz6.12-2 (and
  the theorems based on them) are essential for the current definition of
  function values.

$)

  $c '''' $. $( Fourfold straight apostrophe (function value symbol) $)

  $( Extend the definition of a class to include the alternate function value.
     Read:  "the value of ` F ` at ` A ` " or " ` F ` of ` A ` ".  For using
     several apostrophes as a symbol see comment for ~ cafv . $)
  cafv2 $a class ( F '''' A ) $.

  ${
    $d x A $.  $d x F $.
    $( Alternate definition of the value of a function, ` ( F '''' A ) ` , also
       known as function application (and called "alternate function value" in
       the following).  In contrast to ` ( F `` A ) = (/) ` (see comment of
       ~ df-fv , and especially ~ ndmfv ), ` ( F '''' A ) ` is guaranteed not
       to be in the range of ` F ` if ` F ` is not defined at ` A ` (whereas
       ` (/) ` can be a member of ` ran F ` ).  (Contributed by AV,
       2-Sep-2022.) $)
    df-afv2 $a |- ( F '''' A )
                  = if ( F defAt A , ( iota x A F x ) , ~P U. ran F ) $.

    $( If a function is defined at a class ` A ` the alternate function value
       at ` A ` is the unique value assigned to ` A ` by the function
       (analogously to ` ( F `` A ) ` ).  (Contributed by AV, 2-Sep-2022.) $)
    dfatafv2iota $p |- ( F defAt A -> ( F '''' A ) = ( iota x A F x ) ) $=
      ( wdfat cafv2 cv wbr cio crn cuni cpw cif df-afv2 iftrue eqtrid ) BCDZBCE
      PBAFCGAHZCIJKZLQABCMPQRNO $.

    $( The alternate function value at a class ` A ` if the function is not
       defined at this set ` A ` .  (Contributed by AV, 2-Sep-2022.) $)
    ndfatafv2 $p |- ( -. F defAt A -> ( F '''' A ) = ~P U. ran F ) $=
      ( vx wdfat wn cafv2 cv wbr cio crn cuni cpw cif df-afv2 iffalse eqtrid )
      ABDZEABFQACGBHCIZBJKLZMSCABNQRSOP $.

    $( The alternate function value at a class ` A ` is undefined if the
       function, whose range is a set, is not defined at ` A ` .  (Contributed
       by AV, 2-Sep-2022.) $)
    ndfatafv2undef $p |- ( ( ran F e. V /\ -. F defAt A )
                           -> ( F '''' A ) = ( Undef ` ran F ) ) $=
      ( wdfat wn crn wcel cuni cpw cund cfv ndfatafv2 undefval eqcomd sylan9eqr
      cafv2 ) ABDEBFZCGZABPQHIZQJKZABLRTSQCMNO $.

    $( The alternate function value at a class ` A ` is always a set if the
       function/class ` F ` is defined at ` A ` .  (Contributed by AV,
       6-Sep-2022.) $)
    dfatafv2ex $p |- ( F defAt A -> ( F '''' A ) e. _V ) $=
      ( vx wdfat cafv2 cv wbr cio cvv dfatafv2iota iotaex eqeltrdi ) ABDABEACFB
      GZCHICABJMCKL $.

    $( The alternate function value is always a set if the range of the
       function is a set.  (Contributed by AV, 2-Sep-2022.) $)
    afv2ex $p |- ( ran F e. V -> ( F '''' A ) e. _V ) $=
      ( crn wcel cafv2 wdfat wbr cio cuni cpw cif cvv df-afv2 iotaex a1i uniexg
      vx cv pwexd ifcld eqeltrid ) BDZCEZABFABGZARSBHZRIZUCJZKZLMRABNUDUEUGUIMU
      GMEUDUFROPUDUHMUCCQTUAUB $.
  $}

  ${
    $d x A $.  $d x B $.  $d x F $.  $d x G $.  $d x ph $.
    afv2eq12d.1 $e |- ( ph -> F = G ) $.
    afv2eq12d.2 $e |- ( ph -> A = B ) $.
    $( Equality deduction for function value, analogous to ~ fveq12d .
       (Contributed by AV, 4-Sep-2022.) $)
    afv2eq12d $p |- ( ph -> ( F '''' A ) = ( G '''' B ) ) $=
      ( vx wdfat cv wbr cio crn cuni cpw cif cafv2 dfateq12d eqidd df-afv2
      breq123d iotabidv rneqd unieqd pweqd ifbieq12d 3eqtr4g ) ABDIZBHJZDKZHLZD
      MZNZOZPCEIZCUIEKZHLZEMZNZOZPBDQCEQAUHUOUKUNUQUTABCDEFGRAUJUPHABCUIUIDEGFA
      UISUAUBAUMUSAULURADEFUCUDUEUFHBDTHCETUG $.
  $}

  $( Equality theorem for function value, analogous to ~ fveq1 .  (Contributed
     by AV, 4-Sep-2022.) $)
  afv2eq1 $p |- ( F = G -> ( F '''' A ) = ( G '''' A ) ) $=
    ( wceq id eqidd afv2eq12d ) BCDZAABCHEHAFG $.

  $( Equality theorem for function value, analogous to ~ fveq2 .  (Contributed
     by AV, 4-Sep-2022.) $)
  afv2eq2 $p |- ( A = B -> ( F '''' A ) = ( F '''' B ) ) $=
    ( wceq eqidd id afv2eq12d ) ABDZABCCHCEHFG $.

  ${
    $d A y $.  $d F y $.  $d x y $.
    nfafv2.1 $e |- F/_ x F $.
    nfafv2.2 $e |- F/_ x A $.
    $( Bound-variable hypothesis builder for function value, analogous to
       ~ nffv .  To prove a deduction version of this analogous to ~ nffvd is
       not easily possible because a deduction version of ~ nfdfat cannot be
       shown easily.  (Contributed by AV, 4-Sep-2022.) $)
    nfafv2 $p |- F/_ x ( F '''' A ) $=
      ( vy cafv2 wdfat cv wbr cio crn cuni cpw df-afv2 nfdfat nfcv nfbr nfiotaw
      cif nfrn nfuni nfpw nfif nfcxfr ) ABCGBCHZBFIZCJZFKZCLZMZNZTFBCOUFAUIULAB
      CDEPUHAFABUGCEDAUGQRSAUKAUJACDUAUBUCUDUE $.
  $}

  ${
    $d A y $.  $d B y $.  $d F y $.  $d x y $.
    $( Move class substitution in and out of a function value, analogous to
       ~ csbfv12 , with a direct proof proposed by Mario Carneiro, analogous to
       ~ csbov123 .  (Contributed by AV, 4-Sep-2022.) $)
    csbafv212g $p |- ( A e. V -> [_ A / x ]_ ( F '''' B )
                                = ( [_ A / x ]_ F '''' [_ A / x ]_ B ) ) $=
      ( vy cv cafv2 csb csbeq1 afv2eq12d eqeq12d vex nfcsb1v nfafv2 weq csbeq1a
      wceq csbief vtoclg ) AFGZCDHZIZAUACIZAUADIZHZRABUBIZABCIZABDIZHZRFBEUABRZ
      UCUGUFUJAUABUBJUKUDUHUEUIAUABDJAUABCJKLAUAUBUFFMAUDUEAUADNAUACNOAFPCUDDUE
      AUADQAUACQKST $.
  $}

  $( The alternate function value is always a set if the function (resp. the
     domain of the function) is a set.  (Contributed by AV, 3-Sep-2022.) $)
  fexafv2ex $p |- ( F e. V -> ( F '''' A ) e. _V ) $=
    ( wcel crn cvv cafv2 rnexg afv2ex syl ) BCDBEFDABGFDBCHABFIJ $.

  $( The alternate function value at a class ` A ` at which the function is not
     defined is undefined, i.e., not in the range of the function.
     (Contributed by AV, 2-Sep-2022.) $)
  ndfatafv2nrn $p |- ( -. F defAt A -> ( F '''' A ) e/ ran F ) $=
    ( wdfat cafv2 crn cuni cpw wceq wnel ndfatafv2 pwuninel df-nel eleq1 notbid
    wn wcel bitrid mpbiri syl ) ABCOABDZBEZFGZHZTUAIZABJUCUDUBUAPZOZUAKUDTUAPZO
    UCUFTUALUCUGUETUBUAMNQRS $.

  $( The value of a class outside its domain is not in the range, compare with
     ~ ndmfv .  (Contributed by AV, 2-Sep-2022.) $)
  ndmafv2nrn $p |- ( -. A e. dom F -> ( F '''' A ) e/ ran F ) $=
    ( cdm wcel wn wdfat cafv2 crn wnel csn cres wfun wo orc wa df-dfat xchnxbir
    ianor sylibr ndfatafv2nrn syl ) ABCDZEZABFZEZABGBHIUCUCBAJKLZEZMZUEUCUGNUBU
    FOUHUDUBUFRABPQSABTUA $.

  ${
    $d x y A $.  $d x y z F $.
    $( The alternate function value at a class ` A ` is defined, i.e., in the
       range of the function if the function is defined at ` A ` .
       (Contributed by AV, 2-Sep-2022.) $)
    funressndmafv2rn $p |- ( F defAt A -> ( F '''' A ) e. ran F ) $=
      ( vy vx vz cv wbr cio wcel csn cres wfun wa wi wceq eleq1d cop wex breq2
      wb wdfat cafv2 crn dfatafv2iota df-dfat sneq reseq2d funeqd eleq1 anbi12d
      cdm breq1 iotabidv imbi12d eqid iotaex eqeq2 bibi12d imbi2d weu eldmg ibi
      adantl wmo funressnvmo adantr moeu sylib mpd cbviotavw eqeq1i bitr2di syl
      iota1 vtocl mpbii df-br vex opeq1 spcev elrn2 sylibr vtoclg anabsi6 sylbi
      eqeltrd ) ABUAZABUBACFZBGZCHZBUCZCABUDWGABUKZIZBAJZKZLZMWJWKIZABUEWMWPWQB
      DFZJZKZLZWRWLIZMZWRWHBGZCHZWKIZNWPWMMZWQNDAWLWRAOZXCXGXFWQXHXAWPXBWMXHWTW
      OXHWSWNBWRAUFUGUHWRAWLUIUJXHXEWJWKXHXDWICWRAWHBULUMPUNXCEFZXEQZBIZERZXFXC
      WRXEQZBIZXLXCWRXEBGZXNXCXEXEOZXOXEUOXCXEXIOZWRXIBGZTZNXCXPXOTZNEXEXDCUPZX
      IXEOZXSXTXCYBXQXPXRXOXIXEXEUQXIXEWRBSURUSXCXREUTZXSXCXRERZYCXBYDXAXBYDEWR
      BWLVAVBVCXCXREVDZYDYCNXAYEXBDEBVEVFXREVGVHVIYCXRXREHZXIOXQXREVNYFXEXIXRXD
      ECXIWHWRBSVJVKVLVMVOVPWRXEBVQVHXKXNEWRDVRXIWROXJXMBXIWRXEVSPVTVMEXEBYAWAW
      BWCWDWEWF $.
  $}

  $( Two ways to say that an alternate function value is not defined.
     (Contributed by AV, 5-Sep-2022.) $)
  afv2ndefb $p |- ( ( F '''' A ) = ~P U. ran F <-> ( F '''' A ) e/ ran F ) $=
    ( cafv2 crn cuni cpw wceq wnel wcel wn pwuninel df-nel notbid bitrid mpbiri
    eleq1 wdfat funressndmafv2rn con3i sylbi ndfatafv2 syl impbii ) ABCZBDZEFZG
    ZUDUEHZUGUHUFUEIZJZUEKUHUDUEIZJZUGUJUDUELZUGUKUIUDUFUEPMNOUHABQZJZUGUHULUOU
    MUNUKABRSTABUAUBUC $.

  $( If the restriction of a class to a singleton is not a function, its value
     at the singleton element is undefined, compare with ~ nfunsn .
     (Contributed by AV, 2-Sep-2022.) $)
  nfunsnafv2 $p |- ( -. Fun ( F |` { A } ) -> ( F '''' A ) e/ ran F ) $=
    ( csn cres wfun wn wdfat cafv2 crn wnel cdm wcel wo olc wa df-dfat xchnxbir
    ianor sylibr ndfatafv2nrn syl ) BACDEZFZABGZFZABHBIJUCABKLZFZUCMZUEUCUGNUFU
    BOUHUDUFUBRABPQSABTUA $.

  $( A function's value at a proper class is not defined, compare with
     ~ fvprc .  (Contributed by AV, 5-Sep-2022.) $)
  afv2prc $p |- ( -. A e. _V -> ( F '''' A ) e/ ran F ) $=
    ( cvv wcel wn cdm cafv2 crn wnel prcnel ndmafv2nrn syl ) ACDEABFZDEABGBHIAM
    JABKL $.

  $( The alternate function value at a class ` A ` is defined, i.e. in the
     range of the function, iff the function is defined at ` A ` .
     (Contributed by AV, 2-Sep-2022.) $)
  dfatafv2rnb $p |- ( F defAt A <-> ( F '''' A ) e. ran F ) $=
    ( wdfat cafv2 wcel funressndmafv2rn wn wnel ndfatafv2nrn df-nel sylib con4i
    crn impbii ) ABCZABDZBMZEZABFOROGPQHRGABIPQJKLN $.

  $( If a set is in the range of a function, the alternate function value at a
     class ` A ` equals this set or is not in the range of the function iff the
     alternate function value at the class ` A ` either equals this set or is
     not in the range of the function.  If ` B e/ ran F ` , both disjuncts of
     the exclusive or can be true: ` ( F '''' A ) = B `
     ` -> ( F '''' A ) e/ ran F ` .  (Contributed by AV, 11-Sep-2022.) $)
  afv2orxorb $p |- ( B e. ran F
                     -> ( ( ( F '''' A ) = B \/ ( F '''' A ) e/ ran F )
                      <-> ( ( F '''' A ) = B \/_ ( F '''' A ) e/ ran F ) ) ) $=
    ( crn wcel cafv2 wceq wnel wo wxo wn wi wa wb eleq1 eqcoms a1d jca ex com12
    biimpa nnel sylibr simpl anbi2d pm2.24nel impcom biimtrrdi pm2.24 jaoi xor3
    adantr df-xor dfbi2 3bitri imbitrrdi xoror impbid1 ) BCDZEZACFZBGZVAUSHZIZV
    BVCJZUTVDVBVCKZLZVFVBLZMZVEVDUTVIVBUTVILVCVBUTVIVBUTMZVGVHVJVFVBVJVAUSEZVFV
    BUTVKUTVKNBVABVAUSOPUAVAUSUBUCQVJVBVFVBUTUDQRSVCUTVIVCUTMZVGVHVBVLVFVBVLVCV
    KMVFVBVKUTVCVABUSOUEVKVCVFVFVAUSUFUGUHTVCVHUTVCVBUIULRSUJTVEVBVCNKVBVFNVIVB
    VCUMVBVCUKVBVFUNUOUPVBVCUQUR $.

  $( The alternate function value at a class ` A ` is defined, i.e., in the
     range of the function, iff ` A ` is in the domain of the function.
     (Contributed by AV, 3-Sep-2022.) $)
  dmafv2rnb $p |- ( Fun ( F |` { A } )
                    -> ( A e. dom F <-> ( F '''' A ) e. ran F ) ) $=
    ( csn cres wfun cdm wcel wa cafv2 crn iba df-dfat dfatafv2rnb bitr3i bitrdi
    wdfat ) BACDEZABFGZRQHZABIBJGZQRKSABPTABLABMNO $.

  $( The alternate function value at a class ` A ` is defined, i.e., in the
     range of the function iff ` A ` is in the domain of the function.
     (Contributed by AV, 3-Sep-2022.) $)
  fundmafv2rnb $p |- ( Fun F -> ( A e. dom F <-> ( F '''' A ) e. ran F ) ) $=
    ( wfun csn cres cdm wcel cafv2 crn wb funres dmafv2rnb syl ) BCBADZECABFGAB
    HBIGJNBKABLM $.

  $( An alternate function value belongs to the range of the function,
     analogous to ~ fvelrn .  (Contributed by AV, 3-Sep-2022.) $)
  afv2elrn $p |- ( ( Fun F /\ A e. dom F ) -> ( F '''' A ) e. ran F ) $=
    ( wfun cdm wcel wa wdfat cafv2 crn fundmdfat dfatafv2rnb sylib ) BCABDEFABG
    ABHBIEABJABKL $.

  $( If the alternate function value at an argument is the empty set, the
     function is defined at this argument.  (Contributed by AV, 3-Sep-2022.) $)
  afv20defat $p |- ( ( F '''' A ) = (/) -> F defAt A ) $=
    ( wdfat cafv2 c0 wceq wn crn cuni cpw ndfatafv2 pwne0 neii eqeq1 mtbiri syl
    con4i ) ABCZABDZEFZRGSBHIZJZFZTGABKUCTUBEFUBEUALMSUBENOPQ $.

  $( An alternate function value belongs to the range of the function,
     analogous to ~ fnfvelrn .  (Contributed by AV, 2-Sep-2022.) $)
  fnafv2elrn $p |- ( ( F Fn A /\ B e. A ) -> ( F '''' B ) e. ran F ) $=
    ( cafv2 crn wcel afv2elrn funfni ) BCDCEFABCBCGH $.

  $( An alternate function value belongs to the codomain of the function,
     analogous to ~ ffvelcdm .  (Contributed by AV, 2-Sep-2022.) $)
  fafv2elcdm $p |- ( ( F : A --> B /\ C e. A ) -> ( F '''' C ) e. B ) $=
    ( wf wcel wa cafv2 crn wfn ffn fnafv2elrn sylan wi frn sseld adantr mpd ) A
    BDEZCAFZGCDHZDIZFZUABFZSDAJTUCABDKACDLMSUCUDNTSUBBUAABDOPQR $.

  $( An alternate function value is defined, i.e., belongs to the range of the
     function, iff its argument is in the domain of the function.  (Contributed
     by AV, 3-Sep-2022.) $)
  fafv2elrnb $p |- ( F : A --> B -> ( C e. A <-> ( F '''' C ) e. ran F ) ) $=
    ( wf wcel cafv2 crn wfn ffn fnafv2elrn sylan ex cdm wceq wi wnel ndmafv2nrn
    fdm wn df-nel sylib con4i eleq2 imbitrid syl impbid ) ABDEZCAFZCDGZDHZFZUHU
    IULUHDAIUIULABDJACDKLMUHDNZAOZULUIPABDSULCUMFZUNUIUOULUOTUJUKQULTCDRUJUKUAU
    BUCUMACUDUEUFUG $.

  $( If the codomain of a function is a set, the alternate function value is
     always also a set.  (Contributed by AV, 4-Sep-2022.) $)
  fcdmvafv2v $p |- ( ( F : A --> B /\ B e. V ) -> ( F '''' C ) e. _V ) $=
    ( wf wcel wa crn cvv cafv2 wfn wss wi df-f ssexg ex simplbiim imp afv2ex
    syl ) ABDFZBEGZHDIZJGZCDKJGUBUCUEUBDALUDBMZUCUENABDOUFUCUEUDBEPQRSCDJTUA $.

  ${
    $d A x $.  $d F x $.
    $( Function value when ` F ` is (locally) not a function.  Theorem 6.12(2)
       of [TakeutiZaring] p. 27, analogous to ~ tz6.12-2 .  (Contributed by AV,
       5-Sep-2022.) $)
    tz6.12-2-afv2 $p |- ( -. E! x A F x -> ( F '''' A ) e/ ran F ) $=
      ( wdfat cv wbr weu cafv2 crn wnel wcel dfdfat2 simprbi ndfatafv2nrn nsyl5
      cdm ) BCDZBAECFAGZBCHCIJQBCPKRABCLMBCNO $.

    $( The value of a function at a unique point, analogous to ~ fveu .
       (Contributed by AV, 5-Sep-2022.) $)
    afv2eu $p |- ( E! x A F x -> ( F '''' A ) = U. { x | A F x } ) $=
      ( cvv wcel cv wbr weu cafv2 cab cuni wceq eubrv cdm euex eldmg syl5ibrcom
      wa wex wi impcom wdfat dfdfat2 cio dfatafv2iota sylan9eq ex sylbir expcom
      iotauni pm2.43a adantl mpd mpancom ) BDEZBAFCGZAHZBCIZUPAJKZLZBCAMUOUQRBC
      NEZUTUQUOVAUQVAUOUPASUPAOABCDPQUAUQVAUTTUOVAUQUTVAUQUQUTTZVAUQRBCUBZVBABC
      UCVCUQUTVCUQURUPAUDUSABCUEUPAUJUFUGUHUIUKULUMUN $.

    $d B x $.
    $( The value of a restricted function for an argument at which the function
       is defined.  Analog to ~ fvres .  (Contributed by AV, 5-Sep-2022.) $)
    afv2res $p |- ( ( F defAt A /\ A e. B )
                    -> ( ( F |` B ) '''' A ) = ( F '''' A ) ) $=
      ( vx wdfat wcel wa cres cafv2 cv wbr cio cdm csn wfun wceq df-dfat eqcomd
      wi dfatafv2iota cin elin biimpri dmres eleqtrrdi ex snssi resabs1d funeqd
      biimpd anim12d com12 sylbi imp sylbir syl vex brresi baib iotabidv adantl
      adantr 3eqtrd ) ACEZABFZGZACBHZIZADJZVGKZDLZAVICKZDLZACIZVFAVGMZFZVGANZHZ
      OZGZVHVKPZVDVEVTVDACMZFZCVQHZOZGZVEVTSACQVEWFVTVEWCVPWEVSVEWCVPVEWCGZABWB
      UAZVOAWHFWGABWBUBUCCBUDUEUFVEWEVSVEWDVRVEVRWDVECVQBABUGUHRUIUJUKULUMUNVTA
      VGEWAAVGQDAVGTUOUPVEVKVMPVDVEVJVLDVJVEVLBAVICDUQURUSUTVAVDVMVNPVEVDVNVMDA
      CTRVBVC $.
  $}

  ${
    $d x y A $.  $d x y F $.
    $( Function value (Theorem 6.12(1) of [TakeutiZaring] p. 27), analogous to
       ~ tz6.12 .  (Contributed by AV, 5-Sep-2022.) $)
    tz6.12-afv2 $p |- ( ( <. A , y >. e. F /\ E! y <. A , y >. e. F )
                        -> ( F '''' A ) = y ) $=
      ( vx cvv wcel cv cop weu wa cafv2 wceq wi wbr cio simpl adantl com12 syl
      ex wdfat cdm csn cres wfun vex a1i df-br biimpri breldmg syl3anc velsn wb
      wral breq1 bitr3id eqcoms eubidv biimpd sylbi ralrimiv fnres fnfun sylbir
      wfn df-dfat sylibr dfatafv2iota bicomi eubii biimpi anim12i iota1 biimpac
      jca impr eqtrd wn eu2ndop1stv pm2.24d pm2.61i ) BEFZBAGZHCFZWDAIZJZBCKZWC
      LZMWBWFWHWBWFJZWGBWCCNZAOZWCWIBCUAZWGWKLWIBCUBFZCBUCZUDZUEZJZWLWBWDWEWQWB
      WDJZWMWEWQMWRWBWCEFZWJWMWBWDPWSWRAUFUGWDWJWBWJWDBWCCUHZUIZQBWCEECUJUKWMWE
      WQWMWEJZWMWPWMWEPXBDGZWCCNZAIZDWNUNZWPXBXEDWNWEXCWNFZXEMWMXGWEXEXGXCBLZWE
      XEMDBULXHWEXEXHWDXDAWDXDUMBXCWDWJBXCLXDWTBXCWCCUOUPUQURUSUTRQVAXFWOWNVEWP
      DAWNCVBWNWOVCVDSVOTSVPBCVFVGABCVHSWIWJWJAIZJZWKWCLZWFXJWBWDWJWEXIXAWEXIWD
      WJAWJWDWTVIVJVKVLQXIWJXKWJAVMVNSVQTWFWBVRZWHWEXLWHMWDWEWBWHABCVSVTQRWA $.

    $( Function value (Theorem 6.12(1) of [TakeutiZaring] p. 27), analogous to
       ~ tz6.12-1 .  (Contributed by AV, 5-Sep-2022.) $)
    tz6.12-1-afv2 $p |- ( ( A F y /\ E! y A F y ) -> ( F '''' A ) = y ) $=
      ( cv wbr cop wcel weu cafv2 wceq df-br eubii tz6.12-afv2 syl2anb ) BADZCE
      ZBOFCGZQAHBCIOJPAHBOCKZPQARLABCMN $.
  $}

  ${
    $d y F $.  $d y A $.
    $( Corollary of Theorem 6.12(1) of [TakeutiZaring] p. 27, analogous to
       ~ tz6.12c .  (Contributed by AV, 5-Sep-2022.) $)
    tz6.12c-afv2 $p |- ( E! y A F y -> ( ( F '''' A ) = y <-> A F y ) ) $=
      ( cv wbr weu cafv2 wceq nfeu1 nfv euex tz6.12-1-afv2 expcom breq2 biimprd
      syli exlimimdd syl5ibcom impbid ) BADZCEZAFZBCGZTHZUAUBBUCCEZUDUAUBUAUEAU
      AAIUEAJUAAKUAUBUDUEUAUBUDABCLMZUDUEUAUCTBCNZOPQUGRUFS $.
  $}

  ${
    $d y F $.  $d y A $.  $d y B $.
    $( Corollary of Theorem 6.12(2) of [TakeutiZaring] p. 27. analogous to
       ~ tz6.12i .  (Contributed by AV, 5-Sep-2022.) $)
    tz6.12i-afv2 $p |- ( B e. ran F -> ( ( F '''' A ) = B -> A F B ) ) $=
      ( vy cafv2 wceq crn wcel wbr wi cv eleq1 weu wb wdfat dfatafv2rnb dfdfat2
      cdm breq2 3imtr3d simprbi sylbir tz6.12c-afv2 syl biimpcd sylbird vtocleg
      eqcoms pm2.43i a1i com12 ) ACEZBFZBCGZHZABCIZUMULUNHZAULCIZUOUPUQURJZUMUQ
      URUSDULUNDKZULFUTUNHZAUTCIZUQURVAVBJULUTULUTFZVAUQVBULUTUNLUQVCVBUQVBDMZV
      CVBNUQACOZVDACPVEACRHVDDACQUAUBDACUCUDUEUFUHUTULUNLUTULACSTUGUIUJULBUNLUL
      BACSTUK $.
  $}

  ${
    $d x A $.  $d x B $.  $d x F $.  $d x V $.  $d x W $.
    $( The second argument of a binary relation on a function is the function's
       value, analogous to ~ funbrfv .  (Contributed by AV, 7-Sep-2022.) $)
    funressnbrafv2 $p |- ( ( ( A e. V /\ B e. W ) /\ Fun ( F |` { A } ) )
                           -> ( A F B -> ( F '''' A ) = B ) ) $=
      ( vx wcel wa csn cres wfun wbr cafv2 wceq simpllr cv eleq1 anbi2d anbi1d
      wi breq2 anbi12d eqeq2 imbi12d weu funressneu 3expa tz6.12-1-afv2 syl2an2
      id vtoclg mpcom ex ) ADGZBEGZHZCAIJKZHZABCLZACMZBNZUOURUSHZVAUNUOUQUSOUNF
      PZEGZHZUQHZAVCCLZHZUTVCNZTVBVATFBEVCBNZVHVBVIVAVJVFURVGUSVJVEUPUQVJVDUOUN
      VCBEQRSVCBACUAUBVCBUTUCUDVGVGVFVGFUEZVIVGUJVEUQVGVKFAVCCDEUFUGFACUHUIUKUL
      UM $.

    $( Equivalence of function value and binary relation, analogous to
       ~ fnbrfvb or ~ funbrfvb . ` B e. _V ` is required, because otherwise
       ` A F B <-> (/) e. F ` can be true, but ` ( F '''' A ) = B ` is always
       false (because of ~ dfatafv2ex ).  (Contributed by AV, 6-Sep-2022.) $)
    dfatbrafv2b $p |- ( ( F defAt A /\ B e. W )
                        -> ( ( F '''' A ) = B <-> A F B ) ) $=
      ( vx wdfat wcel wa cafv2 wceq wbr cv wb cvv dfatafv2ex adantr eqeq2 breq2
      eqid simpr bibi12d adantl cdm dfdfat2 tz6.12c-afv2 simplbiim vtocld mpbii
      weu syl5ibcom csn cres wfun wi df-dfat simpll jca31 sylanb funressnbrafv2
      syl impbid ) ACFZBDGZHZACIZBJZABCKZVDAVECKZVFVGVDVEVEJZVHVESVDVEELZJZAVJC
      KZMZVIVHMZEVENVBVENGVCACOPVJVEJZVMVNMVDVOVKVIVLVHVJVEVEQVJVEACRUAUBVBVMVC
      VBACUCZGZVLEUIVMEACUDEACUEUFPUGUHVEBACRUJVDVQVCHCAUKULUMZHZVGVFUNVBVQVRHZ
      VCVSACUOVTVCHVQVCVRVQVRVCUPVTVCTVTVRVCVQVRTPUQURABCVPDUSUTVA $.
  $}

  $( Equivalence of function value and ordered pair membership, analogous to
     ~ fnopfvb or ~ funopfvb .  (Contributed by AV, 6-Sep-2022.) $)
  dfatopafv2b $p |- ( ( F defAt A /\ B e. W )
                      -> ( ( F '''' A ) = B <-> <. A , B >. e. F ) ) $=
    ( wdfat wcel wa cafv2 wceq wbr cop dfatbrafv2b df-br bitrdi ) ACEBDFGACHBIA
    BCJABKCFABCDLABCMN $.

  ${
    $d x A $.  $d x B $.  $d x F $.
    $( The second argument of a binary relation on a function is the function's
       value, analogous to ~ funbrfv .  (Contributed by AV, 6-Sep-2022.) $)
    funbrafv2 $p |- ( Fun F -> ( A F B -> ( F '''' A ) = B ) ) $=
      ( vx wfun wbr cafv2 wceq cvv wcel wa wrel funrel brrelex2 sylan cv anbi2d
      wi breq2 eqeq2 imbi12d funeu tz6.12-1-afv2 sylan2 anabss7 vtoclg mpcom ex
      weu ) CEZABCFZACGZBHZBIJZUJUKKZUMUJCLUKUNCMABCNOUJADPZCFZKZULUPHZRUOUMRDB
      IUPBHZURUOUSUMUTUQUKUJUPBACSQUPBULTUAUJUQUSURUQUQDUIUSDAUPCUBDACUCUDUEUFU
      GUH $.

    $( Equivalence of function value and binary relation, analogous to
       ~ fnbrfvb .  (Contributed by AV, 6-Sep-2022.) $)
    fnbrafv2b $p |- ( ( F Fn A /\ B e. A )
                      -> ( ( F '''' B ) = C <-> B F C ) ) $=
      ( vx wfn wcel wa cafv2 wceq wbr eqid cv wb cvv wdfat fundmdfat funfni syl
      breq2 dfatafv2ex eqeq2 bibi12d adantl tz6.12c-afv2 vtocld mpbii syl5ibcom
      weu fneu wi wfun fnfun funbrafv2 adantr impbid ) DAFZBAGZHZBDIZCJZBCDKZUS
      BUTDKZVAVBUSUTUTJZVCUTLUSUTEMZJZBVEDKZNZVDVCNZEUTOUSBDPZUTOGVJABDBDQRBDUA
      SVEUTJZVHVINUSVKVFVDVGVCVEUTUTUBVEUTBDTUCUDUSVGEUIVHEABDUJEBDUESUFUGUTCBD
      TUHUQVBVAUKZURUQDULVLADUMBCDUNSUOUP $.
  $}

  $( Equivalence of function value and ordered pair membership, analogous to
     ~ fnopfvb .  (Contributed by AV, 6-Sep-2022.) $)
  fnopafv2b $p |- ( ( F Fn A /\ B e. A )
                    -> ( ( F '''' B ) = C <-> <. B , C >. e. F ) ) $=
    ( wfn wcel wa cafv2 wceq wbr cop fnbrafv2b df-br bitrdi ) DAEBAFGBDHCIBCDJB
    CKDFABCDLBCDMN $.

  $( Equivalence of function value and binary relation, analogous to
     ~ funbrfvb .  (Contributed by AV, 6-Sep-2022.) $)
  funbrafv22b $p |- ( ( Fun F /\ A e. dom F )
                      -> ( ( F '''' A ) = B <-> A F B ) ) $=
    ( wfun cdm wfn wcel cafv2 wceq wbr wb funfn fnbrafv2b sylanb ) CDCCEZFAOGAC
    HBIABCJKCLOABCMN $.

  $( Equivalence of function value and ordered pair membership, analogous to
     ~ funopfvb .  (Contributed by AV, 6-Sep-2022.) $)
  funopafv2b $p |- ( ( Fun F /\ A e. dom F )
                     -> ( ( F '''' A ) = B <-> <. A , B >. e. F ) ) $=
    ( wfun cdm wfn wcel cafv2 wceq cop wb funfn fnopafv2b sylanb ) CDCCEZFAOGAC
    HBIABJCGKCLOABCMN $.

  ${
    $d x y A $.  $d x y F $.
    $( Singleton of function value, analogous to ~ fnsnfv .  (Contributed by
       AV, 7-Sep-2022.) $)
    dfatsnafv2 $p |- ( F defAt A -> { ( F '''' A ) } = ( F " { A } ) ) $=
      ( vy vx wdfat cv cafv2 wceq cab wbr csn cima eqcom cvv dfatbrafv2b bitrid
      wb elvd abbidv df-sn a1i cdm wcel weu dfdfat2 imasng adantr sylbi 3eqtr4d
      wa ) ABEZCFZABGZHZCIZAULBJZCIZUMKZBAKLZUKUNUPCUNUMULHZUKUPULUMMUKUTUPQCAU
      LBNORPSURUOHUKCUMTUAUKABUBZUCZADFBJDUDZUJUSUQHZDABUEVBVDVCCAVABUFUGUHUI
      $.
  $}

  ${
    $d F x $.  $d A x $.
    $( A definition of function value in terms of iota, analogous to ~ dffv3 .
       (Contributed by AV, 6-Sep-2022.) $)
    dfafv23 $p |- ( F defAt A
                    -> ( F '''' A ) = ( iota x x e. ( F " { A } ) ) ) $=
      ( wdfat cafv2 cv wbr cio csn cima wcel dfatafv2iota wb cvv wa cop cdm weu
      dfdfat2 simplbi elimasng sylan df-br bitr4di elvd iotabidv eqtr4d ) BCDZB
      CEBAFZCGZAHUICBIJKZAHABCLUHUKUJAUHUKUJMAUHUINKZOUKBUIPCKZUJUHBCQZKZULUKUM
      MUHUOUJARABCSTCBUIUNNUAUBBUICUCUDUEUFUG $.
  $}

  ${
    $d x y A $.  $d x y F $.  $d x y G $.
    $( Domain of a function composition, analogous to ~ dmfco .  (Contributed
       by AV, 7-Sep-2022.) $)
    dfatdmfcoafv2 $p |- ( G defAt A -> ( A e. dom ( F o. G )
                                          <-> ( G '''' A ) e. dom F ) ) $=
      ( vy vx wdfat cv cop wcel wex wa cdm wceq cvv wb elvd exbidv bitrd eldm2g
      syl cafv2 ccom dfatafv2ex opeq1 eleq1d ceqsexgv bicomd dfatopafv2b bitrid
      eqcom anbi1d csn cres wfun df-dfat opelco2g adantr sylbi 3bitr4rd ) ACFZA
      CUAZDGZHZBIZDJZAEGZHCIZVFVBHZBIZKZEJZDJZVABLIZABCUBZLIZUTVDVKDUTVDVFVAMZV
      IKZEJZVKUTVANIZVDVROACUCZVSVRVDVIVDEVANVPVHVCBVFVAVBUDUEUFUGTUTVQVJEUTVPV
      GVIVPVAVFMZUTVGVFVAUJUTWAVGOEAVFCNUHPUIUKQRQUTVSVMVEOVTDVABNSTUTACLZIZCAU
      LUMUNZKVOVLOZACUOWCWEWDWCVOAVBHVNIZDJVLDAVNWBSWCWFVKDWCWFVKODEAVBBCWBNUPP
      QRUQURUS $.
  $}

  ${
    $d F y z $.  $d G y z $.  $d X y z $.
    $( Lemma for ~ dfatco .  (Contributed by AV, 8-Sep-2022.) $)
    dfatcolem $p |- ( ( G defAt X /\ F defAt ( G '''' X ) )
                      -> E! y X ( F o. G ) y ) $=
      ( vz wdfat cafv2 wa cv wbr weu wex cdm wcel wi wceq wb cvv adantl syl2anc
      ccom dfdfat2 wal eqidd cres wfun df-dfat simplbi dfatbrafv2b sylan2 mpbid
      simpr dfatafv2ex breq12 ancoms anbi12d spc2egv mp2and tz6.12c-afv2 adantr
      csn breq2 sylbi breq1 exbiri sylbird impd exlimdv alrimiv sylan2b pm2.43i
      euim com12 vex a1i brcog syl2an eubidv mpbird ) DCFZDCGZBFZHZDAIZBCUAJZAK
      DEIZCJZWFWDBJZHZELZAKZWCWKWBVTWABMZNZWAWDBJZAKZHZWCWKOZAWABUBWPWQVTWOWQWM
      WCWOWKWCWJALZWJWNOZAUCWOWKOWCDWACJZWAWABGZBJZWRWCWAWAPZWTWCWAUDWBVTWMXCWT
      QWBWMBWAVAUEUFWABUGUHZDWACWLUIUJUKWCXAXAPZXBWCXAUDWCWBXARNZXEXBQVTWBULWBX
      FVTWABUMSZWAXABRUITUKWCXFWMWTXBHZWROXGWBWMVTXDSWIXHAEXAWARWLWDXAPZWFWAPZH
      WGWTWHXBXJWGWTQXIWFWADCVBSXJXIWHXBQWFWAWDXABUNUOUPUQTURWCWSAWCWIWNEWCWGWH
      WNWCWGWAWFPZWHWNOZVTXKWGQZWBVTDCMZNZWGEKZHXMEDCUBXPXMXOEDCUSSVCUTWBXKXLOV
      TWBXKWNWHXKWNWHQWBWAWFWDBVDSVESVFVGVHVIWJWNAVLTVMSSVJVKWCWEWJAVTXOWDRNZWE
      WJQWBVTXOCDVAUEUFDCUGUHXQWBAVNVOEDWDBCXNRVPVQVRVS $.
  $}

  ${
    $d F x y $.  $d G x y $.  $d X x y $.
    $( The predicate "defined at" for a function composition.  (Contributed by
       AV, 8-Sep-2022.) $)
    dfatco $p |- ( ( G defAt X /\ F defAt ( G '''' X ) )
                   -> ( F o. G ) defAt X ) $=
      ( vy vx wdfat cafv2 wa ccom cdm wcel wbr weu wex dfatcolem euex syl df-dm
      cv cab eleq2i wb cres wfun df-dfat simplbi adantr wceq breq1 exbidv elabg
      csn bitrid mpbird dfdfat2 sylanbrc ) CBFZCBGAFZHZCABIZJZKZCDSZUTLZDMZCUTF
      USVBVDDNZUSVEVFDABCOZVDDPQVBCESZVCUTLZDNZETZKZUSVFVAVKCEDUTRUAUSCBJZKZVLV
      FUBUQVNURUQVNBCULUCUDCBUEUFUGVJVFECVMVHCUHVIVDDVHCVCUTUIUJUKQUMUNVGDCUTUO
      UP $.
  $}

  ${
    $d F x $.  $d G x $.  $d X x $.
    $( Value of a function composition, analogous to ~ fvco2 .  (Contributed by
       AV, 8-Sep-2022.) $)
    afv2co2 $p |- ( ( G defAt X /\ F defAt ( G '''' X ) )
                    -> ( ( F o. G ) '''' X ) = ( F '''' ( G '''' X ) ) ) $=
      ( vx wdfat cafv2 wa cv ccom csn cima wcel imaco dfatsnafv2 adantr imaeq2d
      cio wceq eqtr4id dfafv23 eleq2d iotabidv dfatco syl adantl 3eqtr4d ) CBEZ
      CBFZAEZGZDHZABIZCJZKZLZDQZUKAUHJZKZLZDQZCULFZUHAFZUJUOUSDUJUNURUKUJUNABUM
      KZKURABUMMUJUQVCAUGUQVCRUICBNOPSUAUBUJCULEVAUPRABCUCDCULTUDUIVBUTRUGDUHAT
      UEUF $.
  $}

  ${
    $d F w x y z $.  $d ph w x y z $.
    rlimdmafv2.1 $e |- ( ph -> F : A --> CC ) $.
    rlimdmafv2.2 $e |- ( ph -> sup ( A , RR* , < ) = +oo ) $.
    $( Two ways to express that a function has a limit, analogous to ~ rlimdm .
       (Contributed by AV, 5-Sep-2022.) $)
    rlimdmafv2 $p |- ( ph -> ( F e. dom ~~>r <-> F ~~>r ( ~~>r '''' F ) ) ) $=
      ( vx vw vy vz crli wcel wbr cv wex wa wceq cvv weq breq2 adantr cdm cafv2
      eldmg ibi simpr cio wdfat weu rlimrel brrelex1i adantl vex a1i breldmg wi
      syl3anc wal biimprd spimevw cc wf cxr clt csup cpnf simprl simprr rlimuni
      ex alrimivv eu4 sylanbrc dfdfat2 dfatafv2iota syl syl5ibrcom impbid iota5
      wb expr elvd eqtrd breqtrrd exlimdv syl5 releldmi impbid1 ) ACJUAZKZCCJUB
      ZJLZWICFMZJLZFNZAWKWIWNFCJWHUCUDAWMWKFAWMWKAWMOZCWLWJJAWMUEZWOWJCGMZJLZGU
      FZWLWOCJUGZWJWSPWOWICHMZJLZHUHZWTWOCQKZWLQKZWMWIWMXDACWLJUIUJUKXEWOFULUMW
      PCWLQQJUNUPWOXBHNZXBCIMZJLZOZHIRZUOZIUQHUQXCWMXFAWMXBHFHFRXBWMXAWLCJSURUS
      UKWOXKHIWOXIXJWOXIOBXAXGCWOBUTCVAZXIAXLWMDTTWOBVBVCVDVEPZXIAXMWMETTWOXBXH
      VFWOXBXHVGVHVIVJXBXHHIXAXGCJSVKVLHCJVMVLGCJVNVOWOWSWLPFWOWRGWLQWOWRGFRZVS
      XEWOWRXNAWMWRXNAWMWROZOBWQWLCAXLXODTAXMXOETAWMWRVGAWMWRVFVHVTWOWRXNWMWPWQ
      WLCJSVPVQTVRWAWBWCVIWDWECWJJUIWFWG $.
  $}

$( *** Relationship between the original and the alternate definition ***
   *** of the value of a function.                                    *** $)

  ${
    $d x A $.  $d x F $.
    $( Alternate definition of ` ( F '''' A ) ` using ` ( F `` A ) ` directly.
       (Contributed by AV, 3-Sep-2022.) $)
    dfafv22 $p |- ( F '''' A ) = if ( F defAt A , ( F ` A ) , ~P U. ran F ) $=
      ( vx cafv2 wdfat cv wbr cio crn cuni cpw cif cfv df-afv2 wceq df-fv ifeq1
      eqcomi ax-mp eqtri ) ABDABEZACFBGCHZBIJKZLZUAABMZUCLZCABNUBUEOUDUFOUEUBCA
      BPRUAUBUEUCQST $.
  $}

  $( If the alternate function value at an argument is undefined, i.e., not in
     the range of the function, the function's value at this argument is the
     empty set.  (Contributed by AV, 3-Sep-2022.) $)
  afv2ndeffv0 $p |- ( ( F '''' A ) e/ ran F -> ( F ` A ) = (/) ) $=
    ( cafv2 crn wnel cdm wcel wn csn cres wfun wo c0 wceq wa df-nel dfatafv2rnb
    cfv wdfat df-dfat bitr3i notbii ianor 3bitri ndmfv nfunsn jaoi sylbi ) ABCZ
    BDZEZABFGZHZBAIJKZHZLZABRMNZUKUIUJGZHULUNOZHUPUIUJPURUSURABSUSABQABTUAUBULU
    NUCUDUMUQUOABUEABUFUGUH $.

  $( If a function is defined at a class ` A ` , the alternate function value
     equals the function's value at ` A ` .  (Contributed by AV,
     3-Sep-2022.) $)
  dfatafv2eqfv $p |- ( F defAt A -> ( F '''' A ) = ( F ` A ) ) $=
    ( wdfat cafv2 cfv crn cuni cpw cif dfafv22 iftrue eqtrid ) ABCZABDMABEZBFGH
    ZINABJMNOKL $.

  $( If the alternate function value is defined, i.e., in the range of the
     function, the alternate function value equals the function's value.
     (Contributed by AV, 3-Sep-2022.) $)
  afv2rnfveq $p |- ( ( F '''' A ) e. ran F -> ( F '''' A ) = ( F ` A ) ) $=
    ( cafv2 crn wcel wdfat cfv wceq dfatafv2rnb dfatafv2eqfv sylbir ) ABCZBDEAB
    FLABGHABIABJK $.

  $( If the alternate function value at an argument is the empty set, the
     function's value at this argument is the empty set.  (Contributed by AV,
     3-Sep-2022.) $)
  afv20fv0 $p |- ( ( F '''' A ) = (/) -> ( F ` A ) = (/) ) $=
    ( wdfat cafv2 c0 wceq cfv afv20defat dfatafv2eqfv eqcomd adantr simpr eqtrd
    wa mpancom ) ABCZABDZEFZABGZEFABHPRNSQEPSQFRPQSABIJKPRLMO $.

  $( If the function's value at an argument is not the empty set, it equals the
     alternate function value at this argument.  (Contributed by AV,
     3-Sep-2022.) $)
  afv2fvn0fveq $p |- ( ( F ` A ) =/= (/) -> ( F '''' A ) = ( F ` A ) ) $=
    ( cfv c0 wne wdfat cafv2 wceq cdm wcel csn cres wfun wa fvfundmfvn0 df-dfat
    sylibr dfatafv2eqfv syl ) ABCZDEZABFZABGTHUAABIJBAKLMNUBABOABPQABRS $.

  $( If the function's value at an argument is the empty set, then the
     alternate function value at this argument is the empty set or undefined.
     (Contributed by AV, 3-Sep-2022.) $)
  afv2fv0 $p |- ( ( F ` A ) = (/) -> ( ( F '''' A ) = (/)
                                    \/ ( F '''' A ) e/ ran F ) ) $=
    ( cafv2 c0 wceq crn wnel wo cfv wn ioran wcel nnel afv2rnfveq eqeq1d notbid
    wa sylbi biimpac con4i ) ABCZDEZUABFZGZHZABIZDEZUEJUBJZUDJZQUGJZUBUDKUIUHUJ
    UIUBUGUIUAUFDUIUAUCLUAUFEUAUCMABNROPSRT $.

  $( The function's value at an argument is the empty set if and only if the
     alternate function value at this argument is the empty set or undefined.
     (Contributed by AV, 3-Sep-2022.) $)
  afv2fv0b $p |- ( ( F ` A ) = (/) <-> ( ( F '''' A ) = (/)
                                       \/ ( F '''' A ) e/ ran F ) ) $=
    ( cfv c0 wceq cafv2 crn wnel wo afv2fv0 afv20fv0 afv2ndeffv0 jaoi impbii )
    ABCDEZABFZDEZPBGHZIABJQORABKABLMN $.

  $( If a set is in the range of a function, the function's value at an
     argument is the empty set if and only if the alternate function value at
     this argument is either the empty set or undefined.  (Contributed by AV,
     11-Sep-2022.) $)
  afv2fv0xorb $p |- ( (/) e. ran F -> ( ( F ` A ) = (/)
                    <-> ( ( F '''' A ) = (/) \/_ ( F '''' A ) e/ ran F ) ) ) $=
    ( cfv c0 wceq cafv2 crn wnel wo wcel wxo afv2fv0b afv2orxorb bitrid ) ABCDE
    ABFZDEZOBGZHZIDQJPRKABLADBMN $.

