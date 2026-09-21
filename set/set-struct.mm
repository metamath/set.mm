$(
###############################################################################
  BASIC STRUCTURES
###############################################################################
$)


$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Extensible structures
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Basic definitions
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  An "extensible structure" (or "structure" in short, at least in this section)
  is used to define a specific group, ring, poset, and so on.  An extensible
  structure can contain many components.  For example, a group will have at
  least two components (base set and operation), although it can be further
  specialized by adding other components such as a multiplicative operation for
  rings (and still remain a group per our definition).  Thus, every ring is
  also a group.  This extensible structure approach allows theorems from more
  general structures (such as groups) to be reused for more specialized
  structures (such as rings) without having to reprove anything.  Structures
  are common in mathematics, but in informal (natural language) proofs the
  details are assumed in ways that we must make explicit.

  An extensible structure is implemented as a function (a set of ordered pairs)
  on a finite (and not necessarily sequential) subset of ` NN ` .  The
  function's argument is the index of a structure component (such as ` 1 ` for
  the base set of a group), and its value is the component (such as the base
  set).  By convention, we normally avoid direct reference to the hard-coded
  numeric index and instead use structure component extractors such as ~ ndxid
  and ~ strfv .  Using extractors makes it easier to change numeric indices and
  also makes the components' purpose clearer.  For example, as noted in
  ~ ndxid , we can refer to a specific poset with base set ` B ` and order
  relation ` L ` using the extensible structure
  ` { <. ( Base `` ndx ) , B >. , <. ( le `` ndx ) , L >. } ` rather than
  ` { <. 1 , B >. , <. ; 1 0 , L >. } ` .  See section header comment
  ~ mmtheorems.html#cnx for more details on numeric indices versus the
  structure component extractors.

  There are many other possible ways to handle structures.  We chose this
  extensible structure approach because this approach (1) results in simpler
  notation than other approaches we are aware of, and (2) is easier to do
  proofs with.  We cannot use an approach that uses "hidden" arguments;
  Metamath does not support hidden arguments, and in any case we want nothing
  hidden.  It would be possible to use a categorical approach (e.g., something
  vaguely similar to Lean's mathlib).  However, instances (the chain of proofs
  that an ` X ` is a ` Y ` via a bunch of forgetful functors) can cause serious
  performance problems for automated tooling, and the resulting proofs would be
  painful to look at directly (in the case of Lean, they are long past the
  level where people would find it acceptable to look at them directly).
  Metamath is working under much stricter conditions than this, and it has
  still managed to achieve about the same level of flexibility through this
  "extensible structure" approach.

  To create a substructure of a given extensible structure, you can simply use
  the multifunction restriction operator for extensible structures ` |``s ` as
  defined in ~ df-ress .  This can be used to turn statements about rings into
  statements about subrings, modules into submodules, etc.  This definition
  knows nothing about individual structures and merely truncates the ` Base `
  set while leaving operators alone.  Individual kinds of structures will need
  to handle this behavior by ignoring operators' values outside the range (like
  ` Ring ` ), defining a function using the base set and applying that (like
  ` TopGrp ` ), or explicitly truncating the slot before use (like ` MetSp ` ).
  For example, the unital ring of integers ` ZZring ` is defined in ~ df-zring
  as simply ` ZZring = ( CCfld |``s ZZ ) ` .  This can be similarly done for
  all other subsets of ` CC ` , which has all the structure we can show applies
  to it, and this all comes "for free".  Should we come up with some new
  structure in the future that we wish ` CC ` to inherit, then we change the
  definition of ` CCfld ` , reprove all the slot extraction theorems, add a new
  one, and that's it.  None of the other downstream theorems have to change.

  Note that the construct of ~ df-prds addresses a different situation.  It is
  not possible to have ` SubGrp ` and ` SubRing ` be the same thing because
  they produce different outputs on the same input.  The subgroups of an
  extensible structure treated as a group are not the same as the subrings of
  that same structure.  With ~ df-prds it can actually reasonably perform the
  task, that is, being the product group given a family of groups, while also
  being the product ring given a family of rings.  There is no contradiction
  here because the group part of a product ring is a product group.

  There is also a general theory of "substructure algebras", in the form of
  ~ df-mre and ~ df-acs .  ` SubGrp ` is a Moore collection, as is
  ` SubRing ` , ` SubRng ` and many other substructure collections.  But it is
  not useful for picking out a particular collection of interest; ` SubRing `
  and ` SubGrp ` still need to be defined and they are distinct --- nothing is
  going to select these definitions for us.

  Extensible structures only work well when they represent concrete categories,
  where there is a "base set", morphisms are functions, and subobjects are
  subsets with induced operations.  In short, they primarily work well for
  "sets with (some) extra structure".  Extensible structures may not suffice
  for more complicated situations.  For example, in manifolds, ` |``s ` would
  not work.  That said, extensible structures are sufficient for many of the
  structures that set.mm currently considers, and offer a good compromise for a
  goal-oriented formalization.

$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Extensible structures as structures with components
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $c Struct $.

  $( Extend class notation with the class of structures with components
     numbered below ` A ` . $)
  cstr $a class Struct $.

  ${
    $d f x $.
    $( Define a structure with components in ` M ... N ` .  This is not a
       requirement for groups, posets, etc., but it is a useful assumption for
       component extraction theorems.

       As mentioned in the section header, an "extensible structure should be
       implemented as a function (a set of ordered pairs)".  The current
       definition, however, is less restrictive: it allows for classes which
       contain the empty set ` (/) ` to be extensible structures.  Because of
       ~ 0nelfun , such classes cannot be functions.  Without the empty set,
       however, a structure must be a function, see ~ structn0fun :
       ` F Struct X -> Fun ( F \ { (/) } ) ` .

       Allowing an extensible structure to contain the empty set ensures that
       expressions like ` { <. A , B >. , <. C , D >. } ` are structures
       without asserting or implying that ` A ` , ` B ` , ` C ` and ` D ` are
       sets (if ` A ` or ` B ` is a proper class, then ` <. A , B >. = (/) ` ,
       see ~ opprc ).  This is used critically in ~ strle1 , ~ strle2 ,
       ~ strle3 and ~ strleun to avoid sethood hypotheses on the "payload"
       sets: without this, ~ ipsstr and theorems like it will have many sethood
       assumptions, and may not even be usable in the empty context.  Instead,
       the sethood assumption is deferred until it is actually needed, e.g.,
       ~ ipsbase , which requires that the base set be a set but not any of the
       other components.  Usually, a concrete structure like ` CCfld ` does not
       contain the empty set, and therefore is a function, see ~ cnfldfun .
       (Contributed by Mario Carneiro, 29-Aug-2015.) $)
    df-struct $a |- Struct = { <. f , x >. | ( x e. ( <_ i^i ( NN X. NN ) ) /\
       Fun ( f \ { (/) } ) /\ dom f C_ ( ... ` x ) ) } $.
  $}

  ${
    $d f x $.
    $( The structure relation is a relation.  (Contributed by Mario Carneiro,
       29-Aug-2015.) $)
    brstruct $p |- Rel Struct $=
      ( vx vf cv cle cn cxp cin wcel c0 csn cdif wfun cdm cfz cfv wss df-struct
      w3a cstr relopabiv ) ACZDEEFGHBCZIJKLUBMUANOPRBASABQT $.
  $}

  ${
    $d f x F $.  $d f x X $.
    $( The property of being a structure with components in
       ` ( 1st `` X ) ... ( 2nd `` X ) ` .  (Contributed by Mario Carneiro,
       29-Aug-2015.) $)
    isstruct2 $p |- ( F Struct X <-> ( X e. ( <_ i^i ( NN X. NN ) ) /\
        Fun ( F \ { (/) } ) /\ dom F C_ ( ... ` X ) ) ) $=
      ( vx vf cstr cvv wcel wa cle cdif wfun cdm cfz cfv wss w3a cun cfn wceq
      cn wbr cxp cin c0 csn brstruct brrelex12i ssun1 undif1 sseqtrri wfn simp2
      funfnd c1st c2nd cop elinel2 1st2nd2 syl 3ad2ant1 fveq2d co fzfi eqeltrri
      df-ov difss dmss ax-mp simp3 sstrid ssfid fnfi syl2anc p0ex unexg sylancl
      eqeltrdi ssexg sylancr elex jca simpr eleq1d simpl difeq1d funeqd sseq12d
      cv dmeqd 3anbi123d df-struct brabga pm5.21nii ) ABEUAAFGZBFGZHBITTUBZUCZG
      ZAUDUEZJZKZALZBMNZOZPZABEUFUGXEWNWOXEAWTWSQZOXFFGZWNAAWSQXFAWSUHAWSUIUJXE
      WTRGZWSFGXGXEWTWTLZUKXIRGXHXEWTWRXAXDULUMXEXCXIXEXCBUNNZBUONZUPZMNZRXEBXL
      MWRXABXLSZXDWRBWPGXNBIWPUQBTTURUSUTVAXJXKMVBXMRXJXKMVEXJXKVCVDVQXEXIXBXCW
      TAOXIXBOAWSVFWTAVGVHWRXAXDVIVJVKXIWTVLVMVNWTWSRFVOVPAXFFVRVSWRXAWOXDBWQVT
      UTWACWHZWQGZDWHZWSJZKZXQLZXOMNZOZPXEDCABEFFXQASZXOBSZHZXPWRXSXAYBXDYEXOBW
      QYCYDWBZWCYEXRWTYEXQAWSYCYDWDZWEWFYEXTXBYAXCYEXQAYGWIYEXOBMYFVAWGWJCDWKWL
      WM $.
  $}

  $( A structure is a set.  (Contributed by AV, 10-Nov-2021.) $)
  structex $p |- ( G Struct X -> G e. _V ) $=
    ( cstr brstruct brrelex1i ) ABCDE $.

  $( A structure without the empty set is a function.  (Contributed by AV,
     13-Nov-2021.) $)
  structn0fun $p |- ( F Struct X -> Fun ( F \ { (/) } ) ) $=
    ( cstr wbr cle cxp cin wcel csn cdif wfun cdm cfz cfv wss isstruct2 simp2bi
    cn c0 ) ABCDBERRFGHASIJKALBMNOABPQ $.

  $( The property of being a structure with components in ` M ... N ` .
     (Contributed by Mario Carneiro, 29-Aug-2015.) $)
  isstruct $p |- ( F Struct <. M , N >. <->
    ( ( M e. NN /\ N e. NN /\ M <_ N ) /\
      Fun ( F \ { (/) } ) /\ dom F C_ ( M ... N ) ) ) $=
    ( cop cstr wbr cle cn cxp cin wcel c0 csn cdif wfun cdm cfz wss w3a wa biid
    cfv co isstruct2 df-3an brinxp2 df-br 3bitr2i df-ov sseq2i 3anbi123i bitr4i
    ) ABCDZEFUMGHHIJZKZALMNOZAPZUMQUBZRZSBHKZCHKZBCGFZSZUPUQBCQUCZRZSAUMUDVCUOU
    PUPVEUSVCUTVATVBTBCUNFUOUTVAVBUEHHBCGUFBCUNUGUHUPUAVDURUQBCQUIUJUKUL $.

  $( Two ways to express the relational part of a structure.  (Contributed by
     Mario Carneiro, 29-Aug-2015.) $)
  structcnvcnv $p |- ( F Struct X -> `' `' F = ( F \ { (/) } ) ) $=
    ( cstr wbr ccnv c0 csn cdif wss cin wceq wcel cvv cxp 0nelxp cnvcnv eqsstri
    wn inss2 cnvss sseli mto disjsn mpbir cnvcnvss reldisj ax-mp mpbi wrel wfun
    wb a1i structn0fun funrel syl dfrel2 sylib difss mp2b eqsstrrdi eqssd ) ABC
    DZAEZEZAFGZHZVDVFIZVBVDVEJFKZVGVHFVDLZRVIFMMNZLMMOVDVJFVDAVJJVJAPAVJSQUAUBV
    DFUCUDVDAIVHVGUKAUEVDVEAUFUGUHULVBVFVFEZEZVDVBVFUIZVLVFKVBVFUJVMABUMVFUNUOV
    FUPUQVFAIVKVCIVLVDIAVEURVFATVKVCTUSUTVA $.

  $( The converse of the converse of a structure is a function.  Closed form of
     ~ structfun .  (Contributed by AV, 12-Nov-2021.) $)
  structfung $p |- ( F Struct X -> Fun `' `' F ) $=
    ( cstr wbr ccnv wfun c0 csn cdif structn0fun structcnvcnv funeqd mpbird ) A
    BCDZAEEZFAGHIZFABJNOPABKLM $.

  ${
    structfun.1 $e |- F Struct X $.
    $( Convert between two kinds of structure closure.  (Contributed by Mario
       Carneiro, 29-Aug-2015.)  (Proof shortened by AV, 12-Nov-2021.) $)
    structfun $p |- Fun `' `' F $=
      ( cstr wbr ccnv wfun structfung ax-mp ) ABDEAFFGCABHI $.
  $}

  ${
    structfn.1 $e |- F Struct <. M , N >. $.
    $( Convert between two kinds of structure closure.  (Contributed by Mario
       Carneiro, 29-Aug-2015.) $)
    structfn $p |- ( Fun `' `' F /\ dom F C_ ( 1 ... N ) ) $=
      ( ccnv wfun cdm c1 cfz co wss cop structfun wcel cle wbr w3a mpbi simp1i
      cn csn cdif cstr isstruct simp3i cuz cfv elnnuz fzss1 ax-mp sstri pm3.2i
      c0 ) AEEFAGZHCIJZKABCLZDMUNBCIJZUOBTNZCTNZBCOPZQZAUMUAUBFZUNUQKZAUPUCPVAV
      BVCQDABCUDRZUEBHUFUGNZUQUOKURVEURUSUTVAVBVCVDSSBUHRBHCUIUJUKUL $.
  $}

  ${
    strleun.f $e |- F Struct <. A , B >. $.
    strleun.g $e |- G Struct <. C , D >. $.
    strleun.l $e |- B < C $.
    $( Combine two structures into one.  (Contributed by Mario Carneiro,
       29-Aug-2015.) $)
    strleun $p |- ( F u. G ) Struct <. A , D >. $=
      ( wbr cn wcel cle w3a wfun cdm wss simp1i mp2an ax-mp cun cop cstr c0 csn
      cdif cfz co isstruct mpbi simp2i simp3i nnrei ltleii letri 3pm3.2i wa cin
      wceq pm3.2i difss dmss sstri ss2in clt fzdisj sseq0 funun difundir funeqi
      mpbir dmun cuz cfv cz nnzi eluz2 mpbir3an fzss2 fzss1 unssi eqsstri ) EFU
      AZADUBUCJAKLZDKLZADMJZNWCUDUEZUFZOZWCPZADUGUHZQWDWEWFWDBKLZABMJZWDWLWMNZE
      WGUFZOZEPZABUGUHZQZEABUBUCJWNWPWSNGEABUIUJZRZRZCKLZWECDMJZXCWEXDNZFWGUFZO
      ZFPZCDUGUHZQZFCDUBUCJXEXGXJNHFCDUIUJZRZUKZACMJZXDWFWMBCMJZXNWDWLWMXAULBCB
      WDWLWMXAUKZUMZCXCWEXDXLRZUMZIUNZABCAXBUMZXQXSUOSZXCWEXDXLULZACDYAXSDXMUMZ
      UOSUPWIWOXFUAZOZWPXGUQWOPZXFPZURZUDUSZYFWPXGWNWPWSWTUKXEXGXJXKUKUTYIWRXIU
      RZQZYKUDUSZYJYGWRQYHXIQYLYGWQWRWOEQYGWQQEWGVAWOEVBTWNWPWSWTULZVCYHXHXIXFF
      QYHXHQFWGVAXFFVBTXEXGXJXKULZVCYGWRYHXIVDSBCVEJYMIABCDVFTYIYKVGSWOXFVHSWHY
      EEFWGVIVJVKWJWQXHUAWKEFVLWQXHWKWQWRWKYNDBVMVNLZWRWKQYPBVOLDVOLBDMJZBXPVPD
      XMVPXOXDYQXTYCBCDXQXSYDUOSBDVQVRBADVSTVCXHXIWKYOCAVMVNLZXIWKQYRAVOLCVOLXN
      AXBVPCXRVPYBACVQVRCADVTTVCWAWBWCADUIVR $.
  $}

  ${
    strle1.i $e |- I e. NN $.
    strle1.a $e |- A = I $.
    $( Make a structure from a singleton.  (Contributed by Mario Carneiro,
       29-Aug-2015.) $)
    strle1 $p |- { <. A , X >. } Struct <. I , I >. $=
      ( cop csn cstr wbr cn wcel cle w3a c0 cdif wfun cdm cfz wss cvv co funsng
      nnrei leidi 3pm3.2i difss eqeltri mpan funss mpsyl wn fun0 opprc2 difeq1d
      sneqd difid eqtrdi funeqd mpbiri pm2.61i dmsnopss sneqi cz wceq nnzi fzsn
      ax-mp eqtr4i sseqtri isstruct mpbir3an ) ACFZGZBBFHIBJKZVNBBLIZMVMNGZOZPZ
      VMQZBBRUAZSVNVNVODDBBDUCUDUECTKZVRVQVMSWAVMPZVRVMVPUFAJKWAWBABJEDUGACJTUB
      UHVQVMUIUJWAUKZVRNPULWCVQNWCVQVPVPONWCVMVPVPWCVLNACUMUOUNVPUPUQURUSUTVSAG
      ZVTACVAWDBGZVTABEVBBVCKVTWEVDBDVEBVFVGVHVIVMBBVJVK $.

    strle2.j $e |- I < J $.
    strle2.k $e |- J e. NN $.
    strle2.b $e |- B = J $.
    $( Make a structure from a pair.  (Contributed by Mario Carneiro,
       29-Aug-2015.) $)
    strle2 $p |- { <. A , X >. , <. B , Y >. } Struct <. I , J >. $=
      ( cop cpr csn cun cstr df-pr strle1 strleun eqbrtri ) AELZBFLZMUANZUBNZOC
      DLPUAUBQCCDDUCUDACEGHRBDFJKRIST $.

    strle3.k $e |- J < K $.
    strle3.l $e |- K e. NN $.
    strle3.c $e |- C = K $.
    $( Make a structure from a triple.  (Contributed by Mario Carneiro,
       29-Aug-2015.) $)
    strle3 $p |- { <. A , X >. , <. B , Y >. , <. C , Z >. }
        Struct <. I , K >. $=
      ( cop ctp cpr csn cun cstr df-tp strle2 strle1 strleun eqbrtri ) AGRZBHRZ
      CIRZSUIUJTZUKUAZUBDFRUCUIUJUKUDDEFFULUMABDEGHJKLMNUECFIPQUFOUGUH $.
  $}

  ${
    $d a b w $.  $d a b E $.  $d b F $.  $d a b W $.  $d a b ps $.
    sbcie2s.a $e |- A = ( E ` W ) $.
    sbcie2s.b $e |- B = ( F ` W ) $.
    sbcie2s.1 $e |- ( ( a = A /\ b = B ) -> ( ph <-> ps ) ) $.
    $( A special version of class substitution commonly used for structures.
       (Contributed by Thierry Arnoux, 14-Mar-2019.)  (Revised by SN,
       2-Mar-2025.) $)
    sbcie2s $p |- ( w = W
      -> ( [. ( E ` w ) / a ]. [. ( F ` w ) / b ]. ph <-> ps ) ) $=
      ( cv wceq cfv fvex fveq2 eqtr4di eqeq2d wb biimpd wa a1i syl2and sbc2iedv
      wi ) CNZHOZABIJUHFPZUHGPZUHFQUHGQUIINZUJOZULDOZJNZUKOZUOEOZABUAZUIUMUNUIU
      JDULUIUJHFPDUHHFRKSTUBUIUPUQUIUKEUOUIUKHGPEUHHGRLSTUBUNUQUCURUGUIMUDUEUF
      $.
  $}

  ${
    $d a b c w $.  $d a b c E $.  $d b c F $.  $d c G $.  $d a b c W $.
    $d a b c ph $.
    sbcie3s.a $e |- A = ( E ` W ) $.
    sbcie3s.b $e |- B = ( F ` W ) $.
    sbcie3s.c $e |- C = ( G ` W ) $.
    sbcie3s.1 $e |- ( ( a = A /\ b = B /\ c = C ) -> ( ph <-> ps ) ) $.
    $( A special version of class substitution commonly used for structures.
       (Contributed by Thierry Arnoux, 15-Mar-2019.) $)
    sbcie3s $p |- ( w = W -> ( [. ( E ` w ) / a ]. [. ( F ` w ) / b ].
      [. ( G ` w ) / c ]. ps <-> ph ) ) $=
      ( cv wceq cfv wsbc cvv fvexd wa wb simpllr fveq2 ad3antrrr eqtr4di simplr
      eqtrd simpr syl3anc bicomd sbcied ) CRZJSZBMUPITZUAZLUPHTZUAAKUPGTZUBUQUP
      GUCUQKRZVASZUDZUSALUTUBVDUPHUCVDLRZUTSZUDZBAMURUBVGUPIUCVGMRZURSZUDZABVJV
      BDSVEESVHFSABUEVJVBJGTZDVJVBVAVKUQVCVFVIUFUQVAVKSVCVFVIUPJGUGUHUKNUIVJVEJ
      HTZEVJVEUTVLVDVFVIUJUQUTVLSVCVFVIUPJHUGUHUKOUIVJVHJITZFVJVHURVMVGVIULUQUR
      VMSVCVFVIUPJIUGUHUKPUIQUMUNUOUOUO $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Substitution of components
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $c sSet $.

  $( Set components of a structure. $)
  csts $a class sSet $.

  ${
    $d e s $.
    $( Set a component of an extensible structure.  This function is useful for
       taking an existing structure and "overriding" one of its components.
       For example, ~ df-ress adjusts the base set to match its second
       argument, which has the effect of making subgroups, subspaces, subrings
       etc. from the original structures.  Or ~ df-mgp , which takes a ring and
       overrides its addition operation with the multiplicative operation, so
       that we can consider the "multiplicative group" using group and monoid
       theorems, which expect the operation to be in the ` +g ` slot instead of
       the ` .r ` slot.  (Contributed by Mario Carneiro, 1-Dec-2014.) $)
    df-sets $a |- sSet = ( s e. _V , e e. _V |->
      ( ( s |` ( _V \ dom { e } ) ) u. { e } ) ) $.
  $}

  ${
    $d e s A $.  $d e s B $.  $d e s S $.
    $( The structure override operator is a proper operator.  (Contributed by
       Stefan O'Rear, 29-Jan-2015.) $)
    reldmsets $p |- Rel dom sSet $=
      ( vs ve cvv cv csn cdm cdif cres cun csts df-sets reldmmpo ) ABCCADCBDEZF
      GHMIJBAKL $.

    $( Value of the structure replacement function.  (Contributed by Mario
       Carneiro, 30-Apr-2015.) $)
    setsvalg $p |- ( ( S e. V /\ A e. W ) -> ( S sSet A ) =
      ( ( S |` ( _V \ dom { A } ) ) u. { A } ) ) $=
      ( vs ve wcel cvv csts co csn cdm cdif cres cun wceq elex wa resexg cv
      adantr snex unexg sylancl simpl simpr sneqd dmeqd difeq2d uneq12d df-sets
      reseq12d ovmpoga mpd3an3 syl2an ) BCGBHGZAHGZBAIJBHAKZLZMZNZUROZPZADGBCQA
      DQUPUQVBHGZVCUPUQRVAHGZURHGVDUPVEUQBUTHSUAAUBVAURHHUCUDEFBAHHETZHFTZKZLZM
      ZNZVHOVBIHVFBPZVGAPZRZVKVAVHURVNVFBVJUTVLVMUEVNVIUSHVNVHURVNVGAVLVMUFUGZU
      HUIULVOUJFEUKUMUNUO $.

    $( Value of the structure replacement function.  (Contributed by Mario
       Carneiro, 1-Dec-2014.)  (Revised by Mario Carneiro, 30-Apr-2015.) $)
    setsval $p |- ( ( S e. V /\ B e. W ) -> ( S sSet <. A , B >. ) =
      ( ( S |` ( _V \ { A } ) ) u. { <. A , B >. } ) ) $=
      ( wcel cop csts co cvv csn cdm cdif cres wceq opex setsvalg mpan2 dmsnopg
      cun difeq2d reseq2d uneq1d sylan9eq ) CDFZBEFZCABGZHIZCJUGKZLZMZNZUITZCJA
      KZMZNZUITUEUGJFUHUMOABPUGCDJQRUFULUPUIUFUKUOCUFUJUNJABESUAUBUCUD $.
  $}

  $( The value of the structure replacement function for its first argument is
     its second argument.  (Contributed by SO, 12-Jul-2018.) $)
  fvsetsid $p |- ( ( F e. V /\ X e. W /\ Y e. U ) ->
      ( ( F sSet <. X , Y >. ) ` X ) = Y ) $=
    ( wcel w3a cop csts co cfv cvv csn cdif cres cun wceq setsval cdm fveq1d wn
    3adant2 simp2 simp3 cin dmres inss1 eqsstri sseli mto fsnunfv syl3anc eqtrd
    neldifsn a1i ) BCGZEDGZFAGZHZEBEFIZJKZLEBMENOZPZVANQZLZFUTEVBVEUQUSVBVERURE
    FBCASUCUAUTURUSEVDTZGZUBZVFFRUQURUSUDUQURUSUEVIUTVHEVCGEMUOVGVCEVGVCBTZUFVC
    BVCUGVCVJUHUIUJUKUPVDDAEFULUMUN $.

  $( The structure replacement function is a function.  (Contributed by SO,
     12-Jul-2018.) $)
  fsets $p |- ( ( ( F e. V /\ F : A --> B ) /\ X e. A /\ Y e. B ) ->
      ( F sSet <. X , Y >. ) : A --> B ) $=
    ( wcel wf wa w3a cop csts co cvv csn cdif cres cun feq1d mpbird difss mpan2
    wss fssres wfn wceq ffn fnresdm syl reseq1d cin resres invdif reseq2i eqtri
    eqtr3di adantl fsnunf2 syl3an1 wb simp1l simp3 setsval syl2anc ) CDGZABCHZI
    ZEAGZFBGZJZABCEFKZLMZHZABCNEOZPZQZVKORZHZVGAVNPZBVPHZVHVIVRVFVTVEVFVTVSBCVS
    QZHZVFVSAUCWBAVNUAABVSCUDUBVFVSBVPWAVFCAQZVOQZVPWAVFWCCVOVFCAUEWCCUFABCUGAC
    UHUIUJWDCAVOUKZQWACAVOULWEVSCAVNUMUNUOUPSTUQABVPEFURUSVJVEVIVMVRUTVEVFVHVIV
    AVGVHVIVBVEVIIABVLVQEFCDBVCSVDT $.

  $( The domain of a structure with replacement is the domain of the original
     structure extended by the index of the replacement.  (Contributed by AV,
     7-Jun-2021.) $)
  setsdm $p |- ( ( G e. V /\ E e. W )
                 -> dom ( G sSet <. I , E >. ) = ( dom G u. { I } ) ) $=
    ( wcel wa cop csts co cdm cvv csn cdif cres cun wceq a1i cin eqtrid dmsnopg
    setsvalg sylan2 dmeqd dmres adantl difeq2d ineq1d incom invdif eqtri eqtrdi
    opex dmun uneq12d undif1 3eqtrd ) BDFZAEFZGZBCAHZIJZKBLVAMZKZNZOZVCPZKZBKZC
    MZNZVJPZVIVJPZUTVBVGUSURVALFZVBVGQVNUSCAUMRVABDLUBUCUDUTVHVFKZVDPVLVFVCUNUT
    VOVKVDVJUTVOVEVISZVKBVEUEUTVPLVJNZVISZVKUTVEVQVIUTVDVJLUSVDVJQURCAEUAUFZUGU
    HVRVIVQSVKVQVIUIVIVJUJUKULTVSUOTVLVMQUTVIVJUPRUQ $.

  $( A structure with replacement is a function if the original structure is a
     function.  (Contributed by AV, 7-Jun-2021.) $)
  setsfun $p |- ( ( ( G e. V /\ Fun G ) /\ ( I e. U /\ E e. W ) )
                  -> Fun ( G sSet <. I , E >. ) ) $=
    ( wcel wfun wa cop csts cvv cdm cin c0 wceq adantl adantr ineq1i a1i co csn
    cdif cres cun funres funsng dmres in32 disjdifr 3eqtri eqtri funun syl21anc
    0in wb opex setsvalg sylan2 funeqd mpbird ) CEGZCHZIZDAGBFGIZIZCDBJZKUAZHZC
    LVGUBZMZUCZUDZVJUEZHZVFVMHZVJHZVMMZVKNZOPZVOVDVPVEVCVPVBVLCUFQRVEVQVDDBAFUG
    QVTVFVSVLCMZNZVKNZOVRWBVKCVLUHSWCVLVKNZWANOWANOVLWAVKUIWDOWAVKLUJSWAUOUKULT
    VMVJUMUNVDVIVOUPVEVDVHVNVCVBVGLGZVHVNPWEVCDBUQTVGCELURUSUTRVA $.

  $( A structure with replacement without the empty set is a function if the
     original structure without the empty set is a function.  This variant of
     ~ setsfun is useful for proofs based on ~ isstruct2 which requires
     ` Fun ( F \ { (/) } ) ` for ` F ` to be an extensible structure.
     (Contributed by AV, 7-Jun-2021.) $)
  setsfun0 $p |- ( ( ( G e. V /\ Fun ( G \ { (/) } ) )
                     /\ ( I e. U /\ E e. W ) )
                  -> Fun ( ( G sSet <. I , E >. ) \ { (/) } ) ) $=
    ( wcel c0 csn cdif wfun wa cvv cdm cres cun cin wceq adantl a1i cop csts co
    funres adantr funsng dmres ineq1i in32 disjdifr 3eqtri eqtri funun syl21anc
    0in difundir resdifcom wne elex anim12i opnz sylibr disjsn2 disjdif2 eqtrid
    3syl uneq12d funeqd mpbird wb opex setsvalg sylan2 difeq1d ) CEGZCHIZJZKZLZ
    DAGZBFGZLZLZCDBUAZUBUCZVPJZKZCMWDIZNZJZOZWHPZVPJZKZWCWNVQWJOZWHPZKZWCWOKZWH
    KZWONZWIQZHRZWQVSWRWBVRWRVOWJVQUDSUEWBWSVSDBAFUFSXBWCXAWJVQNZQZWIQZHWTXDWIV
    QWJUGUHXEWJWIQZXCQHXCQHWJXCWIUIXFHXCWIMUJUHXCUOUKULTWOWHUMUNWCWMWPWCWMWKVPJ
    ZWHVPJZPWPWKWHVPUPWCXGWOXHWHXGWORWCCWJVPUQTWCWDHURZWHVPQHRXHWHRWBXIVSWBDMGZ
    BMGZLXIVTXJWAXKDAUSBFUSUTDBVAVBSWDHVCWHVPVDVFVGVEVHVIVSWGWNVJWBVSWFWMVSWEWL
    VPVRVOWDMGZWEWLRXLVRDBVKTWDCEMVLVMVNVHUEVI $.

  ${
    setsn0fun.s $e |- ( ph -> S Struct X ) $.
    setsn0fun.i $e |- ( ph -> I e. U ) $.
    setsn0fun.e $e |- ( ph -> E e. W ) $.
    $( The value of the structure replacement function (without the empty set)
       is a function if the structure (without the empty set) is a function.
       (Contributed by AV, 7-Jun-2021.)  (Revised by AV, 16-Nov-2021.) $)
    setsn0fun $p |- ( ph -> Fun ( ( S sSet <. I , E >. ) \ { (/) } ) ) $=
      ( cstr wbr cop csts cdif wfun wi wa wcel cvv structn0fun structex sylanl1
      co c0 csn setsfun0 expcom syl2anc com12 mpdan mpcom ) BGKLZABEDMNUDUEUFZO
      PZHUMBUNOPZAUOQBGUAAUMUPRZUOAECSZDFSZUQUOQIJUQURUSRZUOUMBTSUPUTUOBGUBCDBE
      TFUGUCUHUIUJUKUL $.
  $}

  $( An extensible structure with a replaced slot is an extensible structure.
     (Contributed by AV, 14-Nov-2021.) $)
  setsstruct2 $p |- ( ( ( G Struct X /\ E e. V /\ I e. NN )
                       /\ Y = <. if ( I <_ ( 1st ` X ) , I , ( 1st ` X ) ) ,
                                 if ( I <_ ( 2nd ` X ) , ( 2nd ` X ) , I ) >. )
                      -> ( G sSet <. I , E >. ) Struct Y ) $=
    ( cstr wbr wcel cn w3a cfv cle wa cfz wss wi 3adant2 adantl sylbi c1st c2nd
    cif cop wceq csts co cxp cin c0 csn cdif wfun isstruct2 elin elxp6 wb eleq1
    cdm adantr simp3 simp1l ifcld nnred simp1r cr nnre anim12i ancomd min1 max1
    syl letrd df-br sylib opelxpd elind sylbid impcom 3ad2ant1 imp cvv structex
    3exp structn0fun jca simp2 setsfun0 syl12anc cun setsdm syl2anc fveq2 df-ov
    eqtr4di sseq2d df-3an cz 3anim123i ssfzunsnext sseqtrdi sylan2 ex biimtrrid
    nnz expd com12 eqsstrd syl3anbrc breq2 mpbird ) BEGHZADIZCJIZKZFCEUALZMHZCX
    PUCZCEUBLZMHZXSCUCZUDZUEZNBCAUDUFUGZFGHZYDYBGHZXOYFYCXOYBMJJUHZUIZIZYDUJUKZ
    ULUMZYDUSZYBOLZPYFXLXNYIXMXLXNYIXLEYHIZBYJULUMZBUSZEOLZPZKZXNYIQZBEUNZYNYOY
    TYRYNEMIZEYGIZNZYTEMYGUOZUUCUUBYTUUCEXPXSUDZUEZXPJIZXSJIZNZNZUUBYTQEJJUPZUU
    KUUBUUFMIZYTUUGUUBUUMUQUUJEUUFMURUTUUJUUMYTQUUGUUJUUMXNYIUUJUUMXNKZMYGYBUUN
    XRYAMHYBMIUUNXRCYAUUNXRUUNXQCXPJUUJUUMXNVAZUUHUUIUUMXNVBVCZVDUUNCUUOVDUUNYA
    UUNXTXSCJUUHUUIUUMXNVEUUOVCZVDUUNCVFIZXPVFIZNXRCMHUUNUUSUURUUJXNUUSUURNUUMU
    UJUUSXNUURUUHUUSUUIXPVGUTCVGZVHRVICXPVJVLUUNUURXSVFIZNCYAMHUUNUVAUURUUJXNUV
    AUURNUUMUUJUVAXNUURUUIUVAUUHXSVGSUUTVHRVICXSVKVLVMXRYAMVNVOUUNXRYAJJUUPUUQV
    PVQWDSVRTVSTVTTWARXOBWBIZYONZXNXMYKXLXMUVCXNXLUVBYOBEWCZBEWEWFVTXLXMXNVAXLX
    MXNWGZJABCWBDWHWIXOYLYPCUKWJZYMXOUVBXMYLUVFUEXLXMUVBXNUVDVTUVEABCWBDWKWLXLX
    NUVFYMPZXMXLXNUVGXLYSXNUVGQZUUAYNYRUVHYOYNYRUVHYNUUDYRUVHQZUUEUUCUVIUUBUUCU
    UKUVIUULUUKYRYPXPXSOUGZPZUVHUUGYRUVKUQUUJUUGYQUVJYPUUGYQUUFOLUVJEUUFOWMXPXS
    OWNWOWPUTUUJUVKUVHQUUGUVKUUJUVHUVKUUJXNUVGUUJXNNUUHUUIXNKZUVKUVGUUHUUIXNWQU
    VKUVLUVGUVLUVKXPWRIZXSWRIZCWRIZKZUVGUUHUVMUUIUVNXNUVOXPXEXSXECXEWSUVKUVPNUV
    FXRYAOUGYMYPCXPXSWTXRYAOWNXAXBXCXDXFXGSVRTSTWARTWARXHYDYBUNXIUTYCYEYFUQXOFY
    BYDGXJSXK $.

  ${
    $d E y $.  $d G y $.  $d I y $.  $d X y $.
    $( An extensible structure with a replaced slot is an extensible structure.
       (Contributed by AV, 14-Nov-2021.) $)
    setsexstruct2 $p |- ( ( G Struct X /\ E e. V /\ I e. NN )
                          -> E. y ( G sSet <. I , E >. ) Struct y ) $=
      ( cstr wbr wcel cn w3a cop csts co cv c1st cfv cle cif cvv c2nd opex wceq
      a1i eqidd setsstruct2 mpdan breq2 spcedv ) CFGHBEIDJIKZCDBLMNZAOZGHUKDFPQ
      ZRHDUMSZDFUAQZRHUODSZLZGHZATUQUQTIUJUNUPUBUDUJUQUQUCURUJUQUEBCDEFUQUFUGUL
      UQUKGUHUI $.
  $}

  $( An extensible structure with a replaced slot is an extensible structure.
     (Contributed by AV, 9-Jun-2021.)  (Revised by AV, 14-Nov-2021.) $)
  setsstruct $p |- ( ( E e. V /\ I e. ( ZZ>= ` M ) /\ G Struct <. M , N >. )
          -> ( G sSet <. I , E >. ) Struct <. M , if ( I <_ N , N , I ) >. ) $=
    ( wcel cfv cop wbr w3a cn cle cif wceq wa wi c1 cz 3ad2ant1 cstr c1st co c0
    cuz c2nd csts csn cdif wfun cdm cfz isstruct simp2 simp3l 1z nnge1 eluzuzle
    wss sylancr elnnuz imbitrrdi adantld a1d 3imp op1stg breq2d eqidd ifbieq12d
    3jca 3adant3 adantr cxr eluz2 zre rexrd 3ad2ant2 simp3 sylbi adantl xrmineq
    impcom syl eqtr2d 3adant2 op2ndg eqcomd opeq12d pm2.43i expdcom setsstruct2
    jca 3exp ) AFGZCDUEHGZBDEIZUAJZKWQWNCLGZKZDCEMJZECNZIZCWPUBHZMJZCXCNZCWPUFH
    ZMJZXFCNZIOZPZBCAIUGUCXBUAJWNWOWQXJWQWNWOXJWQWNWOPZXJQZWQDLGZELGZDEMJZKZBUD
    UHUIUJZBUKDEULUCUSZKWQXLQZBDEUMXPXQXSXRXPWQXKXJXPWQXKKZWSXIXTWQWNWRXPWQXKUN
    XPWQWNWOUOXPWQXKWRXPXKWRQZWQXMXNYAXOXMWOWRWNXMWOCRUEHGZWRXMRSGRDMJWOYBQUPDU
    QDRCURUTCVAVBVCTVDVEVJXTDXEXAXHXPXKDXEOWQXPXKPZXECDMJZCDNZDXPXEYEOZXKXMXNYF
    XOXMXNPZXDYDCXCCDYGXCDCMDELLVFZVGYGCVHZYHVIVKVLYCCVMGZDVMGZDCMJZKZYEDOXKXPY
    MWOXPYMQZWNWODSGZCSGZYLKZYNDCVNYQYMXPYQYJYKYLYPYOYJYLYPCCVOVPVQYOYPYKYLYODD
    VOVPTYOYPYLVRVJVDVSVTWBCDWAWCWDWEXPWQXAXHOZXKXMXNYRXOYGWTXGECXFCYGEXFCMYGXF
    EDELLWFWGZVGYSYIVIVKTWHWLWMTVSWIWJVEABCFWPXBWKWC $.

  ${
    wunsets.1 $e |- ( ph -> U e. WUni ) $.
    wunsets.2 $e |- ( ph -> S e. U ) $.
    wunsets.3 $e |- ( ph -> A e. U ) $.
    $( Closure of structure replacement in a weak universe.  (Contributed by
       Mario Carneiro, 12-Jan-2017.) $)
    wunsets $p |- ( ph -> ( S sSet A ) e. U ) $=
      ( csts co cvv csn cdm cdif cres cun wcel wceq setsvalg syl2anc wunres
      wunsn wunun eqeltrd ) ACBHIZCJBKZLMZNZUEOZDACDPBDPUDUHQFGBCDDRSAUGUEDEACU
      FDEFTABDEGUAUBUC $.
  $}

  $( The structure replacement function does not affect the value of ` S ` away
     from ` A ` .  (Contributed by Mario Carneiro, 1-Dec-2014.)  (Revised by
     Mario Carneiro, 30-Apr-2015.) $)
  setsres $p |- ( S e. V ->
    ( ( S sSet <. A , B >. ) |` ( _V \ { A } ) ) = ( S |` ( _V \ { A } ) ) ) $=
    ( wcel cop csts co cvv csn cdif cres cdm cun wceq c0 wss ax-mp mpbir eqtri
    opex setsvalg mpan2 reseq1d resundir dmsnopss sscon resabs1 cin dmres disj2
    wrel wb relres reldm0 uneq12i un0 eqtrdi ) CDEZCABFZGHZIAJZKZLCIUTJZMZKZLZV
    DNZVCLZCVCLZUSVAVHVCUSUTIEVAVHOABUAUTCDIUBUCUDVIVGVCLZVDVCLZNZVJVGVDVCUEVMV
    JPNVJVKVJVLPVCVFQZVKVJOVEVBQVNABUFVEVBIUGRZCVCVFUHRVLPOZVLMZPOZVQVCVEUIZPVD
    VCUJVSPOVNVOVCVEUKSTVLULVPVRUMVDVCUNVLUORSUPVJUQTTUR $.

  $( Replacing the same components twice yields the same as the second setting
     only.  (Contributed by Mario Carneiro, 2-Dec-2014.) $)
  setsabs $p |- ( ( S e. V /\ C e. W ) ->
    ( ( S sSet <. A , B >. ) sSet <. A , C >. ) = ( S sSet <. A , C >. ) ) $=
    ( wcel wa cop csts co cvv csn cdif cres cun wceq setsres adantr setsval
    uneq1d ovexd sylan 3eqtr4d ) DEGZCFGZHZDABIZJKZLAMNZOZACIZMZPZDUJOZUMPUIULJ
    KZDULJKUGUKUOUMUEUKUOQUFABDERSUAUEUILGUFUPUNQUEDUHJUBACUILFTUCACDEFTUD $.

  ${
    setscom.1 $e |- A e. _V $.
    setscom.2 $e |- B e. _V $.
    $( Different components can be set in any order.  (Contributed by Mario
       Carneiro, 5-Dec-2014.)  (Revised by Mario Carneiro, 30-Apr-2015.) $)
    setscom $p |- ( ( ( S e. V /\ A =/= B ) /\ ( C e. W /\ D e. X ) ) ->
       ( ( S sSet <. A , C >. ) sSet <. B , D >. ) =
       ( ( S sSet <. B , D >. ) sSet <. A , C >. ) ) $=
      ( wcel wa csts co cvv csn cres cun wceq wss cdif rescom uneq1i un23 eqtri
      wne cop setsval ad2ant2r reseq1d resundir wrel cdm cxp elex ad2antrl opex
      opelxpi sylancr relsn sylibr dmsnopss cin c0 disjsn2 ad2antlr disj2 sylib
      sstrid relssres syl2anc uneq2d eqtrid eqtrd uneq1d ad2ant2rl ad2antll ssv
      wb ssconb mp2an 3eqtr4a ovex simprr simprl 3eqtr4d ) EFKZABUFZLZCGKZDHKZL
      ZLZEACUGZMNZOBPZUAZQZBDUGZPZRZEWSMNZOAPZUAZQZWNPZRZWOWSMNZXBWNMNZWMEXDQZW
      QQZXFRZWTRZEWQQZXDQZWTRZXFRZXAXGXMXOXFRZWTRXQXLXRWTXKXOXFEXDWQUBUCUCXOXFW
      TUDUEWMWRXLWTWMWRXJXFRZWQQZXLWMWOXSWQWGWJWOXSSWHWKACEFGUHUIUJWMXTXKXFWQQZ
      RXLXJXFWQUKWMYAXFXKWMXFULZXFUMZWQTYAXFSWMWNOOUNZKZYBWMAOKCOKZYEIWJYFWIWKC
      GUOUPACOOURUSWNACUQUTVAWMYCXCWQACVBWMXCWPVCVDSZXCWQTZWHYGWGWLABVEVFXCWPVG
      VHZVIXFWQVJVKVLVMVNVOWMXEXPXFWMXEXNWTRZXDQZXPWGWKXEYKSWHWJWGWKLXBYJXDBDEF
      HUHUJVPWMYKXOWTXDQZRXPXNWTXDUKWMYLWTXOWMWTULZWTUMZXDTYLWTSWMWSYDKZYMWMBOK
      DOKZYOJWKYPWIWJDHUOVQBDOOURUSWSBDUQUTVAWMYNWPXDBDVBWMYHWPXDTZYIXCOTWPOTYH
      YQVSXCVRWPVRXCWPOVTWAVHVIWTXDVJVKVLVMVNVOWBWMWOOKWKXHXASEWNMWCWIWJWKWDBDW
      OOHUHUSWMXBOKWJXIXGSEWSMWCWIWJWKWEACXBOGUHUSWF $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Slots
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $c Slot $.

  $( Extend class notation with the slot function. $)
  cslot $a class Slot A $.

  ${
    $d x A $.
    $( Define the slot extractor for extensible structures.  The class
       ` Slot A ` is a function whose argument can be any set, although it is
       meaningful only if that set is a member of an extensible structure (such
       as a partially ordered set ( ~ df-poset ) or a group ( ~ df-grp )).

       Note that ` Slot A ` is implemented as "evaluation at ` A ` ".  That is,
       ` ( Slot A `` S ) ` is defined to be ` ( S `` A ) ` , where ` A ` will
       typically be an index (which is implemented as a small natural number)
       of a component of an extensible structure ` S ` .  Each extensible
       structure is a function defined on specific (natural number) "slots",
       and the function ` Slot A ` extracts the structure's component as a
       function value at a particular slot (with index ` A ` ).

       The special "structure" ` ndx ` , defined as the identity function
       restricted to ` NN ` , can be used to extract the number ` A ` from a
       slot, since ` ( Slot A `` ndx ) = A ` (see ~ ndxarg ).  This is
       typically used to refer to the number of a slot when defining structures
       without having to expose the detail of what that number is (for
       instance, we use the expression ` ( Base `` ndx ) ` in theorems and
       proofs instead of its hard-coded, numeric value 1), and discourage using
       the specific definition of slot extractors like ` Base = Slot 1 ` (see
       ~ df-base ).  Actually, these definitions are used in two basic theorems
       named *id (theorems of the form ` C = Slot ( C `` ndx ) ` ) and *ndx
       (theorems of the form ` ( C `` ndx ) = N ` ) only (see, for example,
       ~ baseid and ~ basendx ), except additionally in the discouraged theorem
       ~ baseval to demonstrate the representations of the value of the base
       set extractor.  The *id theorems are implementation independent
       equivalents of the definitions by the means of ~ ndxid , but the *ndx
       theorems still depend on the hard-coded values of the indices.
       Therefore, the usage of these *ndx theorems is also discouraged (for
       more details see the section header comment ~ mmtheorems.html#cnx ).

       Example:  The group operation is the second component, i.e., the
       component in the second slot, of a group-like structure
       ` G = { <. ( Base `` ndx ) , B >. , <. ( +g `` ndx ) , .+ >. } ` .  The
       slot extractor ` +g = Slot 2 ` (see ~ df-plusg ) applied on the
       structure ` G ` provides the group operation ` .+ = ( +g `` G ) ` .
       Expanding the definitions, we get
       ` .+ = ( Slot 2 `` G ) = ( G `` 2 ) = ( G `` ( +g `` ndx ) ) ` (for the
       last equation, see ~ plusgndx ).

       The class ` Slot ` cannot be defined as
       ` ( x e. _V |-> ( f e. _V |-> ( f `` x ) ) ) ` because each ` Slot A `
       is a function on the proper class ` _V ` so is itself a proper class,
       and the values of functions are sets ( ~ fvex ).  It is necessary to
       allow proper classes as values of ` Slot A ` since for instance the
       class of all (base sets of) groups is proper.  (Contributed by Mario
       Carneiro, 22-Sep-2015.) $)
    df-slot $a |- Slot A = ( x e. _V |-> ( x ` A ) ) $.
  $}

  ${
    $d A f $.  $d B f $.
    $( Equality theorem for the ` Slot ` construction.  The converse holds if
       ` A ` (or ` B ` ) is a set.  (Contributed by BJ, 27-Dec-2021.) $)
    sloteq $p |- ( A = B -> Slot A = Slot B ) $=
      ( vf wceq cvv cv cfv cmpt cslot fveq2 mpteq2dv df-slot 3eqtr4g ) ABDZCEAC
      FZGZHCEBOGZHAIBINCEPQABOJKCALCBLM $.
  $}

  ${
    $d x N $.  $d x S $.
    strfvnd.c $e |- E = Slot N $.
    $( A slot is a function on sets, treated as structures.  (Contributed by
       Mario Carneiro, 22-Sep-2015.) $)
    slotfn $p |- E Fn _V $=
      ( vx cvv cv cfv fvex cslot cmpt df-slot eqtri fnmpti ) DEBDFZGZABNHABIDEO
      JCDBKLM $.

    strfvnd.f $e |- ( ph -> S e. V ) $.
    $( Deduction version of ~ strfvn .  (Contributed by Mario Carneiro,
       15-Nov-2014.) $)
    strfvnd $p |- ( ph -> ( E ` S ) = ( S ` N ) ) $=
      ( vx wcel cvv cfv wceq elex cv fveq1 cslot cmpt df-slot eqtri fvex fvmpt
      3syl ) ABEIBJIBCKDBKZLGBEMHBDHNZKZUCJCDUDBOCDPHJUEQFHDRSDBTUAUB $.
  $}

  ${
    strfvn.f $e |- S e. _V $.
    strfvn.c $e |- E = Slot N $.
    $( Value of a structure component extractor ` E ` .  Normally, ` E ` is a
       defined constant symbol such as ` Base ` ( ~ df-base ) and ` N ` is the
       index of the component. ` S ` is a structure, i.e. a specific member of
       a class of structures such as ` Poset ` ( ~ df-poset ) where
       ` S e. Poset ` .

       Hint:  Do not substitute ` N ` by a specific (positive) integer to be
       independent of a hard-coded index value.  Often, ` ( E `` ndx ) ` can be
       used instead of ` N ` .  Alternatively, use ~ strfv instead of
       ~ strfvn .  (Contributed by NM, 9-Sep-2011.)  (Revised by Mario
       Carneiro, 6-Oct-2013.)  (New usage is discouraged.) $)
    strfvn $p |- ( E ` S ) = ( S ` N ) $=
      ( cfv wceq wtru cvv wcel a1i strfvnd mptru ) ABFCAFGHABCIEAIJHDKLM $.
  $}

  ${
    strfvss.e $e |- E = Slot N $.
    $( A structure component extractor produces a value which is contained in a
       set dependent on ` S ` , but not ` E ` .  This is sometimes useful for
       showing sethood.  (Contributed by Mario Carneiro, 15-Aug-2015.) $)
    strfvss $p |- ( E ` S ) C_ U. ran S $=
      ( cvv wcel cfv crn cuni wss id strfvnd fvssunirn eqsstrdi wn c0 fvprc 0ss
      pm2.61i ) AEFZABGZAHIZJTUACAGUBTABCEDTKLACMNTOUAPUBABQUBRNS $.

    ${
      wunstr.u $e |- ( ph -> U e. WUni ) $.
      wunstr.s $e |- ( ph -> S e. U ) $.
      $( Closure of a structure index in a weak universe.  (Contributed by
         Mario Carneiro, 12-Jan-2017.) $)
      wunstr $p |- ( ph -> ( E ` S ) e. U ) $=
        ( crn cuni cfv wunrn wununi wss strfvss a1i wunss ) ABIZJZBDKZCGARCGABC
        GHLMTSNABDEFOPQ $.
    $}
  $}

  ${
    str0.a $e |- F = Slot I $.
    $( All components of the empty set are empty sets.  (Contributed by Stefan
       O'Rear, 27-Nov-2014.)  (Revised by Mario Carneiro, 7-Dec-2014.) $)
    str0 $p |- (/) = ( F ` (/) ) $=
      ( c0 cfv 0ex strfvn 0fv eqtr2i ) DAEBDEDDABFCGBHI $.
  $}

  ${
    strfvi.e $e |- E = Slot N $.
    strfvi.x $e |- X = ( E ` S ) $.
    $( Structure slot extractors cannot distinguish between proper classes and
       ` (/) ` , so they can be protected using the identity function.
       (Contributed by Stefan O'Rear, 21-Mar-2015.) $)
    strfvi $p |- X = ( E ` ( _I ` S ) ) $=
      ( cfv cid cvv wcel wceq fvi eqcomd fveq2d wn str0 fvprc 3eqtr4a pm2.61i
      c0 eqtri ) DABGZAHGZBGZFAIJZUBUDKUEAUCBUEUCAAILMNUEOZTTBGUBUDBCEPABQUFUCT
      BAHQNRSUA $.
  $}

  ${
    fveqprc.e $e |- ( E ` (/) ) = (/) $.
    fveqprc.y $e |- Y = ( F ` X ) $.
    $( Lemma for showing the equality of values for functions like slot
       extractors ` E ` at a proper class.  Extracted from several former
       proofs of lemmas like ~ zlmlem .  (Contributed by AV, 31-Oct-2024.) $)
    fveqprc $p |- ( -. X e. _V -> ( E ` X ) = ( E ` Y ) ) $=
      ( cvv wcel wn c0 cfv eqcomi fvprc eqtrid fveq2d 3eqtr4a ) CGHIZJJAKZCAKDA
      KRJELCAMQDJAQDCBKJFCBMNOP $.
  $}

  ${
    oveqprc.e $e |- ( E ` (/) ) = (/) $.
    oveqprc.z $e |- Z = ( X O Y ) $.
    oveqprc.r $e |- Rel dom O $.
    $( Lemma for showing the equality of values for functions like slot
       extractors ` E ` at a proper class.  Extracted from several former
       proofs of lemmas like ~ resvlem .  (Contributed by AV, 31-Oct-2024.) $)
    oveqprc $p |- ( -. X e. _V -> ( E ` X ) = ( E ` Z ) ) $=
      ( cvv wcel wn c0 cfv eqcomi fvprc co ovprc1 eqtrid fveq2d 3eqtr4a ) CIJKZ
      LLAMZCAMEAMUBLFNCAOUAELAUAECDBPLGCDBHQRST $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Structure component indices
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  The structure component index extractor ` ndx `, defined in this subsection,
  is used to get the numeric argument from a defined structure component
  extractor such as ~ df-base (see ~ ndxarg ).  For each defined structure
  component extractor, there should be a corresponding specific theorem
  providing its index, like ~ basendx . The usage of these theorems, however,
  is discouraged since the particular value for the index is an implementation
  detail.  It is generally sufficient to work with ` ( Base `` ndx ) ` instead
  of the hard-coded index value, and use theorems such as ~ baseid and
  ~ basendxnplusgndx .

  The main circumstance in which it is necessary to look at indices directly is
  when showing that a set of indices are disjoint (for example in proofs such
  as ~ cznabel , based on ~ setsnid ) or even ordered (in proofs such as
  ~ lmodstr ).  The requirement that the indices are distinct is necessary for
  sets of ordered pairs to be extensible structures, whereas the ordering
  allows for proofs avoiding the usage of quadradically many inequalities
  (compare ~ cnfldfun with ~ cnfldfunALT ).

  As for the inequalities, it is recommended to provide them explicitly as
  theorems like ~ basendxnplusgndx , whenever they are required.  Since these
  theorems use discouraged slot theorems, they should be placed near the
  definition of a slot (within the same subsection), so that the range of
  usages of discouraged theorems is tightly limited.  Although there could be
  quadradically many of them in the total number of indices, much less are
  actually available (and not much more are expected).

  As for the ordering, there are some theorems like ~ basendxltplusgndx
  providing the less-than relationship between two indices.  These theorems are
  also proved by discouraged theorems, so they should be placed near the
  definition of a slot (within the same subsection), too.  However, since such
  theorems are rarely used (in structure building theorems *str like
  ~ rngstr ), it is not recommended to provide explicit theorems for all of
  them, but to use the (discouraged) *ndx theorems as in ~ lmodstr .
  Therefore, *str theorems generally depend on the hard-coded values of the
  indices.

$)

  $c ndx $.

  $( Extend class notation with the structure component index extractor. $)
  cnx $a class ndx $.

  $( Define the structure component index extractor.  See Theorem ~ ndxarg to
     understand its purpose.  The restriction to ` NN ` ensures that ` ndx ` is
     a set.  The restriction to some set is necessary since ` _I ` is a proper
     class.  In principle, we could have chosen ` CC ` or (if we revise all
     structure component definitions such as ~ df-base ) another set such as
     the set of finite ordinals ` _om ` ( ~ df-om ).  (Contributed by NM,
     4-Sep-2011.) $)
  df-ndx $a |- ndx = ( _I |` NN ) $.

  ${
    wunndx.1 $e |- ( ph -> U e. WUni ) $.
    wunndx.2 $e |- ( ph -> _om e. U ) $.
    $( Closure of the index extractor in an infinite weak universe.
       (Contributed by Mario Carneiro, 12-Jan-2017.) $)
    wunndx $p |- ( ph -> ndx e. U ) $=
      ( cnx cid cn cres df-ndx cc wuncn wss nnsscn wunss wf1o wf f1oi f1of mp1i
      a1i wunf eqeltrid ) AEFGHZBIAGGBUCCAJGBCABCDKGJLAMTNZUDGGUCOGGUCPAGQGGUCR
      SUAUB $.
  $}

  ${
    ndxarg.e $e |- E = Slot N $.
    ndxarg.n $e |- N e. NN $.
    $( Get the numeric argument from a defined structure component extractor
       such as ~ df-base .  (Contributed by Mario Carneiro, 6-Oct-2013.) $)
    ndxarg $p |- ( E ` ndx ) = N $=
      ( cnx cfv cid cn cres cvv df-ndx wcel resiexg ax-mp eqeltri strfvn fveq1i
      nnex wceq fvresi 3eqtri ) EAFBEFBGHIZFZBEABEUBJKHJLUBJLRHJMNOCPBEUBKQBHLU
      CBSDHBTNUA $.

    $( A structure component extractor is defined by its own index.  This
       theorem, together with ~ strfv below, is useful for avoiding direct
       reference to the hard-coded numeric index in component extractor
       definitions, such as the ` 1 ` in ~ df-base and the ` ; 1 0 ` in
       ~ df-ple , making it easier to change should the need arise.

       For example, we can refer to a specific poset with base set ` B ` and
       order relation ` L ` using ` { <. ( Base `` ndx ) , B >. , `
       ` <. ( le `` ndx ) , L >. } ` rather than ` { <. 1 , B >. , `
       ` <. ; 1 0 , L >. } ` .  The latter, while shorter to state, requires
       revision if we later change ` ; 1 0 ` to some other number, and it may
       also be harder to remember.  (Contributed by NM, 19-Oct-2012.)  (Revised
       by Mario Carneiro, 6-Oct-2013.)  (Proof shortened by BJ,
       27-Dec-2021.) $)
    ndxid $p |- E = Slot ( E ` ndx ) $=
      ( cnx cfv wceq cslot ndxarg eqcomi sloteq eqtrid ax-mp ) BEAFZGZANHZGNBAB
      CDIJOABHPCBNKLM $.
  $}

  ${
    strndxid.s $e |- ( ph -> S e. V ) $.
    strndxid.e $e |- E = Slot N $.
    strndxid.n $e |- N e. NN $.
    $( The value of a structure component extractor is the value of the
       corresponding slot of the structure.  (Contributed by AV, 13-Mar-2020.)
       (New usage is discouraged.)  Use ~ strfvnd directly with ` N ` set to
       ` ( E `` ndx ) ` if possible. $)
    strndxid $p |- ( ph -> ( S ` ( E ` ndx ) ) = ( E ` S ) ) $=
      ( cfv cnx ndxid strfvnd eqcomd ) ABCIJCIZBIABCNECDGHKFLM $.
  $}

  ${
    setsidvald.e $e |- E = Slot N $.
    setsidvald.s $e |- ( ph -> S e. V ) $.
    setsidvald.f $e |- ( ph -> Fun S ) $.
    setsidvald.d $e |- ( ph -> N e. dom S ) $.
    $( Value of the structure replacement function, deduction version.

       Hint:  Do not substitute ` N ` by a specific (positive) integer to be
       independent of a hard-coded index value.  Often, ` ( E `` ndx ) ` can be
       used instead of ` N ` .  (Contributed by AV, 14-Mar-2020.)  (Revised by
       AV, 17-Oct-2024.) $)
    setsidvald $p |- ( ph -> S = ( S sSet <. N , ( E ` S ) >. ) ) $=
      ( cfv cop csts co cvv csn cdif cres cun wcel wceq setsval sylancl strfvnd
      fvex opeq2d sneqd uneq2d wfun cdm funresdfunsn syl2anc 3eqtrrd ) ABDBCJZK
      ZLMZBNDOPQZUNOZRZUPDDBJZKZOZRZBABESUMNSUOURTGBCUDDUMBENUAUBAUQVAUPAUNUTAU
      MUSDABCDEFGUCUEUFUGABUHDBUISVBBTHIBDUJUKUL $.
  $}

  ${
    strfvd.e $e |- E = Slot ( E ` ndx ) $.
    strfvd.s $e |- ( ph -> S e. V ) $.
    strfvd.f $e |- ( ph -> Fun S ) $.
    strfvd.n $e |- ( ph -> <. ( E ` ndx ) , C >. e. S ) $.
    $( Deduction version of ~ strfv .  (Contributed by Mario Carneiro,
       15-Nov-2014.) $)
    strfvd $p |- ( ph -> C = ( E ` S ) ) $=
      ( cfv cnx strfvnd wfun cop wcel wceq funopfv sylc eqtr2d ) ACDJKDJZCJZBAC
      DTEFGLACMTBNCOUABPHITBCQRS $.
  $}

  ${
    strfv2d.e $e |- E = Slot ( E ` ndx ) $.
    strfv2d.s $e |- ( ph -> S e. V ) $.
    strfv2d.f $e |- ( ph -> Fun `' `' S ) $.
    strfv2d.n $e |- ( ph -> <. ( E ` ndx ) , C >. e. S ) $.
    strfv2d.c $e |- ( ph -> C e. W ) $.
    $( Deduction version of ~ strfv2 .  (Contributed by Mario Carneiro,
       30-Apr-2015.) $)
    strfv2d $p |- ( ph -> C = ( E ` S ) ) $=
      ( cfv cnx strfvnd ccnv cvv cres cnvcnv2 wcel wceq fveq1i fvex fvres ax-mp
      eqtri wfun cop cxp cin elexd opelxpi sylancr elind eleqtrrdi funopfv sylc
      cnvcnv eqtr3id eqtr2d ) ACDLMDLZCLZBACDUTEGHNAVAUTCOOZLZBVCUTCPQZLZVAUTVB
      VDCRUAUTPSZVEVATMDUBZUTPCUCUDUEAVBUFUTBUGZVBSVCBTIAVHCPPUHZUIVBACVIVHJAVF
      BPSVHVISVGABFKUJUTBPPUKULUMCUQUNUTBVBUOUPURUS $.
  $}

  ${
    strfv2.s $e |- S e. _V $.
    strfv2.f $e |- Fun `' `' S $.
    strfv2.e $e |- E = Slot ( E ` ndx ) $.
    strfv2.n $e |- <. ( E ` ndx ) , C >. e. S $.
    $( A variation on ~ strfv to avoid asserting that ` S ` itself is a
       function, which involves sethood of all the ordered pair components of
       ` S ` .  (Contributed by Mario Carneiro, 30-Apr-2015.) $)
    strfv2 $p |- ( C e. V -> C = ( E ` S ) ) $=
      ( wcel cvv a1i ccnv wfun cnx cfv cop id strfv2d ) ADIZABCJDGBJISEKBLLMSFK
      NCOAPBISHKSQR $.
  $}

  ${
    strfv.s $e |- S Struct X $.
    strfv.e $e |- E = Slot ( E ` ndx ) $.
    strfv.n $e |- { <. ( E ` ndx ) , C >. } C_ S $.
    $( Extract a structure component ` C ` (such as the base set) from a
       structure ` S ` (such as a member of ` Poset ` , ~ df-poset ) with a
       component extractor ` E ` (such as the base set extractor ~ df-base ).
       By virtue of ~ ndxid , this can be done without having to refer to the
       hard-coded numeric index of ` E ` .  (Contributed by Mario Carneiro,
       6-Oct-2013.)  (Revised by Mario Carneiro, 29-Aug-2015.) $)
    strfv $p |- ( C e. V -> C = ( E ` S ) ) $=
      ( cstr wbr cvv wcel structex ax-mp structfun cnx cfv cop csn wss strfv2
      opex snss mpbir ) ABCDBEIJBKLFBEMNBEFOGPCQZARZBLUFSBTHUFBUEAUBUCUDUA $.
  $}

  ${
    strfv3.u $e |- ( ph -> U = S ) $.
    strfv3.s $e |- S Struct X $.
    strfv3.e $e |- E = Slot ( E ` ndx ) $.
    strfv3.n $e |- { <. ( E ` ndx ) , C >. } C_ S $.
    strfv3.c $e |- ( ph -> C e. V ) $.
    strfv3.a $e |- A = ( E ` U ) $.
    $( Variant on ~ strfv for large structures.  (Contributed by Mario
       Carneiro, 10-Jan-2017.) $)
    strfv3 $p |- ( ph -> A = C ) $=
      ( cfv wcel wceq strfv syl fveq2d eqtr4d eqtr4id ) ABEFOZCNACDFOZUCACGPCUD
      QMCDFGHJKLRSAEDFITUAUB $.
  $}

  ${
    strssd.e $e |- E = Slot ( E ` ndx ) $.
    strssd.t $e |- ( ph -> T e. V ) $.
    strssd.f $e |- ( ph -> Fun T ) $.
    strssd.s $e |- ( ph -> S C_ T ) $.
    strssd.n $e |- ( ph -> <. ( E ` ndx ) , C >. e. S ) $.
    $( Deduction version of ~ strss .  (Contributed by Mario Carneiro,
       15-Nov-2014.)  (Revised by Mario Carneiro, 30-Apr-2015.) $)
    strssd $p |- ( ph -> ( E ` T ) = ( E ` S ) ) $=
      ( cfv cnx cop sseldd strfvd cvv ssexd wss wfun funss sylc eqtr3d ) ABDELC
      ELABDEFGHIACDMELBNJKOPABCEQGACDFHJRACDSDTCTJICDUAUBKPUC $.
  $}

  ${
    strss.t $e |- T e. _V $.
    strss.f $e |- Fun T $.
    strss.s $e |- S C_ T $.
    strss.e $e |- E = Slot ( E ` ndx ) $.
    strss.n $e |- <. ( E ` ndx ) , C >. e. S $.
    $( Propagate component extraction to a structure ` T ` from a subset
       structure ` S ` .  (Contributed by Mario Carneiro, 11-Oct-2013.)
       (Revised by Mario Carneiro, 15-Jan-2014.) $)
    strss $p |- ( E ` T ) = ( E ` S ) $=
      ( cfv wceq wtru cvv wcel a1i wfun wss cnx cop strssd mptru ) CDJBDJKLABCD
      MHCMNLEOCPLFOBCQLGORDJASBNLIOTUA $.
  $}

  ${
    setsid.e $e |- E = Slot ( E ` ndx ) $.
    $( Value of the structure replacement function at a replaced index.
       (Contributed by Mario Carneiro, 1-Dec-2014.)  (Revised by Mario
       Carneiro, 30-Apr-2015.) $)
    setsid $p |- ( ( W e. A /\ C e. V ) ->
      C = ( E ` ( W sSet <. ( E ` ndx ) , C >. ) ) ) $=
      ( wcel wa cnx cfv cop cvv csn cres cun sylancl wceq c0 eqtri a1i co unexg
      csts cdif setsval fveq2d resexg adantr snex strfvnd fvex snid fvres ax-mp
      cin resres disjdifr reseq2i res0 wrel cdm wss elex adantl opelxpi sylancr
      cxp opex relsn sylibr dmsnopss relssres uneq12d resundir un0 uncom eqtr3i
      3eqtr4g fveq1d eqtr3id fvsng sylancom eqtrd 3eqtrrd ) EAGZBDGZHZEICJZBKZU
      CUAZCJELWHMZUDZNZWIMZOZCJWHWOJZBWGWJWOCWHBEADUEUFWGWOCWHLFWGWMLGZWNLGWOLG
      WEWQWFEWLAUGUHWIUIWMWNLLUBPUJWGWPWHWNJZBWGWPWHWOWKNZJZWRWHWKGWTWPQWHICUKZ
      ULWHWKWOUMUNWGWHWSWNWGWMWKNZWNWKNZORWNOZWSWNWGXBRXCWNXBRQWGXBEWLWKUOZNZRE
      WLWKUPXFERNRXEREWKLUQUREUSSSTWGWNUTZWNVAWKVBXCWNQWGWILLVGGZXGWGWHLGZBLGZX
      HXAWFXJWEBDVCVDWHBLLVEVFWIWHBVHVIVJWHBVKWNWKVLPVMWMWNWKVNWNROWNXDWNVOWNRV
      PVQVRVSVTWEWFXIWRBQXIWGXATWHBLDWAWBWCWD $.

    setsnid.n $e |- ( E ` ndx ) =/= D $.
    $( Value of the structure replacement function at an untouched index.
       (Contributed by Mario Carneiro, 1-Dec-2014.)  (Revised by Mario
       Carneiro, 30-Apr-2015.)  (Proof shortened by AV, 7-Nov-2024.) $)
    setsnid $p |- ( E ` W ) = ( E ` ( W sSet <. D , C >. ) ) $=
      ( cvv wcel cfv cop csts co wceq cnx id strfvnd cres fvres ax-mp c0 strfvn
      ovex csn cdif setsres fveq1d wne fvex eldifsn mpbir2an eqtrid eqtr4d str0
      3eqtr3g eqcomi eqid reldmsets oveqprc pm2.61i ) DGHZDCIZDBAJZKLZCIZMUTVAN
      CIZDIZVDUTDCVEGEUTOPUTVDVEVCIZVFVCCVEDVBKUBEUAUTVEVCGBUCUDZQZIZVEDVHQZIZV
      GVFUTVEVIVKBADGUEUFVEVHHZVJVGMVMVEGHVEBUGNCUHFVEGBUIUJZVEVHVCRSVMVLVFMVNV
      EVHDRSUNUKULCKDVBVCTTCICVEEUMUOVCUPUQURUS $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Base sets
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $c Base $.

  $( Extend class notation with the class of all base set extractors. $)
  cbs $a class Base $.

  $( Define the base set (also called underlying set, ground set, carrier set,
     or carrier) extractor for extensible structures.  (Contributed by NM,
     4-Sep-2011.)  (Revised by Mario Carneiro, 14-Aug-2015.)  Use its
     index-independent form ~ baseid instead.  (New usage is discouraged.) $)
  df-base $a |- Base = Slot 1 $.

  ${
    baseval.k $e |- K e. _V $.
    $( Value of the base set extractor.  (Normally it is preferred to work with
       ` ( Base `` ndx ) ` rather than the hard-coded ` 1 ` in order to make
       structure theorems portable.  This is an example of how to obtain it
       when needed.)  (New usage is discouraged.)  (Contributed by NM,
       4-Sep-2011.) $)
    baseval $p |- ( Base ` K ) = ( K ` 1 ) $=
      ( cbs c1 df-base strfvn ) ACDBEF $.
  $}

  $( Utility theorem: index-independent form of ~ df-base .  (Contributed by
     NM, 20-Oct-2012.) $)
  baseid $p |- Base = Slot ( Base ` ndx ) $=
    ( cbs c1 df-base 1nn ndxid ) ABCDE $.

  $( The base set extractor is a function on ` _V ` .  (Contributed by Stefan
     O'Rear, 8-Jul-2015.) $)
  basfn $p |- Base Fn _V $=
    ( cbs cnx cfv baseid slotfn ) ABACDE $.

  $( The base set of the empty structure.  (Contributed by David A. Wheeler,
     7-Jul-2016.) $)
  base0 $p |- (/) = ( Base ` (/) ) $=
    ( cbs cnx cfv baseid str0 ) ABACDE $.

  ${
    elbasfv.s $e |- S = ( F ` Z ) $.
    elbasfv.b $e |- B = ( Base ` S ) $.
    $( Utility theorem: reverse closure for any structure defined as a
       function.  (Contributed by Stefan O'Rear, 24-Aug-2015.) $)
    elbasfv $p |- ( X e. B -> Z e. _V ) $=
      ( wcel c0 wceq cvv n0i wn cbs cfv fvprc eqtrid fveq2d base0 3eqtr4g nsyl2
      ) DAHAIJEKHZADLUBMZBNOINOAIUCBINUCBECOIFECPQRGSTUA $.
  $}

  ${
    elbasov.o $e |- Rel dom O $.
    elbasov.s $e |- S = ( X O Y ) $.
    elbasov.b $e |- B = ( Base ` S ) $.
    $( Utility theorem: reverse closure for any structure defined as a
       two-argument function.  (Contributed by Mario Carneiro, 3-Oct-2015.) $)
    elbasov $p |- ( A e. B -> ( X e. _V /\ Y e. _V ) ) $=
      ( wcel c0 wceq cvv wa n0i wn cbs cfv co ovprc eqtrid fveq2d base0 3eqtr4g
      nsyl2 ) ABJBKLEMJFMJNZBAOUFPZCQRKQRBKUGCKQUGCEFDSKHEFDGTUAUBIUCUDUE $.
  $}

  ${
    strov2rcl.s $e |- S = ( I F R ) $.
    strov2rcl.b $e |- B = ( Base ` S ) $.
    strov2rcl.f $e |- Rel dom F $.
    $( Partial reverse closure for any structure defined as a two-argument
       function.  (Contributed by Stefan O'Rear, 27-Mar-2015.)  (Proof
       shortened by AV, 2-Dec-2019.) $)
    strov2rcl $p |- ( X e. B -> I e. _V ) $=
      ( wcel cvv elbasov simpld ) FAJEKJBKJFACDEBIGHLM $.
  $}

  $( Index value of the base set extractor.  (Contributed by Mario Carneiro,
     2-Aug-2013.)  Use of this theorem is discouraged since the particular
     value ` 1 ` for the index is an implementation detail, see section header
     comment ~ mmtheorems.html#cnx for more information.
     (New usage is discouraged.) $)
  basendx $p |- ( Base ` ndx ) = 1 $=
    ( cbs c1 df-base 1nn ndxarg ) ABCDE $.

  $( The index value of the base set extractor is a positive integer.  This
     property should be ensured for every concrete coding because otherwise it
     could not be used in an extensible structure (slots must be positive
     integers).  (Contributed by AV, 23-Sep-2020.)  (Proof shortened by AV,
     13-Oct-2024.) $)
  basendxnn $p |- ( Base ` ndx ) e. NN $=
    ( cnx cbs cfv c1 cn basendx 1nn eqeltri ) ABCDEFGH $.

  ${
    basndxelwund.u $e |- ( ph -> U e. WUni ) $.
    basndxelwund.o $e |- ( ph -> _om e. U ) $.
    $( The index of the base set is an element in a weak universe containing
       the natural numbers.  Formerly part of proof for ~ 1strwun .
       (Contributed by AV, 27-Mar-2020.)  (Revised by AV, 17-Oct-2024.) $)
    basndxelwund $p |- ( ph -> ( Base ` ndx ) e. U ) $=
      ( cnx cbs cfv baseid wunndx wunstr ) AEBFEFGHCABCDIJ $.
  $}

  ${
    basprssdmsets.s $e |- ( ph -> S Struct X ) $.
    basprssdmsets.i $e |- ( ph -> I e. U ) $.
    basprssdmsets.w $e |- ( ph -> E e. W ) $.
    basprssdmsets.b $e |- ( ph -> ( Base ` ndx ) e. dom S ) $.
    $( The pair of the base index and another index is a subset of the domain
       of the structure obtained by replacing/adding a slot at the other index
       in a structure having a base slot.  (Contributed by AV, 7-Jun-2021.)
       (Revised by AV, 16-Nov-2021.) $)
    basprssdmsets $p |- ( ph -> { ( Base ` ndx ) , I }
                                C_ dom ( S sSet <. I , E >. ) ) $=
      ( cnx cbs cdm wcel wo elun sylibr syl cvv cfv cpr csn cun csts orcd snidg
      cop co olcd prssd wceq cstr wbr structex setsdm syl2anc sseqtrrd ) ALMUAZ
      EUBBNZEUCZUDZBEDUHUEUINZAUSEVBAUSUTOZUSVAOZPUSVBOAVDVEKUFUSUTVAQRAEUTOZEV
      AOZPEVBOAVGVFAECOVGIECUGSUJEUTVAQRUKABTOZDFOVCVBULABGUMUNVHHBGUOSJDBETFUP
      UQUR $.
  $}

  ${
    opelstrbas.s $e |- ( ph -> S Struct X ) $.
    opelstrbas.v $e |- ( ph -> V e. Y ) $.
    opelstrbas.b $e |- ( ph -> <. ( Base ` ndx ) , V >. e. S ) $.
    $( The base set of a structure with a base set.  (Contributed by AV,
       10-Nov-2021.) $)
    opelstrbas $p |- ( ph -> V = ( Base ` S ) ) $=
      ( cbs cvv baseid cstr wbr wcel structex syl ccnv wfun structfung strfv2d
      ) ACBIJEKABDLMZBJNFBDOPAUABQQRFBDSPHGT $.
  $}

  ${
    1str.g $e |- G = { <. ( Base ` ndx ) , B >. } $.
    $( A constructed one-slot structure.  (Contributed by AV, 15-Nov-2024.) $)
    1strstr $p |- G Struct <. ( Base ` ndx ) , ( Base ` ndx ) >. $=
      ( cnx cbs cfv cop csn cstr basendxnn eqid strle1 eqbrtri ) BDEFZAGHNNGICN
      NAJNKLM $.

    $( The base set of a constructed one-slot structure.  (Contributed by AV,
       27-Mar-2020.)  (Proof shortened by AV, 15-Nov-2024.) $)
    1strbas $p |- ( B e. V -> B = ( Base ` G ) ) $=
      ( cbs cnx cfv cop 1strstr baseid csn eqimss2i strfv ) ABECFEGZNHABDIJBNAH
      KDLM $.

    1strwun.u $e |- ( ph -> U e. WUni ) $.
    ${
      1strwunbndx.b $e |- ( ph -> ( Base ` ndx ) e. U ) $.
      $( A constructed one-slot structure in a weak universe containing the
         index of the base set extractor.  (Contributed by AV, 27-Mar-2020.) $)
      1strwunbndx $p |- ( ( ph /\ B e. U ) -> G e. U ) $=
        ( wcel wa cnx cbs cfv cop csn cwun adantr simpr wunop wunsn eqeltrid )
        ABCHZIZDJKLZBMZNCEUBUDCACOHUAFPZUBUCBCUEAUCCHUAGPAUAQRST $.
    $}

    1strwun.o $e |- ( ph -> _om e. U ) $.
    $( A constructed one-slot structure in a weak universe.  (Contributed by
       AV, 27-Mar-2020.)  (Proof shortened by AV, 17-Oct-2024.) $)
    1strwun $p |- ( ( ph /\ B e. U ) -> G e. U ) $=
      ( basndxelwund 1strwunbndx ) ABCDEFACFGHI $.
  $}

  ${
    2str.g $e |- G = { <. ( Base ` ndx ) , B >. , <. N , .+ >. } $.
    2str.b $e |- ( Base ` ndx ) < N $.
    2str.n $e |- N e. NN $.
    $( A constructed two-slot structure not depending on the hard-coded index
       value of the base set.  (Contributed by AV, 22-Sep-2020.)  (Proof
       shortened by AV, 17-Oct-2024.) $)
    2strstr $p |- G Struct <. ( Base ` ndx ) , N >. $=
      ( cnx cbs cfv cop cpr cstr basendxnn eqid strle2 eqbrtri ) CHIJZAKDBKLRDK
      MERDRDABNROFGDOPQ $.

    $( The base set of a constructed two-slot structure not depending on the
       hard-coded index value of the base set.  (Contributed by AV,
       22-Sep-2020.) $)
    2strbas $p |- ( B e. V -> B = ( Base ` G ) ) $=
      ( cbs cnx cfv cop 2strstr baseid csn cpr snsspr1 sseqtrri strfv ) ACIEJIK
      ZDLABCDFGHMNTALZOUADBLZPCUAUBQFRS $.

    2str.e $e |- E = Slot N $.
    $( The other slot of a constructed two-slot structure not depending on the
       hard-coded index value of the base set.  (Contributed by AV,
       22-Sep-2020.) $)
    2strop $p |- ( .+ e. V -> .+ = ( E ` G ) ) $=
      ( cnx cbs cfv cop 2strstr ndxid csn cpr snsspr2 ndxarg opeq1i sneqi strfv
      3sstr4i ) BDCFKLMZENABDEGHIOCEJIPEBNZQUEANZUFRKCMZBNZQDUGUFSUIUFUHEBCEJIT
      UAUBGUDUC $.  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Base set restrictions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $c |`s $.

  $( Extend class notation with the extensible structure builder restriction
     operator. $)
  cress $a class |`s $.

  ${
    $d w x $.
    $( Define a multifunction restriction operator for extensible structures,
       which can be used to turn statements about rings into statements about
       subrings, modules into submodules, etc.  This definition knows nothing
       about individual structures and merely truncates the ` Base ` set while
       leaving operators alone; individual kinds of structures will need to
       handle this behavior, by ignoring operators' values outside the range
       (like ` Ring ` ), defining a function using the base set and applying
       that (like ` TopGrp ` ), or explicitly truncating the slot before use
       (like ` MetSp ` ).

       (Credit for this operator goes to Mario Carneiro.)

       See ~ ressbas for the altered base set, and ~ resseqnbas ( ~ subrg0 ,
       ~ ressplusg , ~ subrg1 , ~ ressmulr ) for the (un)altered other
       operations.  (Contributed by Stefan O'Rear, 29-Nov-2014.) $)
    df-ress $a |- |`s = ( w e. _V , x e. _V |-> if ( ( Base ` w ) C_ x , w ,
        ( w sSet <. ( Base ` ndx ) , ( x i^i ( Base ` w ) ) >. ) ) ) $.
  $}

  ${
    $d a w $.
    $( The structure restriction is a proper operator, so it can be used with
       ~ ovprc1 .  (Contributed by Stefan O'Rear, 29-Nov-2014.) $)
    reldmress $p |- Rel dom |`s $=
      ( vw va cvv cv cbs cfv wss cnx cin cop csts co cif cress df-ress reldmmpo
      ) ABCCADZEFZBDZGQQHEFSRIJKLMNBAOP $.
  $}

  ${
    $d a w A $.  $d a w B $.  $d a w W $.
    ressbas.r $e |- R = ( W |`s A ) $.
    ressbas.b $e |- B = ( Base ` W ) $.
    $( Value of structure restriction.  (Contributed by Stefan O'Rear,
       29-Nov-2014.) $)
    ressval $p |- ( ( W e. X /\ A e. Y ) -> R = if ( B C_ A , W ,
            ( W sSet <. ( Base ` ndx ) , ( A i^i B ) >. ) ) ) $=
      ( vw va wcel wa cress co wss cbs cfv csts cvv wceq cnx cin cop elex simpl
      cif ovex ifcl sylancl fveq2d eqtr4di simpr sseq12d ineq12d opeq2d oveq12d
      cv ifbieq12d df-ress ovmpoga mpd3an3 syl2an eqtrid ) DEKZAFKZLCDAMNZBAOZD
      DUAPQZABUBZUCZRNZUFZGVDDSKZASKZVFVLTZVEDEUDAFUDVMVNVLSKZVOVMVNLVMVKSKVPVM
      VNUEDVJRUGVGDVKSUHUIIJDASSIUQZPQZJUQZOZVQVQVHVSVRUBZUCZRNZUFVLMSVQDTZVSAT
      ZLZVTVGVQWCDVKWFVRBVSAWFVRDPQBWFVQDPWDWEUEZUJHUKZWDWEULZUMWGWFVQDWBVJRWGW
      FWAVIVHWFVSAVRBWIWHUNUOUPURJIUSUTVAVBVC $.

    $( General behavior of trivial restriction.  (Contributed by Stefan O'Rear,
       29-Nov-2014.) $)
    ressid2 $p |- ( ( B C_ A /\ W e. X /\ A e. Y ) -> R = W ) $=
      ( wss wcel wceq wa cnx cbs cfv cin cop csts co cif iftrue sylan9eqr 3impb
      ressval ) BAIZDEJZAFJZCDKUFUGLUECUEDDMNOABPQRSZTDABCDEFGHUDUEDUHUAUBUC $.

    $( Value of nontrivial structure restriction.  (Contributed by Stefan
       O'Rear, 29-Nov-2014.) $)
    ressval2 $p |- ( ( -. B C_ A /\ W e. X /\ A e. Y ) -> R = ( W sSet
        <. ( Base ` ndx ) , ( A i^i B ) >. ) ) $=
      ( wss wn wcel cnx cbs cfv cin cop csts co wceq wa ressval sylan9eqr 3impb
      cif iffalse ) BAIZJZDEKZAFKZCDLMNABOPQRZSUHUITUGCUFDUJUDUJABCDEFGHUAUFDUJ
      UEUBUC $.

    $( Base set of a structure restriction.  (Contributed by Stefan O'Rear,
       26-Nov-2014.)  (Proof shortened by AV, 7-Nov-2024.) $)
    ressbas $p |- ( A e. V -> ( A i^i B ) = ( Base ` R ) ) $=
      ( cvv wcel cin cbs cfv wceq wss w3a fveq2d 3eqtr4a 3expib wn c0 wa wi cnx
      simp1 sseqin2 sylib ressid2 cop csts co simp2 fvexi baseid setsid sylancl
      inex2 eqtr4d pm2.61i in0 fvprc eqtrid ineq2d cress base0 eqcomi reldmress
      ressval2 oveqprc eqtrd adantr pm2.61ian ) EHIZADIZABJZCKLZMZBANZVLVMUAVPU
      BVQVLVMVPVQVLVMOZBEKLZVNVOGVRVQVNBMVQVLVMUDBAUEUFVRCEKABCEHDFGUGPQRVQSZVL
      VMVPVTVLVMOZVNEUCKLVNUHUIUJZKLZVOWAVLVNHIVNWCMVTVLVMUKBABEKGULUPHVNKHEUMU
      NUOWACWBKABCEHDFGVGPUQRURVLSZVPVMWDVNVSVOWDATJTVNVSAUSWDBTAWDBVSTGEKUTZVA
      VBWEQKVCEACTTKLVDVEFVFVHVIVJVK $.

    $( The base set of a restriction to ` A ` is a subset of ` A ` and the base
       set ` B ` of the original structure.  (Contributed by SN,
       10-Jan-2025.) $)
    ressbasssg $p |- ( Base ` R ) C_ ( A i^i B ) $=
      ( cvv wcel cbs cfv cin wss ressbas ssid eqsstrrdi wn c0 cress reldmress
      co ovprc2 eqtrid fveq2d base0 0ss eqsstrri eqsstrdi pm2.61i ) AGHZCIJZABK
      ZLUIUJUKUKABCGDEFMUKNOUIPZUJQIJZUKULCQIULCDARTQEDARSUAUBUCUMQUKUDUKUEUFUG
      UH $.

    $( Base set of a structure restriction.  (Contributed by Mario Carneiro,
       2-Dec-2014.) $)
    ressbas2 $p |- ( A C_ B -> A = ( Base ` R ) ) $=
      ( wss cin cbs cfv wceq dfss2 biimpi cvv wcel fvexi ssex ressbas eqtr3d
      syl ) ABGZABHZACIJZUAUBAKABLMUAANOUBUCKABBDIFPQABCNDEFRTS $.

    $( The base set of a restriction is a subset of the base set of the
       original structure.  (Contributed by Stefan O'Rear, 27-Nov-2014.)
       (Revised by Mario Carneiro, 30-Apr-2015.)  (Proof shortened by SN,
       25-Feb-2025.) $)
    ressbasss $p |- ( Base ` R ) C_ B $=
      ( cbs cfv cin ressbasssg inss2 sstri ) CGHABIBABCDEFJABKL $.

    $( Obsolete version of ~ ressbas as of 25-Feb-2025.  (Contributed by Stefan
       O'Rear, 27-Nov-2014.)  (Revised by Mario Carneiro, 30-Apr-2015.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    ressbasssOLD $p |- ( Base ` R ) C_ B $=
      ( cvv wcel cbs cfv wss cin ressbas inss2 eqsstrrdi wn c0 cress reldmress
      co ovprc2 eqtrid fveq2d base0 0ss eqsstrri eqsstrdi pm2.61i ) AGHZCIJZBKU
      IUJABLBABCGDEFMABNOUIPZUJQIJZBUKCQIUKCDARTQEDARSUAUBUCULQBUDBUEUFUGUH $.
  $}

  ${
    ressbasss2.r $e |- R = ( W |`s A ) $.
    $( The base set of a restriction to ` A ` is a subset of ` A ` .
       (Contributed by SN, 10-Jan-2025.) $)
    ressbasss2 $p |- ( Base ` R ) C_ A $=
      ( cbs cfv cin eqid ressbasssg inss1 sstri ) BEFACEFZGAALBCDLHIALJK $.
  $}

  ${
    resseqnbas.r $e |- R = ( W |`s A ) $.
    resseqnbas.e $e |- C = ( E ` W ) $.
    resseqnbas.f $e |- E = Slot ( E ` ndx ) $.
    resseqnbas.n $e |- ( E ` ndx ) =/= ( Base ` ndx ) $.
    $( The components of an extensible structure except the base set remain
       unchanged on a structure restriction.  (Contributed by Mario Carneiro,
       26-Nov-2014.)  (Revised by Mario Carneiro, 2-Dec-2014.)  (Revised by AV,
       19-Oct-2024.) $)
    resseqnbas $p |- ( A e. V -> C = ( E ` R ) ) $=
      ( wcel cfv cvv cbs w3a fveq2d 3expib wn cnx c0 wceq wss wa wi ressid2 cin
      eqid csts co ressval2 setsnid eqtr4di pm2.61i cress str0 eqcomi reldmress
      cop oveqprc eqcomd adantr pm2.61ian eqtr4id ) AEKZBFDLZCDLZHFMKZVDVFVEUAZ
      FNLZAUBZVGVDUCVHUDVJVGVDVHVJVGVDOCFDAVICFMEGVIUGZUEPQVJRZVGVDVHVLVGVDOZVF
      FSNLZAVIUFZURUHUIZDLVEVMCVPDAVICFMEGVKUJPVOVNDFIJUKULQUMVGRZVHVDVQVEVFDUN
      FACTTDLDSDLIUOUPGUQUSUTVAVBVC $.
  $}

  $( All restrictions of the empty set are trivial.  (Contributed by Stefan
     O'Rear, 29-Nov-2014.)  (Revised by Mario Carneiro, 30-Apr-2015.) $)
  ress0 $p |- ( (/) |`s A ) = (/) $=
    ( cvv wcel c0 cress co wceq wss 0ss 0ex eqid base0 ressid2 reldmress ovprc2
    mp3an12 pm2.61i ) ABCZDAEFZDGZDAHDBCRTAIJADSDBBSKLMPDAENOQ $.

  ${
    ressid.1 $e |- B = ( Base ` W ) $.
    $( Behavior of trivial restriction.  (Contributed by Stefan O'Rear,
       29-Nov-2014.) $)
    ressid $p |- ( W e. X -> ( W |`s B ) = W ) $=
      ( wss wcel cvv cress co wceq ssid cbs fvexi eqid ressid2 mp3an13 ) AAEBCF
      AGFBAHIZBJAKABLDMAAQBCGQNDOP $.

    $( Restriction only cares about the part of the second set which intersects
       the base of the first.  (Contributed by Stefan O'Rear, 29-Nov-2014.) $)
    ressinbas $p |- ( A e. X -> ( W |`s A ) = ( W |`s ( A i^i B ) ) ) $=
      ( wcel cvv cress co cin wceq elex wss w3a eqid ressid2 syl3an eqtr4d csts
      wn wa ssid incom dfss2 biimpi eqtrid sseqtrrid inex1g 3expb cnx cbs inass
      cfv cop inidm ineq2i eqtr2i opeq2i oveq2i ressval2 inss1 sstr mpan2 con3i
      3eqtr4a pm2.61ian c0 reldmress ovprc1 adantr syl ) ADFAGFZCAHIZCABJZHIZKZ
      ADLCGFZVLVPBAMZVQVLUAVPVRVQVLVPVRVQVLNVMCVOABVMCGGVMOZEPVRBVNMZVQVQVLVNGF
      ZVOCKVRBBVNBUBVRVNBAJZBABUCVRWBBKBAUDUEUFUGCGLZABGUHZVNBVOCGGVOOZEPQRUIVR
      TZVQVLVPWFVQVLNCUJUKUMZVNUNZSICWGVNBJZUNZSIZVMVOWHWJCSVNWIWGWIABBJZJVNABB
      ULWLBABUOUPUQURUSABVMCGGVSEUTWFVTTVQVQVLWAVOWKKVTVRVTVNAMVRABVABVNAVBVCVD
      WCWDVNBVOCGGWEEUTQVEUIVFVQTZVPVLWMVMVGVOCAHVHVICVNHVHVIRVJVFVK $.
  $}

  ${
    ressval3d.r $e |- R = ( S |`s A ) $.
    ressval3d.b $e |- B = ( Base ` S ) $.
    ressval3d.e $e |- E = ( Base ` ndx ) $.
    ressval3d.s $e |- ( ph -> S e. V ) $.
    ressval3d.f $e |- ( ph -> Fun S ) $.
    ressval3d.d $e |- ( ph -> E e. dom S ) $.
    ressval3d.u $e |- ( ph -> A C_ B ) $.
    $( Value of structure restriction, deduction version.  (Contributed by AV,
       14-Mar-2020.)  (Revised by AV, 3-Jul-2022.)  (Proof shortened by AV,
       17-Oct-2024.) $)
    ressval3d $p |- ( ph -> R = ( S sSet <. E , A >. ) ) $=
      ( csts co wceq cbs cvv a1i wss wn wa wo wi wpss sspss dfpss3 orbi1i bitri
      cop cnx cfv cin wcel simplr adantl simpl fvexi ssexg syl2an syl3anc dfss2
      ressval2 biimpi eqcomd adantr opeq12d oveq2d eqtrd cress oveq2 ressid syl
      ex 3eqtrd baseid cdm eqeltrrid setsidvald eqtrdi jaoi sylbi mpcom ) BCUAZ
      ADEFBUKZOPZQZNWEWECBUAUBZUCZBCQZUDZAWHUEZWEBCUFZWKUDWLBCUGWNWJWKBCUHUIUJW
      JWMWKWJAWHWJAUCZDEULRUMZBCUNZUKZOPZWGWOWIEGUOZBSUOZDWSQWEWIAUPAWTWJKUQWJW
      ECSUOZXAAWEWIURXBACERIUSTBCSUTVABCDEGSHIVDVBWOWRWFEOWOWFWRWOFWPBWQFWPQZWO
      JTWJBWQQZAWEXDWIWEWQBWEWQBQBCVCVEVFVGVGVHVFVIVJVOWKAWHWKAUCZDEEWPERUMZUKZ
      OPZWGXEDEBVKPZECVKPZEDXIQXEHTWKXIXJQABCEVKVLVGXEWTXJEQAWTWKKUQCEGIVMVNVPA
      EXHQWKAERWPGVQKLAWPFEVRJMVSVTUQXEXGWFEOXEWFXGXEFWPBXFXCXEJTXEBCXFWKAURIWA
      VHVFVIVPVOWBWCWD $.
  $}

  $( Restriction composition law.  (Contributed by Stefan O'Rear, 29-Nov-2014.)
     (Proof shortened by Mario Carneiro, 2-Dec-2014.) $)
  ressress $p |- ( ( A e. X /\ B e. Y ) ->
    ( ( W |`s A ) |`s B ) = ( W |`s ( A i^i B ) ) ) $=
    ( cvv wcel wa cress co cin wceq cbs cfv wss wn cop csts eqid syl wi w3a cnx
    simplr simpr1 simpr2 syl3anc inass in12 eqtri ressbas ineq2d eqtr2id opeq2d
    ressval2 oveq12d fvex inex2 setsabs sylancl eqtrd simpll ovexd simpr3 inss1
    sstr mpan2 nsyl inex1g 3eqtr4d exp31 ressid2 mp3an2 3ad2antr3 simpl eqsstrd
    ovex in32 dfss2 sylib oveq2d ressinbas 3syl 3adant3r3 oveq1d sstrid sseqin2
    ex inss2 pm2.61ii 3expib c0 ress0 reldmress ovprc1 3eqtr4a a1d pm2.61i ) CF
    GZADGZBEGZHZCAIJZBIJZCABKZIJZLZUAWSWTXAXGXCMNZBOZCMNZAOZWSWTXAUBZXGUAXIPZXK
    PZXLXGXMXNHZXLHZXCUCMNZBXHKZQZRJZCXQXEXJKZQZRJZXDXFXPXTCXQAXJKZQRJZYBRJZYCX
    PXCYEXSYBRXPXNWSWTXCYELXMXNXLUDZXOWSWTXAUEZXOWSWTXAUFZAXJXCCFDXCSZXJSZUOUGX
    PXRYAXQXPYABYDKZXRYAABXJKZKZYLABXJUHZABXJUIUJXPYDXHBXPWTYDXHLZYIAXJXCDCYJYK
    UKZTULUMUNUPXPWSYAFGYFYCLYHXJXECMUQURXQYDYACFFUSUTVAXPXMXCFGZXAXDXTLXMXNXLV
    BXPCAIVCXOWSWTXAVDBXHXDXCFEXDSZXHSZUOUGXPXJXEOZPWSXEFGZXFYCLXPXKUUAYGUUAXEA
    OXKABVEXJXEAVFVGVHYHXPWTUUBYIABDVIZTXEXJXFCFFXFSYKUOUGVJVKXIXLXGXIXLHZXDXCX
    FXIWSXAXDXCLZWTXIYRXAUUECAIVQBXHXDXCFEYSYTVLVMVNUUDCYDIJZCYAIJZXCXFUUDYDYAC
    IUUDYAYDBKZYDABXJVRUUDYDBOUUHYDLUUDYDXHBUUDWTYPXIWSWTXAUFZYQTXIXLVOVPYDBVSV
    TUMWAUUDWTXCUUFLUUIAXJCDYKWBTUUDWTUUBXFUUGLZUUIUUCXEXJCFYKWBZWCVJVAWHXKXLXG
    XKXLHZXDCBIJZXFUULXCCBIXKWSWTXCCLXAAXJXCCFDYJYKVLWDWEUULCYMIJZUUGUUMXFUULYM
    YACIUULYAYNYMYOUULYMAOYNYMLUULYMXJABXJWIXKXLVOWFYMAWGVTUMWAUULXAUUMUUNLXKWS
    WTXAVDBXJCEYKWBTUULWTUUBUUJXKWSWTXAUFUUCUUKWCVJVAWHWJWKWSPZXGXBUUOWLBIJWLXD
    XFBWMUUOXCWLBICAIWNWOWECXEIWNWOWPWQWR $.

  $( Restriction absorption law.  (Contributed by Mario Carneiro,
     12-Jun-2015.) $)
  ressabs $p |- ( ( A e. X /\ B C_ A ) ->
    ( ( W |`s A ) |`s B ) = ( W |`s B ) ) $=
    ( wcel wss wa cress co cin wceq ssexg ancoms ressress syldan sseqin2 bilani
    cvv oveq2d eqtrd ) ADEZBAFZGZCAHIBHIZCABJZHIZCBHIUAUBBREZUDUFKUBUAUGBADLMAB
    CDRNOUCUEBCHUBUEBKUABAPQST $.

  ${
    wunress.1 $e |- ( ph -> U e. WUni ) $.
    wunress.2 $e |- ( ph -> _om e. U ) $.
    wunress.3 $e |- ( ph -> W e. U ) $.
    $( Closure of structure restriction in a weak universe.  (Contributed by
       Mario Carneiro, 12-Jan-2017.)  (Proof shortened by AV, 28-Oct-2024.) $)
    wunress $p |- ( ph -> ( W |`s A ) e. U ) $=
      ( cvv wcel cress co wa cbs cfv wss cnx cin cop eqid c0 csts ressval sylan
      wceq basndxelwund incom baseid wunstr wunin eqeltrid wunop wunsets adantr
      cif ifcld eqeltrd ex wn wun0 reldmress ovprc2 eleq1d syl5ibrcom pm2.61d )
      ABHIZDBJKZCIZAVEVGAVELVFDMNZBOZDDPMNZBVHQZRZUAKZUNZCADCIVEVFVNUDGBVHVFDCH
      VFSVHSUBUCAVNCIVEAVIDVMCGAVLDCEGAVJVKCEACEFUEAVKVHBQCBVHUFAVHBCEADCMVJUGE
      GUHUIUJUKULUOUMUPUQAVGVEURZTCIACEUSVOVFTCDBJUTVAVBVCVD $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Slot definitions
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c +g $.
  $c .r $.
  $c *r $.
  $c Scalar $.
  $c .s $.
  $c .i $.
  $c TopSet $.
  $c le $.
  $c oc $.
  $c dist $.
  $c UnifSet $.
  $c Hom $.
  $c comp $.

  $( Extend class notation with group (addition) operation. $)
  cplusg $a class +g $.

  $( Extend class notation with ring multiplication. $)
  cmulr $a class .r $.

  $( Extend class notation with involution. $)
  cstv $a class *r $.

  $( Extend class notation with scalar field. $)
  csca $a class Scalar $.

  $( Extend class notation with scalar product. $)
  cvsca $a class .s $.

  $( Extend class notation with Hermitian form (inner product). $)
  cip $a class .i $.

  $( Extend class notation with the topology component of a topological
     space. $)
  cts $a class TopSet $.

  $( Extend class notation with "less than or equal to" for posets. $)
  cple $a class le $.

  $( Extend class notation with the class of orthocomplementation
     extractors. $)
  coc $a class oc $.

  $( Extend class notation with the metric space distance function. $)
  cds $a class dist $.

  $( Extend class notation with the uniform structure. $)
  cunif $a class UnifSet $.

  $( Extend class notation with the hom-set structure. $)
  chom $a class Hom $.

  $( Extend class notation with the composition operation. $)
  cco $a class comp $.

  $( Define group operation.  In the context of less restrictive structures,
     this operation is also called magma, semigroup or monoid operation.
     (Contributed by NM, 4-Sep-2011.)  (Revised by Mario Carneiro,
     14-Aug-2015.)  Use its index-independent form ~ plusgid instead.
     (New usage is discouraged.) $)
  df-plusg $a |- +g = Slot 2 $.

  $( Define ring multiplication.  (Contributed by NM, 4-Sep-2011.)  (Revised by
     Mario Carneiro, 14-Aug-2015.)  Use its index-independent form ~ mulrid
     instead.  (New usage is discouraged.) $)
  df-mulr $a |- .r = Slot 3 $.

  $( Define the involution function of a *-ring.  (Contributed by NM,
     4-Sep-2011.)  (Revised by Mario Carneiro, 14-Aug-2015.)  Use its
     index-independent form ~ starvid instead.  (New usage is discouraged.) $)
  df-starv $a |- *r = Slot 4 $.

  $( Define scalar field component of a vector space ` v ` .  (Contributed by
     NM, 4-Sep-2011.)  (Revised by Mario Carneiro, 14-Aug-2015.)  Use its
     index-independent form ~ scaid instead.  (New usage is discouraged.) $)
  df-sca $a |- Scalar = Slot 5 $.

  $( Define scalar product.  (Contributed by NM, 4-Sep-2011.)  (Revised by
     Mario Carneiro, 14-Aug-2015.)  Use its index-independent form ~ vscaid
     instead.  (New usage is discouraged.) $)
  df-vsca $a |- .s = Slot 6 $.

  $( Define Hermitian form (inner product).  (Contributed by NM, 4-Sep-2011.)
     (Revised by Mario Carneiro, 14-Aug-2015.)  Use its index-independent form
     ~ ipid instead.  (New usage is discouraged.) $)
  df-ip $a |- .i = Slot 8 $.

  $( Define the topology component of a topological space (structure).
     (Contributed by NM, 4-Sep-2011.)  (Revised by Mario Carneiro,
     14-Aug-2015.)  Use its index-independent form ~ tsetid instead.
     (New usage is discouraged.) $)
  df-tset $a |- TopSet = Slot 9 $.

  $( Define "less than or equal to" ordering extractor for posets and related
     structures.  (Contributed by NM, 4-Sep-2011.)  (Revised by Mario Carneiro,
     14-Aug-2015.)  (Revised by AV, 9-Sep-2021.)  Use its index-independent
     form ~ pleid instead.  (New usage is discouraged.) $)
  df-ple $a |- le = Slot ; 1 0 $.

  $( Define the orthocomplementation extractor for posets and related
     structures.  (Contributed by NM, 4-Sep-2011.)  (Revised by Mario Carneiro,
     14-Aug-2015.)  Use its index-independent form ~ ocid instead.
     (New usage is discouraged.) $)
  df-ocomp $a |- oc = Slot ; 1 1 $.

  $( Define the distance function component of a metric space (structure).
     (Contributed by NM, 4-Sep-2011.)  (Revised by Mario Carneiro,
     14-Aug-2015.)  Use its index-independent form ~ dsid instead.
     (New usage is discouraged.) $)
  df-ds $a |- dist = Slot ; 1 2 $.

  $( Define the uniform structure component of a uniform space.  (Contributed
     by Mario Carneiro, 14-Aug-2015.)  Use its index-independent form ~ unifid
     instead.  (New usage is discouraged.) $)
  df-unif $a |- UnifSet = Slot ; 1 3 $.

  $( Define the hom-set component of a category.  (Contributed by Mario
     Carneiro, 2-Jan-2017.)  Use its index-independent form ~ homid instead.
     (New usage is discouraged.) $)
  df-hom $a |- Hom = Slot ; 1 4 $.

  $( Define the composition operation of a category.  (Contributed by Mario
     Carneiro, 2-Jan-2017.)  Use its index-independent form ~ ccoid instead.
     (New usage is discouraged.) $)
  df-cco $a |- comp = Slot ; 1 5 $.

  $( Index value of the ~ df-plusg slot.  (Contributed by Mario Carneiro,
     14-Aug-2015.)  (New usage is discouraged.) $)
  plusgndx $p |- ( +g ` ndx ) = 2 $=
    ( cplusg c2 df-plusg 2nn ndxarg ) ABCDE $.

  $( Utility theorem: index-independent form of ~ df-plusg .  (Contributed by
     NM, 20-Oct-2012.) $)
  plusgid $p |- +g = Slot ( +g ` ndx ) $=
    ( cplusg c2 df-plusg 2nn ndxid ) ABCDE $.

  $( The index of the slot for the group operation in an extensible structure
     is a positive integer.  (Contributed by AV, 17-Oct-2024.) $)
  plusgndxnn $p |- ( +g ` ndx ) e. NN $=
    ( cnx cplusg cfv c2 cn plusgndx 2nn eqeltri ) ABCDEFGH $.

  $( The index of the slot for the base set is less than the index of the slot
     for the group operation in an extensible structure.  (Contributed by AV,
     17-Oct-2024.) $)
  basendxltplusgndx $p |- ( Base ` ndx ) < ( +g ` ndx ) $=
    ( c1 c2 cnx cbs cfv cplusg clt 1lt2 basendx plusgndx 3brtr4i ) ABCDECFEGHIJ
    K $.

  $( The slot for the base set is not the slot for the group operation in an
     extensible structure.  (Contributed by AV, 14-Nov-2021.)  (Proof shortened
     by AV, 17-Oct-2024.) $)
  basendxnplusgndx $p |- ( Base ` ndx ) =/= ( +g ` ndx ) $=
    ( cnx cbs cfv cplusg basendxnn nnrei basendxltplusgndx ltneii ) ABCZADCIEFG
    H $.

  ${
    grpfn.g $e |- G = { <. ( Base ` ndx ) , B >. , <. ( +g ` ndx ) , .+ >. } $.
    $( A constructed group is a structure.  Version not depending on the
       implementation of the indices.  (Contributed by AV, 27-Oct-2024.) $)
    grpstr $p |- G Struct <. ( Base ` ndx ) , ( +g ` ndx ) >. $=
      ( cnx cplusg cfv basendxltplusgndx plusgndxnn 2strstr ) ABCEFGDHIJ $.

    $( The base set of a constructed group.  (Contributed by Mario Carneiro,
       2-Aug-2013.)  (Revised by Mario Carneiro, 30-Apr-2015.)  (Revised by AV,
       27-Oct-2024.) $)
    grpbase $p |- ( B e. V -> B = ( Base ` G ) ) $=
      ( cnx cplusg cfv basendxltplusgndx plusgndxnn 2strbas ) ABCFGHDEIJK $.

    $( The operation of a constructed group.  (Contributed by Mario Carneiro,
       2-Aug-2013.)  (Revised by Mario Carneiro, 30-Apr-2015.)  (Revised by AV,
       27-Oct-2024.) $)
    grpplusg $p |- ( .+ e. V -> .+ = ( +g ` G ) ) $=
      ( cplusg cnx cfv basendxltplusgndx plusgndxnn plusgid 2strop ) ABFCGFHDEI
      JKL $.
  $}

  ${
    ressplusg.1 $e |- H = ( G |`s A ) $.
    ressplusg.2 $e |- .+ = ( +g ` G ) $.
    $( ` +g ` is unaffected by restriction.  (Contributed by Stefan O'Rear,
       27-Nov-2014.) $)
    ressplusg $p |- ( A e. V -> .+ = ( +g ` H ) ) $=
      ( cplusg plusgid cnx cbs cfv basendxnplusgndx necomi resseqnbas ) ABDHECF
      GIJKLJHLMNO $.
  $}

  ${
    grpstrx.b $e |- B e. _V $.
    grpstrx.p $e |- .+ e. _V $.
    grpstrx.g $e |- G = { <. 1 , B >. , <. 2 , .+ >. } $.
    $( The base of an explicitly given group.  Note:  This theorem has
       hard-coded structure indices for demonstration purposes.  It is not
       intended for general use; use ~ grpbase instead.
       (New usage is discouraged.)  (Contributed by NM, 17-Oct-2012.) $)
    grpbasex $p |- B = ( Base ` G ) $=
      ( cvv wcel cbs cfv wceq c1 cop c2 cpr cnx cplusg basendx opeq1i plusgndx
      preq12i eqtr4i grpbase ax-mp ) AGHACIJKDABCGCLAMZNBMZOPIJZAMZPQJZBMZOFUHU
      EUJUFUGLARSUINBTSUAUBUCUD $.

    $( The operation of an explicitly given group.  Note:  This theorem has
       hard-coded structure indices for demonstration purposes.  It is not
       intended for general use; use ~ grpplusg instead.
       (New usage is discouraged.)  (Contributed by NM, 17-Oct-2012.) $)
    grpplusgx $p |- .+ = ( +g ` G ) $=
      ( cvv wcel cplusg cfv wceq c1 cop c2 cpr cnx cbs basendx opeq1i plusgndx
      preq12i eqtr4i grpplusg ax-mp ) BGHBCIJKEABCGCLAMZNBMZOPQJZAMZPIJZBMZOFUH
      UEUJUFUGLARSUINBTSUAUBUCUD $.
  $}

  $( Index value of the ~ df-mulr slot.  (Contributed by Mario Carneiro,
     14-Aug-2015.)  (New usage is discouraged.) $)
  mulrndx $p |- ( .r ` ndx ) = 3 $=
    ( cmulr c3 df-mulr 3nn ndxarg ) ABCDE $.

  $( Utility theorem: index-independent form of ~ df-mulr .  (Contributed by
     Mario Carneiro, 8-Jun-2013.) $)
  mulridx $p |- .r = Slot ( .r ` ndx ) $=
    ( cmulr c3 df-mulr 3nn ndxid ) ABCDE $.

  $( The slot for the base set is not the slot for the ring (multiplication)
     operation in an extensible structure.  (Contributed by AV, 16-Feb-2020.)
     (Proof shortened by AV, 28-Oct-2024.) $)
  basendxnmulrndx $p |- ( Base ` ndx ) =/= ( .r ` ndx ) $=
    ( cnx cbs cfv c1 cmulr basendx c3 1re 1lt3 ltneii mulrndx neeqtrri eqnetri
    ) ABCDAECZFDGNDGHIJKLM $.

  $( The slot for the group (addition) operation is not the slot for the ring
     (multiplication) operation in an extensible structure.  (Contributed by
     AV, 16-Feb-2020.) $)
  plusgndxnmulrndx $p |- ( +g ` ndx ) =/= ( .r ` ndx ) $=
    ( cnx cplusg cfv c2 cmulr plusgndx 2re 2lt3 ltneii mulrndx neeqtrri eqnetri
    c3 ) ABCDAECZFDMNDMGHIJKL $.

  ${
    rngfn.r $e |- R
               = { <. ( Base ` ndx ) , B >. , <. ( +g ` ndx ) , .+ >. ,
                   <. ( .r ` ndx ) , .x. >. } $.
    $( A constructed ring is a structure.  (Contributed by Mario Carneiro,
       28-Sep-2013.)  (Revised by Mario Carneiro, 29-Aug-2015.) $)
    rngstr $p |- R Struct <. 1 , 3 >. $=
      ( cnx cbs cfv cop cplusg cmulr ctp c1 c3 cstr c2 1nn basendx 1lt2 2nn 3nn
      plusgndx 2lt3 mulrndx strle3 eqbrtri ) CFGHZAIFJHZBIFKHZDILMNIOEUGUHUIMPN
      ABDQRSTUBUCUAUDUEUF $.

    $( The base set of a constructed ring.  (Contributed by Mario Carneiro,
       2-Oct-2013.)  (Revised by Mario Carneiro, 30-Apr-2015.) $)
    rngbase $p |- ( B e. V -> B = ( Base ` R ) ) $=
      ( cbs c1 cop rngstr baseid cnx cfv csn cplusg cmulr ctp snsstp1 sseqtrri
      c3 strfv ) ACGEHTIABCDFJKLGMAIZNUBLOMBIZLPMDIZQCUBUCUDRFSUA $.

    $( The additive operation of a constructed ring.  (Contributed by Mario
       Carneiro, 2-Oct-2013.)  (Revised by Mario Carneiro, 30-Apr-2015.) $)
    rngplusg $p |- ( .+ e. V -> .+ = ( +g ` R ) ) $=
      ( cplusg c1 cop rngstr plusgid cnx cfv csn cbs cmulr ctp snsstp2 sseqtrri
      c3 strfv ) BCGEHTIABCDFJKLGMBIZNLOMAIZUBLPMDIZQCUCUBUDRFSUA $.

    $( The multiplicative operation of a constructed ring.  (Contributed by
       Mario Carneiro, 2-Oct-2013.)  (Revised by Mario Carneiro,
       30-Apr-2015.) $)
    rngmulr $p |- ( .x. e. V -> .x. = ( .r ` R ) ) $=
      ( cmulr c1 cop rngstr mulridx cnx cfv csn cbs cplusg ctp snsstp3 sseqtrri
      c3 strfv ) DCGEHTIABCDFJKLGMDIZNLOMAIZLPMBIZUBQCUCUDUBRFSUA $.
  $}

  $( Index value of the ~ df-starv slot.  (Contributed by Mario Carneiro,
     14-Aug-2015.)  (New usage is discouraged.) $)
  starvndx $p |- ( *r ` ndx ) = 4 $=
    ( cstv c4 df-starv 4nn ndxarg ) ABCDE $.

  $( Utility theorem: index-independent form of ~ df-starv .  (Contributed by
     Mario Carneiro, 6-Oct-2013.) $)
  starvid $p |- *r = Slot ( *r ` ndx ) $=
    ( cstv c4 df-starv 4nn ndxid ) ABCDE $.

  $( The slot for the involution function is not the slot for the base set in
     an extensible structure.  Formerly part of proof for ~ ressstarv .
     (Contributed by AV, 18-Oct-2024.) $)
  starvndxnbasendx $p |- ( *r ` ndx ) =/= ( Base ` ndx ) $=
    ( cnx cstv cfv cbs wne c4 c1 1re 1lt4 gtneii starvndx basendx neeq12i mpbir
    ) ABCZADCZEFGEGFHIJOFPGKLMN $.

  $( The slot for the involution function is not the slot for the base set in
     an extensible structure.  Formerly part of proof for ~ ressstarv .
     (Contributed by AV, 18-Oct-2024.) $)
  starvndxnplusgndx $p |- ( *r ` ndx ) =/= ( +g ` ndx ) $=
    ( cnx cstv cfv cplusg wne c4 c2 2lt4 gtneii starvndx plusgndx neeq12i mpbir
    2re ) ABCZADCZEFGEGFNHIOFPGJKLM $.

  $( The slot for the involution function is not the slot for the base set in
     an extensible structure.  Formerly part of proof for ~ ressstarv .
     (Contributed by AV, 18-Oct-2024.) $)
  starvndxnmulrndx $p |- ( *r ` ndx ) =/= ( .r ` ndx ) $=
    ( cnx cstv cfv cmulr wne c4 3re 3lt4 gtneii starvndx mulrndx neeq12i mpbir
    c3 ) ABCZADCZEFNENFGHIOFPNJKLM $.

  ${
    ressmulr.1 $e |- S = ( R |`s A ) $.
    ${
      ressmulr.2 $e |- .x. = ( .r ` R ) $.
      $( ` .r ` is unaffected by restriction.  (Contributed by Stefan O'Rear,
         27-Nov-2014.) $)
      ressmulr $p |- ( A e. V -> .x. = ( .r ` S ) ) $=
        ( cmulr mulridx cnx cbs cfv basendxnmulrndx necomi resseqnbas ) ADCHEBF
        GIJKLJHLMNO $.
    $}

    ${
      ressstarv.2 $e |- .* = ( *r ` R ) $.
      $( ` *r ` is unaffected by restriction.  (Contributed by Mario Carneiro,
         9-Oct-2015.) $)
      ressstarv $p |- ( A e. V -> .* = ( *r ` S ) ) $=
        ( cstv starvid starvndxnbasendx resseqnbas ) ADCHEBFGIJK $.
    $}
  $}

  ${
    srngstr.r $e |- R = ( {
      <. ( Base ` ndx ) , B >. , <. ( +g ` ndx ) , .+ >. ,
      <. ( .r ` ndx ) , .x. >. } u. { <. ( *r ` ndx ) , .* >. } ) $.
    $( A constructed star ring is a structure.  (Contributed by Mario Carneiro,
       18-Nov-2013.)  (Revised by Mario Carneiro, 14-Aug-2015.) $)
    srngstr $p |- R Struct <. 1 , 4 >. $=
      ( cnx cbs cfv cop cplusg cmulr ctp cstv csn cun c1 c4 cstr c3 eqid rngstr
      4nn starvndx strle1 3lt4 strleun eqbrtri ) CGHIAJGKIBJGLIDJMZGNIZEJOZPQRJ
      SFQTRRUIUKABUIDUIUAUBUJREUCUDUEUFUGUH $.

    $( The base set of a constructed star ring.  (Contributed by Mario
       Carneiro, 18-Nov-2013.)  (Revised by Mario Carneiro, 6-May-2015.) $)
    srngbase $p |- ( B e. X -> B = ( Base ` R ) ) $=
      ( cbs c1 c4 cop srngstr baseid cnx cfv csn cplusg cmulr ctp snsstp1 ssun1
      cstv cun sseqtrri sstri strfv ) ACHFIJKABCDEGLMNHOAKZPUGNQOBKZNRODKZSZCUG
      UHUITUJUJNUBOEKPZUCCUJUKUAGUDUEUF $.

    $( The addition operation of a constructed star ring.  (Contributed by
       Mario Carneiro, 20-Jun-2015.) $)
    srngplusg $p |- ( .+ e. X -> .+ = ( +g ` R ) ) $=
      ( cplusg c1 c4 cop srngstr plusgid cnx cfv csn cbs cmulr ctp snsstp2 cstv
      cun ssun1 sseqtrri sstri strfv ) BCHFIJKABCDEGLMNHOBKZPNQOAKZUGNRODKZSZCU
      HUGUITUJUJNUAOEKPZUBCUJUKUCGUDUEUF $.

    $( The multiplication operation of a constructed star ring.  (Contributed
       by Mario Carneiro, 20-Jun-2015.) $)
    srngmulr $p |- ( .x. e. X -> .x. = ( .r ` R ) ) $=
      ( cmulr c1 c4 cop srngstr mulridx cnx cfv csn cbs cplusg ctp snsstp3 cstv
      cun ssun1 sseqtrri sstri strfv ) DCHFIJKABCDEGLMNHODKZPNQOAKZNROBKZUGSZCU
      HUIUGTUJUJNUAOEKPZUBCUJUKUCGUDUEUF $.

    $( The involution function of a constructed star ring.  (Contributed by
       Mario Carneiro, 20-Jun-2015.) $)
    srnginvl $p |- ( .* e. X -> .* = ( *r ` R ) ) $=
      ( cstv c1 c4 cop srngstr starvid cnx cfv csn cbs cplusg cmulr ctp ssun2
      cun sseqtrri strfv ) ECHFIJKABCDEGLMNHOEKPZNQOAKNROBKNSODKTZUEUBCUEUFUAGU
      CUD $.
  $}

  $( Index value of the ~ df-sca slot.  (Contributed by Mario Carneiro,
     14-Aug-2015.)  (New usage is discouraged.) $)
  scandx $p |- ( Scalar ` ndx ) = 5 $=
    ( csca c5 df-sca 5nn ndxarg ) ABCDE $.

  $( Utility theorem: index-independent form of scalar ~ df-sca .  (Contributed
     by Mario Carneiro, 19-Jun-2014.) $)
  scaid $p |- Scalar = Slot ( Scalar ` ndx ) $=
    ( csca c5 df-sca 5nn ndxid ) ABCDE $.

  $( The slot for the scalar is not the slot for the base set in an extensible
     structure.  (Contributed by AV, 21-Oct-2024.) $)
  scandxnbasendx $p |- ( Scalar ` ndx ) =/= ( Base ` ndx ) $=
    ( cnx csca cfv cbs wne c5 c1 1re 1lt5 gtneii scandx basendx neeq12i mpbir )
    ABCZADCZEFGEGFHIJOFPGKLMN $.

  $( The slot for the scalar field is not the slot for the group operation in
     an extensible structure.  Formerly part of proof for ~ mgpsca .
     (Contributed by AV, 18-Oct-2024.) $)
  scandxnplusgndx $p |- ( Scalar ` ndx ) =/= ( +g ` ndx ) $=
    ( cnx csca cfv cplusg wne c5 2re 2lt5 gtneii scandx plusgndx neeq12i mpbir
    c2 ) ABCZADCZEFNENFGHIOFPNJKLM $.

  $( The slot for the scalar field is not the slot for the ring
     (multiplication) operation in an extensible structure.  Formerly part of
     proof for ~ mgpsca .  (Contributed by AV, 29-Oct-2024.) $)
  scandxnmulrndx $p |- ( Scalar ` ndx ) =/= ( .r ` ndx ) $=
    ( cnx csca cfv cmulr wne c5 c3 3re 3lt5 gtneii scandx mulrndx neeq12i mpbir
    ) ABCZADCZEFGEGFHIJOFPGKLMN $.

  $( Index value of the ~ df-vsca slot.  (Contributed by Mario Carneiro,
     14-Aug-2015.)  (New usage is discouraged.) $)
  vscandx $p |- ( .s ` ndx ) = 6 $=
    ( cvsca c6 df-vsca 6nn ndxarg ) ABCDE $.

  $( Utility theorem: index-independent form of scalar product ~ df-vsca .
     (Contributed by Mario Carneiro, 2-Oct-2013.)  (Revised by Mario Carneiro,
     19-Jun-2014.) $)
  vscaid $p |- .s = Slot ( .s ` ndx ) $=
    ( cvsca c6 df-vsca 6nn ndxid ) ABCDE $.

  $( The slot for the scalar product is not the slot for the base set in an
     extensible structure.  Formerly part of proof for ~ rmodislmod .
     (Contributed by AV, 18-Oct-2024.) $)
  vscandxnbasendx $p |- ( .s ` ndx ) =/= ( Base ` ndx ) $=
    ( cnx cvsca cfv cbs wne c6 c1 1re 1lt6 gtneii vscandx basendx neeq12i mpbir
    ) ABCZADCZEFGEGFHIJOFPGKLMN $.

  $( The slot for the scalar product is not the slot for the group operation in
     an extensible structure.  Formerly part of proof for ~ rmodislmod .
     (Contributed by AV, 18-Oct-2024.) $)
  vscandxnplusgndx $p |- ( .s ` ndx ) =/= ( +g ` ndx ) $=
    ( cnx cvsca cfv cplusg wne c6 c2 2lt6 gtneii vscandx plusgndx neeq12i mpbir
    2re ) ABCZADCZEFGEGFNHIOFPGJKLM $.

  $( The slot for the scalar product is not the slot for the ring
     (multiplication) operation in an extensible structure.  Formerly part of
     proof for ~ rmodislmod .  (Contributed by AV, 29-Oct-2024.) $)
  vscandxnmulrndx $p |- ( .s ` ndx ) =/= ( .r ` ndx ) $=
    ( cnx cvsca cfv cmulr wne c6 3re 3lt6 gtneii vscandx mulrndx neeq12i mpbir
    c3 ) ABCZADCZEFNENFGHIOFPNJKLM $.

  $( The slot for the scalar product is not the slot for the scalar field in an
     extensible structure.  Formerly part of proof for ~ rmodislmod .
     (Contributed by AV, 18-Oct-2024.) $)
  vscandxnscandx $p |- ( .s ` ndx ) =/= ( Scalar ` ndx ) $=
    ( cnx cvsca cfv csca wne c6 c5 5re 5lt6 gtneii vscandx scandx neeq12i mpbir
    ) ABCZADCZEFGEGFHIJOFPGKLMN $.

  ${
    lmodstr.w $e |- W = ( { <. ( Base ` ndx ) , B >. ,
                            <. ( +g ` ndx ) , .+ >. ,
                            <. ( Scalar ` ndx ) , F >. }
                       u. { <. ( .s ` ndx ) , .x. >. } ) $.
    $( A constructed left module or left vector space is a structure.
       (Contributed by Mario Carneiro, 1-Oct-2013.)  (Revised by Mario
       Carneiro, 29-Aug-2015.) $)
    lmodstr $p |- W Struct <. 1 , 6 >. $=
      ( cnx cbs cfv cop cplusg csca ctp cvsca csn cun c1 c6 cstr c5 1nn basendx
      c2 1lt2 2nn plusgndx 5nn scandx strle3 6nn vscandx strle1 strleun eqbrtri
      2lt5 5lt6 ) EGHIZAJGKIZBJGLIZDJMZGNIZCJOZPQRJSFQTRRUTVBUQURUSQUCTABDUAUBU
      DUEUFUOUGUHUIVARCUJUKULUPUMUN $.

    $( The base set of a constructed left vector space.  (Contributed by Mario
       Carneiro, 2-Oct-2013.)  (Revised by Mario Carneiro, 29-Aug-2015.) $)
    lmodbase $p |- ( B e. X -> B = ( Base ` W ) ) $=
      ( cbs c1 c6 cop lmodstr baseid cnx cfv csn cplusg csca ctp snsstp1 cvsca
      cun ssun1 sseqtrri sstri strfv ) AEHFIJKABCDEGLMNHOAKZPUGNQOBKZNRODKZSZEU
      GUHUITUJUJNUAOCKPZUBEUJUKUCGUDUEUF $.

    $( The additive operation of a constructed left vector space.  (Contributed
       by Mario Carneiro, 2-Oct-2013.)  (Revised by Mario Carneiro,
       29-Aug-2015.) $)
    lmodplusg $p |- ( .+ e. X -> .+ = ( +g ` W ) ) $=
      ( cplusg c1 c6 cop lmodstr plusgid cnx cfv csn cbs csca ctp snsstp2 cvsca
      cun ssun1 sseqtrri sstri strfv ) BEHFIJKABCDEGLMNHOBKZPNQOAKZUGNRODKZSZEU
      HUGUITUJUJNUAOCKPZUBEUJUKUCGUDUEUF $.

    $( The set of scalars of a constructed left vector space.  (Contributed by
       Mario Carneiro, 2-Oct-2013.)  (Revised by Mario Carneiro,
       29-Aug-2015.) $)
    lmodsca $p |- ( F e. X -> F = ( Scalar ` W ) ) $=
      ( csca c1 c6 cop lmodstr scaid cnx cfv csn cbs cplusg ctp snsstp3 cvsca
      cun ssun1 sseqtrri sstri strfv ) DEHFIJKABCDEGLMNHODKZPNQOAKZNROBKZUGSZEU
      HUIUGTUJUJNUAOCKPZUBEUJUKUCGUDUEUF $.

    $( The scalar product operation of a constructed left vector space.
       (Contributed by Mario Carneiro, 2-Oct-2013.)  (Revised by Mario
       Carneiro, 29-Aug-2015.) $)
    lmodvsca $p |- ( .x. e. X -> .x. = ( .s ` W ) ) $=
      ( cvsca c1 c6 cop lmodstr vscaid cnx cfv csn cbs cplusg csca ctp sseqtrri
      cun ssun2 strfv ) CEHFIJKABCDEGLMNHOCKPZNQOAKNROBKNSODKTZUEUBEUEUFUCGUAUD
      $.
  $}

  $( Index value of the ~ df-ip slot.  (Contributed by Mario Carneiro,
     14-Aug-2015.)  (New usage is discouraged.) $)
  ipndx $p |- ( .i ` ndx ) = 8 $=
    ( cip c8 df-ip 8nn ndxarg ) ABCDE $.

  $( Utility theorem: index-independent form of ~ df-ip .  (Contributed by
     Mario Carneiro, 6-Oct-2013.) $)
  ipid $p |- .i = Slot ( .i ` ndx ) $=
    ( cip c8 df-ip 8nn ndxid ) ABCDE $.

  $( The slot for the inner product is not the slot for the base set in an
     extensible structure.  (Contributed by AV, 21-Oct-2024.) $)
  ipndxnbasendx $p |- ( .i ` ndx ) =/= ( Base ` ndx ) $=
    ( cnx cip cfv cbs wne c8 c1 1re 1lt8 gtneii ipndx basendx neeq12i mpbir ) A
    BCZADCZEFGEGFHIJOFPGKLMN $.

  $( The slot for the inner product is not the slot for the group operation in
     an extensible structure.  (Contributed by AV, 29-Oct-2024.) $)
  ipndxnplusgndx $p |- ( .i ` ndx ) =/= ( +g ` ndx ) $=
    ( cnx cip cfv cplusg wne c8 c2 2re 2lt8 gtneii ipndx plusgndx neeq12i mpbir
    ) ABCZADCZEFGEGFHIJOFPGKLMN $.

  $( The slot for the inner product is not the slot for the ring
     (multiplication) operation in an extensible structure.  Formerly part of
     proof for ~ mgpsca .  (Contributed by AV, 29-Oct-2024.) $)
  ipndxnmulrndx $p |- ( .i ` ndx ) =/= ( .r ` ndx ) $=
    ( cnx cip cfv cmulr wne c8 c3 3re 3lt8 gtneii ipndx mulrndx neeq12i mpbir )
    ABCZADCZEFGEGFHIJOFPGKLMN $.

  $( The slot for the scalar is not the index of other slots.  Formerly part of
     proof for ~ srasca and ~ sravsca .  (Contributed by AV, 12-Nov-2024.) $)
  slotsdifipndx $p |- ( ( .s ` ndx ) =/= ( .i ` ndx )
                       /\ ( Scalar ` ndx ) =/= ( .i ` ndx ) ) $=
    ( cnx cvsca cfv cip wne csca c6 6re 6lt8 ltneii vscandx ipndx neeq12i mpbir
    c8 c5 5re 5lt8 scandx pm3.2i ) ABCZADCZEZAFCZUBEZUCGOEGOHIJUAGUBOKLMNUEPOEP
    OQRJUDPUBOSLMNT $.

  ${
    ipspart.a $e |- A = ( { <. ( Base ` ndx ) , B >. ,
       <. ( +g ` ndx ) , .+ >. , <. ( .r ` ndx ) , .X. >. } u.
     { <. ( Scalar ` ndx ) , S >. , <. ( .s ` ndx ) , .x. >. ,
       <. ( .i ` ndx ) , I >. } ) $.
    $( Lemma to shorten proofs of ~ ipsbase through ~ ipsvsca .  (Contributed
       by Stefan O'Rear, 27-Nov-2014.)  (Revised by Mario Carneiro,
       29-Aug-2015.)  (Revised by Thierry Arnoux, 16-Jun-2019.) $)
    ipsstr $p |- A Struct <. 1 , 8 >. $=
      ( cnx cbs cfv cop cplusg cmulr ctp csca cvsca c1 c8 c5 cip cstr c3 rngstr
      cun eqid c6 5nn scandx 5lt6 6nn vscandx 6lt8 ipndx strle3 strleun eqbrtri
      8nn 3lt5 ) AIJKBLIMKCLINKFLOZIPKZDLIQKZELIUAKZGLOZUERSLUBHRUCTSUTVDBCUTFU
      TUFUDVAVBVCTUGSDEGUHUIUJUKULUMURUNUOUSUPUQ $.

    $( The base set of a constructed inner product space.  (Contributed by
       Stefan O'Rear, 27-Nov-2014.)  (Revised by Mario Carneiro, 29-Aug-2015.)
       (Revised by Thierry Arnoux, 16-Jun-2019.) $)
    ipsbase $p |- ( B e. V -> B = ( Base ` A ) ) $=
      ( cbs c1 c8 cop ipsstr baseid cnx cfv csn cplusg ctp cmulr csca cvsca cip
      snsstp1 cun ssun1 sseqtrri sstri strfv ) BAJHKLMABCDEFGINOPJQBMZRUKPSQCMZ
      PUAQFMZTZAUKULUMUEUNUNPUBQDMPUCQEMPUDQGMTZUFAUNUOUGIUHUIUJ $.

    $( The additive operation of a constructed inner product space.
       (Contributed by Stefan O'Rear, 27-Nov-2014.)  (Revised by Mario
       Carneiro, 29-Aug-2015.)  (Revised by Thierry Arnoux, 16-Jun-2019.) $)
    ipsaddg $p |- ( .+ e. V -> .+ = ( +g ` A ) ) $=
      ( cplusg c1 c8 cop ipsstr plusgid cnx cfv csn cbs ctp cmulr snsstp2 cvsca
      csca cip cun ssun1 sseqtrri sstri strfv ) CAJHKLMABCDEFGINOPJQCMZRPSQBMZU
      KPUAQFMZTZAULUKUMUBUNUNPUDQDMPUCQEMPUEQGMTZUFAUNUOUGIUHUIUJ $.

    $( The multiplicative operation of a constructed inner product space.
       (Contributed by Stefan O'Rear, 27-Nov-2014.)  (Revised by Mario
       Carneiro, 29-Aug-2015.)  (Revised by Thierry Arnoux, 16-Jun-2019.) $)
    ipsmulr $p |- ( .X. e. V -> .X. = ( .r ` A ) ) $=
      ( cmulr c1 c8 cop ipsstr mulridx cnx cfv csn cbs ctp cplusg snsstp3 cvsca
      csca cip cun ssun1 sseqtrri sstri strfv ) FAJHKLMABCDEFGINOPJQFMZRPSQBMZP
      UAQCMZUKTZAULUMUKUBUNUNPUDQDMPUCQEMPUEQGMTZUFAUNUOUGIUHUIUJ $.

    $( The set of scalars of a constructed inner product space.  (Contributed
       by Stefan O'Rear, 27-Nov-2014.)  (Revised by Mario Carneiro,
       29-Aug-2015.)  (Revised by Thierry Arnoux, 16-Jun-2019.) $)
    ipssca $p |- ( S e. V -> S = ( Scalar ` A ) ) $=
      ( csca c1 c8 cop ipsstr scaid cnx cfv csn cvsca ctp cip snsstp1 cbs cmulr
      cplusg cun ssun2 sseqtrri sstri strfv ) DAJHKLMABCDEFGINOPJQDMZRUKPSQEMZP
      UAQGMZTZAUKULUMUBUNPUCQBMPUEQCMPUDQFMTZUNUFAUNUOUGIUHUIUJ $.

    $( The scalar product operation of a constructed inner product space.
       (Contributed by Stefan O'Rear, 27-Nov-2014.)  (Revised by Mario
       Carneiro, 29-Aug-2015.)  (Revised by Thierry Arnoux, 16-Jun-2019.) $)
    ipsvsca $p |- ( .x. e. V -> .x. = ( .s ` A ) ) $=
      ( cvsca c1 c8 cop ipsstr vscaid cnx cfv csn csca ctp snsstp2 cplusg cmulr
      cip cbs cun ssun2 sseqtrri sstri strfv ) EAJHKLMABCDEFGINOPJQEMZRPSQDMZUK
      PUDQGMZTZAULUKUMUAUNPUEQBMPUBQCMPUCQFMTZUNUFAUNUOUGIUHUIUJ $.

    $( The multiplicative operation of a constructed inner product space.
       (Contributed by Stefan O'Rear, 27-Nov-2014.)  (Revised by Mario
       Carneiro, 29-Aug-2015.)  (Revised by Thierry Arnoux, 16-Jun-2019.) $)
    ipsip $p |- ( I e. V -> I = ( .i ` A ) ) $=
      ( cip c1 c8 cop ipsstr ipid cnx cfv csn csca ctp cvsca snsstp3 cbs cplusg
      cmulr cun ssun2 sseqtrri sstri strfv ) GAJHKLMABCDEFGINOPJQGMZRPSQDMZPUAQ
      EMZUKTZAULUMUKUBUNPUCQBMPUDQCMPUEQFMTZUNUFAUNUOUGIUHUIUJ $.
  $}

  ${
    resssca.1 $e |- H = ( G |`s A ) $.
    ${
      resssca.2 $e |- F = ( Scalar ` G ) $.
      $( ` Scalar ` is unaffected by restriction.  (Contributed by Mario
         Carneiro, 7-Dec-2014.) $)
      resssca $p |- ( A e. V -> F = ( Scalar ` H ) ) $=
        ( csca scaid scandxnbasendx resseqnbas ) ABDHECFGIJK $.
    $}

    ${
      ressvsca.2 $e |- .x. = ( .s ` G ) $.
      $( ` .s ` is unaffected by restriction.  (Contributed by Mario Carneiro,
         7-Dec-2014.) $)
      ressvsca $p |- ( A e. V -> .x. = ( .s ` H ) ) $=
        ( cvsca vscaid vscandxnbasendx resseqnbas ) ABDHECFGIJK $.
    $}

    ${
      ressip.2 $e |- ., = ( .i ` G ) $.
      $( The inner product is unaffected by restriction.  (Contributed by
         Thierry Arnoux, 16-Jun-2019.) $)
      ressip $p |- ( A e. V -> ., = ( .i ` H ) ) $=
        ( cip ipid ipndxnbasendx resseqnbas ) ADCHEBFGIJK $.
    $}
  $}

  ${
    phlfn.h $e |- H = ( { <. ( Base ` ndx ) , B >. , <. ( +g ` ndx ) , .+ >. ,
               <. ( Scalar ` ndx ) , T >. }
            u. { <. ( .s ` ndx ) , .x. >. , <. ( .i ` ndx ) , ., >. } ) $.
    $( A constructed pre-Hilbert space is a structure.  Starting from ~ lmodstr
       (which has 4 members), we chain ~ strleun once more, adding an ordered
       pair to the function, to get all 5 members.  (Contributed by Mario
       Carneiro, 1-Oct-2013.)  (Revised by Mario Carneiro, 29-Aug-2015.) $)
    phlstr $p |- H Struct <. 1 , 8 >. $=
      ( cnx cbs cfv cop cplusg csca ctp cvsca csn cun cip c1 c8 cstr cpr uneq2i
      df-pr unass 3eqtr4i c6 eqid lmodstr 8nn ipndx strle1 6lt8 strleun eqbrtri
      ) EHIJAKHLJBKHMJCKNZHOJDKZPZQZHRJZFKZPZQZSTKUAUPUQVAUBZQUPURVBQZQEVCVDVEU
      PUQVAUDUCGUPURVBUEUFSUGTTUSVBABDCUSUSUHUIUTTFUJUKULUMUNUO $.

    $( The base set of a constructed pre-Hilbert space.  (Contributed by Mario
       Carneiro, 6-Oct-2013.)  (Revised by Mario Carneiro, 29-Aug-2015.) $)
    phlbase $p |- ( B e. X -> B = ( Base ` H ) ) $=
      ( cbs c1 c8 cop phlstr baseid cnx cfv csn cplusg csca ctp snsstp1 cip cpr
      cvsca cun ssun1 sseqtrri sstri strfv ) AEIGJKLABCDEFHMNOIPALZQUJORPBLZOSP
      CLZTZEUJUKULUAUMUMOUDPDLOUBPFLUCZUEEUMUNUFHUGUHUI $.

    $( The additive operation of a constructed pre-Hilbert space.  (Contributed
       by Mario Carneiro, 6-Oct-2013.)  (Revised by Mario Carneiro,
       29-Aug-2015.) $)
    phlplusg $p |- ( .+ e. X -> .+ = ( +g ` H ) ) $=
      ( cplusg c1 c8 cop phlstr plusgid cnx cfv csn cbs csca ctp cvsca sseqtrri
      snsstp2 cip cpr cun ssun1 sstri strfv ) BEIGJKLABCDEFHMNOIPBLZQORPALZUJOS
      PCLZTZEUKUJULUCUMUMOUAPDLOUDPFLUEZUFEUMUNUGHUBUHUI $.

    $( The ring of scalars of a constructed pre-Hilbert space.  (Contributed by
       Mario Carneiro, 6-Oct-2013.)  (Revised by Mario Carneiro,
       29-Aug-2015.) $)
    phlsca $p |- ( T e. X -> T = ( Scalar ` H ) ) $=
      ( csca c1 c8 cop phlstr scaid cnx cfv csn cbs cplusg ctp snsstp3 sseqtrri
      cvsca cip cpr cun ssun1 sstri strfv ) CEIGJKLABCDEFHMNOIPCLZQORPALZOSPBLZ
      UJTZEUKULUJUAUMUMOUCPDLOUDPFLUEZUFEUMUNUGHUBUHUI $.

    $( The scalar product operation of a constructed pre-Hilbert space.
       (Contributed by Mario Carneiro, 6-Oct-2013.)  (Revised by Mario
       Carneiro, 29-Aug-2015.) $)
    phlvsca $p |- ( .x. e. X -> .x. = ( .s ` H ) ) $=
      ( cvsca c1 c8 cop phlstr vscaid cnx cfv csn cip cpr snsspr1 cbs ctp ssun2
      cplusg csca cun sseqtrri sstri strfv ) DEIGJKLABCDEFHMNOIPDLZQUJORPFLZSZE
      UJUKTULOUAPALOUDPBLOUEPCLUBZULUFEULUMUCHUGUHUI $.

    $( The inner product (Hermitian form) operation of a constructed
       pre-Hilbert space.  (Contributed by Mario Carneiro, 6-Oct-2013.)
       (Revised by Mario Carneiro, 29-Aug-2015.) $)
    phlip $p |- ( ., e. X -> ., = ( .i ` H ) ) $=
      ( cip c1 c8 cop phlstr ipid cnx cfv csn cvsca cpr snsspr2 cbs cplusg csca
      ctp cun ssun2 sseqtrri sstri strfv ) FEIGJKLABCDEFHMNOIPFLZQORPDLZUJSZEUK
      UJTULOUAPALOUBPBLOUCPCLUDZULUEEULUMUFHUGUHUI $.
  $}

  $( Index value of the ~ df-tset slot.  (Contributed by Mario Carneiro,
     14-Aug-2015.)  (New usage is discouraged.) $)
  tsetndx $p |- ( TopSet ` ndx ) = 9 $=
    ( cts c9 df-tset 9nn ndxarg ) ABCDE $.

  $( Utility theorem: index-independent form of ~ df-tset .  (Contributed by
     NM, 20-Oct-2012.) $)
  tsetid $p |- TopSet = Slot ( TopSet ` ndx ) $=
    ( cts c9 df-tset 9nn ndxid ) ABCDE $.

  $( The index of the slot for the group operation in an extensible structure
     is a positive integer.  (Contributed by AV, 31-Oct-2024.) $)
  tsetndxnn $p |- ( TopSet ` ndx ) e. NN $=
    ( cnx cts cfv c9 cn tsetndx 9nn eqeltri ) ABCDEFGH $.

  $( The index of the slot for the base set is less than the index of the slot
     for the topology in an extensible structure.  (Contributed by AV,
     31-Oct-2024.) $)
  basendxlttsetndx $p |- ( Base ` ndx ) < ( TopSet ` ndx ) $=
    ( c1 c9 cnx cbs cfv cts clt 1lt9 basendx tsetndx 3brtr4i ) ABCDECFEGHIJK $.

  $( The slot for the topology is not the slot for the base set in an
     extensible structure.  (Contributed by AV, 21-Oct-2024.)  (Proof shortened
     by AV, 31-Oct-2024.) $)
  tsetndxnbasendx $p |- ( TopSet ` ndx ) =/= ( Base ` ndx ) $=
    ( cnx cbs cfv cts basendxnn nnrei basendxlttsetndx gtneii ) ABCZADCIEFGH $.

  $( The slot for the topology is not the slot for the group operation in an
     extensible structure.  Formerly part of proof for ~ oppgtset .
     (Contributed by AV, 18-Oct-2024.) $)
  tsetndxnplusgndx $p |- ( TopSet ` ndx ) =/= ( +g ` ndx ) $=
    ( cnx cts cfv cplusg wne c9 2re 2lt9 gtneii tsetndx plusgndx neeq12i mpbir
    c2 ) ABCZADCZEFNENFGHIOFPNJKLM $.

  $( The slot for the topology is not the slot for the ring multiplication
     operation in an extensible structure.  (Contributed by AV,
     31-Oct-2024.) $)
  tsetndxnmulrndx $p |- ( TopSet ` ndx ) =/= ( .r ` ndx ) $=
    ( cnx cts cfv cmulr wne c9 c3 3re 3lt9 gtneii tsetndx mulrndx neeq12i mpbir
    ) ABCZADCZEFGEGFHIJOFPGKLMN $.

  $( The slot for the topology is not the slot for the involution in an
     extensible structure.  Formerly part of proof for ~ cnfldfunALT .
     (Contributed by AV, 11-Nov-2024.) $)
  tsetndxnstarvndx $p |- ( TopSet ` ndx ) =/= ( *r ` ndx ) $=
    ( cnx cts cfv cstv wne c9 c4 4re 4lt9 gtneii tsetndx starvndx neeq12i mpbir
    ) ABCZADCZEFGEGFHIJOFPGKLMN $.

  $( The slots ` Scalar ` , ` .s ` and ` .i ` are different from the slot
     ` TopSet ` .  Formerly part of ~ sralem and proofs using it.  (Contributed
     by AV, 29-Oct-2024.) $)
  slotstnscsi $p |- ( ( TopSet ` ndx ) =/= ( Scalar ` ndx )
                   /\ ( TopSet ` ndx ) =/= ( .s ` ndx )
                   /\ ( TopSet ` ndx ) =/= ( .i ` ndx ) ) $=
    ( cnx cts cfv csca wne cvsca cip c9 c5 5re 5lt9 gtneii tsetndx scandx mpbir
    neeq12i c6 6re 6lt9 c8 vscandx 8re 8lt9 ipndx 3pm3.2i ) ABCZADCZEZUFAFCZEZU
    FAGCZEZUHHIEIHJKLUFHUGIMNPOUJHQEQHRSLUFHUIQMUAPOULHTETHUBUCLUFHUKTMUDPOUE
    $.

  ${
    topgrpfn.w $e |- W = { <. ( Base ` ndx ) , B >. ,
       <. ( +g ` ndx ) , .+ >. , <. ( TopSet ` ndx ) , J >. } $.
    $( A constructed topological group is a structure.  (Contributed by Mario
       Carneiro, 29-Aug-2015.) $)
    topgrpstr $p |- W Struct <. 1 , 9 >. $=
      ( cnx cbs cfv cop cplusg cts ctp c1 c9 cstr c2 1nn basendx 1lt2 2nn 2lt9
      plusgndx 9nn tsetndx strle3 eqbrtri ) DFGHZAIFJHZBIFKHZCILMNIOEUGUHUIMPNA
      BCQRSTUBUAUCUDUEUF $.

    $( The base set of a constructed topological group.  (Contributed by Mario
       Carneiro, 29-Aug-2015.) $)
    topgrpbas $p |- ( B e. X -> B = ( Base ` W ) ) $=
      ( cbs c1 cop topgrpstr baseid cnx cfv csn cplusg cts ctp snsstp1 sseqtrri
      c9 strfv ) ADGEHTIABCDFJKLGMAIZNUBLOMBIZLPMCIZQDUBUCUDRFSUA $.

    $( The additive operation of a constructed topological group.  (Contributed
       by Mario Carneiro, 29-Aug-2015.) $)
    topgrpplusg $p |- ( .+ e. X -> .+ = ( +g ` W ) ) $=
      ( cplusg c1 c9 cop topgrpstr plusgid cnx cfv csn cbs cts snsstp2 sseqtrri
      ctp strfv ) BDGEHIJABCDFKLMGNBJZOMPNAJZUBMQNCJZTDUCUBUDRFSUA $.

    $( The topology of a constructed topological group.  (Contributed by Mario
       Carneiro, 29-Aug-2015.) $)
    topgrptset $p |- ( J e. X -> J = ( TopSet ` W ) ) $=
      ( cts c1 cop topgrpstr tsetid cnx cfv csn cbs cplusg ctp snsstp3 sseqtrri
      c9 strfv ) CDGEHTIABCDFJKLGMCIZNLOMAIZLPMBIZUBQDUCUDUBRFSUA $.
  $}

  ${
    resstset.1 $e |- H = ( G |`s A ) $.
    resstset.2 $e |- J = ( TopSet ` G ) $.
    $( ` TopSet ` is unaffected by restriction.  (Contributed by Mario
       Carneiro, 13-Aug-2015.) $)
    resstset $p |- ( A e. V -> J = ( TopSet ` H ) ) $=
      ( cts tsetid tsetndxnbasendx resseqnbas ) ADCHEBFGIJK $.
  $}

  $( Index value of the ~ df-ple slot.  (Contributed by Mario Carneiro,
     14-Aug-2015.)  (Revised by AV, 9-Sep-2021.)
     (New usage is discouraged.) $)
  plendx $p |- ( le ` ndx ) = ; 1 0 $=
    ( cple c1 cc0 cdc df-ple 10nn ndxarg ) ABCDEFG $.

  $( Utility theorem: self-referencing, index-independent form of ~ df-ple .
     (Contributed by NM, 9-Nov-2012.)  (Revised by AV, 9-Sep-2021.) $)
  pleid $p |- le = Slot ( le ` ndx ) $=
    ( cple c1 cc0 cdc df-ple 10nn ndxid ) ABCDEFG $.

  $( The index value of the order slot is a positive integer.  This property
     should be ensured for every concrete coding because otherwise it could not
     be used in an extensible structure (slots must be positive integers).
     (Contributed by AV, 30-Oct-2024.) $)
  plendxnn $p |- ( le ` ndx ) e. NN $=
    ( cnx cple cfv c1 cc0 cdc cn plendx 10nn eqeltri ) ABCDEFGHIJ $.

  $( The index value of the ` Base ` slot is less than the index value of the
     ` le ` slot.  (Contributed by AV, 30-Oct-2024.) $)
  basendxltplendx $p |- ( Base ` ndx ) < ( le ` ndx ) $=
    ( c1 cc0 cdc cnx cbs cfv cple clt 1lt10 basendx plendx 3brtr4i ) AABCDEFDGF
    HIJKL $.

  $( The slot for the order is not the slot for the base set in an extensible
     structure.  (Contributed by AV, 21-Oct-2024.)  (Proof shortened by AV,
     30-Oct-2024.) $)
  plendxnbasendx $p |- ( le ` ndx ) =/= ( Base ` ndx ) $=
    ( cnx cbs cfv cple basendxnn nnrei basendxltplendx gtneii ) ABCZADCIEFGH $.

  $( The slot for the "less than or equal to" ordering is not the slot for the
     group operation in an extensible structure.  Formerly part of proof for
     ~ oppgle .  (Contributed by AV, 18-Oct-2024.) $)
  plendxnplusgndx $p |- ( le ` ndx ) =/= ( +g ` ndx ) $=
    ( cnx cfv cplusg wne c1 cc0 cdc c2 2re 2lt10 gtneii plendx plusgndx neeq12i
    cple mpbir ) AOBZACBZDEFGZHDHSIJKQSRHLMNP $.

  $( The slot for the "less than or equal to" ordering is not the slot for the
     ring multiplication operation in an extensible structure.  Formerly part
     of proof for ~ opsrmulr .  (Contributed by AV, 1-Nov-2024.) $)
  plendxnmulrndx $p |- ( le ` ndx ) =/= ( .r ` ndx ) $=
    ( cnx cple cfv cmulr wne c1 cc0 cdc 3re 3lt10 gtneii plendx mulrndx neeq12i
    c3 mpbir ) ABCZADCZEFGHZOEOSIJKQSROLMNP $.

  $( The slot for the "less than or equal to" ordering is not the slot for the
     scalar in an extensible structure.  Formerly part of proof for ~ opsrsca .
     (Contributed by AV, 1-Nov-2024.) $)
  plendxnscandx $p |- ( le ` ndx ) =/= ( Scalar ` ndx ) $=
    ( cnx cple cfv csca wne c1 cc0 cdc c5 5re 5lt10 gtneii plendx neeq12i mpbir
    scandx ) ABCZADCZEFGHZIEISJKLQSRIMPNO $.

  $( The slot for the "less than or equal to" ordering is not the slot for the
     scalar product in an extensible structure.  Formerly part of proof for
     ~ opsrvsca .  (Contributed by AV, 1-Nov-2024.) $)
  plendxnvscandx $p |- ( le ` ndx ) =/= ( .s ` ndx ) $=
    ( cnx cple cfv cvsca wne c1 cc0 cdc 6re 6lt10 gtneii plendx vscandx neeq12i
    c6 mpbir ) ABCZADCZEFGHZOEOSIJKQSROLMNP $.

  $( The index of the slot for the distance is not the index of other slots.
     Formerly part of proof for ~ cnfldfunALT .  (Contributed by AV,
     11-Nov-2024.) $)
  slotsdifplendx $p |- ( ( *r ` ndx ) =/= ( le ` ndx )
                         /\ ( TopSet ` ndx ) =/= ( le ` ndx ) ) $=
    ( cnx cstv cfv cple wne cts c4 c1 cc0 cdc 4re 4lt10 ltneii starvndx neeq12i
    plendx mpbir c9 9re 9lt10 tsetndx pm3.2i ) ABCZADCZEZAFCZUDEZUEGHIJZEGUHKLM
    UCGUDUHNPOQUGRUHERUHSTMUFRUDUHUAPOQUB $.

  ${
    otpsstr.w $e |- K = { <. ( Base ` ndx ) , B >. ,
      <. ( TopSet ` ndx ) , J >. , <. ( le ` ndx ) , .<_ >. } $.
    $( Functionality of a topological ordered space.  (Contributed by Mario
       Carneiro, 12-Nov-2015.)  (Revised by AV, 9-Sep-2021.) $)
    otpsstr $p |- K Struct <. 1 , ; 1 0 >. $=
      ( cnx cbs cfv cop cts cple ctp c1 cc0 cdc cstr c9 1nn basendx 1lt9 plendx
      9nn tsetndx 9lt10 10nn strle3 eqbrtri ) CFGHZAIFJHZBIFKHZDILMMNOZIPEUHUIU
      JMQUKABDRSTUBUCUDUEUAUFUG $.

    $( The base set of a topological ordered space.  (Contributed by Mario
       Carneiro, 12-Nov-2015.)  (Revised by AV, 9-Sep-2021.) $)
    otpsbas $p |- ( B e. V -> B = ( Base ` K ) ) $=
      ( cbs c1 cc0 cdc cop otpsstr baseid cnx cfv csn cts cple ctp snsstp1
      sseqtrri strfv ) ACGEHHIJKABCDFLMNGOAKZPUCNQOBKZNRODKZSCUCUDUETFUAUB $.

    $( The open sets of a topological ordered space.  (Contributed by Mario
       Carneiro, 12-Nov-2015.)  (Revised by AV, 9-Sep-2021.) $)
    otpstset $p |- ( J e. V -> J = ( TopSet ` K ) ) $=
      ( cts c1 cc0 cdc cop otpsstr tsetid cnx cfv csn cbs cple ctp snsstp2
      sseqtrri strfv ) BCGEHHIJKABCDFLMNGOBKZPNQOAKZUCNRODKZSCUDUCUETFUAUB $.

    $( The order of a topological ordered space.  (Contributed by Mario
       Carneiro, 12-Nov-2015.)  (Revised by AV, 9-Sep-2021.) $)
    otpsle $p |- ( .<_ e. V -> .<_ = ( le ` K ) ) $=
      ( cple c1 cc0 cdc cop otpsstr pleid cnx cfv csn cbs cts ctp snsstp3 strfv
      sseqtrri ) DCGEHHIJKABCDFLMNGODKZPNQOAKZNROBKZUCSCUDUEUCTFUBUA $.
  $}

  ${
    ressle.1 $e |- W = ( K |`s A ) $.
    ressle.2 $e |- .<_ = ( le ` K ) $.
    $( ` le ` is unaffected by restriction.  (Contributed by Mario Carneiro,
       3-Nov-2015.) $)
    ressle $p |- ( A e. V -> .<_ = ( le ` W ) ) $=
      ( cple pleid plendxnbasendx resseqnbas ) ACEHDBFGIJK $.
  $}

  $( Index value of the ~ df-ocomp slot.  (Contributed by Mario Carneiro,
     25-Oct-2015.)  (New usage is discouraged.) $)
  ocndx $p |- ( oc ` ndx ) = ; 1 1 $=
    ( coc c1 cdc df-ocomp 1nn0 1nn decnncl ndxarg ) ABBCDBBEFGH $.

  $( Utility theorem: index-independent form of ~ df-ocomp .  (Contributed by
     Mario Carneiro, 25-Oct-2015.) $)
  ocid $p |- oc = Slot ( oc ` ndx ) $=
    ( coc c1 cdc df-ocomp 1nn0 1nn decnncl ndxid ) ABBCDBBEFGH $.

  $( The slot for the orthocomplementation is not the slot for the base set in
     an extensible structure.  Formerly part of proof for ~ thlbas .
     (Contributed by AV, 11-Nov-2024.) $)
  basendxnocndx $p |- ( Base ` ndx ) =/= ( oc ` ndx ) $=
    ( cnx cbs cfv coc wne c1 cdc 1re 1nn 1nn0 1lt10 declti ltneii basendx ocndx
    neeq12i mpbir ) ABCZADCZEFFFGZEFTHFFFIJJKLMRFSTNOPQ $.

  $( The slot for the orthocomplementation is not the slot for the order in an
     extensible structure.  Formerly part of proof for ~ thlle .  (Contributed
     by AV, 11-Nov-2024.) $)
  plendxnocndx $p |- ( le ` ndx ) =/= ( oc ` ndx ) $=
    ( cnx cple cfv coc wne cc0 cdc 10re 1nn0 0nn0 1nn declt ltneii plendx ocndx
    c1 0lt1 neeq12i mpbir ) ABCZADCZEPFGZPPGZEUBUCHPFPIJKQLMTUBUAUCNORS $.

  $( Index value of the ~ df-ds slot.  (Contributed by Mario Carneiro,
     14-Aug-2015.)  (New usage is discouraged.) $)
  dsndx $p |- ( dist ` ndx ) = ; 1 2 $=
    ( cds c1 c2 cdc df-ds 1nn0 2nn decnncl ndxarg ) ABCDEBCFGHI $.

  $( Utility theorem: index-independent form of ~ df-ds .  (Contributed by
     Mario Carneiro, 23-Dec-2013.) $)
  dsid $p |- dist = Slot ( dist ` ndx ) $=
    ( cds c1 c2 cdc df-ds 1nn0 2nn decnncl ndxid ) ABCDEBCFGHI $.

  $( The index of the slot for the distance in an extensible structure is a
     positive integer.  Formerly part of proof for ~ tmslem .  (Contributed by
     AV, 28-Oct-2024.) $)
  dsndxnn $p |- ( dist ` ndx ) e. NN $=
    ( cnx cds cfv c1 c2 cdc cn dsndx 1nn0 2nn decnncl eqeltri ) ABCDEFGHDEIJKL
    $.

  $( The index of the slot for the base set is less than the index of the slot
     for the distance in an extensible structure.  Formerly part of proof for
     ~ tmslem .  (Contributed by AV, 28-Oct-2024.) $)
  basendxltdsndx $p |- ( Base ` ndx ) < ( dist ` ndx ) $=
    ( c1 c2 cdc cnx cbs cfv cds clt 1nn 2nn0 1lt10 declti basendx dsndx 3brtr4i
    1nn0 ) AABCDEFDGFHABAIJPKLMNO $.

  $( The slot for the distance is not the slot for the base set in an
     extensible structure.  (Contributed by AV, 21-Oct-2024.)  (Proof shortened
     by AV, 28-Oct-2024.) $)
  dsndxnbasendx $p |- ( dist ` ndx ) =/= ( Base ` ndx ) $=
    ( cnx cbs cfv cds basendxnn nnrei basendxltdsndx gtneii ) ABCZADCIEFGH $.

  $( The slot for the distance function is not the slot for the group operation
     in an extensible structure.  Formerly part of proof for ~ mgpds .
     (Contributed by AV, 18-Oct-2024.) $)
  dsndxnplusgndx $p |- ( dist ` ndx ) =/= ( +g ` ndx ) $=
    ( cnx cds cfv cplusg wne c1 c2 cdc 2re 1nn 2nn0 2lt10 declti dsndx plusgndx
    gtneii neeq12i mpbir ) ABCZADCZEFGHZGEGUAIFGGJKKLMPSUATGNOQR $.

  $( The slot for the distance function is not the slot for the ring
     multiplication operation in an extensible structure.  (Contributed by AV,
     31-Oct-2024.) $)
  dsndxnmulrndx $p |- ( dist ` ndx ) =/= ( .r ` ndx ) $=
    ( cnx cds cfv cmulr wne c1 c2 cdc c3 3re 1nn 2nn0 3lt10 declti gtneii dsndx
    3nn0 mulrndx neeq12i mpbir ) ABCZADCZEFGHZIEIUCJFGIKLQMNOUAUCUBIPRST $.

  $( The slots ` Scalar ` , ` .s ` and ` .i ` are different from the slot
     ` dist ` .  Formerly part of ~ sralem and proofs using it.  (Contributed
     by AV, 29-Oct-2024.) $)
  slotsdnscsi $p |- ( ( dist ` ndx ) =/= ( Scalar ` ndx )
                   /\ ( dist ` ndx ) =/= ( .s ` ndx )
                   /\ ( dist ` ndx ) =/= ( .i ` ndx ) ) $=
    ( cnx cds cfv csca wne cvsca cip c1 c2 cdc c5 1nn 2nn0 declti dsndx neeq12i
    gtneii mpbir c6 c8 5re 5nn0 5lt10 scandx 6re 6nn0 6lt10 vscandx 8lt10 ipndx
    8re 8nn0 3pm3.2i ) ABCZADCZEZUNAFCZEZUNAGCZEZUPHIJZKEKVAUAHIKLMUBUCNQUNVAUO
    KOUDPRURVASESVAUEHISLMUFUGNQUNVAUQSOUHPRUTVATETVAUKHITLMULUINQUNVAUSTOUJPRU
    M $.

  $( The slot for the distance function is not the slot for the topology in an
     extensible structure.  Formerly part of proof for ~ tngds .  (Contributed
     by AV, 29-Oct-2024.) $)
  dsndxntsetndx $p |- ( dist ` ndx ) =/= ( TopSet ` ndx ) $=
    ( cnx cds cfv cts wne c1 c2 cdc 9re 1nn 2nn0 9nn0 9lt10 declti gtneii dsndx
    c9 tsetndx neeq12i mpbir ) ABCZADCZEFGHZQEQUCIFGQJKLMNOUAUCUBQPRST $.

  $( The index of the slot for the distance is not the index of other slots.
     Formerly part of proof for ~ cnfldfunALT .  (Contributed by AV,
     11-Nov-2024.) $)
  slotsdifdsndx $p |- ( ( *r ` ndx ) =/= ( dist ` ndx )
                        /\ ( le ` ndx ) =/= ( dist ` ndx ) ) $=
    ( cnx cstv cfv cds wne cple c4 c1 c2 cdc 4re 2nn0 4nn0 4lt10 ltneii neeq12i
    1nn dsndx mpbir cc0 declti starvndx 10re 1nn0 0nn0 2pos declt plendx pm3.2i
    2nn ) ABCZADCZEZAFCZULEZUMGHIJZEGUPKHIGQLMNUAOUKGULUPUBRPSUOHTJZUPEUQUPUCHT
    IUDUEUJUFUGOUNUQULUPUHRPSUI $.

  $( Index value of the ~ df-unif slot.  (Contributed by Thierry Arnoux,
     17-Dec-2017.)  (New usage is discouraged.) $)
  unifndx $p |- ( UnifSet ` ndx ) = ; 1 3 $=
    ( cunif c1 c3 cdc df-unif 1nn0 3nn decnncl ndxarg ) ABCDEBCFGHI $.

  $( Utility theorem: index-independent form of ~ df-unif .  (Contributed by
     Thierry Arnoux, 17-Dec-2017.) $)
  unifid $p |- UnifSet = Slot ( UnifSet ` ndx ) $=
    ( cunif c1 c3 cdc df-unif 1nn0 3nn decnncl ndxid ) ABCDEBCFGHI $.

  $( The index of the slot for the uniform set in an extensible structure is a
     positive integer.  Formerly part of proof for ~ tuslem .  (Contributed by
     AV, 28-Oct-2024.) $)
  unifndxnn $p |- ( UnifSet ` ndx ) e. NN $=
    ( cnx cunif cfv c1 c3 cdc cn unifndx 1nn0 3nn decnncl eqeltri ) ABCDEFGHDEI
    JKL $.

  $( The index of the slot for the base set is less than the index of the slot
     for the uniform set in an extensible structure.  Formerly part of proof
     for ~ tuslem .  (Contributed by AV, 28-Oct-2024.) $)
  basendxltunifndx $p |- ( Base ` ndx ) < ( UnifSet ` ndx ) $=
    ( c1 cdc cnx cbs cfv cunif clt 1nn 3nn0 1nn0 declti basendx unifndx 3brtr4i
    c3 1lt10 ) AAOBCDECFEGAOAHIJPKLMN $.

  $( The slot for the uniform set is not the slot for the base set in an
     extensible structure.  (Contributed by AV, 21-Oct-2024.) $)
  unifndxnbasendx $p |- ( UnifSet ` ndx ) =/= ( Base ` ndx ) $=
    ( cnx cbs cfv cunif basendxnn nnrei basendxltunifndx gtneii ) ABCZADCIEFGH
    $.

  $( The slot for the uniform set is not the slot for the topology in an
     extensible structure.  Formerly part of proof for ~ tuslem .  (Contributed
     by AV, 28-Oct-2024.) $)
  unifndxntsetndx $p |- ( UnifSet ` ndx ) =/= ( TopSet ` ndx ) $=
    ( cnx cunif cfv cts wne c1 c3 cdc c9 9re 1nn 3nn0 9nn0 9lt10 declti unifndx
    gtneii tsetndx neeq12i mpbir ) ABCZADCZEFGHZIEIUCJFGIKLMNOQUAUCUBIPRST $.

  $( The index of the slot for the uniform set is not the index of other slots.
     Formerly part of proof for ~ cnfldfunALT .  (Contributed by AV,
     10-Nov-2024.) $)
  slotsdifunifndx $p |- ( ( ( +g ` ndx ) =/= ( UnifSet ` ndx )
                         /\ ( .r ` ndx ) =/= ( UnifSet ` ndx )
                         /\ ( *r ` ndx ) =/= ( UnifSet ` ndx ) )
                       /\ ( ( le ` ndx ) =/= ( UnifSet ` ndx )
                         /\ ( dist ` ndx ) =/= ( UnifSet ` ndx ) ) ) $=
    ( cnx cfv wne c2 c1 c3 cdc 3nn0 2nn0 declti ltneii unifndx neeq12i mpbir c4
    1nn cc0 1nn0 3nn declt cplusg cunif cmulr cstv w3a cple cds wa 2re plusgndx
    2lt10 3re 3lt10 mulrndx 4re 4nn0 starvndx 3pm3.2i 10re 0nn0 3pos plendx 2nn
    4lt10 decnncl nnrei 2lt3 dsndx pm3.2i ) AUABZAUBBZCZAUCBZVKCZAUDBZVKCZUEAUF
    BZVKCZAUGBZVKCZUHVLVNVPVLDEFGZCDWAUIEFDPHIUKJKVJDVKWAUJLMNVNFWACFWAULEFFPHH
    UMJKVMFVKWAUNLMNVPOWACOWAUOEFOPHUPVDJKVOOVKWAUQLMNURVRVTVREQGZWACWBWAUSEQFR
    UTSVATKVQWBVKWAVBLMNVTEDGZWACWCWAWCEDRVCVEVFEDFRISVGTKVSWCVKWAVHLMNVIVI $.

  ${
    ressunif.1 $e |- H = ( G |`s A ) $.
    ressunif.2 $e |- U = ( UnifSet ` G ) $.
    $( ` UnifSet ` is unaffected by restriction.  (Contributed by Thierry
       Arnoux, 7-Dec-2017.) $)
    ressunif $p |- ( A e. V -> U = ( UnifSet ` H ) ) $=
      ( cunif unifid unifndxnbasendx resseqnbas ) ABDHECFGIJK $.
  $}

  ${
    odrngstr.w $e |- W = ( { <. ( Base ` ndx ) , B >. ,
       <. ( +g ` ndx ) , .+ >. , <. ( .r ` ndx ) , .x. >. } u.
     { <. ( TopSet ` ndx ) , J >. , <. ( le ` ndx ) , .<_ >. ,
       <. ( dist ` ndx ) , D >. } ) $.
    $( Functionality of an ordered metric ring.  (Contributed by Mario
       Carneiro, 20-Aug-2015.)  (Proof shortened by AV, 15-Sep-2021.) $)
    odrngstr $p |- W Struct <. 1 , ; 1 2 >. $=
      ( cnx cbs cfv cop ctp c1 c2 cdc c9 cc0 1nn0 2nn cplusg cmulr cts cple cds
      cun cstr c3 eqid rngstr tsetndx 9lt10 10nn plendx 0nn0 2pos declt decnncl
      9nn dsndx strle3 3lt9 strleun eqbrtri ) GIJKALIUAKCLIUBKDLMZIUCKZELIUDKZF
      LIUEKZBLMZUFNNOPZLUGHNUHQVJVEVIACVEDVEUIUJVFVGVHQNRPVJEFBUSUKULUMUNNROSUO
      TUPUQNOSTURUTVAVBVCVD $.

    $( The base set of an ordered metric ring.  (Contributed by Mario Carneiro,
       20-Aug-2015.) $)
    odrngbas $p |- ( B e. V -> B = ( Base ` W ) ) $=
      ( cbs c1 c2 cdc cop odrngstr baseid cnx cfv csn ctp cplusg cmulr cts cple
      snsstp1 cds cun ssun1 sseqtrri sstri strfv ) AHJGKKLMNABCDEFHIOPQJRANZSUL
      QUARCNZQUBRDNZTZHULUMUNUEUOUOQUCRENQUDRFNQUFRBNTZUGHUOUPUHIUIUJUK $.

    $( The addition operation of an ordered metric ring.  (Contributed by Mario
       Carneiro, 20-Aug-2015.) $)
    odrngplusg $p |- ( .+ e. V -> .+ = ( +g ` W ) ) $=
      ( cplusg c1 c2 cdc cop odrngstr plusgid cnx cfv csn ctp cbs cmulr snsstp2
      cts cple cds cun ssun1 sseqtrri sstri strfv ) CHJGKKLMNABCDEFHIOPQJRCNZSQ
      UARANZULQUBRDNZTZHUMULUNUCUOUOQUDRENQUERFNQUFRBNTZUGHUOUPUHIUIUJUK $.

    $( The multiplication operation of an ordered metric ring.  (Contributed by
       Mario Carneiro, 20-Aug-2015.) $)
    odrngmulr $p |- ( .x. e. V -> .x. = ( .r ` W ) ) $=
      ( cmulr c1 c2 cdc cop odrngstr mulridx cnx cfv csn ctp cbs cplusg snsstp3
      cts cple cds cun ssun1 sseqtrri sstri strfv ) DHJGKKLMNABCDEFHIOPQJRDNZSQ
      UARANZQUBRCNZULTZHUMUNULUCUOUOQUDRENQUERFNQUFRBNTZUGHUOUPUHIUIUJUK $.

    $( The open sets of an ordered metric ring.  (Contributed by Mario
       Carneiro, 20-Aug-2015.) $)
    odrngtset $p |- ( J e. V -> J = ( TopSet ` W ) ) $=
      ( cts c1 c2 cdc cop odrngstr tsetid cnx cfv csn ctp cds snsstp1 cbs cmulr
      cple cplusg cun ssun2 sseqtrri sstri strfv ) EHJGKKLMNABCDEFHIOPQJRENZSUL
      QUERFNZQUARBNZTZHULUMUNUBUOQUCRANQUFRCNQUDRDNTZUOUGHUOUPUHIUIUJUK $.

    $( The order of an ordered metric ring.  (Contributed by Mario Carneiro,
       20-Aug-2015.) $)
    odrngle $p |- ( .<_ e. V -> .<_ = ( le ` W ) ) $=
      ( cple c1 c2 cdc cop odrngstr pleid cnx cfv csn ctp cts cds snsstp2 cmulr
      cbs cplusg cun ssun2 sseqtrri sstri strfv ) FHJGKKLMNABCDEFHIOPQJRFNZSQUA
      RENZULQUBRBNZTZHUMULUNUCUOQUERANQUFRCNQUDRDNTZUOUGHUOUPUHIUIUJUK $.

    $( The metric of an ordered metric ring.  (Contributed by Mario Carneiro,
       20-Aug-2015.) $)
    odrngds $p |- ( D e. V -> D = ( dist ` W ) ) $=
      ( cds c1 c2 cdc cop odrngstr dsid cnx cfv csn ctp cts cple snsstp3 cplusg
      cbs cmulr cun ssun2 sseqtrri sstri strfv ) BHJGKKLMNABCDEFHIOPQJRBNZSQUAR
      ENZQUBRFNZULTZHUMUNULUCUOQUERANQUDRCNQUFRDNTZUOUGHUOUPUHIUIUJUK $.
  $}

  ${
    ressds.1 $e |- H = ( G |`s A ) $.
    ressds.2 $e |- D = ( dist ` G ) $.
    $( ` dist ` is unaffected by restriction.  (Contributed by Mario Carneiro,
       26-Aug-2015.) $)
    ressds $p |- ( A e. V -> D = ( dist ` H ) ) $=
      ( cds dsid dsndxnbasendx resseqnbas ) ABDHECFGIJK $.
  $}

  $( Index value of the ~ df-hom slot.  (Contributed by Mario Carneiro,
     7-Jan-2017.)  (New usage is discouraged.) $)
  homndx $p |- ( Hom ` ndx ) = ; 1 4 $=
    ( chom c1 c4 cdc df-hom 1nn0 4nn decnncl ndxarg ) ABCDEBCFGHI $.

  $( Utility theorem: index-independent form of ~ df-hom .  (Contributed by
     Mario Carneiro, 7-Jan-2017.) $)
  homid $p |- Hom = Slot ( Hom ` ndx ) $=
    ( chom c1 c4 cdc df-hom 1nn0 4nn decnncl ndxid ) ABCDEBCFGHI $.

  $( Index value of the ~ df-cco slot.  (Contributed by Mario Carneiro,
     7-Jan-2017.)  (New usage is discouraged.) $)
  ccondx $p |- ( comp ` ndx ) = ; 1 5 $=
    ( cco c1 c5 cdc df-cco 1nn0 5nn decnncl ndxarg ) ABCDEBCFGHI $.

  $( Utility theorem: index-independent form of ~ df-cco .  (Contributed by
     Mario Carneiro, 7-Jan-2017.) $)
  ccoid $p |- comp = Slot ( comp ` ndx ) $=
    ( cco c1 c5 cdc df-cco 1nn0 5nn decnncl ndxid ) ABCDEBCFGHI $.

  $( The slots ` Base ` , ` Hom ` and ` comp ` are different.  (Contributed by
     AV, 5-Mar-2020.)  (Proof shortened by AV, 28-Oct-2024.) $)
  slotsbhcdif $p |- ( ( Base ` ndx ) =/= ( Hom ` ndx )
                   /\ ( Base ` ndx ) =/= ( comp ` ndx )
                   /\ ( Hom ` ndx ) =/= ( comp ` ndx ) ) $=
    ( cnx cbs cfv wne c1 basendx c4 cdc 1re 1nn 4nn0 1lt10 declti ltneii homndx
    1nn0 neeqtrri eqnetri c5 ccondx chom cco 5nn0 deccl nn0rei 5nn 4lt5 3pm3.2i
    declt ) ABCZAUACZDUJAUBCZDUKULDUJEUKFEEGHZUKEUMIEGEJKPLMNOQRUJEULFEESHZULEU
    NIESEJUCPLMNTQRUKUMULOUMUNULUMUNUMEGPKUDUEEGSPKUFUGUINTQRUH $.

  $( The index of the slot for the "less than or equal to" ordering is not the
     index of other slots.  Formerly part of proof for ~ prstcleval .
     (Contributed by AV, 12-Nov-2024.) $)
  slotsdifplendx2 $p |- ( ( le ` ndx ) =/= ( comp ` ndx )
                       /\ ( le ` ndx ) =/= ( Hom ` ndx ) ) $=
    ( cnx cple cfv cco wne chom c1 cc0 cdc c5 10re 1nn0 5nn declt ltneii plendx
    0nn0 neeq12i mpbir c4 5pos ccondx 4nn 4pos homndx pm3.2i ) ABCZADCZEZUGAFCZ
    EZUIGHIZGJIZEULUMKGHJLQMUANOUGULUHUMPUBRSUKULGTIZEULUNKGHTLQUCUDNOUGULUJUNP
    UERSUF $.

  $( The index of the slot for the orthocomplementation is not the index of
     other slots.  Formerly part of proof for ~ prstcocval .  (Contributed by
     AV, 12-Nov-2024.) $)
  slotsdifocndx $p |- ( ( oc ` ndx ) =/= ( comp ` ndx )
                     /\ ( oc ` ndx ) =/= ( Hom ` ndx ) ) $=
    ( cnx coc cfv cco wne chom c1 cdc c5 1nn0 1nn decnncl nnrei 5nn declt ocndx
    ltneii neeq12i mpbir c4 1lt5 ccondx 4nn 1lt4 homndx pm3.2i ) ABCZADCZEZUGAF
    CZEZUIGGHZGIHZEULUMULGGJKLMZGGIJJNUAOQUGULUHUMPUBRSUKULGTHZEULUOUNGGTJJUCUD
    OQUGULUJUOPUERSUF $.

  ${
    resshom.1 $e |- D = ( C |`s A ) $.
    ${
      resshom.2 $e |- H = ( Hom ` C ) $.
      $( ` Hom ` is unaffected by restriction.  (Contributed by Mario Carneiro,
         5-Jan-2017.) $)
      resshom $p |- ( A e. V -> H = ( Hom ` D ) ) $=
        ( chom homid cnx cbs cfv wne cco w3a slotsbhcdif simp1 ax-mp resseqnbas
        necomd ) ADCHEBFGIJKLZJHLZMZUAJNLZMZUBUDMZOZUBUAMPUGUAUBUCUEUFQTRS $.
    $}

    ${
      ressco.2 $e |- .x. = ( comp ` C ) $.
      $( ` comp ` is unaffected by restriction.  (Contributed by Mario
         Carneiro, 5-Jan-2017.) $)
      ressco $p |- ( A e. V -> .x. = ( comp ` D ) ) $=
        ( cco ccoid cnx cbs cfv chom wne w3a slotsbhcdif simp2 ax-mp resseqnbas
        necomd ) ADCHEBFGIJKLZJMLZNZUAJHLZNZUBUDNZOZUDUANPUGUAUDUCUEUFQTRS $.
    $}
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Definition of the structure product
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c |`t $. $( Function returning a subspace topology. $)
  $c TopOpen $.

  $( Extend class notation with the function returning a subspace topology. $)
  crest $a class |`t $.

  $( Extend class notation with the topology extractor function. $)
  ctopn $a class TopOpen $.

  ${
    $d j x y $.
    $( Function returning the subspace topology induced by the topology ` y `
       and the set ` x ` .  (Contributed by FL, 20-Sep-2010.)  (Revised by
       Mario Carneiro, 1-May-2015.) $)
    df-rest $a |- |`t = ( j e. _V , x e. _V |->
      ran ( y e. j |-> ( y i^i x ) ) ) $.

    $( Define the topology extractor function.  This differs from ~ df-tset
       when a structure has been restricted using ~ df-ress ; in this case the
       ` TopSet ` component will still have a topology over the larger set, and
       this function fixes this by restricting the topology as well.
       (Contributed by Mario Carneiro, 13-Aug-2015.) $)
    df-topn $a |- TopOpen = ( w e. _V |->
      ( ( TopSet ` w ) |`t ( Base ` w ) ) ) $.

    $( The subspace topology operator is a function on pairs.  (Contributed by
       Mario Carneiro, 1-May-2015.) $)
    restfn $p |- |`t Fn ( _V X. _V ) $=
      ( vj vx vy cvv cv cin cmpt crn crest df-rest vex mptex rnex fnmpoi ) ABDD
      CAEZCEBEFZGZHIBCAJQCOPAKLMN $.

    $( The topology extractor function is a function on the universe.
       (Contributed by Mario Carneiro, 13-Aug-2015.) $)
    topnfn $p |- TopOpen Fn _V $=
      ( vw cvv cv cts cfv cbs crest co ctopn ovex df-topn fnmpti ) ABACZDEZMFEZ
      GHINOGJAKL $.
  $}

  ${
    $d j x y A $.  $d x B $.  $d j x y J $.  $d x S $.
    $( The subspace topology induced by the topology ` J ` on the set ` A ` .
       (Contributed by FL, 20-Sep-2010.)  (Revised by Mario Carneiro,
       1-May-2015.) $)
    restval $p |- ( ( J e. V /\ A e. W )
       -> ( J |`t A ) = ran ( x e. J |-> ( x i^i A ) ) ) $=
      ( vj vy wcel cvv crest co cv cin cmpt crn wceq elex mptexg rnexg syl wa
      adantr simpl simpr ineq2d mpteq12dv rneqd df-rest ovmpoga mpd3an3 syl2an
      ) CDHCIHZBIHZCBJKACALZBMZNZOZPZBEHCDQBEQULUMUQIHZURULUSUMULUPIHUSACUOIRUP
      ISTUBFGCBIIAFLZUNGLZMZNZOUQJIUTCPZVABPZUAZVCUPVFAUTVBCUOVDVEUCVFVABUNVDVE
      UDUEUFUGGAFUHUIUJUK $.

    $( The predicate "is an open set of a subspace topology".  (Contributed by
       FL, 5-Jan-2009.)  (Revised by Mario Carneiro, 15-Dec-2013.) $)
    elrest $p |- ( ( J e. V /\ B e. W ) ->
      ( A e. ( J |`t B ) <-> E. x e. J A = ( x i^i B ) ) ) $=
      ( wcel wa crest co cv cin cmpt crn wceq wrex restval eleq2d eqid vex
      inex1 elrnmpti bitrdi ) DEGCFGHZBDCIJZGBADAKZCLZMZNZGBUGOADPUDUEUIBACDEFQ
      RADUGBUHUHSUFCATUAUBUC $.

    $( Sufficient condition for being an open set in a subspace.  (Contributed
       by Jeff Hankins, 11-Jul-2009.)  (Revised by Mario Carneiro,
       15-Dec-2013.) $)
    elrestr $p |- ( ( J e. V /\ S e. W /\ A e. J ) ->
                  ( A i^i S ) e. ( J |`t S ) ) $=
      ( vx wcel cin crest co wa wceq wrex ineq1 rspceeqv mpan2 elrest imbitrrid
      cv eqid 3impia ) CDGZBEGZACGZABHZCBIJGZUDUFUBUCKUEFSZBHZLFCMZUDUEUELUIUET
      FACUHUEUEUGABNOPFUEBCDEQRUA $.

    $( Value of the structure restriction when the topology input is empty.
       (Contributed by Mario Carneiro, 13-Aug-2015.) $)
    0rest $p |- ( (/) |`t A ) = (/) $=
      ( vx cvv wcel c0 crest co wceq cv cin cmpt crn 0ex restval mpan rneqi rn0
      mpt0 eqtri wrel eqtrdi cdm relxp restfn fndmi releqi mpbir ovprc2 pm2.61i
      cxp ) ACDZEAFGZEHUKULBEBIAJZKZLZEECDUKULUOHMBAECCNOUOELEUNEBUMRPQSUAEAFFU
      BZTCCUJZTCCUCUPUQUQFUDUEUFUGUHUI $.
  $}

  ${
    $d f x y z A $.  $d f x y z J $.  $d x V $.
    $( The subspace topology over a subset of the base set is the original
       topology.  (Contributed by Mario Carneiro, 13-Aug-2015.) $)
    restid2 $p |- ( ( A e. V /\ J C_ ~P A ) -> ( J |`t A ) = J ) $=
      ( vx wcel cpw wss wa crest co cv cin cmpt crn cvv wceq pwexg adantr simpr
      ssexd simpl restval cid cres sselda elpwid dfss2 sylib mpteq2dva mptresid
      syl2anc eqtr4di rneqd rnresi eqtrdi eqtrd ) ACEZBAFZGZHZBAIJZDBDKZALZMZNZ
      BUTBOEUQVAVEPUTBUROUQUROEUSACQRUQUSSZTUQUSUADABOCUBUKUTVEUCBUDZNBUTVDVGUT
      VDDBVBMVGUTDBVCVBUTVBBEHZVBAGVCVBPVHVBAUTBURVBVFUEUFVBAUGUHUIDBUJULUMBUNU
      OUP $.

    $( The subspace topology is a collection of subsets of the restriction set.
       (Contributed by Mario Carneiro, 13-Aug-2015.) $)
    restsspw $p |- ( J |`t A ) C_ ~P A $=
      ( vx vy crest co cpw cv wcel wss cin wceq wrex cvv wa wb c0 n0i cxp syl
      wfn cdm restfn fndm ax-mp ndmov nsyl2 elrest inss2 sseq1 mpbiri rexlimivw
      ibi velpw sylibr ssriv ) CBAEFZAGZCHZUQIZUSAJZUSURIUTUSDHZAKZLZDBMZVAUTVE
      UTBNIANIOZUTVEPUTUQQLVFUQUSRBANEENNSZUAEUBVGLUCVGEUDUEUFUGDUSABNNUHTUMVDV
      ADBVDVAVCAJVBAUIUSVCAUJUKULTCAUNUOUP $.

    $( The finite intersections operator commutes with restriction.
       (Contributed by Mario Carneiro, 30-Aug-2015.) $)
    firest $p |- ( fi ` ( J |`t A ) ) = ( ( fi ` J ) |`t A ) $=
      ( vy vf vz cvv wcel wa crest cfi cfv wceq cv cfn cin c0 wrex wb wral syl
      vx co cint cpw csn cdif elfi2 ax-mp wf wex eldifi adantl elin2d wss elfpw
      ovex simplbi sseld elrest adantr sylibd ralrimiv ineq1 eqeq2d ac6sfi ciin
      syl2anc wne eldifsni ad2antlr iinin1 fvex simpllr crn wfn fniinfv simplll
      ffn simpr intrnfi eqeltrd elrestr mp3an2i intiin iineq2 eqtrid syl5ibrcom
      syl13anc eleq1d expimpd exlimdv mpd rexlimdva biimtrid sylancr wi eqtr4di
      eleq1 ineq1i ovexd 3expa ralrimiva ssralv eqeltrrd imbi1d sylbid rexlimdv
      sylc iinfi impbid eqrdv wn fi0 wrel relxp restfn fndmi releqi mpbir ovprc
      cdm fveq2d wo ianor fvprc oveq1d 0rest eqtrdi ovprc2 jaoi 3eqtr4a pm2.61i
      cxp sylbi ) BFGZAFGZHZBAIUBZJKZBJKZAIUBZLYQUAYSUUAYQUAMZYSGZUUBUUAGZUUCUU
      BCMZUCZLZCYRUDZNOZPUEZUFZQZYQUUDYRFGZUUCUULRBAIUPCUUBYRFUGUHYQUUGUUDCUUKY
      QUUEUUKGZHZUUDUUGUUFUUAGZUUOUUEBDMZUIZEMZUUSUUQKZAOZLZEUUESZHZDUJZUUPUUOU
      UENGZUUSUUEAOZLZCBQZEUUESUVEUUOUUHNUUEUUNUUEUUIGZYQUUEUUIUUJUKULZUMZUUOUV
      IEUUEUUOUUSUUEGUUSYRGZUVIUUOUUEYRUUSUUOUVJUUEYRUNZUVKUVJUVNUVFUUEYRUOUQTU
      RYQUVMUVIRUUNCUUSABFFUSUTVAVBUVHUVBECUUEBDUUEUUTLUVGUVAUUSUUEUUTAVCVDVEVG
      UUOUVDUUPDUUOUURUVCUUPUUOUURHZUUPUVCEUUEUVAVFZUUAGUVOUVPEUUEUUTVFZAOZUUAU
      VOUUEPVHZUVPUVRLUUNUVSYQUURUUEUUIPVIVJZEUUEAUUTVKTYTFGZUVOYPUVQYTGUVRUUAG
      BJVLZYOYPUUNUURVMUVOUVQUUQVNUCZYTUVOUUQUUEVOZUVQUWCLUURUWDUUOUUEBUUQVRULE
      UUEUUQVPTUVOYOUURUVSUVFUWCYTGYOYPUUNUURVQUUOUURVSUVTUUOUVFUURUVLUTUUEBUUQ
      FVTWHWAUVQAYTFFWBWCWAUVCUUFUVPUUAUVCUUFEUUEUUSVFZUVPEUUEWDZEUUEUUSUVAWEWF
      WIWGWJWKWLUUBUUFUUAWRWGWMWNYQUUDUUBUUSAOZLZEYTQZUUCYQUWAYPUUDUWIRUWBYOYPV
      SEUUBAYTFFUSWOYQUWHUUCEYTYQUUSYTGZUUSUUFLZCBUDZNOZUUJUFZQZUWHUUCWPZYOUWJU
      WORYPCUUSBFUGUTYQUWKUWPCUWNYQUUEUWNGZHZUWPUWKUUBUUFAOZLZUUCWPUWRUUCUWTUWS
      YSGUWREUUEUWGVFZUWSYSUWRUXAUWEAOZUWSUWRUVSUXAUXBLUWQUVSYQUUEUWMPVIULZEUUE
      AUUSVKTUUFUWEAUWFWSWQUWRUUMUWGYRGZEUUESZUVSUVFUXAYSGUWRBAIWTUWRUUEBUNZUXD
      EBSZUXEUWRUUEUWMGZUXFUWQUXHYQUUEUWMUUJUKULZUXHUXFUVFUUEBUOUQTYQUXGUWQYQUX
      DEBYOYPUUSBGUXDUUSABFFWBXAXBUTUXDEUUEBXCXHUXCUWRUWLNUUEUXIUMEUUEUWGYRFXIW
      HXDUUBUWSYSWRWGUWKUWHUWTUUCUWKUWGUWSUUBUUSUUFAVCVDXEWGWMXFXGXFXJXKYQXLZPJ
      KPYSUUAXMUXJYRPJBAIIYAZXNFFYMZXNFFXOUXKUXLUXLIXPXQXRXSZXTYBUXJYOXLZYPXLZY
      CUUAPLZYOYPYDUXNUXPUXOUXNUUAPAIUBPUXNYTPAIBJYEYFAYGYHYTAIUXMYIYJYNYKYL $.

    restid.1 $e |- X = U. J $.
    $( The subspace topology of the base set is the original topology.
       (Contributed by Jeff Hankins, 9-Jul-2009.)  (Revised by Mario Carneiro,
       13-Aug-2015.) $)
    restid $p |- ( J e. V -> ( J |`t X ) = J ) $=
      ( wcel cvv cpw wss crest wceq cuni uniexg eqeltrid eqimss2i sspwuni mpbir
      co restid2 sylancl ) ABEZCFEACGHZACIQAJTCAKZFDABLMUAUBCHCUBDNACOPCAFRS $.
  $}

  ${
    $d w B $.  $d w J $.  $d w W $.
    topnval.1 $e |- B = ( Base ` W ) $.
    topnval.2 $e |- J = ( TopSet ` W ) $.
    $( Value of the topology extractor function.  (Contributed by Mario
       Carneiro, 13-Aug-2015.) $)
    topnval $p |- ( J |`t B ) = ( TopOpen ` W ) $=
      ( vw cvv wcel crest co ctopn cfv wceq cv cts cbs fveq2 eqtr4di c0 fvprc
      oveq12d df-topn ovex fvmpt eqcomd wn 0rest eqtrid oveq1d 3eqtr4a pm2.61i
      ) CGHZBAIJZCKLZMULUNUMFCFNZOLZUOPLZIJUMGKUOCMZUPBUQAIURUPCOLZBUOCOQERURUQ
      CPLAUOCPQDRUAFUBBAIUCUDUEULUFZSAIJSUMUNAUGUTBSAIUTBUSSECOTUHUICKTUJUK $.

    $( Value of the topology extractor function when the topology is defined
       over the same set as the base.  (Contributed by Mario Carneiro,
       13-Aug-2015.) $)
    topnid $p |- ( J C_ ~P B -> J = ( TopOpen ` W ) ) $=
      ( cpw wss crest co ctopn cfv cvv wcel wceq cbs fvexi restid2 mpan topnval
      eqtr3di ) BAFGZBAHIZBCJKALMUAUBBNACODPABLQRABCDEST $.
  $}

  ${
    topnpropd.1 $e |- ( ph -> ( Base ` K ) = ( Base ` L ) ) $.
    topnpropd.2 $e |- ( ph -> ( TopSet ` K ) = ( TopSet ` L ) ) $.
    $( The topology extractor function depends only on the base and topology
       components.  (Contributed by NM, 18-Jul-2006.) $)
    topnpropd $p |- ( ph -> ( TopOpen ` K ) = ( TopOpen ` L ) ) $=
      ( cts cfv cbs crest co ctopn oveq12d eqid topnval 3eqtr3g ) ABFGZBHGZIJCF
      GZCHGZIJBKGCKGAPRQSIEDLQPBQMPMNSRCSMRMNO $.
  $}

  $c topGen $.
  $c Xt_ $.
  $c 0g $.
  $c gsum $.

  $( Extend class notation with a function that converts a basis to its
     corresponding topology. $)
  ctg $a class topGen $.

  $( Extend class notation with a function whose value is a product
     topology. $)
  cpt $a class Xt_ $.

  $( Extend class notation with group identity element. $)
  c0g $a class 0g $.

  $( Extend class notation to include finitely supported group sums. $)
  cgsu $a class gsum $.

  ${
    $d e f g m n o w x y $.
    $( Define group identity element.  Remark: this definition is required here
       because the symbol ` 0g ` is already used in ~ df-gsum .  The related
       theorems are provided later, see ~ grpidval .  (Contributed by NM,
       20-Aug-2011.) $)
    df-0g $a |- 0g = ( g e. _V |-> ( iota e ( e e. ( Base ` g ) /\
                  A. x e. ( Base ` g )
                  ( ( e ( +g ` g ) x ) = x /\ ( x ( +g ` g ) e ) = x ) ) ) ) $.

    $( Define a finite group sum (also called "iterated sum") of a structure.
       Given ` G gsum F ` where ` F : A --> ( Base `` G ) ` , the set of
       indices is ` A ` and the values are given by ` F ` at each index.  A
       group sum over a multiplicative group may be viewed as a product.  The
       definition is meaningful in different contexts, depending on the size of
       the index set ` A ` and each demanding different properties of ` G ` .

       1.  If ` A = (/) ` and ` G ` has an identity element, then the sum
       equals this identity.  See ~ gsum0 .

       2.  If ` A = ( M ... N ) ` and ` G ` is any magma, then the sum is the
       sum of the elements, evaluated left-to-right, i.e.,
       ` ( ( F `` 1 ) + ( F `` 2 ) ) + ( F `` 3 ) ` , etc.  See ~ gsumval2 and
       ~ gsumnunsn .

       3.  If ` A ` is a finite set (or is nonzero for finitely many indices)
       and ` G ` is a commutative monoid, then the sum adds up these elements
       in some order, which is then uniquely defined.  See ~ gsumval3 .

       4.  If ` A ` is an infinite set and ` G ` is a Hausdorff topological
       group, then there is a meaningful sum, but ` gsum ` cannot handle this
       case.  See ~ df-tsms .

       Remark: this definition is required here because the symbol ` gsum ` is
       already used in ~ df-prds and ~ df-imas .  The related theorems are
       provided later, see ~ gsumvalx .  (Contributed by FL, 5-Sep-2010.)
       (Revised by FL, 17-Oct-2011.)  (Revised by Mario Carneiro,
       7-Dec-2014.) $)
    df-gsum $a |- gsum = ( w e. _V , f e. _V |-> [_ { x e. ( Base ` w ) |
            A. y e. ( Base ` w )
            ( ( x ( +g ` w ) y ) = y /\ ( y ( +g ` w ) x ) = y ) } / o ]_
            if ( ran f C_ o , ( 0g ` w ) , if ( dom f e. ran ... ,
               ( iota x E. m E. n e. ( ZZ>= ` m ) ( dom f = ( m ... n ) /\
                 x = ( seq m ( ( +g ` w ) , f ) ` n ) ) ) , ( iota x E. g
     [. ( `' f " ( _V \ o ) ) / y ]. ( g : ( 1 ... ( # ` y ) ) -1-1-onto-> y /\
             x = ( seq 1 ( ( +g ` w ) , ( f o. g ) ) ` ( # ` y ) ) ) ) ) ) ) $.
  $}

  ${
    $d f g x y z $.
    $( Define a function that converts a basis to its corresponding topology.
       Equivalent to the definition of a topology generated by a basis in
       [Munkres] p. 78 (see ~ tgval2 ).  The first use of this definition is
       ~ tgval but the token is used in ~ df-pt .  See ~ tgval3 for an
       alternate expression for the value.  (Contributed by NM,
       16-Jul-2006.) $)
    df-topgen $a |- topGen = ( x e. _V |-> { y | y C_ U. ( x i^i ~P y ) } ) $.

    $( Define the product topology on a collection of topologies.  For
       convenience, it is defined on arbitrary collections of sets, expressed
       as a function from some index set to the subbases of each factor space.
       (Contributed by Mario Carneiro, 3-Feb-2015.) $)
    df-pt $a |- Xt_ = ( f e. _V |-> ( topGen ` { x | E. g ( ( g Fn dom f /\
      A. y e. dom f ( g ` y ) e. ( f ` y ) /\ E. z e. Fin A. y e. ( dom f \ z )
           ( g ` y ) = U. ( f ` y ) ) /\ x = X_ y e. dom f ( g ` y ) ) } ) ) $.
  $}

  $c Xs_ ^s $.

  $( The function constructing structure products. $)
  cprds $a class Xs_ $.

  $( The function constructing structure powers. $)
  cpws $a class ^s $.

  ${
    $d a c d e f g h s r x v $.
    $( Define a structure product.  This can be a product of groups, rings,
       modules, or ordered topological fields; any unused components will have
       garbage in them but this is usually not relevant for the purpose of
       inheriting the structures present in the factors.  (Contributed by
       Stefan O'Rear, 3-Jan-2015.)  (Revised by Thierry Arnoux, 15-Jun-2019.)
       (Revised by Zhi Wang, 18-Aug-2024.) $)
    df-prds $a |- Xs_ = ( s e. _V , r e. _V |->
      [_ X_ x e. dom r ( Base ` ( r ` x ) ) / v ]_
      [_ ( f e. v , g e. v |-> X_ x e. dom r
           ( ( f ` x ) ( Hom ` ( r ` x ) ) ( g ` x ) ) ) / h ]_
  ( ( { <. ( Base ` ndx ) , v >. ,
        <. ( +g ` ndx ) , ( f e. v , g e. v |-> ( x e. dom r |->
          ( ( f ` x ) ( +g ` ( r ` x ) ) ( g ` x ) ) ) ) >. ,
        <. ( .r ` ndx ) , ( f e. v , g e. v |-> ( x e. dom r |->
          ( ( f ` x ) ( .r ` ( r ` x ) ) ( g ` x ) ) ) ) >. } u.
      { <. ( Scalar ` ndx ) , s >. ,
        <. ( .s ` ndx ) , ( f e. ( Base ` s ) , g e. v |->
          ( x e. dom r |-> ( f ( .s ` ( r ` x ) ) ( g ` x ) ) ) ) >. ,
        <. ( .i ` ndx ) , ( f e. v , g e. v |-> ( s gsum ( x e. dom r |->
          ( ( f ` x ) ( .i ` ( r ` x ) ) ( g ` x ) ) ) ) ) >. } ) u.
    ( { <. ( TopSet ` ndx ) , ( Xt_ ` ( TopOpen o. r ) ) >. ,
        <. ( le ` ndx ) , { <. f , g >. | ( { f , g } C_ v /\
        A. x e. dom r ( f ` x ) ( le ` ( r ` x ) ) ( g ` x ) ) } >. ,
        <. ( dist ` ndx ) , ( f e. v , g e. v |-> sup (
         ( ran ( x e. dom r |-> ( ( f ` x ) ( dist ` ( r ` x ) ) ( g ` x ) ) )
           u. { 0 } ) , RR* , < ) ) >. } u.
      { <. ( Hom ` ndx ) , h >. ,
        <. ( comp ` ndx ) , ( a e. ( v X. v ) , c e. v |->
           ( d e. ( ( 2nd ` a ) h c ) , e e. ( h ` a ) |-> ( x e. dom r |->
             ( ( d ` x ) ( <. ( ( 1st ` a ) ` x ) , ( ( 2nd ` a ) ` x ) >.
               ( comp ` ( r ` x ) ) ( c ` x ) ) ( e ` x ) ) ) ) ) >. } ) ) ) $.

    $( The structure product is a well-behaved binary operator.  (Contributed
       by Stefan O'Rear, 7-Jan-2015.)  (Revised by Thierry Arnoux,
       15-Jun-2019.)  (Revised by Zhi Wang, 18-Aug-2024.) $)
    reldmprds $p |- Rel dom Xs_ $=
      ( vs vr vv vx vh vf vg va vc vd ve cv cfv cbs co cmpo cnx cop cmpt cun wa
      cvv cdm cixp chom cplusg cmulr ctp csca cvsca cip cgsu cts ctopn ccom cpt
      cple cpr wss wbr wral copab cds crn cc0 csn cxr clt csup cco cxp c2nd csb
      c1st cprds df-prds reldmmpo ) ABUBUBCDBLZUCZDLZVRMZNMUDEFGCLZWBDVSVTFLZMZ
      VTGLZMZWAUEMOUDPQNMWBRQUFMFGWBWBDVSWDWFWAUFMOSPRQUGMFGWBWBDVSWDWFWAUGMOSP
      RUHQUIMALZRQUJMFGWGNMWBDVSWCWFWAUJMOSPRQUKMFGWBWBWGDVSWDWFWAUKMOSULOPRUHT
      QUMMUNVRUOUPMRQUQMWCWEURWBUSWDWFWAUQMUTDVSVAUAFGVBRQVCMFGWBWBDVSWDWFWAVCM
      OSVDVEVFTVGVHVIPRUHQUEMELZRQVJMHIWBWBVKWBJKHLZVLMZILZWHOWIWHMDVSVTJLMVTKL
      MVTWIVNMMVTWJMRVTWKMWAVJMOOSPPRURTTVMVMVODCKFGEABHIJVPVQ $.
  $}

  ${
    $d r i $.
    $( Define a structure power, which is just a structure product where all
       the factors are the same.  (Contributed by Mario Carneiro,
       11-Jan-2015.) $)
    df-pws $a |-
        ^s = ( r e. _V , i e. _V |-> ( ( Scalar ` r ) Xs_ ( i X. { r } ) ) ) $.
  $}

  ${
    $d x R $.
    prdsbasex.b $e |- B = X_ x e. dom R ( Base ` ( R ` x ) ) $.
    $( Lemma for structure products.  (Contributed by Mario Carneiro,
       3-Jan-2015.) $)
    prdsbasex $p |- B e. _V $=
      ( cdm cv cfv cbs cixp cvv wcel ixpexg fvexd mprg eqeltri ) BACEZAFZCGZHGZ
      IZJDSJKTJKAPAPSJLQPKRHMNO $.
  $}

  ${
    imasvalstr.u $e |- U = ( ( { <. ( Base ` ndx ) , B >. ,
        <. ( +g ` ndx ) , .+ >. , <. ( .r ` ndx ) , .X. >. } u.
        { <. ( Scalar ` ndx ) , S >. , <. ( .s ` ndx ) , .x. >. ,
          <. ( .i ` ndx ) , ., >. } ) u.
        { <. ( TopSet ` ndx ) , O >. , <. ( le ` ndx ) , L >. ,
        <. ( dist ` ndx ) , D >. } ) $.
    $( An image structure value is a structure.  (Contributed by Stefan O'Rear,
       3-Jan-2015.)  (Revised by Mario Carneiro, 30-Apr-2015.)  (Revised by
       Thierry Arnoux, 16-Jun-2019.) $)
    imasvalstr $p |- U Struct <. 1 , ; 1 2 >. $=
      ( cnx cfv cop ctp cun c1 c2 cdc c9 cbs cplusg cmulr csca cip cts cple cds
      cvsca cstr c8 eqid ipsstr cc0 9nn tsetndx 9lt10 10nn plendx 1nn0 0nn0 2nn
      2pos declt decnncl dsndx strle3 8lt9 strleun eqbrtri ) GLUAMANLUBMCNLUCMF
      NOLUDMDNLUIMENLUEMHNOPZLUFMZJNLUGMZINLUHMZBNOZPQQRSZNUJKQUKTVPVKVOVKACDEF
      HVKULUMVLVMVNTQUNSVPJIBUOUPUQURUSQUNRUTVAVBVCVDQRUTVBVEVFVGVHVIVJ $.
  $}

  $( Structure product value is a structure.  (Contributed by Stefan O'Rear,
     3-Jan-2015.)  (Revised by Mario Carneiro, 30-Apr-2015.)  (Revised by
     Thierry Arnoux, 16-Jun-2019.) $)
  prdsvalstr $p |- ( ( { <. ( Base ` ndx ) , B >. ,
      <. ( +g ` ndx ) , .+ >. , <. ( .r ` ndx ) , .X. >. } u.
      { <. ( Scalar ` ndx ) , S >. , <. ( .s ` ndx ) , .x. >. ,
        <. ( .i ` ndx ) , ., >. } ) u.
    ( { <. ( TopSet ` ndx ) , O >. , <. ( le ` ndx ) , L >. ,
        <. ( dist ` ndx ) , D >. } u.
      { <. ( Hom ` ndx ) , H >. , <. ( comp ` ndx ) , .xb >. } ) )
      Struct <. 1 , ; 1 5 >. $=
    ( cnx cfv cop ctp cun c1 c5 c4 1nn0 cbs cplusg cmulr csca cvsca cip cts cds
    cple chom cco cpr cdc cstr unass c2 eqid imasvalstr 4nn decnncl homndx 4nn0
    5nn 4lt5 declt ccondx strle2 2nn0 2lt4 strleun eqbrtrri ) LUAMANLUBMCNLUCMG
    NOLUDMDNLUEMFNLUFMINOPZLUGMKNLUIMJNLUHMBNOZPZLUJMZHNLUKMZENULZPVLVMVQPPQQRU
    MZNUNVLVMVQUOQQUPUMQSUMZVRVNVQABCDFGVNIJKVNUQURVOVPVSVRHEQSTUSUTVAQSRTVBVCV
    DVEQRTVCUTVFVGQUPSTVHUSVIVEVJVK $.

  ${
    prdsbaslem.u $e |- ( ph -> U = ( ( { <. ( Base ` ndx ) , B >. ,
        <. ( +g ` ndx ) , .+ >. , <. ( .r ` ndx ) , .X. >. } u.
        { <. ( Scalar ` ndx ) , S >. , <. ( .s ` ndx ) , .x. >. ,
          <. ( .i ` ndx ) , ., >. } ) u.
      ( { <. ( TopSet ` ndx ) , O >. , <. ( le ` ndx ) , L >. ,
          <. ( dist ` ndx ) , D >. } u.
        { <. ( Hom ` ndx ) , H >. , <. ( comp ` ndx ) , .xb >. } ) ) ) $.
    prdsbaslem.1 $e |- A = ( E ` U ) $.
    prdsbaslem.2 $e |- E = Slot ( E ` ndx ) $.
    prdsbaslem.3 $e |- ( ph -> T e. V ) $.
    prdsbaslem.4 $e |- { <. ( E ` ndx ) , T >. } C_
      ( ( { <. ( Base ` ndx ) , B >. ,
        <. ( +g ` ndx ) , .+ >. , <. ( .r ` ndx ) , .X. >. } u.
        { <. ( Scalar ` ndx ) , S >. , <. ( .s ` ndx ) , .x. >. ,
          <. ( .i ` ndx ) , ., >. } ) u.
      ( { <. ( TopSet ` ndx ) , O >. , <. ( le ` ndx ) , L >. ,
          <. ( dist ` ndx ) , D >. } u.
        { <. ( Hom ` ndx ) , H >. , <. ( comp ` ndx ) , .xb >. } ) ) $.
    $( Lemma for ~ prdsbas and similar theorems.  (Contributed by Mario
       Carneiro, 7-Jan-2017.)  (Revised by Thierry Arnoux, 16-Jun-2019.)
       (Revised by AV, 12-Jul-2024.) $)
    prdsbaslem $p |- ( ph -> A = T ) $=
      ( cnx cbs cfv cop cplusg cmulr ctp csca cip cun cts cple cds chom cco cpr
      cvsca c1 c5 cdc prdsvalstr strfv3 ) ABHUCUDUECUFUCUGUEEUFUCUHUEJUFUIUCUJU
      EFUFUCUSUEIUFUCUKUENUFUIULUCUMUEPUFUCUNUEOUFUCUOUEDUFUIUCUPUEMUFUCUQUEGUF
      URULULKLQUTUTVAVBUFRCDEFGIJMNOPVCTUBUASVD $.
  $}

  ${
    $d r x $.  $d f g r $.  $d f g v $.
    $( Lemma for ~ prdsval .  (Contributed by Stefan O'Rear, 3-Jan-2015.)
       Extracted from the former proof of ~ prdsval , dependency on ~ df-hom
       removed.  (Revised by AV, 13-Oct-2024.) $)
    prdsvallem $p |- ( f e. v , g e. v |-> X_ x e. dom r ( ( f ` x )
                                     ( Hom ` ( r ` x ) ) ( g ` x ) ) ) e. _V $=
      ( cv cfv chom co cixp crn cuni cmap vex wss rnss uniss mp2b rnex uniex
      cdm cpw ovex pwex wcel cvv wral ovssunirn cnx homid fvssunirn sstri rgenw
      strfvss ss2ixp ax-mp dmex ixpconst sseqtri elpwi2 rgen2w mpoexw ) CDBFZVC
      AEFZUAZAFZCFGZVFDFGZVFVDGZHGZIZJZVDKZLZKZLZKZLZVEMIZUBZBNZWAVSVRVEMUCZUDV
      LVTUECDVCVCVLVSUFWBVLAVEVRJZVSVKVROZAVEUGVLWCOWDAVEVKVJKZLZVRVJVGVHUHVJVP
      OWEVQOWFVROVJVIKZLZVPVIHUIHGUJUNVIVNOWGVOOWHVPOVDVFUKVIVNPWGVOQRULVJVPPWE
      VQQRULUMAVEVKVRUOUPAVEVRVDENZUQVQVPVOVNVMVDWISTSTSTURUSUTVAVB $.
  $}

  ${
    $d h r s v .+ $.  $d h r s v .<_ $.  $d a c d e f g h r s v B $.
    $d a c d e h r s v H $.  $d a c d e f g h r s v x ph $.  $d h r s v D $.
    $d h r s v O $.  $d h r s v .X. $.  $d h r s v .xb $.  $d x I $.
    $d a c d e f g h r s v x R $.  $d a c d e f g h r s v x S $.
    $d h r s v .x. $.  $d h r s v ., $.
    prdsval.p $e |- P = ( S Xs_ R ) $.
    prdsval.k $e |- K = ( Base ` S ) $.
    prdsval.i $e |- ( ph -> dom R = I ) $.
    prdsval.b $e |- ( ph -> B = X_ x e. I ( Base ` ( R ` x ) ) ) $.
    prdsval.a $e |- ( ph -> .+ = ( f e. B , g e. B |-> ( x e. I |->
        ( ( f ` x ) ( +g ` ( R ` x ) ) ( g ` x ) ) ) ) ) $.
    prdsval.t $e |- ( ph -> .X. = ( f e. B , g e. B |-> ( x e. I |->
        ( ( f ` x ) ( .r ` ( R ` x ) ) ( g ` x ) ) ) ) ) $.
    prdsval.m $e |- ( ph -> .x. = ( f e. K , g e. B |-> ( x e. I |->
        ( f ( .s ` ( R ` x ) ) ( g ` x ) ) ) ) ) $.
    prdsval.j $e |- ( ph -> ., = ( f e. B , g e. B |-> ( S gsum
        ( x e. I |-> ( ( f ` x ) ( .i ` ( R ` x ) ) ( g ` x ) ) ) ) ) ) $.
    prdsval.o $e |- ( ph -> O = ( Xt_ ` ( TopOpen o. R ) ) ) $.
    prdsval.l $e |- ( ph -> .<_ = { <. f , g >. | ( { f , g } C_ B /\
        A. x e. I ( f ` x ) ( le ` ( R ` x ) ) ( g ` x ) ) } ) $.
    prdsval.d $e |- ( ph -> D = ( f e. B , g e. B |-> sup ( ( ran ( x e. I |->
   ( ( f ` x ) ( dist ` ( R ` x ) ) ( g ` x ) ) ) u. { 0 } ) , RR* , < ) ) ) $.
    prdsval.h $e |- ( ph -> H = ( f e. B , g e. B |-> X_ x e. I
           ( ( f ` x ) ( Hom ` ( R ` x ) ) ( g ` x ) ) ) ) $.
    prdsval.x $e |- ( ph -> .xb = ( a e. ( B X. B ) , c e. B |->
        ( d e. ( ( 2nd ` a ) H c ) , e e. ( H ` a ) |-> ( x e. I |->
          ( ( d ` x ) ( <. ( ( 1st ` a ) ` x ) , ( ( 2nd ` a ) ` x ) >.
            ( comp ` ( R ` x ) ) ( c ` x ) ) ( e ` x ) ) ) ) ) ) $.
    prdsval.s $e |- ( ph -> S e. W ) $.
    prdsval.r $e |- ( ph -> R e. Z ) $.
    $( Value of the structure product.  (Contributed by Stefan O'Rear,
       3-Jan-2015.)  (Revised by Mario Carneiro, 7-Jan-2017.)  (Revised by
       Thierry Arnoux, 16-Jun-2019.)  (Revised by Zhi Wang, 18-Aug-2024.) $)
    prdsval $p |- ( ph -> P = ( ( { <. ( Base ` ndx ) , B >. ,
        <. ( +g ` ndx ) , .+ >. , <. ( .r ` ndx ) , .X. >. } u.
        { <. ( Scalar ` ndx ) , S >. , <. ( .s ` ndx ) , .x. >. ,
          <. ( .i ` ndx ) , ., >. } ) u.
      ( { <. ( TopSet ` ndx ) , O >. , <. ( le ` ndx ) , .<_ >. ,
          <. ( dist ` ndx ) , D >. } u.
        { <. ( Hom ` ndx ) , H >. , <. ( comp ` ndx ) , .xb >. } ) ) ) $=
      ( vs vr vv vh cprds co cnx cbs cfv cop cplusg cmulr ctp cvsca cip cun cts
      csca cple cds chom cco cpr cvv cdm cixp cmpo cmpt cgsu ctopn ccom cpt wss
      cv wbr wral copab crn cc0 csn cxr clt csup cxp c2nd c1st csb wceq df-prds
      wa a1i ciun cmap wcel cuni rnex uniex baseid simpr fveq1d fveq2d ixpeq2dv
      vex eqtrd ixpeq1d adantr oveqd mpoeq123dv eqtr4d opeq2d mpteq12dv ad4antr
      ad2antrr tpeq123d simpllr uneq12d csbied2 elexd tpex unex fvssunirn uniss
      strfvss rnss mp2b sstri rgenw iunss mpbir ssexi ixpssmap2g ovex ssex mp1i
      3eqtr4d prdsvallem ad3antrrr simplr simp-4r eqtr4di oveq12d coeq2d sseq2d
      ax-mp dmeqd breqd raleqbidv anbi12d opabbidv rneqd uneq1d supeq1d sqxpeqd
      wb preq12d anasss prex ovmpod eqtrid ) AEHGVEVFVGVHVIZCVJZVGVKVIZFVJZVGVL
      VIZKVJZVMZVGVRVIZHVJZVGVNVIZJVJZVGVOVIZPVJZVMZVPZVGVQVIZTVJZVGVSVIZSVJZVG
      VTVIZDVJZVMZVGWAVIZOVJZVGWBVIZIVJZWCZVPZVPZUFAVAVBHGWDWDVCBVBWNZWEZBWNZUX
      IVIZVHVIZWFZVDMNVCWNZUXOBUXJUXKMWNZVIZUXKNWNZVIZUXLWAVIZVFZWFZWGZUVTUXOVJ
      ZUWBMNUXOUXOBUXJUXQUXSUXLVKVIZVFZWHZWGZVJZUWDMNUXOUXOBUXJUXQUXSUXLVLVIZVF
      ZWHZWGZVJZVMZUWGVAWNZVJZUWIMNUYPVHVIZUXOBUXJUXPUXSUXLVNVIZVFZWHZWGZVJZUWK
      MNUXOUXOUYPBUXJUXQUXSUXLVOVIZVFZWHZWIVFZWGZVJZVMZVPZUWOWJUXIWKZWLVIZVJZUW
      QUXPUXRWCZUXOWMZUXQUXSUXLVSVIZWOZBUXJWPZXJZMNWQZVJZUWSMNUXOUXOBUXJUXQUXSU
      XLVTVIZVFZWHZWRZWSWTZVPZXAXBXCZWGZVJZVMZUXBVDWNZVJZUXDUCUDUXOUXOXDZUXOUEL
      UCWNZXEVIZUDWNZVVMVFZVVPVVMVIZBUXJUXKUEWNVIZUXKLWNVIZUXKVVPXFVIVIUXKVVQVI
      VJZUXKVVRVIZUXLWBVIZVFZVFZWHZWGZWGZVJZWCZVPZVPZXGZXGZUXHVEWDVEVAVBWDWDVWP
      WGXHABVCLMNVDVAVBUCUDUEXIXKAUYPHXHZUXIGXHZVWPUXHXHAVWQXJZVWRXJZVCUXNCVWOU
      XHWDUXNBUXJUXMXLZUXJXMVFZWMZUXNWDXNVWTVXAWDXNVXCVXAUXIWRZXOZWRZXOZVXFVXEV
      XDUXIVBYCXPXQXPXQVXAVXGWMUXMVXGWMZBUXJWPVXHBUXJUXMUXLWRZXOZVXGUXLVHUVTXRU
      UCUXLVXEWMVXIVXFWMVXJVXGWMUXIUXKUUAUXLVXEUUDVXIVXFUUBUUEUUFUUGBUXJUXMVXGU
      UHUUIUUJBUXJUXMWDUUKUVDUXNVXBVXAUXJXMUULUUMUUNVWTBQUXMWFBQUXKGVIZVHVIZWFZ
      UXNCVWTBQUXMVXLVWTUXLVXKVHVWTUXKUXIGVWSVWRXSZXTZYAYBVWTBUXJQUXMVWTUXJGWEZ
      QVWTUXIGVXNUVEAVXPQXHVWQVWRUHYMYDZYEACVXMXHVWQVWRUIYMUUOVWTUXOCXHZXJZVDUY
      COVWNUXHWDUYCWDXNVXSBVCMNVBUUPXKVXSUYCMNCCBQUXQUXSVXKWAVIZVFZWFZWGZOVXSMN
      UXOUXOUYBCCVYBVWTVXRXSZVYDVXSUYBBQUYAWFZVYBVXSBUXJQUYAVWTUXJQXHVXRVXQYFYE
      VWTVYEVYBXHVXRVWTBQUYAVYAVWTUXTVXTUXQUXSVWTUXLVXKWAVXOYAYGYBYFYDYHAOVYCXH
      VWQVWRVXRUQUUQYIVXSVVMOXHZXJZVUKUWNVWMUXGVYGUYOUWFVUJUWMVYGUYDUWAUYIUWCUY
      NUWEVYGUXOCUVTVWTVXRVYFUURZYJVYGUYHFUWBVYGUYHMNCCBQUXQUXSVXKVKVIZVFZWHZWG
      ZFVXSUYHVYLXHVYFVXSMNUXOUXOUYGCCVYKVYDVYDVWTUYGVYKXHVXRVWTBUXJUYFQVYJVXQV
      WTUYEVYIUXQUXSVWTUXLVXKVKVXOYAYGYKYFYHYFAFVYLXHVWQVWRVXRVYFUJYLYIYJVYGUYM
      KUWDVYGUYMMNCCBQUXQUXSVXKVLVIZVFZWHZWGZKVXSUYMVYPXHVYFVXSMNUXOUXOUYLCCVYO
      VYDVYDVWTUYLVYOXHVXRVWTBUXJUYKQVYNVXQVWTUYJVYMUXQUXSVWTUXLVXKVLVXOYAYGYKY
      FYHYFAKVYPXHVWQVWRVXRVYFUKYLYIYJYNVYGUYQUWHVUCUWJVUIUWLVYGUYPHUWGAVWQVWRV
      XRVYFUUSYJVYGVUBJUWIVYGVUBMNRCBQUXPUXSVXKVNVIZVFZWHZWGZJVXSVUBVYTXHVYFVXS
      MNUYRUXOVUARCVYSVXSUYRHVHVIRVXSUYPHVHAVWQVWRVXRYOZYAUGUUTVYDVWTVUAVYSXHVX
      RVWTBUXJUYTQVYRVXQVWTUYSVYQUXPUXSVWTUXLVXKVNVXOYAYGYKYFYHYFAJVYTXHVWQVWRV
      XRVYFULYLYIYJVYGVUHPUWKVYGVUHMNCCHBQUXQUXSVXKVOVIZVFZWHZWIVFZWGZPVXSVUHWU
      FXHVYFVXSMNUXOUXOVUGCCWUEVYDVYDVXSUYPHVUFWUDWIWUAVWTVUFWUDXHVXRVWTBUXJVUE
      QWUCVXQVWTVUDWUBUXQUXSVWTUXLVXKVOVXOYAYGYKYFUVAYHYFAPWUFXHVWQVWRVXRVYFUMY
      LYIYJYNYPVYGVVLUXAVWLUXFVYGVUNUWPVVBUWRVVKUWTVYGVUMTUWOVYGVUMWJGWKZWLVIZT
      VYGVULWUGWLVYGUXIGWJVWSVWRVXRVYFYOUVBYAATWUHXHVWQVWRVXRVYFUNYLYIYJVYGVVAS
      UWQVYGVVAVUOCWMZUXQUXSVXKVSVIZWOZBQWPZXJZMNWQZSVXSVVAWUNXHVYFVXSVUTWUMMNV
      XSVUPWUIVUSWULVXSUXOCVUOVYDUVCVWTVUSWULUVNVXRVWTVURWUKBUXJQVXQVWTVUQWUJUX
      QUXSVWTUXLVXKVSVXOYAUVFUVGYFUVHUVIYFASWUNXHVWQVWRVXRVYFUOYLYIYJVYGVVJDUWS
      VYGVVJMNCCBQUXQUXSVXKVTVIZVFZWHZWRZVVGVPZXAXBXCZWGZDVXSVVJWVAXHVYFVXSMNUX
      OUXOVVICCWUTVYDVYDVXSXAVVHWUSXBVXSVVFWURVVGVXSVVEWUQVWTVVEWUQXHVXRVWTBUXJ
      VVDQWUPVXQVWTVVCWUOUXQUXSVWTUXLVXKVTVXOYAYGYKYFUVJUVKUVLYHYFADWVAXHVWQVWR
      VXRVYFUPYLYIYJYNVYGVVNUXCVWKUXEVYGVVMOUXBVXSVYFXSZYJVYGVWJIUXDVYGVWJUCUDC
      CXDZCUELVVQVVROVFZVVPOVIZBQVWAVWBVWCVWDVXKWBVIZVFZVFZWHZWGZWGZIVYGUCUDVVO
      UXOVWIWVCCWVJVYGUXOCVYHUVMVYHVYGUELVVSVVTVWHWVDWVEWVIVYGVVMOVVQVVRWVBYGVY
      GVVPVVMOWVBXTVWTVWHWVIXHVXRVYFVWTBUXJVWGQWVHVXQVWTVWFWVGVWAVWBVWTVWEWVFVW
      CVWDVWTUXLVXKWBVXOYAYGYGYKYMYHYHAIWVKXHVWQVWRVXRVYFURYLYIYJUVOYPYPYQYQUVP
      AHUAUSYRAGUBUTYRUXHWDXNAUWNUXGUWFUWMUWAUWCUWEYSUWHUWJUWLYSYTUXAUXFUWPUWRU
      WTYSUXCUXEUVQYTYTXKUVRUVS $.
  $}

  ${
    $d a c d e f g x B $.  $d a c d e H $.  $d f g K $.  $d a c d e f g x ph $.
    $d a c d e f g w x y z I $.  $d f g x P $.  $d a c d e f g w x y z R $.
    $d a c d e f g x S $.
    prdsbas.p $e |- P = ( S Xs_ R ) $.
    prdsbas.s $e |- ( ph -> S e. V ) $.
    prdsbas.r $e |- ( ph -> R e. W ) $.
    $( Scalar ring of a structure product.  (Contributed by Stefan O'Rear,
       5-Jan-2015.)  (Revised by Mario Carneiro, 15-Aug-2015.)  (Revised by
       Thierry Arnoux, 16-Jun-2019.)  (Revised by Zhi Wang, 18-Aug-2024.) $)
    prdssca $p |- ( ph -> S = ( Scalar ` P ) ) $=
      ( vx vf vg cfv cv co cmpt cmpo cop eqidd cnx va vc vd ve csca cdm cbs cds
      cixp crn cc0 csn cun cxr clt csup cplusg cxp c2nd chom c1st cco cvsca cip
      cmulr cgsu cpr wss cple wbr wral wa copab ctopn ccom cpt eqid prdsval ctp
      scaid cts snsstp1 ssun2 sstri ssun1 prdsbaslem eqcomd ) ABUEMZDAWHJCUFZJN
      ZCMZUGMUIZKLWLWLJWIWJKNZMZWJLNZMZWKUHMOPUJUKULUMUNUOUPQZKLWLWLJWIWNWPWKUQ
      MOPQZDUAUBWLWLURWLUCUDUANZUSMZUBNZKLWLWLJWIWNWPWKUTMOUIQZOWSXBMJWIWJUCNMW
      JUDNMWJWSVAMMWJWTMRWJXAMWKVBMOOPQQZDKLDUGMZWLJWIWMWPWKVCMOPQZKLWLWLJWIWNW
      PWKVEMOPQZBUEXBKLWLWLDJWIWNWPWKVDMOPVFOQZWMWOVGWLVHWNWPWKVIMVJJWIVKVLKLVM
      ZVNCVOVPMZEAJWLWQBWRCDXCXEXFUDKLXBXGWIXDXHXIEFUAUBUCGXDVQAWISAWLSAWRSAXFS
      AXESAXGSAXISAXHSAWQSAXBSAXCSHIVRWHVQVTHTUEMDRZULZTUGMWLRTUQMWRRTVEMXFRVSZ
      XJTVCMXERZTVDMXGRZVSZUMZXPTWAMXIRTVIMXHRTUHMWQRVSTUTMXBRTVBMXCRVGUMZUMXKX
      OXPXJXMXNWBXOXLWCWDXPXQWEWDWFWG $.

    prdsbas.b $e |- B = ( Base ` P ) $.
    prdsbas.i $e |- ( ph -> dom R = I ) $.
    $( Base set of a structure product.  (Contributed by Stefan O'Rear,
       3-Jan-2015.)  (Revised by Mario Carneiro, 15-Aug-2015.)  (Revised by
       Thierry Arnoux, 16-Jun-2019.)  (Revised by Zhi Wang, 18-Aug-2024.) $)
    prdsbas $p |- ( ph -> B = X_ x e. I ( Base ` ( R ` x ) ) ) $=
      ( cfv co cop cvv eqidd cnx vf vg va vc vd ve cv cbs cixp cds cmpt crn cc0
      csn cun cxr clt csup cmpo cxp c2nd chom c1st cco cvsca cmulr cip cgsu cpr
      cplusg wss cple wbr wral wa copab ctopn ccom cpt eqid prdsval baseid ciun
      wcel cmap cuni strfvss fvssunirn rnss uniss sstri rgenw iunss mpbir rnexg
      mp2b uniexg 3syl ssexg sylancr ixpssmap2g ovex ssex ctp cts snsstp1 ssun1
      csca prdsbaslem ) ACBGBUGZEOZUHOZUIZUAUBXMXMBGXJUAUGZOZXJUBUGZOZXKUJOPUKU
      LUMUNUOUPUQURUSZUAUBXMXMBGXOXQXKVJOPUKUSZFUCUDXMXMUTXMUEUFUCUGZVAOZUDUGZU
      AUBXMXMBGXOXQXKVBOPUIUSZPXTYCOBGXJUEUGOXJUFUGOXJXTVCOOXJYAOQXJYBOXKVDOPPU
      KUSUSZXMUAUBFUHOZXMBGXNXQXKVEOPUKUSZUAUBXMXMBGXOXQXKVFOPUKUSZDUHYCUAUBXMX
      MFBGXOXQXKVGOPUKVHPUSZXNXPVIXMVKXOXQXKVLOVMBGVNVOUAUBVPZVQEVRVSOZRABXMXRD
      XSEFYDYFYGUFUAUBYCYHGYEYIYJHIUCUDUEJYEVTNAXMSAXSSAYGSAYFSAYHSAYJSAYISAXRS
      AYCSAYDSKLWAMWBABGXLWCZRWDZXMYKGWEPZVKXMRWDAYKEULZWFZULZWFZVKZYQRWDZYLYRX
      LYQVKZBGVNYTBGXLXKULZWFZYQXKUHTUHOZWBWGXKYOVKUUAYPVKUUBYQVKEXJWHXKYOWIUUA
      YPWJWPWKWLBGXLYQWMWNAYORWDZYPRWDYSAEIWDYNRWDUUDLEIWOYNRWQWRYORWOYPRWQWRYK
      YQRWSWTBGXLRXAXMYMYKGWEXBXCWRUUCXMQZUNZUUETVJOXSQZTVFOYGQZXDZTXHOFQTVEOYF
      QTVGOYHQXDZUOZUUKTXEOYJQTVLOYIQTUJOXRQXDTVBOYCQTVDOYDQVIUOZUOUUFUUIUUKUUE
      UUGUUHXFUUIUUJXGWKUUKUULXGWKXI $.

    ${
      prdsplusg.b $e |- .+ = ( +g ` P ) $.
      $( Addition in a structure product.  (Contributed by Stefan O'Rear,
         3-Jan-2015.)  (Revised by Mario Carneiro, 15-Aug-2015.)  (Revised by
         Thierry Arnoux, 16-Jun-2019.)  (Revised by Zhi Wang, 18-Aug-2024.) $)
      prdsplusg $p |- ( ph -> .+ = ( f e. B , g e. B |-> ( x e. I |->
            ( ( f ` x ) ( +g ` ( R ` x ) ) ( g ` x ) ) ) ) ) $=
        ( cfv cvv va vc vd ve cds cmpt crn cc0 csn cun cxr clt csup cmpo cplusg
        cv co cxp c2nd chom cixp c1st cop cco cbs cvsca cmulr cip cgsu cpr cple
        wss wbr wral wa copab ctopn ccom cpt eqid prdsbas eqidd prdsval plusgid
        cuni cpw cmap wf wcel ovssunirn strfvss fvssunirn rnss uniss mp2b sstri
        cnx ovex elpw mpbir a1i fmpttd rnexg 3syl pwexg 4syl cdm dmexd eqeltrrd
        uniexg elmapd ralrimivw fmpo sylib fvexi xpex fex2 mp3an23 syl ctp csca
        mpbird cts snsstp2 ssun1 prdsbaslem ) AECHICCBJBUPZHUPZSZYGIUPZSZYGFSZU
        ESUQUFUGUHUIUJUKULUMUNZHICCBJYIYKYLUOSZUQZUFZUNZGUAUBCCURZCUCUDUAUPZUSS
        ZUBUPZHICCBJYIYKYLUTSUQVAUNZUQYSUUBSBJYGUCUPSYGUDUPSYGYSVBSSYGYTSVCYGUU
        ASYLVDSUQUQUFUNUNZYQHIGVESZCBJYHYKYLVFSUQUFUNZHICCBJYIYKYLVGSUQUFUNZDUO
        UUBHICCGBJYIYKYLVHSUQUFVIUQUNZYHYJVJCVLYIYKYLVKSVMBJVNVOHIVPZVQFVRVSSZT
        ABCYMDYQFGUUCUUEUUFUDHIUUBUUGJUUDUUHUUIKLUAUBUCMUUDVTQABCDFGJKLMNOPQWAA
        YQWBAUUFWBAUUEWBAUUGWBAUUIWBAUUHWBAYMWBAUUBWBAUUCWBNOWCRWDAYRFUGZWEZUGZ
        WEZUGZWEZWFZJWGUQZYQWHZYQTWIZAYPUUQWIZICVNZHCVNUURAUVAHCAUUTICAUUTJUUPY
        PWHABJYOUUPYOUUPWIZAYGJWIVOUVBYOUUOVLYOYNUGZWEZUUOYNYIYKWJYNUUMVLUVCUUN
        VLUVDUUOVLYNYLUGZWEZUUMYLUOWQUOSZWDWKYLUUKVLUVEUULVLUVFUUMVLFYGWLYLUUKW
        MUVEUULWNWOWPYNUUMWMUVCUUNWNWOWPYOUUOYIYKYNWRWSWTXAXBAUUPJYPTTAUUMTWIZU
        UNTWIUUOTWIUUPTWIAUUKTWIZUULTWIUVHAFLWIUUJTWIUVIOFLXCUUJTXJXDUUKTXCUULT
        XJXDUUMTXCUUNTXJUUOTXEXFAFXGJTQAFLOXHXIXKYBXLXLHICCYPUUQYQYQVTXMXNUURYR
        TWIUUQTWIUUSCCCDVEPXOZUVJXPUUPJWGWRYRUUQYQTTXQXRXSUVGYQVCZUIZWQVESCVCZU
        VKWQVGSUUFVCZXTZWQYASGVCWQVFSUUEVCWQVHSUUGVCXTZUJZUVQWQYCSUUIVCWQVKSUUH
        VCWQUESYMVCXTWQUTSUUBVCWQVDSUUCVCVJUJZUJUVLUVOUVQUVMUVKUVNYDUVOUVPYEWPU
        VQUVRYEWPYF $.
    $}

    ${
      prdsmulr.t $e |- .x. = ( .r ` P ) $.
      $( Multiplication in a structure product.  (Contributed by Mario
         Carneiro, 11-Jan-2015.)  (Revised by Mario Carneiro, 15-Aug-2015.)
         (Revised by Thierry Arnoux, 16-Jun-2019.)  (Revised by Zhi Wang,
         18-Aug-2024.) $)
      prdsmulr $p |- ( ph -> .x. = ( f e. B , g e. B |-> ( x e. I |->
            ( ( f ` x ) ( .r ` ( R ` x ) ) ( g ` x ) ) ) ) ) $=
        ( cfv cvv va vc vd ve cds cmpt crn cc0 csn cun cxr clt csup cmpo cplusg
        cv co cxp c2nd chom cixp c1st cop cco cmulr cbs cvsca cip cgsu cpr cple
        wss wbr wral wa copab ctopn ccom eqid prdsbas prdsplusg prdsval mulridx
        cpt eqidd cuni cpw cmap wcel ovssunirn cnx strfvss fvssunirn rnss uniss
        mp2b sstri ovex elpw mpbir a1i fmpttd rnexg uniexg 3syl pwexd cdm dmexd
        eqeltrrd elmapd mpbird ralrimivw fmpo sylib fvexi xpex fex2 mp3an23 syl
        wf ctp csca cts snsstp3 ssun1 prdsbaslem ) AGCHICCBJBUPZHUPZSZYGIUPZSZY
        GESZUESUQUFUGUHUIUJUKULUMUNZDUOSZFUAUBCCURZCUCUDUAUPZUSSZUBUPZHICCBJYIY
        KYLUTSUQVAUNZUQYPYSSBJYGUCUPSYGUDUPSYGYPVBSSYGYQSVCYGYRSYLVDSUQUQUFUNUN
        ZHICCBJYIYKYLVESZUQZUFZUNZHIFVFSZCBJYHYKYLVGSUQUFUNZUUDDVEYSHICCFBJYIYK
        YLVHSUQUFVIUQUNZYHYJVJCVLYIYKYLVKSVMBJVNVOHIVPZVQEVRWDSZTABCYMDYNEFYTUU
        FUUDUDHIYSUUGJUUEUUHUUIKLUAUBUCMUUEVSQABCDEFJKLMNOPQVTABCDYNEFHIJKLMNOP
        QYNVSWAAUUDWEAUUFWEAUUGWEAUUIWEAUUHWEAYMWEAYSWEAYTWENOWBRWCAYOEUGZWFZUG
        ZWFZUGZWFZWGZJWHUQZUUDXTZUUDTWIZAUUCUUQWIZICVNZHCVNUURAUVAHCAUUTICAUUTJ
        UUPUUCXTABJUUBUUPUUBUUPWIZAYGJWIVOUVBUUBUUOVLUUBUUAUGZWFZUUOUUAYIYKWJUU
        AUUMVLUVCUUNVLUVDUUOVLUUAYLUGZWFZUUMYLVEWKVESZWCWLYLUUKVLUVEUULVLUVFUUM
        VLEYGWMYLUUKWNUVEUULWOWPWQUUAUUMWNUVCUUNWOWPWQUUBUUOYIYKUUAWRWSWTXAXBAU
        UPJUUCTTAUUOTAUUMTWIZUUNTWIUUOTWIAUUKTWIZUULTWIUVHAELWIUUJTWIUVIOELXCUU
        JTXDXEUUKTXCUULTXDXEUUMTXCUUNTXDXEXFAEXGJTQAELOXHXIXJXKXLXLHICCUUCUUQUU
        DUUDVSXMXNUURYOTWIUUQTWIUUSCCCDVFPXOZUVJXPUUPJWHWRYOUUQUUDTTXQXRXSUVGUU
        DVCZUIZWKVFSCVCZWKUOSYNVCZUVKYAZWKYBSFVCWKVGSUUFVCWKVHSUUGVCYAZUJZUVQWK
        YCSUUIVCWKVKSUUHVCWKUESYMVCYAWKUTSYSVCWKVDSYTVCVJUJZUJUVLUVOUVQUVMUVNUV
        KYDUVOUVPYEWQUVQUVRYEWQYF $.
    $}

    ${
      prdsvsca.k $e |- K = ( Base ` S ) $.
      prdsvsca.m $e |- .x. = ( .s ` P ) $.
      $( Scalar multiplication in a structure product.  (Contributed by Stefan
         O'Rear, 5-Jan-2015.)  (Revised by Mario Carneiro, 15-Aug-2015.)
         (Revised by Thierry Arnoux, 16-Jun-2019.)  (Revised by Zhi Wang,
         18-Aug-2024.) $)
      prdsvsca $p |- ( ph -> .x. = ( f e. K , g e. B |-> ( x e. I |->
            ( f ( .s ` ( R ` x ) ) ( g ` x ) ) ) ) ) $=
        ( va vc vd ve cfv cds cmpt crn cc0 csn cun cxr clt csup cmpo cplusg cxp
        cv co c2nd chom cixp c1st cop cco cvsca cmulr cip cgsu cpr wss cple wbr
        wral copab ctopn ccom cpt prdsbas eqid prdsplusg prdsmulr eqidd prdsval
        wa cvv vscaid cuni cpw cmap wcel ovssunirn strfvss fvssunirn rnss uniss
        wf cnx mp2b sstri ovex elpw mpbir a1i fmpttd rnexg uniexg 3syl 4syl cdm
        pwexg dmexd eqeltrrd elmapd mpbird ralrimivw fmpo sylib fvexi xpex fex2
        cbs mp3an23 syl ctp csca cts snsstp2 ssun2 ssun1 prdsbaslem ) AGCHICCBJ
        BURZHURZUEZYLIURZUEZYLEUEZUFUEUSUGUHUIUJUKULUMUNUOZDUPUEZFUAUBCCUQCUCUD
        UAURZUTUEZUBURZHICCBJYNYPYQVAUEUSVBUOZUSYTUUCUEBJYLUCURUEYLUDURUEYLYTVC
        UEUEYLUUAUEVDYLUUBUEYQVEUEUSUSUGUOUOZHIKCBJYMYPYQVFUEZUSZUGZUOZUUHDVGUE
        ZDVFUUCHICCFBJYNYPYQVHUEUSUGVIUSUOZYMYOVJCVKYNYPYQVLUEVMBJVNWEHIVOZVPEV
        QVRUEZWFABCYRDYSEFUUDUUHUUIUDHIUUCUUJJKUUKUULLMUAUBUCNSRABCDEFJLMNOPQRV
        SABCDYSEFHIJLMNOPQRYSVTWAABCDEFUUIHIJLMNOPQRUUIVTWBAUUHWCAUUJWCAUULWCAU
        UKWCAYRWCAUUCWCAUUDWCOPWDTWGAKCUQZEUHZWHZUHZWHZUHZWHZWIZJWJUSZUUHWQZUUH
        WFWKZAUUGUVAWKZICVNZHKVNUVBAUVEHKAUVDICAUVDJUUTUUGWQABJUUFUUTUUFUUTWKZA
        YLJWKWEUVFUUFUUSVKUUFUUEUHZWHZUUSUUEYMYPWLUUEUUQVKUVGUURVKUVHUUSVKUUEYQ
        UHZWHZUUQYQVFWRVFUEZWGWMYQUUOVKUVIUUPVKUVJUUQVKEYLWNYQUUOWOUVIUUPWPWSWT
        UUEUUQWOUVGUURWPWSWTUUFUUSYMYPUUEXAXBXCXDXEAUUTJUUGWFWFAUUQWFWKZUURWFWK
        UUSWFWKUUTWFWKAUUOWFWKZUUPWFWKUVLAEMWKUUNWFWKUVMPEMXFUUNWFXGXHUUOWFXFUU
        PWFXGXHUUQWFXFUURWFXGUUSWFXKXIAEXJJWFRAEMPXLXMXNXOXPXPHIKCUUGUVAUUHUUHV
        TXQXRUVBUUMWFWKUVAWFWKUVCKCKFYBSXSCDYBQXSXTUUTJWJXAUUMUVAUUHWFWFYAYCYDU
        VKUUHVDZUJZWRYBUECVDWRUPUEYSVDWRVGUEUUIVDYEZWRYFUEFVDZUVNWRVHUEUUJVDZYE
        ZUKZUVTWRYGUEUULVDWRVLUEUUKVDWRUFUEYRVDYEWRVAUEUUCVDWRVEUEUUDVDVJUKZUKU
        VOUVSUVTUVQUVNUVRYHUVSUVPYIWTUVTUWAYJWTYK $.
    $}

    ${
      prdsip.m $e |- ., = ( .i ` P ) $.
      $( Inner product in a structure product.  (Contributed by Thierry Arnoux,
         16-Jun-2019.)  (Revised by Zhi Wang, 18-Aug-2024.) $)
      prdsip $p |- ( ph -> ., = ( f e. B , g e. B |-> ( S gsum
        ( x e. I |-> ( ( f ` x ) ( .i ` ( R ` x ) ) ( g ` x ) ) ) ) ) ) $=
        ( cfv cop va vc vd ve cds cmpt crn cc0 csn cun cxr clt csup cmpo cplusg
        cv co cxp c2nd chom cixp c1st cco cip cgsu cbs cvsca cmulr cpr wss cple
        wbr wral copab ctopn ccom cpt eqid prdsbas prdsplusg eqidd prdsval ipid
        cvv wcel fvexi a1i mpoexga sylancl cnx ctp csca cts snsstp3 ssun2 sstri
        wa ssun1 prdsbaslem ) AICGHCCBJBUPZGUPZSZWTHUPZSZWTESZUESUQUFUGUHUIUJUK
        ULUMUNZDUOSZFUAUBCCURCUCUDUAUPZUSSZUBUPZGHCCBJXBXDXEUTSUQVAUNZUQXHXKSBJ
        WTUCUPSWTUDUPSWTXHVBSSWTXISTWTXJSXEVCSUQUQUFUNUNZGHCCFBJXBXDXEVDSUQUFVE
        UQZUNZGHFVFSZCBJXAXDXEVGSUQUFUNZGHCCBJXBXDXEVHSUQUFUNZDVDXKXNXAXCVICVJX
        BXDXEVKSVLBJVMWQGHVNZVOEVPVQSZWDABCXFDXGEFXLXPXQUDGHXKXNJXOXRXSKLUAUBUC
        MXOVRQABCDEFJKLMNOPQVSABCDXGEFGHJKLMNOPQXGVRVTAXQWAAXPWAAXNWAAXSWAAXRWA
        AXFWAAXKWAAXLWANOWBRWCACWDWEZXTXNWDWEXTACDVFPWFZWGYAGHCCXMWDWDWHWIWJVDS
        XNTZUIZWJVFSCTWJUOSXGTWJVHSXQTWKZWJWLSFTZWJVGSXPTZYBWKZUJZYHWJWMSXSTWJV
        KSXRTWJUESXFTWKWJUTSXKTWJVCSXLTVIUJZUJYCYGYHYEYFYBWNYGYDWOWPYHYIWRWPWS
        $.
    $}

    ${
      prdsle.l $e |- .<_ = ( le ` P ) $.
      $( Structure product weak ordering.  (Contributed by Mario Carneiro,
         15-Aug-2015.)  (Revised by Thierry Arnoux, 16-Jun-2019.)  (Revised by
         Zhi Wang, 18-Aug-2024.) $)
      prdsle $p |- ( ph -> .<_ = { <. f , g >. | ( { f , g } C_ B /\
        A. x e. I ( f ` x ) ( le ` ( R ` x ) ) ( g ` x ) ) } ) $=
        ( cfv cop va vc vd ve cds cmpt crn cc0 csn cun cxr clt csup cmpo cplusg
        cv co cxp c2nd chom cixp c1st cco cpr wss cple wbr wa copab cvsca cmulr
        wral cip cgsu ccom cpt cvv cbs eqid prdsbas prdsplusg prdsmulr prdsvsca
        ctopn eqidd prdsval pleid wcel fvexi xpex prss anbi1i opabssxp eqsstrri
        vex opabbii ssexi a1i cnx cts csca snsstp2 ssun1 sstri ssun2 prdsbaslem
        ctp ) AJCGHCCBIBUPZGUPZSZXHHUPZSZXHESZUESUQUFUGUHUIUJUKULUMUNZDUOSZFUAU
        BCCURZCUCUDUAUPZUSSZUBUPZGHCCBIXJXLXMUTSUQVAUNZUQXQXTSBIXHUCUPSXHUDUPSX
        HXQVBSSXHXRSTXHXSSXMVCSUQUQUFUNUNZXIXKVDCVEZXJXLXMVFSVGBIVLZVHZGHVIZDVJ
        SZDVKSZDVFXTGHCCFBIXJXLXMVMSUQUFVNUQUNZYEWDEVOVPSZVQABCXNDXOEFYAYFYGUDG
        HXTYHIFVRSZYEYIKLUAUBUCMYJVSZQABCDEFIKLMNOPQVTABCDXOEFGHIKLMNOPQXOVSWAA
        BCDEFYGGHIKLMNOPQYGVSWBABCDEFYFGHIYJKLMNOPQYKYFVSWCAYHWEAYIWEAYEWEAXNWE
        AXTWEAYAWENOWFRWGYEVQWHAYEXPCCCDVRPWIZYLWJYEXICWHXKCWHVHZYCVHZGHVIXPYNY
        DGHYMYBYCXIXKCGWOHWOWKWLWPYCGHCCWMWNWQWRWSVFSYETZUIZWSWTSYITZYOWSUESXNT
        ZXGZWSUTSXTTWSVCSYATVDZUJZWSVRSCTWSUOSXOTWSVKSYGTXGWSXASFTWSVJSYFTWSVMS
        YHTXGUJZUUAUJYPYSUUAYQYOYRXBYSYTXCXDUUAUUBXEXDXF $.

      $( Closure of the order relation on a structure product.  (Contributed by
         Mario Carneiro, 16-Aug-2015.) $)
      prdsless $p |- ( ph -> .<_ C_ ( B X. B ) ) $=
        ( vf vg vx cv cfv cpr wss cple wbr wral wa copab cxp prdsle wcel anbi1i
        vex prss opabbii opabssxp eqsstrri eqsstrdi ) AGPSZQSZUABUBZRSZURTVAUST
        VADTUCTUDRFUEZUFZPQUGZBBUHZARBCDEPQFGHIJKLMNOUIVDURBUJUSBUJUFZVBUFZPQUG
        VEVGVCPQVFUTVBURUSBPULQULUMUKUNVBPQBBUOUPUQ $.
    $}

    ${
      prdsds.l $e |- D = ( dist ` P ) $.
      $( Structure product distance function.  (Contributed by Mario Carneiro,
         15-Aug-2015.)  (Revised by Thierry Arnoux, 16-Jun-2019.)  (Revised by
         Zhi Wang, 18-Aug-2024.) $)
      prdsds $p |- ( ph -> D = ( f e. B , g e. B |-> sup ( ( ran ( x e. I |->
   ( ( f ` x ) ( dist ` ( R ` x ) ) ( g ` x ) ) ) u. { 0 } ) , RR* , < ) ) ) $=
        ( cfv cop va vc vd ve vy vz vw cv cds cmpt crn cc0 csn cun cxr clt csup
        cmpo cplusg cxp c2nd chom cixp c1st cco cvsca cmulr cip cgsu cple ctopn
        ccom cpt cvv cbs eqid prdsbas prdsplusg prdsmulr prdsvsca eqidd prdsval
        co prdsle dsid wcel cuni cpw fvexi xrex uniex pwex wn wral wrex wi crab
        wbr df-sup ssrab2 unissi elpwi2 eqeltri rgen2w a1i cnx cts ctp cpr csca
        wa mpoexw snsstp3 ssun1 sstri ssun2 prdsbaslem ) ADCHICCBJBUHZHUHSZXRIU
        HSZXRFSZUISWCUJUKULUMUNZUOUPUQZURZEUSSZGUAUBCCUTCUCUDUAUHZVASZUBUHZHICC
        BJXSXTYAVBSWCVCURZWCYFYISBJXRUCUHSXRUDUHSXRYFVDSSXRYGSTXRYHSYAVESWCWCUJ
        URURZYDEVFSZEVGSZEUIYIHICCGBJXSXTYAVHSWCUJVIWCURZEVJSZVKFVLVMSZVNABCYDE
        YEFGYJYKYLUDHIYIYMJGVOSZYNYOKLUAUBUCMYPVPZQABCEFGJKLMNOPQVQABCEYEFGHIJK
        LMNOPQYEVPVRABCEFGYLHIJKLMNOPQYLVPVSABCEFGYKHIJYPKLMNOPQYQYKVPVTAYMWAAY
        OWAABCEFGHIJYNKLMNOPQYNVPWDAYDWAAYIWAAYJWANOWBRWEYDVNWFAHICCYCUOWGZWHZC
        EVOPWIZYTYRUOWJWKZWLYCYSWFHICCYCUEUHZUFUHZUPWRWMUFYBWNUUCUUBUPWRUUCUGUH
        UPWRUGYBWOWPUFUOWNXKZUEUOWQZWGZYSUEUFUGYBUOUPWSUUFYRVNUUAUUEUOUUDUEUOWT
        XAXBXCXDXLXEXFUISYDTZUMZXFXGSYOTZXFVJSYNTZUUGXHZXFVBSYITXFVESYJTXIZUNZX
        FVOSCTXFUSSYETXFVGSYLTXHXFXJSGTXFVFSYKTXFVHSYMTXHUNZUUMUNUUHUUKUUMUUIUU
        JUUGXMUUKUULXNXOUUMUUNXPXOXQ $.

      $( Structure product distance function.  (Contributed by Mario Carneiro,
         15-Sep-2015.) $)
      prdsdsfn $p |- ( ph -> D Fn ( B X. B ) ) $=
        ( vf vg vx cv cfv cxp wfn cds co cmpt crn cc0 csn cun cxr clt csup cmpo
        eqid xrltso supex fnmpoi prdsds fneq1d mpbiri ) ACBBUAZUBPQBBRGRSZPSTVB
        QSTVBETUCTUDUEUFUGUHUIZUJUKULZUMZVAUBPQBBVDVEVEUNUJVCUKUOUPUQAVACVEARBC
        DEFPQGHIJKLMNOURUSUT $.
    $}

    ${
      prdstset.l $e |- O = ( TopSet ` P ) $.
      $( Structure product topology.  (Contributed by Mario Carneiro,
         15-Aug-2015.)  (Revised by Thierry Arnoux, 16-Jun-2019.)  (Revised by
         Zhi Wang, 18-Aug-2024.) $)
      prdstset $p |- ( ph -> O = ( Xt_ ` ( TopOpen o. R ) ) ) $=
        ( vf vx cfv cop cnx va vc vd ve vg cds cplusg cv c2nd chom co cixp cmpo
        cxp c1st cco cmpt ctopn ccom cpt cvsca cmulr cts cip cgsu cple cvv eqid
        cbs prdsbas prdsplusg prdsmulr eqidd prdsle prdsds prdsval tsetid fvexd
        prdsvsca csn ctp cpr cun csca snsstp1 ssun1 sstri ssun2 prdsbaslem ) AG
        BCUFRZCUGRZEUAUBBBUNBUCUDUAUHZUIRZUBUHZPUEBBQFQUHZPUHRZWOUEUHRZWODRZUJR
        UKULUMZUKWLWSRQFWOUCUHRWOUDUHRWOWLUORRWOWMRSWOWNRWRUPRUKUKUQUMUMZURDUSZ
        UTRZCVARZCVBRZCVCWSPUEBBEQFWPWQWRVDRUKUQVEUKUMZCVFRZXBVGAQBWJCWKDEWTXCX
        DUDPUEWSXEFEVIRZXFXBHIUAUBUCJXGVHZNAQBCDEFHIJKLMNVJAQBCWKDEPUEFHIJKLMNW
        KVHVKAQBCDEXDPUEFHIJKLMNXDVHVLAQBCDEXCPUEFXGHIJKLMNXHXCVHVSAXEVMAXBVMAQ
        BCDEPUEFXFHIJKLMNXFVHVNAQBWJCDEPUEFHIJKLMNWJVHVOAWSVMAWTVMKLVPOVQAXAUTV
        RTVCRXBSZVTZXITVFRXFSZTUFRWJSZWAZTUJRWSSTUPRWTSWBZWCZTVIRBSTUGRWKSTVBRX
        DSWATWDRESTVARXCSTVDRXESWAWCZXOWCXJXMXOXIXKXLWEXMXNWFWGXOXPWHWGWI $.
    $}

    ${
      prdshom.h $e |- H = ( Hom ` P ) $.
      $( Structure product hom-sets.  (Contributed by Mario Carneiro,
         7-Jan-2017.)  (Revised by Thierry Arnoux, 16-Jun-2019.)  (Revised by
         Zhi Wang, 18-Aug-2024.) $)
      prdshom $p |- ( ph -> H = ( f e. B , g e. B |->
          X_ x e. I ( ( f ` x ) ( Hom ` ( R ` x ) ) ( g ` x ) ) ) ) $=
        ( cfv cvv va vc vd ve cds cplusg cxp cv c2nd chom co cixp cmpo c1st cop
        cco cmpt cvsca cmulr cip cgsu cple cts eqid prdsplusg prdsmulr prdsvsca
        cbs prdsbas eqidd prdstset prdsle prdsds prdsval homid crn cuni cmap wf
        cpw wcel wral wss ovssunirn cnx strfvss fvssunirn rnss uniss mp2b sstri
        rgenw ss2ixp ax-mp wceq cdm dmexd eqeltrrd rnexg 3syl ixpconstg syl2anc
        uniexg sseqtrid ovex elpw2 sylibr ralrimivw fmpo sylib xpex a1i syl3anc
        fvexi pwex fex2 csn ctp cpr cun csca snsspr1 ssun2 prdsbaslem ) AICDUES
        ZDUFSZFUAUBCCUGZCUCUDUAUHZUISZUBUHZGHCCBJBUHZGUHSZYKHUHSZYKESZUJSZUKZUL
        ZUMZUKYHYRSBJYKUCUHSYKUDUHSYKYHUNSSYKYISUOYKYJSYNUPSUKUKUQUMUMZYRDURSZD
        USSZDUJYRGHCCFBJYLYMYNUTSUKUQVAUKUMZDVBSZDVCSZTABCYEDYFEFYSYTUUAUDGHYRU
        UBJFVHSZUUCUUDKLUAUBUCMUUEVDZQABCDEFJKLMNOPQVIABCDYFEFGHJKLMNOPQYFVDVEA
        BCDEFUUAGHJKLMNOPQUUAVDVFABCDEFYTGHJUUEKLMNOPQUUFYTVDVGAUUBVJACDEFJUUDK
        LMNOPQUUDVDVKABCDEFGHJUUCKLMNOPQUUCVDVLABCYEDEFGHJKLMNOPQYEVDVMAYRVJAYS
        VJNOVNRVOAYGEVPZVQZVPZVQZVPZVQZJVRUKZVTZYRVSZYGTWAZUUNTWAZYRTWAAYQUUNWA
        ZHCWBZGCWBUUOAUUSGCAUURHCAYQUUMWCUURABJUULULZYQUUMYPUULWCZBJWBYQUUTWCUV
        ABJYPYOVPZVQZUULYOYLYMWDYOUUJWCUVBUUKWCUVCUULWCYOYNVPZVQZUUJYNUJWEUJSZV
        OWFYNUUHWCUVDUUIWCUVEUUJWCEYKWGYNUUHWHUVDUUIWIWJWKYOUUJWHUVBUUKWIWJWKWL
        BJYPUULWMWNAJTWAUULTWAZUUTUUMWOAEWPJTQAELOWQWRAUUJTWAZUUKTWAUVGAUUHTWAZ
        UUITWAUVHAELWAUUGTWAUVIOELWSUUGTXCWTUUHTWSUUITXCWTUUJTWSUUKTXCWTBJUULTT
        XAXBXDYQUUMUULJVRXEZXFXGXHXHGHCCYQUUNYRYRVDXIXJUUPACCCDVHPXNZUVKXKXLUUQ
        AUUMUVJXOXLYGUUNYRTTXPXMUVFYRUOZXQZWEVCSUUDUOWEVBSUUCUOWEUESYEUOXRZUVLW
        EUPSYSUOZXSZXTZWEVHSCUOWEUFSYFUOWEUSSUUAUOXRWEYASFUOWEURSYTUOWEUTSUUBUO
        XRXTZUVQXTUVMUVPUVQUVLUVOYBUVPUVNYCWKUVQUVRYCWKYD $.

      prdsco.o $e |- .xb = ( comp ` P ) $.
      $( Structure product composition operation.  (Contributed by Mario
         Carneiro, 7-Jan-2017.)  (Revised by Thierry Arnoux, 16-Jun-2019.)
         (Revised by Zhi Wang, 18-Aug-2024.) $)
      prdsco $p |- ( ph -> .xb = ( a e. ( B X. B ) , c e. B |->
        ( d e. ( ( 2nd ` a ) H c ) , e e. ( H ` a ) |-> ( x e. I |->
          ( ( d ` x ) ( <. ( ( 1st ` a ) ` x ) , ( ( 2nd ` a ) ` x ) >.
            ( comp ` ( R ` x ) ) ( c ` x ) ) ( e ` x ) ) ) ) ) ) $=
        ( vf vg cds cfv cplusg cxp cv c2nd co c1st cop cco cmpt cvsca cmulr cip
        cmpo cgsu cple cts cvv cbs prdsbas prdsplusg prdsmulr prdsvsca prdstset
        eqid eqidd prdsle prdsds prdshom prdsval ccoid wcel fvexi mpoex a1i cnx
        xpex csn ctp chom cpr cun csca snsspr2 ssun2 sstri prdsbaslem ) AGCDUEU
        FZDUGUFZFMNCCUHZCOHMUIZUJUFZNUIZIUKWPIUFBJBUIZOUIUFWSHUIUFWSWPULUFUFWSW
        QUFUMWSWRUFWSEUFZUNUFUKUKUOUSZUSZXBDUPUFZDUQUFZDUNIUCUDCCFBJWSUCUIUFWSU
        DUIUFWTURUFUKUOUTUKUSZDVAUFZDVBUFZVCABCWMDWNEFXBXCXDHUCUDIXEJFVDUFZXFXG
        KLMNOPXHVJZTABCDEFJKLPQRSTVEABCDWNEFUCUDJKLPQRSTWNVJVFABCDEFXDUCUDJKLPQ
        RSTXDVJVGABCDEFXCUCUDJXHKLPQRSTXIXCVJVHAXEVKACDEFJXGKLPQRSTXGVJVIABCDEF
        UCUDJXFKLPQRSTXFVJVLABCWMDEFUCUDJKLPQRSTWMVJVMABCDEFUCUDIJKLPQRSTUAVNAX
        BVKQRVOUBVPXBVCVQAMNWOCXACCCDVDSVRZXJWBXJVSVTWAUNUFXBUMZWCZWAVBUFXGUMWA
        VAUFXFUMWAUEUFWMUMWDZWAWEUFIUMZXKWFZWGZWAVDUFCUMWAUGUFWNUMWAUQUFXDUMWDW
        AWHUFFUMWAUPUFXCUMWAURUFXEUMWDWGZXPWGXLXOXPXNXKWIXOXMWJWKXPXQWJWKWL $.
    $}
  $}

  ${
    $d f g x y z B $.  $d f g x y z F $.  $d f g x y z G $.  $d f g x y z ph $.
    $d f g x y z I $.  $d x J $.  $d y z K $.  $d x T $.  $d x V $.
    $d f g x y z R $.  $d f g x y z S $.  $d x W $.  $d f g x y z Y $.
    prdsbasmpt.y $e |- Y = ( S Xs_ R ) $.
    prdsbasmpt.b $e |- B = ( Base ` Y ) $.
    ${
      prdsbasmpt.s $e |- ( ph -> S e. V ) $.
      prdsbasmpt.i $e |- ( ph -> I e. W ) $.
      prdsbasmpt.r $e |- ( ph -> R Fn I ) $.
      $( The base set of a structure product is an indexed set product.
         (Contributed by Stefan O'Rear, 10-Jan-2015.)  (Revised by Mario
         Carneiro, 15-Aug-2015.) $)
      prdsbas2 $p |- ( ph -> B = X_ x e. I ( Base ` ( R ` x ) ) ) $=
        ( cvv wfn wcel fnex syl2anc fndmd prdsbas ) ABCIDEFGOJLADFPFHQDOQNMFHDR
        SKAFDNTUA $.

      $( A constructed tuple is a point in a structure product iff each
         coordinate is in the proper base set.  (Contributed by Stefan O'Rear,
         10-Jan-2015.) $)
      prdsbasmpt $p |- ( ph -> ( ( x e. I |-> U ) e. B <->
          A. x e. I U e. ( Base ` ( R ` x ) ) ) ) $=
        ( cmpt wcel cv cfv cbs cixp wral prdsbas2 eleq2d wb mptelixpg syl bitrd
        ) ABGFPZCQUIBGBRDSTSZUAZQZFUJQBGUBZACUKUIABCDEGHIJKLMNOUCUDAGIQULUMUENB
        GFUJIUFUGUH $.

      ${
        prdsbasmpt.t $e |- ( ph -> T e. B ) $.
        $( Points in the structure product are functions; use this with ~ dffn5
           to establish equalities.  (Contributed by Stefan O'Rear,
           10-Jan-2015.) $)
        prdsbasfn $p |- ( ph -> T Fn I ) $=
          ( vx cv cfv cbs cixp wcel wfn prdsbas2 eleqtrd ixpfn syl ) AEPFPQCRSR
          ZTZUAEFUBAEBUHOAPBCDFGHIJKLMNUCUDPFUGEUEUF $.

        prdsbasprj.j $e |- ( ph -> J e. I ) $.
        $( Each point in a structure product restricts on each coordinate to
           the relevant base set.  (Contributed by Stefan O'Rear,
           10-Jan-2015.) $)
        prdsbasprj $p |- ( ph -> ( T ` J ) e. ( Base ` ( R ` J ) ) ) $=
          ( vx cfv wcel cv wceq fveq2 2fveq3 eleq12d cixp wral prdsbas2 eleqtrd
          cbs cvv wfn elixp2 simp3bi syl rspcdva ) ARUAZESZUQCSUJSZTZGESZGCSUJS
          ZTRFGUQGUBURVAUSVBUQGEUCUQGUJCUDUEAERFUSUFZTZUTRFUGZAEBVCPARBCDFHIJKL
          MNOUHUIVDEUKTEFULVERFUSEUMUNUOQUP $.
      $}

      prdsplusgval.f $e |- ( ph -> F e. B ) $.
      prdsplusgval.g $e |- ( ph -> G e. B ) $.
      ${
        prdsplusgval.p $e |- .+ = ( +g ` Y ) $.
        $( Value of a componentwise sum in a structure product.  (Contributed
           by Stefan O'Rear, 10-Jan-2015.)  (Revised by Mario Carneiro,
           15-Aug-2015.) $)
        prdsplusgval $p |- ( ph -> ( F .+ G ) = ( x e. I |-> ( ( F ` x )
            ( +g ` ( R ` x ) ) ( G ` x ) ) ) ) $=
          ( vy vz cv cfv cplusg cmpt cvv wcel fnex syl2anc fndmd prdsplusg wceq
          co wfn wa fveq1 oveqan12d adantl mpteq2dv mptexd ovmpod ) AUAUBGHCCBI
          BUCZUAUCZUDZVCUBUCZUDZVCEUDUEUDZUNZUFBIVCGUDZVCHUDZVHUNZUFDUGABCLDEFU
          AUBIJUGMOAEIUOIKUHEUGUHQPIKEUIUJNAIEQUKTULAVDGUMZVFHUMZUPZUPBIVIVLVOV
          IVLUMAVMVNVEVJVGVKVHVCVDGUQVCVFHUQURUSUTRSABIVLKPVAVB $.

        prdsplusgfval.j $e |- ( ph -> J e. I ) $.
        $( Value of a structure product sum at a single coordinate.
           (Contributed by Stefan O'Rear, 10-Jan-2015.) $)
        prdsplusgfval $p |- ( ph -> ( ( F .+ G ) ` J ) = ( ( F ` J )
            ( +g ` ( R ` J ) ) ( G ` J ) ) ) $=
          ( vx co cfv cv cplusg cmpt prdsplusgval fveq1d wcel wceq 2fveq3 fveq2
          oveq123d eqid ovex fvmpt syl eqtrd ) AIFGCUCZUDIUBHUBUEZFUDZVAGUDZVAD
          UDUFUDZUCZUGZUDZIFUDZIGUDZIDUDUFUDZUCZAIUTVFAUBBCDEFGHJKLMNOPQRSTUHUI
          AIHUJVGVKUKUAUBIVEVKHVFVAIUKVBVHVCVIVDVJVAIUFDULVAIFUMVAIGUMUNVFUOVHV
          IVJUPUQURUS $.
      $}

      ${
        prdsmulrval.t $e |- .x. = ( .r ` Y ) $.
        $( Value of a componentwise ring product in a structure product.
           (Contributed by Mario Carneiro, 11-Jan-2015.) $)
        prdsmulrval $p |- ( ph -> ( F .x. G ) = ( x e. I |-> ( ( F ` x )
            ( .r ` ( R ` x ) ) ( G ` x ) ) ) ) $=
          ( vy vz cv cfv cmulr co cmpt cvv wfn wcel fnex syl2anc fndmd prdsmulr
          wceq wa fveq1 oveqan12d adantl mpteq2dv mptexd ovmpod ) AUAUBGHCCBIBU
          CZUAUCZUDZVCUBUCZUDZVCDUDUEUDZUFZUGBIVCGUDZVCHUDZVHUFZUGFUHABCLDEFUAU
          BIJUHMOADIUIIKUJDUHUJQPIKDUKULNAIDQUMTUNAVDGUOZVFHUOZUPZUPBIVIVLVOVIV
          LUOAVMVNVEVJVGVKVHVCVDGUQVCVFHUQURUSUTRSABIVLKPVAVB $.

        prdsmulrfval.j $e |- ( ph -> J e. I ) $.
        $( Value of a structure product's ring product at a single coordinate.
           (Contributed by Mario Carneiro, 11-Jan-2015.) $)
        prdsmulrfval $p |- ( ph -> ( ( F .x. G ) ` J ) = ( ( F ` J )
            ( .r ` ( R ` J ) ) ( G ` J ) ) ) $=
          ( vx co cfv cv cmulr cmpt prdsmulrval fveq1d wcel wceq fveq2 oveq123d
          2fveq3 eqid ovex fvmpt syl eqtrd ) AIFGEUCZUDIUBHUBUEZFUDZVAGUDZVACUD
          UFUDZUCZUGZUDZIFUDZIGUDZICUDUFUDZUCZAIUTVFAUBBCDEFGHJKLMNOPQRSTUHUIAI
          HUJVGVKUKUAUBIVEVKHVFVAIUKVBVHVCVIVDVJVAIUFCUNVAIFULVAIGULUMVFUOVHVIV
          JUPUQURUS $.
      $}

      ${
        prdsleval.l $e |- .<_ = ( le ` Y ) $.
        $( Value of the product ordering in a structure product.  (Contributed
           by Mario Carneiro, 15-Aug-2015.) $)
        prdsleval $p |- ( ph -> ( F .<_ G <->
          A. x e. I ( F ` x ) ( le ` ( R ` x ) ) ( G ` x ) ) ) $=
          ( vf vg wbr cop cv wcel wa cfv cple wral copab df-br cpr wss cvv fnex
          wfn syl2anc fndmd prdsle prss anbi1i opabbii eqtr4di eleq2d bitrid wb
          vex wceq fveq1 breqan12d ralbidv opelopab2a bitrd ) AFGIUCZFGUDZUAUEZ
          CUFUBUEZCUFUGZBUEZVQUHZVTVRUHZVTDUHUIUHZUCZBHUJZUGZUAUBUKZUFZVTFUHZVT
          GUHZWCUCZBHUJZVOVPIUFAWHFGIULAIWGVPAIVQVRUMCUNZWEUGZUAUBUKWGABCLDEUAU
          BHIJUOMOADHUQHKUFDUOUFQPHKDUPURNAHDQUSTUTWFWNUAUBVSWMWEVQVRCUAVHUBVHV
          AVBVCVDVEVFAFCUFGCUFWHWLVGRSWEWLUAUBFGCCVQFVIZVRGVIZUGWDWKBHWOWPWAWIW
          BWJWCVTVQFVJVTVRGVJVKVLVMURVN $.
      $}

      ${
        prdsdsval.d $e |- D = ( dist ` Y ) $.
        $( Value of the metric in a structure product.  (Contributed by Mario
           Carneiro, 20-Aug-2015.) $)
        prdsdsval $p |- ( ph -> ( F D G ) = sup ( ( ran ( x e. I |->
     ( ( F ` x ) ( dist ` ( R ` x ) ) ( G ` x ) ) ) u. { 0 } ) , RR* , < ) ) $=
          ( vf vg cv cfv cds co cmpt crn cc0 csn cun cxr clt csup cvv wcel fnex
          wfn syl2anc cdm wceq syl prdsds fveq1 oveqan12d adantl mpteq2dv rneqd
          fndm wa uneq1d supeq1d xrltso supex a1i ovmpod ) AUAUBGHCCBIBUCZUAUCZ
          UDZVQUBUCZUDZVQEUDUEUDZUFZUGZUHZUIUJZUKZULUMUNBIVQGUDZVQHUDZWBUFZUGZU
          HZWFUKZULUMUNZDUOABCDLEFUAUBIJUOMOAEIURZIKUPEUOUPQPIKEUQUSNAWOEUTIVAQ
          IEVIVBTVCAVRGVAZVTHVAZVJZVJZULWGWMUMWSWEWLWFWSWDWKWSBIWCWJWRWCWJVAAWP
          WQVSWHWAWIWBVQVRGVDVQVTHVDVEVFVGVHVKVLRSWNUOUPAULWMUMVMVNVOVP $.
      $}
    $}

    prdsvscaval.t $e |- .x. = ( .s ` Y ) $.
    prdsvscaval.k $e |- K = ( Base ` S ) $.
    prdsvscaval.s $e |- ( ph -> S e. V ) $.
    prdsvscaval.i $e |- ( ph -> I e. W ) $.
    prdsvscaval.r $e |- ( ph -> R Fn I ) $.
    prdsvscaval.f $e |- ( ph -> F e. K ) $.
    prdsvscaval.g $e |- ( ph -> G e. B ) $.
    $( Scalar multiplication in a structure product is pointwise.  (Contributed
       by Stefan O'Rear, 10-Jan-2015.) $)
    prdsvscaval $p |- ( ph -> ( F .x. G ) = ( x e. I |->
        ( F ( .s ` ( R ` x ) ) ( G ` x ) ) ) ) $=
      ( vy vz cv cfv cvsca co cmpt cvv wcel fnex syl2anc fndmd prdsvsca wceq wa
      wfn id fveq1 oveqan12d adantl mpteq2dv mptexd ovmpod ) AUCUDGHJCBIUCUEZBU
      EZUDUEZUFZVGDUFUGUFZUHZUIBIGVGHUFZVJUHZUIFUJABCMDEFUCUDIJKUJNRADIURILUKDU
      JUKTSILDULUMOAIDTUNQPUOAVFGUPZVHHUPZUQZUQBIVKVMVPVKVMUPAVNVOVFGVIVLVJVNUS
      VGVHHUTVAVBVCUAUBABIVMLSVDVE $.

    prdsvscafval.j $e |- ( ph -> J e. I ) $.
    $( Scalar multiplication of a single coordinate in a structure product.
       (Contributed by Stefan O'Rear, 10-Jan-2015.) $)
    prdsvscafval $p |- ( ph -> ( ( F .x. G ) ` J ) =
        ( F ( .s ` ( R ` J ) ) ( G ` J ) ) ) $=
      ( vx cv cfv cvsca cvv prdsvscaval wceq 2fveq3 eqidd fveq2 oveq123d adantl
      co ovexd fvmptd ) AUDIFUDUEZGUFZUSCUFUGUFZUPZFIGUFZICUFUGUFZUPZHFGEUPUHAU
      DBCDEFGHJKLMNOPQRSTUAUBUIUSIUJZVBVEUJAVFFFUTVCVAVDUSIUGCUKVFFULUSIGUMUNUO
      UCAFVCVDUQUR $.
  $}

  ${
    $d y B $.  $d x y F $.  $d x y G $.  $d y ph $.  $d y S $.  $d y V $.
    $d x y I $.  $d y R $.  $d y W $.  $d y Y $.
    prdsbasmpt2.y $e |- Y = ( S Xs_ ( x e. I |-> R ) ) $.
    prdsbasmpt2.b $e |- B = ( Base ` Y ) $.
    prdsbasmpt2.s $e |- ( ph -> S e. V ) $.
    prdsbasmpt2.i $e |- ( ph -> I e. W ) $.
    prdsbasmpt2.r $e |- ( ph -> A. x e. I R e. X ) $.
    ${
      prdsbasmpt2.k $e |- K = ( Base ` R ) $.
      $( The base set of an indexed structure product.  (Contributed by Mario
         Carneiro, 13-Sep-2015.) $)
      prdsbas3 $p |- ( ph -> B = X_ x e. I K ) $=
        ( vy cfv cbs cv cmpt cixp wcel wral wfn eqid syl prdsbas2 nfcv nffvmpt1
        nffv 2fveq3 cbvixp eqtrdi wceq wa fvmpt2 fveq2d eqtr4di ralimiaa ixpeq2
        fnmpt 3syl eqtrd ) ACBFBUAZBFDUBZSZTSZUCZBFGUCZACRFRUAZVGSZTSZUCVJARCVG
        EFHIKLMNOADJUDZBFUEZVGFUFPBFDVGJVGUGZVCUHUIRBFVNVIBVMTBTUJBFDVLUKULRVIU
        JVLVFTVGUMUNUOAVPVIGUPZBFUEVJVKUPPVOVRBFVFFUDVOUQZVIDTSGVSVHDTBFDJVGVQU
        RUSQUTVABFVIGVBVDVE $.

      $( A constructed tuple is a point in a structure product iff each
         coordinate is in the proper base set.  (Contributed by Mario Carneiro,
         3-Jul-2015.)  (Revised by Mario Carneiro, 13-Sep-2015.) $)
      prdsbasmpt2 $p |- ( ph ->
          ( ( x e. I |-> U ) e. B <-> A. x e. I U e. K ) ) $=
        ( cmpt wcel cixp wral prdsbas3 eleq2d wb mptelixpg syl bitrd ) ABGFSZCT
        UIBGHUAZTZFHTBGUBZACUJUIABCDEGHIJKLMNOPQRUCUDAGJTUKULUEPBGFHJUFUGUH $.

      prdsbascl.f $e |- ( ph -> F e. B ) $.
      $( An element of the base has projections closed in the factors.
         (Contributed by Mario Carneiro, 27-Aug-2015.) $)
      prdsbascl $p |- ( ph -> A. x e. I ( F ` x ) e. K ) $=
        ( wcel cfv cmpt wral wfn wceq eqid fnmpt prdsbasfn dffn5 sylib eqeltrrd
        cv syl prdsbasmpt2 mpbid ) ABGBULFUAZUBZCTUPHTBGUCAFUQCAFGUDFUQUEACBGDU
        BZEFGIJLMNOPADKTBGUCURGUDQBGDURKURUFUGUMSUHBGFUIUJSUKABCDEUPGHIJKLMNOPQ
        RUNUO $.
    $}

    prdsdsval2.f $e |- ( ph -> F e. B ) $.
    prdsdsval2.g $e |- ( ph -> G e. B ) $.
    ${
      prdsdsval2.e $e |- E = ( dist ` R ) $.
      prdsdsval2.d $e |- D = ( dist ` Y ) $.
      $( Value of the metric in a structure product.  (Contributed by Mario
         Carneiro, 20-Aug-2015.) $)
      prdsdsval2 $p |- ( ph -> ( F D G ) = sup ( ( ran ( x e. I |->
        ( ( F ` x ) E ( G ` x ) ) ) u. { 0 } ) , RR* , < ) ) $=
        ( vy co cv cfv cmpt cds crn cc0 csn cun cxr clt csup wcel wral wfn eqid
        fnmpt syl prdsdsval nfcv nffvmpt1 nffv nfov wceq 2fveq3 oveq123d cbvmpt
        fveq2 eqidd fvmpt2 fveq2d eqtr4di oveqd ralimiaa mpteq12 syl2anc eqtrid
        wa rneqd uneq1d supeq1d eqtrd ) AHIDUEUDJUDUFZHUGZWGIUGZWGBJEUHZUGZUIUG
        ZUEZUHZUJZUKULZUMZUNUOUPBJBUFZHUGZWRIUGZGUEZUHZUJZWPUMZUNUOUPAUDCDWJFHI
        JKLNOPQRAEMUQZBJURZWJJUSSBJEWJMWJUTZVAVBTUAUCVCAUNWQXDUOAWOXCWPAWNXBAWN
        BJWSWTWRWJUGZUIUGZUEZUHZXBUDBJWMXJBWHWIWLBWHVDBWKUIBUIVDBJEWGVEVFBWIVDV
        GUDXJVDWGWRVHWHWSWIWTWLXIWGWRUIWJVIWGWRHVLWGWRIVLVJVKAJJVHXJXAVHZBJURZX
        KXBVHAJVMAXFXMSXEXLBJWRJUQXEWBZXIGWSWTXNXIEUIUGGXNXHEUIBJEMWJXGVNVOUBVP
        VQVRVBBJXJJXAVSVTWAWCWDWEWF $.
    $}

    ${
      prdsdsval3.k $e |- K = ( Base ` R ) $.
      prdsdsval3.e $e |- E = ( ( dist ` R ) |` ( K X. K ) ) $.
      prdsdsval3.d $e |- D = ( dist ` Y ) $.
      $( Value of the metric in a structure product.  (Contributed by Mario
         Carneiro, 27-Aug-2015.) $)
      prdsdsval3 $p |- ( ph -> ( F D G ) = sup ( ( ran ( x e. I |->
        ( ( F ` x ) E ( G ` x ) ) ) u. { 0 } ) , RR* , < ) ) $=
        ( co cv cfv cds cmpt crn cc0 csn cun cxr csup eqid prdsdsval2 wceq wral
        clt eqidd wcel prdsbascl wa cxp cres oveqi ovres eqtrid ex ral2imi sylc
        mpteq12 syl2anc rneqd uneq1d supeq1d eqtr4d ) AHIDUFBJBUGZHUHZVTIUHZEUI
        UHZUFZUJZUKZULUMZUNZUOVAUPBJWAWBGUFZUJZUKZWGUNZUOVAUPABCDEFWCHIJLMNOPQR
        STUAUBWCUQUEURAUOWLWHVAAWKWFWGAWJWEAJJUSWIWDUSZBJUTZWJWEUSAJVBAWAKVCZBJ
        UTWBKVCZBJUTWNABCEFHJKLMNOPQRSTUCUAVDABCEFIJKLMNOPQRSTUCUBVDWOWPWMBJWOW
        PWMWOWPVEWIWAWBWCKKVFVGZUFWDGWQWAWBUDVHWAWBKKWCVIVJVKVLVMBJWIJWDVNVOVPV
        QVRVS $.
    $}
  $}

  ${
    $d i r F $.  $d i r I $.  $d i r R $.
    pwsval.y $e |- Y = ( R ^s I ) $.
    pwsval.f $e |- F = ( Scalar ` R ) $.
    $( Value of a structure power.  (Contributed by Mario Carneiro,
       11-Jan-2015.) $)
    pwsval $p |- ( ( R e. V /\ I e. W ) -> Y = ( F Xs_ ( I X. { R } ) ) ) $=
      ( vr vi wcel wa cpws co csn cxp cprds cvv wceq csca elex cfv simpl fveq2d
      cv eqtr4di sneq xpeq12 syl2anr oveq12d df-pws ovex ovmpoa syl2an eqtrid
      id ) ADKZCEKZLFACMNZBCAOZPZQNZGUQARKCRKUSVBSURADUACEUAIJACRRIUEZTUBZJUEZV
      COZPZQNVBMVCASZVECSZLZVDBVGVAQVJVDATUBBVJVCATVHVIUCUDHUFVIVIVFUTSVGVASVHV
      IUPVCAUGVECVFUTUHUIUJJIUKBVAQULUMUNUO $.
  $}

  ${
    $d x I $.  $d x R $.  $d x V $.  $d x W $.
    pwsbas.y $e |- Y = ( R ^s I ) $.
    pwsbas.f $e |- B = ( Base ` R ) $.
    $( Base set of a structure power.  (Contributed by Mario Carneiro,
       11-Jan-2015.) $)
    pwsbas $p |- ( ( R e. V /\ I e. W ) -> ( B ^m I ) = ( Base ` Y ) ) $=
      ( vx wcel wa cbs cfv csca co cixp cmap eqid cvv wceq csn cxp cprds pwsval
      fveq2d cv fvexd simpr snex xpexg sylancl c0 wne cdm snnzg adantr dmxp syl
      prdsbas wral fvconst2g ralrimiva ixpeq2 eqtrd fvex oveq1i eqtr4di 3eqtrrd
      ixpconstg ) BDJZCEJZKZFLMBNMZCBUAZUBZUCOZLMZICBLMZPZACQOZVLFVPLBVMCDEFGVM
      RUDUEVLVQICIUFZVOMZLMZPZVSVLIVQVPVOVMCSSVPRVLBNUGVLVKVNSJVOSJVJVKUHZBUICV
      NESUJUKVQRVLVNULUMZVOUNCTVJWFVKBDUOUPCVNUQURUSVLWCVRTZICUTZWDVSTVJWHVKVJW
      GICVJWACJKWBBLCBWADVAUEVBUPICWCVRVCURVDVLVSVRCQOZVTVLVKVRSJVSWITWEBLVEICV
      RESVIUKAVRCQHVFVGVH $.

    pwselbas.v $e |- V = ( Base ` Y ) $.
    $( Membership in the base set of a structure power.  (Contributed by Stefan
       O'Rear, 24-Jan-2015.) $)
    pwselbasb $p |- ( ( R e. W /\ I e. Z ) -> ( X e. V <-> X : I --> B ) ) $=
      ( wcel wa cmap co wf cbs cfv pwsbas cvv eqtr4di eleq2d elmapg mpan adantl
      wb fvexi bitr3d ) BELZCHLZMZFACNOZLZFDLCAFPZUKULDFUKULGQRDABCEHGIJSKUAUBU
      JUMUNUFZUIATLUJUOABQJUGACFTHUCUDUEUH $.

    pwselbas.r $e |- ( ph -> R e. W ) $.
    pwselbas.i $e |- ( ph -> I e. Z ) $.
    ${
      pwselbas.x $e |- ( ph -> X e. V ) $.
      $( An element of a structure power is a function from the index set to
         the base set of the structure.  (Contributed by Mario Carneiro,
         11-Jan-2015.)  (Revised by Mario Carneiro, 5-Jun-2015.) $)
      pwselbas $p |- ( ph -> X : I --> B ) $=
        ( wcel wf wb pwselbasb syl2anc mpbid ) AGEPZDBGQZOACFPDIPUBUCRMNBCDEFGH
        IJKLSTUA $.
    $}

    ${
      pwselbasr.x $e |- ( ph -> X : I --> B ) $.
      $( The reverse direction of ~ pwselbasb : a function between the index
         and base set of a structure is an element of the structure power.
         (Contributed by SN, 29-Jul-2024.) $)
      pwselbasr $p |- ( ph -> X e. V ) $=
        ( wcel wf wb pwselbasb syl2anc mpbird ) AGEPZDBGQZOACFPDIPUBUCRMNBCDEFG
        HIJKLSTUA $.
    $}
  $}

  ${
    $d x .+ $.  $d x F $.  $d x G $.  $d x I $.  $d x ph $.  $d x .x. $.
    $d x R $.  $d x W $.
    pwsplusgval.y $e |- Y = ( R ^s I ) $.
    pwsplusgval.b $e |- B = ( Base ` Y ) $.
    pwsplusgval.r $e |- ( ph -> R e. V ) $.
    pwsplusgval.i $e |- ( ph -> I e. W ) $.
    pwsplusgval.f $e |- ( ph -> F e. B ) $.
    pwsplusgval.g $e |- ( ph -> G e. B ) $.
    ${
      pwsplusgval.a $e |- .+ = ( +g ` R ) $.
      pwsplusgval.p $e |- .+b = ( +g ` Y ) $.
      $( Value of addition in a structure power.  (Contributed by Mario
         Carneiro, 11-Jan-2015.) $)
      pwsplusgval $p |- ( ph -> ( F .+b G ) = ( F oF .+ G ) ) $=
        ( cfv vx csca csn cxp cprds co cplusg cv cmpt cof cbs cvv eqid wcel wfn
        fvexd fnconstg syl pwsval syl2anc fveq2d eqtrid eleqtrd prdsplusgval wa
        wceq fvconst2g sylan eqtr4di mpteq2dva pwselbas feqmptd offval2 3eqtr4d
        oveqd eqtrd ) AFGEUBTZHEUCUDZUEUFZUGTZUFZUAHUAUHZFTZWBGTZCUFZUIZFGDUFFG
        CUJUFAWAUAHWCWDWBVRTZUGTZUFZUIWFAUAVSUKTZVTVRVQFGHULJVSVSUMWJUMAEUBUPOA
        EIUNZVRHUONHEIUQURAFBWJPABKUKTWJMAKVSUKAWKHJUNKVSVFNOEVQHIJKLVQUMUSUTZV
        AVBZVCAGBWJQWMVCVTUMVDAUAHWIWEAWBHUNZVEZWHCWCWDWOWHEUGTCWOWGEUGAWKWNWGE
        VFNHEWBIVGVHVARVIVOVJVPADVTFGADKUGTVTSAKVSUGWLVAVBVOAUAHWCWDCFGJULULOWO
        WBFUPWOWBGUPAUAHEUKTZFAWPEHBIFKJLWPUMZMNOPVKVLAUAHWPGAWPEHBIGKJLWQMNOQV
        KVLVMVN $.
    $}

    ${
      pwsmulrval.a $e |- .x. = ( .r ` R ) $.
      pwsmulrval.p $e |- .xb = ( .r ` Y ) $.
      $( Value of multiplication in a structure power.  (Contributed by Mario
         Carneiro, 11-Jan-2015.) $)
      pwsmulrval $p |- ( ph -> ( F .xb G ) = ( F oF .x. G ) ) $=
        ( cfv vx csca csn cxp cprds co cmulr cv cmpt cof cbs cvv eqid fvexd wfn
        wcel fnconstg syl wceq pwsval syl2anc fveq2d eqtrid eleqtrd prdsmulrval
        wa fvconst2g sylan eqtr4di oveqd eqtrd pwselbas feqmptd offval2 3eqtr4d
        mpteq2dva ) AFGCUBTZHCUCUDZUEUFZUGTZUFZUAHUAUHZFTZWBGTZEUFZUIZFGDUFFGEU
        JUFAWAUAHWCWDWBVRTZUGTZUFZUIWFAUAVSUKTZVRVQVTFGHULJVSVSUMWJUMACUBUNOACI
        UPZVRHUONHCIUQURAFBWJPABKUKTWJMAKVSUKAWKHJUPKVSUSNOCVQHIJKLVQUMUTVAZVBV
        CZVDAGBWJQWMVDVTUMVEAUAHWIWEAWBHUPZVFZWHEWCWDWOWHCUGTEWOWGCUGAWKWNWGCUS
        NHCWBIVGVHVBRVIVJVPVKADVTFGADKUGTVTSAKVSUGWLVBVCVJAUAHWCWDEFGJULULOWOWB
        FUNWOWBGUNAUAHCUKTZFAWPCHBIFKJLWPUMZMNOPVLVMAUAHWPGAWPCHBIGKJLWQMNOQVLV
        MVNVO $.
    $}
  $}

  ${
    $d f g x B $.  $d f g x I $.  $d f g x O $.  $d f g x R $.  $d f g x V $.
    $d x F $.  $d x G $.  $d x ph $.  $d f g x W $.
    pwsle.y $e |- Y = ( R ^s I ) $.
    pwsle.v $e |- B = ( Base ` Y ) $.
    pwsle.o $e |- O = ( le ` R ) $.
    pwsle.l $e |- .<_ = ( le ` Y ) $.
    $( Ordering in a structure power.  (Contributed by Mario Carneiro,
       16-Aug-2015.) $)
    pwsle $p |- ( ( R e. V /\ I e. W ) -> .<_ = ( oR O i^i ( B X. B ) ) ) $=
      ( vf vg vx wcel wa cfv cple eqid cv cpr csca csn cxp cprds co cbs wss wbr
      wral copab cofr cin vex prss pwsval fveq2d eqtrid sseq2d bitrid fvconst2g
      anbi1d wceq ad4ant14 eqtr4di breqd ralbidva simpll simplr simprl pwselbas
      ffnd simprr inidm eqidd ofrfvalg bitr4d pm5.32da brinxp2 bitr4di opabbidv
      bitr3d cvv fvexd simpr snex xpexg sylancl c0 wne snnzg adantr dmxp prdsle
      cdm syl eqtrd wrel relinxp a1i dfrel4v sylib 3eqtr4d ) BFPZCGPZQZMUAZNUAZ
      UBZBUCRZCBUDZUEZUFUGZUHRZUIZOUAZXHRZXQXIRZXQXMRZSRZUJZOCUKZQZMNULZXHXIEUM
      ZAAUEUNZUJZMNULZDYGXGYDYHMNXGXHAPZXIAPZQZYCQZYDYHXGYLXPYCYLXJAUIXGXPXHXIA
      MUONUOUPXGAXOXJXGAHUHRXOJXGHXNUHBXKCFGHIXKTUQZURUSUTVAVCXGYMYLXHXIYFUJZQY
      HXGYLYCYOXGYLQZYCXRXSEUJZOCUKYOYPYBYQOCYPXQCPZQZYAEXRXSYSYABSREYSXTBSXEYR
      XTBVDXFYLCBXQFVBVEURKVFVGVHYPOCCXRXSECXHXIAAYPCBUHRZXHYPYTBCAFXHHGIYTTZJX
      EXFYLVIZXEXFYLVJZXGYJYKVKZVLVMYPCYTXIYPYTBCAFXIHGIUUAJUUBUUCXGYJYKVNZVLVM
      UUDUUECVOYSXRVPYSXSVPVQVRVSAAXHXIYFVTWAWCWBXGDXNSRZYEXGDHSRUUFLXGHXNSYNUR
      USXGOXOXNXMXKMNCUUFWDWDXNTXGBUCWEXGXFXLWDPXMWDPXEXFWFBWGCXLGWDWHWIXOTXGXL
      WJWKZXMWPCVDXEUUGXFBFWLWMCXLWNWQUUFTWOWRXGYGWSZYGYIVDUUHXGAAYFWTXAMNYGXBX
      CXD $.
    $( $j usage 'pwsle' avoids 'ax-rep'; $)

    pwsleval.r $e |- ( ph -> R e. V ) $.
    pwsleval.i $e |- ( ph -> I e. W ) $.
    pwsleval.a $e |- ( ph -> F e. B ) $.
    pwsleval.b $e |- ( ph -> G e. B ) $.
    $( Ordering in a structure power.  (Contributed by Mario Carneiro,
       16-Aug-2015.) $)
    pwsleval $p |- ( ph -> ( F .<_ G <-> A. x e. I ( F ` x ) O ( G ` x ) ) ) $=
      ( wbr cofr cxp cin cfv wral wcel wceq pwsle syl2anc breqd brinxp cbs eqid
      cv wb pwselbas ffnd inidm wa eqidd ofrfvalg 3bitr2d ) AEFHUAEFIUBZCCUCUDZ
      UAZEFVDUAZBUOZEUEZVHFUEZIUABGUFAHVEEFADJUGGKUGHVEUHQRCDGHIJKLMNOPUIUJUKAE
      CUGFCUGVGVFUPSTEFCCVDULUJABGGVIVJIGEFCCAGDUMUEZEAVKDGCJELKMVKUNZNQRSUQURA
      GVKFAVKDGCJFLKMVLNQRTUQURSTGUSAVHGUGUTZVIVAVMVJVAVBVC $.
    $( $j usage 'pwsleval' avoids 'ax-rep'; $)
  $}

  ${
    $d x A $.  $d x F $.  $d x I $.  $d x K $.  $d x R $.  $d x W $.  $d x X $.
    $d x ph $.  $d x .x. $.
    pwsvscaval.y $e |- Y = ( R ^s I ) $.
    pwsvscaval.b $e |- B = ( Base ` Y ) $.
    pwsvscaval.s $e |- .x. = ( .s ` R ) $.
    pwsvscaval.t $e |- .xb = ( .s ` Y ) $.
    pwsvscaval.f $e |- F = ( Scalar ` R ) $.
    pwsvscaval.k $e |- K = ( Base ` F ) $.
    pwsvscaval.r $e |- ( ph -> R e. V ) $.
    pwsvscaval.i $e |- ( ph -> I e. W ) $.
    pwsvscaval.a $e |- ( ph -> A e. K ) $.
    pwsvscaval.x $e |- ( ph -> X e. B ) $.
    $( Scalar multiplication in a structure power is pointwise.  (Contributed
       by Mario Carneiro, 11-Jan-2015.) $)
    pwsvscafval $p |- ( ph -> ( A .xb X ) = ( ( I X. { A } ) oF .x. X ) ) $=
      ( vx co csn cxp cprds cvsca cfv cv cmpt wcel pwsval syl2anc fveq2d eqtrid
      cof wceq oveqd cbs cvv eqid csca a1i wfn fnconstg syl eleqtrd prdsvscaval
      fvexi wa fvconst2g sylan eqtr4di mpteq2dva adantr fvexd fconstmpt feqmptd
      pwselbas offval2 eqtr4d 3eqtrd ) ABLEUEBLGHDUFUGZUHUEZUIUJZUEUDHBUDUKZLUJ
      ZWHWEUJZUIUJZUEZULZHBUFUGZLFURUEZAEWGBLAEMUIUJWGQAMWFUIADJUMZHKUMMWFUSTUA
      DGHJKMNRUNUOZUPUQUTAUDWFVAUJZWEGWGBLHIVBKWFWFVCWRVCWGVCSGVBUMAGDVDRVKVEUA
      AWPWEHVFTHDJVGVHUBALCWRUCACMVAUJWROAMWFVAWQUPUQVIVJAWMUDHBWIFUEZULWOAUDHW
      LWSAWHHUMZVLZWKFBWIXAWKDUIUJFXAWJDUIAWPWTWJDUSTHDWHJVMVNUPPVOUTVPAUDHBWIF
      WNLKIVBUAABIUMWTUBVQXAWHLVRWNUDHBULUSAUDHBVSVEAUDHDVAUJZLAXBDHCJLMKNXBVCO
      TUAUCWAVTWBWCWD $.

    pwsvscaval.j $e |- ( ph -> J e. I ) $.
    $( Scalar multiplication of a single coordinate in a structure power.
       (Contributed by Mario Carneiro, 11-Jan-2015.) $)
    pwsvscaval $p |- ( ph -> ( ( A .xb X ) ` J ) = ( A .x. ( X ` J ) ) ) $=
      ( co cfv csn cxp cof pwsvscafval fveq1d wcel wceq cbs eqid pwselbas eqidd
      ffnd wa ofc1 mpdan eqtrd ) AIBMEUFZUGIHBUHUIMFUJUFZUGZBIMUGZFUFZAIVDVEABC
      DEFGHJKLMNOPQRSTUAUBUCUDUKULAIHUMZVFVHUNUEAHBVGFMLJIUBUCAHDUOUGZMAVJDHCKM
      NLOVJUPPUAUBUDUQUSAVIUTVGURVAVBVC $.
  $}

  ${
    pwssca.y $e |- Y = ( R ^s I ) $.
    pwssca.s $e |- S = ( Scalar ` R ) $.
    $( The ring of scalars of a structure power.  (Contributed by Stefan
       O'Rear, 24-Jan-2015.) $)
    pwssca $p |- ( ( R e. V /\ I e. W ) -> S = ( Scalar ` Y ) ) $=
      ( wcel wa csn cxp cprds co csca cfv cvv eqid fvexi a1i simpr snex sylancl
      xpexg prdssca pwsval fveq2d eqtr4d ) ADIZCEIZJZBBCAKZLZMNZOPFOPUKUNUMBQQU
      NRBQIUKBAOHSTUKUJULQIUMQIUIUJUAAUBCULEQUDUCUEUKFUNOABCDEFGHUFUGUH $.
  $}

  ${
    pwsdiagel.y $e |- Y = ( R ^s I ) $.
    pwsdiagel.b $e |- B = ( Base ` R ) $.
    pwsdiagel.c $e |- C = ( Base ` Y ) $.
    $( Membership of diagonal elements in the structure power base set.
       (Contributed by Stefan O'Rear, 24-Jan-2015.) $)
    pwsdiagel $p |- ( ( ( R e. V /\ I e. W ) /\ A e. B ) ->
        ( I X. { A } ) e. C ) $=
      ( wcel wa csn cxp wf fconst6g adantl wb pwselbasb adantr mpbird ) DFLEGLM
      ZABLZMEANOZCLZEBUEPZUDUGUCEABQRUCUFUGSUDBDECFUEHGIJKTUAUB $.
  $}

  ${
    $d Y x $.  $d R x $.  $d I x $.  $d B x $.  $d C x $.  $d W x $.
    pwssnf1o.y $e |- Y = ( R ^s { I } ) $.
    pwssnf1o.b $e |- B = ( Base ` R ) $.
    pwssnf1o.f $e |- F = ( x e. B |-> ( { I } X. { x } ) ) $.
    pwssnf1o.c $e |- C = ( Base ` Y ) $.
    $( Triviality of singleton powers: set equipollence.  (Contributed by
       Stefan O'Rear, 24-Jan-2015.) $)
    pwssnf1o $p |- ( ( R e. V /\ I e. W ) -> F : B -1-1-onto-> C ) $=
      ( wcel wa wf1o csn cmap cvv cbs co fvexi simpr mapsnf1o sylancr wceq snex
      cfv pwsbas mpan2 adantr eqtr4id f1oeq3d mpbird ) DGNZFHNZOZBCEPBBFQZRUAZE
      PZUQBSNUPUTBDTKUBUOUPUCABEFSHLUDUEUQCUSBEUQCITUHZUSMUOUSVAUFZUPUOURSNVBFU
      GBDURGSIJKUIUJUKULUMUN $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Definition of the structure quotient
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c ordTop $.
  $c RR*s $.

  $( Extend class notation with the order topology. $)
  cordt $a class ordTop $.

  $( Extend class notation with the extended real number structure. $)
  cxrs $a class RR*s $.

  ${
    $d r x y $.
    $( Define the order topology, given an order ` <_ ` , written as ` r `
       below.  A closed subbasis for the order topology is given by the closed
       rays ` [ y , +oo ) = { z e. X | y <_ z } ` and
       ` ( -oo , y ] = { z e. X | z <_ y } ` , along with ` ( -oo , +oo ) = X `
       itself.  (Contributed by Mario Carneiro, 3-Sep-2015.) $)
    df-ordt $a |- ordTop = ( r e. _V |-> ( topGen ` ( fi ` ( { dom r } u. ran
       ( ( x e. dom r |-> { y e. dom r | -. y r x } ) u.
         ( x e. dom r |-> { y e. dom r | -. x r y } ) ) ) ) ) ) $.

    $( The extended real number structure.  Unlike ~ df-cnfld , the extended
       real numbers do not have good algebraic properties, so this is not
       actually a group or anything higher, even though it has just as many
       operations as ~ df-cnfld .  The main interest in this structure is in
       its ordering, which is complete and compact.  The metric described here
       is an extension of the absolute value metric, but it is not itself a
       metric because ` +oo ` is infinitely far from all other points.  The
       topology is based on the order and not the extended metric (which would
       make ` +oo ` an isolated point since there is nothing else in the ` 1 `
       -ball around it).  All components of this structure agree with ` CCfld `
       when restricted to ` RR ` .  (Contributed by Mario Carneiro,
       20-Aug-2015.) $)
    df-xrs $a |- RR*s = ( { <. ( Base ` ndx ) , RR* >. ,
        <. ( +g ` ndx ) , +e >. , <. ( .r ` ndx ) , *e >. } u.
        { <. ( TopSet ` ndx ) , ( ordTop ` <_ ) >. ,
          <. ( le ` ndx ) , <_ >. ,
          <. ( dist ` ndx ) , ( x e. RR* , y e. RR* |->
            if ( x <_ y , ( y +e -e x ) , ( x +e -e y ) ) ) >. } ) $.
  $}

  $c "s $. $( Image structure $)
  $c /s $. $( Quotient structure $)
  $c qTop $. $( Quotient topology $)
  $c Xs. $. $( Binary structure $)

  $( Extend class notation with the quotient topology function. $)
  cqtop $a class qTop $.

  $( Image structure function. $)
  cimas $a class "s $.

  $( Quotient structure function. $)
  cqus $a class /s $.

  $( Binary product structure function. $)
  cxps $a class Xs. $.

  ${
    $d e f g h i j n p q r s v x y $.
    $( Define the quotient topology given a function ` f ` and topology ` j `
       on the domain of ` f ` .  (Contributed by Mario Carneiro,
       23-Mar-2015.) $)
    df-qtop $a |- qTop = ( j e. _V , f e. _V |->
       { s e. ~P ( f " U. j ) | ( ( `' f " s ) i^i U. j ) e. j } ) $.

    $( Define an image structure, which takes a structure and a function on the
       base set, and maps all the operations via the function.  For this to
       work properly ` f ` must either be injective or satisfy the
       well-definedness condition ` f ( a ) = f ( c ) /\ f ( b ) = f ( d ) -> `
       ` f ( a + b ) = f ( c + d ) ` for each relevant operation.

       Note that although we call this an "image" by association to ~ df-ima ,
       in order to keep the definition simple we consider only the case when
       the domain of ` F ` is equal to the base set of ` R ` .  Other cases can
       be achieved by restricting ` F ` (with ~ df-res ) and/or ` R ` ( with
       ~ df-ress ) to their common domain.  (Contributed by Mario Carneiro,
       23-Feb-2015.)  (Revised by AV, 6-Oct-2020.) $)
    df-imas $a |- "s = ( f e. _V , r e. _V |-> [_ ( Base ` r ) / v ]_
  ( ( { <. ( Base ` ndx ) , ran f >. ,
        <. ( +g ` ndx ) , U_ p e. v U_ q e. v
     { <. <. ( f ` p ) , ( f ` q ) >. , ( f ` ( p ( +g ` r ) q ) ) >. } >. ,
        <. ( .r ` ndx ) , U_ p e. v U_ q e. v
     { <. <. ( f ` p ) , ( f ` q ) >. , ( f ` ( p ( .r ` r ) q ) ) >. } >. } u.
      { <. ( Scalar ` ndx ) , ( Scalar ` r ) >. ,
        <. ( .s ` ndx ) , U_ q e. v ( p e. ( Base ` ( Scalar ` r ) ) ,
           x e. { ( f ` q ) } |-> ( f ` ( p ( .s ` r ) q ) ) ) >. ,
        <. ( .i ` ndx ) , U_ p e. v U_ q e. v
     { <. <. ( f ` p ) , ( f ` q ) >. , ( p ( .i ` r ) q ) >. } >. } ) u.
      { <. ( TopSet ` ndx ) , ( ( TopOpen ` r ) qTop f ) >. ,
        <. ( le ` ndx ) , ( ( f o. ( le ` r ) ) o. `' f ) >. ,
        <. ( dist ` ndx ) , ( x e. ran f , y e. ran f |-> inf ( U_ n e. NN
         ran ( g e. { h e. ( ( v X. v ) ^m ( 1 ... n ) ) |
        ( ( f ` ( 1st ` ( h ` 1 ) ) ) = x /\ ( f ` ( 2nd ` ( h ` n ) ) ) = y /\
         A. i e. ( 1 ... ( n - 1 ) ) ( f ` ( 2nd ` ( h ` i ) ) ) =
           ( f ` ( 1st ` ( h ` ( i + 1 ) ) ) ) ) } |->
           ( RR*s gsum ( ( dist ` r ) o. g ) ) ) , RR* , < ) ) >. } ) ) $.

    $( Define a quotient ring (or quotient group), which is a special case of
       an image structure ~ df-imas where the image function is
       ` x |-> [ x ] e ` .  (Contributed by Mario Carneiro, 23-Feb-2015.) $)
    df-qus $a |- /s = ( r e. _V , e e. _V |->
      ( ( x e. ( Base ` r ) |-> [ x ] e ) "s r ) ) $.

    $( Define a binary product on structures.  (Contributed by Mario Carneiro,
       14-Aug-2015.)  (Revised by Jim Kingdon, 25-Sep-2023.) $)
    df-xps $a |- Xs. = ( r e. _V , s e. _V |->
        ( `' ( x e. ( Base ` r ) , y e. ( Base ` s )
        |-> { <. (/) , x >. , <. 1o , y >. } )
        "s ( ( Scalar ` r ) Xs_ { <. (/) , r >. , <. 1o , s >. } ) ) ) $.
  $}

  ${
    $d f r v .<_ $.  $d f r v B $.  $d f r v D $.  $d f r v G $.  $d f r v O $.
    $d f g h i n p q r v x y F $.  $d f g h i n p q r v x y R $.  $d h p q V $.
    $d f r v I $.  $d f r v .+b $.  $d f g h i n p q r v x y ph $.
    $d f r v .(x) $.  $d f r v .xb $.
    imasval.u $e |- ( ph -> U = ( F "s R ) ) $.
    imasval.v $e |- ( ph -> V = ( Base ` R ) ) $.
    imasval.p $e |- .+ = ( +g ` R ) $.
    imasval.m $e |- .X. = ( .r ` R ) $.
    imasval.g $e |- G = ( Scalar ` R ) $.
    imasval.k $e |- K = ( Base ` G ) $.
    imasval.q $e |- .x. = ( .s ` R ) $.
    imasval.i $e |- ., = ( .i ` R ) $.
    imasval.j $e |- J = ( TopOpen ` R ) $.
    imasval.e $e |- E = ( dist ` R ) $.
    imasval.n $e |- N = ( le ` R ) $.
    imasval.a $e |- ( ph -> .+b = U_ p e. V U_ q e. V
     { <. <. ( F ` p ) , ( F ` q ) >. , ( F ` ( p .+ q ) ) >. } ) $.
    imasval.t $e |- ( ph -> .xb = U_ p e. V U_ q e. V
     { <. <. ( F ` p ) , ( F ` q ) >. , ( F ` ( p .X. q ) ) >. } ) $.
    imasval.s $e |- ( ph -> .(x) = U_ q e. V ( p e. K ,
           x e. { ( F ` q ) } |-> ( F ` ( p .x. q ) ) ) ) $.
    imasval.w $e |- ( ph -> I = U_ p e. V U_ q e. V
     { <. <. ( F ` p ) , ( F ` q ) >. , ( p ., q ) >. } ) $.
    imasval.o $e |- ( ph -> O = ( J qTop F ) ) $.
    imasval.d $e |- ( ph -> D = ( x e. B , y e. B |-> inf ( U_ n e. NN
         ran ( g e. { h e. ( ( V X. V ) ^m ( 1 ... n ) ) |
        ( ( F ` ( 1st ` ( h ` 1 ) ) ) = x /\ ( F ` ( 2nd ` ( h ` n ) ) ) = y /\
         A. i e. ( 1 ... ( n - 1 ) ) ( F ` ( 2nd ` ( h ` i ) ) ) =
           ( F ` ( 1st ` ( h ` ( i + 1 ) ) ) ) ) } |->
         ( RR*s gsum ( E o. g ) ) ) , RR* , < ) ) ) $.
    imasval.l $e |- ( ph -> .<_ = ( ( F o. N ) o. `' F ) ) $.
    imasval.f $e |- ( ph -> F : V -onto-> B ) $.
    imasval.r $e |- ( ph -> R e. Z ) $.
    $( Value of an image structure.  (Contributed by Mario Carneiro,
       23-Feb-2015.)  (Revised by Mario Carneiro, 11-Jul-2015.)  (Revised by
       Thierry Arnoux, 16-Jun-2019.)  (Revised by AV, 6-Oct-2020.) $)
    imasval $p |- ( ph -> U = ( ( { <. ( Base ` ndx ) , B >. ,
        <. ( +g ` ndx ) , .+b >. , <. ( .r ` ndx ) , .xb >. } u.
        { <. ( Scalar ` ndx ) , G >. , <. ( .s ` ndx ) , .(x) >. ,
          <. ( .i ` ndx ) , I >. } ) u.
        { <. ( TopSet ` ndx ) , O >. , <. ( le ` ndx ) , .<_ >. ,
        <. ( dist ` ndx ) , D >. } ) ) $=
      ( vf vr vv cimas cnx cbs cfv cop cplusg cmulr ctp csca cvsca cip cun cple
      co cds cvv cv crn csn ciun cmpo ctopn cqtop ccom ccnv cn c1 c1st wceq cfz
      c2nd wral w3a cxp cmap crab cxrs cgsu cmpt cxr clt cinf wa rneqd ad2antrr
      a1i syl eqtrd opeq2d fveq2d 3eqtr4d fveq1d opeq12d eqtr4di oveqd iuneq12d
      fveq12d sneqd eqtr4d tpeq123d mpoeq123dv iuneq2d uneq12d coeq12d eqeq1d
      tpex cts caddc cmin csb df-imas fvexd simplrl wfo simplrr iuneq1d oveq12d
      simpr cnveqd sqxpeqd oveq1d eqeq12d ralbidv 3anbi123d rabeqbidv mpteq12dv
      forn coeq1d oveq2d infeq1d csbied wf fvex eqeltrdi fexd elexd wcel ovmpod
      fof unex ) AMSHVOWHVPVQVRZDVSZVPVTVRZGVSZVPWAVRZIVSZWBZVPWCVRZTVSZVPWDVRZ
      LVSZVPWEVRZUBVSZWBZWFZVPUUAVRZUGVSZVPWGVRZUEVSZVPWIVRZEVSZWBZWFZULAVLVMSH
      WJWJVNVMWKZVQVRZUVOVLWKZWLZVSZUVQUKVNWKZUJUXCUKWKZUWTVRZUJWKZUWTVRZVSZUXD
      UXFUWRVTVRZWHZUWTVRZVSZWMZWNZWNZVSZUVSUKUXCUJUXCUXHUXDUXFUWRWAVRZWHZUWTVR
      ZVSZWMZWNZWNZVSZWBZUWBUWRWCVRZVSZUWDUJUXCUKBUYFVQVRZUXGWMZUXDUXFUWRWDVRZW
      HZUWTVRZWOZWNZVSZUWFUKUXCUJUXCUXHUXDUXFUWRWEVRZWHZVSZWMZWNZWNZVSZWBZWFZUW
      JUWRWPVRZUWTWQWHZVSZUWLUWTUWRWGVRZWRZUWTWSZWRZVSZUWNBCUXAUXAQWTNXAOWKZVRX
      BVRZUWTVRZBWKZXCZQWKZVUMVRXEVRZUWTVRZCWKZXCZPWKZVUMVRXEVRZUWTVRZVVCXAUUBW
      HVUMVRXBVRZUWTVRZXCZPXAVURXAUUCWHXDWHZXFZXGZOUXCUXCXHZXAVURXDWHZXIWHZXJZX
      KUWRWIVRZNWKZWRZXLWHZXMZWLZWNZXNXOXPZWOZVSZWBZWFZUUDZUWQVOWJVOVLVMWJWJVWH
      WOXCABCVNVLNOPQVMUJUKUUEXTAUWTSXCZUWRHXCZXQZXQZVNUWSVWGUWQWJVWLUWRVQUUFVW
      LUXCUWSXCZXQZVUDUWIVWFUWPVWNUYEUWAVUCUWHVWNUXBUVPUXPUVRUYDUVTVWNUXADUVOVW
      NUXASWLZDVWNUWTSAVWIVWJVWMUUGZXRAVWODXCZVWKVWMAUHDSUUHZVWQVJUHDSUVAYAXSYB
      ZYCVWNUXOGUVQVWNUXOUKUHUJUHUXDSVRZUXFSVRZVSZUXDUXFFWHZSVRZVSZWMZWNZWNZGVW
      NUKUXCUHUXNVXGVWNUWSHVQVRZUXCUHVWNUWRHVQAVWIVWJVWMUUIZYDVWLVWMUULAUHVXIXC
      VWKVWMUMXSYEZVWNUJUXCUHUXMVXFVXKVWNUXLVXEVWNUXHVXBUXKVXDVWNUXEVWTUXGVXAVW
      NUXDUWTSVWPYFVWNUXFUWTSVWPYFZYGZVWNUXJVXCUWTSVWPVWNUXIFUXDUXFVWNUXIHVTVRF
      VWNUWRHVTVXJYDUNYHYIYKYGYLYJYJAGVXHXCVWKVWMVCXSYMYCVWNUYCIUVSVWNUYCUKUHUJ
      UHVXBUXDUXFKWHZSVRZVSZWMZWNZWNZIVWNUKUXCUHUYBVXRVXKVWNUJUXCUHUYAVXQVXKVWN
      UXTVXPVWNUXHVXBUXSVXOVXMVWNUXRVXNUWTSVWPVWNUXQKUXDUXFVWNUXQHWAVRKVWNUWRHW
      AVXJYDUOYHYIYKYGYLYJYJAIVXSXCVWKVWMVDXSYMYCYNVWNUYGUWCUYOUWEVUBUWGVWNUYFT
      UWBVWNUYFHWCVRTVWNUWRHWCVXJYDUPYHZYCVWNUYNLUWDVWNUJUHUYMWNUJUHUKBUDVXAWMZ
      UXDUXFJWHZSVRZWOZWNZUYNLVWNUJUHUYMVYDVWNUKBUYHUYIUYLUDVYAVYCVWNUYHTVQVRUD
      VWNUYFTVQVXTYDUQYHVWNUXGVXAVXLYLVWNUYKVYBUWTSVWPVWNUYJJUXDUXFVWNUYJHWDVRJ
      VWNUWRHWDVXJYDURYHYIYKYOYPVWNUJUXCUHUYMVXKUUJALVYEXCVWKVWMVEXSYEYCVWNVUAU
      BUWFVWNVUAUKUHUJUHVXBUXDUXFUAWHZVSZWMZWNZWNZUBVWNUKUXCUHUYTVYIVXKVWNUJUXC
      UHUYSVYHVXKVWNUYRVYGVWNUXHVXBUYQVYFVXMVWNUYPUAUXDUXFVWNUYPHWEVRUAVWNUWRHW
      EVXJYDUSYHYIYGYLYJYJAUBVYJXCVWKVWMVFXSYMYCYNYQVWNVUGUWKVULUWMVWEUWOVWNVUF
      UGUWJVWNVUFUCSWQWHZUGVWNVUEUCUWTSWQVWNVUEHWPVRUCVWNUWRHWPVXJYDUTYHVWPUUKA
      UGVYKXCVWKVWMVGXSYMYCVWNVUKUEUWLVWNVUKSUFWRZSWSZWRZUEVWNVUIVYLVUJVYMVWNUW
      TSVUHUFVWPVWNVUHHWGVRUFVWNUWRHWGVXJYDVBYHYRVWNUWTSVWPUUMYRAUEVYNXCVWKVWMV
      IXSYMYCVWNVWDEUWNVWNVWDBCDDQWTNVUNSVRZVUPXCZVUSSVRZVVAXCZVVDSVRZVVFSVRZXC
      ZPVVIXFZXGZOUHUHXHZVVMXIWHZXJZXKRVVQWRZXLWHZXMZWLZWNZXNXOXPZWOZEVWNBCUXAU
      XAVWCDDWULVWSVWSVWNXNVWBWUKXOVWNQWTVWAWUJVWNVVTWUIVWNNVVOVVSWUFWUHVWNVVKW
      UCOVVNWUEVWNVVLWUDVVMXIVWNUXCUHVXKUUNUUOVWNVUQVYPVVBVYRVVJWUBVWNVUOVYOVUP
      VWNVUNUWTSVWPYFYSVWNVUTVYQVVAVWNVUSUWTSVWPYFYSVWNVVHWUAPVVIVWNVVEVYSVVGVY
      TVWNVVDUWTSVWPYFVWNVVFUWTSVWPYFUUPUUQUURUUSVWNVVRWUGXKXLVWNVVPRVVQVWNVVPH
      WIVRRVWNUWRHWIVXJYDVAYHUVBUVCUUTXRYPUVDYOAEWUMXCVWKVWMVHXSYMYCYNYQUVEAUHD
      WJSAVWRUHDSUVFVJUHDSUVMYAAUHVXIWJUMHVQUVGUVHUVIAHUIVKUVJUWQWJUVKAUWIUWPUW
      AUWHUVPUVRUVTYTUWCUWEUWGYTUVNUWKUWMUWOYTUVNXTUVLYB $.
  $}

  ${
    $d g h i n p q u v w x y z F $.  $d g h i n p q u v w x y z R $.  $d x U $.
    $d x y B $.  $d x y E $.  $d g h i n p q u v w x y z ph $.  $d h n x y X $.
    $d p x K $.  $d g x y S $.  $d g h p q w z V $.  $d h n x y Y $.
    imasbas.u $e |- ( ph -> U = ( F "s R ) ) $.
    imasbas.v $e |- ( ph -> V = ( Base ` R ) ) $.
    imasbas.f $e |- ( ph -> F : V -onto-> B ) $.
    imasbas.r $e |- ( ph -> R e. Z ) $.
    $( The base set of an image structure.  (Contributed by Mario Carneiro,
       23-Feb-2015.)  (Revised by Mario Carneiro, 11-Jul-2015.)  (Revised by
       Thierry Arnoux, 16-Jun-2019.)  (Revised by AV, 6-Oct-2020.) $)
    imasbas $p |- ( ph -> B = ( Base ` U ) ) $=
      ( cfv cnx cop cv co ciun c1 eqid eqidd vp vq vx vy vn vg vh vi cbs cplusg
      csn cmulr ctp csca cvsca cmpo cip cun cts ctopn cqtop cple ccom ccnv c1st
      cds cn wceq c2nd caddc cmin cfz wral w3a cxp cmap crab cxrs cgsu cmpt crn
      cxr clt cinf cvv c2 cdc imasval imasvalstr baseid snsstp1 ssun1 sstri wfo
      wcel fvex eqeltrdi focdmex sylc strfv3 eqcomd ) ADUILZBAXBBMUILBNZMUJLUAF
      UBFUAOZELUBOZELZNZXDXECUJLZPELNUKQQZNZMULLUAFUBFXGXDXECULLZPELNUKQQZNZUMZ
      MUNLCUNLZNMUOLUBFUAUCXOUILZXFUKXDXECUOLZPELUPQZNMUQLUAFUBFXGXDXECUQLZPNUK
      QQZNUMZURZMUSLCUTLZEVAPZNMVBLECVBLZVCEVDVCZNMVFLUCUDBBUEVGUFRUGOZLVELELUC
      OVHUEOZYGLVILELUDOVHUHOZYGLVILELYIRVJPYGLVELELVHUHRYHRVKPVLPVMVNUGFFVORYH
      VLPVPPVQVRCVFLZUFOVCVSPVTWAQWBWCWDUPZNUMZURZDUIWERRWFWGNAUCUDBYKXHXICXLXQ
      XKXRDUFUGUHUEYJEXOXSXTYCXPYFYEYDFGUBUAHIXHSXKSXOSXPSXQSXSSYCSYJSYESAXITAX
      LTAXRTAXTTAYDTAYKTAYFTJKWHBYKXIXOXRXLYMXTYFYDYMSWIWJXCUKZYBYMYNXNYBXCXJXM
      WKXNYAWLWMYBYLWLWMAFWEWOFBEWNBWEWOAFCUILWEICUIWPWQJFBWEEWRWSXBSWTXA $.

    ${
      imasds.e $e |- E = ( dist ` R ) $.
      imasds.d $e |- D = ( dist ` U ) $.
      $( The distance function of an image structure.  (Contributed by Mario
         Carneiro, 23-Feb-2015.)  (Revised by Mario Carneiro, 11-Jul-2015.)
         (Revised by Thierry Arnoux, 16-Jun-2019.)  (Revised by AV,
         6-Oct-2020.) $)
      imasds $p |- ( ph -> D = ( x e. B , y e. B |-> inf ( U_ n e. NN
         ran ( g e. { h e. ( ( V X. V ) ^m ( 1 ... n ) ) |
        ( ( F ` ( 1st ` ( h ` 1 ) ) ) = x /\ ( F ` ( 2nd ` ( h ` n ) ) ) = y /\
         A. i e. ( 1 ... ( n - 1 ) ) ( F ` ( 2nd ` ( h ` i ) ) ) =
           ( F ` ( 1st ` ( h ` ( i + 1 ) ) ) ) ) } |->
         ( RR*s gsum ( E o. g ) ) ) , RR* , < ) ) ) $=
        ( vp vq cn c1 cv cfv c1st wceq c2nd caddc co cmin cfz wral w3a cxp cmap
        crab cxrs ccom cgsu cmpt crn ciun cxr clt cinf cnx cbs cop cplusg cmulr
        cmpo csn ctp csca cvsca cip cun cts ctopn cple ccnv cds cvv c2 cdc eqid
        cqtop eqidd imasval imasvalstr dsid snsstp3 ssun2 wcel wfo fvex focdmex
        sstri eqeltrdi sylc mpoexga syl2anc strfv3 ) AEBCDDKUDHUEIUFZUGUHUGMUGB
        UFUIKUFZXGUGUJUGMUGCUFUIJUFZXGUGUJUGMUGXIUEUKULXGUGUHUGMUGUIJUEXHUEUMUL
        UNULUOUPINNUQUEXHUNULURULUSUTLHUFVAVBULVCVDVEVFVGVHZVNZVIVJUGDVKVIVLUGU
        BNUCNUBUFZMUGUCUFZMUGZVKZXLXMFVLUGZULMUGVKVOVEVEZVKVIVMUGUBNUCNXOXLXMFV
        MUGZULMUGVKVOVEVEZVKVPVIVQUGFVQUGZVKVIVRUGUCNUBBXTVJUGZXNVOXLXMFVRUGZUL
        MUGVNVEZVKVIVSUGUBNUCNXOXLXMFVSUGZULVKVOVEVEZVKVPVTZVIWAUGFWBUGZMWJULZV
        KZVIWCUGMFWCUGZVAMWDVAZVKZVIWEUGXKVKZVPZVTZGWEWFUEUEWGWHVKABCDXKXPXQFXS
        YBXRYCGHIJKLMXTYDYEYGYAYKYJYHNOUCUBPQXPWIXRWIXTWIYAWIYBWIYDWIYGWITYJWIA
        XQWKAXSWKAYCWKAYEWKAYHWKAXKWKAYKWKRSWLDXKXQXTYCXSYOYEYKYHYOWIWMWNYMVOYN
        YOYIYLYMWOYNYFWPXAADWFWQZYPXKWFWQANWFWQNDMWRYPANFVJUGWFQFVJWSXBRNDWFMWT
        XCZYQBCDDXJWFWFXDXEUAXF $.

      $( The distance function is a function on the base set.  (Contributed by
         Mario Carneiro, 20-Aug-2015.)  (Proof shortened by AV, 6-Oct-2020.) $)
      imasdsfn $p |- ( ph -> D Fn ( B X. B ) ) $=
        ( vx c1 cv cfv co vy vn vg vh vi cxp wfn c1st wceq c2nd caddc cmin wral
        cfz w3a cmap crab cxrs ccom cgsu cmpt crn ciun cxr clt cinf cmpo xrltso
        cn eqid infex fnmpoi imasds fneq1d mpbiri ) ACBBUFZUGPUABBUBVIUCQUDRZSU
        HSGSPRUIUBRZVQSUJSGSUARUIUERZVQSUJSGSVSQUKTVQSUHSGSUIUEQVRQULTUNTUMUOUD
        HHUFQVRUNTUPTUQURFUCRUSUTTVAVBVCZVDVEVFZVGZVPUGPUABBWAWBWBVJVDVTVEVHVKV
        LAVPCWBAPUABCDEUCUDUEUBFGHIJKLMNOVMVNVO $.

      imasdsval.x $e |- ( ph -> X e. B ) $.
      imasdsval.y $e |- ( ph -> Y e. B ) $.
      imasdsval.s $e |- S = { h e. ( ( V X. V ) ^m ( 1 ... n ) ) |
        ( ( F ` ( 1st ` ( h ` 1 ) ) ) = X /\ ( F ` ( 2nd ` ( h ` n ) ) ) = Y /\
         A. i e. ( 1 ... ( n - 1 ) ) ( F ` ( 2nd ` ( h ` i ) ) ) =
           ( F ` ( 1st ` ( h ` ( i + 1 ) ) ) ) ) } $.
      $( The distance function of an image structure.  (Contributed by Mario
         Carneiro, 20-Aug-2015.)  (Revised by AV, 6-Oct-2020.) $)
      imasdsval $p |- ( ph -> ( X D Y ) = inf ( U_ n e. NN
        ran ( g e. S |-> ( RR*s gsum ( E o. g ) ) ) , RR* , < ) ) $=
        ( vx vy cn c1 cv cfv c1st wceq c2nd caddc co cmin cfz wral w3a cxp cmap
        crab cxrs ccom cgsu cmpt crn ciun cxr clt cinf imasds wa simplrl eqeq2d
        cvv wcel simplrr 3anbi12d rabbidv eqtr4di mpteq1d rneqd iuneq2dv xrltso
        infeq1d infex a1i ovmpod ) AUFUGNOBBJUHGUIHUJZUKULUKLUKZUFUJZUMZJUJZWKU
        KUNUKLUKZUGUJZUMZIUJZWKUKUNUKLUKWSUIUOUPWKUKULUKLUKUMIUIWOUIUQUPURUPUSZ
        UTZHMMVAUIWOURUPVBUPZVCZVDKGUJVEVFUPZVGZVHZVIZVJVKVLJUHGEXDVGZVHZVIZVJV
        KVLZCVQAUFUGBCDFGHIJKLMPQRSTUAUBVMAWMNUMZWQOUMZVNVNZVJXGXJVKXNJUHXFXIXN
        WOUHVRZVNZXEXHXPGXCEXDXPXCWLNUMZWPOUMZWTUTZHXBVCEXPXAXSHXBXPWNXQWRXRWTX
        PWMNWLAXLXMXOVOVPXPWQOWPAXLXMXOVSVPVTWAUEWBWCWDWEWGUCUDXKVQVRAVJXJVKWFW
        HWIWJ $.

      imasds.u $e |- T = ( E |` ( V X. V ) ) $.
      $( The distance function of an image structure.  (Contributed by Mario
         Carneiro, 20-Aug-2015.)  (Revised by AV, 6-Oct-2020.) $)
      imasdsval2 $p |- ( ph -> ( X D Y ) = inf ( U_ n e. NN
        ran ( g e. S |-> ( RR*s gsum ( T o. g ) ) ) , RR* , < ) ) $=
        ( co cn cxrs cv ccom cgsu cmpt crn ciun cxr clt cinf imasdsval wceq cxp
        wcel cres coeq1i c1 cfz cmap wf wss cfv c1st c2nd caddc cmin w3a ssrab3
        wral sseli elmapi frn cores 4syl eqtrid oveq2d mpteq2ia iuneq2i infeq1i
        rneqi a1i eqtr4di ) AOPCUHKUIHEUJLHUKZULZUMUHZUNZUOZUPZUQURUSKUIHEUJFWL
        ULZUMUHZUNZUOZUPZUQURUSABCDEGHIJKLMNOPQRSTUAUBUCUDUEUFUTUQXBWQURKUIXAWP
        XAWPVAKUKZUIVCWTWOHEWSWNWLEVCZWRWMUJUMXDWRLNNVBZVDZWLULZWMFXFWLUGVEXDWL
        XEVFXCVGUHZVHUHZVCXHXEWLVIWLUOXEVJXGWMVAEXIWLVFIUKZVKVLVKMVKOVAXCXJVKVM
        VKMVKPVAJUKZXJVKVMVKMVKXKVFVNUHXJVKVLVKMVKVAJVFXCVFVOUHVGUHVRVPIXIEUFVQ
        VSWLXEXHVTXHXEWLWALWLXEWBWCWDWEWFWIWJWGWHWK $.
    $}

    ${
      imasplusg.p $e |- .+ = ( +g ` R ) $.
      imasplusg.a $e |- .+b = ( +g ` U ) $.
      $( The group operation in an image structure.  (Contributed by Mario
         Carneiro, 23-Feb-2015.)  (Revised by Mario Carneiro, 11-Jul-2015.)
         (Revised by Thierry Arnoux, 16-Jun-2019.) $)
      imasplusg $p |- ( ph -> .+b = U_ p e. V U_ q e. V
        { <. <. ( F ` p ) , ( F ` q ) >. , ( F ` ( p .+ q ) ) >. } ) $=
        ( cfv cop cvv vx vy vg vh vi vn cv co csn ciun cnx cbs cplusg cmulr ctp
        csca cvsca cmpo cip cun cts ctopn cqtop cple ccom ccnv cds c1 cdc eqidd
        c2 eqid imasds imasval imasvalstr plusgid snsstp2 ssun1 sstri wcel wral
        fvex eqeltrdi snex rgenw iunexg sylancl ralrimivw syl2anc strfv3 ) ADKH
        JHKUGZGRJUGZGRZSZWKWLCUHGRSZUIZUJZUJZUKULRBSZUKUMRWRSZUKUNRKHJHWNWKWLEU
        NRZUHGRSUIUJUJZSZUOZUKUPREUPRZSUKUQRJHKUAXEULRZWMUIWKWLEUQRZUHGRURUJZSU
        KUSRKHJHWNWKWLEUSRZUHSUIUJUJZSUOZUTZUKVAREVBRZGVCUHZSUKVDRGEVDRZVEGVFVE
        ZSUKVGRFVGRZSUOZUTZFUMTVHVHVKVISAUAUBBXQCWREXBXGXAXHFUCUDUEUFEVGRZGXEXI
        XJXMXFXPXOXNHIJKLMPXAVLXEVLXFVLXGVLXIVLXMVLXTVLZXOVLAWRVJAXBVJAXHVJAXJV
        JAXNVJAUAUBBXQEFUCUDUEUFXTGHILMNOYAXQVLVMAXPVJNOVNBXQWRXEXHXBXSXJXPXNXS
        VLVOVPWTUIZXLXSYBXDXLWSWTXCVQXDXKVRVSXLXRVRVSAHTVTZWQTVTZKHWAWRTVTAHEUL
        RTMEULWBWCZAYDKHAYCWPTVTZJHWAYDYEYFJHWOWDWEJHWPTTWFWGWHKHWQTTWFWIQWJ $.
    $}

    ${
      imasmulr.p $e |- .x. = ( .r ` R ) $.
      imasmulr.t $e |- .xb = ( .r ` U ) $.
      $( The ring multiplication in an image structure.  (Contributed by Mario
         Carneiro, 23-Feb-2015.)  (Revised by Mario Carneiro, 11-Jul-2015.)
         (Revised by Thierry Arnoux, 16-Jun-2019.) $)
      imasmulr $p |- ( ph -> .xb = U_ p e. V U_ q e. V
        { <. <. ( F ` p ) , ( F ` q ) >. , ( F ` ( p .x. q ) ) >. } ) $=
        ( cfv cop eqid vx vy vg vh vi vn cv co csn ciun cnx cbs cplusg ctp csca
        cmulr cvsca cmpo cip cun cts ctopn cqtop cple ccom cds cvv c1 imasplusg
        ccnv c2 cdc eqidd imasds imasval imasvalstr mulridx snsstp3 ssun1 sstri
        wcel wral fvex eqeltrdi rgenw iunexg sylancl ralrimivw syl2anc strfv3
        snex ) ADKHJHKUGZGRJUGZGRZSZWLWMEUHGRSZUIZUJZUJZUKULRBSZUKUMRFUMRZSZUKU
        PRWSSZUNZUKUORCUORZSUKUQRJHKUAXEULRZWNUIWLWMCUQRZUHGRURUJZSUKUSRKHJHWOW
        LWMCUSRZUHSUIUJUJZSUNZUTZUKVARCVBRZGVCUHZSUKVDRGCVDRZVEGVJVEZSUKVFRFVFR
        ZSUNZUTZFUPVGVHVHVKVLSAUAUBBXQCUMRZXACWSXGEXHFUCUDUEUFCVFRZGXEXIXJXMXFX
        PXOXNHIJKLMXTTZPXETXFTXGTXITXMTYATZXOTABXTXACFGHIJKLMNOYBXATVIAWSVMAXHV
        MAXJVMAXNVMAUAUBBXQCFUCUDUEUFYAGHILMNOYCXQTVNAXPVMNOVOBXQXAXEXHWSXSXJXP
        XNXSTVPVQXCUIZXLXSYDXDXLWTXBXCVRXDXKVSVTXLXRVSVTAHVGWAZWRVGWAZKHWBWSVGW
        AAHCULRVGMCULWCWDZAYFKHAYEWQVGWAZJHWBYFYGYHJHWPWKWEJHWQVGVGWFWGWHKHWRVG
        VGWFWIQWJ $.
    $}

    ${
      imassca.g $e |- G = ( Scalar ` R ) $.
      $( The scalar field of an image structure.  (Contributed by Mario
         Carneiro, 23-Feb-2015.)  (Revised by Thierry Arnoux, 16-Jun-2019.) $)
      imassca $p |- ( ph -> G = ( Scalar ` U ) ) $=
        ( vq vp cnx cfv cop csca eqid vx vy vg vh vi cbs cplusg cmulr ctp cvsca
        vn cv csn cmpo ciun cip cun cts ctopn cqtop cple ccom ccnv cds cvv wcel
        co wceq fvexi c1 imasvalstr scaid snsstp1 ssun2 sstri ssun1 strfv ax-mp
        c2 cdc imasplusg imasmulr eqidd imasds imasval fveq2d eqtr4id ) AFPUFQB
        RPUGQDUGQZRPUHQDUHQZRUIZPSQFRZPUJQNGOUAFUFQZNULZEQZUMOULZWMCUJQZVGEQUNU
        OZRZPUPQOGNGWOEQWNRWOWMCUPQZVGRUMUOUOZRZUIZUQZPURQCUSQZEUTVGZRPVAQECVAQ
        ZVBEVCVBZRPVDQDVDQZRUIZUQZSQZDSQFVEVFFXKVHFCSMVIFXJSVEVJVJVSVTRBXHWHFWQ
        WIXJWTXGXEXJTVKVLWKUMZXCXJXLXBXCWKWRXAVMXBWJVNVOXCXIVPVOVQVRADXJSAUAUBB
        XHCUGQZWHCWIWPCUHQZWQDUCUDUEUKCVDQZEFWSWTXDWLXGXFXEGHNOIJXMTZXNTZMWLTWP
        TWSTXDTXOTZXFTABXMWHCDEGHNOIJKLXPWHTWAABCWIXNDEGHNOIJKLXQWITWBAWQWCAWTW
        CAXEWCAUAUBBXHCDUCUDUEUKXOEGHIJKLXRXHTWDAXGWCKLWEWFWG $.

      imasvsca.k $e |- K = ( Base ` G ) $.
      imasvsca.q $e |- .x. = ( .s ` R ) $.
      imasvsca.s $e |- .xb = ( .s ` U ) $.
      $( The scalar multiplication operation of an image structure.
         (Contributed by Mario Carneiro, 23-Feb-2015.)  (Revised by Thierry
         Arnoux, 16-Jun-2019.) $)
      imasvsca $p |- ( ph -> .xb = U_ q e. V ( p e. K ,
           x e. { ( F ` q ) } |-> ( F ` ( p .x. q ) ) ) ) $=
        ( vy vz vw vv vu cv cfv csn cmpo ciun cnx cbs cop cplusg cmulr ctp csca
        co cvsca cip cun cts ctopn cqtop cple ccom ccnv cds cvv cdc eqid fveq2i
        c1 c2 eqtri imasplusg imasmulr imasds imasval imasvalstr vscaid snsstp2
        eqidd ssun2 ssun1 sstri wcel wral fvex eqeltrdi fvexi snex mpoex iunexg
        rgenw sylancl strfv3 ) AEMKNBJMUHZHUIZUJZNUHZWTFUTHUIZUKZULZUMUNUICUOUM
        UPUIGUPUIZUOUMUQUIGUQUIZUOURZUMUSUIDUSUIZUOZUMVAUIXFUOZUMVBUINKMKXCHUIX
        AUOXCWTDVBUIZUTUOUJULULZUOZURZVCZUMVDUIDVEUIZHVFUTZUOUMVGUIHDVGUIZVHHVI
        VHZUOUMVJUIGVJUIZUOURZVCZGVAVKVOVOVPVLUOABUCCYBDUPUIZXGDXHFDUQUIZXFGUDU
        EUFUGDVJUIZHXJXMXNXRJYAXTXSKLMNOPYEVMZYFVMZXJVMJIUNUIXJUNUITIXJUNSVNVQU
        AXMVMXRVMYGVMZXTVMACYEXGDGHKLMNOPQRYHXGVMVRACDXHYFGHKLMNOPQRYIXHVMVSAXF
        WEAXNWEAXSWEABUCCYBDGUDUEUFUGYGHKLOPQRYJYBVMVTAYAWEQRWACYBXGXJXFXHYDXNY
        AXSYDVMWBWCXLUJXPYDXKXLXOWDXPXQYDXPXIWFXQYCWGWHWHAKVKWIXEVKWIZMKWJXFVKW
        IAKDUNUIVKPDUNWKWLYKMKNBJXBXDJIUNTWMXAWNWOWQMKXEVKVKWPWRUBWS $.
    $}

    ${
      imasip.i $e |- ., = ( .i ` R ) $.
      imasip.w $e |- I = ( .i ` U ) $.
      $( The inner product of an image structure.  (Contributed by Thierry
         Arnoux, 16-Jun-2019.) $)
      imasip $p |- ( ph -> I = U_ p e. V U_ q e. V
        { <. <. ( F ` p ) , ( F ` q ) >. , ( p ., q ) >. } ) $=
        ( cfv cop eqid vx vy vz vw vv vu cv co csn ciun cnx cbs cplusg ctp csca
        cmulr cvsca cip cun cts ctopn cqtop cple ccom ccnv cds cvv c1 imasplusg
        c2 imasmulr imasvsca eqidd imasds imasval imasvalstr ipid snsstp3 ssun2
        sstri ssun1 wcel wral fvex eqeltrdi snex rgenw iunexg sylancl ralrimivw
        cdc syl2anc strfv3 ) AGKHJHKUGZERJUGZERSWNWOFUHSZUIZUJZUJZUKULRBSUKUMRD
        UMRZSUKUPRDUPRZSUNZUKUORCUORZSZUKUQRDUQRZSZUKURRWSSZUNZUSZUKUTRCVARZEVB
        UHZSUKVCRECVCRZVDEVEVDZSUKVFRDVFRZSUNZUSZDURVGVHVHVJWKSAUAUBBXNCUMRZWTC
        XACUQRZCUPRZXEDUCUDUEUFCVFRZEXCFWSXJXCULRZXMXLXKHIJKLMXQTZXSTZXCTZYATZX
        RTZPXJTXTTZXLTABXQWTCDEHIJKLMNOYBWTTVIABCXAXSDEHIJKLMNOYCXATVKAUABCXEXR
        DEXCYAHIJKLMNOYDYEYFXETVLAWSVMAXKVMAUAUBBXNCDUCUDUEUFXTEHILMNOYGXNTVNAX
        MVMNOVOBXNWTXCXEXAXPWSXMXKXPTVPVQXGUIZXIXPYHXHXIXDXFXGVRXHXBVSVTXIXOWAV
        TAHVGWBZWRVGWBZKHWCWSVGWBAHCULRVGMCULWDWEZAYJKHAYIWQVGWBZJHWCYJYKYLJHWP
        WFWGJHWQVGVGWHWIWJKHWRVGVGWHWLQWM $.
    $}

    ${
      imastset.j $e |- J = ( TopOpen ` R ) $.
      imastset.o $e |- O = ( TopSet ` U ) $.
      $( The topology of an image structure.  (Contributed by Mario Carneiro,
         23-Feb-2015.) $)
      imastset $p |- ( ph -> O = ( J qTop F ) ) $=
        ( vp cfv cnx cop eqid vq vx vy vz vw vv cts cbs cplusg cmulr csca cvsca
        vu ctp cip cv csn ciun cqtop cple ccom ccnv imasplusg imasmulr imasvsca
        co cun cds eqidd imasds imasval fveq2d cvv wcel wceq ovex c1 imasvalstr
        c2 cdc tsetid snsstp1 ssun2 sstri strfv ax-mp 3eqtr4g ) ADUGQRUHQBSRUIQ
        DUIQZSRUJQDUJQZSUNRUKQCUKQZSRULQDULQZSRUOQPHUAHPUPZEQUAUPZEQSWLWMCUOQZV
        FSUQURURZSUNVGZRUGQFEUSVFZSZRUTQECUTQZVAEVBVAZSZRVHQDVHQZSZUNZVGZUGQZGW
        QADXEUGAUBUCBXBCUIQZWHCWICULQZCUJQZWKDUDUEUFUMCVHQZEWJWNWOFWJUHQZWTWSWQ
        HIUAPJKXGTZXITZWJTZXKTZXHTZWNTNXJTZWSTABXGWHCDEHIUAPJKLMXLWHTVCABCWIXID
        EHIUAPJKLMXMWITVDAUBBCWKXHDEWJXKHIUAPJKLMXNXOXPWKTVEAWOVIAWQVIAUBUCBXBC
        DUDUEUFUMXJEHIJKLMXQXBTVJAWTVILMVKVLOWQVMVNWQXFVOFEUSVPWQXEUGVMVQVQVSVT
        SBXBWHWJWKWIXEWOWTWQXETVRWAWRUQXDXEWRXAXCWBXDWPWCWDWEWFWG $.
    $}

    ${
      imasle.n $e |- N = ( le ` R ) $.
      imasle.l $e |- .<_ = ( le ` U ) $.
      $( The ordering of an image structure.  (Contributed by Mario Carneiro,
         23-Feb-2015.) $)
      imasle $p |- ( ph -> .<_ = ( ( F o. N ) o. `' F ) ) $=
        ( cnx cfv cop cvv eqid vp vq vx vy vz vw vv vu ccom ccnv cbs cplusg ctp
        cmulr csca cvsca cip cv co csn ciun cun cts cple cds c1 ctopn imasplusg
        c2 cdc imasmulr imasvsca eqidd imastset imasds imasval imasvalstr pleid
        snsstp2 ssun2 sstri wcel wfo fof fvex eqeltrdi fexd fvexi coexg sylancl
        wf syl cnvexg syl2anc strfv3 ) AFEGUIZEUJZUIZPUKQBRPULQDULQZRPUNQDUNQZR
        UMPUOQCUOQZRPUPQDUPQZRPUQQUAHUBHUAURZEQUBURZEQRXCXDCUQQZUSRUTVAVAZRUMVB
        ZPVCQDVCQZRZPVDQWRRZPVEQDVEQZRZUMZVBZDVDSVFVFVIVJRAUCUDBXKCULQZWSCWTCUP
        QZCUNQZXBDUEUFUGUHCVEQZEXAXEXFCVGQZXAUKQZWRGXHHIUBUAJKXOTZXQTZXATZXTTZX
        PTZXETXSTZXRTZNABXOWSCDEHIUBUAJKLMYAWSTVHABCWTXQDEHIUBUAJKLMYBWTTVKAUCB
        CXBXPDEXAXTHIUBUAJKLMYCYDYEXBTVLAXFVMABCDEXSXHHIJKLMYFXHTVNAUCUDBXKCDUE
        UFUGUHXREHIJKLMYGXKTVOAWRVMLMVPBXKWSXAXBWTXNXFWRXHXNTVQVRXJUTXMXNXIXJXL
        VSXMXGVTWAAWPSWBZWQSWBZWRSWBAESWBZGSWBYHAHBSEAHBEWCHBEWKLHBEWDWLAHCUKQS
        KCUKWEWFWGZGCVDNWHEGSSWIWJAYJYIYKESWMWLWPWQSSWIWNOWO $.
    $}
  $}

  ${
    f1ocpbl.f $e |- ( ph -> F : V -1-1-onto-> X ) $.
    $( Lemma for ~ f1ocpbl .  (Contributed by Mario Carneiro, 24-Feb-2015.) $)
    f1ocpbllem $p |- ( ( ph /\ ( A e. V /\ B e. V ) /\ ( C e. V /\ D e. V ) )
      -> ( ( ( F ` A ) = ( F ` C ) /\ ( F ` B ) = ( F ` D ) )
        <-> ( A = C /\ B = D ) ) ) $=
      ( wcel wa w3a cfv wceq wf1 wb wf1o f1of1 f1fveq syl12anc 3ad2ant1 anbi12d
      syl simp2l simp3l simp2r simp3r ) ABGJZCGJZKZDGJZEGJZKZLZBFMDFMNZBDNZCFME
      FMNZCENZUNGHFOZUHUKUOUPPAUJUSUMAGHFQUSIGHFRUCUAZAUHUIUMUDAUJUKULUEGHBDFST
      UNUSUIULUQURPUTAUHUIUMUFAUJUKULUGGHCEFSTUB $.

    $( An injection is compatible with any operations on the base set.
       (Contributed by Mario Carneiro, 24-Feb-2015.) $)
    f1ocpbl $p |- ( ( ph /\ ( A e. V /\ B e. V ) /\ ( C e. V /\ D e. V ) ) ->
      ( ( ( F ` A ) = ( F ` C ) /\ ( F ` B ) = ( F ` D ) ) ->
        ( F ` ( A .+ B ) ) = ( F ` ( C .+ D ) ) ) ) $=
      ( wcel wa w3a cfv wceq co f1ocpbllem oveq12 fveq2d biimtrdi ) ABHKCHKLDHK
      EHKLMBGNDGNOCGNEGNOLBDOCEOLZBCFPZGNDEFPZGNOABCDEGHIJQUAUBUCGBDCEFRST $.

    $( An injection is compatible with any operations on the base set.
       (Contributed by Mario Carneiro, 15-Aug-2015.) $)
    f1ovscpbl $p |- ( ( ph /\ ( A e. K /\ B e. V /\ C e. V ) ) ->
      ( ( F ` B ) = ( F ` C ) -> ( F ` ( A .+ B ) ) = ( F ` ( A .+ C ) ) ) ) $=
      ( wcel w3a wa cfv wceq co wf1 wb wf1o f1of1 adantr simpr2 simpr3 syl12anc
      syl f1fveq oveq2 fveq2d biimtrdi ) ABGKZCHKZDHKZLZMZCFNDFNOZCDOZBCEPZFNBD
      EPZFNOUNHIFQZUKULUOUPRAUSUMAHIFSUSJHIFTUEUAAUJUKULUBAUJUKULUCHICDFUFUDUPU
      QURFCDBEUGUHUI $.

    $( An injection is compatible with any relations on the base set.
       (Contributed by Mario Carneiro, 24-Feb-2015.) $)
    f1olecpbl $p |- ( ( ph /\ ( A e. V /\ B e. V ) /\ ( C e. V /\ D e. V ) ) ->
      ( ( ( F ` A ) = ( F ` C ) /\ ( F ` B ) = ( F ` D ) ) ->
        ( A N B <-> C N D ) ) ) $=
      ( wcel wa w3a cfv wceq wbr wb f1ocpbllem breq12 biimtrdi ) ABHKCHKLDHKEHK
      LMBFNDFNOCFNEFNOLBDOCEOLBCGPDEGPQABCDEFHIJRBDCEGST $.
  $}

  ${
    $d p q B $.  $d p q R $.  $d a b p q w y z V $.  $d p q w .x. $.  $d p X $.
    $d a b p q w x y z F $.  $d a b p q w ph $.  $d a b p q w x y z .xb $.
    $d p q Y $.
    imasaddf.f $e |- ( ph -> F : V -onto-> B ) $.
    imasaddf.e $e |- ( ( ph /\ ( a e. V /\ b e. V ) /\ ( p e. V /\ q e. V ) )
      -> ( ( ( F ` a ) = ( F ` p ) /\ ( F ` b ) = ( F ` q ) )
        -> ( F ` ( a .x. b ) ) = ( F ` ( p .x. q ) ) ) ) $.
    ${
      imasaddflem.a $e |- ( ph -> .xb = U_ p e. V U_ q e. V
          { <. <. ( F ` p ) , ( F ` q ) >. , ( F ` ( p .x. q ) ) >. } ) $.
      $( The image structure operation is a function if the original operation
         is compatible with the function.  (Contributed by Mario Carneiro,
         23-Feb-2015.) $)
      imasaddfnlem $p |- ( ph -> .xb Fn ( B X. B ) ) $=
        ( vx vw vz wceq wral wcel syl vy wfun cdm cxp wfn cv wbr wmo cfv cop co
        wrel csn ciun opex relsnop rgenw reliun mpbir releqd mpbiri crn wss cvv
        fvex wa wfo fof ffvelcdm anim12dan sylan opelxpi sylancl anassrs iunssd
        wf snssd eqsstrd dmss wne vn0 dmxp ax-mp sseqtrdi forn sqxpeqd sseqtrrd
        c0 wi wal wrex eleq2d adantr df-br eliun rexbii bitr2i 3bitr4g w3a elsn
        wb vex opth biimtrid eqeq2 biimprd syl6 3expa rexlimdvva sylbid alrimiv
        impd mo2icl ralrimivva fofn opeq2 breq1d mobidv ralrn opeq1 breq1 ralxp
        ralbidv mpbird sylibr ssralv dffun7 sylanbrc eqimss2 iunss sylib opeldm
        sylc snss sylbir ralimi sylbi eleq1d eleq1 dfss3 eqsstrrd eqssd df-fn )
        ACUBZCUCZBBUDZQCUUFUEACULZNUFZOUFZCUGZOUHZNUUERZUUDAUUGHFGFHUFZEUIZGUFZ
        EUIZUJZUUMUUODUKZEUIZUJZUMZUNZUNZULZUVDUVBULZHFRUVEHFUVEUVAULZGFRUVFGFU
        UQUUSUUNUUPUOZUUREVEZUPUQGFUVAURUSUQHFUVBURUSACUVCMUTVAAUUEEVBZUVIUDZVC
        UUKNUVJRZUULAUUEUUFUVJAUUEUUFVDUDZUCZUUFACUVLVCUUEUVMVCACUVCUVLMAHFUVBU
        VLAUUMFSZVFGFUVAUVLAUVNUUOFSZUVAUVLVCAUVNUVOVFZVFZUUTUVLUVQUUQUUFSZUUSV
        DSUUTUVLSUVQUUNBSZUUPBSZVFZUVRAFBEVPZUVPUWAAFBEVGZUWBKFBEVHTUWBUVNUVSUV
        OUVTFBUUMEVIFBUUOEVIVJVKUUNUUPBBVLTUVHUUQUUSUUFVDVLVMVQVNVOVOVRCUVLVSTV
        DWHVTUVMUUFQWAUUFVDWBWCWDZAUVIBAUWCUVIBQKFBEWETWFZWGAUAUFZPUFZUJZUUICUG
        ZOUHZPUVIRZUAUVIRZUVKAUWLIUFZEUIZUWGUJZUUICUGZOUHZPUVIRZIFRZAUWSUWNJUFZ
        EUIZUJZUUICUGZOUHZJFRZIFRAUXDIJFFAUWMFSUWTFSVFZVFZUXCUUIUWMUWTDUKEUIZQZ
        WIZOWJUXDUXGUXJOUXGUXCUXBUUIUJZUVASZGFWKZHFWKZUXIUXGUXKCSZUXKUVCSZUXCUX
        NAUXOUXPXAUXFACUVCUXKMWLWMUXBUUICWNUXPUXKUVBSZHFWKUXNHUXKFUVBWOUXQUXMHF
        GUXKFUVAWOWPWQWRUXGUXLUXIHGFFAUXFUVPUXLUXIWIUXLUXKUUTQZAUXFUVPWSZUXIUXK
        UUTUXBUUIUOWTUXRUXBUUQQZUUIUUSQZVFUXSUXIUXBUUIUUQUUSUWNUXAUOOXBXCUXSUXT
        UYAUXIUXSUXTUXHUUSQZUYAUXIWIUXTUWNUUNQUXAUUPQVFUXSUYBUWNUXAUUNUUPUWMEVE
        UWTEVEXCLXDUYBUXIUYAUXHUUSUUIXEXFXGXLXDXDXHXIXJXKUXCOUXHXMTXNAUWRUXEIFA
        EFUEZUWRUXEXAAUWCUYCKFBEXOTZUWQUXDPJFEUWGUXAQZUWPUXCOUYEUWOUXBUUICUWGUX
        AUWNXPXQXRXSTYCYDAUYCUWLUWSXAUYDUWKUWRUAIFEUWFUWNQZUWJUWQPUVIUYFUWIUWPO
        UYFUWHUWOUUICUWFUWNUWGXTXQXRYCXSTYDUUKUWJNUAPUVIUVIUUHUWHQUUJUWIOUUHUWH
        UUICYAXRYBYEUUKNUUEUVJYFYMNOCYGYHAUUEUUFUWDAUUFUVJUUEUWEAUUHUUESZNUVJRZ
        UVJUUEVCAUWHUUESZPUVIRZUAUVIRZUYHAUYKUUNUWGUJZUUESZPUVIRZHFRZAUYOUUQUUE
        SZGFRZHFRZAUVBCVCZHFRZUYRAUVCCVCZUYTACUVCQVUAMUVCCYITHFUVBCYJYKUYSUYQHF
        UYSUVACVCZGFRUYQGFUVACYJVUBUYPGFVUBUUTCSUYPUUTCUUQUUSUOYNUUQUUSCUVGUVHY
        LYOYPYQYPTAUYNUYQHFAUYCUYNUYQXAUYDUYMUYPPGFEUWGUUPQUYLUUQUUEUWGUUPUUNXP
        YRXSTYCYDAUYCUYKUYOXAUYDUYJUYNUAHFEUWFUUNQZUYIUYMPUVIVUCUWHUYLUUEUWFUUN
        UWGXTYRYCXSTYDUYGUYINUAPUVIUVIUUHUWHUUEYSYBYENUVJUUEYTYEUUAUUBCUUFUUCYH
        $.

      $( The operation of an image structure is defined to distribute over the
         mapping function.  (Contributed by Mario Carneiro, 23-Feb-2015.) $)
      imasaddvallem $p |- ( ( ph /\ X e. V /\ Y e. V ) ->
        ( ( F ` X ) .xb ( F ` Y ) ) = ( F ` ( X .x. Y ) ) ) $=
        ( cfv co cop wceq wss wcel w3a df-ov wfun cxp wfn imasaddfnlem 3ad2ant1
        fnfun syl csn cv ciun fveq2 fvoveq1 opeq12d sneqd ssiun2s 3ad2ant2 wral
        opeq1d opeq2d oveq2 fveq2d ralrimivw ss2iun 3ad2ant3 sseqtrrd opex snss
        sstrd sylibr funopfv sylc eqtrid ) AGFUAZHFUAZUBZGEPZHEPZCQVSVTRZCPZGHD
        QEPZVSVTCUCVRCUDZWAWCRZCUAZWBWCSAVPWDVQACBBUEZUFWDABCDEFIJKLMNOUGWGCUIU
        JUHVRWEUKZCTWFVRWHJFIFJULZEPZIULZEPZRZWIWKDQZEPZRZUKZUMZUMZCVRWHJFWJVTR
        ZWIHDQZEPZRZUKZUMZWSVPAWHXETVQJFXDGWHWIGSZXCWEXFWTWAXBWCXFWJVSVTWIGEUNV
        AWIGHEDUOUPUQURUSVQAXEWSTZVPVQXDWRTZJFUTXGVQXHJFIFWQHXDWKHSZWPXCXIWMWTW
        OXBXIWLVTWJWKHEUNVBXIWNXAEWKHWIDVCVDUPUQURVEJFXDWRVFUJVGVKAVPCWSSVQOUHV
        HWECWAWCVIVJVLWAWCCVMVNVO $.

      imasaddflem.c $e |- ( ( ph /\ ( p e. V /\ q e. V ) ) ->
        ( p .x. q ) e. V ) $.
      $( The image set operations are closed if the original operation is.
         (Contributed by Mario Carneiro, 23-Feb-2015.) $)
      imasaddflem $p |- ( ph -> .xb : ( B X. B ) --> B ) $=
        ( cxp wss cfv wcel wa ffvelcdm wfn wf imasaddfnlem cop csn ciun wfo fof
        cv co syl anim12dan opelxpi sylan syl2an2r opelxpd snssd anassrs iunssd
        eqsstrd dff2 sylanbrc ) ACBBOZUACVCBOZPVCBCUBABCDEFGHIJKLMUCACHFGFHUIZE
        QZGUIZEQZUDZVEVGDUJZEQZUDZUEZUFZUFVDMAHFVNVDAVEFRZSGFVMVDAVOVGFRZVMVDPA
        VOVPSZSZVLVDVRVIVKVCBAFBEUBZVQVIVCRZAFBEUGVSKFBEUHUKZVSVQSVFBRZVHBRZSVT
        VSVOWBVPWCFBVEETFBVGETULVFVHBBUMUKUNAVSVQVJFRVKBRWANFBVJETUOUPUQURUSUSU
        TVCBCVAVB $.
    $}

    imasaddf.u $e |- ( ph -> U = ( F "s R ) ) $.
    imasaddf.v $e |- ( ph -> V = ( Base ` R ) ) $.
    imasaddf.r $e |- ( ph -> R e. Z ) $.
    ${
      imasaddf.p $e |- .x. = ( +g ` R ) $.
      imasaddf.a $e |- .xb = ( +g ` U ) $.
      $( The image structure's group operation is a function.  (Contributed by
         Mario Carneiro, 23-Feb-2015.)  (Revised by Mario Carneiro,
         10-Jul-2015.) $)
      imasaddfn $p |- ( ph -> .xb Fn ( B X. B ) ) $=
        ( imasplusg imasaddfnlem ) ABDEGHJKLMNOABEDCFGHIJKPQNRSTUAUB $.

      $( The value of an image structure's group operation.  (Contributed by
         Mario Carneiro, 23-Feb-2015.) $)
      imasaddval $p |- ( ( ph /\ X e. V /\ Y e. V ) ->
        ( ( F ` X ) .xb ( F ` Y ) ) = ( F ` ( X .x. Y ) ) ) $=
        ( imasplusg imasaddvallem ) ABDEGHIJLMNOPQABEDCFGHKLMRSPTUAUBUCUD $.

      imasaddf.c $e |- ( ( ph /\ ( p e. V /\ q e. V ) ) ->
        ( p .x. q ) e. V ) $.
      $( The image structure's group operation is closed in the base set.
         (Contributed by Mario Carneiro, 23-Feb-2015.) $)
      imasaddf $p |- ( ph -> .xb : ( B X. B ) --> B ) $=
        ( imasplusg imasaddflem ) ABDEGHJKLMNOABEDCFGHIJKPQNRSTUBUAUC $.
    $}

    ${
      imasmulf.p $e |- .x. = ( .r ` R ) $.
      imasmulf.a $e |- .xb = ( .r ` U ) $.
      $( The image structure's ring multiplication is a function.  (Contributed
         by Mario Carneiro, 23-Feb-2015.) $)
      imasmulfn $p |- ( ph -> .xb Fn ( B X. B ) ) $=
        ( imasmulr imasaddfnlem ) ABDEGHJKLMNOABCDEFGHIJKPQNRSTUAUB $.

      $( The value of an image structure's ring multiplication.  (Contributed
         by Mario Carneiro, 23-Feb-2015.) $)
      imasmulval $p |- ( ( ph /\ X e. V /\ Y e. V ) ->
        ( ( F ` X ) .xb ( F ` Y ) ) = ( F ` ( X .x. Y ) ) ) $=
        ( imasmulr imasaddvallem ) ABDEGHIJLMNOPQABCDEFGHKLMRSPTUAUBUCUD $.

      imasmulf.c $e |- ( ( ph /\ ( p e. V /\ q e. V ) ) ->
        ( p .x. q ) e. V ) $.
      $( The image structure's ring multiplication is closed in the base set.
         (Contributed by Mario Carneiro, 23-Feb-2015.) $)
      imasmulf $p |- ( ph -> .xb : ( B X. B ) --> B ) $=
        ( imasmulr imasaddflem ) ABDEGHJKLMNOABCDEFGHIJKPQNRSTUBUAUC $.
    $}
  $}

  ${
    $d a p q w x y z F $.  $d a p q w x y z K $.  $d a p q w x ph $.  $d x U $.
    $d p q x B $.  $d p q x R $.  $d p q w x y z .x. $.  $d a p q w x y .xb $.
    $d a p q w x y V $.  $d p x X $.  $d p q x Y $.
    imasvscaf.u $e |- ( ph -> U = ( F "s R ) ) $.
    imasvscaf.v $e |- ( ph -> V = ( Base ` R ) ) $.
    imasvscaf.f $e |- ( ph -> F : V -onto-> B ) $.
    imasvscaf.r $e |- ( ph -> R e. Z ) $.
    imasvscaf.g $e |- G = ( Scalar ` R ) $.
    imasvscaf.k $e |- K = ( Base ` G ) $.
    imasvscaf.q $e |- .x. = ( .s ` R ) $.
    imasvscaf.s $e |- .xb = ( .s ` U ) $.
    imasvscaf.e $e |- ( ( ph /\ ( p e. K /\ a e. V /\ q e. V ) ) ->
    ( ( F ` a ) = ( F ` q ) -> ( F ` ( p .x. a ) ) = ( F ` ( p .x. q ) ) ) ) $.
    $( The image structure's scalar multiplication is a function.  (Contributed
       by Mario Carneiro, 24-Feb-2015.) $)
    imasvscafn $p |- ( ph -> .xb Fn ( K X. B ) ) $=
      ( vx vw vy vz wfun cdm cxp wceq wfn wrel cv wbr wmo wral cfv co cmpo ciun
      csn eqid fnmpoi fnrel ax-mp rgenw reliun mpbir imasvsca releqd mpbiri crn
      fvex wss cvv wcel wa wf dffn2 mpbi fssxp wfo ffvelcdmda snssd xpss2 xpss1
      fof syl 3syl sstrid ralrimiva iunss sylibr eqsstrd dmss wne dmxp sseqtrdi
      c0 vn0 forn xpeq2d sseqtrrd cop wi wal df-br eleq2d adantr wrex eliun w3a
      df-3an mpofun funopfv df-ov opex vex opeldm dmmpo eleqtrdi opelxp fvoveq1
      wb sylib eqidd weq cbvmpov ovmpo eqtr3id biimtrid ralrimivva opeq2 mobidv
      ralrn ralbidv mpbird ralxp sylanbrc eqtr3d adantl elsni simpl2im impel ex
      eqtr4d sylan2br anassrs rexlimdva sylbid alrimiv mo2icl fofn breq1d breq1
      ssralv sylc dffun7 eqimss2 r19.21bi adantrl eqsstrrid simprl snid opelxpi
      sylancl sseldd eleq1d eleq1 dfss3 eqsstrrd eqssd df-fn ) ADUHZDUIZIBUJZUK
      DUVQULADUMZUDUNZUEUNZDUOZUEUPZUDUVPUQZUVOAUVRLJMUDILUNZGURZVBZMUNZUWDEUSZ
      GURZUTZVAZUMZUWLUWJUMZLJUQUWMLJUWJIUWFUJZULZUWMMUDIUWFUWIUWJUWJVCZUWHGVNZ
      VDZUWNUWJVEVFVGLJUWJVHVIADUWKAUDBCDEFGHIJKLMOPQRSTUAUBVJZVKVLAUVPIGVMZUJZ
      VOUWBUDUXAUQZUWCAUVPUVQUXAAUVPUVQVPUJZUIZUVQADUXCVOUVPUXDVOADUWKUXCUWSAUW
      JUXCVOZLJUQUWKUXCVOAUXELJAUWDJVQZVRZUWJUWNVPUJZUXCUWNVPUWJVSZUWJUXHVOUWOU
      XIUWRUWNUWJVTWAUWNVPUWJWBVFUXGUWFBVOUWNUVQVOUXHUXCVOUXGUWEBAJBUWDGAJBGWCZ
      JBGVSQJBGWHWIWDWEUWFBIWFUWNUVQVPWGWJWKWLLJUWJUXCWMWNWODUXCWPWIVPWTWQUXDUV
      QUKXAUVQVPWRVFWSZAUWTBIAUXJUWTBUKQJBGXBWIXCZXDAUWGUFUNZXEZUVTDUOZUEUPZUFU
      WTUQZMIUQZUXBAUXRUWGNUNZGURZXEZUVTDUOZUEUPZNJUQZMIUQAUYCMNIJAUWGIVQZUXSJV
      QZVRZVRZUYBUVTUWGUXSEUSGURZUKZXFZUEXGUYCUYHUYKUEUYBUYAUVTXEZDVQZUYHUYJUYA
      UVTDXHUYHUYMUYLUWKVQZUYJAUYMUYNYEUYGADUWKUYLUWSXIXJUYNUYLUWJVQZLJXKUYHUYJ
      LUYLJUWJXLUYHUYOUYJLJAUYGUXFUYOUYJXFZUYGUXFVRAUYEUYFUXFXMZUYPUYEUYFUXFXNA
      UYQVRZUYOUYJUYRUYOVRUVTUWIUYIUYOUVTUWIUKUYRUYOUYAUWJURZUVTUWIUWJUHUYOUYSU
      VTUKXFMUDIUWFUWIUWJUWPXOUYAUVTUWJXPVFUYOUYSUWGUXTUWJUSZUWIUWGUXTUWJXQUYOU
      YEUXTUWFVQZVRZUYTUWIUKUYOUYAUWNVQVUBUYOUYAUWJUIZUWNUYAUVTUWJUWGUXTXRUEXSX
      TMUDIUWFUWIUWJUWPUWQYAZYBUWGUXTIUWFYCYFZUGUFUWGUXTIUWFUGUNZUWDEUSGURZUWIU
      WJUWIVUFUWGUWDGEYDUXMUXTUKZUWIYGMUDUGUFIUWFUWIVUGVUGUWGVUFUWDGEYDUDUFYHVU
      GYGYIUWQYJWIYKUUAUUBUYRUXTUWEUKZUYIUWIUKUYOUCUYOUYEVUAVUIVUEUXTUWEUUCUUDU
      UEUUGUUFUUHUUIUUJYLUUKYLUULUYBUEUYIUUMWIYMAUXQUYDMIAUXJGJULZUXQUYDYEQJBGU
      UNZUXPUYCUFNJGVUHUXOUYBUEVUHUXNUYAUVTDUXMUXTUWGYNUUOYOYPWJYQYRUWBUXPUDMUF
      IUWTUVSUXNUKUWAUXOUEUVSUXNUVTDUUPYOYSWNUWBUDUVPUXAUUQUURUDUEDUUSYTAUVPUVQ
      UXKAUVQUXAUVPUXLAUVSUVPVQZUDUXAUQZUXAUVPVOAUXNUVPVQZUFUWTUQZMIUQZVUMAVUPU
      WGUWEXEZUVPVQZLJUQZMIUQAVURMLIJAUYEUXFVRVRZUWNUVPVUQVUTUWNVUCUVPVUDVUTUWJ
      DVOZVUCUVPVOAUXFVVAUYEAVVALJAUWKDVOZVVALJUQADUWKUKVVBUWSUWKDUUTWILJUWJDWM
      YFUVAUVBUWJDWPWIUVCVUTUYEUWEUWFVQVUQUWNVQAUYEUXFUVDUWEUWDGVNUVEUWGUWEIUWF
      UVFUVGUVHYMAVUOVUSMIAUXJVUJVUOVUSYEQVUKVUNVURUFLJGUXMUWEUKUXNVUQUVPUXMUWE
      UWGYNUVIYPWJYQYRVULVUNUDMUFIUWTUVSUXNUVPUVJYSWNUDUXAUVPUVKWNUVLUVMDUVQUVN
      YT $.

    $( The value of an image structure's scalar multiplication.  (Contributed
       by Mario Carneiro, 24-Feb-2015.) $)
    imasvscaval $p |- ( ( ph /\ X e. K /\ Y e. V ) ->
      ( X .xb ( F ` Y ) ) = ( F ` ( X .x. Y ) ) ) $=
      ( vx wcel w3a cfv co csn cv cmpo cop wfun wss cdm wceq cxp wfn imasvscafn
      fnfun syl 3ad2ant1 ciun eqidd fveq2 sneqd oveq2 fveq2d mpoeq123dv ssiun2s
      3ad2ant3 imasvsca sseqtrrd simp2 fvex snid opelxpi sylancl eqid eleqtrrdi
      dmmpo funssfv syl3anc df-ov 3eqtr4g fvoveq1 ovmpo eqtrd ) AKIUGZLJUGZUHZK
      LGUIZDUJZKWNOUFIWNUKZOULZLEUJZGUIZUMZUJZKLEUJZGUIZWMKWNUNZDUIZXDWTUIZWOXA
      WMDUOZWTDUPXDWTUQZUGXEXFURAWKXGWLADIBUSZUTXGABCDEFGHIJMNOPQRSTUAUBUCUDUEV
      AXIDVBVCVDWMWTNJOUFINULZGUIZUKZWQXJEUJZGUIZUMZVEZDWLAWTXPUPWKNJXOLWTXJLUR
      ZOUFIXLXNIWPWSXQIVFXQXKWNXJLGVGVHXQXMWRGXJLWQEVIVJVKVLVMAWKDXPURWLAUFBCDE
      FGHIJMNOQRSTUAUBUCUDVNVDVOWMXDIWPUSZXHWMWKWNWPUGZXDXRUGAWKWLVPZWNLGVQVRZK
      WNIWPVSVTOUFIWPWSWTWTWAZWRGVQWCWBXDDWTWDWEKWNDWFKWNWTWFWGWMWKXSXAXCURXTYA
      OUFKWNIWPWSXCWTXCWQKLGEWHUFULWNURXCVFYBXBGVQWIVTWJ $.

    imasvscaf.c $e |- ( ( ph /\ ( p e. K /\ q e. V ) ) -> ( p .x. q ) e. V ) $.
    $( The image structure's scalar multiplication is closed in the base set.
       (Contributed by Mario Carneiro, 24-Feb-2015.) $)
    imasvscaf $p |- ( ph -> .xb : ( K X. B ) --> B ) $=
      ( vx cxp wfn wss wf imasvscafn cv cfv csn co cmpo ciun imasvsca wral wcel
      wa wfo fof ffvelcdmda syldan ralrimivw anass1rs ralrimiva eqid fmpo sylib
      syl fssxp snssd xpss2 xpss1 3syl sstrd iunss sylibr eqsstrd dff2 sylanbrc
      ) ADIBUFZUGDWCBUFZUHWCBDUIABCDEFGHIJKLMNOPQRSTUAUBUCUJADLJMUEILUKZGULZUMZ
      MUKZWEEUNZGULZUOZUPZWDAUEBCDEFGHIJKLMOPQRSTUAUBUQAWKWDUHZLJURWLWDUHAWMLJA
      WEJUSZUTZWKIWGUFZBUFZWDWOWPBWKUIZWKWQUHWOWJBUSZUEWGURZMIURWRWOWTMIAWHIUSZ
      WNWTAXAWNUTZUTWSUEWGAXBWIJUSWSUDAJBWIGAJBGVAJBGUIQJBGVBVKZVCVDVEVFVGMUEIW
      GWJBWKWKVHVIVJWPBWKVLVKWOWGBUHWPWCUHWQWDUHWOWFBAJBWEGXCVCVMWGBIVNWPWCBVOV
      PVQVGLJWKWDVRVSVTWCBDWAWB $.
  $}

  ${
    imasless.u $e |- ( ph -> U = ( F "s R ) ) $.
    imasless.v $e |- ( ph -> V = ( Base ` R ) ) $.
    imasless.f $e |- ( ph -> F : V -onto-> B ) $.
    imasless.r $e |- ( ph -> R e. Z ) $.
    imasless.l $e |- .<_ = ( le ` U ) $.
    $( The order relation defined on an image set is a subset of the base set.
       (Contributed by Mario Carneiro, 24-Feb-2015.) $)
    imasless $p |- ( ph -> .<_ C_ ( B X. B ) ) $=
      ( ccom ccnv cxp cdm crn wss cima cple cfv eqid wrel relco relssdmrn ax-mp
      imasle dmco wceq wfo wf fof frel 3syl sylib imaeq1d imassrn forn sseqtrid
      dfrel2 syl eqsstrd eqsstrid rncoss rnco2 sstrid xpss12 syl2anc ) AFECUAUB
      ZNZEOZNZBBPZABCDEFVJGHIJKLVJUCMUHAVMVMQZVMRZPZVNVMUDVMVQSVKVLUEVMUFUGAVOB
      SVPBSVQVNSAVOVLOZVKQZTZBVKVLUIAVTEVSTZBAVREVSAEUDZVREUJAGBEUKZGBEULWBKGBE
      UMGBEUNUOEVAUPUQAERZWABEVSURAWCWDBUJKGBEUSVBZUTVCVDAVPVKRZBVKVLVEAWFEVJRZ
      TZBEVJVFAWDWHBEWGURWEUTVDVGVOBVPBVHVIVGVC $.

    $d c d .<_ $.  $d a b c d F $.  $d a b c d N $.  $d a b c d V $.  $d d Y $.
    $d a b c d ph $.  $d c d X $.
    imasleval.n $e |- N = ( le ` R ) $.
    imasleval.e $e |- ( ( ph /\ ( a e. V /\ b e. V ) /\ ( c e. V /\ d e. V ) )
      -> ( ( ( F ` a ) = ( F ` c ) /\ ( F ` b ) = ( F ` d ) )
        -> ( a N b <-> c N d ) ) ) $.
    $( The value of the image structure's ordering when the order is compatible
       with the mapping function.  (Contributed by Mario Carneiro,
       24-Feb-2015.) $)
    imasleval $p |- ( ( ph /\ X e. V /\ Y e. V ) ->
      ( ( F ` X ) .<_ ( F ` Y ) <-> X N Y ) ) $=
      ( wcel cfv wbr wb wa cv wi fveq2 breq1d breq1 bibi12d imbi2d breq2d breq2
      wceq ccom ccnv wrex cdm wfn wfo adantr fndmd rexeqdv fnbrfvb sylan anbi1d
      fofn syl wex ancom fvex breldm pm4.71ri bitri exbii brco 3bitr4i ad2antrr
      vex df-rex 3expa an32s anassrs impl pm5.32da bitr3d r19.41v bitrdi simprr
      rexbidva eqid fveqeq2 rspcev sylancl biantrurd 3bitr4d bitrid bitrd brcnv
      anbi1i 3bitr4ri 3bitr3g imasle breqd simprl expcom vtocl2ga com12 3impib
      ) AIHUCZJHUCZIEUDZJEUDZFUEZIJGUEZUFZXMXNUGAXSANUHZEUDZOUHZEUDZFUEZXTYBGUE
      ZUFZUIAXOYCFUEZIYBGUEZUFZUIAXSUINOIJHHXTIUQZYFYIAYJYDYGYEYHYJYAXOYCFXTIEU
      JUKXTIYBGULUMUNYBJUQZYIXSAYKYGXQYHXRYKYCXPXOFYBJEUJUOYBJIGUPUMUNAXTHUCZYB
      HUCZUGZYFAYNUGZYAYCEGURZEUSZURZUEZLUHZEUDYAUQZLHUTZYEUGZYDYEYOYTYAEUEZYTY
      CYPUEZUGZLEVAZUTZUUAYEUGZLHUTZYSUUCYOUUHUUFLHUTUUJYOUUFLUUGHYOHEAEHVBZYNA
      HBEVCUUKRHBEVJVKVDZVEZVFYOUUFUUILHYOYTHUCZUGZUUAUUEUGUUFUUIUUOUUAUUDUUEYO
      UUKUUNUUAUUDUFUULHYTYAEVGVHVIUUOUUAUUEYEUUEMUHZYCEUEZYTUUPGUEZUGZMUUGUTZU
      UOUUAUGZYEUURUUQUGZMVLUUPUUGUCZUUSUGZMVLUUEUUTUVBUVDMUVBUUSUVDUURUUQVMUUS
      UVCUUQUVCUURUUPYCEMWBYBEVNZVOVDVPVQVRMYTYCEGLWBZUVEVSUUSMUUGWCVTUVAUUSMHU
      TZUUPEUDYCUQZMHUTZYEUGZUUTYEUVAUVGUVHYEUGZMHUTUVJUVAUUSUVKMHUVAUUPHUCZUGZ
      UVHUURUGZUUSUVKUVMUVHUUQUURUVAUUKUVLUVHUUQUFYOUUKUUNUUAUULWAHUUPYCEVGVHVI
      UUOUVLUUAUVNUVKUFUUOUVLUGZUUAUGUVHUURYEUVOUUAUVHUURYEUFZYOUUNUVLUUAUVHUGU
      VPUIZAUUNUVLUGZYNUVQAUVRYNUVQUBWDWEWFWGWHWEWIWMUVHYEMHWJWKYOUUTUVGUFUUNUU
      AYOUUSMUUGHUUMVFWAYOYEUVJUFUUNUUAYOUVIYEYOYMYCYCUQZUVIAYLYMWLYCWNUVHUVSMY
      BHUUPYBYCEWOWPWQWRWAWSWTWHWIWMXAYAYTYQUEZUUEUGZLVLYTUUGUCZUUFUGZLVLYSUUHU
      WAUWCLUWAUUFUWCUVTUUDUUEYAYTEXTEVNZUVFXBXCUUFUWBUUDUWBUUEYTYAEUVFUWDVOVDV
      PVQVRLYAYCYPYQUWDUVEVSUUFLUUGWCXDUUAYELHWJXEYOFYRYAYCAFYRUQYNABCDEFGHKPQR
      SUATXFVDXGYOUUBYEYOYLYAYAUQZUUBAYLYMXHYAWNUUAUWELXTHYTXTYAEWOWPWQWRWSXIXJ
      XKXL $.
  $}

  ${
    $d e r x y .~ $.  $d e r F $.  $d e r x ph $.  $d e r x R $.  $d x y V $.
    qusval.u $e |- ( ph -> U = ( R /s .~ ) ) $.
    qusval.v $e |- ( ph -> V = ( Base ` R ) ) $.
    qusval.f $e |- F = ( x e. V |-> [ x ] .~ ) $.
    qusval.e $e |- ( ph -> .~ e. W ) $.
    qusval.r $e |- ( ph -> R e. Z ) $.
    $( Value of a quotient structure.  (Contributed by Mario Carneiro,
       23-Feb-2015.) $)
    qusval $p |- ( ph -> U = ( F "s R ) ) $=
      ( vr ve cqus cimas cvv wceq co cv cbs cfv cec cmpt cmpo df-qus a1i simprl
      fveq2d adantr eqtr4d eceq2 ad2antll mpteq12dv eqtr4di oveq12d elexd ovexd
      wa ovmpod eqtrd ) AEDCQUAFDRUAZJAOPDCSSBOUBZUCUDZBUBZPUBZUEZUFZVERUAZVDQS
      QOPSSVKUGTABPOUHUIAVEDTZVHCTZVAZVAZVJFVEDRVOVJBGVGCUEZUFFVOBVFVIGVPVOVFDU
      CUDZGVOVEDUCAVLVMUJZUKAGVQTVNKULUMVMVIVPTAVLVHCVGUNUOUPLUQVRURADINUSACHMU
      SAFDRUTVBVC $.

    $( The function in ~ qusval is a surjection onto a quotient set.
       (Contributed by Mario Carneiro, 23-Feb-2015.) $)
    quslem $p |- ( ph -> F : V -onto-> ( V /. .~ ) ) $=
      ( vy wfo cv cvv wcel syl crn cqs wfn cec wral ecexg ralrimivw fnmpt dffn4
      sylib wceq wb wrex cab rnmpt df-qs eqtr4i foeq3 ax-mp ) AGFUAZFPZGGCUBZFP
      ZAFGUCZVAABQZCUDZRSZBGUEVDAVGBGACHSVGMVEHCUFTUGBGVFFRLUHTGFUIUJUTVBUKVAVC
      ULUTOQVFUKBGUMOUNVBBOGVFFLUOBOGCUPUQUTVBGFURUSUJ $.
  $}

  ${
    $d x .~ $.  $d x ph $.  $d x R $.  $d x V $.
    qusin.u $e |- ( ph -> U = ( R /s .~ ) ) $.
    qusin.v $e |- ( ph -> V = ( Base ` R ) ) $.
    qusin.e $e |- ( ph -> .~ e. W ) $.
    qusin.r $e |- ( ph -> R e. Z ) $.
    qusin.s $e |- ( ph -> ( .~ " V ) C_ V ) $.
    $( Restrict the equivalence relation in a quotient structure to the base
       set.  (Contributed by Mario Carneiro, 23-Feb-2015.) $)
    qusin $p |- ( ph -> U = ( R /s ( .~ i^i ( V X. V ) ) ) ) $=
      ( vx cec cmpt cimas co wcel eqid qusval cxp cin cqus cima wss wceq ecinxp
      cv sylan mpteq2dva oveq1d cvv eqidd inex1g syl 3eqtr4d ) AMEMUHZBNZOZCPQM
      EUQBEEUAZUBZNZOZCPQDCVAUCQZAUSVCCPAMEURVBABEUDEUEUQERURVBUFLEUQBUGUIUJUKA
      MBCDUSEFGHIUSSJKTAMVACVDVCEULGAVDUMIVCSABFRVAULRJBUTFUNUOKTUP $.
  $}

  ${
    $d x .~ $.  $d x ph $.  $d x R $.  $d x V $.
    qusbas.u $e |- ( ph -> U = ( R /s .~ ) ) $.
    qusbas.v $e |- ( ph -> V = ( Base ` R ) ) $.
    qusbas.e $e |- ( ph -> .~ e. W ) $.
    qusbas.r $e |- ( ph -> R e. Z ) $.
    $( Base set of a quotient structure.  (Contributed by Mario Carneiro,
       23-Feb-2015.) $)
    qusbas $p |- ( ph -> ( V /. .~ ) = ( Base ` U ) ) $=
      ( vx cqs cv cec cmpt eqid qusval quslem imasbas ) AEBMCDLELNBOPZEGALBCDUA
      EFGHIUAQZJKRIALBCDUAEFGHIUBJKSKT $.

    quss.k $e |- K = ( Scalar ` R ) $.
    $( The scalar field of a quotient structure.  (Contributed by Mario
       Carneiro, 24-Feb-2015.) $)
    quss $p |- ( ph -> K = ( Scalar ` U ) ) $=
      ( vx cqs cv cec cmpt eqid qusval quslem imassca ) AFBOCDNFNPBQRZEFHANBCDU
      CFGHIJUCSZKLTJANBCDUCFGHIJUDKLUALMUB $.
  $}

  ${
    $d x .~ $.  $d a b x A $.  $d b x B $.  $d x C $.  $d x D $.  $d a b x V $.
    $d a b x .+ $.  $d a b x ph $.
    ercpbl.r $e |- ( ph -> .~ Er V ) $.
    ercpbl.v $e |- ( ph -> V e. W ) $.
    ercpbl.f $e |- F = ( x e. V |-> [ x ] .~ ) $.
    $( Value of the function in ~ qusval .  (Contributed by Mario Carneiro,
       24-Feb-2015.)  (Revised by Mario Carneiro, 12-Aug-2015.)  (Revised by
       AV, 12-Jul-2024.) $)
    divsfval $p |- ( ph -> ( F ` A ) = [ A ] .~ ) $=
      ( wcel cec wceq cvv ecss ssexd wn c0 cdm syl cfv eceq1 fvmptg sylan2 cmpt
      cv expcom dmeqi ralrimivw dmmptg eqtrid eleq2d notbid ndmfv biimtrrdi wne
      wa wral ecdmn0 wer erdm biimpd biimtrrid necon1bd jcad eqtr3 syl6 pm2.61d
      ) ACFKZCEUAZCDLZMZVIAVLAVIVKNKVLAVKFGIACDFHOPBCBUFZDLZVKFNEVMCDUBJUCUDUGA
      VIQZVJRMZVKRMZUQVLAVOVPVQAVOCESZKZQVPAVSVIAVRFCAVRBFVNUEZSZFEVTJUHAVNNKZB
      FURWAFMAWBBFAVNFGIAVMDFHOPUIBFVNNUJTUKULUMCEUNUOAVIVKRVKRUPCDSZKZAVICDUSA
      WDVIAWCFCAFDUTWCFMHFDVATULVBVCVDVEVJVKRVFVGVH $.

    ${
      ercpbllem.1 $e |- ( ph -> A e. V ) $.
      $( Lemma for ~ ercpbl .  (Contributed by Mario Carneiro, 24-Feb-2015.)
         (Revised by AV, 12-Jul-2024.) $)
      ercpbllem $p |- ( ph -> ( ( F ` A ) = ( F ` B ) <-> A .~ B ) ) $=
        ( cfv wceq cec wbr divsfval eqeq12d erth bitr4d ) ACFMZDFMZNCEOZDEOZNCD
        EPAUAUCUBUDABCEFGHIJKQABDEFGHIJKQRACDEGILST $.
    $}

    ${
      ercpbl.c $e |- ( ( ph /\ ( a e. V /\ b e. V ) ) -> ( a .+ b ) e. V ) $.
      ercpbl.e $e |- ( ph ->
        ( ( A .~ C /\ B .~ D ) -> ( A .+ B ) .~ ( C .+ D ) ) ) $.
      $( Translate the function compatibility relation to a quotient set.
         (Contributed by Mario Carneiro, 24-Feb-2015.)  (Revised by Mario
         Carneiro, 12-Aug-2015.)  (Revised by AV, 12-Jul-2024.) $)
      ercpbl $p |- ( ( ph /\ ( A e. V /\ B e. V ) /\ ( C e. V /\ D e. V ) ) ->
        ( ( ( F ` A ) = ( F ` C ) /\ ( F ` B ) = ( F ` D ) ) ->
          ( F ` ( A .+ B ) ) = ( F ` ( C .+ D ) ) ) ) $=
        ( wcel cfv wa w3a wbr wceq 3ad2ant1 wer simp2l ercpbllem simp2r anbi12d
        co wi caovclg 3adant3 3imtr4d ) ACJSZDJSZUAZEJSFJSUAZUBZCEHUCZDFHUCZUAZ
        CDGUKZEFGUKZHUCZCITEITUDZDITFITUDZUAVDITVEITUDAURVCVFULUSRUEUTVGVAVHVBU
        TBCEHIJKAURJHUFUSNUEZAURJKSUSOUEZPAUPUQUSUGUHUTBDFHIJKVIVJPAUPUQUSUIUHU
        JUTBVDVEHIJKVIVJPAURVDJSUSALMCDJJJGQUMUNUHUO $.
    $}

    erlecpbl.e $e |- ( ph ->
      ( ( A .~ C /\ B .~ D ) -> ( A N B <-> C N D ) ) ) $.
    $( Translate the relation compatibility relation to a quotient set.
       (Contributed by Mario Carneiro, 24-Feb-2015.)  (Revised by Mario
       Carneiro, 12-Aug-2015.)  (Revised by AV, 12-Jul-2024.) $)
    erlecpbl $p |- ( ( ph /\ ( A e. V /\ B e. V ) /\ ( C e. V /\ D e. V ) ) ->
      ( ( ( F ` A ) = ( F ` C ) /\ ( F ` B ) = ( F ` D ) ) ->
        ( A N B <-> C N D ) ) ) $=
      ( wcel wa cfv wbr 3ad2ant1 w3a wceq wb simp2l ercpbllem simp2r anbi12d wi
      wer sylbid ) ACJPZDJPZQZEJPFJPQZUAZCHREHRUBZDHRFHRUBZQCEGSZDFGSZQZCDISEFI
      SUCZUOUPURUQUSUOBCEGHJKAUMJGUIUNLTZAUMJKPUNMTZNAUKULUNUDUEUOBDFGHJKVBVCNA
      UKULUNUFUEUGAUMUTVAUHUNOTUJ $.
  $}

  ${
    $d a b p q x .~ $.  $d a b p q F $.  $d a b p q x ph $.  $d a b p q x V $.
    $d p q x R $.  $d p q x .x. $.  $d p q x X $.  $d a b p q .xb $.
    $d p q x Y $.
    qusaddf.u $e |- ( ph -> U = ( R /s .~ ) ) $.
    qusaddf.v $e |- ( ph -> V = ( Base ` R ) ) $.
    qusaddf.r $e |- ( ph -> .~ Er V ) $.
    qusaddf.z $e |- ( ph -> R e. Z ) $.
    qusaddf.e $e |- ( ph ->
      ( ( a .~ p /\ b .~ q ) -> ( a .x. b ) .~ ( p .x. q ) ) ) $.
    qusaddf.c $e |- ( ( ph /\ ( p e. V /\ q e. V ) ) ->
      ( p .x. q ) e. V ) $.
    ${
      qusaddflem.f $e |- F = ( x e. V |-> [ x ] .~ ) $.
      qusaddflem.g $e |- ( ph -> .xb = U_ p e. V U_ q e. V
          { <. <. ( F ` p ) , ( F ` q ) >. , ( F ` ( p .x. q ) ) >. } ) $.
      $( Value of an operation defined on a quotient structure.  (Contributed
         by Mario Carneiro, 24-Feb-2015.) $)
      qusaddvallem $p |- ( ( ph /\ X e. V /\ Y e. V ) ->
        ( [ X ] .~ .xb [ Y ] .~ ) = [ ( X .x. Y ) ] .~ ) $=
        ( wcel w3a cfv co cec cqs cvv wer cbs fvex eqeltrdi erex sylc quslem cv
        ercpbl imasaddvallem 3ad2ant1 divsfval oveq12d 3eqtr3d ) AJIUEZKIUEZUFZ
        JHUGZKHUGZEUHJKFUHZHUGJCUIZKCUIZEUHVKCUIAICUJEFHIJKMNOPABCDGHIUKLQRUCAI
        CULZIUKUEZCUKUESAIDUMUGUKRDUMUNUOZICUKUPUQTURABOUSPUSNUSMUSFCHIUKNMSVPU
        CUBUAUTUDVAVHVIVLVJVMEVHBJCHIUKAVFVNVGSVBZAVFVOVGVPVBZUCVCVHBKCHIUKVQVR
        UCVCVDVHBVKCHIUKVQVRUCVCVE $.

      $( The operation of a quotient structure is a function.  (Contributed by
         Mario Carneiro, 24-Feb-2015.) $)
      qusaddflem $p |- ( ph ->
        .xb : ( ( V /. .~ ) X. ( V /. .~ ) ) --> ( V /. .~ ) ) $=
        ( cqs cvv wer wcel cbs cfv fvex eqeltrdi erex quslem ercpbl imasaddflem
        sylc cv ) AICUCEFHIKLMNABCDGHIUDJOPUAAICUEIUDUFCUDUFQAIDUGUHUDPDUGUIUJZ
        ICUDUKUORULABMUPNUPLUPKUPFCHIUDLKQUQUATSUMUBTUN $.
    $}

    ${
      qusaddf.p $e |- .x. = ( +g ` R ) $.
      qusaddf.a $e |- .xb = ( +g ` U ) $.
      $( The addition in a quotient structure.  (Contributed by Mario Carneiro,
         24-Feb-2015.) $)
      qusaddval $p |- ( ( ph /\ X e. V /\ Y e. V ) ->
        ( [ X ] .~ .xb [ Y ] .~ ) = [ ( X .x. Y ) ] .~ ) $=
        ( cec cmpt eqid cqs cvv wer wcel cbs cfv fvex eqeltrdi erex sylc qusval
        vx cv quslem imasplusg qusaddvallem ) AUQBCDEFUQGUQURBUCUDZGHIJKLMNOPQR
        STVBUEZAGBUFEDCFVBGJKLAUQBCFVBGUGJOPVCAGBUHGUGUIBUGUIQAGCUJUKUGPCUJULUM
        GBUGUNUOZRUPPAUQBCFVBGUGJOPVCVDRUSRUAUBUTVA $.

      $( The addition in a quotient structure as a function.  (Contributed by
         Mario Carneiro, 24-Feb-2015.) $)
      qusaddf $p |- ( ph ->
        .xb : ( ( V /. .~ ) X. ( V /. .~ ) ) --> ( V /. .~ ) ) $=
        ( cec cmpt eqid cqs cvv wer wcel cbs cfv fvex eqeltrdi erex sylc qusval
        vx cv quslem imasplusg qusaddflem ) AUOBCDEFUOGUOUPBUAUBZGHIJKLMNOPQRUT
        UCZAGBUDEDCFUTGHIJAUOBCFUTGUEHMNVAAGBUFGUEUGBUEUGOAGCUHUIUENCUHUJUKGBUE
        ULUMZPUNNAUOBCFUTGUEHMNVAVBPUQPSTURUS $.
    $}

    ${
      qusmulf.p $e |- .x. = ( .r ` R ) $.
      qusmulf.a $e |- .xb = ( .r ` U ) $.
      $( The multiplication in a quotient structure.  (Contributed by Mario
         Carneiro, 24-Feb-2015.) $)
      qusmulval $p |- ( ( ph /\ X e. V /\ Y e. V ) ->
        ( [ X ] .~ .xb [ Y ] .~ ) = [ ( X .x. Y ) ] .~ ) $=
        ( cec cmpt eqid cqs cvv wer wcel cbs cfv fvex eqeltrdi erex sylc qusval
        vx cv quslem imasmulr qusaddvallem ) AUQBCDEFUQGUQURBUCUDZGHIJKLMNOPQRS
        TVBUEZAGBUFCDEFVBGJKLAUQBCFVBGUGJOPVCAGBUHGUGUIBUGUIQAGCUJUKUGPCUJULUMG
        BUGUNUOZRUPPAUQBCFVBGUGJOPVCVDRUSRUAUBUTVA $.

      $( The multiplication in a quotient structure as a function.
         (Contributed by Mario Carneiro, 24-Feb-2015.) $)
      qusmulf $p |- ( ph ->
        .xb : ( ( V /. .~ ) X. ( V /. .~ ) ) --> ( V /. .~ ) ) $=
        ( cec cmpt eqid cqs cvv wer wcel cbs cfv fvex eqeltrdi erex sylc qusval
        vx cv quslem imasmulr qusaddflem ) AUOBCDEFUOGUOUPBUAUBZGHIJKLMNOPQRUTU
        CZAGBUDCDEFUTGHIJAUOBCFUTGUEHMNVAAGBUFGUEUGBUEUGOAGCUHUIUENCUHUJUKGBUEU
        LUMZPUNNAUOBCFUTGUEHMNVAVBPUQPSTURUS $.
    $}
  $}

  $( Function with a domain of ` 2o ` .  (Contributed by Jim Kingdon,
     25-Sep-2023.) $)
  fnpr2o $p |- ( ( A e. V /\ B e. W )
      -> { <. (/) , A >. , <. 1o , B >. } Fn 2o ) $=
    ( wcel wa c0 cop c1o cpr wfn c2o com wne peano1 a1i 1onn simpl simpr 1n0
    necomi fnprg syl221anc df2o3 fneq2i sylibr ) ACEZBDEZFZGAHIBHJZGIJZKZUJLKUI
    GMEZIMEZUGUHGINZULUMUIOPUNUIQPUGUHRUGUHSUOUIIGTUAPGIABMMCDUBUCLUKUJUDUEUF
    $.

  ${
    $d A k $.  $d B k $.
    $( Biconditional version of ~ fnpr2o .  (Contributed by Jim Kingdon,
       27-Sep-2023.) $)
    fnpr2ob $p |- ( ( A e. _V /\ B e. _V )
        <-> { <. (/) , A >. , <. 1o , B >. } Fn 2o ) $=
      ( vk cvv wcel wa cop c1o cpr c2o wex df2o3 eleqtrri eleqtrrid eldm2 sylib
      c0 0ex wceq 1oex wfn fnpr2o cv cdm prid1 fndm wn 1n0 nesymi vex opth1 mto
      wo elpri orel2 mpsyl opth simprd eximi isset sylibr syl 1oelpr orcomd jca
      neii impbii ) ADEZBDEZFQAGZHBGZIZJUAZABDDUBVMVHVIVMQCUCZGZVLEZCKZVHVMQVLU
      DZEVQVMQJVRQQHIZJQHRUELMJVLUFZNCQVLROPVQVNASZCKVHVPWACVPQQSZWAVPVOVJSZWBW
      AFVOVKSZUGVPWCWDUMWCWDQHSHQUHUIQVNHBRCUJZUKULVOVJVKUNWDWCUOUPQVNQARWEUQPU
      RUSCAUTVAVBVMHVNGZVLEZCKZVIVMHVREWHVMHJVRHVSJVCLMVTNCHVLTOPWHVNBSZCKVIWGW
      ICWGHHSZWIWGWFVKSZWJWIFWFVJSZUGWGWKWLUMWKWLHQSHQUHVFHVNQATWEUKULWGWLWKWFV
      JVKUNVDWLWKUOUPHVNHBTWEUQPURUSCBUTVAVBVEVG $.
  $}

  $( The value of a function with a domain of (at most) two elements.
     (Contributed by Jim Kingdon, 25-Sep-2023.) $)
  fvpr0o $p |- ( A e. V -> ( { <. (/) , A >. , <. 1o , B >. } ` (/) ) = A ) $=
    ( c0 com wcel c1o wne cop cpr cfv wceq peano1 1n0 necomi fvpr1g mp3an13 ) D
    EFACFDGHDDAIGBIJKALMGDNODGABECPQ $.

  $( The value of a function with a domain of (at most) two elements.
     (Contributed by Jim Kingdon, 25-Sep-2023.) $)
  fvpr1o $p |- ( B e. V -> ( { <. (/) , A >. , <. 1o , B >. } ` 1o ) = B ) $=
    ( c1o com wcel c0 wne cop cpr cfv wceq 1onn 1n0 necomi fvpr2g mp3an13 ) DEF
    BCFGDHDGAIDBIJKBLMDGNOGDABECPQ $.

  $( The value of the pair function at an element of ` 2o ` .  (Contributed by
     Mario Carneiro, 14-Aug-2015.) $)
  fvprif $p |- ( ( A e. V /\ B e. W /\ C e. 2o )
      -> ( { <. (/) , A >. , <. 1o , B >. } ` C ) = if ( C = (/) , A , B ) ) $=
    ( wcel c2o w3a c0 wceq cop c1o cpr cfv cif wa adantr simpr fveq2d 3eqtr4d
    fvpr0o 3ad2ant1 iftrued fvpr1o 3ad2ant2 1n0 eqeq1d mtbiri iffalsed wo elpri
    neii df2o3 eleq2s 3ad2ant3 mpjaodan ) ADFZBEFZCGFZHZCIJZCIAKLBKMZNZVAABOZJC
    LJZUTVAPZIVBNZAVCVDUTVGAJZVAUQURVHUSABDUAUBQVFCIVBUTVARZSVFVAABVIUCTUTVEPZL
    VBNZBVCVDUTVKBJZVEURUQVLUSABEUDUEQVJCLVBUTVERZSVJVAABVJVALIJLIUFULVJCLIVMUG
    UHUITUSUQVAVEUJZURVNCILMGCILUKUMUNUOUP $.

  ${
    $d k A $.  $d k B $.  $d k G $.
    $( Elementhood in the target space of the function ` F ` appearing in
       ~ xpsval .  (Contributed by Mario Carneiro, 14-Aug-2015.) $)
    xpsfrnel $p |- ( G e. X_ k e. 2o if ( k = (/) , A , B ) <-> ( G Fn 2o /\
       ( G ` (/) ) e. A /\ ( G ` 1o ) e. B ) ) $=
      ( c2o cv c0 wceq wcel cfv wral w3a c1o cfn fveq2 eleq12d wne bitri 3anass
      wa cif cixp cvv elixp2 3ancoma 2onn nnfi ax-mp fnfi mpan2 elexd biantrurd
      wfn com cpr df2o3 raleqi 0ex 1oex iftrue 1n0 neeq1 mpbiri ifnefalse ralpr
      syl bitr3di pm5.32i 3bitr4i ) DCECFZGHZABUAZUBIDUCIZDEUMZVJDJZVLIZCEKZLZV
      NGDJZAIZMDJZBIZLZCEVLDUDVRVNVMVQLZWCVMVNVQUEVNVMVQTZTVNVTWBTZTWDWCVNWEWFV
      NVQWEWFVNVMVQVNDNVNENIZDNIEUNIWGUFEUGUHEDUIUJUKULVQVPCGMUOZKWFVPCEWHUPUQV
      PVTWBCGMURUSVKVOVSVLAVJGDOVKABUTPVJMHZVOWAVLBVJMDOWIVJGQZVLBHWIWJMGQVAVJM
      GVBVCVJGABVDVFPVERVGVHVNVMVQSVNVTWBSVIRR $.
  $}

  ${
    $d k A $.  $d k B $.  $d k G $.  $d k X $.  $d k Y $.
    $( A function on ` 2o ` is determined by its values at zero and one.
       (Contributed by Mario Carneiro, 27-Aug-2015.) $)
    xpsfeq $p |- ( G Fn 2o ->
       { <. (/) , ( G ` (/) ) >. , <. 1o , ( G ` 1o ) >. } = G ) $=
      ( vk c2o wfn c0 cfv cop c1o cpr cvv wcel fvex fnpr2o mp2an a1i wceq ax-mp
      id fveq2 3eqtr4a cv wo elpri eleq2s fvpr0o fvpr1o jaoi syl adantl eqfnfvd
      df2o3 ) ACDZBCEEAFZGHHAFZGIZAUOCDZULUMJKZUNJKZUPEALZHALZUMUNJJMNOULRBUAZC
      KZVAUOFZVAAFZPZULVBVAEPZVAHPZUBZVEVHVAEHICVAEHUCUKUDVFVEVGVFEUOFZUMVCVDUQ
      VIUMPUSUMUNJUEQVAEUOSVAEASTVGHUOFZUNVCVDURVJUNPUTUMUNJUFQVAHUOSVAHASTUGUH
      UIUJ $.

    $( Elementhood in the target space of the function ` F ` appearing in
       ~ xpsval .  (Contributed by Mario Carneiro, 15-Aug-2015.) $)
    xpsfrnel2 $p |- ( { <. (/) , X >. , <. 1o , Y >. } e.
        X_ k e. 2o if ( k = (/) , A , B ) <-> ( X e. A /\ Y e. B ) ) $=
      ( c0 cop c1o cpr c2o cv wceq cif cixp wcel cfv wa cvv elex eleq1d wfn w3a
      xpsfrnel fnpr2ob biimpri 3ad2ant1 3anass fnpr2o biantrurd fvpr0o bi2anan9
      anim12i fvpr1o bitr3d bitrid pm5.21nii bitri ) FDGHEGIZCJCKFLABMNOURJUAZF
      URPZAOZHURPZBOZUBZDAOZEBOZQZABCURUCVDDROZEROZQZVGUSVAVJVCVJUSDEUDUEUFVEVH
      VFVIDASEBSULVDUSVAVCQZQZVJVGUSVAVCUGVJVKVLVGVJUSVKDERRUHUIVHVAVEVIVCVFVHU
      TDADERUJTVIVBEBDERUMTUKUNUOUPUQ $.

    $( Equivalent condition for the pair function to be a proper function on
       ` A ` .  (Contributed by Mario Carneiro, 20-Aug-2015.) $)
    xpscf $p |- ( { <. (/) , X >. , <. 1o , Y >. } : 2o --> A <->
        ( X e. A /\ Y e. A ) ) $=
      ( vk c2o c0 cop c1o cpr wf cv wceq cif cixp wcel wa wfn wral com 3bitr4i
      cfv ifid eleq2i ralbii anbi2i cvv df-3an elixp2 2onn fnex pm4.71ri anbi1i
      w3a mpan2 ffnfv xpsfrnel2 bitr3i ) EAFBGHCGIZJZURDEDKZFLZAAMZNOZBAOCAOPUR
      EQZUTURUAZVBOZDERZPZVDVEAOZDERZPVCUSVGVJVDVFVIDEVBAVEVAAUBUCUDUEURUFOZVDV
      GUMVKVDPZVGPVCVHVKVDVGUGDEVBURUHVDVLVGVDVKVDESOVKUIESURUJUNUKULTDEAURUOTA
      ADBCUPUQ $.
  $}

  ${
    $d A a b k x y z w $.  $d B a b k x y z w $.  $d F a b w z $.  $d X x y $.
    $d Y x y $.
    xpsff1o.f $e |- F = ( x e. A , y e. B
      |-> { <. (/) , x >. , <. 1o , y >. } ) $.
    $( The value of the function appearing in ~ xpsval .  (Contributed by Mario
       Carneiro, 15-Aug-2015.) $)
    xpsfval $p |- ( ( X e. A /\ Y e. B ) ->
        ( X F Y ) = { <. (/) , X >. , <. 1o , Y >. } ) $=
      ( c0 cv cop c1o cpr wceq wa simpl opeq2d simpr preq12d prex ovmpoa ) ABFG
      CDIAJZKZLBJZKZMIFKZLGKZMEUBFNZUDGNZOZUCUFUEUGUJUBFIUHUIPQUJUDGLUHUIRQSHUF
      UGTUA $.

    $( The function appearing in ~ xpsval is a bijection from the cartesian
       product to the indexed cartesian product indexed on the pair
       ` 2o = { (/) , 1o } ` .  (Contributed by Mario Carneiro,
       15-Aug-2015.) $)
    xpsff1o $p |- F : ( A X. B ) -1-1-onto->
        X_ k e. 2o if ( k = (/) , A , B ) $=
      ( vz vw va vb cv c0 wceq cfv wral cop c1o wcel cvv cxp c2o cif wf1 wfo wf
      cixp wf1o wi cpr wa xpsfrnel2 biimpri rgen2 fmpo mpbi c1st 1st2nd2 fveq2d
      c2nd df-ov xp1st xp2nd xpsfval syl2anc eqtr3id eqtrd eqeqan12d fveq1 fvex
      co fvpr0o ax-mp 3eqtr3g fvpr1o opeq12d imbitrrid sylbid mpbir2an wrex wfn
      dff13 xpsfrnel simp2bi simp3bi ixpfn xpsfeq syl rspceov syl3anc rgen foov
      eqtr2d df-f1o ) CDUAZEUBELMNCDUCZUGZFUHWOWQFUDZWOWQFUEZWRWOWQFUFZHLZFOZIL
      ZFOZNZXAXCNZUIZIWOPHWOPMALZQRBLZQUJZWQSZBDPACPWTXKABCDXKXHCSXIDSUKCDEXHXI
      ULUMUNABCDXJWQFGUOUPZXGHIWOWOXAWOSZXCWOSZUKZXEMXAUQOZQRXAUTOZQUJZMXCUQOZQ
      RXCUTOZQUJZNZXFXMXNXBXRXDYAXMXBXPXQQZFOZXRXMXAYCFXACDURZUSXMYDXPXQFVKZXRX
      PXQFVAXMXPCSXQDSYFXRNXACDVBXACDVCABCDFXPXQGVDVEVFVGXNXDXSXTQZFOZYAXNXCYGF
      XCCDURZUSXNYHXSXTFVKZYAXSXTFVAXNXSCSXTDSYJYANXCCDVBXCCDVCABCDFXSXTGVDVEVF
      VGVHYBXFXOYCYGNYBXPXSXQXTYBMXROZMYAOZXPXSMXRYAVIXPTSYKXPNXAUQVJXPXQTVLVMX
      STSYLXSNXCUQVJXSXTTVLVMVNYBRXROZRYAOZXQXTRXRYAVIXQTSYMXQNXAUTVJXPXQTVOVMX
      TTSYNXTNXCUTVJXSXTTVOVMVNVPXMXNXAYCXCYGYEYIVHVQVRUNHIWOWQFWBVSWSWTXAJLKLF
      VKNKDVTJCVTZHWQPXLYOHWQXAWQSZMXAOZCSZRXAOZDSZXAYQYSFVKZNYOYPXAUBWAZYRYTCD
      EXAWCZWDZYPUUBYRYTUUCWEZYPUUAMYQQRYSQUJZXAYPYRYTUUAUUFNUUDUUEABCDFYQYSGVD
      VEYPUUBUUFXANEUBWPXAWFXAWGWHWMJKCDYQYSXAFWIWJWKJKHCDWQFWLVSWOWQFWNVS $.

    $( A short expression for the indexed cartesian product on two indices.
       (Contributed by Mario Carneiro, 15-Aug-2015.) $)
    xpsfrn $p |- ran F = X_ k e. 2o if ( k = (/) , A , B ) $=
      ( cxp c2o cv c0 wceq cif cixp wf1o wfo crn xpsff1o f1ofo forn mp2b ) CDHZ
      EIEJKLCDMNZFOUBUCFPFQUCLABCDEFGRUBUCFSUBUCFTUA $.

    $( The function appearing in ~ xpsval is a bijection from the cartesian
       product to the indexed cartesian product indexed on the pair
       ` 2o = { (/) , 1o } ` .  (Contributed by Mario Carneiro,
       24-Jan-2015.) $)
    xpsff1o2 $p |- F : ( A X. B ) -1-1-onto-> ran F $=
      ( vk cxp c2o cv c0 wceq cif cixp wf1o wf1 crn xpsff1o f1of1 f1f1orn mp2b
      ) CDHZGIGJKLCDMNZEOUBUCEPUBEQEOABCDGEFRUBUCESUBUCETUA $.
  $}

  ${
    $d r s y $.  $d c k x y A $.  $d c k x y B $.  $d c d k x y C $.  $d k G $.
    $d c d k x y D $.  $d r s F $.  $d c d k r s S $.  $d k r s U $.  $d x W $.
    $d a b c d k ph $.  $d k x y .x. $.  $d k x y .X. $.  $d a b c d k x y X $.
    $d c d k r s x R $.  $d a b c d .xb $.  $d a b c d k x y Y $.
    xpsval.t $e |- T = ( R Xs. S ) $.
    xpsval.x $e |- X = ( Base ` R ) $.
    xpsval.y $e |- Y = ( Base ` S ) $.
    xpsval.1 $e |- ( ph -> R e. V ) $.
    xpsval.2 $e |- ( ph -> S e. W ) $.

    ${
      xpsval.f $e |- F = ( x e. X , y e. Y
        |-> { <. (/) , x >. , <. 1o , y >. } ) $.
      xpsval.k $e |- G = ( Scalar ` R ) $.
      xpsval.u $e |- U = ( G Xs_ { <. (/) , R >. , <. 1o , S >. } ) $.
      $( Value of the binary structure product function.  (Contributed by Mario
         Carneiro, 14-Aug-2015.)  (Revised by Jim Kingdon, 25-Sep-2023.) $)
      xpsval $p |- ( ph -> T = ( `' F "s U ) ) $=
        ( vr vs cxps co ccnv cimas cvv wcel wceq elexd cbs cfv cop c1o cpr cmpo
        cv c0 csca cprds fveq2 eqtr4di mpoeq12 syl2an cnveqd adantr simpl simpr
        wa opeq2d preq12d oveq12d df-xps ovex ovmpoa syl2anc eqtrid ) AFDEUDUEZ
        HUFZGUGUEZNADUHUIEUHUIVSWAUJADJQUKAEKRUKUBUCDEUHUHBCUBURZULUMZUCURZULUM
        ZUSBURUNUOCURUNUPZUQZUFZWBUTUMZUSWBUNZUOWDUNZUPZVAUEZUGUEWAUDWBDUJZWDEU
        JZVJZWHVTWMGUGWPWGHWPWGBCLMWFUQZHWNWCLUJWEMUJWGWQUJWOWNWCDULUMLWBDULVBO
        VCWOWEEULUMMWDEULVBPVCBCWCWELMWFVDVESVCVFWPWMIUSDUNZUOEUNZUPZVAUEGWPWII
        WLWTVAWPWIDUTUMZIWNWIXAUJWOWBDUTVBVGTVCWPWJWRWKWSWPWBDUSWNWOVHVKWPWDEUO
        WNWOVIVKVLVMUAVCVMBCUCUBVNVTGUGVOVPVQVR $.

      $( The indexed structure product that appears in ~ xpsval has the same
         base as the target of the function ` F ` .  (Contributed by Mario
         Carneiro, 15-Aug-2015.)  (Revised by Jim Kingdon, 25-Sep-2023.) $)
      xpsrnbas $p |- ( ph -> ran F = ( Base ` U ) ) $=
        ( vk cbs cfv c2o cv c0 cop c1o cpr cixp crn cvv con0 eqid wcel csca a1i
        fvexi 2on wfn fnpr2o syl2anc prdsbas2 wceq cif fvprif 3expia imp fveq2d
        wa wi ifeq12 mp2an fvif eqtr4i eqtr4di ixpeq2dva xpsfrn eqtr2d ) AGUCUD
        ZUBUEUBUFZUGDUHUIEUHUJZUDZUCUDZUKZHULZAUBWAWCIUEUMUNGUAWAUOIUMUPAIDUQTU
        SURUEUNUPAUTURADJUPZEKUPZWCUEVAQRDEJKVBVCVDAWFUBUEWBUGVEZLMVFZUKWGAUBUE
        WEWKAWBUEUPZVKZWEWJDEVFZUCUDZWKWMWDWNUCAWLWDWNVEZAWHWIWLWPVLQRWHWIWLWPD
        EWBJKVGVHVCVIVJWKWJDUCUDZEUCUDZVFZWOLWQVEMWRVEWKWSVEOPWJLWQMWRVMVNWJDEU
        CVOVPVQVRBCLMUBHSVSVQVT $.
    $}

    $( The base set of the binary structure product.  (Contributed by Mario
       Carneiro, 15-Aug-2015.) $)
    xpsbas $p |- ( ph -> ( X X. Y ) = ( Base ` T ) ) $=
      ( vx vy c0 cop c1o cpr eqid cxp csca cfv cprds co cv cmpo ccnv crn xpsval
      cvv xpsrnbas wf1o wfo xpsff1o2 f1ocnv ax-mp f1ofo mp1i ovexd imasbas ) AG
      HUAZBUBUCZPBQRCQSZUDUEZDNOGHPNUFQROUFQSUGZUHZVFUIZUKANOBCDVEVFVCEFGHIJKLM
      VFTZVCTZVETZUJANOBCDVEVFVCEFGHIJKLMVIVJVKULVHVBVGUMZVHVBVGUNAVBVHVFUMVLNO
      GHVFVIUOVBVHVFUPUQVHVBVGURUSAVCVDUDUTVA $.

    xpsadd.3 $e |- ( ph -> A e. X ) $.
    xpsadd.4 $e |- ( ph -> B e. Y ) $.
    xpsadd.5 $e |- ( ph -> C e. X ) $.
    xpsadd.6 $e |- ( ph -> D e. Y ) $.
    xpsadd.7 $e |- ( ph -> ( A .x. C ) e. X ) $.
    xpsadd.8 $e |- ( ph -> ( B .X. D ) e. Y ) $.
    ${
      xpsaddlem.m $e |- .x. = ( E ` R ) $.
      xpsaddlem.n $e |- .X. = ( E ` S ) $.
      xpsaddlem.p $e |- .xb = ( E ` T ) $.
      xpsaddlem.f $e |- F = ( x e. X , y e. Y
        |-> { <. (/) , x >. , <. 1o , y >. } ) $.
      xpsaddlem.u $e |- U =
        ( ( Scalar ` R ) Xs_ { <. (/) , R >. , <. 1o , S >. } ) $.
      xpsaddlem.1 $e |- ( ( ph /\
        { <. (/) , A >. , <. 1o , B >. } e. ran F
        /\ { <. (/) , C >. , <. 1o , D >. } e. ran F ) ->
        ( ( `' F ` { <. (/) , A >. , <. 1o , B >. } )
          .xb ( `' F ` { <. (/) , C >. , <. 1o , D >. } ) ) =
        ( `' F ` ( { <. (/) , A >. , <. 1o , B >. }
          ( E ` U ) { <. (/) , C >. , <. 1o , D >. } ) ) ) $.
      xpsaddlem.2 $e |- ( ( { <. (/) , R >. , <. 1o , S >. } Fn 2o /\
        { <. (/) , A >. , <. 1o , B >. } e. ( Base ` U ) /\
        { <. (/) , C >. , <. 1o , D >. } e. ( Base ` U ) ) ->
        ( { <. (/) , A >. , <. 1o , B >. }
          ( E ` U ) { <. (/) , C >. , <. 1o , D >. } ) =
        ( k e. 2o |-> ( ( { <. (/) , A >. , <. 1o , B >. } ` k )
        ( E ` ( { <. (/) , R >. , <. 1o , S >. } ` k ) )
        ( { <. (/) , C >. , <. 1o , D >. } ` k ) ) ) ) $.
      $( Lemma for ~ xpsadd and ~ xpsmul .  (Contributed by Mario Carneiro,
         15-Aug-2015.) $)
      xpsaddlem $p |- ( ph ->
        ( <. A , B >. .xb <. C , D >. ) = <. ( A .x. C ) , ( B .X. D ) >. ) $=
        ( c0 cop c1o cpr ccnv cfv co crn wcel df-ov xpsfval syl2anc eqtr3id cxp
        wceq opelxpd wf1o wf xpsff1o2 f1of ax-mp ffvelcdmi eqeltrrd mpd3an23 wi
        syl f1ocnvfv sylancr mpd oveq12d c2o cv cmpt cif iftrue fveq2d oveq123d
        wa eqtr4di eqtr4d iffalse pm2.61i adantr simpr fvprif syl3anc mpteq2dva
        wn 3eqtr4a wfn cbs csca eqid xpsrnbas eleqtrd dffn5 sylib 3eqtr4d eqtrd
        fnpr2o 3eqtr3d ) AUTDVAVBEVAVCZQVDZVEZUTFVAVBGVAVCZYBVEZJVFZYAYDNPVEVFZ
        YBVEZDEVAZFGVAZJVFDFLVFZEGMVFZVAZAYAQVGZVHYDYNVHYFYHVNAYIQVEZYAYNAYODEQ
        VFZYADEQVIADTVHZEUAVHZYPYAVNUGUHBCTUAQDEUPVJVKVLZAYITUAVMZVHZYOYNVHADET
        UAUGUHVOZYTYNYIQYTYNQVPZYTYNQVQBCTUAQUPVRZYTYNQVSVTZWAWEWBZAYJQVEZYDYNA
        UUGFGQVFZYDFGQVIAFTVHZGUAVHZUUHYDVNUIUJBCTUAQFGUPVJVKVLZAYJYTVHZUUGYNVH
        AFGTUAUIUJVOZYTYNYJQUUEWAWEWBZURWCAYCYIYEYJJAYOYAVNZYCYIVNZYSAUUCUUAUUO
        UUPWDUUDUUBYTYNYIYAQWFWGWHAUUGYDVNZYEYJVNZUUKAUUCUULUUQUURWDUUDUUMYTYNY
        JYDQWFWGWHWIAYHUTYKVAVBYLVAVCZYBVEZYMAYGUUSYBAOWJOWKZYAVEZUVAYDVEZUVAUT
        HVAVBIVAVCZVEZPVEZVFZWLZOWJUVAUUSVEZWLZYGUUSAOWJUVGUVIAUVAWJVHZWQZUVAUT
        VNZDEWMZUVMFGWMZUVMHIWMZPVEZVFZUVMYKYLWMZUVGUVIUVMUVRUVSVNUVMUVRYKUVSUV
        MUVNDUVOFUVQLUVMUVQHPVELUVMUVPHPUVMHIWNWOUMWRUVMDEWNUVMFGWNWPUVMYKYLWNW
        SUVMXGZUVRYLUVSUVTUVNEUVOGUVQMUVTUVQIPVEMUVTUVPIPUVMHIWTWOUNWRUVMDEWTUV
        MFGWTWPUVMYKYLWTWSXAUVLUVBUVNUVCUVOUVFUVQUVLUVEUVPPUVLHRVHZISVHZUVKUVEU
        VPVNAUWAUVKUEXBAUWBUVKUFXBAUVKXCZHIUVARSXDXEWOUVLYQYRUVKUVBUVNVNAYQUVKU
        GXBAYRUVKUHXBUWCDEUVATUAXDXEUVLUUIUUJUVKUVCUVOVNAUUIUVKUIXBAUUJUVKUJXBU
        WCFGUVATUAXDXEWPUVLYKTVHZYLUAVHZUVKUVIUVSVNAUWDUVKUKXBAUWEUVKULXBUWCYKY
        LUVATUAXDXEXHXFAUVDWJXIZYANXJVEZVHYDUWGVHYGUVHVNAUWAUWBUWFUEUFHIRSXSVKA
        YAYNUWGUUFABCHIKNQHXKVEZRSTUAUBUCUDUEUFUPUWHXLUQXMZXNAYDYNUWGUUNUWIXNUS
        XEAUUSWJXIZUUSUVJVNAUWDUWEUWJUKULYKYLTUAXSVKOWJUUSXOXPXQWOAYMQVEZUUSVNZ
        UUTYMVNZAUWKYKYLQVFZUUSYKYLQVIAUWDUWEUWNUUSVNUKULBCTUAQYKYLUPVJVKVLAUUC
        YMYTVHUWLUWMWDUUDAYKYLTUAUKULVOYTYNYMUUSQWFWGWHXRXT $.
    $}

    ${
      xpsadd.m $e |- .x. = ( +g ` R ) $.
      xpsadd.n $e |- .X. = ( +g ` S ) $.
      xpsadd.p $e |- .xb = ( +g ` T ) $.
      $( Value of the addition operation in a binary structure product.
         (Contributed by Mario Carneiro, 15-Aug-2015.) $)
      xpsadd $p |- ( ph ->
        ( <. A , B >. .xb <. C , D >. ) = <. ( A .x. C ) , ( B .X. D ) >. ) $=
        ( vx vy vk vd vc va vb csca cfv c0 cop c1o cprds co cplusg cv cmpo eqid
        cpr cxp ccnv crn cvv wf1o wfo xpsff1o2 f1ocnv mp1i f1ofo f1ocpbl xpsval
        syl xpsrnbas ovexd imasaddval c2o wfn cbs wcel w3a con0 fvexd 2on simp1
        a1i simp2 simp3 prdsplusgval xpsaddlem ) AUJUKBCDEFGHIJKFUQURZUSFUTVAGU
        TVHZVBVCZULVDUJUKNOUSUJVEUTVAUKVEUTVHVFZLMNOPQRSTUAUBUCUDUEUFUGUHUIXBVG
        ZXAVGZANOVIZXAHXAVDURZIXBVJZXBVKZUSBUTVACUTVHZUSDUTVAEUTVHZVLUMUNUOUPAX
        HXEXGVMZXHXEXGVNXEXHXBVMXKAUJUKNOXBXCVOXEXHXBVPVQZXHXEXGVRWAAUOVEUPVEUN
        VEUMVEXFXGXHXEXLVSAUJUKFGIXAXBWSLMNOPQRSTXCWSVGZXDVTAUJUKFGIXAXBWSLMNOP
        QRSTXCXMXDWBAWSWTVBWCXFVGZUIWDWTWEWFZXIXAWGURZWHZXJXPWHZWIZULXPXFWTWSXI
        XJWEVLWJXAXDXPVGXSFUQWKWEWJWHXSWLWNXOXQXRWMXOXQXRWOXOXQXRWPXNWQWR $.
    $}

    ${
      xpsmul.m $e |- .x. = ( .r ` R ) $.
      xpsmul.n $e |- .X. = ( .r ` S ) $.
      xpsmul.p $e |- .xb = ( .r ` T ) $.
      $( Value of the multiplication operation in a binary structure product.
         (Contributed by Mario Carneiro, 15-Aug-2015.) $)
      xpsmul $p |- ( ph ->
        ( <. A , B >. .xb <. C , D >. ) = <. ( A .x. C ) , ( B .X. D ) >. ) $=
        ( vx vy vk vd vc va vb csca cfv c0 cop c1o cpr cprds co cmulr cmpo eqid
        cxp ccnv crn cvv wf1o wfo xpsff1o2 f1ocnv mp1i f1ofo syl f1ocpbl xpsval
        xpsrnbas ovexd imasmulval c2o wfn cbs wcel w3a con0 fvexd 2on a1i simp1
        cv simp2 simp3 prdsmulrval xpsaddlem ) AUJUKBCDEFGHIJKFUQURZUSFUTVAGUTV
        BZVCVDZULVEUJUKNOUSUJWNUTVAUKWNUTVBVFZLMNOPQRSTUAUBUCUDUEUFUGUHUIXBVGZX
        AVGZANOVHZXAHXAVEURZIXBVIZXBVJZUSBUTVACUTVBZUSDUTVAEUTVBZVKUMUNUOUPAXHX
        EXGVLZXHXEXGVMXEXHXBVLXKAUJUKNOXBXCVNXEXHXBVOVPZXHXEXGVQVRAUOWNUPWNUNWN
        UMWNXFXGXHXEXLVSAUJUKFGIXAXBWSLMNOPQRSTXCWSVGZXDVTAUJUKFGIXAXBWSLMNOPQR
        STXCXMXDWAAWSWTVCWBXFVGZUIWCWTWDWEZXIXAWFURZWGZXJXPWGZWHZULXPWTWSXFXIXJ
        WDVKWIXAXDXPVGXSFUQWJWDWIWGXSWKWLXOXQXRWMXOXQXRWOXOXQXRWPXNWQWR $.
    $}
  $}

  ${
    $d a k x y A $.  $d a c k x y B $.  $d a c k G $.  $d a b c K $.  $d x W $.
    $d a c k x y C $.  $d a c k x y R $.  $d a c k x y S $.  $d a b c x y X $.
    $d a b c k ph $.  $d k x y .x. $.  $d k x y .X. $.  $d a b c x y Y $.
    $d a b c .xb $.
    xpssca.t $e |- T = ( R Xs. S ) $.
    xpssca.g $e |- G = ( Scalar ` R ) $.
    xpssca.1 $e |- ( ph -> R e. V ) $.
    xpssca.2 $e |- ( ph -> S e. W ) $.
    $( Value of the scalar field of a binary structure product.  For
       concreteness, we choose the scalar field to match the left argument, but
       in most cases where this slot is meaningful both factors will have the
       same scalar field, so that it doesn't matter which factor is chosen.
       (Contributed by Mario Carneiro, 15-Aug-2015.) $)
    xpssca $p |- ( ph -> G = ( Scalar ` T ) ) $=
      ( vx vy c0 cop c1o csca cfv cvv eqid cpr cprds co wcel fvexi prex prdssca
      a1i cbs cxp cv cmpo ccnv crn xpsval xpsrnbas wf1o wfo xpsff1o2 mp1i f1ofo
      f1ocnv syl ovexd imassca eqtrd ) AEENBOZPCOZUAZUBUCZQRZDQRAVJVIESSVJTZESU
      DAEBQIUEUHVISUDAVGVHUFUHUGABUIRZCUIRZUJZVJDLMVMVNNLUKOPMUKOUAULZUMZVKVPUN
      ZSALMBCDVJVPEFGVMVNHVMTZVNTZJKVPTZIVLUOALMBCDVJVPEFGVMVNHVSVTJKWAIVLUPAVR
      VOVQUQZVRVOVQURVOVRVPUQWBALMVMVNVPWAUSVOVRVPVBUTVRVOVQVAVCAEVIUBVDVKTVEVF
      $.

    xpsvsca.x $e |- X = ( Base ` R ) $.
    xpsvsca.y $e |- Y = ( Base ` S ) $.
    xpsvsca.k $e |- K = ( Base ` G ) $.
    xpsvsca.m $e |- .x. = ( .s ` R ) $.
    xpsvsca.n $e |- .X. = ( .s ` S ) $.
    xpsvsca.p $e |- .xb = ( .s ` T ) $.
    xpsvsca.3 $e |- ( ph -> A e. K ) $.
    xpsvsca.4 $e |- ( ph -> B e. X ) $.
    xpsvsca.5 $e |- ( ph -> C e. Y ) $.
    xpsvsca.6 $e |- ( ph -> ( A .x. B ) e. X ) $.
    xpsvsca.7 $e |- ( ph -> ( A .X. C ) e. Y ) $.
    $( Value of the scalar multiplication function in a binary structure
       product.  (Contributed by Mario Carneiro, 15-Aug-2015.) $)
    xpsvsca $p |- ( ph ->
        ( A .xb <. B , C >. ) = <. ( A .x. B ) , ( A .X. C ) >. ) $=
      ( vx vy vc va vb vk c0 cop c1o cpr cv cmpo ccnv cfv cprds cvsca wcel wceq
      co crn df-ov eqid xpsfval syl2anc eqtr3id cxp opelxpd wf1o xpsff1o2 ax-mp
      wf f1of ffvelcdmi syl eqeltrrd cvv xpsval xpsrnbas wfo f1ocnv f1ofo ovexd
      mp1i csca wtru fvexi prex prdssca mptru f1ovscpbl imasvscaval mpd3an23 wi
      a1i f1ocnvfv sylancr mpd oveq2d c2o wa cif iftrue fveq2d eqtr4di oveq123d
      cmpt eqidd eqtr4d iffalse pm2.61i adantr fvprif syl3anc 3eqtr4a mpteq2dva
      wn simpr cbs 2on wfn fnpr2o eleqtrd prdsvscaval dffn5 sylib 3eqtr4d eqtrd
      con0 3eqtr3d ) ABURCUSUTDUSVAZULUMOPURULVBUSUTUMVBUSVAVCZVDZVEZGVJZBUUAKU
      REUSZUTFUSZVAZVFVJZVGVEZVJZUUCVEZBCDUSZGVJBCIVJZBDJVJZUSZABLVHUUAUUBVKZVH
      UUEUULVIUGAUUMUUBVEZUUAUUQAUURCDUUBVJZUUACDUUBVLACOVHZDPVHZUUSUUAVIUHUIUL
      UMOPUUBCDUUBVMZVNVOVPZAUUMOPVQZVHZUURUUQVHACDOPUHUIVRZUVDUUQUUMUUBUVDUUQU
      UBVSZUVDUUQUUBWBULUMOPUUBUVBVTZUVDUUQUUBWCWAWDWEWFZAUVDUUIGUUJHUUCKLUUQBU
      UAWGUNUOUPAULUMEFHUUIUUBKMNOPQUAUBSTUVBRUUIVMZWHAULUMEFHUUIUUBKMNOPQUAUBS
      TUVBRUVJWIZAUUQUVDUUCVSZUUQUVDUUCWJUVGUVLAUVHUVDUUQUUBWKWNZUUQUVDUUCWLWEA
      KUUHVFWMKUUIWOVEVIWPUUIUUHKWGWGUVJKWGVHZWPKEWORWQZXEUUHWGVHWPUUFUUGWRXEWS
      WTUCUUJVMZUFAUOVBUPVBUNVBUUJUUCLUUQUVDUVMXAXBXCAUUDUUMBGAUURUUAVIZUUDUUMV
      IZUVCAUVGUVEUVQUVRXDUVHUVFUVDUUQUUMUUAUUBXFXGXHXIAUULURUUNUSUTUUOUSVAZUUC
      VEZUUPAUUKUVSUUCAUQXJBUQVBZUUAVEZUWAUUHVEZVGVEZVJZXQUQXJUWAUVSVEZXQZUUKUV
      SAUQXJUWEUWFAUWAXJVHZXKZBUWAURVIZCDXLZUWJEFXLZVGVEZVJZUWJUUNUUOXLZUWEUWFU
      WJUWNUWOVIUWJUWNUUNUWOUWJBBUWKCUWMIUWJUWMEVGVEIUWJUWLEVGUWJEFXMXNUDXOUWJB
      XRUWJCDXMXPUWJUUNUUOXMXSUWJYGZUWNUUOUWOUWPBBUWKDUWMJUWPUWMFVGVEJUWPUWLFVG
      UWJEFXTXNUEXOUWPBXRUWJCDXTXPUWJUUNUUOXTXSYAUWIBBUWBUWKUWDUWMUWIUWCUWLVGUW
      IEMVHZFNVHZUWHUWCUWLVIAUWQUWHSYBAUWRUWHTYBAUWHYHZEFUWAMNYCYDXNUWIBXRUWIUU
      TUVAUWHUWBUWKVIAUUTUWHUHYBAUVAUWHUIYBUWSCDUWAOPYCYDXPUWIUUNOVHZUUOPVHZUWH
      UWFUWOVIAUWTUWHUJYBAUXAUWHUKYBUWSUUNUUOUWAOPYCYDYEYFAUQUUIYIVEZUUHKUUJBUU
      AXJLWGYSUUIUVJUXBVMUVPUCUVNAUVOXEXJYSVHAYJXEAUWQUWRUUHXJYKSTEFMNYLVOUGAUU
      AUUQUXBUVIUVKYMYNAUVSXJYKZUVSUWGVIAUWTUXAUXCUJUKUUNUUOOPYLVOUQXJUVSYOYPYQ
      XNAUUPUUBVEZUVSVIZUVTUUPVIZAUXDUUNUUOUUBVJZUVSUUNUUOUUBVLAUWTUXAUXGUVSVIU
      JUKULUMOPUUBUUNUUOUVBVNVOVPAUVGUUPUVDVHUXEUXFXDUVHAUUNUUOOPUJUKVRUVDUUQUU
      PUVSUUBXFXGXHYRYT $.
  $}

  ${
    $d c d k x y A $.  $d d k x y C $.  $d a b c d k ph $.  $d a b c d k x R $.
    $d c d k x y B $.  $d d k x y D $.  $d a b c d k S $.  $d a b c d x y X $.
    $d c d .<_ $.  $d x W $.  $d a b c d x y Y $.
    xpsle.t $e |- T = ( R Xs. S ) $.
    xpsle.x $e |- X = ( Base ` R ) $.
    xpsle.y $e |- Y = ( Base ` S ) $.
    xpsle.1 $e |- ( ph -> R e. V ) $.
    xpsle.2 $e |- ( ph -> S e. W ) $.
    xpsle.p $e |- .<_ = ( le ` T ) $.
    $( Closure of the ordering in a binary structure product.  (Contributed by
       Mario Carneiro, 15-Aug-2015.) $)
    xpsless $p |- ( ph -> .<_ C_ ( ( X X. Y ) X. ( X X. Y ) ) ) $=
      ( vx vy c0 cop eqid cxp csca cfv c1o cpr cprds co cv cmpo ccnv crn xpsval
      cvv xpsrnbas wf1o wfo xpsff1o2 f1ocnv mp1i f1ofo syl ovexd imasless ) AHI
      UAZBUBUCZRBSUDCSUEZUFUGZDPQHIRPUHSUDQUHSUEUIZUJZEVHUKZUMAPQBCDVGVHVEFGHIJ
      KLMNVHTZVETZVGTZULAPQBCDVGVHVEFGHIJKLMNVKVLVMUNAVJVDVIUOZVJVDVIUPVDVJVHUO
      VNAPQHIVHVKUQVDVJVHURUSVJVDVIUTVAAVEVFUFVBOVC $.

    xpsle.m $e |- M = ( le ` R ) $.
    xpsle.n $e |- N = ( le ` S ) $.
    xpsle.3 $e |- ( ph -> A e. X ) $.
    xpsle.4 $e |- ( ph -> B e. Y ) $.
    xpsle.5 $e |- ( ph -> C e. X ) $.
    xpsle.6 $e |- ( ph -> D e. Y ) $.
    $( Value of the ordering in a binary structure product.  (Contributed by
       Mario Carneiro, 20-Aug-2015.) $)
    xpsle $p |- ( ph ->
        ( <. A , B >. .<_ <. C , D >. <-> ( A M C /\ B N D ) ) ) $=
      ( vx vy va vb vc vd vk c0 cop c1o cpr cv cmpo ccnv cfv csca cprds co cple
      wbr wa crn wcel wb df-ov wceq eqid xpsfval syl2anc eqtr3id cxp opelxpd wf
      wf1o xpsff1o2 ax-mp ffvelcdmi syl eqeltrrd cvv xpsval xpsrnbas wfo f1ocnv
      f1of f1ofo ovexd f1olecpbl imasleval mpd3an23 wi f1ocnvfv sylancr breq12d
      mp1i mpd c2o wral cbs fvexd 2on a1i fnpr2o eleqtrd prdsleval df2o3 raleqi
      con0 wfn 0ex 1oex fveq2 2fveq3 breq123d ralpr bitri fvpr0o fveq2d eqtr4di
      fvpr1o anbi12d bitrid bitrd 3bitr3d ) AUOBUPUQCUPURZUHUINOUOUHUSUPUQUIUSU
      PURUTZVAZVBZUODUPUQEUPURZYNVBZIVGZYLYPFVCVBZUOFUPUQGUPURZVDVEZVFVBZVGZBCU
      PZDEUPZIVGBDJVGZCEKVGZVHZAYLYMVIZVJYPUUIVJYRUUCVKAUUDYMVBZYLUUIAUUJBCYMVE
      ZYLBCYMVLABNVJZCOVJZUUKYLVMUDUEUHUINOYMBCYMVNZVOVPVQZAUUDNOVRZVJZUUJUUIVJ
      ABCNOUDUEVSZUUPUUIUUDYMUUPUUIYMWAZUUPUUIYMVTUHUINOYMUUNWBZUUPUUIYMWLWCZWD
      WEWFZAUUEYMVBZYPUUIAUVCDEYMVEZYPDEYMVLADNVJZEOVJZUVDYPVMUFUGUHUINOYMDEUUN
      VOVPVQZAUUEUUPVJZUVCUUIVJADENOUFUGVSZUUPUUIUUEYMUVAWDWEWFZAUUPUUAHYNIUUBU
      UIYLYPWGUJUKULUMAUHUIFGHUUAYMYSLMNOPQRSTUUNYSVNZUUAVNZWHAUHUIFGHUUAYMYSLM
      NOPQRSTUUNUVKUVLWIZAUUIUUPYNWAZUUIUUPYNWJUUSUVNAUUTUUPUUIYMWKXBZUUIUUPYNW
      MWEAYSYTVDWNUAUUBVNZAUJUSUKUSULUSUMUSYNUUBUUIUUPUVOWOWPWQAYOUUDYQUUEIAUUJ
      YLVMZYOUUDVMZUUOAUUSUUQUVQUVRWRUUTUURUUPUUIUUDYLYMWSWTXCAUVCYPVMZYQUUEVMZ
      UVGAUUSUVHUVSUVTWRUUTUVIUUPUUIUUEYPYMWSWTXCXAAUUCUNUSZYLVBZUWAYPVBZUWAYTV
      BVFVBZVGZUNXDXEZUUHAUNUUAXFVBZYTYSYLYPXDUUBWGXOUUAUVLUWGVNAFVCXGXDXOVJAXH
      XIAFLVJZGMVJZYTXDXPSTFGLMXJVPAYLUUIUWGUVBUVMXKAYPUUIUWGUVJUVMXKUVPXLUWFUO
      YLVBZUOYPVBZUOYTVBZVFVBZVGZUQYLVBZUQYPVBZUQYTVBZVFVBZVGZVHZAUUHUWFUWEUNUO
      UQURZXEUWTUWEUNXDUXAXMXNUWEUWNUWSUNUOUQXQXRUWAUOVMUWBUWJUWCUWKUWDUWMUWAUO
      YLXSUWAUOVFYTXTUWAUOYPXSYAUWAUQVMUWBUWOUWCUWPUWDUWRUWAUQYLXSUWAUQVFYTXTUW
      AUQYPXSYAYBYCAUWNUUFUWSUUGAUWJBUWKDUWMJAUULUWJBVMUDBCNYDWEAUWMFVFVBJAUWLF
      VFAUWHUWLFVMSFGLYDWEYEUBYFAUVEUWKDVMUFDENYDWEYAAUWOCUWPEUWRKAUUMUWOCVMUEB
      COYGWEAUWRGVFVBKAUWQGVFAUWIUWQGVMTFGMYGWEYEUCYFAUVFUWPEVMUGDEOYGWEYAYHYIY
      JYK $.
  $}


$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Moore spaces
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

  $c Moore mrCls mrInd ACS $.

  $( The class of Moore systems. $)
  cmre $a class Moore $.

  $( The class function generating Moore closures. $)
  cmrc $a class mrCls $.

  $( ` mrInd ` is a class function which takes a Moore system to its set of
     independent sets. $)
  cmri $a class mrInd $.

  $( The class of algebraic closure (Moore) systems. $)
  cacs $a class ACS $.

  ${
    $d c f s x $.

    $( Define a _Moore collection_, which is a family of subsets of a base set
       which preserve arbitrary intersection.  Elements of a Moore collection
       are termed _closed_; Moore collections generalize the notion of
       closedness from topologies ( ~ cldmre ) and vector spaces ( ~ lssmre )
       to the most general setting in which such concepts make sense.
       Definition of Moore collection of sets in [Schechter] p. 78.  A Moore
       collection may also be called a _closure system_ (Section 0.6 in
       [Gratzer] p. 23.)  The name _Moore collection_ is after Eliakim Hastings
       Moore, who discussed these systems in Part I of [Moore] p. 53 to 76.

       See ~ ismre , ~ mresspw , ~ mre1cl and ~ mreintcl for the major
       properties of a Moore collection.  Note that a Moore collection uniquely
       determines its base set ( ~ mreuni ); as such the disjoint union of all
       Moore collections is sometimes considered as ` U. ran Moore ` ,
       justified by ~ mreunirn .  (Contributed by Stefan O'Rear, 30-Jan-2015.)
       (Revised by David Moews, 1-May-2017.) $)
    df-mre $a |- Moore = ( x e. _V |-> { c e. ~P ~P x | ( x e. c /\
        A. s e. ~P c ( s =/= (/) -> |^| s e. c ) ) } ) $.

    $( Define the _Moore closure_ of a generating set, which is the smallest
       closed set containing all generating elements.  Definition of Moore
       closure in [Schechter] p. 79.  This generalizes topological closure
       ( ~ mrccls ) and linear span ( ~ mrclsp ).

       A Moore closure operation ` N ` is (1) extensive, i.e.,
       ` x C_ ( N `` x ) ` for all subsets ` x ` of the base set ( ~ mrcssid ),
       (2) isotone, i.e., ` x C_ y ` implies that ` ( N `` x ) C_ ( N `` y ) `
       for all subsets ` x ` and ` y ` of the base set ( ~ mrcss ), and (3)
       idempotent, i.e., ` ( N `` ( N `` x ) ) = ( N `` x ) ` for all subsets
       ` x ` of the base set ( ~ mrcidm .)  Operators satisfying these three
       properties are in bijective correspondence with Moore collections, so
       these properties may be used to give an alternate characterization of a
       Moore collection by providing a closure operation ` N ` on the set of
       subsets of a given base set which satisfies (1), (2), and (3); the
       closed sets can be recovered as those sets which equal their closures
       (Section 4.5 in [Schechter] p. 82.)  (Contributed by Stefan O'Rear,
       31-Jan-2015.)  (Revised by David Moews, 1-May-2017.) $)
    df-mrc $a |- mrCls = ( c e. U. ran Moore |-> ( x e. ~P U. c |->
        |^| { s e. c | x C_ s } ) ) $.

    $( In a Moore system, a set is _independent_ if no element of the set is in
       the closure of the set with the element removed (Section 0.6 in
       [Gratzer] p. 27; Definition 4.1.1 in [FaureFrolicher] p. 83.) ` mrInd `
       is a class function which takes a Moore system to its set of independent
       sets.  (Contributed by David Moews, 1-May-2017.) $)
    df-mri $a |- mrInd = ( c e. U. ran Moore |->
                 { s e. ~P U. c |
                   A. x e. s -. x e. ( ( mrCls ` c ) ` ( s \ { x } ) ) } ) $.

    $( An important subclass of Moore systems are those which can be
       interpreted as closure under some collection of operators of finite
       arity (the collection itself is not required to be finite).  These are
       termed _algebraic closure systems_; similar to definition (A) of an
       algebraic closure system in [Schechter] p. 84, but to avoid the
       complexity of an arbitrary mixed collection of functions of various
       arities (especially if the axiom of infinity ~ omex is to be avoided),
       we consider a single function defined on finite sets instead.
       (Contributed by Stefan O'Rear, 2-Apr-2015.) $)
    df-acs $a |- ACS = ( x e. _V |-> { c e. ( Moore ` x ) |
            E. f ( f : ~P x --> ~P x /\ A. s e. ~P x ( s e. c <->
                    U. ( f " ( ~P s i^i Fin ) ) C_ s ) ) } ) $.
  $}

  ${
    $d C c s x $.  $d X c s x $.  $d S c s x $.
    $( Property of being a Moore collection on some base set.  (Contributed by
       Stefan O'Rear, 30-Jan-2015.) $)
    ismre $p |- ( C e. ( Moore ` X ) <-> ( C C_ ~P X /\ X e. C /\
        A. s e. ~P C ( s =/= (/) -> |^| s e. C ) ) ) $=
      ( vc vx cmre cfv wcel cvv cpw cv wi wral wa crab wceq pweq anbi1d eleq2
      wb wss wne cint w3a elfvex elex 3ad2ant2 wel pweqd eleq1 rabeqbidv df-mre
      vpwex pwex rabex fvmpt3i eleq2d imbi2d raleqbidv anbi12d elrab a1i elpw2g
      c0 pwexg syl 3anass bitr4di 3bitrd pm5.21nii ) ABFGZHZBIHZABJZUAZBAHZCKZV
      DUBZVQUCZAHZLZCAJZMZUDZABFUEVPVOVMWCBAUFUGVMVLABDKZHZVRVSWEHZLZCWEJZMZNZD
      VNJZOZHZAWLHZVPWCNZNZWDVMVKWMAEBEDUHZWJNZDEKZJZJZOWMIFWTBPZWSWKDXBWLXCXAV
      NWTBQUIXCWRWFWJWTBWEUJRUKECDULWSDXBXAEUMUNUOUPUQWNWQTVMWKWPDAWLWEAPZWFVPW
      JWCWEABSXDWHWACWIWBWEAQXDWGVTVRWEAVSSURUSUTVAVBVMWQVOWPNWDVMWOVOWPVMVNIHW
      OVOTBIVEAVNIVCVFRVOVPWCVGVHVIVJ $.

    $( The Moore collection generator is a well-behaved function.  Analogue for
       Moore collections of ~ fntopon for topologies.  (Contributed by Stefan
       O'Rear, 30-Jan-2015.) $)
    fnmre $p |- Moore Fn _V $=
      ( vx vc vs cvv wel cv c0 wne cint wcel wi wral crab cmre vpwex pwex rabex
      cpw wa df-mre fnmpti ) ADABECFZGHUBIBFZJKCUCRLSZBAFRZRZMNUDBUFUEAOPQACBTU
      A $.

    $( A Moore collection is a subset of the power of the base set; each closed
       subset of the system is actually a subset of the base.  (Contributed by
       Stefan O'Rear, 30-Jan-2015.) $)
    mresspw $p |- ( C e. ( Moore ` X ) -> C C_ ~P X ) $=
      ( vs cmre cfv wcel cpw wss cv c0 wne cint wi wral ismre simp1bi ) ABDEFAB
      GHBAFCIZJKQLAFMCAGNABCOP $.

    $( A Moore-closed subset is a subset.  (Contributed by Stefan O'Rear,
       31-Jan-2015.) $)
    mress $p |- ( ( C e. ( Moore ` X ) /\ S e. C ) -> S C_ X ) $=
      ( cmre cfv wcel wa cpw mresspw sselda elpwid ) ACDEFZBAFGBCLACHBACIJK $.

    $( In any Moore collection the base set is closed.  (Contributed by Stefan
       O'Rear, 30-Jan-2015.) $)
    mre1cl $p |- ( C e. ( Moore ` X ) -> X e. C ) $=
      ( vs cmre cfv wcel cpw wss cv c0 wne cint wi wral ismre simp2bi ) ABDEFAB
      GHBAFCIZJKQLAFMCAGNABCOP $.

    $( A nonempty collection of closed sets has a closed intersection.
       (Contributed by Stefan O'Rear, 30-Jan-2015.) $)
    mreintcl $p |- ( ( C e. ( Moore ` X ) /\ S C_ C /\ S =/= (/) ) ->
        |^| S e. C ) $=
      ( vs cmre cfv wcel wss c0 wne w3a cpw cv cint wral elpw2g biimpar 3adant3
      wi ismre simp3bi 3ad2ant1 simp3 neeq1 inteq eleq1d imbi12d rspcva syl3anc
      wceq 3impia ) ACEFZGZBAHZBIJZKBALZGZDMZIJZURNZAGZSZDUPOZUOBNZAGZUMUNUQUOU
      MUQUNBAULPQRUMUNVCUOUMACLHCAGVCACDTUAUBUMUNUOUCUQVCUOVEVBUOVESDBUPURBUJZU
      SUOVAVEURBIUDVFUTVDAURBUEUFUGUHUKUI $.

    $d I s y $.  $d X y $.  $d C y $.
    $( A nonempty indexed intersection of closed sets is closed.  (Contributed
       by Stefan O'Rear, 1-Feb-2015.) $)
    mreiincl $p |- ( ( C e. ( Moore ` X ) /\ I =/= (/) /\
          A. y e. I S e. C ) -> |^|_ y e. I S e. C ) $=
      ( vs cmre cfv wcel c0 wne wral w3a ciin cv wceq wrex cab 3ad2ant3 wex wss
      cint dfiin2g simp1 uniiunlem ibi wi nfra1 nfre1 nfab nfcv nfne nfim com12
      n0 elisset rspe ex syl5 rexcom4 imbitrdi syld abn0 imbitrrdi exlimi sylbi
      rsp imp 3adant1 mreintcl syl3anc eqeltrd ) BEGHIZDJKZCBIZADLZMZADCNZFOCPZ
      ADQZFRZUBZBVPVMVRWBPVNAFDCBUCSVQVMWABUAZWAJKZWBBIVMVNVPUDVPVMWCVNVPWCAFDC
      BBUEUFSVNVPWDVMVNVPWDVNAODIZATVPWDUGZADUOWEWFAVPWDAVOADUHAWAJVTAFVSADUIUJ
      AJUKULUMWEVPVTFTZWDWEVPVOWGVPWEVOVOADVGUNWEVOVSFTZADQZWGVOWHWEWIFCBUPWEWH
      WIWHADUQURUSVSAFDUTVAVBVTFVCVDVEVFVHVIBWAEVJVKVL $.

    $( The relative intersection of a set of closed sets is closed.
       (Contributed by Stefan O'Rear, 3-Apr-2015.) $)
    mrerintcl $p |- ( ( C e. ( Moore ` X ) /\ S C_ C ) ->
        ( X i^i |^| S ) e. C ) $=
      ( cmre cfv wcel wss wa cint cin wceq rint0 adantl mre1cl ad2antrr eqeltrd
      c0 wne w3a cpw simp2 mresspw 3ad2ant1 sstrd simp3 rintn0 syl2anc mreintcl
      3expa pm2.61dane ) ACDEFZBAGZHZCBIZJZAFZBQUMBQKZHUOCAUQUOCKUMCBLMUKCAFULU
      QACNOPUKULBQRZUPUKULURSZUOUNAUSBCTZGURUOUNKUSBAUTUKULURUAUKULAUTGURACUBUC
      UDUKULURUECBUFUGABCUHPUIUJ $.

    $( The relative intersection of a family of closed sets is closed.
       (Contributed by Stefan O'Rear, 3-Apr-2015.) $)
    mreriincl $p |- ( ( C e. ( Moore ` X ) /\ A. y e. I S e. C ) ->
        ( X i^i |^|_ y e. I S ) e. C ) $=
      ( cmre cfv wcel wral wa ciin c0 wceq riin0 adantl mre1cl ad2antrr eqeltrd
      cin wne wss mress ex ralimdv imp riinn0 sylan simpll simpr simplr syl3anc
      mreiincl pm2.61dane ) BEFGHZCBHZADIZJZEADCKZSZBHDLUQDLMZJUSEBUTUSEMUQAECD
      NOUNEBHUPUTBEPQRUQDLTZJZUSURBUQCEUAZADIZVAUSURMUNUPVDUNUOVCADUNUOVCBCEUBU
      CUDUEAECDUFUGVBUNVAUPURBHUNUPVAUHUQVAUIUNUPVAUJABCDEULUKRUM $.

    $( Two closed sets have a closed intersection.  (Contributed by Stefan
       O'Rear, 30-Jan-2015.) $)
    mreincl $p |- ( ( C e. ( Moore ` X ) /\ A e. C /\ B e. C ) ->
        ( A i^i B ) e. C ) $=
      ( cmre cfv wcel w3a cpr cint cin wceq intprg 3adant1 c0 simp1 prssi prnzg
      wss wne 3ad2ant2 mreintcl syl3anc eqeltrrd ) CDEFGZACGZBCGZHZABIZJZABKZCU
      FUGUJUKLUEABCCMNUHUEUICSZUIOTZUJCGUEUFUGPUFUGULUEABCQNUFUEUMUGABCRUACUIDU
      BUCUD $.

    $( Since the entire base set of a Moore collection is the greatest element
       of it, the base set can be recovered from a Moore collection by set
       union.  (Contributed by Stefan O'Rear, 30-Jan-2015.) $)
    mreuni $p |- ( C e. ( Moore ` X ) -> U. C = X ) $=
      ( cmre cfv wcel cpw wss cuni wceq mre1cl mresspw elpwuni biimpa syl2anc )
      ABCDEBAEZABFGZAHBIZABJABKOPQABLMN $.

    $( Two ways to express the notion of being a Moore collection on an
       unspecified base.  (Contributed by Stefan O'Rear, 30-Jan-2015.) $)
    mreunirn $p |- ( C e. U. ran Moore <-> C e. ( Moore ` U. C ) ) $=
      ( vx cmre crn cuni wcel cfv cv cvv wrex wfn wb fnmre fnunirn ax-mp mreuni
      fveq2d eleq2d ibir rexlimivw sylbi fvssunirn sseli impbii ) ACDEZFZAAEZCG
      ZFZUFABHZCGZFZBIJZUICIKUFUMLMBACINOULUIBIULUIULUHUKAULUGUJCAUJPQRSTUAUHUE
      ACUGUBUCUD $.
  $}

  ${
    $d ph s $.  $d C s $.  $d X s $.
    ismred.ss $e |- ( ph -> C C_ ~P X ) $.
    ismred.ba $e |- ( ph -> X e. C ) $.
    ismred.in $e |- ( ( ph /\ s C_ C /\ s =/= (/) ) -> |^| s e. C ) $.
    $( Properties that determine a Moore collection.  (Contributed by Stefan
       O'Rear, 30-Jan-2015.) $)
    ismred $p |- ( ph -> C e. ( Moore ` X ) ) $=
      ( cpw wss wcel cv c0 wne cint wi wral cmre cfv velpw 3expia sylan2b ismre
      ralrimiva syl3anbrc ) ABCHICBJDKZLMZUENBJZOZDBHZPBCQRJEFAUHDUIUEUIJAUEBIZ
      UHDBSAUJUFUGGTUAUCBCDUBUD $.
  $}

  ${
    $d ph s $.  $d C s $.  $d X s $.
    ismred2.ss $e |- ( ph -> C C_ ~P X ) $.
    ismred2.in $e |- ( ( ph /\ s C_ C ) -> ( X i^i |^| s ) e. C ) $.
    $( Properties that determine a Moore collection, using restricted
       intersection.  (Contributed by Stefan O'Rear, 3-Apr-2015.) $)
    ismred2 $p |- ( ph -> C e. ( Moore ` X ) ) $=
      ( c0 cint cin wceq eqid rint0 ax-mp wss wcel 0ss cv wa wi 0ex sseq1 inteq
      anbi2d ineq2d eleq1d imbi12d vtocl mpan2 eqeltrrid wne w3a simp2 3ad2ant1
      cpw sstrd simp3 rintn0 syl2anc 3adant3 eqeltrrd ismred ) ABCDEACCGHZIZBGG
      JVCCJGKCGLMAGBNZVCBOZBPADQZBNZRZCVFHZIZBOZSAVDRZVESDGTVFGJZVHVLVKVEVMVGVD
      AVFGBUAUCVMVJVCBVMVIVBCVFGUBUDUEUFFUGUHUIAVGVFGUJZUKZVJVIBVOVFCUNZNVNVJVI
      JVOVFBVPAVGVNULAVGBVPNVNEUMUOAVGVNUPCVFUQURAVGVKVNFUSUTVA $.
  $}

  ${
    $d V a b c $.  $d X a b c $.

    $( The Moore collections of subsets of a space, viewed as a kind of subset
       of the power set, form a Moore collection in their own right on the
       power set.  (Contributed by Stefan O'Rear, 30-Jan-2015.) $)
    mremre $p |- ( X e. V -> ( Moore ` X ) e. ( Moore ` ~P X ) ) $=
      ( va vb vc wcel cpw wss cv mresspw c0 wne w3a cint 3ad2ant1 mpbird ismred
      wb wa sselda cmre cfv velpw sylibr ssriv a1i ssidd cuni intssuni2 3adant1
      pwidg unipw sseqtrdi elpw2g wel wex intss1 adantl simpr syl sstrd exlimdv
      n0 ex biimtrid 3impia wral mre1cl ralrimiva elintg simp12 simpl2 mreintcl
      simp2 simpl3 syl3anc cvv intex sylbi 3ad2ant3 ) BAFZBUAUBZBGZCWBWCGZHWACW
      BWDCIZWBFWEWCHZWEWDFWEBJCWCUCUDUEUFWAWCBCWAWCUGBAUKWAWFWEKLZMZWENZWCFZWIB
      HZWHWIWCUHZBWFWGWIWLHWAWEWCUIUJBULUMWAWFWJWKRWGWIBAUNOPQWAWEWBHZWGMZWIBDW
      AWMWGWIWCHZWGDCUOZDUPWAWMSZWODWEVCWQWPWODWQWPWOWQWPSZWIDIZWCWPWIWSHWQWSWE
      UQURWRWSWBFZWSWCHWQWEWBWSWAWMUSTWSBJUTVAVDVBVEVFWNBWIFZBWSFZDWEVGZWNXBDWE
      WNWPSWTXBWNWEWBWSWAWMWGVNTWSBVHUTVIWAWMXAXCRWGDBWEAVJOPWNWSWIHZWSKLZMZWSN
      ZWIFZXGEIZFZEWEVGZXFXJEWEXFECUOZSZXIWBFWSXIHXEXJXFWEWBXIWAWMWGXDXEVKTXMWS
      WIXIWNXDXEXLVLXLWIXIHXFXIWEUQURVAWNXDXEXLVOXIWSBVMVPVIXEWNXHXKRZXDXEXGVQF
      XNWSVREXGWEVQVJVSVTPQQ $.
  $}

  ${
    $d A x $.  $d C x $.  $d X x $.
    $( The subcollection of a closed set system below a given closed set is
       itself a closed set system.  (Contributed by Stefan O'Rear,
       9-Mar-2015.) $)
    submre $p |- ( ( C e. ( Moore ` X ) /\ A e. C ) ->
        ( C i^i ~P A ) e. ( Moore ` A ) ) $=
      ( vx cmre cfv wcel wa cpw cin wss inss2 a1i simpr pwidg adantl elind sstr
      mpan2 3ad2ant2 cv c0 wne w3a cint simp1l inss1 mreintcl syl3anc intssuni2
      simp3 cuni syl2anc unipw sseqtrdi wb elpw2g 3ad2ant1 mpbird ismred ) BCEF
      GZABGZHZBAIZJZADVEVDKZVCBVDLZMVCBVDAVAVBNVBAVDGVAABOPQVCDUAZVEKZVHUBUCZUD
      ZBVDVHUEZVKVAVHBKZVJVLBGVAVBVIVJUFVIVCVMVJVIVEBKVMBVDUGVHVEBRSTVCVIVJUKZB
      VHCUHUIVKVLVDGZVLAKZVKVLVDULZAVKVHVDKZVJVLVQKVIVCVRVJVIVFVRVGVHVEVDRSTVNV
      HVDUJUMAUNUOVCVIVOVPUPZVJVBVSVAVLABUQPURUSQUT $.
  $}

  ${
    $d x y $.
    $( The ordering of the extended real number structure.  (Contributed by
       Mario Carneiro, 21-Aug-2015.) $)
    xrsle $p |- <_ = ( le ` RR*s ) $=
      ( vx vy cle cvv wcel cxrs cple cfv wceq cxr cxp xrex lerelxr ssexi cv wbr
      xpex cxne cxad co cif cmpo cxmu cordt df-xrs odrngle ax-mp ) CDECFGHICJJK
      JJLLQMNJABJJAOZBOZCPUIUHRSTUHUIRSTUAUBSUCCUDHCDFABUEUFUG $.
  $}

  $( The "less than or equal to" relation in the extended real numbers.
     (Contributed by Thierry Arnoux, 14-Mar-2018.) $)
  xrge0le $p |- <_ = ( le ` ( RR*s |`s ( 0 [,] +oo ) ) ) $=
    ( cc0 cpnf cicc co cvv wcel cle cxrs cress cple wceq ovex eqid xrsle ressle
    cfv ax-mp ) ABCDZEFGHRIDZJPKABCLRHGESSMNOQ $.

  ${
    $d x y $.
    $( The base set of the extended real number structure.  (Contributed by
       Mario Carneiro, 21-Aug-2015.) $)
    xrsbas $p |- RR* = ( Base ` RR*s ) $=
      ( vx vy cxr cvv wcel cxrs cbs cfv wceq xrex cv cle wbr cxne cxad cif cmpo
      co cxmu cordt df-xrs odrngbas ax-mp ) CDECFGHIJCABCCAKZBKZLMUEUDNORUDUENO
      RPQOSLTHLDFABUAUBUC $.
  $}

  $( The base of the extended nonnegative real numbers.  (Contributed by
     Thierry Arnoux, 30-Jan-2017.) $)
  xrge0base $p |- ( 0 [,] +oo ) = ( Base ` ( RR*s |`s ( 0 [,] +oo ) ) ) $=
    ( cc0 cpnf cicc cxr cin cxrs cress cbs cfv wss wceq iccssxr dfss2 mpbi wcel
    co cvv ovex eqid xrsbas ressbas ax-mp eqtr3i ) ABCPZDEZUDFUDGPZHIZUDDJUEUDK
    ABLUDDMNUDQOUEUGKABCRUDDUFQFUFSTUAUBUC $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Moore closures
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d F c x s $.  $d C c x s $.  $d X c x s $.  $d U c x s $.  $d V c x s $.
    $( The domain and codomain of the function expression for Moore closures.
       (Contributed by Stefan O'Rear, 31-Jan-2015.) $)
    mrcflem $p |- ( C e. ( Moore ` X ) ->
        ( x e. ~P X |-> |^| { s e. C | x C_ s } ) : ~P X --> C ) $=
      ( cmre cfv wcel cpw cv wss crab cint wa wne simpl ssrab2 a1i sseq2 mre1cl
      c0 adantr elpwi adantl elrabd ne0d mreintcl syl3anc fmpttd ) BCEFGZACHZAI
      ZDIZJZDBKZLZBUIUKUJGZMZUIUNBJZUNTNUOBGUIUPOURUQUMDBPQUQUNCUQUMUKCJZDCBULC
      UKRUICBGUPBCSUAUPUSUIUKCUBUCUDUEBUNCUFUGUH $.

    $( Moore-closure is a well-behaved function.  (Contributed by Stefan
       O'Rear, 1-Feb-2015.) $)
    fnmrc $p |- mrCls Fn U. ran Moore $=
      ( vx vc vs cv cuni cpw wss crab cint cmpt cvv wcel cmrc cmre df-mrc fnmpt
      crn wfn cfv mreunirn cxp mrcflem fssxp syl vuniex pwex xpex ssexg sylancl
      wf vex sylbi mprg ) ABDZEZFZADCDGCUNHIJZKLZMNQEZRBUSBUSUQMKACBOPUNUSLUNUO
      NSLZURUNTUTUQUPUNUAZGZVAKLURUTUPUNUQUJVBAUNUOCUBUPUNUQUCUDUPUNUOBUEUFBUKU
      GUQVAKUHUIULUM $.

    mrcfval.f $e |- F = ( mrCls ` C ) $.
    $( Value of the function expression for the Moore closure.  (Contributed by
       Stefan O'Rear, 31-Jan-2015.) $)
    mrcfval $p |- ( C e. ( Moore ` X ) -> F =
        ( x e. ~P X |-> |^| { s e. C | x C_ s } ) ) $=
      ( vc cmre cfv wcel cmrc cpw cv wss crab cint cmpt cuni wceq cvv fvssunirn
      crn sseli unieq pweqd rabeq inteqd mpteq12dv df-mrc cxp wf mreunirn sylbi
      mrcflem fssxp syl vuniex pwex vex xpex ssexg sylancl fvmpt3 mpteq1d eqtrd
      mreuni eqtrid ) BDHIZJZCBKIZADLZAMEMNZEBOZPZQZFVIVJABRZLZVNQZVOVIBHUBRZJV
      JVRSVHVSBHDUAUCGBAGMZRZLZVLEVTOZPZQZVRVSKTVTBSZAWBWDVQVNWFWAVPVTBUDUEWFWC
      VMVLEVTBUFUGUHAEGUIVTVSJZWEWBVTUJZNZWHTJWETJWGWBVTWEUKZWIWGVTWAHIJWJVTULA
      VTWAEUNUMWBVTWEUOUPWBVTWAGUQURGUSUTWEWHTVAVBVCUPVIAVQVKVNVIVPDBDVFUEVDVEV
      G $.

    $( The Moore closure is a function mapping arbitrary subsets to closed
       sets.  (Contributed by Stefan O'Rear, 31-Jan-2015.) $)
    mrcf $p |- ( C e. ( Moore ` X ) -> F : ~P X --> C ) $=
      ( vx vs cmre cfv wcel cpw wf cv wss crab cint cmpt mrcflem mrcfval mpbird
      feq1d ) ACGHIZCJZABKUBAEUBELFLMFANOPZKEACFQUAUBABUCEABCFDRTS $.

    $( Evaluation of the Moore closure of a set.  (Contributed by Stefan
       O'Rear, 31-Jan-2015.)  (Proof shortened by Fan Zheng, 6-Jun-2016.) $)
    mrcval $p |- ( ( C e. ( Moore ` X ) /\ U C_ X ) -> ( F ` U ) =
        |^| { s e. C | U C_ s } ) $=
      ( vx cmre cfv wcel wss wa cv crab cint cpw cvv cmpt wceq adantr inteqd wb
      mrcfval sseq1 rabbidv adantl mre1cl elpw2g syl biimpar c0 wne sseq2 simpr
      elrabd ne0d intex sylib fvmptd ) ADHIJZBDKZLZGBGMZEMZKZEANZOZBVDKZEANZOZD
      PZCQUTCGVKVGRSVAGACDEFUCTVCBSZVGVJSVBVLVFVIVLVEVHEAVCBVDUDUEUAUFUTBVKJZVA
      UTDAJZVMVAUBADUGZBDAUHUIUJVBVIUKULVJQJVBVIDVBVHVAEDAVDDBUMUTVNVAVOTUTVAUN
      UOUPVIUQURUS $.

    $( The Moore closure of a set is a closed set.  (Contributed by Stefan
       O'Rear, 31-Jan-2015.) $)
    mrccl $p |- ( ( C e. ( Moore ` X ) /\ U C_ X ) -> ( F ` U ) e. C ) $=
      ( cmre cfv wcel wss wa cpw wf mrcf adantr mre1cl elpw2g biimpar ffvelcdmd
      wb syl ) ADFGHZBDIZJDKZABCUAUCACLUBACDEMNUABUCHZUBUADAHUDUBSADOBDAPTQR $.

    $( The Moore closure of a singleton is a closed set.  (Contributed by
       Stefan O'Rear, 31-Jan-2015.) $)
    mrcsncl $p |- ( ( C e. ( Moore ` X ) /\ U e. X ) -> ( F ` { U } ) e. C ) $=
      ( wcel cmre cfv csn wss snssi mrccl sylan2 ) BDFADGHFBIZDJNCHAFBDKANCDELM
      $.

    $( The closure of a closed set is itself.  (Contributed by Stefan O'Rear,
       31-Jan-2015.) $)
    mrcid $p |- ( ( C e. ( Moore ` X ) /\ U e. C ) -> ( F ` U ) = U ) $=
      ( vs cmre cfv wcel wa cv crab cint wceq mress mrcval syldan intmin adantl
      wss eqtrd ) ADGHIZBAIZJBCHZBFKTFALMZBUBUCBDTUDUENABDOABCDFEPQUCUEBNUBFBAR
      SUA $.

    $( The closure of a set is a subset of the base.  (Contributed by Stefan
       O'Rear, 31-Jan-2015.) $)
    mrcssv $p |- ( C e. ( Moore ` X ) -> ( F ` U ) C_ X ) $=
      ( cmre cfv wcel crn cuni fvssunirn cpw wf wss mrcf frn uniss 3syl sseqtrd
      mreuni sstrid ) ADFGHZBCGCIZJZDCBKUBUDAJZDUBDLZACMUCANUDUENACDEOUFACPUCAQ
      RADTSUA $.

    $( A set is closed iff it is equal to its closure.  (Contributed by Stefan
       O'Rear, 31-Jan-2015.) $)
    mrcidb $p |- ( C e. ( Moore ` X ) -> ( U e. C <-> ( F ` U ) = U ) ) $=
      ( cmre cfv wcel wceq mrcid wa simpr mrcssv adantr eqsstrrd mrccl eqeltrrd
      wss syldan impbida ) ADFGHZBAHBCGZBIZABCDEJUAUCKZUBBAUAUCLZUAUCBDRUBAHUDB
      UBDUEUAUBDRUCABCDEMNOABCDEPSQT $.

    $( Closure preserves subset ordering.  (Contributed by Stefan O'Rear,
       31-Jan-2015.) $)
    mrcss $p |- ( ( C e. ( Moore ` X ) /\ U C_ V /\ V C_ X ) ->
        ( F ` U ) C_ ( F ` V ) ) $=
      ( vs cmre cfv wcel wss w3a cv crab cint wi sstr2 adantr wceq mrcval intss
      ss2rabdv syl 3ad2ant2 simp1 sstr 3adant1 syl2anc 3adant2 3sstr4d ) AEHIJZ
      BDKZDEKZLZBGMZKZGANZOZDUOKZGANZOZBCIZDCIZULUKURVAKZUMULUTUQKVDULUSUPGAULU
      SUPPUOAJBDUOQRUBUTUQUAUCUDUNUKBEKZVBURSUKULUMUEULUMVEUKBDEUFUGABCEGFTUHUK
      UMVCVASULADCEGFTUIUJ $.

    $( The closure of a set is a superset.  (Contributed by Stefan O'Rear,
       31-Jan-2015.) $)
    mrcssid $p |- ( ( C e. ( Moore ` X ) /\ U C_ X ) -> U C_ ( F ` U ) ) $=
      ( vs cmre cfv wcel wss wa cv crab cint ssintub mrcval sseqtrrid ) ADGHIBD
      JKBFLJFAMNBBCHFBAOABCDFEPQ $.

    $( A set is closed iff it contains its closure.  (Contributed by Stefan
       O'Rear, 2-Apr-2015.) $)
    mrcidb2 $p |- ( ( C e. ( Moore ` X ) /\ U C_ X ) ->
        ( U e. C <-> ( F ` U ) C_ U ) ) $=
      ( cmre cfv wcel wss wa wceq wb mrcidb eqss mrcssid biantrud bitr4id bitrd
      adantr ) ADFGHZBDIZJZBAHZBCGZBKZUDBIZTUCUELUAABCDEMSUBUEUFBUDIZJUFUDBNUBU
      GUFABCDEOPQR $.

    $( The closure operation is idempotent.  (Contributed by Stefan O'Rear,
       31-Jan-2015.) $)
    mrcidm $p |- ( ( C e. ( Moore ` X ) /\ U C_ X ) ->
        ( F ` ( F ` U ) ) = ( F ` U ) ) $=
      ( cmre cfv wcel wss wceq mrccl mrcid syldan ) ADFGHBDIBCGZAHNCGNJABCDEKAN
      CDELM $.

    $( The closure is the minimal closed set; any closed set which contains the
       generators is a superset of the closure.  (Contributed by Stefan O'Rear,
       31-Jan-2015.) $)
    mrcsscl $p |- ( ( C e. ( Moore ` X ) /\ U C_ V /\ V e. C ) ->
        ( F ` U ) C_ V ) $=
      ( cmre cfv wcel wss w3a mress 3adant2 mrcss syld3an3 wceq mrcid sseqtrd )
      AEGHIZBDJZDAIZKBCHZDCHZDSTUADEJZUBUCJSUAUDTADELMABCDEFNOSUAUCDPTADCEFQMR
      $.

    $( Idempotence of closure under a general union.  (Contributed by Stefan
       O'Rear, 31-Jan-2015.) $)
    mrcuni $p |- ( ( C e. ( Moore ` X ) /\ U C_ ~P X ) ->
        ( F ` U. U ) = ( F ` U. ( F " U ) ) ) $=
      ( vs vx cfv wcel wss wa cuni cv wral syl2anc adantr unissb sylibr syl3anc
      mrcss cmre cpw cima simpl simpll ssel2 elpwid adantll mrcssid wfun cdm wi
      mrcf ffund fdmd sseq2d biimpar funfvima2 imp elssuni syl ralrimiva mrcssv
      sstrd ralrimivw wfn wb ffnd sseq1 ralima sylan mpbird adantl sspwuni wceq
      bilani mrcidm sseqtrd eqssd ) ADUAHIZBDUBZJZKZBLZCHZCBUCZLZCHZWCVTWDWGJZW
      GDJZWEWHJVTWBUDZWCFMZWGJZFBNWIWCWMFBWCWLBIZKZWLWLCHZWGWOVTWLDJZWLWPJVTWBW
      NUEWBWNWQVTWBWNKWLDBWAWLUFUGUHAWLCDEUIOWOWPWFIZWPWGJWCWNWRWCCUJZBCUKZJZWN
      WRULVTWSWBVTWAACACDEUMZUNPVTXAWBVTWTWABVTWAACXBUOUPUQBWLCUROUSWPWFUTVAVDV
      BFBWGQRWCWQFWFNZWJWCXCGMZCHZDJZGBNZWCXFGBVTXFWBAXDCDEVCPVEVTCWAVFZWBXCXGV
      GVTWAACXBVHZWQXFFGWABCWLXEDVIVJVKVLFWFDQRAWDCWGDETSWCWHWECHZWEWCVTWGWEJZW
      EDJZWHXJJWKWCWLWEJZFWFNZXKWCXNXEWEJZGBNZWCXOGBWCXDBIZKVTXDWDJZWDDJZXOVTWB
      XQUEXQXRWCXDBUTVMWCXSXQWBXSVTBDVNVPZPAXDCWDDETSVBVTXHWBXNXPVGXIXMXOFGWABC
      WLXEWEVIVJVKVLFWFWEQRVTXLWBAWDCDEVCPAWGCWEDETSWCVTXSXJWEVOWKXTAWDCDEVQOVR
      VS $.

    $( Idempotence of closure under a pair union.  (Contributed by Stefan
       O'Rear, 31-Jan-2015.) $)
    mrcun $p |- ( ( C e. ( Moore ` X ) /\ U C_ X /\ V C_ X ) ->
        ( F ` ( U u. V ) ) = ( F ` ( ( F ` U ) u. ( F ` V ) ) ) ) $=
      ( cfv wcel wss cpr cuni cun wceq elpw2g syl biimpar syl2anc fveq2d fvex
      wb cmre w3a cima cpw simp1 mre1cl 3adant3 3adant2 prssd mrcuni uniprg wfn
      mrcf ffnd 3ad2ant1 fnimapr syl3anc unieqd unipr eqtrdi 3eqtr3d ) AEUAGHZB
      EIZDEIZUBZBDJZKZCGZCVFUCZKZCGZBDLZCGBCGZDCGZLZCGVEVBVFEUDZIVHVKMVBVCVDUEV
      EBDVPVBVCBVPHZVDVBVQVCVBEAHZVQVCTAEUFZBEANOPUGZVBVDDVPHZVCVBWAVDVBVRWAVDT
      VSDEANOPUHZUIAVFCEFUJQVEVGVLCVEVQWAVGVLMVTWBBDVPVPUKQRVEVJVOCVEVJVMVNJZKV
      OVEVIWCVECVPULZVQWAVIWCMVBVCWDVDVBVPACACEFUMUNUOVTWBVPBDCUPUQURVMVNBCSDCS
      USUTRVA $.
  $}

  ${
    mrcssd.1 $e |- ( ph -> A e. ( Moore ` X ) ) $.
    mrcssd.2 $e |- N = ( mrCls ` A ) $.
    $( The Moore closure of a set is a subset of the base.  Deduction form of
       ~ mrcssv .  (Contributed by David Moews, 1-May-2017.) $)
    mrcssvd $p |- ( ph -> ( N ` B ) C_ X ) $=
      ( cmre cfv wcel wss mrcssv syl ) ABEHIJCDIEKFBCDEGLM $.

    mrcssd.3 $e |- ( ph -> U C_ V ) $.
    mrcssd.4 $e |- ( ph -> V C_ X ) $.
    $( Moore closure preserves subset ordering.  Deduction form of ~ mrcss .
       (Contributed by David Moews, 1-May-2017.) $)
    mrcssd $p |- ( ph -> ( N ` U ) C_ ( N ` V ) ) $=
      ( cmre cfv wcel wss mrcss syl3anc ) ABFKLMCENEFNCDLEDLNGIJBCDEFHOP $.
  $}

  ${
    mrcssidd.1 $e |- ( ph -> A e. ( Moore ` X ) ) $.
    mrcssidd.2 $e |- N = ( mrCls ` A ) $.
    mrcssidd.3 $e |- ( ph -> U C_ X ) $.
    $( A set is contained in its Moore closure.  Deduction form of ~ mrcssid .
       (Contributed by David Moews, 1-May-2017.) $)
    mrcssidd $p |- ( ph -> U C_ ( N ` U ) ) $=
      ( cmre cfv wcel wss mrcssid syl2anc ) ABEIJKCELCCDJLFHBCDEGMN $.

    $( Moore closure is idempotent.  Deduction form of ~ mrcidm .  (Contributed
       by David Moews, 1-May-2017.) $)
    mrcidmd $p |- ( ph -> ( N ` ( N ` U ) ) = ( N ` U ) ) $=
      ( cmre cfv wcel wss wceq mrcidm syl2anc ) ABEIJKCELCDJZDJPMFHBCDEGNO $.
  $}

  ${
    mressmrcd.1 $e |- ( ph -> A e. ( Moore ` X ) ) $.
    mressmrcd.2 $e |- N = ( mrCls ` A ) $.
    mressmrcd.3 $e |- ( ph -> S C_ ( N ` T ) ) $.
    mressmrcd.4 $e |- ( ph -> T C_ S ) $.
    $( In a Moore system, if a set is between another set and its closure, the
       two sets have the same closure.  Deduction form.  (Contributed by David
       Moews, 1-May-2017.) $)
    mressmrcd $p |- ( ph -> ( N ` S ) = ( N ` T ) ) $=
      ( cfv mrcssvd mrcssd sstrd mrcidmd sseqtrd eqssd ) ACEKZDEKZARSEKSABCESFG
      HIABDEFGHLZMABDEFGHADCFJACSFITNZNOPABDECFGHJUAMQ $.
  $}

  ${
    submrc.f $e |- F = ( mrCls ` C ) $.
    submrc.g $e |- G = ( mrCls ` ( C i^i ~P D ) ) $.
    $( In a closure system which is cut off above some level, closures below
       that level act as normal.  (Contributed by Stefan O'Rear,
       9-Mar-2015.) $)
    submrc $p |- ( ( C e. ( Moore ` X ) /\ D e. C /\ U C_ D ) ->
        ( G ` U ) = ( F ` U ) ) $=
      ( cmre cfv wcel wss w3a 3adant3 mrcssidd mrccl syl2anc mrcsscl syl3anc
      cpw submre simp1 simp3 mress sstrd 3com23 fvex sylibr elind elin1d eqssd
      cin elpw ) AFIJKZBAKZCBLZMZCEJZCDJZUQABTZULZBIJKZCUSLUSVAKURUSLUNUOVBUPBA
      FUANZUQACDFUNUOUPUBZGUQCBFUNUOUPUCZUNUOBFLUPABFUDNUEZOUQAUTUSUQUNCFLUSAKV
      DVFACDFGPQUQUSBLZUSUTKUNUPUOVGACDBFGRUFUSBCDUGUMUHUIVACEUSBHRSUQUNCURLURA
      KUSURLVDUQVACEBVCHVEOUQAUTURUQVBUPURVAKVCVEVACEBHPQUJACDURFGRSUK $.
  $}

  ${
    mrieqvlemd.1 $e |- ( ph -> A e. ( Moore ` X ) ) $.
    mrieqvlemd.2 $e |- N = ( mrCls ` A ) $.
    mrieqvlemd.3 $e |- ( ph -> S C_ X ) $.
    mrieqvlemd.4 $e |- ( ph -> Y e. S ) $.
    $( In a Moore system, if ` Y ` is a member of ` S ` , ` ( S \ { Y } ) ` and
       ` S ` have the same closure if and only if ` Y ` is in the closure of
       ` ( S \ { Y } ) ` .  Used in the proof of ~ mrieqvd and ~ mrieqv2d .
       Deduction form.  (Contributed by David Moews, 1-May-2017.) $)
    mrieqvlemd $p |- ( ph -> ( Y e. ( N ` ( S \ { Y } ) ) <->
                               ( N ` ( S \ { Y } ) ) = ( N ` S ) ) ) $=
      ( csn cdif cfv wcel wceq wa adantr cun mrcssidd simpr undif1 wss ssdifssd
      cmre snssd unssd eqsstrrid unssad difssd mressmrcd eqcomd sseldd eleqtrrd
      impbida ) AFCFKZLZDMZNZUQCDMZOZAURPZUSUQVABCUPDEABEUDMNURGQZHVACUOUQVACUO
      RUPUORUQCUOUAVAUPUOUQVABUPDEVBHVACEUOACEUBURIQUCSVAFUQAURTUEUFUGUHVACUOUI
      UJUKAUTPFUSUQAFUSNUTACUSFABCDEGHISJULQAUTTUMUN $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Independent sets in a Moore system
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d A c s x $.  $d c N $.  $d s X $.
    mrisval.1 $e |- N = ( mrCls ` A ) $.
    mrisval.2 $e |- I = ( mrInd ` A ) $.
    $( Value of the set of independent sets of a Moore system.  (Contributed by
       David Moews, 1-May-2017.) $)
    mrisval $p |- ( A e. ( Moore ` X ) -> I = { s e. ~P X |
                    A. x e. s -. x e. ( N ` ( s \ { x } ) ) } ) $=
      ( vc cmre cfv wcel cv wn wral cuni cpw crab cmri cmrc cdif wceq fvssunirn
      csn sseli unieq pweqd fveq2 eqtr4di fveq1d eleq2d notbid rabeqbidv df-mri
      crn ralbidv vuniex pwex rabex fvmpt3i syl eqtrid mreuni rabeqdv eqtrd ) B
      EJKZLZCAMZFMZVHUDUAZDKZLZNZAVIOZFBPZQZRZVNFEQZRVGCBSKZVQHVGBJUOPZLVSVQUBV
      FVTBJEUCUEIBVHVJIMZTKZKZLZNZAVIOZFWAPZQZRVQVTSWABUBZWFVNFWHVPWIWGVOWABUFU
      GWIWEVMAVIWIWDVLWIWCVKVHWIVJWBDWIWBBTKDWABTUHGUIUJUKULUPUMAFIUNWFFWHWGIUQ
      URUSUTVAVBVGVNFVPVRVGVOEBEVCUGVDVE $.
  $}

  ${
    $d A s x $.  $d s S x $.  $d s X $.  $d s N $.
    ismri.1 $e |- N = ( mrCls ` A ) $.
    ismri.2 $e |- I = ( mrInd ` A ) $.
    $( Criterion for a set to be an independent set of a Moore system.
       (Contributed by David Moews, 1-May-2017.) $)
    ismri $p |- ( A e. ( Moore ` X ) -> ( S e. I <->
                  ( S C_ X /\ A. x e. S -. x e. ( N ` ( S \ { x } ) ) ) ) ) $=
      ( vs cmre cfv wcel cpw cv cdif wn wral wa eleq2d cvv csn wss crab mrisval
      wceq difeq1 fveq2d notbid raleqbi1dv elrab bitrdi wb elfvex elpw2g anbi1d
      syl bitrd ) BFJKLZCDLZCFMZLZANZCVBUAZOZEKZLZPZACQZRZCFUBZVHRURUSCVBINZVCO
      ZEKZLZPZAVKQZIUTUCZLVIURDVQCABDEFIGHUDSVPVHICUTVOVGAVKCVKCUEZVNVFVRVMVEVB
      VRVLVDEVKCVCUFUGSUHUIUJUKURVAVJVHURFTLVAVJULBFJUMCFTUNUPUOUQ $.
  $}

  ${
    $d A x $.  $d S x $.
    ismri2.1 $e |- N = ( mrCls ` A ) $.
    ismri2.2 $e |- I = ( mrInd ` A ) $.
    $( Criterion for a subset of the base set in a Moore system to be
       independent.  (Contributed by David Moews, 1-May-2017.) $)
    ismri2 $p |- ( ( A e. ( Moore ` X ) /\ S C_ X ) ->
                   ( S e. I <-> A. x e. S -. x e. ( N ` ( S \ { x } ) ) ) ) $=
      ( cmre cfv wcel wss cv csn cdif wn wral ismri baibd ) BFIJKCDKCFLAMZCTNOE
      JKPACQABCDEFGHRS $.

    ismri2d.3 $e |- ( ph -> A e. ( Moore ` X ) ) $.
    ismri2d.4 $e |- ( ph -> S C_ X ) $.
    $( Criterion for a subset of the base set in a Moore system to be
       independent.  Deduction form.  (Contributed by David Moews,
       1-May-2017.) $)
    ismri2d $p |- ( ph ->
                    ( S e. I <-> A. x e. S -. x e. ( N ` ( S \ { x } ) ) ) ) $=
      ( cmre cfv wcel wss cv csn cdif wn wral wb ismri2 syl2anc ) ACGLMNDGODENB
      PZDUDQRFMNSBDTUAJKBCDEFGHIUBUC $.

    ismri2dd.5 $e |- ( ph -> A. x e. S -. x e. ( N ` ( S \ { x } ) ) ) $.
    $( Definition of independence of a subset of the base set in a Moore
       system.  One-way deduction form.  (Contributed by David Moews,
       1-May-2017.) $)
    ismri2dd $p |- ( ph -> S e. I ) $=
      ( wcel cv csn cdif cfv wn wral ismri2d mpbird ) ADEMBNZDUBOPFQMRBDSLABCDE
      FGHIJKTUA $.
  $}

  ${
    $d A x $.  $d S x $.
    mriss.1 $e |- I = ( mrInd ` A ) $.
    $( An independent set of a Moore system is a subset of the base set.
       (Contributed by David Moews, 1-May-2017.) $)
    mriss $p |- ( ( A e. ( Moore ` X ) /\ S e. I ) -> S C_ X ) $=
      ( vx cmre cfv wcel wss cv csn cdif cmrc wn wral eqid ismri simprbda ) ADG
      HIBCIBDJFKZBTLMANHZHIOFBPFABCUADUAQERS $.

    mrissd.2 $e |- ( ph -> A e. ( Moore ` X ) ) $.
    mrissd.3 $e |- ( ph -> S e. I ) $.
    $( An independent set of a Moore system is a subset of the base set.
       Deduction form.  (Contributed by David Moews, 1-May-2017.) $)
    mrissd $p |- ( ph -> S C_ X ) $=
      ( cmre cfv wcel wss mriss syl2anc ) ABEIJKCDKCELGHBCDEFMN $.
  $}

  ${
    $d A x $.  $d S x $.  $d x ph $.  $d x Y $.  $d x N $.
    ismri2dad.1 $e |- N = ( mrCls ` A ) $.
    ismri2dad.2 $e |- I = ( mrInd ` A ) $.
    ismri2dad.3 $e |- ( ph -> A e. ( Moore ` X ) ) $.
    ismri2dad.4 $e |- ( ph -> S e. I ) $.
    ismri2dad.5 $e |- ( ph -> Y e. S ) $.
    $( Consequence of a set in a Moore system being independent.  Deduction
       form.  (Contributed by David Moews, 1-May-2017.) $)
    ismri2dad $p |- ( ph -> -. Y e. ( N ` ( S \ { Y } ) ) ) $=
      ( vx cv csn cdif cfv wcel wn wral mrissd ismri2d mpbid wceq simpr difeq2d
      wa sneqd fveq2d eleq12d notbid rspcdv mpd ) AMNZCUNOZPZEQZRZSZMCTZGCGOZPZ
      EQZRZSZACDRUTKAMBCDEFHIJABCDFIJKUAUBUCAUSVEMGCLAUNGUDZUGZURVDVGUNGUQVCAVF
      UEZVGUPVBEVGUOVACVGUNGVHUHUFUIUJUKULUM $.
  $}

  ${
    $d A x $.  $d S x $.  $d x ph $.
    mrieqvd.1 $e |- ( ph -> A e. ( Moore ` X ) ) $.
    mrieqvd.2 $e |- N = ( mrCls ` A ) $.
    mrieqvd.3 $e |- I = ( mrInd ` A ) $.
    mrieqvd.4 $e |- ( ph -> S C_ X ) $.
    $( In a Moore system, a set is independent if and only if, for all elements
       of the set, the closure of the set with the element removed is unequal
       to the closure of the original set.  Part of Proposition 4.1.3 in
       [FaureFrolicher] p. 83.  (Contributed by David Moews, 1-May-2017.) $)
    mrieqvd $p |- ( ph -> ( S e. I <->
                          A. x e. S ( N ` ( S \ { x } ) ) =/= ( N ` S ) ) ) $=
      ( wcel cv csn cdif cfv wn wral wne adantr ismri2d wa wss simpr mrieqvlemd
      cmre necon3bbid ralbidva bitrd ) ADELBMZDUJNOFPZLZQZBDRUKDFPZSZBDRABCDEFG
      IJHKUAAUMUOBDAUJDLZUBZULUKUNUQCDFGUJACGUFPLUPHTIADGUCUPKTAUPUDUEUGUHUI $.

    $d s S x $.  $d s x ph $.  $d s x I $.  $d s x N $.
    $( In a Moore system, a set is independent if and only if all its proper
       subsets have closure properly contained in the closure of the set.  Part
       of Proposition 4.1.3 in [FaureFrolicher] p. 83.  (Contributed by David
       Moews, 1-May-2017.) $)
    mrieqv2d $p |- ( ph -> ( S e. I <->
                             A. s ( s C. S -> ( N ` s ) C. ( N ` S ) ) ) ) $=
      ( vx wcel wpss cfv wa w3a 3ad2ant1 adantr 3expia cv wi wn pssnel 3ad2ant3
      wal wex cdif cmre wceq simprr difsnb simpl3 pssssd ssdifd eqsstrrd simpl2
      csn sylib mrissd ssdifssd mrcssd difssd simprl sseldd ismri2dad ssnelpssd
      mrcssidd sspsstrd exlimddv alrimiv wral wne cvv elfvexd wss difexd simp1r
      ssexd difsnpss simp2 psseq1d mpbird simp3 mpd fveq2d mpbid spcimdv 3impia
      ex pssned 3com23 mrieqvlemd necon3bbid ralrimiv ismri2d sylibrd impbid )
      ACDMZGUAZCNZWTEOZCEOZNZUBZGUFZAWSXFAWSPXEGAWSXAXDAWSXAQZLUAZCMZXHWTMUCZPZ
      XDLXAAXKLUGWSLWTCUDUEXGXKPZXBCXHURZUHZEOZXCXLBWTEXNFXGBFUIOMZXKAWSXPXAHRS
      ZIXLWTWTXMUHZXNXLXJXRWTUJXGXIXJUKXHWTULUSXLWTCXMXLWTCAWSXAXKUMUNUOUPXLCFX
      MXLBCDFJXQAWSXAXKUQZUTZVAVBXLXOXCXHXLBXNECFXQIXLCXMVCXTVBXLCXCXHXLBCEFXQI
      XTVHXGXIXJVDZVEXLBCDEFXHIJXQXSYAVFVGVIVJTVKWJAXFXHXOMZUCZLCVLZWSAXFYDAXFP
      YCLCAXFXIYCAXFXIQZYCXOXCVMZAXIXFYFAXIXFQXOXCAXIXFXOXCNZAXIPZXEYGGXNVNYHCX
      MVNYHCFVNYHBUIFAXPXIHSVOACFVPZXIKSVSVQYHWTXNUJZXEYGYHYJXEQZXDYGYKXAXDYKXA
      XNCNZYKXIYLAXIYJXEVRXHCVTUSYKWTXNCYHYJXEWAZWBWCYHYJXEWDWEYKXBXOXCYKWTXNEY
      MWFWBWGTWHWIWKWLYEYBXOXCYEBCEFXHAXFXPXIHRIAXFYIXIKRAXFXIWDWMWNWCTWOWJALBC
      DEFIJHKWPWQWR $.
  $}

  ${
    $d A s $.  $d s S $.  $d s T $.  $d s X $.  $d s ph $.  $d s I $.
    $d s N $.
    mrissmrcd.1 $e |- ( ph -> A e. ( Moore ` X ) ) $.
    mrissmrcd.2 $e |- N = ( mrCls ` A ) $.
    mrissmrcd.3 $e |- I = ( mrInd ` A ) $.
    mrissmrcd.4 $e |- ( ph -> S C_ ( N ` T ) ) $.
    mrissmrcd.5 $e |- ( ph -> T C_ S ) $.
    mrissmrcd.6 $e |- ( ph -> S e. I ) $.
    $( In a Moore system, if an independent set is between a set and its
       closure, the two sets are equal (since the two sets must have equal
       closures by ~ mressmrcd , and so are equal by ~ mrieqv2d .)
       (Contributed by David Moews, 1-May-2017.) $)
    mrissmrcd $p |- ( ph -> S = T ) $=
      ( vs wpss wn wceq cfv wi psseq1d mressmrcd pssne necomd necon2bi syl wcel
      cv wal mrissd mrieqv2d mpbid cvv ssexd wa simpr fveq2d imbi12d spcdv mtod
      mpd wss wo sspss sylib ord eqcomd ) ADCADCOZPDCQZAVGDFRZCFRZOZAVJVIQVKPAB
      CDFGHIKLUAVKVJVIVKVIVJVIVJUBUCUDUEANUGZCOZVLFRZVJOZSZNUHZVGVKSZACEUFVQMAB
      CEFGNHIJABCEGJHMUIUJUKAVPVRNDULADCEMLUMAVLDQZUNZVMVGVOVKVTVLDCAVSUOZTVTVN
      VIVJVTVLDFWAUPTUQURUTUSAVGVHADCVAVGVHVBLDCVCVDVEUTVF $.
  $}

  ${
    $d A x $.  $d S x $.  $d T x $.  $d x ph $.
    mrissmrid.1 $e |- ( ph -> A e. ( Moore ` X ) ) $.
    mrissmrid.2 $e |- N = ( mrCls ` A ) $.
    mrissmrid.3 $e |- I = ( mrInd ` A ) $.
    mrissmrid.4 $e |- ( ph -> S e. I ) $.
    mrissmrid.5 $e |- ( ph -> T C_ S ) $.
    $( In a Moore system, subsets of independent sets are independent.
       (Contributed by David Moews, 1-May-2017.) $)
    mrissmrid $p |- ( ph -> T e. I ) $=
      ( vx mrissd sstrd cdif cfv wcel wn wral cv csn ismri2d mpbid sseld ssdifd
      ssdifssd mrcssd ssneld imim12d ralimdv2 mpd ismri2dd ) AMBDEFGIJHADCGLABC
      EGJHKNZOAMUAZCUOUBZPZFQZRSZMCTZUODUPPZFQZRSZMDTACERUTKAMBCEFGIJHUNUCUDAUS
      VCMCDAUODRUOCRUSVCADCUOLUEAVBURUOABVAFUQGHIADCUPLUFACGUPUNUGUHUIUJUKULUM
      $.
  $}

  ${
    $d s X y $.  $d s S y z $.  $d s ph y z $.  $d s y Y z $.  $d s y z Z $.
    $d s y z N $.
    mreexd.1 $e |- ( ph -> X e. V ) $.
    mreexd.2 $e |- ( ph -> A. s e. ~P X A. y e. X
                     A. z e. ( ( N ` ( s u. { y } ) ) \ ( N ` s ) )
                     y e. ( N ` ( s u. { z } ) ) ) $.
    mreexd.3 $e |- ( ph -> S C_ X ) $.
    mreexd.4 $e |- ( ph -> Y e. X ) $.
    mreexd.5 $e |- ( ph -> Z e. ( N ` ( S u. { Y } ) ) ) $.
    mreexd.6 $e |- ( ph -> -. Z e. ( N ` S ) ) $.
    $( In a Moore system, the closure operator is said to have the _exchange
       property_ if, for all elements ` y ` and ` z ` of the base set and
       subsets ` S ` of the base set such that ` z ` is in the closure of
       ` ( S u. { y } ) ` but not in the closure of ` S ` , ` y ` is in the
       closure of ` ( S u. { z } ) ` (Definition 3.1.9 in [FaureFrolicher]
       p. 57 to 58.)  This theorem allows to construct substitution instances
       of this definition.  (Contributed by David Moews, 1-May-2017.) $)
    mreexd $p |- ( ph -> Y e. ( N ` ( S u. { Z } ) ) ) $=
      ( csn cun cfv wcel cv cdif wral cpw sselpwd wceq wa adantr ad2antrr simpr
      simplr uneq12d fveq2d eleqtrrd wn neleqtrrd eldifd simpllr eleq12d rspcdv
      sneqd rspcimdv mpd ) ABUAZJUAZCUAZQZRZESZTZCVEVDQZRZESZVEESZUBZUCZBGUCZJG
      UDZUCHDIQZRZESZTZLAVQWBJDVRADGFKMUEAVEDUFZUGZVPWBBHGAHGTWCNUHWDVDHUFZUGZV
      JWBCIVOWFIVMVNWFIDHQZRZESZVMAIWITWCWEOUIWFVLWHEWFVEDVKWGAWCWEUKZWFVDHWDWE
      UJVAULUMUNWFVNDESZIAIWKTUOWCWEPUIWFVEDEWJUMUPUQWFVFIUFZUGZVDHVIWAWDWEWLUK
      WMVHVTEWMVEDVGVSAWCWEWLURWMVFIWFWLUJVAULUMUSUTVBVBVC $.
  $}

  ${
    $d A x $.  $d s X y $.  $d s S x y z $.  $d s x ph y z $.  $d s x y Y z $.
    $d s y z N $.
    mreexmrid.1 $e |- ( ph -> A e. ( Moore ` X ) ) $.
    mreexmrid.2 $e |- N = ( mrCls ` A ) $.
    mreexmrid.3 $e |- I = ( mrInd ` A ) $.
    mreexmrid.4 $e |- ( ph -> A. s e. ~P X A. y e. X
                        A. z e. ( ( N ` ( s u. { y } ) ) \ ( N ` s ) )
                        y e. ( N ` ( s u. { z } ) ) ) $.
    mreexmrid.5 $e |- ( ph -> S e. I ) $.
    mreexmrid.6 $e |- ( ph -> Y e. X ) $.
    mreexmrid.7 $e |- ( ph -> -. Y e. ( N ` S ) ) $.
    $( In a Moore system whose closure operator has the exchange property, if a
       set is independent and an element is not in its closure, then adding the
       element to the set gives another independent set.  Lemma 4.1.5 in
       [FaureFrolicher] p. 84.  (Contributed by David Moews, 1-May-2017.) $)
    mreexmrid $p |- ( ph -> ( S u. { Y } ) e. I ) $=
      ( cun cfv wcel vx csn mrissd snssd unssd cv cdif wn w3a cvv cmre 3ad2ant1
      wa elfvexd wral cpw ssdifssd simp3 difundir simp2 mrcssidd ssneldd nelneq
      wceq syl2anc elsni nsyl difsnb uneq2d eqtrid fveq2d eleqtrd mreexd undif1
      ismri2dad wss ssequn2 neleqtrrd pm2.65i df-3an mtbi imnani adantlr adantl
      sylib ad2antrr eqneltrd sneqd difeq2d difun2 eqtrdi eqtrd bilani mpjaodan
      wo elun ralrimiva ismri2dd ) AUADEIUBZRZFGHLMKAEWSHADEFHMKOUCZAIHPUDUEAUA
      UFZWTXBUBZUGZGSZTZUHZUAWTAXBWTTZUMZXBETZXGXBWSTZAXJXGXHAXJUMZXFAXJXFUIZXL
      XFUMXMIEXCUGZXCRZGSZTXMBCXNGUJHIXBJXMDUKHAXJDHUKSTXFKULZUNAXJBUFZJUFZCUFU
      BRGSTCXSXRUBRGSXSGSUGUOBHUOJHUPUOXFNULXMEHXCXMDEFHMXQAXJEFTXFOULZUCUQAXJI
      HTXFPULXMXBXEXNWSRZGSAXJXFURXMXDYAGXMXDXNWSXCUGZRYAEWSXCUSXMYBWSXNXMXKUHY
      BWSVDXMXBIVDZXKXMXJIETUHZYCUHAXJXFUTZAXJYDXFAEEGSZIADEGHKLXAVAQVBZULXBIEV
      CVEXBIVFZVGXBWSVHWEVIVJVKVLXMDEFGHXBLMXQXTYEVOVMXMXPYFIAXJIYFTUHZXFQULXMX
      OEGXMXOEXCRZEEXCVNXMXCEVPYJEVDXMXBEYEUDXCEVQWEVJVKVRVSAXJXFVTWAWBWCXIXKUM
      ZXEYFXBYKXBIYFXKYCXIYHWDZAYIXHXKQWFWGYKXDEGYKXDEWSUGZEYKXDWTWSUGYMYKXCWSW
      TYKXBIYLWHWIEWSWJWKAYMEVDZXHXKAYDYNYGIEVHWEWFWLVKVRXHXJXKWOAXBEWSWPWMWNWQ
      WR $.
  $}

  ${
    $d f F g h j $.  $d f g G h j $.  $d f g h H j $.  $d f g h ph j $.
    $d t u f v g h i I j $.  $d t u f v g h K $.  $d t u f v g h N $.
    $d t u f v g h X $.
    mreexexlemd.1 $e |- ( ph -> X e. J ) $.
    mreexexlemd.2 $e |- ( ph -> F C_ ( X \ H ) ) $.
    mreexexlemd.3 $e |- ( ph -> G C_ ( X \ H ) ) $.
    mreexexlemd.4 $e |- ( ph -> F C_ ( N ` ( G u. H ) ) ) $.
    mreexexlemd.5 $e |- ( ph -> ( F u. H ) e. I ) $.
    mreexexlemd.6 $e |- ( ph -> ( F ~~ K \/ G ~~ K ) ) $.
    mreexexlemd.7 $e |- ( ph -> A. t A. u e. ~P ( X \ t ) A. v e. ~P ( X \ t )
                                ( ( ( u ~~ K \/ v ~~ K ) /\
                                  u C_ ( N ` ( v u. t ) ) /\ ( u u. t ) e. I )
                           -> E. i e. ~P v ( u ~~ i /\ ( i u. t ) e. I ) ) ) $.
    $( This lemma is used to generate substitution instances of the induction
       hypothesis in ~ mreexexd .  (Contributed by David Moews, 1-May-2017.) $)
    mreexexlemd $p |- ( ph -> E. j e. ~P G ( F ~~ j /\ ( j u. H ) e. I ) ) $=
      ( vf vg vh cen wbr wo cun cfv wss wcel cv wa cpw wrex w3a wi cdif wal weq
      wral simplr breq1d orbi12d simpll uneq12d fveq2d sseq12d eleq1d 3anbi123d
      simpr simpllr breq12d simplll anbi12d pweqd cbvrexdva2 imbi12d wceq simpl
      difeq2d adantr cbvraldva2 cbvalvw sylib cvv ssun2 difexd sselpwd eleqtrrd
      a1i ssexd ad2antrr uneq2d rexeqbidv rspcdv rspcimdv spcimdv mpd mp3and )
      AGLUEUFZHLUEUFZUGZGHIUHZMUIZUJZGIUHZJUKZGFULZUEUFZXIIUHZJUKZUMZFHUNZUOZTR
      SAUBULZLUEUFZUCULZLUEUFZUGZXPXRUDULZUHZMUIZUJZXPYAUHZJUKZUPZXPXIUEUFZXIYA
      UHZJUKZUMZFXRUNZUOZUQZUCNYAURZUNZVAZUBYPVAZUDUSZXCXFXHUPZXOUQZACULZLUEUFZ
      BULZLUEUFZUGZUUBUUDDULZUHZMUIZUJZUUBUUGUHZJUKZUPZUUBEULZUEUFZUUNUUGUHZJUK
      ZUMZEUUDUNZUOZUQZBNUUGURZUNZVAZCUVCVAZDUSYSUAUVEYRDUDDUDUTZUVDYQCUBUVCYPU
      VFCUBUTZUMZUVAYNBUCUVCYPUVHBUCUTZUMZUUMYGUUTYMUVJUUFXTUUJYDUULYFUVJUUCXQU
      UEXSUVJUUBXPLUEUVFUVGUVIVBZVCUVJUUDXRLUEUVHUVIVKZVCVDUVJUUBXPUUIYCUVKUVJU
      UHYBMUVJUUDXRUUGYAUVLUVFUVGUVIVEZVFVGVHUVJUUKYEJUVJUUBXPUUGYAUVKUVMVFVIVJ
      UVJUURYKEFUUSYLUVJEFUTZUMZUUOYHUUQYJUVOUUBXPUUNXIUEUVFUVGUVIUVNVLUVJUVNVK
      ZVMUVOUUPYIJUVOUUNXIUUGYAUVPUVFUVGUVIUVNVNVFVIVOUVOUUDXRUVHUVIUVNVBVPVQVR
      UVHUVCYPVSUVIUVHUVBYOUVHUUGYANUVFUVGVTWAVPZWBWCUVQWCWDWEAYRUUAUDIWFAIXGJS
      IXGUJAIGWGWKWLAYAIVSZUMZYQUUAUBGYPUVSGNIURZUNZYPAGUWAUKUVRAGUVTWFANIKOWHZ
      PWIWBUVSYOUVTUVSYAINAUVRVKWAVPZWJUVSXPGVSZUMZYNUUAUCHYPUWEHUWAYPAHUWAUKUV
      RUWDAHUVTWFUWBQWIWMUVSYPUWAVSUWDUWCWBWJUWEXRHVSZUMZYGYTYMXOUWGXTXCYDXFYFX
      HUWGXQXAXSXBUWGXPGLUEUVSUWDUWFVBZVCUWGXRHLUEUWEUWFVKZVCVDUWGXPGYCXEUWHUWG
      YBXDMUWGXRHYAIUWIAUVRUWDUWFVLZVFVGVHUWGYEXGJUWGXPGYAIUWHUWJVFVIVJUWGYKXMF
      YLXNUWGXRHUWIVPUWGYHXJYJXLUWGXPGXIUEUWHVCUWGYIXKJUWGYAIXIUWJWNVIVOWOVRWPW
      QWRWSWT $.
  $}

  ${
    mreexexlem2d.1 $e |- ( ph -> A e. ( Moore ` X ) ) $.
    mreexexlem2d.2 $e |- N = ( mrCls ` A ) $.
    mreexexlem2d.3 $e |- I = ( mrInd ` A ) $.
    mreexexlem2d.4 $e |- ( ph -> A. s e. ~P X A. y e. X
                           A. z e. ( ( N ` ( s u. { y } ) ) \ ( N ` s ) )
                           y e. ( N ` ( s u. { z } ) ) ) $.
    mreexexlem2d.5 $e |- ( ph -> F C_ ( X \ H ) ) $.
    mreexexlem2d.6 $e |- ( ph -> G C_ ( X \ H ) ) $.
    mreexexlem2d.7 $e |- ( ph -> F C_ ( N ` ( G u. H ) ) ) $.
    mreexexlem2d.8 $e |- ( ph -> ( F u. H ) e. I ) $.
    ${
      $d s F g y z $.  $d s g G y z $.  $d s g H y z $.  $d s g ph y z $.
      $d s g y Y z $.  $d s g y z N $.  $d s X y $.
      mreexexlem2d.9 $e |- ( ph -> Y e. F ) $.
      $( Used in ~ mreexexlem4d to prove the induction step in ~ mreexexd .
         See the proof of Proposition 4.2.1 in [FaureFrolicher] p. 86 to 87.
         (Contributed by David Moews, 1-May-2017.) $)
      mreexexlem2d $p |- ( ph -> E. g e. G
                              ( -. g e. ( F \ { Y } ) /\
                                ( ( F \ { Y } ) u. ( H u. { g } ) ) e. I ) ) $=
        ( cv wcel csn cdif wn cun wa wex wrex cfv wss cmre simpr ssun2 difundir
        adantr wceq cin c0 incom ssdifin0 syl eqtr3id minel difsnb sylib uneq2d
        syl2anc eqtrid sseqtrrid mrissd ssdifssd mrcssidd sstrd mrcssvd mrcidmd
        unssd mrcssd sseqtrd sseldd sselid ismri2dad pm2.65da nss simprl simprr
        ssun1 ssneldd unass wral cpw difss unss1 mp1i mrissmrid fveq2d neleqtrd
        difss2d mreexmrid eqeltrrid jca32 ex eximdv mpd df-rex sylibr ) AEUCZGU
        DZXIFLUEZUFZUDUGZXLHXIUEZUHUHZIUDZUIZUIZEUJZXQEGUKAXJXIFHUHZXKUFZJULZUD
        UGZUIZEUJZXSAGYBUMZUGYEAYFLYBUDAYFUIZFYBLYGFGHUHZJULZYBAFYIUMYFTURYGYIY
        BJULYBYGDYHJYBKADKUNULUDZYFNURZOYGGHYBAYFUOAHYBUMYFAHYAYBAXLHUHZHYAHXLU
        PAYAXLHXKUFZUHYLFHXKUQAYMHXLALHUDUGZYMHUSALFUDZHFUTZVAUSYNUBAYPFHUTZVAF
        HVBAFKHUFZUMYQVAUSRFKHVCVDVELFHVFVJLHVGVHVIVKZVLADYAJKNOAXTKXKADXTIKPNU
        AVMVNZVOZVPURVSYGDYAJKYKOVQVTYGDYAJKYKOAYAKUMYFYTURVRWAVPAYOYFUBURZWBYG
        DXTIJKLOPYKAXTIUDZYFUAURYGFXTLFHWIUUBWCWDWEEGYBWFVHAYDXREAYDXRAYDUIZXJX
        MXPAXJYCWGZUUDXLYBXIAXLYBUMYDAXLYAYBAYLXLYAXLHWIYSVLUUAVPURAXJYCWHZWJUU
        DXOYLXNUHIXLHXNWKUUDBCDYLIJKXIMAYJYDNURZOPABUCZMUCZCUCUEUHJULUDCUUIUUHU
        EUHJULUUIJULUFWLBKWLMKWMWLYDQURUUDDXTYLIJKUUGOPAUUCYDUAURXLFUMYLXTUMUUD
        FXKWNXLFHWOWPWQUUDGKXIUUDGKHAGYRUMYDSURWTUUEWBUUDYBYLJULXIUUFUUDYAYLJAY
        AYLUSYDYSURWRWSXAXBXCXDXEXFXQEGXGXH $.
    $}

    ${
      $d F i $.  $d G i $.  $d H i $.  $d i I $.
      mreexexlem3d.9 $e |- ( ph -> ( F = (/) \/ G = (/) ) ) $.
      $( Base case of the induction in ~ mreexexd .  (Contributed by David
         Moews, 1-May-2017.) $)
      mreexexlem3d $p |- ( ph ->
                           E. i e. ~P G ( F ~~ i /\ ( i u. H ) e. I ) ) $=
        ( cpw wcel cen wbr cun cv wa wrex c0 wceq simpr wss cdif cin cfv adantr
        cmre uneq1d uncom un0 eqtr3i eqtrdi fveq2d mrissd unssbd mrcssidd unssd
        sseqtrd ssun2 a1i mrissmrcd ssequn1 sylibr ssind disjdif sseqtrdi sylib
        ss0b mpjaodan 0elpw eqeltrdi cvv elfvexd difss2d ssexd enrefg syl breq2
        uneq1 eleq1d anbi12d rspcev syl12anc ) AFGUBZUCFFUDUEZFHUFZIUCZFEUGZUDU
        EZWSHUFZIUCZUHZEWOUIAFUJWOAFUJUKZXDGUJUKZAXDULAXEUHZFUJUMXDXFFHKHUNZUOU
        JXFFHXGXFWQHUKFHUMXFDWQHIJKADKURUPUCXEMUQZNOXFFHHJUPZXFFGHUFZJUPZXIAFXK
        UMXESUQXFXJHJXFXJUJHUFZHXFGUJHAXEULUSHUJUFXLHHUJUTHVAVBVCVDVIXFDHJKXHNX
        FFHKXFDWQIKOXHAWRXETUQZVEVFVGVHHWQUMXFHFVJVKXMVLFHVMVNAFXGUMXEQUQVOHKVP
        VQFVSVRUAVTGWAWBAFWCUCWPAFKWCADURKMWDAFKHQWEWFFWCWGWHTXCWPWRUHEFWOWSFUK
        ZWTWPXBWRWSFFUDWIXNXAWQIWSFHWJWKWLWMWN $.
    $}

    ${
      $d f g h X $.  $d f g h I i j $.  $d f g h L $.  $d f g h N $.
      $d q s y z N $.  $d q r s F y z $.  $d q r s G y z $.  $d q r s H y z $.
      $d q r s ph y z $.  $d q r I i j $.  $d q r ph i $.  $d q r F i j $.
      $d q r G i j $.  $d q r H i j $.  $d s X y $.
      mreexexlem4d.9 $e |- ( ph -> L e. _om ) $.
      mreexexlem4d.A $e |- ( ph ->
                             A. h A. f e. ~P ( X \ h ) A. g e. ~P ( X \ h )
                             ( ( ( f ~~ L \/ g ~~ L ) /\
                               f C_ ( N ` ( g u. h ) ) /\ ( f u. h ) e. I ) ->
                              E. j e. ~P g ( f ~~ j /\ ( j u. h ) e. I ) ) ) $.
      mreexexlem4d.B $e |- ( ph -> ( F ~~ suc L \/ G ~~ suc L ) ) $.
      $( Induction step of the induction in ~ mreexexd .  (Contributed by David
         Moews, 1-May-2017.) $)
      mreexexlem4d $p |- ( ph ->
                           E. j e. ~P G ( F ~~ j /\ ( j u. H ) e. I ) ) $=
        ( vr vq vi cv cen wbr cun wcel wa cpw wrex c0 wceq cmre cfv adantr cdif
        csn wral wss animorrl mreexexlem3d wne wex n0 bilani simpr mreexexlem2d
        wn w3a 3anass cvv ad2antrr simpr2 difsnb sylib ssdifssd ssdifd eqsstrrd
        elfvexd difun1 sseqtrrdi simpr1 uncom uneq2i difsnid uneq1d eqtr3id syl
        unass eqtrid fveq2d sseqtrrd simpr3 csuc wo com simplr 3anan12 dif1ennn
        wi sylbir expcom syl2anc orim12d mpd mreexexlemd ad3antrrr ssexd simprl
        wal difss2d simplr1 snssd unssd sselpwd ad3antlr cin simprrl en2sn el2v
        elpwid a1i disjdifr ssdifin0 syl22anc eqbrtrrd eqtr2i simprrr eqeltrrid
        unen breq2 rexlimddv eleq1d anbi12d rspcev syl12anc sylan2br pm2.61dane
        uneq1 adantlr exlimddv ) AIHUKZULUMZUUJKUNZLUOZUPZHJUQZURZIUSAIUSUTZUPB
        CDHIJKLNOPADOVAVBUOZUUQQVCRSABUKZPUKZCUKVEUNNVBUOCUUTUUSVEUNNVBUUTNVBVD
        VFBOVFPOUQVFZUUQTVCAIOKVDZVGZUUQUAVCAJUVBVGZUUQUBVCAIJKUNZNVBZVGZUUQUCV
        CAIKUNLUOZUUQUDVCAUUQJUSUTVHVIAIUSVJZUPUHUKZIUOZUUPUHUVIUVKUHVKAUHIVLVM
        AUVKUUPUVIAUVKUPZUIUKZIUVJVEZVDZUOVPZUVOKUVMVEZUNZUNLUOZUPZUUPUIJUVLBCD
        UIIJKLNOUVJPAUURUVKQVCRSAUVAUVKTVCAUVCUVKUAVCAUVDUVKUBVCAUVGUVKUCVCAUVH
        UVKUDVCAUVKVNVOUVMJUOZUVTUPUVLUWAUVPUVSVQZUUPUWAUVPUVSVRUVLUWBUPZUVOUJU
        KZULUMZUWDUVRUNZLUOZUPZUUPUJJUVQVDZUQZUWCFEGHUJUVOUWIUVRLVSMNOUWCDVAOAU
        URUVKUWBQVTWGZUWCUVOUVBUVQVDZOUVRVDZUWCUVOUVOUVQVDZUWLUWCUVPUWNUVOUTUVL
        UWAUVPUVSWAUVMUVOWBWCUWCUVOUVBUVQUWCIUVBUVNAUVCUVKUWBUAVTWDWEWFOKUVQWHZ
        WIUWCUWIUWLUWMUWCJUVBUVQAUVDUVKUWBUBVTWEUWOWIUWCIUWIUVRUNZNVBZUVNUWCIUV
        FUWQAUVGUVKUWBUCVTUWCUWPUVENUWCUWAUWPUVEUTUVLUWAUVPUVSWJZUWAUWPUWIUVQKU
        NZUNZUVEUVRUWSUWIKUVQWKWLUWAUWTUWIUVQUNZKUNUVEUWIUVQKWQUWAUXAJKJUVMWMWN
        WOWRWPWSWTWDUVLUWAUVPUVSXAUWCIMXBZULUMZJUXBULUMZXCZUVOMULUMZUWIMULUMZXC
        AUXEUVKUWBUGVTUWCUXCUXFUXDUXGUWCMXDUOZUVKUXCUXFXHAUXHUVKUWBUEVTZAUVKUWB
        XEUXCUXHUVKUPZUXFUXCUXJUPUXHUXCUVKVQUXFUXHUXCUVKXFIMUVJXGXIXJXKUWCUXHUW
        AUXDUXGXHUXIUWRUXDUXHUWAUPZUXGUXDUXKUPUXHUXDUWAVQUXGUXHUXDUWAXFJMUVMXGX
        IXJXKXLXMAEUKZMULUMFUKZMULUMXCUXLUXMGUKZUNNVBVGUXLUXNUNLUOVQUXLUUJULUMU
        UJUXNUNLUOUPHUXMUQURXHFOUXNVDUQZVFEUXOVFGXRUVKUWBUFVTXNUWCUWDUWJUOZUWHU
        PZUPZUWDUVQUNZUUOUOIUXSULUMZUXSKUNZLUOZUUPUXRUXSJVSUXRJOVSUWCOVSUOUXQUW
        KVCUXRJOKAUVDUVKUWBUXQUBXOXSXPUXRUWDUVQJUXRUWDJUVQUXRUWDUWIUWCUXPUWHXQY
        IZXSUXRUVMJUWAUVPUVSUVLUXQXTYAYBYCUXRUVOUVNUNZIUXSULUVKUYDIUTAUWBUXQIUV
        JWMYDUXRUWEUVNUVQULUMZUVOUVNYEUSUTZUWDUVQYEUSUTZUYDUXSULUMUWCUXPUWEUWGY
        FUYEUXRUYEUHUIUVJUVMVSVSYGYHYJUYFUXRUVNIYKYJUXRUWDUWIVGUYGUYCUWDJUVQYLW
        PUVOUWDUVNUVQYRYMYNUXRUYAUWFLUYAUWDUWSUNUWFUWDUVQKWQUWSUVRUWDUVQKWKWLYO
        UWCUXPUWEUWGYPYQUUNUXTUYBUPHUXSUUOUUJUXSUTZUUKUXTUUMUYBUUJUXSIULYSUYHUU
        LUYALUUJUXSKUUGUUAUUBUUCUUDYTUUEYTUUHUUIUUF $.
    $}

    $d q f F g h $.  $d f F g h l $.  $d q f g G h $.  $d f g G h l $.
    $d s f g h X y z k $.  $d s f g h ph y z k $.  $d s f g h y I i z k $.
    $d s f g h y z k N $.  $d f g h X k l $.  $d f g h ph k l $.
    $d f g h I i k l $.  $d f g h k l N $.  $d q f g h ph $.  $d q f g h I i $.
    $d q H $.
    mreexexd.9 $e |- ( ph -> ( F e. Fin \/ G e. Fin ) ) $.
    $( Exchange-type theorem.  In a Moore system whose closure operator has the
       exchange property, if ` F ` and ` G ` are disjoint from ` H ` ,
       ` ( F u. H ) ` is independent, ` F ` is contained in the closure of
       ` ( G u. H ) ` , and either ` F ` or ` G ` is finite, then there is a
       subset ` q ` of ` G ` equinumerous to ` F ` such that ` ( q u. H ) ` is
       independent.  This implies the case of Proposition 4.2.1 in
       [FaureFrolicher] p. 86 where either ` ( A \ B ) ` or ` ( B \ A ) ` is
       finite.  The theorem is proven by induction using ~ mreexexlem3d for the
       base case and ~ mreexexlem4d for the induction step.  (Contributed by
       David Moews, 1-May-2017.)  Remove dependencies on ~ ax-rep and
       ~ ax-ac2 .  (Revised by Brendan Leahy, 2-Jun-2021.) $)
    mreexexd $p |- ( ph -> E. q e. ~P G ( F ~~ q /\ ( q u. H ) e. I ) ) $=
      ( vg vf vh vi vl vk cvv cfn wcel ccrd cfv cif elfvexd wn wo cen wbr exmid
      cmre wi ficardid ensymd iftrue breqtrrd a1i wa orcanai syl iffalse adantl
      wceq ex orim12d mpi com cv cun wss w3a cpw wrex cdif wral ficardom ifclda
      wal csuc breq2 orbi12d 3anbi1d imbi1d 2ralbidv albidv imbi2d weq ad2antrr
      c0 csn simplrl elpwid simplrr simpr2 simpr3 simpr1 en0 sylib mreexexlem3d
      orbi12i ralrimivva alrimiv nfv nfa1 nf3an nfra1 nfal nfra2w nfan 3ad2ant1
      simpll2 simpll3 mreexexlem4d expr alrimi 3exp com12 a2d finds mreexexlemd
      ralrimi mpcom ) AUBUCUDUELEFGHUHEUIUJZEUKULZFUKULZUMZIJADUTJMUNQRSTAYLYLU
      OZUPEYOUQURZFYOUQURZUPYLUSAYLYQYPYRYLYQVAAYLEYMYOUQYLYMEEVBVCYLYMYNVDVEVF
      AYPYRAYPVGZFYNYOUQYSFUIUJZFYNUQURAYLYTUAVHZYTYNFFVBVCVIYPYOYNVLAYLYMYNVJV
      KVEVMVNVOYOVPUJAUCVQZYOUQURZUBVQZYOUQURZUPZUUBUUDUDVQZVRIULVSZUUBUUGVRHUJ
      ZVTZUUBUEVQZUQURUUKUUGVRHUJVGUEUUDWAWBZVAZUBJUUGWCZWAZWDUCUUOWDZUDWGZAYLY
      MYNVPYLYMVPUJAEWEVKYSYTYNVPUJUUAFWEVIWFAUUBUFVQZUQURZUUDUURUQURZUPZUUHUUI
      VTZUULVAZUBUUOWDUCUUOWDZUDWGZVAAUUBWRUQURZUUDWRUQURZUPZUUHUUIVTZUULVAZUBU
      UOWDUCUUOWDZUDWGZVAAUUBUGVQZUQURZUUDUVMUQURZUPZUUHUUIVTZUULVAZUBUUOWDZUCU
      UOWDZUDWGZVAAUUBUVMWHZUQURZUUDUWBUQURZUPZUUHUUIVTZUULVAZUBUUOWDZUCUUOWDZU
      DWGZVAAUUQVAUFUGYOUURWRVLZUVEUVLAUWKUVDUVKUDUWKUVCUVJUCUBUUOUUOUWKUVBUVIU
      ULUWKUVAUVHUUHUUIUWKUUSUVFUUTUVGUURWRUUBUQWIUURWRUUDUQWIWJWKWLWMWNWOUFUGW
      PZUVEUWAAUWLUVDUVTUDUWLUVCUVRUCUBUUOUUOUWLUVBUVQUULUWLUVAUVPUUHUUIUWLUUSU
      VNUUTUVOUURUVMUUBUQWIUURUVMUUDUQWIWJWKWLWMWNWOUURUWBVLZUVEUWJAUWMUVDUWIUD
      UWMUVCUWGUCUBUUOUUOUWMUVBUWFUULUWMUVAUWEUUHUUIUWMUUSUWCUUTUWDUURUWBUUBUQW
      IUURUWBUUDUQWIWJWKWLWMWNWOUURYOVLZUVEUUQAUWNUVDUUPUDUWNUVCUUMUCUBUUOUUOUW
      NUVBUUJUULUWNUVAUUFUUHUUIUWNUUSUUCUUTUUEUURYOUUBUQWIUURYOUUDUQWIWJWKWLWMW
      NWOAUVKUDAUVJUCUBUUOUUOAUUBUUOUJZUUDUUOUJZVGZVGZUVIUULUWRUVIVGZBCDUEUUBUU
      DUUGHIJKADJUTULUJZUWQUVIMWQNOABVQZKVQZCVQWSVRIULUJCUXBUXAWSVRIULUXBIULWCW
      DBJWDKJWAWDZUWQUVIPWQUWSUUBUUNAUWOUWPUVIWTXAUWSUUDUUNAUWOUWPUVIXBXAUWRUVH
      UUHUUIXCUWRUVHUUHUUIXDUWSUVHUUBWRVLZUUDWRVLZUPUWRUVHUUHUUIXEUVFUXDUVGUXEU
      UBXFUUDXFXIXGXHVMXJXKUVMVPUJZAUWAUWJAUXFUWAUWJVAAUXFUWAUWJAUXFUWAVTZUWIUD
      AUXFUWAUDAUDXLUXFUDXLUVTUDXMXNUXGUWHUCUUOAUXFUWAUCAUCXLUXFUCXLUVTUCUDUVSU
      CUUOXOXPXNUXGUWOUWHUXGUWOVGUWGUBUUOUXGUWOUBAUXFUWAUBAUBXLUXFUBXLUVTUBUDUV
      RUCUBUUOUUOXQXPXNUWOUBXLXRUXGUWOUWPUWGUXGUWQVGZUWFUULUXHUWFVGZBCDUCUBUDUE
      UUBUUDUUGHUVMIJKUXGUWTUWQUWFAUXFUWTUWAMXSWQNOUXGUXCUWQUWFAUXFUXCUWAPXSWQU
      XIUUBUUNUXGUWOUWPUWFWTXAUXIUUDUUNUXGUWOUWPUWFXBXAUXHUWEUUHUUIXCUXHUWEUUHU
      UIXDAUXFUWAUWQUWFXTAUXFUWAUWQUWFYAUXHUWEUUHUUIXEYBVMYCYJVMYJYDYEYFYGYHYKY
      I $.
  $}

  ${
    $d s X y z $.  $d s ph y z $.  $d s y I z $.  $d s y z N $.  $d S i $.
    $d T i $.  $d ph i $.  $d i I $.
    mreexdomd.1 $e |- ( ph -> A e. ( Moore ` X ) ) $.
    mreexdomd.2 $e |- N = ( mrCls ` A ) $.
    mreexdomd.3 $e |- I = ( mrInd ` A ) $.
    mreexdomd.4 $e |- ( ph -> A. s e. ~P X A. y e. X
                        A. z e. ( ( N ` ( s u. { y } ) ) \ ( N ` s ) )
                        y e. ( N ` ( s u. { z } ) ) ) $.
    mreexdomd.5 $e |- ( ph -> S C_ ( N ` T ) ) $.
    mreexdomd.6 $e |- ( ph -> T C_ X ) $.
    mreexdomd.7 $e |- ( ph -> ( S e. Fin \/ T e. Fin ) ) $.
    mreexdomd.8 $e |- ( ph -> S e. I ) $.
    $( In a Moore system whose closure operator has the exchange property, if
       ` S ` is independent and contained in the closure of ` T ` , and either
       ` S ` or ` T ` is finite, then ` T ` dominates ` S ` .  This is an
       immediate consequence of ~ mreexexd .  (Contributed by David Moews,
       1-May-2017.) $)
    mreexdomd $p |- ( ph -> S ~<_ T ) $=
      ( vi c0 cv cen wbr cun wcel wa cdom cpw cdif mrissd dif0 sseqtrrdi fveq2i
      cfv un0 eqeltrid mreexexd simprrl wss simprl elpwid wi cmre elfvexd ssexd
      cvv ssdomg syl adantr mpd endomtr syl2anc rexlimddv ) AESUAZUBUCZVNTUDGUE
      ZUFZEFUGUCZSFUHZABCDEFTGHIJSKLMNAEIITUIZADEGIMKRUJIUKZULAFIVTPWAULAEFHUNF
      TUDZHUNOWBFHFUOUMULAETUDEGEUORUPQUQAVNVSUEZVQUFZUFZVOVNFUGUCZVRAWCVOVPURW
      EVNFUSZWFWEVNFAWCVQUTVAAWGWFVBZWDAFVFUEWHAFIVFADVCIKVDPVEVNFVFVGVHVIVJEVN
      FVKVLVM $.
  $}

  ${
    $d s X y z $.  $d s ph y z $.  $d s y I z $.  $d s y z N $.
    mreexfidimd.1 $e |- ( ph -> A e. ( Moore ` X ) ) $.
    mreexfidimd.2 $e |- N = ( mrCls ` A ) $.
    mreexfidimd.3 $e |- I = ( mrInd ` A ) $.
    mreexfidimd.4 $e |- ( ph -> A. s e. ~P X A. y e. X
                          A. z e. ( ( N ` ( s u. { y } ) ) \ ( N ` s ) )
                          y e. ( N ` ( s u. { z } ) ) ) $.
    mreexfidimd.5 $e |- ( ph -> S e. I ) $.
    mreexfidimd.6 $e |- ( ph -> T e. I ) $.
    mreexfidimd.7 $e |- ( ph -> S e. Fin ) $.
    mreexfidimd.8 $e |- ( ph -> ( N ` S ) = ( N ` T ) ) $.
    $( In a Moore system whose closure operator has the exchange property, if
       two independent sets have equal closure and one is finite, then they are
       equinumerous.  Proven by using ~ mreexdomd twice.  This implies a
       special case of Theorem 4.2.2 in [FaureFrolicher] p. 87.  (Contributed
       by David Moews, 1-May-2017.) $)
    mreexfidimd $p |- ( ph -> S ~~ T ) $=
      ( cdom wbr cen cfv mrcssidd sseqtrd cfn wcel orcd mreexdomd sseqtrrd olcd
      mrissd sbth syl2anc ) AEFSTFESTEFUATABCDEFGHIJKLMNAEEHUBZFHUBZADEHIKLADEG
      IMKOUKZUCRUDADFGIMKPUKZAEUEUFZFUEUFZQUGOUHABCDFEGHIJKLMNAFUOUNADFHIKLUQUC
      RUIUPAURUSQUJPUHEFULUM $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Algebraic closure systems
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d C c f s $.  $d C t y $.  $d F f s t y z $.  $d S s y $.  $d X c f s x $.
    $d X t y $.
    $( A set is an algebraic closure system iff it is specified by some
       function of the finite subsets, such that a set is closed iff it does
       not expand under the operation.  (Contributed by Stefan O'Rear,
       2-Apr-2015.) $)
    isacs $p |- ( C e. ( ACS ` X ) <-> ( C e. ( Moore ` X ) /\
          E. f ( f : ~P X --> ~P X /\ A. s e. ~P X ( s e. C <->
                  U. ( f " ( ~P s i^i Fin ) ) C_ s ) ) ) ) $=
      ( vc vx cacs cfv wcel cvv cmre cpw cv wf wb wral wa wex elfvex crab fveq2
      cfn cin cima cuni wss adantr wceq feq23d raleqdv anbi12d exbidv rabeqbidv
      wel pweq df-acs fvex rabex fvmpt eleq2d eleq2 bibi1d ralbidv anbi2d elrab
      bitrdi pm5.21nii ) ACGHZIZCJIZACKHZIZCLZVMBMZNZDMZAIZVNVPLUBUCUDUEVPUFZOZ
      DVMPZQZBRZQZACGSVLVJWBACKSUGVJVIAVODEUNZVROZDVMPZQZBRZEVKTZIWCVJVHWIAFCFM
      ZLZWKVNNZWEDWKPZQZBRZEWJKHZTWIJGWJCUHZWOWHEWPVKWJCKUAWQWNWGBWQWLVOWMWFWQW
      KWKVMVMVNWJCUOZWRUIWQWEDWKVMWRUJUKULUMFBDEUPWHEVKCKUQURUSUTWHWBEAVKEMZAUH
      ZWGWABWTWFVTVOWTWEVSDVMWTWDVQVRWSAVPVAVBVCVDULVEVFVG $.

    $( Algebraic closure systems are closure systems.  (Contributed by Stefan
       O'Rear, 2-Apr-2015.) $)
    acsmre $p |- ( C e. ( ACS ` X ) -> C e. ( Moore ` X ) ) $=
      ( vf vs cacs cfv wcel cmre cpw cv wf cfn cin cima cuni wss wb wral wa wex
      isacs simplbi ) ABEFGABHFGBIZUCCJZKDJZAGUDUEILMNOUEPQDUCRSCTACBDUAUB $.

    isacs2.f $e |- F = ( mrCls ` C ) $.
    $( In the definition of an algebraic closure system, we may always take the
       operation being closed over as the Moore closure.  (Contributed by
       Stefan O'Rear, 2-Apr-2015.) $)
    isacs2 $p |- ( C e. ( ACS ` X ) <-> ( C e. ( Moore ` X ) /\
          A. s e. ~P X ( s e. C <->
              A. y e. ( ~P s i^i Fin ) ( F ` y ) C_ s ) ) ) $=
      ( vf vt vz cfv wcel cpw cv cfn cin wss wb wral wa sseq1d cacs cmre wf wex
      cima cuni isacs ciun wfun wceq ffun funiunfv iunss bitr3di bibi2d ralbidv
      syl pm5.32i simpll elinel1 elpwid adantl simplr mrcsscl syl3anc ralrimiva
      exbii ad4ant14 weq fveq2 simplll elpwi ad2antlr sstrd mrccl syl2anc eleq1
      wi pweq ineq1d raleqbidv bibi12d simprr ad2antrr mresspw ad3antrrr sseldd
      sseq2 rspcdva mpbid mrcssidd vex elpw sylibr elinel2 elind sstr2 ralimdva
      imp cbvralvw sylib mpbird impbida exlimdv mrcf fssd cmrc fvexi feq1 fveq1
      ex bitrdi anbi12d spcev sylan impbid bitrid bitri ) BDUAJKBDUBJKZDLZXTGMZ
      UCZHMZBKZYAYCLZNOZUEUFZYCPZQZHXTRZSZGUDZSXSEMZBKZAMZCJZYMPZAYMLZNOZRZQZEX
      TRZSBGDHUGXSYLUUBYLYBYDIMZYAJZYCPZIYFRZQZHXTRZSZGUDZXSUUBYKUUIGYBYJUUHYBY
      IUUGHXTYBYHUUFYDYBIYFUUDUHZYCPYHUUFYBUUKYGYCYBYAUIUUKYGUJXTXTYAUKIYFYAULU
      QTIYFUUDYCUMUNUOUPURVGXSUUJUUBXSUUIUUBGXSUUIUUBXSUUISZUUAEXTUULYMXTKZSZYN
      YTXSYNYTUUIUUMXSYNSZYQAYSUUOYOYSKZSXSYOYMPZYNYQXSYNUUPUSUUPUUQUUOUUPYOYMY
      OYRNUTVAZVBXSYNUUPVCBYOCYMDFVDVEVFVHUUNYTSZYNUUDYMPZIYSRZUUSYOYAJZYMPZAYS
      RZUVAUUNYTUVDUUNYQUVCAYSUUNUUPSZUVBYPPZYQUVCVRUVEUUDYPPZUVFIYPLZNOZYOIAVI
      ZUUDUVBYPUUCYOYAVJTUVEYPBKZUVGIUVIRZUVEXSYODPUVKXSUUIUUMUUPVKZUVEYOYMDUUP
      UUQUUNUURVBUUMYMDPUULUUPYMDVLVMVNZBYOCDFVOVPZUVEUUGUVKUVLQHXTYPYCYPUJZYDU
      VKUUFUVLYCYPBVQUVPUUEUVGIYFUVIUVPYEUVHNYCYPVSVTYCYPUUDWHWAWBUULUUHUUMUUPX
      SYBUUHWCZWDUVEBXTYPXSBXTPUUIUUMUUPBDWEZWFUVOWGWIWJUVEUVHNYOUVEYOYPPYOUVHK
      UVEBYOCDUVMFUVNWKYOYPAWLWMWNUUPYONKUUNYOYRNWOVBWPWIUVBYPYMWQUQWRWSUVCUUTA
      IYSAIVIUVBUUDYMYOUUCYAVJTWTXAUUSUUGYNUVAQHXTYMHEVIZYDYNUUFUVAYCYMBVQZUVSU
      UEUUTIYFYSUVSYEYRNYCYMVSVTZYCYMUUDWHWAWBUULUUHUUMYTUVQWDUULUUMYTVCWIXBXCV
      FXKXDXSUUBUUJXSXTXTCUCZUUBUUJXSXTBXTCBCDFXEUVRXFUUIUWBUUBSGCCBXGFXHYACUJZ
      YBUWBUUHUUBXTXTYACXIUWCUUHYDYPYCPZAYFRZQZHXTRUUBUWCUUGUWFHXTUWCUUFUWEYDUW
      CUUFUUCCJZYCPZIYFRUWEUWCUUEUWHIYFUWCUUDUWGYCUUCYACXJTUPUWHUWDIAYFUVJUWGYP
      YCUUCYOCVJTWTXLUOUPUWFUUAHEXTUVSYDYNUWEYTUVTUVSUWDYQAYFYSUWAYCYMYPWHWAWBW
      TXLXMXNXOXKXPXQURXR $.

    $( A set is closed in an algebraic closure system iff it contains all
       closures of finite subsets.  (Contributed by Stefan O'Rear,
       2-Apr-2015.) $)
    acsfiel $p |- ( C e. ( ACS ` X ) -> ( S e. C <->
          ( S C_ X /\ A. y e. ( ~P S i^i Fin ) ( F ` y ) C_ S ) ) ) $=
      ( vs cacs cfv wcel wss wa cv cpw cfn cin wral cmre acsmre wb ex wceq pweq
      mress sylan pm4.71rd eleq1 ineq1d raleqbidv bibi12d isacs2 simprbi adantr
      sseq2 cdm elfvdm elpw2g syl biimpar rspcdva pm5.32da bitrd ) BEHIJZCBJZCE
      KZVDLVEAMDIZCKZACNZOPZQZLVCVDVEVCVDVEVCBERIJZVDVEBESBCEUDUEUAUFVCVEVDVJVC
      VELGMZBJZVFVLKZAVLNZOPZQZTZVDVJTGENZCVLCUBZVMVDVQVJVLCBUGVTVNVGAVPVIVTVOV
      HOVLCUCUHVLCVFUNUIUJVCVRGVSQZVEVCVKWAABDEGFUKULUMVCCVSJZVEVCEHUOZJWBVETBE
      HUPCEWCUQURUSUTVAVB $.

    $( A set is closed in an algebraic closure system iff it contains all
       closures of finite subsets.  (Contributed by Stefan O'Rear,
       3-Apr-2015.) $)
    acsfiel2 $p |- ( ( C e. ( ACS ` X ) /\ S C_ X ) -> ( S e. C <->
          A. y e. ( ~P S i^i Fin ) ( F ` y ) C_ S ) ) $=
      ( cacs cfv wcel wss cv cpw cfn cin wral acsfiel baibd ) BEGHICBICEJAKDHCJ
      ACLMNOABCDEFPQ $.
  $}

  ${
    acsmred.1 $e |- ( ph -> A e. ( ACS ` X ) ) $.
    $( An algebraic closure system is also a Moore system.  Deduction form of
       ~ acsmre .  (Contributed by David Moews, 1-May-2017.) $)
    acsmred $p |- ( ph -> A e. ( Moore ` X ) ) $=
      ( cacs cfv wcel cmre acsmre syl ) ABCEFGBCHFGDBCIJ $.
  $}

  ${
    $d F a s t $.  $d F f $.  $d V a t $.  $d X a s t $.  $d X f $.
    $d f s t $.
    $( A closure system determined by a function is a closure system and
       algebraic.  (Contributed by Stefan O'Rear, 3-Apr-2015.) $)
    isacs1i $p |- ( ( X e. V /\ F : ~P X --> ~P X ) ->
        { s e. ~P X | U. ( F " ( ~P s i^i Fin ) ) C_ s } e. ( ACS ` X ) ) $=
      ( vf vt va wcel cpw wa cv cfn cin cima cuni wss wral pweq unieqd cvv crab
      wf cmre cfv wb wex cacs ssrab2 a1i cint wceq ineq1d imaeq2d sseq12d inss1
      id elpw2g mpbiri ad2antrr crn imassrn adantl sstrid unissd unipw sseqtrdi
      frn adantr wel inss2 intss1 sspwd ssrind imass2 syl ssel2 simprbi adantll
      elrab sstrd ralrimiva ssint sylibr ssind elrabd ismred2 fssxp pwexg xpexd
      weq cxp ssexg syl2anr simpr elrab3 rgen feq1 imaeq1 sseq1d bibi2d ralbidv
      jctir anbi12d spcedv isacs sylanbrc ) CBHZCIZXHAUBZJZADKZIZLMZNZOZXKPZDXH
      UAZCUCUDHXHXHEKZUBZFKZXQHZXRXTIZLMZNZOZXTPZUEZFXHQZJZEUFXQCUGUDHXJXQCFXQX
      HPXJXPDXHUHUIXJXTXQPZJZXPACXTUJZMZIZLMZNZOZYMPDYMXHXKYMUKZXOYQXKYMYRXNYPY
      RXMYOAYRXLYNLXKYMRULUMSYRUPUNXGYMXHHZXIYJXGYSYMCPCYLUOYMCBUQURUSYKYQCYLXJ
      YQCPYJXJYQXHOCXJYPXHXJYPAUTZXHAYOVAXIYTXHPXGXHXHAVGVBVCVDCVEVFVHYKYQGKZPZ
      GXTQYQYLPYKUUBGXTYKGFVIZJZYQAUUAIZLMZNZOZUUAUUDYPUUGUUDYOUUFPYPUUGPUUDYNU
      UELUUDYMUUAUUCYMUUAPYKUUCYMYLUUACYLVJUUAXTVKVCVBVLVMYOUUFAVNVOVDYJUUCUUHU
      UAPZXJYJUUCJUUAXQHZUUIXTXQUUAVPUUJUUAXHHUUIXPUUIDUUAXHDGWJZXOUUHXKUUAUUKX
      NUUGUUKXMUUFAUUKXLUUELXKUUARULUMSUUKUPUNVSVQVOVRVTWAGYQXTWBWCWDWEWFXJYIXI
      YAAYCNZOZXTPZUEZFXHQZJETAXIAXHXHWKZPUUQTHATHXGXHXHAWGXGXHXHTTCBWHZUURWIAU
      UQTWLWMXJXIUUPXGXIWNUUOFXHXPUUNDXTXHDFWJZXOUUMXKXTUUSXNUULUUSXMYCAUUSXLYB
      LXKXTRULUMSUUSUPUNWOWPXBXRAUKZXSXIYHUUPXHXHXRAWQUUTYGUUOFXHUUTYFUUNYAUUTY
      EUUMXTUUTYDUULXRAYCWRSWSWTXAXCXDXQECFXEXF $.
  $}

  ${
    $d K a b c $.  $d T a b c $.  $d V a b c $.  $d X a b c x $.  $d a d e $.
    $d a f $.  $d b d e $.  $d b f $.  $d c d e $.  $d c f $.  $d d f x $.
    $d e x $.
    $( Algebraicity is a composable property; combining several algebraic
       closure properties gives another.  (Contributed by Stefan O'Rear,
       3-Apr-2015.) $)
    mreacs $p |- ( X e. V -> ( ACS ` X ) e. ( Moore ` ~P X ) ) $=
      ( vx va vf vb vc vd ve cv cfv cpw cmre wcel wss wb wral wa cvv iunss cacs
      wceq fveq2 pweq fveq2d eleq12d wtru acsmre mresspw syl elpwd a1i cint cin
      ssriv cfn cima cuni wex vex mremre mp1i sstr mpan2 mrerintcl syl2anc cmrc
      wf ciun cmpt cxp ssel2 acsmred eqid mrcssvd ralrimiva adantr sylibr elpw2
      wel fmpttd fssxp vpwex xpex ssexg sylancl adantlr elpwi ad2antlr acsfiel2
      ralbidva ralbii ralcom bitri bitr4di elrint2 adantl funmpt funiunfv ax-mp
      wfun sseq1i weq iuneq2d inss1 sspwd sstrid sselda ad2antrr fvmptd3 sseq1d
      bitrid bitr3id 3bitr4d jca feq1 imaeq1 unieqd bibi2d ralbidv spcedv isacs
      anbi12d sylanbrc ismred2 mptru vtoclg ) CJZUAKZYHLZMKZNZBUAKZBLZMKZNCBAYH
      BUBZYIYMYKYOYHBUAUCYPYJYNMYHBUDUEUFYLUGYIYJDYIYJLZOUGDYIYQDJZYINZYRYJYHMK
      ZYRYHUHZYSYRYTNYRYJOUUAYRYHUIUJUKUOULYRYIOZYJYRUMUNZYINZUGUUBUUCYTNZYJYJE
      JZVHZFJZUUCNZUUFUUHLZUPUNZUQZURZUUHOZPZFYJQZRZEUSUUDUUBYTYKNZYRYTOZUUEYHS
      NZUURUUBCUTZSYHVAVBUUBYIYTOUUSDYIYTUUAUOYRYIYTVCVDYTYRYJVEVFUUBUUQYJYJGYJ
      HYRGJZHJZVGKZKZVIZVJZVHZUUIUVGUUKUQZURZUUHOZPZFYJQZRESUVGUUBUVGYJYJVKZOZU
      VNSNUVGSNUUBUVHUVOUUBGYJUVFYJUUBUVBYJNZRZUVFYHOZUVFYJNUVQUVEYHOZHYRQZUVRU
      UBUVTUVPUUBUVSHYRUUBHDVTZRZUVCUVBUVDYHUWBUVCYHYRYIUVCVLZVMZUVDVNZVOVPVQHY
      RUVEYHTVRUVFYHUVAVSVRWAZYJYJUVGWBUJYJYJCWCZUWGWDUVGUVNSWEWFUUBUVHUVMUWFUU
      BUVLFYJUUBUUHYJNZRZFHVTZHYRQZHYRIJZUVDKZVIZUUHOZIUUKQZUUIUVKUWIUWKUWMUUHO
      ZIUUKQZHYRQZUWPUWIUWJUWRHYRUWIUWARUVCYINZUUHYHOZUWJUWRPUUBUWAUWTUWHUWCWGU
      WHUXAUUBUWAUUHYHWHZWIIUVCUUHUVDYHUWEWJVFWKUWPUWQHYRQZIUUKQUWSUWOUXCIUUKHY
      RUWMUUHTWLUWQIHUUKYRWMWNWOUWHUUIUWKPUUBHYJYRUUHWPWQUVKIUUKUWLUVGKZVIZUUHO
      ZUWIUWPUXEUVJUUHUVGXAUXEUVJUBGYJUVFWRIUUKUVGWSWTXBUXFUXDUUHOZIUUKQUWIUWPI
      UUKUXDUUHTUWIUXGUWOIUUKUWIUWLUUKNZRZUXDUWNUUHUXIGUWLUVFUWNYJUVGSUVGVNGIXC
      HYRUVEUWMUVBUWLUVDUCXDUWIUUKYJUWLUWIUUKUUJYJUUJUPXEUWHUUJYJOUUBUWHUUHYHUX
      BXFWQXGXHUXIUWNYHOZUUTUWNSNUXIUWMYHOZHYRQZUXJUUBUXLUWHUXHUUBUXKHYRUWBUVCU
      WLUVDYHUWDUWEVOVPXIHYRUWMYHTVRUVAUWNYHSWEWFXJXKWKXLXMXNVPXOUUFUVGUBZUUGUV
      HUUPUVMYJYJUUFUVGXPUXMUUOUVLFYJUXMUUNUVKUUIUXMUUMUVJUUHUXMUULUVIUUFUVGUUK
      XQXRXKXSXTYCYAUUCEYHFYBYDWQYEYFYG $.

    $( Algebraicity of a conditional point closure condition.  (Contributed by
       Stefan O'Rear, 3-Apr-2015.) $)
    acsfn $p |- ( ( ( X e. V /\ K e. X ) /\ ( T C_ X /\ T e. Fin ) ) ->
        { a e. ~P X | ( T C_ a -> K e. a ) } e. ( ACS ` X ) ) $=
      ( vb vc wcel wa wss cfn cv wi cpw wceq c0 wral syl wb adantl crab csn cif
      cmpt cin cima cuni cacs cfv ciun wfun funmpt funiunfv mp1i elinel1 elpwid
      elpwi sylan9ssr velpw sylibr adantll weq eqeq1 ifbid eqid snex ifex fvmpt
      0ex iuneq2dv eqtr3d sseq1d iunss sseq1 bibi1d snssg adantr bitr3d 0ss a1i
      biimt wn pm2.21 ifbothda ralbidv ad3antlr bitrid inss1 sspwd sstrid ralss
      2thd bi2.04 ralbii elpwg biimparc ad2antlr eleq1 imbi1d ceqsralv biantrud
      simplrr elin bitr4di vex elpw2 bitr3di 3bitrd 3bitrrd rabbidva wf snelpwi
      simpll 0elpw ifcl sylancl fmpttd isacs1i syl2anc eqeltrd ) DCHZBDHZIZADJZ
      AKHZIZIZAELZJZBYHHZMZEDNZUAFYLFLZAOZBUBZPUCZUDZYHNZKUEZUFUGZYHJZEYLUAZDUH
      UIZYGYKUUAEYLYGYHYLHZIZUUAGYSGLZAOZYOPUCZUJZYHJZUUGYJMZGYSQZYKUUEYTUUIYHU
      UEGYSUUFYQUIZUJZYTUUIYQUKUUNYTOUUEFYLYPULGYSYQUMUNUUEGYSUUMUUHUUEUUFYSHZI
      UUFYLHZUUMUUHOUUDUUOUUPYGUUDUUOIUUFDJUUPUUOUUDUUFYHDUUOUUFYHUUFYRKUOUPYHD
      UQZURGDUSUTVAFUUFYPUUHYLYQFGVBYNUUGYOPYMUUFAVCVDYQVEUUGYOPBVFVIVGVHRVJVKV
      LUUJUUHYHJZGYSQZUUEUULGYSUUHYHVMYBUUSUULSYAYFUUDYBUURUUKGYSUUGYOYHJZUUKSP
      YHJZUUKSZUURUUKSYBYOPYOUUHOUUTUURUUKYOUUHYHVNVOPUUHOUVAUURUUKPUUHYHVNVOYB
      UUGIYJUUTUUKYBYJUUTSUUGBYHDVPVQUUGYJUUKSYBUUGYJWATVRUUGWBZUVBYBUVCUVAUUKU
      VAUVCYHVSVTUUGYJWCWLTWDWEWFWGUUEUULUUOUUKMZGYLQZAYSHZYJMZYKUUEYSYLJZUULUV
      ESUUDUVHYGUUDYSYRYLYRKWHUUDYHDUUQWIWJTUUKGYSYLWKRUVEUUGUUOYJMZMZGYLQZUUEU
      VGUVDUVJGYLUUOUUGYJWMWNUUEAYLHZUVKUVGSYFUVLYCUUDYEUVLYDADKWOWPWQUVIUVGGAY
      LUUGUUOUVFYJUUFAYSWRWSWTRWGUUEUVFYIYJUUEAYRHZUVFYIUUEUVMUVMYEIUVFUUEYEUVM
      YCYDYEUUDXBXAAYRKXCXDAYHEXEXFXGWSXHXIXJYGYAYLYLYQXKUUBUUCHYAYBYFXMYGFYLYP
      YLYGYPYLHZYMYLHYGYOYLHZPYLHUVNYBUVOYAYFBDXLWQDXNYNYOPYLXOXPVQXQYQCDEXRXSX
      T $.

    $( Algebraicity of a point closure condition.  (Contributed by Stefan
       O'Rear, 3-Apr-2015.) $)
    acsfn0 $p |- ( ( X e. V /\ K e. X ) ->
        { a e. ~P X | K e. a } e. ( ACS ` X ) ) $=
      ( wcel wa cv cpw crab c0 wss wi cacs cfv 0ss a1bi rabbii cfn 0fi acsfn
      mpanr12 eqeltrid ) CBEACEFZADGZEZDCHZIJUDKZUELZDUFIZCMNZUEUHDUFUGUEUDOPQU
      CJCKJREUIUJECOSJABCDTUAUB $.

    $d E a $.
    $( Algebraicity of a one-argument closure condition.  (Contributed by
       Stefan O'Rear, 3-Apr-2015.) $)
    acsfn1 $p |- ( ( X e. V /\ A. b e. X E e. X ) ->
        { a e. ~P X | A. b e. a E e. a } e. ( ACS ` X ) ) $=
      ( wcel wral wa cv cpw crab csn wss wi ciin cin cacs cfv wel wb elpwi snss
      ralss syl vex imbi1i ralbii bitrdi rabbiia riinrab eqtr4i cmre mreacs cfn
      simpll simpr snssi ad2antlr snfi a1i acsfn syl22anc ex ralimdva mreriincl
      imp syl2an2r eqeltrid ) CBFZACFZECGZHADIZFZEVLGZDCJZKZVOECEIZLZVLMZVMNZDV
      OKZOPZCQRZVPVTECGZDVOKWBVNWDDVOVLVOFZVNEDSZVMNZECGZWDWEVLCMVNWHTVLCUAVMEV
      LCUCUDWGVTECWFVSVMVQVLEUEUBUFUGUHUIVTEDVOCUJUKVIWCVOULRFVKWAWCFZECGZWBWCF
      BCUMVIVKWJVIVJWIECVIVQCFZHZVJWIWLVJHZVIVJVRCMZVRUNFZWIVIWKVJUOWLVJUPWKWNV
      IVJVQCUQURWOWMVQUSUTVRABCDVAVBVCVDVFEWCWACVOVEVGVH $.

    $( Algebraicity of a one-argument closure condition with additional
       constant.  (Contributed by Stefan O'Rear, 3-Apr-2015.) $)
    acsfn1c $p |- ( ( X e. V /\ A. b e. K A. c e. X E e. X ) ->
        { a e. ~P X | A. b e. K A. c e. a E e. a } e. ( ACS ` X ) ) $=
      ( wcel wral wa cv cpw crab ciin cin cacs cfv riinrab cmre mreacs syl2an2r
      acsfn1 ex ralimdv imp mreriincl eqeltrrid ) DCHZADHGDIZFBIZJAEKZHGUKIZFBI
      EDLZMUMFBULEUMMZNOZDPQZULFEUMBRUHUPUMSQHUJUNUPHZFBIZUOUPHCDTUHUJURUHUIUQF
      BUHUIUQACDEGUBUCUDUEFUPUNBUMUFUAUG $.

    $( Algebraicity of a two-argument closure condition.  (Contributed by
       Stefan O'Rear, 3-Apr-2015.) $)
    acsfn2 $p |- ( ( X e. V /\ A. b e. X A. c e. X E e. X ) ->
        { a e. ~P X | A. b e. a A. c e. a E e. a } e. ( ACS ` X ) ) $=
      ( wcel wral wa cv crab wss wi ciin cin cfv wel ralss vex riinrab cpw cacs
      cpr wb elpwi r19.21v impexp prss imbi1i bitr3i ralbii 3bitr3g ralbidv syl
      bitrd rabbiia eqtr4i mreacs ad2antrr simpll simprr prssi ancoms ad2ant2lr
      cmre cfn prfi a1i acsfn syl22anc ralimdva imp mreriincl syl2anc eqeltrrid
      expr ex syl2an2r eqeltrid ) CBGZACGZFCHZECHZIADJZGZFWDHZEWDHZDCUAZKZWHECF
      JZEJZUCZWDLZWEMZFCHZDWHKZNOZCUBPZWIWOECHZDWHKWQWGWSDWHWDWHGWDCLZWGWSUDWDC
      UEWTWGEDQZWFMZECHWSWFEWDCRWTXBWOECWTXAWEMZFWDHFDQZXCMZFCHXBWOXCFWDCRXAWEF
      WDUFXEWNFCXEXDXAIZWEMWNXDXAWEUGXFWMWEWJWKWDFSESUHUIUJUKULUMUOUNUPWOEDWHCT
      UQVTWRWHVEPGZWCWPWRGZECHZWQWRGBCURZVTWCXIVTWBXHECVTWKCGZIZWBXHXLWBIZWPWHF
      CWNDWHKZNOZWRWNFDWHCTXMXGXNWRGZFCHZXOWRGVTXGXKWBXJUSXLWBXQXLWAXPFCXLWJCGZ
      WAXPXLXRWAIZIZVTWAWLCLZWLVFGZXPVTXKXSUTXLXRWAVAXKXRYAVTWAXRXKYAWJWKCVBVCV
      DYBXTWJWKVGVHWLABCDVIVJVPVKVLFWRXNCWHVMVNVOVQVKVLEWRWPCWHVMVRVS $.
  $}

