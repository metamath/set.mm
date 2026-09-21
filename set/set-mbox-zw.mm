$[ set-main.mm $]
$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Mathbox for Zhi Wang
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Propositional calculus
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    imbi12d2.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    ${
      imbi12d2.2 $e |- ( ph -> ( ps -> ( th <-> ta ) ) ) $.
      $( Distribution of implication over biconditional with replacement
         (deduction form).  (Contributed by Zhi Wang, 30-Aug-2024.) $)
      imbi12d2 $p |- ( ph -> ( ( ps -> th ) <-> ( ch -> ta ) ) ) $=
        ( wi pm5.74d imbi1d bitrd ) ABDHBEHCEHABDEGIABCEFJK $.
    $}

    ${
      imbi12d2a.2 $e |- ( ( ph /\ ps ) -> ( th <-> ta ) ) $.
      $( Variant of ~ imbi12d2 .  (Contributed by Zhi Wang, 30-Aug-2024.) $)
      imbi12d2a $p |- ( ph -> ( ( ps -> th ) <-> ( ch -> ta ) ) ) $=
        ( wb ex imbi12d2 ) ABCDEFABDEHGIJ $.
    $}

    ${
      imbi12d3.2 $e |- ( ph -> ( ( ps /\ ch ) -> ( th <-> ta ) ) ) $.
      $( Variant of ~ imbi12d2 .  (Contributed by Zhi Wang, 30-Aug-2024.) $)
      imbi12d3 $p |- ( ph -> ( ( ps -> th ) <-> ( ch -> ta ) ) ) $=
        ( wa wb pm4.71da sylbid imbi12d2 ) ABCDEFABBCHDEIABCFJGKL $.
    $}
  $}

  ${
    pm5.32rda.1 $e |- ( ( ph /\ ps ) -> ( ch <-> th ) ) $.
    $( Distribution of implication over biconditional (deduction form).
       Variant of ~ pm5.32da .  (Contributed by Zhi Wang, 30-Aug-2024.) $)
    pm5.32rda $p |- ( ph -> ( ( ch /\ ps ) <-> ( th /\ ps ) ) ) $=
      ( wa pm5.32da ancom 3bitr3g ) ABCFBDFCBFDBFABCDEGBCHBDHI $.
  $}

  ${
    pm5.32dar.1 $e |- ( ph -> ( ( ps /\ ch ) <-> ( ps /\ th ) ) ) $.
    $( Reverse distribution of implication over biconditional (deduction form).
       (Contributed by Zhi Wang, 6-Sep-2024.) $)
    pm5.32dar $p |- ( ( ph /\ ps ) -> ( ch <-> th ) ) $=
      ( wb wa wi pm5.32 sylibr imp ) ABCDFZABCGBDGFBLHEBCDIJK $.
  $}

  ${
    exp12bd.1 $e |- ( ph -> ( ( ( ps /\ ch ) -> th )
                              <-> ( ( ta /\ et ) -> ze ) ) ) $.
    $( The import-export theorem ( ~ impexp ) for biconditionals (deduction
       form).  (Contributed by Zhi Wang, 3-Sep-2024.) $)
    exp12bd $p |- ( ph -> ( ( ps -> ( ch -> th ) )
                            <-> ( ta -> ( et -> ze ) ) ) ) $=
      ( wa wi impexp 3bitr3g ) ABCIDJEFIGJBCDJJEFGJJHBCDKEFGKL $.
  $}

  ${
    mpbiran3d.1 $e |- ( ph -> ( ps <-> ( ch /\ th ) ) ) $.
    ${
      mpbiran3d.2 $e |- ( ( ph /\ ch ) -> th ) $.
      $( Equivalence with a conjunction one of whose conjuncts is a consequence
         of the other.  Deduction form.  (Contributed by Zhi Wang,
         24-Sep-2024.) $)
      mpbiran3d $p |- ( ph -> ( ps <-> ch ) ) $=
        ( simprbda ex wa ancld sylibrd impbid ) ABCABCABCDEGHACCDIBACDACDFHJEKL
        $.
    $}

    ${
      mpbiran4d.2 $e |- ( ( ph /\ th ) -> ch ) $.
      $( Equivalence with a conjunction one of whose conjuncts is a consequence
         of the other.  Deduction form.  (Contributed by Zhi Wang,
         27-Sep-2024.) $)
      mpbiran4d $p |- ( ph -> ( ps <-> th ) ) $=
        ( biancomd mpbiran3d ) ABDCABDCEGFH $.
    $}
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Predicate calculus with equality
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Axiom scheme ax-5 (Distinctness)
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d x y $.
    dtrucor3.1 $e |- -. A. x x = y $.
    dtrucor3.2 $e |- ( x = y -> A. x x = y ) $.
    $( An example of how ~ ax-5 without a distinct variable condition causes
       paradox in models of at least two objects.  The hypothesis "dtrucor3.1"
       is provable from ~ dtru in the ZF set theory. ~ axc16nf and ~ euae
       demonstrate that the violation of ~ dtru leads to a model with only one
       object assuming its existence ( ~ ax-6 ).  The conclusion is also
       provable in the empty model ( see ~ emptyal ).  See also ~ nf5 and
       ~ nf5i for the relation between unconditional ~ ax-5 and being not free.
       (Contributed by Zhi Wang, 23-Sep-2024.) $)
    dtrucor3 $p |- A. x x = y $=
      ( weq wex wal ax6ev mto nex pm2.24ii ) ABEZAFLAGZABHLALMCDIJK $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  ZF Set Theory - start with the Axiom of Extensionality
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Restricted quantification
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d ph x $.
    ralbidb.1 $e |- ( ph -> ( x e. A <-> ( x e. B /\ ps ) ) ) $.
    ${
      ralbidb.2 $e |- ( ( ph /\ x e. A ) -> ( ch <-> th ) ) $.
      $( Formula-building rule for restricted universal quantifier and
         additional condition (deduction form).  See ~ ralbidc for a more
         generalized form.  (Contributed by Zhi Wang, 6-Sep-2024.) $)
      ralbidb $p  |- ( ph -> ( A. x e. A ch <-> A. x e. B ( ps -> th ) ) ) $=
        ( wi cv wcel wa imbi12d2a impexp bitrdi ralbidv2 ) ACBDJZEFGAEKZFLZCJSG
        LZBMZDJUARJATUBCDHINUABDOPQ $.
    $}

    ralbidc.2 $e |- ( ph -> ( ( x e. A /\ ( x e. B /\ ps ) )
                           -> ( ch <-> th ) ) ) $.
    $( Formula-building rule for restricted universal quantifier and additional
       condition (deduction form).  A variant of ~ ralbidb .  (Contributed by
       Zhi Wang, 30-Aug-2024.) $)
    ralbidc $p |- ( ph -> ( A. x e. A ch <-> A. x e. B ( ps -> th ) ) ) $=
      ( wi cv wcel wa imbi12d3 impexp bitrdi ralbidv2 ) ACBDJZEFGAEKZFLZCJSGLZB
      MZDJUARJATUBCDHINUABDOPQ $.
  $}

  ${
    $d ch x $.
    r19.41dv.1 $e |- ( ph -> E. x e. A ps ) $.
    $( A complex deduction form of ~ r19.41v .  (Contributed by Zhi Wang,
       6-Sep-2024.) $)
    r19.41dv $p |- ( ( ph /\ ch ) -> E. x e. A ( ps /\ ch ) ) $=
      ( wa wrex anim1i r19.41v sylibr ) ACGBDEHZCGBCGDEHALCFIBCDEJK $.
  $}

  $( Two ways of expressing "at most one" element.  (Contributed by Zhi Wang,
     19-Sep-2024.)  (Proof shortened by BJ, 23-Sep-2024.) $)
  rmotru $p |- ( E* x x e. A <-> E* x e. A T. ) $=
    ( cv wcel wmo wtru wa wrmo tru biantru mobii df-rmo bitr4i ) ACBDZAENFGZAEF
    ABHNOAFNIJKFABLM $.

  $( Two ways of expressing "exactly one" element.  (Contributed by Zhi Wang,
     23-Sep-2024.) $)
  reutru $p |- ( E! x x e. A <-> E! x e. A T. ) $=
    ( cv wcel weu wtru wa wreu tru biantru eubii df-reu bitr4i ) ACBDZAENFGZAEF
    ABHNOAFNIJKFABLM $.

  $( Alternate proof of ~ reutru .  (Contributed by Zhi Wang, 23-Sep-2024.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  reutruALT $p |- ( E! x x e. A <-> E! x e. A T. ) $=
    ( cv wcel wex wmo wa wtru wrex wrmo weu rextru rmotru anbi12i df-eu 3bitr4i
    wreu reu5 ) ACBDZAEZSAFZGHABIZHABJZGSAKHABQTUBUAUCABLABMNSAOHABRP $.

  ${
    $d A x $.  $d B x $.  $d ph x $.
    reueqbidva.1 $e |- ( ph -> A = B ) $.
    reueqbidva.2 $e |- ( ( ph /\ x e. A ) -> ( ps <-> ch ) ) $.
    $( Formula-building rule for restricted existential uniqueness quantifier.
       Deduction form.  General version of ~ reueqbidv .  (Contributed by Zhi
       Wang, 20-Nov-2025.) $)
    reueqbidva $p |- ( ph -> ( E! x e. A ps <-> E! x e. B ch ) ) $=
      ( wreu reubidva reueqdv bitrd ) ABDEICDEICDFIABCDEHJACDEFGKL $.
    $( $j usage 'reueqbidva' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  The universal class
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d x y ph $.  $d y ps $.  $d x ch $.  $d x A $.  $d x y B $.  $d x y C $.
    reuxfr1dd.1 $e |- ( ( ph /\ y e. C ) -> A e. B ) $.
    reuxfr1dd.2 $e |- ( ( ph /\ x e. B ) -> E! y e. C x = A ) $.
    reuxfr1dd.3 $e |- ( ( ph /\ ( y e. C /\ x = A ) ) -> ( ps <-> ch ) ) $.
    $( Transfer existential uniqueness from a variable ` x ` to another
       variable ` y ` contained in expression ` A ` .  Simplifies ~ reuxfr1d .
       (Contributed by Zhi Wang, 20-Sep-2025.) $)
    reuxfr1dd $p |- ( ph -> ( E! x e. B ps <-> E! y e. C ch ) ) $=
      ( wreu cv wceq wa wrex wcel syl anass bitrd biantrurd wb r19.41v pm5.32da
      reurex 3bitr3g rexbidv2 bitr3id adantr reubidva wrmo reurmo reuxfrd ) ABD
      GLDMZFNZCOZEHPZDGLCEHLABUQDGAUNGQZOZBUOEHPZBOZUQUSUTBUSUOEHLZUTJUOEHUERUA
      AVAUQUBURVAUOBOZEHPAUQUOBEHUCAVCUPEHHAEMHQZUOOZBOVECOVDVCOVDUPOAVEBCKUDVD
      UOBSVDUOCSUFUGUHUITUJACDEFGHIUSVBUOEHUKJUOEHULRUMT $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  The empty set
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    ssdisjd.1 $e |- ( ph -> A C_ B ) $.
    ${
      ssdisjd.2 $e |- ( ph -> ( B i^i C ) = (/) ) $.
      $( Subset preserves disjointness.  Deduction form of ~ ssdisj .
         (Contributed by Zhi Wang, 7-Sep-2024.) $)
      ssdisjd $p |- ( ph -> ( A i^i C ) = (/) ) $=
        ( cin wss c0 wceq ssrind sseq0 syl2anc ) ABDGZCDGZHOIJNIJABCDEKFNOLM $.
    $}

    ${
      ssdisjdr.2 $e |- ( ph -> ( C i^i B ) = (/) ) $.
      $( Subset preserves disjointness.  Deduction form of ~ ssdisj .
         Alternatively this could be proved with ~ ineqcom in tandem with
         ~ ssdisjd .  (Contributed by Zhi Wang, 7-Sep-2024.) $)
      ssdisjdr $p |- ( ph -> ( C i^i A ) = (/) ) $=
        ( cin wss c0 wceq sslin syl sseq0 syl2anc ) ADBGZDCGZHZPIJOIJABCHQEBCDK
        LFOPMN $.

$(
      @( Subset preserves disjointness.  Deduction form of ~ ssdisj .
         (Contributed by Zhi Wang, 7-Sep-2024.)
         (Proof modification is discouraged.)  (New usage is discouraged.) @)
      ssdisjdrALT @p |- ( ph -> ( C i^i A ) = (/) ) @=
        ( cin c0 wceq ineqcom sylib ssdisjd sylibr ) ABDGHIDBGHIABCDEADCGHICDGH
        IFDCHJKLDBHJM @.
$)
    $}
  $}

  $( Relative complement is anticommutative regarding intersection.
     (Contributed by Zhi Wang, 5-Sep-2024.) $)
  disjdifb $p |- ( ( A \ B ) i^i ( B \ A ) ) = (/) $=
    ( cdif cin c0 indif1 disjdif difeq1i 0dif 3eqtri ) ABCBACZDAKDZBCEBCEAKBFLE
    BABGHBIJ $.

  ${
    predisj.1 $e |- ( ph -> Fun F ) $.
    predisj.2 $e |- ( ph -> ( A i^i B ) = (/) ) $.
    predisj.3 $e |- ( ph -> S C_ ( `' F " A ) ) $.
    predisj.4 $e |- ( ph -> T C_ ( `' F " B ) ) $.
    $( Preimages of disjoint sets are disjoint.  (Contributed by Zhi Wang,
       9-Sep-2024.) $)
    predisj $p |- ( ph -> ( S i^i T ) = (/) ) $=
      ( ccnv cima cin c0 wfun wceq inpreima syl imaeq2d ima0 ssdisjd ssdisjdr
      eqtrdi eqtr3d ) AEFKZCLZDJADUEBLZUFIAUEBCMZLZUGUFMZNAFOUIUJPGBCFQRAUIUENL
      NAUHNUEHSUETUCUDUAUB $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Unordered and ordered pairs
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( The singleton of the universal class is the empty set.  (Contributed by
     Zhi Wang, 19-Sep-2024.) $)
  vsn $p |- { _V } = (/) $=
    ( cvv wcel wn csn c0 wceq vprc snprc mpbi ) AABCADEFGAHI $.

  ${
    $d A x z $.  $d A y z $.  $d B x $.
    $( "At most one" element in a singleton.  (Contributed by Zhi Wang,
       19-Sep-2024.) $)
    mosn $p |- ( A = { B } -> E* x x e. A ) $=
      ( csn wceq cv wcel wmo wtru wrmo rmosn rmotru mpbir eleq2 mobidv mpbiri )
      BCDZEZAFZBGZAHSQGZAHZUBIAQJIACKAQLMRTUAABQSNOP $.

    $( "At most one" element in an empty set.  (Contributed by Zhi Wang,
       19-Sep-2024.) $)
    mo0 $p |- ( A = (/) -> E* x x e. A ) $=
      ( c0 wceq cvv csn cv wcel wmo vsn eqcomi eqeq1 mpbiri mosn syl ) BCDZBEFZ
      DZAGBHAIPRCQDQCJKBCQLMABENO $.

    $( "At most one" element in a subclass of a singleton.  (Contributed by Zhi
       Wang, 23-Sep-2024.) $)
    mosssn $p |- ( A C_ { B } -> E* x x e. A ) $=
      ( csn wss c0 wceq wo cv wcel wmo sssn mo0 mosn jaoi sylbi ) BCDZEBFGZBQGZ
      HAIBJAKZBCLRTSABMABCNOP $.

    $( Two ways of expressing "at most one" element in a class.  (Contributed
       by Zhi Wang, 19-Sep-2024.) $)
    mo0sn $p |- ( E* x x e. A <-> ( A = (/) \/ E. y A = { y } ) ) $=
      ( vz cv wcel wmo c0 wceq csn wex wo nfv eleq1w cbvmow wn wa wb wal weu
      neq0 anbi1i df-eu eu6 dfcleq velsn bibi2i albii sylbbr eximi sylbi expcom
      3bitr2i orrd mo0 mosn exlimiv jaoi impbii bitri ) AECFZAGDEZCFZDGZCHIZCBE
      ZJZIZBKZLZVAVCADVADMVCAMADCNOVDVJVDVEVIVEPZVDVIVKVDQZVCVBVFIZRZDSZBKZVIVL
      VCDKZVDQVCDTVPVKVQVDDCUAUBVCDUCVCDBUDUMVOVHBVHVCVBVGFZRZDSVODCVGUEVSVNDVR
      VMVCDVFUFUGUHUIUJUKULUNVEVDVIDCUOVHVDBDCVFUPUQURUSUT $.

    $( Two ways of expressing "at most one" element in a class.  (Contributed
       by Zhi Wang, 23-Sep-2024.) $)
    mosssn2 $p |- ( E* x x e. A <-> E. y A C_ { y } ) $=
      ( c0 wceq cv csn wo wex wss wcel wmo 19.45v sssn exbii mo0sn 3bitr4ri ) C
      DEZCBFZGZEZHZBIRUABIHCTJZBIAFCKALRUABMUCUBBCSNOABCPQ $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  The union of a class
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d A x y $.  $d B x y $.
    $( Superclass of the greatest lower bound.  A dual statement of ~ ssintub .
       (Contributed by Zhi Wang, 29-Sep-2024.) $)
    unilbss $p |- U. { x e. B | x C_ A } C_ A $=
      ( vy cv wss crab cuni unissb wcel sseq1 elrab simprbi mprgbir ) AEZBFZACG
      ZHBFDEZBFZDQDQBIRQJRCJSPSARCORBKLMN $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Indexed union and intersection
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( An indexed union is empty iff all indexed classes are empty.  (Contributed
     by Zhi Wang, 1-Nov-2025.) $)
  iuneq0 $p |- ( A. x e. A B = (/) <-> U_ x e. A B = (/) ) $=
    ( ciun c0 wss wral wceq iunss ss0b ralbii 3bitr3ri ) ABCDZEFCEFZABGMEHCEHZA
    BGABCEIMJNOABCJKL $.

  ${
    $d A y $.  $d B y $.  $d x y $.
    $( An indexed intersection is empty if one of the intersected classes is
       empty.  (Contributed by Zhi Wang, 30-Oct-2025.) $)
    iineq0 $p |- ( E. x e. A B = (/) -> |^|_ x e. A B = (/) ) $=
      ( vy c0 wceq wrex ciin cv wcel wral wn nel02 reximi rexnal sylib wb eliin
      cvv elv sylnibr eq0rdv ) CEFZABGZDABCHZUDDIZCJZABKZUFUEJZUDUGLZABGUHLUCUJ
      ABCUFMNUGABOPUIUHQDAUFBCSRTUAUB $.
  $}

  ${
    $d A x $.  $d C x $.  $d X x $.  $d ph x $.
    iunlub.1 $e |- ( ph -> X e. A ) $.
    iunlub.2 $e |- ( ( ph /\ x = X ) -> B = C ) $.
    ${
      iunlub.3 $e |- ( ( ph /\ x e. A ) -> B C_ C ) $.
      $( The indexed union is the the lowest upper bound if it exists.
         (Contributed by Zhi Wang, 1-Nov-2025.) $)
      iunlub $p |- ( ph -> U_ x e. A B = C ) $=
        ( ciun iunssd wss wrex cv wceq wa sseq2d ssidd rspcedvd ssiun syl eqssd
        ) ABCDJZEABCDEIKAEDLZBCMEUCLAUDEELBFCGABNFOPDEEHQAERSBCDETUAUB $.
    $}

    ${
      iinglb.3 $e |- ( ( ph /\ x e. A ) -> C C_ B ) $.
      $( The indexed intersection is the the greatest lower bound if it exists.
         (Contributed by Zhi Wang, 1-Nov-2025.) $)
      iinglb $p |- ( ph -> |^|_ x e. A B = C ) $=
        ( ciin wss wrex cv wceq wa sseq1d ssidd rspcedvd iinss syl ssiin sylibr
        wral ralrimiva eqssd ) ABCDJZEADEKZBCLUFEKAUGEEKBFCGABMFNODEEHPAEQRBCDE
        STAEDKZBCUCEUFKAUHBCIUDBCDEUAUBUE $.
    $}
  $}

  ${
    $d A x $.  $d C x $.
    $( Indexed union of identical classes.  (Contributed by Zhi Wang,
       6-Nov-2025.) $)
    iuneqconst2 $p |- ( ( A =/= (/) /\ A. x e. A B = C ) -> U_ x e. A B = C )
    $=
      ( c0 wne wceq wral ciun wss eqimss ralimi adantl iunss sylibr wrex r19.2z
      wa eqimss2 reximi ssiun 3syl eqssd ) BEFZCDGZABHZRZABCIZDUGCDJZABHZUHDJUF
      UJUDUEUIABCDKLMABCDNOUGUEABPDCJZABPDUHJUEABQUEUKABDCSTABCDUAUBUC $.

    $( Indexed intersection of identical classes.  (Contributed by Zhi Wang,
       6-Nov-2025.) $)
    iineqconst2 $p |- ( ( A =/= (/) /\ A. x e. A B = C ) -> |^|_ x e. A B = C )
    $=
      ( c0 wne wceq wral wa ciin wrex r19.2z eqimss reximi iinss eqimss2 ralimi
      wss 3syl adantl ssiin sylibr eqssd ) BEFZCDGZABHZIZABCJZDUGUEABKCDRZABKUH
      DRUEABLUEUIABCDMNABCDOSUGDCRZABHZDUHRUFUKUDUEUJABDCPQTABCDUAUBUC $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  ZF Set Theory - add the Axiom of Replacement
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Theorems requiring subset and intersection existence
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d A x $.  $d B x $.  $d V x $.
    $( Two ways of expressing a collection of subsets as seen in ~ df-ntr ,
       ~ unimax , and others.  (Contributed by Zhi Wang, 27-Sep-2024.) $)
    inpw $p |- ( B e. V -> ( A i^i ~P B ) = { x e. A | x C_ B } ) $=
      ( wcel cpw cin cv crab wss dfin5 elpw2g rabbidv eqtrid ) CDEZBCFZGAHZPEZA
      BIQCJZABIABPKORSABQCDLMN $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  ZF Set Theory - add the Axiom of Power Sets
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Ordered pair theorem
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( Two ordered pairs are not equal if their first components are not equal.
     (Contributed by Zhi Wang, 7-Oct-2025.) $)
  opth1neg $p |- ( ( A e. V /\ B e. W )
          -> ( A =/= C -> <. A , B >. =/= <. C , D >. ) ) $=
    ( wne cop wcel wa wo orc opthneg imbitrrid ) ACGZABHCDHGAEIBFIJOBDGZKOPLABC
    DEFMN $.

  $( Two ordered pairs are not equal if their second components are not equal.
     (Contributed by Zhi Wang, 7-Oct-2025.) $)
  opth2neg $p |- ( ( A e. V /\ B e. W )
          -> ( B =/= D -> <. A , B >. =/= <. C , D >. ) ) $=
    ( wne cop wcel wa wo olc opthneg imbitrrid ) BDGZABHCDHGAEIBFIJACGZOKOPLABC
    DEFMN $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Ordered-pair class abstractions (cont.)
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d A x y $.  $d B x y $.  $d U x y $.  $d V x y $.  $d ch x y $.
    $d ph x y $.
    brab2dd.1 $e |- ( ph -> R = { <. x , y >. |
            ( ( x e. C /\ y e. D ) /\ ps ) } ) $.
    ${
      brab2dd.2 $e |- ( ( ph /\ ( x = A /\ y = B ) ) -> ( ps <-> ch ) ) $.
      brab2dd.3 $e |- ( ( ph /\ ( x = A /\ y = B ) ) -> ( ( x e. C /\ y e. D )
                <-> ( A e. U /\ B e. V ) ) ) $.
      $( Expressing that two sets are related by a binary relation which is
         expressed as a class abstraction of ordered pairs.  (Contributed by
         Zhi Wang, 24-Sep-2025.) $)
      brab2dd $p |- ( ph -> ( A R B <-> ( ( A e. U /\ B e. V ) /\ ch ) ) ) $=
        ( cop cv wceq wcel wa wbr copab df-br eleq2d bitrid elopab bitrdi simpl
        wex eqcom vex opth sylbb1 ad2antrl simprrl biimpa syl21anc exlimdvv imp
        ex simprl simprr wb anbi12d adantlr copsex2dv bibiad bitrd ) AFGJUAZFGP
        ZDQZEQZPZRZVKHSVLISTZBTZTZEUIDUIZFKSZGLSZTZCTZAVIVJVPDEUBZSZVRVIVJJSAWD
        FGJUCAJWCVJMUDUEVPDEVJUFUGAVRWBWAAVRWAAVQWADEAVQWAAVQTAVKFRVLGRTZVOWAAV
        QUHVNWEAVPVMVJRVNWEVMVJUJVKVLFGDUKEUKULUMUNAVNVOBUOAWETZVOWAOUPUQUTURUS
        AWACVAAWATVPWBDEFGKLAVSVTVAAVSVTVBAWEVPWBVCWAWFVOWABCONVDVEVFVGVH $.
    $}

    brab2ddw.2 $e |- ( x = A -> ( ps <-> th ) ) $.
    brab2ddw.3 $e |- ( y = B -> ( th <-> ch ) ) $.
    ${
      brab2ddw.4 $e |- ( ( x = A /\ y = B ) -> C = U ) $.
      brab2ddw.5 $e |- ( ( x = A /\ y = B ) -> D = V ) $.
      $( Expressing that two sets are related by a binary relation which is
         expressed as a class abstraction of ordered pairs.  (Contributed by
         Zhi Wang, 24-Sep-2025.) $)
      brab2ddw $p |- ( ph -> ( A R B <-> ( ( A e. U /\ B e. V ) /\ ch ) ) ) $=
        ( wa wcel cv wceq sylan9bb adantl simpl eleq12d simpr anbi12d brab2dd
        wb ) ABCEFGHIJKLMNEUAZGUBZFUAZHUBZSZBCUJAULBDUNCOPUCUDUOUKITZUMJTZSGLTZ
        HMTZSUJAUOUPURUQUSUOUKGILULUNUEQUFUOUMHJMULUNUGRUFUHUDUI $.
    $}

    ${
      brab2ddw2.4 $e |- ( x = A -> C = U ) $.
      brab2ddw2.5 $e |- ( y = B -> D = V ) $.
      $( Expressing that two sets are related by a binary relation which is
         expressed as a class abstraction of ordered pairs.  (Contributed by
         Zhi Wang, 24-Sep-2025.) $)
      brab2ddw2 $p |- ( ph -> ( A R B <-> ( ( A e. U /\ B e. V ) /\ ch ) ) ) $=
        ( wa wcel cv wceq wb sylan9bb adantl id eleq12d bi2anan9 brab2dd ) ABCE
        FGHIJKLMNEUAZGUBZFUAZHUBZSZBCUCAUKBDUMCOPUDUEUNUJITZULJTZSGLTZHMTZSUCAU
        KUOUQUMUPURUKUJGILUKUFQUGUMULHJMUMUFRUGUHUEUI $.
    $}
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Relations
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d A x y z $.  $d B y z $.  $d C y z $.
    $( Indexed intersection of Cartesian products is the Cartesian product of
       indexed intersections.  See also ~ inxp and ~ intxpd .  (Contributed by
       Zhi Wang, 30-Oct-2025.) $)
    iinxp $p |- ( A =/= (/) ->
            |^|_ x e. A ( B X. C ) = ( |^|_ x e. A B X. |^|_ x e. A C ) ) $=
      ( vy vz c0 cxp ciin wrel wral relxp cv wcel wa wb cvv eliin elv opelxp
      wne wceq wrex rgenw r19.2z mpan2 reliin syl cop anbi12i opex ax-mp ralbii
      r19.26 3bitri 3bitr4ri eqrelriv sylancl ) BGUAZABCDHZIZJZABCIZABDIZHZJVAV
      EUBUSUTJZABUCZVBUSVFABKVGVFABCDLUDVFABUEUFABUTUGUHVCVDLEFVAVEEMZVCNZFMZVD
      NZOVHCNZABKZVJDNZABKZOZVHVJUIZVENVQVANZVIVMVKVOVIVMPEAVHBCQRSVKVOPFAVJBDQ
      RSUJVHVJVCVDTVRVQUTNZABKZVLVNOZABKVPVQQNVRVTPVHVJUKAVQBUTQRULVSWAABVHVJCD
      TUMVLVNABUNUOUPUQUR $.
  $}

  ${
    $d A x $.  $d ph x $.
    intxpd.1 $e |- ( ph -> A =/= (/) ) $.
    intxpd.2 $e |- ( ( ph /\ x e. A ) -> x = ( dom x X. ran x ) ) $.
    intxpd.3 $e |- X = |^|_ x e. A dom x $.
    intxpd.4 $e |- Y = |^|_ x e. A ran x $.
    $( Intersection of Cartesian products is the Cartesian product of
       intersection of domains and ranges.  See also ~ inxp and ~ iinxp .
       (Contributed by Zhi Wang, 30-Oct-2025.) $)
    intxpd $p |- ( ph -> |^| A = ( X X. Y ) ) $=
      ( cint cv cdm ciin crn cxp intiin iineq2dv eqtrid c0 wne wceq iinxp eqtrd
      syl xpeq12i eqtr4di ) ACJZBCBKZLZMZBCUHNZMZOZDEOAUGBCUIUKOZMZUMAUGBCUHMUO
      BCPABCUHUNGQRACSTUOUMUAFBCUIUKUBUDUCDUJEULHIUEUF $.
  $}

  ${
    $d A x y z $.  $d B x y z $.  $d C x y z $.
    $( Composition with a Cartesian product.  (Contributed by Zhi Wang,
       6-Oct-2025.) $)
    coxp $p |- ( A o. ( B X. C ) ) = ( B X. ( A " C ) ) $=
      ( vx vy vz cxp ccom cima relco relxp cv wbr wex wcel cop brxp vex 3bitr4i
      wa anbi1i anass bitri exbii opelco elima2 anbi2i opelxp 19.42v eqrelriiv
      ) DEABCGZHZBACIZGZAUKJBUMKDLZFLZUKMZUPELZAMZTZFNUOBOZUPCOZUSTZTZFNZUOURPZ
      ULOVFUNOZUTVDFUTVAVBTZUSTVDUQVHUSUOUPBCQUAVAVBUSUBUCUDFUOURAUKDRERZUEVAUR
      UMOZTVAVCFNZTVGVEVJVKVAFURACVIUFUGUOURBUMUHVAVCFUISSUJ $.
  $}

  $( Composition with an ordered pair singleton.  (Contributed by Zhi Wang,
     6-Oct-2025.) $)
  cosn $p |- ( ( B e. U /\ C e. V )
            -> ( A o. { <. B , C >. } ) = ( { B } X. ( A " { C } ) ) ) $=
    ( wcel wa csn cxp ccom cop cima xpsng coeq2d coxp eqtr3di ) BDFCEFGZABHZCHZ
    IZJABCKHZJRASLIQTUAABCDEMNARSOP $.

  ${
    cosni.1 $e |- B e. _V $.
    cosni.2 $e |- C e. _V $.
    $( Composition with an ordered pair singleton.  (Contributed by Zhi Wang,
       6-Oct-2025.) $)
    cosni $p |- ( A o. { <. B , C >. } ) = ( { B } X. ( A " { C } ) ) $=
      ( cvv wcel cop csn ccom cima cxp wceq cosn mp2an ) BFGCFGABCHIJBIACIKLMDE
      ABCFFNO $.
  $}

  ${
    $d A x $.  $d B x $.  $d F x $.
    $( The inverse image of a singleton subset of an image is non-empty.
       (Contributed by Zhi Wang, 7-Nov-2025.) $)
    inisegn0a $p |- ( A e. ( F " B ) -> ( `' F " { A } ) =/= (/) ) $=
      ( vx cima wcel cv wbr wrex ccnv csn wne elimag ibi vex eliniseg biimtrrdi
      c0 ne0i rexlimdvw mpd ) ACBEZFZDGZACHZDBIZCJAKEZRLZUCUFDACBUBMNUCUEUHDBUC
      UEUDUGFUHCAUDUBDOPUGUDSQTUA $.
  $}

  $( A Cartesian product is the Cartesian product of its domain and range.
     (Contributed by Zhi Wang, 30-Oct-2025.) $)
  dmrnxp $p |- ( R = ( A X. B ) -> R = ( dom R X. ran R ) ) $=
    ( cxp wceq c0 wne cdm crn wn wa simpl nne bilani eqtrdi eqtrd dmeqd xpeq12d
    rneqd eqtr4d xpeq1d 0xp dm0 rn0 xpeq2d xp0 dmxp ad2antll ad2antrl pm2.61dda
    rnxp ) CABDZEZAFGZBFGZCCHZCIZDZEUMUNJZKZCFURUTCULFUMUSLUTULFBDFUTAFBUSAFEUM
    AFMNUABUBOPZUTURFFDZFUTUPFUQFUTUPFHZFUTCFVAQUCOUTUQFIZFUTCFVASUDORFUBZOTUMU
    OJZKZCFURVGCULFUMVFLVGULAFDFVGBFAVFBFEUMBFMNUEAUFOPZVGURVBFVGUPFUQFVGUPVCFV
    GCFVHQUCOVGUQVDFVGCFVHSUDORVEOTUMUNUOKZKZCULURUMVILZVJUPAUQBVJUPULHZAVJCULV
    KQUOVLAEUMUNABUGUHPVJUQULIZBVJCULVKSUNVMBEUMUOABUKUIPRTUJ $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Functions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d A g $.  $d f g $.  $d B f $.
    $( There is at most one function into the empty set.  (Contributed by Zhi
       Wang, 19-Sep-2024.) $)
    mof0 $p |- E* f f : A --> (/) $=
      ( vg c0 cv wf wmo wceq wi wal wex 0ex eqeq2 imbi2d albidv f00 simplbi mpg
      spcev dfmo mpbir ) ADBEZFZBGUCUBCEZHZIZBJZCKZUCUBDHZIZUHBUGUJBJCDLUDDHZUF
      UJBUKUEUIUCUDDUBMNOSUCUIADHAUBPQRUCBCTUA $.

    $( A variant of ~ mof0 .  (Contributed by Zhi Wang, 20-Sep-2024.) $)
    mof02 $p |- ( B = (/) -> E* f f : A --> B ) $=
      ( c0 wceq cv wf wmo mof0 feq3 mobidv mpbiri ) BDEZABCFZGZCHADNGZCHACIMOPC
      BDANJKL $.
  $}

  ${
    $d A f g $.
    $( Alternate proof of ~ mof0 with stronger requirements on distinct
       variables.  Uses ~ mo4 .  (Contributed by Zhi Wang, 19-Sep-2024.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    mof0ALT $p |- E* f f : A --> (/) $=
      ( vg c0 cv wf wmo wa wceq wi wal f00 simplbi eqtr3 syl2an gen2 feq1 mpbir
      mo4 ) ADBEZFZBGUAADCEZFZHTUBIZJZCKBKUEBCUATDIZUBDIZUDUCUAUFADIZATLMUCUGUH
      AUBLMTUBDNOPUAUCBCADTUBQSR $.
  $}

  ${
    $d A f g x $.  $d B f g x $.  $d f ph $.
    eufsn.1 $e |- ( ph -> B e. W ) $.
    ${
      eufsnlem.2 $e |- ( ph -> ( A X. { B } ) e. V ) $.
      $( There is exactly one function into a singleton.  For a simpler
         hypothesis, see ~ eufsn assuming ~ ax-rep , or ~ eufsn2 assuming
         ~ ax-pow and ~ ax-un .  (Contributed by Zhi Wang, 19-Sep-2024.) $)
      eufsnlem $p |- ( ph -> E! f f : A --> { B } ) $=
        ( vg csn cv wf wceq wb wal wex weu cxp wcel syl fconst2g alrimiv bibi2d
        eqeq2 albidv spcedv eu6im ) ABCJZDKZLZUIIKZMZNZDOZIPUJDQAUNUJUIBUHRZMZN
        ZDOIEUOHAUQDACFSUQGBCFUIUATUBUKUOMZUMUQDURULUPUJUKUOUIUDUCUEUFUJDIUGT
        $.
    $}

    eufsn.2 $e |- ( ph -> A e. V ) $.
    $( There is exactly one function into a singleton, assuming ~ ax-rep .  See
       ~ eufsn2 for different axiom requirements.  If existence is not needed,
       use ~ mofsn or ~ mofsn2 for fewer axiom assumptions.  (Contributed by
       Zhi Wang, 19-Sep-2024.) $)
    eufsn $p |- ( ph -> E! f f : A --> { B } ) $=
      ( vx cvv wcel csn cxp cmpt fconstmpt mptexg eqeltrid syl eufsnlem ) ABCDJ
      FGABEKZBCLMZJKHTUAIBCNJIBCOIBCEPQRS $.

    $( There is exactly one function into a singleton, assuming ~ ax-pow and
       ~ ax-un .  Variant of ~ eufsn .  If existence is not needed, use ~ mofsn
       or ~ mofsn2 for fewer axiom assumptions.  (Contributed by Zhi Wang,
       19-Sep-2024.) $)
    eufsn2 $p |- ( ph -> E! f f : A --> { B } ) $=
      ( cvv wcel csn cxp snex xpexg sylancl eufsnlem ) ABCDIFGABEJCKZIJBQLIJHCM
      BQEINOP $.
  $}

  ${
    $d A f g y $.  $d B f g x y $.  $d V f g $.  $d Y f $.
    $( There is at most one function into a singleton, with fewer axioms than
       ~ eufsn and ~ eufsn2 .  See also ~ mofsn2 .  (Contributed by Zhi Wang,
       19-Sep-2024.) $)
    mofsn $p |- ( B e. V -> E* f f : A --> { B } ) $=
      ( vg wcel csn cv wf wa wceq wal wmo cxp fconst2g biimpd eqtr3 a1i syl2and
      wi alrimivv feq1 mo4 sylibr ) BDFZABGZCHZIZAUFEHZIZJUGUIKZTZELCLUHCMUEULC
      EUEUHUGAUFNZKZUJUIUMKZUKUEUHUNABDUGOPUEUJUOABDUIOPUNUOJUKTUEUGUIUMQRSUAUH
      UJCEAUFUGUIUBUCUD $.

    $( There is at most one function into a singleton.  An unconditional
       variant of ~ mofsn , i.e., the singleton could be empty if ` Y ` is a
       proper class.  (Contributed by Zhi Wang, 19-Sep-2024.) $)
    mofsn2 $p |- ( B = { Y } -> E* f f : A --> B ) $=
      ( csn wceq cvv wcel cv wf wa mofsn adantl wb feq3 mobidv adantr mpbird c0
      wmo wn simpl snprc bilani eqtrd mof02 syl pm2.61dan ) BDEZFZDGHZABCIZJZCT
      ZUJUKKUNAUIULJZCTZUKUPUJADCGLMUJUNUPNUKUJUMUOCBUIAULOPQRUJUKUAZKZBSFUNURB
      UISUJUQUBUQUISFUJDUCUDUEABCUFUGUH $.

    $( There is at most one function into a subclass of a singleton.
       (Contributed by Zhi Wang, 24-Sep-2024.) $)
    mofsssn $p |- ( B C_ { Y } -> E* f f : A --> B ) $=
      ( csn wss c0 wceq wo cv wf wmo sssn mof02 mofsn2 jaoi sylbi ) BDEZFBGHZBR
      HZIABCJKCLZBDMSUATABCNABCDOPQ $.

    $( There is at most one function into a class containing at most one
       element.  (Contributed by Zhi Wang, 19-Sep-2024.) $)
    mofmo $p |- ( E* x x e. B -> E* f f : A --> B ) $=
      ( vy cv wcel wmo c0 wceq csn wex wo mo0sn mof02 mofsn2 exlimiv jaoi sylbi
      wf ) AFCGAHCIJZCEFZKJZELZMBCDFTDHZAECNUAUEUDBCDOUCUEEBCDUBPQRS $.
  $}

  ${
    $d A y $.  $d B x y $.  $d F y $.  $d G y $.  $d ph y $.
    mofeu.1 $e |- G = ( A X. B ) $.
    mofeu.2 $e |- ( ph -> ( B = (/) -> A = (/) ) ) $.
    mofeu.3 $e |- ( ph -> E* x x e. B ) $.
    $( The uniqueness of a function into a set with at most one element.
       (Contributed by Zhi Wang, 1-Oct-2024.) $)
    mofeu $p |- ( ph -> ( F : A --> B <-> F = G ) ) $=
      ( vy c0 wceq wf wb cv wex wa feq3 adantl cxp csn imp f00 rbaib syl eqtrdi
      xpeq2 xp0 eqtrid eqeq2d 3bitr4d 19.42v cvv fconst2g bibi12d mpbiri eqeq2i
      elv bitr4di exlimiv sylbir wcel wmo wo mo0sn sylib mpjaodan ) ADKLZCDEMZE
      FLZNZDJOZUAZLZJPZAVHQZCKEMZEKLZVIVJVPCKLZVQVRNAVHVSHUBVQVRVSCEUCUDUEVHVIV
      QNADKCERSVPFKEVHFKLAVHFCDTZKGVHVTCKTKDKCUGCUHUFUISUJUKAVOQAVNQZJPVKAVNJUL
      WAVKJVNVKAVNVIEVTLZVJVNVIWBNCVMEMZECVMTZLZNZWFJCVLUMEUNURVNVIWCWBWEDVMCER
      VNVTWDEDVMCUGUJUOUPFVTEGUQUSSUTVAABODVBBVCVHVOVDIBJDVEVFVG $.
  $}

  $( If a function value has a member, then the function is not an empty set
     (An artifact of our function value definition.)  (Contributed by Zhi Wang,
     16-Sep-2024.) $)
  elfvne0 $p |- ( A e. ( F ` B ) -> F =/= (/) ) $=
    ( cfv wcel c0 wne ne0i wceq fveq1 0fv eqtrdi necon3i syl ) ABCDZEOFGCFGOAHC
    FOFCFIOBFDFBCFJBKLMN $.

  $( A function with non-empty domain is non-empty and has non-empty codomain.
     (Contributed by Zhi Wang, 1-Oct-2024.) $)
  fdomne0 $p |- ( ( F : X --> Y /\ X =/= (/) )
               -> ( F =/= (/) /\ Y =/= (/) ) ) $=
    ( wf c0 wne wa f0dom0 necon3bid biimpa wceq wn wi feq3 f00 simprbi biimtrdi
    nne imbitrrdi imnan sylib necon2ai jca ) BCADZBEFZGZAEFZCEFUDUEUGUDBEAEABCH
    IJUFCECEKZUDUELZMUFLUHUDBEKZUIUHUDBEADZUJCEBANUKAEKUJBAOPQBERSUDUETUAUBUC
    $.

  $( A function that maps a singleton to a class is injective.  (Contributed by
     Zhi Wang, 1-Oct-2024.) $)
  f1sn2g $p |- ( ( A e. V /\ F : { A } --> B ) -> F : { A } -1-1-> B ) $=
    ( wcel csn wf wa wf1 cfv cop wceq fsn2g biimpa simpld f1sng syldan wb f1eq1
    simpl2im mpbird ) ADEZAFZBCGZHZUCBCIZUCBAACJZKFZIZUBUDUGBEZUIUEUJCUHLZUBUDU
    JUKHABCDMNZOAUGDBPQUEUJUKUFUIRULUCBCUHSTUA $.

  $( A function that maps the empty set to a class is injective.  (Contributed
     by Zhi Wang, 1-Oct-2024.) $)
  f102g $p |- ( ( A = (/) /\ F : A --> B ) -> F : A -1-1-> B ) $=
    ( c0 wceq wf wa wf1 feq2 biimpa f0bi f10 f1eq1 mpbiri sylbi wb f1eq2 adantr
    syl mpbird ) ADEZABCFZGZABCHZDBCHZUCDBCFZUEUAUBUFADBCIJUFCDEZUECBKUGUEDBDHB
    LDBCDMNOSUAUDUEPUBADBCQRT $.

  ${
    $d A x y $.  $d B y $.  $d F y $.
    $( A function that maps a set with at most one element to a class is
       injective.  (Contributed by Zhi Wang, 1-Oct-2024.) $)
    f1mo $p |- ( ( E* x x e. A /\ F : A --> B ) -> F : A -1-1-> B ) $=
      ( vy cv wcel wmo c0 wceq csn wex wo wf wf1 mo0sn f102g wi cvv vex imbi12d
      f1sn2g mpan feq2 f1eq2 mpbiri exlimiv imp jaoian sylanb ) AFBGAHBIJZBEFZK
      ZJZELZMBCDNZBCDOZAEBPUKUPUQUOBCDQUOUPUQUNUPUQRZEUNURUMCDNZUMCDOZRULSGUSUT
      ETULCDSUBUCUNUPUSUQUTBUMCDUDBUMCDUEUAUFUGUHUIUJ $.
  $}

  ${
    f002.1 $e |- ( ph -> F : A --> B ) $.
    $( A function with an empty codomain must have empty domain.  (Contributed
       by Zhi Wang, 1-Oct-2024.) $)
    f002 $p |- ( ph -> ( B = (/) -> A = (/) ) ) $=
      ( wf c0 wceq feq3 f00 simprbi biimtrdi syl5com ) ABCDFZCGHZBGHZEONBGDFZPC
      GBDIQDGHPBDJKLM $.
  $}

  ${
    $d A f $.  $d B f $.  $d V f $.  $d W f $.
    map0cor.1 $e |- ( ph -> A e. V ) $.
    map0cor.2 $e |- ( ph -> B e. W ) $.
    $( A function exists iff an empty codomain is accompanied with an empty
       domain.  (Contributed by Zhi Wang, 1-Oct-2024.) $)
    map0cor $p |- ( ph -> ( ( B = (/) -> A = (/) ) <-> E. f f : A --> B ) ) $=
      ( wcel c0 wceq wi cv wf wex wb wa cmap co wn biid necon2bbii imbi2i imnan
      wne bitri map0g notbid bitr4id neq0 a1i elmapg exbidv 3bitrd syl2anc ) AC
      FIZBEIZCJKZBJKZLZBCDMZNZDOZPHGUPUQQZUTCBRSZJKZTZVAVEIZDOZVCVDUTURBJUEZQZT
      ZVGUTURVJTZLVLUSVMURVJBJVJUAUBUCURVJUDUFVDVFVKCBFEUGUHUIVGVIPVDDVEUJUKVDV
      HVBDCBVAFEULUMUNUO $.
  $}

  $( Relation with function value.  (Contributed by Zhi Wang, 25-Nov-2025.) $)
  ffvbr $p |- ( ( F : A --> B /\ X e. A ) -> X F ( F ` X ) ) $=
    ( wf wcel wfun cdm cfv wbr simpl ffund simpr fdmd eleqtrrd funfvbrb syl2anc
    wa biimpa ) ABCEZDAFZRZCGZDCHZFZDDCICJZUBABCTUAKZLUBDAUDTUAMUBABCUGNOUCUEUF
    DCPSQ $.

  ${
    $d A x y z $.  $d B x y z $.  $d C x y z $.  $d F x y z $.
    $( Composition of a Cartesian product with a function.  (Contributed by Zhi
       Wang, 25-Nov-2025.) $)
    xpco2 $p |- ( F : A --> B -> ( ( B X. C ) o. F ) = ( A X. C ) ) $=
      ( vx vy vz wf cxp ccom relco cv wbr wa wcel vex wceq brxp jca adantrr wex
      relxp cdm breldm ad2antrl fdm adantr eleqtrd simprbi ad2antll exlimdv imp
      ex ffvelcdm ffvbr simprr sylanbrc breq2 breq1 anbi12d spcedv impbida brco
      cfv 3bitr4g eqbrrdiv ) ABDHZEFBCIZDJZACIZVHDKACUBVGELZGLZDMZVLFLZVHMZNZGU
      AZVKAOZVNCOZNZVKVNVIMVKVNVJMVGVQVTVGVQVTVGVPVTGVGVPVTVGVPNZVRVSWAVKDUCZAV
      MVKWBOVGVOVKVLDEPZGPUDUEVGWBAQVPABDUFUGUHVOVSVGVMVOVLBOVSVLVNBCRUIUJSUMUK
      ULVGVTNZVPVKVKDVDZDMZWEVNVHMZNGBWEVGVRWEBOZVSABVKDUNTZWDWFWGVGVRWFVSABDVK
      UOTWDWHVSWGWIVGVRVSUPWEVNBCRUQSVLWEQVMWFVOWGVLWEVKDURVLWEVNVHUSUTVAVBGVKV
      NVHDWCFPVCVKVNACRVEVF $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Operations
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( The operation value of a singleton of a nested ordered pair is the last
     member.  (Contributed by Zhi Wang, 22-Oct-2025.) $)
  ovsng $p |- ( C e. V -> ( A { <. <. A , B >. , C >. } B ) = C ) $=
    ( wcel cop csn co cfv df-ov cvv wceq opex fvsng mpan eqtrid ) CDEZABABFZCFG
    ZHRSIZCABSJRKEQTCLABMRCKDNOP $.

  $( The operation value of a singleton of an ordered triple is the last
     member.  (Contributed by Zhi Wang, 22-Oct-2025.) $)
  ovsng2 $p |- ( C e. V -> ( A { <. A , B , C >. } B ) = C ) $=
    ( wcel cotp csn co cop df-ot sneqi oveqi ovsng eqtrid ) CDEABABCFZGZHABABIC
    IZGZHCPRABOQABCJKLABCDMN $.

  ${
    ovsn.1 $e |- C e. _V $.
    $( The operation value of a singleton of a nested ordered pair is the last
       member.  (Contributed by Zhi Wang, 22-Oct-2025.) $)
    ovsn $p |- ( A { <. <. A , B >. , C >. } B ) = C $=
      ( cvv wcel cop csn co wceq ovsng ax-mp ) CEFABABGCGHICJDABCEKL $.

    $( The operation value of a singleton of an ordered triple is the last
       member.  (Contributed by Zhi Wang, 22-Oct-2025.) $)
    ovsn2 $p |- ( A { <. A , B , C >. } B ) = C $=
      ( cvv wcel cotp csn co wceq ovsng2 ax-mp ) CEFABABCGHICJDABCEKL $.
  $}

  ${
    ovconstbrd.1 $e |- ( ph -> F = ( R X. { Y } ) ) $.
    ${
      ovconstbrd.2 $e |- ( ph -> Y e. V ) $.
      ovconstbrd.3 $e |- ( ph -> Y =/= (/) ) $.
      $( Two ways of expressing ` A R B ` .  (Contributed by Zhi Wang,
         18-Sep-2024.) $)
      ovconstbrd $p |- ( ph -> ( A R B <-> ( A F B ) = Y ) ) $=
        ( wbr cop wcel co wceq df-br wa adantr c0 wne csn oveqd df-ov fvconst2g
        cxp cfv eqtrdi sylan eqtrd simpr eqnetrd wb neeq1d mpbid ndmfv necon1ai
        cdm dmxpss sselid syl impbida bitrid ) BCDKBCLZDMZABCENZGOZBCDPAVDVFAVD
        QVEVCDGUAZUEZUFZGAVEVIOVDAVEBCVHNVIAEVHBCHUBBCVHUCUGZRAGFMVDVIGOIDGVCFU
        DUHUIAVFQZVISTZVDVKVESTZVLVKVEGSAVFUJAGSTVFJRUKAVMVLULVFAVEVISVJUMRUNVL
        VHUQZDVCDVGURVCVNMVISVCVHUOUPUSUTVAVB $.

      $( Two ways of expressing ` A R B ` .  (Contributed by Zhi Wang,
         20-Sep-2024.) $)
      ovconstbrn0d $p |- ( ph -> ( A R B <-> ( A F B ) =/= (/) ) ) $=
        ( wbr cop wcel co c0 wne df-br wa wceq adantr csn oveqd df-ov fvconst2g
        cxp cfv eqtrdi sylan eqtrd eqnetrd neeq1d biimpa dmxpss necon1ai sselid
        cdm ndmfv syl impbida bitrid ) BCDKBCLZDMZABCENZOPZBCDQAVBVDAVBRZVCGOVE
        VCVADGUAZUEZUFZGAVCVHSVBAVCBCVGNVHAEVGBCHUBBCVGUCUGZTAGFMVBVHGSIDGVAFUD
        UHUIAGOPVBJTUJAVDRVHOPZVBAVDVJAVCVHOVIUKULVJVGUPZDVADVFUMVAVKMVHOVAVGUQ
        UNUOURUSUT $.
    $}

    ${
      elovconstbrd.2 $e |- ( ph -> X e. ( A F B ) ) $.
      $( Two ways of expressing ` A R B ` .  (Contributed by Zhi Wang,
         18-Sep-2024.) $)
      elovconstbrd $p |- ( ph -> A R B ) $=
        ( cop wcel wbr co c0 wne ne0d csn cxp cfv oveqd df-ov eqtrdi neeq1d cdm
        dmxpss ndmfv necon1ai sselid biimtrdi mpd df-br sylibr ) ABCJZDKZBCDLAB
        CEMZNOZUNAUOFIPAUPUMDGQZRZSZNOZUNAUOUSNAUOBCURMUSAEURBCHTBCURUAUBUCUTUR
        UDZDUMDUQUEUMVAKUSNUMURUFUGUHUIUJBCDUKUL $.
    $}
  $}

  ${
    $d x y $.
    ovmpt4d.1 $e |- ( ph -> F = ( x e. A , y e. B |-> C ) ) $.
    ovmpt4d.2 $e |- ( ( ph /\ ( x e. A /\ y e. B ) ) -> C e. V ) $.
    $( Deduction version of ~ ovmpt4g .  (This is the operation analogue of
       ~ fvmpt2d .)  (Contributed by Zhi Wang, 9-Oct-2025.) $)
    ovmpt4d $p |- ( ( ph /\ ( x e. A /\ y e. B ) ) -> ( x F y ) = C ) $=
      ( cv wcel wa co cmpo oveqdr wceq simprl simprr eqid ovmpt4g syl3anc eqtrd
      ) ABKZDLZCKZELZMZMZUDUFGNUDUFBCDEFOZNZFAUHBCGUJIPUIUEUGFHLUKFQAUEUGRAUEUG
      SJBCDEFUJHUJTUAUBUC $.
  $}

  ${
    $d A x y $.  $d B x y $.  $d F x y $.  $d G x y $.  $d ph x y $.
    eqfnovd.1 $e |- ( ph -> F Fn ( A X. B ) ) $.
    eqfnovd.2 $e |- ( ph -> G Fn ( A X. B ) ) $.
    eqfnovd.3 $e |- ( ( ph /\ ( x e. A /\ y e. B ) )
                   -> ( x F y ) = ( x G y ) ) $.
    $( Deduction for equality of operations.  (Contributed by Zhi Wang,
       19-Nov-2025.) $)
    eqfnovd $p |- ( ph -> F = G ) $=
      ( wceq cv co wral ralrimivva cxp wfn wb eqfnov2 syl2anc mpbird ) AFGKZBLZ
      CLZFMUCUDGMKZCENBDNZAUEBCDEJOAFDEPZQGUGQUBUFRHIBCDEFGSTUA $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  ZF Set Theory - add the Axiom of Union
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Relations and functions (cont.)
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    fonex.1 $e |- B e/ _V $.
    fonex.2 $e |- F : A -onto-> B $.
    $( The domain of a surjection is a proper class if the range is a proper
       class as well.  Can be used to prove that if a structure component
       extractor restricted to a class maps onto a proper class, then the class
       is a proper class as well.  (Contributed by Zhi Wang, 20-Oct-2025.) $)
    fonex $p |- A e/ _V $=
      ( cvv wcel neli cdm crn wfun wfo fofun ax-mp funrnex mpi wfn fndmi eleq1i
      fofn wceq forn 3imtr3i mto nelir ) AFAFGZBFGZBFDHCIZFGZCJZFGZUFUGUICKZUKA
      BCLZULEABCMNFCOPUHAFACUMCAQEABCTNRSUJBFUMUJBUAEABCUBNSUCUDUE $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  First and second members of an ordered pair
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d A w x $.  $d A w y $.  $d A w z $.  $d ph w $.
    $( Reconstruction of a nested ordered pair in terms of its ordered pair
       components.  (Contributed by Zhi Wang, 27-Oct-2025.) $)
    eloprab1st2nd $p |- ( A e. { <. <. x , y >. , z >. | ph }
     -> A = <. <. ( 1st ` ( 1st ` A ) ) , ( 2nd ` ( 1st ` A ) ) >.
              , ( 2nd ` A ) >. ) $=
      ( vw coprab wcel cv cop wceq wex c1st cfv c2nd vex fveq2d eqtr2di opeq12d
      wa eqeq1 anbi1d 3exbidv df-oprab elab2g id opex op1std op1st op2nd op2ndd
      ibi eqcomd eqtrd adantr exlimiv exlimivv syl ) EABCDGZHZEBIZCIZJZDIZJZKZA
      TZDLZCLBLZEEMNZMNZVJONZJZEONZJZKZUTVIFIZVEKZATZDLCLBLVIFEUSUSVQEKZVSVGBCD
      VTVRVFAVQEVEUAUBUCABCDFUDUEULVHVPBCVGVPDVFVPAVFEVEVOVFUFVFVCVMVDVNVFVAVKV
      BVLVFVKVCMNVAVFVJVCMVCVDEVAVBUGZDPZUHZQVAVBBPZCPZUIRVFVLVCONVBVFVJVCOWCQV
      AVBWDWEUJRSVFVNVDVCVDEWAWBUKUMSUNUOUPUQUR $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Operations in maps-to notation (continued)
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Function transposition
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    resinsnlem.1 $e |- ( ph -> ( ch <-> -. ps ) ) $.
    resinsnlem.2 $e |- ( -. ph -> ch ) $.
    $( Lemma for ~ resinsnALT .  (Contributed by Zhi Wang, 6-Oct-2025.) $)
    resinsnlem $p |- ( ( ph /\ ps ) <-> -. ch ) $=
      ( wa wn con2bid biimpa con1i wb syl ibir jca impbii ) ABFCGZABPACBDHZIPAB
      ACEJZPBPABPKRQLMNO $.
  $}

  $( Restriction to the intersection with a singleton.  (Contributed by Zhi
     Wang, 6-Oct-2025.) $)
  resinsn $p |- ( ( F |` ( A i^i { B } ) ) = (/)
              <-> -. B e. ( dom F i^i A ) ) $=
    ( csn cin cres c0 wceq cdm wcel wn wb relres reldm0 ax-mp incom dmres inass
    wrel 3eqtr4i eqeq1i disjsn 3bitri ) CABDZEZFZGHZUFIZGHZCIZAEZUDEZGHBUKJKUFS
    UGUILCUEMUFNOUHULGUEUJEUJUEEUHULUEUJPCUEQUJAUDRTUAUKBUBUC $.

  $( Restriction to the intersection with a singleton.  (Contributed by Zhi
     Wang, 6-Oct-2025.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  resinsnALT $p |- ( ( F |` ( A i^i { B } ) ) = (/)
              <-> -. B e. ( dom F i^i A ) ) $=
    ( csn cin cres c0 wceq wcel wn wrel wb relres reldm0 incom wa ineq2d disjsn
    cdm 3bitri ax-mp dmres eqtri eqeq1i ancom wss snssi dfss2 biimpi eqtrid syl
    elin eqeq1d bitrdi biimpri in0 eqtrdi resinsnlem con2bii ) CABDZEZFZGHZVBSZ
    GHZCSZVAEZGHZBVFAEIZJVBKVCVELCVAMVBNUAVDVGGVDVAVFEVGCVAUBVAVFOUCUDVIVHVIBVF
    IZBAIZPVKVJPVHJBVFAULVJVKUEVKVJVHVKVHVFUTEZGHVJJVKVGVLGVKVAUTVFVKUTAUFZVAUT
    HBAUGVMVAUTAEZUTAUTOVMVNUTHUTAUHUIUJUKQUMVFBRUNVKJZVGVFGEGVOVAGVFVAGHVOABRU
    OQVFUPUQURTUST $.

  ${
    $d F x y $.  $d R x $.
    $( Alternate definition of ` tpos ` .  (Contributed by Zhi Wang,
       6-Oct-2025.) $)
    dftpos5 $p |- tpos F = ( F o. ( ( x e. `' dom F |-> U. `' { x } )
                                 u. { <. (/) , (/) >. } ) ) $=
      ( ctpos cdm ccnv c0 csn cun cv cuni cmpt ccom cop df-tpos mptun wcel wceq
      cvv 0ex eqtri sneq cnveqd unieqd cnvsn0 unieqi uni0 eqtrdi fmptsng uneq2i
      mp2an eqtr4i coeq2i ) BCBABDEZFGZHAIZGZEZJZKZLBAUMURKZFFMGZHZLABNUSVBBUSU
      TAUNURKZHVBAUMUNUROVAVCUTFRPZVDVAVCQSSAFURFRRUOFQZURUNEZJZFVEUQVFVEUPUNUO
      FUAUBUCVGFJFVFFUDUEUFTUGUHUJUIUKULT $.

    $( Alternate definition of ` tpos ` .  The second half of the right hand
       side could apply ~ ressn and become ` ( F |`` { (/) } ) ` .
       (Contributed by Zhi Wang, 6-Oct-2025.) $)
    dftpos6 $p |- tpos F = ( ( F o. ( x e. `' dom F |-> U. `' { x } ) )
                          u. ( { (/) } X. ( F " { (/) } ) ) ) $=
      ( ctpos cdm ccnv cv csn cuni cmpt c0 cop cun ccom cima cxp dftpos5 coundi
      0ex cosni uneq2i 3eqtri ) BCBABDEAFGEHIZJJKGZLMBUBMZBUCMZLUDJGZBUFNOZLABP
      BUBUCQUEUGUDBJJRRSTUA $.

    $( The domain of ` tpos F ` is a subset.  (Contributed by Zhi Wang,
       6-Oct-2025.) $)
    dmtposss $p |- dom tpos F C_ ( ( _V X. _V ) u. { (/) } ) $=
      ( vx ctpos cdm ccnv c0 csn cun cv cuni cmpt ccom cvv df-tpos dmeqi dmcoss
      cxp eqid wss sstri dmmptss wrel relcnv df-rel mpbi unss1 ax-mp eqsstri )
      ACZDABADZEZFGZHZBIGEJZKZLZDZMMQZULHZUIUPBANOUQUODZUSAUOPUTUMUSBUMUNUOUORU
      AUKURSZUMUSSUKUBVAUJUCUKUDUEUKURULUFUGTTUH $.

    $( The transposition of a set restricted to the empty set is the set
       restricted to the empty set.  See also ~ ressn and ~ dftpos6 for an
       alternate proof.  (Contributed by Zhi Wang, 6-Oct-2025.) $)
    tposres0 $p |- ( tpos F |` { (/) } ) = ( F |` { (/) } ) $=
      ( vx vy ctpos c0 csn cres relres cv wcel wbr wa wceq wb velsn cvv brtpos0
      elv breq1 brresi bibi12d mpbiri sylbi pm5.32i vex 3bitr4i eqbrriv ) BCADZ
      EFZGZAUIGZUHUIHAUIHBIZUIJZULCIZUHKZLUMULUNAKZLULUNUJKULUNUKKUMUOUPUMULEMZ
      UOUPNZBEOUQUREUNUHKZEUNAKZNZVACUNAPQRUQUOUSUPUTULEUNUHSULEUNASUAUBUCUDUIU
      LUNUHCUEZTUIULUNAVBTUFUG $.

    $( The transposition restricted to a set.  (Contributed by Zhi Wang,
       6-Oct-2025.) $)
    tposresg $p |- ( tpos F |` R ) = ( ( tpos F |` `' `' R )
                                     u. ( F |` ( R i^i { (/) } ) ) ) $=
      ( ctpos cres cvv cxp c0 csn cun cin ccnv rescom wrel cdm wss wceq reltpos
      reseq1i resres 3eqtri dmtposss relssres 3eqtr3i indi cnvcnv uneq1i eqtr4i
      mp2an reseq2i resundi tposres0 3eqtr3ri uneq2i eqtri ) BCZADZUOAEEFZGHZIZ
      JZDZUOAKKZAURJZIZDZUOVBDZBVCDZIZUOUSDZADUPUSDUPVAUOUSALVIUOAUOMUONUSOVIUO
      PBQBUAUOUSUBUHRUOAUSSUCUTVDUOUTAUQJZVCIVDAUQURUDVBVJVCAUEUFUGUIVEVFUOVCDZ
      IVHUOVBVCUJVKVGVFVKBURDZADZBADURDVGUOURDZADUPURDVMVKUOURALVNVLABUKRUOAURS
      ULBURALBAURSTUMUNT $.

    $( The transposition restricted to a converse is the transposition of the
       restricted class, with the empty set removed from the domain.  Note that
       the right hand side is a more useful form of
       ` ( tpos ( F |`` R ) |`` ( _V \ { (/) } ) ) ` by ~ df-tpos .
       (Contributed by Zhi Wang, 6-Oct-2025.) $)
    tposrescnv $p |- ( tpos F |` `' R )
   = ( F o. ( x e. `' dom ( F |` R ) |-> U. `' { x } ) ) $=
      ( ctpos ccnv cres cdm c0 csn cun cuni cmpt ccom df-tpos reseq1i resco cin
      cv eqtri 3eqtri resmpt3 cnvin dmres cnveqi incom indi wceq wcel wn relcnv
      wrel 0nelrel0 ax-mp disjsn mpbir uneq2i un0 3eqtr4ri mpteq1i coeq2i ) CDZ
      BEZFCACGZEZHIZJZARIEKZLZMZVBFCVHVBFZMCACBFGZEZVGLZMVAVIVBACNOCVHVBPVJVMCV
      JAVFVBQZVGLVMAVFVBVGUAAVNVLVGBVCQZEVBVDQZVLVNBVCUBVKVOCBUCUDVNVBVFQVPVBVE
      QZJZVPVFVBUEVBVDVEUFVRVPHJVPVQHVPVQHUGHVBUHUIZVBUKVSBUJVBULUMVBHUNUOUPVPU
      QSTURUSSUTT $.

    ${
      tposres2.1 $e |- ( ph -> -. (/) e. ( dom F i^i R ) ) $.
      $( The transposition restricted to a set.  (Contributed by Zhi Wang,
         6-Oct-2025.) $)
      tposres2 $p |- ( ph -> ( tpos F |` R ) = ( tpos F |` `' `' R ) ) $=
        ( ctpos cres ccnv c0 cun csn cin tposresg wcel wn resinsn sylibr uneq2d
        cdm wceq eqtrid un0 eqtrdi ) ACEZBFZUCBGGFZHIZUEAUDUECBHJKFZIUFBCLAUGHU
        EAHCRBKMNUGHSDBHCOPQTUEUAUB $.

      $( The transposition restricted to a set.  (Contributed by Zhi Wang,
         6-Oct-2025.) $)
      tposres3 $p |- ( ph -> ( tpos F |` R ) = tpos ( F |` `' R ) ) $=
        ( vx ctpos cres ccnv tposres2 cdm cv csn ccom wceq wrel relcnv ax-mp c0
        cun 3eqtri cuni cmpt crn wss wfo wf1o f1ofo forn cnvcnvss resdmss sstri
        cnvf1o eqsstri cores cima cxp dftpos6 ressn cin resres wcel wn 0nelrel0
        disjsn mpbir reseq2i res0 eqtr3i uneq2i un0 tposrescnv 3eqtr4ri eqtrdi
        ) ACFZBGVNBHZHGZCVOGZFZABCDIVQEVQJZHZEKLHUAUBZMZCWAMZVRVPWAUCZVOUDWBWCN
        WDVTHZVOVTWEWAUEZWDWENVTWEWAUFZWFVTOWGVSPEVTULQVTWEWAUGQVTWEWAUHQWEVSVO
        VSUICVOUJUKUMCWAVOUNQVRWBRLZVQWHUOUPZSWBRSWBEVQUQWIRWBVQWHGZWIRVQRURWJC
        VOWHUSZGCRGRCVOWHUTWKRCWKRNRVOVAVBZVOOWLBPVOVCQVORVDVEVFCVGTVHVIWBVJTEV
        OCVKVLVM $.
    $}

    $( The transposition restricted to a relation.  (Contributed by Zhi Wang,
       6-Oct-2025.) $)
    tposres $p |- ( Rel R -> ( tpos F |` R ) = tpos ( F |` `' R ) ) $=
      ( wrel c0 wcel wn cdm cin 0nelrel0 nel2nelin syl tposres3 ) ACZABMDAEFDBG
      ZAHEFAIDNAJKL $.

    $( The transposition restricted to a Cartesian product.  (Contributed by
       Zhi Wang, 6-Oct-2025.) $)
    tposresxp $p |- ( tpos F |` ( A X. B ) ) = tpos ( F |` ( B X. A ) ) $=
      ( ctpos cxp cres ccnv wrel wceq relxp tposres ax-mp cnvxp reseq2i tposeqi
      eqtri ) CDABEZFZCQGZFZDZCBAEZFZDQHRUAIABJQCKLTUCSUBCABMNOP $.
  $}

  $( Condition of a bijective transposition.  (Contributed by Zhi Wang,
     5-Oct-2025.) $)
  tposf1o $p |- ( F : ( A X. B ) -1-1-onto-> C
            -> tpos F : ( B X. A ) -1-1-onto-> C ) $=
    ( cxp wf1o ccnv ctpos wrel wi relxp tposf1o2 ax-mp wceq cnvxp f1oeq2 sylib
    wb ) ABEZCDFZSGZCDHZFZBAEZCUBFZSITUCJABKSCDLMUAUDNUCUERABOUAUDCUBPMQ $.

  $( Swap an ordered pair.  (Contributed by Zhi Wang, 5-Oct-2025.) $)
  tposid $p |- ( X tpos _I Y ) = <. Y , X >. $=
    ( cid ctpos co cop cfv ovtpos df-ov cvv wcel wceq opex fvi ax-mp 3eqtri ) A
    BCDEBACEBAFZCGZQABCHBACIQJKRQLBAMQJNOP $.

  ${
    tposidres.x $e |- ( ph -> X e. A ) $.
    tposidres.y $e |- ( ph -> Y e. B ) $.
    $( Swap an ordered pair.  (Contributed by Zhi Wang, 5-Oct-2025.) $)
    tposidres $p |- ( ph -> ( Y tpos ( _I |` ( A X. B ) ) X )
                          = <. X , Y >. ) $=
      ( cid cxp cres ctpos co cop cfv ovtpos df-ov eqtri opelxpd fvresd cvv fvi
      eqtrid wcel wceq opex ax-mp eqtrdi ) AEDHBCIZJZKLZDEMZHNZUKAUJUKUINZULUJD
      EUILUMEDUIODEUIPQAUKUHHADEBCFGRSUBUKTUCULUKUDDEUEUKTUAUFUG $.
  $}

  $( The swap function, or the twisting map, is bijective.  (Contributed by Zhi
     Wang, 5-Oct-2025.) $)
  tposidf1o $p |- tpos ( _I |` ( A X. B ) )
                  : ( B X. A ) -1-1-onto-> ( A X. B ) $=
    ( cxp cid cres wf1o ctpos f1oi tposf1o ax-mp ) ABCZKDKEZFBACKLGFKHABKLIJ $.

  ${
    $d R x y $.
    $( Two ways of expressing the swap function.  (Contributed by Zhi Wang,
       6-Oct-2025.) $)
    tposideq $p |- ( Rel R ->
            ( tpos _I |` R ) = ( x e. R |-> U. `' { x } ) ) $=
      ( vy wrel cid ctpos cres ccnv cv csn cuni wfn wceq a1i wcel c2nd cfv c1st
      cop cvv cmpt tposres relcnv fnresi tposfn2 mp2 dfrel2 biimpi fneq2d mpbii
      vsnex cnvex uniex eqid fnmpti cxp 1st2nd 1st2ndb biimpri 2nd1st 3syl sneq
      wa cnveqd unieqd fvmpt3i adantl fveq2d co ovtpos df-ov 3eqtr3i simpr fvex
      eqeltrrd opelcnv fvresi 3eqtrd 3eqtr4rd eqfnfvd eqtrd ) BDZEFBGEBHZGZFZAB
      AIZJZHZKZUAZBEUBWBCBWEWJWBWEWCHZLZWEBLWCDWDWCLWLBUCWCUDWCWDUEUFWBWKBWEWBW
      KBMBUGUHUIUJWJBLWBABWIWJWHWGAUKULUMZWJUNZUONWBCIZBOZVCZWOJZHZKZWOPQZWORQZ
      SZWOWJQZWOWEQZWQWOXBXASZMZWOTTUPOZWTXCMWOBUQZXHXGWOURUSWOTTUTVAWPXDWTMWBA
      WOWIWTBWJWFWOMZWHWSXJWGWRWFWOVBVDVEWNWMVFVGWQXEXFWEQZXCWDQZXCWQWOXFWEXIVH
      XKXLMWQXBXAWEVIXAXBWDVIXKXLXBXAWDVJXBXAWEVKXAXBWDVKVLNWQXFBOZXCWCOZXLXCMW
      QWOXFBXIWBWPVMVOXNXMXAXBBWOPVNWORVNVPUSWCXCVQVAVRVSVTWA $.

    tposideq2.1 $e |- R = ( A X. B ) $.
    $( Two ways of expressing the swap function.  (Contributed by Zhi Wang,
       6-Oct-2025.) $)
    tposideq2 $p |- ( tpos _I |` R ) = ( x e. R |-> U. `' { x } ) $=
      ( wrel cid ctpos cres cv csn ccnv cuni cmpt wceq cxp relxp mpbir tposideq
      releqi ax-mp ) DFZGHDIADAJKLMNOUBBCPZFBCQDUCETRADSUA $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Infinite Cartesian products
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d A f g x $.
    $( Infinite Cartesian product of the universal class is the set of
       functions with a fixed domain.  (Contributed by Zhi Wang,
       1-Nov-2025.) $)
    ixpv $p |- X_ x e. A _V = { f | f Fn A } $=
      ( vg cvv cixp cv wfn cab wf wcel dffn2 vex fneq1 elab elixpconst 3bitr4ri
      eqriv ) DABEFZCGZBHZCIZDGZBHZBEUCJUCUBKUCSKBUCLUAUDCUCDMZBTUCNOABEUCUEPQR
      $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Equinumerosity
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    fvconst0ci.1 $e |- B e. _V $.
    fvconst0ci.2 $e |- Y = ( ( A X. { B } ) ` X ) $.
    $( A constant function's value is either the constant or the empty set.
       (An artifact of our function value definition.)  (Contributed by Zhi
       Wang, 18-Sep-2024.) $)
    fvconst0ci $p |- ( Y = (/) \/ Y = B ) $=
      ( csn cxp cdm wcel c0 wceq wo cfv dmxpss sseli fvconst2 syl eqtrid olcd
      wn ndmfv orcd pm2.61i ) CABGZHZIZJZDKLZDBLZMUHUJUIUHDCUFNZBFUHCAJUKBLUGAC
      AUEOPABCEQRSTUHUAZUIUJULDUKKFCUFUBSUCUD $.
  $}

  ${
    fvconstdomi.1 $e |- B e. _V $.
    $( A constant function's value is dominated by the constant.  (An artifact
       of our function value definition.)  (Contributed by Zhi Wang,
       18-Sep-2024.) $)
    fvconstdomi $p |- ( ( A X. { B } ) ` X ) ~<_ B $=
      ( csn cxp cdm wcel cfv cdom wbr wceq sseli fvconst2 syl cvv domrefg ax-mp
      dmxpss eqbrtrdi wn c0 ndmfv 0dom pm2.61i ) CABEZFZGZHZCUGIZBJKUIUJBBJUICA
      HUJBLUHACAUFSMABCDNOBPHBBJKDBPQRTUIUAUJUBBJCUGUCBDUDTUE $.
  $}

  ${
    $d A y $.  $d F y $.  $d X y $.  $d ph y $.  $d x y $.
    f1omo.1 $e |- ( ph -> F = ( A X. { 1o } ) ) $.
    $( There is at most one element in the function value of a constant
       function whose output is ` 1o ` .  (An artifact of our function value
       definition.)  Proof could be significantly shortened by ~ fvconstdomi
       assuming ~ ax-un (see ~ f1omoALT ).  (Contributed by Zhi Wang,
       19-Sep-2024.)  (Proof shortened by SN, 24-Nov-2025.) $)
    f1omo $p |- ( ph -> E* y y e. ( F ` X ) ) $=
      ( cv cfv wcel wmo c1o csn cxp c0 wceq wo 1oex eqid fvconst0ci mo0 eqeq2i
      df1o2 mosn sylbi jaoi ax-mp fveq1d eleq2d mobidv mpbiri ) ABGZEDHZIZBJUKE
      CKLMZHZIZBJZUONOZUOKOZPUQCKEUOQUORSURUQUSBUOTUSUONLZOUQKUTUOUBUABUONUCUDU
      EUFAUMUPBAULUOUKAEDUNFUGUHUIUJ $.

    $( Obsolete version of ~ f1omo as of 24-Nov-2025.  (Contributed by Zhi
       Wang, 19-Sep-2024.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    f1omoOLD $p |- ( ph -> E* y y e. ( F ` X ) ) $=
      ( vx cv cfv wcel wmo c1o csn cxp c0 wceq wal el1o mobidv mpbiri 1oex eqid
      wo fvconst0ci mo0 wa wi eqtr3 syl2anb gen2 eleq1w mo4 mpbir eleq2w2 ax-mp
      jaoi fveq1d eleq2d ) ABHZEDIZJZBKUSECLMNZIZJZBKZVCOPZVCLPZUCVECLEVCUAVCUB
      UDVFVEVGBVCUEVGVEUSLJZBKZVIVHGHZLJZUFUSVJPZUGZGQBQVMBGVHUSOPVJOPVLVKUSRVJ
      RUSVJOUHUIUJVHVKBGBGLUKULUMVGVDVHBBVCLUNSTUPUOAVAVDBAUTVCUSAEDVBFUQURST
      $.
  $}

  ${
    $d F y $.  $d X y $.
    f1omoALT.1 $e |- ( ph -> F = ( A X. { 1o } ) ) $.
    $( There is at most one element in the function value of a constant
       function whose output is ` 1o ` .  (An artifact of our function value
       definition.)  Use ~ f1omo without assuming ~ ax-un .  (Contributed by
       Zhi Wang, 18-Sep-2024.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    f1omoALT $p |- ( ph -> E* y y e. ( F ` X ) ) $=
      ( cfv c1o cdom wbr cv wcel wmo csn cxp fveq1d fvconstdomi eqbrtrdi modom2
      1oex sylibr ) AEDGZHIJBKUBLBMAUBECHNOZGHIAEDUCFPCHETQRBUBSUA $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Order sets
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Real number intervals
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d A x y z $.  $d B x y z $.  $d C x y z $.  $d D x y z $.
    $( Intersection of two closed intervals of extended reals.  (Contributed by
       Zhi Wang, 9-Sep-2024.) $)
    iccin $p |- ( ( ( A e. RR* /\ B e. RR* ) /\ ( C e. RR* /\ D e. RR* ) ) ->
         ( ( A [,] B ) i^i ( C [,] D ) ) =
         ( if ( A <_ C , C , A ) [,] if ( B <_ D , B , D ) ) ) $=
      ( vx vy vz cle cicc df-icc cv xrmaxle xrlemin ixxin ) EFGABCDHHIEFGJACGKZ
      LOBDMN $.
  $}

  ${
    $d A w x y z $.  $d C w x y z $.  $d D w x y z $.
    $( If the upper bound of one closed interval is less than the lower bound
       of the other, the intervals are disjoint.  (Contributed by Zhi Wang,
       9-Sep-2024.) $)
    iccdisj2 $p |- ( ( A e. RR* /\ D e. RR* /\ B < C )
                      -> ( ( A [,] B ) i^i ( C [,] D ) ) = (/) ) $=
      ( vx vy vz vw cxr wcel clt wbr w3a cicc co cico cle wss simp1 wa brel syl
      simp3 ltrelxr simprd xrleidd iccssico syl22anc cin c0 simp2 df-ico df-icc
      wceq cv xrlenlt ixxdisj syl3anc ssdisjd ) AIJZDIJZBCKLZMZABNOZACPOZCDNOZV
      CUTCIJZAAQLVBVDVERUTVAVBSZVCBIJZVGVCVBVIVGTUTVAVBUCZBCIIKUDUAUBUEZVCAVHUF
      VJACABUGUHVCUTVGVAVEVFUIUJUNVHVKUTVAVBUKEFGHACDNQKQQPEFGULEFGUMCHUOUPUQUR
      US $.
  $}

  $( If the upper bound of one closed interval is less than the lower bound of
     the other, the intervals are disjoint.  (Contributed by Zhi Wang,
     9-Sep-2024.) $)
  iccdisj $p |- ( ( ( ( A e. RR* /\ B e. RR* ) /\ ( C e. RR* /\ D e. RR* ) )
     /\ B < C ) -> ( ( A [,] B ) i^i ( C [,] D ) ) = (/) ) $=
    ( cxr wcel wa clt wbr cicc co cin c0 simplll simplrr simpr iccdisj2 syl3anc
    wceq ) AEFZBEFZGZCEFZDEFZGZGZBCHIZGTUDUGABJKCDJKLMSTUAUEUGNUBUCUDUGOUFUGPAB
    CDQR $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Extensible structures
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Basic definitions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d A b k $.  $d E b k $.  $d K k $.  $d V b k $.
    slotresfo.e $e |- E Fn _V $.
    slotresfo.v $e |- ( k e. A -> ( E ` k ) e. V ) $.
    slotresfo.k $e |- ( b e. V -> K e. A ) $.
    slotresfo.b $e |- ( b e. V -> b = ( E ` K ) ) $.
    $( The condition of a structure component extractor restricted to a class
       being a surjection.  This combined with ~ fonex can be used to prove a
       class being proper.  (Contributed by Zhi Wang, 20-Oct-2025.) $)
    slotresfo $p |- ( E |` A ) : A -onto-> V $=
      ( cv cfv wceq wrex wral wfn wss cvv mp2an wcel cres wfo crn fnssres fvres
      wf ssv eqeltrd rgen fnfvrnss df-f mpbir2an fveq2 eqeq2d rspcedvdw rexbiia
      sylibr dffo3 ) AECAUAZUBAEUSUFZFKZBKZUSLZMZBANZFEOUTUSAPZUSUCEQZCRPARQVFG
      AUGRACUDSZVFVCETZBAOVGVHVIBAVBATZVCVBCLZEVBACUEZHUHUIBAEUSUJSAEUSUKULVEFE
      VAETZVAVKMZBANVEVMVNVADCLZMBDAVBDMVKVOVAVBDCUMUNIJUOVDVNBAVJVCVKVAVLUNUPU
      QUIBFAEUSURUL $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Moore spaces
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( The union of a collection of closed sets is a subset.  (Contributed by Zhi
     Wang, 29-Sep-2024.) $)
  mreuniss $p |- ( ( C e. ( Moore ` X ) /\ S C_ C ) -> U. S C_ X ) $=
    ( cmre cfv wcel wss wa cuni uniss adantl wceq mreuni adantr sseqtrd ) ACDEF
    ZBAGZHBIZAIZCQRSGPBAJKPSCLQACMNO $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Topology
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  Additional contents for topology.

$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Closure and interior
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( The union of closed sets is the underlying set of the topology (the union
     of open sets).  (Contributed by Zhi Wang, 6-Sep-2024.) $)
  clduni $p |- ( J e. Top -> U. ( Clsd ` J ) = U. J ) $=
    ( ctop wcel cuni ctopon cfv ccld cmre wceq toptopon2 biimpi cldmreon mreuni
    3syl ) ABCZAADZEFCZAGFZPHFCRDPIOQAJKPALRPMN $.

  ${
    $d J x y $.  $d ch x $.  $d ph x y $.  $d ps y $.
    opncldbid.1 $e |- ( ph -> J e. Top ) $.
    opncldbid.2 $e |- ( ( ph /\ x = ( U. J \ y ) ) -> ( ps <-> ch ) ) $.
    $( Conditions on open sets are equivalent to conditions on closed sets.
       (Contributed by Zhi Wang, 30-Aug-2024.) $)
    opncldbid $p |- ( ph -> ( A. x e. J ps <-> A. y e. ( Clsd ` J ) ch ) ) $=
      ( cuni cv cdif ccld cfv wcel eqid cldopn adantl ctop wceq wa wrex wex wss
      opncld elssuni dfss4 sylib eqcomd jca difeq2 eqeq2d anbi12d spcedv df-rex
      eleq1 sylibr sylan ralxfrd ) ABCDEFIZEJZKZFFLMZUTVBNZVAFNAUTFUSUSOZPQAFRN
      ZDJZFNZVFVASZEVBUAZGVEVGTZVCVHTZEUBVIVJVKUSVFKZVBNZVFUSVLKZSZTEVBVLVFFUSV
      DUDZVJVMVOVPVGVOVEVGVNVFVGVFUSUCVNVFSVFFUEVFUSUFUGUHQUIUTVLSZVCVMVHVOUTVL
      VBUOVQVAVNVFUTVLUSUJUKULUMVHEVBUNUPUQHUR $.
  $}

  $( Two ways of saying that two open sets are disjoint, if ` J ` is a topology
     and ` X ` is an open set.  (Contributed by Zhi Wang, 6-Sep-2024.) $)
  opndisj $p |- ( Z = ( U. J \ X ) -> ( Y e. ( J i^i ~P Z )
                                  <-> ( Y e. J /\ ( X i^i Y ) = (/) ) ) ) $=
    ( cuni cdif wceq wcel cpw wa wss cin c0 elpwg sseq2 sylan9bbr pm5.32da elin
    wb elssuni incom eqeq1i reldisj bitrid syl pm5.32i 3bitr4g ) DAEZBFZGZCAHZC
    DIZHZJUKCUIKZJCAULLHUKBCLZMGZJUJUKUMUNUKUMCDKUJUNCDANDUICOPQCAULRUKUPUNUKCU
    HKZUPUNSCATUPCBLZMGUQUNUOURMBCUAUBCBUHUCUDUEUFUG $.

  $( Two ways of saying that two closed sets are disjoint, if ` J ` is a
     topology and ` X ` is a closed set.  An alternative proof is similar to
     that of ~ opndisj with ~ elssuni replaced by the combination of ~ cldss
     and ~ eqid .  (Contributed by Zhi Wang, 6-Sep-2024.) $)
  clddisj $p |- ( Z = ( U. J \ X ) -> ( Y e. ( ( Clsd ` J ) i^i ~P Z )
                         <-> ( Y e. ( Clsd ` J ) /\ ( X i^i Y ) = (/) ) ) ) $=
    ( ccld cfv cpw cin wcel wa cuni cdif wceq c0 elin simpl ctop cldrcl clduni
    wb difeq1d adantl eqtr4d opndisj bitr3id pm5.32dar sylancom pm5.32da bitrid
    syl ) CAEFZDGZHIZCUKIZCULIZJZDAKZBLZMZUNBCHNMZJZCUKULOZUSUNUOUTUSUNDUKKZBLZ
    MZUOUTTUSUNJDURVDUSUNPUNVDURMZUSUNAQIZVFCARVGVCUQBASUAUJUBUCVEUNUOUTUPUMVEV
    AVBUKBCDUDUEUFUGUHUI $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Neighborhoods
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d J f $.  $d g j x y $.
    $( Reverse closure of the neighborhood operation.  (This theorem depends on
       a function's value being empty outside of its domain, but it will make
       later theorems simpler to state.)  (Contributed by Zhi Wang,
       16-Sep-2024.) $)
    neircl $p |- ( N e. ( ( nei ` J ) ` S ) -> J e. Top ) $=
      ( vf vj vx vg vy cnei cfv wcel c0 wne cv wex ctop elfvne0 n0 biimpi wss
      cuni cpw wa wrex crab cmpt df-nei mptrcl exlimiv 3syl ) CABIJZJKUKLMZDNZU
      KKZDOZBPKZCAUKQULUODUKRSUNUPDEPFENZUAUBZFNGNZTUSHNTUCGUQUDHURUEUFIUMBFHGE
      UGUHUIUJ $.
  $}

  ${
    $d J x y $.  $d S x y $.  $d ch x $.  $d ph x y $.  $d ps y $.
    opnneilem.1 $e |- ( ( ph /\ x = y ) -> ( ps <-> ch ) ) $.
    $( Lemma factoring out common proof steps of ~ opnneil and ~ opnneirv .
       (Contributed by Zhi Wang, 31-Aug-2024.) $)
    opnneilem $p |- ( ph -> ( E. x e. J ( S C_ x /\ ps )
                          <-> E. y e. J ( S C_ y /\ ch ) ) ) $=
      ( cv wss wa weq wb sseq2 adantl anbi12d cbvrexdva ) AFDIZJZBKFEIZJZCKDEGA
      DELZKSUABCUBSUAMARTFNOHPQ $.
  $}

  ${
    $d J x $.
    opnneir.1 $e |- ( ph -> J e. Top ) $.
    $( If something is true for an open neighborhood, it must be true for a
       neighborhood.  (Contributed by Zhi Wang, 31-Aug-2024.) $)
    opnneir $p |- ( ph -> ( E. x e. J ( S C_ x /\ ps )
                         -> E. x e. ( ( nei ` J ) ` S ) ps ) ) $=
      ( ctop wcel cv wss wa wrex cnei wi anass opnneiss 3expib anim1d biimtrrid
      cfv reximdv2 syl ) AEGHZDCIZJZBKZCELBCDEMTTZLNFUCUFBCEUGUDEHZUFKUHUEKZBKU
      CUDUGHZBKUHUEBOUCUIUJBUCUHUEUJDEUDPQRSUAUB $.

    $d J x y $.  $d S x y $.  $d ch x $.  $d ph x y $.  $d ps y $.
    ${
      opnneirv.2 $e |- ( ( ph /\ x = y ) -> ( ps <-> ch ) ) $.
      $( A variant of ~ opnneir with different dummy variables.  (Contributed
         by Zhi Wang, 31-Aug-2024.) $)
      opnneirv $p |- ( ph -> ( E. x e. J ( S C_ x /\ ps )
                          -> E. y e. ( ( nei ` J ) ` S ) ch ) ) $=
        ( cv wss wa wrex cnei cfv opnneilem opnneir sylbid ) AFDJKBLDGMFEJKCLEG
        MCEFGNOOMABCDEFGIPACEFGHQR $.
    $}

    opnneilv.2 $e |- ( ( ph /\ y C_ x ) -> ( ps -> ch ) ) $.
    $( The converse of ~ opnneir with different dummy variables.  Note that the
       second hypothesis could be generalized by adding ` y e. J ` to the
       antecedent.  See the proof for details.  Although ` J e. Top ` might be
       redundant here (see ~ neircl ), it is listed for explicitness.
       (Contributed by Zhi Wang, 31-Aug-2024.) $)
    opnneilv $p |- ( ph -> ( E. x e. ( ( nei ` J ) ` S ) ps
                           -> E. y e. J ( S C_ y /\ ch ) ) ) $=
      ( cnei cfv wrex cv wcel wa wex wss df-rex ctop biimtrid neii2 sylan anass
      r19.41dv expl expimpd anim2d reximdv syld exlimdv ) BDFGJKKZLDMZUKNZBOZDP
      AFEMZQZCOZEGLZBDUKRAUNURDAUNUPUOULQZOZBOZEGLZURAUMBVBAUMOUTBEGAGSNUMUTEGL
      HFEGULUAUBUDUEAVAUQEGVAUPUSBOZOAUQUPUSBUCAVCCUPAUSBCIUFUGTUHUIUJT $.

    opnneil.3 $e |- ( ( ph /\ x = y ) -> ( ps <-> ch ) ) $.
    $( A variant of ~ opnneilv .  (Contributed by Zhi Wang, 31-Aug-2024.) $)
    opnneil $p  |- ( ph -> ( E. x e. ( ( nei ` J ) ` S ) ps
                          -> E. x e. J ( S C_ x /\ ps ) ) ) $=
      ( cnei cfv wrex cv wss wa opnneilv opnneilem sylibrd ) ABDFGKLLMFENOCPEGM
      FDNOBPDGMABCDEFGHIQABCDEFGJRS $.

    $( The equivalence between neighborhood and open neighborhood.  See
       ~ opnneibid2 for different dummy variables.  (Contributed by Zhi Wang,
       31-Aug-2024.) $)
    opnneibid $p |- ( ph -> ( E. x e. ( ( nei ` J ) ` S ) ps
                           <-> E. x e. J ( S C_ x /\ ps ) ) ) $=
      ( cnei cfv wrex cv wss wa opnneil opnneir impbid ) ABDFGKLLMFDNOBPDGMABCD
      EFGHIJQABDFGHRS $.

    $( The equivalence between neighborhood and open neighborhood.  A variant
       of ~ opnneibid with two dummy variables.  (Contributed by Zhi Wang,
       31-Aug-2024.) $)
    opnneibid2 $p |- ( ph -> ( E. x e. ( ( nei ` J ) ` S ) ps
                           <-> E. y e. J ( S C_ y /\ ch ) ) ) $=
      ( cnei cfv wrex cv wss wa opnneibid opnneilem bitrd ) ABDFGKLLMFDNOBPDGMF
      ENOCPEGMABCDEFGHIJQABCDEFGJRS $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Subspace topologies
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    restcls2.1 $e |- ( ph -> J e. Top ) $.
    restcls2.2 $e |- ( ph -> X = U. J ) $.
    restcls2.3 $e |- ( ph -> Y C_ X ) $.
    restcls2.4 $e |- ( ph -> K = ( J |`t Y ) ) $.
    restcls2.5 $e |- ( ph -> S e. ( Clsd ` K ) ) $.
    $( A closed set in a subspace topology is a subset of the subspace.
       (Contributed by Zhi Wang, 2-Sep-2024.) $)
    restcls2lem $p |- ( ph -> S C_ Y ) $=
      ( cuni ccld cfv wcel wss eqid cldss syl crest co ctop wceq sseqtrd unieqd
      restuni syl2anc eqtr4d sseqtrrd ) ABDLZFABDMNOBUJPKBDUJUJQRSAFCFTUAZLZUJA
      CUBOFCLZPFULUCGAFEUMIHUDFCUMUMQUFUGADUKJUEUHUI $.

    $( A closed set in a subspace topology is the closure in the original
       topology intersecting with the subspace.  (Contributed by Zhi Wang,
       2-Sep-2024.) $)
    restcls2 $p |- ( ph -> S = ( ( ( cls ` J ) ` S ) i^i Y ) ) $=
      ( ccl cfv crest co cin wcel wceq wss eqid fveq2d fveq1d ccld ctop sseqtrd
      cldcls syl cuni restcls2lem restcls syl3anc 3eqtr3d ) ABDLMZMZBCFNOZLMZMZ
      BBCLMMFPZABUMUPADUOLJUAUBABDUCMQUNBRKBDUFUGACUDQFCUHZSBFSUQURRGAFEUSIHUEA
      BCDEFGHIJKUIBCUOUSFUSTUOTUJUKUL $.

    restclsseplem.6 $e |- ( ph -> ( S i^i T ) = (/) ) $.
    ${
      restclsseplem.7 $e |- ( ph -> T C_ Y ) $.
      $( Lemma for ~ restclssep .  (Contributed by Zhi Wang, 2-Sep-2024.) $)
      restclsseplem $p |- ( ph -> ( ( ( cls ` J ) ` S ) i^i T ) = (/) ) $=
        ( cin ccl cfv c0 restcls2 ineq1d inass eqtrdi wceq sseqin2 sylib ineq2d
        wss 3eqtr3rd ) ABCOZBDPQQZGCOZOZRUJCOAUIUJGOZCOULABUMCABDEFGHIJKLSTUJGC
        UAUBMAUKCUJACGUGUKCUCNCGUDUEUFUH $.
    $}

    restclssep.7 $e |- ( ph -> T e. ( Clsd ` K ) ) $.
    $( Two disjoint closed sets in a subspace topology are separated in the
       original topology.  (Contributed by Zhi Wang, 2-Sep-2024.) $)
    restclssep $p |- ( ph -> ( ( S i^i ( ( cls ` J ) ` T ) ) = (/)
                            /\ ( ( ( cls ` J ) ` S ) i^i T ) = (/) ) ) $=
      ( cfv cin c0 wceq incom eqtr3id ccl restcls2lem restclsseplem jca ) ABCDU
      AOZOZPZQRBUEOCPQRAUGUFBPQUFBSACBDEFGHIJKNACBPBCPQBCSMTABDEFGHIJKLUBUCTABC
      DEFGHIJKLMACDEFGHIJKNUBUCUD $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Limits and continuity in topological spaces
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    cnneiima.1 $e |- ( ph -> F e. ( J Cn K ) ) $.
    cnneiima.2 $e |- ( ph -> N e. ( ( nei ` K ) ` T ) ) $.
    cnneiima.3 $e |- ( ph -> S C_ ( `' F " T ) ) $.
    $( Given a continuous function, the preimage of a neighborhood is a
       neighborhood.  To be precise, the preimage of a neighborhood of a subset
       ` T ` of the codomain of a continuous function is a neighborhood of any
       subset of the preimage of ` T ` .  (Contributed by Zhi Wang,
       9-Sep-2024.) $)
    cnneiima $p |- ( ph -> ( `' F " N ) e. ( ( nei ` J ) ` S ) ) $=
      ( cima cnei cfv wcel cnt wss syl syl2anc sspreima sstrd ccnv wfun cuni co
      ccn wf eqid ffund ctop wb cntop2 neiss2 neii1 neiint syl3anc mpbid cnntri
      cnf cntop1 wceq fimacnv sseqtrd mpbird ) ADUAZGKZBELMMNZBVEEOMMZPZABVDGFO
      MMZKZVGABVDCKZVJJADUBZCVIPZVKVJPAEUCZFUCZDADEFUEUDNZVNVODUFZHDEFVNVOVNUGZ
      VOUGZURQZUHZAGCFLMMNZVMIAFUINZCVOPZGVOPZWBVMUJAVPWCHDEFUKQZAWCWBWDWFICFGV
      OVSULRZAWCWBWEWFICFGVOVSUMRZCFGVOVSUNUOUPCVIDSRTAVPWEVJVGPHWHGDEFVOVSUQRT
      AEUINZBVNPVEVNPVFVHUJAVPWIHDEFUSQABVKVNJAVKVDVOKZVNAVLWDVKWJPWAWGCVODSRAV
      QWJVNUTVTVNVODVAQZVBTAVEWJVNAVLWEVEWJPWAWHGVODSRWKVBBEVEVNVRUNUOVC $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Topological definitions using the reals
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( Open intervals are open sets of ` II ` .  (Contributed by Zhi Wang,
     9-Sep-2024.) $)
  iooii $p |- ( ( 0 <_ A /\ B <_ 1 ) -> ( A (,) B ) e. II ) $=
    ( cc0 cle wbr c1 wa cioo wss cii wcel cxr 0xr 1xr ioossioo mpanl12 iooretop
    co cicc cvv crn ctg cfv crest ioossicc ctop w3a retop ovex restopnb mp3an12
    wb mpbii dfii2 eleqtrrdi syl ) CADEBFDEGZABHRZCFHRZIZURJKCLKFLKUQUTMNCFABOP
    UTURHUAUBUCZCFSRZUDRZJUTURVAKZURVCKZABQUSVAKZUSVBIZUTVDVEULZCFQCFUEVAUFKVBT
    KVFVGUTUGVHUHCFSUIVBUSURVATUJPUKUMUNUOUP $.

  $( Closed intervals are closed sets of ` II ` .  Note that ~ iccss ,
     ~ iccordt , and ~ ordtresticc are proved from ~ ixxss12 , ~ ordtcld3 , and
     ~ ordtrest2 , respectively.  An alternate proof uses ~ restcldi ,
     ~ dfii2 , and ~ icccld .  (Contributed by Zhi Wang, 8-Sep-2024.) $)
  icccldii $p |- ( ( 0 <_ A /\ B <_ 1 ) -> ( A [,] B ) e. ( Clsd ` II ) ) $=
    ( cc0 cle wbr c1 wa cicc co cordt cfv ccld cii cxr wss wcel iccssxr iccordt
    crest cr 0re 1re iccss mpanl12 letopuni restcldi mp3an12i dfii5 ordtresticc
    cxp cin eqtr4i fveq2i eleqtrrdi ) CADEBFDEGZABHIZDJKZCFHIZSIZLKZMLKURNOUPUQ
    LKPUOUPUROZUPUTPCFQABRCTPFTPUOVAUAUBCFABUCUDURUPUQNUEUFUGMUSLMDURURUJUKJKUS
    UHCFUIULUMUN $.

  ${
    $d A x $.
    $( ` ( 0 [,) A ) ` is open in ` II ` .  (Contributed by Zhi Wang,
       9-Sep-2024.) $)
    i0oii $p |- ( A <_ 1 -> ( 0 [,) A ) e. II ) $=
      ( vx c1 cle wbr cc0 co cmnf cioo cicc cii cr clt w3a wa cxr wi anbi1d cvv
      wcel cico cin cv anandi3r rexr lerelxr simpld 1xr xrltletr xrltle 3adant2
      brel syld mp3an3 syl2an sylbi 3com12 3expib pm4.71d 3anan32 3anass anbi2i
      imp anandi anass 3bitr3ri 3bitr2i 3bitr4g 0re elico2 sylancr elin elicc01
      bitri elioomnf syl bitrid 3bitr4rd eqrdv crn ctg crest fvex ovex iooretop
      wb cfv elrestr mp3an dfii2 eleqtrri eqeltrrdi ) ACDEZFAUAGZHAIGZFCJGZUBZK
      WMBWQWNWMBUCZLTZFWRDEZWRAMEZNZWSXAOZWSWTWRCDEZNZOZWRWNTZWRWQTZWMXCWTOXCXD
      OZWTOZXBXFWMXCXIWTWMXCXDWMWSXAXDWSWMXAXDWSWMXANWSWMOZXAWMOZOXDWSWMXAUDXKX
      LXDWSWRPTZAPTZXLXDQZWMWRUEWMXNCPTZACPPDUFULUGZXMXNXPXOUHXMXNXPNXLWRCMEZXD
      WRACUIXMXPXRXDQXNWRCUJUKUMUNUOVCUPUQURUSRWSWTXAUTXFXCWSWTXDOZOZOWSXAXSOOZ
      XJXEXTXCWSWTXDVAVBWSXAXSVDXCWTXDNXCXSOXJYAXCWTXDVAXCWTXDUTWSXAXSVEVFVGVHW
      MFLTXNXGXBWFVIXQFAWRVJVKXHWRWOTZXEOZWMXFXHYBWRWPTZOYCWRWOWPVLYDXEYBWRVMVB
      VNWMYBXCXEWMXNYBXCWFXQAWRVOVPRVQVRVSWQIVTZWAWGZWPWBGZKYFSTWPSTWOYFTWQYGTY
      EWAWCFCJWDHAWEWOWPYFSSWHWIWJWKWL $.

    $( ` ( A (,] 1 ) ` is open in ` II ` .  (Contributed by Zhi Wang,
       9-Sep-2024.) $)
    io1ii $p |- ( 0 <_ A -> ( A (,] 1 ) e. II ) $=
      ( vx cc0 cle wbr c1 co cpnf cioo cicc cii cr clt w3a wa cxr wi anbi1d cvv
      wcel cioc cin cv 0xr lerelxr brel simprd xrlelttr xrltle 3adant2 mp3an3an
      rexr syld 3impdi 3expib pm4.71d df-3an 3anass anbi2i anandi anass 3bitr2i
      imp bitr2i 3bitr4g wb 1re elioc2 sylancl elin elicc01 elioopnf syl bitrid
      bitri 3bitr4rd eqrdv crn ctg crest fvex ovex iooretop elrestr mp3an dfii2
      cfv eleqtrri eqeltrrdi ) CADEZAFUAGZAHIGZCFJGZUBZKWJBWNWKWJBUCZLTZAWOMEZW
      OFDEZNZWPWQOZWPCWODEZWRNZOZWOWKTZWOWNTZWJWTWROWTXAOZWROZWSXCWJWTXFWRWJWTX
      AWJWPWQXAWJWPWQXAWJWPOWJWQOZXACPTZWJAPTZWPWOPTZXHXAQUDWJXIXJCAPPDUEUFUGZW
      OULXIXJXKNXHCWOMEZXACAWOUHXIXKXMXAQXJCWOUIUJUMUKVCUNUOUPRWPWQWRUQXCWTWPXA
      WROZOZOWPWQXNOOZXGXBXOWTWPXAWRURUSWPWQXNUTXGWTXNOXPWTXAWRVAWPWQXNVAVDVBVE
      WJXJFLTXDWSVFXLVGAFWOVHVIXEWOWLTZXBOZWJXCXEXQWOWMTZOXRWOWLWMVJXSXBXQWOVKU
      SVOWJXQWTXBWJXJXQWTVFXLAWOVLVMRVNVPVQWNIVRZVSWGZWMVTGZKYASTWMSTWLYATWNYBT
      XTVSWACFJWBAHWCWLWMYASSWDWEWFWHWI $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Separated sets
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d ph y $.
    $( Lemma for ~ sepnsepo .  (Contributed by Zhi Wang, 1-Sep-2024.) $)
    sepnsepolem1 $p |- ( E. x e. J E. y e. J ( ph /\ ps /\ ch )
                   <-> E. x e. J ( ph /\ E. y e. J ( ps /\ ch ) ) ) $=
      ( w3a wrex wa 3anass 2rexbii r19.42v rexbii bitri ) ABCGZEFHDFHABCIZIZEFH
      ZDFHAPEFHIZDFHOQDEFFABCJKRSDFAPEFLMN $.
  $}

  ${
    $d D y z $.  $d J y z $.  $d x y z $.
    sepnsepolem2.1 $e |- ( ph -> J e. Top ) $.
    $( Open neighborhood and neighborhood is equivalent regarding disjointness.
       Lemma for ~ sepnsepo .  Proof could be shortened by 1 step using
       ~ ssdisjdr .  (Contributed by Zhi Wang, 1-Sep-2024.) $)
    sepnsepolem2 $p |- ( ph -> ( E. y e. ( ( nei ` J ) ` D ) ( x i^i y ) = (/)
                           <-> E. y e. J ( D C_ y /\ ( x i^i y ) = (/) ) ) ) $=
      ( vz ctop wcel cv cin c0 wceq cnei cfv wrex wss wb syl adantl wa id sslin
      wi sseq0 ex ineq2 eqeq1d opnneibid ) AEHIZBJZCJZKZLMZCDENOOPDULQUNUACEPRF
      UJUNUKGJZKZLMZCGDEUJUBUOULQZUNUQUDZUJURUPUMQZUSUOULUKUCUTUNUQUPUMUEUFSTUL
      UOMZUNUQRUJVAUMUPLULUOUKUGUHTUIS $.

$(
    @d D y z @.  @d J y z @.  @d ph y z @.  @d x y z @.
    @( Open neighborhood and neighborhood is equivalent regarding disjointness.
       Lemma for ~ sepnsepo .  (Contributed by Zhi Wang, 7-Sep-2024.)
       (Proof modification is discouraged.)  (New usage is discouraged.) @)
    sepnsepolem2ALT @p |- ( ph -> ( E. y e. ( ( nei ` J ) ` d ) ( x i^i y ) =
            (/) <-> E. y e. J ( d C_ y /\ ( x i^i y ) = (/) ) ) ) @=
      ( vz cv cin c0 wceq wss w3a simp2 simp3 ssdisjdr 3expia wb ineq2 eqeq1d
      adantl opnneibid ) ABHZCHZIZJKZUCGHZIZJKZCGEHDFAUGUDLZUFUIAUJUFMUGUDUCAUJ
      UFNAUJUFOPQUDUGKZUFUIRAUKUEUHJUDUGUCSTUAUB @.
$)

    $d C x y z $.  $d D x y z $.  $d J x y z $.
    $( Open neighborhood and neighborhood is equivalent regarding disjointness
       for both sides.  Namely, separatedness by open neighborhoods is
       equivalent to separatedness by neighborhoods.  (Contributed by Zhi Wang,
       1-Sep-2024.) $)
    sepnsepo $p |- ( ph ->
    ( E. x e. ( ( nei ` J ) ` C ) E. y e. ( ( nei ` J ) ` D ) ( x i^i y ) = (/)
    <-> E. x e. J E. y e. J ( C C_ x /\ D C_ y /\ ( x i^i y ) = (/) ) ) ) $=
      ( vz ctop cv cin c0 wceq cfv wrex wss wb wa rexbidv syl wcel sepnsepolem2
      cnei w3a id anbi2d wi ssrin sseq0 ex adantl simpr ineq1d eqeq1d opnneibid
      reximdv sepnsepolem1 a1i 3bitr4d ) AFIUAZBJZCJZKZLMZCEFUCNZNZOZBDVENOZDVA
      PZEVBPZVDUDCFOBFOZQGUTVIVGRZBFOVIVJVDRCFOZRZBFOZVHVKUTVLVNBFUTVGVMVIUTBCE
      FUTUEZUBUFSUTVGHJZVBKZLMZCVFOBHDFVPUTVQVAPZRVDVSCVFVTVDVSUGZUTVTVRVCPZWAV
      QVAVBUHWBVDVSVRVCUIUJTUKUPUTVAVQMZRZVDVSCVFWDVCVRLWDVAVQVBUTWCULUMUNSUOVK
      VOQUTVIVJVDBCFUQURUST $.
  $}

  ${
    sepdisj.1 $e |- ( ph -> J e. Top ) $.
    ${
      sepdisj.2 $e |- ( ph -> S C_ U. J ) $.
      sepdisj.3 $e |- ( ph -> ( ( ( cls ` J ) ` S ) i^i T ) = (/) ) $.
      $( Separated sets are disjoint.  Note that in general separatedness also
         requires ` T C_ U. J ` and ` ( S i^i ( ( cls `` J ) `` T ) ) = (/) `
         as well but they are unnecessary here.  (Contributed by Zhi Wang,
         7-Sep-2024.) $)
      sepdisj $p |- ( ph -> ( S i^i T ) = (/) ) $=
        ( ccl cfv ctop wcel cuni wss eqid sscls syl2anc ssdisjd ) ABBDHIIZCADJK
        BDLZMBRMEFBDSSNOPGQ $.
    $}

    ${
      $d J m n $.  $d S m n $.  $d T m n $.
      seposep.2 $e |- ( ph -> E. n e. J E. m e. J
              ( S C_ n /\ T C_ m /\ ( n i^i m ) = (/) ) ) $.
      $( If two sets are separated by (open) neighborhoods, then they are
         separated subsets of the underlying set.  Note that separatedness by
         open neighborhoods is equivalent to separatedness by neighborhoods.
         See ~ sepnsepo .  The relationship between separatedness and closure
         is also seen in ~ isnrm , ~ isnrm2 , ~ isnrm3 .  (Contributed by Zhi
         Wang, 7-Sep-2024.) $)
      seposep $p |- ( ph -> ( ( S C_ U. J /\ T C_ U. J )
                         /\ ( ( S i^i ( ( cls ` J ) ` T ) ) = (/)
                           /\ ( ( ( cls ` J ) ` S ) i^i T ) = (/) ) ) ) $=
        ( wcel cv wss cin c0 wceq wa cfv syl2anc sstrd cdif sylc ctop wrex cuni
        w3a ccl simp31 simp1 simp2l eqid simp32 simp2r ccld opncld incom simp33
        eltopss eqtr3id reldisj biimpd clsss2 disjdif ssdisjdr disjdifr ssdisjd
        sscond a1i jca jca31 3exp rexlimdvv ) AFUAIZBEJZKZCDJZKZVLVNLZMNZUDZDFU
        BEFUBBFUCZKZCVSKZOBCFUEPZPZLMNZBWBPZCLMNZOZOZGHVKVRWHEDFFVKVLFIZVNFIZOZ
        VRWHVKWKVRUDZVTWAWGWLBVLVSVKWKVMVOVQUFZWLVKWIVLVSKZVKWKVRUGZVKWIWJVRUHZ
        VLFVSVSUIZUPQZRWLCVNVSVKWKVMVOVQUJZWLVKWJVNVSKZWOVKWIWJVRUKZVNFVSWQUPQZ
        RWLWDWFWLWCVSBSZBWLWCVSVLSZXCWLXDFULPZIZCXDKWCXDKWLVKWIXFWOWPVLFVSWQUMQ
        WLCVNXDWSWLWTVNVLLZMNZVNXDKZXBWLXGVPMVLVNUNVKWKVMVOVQUOZUQWTXHXIVNVLVSU
        RUSTRXDCFVSWQUTQWLBVLVSWMVERBXCLMNWLBVSVAVFVBWLWEVSCSZCWLWEVSVNSZXKWLXL
        XEIZBXLKWEXLKWLVKWJXMWOXAVNFVSWQUMQWLBVLXLWMWLWNVQVLXLKZWRXJWNVQXNVLVNV
        SURUSTRXLBFVSWQUTQWLCVNVSWSVERXKCLMNWLCVSVCVFVDVGVHVIVJT $.
    $}

    ${
      $d J m n $.  $d S m n $.  $d T m n $.
      sepcsepo.2 $e |- ( ph ->
      E. n e. ( ( nei ` J ) ` S ) E. m e. ( ( nei ` J ) ` T )
      ( n e. ( Clsd ` J ) /\ m e. ( Clsd ` J ) /\ ( n i^i m ) = (/) ) ) $.
      $( If two sets are separated by closed neighborhoods, then they are
         separated by (open) neighborhoods.  See ~ sepnsepo for the equivalence
         between separatedness by open neighborhoods and separatedness by
         neighborhoods.  Although ` J e. Top ` might be redundant here, it is
         listed for explicitness. ` J e. Top ` can be obtained from ~ neircl ,
         ~ adantr , and ~ rexlimiva .  (Contributed by Zhi Wang,
         8-Sep-2024.) $)
      sepcsepo $p |- ( ph -> E. n e. J E. m e. J
              ( S C_ n /\ T C_ m /\ ( n i^i m ) = (/) ) ) $=
        ( cv cin c0 wceq cnei cfv wrex wss w3a ccld wcel reximi simp3 syl mpbid
        sepnsepo ) AEIZDIZJKLZDCFMNZNZOZEBUHNZOZBUEPCUFPUGQDFOEFOAUEFRNZSZUFUMS
        ZUGQZDUIOZEUKOULHUQUJEUKUPUGDUIUNUOUGUATTUBAEDBCFGUDUC $.
    $}
  $}

  ${
    $d J f m n $.  $d S f n $.  $d T f m n $.
    sepfsepc.1 $e |- ( ph -> E. f e. ( J Cn II )
              ( S C_ ( `' f " { 0 } ) /\ T C_ ( `' f " { 1 } ) ) ) $.
    $( If two sets are separated by a continuous function, then they are
       separated by closed neighborhoods.  (Contributed by Zhi Wang,
       9-Sep-2024.) $)
    sepfsepc $p |- ( ph ->
      E. n e. ( ( nei ` J ) ` S ) E. m e. ( ( nei ` J ) ` T )
      ( n e. ( Clsd ` J ) /\ m e. ( Clsd ` J ) /\ ( n i^i m ) = (/) ) ) $=
      ( cc0 wss c1 wa cii co cfv wcel wceq c3 wbr mp2an vg vh ccnv csn cima ccn
      cv wrex ccld cin c0 w3a cnei cdiv cicc c2 simpl cle 0re 1re 0le0 3re 3ne0
      cr rereccli clt 1lt3 recgt1i simpri ltleii iccss mp4an i0oii ax-mp simpli
      cico cxr wb rexri elico2 biimpri snssd mp3an icossicc sseq2 sseq1 anbi12d
      pm3.2i rspcev ctop iitop sstri iiuni mpbir2an a1i simprl cnneiima halfge0
      isnei 1le1 halflt1 halfre elioc2 iocssicc simprr icccldii cnclima sylancl
      cioc io1ii wfun cuni eqid cnf syl 0xr 1xr 2lt3 2re 2pos 3pos ltrecii mpbi
      ffund iccdisj2 ssidd predisj eleq1 ineq1 eqeq1d 3anbi13d 3anbi23d rspc2ev
      ineq2 syl113anc rexlimiva ) ABDUGZUCZIUDZUEJZCYRKUDZUEJZLZDGMUFNZUHFUGZGU
      IOZPZEUGZUUFPZUUEUUHUJZUKQZULZECGUMOZOZUHFBUUMOZUHZHUUCUUPDUUDYQUUDPZUUCL
      ZYRIKRUNNZUONZUEZUUOPYRKUPUNNZKUONZUEZUUNPUVAUUFPZUVDUUFPZUVAUVDUJZUKQZUU
      PUURBYSYQGMUUTUUQUUCUQZUUTYSMUMOZOPZUURUVKUUTIKUONZJZYSUAUGZJZUVNUUTJZLZU
      AMUHZIVDPZKVDPZIIURSZUUSKURSZUVMUSUTVAUUSKRVBVCVEZUTIUUSVFSZUUSKVFSZRVDPK
      RVFSUWDUWELVBVGRVHTZVIVJZIKIUUSVKVLZIUUSVPNZMPZYSUWIJZUWIUUTJZLZUVRUWBUWJ
      UWGUUSVMVNUWKUWLUVSUWAUWDUWKUSVAUWDUWEUWFVOUVSUWAUWDULZIUWIIUWIPZUWNUVSUU
      SVQPUWOUWNVRUSUUSUWCVSIUUSIVTTWAWBWCZIUUSWDZWHUVQUWMUAUWIMUVNUWIQUVOUWKUV
      PUWLUVNUWIYSWEUVNUWIUUTWFWGWITMWJPZYSUVLJUVKUVMUVRLVRWKYSUUTUVLYSUWIUUTUW
      PUWQWLUWHWLYSUAMUUTUVLWMWSTWNWOUUQYTUUBWPWQUURCUUAYQGMUVCUVIUVCUUAUVJOPZU
      URUWSUVCUVLJZUUAUBUGZJZUXAUVCJZLZUBMUHZUVSUVTIUVBURSZKKURSZUWTUSUTWRWTIKU
      VBKVKVLZUVBKXINZMPZUUAUXIJZUXIUVCJZLZUXEUXFUXJWRUVBXJVNUXKUXLUVTUVBKVFSZU
      XGUXKUTXAWTUVTUXNUXGULZKUXIKUXIPZUXOUVBVQPUVTUXPUXOVRUVBXBVSUTUVBKKXCTWAW
      BWCZUVBKXDZWHUXDUXMUBUXIMUXAUXIQUXBUXKUXCUXLUXAUXIUUAWEUXAUXIUVCWFWGWITUW
      RUUAUVLJUWSUWTUXELVRWKUUAUVCUVLUUAUXIUVCUXQUXRWLUXHWLUUAUBMUVCUVLWMWSTWNW
      OUUQYTUUBXEWQUURUUQUUTMUIOZPZUVEUVIUWAUWBUXTVAUWGIUUSXFTUUTYQGMXGXHUURUUQ
      UVCUXSPZUVFUVIUXFUXGUYAWRWTUVBKXFTUVCYQGMXGXHUURUUTUVCUVAUVDYQUURUUQYQXKU
      VIUUQGXLZUVLYQYQGMUYBUVLUYBXMWMXNYDXOUUTUVCUJUKQZUURIVQPKVQPUUSUVBVFSZUYC
      XPXQUPRVFSUYDXRUPRXSVBXTYAYBYCIUUSUVBKYEWCWOUURUVAYFUURUVDYFYGUULUVEUVFUV
      HULUVEUUIUVAUUHUJZUKQZULFEUVAUVDUUOUUNUUEUVAQZUUGUVEUUKUYFUUIUUEUVAUUFYHU
      YGUUJUYEUKUUEUVAUUHYIYJYKUUHUVDQZUUIUVFUYFUVHUVEUUHUVDUUFYHUYHUYEUVGUKUUH
      UVDUVAYNYJYLYMYOYPXO $.
  $}

  ${
    seppsepf.1 $e |- ( ph -> E. f e. ( J Cn II )
              ( S = ( `' f " { 0 } ) /\ T = ( `' f " { 1 } ) ) ) $.
    $( If two sets are precisely separated by a continuous function, then they
       are separated by the continuous function.  (Contributed by Zhi Wang,
       9-Sep-2024.) $)
    seppsepf $p |- ( ph -> E. f e. ( J Cn II )
              ( S C_ ( `' f " { 0 } ) /\ T C_ ( `' f " { 1 } ) ) ) $=
      ( cv ccnv cc0 csn cima wceq c1 wa cii ccn co wrex wss eqimss anim12i syl
      reximi ) ABDGHZIJKZLZCUDMJKZLZNZDEOPQZRBUESZCUGSZNZDUJRFUIUMDUJUFUKUHULBU
      ETCUGTUAUCUB $.

    $d J f $.  $d S f $.  $d T f $.
    $( If two sets are precisely separated by a continuous function, then they
       are closed.  An alternate proof involves ` II e. Fre ` .  (Contributed
       by Zhi Wang, 9-Sep-2024.) $)
    seppcld $p |- ( ph -> ( S e. ( Clsd ` J ) /\ T e. ( Clsd ` J ) ) ) $=
      ( cc0 csn cima wceq c1 wa cii co ccld cfv wcel cicc cle wbr ccnv ccn wrex
      cv simprl simpl cxr iccid ax-mp 0le0 0le1 icccldii mp2an eqeltrri cnclima
      0xr sylancl eqeltrd simprr 1xr 1le1 jca rexlimiva syl ) ABDUDZUAZGHZIZJZC
      VFKHZIZJZLZDEMUBNZUCBEOPZQZCVOQZLZFVMVRDVNVEVNQZVMLZVPVQVTBVHVOVSVIVLUEVT
      VSVGMOPZQVHVOQVSVMUFZGGRNZVGWAGUGQWCVGJUPGUHUIGGSTGKSTZWCWAQUJUKGGULUMUNV
      GVEEMUOUQURVTCVKVOVSVIVLUSVTVSVJWAQVKVOQWBKKRNZVJWAKUGQWEVJJUTKUHUIWDKKST
      WEWAQUKVAKKULUMUNVJVEEMUOUQURVBVCVD $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Separated spaces: T0, T1, T2 (Hausdorff) ...
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d J c d x y $.
    $( A topological space is normal iff any two disjoint closed sets are
       separated by neighborhoods.  (Contributed by Zhi Wang, 1-Sep-2024.) $)
    isnrm4 $p |- ( J e. Nrm <-> ( J e. Top /\ A. c e. ( Clsd ` J ) A. d e. (
    Clsd ` J ) ( ( c i^i d ) = (/) -> E. x e. ( ( nei ` J ) ` c ) E. y e. ( (
    nei ` J ) ` d ) ( x i^i y ) = (/) ) ) ) $=
      ( cnrm wcel ctop cv cin c0 wceq wss w3a wrex wi ccld cfv wral wa sepnsepo
      cnei isnrm3 id imbi2d 2ralbidv pm5.32i bitr4i ) CFGCHGZDIZEIZJKLZUJAIZMUK
      BIZMUMUNJKLZNBCOACOZPZECQRZSDURSZTUIULUOBUKCUBRZROAUJUTROZPZEURSDURSZTABC
      DEUCUIVCUSUIVBUQDEURURUIVAUPULUIABUJUKCUIUDUAUEUFUGUH $.
  $}

  ${
    $d c d j x y $.
    $( A topological space is normal if any disjoint closed sets can be
       separated by open neighborhoods.  An alternate definition of ~ df-nrm .
       (Contributed by Zhi Wang, 30-Aug-2024.) $)
    dfnrm2 $p |- Nrm = { j e. Top | A. c e. ( Clsd ` j ) A. d e. ( Clsd ` j )
                 ( ( c i^i d ) = (/) -> E. x e. j E. y e. j ( c C_ x /\ d C_ y
                 /\ ( x i^i y ) = (/) ) ) } $=
      ( cnrm cv ctop wcel cin c0 wceq wss w3a wrex wi ccld cfv wral wa cab crab
      isnrm3 eqabi df-rab eqtr4i ) FCGZHIDGZEGZJKLUHAGZMUIBGZMUJUKJKLNBUGOAUGOP
      EUGQRZSDULSZTZCUAUMCHUBUNCFABUGDEUCUDUMCHUEUF $.

    $( A topological space is normal if any disjoint closed sets can be
       separated by neighborhoods.  An alternate definition of ~ df-nrm .
       (Contributed by Zhi Wang, 2-Sep-2024.) $)
    dfnrm3 $p |- Nrm = { j e. Top | A. c e. ( Clsd ` j ) A. d e. ( Clsd ` j )
    ( ( c i^i d ) = (/) -> E. x e. ( ( nei ` j ) ` c ) E. y e. ( ( nei ` j ) `
    d ) ( x i^i y ) = (/) ) } $=
      ( cnrm cv ctop wcel cin c0 wceq cnei cfv wrex wi ccld wral wa cab isnrm4
      crab eqabi df-rab eqtr4i ) FCGZHIDGZEGZJKLAGBGJKLBUHUFMNZNOAUGUINOPEUFQNZ
      RDUJRZSZCTUKCHUBULCFABUFDEUAUCUKCHUDUE $.
  $}

  ${
    $d J x $.
    $( Lemma for ~ iscnrm3 .  Subspace topology is a topology.  (Contributed by
       Zhi Wang, 3-Sep-2024.) $)
    iscnrm3lem1 $p |- ( J e. Top -> ( A. x e. A ph
                <-> A. x e. A ( ( J |`t x ) e. Top /\ ph ) ) ) $=
      ( ctop wcel cv crest co wa resttop biantrurd ralbidva ) DEFZADBGZHIEFZAJB
      CNOCFJPAODCKLM $.
  $}

  ${
    $d A v w y z $.  $d B v w z $.  $d C v w $.  $d D v x y z $.  $d E x y z $.
    $d ch x y z $.  $d ph v w x y z $.  $d ps v w $.
    iscnrm3lem2.1 $e |- ( ph -> ( A. x e. A A. y e. B A. z e. C ps
                                  -> ( ( w e. D /\ v e. E ) -> ch ) ) ) $.
    iscnrm3lem2.2 $e |- ( ph -> ( A. w e. D A. v e. E ch
                             -> ( ( x e. A /\ y e. B /\ z e. C ) -> ps ) ) ) $.
    $( Lemma for ~ iscnrm3 proving a biconditional on restricted universal
       quantifications.  (Contributed by Zhi Wang, 3-Sep-2024.) $)
    iscnrm3lem2 $p |- ( ph -> ( A. x e. A A. y e. B A. z e. C ps
                            <-> A. w e. D A. v e. E ch ) ) $=
      ( cv wcel wi wal wral w3a 2ax5 r3al biimtrrid 2alimdv syl5 alrimiv alimdv
      wa r2al impbid 3bitr4g ) ADPIQEPJQFPKQUABRZFSESZDSZGPLQHPMQUICRZHSGSZBFKT
      EJTDITZCHMTGLTZAUOUQUOUOHSGSAUQUOGHUBAUOUPGHUOURAUPBDEFIJKUCZNUDUEUFUQUQF
      SESZDSAUOUQVADUQEFUBUGAVAUNDAUQUMEFUQUSAUMCGHLMUJZOUDUEUHUFUKUTVBUL $.
  $}

  ${
    iscnrm3lem4.1 $e |- ( et -> ( ps -> ze ) ) $.
    iscnrm3lem4.2 $e |- ( ( ph /\ ch /\ th ) -> et ) $.
    iscnrm3lem4.3 $e |- ( ( ph /\ ch /\ th ) -> ( ze -> ta ) ) $.
    $( Lemma for ~ iscnrm3lem5 and ~ iscnrm3r .  (Contributed by Zhi Wang,
       4-Sep-2024.) $)
    iscnrm3lem4 $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $=
      ( wa w3a 4anpull2 wi syl syld imp sylbi exp43 ) ABCDEABKCDKKACDLZBKEABCDM
      TBETBGETFBGNIHOJPQRS $.
  $}

  ${
    $d S x y $.  $d T x y $.  $d V x y $.  $d W x y $.  $d ps x y $.
    $d th x y $.
    iscnrm3lem5.1 $e |- ( ( x = S /\ y = T ) -> ( ph <-> ps ) ) $.
    iscnrm3lem5.2 $e |- ( ( x = S /\ y = T ) -> ( ch <-> th ) ) $.
    iscnrm3lem5.3 $e |- ( ( ta /\ et /\ ze ) -> ( S e. V /\ T e. W ) ) $.
    iscnrm3lem5.4 $e |- ( ( ta /\ et /\ ze ) -> ( ( ps -> th ) -> si ) ) $.
    $( Lemma for ~ iscnrm3l .  (Contributed by Zhi Wang, 3-Sep-2024.) $)
    iscnrm3lem5 $p |- ( ta -> ( A. x e. V A. y e. W ( ph -> ch )
                            -> ( et -> ( ze -> si ) ) ) ) $=
      ( wi wral wcel wa cv wceq imbi12d rspc2gv iscnrm3lem4 ) EACSZJNTIMTFGHKMU
      ALNUAUBBDSZUHUIIJKLMNIUCKUDJUCLUDUBABCDOPUEUFQRUG $.
  $}

$(
  @{
    iscnrm3lem99.1 @e |- ( x = A -> ( ps <-> et ) ) @.
    iscnrm3lem99.2 @e |- ( y = B -> ( et <-> ze ) ) @.
    iscnrm3lem99.3 @e |- ( z = C -> ( ze <-> si ) ) @.
    iscnrm3lem99.4 @e |- ( ( ph /\ ch /\ th ) ->
                        ( A e. R /\ B e. S /\ C e. T ) ) @.
    iscnrm3lem99.5 @e |- ( ( ph /\ ch /\ th ) -> ( si -> ta ) ) @.
    @( Lemma for ~ iscnrm3 .  (Contributed by Zhi Wang, XX-Sep-2024.) @)
    iscnrm3lem99 @p |- ( ph -> ( A. x e. R A. y e. S A. z e. T ps
            -> ( ch -> ( th -> ta ) ) ) ) @=
       ? @.
  @}
$)

  ${
    $d V y $.  $d ch x y $.  $d ph x y $.
    iscnrm3lem6.1 $e |- ( ( ph /\ ( x e. V /\ y e. W ) /\ ps ) -> ch ) $.
    $( Lemma for ~ iscnrm3lem7 .  (Contributed by Zhi Wang, 5-Sep-2024.) $)
    iscnrm3lem6 $p |- ( ph -> ( E. x e. V E. y e. W ps -> ch ) ) $=
      ( cv wcel wa 3exp rexlimdvv ) ABCDEFGADIFJEIGJKBCHLM $.
  $}

  ${
    $d A y $.  $d C x y z $.  $d D w x y z $.  $d W w $.  $d Z w z $.
    $d ch x y $.  $d ph x y $.  $d ta w $.  $d th z $.
    iscnrm3lem7.1 $e |- ( z = Z -> ( ch <-> th ) ) $.
    iscnrm3lem7.2 $e |- ( w = W -> ( th <-> ta ) ) $.
    iscnrm3lem7.3 $e |- ( ( ph /\ ( x e. A /\ y e. B ) /\ ps )
                  -> ( Z e. C /\ W e. D /\ ta ) ) $.
    $( Lemma for ~ iscnrm3rlem8 and ~ iscnrm3llem2 involving restricted
       existential quantifications.  (Contributed by Zhi Wang, 5-Sep-2024.) $)
    iscnrm3lem7 $p |- ( ph -> ( E. x e. A E. y e. B ps
                                 -> E. z e. C E. w e. D ch ) ) $=
      ( wrex wcel cv wa w3a rspc2ev syl iscnrm3lem6 ) ABCIMSHLSZFGJKAFUAJTGUAKT
      UBBUCOLTNMTEUCUGRCEDHIONLMPQUDUEUF $.
  $}

$(
  @( All subspaces are normal iff in the original topology two separated sets
     can be separated by open neighborhoods.  (Contributed by Zhi Wang,
     XX-Sep-2024.) @)
    restnrmsep @p |- ( J e. Top -> ( ( ( Y e. ~P U. J /\ C e. ( Clsd ` ( J |`t
    Y ) ) /\ D e. ( Clsd ` ( J |`t Y ) ) ) -> ( ( C i^i D ) = (/) -> E. n e. (
    J |`t Y ) E. m e. ( J |`t Y ) ( C C_ n /\ D C_ m /\ ( n i^i m ) = (/) ) ) )
    <-> ( ( S e. ~P U. J /\ T e. ~P U. J ) -> ( ( ( S i^i ( ( cls ` J ) ` T ) )
    = (/) /\ ( ( ( cls ` J ) ` S ) i^i T ) = (/) ) -> E. n e. J E. m e. J ( S
    C_ n /\ T C_ m /\ ( n i^i m ) = (/) ) ) ) ) ) @=
    ? @.
$)

$(
  @{
    @d J c d m n x y z @.
    iscnrm3OLD.1 @e  |- ( J e. Top -> ( ( ( z e. ~P U. J /\ c e. ( Clsd ` ( J
                        |`t z ) ) /\ d e. ( Clsd ` ( J |`t z ) ) ) -> ( ( c i^i
                        d ) = (/) -> E. n e. ( J |`t z ) E. m e. ( J |`t z ) (
                        c C_ n /\ d C_ m /\ ( n i^i m ) = (/) ) ) ) <-> ( ( x
                        e. ~P U. J /\ y e. ~P U. J ) -> ( ( ( x i^i ( ( cls ` J
                        ) ` y ) ) = (/) /\ ( ( ( cls ` J ) ` x ) i^i y ) = (/)
                        ) -> E. n e. J E. m e. J ( x C_ n /\ y C_ m /\ ( n i^i
                        m ) = (/) ) ) ) ) ) @.
    @( A completely normal topology is a topology in which two separated sets
       can be separated by open neighborhoods.  (Contributed by Zhi Wang,
       3-Sep-2024.)  (Proof modification is discouraged.)
       (New usage is discouraged.) @)
    iscnrm3OLD @p |- ( J e. CNrm <->
            ( J e. Top /\ A. x e. ~P U. J A. y e. ~P U. J
    ( ( ( x i^i ( ( cls ` J ) ` y ) ) = (/) /\ ( ( ( cls ` J ) ` x ) i^i y ) =
    (/) ) -> E. n e. J E. m e. J ( x C_ n /\ y C_ m /\ ( n i^i m ) = (/) ) ) )
    ) @=
      ( wcel cv wral wa cfv cin c0 wceq wss wal 19.3v ccnrm ctop crest cnrm cpw
      cuni ccl w3a wrex eqid iscnrm ccld iscnrm3lem1 isnrm3 ralbii bitr4di r3al
      co bitri 2albidv r2al bitr3id albidv bitrid 3bitri bitrdi bitr3d pm5.32i
      wi ) FUAJFUBJZFCKZUCURZUDJZCFUFZUEZLZMVJAKZBKZFUGNZNOPQVQVSNVROPQMVQEKZRV
      RDKZRVTWAOPQZUHDFUIEFUIVIZBVOLAVOLZMCFVNVNUJUKVJVPWDVJGKZHKZOPQWEVTRWFWAR
      WBUHDVLUIEVLUIVIZHVLULNZLGWHLZCVOLZVPWDVJWJVLUBJWIMZCVOLVPWICVOFUMVMWKCVO
      EDVLGHUNUOUPVJWJWDHSZGSZCSZWDWJVKVOJWEWHJWFWHJUHWGVIZHSGSZCSVJWNWGCGHVOWH
      WHUQVJWPWMCVJWOWDGHWOWOBSZASZVJWDWRWQWOWQATWOBTUSVJWRVQVOJVRVOJMWCVIZBSAS
      WDVJWOWSABIUTWCABVOVOVAUPVBUTVCVDWNWMWLWDWMCTWLGTWDHTVEVFVGVHUS @.
  @}
$)

  ${
    iscnrm3rlem1.1 $e |- ( ph -> S C_ X ) $.
    $( Lemma for ~ iscnrm3rlem2 .  The hypothesis could be generalized to
       ` ( ph -> ( S \ T ) C_ X ) ` .  (Contributed by Zhi Wang,
       5-Sep-2024.) $)
    iscnrm3rlem1 $p |- ( ph -> ( S \ T ) = ( S i^i ( X \ ( S i^i T ) ) ) ) $=
      ( cin cdif cun difindi ineq2i indi disjdif uneq1i 0un indif2 3eqtri dfss2
      c0 wss wceq sylib difeq1d eqtr2id ) ABDBCFGZFZBDFZCGZBCGUEBDBGZDCGZHZFBUH
      FZBUIFZHZUGUDUJBDBCIJBUHUIKUMRULHULUGUKRULBDLMULNBDCOPPAUFBCABDSUFBTEBDQU
      AUBUC $.
  $}

  ${
    $d J c $.  $d S c $.  $d T c $.
    iscnrm3rlem2.1 $e |- ( ph -> J e. Top ) $.
    iscnrm3rlem2.2 $e |- ( ph -> S C_ U. J ) $.
    $( Lemma for ~ iscnrm3rlem3 .  (Contributed by Zhi Wang, 5-Sep-2024.) $)
    iscnrm3rlem2 $p |- ( ph -> ( ( ( cls ` J ) ` S ) \ T ) e. ( Clsd ` ( J |`t
                       ( U. J \ ( ( ( cls ` J ) ` S ) i^i T ) ) ) ) ) $=
      ( vc ccl cfv cdif cuni cin crest co ccld wcel cv wceq wss syl2anc wrex wa
      ctop eqid clscld clsss3 iscnrm3rlem1 ineq1 rspceeqv difss restcld sylancl
      wb mpbird ) ABDHIIZCJZDDKZUOCLZJZMNOIPZUPGQZUSLZRGDOIZUAZADUCPZBUQSZVDEFV
      EVFUBZUOVCPUPUOUSLZRVDBDUQUQUDZUEVGUOCUQBDUQVIUFUGGUOVCVBVHUPVAUOUSUHUITT
      AVEUSUQSUTVDUMEUQURUJGUPUSDUQVIUKULUN $.
  $}

  $( Lemma for ~ iscnrm3r .  The designed subspace is a subset of the original
     set; the two sets are closed sets in the subspace.  (Contributed by Zhi
     Wang, 5-Sep-2024.) $)
  iscnrm3rlem3 $p |- ( ( J e. Top /\ ( S e. ~P U. J /\ T e. ~P U. J ) ) -> ( (
  U. J \ ( ( ( cls ` J ) ` S ) i^i ( ( cls ` J ) ` T ) ) ) e. ~P U. J /\ ( ( (
  cls ` J ) ` S ) \ ( ( cls ` J ) ` T ) ) e. ( Clsd ` ( J |`t ( U. J \ ( ( (
  cls ` J ) ` S ) i^i ( ( cls ` J ) ` T ) ) ) ) ) /\ ( ( ( cls ` J ) ` T ) \ (
  ( cls ` J ) ` S ) ) e. ( Clsd ` ( J |`t ( U. J \ ( ( ( cls ` J ) ` S ) i^i (
  ( cls ` J ) ` T ) ) ) ) ) ) ) $=
    ( ctop wcel cuni cpw wa ccl cfv cin cdif crest co ccld uniexg difssd elpwid
    cvv iscnrm3rlem2 sselpwd adantr simpl simprl simprr incom difeq2i eleqtrrdi
    oveq2i fveq2i 3jca ) CDEZACFZGZEZBUNEZHZHZUMACIJZJZBUSJZKZLZUNEZUTVALCVCMNZ
    OJZEVAUTLZVFEULVDUQULVCUMSCDPULUMVBQUAUBURAVACULUQUCZURAUMULUOUPUDRTURVGCUM
    VAUTKZLZMNZOJVFURBUTCVHURBUMULUOUPUERTVEVKOVCVJCMVBVIUMUTVAUFUGUIUJUHUK $.

  ${
    iscnrm3rlem4.1 $e |- ( ph -> J e. Top ) $.
    iscnrm3rlem4.2 $e |- ( ph -> S C_ U. J ) $.
    ${
      iscnrm3rlem4.3 $e |- ( ph -> ( S i^i T ) = (/) ) $.
      iscnrm3rlem4.4 $e |- ( ph -> ( ( ( cls ` J ) ` S ) \ T ) C_ N ) $.
      $( Lemma for ~ iscnrm3rlem8 .  Given two disjoint subsets ` S ` and ` T `
         of the underlying set of a topology ` J ` , if ` N ` is a superset of
         ` ( ( ( cls `` J ) `` S ) \ T ) ` , then it is a superset of ` S ` .
         (Contributed by Zhi Wang, 5-Sep-2024.) $)
      iscnrm3rlem4 $p |- ( ph -> S C_ N ) $=
        ( ccl cfv cdif cin wceq wss indifdi a1i c0 difeq2d dfss2 dif0 ctop wcel
        eqtrdi cuni eqid sscls syl2anc sylib 3eqtrd sylibr sstrd ) ABBDJKKZCLZE
        ABUNMZBNBUNOAUOBUMMZBCMZLZUPBUOURNABUMCPQAURUPRLUPAUQRUPHSUPUAUDABUMOZU
        PBNADUBUCBDUEZOUSFGBDUTUTUFUGUHBUMTUIUJBUNTUKIUL $.
    $}

    iscnrm3rlem5.3 $e |- ( ph -> T C_ U. J ) $.
    $( Lemma for ~ iscnrm3rlem6 .  (Contributed by Zhi Wang, 5-Sep-2024.) $)
    iscnrm3rlem5 $p |- ( ph -> ( U. J \ ( ( ( cls ` J ) ` S )
                      i^i ( ( cls ` J ) ` T ) ) ) e. J ) $=
      ( ccl cfv cin ccld wcel cuni cdif ctop wss eqid clscld syl2anc incld syl
      cldopn ) ABDHIZIZCUCIZJZDKIZLZDMZUFNDLAUDUGLZUEUGLZUHADOLZBUIPUJEFBDUIUIQ
      ZRSAULCUIPUKEGCDUIUMRSUDUEDTSUFDUIUMUBUA $.

    ${
      iscnrm3rlem6.4 $e |- ( ph -> O C_ ( U. J \ ( ( ( cls ` J ) ` S )
                                   i^i ( ( cls ` J ) ` T ) ) ) ) $.
      $( Lemma for ~ iscnrm3rlem7 .  (Contributed by Zhi Wang, 5-Sep-2024.) $)
      iscnrm3rlem6 $p |- ( ph -> ( O e. ( J |`t ( U. J \ ( ( ( cls ` J ) ` S )
                           i^i ( ( cls ` J ) ` T ) ) ) ) <-> O e. J ) ) $=
        ( cuni ccl cfv cin cdif crest co wcel wss ctop wa iscnrm3rlem5 restopn2
        wb syl2anc mpbiran2d ) AEDDJBDKLZLCUFLMNZOPQZEDQZEUGRZIADSQUGDQUHUIUJTU
        CFABCDFGHUAUGEDUBUDUE $.
    $}

    iscnrm3rlem7.4 $e |- ( ph -> O e. ( J |`t ( U. J \ ( ( ( cls ` J ) ` S )
                           i^i ( ( cls ` J ) ` T ) ) ) ) ) $.
    $( Lemma for ~ iscnrm3rlem8 .  Open neighborhoods in the subspace topology
       are open neighborhoods in the original topology given that the subspace
       is an open set in the original topology.  (Contributed by Zhi Wang,
       5-Sep-2024.) $)
    iscnrm3rlem7 $p |- ( ph -> O e. J ) $=
      ( cuni ccl cfv cin cdif wcel ctop wss cvv syl2anc eqid co resttop eltopss
      crest uniexd difexd wceq difssd restuni sseqtrrd iscnrm3rlem6 mpbid ) AED
      DJZBDKLZLCUNLMZNZUDUAZOZEDOIABCDEFGHAEUQJZUPAUQPOZUREUSQADPOZUPROUTFAUMUO
      RADPFUEUFUPDRUBSIEUQUSUSTUCSAVAUPUMQUPUSUGFAUMUOUHUPDUMUMTUISUJUKUL $.
  $}

  ${
    $d J k l m n $.  $d S k l m n $.  $d T k l m n $.
    $( Lemma for ~ iscnrm3r .  Disjoint open neighborhoods in the subspace
       topology are disjoint open neighborhoods in the original topology given
       that the subspace is an open set in the original topology.  Therefore,
       given any two sets separated in the original topology and separated by
       open neighborhoods in the subspace topology, they must be separated by
       open neighborhoods in the original topology.  (Contributed by Zhi Wang,
       5-Sep-2024.) $)
    iscnrm3rlem8 $p |- ( ( J e. Top /\ ( S e. ~P U. J /\ T e. ~P U. J ) /\
    ( ( S i^i ( ( cls ` J ) ` T ) ) = (/) /\ ( ( ( cls ` J ) ` S ) i^i T )
    = (/) ) ) -> ( E. l e. ( J |`t ( U. J \ ( ( ( cls ` J ) ` S ) i^i
    ( ( cls ` J ) ` T ) ) ) ) E. k e. ( J |`t ( U. J \ ( ( ( cls ` J ) ` S )
    i^i ( ( cls ` J ) ` T ) ) ) ) ( ( ( ( cls ` J ) ` S ) \ ( ( cls ` J )
    ` T ) ) C_ l /\ ( ( ( cls ` J ) ` T ) \ ( ( cls ` J ) ` S ) ) C_ k
    /\ ( l i^i k ) = (/) ) -> E. n e. J E. m e. J ( S C_ n /\ T C_ m /\
    ( n i^i m ) = (/) ) ) ) $=
      ( wcel wa cfv cin c0 wceq w3a cdif cv wss sseq2 eqeq1d elpwid ctop cpw co
      cuni ccl crest ineq1 3anbi13d ineq2 3anbi23d simp12l simp12r iscnrm3rlem7
      simp11 simp2l simp2r simp13l simp31 iscnrm3rlem4 incom simp32 simp33 3jca
      simp13r eqtr3id iscnrm3lem7 ) FUAHZAFUDZUBZHZBVIHZIZABFUEJZJZKLMZAVMJZBKZ
      LMZIZNZVPVNOGPZQZVNVPOCPZQZWAWCKZLMZNZAEPZQZBDPZQZWHWJKZLMZNAWAQZWKWAWJKZ
      LMZNWNBWCQZWFNZGCEDFVHVPVNKOUFUCZWSFFWCWAWHWAMZWIWNWMWPWKWHWAARWTWLWOLWHW
      AWJUGSUHWJWCMZWKWQWPWFWNWJWCBRXAWOWELWJWCWAUISUJVTWAWSHZWCWSHZIZWGNZWAFHW
      CFHWRXEABFWAVGVLVSXDWGUNZXEAVHVJVKVGVSXDWGUKTZXEBVHVJVKVGVSXDWGULTZVTXBXC
      WGUOUMXEABFWCXFXGXHVTXBXCWGUPUMXEWNWQWFXEAVNFWAXFXGVOVRVGVLXDWGUQVTXDWBWD
      WFURUSXEBVPFWCXFXHXEBVPKVQLVPBUTVOVRVGVLXDWGVDVEVTXDWBWDWFVAUSVTXDWBWDWFV
      BVCVCVF $.

    $d J c d k l z $.  $d S c d k l z $.  $d T c d k l z $.
    $( Lemma for ~ iscnrm3 .  If all subspaces of a topology are normal, i.e.,
       two disjoint closed sets can be separated by open neighborhoods, then in
       the original topology two separated sets can be separated by open
       neighborhoods.  (Contributed by Zhi Wang, 5-Sep-2024.) $)
    iscnrm3r $p |- ( J e. Top -> ( A. z e. ~P U. J A. c e. ( Clsd ` ( J |`t z )
    ) A. d e. ( Clsd ` ( J |`t z ) ) ( ( c i^i d ) = (/) -> E. l e. ( J |`t z )
    E. k e. ( J |`t z ) ( c C_ l /\ d C_ k /\ ( l i^i k ) = (/) ) ) -> ( ( S e.
    ~P U. J /\ T e. ~P U. J ) -> ( ( ( S i^i ( ( cls ` J ) ` T ) ) = (/) /\ ( (
    ( cls ` J ) ` S ) i^i T ) = (/) ) -> E. n e. J E. m e. J ( S C_ n /\ T C_ m
    /\ ( n i^i m ) = (/) ) ) ) ) ) $=
      ( wcel cv cin c0 wceq wss w3a wrex wi cfv ctop crest co ccld wral cuni wa
      cpw ccl cdif oveq2 fveq2d rexeqdv rexeqbidv imbi2d raleqbidv rspcv ineq12
      3ad2ant1 eqeq1d simpl sseq1d simpr 3anbi12d 2rexbidv imbi12d rspc2gv syld
      3adant1 iscnrm3rlem3 3adant3 disjdifb iscnrm3rlem8 embantd iscnrm3lem4
      a1i ) GUAKZHLZILZMZNOZVRJLZPZVSDLZPZWBWDMNOZQZDGALZUBUCZRZJWIRZSZIWIUDTZU
      EZHWMUEZAGUFZUHZUEZBWQKCWQKUGZBCGUITZTZMNOBWTTZCMNOUGZBFLZPCELZPXDXEMNOQE
      GRFGRZWPXBXAMUJZWQKZXBXAUJZGXGUBUCZUDTZKZXAXBUJZXKKZQZXIXMMZNOZXIWBPZXMWD
      PZWFQZDXJRJXJRZSZXOWRWAWGDXJRZJXJRZSZIXKUEZHXKUEZYBXHXLWRYGSXNWOYGAXGWQWH
      XGOZWNYFHWMXKYHWIXJUDWHXGGUBUKZULZYHWLYEIWMXKYJYHWKYDWAYHWJYCJWIXJYIYHWGD
      WIXJYIUMUNUOUPUPUQUSXLXNYGYBSXHYEYBHIXIXMXKXKVRXIOZVSXMOZUGZWAXQYDYAYMVTX
      PNVRXIVSXMURUTYMWGXTJDXJXJYMWCXRWEXSWFYMVRXIWBYKYLVAVBYMVSXMWDYKYLVCVBVDV
      EVFVGVIVHVQWSXOXCBCGVJVKVQWSXCQZXQYAXFXQYNXBXAVLVPBCDEFGJVMVNVO $.
  $}

  $( Lemma for ~ iscnrm3l .  Closed sets in the subspace are subsets of the
     underlying set of the original topology.  (Contributed by Zhi Wang,
     4-Sep-2024.) $)
  iscnrm3llem1 $p  |- ( ( J e. Top
                         /\ ( Z e. ~P U. J
                            /\ C e. ( Clsd ` ( J |`t Z ) )
                            /\ D e. ( Clsd ` ( J |`t Z ) ) )
                         /\ ( C i^i D ) = (/) )
                      -> ( C e. ~P U. J
                         /\ D e. ~P U. J ) ) $=
    ( ctop wcel cuni cpw crest co ccld cfv w3a cin wceq eqidd restcls2lem sstrd
    c0 elpwd simp22 simp1 simp21 elpwid simp23 jca ) CEFZDCGZHZFZACDIJZKLZFZBUL
    FZMZABNSOZMZAUIFBUIFUQAUHULUGUJUMUNUPUAZUQADUHUQACUKUHDUGUOUPUBZUQUHPZUQDUH
    UGUJUMUNUPUCUDZUQUKPZURQVARTUQBUHULUGUJUMUNUPUEZUQBDUHUQBCUKUHDUSUTVAVBVCQV
    ARTUF $.

  ${
    $d C k l m n $.  $d D k l m n $.  $d J k l m n $.  $d Z k l m n $.
    $( Lemma for ~ iscnrm3l .  If there exist disjoint open neighborhoods in
       the original topology for two disjoint closed sets in a subspace, then
       they can be separated by open neighborhoods in the subspace topology.
       (Could shorten proof with ~ ssin0 .)  (Contributed by Zhi Wang,
       5-Sep-2024.) $)
    iscnrm3llem2 $p |- ( ( J e. Top /\ ( Z e. ~P U. J /\ C e. ( Clsd `
    ( J |`t Z ) ) /\ D e. ( Clsd ` ( J |`t Z ) ) ) /\ ( C i^i D ) = (/) )
    -> ( E. n e. J E. m e. J ( C C_ n /\ D C_ m /\ ( n i^i m ) = (/) )
    -> E. l e. ( J |`t Z ) E. k e. ( J |`t Z )
    ( C C_ l /\ D C_ k /\ ( l i^i k ) = (/) ) ) ) $=
      ( ctop wcel w3a cin c0 wceq cv wss sseq2 eqeq1d elrestr syl3anc cpw crest
      cuni co cfv ineq1 3anbi13d ineq2 3anbi23d wa simp11 simp121 simp2l simp2r
      simp31 eqidd elpwid simp122 restcls2lem ssind simp32 simp123 inss1 simp33
      ccld ss2in mp2an sseqtrid ss0 syl 3jca iscnrm3lem7 ) FIJZGFUCZUAZJZAFGUBU
      DZVEUEZJZBVRJZKZABLMNZKZAEOZPZBDOZPZWDWFLZMNZKZAHOZPZBCOZPZWKWMLZMNZKAWDG
      LZPZWNWQWMLZMNZKWRBWFGLZPZWQXALZMNZKZEDHCFFVQVQXAWQWKWQNZWLWRWPWTWNWKWQAQ
      XFWOWSMWKWQWMUFRUGWMXANZWNXBWTXDWRWMXABQXGWSXCMWMXAWQUHRUIWCWDFJZWFFJZUJZ
      WJKZWQVQJZXAVQJZXEXKVMVPXHXLVMWAWBXJWJUKZVPVSVTVMWBXJWJULZWCXHXIWJUMWDGFI
      VOSTXKVMVPXIXMXNXOWCXHXIWJUNWFGFIVOSTXKWRXBXDXKAWDGWCXJWEWGWIUOXKAFVQVNGX
      NXKVNUPZXKGVNXOUQZXKVQUPZVPVSVTVMWBXJWJURUSUTXKBWFGWCXJWEWGWIVAXKBFVQVNGX
      NXPXQXRVPVSVTVMWBXJWJVBUSUTXKXCMPXDXKWHXCMWQWDPXAWFPXCWHPWDGVCWFGVCWQWDXA
      WFVFVGWCXJWEWGWIVDVHXCVIVJVKVKVL $.

    $d C m n s t $.  $d D m n s t $.  $d J m n s t $.
    $( Lemma for ~ iscnrm3 .  Given a topology ` J ` , if two separated sets
       can be separated by open neighborhoods, then all subspaces of the
       topology ` J ` are normal, i.e., two disjoint closed sets can be
       separated by open neighborhoods.  (Contributed by Zhi Wang,
       5-Sep-2024.) $)
    iscnrm3l $p |- ( J e. Top -> ( A. s e. ~P U. J A. t e. ~P U. J
    ( ( ( s i^i ( ( cls ` J ) ` t ) ) = (/) /\ ( ( ( cls ` J ) ` s ) i^i t )
    = (/) ) -> E. n e. J E. m e. J ( s C_ n /\ t C_ m /\ ( n i^i m ) = (/) ) )
    -> ( ( Z e. ~P U. J /\ C e. ( Clsd ` ( J |`t Z ) ) /\
    D e. ( Clsd ` ( J |`t Z ) ) ) -> ( ( C i^i D ) = (/) -> E. l e. ( J |`t Z )
    E. k e. ( J |`t Z ) ( C C_ l /\ D C_ k /\ ( l i^i k ) = (/) ) ) ) ) ) $=
      ( cv cfv cin c0 wceq wa wss w3a wrex wcel ccl ctop cuni cpw crest co ccld
      simpl fveq2d ineq12d eqeq1d anbi12d sseq1d 3anbi12d 2rexbidv iscnrm3llem1
      simpr simp1 eqidd simp21 elpwid simp3 restclssep iscnrm3llem2 iscnrm3lem5
      simp22 simp23 embantd ) IKZAKZGUALZLZMZNOZVIVKLZVJMZNOZPBCVKLZMZNOZBVKLZC
      MZNOZPZVIFKZQZVJEKZQZWEWGMNOZRZEGSFGSBWEQZCWGQZWIRZEGSFGSZGUBTZHGUCZUDZTZ
      BGHUEUFZUGLZTZCWTTZRZBCMNOZBJKZQCDKZQXEXFMNORDWSSJWSSZIABCWQWQVIBOZVJCOZP
      ZVNVTVQWCXJVMVSNXJVIBVLVRXHXIUHZXJVJCVKXHXIUQZUIUJUKXJVPWBNXJVOWAVJCXJVIB
      VKXKUIXLUJUKULXJWJWMFEGGXJWFWKWHWLWIXJVIBWEXKUMXJVJCWGXLUMUNUOBCGHUPWOXCX
      DRZWDWNXGXMBCGWSWPHWOXCXDURXMWPUSXMHWPWOWRXAXBXDUTVAXMWSUSWOWRXAXBXDVFWOX
      CXDVBWOWRXAXBXDVGVCBCDEFGHJVDVHVE $.
  $}

  ${
    $d J c d k l m n s t z $.
    $( A completely normal topology is a topology in which two separated sets
       can be separated by open neighborhoods.  (Contributed by Zhi Wang,
       5-Sep-2024.) $)
    iscnrm3 $p |- ( J e. CNrm <-> ( J e. Top /\ A. s e. ~P U. J A. t e. ~P U. J
    ( ( ( s i^i ( ( cls ` J ) ` t ) ) = (/) /\ ( ( ( cls ` J ) ` s ) i^i t ) =
    (/) ) -> E. n e. J E. m e. J ( s C_ n /\ t C_ m /\ ( n i^i m ) = (/) ) ) )
    ) $=
      ( vz vc vd vl vk wcel cv wral wa cfv cin c0 wceq wss wrex ccnrm ctop cnrm
      crest cuni cpw ccl w3a eqid iscnrm ccld iscnrm3lem1 isnrm3 ralbii bitr4di
      co wi iscnrm3r iscnrm3l iscnrm3lem2 bitr3d pm5.32i bitri ) DUAKDUBKZDFLZU
      DUPZUCKZFDUEZUFZMZNVDELZALZDUGOZOPQRVKVMOVLPQRNVKCLZSVLBLZSVNVOPQRUHBDTCD
      TUQZAVIMEVIMZNFDVHVHUIUJVDVJVQVDGLZHLZPQRVRILZSVSJLZSVTWAPQRUHJVFTIVFTUQZ
      HVFUKOZMGWCMZFVIMZVJVQVDWEVFUBKWDNZFVIMVJWDFVIDULVGWFFVIIJVFGHUMUNUOVDWBV
      PFGHEAVIWCWCVIVIFVKVLJBCDGHIURAVRVSJBCDVEEIUSUTVAVBVC $.
  $}

  ${
    $d J m n s t $.
    $( A topology is completely normal iff two separated sets can be separated
       by open neighborhoods.  (Contributed by Zhi Wang, 10-Sep-2024.) $)
    iscnrm3v $p |- ( J e. Top -> ( J e. CNrm <-> A. s e. ~P U. J A. t e.
    ~P U. J ( ( ( s i^i ( ( cls ` J ) ` t ) ) = (/) /\ ( ( ( cls ` J ) ` s )
    i^i t ) = (/) ) -> E. n e. J E. m e. J ( s C_ n /\ t C_ m /\ ( n i^i m ) =
    (/) ) ) ) ) $=
      ( ccnrm wcel ctop cv ccl cfv cin c0 wceq wa wss w3a wrex wi wral cuni cpw
      iscnrm3 baib ) DFGDHGEIZAIZDJKZKLMNUEUGKUFLMNOUECIZPUFBIZPUHUILMNQBDRCDRS
      ADUAUBZTEUJTABCDEUCUD $.

    $( A completely normal topology is a topology in which two separated sets
       can be separated by neighborhoods.  (Contributed by Zhi Wang,
       5-Sep-2024.) $)
    iscnrm4 $p |- ( J e. CNrm <-> ( J e. Top /\ A. s e. ~P U. J A. t e. ~P U. J
    ( ( ( s i^i ( ( cls ` J ) ` t ) ) = (/) /\ ( ( ( cls ` J ) ` s ) i^i t ) =
    (/) ) -> E. n e. ( ( nei ` J ) ` s ) E. m e. ( ( nei ` J ) ` t )
    ( n i^i m ) = (/) ) ) ) $=
      ( ccnrm wcel ctop cv ccl cfv cin c0 wceq wa wss w3a wrex wi wral cuni cpw
      cnei iscnrm3 id sepnsepo imbi2d 2ralbidv pm5.32i bitr4i ) DFGDHGZEIZAIZDJ
      KZKLMNULUNKUMLMNOZULCIZPUMBIZPUPUQLMNZQBDRCDRZSZADUAUBZTEVATZOUKUOURBUMDU
      CKZKRCULVCKRZSZAVATEVATZOABCDEUDUKVFVBUKVEUTEAVAVAUKVDUSUOUKCBULUMDUKUEUF
      UGUHUIUJ $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Preordered sets and directed sets using extensible structures
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d K x y z $.  $d ph x y z $.
    isprsd.b $e |- ( ph -> B = ( Base ` K ) ) $.
    isprsd.l $e |- ( ph -> .<_ = ( le ` K ) ) $.
    isprsd.k $e |- ( ph -> K e. V ) $.
    $( Property of being a preordered set (deduction form).  (Contributed by
       Zhi Wang, 18-Sep-2024.) $)
    isprsd $p |- ( ph -> ( K e. Proset <-> A. x e. B A. y e. B A. z e. B
           ( x .<_ x /\ ( ( x .<_ y /\ y .<_ z ) -> x .<_ z ) ) ) ) $=
      ( wcel cv cfv wbr wa wi wral breqd raleqbidv cproset cple cbs cvv wb eqid
      elexd isprs baib syl anbi12d imbi12d bitr4d ) AFUALZBMZUOFUBNZOZUOCMZUPOZ
      URDMZUPOZPZUOUTUPOZQZPZDFUCNZRZCVFRZBVFRZUOUOGOZUOURGOZURUTGOZPZUOUTGOZQZ
      PZDERZCERZBERAFUDLZUNVIUEAFHKUGUNVSVIBCDVFFUPVFUFUPUFUHUIUJAVRVHBEVFIAVQV
      GCEVFIAVPVEDEVFIAVJUQVOVDAGUPUOUOJSAVMVBVNVCAVKUSVLVAAGUPUOURJSAGUPURUTJS
      UKAGUPUOUTJSULUKTTTUM $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Posets and lattices using extensible structures
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Posets
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d .<_ x y z $.  $d B x y z $.  $d K x y z $.  $d S x y z $.
    lubeldm2.b $e |- B = ( Base ` K ) $.
    lubeldm2.l $e |- .<_ = ( le ` K ) $.
    ${
      lubeldm2.u $e |- U = ( lub ` K ) $.
      lubeldm2.p $e |- ( ps
   <-> ( A. y e. S y .<_ x /\ A. z e. B ( A. y e. S y .<_ z -> x .<_ z ) ) ) $.
      lubeldm2.k $e |- ( ph -> K e. Poset ) $.
      $( Member of the domain of the least upper bound function of a poset.
         (Contributed by Zhi Wang, 26-Sep-2024.) $)
      lubeldm2 $p |- ( ph -> ( S e. dom U <-> ( S C_ B /\ E. x e. B ps ) ) ) $=
        ( wcel wa cv wbr wral cdm wss wrex cpo lubeldm biimpa reurex anim2i syl
        wreu simpl simprl wrmo poslubmo sylan rmobii sylibr anim1ci reu5 anasss
        wi biimpar syl12anc impbida ) AGHUAPZGFUBZBCFUCZQZAVEQVFBCFUJZQZVHAVEVJ
        ABCDEFGHIJUDKLMNOUEZUFVIVGVFBCFUGUHUIAVHQAVFVIVEAVHUKAVFVGULAVFVGVIAVFQ
        ZVGQVGBCFUMZQVIVLVMVGVLDRZCRZJSDGTVNERZJSDGTVOVPJSVAEFTQZCFUMZVMAIUDPVF
        VROCDEFGIJLKUNUOBVQCFNUPUQURBCFUSUQUTAVEVJVKVBVCVD $.
    $}

    ${
      glbeldm2.g $e |- G = ( glb ` K ) $.
      glbeldm2.p $e |- ( ps
   <-> ( A. y e. S x .<_ y /\ A. z e. B ( A. y e. S z .<_ y -> z .<_ x ) ) ) $.
      glbeldm2.k $e |- ( ph -> K e. Poset ) $.
      $( Member of the domain of the greatest lower bound function of a poset.
         (Contributed by Zhi Wang, 26-Sep-2024.) $)
      glbeldm2 $p |- ( ph -> ( S e. dom G <-> ( S C_ B /\ E. x e. B ps ) ) ) $=
        ( wcel wa cv wbr wral cdm wss wrex cpo glbeldm biimpa reurex anim2i syl
        wreu simpl simprl wrmo posglbmo sylan rmobii sylibr anim1ci reu5 anasss
        wi biimpar syl12anc impbida ) AGHUAPZGFUBZBCFUCZQZAVEQVFBCFUJZQZVHAVEVJ
        ABCDEFGHIJUDKLMNOUEZUFVIVGVFBCFUGUHUIAVHQAVFVIVEAVHUKAVFVGULAVFVGVIAVFQ
        ZVGQVGBCFUMZQVIVLVMVGVLCRZDRZJSDGTERZVOJSDGTVPVNJSVAEFTQZCFUMZVMAIUDPVF
        VROCDEFGIJLKUNUOBVQCFNUPUQURBCFUSUQUTAVEVJVKVBVCVD $.
    $}
  $}

  ${
    $d K x y z $.  $d S x y z $.  $d ph x y z $.
    lubeldm2d.b $e |- ( ph -> B = ( Base ` K ) ) $.
    lubeldm2d.l $e |- ( ph -> .<_ = ( le ` K ) ) $.
    ${
      lubeldm2d.u $e |- ( ph -> U = ( lub ` K ) ) $.
      lubeldm2d.p $e |- ( ( ph /\ x e. B ) -> ( ps <-> ( A. y e. S y .<_ x /\
                      A. z e. B ( A. y e. S y .<_ z -> x .<_ z ) ) ) ) $.
      lubeldm2d.k $e |- ( ph -> K e. Poset ) $.
      $( Member of the domain of the least upper bound function of a poset.
         (Contributed by Zhi Wang, 28-Sep-2024.) $)
      lubeldm2d $p |- ( ph -> ( S e. dom U
                <-> ( S C_ B /\ E. x e. B ps ) ) ) $=
        ( cfv wcel wbr wral wa club cdm cbs wss cv cple wrex eqid biid lubeldm2
        wi dmeqd eleq2d sseq2d wb breqd ralbidv imbi12d raleqbidv anbi12d bitrd
        adantr pm5.32da anbi1d rexbidv2 3bitr4d ) AGIUAPZUBZQGIUCPZUDZDUEZCUEZI
        UFPZRZDGSZVKEUEZVMRZDGSZVLVPVMRZUKZEVISZTZCVIUGZTGHUBZQGFUDZBCFUGZTAWBC
        DEVIGVGIVMVIUHVMUHVGUHWBUIOUJAWDVHGAHVGMULUMAWEVJWFWCAFVIGKUNABWBCFVIAV
        LFQZBTWGWBTVLVIQZWBTAWGBWBAWGTBVKVLJRZDGSZVKVPJRZDGSZVLVPJRZUKZEFSZTZWB
        NAWPWBUOWGAWJVOWOWAAWIVNDGAJVMVKVLLUPUQAWNVTEFVIKAWLVRWMVSAWKVQDGAJVMVK
        VPLUPUQAJVMVLVPLUPURUSUTVBVAVCAWGWHWBAFVIVLKUMVDVAVEUTVF $.
    $}

    ${
      glbeldm2d.g $e |- ( ph -> G = ( glb ` K ) ) $.
      glbeldm2d.p $e |- ( ( ph /\ x e. B ) -> ( ps <-> ( A. y e. S x .<_ y /\
                      A. z e. B ( A. y e. S z .<_ y -> z .<_ x ) ) ) ) $.
      glbeldm2d.k $e |- ( ph -> K e. Poset ) $.
      $( Member of the domain of the greatest lower bound function of a poset.
         (Contributed by Zhi Wang, 29-Sep-2024.) $)
      glbeldm2d $p |- ( ph -> ( S e. dom G
              <-> ( S C_ B /\ E. x e. B ps ) ) ) $=
        ( cfv wcel wbr wral wa cglb cdm cbs wss cv cple wrex eqid biid glbeldm2
        wi dmeqd eleq2d sseq2d wb breqd ralbidv imbi12d raleqbidv anbi12d bitrd
        adantr pm5.32da anbi1d rexbidv2 3bitr4d ) AGIUAPZUBZQGIUCPZUDZCUEZDUEZI
        UFPZRZDGSZEUEZVLVMRZDGSZVPVKVMRZUKZEVISZTZCVIUGZTGHUBZQGFUDZBCFUGZTAWBC
        DEVIGVGIVMVIUHVMUHVGUHWBUIOUJAWDVHGAHVGMULUMAWEVJWFWCAFVIGKUNABWBCFVIAV
        KFQZBTWGWBTVKVIQZWBTAWGBWBAWGTBVKVLJRZDGSZVPVLJRZDGSZVPVKJRZUKZEFSZTZWB
        NAWPWBUOWGAWJVOWOWAAWIVNDGAJVMVKVLLUPUQAWNVTEFVIKAWLVRWMVSAWKVQDGAJVMVP
        VLLUPUQAJVMVPVKLUPURUSUTVBVAVCAWGWHWBAFVIVKKUMVDVAVEUTVF $.
    $}
  $}

  ${
    $d G x y z $.  $d K x y z $.  $d S x y z $.  $d T x y z $.  $d U x y z $.
    $d ph x y z $.
    lubsscl.k $e |- ( ph -> K e. Poset ) $.
    lubsscl.t $e |- ( ph -> T C_ S ) $.
    ${
      lubsscl.u $e |- U = ( lub ` K ) $.
      lubsscl.s $e |- ( ph -> S e. dom U ) $.
      lubsscl.x $e |- ( ph -> ( U ` S ) e. T ) $.
      $( If a subset of ` S ` contains the LUB of ` S ` , then the two sets
         have the same LUB. (Contributed by Zhi Wang, 26-Sep-2024.) $)
      lubsscl $p |- ( ph -> ( T e. dom U /\ ( U ` T ) = ( U ` S ) ) ) $=
        ( vy vx vz wcel cfv cv wbr wral wa cpo cdm wceq cbs wss cple wi lubelss
        wrex eqid sstrd sseldd adantr sselda luble ralrimiva w3a breq1 3ad2ant1
        simp3 rspcdva 3expia breq2 ralbidv imbi2d rspcev syl12anc biid lubeldm2
        anbi12d mpbir2and poslubd jca ) ACDUAZNZCDOBDOZUBAVNCEUCOZUDKPZLPZEUEOZ
        QZKCRZVQMPZVSQZKCRZVRWBVSQZUFZMVPRZSZLVPUHZACBVPGAVPBDEVSTVPUIZVSUIZHFI
        UGUJZAVOVPNVQVOVSQZKCRZWDVOWBVSQZUFZMVPRZWIACVPVOWLJUKZAWMKCAVQCNZSVPBD
        EVSTVQWJWKHAETNWSFULABVMNWSIULACBVQGUMUNZUOAWPMVPAWBVPNZWDWOAXAWDUPWCWO
        KCVOVQVOWBVSUQAXAWDUSAXAVOCNWDJURUTZVAUOWHWNWQSLVOVPVRVOUBZWAWNWGWQXCVT
        WMKCVRVOVQVSVBVCXCWFWPMVPXCWEWOWDVRVOWBVSUQVDVCVIVEVFAWHLKMVPCDEVSWJWKH
        WHVGFVHVJAKMVPCVODEVSWKWJHFWLWRWTXBVKVL $.
    $}

    ${
      glbsscl.g $e |- G = ( glb ` K ) $.
      glbsscl.s $e |- ( ph -> S e. dom G ) $.
      glbsscl.x $e |- ( ph -> ( G ` S ) e. T ) $.
      $( If a subset of ` S ` contains the GLB of ` S ` , then the two sets
         have the same GLB. (Contributed by Zhi Wang, 26-Sep-2024.) $)
      glbsscl $p |- ( ph -> ( T e. dom G /\ ( G ` T ) = ( G ` S ) ) ) $=
        ( vx vy vz wcel cfv wceq cv wbr wral wa cdm cbs wss cple wi cpo glbelss
        wrex eqid sstrd sseldd adantr sselda glble ralrimiva w3a breq2 3ad2ant1
        simp3 rspcdva 3expia breq1 ralbidv imbi2d rspcev syl12anc biid glbeldm2
        anbi12d mpbir2and eqidd cglb a1i posglbdg jca ) ACDUAZNZCDOBDOZPAVQCEUB
        OZUCKQZLQZEUDOZRZLCSZMQZWAWBRZLCSZWEVTWBRZUEZMVSSZTZKVSUHZACBVSGAVSBDEW
        BUFVSUIZWBUIZHFIUGUJZAVRVSNVRWAWBRZLCSZWGWEVRWBRZUEZMVSSZWLACVSVRWOJUKZ
        AWPLCAWACNZTVSBDEWBUFWAWMWNHAEUFNXBFULABVPNXBIULACBWAGUMUNZUOAWSMVSAWEV
        SNZWGWRAXDWGUPWFWRLCVRWAVRWEWBUQAXDWGUSAXDVRCNWGJURUTZVAUOWKWQWTTKVRVSV
        TVRPZWDWQWJWTXFWCWPLCVTVRWAWBVBVCXFWIWSMVSXFWHWRWGVTVRWEWBUQVDVCVIVEVFA
        WKKLMVSCDEWBWMWNHWKVGFVHVJALMVSCVRDEWBWNAVSVKDEVLOPAHVMFWOXAXCXEVNVO $.
    $}
  $}

  ${
    $d .<_ z $.  $d B z $.  $d X z $.  $d Y z $.
    lubpr.k $e |- ( ph -> K e. Poset ) $.
    lubpr.b $e |- B = ( Base ` K ) $.
    lubpr.x $e |- ( ph -> X e. B ) $.
    lubpr.y $e |- ( ph -> Y e. B ) $.
    lubpr.l $e |- .<_ = ( le ` K ) $.
    lubpr.c $e |- ( ph -> X .<_ Y ) $.
    lubpr.s $e |- ( ph -> S = { X , Y } ) $.
    ${
      lubpr.u $e |- U = ( lub ` K ) $.
      $( Lemma for ~ lubprdm and ~ lubpr .  (Contributed by Zhi Wang,
         26-Sep-2024.) $)
      lubprlem $p |- ( ph -> ( S e. dom U /\ ( U ` S ) = Y ) ) $=
        ( vz wcel cfv wbr cdm wceq cpr cv breq1 elrabd cpo posref syl2anc prssd
        crab lublecl prid2g syl eqeltrd lubsscl simpld fveq2d simprd 3eqtrd jca
        lubid ) ACDUAZRCDSZHUBACGHUCZVCOAVEVCRZVEDSZQUDZHFTZQBUKZDSZUBZAVJVEDEI
        AGHVJAVIGHFTQGBVHGHFUEKNUFAVIHHFTZQHBVHHHFUELAEUGRHBRZVMILBEFHJMUHUIUFU
        JPAQBDEFHJMPILULAVKHVEAQBDEFHJMPILVBZAVNHVERLGHBUMUNUOUPZUQUOAVDVGVKHAC
        VEDOURAVFVLVPUSVOUTVA $.

      $( The set of two comparable elements in a poset has LUB. (Contributed by
         Zhi Wang, 26-Sep-2024.) $)
      lubprdm $p |- ( ph -> S e. dom U ) $=
        ( cdm wcel cfv wceq lubprlem simpld ) ACDQRCDSHTABCDEFGHIJKLMNOPUAUB $.

      $( The LUB of the set of two comparable elements in a poset is the
         greater one of the two.  (Contributed by Zhi Wang, 26-Sep-2024.) $)
      lubpr $p |- ( ph -> ( U ` S ) = Y ) $=
        ( cdm wcel cfv wceq lubprlem simprd ) ACDQRCDSHTABCDEFGHIJKLMNOPUAUB $.
    $}

    ${
      glbpr.g $e |- G = ( glb ` K ) $.
      $( Lemma for ~ glbprdm and ~ glbpr .  (Contributed by Zhi Wang,
         26-Sep-2024.) $)
      glbprlem $p |- ( ph -> ( S e. dom G /\ ( G ` S ) = X ) ) $=
        ( cdm wcel cfv cpo wceq codu club odupos syl odubas oduleval wbr brcnvg
        ccnv eqid syl2anc mpbird cpr prcom eqtrdi lubprdm odulub dmeqd eleqtrrd
        wb fveq1d lubpr eqtrd jca ) ACDQZRCDSZGUAACEUBSZUCSZQVFABCVIVHFUJZHGAET
        RZVHTRIVHEVHUKZUDUEZBVHEVLJUFZLKVHFEVLMUGZAHGVJUHZGHFUHZNAHBRGBRVPVQVAL
        KHGBBFUIULUMZACGHUNHGUNOGHUOUPZVIUKZUQADVIAVKDVIUAIVHDETVLPURUEZUSUTAVG
        CVISGACDVIWAVBABCVIVHVJHGVMVNLKVOVRVSVTVCVDVE $.

      $( The set of two comparable elements in a poset has GLB. (Contributed by
         Zhi Wang, 26-Sep-2024.) $)
      glbprdm $p |- ( ph -> S e. dom G ) $=
        ( cdm wcel cfv wceq glbprlem simpld ) ACDQRCDSGTABCDEFGHIJKLMNOPUAUB $.

      $( The GLB of the set of two comparable elements in a poset is the less
         one of the two.  (Contributed by Zhi Wang, 26-Sep-2024.) $)
      glbpr $p |- ( ph -> ( G ` S ) = X ) $=
        ( cdm wcel cfv wceq glbprlem simprd ) ACDQRCDSGTABCDEFGHIJKLMNOPUAUB $.
    $}
  $}

  ${
    $d ./\ w x y z $.  $d .\/ w x y z $.  $d .<_ v $.  $d B w x y z $.
    $d K v w z $.  $d ph x y $.  $d v w x y z $.
    joindm2.b $e |- B = ( Base ` K ) $.
    joindm2.k $e |- ( ph -> K e. V ) $.
    ${
      joindm2.u $e |- U = ( lub ` K ) $.
      joindm2.j $e |- .\/ = ( join ` K ) $.
      $( The join of any two elements always exists iff all unordered pairs
         have LUB. (Contributed by Zhi Wang, 25-Sep-2024.) $)
      joindm2 $p |- ( ph -> ( dom .\/ = ( B X. B )
                <-> A. x e. B A. y e. B { x , y } e. dom U ) ) $=
        ( cdm wss cv wcel wal wb a1i cvv cxp wceq cop wi cpr wral joindmss eqss
        baib syl wrel relxp ssrel wa opelxp vex joindef imbi12d 2albidv bitr4di
        mp1i r2al 3bitrd ) AFMZDDUAZUBZVEVDNZBOZCOZUCZVEPZVJVDPZUDZCQBQZVHVIUEE
        MPZCDUFBDUFZAVDVENZVFVGRADFGHILJUGVFVQVGVDVEUHUIUJVEUKVGVNRADDULBCVEVDU
        MVAAVNVHDPVIDPUNZVOUDZCQBQVPAVMVSBCAVKVRVLVOVKVRRAVHVIDDUOSAEFGHTVHVITK
        LJVHTPABUPSVITPACUPSUQURUSVOBCDDVBUTVC $.

      joindm3.l $e |- .<_ = ( le ` K ) $.
      $( The join of any two elements always exists iff all unordered pairs
         have LUB (expanded version).  (Contributed by Zhi Wang,
         25-Sep-2024.) $)
      joindm3 $p |- ( ph -> ( dom .\/ = ( B X. B ) <->
                A. x e. B A. y e. B E! z e. B ( ( x .<_ z /\ y .<_ z ) /\
                    A. w e. B ( ( x .<_ w /\ y .<_ w ) -> z .<_ w ) ) ) ) $=
        ( vv wral wbr wa cdm cxp wceq cv cpr wcel wi wreu joindm2 wss wb simprl
        simprr prssd biid lubeldm baibd syldan adantr joinval2lem reubidv bitrd
        adantl 2ralbidva ) AHUAFFUBUCBUDZCUDZUEZGUAUFZCFRBFRVEDUDZJSVFVIJSTVEEU
        DZJSVFVJJSTVIVJJSZUGEFRTZDFUHZCFRBFRABCFGHIKLMNOUIAVHVMBCFFAVEFUFZVFFUF
        ZTZTZVHQUDZVIJSQVGRVRVJJSQVGRVKUGEFRTZDFUHZVMAVPVGFUJZVHVTUKVQVEVFFAVNV
        OULZAVNVOUMZUNAVHWAVTAVSDQEFVGGIJKLPNVSUOMUPUQURVPVTVMUKAVPVSVLDFVQDQEF
        HIJKVEVFLPOAIKUFVPMUSWBWCUTVAVCVBVDVB $.
    $}

    ${
      meetdm2.g $e |- G = ( glb ` K ) $.
      meetdm2.m $e |- ./\ = ( meet ` K ) $.
      $( The meet of any two elements always exists iff all unordered pairs
         have GLB. (Contributed by Zhi Wang, 25-Sep-2024.) $)
      meetdm2 $p |- ( ph -> ( dom ./\ = ( B X. B )
                <-> A. x e. B A. y e. B { x , y } e. dom G ) ) $=
        ( cdm wss cv wcel wal wb a1i cvv cxp wceq cop wi cpr wral meetdmss eqss
        baib syl wrel relxp ssrel wa opelxp vex meetdef imbi12d 2albidv bitr4di
        mp1i r2al 3bitrd ) AGMZDDUAZUBZVEVDNZBOZCOZUCZVEPZVJVDPZUDZCQBQZVHVIUEE
        MPZCDUFBDUFZAVDVENZVFVGRADFGHILJUGVFVQVGVDVEUHUIUJVEUKVGVNRADDULBCVEVDU
        MVAAVNVHDPVIDPUNZVOUDZCQBQVPAVMVSBCAVKVRVLVOVKVRRAVHVIDDUOSAEFGHTVHVITK
        LJVHTPABUPSVITPACUPSUQURUSVOBCDDVBUTVC $.

      meetdm3.l $e |- .<_ = ( le ` K ) $.
      $( The meet of any two elements always exists iff all unordered pairs
         have GLB (expanded version).  (Contributed by Zhi Wang,
         25-Sep-2024.) $)
      meetdm3 $p |- ( ph -> ( dom ./\ = ( B X. B ) <->
                A. x e. B A. y e. B E! z e. B ( ( z .<_ x /\ z .<_ y ) /\
                    A. w e. B ( ( w .<_ x /\ w .<_ y ) -> w .<_ z ) ) ) ) $=
        ( vv wral wbr wa cdm cxp wceq cv cpr wcel wi wreu meetdm2 wss wb simprl
        simprr prssd biid glbeldm baibd syldan adantr meetval2lem reubidv bitrd
        adantl 2ralbidva ) AJUAFFUBUCBUDZCUDZUEZGUAUFZCFRBFRDUDZVEISVIVFISTEUDZ
        VEISVJVFISTVJVIISZUGEFRTZDFUHZCFRBFRABCFGHJKLMNOUIAVHVMBCFFAVEFUFZVFFUF
        ZTZTZVHVIQUDZISQVGRVJVRISQVGRVKUGEFRTZDFUHZVMAVPVGFUJZVHVTUKVQVEVFFAVNV
        OULZAVNVOUMZUNAVHWAVTAVSDQEFVGGHIKLPNVSUOMUPUQURVPVTVMUKAVPVSVLDFVQDQEF
        HIJKVEVFLPOAHKUFVPMUSWBWCUTVAVCVBVDVB $.
    $}
  $}

  ${
    posjidm.b $e |- B = ( Base ` K ) $.
    ${
      posjidm.j $e |- .\/ = ( join ` K ) $.
      $( Poset join is idempotent. ~ latjidm could be shortened by this.
         (Contributed by Zhi Wang, 27-Sep-2024.) $)
      posjidm $p |- ( ( K e. Poset /\ X e. B ) -> ( X .\/ X ) = X ) $=
        ( cpo wcel wa cpr club cfv eqid simpl simpr joinval cple posref eqidd
        co lubpr eqtrd ) CGHZDAHZIZDDBTDDJZCKLZLDUEUGBCGADDAUGMZFUCUDNZUCUDOZUJ
        PUEAUFUGCCQLZDDUIEUJUJUKMZACUKDEULRUEUFSUHUAUB $.
    $}

    ${
      posmidm.m $e |- ./\ = ( meet ` K ) $.
      $( Poset meet is idempotent. ~ latmidm could be shortened by this.
         (Contributed by Zhi Wang, 27-Sep-2024.) $)
      posmidm $p |- ( ( K e. Poset /\ X e. B ) -> ( X ./\ X ) = X ) $=
        ( cpo wcel wa cpr cglb cfv eqid simpl simpr meetval cple posref eqidd
        co glbpr eqtrd ) BGHZDAHZIZDDCTDDJZBKLZLDUEUGBCGADDAUGMZFUCUDNZUCUDOZUJ
        PUEAUFUGBBQLZDDUIEUJUJUKMZABUKDEULRUEUFSUHUAUB $.
    $}
  $}

  ${
    $d B x y z $.  $d K x y z $.  $d V x y z $.
    resipos.k $e |- K = { <. ( Base ` ndx ) , B >.
                          , <. ( le ` ndx ) , ( _I |` B ) >. } $.
    $( Construct a poset ( ~ resipos ) for any base set.  (Contributed by Zhi
       Wang, 20-Oct-2025.) $)
    resiposbas $p |- ( B e. V -> B = ( Base ` K ) ) $=
      ( cid cres cnx cple cfv basendxltplendx plendxnn 2strbas ) AEAFBGHICDJKL
      $.

    $( A set equipped with an order where no distinct elements are comparable
       is a poset.  (Contributed by Zhi Wang, 20-Oct-2025.) $)
    resipos $p |- ( B e. V -> K e. Poset ) $=
      ( vx vy vz wcel cvv cnx cfv cop cple cv wbr weq wb resieq wa syl2anc cres
      cid cbs cpr prex eqeltri resiposbas wceq resiexg basendxltplendx plendxnn
      a1i pleid 2strop syl equid anidms mpbiri adantl wi biimpd adantrd 3adant1
      w3a eqtr simpr1 simpr2 simpr3 anbi12d 3imtr4d isposd ) ACHZEFGABUBAUAZIBI
      HVLBJUCKALZJMKZVMLZUDIDVNVPUEUFULABCDUGVLVMIHVMBMKUHACUIAVMMBVOIDUJUKUMUN
      UOENZAHZVQVQVMOZVLVRVSEEPZEUPVRVSVTQAVQVQRUQURUSVRFNZAHZVQWAVMOZWAVQVMOZS
      EFPZUTVLVRWBSZWCWEWDWFWCWEAVQWARZVAVBVCVLVRWBGNZAHZVDSZWEFGPZSZEGPZWCWAWH
      VMOZSVQWHVMOZWLWMUTWJVQWAWHVEULWJWCWEWNWKWJVRWBWCWEQVLVRWBWIVFZVLVRWBWIVG
      ZWGTWJWBWIWNWKQWQVLVRWBWIVHZAWAWHRTVIWJVRWIWOWMQWPWRAVQWHRTVJVK $.
  $}

  ${
    $d B k $.  $d b k $.
    $( There exists a poset for any base set.  (Contributed by Zhi Wang,
       20-Oct-2025.) $)
    exbaspos $p |- ( B e. V -> E. k e. Poset B = ( Base ` k ) ) $=
      ( wcel cv cbs cfv wceq cnx cop cple cid cres cpr cpo fveq2 eqeq2d resipos
      eqid resiposbas rspcedvdw ) ACDABEZFGZHAIFGAJIKGLAMJNZFGZHBUDOUBUDHUCUEAU
      BUDFPQAUDCUDSZRAUDCUFTUA $.

    $( There exists a preordered set for any base set.  (Contributed by Zhi
       Wang, 20-Oct-2025.) $)
    exbasprs $p |- ( B e. V -> E. k e. Proset B = ( Base ` k ) ) $=
      ( wcel cv cbs cfv wceq cnx cop cple cid cres cpr cproset fveq2 eqeq2d cpo
      eqid resipos posprs syl resiposbas rspcedvdw ) ACDZABEZFGZHAIFGAJIKGLAMJN
      ZFGZHBUHOUFUHHUGUIAUFUHFPQUEUHRDUHODAUHCUHSZTUHUAUBAUHCUJUCUD $.

    $( The base function restricted to the class of posets maps the class of
       posets onto the universal class.  (Contributed by Zhi Wang,
       20-Oct-2025.) $)
    basresposfo $p |- ( Base |` Poset ) : Poset -onto-> _V $=
      ( vb vk cpo cvv cbs cres wfo wf cv cfv wceq wrex wral wfn wss ssv fnssres
      basfn mp2an wcel dffn2 mpbi exbaspos fvres eqeq2d rexbiia sylibr mpbir2an
      rgen dffo3 ) CDECFZGCDUKHZAIZBIZUKJZKZBCLZADMUKCNZULEDNCDOURRCPDCEQSCUKUA
      UBUQADUMDTUMUNEJZKZBCLUQUMBDUCUPUTBCUNCTUOUSUMUNCEUDUEUFUGUIBACDUKUJUH $.

    $( The base function restricted to the class of preordered sets maps the
       class of preordered sets onto the universal class.  (Contributed by Zhi
       Wang, 20-Oct-2025.) $)
    basresprsfo $p |- ( Base |` Proset ) : Proset -onto-> _V $=
      ( vk vb cproset cbs cnx cfv cv cop cple cid cres cpr cvv basfn wcel fvexd
      cpo eqid resipos posprs syl resiposbas slotresfo ) CADEDFBGZHEIFJUDKHLZMB
      NAGZCOUFDPUDMOUEQOUECOUDUEMUERZSUETUAUDUEMUGUBUC $.
  $}

  $( The class of posets is a proper class.  (Contributed by Zhi Wang,
     20-Oct-2025.) $)
  posnex $p |- Poset e/ _V $=
    ( cpo cvv cbs cres vprc nelir basresposfo fonex ) ABCADBBEFGH $.

  $( The class of preordered sets is a proper class.  (Contributed by Zhi Wang,
     20-Oct-2025.) $)
  prsnex $p |- Proset e/ _V $=
    ( cproset cvv cbs cres vprc nelir basresprsfo fonex ) ABCADBBEFGH $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Lattices
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d K x y $.
    $( A toset is a lattice.  (Contributed by Zhi Wang, 26-Sep-2024.) $)
    toslat $p |- ( K e. Toset -> K e. Lat ) $=
      ( vx vy wcel cpo cfv cdm wceq wa cv cpr wral wbr ad2antrr simplrl simplrr
      eqid simpr lubprdm mpjaodan ctos cjn cbs cmee clat tospos club cple eqidd
      cxp prcom a1i tleile 3expb ralrimivva joindm2 mpbird cglb glbprdm meetdm2
      wo jca islat sylanbrc ) AUADZAEDZAUBFZGAUCFZVHUJZHZAUDFZGVIHZIAUEDAUFZVEV
      JVLVEVJBJZCJZKZAUGFZGDZCVHLBVHLVEVRBCVHVHVEVNVHDZVOVHDZIZIZVNVOAUHFZMZVRV
      OVNWCMZWBWDIZVHVPVQAWCVNVOVEVFWAWDVMNZVHQZVEVSVTWDOZVEVSVTWDPZWCQZWBWDRZW
      FVPUIZVQQZSWBWEIZVHVPVQAWCVOVNVEVFWAWEVMNZWHVEVSVTWEPZVEVSVTWEOZWKWBWERZV
      PVOVNKHWOVNVOUKULZWNSVEVSVTWDWEVAVHAWCVNVOWHWKUMUNZTUOVEBCVHVQVGAEWHVMWNV
      GQZUPUQVEVLVPAURFZGDZCVHLBVHLVEXDBCVHVHWBWDXDWEWFVHVPXCAWCVNVOWGWHWIWJWKW
      LWMXCQZUSWOVHVPXCAWCVOVNWPWHWQWRWKWSWTXEUSXATUOVEBCVHXCAVKEWHVMXEVKQZUTUQ
      VBVHVGAVKWHXBXFVCVD $.
  $}

  ${
    $d B s $.  $d G s $.  $d K t x y z $.  $d U s $.  $d ph s $.
    isclatd.b $e |- ( ph -> B = ( Base ` K ) ) $.
    isclatd.u $e |- ( ph -> U = ( lub ` K ) ) $.
    isclatd.g $e |- ( ph -> G = ( glb ` K ) ) $.
    isclatd.k $e |- ( ph -> K e. Poset ) $.
    isclatd.1 $e |- ( ( ph /\ s C_ B ) -> s e. dom U ) $.
    isclatd.2 $e |- ( ( ph /\ s C_ B ) -> s e. dom G ) $.
    $( The predicate "is a complete lattice" (deduction form).  (Contributed by
       Zhi Wang, 29-Sep-2024.) $)
    isclatd $p |- ( ph -> K e. CLat ) $=
      ( vy vx vt vz wcel cv wbr wral cpo club cfv cdm cbs cpw wceq cglb ccla wi
      cple wreu crab eqid biid lubdm ssrab2 eqsstrdi wss elpwi sylan2 ralrimiva
      wa dfss3 sylibr pweqd dmeqd 3sstr3d eqssd glbdm isclat biimpri syl12anc )
      AEUAQZEUBUCZUDZEUEUCZUFZUGZEUHUCZUDZVRUGZEUIQZJAVPVRAVPMRZNRZEUKUCZSMORZT
      WDPRZWFSMWGTWEWHWFSUJPVQTVCZNVQULZOVRUMVRAWINMPVQVOEWFUAOVQUNZWFUNZVOUNZW
      IUOJUPWJOVRUQURABUFZCUDZVRVPAFRZWOQZFWNTWNWOUSAWQFWNWPWNQZAWPBUSZWQWPBUTZ
      KVAVBFWNWOVDVEABVQGVFZACVOHVGVHVIAWAVRAWAWEWDWFSMWGTWHWDWFSMWGTWHWEWFSUJP
      VQTVCZNVQULZOVRUMVRAXBNMPVQVTEWFUAOWKWLVTUNZXBUOJVJXCOVRUQURAWNDUDZVRWAAW
      PXEQZFWNTWNXEUSAXFFWNWRAWSXFWTLVAVBFWNXEVDVEXAADVTIVGVHVIWCVNVSWBVCVCVQVO
      VTEWKWMXDVKVLVM $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Subset order structures
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d A x y z $.  $d B x y z $.  $d C y z $.
    $( Existential uniqueness of the least upper bound.  (Contributed by Zhi
       Wang, 28-Sep-2024.) $)
    intubeu $p |- ( C e. B -> ( ( A C_ C /\ A. y e. B ( A C_ y -> C C_ y ) )
                 <-> C = |^| { x e. B | A C_ x } ) ) $=
      ( vz wcel wss cv wi wral crab cint wceq ssint sseq2 ralrab bitri bilanri
      wa simpll simplr elrabd cbvrabv eleqtrdi intss1 eqssd expl ssintub mpbiri
      syl eqimss sylib jca impbid1 ) EDGZCEHZCBIZHZEURHZJBDKZTECAIZHZADLZMZNZUP
      UQVAVFUPUQTZVATZEVEEVEHZVAVGVIUTBVDKVABEVDOVCUSUTBADVBURCPQRZSVHEVDGVEEHV
      HECFIZHZFDLVDVHVLUQFEDVKECPUPUQVAUAUPUQVAUBUCVLVCFADVKVBCPUDUEEVDUFUKUGUH
      VFUQVAVFUQCVEHACDUIEVECPUJVFVIVAEVEULVJUMUNUO $.

    $( Existential uniqueness of the greatest lower bound.  (Contributed by Zhi
       Wang, 29-Sep-2024.) $)
    unilbeu $p |- ( C e. B -> ( ( C C_ A /\ A. y e. B ( y C_ A -> y C_ C ) )
                 <-> C = U. { x e. B | x C_ A } ) ) $=
      ( vz wcel cv wi wral wa crab cuni wceq sseq1 simpll simplr elrabd cbvrabv
      wss eleqtrdi elssuni syl unissb ralrab bitri bilanri eqssd unilbss mpbiri
      expl eqimss2 sylib jca impbid1 ) EDGZECTZBHZCTZURETZIBDJZKEAHZCTZADLZMZNZ
      UPUQVAVFUPUQKZVAKZEVEVHEVDGEVETVHEFHZCTZFDLVDVHVJUQFEDVIECOUPUQVAPUPUQVAQ
      RVJVCFADVIVBCOSUAEVDUBUCVEETZVAVGVKUTBVDJVABVDEUDVCUSUTBADVBURCOUEUFZUGUH
      UKVFUQVAVFUQVECTACDUIEVECOUJVFVKVAVEEULVLUMUNUO $.
  $}

  ${
    ipolub.i $e |- I = ( toInc ` F ) $.
    ipolub.f $e |- ( ph -> F e. V ) $.
    ipolub.s $e |- ( ph -> S C_ F ) $.
    ${
      $d F y z $.  $d S y $.  $d X y z $.  $d ph y z $.
      ipolublem.l $e |- .<_ = ( le ` I ) $.
      $( Lemma for ~ ipolubdm and ~ ipolub .  (Contributed by Zhi Wang,
         28-Sep-2024.) $)
      ipolublem $p |- ( ( ph /\ X e. F )
            -> ( ( U. S C_ X /\ A. z e. F ( U. S C_ z -> X C_ z ) )
    <-> ( A. y e. S y .<_ X /\
        A. z e. F ( A. y e. S y .<_ z -> X .<_ z ) ) ) ) $=
        ( wcel wa wss wbr wral wb ad2antrr cuni cv wi unissb simpr sseldd ipole
        simplr syl3anc ralbidva bitr4id adantlr bicomd imbi12d anbi12d ) AIENZO
        ZDUAZIPZBUBZIGQZBDRZURCUBZPZIVCPZUCZCERUTVCGQZBDRZIVCGQZUCZCERUQUSUTIPZ
        BDRVBBDIUDUQVAVKBDUQUTDNZOZEHNZUTENZUPVAVKSAVNUPVLKTZVMDEUTADEPUPVLLTUQ
        VLUEUFZAUPVLUHEFGHUTIJMUGUIUJUKUQVFVJCEUQVCENZOZVDVHVEVIVSVDUTVCPZBDRVH
        BDVCUDVSVGVTBDVSVLOVNVOVRVGVTSUQVLVNVRVPULUQVLVOVRVQULUQVRVLUHEFGHUTVCJ
        MUGUIUJUKVSVIVEVSVNUPVRVIVESAVNUPVRKTAUPVRUHUQVRUEEFGHIVCJMUGUIUMUNUJUO
        $.
    $}

    ${
      $d F t v w x y z $.  $d I t v w y z $.  $d S t v w x y z $.
      $d U v w y z $.  $d T t v w y z $.  $d ph t v w y z $.
      ipolub.u $e |- ( ph -> U = ( lub ` I ) ) $.
      ipolubdm.t $e |- ( ph -> T = |^| { x e. F | U. S C_ x } ) $.
      $( The domain of the LUB of the inclusion poset.  (Contributed by Zhi
         Wang, 28-Sep-2024.) $)
      ipolubdm $p |- ( ph -> ( S e. dom U <-> T e. F ) ) $=
        ( vt vz wcel cv wss wa wceq vy cdm cuni wi wral wrex cfv cbs ipobas syl
        cple eqidd eqid ipolublem cpo a1i lubeldm2d mpbirand crab cint ad2antrr
        ipopos intubeu biimpa adantll eqtr4d eqeltrd simpr biimparc sylan sseq2
        simplr ex sseq1 imbi2d ralbidv anbi12d rspceb2dv bitrd ) ACEUBPZCUCZNQZ
        RZWAOQZRZWBWDRZUDZOFUEZSZNFUFZDFPZAVTCFRWJKAWINUAOFCEGGUKUGZAFHPFGUHUGT
        JFGHIUIUJAWLULLAUAOCFGWLHWBIJKWLUMUNGUOPAFGIVBUPUQURAWIWKWADRZWEDWDRZUD
        ZOFUEZSZNDFAWBFPZSZWIWKWSWISZDWBFWTDWABQRBFUSUTZWBADXATZWRWIMVAWRWIWBXA
        TZAWRWIXCBOWAFWBVCVDVEVFAWRWIVLVGVMAWKVHAXBWKWQMWKWQXBBOWAFDVCVIVJWBDTZ
        WCWMWHWPWBDWAVKXDWGWOOFXDWFWNWEWBDWDVNVOVPVQVRVS $.

      ipolub.t $e |- ( ph -> T e. F ) $.
      $( The LUB of the inclusion poset.  (hypotheses "ipolub.s" and "ipolub.t"
         could be eliminated with ` S e. dom U ` .)  Could be significantly
         shortened if ~ poslubdg is in quantified form. ~ mrelatlub could
         potentially be shortened using this.  See ~ mrelatlubALT .
         (Contributed by Zhi Wang, 28-Sep-2024.) $)
      ipolub $p |- ( ph -> ( U ` S ) = T ) $=
        ( vw vv wcel cv wbr wral vy vz cple cfv eqid cbs wceq ipobas syl ipopos
        cpo a1i wa breq1 wi cuni crab cint intubeu biimpar syl2anc wb ipolublem
        mpdan mpbid simpld adantr simpr rspcdva ralbidv cbvralvw bitrdi imbi12d
        wss breq2 simprd 3impia poslubdg ) AUAUBFCDEGGUCUDZVSUEZAFHQFGUFUDUGJFG
        HIUHUILGUKQAFGIUJULKNAUARZCQZUMORZDVSSZWADVSSOCWAWCWADVSUNAWDOCTZWBAWEW
        CPRZVSSZOCTZDWFVSSZUOZPFTZACUPZDVNWLWFVNDWFVNUOPFTUMZWEWKUMZADFQZDWLBRV
        NBFUQURUGZWMNMWOWMWPBPWLFDUSUTVAAWOWMWNVBNAOPCFGVSHDIJKVTVCVDVEZVFVGAWB
        VHVIAUBRZFQZWAWRVSSZUACTZDWRVSSZAWSUMWJXAXBUOPFWRWFWRUGZWHXAWIXBXCWHWCW
        RVSSZOCTXAXCWGXDOCWFWRWCVSVOVJXDWTOUACWCWAWRVSUNVKVLWFWRDVSVOVMAWKWSAWE
        WKWQVPVGAWSVHVIVQVR $.
    $}

    ${
      $d F y z $.  $d S y $.  $d X y z $.  $d ph y z $.
      ipoglblem.l $e |- .<_ = ( le ` I ) $.
      $( Lemma for ~ ipoglbdm and ~ ipoglb .  (Contributed by Zhi Wang,
         29-Sep-2024.) $)
      ipoglblem $p |- ( ( ph /\ X e. F )
            -> ( ( X C_ |^| S /\ A. z e. F ( z C_ |^| S -> z C_ X ) )
    <-> ( A. y e. S X .<_ y /\
        A. z e. F ( A. y e. S z .<_ y -> z .<_ X ) ) ) ) $=
        ( wcel wa wss wbr wral wb ad2antrr cint cv wi ssint simplr simpr sseldd
        ipole syl3anc ralbidva bitr4id adantlr bicomd imbi12d anbi12d ) AIENZOZ
        IDUAZPZIBUBZGQZBDRZCUBZURPZVCIPZUCZCERVCUTGQZBDRZVCIGQZUCZCERUQUSIUTPZB
        DRVBBIDUDUQVAVKBDUQUTDNZOZEHNZUPUTENZVAVKSAVNUPVLKTZAUPVLUEVMDEUTADEPUP
        VLLTUQVLUFUGZEFGHIUTJMUHUIUJUKUQVFVJCEUQVCENZOZVDVHVEVIVSVDVCUTPZBDRVHB
        VCDUDVSVGVTBDVSVLOVNVRVOVGVTSUQVLVNVRVPULUQVRVLUEUQVLVOVRVQULEFGHVCUTJM
        UHUIUJUKVSVIVEVSVNVRUPVIVESAVNUPVRKTUQVRUFAUPVRUEEFGHVCIJMUHUIUMUNUJUO
        $.
    $}

    ${
      $d F v w x y z $.  $d I v w y z $.  $d S v w x y z $.  $d G v w y z $.
      $d T v w y z $.  $d ph v w y z $.
      ipoglb.g $e |- ( ph -> G = ( glb ` I ) ) $.
      ipoglbdm.t $e |- ( ph -> T = U. { x e. F | x C_ |^| S } ) $.
      $( The domain of the GLB of the inclusion poset.  (Contributed by Zhi
         Wang, 29-Sep-2024.) $)
      ipoglbdm $p |- ( ph -> ( S e. dom G <-> T e. F ) ) $=
        ( vw vz wcel cv wss wa wceq vy cdm cint wi wral wrex cfv cbs ipobas syl
        cple eqidd eqid ipoglblem cpo a1i glbeldm2d mpbirand crab cuni ad2antrr
        ipopos unilbeu biimpa adantll eqtr4d eqeltrd simpr biimparc sylan sseq1
        simplr ex sseq2 imbi2d ralbidv anbi12d rspceb2dv bitrd ) ACFUBPZNQZCUCZ
        RZOQZWBRZWDWARZUDZOEUEZSZNEUFZDEPZAVTCERWJKAWINUAOECFGGUKUGZAEHPEGUHUGT
        JEGHIUIUJAWLULLAUAOCEGWLHWAIJKWLUMUNGUOPAEGIVBUPUQURAWIWKDWBRZWEWDDRZUD
        ZOEUEZSZNDEAWAEPZSZWIWKWSWISZDWAEWTDBQWBRBEUSUTZWAADXATZWRWIMVAWRWIWAXA
        TZAWRWIXCBOWBEWAVCVDVEVFAWRWIVLVGVMAWKVHAXBWKWQMWKWQXBBOWBEDVCVIVJWADTZ
        WCWMWHWPWADWBVKXDWGWOOEXDWFWNWEWADWDVNVOVPVQVRVS $.

      ipoglb.t $e |- ( ph -> T e. F ) $.
      $( The GLB of the inclusion poset.  (hypotheses "ipolub.s" and "ipoglb.t"
         could be eliminated with ` S e. dom G ` .)  Could be significantly
         shortened if ~ posglbdg is in quantified form. ~ mrelatglb could
         potentially be shortened using this.  See ~ mrelatglbALT .
         (Contributed by Zhi Wang, 29-Sep-2024.) $)
      ipoglb $p |- ( ph -> ( G ` S ) = T ) $=
        ( vy vz wcel cv wbr wral vv vw cple cfv eqid cbs wceq ipobas syl ipopos
        cpo a1i wa breq2 wi cint crab cuni unilbeu biimpar syl2anc wb ipoglblem
        mpdan mpbid simpld adantr simpr rspcdva ralbidv cbvralvw bitrdi imbi12d
        wss breq1 simprd 3impia posglbdg ) AUAUBECDFGGUCUDZVSUEZAEHQEGUFUDUGJEG
        HIUHUILGUKQAEGIUJULKNAUARZCQZUMDORZVSSZDWAVSSOCWAWCWADVSUNAWDOCTZWBAWEP
        RZWCVSSZOCTZWFDVSSZUOZPETZADCUPZVNWFWLVNWFDVNUOPETUMZWEWKUMZADEQZDBRWLV
        NBEUQURUGZWMNMWOWMWPBPWLEDUSUTVAAWOWMWNVBNAOPCEGVSHDIJKVTVCVDVEZVFVGAWB
        VHVIAUBRZEQZWRWAVSSZUACTZWRDVSSZAWSUMWJXAXBUOPEWRWFWRUGZWHXAWIXBXCWHWRW
        CVSSZOCTXAXCWGXDOCWFWRWCVSVOVJXDWTOUACWCWAWRVSUNVKVLWFWRDVSVOVMAWKWSAWE
        WKWQVPVGAWSVHVIVQVR $.
    $}
  $}

  ${
    $d F x y z $.  $d G x y z $.  $d I x y z $.  $d U x y z $.  $d V x y z $.
    ipoglb0.i $e |- I = ( toInc ` F ) $.
    ${
      ipolub0.u $e |- ( ph -> U = ( lub ` I ) ) $.
      ipolub0.f $e |- ( ph -> |^| F e. F ) $.
      ipolub0.v $e |- ( ph -> F e. V ) $.
      $( The LUB of the empty set is the intersection of the base.
         (Contributed by Zhi Wang, 30-Sep-2024.) $)
      ipolub0 $p  |- ( ph -> ( U ` (/) ) = |^| F ) $=
        ( vx c0 cint wss 0ss a1i cuni cv crab wceq wcel eqsstri rabeqc eqcomi
        uni0 inteqi ipolub ) AJKCLZBCDEFIKCMACNOGUGKPZJQZMZJCRZLSACUKUKCUJJCUJU
        ICTUHKUIUDUINUAOUBUCUEOHUF $.
    $}

    ${
      ipolub00.u $e |- ( ph -> U = ( lub ` I ) ) $.
      ipolub00.f $e |- ( ph -> (/) e. F ) $.
      $( The LUB of the empty set is the empty set if it is contained.
         (Contributed by Zhi Wang, 30-Sep-2024.) $)
      ipolub00 $p  |- ( ph -> ( U ` (/) ) = (/) ) $=
        ( vy vx vz wcel c0 cfv wceq wa club adantr eqtrd cv wbr cvv cint int0el
        syl eqeltrd simpr ipolub0 wn cipo fvprc adantl eqtrid fveq2d fveq1d cdm
        wss cple wral wi wrex rex0 intnan base0 eqid biid cpo 0pos a1i lubeldm2
        mtbiri ndmfv pm2.61dan ) ACUAKZLBMZLNAVMOZVNCUBZLVOBCDUAEABDPMZNZVMFQAV
        PCKVMAVPLCALCKVPLNZGCUCUDZGUEQAVMUFUGAVSVMVTQRAVMUHZOZVNLLPMZMZLWBLBWCW
        BBVQWCAVRWAFQWBDLPWBDCUIMZLEWAWELNACUIUJUKULUMRUNWBLWCUOKZUHWDLNWBWFLLU
        PZHSZISZLUQMZTHLURWHJSZWJTHLURWIWKWJTUSJLUROZILUTZOWMWGWLIVAVBWBWLIHJLL
        WCLWJVCWJVDWCVDWLVELVFKWBVGVHVIVJLWCVKUDRVL $.
    $}

    ${
      ipoglb0.g $e |- ( ph -> G = ( glb ` I ) ) $.
      ipoglb0.f $e |- ( ph -> U. F e. F ) $.
      $( The GLB of the empty set is the union of the base.  (Contributed by
         Zhi Wang, 30-Sep-2024.) $)
      ipoglb0 $p |- ( ph -> ( G ` (/) ) = U. F ) $=
        ( vx c0 cuni cvv wcel uniexr syl wss 0ss a1i cv cint crab wceq ssv int0
        sseqtrri rabeqc unieqi eqcomi ipoglb ) AHIBJZBCDKEAUIBLBKLGBBMNIBOABPQF
        UIHRZISZOZHBTZJZUAAUNUIUMBULHBULUJBLUJKUKUJUBUCUDQUEUFUGQGUH $.
    $}
  $}

  ${
    $d C x y $.  $d F x y $.  $d G x y $.  $d I x y $.  $d U x y $.
    $d X x y $.
    mreclatGOOD.i $e |- I = ( toInc ` C ) $.
    ${
      mrelatlubALT.f $e |- F = ( mrCls ` C ) $.
      mrelatlubALT.l $e |- L = ( lub ` I ) $.
      $( Least upper bounds in a Moore space are realized by the closure of the
         union.  (Contributed by Stefan O'Rear, 31-Jan-2015.)  (Proof shortened
         by Zhi Wang, 29-Sep-2024.)  (Proof modification is discouraged.)
         (New usage is discouraged.) $)
      mrelatlubALT $p |- ( ( C e. ( Moore ` X ) /\ U C_ C ) ->
          ( L ` U ) = ( F ` U. U ) ) $=
        ( vx cmre cfv wcel wss wa cuni simpl simpr wceq syldan club a1i cv crab
        cint mreuniss mrcval mrccl ipolub ) AFKLZMZBANZOZJBBPZCLZEADUJGUKULQUKU
        LREDUALSUMIUBUKULUNFNZUOUNJUCNJAUDUESABFUFZAUNCFJHUGTUKULUPUOAMUQAUNCFH
        UHTUI $.
    $}

    ${
      mrelatglbALT.g $e |- G = ( glb ` I ) $.
      $( Greatest lower bounds in a Moore space are realized by intersections.
         (Contributed by Stefan O'Rear, 31-Jan-2015.)  (Proof shortened by Zhi
         Wang, 29-Sep-2024.)  (Proof modification is discouraged.)
         (New usage is discouraged.) $)
      mrelatglbALT $p |- ( ( C e. ( Moore ` X ) /\ U C_ C /\ U =/= (/) ) ->
          ( G ` U ) = |^| U ) $=
        ( vx cmre cfv wcel wss c0 wne w3a cint simp1 simp2 cglb wceq a1i unimax
        cv crab cuni mreintcl eqcomd syl ipoglb ) AEIJZKZBALZBMNZOZHBBPZACDUJFU
        KULUMQUKULUMRCDSJTUNGUAUNUOAKZUOHUCUOLHAUDUEZTABEUFZUPUQUOHUOAUBUGUHURU
        I $.
    $}

    $( A Moore space is a complete lattice under inclusion.  (Contributed by
       Zhi Wang, 30-Sep-2024.) $)
    mreclat $p |- ( C e. ( Moore ` X ) -> I e. CLat ) $=
      ( vx vy cfv wcel eqidd cv wss wa cdm cuni syldan crab cint wceq eqeltrd
      c0 cmre club cglb ipobas cpo ipopos cmrc mreuniss eqid mrccl simpl mrcval
      a1i simpr ipolubdm mpbird cvv ssv int0 sseqtrri simplr sseqtrrid rabeqcda
      inteqd unieqd mreuni mre1cl ad2antrr wne mreintcl unimax 3expa pm2.61dane
      w3a syl ipoglbdm isclatd ) ACUAGZHZABUBGZBUCGZBEABVRDUDVSVTIVSWAIBUEHVSAB
      DUFUMVSEJZAKZLZWBVTMHWBNZAUGGZGZAHZVSWCWECKZWHAWBCUHZAWEWFCWFUIZUJOWDFWBW
      GVTABVRDVSWCUKZVSWCUNZWDVTIVSWCWIWGWEFJZKFAPQRWJAWEWFCFWKULOUOUPWDWBWAMHW
      NWBQZKZFAPZNZAHZWDWSWBTWDWBTRZLZWRANZAXAWQAXAWPFAXAWNAHZLZTQZWNWOWNUQXEWN
      URUSUTXDWBTWDWTXCVAVDVBVCVEVSXBAHWCWTVSXBCAACVFACVGSVHSVSWCWBTVIZWSVSWCXF
      VNZWRWOAXGWOAHWRWORAWBCVJZFWOAVKVOXHSVLVMWDFWBWRAWABVRDWLWMWDWAIWDWRIVPUP
      VQ $.
  $}

  ${
    $d G x y $.  $d I x y $.  $d J x y $.  $d S x y $.  $d U x y $.
    topclat.i $e |- I = ( toInc ` J ) $.
    $( A topology is a complete lattice under inclusion.  (Contributed by Zhi
       Wang, 30-Sep-2024.) $)
    topclat $p |- ( J e. Top -> I e. CLat ) $=
      ( vx vy ctop wcel club cfv cglb ipobas eqidd cv wss cuni uniopn crab cint
      cdm mpbird cpo ipopos a1i wa simpl wceq intmin eqcomd syl ipolubdm ssrab2
      simpr sylancl ipoglbdm isclatd ) BFGZBAHIZAJIZADBAFCKUPUQLUPURLAUAGUPBACU
      BUCUPDMZBNZUDZUSUQSGUSOZBGZUSBPZVAEUSVBUQBAFCUPUTUEZUPUTULZVAUQLVAVCVBVBE
      MZNEBQRZUFVDVCVHVBEVBBUGUHUIUJTVAUSURSGVGUSRNZEBQZOZBGZVAUPVJBNVLVEVIEBUK
      VJBPUMVAEUSVKBURAFCVEVFVAURLVAVKLUNTUO $.

    toplatlub.j $e |- ( ph -> J e. Top ) $.
    ${
      toplatglb0.g $e |- G = ( glb ` I ) $.
      $( The empty intersection in a topology is realized by the base set.
         (Contributed by Zhi Wang, 30-Sep-2024.) $)
      toplatglb0 $p |- ( ph -> ( G ` (/) ) = U. J ) $=
        ( cglb cfv wceq a1i ctop wcel cuni eqid topopn syl ipoglb0 ) ADBCEBCHIJ
        AGKADLMDNZDMFDSSOPQR $.
    $}

    toplatlub.s $e |- ( ph -> S C_ J ) $.
    ${
      toplatlub.u $e |- U = ( lub ` I ) $.
      $( Least upper bounds in a topology are realized by unions.  (Contributed
         by Zhi Wang, 30-Sep-2024.) $)
      toplatlub $p |- ( ph -> ( U ` S ) = U. S ) $=
        ( vx cuni ctop club cfv wceq a1i wcel cv wss crab uniopn syl2anc intmin
        cint eqcomd syl ipolub ) AJBBKZCEDLFGHCDMNOAIPAUHEQZUHUHJRSJETUDZOAELQB
        ESUIGHBEUAUBZUIUJUHJUHEUCUEUFUKUG $.
    $}

    toplatglb.g $e |- G = ( glb ` I ) $.
    toplatglb.e $e |- ( ph -> S =/= (/) ) $.
    $( Greatest lower bounds in a topology are realized by the interior of the
       intersection.  (Contributed by Zhi Wang, 30-Sep-2024.) $)
    toplatglb $p |- ( ph -> ( G ` S ) = ( ( int ` J ) ` |^| S ) ) $=
      ( vx cfv ctop wceq cuni wss wcel syl syl2anc cvv cint cnt cglb a1i cpw cv
      cin crab c0 wne intssuni unissd sstrd eqid ntrval uniexd ssexd inpw eqtrd
      unieqd ntropn ipoglb ) AKBBUAZEUBLLZECDMFGHCDUCLNAIUDAVDEVCUEUGZOZKUFVCPK
      EUHZOZAEMQZVCEOZPZVDVFNGAVCBOZVJABUIUJVCVLPJBUKRABEHULUMZVCEVJVJUNZUOSAVC
      TQZVFVHNAVCVJTAEMGUPVMUQVOVEVGKEVCTURUTRUSAVIVKVDEQGVMVCEVJVNVASVB $.
  $}

  ${
    $d A x $.  $d B x $.  $d J x $.
    toplatmeet.i $e |- I = ( toInc ` J ) $.
    toplatmeet.j $e |- ( ph -> J e. Top ) $.
    toplatmeet.a $e |- ( ph -> A e. J ) $.
    toplatmeet.b $e |- ( ph -> B e. J ) $.
    ${
      toplatjoin.j $e |- .\/ = ( join ` I ) $.
      $( Joins in a topology are realized by unions.  (Contributed by Zhi Wang,
         30-Sep-2024.) $)
      toplatjoin $p   |- ( ph -> ( A .\/ B ) = ( A u. B ) ) $=
        ( vx co cpr cfv cpo wcel a1i ctop wceq club cun eqid joinval prssd cuni
        ipopos cv wss crab cint uniprg syl2anc unopn syl3anc eqeltrd intmin syl
        eqtr2d ipolub eqtrd ) ABCFMBCNZDUAOZOBCUBZAVCFDPEBCEVCUCZKDPQAEDGUGRIJU
        DALVBVDVCEDSGHABCEIJUEVCVCTAVERAVBUFZLUHUILEUJUKZVFVDAVFEQVGVFTAVFVDEAB
        EQZCEQZVFVDTIJBCEEULUMZAESQVHVIVDEQHIJBCEUNUOZUPLVFEUQURVJUSVKUTVA $.
    $}

    ${
      toplatmeet.m $e |- ./\ = ( meet ` I ) $.
      $( Meets in a topology are realized by intersections.  (Contributed by
         Zhi Wang, 30-Sep-2024.) $)
      toplatmeet $p   |- ( ph -> ( A ./\ B ) = ( A i^i B ) ) $=
        ( vx co cpr cfv cpo wcel a1i ctop wceq cglb cin ipopos meetval prssd cv
        eqid cint wss crab cuni intprg syl2anc inopn syl3anc eqeltrd unimax syl
        eqtr2d ipoglb eqtrd ) ABCFMBCNZDUAOZOBCUBZAVCDFPEBCEVCUGZKDPQAEDGUCRIJU
        DALVBVDEVCDSGHABCEIJUEVCVCTAVERALUFVBUHZUILEUJUKZVFVDAVFEQVGVFTAVFVDEAB
        EQZCEQZVFVDTIJBCEEULUMZAESQVHVIVDEQHIJBCEUNUOZUPLVFEUQURVJUSVKUTVA $.
    $}
  $}

  ${
    $d I x y z $.  $d J x y z $.
    topdlat.i $e |- I = ( toInc ` J ) $.
    $( A topology is a distributive lattice under inclusion.  (Contributed by
       Zhi Wang, 30-Sep-2024.) $)
    topdlat $p |- ( J e. Top -> I e. DLat ) $=
      ( vx vy vz ctop wcel cv cfv co wceq wral syl cun eleqtrrd eqid toplatmeet
      cin syl3anc clat cjn cmee cbs cdlat topclat clatl w3a simpl simpr2 ipobas
      ccla wa simpr3 toplatjoin oveq2d simpr1 unopn inopn oveq12d indi 3eqtr4rd
      a1i 3eqtrd ralrimivvva isdlat sylanbrc ) BGHZAUAHZDIZEIZFIZAUBJZKZAUCJZKZ
      VJVKVOKZVJVLVOKZVMKZLZFAUDJZMEWAMDWAMAUEHVHAULHVIABCUFAUGNVHVTDEFWAWAWAVH
      VJWAHZVKWAHZVLWAHZUHZUMZVPVJVKVLOZVOKVJWGSZVSWFVNWGVJVOWFVKVLABVMCVHWEUIZ
      WFVKWABVHWBWCWDUJWFVHBWALWIBAGCUKNZPZWFVLWABVHWBWCWDUNWJPZVMQZUOUPWFVJWGA
      BVOCWIWFVJWABVHWBWCWDUQWJPZWFVHVKBHZVLBHZWGBHWIWKWLVKVLBURTVOQZRWFVJVKSZV
      JVLSZVMKWRWSOZVSWHWFWRWSABVMCWIWFVHVJBHZWOWRBHWIWNWKVJVKBUSTWFVHXAWPWSBHW
      IWNWLVJVLBUSTWMUOWFVQWRVRWSVMWFVJVKABVOCWIWNWKWQRWFVJVLABVOCWIWNWLWQRUTWH
      WTLWFVJVKVLVAVCVBVDVEDEFWAVMAVOWAQWMWQVFVG $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Rings
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Multiplicative Group
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d B y $.  $d M y $.  $d R y $.  $d X y $.  $d ph y $.
    elmgpcntrd.b $e |- B = ( Base ` R ) $.
    elmgpcntrd.m $e |- M = ( mulGrp ` R ) $.
    elmgpcntrd.z $e |- Z = ( Cntr ` M ) $.
    elmgpcntrd.x $e |- ( ph -> X e. B ) $.
    elmgpcntrd.y $e |- ( ( ph /\ y e. B ) ->
                         ( X ( .r ` R ) y ) = ( y ( .r ` R ) X ) ) $.
    $( The center of a ring.  (Contributed by Zhi Wang, 11-Sep-2025.) $)
    elmgpcntrd $p |- ( ph -> X e. Z ) $=
      ( wcel cv cmulr cfv co wceq wral ralrimiva mgpbas eqid mgpplusg sylanbrc
      elcntr ) AFCMFBNZDOPZQUFFUGQRZBCSFGMKAUHBCLTBFCUGEGCDEIHUADUGEIUGUBUCJUEU
      D $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Associative algebras
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Definition and basic properties
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    asclelbasALT.a $e |- A = ( algSc ` W ) $.
    asclelbasALT.f $e |- F = ( Scalar ` W ) $.
    asclelbasALT.b $e |- B = ( Base ` F ) $.
    asclelbasALT.w $e |- ( ph -> W e. AssAlg ) $.
    asclelbasALT.c $e |- ( ph -> C e. B ) $.
    $( Alternate proof of ~ asclelbas .  (Contributed by Zhi Wang,
       11-Sep-2025.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    asclelbasALT $p |- ( ph -> ( A ` C ) e. ( Base ` W ) ) $=
      ( cfv cur cvsca co cbs wcel wceq eqid syl asclval casa clmod assalmod crg
      assaring ringidcl 3syl lmodvscld eqeltrd ) ADBLZDFMLZFNLZOZFPLZADCQUKUNRK
      BUMULECFDGHIUMSZULSZUATADUMECUOFULUOSZHUPIAFUBQZFUCQJFUDTKAUSFUEQULUOQJFU
      FUOFULURUQUGUHUIUJ $.

    ${
      $d A x $.  $d C x $.  $d M x $.  $d W x $.  $d ph x $.
      asclcntr.m $e |- M = ( mulGrp ` W ) $.
      $( The algebra scalar lifting function maps into the center of the
         algebra.  Equivalently, a lifted scalar is a center of the algebra.
         (Contributed by Zhi Wang, 11-Sep-2025.) $)
      asclcntr $p |- ( ph -> ( A ` C ) e. ( Cntr ` M ) ) $=
        ( vx cbs cfv eqid wcel co adantr ccntr asclelbas cv wa casa cmulr simpr
        wceq w3a cvsca asclmul1 asclmul2 eqtr4d syl3anc elmgpcntrd ) ANGOPZGFDB
        PZFUAPZUPQZMURQABCDEGHIJKLUBANUCZUPRZUDGUERZDCRZVAUQUTGUFPZSZUTUQVDSZUH
        AVBVAKTAVCVALTAVAUGVBVCVAUIVEDUTGUJPZSVFBDVGVDECUPGUTHIJUSVDQZVGQZUKBDV
        GVDECUPGUTHIJUSVHVIULUMUNUO $.
    $}

    ${
      asclcom.m $e |- .* = ( .r ` F ) $.
      asclcom.d $e |- ( ph -> D e. B ) $.
      $( Scalars are commutative after being lifted.

         However, the scalars themselves are not necessarily commutative if the
         algebra is not a faithful module.  For example, Let ` F ` be the 2 by
         2 upper triangular matrix algebra over a commutative ring ` W ` .  It
         is provable that ` F ` is in general non-commutative.  Define scalar
         multiplication ` C .x. X ` as multipying the top-left entry, which is
         a "vector" element of ` W ` , of the "scalar" ` C ` , which is now an
         upper triangular matrix, with the "vector" ` X e. ( Base `` W ) ` .

         Equivalently, the algebra scalar lifting function is not necessarily
         injective unless the algebra is faithful.  Therefore, all "scalar
         injection" was renamed.

         Alternate proof involves ~ assa2ass , ~ assa2ass2 , and ~ asclval , by
         setting ` X ` and ` Y ` the multiplicative identity of the algebra.

         (Contributed by Zhi Wang, 11-Sep-2025.) $)
      asclcom $p |- ( ph -> ( A ` ( C .* D ) ) = ( A ` ( D .* C ) ) ) $=
        ( cfv co wcel wceq eqid cmulr cbs asclelbas w3a cvsca asclmul1 asclmul2
        casa eqtr4d syl3anc ascldimul 3eqtr4d ) ADBPZEBPZHUAPZQZUNUMUOQZDEGQBPZ
        EDGQBPZAHUHRZDCRZUNHUBPZRZUPUQSLMABCEFHIJKLOUCUTVAVCUDUPDUNHUEPZQUQBDVD
        UOFCVBHUNIJKVBTZUOTZVDTZUFBDVDUOFCVBHUNIJKVEVFVGUGUIUJAUTVAECRZURUPSLMO
        BDEGUOFCHIJKVFNUKUJAUTVHVAUSUQSLOMBEDGUOFCHIJKVFNUKUJUL $.
    $}
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Categories
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Categories
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d C x y $.
    $( The base is empty iff the functionalized Hom-set operation is empty.
       (Contributed by Zhi Wang, 23-Oct-2025.) $)
    homf0 $p |- ( ( Base ` C ) = (/) <-> ( Homf ` C ) = (/) ) $=
      ( vx vy cbs c0 wceq chomf cv chom co cmpo eqid homffval 0mpo0 orcs eqtrid
      cfv cxp wfn homffn wf f0bi ffn sylbir fndmu sylancr wo xpeq0 pm4.25 sylib
      bitr4i impbii ) ADQZEFZAGQZEFZUNUOBCUMUMBHCHAIQZJZKZEBCUMAUOUQUOLZUMLZUQL
      MUNUNUSEFBCUMUMURNOPUPUMUMRZEFZUNUPUOVBSUOESZVCUMAUOUTVATUPEEUOUAVDUOEUBE
      EUOUCUDVBEUOUEUFVCUNUNUGUNUMUMUHUNUIUKUJUL $.
  $}

  ${
    $d .<_ w x y z $.  $d B w x y z $.  $d H w x y z $.  $d X w z $.
    $d Y w z $.
    catprs.1 $e |- ( ph -> A. x e. B A. y e. B
                               ( x .<_ y <-> ( x H y ) =/= (/) ) ) $.
    ${
      catprslem.x $e |- ( ph -> X e. B ) $.
      catprslem.y $e |- ( ph -> Y e. B ) $.
      $( Lemma for ~ catprs .  (Contributed by Zhi Wang, 18-Sep-2024.) $)
      catprslem $p  |- ( ph -> ( X .<_ Y <-> ( X H Y ) =/= (/) ) ) $=
        ( vz vw cv wbr co c0 wne wb wral breq1 oveq1 neeq1d bibi12d breq2 oveq2
        weq cbvral2vw sylib wcel wi wceq wa breq12 oveq12 rspc2gv syl2anc mpd )
        ALNZMNZFOZUSUTEPZQRZSZMDTLDTZGHFOZGHEPZQRZSZABNZCNZFOZVJVKEPZQRZSZCDTBD
        TVEIVOVDUSVKFOZUSVKEPZQRZSBCLMDDBLUGZVLVPVNVRVJUSVKFUAVSVMVQQVJUSVKEUBU
        CUDCMUGZVPVAVRVCVKUTUSFUEVTVQVBQVKUTUSEUFUCUDUHUIAGDUJHDUJVEVIUKJKVDVIL
        MGHDDUSGULUTHULUMZVAVFVCVHUSGUTHFUNWAVBVGQUSGUTHEUOUCUDUPUQUR $.
    $}

    catprs.b $e |- ( ph -> B = ( Base ` C ) ) $.
    catprs.h $e |- ( ph -> H = ( Hom ` C ) ) $.
    ${
      catprs.c $e |- ( ph -> C e. Cat ) $.
      $( A preorder can be extracted from a category.  See ~ catprs2 for more
         details.  (Contributed by Zhi Wang, 18-Sep-2024.) $)
      catprs $p |- ( ( ph /\ ( X e. B /\ Y e. B /\ Z e. B ) ) -> ( X .<_ X
                  /\ ( ( X .<_ Y /\ Y .<_ Z ) -> X .<_ Z ) ) ) $=
        ( wcel wa wbr co c0 wne w3a wi ccid cfv chom eqid adantr simpr1 eleqtrd
        cbs ccat wceq catidcl oveqd eleqtrrd ne0d cv wb wral catprslem ad2antrr
        mpbird eleq2d pm5.32i cco simplr1 simplr2 simplr3 simpr2 biimpa adantrr
        3anbi123d eqnetrrd sylanbr simpr3 adantrl catcone0 sylanb eqnetrd jca
        ex ) AHDOZIDOZJDOZUAZPZHHGQZHIGQZIJGQZPZHJGQZUBWFWGHHFRZSTWFWLHEUCUDZUD
        ZWFWNHHEUEUDZRWLWFEUJUDZEWMWOHWPUFZWOUFZWMUFAEUKOZWENUGWFHDWPAWBWCWDUHZ
        ADWPULWELUGUIUMWFFWOHHAFWOULZWEMUGUNUOUPWFBCDFGHHABUQZCUQZGQXBXCFRSTURC
        DUSBDUSWEKUGZWTWTUTVBWFWJWKWFWJPZWKHJFRZSTZXEXFHJWORZSXEFWOHJAXAWEWJMVA
        ZUNWFAHWPOZIWPOZJWPOZUAZPZWJXHSTAWEXMAWBXJWCXKWDXLADWPHLVCADWPILVCADWPJ
        LVCVLVDZXNWJPWPEEVEUDZWOHIJWQWRXPUFAWSXMWJNVAXJXKXLAWJVFXJXKXLAWJVGXJXK
        XLAWJVHXNWFWJHIWORZSTXOXEHIFRZXQSXEFWOHIXIUNWFWHXRSTZWIWFWHXSWFBCDFGHIX
        DWTAWBWCWDVIZUTVJVKVMVNXNWFWJIJWORZSTXOXEIJFRZYASXEFWOIJXIUNWFWIYBSTZWH
        WFWIYCWFBCDFGIJXDXTAWBWCWDVOZUTVJVPVMVNVQVRVSWFWKXGURWJWFBCDFGHJXDWTYDU
        TUGVBWAVT $.

      ${
        $d B u v $.  $d C u v w $.  $d ph u v w $.
        catprs2.l $e |- ( ph -> .<_ = ( le ` C ) ) $.
        $( A category equipped with the induced preorder, where an object ` x `
           is defined to be "less than or equal to" ` y ` iff there is a
           morphism from ` x ` to ` y ` , is a preordered set, or a proset.
           The category might not be thin.  See ~ catprsc and ~ catprsc2 for
           constructions satisfying the hypothesis "catprs.1".  See ~ catprs
           for a more primitive version.  See ~ prsthinc for constructing a
           thin category from a proset.  (Contributed by Zhi Wang,
           18-Sep-2024.) $)
        catprs2 $p |- ( ph -> C e. Proset ) $=
          ( vw vv vu cproset cv wbr wa wral wcel catprs ralrimivvva ccat isprsd
          wi mpbird ) AEPUAMQZUHGRUHNQZGRUIOQZGRSUHUJGRUFSZODTNDTMDTAUKMNODDDAB
          CDEFGUHUIUJHIJKUBUCAMNODEGUDILKUEUG $.
      $}

$(
      catprs3.k @e |- ( ph -> K = ( C sSet <. ( le ` ndx ) , .<_ >. ) ) @.
      @( A category equipped with the induced preorder is a preordered set, or
         a proset.  (Contributed by Zhi Wang, XX-Sep-2024.) @)
      catprs3 @p |- ( ph -> K e. Proset ) @=
        (  ) ? @.
$)
    $}

$(
    catprs4.f @e |- ( ph -> F = ( c e. Cat |-> .<_ ) ) @.
    @( There is a function from ` Cat ` to the class of preorders.
       (Contributed by Zhi Wang, XX-Sep-2024.) @)
    catprs4 @p |- ( ph -> F : Cat --> ( le " Proset ) ) @=
      (  ) ? @.
$)
  $}

  ${
    $d B w x y $.  $d H x y $.  $d ph w z $.  $d x y z $.
    catprsc.1 $e |- ( ph -> .<_ = { <. x , y >. |
            ( x e. B /\ y e. B /\ ( x H y ) =/= (/) ) } ) $.
    $( A construction of the preorder induced by a category.  See ~ catprs2 for
       details.  See also ~ catprsc2 for an alternate construction.
       (Contributed by Zhi Wang, 18-Sep-2024.) $)
    catprsc $p |- ( ph -> A. z e. B A. w e. B
                          ( z .<_ w <-> ( z H w ) =/= (/) ) ) $=
      ( cv wbr co c0 wne wcel wa w3a vex weq eleq1d wb copab breqd simpl oveq12
      simpr neeq1d 3anbi123d df-3an bitrdi eqid braba baibd ralrimivva ) ADJZEJ
      ZHKZUOUPGLZMNZUADEFFAUQUOFOZUPFOZPZUSAUQUOUPBJZFOZCJZFOZVCVEGLZMNZQZBCUBZ
      KVBUSPZAHVJUOUPIUCVIVKBCUOUPVJDRERBDSZCESZPZVIUTVAUSQVKVNVDUTVFVAVHUSVNVC
      UOFVLVMUDTVNVEUPFVLVMUFTVNVGURMVCUOVEUPGUEUGUHUTVAUSUIUJVJUKULUJUMUN $.
  $}

  ${
    $d B w $.  $d H x y $.  $d ph w z $.  $d w x y z $.
    catprsc2.1 $e |- ( ph -> .<_ = { <. x , y >. | ( x H y ) =/= (/) } ) $.
    $( An alternate construction of the preorder induced by a category.  See
       ~ catprs2 for details.  See also ~ catprsc for a different construction.
       The two constructions are different because ~ df-cat does not require
       the domain of ` H ` to be ` B X. B ` .  (Contributed by Zhi Wang,
       23-Sep-2024.) $)
    catprsc2 $p |- ( ph -> A. z e. B A. w e. B
                          ( z .<_ w <-> ( z H w ) =/= (/) ) ) $=
      ( cv wbr co c0 wne wb wcel wa copab vex weq oveq12 neeq1d eqid ralrimivva
      breqd braba bitrdi adantr ) ADJZEJZHKZUIUJGLZMNZOZDEFFAUNUIFPUJFPQAUKUIUJ
      BJZCJZGLZMNZBCRZKUMAHUSUIUJIUEURUMBCUIUJUSDSESBDTCETQUQULMUOUIUPUJGUAUBUS
      UCUFUGUHUD $.
  $}

  ${
    $d B f g k $.  $d C f g k $.  $d H f g k $.  $d M f g k $.  $d X f g k $.
    $d f g k ph $.
    endmndlem.b $e |- B = ( Base ` C ) $.
    endmndlem.h $e |- H = ( Hom ` C ) $.
    endmndlem.o $e |- .x. = ( comp ` C ) $.
    endmndlem.c $e |- ( ph -> C e. Cat ) $.
    endmndlem.x $e |- ( ph -> X e. B ) $.
    endmndlem.m $e |- ( ph -> ( X H X ) = ( Base ` M ) ) $.
    endmndlem.p $e |- ( ph -> ( <. X , X >. .x. X ) = ( +g ` M ) ) $.
    $( A diagonal hom-set in a category equipped with the restriction of the
       composition has a structure of monoid.  See also ~ df-mndtc for
       converting a monoid to a category.  Lemma for ~ bj-endmnd .
       (Contributed by Zhi Wang, 25-Sep-2024.) $)
    endmndlem $p |- ( ph -> M e. Mnd ) $=
      ( vf vg vk cv wcel adantr co cop ccid cfv w3a ccat 3ad2ant1 simp3 catcocl
      simp2 simpr3 simpr2 simpr1 catass eqid catidcl simpr catlid catrid ismndd
      wa ) AOPQGGEUAZGGUBGDUAFGCUCUDZUDMNAORZVBSZPRZVBSZUEBCDVFVDEGGGHIJAVECUFS
      ZVGKUGAVEGBSZVGLUGZVJVJAVEVGUHAVEVGUJUIAVEVGQRZVBSZUEZVABCDVKVFEVDGGGGHIJ
      AVHVMKTAVIVMLTZVNVNAVEVGVLUKAVEVGVLULVNAVEVGVLUMUNABCVCEGHIVCUOZKLUPAVEVA
      ZBCDVCVDEGGHIVOAVHVEKTZAVIVELTZJVRAVEUQZURVPBCDVCVDEGGHIVOVQVRJVRVSUSUT
      $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Opposite category
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    oppccatb.o $e |- O = ( oppCat ` C ) $.
    oppccatb.c $e |- ( ph -> C e. V ) $.
    $( An opposite category is a category.  (Contributed by Zhi Wang,
       23-Oct-2025.) $)
    oppccatb $p |- ( ph -> ( C e. Cat <-> O e. Cat ) ) $=
      ( ccat wcel oppccat coppc cfv eqid cvv chomf wceq 2oppchomf a1i 2oppccomf
      ccomf fvexd catpropd imbitrrid impbid2 ) ABGHZCGHZBCEIUEUDACJKZGHCUFUFLIA
      BUFDMBNKUFNKOABCEPQBSKUFSKOABCERQFACJTUAUBUC $.
  $}

  ${
    $d A x y $.  $d B x y $.  $d X x y $.  $d Y x y $.  $d ph x y $.
    $d ps x y $.
    oppcmndclem.1 $e |- ( ph -> B = { A } ) $.
    $( Lemma for ~ oppcmndc .  Everything is true for two distinct elements in
       a singleton or an empty set (since it is impossible).  Note that if this
       theorem and ~ oppcendc are in ` -. x = y ` form, then both proofs should
       be one step shorter.  (Contributed by Zhi Wang, 16-Oct-2025.) $)
    oppcmndclem $p |- ( ( ph /\ ( X e. B /\ Y e. B ) )
                     -> ( X =/= Y -> ps ) ) $=
      ( vx vy wne wceq wn wcel wa df-ne cv eqeq1 eqeq2 wral wmo mosn moel sylib
      csn syl adantr simprl simprr rspc2dv pm2.24d biimtrid ) EFJEFKZLAEDMZFDMZ
      NZNZBEFOUPULBUPHPZIPZKZULEURKHIEFDDUQEURQURFERAUSIDSHDSZUOAUQDMHTZUTADCUD
      KVAGHDCUAUEHIDUBUCUFAUMUNUGAUMUNUHUIUJUK $.
  $}

  ${
    $d B p q x y $.  $d C p q $.  $d H p q x y $.  $d p ph q x y $.
    oppcendc.o $e |- O = ( oppCat ` C ) $.
    oppcendc.b $e |- B = ( Base ` C ) $.
    ${
      oppcendc.h $e |- H = ( Hom ` C ) $.
      oppcendc.1 $e |- ( ( ph /\ ( x e. B /\ y e. B ) )
                      -> ( x =/= y -> ( x H y ) = (/) ) ) $.
      $( The opposite category of a category whose morphisms are all
         endomorphisms has the same base and hom-sets as the original category.
         (Contributed by Zhi Wang, 16-Oct-2025.) $)
      oppcendc $p |- ( ph -> ( Homf ` C ) = ( Homf ` O ) ) $=
        ( vp vq cv co wceq wral wa c0 weq chomf cfv ctpos wne ralrimivva eqeq12
        wcel necon3bid oveq12 eqeq1d imbi12d rspc2gv mpan9 simprr simprl adantr
        wi equcom bitr4di imp syl21anc wn nne id equcomi oveq12d sylbi eqtr3 ja
        jcad syl eqid homfval 3eqtr4d cxp wfn wb homffn tpossym sylibr oppchomf
        ax-mp eqtr3di ) AEUAUBZUCZWDGUAUBALNZMNZWDOZWGWFWDOZPZMDQLDQZWEWDPZAWJL
        MDDAWFDUGZWGDUGZRZRZWFWGFOZWGWFFOZWHWIWPWFWGUDZWQSPZWRSPZRZUQWQWRPZWPWS
        WTXAABNZCNZUDZXDXEFOZSPZUQZCDQBDQZWOWSWTUQZAXIBCDDKUEZXIXKBCWFWGDDBLTCM
        TRZXFWSXHWTXMXDXEWFWGXDWFXEWGUFUHXMXGWQSXDWFXEWGFUIUJUKULUMWPWNWMXJWSXA
        UQZAWMWNUNZAWMWNUOZAXJWOXLUPWNWMRXJXNXIXNBCWGWFDDBMTCLTRZXFWSXHXAXQXDXE
        WFWGXQBCTMLTLMTZXDWGXEWFUFLMURUSUHXQXGWRSXDWGXEWFFUIUJUKULUTVAVJWSXBXCW
        SVBXRXCWFWGVCXRWFWGWGWFFXRVDLMVEVFVGWQWRSVHVIVKWPDEWDFWFWGWDVLZIJXPXOVM
        WPDEWDFWGWFXSIJXOXPVMVNUEWDDDVOVPWLWKVQDEWDXSIVRLMDWDVSWBVTEWDGHXSWAWC
        $.
    $}

    $d C x y $.  $d O x y $.  $d X x y $.
    oppcmndc.x $e |- ( ph -> B = { X } ) $.
    $( The opposite category of a category whose base set is a singleton or an
       empty set has the same base and hom-sets as the original category.
       (Contributed by Zhi Wang, 16-Oct-2025.) $)
    oppcmndc $p |- ( ph -> ( Homf ` C ) = ( Homf ` O ) ) $=
      ( vx vy chom cfv eqid cv co c0 wceq oppcmndclem oppcendc ) AIJBCCKLZDFGTM
      AINZJNZTOPQEBUAUBHRS $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Monomorphisms and epimorphisms
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d .1. g h z $.  $d B g h z $.  $d C g h z $.  $d H g h z $.  $d X g h z $.
    $d g h ph z $.
    idmon.b $e |- B = ( Base ` C ) $.
    idmon.h $e |- H = ( Hom ` C ) $.
    idmon.i $e |- .1. = ( Id ` C ) $.
    idmon.c $e |- ( ph -> C e. Cat ) $.
    idmon.x $e |- ( ph -> X e. B ) $.
    ${
      idmon.m $e |- M = ( Mono ` C ) $.
      $( An identity arrow, or an identity morphism, is a monomorphism.
         (Contributed by Zhi Wang, 21-Sep-2024.) $)
      idmon $p |- ( ph -> ( .1. ` X ) e. ( X M X ) ) $=
        ( vg vz vh co wcel cv wral cfv cop cco wceq wi catidcl wa adantr simpr1
        w3a ccat eqid simpr2 catlid simpr3 eqeq12d biimpd ralrimivvva mpbir2and
        ismon2 ) AGDUAZGGFQRVAGGEQRVANSZOSZGUBGCUCUAZQZQZVAPSZVEQZUDZVBVGUDZUEZ
        PVCGEQZTNVLTOBTABCDEGHIJKLUFAVKONPBVLVLAVCBRZVBVLRZVGVLRZUJZUGZVIVJVQVF
        VBVHVGVQBCVDDVBEVCGHIJACUKRVPKUHZAVMVNVOUIZVDULZAGBRVPLUHZAVMVNVOUMUNVQ
        BCVDDVGEVCGHIJVRVSVTWAAVMVNVOUOUNUPUQURAOBCVDNPVAEFGGHIVTMKLLUTUS $.
    $}

    ${
      idepi.e $e |- E = ( Epi ` C ) $.
      $( An identity arrow, or an identity morphism, is an epimorphism.
         (Contributed by Zhi Wang, 21-Sep-2024.) $)
      idepi $p |- ( ph -> ( .1. ` X ) e. ( X E X ) ) $=
        ( vg vz vh co wcel cv wral cfv cop cco wceq wi catidcl w3a wa ccat eqid
        adantr simpr1 simpr2 catrid simpr3 eqeq12d biimpd ralrimivvva mpbir2and
        isepi2 ) AGDUAZGGEQRVAGGFQRNSZVAGGUBOSZCUCUAZQZQZPSZVAVEQZUDZVBVGUDZUEZ
        PGVCFQZTNVLTOBTABCDFGHIJKLUFAVKONPBVLVLAVCBRZVBVLRZVGVLRZUGZUHZVIVJVQVF
        VBVHVGVQBCVDDVBFGVCHIJACUIRVPKUKZAGBRVPLUKZVDUJZAVMVNVOULZAVMVNVOUMUNVQ
        BCVDDVGFGVCHIJVRVSVTWAAVMVNVOUOUNUPUQURAOBCVDNPEVAFGGHIVTMKLLUTUS $.
    $}
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Sections, inverses, isomorphisms
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d B x y $.  $d C c f g h x y $.  $d f g ph x y $.
    sectrcl.s $e |- S = ( Sect ` C ) $.
    sectrcl.f $e |- ( ph -> F ( X S Y ) G ) $.
    $( Reverse closure for section relations.  (Contributed by Zhi Wang,
       14-Nov-2025.) $)
    sectrcl $p |- ( ph -> C e. Cat ) $=
      ( vx vc vy vf vh vg co cv cfv wcel c0 wbr csect wex ccat wne df-br eleq2i
      cop df-ov bitri elfvne0 sylbi neeq1i n0 sylib cbs cco ccid wceq chom wsbc
      wa copab cmpo df-sect mptrcl exlimiv 3syl ) ADEFGCPZUAZJQZBUBRZSZJUCZBUDS
      ZIVJCTUEZVNVJDEUHZFGUHZCRZSZVPVJVQVISVTDEVIUFVIVSVQFGCUIUGUJVQVRCUKULVPVL
      TUEVNCVLTHUMJVLUNUJUOVMVOJKUDJLKQZUPRZWBMQZVKLQZNQZPSOQZWDVKWEPSVBWFWCVKW
      DUHVKWAUQRPPVKWAURRRUSVBNWAUTRVAMOVCVDUBVKBJLMONKVEVFVGVH $.

    sectrcl2.b $e |- B = ( Base ` C ) $.
    $( Reverse closure for section relations.  (Contributed by Zhi Wang,
       14-Nov-2025.) $)
    sectrcl2 $p |- ( ph -> ( X e. B /\ Y e. B ) ) $=
      ( vx vy vf vg cv cfv co wcel eqid cop chom cco ccid wceq copab cmpo df-br
      wa wbr sylib sectrcl sectffval oveqd eleqtrd elmpocl syl ) AEFUAZGHLMBBNP
      ZLPZMPZCUBQZRSOPZVAUTVBRSUIVCUSUTVAUAUTCUCQZRRUTCUDQZQUEUINOUFZUGZRZSGBSH
      BSUIAURGHDRZVHAEFVIUJURVISJEFVIUHUKADVGGHALMBCDVDVENOVBKVBTVDTVETIACDEFGH
      IJULUMUNUOLMBBVFGHVGURVGTUPUQ $.
  $}

  ${
    $d B x y $.  $d C c x y $.  $d ph x y $.
    invrcl.n $e |- N = ( Inv ` C ) $.
    invrcl.f $e |- ( ph -> F ( X N Y ) G ) $.
    $( Reverse closure for inverse relations.  (Contributed by Zhi Wang,
       14-Nov-2025.) $)
    invrcl $p |- ( ph -> C e. Cat ) $=
      ( vx vc vy co cv cinv cfv wcel ccat c0 wne wbr wex cop df-br df-ov eleq2i
      bitri elfvne0 sylbi neeq1i n0 sylib cbs csect ccnv cin cmpo df-inv mptrcl
      exlimiv 3syl ) ACDFGEMZUAZJNZBOPZQZJUBZBRQZIVCESTZVGVCCDUCZFGUCZEPZQZVIVC
      VJVBQVMCDVBUDVBVLVJFGEUEUFUGVJVKEUHUIVIVESTVGEVESHUJJVEUKUGULVFVHJKRJLKNZ
      UMPZVOVDLNZVNUNPZMVPVDVQMUOUPUQOVDBJLKURUSUTVA $.

    invrcl2.b $e |- B = ( Base ` C ) $.
    $( Reverse closure for inverse relations.  (Contributed by Zhi Wang,
       14-Nov-2025.) $)
    invrcl2 $p |- ( ph -> ( X e. B /\ Y e. B ) ) $=
      ( vx vy cop cv csect cfv co wcel eqid ccnv cin cmpo wa df-br sylib invrcl
      wbr invffval oveqd eleqtrd elmpocl syl ) ADENZGHLMBBLOZMOZCPQZRUPUOUQRUAU
      BZUCZRZSGBSHBSUDAUNGHFRZUTADEVAUHUNVASJDEVAUEUFAFUSGHALMBCUQFKIACDEFGHIJU
      GUQTUIUJUKLMBBURGHUSUNUSTULUM $.
  $}

  ${
    isinv2.n $e |- N = ( Inv ` C ) $.
    isinv2.s $e |- S = ( Sect ` C ) $.
    $( The property " ` F ` is an inverse of ` G ` ".  (Contributed by Zhi
       Wang, 14-Nov-2025.) $)
    isinv2 $p |- ( F ( X N Y ) G <-> ( F ( X S Y ) G /\ G ( Y S X ) F ) ) $=
      ( co wbr ccat wcel cbs cfv wa id invrcl jca simpl invrcl2 sectrcl2 simprl
      eqid sectrcl simprr isinv pm5.21nii ) CDFGEJKZALMZFANOZMZGUKMZPZPZCDFGBJK
      ZDCGFBJKZPZUIUJUNUIACDEFGHUIQZRUIUKACDEFGHUSUKUDZUASURUJUNURABCDFGIUPUQTZ
      UEURUKABCDFGIVAUTUBSUOUKABCDEFGUTHUJUNTUJULUMUCUJULUMUFIUGUH $.
  $}

  ${
    $d .1. g $.  $d .x. g $.  $d B g $.  $d C g $.  $d F g $.  $d G g $.
    $d H g $.  $d I g $.  $d X g $.  $d Y g $.  $d g ph $.
    isisod.b $e |- B = ( Base ` C ) $.
    isisod.h $e |- H = ( Hom ` C ) $.
    isisod.o $e |- .x. = ( comp ` C ) $.
    isisod.i $e |- I = ( Iso ` C ) $.
    isisod.1 $e |- .1. = ( Id ` C ) $.
    isisod.c $e |- ( ph -> C e. Cat ) $.
    isisod.x $e |- ( ph -> X e. B ) $.
    isisod.y $e |- ( ph -> Y e. B ) $.
    isisod.f $e |- ( ph -> F e. ( X H Y ) ) $.
    isisod.g $e |- ( ph -> G e. ( Y H X ) ) $.
    isisod.gf $e |- ( ph -> ( G ( <. X , Y >. .x. X ) F ) = ( .1. ` X ) ) $.
    isisod.fg $e |- ( ph -> ( F ( <. Y , X >. .x. Y ) G ) = ( .1. ` Y ) ) $.
    $( The predicate "is an isomorphism" (deduction form).  (Contributed by Zhi
       Wang, 16-Sep-2025.) $)
    isisod $p |- ( ph -> F e. ( X I Y ) ) $=
      ( vg co wcel cv cop cfv wceq wa wrex oveq1d eqeq1d oveq2d anbi12d rspcedv
      simpr mp2and cco oveqi dfiso2 mpbird ) AFJKIUEUFUDUGZFJKUHZJDUEZUEZJEUIZU
      JZFVDKJUHZKDUEZUEZKEUIZUJZUKZUDKJHUEZULZAGFVFUEZVHUJZFGVKUEZVMUJZVQUBUCAV
      OVSWAUKUDGVPUAAVDGUJZUKZVIVSVNWAWCVGVRVHWCVDGFVFAWBURZUMUNWCVLVTVMWCVDGFV
      KWDUOUNUPUQUSABCEUDFHIVKJKVFLMQORSTPDCUTUIZVEJNVADWEVJKNVAVBVC $.
  $}

  ${
    $d .x. k $.  $d C k $.  $d F k $.  $d G k $.  $d H k $.  $d X k $.
    $d Y k $.  $d Z k $.  $d k ph $.
    upeu2lem.b $e |- B = ( Base ` C ) $.
    upeu2lem.h $e |- H = ( Hom ` C ) $.
    upeu2lem.o $e |- .x. = ( comp ` C ) $.
    upeu2lem.i $e |- I = ( Iso ` C ) $.
    upeu2lem.c $e |- ( ph -> C e. Cat ) $.
    upeu2lem.x $e |- ( ph -> X e. B ) $.
    upeu2lem.y $e |- ( ph -> Y e. B ) $.
    upeu2lem.z $e |- ( ph -> Z e. B ) $.
    upeu2lem.f $e |- ( ph -> F e. ( X I Y ) ) $.
    upeu2lem.g $e |- ( ph -> G e. ( X H Z ) ) $.
    $( Lemma for ~ upeu2 .  There exists a unique morphism from ` Y ` to ` Z `
       that commutes if ` F : X --> Y ` is an isomorphism.  (Contributed by Zhi
       Wang, 20-Sep-2025.) $)
    upeu2lem $p |- ( ph -> E! k e. ( Y H Z )
            G = ( k ( <. X , Y >. .x. Z ) F ) ) $=
      ( cinv cfv co wcel cv wceq wb wral wreu isohom eqid invf ffvelcdmd sseldd
      cop catcocl wa oveq1 adantl ccid adantr simpr catass cco oveqi isocoinvid
      oveq2d catrid 3eqtrd eqtr2d invcoisoid impbida ralrimiva reu6i syl2anc
      ccat ) AGFJKCUCUDZUEZUDZKJUQZLDUEZUEZKLHUEZUFGEUGZFJKUQZLDUEZUEZUHZWFWDUH
      ZUIZEWEUJWJEWEUKABCDWAGHKJLMNOQSRTAKJIUEZKJHUEZWAABCHIKJMNPQSRULAJKIUEZWM
      FVTABCIVSJKMVSUMZQRSPUNUAUOUPZUBURAWLEWEAWFWEUFZUSZWJWKWSWJUSWDWIWAWCUEZW
      FWJWDWTUHWSGWIWAWCUTVAWSWTWFUHWJWSWTWFFWAWBKDUEZUEZKKUQLDUEZUEWFKCVBUDZUD
      ZXCUEWFWSBCDWAFHWFLKJKMNOACVRUFWRQVCZAKBUFWRSVCZAJBUFWRRVCZXGAWAWNUFWRWQV
      CZAFJKHUEZUFWRAWOXJFABCHIJKMNPQRSULUAUPVCZALBUFWRTVCZAWRVDZVEWSXBXEWFXCWS
      BCXDFIVSJKXAMPWPXFXHXGAFWOUFWRUAVCZXDUMZDCVFUDZWBKOVGVHVIWSBCDXDWFHKLMNXO
      XFXGOXLXMVJVKVCVLWSWKUSWIWDFWHUEZGWKWIXQUHWSWFWDFWHUTVAWSXQGUHWKWSXQGWAFW
      GJDUEZUEZJJUQLDUEZUEGJXDUDZXTUEGWSBCDFWAHGLJKJMNOXFXHXGXHXKXIXLAGJLHUEUFW
      RUBVCZVEWSXSYAGXTWSBCXDFIVSJKXRMPWPXFXHXGXNXODXPWGJOVGVMVIWSBCDXDGHJLMNXO
      XFXHOXLYBVJVKVCVLVNVOWJEWEWDVPVQ $.
  $}

  ${
    $d C f g x y $.
    $( The function value of the function returning the sections of a category
       is a function over the Cartesian square of the base set of the category.
       (Contributed by Zhi Wang, 27-Oct-2025.) $)
    sectfn $p |- ( C e. Cat
                  -> ( Sect ` C ) Fn ( ( Base ` C ) X. ( Base ` C ) ) ) $=
      ( vx vy vf vg ccat wcel csect cfv cbs cxp wfn cv chom co wa cop eqid ovex
      cco ccid wceq copab cmpo opabssxp ssexi fnmpoi id sectffval fneq1d mpbiri
      xpex ) AFGZAHIZAJIZUOKZLBCUOUODMZBMZCMZANIZOZGEMZUSURUTOZGPVBUQURUSQURATI
      ZOOURAUAIZIUBZPDEUCZUDZUPLBCUOUOVGVHVHRVGVAVCKVAVCURUSUTSUSURUTSULVFDEVAV
      CUEUFUGUMUPUNVHUMBCUOAUNVDVEDEUTUORUTRVDRVERUNRUMUHUIUJUK $.
  $}

  ${
    $d C c x y $.
    $( The function value of the function returning the inverses of a category
       is a function over the Cartesian square of the base set of the category.
       Simplifies ~ isofn (see ~ isofnALT ).  (Contributed by Zhi Wang,
       27-Oct-2025.) $)
    invfn $p |- ( C e. Cat
                  -> ( Inv ` C ) Fn ( ( Base ` C ) X. ( Base ` C ) ) ) $=
      ( vx vy vc ccat wcel cinv cfv cbs wfn cv csect co ccnv cin cmpo cvv fveq2
      wral wa cxp ovex inex1 a1i ralrimivva eqid fnmpo df-inv wceq oveqd cnveqd
      syl ineq12d mpoeq123dv id fvex pm3.2i mpoexga mp1i fvmptd3 fneq1d mpbird
      ) AEFZAGHZAIHZVEUAZJBCVEVEBKZCKZALHZMZVHVGVIMZNZOZPZVFJZVCVMQFZCVESBVESVO
      VCVPBCVEVEVPVCVGVEFVHVEFTTVJVLVGVHVIUBUCUDUEBCVEVEVMVNQVNUFUGULVCVFVDVNVC
      DABCDKZIHZVRVGVHVQLHZMZVHVGVSMZNZOZPVNEGQBCDUHVQAUIZBCVRVRWCVEVEVMVQAIRZW
      EWDVTVJWBVLWDVSVIVGVHVQALRZUJWDWAVKWDVSVIVHVGWFUJUKUMUNVCUOVEQFZWGTVNQFVC
      WGWGAIUPZWHUQBCVEVEVMQQURUSUTVAVB $.

    $( The function value of the function returning the isomorphisms of a
       category is a function over the Cartesian square of the base set of the
       category.  (Contributed by AV, 5-Apr-2020.)  (Proof shortened by Zhi
       Wang, 3-Nov-2025.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    isofnALT $p |- ( C e. Cat
                  -> ( Iso ` C ) Fn ( ( Base ` C ) X. ( Base ` C ) ) ) $=
      ( vx ccat wcel ciso cfv cbs cxp wfn cvv cdm cmpt cinv ccom crn wral dmexg
      cv wss adantl ralrimiva eqid fnmpt syl invfn ssv a1i fnco syl3anc isofval
      fneq1d mpbird ) ACDZAEFZAGFZUOHZIBJBRZKZLZAMFZNZUPIZUMUSJIZUTUPIUTOZJSZVB
      UMURJDZBJPVCUMVFBJUQJDVFUMUQJQTUABJURUSJUSUBUCUDAUEVEUMVDUFUGJUPUSUTUHUIU
      MUPUNVABAUJUKUL $.
  $}

  ${
    $d B x y $.  $d I x y $.  $d ph x y $.
    isofval2.b $e |- B = ( Base ` C ) $.
    isofval2.n $e |- N = ( Inv ` C ) $.
    isofval2.c $e |- ( ph -> C e. Cat ) $.
    isofval2.i $e |- I = ( Iso ` C ) $.
    $( Function value of the function returning the isomorphisms of a category.
       (Contributed by Zhi Wang, 27-Oct-2025.) $)
    isofval2 $p |- ( ph -> I = ( x e. B , y e. B |-> dom ( x N y ) ) ) $=
      ( cv co cmpo cdm ccat wcel cxp wfn cfv wceq ciso cbs isofn fneq1i xpeq12i
      fneq2i bitri sylibr fnov sylib syl w3a simp2 simp3 isoval mpoeq3dva eqtrd
      3ad2ant1 ) AFBCDDBLZCLZFMZNZBCDDUTVAGMOZNAEPQZFVCUAZJVEFDDRZSZVFVEEUBTZEU
      CTZVJRZSZVHEUDVHVIVGSVLVGFVIKUEVGVKVIDVJDVJHHUFUGUHUIBCDDFUJUKULABCDDVBVD
      AUTDQZVADQZUMDEFGUTVAHIAVMVEVNJUSAVMVNUNAVMVNUOKUPUQUR $.
  $}

  ${
    $d B x y $.  $d C c x $.  $d I x y $.  $d ph x y $.
    isorcl.i $e |- I = ( Iso ` C ) $.
    isorcl.f $e |- ( ph -> F e. ( X I Y ) ) $.
    $( Reverse closure for isomorphism relations.  (Contributed by Zhi Wang,
       17-Nov-2025.) $)
    isorcl $p |- ( ph -> C e. Cat ) $=
      ( vx vc co wcel cv ciso cfv wex ccat c0 wne cop df-ov eleq2s neeq1i bitri
      elfvne0 n0 sylib cvv cdm cmpt cinv ccom df-iso mptrcl exlimiv 3syl ) ACEF
      DKZLZIMZBNOZLZIPZBQLZHURDRSZVBVDCEFTZDOUQCVEDUEEFDUAUBVDUTRSVBDUTRGUCIUTU
      FUDUGVAVCIJQIUHUSUIUJJMUKOULNUSBIJUMUNUOUP $.

    isorcl2.b $e |- B = ( Base ` C ) $.
    $( Reverse closure for isomorphism relations.  (Contributed by Zhi Wang,
       17-Nov-2025.) $)
    isorcl2 $p |- ( ph -> ( X e. B /\ Y e. B ) ) $=
      ( vx vy cv cinv cfv co cdm cmpo wcel eqid isorcl isofval2 eleqtrd elmpocl
      wa oveqd syl ) ADFGKLBBKMLMCNOZPQZRZPZSFBSGBSUEADFGEPUKIAEUJFGAKLBCEUHJUH
      TACDEFGHIUAHUBUFUCKLBBUIFGUJDUJTUDUG $.
  $}

  ${
    $d C f g $.  $d I f g $.  $d N f g $.  $d X f g $.  $d Y f g $.
    isoval2.n $e |- N = ( Inv ` C ) $.
    isoval2.i $e |- I = ( Iso ` C ) $.
    $( The isomorphisms are the domain of the inverse relation.  (Contributed
       by Zhi Wang, 17-Nov-2025.) $)
    isoval2 $p |- ( X I Y ) = dom ( X N Y ) $=
      ( vf vg co cdm cv wcel id cbs cfv eqid isorcl simpld simprd isoval invrcl
      isorcl2 eleqtrd wbr wex eldm invrcl2 inviso1 exlimiv sylbi impbii eqriv
      vex ) HDEBJZDECJZKZHLZUOMZURUQMZUSURUOUQUSNZUSAOPZABCDEVBQZFUSAURBDEGVARU
      SDVBMZEVBMZUSVBAURBDEGVAVCUCZSUSVDVEVFTGUAUDUTURILZUPUEZIUFUSIURUPHUNUGVH
      USIVHVBAURVGBCDEVCFVHAURVGCDEFVHNZUBVHVDVEVHVBAURVGCDEFVIVCUHZSVHVDVEVJTG
      VIUIUJUKULUM $.
  $}

  ${
    $d C c f g h x y z $.  $d D c f g h x y z $.  $d P c f g h x y z $.
    $d c f g h ph x y z $.
    sectpropd.1 $e |- ( ph -> ( Homf ` C ) = ( Homf ` D ) ) $.
    sectpropd.2 $e |- ( ph -> ( comf ` C ) = ( comf ` D ) ) $.
    $( Lemma for ~ sectpropd .  (Contributed by Zhi Wang, 27-Oct-2025.) $)
    sectpropdlem $p |- ( ( ph /\ P e. ( Sect ` C ) ) -> P e. ( Sect ` D ) ) $=
      ( vx vy vf vg cfv wcel wa cv co wceq eqid adantr eleq2d anbi12d c1st c2nd
      vz vc vh csect cop cbs chom cco ccid copab coprab simpr cmpo ccat df-sect
      mptrcl adantl sectffval df-mpo eqtrdi eleqtrd eloprab1st2nd syl wbr chomf
      wsbc ccomf eleq1 anbi1d oveq1 oveq2 opeq1 id oveq12d oveqd fveq2 opabbidv
      eqeq12d eqeq2d anbi2d opeq2 oveq1d eqeq1d eloprabi simplld simplrd simprl
      simprr comfeqval cvv homfeqbas elfvexd cidpropd fveq1d pm5.32da homfeqval
      eqeq1 bitrd simprd catpropd mpbid sectfval 3eqtr4rd cxp wb sectfn fnbrovb
      wfn syl12anc df-br sylib eqeltrd ) ADBUFKZLZMZDDUAKZUAKZXRUBKZUGZDUBKZUGZ
      CUFKZXQDGNZBUHKZLZHNZYFLZMZUCNZINZYEYHBUIKZOZLZJNZYHYEYMOZLZMZYPYLYEYHUGZ
      YEBUJKZOZOZYEBUKKZKZPZMZIJULZPZMZGHUCUMZLZDYCPXQDXOUUKAXPUNXQXOGHYFYFUUHU
      OUUKXQGHYFBXOUUAUUDIJYMYFQZYMQZUUAQZUUDQXOQXPBUPLZAUDUPGHUDNZUHKZUURYLYEY
      HUENZOLYPYHYEUUSOLMYPYLYTYEUUQUJKOOYEUUQUKKKPMUEUUQUIKVHIJULUOUFDBGHIJUEU
      DUQURUSZUTGHUCYFYFUUHVAVBVCZUUJGHUCDVDVEXQYAYBYDVFZYCYDLXQXSXTYDOZYBPZUVB
      XQYLXSXTYMOZLZYPXTXSYMOZLZMZYPYLYAXSUUAOZOZXSUUDKZPZMZIJULZYLXSXTCUIKZOZL
      ZYPXTXSUVPOZLZMZYPYLYAXSCUJKZOOZXSCUKKZKZPZMZIJULYBUVCXQUVNUWGIJXQUVNUVIU
      WFMUWGXQUVIUVMUWFXQUVIMZUVKUWCUVLUWEUWHYFBCUWBUUAYLYPYMXSXTXSUUMUUNUUOUWB
      QZXQBVGKCVGKPZUVIAUWJXPERZRXQBVIKCVIKPZUVIAUWLXPFRZRXQXSYFLZUVIXQUWNXTYFL
      ZYBUVOPZXQUULUWNUWOMZUWPMZUVAUUJUWNYIMZYKYLXSYHYMOZLZYPYHXSYMOZLZMZYPYLXS
      YHUGZXSUUAOZOZUVLPZMZIJULZPZMUWQYKUVOPZMUWRGHUCDYEXSPZYJUWSUUIUXKUXMYGUWN
      YIYEXSYFVJVKUXMUUHUXJYKUXMUUGUXIIJUXMYSUXDUUFUXHUXMYOUXAYRUXCUXMYNUWTYLYE
      XSYHYMVLSUXMYQUXBYPYEXSYHYMVMSTUXMUUCUXGUUEUVLUXMUUBUXFYPYLUXMYTUXEYEXSUU
      AYEXSYHVNUXMVOVPVQYEXSUUDVRVTTVSWATYHXTPZUWSUWQUXKUXLUXNYIUWOUWNYHXTYFVJW
      BUXNUXJUVOYKUXNUXIUVNIJUXNUXDUVIUXHUVMUXNUXAUVFUXCUVHUXNUWTUVEYLYHXTXSYMV
      MSUXNUXBUVGYPYHXTXSYMVLSTUXNUXGUVKUVLUXNUXFUVJYPYLUXNUXEYAXSUUAYHXTXSWCWD
      VQWETVSWATYKYBPUXLUWPUWQYKYBUVOWSWBWFVEZWGZRZXQUWOUVIXQUWNUWOUWPUXOWHZRUX
      QXQUVFUVHWIXQUVFUVHWJWKXQUVLUWEPUVIXQXSUUDUWDXQBCUPWLUWKUWMUUTXQXSUHCXQXS
      YFCUHKZUXPXQBCUWKWMZVCZWNZWOWPRVTWQXQUVIUWAUWFXQUVFUVRUVHUVTXQUVEUVQYLXQY
      FBCYMUVPXSXTUUMUUNUVPQZUWKUXPUXRWRSXQUVGUVSYPXQYFBCYMUVPXTXSUUMUUNUYCUWKU
      XRUXPWRSTVKWTVSXQUWQUWPUXOXAXQUXSCYDUWBUWDIJUVPXSXTUXSQUYCUWIUWDQYDQXQUUP
      CUPLZUUTXQBCUPWLUWKUWMUUTUYBXBXCZUYAXQXTYFUXSUXRUXTVCZXDXEXQYDUXSUXSXFXJZ
      XSUXSLXTUXSLUVDUVBXGXQUYDUYGUYECXHVEUYAUYFXSXTYBYDUXSUXSXIXKXCYAYBYDXLXMX
      N $.

    $( Two structures with the same base, hom-sets and composition operation
       have the same sections.  (Contributed by Zhi Wang, 27-Oct-2025.) $)
    sectpropd $p |- ( ph -> ( Sect ` C ) = ( Sect ` D ) ) $=
      ( vf csect cfv cv wcel sectpropdlem chomf eqcomd ccomf impbida eqrdv ) AF
      BGHZCGHZAFIZQJSRJABCSDEKACBSABLHCLHDMABNHCNHEMKOP $.

    $( Lemma for ~ invpropd .  (Contributed by Zhi Wang, 27-Oct-2025.) $)
    invpropdlem $p |- ( ( ph /\ P e. ( Inv ` C ) ) -> P e. ( Inv ` D ) ) $=
      ( vx vy vz cfv wcel wa cv cbs co ccnv cin wceq eqid ccat vc cinv c1st cop
      c2nd csect coprab simpr cmpo df-inv mptrcl adantl invffval df-mpo eleqtrd
      eqtrdi eloprab1st2nd syl chomf adantr ccomf sectpropd oveqd ineq12d eleq1
      wbr cnveqd anbi1d oveq1 oveq2 eqeq2d anbi12d anbi2d eqeq1 eloprabi simprd
      cvv simplld homfeqbas elfvexd catpropd mpbid simplrd invfval 3eqtr4rd cxp
      wfn wb invfn fnbrovb syl12anc df-br sylib eqeltrd ) ADBUBJZKZLZDDUCJZUCJZ
      WRUEJZUDZDUEJZUDZCUBJZWQDGMZBNJZKZHMZXFKZLZIMZXEXHBUFJZOZXHXEXLOZPZQZRZLZ
      GHIUGZKZDXCRWQDWOXSAWPUHWQWOGHXFXFXPUIXSWQGHXFBXLWOXFSWOSWPBTKZAUATGHUAMZ
      NJZYCXEXHYBUFJZOXHXEYDOPQUIUBDBGHUAUJUKULZXLSUMGHIXFXFXPUNUPUOZXRGHIDUQUR
      WQXAXBXDVFZXCXDKWQWSWTXDOZXBRZYGWQWSWTXLOZWTWSXLOZPZQZWSWTCUFJZOZWTWSYNOZ
      PZQXBYHWQYJYOYLYQWQXLYNWSWTWQBCABUSJCUSJRWPEUTZABVAJCVAJRWPFUTZVBZVCWQYKY
      PWQXLYNWTWSYTVCVGVDWQWSXFKZWTXFKZLZXBYMRZWQXTUUCUUDLZYFXRUUAXILZXKWSXHXLO
      ZXHWSXLOZPZQZRZLUUCXKYMRZLUUEGHIDXEWSRZXJUUFXQUUKUUMXGUUAXIXEWSXFVEVHUUMX
      PUUJXKUUMXMUUGXOUUIXEWSXHXLVIUUMXNUUHXEWSXHXLVJVGVDVKVLXHWTRZUUFUUCUUKUUL
      UUNXIUUBUUAXHWTXFVEVMUUNUUJYMXKUUNUUGYJUUIYLXHWTWSXLVJUUNUUHYKXHWTWSXLVIV
      GVDVKVLXKXBRUULUUDUUCXKXBYMVNVMVOURZVPWQCNJZCYNXDWSWTUUPSXDSWQYACTKZYEWQB
      CTVQYRYSYEWQWSNCWQWSXFUUPWQUUAUUBUUDUUOVRWQBCYRVSZUOZVTWAWBZUUSWQWTXFUUPW
      QUUAUUBUUDUUOWCUURUOZYNSWDWEWQXDUUPUUPWFWGZWSUUPKWTUUPKYIYGWHWQUUQUVBUUTC
      WIURUUSUVAWSWTXBXDUUPUUPWJWKWBXAXBXDWLWMWN $.

    $( Two structures with the same base, hom-sets and composition operation
       have the same inverses.  (Contributed by Zhi Wang, 27-Oct-2025.) $)
    invpropd $p |- ( ph -> ( Inv ` C ) = ( Inv ` D ) ) $=
      ( vf cinv cfv cv wcel invpropdlem chomf eqcomd ccomf impbida eqrdv ) AFBG
      HZCGHZAFIZQJSRJABCSDEKACBSABLHCLHDMABNHCNHEMKOP $.

    $( Lemma for ~ isopropd .  (Contributed by Zhi Wang, 27-Oct-2025.) $)
    isopropdlem $p |- ( ( ph /\ P e. ( Iso ` C ) ) -> P e. ( Iso ` D ) ) $=
      ( vx vy vz vc ciso cfv wcel wa cv co cdm wceq eqid ccat c1st c2nd cop cbs
      cinv coprab simpr cmpo cvv cmpt ccom df-iso mptrcl adantl isofval2 df-mpo
      eqtrdi eleqtrd eloprab1st2nd syl wbr chomf adantr ccomf oveqd dmeqd eleq1
      invpropd anbi1d oveq1 eqeq2d anbi12d anbi2d oveq2 eloprabi simprd simplld
      eqeq1 homfeqbas elfvexd catpropd mpbid simplrd isoval 3eqtr4rd cxp wfn wb
      isofn fnbrovb syl12anc df-br sylib eqeltrd ) ADBKLZMZNZDDUALZUALZWRUBLZUC
      ZDUBLZUCZCKLZWQDGOZBUDLZMZHOZXFMZNZIOZXEXHBUELZPZQZRZNZGHIUFZMZDXCRWQDWOX
      QAWPUGWQWOGHXFXFXNUHXQWQGHXFBWOXLXFSXLSWPBTMZAJTGUIXEQUJJOUELUKKDBGJULUMU
      NZWOSUOGHIXFXFXNUPUQURZXPGHIDUSUTWQXAXBXDVAZXCXDMWQWSWTXDPZXBRZYBWQWSWTXL
      PZQZWSWTCUELZPZQXBYCWQYEYHWQXLYGWSWTWQBCABVBLCVBLRWPEVCZABVDLCVDLRWPFVCZV
      HVEVFWQWSXFMZWTXFMZNZXBYFRZWQXRYMYNNZYAXPYKXINZXKWSXHXLPZQZRZNYMXKYFRZNYO
      GHIDXEWSRZXJYPXOYSUUAXGYKXIXEWSXFVGVIUUAXNYRXKUUAXMYQXEWSXHXLVJVFVKVLXHWT
      RZYPYMYSYTUUBXIYLYKXHWTXFVGVMUUBYRYFXKUUBYQYEXHWTWSXLVNVFVKVLXKXBRYTYNYMX
      KXBYFVRVMVOUTZVPWQCUDLZCXDYGWSWTUUDSYGSWQXSCTMZXTWQBCTUIYIYJXTWQWSUDCWQWS
      XFUUDWQYKYLYNUUCVQWQBCYIVSZURZVTWAWBZUUGWQWTXFUUDWQYKYLYNUUCWCUUFURZXDSWD
      WEWQXDUUDUUDWFWGZWSUUDMWTUUDMYDYBWHWQUUEUUJUUHCWIUTUUGUUIWSWTXBXDUUDUUDWJ
      WKWBXAXBXDWLWMWN $.

    $( Two structures with the same base, hom-sets and composition operation
       have the same isomorphisms.  (Contributed by Zhi Wang, 27-Oct-2025.) $)
    isopropd $p |- ( ph -> ( Iso ` C ) = ( Iso ` D ) ) $=
      ( vf ciso cfv cv wcel isopropdlem chomf eqcomd ccomf impbida eqrdv ) AFBG
      HZCGHZAFIZQJSRJABCSDEKACBSABLHCLHDMABNHCNHEMKOP $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Isomorphic objects
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( ` ~=c ` is a function on ` Cat ` .  (Contributed by Zhi Wang,
     26-Oct-2025.) $)
  cicfn $p |- ~=c Fn Cat $=
    ( vc ccat cv ciso cfv c0 csupp co ccic ovex df-cic fnmpti ) ABACDEZFGHIMFGJ
    AKL $.

  $( Isomorphism implies the structure being a category.  (Contributed by Zhi
     Wang, 26-Oct-2025.) $)
  cicrcl2 $p |- ( R ( ~=c ` C ) S -> C e. Cat ) $=
    ( ccic cfv wbr cop wcel ccat df-br cdm elfvdm cicfn fndmi eleqtrdi sylbi )
    BCADEZFBCGZQHZAIHBCQJSADKIRADLIDMNOP $.

  ${
    oppccic.o $e |- O = ( oppCat ` C ) $.
    oppccic.i $e |- ( ph -> R ( ~=c ` C ) S ) $.
    $( Isomorphic objects are isomorphic in the opposite category.
       (Contributed by Zhi Wang, 26-Oct-2025.) $)
    oppccic $p |- ( ph -> R ( ~=c ` O ) S ) $=
      ( ccat wcel ccic cfv wbr syl ciso co c0 wne eqid syl2anc brcic cbs cicrcl
      cicrcl2 oppccat ciclcl oppciso neeq1d oppcbas 3bitr4rd mpbid cicsym ) AEH
      IZDCEJKZLZCDUMLABHIZULACDBJKLZUOGBCDUCMZBEFUDMZAUPUNGADCENKZOZPQCDBNKZOZP
      QUNUPAUTVBPABUAKZBVAUSEDCVCRZFUQAUOUPDVCIUQGBCDUBSZAUOUPCVCIUQGBCDUESZVAR
      ZUSRZUFUGAVCEUSDCVHVCBEFVDUHURVEVFTAVCBVACDVGVDUQVFVETUIUJEDCUKS $.
  $}

  ${
    $d C f x y $.
    $( The set of isomorphic objects is a relation.  Simplifies ~ cicer (see
       ~ cicerALT ).  (Contributed by Zhi Wang, 27-Oct-2025.) $)
    relcic $p |- ( C e. Cat -> Rel ( ~=c ` C ) ) $=
      ( vf vx vy ccat wcel ccic cfv wrel ciso c0 csupp cv wne cbs releqd mpbird
      a1i wceq cvv cxp crab cop w3a copab relopab fveq2 neeq1d rabxp isofn fvex
      co wfn sqxpexg mp1i 0ex suppvalfn syl3anc cicfval ) AEFZAGHZIAJHZKLULZIZU
      TVDBMZVBHZKNZBAOHZVHUAZUBZIZUTVKCMZVHFDMZVHFVLVMUCZVBHZKNZUDZCDUEZIZVSUTV
      QCDUFRUTVJVRVJVRSUTVGVPBCDVHVHVEVNSVFVOKVEVNVBUGUHUIRPQUTVCVJUTVBVIUMVITF
      ZKTFZVCVJSAUJVHTFVTUTAOUKVHTUNUOWAUTUPRBVBTTVIKUQURPQUTVAVCAUSPQ $.
  $}

  ${
    $d C x y z $.
    $( Isomorphism is an equivalence relation on objects of a category.  Remark
       3.16 in [Adamek] p. 29.  (Contributed by AV, 5-Apr-2020.)  (Proof
       shortened by Zhi Wang, 3-Nov-2025.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    cicerALT $p |- ( C e. Cat -> ( ~=c ` C ) Er ( Base ` C ) ) $=
      ( vx vy vz ccat wcel cbs cfv ccic relcic cv cicsym wbr cictr 3expb cicref
      ciclcl impbida iserd ) AEFZBCDAGHZAIHZAJABKZCKZLTUCUDUBMUDDKZUBMUCUEUBMAU
      CUDUENOTUCUAFUCUCUBMAUCPAUCUCQRS $.
  $}

  $( Reconstruction of a pair of isomorphic objects in terms of its ordered
     pair components.  (Contributed by Zhi Wang, 27-Oct-2025.) $)
  cic1st2nd $p |- ( P e. ( ~=c ` C )
                 -> P = <. ( 1st ` P ) , ( 2nd ` P ) >. ) $=
    ( ccic cfv wrel wcel c1st c2nd wceq ccat elfvdm cicfn fndmi eleqtrdi relcic
    cop cdm syl 1st2nd mpancom ) ACDZEZBUAFZBBGDBHDPIUCAJFUBUCACQJBACKJCLMNAORB
    UAST $.

  $( Rewrite the predicate of isomorphic objects with separated parts.
     (Contributed by Zhi Wang, 27-Oct-2025.) $)
  cic1st2ndbr $p |- ( P e. ( ~=c ` C )
                 -> ( 1st ` P ) ( ~=c ` C ) ( 2nd ` P ) ) $=
    ( ccic cfv wcel c1st c2nd cop wbr cic1st2nd id eqeltrrd df-br sylibr ) BACD
    ZEZBFDZBGDZHZOEQROIPBSOABJPKLQROMN $.

  ${
    cicpropd.1 $e |- ( ph -> ( Homf ` C ) = ( Homf ` D ) ) $.
    cicpropd.2 $e |- ( ph -> ( comf ` C ) = ( comf ` D ) ) $.
    $( Lemma for ~ cicpropd .  (Contributed by Zhi Wang, 27-Oct-2025.) $)
    cicpropdlem $p |- ( ( ph /\ P e. ( ~=c ` C ) ) -> P e. ( ~=c ` D ) ) $=
      ( ccic cfv wcel wceq adantl wbr ciso co c0 adantr cbs eqid ccat syl chomf
      wa c1st cop cic1st2nd cic1st2ndbr wne ccomf isopropd oveqd neeq1d cicrcl2
      c2nd ciclcl mpancom cicrcl brcic homfeqbas eleqtrd elfvexd catpropd mpbid
      cvv 3bitr4d df-br sylib eqeltrd ) ADBGHZIZUBZDDUCHZDUMHZUDZCGHZVIDVMJABDU
      EKVJVKVLVNLZVMVNIVJVKVLVHLZVOVIVPABDUFZKVJVKVLBMHZNZOUGVKVLCMHZNZOUGVPVOV
      JVSWAOVJVRVTVKVLVJBCABUAHCUAHJVIEPZABUHHCUHHJVIFPZUIUJUKVJBQHZBVRVKVLVRRW
      DRVIBSIZAVIVPWEVQBVKVLULZTKZVIVKWDIZAVIVPWHVQWEVPWHWFBVKVLUNUOTKZVIVLWDIZ
      AVIVPWJVQWEVPWJWFBVKVLUPUOTKZUQVJCQHZCVTVKVLVTRWLRVJWECSIWGVJBCSVCWBWCWGV
      JVKQCVJVKWDWLWIAWDWLJVIABCEURPZUSZUTVAVBWNVJVLWDWLWKWMUSUQVDVBVKVLVNVEVFV
      G $.

    $d C f $.  $d D f $.  $d f ph $.
    $( Two structures with the same base, hom-sets and composition operation
       have the same isomorphic objects.  (Contributed by Zhi Wang,
       27-Oct-2025.) $)
    cicpropd $p |- ( ph -> ( ~=c ` C ) = ( ~=c ` D ) ) $=
      ( vf ccic cfv cv wcel cicpropdlem chomf eqcomd ccomf impbida eqrdv ) AFBG
      HZCGHZAFIZQJSRJABCSDEKACBSABLHCLHDMABNHCNHEMKOP $.
  $}

  ${
    oppccicb.o $e |- O = ( oppCat ` C ) $.
    $( Isomorphic objects are isomorphic in the opposite category.
       (Contributed by Zhi Wang, 27-Oct-2025.) $)
    oppccicb $p |- ( R ( ~=c ` C ) S <-> R ( ~=c ` O ) S ) $=
      ( ccic cfv wbr id oppccic coppc eqid chomf wceq 2oppchomf ccomf 2oppccomf
      a1i cicpropd breqd mpbird impbii ) BCAFGZHZBCDFGHZUDABCDEUDIJUEUDBCDKGZFG
      ZHUEDBCUFUFLUEIJUEUCUGBCUEAUFAMGUFMGNUEADEORAPGUFPGNUEADEQRSTUAUB $.

    $d C p $.  $d O p $.
    $( The opposite category has the same isomorphic objects as the original
       category.  (Contributed by Zhi Wang, 27-Oct-2025.) $)
    oppcciceq $p |- ( ~=c ` C ) = ( ~=c ` O ) $=
      ( vp ccic cfv cv wcel c1st c2nd cop cic1st2nd wbr cic1st2ndbr df-br sylib
      oppccic eqeltrd oppccicb sylibr impbii eqriv ) DAEFZBEFZDGZUCHZUEUDHZUFUE
      UEIFZUEJFZKZUDAUELUFUHUIUDMZUJUDHUFAUHUIBCAUENQUHUIUDOPRUGUEUJUCBUELUGUHU
      IUCMZUJUCHUGUKULBUENAUHUIBCSTUHUIUCOPRUAUB $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Subcategories
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( The double domain of a function on a Cartesian square.  (Contributed by
     Zhi Wang, 1-Nov-2025.) $)
  dmdm $p |- ( A Fn ( B X. B ) -> B = dom dom A ) $=
    ( cxp wfn cdm fndm dmeqd dmxpid eqtr2di ) ABBCZDZAEZEJEBKLJJAFGBHI $.

  ${
    $d A w x y z $.  $d H w y z $.  $d S w y z $.
    iinfssc.1 $e |- ( ph -> A =/= (/) ) $.
    iinfssc.2 $e |- ( ( ph /\ x e. A ) -> H C_cat J ) $.
    iinfssc.3 $e |- ( ph -> K = ( y e. |^|_ x e. A dom H
                         |-> |^|_ x e. A ( H ` y ) ) ) $.
    ${
      iinfssclem1.4 $e |- ( ( ph /\ x e. A ) -> S = dom dom H ) $.
      iinfssclem1.5 $e |- F/ x ph $.
      $( Lemma for ~ iinfssc .  (Contributed by Zhi Wang, 31-Oct-2025.) $)
      iinfssclem1 $p |- ( ph -> K = ( z e. |^|_ x e. A S
         , w e. |^|_ x e. A S |-> |^|_ x e. A ( z H w ) ) ) $=
        ( ciin cxp cv cfv wceq cmpt co cmpo cdm wcel wa sscfn1 fndmd iineq2d c0
        wne iinxp syl eqtrd mpteq1d fveq2 eqtr4di adantr iineq2dv mpompt eqtrdi
        cop df-ov ) AJCBFGPZVDQZBFCRZHSZPZUAZDEVDVDBFDRZERZHUBZPZUCAJCBFHUDZPZV
        HUAVIMACVOVEVHAVOBFGGQZPZVEABFVNVPOABRFUEZUFZVPHVSGHILNUGUHUIAFUJUKVQVE
        TKBFGGULUMUNUOUNDECVDVDVHVMVFVJVKVBZTZBFVGVLWAVGVLTVRWAVGVTHSVLVFVTHUPV
        JVKHVCUQURUSUTVA $.

      $d J w z $.  $d K w z $.  $d ph w z $.
      $( Lemma for ~ iinfssc .  (Contributed by Zhi Wang, 31-Oct-2025.) $)
      iinfssclem2 $p |- ( ph -> K Fn ( |^|_ x e. A S X. |^|_ x e. A S ) ) $=
        ( vz vw ciin wfn cvv wcel wral cxp cv co cmpo wa wne ovex rgenw sylancl
        c0 iinexg adantr ralrimivva eqid fnmpo syl iinfssclem1 fneq1d mpbird )
        AHBDEPZUTUAZQNOUTUTBDNUBZOUBZFUCZPZUDZVAQZAVERSZOUTTNUTTVGAVHNOUTUTAVHV
        BUTSVCUTSUEADUJUFVDRSZBDTVHIVIBDVBVCFUGUHBDVDRUKUIULUMNOUTUTVEVFRVFUNUO
        UPAVAHVFABCNODEFGHIJKLMUQURUS $.

      $d X w x z $.  $d Y w x z $.
      iinfssclem3.x $e |- ( ph -> X e. |^|_ x e. A S ) $.
      iinfssclem3.y $e |- ( ph -> Y e. |^|_ x e. A S ) $.
      $( Lemma for ~ iinfssc .  (Contributed by Zhi Wang, 31-Oct-2025.) $)
      iinfssclem3 $p |- ( ph -> ( X K Y ) = |^|_ x e. A ( X H Y ) ) $=
        ( vz vw cvv ciin cv co iinfssclem1 wceq wa nfan simplrl simplrr oveq12d
        nfv wcel iineq2d c0 wne wral ovex rgenw iinexg sylancl ovmpod ) ARSIJBD
        EUAZVBBDRUBZSUBZFUCZUABDIJFUCZUAZHTABCRSDEFGHKLMNOUDAVCIUEZVDJUEZUFZUFZ
        BDVEVFAVJBOVJBUKUGVKBUBDULZUFVCIVDJFAVHVIVLUHAVHVIVLUIUJUMPQADUNUOVFTUL
        ZBDUPVGTULKVMBDIJFUQURBDVFTUSUTVA $.
    $}

    $d J w x z $.  $d K w z $.  $d ph w x y z $.
    $( Indexed intersection of subcategories is a subcategory (the
       category-agnostic version).  (Contributed by Zhi Wang, 31-Oct-2025.) $)
    iinfssc $p |- ( ph -> K C_cat J ) $=
      ( vz vw cssc cdm wss cv wral wcel wa cvv wbr ciin co wrex c0 eqidd sscfn1
      wne sscfn2 ssc1 ralrimiva r19.2z syl2anc iinss syl iinfssclem1 ovex rgenw
      nfv iinexg sylancl adantr ovmpt4d nfii1 nfcri nfan cxp wfn adantlr iinss2
      adantl simplrl sseldd simplrr ralrimia jca eqsstrd ralrimivva iinfssclem2
      ssc2 3syl wex n0 sylib exlimddv sscrel brrelex2i dmexd isssc mpbir2and )
      AGFMUABDENNZUBZFNZNZOZKPZLPZGUCZWPWQFUCZOZLWLQKWLQAWKWNOZBDUDZWOADUEUHZXA
      BDQXBHAXABDABPDRZSZWKWNEFXEWKEFIXEWKUFZUGZXEWNEFIXEWNUFUIZIUJUKXABDULUMBD
      WKWNUNUOAWTKLWLWLAWPWLRZWQWLRZSZSZWRBDWPWQEUCZUBZWSAKLWLWLXNGTABCKLDWKEFG
      HIJXFABUSZUPAXNTRZXKAXCXMTRZBDQXPHXQBDWPWQEUQURBDXMTUTVAVBVCXLXCXMWSOZBDQ
      ZSXRBDUDXNWSOXLXCXSAXCXKHVBXLXRBDAXKBXOXIXJBBKWLBDWKVDZVEBLWLXTVEVFVFXLXD
      SZWKEFWPWQAXDEWKWKVGVHXKXGVIAXDEFMUAZXKIVIYAWLWKWPXDWLWKOXLBDWKVJVKZAXIXJ
      XDVLVMYAWLWKWQYCAXIXJXDVNVMVTVOVPXRBDULBDXMWSUNWAVQVRAKLWLWNGFTABCDWKEFGH
      IJXFXOVSAXDFWNWNVGVHBAXCXDBWBHBDWCWDZXHWEAWMTAFTAXDFTRZBYDXEYBYEIEFMWFWGU
      OWEWHWHWIWJ $.
  $}

  ${
    $d A a b c f g x y $.  $d C a b c f g x $.  $d H a b c f g y $.
    $d K a b c f g $.  $d a b c f g ph x y $.
    iinfsubc.1 $e |- ( ph -> A =/= (/) ) $.
    iinfsubc.2 $e |- ( ( ph /\ x e. A ) -> H e. ( Subcat ` C ) ) $.
    iinfsubc.3 $e |- ( ph -> K = ( y e. |^|_ x e. A dom H
                         |-> |^|_ x e. A ( H ` y ) ) ) $.
    $( Indexed intersection of subcategories is a subcategory.  (Contributed by
       Zhi Wang, 31-Oct-2025.) $)
    iinfsubc $p |- ( ph -> K e. ( Subcat ` C ) ) $=
      ( va vg cfv wcel cv co wral ciin wa adantr vf vb vc csubc chomf cssc ccid
      wbr cop cco cdm eqid subcssc iinfssc eqidd subcfn simpr subcidcl ralimdva
      cxp wfn ex cvv eliin elv fvex ax-mp 3imtr4g imp wne adantlr cmpt wceq nfv
      wb c0 nfii1 nfcri iinfssclem3 eleqtrrd simprl ad2antrr eleqtrd simprr jca
      nfan ad5ant15 iinss2 adantl sseldd simplrl simplrr subccocl ralrimia ovex
      wss sylibr syldan ralrimivva ralrimiva ccat wex n0 sylib subcrcl exlimddv
      syl iinfssclem2 issubc2 mpbir2and ) AGEUDMZNGEUEMZUFUHKOZEUGMZMZXMXMGPZNZ
      LOZUAOZXMUBOZUIUCOZEUJMZPZPZXMYAGPZNZLXTYAGPZQUAXMXTGPZQZUCBDFUKZUKZRZQUB
      YLQZSZKYLQABCDFXLGHABODNZSZEXLFIXLULZUMZJUNAYNKYLAXMYLNZSZXQYMYTXOBDXMXMF
      PZRZXPAYSXOUUBNZAXMYKNZBDQZXOUUANZBDQZYSUUCAUUDUUFBDYPUUDUUFYPUUDSEYKXNFX
      MYPFXKNZUUDITYPFYKYKUTVAZUUDYPEYKFIYPYKUOZUPZTYPUUDUQXNULZURVBUSYSUUEVOKB
      XMDYKVCVDVEXOVCNUUCUUGVOXMXNVFBXODUUAVCVDVGVHVIYTBCDYKFXLGXMXMADVPVJZYSHT
      AYOFXLUFUHZYSYRVKZAGCBDYJRBDCOFMRVLVMZYSJTYTYOSYKUOAYSBABVNZBKYLBDYKVQZVR
      WFZAYSUQZUUTVSVTYTYIUBUCYLYLYTXTYLNZYAYLNZSZSZYFUALYHYGUVDXSYHNZXRYGNZSZS
      ZYDBDXMYAFPZRZYEUVDUVGXSBDXMXTFPZRZNZXRBDXTYAFPZRZNZSZYDUVJNZUVHUVMUVPUVH
      XSYHUVLUVDUVEUVFWAUVDYHUVLVMUVGUVDBCDYKFXLGXMXTAUUMYSUVCHWBZYTYOUUNUVCUUO
      VKZAUUPYSUVCJWBZUVDYOSYKUOZYTUVCBUUSUVAUVBBBUBYLUURVRBUCYLUURVRWFWFZYTYSU
      VCUUTTZYTUVAUVBWAZVSTWCUVHXRYGUVOUVDUVEUVFWDUVDYGUVOVMUVGUVDBCDYKFXLGXTYA
      UVSUVTUWAUWBUWCUWEYTUVAUVBWDZVSTWCWEUVDUVQSZYDUVINZBDQZUVRUWGUWHBDUVDUVQB
      UWCUVMUVPBBUAUVLBDUVKVQVRBLUVOBDUVNVQVRWFWFUWGYOSZEYKYBXSXRFXMXTYAAYOUUHY
      SUVCUVQIWGAYOUUIYSUVCUVQUUKWGUWJYLYKXMYOYLYKWPUWGBDYKWHWIZUVDYSUVQYOUWDWB
      WJYBULZUWJYLYKXTUWKUVDUVAUVQYOUWEWBWJUWJYLYKYAUWKUVDUVBUVQYOUWFWBWJUWJUVL
      UVKXSYOUVLUVKWPUWGBDUVKWHWIUVDUVMUVPYOWKWJUWJUVOUVNXRYOUVOUVNWPUWGBDUVNWH
      WIUVDUVMUVPYOWLWJWMWNYDVCNUVRUWIVOXRXSYCWOBYDDUVIVCVDVGWQWRUVDYEUVJVMUVGU
      VDBCDYKFXLGXMYAUVSUVTUWAUWBUWCUWDUWFVSTVTWSWSWEWTAKUBUCEYLYBXNUALXLGYQUUL
      UWLAYOEXANZBAUUMYOBXBHBDXCXDYPUUHUWMIEFXEXGXFABCDYKFXLGHYRJUUJUUQXHXIXJ
      $.
  $}

  ${
    $d A w x y z $.  $d B w x y z $.  $d C w x y z $.  $d V x $.  $d W x $.
    $( Indexed intersection of functions with an unordered pair index.
       (Contributed by Zhi Wang, 31-Oct-2025.) $)
    iinfprg $p |- ( ( A e. V /\ B e. W ) ->
      ( x e. ( dom A i^i dom B ) |-> ( ( A ` x ) i^i ( B ` x ) ) ) =
      ( x e. |^|_ y e. { A , B } dom y |-> |^|_ y e. { A , B } ( y ` x ) ) ) $=
      ( wcel wa cpr cdm ciin cfv cmpt cin dmeq iinxprg fveq1 mpteq12dv eqcomd
      cv ) CEGDFGHZABCDIZBTZJZKZBUBATZUCLZKZMACJZDJZNZUFCLZUFDLZNZMUAAUEUHUKUNB
      CDUDUIUJEFUCCOUCDOPBCDUGULUMEFUFUCCQUFUCDQPRS $.

    $( The intersection of two subcategories is a subcategory.  (Contributed by
       Zhi Wang, 31-Oct-2025.) $)
    infsubc $p |- ( ( A e. ( Subcat ` C ) /\ B e. ( Subcat ` C ) )
                 -> ( x e. ( dom A i^i dom B )
                      |-> ( ( A ` x ) i^i ( B ` x ) ) ) e. ( Subcat ` C ) ) $=
      ( vy csubc cfv wcel wa cpr cv cdm cin cmpt c0 prnzg wceq eleq1 syl5ibrcom
      wne adantr simpll simplr wo elpri adantl mpjaod iinfprg iinfsubc ) BDFGZH
      ZCUJHZIZEABCJZDEKZABLCLMAKZBGUPCGMNUKUNOTULBCUJPUAUMUOUNHZIZUOBQZUOUJHZUO
      CQZURUTUSUKUKULUQUBUOBUJRSURUTVAULUKULUQUCUOCUJRSUQUSVAUDUMUOBCUEUFUGAEBC
      UJUJUHUI $.

    $( The intersection of two subcategories is a subcategory.  (Contributed by
       Zhi Wang, 31-Oct-2025.) $)
    infsubc2 $p |- ( ( A e. ( Subcat ` C ) /\ B e. ( Subcat ` C ) )
                  -> ( x e. ( dom dom A i^i dom dom B )
                     , y e. ( dom dom A i^i dom dom B )
                       |-> ( ( x A y ) i^i ( x B y ) ) ) e. ( Subcat ` C ) ) $=
      ( vz vw cfv wcel wa cdm cin cv co cmpo ciin wceq cssc wbr subcssc cmpt c0
      csubc cpr chomf prnzg adantr simpll eqid breq1 syl5ibrcom simplr wo elpri
      wne adantl mpjaod iinfprg eqidd iinfssclem1 dmeq dmeqd iinxprg mpoeq123dv
      nfv oveq eqtrd infsubc eqeltrrd ) CEUCHZIZDVJIZJZFCKZDKZLFMZCHVPDHLUAZABV
      NKZVOKZLZVTAMZBMZCNZWAWBDNZLZOZVJVMVQABGCDUDZGMZKZKZPZWKGWGWAWBWHNZPZOWFV
      MGFABWGWJWHEUEHZVQVKWGUBUOVLCDVJUFUGVMWHWGIZJZWHCQZWHWNRSZWHDQZWPWRWQCWNR
      SWPEWNCVKVLWOUHWNUIZTWHCWNRUJUKWPWRWSDWNRSWPEWNDVKVLWOULWTTWHDWNRUJUKWOWQ
      WSUMVMWHCDUNUPUQFGCDVJVJURWPWJUSVMGVEUTVMABWKWKWMVTVTWEGCDWJVRVSVJVJWQWIV
      NWHCVAVBWSWIVOWHDVAVBVCZXAGCDWLWCWDVJVJWAWBWHCVFWAWBWHDVFVCVDVGFCDEVHVI
      $.
  $}

  ${
    $d C x y $.  $d H x y $.  $d J x y $.  $d S x y $.  $d T x y $.
    infsubc2d.1 $e |- ( ph -> H Fn ( S X. S ) ) $.
    infsubc2d.2 $e |- ( ph -> J Fn ( T X. T ) ) $.
    infsubc2d.3 $e |- ( ph -> H e. ( Subcat ` C ) ) $.
    infsubc2d.4 $e |- ( ph -> J e. ( Subcat ` C ) ) $.
    $( The intersection of two subcategories is a subcategory.  (Contributed by
       Zhi Wang, 31-Oct-2025.) $)
    infsubc2d $p |- ( ph -> ( x e. ( S i^i T ) , y e. ( S i^i T )
                       |-> ( ( x H y ) i^i ( x J y ) ) ) e. ( Subcat ` C ) ) $=
      ( cdm cin cv co cmpo wceq cxp wcel csubc cfv fndmd dmxpid ineq12d mpoeq12
      dmeqd eqtrdi syl2anc infsubc2 eqeltrrd ) ABCGMZMZHMZMZNZUPBOZCOZGPUQURHPN
      ZQZBCEFNZVAUSQZDUAUBZAUPVARZVDUTVBRAUMEUOFAUMEESZMEAULVEAVEGIUCUGEUDUHAUO
      FFSZMFAUNVFAVFHJUCUGFUDUHUEZVGBCUPUPVAVAUSUFUIAGVCTHVCTUTVCTKLBCGHDUJUIUK
      $.
  $}

  ${
    $d S a b c f g x y $.
    discsubc.j $e |- J = ( x e. S , y e. S |->
                           if ( x = y , { ( I ` x ) } , (/) ) ) $.
    $( Lemma for ~ discsubc .  (Contributed by Zhi Wang, 1-Nov-2025.) $)
    discsubclem $p |- J Fn ( S X. S ) $=
      ( weq cv cfv csn c0 cif snex 0ex ifex fnmpoi ) ABCCABGZAHDIZJZKLEFQSKRMNO
      P $.

    $d B a b c f g $.  $d C a b c f g $.  $d I a b c f g x y $.
    $d J a b c f g $.  $d a b c f g ph $.
    discsubc.b $e |- B = ( Base ` C ) $.
    discsubc.i $e |- I = ( Id ` C ) $.
    discsubc.s $e |- ( ph -> S C_ B ) $.
    discsubc.c $e |- ( ph -> C e. Cat ) $.
    $( A discrete category, whose only morphisms are the identity morphisms, is
       a subcategory.  (Contributed by Zhi Wang, 1-Nov-2025.) $)
    discsubc $p |- ( ph -> J e. ( Subcat ` C ) ) $=
      ( va vb wcel co wa weq c0 vg vf csubc cfv chomf cssc wbr cop cco wral wss
      vc csn cif wceq eqeq12 simpl fveq2d sneqd ifbieq1d snex 0ex ovmpoa adantl
      cv ifex sseq1 chom eqid ccat ad2antrr simplrl sseldd catidcl simpr oveq2d
      homfval eqtr3d eleqtrd wn 0ss a1i ifbothda eqsstrd ralrimivva cvv cxp wfn
      snssd discsubclem homffn cbs fvexi isssc mpbir2and fvex snid equtr2 eqtrd
      iftrued syl2anc eleqtrrid wne simprl iffalse necon1ai syl opeq2d ad2antlr
      ne0d simprr oveq12d eqcomd elsnd eqtr4d oveq123d ad3antrrr catlid 3eltr4d
      jca ralrimiva issubc2 ) AHEUCUDPHEUEUDZUFUGZNVEZGUDZYEYEHQZPZUAVEZUBVEZYE
      OVEZUHZULVEZEUIUDZQZQZYEYMHQZPZUAYKYMHQZUJUBYEYKHQZUJZULFUJOFUJZRZNFUJAYD
      FDUKZYTYEYKYCQZUKZOFUJNFUJLAUUFNOFFAYEFPZYKFPZRZRZYTNOSZYFUMZTUNZUUEUUIYT
      UUMUOZABCYEYKFFBCSZBVEZGUDZUMZTUNZUUMHBNSZCOSZRZUUOUUKUURUULTUUPYECVEZYKU
      PUVBUUQYFUVBUUPYEGUUTUVAUQURUSUTIUUKUULTYFVAZVBVFVCZVDUUKUULUUEUKTUUEUKZU
      UMUUEUKUUJUULTUULUUMUUEVGTUUMUUEVGUUJUUKRZYFUUEUVGYFYEYEEVHUDZQZUUEUVGDEG
      UVHYEJUVHVIZKAEVJPZUUIUUKMVKUVGFDYEAUUDUUIUUKLVKAUUGUUHUUKVLVMZVNUVGYEYEY
      CQUVIUUEUVGDEYCUVHYEYEYCVIZJUVJUVLUVLVQUVGYEYKYEYCUUJUUKVOVPVRVSWIUVFUUJU
      UKVTRUUEWAWBWCWDWEANOFDHYCWFHFFWGWHABCFGHIWJWBZYCDDWGWHADEYCUVMJWKWBDWFPA
      DEWLJWMWBWNWOAUUCNFAUUGRZYHUUBUVOYFUULYGYFYEGWPWQZUVOUUGUUGYGUULUOZAUUGVO
      ZUVRBCYEYEFFUUSUULHUUTCNSZRZUUSUURUULUVTUUOUURTBCNWRWTUVTUUQYFUVTUUPYEGUU
      TUVSUQURUSWSIUVDVCZXAXBUVOUUAOULFFUVOUUHYMFPZRZRZYRUBUAYTYSUWDYJYTPZYIYSP
      ZRZRZYFUULYPYQYFUULPUWHUVPWBUWHYPYFYFYEYEUHZYEYNQZQYFUWHYIYFYJYFYOUWJUWHU
      WJYOUWHUWIYLYEYMYNUWHYEYKYEUWHUUMTXCUUKUWHUUMYJUWHYJYTUUMUWDUWEUWFXDUWHUU
      GUUHUUNUVOUUGUWCUWGUVRVKZUVOUUHUWBUWGVLUVEXAVSZXJUUKUUMTUUKUULTXEXFXGZXHU
      WHYEYKYMUWMUWHOULSZYKGUDZUMZTUNZTXCUWNUWHUWQYIUWHYIYSUWQUWDUWEUWFXKUWCYSU
      WQUOUVOUWGBCYKYMFFUUSUWQHBOSZCULSZRZUUOUWNUURUWPTUUPYKUVCYMUPUWTUUQUWOUWT
      UUPYKGUWRUWSUQURUSUTIUWNUWPTUWOVAVBVFVCXIVSZXJUWNUWQTUWNUWPTXEXFXGZWSZXLX
      MUWHYIUWOYFUWHYIUWOUWHYIUWQUWPUXAUWHUWNUWPTUXBWTVSXNUWHYEYKGUWMURXOUWHYJY
      FUWHYJUUMUULUWLUWHUUKUULTUWMWTVSXNXPUWHDEYNGYFUVHYEYEJUVJKAUVKUUGUWCUWGMX
      QZUWHFDYEAUUDUUGUWCUWGLXQUWKVMZYNVIZUXEUWHDEGUVHYEJUVJKUXDUXEVNXRWSUWHYGY
      QUULUWHYEYMYEHUXCVPUWHUUGUUGUVQUWKUWKUWAXAVRXSWEWEXTYAANOULEFYNGUBUAYCHUV
      MKUXFMUVNYBWO $.

    $d J h j $.  $d S h j $.
    iinfconstbas.a $e |- ( ph -> A = ( ( Subcat ` C )
                                   i^i { j | j Fn ( S X. S ) } ) ) $.
    $( Lemma for ~ iinfconstbas .  (Contributed by Zhi Wang, 1-Nov-2025.) $)
    iinfconstbaslem $p |- ( ph -> J e. A ) $=
      ( csubc cfv cv wfn cxp cab cin discsubc discsubclem a1i fneq1 elabd elind
      eleqtrrd ) AJFQRZHSZGGUAZTZHUBZUCDAUKUOJABCEFGIJKLMNOUDZAUNJUMTZHJUKUPUQA
      BCGIJKUEUFUMULJUGUHUIPUJ $.

    $d A h x y z $.  $d I h x y $.  $d S h x y z $.  $d h ph x y $.
    $( The discrete category is the indexed intersection of all subcategories
       with the same base.  (Contributed by Zhi Wang, 1-Nov-2025.) $)
    iinfconstbas $p |- ( ph ->
                  J = ( z e. |^|_ h e. A dom h |-> |^|_ h e. A ( h ` z ) ) ) $=
      ( wceq wcel ciin cv co cmpo cdm cfv cmpt csn cif wne iinfconstbaslem ne0d
      c0 iinconst syl eqcomd adantr wa simpr oveqd cvv snex ifex ovmpt4g mp3an3
      0ex ad2antlr eqtrd wss sseq1 csubc cxp wfn cab cin eleqtrd elin1d adantlr
      elin2d vex fneq1 elab sylib simplrl subcidcl oveq2d snssd wn 0ss ifbothda
      a1i iinglb mpoeq123dva eqtrid chomf eqid subcssc eqidd iinfssclem1 eqtr4d
      dmdm nfv ) ALBCIEHUAZXCIEBUBZCUBZIUBZUCZUAZUDZDIEXFUEZUAIEDUBXFUFUAUGZALB
      CHHXDXESZXDKUFZUHZUMUIZUDXIMABCHHXOXCXCXHAXCHAEUMUJXCHSAELABCEFGHJKLMNOPQ
      RUKZULZIEHUNUOUPZAHXCSXDHTZXRUQAXSXEHTZURZURZXHXOYBIEXGXOLALETYAXPUQYBXFL
      SZURZXGXDXELUCZXOYDXFLXDXEYBYCUSUTYAYEXOSZAYCXSXTXOVATYFXLXNUMXMVBVFVCBCH
      HXOLVAMVDVEVGVHXLXNXGVIUMXGVIZXOXGVIYBXFETZURZXNUMXNXOXGVJUMXOXGVJYIXLURZ
      XMXGYJXMXDXDXFUCZXGYIXMYKTXLYIGHKXFXDAYHXFGVKUFZTYAAYHURZYLJUBZHHVLZVMZJV
      NZXFYMXFEYLYQVOZAYHUSAEYRSYHRUQVPZVQZVRAYHXFYOVMZYAYMXFYQTUUAYMYLYQXFYSVS
      YPUUAJXFIVTYOYNXFWAWBWCZVRAXSXTYHWDOWEUQYJXDXEXDXFYIXLUSWFVPWGYGYIXLWHURX
      GWIWKWJWLUPWMWNAIDBCEHXFGWOUFZXKXQYMGUUCXFYTUUCWPWQAXKWRYMUUAHXJUESUUBXFH
      XAUOAIXBWSWT $.
  $}

  ${
    nelsubc.b $e |- B = ( Base ` C ) $.
    nelsubc.s $e |- ( ph -> S C_ B ) $.
    nelsubc.0 $e |- ( ph -> S =/= (/) ) $.
    nelsubc.j $e |- ( ph -> J = ( ( S X. S ) X. { (/) } ) ) $.
    ${
      $d H p q $.  $d J f $.  $d J p q $.  $d S p q $.  $d S x y z $.
      $d f x y $.  $d p ph q $.  $d ph x y z $.
      nelsubc.h $e |- H = ( Homf ` C ) $.
      $( Lemma for ~ nelsubc .  (Contributed by Zhi Wang, 5-Nov-2025.) $)
      nelsubclem $p |- ( ph -> ( J Fn ( S X. S ) /\ ( J C_cat H
          /\ ( -. A. x e. S I e. ( x J x )
          /\ A. x e. S A. y e. S A. z e. S A. f e. ( x J y ) ps ) ) ) ) $=
        ( co wcel c0 vp vq cxp wfn cssc wbr cv wn wa csn cvv 0ex fnconstg ax-mp
        wral fneq1d mpbiri wss ovconst2 sylan9eq 0ss eqsstrdi ralrimivva homffn
        oveqd a1i cbs fvexi isssc mpbir2and wrex wne anidms nel02 syl reximdva0
        wceq mpdan rexnal sylib rzal ralrimivw jca jca32 ) ALHHUCZUDZLJUEUFZKCU
        GZWHLRZSZCHUOUHZBIWHDUGZLRZUOZEHUOZDHUOCHUOZUIAWFWETUJUCZWEUDZTUKSWRULW
        ETUKUMUNAWELWQPUPUQZAWGHFURUAUGZUBUGZLRZWTXAJRZURZUBHUOUAHUONAXDUAUBHHA
        WTHSXAHSUIZUIXBTXCAXEXBWTXAWQRTALWQWTXAPVEHHTWTXAULUSUTXCVAVBVCAUAUBHFL
        JUKWSJFFUCUDAFGJQMVDVFFUKSAFGVGMVHVFVIVJAWKWPAWJUHZCHVKZWKAHTVLXGOAXFCH
        AWHHSZUIWITVQXFAXHWIWHWHWQRZTALWQWHWHPVEXHXITVQHHTWHWHULUSVMUTWIKVNVOVP
        VRWJCHVSVTAWOCDHHAXHWLHSUIZUIZWNEHXKWMTVQWNAXJWMWHWLWQRTALWQWHWLPVEHHTW
        HWLULUSUTBIWMWAVOWBVCWCWD $.

      nelsubc.i $e |- .1. = ( Id ` C ) $.
      nelsubc.o $e |- .x. = ( comp ` C ) $.
      $( An empty "hom-set" for non-empty base satisfies all conditions for a
         subcategory but the existence of identity morphisms.  (Contributed by
         Zhi Wang, 5-Nov-2025.) $)
      nelsubc $p |- ( ph -> ( J Fn ( S X. S ) /\ ( J C_cat H
          /\ ( -. A. x e. S ( .1. ` x ) e. ( x J x )
          /\ A. x e. S A. y e. S A. z e. S A. f e. ( x J y ) A. g e. ( y J z )
          ( g ( <. x , y >. .x. z ) f ) e. ( x J z ) ) ) ) ) $=
        ( cv cop co wcel wral cfv nelsubclem ) AKUAJUABUAZCUAZUBDUAZHUCUCUHUJMU
        CUDKUIUJMUCUEBCDEFGJLUHIUFMNOPQRUG $.
    $}

    $d B f g x y z $.  $d C f g x y z $.  $d J f g x y z $.  $d S f g x y z $.
    $d f g ph x y z $.
    nelsubc2.c $e |- ( ph -> C e. Cat ) $.
    $( An empty "hom-set" for non-empty base is not a subcategory.
       (Contributed by Zhi Wang, 5-Nov-2025.) $)
    nelsubc2 $p |- ( ph -> -. J e. ( Subcat ` C ) ) $=
      ( vx vg vf vy vz cfv cv co wral wa csubc wcel ccid cop cco cxp chomf cssc
      wfn wbr eqid nelsubc simprrd simpld issubc2 simplbda r19.26 sylib mtand
      wn ) AECUAPUBZKQZCUCPZPVBVBERUBZKDSZAVEUTZLQMQVBNQZUDOQZCUEPZRRVBVHERUBLV
      GVHERSMVBVGERSODSNDSZKDSZAEDDUFUIZECUGPZUHUJZVFVKTZAKNOBCDVIVCMLVMEFGHIVM
      UKZVCUKZVIUKZULZUMUNAVATZVEVKVTVDVJTKDSZVEVKTAVAVNWAAKNOCDVIVCMLVMEVPVQVR
      JAVLVNVOTVSUNUOUPVDVJKDUQURUNUS $.
  $}

  ${
    $d C c f j s $.  $d C c g j s $.  $d C c j s x $.  $d C c j s y $.
    $d C c j s z $.  $d J f j s $.  $d J g j s $.  $d J j s x $.  $d J j s y $.
    $d J j s z $.  $d S s x $.  $d S s y $.  $d S s z $.
    nelsubc3lem.c $e |- C e. Cat $.
    nelsubc3lem.j $e |- J e. _V $.
    nelsubc3lem.s $e |- S e. _V $.
    nelsubc3lem.1 $e |- ( J Fn ( S X. S ) /\ ( J C_cat ( Homf ` C )
           /\ ( -. A. x e. S ( ( Id ` C ) ` x ) e. ( x J x )
           /\ A. x e. S A. y e. S A. z e. S A. f e. ( x J y ) A. g e. ( y J z )
           ( g ( <. x , y >. ( comp ` C ) z ) f ) e. ( x J z ) ) ) ) $.
    $( Lemma for ~ nelsubc3 .  (Contributed by Zhi Wang, 5-Nov-2025.) $)
    nelsubc3lem $p |- E. c e. Cat E. j E. s ( j Fn ( s X. s ) /\ (
      j C_cat ( Homf ` c ) /\ ( -. A. x e. s ( ( Id ` c ) ` x ) e. ( x j x )
      /\ A. x e. s A. y e. s A. z e. s A. f e. ( x j y ) A. g e. ( y j z )
      ( g ( <. x , y >. ( comp ` c ) z ) f ) e. ( x j z ) ) ) ) $=
      ( cv cfv co wral wa ccat wcel cxp wfn chomf cssc wbr ccid wn cop cco wrex
      wceq id sqxpeqd fneq2d raleq notbid raleqbi1dv anbi12d anbi2d spcev fneq1
      wex breq1 oveq eleq2d ralbidv raleqbidv 3ralbidv exbidv mp2b fveq2 breq2d
      fveq1d eleq1d oveqd 4ralbidv 2exbidv rspcev mp2an ) DUAUBHPZJPZWCUCZUDZWB
      DUEQZUFUGZAPZDUHQZQZWHWHWBRZUBZAWCSZUIZGPZFPZWHBPZUJZCPZDUKQZRZRZWHWSWBRZ
      UBZGWQWSWBRZSZFWHWQWBRZSZCWCSBWCSAWCSZTZTZTZJVDZHVDZWEWBKPZUEQZUFUGZWHXOU
      HQZQZWKUBZAWCSZUIZWOWPWRWSXOUKQZRZRZXCUBZGXESZFXGSCWCSBWCSAWCSZTZTZTZJVDH
      VDZKUAULLIEEUCZUDZIWFUFUGZWJWHWHIRZUBZAESZUIZXBWHWSIRZUBZGWQWSIRZSZFWHWQI
      RZSZCESZBESZAESZTZTZTZIWDUDZYOYQAWCSZUIZUUECWCSZBWCSZAWCSZTZTZTZJVDZXNOUU
      TUUKJENWCEUMZUULYNUUSUUJUVBWDYMIUVBWCEUVBUNUOUPUVBUURUUIYOUVBUUNYSUUQUUHU
      VBUUMYRYQAWCEUQURUUPUUGAWCEUUOUUFBWCEUUECWCEUQUSUSUTVAUTVBXMUVAHIMWBIUMZX
      LUUTJUVCWEUULXKUUSWDWBIVCUVCWGYOXJUURWBIWFUFVEUVCWNUUNXIUUQUVCWMUUMUVCWLY
      QAWCUVCWKYPWJWHWHWBIVFVGVHURUVCXHUUEABCWCWCWCUVCXFUUCFXGUUDWHWQWBIVFUVCXD
      UUAGXEUUBWQWSWBIVFUVCXCYTXBWHWSWBIVFVGVIVIVJUTUTUTVKVBVLYLXNKDUAXODUMZYKX
      LHJUVDYJXKWEUVDXQWGYIXJUVDXPWFWBUFXODUEVMVNUVDYBWNYHXIUVDYAWMUVDXTWLAWCUV
      DXSWJWKUVDWHXRWIXODUHVMVOVPVHURUVDYGXFABCFWCWCWCXGUVDYFXDGXEUVDYEXBXCUVDY
      DXAWOWPUVDYCWTWRWSXODUKVMVQVQVPVHVRUTUTVAVSVTWA $.
  $}

  ${
    $d c f j s x y $.  $d c g j s $.  $d c j s x y z $.
    $( Remark 4.2(2) of [Adamek] p. 48.  There exists a set satisfying all
       conditions for a subcategory but the existence of identity morphisms.
       Therefore such condition in ~ df-subc is necessary.

       Note that this theorem cheated a little bit because ` ( C |``cat J ) `
       is not a category.  In fact ` ( C |``cat J ) e. Cat ` is a stronger
       statement than the condition (d) of Definition 4.1(1) of [Adamek] p. 48,
       as stated here (see the proof of ~ issubc3 ).  To construct such a
       category, see ~ setc1onsubc and ~ cnelsubc .  (Contributed by Zhi Wang,
       5-Nov-2025.) $)
    nelsubc3 $p |- E. c e. Cat E. j E. s ( j Fn ( s X. s ) /\ (
      j C_cat ( Homf ` c ) /\ ( -. A. x e. s ( ( Id ` c ) ` x ) e. ( x j x )
      /\ A. x e. s A. y e. s A. z e. s A. f e. ( x j y ) A. g e. ( y j z )
      ( g ( <. x , y >. ( comp ` c ) z ) f ) e. ( x j z ) ) ) ) $=
      ( c2o cfv c1o c0 cvv wcel 1oex cv co wral wa wtru csetc cxp csn ccat 2oex
      eqid setccat ax-mp xpex p0ex wfn chomf cssc wbr ccid cop cco cbs wceq a1i
      wn setcbas mptru wss wne 2on0 word wb 2on onordi ordge1n0 mpbir 1n0 eqidd
      nelsubclem nelsubc3lem ) ABCIUAJZKDEFKKUBZLUCZUBZGHIMNZVQUDNUEVQIMVQUFZUG
      UHVRVSKKOOUIUJUIOVTVRUKVTVQULJZUMUNAPZVQUOJJZWDWDVTQNAKRVAEPDPWDBPZUPCPZV
      QUQJQQWDWGVTQNEWFWGVTQRZDWDWFVTQRCKRBKRAKRSSSTWHABCIVQKDWCWEVTIVQURJUSTVQ
      IMWBWATUEUTVBVCKIVDZTWIILVEZVFIVGWIWJVHIVIVJIVKUHVLUTKLVETVMUTTVTVNWCUFVO
      VCVP $.
  $}

  ${
    $d .1. a b m x $.  $d .1. f g k w x z $.  $d .x. a b m x y $.
    $d .x. f g k w x y z $.  $d D g k w y z $.  $d J a b m x y $.
    $d J f g k w x y z $.  $d S a b m x y $.  $d S f g k w x y z $.
    $d a b m ph x y $.  $d b m ph x y z $.  $d f g m ph x y z $.
    $d k ph w x y z $.
    ssccatid.h $e |- H = ( Homf ` C ) $.
    ssccatid.d $e |- D = ( C |`cat J ) $.
    ssccatid.x $e |- .x. = ( comp ` C ) $.
    ssccatid.j $e |- ( ph -> J C_cat H ) $.
    ssccatid.f $e |- ( ph -> J Fn ( S X. S ) ) $.
    ssccatid.c $e |- ( ph -> C e. Cat ) $.
    ssccatid.i $e |- ( ( ph /\ y e. S ) -> .1. e. ( y J y ) ) $.
    ssccatid.l $e |- ( ( ph /\ ( a e. S /\ b e. S /\ m e. ( a J b ) ) )
                        -> ( .1. ( <. a , b >. .x. b ) m ) = m ) $.
    ssccatid.r $e |- ( ( ph /\ ( a e. S /\ b e. S /\ m e. ( a J b ) ) )
                        -> ( m ( <. a , a >. .x. b ) .1. ) = m ) $.
    ssccatid.1 $e |- ( ( ph /\ ( x e. S /\ y e. S /\ z e. S )
                         /\ ( f e. ( x J y ) /\ g e. ( y J z ) ) )
                      -> ( g ( <. x , y >. .x. z ) f ) e. ( x J z ) ) $.
    $( A category ` C ` restricted by ` J ` is a category if all of the
       following are satisfied: a) the base is a subset of base of ` C ` , b)
       all hom-sets are subsets of hom-sets of ` C ` , c) it has identity
       morphisms for all objects, d) the composition under ` C ` is closed in
       ` J ` .  But ` J ` might not be a subcategory of ` C ` (see
       ~ cnelsubc ).  (Contributed by Zhi Wang, 6-Nov-2025.) $)
    ssccatid $p |- ( ph -> ( D e. Cat /\ ( Id ` D ) = ( y e. S |-> .1. ) ) ) $=
      ( vw vk cv wcel w3a cvv cbs cfv ccat eqid cxp wfn homffn a1i ssc1 rescbas
      wa co reschom rescco cresc ovexi biid cop wceq weq oveq2 id eqeq12d oveq1
      wral opeq1 oveq1d oveqd eqeq1d raleqbidv opeq2 oveq12d ralrimivvva adantr
      simpr1l simpr1r rspc2dv simpr31 rspcdva opeq12d simpr2l simpr32 syl132anc
      simpl chom wss sseldd cssc homfval eleqtrd simpr2r simpr33 catass iscatd2
      wbr ssc2 ) ABUIZGUJZCUIZGUJZVCZDUIZGUJZUGUIZGUJZVCZJUIZXIXKNVDZUJZKUIZXKX
      NNVDZUJZUHUIZXNXPNVDZUJZUKZUKZBCDUGGFHIJKUHNULAEUMUNZEFGNUORYJUPZUBUAAGYJ
      NMUAMYJYJUQURAYJEMQYKUSUTTVAZVBAYJEFGNUORYKUBUAYLVEAYJEFGHNUORYKUBUAYLSVF
      FULUJAFENVGRVHUTYIVIUCAYIVCZILUIZXIXKVJZXKHVDZVDZYNVKZIXSYPVDZXSVKLXTXSLJ
      VLZYQYSYNXSYNXSIYPVMYTVNVOYMIYNOUIZPUIZVJZUUBHVDZVDZYNVKZLUUAUUBNVDZVQZYR
      LXTVQIYNXIUUBVJZUUBHVDZVDZYNVKZLXIUUBNVDZVQOPXIXKGGOBVLZUUFUULLUUGUUMUUAX
      IUUBNVPUUNUUEUUKYNUUNUUDUUJIYNUUNUUCUUIUUBHUUAXIUUBVRVSVTWAWBPCVLZUULYRLU
      UMXTUUBXKXINVMUUOUUKYQYNUUOUUJYPIYNUUOUUIYOUUBXKHUUBXKXIWCUUOVNWDVTWAWBAU
      UHPGVQOGVQYIAUUFOPLGGUUGUDWEWFXJXLXRYHAWGZXJXLXRYHAWHZWIYAYDYGXMXRAWJZWKY
      MYNIXKXKVJZXNHVDZVDZYNVKZYBIUUTVDZYBVKLYCYBLKVLZUVAUVCYNYBYNYBIUUTVPUVDVN
      VOYMYNIUUAUUAVJZUUBHVDZVDZYNVKZLUUGVQZUVBLYCVQYNIUUSUUBHVDZVDZYNVKZLXKUUB
      NVDZVQOPXKXNGGOCVLZUVHUVLLUUGUVMUUAXKUUBNVPUVNUVGUVKYNUVNUVFUVJYNIUVNUVEU
      USUUBHUVNUUAXKUUAXKUVNVNZUVOWLVSVTWAWBPDVLZUVLUVBLUVMYCUUBXNXKNVMUVPUVKUV
      AYNUVPUVJUUTYNIUUBXNUUSHVMVTWAWBAUVIPGVQOGVQYIAUVHOPLGGUUGUEWEWFUUQXOXQXM
      YHAWMZWIYAYDYGXMXRAWNZWKYMAXJXLXOYAYDYBXSYOXNHVDVDXIXNNVDUJAYIWPUUPUUQUVQ
      UURUVRUFWOYMYJEHXSYBEWQUNZYEXPXIXKXNYKUVSUPZSAEUOUJYIUBWFYMGYJXIAGYJWRYIY
      LWFZUUPWSZYMGYJXKUWAUUQWSZYMGYJXNUWAUVQWSZYMXSXIXKMVDZXIXKUVSVDYMXTUWEXSY
      MGNMXIXKANGGUQURYIUAWFZANMWTXGYITWFZUUPUUQXHUURWSYMYJEMUVSXIXKQYKUVTUWBUW
      CXAXBYMYBXKXNMVDZXKXNUVSVDYMYCUWHYBYMGNMXKXNUWFUWGUUQUVQXHUVRWSYMYJEMUVSX
      KXNQYKUVTUWCUWDXAXBYMGYJXPUWAXOXQXMYHAXCZWSZYMYEXNXPMVDZXNXPUVSVDYMYFUWKY
      EYMGNMXNXPUWFUWGUVQUWIXHYAYDYGXMXRAXDWSYMYJEMUVSXNXPQYKUVTUWDUWJXAXBXEXF
      $.
  $}

  ${
    $d .xb f g x y $.  $d D f g x y z $.  $d E f g z $.  $d J g $.
    $d S f g x y z $.  $d f g ph x y z $.
    resccat.d $e |- D = ( C |`cat J ) $.
    resccat.b $e |- B = ( Base ` C ) $.
    resccat.s $e |- S = ( Base ` E ) $.
    resccat.j $e |- J = ( Homf ` E ) $.
    resccat.x $e |- .x. = ( comp ` C ) $.
    resccat.xb $e |- .xb = ( comp ` E ) $.
    resccat.1 $e |- ( ( ( ph /\ ( x e. S /\ y e. S /\ z e. S ) )
                         /\ ( f e. ( x J y ) /\ g e. ( y J z ) ) )
                      -> ( g ( <. x , y >. .x. z ) f )
                         = ( g ( <. x , y >. .xb z ) f ) ) $.
    resccat.e $e |- ( ph -> E e. V ) $.
    resccat.ss $e |- ( ph -> S C_ B ) $.
    ${
      resccatlem.c $e |- ( ph -> C e. U ) $.
      $( Lemma for ~ resccat .  (Contributed by Zhi Wang, 6-Nov-2025.) $)
      resccatlem $p |- ( ph -> ( D e. Cat <-> E e. Cat ) ) $=
        ( cvv chomf cfv cxp wfn homffn a1i reschomf eqtr3di ccomf wceq cop wral
        cv co wcel w3a ralrimivva ralrimivvva cco chom eqid rescbas cbs reschom
        comfeq oveqd rescco eqeq1d raleqbidv 3ralbidv bitr4d mpbird cresc ovexi
        wa catpropd ) AGNUGPAOGUHUINUHUIAEFGHOKQRUFOHHUJUKAHNOTSULUMZUEUNTUOZAG
        UPUINUPUIUQZMUTZLUTZBUTZCUTZURZDUTZJVAZVAZWGWHWKWLIVAVAZUQZMWJWLOVAZUSZ
        LWIWJOVAZUSZDHUSCHUSBHUSZAWTBCDHHHAWIHVBWJHVBWLHVBVCWBWPLMWSWQUCVDVEAWF
        WGWHWKWLGVFUIZVAZVAZWOUQZMWJWLGVGUIZVAZUSZLWIWJXFVAZUSZDHUSCHUSBHUSXAAB
        CDHGNIXBLMXFXBVHUBXFVHAEFGHOKQRUFWDUEVIHNVJUIUQASUMWEVLAWTXJBCDHHHAWRXH
        LWSXIAOXFWIWJAEFGHOKQRUFWDUEVKZVMAWPXEMWQXGAOXFWJWLXKVMAWNXDWOAWMXCWGWH
        AJXBWKWLAEFGHJOKQRUFWDUEUAVNVMVMVOVPVPVQVRVSGUGVBAGFOVTQWAUMUDWC $.
    $}

    $d C f g x y z $.  $d c h $.
    $( A class ` C ` restricted by the hom-sets of another set ` E ` , whose
       base is a subset of the base of ` C ` and whose composition is
       compatible with ` C ` , is a category iff ` E ` is a category.  Note
       that the compatibility condition "resccat.1" can be weakened by removing
       ` x e. S ` because ` f e. ( x J y ) ` implies these.  (Contributed by
       Zhi Wang, 6-Nov-2025.) $)
    resccat $p |- ( ph -> ( D e. Cat <-> E e. Cat ) ) $=
      ( vc vh cvv wcel ccat wb wa cv w3a co cop wceq adantllr adantr resccatlem
      wss simpr wn c0 cresc cdm cress cnx chom cfv csts df-resc reldmmpo ovprc1
      eqtrid 0cat eqeltrdi adantl cbs fvprc sseq0 syl2an eqtr3di 0catg syl2an2r
      2thd pm2.61dan ) AFUGUHZGUIUHZMUIUHZUJAWGUKBCDEFGHIJUGKLMNOPQRSTUAABULZHU
      HCULZHUHDULZHUHUMKULZWJWKNUNUHLULZWKWLNUNUHUKWNWMWJWKUOZWLJUNUNWNWMWOWLIU
      NUNUPWGUBUQAMOUHZWGUCURAHEUTZWGUDURAWGVAUSAWGVBZUKZWHWIWRWHAWRGVCUIWRGFNV
      DUNVCPFNVDUEUFUGUGUEULUFULZVEVEVFUNVGVHVIWTUOVJUNVDUFUEVKVLVMVNVOVPVQAWPW
      RVCMVRVIZUPWIUCWSHVCXAAWQEVCUPHVCUPWRUDWREFVRVIVCQFVRVSVNHEVTWARWBMOWCWDW
      EWF $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Functors
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d b f g m n t u x y z $.
    $( The domain of ` Func ` is a relation.  (Contributed by Zhi Wang,
       12-Nov-2025.) $)
    reldmfunc $p |- Rel dom Func $=
      ( vt vu vb vf vg vz vx vn vm vy ccat cv cbs cfv chom ccid wceq cop wral
      co wf cxp c1st c2nd cmap cixp wcel cco wa w3a wsbc copab df-func reldmmpo
      cfunc ) ABKKCLZBLZMNDLZUAELZFUPUPUBFLZUCNURNUTUDNURNUQONTUTALZONZNUETUFUG
      GLZVAPNNVCVCUSTNVCURNZUQPNNQHLZILZVCJLZRUTVAUHNTTVCUTUSTNVEVGUTUSTNVFVCVG
      USTNVDVGURNRUTURNUQUHNTTQHVGUTVBTSIVCVGVBTSFUPSJUPSUIGUPSUJCVAMNUKDEULUOG
      JFBADEIHCUMUN $.
  $}

  ${
    func1st2nd.1 $e |- ( ph -> F e. ( C Func D ) ) $.
    $( Rewrite the functor predicate with separated parts.  (Contributed by Zhi
       Wang, 19-Oct-2025.) $)
    func1st2nd $p |- ( ph -> ( 1st ` F ) ( C Func D ) ( 2nd ` F ) ) $=
      ( cfunc co wrel wcel c1st cfv c2nd wbr relfunc 1st2ndbr sylancr ) ABCFGZH
      DQIDJKDLKQMBCNEDQOP $.
  $}

  ${
    func1st.1 $e |- ( ph -> F ( C Func D ) G ) $.
    $( Extract the first member of a functor.  (Contributed by Zhi Wang,
       15-Nov-2025.) $)
    func1st $p |- ( ph -> ( 1st ` <. F , G >. ) = F ) $=
      ( cfunc co wbr cvv wcel cop c1st cfv wceq relfunc brrelex12i op1stg 3syl
      wa ) ADEBCGHZIDJKEJKTDELMNDOFDEUABCPQDEJJRS $.

    $( Extract the second member of a functor.  (Contributed by Zhi Wang,
       15-Nov-2025.) $)
    func2nd $p |- ( ph -> ( 2nd ` <. F , G >. ) = G ) $=
      ( cfunc co wbr cvv wcel cop c2nd cfv wceq relfunc brrelex12i op2ndg 3syl
      wa ) ADEBCGHZIDJKEJKTDELMNEOFDEUABCPQDEJJRS $.
  $}

  ${
    funcrcl2.f $e |- ( ph -> F ( D Func E ) G ) $.
    $( Reverse closure for a functor.  (Contributed by Zhi Wang,
       17-Sep-2025.) $)
    funcrcl2 $p |- ( ph -> D e. Cat ) $=
      ( ccat wcel cfunc co wbr cop wa df-br biimpi funcrcl 3syl simpld ) ABGHZC
      GHZADEBCIJZKZDELZUAHZSTMFUBUDDEUANOBCUCPQR $.

    $( Reverse closure for a functor.  (Contributed by Zhi Wang,
       17-Sep-2025.) $)
    funcrcl3 $p |- ( ph -> E e. Cat ) $=
      ( ccat wcel cfunc co wbr cop wa df-br biimpi funcrcl 3syl simprd ) ABGHZC
      GHZADEBCIJZKZDELZUAHZSTMFUBUDDEUANOBCUCPQR $.
  $}

  ${
    $d B x y z $.  $d F x y z $.  $d G x y z $.  $d H x y z $.  $d J x y z $.
    $( A utility theorem for proving equivalence of "is a functor".
       (Contributed by Zhi Wang, 1-Oct-2024.) $)
    funcf2lem $p |- ( G e. X_ z e. ( B X. B )
    ( ( ( F ` ( 1st ` z ) ) J ( F ` ( 2nd ` z ) ) ) ^m ( H ` z ) )
    <-> ( G e. _V /\ G Fn ( B X. B ) /\ A. x e. B A. y e. B
           ( x G y ) : ( x H y ) --> ( ( F ` x ) J ( F ` y ) ) ) ) $=
      ( cv cfv co cmap wcel wral w3a fveq2 df-ov eqtr4di vex fveq2d cxp cvv wfn
      c1st c2nd cixp elixp2 cop wceq op1std op2ndd oveq12d eleq12d elmap bitrdi
      wf ovex ralxp 3anbi3i bitri ) FCDDUAZCIZUDJZEJZVBUEJZEJZHKZVBGJZLKZUFMFUB
      MZFVAUCZVBFJZVIMZCVANZOVJVKAIZBIZGKZVOEJZVPEJZHKZVOVPFKZUPZBDNADNZOCVAVIF
      UGVNWCVJVKVMWBCABDDVBVOVPUHZUIZVMWAVTVQLKZMWBWEVLWAVIWFWEVLWDFJWAVBWDFPVO
      VPFQRWEVGVTVHVQLWEVDVRVFVSHWEVCVOEVOVPVBASZBSZUJTWEVEVPEVOVPVBWGWHUKTULWE
      VHWDGJVQVBWDGPVOVPGQRULUMVTVQWAVRVSHUQVOVPGUQUNUOURUSUT $.

    funcf2lem2.b $e |- B = ( E ` C ) $.
    $( A utility theorem for proving equivalence of "is a functor".
       (Contributed by Zhi Wang, 25-Sep-2025.) $)
    funcf2lem2 $p |- ( G e. X_ z e. ( B X. B )
    ( ( ( F ` ( 1st ` z ) ) J ( F ` ( 2nd ` z ) ) ) ^m ( H ` z ) )
    <-> ( G Fn ( B X. B ) /\ A. x e. B A. y e. B
           ( x G y ) : ( x H y ) --> ( ( F ` x ) J ( F ` y ) ) ) ) $=
      ( cxp cv c1st cfv c2nd co wcel wral cvv cmap cixp wfn wf wa w3a funcf2lem
      3simpc sylbi cmpo wceq biimpi fvexi mpoex eqeltrdi adantr simpl syl3anbrc
      fnov simpr impbii ) HCDDLZCMZNOGOVCPOGOJQVCIOUAQUBRZHVBUCZAMZBMZIQVFGOVGG
      OJQVFVGHQZUDBDSADSZUEZVDHTRZVEVIUFVJABCDGHIJUGZVKVEVIUHUIVJVKVEVIVDVEVKVI
      VEHABDDVHUJZTVEHVMUKABDDHUSULABDDVHDEFKUMZVNUNUOUPVEVIUQVEVIUTVLURVA $.
  $}

  ${
    0funcglem.1 $e |- ( ph -> ( ps <-> ( ch /\ th /\ ta ) ) ) $.
    0funcglem.2 $e |- ( ph -> ( ch <-> et ) ) $.
    0funcglem.3 $e |- ( ph -> ( th <-> ze ) ) $.
    0funcglem.4 $e |- ( ph -> ta ) $.
    $( Lemma for ~ 0funcg .  (Contributed by Zhi Wang, 17-Oct-2025.) $)
    0funcglem $p |- ( ph -> ( ps <-> ( et /\ ze ) ) ) $=
      ( wa w3a df-3an bitrdi mpbiran2d anbi12d bitrd ) ABCDLZFGLABSEKABCDEMSELH
      CDENOPACFDGIJQR $.
  $}

  ${
    $d C f g m n x y z $.  $d D f g m n x y z $.  $d F m n x y z $.
    $d G m n x y z $.  $d V f g m n x y z $.  $d f g m n ph x y z $.
    0funcg.c $e |- ( ph -> C e. V ) $.
    0funcg.b $e |- ( ph -> (/) = ( Base ` C ) ) $.
    0funcg.d $e |- ( ph -> D e. Cat ) $.
    $( The functor from the empty category.  (Contributed by Zhi Wang,
       17-Oct-2025.) $)
    0funcg2 $p |- ( ph -> ( F ( C Func D ) G <-> ( F = (/) /\ G = (/) ) ) ) $=
      ( vz vx vn vy co cfv cv wceq wral c0 eqid vm cfunc wbr cbs c1st c2nd chom
      wf cxp cmap cixp wcel ccid cop wa ccat 0catg syl2anc isfunc feq2d bitr3di
      cco f0bi wfn eqcomd rzal syl funcf2lem2 a1i mpbiran2d sqxpeqd 0xp eqtr3di
      wb fneq2d fn0 bitrdi bitrd 0funcglem ) ADEBCUBNUCBUDOZCUDOZDUHZEJVTVTUIZJ
      PZUEODOWDUFODOCUGOZNWDBUGOZOUJNUKULZKPZBUMOZOWHWHENOWHDOZCUMOZOQLPZUAPZWH
      MPZUNWDBVBOZNNWHWDENOWLWNWDENOWMWHWNENZOWJWNDOZUNWDDOCVBOZNNQLWNWDWFNRUAW
      HWNWFNZRJVTRMVTRUOZKVTRZDSQZESQZAKMJVTWABWOWIUALCDEWFWKWEWRVTTZWATWFTWETW
      ITWKTWOTWRTABFULSVTQBUPULGHBFUQURIUSASWADUHWBXBASVTWADHUTDWAVCVAAWGEWCVDZ
      XCAWGXEWSWJWQWENWPUHMVTRZKVTRZAVTSQZXGASVTHVEZXFKVTVFVGWGXEXGUOVNAKMJVTBU
      DDEWFWEXDVHVIVJAXEESVDXCAWCSEASSUIWCSASVTHVKSVLVMVOEVPVQVRAXHXAXIWTKVTVFV
      GVS $.

    $( The functor from the empty category.  Corollary of Definition 3.47 of
       [Adamek] p. 40, Definition 7.1 of [Adamek] p. 101, Example 3.3(4.c) of
       [Adamek] p. 24, and Example 7.2(3) of [Adamek] p. 101.  (Contributed by
       Zhi Wang, 17-Oct-2025.) $)
    0funcg $p |- ( ph -> ( C Func D ) = { <. (/) , (/) >. } ) $=
      ( vf vg cfunc co c0 cop csn relfunc 0ex cv wbr wceq cvv relsnop wa brsnop
      0funcg2 wcel wb mp2an bitr4di eqbrrdiv ) AHIBCJKZLLMNZBCOLLPPUAAHQZIQZUJR
      ULLSUMLSUBZULUMUKRZABCULUMDEFGUDLTUEZUPUOUNUFPPLLTTULUMUCUGUHUI $.
  $}

  ${
    0funclem.1 $e |- ( ph -> ( ps <-> ( ch /\ th /\ ta ) ) ) $.
    0funclem.2 $e |- ( ch <-> et ) $.
    0funclem.3 $e |- ( th <-> ze ) $.
    0funclem.4 $e |- ta $.
    $( Lemma for ~ 0funcALT .  (Contributed by Zhi Wang, 7-Oct-2025.) $)
    0funclem $p |- ( ph -> ( ps <-> ( et /\ ze ) ) ) $=
      ( wa wb w3a df-3an bitrdi rbaibd mpan2 anbi12i ) ABCDLZFGLAEBTMKABTEABCDE
      NTELHCDEOPQRCFDGIJSP $.
  $}

  ${
    $d C f g m n x y z $.  $d f g m n ph x y z $.
    0func.c $e |- ( ph -> C e. Cat ) $.
    $( The functor from the empty category.  (Contributed by Zhi Wang,
       7-Oct-2025.)  (Proof shortened by Zhi Wang, 17-Oct-2025.) $)
    0func $p |- ( ph -> ( (/) Func C ) = { <. (/) , (/) >. } ) $=
      ( c0 cvv wcel 0ex a1i cbs cfv wceq base0 0funcg ) ADBEDEFAGHDDIJKALHCM $.

    $( Alternate proof of ~ 0func .  (Contributed by Zhi Wang, 7-Oct-2025.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    0funcALT $p |- ( ph -> ( (/) Func C ) = { <. (/) , (/) >. } ) $=
      ( vf vz vx vn vm vy c0 co cop 0ex cv wceq cfv wcel wral eqid cvv vg cfunc
      csn relfunc relsnop wbr wa cbs wf cxp c1st c2nd chom cmap cixp ccid base0
      cco ccat 0cat a1i isfunc f0bi wfn ral0 funcf2lem2 mpbiran2 0xp fneq2i fn0
      3bitri 0funclem wb brsnop mp2an bitr4di eqbrrdiv ) ADUAJBUBKZJJLUCZJBUDJJ
      MMUEADNZUANZVRUFZVTJOZWAJOZUGZVTWAVSUFZAWBJBUHPZVTUIWAEJJUJZENZUKPVTPWIUL
      PVTPBUMPZKWIJUMPZPUNKUOQZFNZJUPPZPWMWMWAKPWMVTPZBUPPZPOGNZHNZWMINZLWIJURP
      ZKKWMWIWAKPWQWSWIWAKPWRWMWSWAKZPWOWSVTPZLWIVTPBURPZKKOGWSWIWKKRHWMWSWKKZR
      EJRIJRUGZFJRWCWDAFIEJWGJWTWNHGBVTWAWKWPWJXCUQWGSWKSWJSWNSWPSWTSXCSJUSQAUT
      VACVBVTWGVCWLWAWHVDZWAJVDWDWLXFXDWOXBWJKXAUIIJRZFJRXGFVEFIEJJUHVTWAWKWJUQ
      VFVGWHJWAJVHVIWAVJVKXEFVEVLJTQZXHWFWEVMMMJJTTVTWAVNVOVPVQ $.
  $}

  ${
    func0g.a $e |- A = ( Base ` C ) $.
    func0g.b $e |- B = ( Base ` D ) $.
    func0g.d $e |- ( ph -> B = (/) ) $.
    ${
      func0g.f $e |- ( ph -> F ( C Func D ) G ) $.
      $( The source category of a functor to the empty category must be empty
         as well.  (Contributed by Zhi Wang, 19-Oct-2025.) $)
      func0g $p |- ( ph -> A = (/) ) $=
        ( c0 wceq funcf1 f002 mpd ) ACLMBLMJABCFABCDEFGHIKNOP $.
    $}

    func0g2.f $e |- ( ph -> F e. ( C Func D ) ) $.
    $( The source category of a functor to the empty category must be empty as
       well.  (Contributed by Zhi Wang, 19-Oct-2025.) $)
    func0g2 $p |- ( ph -> A = (/) ) $=
      ( c1st cfv c2nd func1st2nd func0g ) ABCDEFKLFMLGHIADEFJNO $.
  $}

  ${
    $d C d f $.
    $( Sets with empty base are the only initial objects in the category of
       small categories.  Example 7.2(3) of [Adamek] p. 101.  (Contributed by
       Zhi Wang, 15-Nov-2025.) $)
    initc $p |- ( ( C e. _V /\ (/) = ( Base ` C ) )
           <-> A. d e. Cat E! f f e. ( C Func d ) ) $=
      ( cvv wcel c0 cbs cfv wceq wa cv cfunc weu ccat wral csn wex cop simpll
      co simplr simpr 0funcg opex sneq eqeq2d syl eusn sylibr ralrimiva wi 0cat
      spcev oveq2 eleq2d eubidv rspcv ax-mp euex funcrcl elexd eqid base0 eqidd
      simpld id func0g2 eqcomd jca exlimiv 3syl impbii ) ADEZFAGHZIZJZBKZACKZLT
      ZEZBMZCNOZVPWACNVPVRNEZJZVSVQPZIZBQZWAWDVSFFRZPZIZWGWDAVRDVMVOWCSVMVOWCUA
      VPWCUBUCWFWJBWHFFUDVQWHIWEWIVSVQWHUEUFUMUGBVSUHUIUJWBVQAFLTZEZBMZWLBQVPFN
      EZWBWMUKULWAWMCFNVRFIZVTWLBWOVSWKVQVRFALUNUOUPUQURWLBUSWLVPBWLVMVOWLANWLA
      NEWNAFVQUTVEVAWLVNFWLVNFAFVQVNVBVCWLFVDWLVFVGVHVIVJVKVL $.
  $}

  ${
    cofu1st2nd.f $e |- ( ph -> F e. ( C Func D ) ) $.
    cofu1st2nd.g $e |- ( ph -> G e. ( D Func E ) ) $.
    $( Rewrite the functor composition with separated functor parts.
       (Contributed by Zhi Wang, 15-Nov-2025.) $)
    cofu1st2nd $p |- ( ph -> ( G o.func F ) = ( <. ( 1st ` G ) , ( 2nd ` G ) >.
                       o.func <. ( 1st ` F ) , ( 2nd ` F ) >. ) ) $=
      ( c1st cfv c2nd cop cfunc co wrel wcel wceq relfunc 1st2nd sylancr ccofu
      oveq12d ) AFFIJFKJLZEEIJEKJLZUAACDMNZOFUEPFUCQCDRHFUESTABCMNZOEUFPEUDQBCR
      GEUFSTUB $.
  $}

  ${
    $d C f g x y $.  $d D f g x y $.  $d E f g x y $.
    $( The restriction of functor composition is a function from product
       functor space to functor space.  (Contributed by Zhi Wang,
       25-Sep-2025.) $)
    rescofuf $p |- ( o.func |` ( ( D Func E ) X. ( C Func D ) ) ) :
        ( ( D Func E ) X. ( C Func D ) ) --> ( C Func E ) $=
      ( vg vf vx vy cv c1st cfv ccom c2nd cdm co cmpo cfunc wcel wral ccofu cvv
      cop cxp cres wf wa wceq vex opex df-cofu ovmpt4g mp3an simpr simpl cofucl
      eqeltrrid rgen2 reseq1i wss ssv resmpo mp2an eqtri fmpo mpbi ) DHZIJEHZIJ
      ZKZFGVFLJZMMZVJFHZVGJGHZVGJVELJNVKVLVINKOZUAZACPNZQZEABPNZRDBCPNZRVRVQUBZ
      VOSVSUCZUDVPDEVRVQVEVRQZVFVQQZUEZVNVEVFSNZVOVETQVFTQVNTQWDVNUFDUGEUGVHVMU
      HDETTVNSTFGEDUIZUJUKWCABCVFVEWAWBULWAWBUMUNUOUPDEVRVQVNVOVTVTDETTVNOZVSUC
      ZDEVRVQVNOZSWFVSWEUQVRTURVQTURWGWHUFVRUSVQUSDETTVRVQVNUTVAVBVCVD $.
  $}

  ${
    cofu1a.b $e |- B = ( Base ` C ) $.
    cofu1a.f $e |- ( ph -> F ( C Func D ) G ) $.
    cofu1a.k $e |- ( ph -> K ( D Func E ) L ) $.
    cofu1a.m $e |- ( ph ->
            ( <. K , L >. o.func <. F , G >. ) = <. M , N >. ) $.
    cofu1a.x $e |- ( ph -> X e. B ) $.
    $( Value of the object part of the functor composition.  (Contributed by
       Zhi Wang, 16-Nov-2025.) $)
    cofu1a $p |- ( ph -> ( K ` ( F ` X ) ) = ( M ` X ) ) $=
      ( co c1st cfv cop ccofu cfunc wbr wcel df-br sylib fveq2d cofucl eqeltrrd
      cofu1 sylibr func1st eqtrd fveq1d fveq12d 3eqtr3rd ) ALHIUAZFGUAZUBRZSTZT
      LUSSTZTZURSTZTLJTLFTZHTABCDEUSURLMAFGCDUCRZUDUSVFUENFGVFUFUGZAHIDEUCRZUDU
      RVHUEOHIVHUFUGZQUKALVAJAVAJKUAZSTJAUTVJSPUHACEJKAVJCEUCRZUEJKVKUDAUTVJVKP
      ACDEUSURVGVIUIUJJKVKUFULUMUNUOAVCVEVDHADEHIOUMALVBFACDFGNUMUOUPUQ $.

    cofu2a.y $e |- ( ph -> Y e. B ) $.
    cofu2a.h $e |- H = ( Hom ` C ) $.
    cofu2a.r $e |- ( ph -> R e. ( X H Y ) ) $.
    $( Value of the morphism part of the functor composition.  (Contributed by
       Zhi Wang, 16-Nov-2025.) $)
    cofu2a $p |- ( ph -> ( ( ( F ` X ) L ( F ` Y ) ) ` ( ( X G Y ) ` R ) )
            = ( ( X N Y ) ` R ) ) $=
      ( cop ccofu co c2nd cfv c1st cfunc wcel df-br sylib cofu2 fveq2d eqeltrrd
      wbr cofucl sylibr func2nd eqtrd fveq1d func1st oveq123d fveq12d 3eqtr3rd
      oveqd ) AENOJKUDZGHUDZUEUFZUGUHZUFZUHENOVIUGUHZUFZUHZNVIUIUHZUHZOVPUHZVHU
      GUHZUFZUHENOMUFZUHENOHUFZUHZNGUHZOGUHZKUFZUHABCDEFVIVHINOPAGHCDUJUFZUQVIW
      GUKQGHWGULUMZAJKDFUJUFZUQVHWIUKRJKWIULUMZTUAUBUCUNAEVLWAAVKMNOAVKLMUDZUGU
      HMAVJWKUGSUOACFLMAWKCFUJUFZUKLMWLUQAVJWKWLSACDFVIVHWHWJURUPLMWLULUSUTVAVG
      VBAVOWCVTWFAVQWDVRWEVSKADFJKRUTANVPGACDGHQVCZVBAOVPGWMVBVDAEVNWBAVMHNOACD
      GHQUTVGVBVEVF $.
  $}

  ${
    cofucla.f $e |- ( ph -> F ( C Func D ) G ) $.
    cofucla.k $e |- ( ph -> K ( D Func E ) L ) $.
    $( The composition of two functors is a functor.  Proposition 3.23 of
       [Adamek] p. 33.  (Contributed by Zhi Wang, 16-Nov-2025.) $)
    cofucla $p |- ( ph ->
            ( <. K , L >. o.func <. F , G >. ) e. ( C Func E ) ) $=
      ( cop cfunc co wbr wcel df-br sylib cofucl ) ABCDEFKZGHKZAEFBCLMZNSUAOIEF
      UAPQAGHCDLMZNTUBOJGHUBPQR $.
  $}

  ${
    $d A x y $.  $d B x y $.  $d C x y $.  $d D x y $.  $d F x y $.
    $d G x y $.  $d ph x y $.
    funchomf.1 $e |- ( ph -> F ( A Func C ) G ) $.
    funchomf.2 $e |- ( ph -> F ( B Func D ) G ) $.
    $( Source categories of a functor have the same set of objects and
       morphisms.  (Contributed by Zhi Wang, 10-Nov-2025.) $)
    funchomf $p |- ( ph -> ( Homf ` A ) = ( Homf ` B ) ) $=
      ( vx vy cfv wceq chom co cbs wfn eqid adantr ffnd chomf cv wral cfunc wbr
      wcel wa simprl simprr funcf2 funcf1 fndmu syl2anc ralrimivva eqidd homfeq
      eleqtrd mpbird ) ABUALCUALMJUBZKUBZBNLZOZUSUTCNLZOZMZKBPLZUCJVFUCAVEJKVFV
      FAUSVFUFZUTVFUFZUGZUGZUSUTGOZVBQVKVDQVEVJVBUSFLZUTFLZDNLZOVKVJVFBDFGVAVNU
      SUTVFRZVARZVNRAFGBDUDOUEVIHSAVGVHUHZAVGVHUIZUJTVJVDVLVMENLZOVKVJCPLZCEFGV
      CVSUSUTVTRZVCRZVSRAFGCEUDOUEVIISVJUSVFVTVQAVFVTMZVIAFVFQFVTQWCAVFDPLZFAVF
      WDBDFGVOWDRHUKTAVTEPLZFAVTWECEFGWAWERIUKTVFVTFULUMZSZUQVJUTVFVTVRWGUQUJTV
      BVDVKULUMUNAJKVFBCVAVCVPWBAVFUOWFUPUR $.
  $}

  ${
    $d C b t z $.  $d D b t z $.  $d E b t z $.
    $( Reverse closure for an identity functor.  (Contributed by Zhi Wang,
       10-Nov-2025.) $)
    idfurcl $p |- ( ( idFunc ` C ) e. ( D Func E ) -> C e. Cat ) $=
      ( vt vb vz cfunc co ccat cidfu cv cbs cfv cid cres cxp chom cmpt cop csb
      opex csbex df-idfu dmmpti wrel c0 wcel wn relfunc 0nelrel0 ax-mp ndmfvrcl
      ) ABCGHZIJDIEDKZLMZNEKZOZFUPUPPNFKUNQMMORZSZTJEUOUSUQURUAUBFDEUCUDUMUEUFU
      MUGUHBCUIUMUJUKUL $.
  $}

  ${
    idfu1stf1o.i $e |- I = ( idFunc ` C ) $.
    idfu1stf1o.b $e |- B = ( Base ` C ) $.
    $( The identity functor/inclusion functor is bijective on objects.
       (Contributed by Zhi Wang, 16-Nov-2025.) $)
    idfu1stf1o $p |- ( C e. Cat -> ( 1st ` I ) : B -1-1-onto-> B ) $=
      ( ccat wcel c1st cfv wf1o cid cres f1oi id idfu1st f1oeq1d mpbiri ) BFGZA
      ACHIZJAAKALZJAMRAASTRABCDERNOPQ $.
  $}

  ${
    idfu2nda.i $e |- I = ( idFunc ` C ) $.
    idfu2nda.d $e |- ( ph -> I e. ( D Func E ) ) $.
    idfu2nda.b $e |- ( ph -> B = ( Base ` D ) ) $.
    $( Lemma for ~ idfu1sta .  (Contributed by Zhi Wang, 10-Nov-2025.) $)
    idfu1stalem $p |- ( ph -> B = ( Base ` C ) ) $=
      ( cbs cfv c1st c2nd cidfu cfunc co wcel ccat eqeltrrid func1st2nd idfurcl
      idfucl 3syl funchomf homfeqbas eqtr4d ) ABDJKCJKIACDACDCEFLKFMKACCFACNKZD
      EOPZQCRQFCCOPQAUGFUHGHSCDEUACFGUBUCTADEFHTUDUEUF $.

    $( Value of the object part of the identity functor.  (Contributed by Zhi
       Wang, 10-Nov-2025.) $)
    idfu1sta $p |- ( ph -> ( 1st ` I ) = ( _I |` B ) ) $=
      ( c1st cfv cid cbs cres eqid cidfu cfunc co wcel ccat idfurcl syl idfu1st
      eqeltrrid idfu1stalem reseq2d eqtr4d ) AFJKLCMKZNLBNAUHCFGUHOACPKZDEQRZSC
      TSAUIFUJGHUDCDEUAUBUCABUHLABCDEFGHIUEUFUG $.

    idfu2nda.x $e |- ( ph -> X e. B ) $.
    $( Value of the object part of the identity functor.  (Contributed by Zhi
       Wang, 10-Nov-2025.) $)
    idfu1a $p |- ( ph -> ( ( 1st ` I ) ` X ) = X ) $=
      ( cbs cfv eqid cidfu cfunc co wcel ccat eqeltrrid idfurcl syl idfu1stalem
      eleqtrd idfu1 ) ACLMZCFGHUFNACOMZDEPQZRCSRAUGFUHHITCDEUAUBAGBUFKABCDEFHIJ
      UCUDUE $.

    idfu2nda.y $e |- ( ph -> Y e. B ) $.
    idfu2nda.h $e |- ( ph -> H = ( X ( Hom ` D ) Y ) ) $.
    $( Value of the morphism part of the identity functor.  (Contributed by Zhi
       Wang, 10-Nov-2025.) $)
    idfu2nda $p |- ( ph -> ( X ( 2nd ` I ) Y ) = ( _I |` H ) ) $=
      ( cfv co cid eqid wcel c2nd chom cres cbs cidfu cfunc idfurcl idfu1stalem
      ccat eqeltrrid syl eleqtrd idfu2nd c1st idfucl func1st2nd funchomf eqtr4d
      homfeqval reseq2d ) AHIGUAPZQRHICUBPZQZUCRFUCACUDPZCVBGHIJVDSZACUEPZDEUFQ
      ZTCUITZAVFGVGJKUJCDEUGUKZVBSZAHBVDMABCDEGJKLUHZULZAIBVDNVKULZUMAFVCRAFHID
      UBPZQVCOAVDCDVBVNHIVEVJVNSACDCEGUNPVAACCGAVHGCCUFQTVICGJUOUKUPADEGKUPUQVL
      VMUSURUTUR $.
  $}

  ${
    $d A x $.  $d B x $.  $d F x $.  $d G x $.
    imasubclem1.f $e |- ( ph -> F e. V ) $.
    imasubclem1.g $e |- ( ph -> G e. W ) $.
    $( Lemma for ~ imasubc .  (Contributed by Zhi Wang, 6-Nov-2025.) $)
    imasubclem1 $p |- ( ph -> U_ x e. ( ( `' F " A ) X. ( `' G " B ) )
                               ( ( H ` C ) " D ) e. _V ) $=
      ( ccnv cima cvv wcel cnvexg syl imaexd cxp cfv wral ciun xpexd fvex imaex
      rgenw iunexg sylancl ) AGNZCOZHNZDOZUAZPQEIUBZFOZPQZBUOUCBUOUQUDPQAULUNPP
      AUKCPAGJQUKPQLGJRSTAUMDPAHKQUMPQMHKRSTUEURBUOUPFEIUFUGUHBUOUQPPUIUJ $.

    ${
      $d X y z $.  $d Y y z $.  $d ph y z $.
      imasubclem2.k $e |- K = ( y e. X , z e. Y |-> U_ x
                            e. ( ( `' F " A ) X. ( `' G " B ) )
                               ( ( H ` C ) " D ) ) $.
      $( Lemma for ~ imasubc .  (Contributed by Zhi Wang, 7-Nov-2025.) $)
      imasubclem2 $p |- ( ph -> K Fn ( X X. Y ) ) $=
        ( cima ccnv cxp cfv ciun cvv wcel wral wfn cv wa imasubclem1 ralrimivva
        adantr fnmpo syl ) ABIUAETJUAFTUBGKUCHTUDZUEUFZDPUGCOUGLOPUBUHAUQCDOPAU
        QCUIOUFDUIPUFUJABEFGHIJKMNQRUKUMULCDOPUPLUESUNUO $.
    $}

    $d A x y $.  $d B x y $.  $d C x y $.  $d D x y $.  $d F x y z $.
    $d G x y z $.  $d H x y $.  $d X x y z $.  $d Y x y z $.
    imasubclem3.x $e |- ( ph -> X e. A ) $.
    imasubclem3.y $e |- ( ph -> Y e. B ) $.
    imasubclem3.k $e |- K = ( x e. A , y e. B |-> U_ z
                           e. ( ( `' F " { x } ) X. ( `' G " { y } ) )
                              ( ( H ` C ) " D ) ) $.
    $( Lemma for ~ imasubc .  (Contributed by Zhi Wang, 7-Nov-2025.) $)
    imasubclem3 $p |- ( ph -> ( X K Y ) = U_ z
                           e. ( ( `' F " { X } ) X. ( `' G " { Y } ) )
                              ( ( H ` C ) " D ) ) $=
      ( wcel ccnv csn cima cxp cfv ciun co wceq imasubclem1 cv wa simpl imaeq2d
      cvv sneqd simpr xpeq12d iuneq1d ovmpoga syl3anc ) AOEUBPFUBDIUCZOUDZUEZJU
      CZPUDZUEZUFZGKUGHUEZUHZUPUBOPLUIVKUJSTADVDVGGHIJKMNQRUKBCOPEFDVCBULZUDZUE
      ZVFCULZUDZUEZUFZVJUHVKLUPVLOUJZVOPUJZUMZDVRVIVJWAVNVEVQVHWAVMVDVCWAVLOVSV
      TUNUQUOWAVPVGVFWAVOPVSVTURUQUOUSUTUAVAVB $.
  $}

  ${
    imaf1hom.s $e |- S = ( F " A ) $.
    imaf1hom.1 $e |- ( ph -> F : B -1-1-> C ) $.
    imaf1hom.x $e |- ( ph -> X e. S ) $.
    $( Lemma for ~ imaf1hom and other theorems.  (Contributed by Zhi Wang,
       7-Nov-2025.) $)
    imaf1homlem $p |- ( ph -> ( { ( `' F ` X ) } = ( `' F " { X } )
            /\ ( F ` ( `' F ` X ) ) = X /\ ( `' F ` X ) e. B ) ) $=
      ( ccnv cfv csn cima wceq wcel crn wfn syl syl2anc wf1o wf1 f1f1orn dff1o4
      simprbi imassrn eleqtrdi sselid fnsnfv f1ocnvfv2 f1ocnvdm 3jca ) AGFKZLZM
      UMGMNOZUNFLGOZUNCPZAUMFQZRZGURPZUOACURFUAZUSACDFUBVAICDFUCSZVAFCRUSCURFUD
      UESAFBNZURGFBUFAGEVCJHUGUHZURGUMUITAVAUTUPVBVDCURGFUJTAVAUTUQVBVDCURGFUKT
      UL $.

    $d F p x y $.  $d G p x y $.  $d H p x y $.  $d S x y $.  $d X p x y $.
    $d Y p x y $.
    imaf1hom.y $e |- ( ph -> Y e. S ) $.
    imaf1hom.f $e |- ( ph -> F e. V ) $.
    imaf1hom.k $e |- K = ( x e. S , y e. S |-> U_ p e.
        ( ( `' F " { x } ) X. ( `' F " { y } ) ) ( ( G ` p ) " ( H ` p ) ) ) $.
    $( The hom-set of an image of a functor injective on objects.  (Contributed
       by Zhi Wang, 7-Nov-2025.) $)
    imaf1hom $p |- ( ph -> ( X K Y ) = ( ( ( `' F ` X ) G ( `' F ` Y ) )
                                  " ( ( `' F ` X ) H ( `' F ` Y ) ) ) ) $=
      ( ccnv cfv cop csn cima ciun cxp imasubclem3 wceq wcel imaf1homlem simp1d
      co cv xpeq12d fvex xpsn eqtr3di iuneq1d eqtrd opex fveq2 eqtr4di imaeq12d
      df-ov iunxsn eqtrdi ) AMNKUNZOMHUBZUCZNVJUCZUDZUEZOUOZIUCZVOJUCZUFZUGZVKV
      LIUNZVKVLJUNZUFZAVIOVJMUEUFZVJNUEUFZUHZVRUGVSABCOGGVOVQHHIKLLMNTTRSUAUIAO
      WEVNVRAVKUEZVLUEZUHWEVNAWFWCWGWDAWFWCUJVKHUCMUJVKEUKADEFGHMPQRULUMAWGWDUJ
      VLHUCNUJVLEUKADEFGHNPQSULUMUPVKVLMVJUQNVJUQURUSUTVAOVMVRWBVKVLVBVOVMUJZVP
      VTVQWAWHVPVMIUCVTVOVMIVCVKVLIVFVDWHVQVMJUCWAVOVMJVCVKVLJVFVDVEVGVH $.
  $}

  ${
    imaidfu.i $e |- I = ( idFunc ` C ) $.
    imaidfu.d $e |- ( ph -> I e. ( D Func E ) ) $.
    $( Lemma for ~ imaidfu2 .  (Contributed by Zhi Wang, 10-Nov-2025.) $)
    imaidfu2lem $p |- ( ph ->
            ( ( 1st ` I ) " ( Base ` D ) ) = ( Base ` D ) ) $=
      ( c1st cfv cbs cima cid cres eqidd idfu1sta imaeq1d wss wceq ssid resiima
      ax-mp eqtrdi ) AEHIZCJIZKLUDMZUDKZUDAUCUEUDAUDBCDEFGAUDNOPUDUDQUFUDRUDSUD
      UDTUAUB $.

    imaidfu.h $e |- H = ( Hom ` D ) $.
    imaidfu.j $e |- J = ( Homf ` D ) $.
    imaidfu.k $e |- K = ( x e. S , y e. S |-> U_ p e.
        ( ( `' ( 1st ` I ) " { x } ) X. ( `' ( 1st ` I ) " { y } ) )
        ( ( ( 2nd ` I ) ` p ) " ( H ` p ) ) ) $.
    ${
      $d H p x y $.  $d I p x y $.  $d J q w z $.  $d K q w z $.  $d S q w z $.
      $d S w x y z $.  $d p w x y z $.  $d ph w x y z $.
      imaidfu.s $e |- S = ( ( 1st ` I ) " A ) $.
      $( The image of the identity functor.  (Contributed by Zhi Wang,
         10-Nov-2025.) $)
      imaidfu $p |- ( ph -> ( J |` ( S X. S ) ) = K ) $=
        ( cfv vq vz vw cxp cres wceq cv wral co wcel wa c1st ccnv c2nd cima cid
        cbs eqidd idfu1sta adantr cnveqd cnvresid eqtrdi fveq1d wss crn imassrn
        eqsstri rneqd rnresi sseqtrid simprl sseldd fvresi eqtrd simprr oveq12d
        syl imaeq12d cvv wf1o wf1 f1oi f1oeq1d mpbiri f1of1 fvexd imaf1hom eqid
        homfval cfunc chom oveqi a1i idfu2nda imaeq1d ssid resiima ax-mp eqtr4d
        3eqtr4rd ralrimivva cop fveq2 df-ov eqtr4di eqeq12d ralxp sylibr wfn wb
        homffn csn imasubclem2 xpss12 syl2anc fvreseq1 syl21anc mpbird ) AKGGUD
        ZUELUFZUAUGZKTZYBLTZUFZUAXTUHZAUBUGZUCUGZKUIZYGYHLUIZUFZUCGUHUBGUHYFAYK
        UBUCGGAYGGUJZYHGUJZUKZUKZYGJULTZUMZTZYHYQTZJUNTZUIZYRYSIUIZUOYGYHYTUIZY
        GYHIUIZUOZYJYIYOUUAUUCUUBUUDYOYRYGYSYHYTYOYRYGUPFUQTZUEZTZYGYOYGYQUUGYO
        YQUUGUMUUGYOYPUUGAYPUUGUFYNAUUFEFHJNOAUUFURUSZUTZVAUUFVBVCZVDYOYGUUFUJU
        UHYGUFYOGUUFYGAGUUFVEZYNAYPVFZGUUFGYPDUOUUMSYPDVGVHAUUMUUGVFUUFAYPUUGUU
        IVIUUFVJVCVKZUTZAYLYMVLZVMZUUFYGVNVRVOZYOYSYHUUGTZYHYOYHYQUUGUUKVDYOYHU
        UFUJUUSYHUFYOGUUFYHUUOAYLYMVPZVMZUUFYHVNVRVOZVQYOYRYGYSYHIUURUVBVQVSYOB
        CDUUFUUFGYPYTILVTYGYHMSYOUUFUUFYPWAZUUFUUFYPWBYOUVCUUFUUFUUGWAUUFWCYOUU
        FUUFYPUUGUUJWDWEUUFUUFYPWFVRUUPUUTYOJULWGRWHYOYIUUDUUEYOUUFFKIYGYHQUUFW
        IZPUUQUVAWJYOUUEUPUUDUEZUUDUOZUUDYOUUCUVEUUDYOUUFEFHUUDJYGYHNAJFHWKUIUJ
        YNOUTYOUUFURUUQUVAUUDYGYHFWLTZUIUFYOIUVGYGYHPWMWNWOWPUUDUUDVEUVFUUDUFUU
        DWQUUDUUDWRWSVCWTXAXBYEYKUAUBUCGGYBYGYHXCZUFZYCYIYDYJUVIYCUVHKTYIYBUVHK
        XDYGYHKXEXFUVIYDUVHLTYJYBUVHLXDYGYHLXEXFXGXHXIAKUUFUUFUDZXJZLXTXJXTUVJV
        EZYAYFXKUVKAUUFFKQUVDXLWNAMBCBUGXMCUGXMMUGZUVMITYPYPYTLVTVTGGAJULWGZUVN
        RXNAUULUULUVLUUNUUNGUUFGUUFXOXPUAUVJXTKLXQXRXS $.
    $}

    $d D x y $.  $d H p x y $.  $d I p x y $.  $d ph x y $.
    imaidfu2.s $e |- ( ph -> S = ( Base ` D ) ) $.
    $( The image of the identity functor.  (Contributed by Zhi Wang,
       10-Nov-2025.) $)
    imaidfu2 $p |- ( ph -> J = K ) $=
      ( cfv cima c1st ccnv cv csn cxp c2nd ciun cmpo cbs cres imaidfu cid eqidd
      eqid idfu1sta imaeq1d wss wceq ssid resiima eqtrdi sqxpeqd reseq2d homffn
      ax-mp wfn fnresdm 3eqtr4a mpoeq123dv 3eqtr3d eqtr4di ) AJBCFFLIUASZUBZBUC
      UDTVMCUCUDTUELUCZIUFSSVNHSTUGZUHZKAJVLEUISZTZVRUEZUJZBCVRVRVOUHZJVPABCVQD
      EVRGHIJWALMNOPWAUNVRUNUKAVTJVQVQUEZUJZJAVSWBJAVRVQAVRULVQUJZVQTZVQAVLWDVQ
      AVQDEGIMNAVQUMUOUPZVQVQUQWEVQURVQUSVQVQUTVEZVAVBVCJWBVFWCJURVQEJPVQUNVDWB
      JVGVEVAABCVRVRVOFFVOAWEVQVRFWGWFRVHZWHAVOUMVIVJQVK $.
  $}

  ${
    cofid1a.i $e |- I = ( idFunc ` D ) $.
    cofid1a.b $e |- B = ( Base ` D ) $.
    cofid1a.x $e |- ( ph -> X e. B ) $.
    ${
      cofid1a.f $e |- ( ph -> F e. ( D Func E ) ) $.
      cofid1a.g $e |- ( ph -> G e. ( E Func D ) ) $.
      cofid1a.o $e |- ( ph -> ( G o.func F ) = I ) $.
      $( Express the object part of ` ( G o.func F ) = I ` explicitly.
         (Contributed by Zhi Wang, 15-Nov-2025.) $)
      cofid1a $p |- ( ph ->
              ( ( 1st ` G ) ` ( ( 1st ` F ) ` X ) ) = X ) $=
        ( ccofu co c1st cfv fveq2d fveq1d cofu1 c2nd func1st2nd funcrcl2 idfu1
        3eqtr3d ) AHFEOPZQRZRHGQRZRHEQRZRFQRRHAHUHUIAUGGQNSTABCDCEFHJLMKUAABCGH
        IJACDUJEUBRACDELUCUDKUEUF $.

      cofid2a.y $e |- ( ph -> Y e. B ) $.
      cofid2a.h $e |- H = ( Hom ` D ) $.
      cofid2a.r $e |- ( ph -> R e. ( X H Y ) ) $.
      $( Express the morphism part of ` ( G o.func F ) = I ` explicitly.
         (Contributed by Zhi Wang, 15-Nov-2025.) $)
      cofid2a $p |- ( ph
         -> ( ( ( ( 1st ` F ) ` X ) ( 2nd ` G ) ( ( 1st ` F ) ` Y ) )
            ` ( ( X ( 2nd ` F ) Y ) ` R ) ) = R ) $=
        ( ccofu co c2nd cfv fveq2d oveqd fveq1d cofu2 func1st2nd funcrcl2 idfu2
        c1st 3eqtr3d ) ADJKGFUAUBZUCUDZUBZUDDJKIUCUDZUBZUDDJKFUCUDZUBUDJFULUDZU
        DKUTUDGUCUDUBUDDADUPURAUOUQJKAUNIUCQUEUFUGABCEDCFGHJKMOPNRSTUHABCDHIJKL
        MACEUTUSACEFOUIUJSNRTUKUM $.
    $}

    ${
      cofid1.f $e |- ( ph -> F ( D Func E ) G ) $.
      cofid1.k $e |- ( ph -> K ( E Func D ) L ) $.
      cofid1.o $e |- ( ph -> ( <. K , L >. o.func <. F , G >. ) = I ) $.
      $( Express the object part of ` ( G o.func F ) = I ` explicitly.
         (Contributed by Zhi Wang, 15-Nov-2025.) $)
      cofid1 $p |- ( ph -> ( K ` ( F ` X ) ) = X ) $=
        ( cop c1st cfv func1st fveq1d fveq12d cfunc co wcel df-br sylib cofid1a
        wbr eqtr3d ) AJEFQZRSZSZHIQZRSZSJESZHSJAUMUPUOHADCHIOTAJULEACDEFNTUAUBA
        BCDUKUNGJKLMAEFCDUCUDZUIUKUQUENEFUQUFUGAHIDCUCUDZUIUNURUEOHIURUFUGPUHUJ
        $.

      cofid2.y $e |- ( ph -> Y e. B ) $.
      cofid2.h $e |- H = ( Hom ` D ) $.
      cofid2.r $e |- ( ph -> R e. ( X H Y ) ) $.
      $( Express the morphism part of ` ( G o.func F ) = I ` explicitly.
         (Contributed by Zhi Wang, 15-Nov-2025.) $)
      cofid2 $p |- ( ph ->
              ( ( ( F ` X ) L ( F ` Y ) ) ` ( ( X G Y ) ` R ) ) = R ) $=
        ( cop c2nd cfv c1st func2nd func1st fveq1d oveq123d oveqd fveq12d cfunc
        co wbr wcel df-br sylib cofid2a eqtr3d ) ADLMFGUCZUDUEZUNZUEZLVAUFUEZUE
        ZMVEUEZJKUCZUDUEZUNZUEDLMGUNZUEZLFUEZMFUEZKUNZUEDAVDVLVJVOAVFVMVGVNVIKA
        ECJKRUGALVEFACEFGQUHZUIAMVEFVPUIUJADVCVKAVBGLMACEFGQUGUKUIULABCDEVAVHHI
        LMNOPAFGCEUMUNZUOVAVQUPQFGVQUQURAJKECUMUNZUOVHVRUPRJKVRUQURSTUAUBUSUT
        $.
    $}
  $}

  ${
    $d B x y $.  $d B z $.  $d D z $.  $d F x y $.  $d G x y $.  $d H z $.
    $d ph x y $.  $d ph z $.
    cofidvala.i $e |- I = ( idFunc ` D ) $.
    cofidvala.b $e |- B = ( Base ` D ) $.
    cofidvala.f $e |- ( ph -> F e. ( D Func E ) ) $.
    cofidvala.g $e |- ( ph -> G e. ( E Func D ) ) $.
    cofidvala.o $e |- ( ph -> ( G o.func F ) = I ) $.
    ${
      cofidvala.h $e |- H = ( Hom ` D ) $.
      $( The property " ` F ` is a section of ` G ` " in a category of small
         categories (in a universe); expressed explicitly.  (Contributed by Zhi
         Wang, 15-Nov-2025.) $)
      cofidvala $p |- ( ph -> ( ( ( 1st ` G ) o. ( 1st ` F ) ) = ( _I |` B )
         /\ ( x e. B , y e. B |-> ( ( ( ( 1st ` F ) ` x ) ( 2nd ` G )
              ( ( 1st ` F ) ` y ) ) o. ( x ( 2nd ` F ) y ) ) )
          = ( z e. ( B X. B ) |-> ( _I |` ( H ` z ) ) ) ) ) $=
        ( cfv cv co c1st ccom c2nd cmpo cop cid cres cmpt wceq wa ccofu cofuval
        cxp func1st2nd funcrcl2 idfuval 3eqtr3d cvv wcel cbs fvexi resiexg xpex
        ax-mp mptex opth2 sylib ) AIUARHUARZUBZBCEEBSZVHRCSZVHRIUCRTVJVKHUCRZTU
        BUDZUEZUFEUGZDEEUMZUFDSJRUGZUHZUEZUIVIVOUIVMVRUIUJAIHUKTKVNVSPABCEFGFHI
        MNOULADEFJKLMAFGVHVLAFGHNUNUOQUPUQVIVMVOVREURUSVOURUSEFUTMVAZEURVBVDDVP
        VQEEVTVTVCVEVFVG $.

      cofidf2a.j $e |- J = ( Hom ` E ) $.
      cofidf2a.x $e |- ( ph -> X e. B ) $.
      cofidf2a.y $e |- ( ph -> Y e. B ) $.
      $( If " ` F ` is a section of ` G ` " in a category of small categories
         (in a universe), then the morphism part of ` F ` is injective, and the
         morphism part of ` G ` is surjective in the image of ` F ` .
         (Contributed by Zhi Wang, 15-Nov-2025.) $)
      cofidf2a $p |- ( ph -> ( ( X ( 2nd ` F ) Y ) : ( X H Y ) -1-1->
                                ( ( ( 1st ` F ) ` X ) J ( ( 1st ` F ) ` Y ) )
      /\ ( ( ( 1st ` F ) ` X ) ( 2nd ` G ) ( ( 1st ` F ) ` Y ) )
       : ( ( ( 1st ` F ) ` X ) J ( ( 1st ` F ) ` Y ) ) -onto-> ( X H Y ) ) ) $=
        ( co c1st cfv c2nd wf1 wfo ccom cid cres func1st2nd funcf2 ccofu fveq2d
        wf oveqd cofu2nd funcrcl2 idfu2nd 3eqtr3d fcof1 syl2anc cofid1a oveq12d
        wceq cbs eqid funcf1 ffvelcdmd feq3dd fcofo syl3anc jca ) AJKGUAZJEUBUC
        ZUCZKVNUCZIUAZJKEUDUCZUAZUEZVQVMVOVPFUDUCZUAZUFZAVMVQVSUNZWBVSUGZUHVMUI
        ZVDZVTABCDVNVRGIJKMQRACDENUJZSTUKZAJKFEULUAZUDUCZUAJKHUDUCZUAWEWFAWKWLJ
        KAWJHUDPUMUOABCDCEFJKMNOSTUPABCGHJKLMACDVNVRWHUQQSTURUSZVMVQWBVSUTVAAVQ
        VMWBUNWDWGWCAVQVOFUBUCZUCZVPWNUCZGUAVMWBAWOJWPKGABCDEFHJLMSNOPVBABCDEFH
        KLMTNOPVBVCADVEUCZDCWNWAIGVOVPWQVFZRQADCFOUJABWQJVNABWQCDVNVRMWRWHVGZSV
        HABWQKVNWSTVHUKVIWIWMVQVMVSWBVJVKVL $.
    $}

    cofidf1a.c $e |- C = ( Base ` E ) $.
    $( If " ` F ` is a section of ` G ` " in a category of small categories (in
       a universe), then the object part of ` F ` is injective, and the object
       part of ` G ` is surjective.  (Contributed by Zhi Wang, 15-Nov-2025.) $)
    cofidf1a $p |- ( ph -> ( ( 1st ` F ) : B -1-1-> C
                            /\ ( 1st ` G ) : C -onto-> B ) ) $=
      ( vx vy vz c1st cfv cv wf1 wfo wf ccom cid cres wceq func1st2nd funcf1 co
      c2nd cmpo cxp chom cmpt eqid cofidvala simpld fcof1 syl2anc fcofo syl3anc
      jca ) ABCFRSZUAZCBGRSZUBZABCVDUCZVFVDUDUEBUFUGZVEABCDEVDFUKSZJNADEFKUHUIZ
      AVIOPBBOTZVDSPTZVDSGUKSZUJVLVMVJUJUDULQBBUMUEQTDUNSZSUFUOUGAOPQBDEFGVOHIJ
      KLMVOUPUQURZBCVFVDUSUTACBVFUCVHVIVGACBEDVFVNNJAEDGLUHUIVKVPCBVDVFVAVBVC
      $.
  $}

  ${
    $d B x y $.  $d B z $.  $d D z $.  $d F x y $.  $d G x y $.  $d H z $.
    $d K x y $.  $d L x y $.  $d ph x y $.  $d ph z $.
    cofidval.i $e |- I = ( idFunc ` D ) $.
    cofidval.b $e |- B = ( Base ` D ) $.
    cofidval.f $e |- ( ph -> F ( D Func E ) G ) $.
    cofidval.k $e |- ( ph -> K ( E Func D ) L ) $.
    cofidval.o $e |- ( ph -> ( <. K , L >. o.func <. F , G >. ) = I ) $.
    ${
      cofidval.h $e |- H = ( Hom ` D ) $.
      $( The property " ` <. F , G >. ` is a section of ` <. K , L >. ` " in a
         category of small categories (in a universe); expressed explicitly.
         (Contributed by Zhi Wang, 15-Nov-2025.) $)
      cofidval $p |- ( ph -> ( ( K o. F ) = ( _I |` B )
       /\ ( x e. B , y e. B |-> ( ( ( F ` x ) L ( F ` y ) ) o. ( x G y ) ) )
        = ( z e. ( B X. B ) |-> ( _I |` ( H ` z ) ) ) ) ) $=
        ( cop ccom cv cfv co cmpo cid cres cmpt wceq wa ccofu cofuval2 funcrcl2
        cxp idfuval 3eqtr3d cvv wcel fvexi resiexg ax-mp xpex mptex opth2 sylib
        cbs ) ALHUAZBCEEBUBZHUCCUBZHUCMUDVHVIIUDUAUEZTZUFEUGZDEEUNZUFDUBJUCUGZU
        HZTZUIVGVLUIVJVOUIUJALMTHITUKUDKVKVPRABCEFGFHILMOPQULADEFJKNOAFGHIPUMSU
        OUPVGVJVLVOEUQURVLUQUREFVFOUSZEUQUTVADVMVNEEVQVQVBVCVDVE $.

      cofidf2.j $e |- J = ( Hom ` E ) $.
      cofidf2.x $e |- ( ph -> X e. B ) $.
      cofidf2.y $e |- ( ph -> Y e. B ) $.
      $( If " ` F ` is a section of ` G ` " in a category of small categories
         (in a universe), then the morphism part of ` F ` is injective, and the
         morphism part of ` G ` is surjective in the image of ` F ` .
         (Contributed by Zhi Wang, 15-Nov-2025.) $)
      cofidf2 $p |- ( ph -> (
             ( X G Y ) : ( X H Y ) -1-1-> ( ( F ` X ) J ( F ` Y ) )
          /\ ( ( F ` X ) L ( F ` Y ) )
           : ( ( F ` X ) J ( F ` Y ) ) -onto-> ( X H Y ) ) ) $=
        ( co cop c1st cfv c2nd wf1 wfo wa cfunc wbr wcel df-br cofidf2a func2nd
        sylib oveqd func1st fveq1d oveq12d f1eq123d oveq123d foeq123d anbi12d
        eqidd mpbid ) ALMGUCZLEFUDZUEUFZUFZMVJUFZIUCZLMVIUGUFZUCZUHZVMVHVKVLJKU
        DZUGUFZUCZUIZUJVHLEUFZMEUFZIUCZLMFUCZUHZWCVHWAWBKUCZUIZUJABCDVIVQGHILMN
        OAEFCDUKUCZULVIWHUMPEFWHUNUQAJKDCUKUCZULVQWIUMQJKWIUNUQRSTUAUBUOAVPWEVT
        WGAVHVHVMWCVOWDAVNFLMACDEFPUPURAVHVFZAVKWAVLWBIALVJEACDEFPUSZUTZAMVJEWK
        UTZVAZVBAVMWCVHVHVSWFAVKWAVLWBVRKADCJKQUPWLWMVCWNWJVDVEVG $.
    $}

    cofidf1.c $e |- C = ( Base ` E ) $.
    $( If " ` <. F , G >. ` is a section of ` <. K , L >. ` " in a category of
       small categories (in a universe), then ` F ` is injective, and ` K ` is
       surjective.  (Contributed by Zhi Wang, 15-Nov-2025.) $)
    cofidf1 $p |- ( ph -> ( F : B -1-1-> C /\ K : C -onto-> B ) ) $=
      ( vx vy vz cfv wf1 wfo wf ccom cid cres wceq funcf1 cv cmpo cxp chom cmpt
      co eqid cofidval simpld fcof1 syl2anc fcofo syl3anc jca ) ABCFUAZCBIUBZAB
      CFUCZIFUDUEBUFUGZVCABCDEFGLPMUHZAVFQRBBQUIZFTRUIZFTJUNVHVIGUNUDUJSBBUKUES
      UIDULTZTUFUMUGAQRSBDEFGVJHIJKLMNOVJUOUPUQZBCIFURUSACBIUCVEVFVDACBEDIJPLNU
      HVGVKCBFIUTVAVB $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Opposite functors
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $c oppFunc $.

  $( Extend class notation with the operation generating opposite functors. $)
  coppf $a class oppFunc $.

  ${
    $d C f g $.  $d D f g $.  $d F f g $.  $d G f g $.
    $( Definition of the operation generating opposite functors.  Definition
       3.41 of [Adamek] p. 39.  The object part of the functor is unchanged
       while the morphism part is transposed due to reversed direction of
       arrows in the opposite category.  The opposite functor is a functor on
       opposite categories ( ~ oppfoppc ).  (Contributed by Zhi Wang,
       4-Nov-2025.)  Better reverse closure.  (Revised by Zhi Wang,
       13-Nov-2025.) $)
    df-oppf $a |- oppFunc = ( f e. _V , g e. _V |->
            if ( ( Rel g /\ Rel dom g ) , <. f , tpos g >. , (/) ) ) $.

    $( ` oppFunc ` is a function on ` ( _V X. _V ) ` .  (Contributed by Zhi
       Wang, 17-Nov-2025.) $)
    oppffn $p |- oppFunc Fn ( _V X. _V ) $=
      ( vf vg cvv cv wrel cdm wa ctpos cop c0 cif coppf df-oppf opex 0ex fnmpoi
      ifex ) ABCCBDZERFEGZADZRHZIZJKLABMSUBJTUANOQP $.

    $( The domain of ` oppFunc ` is a relation.  (Contributed by Zhi Wang,
       13-Nov-2025.) $)
    reldmoppf $p |- Rel dom oppFunc $=
      ( vf vg cvv cv wrel cdm wa ctpos cop c0 cif coppf df-oppf reldmmpo ) ABCC
      BDZEOFEGADOHIJKLABMN $.

    $( Value of the opposite functor.  (Contributed by Zhi Wang,
       13-Nov-2025.) $)
    oppfvalg $p |- ( ( F e. _V /\ G e. _V ) -> ( F oppFunc G )
            = if ( ( Rel G /\ Rel dom G ) , <. F , tpos G >. , (/) ) ) $=
      ( vf vg cvv cv wrel cdm wa ctpos cop c0 cif coppf wceq simpr releqd dmeqd
      anbi12d simpl tposeqd opeq12d ifbieq1d df-oppf opex 0ex ifex ovmpoa ) CDA
      BEEDFZGZUIHZGZIZCFZUIJZKZLMBGZBHZGZIZABJZKZLMNUNAOZUIBOZIZUMUTUPVBLVEUJUQ
      ULUSVEUIBVCVDPZQVEUKURVEUIBVFRQSVEUNAUOVAVCVDTVEUIBVFUAUBUCCDUDUTVBLAVAUE
      UFUGUH $.

    oppfrcl.1 $e |- ( ph -> G e. R ) $.
    oppfrcl.2 $e |- Rel R $.
    $( Lemma for ~ oppfrcl .  (Contributed by Zhi Wang, 14-Nov-2025.) $)
    oppfrcllem $p |- ( ph -> G =/= (/) ) $=
      ( wcel c0 wn wne wrel 0nelrel0 ax-mp nelne2 sylancl ) ACBFGBFHZCGIDBJOEBK
      LCGBMN $.

    oppfrcl.3 $e |- G = ( oppFunc ` F ) $.
    $( If an opposite functor of a class is a functor, then the original class
       must be an ordered pair.  (Contributed by Zhi Wang, 14-Nov-2025.) $)
    oppfrcl $p |- ( ph -> F e. ( _V X. _V ) ) $=
      ( coppf cdm cvv cxp c0 wne wcel oppfrcllem wn cfv ndmfv eqtrid necon1ai
      syl oppffn fndmi eleqtrdi ) ACHIZJJKZADLMCUENZABDEFOUGDLUGPDCHQLGCHRSTUAU
      FHUBUCUD $.

    ${
      oppfrcl2.4 $e |- ( ph -> F = <. A , B >. ) $.
      $( If an opposite functor of a class is a functor, then the two
         components of the original class must be sets.  (Contributed by Zhi
         Wang, 14-Nov-2025.) $)
      oppfrcl2 $p |- ( ph -> ( A e. _V /\ B e. _V ) ) $=
        ( cop c0 wne cvv wcel wa cxp wn oppfrcl eqeltrrd 0nelxp nelne2 necon1ai
        sylancl opprc syl ) ABCKZLMZBNOCNOPZAUGNNQZOLUJORUHAEUGUJJADEFGHISTNNUA
        UGLUJUBUDUIUGLBCUEUCUF $.

      $( If an opposite functor of a class is a functor, then the second
         component of the original class must be a relation whose domain is a
         relation as well.  (Contributed by Zhi Wang, 14-Nov-2025.) $)
      oppfrcl3 $p |- ( ph -> ( Rel B /\ Rel dom B ) ) $=
        ( wrel cdm wa cop c0 coppf cfv cvv wcel syl ctpos cif co fveq2d 3eqtr4g
        df-ov wceq oppfrcl2 oppfvalg eqtrd oppfrcllem eqnetrrd iffalse necon1ai
        wne ) ACKCLKMZBCUANZOUBZOUOUPAFUROAFBCPUCZURAEPQBCNZPQFUSAEUTPJUDIBCPUF
        UEABRSCRSMUSURUGABCDEFGHIJUHBCUITUJADFGHUKULUPUROUPUQOUMUNT $.

      $( Rewrite the opposite functor into its components ( ~ eqopi ).
         (Contributed by Zhi Wang, 14-Nov-2025.) $)
      oppf1st2nd $p |- ( ph -> ( G e. ( _V X. _V ) /\
                ( ( 1st ` G ) = A /\ ( 2nd ` G ) = tpos B ) ) ) $=
        ( cvv wcel c1st cfv wceq c2nd cop coppf fveq2d eqtrd cxp ctpos wrel cdm
        wa c0 cif co df-ov 3eqtr4g oppfrcl2 oppfvalg syl iftrued simpld tposexg
        oppfrcl3 simpl2im opelxpd eqeltrd op1stg syl2anc op2ndg jca32 ) AFKKUAZ
        LFMNZBOFPNZCUBZOAFBVHQZVEAFCUCCUDUCUEZVIUFUGZVIAFBCRUHZVKAERNBCQZRNFVLA
        EVMRJSIBCRUIUJABKLZCKLZUEVLVKOABCDEFGHIJUKZBCULUMTAVJVIUFABCDEFGHIJUQUN
        TZABVHKKAVNVOVPUOZAVNVOVHKLZVPCKUPURZUSUTAVFVIMNZBAFVIMVQSAVNVSWABOVRVT
        BVHKKVAVBTAVGVIPNZVHAFVIPVQSAVNVSWBVHOVRVTBVHKKVCVBTVD $.
    $}

    $( The double opposite functor is the original functor.  Remark 3.42 of
       [Adamek] p. 39.  (Contributed by Zhi Wang, 14-Nov-2025.) $)
    2oppf $p |- ( ph -> ( oppFunc ` G ) = F ) $=
      ( c1st cfv c2nd ctpos coppf wrel wa cop c0 cvv wcel wceq syl cdm cif fvex
      tposex oppfvalg mp2an df-ov cxp oppfrcl 1st2nd2 oppf1st2nd fveq2d eqtr4id
      co eqopi oppfrcl3 tpostpos2 opeq2d wn 0nelrel0 simpl2im reldmtpos reltpos
      sylibr jctil iftrued 3eqtr4d 3eqtr3a ) ACHIZCJIZKZLUNZVKMZVKUAMZNZVIVKKZO
      ZPUBZDLIZCVIQRVKQRVLVRSCHUCVJCJUCUDVIVKUEUFAVLVIVKOZLIVSVIVKLUGADVTLADQQU
      HZRDHIVISDJIVKSNNDVTSAVIVJBCDEFGACWARCVIVJOZSABCDEFGUICQQUJTZUKDVIVKQQUOT
      ULUMAVQWBVRCAVPVJVIAVJMZVJUAZMZNVPVJSAVIVJBCDEFGWCUPZVJUQTURAVOVQPAVNVMAP
      WERUSZVNAWDWFWHWGWEUTVAVJVBVDVJVCVEVFWCVGVH $.
  $}

  ${
    eloppf.g $e |- G = ( oppFunc ` F ) $.
    eloppf.x $e |- ( ph -> X e. G ) $.
    $( The pre-image of a non-empty opposite functor is non-empty; and the
       second component of the pre-image is a relation on triples.
       (Contributed by Zhi Wang, 18-Nov-2025.) $)
    eloppf $p |- ( ph -> ( F =/= (/) /\
                    ( Rel ( 2nd ` F ) /\ Rel dom ( 2nd ` F ) ) ) ) $=
      ( c0 wne c2nd cfv wrel cdm cvv wcel coppf eleqtrdi syl c1st cop wceq 3syl
      wa cxp elfvdm oppffn fndmi 0nelxp nelne2 sylancl ctpos cif 1st2nd2 fveq2d
      wn co df-ov fvex oppfvalg eqtr3i eqtrdi eleqtrd ne0d iffalse necon1ai jca
      mp2an ) ABGHZBIJZKVHLKUBZABMMUCZNZGVJNUNVGADBOJZNZVKADCVLFEPZVMBOLVJDBOUD
      VJOUEUFPZQMMUGBGVJUHUIAVIBRJZVHUJSZGUKZGHVIAVRDADVLVRVNAVLVPVHSZOJZVRABVS
      OAVMVKBVSTVNVOBMMULUAUMVPVHOUOZVTVRVPVHOUPVPMNVHMNWAVRTBRUQBIUQVPVHURVFUS
      UTVAVBVIVRGVIVQGVCVDQVE $.
  $}

  ${
    $d f g $.
    eloppf2.k $e |- ( F oppFunc G ) = K $.
    eloppf2.x $e |- ( ph -> X e. K ) $.
    $( Both components of a pre-image of a non-empty opposite functor exist;
       and the second component is a relation on triples.  (Contributed by Zhi
       Wang, 18-Nov-2025.) $)
    eloppf2 $p |- ( ph -> ( ( F e. _V /\ G e. _V )
                         /\ ( Rel G /\ Rel dom G ) ) ) $=
      ( vf vg cvv wcel wa wrel cdm coppf cv ctpos cop c0 syl co df-oppf elmpocl
      eleqtrrdi cif wne wceq oppfvalg eleqtrd ne0d iffalse necon1ai jca ) ABJKC
      JKLZCMCNMLZAEBCOUAZKUNAEDUPGFUDZHIJJIPZMURNMLHPURQRSUEBCOEHIUBUCTZAUOBCQR
      ZSUEZSUFUOAVAEAEUPVAUQAUNUPVAUGUSBCUHTUIUJUOVASUOUTSUKULTUM $.
  $}

  $( Lemma for ~ oppfval .  (Contributed by Zhi Wang, 13-Nov-2025.) $)
  oppfvallem $p |- ( F ( C Func D ) G -> ( Rel G /\ Rel dom G ) ) $=
    ( cfunc co wbr wrel cdm cbs cfv cxp wfn eqid funcfn2 fnrel syl relxp fndmd
    id releqd mpbiri jca ) CDABEFGZDHZDIZHZUDDAJKZUHLZMUEUDUHABCDUHNUDTOZUIDPQU
    DUGUIHUHUHRUDUFUIUDUIDUJSUAUBUC $.

  $( Value of the opposite functor.  (Contributed by Zhi Wang, 4-Nov-2025.) $)
  oppfval $p |- ( F ( C Func D ) G -> ( F oppFunc G ) = <. F , tpos G >. ) $=
    ( cfunc co wbr coppf wrel cdm wa ctpos cop cif wcel wceq relfunc brrelex12i
    c0 cvv oppfvalg syl oppfvallem iftrued eqtrd ) CDABEFZGZCDHFZDIDJIKZCDLMZSN
    ZUJUGCTODTOKUHUKPCDUFABQRCDUAUBUGUIUJSABCDUCUDUE $.

  $( Value of the opposite functor.  (Contributed by Zhi Wang, 13-Nov-2025.) $)
  oppfval2 $p |- ( F e. ( C Func D ) ->
            ( oppFunc ` F ) = <. ( 1st ` F ) , tpos ( 2nd ` F ) >. ) $=
    ( cfunc co wcel coppf cfv c1st c2nd ctpos cop wrel wceq relfunc 1st2nd mpan
    fveq2d df-ov eqtr4di wbr 1st2ndbr oppfval syl eqtrd ) CABDEZFZCGHZCIHZCJHZG
    EZUIUJKLZUGUHUIUJLZGHUKUGCUMGUFMZUGCUMNABOZCUFPQRUIUJGSTUGUIUJUFUAZUKULNUNU
    GUPUOCUFUBQABUIUJUCUDUE $.

  ${
    oppfval3.g $e |- ( ph -> F = <. G , K >. ) $.
    oppfval3.f $e |- ( ph -> F e. ( C Func D ) ) $.
    $( Value of the opposite functor.  (Contributed by Zhi Wang,
       19-Nov-2025.) $)
    oppfval3 $p |- ( ph -> ( oppFunc ` F ) = <. G , tpos K >. ) $=
      ( coppf cfv co ctpos cop fveq2d df-ov eqtr4di cfunc wbr wceq wcel oppfval
      eqeltrrd df-br sylibr syl eqtrd ) ADIJZEFIKZEFLMZAUGEFMZIJUHADUJIGNEFIOPA
      EFBCQKZRZUHUISAUJUKTULADUJUKGHUBEFUKUCUDBCEFUAUEUF $.
  $}

  ${
    oppf1.f $e |- ( ph -> F e. ( C Func D ) ) $.
    $( Value of the object part of the opposite functor.  (Contributed by Zhi
       Wang, 19-Nov-2025.) $)
    oppf1 $p |- ( ph -> ( 1st ` ( oppFunc ` F ) ) = ( 1st ` F ) ) $=
      ( cfunc co wcel coppf cfv c1st c2nd ctpos cop wceq oppfval2 tposex op1std
      fvex 3syl ) ADBCFGHDIJZDKJZDLJZMZNOUAKJUBOEBCDPUBUDUADKSUCDLSQRT $.

    $( Value of the morphism part of the opposite functor.  (Contributed by Zhi
       Wang, 19-Nov-2025.) $)
    oppf2 $p |- ( ph -> ( M ( 2nd ` ( oppFunc ` F ) ) N )
                      = ( N ( 2nd ` F ) M ) ) $=
      ( coppf cfv c2nd co ctpos cfunc wcel c1st cop wceq oppfval2 fvex tposex
      op2ndd 3syl oveqd ovtpos eqtrdi ) AEFDHIZJIZKEFDJIZLZKFEUHKAUGUIEFADBCMKN
      UFDOIZUIPQUGUIQGBCDRUJUIUFDOSUHDJSTUAUBUCEFUHUDUE $.
  $}

  ${
    oppfoppc.o $e |- O = ( oppCat ` C ) $.
    oppfoppc.p $e |- P = ( oppCat ` D ) $.
    ${
      oppfoppc.f $e |- ( ph -> F ( C Func D ) G ) $.
      $( The opposite functor is a functor on opposite categories.
         (Contributed by Zhi Wang, 4-Nov-2025.) $)
      oppfoppc $p |- ( ph -> ( F oppFunc G ) e. ( O Func P ) ) $=
        ( coppf co ctpos cop cfunc wbr wceq oppfval syl wcel funcoppc eqeltrd
        df-br sylib ) AEFKLZEFMZNZGDOLZAEFBCOLPUEUGQJBCEFRSAEUFUHPUGUHTABCDEFGH
        IJUAEUFUHUCUDUB $.
    $}

    oppfoppc2.f $e |- ( ph -> F e. ( C Func D ) ) $.
    $( The opposite functor is a functor on opposite categories.  (Contributed
       by Zhi Wang, 14-Nov-2025.) $)
    oppfoppc2 $p |- ( ph -> ( oppFunc ` F ) e. ( O Func P ) ) $=
      ( coppf cfv c1st c2nd co cfunc cop wrel wcel wceq relfunc sylancr eqtr4di
      1st2nd fveq2d df-ov func1st2nd oppfoppc eqeltrd ) AEJKZELKZEMKZJNZFDONAUI
      UJUKPZJKULAEUMJABCONZQEUNREUMSBCTIEUNUCUAUDUJUKJUEUBABCDUJUKFGHABCEIUFUGU
      H $.
  $}

  ${
    funcoppc2.o $e |- O = ( oppCat ` C ) $.
    funcoppc2.p $e |- P = ( oppCat ` D ) $.
    funcoppc2.c $e |- ( ph -> C e. V ) $.
    funcoppc2.d $e |- ( ph -> D e. W ) $.
    ${
      funcoppc2.f $e |- ( ph -> F ( O Func P ) G ) $.
      $( A functor on opposite categories yields a functor on the original
         categories.  (Contributed by Zhi Wang, 4-Nov-2025.) $)
      funcoppc2 $p |- ( ph -> F ( C Func D ) tpos G ) $=
        ( coppc cfv chomf wceq a1i ccomf ctpos cfunc co eqid funcoppc 2oppchomf
        wbr cvv 2oppccomf elexd fvexd funcpropd breqd mpbird ) AEFUAZBCUBUCZUGE
        UOGOPZDOPZUBUCZUGAGDUREFUQUQUDURUDNUEAUPUSEUOABUQCURUHBQPUQQPRABGJUFSBT
        PUQTPRABGJUISCQPURQPRACDKUFSCTPURTPRACDKUISABHLUJAGOUKACIMUJADOUKULUMUN
        $.
    $}

    ${
      funcoppc4.f $e |- ( ph -> ( F oppFunc G ) e. ( O Func P ) ) $.
      $( A functor on opposite categories yields a functor on the original
         categories.  (Contributed by Zhi Wang, 14-Nov-2025.) $)
      funcoppc4 $p |- ( ph -> F ( C Func D ) G ) $=
        ( coppf co cfv ctpos cfunc wceq c1st c2nd func1st2nd funcoppc2 cvv wcel
        cxp cop relfunc df-ov eqidd oppf1st2nd simprld simprrd tposeqd wrel cdm
        wa oppfrcl3 tpostpos2 syl eqtrd 3brtr3d ) AEFOPZUAQZVDUBQZRZEFBCSPABCDV
        EVFGHIJKLMAGDVDNUCUDAVDUEUEUGUFZVEETZVFFRZTZAEFGDSPZEFUHZVDNGDUIZEFOUJZ
        AVMUKZULZUMAVGVJRZFAVFVJAVHVIVKVQUNUOAFUPFUQUPURVRFTAEFVLVMVDNVNVOVPUSF
        UTVAVBVC $.
    $}

    ${
      funcoppc5.f $e |- ( ph -> ( oppFunc ` F ) e. ( O Func P ) ) $.
      $( A functor on opposite categories yields a functor on the original
         categories.  (Contributed by Zhi Wang, 14-Nov-2025.) $)
      funcoppc5 $p |- ( ph -> F e. ( C Func D ) ) $=
        ( c1st cfv cfunc co cvv wcel coppf c2nd cop cxp relfunc oppfrcl 1st2nd2
        wceq eqid syl wbr fveq2d df-ov eqtr4di eqeltrrd funcoppc4 df-br eqeltrd
        sylib ) AEENOZEUAOZUBZBCPQZAERRUCSEVAUGAFDPQZEETOZMFDUDVDUHUEERRUFUIZAU
        SUTVBUJVAVBSABCDUSUTFGHIJKLAVDUSUTTQZVCAVDVATOVFAEVATVEUKUSUTTULUMMUNUO
        USUTVBUPURUQ $.
    $}

    ${
      2oppffunc.f $e |- ( ph -> F e. ( O Func P ) ) $.
      $( The opposite functor of an opposite functor is a functor on the
         original categories.  (Contributed by Zhi Wang, 14-Nov-2025.)  The
         functor in opposite categories does not have to be an opposite
         functor.  (Revised by Zhi Wang, 17-Nov-2025.) $)
      2oppffunc $p |- ( ph -> ( oppFunc ` F ) e. ( C Func D ) ) $=
        ( coppf cfv c1st c2nd cfunc co wcel cop wceq oppfval2 syl wbr funcoppc2
        ctpos func1st2nd df-br sylib eqeltrd ) AENOZEPOZEQOZUGZUAZBCRSZAEFDRSTU
        LUPUBMFDEUCUDAUMUOUQUEUPUQTABCDUMUNFGHIJKLAFDEMUHUFUMUOUQUIUJUK $.
    $}

    funcoppc3.f $e |- ( ph -> F ( O Func P ) tpos G ) $.
    funcoppc3.g $e |- ( ph -> G Fn ( A X. B ) ) $.
    $( A functor on opposite categories yields a functor on the original
       categories.  (Contributed by Zhi Wang, 4-Nov-2025.) $)
    funcoppc3 $p |- ( ph -> F ( C Func D ) G ) $=
      ( ctpos cfunc wrel co funcoppc2 cdm wceq cxp wfn fnrel relxp fndmd releqd
      syl mpbiri tpostpos2 syl2anc breqtrd ) AGHRZRZHDESUAADEFGUPIJKLMNOPUBAHTZ
      HUCZTZUQHUDAHBCUEZUFURQVAHUGUKAUTVATBCUHAUSVAAVAHQUIUJULHUMUNUO $.
  $}

  ${
    $d C f g $.  $d D f g $.  $d O f g $.  $d P f g $.  $d V f g $.
    $d W f g $.  $d f g ph $.
    oppff1.o $e |- O = ( oppCat ` C ) $.
    oppff1.p $e |- P = ( oppCat ` D ) $.
    $( The operation generating opposite functors is injective.  (Contributed
       by Zhi Wang, 17-Nov-2025.) $)
    oppff1 $p |- ( oppFunc |` ( C Func D ) )
                            : ( C Func D ) -1-1-> ( O Func P ) $=
      ( vf vg cfunc co coppf cv cfv wceq wral wfn wcel cvv relfunc oppfoppc2 wf
      cres wf1 cxp wss oppffn wrel df-rel mpbi fnssres mp2an fvres eqeltrd rgen
      wi id ffnfv mpbir2an simpl fvresd simpr eqeq12d fveq2 eqid 2oppf imbitrid
      wa sylbid rgen2 dff13 ) ABIJZDCIJZKVKUBZUCVKVLVMUAZGLZVMMZHLZVMMZNZVOVQNZ
      UOZHVKOGVKOVNVMVKPZVPVLQZGVKOKRRUDZPVKWDUEZWBUFVKUGWEABSVKUHUIWDVKKUJUKWC
      GVKVOVKQZVPVOKMZVLVOVKKULWFABCVODEFWFUPTUMUNGVKVLVMUQURWAGHVKVKWFVQVKQZVG
      ZVSWGVQKMZNZVTWIVPWGVRWJWIVOVKKWFWHUSZUTWIVQVKKWFWHVAZUTVBWKWGKMZWJKMZNWI
      VTWGWJKVCWIWNVOWOVQWIVLVOWGWIABCVODEFWLTDCSZWGVDVEWIVLVQWJWIABCVQDEFWMTWP
      WJVDVEVBVFVHVIGHVKVLVMVJUR $.

    oppff1o.c $e |- ( ph -> C e. V ) $.
    oppff1o.d $e |- ( ph -> D e. W ) $.
    $( The operation generating opposite functors is bijective.  (Contributed
       by Zhi Wang, 17-Nov-2025.) $)
    oppff1o $p |- ( ph -> ( oppFunc |` ( C Func D ) )
                          : ( C Func D ) -1-1-onto-> ( O Func P ) ) $=
      ( vf vg cfunc co coppf cv cfv wceq wcel cres wf1 wfo wf1o oppff1 a1i wrex
      wf wral f1f syl wa fveq2 eqeq2d adantr simpr 2oppffunc relfunc eqid 2oppf
      fvresd eqtr2d rspcedvdw ralrimiva dffo3 sylanbrc df-f1o ) ABCNOZEDNOZPVHU
      AZUBZVHVIVJUCZVHVIVJUDVKABCDEHIUEUFZAVHVIVJUHZLQZMQZVJRZSZMVHUGZLVIUIVLAV
      KVNVMVHVIVJUJUKAVSLVIAVOVITZULZVRVOVOPRZVJRZSMWBVHVPWBSVQWCVOVPWBVJUMUNWA
      BCDVOEFGHIABFTVTJUOACGTVTKUOAVTUPUQZWAWCWBPRVOWAWBVHPWDVAWAVHVOWBWDBCURWB
      USUTVBVCVDMLVHVIVJVEVFVHVIVJVGVF $.
  $}

  ${
    $d C x y $.  $d D x y $.  $d E x y $.  $d F x y $.  $d G x y $.
    $d K x y $.  $d ph x y $.
    cofuoppf.k $e |- ( ph -> ( G o.func F ) = K ) $.
    cofuoppf.f $e |- ( ph -> F e. ( C Func D ) ) $.
    cofuoppf.g $e |- ( ph -> G e. ( D Func E ) ) $.
    $( Composition of opposite functors.  (Contributed by Zhi Wang,
       26-Nov-2025.) $)
    cofuoppf $p |- ( ph ->
        ( ( oppFunc ` G ) o.func ( oppFunc ` F ) ) = ( oppFunc ` K ) ) $=
      ( vy vx cfv ctpos cop ccofu co ccom eqid wcel c1st c2nd cbs cv cmpo coppf
      coppc oppcbas func1st2nd funcoppc cofuval2 cfunc oppfval2 oveq12d cofuval
      syl eqtr3d cofucl eqeltrrd oppfval3 wa ovtpos coeq12i eqcomi a1i mpoeq3ia
      wceq tposmpo opeq2i eqtrdi 3eqtr4d ) AFUAMZFUBMZNZOZEUAMZEUBMZNZOZPQVLVPR
      ZKLBUCMZWAKUDZVPMZLUDZVPMZVNQZWBWDVRQZRZUEZOZFUFMZEUFMZPQGUFMZAKLWABUGMZC
      UGMZDUGMZVPVRVLVNWABWNWNSZWASZUHABCWOVPVQWNWQWOSZABCEIUIUJACDWPVLVMWOWSWP
      SACDFJUIUJUKAWKVOWLVSPAFCDULQTWKVOVGJCDFUMUPAEBCULQTWLVSVGIBCEUMUPUNAWMVT
      LKWAWAWEWCVMQZWDWBVQQZRZUEZNZOWJABDGVTXCAFEPQZGVTXCOHALKWABCDEFWRIJUOUQAX
      EGBDULQHABCDEFIJURUSUTXDWIVTLKWAWAWHXCLKWAWAXBWHXBWHVGWDWATWBWATVAWHXBWFW
      TWGXAWCWEVMVBWBWDVQVBVCVDVEVFVHVIVJVK $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Full & faithful functors
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d F m n p $.  $d F p x y $.  $d G m n p $.  $d G p x y $.  $d H m n p $.
    $d H p x y $.  $d J q w z $.  $d K q w z $.  $d S m n w z $.  $d S q w z $.
    $d S w x y z $.  $d m n ph w z $.  $d p w x y z $.
    imasubc.s $e |- S = ( F " A ) $.
    imasubc.h $e |- H = ( Hom ` D ) $.
    imasubc.k $e |- K = ( x e. S , y e. S |-> U_ p e.
        ( ( `' F " { x } ) X. ( `' F " { y } ) ) ( ( G ` p ) " ( H ` p ) ) ) $.
    ${
      $d E m n p $.  $d ph w x y z $.
      imasubc.f $e |- ( ph -> F ( D Full E ) G ) $.
      ${
        imasubc.c $e |- C = ( Base ` E ) $.
        imasubc.j $e |- J = ( Homf ` E ) $.
        $( An image of a full functor is a full subcategory.  Remark 4.2(3) of
           [Adamek] p. 48.  (Contributed by Zhi Wang, 7-Nov-2025.) $)
        imasubc $p |- ( ph -> ( K Fn ( S X. S ) /\ S C_ C /\
                              ( J |` ( S X. S ) ) = K ) ) $=
          ( vq vz vw vm vn cxp wfn wss cres wceq cv csn cfv cvv cful co relfull
          wbr wcel brrelex1i syl imasubclem2 cima cbs eqid cfunc fullfunc ssbri
          funcf1 fimassd eqsstrid wral wa ccnv ciun chom c0 wne simprl eleqtrdi
          inisegn0a simprr jca xpnz sylib ffnd ad2antrr fniniseg biimpa syl2anc
          wfo simprd oveq12d simpld fullfo foeq3 foima ralrimivva fveq2 eqtr4di
          cop df-ov imaeq12d eqeq1d ralxp sylibr iuneqconst2 adantr imasubclem3
          sseldd homfval 3eqtr4rd wb homffn a1i xpss12 fvreseq1 syl21anc mpbird
          eqeq12d 3jca ) AMGGUFZUGZGEUHZLYBUIMUJZANBCBUKULCUKULNUKZYFKUMZIIJMUN
          UNGGAIJFHUOUPZURZIUNUSZRIJYHFHUQUTVAZYKQVBZAGIDVCZEOAFVDUMZEIDAYNEFHI
          JYNVEZSAYIIJFHVFUPZURRYHYPIJFHVGVHVAVIZVJVKZAYEUAUKZLUMZYSMUMZUJZUAYB
          VLZAUBUKZUCUKZLUPZUUDUUEMUPZUJZUCGVLUBGVLUUCAUUHUBUCGGAUUDGUSZUUEGUSZ
          VMZVMZNIVNZUUDULVCZUUMUUEULVCZUFZYFJUMZYGVCZVOZUUDUUEHVPUMZUPZUUGUUFU
          ULUUPVQVRZUURUVAUJZNUUPVLZUUSUVAUJUULUUNVQVRZUUOVQVRZVMUVBUULUVEUVFUU
          LUUDYMUSUVEUULUUDGYMAUUIUUJVSZOVTUUDDIWAVAUULUUEYMUSUVFUULUUEGYMAUUIU
          UJWBZOVTUUEDIWAVAWCUUNUUOWDWEUULUDUKZUEUKZJUPZUVIUVJKUPZVCZUVAUJZUEUU
          OVLUDUUNVLUVDUULUVNUDUEUUNUUOUULUVIUUNUSZUVJUUOUSZVMZVMZUVLUVAUVKWKZU
          VNUVRUVIIUMZUVJIUMZUUTUPZUVAUJZUVLUWBUVKWKZUVSUVRUVTUUDUWAUUEUUTUVRUV
          IYNUSZUVTUUDUJZUVRIYNUGZUVOUWEUWFVMZAUWGUUKUVQAYNEIYQWFWGZUULUVOUVPVS
          UWGUVOUWHYNUUDUVIIWHWIWJZWLUVRUVJYNUSZUWAUUEUJZUVRUWGUVPUWKUWLVMZUWIU
          ULUVOUVPWBUWGUVPUWMYNUUEUVJIWHWIWJZWLWMUVRYNFHIJKUUTUVIUVJYOUUTVEZPAY
          IUUKUVQRWGUVRUWEUWFUWJWNUVRUWKUWLUWNWNWOUWCUWDUVSUWBUVAUVLUVKWPWIWJUV
          LUVAUVKWQVAWRUVCUVNNUDUEUUNUUOYFUVIUVJXAZUJZUURUVMUVAUWQUUQUVKYGUVLUW
          QUUQUWPJUMUVKYFUWPJWSUVIUVJJXBWTUWQYGUWPKUMUVLYFUWPKWSUVIUVJKXBWTXCXD
          XEXFNUUPUURUVAXGWJUULBCNGGYFYGIIJMUNUNUUDUUEAYJUUKYKXHZUWRUVGUVHQXIUU
          LEHLUUTUUDUUETSUWOUULGEUUDAYDUUKYRXHZUVGXJUULGEUUEUWSUVHXJXKXLWRUUBUU
          HUAUBUCGGYSUUDUUEXAZUJZYTUUFUUAUUGUXAYTUWTLUMUUFYSUWTLWSUUDUUELXBWTUX
          AUUAUWTMUMUUGYSUWTMWSUUDUUEMXBWTXTXEXFALEEUFZUGZYCYBUXBUHZYEUUCXMUXCA
          EHLTSXNXOYLAYDYDUXDYRYRGEGEXPWJUAUXBYBLMXQXRXSYA $.
      $}

      $( An image of a full functor is a (full) subcategory.  Remark 4.2(3) of
         [Adamek] p. 48.  (Contributed by Zhi Wang, 7-Nov-2025.) $)
      imasubc2 $p |- ( ph -> K e. ( Subcat ` E ) ) $=
        ( cfv eqid co wbr chomf cxp cres csubc wfn cbs wceq imasubc simp3d cful
        wss cfunc fullfunc ssbri syl funcrcl3 simp2d fullsubc eqeltrrd ) AGUAQZ
        FFUBZUCZKGUDQAKVAUEZFGUFQZUKZVBKUGZABCDVDEFGHIJUTKLMNOPVDRZUTRZUHZUIAVD
        GFUTVGVHAEGHIAHIEGUJSZTHIEGULSZTPVJVKHIEGUMUNUOUPAVCVEVFVIUQURUS $.
    $}

    imassc.f $e |- ( ph -> F ( D Func E ) G ) $.
    ${
      $d E m n p $.  $d ph w x y z $.
      imassc.j $e |- J = ( Homf ` E ) $.
      $( An image of a functor satisfies the subcategory subset relation.
         (Contributed by Zhi Wang, 7-Nov-2025.) $)
      imassc $p |- ( ph -> K C_cat J ) $=
        ( cfv cv vz vw vm vn cssc wbr cbs wss co wral cima eqid funcf1 eqsstrid
        fimassd wcel ccnv csn cxp ciun chom cfunc ad2antrr wceq wfn ffnd simprl
        fniniseg biimpa syl2anc simpld simprr funcf2 oveq12d sseqtrd ralrimivva
        simprd iunss cop fveq2 df-ov eqtr4di imaeq12d sseq1d ralxp bitri sylibr
        cvv relfunc brrelex1i syl adantr imasubclem3 sseldd homfval imasubclem2
        wa 3sstr4d homffn a1i fvexd isssc mpbir2and ) ALKUEUFFGUGSZUHZUATZUBTZL
        UIZXFXGKUIZUHZUBFUJUAFUJAFHDUKXDNAEUGSZXDHDAXKXDEGHIXKULZXDULZQUMUOUNZA
        XJUAUBFFAXFFUPZXGFUPZWQZWQZMHUQZXFURUKZXSXGURUKZUSZMTZISZYCJSZUKZUTZXFX
        GGVASZUIZXHXIXRUCTZUDTZIUIZYJYKJUIZUKZYIUHZUDYAUJUCXTUJZYGYIUHZXRYOUCUD
        XTYAXRYJXTUPZYKYAUPZWQZWQZYNYJHSZYKHSZYHUIZYIUUAYMUUDYLYMUUAXKEGHIJYHYJ
        YKXLOYHULZAHIEGVBUIZUFZXQYTQVCZUUAYJXKUPZUUBXFVDZUUAHXKVEZYRUUIUUJWQZUU
        AXKXDHUUAXKXDEGHIXLXMUUHUMVFZXRYRYSVGUUKYRUULXKXFYJHVHVIVJZVKUUAYKXKUPZ
        UUCXGVDZUUAUUKYSUUOUUPWQZUUMXRYRYSVLUUKYSUUQXKXGYKHVHVIVJZVKVMUOUUAUUBX
        FUUCXGYHUUAUUIUUJUUNVQUUAUUOUUPUURVQVNVOVPYQYFYIUHZMYBUJYPMYBYFYIVRUUSY
        OMUCUDXTYAYCYJYKVSZVDZYFYNYIUVAYDYLYEYMUVAYDUUTISYLYCUUTIVTYJYKIWAWBUVA
        YEUUTJSYMYCUUTJVTYJYKJWAWBWCWDWEWFWGXRBCMFFYCYEHHILWHWHXFXGAHWHUPZXQAUU
        GUVBQHIUUFEGWIWJWKZWLZUVDAXOXPVGZAXOXPVLZPWMXRXDGKYHXFXGRXMUUEXRFXDXFAX
        EXQXNWLZUVEWNXRFXDXGUVGUVFWNWOWRVPAUAUBFXDLKWHAMBCBTURCTURYCYEHHILWHWHF
        FUVCUVCPWPKXDXDUSVEAXDGKRXMWSWTAGUGXAXBXC $.
    $}

    ${
      $d I m p $.  $d X m p $.  $d X p x y $.
      imaid.i $e |- I = ( Id ` E ) $.
      imaid.x $e |- ( ph -> X e. S ) $.
      $( An image of a functor preserves the identity morphism.  (Contributed
         by Zhi Wang, 7-Nov-2025.) $)
      imaid $p |- ( ph -> ( I ` X ) e. ( X K X ) ) $=
        ( vm cfv ccnv csn cima cxp cv ciun wcel wrex wne wex eleqtrdi inisegn0a
        co c0 syl n0 sylib cop wceq fveq2 df-ov eqtr4di imaeq12d eleq2d opelxpd
        wa simpr ccid cbs eqid cfunc wbr adantr wfn funcf1 ffnd fniniseg biimpa
        wb simpld funcid simprd fveq2d eqtrd funcrcl2 catidcl funcf2 funfvima2d
        chom mpdan eqeltrrd rspcedvdw exlimddv eliund cvv brrelex1i imasubclem3
        relfunc eleqtrrd ) AMKUBZNHUCMUDUEZXCUFZNUGZIUBZXEJUBZUEZUHMMLUOANXBXDX
        HAUAUGZXCUIZXBXHUIZNXDUJUAAXCUPUKZXJUAULAMHDUEZUIXLAMFXMTOUMMDHUNUQUAXC
        URUSAXJVHZXKXBXIXIIUOZXIXIJUOZUEZUINXIXIUTZXDXEXRVAZXHXQXBXSXFXOXGXPXSX
        FXRIUBXOXEXRIVBXIXIIVCVDXSXGXRJUBXPXEXRJVBXIXIJVCVDVEVFXNXIXIXCXCAXJVIZ
        XTVGXNXIEVJUBZUBZXOUBZXBXQXNYCXIHUBZKUBXBXNEVKUBZEYAGHIKXIYEVLZYAVLZSAH
        IEGVMUOZVNZXJRVOZXNXIYEUIZYDMVAZAXJYKYLVHZAHYEVPXJYMWAAYEGVKUBZHAYEYNEG
        HIYFYNVLRVQVRYEMXIHVSUQVTZWBZWCXNYDMKXNYKYLYOWDWEWFXNYBXPUIYCXQUIXNYEEY
        AJXIYFPYGXNEGHIYJWGYPWHXNXPYDYDGWKUBZUOXOYBXNYEEGHIJYQXIXIYFPYQVLYJYPYP
        WIWJWLWMWNWOWPABCNFFXEXGHHILWQWQMMAYIHWQUIRHIYHEGWTWRUQZYRTTQWSXA $.
    $}

    ${
      $d .xb m n $.  $d A m n $.  $d B m n $.  $d C m n $.  $d D m n $.
      $d E m n $.  $d F m n $.  $d G m n $.  $d H m n $.  $d K m n $.
      $d M m n $.  $d N m n $.  $d S m n $.  $d X p m n x y $.
      $d Y p m n x y $.  $d Z p m n x y $.  $d m n ph $.
      imaf1co.b $e |- B = ( Base ` D ) $.
      imaf1co.c $e |- C = ( Base ` E ) $.
      imaf1co.o $e |- .xb = ( comp ` E ) $.
      imaf1co.f $e |- ( ph -> F : B -1-1-> C ) $.
      imaf1co.x $e |- ( ph -> X e. S ) $.
      imaf1co.y $e |- ( ph -> Y e. S ) $.
      imaf1co.z $e |- ( ph -> Z e. S ) $.
      imaf1co.m $e |- ( ph -> M e. ( X K Y ) ) $.
      imaf1co.n $e |- ( ph -> N e. ( Y K Z ) ) $.
      $( An image of a functor whose object part is injective preserves the
         composition.  (Contributed by Zhi Wang, 7-Nov-2025.) $)
      imaf1co $p |- ( ph -> ( N ( <. X , Y >. .xb Z ) M ) e. ( X K Z ) ) $=
        ( vm vn cv ccnv cfv co wceq cop wcel wa cima eqid ccat funcrcl2 ad4antr
        cco imaf1homlem simp3d simp-4r simplr catcocl chom wf funcf2 funfvima2d
        csn mpdan cfunc wbr funcco simp2d opeq12d oveq12d simpr oveq123d eqtr2d
        simpllr cvv relfunc brrelex1i syl imaf1hom 3eltr4d wrex eleqtrd fvelima
        wfun ffund syl2anc ad2antrr r19.29a ) AUNUPZQKUQZURZRXFURZLUSZURZOUTZPO
        QRVAZSIUSZUSZQSNUSZVBZUNXGXHMUSZAXEXQVBZVCZXKVCZUOUPZXHSXFURZLUSZURZPUT
        ZXPUOXHYBMUSZXTYAYFVBZVCZYEVCZYAXEXGXHVAYBGVIURZUSUSZXGYBLUSZURZYLXGYBM
        USZVDZXNXOYIYKYNVBYMYOVBYIEGYJXEYAMXGXHYBUEUBYJVEZAGVFVBXRXKYGYEAGJKLUD
        VGVHAXGEVBZXRXKYGYEAXGVSXFQVSVDUTZXGKURZQUTZYQADEFHKQUAUHUIVJZVKZVHZAXH
        EVBZXRXKYGYEAXHVSXFRVSVDUTZXHKURZRUTZUUDADEFHKRUAUHUJVJZVKZVHZAYBEVBZXR
        XKYGYEAYBVSXFSVSVDUTZYBKURZSUTZUUKADEFHKSUAUHUKVJZVKZVHZAXRXKYGYEVLZXTY
        GYEVMZVNYIYNYSUUMJVOURZUSZYLYKAYNUVAYLVPXRXKYGYEAEGJKLMUUTXGYBUEUBUUTVE
        ZUDUUBUUPVQVHVRVTYIYMYDXJYSUUFVAZUUMIUSZUSXNYIEGYJJKLMXEYAIXGXHYBUEUBYP
        UGAKLGJWAUSZWBZXRXKYGYEUDVHUUCUUJUUQUURUUSWCYIYDPXJOUVDXMYIUVCXLUUMSIYI
        YSQUUFRAYTXRXKYGYEAYRYTYQUUAWDVHAUUGXRXKYGYEAUUEUUGUUDUUHWDVHWEAUUNXRXK
        YGYEAUULUUNUUKUUOWDVHWFYHYEWGXSXKYGYEWJWHWIAXOYOUTXRXKYGYEABCDEFHKLMNWK
        QSTUAUHUIUKAUVFKWKVBUDKLUVEGJWLWMWNZUCWOVHWPAYEUOYFWQZXRXKAYCWTPYCYFVDZ
        VBUVHAYFUUFUUMUUTUSYCAEGJKLMUUTXHYBUEUBUVBUDUUIUUPVQXAAPRSNUSUVIUMABCDE
        FHKLMNWKRSTUAUHUJUKUVGUCWOWRUOPYFYCWSXBXCXDAXIWTOXIXQVDZVBXKUNXQWQAXQYS
        UUFUUTUSXIAEGJKLMUUTXGXHUEUBUVBUDUUBUUIVQXAAOQRNUSUVJULABCDEFHKLMNWKQRT
        UAUHUIUJUVGUCWOWRUNOXQXIWSXBXD $.
    $}

    $d E a b c f g $.  $d E a b c p $.  $d F p x y $.  $d G p x y $.
    $d H p x y $.  $d K a b c f g $.  $d S a b c f g $.  $d S a b c x y $.
    $d a b c f g ph $.  $d ph x y $.
    imasubc3.f $e |- ( ph -> Fun `' F ) $.
    $( An image of a functor injective on objects is a subcategory.  Remark
       4.2(3) of [Adamek] p. 48.  (Contributed by Zhi Wang, 7-Nov-2025.) $)
    imasubc3 $p |- ( ph -> K e. ( Subcat ` E ) ) $=
      ( cfv wcel cv va vg vf vb vc csubc chomf cssc wbr ccid co cop cco wral wa
      eqid imassc cfunc adantr simpr imaid cbs ad3antrrr wf1 wf ccnv wfun df-f1
      funcf1 simpllr simplrl simplrr simprl simprr imaf1co ralrimivva ralrimiva
      sylanbrc jca funcrcl3 csn cvv relfunc brrelex1i syl imasubclem2 mpbir2and
      issubc2 ) AKGUFRSKGUGRZUHUIUATZGUJRZRWJWJKUKSZUBTZUCTZWJUDTZULUETZGUMRZUK
      UKWJWPKUKSZUBWOWPKUKZUNUCWJWOKUKZUNZUEFUNUDFUNZUOZUAFUNABCDEFGHIJWIKLMNOP
      WIUPZUQAXCUAFAWJFSZUOZWLXBXFBCDEFGHIJWKKWJLMNOAHIEGURUKZUIZXEPUSWKUPZAXEU
      TVAXFXAUDUEFFXFWOFSZWPFSZUOZUOZWRUCUBWTWSXMWNWTSZWMWSSZUOZUOBCDEVBRZGVBRZ
      EFWQGHIJKWNWMWJWOWPLMNOAXHXEXLXPPVCXQUPZXRUPZWQUPZAXQXRHVDZXEXLXPAXQXRHVE
      HVFVGYBAXQXREGHIXSXTPVIQXQXRHVHVRVCAXEXLXPVJXFXJXKXPVKXFXJXKXPVLXMXNXOVMX
      MXNXOVNVOVPVPVSVQAUAUDUEGFWQWKUCUBWIKXDXIYAAEGHIPVTALBCBTWACTWALTZYCJRHHI
      KWBWBFFAXHHWBSPHIXGEGWCWDWEZYDOWFWHWG $.
  $}

  ${
    $d A f g x y z $.  $d B f g x y z $.  $d f g ph x y z $.
    fthcomf.1 $e |- ( ph -> F ( A Faith C ) G ) $.
    fthcomf.2 $e |- ( ph -> F ( B Func D ) G ) $.
    fthcomf.3 $e |- ( ( ( ph /\
             ( x e. ( Base ` A ) /\ y e. ( Base ` A ) /\ z e. ( Base ` A ) ) )
          /\ ( f e. ( x ( Hom ` A ) y ) /\ g e. ( y ( Hom ` A ) z ) ) )
        -> ( ( ( y G z ) ` g )
             ( <. ( F ` x ) , ( F ` y ) >. ( comp ` C ) ( F ` z ) )
             ( ( x G y ) ` f ) )
         = ( ( ( y G z ) ` g )
             ( <. ( F ` x ) , ( F ` y ) >. ( comp ` D ) ( F ` z ) )
             ( ( x G y ) ` f ) ) ) $.
    $( Source categories of a faithful functor have the same base, hom-sets and
       composition operation if the composition is compatible in images of the
       functor.  (Contributed by Zhi Wang, 10-Nov-2025.) $)
    fthcomf $p |- ( ph -> ( comf ` A ) = ( comf ` B ) ) $=
      ( cfv co wcel eqid ad2antrr ccomf wceq cop cco chom wral cbs w3a cfth wbr
      cv cfunc fthfunc ssbri syl simplr1 simplr2 simplr3 simprl simprr funchomf
      wa funcco homfeqbas eleqtrd chomf homfeqval 3eqtr4d ccat funcrcl2 catcocl
      eleqtrrd fthi mpbid ralrimivva ralrimivvva eqidd comfeq mpbird ) AEUAPFUA
      PUBJUKZIUKZBUKZCUKZUCZDUKZEUDPZQQZVTWAWDWEFUDPZQQZUBZJWCWEEUEPZQZUFIWBWCW
      KQZUFZDEUGPZUFCWOUFBWOUFAWNBCDWOWOWOAWBWORZWCWORZWEWORZUHZVBZWJIJWMWLWTWA
      WMRZVTWLRZVBZVBZWGWBWELQZPZWIXEPZUBWJXDVTWCWELQPZWAWBWCLQPZWBKPWCKPUCZWEK
      PZGUDPZQQXHXIXJXKHUDPZQQXFXGOXDWOEWFGKLWKWAVTXLWBWCWEWOSZWKSZWFSZXLSXDKLE
      GUIQZUJZKLEGULQZUJZAXRWSXCMTZXQXSKLEGUMUNZUOWPWQWRAXCUPZWPWQWRAXCUQZWPWQW
      RAXCURZWTXAXBUSZWTXAXBUTZVCXDFUGPZFWHHKLFUEPZWAVTXMWBWCWEYHSZYISZWHSZXMSA
      KLFHULQUJWSXCNTXDWBWOYHYCAWOYHUBWSXCAEFAEFGHKLAXRXTMYBUOZNVAZVDZTZVEZXDWC
      WOYHYDYPVEZXDWEWOYHYEYPVEZXDWAWMWBWCYIQYFXDWOEFWKYIWBWCXNXOYKAEVFPFVFPUBW
      SXCYNTZYCYDVGVEZXDVTWLWCWEYIQYGXDWOEFWKYIWCWEXNXOYKYTYDYEVGVEZVCVHXDWOEGW
      GWIKLWKGUEPZWBWEXNXOUUCSYAYCYEXDWOEWFWAVTWKWBWCWEXNXOXPAEVIRWSXCAEGKLYMVJ
      TYCYDYEYFYGVKXDWIWBWEYIQWBWEWKQXDYHFWHWAVTYIWBWCWEYJYKYLAFVIRWSXCAFHKLNVJ
      TYQYRYSUUAUUBVKXDWOEFWKYIWBWEXNXOYKYTYCYEVGVLVMVNVOVPABCDWOEFWHWFIJWKXPYL
      XOAWOVQYOYNVRVS $.
  $}

  ${
    $d B p x y $.  $d C p x y $.  $d D p x y $.  $d E p x y $.  $d H p x y $.
    $d I p x y $.  $d J p x y $.
    idfth.i $e |- I = ( idFunc ` C ) $.
    $( The inclusion functor is a faithful functor.  (Contributed by Zhi Wang,
       10-Nov-2025.) $)
    idfth $p |- ( I e. ( D Func E ) -> I e. ( D Faith E ) ) $=
      ( vx vy cfunc co wcel c1st cfv c2nd wbr cv ccnv wfun wral wa eqidd 1st2nd
      cop cfth wrel wceq relfunc mpan cbs id func1st2nd cid chom cres wf1o f1oi
      dff1o3 mpbi simpri simprl simprr idfu2nda cnveqd funeqd mpbiri ralrimivva
      wfo simpl eqid isfth sylanbrc df-br sylib eqeltrd ) DBCHIZJZDDKLZDMLZUBZB
      CUCIZVNUDVODVRUEBCUFDVNUAUGVOVPVQVSNZVRVSJVOVPVQVNNFOZGOZVQIZPZQZGBUHLZRF
      WFRVTVOBCDVOUIUJVOWEFGWFWFVOWAWFJZWBWFJZSZSZWEUKWAWBBULLIZUMZPZQZWKWKWLVF
      ZWNWKWKWLUNWOWNSWKUOWKWKWLUPUQURWJWDWMWJWCWLWJWFABCWKDWAWBEVOWIVGWJWFTVOW
      GWHUSVOWGWHUTWJWKTVAVBVCVDVEFGWFBCVPVQWFVHVIVJVPVQVSVKVLVM $.

    $( The inclusion functor is an embedding.  Remark 4.4(1) in [Adamek] p. 49.
       (Contributed by Zhi Wang, 16-Nov-2025.) $)
    idemb $p |- ( I e. ( D Func E ) -> ( I e. ( D Faith E )
                                      /\ Fun `' ( 1st ` I ) ) ) $=
      ( cfunc wcel cfth c1st cfv ccnv wfun idfth cbs ccat wf1o wfn cidfu eleq1i
      co idfurcl sylbi eqid idfu1stf1o dff1o4 simprbi 3syl fnfund jca ) DBCFTZG
      ZDBCHTGDIJZKZLABCDEMUKANJZUMUKAOGZUNUNULPZUMUNQZUKARJZUJGUODURUJESABCUAUB
      UNADEUNUCUDUPULUNQUQUNUNULUEUFUGUHUI $.

    idsubc.h $e |- H = ( Homf ` D ) $.
    $( The source category of an inclusion functor is a subcategory of the
       target category.  See also Remark 4.4 in [Adamek] p. 49.  (Contributed
       by Zhi Wang, 10-Nov-2025.) $)
    idsubc $p |- ( I e. ( D Func E ) -> H e. ( Subcat ` E ) ) $=
      ( vx vy vp cfunc co wcel cfv cima ccnv cv csn eqid wfun c1st cbs cxp c2nd
      chom ciun cmpo csubc id imaidfu2lem imaidfu2 func1st2nd cid cres wfo wf1o
      wa f1oi dff1o3 mpbi simpri idfu1sta cnveqd funeqd mpbiri imasubc3 eqeltrd
      eqidd ) EBCKLMZDHIEUANZBUBNZOZVLJVJPZHQROVMIQROUCJQZEUDNZNVNBUENZNOUFUGZC
      UHNVIHIABVLCVPEDVQJFVIUIZVPSZGVQSZVIABCEFVRUJUKVIHIVKBVLCVJVOVPVQJVLSVSVT
      VIBCEVRULVIVMTUMVKUNZPZTZVKVKWAUOZWCVKVKWAUPWDWCUQVKURVKVKWAUSUTVAVIVMWBV
      IVJWAVIVKABCEFVRVIVKVHVBVCVDVEVFVG $.

    idfullsubc.j $e |- J = ( Homf ` E ) $.
    idfullsubc.b $e |- B = ( Base ` D ) $.
    idfullsubc.c $e |- C = ( Base ` E ) $.
    $( The source category of an inclusion functor is a full subcategory of the
       target category if the inclusion functor is full.  Remark 4.4(2) in
       [Adamek] p. 49.  See also ~ ressffth .  (Contributed by Zhi Wang,
       11-Nov-2025.) $)
    idfullsubc $p |- ( I e. ( D Full E ) ->
            ( B C_ C /\ ( J |` ( B X. B ) ) = H ) ) $=
      ( vx vy vp cxp cfv cima cv eqid cful co wcel wss cres wceq c1st cbs cfunc
      fullfunc imaidfu2lem eqtr4id ccnv csn c2nd chom ciun cmpo wfn wbr relfull
      wrel 1st2ndbr mpan imasubc simp2d eqsstrd simp3d sqxpeqd reseq2d imaidfu2
      sseli 3eqtr4d jca ) FCDUAUBZUCZABUDGAAPZUEZEUFVPAFUGQZCUHQZRZBVPAVTWAKVPB
      CDFHVOCDUIUBFCDUJVLZUKZULZVPMNWAWAOVSUMZMSUNRWENSUNRPOSZFUOQZQWFCUPQZQRUQ
      URZWAWAPZUSZWABUDZGWJUEZWIUFZVPMNVTBCWADVSWGWHGWIOWATWHTZWITZVOVBVPVSWGVO
      UTCDVAFVOVCVDLJVEZVFVGVPWMWIVREVPWKWLWNWQVHVPVQWJGVPAWAWDVIVJVPMNBCWADWHF
      EWIOHWBWOIWPWCVKVMVN $.
  $}

  ${
    $d D x y $.  $d E x y $.  $d F x y $.  $d G x y $.  $d ph x y $.
    cofidfth.i $e |- I = ( idFunc ` D ) $.
    cofidfth.f $e |- ( ph -> F ( D Func E ) G ) $.
    cofidfth.k $e |- ( ph -> K ( E Func D ) L ) $.
    cofidfth.o $e |- ( ph -> ( <. K , L >. o.func <. F , G >. ) = I ) $.
    $( If " ` F ` is a section of ` G ` " in a category of small categories (in
       a universe), then ` F ` is faithful.  Combined with ~ cofidf1 , this
       theorem proves that ` F ` is an embedding (a faithful functor injective
       on objects, remark 3.28(1) of [Adamek] p. 34).  (Contributed by Zhi
       Wang, 15-Nov-2025.) $)
    cofidfth $p |- ( ph -> F ( D Faith E ) G ) $=
      ( vx vy cfunc co wbr cfv eqid adantr cv chom wf1 cbs wral cfth wa wfo cop
      wcel ccofu wceq simprl simprr cofidf2 simpld ralrimivva isfth2 sylanbrc )
      ADEBCOPQZMUAZNUAZBUBRZPZVADRZVBDRZCUBRZPZVAVBEPUCZNBUDRZUEMVJUEDEBCUFPQJA
      VIMNVJVJAVAVJUJZVBVJUJZUGZUGZVIVHVDVEVFHPUHVNVJBCDEVCFVGGHVAVBIVJSZAUTVMJ
      TAGHCBOPQVMKTAGHUIDEUIUKPFULVMLTVCSZVGSZAVKVLUMAVKVLUNUOUPUQMNVJBCDEVCVGV
      OVPVQURUS $.
  $}

  ${
    fulloppf.o $e |- O = ( oppCat ` C ) $.
    fulloppf.p $e |- P = ( oppCat ` D ) $.
    ${
      fulloppf.f $e |- ( ph -> F e. ( C Full D ) ) $.
      $( The opposite functor of a full functor is also full.  Proposition
         3.43(d) in [Adamek] p. 39.  (Contributed by Zhi Wang, 26-Nov-2025.) $)
      fulloppf $p |- ( ph -> ( oppFunc ` F ) e. ( O Full P ) ) $=
        ( coppf cfv c1st c2nd ctpos cop cful co wcel cfunc wbr fullfunc relfull
        wceq sseli oppfval2 3syl 1st2ndbr sylancr fulloppc df-br sylib eqeltrd
        wrel ) AEJKZELKZEMKZNZOZFDPQZAEBCPQZRZEBCSQZRUNURUCIUTVBEBCUAUDBCEUEUFA
        UOUQUSTURUSRABCDUOUPFGHAUTUMVAUOUPUTTBCUBIEUTUGUHUIUOUQUSUJUKUL $.
    $}

    ${
      fthoppf.f $e |- ( ph -> F e. ( C Faith D ) ) $.
      $( The opposite functor of a faithful functor is also faithful.
         Proposition 3.43(c) in [Adamek] p. 39.  (Contributed by Zhi Wang,
         26-Nov-2025.) $)
      fthoppf $p |- ( ph -> ( oppFunc ` F ) e. ( O Faith P ) ) $=
        ( coppf cfv c1st c2nd ctpos cop cfth co wcel cfunc wbr fthfunc oppfval2
        wceq sseli 3syl relfth 1st2ndbr sylancr fthoppc df-br sylib eqeltrd
        wrel ) AEJKZELKZEMKZNZOZFDPQZAEBCPQZRZEBCSQZRUNURUCIUTVBEBCUAUDBCEUBUEA
        UOUQUSTURUSRABCDUOUPFGHAUTUMVAUOUPUTTBCUFIEUTUGUHUIUOUQUSUJUKUL $.
    $}

    ${
      ffthoppf.f $e |- ( ph -> F e. ( ( C Full D ) i^i ( C Faith D ) ) ) $.
      $( The opposite functor of a fully faithful functor is also full and
         faithful.  (Contributed by Zhi Wang, 26-Nov-2025.) $)
      ffthoppf $p |- ( ph ->
              ( oppFunc ` F ) e. ( ( O Full P ) i^i ( O Faith P ) ) ) $=
        ( cful co cfth coppf cfv elin1d fulloppf elin2d fthoppf elind ) AFDJKFD
        LKEMNABCDEFGHABCJKZBCLKZEIOPABCDEFGHATUAEIQRS $.
    $}
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Universal property
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d B m y $.  $d F k m $.  $d F l m $.  $d F k n y $.  $d G k m $.
    $d G l m $.  $d G k n y $.  $d H k m $.  $d H l m $.  $d H k n y $.
    $d J m n y $.  $d M k m $.  $d M l m $.  $d M k n y $.  $d N k m $.
    $d N l m $.  $d N k m n $.  $d O k m $.  $d O l m $.  $d O k n y $.
    $d X k m $.  $d X l m $.  $d X k n y $.  $d Y k m $.  $d Y l m $.
    $d Y k n y $.  $d Z k m $.  $d Z l m $.  $d Z k n y $.
    upciclem1.1 $e |- ( ph -> A. y e. B A. n e. ( Z J ( F ` y ) )
           E! k e. ( X H y )
           n = ( ( ( X G y ) ` k ) ( <. Z , ( F ` X ) >. O ( F ` y ) ) M ) ) $.
    upciclem1.y $e |- ( ph -> Y e. B ) $.
    upciclem1.n $e |- ( ph -> N e. ( Z J ( F ` Y ) ) ) $.
    $( Lemma for ~ upcic , ~ upeu , and ~ upeu2 .  (Contributed by Zhi Wang,
       16-Sep-2025.)  (Proof shortened by Zhi Wang, 5-Nov-2025.) $)
    upciclem1 $p |- ( ph -> E! l e. ( X H Y )
                            N = ( ( ( X G Y ) ` l )
                            ( <. Z , ( F ` X ) >. O ( F ` Y ) ) M ) ) $=
      ( co vm cv cfv cop wceq wreu eqeq1 reubidv wral fveq2 oveq2d oveq2 fveq1d
      eqidd oveq123d eqeq2d reueqbidv raleqbidv rspcdva oveq1d cbvreuvw bitri
      sylib ) AKDUBZMNGTZUCZJOMFUCUDZNFUCZLTZTZUEZDMNHTZUFZKPUBZVEUCZJVITZUEZPV
      LUFZAEUBZVJUEZDVLUFZVMEOVHITZKVSKUEVTVKDVLVSKVJUGUHAVSVDMBUBZGTZUCZJVGWCF
      UCZLTZTZUEZDMWCHTZUFZEOWFITZUIWAEWBUIBCNWCNUEZWKWAEWLWBWMWFVHOIWCNFUJZUKW
      MWIVTDWJVLWCNMHULWMWHVJVSWMWEVFJJWGVIWMWFVHVGLWNUKWMVDWDVEWCNMGULUMWMJUNU
      OUPUQURQRUSSUSVMKUAUBZVEUCZJVITZUEZUAVLUFVRVKWRDUAVLVDWOUEZVJWQKWSVFWPJVI
      VDWOVEUJUTUPVAWRVQUAPVLWOVNUEZWQVPKWTWPVOJVIWOVNVEUJUTUPVAVBVC $.
  $}

  ${
    upcic.b $e |- B = ( Base ` D ) $.
    upcic.c $e |- C = ( Base ` E ) $.
    upcic.h $e |- H = ( Hom ` D ) $.
    upcic.j $e |- J = ( Hom ` E ) $.
    upcic.o $e |- O = ( comp ` E ) $.
    upcic.f $e |- ( ph -> F ( D Func E ) G ) $.
    upcic.x $e |- ( ph -> X e. B ) $.
    upcic.y $e |- ( ph -> Y e. B ) $.
    ${
      upciclem2.z $e |- ( ph -> Z e. B ) $.
      upciclem2.w $e |- ( ph -> W e. C ) $.
      upciclem2.m $e |- ( ph -> M e. ( W J ( F ` X ) ) ) $.
      upciclem2.od $e |- .x. = ( comp ` D ) $.
      upciclem2.k $e |- ( ph -> K e. ( X H Y ) ) $.
      upciclem2.l $e |- ( ph -> L e. ( Y H Z ) ) $.
      upciclem2.nm $e |- ( ph -> N = ( ( ( X G Y ) ` K )
                  ( <. W , ( F ` X ) >. O ( F ` Y ) ) M ) ) $.
      $( Lemma for ~ upciclem3 and ~ upeu2 .  (Contributed by Zhi Wang,
         19-Sep-2025.) $)
      upciclem2 $p |- ( ph -> ( ( ( X G Z ) ` ( L ( <. X , Y >. .x. Z ) K ) )
             ( <. W , ( F ` X ) >. O ( F ` Z ) ) M )
             = ( ( ( Y G Z ) ` L ) ( <. W , ( F ` Y ) >. O ( F ` Z ) ) N ) ) $=
        ( cfv cop funcrcl3 funcf1 ffvelcdmd funcf2 catass funcco oveq1d 3eqtr4d
        co oveq2d ) ALRSHVEZUOZKQRHVEZUOZQGUOZRGUOZUPSGUOZOVEVEZMPVKUPZVMOVEZVE
        VHVJMVOVLOVEVEZPVLUPVMOVEZVELKQRUPSEVEVEQSHVEUOZMVPVEVHNVRVEACFOMVJJVHV
        MPVKVLUAUCUDADFGHUEUQUIABCQGABCDFGHTUAUEURZUFUSABCRGVTUGUSUJAQRIVEVKVLJ
        VEKVIABDFGHIJQRTUBUCUEUFUGUTULUSABCSGVTUHUSARSIVEVLVMJVELVGABDFGHIJRSTU
        BUCUEUGUHUTUMUSVAAVSVNMVPABDEFGHIKLOQRSTUBUKUDUEUFUGUHULUMVBVCANVQVHVRU
        NVFVD $.
    $}

    upcic.z $e |- ( ph -> Z e. C ) $.
    upcic.m $e |- ( ph -> M e. ( Z J ( F ` X ) ) ) $.
    upcic.1 $e |- ( ph -> A. w e. B A. f e. ( Z J ( F ` w ) ) E! k e. ( X H w )
           f = ( ( ( X G w ) ` k ) ( <. Z , ( F ` X ) >. O ( F ` w ) ) M ) ) $.
    ${
      $d .x. p $.  $d B p w $.  $d D p $.  $d F f p k w $.  $d G f p k w $.
      $d H f p k w $.  $d J f p w $.  $d K p $.  $d L p $.  $d M f p k w $.
      $d O f p k w $.  $d X f p k w $.  $d Y p $.  $d Z f p k w $.
      upciclem3.od $e |- .x. = ( comp ` D ) $.
      upciclem3.k $e |- ( ph -> K e. ( X H Y ) ) $.
      upciclem3.l $e |- ( ph -> L e. ( Y H X ) ) $.
      upciclem3.mn $e |- ( ph -> M = ( ( ( Y G X ) ` L )
                             ( <. Z , ( F ` Y ) >. O ( F ` X ) ) N ) ) $.
      upciclem3.nm $e |- ( ph -> N = ( ( ( X G Y ) ` K )
                             ( <. Z , ( F ` X ) >. O ( F ` Y ) ) M ) ) $.
      $( Lemma for ~ upciclem4 .  (Contributed by Zhi Wang, 17-Sep-2025.) $)
      upciclem3 $p |- ( ph -> ( L ( <. X , Y >. .x. X ) K )
                          = ( ( Id ` D ) ` X ) ) $=
        ( vp cv co cfv wceq ccid fveq2 oveq1d eqeq2d upciclem1 funcrcl2 catcocl
        cop eqid catidcl upciclem2 eqtr4d funcid funcf1 ffvelcdmd catlid eqtr2d
        funcrcl3 reu2eqd ) APURUSZSSKUTZVAZPUASJVAZVJWERUTZUTZVBPONSTVJSFUTUTZW
        CVAZPWFUTZVBPSEVCVAZVAZWCVAZPWFUTZVBURSSLUTWHWLWBWHVBZWGWJPWOWDWIPWFWBW
        HWCVDVEVFWBWLVBZWGWNPWPWDWMPWFWBWLWCVDVEVFABCHGJKLMPPRSSUAURULUHUKVGACE
        FNOLSTSUBUDUMAEIJKUGVHZUHUIUHUNUOVIACEWKLSUBUDWKVKZWQUHVLAPOTSKUTVAQUAT
        JVAVJWERUTUTWJUPACDEFIJKLMNOPQRUASTSUBUCUDUEUFUGUHUIUHUJUKUMUNUOUQVMVNA
        WNWEIVCVAZVAZPWFUTPAWMWTPWFACEWKIJKWSSUBWRWSVKZUGUHVOVEADIRWSPMUAWEUCUE
        XAAEIJKUGVTUJUFACDSJACDEIJKUBUCUGVPUHVQUKVRVSWA $.
    $}

    ${
      $d B p q v $.  $d B p q w $.  $d D p q r $.  $d F f k p q w $.
      $d F g l p q v $.  $d F p q r $.  $d G f k p q w $.  $d G g l p q v $.
      $d G p q r $.  $d H f k p q w $.  $d H g l p q v $.  $d H p q r $.
      $d J f p q w $.  $d J g p q v $.  $d M f k w $.  $d M g l $.
      $d M p q r $.  $d N f k $.  $d N g l v $.  $d N p q r $.
      $d O f k p q w $.  $d O g l p q v $.  $d O p q r $.  $d X f k p q w $.
      $d X g l p q v $.  $d X p q r $.  $d Y f k p q w $.  $d Y g l p q v $.
      $d Y p q r $.  $d Z f k p q w $.  $d Z g l p q v $.  $d Z p q r $.
      $d p ph q $.
      upcic.n $e |- ( ph -> N e. ( Z J ( F ` Y ) ) ) $.
      upcic.2 $e |- ( ph -> A. v e. B A. g e. ( Z J ( F ` v ) )
           E! l e. ( Y H v )
           g = ( ( ( Y G v ) ` l ) ( <. Z , ( F ` Y ) >. O ( F ` v ) ) N ) ) $.
      $( Lemma for ~ upcic and ~ upeu .  (Contributed by Zhi Wang,
         19-Sep-2025.) $)
      upciclem4 $p |- ( ph -> ( X ( ~=c ` D ) Y /\ E. r e. ( X ( Iso ` D ) Y )
         N = ( ( ( X G Y ) ` r ) ( <. Z , ( F ` X ) >. O ( F ` Y ) ) M ) ) ) $=
        ( vp vq ccic cfv wbr cv co cop wceq ciso wrex wreu upciclem1 reurex syl
        wcel wa simpl 3syl eqid cfunc ad2antrr funcrcl2 cco ccid simplrl simprl
        simprr simplrr upciclem3 isisod brcici rexlimddv reximssdv fveq2 oveq1d
        wral eqeq2d cbvrexvw sylib jca ) ARSFURUSUTZPUAVAZRSLVBZUSZOTRKUSZVCZSK
        USZQVBZVBZVDZUARSFVEUSZVBZVFZAPUPVAZWSUSZOXDVBZVDZWQUPRSMVBZAXMUPXNVGXM
        UPXNVFABDIGKLMNOPQRSTUPUMUJUNVHXMUPXNVIVJZAXJXNVKZXMVLZVLZOUQVAZSRLVBUS
        PTXCVCZXAQVBVBVDZWQUQSRMVBZXRAYAUQYBVGYAUQYBVFAXQVMACDUBHKLMNPOQSRTUQUO
        UIULVHYAUQYBVIVNZXRXSYBVKZYAVLZVLZDFXJXGRSXGVOZUCYFFJKLAKLFJVPVBUTXQYEU
        HVQZVRZARDVKXQYEUIVQZASDVKXQYEUJVQZYFDFFVSUSZFVTUSZXJXSMXGRSUCUEYLVOZYG
        YMVOYIYJYKAXPXMYEWAZXRYDYAWBZYFBDEFYLGIJKLMNXJXSOPQRSTUCUDUEUFUGYHYJYKA
        TEVKXQYEUKVQZAOTXANVBVKXQYEULVQAGVAIVARBVAZLVBUSOXBYRKUSZQVBVBVDIRYRMVB
        VGGTYSNVBWLBDWLXQYEUMVQYNYOYPXRYDYAWCZAXPXMYEWDZWEYFCDEFYLHUBJKLMNXSXJP
        OQSRTUCUDUEUFUGYHYKYJYQAPTXCNVBVKXQYEUNVQAHVAUBVASCVAZLVBUSPXTUUBKUSZQV
        BVBVDUBSUUBMVBVGHTUUCNVBWLCDWLXQYEUOVQYNYPYOUUAYTWEWFZWGWHWHAXMUPXHVFXI
        AXMXMUPXHXNXOXRYAXJXHVKUQYBYCUUDWHAXPXMWCWIXMXFUPUAXHXJWRVDZXLXEPUUEXKW
        TOXDXJWRWSWJWKWMWNWOWP $.

      $( A universal property defines an object up to isomorphism given its
         existence.  (Contributed by Zhi Wang, 17-Sep-2025.) $)
      upcic $p |- ( ph -> X ( ~=c ` D ) Y ) $=
        ( vr ccic cfv wbr cv co cop wceq ciso wrex upciclem4 simpld ) ARSFUPUQU
        RPUOUSRSLUTUQOTRKUQVASKUQQUTUTVBUORSFVCUQUTVDABCDEFGHIJKLMNOPQRSTUOUAUB
        UCUDUEUFUGUHUIUJUKULUMUNVEVF $.

      $( A universal property defines an essentially unique (strong form) pair
         of object ` X ` and morphism ` M ` if it exists.  (Contributed by Zhi
         Wang, 19-Sep-2025.) $)
      upeu $p |- ( ph -> E! r e. ( X ( Iso ` D ) Y )
           N = ( ( ( X G Y ) ` r ) ( <. Z , ( F ` X ) >. O ( F ` Y ) ) M ) ) $=
        ( cv co cfv cop wceq ciso wrex wrmo wreu ccic wbr upciclem4 simprd eqid
        wss funcrcl2 isohom upciclem1 reurmo syl nfcv ssrmof sylc reu5 sylanbrc
        ) APUAUPRSLUQUROTRKURUSSKURQUQUQUTZUARSFVAURZUQZVBZWAUAWCVCZWAUAWCVDARS
        FVEURVFWDABCDEFGHIJKLMNOPQRSTUAUBUCUDUEUFUGUHUIUJUKULUMUNUOVGVHAWCRSMUQ
        ZVJWAUAWFVCZWEADFMWBRSUCUEWBVIAFJKLUHVKUIUJVLAWAUAWFVDWGABDIGKLMNOPQRST
        UAUMUJUNVMWAUAWFVNVOWAUAWCWFUAWCVPUAWFVPVQVRWAUAWCVSVT $.
    $}

    ${
      $d B g l p $.  $d B w $.  $d D l p $.  $d E p $.  $d F f k w $.
      $d F l p $.  $d G f k w $.  $d G l p $.  $d H f k w $.  $d H l p $.
      $d I p $.  $d J f w $.  $d J l p $.  $d K l p $.  $d M f k w $.
      $d M l p $.  $d N p $.  $d O f k w $.  $d O l p $.  $d X f k w $.
      $d X l p $.  $d Y l p $.  $d Z f k w $.  $d Z l p $.  $d f g k p v $.
      $d g l p ph v $.  $d p v w $.
      upeu2.i $e |- I = ( Iso ` D ) $.
      upeu2.k $e |- ( ph -> K e. ( X I Y ) ) $.
      upeu2.n $e |- ( ph ->
           N = ( ( ( X G Y ) ` K ) ( <. Z , ( F ` X ) >. O ( F ` Y ) ) M ) ) $.
      $( Generate new universal morphism through isomorphism from existing
         universal object.  (Contributed by Zhi Wang, 20-Sep-2025.) $)
      upeu2 $p |- ( ph -> ( N e. ( Z J ( F ` Y ) ) /\
       A. v e. B A. g e. ( Z J ( F ` v ) )
           E! l e. ( Y H v )
           g = ( ( ( Y G v ) ` l ) ( <. Z , ( F ` Y ) >. O ( F ` v ) ) N ) ) )
      $=
        ( vp cfv co wcel cv cop wceq wreu wral funcrcl3 funcf1 ffvelcdmd funcf2
        funcrcl2 isohom sseldd catcocl eqeltrd wa adantr simprl simprr cco eqid
        upciclem1 ccat ad2antrr simpr upeu2lem fveq2d cfunc wbr upciclem2 eqtrd
        oveq1d eqeq2d reuxfr1dd mpbid ralrimivva jca ) ARUBUAKUSZOUTZVAHVBZUCVB
        ZUACVBZLUTUSRUBWRVCXBKUSZSUTUTZVDZUCUAXBMUTZVEZHUBXCOUTZVFCDVFARPTUALUT
        ZUSZQUBTKUSZVCZWRSUTUTZWSUQAEJSQXJOUBXKWRUEUGUHAFJKLUIVGULADETKADEFJKLU
        DUEUIVHZUJVIADEUAKXNUKVIUMATUAMUTZXKWROUTPXIADFJKLMOTUAUDUFUGUIUJUKVJAT
        UANUTZXOPADFMNTUAUDUFUOAFJKLUIVKZUJUKVLUPVMZVIVNVOAXGCHDXHAXBDVAZWTXHVA
        ZVPZVPZWTURVBZTXBLUTZUSZQXLXCSUTZUTZVDZURTXBMUTZVEXGYBBDIGKLMOQWTSTXBUB
        URAGVBIVBTBVBZLUTUSQXLYJKUSZSUTUTVDITYJMUTVEGUBYKOUTVFBDVFYAUNVQAXSXTVR
        ZAXSXTVSWBYBYHXEURUCXAPTUAVCXBFVTUSZUTUTZYIXFYBXAXFVAZVPDFYMPXAMTUAXBUD
        UFYMWAZAFWCVAZYAYOXQWDATDVAZYAYOUJWDAUADVAZYAYOUKWDYBXSYOYLVQAPXOVAZYAY
        OXRWDYBYOWEVNYBYCYIVAZVPDFYMUCPYCMNTUAXBUDUFYPUOAYQYAUUAXQWDAYRYAUUAUJW
        DAYSYAUUAUKWDYBXSUUAYLVQAPXPVAYAUUAUPWDYBUUAWEWFYBYOYCYNVDZVPZVPZYGXDWT
        UUDYGYNYDUSZQYFUTXDUUDYEUUEQYFUUDYCYNYDYBYOUUBVSWGWLUUDDEFYMJKLMOPXAQRS
        UBTUAXBUDUEUFUGUHAKLFJWHUTWIYAUUCUIWDAYRYAUUCUJWDAYSYAUUCUKWDYBXSUUCYLV
        QAUBEVAYAUUCULWDAQUBXKOUTVAYAUUCUMWDYPAYTYAUUCXRWDYBYOUUBVRARXMVDYAUUCU
        QWDWJWKWMWNWOWPWQ $.
    $}
  $}

  $c UP $.

  $( Extend class notation with the class of universal properties. $)
  cup $a class UP $.

  ${
    $d B b c d e f g h j k m o w x y $.  $d C b c d e f g h j k m o w x y $.
    $d D b c d e f g h j k m o w x y $.  $d E b c d e f g h j k m o w x y $.
    $d F b c d e f g h j k m o w x y $.  $d G b c d e f g h j k m o w x y $.
    $d H b c d e f g h j k m o w x y $.  $d J b c d e f g h j k m o w x y $.
    $d M b c d e f g h j k m o w x y $.  $d N b c d e f g h j k m o w x y $.
    $d O b c d e f g h j k m o w x y $.  $d W b c d e f g h j k m o w x y $.
    $d X b c d e f g h j k m o w x y $.  $d Y b c d e f g h j k m o w x y $.
    $d m ph x $.
    $( Definition of the class of universal properties.

       Given categories ` D ` and ` E ` , if ` F : D --> E ` is a functor and
       ` W ` an object of ` E ` , a universal pair from ` W ` to ` F ` is a
       pair ` <. X , M >. ` consisting of an object ` X ` of ` D ` and a
       morphism ` M : W --> F X ` of ` E ` , such that to every pair
       ` <. y , g >. ` with ` y ` an object of ` D ` and ` g : W --> F y ` a
       morphism of ` E ` , there is a unique morphism ` k : X --> y ` of ` D `
       with ` F k .o. M = g ` .  Such property is commonly referred to as a
       universal property.  In our definition, it is denoted as
       ` X ( F ( D UP E ) W ) M ` .

       Note that the universal pair is termed differently as "universal arrow"
       in p. 55 of Mac Lane, Saunders, _Categories for the Working
       Mathematician_, 2nd Edition, Springer Science+Business Media, New York,
       (1998) [QA169.M33 1998]; available at
       ~ https://math.mit.edu/~~hrm/palestine/maclane-categories.pdf (retrieved
       6 Oct 2025).  Interestingly, the "universal arrow" is referring to the
       morphism ` M ` instead of the pair near the end of the same piece of the
       text, causing name collision.  The name "universal arrow" is also
       adopted in papers such as ~ https://arxiv.org/pdf/2212.08981 .
       Alternatively, the universal pair is called the "universal morphism" in
       Wikipedia ( ~ https://en.wikipedia.org/wiki/Universal_property ) as well
       as published works, e.g., ~ https://arxiv.org/pdf/2412.12179 .  But the
       pair ` <. X , M >. ` should be named differently as the morphism ` M ` ,
       and thus we call ` X ` the _universal object_, ` M ` the _universal
       morphism_, and ` <. X , M >. ` the _universal pair_.

       Given its existence, such universal pair is essentially unique
       ( ~ upeu3 ), and can be generated from an existing universal pair by
       isomorphisms ( ~ upeu4 ).  See also ~ oppcup for the dual concept.

       (Contributed by Zhi Wang, 24-Sep-2025.) $)
    df-up $a |- UP = ( d e. _V , e e. _V |->
            [_ ( Base ` d ) / b ]_ [_ ( Base ` e ) / c ]_
            [_ ( Hom ` d ) / h ]_ [_ ( Hom ` e ) / j ]_
            [_ ( comp ` e ) / o ]_
            ( f e. ( d Func e ) , w e. c |->
            { <. x , m >. | ( ( x e. b /\ m e. ( w j ( ( 1st ` f ) ` x ) ) ) /\
            A. y e. b A. g e. ( w j ( ( 1st ` f ) ` y ) )
            E! k e. ( x h y ) g = ( ( ( x ( 2nd ` f ) y ) ` k )
            ( <. w , ( ( 1st ` f ) ` x ) >. o ( ( 1st ` f ) ` y ) ) m )
            ) } ) ) $.

    $( The domain of ` UP ` is a relation.  (Contributed by Zhi Wang,
       25-Sep-2025.) $)
    reldmup $p |- Rel dom UP $=
      ( vd ve vb vc vh vj vo vf vw vx vm vg vk vy cvv cv cbs cfv co csb chom wa
      cco cfunc wcel c1st c2nd cop wceq wreu wral copab cmpo cup df-up reldmmpo
      ) ABOOCAPZQRDBPZQREUQUARFURUARGURUCRHIUQURUDSDPJPZCPZUEKPZIPZUSHPZUFRZRZF
      PZSUEUBLPMPUSNPZVCUGRSRVAVBVEUHVGVDRZGPSSUIMUSVGEPSUJLVBVHVFSUKNUTUKUBJKU
      LUMTTTTTUNJNIBHLEFMKGCDAUOUP $.

    upfval.b $e |- B = ( Base ` D ) $.
    upfval.c $e |- C = ( Base ` E ) $.
    upfval.h $e |- H = ( Hom ` D ) $.
    upfval.j $e |- J = ( Hom ` E ) $.
    upfval.o $e |- O = ( comp ` E ) $.
    $( Function value of the class of universal properties.  (Contributed by
       Zhi Wang, 24-Sep-2025.)  (Proof shortened by Zhi Wang, 12-Nov-2025.) $)
    upfval $p |- ( D UP E ) = ( f e. ( D Func E ) , w e. C |->
           { <. x , m >. | ( ( x e. B /\ m e. ( w J ( ( 1st ` f ) ` x ) ) ) /\
           A. y e. B A. g e. ( w J ( ( 1st ` f ) ` y ) )
           E! k e. ( x H y ) g = ( ( ( x ( 2nd ` f ) y ) ` k )
           ( <. w , ( ( 1st ` f ) ` x ) >. O ( ( 1st ` f ) ` y ) ) m ) ) } ) $=
      ( cfv vd ve vb vc vh vj vo cvv wcel wa cup co cfunc cv c1st c2nd cop wceq
      wreu wral copab cmpo cbs cco csb fvexd fveq2 adantr eqtr4di simplr fveq2d
      chom simplll simp-4r simp-5r simp-6l simp-6r oveq12d eleq2d oveqd anbi12d
      oveqdr simpr eqeq2d reueqbidv raleqbidv opabbidv mpoeq123dv csbied2 df-up
      ovex fvexi mpoex ovmpoa wn c0 reldmup ovprc wo reldmfunc 0mpo0 syl eqtr4d
      orcd pm2.61i ) FUHUIKUHUIUJZFKUKULZGCFKUMULZEAUNZDUIZJUNZCUNZXIGUNZUOTZTZ
      MULZUIZUJZHUNZIUNXIBUNZXMUPTULTZXKXLXOUQZXTXNTZNULZULZURZIXIXTLULZUSZHXLY
      CMULZUTZBDUTZUJZAJVAZVBZURUAUBFKUHUHUCUAUNZVCTZUDUBUNZVCTZUEYOVLTZUFYQVLT
      ZUGYQVDTZGCYOYQUMULZUDUNZXIUCUNZUIZXKXLXOUFUNZULZUIZUJZXSYAXKYBYCUGUNZULZ
      ULZURZIXIXTUEUNZULZUSZHXLYCUUFULZUTZBUUDUTZUJZAJVAZVBZVEZVEZVEZVEZVEYNUKY
      OFURZYQKURZUJZUCYPDUVFYNUHUVIYOVCVFUVIYPFVCTZDUVGYPUVJURUVHYOFVCVGVHOVIUV
      IUUDDURZUJZUDYREUVEYNUHUVLYQVCVFUVLYRKVCTEUVLYQKVCUVGUVHUVKVJVKPVIUVLUUCE
      URZUJZUEYSLUVDYNUHUVNYOVLVFUVNYSFVLTLUVNYOFVLUVGUVHUVKUVMVMVKQVIUVNUUNLUR
      ZUJZUFYTMUVCYNUHUVPYQVLVFUVPYTKVLTMUVPYQKVLUVGUVHUVKUVMUVOVNVKRVIUVPUUFMU
      RZUJZUGUUANUVBYNUHUVRYQVDVFUVRUUAKVDTNUVRYQKVDUVGUVHUVKUVMUVOUVQVOVKSVIUV
      RUUJNURZUJZGCUUBUUCUVAXHEYMUVTYOFYQKUMUVGUVHUVKUVMUVOUVQUVSVPUVGUVHUVKUVM
      UVOUVQUVSVQVRUVLUVMUVOUVQUVSVNUVTUUTYLAJUVTUUIXRUUSYKUVTUUEXJUUHXQUVTUUDD
      XIUVIUVKUVMUVOUVQUVSVOZVSUVTUUGXPXKUVTUUFMXLXOUVPUVQUVSVJZVTVSWAUVTUURYJB
      UUDDUWAUVTUUPYHHUUQYIUVTUUFMXLYCUWBVTUVTUUMYFIUUOYGUVRUVSABUUNLUVNUVOUVQV
      JWBUVTUULYEXSUVTUUKYDYAXKUVTUUJNYBYCUVRUVSWCVTVTWDWEWFWFWAWGWHWIWIWIWIWIA
      BCUBGHUEUFIJUGUCUDUAWJGCXHEYMFKUMWKEKVCPWLWMWNXFWOZXGWPYNFKUKWQWRUWCXHWPU
      RZEWPURZWSYNWPURUWCUWDUWEFKUMWTWRXDGCXHEYMXAXBXCXE $.

    upfval2.w $e |- ( ph -> W e. C ) $.
    ${
      upfval2.f $e |- ( ph -> F e. ( D Func E ) ) $.
      $( Function value of the class of universal properties.  (Contributed by
         Zhi Wang, 24-Sep-2025.) $)
      upfval2 $p |- ( ph -> ( F ( D UP E ) W ) =
           { <. x , m >. | ( ( x e. B /\ m e. ( W J ( ( 1st ` F ) ` x ) ) ) /\
           A. y e. B A. g e. ( W J ( ( 1st ` F ) ` y ) )
           E! k e. ( x H y ) g = ( ( ( x ( 2nd ` F ) y ) ` k )
           ( <. W , ( ( 1st ` F ) ` x ) >. O ( ( 1st ` F ) ` y ) ) m ) ) } ) $=
        ( vf vw cfunc co wcel cv c1st cfv c2nd cop wceq wreu wral copab cvv cup
        anass opabbii cbs fvexi a1i simprl ovexd abexd opabex3d eqeltrid fveq1d
        wa fveq2 oveq2d eleq2d anbi2d opeq2d oveq12d oveqd eqidd eqeq2d reubidv
        oveq123d raleqbidv ralbidv anbi12d opabbidv oveq1 oveq1d upfval syl3anc
        opeq1 ovmpog ) AKFJUEUFZUGOEUGBUHZDUGZIUHZOWMKUIUJZUJZMUFZUGZVJZGUHZHUH
        ZWMCUHZKUKUJZUFZUJZWOOWQULZXCWPUJZNUFZUFZUMZHWMXCLUFZUNZGOXHMUFZUOZCDUO
        ZVJZBIUPZUQUGKOFJURUFZUFXRUMUBUAAXRWNWSXPVJZVJZBIUPUQXQYABIWNWSXPUSUTAX
        TBIDUQDUQUGADFVAPVBVCAWNVJZXTIWRUQYBWSXPVDYBOWQMVEVFVGVHUCUDKOWLEWNWOUD
        UHZWMUCUHZUIUJZUJZMUFZUGZVJZXAXBWMXCYDUKUJZUFZUJZWOYCYFULZXCYEUJZNUFZUF
        ZUMZHXLUNZGYCYNMUFZUOZCDUOZVJZBIUPXRXSWNWOYCWQMUFZUGZVJZXAXFWOYCWQULZXH
        NUFZUFZUMZHXLUNZGYCXHMUFZUOZCDUOZVJZBIUPUQYDKUMZUUBUUNBIUUOYIUUEUUAUUMU
        UOYHUUDWNUUOYGUUCWOUUOYFWQYCMUUOWMYEWPYDKUIVKZVIZVLVMVNUUOYTUULCDUUOYRU
        UJGYSUUKUUOYNXHYCMUUOXCYEWPUUPVIZVLUUOYQUUIHXLUUOYPUUHXAUUOYLXFWOWOYOUU
        GUUOYMUUFYNXHNUUOYFWQYCUUQVOUURVPUUOXBYKXEUUOYJXDWMXCYDKUKVKVQVIUUOWOVR
        WAVSVTWBWCWDWEYCOUMZUUNXQBIUUSUUEWTUUMXPUUSUUDWSWNUUSUUCWRWOYCOWQMWFVMV
        NUUSUULXOCDUUSUUJXMGUUKXNYCOXHMWFUUSUUIXKHXLUUSUUHXJXAUUSUUGXIXFWOUUSUU
        FXGXHNYCOWQWJWGVQVSVTWBWCWDWEBCUDDEFUCGHIJLMNPQRSTWHWKWI $.
    $}

    upfval3.f $e |- ( ph -> F ( D Func E ) G ) $.
    $( Function value of the class of universal properties.  (Contributed by
       Zhi Wang, 24-Sep-2025.) $)
    upfval3 $p |- ( ph -> ( <. F , G >. ( D UP E ) W ) =
            { <. x , m >. | ( ( x e. B /\ m e. ( W J ( F ` x ) ) ) /\
            A. y e. B A. g e. ( W J ( F ` y ) )
            E! k e. ( x H y ) g = ( ( ( x G y ) ` k )
            ( <. W , ( F ` x ) >. O ( F ` y ) ) m ) ) } ) $=
      ( cop cup co cv wcel c1st cfv c2nd wceq wreu wral copab cfunc df-br sylib
      wbr upfval2 cvv relfunc brrelex12i op1stg syl fveq1d oveq2d eleq2d anbi2d
      opeq2d oveq12d op2ndg oveqd eqidd oveq123d eqeq2d reubidv ralbidv anbi12d
      wa raleqbidv opabbidv eqtrd ) AKLUDZPFJUEUFUFBUGZDUHZIUGZPWEWDUIUJZUJZNUF
      ZUHZVTZGUGZHUGZWECUGZWDUKUJZUFZUJZWGPWIUDZWOWHUJZOUFZUFZULZHWEWOMUFZUMZGP
      WTNUFZUNZCDUNZVTZBIUOZWFWGPWEKUJZNUFZUHZVTZWMWNWEWOLUFZUJZWGPXKUDZWOKUJZO
      UFZUFZULZHXDUMZGPXRNUFZUNZCDUNZVTZBIUOZABCDEFGHIJWDMNOPQRSTUAUBAKLFJUPUFZ
      USZWDYHUHUCKLYHUQURUTAYIXJYGULUCYIXIYFBIYIWLXNXHYEYIWKXMWFYIWJXLWGYIWIXKP
      NYIWEWHKYIKVAUHLVAUHVTZWHKULKLYHFJVBVCZKLVAVAVDVEZVFZVGVHVIYIXGYDCDYIXEYB
      GXFYCYIWTXRPNYIWOWHKYLVFZVGYIXCYAHXDYIXBXTWMYIWRXPWGWGXAXSYIWSXQWTXROYIWI
      XKPYMVJYNVKYIWNWQXOYIWPLWEWOYIYJWPLULYKKLVAVAVLVEVMVFYIWGVNVOVPVQWAVRVSWB
      VEWC $.

    $( Lemma for ~ isup and other theorems.  (Contributed by Zhi Wang,
       25-Sep-2025.) $)
    isuplem $p |- ( ph -> ( X ( <. F , G >. ( D UP E ) W ) M <->
               ( ( X e. B /\ M e. ( W J ( F ` X ) ) )
               /\ A. y e. B A. g e. ( W J ( F ` y ) )
               E! k e. ( X H y ) g = ( ( ( X G y ) ` k )
               ( <. W , ( F ` X ) >. O ( F ` y ) ) M ) ) ) ) $=
      ( vx vm cv co cfv cop wceq wreu wral cup oveq1 fveq2 opeq2d oveq1d fveq1d
      upfval3 eqidd oveq123d eqeq2d reueqbidv 2ralbidv reubidv wa fveq2d oveq2d
      oveq2 simpl brab2ddw ) AFUFZGUFZUDUFZBUFZJUGZUHZUEUFZOVNIUHZUIZVOIUHZNUGZ
      UGZUJZGVNVOKUGZUKZFOWALUGZULBCULVLVMPVOJUGZUHZMOPIUHZUIZWANUGZUGZUJZGPVOK
      UGZUKZFWGULBCULVLWIVRWLUGZUJZGWOUKZFWGULBCULUDUEPMCOVSLUGIJUIOEHUMUGUGCOW
      JLUGAUDBCDEFGUEHIJKLNOQRSTUAUBUCUSVNPUJZWFWSBFCWGWTWDWRGWEWOVNPVOKUNWTWCW
      QVLWTVQWIVRVRWBWLWTVTWKWANWTVSWJOVNPIUOUPUQWTVMVPWHVNPVOJUNURWTVRUTVAVBVC
      VDVRMUJZWSWPBFCWGXAWRWNGWOXAWQWMVLVRMWIWLVIVBVEVDWTXAVFZCUTXBVSWJOLXBVNPI
      WTXAVJVGVHVK $.

    isup.x $e |- ( ph -> X e. B ) $.
    isup.m $e |- ( ph -> M e. ( W J ( F ` X ) ) ) $.
    $( The predicate "is a universal pair".  (Contributed by Zhi Wang,
       24-Sep-2025.) $)
    isup $p |- ( ph -> ( X ( <. F , G >. ( D UP E ) W ) M <->
            A. y e. B A. g e. ( W J ( F ` y ) )
            E! k e. ( X H y ) g = ( ( ( X G y ) ` k )
            ( <. W , ( F ` X ) >. O ( F ` y ) ) M ) ) ) $=
      ( cop cup co wbr wcel cfv wa cv wceq wreu wral jca isuplem mpbirand ) APM
      IJUFOEHUGUHUHUIPCUJZMOPIUKZLUHUJZULFUMGUMPBUMZJUHUKMOVAUFVCIUKZNUHUHUNGPV
      CKUHUOFOVDLUHUPBCUPAUTVBUDUEUQABCDEFGHIJKLMNOPQRSTUAUBUCURUS $.
  $}

  ${
    $d A f g k m w x y $.  $d B f g k m w x y $.  $d C f g k m w x y $.
    $d D f g k m w x y $.  $d V f g k m w x y $.  $d f g k m ph w x y $.
    uppropd.1 $e |- ( ph -> ( Homf ` A ) = ( Homf ` B ) ) $.
    uppropd.2 $e |- ( ph -> ( comf ` A ) = ( comf ` B ) ) $.
    uppropd.3 $e |- ( ph -> ( Homf ` C ) = ( Homf ` D ) ) $.
    uppropd.4 $e |- ( ph -> ( comf ` C ) = ( comf ` D ) ) $.
    uppropd.a $e |- ( ph -> A e. V ) $.
    uppropd.b $e |- ( ph -> B e. V ) $.
    uppropd.c $e |- ( ph -> C e. V ) $.
    uppropd.d $e |- ( ph -> D e. V ) $.
    $( If two categories have the same set of objects, morphisms, and
       compositions, then they have the same universal pairs.  (Contributed by
       Zhi Wang, 20-Nov-2025.) $)
    uppropd $p |- ( ph -> ( A UP C ) = ( B UP D ) ) $=
      ( co cfv cv wcel wa eqid vf vw vx vm vg vk vy cfunc cbs c1st chom cop cco
      c2nd wceq wreu wral copab cmpo funcpropd homfeqbas adantr chomf ad3antrrr
      cup simprr ad2antrr simprl func1st2nd funcf1 ffvelcdmda homfeqval ad4antr
      wf simplr ccomf ad5antr wbr funcf2 comfeqval eqeq2d reueqbidva raleqbidva
      adantrr pm5.32da simplrr eleq2d anbi1d bitrd opabbidv mpoeq123dva 3eqtr4g
      upfval ) AUAUBBDUHOZDUIPZUCQZBUIPZRZUDQZUBQZWPUAQZUJPZPZDUKPZOZRZSZUEQZUF
      QZWPUGQZXAUNPZOZPZWSWTXCULZXJXBPZDUMPZOOZUOZUFWPXJBUKPZOZUPZUEWTXOXDOZUQZ
      UGWQUQZSZUCUDURZUSUAUBCEUHOZEUIPZWPCUIPZRZWSWTXCEUKPZOZRZSZXHXMWSXNXOEUMP
      ZOOZUOZUFWPXJCUKPZOZUPZUEWTXOYKOZUQZUGYIUQZSZUCUDURZUSBDVEOCEVEOAUAUBWNWO
      YFYGYHUUEABCDEFGHIJKLMNUTAWOYHUOXAWNRZADEIVAVBAUUFWTWORZSZSZYEUUDUCUDUUIY
      EXGUUCSUUDUUIXGYDUUCUUIXGSZYCUUBUGWQYIUUIWQYIUOZXGAUUKUUHABCGVAVBZVBUUJXJ
      WQRZSZYAYTUEYBUUAUUNWODEXDYKWTXOWOTZXDTZYKTZADVCPEVCPUOZUUHXGUUMIVDZUUIUU
      GXGUUMAUUFUUGVFVGZUUJWQWOXJXBUUIWQWOXBVNXGUUIWQWOBDXBXKWQTZUUOUUIBDXAAUUF
      UUGVHVIZVJZVBVKZVLUUNXHYBRZSZXRYQUFXTYSUVFWQBCXSYRWPXJUVAXSTZYRTZABVCPCVC
      PUOUUHXGUUMUVEGVMUUJWRUUMUVEUUIWRXFVHVGZUUJUUMUVEVOZVLUVFXIXTRZSZXQYPXHUV
      LWODEYOXPWSXMXDWTXCXOUUOUUPXPTZYOTZUUNUURUVEUVKUUSVGADVPPEVPPUOUUHXGUUMUV
      EUVKJVQUUNUUGUVEUVKUUTVGUUJXCWORZUUMUVEUVKUUIWRUVOXFUUIWQWOWPXBUVCVKZWDVD
      UUNXOWORUVEUVKUVDVGUUJXFUUMUVEUVKUUIWRXFVFVDUVFXTXCXOXDOXIXLUVFWQBDXBXKXS
      XDWPXJUVAUVGUUPUUIXBXKWNVRXGUUMUVEUVBVDUVIUVJVSVKVTWAWBWCWCWEUUIXGYNUUCUU
      IXGWRYMSYNUUIWRXFYMUUIWRSZXEYLWSUVQWODEXDYKWTXCUUOUUPUUQAUURUUHWRIVGAUUFU
      UGWRWFUVPVLWGWEUUIWRYJYMUUIWQYIWPUULWGWHWIWHWIWJWKUCUGUBWQWOBUAUEUFUDDXSX
      DXPUVAUUOUVGUUPUVMWMUCUGUBYIYHCUAUEUFUDEYRYKYOYITYHTUVHUUQUVNWMWL $.
  $}

  ${
    $d C f g k m w x y $.  $d D f g k m w x y $.  $d E f g k m w x y $.
    $( The domain of ` ( D UP E ) ` is a relation.  (Contributed by Zhi Wang,
       16-Oct-2025.) $)
    reldmup2 $p |- Rel dom ( D UP E ) $=
      ( vf vw vx vm vg vk vy cfunc co cbs cfv cv wcel c1st chom wa wral eqid
      c2nd cop cco wceq wreu copab cup upfval reldmmpo ) CDABJKBLMZENZALMZOFNZD
      NZUKCNZPMZMZBQMZKORGNHNUKINZUOUAMKMUMUNUQUBUSUPMZBUCMZKKUDHUKUSAQMZKUEGUN
      UTURKSIULSREFUFABUGKEIDULUJACGHFBVBURVAULTUJTVBTURTVATUHUI $.

    $( The set of universal pairs is a relation.  (Contributed by Zhi Wang,
       25-Sep-2025.) $)
    relup $p |- Rel ( F ( D UP E ) W ) $=
      ( vx vm vw vf vg vk vy cv cbs cfv wcel chom co wa wral eqid c1st c2nd cop
      cco wceq wreu cfunc cup upfval relmpoopab ) ELZAMNZOFLZGLZUKHLZUANZNZBPNZ
      QORILJLUKKLZUOUBNQNUMUNUQUCUSUPNZBUDNZQQUEJUKUSAPNZQUFIUNUTURQSKULSRHGEFA
      BUGQBMNZCDABUHQEKGULVCAHIJFBVBURVAULTVCTVBTURTVATUIUJ $.

    uprcl.c $e |- C = ( Base ` E ) $.
    $( Reverse closure for the class of universal property.  (Contributed by
       Zhi Wang, 25-Sep-2025.) $)
    uprcl $p |- ( X e. ( F ( D UP E ) W )
              -> ( F e. ( D Func E ) /\ W e. C ) ) $=
      ( vf vw vx vm vg vk vy co cv cfv wcel chom eqid cfunc cbs c1st wa cop cco
      c2nd wceq wreu wral copab cup upfval elmpocl ) HIBCUAOAJPZBUBQZRKPZIPZUOH
      PZUCQZQZCSQZORUDLPMPUONPZUSUGQOQUQURVAUEVCUTQZCUFQZOOUHMUOVCBSQZOUILURVDV
      BOUJNUPUJUDJKUKDEBCULOFJNIUPABHLMKCVFVBVEUPTGVFTVBTVETUMUN $.
  $}

  ${
    up1st2nd.1 $e |- ( ph -> X ( F ( D UP E ) W ) M ) $.
    $( Rewrite the universal property predicate with separated parts.
       (Contributed by Zhi Wang, 23-Oct-2025.) $)
    up1st2nd $p |- ( ph -> X ( <. ( 1st ` F ) , ( 2nd ` F ) >.
                               ( D UP E ) W ) M ) $=
      ( cup co c1st cfv c2nd cop cfunc wrel wcel wceq relfunc cbs wa df-br eqid
      wbr sylib uprcl syl simpld 1st2nd sylancr oveq1d breqdi ) ADFBCIJZJZDKLDM
      LNZFUMJGEADUOFUMABCOJZPDUPQZDUORBCSAUQFCTLZQZAGENZUNQZUQUSUAAGEUNUDVAHGEU
      NUBUEURBCDFUTURUCUFUGUHDUPUIUJUKHUL $.
  $}

  ${
    up1st2ndr.1 $e |- ( ph -> F e. ( D Func E ) ) $.
    ${
      up1st2ndr.2 $e |- ( ph -> X ( <. ( 1st ` F ) , ( 2nd ` F ) >.
                                    ( D UP E ) W ) M ) $.
      $( Combine separated parts in the universal property predicate.
         (Contributed by Zhi Wang, 23-Oct-2025.) $)
      up1st2ndr $p |- ( ph -> X ( F ( D UP E ) W ) M ) $=
        ( c1st cfv c2nd cop cup co cfunc wrel wcel wceq relfunc 1st2nd sylancr
        oveq1d eqcomd breqdi ) ADJKDLKMZFBCNOZOZDFUGOZGEAUIUHADUFFUGABCPOZQDUJR
        DUFSBCTHDUJUAUBUCUDIUE $.
    $}

    $( Combine/separate parts in the universal property predicate.
       (Contributed by Zhi Wang, 23-Oct-2025.) $)
    up1st2ndb $p |- ( ph -> ( X ( F ( D UP E ) W ) M
                             <-> X ( <. ( 1st ` F ) , ( 2nd ` F ) >.
                                     ( D UP E ) W ) M ) ) $=
      ( cup co wbr c1st cfv c2nd cop wa simpr up1st2nd cfunc wcel up1st2ndr
      adantr impbida ) AGEDFBCIJZJKZGEDLMDNMOFUDJKZAUEPBCDEFGAUEQRAUFPBCDEFGADB
      CSJTUFHUBAUFQUAUC $.
  $}

  ${
    up1st2nd2.1 $e |- ( ph -> X e. ( F ( D UP E ) W ) ) $.
    $( Rewrite the universal property predicate with separated parts.
       (Contributed by Zhi Wang, 23-Oct-2025.) $)
    up1st2nd2 $p |- ( ph -> ( 1st ` X ) ( F ( D UP E ) W ) ( 2nd ` X ) ) $=
      ( cup co wrel wcel c1st cfv c2nd wbr relup 1st2ndbr sylancr ) ADEBCHIIZJF
      SKFLMFNMSOBCDEPGFSQR $.
  $}

  ${
    $d B g k y $.  $d D g k y $.  $d E g k y $.  $d F g k y $.  $d G g k y $.
    $d J g k y $.  $d M g k y $.  $d W g k y $.  $d X g k y $.
    uprcl2.x $e |- ( ph -> X ( <. F , G >. ( D UP E ) W ) M ) $.
    $( Reverse closure for the class of universal property.  (Contributed by
       Zhi Wang, 25-Sep-2025.) $)
    uprcl2 $p |- ( ph -> F ( D Func E ) G ) $=
      ( cop cup co wbr wcel cfunc df-br biimpi cbs cfv eqid simpld biimpri 4syl
      uprcl ) AHFDEJZGBCKLLZMZHFJZUFNZUEBCOLZNZDEUJMZIUGUIHFUFPQUIUKGCRSZNUMBCU
      EGUHUMTUDUAULUKDEUJPUBUC $.

    ${
      uprcl3.c $e |- C = ( Base ` E ) $.
      $( Reverse closure for the class of universal property.  (Contributed by
         Zhi Wang, 25-Sep-2025.) $)
      uprcl3 $p |- ( ph -> W e. C ) $=
        ( cop cup co wbr wcel df-br biimpi cfunc uprcl simprd 3syl ) AIGEFLZHCD
        MNNZOZIGLZUDPZHBPZJUEUGIGUDQRUGUCCDSNPUHBCDUCHUFKTUAUB $.
    $}

    ${
      uprcl4.b $e |- B = ( Base ` D ) $.
      $( Reverse closure for the class of universal property.  (Contributed by
         Zhi Wang, 25-Sep-2025.) $)
      uprcl4 $p |- ( ph -> X e. B ) $=
        ( vg vk vy wcel cfv chom co cv eqid cop cco wceq wreu cup wbr wa uprcl3
        wral cbs uprcl2 isuplem mpbid simplld ) AIBOZGHIEPZDQPZROZLSMSINSZFRPGH
        UPUAUSEPZDUBPZRRUCMIUSCQPZRUDLHUTUQRUINBUIZAIGEFUAHCDUERRUFUOURUGVCUGJA
        NBDUJPZCLMDEFVBUQGVAHIKVDTZVBTUQTVATAVDCDEFGHIJVEUHACDEFGHIJUKULUMUN $.
    $}

    ${
      uprcl5.j $e |- J = ( Hom ` E ) $.
      $( Reverse closure for the class of universal property.  (Contributed by
         Zhi Wang, 25-Sep-2025.) $)
      uprcl5 $p |- ( ph -> M e. ( W J ( F ` X ) ) ) $=
        ( vg vk vy cbs cfv wcel co cv eqid cop cco wceq chom wreu cup wa uprcl3
        wral wbr uprcl2 isuplem mpbid simplrd ) AIBOPZQZGHIDPZFRQZLSMSINSZERPGH
        UQUAUSDPZCUBPZRRUCMIUSBUDPZRUELHUTFRUINUOUIZAIGDEUAHBCUFRRUJUPURUGVCUGJ
        ANUOCOPZBLMCDEVBFGVAHIUOTVDTZVBTKVATAVDBCDEGHIJVEUHABCDEGHIJUKULUMUN $.
    $}
  $}

  ${
    $d D m $.  $d E m $.  $d F m $.  $d W m $.  $d X m $.
    $( Reverse closure for universal object.  (Contributed by Zhi Wang,
       17-Nov-2025.) $)
    uobrcl $p |- ( X e. dom ( F ( D UP E ) W ) -> ( D e. Cat /\ E e. Cat ) ) $=
      ( vm cup co cdm wcel ccat c1st cfv c2nd cv wbr cfunc wex eldmg ibi uprcl2
      wa simpr up1st2nd exlimddv funcrcl2 funcrcl3 jca ) ECDABGHHZIZJZAKJBKJUKA
      BCLMZCNMZUKEFOZUIPZULUMABQHPFUKUOFRFEUIUJSTUKUOUBZABULUMUNDEUPABCUNDEUKUO
      UCUDUAUEZUFUKABULUMUQUGUH $.
  $}

  ${
    $d B g k y $.  $d D g k y $.  $d E g k y $.  $d F g k y $.  $d G g k y $.
    $d H g k y $.  $d J g k y $.  $d M g k y $.  $d O g k y $.  $d W g k y $.
    $d X g k y $.
    isup2.b $e |- B = ( Base ` D ) $.
    isup2.h $e |- H = ( Hom ` D ) $.
    isup2.j $e |- J = ( Hom ` E ) $.
    isup2.o $e |- O = ( comp ` E ) $.
    isup2.x $e |- ( ph -> X ( <. F , G >. ( D UP E ) W ) M ) $.
    $( The universal property of a universal pair.  (Contributed by Zhi Wang,
       24-Sep-2025.) $)
    isup2 $p |- ( ph -> A. y e. B A. g e. ( W J ( F ` y ) )
                E! k e. ( X H y ) g = ( ( ( X G y ) ` k )
                ( <. W , ( F ` X ) >. O ( F ` y ) ) M ) ) $=
      ( cop cup co wbr cv cfv wceq wreu wral cbs eqid uprcl3 uprcl2 uprcl4 isup
      uprcl5 mpbid ) AOLHIUANDGUBUCUCUDEUEFUEOBUEZIUCUFLNOHUFUAURHUFZMUCUCUGFOU
      RJUCUHENUSKUCUIBCUITABCGUJUFZDEFGHIJKLMNOPUTUKZQRSAUTDGHILNOTVAULADGHILNO
      TUMACDGHILNOTPUNADGHIKLNOTRUPUOUQ $.
  $}

  ${
    $d D f g k x y $.  $d D r $.  $d E f g k x y $.  $d E r $.
    $d F f g k x y $.  $d F r $.  $d G f g k x y $.  $d G r $.
    $d I f g k x y $.  $d K f g k x y $.  $d M f g k x y $.  $d M r $.
    $d N f g k x y $.  $d N r $.  $d W f g k x y $.  $d W r $.
    $d X f g k x y $.  $d X r $.  $d Y f g k x y $.  $d Y r $.
    $d ph f g k x y $.  $d ph r $.  $d .o. f g k x y $.
    upeu3.i $e |- ( ph -> I = ( Iso ` D ) ) $.
    upeu3.o $e |- ( ph ->
            .o. = ( <. W , ( F ` X ) >. ( comp ` E ) ( F ` Y ) ) ) $.
    upeu3.x $e |- ( ph -> X ( <. F , G >. ( D UP E ) W ) M ) $.
    ${
      upeu3.y $e |- ( ph -> Y ( <. F , G >. ( D UP E ) W ) N ) $.
      $( The universal pair ` <. X , M >. ` from object ` W ` to functor
         ` <. F , G >. ` is essentially unique (strong form) if it exists.
         (Contributed by Zhi Wang, 24-Sep-2025.) $)
      upeu3 $p |- ( ph ->
              E! r e. ( X I Y ) N = ( ( ( X G Y ) ` r ) .o. M ) ) $=
        ( co cfv eqid vy vg vk cv wceq wreu cop cco ciso cbs chom uprcl2 uprcl4
        uprcl3 uprcl5 isup2 upeu oveqd eqeq2d reueqbidv mpbird ) AHMUDJKERSZGLR
        ZUEZMJKFRZUFHVBGIJDSUGKDSCUHSZRZRZUEZMJKBUISZRZUFAUAUABUJSZCUJSZBUBUBUC
        CDEBUKSZCUKSZGHVFJKIMUCVLTZVMTZVNTZVOTZVFTZABCDEGIJPULAVLBCDEGIJPVPUMAV
        LBCDEHIKQVPUMAVMBCDEGIJPVQUNABCDEVOGIJPVSUOAUAVLBUBUCCDEVNVOGVFIJVPVRVS
        VTPUPABCDEVOHIKQVSUOAUAVLBUBUCCDEVNVOHVFIKVPVRVSVTQUPUQAVDVIMVEVKAFVJJK
        NURAVCVHHALVGVBGOURUSUTVA $.
    $}

    ${
      upeu4.k $e |- ( ph -> K e. ( X I Y ) ) $.
      upeu4.n $e |- ( ph -> N = ( ( ( X G Y ) ` K ) .o. M ) ) $.
      $( Generate a new universal morphism through an isomorphism from an
         existing universal object, and pair with the codomain of the
         isomorphism to form a universal pair.  (Contributed by Zhi Wang,
         25-Sep-2025.) $)
      upeu4 $p |- ( ph -> Y ( <. F , G >. ( D UP E ) W ) N ) $=
        ( co cfv vg vk vy vx vf cop cup wbr cv cco wceq chom wreu wral cbs wcel
        ciso eqid uprcl2 uprcl4 cmpo cxp ccat funcrcl2 isofn fneq1d mpbird fnov
        wfn sylib oveqd eleqtrd elmpocl2 uprcl3 uprcl5 isup2 eqtrd upeu2 simprd
        syl simpld isup ) ALIDEUFJBCUGSSUHUAUIUBUILUCUIZESTIJLDTZUFWCDTZCUJTZSS
        UKUBLWCBULTZSUMUAJWECULTZSUNUCBUOTZUNZAIJWDWHSUPZWJAUDUCWICUOTZBUEUAUBC
        DEWGBUQTZWHGHIWFKLJUBWIURZWLURZWGURZWHURZWFURZABCDEHJKPUSZAWIBCDEHJKPWN
        UTAGKLUDUCWIWIUDUIWCFSZVAZSZUPLWIUPAGKLFSZXBQAFXAKLAFWIWIVBZVIZFXAUKAXE
        WMXDVIZABVCUPXFABCDEWSVDBVEVTAXDFWMNVFVGUDUCWIWIFVHVJVKVLUDUCWIWIWTKLXA
        GXAURVMVTZAWLBCDEHJKPWOVNZABCDEWHHJKPWQVOAUDWIBUEUBCDEWGWHHWFJKWNWPWQWR
        PVPWMURAGXCKLWMSQAFWMKLNVKVLAIGKLESTZHMSXIHJKDTUFWDWFSZSRAMXJXIHOVKVQVR
        ZVSAUCWIWLBUAUBCDEWGWHIWFJLWNWOWPWQWRXHWSXGAWKWJXKWAWBVG $.
    $}
  $}

  ${
    oppcuprcl2.x $e |- ( ph -> X ( <. F , G >. ( O UP P ) W ) M ) $.
    ${
      uptpos.h $e |- ( ph -> tpos G = H ) $.
      $( Lemma for ~ uptpos .  (Contributed by Zhi Wang, 4-Nov-2025.) $)
      uptposlem $p |- ( ph -> tpos H = G ) $=
        ( ctpos tposeqd wrel cdm wceq cbs cfv cxp wfn eqid uprcl2 funcfn2 fnrel
        syl relxp fndmd releqd mpbiri tpostpos2 syl2anc eqtr3d ) ADLZLZELDAUMEK
        MADNZDOZNZUNDPADGQRZURSZTUOAURGBCDURUAAGBCDFHIJUBUCZUSDUDUEAUQUSNURURUF
        AUPUSAUSDUTUGUHUIDUJUKUL $.

      $( Rewrite the predicate of universal property in the form of opposite
         functor.  (Contributed by Zhi Wang, 4-Nov-2025.) $)
      uptpos $p |- ( ph -> X ( <. F , tpos H >. ( O UP P ) W ) M ) $=
        ( ctpos cop cup co wbr uptposlem opeq2d oveq1d breqd mpbird ) AIFCELZMZ
        HGBNOZOZPIFCDMZHUDOZPJAUEUGIFAUCUFHUDAUBDCABCDEFGHIJKQRSTUA $.
    $}

    ${
      oppcuprcl4.o $e |- O = ( oppCat ` D ) $.
      oppcuprcl4.b $e |- B = ( Base ` D ) $.
      $( Reverse closure for the class of universal property in opposite
         categories.  (Contributed by Zhi Wang, 4-Nov-2025.) $)
      oppcuprcl4 $p |- ( ph -> X e. B ) $=
        ( oppcbas uprcl4 ) ABHDEFGIJKBCHLMNO $.
    $}

    oppcuprcl2.p $e |- P = ( oppCat ` E ) $.
    ${
      oppcuprcl3.c $e |- C = ( Base ` E ) $.
      $( Reverse closure for the class of universal property in opposite
         categories.  (Contributed by Zhi Wang, 4-Nov-2025.) $)
      oppcuprcl3 $p |- ( ph -> W e. C ) $=
        ( oppcbas uprcl3 ) ABHCEFGIJKBDCLMNO $.
    $}

    ${
      oppcuprcl5.j $e |- J = ( Hom ` E ) $.
      $( Reverse closure for the class of universal property in opposite
         categories.  (Contributed by Zhi Wang, 4-Nov-2025.) $)
      oppcuprcl5 $p |- ( ph -> M e. ( ( F ` X ) J W ) ) $=
        ( cfv chom co eqid uprcl5 oppchom eleqtrdi ) AGIJDNZBONZPUAIFPAHBDEUBGI
        JKUBQRCFBIUAMLST $.
    $}

    oppcuprcl2.o $e |- O = ( oppCat ` D ) $.
    oppcuprcl2.d $e |- ( ph -> D e. U ) $.
    oppcuprcl2.e $e |- ( ph -> E e. V ) $.
    oppcuprcl2.h $e |- ( ph -> tpos G = H ) $.
    $( Reverse closure for the class of universal property in opposite
       categories.  (Contributed by Zhi Wang, 4-Nov-2025.) $)
    oppcuprcl2 $p |- ( ph -> F ( D Func E ) H ) $=
      ( ctpos cfunc co uprcl2 funcoppc2 breqtrd ) AFGTHBEUAUBABECFGJDKPOQRAJCFG
      ILMNUCUDSUE $.
  $}

  ${
    uprcl2a.x $e |- ( ph -> X ( G ( O UP P ) W ) M ) $.
    $( Reverse closure for the class of universal property.  (Contributed by
       Zhi Wang, 14-Nov-2025.) $)
    uprcl2a $p |- ( ph -> G e. ( O Func P ) ) $=
      ( cfunc co wcel cbs cfv cop cup wa wbr df-br sylib eqid uprcl syl simpld
      ) ACEBIJKZFBLMZKZAGDNZCFEBOJJZKZUDUFPAGDUHQUIHGDUHRSUEEBCFUGUETUAUBUC $.

    oppfuprcl.g $e |- G = ( oppFunc ` F ) $.
    oppfuprcl.o $e |- O = ( oppCat ` D ) $.
    oppfuprcl.p $e |- P = ( oppCat ` E ) $.
    oppfuprcl.d $e |- ( ph -> D e. U ) $.
    oppfuprcl.e $e |- ( ph -> E e. V ) $.
    $( Reverse closure for the class of universal property for opposite
       functors.  (Contributed by Zhi Wang, 14-Nov-2025.) $)
    oppfuprcl $p |- ( ph -> F e. ( D Func E ) ) $=
      ( coppf cfv cfunc co uprcl2a eqeltrrid funcoppc5 ) ABECFIDJOPQRAFSTGICUAU
      BNACGHIKLMUCUDUE $.

    oppfuprcl2.f $e |- ( ph -> F = <. A , B >. ) $.
    $( Reverse closure for the class of universal property for opposite
       functors.  (Contributed by Zhi Wang, 14-Nov-2025.) $)
    oppfuprcl2 $p |- ( ph -> A ( D Func E ) B ) $=
      ( cop cfunc co wcel wbr oppfuprcl eqeltrrd df-br sylibr ) ABCUBZDGUCUDZUE
      BCULUFAHUKULUAADEFGHIJKLMNOPQRSTUGUHBCULUIUJ $.
  $}

  ${
    $d B y $.  $d F k m $.  $d F l m $.  $d F k n y $.  $d G k m $.
    $d G l m $.  $d G k n y $.  $d H k m $.  $d H l m $.  $d H k n y $.
    $d J n y $.  $d M k m $.  $d M l m $.  $d M k n y $.  $d N k m $.
    $d N l m $.  $d N k n $.  $d O k m $.  $d O l m $.  $d O k n y $.
    $d X k m $.  $d X l m $.  $d X k n y $.  $d Y k m $.  $d Y l m $.
    $d Y k n y $.  $d Z k m $.  $d Z l m $.  $d Z k n y $.
    oppcup3lem.1 $e |- ( ph -> A. y e. B A. n e. ( ( F ` y ) J Z )
           E! k e. ( y H X )
           n = ( M ( <. ( F ` y ) , ( F ` X ) >. O Z ) ( ( y G X ) ` k ) ) ) $.
    oppcup3lem.y $e |- ( ph -> Y e. B ) $.
    oppcup3lem.n $e |- ( ph -> N e. ( ( F ` Y ) J Z ) ) $.
    $( Lemma for ~ oppcup3 .  (Contributed by Zhi Wang, 4-Nov-2025.) $)
    oppcup3lem $p |- ( ph -> E! l e. ( Y H X ) N =
               ( M ( <. ( F ` Y ) , ( F ` X ) >. O Z ) ( ( Y G X ) ` l ) ) ) $=
      ( co vm cv cfv cop wceq wreu eqeq1 reubidv wral fveq2 oveq1d oveq1 opeq1d
      eqidd fveq1d oveq123d eqeq2d reueqbidv raleqbidv rspcdva oveq2d cbvreuvw
      bitri sylib ) AKJDUBZNMGTZUCZNFUCZMFUCZUDZOLTZTZUEZDNMHTZUFZKJPUBZVFUCZVK
      TZUEZPVNUFZAEUBZVLUEZDVNUFZVOEVHOITZKWAKUEWBVMDVNWAKVLUGUHAWAJVEBUBZMGTZU
      CZWEFUCZVIUDZOLTZTZUEZDWEMHTZUFZEWHOITZUIWCEWDUIBCNWENUEZWNWCEWOWDWPWHVHO
      IWENFUJZUKWPWLWBDWMVNWENMHULWPWKVLWAWPJJWGVGWJVKWPWIVJOLWPWHVHVIWQUMUKWPJ
      UNWPVEWFVFWENMGULUOUPUQURUSQRUTSUTVOKJUAUBZVFUCZVKTZUEZUAVNUFVTVMXADUAVNV
      EWRUEZVLWTKXBVGWSJVKVEWRVFUJVAUQVBXAVSUAPVNWRVPUEZWTVRKXCWSVQJVKWRVPVFUJV
      AUQVBVCVD $.
  $}

  ${
    $d B g k y $.  $d C g k y $.  $d F g k y $.  $d G g k y $.  $d H k $.
    $d M g k y $.  $d O g k y $.  $d P g k y $.  $d W g k y $.  $d X g k y $.
    $d g k ph y $.
    oppcup.b $e |- B = ( Base ` D ) $.
    oppcup.c $e |- C = ( Base ` E ) $.
    oppcup.h $e |- H = ( Hom ` D ) $.
    oppcup.j $e |- J = ( Hom ` E ) $.
    oppcup.xb $e |- .xb = ( comp ` E ) $.
    oppcup.w $e |- ( ph -> W e. C ) $.
    oppcup.f $e |- ( ph -> F ( D Func E ) G ) $.
    oppcup.x $e |- ( ph -> X e. B ) $.
    oppcup.m $e |- ( ph -> M e. ( ( F ` X ) J W ) ) $.
    oppcup.o $e |- O = ( oppCat ` D ) $.
    oppcup.p $e |- P = ( oppCat ` E ) $.
    $( The universal pair ` <. X , M >. ` from a functor to an object is
       universal from an object to a functor in the opposite category.
       (Contributed by Zhi Wang, 24-Sep-2025.) $)
    oppcup $p |- ( ph -> ( X ( <. F , tpos G >. ( O UP P ) W ) M <->
       A. y e. B A. g e. ( ( F ` y ) J W ) E! k e. ( y H X )
       g = ( M ( <. ( F ` y ) , ( F ` X ) >. .xb W ) ( ( y G X ) ` k ) ) ) ) $=
      ( ctpos cop cup co wbr cv cfv cco wceq chom wreu oppcbas funcoppc oppchom
      wral eqid eleqtrrdi isup wcel wa ovtpos fveq1i oveq1i adantr cfunc funcf1
      ffvelcdmd simpr oppcco eqtrid eqeq2d reueqbidv raleqbidv ralbidva bitrd
      a1i ) AROKLUJZUKQPFULUMUMUNHUOZIUOZRBUOZWFUMZUPZOQRKUPZUKWIKUPZFUQUPZUMZU
      MZURZIRWIPUSUPZUMZUTZHQWMFUSUPZUMZVDZBCVDWGOWHWIRLUMZUPZWMWLUKQGUMUMZURZI
      WIRMUMZUTZHWMQNUMZVDZBCVDABCDPHIFKWFWRXAOWNQRCEPUHSVADJFUITVAWRVEXAVEWNVE
      UDAEJFKLPUHUIUEVBUFAOWLQNUMQWLXAUMUGJNFQWLUBUIVCVFVGAXCXKBCAWICVHZVIZWTXI
      HXBXJXBXJURXMJNFQWMUBUIVCWEXMWQXGIWSXHWSXHURXMEMPRWIUAUHVCWEXMWPXFWGXMWPX
      EOWOUMXFWKXEOWOWHWJXDRWILVJVKVLXMDJGOXEFQWLWMTUCUIAQDVHXLUDVMXMCDRKXMCDEJ
      KLSTAKLEJVNUMUNXLUEVMVOZARCVHXLUFVMVPXMCDWIKXNAXLVQVPVRVSVTWAWBWCWD $.
  $}

  ${
    $d B g k y $.  $d E g k y $.  $d F g k y $.  $d G g k y $.  $d H k $.
    $d M g k y $.  $d O g k y $.  $d P g k y $.  $d W g k y $.  $d X g k y $.
    $d g k ph y $.
    oppcup2.b $e |- B = ( Base ` D ) $.
    oppcup2.h $e |- H = ( Hom ` D ) $.
    oppcup2.j $e |- J = ( Hom ` E ) $.
    oppcup2.xb $e |- .xb = ( comp ` E ) $.
    oppcup2.o $e |- O = ( oppCat ` D ) $.
    oppcup2.p $e |- P = ( oppCat ` E ) $.
    oppcup2.f $e |- ( ph -> F ( D Func E ) G ) $.
    oppcup2.x $e |- ( ph -> X ( <. F , tpos G >. ( O UP P ) W ) M ) $.
    $( The universal property for the universal pair ` <. X , M >. ` from a
       functor to an object, expressed explicitly.  (Contributed by Zhi Wang,
       4-Nov-2025.) $)
    oppcup2 $p |- ( ph -> A. y e. B A. g e. ( ( F ` y ) J W ) E! k e. ( y H X )
       g = ( M ( <. ( F ` y ) , ( F ` X ) >. .xb W ) ( ( y G X ) ` k ) ) ) $=
      ( ctpos cop cup co wbr cv wceq wreu wral oppcuprcl3 oppcuprcl4 oppcuprcl5
      cfv cbs eqid oppcup mpbid ) AQNJKUFZUGPOEUHUIUIUJGUKNHUKBUKZQKUIURVDJURZQ
      JURUGPFUIUIULHVDQLUIUMGVEPMUIUNBCUNUEABCIUSURZDEFGHIJKLMNOPQRVFUTZSTUAAVF
      EIJVCNOPQUEUCVGUOUDACDEJVCNOPQUEUBRUPAEIJVCMNOPQUEUCTUQUBUCVAVB $.
  $}

  ${
    $d .xb g k y $.  $d B g k y $.  $d E g k y $.  $d F g k y $.  $d G g k y $.
    $d H g k y $.  $d J g y $.  $d M g k y $.  $d N g k $.  $d O g k y $.
    $d P g k y $.  $d W g k y $.  $d X g k y $.  $d Y g k y $.  $d g k ph y $.
    oppcup3.b $e |- B = ( Base ` D ) $.
    oppcup3.h $e |- H = ( Hom ` D ) $.
    oppcup3.j $e |- J = ( Hom ` E ) $.
    oppcup3.xb $e |- .xb = ( comp ` E ) $.
    oppcup3.o $e |- O = ( oppCat ` D ) $.
    oppcup3.p $e |- P = ( oppCat ` E ) $.
    oppcup3.x $e |- ( ph -> X ( <. F , T >. ( O UP P ) W ) M ) $.
    oppcup3.g $e |- ( ph -> tpos T = G ) $.
    oppcup3.y $e |- ( ph -> Y e. B ) $.
    oppcup3.n $e |- ( ph -> N e. ( ( F ` Y ) J W ) ) $.
    $( The universal property for the universal pair ` <. X , M >. ` from a
       functor to an object, expressed explicitly.  (Contributed by Zhi Wang,
       4-Nov-2025.) $)
    oppcup3 $p |- ( ph -> E! k e. ( Y H X )
       N = ( M ( <. ( F ` Y ) , ( F ` X ) >. .xb W ) ( ( Y G X ) ` k ) ) ) $=
      ( vy vg cvv cbs cfv eleqtrdi elfvexd co c0 wcel ne0d wn chom fvprc eqtrid
      wne oveqd 0ov eqtrdi necon1ai syl oppcuprcl2 uptpos oppcup2 oppcup3lem )
      AUIBGUJIJKLMNEQRPGAUIBCDEUJGHIJKLMOPQSTUAUBUCUDACDUKHIFJMOUKPQUEUDUCARULC
      ARBCULUMUGSUNUOARIUMZPLUPZUQVDHUKURZAVONUHUSVPVOUQVPUTZVOVNPUQUPUQVQLUQVN
      PVQLHVAUMUQUAHVAVBVCVEVNPVFVGVHVIUFVJADIFJMOPQUEUFVKVLUGUHVM $.
  $}

  ${
    uptrlem1.h $e |- H = ( Hom ` C ) $.
    uptrlem1.i $e |- I = ( Hom ` D ) $.
    uptrlem1.j $e |- J = ( Hom ` E ) $.
    uptrlem1.d $e |- .xb = ( comp ` D ) $.
    uptrlem1.e $e |- .o. = ( comp ` E ) $.
    ${
      $d .o. g $.  $d .xb h $.  $d A h $.  $d B g $.  $d F g h k $.  $d G h $.
      $d H g h $.  $d I g h k $.  $d J g h $.  $d K g h $.  $d L g $.
      $d N g h k $.  $d W g h k $.  $d X g h k $.  $d Y g h $.  $d Z g h $.
      $d g h k ph $.
      uptrlem1.x $e |- ( ph -> X e. ( Base ` D ) ) $.
      uptrlem1.y $e |- ( ph -> ( M ` X ) = Y ) $.
      uptrlem1.z $e |- ( ph -> Z e. ( Base ` C ) ) $.
      uptrlem1.w $e |- ( ph -> W e. ( Base ` C ) ) $.
      uptrlem1.a $e |- ( ph -> A e. ( X I ( F ` Z ) ) ) $.
      uptrlem1.b $e |- ( ph -> ( ( X N ( F ` Z ) ) ` A ) = B ) $.
      uptrlem1.f $e |- ( ph -> F ( C Func D ) G ) $.
      uptrlem1.m $e |- ( ph -> M ( ( D Full E ) i^i ( D Faith E ) ) N ) $.
      uptrlem1.k $e |- ( ph -> ( <. M , N >. o.func <. F , G >. )
                             = <. K , L >. ) $.
      $( Lemma for ~ uptr .  (Contributed by Zhi Wang, 16-Nov-2025.) $)
      uptrlem1 $p |- ( ph -> ( A. h e. ( Y J ( K ` W ) ) E! k e. ( Z H W )
       h = ( ( ( Z L W ) ` k ) ( <. Y , ( K ` Z ) >. .o. ( K ` W ) ) B )
       <-> A. g e. ( X I ( F ` W ) ) E! k e. ( Z H W )
       g = ( ( ( Z G W ) ` k ) ( <. X , ( F ` Z ) >. .xb ( F ` W ) ) A ) ) ) $=
        ( cv cfv cop wceq wreu wf1o cbs eqid funcf1 ffvelcdmd ffthf1o cful cfth
        co wf cin wbr cfunc inss1 fullfunc sstri ssbri syl cofu1a oveq12d mpbid
        f1oeq3d f1of ffvelcdmda wfo wcel wrex f1ofo foelrn w3a wa simpl3 eqeq1d
        sylan ad2antrr funcf2 adantr funcco opeq12d ccofu simpr cofu2a oveq123d
        eqtrd eqeq2d wf1 f1of1 simplr funcrcl2 catcocl f1fveq syl12anc 3adantl3
        wb bitr3d bitrd reubidva ralxfrd2 ) AHUSZIUSZUDTQVLUTZCUBUDPUTZVAZTPUTZ
        UCVLZVLZVBZIUDTMVLZVCGUSZYCUDTLVLZUTZBUAUDKUTZVATKUTZFVLVLZVBZIYKVCHGYL
        UAYPSVLZUTZUBYGOVLZUAYPNVLZAUUBUUAYLYSAUUBUUAYSVDZUUBUUAYSVMAUUBUARUTZY
        PRUTZOVLZYSVDUUCAEVEUTZEJRSNOUAYPUUGVFZUFUGUQUJADVEUTZUUGTKAUUIUUGDEKLU
        UIVFZUUHUPVGZUMVHZVIAUUFUUAUUBYSAUUDUBUUEYGOUKAUUIDEJKLRSPQTUUJUPARSEJV
        JVLZEJVKVLZVNZVORSEJVPVLZVOZUQUUOUUPRSUUOUUMUUPUUMUUNVQEJVRVSVTWAZURUMW
        BZWCWEWDZUUBUUAYSWFWAWGAUUBUUAYSWHZYBUUAWIYBYTVBZGUUBWJAUUCUVAUUTUUBUUA
        YSWKWAGUUBUUAYBYSWLWQAYLUUBWIZUVBWMZYJYRIYKUVDYCYKWIZWNZYJYTYIVBZYRUVFY
        BYTYIAUVCUVBUVEWOWPAUVCUVEUVGYRXQUVBAUVCWNZUVEWNZYTYQYSUTZVBZUVGYRUVIUV
        JYIYTUVIUVJYNYOYPSVLUTZBUAYOSVLUTZUUDYORUTZVAZUUEUCVLZVLYIUVIUUGEFJRSNB
        YNUCUAYOYPUUHUFUHUIAUUQUVCUVEUURWRZAUAUUGWIUVCUVEUJWRZAYOUUGWIUVCUVEAUU
        IUUGUDKUUKULVHWRZAYPUUGWIUVCUVEUULWRZABUAYONVLWIUVCUVEUNWRZUVHYKYOYPNVL
        ZYCYMAYKUWBYMVMUVCAUUIDEKLMNUDTUUJUEUFUPULUMWSWTWGZXAUVIUVLYDUVMCUVPYHU
        VIUVOYFUUEYGUCUVIUUDUBUVNYEAUUDUBVBUVCUVEUKWRAUVNYEVBUVCUVEAUUIDEJKLRSP
        QUDUUJUPUURURULWBWRXBAUUEYGVBUVCUVEUUSWRWCUVIUUIDEYCJKLMRSPQUDTUUJAKLDE
        VPVLVOUVCUVEUPWRUVQARSVAKLVAXCVLPQVAVBUVCUVEURWRAUDUUIWIUVCUVEULWRATUUI
        WIUVCUVEUMWRUEUVHUVEXDXEAUVMCVBUVCUVEUOWRXFXGXHUVIUUBUUAYSXIZUVCYQUUBWI
        UVKYRXQAUWDUVCUVEAUUCUWDUUTUUBUUAYSXJWAWRAUVCUVEXKUVIUUGEFBYNNUAYOYPUUH
        UFUHUVIEJRSUVQXLUVRUVSUVTUWAUWCXMUUBUUAYLYQYSXNXOXRXPXSXTYA $.
    $}

    ${
      $d .o. g $.  $d .xb h $.  $d F g h k $.  $d G g h $.  $d H g h $.
      $d I g h k $.  $d J g h $.  $d K g h k $.  $d M h $.  $d N g $.
      $d W g h k $.  $d X g h k $.  $d Y g h $.  $d Z g h $.  $d g h k ph $.
      uptrlem2.a $e |- A = ( Base ` C ) $.
      uptrlem2.b $e |- B = ( Base ` D ) $.
      uptrlem2.x $e |- ( ph -> X e. B ) $.
      uptrlem2.y $e |- ( ph -> ( ( 1st ` K ) ` X ) = Y ) $.
      uptrlem2.z $e |- ( ph -> Z e. A ) $.
      uptrlem2.w $e |- ( ph -> W e. A ) $.
      uptrlem2.m $e |- ( ph -> M e. ( X I ( ( 1st ` F ) ` Z ) ) ) $.
      uptrlem2.n $e |- ( ph -> ( ( X ( 2nd ` K ) ( ( 1st ` F ) ` Z ) ) ` M )
                             = N ) $.
      uptrlem2.f $e |- ( ph -> F e. ( C Func D ) ) $.
      uptrlem2.k $e |- ( ph -> K e. ( ( D Full E ) i^i ( D Faith E ) ) ) $.
      uptrlem2.g $e |- ( ph -> ( K o.func F ) = G ) $.
      $( Lemma for ~ uptr .  (Contributed by Zhi Wang, 16-Nov-2025.) $)
      uptrlem2 $p |- ( ph -> ( A. h e. ( Y J ( ( 1st ` G ) ` W ) )
       E! k e. ( Z H W ) h = ( ( ( Z ( 2nd ` G ) W ) ` k )
        ( <. Y , ( ( 1st ` G ) ` Z ) >. .o. ( ( 1st ` G ) ` W ) ) N )
      <-> A. g e. ( X I ( ( 1st ` F ) ` W ) )
       E! k e. ( Z H W ) g = ( ( ( Z ( 2nd ` F ) W ) ` k )
        ( <. X , ( ( 1st ` F ) ` Z ) >. .xb ( ( 1st ` F ) ` W ) ) M ) ) ) $=
        ( c1st cfv c2nd cbs eleqtrdi func1st2nd cop cful cfth cin wcel wbr wrel
        co wceq relfull relin1 ax-mp 1st2nd sylancr eqeltrrd df-br sylibr ccofu
        cfunc inss1 fullfunc sselid cofu1st2nd relfunc cofucl 3eqtr3d uptrlem1
        sstri ) AQRDEFGHIJKUTVAZKVBVAZMNOLUTVAZLVBVAZPUTVAZPVBVAZSTUAUBUCUDUEUF
        UGUHATCEVCVAUKUJVDULAUCBDVCVAZUMUIVDASBWTUNUIVDUOUPADEKUQVEAWRWSVFZEJVG
        VMZEJVHVMZVIZVJWRWSXDVKAPXAXDAXDVLZPXDVJPXAVNXBVLXEEJVOXBXCVPVQURPXDVRV
        SURVTWRWSXDWAWBAPKWCVMZLXAWNWOVFWCVMWPWQVFZUSADEJKPUQAXDEJWDVMZPXDXBXHX
        BXCWEEJWFWMURWGZWHADJWDVMZVLLXJVJLXGVNDJWIAXFLXJUSADEJKPUQXIWJVTLXJVRVS
        WKWL $.
    $}
  $}

  ${
    $d A g h k y $.  $d B g h k y $.  $d C g h k y $.  $d D g h k y $.
    $d E g h k y $.  $d F g h k y $.  $d G g h k y $.  $d J g h k y $.
    $d K g h k y $.  $d L g h k y $.  $d M g h k y $.  $d N g h k y $.
    $d R g h k y $.  $d S g h k y $.  $d X g h k y $.  $d Y g h k y $.
    $d Z g h k y $.  $d g h k ph y $.
    uptr.y $e |- ( ph -> ( R ` X ) = Y ) $.
    uptr.r $e |- ( ph -> R ( ( D Full E ) i^i ( D Faith E ) ) S ) $.
    uptr.k $e |- ( ph -> ( <. R , S >. o.func <. F , G >. ) = <. K , L >. ) $.
    ${
      uptr.b $e |- B = ( Base ` D ) $.
      uptr.x $e |- ( ph -> X e. B ) $.
      uptr.f $e |- ( ph -> F ( C Func D ) G ) $.
      uptr.n $e |- ( ph -> ( ( X S ( F ` Z ) ) ` M ) = N ) $.
      uptr.j $e |- J = ( Hom ` D ) $.
      uptr.m $e |- ( ph -> M e. ( X J ( F ` Z ) ) ) $.
      ${
        uptrlem3.a $e |- A = ( Base ` C ) $.
        uptrlem3.z $e |- ( ph -> Z e. A ) $.
        $( Lemma for ~ uptr .  (Contributed by Zhi Wang, 16-Nov-2025.) $)
        uptrlem3 $p |- ( ph -> ( Z ( <. F , G >. ( C UP D ) X ) M
                           <-> Z ( <. K , L >. ( C UP E ) Y ) N ) ) $=
          ( vh vk vy vg cv co cfv cop cco wceq chom wreu wral cup wbr wcel eqid
          cbs eleqtrdi adantr simpr cfunc cful cfth cin ccofu uptrlem1 ralbidva
          wa inss1 fullfunc sstri ssbri funcf1 ffvelcdmd eqeltrrd cofucla df-br
          syl sylibr funcf2 cofu1a oveq12d 3eltr3d isup 3bitr4rd ) AUJUNUKUNZRU
          LUNZMUOUPOQRLUPZUQWQLUPZHURUPZUOUOUSUKRWQDUTUPZUOZVAUJQWSHUTUPZUOVBZU
          LBVBUMUNWPRWQJUOUPNPRIUPZUQWQIUPZEURUPZUOUOUSUKXBVAUMPXFKUOVBZULBVBRO
          LMUQZQDHVCUOUOVDRNIJUQZPDEVCUOUOVDAXDXHULBAWQBVEZVRZNODEXGUMUJUKHIJXA
          KXCLMFGWQPQWTRXAVFZUFXCVFZXGVFZWTVFZAPEVGUPZVEXKAPCXQUCUBVHVIAPFUPZQU
          SXKSVIARDVGUPZVEXKARBXSUIUHVHVIXLWQBXSAXKVJUHVHANPXEKUOZVEXKUGVIANPXE
          GUOZUPZOUSXKUEVIAIJDEVKUOVDXKUDVIAFGEHVLUOZEHVMUOZVNZVDZXKTVIAFGUQXJV
          OUOZXIUSXKUAVIVPVQAULBHVGUPZDUJUKHLMXAXCOWTQRUHYHVFZXMXNXPAXRQYHSACYH
          PFACYHEHFGUBYIAYFFGEHVKUOZVDTYEYJFGYEYCYJYCYDVSEHVTWAWBWHZWCUCWDWEAXI
          DHVKUOZVELMYLVDAYGXIYLUAADEHIJFGUDYKWFWELMYLWGWIUIAYBXRXEFUPZXCUOZOQW
          RXCUOAXTYNNYAACEHFGKXCPXEUBUFXNYKUCABCRIABCDEIJUHUBUDWCUIWDWJUGWDUEAX
          RQYMWRXCSABDEHIJFGLMRUHUDYKUAUIWKWLWMWNAULBCDUMUKEIJXAKNXGPRUHUBXMUFX
          OUCUDUIUGWNWO $.
      $}

      $( Universal property and fully faithful functor.  (Contributed by Zhi
         Wang, 16-Nov-2025.) $)
      uptr $p |- ( ph -> ( Z ( <. F , G >. ( C UP D ) X ) M
                     <-> Z ( <. K , L >. ( C UP E ) Y ) N ) ) $=
        ( cop cup co wbr simpr wa cbs cfv wceq adantr cful cfth cin ccofu cfunc
        wcel eqid uprcl4 uptrlem3 mpbird bibiad ) AQMHIUGZOCDUHUIUIUJZQNKLUGZPC
        GUHUIUIUJZVIAVIUKZAVKULZVIVKAVKUKZVMCUMUNZBCDEFGHIJKLMNOPQAOEUNPUOZVKRU
        PAEFDGUQUIDGURUIUSUJZVKSUPAEFUGVHUTUIVJUOZVKTUPUAAOBVBZVKUBUPAHICDVAUIU
        JZVKUCUPAMOQHUNZFUIUNNUOZVKUDUPUEAMOWAJUIVBZVKUFUPVOVCZVMVOCGKLNPQVNWDV
        DVEVFAVIULZVOBCDEFGHIJKLMNOPQAVPVIRUPAVQVISUPAVRVITUPUAAVSVIUBUPAVTVIUC
        UPAWBVIUDUPUEAWCVIUFUPWDWEVOCDHIMOQVLWDVDVEVG $.
    $}

    uptri.n $e |- ( ph -> ( ( X S ( F ` Z ) ) ` M ) = N ) $.
    uptri.z $e |- ( ph -> Z ( <. F , G >. ( C UP D ) X ) M ) $.
    $( Universal property and fully faithful functor.  (Contributed by Zhi
       Wang, 16-Nov-2025.) $)
    uptri $p |- ( ph -> Z ( <. K , L >. ( C UP E ) Y ) N ) $=
      ( cop cup co wbr wb wa cbs cfv chom wceq adantr cful cfth cin eqid uprcl3
      ccofu uprcl2 uprcl5 uptr mpdan mpbid ) AOKGHUAZMBCUBUCUCUDZOLIJUAZNBFUBUC
      UCUDZTAVDVDVFUETAVDUFZCUGUHZBCDEFGHCUIUHZIJKLMNOAMDUHNUJVDPUKADECFULUCCFU
      MUCUNUDVDQUKADEUAVCUQUCVEUJVDRUKVHUOZVGVHBCGHKMOAVDVDTUKZVJUPVGBCGHKMOVKU
      RAKMOGUHEUCUHLUJVDSUKVIUOZVGBCGHVIKMOVKVLUSUTVAVB $.
  $}

  ${
    uptra.y $e |- ( ph -> ( ( 1st ` K ) ` X ) = Y ) $.
    uptra.k $e |- ( ph -> K e. ( ( D Full E ) i^i ( D Faith E ) ) ) $.
    uptra.g $e |- ( ph -> ( K o.func F ) = G ) $.
    ${
      uptra.b $e |- B = ( Base ` D ) $.
      uptra.x $e |- ( ph -> X e. B ) $.
      uptra.f $e |- ( ph -> F e. ( C Func D ) ) $.
      ${
        uptra.n $e |- ( ph ->
            ( ( X ( 2nd ` K ) ( ( 1st ` F ) ` Z ) ) ` M ) = N ) $.
        uptra.j $e |- J = ( Hom ` D ) $.
        uptra.m $e |- ( ph -> M e. ( X J ( ( 1st ` F ) ` Z ) ) ) $.
        $( Universal property and fully faithful functor.  (Contributed by Zhi
           Wang, 16-Nov-2025.) $)
        uptra $p |- ( ph -> ( Z ( F ( C UP D ) X ) M
                      <-> Z ( G ( C UP E ) Y ) N ) ) $=
          ( c1st cfv c2nd cop cup co wbr cful cfth cin wrel wcel relfull relin1
          ax-mp 1st2ndbr sylancr ccofu cfunc inss1 sstri sselid cofu1st2nd wceq
          fullfunc relfunc cofucl eqeltrrd 3eqtr3d func1st2nd up1st2ndb 3bitr4d
          1st2nd uptr ) ANJFUDUEZFUFUEZUGZLCDUHUIZUIUJNKGUDUEZGUFUEZUGZMCEUHUIZ
          UIUJNJFLWAUIUJNKGMWEUIUJABCDIUDUEZIUFUEZEVRVSHWBWCJKLMNOADEUKUIZDEULU
          IZUMZUNZIWJUOWFWGWJUJWHUNWKDEUPWHWIUQURPIWJUSUTAIFVAUIZGWFWGUGVTVAUIW
          DQACDEFITAWJDEVBUIZIWJWHWMWHWIVCDEVHVDPVEZVFACEVBUIZUNGWOUOGWDVGCEVIA
          WLGWOQACDEFITWNVJVKZGWOVPUTVLRSACDFTVMUAUBUCVQACDFJLNTVNACEGKMNWPVNVO
          $.
      $}

      uptrar.m $e |- ( ph ->
            ( `' ( X ( 2nd ` K ) ( ( 1st ` F ) ` Z ) ) ` N ) = M ) $.
      uptrar.z $e |- ( ph -> Z ( G ( C UP E ) Y ) N ) $.
      $( Universal property and fully faithful functor.  (Contributed by Zhi
         Wang, 17-Nov-2025.) $)
      uptrar $p |- ( ph -> Z ( F ( C UP D ) X ) M ) $=
        ( cup co wbr wb wa chom cfv c1st wceq adantr cful cfth wcel ccofu cfunc
        cin c2nd ccnv fveq2d wf1o eqid wrel relfull relin1 1st2ndbr sylancr cbs
        ax-mp func1st2nd funcf1 simpr up1st2nd ffvelcdmd ffthf1o inss1 fullfunc
        uprcl4 sstri sselid cofu1 fveq1d eqtr3d oveq12d f1oeq3d mpbid f1ocnvfv2
        uprcl5 syl2anc f1ocnvdm eqeltrrd uptra mpdan mpbird ) AMIFKCDUBUCUCUDZM
        JGLCEUBUCUCUDZUAAWPWOWPUEUAAWPUFZBCDEFGDUGUHZHIJKLMAKHUIUHZUHZLUJWPNUKZ
        AHDEULUCZDEUMUCZUQZUNZWPOUKAHFUOUCZGUJWPPUKZQAKBUNWPRUKZAFCDUPUCUNWPSUK
        ZWQJKMFUIUHZUHZHURUHZUCZUSUHZXMUHZIXMUHJWQXNIXMAXNIUJWPTUKZUTWQKXKWRUCZ
        LMGUIUHZUHZEUGUHZUCZXMVAZJYAUNZXOJUJWQXQWTXKWSUHZXTUCZXMVAYBWQBDEWSXLWR
        XTKXKQWRVBZXTVBZAWSXLXDUDZWPAXDVCZXEYHXBVCYIDEVDXBXCVEVIOHXDVFVGUKXHWQC
        VHUHZBMXJWQYJBCDXJFURUHYJVBZQWQCDFXIVJVKWQYJCEXRGURUHZJLMWQCEGJLMAWPVLV
        MZYKVRZVNVOWQYEYAXQXMWQWTLYDXSXTXAWQMXFUIUHZUHYDXSWQYJCDEFHMYKXIAHDEUPU
        CZUNWPAXDYPHXDXBYPXBXCVPDEVQVSOVTUKYNWAWQMYOXRWQXFGUIXGUTWBWCWDWEWFZWQC
        EXRYLXTJLMYMYGWHZXQYAJXMWGWIWCYFWQXNIXQXPWQYBYCXNXQUNYQYRXQYAJXMWJWIWKW
        LWMWN $.
    $}

    uptrai.n $e |- ( ph ->
            ( ( X ( 2nd ` K ) ( ( 1st ` F ) ` Z ) ) ` M ) = N ) $.
    uptrai.z $e |- ( ph -> Z ( F ( C UP D ) X ) M ) $.
    $( Universal property and fully faithful functor.  (Contributed by Zhi
       Wang, 16-Nov-2025.) $)
    uptrai $p |- ( ph -> Z ( G ( C UP E ) Y ) N ) $=
      ( co cfv adantr cup wbr wb wa cbs chom c1st wceq cful cfth cin wcel ccofu
      eqid c2nd simpr up1st2nd uprcl3 uprcl2a uprcl5 uptra mpdan mpbid ) ALHEJB
      CUARRUBZLIFKBDUARRUBZQAVDVDVEUCQAVDUDZCUESZBCDEFCUFSZGHIJKLAJGUGSSKUHVDMT
      AGCDUIRCDUJRUKULVDNTAGEUMRFUHVDOTVGUNZVFVGBCEUGSZEUOSZHJLVFBCEHJLAVDUPZUQ
      ZVIURVFCEHBJLVLUSAHJLVJSGUOSRSIUHVDPTVHUNZVFBCVJVKVHHJLVMVNUTVAVBVC $.
  $}

  ${
    $d B m n z $.  $d C m n z $.  $d D m n z $.  $d E m n z $.  $d F m n z $.
    $d G m n z $.  $d I m n z $.  $d K m n z $.  $d L m n z $.  $d X m n z $.
    $d Y m n z $.  $d m n ph z $.
    uobffth.b $e |- B = ( Base ` D ) $.
    uobffth.x $e |- ( ph -> X e. B ) $.
    uobffth.f $e |- ( ph -> F e. ( C Func D ) ) $.
    uobffth.g $e |- ( ph -> ( K o.func F ) = G ) $.
    uobffth.y $e |- ( ph -> ( ( 1st ` K ) ` X ) = Y ) $.
    ${
      uobffth.k $e |- ( ph -> K e. ( ( D Full E ) i^i ( D Faith E ) ) ) $.
      $( A fully faithful functor generates equal sets of universal objects.
         (Contributed by Zhi Wang, 19-Nov-2025.) $)
      uobffth $p |- ( ph -> dom ( F ( C UP D ) X )
                          = dom ( G ( C UP E ) Y ) ) $=
        ( vm vn co adantr vz cup cdm cv wbr wex wcel 19.42v c1st cfv c2nd fvexd
        wa cvv wceq cful cfth cin ccofu eqidd simpr uptrai breq2 spcedv exlimiv
        sylbir ccnv cfunc uptrar impbida wb relup releldmb ax-mp 3bitr4g eqrdv
        wrel ) AUAFICDUBSSZUCZGJCEUBSSZUCZAUAUDZQUDZVRUEZQUFZWBRUDZVTUEZRUFZWBV
        SUGZWBWAUGZAWEWHAWEUMAWDUMZQUFWHAWDQUHWKWHQWKWGWBWCIWBFUIUJUJHUKUJSZUJZ
        VTUERUNWMWKWCWLULWKCDEFGHWCWMIJWBAIHUIUJUJJUOZWDOTAHDEUPSDEUQSURUGZWDPT
        AHFUSSGUOZWDNTWKWMUTAWDVAVBWFWMWBVTVCVDVEVFAWHUMAWGUMZRUFWEAWGRUHWQWERW
        QWDWBWFWLVGZUJZVRUEQUNWSWQWFWRULWQBCDEFGHWSWFIJWBAWNWGOTAWOWGPTAWPWGNTK
        AIBUGWGLTAFCDVHSUGWGMTWQWSUTAWGVAVIWCWSWBVRVCVDVEVFVJVRVQWIWEVKCDFIVLQW
        BVRVMVNVTVQWJWHVKCEGJVLRWBVTVMVNVOVP $.
    $}

    uobeq.i $e |- I = ( idFunc ` D ) $.
    uobeq.k $e |- ( ph -> K e. ( D Full E ) ) $.
    uobeq.n $e |- ( ph -> ( L o.func K ) = I ) $.
    ${
      uobeqw.l $e |- ( ph -> L e. ( ( E Full D ) i^i ( E Faith D ) ) ) $.
      $( If a full functor (in fact, a full embedding) is a section of a fully
         faithful functor (surjective on objects), then the sets of universal
         objects are equal.  (Contributed by Zhi Wang, 17-Nov-2025.) $)
      uobeqw $p |- ( ph -> dom ( F ( C UP D ) X ) = dom ( G ( C UP E ) Y ) ) $=
        ( vz vm vn cup co cdm cv wbr wex wcel wa 19.42v c1st cfv c2nd cvv fvexd
        wceq adantr cful cfth cin cop cfunc wrel relfunc fullfunc sselid 1st2nd
        sylancr func1st2nd inss1 sstri ccofu cofu1st2nd eqtr3d cofidfth eqeltrd
        df-br sylib elind eqidd simpr uptrai breq2 spcedv exlimiv sylbir fveq2d
        cofid1a cofuass oveq1d cofulid eqtrd 3eqtr3rd impbida wb relup releldmb
        oveq2d ax-mp 3bitr4g eqrdv ) AUBFKCDUEUFUFZUGZGLCEUEUFUFZUGZAUBUHZUCUHZ
        XEUIZUCUJZXIUDUHZXGUIZUDUJZXIXFUKZXIXHUKZAXLXOAXLULAXKULZUCUJXOAXKUCUMX
        RXOUCXRXNXIXJKXIFUNUOUOIUPUOZUFZUOZXGUIUDUQYAXRXJXTURXRCDEFGIXJYAKLXIAK
        IUNUOZUOZLUSXKQUTAIDEVAUFZDEVBUFZVCUKXKAYDYEISAIYBXSVDZYEADEVEUFZVFIYGU
        KIYFUSDEVGAYDYGIDEVHSVIZIYGVJVKAYBXSYEUIYFYEUKADEYBXSHJUNUOZJUPUOZRADEI
        YHVLAEDJAEDVAUFZEDVBUFZVCZEDVEUFZJYMYKYNYKYLVMEDVHVNUAVIZVLAJIVOUFZYIYJ
        VDYFVOUFHADEDIJYHYOVPTVQVRYBXSYEVTWAVSWBUTAIFVOUFZGUSXKPUTXRYAWCAXKWDWE
        XMYAXIXGWFWGWHWIAXOULAXNULZUDUJXLAXNUDUMYRXLUDYRXKXIXMLXIGUNUOUOYJUFZUO
        ZXEUIUCUQYTYRXMYSURYRCEDGFJXMYTLKXIALYIUOZKUSXNAYCYIUOUUAKAYCLYIQWJABDE
        IJHKRMNYHYOTWKVQUTAJYMUKXNUAUTAJGVOUFZFUSXNAYPFVOUFZJYQVOUFFUUBACDEDFIJ
        OYHYOWLAUUCHFVOUFFAYPHFVOTWMACDFHORWNWOAYQGJVOPXAWPUTYRYTWCAXNWDWEXJYTX
        IXEWFWGWHWIWQXEVFXPXLWRCDFKWSUCXIXEWTXBXGVFXQXOWRCEGLWSUDXIXGWTXBXCXD
        $.
    $}

    uobeq.l $e |- ( ph -> L e. ( E Func D ) ) $.
    $( If a full functor (in fact, a full embedding) is a section of a functor
       (surjective on objects), then the sets of universal objects are equal.
       (Contributed by Zhi Wang, 17-Nov-2025.) $)
    uobeq $p |- ( ph -> dom ( F ( C UP D ) X ) = dom ( G ( C UP E ) Y ) ) $=
      ( cful co cfth c1st cfv c2nd cfunc wrel wcel wceq relfunc fullfunc sselid
      cop 1st2nd sylancr wbr func1st2nd ccofu cofu1st2nd cofidfth df-br eqeltrd
      eqtr3d sylib elind uobffth ) ABCDEFGIKLMNOPQADEUBUCZDEUDUCZISAIIUEUFZIUGU
      FZUOZVJADEUHUCZUIIVNUJIVMUKDEULAVIVNIDEUMSUNZIVNUPUQAVKVLVJURVMVJUJADEVKV
      LHJUEUFZJUGUFZRADEIVOUSAEDJUAUSAJIUTUCVPVQUOVMUTUCHADEDIJVOUAVATVEVBVKVLV
      JVCVFVDVGVH $.
  $}

  ${
    $d A g k l x y $.  $d B g k l x y $.  $d C g k l x y $.  $d D g k l x y $.
    $d E g k l x y $.  $d F g k l x y $.  $d G g k l x y $.  $d K g k l x y $.
    $d L g k l x y $.  $d M g k l x y $.  $d R g k l x y $.  $d S g k l x y $.
    $d X g k l x y $.  $d Y g k l x y $.  $d Z g k l x y $.  $d g k l ph x y $.
    uptr2.a $e |- A = ( Base ` C ) $.
    uptr2.b $e |- B = ( Base ` D ) $.
    uptr2.y $e |- ( ph -> Y = ( R ` X ) ) $.
    uptr2.r $e |- ( ph -> R : A -onto-> B ) $.
    uptr2.s $e |- ( ph -> R ( ( C Full D ) i^i ( C Faith D ) ) S ) $.
    uptr2.f $e |- ( ph -> ( <. K , L >. o.func <. R , S >. ) = <. F , G >. ) $.
    uptr2.x $e |- ( ph -> X e. A ) $.
    uptr2.k $e |- ( ph -> K ( D Func E ) L ) $.
    $( Universal property and fully faithful functor surjective on objects.
       (Contributed by Zhi Wang, 25-Nov-2025.) $)
    uptr2 $p |- ( ph -> ( X ( <. F , G >. ( C UP E ) Z ) M
                      <-> Y ( <. K , L >. ( D UP E ) Z ) M ) ) $=
      ( vg vl vy vk vx cop cup co wbr cbs wcel chom wa simpr eqid uprcl3 uprcl5
      cfv jca wceq fveq2d cful cfth cin cfunc inss1 fullfunc sstri ssbri cofu1a
      syl eqtrd oveq2d adantr eleqtrd cv cco wreu wral wfo wf ffvelcdmda foelrn
      fof wrex sylan w3a simp3 simp1l 3ad2ant1 ccofu simp2 wf1o ffthf1o oveq12d
      f1oeq3d mpbird f1of eqcom reubii sylib opeq2d simpl3 simprr simprl cofu2a
      f1ofveu fveq12d eqidd oveq123d eqeq2d reuxfr1dd ralxfrd2 eqeltrd eleqtrrd
      raleqbidv ffvelcdmd isup cofucla eqeltrrd df-br sylibr 3bitr4rd bibiad )
      ANMIJUJZPDHUKULULUMZOMKLUJZPEHUKULULUMZPHUNVBZUOZMPNIVBZHUPVBZULZUOZUQZAY
      JUQZYNYRYTYMDHIJMPNAYJURZYMUSZUTYTDHIJYPMPNUUAYPUSZVAVCAYLUQZYNYRUUDYMEHK
      LMPOAYLURZUUBUTUUDMPOKVBZYPULZYQUUDEHKLYPMPOUUEUUCVAAUUGYQVDZYLAUUFYOPYPA
      UUFNFVBZKVBYOAOUUIKSVEABDEHFGKLIJNQAFGDEVFULZDEVGULZVHZUMZFGDEVIULZUMZUAU
      ULUUNFGUULUUJUUNUUJUUKVJDEVKVLVMVOZUDUBUCVNVPZVQZVRVSVCAYSUQZUEVTZUFVTZOU
      GVTZLULZVBZMPUUFUJZUVBKVBZHWAVBZULZULZVDZUFOUVBEUPVBZULZWBZUEPUVFYPULZWCZ
      UGCWCUUTUHVTZNUIVTZJULVBZMPYOUJZUVQIVBZUVGULZULZVDZUHNUVQDUPVBZULZWBZUEPU
      VTYPULZWCZUIBWCYLYJUUSUVOUWHUGUIUVQFVBZCBUUSBCUVQFUUSBCFWDZBCFWEAUWJYSTVR
      ZBCFWHVOZWFUUSUWJUVBCUOUVBUWIVDZUIBWIUWKUIBCUVBFWGWJUUSUVQBUOZUWMWKZUVMUW
      FUEUVNUWGUWOUVFUVTPYPUWOUVFUWIKVBUVTUWOUVBUWIKUUSUWNUWMWLZVEUWOBDEHFGKLIJ
      UVQQUWOAUUOAYSUWNUWMWMZUUPVOZUUSUWNKLEHVIULUMZUWMAUWSYSUDVRZWNZUWOAYKFGUJ
      WOULZYIVDZUWQUBVOZUUSUWNUWMWPZVNVPZVQUWOUVJUWCUFUHUVPNUVQGULZVBZUVLUWEUWO
      UWEUVLUVPUXGUWOUWEUVLUXGWQZUWEUVLUXGWEUWOUXIUWEUUIUWIUVKULZUXGWQUWOBDEFGU
      WDUVKNUVQQUWDUSZUVKUSZUWOAUUMUWQUAVOUWOANBUOZUWQUCVOZUXEWRUWOUVLUXJUWEUXG
      UWOOUUIUVBUWIUVKUWOAOUUIVDZUWQSVOZUWPWSWTXAZUWEUVLUXGXBVOWFUWOUXIUVAUVLUO
      ZUVAUXHVDZUHUWEWBZUXQUXIUXRUQUXHUVAVDZUHUWEWBUXTUHUWEUVLUVAUXGXKUYAUXSUHU
      WEUXHUVAXCXDXEWJUWOUVPUWEUOZUXSUQZUQZUVIUWBUUTUYDUVDUVRMMUVHUWAUWOUVHUWAV
      DUYCUWOUVEUVSUVFUVTUVGUWOUUFYOPUWOAUUFYOVDUWQUUQVOXFUXFWSVRUYDUVDUXHUUIUW
      ILULZVBUVRUYDUVAUXHUVCUYEUYDOUUIUVBUWILUWOUXOUYCUXPVRUUSUWNUWMUYCXGWSUWOU
      YBUXSXHXLUYDBDEUVPHFGUWDKLIJNUVQQUWOUUOUYCUWRVRUWOUWSUYCUXAVRUWOUXCUYCUXD
      VRUWOUXMUYCUXNVRUWOUWNUYCUXEVRUXKUWOUYBUXSXIXJVPUYDMXMXNXOXPXTXQUUSUGCYME
      UEUFHKLUVKYPMUVGPORUUBUXLUUCUVGUSZAYNYRXIZUWTUUSOUUICAUXOYSSVRUUSBCNFUWLA
      UXMYSUCVRZYAXRUUSMYQUUGAYNYRXHZAUUHYSUURVRXSYBUUSUIBYMDUEUHHIJUWDYPMUVGPN
      QUUBUXKUUCUYFUYGAIJDHVIULZUMZYSAYIUYJUOUYKAUXBYIUYJUBADEHFGKLUUPUDYCYDIJU
      YJYEYFVRUYHUYIYBYGYH $.
  $}

  ${
    uptr2a.a $e |- A = ( Base ` C ) $.
    uptr2a.b $e |- B = ( Base ` D ) $.
    uptr2a.y $e |- ( ph -> Y = ( ( 1st ` K ) ` X ) ) $.
    uptr2a.f $e |- ( ph -> ( G o.func K ) = F ) $.
    uptr2a.x $e |- ( ph -> X e. A ) $.
    uptr2a.g $e |- ( ph -> G e. ( D Func E ) ) $.
    uptr2a.k $e |- ( ph -> K e. ( ( C Full D ) i^i ( C Faith D ) ) ) $.
    uptr2a.1 $e |- ( ph -> ( 1st ` K ) : A -onto-> B ) $.
    $( Universal property and fully faithful functor surjective on objects.
       (Contributed by Zhi Wang, 25-Nov-2025.) $)
    uptr2a $p |- ( ph -> ( X ( F ( C UP E ) Z ) M
                       <-> Y ( G ( D UP E ) Z ) M ) ) $=
      ( c1st cfv c2nd cop cup co wbr cful cfth cin wrel relfull relin1 1st2ndbr
      wcel ax-mp sylancr ccofu cfunc inss1 sstri sselid cofu1st2nd wceq relfunc
      fullfunc cofucl eqeltrrd 1st2nd 3eqtr3d func1st2nd up1st2ndb 3bitr4d
      uptr2 ) AKJGUBUCZGUDUCZUEZMDFUFUGZUGUHLJHUBUCZHUDUCZUEZMEFUFUGZUGUHKJGMVS
      UGUHLJHMWCUGUHABCDEIUBUCZIUDUCZFVPVQVTWAJKLMNOPUAADEUIUGZDEUJUGZUKZULZIWH
      UPWDWEWHUHWFULWIDEUMWFWGUNUQTIWHUOURAHIUSUGZGWBWDWEUEUSUGVRQADEFIHAWHDEUT
      UGZIWHWFWKWFWGVADEVGVBTVCZSVDADFUTUGZULGWMUPGVRVEDFVFAWJGWMQADEFIHWLSVHVI
      ZGWMVJURVKRAEFHSVLVOADFGJMKWNVMAEFHJMLSVMVN $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Natural transformations and the functor category
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d A h x y $.  $d B h x y $.  $d C h x y $.  $d D h x y $.  $d F h x y $.
    $d G h x y $.  $d H h $.  $d K h x y $.  $d L h x y $.  $d h ph x y $.
    isnatd.1 $e |- N = ( C Nat D ) $.
    isnatd.b $e |- B = ( Base ` C ) $.
    isnatd.h $e |- H = ( Hom ` C ) $.
    isnatd.j $e |- J = ( Hom ` D ) $.
    isnatd.o $e |- .x. = ( comp ` D ) $.
    isnatd.f $e |- ( ph -> F ( C Func D ) G ) $.
    isnatd.g $e |- ( ph -> K ( C Func D ) L ) $.
    isnatd.a $e |- ( ph -> A Fn B ) $.
    isnatd.2 $e |- ( ( ph /\ x e. B )
            -> ( A ` x ) e. ( ( F ` x ) J ( K ` x ) ) ) $.
    isnatd.3 $e |- ( ( ( ph /\ ( x e. B /\ y e. B ) ) /\ h e. ( x H y ) )
    -> ( ( A ` y )
        ( <. ( F ` x ) , ( F ` y ) >. .x. ( K ` y ) )
        ( ( x G y ) ` h ) )
    = ( ( ( x L y ) ` h )
        ( <. ( F ` x ) , ( K ` x ) >. .x. ( K ` y ) )
        ( A ` x ) ) ) $.
    $( Property of being a natural transformation; deduction form.
       (Contributed by Zhi Wang, 29-Sep-2025.) $)
    isnatd $p |- ( ph -> A e. ( <. F , G >. N <. K , L >. ) ) $=
      ( cop co wcel cfv cixp wceq wral cvv wfn cmpt dffn5 sylib cbs fvexi mptex
      cv eqeltrdi ralrimiva elixp2 syl3anbrc wa ralrimivva isnat mpbir2and ) AD
      JKUGNOUGPUHUIDBEBVBZJUJZVKNUJZMUHZUKUIZCVBZDUJIVBZVKVPKUHUJVLVPJUJUGVPNUJ
      ZHUHUHVQVKVPOUHUJVKDUJZVLVMUGVRHUHUHULZIVKVPLUHZUMZCEUMBEUMADUNUIDEUOZVSV
      NUIZBEUMVOADBEVSUPZUNAWCDWEULUDBEDUQURBEVSEFUSRUTVAVCUDAWDBEUEVDBEVNDVEVF
      AWBBCEEAVKEUIVPEUIVGVGVTIWAUFVDVHABCDEFGHIJKLMNOPQRSTUAUBUCVIVJ $.
  $}

  ${
    natrcl2.n $e |- N = ( C Nat D ) $.
    natrcl2.a $e |- ( ph -> A e. ( <. F , G >. N <. K , L >. ) ) $.
    $( Reverse closure for a natural transformation.  (Contributed by Zhi Wang,
       1-Oct-2025.) $)
    natrcl2 $p |- ( ph -> F ( C Func D ) G ) $=
      ( cop cfunc co wcel wbr wa natrcl syl simpld df-br sylibr ) AEFLZCDMNZOZE
      FUDPAUEGHLZUDOZABUCUFINOUEUGQKBCDUCUFIJRSTEFUDUAUB $.

    $( Reverse closure for a natural transformation.  (Contributed by Zhi Wang,
       1-Oct-2025.) $)
    natrcl3 $p |- ( ph -> K ( C Func D ) L ) $=
      ( cop cfunc co wcel wbr wa natrcl syl simprd df-br sylibr ) AGHLZCDMNZOZG
      HUDPAEFLZUDOZUEABUFUCINOUGUEQKBCDUFUCIJRSTGHUDUAUB $.
  $}

  ${
    catbas.c $e |- C = { <. ( Base ` ndx ) , B >. ,
                         <. ( Hom ` ndx ) , H >. ,
                         <. ( comp ` ndx ) , .x. >. } $.
    ${
      catbas.b $e |- B e. _V $.
      $( The base of the category structure.  (Contributed by Zhi Wang,
         5-Nov-2025.) $)
      catbas $p |- B = ( Base ` C ) $=
        ( cvv wcel cbs cfv wceq c1 c5 cdc cop cnx chom cco ctp cstr eqbrtri csn
        catstr baseid snsstp1 sseqtrri strfv ax-mp ) AGHABIJKFABIGLLMNOZBPIJAOZ
        PQJDOZPRJCOZSZUITECADUCUAUDUJUBUMBUJUKULUEEUFUGUH $.
    $}

    ${
      cathomfval.h $e |- H e. _V $.
      $( The hom-sets of the category structure.  (Contributed by Zhi Wang,
         5-Nov-2025.) $)
      cathomfval $p |- H = ( Hom ` C ) $=
        ( cvv wcel chom cfv wceq c1 c5 cdc cop cnx cbs cco ctp cstr eqbrtri csn
        catstr homid snsstp2 sseqtrri strfv ax-mp ) DGHDBIJKFDBIGLLMNOZBPQJAOZP
        IJDOZPRJCOZSZUITECADUCUAUDUKUBUMBUJUKULUEEUFUGUH $.
    $}

    ${
      catcofval.x $e |- .x. e. _V $.
      $( Composition of the category structure.  (Contributed by Zhi Wang,
         5-Nov-2025.) $)
      catcofval $p |- .x. = ( comp ` C ) $=
        ( cvv wcel cco cfv wceq c1 c5 cdc cop cnx cbs chom ctp cstr eqbrtri csn
        catstr ccoid snsstp3 sseqtrri strfv ax-mp ) CGHCBIJKFCBIGLLMNOZBPQJAOZP
        RJDOZPIJCOZSZUITECADUCUAUDULUBUMBUJUKULUEEUFUGUH $.
    $}
  $}

  ${
    $d A m x y $.  $d C m x y $.  $d D m x y $.  $d F m x y $.  $d G m x y $.
    $d K m x y $.  $d L m x y $.  $d M m x y $.  $d N m x y $.  $d O m x y $.
    $d P m x y $.  $d V x $.  $d W x $.  $d m ph x y $.
    natoppf.o $e |- O = ( oppCat ` C ) $.
    natoppf.p $e |- P = ( oppCat ` D ) $.
    natoppf.n $e |- N = ( C Nat D ) $.
    natoppf.m $e |- M = ( O Nat P ) $.
    ${
      natoppf.a $e |- ( ph -> A e. ( <. F , G >. N <. K , L >. ) ) $.
      $( A natural transformation is natural between opposite functors.
         (Contributed by Zhi Wang, 18-Nov-2025.) $)
      natoppf $p |- ( ph -> A e. ( <. K , tpos L >. M <. F , tpos G >. ) ) $=
        ( cfv eqid co vx vy cbs cco ctpos chom oppcbas natrcl3 funcoppc natrcl2
        vm natfn cv wcel wa cop adantr simpr oppchom eleqtrrdi ad2antrr simplrr
        simplrl eleqtrdi nati wf funcf1 ffvelcdmd oppcco 3eqtr4rd ovtpos fveq1i
        natcl oveq2i oveq1i 3eqtr4g isnatd ) AUAUBBCUCRZLEEUDRZUKHIUEZLUFRZEUFR
        ZFGUEZJPVRCLMVRSZUGWASWBSVSSACDEHILMNABCDFGHIKOQUHZUIACDEFGLMNABCDFGHIK
        OQUJZUIABVRCDFGHIKOQWDULAUAUMZVRUNZUOZWGBRZWGFRZWGHRZDUFRZTWLWKWBTWIBVR
        CDFGWMHIKWGOABFGUPHIUPKTUNZWHQUQWDWMSZAWHURVMDWMEWLWKWONUSUTAWHUBUMZVRU
        NZUOZUOZUKUMZWGWPWATZUNZUOZWPBRZWTWPWGITZRZWLWPHRZUPWPFRZVSTZTZWTWPWGGT
        ZRZWJWLWKUPXHVSTZTZXDWTWGWPVTTZRZXITWTWGWPWCTZRZWJXMTXCWJXLXHWKUPWLDUDR
        ZTTXFXDXHXGUPWLXSTTXNXJXCBVRCDWTXSFGCUFRZHIKWPWGOAWNWRXBQVAWDXTSZXSSZAW
        HWQXBVBZAWHWQXBVCZXCWTXAWPWGXTTWSXBURCXTLWGWPYAMUSVDVEXCDUCRZDXSWJXLEWL
        WKXHYESZYBNXCVRYEWGHAVRYEHVFWRXBAVRYECDHIWDYFWEVGVAZYDVHZXCVRYEWGFAVRYE
        FVFWRXBAVRYECDFGWDYFWFVGVAZYDVHXCVRYEWPFYIYCVHZVIXCYEDXSXFXDEWLXGXHYFYB
        NYHXCVRYEWPHYGYCVHYJVIVJXPXFXDXIWTXOXEWGWPIVKVLVNXRXLWJXMWTXQXKWGWPGVKV
        LVOVPVQ $.
    $}

    natoppfb.k $e |- ( ph -> K = ( oppFunc ` F ) ) $.
    natoppfb.l $e |- ( ph -> L = ( oppFunc ` G ) ) $.
    ${
      natoppf2.a $e |- ( ph -> A e. ( F N G ) ) $.
      $( A natural transformation is natural between opposite functors.
         (Contributed by Zhi Wang, 18-Nov-2025.) $)
      natoppf2 $p |- ( ph -> A e. ( L M K ) ) $=
        ( cfv c1st c2nd ctpos co nat1st2nd natoppf coppf wcel cfunc wceq natrcl
        cop simprd oppfval2 3syl eqtrd simpld oveq12d eleqtrrd ) ABGUATZGUBTZUC
        ULZFUATZFUBTZUCULZJUDIHJUDABCDEVCVDUTVAJKLMNOPABCDFGKOSUEUFAIVBHVEJAIGU
        GTZVBRABFGKUDUHZGCDUIUDZUHZVFVBUJSVGFVHUHZVIBCDFGKOUKZUMCDGUNUOUPAHFUGT
        ZVEQAVGVJVLVEUJSVGVJVIVKUQCDFUNUOUPURUS $.
    $}

    natoppfb.c $e |- ( ph -> C e. V ) $.
    natoppfb.d $e |- ( ph -> D e. W ) $.
    $( A natural transformation is natural between opposite functors, and vice
       versa.  (Contributed by Zhi Wang, 18-Nov-2025.) $)
    natoppfb $p |- ( ph -> ( F N G ) = ( L M K ) ) $=
      ( vx co cv wcel wa coppf cfv wceq adantr simpr natoppf2 coppc cnat fveq2d
      cfunc natrcl adantl simpld eqeltrrd relfunc 2oppf eqtr2d simprd 2oppchomf
      eqid chomf a1i ccomf 2oppccomf c1st funcoppc5 func1st2nd funcrcl2 oppccat
      c2nd ccat 3syl funcrcl3 natpropd eqtrid oveqd eleqtrrd impbida eqrdv ) AU
      BEFJUCZHGIUCZAUBUDZWFUEZWHWGUEZAWIUFWHBCDEFGHIJKNOPQAGEUGUHZUIZWIRUJAHFUG
      UHZUIZWISUJAWIUKULAWJUFZWHEFKUMUHZDUMUHZUNUCZUCWFWOWHKDWQHGFEWRIWPWPVFZWQ
      VFZQWRVFWOHUGUHWMUGUHFWOHWMUGAWNWJSUJZUOWOKDUPUCZFWMWOHWMXBXAWOHXBUEZGXBU
      EZWJXCXDUFAWHKDHGIQUQURZUSUTKDVAZWMVFVBVCWOGUGUHWKUGUHEWOGWKUGAWLWJRUJZUO
      WOXBEWKWOGWKXBXGWOXCXDXEVDUTZXFWKVFVBVCAWJUKULWOJWREFWOJBCUNUCWRPWOBWPCWQ
      BVGUHWPVGUHUIWOBKNVEVHBVIUHWPVIUHUIWOBKNVJVHCVGUHWQVGUHUIWOCDOVEVHCVIUHWQ
      VIUHUIWOCDOVJVHWOBCEVKUHZEVPUHZWOBCEWOBCDEKLMNOABLUEWJTUJACMUEWJUAUJXHVLV
      MZVNZWOBVQUEKVQUEWPVQUEXLBKNVOKWPWSVOVRWOBCXIXJXKVSZWOCVQUEDVQUEWQVQUEXMC
      DOVODWQWTVOVRVTWAWBWCWDWE $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Initial, terminal and zero objects of a category
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d B b h $.  $d C b h $.  $d O b h $.
    initoo2.b $e |- B = ( Base ` C ) $.
    $( An initial object is an object in the base set.  (Contributed by Zhi
       Wang, 23-Oct-2025.) $)
    initoo2 $p |- ( O e. ( InitO ` C ) -> O e. B ) $=
      ( vh vb cinito cfv wcel cv chom co weu wral eqid initorcl isinitoi anidms
      wa simpld ) CBGHIZCAIZEJCFJBKHZLIEMFANZUAUBUDSUAABEUCCFDUCOBCPQRT $.

    $( A terminal object is an object in the base set.  (Contributed by Zhi
       Wang, 23-Oct-2025.) $)
    termoo2 $p |- ( O e. ( TermO ` C ) -> O e. B ) $=
      ( vh vb ctermo cfv wcel cv chom co weu wral eqid termorcl istermoi anidms
      wa simpld ) CBGHIZCAIZEJFJCBKHZLIEMFANZUAUBUDSUAABEUCCFDUCOBCPQRT $.

    $( A zero object is an object in the base set.  (Contributed by Zhi Wang,
       23-Oct-2025.) $)
    zeroo2 $p |- ( O e. ( ZeroO ` C ) -> O e. B ) $=
      ( czeroo cfv wcel ccat zeroorcl wa cinito ctermo iszeroi simpld eleqtrrdi
      cbs mpancom ) CBEFGZCBPFZABHGZRCSGZBCITRJUACBKFGCBLFGJBCMNQDO $.
  $}

  ${
    $d C c $.  $d I c $.
    $( Initial objects are terminal in the opposite category.  (Contributed by
       Zhi Wang, 23-Oct-2025.) $)
    oppcinito $p |- ( I e. ( InitO ` C )
                  <-> I e. ( TermO ` ( oppCat ` C ) ) ) $=
      ( vc cinito cfv wcel ccat coppc ctermo initorcl termorcl cbs eqid oppcbas
      cvv wb termoo2 elfvex id oppccatb 3syl mpbird 2fveq3 dfinito2 fvex eleq2d
      cv fvmpt pm5.21nii ) BADEZFAGFZBAHEZIEZFZABJUNUKULGFZULBKUNBALEZFAOFZUKUO
      PUPULBUPAULULMZUPMNQBALRUQAULOURUQSTUAUBUKUJUMBCACUGZHEIEUMGDUSAIHUCCUDUL
      IUEUHUFUI $.

    $( Terminal objects are initial in the opposite category.  Comments before
       Definition 7.4 in [Adamek] p. 102.  (Contributed by Zhi Wang,
       26-Oct-2025.) $)
    oppctermo $p |- ( I e. ( TermO ` C )
                  <-> I e. ( InitO ` ( oppCat ` C ) ) ) $=
      ( vc ctermo cfv wcel ccat coppc cinito termorcl initorcl cbs eqid oppcbas
      cvv wb initoo2 elfvex id oppccatb 3syl mpbird 2fveq3 dftermo2 fvex eleq2d
      cv fvmpt pm5.21nii ) BADEZFAGFZBAHEZIEZFZABJUNUKULGFZULBKUNBALEZFAOFZUKUO
      PUPULBUPAULULMZUPMNQBALRUQAULOURUQSTUAUBUKUJUMBCACUGZHEIEUMGDUSAIHUCCUDUL
      IUEUHUFUI $.

    $( Zero objects are zero in the opposite category.  Remark 7.8 of [Adamek]
       p. 103.  (Contributed by Zhi Wang, 27-Oct-2025.) $)
    oppczeroo $p |- ( I e. ( ZeroO ` C )
                  <-> I e. ( ZeroO ` ( oppCat ` C ) ) ) $=
      ( vc czeroo cfv wcel ccat coppc zeroorcl cbs cvv wb eqid id cinito ctermo
      cin eqriv chom zerooval zeroo2 elfvex oppccatb mpbird oppcinito oppctermo
      oppcbas 3syl cv ineq12i incom eqtri oppccat 3eqtr4a eleq2d pm5.21nii ) BA
      DEZFAGFZBAHEZDEZFZABIVAURUSGFZUSBIVABAJEZFAKFZURVBLVCUSBVCAUSUSMZVCMZUGZU
      ABAJUBVDAUSKVEVDNUCUHUDURUQUTBURAOEZAPEZQZUSOEZUSPEZQZUQUTVJVLVKQVMVHVLVI
      VKCVHVLACUIZUERCVIVKAVNUFRUJVLVKUKULURVCAASEZURNVFVOMTURVCUSUSSEZAUSVEUMV
      GVPMTUNUOUP $.
  $}

  ${
    termoeu2.c $e |- ( ph -> C e. Cat ) $.
    termoeu2.a $e |- ( ph -> A e. ( TermO ` C ) ) $.
    termoeu2.i $e |- ( ph -> A ( ~=c ` C ) B ) $.
    $( Terminal objects are essentially unique; if ` A ` is a terminal object,
       then so is every object that is isomorphic to ` A ` .  (Contributed by
       Zhi Wang, 26-Oct-2025.) $)
    termoeu2 $p |- ( ph -> B e. ( TermO ` C ) ) $=
      ( coppc cfv cinito wcel ctermo ccat eqid oppccat oppctermo sylib initoeu2
      syl oppccic sylibr ) ACDHIZJIZKCDLIZKABCUBADMKUBMKEDUBUBNZOSABUDKBUCKFDBP
      QADBCUBUEGTRDCPUA $.
  $}

  ${
    initopropdlemlem.1 $e |- F Fn X $.
    initopropdlemlem.2 $e |- ( ph -> -. A e. Y ) $.
    initopropdlemlem.3 $e |- X C_ Y $.
    initopropdlemlem.4 $e |- ( ( ph /\ B e. X ) -> ( F ` B ) = (/) ) $.
    $( Lemma for ~ initopropdlem , ~ termopropdlem , and ~ zeroopropdlem .
       (Contributed by Zhi Wang, 26-Oct-2025.) $)
    initopropdlemlem $p |- ( ph -> ( F ` A ) = ( F ` B ) ) $=
      ( wcel cfv wceq wa c0 wn eleq2i ndmfv sylnbir adantr sseli nsyl cdm fndmi
      syl eqtr4d adantl pm2.61dan ) ACEKZBDLZCDLZMAUINUJOUKAUJOMZUIABEKZPULABFK
      UMHEFBIUAUBUMBDUCZKULUNEBEDGUDZQBDRSUEZTJUFAUIPZNUJOUKAULUQUPTUQUKOMZAUIC
      UNKURUNECUOQCDRSUGUFUH $.
  $}

  ${
    $d C a b h $.  $d D a b h $.  $d a b h ph $.
    initopropd.1 $e |- ( ph -> ( Homf ` C ) = ( Homf ` D ) ) $.
    initopropd.2 $e |- ( ph -> ( comf ` C ) = ( comf ` D ) ) $.
    ${
      initopropdlem.1 $e |- ( ph -> -. C e. _V ) $.
      $( Lemma for ~ initopropd .  (Contributed by Zhi Wang, 26-Oct-2025.) $)
      initopropdlem $p |- ( ph -> ( InitO ` C ) = ( InitO ` D ) ) $=
        ( vh va vb cinito ccat cvv wcel cfv cv crab c0 eqid wceq chomf ssv chom
        initofn wa co weu cbs wral simpr initoval fvprc syl eqtr3d homf0 sylibr
        wn rabeqdv rab0 eqtrdi adantr eqtrd initopropdlemlem ) ABCJKLUCFKUAACKM
        ZUDZCJNGOHOIOCUBNZUEMGUFICUGNZUHZHVFPZQVDVFCGVEHIAVCUIVFRVERUJAVHQSVCAV
        HVGHQPQAVGHVFQACTNZQSVFQSABTNZVIQDABLMUPVJQSFBTUKULUMCUNUOUQVGHURUSUTVA
        VB $.

      $( Lemma for ~ termopropd .  (Contributed by Zhi Wang, 26-Oct-2025.) $)
      termopropdlem $p |- ( ph -> ( TermO ` C ) = ( TermO ` D ) ) $=
        ( vh vb va ctermo ccat cvv wcel cfv cv crab c0 eqid wceq chomf ssv chom
        termofn wa co weu cbs wral simpr termoval fvprc syl eqtr3d homf0 sylibr
        wn rabeqdv rab0 eqtrdi adantr eqtrd initopropdlemlem ) ABCJKLUCFKUAACKM
        ZUDZCJNGOHOIOCUBNZUEMGUFHCUGNZUHZIVFPZQVDVFCGVEIHAVCUIVFRVERUJAVHQSVCAV
        HVGIQPQAVGIVFQACTNZQSVFQSABTNZVIQDABLMUPVJQSFBTUKULUMCUNUOUQVGIURUSUTVA
        VB $.

      $( Lemma for ~ zeroopropd .  (Contributed by Zhi Wang, 26-Oct-2025.) $)
      zeroopropdlem $p |- ( ph -> ( ZeroO ` C ) = ( ZeroO ` D ) ) $=
        ( czeroo ccat cvv wcel cfv cinito ctermo cin eqid wceq fvprc syl eqtr3d
        c0 zeroofn ssv wa cbs simpr zerooval initopropdlem adantr termopropdlem
        chom wn ineq12d inidm eqtrdi eqtrd initopropdlemlem ) ABCGHIUAFHUBACHJZ
        UCZCGKCLKZCMKZNZTURCUDKZCCUJKZAUQUEVBOVCOUFURVATTNTURUSTUTTAUSTPUQABLKZ
        USTABCDEFUGABIJUKZVDTPFBLQRSUHAUTTPUQABMKZUTTABCDEFUIAVEVFTPFBMQRSUHULT
        UMUNUOUP $.
    $}

    $( Two structures with the same base, hom-sets and composition operation
       have the same initial objects.  (Contributed by Zhi Wang,
       23-Oct-2025.) $)
    initopropd $p |- ( ph -> ( InitO ` C ) = ( InitO ` D ) ) $=
      ( vh va vb cvv wcel cinito cfv wceq wn wa adantr simpr ccat wral eqid weu
      chomf ccomf initopropdlem eqcomd cv chom cbs eqidd homfeqbas homfeq mpbid
      co crab r19.21bi eleq2d ralbidva pm5.32da raleqdv anbi12d bitrd rabbidva2
      eubidv initoval simprl simprr catpropd biimpa 3eqtr4d pm5.32i cdm initofn
      sylbir c0 fndmi eleq2i ndmfv sylnbir ad2antrl eqtr4d pm2.61ddan pm2.61dda
      ad2antll ) ABIJZCIJZBKLZCKLZMZAWDNZOBCABUBLZCUBLZMZWIDPABUCLZCUCLZMZWIEPA
      WIQUDAWENZOZWGWFWQCBWQWJWKAWLWPDPUEWQWMWNAWOWPEPUEAWPQUDUEAWDWEOZOZBRJZCR
      JZWHWSWTOZFUFZGUFZHUFZBUGLZUMZJZFUAZHBUHLZSZGXJUNXCXDXECUGLZUMZJZFUAZHCUH
      LZSZGXPUNWFWGXBXKXQGXJXPXBXDXJJZXKOXRXOHXJSZOXDXPJZXQOXBXRXKXSXBXROZXIXOH
      XJYAXEXJJOZXHXNFYBXGXMXCYAXGXMMZHXJXBYCHXJSZGXJXBWLYDGXJSWSWLWTAWLWRDPZPZ
      XBGHXJBCXFXLXFTZXLTZXBXJUIXBBCYFUJZUKULUOUOUPVCUQURXBXRXTXSXQXBXJXPXDYIUP
      XBXOHXJXPYIUSUTVAVBXBXJBFXFGHWSWTQXJTYGVDXBXPCFXLGHWSWTXAWSBCIIYEAWOWREPA
      WDWEVEAWDWEVFVGZVHXPTYHVDVIZWSXAOXBWHWSWTXAYJVJYKVMWSWTNZXANZOOWFVNWGYLWF
      VNMZWSYMWTBKVKZJYNYORBRKVLVOZVPBKVQVRVSYMWGVNMZWSYLXACYOJYQYORCYPVPCKVQVR
      WCVTWAWB $.

    $( Two structures with the same base, hom-sets and composition operation
       have the same terminal objects.  (Contributed by Zhi Wang,
       26-Oct-2025.) $)
    termopropd $p |- ( ph -> ( TermO ` C ) = ( TermO ` D ) ) $=
      ( vh vb va cvv wcel ctermo cfv wceq wn wa adantr simpr ccat wral eqid weu
      chomf ccomf termopropdlem eqcomd cv chom cbs crab homfeqbas homfeq ralcom
      eqidd bitrdi mpbid r19.21bi eleq2d eubidv ralbidva pm5.32da raleqdv bitrd
      co anbi12d rabbidva2 termoval simprl simprr biimpa 3eqtr4d pm5.32i sylbir
      catpropd c0 cdm termofn fndmi eleq2i sylnbir ad2antrl ad2antll pm2.61ddan
      ndmfv eqtr4d pm2.61dda ) ABIJZCIJZBKLZCKLZMZAWFNZOBCABUBLZCUBLZMZWKDPABUC
      LZCUCLZMZWKEPAWKQUDAWGNZOZWIWHWSCBWSWLWMAWNWRDPUEWSWOWPAWQWREPUEAWRQUDUEA
      WFWGOZOZBRJZCRJZWJXAXBOZFUFZGUFZHUFZBUGLZVCZJZFUAZGBUHLZSZHXLUIXEXFXGCUGL
      ZVCZJZFUAZGCUHLZSZHXRUIWHWIXDXMXSHXLXRXDXGXLJZXMOXTXQGXLSZOXGXRJZXSOXDXTX
      MYAXDXTOZXKXQGXLYCXFXLJOZXJXPFYDXIXOXEYCXIXOMZGXLXDYEGXLSZHXLXDWNYFHXLSZX
      AWNXBAWNWTDPZPZXDWNYEHXLSGXLSYGXDGHXLBCXHXNXHTZXNTZXDXLUMXDBCYIUJZUKYEGHX
      LXLULUNUOUPUPUQURUSUTXDXTYBYAXSXDXLXRXGYLUQXDXQGXLXRYLVAVDVBVEXDXLBFXHHGX
      AXBQXLTYJVFXDXRCFXNHGXAXBXCXABCIIYHAWQWTEPAWFWGVGAWFWGVHVMZVIXRTYKVFVJZXA
      XCOXDWJXAXBXCYMVKYNVLXAXBNZXCNZOOWHVNWIYOWHVNMZXAYPXBBKVOZJYQYRRBRKVPVQZV
      RBKWCVSVTYPWIVNMZXAYOXCCYRJYTYRRCYSVRCKWCVSWAWDWBWE $.

    $( Two structures with the same base, hom-sets and composition operation
       have the same zero objects.  (Contributed by Zhi Wang, 26-Oct-2025.) $)
    zeroopropd $p |- ( ph -> ( ZeroO ` C ) = ( ZeroO ` D ) ) $=
      ( cvv wcel czeroo wceq wn wa chomf adantr ccomf simpr eqcomd ccat eqid c0
      cfv zeroopropdlem cin ad2antrr initopropd termopropd ineq12d cbs zerooval
      cinito ctermo chom simprl simprr catpropd biimpa 3eqtr4d sylbir cdm fndmi
      pm5.32i zeroofn eleq2i ndmfv sylnbir ad2antrl eqtr4d pm2.61ddan pm2.61dda
      ad2antll ) ABFGZCFGZBHTZCHTZIZAVJJZKBCABLTZCLTZIZVODMABNTZCNTZIZVOEMAVOOU
      AAVKJZKZVMVLWCCBWCVPVQAVRWBDMPWCVSVTAWAWBEMPAWBOUAPAVJVKKZKZBQGZCQGZVNWEW
      FKZBUITZBUJTZUBCUITZCUJTZUBVLVMWHWIWKWJWLWHBCAVRWDWFDUCZAWAWDWFEUCZUDWHBC
      WMWNUEUFWHBUGTZBBUKTZWEWFOWORWPRUHWHCUGTZCCUKTZWEWFWGWEBCFFAVRWDDMAWAWDEM
      AVJVKULAVJVKUMUNZUOWQRWRRUHUPZWEWGKWHVNWEWFWGWSUTWTUQWEWFJZWGJZKKVLSVMXAV
      LSIZWEXBWFBHURZGXCXDQBQHVAUSZVBBHVCVDVEXBVMSIZWEXAWGCXDGXFXDQCXEVBCHVCVDV
      IVFVGVH $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Product of categories
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( The binary product of categories is a proper operator, so it can be used
     with ~ ovprc1 , ~ elbasov , ~ strov2rcl , and so on.  See ~ reldmxpcALT
     for an alternate proof with less "essential steps" but more "bytes".
     (Proposed by SN, 15-Oct-2025.)  (Contributed by Zhi Wang, 15-Oct-2025.) $)
  reldmxpc $p |- Rel dom Xc. $=
    ( cxpc cdm wrel cvv cxp relxp fnxpc fndmi releqi mpbir ) ABZCDDEZCDDFKLLAGH
    IJ $.

  ${
    $d b f g h r s u v x y $.
    $( Alternate proof of ~ reldmxpc .  (Contributed by Zhi Wang, 15-Oct-2025.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    reldmxpcALT $p |- Rel dom Xc. $=
      ( vr vs vb vh vu vv vx vy vg vf cv cbs cfv cxp c1st chom co c2nd cmpo cop
      cvv cnx cco ctp csb cxpc df-xpc reldmmpo ) ABUAUACAKZLMBKZLMNDEFCKZUKEKZO
      MFKZOMUIPMQULRMUMRMUJPMQNSUBLMUKTUBPMDKZTUBUCMGHUKUKNUKIJGKZRMZHKZUNQUOUN
      MIKZOMJKZOMUOOMZOMUPOMTUQOMUIUCMQQURRMUSRMUTRMUPRMTUQRMUJUCMQQTSSTUDUEUEU
      FGHFEJIDBACUGUH $.
  $}

  ${
    elxpcbasex1.t $e |- T = ( C Xc. D ) $.
    elxpcbasex1.b $e |- B = ( Base ` T ) $.
    elxpcbasex1.x $e |- ( ph -> X e. B ) $.
    $( A non-empty base set of the product category indicates the existence of
       the first factor of the product category.  (Contributed by Zhi Wang,
       8-Oct-2025.)  (Proof shortened by SN, 15-Oct-2025.) $)
    elxpcbasex1 $p |- ( ph -> C e. _V ) $=
      ( wcel cvv cxpc reldmxpc strov2rcl syl ) AFBJCKJIBDELCFGHMNO $.

    $( Alternate proof of ~ elxpcbasex1 .  (Contributed by Zhi Wang,
       8-Oct-2025.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    elxpcbasex1ALT $p |- ( ph -> C e. _V ) $=
      ( c1st cfv cbs cxp wcel eqid xpcbas eqtr4i eleqtrdi xp1st syl elfvexd ) A
      FJKZLCAFCLKZDLKZMZNUBUCNAFBUEIBELKUEHCDEUCUDGUCOUDOPQRFUCUDSTUA $.

    $( A non-empty base set of the product category indicates the existence of
       the second factor of the product category.  (Contributed by Zhi Wang,
       8-Oct-2025.)  (Proof shortened by SN, 15-Oct-2025.) $)
    elxpcbasex2 $p |- ( ph -> D e. _V ) $=
      ( cvv wcel wa cxpc reldmxpc elbasov syl simprd ) ACJKZDJKZAFBKRSLIFBEMCDN
      GHOPQ $.

    $( Alternate proof of ~ elxpcbasex2 .  (Contributed by Zhi Wang,
       8-Oct-2025.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    elxpcbasex2ALT $p |- ( ph -> D e. _V ) $=
      ( c2nd cfv cbs cxp wcel eqid xpcbas eqtr4i eleqtrdi xp2nd syl elfvexd ) A
      FJKZLDAFCLKZDLKZMZNUBUDNAFBUEIBELKUEHCDEUCUDGUCOUDOPQRFUCUDSTUA $.
  $}

  ${
    $d A u v $.  $d B u v $.  $d C u v $.  $d D u v $.  $d E u v $.
    xpcfucbas.t $e |- T = ( ( B FuncCat C ) Xc. ( D FuncCat E ) ) $.
    $( The base set of the product of two categories of functors.  (Contributed
       by Zhi Wang, 1-Oct-2025.) $)
    xpcfucbas $p |- ( ( B Func C ) X. ( D Func E ) ) = ( Base ` T ) $=
      ( cfuc co cfunc eqid fucbas xpcbas ) ABGHZCEGHZDABIHCEIHFABMMJKCENNJKL $.

    xpcfuchomfval.b $e |- A = ( Base ` T ) $.
    xpcfuchomfval.k $e |- K = ( Hom ` T ) $.
    $( Set of morphisms of the binary product of categories of functors.
       (Contributed by Zhi Wang, 1-Oct-2025.) $)
    xpcfuchomfval $p |- K = ( u e. A , v e. A |->
              ( ( ( 1st ` u ) ( B Nat C ) ( 1st ` v ) )
             X. ( ( 2nd ` u ) ( D Nat E ) ( 2nd ` v ) ) ) ) $=
      ( cfuc co cnat eqid fuchom xpchomfval ) ABCDEMNZFHMNZGDEONZFHONZIJKDESUAS
      PUAPQFHTUBTPUBPQLR $.

    xpcfuchom.x $e |- ( ph -> X e. A ) $.
    xpcfuchom.y $e |- ( ph -> Y e. A ) $.
    $( Set of morphisms of the binary product of categories of functors.
       (Contributed by Zhi Wang, 1-Oct-2025.) $)
    xpcfuchom $p |- ( ph -> ( X K Y ) =
         ( ( ( 1st ` X ) ( B Nat C ) ( 1st ` Y ) )
        X. ( ( 2nd ` X ) ( D Nat E ) ( 2nd ` Y ) ) ) ) $=
      ( cfuc co cnat eqid fuchom xpchom ) ABCDPQZEGPQZFCDRQZEGRQZHIJKLCDUBUDUBS
      UDSTEGUCUEUCSUESTMNOUA $.
  $}

  ${
    xpcfuchom2.t $e |- T = ( ( B FuncCat C ) Xc. ( D FuncCat E ) ) $.
    ${
      xpcfuchom2.m $e |- ( ph -> M e. ( B Func C ) ) $.
      xpcfuchom2.n $e |- ( ph -> N e. ( D Func E ) ) $.
      xpcfuchom2.p $e |- ( ph -> P e. ( B Func C ) ) $.
      xpcfuchom2.q $e |- ( ph -> Q e. ( D Func E ) ) $.
      xpcfuchom2.k $e |- K = ( Hom ` T ) $.
      $( Value of the set of morphisms in the binary product of categories of
         functors.  (Contributed by Zhi Wang, 1-Oct-2025.) $)
      xpcfuchom2 $p |- ( ph -> ( <. M , N >. K <. P , Q >. ) =
         ( ( M ( B Nat C ) P ) X. ( N ( D Nat E ) Q ) ) ) $=
        ( cfuc co eqid cnat cfunc fucbas fuchom xpchom2 ) ABCRSZDHRSZEFGBCUASZD
        HUASZIJKBCUBSDHUBSLBCUFUFTZUCDHUGUGTZUCBCUFUHUJUHTUDDHUGUIUKUITUDMNOPQU
        E $.
    $}

    xpcfucco2.o $e |- O = ( comp ` T ) $.
    xpcfucco2.f $e |- ( ph -> F e. ( M ( B Nat C ) P ) ) $.
    xpcfucco2.g $e |- ( ph -> G e. ( N ( D Nat E ) Q ) ) $.
    xpcfucco2.k $e |- ( ph -> K e. ( P ( B Nat C ) R ) ) $.
    xpcfucco2.l $e |- ( ph -> L e. ( Q ( D Nat E ) S ) ) $.
    $( Value of composition in the binary product of categories of functors.
       (Contributed by Zhi Wang, 1-Oct-2025.) $)
    xpcfucco2 $p |- ( ph ->
              ( <. K , L >.
                ( <. <. M , N >. , <. P , Q >. >. O <. R , S >. )
                <. F , G >. )
              = <. ( K ( <. M , P >. ( comp ` ( B FuncCat C ) ) R ) F )
                 , ( L ( <. N , Q >. ( comp ` ( D FuncCat E ) ) S ) G ) >. ) $=
      ( cfuc co cco cfv cnat cfunc eqid fucbas fuchom wcel wa natrcl syl simpld
      simprd xpcco2 ) ABCUDUEZDJUDUEZEFGHVAUFUGZIUTUFUGZKLBCUHUEZDJUHUEZMNOPQBC
      UIUEZDJUIUEZRBCUTUTUJZUKDJVAVAUJZUKBCUTVDVHVDUJZULDJVAVEVIVEUJZULAOVFUMZE
      VFUMZAKOEVDUEUMVLVMUNTKBCOEVDVJUOUPZUQAPVGUMZFVGUMZALPFVEUEUMVOVPUNUALDJP
      FVEVKUOUPZUQAVLVMVNURAVOVPVQURVCUJVBUJSAVMGVFUMZAMEGVDUEUMVMVRUNUBMBCEGVD
      VJUOUPURAVPHVGUMZANFHVEUEUMVPVSUNUCNDJFHVEVKUOUPURTUAUBUCUS $.

    $( The composition of two natural transformations is a natural
       transformation.  (Contributed by Zhi Wang, 1-Oct-2025.) $)
    xpcfuccocl $p |- ( ph ->
               ( <. K , L >.
                 ( <. <. M , N >. , <. P , Q >. >. O <. R , S >. )
                 <. F , G >. )
                e. ( ( M ( B Nat C ) R ) X. ( N ( D Nat E ) S ) ) ) $=
      ( cop co cfuc cco cfv cnat cxp xpcfucco2 eqid fuccocl opelxpd eqeltrd ) A
      MNUDKLUDOPUDEFUDUDGHUDQUEUEMKOEUDGBCUFUEZUGUHZUEUEZNLPFUDHDJUFUEZUGUHZUEU
      EZUDOGBCUIUEZUEZPHDJUIUEZUEZUJABCDEFGHIJKLMNOPQRSTUAUBUCUKAURVAVCVEABCUPK
      MUQOEGVBUPULVBULUQULTUBUMADJUSLNUTPFHVDUSULVDULUTULUAUCUMUNUO $.

    $d .x. x $.  $d .xb y $.  $d B x $.  $d C x $.  $d D y $.  $d E y $.
    $d F x $.  $d G y $.  $d K x $.  $d L y $.  $d M x $.  $d N y $.  $d P x $.
    $d Q y $.  $d R x $.  $d S y $.  $d X x $.  $d Y y $.  $d ph x $.
    $d ph y $.
    xpcfucco3.x $e |- X = ( Base ` B ) $.
    xpcfucco3.y $e |- Y = ( Base ` D ) $.
    xpcfucco3.o1 $e |- .x. = ( comp ` C ) $.
    xpcfucco3.o2 $e |- .xb = ( comp ` E ) $.
    $( Value of composition in the binary product of categories of functors;
       expressed explicitly.  (Contributed by Zhi Wang, 1-Oct-2025.) $)
    xpcfucco3 $p |- ( ph ->
              ( <. K , L >.
                ( <. <. M , N >. , <. P , Q >. >. O <. R , S >. )
                <. F , G >. )
              = <. ( x e. X |-> ( ( K ` x )
              ( <. ( ( 1st ` M ) ` x ) , ( ( 1st ` P ) ` x ) >.
                .x. ( ( 1st ` R ) ` x ) )
                                 ( F ` x ) ) )
                 , ( y e. Y |-> ( ( L ` y )
              ( <. ( ( 1st ` N ) ` y ) , ( ( 1st ` Q ) ` y ) >.
                .xb ( ( 1st ` S ) ` y ) )
                                 ( G ` y ) ) ) >. ) $=
      ( cop co cfuc cco cfv c1st cmpt xpcfucco2 cnat eqid fucco opeq12d eqtrd
      cv ) AQRUNOPUNSTUNGHUNUNIJUNUAUOUOQOSGUNIDEUPUOZUQURZUOUOZRPTHUNJFNUPUOZU
      QURZUOUOZUNBUBBVGZQURVNOURVNSUSURURVNGUSURURUNVNIUSURURMUOUOUTZCUCCVGZRUR
      VPPURVPTUSURURVPHUSURURUNVPJUSURURKUOUOUTZUNADEFGHIJLNOPQRSTUAUDUEUFUGUHU
      IVAAVJVOVMVQABUBDEVHOQVIMSGIDEVBUOZVHVCVRVCUJULVIVCUFUHVDACUCFNVKPRVLKTHJ
      FNVBUOZVKVCVSVCUKUMVLVCUGUIVDVEVF $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Swap functors
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $c swapF $.

  $( Extend class notation with the class of swap functors. $)
  cswapf $a class swapF $.

  ${
    $d B b c d h s u v x $.  $d C b c d h s u v $.  $d D b c d h s u v $.
    $d H b c d f h s u v $.  $d S b c d h s u v $.  $d U b c d h s $.
    $d V b c d h s $.  $d b c d h ph s u v $.  $d b c d f h s u v x $.
    $( Define the swap functor from ` ( C Xc. D ) ` to ` ( D Xc. C ) ` by
       swapping all objects ( ~ swapf1 ) and morphisms ( ~ swapf2 ) .

       Such functor is called a "swap functor" in
       ~ https://arxiv.org/pdf/2302.07810 or a "twist functor" in
       ~ https://arxiv.org/pdf/2508.01886 , the latter of which finds its
       counterpart as "twisting map" in ~ https://arxiv.org/pdf/2411.04102 for
       tensor product of algebras.  The "swap functor" or "twisting map" is
       often denoted as a small tau ` ta ` in literature.  However, the term
       "twist functor" is defined differently in
       ~ https://arxiv.org/pdf/1208.4046 and thus not adopted here.

       ` tpos _I ` depends on more mathbox theorems, and thus are not adopted
       here.  See ~ dfswapf2 for an alternate definition.

       (Contributed by Zhi Wang, 7-Oct-2025.) $)
    df-swapf $a |- swapF = ( c e. _V , d e. _V |->
        [_ ( c Xc. d ) / s ]_ [_ ( Base ` s ) / b ]_ [_ ( Hom ` s ) / h ]_
        <. ( x e. b |-> U. `' { x } ) ,
           ( u e. b , v e. b |-> ( f e. ( u h v ) |-> U. `' { f } ) ) >. ) $.

    $( Alternate definition of ` swapF ` ( ~ df-swapf ).  (Contributed by Zhi
       Wang, 9-Oct-2025.) $)
    dfswapf2 $p |- swapF = ( c e. _V , d e. _V |->
        [_ ( c Xc. d ) / s ]_ [_ ( Base ` s ) / b ]_ [_ ( Hom ` s ) / h ]_
        <. ( tpos _I |` b ) ,
           ( u e. b , v e. b |-> ( tpos _I |` ( u h v ) ) ) >. ) $=
      ( vx vf cvv cv co cbs cfv chom cmpo cop csb eqid csbie cxpc csn ccnv cuni
      cswapf cmpt cid ctpos cres df-swapf wceq wcel wa cxp fvex eqtr4di mpteq1d
      id eqidd mpoeq123dv opeq12d csbeq2dv ovex fveq2 csbeq1d csbeq12dv reseq2d
      xpcbas tposideq2 c1st c2nd simpl xpchom 3eqtr4a mpoeq3ia opeq12i mpoeq3dv
      simpr oveq opeq2d 3eqtr4i 3eqtri 3eqtr4ri a1i eqtr4i ) UEFGJJDFKZGKZUALZE
      DKZMNZCWIONZHEKZHKUBUCUDZUFZBAWLWLIBKZAKZCKZLZIKUBUCUDZUFZPZQZRZRZRZPFGJJ
      DWHEWJCWKUGUHZWLUIZBAWLWLXFWRUIZPZQZRZRZRZPHABICDEFGUJFGJJXMXEXMXEUKWFJUL
      WGJULUMEWHMNZCWHONZXBRZRZCXOHWFMNZWGMNZUNZWMUFZBAXTXTWTPZQZRZXEXMEXNXPYDW
      HMUOZWLXNUKZCXOXBYCYFWNYAXAYBYFHWLXTWMYFWLXNXTYFURWFWGWHXRXSWHSZXRSXSSVHZ
      UPZUQYFBAWLWLWTXTXTWTYIYIYFWTUSUTVAVBTDWHXDXQWFWGUAVCZWIWHUKZEWJXCXNXPWIW
      HMVDZYKCWKXOXBWIWHOVDZVEVFTXMEXNCXOXJRZRZCXOXFXTUIZBAXTXTXHPZQZRZYDDWHXLY
      OYJYKEWJXKXNYNYLYKCWKXOXJYMVEVFTEXNYNYSYEYFCXOXJYRYFXGYPXIYQYFWLXTXFYIVGY
      FBAWLWLXHXTXTXHYIYIYFXHUSUTVAVBTYPBAXTXTXFWOWPXOLZUIZPZQZYABAXTXTIYTWSUFZ
      PZQZYSYDYPYAUUBUUEHXRXSXTXTSVIBAXTXTUUAUUDWOXTULZWPXTULZUMZXFWOVJNWPVJNWF
      ONZLZWOVKNWPVKNWGONZLZUNZUIIUUNWSUFUUAUUDIUUKUUMUUNUUNSVIUUIYTUUNXFUUIXTW
      FWGWHUUJUULXOWOWPYGYHUUJSUULSXOSUUGUUHVLUUGUUHVRVMZVGUUIIYTUUNWSUUOUQVNVO
      VPCXOYRUUCWHOUOZWQXOUKZYQUUBYPUUQBAXTXTXHUUAUUQWRYTXFWOWPWQXOVSZVGVQVTTCX
      OYCUUFUUPUUQYBUUEYAUUQBAXTXTWTUUDUUQIWRYTWSUURUQVQVTTWAWBWCWDVOWE $.

    swapfval.c $e |- ( ph -> C e. U ) $.
    swapfval.d $e |- ( ph -> D e. V ) $.
    ${
      swapfval.s $e |- S = ( C Xc. D ) $.
      swapfval.b $e |- B = ( Base ` S ) $.
      swapfval.h $e |- ( ph -> H = ( Hom ` S ) ) $.
      $( Value of the swap functor.  (Contributed by Zhi Wang, 7-Oct-2025.) $)
      swapfval $p |- ( ph -> ( C swapF D ) = <. ( x e. B |-> U. `' { x } ) ,
             ( u e. B , v e. B |-> ( f e. ( u H v ) |-> U. `' { f } ) ) >. ) $=
        ( cvv cv wceq vc vd vs vb cxpc cbs cfv chom csn ccnv cuni cmpt cmpo cop
        vh co csb cswapf df-swapf a1i ovexd simprl simprr oveq12d eqtr4di fvexd
        simpr fveq2d simplr ad3antrrr eqtr4d mpteq1d mpoeq123dv opeq12d csbied2
        wa oveqd elexd wcel opex ovmpod ) AUAUBFGRRUCUASZUBSZUEUPZUDUCSZUFUGZUO
        WEUHUGZBUDSZBSUIUJUKZULZDCWHWHJDSZCSZUOSZUPZJSUIUJUKZULZUMZUNZUQZUQZUQZ
        BEWIULZDCEEJWKWLKUPZWOULZUMZUNZURRURUAUBRRXAUMTABCDJUOUCUDUAUBUSUTAWBFT
        ZWCGTZVPZVPZUCWDHWTXFRXJWBWCUEVAXJWDFGUEUPHXJWBFWCGUEAXGXHVBAXGXHVCVDOV
        EXJWEHTZVPZUDWFEWSXFRXLWEUFVFXLWFHUFUGEXLWEHUFXJXKVGVHPVEXLWHETZVPZUOWG
        KWRXFRXNWEUHVFXNWGHUHUGZKXNWEHUHXJXKXMVIVHAKXOTXIXKXMQVJVKXNWMKTZVPZWJX
        BWQXEXQBWHEWIXLXMXPVIZVLXQDCWHWHWPEEXDXRXRXQJWNXCWOXQWMKWKWLXNXPVGVQVLV
        MVNVOVOVOAFIMVRAGLNVRXFRVSAXBXEVTUTWA $.
    $}

    ${
      $d C f u v x $.  $d D f u v x $.  $d U f u v x $.  $d V f u v x $.
      $d f ph u v x $.
      $( A swap functor is an ordered pair.  (Contributed by Zhi Wang,
         7-Oct-2025.) $)
      swapfelvv $p |- ( ph -> ( C swapF D ) e. ( _V X. _V ) ) $=
        ( vx vu vv vf co cbs cfv cv csn ccnv cuni cmpt cvv cswapf cxpc chom cop
        cmpo cxp eqid eqidd swapfval fvex mptex mpoex opelvv eqeltrdi ) ABCUALH
        BCUBLZMNZHOPQRZSZIJUPUPKIOJOUOUCNZLKOPQRSZUEZUDTTUFAHJIUPBCUODKUSEFGUOU
        GUPUGAUSUHUIURVAHUPUQUOMUJZUKIJUPUPUTVBVBULUMUN $.
    $}

    swapf2fvala.s $e |- S = ( C Xc. D ) $.
    swapf2fvala.b $e |- B = ( Base ` S ) $.
    ${
      $d C x $.  $d D x $.  $d H x $.  $d S x $.  $d U x $.  $d V x $.
      $d ph x $.
      swapf2fvala.h $e |- ( ph -> H = ( Hom ` S ) ) $.
      $( The morphism part of the swap functor.  See also ~ swapf2fval .
         (Contributed by Zhi Wang, 7-Oct-2025.) $)
      swapf2fvala $p |- ( ph -> ( 2nd ` ( C swapF D ) ) =
                ( u e. B , v e. B |-> ( f e. ( u H v ) |-> U. `' { f } ) ) ) $=
        ( vx co c2nd cv cswapf cfv csn ccnv cuni cmpt cop swapfval fveq2d fvexi
        cmpo cbs mptex mpoex op2nd eqtrdi ) AEFUARZSUBQDQTUCUDUEZUFZCBDDICTBTJR
        ITUCUDUEUFZUKZUGZSUBVAAUQVBSAQBCDEFGHIJKLMNOPUHUIUSVAQDURDGULOUJZUMCBDD
        UTVCVCUNUOUP $.

      swapf2fval.o $e |- ( ph -> ( C swapF D ) = <. O , P >. ) $.
      $( The morphism part of the swap functor.  See also ~ swapf2fvala .
         (Contributed by Zhi Wang, 7-Oct-2025.) $)
      swapf2fval $p |- ( ph -> P =
                ( u e. B , v e. B |-> ( f e. ( u H v ) |-> U. `' { f } ) ) ) $=
        ( cvv cswapf co c2nd cfv cop csn ccnv cuni cmpt cmpo fveq2d swapf2fvala
        cv cxp wcel wceq swapfelvv eqeltrrd opelxp biimpi op2ndg 3syl 3eqtr3rd
        wa ) AEFUAUBZUCUDLGUEZUCUDZCBDDJCUMBUMKUBJUMUFUGUHUIUJGAVEVFUCSUKABCDEF
        HIJKMNOPQRULAVFTTUNZUOZLTUOGTUOVDZVGGUPAVEVFVHSAEFIMNOUQURVIVJLGTTUSUTL
        GTTVAVBVC $.
    $}

    $d B f $.  $d C f $.  $d D f $.  $d O f u v $.  $d P f u v $.  $d S f $.
    $d U f u v $.  $d V f u v $.  $d f ph $.
    $( The object part of the swap functor.  See also ~ swapf1val .
       (Contributed by Zhi Wang, 7-Oct-2025.) $)
    swapf1vala $p |- ( ph -> ( 1st ` ( C swapF D ) ) =
                               ( x e. B |-> U. `' { x } ) ) $=
      ( vu vv vf co c1st cfv cv csn ccnv cuni cmpt chom cmpo cop eqidd swapfval
      cswapf fveq2d cbs fvexi mptex mpoex op1st eqtrdi ) ADEUIPZQRBCBSTUAUBZUCZ
      MNCCOMSNSFUDRZPOSTUAUBUCZUEZUFZQRUSAUQVCQABNMCDEFGOUTHIJKLAUTUGUHUJUSVBBC
      URCFUKLULZUMMNCCVAVDVDUNUOUP $.

    swapf1val.o $e |- ( ph -> ( C swapF D ) = <. O , P >. ) $.
    $( The object part of the swap functor.  See also ~ swapf1vala .
       (Contributed by Zhi Wang, 7-Oct-2025.) $)
    swapf1val $p |- ( ph -> O = ( x e. B |-> U. `' { x } ) ) $=
      ( cswapf c1st cfv cvv wcel co cop cv csn ccnv cuni cmpt fveq2d swapf1vala
      cxp wa wceq swapfelvv eqeltrrd opelxp biimpi op1stg 3syl 3eqtr3rd ) ADEPU
      AZQRIFUBZQRZBCBUCUDUEUFUGIAUTVAQOUHABCDEGHJKLMNUIAVASSUJZTZISTFSTUKZVBIUL
      AUTVAVCOADEHJKLUMUNVDVEIFSSUOUPIFSSUQURUS $.

    $( The morphism part of the swap functor is a function on the Cartesian
       square of the base set.  (Contributed by Zhi Wang, 7-Oct-2025.) $)
    swapf2fn $p |- ( ph -> P Fn ( B X. B ) ) $=
      ( vu vv vf cxp wfn cv chom cfv co csn ccnv cuni cmpt cmpo eqid ovex mptex
      fnmpoi eqidd swapf2fval fneq1d mpbiri ) AEBBRZSOPBBQOTZPTZFUAUBZUCZQTUDUE
      UFZUGZUHZUQSOPBBVCVDVDUIQVAVBURUSUTUJUKULAUQEVDAPOBCDEFGQUTHIJKLMAUTUMNUN
      UOUP $.
  $}

  ${
    $d B u v x $.  $d C u v x $.  $d D u v x $.  $d H f u v $.  $d O u v x $.
    $d P u v x $.  $d S u v x $.  $d X f u v x $.  $d Y f u v $.
    $d ph u v x $.
    swapf1a.o $e |- ( ph -> ( C swapF D ) = <. O , P >. ) $.
    swapf1a.s $e |- S = ( C Xc. D ) $.
    swapf1a.b $e |- B = ( Base ` S ) $.
    swapf1a.x $e |- ( ph -> X e. B ) $.
    $( The object part of the swap functor swaps the objects.  (Contributed by
       Zhi Wang, 7-Oct-2025.) $)
    swapf1a $p |- ( ph -> ( O ` X ) = <. ( 2nd ` X ) , ( 1st ` X ) >. ) $=
      ( vx csn ccnv cuni cfv cvv wceq cbs c2nd c1st cop elxpcbasex1 elxpcbasex2
      cv swapf1val wa simpr sneqd cnveqd unieqd cxp wcel xpcbas eqtr4i eleqtrdi
      eqid 2nd1st syl adantr eqtrd opex a1i fvmptd ) AMHMUFZNZOZPZHUAQZHUBQZUCZ
      BGRAMBCDEFRGRABCDFHJKLUDABCDFHJKLUEJKIUGAVFHSZUHZVIHNZOZPZVLVNVHVPVNVGVOV
      NVFHAVMUIUJUKULAVQVLSZVMAHCTQZDTQZUMZUNVRAHBWALBFTQWAKCDFVSVTJVSURVTURUOU
      PUQHVSVTUSUTVAVBLVLRUNAVJVKVCVDVE $.

    swapf2a.y $e |- ( ph -> Y e. B ) $.
    swapf2a.h $e |- ( ph -> H = ( Hom ` S ) ) $.
    $( The morphism part of the swap functor swaps the morphisms.  (Contributed
       by Zhi Wang, 7-Oct-2025.) $)
    swapf2vala $p |- ( ph -> ( X P Y )
              = ( f e. ( X H Y ) |-> U. `' { f } ) ) $=
      ( vu vv cvv cv csn ccnv cuni cmpt elxpcbasex1 elxpcbasex2 swapf2fval wceq
      co wa simprl simprr oveq12d mpteq1d wcel ovex mptex a1i ovmpod ) ARSJKBBG
      RUAZSUAZHUJZGUAUBUCUDZUEGJKHUJZVDUEZETASRBCDEFTGHITABCDFJMNOUFABCDFJMNOUG
      MNQLUHAVAJUIZVBKUIZUKUKZGVCVEVDVIVAJVBKHAVGVHULAVGVHUMUNUOOPVFTUPAGVEVDJK
      HUQURUSUT $.

    $d B f $.  $d C f $.  $d D f $.  $d F f $.  $d O f $.  $d P f $.  $d S f $.
    $d f ph $.
    swapf2a.f $e |- ( ph -> F e. ( X H Y ) ) $.
    $( The morphism part of the swap functor swaps the morphisms.  (Contributed
       by Zhi Wang, 7-Oct-2025.) $)
    swapf2a $p |- ( ph ->
            ( ( X P Y ) ` F ) = <. ( 2nd ` F ) , ( 1st ` F ) >. ) $=
      ( cfv co vf cv csn ccnv cuni c2nd c1st cop swapf2vala wceq wa simpr sneqd
      cvv cnveqd unieqd chom wcel oveqd eqid xpchom eqtrd eleqtrd 2nd1st adantr
      cxp syl opex a1i fvmptd ) AUAGUAUBZUCZUDZUEZGUFSZGUGSZUHZJKHTZJKETUNABCDE
      FUAHIJKLMNOPQUIAVKGUJZUKZVNGUCZUDZUEZVQVTVMWBVTVLWAVTVKGAVSULUMUOUPAWCVQU
      JZVSAGJUGSKUGSCUQSZTZJUFSKUFSDUQSZTZVFZURWDAGVRWIRAVRJKFUQSZTWIAHWJJKQUSA
      BCDFWEWGWJJKMNWEUTWGUTWJUTOPVAVBVCGWFWHVDVGVEVBRVQUNURAVOVPVHVIVJ $.
  $}

  ${
    $d C u v x $.  $d D u v x $.  $d H f u v $.  $d O u v x $.  $d P u v x $.
    $d S u v $.  $d W f u v $.  $d X f u v x $.  $d Y f u v x $.  $d Z f u v $.
    $d ph u v x $.
    swapf1.o $e |- ( ph -> ( C swapF D ) = <. O , P >. ) $.
    swapf1.x $e |- ( ph -> X e. ( Base ` C ) ) $.
    swapf1.y $e |- ( ph -> Y e. ( Base ` D ) ) $.
    $( The object part of the swap functor swaps the objects.  (Contributed by
       Zhi Wang, 7-Oct-2025.) $)
    swapf1 $p |- ( ph -> ( X O Y ) = <. Y , X >. ) $=
      ( vx co cop cfv csn ccnv cuni cbs cvv eqid df-ov cv cxp elfvexd swapf1val
      cxpc xpcbas wceq simpr sneqd cnveqd unieqd opswap eqtrdi opelxpd wcel a1i
      wa opex fvmptd eqtrid ) AFGELFGMZENGFMZFGEUAAKVBKUBZOZPZQZVCBRNZCRNZUCZES
      AKVJBCDBCUFLZSESAFRBIUDAGRCJUDVKTZBCVKVHVIVLVHTVITUGHUEAVDVBUHZURZVGVBOZP
      ZQVCVNVFVPVNVEVOVNVDVBAVMUIUJUKULFGUMUNAFGVHVIIJUOVCSUPAGFUSUQUTVA $.

    swapf2.z $e |- ( ph -> Z e. ( Base ` C ) ) $.
    swapf2.w $e |- ( ph -> W e. ( Base ` D ) ) $.
    ${
      swapf2val.s $e |- S = ( C Xc. D ) $.
      swapf2val.h $e |- ( ph -> H = ( Hom ` S ) ) $.
      $( The morphism part of the swap functor swaps the morphisms.
         (Contributed by Zhi Wang, 7-Oct-2025.) $)
      swapf2val $p |- ( ph -> ( <. X , Y >. P <. Z , W >. ) =
             ( f e. ( <. X , Y >. H <. Z , W >. ) |-> U. `' { f } ) ) $=
        ( cbs cfv cxp cop eqid xpcbas opelxpd swapf2vala ) ABTUAZCTUAZUBBCDEFGH
        JKUCLIUCMRBCEUHUIRUHUDUIUDUEAJKUHUINOUFALIUHUIPQUFSUG $.
    $}

    $d C f $.  $d D f $.  $d F f $.  $d G f $.  $d O f $.  $d P f $.
    $d f ph $.
    swapf2.f $e |- ( ph -> F e. ( X ( Hom ` C ) Z ) ) $.
    swapf2.g $e |- ( ph -> G e. ( Y ( Hom ` D ) W ) ) $.
    $( The morphism part of the swap functor swaps the morphisms.  (Contributed
       by Zhi Wang, 7-Oct-2025.) $)
    swapf2 $p |- ( ph ->
            ( F ( <. X , Y >. P <. Z , W >. ) G ) = <. G , F >. ) $=
      ( co cfv vf cop df-ov cv csn ccnv cuni cxpc chom cvv eqid eqidd swapf2val
      wceq simpr sneqd cnveqd unieqd opswap eqtrdi cxp opelxpd xpchom2 eleqtrrd
      wa cbs wcel opex a1i fvmptd eqtrid ) AEFIJUBZKHUBZDSZSEFUBZVNTFEUBZEFVNUC
      AUAVOUAUDZUEZUFZUGZVPVLVMBCUHSZUITZSZVNUJABCDWAUAWBGHIJKLMNOPWAUKZAWBULUM
      AVQVOUNZVEZVTVOUEZUFZUGVPWFVSWHWFVRWGWFVQVOAWEUOUPUQUREFUSUTAVOIKBUITZSZJ
      HCUITZSZVAWCAEFWJWLQRVBABCKHWAWIWKWBIJBVFTZCVFTZWDWMUKWNUKWIUKWKUKMNOPWBU
      KVCVDVPUJVGAFEVHVIVJVK $.
  $}

  ${
    $d A x $.  $d B f x $.  $d C f x $.  $d D f x $.  $d H f $.  $d J f $.
    $d O f x $.  $d P f x $.  $d S f x $.  $d T f x $.  $d U x $.  $d V x $.
    $d W f $.  $d X f $.  $d Y f $.  $d Z f $.  $d f ph x $.
    swapf1f1o.o $e |- ( ph -> ( C swapF D ) = <. O , P >. ) $.
    swapf1f1o.s $e |- S = ( C Xc. D ) $.
    swapf1f1o.t $e |- T = ( D Xc. C ) $.
    ${
      swapf1f1o.c $e |- ( ph -> C e. U ) $.
      swapf1f1o.d $e |- ( ph -> D e. V ) $.
      swapf1f1o.b $e |- B = ( Base ` S ) $.
      swapf1f1o.a $e |- A = ( Base ` T ) $.
      $( The object part of the swap functor is a bijection between base sets.
         (Contributed by Zhi Wang, 8-Oct-2025.) $)
      swapf1f1o $p |- ( ph -> O : B -1-1-onto-> A ) $=
        ( vx cbs wf1o cfv cxp cv csn ccnv cuni cmpt eqid xpcbas eqtr4i xpcomf1o
        mpteq1i swapf1val wceq a1i f1oeq123d mpbiri ) ACBJUADTUBZETUBZUCZUTUSUC
        ZSCSUDUEUFUGZUHZUASUSUTVDSCVAVCCGTUBVAQDEGUSUTMUSUIZUTUIZUJUKZUMULACVAB
        VBJVDASCDEFGIJKOPMQLUNCVAUOAVGUPBVBUOABHTUBVBREDHUTUSNVFVEUJUKUPUQUR $.
    $}

    swapf2f1o.h $e |- H = ( Hom ` S ) $.
    swapf2f1o.j $e |- J = ( Hom ` T ) $.
    ${
      swapf2f1o.x $e |- ( ph -> X e. ( Base ` C ) ) $.
      swapf2f1o.y $e |- ( ph -> Y e. ( Base ` D ) ) $.
      swapf2f1o.z $e |- ( ph -> Z e. ( Base ` C ) ) $.
      swapf2f1o.w $e |- ( ph -> W e. ( Base ` D ) ) $.
      $( The morphism part of the swap functor is a bijection between hom-sets.
         (Contributed by Zhi Wang, 8-Oct-2025.) $)
      swapf2f1o $p |- ( ph -> ( <. X , Y >. P <. Z , W >. )
                          : ( <. X , Y >. H <. Z , W >. )
                -1-1-onto-> ( <. Y , X >. J <. W , Z >. ) ) $=
        ( vf cop co wf1o chom cfv cxp csn ccnv cuni cmpt eqid xpcomf1o wceq a1i
        cv swapf2val cbs xpchom2 mpteq1d eqtrd f1oeq123d mpbiri ) AKLUDZMJUDZGU
        EZLKUDJMUDHUEZVFVGDUEZUFKMBUGUHZUEZLJCUGUHZUEZUIZVNVLUIZUCVOUCURUJUKULZ
        UMZUFUCVLVNVRVRUNUOAVHVOVIVPVJVRAVJUCVHVQUMVRABCDEUCGIJKLMNSTUAUBOGEUGU
        HUPAQUQUSAUCVHVOVQABCMJEVKVMGKLBUTUHZCUTUHZOVSUNZVTUNZVKUNZVMUNZSTUAUBQ
        VAZVBVCWEACBJMFVMVKHLKVTVSPWBWAWDWCTSUBUARVAVDVE $.
    $}

    swapf2f1oa.b $e |- B = ( Base ` S ) $.
    swapf2f1oa.x $e |- ( ph -> X e. B ) $.
    swapf2f1oa.y $e |- ( ph -> Y e. B ) $.
    $( The morphism part of the swap functor is a bijection between hom-sets.
       (Contributed by Zhi Wang, 9-Oct-2025.) $)
    swapf2f1oa $p |- ( ph -> ( X P Y ) : ( X H Y )
                     -1-1-onto-> ( ( O ` X ) J ( O ` Y ) ) ) $=
      ( co cfv wf1o c1st c2nd cop cbs cxp wcel xpcbas eqtr4i eleqtrdi xp1st syl
      eqid xp2nd swapf2f1o wceq 1st2nd2 oveq12d swapf1a f1oeq123d mpbird ) AKLH
      UAZKJUBZLJUBZIUAZKLEUAZUCKUDUBZKUEUBZUFZLUDUBZLUEUBZUFZHUAZVJVIUFZVMVLUFZ
      IUAZVKVNEUAZUCACDEFGHIJVMVIVJVLMNOPQAKCUGUBZDUGUBZUHZUIZVIVTUIAKBWBSBFUGU
      BWBRCDFVTWANVTUOWAUOUJUKZULZKVTWAUMUNAWCVJWAUIWEKVTWAUPUNALWBUIZVLVTUIALB
      WBTWDULZLVTWAUMUNAWFVMWAUIWGLVTWAUPUNUQAVDVOVGVRVHVSAKVKLVNEAWCKVKURWEKVT
      WAUSUNZAWFLVNURWGLVTWAUSUNZUTAKVKLVNHWHWIUTAVEVPVFVQIABCDEFJKMNRSVAABCDEF
      JLMNRTVAUTVBVC $.

    $( Alternate proof of ~ swapf2f1oa .  (Contributed by Zhi Wang,
       8-Oct-2025.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    swapf2f1oaALT $p |- ( ph -> ( X P Y ) : ( X H Y )
                        -1-1-onto-> ( ( O ` X ) J ( O ` Y ) ) ) $=
      ( vf co cfv wf1o c1st chom c2nd cxp csn ccnv cuni cmpt eqid xpcomf1o wceq
      cv a1i swapf2vala xpchom mpteq1d eqtrd cbs wf cvv elxpcbasex1 elxpcbasex2
      swapf1f1o f1of syl ffvelcdmd cop swapf1a fveq2d fvex op1st eqtrdi oveq12d
      op2nd xpeq12d f1oeq123d mpbiri ) AKLHUBZKJUCZLJUCZIUBZKLEUBZUDKUEUCZLUEUC
      ZCUFUCZUBZKUGUCZLUGUCZDUFUCZUBZUHZWNWJUHZUAWOUAUPUIUJUKZULZUDUAWJWNWRWRUM
      UNAWBWOWEWPWFWRAWFUAWBWQULWRABCDEFUAHJKLMNRSTHFUFUCUOAPUQURAUAWBWOWQABCDF
      WIWMHKLNRWIUMZWMUMZPSTUSZUTVAXAAWEWCUEUCZWDUEUCZWMUBZWCUGUCZWDUGUCZWIUBZU
      HWPAGVBUCZDCGWMWIIWCWDOXHUMZWTWSQABXHKJABXHJUDBXHJVCAXHBCDEFGVDJVDMNOABCD
      FKNRSVEABCDFKNRSVFRXIVGBXHJVHVIZSVJABXHLJXJTVJUSAXDWNXGWJAXBWKXCWLWMAXBWK
      WGVKZUEUCWKAWCXKUEABCDEFJKMNRSVLZVMWKWGKUGVNZKUEVNZVOVPAXCWLWHVKZUEUCWLAW
      DXOUEABCDEFJLMNRTVLZVMWLWHLUGVNZLUEVNZVOVPVQAXEWGXFWHWIAXEXKUGUCWGAWCXKUG
      XLVMWKWGXMXNVRVPAXFXOUGUCWHAWDXOUGXPVMWLWHXQXRVRVPVQVSVAVTWA $.
  $}

  ${
    $d C m n x y z $.  $d D m n x y z $.  $d O m n x y z $.  $d P m n x y z $.
    $d S m n x y z $.  $d T m n x y z $.  $d m n ph x y z $.
    swapfid.c $e |- ( ph -> C e. Cat ) $.
    swapfid.d $e |- ( ph -> D e. Cat ) $.
    swapfid.s $e |- S = ( C Xc. D ) $.
    swapfid.t $e |- T = ( D Xc. C ) $.
    ${
      swapfid.o $e |- ( ph -> ( C swapF D ) = <. O , P >. ) $.
      ${
        swapfid.x $e |- ( ph -> X e. ( Base ` C ) ) $.
        swapfid.y $e |- ( ph -> Y e. ( Base ` D ) ) $.
        swapfid.1 $e |- .1. = ( Id ` S ) $.
        swapfid.i $e |- I = ( Id ` T ) $.
        $( Each identity morphism in the source category is mapped to the
           corresponding identity morphism in the target category.  See also
           ~ swapfida .  (Contributed by Zhi Wang, 8-Oct-2025.) $)
        swapfid $p |- ( ph -> ( ( <. X , Y >. P <. X , Y >. )
             ` ( .1. ` <. X , Y >. ) ) = ( I ` ( O ` <. X , Y >. ) ) ) $=
          ( cop cfv ccid co cbs eqid xpcid df-ov swapf1 eqtr3id fveq2d wceq a1i
          chom catidcl swapf2 3eqtr2d 3eqtr4rd ) AKJUAZHUBKCUCUBZUBZJBUCUBZUBZU
          AZJKUAZIUBZHUBVEGUBZVEVEDUDZUBZACBKJFHUTVBCUEUBZBUEUBZOMLVJUFZVKUFZUT
          UFZVBUFZTRQUGAVFUSHAVFJKIUDUSJKIUHABCDIJKPQRUIUJUKAVIVCVAUAZVHUBZVCVA
          VHUDZVDAVGVPVHABCJKEGVBUTVKVJNLMVMVLVOVNSQRUGUKVRVQULAVCVAVHUHUMABCDV
          CVAIKJKJPQRQRAVKBVBBUNUBZJVMVSUFVOLQUOAVJCUTCUNUBZKVLVTUFVNMRUOUPUQUR
          $.
      $}

      ${
        swapfida.b $e |- B = ( Base ` S ) $.
        swapfida.x $e |- ( ph -> X e. B ) $.
        ${
          swapfida.1 $e |- .1. = ( Id ` S ) $.
          swapfida.i $e |- I = ( Id ` T ) $.
          $( Each identity morphism in the source category is mapped to the
             corresponding identity morphism in the target category.  See also
             ~ swapfid .  (Contributed by Zhi Wang, 8-Oct-2025.) $)
          swapfida $p |- ( ph -> ( ( X P X )
             ` ( .1. ` X ) ) = ( I ` ( O ` X ) ) ) $=
            ( c1st cfv c2nd cop co cbs cxp wcel eqid xpcbas eqtr4i eleqtrdi syl
            xp1st xp2nd swapfid wceq 1st2nd2 oveq12d fveq2d fveq12d 3eqtr4d ) A
            KUAUBZKUCUBZUDZHUBZVEVEEUEZUBVEJUBZIUBKHUBZKKEUEZUBKJUBZIUBACDEFGHI
            JVCVDLMNOPAKCUFUBZDUFUBZUGZUHZVCVLUHAKBVNRBFUFUBVNQCDFVLVMNVLUIVMUI
            UJUKULZKVLVMUNUMAVOVDVMUHVPKVLVMUOUMSTUPAVIVFVJVGAKVEKVEEAVOKVEUQVP
            KVLVMURUMZVQUSAKVEHVQUTVAAVKVHIAKVEJVQUTUTVB $.
        $}

        swapfcoa.y $e |- ( ph -> Y e. B ) $.
        swapfcoa.z $e |- ( ph -> Z e. B ) $.
        swapfcoa.h $e |- H = ( Hom ` S ) $.
        swapfcoa.m $e |- ( ph -> M e. ( X H Y ) ) $.
        swapfcoa.n $e |- ( ph -> N e. ( Y H Z ) ) $.
        swapfcoa.os $e |- .x. = ( comp ` S ) $.
        swapfcoa.ot $e |- .xb = ( comp ` T ) $.
        $( Composition in the source category is mapped to composition in the
           target. ` ( ph -> C e. Cat ) ` and ` ( ph -> D e. Cat ) ` can be
           replaced by a weaker hypothesis ` ( ph -> S e. Cat ) ` .
           (Contributed by Zhi Wang, 8-Oct-2025.) $)
        swapfcoa $p |- ( ph -> ( ( X P Z ) ` ( N ( <. X , Y >. .x. Z ) M ) ) =
                             ( ( ( Y P Z ) ` N ) ( <. ( O ` X ) , ( O ` Y ) >.
                                  .xb ( O ` Z ) ) ( ( X P Y ) ` M ) ) ) $=
          ( co cfv c1st cop cco c2nd swapf1a fveq2d fvex eqtrdi opeq12d oveq12d
          op1st chom wceq a1i swapf2a oveq123d op2nd cbs eqid wf1o wf swapf1f1o
          ccat f1of syl ffvelcdmd swapf2f1oa xpcco xpccat catcocl eqeltrrd ovex
          opeq12i eqtrd 3eqtr4rd ) ALOPEUKZULZUMULZKNOEUKZULZUMULZNMULZUMULZOMU
          LZUMULZUNZPMULZUMULZDUOULZUKZUKZWIUPULZWLUPULZWNUPULZWPUPULZUNZWSUPUL
          ZCUOULZUKZUKZUNLUPULZKUPULZNUPULZOUPULZUNZPUPULZXAUKZUKZLUMULZKUMULZN
          UMULZOUMULZUNZPUMULZXJUKZUKZUNZWIWLWNWPUNWSGUKUKLKNOUNPIUKUKZNPEUKZUL
          ZAXCXTXLYHAWJXMWMXNXBXSAWRXQWTXRXAAWOXOWQXPAWOXOYCUNZUMULXOAWNYMUMABC
          DEFMNUASUBUCUQZURXOYCNUPUSZNUMUSZVCUTAWQXPYDUNZUMULXPAWPYQUMABCDEFMOU
          ASUBUDUQZURXPYDOUPUSZOUMUSZVCUTVAAWTXRYFUNZUMULXRAWSUUAUMABCDEFMPUASU
          BUEUQZURXRYFPUPUSZPUMUSZVCUTVBAWJXMYAUNZUMULXMAWIUUEUMABCDEFLJMOPUASU
          BUDUEJFVDULVEAUFVFZUHVGZURXMYALUPUSZLUMUSZVCUTAWMXNYBUNZUMULXNAWLUUJU
          MABCDEFKJMNOUASUBUCUDUUFUGVGZURXNYBKUPUSZKUMUSZVCUTVHAXDYAXEYBXKYGAXH
          YEXIYFXJAXFYCXGYDAXFYMUPULYCAWNYMUPYNURXOYCYOYPVIUTAXGYQUPULYDAWPYQUP
          YRURXPYDYSYTVIUTVAAXIUUAUPULYFAWSUUAUPUUBURXRYFUUCUUDVIUTVBAXDUUEUPUL
          YAAWIUUEUPUUGURXMYAUUHUUIVIUTAXEUUJUPULYBAWLUUJUPUUKURXNYBUULUUMVIUTV
          HVAAHVJULZDCXJHXAWLWIHVDULZGWNWPWSTUUNVKZUUOVKZXAVKZXJVKZUJABUUNNMABU
          UNMVLBUUNMVMAUUNBCDEFHVOMVOUASTQRUBUUPVNBUUNMVPVQZUCVRABUUNOMUUTUDVRA
          BUUNPMUUTUEVRANOJUKZWNWPUUOUKZKWKAUVAUVBWKVLUVAUVBWKVMABCDEFHJUUOMNOU
          ASTUFUUQUBUCUDVSUVAUVBWKVPVQUGVRAOPJUKZWPWSUUOUKZLWHAUVCUVDWHVLUVCUVD
          WHVMABCDEFHJUUOMOPUASTUFUUQUBUDUEVSUVCUVDWHVPVQUHVRVTAYLYHXTUNZYKULZY
          IAYJUVEYKABCDXAFXJKLJINOPSUBUFUUSUURUIUCUDUEUGUHVTZURAUVFUVEUPULZUVEU
          MULZUNYIABCDEFUVEJMNPUASUBUCUEUUFAYJUVENPJUKUVGABFIKLJNOPUBUFUIACDFSQ
          RWAUCUDUEUGUHWBWCVGUVHXTUVIYHYHXTYAYBYGWDZXMXNXSWDZVIYHXTUVJUVKVCWEUT
          WFWG $.
      $}

      $( The swap functor is a functor.  (Contributed by Zhi Wang,
         8-Oct-2025.) $)
      swapffunc $p |- ( ph -> O ( S Func T ) P ) $=
        ( cfv eqid ccat cv wcel wa co adantr vx vy vz vm vn cbs cco ccid xpccat
        chom wf1o swapf1f1o f1of syl swapf2fn cswapf cop wceq simprl swapf2f1oa
        simprr simpr swapfida w3a 3ad2ant1 simp21 simp22 simp23 simp3l swapfcoa
        wf simp3r isfuncd ) AUAUBUCEUFMZFUFMZEEUGMZEUHMZUDUEFGDEUJMZFUHMZFUJMZF
        UGMZVNNZVONZVRNZVTNZVQNZVSNZVPNZWANZABCEJHIUIACBFKIHUIAVNVOGUKVNVOGVKAV
        OVNBCDEFOGOLJKHIWBWCULVNVOGUMUNAVNBCDEOGOHIJWBLUOAUAPZVNQZUBPZVNQZRZRZW
        JWLVRSZWJGMWLGMVTSZWJWLDSZUKWPWQWRVKWOVNBCDEFVRVTGWJWLABCUPSGDUQURZWNLT
        JKWDWEWBAWKWMUSAWKWMVAUTWPWQWRUMUNAWKRVNBCDEFVQVSGWJABOQZWKHTACOQZWKITJ
        KAWSWKLTWBAWKVBWFWGVCAWKWMUCPZVNQZVDZUDPZWPQZUEPZWLXBVRSQZRZVDVNBCDEWAF
        VPVRXEXGGWJWLXBAXDWTXIHVEAXDXAXIIVEJKAXDWSXILVEWBAWKWMXCXIVFAWKWMXCXIVG
        AWKWMXCXIVHWDAXDXFXHVIAXDXFXHVLWHWIVJVM $.

      $( The swap functor is a fully faithful functor.  (Contributed by Zhi
         Wang, 8-Oct-2025.) $)
      swapfffth $p |- ( ph -> O ( ( S Full T ) i^i ( S Faith T ) ) P ) $=
        ( vx vy co wbr cv chom cfv eqid cfunc wf1o cbs wral cful cfth swapffunc
        cin wcel wa cswapf cop wceq adantr simprl swapf2f1oa ralrimivva isffth2
        simprr sylanbrc ) AGDEFUAOPMQZNQZERSZOVAGSVBGSFRSZOVAVBDOUBZNEUCSZUDMVF
        UDGDEFUEOEFUFOUHPABCDEFGHIJKLUGAVEMNVFVFAVAVFUIZVBVFUIZUJZUJVFBCDEFVCVD
        GVAVBABCUKOGDULUMVILUNJKVCTZVDTZVFTZAVGVHUOAVGVHUSUPUQMNVFEFGDVCVDVLVJV
        KURUT $.
    $}

    $( The swap functor is a functor.  (Contributed by Zhi Wang,
       9-Oct-2025.) $)
    swapffunca $p |- ( ph -> ( C swapF D ) e. ( S Func T ) ) $=
      ( cswapf co c1st cfv c2nd cop cfunc cvv cxp wcel ccat swapfelvv swapffunc
      wceq 1st2nd2 syl wbr df-br sylib eqeltrd ) ABCJKZUJLMZUJNMZOZDEPKZAUJQQRS
      UJUMUCABCTTFGUAUJQQUDUEZAUKULUNUFUMUNSABCULDEUKFGHIUOUBUKULUNUGUHUI $.

    swapfiso.e $e |- E = ( CatCat ` U ) $.
    swapfiso.u $e |- ( ph -> U e. V ) $.
    swapfiso.s $e |- ( ph -> S e. U ) $.
    swapfiso.t $e |- ( ph -> T e. U ) $.
    ${
      swapfiso.i $e |- I = ( Iso ` E ) $.
      $( The swap functor is an isomorphism between product categories.
         (Contributed by Zhi Wang, 8-Oct-2025.) $)
      swapfiso $p |- ( ph -> ( C swapF D ) e. ( S I T ) ) $=
        ( cfv ccat cswapf co wcel cful cfth cin cbs c1st wf1o c2nd cop cvv wceq
        cxp swapfelvv 1st2nd2 syl wbr swapfffth df-br sylib eqeltrd eqid xpccat
        swapf1f1o elind catcbas eleqtrrd catciso mpbir2and ) ABCUAUBZDEHUBUCVKD
        EUDUBDEUEUBUFZUCDUGSZEUGSZVKUHSZUIAVKVOVKUJSZUKZVLAVKULULUNUCVKVQUMABCT
        TJKUOVKULULUPUQZAVOVPVLURVQVLUCABCVPDEVOJKLMVRUSVOVPVLUTVAVBAVNVMBCVPDE
        TVOTVRLMJKVMVCZVNVCZVEAGUGSZGVMVNFVKHIDENWAVCZVSVTOADFTUFZWAAFTDPABCDLJ
        KVDVFAWAGFINWBOVGZVHAEWCWAAFTEQACBEMKJVDVFWDVHRVIVJ $.
    $}

    $( The product category is categorically isomorphic to the swapped product
       category.  (Contributed by Zhi Wang, 8-Oct-2025.) $)
    swapciso $p |- ( ph -> S ( ~=c ` E ) T ) $=
      ( cfv eqid wcel ccat cbs cswapf ciso catccat syl cin xpccat elind catcbas
      co eleqtrrd swapfiso brcici ) AGUAQZGBCUBUJGUCQZDEUORZUNRZAFHSGTSNGFHMUDU
      EADFTUFZUNAFTDOABCDKIJUGUHAUNGFHMUQNUIZUKAEURUNAFTEPACBELJIUGUHUSUKABCDEF
      GUOHIJKLMNOPUPULUM $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Functor evaluation
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d C x y $.  $d D x y $.  $d F x $.  $d O x y $.  $d P x y $.
    $d b c d x y $.  $d ph x y $.
    oppc1stf.o $e |- O = ( oppCat ` C ) $.
    oppc1stf.p $e |- P = ( oppCat ` D ) $.
    oppc1stf.c $e |- ( ph -> C e. V ) $.
    oppc1stf.d $e |- ( ph -> D e. W ) $.
    ${
      oppc1stflem.1 $e |- ( ( ph /\ ( C e. Cat /\ D e. Cat ) ) ->
        ( oppFunc ` ( C F D ) ) = ( O F P ) ) $.
      oppc1stflem.f $e |- F = ( c e. Cat , d e. Cat |-> Y ) $.
      $( A utility theorem for proving theorems on projection functors of
         opposite categories.  (Contributed by Zhi Wang, 19-Nov-2025.) $)
      oppc1stflem $p |- ( ph -> ( oppFunc ` ( C F D ) ) = ( O F P ) ) $=
        ( wcel wa ccat vx co coppf cfv cv wne c2nd wrel cdm simpr eloppf simpld
        c0 eqid mpondm0 necon1ai syl simplr wceq adantlr eleqtrd mpdan oppccatb
        anbi12d biimprd elmpocl impel eleqtrrd impbida eqrdv ) AUABCEUBZUCUDZFD
        EUBZAUAUEZVLRZVNVMRZAVOSZBTRZCTRZSZVPVQVKUMUFZVTVQWAVKUGUDZUHWBUIUHSVQV
        KVLVNVLUNAVOUJUKULVTVKUMJKIEBCTTQUOUPUQVQVTSVNVLVMAVOVTURAVTVLVMUSZVOPU
        TVAVBAVPSZVTVOAFTRZDTRZSZVTVPAVTWGAVRWEVSWFABFGLNVCACDHMOVCVDVEJKTTIFDE
        VNQVFVGWDVTSVNVMVLAVPVTURAVTWCVPPUTVHVBVIVJ $.
    $}

    $( The opposite functor of the first projection functor is the first
       projection functor of opposite categories.  (Contributed by Zhi Wang,
       19-Nov-2025.) $)
    oppc1stf $p |- ( ph -> ( oppFunc ` ( C 1stF D ) ) = ( O 1stF P ) ) $=
      ( vx vy cv cfv c1st co chom wcel eqid vb vc vd cbs cxp cres cxpc cmpo cop
      c1stf csb ccat wa ctpos coppf tposmpo c2nd oppchom xpeq12i oppcbas xpcbas
      simp2 simp3 xpchom 3eqtr4a reseq2d mpoeq3dva eqtr4id opeq2d simprl simprr
      w3a 1stfval 1stfcl oppfval3 oppccat syl 3eqtr4d df-1stf oppc1stflem ) ABC
      DUJEFGUAUBNZUDOUCNZUDOUEPUANZUFLMWCWCPLNZMNZWAWBUGQROQUFUHUIUKUBUCHIJKABU
      LSZCULSZUMUMZPBUDOZCUDOZUEZUFZLMWKWKPWDWEBCUGQZROZQZUFZUHZUNZUIWLMLWKWKPW
      EWDEDUGQZROZQZUFZUHZUIBCUJQZUOOEDUJQZWHWRXCWLWHWRMLWKWKWPUHXCLMWKWKWPWQWQ
      TUPWHMLWKWKXBWPWHWEWKSZWDWKSZVLZXAWOPXHWEPOZWDPOZEROZQZWEUQOZWDUQOZDROZQZ
      UEXJXIBROZQZXNXMCROZQZUEXAWOXLXRXPXTBXQEXIXJXQTZHURCXSDXMXNXSTZIURUSXHWKE
      DWSXKXOWTWEWDWSTZEDWSWIWJYCWIBEHWITZUTWJCDIWJTZUTVAZXKTXOTWTTZWHXFXGVBZWH
      XFXGVCZVDXHWKBCWMXQXSWNWDWEWMTZBCWMWIWJYJYDYEVAZYAYBWNTZYIYHVDVEVFVGVHVIW
      HWMBXDWLWQWHLMWKBCXDWMWNYJYKYLAWFWGVJZAWFWGVKZXDTZVMWHBCXDWMYJYMYNYOVNVOW
      HMLWKEDXEWSWTYCYFYGWHWFEULSYMBEHVPVQWHWGDULSYNCDIVPVQXETVMVRLMUCUBUAVSVT
      $.

    $( The opposite functor of the second projection functor is the second
       projection functor of opposite categories.  (Contributed by Zhi Wang,
       19-Nov-2025.) $)
    oppc2ndf $p |- ( ph -> ( oppFunc ` ( C 2ndF D ) ) = ( O 2ndF P ) ) $=
      ( vx vy cv cfv c2nd co chom wcel eqid vb vc vd cbs cxp cres cxpc cmpo cop
      c2ndf csb ccat wa ctpos coppf tposmpo c1st oppchom xpeq12i oppcbas xpcbas
      simp2 simp3 xpchom 3eqtr4a reseq2d mpoeq3dva eqtr4id opeq2d simprl simprr
      w3a 2ndfval 2ndfcl oppfval3 oppccat syl 3eqtr4d df-2ndf oppc1stflem ) ABC
      DUJEFGUAUBNZUDOUCNZUDOUEPUANZUFLMWCWCPLNZMNZWAWBUGQROQUFUHUIUKUBUCHIJKABU
      LSZCULSZUMUMZPBUDOZCUDOZUEZUFZLMWKWKPWDWEBCUGQZROZQZUFZUHZUNZUIWLMLWKWKPW
      EWDEDUGQZROZQZUFZUHZUIBCUJQZUOOEDUJQZWHWRXCWLWHWRMLWKWKWPUHXCLMWKWKWPWQWQ
      TUPWHMLWKWKXBWPWHWEWKSZWDWKSZVLZXAWOPXHWEUQOZWDUQOZEROZQZWEPOZWDPOZDROZQZ
      UEXJXIBROZQZXNXMCROZQZUEXAWOXLXRXPXTBXQEXIXJXQTZHURCXSDXMXNXSTZIURUSXHWKE
      DWSXKXOWTWEWDWSTZEDWSWIWJYCWIBEHWITZUTWJCDIWJTZUTVAZXKTXOTWTTZWHXFXGVBZWH
      XFXGVCZVDXHWKBCWMXQXSWNWDWEWMTZBCWMWIWJYJYDYEVAZYAYBWNTZYIYHVDVEVFVGVHVIW
      HWMCXDWLWQWHLMWKBCXDWMWNYJYKYLAWFWGVJZAWFWGVKZXDTZVMWHBCXDWMYJYMYNYOVNVOW
      HMLWKEDXEWSWTYCYFYGWHWFEULSYMBEHVPVQWHWGDULSYNCDIVPVQXETVMVRLMUCUBUAVSVT
      $.
  $}

  ${
    $d A x y $.  $d B x y $.  $d C x y $.  $d D x y $.  $d ph x y $.
    1stfpropd.1 $e |- ( ph -> ( Homf ` A ) = ( Homf ` B ) ) $.
    1stfpropd.2 $e |- ( ph -> ( comf ` A ) = ( comf ` B ) ) $.
    1stfpropd.3 $e |- ( ph -> ( Homf ` C ) = ( Homf ` D ) ) $.
    1stfpropd.4 $e |- ( ph -> ( comf ` C ) = ( comf ` D ) ) $.
    1stfpropd.a $e |- ( ph -> A e. Cat ) $.
    1stfpropd.b $e |- ( ph -> B e. Cat ) $.
    1stfpropd.c $e |- ( ph -> C e. Cat ) $.
    1stfpropd.d $e |- ( ph -> D e. Cat ) $.
    $( If two categories have the same set of objects, morphisms, and
       compositions, then they have same first projection functors.
       (Contributed by Zhi Wang, 20-Nov-2025.) $)
    1stfpropd $p |- ( ph -> ( A 1stF C ) = ( B 1stF D ) ) $=
      ( vx vy c1st co cfv cres eqid cxpc cbs cv chom cmpo cop c1stf ccat fveq2d
      xpcpropd reseq2d oveqd mpoeq123dv opeq12d 1stfval 3eqtr4d ) APBDUAQZUBRZS
      ZNOURURPNUCZOUCZUQUDRZQZSZUEZUFPCEUAQZUBRZSZNOVGVGPUTVAVFUDRZQZSZUEZUFBDU
      GQZCEUGQZAUSVHVEVLAURVGPAUQVFUBABCDEUHFGHIJKLMUJZUIZUKANOURURVDVGVGVKVPVP
      AVCVJPAVBVIUTVAAUQVFUDVOUIULUKUMUNANOURBDVMUQVBUQTURTVBTJLVMTUOANOVGCEVNV
      FVIVFTVGTVITKMVNTUOUP $.

    $( If two categories have the same set of objects, morphisms, and
       compositions, then they have same second projection functors.
       (Contributed by Zhi Wang, 20-Nov-2025.) $)
    2ndfpropd $p |- ( ph -> ( A 2ndF C ) = ( B 2ndF D ) ) $=
      ( vx vy c2nd co cfv cres eqid cxpc cbs cv chom cmpo cop c2ndf ccat fveq2d
      xpcpropd reseq2d oveqd mpoeq123dv opeq12d 2ndfval 3eqtr4d ) APBDUAQZUBRZS
      ZNOURURPNUCZOUCZUQUDRZQZSZUEZUFPCEUAQZUBRZSZNOVGVGPUTVAVFUDRZQZSZUEZUFBDU
      GQZCEUGQZAUSVHVEVLAURVGPAUQVFUBABCDEUHFGHIJKLMUJZUIZUKANOURURVDVGVGVKVPVP
      AVCVJPAVBVIUTVAAUQVFUDVOUIULUKUMUNANOURBDVMUQVBUQTURTVBTJLVMTUOANOVGCEVNV
      FVIVFTVGTVITKMVNTUOUP $.

    $( If two categories have the same set of objects, morphisms, and
       compositions, then they have same diagonal functors.  (Contributed by
       Zhi Wang, 20-Nov-2025.) $)
    diagpropd $p |- ( ph -> ( A DiagFunc C ) = ( B DiagFunc D ) ) $=
      ( cop c1stf co ccurf cdiag eqid diagval 1stfcl curfpropd 1stfpropd oveq2d
      cxpc eqtr4d 3eqtr4d ) ABDNBDOPZQPCENZUHQPZBDRPZCERPZABCDEBUHFGHIJKLMABDUH
      BDUEPZUMSJLUHSUAUBABDUKUKSJLTAULUICEOPZQPUJACEULULSKMTAUHUNUIQABCDEFGHIJK
      LMUCUDUFUG $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Transposed curry functors
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    cofuswapf1.c $e |- ( ph -> C e. Cat ) $.
    cofuswapf1.d $e |- ( ph -> D e. Cat ) $.
    cofuswapf1.f $e |- ( ph -> F e. ( ( D Xc. C ) Func E ) ) $.
    cofuswapf1.g $e |- ( ph -> G = ( F o.func ( C swapF D ) ) ) $.
    $( The bifunctor pre-composed with a swap functor is a bifunctor.
       (Contributed by Zhi Wang, 10-Oct-2025.) $)
    cofuswapfcl $p |- ( ph -> G e. ( ( C Xc. D ) Func E ) ) $=
      ( cswapf co ccofu cxpc cfunc eqid swapffunca cofucl eqeltrd ) AFEBCKLZMLB
      CNLZDOLJAUACBNLZDTEABCUAUBGHUAPUBPQIRS $.

    cofuswapf1.a $e |- A = ( Base ` C ) $.
    cofuswapf1.b $e |- B = ( Base ` D ) $.
    cofuswapf1.x $e |- ( ph -> X e. A ) $.
    cofuswapf1.y $e |- ( ph -> Y e. B ) $.
    $( The object part of a bifunctor pre-composed with a swap functor.
       (Contributed by Zhi Wang, 9-Oct-2025.) $)
    cofuswapf1 $p |- ( ph -> ( X ( 1st ` G ) Y ) = ( Y ( 1st ` F ) X ) ) $=
      ( cfv co c1st cop cswapf ccofu df-ov fveq2d fveq1d eqtrid cxp cxpc xpcbas
      eqid swapffunca opelxpd c2nd cvv wcel wceq ccat swapfelvv 1st2nd2 syl cbs
      cofu1 eleqtrdi swapf1 eqtr3id 3eqtrd eqtr4di ) AIJHUASZTZJIUBZGUASZSZJIVM
      TAVKIJUBZGDEUCTZUDTZUASZSZVOVPUASZSZVMSVNAVKVOVJSVSIJVJUEAVOVJVRAHVQUANUF
      UGUHABCUIDEUJTZEDUJTZFVPGVODEWBBCWBULZOPUKADEWBWCKLWDWCULUMMAIJBCQRUNVDAW
      AVLVMAWAIJVTTVLIJVTUEADEVPUOSZVTIJAVPUPUPUIUQVPVTWEUBURADEUSUSKLUTVPUPUPV
      AVBAIBDVCSQOVEAJCEVCSRPVEVFVGUFVHJIVMUEVI $.

    cofuswapf2.z $e |- ( ph -> Z e. A ) $.
    cofuswapf2.w $e |- ( ph -> W e. B ) $.
    cofuswapf2.h $e |- H = ( Hom ` C ) $.
    cofuswapf2.j $e |- J = ( Hom ` D ) $.
    cofuswapf2.m $e |- ( ph -> M e. ( X H Z ) ) $.
    cofuswapf2.n $e |- ( ph -> N e. ( Y J W ) ) $.
    $( The morphism part of a bifunctor pre-composed with a swap functor.
       (Contributed by Zhi Wang, 9-Oct-2025.) $)
    cofuswapf2 $p |- ( ph -> ( M ( <. X , Y >. ( 2nd ` G ) <. Z , W >. ) N )
                      = ( N ( <. Y , X >. ( 2nd ` F ) <. W , Z >. ) M ) ) $=
      ( cop c2nd cfv co cswapf ccofu c1st fveq2d oveqd df-ov cxp cxpc chom eqid
      xpcbas swapffunca opelxpd xpchom2 eleqtrrd eqtrid cvv wcel wceq swapfelvv
      cofu2 ccat 1st2nd2 syl cbs eleqtrdi swapf1 eqtr3id oveq12d swapf2 fveq12d
      oveqi 3eqtrd eqtr4di ) AKLNOUKZPMUKZHULUMZUNZUNZLKUKZONUKZMPUKZGULUMZUNZU
      MZLKWRUNAWMKLWIWJGDEUOUNZUPUNZULUMZUNZUNZKLUKZWIWJWTULUMZUNZUMZWIWTUQUMZU
      MZWJXIUMZWQUNZUMZWSAWLXCKLAWKXBWIWJAHXAULTURUSUSAXDXEXCUMXMKLXCUTABCVADEV
      BUNZEDVBUNZXEFWTGXNVCUMZWIWJDEXNBCXNVDZUAUBVEADEXNXOQRXQXOVDVFSANOBCUCUDV
      GAPMBCUEUFVGXPVDZAXENPIUNZOMJUNZVAWIWJXPUNAKLXSXTUIUJVGADEPMXNIJXPNOBCXQU
      AUBUGUHUCUDUEUFXRVHVIVOVJAXHWNXLWRAXJWOXKWPWQAXJNOXIUNWONOXIUTADEXFXINOAW
      TVKVKVAVLWTXIXFUKVMADEVPVPQRVNWTVKVKVQVRZANBDVSUMZUCUAVTZAOCEVSUMZUDUBVTZ
      WAWBAXKPMXIUNWPPMXIUTADEXFXIPMYAAPBYBUEUAVTZAMCYDUFUBVTZWAWBWCAXHKLXGUNWN
      KLXGUTADEXFKLXIMNOPYAYCYEYFYGAKXSNPDVCUMZUNUIIYHNPUGWFVTALXTOMEVCUMZUNUJJ
      YIOMUHWFVTWDWBWEWGLKWRUTWH $.
  $}

  ${
    $d .1. g y z $.  $d A y $.  $d B g y z $.  $d C g y z $.  $d D g y z $.
    $d E g y z $.  $d F g y z $.  $d J g $.  $d X g y z $.  $d g ph y z $.
    tposcurf1.g $e |- ( ph -> G = ( <. C , D >. curryF
                ( F o.func ( C swapF D ) ) ) ) $.
    tposcurf1.a $e |- A = ( Base ` C ) $.
    tposcurf1.c $e |- ( ph -> C e. Cat ) $.
    tposcurf1.d $e |- ( ph -> D e. Cat ) $.
    tposcurf1.f $e |- ( ph -> F e. ( ( D Xc. C ) Func E ) ) $.
    tposcurf1.x $e |- ( ph -> X e. A ) $.
    tposcurf1.k $e |- ( ph -> K = ( ( 1st ` G ) ` X ) ) $.
    $( The partially evaluated transposed curry functor is a functor.
       (Contributed by Zhi Wang, 9-Oct-2025.) $)
    tposcurf1cl $p |- ( ph -> K e. ( D Func E ) ) $=
      ( co c1st cfv eqid cop cswapf ccofu ccurf cfunc fveq2d fveq1d eqtrd eqidd
      cbs cofuswapfcl curf1cl eqeltrd ) AHICDUAFCDUBQUCQZUDQZRSZSZDEUEQAHIGRSZS
      UQPAIURUPAGUORJUFUGUHABDUJSZCDEUNUOUQIUOTKLMACDEFUNLMNAUNUIUKUSTOUQTULUM
      $.

    tposcurf1.b $e |- B = ( Base ` D ) $.
    ${
      tposcurf11.y $e |- ( ph -> Y e. B ) $.
      $( Value of the double evaluated transposed curry functor.  (Contributed
         by Zhi Wang, 9-Oct-2025.) $)
      tposcurf11 $p |- ( ph -> ( ( 1st ` K ) ` Y ) = ( Y ( 1st ` F ) X ) ) $=
        ( c1st cfv cop cswapf ccofu ccurf fveq2d fveq1d eqtrd eqidd cofuswapfcl
        co eqid curf11 cofuswapf1 3eqtrd ) AKIUAUBZUBKJDEUCGDEUDULUEULZUFULZUAU
        BZUBZUAUBZUBJKURUAUBULKJGUAUBULAKUQVBAIVAUAAIJHUAUBZUBVARAJVCUTAHUSUALU
        GUHUIUGUHABCDEFURUSVAJKUSUMMNOADEFGURNOPAURUJZUKSQVAUMTUNABCDEFGURJKNOP
        VDMSQTUOUP $.

      tposcurf12.j $e |- J = ( Hom ` D ) $.
      tposcurf12.1 $e |- .1. = ( Id ` C ) $.
      tposcurf12.y $e |- ( ph -> Z e. B ) $.
      tposcurf12.g $e |- ( ph -> H e. ( Y J Z ) ) $.
      $( The partially evaluated transposed curry functor at a morphism.
         (Contributed by Zhi Wang, 9-Oct-2025.) $)
      tposcurf12 $p |- ( ph -> ( ( Y ( 2nd ` K ) Z ) ` H ) =
        ( H ( <. Y , X >. ( 2nd ` F ) <. Z , X >. ) ( .1. ` X ) ) ) $=
        ( c2nd cfv co cop cswapf ccofu ccurf c1st fveq2d eqtrd oveqd eqid eqidd
        fveq1d cofuswapfcl curf12 chom catidcl cofuswapf2 3eqtrd ) AJNOLUIUJZUK
        ZUJJNOMDEULHDEUMUKUNUKZUOUKZUPUJZUJZUIUJZUKZUJMFUJZJMNULMOULVKUIUJUKUKJ
        VQNMULOMULHUIUJUKUKAJVJVPAVIVONOALVNUIALMIUPUJZUJVNUBAMVRVMAIVLUPPUQVBU
        RUQUSVBABCDEFGVKVLJKVNMNOVLUTQRSADEGHVKRSTAVKVAZVCUCUAVNUTUDUEUFUGUHVDA
        BCDEGHVKDVEUJZKVQJOMNMRSTVSQUCUAUDUAUGVTUTZUEABDFVTMQWAUFRUAVFUHVGVH $.
    $}

    ${
      tposcurf1.j $e |- J = ( Hom ` D ) $.
      tposcurf1.1 $e |- .1. = ( Id ` C ) $.
      $( Value of the object part of the transposed curry functor.
         (Contributed by Zhi Wang, 9-Oct-2025.) $)
      tposcurf1 $p |- ( ph -> K = <. ( y e. B |-> ( y ( 1st ` F ) X ) ) ,
       ( y e. B , z e. B |-> ( g e. ( y J z ) |->
         ( g ( <. y , X >. ( 2nd ` F ) <. z , X >. ) ( .1. ` X ) ) ) ) >. ) $=
        ( cv cswapf ccofu c1st cfv cmpt cop c2nd cmpo ccurf fveq2d fveq1d eqidd
        co eqid cofuswapfcl curf1 3eqtrd wcel wa cvv wceq cbs fvexi mptex mpoex
        op1std syl ovexd fvmpt2d adantr ccat cxpc cfunc simpr tposcurf11 eqtr3d
        mpteq2dva op2ndd ovex ovmpt4d ad2antrr simplrl simplrr tposcurf12 3impb
        a1i mpoeq3dva opeq12d eqtrd ) ANBEOBUFZKFGUGUSUHUSZUIUJZUSZUKZBCEEIWPCU
        FZMUSZOHUJZIUFZOWPULOXAULWQUMUJUSZUSZUKZUNZULZBEWPOKUIUJUSZUKZBCEEIXBXD
        XCWPOULXAOULKUMUJUSUSZUKZUNZULANOLUIUJZUJZOFGULWQUOUSZUIUJZUJZXIUBAOXOX
        RALXQUIPUPUQABCDEFGHIJWQXQMXSOXQUTQRSAFGJKWQRSTAWQURVAUCUAXSUTUDUEVBVCZ
        AWTXKXHXNABEWSXJAWPEVDZVEZWPNUIUJZUJWSXJABEWSYCVFANXIVGZYCWTVGXTWTXHNBE
        WSEGVHUCVIZVJZBCEEXGYEYEVKZVLVMYBOWPWRVNVOYBDEFGJKLNOWPALXQVGZYAPVPQAFV
        QVDZYARVPAGVQVDZYASVPAKGFVRUSJVSUSVDZYATVPAODVDZYAUAVPANXPVGZYAUBVPUCAY
        AVTWAWBWCABCEEXGXMAYAXAEVDZXGXMVGAYAYNVEZVEZIXBXFXLYPXDXBVDZVEZXDWPXANU
        MUJZUSZUJXFXLYPIXBXFYTVFABCEEXGYSVFAYDYSXHVGXTWTXHNYFYGWDVMXGVFVDYPIXBX
        FWPXAMWEVJWLWFYRXCXDXEVNVOYRDEFGHJKLXDMNOWPXAAYHYOYQPWGQAYIYOYQRWGAYJYO
        YQSWGAYKYOYQTWGAYLYOYQUAWGAYMYOYQUBWGUCAYAYNYQWHUDUEAYAYNYQWIYPYQVTWJWB
        WCWKWMWNWO $.
    $}
  $}

  ${
    $d B z $.  $d C z $.  $d D z $.  $d E z $.  $d F z $.  $d H z $.  $d I z $.
    $d K z $.  $d X z $.  $d Y z $.  $d Z z $.  $d ph z $.
    tposcurf2.g $e |- ( ph -> G = ( <. C , D >. curryF
                ( F o.func ( C swapF D ) ) ) ) $.
    tposcurf2.a $e |- A = ( Base ` C ) $.
    tposcurf2.c $e |- ( ph -> C e. Cat ) $.
    tposcurf2.d $e |- ( ph -> D e. Cat ) $.
    tposcurf2.f $e |- ( ph -> F e. ( ( D Xc. C ) Func E ) ) $.
    tposcurf2.b $e |- B = ( Base ` D ) $.
    tposcurf2.h $e |- H = ( Hom ` C ) $.
    tposcurf2.i $e |- I = ( Id ` D ) $.
    tposcurf2.x $e |- ( ph -> X e. A ) $.
    tposcurf2.y $e |- ( ph -> Y e. A ) $.
    tposcurf2.k $e |- ( ph -> K e. ( X H Y ) ) $.
    tposcurf2.l $e |- ( ph -> L = ( ( X ( 2nd ` G ) Y ) ` K ) ) $.
    $( Value of the transposed curry functor at a morphism.  (Contributed by
       Zhi Wang, 10-Oct-2025.) $)
    tposcurf2 $p |- ( ph -> L = ( z e. B |->
      ( ( I ` z ) ( <. z , X >. ( 2nd ` F ) <. z , Y >. ) K ) ) ) $=
      ( cop cswapf co ccofu ccurf c2nd cfv cmpt fveq2d oveqd fveq1d eqtrd eqidd
      cv eqid cofuswapfcl curf2 wcel wa chom ccat adantr cfunc simpr cofuswapf2
      cxpc catidcl mpteq2dva 3eqtrd ) AMLNOEFUHHEFUIUJUKUJZULUJZUMUNZUJZUNZBDLB
      VAZKUNZNWBUHOWBUHVQUMUNUJUJZUOBDWCLWBNUHWBOUHHUMUNUJUJZUOAMLNOIUMUNZUJZUN
      WAUGALWGVTAWFVSNOAIVRUMPUPUQURUSABCDEFGVQVRJKLWANOVRVBQRSAEFGHVQRSTAVQUTV
      CUAUBUCUDUEUFWAVBVDABDWDWEAWBDVEZVFZCDEFGHVQJFVGUNZLWCWBNWBOAEVHVEWHRVIAF
      VHVEWHSVIZAHFEVMUJGVJUJVEWHTVIWIVQUTQUAANCVEWHUDVIAWHVKZAOCVEWHUEVIWLUBWJ
      VBZALNOJUJVEWHUFVIWIDFKWJWBUAWMUCWKWLVNVLVOVP $.

    ${
      tposcurf2.z $e |- ( ph -> Z e. B ) $.
      $( Value of a component of the transposed curry functor natural
         transformation.  (Contributed by Zhi Wang, 10-Oct-2025.) $)
      tposcurf2val $p |- ( ph -> ( L ` Z ) =
        ( ( I ` Z ) ( <. Z , X >. ( 2nd ` F ) <. Z , Y >. ) K ) ) $=
        ( vz cv cfv cop c2nd co cvv tposcurf2 wceq wa simpr opeq1d fveq2d eqidd
        oveq12d oveq123d ovexd fvmptd ) AUIOUIUJZJUKZKVGMULZVGNULZGUMUKZUNZUNOJ
        UKZKOMULZONULZVKUNZUNCLUOAUIBCDEFGHIJKLMNPQRSTUAUBUCUDUEUFUGUPAVGOUQZUR
        ZVHVMKKVLVPVRVIVNVJVOVKVRVGOMAVQUSZUTVRVGONVSUTVCVRVGOJVSVAVRKVBVDUHAVM
        KVPVEVF $.
    $}

    tposcurf2.n $e |- N = ( D Nat E ) $.
    $( The transposed curry functor at a morphism is a natural transformation.
       (Contributed by Zhi Wang, 10-Oct-2025.) $)
    tposcurf2cl $p |- ( ph ->
      L e. ( ( ( 1st ` G ) ` X ) N ( ( 1st ` G ) ` Y ) ) ) $=
      ( cop cswapf co ccofu ccurf c2nd cfv c1st eqid cofuswapfcl curf2cl fveq2d
      eqidd oveqd fveq1d eqtrd oveq12d 3eltr4d ) AKNODEUIGDEUJUKULUKZUMUKZUNUOZ
      UKZUOZNVHUPUOZUOZOVLUOZMUKLNHUPUOZUOZOVOUOZMUKABCDEFVGVHIJKVKMNOVHUQQRSAD
      EFGVGRSTAVGVAURUAUBUCUDUEUFVKUQUHUSALKNOHUNUOZUKZUOVKUGAKVSVJAVRVINOAHVHU
      NPUTVBVCVDAVPVMVQVNMANVOVLAHVHUPPUTZVCAOVOVLVTVCVEVF $.
  $}

  ${
    tposcurfcl.g $e |- ( ph -> G = ( <. C , D >. curryF
                ( F o.func ( C swapF D ) ) ) ) $.
    tposcurfcl.q $e |- Q = ( D FuncCat E ) $.
    tposcurfcl.c $e |- ( ph -> C e. Cat ) $.
    tposcurfcl.d $e |- ( ph -> D e. Cat ) $.
    tposcurfcl.f $e |- ( ph -> F e. ( ( D Xc. C ) Func E ) ) $.
    $( The transposed curry functor of a functor ` F : D X. C --> E ` is a
       functor tposcurry ` ( F ) : C --> ( D --> E ) ` .  (Contributed by Zhi
       Wang, 9-Oct-2025.) $)
    tposcurfcl $p |- ( ph -> G e. ( C Func Q ) ) $=
      ( cop cswapf co ccofu ccurf cfunc eqid eqidd cofuswapfcl curfcl eqeltrd )
      AGBCMFBCNOPOZQOZBDROHABCDEUDUEUESIJKABCEFUDJKLAUDTUAUBUC $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Constant functors
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d B f y z $.  $d J f $.  $d K f y z $.  $d f ph y z $.
    diag1.l $e |- L = ( C DiagFunc D ) $.
    diag1.c $e |- ( ph -> C e. Cat ) $.
    diag1.d $e |- ( ph -> D e. Cat ) $.
    diag1.a $e |- A = ( Base ` C ) $.
    diag1.x $e |- ( ph -> X e. A ) $.
    diag1.k $e |- K = ( ( 1st ` L ) ` X ) $.
    diag1.b $e |- B = ( Base ` D ) $.
    diag1.j $e |- J = ( Hom ` D ) $.
    diag1.i $e |- .1. = ( Id ` C ) $.
    $( The constant functor of ` X ` .  Example 3.20(2) of [Adamek] p. 30.
       (Contributed by Zhi Wang, 17-Oct-2025.) $)
    diag1 $p |- ( ph -> K = <. ( y e. B |-> X ) ,
       ( y e. B , z e. B |-> ( f e. ( y J z ) |-> ( .1. ` X ) ) ) >. ) $=
      ( c1st cfv c2nd cop cmpt cv co cmpo wrel wcel wceq relfunc diag1cl 1st2nd
      cfunc sylancr wbr 1st2ndbr funcf1 feqmptd wa ccat adantr diag11 mpteq2dva
      simpr eqtrd cxp wfn funcfn2 fnov sylib w3a chom eqid 3ad2ant1 simp2 simp3
      funcf2 simpl1 syl diag12 mpoeq3dva opeq12d ) AKKUCUDZKUEUDZUFZBEMUGZBCEEI
      BUHZCUHZJUIZMHUDZUGZUJZUFAGFUQUIZUKZKWQULZKWIUMGFUNZADFGKLMNOPQRSUOZKWQUP
      URAWGWJWHWPAWGBEWKWGUDZUGWJABEDWGAEDGFWGWHTQAWRWSWGWHWQUSZWTXAKWQUTURZVAV
      BABEXBMAWKEULZVCDEFGKLMWKNAFVDULZXEOVEAGVDULZXEPVEQAMDULZXERVESTAXEVHVFVG
      VIAWHBCEEWKWLWHUIZUJZWPAWHEEVJVKWHXJUMAEGFWGWHTXDVLBCEEWHVMVNABCEEXIWOAXE
      WLEULZVOZXIIWMIUHZXIUDZUGWOXLIWMXBWLWGUDFVPUDZUIXIXLEGFWGWHJXOWKWLTUAXOVQ
      AXEXCXKXDVRAXEXKVSZAXEXKVTZWAVBXLIWMXNWNXLXMWMULZVCZDEFGHXMJKLMWKWLNXSAXF
      AXEXKXRWBZOWCXSAXGXTPWCQXSAXHXTRWCSTXLXEXRXPVEUAUBXLXKXRXQVEXLXRVHWDVGVIW
      EVIWFVI $.

    $d .1. f $.  $d X f y $.
    $( The constant functor of ` X ` .  (Contributed by Zhi Wang,
       19-Oct-2025.) $)
    diag1a $p |- ( ph -> K = <. ( B X. { X } ) ,
       ( y e. B , z e. B |-> ( ( y J z ) X. { ( .1. ` X ) } ) ) >. ) $=
      ( vf cmpt cv co cfv cmpo cop csn cxp diag1 fconstmpt wceq wa a1i mpoeq3ia
      wcel opeq12i eqtr4di ) AJBELUCZBCEEUBBUDZCUDZIUEZLHUFZUCZUGZUHELUIUJZBCEE
      VCVDUIUJZUGZUHABCDEFGHUBIJKLMNOPQRSTUAUKVGUTVIVFBELULBCEEVHVEVHVEUMVAEUQV
      BEUQUNUBVCVDULUOUPURUS $.
  $}

  ${
    $d A x y $.  $d B x y $.  $d C x y $.  $d D x y $.  $d L x y $.
    $d M x y $.  $d N x y $.  $d X x y $.  $d Y x y $.  $d ph x y $.
    diag1f1.l $e |- L = ( C DiagFunc D ) $.
    diag1f1.c $e |- ( ph -> C e. Cat ) $.
    diag1f1.d $e |- ( ph -> D e. Cat ) $.
    diag1f1.a $e |- A = ( Base ` C ) $.
    diag1f1.b $e |- B = ( Base ` D ) $.
    diag1f1.0 $e |- ( ph -> B =/= (/) ) $.
    ${
      diag1f1lem.x $e |- ( ph -> X e. A ) $.
      diag1f1lem.y $e |- ( ph -> Y e. A ) $.
      diag1f1lem.m $e |- M = ( ( 1st ` L ) ` X ) $.
      diag1f1lem.n $e |- N = ( ( 1st ` L ) ` Y ) $.
      $( The object part of the diagonal functor is 1-1 if ` B ` is non-empty.
         Note that ` ( ph -> ( M = N <-> X = Y ) ) ` also holds because of
         ~ diag1f1 and ~ f1fveq .  (Contributed by Zhi Wang, 19-Oct-2025.) $)
      diag1f1lem $p |- ( ph -> ( M = N -> X = Y ) ) $=
        ( vx vy wceq csn cxp cv chom cfv co ccid cmpo eqid diag1a eqeq12d fvexi
        cop cbs snex xpex mpoex opth1 c0 wne wb xpcan syl wcel wi sneqrg sylbid
        syl5 ) AGHUCCIUDZUEZUAUBCCUAUFUBUFEUGUHZUIZIDUJUHZUHUDUEZUKZUPZCJUDZUEZ
        UAUBCCVOJVPUHUDUEUKZUPZUCZIJUCZAGVSHWCAUAUBBCDEVPVNGFIKLMNQSOVNULZVPULZ
        UMAUAUBBCDEVPVNHFJKLMNRTOWFWGUMUNWDVMWAUCZAWEVMVRWAWBCVLCEUQOUOZIURUSUA
        UBCCVQWIWIUTVAAWHVLVTUCZWEACVBVCWHWJVDPVLVTCVEVFAIBVGWJWEVHQIJBVIVFVJVK
        VJ $.
    $}

    $( The object part of the diagonal functor is 1-1 if ` B ` is non-empty.
       (Contributed by Zhi Wang, 19-Oct-2025.) $)
    diag1f1 $p |- ( ph -> ( 1st ` L ) : A -1-1-> ( D Func C ) ) $=
      ( vx vy co cfv cv eqid wcel adantr cfunc c1st wf wceq wi wral cfuc fucbas
      wf1 c2nd diagcl func1st2nd funcf1 wa ccat c0 wne simprl simprr diag1f1lem
      ralrimivva dff13 sylanbrc ) ABEDUAOZFUBPZUCMQZVEPZNQZVEPZUDVFVHUDUEZNBUFM
      BUFBVDVEUIABVDDEDUGOZVEFUJPJEDVKVKRZUHADVKFADEVKFGHIVLUKULUMAVJMNBBAVFBSZ
      VHBSZUNZUNBCDEFVGVIVFVHGADUOSVOHTAEUOSVOITJKACUPUQVOLTAVMVNURAVMVNUSVGRVI
      RUTVAMNBVDVEVBVC $.
  $}

  ${
    $d A f g $.  $d B f g $.  $d C f g $.  $d D f g $.  $d H f g $.
    $d L f g $.  $d N f g $.  $d X f g $.  $d Y f g $.  $d f g ph $.
    diag2f1.l $e |- L = ( C DiagFunc D ) $.
    diag2f1.a $e |- A = ( Base ` C ) $.
    diag2f1.b $e |- B = ( Base ` D ) $.
    diag2f1.h $e |- H = ( Hom ` C ) $.
    diag2f1.c $e |- ( ph -> C e. Cat ) $.
    diag2f1.d $e |- ( ph -> D e. Cat ) $.
    diag2f1.x $e |- ( ph -> X e. A ) $.
    diag2f1.y $e |- ( ph -> Y e. A ) $.
    diag2f1.0 $e |- ( ph -> B =/= (/) ) $.
    ${
      diag2f1lem.f $e |- ( ph -> F e. ( X H Y ) ) $.
      diag2f1lem.g $e |- ( ph -> G e. ( X H Y ) ) $.
      $( Lemma for ~ diag2f1 .  The converse is trivial ( ~ fveq2 ).
         (Contributed by Zhi Wang, 21-Oct-2025.) $)
      diag2f1lem $p |- ( ph -> ( ( ( X ( 2nd ` L ) Y ) ` F )
                             = ( ( X ( 2nd ` L ) Y ) ` G ) -> F = G ) ) $=
        ( c2nd cfv co wceq csn cxp diag2 eqeq12d c0 wne wb xpcan syl bitrd wcel
        wi sneqrg sylbid ) AFJKIUCUDUEZUDZGVAUDZUFZFUGZGUGZUFZFGUFZAVDCVEUHZCVF
        UHZUFZVGAVBVIVCVJABCDEFHIJKLMNOPQRSUAUIABCDEGHIJKLMNOPQRSUBUIUJACUKULVK
        VGUMTVEVFCUNUOUPAFJKHUEZUQVGVHURUAFGVLUSUOUT $.
    $}

    diag2f1.n $e |- N = ( D Nat C ) $.
    $( If ` B ` is non-empty, the morphism part of a diagonal functor is
       injective functions from hom-sets into sets of natural transformations.
       (Contributed by Zhi Wang, 21-Oct-2025.) $)
    diag2f1 $p |- ( ph -> ( X ( 2nd ` L ) Y ) : ( X H Y ) -1-1->
     ( ( ( 1st ` L ) ` X ) N ( ( 1st ` L ) ` Y ) ) ) $=
      ( vf vg co c1st cfv c2nd wf cv wceq wi wral cfuc fuchom diagcl func1st2nd
      wf1 eqid funcf2 wcel wa adantr c0 wne simprl simprr diag2f1lem ralrimivva
      ccat dff13 sylanbrc ) AIJFUCZIGUDUEZUEJVLUEHUCZIJGUFUEZUCZUGUAUHZVOUEUBUH
      ZVOUEUIVPVQUIUJZUBVKUKUAVKUKVKVMVOUPABDEDULUCZVLVNFHIJLNEDVSHVSUQZTUMADVS
      GADEVSGKOPVTUNUOQRURAVRUAUBVKVKAVPVKUSZVQVKUSZUTZUTBCDEVPVQFGIJKLMNADVHUS
      WCOVAAEVHUSWCPVAAIBUSWCQVAAJBUSWCRVAACVBVCWCSVAAWAWBVDAWAWBVEVFVGUAUBVKVM
      VOVIVJ $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Functor composition bifunctors
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    fucofulem1.1 $e |- ( ph -> ( ps <-> ( ch /\ th /\ ta ) ) ) $.
    fucofulem1.2 $e |- ( ( ph /\ ( th /\ ta ) ) -> et ) $.
    fucofulem1.3 $e |- ch $.
    fucofulem1.4 $e |- ( ( ph /\ et ) -> th ) $.
    fucofulem1.5 $e |- ( ( ph /\ et ) -> ta ) $.
    $( Lemma for proving functor theorems.  (Contributed by Zhi Wang,
       25-Sep-2025.) $)
    fucofulem1 $p |- ( ph -> ( ps <-> et ) ) $=
      ( wa simpl w3a biimpa simp2d simp3d syl12anc a1i biimpar syl13anc impbida
      ) ABFABLZADEFABMUCCDEABCDENZGOZPUCCDEUEQHRAFLZACDEBAFMCUFISJKABUDGTUAUB
      $.
  $}

  ${
    $d B m n r z $.  $d B u v r $.  $d C a b m n r $.  $d C m n p q r $.
    $d C m n z $.  $d D a b $.  $d D p q r $.  $d E a b m n $.
    $d E m n p q r $.  $d E m n z $.  $d F m n p q r $.  $d F m n z $.
    $d G a b m n $.  $d G m n p q r $.  $d G u v $.  $d G m n z $.
    $d H m n r $.  $d H m n z $.
    fucofulem2.b $e |- B = ( ( D Func E ) X. ( C Func D ) ) $.
    fucofulem2.h $e |- H = ( Hom ` ( ( D FuncCat E ) Xc. ( C FuncCat D ) ) ) $.
    $( Lemma for proving functor theorems.  Maybe consider ~ eufnfv to prove
       the uniqueness of a functor.  (Contributed by Zhi Wang, 25-Sep-2025.) $)
    fucofulem2 $p |- ( G e. X_ z e. ( B X. B )
       ( ( ( F ` ( 1st ` z ) ) ( C Nat E ) ( F ` ( 2nd ` z ) ) ) ^m ( H ` z ) )
       <-> ( G = ( u e. B , v e. B |-> ( u G v ) )
       /\ A. m e. B A. n e. B ( ( m G n ) = (
       b e. ( ( 1st ` m ) ( D Nat E ) ( 1st ` n ) )
       , a e. ( ( 2nd ` m ) ( C Nat D ) ( 2nd ` n ) ) |-> ( b ( m G n ) a ) )
       /\ A. p e. ( ( 1st ` m ) ( D Nat E ) ( 1st ` n ) )
       A. q e. ( ( 2nd ` m ) ( C Nat D ) ( 2nd ` n ) )
       ( p ( m G n ) q ) e. ( ( F ` m ) ( C Nat E ) ( F ` n ) ) ) ) ) $=
      ( cfv co vr cxp cv c1st c2nd cnat cmap cixp wcel wfn wf wral wa cmpo wceq
      cfuc cxpc cbs cfunc eqid xpcfucbas eqtri funcf2lem2 fnov wtru ffnfv simpl
      wb simpr xpcfuchom fneq2d bitrdi raleqdv fveq2 df-ov eqtr4di eleq1d ralxp
      cop anbi12d bitrid adantl 2ralbidva mptru anbi12i bitri ) KADDUBZAUCZUDSJ
      SWHUESJSEIUFTZTWHLSUGTUHUIKWGUJZGUCZHUCZLTZWKJSWLJSWITZWKWLKTZUKZHDULGDUL
      ZUMKCBDDCUCBUCKTUNUOZWOPOWKUDSWLUDSFIUFTTZWKUESWLUESEFUFTTZPUCOUCWOTUNUOZ
      NUCZMUCZWOTZWNUIZMWTULNWSULZUMZHDULGDULZUMGHADFIUPTEFUPTUQTZURJKLWIDFIUST
      EFUSTUBXIURSQFIEXIFXIUTZVAVBZVCWJWRWQXHCBDDKVDWQXHVHVEWPXGGHDDWKDUIZWLDUI
      ZUMZWPXGVHVEWPWOWMUJZUAUCZWOSZWNUIZUAWMULZUMXNXGUAWMWNWOVFXNXOXAXSXFXNXOW
      OWSWTUBZUJXAXNWMXTWOXNDFIEXIFLWKWLXJXKRXLXMVGXLXMVIVJZVKPOWSWTWOVDVLXNXSX
      RUAXTULXFXNXRUAWMXTYAVMXRXEUANMWSWTXPXBXCVSZUOZXQXDWNYCXQYBWOSXDXPYBWOVNX
      BXCWOVOVPVQVRVLVTWAWBWCWDWEWF $.
  $}

  ${
    $( Equivalence of product functor.  (Contributed by Zhi Wang,
       29-Sep-2025.) $)
    fuco2el $p |- ( <. <. K , L >. , <. F , G >. >. e. ( S X. R )
            <-> ( K S L /\ F R G ) ) $=
      ( cop cxp wcel wa wbr opelxp df-br anbi12i bitr4i ) EFGZCDGZGBAHIPBIZQAIZ
      JEFBKZCDAKZJPQBALTRUASEFBMCDAMNO $.
  $}

  ${
    fuco2eld.w $e |- ( ph -> W = ( S X. R ) ) $.
    ${
      fuco2eld.u $e |- ( ph -> U = <. <. K , L >. , <. F , G >. >. ) $.
      fuco2eld.k $e |- ( ph -> K S L ) $.
      fuco2eld.f $e |- ( ph -> F R G ) $.
      $( Equivalence of product functor.  (Contributed by Zhi Wang,
         29-Sep-2025.) $)
      fuco2eld $p |- ( ph -> U e. W ) $=
        ( cop cxp wbr wcel fuco2el sylanbrc 3eltr4d ) AGHNEFNNZCBOZDIAGHCPEFBPU
        AUBQLMBCEFGHRSKJT $.
    $}

    fuco2eld2.u $e |- ( ph -> U e. W ) $.
    fuco2eld2.s $e |- Rel S $.
    fuco2eld2.r $e |- Rel R $.
    $( Equivalence of product functor.  (Contributed by Zhi Wang,
       29-Sep-2025.) $)
    fuco2eld2 $p |- ( ph -> U
              = <. <. ( 1st ` ( 1st ` U ) ) , ( 2nd ` ( 1st ` U ) ) >. ,
                   <. ( 1st ` ( 2nd ` U ) ) , ( 2nd ` ( 2nd ` U ) ) >. >. ) $=
      ( c1st cfv c2nd cop cxp wcel wceq 1st2nd2 cvv wrel wss eleqtrd syl df-rel
      mpbi xp1st sselid 3syl xp2nd opeq12d eqtrd ) ADDJKZDLKZMZUKJKUKLKMZULJKUL
      LKMZMADCBNZOZDUMPADEUPGFUAZDCBQUBAUKUNULUOAUQUKRRNZOUKUNPURUQCUSUKCSCUSTH
      CUCUDDCBUEUFUKRRQUGAUQULUSOULUOPURUQBUSULBSBUSTIBUCUDDCBUHUFULRRQUGUIUJ
      $.

    $( Equivalence of product functor.  (Contributed by Zhi Wang,
       29-Sep-2025.) $)
    fuco2eld3 $p |- ( ph -> (
                ( 1st ` ( 1st ` U ) ) S ( 2nd ` ( 1st ` U ) )
             /\ ( 1st ` ( 2nd ` U ) ) R ( 2nd ` ( 2nd ` U ) ) ) ) $=
      ( c1st cfv c2nd cop cxp wcel wbr wa fuco2eld2 3eltr3d fuco2el sylib ) ADJ
      KZJKZUBLKZMDLKZJKZUELKZMMZCBNZOUCUDCPUFUGBPQADEUHUIGABCDEFGHIRFSBCUFUGUCU
      DTUA $.
  $}

  $c o.F $.

  $( Extend class notation with functor composition bifunctors. $)
  cfuco $a class o.F $.

  ${
    $d C a b c d e f g k l m p r u v w x y $.
    $d D a b c d e f g k l m p r u v w x y $.
    $d E a b c d e f g k l m p r u v w x y $.
    $d W a b c d e f k l m p r u v w x $.
    $d a b c d e f g k l m p ph r u v w x y $.  $d .o. c d e g p w y $.
    $d T c d e g p w y $.  $d U c d e g p w y $.  $d V c d e g p w y $.
    $( Definition of functor composition bifunctors.  Given three categories
       ` C ` , ` D ` , and ` E ` , ` ( <. C , D >. o.F E ) ` is a functor from
       the product category of two categories of functors to a category of
       functors ( ~ fucofunc ).  The object part maps two functors to their
       composition ( ~ fuco11 and ~ fuco11b ).  The morphism part defines the
       "composition" of two natural transformations ( ~ fuco22 ) into another
       natural transformation ( ~ fuco22nat ) such that a "cube-like" diagram
       commutes.  The naturality property also gives an alternate definition
       ( ~ fuco23a ).  Note that such "composition" is different from ~ fucco
       because they "compose" along different "axes".  (Contributed by Zhi
       Wang, 29-Sep-2025.) $)
    df-fuco $a |- o.F = ( p e. _V , e e. _V |->
            [_ ( 1st ` p ) / c ]_ [_ ( 2nd ` p ) / d ]_
            [_ ( ( d Func e ) X. ( c Func d ) ) / w ]_ <. ( o.func |` w ) ,
            ( u e. w , v e. w |-> [_ ( 1st ` ( 2nd ` u ) ) / f ]_
            [_ ( 1st ` ( 1st ` u ) ) / k ]_ [_ ( 2nd ` ( 1st ` u ) ) / l ]_
            [_ ( 1st ` ( 2nd ` v ) ) / m ]_ [_ ( 1st ` ( 1st ` v ) ) / r ]_
            ( b e. ( ( 1st ` u ) ( d Nat e ) ( 1st ` v ) ) ,
              a e. ( ( 2nd ` u ) ( c Nat d ) ( 2nd ` v ) ) |->
            ( x e. ( Base ` c ) |-> ( ( b ` ( m ` x ) )
            ( <. ( k ` ( f ` x ) ) , ( k ` ( m ` x ) ) >.
              ( comp ` e ) ( r ` ( m ` x ) ) )
            ( ( ( f ` x ) l ( m ` x ) ) ` ( a ` x ) ) ) ) ) ) >. ) $.

    ${
      $d P a b c d e f k l m p r u v w x $.
      fucofvalg.p $e |- ( ph -> P e. U ) $.
      fucofvalg.c $e |- ( ph -> ( 1st ` P ) = C ) $.
      fucofvalg.d $e |- ( ph -> ( 2nd ` P ) = D ) $.
      fucofvalg.e $e |- ( ph -> E e. V ) $.
      fucofvalg.o $e |- ( ph -> ( P o.F E ) = .o. ) $.
      fucofvalg.w $e |- ( ph -> W = ( ( D Func E ) X. ( C Func D ) ) ) $.
      $( Value of the function giving the functor composition bifunctor.
         (Contributed by Zhi Wang, 7-Oct-2025.) $)
      fucofvalg $p |- ( ph -> .o. = <. ( o.func |` W ) ,
                ( u e. W , v e. W |-> [_ ( 1st ` ( 2nd ` u ) ) / f ]_
                [_ ( 1st ` ( 1st ` u ) ) / k ]_ [_ ( 2nd ` ( 1st ` u ) ) / l ]_
                [_ ( 1st ` ( 2nd ` v ) ) / m ]_ [_ ( 1st ` ( 1st ` v ) ) / r ]_
                ( b e. ( ( 1st ` u ) ( D Nat E ) ( 1st ` v ) ) ,
                  a e. ( ( 2nd ` u ) ( C Nat D ) ( 2nd ` v ) ) |->
                ( x e. ( Base ` C ) |-> ( ( b ` ( m ` x ) )
                ( <. ( k ` ( f ` x ) ) , ( k ` ( m ` x ) ) >.
                  ( comp ` E ) ( r ` ( m ` x ) ) )
                ( ( ( f ` x ) l ( m ` x ) ) ` ( a ` x ) ) ) ) ) ) >. ) $=
        ( vp ve vc vd vw cfuco co ccofu cres cv c2nd cfv c1st cnat cbs cop cmpt
        cco cmpo csb cvv cfunc cxp df-fuco a1i fvexd simprl fveq2d adantr eqtrd
        wceq simplrl ad2antrr simpr simpllr simprd oveq12d simplr xpeq12d ovexd
        wa xpexd eqeltrd ad3antrrr eqtr4d reseq2d mpteq12dv mpoeq123dv csbeq2dv
        oveqd opeq12d csbied2 elexd wcel opex ovmpod eqtr3d ) AGLUKULOUMNUNZDCN
        NIDUOZUPUQZURUQZJXDURUQZURUQZSXGUPUQZKCUOZUPUQZURUQZPXJURUQZURUQZRQXGXM
        FLUSULZULZXEXKEFUSULZULZBEUTUQZBUOZKUOUQZRUOUQZXTQUOUQXTIUOUQZYASUOULUQ
        ZYCJUOZUQYAYEUQVAZYAPUOUQZLVCUQZULZULZVBZVDZVEZVEZVEZVEZVEZVDZVAZUDAUFU
        GGLVFVFUHUFUOZURUQZUIYTUPUQZUJUIUOZUGUOZVGULZUHUOZUUCVGULZVHZUMUJUOZUNZ
        DCUUIUUIIXFJXHSXIKXLPXNRQXGXMUUCUUDUSULZULZXEXKUUFUUCUSULZULZBUUFUTUQZY
        BYDYFYGUUDVCUQZULZULZVBZVDZVEZVEZVEZVEZVEZVDZVAZVEZVEZVEZYSUKVFUKUFUGVF
        VFUVJVDVPABUJCDUGIJKPUFQRUHUISVIVJAYTGVPZUUDLVPZWFZWFZUHUUAEUVIYSVFUVNY
        TURVKUVNUUAGURUQZEUVNYTGURAUVKUVLVLVMAUVOEVPUVMUAVNVOUVNUUFEVPZWFZUIUUB
        FUVHYSVFUVQYTUPVKUVQUUBGUPUQZFUVQYTGUPAUVKUVLUVPVQVMAUVRFVPUVMUVPUBVRVO
        UVQUUCFVPZWFZUJUUHNUVGYSVFUVTUUHFLVGULZEFVGULZVHZVFUVTUUEUWAUUGUWBUVTUU
        CFUUDLVGUVQUVSVSZUVTUVKUVLAUVMUVPUVSVTWAZWBUVTUUFEUUCFVGUVNUVPUVSWCUWDW
        BWDZUVTUWAUWBVFVFUVTFLVGWEUVTEFVGWEWGWHUVTUUHUWCNUWFANUWCVPUVMUVPUVSUEW
        IWJUVTUUINVPZWFZUUJXCUVFYRUWHUUINUMUVTUWGVSZWKUWHDCUUIUUIUVENNYQUWIUWIU
        WHIXFUVDYPUWHJXHUVCYOUWHSXIUVBYNUWHKXLUVAYMUWHPXNUUTYLUWHRQUULUUNUUSXPX
        RYKUWHUUKXOXGXMUWHUUCFUUDLUSUVQUVSUWGWCZUVTUVLUWGUWEVNZWBWOUWHUUMXQXEXK
        UWHUUFEUUCFUSUVNUVPUVSUWGVTZUWJWBWOUWHBUUOUURXSYJUWHUUFEUTUWLVMUWHUUQYI
        YBYDUWHUUPYHYFYGUWHUUDLVCUWKVMWOWOWLWMWNWNWNWNWNWMWPWQWQWQAGHTWRALMUCWR
        YSVFWSAXCYRWTVJXAXB $.
    $}

    fucofval.c $e |- ( ph -> C e. T ) $.
    fucofval.d $e |- ( ph -> D e. U ) $.
    fucofval.e $e |- ( ph -> E e. V ) $.
    ${
      fucofval.o $e |- ( ph -> ( <. C , D >. o.F E ) = .o. ) $.
      ${
        fucofval.w $e |- ( ph -> W = ( ( D Func E ) X. ( C Func D ) ) ) $.
        $( Value of the function giving the functor composition bifunctor.
           Hypotheses fucofval.c and fucofval.d are not redundant
           ( ~ fucofvalne ).  (Contributed by Zhi Wang, 29-Sep-2025.) $)
        fucofval $p |- ( ph -> .o. = <. ( o.func |` W ) ,
                ( u e. W , v e. W |-> [_ ( 1st ` ( 2nd ` u ) ) / f ]_
                [_ ( 1st ` ( 1st ` u ) ) / k ]_ [_ ( 2nd ` ( 1st ` u ) ) / l ]_
                [_ ( 1st ` ( 2nd ` v ) ) / m ]_ [_ ( 1st ` ( 1st ` v ) ) / r ]_
                ( b e. ( ( 1st ` u ) ( D Nat E ) ( 1st ` v ) ) ,
                  a e. ( ( 2nd ` u ) ( C Nat D ) ( 2nd ` v ) ) |->
                ( x e. ( Base ` C ) |-> ( ( b ` ( m ` x ) )
                ( <. ( k ` ( f ` x ) ) , ( k ` ( m ` x ) ) >.
                  ( comp ` E ) ( r ` ( m ` x ) ) )
                ( ( ( f ` x ) l ( m ` x ) ) ` ( a ` x ) ) ) ) ) ) >. ) $=
          ( cop cvv wcel opex a1i c1st cfv wceq op1stg syl2anc op2ndg fucofvalg
          c2nd ) ABCDEFEFUEZUFIJKLMNOPQRSURUFUGAEFUHUIAEGUGZFHUGZURUJUKEULTUAEF
          GHUMUNAUSUTURUQUKFULTUAEFGHUOUNUBUCUDUP $.
      $}

      $( A functor composition bifunctor is an ordered pair.  Enables
         ~ 1st2ndb .  (Contributed by Zhi Wang, 29-Sep-2025.) $)
      fucoelvv $p |- ( ph -> .o. e. ( _V X. _V ) ) $=
        ( vf vx co cv c2nd cfv c1st cvv vu vv vk vl vm vr vb va vg vy ccofu cxp
        cfunc cres cnat cbs cop cco cmpt cmpo csb eqidd fucofval wfun wcel ccom
        cdm df-cofu mpofun ovex xpex resfunexg mp2an mpoex opelvv eqeltrdi ) AH
        UKCFUMOZBCUMOZULZUNZUAUBVSVSMUAPZQRZSRUCWASRZSRUDWCQRUEUBPZQRZSRUFWDSRZ
        SRUGUHWCWFCFUOOOWBWEBCUOOONBUPRNPZUEPRZUGPRWGUHPRWGMPZRZWHUDPORWJUCPZRW
        HWKRUQWHUFPRFURROOUSUTVAVAVAVAVAZUTZUQTTULANUBUABCDEMUCUEFGVSHUFUHUGUDI
        JKLAVSVBVCVTWMUKVDVSTVEVTTVEUIMTTUIPZSRWISRZVFNUJWIQRZVGVGZWQWGWORUJPZW
        ORWNQROWGWRWPOVFUTUQUKNUJMUIVHVIVQVRCFUMVJBCUMVJVKZUKVSTVLVMUAUBVSVSWLW
        SWSVNVOVP $.
    $}

    fuco1.o $e |- ( ph -> ( <. C , D >. o.F E ) = <. O , P >. ) $.
    fuco1.w $e |- ( ph -> W = ( ( D Func E ) X. ( C Func D ) ) ) $.
    $( The object part of the functor composition bifunctor.  (Contributed by
       Zhi Wang, 29-Sep-2025.) $)
    fuco1 $p |- ( ph -> O = ( o.func |` W ) ) $=
      ( cv cfv c1st co cvv vu vv vf vk vl vm vr vb va vx cop cres c2nd cnat cbs
      ccofu cco cmpt cmpo csb wceq fucofval wi cxp fucoelvv opelxp1 syl opelxp2
      wcel opth1g syl2anc mpd ) AHDUKZUPJULZUAUBJJUCUAPZUMQZRQUDVORQZRQUEVQUMQU
      FUBPZUMQZRQUGVRRQZRQUHUIVQVTCGUNSSVPVSBCUNSSUJBUOQUJPZUFPQZUHPQWAUIPQWAUC
      PQZWBUEPSQWCUDPZQWBWDQUKWBUGPQGUQQSSURUSUTUTUTUTUTUSZUKVAZHVNVAZAUJUBUABC
      EFUCUDUFGIJVMUGUIUHUEKLMNOVBAHTVIZDTVIZWFWGVCAVMTTVDVIZWHABCEFGIVMKLMNVEZ
      HDTTVFVGAWJWIWKHDTTVHVGHDVNWETTVJVKVL $.

    $( The object part of the functor composition bifunctor maps
       ` ( ( D Func E ) X. ( C Func D ) ) ` into ` ( C Func E ) ` .
       (Contributed by Zhi Wang, 29-Sep-2025.) $)
    fucof1 $p |- ( ph -> O : W --> ( C Func E ) ) $=
      ( cfunc co wf ccofu cres cxp rescofuf fuco1 reseq2d eqtrd feq12d mpbiri )
      AJBGPQZHRCGPQBCPQUAZUHSUITZRBCGUBAJUIUHHUJAHSJTUJABCDEFGHIJKLMNOUCAJUISOU
      DUEOUFUG $.

    $( The morphism part of the functor composition bifunctor.  (Contributed by
       Zhi Wang, 29-Sep-2025.) $)
    fuco2 $p |- ( ph -> P = ( u e. W , v e. W |->
          [_ ( 1st ` ( 2nd ` u ) ) / f ]_
          [_ ( 1st ` ( 1st ` u ) ) / k ]_ [_ ( 2nd ` ( 1st ` u ) ) / l ]_
          [_ ( 1st ` ( 2nd ` v ) ) / m ]_ [_ ( 1st ` ( 1st ` v ) ) / r ]_
          ( b e. ( ( 1st ` u ) ( D Nat E ) ( 1st ` v ) ) ,
            a e. ( ( 2nd ` u ) ( C Nat D ) ( 2nd ` v ) ) |->
          ( x e. ( Base ` C ) |-> ( ( b ` ( m ` x ) )
          ( <. ( k ` ( f ` x ) ) , ( k ` ( m ` x ) ) >.
            ( comp ` E ) ( r ` ( m ` x ) ) )
          ( ( ( f ` x ) l ( m ` x ) ) ` ( a ` x ) ) ) ) ) ) ) $=
      ( ccofu cres wceq cv c2nd cfv c1st cnat co cbs cop cco cmpt cmpo fucofval
      csb wa cvv wb cxp fucoelvv opelxp1 syl opelxp2 opthg syl2anc mpbid simprd
      wcel ) ANUFPUGZUHZGDCPPJDUIZUJUKZULUKKVQULUKZULUKTVSUJUKLCUIZUJUKZULUKQVT
      ULUKZULUKSRVSWBFMUMUNUNVRWAEFUMUNUNBEUOUKBUIZLUIUKZSUIUKWCRUIUKWCJUIUKZWD
      TUIUNUKWEKUIZUKWDWFUKUPWDQUIUKMUQUKUNUNURUSVAVAVAVAVAUSZUHZANGUPZVOWGUPUH
      ZVPWHVBZABCDEFHIJKLMOPWIQRSTUAUBUCUDUEUTANVCVNZGVCVNZWJWKVDAWIVCVCVEVNZWL
      AEFHIMOWIUAUBUCUDVFZNGVCVCVGVHAWNWMWONGVCVCVIVHNGVOWGVCVCVJVKVLVM $.

    $d P u v $.
    $( The morphism part of the functor composition bifunctor is a function on
       the Cartesian square of the base set.  (Contributed by Zhi Wang,
       29-Sep-2025.) $)
    fucofn2 $p |- ( ph -> P Fn ( W X. W ) ) $=
      ( cv cfv c1st co csb vu vv vf vk vl vm vr vb va cxp wfn c2nd cnat cbs cop
      vx cco cmpt cmpo eqid ovex mpoex csbex fnmpoi fuco2 fneq1d mpbiri ) ADJJU
      JZUKUAUBJJUCUAPZULQZRQZUDVIRQZRQZUEVLULQZUFUBPZULQZRQZUGVORQZRQZUHUIVLVRC
      GUMSZSZVJVPBCUMSZSZUPBUNQUPPZUFPQZUHPQWDUIPQWDUCPQZWEUEPSQWFUDPZQWEWGQUOW
      EUGPQGUQQSSURZUSZTZTZTZTZTZUSZVHUKUAUBJJWNWOWOUTUCVKWMUDVMWLUEVNWKUFVQWJU
      GVSWIUHUIWAWCWHVLVRVTVAVJVPWBVAVBVCVCVCVCVCVDAVHDWOAUPUBUABCDEFUCUDUFGHIJ
      UGUIUHUEKLMNOVEVFVG $.
  $}

  ${
    $d E a b f k l m r u v x $.  $d a b f k l m ph r u v x $.
    $d b f g m n t u x y z $.  $d .o. g n t y z $.  $d C g n t y z $.
    $d D g n t y z $.  $d W g n t y z $.
    fucofvalne.c $e |- ( ph -> -. ( C e. _V /\ D e. _V ) ) $.
    fucofvalne.e $e |- ( ph -> E e. Cat ) $.
    fucofvalne.o $e |- ( ph -> ( <. C , D >. o.F E ) = .o. ) $.
    fucofvalne.w $e |- ( ph -> W = ( ( D Func E ) X. ( C Func D ) ) ) $.
    $( Value of the function giving the functor composition bifunctor, if ` C `
       or ` D ` are not sets.  (Contributed by Zhi Wang, 7-Oct-2025.) $)
    fucofvalne $p |- ( ph -> .o. =/= <. ( o.func |` W ) ,
                ( u e. W , v e. W |-> [_ ( 1st ` ( 2nd ` u ) ) / f ]_
                [_ ( 1st ` ( 1st ` u ) ) / k ]_ [_ ( 2nd ` ( 1st ` u ) ) / l ]_
                [_ ( 1st ` ( 2nd ` v ) ) / m ]_ [_ ( 1st ` ( 1st ` v ) ) / r ]_
                ( b e. ( ( 1st ` u ) ( D Nat E ) ( 1st ` v ) ) ,
                  a e. ( ( 2nd ` u ) ( C Nat D ) ( 2nd ` v ) ) |->
                ( x e. ( Base ` C ) |-> ( ( b ` ( m ` x ) )
                ( <. ( k ` ( f ` x ) ) , ( k ` ( m ` x ) ) >.
                  ( comp ` E ) ( r ` ( m ` x ) ) )
                ( ( ( f ` x ) l ( m ` x ) ) ` ( a ` x ) ) ) ) ) ) >. ) $=
      ( vt vg vz vn vy ccofu c0 cfunc co cxp cres cv c2nd cfv c1st cnat cbs cop
      cco cmpt cmpo csb cvv ccat wcel 0ex a1i wceq 1st0 2nd0 cfuco wa opprc syl
      wn oveq1d eqtr3d eqidd fucofvalg wne cdm csn opex snnz ioran xpeq0 biimpi
      neii wo con3i sylbir mp2an 0func 0cat xpeq12d wrel wf chom cmap cixp ccid
      wral wsbc copab df-func reldmmpo 0nelrel0 ax-mp eleq1d mtbiri df-ov ndmfv
      w3a eqtrid xpeq2d xp0 eqtrdi eqeq12d rescofuf fdmi eqeq12i neqned reseq2d
      dmeq 3syl neeqtrrd wi ovex xpex fex mpoex opth1neg eqnetrd ) ALUFUGJUHUIZ
      UGUGUHUIZUJZUKZDCYPYPGDULZUMUNZUOUNZHYRUOUNZUOUNZPUUAUMUNZICULZUMUNZUOUNZ
      MUUDUOUNZUOUNZONUUAUUGUGJUPUIUIYSUUEUGUGUPUIUIBUGUQUNBULZIULZUNZOULZUNUUI
      NULUNUUIGULZUNZUUKPULUIUNUUNHULZUNUUKUUOUNURUUKMULUNJUSUNUIUIZUTVAVBVBVBV
      BVBZVAZURZUFKUKZDCKKGYTHUUBPUUCIUUFMUUHONUUAUUGFJUPUIUIYSUUEEFUPUIUIBEUQU
      NUUPUTVAVBVBVBVBVBVAZURZABCDUGUGUGVCGHIJVDYPLMNOPUGVCVEAVFVGUGUOUNUGVHAVI
      VGUGUMUNUGVHAVJVGRAEFURZJVKUIUGJVKUILAUVCUGJVKAEVCVEFVCVEVLVOUVCUGVHQEFVM
      VNZVPSVQAYPVRVSAYQUUTVTZUUSUVBVTZAYQUFFJUHUIZEFUHUIZUJZUKZUUTAYQUVJAYPUVI
      VHZVOYQWAZUVJWAZVHZVOYQUVJVHZVOAUVKUGUGURZWBZUVQUJZUGVHZUVQUGVHZVOZUWAUVS
      VOZUVQUGUVPUGUGWCWDWHZUWCUWAUWAVLUVTUVTWIZVOUWBUVTUVTWEUVSUWDUVSUWDUVQUVQ
      WFWGWJWKWLAYPUVRUVIUGAYNUVQYOUVQAJRWMAUGUGVDVEAWNVGWMWOAUVCUHWAZVEZVOZUVI
      UGVHAUWFUGUWEVEZUWEWPUWHVOUADVDVDUULYRUQUNUUMWQUBULZUCUULUULUJUCULZUOUNUU
      MUNUWJUMUNUUMUNYRWRUNUIUWJUAULZWRUNZUNWSUIWTVEUUIUWKXAUNUNUUIUUIUWIUIUNUU
      NYRXAUNUNVHUDULZUUJUUIUEULZURUWJUWKUSUNUIUIUUIUWJUWIUIUNUWMUWNUWJUWIUIUNU
      UJUUIUWNUWIUIUNUUNUWNUUMUNURUWJUUMUNYRUSUNUIUIVHUDUWNUWJUWLUIXBIUUIUWNUWL
      UIXBUCUULXBUEUULXBVLBUULXBXMOUWKUQUNXCGUBXDUHBUEUCDUAGUBIUDOXEXFUWEXGXHAU
      VCUGUWEUVDXIXJUWGUVIUVGUGUJUGUWGUVHUGUVGUWGUVHUVCUHUNUGEFUHXKUVCUHXLXNXOU
      VGXPXQVNXRXJUVNUVKUVNUVKUVLYPUVMUVIYPYNYQUGUGJXSZXTUVIEJUHUIUVJEFJXSXTYAW
      GWJUVOUVNYQUVJYDWJYEYBAKUVIUFTYCYFYQVCVEZUURVCVEUVEUVFYGYPYNYQWQYPVCVEUWP
      UWOYNYOUGJUHYHUGUGUHYHYIZYPYNVCYQYJWLDCYPYPUUQUWQUWQYKYQUURUUTUVAVCVCYLWL
      VNYM $.
  $}

  ${
    fuco11.o $e |- ( ph -> ( <. C , D >. o.F E ) = <. O , P >. ) $.
    fuco11.f $e |- ( ph -> F ( C Func D ) G ) $.
    fuco11.k $e |- ( ph -> K ( D Func E ) L ) $.
    fuco11.u $e |- ( ph -> U = <. <. K , L >. , <. F , G >. >. ) $.
    $( The object part of the functor composition bifunctor maps two functors
       to their composition.  (Contributed by Zhi Wang, 30-Sep-2025.) $)
    fuco11 $p |- ( ph -> ( O ` U ) = ( <. K , L >. o.func <. F , G >. ) ) $=
      ( cfv ccofu co cop ccat cfunc cres funcrcl2 funcrcl3 eqidd fuco1 fuco2eld
      cxp fveq1d fvresd fveq2d df-ov eqtr4di 3eqtrd ) AEKPEQCFUARZBCUARZUHZUBZP
      EQPZIJSZGHSZQRZAEKURABCDTTFKTUQABCGHMUCACFIJNUCACFIJNUDLAUQUEZUFUIAEUQQAU
      PUOEGHIJUQVCONMUGUJAUSUTVASZQPVBAEVDQOUKUTVAQULUMUN $.

    $( The object part of the functor composition bifunctor maps into
       ` ( C Func E ) ` .  (Contributed by Zhi Wang, 30-Sep-2025.) $)
    fuco11cl $p |- ( ph -> ( O ` U ) e. ( C Func E ) ) $=
      ( cfunc co cxp ccat funcrcl2 funcrcl3 eqidd fucof1 fuco2eld ffvelcdmd ) A
      CFPQZBCPQZRZBFPQEKABCDSSFKSUHABCGHMTACFIJNTACFIJNUALAUHUBZUCAUGUFEGHIJUHU
      IONMUDUE $.

    ${
      $d B x y $.  $d F x y $.  $d G x y $.  $d K x y $.  $d L x y $.
      $d ph x y $.
      fuco11a.b $e |- B = ( Base ` C ) $.
      $( The object part of the functor composition bifunctor maps two functors
         to their composition, expressed explicitly.  (Contributed by Zhi Wang,
         30-Sep-2025.) $)
      fuco11a $p |- ( ph -> ( O ` U ) = <. ( K o. F ) , ( x e. B , y e. B |->
                    ( ( ( F ` x ) L ( F ` y ) ) o. ( x G y ) ) ) >. ) $=
        ( cfv cop ccofu co ccom cv cmpo fuco11 cofuval2 eqtrd ) AHNTLMUAJKUAUBU
        CLJUDBCDDBUEZJTCUEZJTMUCUJUKKUCUDUFUAAEFGHIJKLMNOPQRUGABCDEFIJKLMSPQUHU
        I $.

      $( The object part of the functor composition bifunctor maps two functors
         to their composition, expressed explicitly for the morphism part of
         the composed functor.  (Contributed by Zhi Wang, 3-Oct-2025.) $)
      fuco112 $p |- ( ph -> ( 2nd ` ( O ` U ) ) = ( x e. B , y e. B |->
                    ( ( ( F ` x ) L ( F ` y ) ) o. ( x G y ) ) ) ) $=
        ( cvv cfv c2nd ccom cv co cmpo cop fuco11a fveq2d wcel wceq wbr relfunc
        cfunc brrelex1i syl coexd cbs fvexi mpoex op2ndg sylancl eqtrd ) AHNUAZ
        UBUALJUCZBCDDBUDZJUACUDZJUAMUEVFVGKUEUCZUFZUGZUBUAZVIAVDVJUBABCDEFGHIJK
        LMNOPQRSUHUIAVETUJVITUJVKVIUKALJTTALMFIUNUEZULLTUJQLMVLFIUMUOUPAJKEFUNU
        EZULJTUJPJKVMEFUMUOUPUQBCDDVHDEURSUSZVNUTVEVITTVAVBVC $.
    $}

    ${
      $d C x y $.  $d D x y $.  $d E x y $.  $d F x y $.  $d G x y $.
      $d K x y $.  $d L x y $.  $d O x y $.  $d P x y $.  $d U x y $.
      $d X x y $.  $d Y x y $.  $d ph x y $.
      $( The object part of the functor composition bifunctor maps two functors
         to their composition, expressed explicitly for the object part of the
         composed functor.  (Contributed by Zhi Wang, 2-Oct-2025.) $)
      fuco111 $p |- ( ph -> ( 1st ` ( O ` U ) ) = ( K o. F ) ) $=
        ( vx vy cfv co cvv c1st ccom cbs cmpo cop eqid fuco11a fveq2d wcel wceq
        cfunc wbr relfunc brrelex1i syl coexd fvex mpoex op1stg sylancl eqtrd
        cv ) AEKRZUARIGUBZPQBUCRZVEPVBZGRQVBZGRJSVFVGHSUBZUDZUEZUARZVDAVCVJUAAP
        QVEBCDEFGHIJKLMNOVEUFUGUHAVDTUIVITUIVKVDUJAIGTTAIJCFUKSZULITUINIJVLCFUM
        UNUOAGHBCUKSZULGTUIMGHVMBCUMUNUOUPPQVEVEVHBUCUQZVNURVDVITTUSUTVA $.

      fuco111x.x $e |- ( ph -> X e. ( Base ` C ) ) $.
      $( The object part of the functor composition bifunctor maps two functors
         to their composition, expressed explicitly for the object part of the
         composed functor.  An object is mapped by two functors in succession.
         (Contributed by Zhi Wang, 3-Oct-2025.) $)
      fuco111x $p |- ( ph ->
              ( ( 1st ` ( O ` U ) ) ` X ) = ( K ` ( F ` X ) ) ) $=
        ( cfv cbs eqid c1st ccom fuco111 fveq1d funcf1 fvco3d eqtrd ) ALEKRUARZ
        RLIGUBZRLGRIRALUHUIABCDEFGHIJKMNOPUCUDABSRZCSRZLIGAUJUKBCGHUJTUKTNUEQUF
        UG $.

      fuco112x.y $e |- ( ph -> Y e. ( Base ` C ) ) $.
      $( The object part of the functor composition bifunctor maps two functors
         to their composition, expressed explicitly for the morphism part of
         the composed functor.  (Contributed by Zhi Wang, 3-Oct-2025.) $)
      fuco112x $p |- ( ph -> ( X ( 2nd ` ( O ` U ) ) Y ) =
                    ( ( ( F ` X ) L ( F ` Y ) ) o. ( X G Y ) ) ) $=
        ( cfv vx vy cbs cv ccom c2nd cvv eqid fuco112 wceq simprl fveq2d simprr
        co wa oveq12d coeq12d ovexd coexd ovmpod ) AUAUBLMBUCTZVAUAUDZGTZUBUDZG
        TZJUNZVBVDHUNZUELGTZMGTZJUNZLMHUNZUEEKTUFTUGAUAUBVABCDEFGHIJKNOPQVAUHUI
        AVBLUJZVDMUJZUOUOZVFVJVGVKVNVCVHVEVIJVNVBLGAVLVMUKZULVNVDMGAVLVMUMZULUP
        VNVBLVDMHVOVPUPUQRSAVJVKUGUGAVHVIJURALMHURUSUT $.

      fuco112xa.a $e |- ( ph -> A e. ( X ( Hom ` C ) Y ) ) $.
      $( The object part of the functor composition bifunctor maps two functors
         to their composition, expressed explicitly for the morphism part of
         the composed functor.  A morphism is mapped by two functors in
         succession.  (Contributed by Zhi Wang, 3-Oct-2025.) $)
      fuco112xa $p |- ( ph -> ( ( X ( 2nd ` ( O ` U ) ) Y ) ` A ) =
                    ( ( ( F ` X ) L ( F ` Y ) ) ` ( ( X G Y ) ` A ) ) ) $=
        ( cfv c2nd co ccom fuco112x fveq1d chom cbs eqid funcf2 fvco3d eqtrd )
        ABMNFLUBUCUBUDZUBBMHUBZNHUBZKUDZMNIUDZUEZUBBURUBUQUBABUNUSACDEFGHIJKLMN
        OPQRSTUFUGAMNCUHUBZUDUOUPDUHUBZUDBUQURACUIUBZCDHIUTVAMNVBUJUTUJVAUJPSTU
        KUAULUM $.
    $}

    ${
      fuco11id.q $e |- Q = ( C FuncCat E ) $.
      fuco11id.i $e |- I = ( Id ` Q ) $.
      fuco11id.1 $e |- .1. = ( Id ` E ) $.
      $( The identity morphism of the mapped object.  (Contributed by Zhi Wang,
         30-Sep-2025.) $)
      fuco11id $p |- ( ph -> ( I ` ( O ` U ) ) = ( .1. o. ( K o. F ) ) ) $=
        ( cfv c1st ccom fuco11cl fucid fuco111 coeq2d eqtrd ) AFNUBZKUBGUJUCUBZ
        UDGLIUDZUDABHEGUJKSTUAABCDFHIJLMNOPQRUEUFAUKULGABCDFHIJLMNOPQRUGUHUI $.

      fuco11idx.x $e |- ( ph -> X e. ( Base ` C ) ) $.
      $( The identity morphism of the mapped object.  (Contributed by Zhi Wang,
         3-Oct-2025.) $)
      fuco11idx $p |- ( ph -> ( ( I ` ( O ` U ) ) ` X )
            = ( .1. ` ( K ` ( F ` X ) ) ) ) $=
        ( cfv ccom fuco11id coass eqtr4di fveq1d funcf1 fvco3d ffvelcdmd 3eqtrd
        cbs eqid ) AOFNUDKUDZUDOGLUEZIUEZUDOIUDZUQUDUSLUDGUDAOUPURAUPGLIUEUEURA
        BCDEFGHIJKLMNPQRSTUAUBUFGLIUGUHUIABUNUDZCUNUDZOUQIAUTVABCIJUTUOVAUOZQUJ
        ZUCUKAVAHUNUDZUSGLAVAVDCHLMVBVDUORUJAUTVAOIVCUCULUKUM $.
    $}

    $d C a b f k l m r u v x $.  $d D a b f k l m r u v x $.
    $d E a b f k l m r u v x $.  $d F a b f k l m r u v x $.
    $d G a b f k l m r u v $.  $d K a b f k l m r u v x $.
    $d L a b f k l m r u v x $.  $d M a b f k l m r u v x $.
    $d N a b f k l m r u v $.  $d O f k l m r u v $.  $d P f k l m r u v $.
    $d R a b f k l m r u v x $.  $d S a b f k l m r u v $.
    $d U a b f k l m r u v x $.  $d V a b f k l m r u v x $.
    $d a b f k l m ph r u v x $.
    fuco21.m $e |- ( ph -> M ( C Func D ) N ) $.
    fuco21.r $e |- ( ph -> R ( D Func E ) S ) $.
    fuco21.v $e |- ( ph -> V = <. <. R , S >. , <. M , N >. >. ) $.
    $( The morphism part of the functor composition bifunctor.  (Contributed by
       Zhi Wang, 29-Sep-2025.) $)
    fuco21 $p |- ( ph -> ( U P V ) = (
                b e. ( <. K , L >. ( D Nat E ) <. R , S >. ) ,
                a e. ( <. F , G >. ( C Nat D ) <. M , N >. ) |->
              ( x e. ( Base ` C ) |-> ( ( b ` ( M ` x ) )
              ( <. ( K ` ( F ` x ) ) , ( K ` ( M ` x ) ) >.
                ( comp ` E ) ( R ` ( M ` x ) ) )
              ( ( ( F ` x ) L ( M ` x ) ) ` ( a ` x ) ) ) ) ) ) $=
      ( vu vv vf vk vl vm vr cfunc cxp c2nd cfv c1st cnat cbs cop cco cmpt cmpo
      co cv csb cvv ccat funcrcl2 funcrcl3 eqidd fuco2 wceq fvexd simprl adantr
      wa eqtrd fveq2d opex op2nd fveq2i wcel relfunc brrelex1i brrelex2i op1stg
      wbr syl2anc eqtrid op1st ad2antrr op2ndg ad3antrrr simp-4r simprd ad4antr
      syl ad5antr eqtrdi oveq12d simp-5r fveq1d fveq12d simplr opeq12d oveq123d
      simpr simpllr mpteq2dv mpoeq123dv csbied2 fuco2eld ovex mpoex a1i ovmpod
      ) AUGUHHQDIUNVEZCDUNVEZUOZYAUIUGVFZUPUQZURUQZUJYBURUQZURUQZUKYEUPUQZULUHV
      FZUPUQZURUQZUMYHURUQZURUQZSRYEYKDIUSVEZVEZYCYICDUSVEZVEZBCUTUQZBVFZULVFZU
      QZSVFZUQZYRRVFUQZYRUIVFZUQZYTUKVFZVEZUQZUUEUJVFZUQZYTUUIUQZVAZYTUMVFZUQZI
      VBUQZVEZVEZVCZVDZVGZVGZVGZVGZVGSRLMVAZFGVAZYMVEZJKVAZNOVAZYOVEZBYQYRNUQZU
      UAUQZUUCYRJUQZUVJMVEZUQZUVLLUQZUVJLUQZVAZUVJFUQZUUOVEZVEZVCZVDZEVHABUHUGC
      DEVIVIUIUJULIPVIYAUMRSUKACDJKUAVJADILMUBVJADILMUBVKTAYAVLZVMAYBHVNZYHQVNZ
      VRZVRZUIYDJUVCUWBVHUWGYCURVOUWGYDUVDUVGVAZUPUQZURUQZJUWGYCUWIURUWGYBUWHUP
      UWGYBHUWHAUWDUWEVPZAHUWHVNZUWFUCVQZVSVTZVTAUWJJVNUWFAUWJUVGURUQZJUWIUVGUR
      UVDUVGLMWAZJKWAZWBZWCAJVHWDZKVHWDZUWOJVNAJKXTWIZUWSUAJKXTCDWEZWFWSAUXAUWT
      UAJKXTUXBWGWSJKVHVHWHWJWKVQVSUWGUUDJVNZVRZUJYFLUVBUWBVHUXDYEURVOUXDYFUWHU
      RUQZURUQZLUXDYEUXEURUXDYBUWHURUXDYBHUWHUWGUWDUXCUWKVQZUWGUWLUXCUWMVQZVSVT
      VTAUXFLVNUWFUXCAUXFUVDURUQZLUXEUVDURUVDUVGUWPUWQWLZWCALVHWDZMVHWDZUXILVNA
      LMXSWIZUXKUBLMXSDIWEZWFWSZAUXMUXLUBLMXSUXNWGWSZLMVHVHWHWJWKWMVSUXDUUILVNZ
      VRZUKYGMUVAUWBVHUXRYEUPVOUXRYGUXEUPUQZMUXRYEUXEUPUXRYBUWHURUXRYBHUWHUXDUW
      DUXQUXGVQUXDUWLUXQUXHVQVSVTZVTAUXSMVNUWFUXCUXQAUXSUVDUPUQZMUXEUVDUPUXJWCA
      UXKUXLUYAMVNUXOUXPLMVHVHWNWJWKWOVSUXRUUFMVNZVRZULYJNUUTUWBVHUYCYIURVOUYCY
      JUVEUVHVAZUPUQZURUQZNUYCYIUYEURUYCYHUYDUPUYCYHQUYDUYCUWDUWEAUWFUXCUXQUYBW
      PWQZAQUYDVNZUWFUXCUXQUYBUFWRZVSVTZVTAUYFNVNUWFUXCUXQUYBAUYFUVHURUQZNUYEUV
      HURUVEUVHFGWAZNOWAZWBZWCANVHWDZOVHWDZUYKNVNANOXTWIZUYOUDNOXTUXBWFWSAUYQUY
      PUDNOXTUXBWGWSNOVHVHWHWJWKWRVSUYCYSNVNZVRZUMYLFUUSUWBVHUYSYKURVOUYSYLUYDU
      RUQZURUQZFUYSYKUYTURUYSYHUYDURUYSYHQUYDUYCUWEUYRUYGVQUYCUYHUYRUYIVQVSVTZV
      TAVUAFVNUWFUXCUXQUYBUYRAVUAUVEURUQZFUYTUVEURUVEUVHUYLUYMWLZWCAFVHWDZGVHWD
      ZVUCFVNAFGXSWIZVUEUEFGXSUXNWFWSAVUGVUFUEFGXSUXNWGWSFGVHVHWHWJWKWTVSUYSUUM
      FVNZVRZSRYNYPUURUVFUVIUWAVUIYEUVDYKUVEYMVUIYEUXEUVDUXRYEUXEVNUYBUYRVUHUXT
      WOUXJXAVUIYKUYTUVEUYSYKUYTVNVUHVUBVQVUDXAXBVUIYCUVGYIUVHYOVUIYCUWIUVGUWGY
      CUWIVNUXCUXQUYBUYRVUHUWNWTUWRXAVUIYIUYEUVHUYCYIUYEVNUYRVUHUYJWMUYNXAXBVUI
      BYQUUQUVTVUIUUBUVKUUHUVNUUPUVSVUIUULUVQUUNUVRUUOVUIUUJUVOUUKUVPVUIUUEUVLU
      UILUXDUXQUYBUYRVUHWPZVUIYRUUDJUWGUXCUXQUYBUYRVUHXCXDZXEVUIYTUVJUUILVUJVUI
      YRYSNUYCUYRVUHXFXDZXEXGVUIYTUVJUUMFUYSVUHXIVULXEXBVUIYTUVJUUAVULVTVUIUUCU
      UGUVMVUIUUEUVLYTUVJUUFMUXRUYBUYRVUHXJVUKVULXHXDXHXKXLXMXMXMXMXMAXTXSHJKLM
      YAUWCUCUBUAXNAXTXSQNOFGYAUWCUFUEUDXNUWBVHWDASRUVFUVIUWAUVDUVEYMXOUVGUVHYO
      XOXPXQXR $.
  $}

  ${
    fuco11b.o $e |- ( ph -> ( 1st ` ( <. C , D >. o.F E ) ) = O ) $.
    fuco11b.f $e |- ( ph -> F e. ( C Func D ) ) $.
    fuco11b.g $e |- ( ph -> G e. ( D Func E ) ) $.
    $( The object part of the functor composition bifunctor maps two functors
       to their composition.  (Contributed by Zhi Wang, 11-Oct-2025.) $)
    fuco11b $p |- ( ph -> ( G O F ) = ( G o.func F ) ) $=
      ( co ccofu cfunc cxp c1st cfv c2nd ccat cvv wcel cres func1st2nd funcrcl2
      cop cfuco funcrcl3 wceq eqidd fucoelvv 1st2nd2 fuco1 eqtr3d oveqd syl2anc
      syl ovres eqtrd ) AFEGKFELCDMKZBCMKZNZUAZKZFELKZAGVAFEABCUDDUEKZOPZGVAHAB
      CVDQPZRRDVERUTABCEOPEQPABCEIUBUCZACDFOPZFQPZACDFJUBZUCZACDVHVIVJUFZAVDSSN
      TVDVEVFUDUGABCRRDRVDVGVKVLAVDUHUIVDSSUJUOAUTUHUKULUMAFURTEUSTVBVCUGJIFEUR
      USLUPUNUQ $.

    $( Alternate proof of ~ fuco11b .  (Contributed by Zhi Wang, 11-Oct-2025.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    fuco11bALT $p |- ( ph -> ( G O F ) = ( G o.func F ) ) $=
      ( co cop cfv ccofu c1st c2nd wcel wceq sylancr cvv df-ov cfuco cfunc wrel
      relfunc 1st2nd oveq12d cxp ccat 1st2ndbr funcrcl2 funcrcl3 eqidd fucoelvv
      wbr 1st2nd2 syl opeq12d fuco11 fveq1d 3eqtr2rd eqtrid ) AFEGKFELZGMZFENKZ
      FEGUAAVEFOMZFPMZLZEOMZEPMZLZNKVCBCLDUBKZOMZMVDAFVHEVKNACDUCKZUDZFVNQZFVHR
      CDUEZJFVNUFSZABCUCKZUDZEVSQZEVKRBCUEZIEVSUFSZUGABCVLPMZVCDVIVJVFVGVMAVLTT
      UHQVLVMWDLRABCUIUIDUIVLABCVIVJAVTWAVIVJVSUOWBIEVSUJSZUKACDVFVGAVOVPVFVGVN
      UOVQJFVNUJSZUKACDVFVGWFULAVLUMUNVLTTUPUQWEWFAFVHEVKVRWCURUSAVCVMGHUTVAVB
      $.
  $}

  ${
    $d A a b x $.  $d B a b x $.  $d C a b x $.  $d D a b x $.  $d E a b x $.
    $d F a b x $.  $d G a b $.  $d K a b x $.  $d L a b x $.  $d M a b x $.
    $d N a b $.  $d O a b $.  $d P a b $.  $d R a b x $.  $d S a b $.
    $d U a b x $.  $d V a b x $.  $d a b ph x $.
    fuco22.o $e |- ( ph -> ( <. C , D >. o.F E ) = <. O , P >. ) $.
    fuco22.u $e |- ( ph -> U = <. <. K , L >. , <. F , G >. >. ) $.
    fuco22.v $e |- ( ph -> V = <. <. R , S >. , <. M , N >. >. ) $.
    fuco22.a $e |- ( ph -> A e. ( <. F , G >. ( C Nat D ) <. M , N >. ) ) $.
    fuco22.b $e |- ( ph -> B e. ( <. K , L >. ( D Nat E ) <. R , S >. ) ) $.
    $( The morphism part of the functor composition bifunctor.  See also
       ~ fuco22a .  (Contributed by Zhi Wang, 29-Sep-2025.) $)
    fuco22 $p |- ( ph -> ( B ( U P V ) A ) = ( x e. ( Base ` C ) |->
               ( ( B ` ( M ` x ) )
               ( <. ( K ` ( F ` x ) ) , ( K ` ( M ` x ) ) >.
                 ( comp ` E ) ( R ` ( M ` x ) ) )
               ( ( ( F ` x ) L ( M ` x ) ) ` ( A ` x ) ) ) ) ) $=
      ( vb va cop cnat co cbs cfv cco cmpt cvv eqid natrcl2 natrcl3 fuco21 wceq
      cv wa simplrl fveq1d simplrr fveq2d oveq12d mpteq2dva fvexd mptexd ovmpod
      wcel ) AUEUFDCNOUGHIUGFKUHUIZUILMUGPQUGEFUHUIZUIBEUJUKZBUTZPUKZUEUTZUKZVO
      UFUTZUKZVOLUKZVPOUIZUKZWANUKVPNUKUGVPHUKKULUKUIZUIZUMBVNVPDUKZVOCUKZWBUKZ
      WDUIZUMJSGUIUNABEFGHIJKLMNOPQRSUFUETACEFLMPQVMVMUOZUCUPADFKNOHIVLVLUOZUDU
      PUAACEFLMPQVMWJUCUQADFKNOHIVLWKUDUQUBURAVQDUSZVSCUSZVAVAZBVNWEWIWNVOVNVKZ
      VAZVRWFWCWHWDWPVPVQDAWLWMWOVBVCWPVTWGWBWPVOVSCAWLWMWOVDVCVEVFVGUDUCABVNWI
      UNAEUJVHVIVJ $.

    $d .* x $.  $d G x $.  $d N x $.  $d O x $.  $d P x $.  $d S x $.
    $d X x $.
    $( The morphism part of the functor composition bifunctor maps two natural
       transformations to a function on a base set.  (Contributed by Zhi Wang,
       30-Sep-2025.) $)
    fucofn22 $p |- ( ph -> ( B ( U P V ) A ) Fn ( Base ` C ) ) $=
      ( vx co cbs cfv wfn cv cop cco cmpt ovex eqid fnmpti fuco22 fneq1d mpbiri
      ) ACBIRFUEUEZDUFUGZUHUDUTUDUIZOUGZCUGZVABUGVAKUGZVBNUEUGZVDMUGVBMUGUJVBGU
      GJUKUGUEZUEZULZUTUHUDUTVGVHVCVEVFUMVHUNUOAUTUSVHAUDBCDEFGHIJKLMNOPQRSTUAU
      BUCUPUQUR $.

    fuco23.x $e |- ( ph -> X e. ( Base ` C ) ) $.
    fuco23.o $e |- ( ph -> .* = ( <. ( K ` ( F ` X ) ) , ( K ` ( M ` X ) ) >.
                ( comp ` E ) ( R ` ( M ` X ) ) ) ) $.
    $( The morphism part of the functor composition bifunctor.  See also
       ~ fuco23a .  (Contributed by Zhi Wang, 29-Sep-2025.) $)
    fuco23 $p |- ( ph -> ( ( B ( U P V ) A ) ` X ) =
        ( ( B ` ( M ` X ) ) .* ( ( ( F ` X ) L ( M ` X ) ) ` ( A ` X ) ) ) ) $=
      ( vx cv cfv co cop cco cbs cvv fuco22 wceq wa simpr fveq2d opeq12d adantr
      oveq12d eqtr4d fveq12d oveq123d ovexd fvmptd ) AUHTUHUIZPUJZCUJZVIBUJZVIK
      UJZVJOUKZUJZVMNUJZVJNUJZULZVJGUJZJUMUJZUKZUKTPUJZCUJZTBUJZTKUJZWBOUKZUJZM
      UKDUNUJCBISFUKUKUOAUHBCDEFGHIJKLNOPQRSUAUBUCUDUEUPAVITUQZURZVKWCVOWGWAMWI
      WAWENUJZWBNUJZULZWBGUJZVTUKZMWIVRWLVSWMVTWIVPWJVQWKWIVMWENWIVITKAWHUSZUTZ
      UTWIVJWBNWIVITPWOUTZUTVAWIVJWBGWQUTVCAMWNUQWHUGVBVDWIVJWBCWQUTWIVLWDVNWFW
      IVMWEVJWBOWPWQVCWIVITBWOUTVEVFUFAWCWGMVGVH $.
  $}

  ${
    fuco22natlem1.x $e |- ( ph -> X e. ( Base ` C ) ) $.
    fuco22natlem1.y $e |- ( ph -> Y e. ( Base ` C ) ) $.
    fuco22natlem1.a $e |- ( ph ->
        A e. ( <. F , G >. ( C Nat D ) <. M , N >. ) ) $.
    fuco22natlem1.h $e |- ( ph -> H e. ( X ( Hom ` C ) Y ) ) $.
    ${
      fuco22natlem1.k $e |- ( ph -> K ( D Func E ) L ) $.
      $( Lemma for ~ fuco22nat .  The commutative square of natural
         transformation ` A ` in category ` D ` , mapped to category ` E ` by
         the morphism part ` L ` of the functor.  (Contributed by Zhi Wang,
         30-Sep-2025.) $)
      fuco22natlem1 $p |- ( ph ->
              ( ( ( ( F ` Y ) L ( M ` Y ) ) ` ( A ` Y ) )
               ( <. ( K ` ( F ` X ) ) , ( K ` ( F ` Y ) ) >.
                 ( comp ` E ) ( K ` ( M ` Y ) ) )
                ( ( ( F ` X ) L ( F ` Y ) ) ` ( ( X G Y ) ` H ) ) )
            = ( ( ( ( M ` X ) L ( M ` Y ) ) ` ( ( X N Y ) ` H ) )
               ( <. ( K ` ( F ` X ) ) , ( K ` ( M ` X ) ) >.
                 ( comp ` E ) ( K ` ( M ` Y ) ) )
                ( ( ( F ` X ) L ( M ` X ) ) ` ( A ` X ) ) ) ) $=
        ( cfv co cop cco chom cnat eqid fveq2d natrcl2 funcf1 ffvelcdmd natrcl3
        cbs nati funcf2 natcl funcco 3eqtr3d ) ANBTZHMNGUAZTZMFTZNFTZUBNKTZDUCT
        ZUAUAZVAVCJUAZTHMNLUAZTZMBTZVAMKTZUBVCVDUAUAZVFTURVBVCJUATUTVAVBJUATVAI
        TZVBITUBVCITZEUCTZUAUAVHVJVCJUATVIVAVJJUATVLVJITUBVMVNUAUAAVEVKVFABCULT
        ZCDHVDFGCUDTZKLCDUEUAZMNVQUFZQVOUFZVPUFZVDUFZOPRUMUGADULTZDVDEIJDUDTZUT
        URVNVAVBVCWBUFZWCUFZWAVNUFZSAVOWBMFAVOWBCDFGVSWDABCDFGKLVQVRQUHZUIZOUJZ
        AVOWBNFWHPUJAVOWBNKAVOWBCDKLVSWDABCDFGKLVQVRQUKZUIZPUJZAMNVPUAZVAVBWCUA
        HUSAVOCDFGVPWCMNVSVTWEWGOPUNRUJABVOCDFGWCKLVQNVRQVSWEPUOUPAWBDVDEIJWCVI
        VHVNVAVJVCWDWEWAWFSWIAVOWBMKWKOUJWLABVOCDFGWCKLVQMVRQVSWEOUOAWMVJVCWCUA
        HVGAVOCDKLVPWCMNVSVTWEWJOPUNRUJUPUQ $.
    $}

    fuco22natlem2.b $e |- ( ph ->
            B e. ( <. K , L >. ( D Nat E ) <. R , S >. ) ) $.
    $( Lemma for ~ fuco22nat .  The commutative square of natural
       transformation ` B ` in category ` E ` , combined with the commutative
       square of ~ fuco22natlem1 .  (Contributed by Zhi Wang, 30-Sep-2025.) $)
    fuco22natlem2 $p |- ( ph -> ( ( ( B ` ( M ` Y ) )
              ( <. ( K ` ( F ` Y ) ) , ( K ` ( M ` Y ) ) >.
                ( comp ` E ) ( R ` ( M ` Y ) ) )
              ( ( ( F ` Y ) L ( M ` Y ) ) ` ( A ` Y ) ) )
              ( <. ( K ` ( F ` X ) ) , ( K ` ( F ` Y ) ) >.
                ( comp ` E ) ( R ` ( M ` Y ) ) )
              ( ( ( F ` X ) L ( F ` Y ) ) ` ( ( X G Y ) ` H ) ) )
              = ( ( ( ( M ` X ) S ( M ` Y ) ) ` ( ( X N Y ) ` H ) )
              ( <. ( K ` ( F ` X ) ) , ( R ` ( M ` X ) ) >.
                ( comp ` E ) ( R ` ( M ` Y ) ) )
              ( ( B ` ( M ` X ) )
              ( <. ( K ` ( F ` X ) ) , ( K ` ( M ` X ) ) >.
                ( comp ` E ) ( R ` ( M ` X ) ) )
              ( ( ( F ` X ) L ( M ` X ) ) ` ( A ` X ) ) ) ) ) $=
      ( cfv co cop cco chom eqid cnat natrcl2 funcrcl3 funcf1 ffvelcdmd natrcl3
      cbs funcf2 natcl catass fuco22natlem1 oveq2d nati oveq1d 3eqtr3d 3eqtrd )
      AQNUCZCUCZQBUCZQIUCZVEMUDZUCZVHLUCZVELUCZUEVEFUCZHUFUCZUDUDKPQJUDZUCZPIUC
      ZVHMUDZUCZVQLUCZVKUEZVMVNUDUDVFVJVSWAVLVNUDUDZVTVLUEVMVNUDZUDVFKPQOUDZUCZ
      PNUCZVEMUDZUCZPBUCZVQWFMUDZUCZVTWFLUCZUEZVLVNUDUDZWCUDZWEWFVEGUDZUCZWFCUC
      ZWKWMWFFUCZVNUDUDVTWSUEVMVNUDUDZAHUOUCZHVNVSVJHUGUCZVFVMVTVKVLXAUHZXBUHZV
      NUHZAEHLMACEHLMFGEHUIUDZXFUHZUBUJZUKZAEUOUCZXAVQLAXJXAEHLMXJUHZXCXHULZADU
      OUCZXJPIAXMXJDEIJXMUHZXKABDEIJNODEUIUDZXOUHZTUJZULZRUMZUMZAXJXAVHLXLAXMXJ
      QIXRSUMZUMAXJXAVELXLAXMXJQNAXMXJDENOXNXKABDEIJNOXOXPTUNZULZSUMZUMZAVQVHEU
      GUCZUDZVTVKXBUDVPVRAXJEHLMYFXBVQVHXKYFUHZXDXHXSYAUPAPQDUGUCZUDZYGKVOAXMDE
      IJYIYFPQXNYIUHZYHXQRSUPUAUMUMAVHVEYFUDVKVLXBUDVGVIAXJEHLMYFXBVHVEXKYHXDXH
      YAYDUPABXMDEIJYFNOXOQXPTXNYHSUQUMAXJXAVEFAXJXAEHFGXKXCACEHLMFGXFXGUBUNZUL
      ZYDUMZACXJEHLMXBFGXFVEXGUBXKXDYDUQZURAWBWNVFWCABDEHIJKLMNOPQRSTUAXHUSUTAV
      FWHWLVLUEVMVNUDUDZWKWMVMVNUDZUDWQWRWLWSUEVMVNUDUDZWKYQUDWOWTAYPYRWKYQACXJ
      EHWEVNLMYFFGXFWFVEXGUBXKYHXEAXMXJPNYCRUMZYDAYJWFVEYFUDZKWDAXMDENOYIYFPQXN
      YKYHYBRSUPUAUMZVAVBAXAHVNWKWHXBVFVMVTWLVLXCXDXEXIXTAXJXAWFLXLYSUMZYEAVQWF
      YFUDVTWLXBUDWIWJAXJEHLMYFXBVQWFXKYHXDXHXSYSUPABXMDEIJYFNOXOPXPTXNYHRUQUMZ
      AYTWLVLXBUDWEWGAXJEHLMYFXBWFVEXKYHXDXHYSYDUPUUAUMYNYOURAXAHVNWKWRXBWQVMVT
      WLWSXCXDXEXIXTUUBAXJXAWFFYMYSUMUUCACXJEHLMXBFGXFWFXGUBXKXDYSUQYNAYTWSVMXB
      UDWEWPAXJEHFGYFXBWFVEXKYHXDYLYSYDUPUUAUMURVCVD $.

    fuco22natlem3.o $e |- ( ph -> ( <. C , D >. o.F E ) = <. O , P >. ) $.
    fuco22natlem3.u $e |- ( ph -> U = <. <. K , L >. , <. F , G >. >. ) $.
    fuco22natlem3.v $e |- ( ph -> V = <. <. R , S >. , <. M , N >. >. ) $.
    $( Combine ~ fuco22natlem2 with ~ fuco23 .  (Contributed by Zhi Wang,
       30-Sep-2025.) $)
    fuco22natlem3 $p |- ( ph -> (
                   ( ( B ( U P V ) A ) ` Y )
                        ( <. ( ( K o. F ) ` X ) , ( ( K o. F ) ` Y ) >.
                                     ( comp ` E ) ( ( R o. M ) ` Y ) )
                   ( ( ( ( F ` X ) L ( F ` Y ) ) o. ( X G Y ) ) ` H )
                  ) = (
                   ( ( ( ( M ` X ) S ( M ` Y ) ) o. ( X N Y ) ) ` H )
                        ( <. ( ( K o. F ) ` X ) , ( ( R o. M ) ` X ) >.
                                     ( comp ` E ) ( ( R o. M ) ` Y ) )
                   ( ( B ( U P V ) A ) ` X )
                  ) ) $=
      ( cfv co cop cco ccom fuco22natlem2 cbs eqid cnat natrcl2 opeq12d natrcl3
      funcf1 fvco3d oveq12d eqidd fuco23 chom funcf2 oveq123d 3eqtr4d ) AUAPUJZ
      CUJUABUJUAKUJZVKOUKUJVLNUJZVKNUJULVKGUJZJUMUJZUKZUKZMTUALUKZUJTKUJZVLOUKZ
      UJZVSNUJZVMULZVNVOUKZUKMTUAQUKZUJTPUJZVKHUKZUJZWFCUJTBUJVSWFOUKUJWBWFNUJU
      LWFGUJZVOUKZUKZWBWIULZVNVOUKZUKUACBISFUKUKZUJZMVTVRUNUJZTNKUNZUJZUAWQUJZU
      LZUAGPUNZUJZVOUKZUKMWGWEUNUJZTWNUJZWRTXAUJZULZXBVOUKZUKABCDEGHJKLMNOPQTUA
      UBUCUDUEUFUOAWOVQWPWAXCWDAWTWCXBVNVOAWRWBWSVMADUPUJZEUPUJZTNKAXIXJDEKLXIU
      QZXJUQZABDEKLPQDEURUKZXMUQZUDUSZVBZUBVCZAXIXJUANKXPUCVCUTAXIXJUAGPAXIXJDE
      PQXKXLABDEKLPQXMXNUDVAZVBZUCVCZVDABCDEFGHIJKLVPNOPQRSUAUGUHUIUDUFUCAVPVEV
      FATUADVGUJZUKZVSVLEVGUJZUKMVTVRAXIDEKLYAYCTUAXKYAUQZYCUQZXOUBUCVHUEVCVIAX
      DWHXEWKXHWMAXGWLXBVNVOAWRWBXFWIXQAXIXJTGPXSUBVCUTXTVDAYBWFVKYCUKMWGWEAXID
      EPQYAYCTUAXKYDYEXRUBUCVHUEVCABCDEFGHIJKLWJNOPQRSTUGUHUIUDUFUBAWJVEVFVIVJ
      $.
  $}

  ${
    $d A h w x y z $.  $d B h w x y z $.  $d C h w x y z $.  $d D h w x y z $.
    $d E h w x y z $.  $d F h w x y z $.  $d G h w x y z $.  $d K h w x y z $.
    $d L h w x y z $.  $d M h w x y z $.  $d N h w x y z $.  $d O h w x y z $.
    $d P h w x y z $.  $d R h w x y z $.  $d S h w x y z $.  $d U h w x y z $.
    $d V h w x y z $.  $d h ph w x y z $.
    fuco22natlem.o $e |- ( ph -> ( <. C , D >. o.F E ) = <. O , P >. ) $.
    fuco22natlem.a $e |- ( ph ->
        A e. ( <. F , G >. ( C Nat D ) <. M , N >. ) ) $.
    fuco22natlem.b $e |- ( ph ->
            B e. ( <. K , L >. ( D Nat E ) <. R , S >. ) ) $.
    fuco22natlem.u $e |- ( ph -> U = <. <. K , L >. , <. F , G >. >. ) $.
    fuco22natlem.v $e |- ( ph -> V = <. <. R , S >. , <. M , N >. >. ) $.
    $( The composed natural transformation is a natural transformation.  Use
       ~ fuco22nat instead.  (New usage is discouraged.)  (Contributed by Zhi
       Wang, 30-Sep-2025.) $)
    fuco22natlem $p |- ( ph -> ( B ( U P V ) A ) e.
            ( ( O ` U ) ( C Nat E ) ( O ` V ) ) ) $=
      ( vz vw vx vy vh co ccom cbs cfv cv cmpo cop cnat cco chom eqid cfunc wbr
      natrcl2 fuco11a fuco11cl eqeltrrd df-br sylibr natrcl3 fucofn22 wa adantr
      wcel funcrcl3 funcf1 simpr ffvelcdmd funcf2 natcl ffvelcdmda catcocl wceq
      cfuco eqidd fuco23 oveq12d 3eltr4d simplrl simplrr ad2antrr fuco22natlem3
      fvco3d fveq2 oveq1d oveq1 coeq12d oveq2d oveq2 ovex ovmpo ad2antlr fveq1d
      coex 3eqtr4d isnatd eleqtrrd ) ACBIRFUIUIZMKUJZUDUEDUKULZXHUDUMZKULZUEUMZ
      KULZNUIZXIXKLUIZUJZUNZUOZGOUJZUDUEXHXHXIOULZXKOULZHUIZXIXKPUIZUJZUNZUOZDJ
      UPUIZUIIQULZRQULZYFUIAUFUGXFXHDJJUQULZUHXGXPDURULZJURULZXRYDYFYFUSXHUSZYJ
      USYKUSZYIUSZAXQDJUTUIZVLXGXPYOVAAYGXQYOAUDUEXHDEFIJKLMNQSABDEKLOPDEUPUIZY
      PUSZTVBZACEJMNGHEJUPUIZYSUSZUAVBZUBYLVCZADEFIJKLMNQSYRUUAUBVDVEXGXPYOVFVG
      AYEYOVLXRYDYOVAAYHYEYOAUDUEXHDEFRJOPGHQSABDEKLOPYPYQTVHZACEJMNGHYSYTUAVHZ
      UCYLVCZADEFRJOPGHQSUUCUUDUCVDVEXRYDYOVFVGABCDEFGHIJKLMNOPQRSUBUCTUAVIAUFU
      MZXHVLZVJZUUFOULZCULZUUFBULZUUFKULZUUINUIZULZUULMULZUUIMULZUOUUIGULZYIUIZ
      UIUUOUUQYKUIUUFXFULZUUFXGULZUUFXRULZYKUIUUHJUKULZJYIUUNUUJYKUUOUUPUUQUVBU
      SZYMYNUUHEJMNAMNEJUTUIZVAUUGUUAVKZVMUUHEUKULZUVBUULMUUHUVFUVBEJMNUVFUSZUV
      CUVEVNZUUHXHUVFUUFKUUHXHUVFDEKLYLUVGAKLDEUTUIZVAUUGYRVKVNZAUUGVOZVPZVPUUH
      UVFUVBUUIMUVHUUHXHUVFUUFOUUHXHUVFDEOPYLUVGAOPUVIVAUUGUUCVKVNZUVKVPZVPUUHU
      VFUVBUUIGUUHUVFUVBEJGHUVGUVCAGHUVDVAUUGUUDVKVNUVNVPUUHUULUUIEURULZUIUUOUU
      PYKUIUUKUUMUUHUVFEJMNUVOYKUULUUIUVGUVOUSZYMUVEUVLUVNVQUUHBXHDEKLUVOOPYPUU
      FYQABKLUOZOPUOZYPUIVLZUUGTVKZYLUVPUVKVRVPUUHCUVFEJMNYKGHYSUUIYTACMNUOZGHU
      OZYSUIVLZUUGUAVKZUVGYMAXHUVFUUFOAXHUVFDEOPYLUVGUUCVNVSVRVTUUHBCDEFGHIJKLU
      URMNOPQRUUFADEUOJWBUIQFUOWAZUUGSVKAIUWAUVQUOWAZUUGUBVKARUWBUVRUOWAZUUGUCV
      KUVTUWDUVKUUHUURWCWDUUHUUTUUOUVAUUQYKUUHXHUVFUUFMKUVJUVKWKUUHXHUVFUUFGOUV
      MUVKWKWEWFAUUGUGUMZXHVLZVJZVJZUHUMZUUFUWHYJUIVLZVJZUWHXFULZUWLUULUWHKULZN
      UIZUUFUWHLUIZUJZULZUUTUWHXGULUOUWHXRULZYIUIZUIUWLUUIUWHOULZHUIZUUFUWHPUIZ
      UJZULZUUSUUTUVAUOUXAYIUIZUIUWOUWLUUFUWHXPUIZULZUXBUIUWLUUFUWHYDUIZULZUUSU
      XHUIUWNBCDEFGHIJKLUWLMNOPQRUUFUWHAUUGUWIUWMWGAUUGUWIUWMWHAUVSUWJUWMTWIUWK
      UWMVOAUWCUWJUWMUAWIAUWEUWJUWMSWIAUWFUWJUWMUBWIAUWGUWJUWMUCWIWJUWNUXJUWTUW
      OUXBUWNUWLUXIUWSUWJUXIUWSWAAUWMUDUEUUFUWHXHXHXOUWSXPUULXLNUIZUUFXKLUIZUJX
      IUUFWAZXMUXMXNUXNUXOXJUULXLNXIUUFKWLWMXIUUFXKLWNWOXKUWHWAZUXMUWQUXNUWRUXP
      XLUWPUULNXKUWHKWLWPXKUWHUUFLWQWOXPUSUWQUWRUULUWPNWRUUFUWHLWRXBWSWTXAWPUWN
      UXLUXGUUSUXHUWNUWLUXKUXFUWJUXKUXFWAAUWMUDUEUUFUWHXHXHYCUXFYDUUIXTHUIZUUFX
      KPUIZUJUXOYAUXQYBUXRUXOXSUUIXTHXIUUFOWLWMXIUUFXKPWNWOUXPUXQUXDUXRUXEUXPXT
      UXCUUIHXKUWHOWLWPXKUWHUUFPWQWOYDUSUXDUXEUUIUXCHWRUUFUWHPWRXBWSWTXAWMXCXDA
      YGXQYHYEYFUUBUUEWEXE $.
  $}

  ${
    fuco22nat.o $e |- ( ph -> ( <. C , D >. o.F E ) = <. O , P >. ) $.
    fuco22nat.a $e |- ( ph -> A e. ( F ( C Nat D ) M ) ) $.
    fuco22nat.b $e |- ( ph -> B e. ( K ( D Nat E ) R ) ) $.
    fuco22nat.u $e |- ( ph -> U = <. K , F >. ) $.
    fuco22nat.v $e |- ( ph -> V = <. R , M >. ) $.
    $( The composed natural transformation is a natural transformation.
       (Contributed by Zhi Wang, 2-Oct-2025.) $)
    fuco22nat $p |- ( ph -> ( B ( U P V ) A ) e.
            ( ( O ` U ) ( C Nat E ) ( O ` V ) ) ) $=
      ( cfv c1st c2nd cnat co eqid nat1st2nd cop cfunc wrel wcel relfunc natrcl
      wceq wa syl simpld 1st2nd sylancr opeq12d eqtrd simprd fuco22natlem ) ABC
      DEFGUATZGUBTZHIJUATZJUBTZKUATZKUBTZLUATZLUBTZMNOABDEJLDEUCUDZVKUEZPUFACEI
      KGEIUCUDZVMUEZQUFAHKJUGVGVHUGZVEVFUGZUGRAKVOJVPAEIUHUDZUIZKVQUJZKVOUMEIUK
      ZAVSGVQUJZACKGVMUDUJVSWAUNQCEIKGVMVNULUOZUPKVQUQURADEUHUDZUIZJWCUJZJVPUMD
      EUKZAWELWCUJZABJLVKUDUJWEWGUNPBDEJLVKVLULUOZUPJWCUQURUSUTANGLUGVCVDUGZVIV
      JUGZUGSAGWILWJAVRWAGWIUMVTAVSWAWBVAGVQUQURAWDWGLWJUMWFAWEWGWHVALWCUQURUSU
      TVB $.
  $}

  ${
    $d C a b x $.  $d D a b x $.  $d E a b x $.  $d J a b x $.  $d O a b x $.
    $d P a b x $.  $d T a b x $.  $d U a b x $.  $d V a b x $.  $d W a b x $.
    $d a b ph x $.
    fucof21.o $e |- ( ph -> ( <. C , D >. o.F E ) = <. O , P >. ) $.
    fucof21.t $e |- T = ( ( D FuncCat E ) Xc. ( C FuncCat D ) ) $.
    fucof21.j $e |- J = ( Hom ` T ) $.
    fucof21.w $e |- ( ph -> W = ( ( D Func E ) X. ( C Func D ) ) ) $.
    fucof21.u $e |- ( ph -> U e. W ) $.
    fucof21.v $e |- ( ph -> V e. W ) $.
    $( The morphism part of the functor composition bifunctor maps a hom-set of
       the product category into a set of natural transformations.
       (Contributed by Zhi Wang, 30-Sep-2025.) $)
    fucof21 $p |- ( ph -> ( U P V ) : ( U J V ) -->
            ( ( O ` U ) ( C Nat E ) ( O ` V ) ) ) $=
      ( c1st cfv co vb va vx c2nd cop cnat cbs cco cmpt cfunc relfunc fuco2eld3
      cv simprd simpld fuco2eld2 fuco21 wcel wa cfuco wceq adantr simprr simprl
      wbr fuco22 fuco22nat eqeltrrd cxp xpcfucbas eleqtrd xpcfuchom fveq2d opex
      op1st eqtrdi oveq12d op2nd xpeq12d eqtrd fmpodg ) AUAUBFRSZRSZWBUDSZUEZJR
      SZRSZWFUDSZUEZCGUFTZTZFUDSZRSZWLUDSZUEZJUDSZRSZWPUDSZUEZBCUFTZTZUCBUGSUCU
      MZWQSZUAUMZSXBUBUMZSXBWMSZXCWDTSXFWCSXCWCSUEXCWGSGUHSTTUIZFJHTZFISJISBGUF
      TTZFJDTZAUCBCDWGWHFGWMWNWCWDWQWRIJUBUALAWCWDCGUJTZVEZWMWNBCUJTZVEZAXMXKFK
      OPCGUKZBCUKZULZUNAXLXNXQUOAXMXKFKOPXOXPUPZAWGWHXKVEZWQWRXMVEZAXMXKJKOQXOX
      PULZUNAXSXTYAUOAXMXKJKOQXOXPUPZUQAXDWKURZXEXAURZUSZUSZXDXEXJTXGXIYFUCXEXD
      BCDWGWHFGWMWNWCWDWQWRIJABCUEGUTTIDUEVAYELVBZAFWEWOUEZVAYEXRVBZAJWIWSUEZVA
      YEYBVBZAYCYDVCZAYCYDVDZVFYFXEXDBCDWIFGWOWEWSIJYGYLYMYIYKVGVHAXHWBWFWJTZWL
      WPWTTZVIWKXAVIAXKXMVIZCGBECHFJMCGBECMVJNAFKYPPOVKAJKYPQOVKVLAYNWKYOXAAWBW
      EWFWIWJAWBYHRSWEAFYHRXRVMWEWOWCWDVNZWMWNVNZVOVPAWFYJRSWIAJYJRYBVMWIWSWGWH
      VNZWQWRVNZVOVPVQAWLWOWPWSWTAWLYHUDSWOAFYHUDXRVMWEWOYQYRVRVPAWPYJUDSWSAJYJ
      UDYBVMWIWSYSYTVRVPVQVSVTWA $.
  $}

  ${
    $d .1. w x $.  $d C w x $.  $d D w x $.  $d E w x $.  $d F w x $.
    $d G w x $.  $d I w x $.  $d K w x $.  $d L w x $.  $d O w x $.
    $d P w x $.  $d Q w x $.  $d T w x $.  $d U w x $.  $d ph w x $.
    fucoid.o $e |- ( ph -> ( <. C , D >. o.F E ) = <. O , P >. ) $.
    fucoid.t $e |- T = ( ( D FuncCat E ) Xc. ( C FuncCat D ) ) $.
    fucoid.1 $e |- .1. = ( Id ` T ) $.
    fucoid.q $e |- Q = ( C FuncCat E ) $.
    fucoid.i $e |- I = ( Id ` Q ) $.
    ${
      fucoid.f $e |- ( ph -> F ( C Func D ) G ) $.
      fucoid.k $e |- ( ph -> K ( D Func E ) L ) $.
      fucoid.u $e |- ( ph -> U = <. <. K , L >. , <. F , G >. >. ) $.
      $( Each identity morphism in the source category is mapped to the
         corresponding identity morphism in the target category.  See also
         ~ fucoid2 .  (Contributed by Zhi Wang, 30-Sep-2025.) $)
      fucoid $p |- ( ph -> ( ( U P U ) ` ( .1. ` U ) ) = ( I ` ( O ` U ) ) ) $=
        ( vx vw cbs cfv cv ccid ccom cop cco cmpt wfn ovex eqid fnmpti a1i ccat
        co wf wcel funcrcl3 cidfn syl funcf1 fcod fnfco syl2anc cvv wceq 2fveq3
        wa opeq12d oveq12d fveq2 fveq12d oveq123d simpr fvmptd3 chom ffvelcdmda
        ovexd adantr ffvelcdmd catidcl catlid fvco3d fveq2d cfunc eqtrd 3eqtr4d
        funcid eqfnfvd cfuc funcrcl2 fuccat fucbas df-br sylib xpcid c1st fucid
        wbr relfunc brrelex1i brrelex2i op1stg coeq2d 3eqtrd df-ov eqtr4di cnat
        fuchom eqeltrrd fuco22 fuco11id ) AUDBUFUGZUDUHZJUGZIUIUGZMUJZUGZXSCUIU
        GZJUJZUGZXTXTNUTZUGZXTMUGZYIUKZYIIULUGZUTZUTZUMZYAMJUJZUJZGHUGZGGDUTZUG
        ZGOUGLUGAUEXRYNYPYNXRUNAUDXRYMYNYCYHYLUOYNUPZUQURAYAIUFUGZUNZXRUUAYOVAZ
        YPXRUNAIUSVBZUUBACIMNUBVCZUUAIYAUUAUPZYAUPZVDVEAXRCUFUGZUUAMJAUUHUUACIM
        NUUHUPZUUFUBVFZAXRUUHBCJKXRUPUUIUAVFZVGZUUAXRYAYOVHVIAUEUHZXRVBZVMZUUMY
        NUGUUMJUGZYBUGZUUMYEUGZUUPUUPNUTZUGZUUPMUGZUVAUKZUVAYKUTZUTZUUMYPUGZUUO
        UDUUMYMUVDXRYNVJYTXSUUMVKZYCUUQYHUUTYLUVCUVFYJUVBYIUVAYKUVFYIUVAYIUVAXS
        UUMMJVLZUVGVNUVGVOXSUUMYBJVLUVFYFUURYGUUSUVFXTUUPXTUUPNXSUUMJVPZUVHVOXS
        UUMYEVPVQVRAUUNVSZUUOUUQUUTUVCWCVTUUOUVAYAUGZUVJUVCUTUVJUVDUVEUUOUUAIYK
        YAUVJIWAUGZUVAUVAUUFUVKUPZUUGAUUDUUNUUEWDZUUOUUHUUAUUPMAUUHUUAMVAUUNUUJ
        WDZAXRUUHUUMJUUKWBZWEZYKUPUVPUUOUUAIYAUVKUVAUUFUVLUUGUVMUVPWFWGUUOUUQUV
        JUUTUVJUVCUUOUUHUUAUUPYAMUVNUVOWHUUOUUTUUPYDUGZUUSUGUVJUUOUURUVQUUSUUOX
        RUUHUUMYDJAXRUUHJVAUUNUUKWDZUVIWHWIUUOUUHCYDIMNYAUUPUUIYDUPZUUGAMNCIWJU
        TZXDZUUNUBWDUVOWMWKVOUUOUVEUUMYOUGZYAUGUVJUUOXRUUAUUMYAYOAUUCUUNUULWDUV
        IWHUUOUWBUVAYAUUOXRUUHUUMMJUVRUVIWHWIWKWLWKWNAYSYBYEYRUTZYNAYSYBYEUKZYR
        UGUWCAYQUWDYRAYQMNUKZJKUKZUKZHUGUWECIWOUTZUIUGZUGZUWFBCWOUTZUIUGZUGZUKU
        WDAGUWGHUCWIAUWHUWKUWEUWFFHUWIUWLUVTBCWJUTZQACIUWHUWHUPZACIMNUBWPZUUEWQ
        ZABCUWKUWKUPZABCJKUAWPUWPWQZCIUWHUWOWRZBCUWKUWRWRZUWIUPZUWLUPZRAUWAUWEU
        VTVBUBMNUVTWSWTZAJKUWNXDZUWFUWNVBUAJKUWNWSWTZXAAUWJYBUWMYEAUWJYAUWEXBUG
        ZUJYBACIUWHYAUWEUWIUWOUXBUUGUXDXCAUXGMYAAMVJVBZNVJVBZUXGMVKAUWAUXHUBMNU
        VTCIXEZXFVEAUWAUXIUBMNUVTUXJXGVEMNVJVJXHVIXIWKZAUWMYDUWFXBUGZUJYEABCUWK
        YDUWFUWLUWRUXCUVSUXFXCAUXLJYDAJVJVBZKVJVBZUXLJVKAUXEUXMUAJKUWNBCXEZXFVE
        AUXEUXNUAJKUWNUXOXGVEJKVJVJXHVIXIWKZVNXJWIYBYEYRXKXLAUDYEYBBCDMNGIJKMNJ
        KOGPUCUCAUWMYEUWFUWFBCXMUTZUTUXPAUWNUWKUWLUXQUWFUXABCUWKUXQUWRUXQUPXNUX
        CUWSUXFWFXOAUWJYBUWEUWECIXMUTZUTUXKAUVTUWHUWIUXRUWEUWTCIUWHUXRUWOUXRUPX
        NUXBUWQUXDWFXOXPWKABCDEGYAIJKLMNOPUAUBUCSTUUGXQWL $.
    $}

    fucoid2.w $e |- ( ph -> W = ( ( D Func E ) X. ( C Func D ) ) ) $.
    fucoid2.u $e |- ( ph -> U e. W ) $.
    $( Each identity morphism in the source category is mapped to the
       corresponding identity morphism in the target category.  See also
       ~ fucoid .  (Contributed by Zhi Wang, 30-Sep-2025.) $)
    fucoid2 $p |- ( ph -> ( ( U P U ) ` ( .1. ` U ) ) = ( I ` ( O ` U ) ) ) $=
      ( cfv c2nd c1st cop co wcel wbr cxp relfunc fuco2eld2 3eltr3d opelxp2 syl
      cfunc df-br sylibr opelxp1 fucoid ) ABCDEFGHIGUATZUBTZURUATZJGUBTZUBTZVAU
      ATZKMNOPQAUSUTUCZBCUMUDZUEZUSUTVEUFAVBVCUCZVDUCZCIUMUDZVEUGZUEZVFAGLVHVJS
      AVEVIGLRSCIUHBCUHUIZRUJZVGVDVIVEUKULUSUTVEUNUOAVGVIUEZVBVCVIUFAVKVNVMVGVD
      VIVEUPULVBVCVIUNUOVLUQ $.
  $}

  ${
    $d A x $.  $d B x $.  $d C x $.  $d D x $.  $d E x $.  $d F x $.  $d K x $.
    $d M x $.  $d R x $.  $d U x $.  $d V x $.  $d ph x $.
    fuco22a.o $e |- ( ph -> ( <. C , D >. o.F E ) = <. O , P >. ) $.
    fuco22a.u $e |- ( ph -> U = <. K , F >. ) $.
    fuco22a.v $e |- ( ph -> V = <. R , M >. ) $.
    fuco22a.a $e |- ( ph -> A e. ( F ( C Nat D ) M ) ) $.
    fuco22a.b $e |- ( ph -> B e. ( K ( D Nat E ) R ) ) $.
    $( The morphism part of the functor composition bifunctor.  See also
       ~ fuco22 .  (Contributed by Zhi Wang, 1-Oct-2025.) $)
    fuco22a $p |- ( ph -> ( B ( U P V ) A ) = ( x e. ( Base ` C )
                               |-> ( ( B ` ( ( 1st ` M ) ` x ) )
                      ( <. ( ( 1st ` K ) ` ( ( 1st ` F ) ` x ) ) ,
                           ( ( 1st ` K ) ` ( ( 1st ` M ) ` x ) ) >.
              ( comp ` E ) ( ( 1st ` R ) ` ( ( 1st ` M ) ` x ) ) )
       ( ( ( ( 1st ` F ) ` x ) ( 2nd ` K ) ( ( 1st ` M ) ` x ) )
                                                   ` ( A ` x ) ) ) ) ) $=
      ( c1st cfv c2nd cop cvv cxp wcel wceq cfunc co wrel wss relfunc mpbi cnat
      df-rel wa eqid natrcl simpld sselid 1st2ndb sylib opeq12d eqtrd nat1st2nd
      syl simprd fuco22 ) ABCDEFGHUAUBZHUCUBZIJKUAUBZKUCUBZLUAUBZLUCUBZMUAUBZMU
      CUBZNOPAILKUDVNVOUDZVLVMUDZUDQALVRKVSALUEUEUFZUGLVRUHAFJUIUJZVTLWAUKWAVTU
      LFJUMWAUPUNZALWAUGZHWAUGZADLHFJUOUJZUJUGWCWDUQTDFJLHWEWEURZUSVGZUTVALVBVC
      AKVTUGKVSUHAEFUIUJZVTKWHUKWHVTULEFUMWHUPUNZAKWHUGZMWHUGZACKMEFUOUJZUJUGWJ
      WKUQSCEFKMWLWLURZUSVGZUTVAKVBVCVDVEAOHMUDVJVKUDZVPVQUDZUDRAHWOMWPAHVTUGHW
      OUHAWAVTHWBAWCWDWGVHVAHVBVCAMVTUGMWPUHAWHVTMWIAWJWKWNVHVAMVBVCVDVEACEFKMW
      LWMSVFADFJLHWEWFTVFVI $.
  $}

  ${
    fuco23a.a $e |- ( ph -> A e. ( <. F , G >. ( C Nat D ) <. M , N >. ) ) $.
    fuco23a.b $e |- ( ph -> B e. ( <. K , L >. ( D Nat E ) <. R , S >. ) ) $.
    fuco23a.x $e |- ( ph -> X e. ( Base ` C ) ) $.
    ${
      fuco23alem.o $e |- .x. = ( comp ` E ) $.
      $( The naturality property ( ~ nati ) in category ` E ` .  (Contributed
         by Zhi Wang, 3-Oct-2025.) $)
      fuco23alem $p |- ( ph ->
             ( ( B ` ( M ` X ) )
          ( <. ( K ` ( F ` X ) ) , ( K ` ( M ` X ) ) >. .x. ( R ` ( M ` X ) ) )
           ( ( ( F ` X ) L ( M ` X ) ) ` ( A ` X ) ) )
       = ( ( ( ( F ` X ) S ( M ` X ) ) ` ( A ` X ) )
          ( <. ( K ` ( F ` X ) ) , ( R ` ( F ` X ) ) >. .x. ( R ` ( M ` X ) ) )
               ( B ` ( F ` X ) ) ) ) $=
        ( cbs cfv chom cnat co eqid natrcl2 funcf1 ffvelcdmd natrcl3 natcl nati
        ) ACEUAUBZEIPBUBHLMEUCUBZFGEIUDUEZPJUBPNUBUOUFRUMUFZUNUFZTADUAUBZUMPJAU
        RUMDEJKURUFZUPABDEJKNODEUDUEZUTUFZQUGUHSUIAURUMPNAURUMDENOUSUPABDEJKNOU
        TVAQUJUHSUIABURDEJKUNNOUTPVAQUSUQSUKUL $.
    $}

    fuco23a.p $e |- ( ph -> ( <. C , D >. o.F E ) = <. O , P >. ) $.
    fuco23a.u $e |- ( ph -> U = <. <. K , L >. , <. F , G >. >. ) $.
    fuco23a.v $e |- ( ph -> V = <. <. R , S >. , <. M , N >. >. ) $.
    fuco23a.o $e |- ( ph -> .* = ( <. ( K ` ( F ` X ) ) , ( R ` ( F ` X ) ) >.
                ( comp ` E ) ( R ` ( M ` X ) ) ) ) $.
    $( The morphism part of the functor composition bifunctor.  An alternate
       definition of ` o.F ` .  See also ~ fuco23 .  (Contributed by Zhi Wang,
       3-Oct-2025.) $)
    fuco23a $p |- ( ph -> ( ( B ( U P V ) A ) ` X ) =
        ( ( ( ( F ` X ) S ( M ` X ) ) ` ( A ` X ) ) .* ( B ` ( F ` X ) ) ) ) $=
      ( cfv co cop cco eqid fuco23alem eqidd fuco23 oveqd 3eqtr4d ) ATPUHZCUHTB
      UHZTKUHZUROUIUHUTNUHZURNUHUJURGUHZJUKUHZUIZUIUSUTURHUIUHZUTCUHZVAUTGUHUJV
      BVCUIZUITCBISFUIUIUHVEVFMUIABCDEGHVCJKLNOPQTUAUBUCVCULUMABCDEFGHIJKLVDNOP
      QRSTUDUEUFUAUBUCAVDUNUOAMVGVEVFUGUPUQ $.
  $}

  ${
    $d .x. p $.  $d .xb p $.  $d .* p x $.  $d A p $.  $d B p $.  $d C p x $.
    $d D p x $.  $d E p x $.  $d F p x $.  $d G p x $.  $d K p x $.
    $d L p x $.  $d M p x $.  $d N p x $.  $d O p $.  $d P p $.  $d Q p $.
    $d R p x $.  $d S p x $.  $d T p $.  $d U p x $.  $d V p x $.  $d X p x $.
    $d Y p $.  $d Z p x $.  $d p ph x $.
    fucoco.r $e |- ( ph -> R e. ( F ( D Nat E ) K ) ) $.
    fucoco.s $e |- ( ph -> S e. ( G ( C Nat D ) L ) ) $.
    fucoco.u $e |- ( ph -> U e. ( K ( D Nat E ) M ) ) $.
    fucoco.v $e |- ( ph -> V e. ( L ( C Nat D ) N ) ) $.
    ${
      fucocolem1.x $e |- ( ph -> X e. ( Base ` C ) ) $.
      fucocolem1.p $e |- ( ph -> P e. ( D Func E ) ) $.
      fucocolem1.q $e |- ( ph -> Q e. ( C Func D ) ) $.
      fucocolem1.a $e |- ( ph -> A e. ( ( ( 1st ` P ) ` ( ( 1st ` Q ) ` X ) )
            ( Hom ` E ) ( ( 1st ` K ) ` ( ( 1st ` N ) ` X ) ) ) ) $.
      fucocolem1.b $e |- ( ph -> B e. ( ( ( 1st ` F ) ` ( ( 1st ` L ) ` X ) )
            ( Hom ` E ) ( ( 1st ` P ) ` ( ( 1st ` Q ) ` X ) ) ) ) $.
      $( Lemma for ~ fucoco .  Associativity for morphisms in category ` E ` .
         To simply put,
         ` ( ( a .x. b ) .x. ( c .x. d ) ) = ( a .x. ( ( b .x. c ) .x. d ) ) `
         for morphism compositions.  (Contributed by Zhi Wang, 2-Oct-2025.) $)
      fucocolem1 $p |- ( ph -> ( (
                         ( U ` ( ( 1st ` N ) ` X ) )
                          ( <. ( ( 1st ` P ) ` ( ( 1st ` Q ) ` X ) )
                             , ( ( 1st ` K ) ` ( ( 1st ` N ) ` X ) ) >.
                  ( comp ` E ) ( ( 1st ` M ) ` ( ( 1st ` N ) ` X ) ) )
                           A )
                          ( <. ( ( 1st ` F ) ` ( ( 1st ` G ) ` X ) )
                             , ( ( 1st ` P ) ` ( ( 1st ` Q ) ` X ) ) >.
                  ( comp ` E ) ( ( 1st ` M ) ` ( ( 1st ` N ) ` X ) ) )
                         ( B
                          ( <. ( ( 1st ` F ) ` ( ( 1st ` G ) ` X ) )
                             , ( ( 1st ` F ) ` ( ( 1st ` L ) ` X ) ) >.
                  ( comp ` E ) ( ( 1st ` P ) ` ( ( 1st ` Q ) ` X ) ) )
           ( ( ( ( 1st ` G ) ` X ) ( 2nd ` F ) ( ( 1st ` L ) ` X ) )
                                                       ` ( S ` X ) ) ) )
                     = ( ( U ` ( ( 1st ` N ) ` X ) )
                          ( <. ( ( 1st ` F ) ` ( ( 1st ` G ) ` X ) )
                             , ( ( 1st ` K ) ` ( ( 1st ` N ) ` X ) ) >.
                  ( comp ` E ) ( ( 1st ` M ) ` ( ( 1st ` N ) ` X ) ) )
                       ( ( A
                          ( <. ( ( 1st ` F ) ` ( ( 1st ` L ) ` X ) )
                             , ( ( 1st ` P ) ` ( ( 1st ` Q ) ` X ) ) >.
                  ( comp ` E ) ( ( 1st ` K ) ` ( ( 1st ` N ) ` X ) ) )
                           B )
                          ( <. ( ( 1st ` F ) ` ( ( 1st ` G ) ` X ) )
                             , ( ( 1st ` F ) ` ( ( 1st ` L ) ` X ) ) >.
                  ( comp ` E ) ( ( 1st ` K ) ` ( ( 1st ` N ) ` X ) ) )
           ( ( ( ( 1st ` G ) ` X ) ( 2nd ` F ) ( ( 1st ` L ) ` X ) )
                                                       ` ( S ` X ) ) ) ) ) $=
        ( c1st cfv cop cco c2nd cbs chom eqid cfunc wcel cnat natrcl syl simpld
        co func1st2nd funcrcl3 funcf1 ffvelcdmd simprd funcf2 nat1st2nd catcocl
        wa natcl catass oveq2d eqtr4d ) ASQUIUJZUJZJUJZBSGUIUJZUJZFUIUJZUJZVRNU
        IUJZUJZUKVRPUIUJZUJZKULUJZVCVCCSIUJZSMUIUJZUJZSOUIUJZUJZLUMUJZVCZUJZWKL
        UIUJZUJZWMWQUJZUKZWCWHVCVCZWRWCUKZWGWHVCVCVSBXAXBWEWHVCVCZWRWEUKWGWHVCZ
        VCVSBCWSWCUKWEWHVCVCWPWTWEWHVCVCZXDVCAKUNUJZKWHXABKUOUJZVSWGWRWCWEXFUPZ
        XGUPZWHUPZAEKWQWNAEKLALEKUQVCZURZNXKURZAHLNEKUSVCZVCURXLXMVLTHEKLNXNXNU
        PZUTVAZVBVDZVEZAEUNUJZXFWKWQAXSXFEKWQWNXSUPZXHXQVFZADUNUJZXSSWJAYBXSDEW
        JMUMUJZYBUPZXTADEMAMDEUQVCZURZOYEURZAIMODEUSVCZVCURYFYGVLUAIDEMOYHYHUPZ
        UTVAZVBVDVFUDVGZVGZAXSXFWAWBAXSXFEKWBFUMUJXTXHAEKFUEVDVFAYBXSSVTAYBXSDE
        VTGUMUJYDXTADEGUFVDVFUDVGVGZAXSXFVRWDAXSXFEKWDNUMUJZXTXHAEKNAXLXMXPVHVD
        VFAYBXSSVQAYBXSDEVQQUMUJYDXTADEQAYGQYEURZAROQYHVCURYGYOVLUCRDEOQYHYIUTV
        AVHVDVFUDVGZVGZAXFKWHWPCXGWRWSWCXHXIXJXRYLAXSXFWMWQYAAYBXSSWLAYBXSDEWLO
        UMUJZYDXTADEOAYFYGYJVHVDVFUDVGZVGZYMAWKWMEUOUJZVCWRWSXGVCWIWOAXSEKWQWNU
        UAXGWKWMXTUUAUPZXIXQYKYSVIAIYBDEWJYCUUAWLYRYHSYIAIDEMOYHYIUAVJYDUUBUDVM
        VGZUHVKUGAXSXFVRWFAXSXFEKWFPUMUJZXTXHAEKPAXMPXKURZAJNPXNVCURXMUUEVLUBJE
        KNPXNXOUTVAVHVDVFYPVGAJXSEKWDYNXGWFUUDXNVRXOAJEKNPXNXOUBVJXTXIYPVMVNAXE
        XCVSXDAXFKWHWPCXGBWEWRWSWCXHXIXJXRYLYTYMUUCUHYQUGVNVOVP $.
    $}

    fucoco.o $e |- ( ph -> ( <. C , D >. o.F E ) = <. O , P >. ) $.
    fucoco.x $e |- ( ph -> X = <. F , G >. ) $.
    fucoco.y $e |- ( ph -> Y = <. K , L >. ) $.
    fucoco.z $e |- ( ph -> Z = <. M , N >. ) $.
    fucoco.a $e |- ( ph -> A = <. R , S >. ) $.
    fucoco.b $e |- ( ph -> B = <. U , V >. ) $.
    ${
      fucocolem2.t $e |- T = ( ( D FuncCat E ) Xc. ( C FuncCat D ) ) $.
      fucocolem2.ot $e |- .x. = ( comp ` T ) $.
      fucocolem2.od $e |- .* = ( comp ` D ) $.
      $( Lemma for ~ fucoco .  The composed natural transformations are mapped
         to composition of 4 natural transformations.  (Contributed by Zhi
         Wang, 2-Oct-2025.) $)
      fucocolem2 $p  |- ( ph -> ( ( X P Z ) ` ( B ( <. X , Y >. .x. Z ) A ) )
            = ( x e. ( Base ` C ) |-> ( ( ( U ` ( ( 1st ` N ) ` x ) )
                           ( <. ( ( 1st ` F ) ` ( ( 1st ` N ) ` x ) ) ,
                                ( ( 1st ` K ) ` ( ( 1st ` N ) ` x ) ) >.
                   ( comp ` E ) ( ( 1st ` M ) ` ( ( 1st ` N ) ` x ) ) )
                          ( R ` ( ( 1st ` N ) ` x ) ) )
                           ( <. ( ( 1st ` F ) ` ( ( 1st ` G ) ` x ) ) ,
                                ( ( 1st ` F ) ` ( ( 1st ` N ) ` x ) ) >.
                   ( comp ` E ) ( ( 1st ` M ) ` ( ( 1st ` N ) ` x ) ) )
            ( ( ( ( 1st ` G ) ` x ) ( 2nd ` F ) ( ( 1st ` N ) ` x ) )
                                ` ( ( V ` x )
                     ( <. ( ( 1st ` G ) ` x ) , ( ( 1st ` L ) ` x ) >.
                       .* ( ( 1st ` N ) ` x ) )
                                    ( S ` x ) ) ) ) ) ) $=
        ( vp cop co cfv cbs cv c1st cco cmpt c2nd opeq12d oveq12d oveq123d eqid
        xpcfucco3 eqtrd df-ov eqtr4di cnat cxp wcel xpcfuccocl eqeltrrd opelxp2
        fveq2d syl opelxp1 fuco22a wa cfunc natrcl simprd func1st2nd ffvelcdmda
        wceq funcf1 fveq2 ovex fvmpt3i adantl mpteq2dva 3eqtrd ) ADCUCUDUTZUEKV
        AZVAZUCUEGVAZVBZUSFVCVBZUSVDZLVBZXGHVBZXGNVEVBZVBZXGQVEVBZVBZUTZXGSVEVB
        ZVBZMVFVBZVAZVAZVGZUSEVCVBZXGUBVBZXGIVBZXGOVEVBZVBZXGRVEVBZVBZUTZXGTVEV
        BZVBZPVAZVAZVGZXDVAZBYABVDZYIVBZXTVBZYOYMVBZYOYDVBZYPNVHVBVAZVBZYSXJVBY
        PXJVBZUTYPXOVBZXQVAZVAZVGBYAYPLVBZYPHVBZUUBYPXLVBZUTZUUCXQVAZVAZYOUBVBZ
        YOIVBZYSYOYFVBZUTZYPPVAZVAZYTVBZUUDVAZVGAXEXTYMUTZXDVBYNAXCUUTXDAXCLUBU
        TZHIUTZNOUTZQRUTZUTZSTUTZKVAZVAZUUTADUVACUVBXBUVGAXAUVEUEUVFKAUCUVCUDUV
        DUKULVIUMVJUOUNVKAUSUSFMEQRSTPJXQFHILUBNOKXFYAUPUQUFUGUHUIXFVLZYAVLZXQV
        LURVMZVNWCXTYMXDVOVPABYMXTEFGSUCMONTUAUEUJUKUMAUUTNSFMVQVAVAZOTEFVQVAZV
        AZVRZVSZYMUVNVSAUVHUUTUVOUVKAFMEQRSTJFHILUBNOKUPUQUFUGUHUIVTWAZXTYMUVLU
        VNWBWDAUVPXTUVLVSUVQXTYMUVLUVNWEWDWFABYAUUEUUSAYOYAVSZWGZYQUUKUUAUURUUD
        UVSYPXFVSYQUUKWMAYAXFYOYIAYAXFEFYITVHVBUVJUVIAEFTAREFWHVAZVSZTUVTVSZAUB
        RTUVMVAVSUWAUWBWGUIUBEFRTUVMUVMVLWIWDWJWKWNWLUSYPXSUUKXFXTXGYPWMZXHUUFX
        IUUGXRUUJUWCXNUUIXPUUCXQUWCXKUUBXMUUHXGYPXJWOXGYPXLWOVIXGYPXOWOVJXGYPLW
        OXGYPHWOVKXTVLXHXIXRWPWQWDUVRUUAUURWMAUVRYRUUQYTUSYOYLUUQYAYMXGYOWMZYBU
        ULYCUUMYKUUPUWDYHUUOYJYPPUWDYEYSYGUUNXGYOYDWOXGYOYFWOVIXGYOYIWOVJXGYOUB
        WOXGYOIWOVKYMVLYBYCYKWPWQWCWRVJWSWT $.

      $( Lemma for ~ fucoco .  The composed natural transformations are mapped
         to composition of 4 natural transformations.  (Contributed by Zhi
         Wang, 3-Oct-2025.) $)
      fucocolem3 $p |- ( ph -> ( ( X P Z ) ` ( B ( <. X , Y >. .x. Z ) A ) )
            = ( x e. ( Base ` C ) |-> (
              ( U ` ( ( 1st ` N ) ` x ) )
               ( <. ( ( 1st ` F ) ` ( ( 1st ` G ) ` x ) )
                  , ( ( 1st ` K ) ` ( ( 1st ` N ) ` x ) ) >.
       ( comp ` E ) ( ( 1st ` M ) ` ( ( 1st ` N ) ` x ) ) ) ( (
              ( R ` ( ( 1st ` N ) ` x ) )
               ( <. ( ( 1st ` F ) ` ( ( 1st ` L ) ` x ) )
                  , ( ( 1st ` F ) ` ( ( 1st ` N ) ` x ) ) >.
       ( comp ` E ) ( ( 1st ` K ) ` ( ( 1st ` N ) ` x ) ) )
        ( ( ( ( 1st ` L ) ` x ) ( 2nd ` F ) ( ( 1st ` N ) ` x ) ) ` ( V ` x ) )
             ) ( <. ( ( 1st ` F ) ` ( ( 1st ` G ) ` x ) )
                  , ( ( 1st ` F ) ` ( ( 1st ` L ) ` x ) ) >.
       ( comp ` E ) ( ( 1st ` K ) ` ( ( 1st ` N ) ` x ) ) )
        ( ( ( ( 1st ` G ) ` x ) ( 2nd ` F ) ( ( 1st ` L ) ` x ) ) ` ( S ` x ) )
          ) ) ) ) $=
        ( cop co cfv cbs cv c1st cco c2nd cmpt fucocolem2 wcel wa chom eqid wbr
        cfunc cnat natrcl syl simpld func1st2nd adantr funcf1 ffvelcdmda simprd
        nat1st2nd simpr natcl funcco oveq2d funcf2 ffvelcdmd fucocolem1 eqtrd
        mpteq2dva ) ADCUCUDUSUEKUTUTUCUEGUTVABEVBVAZBVCZTVDVAZVAZLVAZWQHVAZWQNV
        DVAZVAZWQQVDVAZVAZUSWQSVDVAVAZMVEVAZUTUTZWOUBVAZWOIVAZWOOVDVAZVAZWORVDV
        AZVAZUSWQPUTUTXJWQNVFVAZUTVAZXJWTVAZXAUSXDXEUTZUTZVGBWNWRWSXGXLWQXMUTZV
        AZXLWTVAZXAUSXCXEUTUTXHXJXLXMUTVAZXOXTUSZXCXEUTUTXOXCUSXDXEUTUTZVGABCDE
        FGHIJKLMNOPQRSTUAUBUCUDUEUFUGUHUIUJUKULUMUNUOUPUQURVHABWNXQYCAWOWNVIZVJ
        ZXQXFXSYAYBXAXEUTUTZXPUTYCYEXNYFXFXPYEFVBVAZFPMWTXMFVKVAZXHXGXEXJXLWQYG
        VLZYHVLZURXEVLAWTXMFMVNUTZVMYDAFMNANYKVIZQYKVIZAHNQFMVOUTZUTVIZYLYMVJUF
        HFMNQYNYNVLZVPVQVRZVSVTZAWNYGWOXIAWNYGEFXIOVFVAZWNVLZYIAEFOAOEFVNUTZVIZ
        RUUAVIZAIOREFVOUTZUTVIZUUBUUCVJUGIEFORUUDUUDVLZVPVQZVRVSWAWBAWNYGWOXKAW
        NYGEFXKRVFVAZYTYIAEFRAUUBUUCUUGWCVSWAWBZAWNYGWOWPAWNYGEFWPTVFVAZYTYIAEF
        TAUUCTUUAVIZAUBRTUUDUTVIZUUCUUKVJUIUBEFRTUUDUUFVPVQWCZVSWAWBZYEIWNEFXIY
        SYHXKUUHUUDWOUUFAIXIYSUSXKUUHUSZUUDUTVIYDAIEFORUUDUUFUGWDVTYTYJAYDWEZWF
        YEUBWNEFXKUUHYHWPUUJUUDWOUUFAUBUUOWPUUJUSUUDUTVIYDAUBEFRTUUDUUFUIWDVTYT
        YJUUPWFZWGWHYEWSXSEFNTHILMNOQRSTUBWOAYOYDUFVTAUUEYDUGVTALQSYNUTVIYDUHVT
        AUULYDUIVTUUPAYLYDYQVTAUUKYDUUMVTYEHYGFMWTXMMVKVAZXBQVFVAZYNWQYPAHWTXMU
        SXBUUSUSYNUTVIYDAHFMNQYNYPUFWDVTYIUURVLZUUNWFYEXLWQYHUTXTXAUURUTXGXRYEY
        GFMWTXMYHUURXLWQYIYJUUTYRUUIUUNWIUUQWJWKWLWMWL $.
    $}

    $d A x $.  $d B x $.  $d O x $.  $d P x $.  $d Y x $.
    fucoco.q $e |- Q = ( C FuncCat E ) $.
    fucoco.oq $e |- .xb = ( comp ` Q ) $.
    $( Lemma for ~ fucoco .  The composed natural transformations are mapped to
       composition of 4 natural transformations.  (Contributed by Zhi Wang,
       2-Oct-2025.) $)
    fucocolem4 $p |- ( ph -> ( ( ( Y P Z ) ` B )
        ( <. ( O ` X ) , ( O ` Y ) >. .xb ( O ` Z ) ) ( ( X P Y ) ` A ) )
                  = ( x e. ( Base ` C ) |-> ( (
               ( U ` ( ( 1st ` N ) ` x ) )
                ( <. ( ( 1st ` K ) ` ( ( 1st ` L ) ` x ) ) ,
                     ( ( 1st ` K ) ` ( ( 1st ` N ) ` x ) ) >.
        ( comp ` E ) ( ( 1st ` M ) ` ( ( 1st ` N ) ` x ) ) )
        ( ( ( ( 1st ` L ) ` x ) ( 2nd ` K ) ( ( 1st ` N ) ` x ) ) ` ( V ` x ) )
              ) ( <. ( ( 1st ` F ) ` ( ( 1st ` G ) ` x ) ) ,
                     ( ( 1st ` K ) ` ( ( 1st ` L ) ` x ) ) >.
        ( comp ` E ) ( ( 1st ` M ) ` ( ( 1st ` N ) ` x ) ) ) (
               ( R ` ( ( 1st ` L ) ` x ) )
                ( <. ( ( 1st ` F ) ` ( ( 1st ` G ) ` x ) ) ,
                     ( ( 1st ` F ) ` ( ( 1st ` L ) ` x ) ) >.
        ( comp ` E ) ( ( 1st ` K ) ` ( ( 1st ` L ) ` x ) ) )
        ( ( ( ( 1st ` G ) ` x ) ( 2nd ` F ) ( ( 1st ` L ) ` x ) ) ` ( S ` x ) )
                 ) ) ) ) $=
      ( co cfv cop cbs cv c1st cco cmpt c2nd cnat eqid fveq2d eqtr4di fuco22nat
      df-ov eqeltrd fucco wcel wa ccom wceq cfunc natrcl simpld func1st2nd wrel
      syl relfunc 1st2nd sylancr opeq12d fuco111 fveq1d adantr wf funcf1 fvco3d
      eqtrd simpr simprd oveq12d cvv fuco22a ovexd fvmpt2d oveq123d mpteq2dva )
      ADUCUDGUQZURZCUBUCGUQZURZUBTURZUCTURZUSUDTURZKUQUQBEUTURZBVAZXEURZXLXGURZ
      XLXHVBURZURZXLXIVBURZURZUSZXLXJVBURZURZMVCURZUQZUQZVDBXKXLSVBURZURZLURZXL
      UAURXLQVBURZURZYFPVEURZUQURZYIPVBURZURZYFYLURUSYFRVBURZURZYBUQZUQZYIIURZX
      LJURXLOVBURZURZYINVEURZUQURZYTNVBURZURZYIUUCURUSYMYBUQZUQZUUDYMUSZYOYBUQZ
      UQZVDABXKEMHXGXEKYBXHXIXJEMVFUQZUOUUJVGXKVGZYBVGUPAXGIJXFUQZXHXIUUJUQAXGI
      JUSZXFURUULACUUMXFUMVHIJXFVKVIZAJIEFGPUBMONQTUCUIUFUEUJUKVJVLAXELUAXDUQZX
      IXJUUJUQAXELUAUSZXDURUUOADUUPXDUNVHLUAXDVKVIZAUALEFGRUCMQPSTUDUIUHUGUKULV
      JVLVMABXKYDUUIAXLXKVNZVOZXMYQXNUUFYCUUHUUSXSUUGYAYOYBUUSXPUUDXRYMUUSXPXLU
      UCYSVPZURZUUDAXPUVAVQUURAXLXOUUTAEFGUBMYSOVEURZUUCUUATUIAEFOAOEFVRUQZVNZQ
      UVCVNZAJOQEFVFUQZUQVNUVDUVEVOUFJEFOQUVFUVFVGZVSWCZVTZWAZAFMNANFMVRUQZVNZP
      UVKVNZAINPFMVFUQZUQVNUVLUVMVOUEIFMNPUVNUVNVGZVSWCZVTZWAAUBNOUSUUCUUAUSZYS
      UVBUSZUSUJANUVROUVSAUVKWBZUVLNUVRVQFMWDZUVQNUVKWEWFAUVCWBZUVDOUVSVQEFWDZU
      VIOUVCWEWFWGWNWHWIWJUUSXKFUTURZXLUUCYSAXKUWDYSWKUURAXKUWDEFYSUVBUUKUWDVGZ
      UVJWLWJAUURWOZWMWNUUSXRXLYLYHVPZURZYMAXRUWHVQUURAXLXQUWGAEFGUCMYHQVEURZYL
      YJTUIAEFQAUVDUVEUVHWPZWAZAFMPAUVLUVMUVPWPZWAAUCPQUSYLYJUSZYHUWIUSZUSUKAPU
      WMQUWNAUVTUVMPUWMVQUWAUWLPUVKWEWFAUWBUVEQUWNVQUWCUWJQUVCWEWFWGWNWHWIWJUUS
      XKUWDXLYLYHAXKUWDYHWKUURAXKUWDEFYHUWIUUKUWEUWKWLWJUWFWMWNWGUUSYAXLYNYEVPZ
      URZYOAYAUWPVQUURAXLXTUWOAEFGUDMYESVEURZYNRVEURZTUIAEFSAUVESUVCVNZAUAQSUVF
      UQVNUVEUWSVOUHUAEFQSUVFUVGVSWCWPZWAZAFMRAUVMRUVKVNZALPRUVNUQVNUVMUXBVOUGL
      FMPRUVNUVOVSWCWPZWAAUDRSUSYNUWRUSZYEUWQUSZUSULARUXDSUXEAUVTUXBRUXDVQUWAUX
      CRUVKWEWFAUWBUWSSUXEVQUWCUWTSUVCWEWFWGWNWHWIWJUUSXKUWDXLYNYEAXKUWDYEWKUUR
      AXKUWDEFYEUWQUUKUWEUXAWLWJUWFWMWNWQABXKYQXEWRAXEUUOBXKYQVDUUQABUALEFGRUCM
      QPSTUDUIUKULUHUGWSWNUUSYGYKYPWTXAABXKUUFXGWRAXGUULBXKUUFVDUUNABJIEFGPUBMO
      NQTUCUIUJUKUFUEWSWNUUSYRUUBUUEWTXAXBXCWN $.

    fucoco.t $e |- T = ( ( D FuncCat E ) Xc. ( C FuncCat D ) ) $.
    fucoco.ot $e |- .x. = ( comp ` T ) $.
    $( Composition in the source category is mapped to composition in the
       target.  See also ~ fucoco2 .  (Contributed by Zhi Wang, 3-Oct-2025.) $)
    fucoco $p |- ( ph -> ( ( X P Z ) ` ( B ( <. X , Y >. .x. Z ) A ) )
                         = ( ( ( Y P Z ) ` B )
                             ( <. ( O ` X ) , ( O ` Y ) >. .xb ( O ` Z ) )
                             ( ( X P Y ) ` A ) ) ) $=
      ( vp cbs cfv cv c1st c2nd co cop cco cmpt wcel cnat eqid nat1st2nd adantr
      wa simpr fuco23alem oveq1d oveq2d cfunc natrcl syl simprd chom func1st2nd
      wbr funcf1 ffvelcdmda funcf2 natcl ffvelcdmd fucocolem1 eqtr4d fucocolem3
      mpteq2dva fucocolem4 3eqtr4d ) AUTDVAVBZUTVCZTVDVBZVBZMVBZXAHVBWSUBVBZWSR
      VDVBZVBZXAOVEVBZVFVBXEOVDVBZVBZXAXGVBVGXAQVDVBZVBZNVHVBZVFVFZWSIVBWSPVDVB
      VBZXEXFVFVBZXMXGVBZXHVGZXJXKVFZVFZXOXJVGXASVDVBVBZXKVFZVFZVIUTWRXBXCXEXAQ
      VEVBZVFZVBZXEXIVBZXJVGXSXKVFVFXEHVBZXNXPYEXKVFVFXOYEVGXSXKVFVFZVICBUCUDVG
      UELVFVFUCUEFVFVBCUDUEFVFVBBUCUDFVFVBUCUAVBUDUAVBVGUEUAVBJVFVFAUTWRYAYGAWS
      WRVJZVOZYAXBYDYFXHYEVGXJXKVFVFZXNXQVFZXTVFYGYIXRYKXBXTYIXLYJXNXQYIUBHDEXI
      YBXKNXDRVEVBZXGXFWTTVEVBZWSAUBXDYLVGWTYMVGDEVKVFZVFVJYHAUBDERTYNYNVLZUIVM
      VNZAHXGXFVGXIYBVGENVKVFZVFVJYHAHENOQYQYQVLZUFVMVNZAYHVPZXKVLVQVRVSYIYDYFD
      EQRHIMNOPQRSTUBWSAHOQYQVFVJZYHUFVNAIPRYNVFVJZYHUGVNAMQSYQVFVJYHUHVNAUBRTY
      NVFVJZYHUIVNYTAQENVTVFZVJZYHAOUUDVJZUUEAUUAUUFUUEVOUFHENOQYQYRWAWBWCZVNAR
      DEVTVFZVJZYHAPUUHVJZUUIAUUBUUJUUIVOUGIDEPRYNYOWAWBWCZVNYIXEXAEWDVBZVFYEXJ
      NWDVBZVFXCYCYIEVAVBZENXIYBUULUUMXEXAUUNVLZUULVLZUUMVLZAXIYBUUDWFYHAENQUUG
      WEVNAWRUUNWSXDAWRUUNDEXDYLWRVLZUUOADERUUKWEWGWHZAWRUUNWSWTAWRUUNDEWTYMUUR
      UUOADETAUUITUUHVJZAUUCUUIUUTVOUIUBDERTYNYOWAWBWCWEWGWHWIYIUBWRDEXDYLUULWT
      YMYNWSYOYPUURUUPYTWJWKYIHUUNENXGXFUUMXIYBYQXEYRYSUUOUUQUUSWJWLWMWOAUTBCDE
      FHIKLMNOPEVHVBZQRSTUAUBUCUDUEUFUGUHUIUJUKULUMUNUOURUSUVAVLWNAUTBCDEFGHIJM
      NOPQRSTUAUBUCUDUEUFUGUHUIUJUKULUMUNUOUPUQWPWQ $.
  $}

  ${
    fucoco2.t $e |- T = ( ( D FuncCat E ) Xc. ( C FuncCat D ) ) $.
    fucoco2.q $e |- Q = ( C FuncCat E ) $.
    fucoco2.o $e |- ( ph -> ( <. C , D >. o.F E ) = <. O , P >. ) $.
    ${
      fucoco2.1 $e |- .x. = ( comp ` T ) $.
      fucoco2.2 $e |- .xb = ( comp ` Q ) $.
      fucoco2.w $e |- ( ph -> W = ( ( D Func E ) X. ( C Func D ) ) ) $.
      fucoco2.x $e |- ( ph -> X e. W ) $.
      fucoco2.y $e |- ( ph -> Y e. W ) $.
      fucoco2.z $e |- ( ph -> Z e. W ) $.
      fucoco2.j $e |- J = ( Hom ` T ) $.
      fucoco2.a $e |- ( ph -> A e. ( X J Y ) ) $.
      fucoco2.b $e |- ( ph -> B e. ( Y J Z ) ) $.
      $( Composition in the source category is mapped to composition in the
         target.  See also ~ fucoco .  (Contributed by Zhi Wang,
         3-Oct-2025.) $)
      fucoco2 $p |- ( ph -> ( ( X P Z ) ` ( B ( <. X , Y >. .x. Z ) A ) )
                         = ( ( ( Y P Z ) ` B )
                             ( <. ( O ` X ) , ( O ` Y ) >. .xb ( O ` Z ) )
                             ( ( X P Y ) ` A ) ) ) $=
        ( c1st cfv c2nd cnat co cxp cfunc xpcfucbas eleqtrd xpcfuchom xp1st syl
        wcel xp2nd cop wceq 1st2nd2 fucoco ) ABCDEFGBUJUKZBULUKZHIJCUJUKZKOUJUK
        ZOULUKZPUJUKZPULUKZQUJUKZQULUKZMCULUKZOPQABVKVMEKUMUNZUNZVLVNDEUMUNZUNZ
        UOZVBZVHVSVBABOPLUNWBUHAEKUPUNZDEUPUNZUOZEKDIELOPREKDIERUQZUGAONWFUDUCU
        RZAPNWFUEUCURZUSURZBVSWAUTVAAWCVIWAVBWJBVSWAVCVAACVMVOVRUNZVNVPVTUNZUOZ
        VBZVJWKVBACPQLUNWMUIAWFEKDIELPQRWGUGWIAQNWFUFUCURZUSURZCWKWLUTVAAWNVQWL
        VBWPCWKWLVCVATAOWFVBOVKVLVDVEWHOWDWEVFVAAPWFVBPVMVNVDVEWIPWDWEVFVAAQWFV
        BQVOVPVDVEWOQWDWEVFVAAWCBVHVIVDVEWJBVSWAVFVAAWNCVJVQVDVEWPCWKWLVFVASUBR
        UAVG $.
    $}

    $d C m n x y z $.  $d D m n x y z $.  $d E m n x y z $.  $d O m n x y z $.
    $d P m n x y z $.  $d Q m n x y z $.  $d T m n x y z $.  $d m n ph x y z $.
    fucofunc.c $e |- ( ph -> C e. Cat ) $.
    fucofunc.d $e |- ( ph -> D e. Cat ) $.
    fucofunc.e $e |- ( ph -> E e. Cat ) $.
    $( The functor composition bifunctor is a functor.  See also ~ fucofunca .

       However, it is unlikely the unique functor compatible with the functor
       composition.  As a counterexample, let ` C ` and ` D ` be terminal
       categories (categories of one object and one morphism, ~ df-termc ), for
       example, ` ( SetCat `` 1o ) ` (the trivial category, ~ setc1oterm ), and
       ` E ` be a category with two objects equipped with only two non-identity
       morphisms ` f ` and ` g ` , pointing in the same direction.  It is
       possible to map the ordered pair of natural transformations
       ` <. a , i >. ` , where ` a ` sends to ` f ` and ` i ` is the identity
       natural transformation, to the other natural transformation ` b `
       sending to ` g ` , i.e., define the morphism part ` P ` such that
       ` ( a ( U P V ) i ) = b ` such that ` ( b `` X ) = g ` given hypotheses
       of ~ fuco23 .  Such construction should be provable as a functor.

       Given any ` P ` , it is a morphism part of a functor compatible with the
       object part, i.e., the functor composition, i.e., the restriction of
       ` o.func ` , iff both of the following hold.

       1.  It has the same form as ~ df-fuco up to ~ fuco23 , but
       ` ( ( B ( U P V ) A ) `` X ) ` might be mapped to a different morphism
       in category ` E ` .  See ~ fucofulem2 for some insights.

       2. ~ fuco22nat , ~ fucoid , and ~ fucoco are satisfied.

       (Contributed by Zhi Wang, 3-Oct-2025.) $)
    fucofunc $p |- ( ph -> O ( T Func Q ) P ) $=
      ( co cfv eqid ccat cv wcel vx vy vz vm cfunc cxp ccid chom cnat xpcfucbas
      vn cco fucbas fuchom cfuc fuccat xpccat eqidd fucof1 fucofn2 wa cop cfuco
      wceq adantr simprl simprr fucof21 simpr w3a 3ad2ant1 simp21 simp22 simp23
      fucoid2 simp3l simp3r fucoco2 isfuncd ) AUAUBUCCGUEOBCUEOUFZBGUEOFFULPZFU
      GPZUDUKEHDFUHPZEUGPZBGUIOZEULPZCGBFCIUJBGEJUMWCQZBGEWEJWEQUNWBQZWDQZWAQZW
      FQZACGUOOZBCUOOZFIACGWLWLQMNUPABCWMWMQLMUPUQABGEJLNUPABCDRRGHRVTLMNKAVTUR
      ZUSABCDRRGHRVTLMNKWNUTAUASZVTTZUBSZVTTZVAZVAZBCDFWOGWCHWQVTABCVBGVCOHDVBV
      DZWSKVEIWGWTVTURAWPWRVFAWPWRVGVHAWPVAZBCDEFWOWBGWDHVTAXAWPKVEIWHJWIXBVTUR
      AWPVIVOAWPWRUCSZVTTZVJZUDSZWOWQWCOTZUKSZWQXCWCOTZVAZVJZXFXHBCDEWFFWAGWCHV
      TWOWQXCIJAXEXAXJKVKWJWKXKVTURAWPWRXDXJVLAWPWRXDXJVMAWPWRXDXJVNWGAXEXGXIVP
      AXEXGXIVQVRVS $.
  $}

  ${
    fucofunca.t $e |- T = ( ( D FuncCat E ) Xc. ( C FuncCat D ) ) $.
    fucofunca.q $e |- Q = ( C FuncCat E ) $.
    fucofunca.c $e |- ( ph -> C e. Cat ) $.
    fucofunca.d $e |- ( ph -> D e. Cat ) $.
    fucofunca.e $e |- ( ph -> E e. Cat ) $.
    $( The functor composition bifunctor is a functor.  See also ~ fucofunc .
       (Contributed by Zhi Wang, 10-Oct-2025.) $)
    fucofunca $p |- ( ph -> ( <. C , D >. o.F E ) e. ( T Func Q ) ) $=
      ( cop cfuco co c1st cfv c2nd cvv wcel ccat cfunc cxp fucoelvv 1st2nd2 syl
      wceq eqidd wbr fucofunc df-br sylib eqeltrd ) ABCLFMNZUMOPZUMQPZLZEDUANZA
      UMRRUBSUMUPUFABCTTFTUMIJKAUMUGUCUMRRUDUEZAUNUOUQUHUPUQSABCUODEFUNGHURIJKU
      IUNUOUQUJUKUL $.
  $}

  ${
    $d A x $.  $d C x $.  $d D x $.  $d E x $.  $d F x $.  $d G x $.  $d H x $.
    $d ph x $.
    fucolid.p $e |- ( ph -> ( 2nd ` ( <. C , D >. o.F E ) ) = P ) $.
    fucolid.i $e |- I = ( Id ` Q ) $.
    ${
      fucolid.q $e |- Q = ( D FuncCat E ) $.
      fucolid.a $e |- ( ph -> A e. ( G ( C Nat D ) H ) ) $.
      fucolid.f $e |- ( ph -> F e. ( D Func E ) ) $.
      $( Post-compose a natural transformation with an identity natural
         transformation.  (Contributed by Zhi Wang, 11-Oct-2025.) $)
      fucolid $p |- ( ph -> ( ( I ` F ) ( <. F , G >. P <. F , H >. ) A )
              = ( x e. ( Base ` C ) |-> ( ( ( ( 1st ` G ) ` x )
                  ( 2nd ` F ) ( ( 1st ` H ) ` x ) ) ` ( A ` x ) ) ) ) $=
        ( cfv co eqid cop ccid c1st ccom cbs cv c2nd cco fucid oveq1d cfuco cvv
        cmpt wcel wceq ccat cnat nat1st2nd natrcl2 funcrcl2 funcrcl3 func1st2nd
        cxp eqidd fucoelvv 1st2nd2 opeq2d eqtrd fucidcl fuco22a wa cfunc adantr
        syl funcf1 natrcl3 ffvelcdmda fvco3d chom ffvelcdmd funcf2 simpr catlid
        wbr natcl mpteq2dva 3eqtrd ) AILRZCIJUAZIKUAZFSZSHUBRZIUCRZUDZCWKSBDUER
        ZBUFZKUCRZRZWNRZWPCRZWPJUCRZRZWRIUGRZSZRZXBWMRZWRWMRZUAXGHUHRZSZSZUMBWO
        XEUMAWHWNCWKAEHGWLILONWLTZQUIUJABCWNDEFIWIHJIKDEUAHUKSZUCRZWJAXLXMXLUGR
        ZUAZXMFUAAXLULULVCUNXLXOUOADEUPUPHUPXLADEXAJUGRZACDEXAXPWQKUGRZDEUQSZXR
        TZACDEJKXRXSPURZUSZUTADEXAXPYAVAAEHWMXCAEHIQVBZVAZAXLVDVEXLULULVFVNAXNF
        XMMVGVHAWIVDAWJVDPAEHGWLIEHUQSZOYDTXKQVIVJABWOXJXEAWPWOUNZVKZXJXGWLRZXE
        XISXEYFWSYGXEXIYFEUERZHUERZWRWLWMYFYHYIEHWMXCYHTZYITZAWMXCEHVLSWDYEYBVM
        ZVOZAWOYHWPWQAWOYHDEWQXQWOTZYJACDEXAXPWQXQXRXSXTVPVOVQZVRUJYFYIHXHWLXEH
        VSRZXFXGYKYPTZXKAHUPUNYEYCVMYFYHYIXBWMYMAWOYHWPXAAWOYHDEXAXPYNYJYAVOVQZ
        VTXHTYFYHYIWRWMYMYOVTYFXBWREVSRZSXFXGYPSWTXDYFYHEHWMXCYSYPXBWRYJYSTZYQY
        LYRYOWAYFCWODEXAXPYSWQXQXRWPXSACXAXPUAWQXQUAXRSUNYEXTVMYNYTAYEWBWEVTWCV
        HWFWG $.
    $}

    fucorid.q $e |- Q = ( C FuncCat D ) $.
    fucorid.a $e |- ( ph -> A e. ( G ( D Nat E ) H ) ) $.
    fucorid.f $e |- ( ph -> F e. ( C Func D ) ) $.
    $( Pre-composing a natural transformation with the identity natural
       transformation of a functor is pre-composing it with the object part of
       the functor, in maps-to notation.  (Contributed by Zhi Wang,
       11-Oct-2025.) $)
    fucorid $p |- ( ph -> ( A ( <. G , F >. P <. H , F >. ) ( I ` F ) )
            = ( x e. ( Base ` C ) |-> ( A ` ( ( 1st ` F ) ` x ) ) ) ) $=
      ( cfv co eqid cop ccid c1st ccom cbs c2nd cco cmpt fucid oveq2d cfuco cvv
      cv cxp wcel wceq ccat func1st2nd funcrcl2 cnat nat1st2nd natrcl2 funcrcl3
      eqidd fucoelvv 1st2nd2 syl opeq2d eqtrd fucidcl fuco22a wbr adantr funcf1
      wa cfunc simpr fvco3d fveq2d ffvelcdmd funcid chom natcl catrid mpteq2dva
      natrcl3 3eqtrd ) ACILRZJIUAZKIUAZFSZSCEUBRZIUCRZUDZWKSBDUERZBUMZWMRZCRZWP
      WNRZWQWQJUFRZSZRZWQJUCRZRZXDUAWQKUCRZRZHUGRZSZSZUHBWOWRUHAWHWNCWKADEGWLIL
      ONWLTZQUIUJABWNCDEFKWIHIJIDEUAHUKSZUCRZWJAXKXLXKUFRZUAZXLFUAAXKULULUNUOXK
      XNUPADEUQUQHUQXKADEWMIUFRZADEIQURZUSAEHXCWTACEHXCWTXEKUFRZEHUTSZXRTZACEHJ
      KXRXSPVAZVBZUSAEHXCWTYAVCZAXKVDVEXKULULVFVGAXMFXLMVHVIAWIVDAWJVDADEGWLIDE
      UTSZOYCTXJQVJPVKABWOXIWRAWPWOUOZVOZXIWRXDHUBRZRZXHSWRYEXBYGWRXHYEXBWQWLRZ
      XARYGYEWSYHXAYEWOEUERZWPWLWMYEWOYIDEWMXOWOTYITZAWMXODEVPSVLYDXPVMVNZAYDVQ
      ZVRVSYEYIEWLHXCWTYFWQYJXJYFTZAXCWTEHVPSZVLYDYAVMZYEWOYIWPWMYKYLVTZWAVIUJY
      EHUERZHXGYFWRHWBRZXDXFYQTZYRTZYMAHUQUOYDYBVMYEYIYQWQXCYEYIYQEHXCWTYJYSYOV
      NYPVTXGTYEYIYQWQXEYEYIYQEHXEXQYJYSAXEXQYNVLYDACEHXCWTXEXQXRXSXTWFVMVNYPVT
      YECYIEHXCWTYRXEXQXRWQXSACXCWTUAXEXQUAXRSUOYDXTVMYJYTYPWCWDVIWEWG $.

    $( Pre-composing a natural transformation with the identity natural
       transformation of a functor is pre-composing it with the object part of
       the functor.  (Contributed by Zhi Wang, 11-Oct-2025.) $)
    fucorid2 $p |- ( ph -> ( A ( <. G , F >. P <. H , F >. ) ( I ` F ) )
            = ( A o. ( 1st ` F ) ) ) $=
      ( vx cfv co c1st cop cbs cv cmpt ccom fucorid cvv wceq wfn c2nd cnat eqid
      wf nat1st2nd natfn dffn2 sylib func1st2nd funcf1 fcompt syl2anc eqtr4d )
      ABHKRIHUAJHUAESSQCUBRZQUCHTRZRBRUDZBVDUEZAQBCDEFGHIJKLMNOPUFADUBRZUGBUMZV
      CVGVDUMVFVEUHABVGUIVHABVGDGITRIUJRJTRJUJRDGUKSZVIULZABDGIJVIVJOUNVGULZUOV
      GBUPUQAVCVGCDVDHUJRVCULVKACDHPURUSQBVDVCVGUGUTVAVB $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Post-composition functors
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d C a g h x $.  $d D a g h x $.  $d E a g h x $.  $d F a g h x $.
    $d K a g h $.  $d Q a g h $.  $d R a g h $.  $d a g h ph x $.
    postcofval.q $e |- Q = ( C FuncCat D ) $.
    postcofval.r $e |- R = ( D FuncCat E ) $.
    postcofval.o $e |- .o. = ( <. R , Q >. curryF ( <. C , D >. o.F E ) ) $.
    postcofval.f $e |- ( ph -> F e. ( D Func E ) ) $.
    postcofval.c $e |- ( ph -> C e. Cat ) $.
    postcofval.k $e |- K = ( ( 1st ` .o. ) ` F ) $.
    $( Value of the post-composition functor as a curry of the functor
       composition bifunctor.  (Contributed by Zhi Wang, 11-Oct-2025.) $)
    postcofval $p |- ( ph -> K = <. ( g e. ( C Func D ) |-> ( F o.func g ) )
      , ( g e. ( C Func D ) , h e. ( C Func D )
         |-> ( a e. ( g ( C Nat D ) h ) |-> ( x e. ( Base ` C )
        |-> ( ( ( ( 1st ` g ) ` x ) ( 2nd ` F ) ( ( 1st ` h ) ` x ) )
                     ` ( a ` x ) ) ) ) ) >. ) $=
      ( co cfunc cv cop cfuco c1st cfv cmpt cnat ccid c2nd cmpo cbs cfuc fucbas
      ccofu func1st2nd funcrcl2 fuccat cxpc oveq12i eqid fucofunca fuchom curf1
      funcrcl3 wa eqidd simpr adantr fuco11b mpteq2dva fucolid mpoeq3dv opeq12d
      wcel eqtrd ) AKGCDUATZJGUBZCDUCIUDTZUEUFZTZUGZGHVQVQMVRHUBZCDUHTZTZJFUIUF
      ZUFMUBZJVRUCJWCUCVSUJUFZTTZUGZUKZUCGVQJVRUOTZUGZGHVQVQMWEBCULUFBUBZWGUFWN
      VRUEUFUFWNWCUEUFUFJUJUFZTUFUGZUGZUKZUCAGHDIUATZVQFEWFMCIUMTZVSLWDKJPDIFOU
      NADIFOADIJUEUFZWOADIJQUPZUQZADIXAWOXBVEZURACDENRXCURACDWTFEUSTIFDIUMTECDU
      MTUSONUTWTVARXCXDVBCDENUNQSCDEWDNWDVAVCWFVAZVDAWBWMWKWRAGVQWAWLAVRVQVOZVF
      ZCDIVRJVTXGVTVGAXFVHAJWSVOZXFQVIVJVKAGHVQVQWJWQAMWEWIWPAWGWEVOZVFZBWGCDWH
      FIJVRWCWFXJWHVGXEOAXIVHAXHXIQVIVLVKVMVNVP $.

    postcofcl.s $e |- S = ( C FuncCat E ) $.
    $( The post-composition functor as a curry of the functor composition
       bifunctor is a functor.  (Contributed by Zhi Wang, 11-Oct-2025.) $)
    postcofcl $p |- ( ph -> K e. ( Q Func S ) ) $=
      ( co cfv fuccat cfunc cfuco fucbas c1st c2nd func1st2nd funcrcl2 funcrcl3
      cbs cop cxpc cfuc oveq12i fucofunca eqid curf1cl ) ACGUARDUISZEDFBCUJGUBR
      JIHMCGELUCACGELACGHUDSZHUESZACGHNUFZUGZACGURUSUTUHZTABCDKOVATABCFEDUKRGEC
      GULRDBCULRUKLKUMQOVAVBUNUQUONPUP $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Pre-composition functors
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    precofvallem.a $e |- A = ( Base ` C ) $.
    precofvallem.b $e |- B = ( Base ` E ) $.
    precofvallem.1 $e |- .1. = ( Id ` D ) $.
    precofvallem.i $e |- I = ( Id ` E ) $.
    precofvallem.f $e |- ( ph -> F ( C Func D ) G ) $.
    precofvallem.k $e |- ( ph -> K ( D Func E ) L ) $.
    precofvallem.x $e |- ( ph -> X e. A ) $.
    $( Lemma for ~ precofval to enable ~ catlid or ~ catrid .  (Contributed by
       Zhi Wang, 11-Oct-2025.) $)
    precofvallem $p |- ( ph -> ( ( ( ( F ` X ) L ( F ` X ) )
                 ` ( ( .1. o. F ) ` X ) ) = ( I ` ( K ` ( F ` X ) ) )
                /\ ( K ` ( F ` X ) ) e. B ) ) $=
      ( ccom cfv wceq wcel cbs eqid funcf1 fvco3d fveq2d ffvelcdmd funcid eqtrd
      co jca ) AMFHUAUBZMHUBZUPLUMZUBZUPKUBZJUBZUCUSCUDAURUPFUBZUQUBUTAUOVAUQAB
      EUEUBZMFHABVBDEHINVBUFZRUGZTUHUIAVBEFGKLJUPVCPQSABVBMHVDTUJZUKULAVBCUPKAV
      BCEGKLVCOSUGVEUJUN $.
  $}

  ${
    $d C a g h x $.  $d D a g h x $.  $d E a g h x $.  $d F a g h x $.
    $d Q a g h $.  $d R a g h $.  $d a g h ph x $.
    precofval.q $e |- Q = ( C FuncCat D ) $.
    precofval.r $e |- R = ( D FuncCat E ) $.
    precofval.o $e |- ( ph -> .o. = ( <. Q , R >. curryF
                          ( ( <. C , D >. o.F E ) o.func ( Q swapF R ) ) ) ) $.
    precofval.f $e |- ( ph -> F e. ( C Func D ) ) $.
    precofval.e $e |- ( ph -> E e. Cat ) $.
    precofval.k $e |- ( ph -> K = ( ( 1st ` .o. ) ` F ) ) $.
    $( Value of the pre-composition functor as a transposed curry of the
       functor composition bifunctor.  (Contributed by Zhi Wang,
       11-Oct-2025.) $)
    precofval $p |- ( ph -> K = <. ( g e. ( D Func E ) |-> ( g o.func F ) )
      , ( g e. ( D Func E ) , h e. ( D Func E )
         |-> ( a e. ( g ( D Nat E ) h ) |-> ( x e. ( Base ` C )
                 |-> ( a ` ( ( 1st ` F ) ` x ) ) ) ) ) >. ) $=
      ( co cfunc cv cop cfuco c1st cfv cmpt cnat ccid c2nd cmpo cbs cfuc fucbas
      func1st2nd funcrcl2 funcrcl3 fuccat cxpc oveq12i eqid fucofunca tposcurf1
      ccofu fuchom wcel wa eqidd adantr simpr fuco11b mpteq2dva fucorid opeq12d
      mpoeq3dv eqtrd ) AKGDIUATZGUBZJCDUCIUDTZUEUFZTZUGZGHVQVQMVRHUBZDIUHTZTZMU
      BZJEUIUFZUFVRJUCWCJUCVSUJUFZTTZUGZUKZUCGVQVRJVDTZUGZGHVQVQMWEBCULUFBUBJUE
      UFZUFWFUFUGZUGZUKZUCAGHCDUATZVQEFWGMCIUMTZVSLWDKJPCDENUNACDENACDWNJUJUFZA
      CDJQUOZUPZACDWNWTXAUQZURADIFOXCRURACDWSFEUSTIFDIUMTECDUMTUSONUTWSVAXBXCRV
      BQSDIFOUNDIFWDOWDVAVEWGVAZVCAWBWMWKWQAGVQWAWLAVRVQVFZVGZCDIJVRVTXFVTVHAJW
      RVFZXEQVIAXEVJVKVLAGHVQVQWJWPAMWEWIWOAWFWEVFZVGZBWFCDWHEIJVRWCWGXIWHVHXDN
      AXHVJAXGXHQVIVMVLVOVNVP $.

    $( Alternate proof of ~ precofval .  (Contributed by Zhi Wang,
       11-Oct-2025.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    precofvalALT $p |- ( ph -> K = <. ( g e. ( D Func E ) |-> ( g o.func F ) )
      , ( g e. ( D Func E ) , h e. ( D Func E )
         |-> ( a e. ( g ( D Nat E ) h ) |-> ( x e. ( Base ` C )
                 |-> ( a ` ( ( 1st ` F ) ` x ) ) ) ) ) >. ) $=
      ( cfv cfunc co cv cop cfuco c1st cmpt cnat ccid c2nd cmpo cbs cfuc fucbas
      ccofu wrel wcel relfunc 1st2ndbr sylancr funcrcl2 funcrcl3 fuccat oveq12i
      wbr cxpc eqid fucofunca fuchom tposcurf1 wa df-ov wceq cvv cxp ccat eqidd
      fucoelvv 1st2nd2 syl adantr adantl 1st2nd opeq12d fuco11 eqtr4d mpteq2dva
      mpan oveq12d eqtrid ccom cco fucid oveq2d fucidcl simpr fuco22a ad3antrrr
      ad2antrr ad3antlr precofvallem simpld simprd simpllr ffvelcdmda ffvelcdmd
      chom funcf1 nat1st2nd natcl catrid eqtrd 3eqtrd 3impb mpoeq3dva ) AKGDIUA
      UBZGUCZJCDUDIUEUBZUFTZUBZUGZGHXPXPMXQHUCZDIUHUBZUBZMUCZJEUITZTZXQJUDZYBJU
      DZXRUJTZUBZUBZUGZUKZUDGXPXQJUOUBZUGZGHXPXPMYDBCULTZBUCZJUFTZTZYETZUGZUGZU
      KZUDAGHCDUAUBZXPEFYFMCIUMUBZXRLYCKJPCDENUNACDENACDYSJUJTZAUUEUPZJUUEUQZYS
      UUGUUEVEZCDURZQJUUEUSUTZVAZACDYSUUGUULVBZVCADIFOUUNRVCACDUUFFEVFUBIFDIUMU
      BECDUMUBVFONVDUUFVGUUMUUNRVHQSDIFOUNDIFYCOYCVGZVIYFVGZVJAYAYPYNUUDAGXPXTY
      OAXQXPUQZVKZXTYHXSTZYOXQJXSVLUURUUSXQUFTZXQUJTZUDZYSUUGUDZUOUBYOUURCDYJYH
      IYSUUGUUTUVAXSAXRXSYJUDVMZUUQAXRVNVNVOUQUVDACDVPVPIVPXRUUMUUNRAXRVQVRXRVN
      VNVSVTZWAAUUJUUQUULWAUUQUUTUVAXPVEZAXPUPZUUQUVFDIURZXQXPUSWHZWBUURXQUVBJU
      VCUUQXQUVBVMZAUVGUUQUVJUVHXQXPWCWHWBZAJUVCVMZUUQAUUHUUIUVLUUKQJUUEWCUTWAZ
      WDWEUURXQUVBJUVCUOUVKUVMWIWFWJWGAGHXPXPYMUUCAUUQYBXPUQZYMUUCVMAUUQUVNVKZV
      KZMYDYLUUBUVPYEYDUQZVKZYLYEDUITZYSWKZYKUBBYQUUAYRUVTTYTYTUVAUBTZYTUUTTZUW
      BUDYTYBUFTZTZIWLTZUBZUBZUGUUBUVRYGUVTYEYKAYGUVTVMUVOUVQACDEUVSJYFNUUPUVSV
      GZQWMWSWNUVRBUVTYECDYJYBYHIJXQJXSYIAUVDUVOUVQUVEWSUVRYHVQUVRYIVQAUVTJJCDU
      HUBZUBUQUVOUVQACDEUVSJUWINUWIVGUWHQWOWSUVPUVQWPZWQUVRBYQUWGUUAUVRYRYQUQZV
      KZUWGUUAUWBIUITZTZUWFUBUUAUWLUWAUWNUUAUWFUWLUWAUWNVMZUWBIULTZUQZUWLYQUWPC
      DUVSIYSUUGUWMUUTUVAYRYQVGZUWPVGZUWHUWMVGZAUUJUVOUVQUWKUULWRUVOUVFAUVQUWKU
      UQUVFUVNUVIWAWTUVRUWKWPXAZXBWNUWLUWPIUWEUWMUUAIXGTZUWBUWDUWSUXBVGZUWTAIVP
      UQUVOUVQUWKRWRUWLUWOUWQUXAXCUWEVGUWLDULTZUWPYTUWCUWLUXDUWPDIUWCYBUJTZUXDV
      GZUWSUWLUVGUVNUWCUXEXPVEUVHUWLUUQUVNAUVOUVQUWKXDXCYBXPUSUTXHUVRYQUXDYRYSU
      VRYQUXDCDYSUUGUWRUXFAUUJUVOUVQUULWSXHXEZXFUWLYEUXDDIUUTUVAUXBUWCUXEYCYTUU
      OUWLYEDIXQYBYCUUOUVRUVQUWKUWJWAXIUXFUXCUXGXJXKXLWGXMWGXNXOWDXL $.

    $( Value of the pre-composition functor as a transposed curry of the
       functor composition bifunctor.  (Contributed by Zhi Wang,
       11-Oct-2025.) $)
    precofval2 $p |- ( ph -> K = <. ( g e. ( D Func E ) |-> ( g o.func F ) )
      , ( g e. ( D Func E ) , h e. ( D Func E )
         |-> ( a e. ( g ( D Nat E ) h ) |-> ( a o. ( 1st ` F ) ) ) ) >. ) $=
      ( vx cfv cfunc co cv ccofu cmpt cnat cbs c1st cmpo cop ccom precofval cvv
      wcel wf wceq wfn c2nd eqid nat1st2nd natfn dffn2 func1st2nd funcf1 fcompt
      id sylib syl2anr mpteq2dva mpoeq3dv opeq2d eqtr4d ) AJFCHUAUBZFUCZIUDUBUE
      ZFGVMVMLVNGUCZCHUFUBZUBZSBUGTZSUCIUHTZTLUCZTUEZUEZUIZUJVOFGVMVMLVRWAVTUKZ
      UEZUIZUJASBCDEFGHIJKLMNOPQRULAWGWDVOAFGVMVMWFWCALVRWEWBWAVRUNZCUGTZUMWAUO
      ZVSWIVTUOWEWBUPAWHWAWIUQWJWHWAWICHVNUHTVNURTVPUHTVPURTVQVQUSZWHWACHVNVPVQ
      WKWHVFUTWIUSZVAWIWAVBVGAVSWIBCVTIURTVSUSWLABCIPVCVDSWAVTVSWIUMVEVHVIVJVKV
      L $.

    precofcl.s $e |- S = ( C FuncCat E ) $.
    $( The pre-composition functor as a transposed curry of the functor
       composition bifunctor is a functor.  (Contributed by Zhi Wang,
       11-Oct-2025.) $)
    precofcl $p |- ( ph -> K e. ( R Func S ) ) $=
      ( co cfv fuccat cfunc cfuco fucbas c1st c2nd func1st2nd funcrcl2 funcrcl3
      cop cxpc cfuc oveq12i fucofunca tposcurf1cl ) ABCUARDEFBCUIGUBRJIHMBCDKUC
      ABCDKABCHUDSZHUESZABCHNUFZUGZABCUOUPUQUHZTACGELUSOTABCFEDUJRGECGUKRDBCUKR
      UJLKULQURUSOUMNPUN $.
  $}

  ${
    $d C a g h $.  $d D a g h $.  $d E a g h $.  $d F a g h $.  $d G a g h $.
    $d Q a g h $.  $d R a g h $.  $d a g h ph $.
    precoffunc.r $e |- R = ( D FuncCat E ) $.
    precoffunc.b $e |- B = ( D Func E ) $.
    precoffunc.n $e |- N = ( D Nat E ) $.
    precoffunc.f $e |- ( ph -> F ( C Func D ) G ) $.
    precoffunc.e $e |- ( ph -> E e. Cat ) $.
    precoffunc.k $e |- ( ph -> K = ( g e. B |-> ( g o.func <. F , G >. ) ) ) $.
    precoffunc.l $e |- ( ph -> L = ( g e. B , h e. B
         |-> ( a e. ( g N h ) |-> ( a o. F ) ) ) ) $.
    ${
      precofval3.q $e |- Q = ( C FuncCat D ) $.
      precofval3.o $e |- ( ph -> .o. = ( <. Q , R >. curryF
                          ( ( <. C , D >. o.F E ) o.func ( Q swapF R ) ) ) ) $.
      precofval3.m $e |- ( ph -> M = ( ( 1st ` .o. ) ` <. F , G >. ) ) $.
      $( Value of the pre-composition functor as a transposed curry of the
         functor composition bifunctor.  (Contributed by Zhi Wang,
         20-Oct-2025.) $)
      precofval3 $p |- ( ph -> <. K , L >. = M ) $=
        ( cop cfunc co cv ccofu cmpt cnat c1st cfv ccom cmpo mpteq1i eqtrdi a1i
        wceq oveqd cvv wcel wa wrel wbr relfunc brrelex12 sylancr op1stg eqcomd
        coeq2d mpteq12dv mpoeq123dv eqtrd opeq12d df-br sylib precofval2 eqtr4d
        syl ) ALMUHGDIUIUJZGUKZJKUHZULUJZUMZGHWDWDQWEHUKZDIUNUJZUJZQUKZWFUOUPZU
        QZUMZURZUHNALWHMWPALGBWGUMWHUCGBWDWGSUSUTAMGHBBQWEWIOUJZWLJUQZUMZURWPUD
        AGHBBWSWDWDWOBWDVBASVAZWTAQWQWRWKWNAOWJWEWIOWJVBATVAVCAJWMWLAWMJAJVDVEK
        VDVEVFZWMJVBACDUIUJZVGJKXBVHZXACDVIUAJKXBVJVKJKVDVDVLWCVMVNVOVPVQVRACDE
        FGHIWFNPQUERUFAXCWFXBVEUAJKXBVSVTUBUGWAWB $.
    $}

    precoffunc.s $e |- S = ( C FuncCat E ) $.
    $( The pre-composition functor, expressed explicitly, is a functor.
       (Contributed by Zhi Wang, 11-Oct-2025.)  (Proof shortened by Zhi Wang,
       20-Oct-2025.) $)
    precoffunc $p |- ( ph -> K ( R Func S ) L ) $=
      ( cop cfunc wcel wbr cfuc cfuco cswapf ccofu ccurf eqid eqidd df-br sylib
      co c1st cfv precofval3 precofcl sylibr ) ALMUDZEFUEUQZUFLMVDUGACDCDUHUQZE
      FIJKUDZVCVEEUDCDUDIUIUQVEEUJUQUKUQULUQZVEUMZPAVGUNZAJKCDUEUQZUGVFVJUFSJKV
      JUOUPTABCDVEEGHIJKLMVFVGURUSUSZNVGOPQRSTUAUBVHVIAVKUNUTUCVALMVDUOVB $.
  $}

  $c -o.F $.

  $( Extend class notation with pre-composition functors. $)
  cprcof $a class -o.F $.

$(
  @( Alternate definition of pre-composition functors.  (Contributed by Zhi
     Wang, XX-Nov-2025.)  (New usage is discouraged.) @)
  df-prcofALT @a |- -o.F = ( s e. _V , f e. _V |->
        [_ ( s ` 0 ) / c ]_ [_ ( s ` 1 ) / d ]_ [_ ( s ` 2 ) / e ]_
        [_ ( d Func e ) / b ]_
        <. ( g e. b |-> ( g o.func f ) ) , ( g e. b , h e. b
           |-> ( a e. ( g ( d Nat e ) h ) |-> ( a o. ( 1st ` f ) ) ) ) >. ) @.
$)

  ${
    $d B a b d e f k l p $.  $d D a b d e f k l p $.  $d E a b d e f k l p $.
    $d F a b d e f k l p $.  $d G a k l $.  $d N b d e f p $.
    $d P a b d e f k l p $.  $d U b d e f p $.  $d V b d e f p $.
    $d a b d e f k l p ph $.
    $( Definition of pre-composition functors.  The object part of the
       pre-composition functor given by ` F ` pre-composes a functor with
       ` F ` ; the morphism part pre-composes a natural transformation with the
       object part of ` F ` , in terms of function composition.  Comments
       before the definition in <HTML>&sect;</HTML> 3 of Chapter X in p. 236 of
       Mac Lane, Saunders, _Categories for the Working Mathematician_, 2nd
       Edition, Springer Science+Business Media, New York, (1998)
       [QA169.M33 1998]; available at
       ~ https://math.mit.edu/~~hrm/palestine/maclane-categories.pdf (retrieved
       3 Nov 2025). The notation ` -o.F ` is inspired by this page:
       ~ https://1lab.dev/Cat.Functor.Compose.html .

       The pre-composition functor can also be defined as a transposed curry of
       the functor composition bifunctor ( ~ precofval3 ).  But such definition
       requires an explicit third category. ~ prcoftposcurfuco and
       ~ prcoftposcurfucoa prove the equivalence.  (Contributed by Zhi Wang,
       2-Nov-2025.) $)
    df-prcof $a |- -o.F = ( p e. _V , f e. _V |->
         [_ ( 1st ` p ) / d ]_ [_ ( 2nd ` p ) / e ]_ [_ ( d Func e ) / b ]_
         <. ( k e. b |-> ( k o.func f ) ) ,
            ( k e. b , l e. b |->
              ( a e. ( k ( d Nat e ) l ) |-> ( a o. ( 1st ` f ) ) ) ) >. ) $.

    $( The domain of ` -o.F ` is a relation.  (Contributed by Zhi Wang,
       2-Nov-2025.) $)
    reldmprcof $p |- Rel dom -o.F $=
      ( vp vf vd ve vb vk vl va cvv cv c1st cfv c2nd cfunc ccofu cmpt cnat ccom
      co csb cmpo cop cprcof df-prcof reldmmpo ) ABIICAJZKLDUFMLECJZDJZNSFEJZFJ
      ZBJZOSPFGUIUIHUJGJUGUHQSSHJUKKLRPUAUBTTTUCDBFAHECGUDUE $.

    ${
      prcofvalg.b $e |- B = ( D Func E ) $.
      prcofvalg.n $e |- N = ( D Nat E ) $.
      ${
        prcofvalg.f $e |- ( ph -> F e. U ) $.
        prcofvalg.p $e |- ( ph -> P e. V ) $.
        prcofvalg.d $e |- ( ph -> ( 1st ` P ) = D ) $.
        prcofvalg.e $e |- ( ph -> ( 2nd ` P ) = E ) $.
        $( Value of the pre-composition functor.  (Contributed by Zhi Wang,
           2-Nov-2025.) $)
        prcofvalg $p |- ( ph -> ( P -o.F F ) =
                 <. ( k e. B |-> ( k o.func F ) ) ,
                    ( k e. B , l e. B |->
                      ( a e. ( k N l ) |-> ( a o. ( 1st ` F ) ) ) ) >. ) $=
          ( cvv cv vp vf vd ve vb c1st cfv c2nd cfunc ccofu cmpt cnat ccom cmpo
          co cop csb cprcof df-prcof a1i wa fvexd simprl fveq2d adantr ad2antrr
          wceq eqtrd ovexd simplr simpr oveq12d eqtr4di simprd oveq2d mpteq12dv
          simp-4r oveqdr coeq2d mpoeq123dv opeq12d csbied2 elexd wcel ovmpod
          opex ) AUAUBDHSSUCUATZUFUGZUDWGUHUGZUEUCTZUDTZUIUOZFUETZFTZUBTZUJUOZU
          KZFLWMWMKWNLTZWJWKULUOZUOZKTZWOUFUGZUMZUKZUNZUPZUQZUQZUQZFBWNHUJUOZUK
          ZFLBBKWNWRIUOZXAHUFUGZUMZUKZUNZUPZURSURUAUBSSXIUNVGAUDUBFUAKUEUCLUSUT
          AWGDVGZWOHVGZVAZVAZUCWHCXHXQSYAWGUFVBYAWHDUFUGZCYAWGDUFAXRXSVCZVDAYBC
          VGXTQVEVHYAWJCVGZVAZUDWIGXGXQSYEWGUHVBYEWIDUHUGZGYEWGDUHYAXRYDYCVEVDA
          YFGVGXTYDRVFVHYEWKGVGZVAZUEWLBXFXQSYHWJWKUIVIYHWLCGUIUOBYHWJCWKGUIYAY
          DYGVJZYEYGVKZVLMVMYHWMBVGZVAZWQXKXEXPYLFWMWPBXJYHYKVKZYLWOHWNUJYLXRXS
          AXTYDYGYKVQVNZVOVPYLFLWMWMXDBBXOYMYMYLKWTXCXLXNYHYKFLWSIYHWSCGULUOIYH
          WJCWKGULYIYJVLNVMVRYLXBXMXAYLWOHUFYNVDVSVPVTWAWBWBWBADJPWCAHEOWCXQSWD
          AXKXPWFUTWE $.
      $}

      ${
        prcofvala.d $e |- ( ph -> D e. V ) $.
        prcofvala.e $e |- ( ph -> E e. W ) $.
        ${
          prcofvala.f $e |- ( ph -> F e. U ) $.
          $( Value of the pre-composition functor.  (Contributed by Zhi Wang,
             2-Nov-2025.) $)
          prcofvala $p |- ( ph -> ( <. D , E >. -o.F F ) =
                 <. ( k e. B |-> ( k o.func F ) ) ,
                    ( k e. B , l e. B |->
                      ( a e. ( k N l ) |-> ( a o. ( 1st ` F ) ) ) ) >. ) $=
            ( cvv wcel cfv cop opex a1i c1st wceq op1stg syl2anc c2nd prcofvalg
            op2ndg ) ABCCFUAZDEFGHRKLMNQUKRSACFUBUCACISZFJSZUKUDTCUEOPCFIJUFUGA
            ULUMUKUHTFUEOPCFIJUJUGUI $.
        $}

        prcofval.r $e |- Rel R $.
        prcofval.f $e |- ( ph -> F R G ) $.
        $( Value of the pre-composition functor.  (Contributed by Zhi Wang,
           2-Nov-2025.) $)
        prcofval $p |- ( ph -> ( <. D , E >. -o.F <. F , G >. ) =
                 <. ( k e. B |-> ( k o.func <. F , G >. ) ) ,
                    ( k e. B , l e. B |->
                      ( a e. ( k N l ) |-> ( a o. F ) ) ) >. ) $=
          ( cvv cop cprcof co ccofu cmpt c1st cfv ccom cmpo wcel opex prcofvala
          cv a1i wa wceq brrelex12i op1stg 3syl coeq2d mpteq2dv mpoeq3dv opeq2d
          wbr eqtrd ) ACFUAGHUAZUBUCEBEUMZVFUDUCUEZEMBBLVGMUMIUCZLUMZVFUFUGZUHZ
          UEZUIZUAVHEMBBLVIVJGUHZUEZUIZUAABCTEFVFIJKLMNOPQVFTUJAGHUKUNULAVNVQVH
          AEMBBVMVPALVIVLVOAVKGVJAGHDVDGTUJHTUJUOVKGUPSGHDRUQGHTTURUSUTVAVBVCVE
          $.
      $}
    $}

    ${
      $d A a k l $.  $d C a k l $.
      prcofpropd.1 $e |- ( ph -> ( Homf ` A ) = ( Homf ` B ) ) $.
      prcofpropd.2 $e |- ( ph -> ( comf ` A ) = ( comf ` B ) ) $.
      prcofpropd.3 $e |- ( ph -> ( Homf ` C ) = ( Homf ` D ) ) $.
      prcofpropd.4 $e |- ( ph -> ( comf ` C ) = ( comf ` D ) ) $.
      prcofpropd.a $e |- ( ph -> A e. V ) $.
      prcofpropd.b $e |- ( ph -> B e. V ) $.
      prcofpropd.c $e |- ( ph -> C e. V ) $.
      prcofpropd.d $e |- ( ph -> D e. V ) $.
      prcofpropd.f $e |- ( ph -> F e. W ) $.
      $( If the categories have the same set of objects, morphisms, and
         compositions, then they have the same pre-composition functors.
         (Contributed by Zhi Wang, 21-Nov-2025.) $)
      prcofpropd $p |- ( ph -> ( <. A , C >. -o.F F )
                             = ( <. B , D >. -o.F F ) ) $=
        ( vk co cfv vl va cfunc cv ccofu cmpt cnat c1st ccom cmpo cop funcpropd
        cprcof mpteq1d wceq wcel adantr wa chomf ccat funcrcl ad2antrl catpropd
        ccomf simpld mpbid natpropd oveqd mpoeq123dva opeq12d prcofvala 3eqtr4d
        simprd eqid ) ARBDUCSZRUDZFUESZUFZRUAVOVOUBVPUAUDZBDUGSZSZUBUDFUHTUIZUF
        ZUJZUKRCEUCSZVQUFZRUAWEWEUBVPVSCEUGSZSZWBUFZUJZUKBDUKFUMSCEUKFUMSAVRWFW
        DWJARVOWEVQABCDEGIJKLMNOPULZUNARUAVOVOWCWEWEWIWKAVOWEUOVPVOUPZWKUQAWLVS
        VOUPZURZURZUBWAWHWBWOVTWGVPVSWOBCDEABUSTCUSTUOWNIUQZABVDTCVDTUOWNJUQZAD
        USTEUSTUOWNKUQZADVDTEVDTUOWNLUQZWOBUTUPZDUTUPZWLWTXAURAWMBDVPVAVBZVEZWO
        WTCUTUPXCWOBCUTGWPWQXCACGUPWNNUQVCVFWOWTXAXBVMZWOXAEUTUPXDWODEUTGWRWSXD
        AEGUPWNPUQVCVFVGVHUNVIVJAVOBHRDFVTGGUBUAVOVNVTVNMOQVKAWECHREFWGGGUBUAWE
        VNWGVNNPQVKVL $.
    $}

    ${
      prcofelvv.f $e |- ( ph -> F e. U ) $.
      prcofelvv.p $e |- ( ph -> P e. V ) $.
      $( The pre-composition functor is an ordered pair.  (Contributed by Zhi
         Wang, 4-Nov-2025.) $)
      prcofelvv $p |- ( ph -> ( P -o.F F ) e. ( _V X. _V ) ) $=
        ( vk vl va cprcof co c1st cfv cfunc cv cmpt cvv eqid eqidd c2nd cop cxp
        ccofu cnat ccom cmpo prcofvalg ovex mptex mpoex opelvv eqeltrdi ) ABDKL
        HBMNZBUANZOLZHPZDUDLZQZHIUPUPJUQIPUNUOUELZLJPDMNUFQZUGZUBRRUCAUPUNBCHUO
        DUTEJIUPSUTSFGAUNTAUOTUHUSVBHUPURUNUOOUIZUJHIUPUPVAVCVCUKULUM $.
    $}

    $( The domain of the object part of the pre-composition functor is a
       relation.  (Contributed by Zhi Wang, 2-Nov-2025.) $)
    reldmprcof1 $p |- Rel dom ( 1st ` ( P -o.F F ) ) $=
      ( vk vl va cvv wcel cprcof co c1st cfv wrel cfunc cv ccofu cmpt ovex eqid
      cdm c0 wa c2nd relfunc dmmpti releqi mpbir cnat ccom cmpo cop simpr simpl
      wceq eqidd prcofvalg mptex mpoex op1std dmeqd releqd mpbiri wn reldmprcof
      syl rel0 ovprc fveq2d 1st0 eqtrdi dm0 pm2.61i ) AFGZBFGZUAZABHIZJKZSZLZVN
      VRCAJKZAUBKZMIZCNZBOIZPZSZLZWFWALVSVTUCWEWACWAWCWDWBBOQWDRUDUEUFVNVQWEVNV
      PWDVNVOWDCDWAWAEWBDNVSVTUGIZIENBJKUHPZUIZUJUMVPWDUMVNWAVSAFCVTBWGFEDWARWG
      RVLVMUKVLVMULVNVSUNVNVTUNUOWDWIVOCWAWCVSVTMQZUPCDWAWAWHWJWJUQURVDUSUTVAVN
      VBZVRTLVEWKVQTWKVQTSTWKVPTWKVPTJKTWKVOTJABHVCVFVGVHVIUSVJVIUTVAVK $.

    $( The domain of the morphism part of the pre-composition functor is a
       relation.  (Contributed by Zhi Wang, 2-Nov-2025.) $)
    reldmprcof2 $p |- Rel dom ( 2nd ` ( P -o.F F ) ) $=
      ( vk vl va cvv wcel cprcof co c2nd cfv cdm wrel c1st cfunc cmpt eqid wceq
      cv c0 cnat ccom cmpo reldmmpo ccofu cop simpr simpl eqidd prcofvalg mptex
      wa ovex mpoex op2ndd syl dmeqd releqd mpbiri rel0 reldmprcof ovprc fveq2d
      wn 2nd0 eqtrdi dm0 pm2.61i ) AFGZBFGZULZABHIZJKZLZMZVKVOCDANKZAJKZOIZVREC
      SZDSVPVQUAIZIESBNKUBPZUCZLZMCDVRVRWAWBWBQUDVKVNWCVKVMWBVKVLCVRVSBUEIZPZWB
      UFRVMWBRVKVRVPAFCVQBVTFEDVRQVTQVIVJUGVIVJUHVKVPUIVKVQUIUJWEWBVLCVRWDVPVQO
      UMZUKCDVRVRWAWFWFUNUOUPUQURUSVKVDZVOTMUTWGVNTWGVNTLTWGVMTWGVMTJKTWGVLTJAB
      HVAVBVCVEVFUQVGVFURUSVH $.

    prcoffunc.r $e |- R = ( D FuncCat E ) $.
    prcoffunc.e $e |- ( ph -> E e. Cat ) $.
    ${
      $d .o. a k l $.  $d C a k l $.  $d M a k l $.  $d N a k l $.
      $d R a k l $.  $d Q a k l $.
      prcoftposcurfuco.q $e |- Q = ( C FuncCat D ) $.
      prcoftposcurfuco.o $e |- ( ph -> .o. = ( <. Q , R >. curryF
                          ( ( <. C , D >. o.F E ) o.func ( Q swapF R ) ) ) ) $.
      ${
        prcoftposcurfuco.m $e |- ( ph -> M
                                         = ( ( 1st ` .o. ) ` <. F , G >. ) ) $.
        prcoftposcurfuco.f $e |- ( ph -> F ( C Func D ) G ) $.
        $( The pre-composition functor is the transposed curry of the functor
           composition bifunctor.  (Contributed by Zhi Wang, 2-Nov-2025.) $)
        prcoftposcurfuco $p |- ( ph ->
                                      ( <. D , E >. -o.F <. F , G >. ) = M ) $=
          ( vk vl va co cop cprcof cfunc cv ccofu cmpt cnat ccom cmpo ccat eqid
          funcrcl3 relfunc prcofval eqidd precofval3 eqtrd ) ACFUAGHUAZUBTQCFUC
          TZQUDZURUETUFZQRUSUSSUTRUDCFUGTZTSUDGUHUFUIZUAIAUSCBCUCTQFGHVBUJUJSRU
          SUKZVBUKZABCGHPULLBCUMPUNAUSBCDEQRFGHVAVCIVBJSKVDVEPLAVAUOAVCUOMNOUPU
          Q $.
      $}

      prcoftposcurfucoa.m $e |- ( ph -> M = ( ( 1st ` .o. ) ` F ) ) $.
      prcoftposcurfucoa.f $e |- ( ph -> F e. ( C Func D ) ) $.
      $( The pre-composition functor is the transposed curry of the functor
         composition bifunctor.  (Contributed by Zhi Wang, 2-Nov-2025.) $)
      prcoftposcurfucoa $p |- ( ph -> ( <. D , E >. -o.F F ) = M ) $=
        ( cop cprcof co c1st cfv c2nd cfunc wrel wcel wceq 1st2nd oveq2d fveq2d
        relfunc sylancr eqtrd func1st2nd prcoftposcurfuco ) ACFPZGQRUNGSTZGUATZ
        PZQRHAGUQUNQABCUBRZUCGURUDGUQUEBCUIOGURUFUJZUGABCDEFUOUPHIJKLMAHGISTZTU
        QUTTNAGUQUTUSUHUKABCGOULUMUK $.
    $}

    prcoffunc.s $e |- S = ( C FuncCat E ) $.
    ${
      prcoffunc.f $e |- ( ph -> F ( C Func D ) G ) $.
      $( The pre-composition functor is a functor.  (Contributed by Zhi Wang,
         2-Nov-2025.) $)
      prcoffunc $p |- ( ph -> ( <. D , E >. -o.F <. F , G >. )
                             e. ( R Func S ) ) $=
        ( cfuc co cop cprcof cfuco cswapf eqidd cfv ccofu ccurf eqid cfunc wcel
        wbr df-br sylib c1st prcoftposcurfuco precofcl ) ABCBCMNZDEFGHOZCFOUMPN
        ULDOBCOFQNULDRNUANUBNZULUCZIAUNSZAGHBCUDNZUFUMUQUELGHUQUGUHJABCULDFGHUM
        UNUITTZUNIJUOUPAURSLUJKUK $.
    $}

    prcoffunca.f $e |- ( ph -> F e. ( C Func D ) ) $.
    $( The pre-composition functor is a functor.  (Contributed by Zhi Wang,
       2-Nov-2025.) $)
    prcoffunca $p |- ( ph -> ( <. D , E >. -o.F F ) e. ( R Func S ) ) $=
      ( cfuc co cop cprcof cfuco cswapf ccofu eqidd cfv ccurf prcoftposcurfucoa
      eqid c1st precofcl ) ABCBCLMZDEFGCFNGOMUFDNBCNFPMUFDQMRMUAMZUFUCZHAUGSZKI
      ABCUFDFGGUGUDTTZUGHIUHUIAUJSKUBJUE $.

    prcoffunca2.k $e |- ( ph -> ( <. D , E >. -o.F F ) = <. K , L >. ) $.
    $( The pre-composition functor is a functor.  (Contributed by Zhi Wang,
       4-Nov-2025.) $)
    prcoffunca2 $p |- ( ph -> K ( R Func S ) L ) $=
      ( cop cfunc co wcel wbr cprcof prcoffunca eqeltrrd df-br sylibr ) AHIOZDE
      PQZRHIUFSACFOGTQUEUFNABCDEFGJKLMUAUBHIUFUCUD $.
  $}

  ${
    $d D a b k l $.  $d E a b k l $.  $d F a b k l $.  $d K a b k l $.
    $d O a b k l $.  $d a b k l ph $.
    prcof1.k $e |- ( ph -> K e. ( D Func E ) ) $.
    prcof1.o $e |- ( ph -> ( 1st ` ( <. D , E >. -o.F F ) ) = O ) $.
    $( The object part of the pre-composition functor.  (Contributed by Zhi
       Wang, 3-Nov-2025.) $)
    prcof1 $p |- ( ph -> ( O ` K ) = ( K o.func F ) ) $=
      ( vk vl va vb cvv cfv ccofu co wceq cv c1st c0 wcel cfunc cop cprcof cmpt
      wa adantr cnat ccom cmpo ccat eqid func1st2nd funcrcl2 funcrcl3 prcofvala
      c2nd simpr fveq2d mptex mpoex op1st eqtrdi eqtr3d oveq1d ovexd fvmptd 0fv
      ovex reldmprcof ovprc2 1st0 sylan9req fveq1d cdm df-cofu reldmmpo 3eqtr4a
      wn adantl pm2.61dan ) ADMUAZEFNZEDOPZQAWBUFZIEIRZDOPZWDBCUBPZFMWEBCUCZDUD
      PZSNZFIWHWGUEZAWKFQWBHUGWEWKWLIJWHWHKWFJRZBCUHPZPKRZDSNUIUEZUJZUCZSNWLWEW
      JWRSWEWHBMICDWNUKUKKJWHULWNULWEBCESNZEUQNZWEBCEAEWHUAWBGUGZUMZUNWEBCWSWTX
      BUOAWBURUPUSWLWQIWHWGBCUBVIZUTIJWHWHWPXCXCVAVBVCVDWEWFEQZUFWFEDOWEXDURVEX
      AWEEDOVFVGAWBVSZUFZETNTWCWDEVHXFEFTAXEFWKTHXEWKTSNTXEWJTSWIDUDVJVKUSVLVCV
      MVNXEWDTQAEDOJIMMWMSNWFSNZUIKLWFUQNZVOVOZXIWOXGNLRZXGNWMUQNPWOXJXHPUIUJUC
      OKLIJVPVQVKVTVRWA $.
  $}

  ${
    $d D a k l $.  $d E a k l $.  $d F a k l $.  $d G a k l $.  $d K a k l $.
    $d L a k l $.  $d N a k l $.  $d P k l $.  $d R k l $.  $d U k l $.
    $d a k l ph $.
    prcof2a.n $e |- N = ( D Nat E ) $.
    prcof2a.k $e |- ( ph -> K e. ( D Func E ) ) $.
    prcof2a.l $e |- ( ph -> L e. ( D Func E ) ) $.
    ${
      prcof2a.p $e |- ( ph -> ( 2nd ` ( <. D , E >. -o.F F ) ) = P ) $.
      prcof2a.f $e |- ( ph -> F e. U ) $.
      $( The morphism part of the pre-composition functor.  (Contributed by Zhi
         Wang, 3-Nov-2025.) $)
      prcof2a $p |- ( ph -> ( K P L ) = ( a e. ( K N L )
                                      |-> ( a o. ( 1st ` F ) ) ) ) $=
        ( vk vl co cfv c2nd cfunc c1st ccom cmpt cvv cop cprcof cmpo ccofu ccat
        cv eqid func1st2nd funcrcl2 funcrcl3 prcofvala fveq2d mptex mpoex op2nd
        ovex eqtrdi eqtr3d wceq simprl simprr oveq12d mpteq1d wcel a1i ovmpod
        wa ) APQGHBEUARZVMJPUKZQUKZIRZJUKFUBSUCZUDZJGHIRZVQUDZCUEABEUFFUGRZTSZC
        PQVMVMVRUHZNAWBPVMVNFUIRZUDZWCUFZTSWCAWAWFTAVMBDPEFIUJUJJQVMULKABEGUBSZ
        GTSZABEGLUMZUNABEWGWHWIUOOUPUQWEWCPVMWDBEUAVAZURPQVMVMVRWJWJUSUTVBVCAVN
        GVDZVOHVDZVLVLZJVPVSVQWMVNGVOHIAWKWLVEAWKWLVFVGVHLMVTUEVIAJVSVQGHIVAURV
        JVK $.
    $}

    prcof2.p $e |- ( ph -> ( 2nd ` ( <. D , E >. -o.F <. F , G >. ) ) = P ) $.
    prcof2.r $e |- Rel R $.
    prcof2.f $e |- ( ph -> F R G ) $.
    $( The morphism part of the pre-composition functor.  (Contributed by Zhi
       Wang, 3-Nov-2025.) $)
    prcof2 $p |- ( ph -> ( K P L ) = ( a e. ( K N L ) |-> ( a o. F ) ) ) $=
      ( vk vl co cfunc cv ccom cmpt cvv cop cprcof c2nd cfv cmpo ccat eqid c1st
      ccofu func1st2nd funcrcl2 funcrcl3 prcofval fveq2d ovex mptex mpoex op2nd
      eqtrdi eqtr3d wceq wa simprl simprr oveq12d mpteq1d wcel a1i ovmpod ) ARS
      HIBEUATZVOKRUBZSUBZJTZKUBFUCZUDZKHIJTZVSUDZCUEABEUFFGUFZUGTZUHUIZCRSVOVOV
      TUJZOAWERVOVPWCUNTZUDZWFUFZUHUIWFAWDWIUHAVOBDREFGJUKUKKSVOULLABEHUMUIZHUH
      UIZABEHMUOZUPABEWJWKWLUQPQURUSWHWFRVOWGBEUAUTZVARSVOVOVTWMWMVBVCVDVEAVPHV
      FZVQIVFZVGVGZKVRWAVSWPVPHVQIJAWNWOVHAWNWOVIVJVKMNWBUEVLAKWAVSHIJUTVAVMVN
      $.
  $}

  ${
    $d A a $.  $d D a $.  $d E a $.  $d F a $.  $d K a $.  $d L a $.  $d N a $.
    $d P a $.  $d U a $.  $d a ph $.
    prcof21a.n $e |- N = ( D Nat E ) $.
    prcof21a.a $e |- ( ph -> A e. ( K N L ) ) $.
    prcof21a.p $e |- ( ph -> ( 2nd ` ( <. D , E >. -o.F F ) ) = P ) $.
    ${
      prcof21a.f $e |- ( ph -> F e. U ) $.
      $( The morphism part of the pre-composition functor.  (Contributed by Zhi
         Wang, 3-Nov-2025.) $)
      prcof21a $p |- ( ph -> ( ( K P L ) ` A ) = ( A o. ( 1st ` F ) ) ) $=
        ( va c1st ccom co cvv wcel cv cfv cfunc wa natrcl simpld simprd prcof2a
        syl wceq simpr coeq1d fvexd coexd fvmptd ) AOBOUAZGPUBZQBUQQHIJRZHIDRSA
        CDEFGHIJOKAHCFUCRZTZIUSTZABURTUTVAUDLBCFHIJKUEUIZUFAUTVAVBUGMNUHAUPBUJZ
        UDUPBUQAVCUKULLABUQURSLAGPUMUNUO $.
    $}

    prcof22a.b $e |- B = ( Base ` C ) $.
    prcof22a.x $e |- ( ph -> X e. B ) $.
    prcof22a.f $e |- ( ph -> F e. ( C Func D ) ) $.
    $( The morphism part of the pre-composition functor.  (Contributed by Zhi
       Wang, 3-Nov-2025.) $)
    prcof22a $p |- ( ph -> ( ( ( K P L ) ` A ) ` X )
                           = ( A ` ( ( 1st ` F ) ` X ) ) ) $=
      ( co cfv c1st ccom prcof21a fveq1d cbs c2nd eqid func1st2nd funcf1 fvco3d
      cfunc eqtrd ) ALBIJFSTZTLBHUATZUBZTLUNTBTALUMUOABEFDEUKSGHIJKMNORUCUDACEU
      ETZLBUNACUPDEUNHUFTPUPUGADEHRUHUIQUJUL $.
  $}

  ${
    $d B f x y $.  $d C f x y $.  $d D f x y $.  $d E f x y $.  $d F f x y $.
    $d G f x y $.  $d L f x y $.  $d M f x y $.  $d X f x y $.  $d f ph x y $.
    prcofdiag.l $e |- L = ( C DiagFunc D ) $.
    prcofdiag.m $e |- M = ( C DiagFunc E ) $.
    prcofdiag.f $e |- ( ph -> F e. ( E Func D ) ) $.
    prcofdiag.c $e |- ( ph -> C e. Cat ) $.
    ${
      prcofdiag1.b $e |- B = ( Base ` C ) $.
      prcofdiag1.x $e |- ( ph -> X e. B ) $.
      $( A constant functor pre-composed by a functor is another constant
         functor.  (Contributed by Zhi Wang, 25-Nov-2025.) $)
      prcofdiag1 $p |- ( ph ->
              ( ( ( 1st ` L ) ` X ) o.func F ) = ( ( 1st ` M ) ` X ) ) $=
        ( cfv co eqid wcel adantr vx vy c1st ccofu c2nd cop func1st2nd funcrcl3
        vf cbs diag1cl cofucl funcf1 ffnd funcrcl2 cv wa ccat ffvelcdmda diag11
        cfunc simpr cofu1 3eqtr4d eqfnfvd funcfn2 chom wbr simprl simprr funcf2
        ccid ad2antrr ffvelcdmd diag12 eqfnovd opeq12d wrel wceq relfunc 1st2nd
        cofu2 sylancr ) AIGUCPPZFUDQZUCPZWEUEPZUFZIHUCPPZUCPZWIUEPZUFZWEWIAWFWJ
        WGWKAUAEUJPZWFWJAWMBWFAWMBECWFWGWMRZNAECWEAEDCFWDLABCDWDGIJMAEDFUCPZFUE
        PZAEDFLUGZUHZNOWDRZUKZULZUGZUMUNAWMBWJAWMBECWJWKWNNAECWIABCEWIHIKMAEDWO
        WPWQUOZNOWIRZUKZUGZUMUNAUAUPZWMSZUQZXGWOPZWDUCPPIXGWFPZXGWJPZXIBDUJPZCD
        WDGIXJJACURSZXHMTZADURSZXHWRTNAIBSZXHOTZWSXMRZAWMXMXGWOAWMXMEDWOWPWNXSW
        QUMUSUTXIWMEDCFWDXGWNAFEDVAQZSZXHLTAWDDCVAQSZXHWTTAXHVBZVCXIBWMCEWIHIXG
        KXOAEURSZXHXCTNXRXDWNYCUTVDVEAUAUBWMWMWGWKAWMECWFWGWNXBVFAWMECWJWKWNXFV
        FAXHUBUPZWMSZUQZUQZUIXGYEEVGPZQZXGYEWGQZXGYEWKQZYHYJXKYEWFPCVGPZQYKYHWM
        ECWFWGYIYMXGYEWNYIRZYMRZAWFWGECVAQZVHYGXBTAXHYFVIZAXHYFVJZVKUNYHYJXLYEW
        JPYMQYLYHWMECWJWKYIYMXGYEWNYNYOAWJWKYPVHYGXFTYQYRVKUNYHUIUPZYJSZUQZYSXG
        YEWPQZPZXJYEWOPZWDUEPQPICVLPZPYSYKPYSYLPUUABXMCDUUEUUCDVGPZWDGIXJUUDJAX
        NYGYTMVMZAXPYGYTWRVMNAXQYGYTOVMZWSXSUUAWMXMXGWOUUAWMXMEDWOWPWNXSAWOWPXT
        VHYGYTWQVMZUMZYHXHYTYQTZVNUUFRZUUERZUUAWMXMYEWOUUJYHYFYTYRTZVNUUAYJXJUU
        DUUFQYSUUBUUAWMEDWOWPYIUUFXGYEWNYNUULUUIUUKUUNVKYHYTVBZVNVOUUAWMEDYSCFW
        DYIXGYEWNAYAYGYTLVMAYBYGYTWTVMUUKUUNYNUUOWBUUABWMCEUUEYSYIWIHIXGYEKUUGA
        YDYGYTXCVMNUUHXDWNUUKYNUUMUUNUUOVOVDVEVPVQAYPVRZWEYPSWEWHVSECVTZXAWEYPW
        AWCAUUPWIYPSWIWLVSUUQXEWIYPWAWCVD $.
    $}

    prcofdiag.g $e |- ( ph -> ( <. D , C >. -o.F F ) = G ) $.
    $( A diagonal functor post-composed by a pre-composition functor is another
       diagonal functor.  (Contributed by Zhi Wang, 25-Nov-2025.) $)
    prcofdiag $p |- ( ph -> ( G o.func L ) = M ) $=
      ( co c1st cfv c2nd eqid wcel adantr vx vy vf cop cfuc func1st2nd funcrcl3
      ccofu diagcl cprcof cfunc prcoffunca eqeltrrd cofucl funcf1 ffnd funcrcl2
      cbs cv wa simpr ccat diag1cl wceq fveq2d prcof1 prcofdiag1 3eqtrd eqfnfvd
      cofu1 funcfn2 chom wbr simprl simprr funcf2 csn cxp wf ad2antrr xpco2 syl
      ccom cofu2 diag2 cnat diag2cl 3eqtr4d eqfnovd opeq12d wrel relfunc 1st2nd
      prcof21a sylancr ) AFGUHNZOPZWPQPZUDZHOPZHQPZUDZWPHAWQWTWRXAAUABURPZWQWTA
      XCDBUENZURPZWQAXCXEBXDWQWRXCRZXERZABXDWPABCBUENZXDGFABCXHGILADCEOPZEQPZAD
      CEKUFZUGZXHRZUIZACBUDEUJNZFXHXDUKNZMADCXHXDBEXMLXDRZKULUMZUNZUFZUOUPAXCXE
      WTAXCXEBXDWTXAXFXGABXDHABDXDHJLADCXIXJXKUQZXQUIZUFZUOUPAUAUSZXCSZUTZYDWQP
      ZYDGOPZPZFOPZPYIEUHNYDWTPZYFXCBXHXDGFYDXFAGBXHUKNSZYEXNTAFXPSZYEXRTAYEVAZ
      VJYFCBEYIYJYFXCBCYIGYDIABVBSZYELTZACVBSZYEXLTXFYNYIRVCAXOOPYJVDYEAXOFOMVE
      TVFYFXCBCDEGHYDIJAEDCUKNZSZYEKTYPXFYNVGVHVIAUAUBXCXCWRXAAXCBXDWQWRXFXTVKA
      XCBXDWTXAXFYCVKAYEUBUSZXCSZUTZUTZUCYDYTBVLPZNZYDYTWRNZYDYTXANZUUCUUEYGYTW
      QPXDVLPZNUUFUUCXCBXDWQWRUUDUUHYDYTXFUUDRZUUHRZAWQWRBXDUKNZVMUUBXTTAYEUUAV
      NZAYEUUAVOZVPUPUUCUUEYKYTWTPUUHNUUGUUCXCBXDWTXAUUDUUHYDYTXFUUIUUJAWTXAUUK
      VMUUBYCTUULUUMVPUPUUCUCUSZUUESZUTZCURPZUUNVQZVRZXIWCZDURPZUURVRZUUNUUFPZU
      UNUUGPUUPUVAUUQXIVSUUTUVBVDUUPUVAUUQDCXIXJUVARZUUQRZUUPDCEAYSUUBUUOKVTZUF
      UOUVAUUQUURXIWAWBUUPUVCUUNYDYTGQPNPZYIYTYHPZFQPZNZPUUSUVJPUUTUUPXCBXHUUNX
      DGFUUDYDYTXFAYLUUBUUOXNVTAYMUUBUUOXRVTUUCYEUUOUULTZUUCUUAUUOUUMTZUUIUUCUU
      OVAZWDUUPUVGUUSUVJUUPXCUUQBCUUNUUDGYDYTIXFUVEUUIAYOUUBUUOLVTZAYQUUBUUOXLV
      TZUVKUVLUVMWEVEUUPUUSCUVIYRBEYIUVHCBWFNZUVPRZUUPXCUUQBCUUNUUDGUVPYDYTIXFU
      VEUUIUVNUVOUVKUVLUVMUVQWGAXOQPUVIVDUUBUUOAXOFQMVEVTUVFWNVHUUPXCUVABDUUNUU
      DHYDYTJXFUVDUUIUVNADVBSUUBUUOYAVTUVKUVLUVMWEWHVIWIWJAUUKWKZWPUUKSWPWSVDBX
      DWLZXSWPUUKWMWOAUVRHUUKSHXBVDUVSYBHUUKWMWOWH $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Examples of categories
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  The category of categories
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    catcrcl.c $e |- C = ( CatCat ` U ) $.
    catcrcl.h $e |- H = ( Hom ` C ) $.
    catcrcl.f $e |- ( ph -> F e. ( X H Y ) ) $.
    $( Reverse closure for the category of categories (in a universe)
       (Contributed by Zhi Wang, 14-Nov-2025.) $)
    catcrcl $p |- ( ph -> U e. _V ) $=
      ( co wcel c0 wne cvv cop cfv wceq ccatc chom df-ov eleq2s wn fvprc eqtrid
      elfvne0 fveq2 cnx homid str0 3eqtr4g syl necon1ai 3syl ) ADFGEKZLEMNZCOLZ
      JUPDFGPZEQUODUREUFFGEUAUBUQEMUQUCZBMRZEMRUSBCSQMHCSUDUEUTBTQMTQEMBMTUGITU
      HTQUIUJUKULUMUN $.

    $d B x y $.  $d U x y $.  $d ph x y $.
    ${
      catcrcl2.b $e |- B = ( Base ` C ) $.
      $( Reverse closure for the category of categories (in a universe)
         (Contributed by Zhi Wang, 14-Nov-2025.) $)
      catcrcl2 $p |- ( ph -> ( X e. B /\ Y e. B ) ) $=
        ( vx vy cv cfunc co cmpo wcel wa catcrcl catchomfval oveqd eleqtrd eqid
        cvv elmpocl syl ) AEGHMNBBMONOPQZRZQZSGBSHBSTAEGHFQUKKAFUJGHAMNBCDFUFIL
        ACDEFGHIJKUAJUBUCUDMNBBUIGHUJEUJUEUGUH $.
    $}

    $( A morphism of the category of categories (in a universe) is a functor.
       See ~ df-catc for the definition of the category Cat, which consists of
       all categories in the universe ` u ` (i.e., " ` u ` -small categories",
       see Definition 3.44. of [Adamek] p. 39), with functors as the morphisms
       ( ~ catchom ).  (Contributed by Zhi Wang, 14-Nov-2025.) $)
    elcatchom $p |- ( ph -> F e. ( X Func Y ) ) $=
      ( co cfunc cbs cfv cvv eqid catcrcl wcel catcrcl2 simpld catchom eleqtrd
      simprd ) ADFGEKFGLKJABMNZBCEOFGHUDPZABCDEFGHIJQIAFUDRZGUDRZAUDBCDEFGHIJUE
      SZTAUFUGUHUCUAUB $.
  $}

  ${
    catcsect.c $e |- C = ( CatCat ` U ) $.
    catcsect.h $e |- H = ( Hom ` C ) $.
    catcsect.i $e |- I = ( idFunc ` X ) $.
    catcsect.s $e |- S = ( Sect ` C ) $.
    $( The property " ` F ` is a section of ` G ` " in a category of small
       categories (in a universe).  (Contributed by Zhi Wang, 14-Nov-2025.) $)
    catcsect $p |- ( F ( X S Y ) G <-> (
            ( F e. ( X H Y ) /\ G e. ( Y H X ) ) /\ ( G o.func F ) = I ) ) $=
      ( co wcel cfv wa eqid cvv syl wbr cop cco ccid wceq w3a ccofu ccat cbs id
      sectrcl sectrcl2 jca simpl catcrcl catccat catcrcl2 3adant3 simprl simprr
      issect pm5.21nii df-3an elcatchom catcco catcid eqeq12d pm5.32i 3bitri
      simpr ) DEHIBNUAZDHIFNOZEIHFNOZEDHIUBHAUCPZNNZHAUDPZPZUEZUFZVLVMQZVRQVTED
      UGNZGUEZQVKAUHOZHAUIPZOZIWDOZQZQZVSVKWCWGVKABDEHIMVKUJZUKVKWDABDEHIMWIWDR
      ZULUMVLVMWHVRVTWCWGVTCSOWCVTACDFHIJKVLVMUNZUOZACSJUPTVTWDACDFHIJKWKWJUQUM
      ZURWHWDABVNVPDEFHIWJKVNRZVPRZMWCWGUNWCWEWFUSZWCWEWFUTZVAVBVLVMVRVCVTVRWBV
      TVOWAVQGVTWDAVNCDESHIHJWJWLWNVTWHWEWMWPTZVTWHWFWMWQTWRVTACDFHIJKWKVDVTACE
      FIHJKVLVMVJVDVEVTWDACVPGSHJWJWOLWLWRVFVGVHVI $.
  $}

  ${
    catcinv.c $e |- C = ( CatCat ` U ) $.
    catcinv.n $e |- N = ( Inv ` C ) $.
    catcinv.h $e |- H = ( Hom ` C ) $.
    catcinv.i $e |- I = ( idFunc ` X ) $.
    catcinv.j $e |- J = ( idFunc ` Y ) $.
    $( The property " ` F ` is an inverse of ` G ` " in a category of small
       categories (in a universe).  (Contributed by Zhi Wang, 14-Nov-2025.) $)
    catcinv $p |- ( F ( X N Y ) G <-> ( ( F e. ( X H Y ) /\ G e. ( Y H X ) )
                   /\ ( ( G o.func F ) = I /\ ( F o.func G ) = J ) ) ) $=
      ( co wbr wa wcel ccofu csect cfv wceq eqid catcsect bianbi anbi12i isinv2
      ancom anandi 3bitr4i ) CDIJAUAUBZPQZDCJIULPQZRCIJEPSZDJIEPSZRZDCTPFUCZRZU
      QCDTPGUCZRZRCDIJHPQUQURUTRRUMUSUNVAAULBCDEFIJKMNULUDZUEUNUPUORUTUQAULBDCE
      GJIKMOVBUEUPUOUIUFUGAULCDHIJLVBUHUQURUTUJUK $.
  $}

  ${
    catcisoi.c $e |- C = ( CatCat ` U ) $.
    catcisoi.r $e |- R = ( Base ` X ) $.
    catcisoi.s $e |- S = ( Base ` Y ) $.
    catcisoi.i $e |- I = ( Iso ` C ) $.
    catcisoi.f $e |- ( ph -> F e. ( X I Y ) ) $.
    $( A functor is an isomorphism of categories only if it is full and
       faithful, and is a bijection on the objects.  Remark 3.28(2) in [Adamek]
       p. 34.  (Contributed by Zhi Wang, 17-Nov-2025.) $)
    catcisoi $p |- ( ph -> ( F e. ( ( X Full Y ) i^i ( X Faith Y ) ) /\
                             ( 1st ` F ) : R -1-1-onto-> S ) ) $=
      ( co wcel cful cfth cfv cvv cin c1st wf1o cbs eqid isorcl2 simpld elbasfv
      wa ccatc syl simprd catciso mpbid ) AFHIGOPFHIQOHIROUAPCDFUBSUCUINABUDSZB
      CDEFGTHIJUOUEZKLAHUOPZETPAUQIUOPZAUOBFGHIMNUPUFZUGZUOBUJHEJUPUHUKUTAUQURU
      SULMUMUN $.
  $}

  ${
    $d B l $.  $d C l $.  $d D l $.  $d E l $.  $d F l $.  $d G l $.  $d I l $.
    $d K l $.  $d S l $.  $d Q l $.  $d U l $.  $d X l $.  $d Y l $.
    $d l ph $.
    uobeq2.b $e |- B = ( Base ` D ) $.
    uobeq2.x $e |- ( ph -> X e. B ) $.
    uobeq2.f $e |- ( ph -> F e. ( C Func D ) ) $.
    uobeq2.g $e |- ( ph -> ( K o.func F ) = G ) $.
    uobeq2.y $e |- ( ph -> ( ( 1st ` K ) ` X ) = Y ) $.
    uobeq2.q $e |- Q = ( CatCat ` U ) $.
    ${
      uobeq2.s $e |- S = ( Sect ` Q ) $.
      uobeq2.k $e |- ( ph -> K e. ( D Full E ) ) $.
      uobeq2.1 $e |- ( ph -> K e. dom ( D S E ) ) $.
      $( If a full functor (in fact, a full embedding) is a section, then the
         sets of universal objects are equal.  (Contributed by Zhi Wang,
         17-Nov-2025.) $)
      uobeq2 $p |- ( ph -> dom ( F ( C UP D ) X ) = dom ( G ( C UP E ) Y ) ) $=
        ( vl cv co wbr cup cdm wceq wex eldmg ibi syl wa cidfu cfv adantr cfunc
        wcel ccofu c1st eqid cful chom catcsect simprbi adantl simprd elcatchom
        simplbi uobeq exlimddv ) AKUCUDZDHFUEZUFZILCDUGUEUEUHJMCHUGUEUEUHUIUCAK
        VNUHZUSZVOUCUJZUBVQVRUCKVNVPUKULUMAVOUNBCDHIJDUOUPZKVMLMNALBUSVOOUQAICD
        URUEUSVOPUQAKIUTUEJUIVOQUQALKVAUPUPMUIVORUQVSVBZAKDHVCUEUSVOUAUQVOVMKUT
        UEVSUIZAVOKDHEVDUPZUEUSZVMHDWBUEUSZUNZWAEFGKVMWBVSDHSWBVBZVTTVEZVFVGVOV
        MHDURUEUSAVOEGVMWBHDSWFVOWCWDVOWEWAWGVJVHVIVGVKVL $.
    $}

    uobeq3.i $e |- I = ( Iso ` Q ) $.
    uobeq3.1 $e |- ( ph -> K e. ( D I E ) ) $.
    $( An isomorphism between categories generates equal sets of universal
       objects.  (Contributed by Zhi Wang, 17-Nov-2025.) $)
    uobeq3 $p |- ( ph -> dom ( F ( C UP D ) X ) = dom ( G ( C UP E ) Y ) ) $=
      ( cful co cfth cin wcel cbs cfv c1st wf1o eqid catcisoi simpld uobffth )
      ABCDGHIKLMNOPQRAKDGUBUCDGUDUCUEUFBGUGUHZKUIUHUJAEBUOFKJDGSNUOUKTUAULUMUN
      $.
  $}

  ${
    $d N x y $.  $d X x y $.  $d ph x y $.
    opf11.f $e |- ( ph -> F = ( oppFunc |` ( C Func D ) ) ) $.
    opf11.x $e |- ( ph -> X e. ( C Func D ) ) $.
    $( The object part of the op functor on functor categories.  Lemma for
       ~ fucoppc .  (Contributed by Zhi Wang, 18-Nov-2025.) $)
    opf11 $p |- ( ph -> ( 1st ` ( F ` X ) ) = ( 1st ` X ) ) $=
      ( cfv c1st c2nd ctpos cop wceq coppf cfunc co cres fveq1d syl fvex fvresd
      wcel oppfval2 3eqtrd tposex op1std ) AEDHZEIHZEJHZKZLZMUGIHUHMAUGENBCOPZQ
      ZHENHZUKAEDUMFRAEULNGUAAEULUBUNUKMGBCEUCSUDUHUJUGEITUIEJTUEUFS $.

    $( The object part of the op functor on functor categories.  Lemma for
       ~ oppfdiag .  (Contributed by Zhi Wang, 19-Nov-2025.) $)
    opf12 $p |- ( ph -> ( M ( 2nd ` ( F ` X ) ) N )
                              = ( N ( 2nd ` X ) M ) ) $=
      ( cfv c2nd co ctpos c1st cop wceq coppf cfunc syl fvex cres fveq1d fvresd
      wcel oppfval2 3eqtrd tposex op2ndd oveqd ovtpos eqtrdi ) AEFGDJZKJZLEFGKJ
      ZMZLFEUNLAUMUOEFAULGNJZUOOZPUMUOPAULGQBCRLZUAZJGQJZUQAGDUSHUBAGURQIUCAGUR
      UDUTUQPIBCGUESUFUPUOULGNTUNGKTUGUHSUIEFUNUJUK $.
  $}

  ${
    $d N x y $.  $d X x y $.  $d Y x y $.  $d ph x y $.
    opf2fval.f $e |- ( ph -> F = ( x e. A , y e. B |->
                ( _I |` ( y N x ) ) ) ) $.
    opf2fval.x $e |- ( ph -> X e. A ) $.
    opf2fval.y $e |- ( ph -> Y e. B ) $.
    $( The morphism part of the op functor on functor categories.  Lemma for
       ~ fucoppc .  (Contributed by Zhi Wang, 18-Nov-2025.) $)
    opf2fval $p |- ( ph -> ( X F Y ) = ( _I |` ( Y N X ) ) ) $=
      ( cid cv co cres cvv wceq wa wcel simprr simprl oveq12d reseq2d ovexd syl
      resiexg ovmpod ) ABCHIDEMCNZBNZGOZPMIHGOZPZFQJAUJHRZUIIRZSSZUKULMUPUIIUJH
      GAUNUOUAAUNUOUBUCUDKLAULQTUMQTAIHGUEULQUGUFUH $.

    opf2.c $e |- ( ph -> C = D ) $.
    opf2.d $e |- ( ph -> D e. ( Y N X ) ) $.
    $( The morphism part of the op functor on functor categories.  Lemma for
       ~ fucoppc .  (Contributed by Zhi Wang, 18-Nov-2025.) $)
    opf2 $p |- ( ph -> ( ( X F Y ) ` C ) = D ) $=
      ( co cfv cid cres opf2fval fveq12d wcel wceq fvresi syl eqtrd ) AFJKHQZRG
      SKJIQZTZRZGAFGUHUJABCDEHIJKLMNUAOUBAGUIUCUKGUDPUIGUEUFUG $.
  $}

  ${
    fucoppclem.o $e |- O = ( oppCat ` C ) $.
    fucoppclem.p $e |- P = ( oppCat ` D ) $.
    fucoppclem.n $e |- N = ( C Nat D ) $.
    fucoppclem.f $e |- ( ph -> F = ( oppFunc |` ( C Func D ) ) ) $.
    fucoppclem.x $e |- ( ph -> X e. ( C Func D ) ) $.
    fucoppclem.y $e |- ( ph -> Y e. ( C Func D ) ) $.
    $( Lemma for ~ fucoppc .  (Contributed by Zhi Wang, 18-Nov-2025.) $)
    fucoppclem $p |- ( ph ->
            ( Y N X ) = ( ( F ` X ) ( O Nat P ) ( F ` Y ) ) ) $=
      ( cfv co ccat coppf fveq1d cnat eqid cfunc cres fvresd c1st c2nd funcrcl2
      eqtrd func1st2nd funcrcl3 natoppfb ) ABCDIHIEPZHEPZGDUAQZFGRRJKLUOUBAUMIS
      BCUCQZUDZPISPAIEUQMTAIUPSOUEUIAUNHUQPHSPAHEUQMTAHUPSNUEUIABCHUFPZHUGPZABC
      HNUJZUHABCURUSUTUKUL $.
  $}

  ${
    fucoppc.o $e |- O = ( oppCat ` C ) $.
    fucoppc.p $e |- P = ( oppCat ` D ) $.
    fucoppc.q $e |- Q = ( C FuncCat D ) $.
    fucoppc.r $e |- R = ( oppCat ` Q ) $.
    fucoppc.s $e |- S = ( O FuncCat P ) $.
    fucoppc.n $e |- N = ( C Nat D ) $.
    fucoppc.f $e |- ( ph -> F = ( oppFunc |` ( C Func D ) ) ) $.
    fucoppc.g $e |- ( ph -> G = ( x e. ( C Func D ) , y e. ( C Func D )
             |-> ( _I |` ( y N x ) ) ) ) $.
    ${
      $d N x y $.  $d X x y $.  $d ph x y $.
      fucoppcid.x $e |- ( ph -> X e. ( C Func D ) ) $.
      $( The opposite category of functors is compatible with the category of
         opposite functors in terms of identity morphism.  (Contributed by Zhi
         Wang, 18-Nov-2025.) $)
      fucoppcid $p |- ( ph -> ( ( X G X ) ` ( ( Id ` R ) ` X ) )
                         = ( ( Id ` S ) ` ( F ` X ) ) ) $=
        ( ccid c1st ccom co ccat wcel wceq c2nd func1st2nd funcrcl3 eqid oppcid
        cfv syl opf11 coeq12d cfunc wf coppf cres wf1 oppff1 ax-mp feq1d mpbiri
        f1f ffvelcdmd fucid funcrcl2 fuccat fveq1d eqtrd fucidcl opf2 3eqtr4rd
        ) AFUDUPZNJUPZUEUPZUFEUDUPZNUEUPZUFZVTIUDUPZUPNHUDUPZUPZNNKUGUPAVSWBWAW
        CAEUHUIVSWBUJADEWCNUKUPZADENUCULZUMZWBEFPWBUNZUOUQADEJNUAUCURUSAMFIVSVT
        WESWEUNVSUNADEUTUGZMFUTUGZNJAWLWMJVAWLWMVBWLVCZVAZWLWMWNVDWODEFMOPVEWLW
        MWNVIVFAWLWMJWNUAVGVHUCVJVKABCWLWLWGWDKLNNUBUCUCAWGNGUDUPZUPWDANWFWPAGU
        HUIWFWPUJADEGQADEWCWHWIVLWJVMWPGHRWPUNZUOUQVNADEGWBNWPQWQWKUCVKVOADEGWB
        NLQTWKUCVPVQVR $.
    $}

    ${
      $d A z $.  $d B z $.  $d C z $.  $d D z $.  $d F z $.  $d N x y $.
      $d O z $.  $d P z $.  $d X x y $.  $d X z $.  $d Y x y $.  $d Y z $.
      $d Z x y $.  $d Z z $.  $d ph x y $.  $d ph z $.
      fucoppcco.a $e |- ( ph -> A e. ( X ( Hom ` R ) Y ) ) $.
      fucoppcco.b $e |- ( ph -> B e. ( Y ( Hom ` R ) Z ) ) $.
      $( The opposite category of functors is compatible with the category of
         opposite functors in terms of composition.  (Contributed by Zhi Wang,
         18-Nov-2025.) $)
      fucoppcco $p |- ( ph -> ( ( X G Z )
          ` ( B ( <. X , Y >. ( comp ` R ) Z ) A ) )
        = ( ( ( Y G Z ) ` B )
            ( <. ( F ` X ) , ( F ` Y ) >. ( comp ` S ) ( F ` Z ) )
            ( ( X G Y ) ` A ) ) ) $=
        ( vz cfv cop cco co cbs c1st cmpt cnat eqid oppcbas chom fuchom oppchom
        cv eleqtrdi cfunc wcel wa natrcl simprd simpld fucoppclem eleqtrd fucco
        syl eqidd opf2 oveq12d fucbas oppcco fuccocl opf11 fveq1d opeq12d oveqd
        wceq adantr c2nd func1st2nd ffvelcdmda eqtrd mpteq2dva 3eqtr4d 3eqtr4rd
        funcf1 ) AEDPLUJZQLUJZUKRLUJZKULUJZUMZUMUIFUNUJZUIVCZEUJZXADUJZXAWOUOUJ
        ZUJZXAWPUOUJZUJZUKZXAWQUOUJZUJZHULUJZUMZUMZUPZEQRMUMUJZDPQMUMUJZWSUMEDP
        QUKRJULUJUMUMZPRMUMUJZAUIWTOHKDEWRXKWOWPWQOHUQUMZUCXSURWTFOSWTURZUSXKUR
        WRURADQPNUMZWOWPXSUMADPQJUTUJZUMYAUGINJPQFGINUAUDVAZUBVBVDZAFGHLNOPQSTU
        DUEAQFGVEUMZVFZPYEVFZADYAVFYFYGVGYDDFGQPNUDVHVNZVIZAYFYGYHVJZVKVLAERQNU
        MZWPWQXSUMAEQRYBUMYKUHINJQRYCUBVBVDZAFGHLNOQRSTUDUEYJARYEVFZYFAEYKVFYMY
        FVGYLEFGRQNUDVHVNVJZVKVLVMAXOEXPDWSABCYEYEEEMNQRUFYJYNAEVOYLVPABCYEYEDD
        MNPQUFYIYJADVOYDVPVQADERQUKPIULUJZUMUMZUIWTXCXBXARUOUJZUJZXAQUOUJZUJZUK
        XAPUOUJZUJZGULUJZUMUMZUPXRXNAUIWTFGIEDYOUUCRQPNUAUDXTUUCURZYOURZYLYDVMA
        BCYEYEXQYPMNPRUFYIYNAYEIYODEJPQRFGIUAVRUUFUBYIYJYNVSAFGIEDYORQPNUAUDUUF
        YLYDVTVPAUIWTXMUUDAXAWTVFZVGZXMXBXCUUBYTUKZYRXKUMZUMZUUDAXMUUKWEUUGAXLU
        UJXBXCAXHUUIXJYRXKAXEUUBXGYTAXAXDUUAAFGLPUEYIWAWBAXAXFYSAFGLQUEYJWAWBWC
        AXAXIYQAFGLRUEYNWAWBVQWDWFUUHGUNUJZGUUCXCXBHUUBYTYRUULURZUUETAWTUULXAUU
        AAWTUULFGUUAPWGUJXTUUMAFGPYIWHWNWIAWTUULXAYSAWTUULFGYSQWGUJXTUUMAFGQYJW
        HWNWIAWTUULXAYQAWTUULFGYQRWGUJXTUUMAFGRYNWHWNWIVSWJWKWLWM $.
    $}

    ${
      $d B a b f g k $.  $d C a b f g k x y $.  $d D a b f g k x y $.
      $d F a b f g k $.  $d G a b f g k $.  $d N a b f g k x y $.
      $d O a b f g k $.  $d P a b f g k $.  $d Q a b f g k $.
      $d R a b f g k x y $.  $d S a b f g k $.  $d T a b f g k $.
      $d U a b f g k $.  $d V a b f g k $.  $d W a b f g k $.
      $d a b f g k ph x y $.
      fucoppc.t $e |- T = ( CatCat ` U ) $.
      fucoppc.b $e |- B = ( Base ` T ) $.
      fucoppc.i $e |- I = ( Iso ` T ) $.
      fucoppc.c $e |- ( ph -> C e. V ) $.
      fucoppc.d $e |- ( ph -> D e. W ) $.
      fucoppc.1 $e |- ( ph -> R e. B ) $.
      fucoppc.2 $e |- ( ph -> S e. B ) $.
      $( The isomorphism from the opposite category of functors to the category
         of opposite functors.  (Contributed by Zhi Wang, 18-Nov-2025.) $)
      fucoppc $p |- ( ph -> F ( R I S ) G ) $=
        ( vf vg vk va vb cop co wcel wbr cful cfth cin cfunc c1st cfv wf1o chom
        cv cnat wral cco ccid fucbas oppcbas eqid fuchom ccat cvv ccatc elbasfv
        syl catcbas eleqtrd elin2d wf coppf cres oppff1o f1oeq1d mpbird cxp wfn
        f1of cmpo ovex resiexg ax-mp fnmpoi fneq1d mpbiri wa f1oi adantr simprl
        cid simprr opf2fval oppchom fucoppclem eqcomd f1oeq123d simpr fucoppcid
        wceq a1i w3a 3ad2ant1 simp3l simp3r isfuncd ralrimivva isffth2 sylanbrc
        fucoppcco df-br sylib func1st catciso mpbir2and sylibr ) AMNUTZIJOVAZVB
        ZMNYPVCAYQYOIJVDVAIJVEVAVFZVBZEFVGVAZQGVGVAZYOVHVIZVJZAMNYRVCZYSAMNIJVG
        VAVCUOVLZUPVLZIVKVIZVAZUUEMVIUUFMVIQGVMVAZVAZUUEUUFNVAZVJZUPYTVNUOYTVNU
        UDAUOUPUQYTUUAIIVOVIZIVPVIZURUSJMNUUGJVPVIZUUIJVOVIZYTHIUCEFHUBVQVRZQGJ
        UDVQZUUGVSZQGJUUIUDUUIVSVTZUUNVSUUOVSUUMVSUUPVSALWAIAIDLWAVFZUMADKLWBUH
        UIAIDVBLWBVBUMDKWCILUHUIWDWEZWFZWGWHALWAJAJDUVAUNUVCWGWHAYTUUAMVJZYTUUA
        MWIAUVDYTUUAWJYTWKZVJAEFGQRSTUAUKULWLAYTUUAMUVEUFWMWNZYTUUAMWQWEANYTYTW
        OZWPBCYTYTXICVLZBVLZPVAZWKZWRZUVGWPBCYTYTUVKUVLUVLVSUVJWBVBUVKWBVBUVHUV
        IPWSUVJWBWTXAXBAUVGNUVLUGXCXDAUUEYTVBZUUFYTVBZXEZXEZUULUUHUUJUUKWIUVPUU
        LUUFUUEPVAZUVQXIUVQWKZVJUVQXFUVPUUHUVQUUJUVQUUKUVRUVPBCYTYTNPUUEUUFANUV
        LXRZUVOUGXGAUVMUVNXHZAUVMUVNXJZXKUUHUVQXRUVPHPIUUEUUFEFHPUBUEVTUCXLXSUV
        PUVQUUJUVPEFGMPQUUEUUFTUAUEAMUVEXRZUVOUFXGUVTUWAXMXNXOXDZUUHUUJUUKWQWEA
        UVMXEBCEFGHIJMNPQUUETUAUBUCUDUEAUWBUVMUFXGAUVSUVMUGXGAUVMXPXQAUVMUVNUQV
        LZYTVBXTZURVLZUUHVBZUSVLZUUFUWDUUGVAVBZXEZXTBCUWFUWHEFGHIJMNPQUUEUUFUWD
        TUAUBUCUDUEAUWEUWBUWJUFYAAUWEUVSUWJUGYAAUWEUWGUWIYBAUWEUWGUWIYCYHYDZAUU
        LUOUPYTYTUWCYEUOUPYTIJMNUUGUUIUUQUUSUUTYFYGMNYRYIYJAUUCUVDUVFAYTUUAUUBM
        AIJMNUWKYKWMWNADKYTUUALYOOWBIJUHUIUUQUURUVBUMUNUJYLYMMNYPYIYN $.
    $}

    $d C x y $.  $d D x y $.  $d N x y $.  $d R x y $.  $d ph x y $.
    fucoppcffth.c $e |- ( ph -> C e. Cat ) $.
    fucoppcffth.d $e |- ( ph -> D e. Cat ) $.
    $( A fully faithful functor from the opposite category of functors to the
       category of opposite functors.  (Contributed by Zhi Wang,
       19-Nov-2025.) $)
    fucoppcffth $p |- ( ph -> F ( ( R Full S ) i^i ( R Faith S ) ) G ) $=
      ( cop cful cfth cin wcel wbr cbs cfv c1st wf1o cpr ccatc ciso eqid fuccat
      co ccat oppccat syl prid1g elind cvv prex catcbas eleqtrrd prid2g fucoppc
      a1i df-br sylib catcisoi simpld sylibr ) AJKUDZHIUEUSHIUFUSUGZUHZJKVRUIAV
      SHUJUKZIUJUKZVQULUKUMAHIUNZUOUKZVTWAWBVQWCUPUKZHIWCUQZVTUQWAUQWDUQZAJKHIW
      DUSZUIVQWGUHABCWCUJUKZDEFGHIWCWBJKWDLMUTUTNOPQRSTUAWEWHUQZWFUBUCAHWBUTUGZ
      WHAWBUTHAHUTUHZHWBUHAGUTUHWKADEGPUBUCURGHQVAVBZHIUTVCVBWLVDAWHWCWBVEWEWIW
      BVEUHAHIVFVKVGZVHAIWJWHAWBUTIAIUTUHIWBUHAMFIRADUTUHMUTUHUBDMNVAVBAEUTUHFU
      TUHUCEFOVAVBURZHIUTVIVBWNVDWMVHVJJKWGVLVMVNVOJKVRVLVP $.

    $( A functor from the opposite category of functors to the category of
       opposite functors.  (Contributed by Zhi Wang, 19-Nov-2025.) $)
    fucoppcfunc $p |- ( ph -> F ( R Func S ) G ) $=
      ( cful co cfth cin wbr cfunc fucoppcffth inss1 fullfunc sstri ssbri syl )
      AJKHIUDUEZHIUFUEZUGZUHJKHIUIUEZUHABCDEFGHIJKLMNOPQRSTUAUBUCUJURUSJKURUPUS
      UPUQUKHIULUMUNUO $.
  $}

  ${
    $d D f g $.  $d E f g $.  $d X f g $.  $d f g ph $.
    fucoppccic.c $e |- C = ( CatCat ` U ) $.
    fucoppccic.b $e |- B = ( Base ` C ) $.
    fucoppccic.x $e |- X = ( oppCat ` ( D FuncCat E ) ) $.
    fucoppccic.y $e |- Y = ( ( oppCat ` D ) FuncCat ( oppCat ` E ) ) $.
    fucoppccic.xb $e |- ( ph -> X e. B ) $.
    fucoppccic.yb $e |- ( ph -> Y e. B ) $.
    fucoppccic.d $e |- ( ph -> D e. V ) $.
    fucoppccic.e $e |- ( ph -> E e. W ) $.
    $( The opposite category of functors is isomorphic to the category of
       opposite functors.  (Contributed by Zhi Wang, 18-Nov-2025.) $)
    fucoppccic $p |- ( ph -> X ( ~=c ` C ) Y ) $=
      ( co eqid vf vg coppf cfunc cres cid cnat cmpo cop ciso cfv wcel cvv ccat
      cv ccatc elbasfv catccat 3syl coppc cfuc eqidd fucoppc df-br sylib brcici
      wbr ) ABCUCDFUDSZUEZUAUBVHVHUFUBUOUAUODFUGSZSUEUHZUIZCUJUKZIJVMTZLAIBULEU
      MULCUNULOBCUPIEKLUQCEUMKURUSOPAVIVKIJVMSZVGVLVOULAUAUBBDFFUTUKZDFVASZIJCE
      VIVKVMVJDUTUKZGHVRTVPTVQTMNVJTAVIVBAVKVBKLVNQROPVCVIVKVOVDVEVF $.
  $}

  ${
    $d A f y z $.  $d C f m n x y z $.  $d D f m n x y z $.  $d F f x y z $.
    $d G f x y z $.  $d L f m n x y z $.  $d N f m n x y z $.  $d O f x y z $.
    $d P f x y z $.  $d X f y z $.  $d f m n ph x y z $.
    oppfdiag.o $e |- O = ( oppCat ` C ) $.
    oppfdiag.p $e |- P = ( oppCat ` D ) $.
    oppfdiag.l $e |- L = ( C DiagFunc D ) $.
    oppfdiag.c $e |- ( ph -> C e. Cat ) $.
    oppfdiag.d $e |- ( ph -> D e. Cat ) $.
    ${
      oppfdiag1.f $e |- ( ph -> F = ( oppFunc |` ( D Func C ) ) ) $.
      oppfdiag1.a $e |- A = ( Base ` C ) $.
      oppfdiag1.x $e |- ( ph -> X e. A ) $.
      $( A constant functor for opposite categories is the opposite functor of
         the constant functor for original categories.  (Contributed by Zhi
         Wang, 19-Nov-2025.) $)
      oppfdiag1 $p |- ( ph -> ( F ` ( ( 1st ` L ) ` X ) )
             = ( ( 1st ` ( O DiagFunc P ) ) ` X ) ) $=
        ( cfv co eqid vy vm vn vz vf c1st c2nd cop cdiag cfuc fucbas func1st2nd
        cfunc diagcl funcf1 ffvelcdmd opf11 cbs oppcbas cv cnat cres cmpo coppf
        cid ccofu coppc oppfoppc2 wbr eqidd fucoppcfunc df-br sylib cofu1 oppf1
        wcel func1st fveq1d fveq12d eqtrd cofucl eqeltrrd ffnd ccat oppccat syl
        feq1dd wa adantr simpr diag11 eqtr4d eqfnfvd funcfn2 wceq opf12 oppchom
        chom a1i simprl simprr funcf2 feq2dd oppcid ad2antrr eleqtrrdi 3eqtr4rd
        ccid diag12 eqfnovd opeq12d wrel relfunc 1st2nd sylancr 3eqtr4d ) AIGUF
        RZRZFRZUFRZXSUGRZUHZIHEUISZUFRZRZUFRZYEUGRZUHZXSYEAXTYFYAYGAXTXRUFRZYFA
        DCFXROABDCUMSZIXQABYJCDCUJSZXQGUGRPDCYKYKTZUKACYKGACDYKGLMNYLUNZULUOQUP
        ZUQZAUADURRZYIYFAYPBYIAYPBXTYIYOAYPBEHXTYAYPDEKYPTZUSZBCHJPUSZAEHXSAIFU
        BUCYJYJVEUCUTUBUTDCVASZSVBVCZUHZGVDRZVFSZUFRZRZXSEHUMSZAUUFIUUCUFRZRZUU
        BUFRZRXSABHYKVGRZEHUJSZUUCUUBIYSACYKUUKGHJUUKTZYMVHZAFUUAUUKUULUMSZVIUU
        BUUOVPAUBUCDCHYKUUKUULFUUAYTEKJYLUUMUULTZYTTOAUUAVJNMVKZFUUAUUOVLVMZQVN
        AUUIXRUUJFAUUKUULFUUAUUQVQAIUUHXQACYKGYMVOVRVSVTABUUGIUUEABUUGHUULUUEUU
        DUGRYSEHUULUUPUKZAHUULUUDAHUUKUULUUCUUBUUNUURWAULUOQUPWBZULZUOWGWCAYPBY
        FAYPBEHYFYGYRYSAEHYEABUUGIYDABUUGHUULYDYCUGRYSUUSAHUULYCAHEUULYCYCTZACW
        DVPZHWDVPZMCHJWEZWFZADWDVPZEWDVPZNDEKWEZWFZUUPUNULUOQUPZULZUOWCAUAUTZYP
        VPZWHZUVMYIRIUVMYFRZUVOBYPCDXRGIUVMLAUVCUVNMWIAUVGUVNNWIPAIBVPZUVNQWIZX
        RTZYQAUVNWJZWKUVOBYPHEYEYCIUVMUVBAUVDUVNUVFWIAUVHUVNUVJWIYSUVRYETZYRUVT
        WKWLWMVTAUAUDYPYPYAYGAYPEHXTYAYRUVAWNAYPEHYFYGYRUVLWNAUVNUDUTZYPVPZWHZW
        HZUVMUWBYASZUWBUVMXRUGRSZUVMUWBYGSZAUWFUWGWOUWDADCFUVMUWBXROYNWPWIZUWEU
        EUWBUVMDWRRZSZUWGUWHUWEUWKUVMXTRUWBXTRHWRRZSZUWGUWEUWKUWMUWFUWGUWIUWEUV
        MUWBEWRRZSZUWKUWMUWFUWOUWKWOUWEDUWJEUVMUWBUWJTZKWQZWSZUWEYPEHXTYAUWNUWL
        UVMUWBYRUWNTZUWLTZAXTYAUUGVIUWDUVAWIAUVNUWCWTZAUVNUWCXAZXBXCWGWCUWEUWKU
        VPUWBYFRUWLSZUWHUWEUWOUWKUXCUWHUWRUWEYPEHYFYGUWNUWLUVMUWBYRUWSUWTAYFYGU
        UGVIUWDUVLWIUXAUXBXBXCWCUWEUEUTZUWKVPZWHZIHXHRZRZICXHRZRZUXDUWHRUXDUWGR
        AUXHUXJWOUWDUXEAIUXGUXIAUVCUXGUXIWOMUXICHJUXITZXDWFVRXEUXFBYPHEUXGUXDUW
        NYEYCIUVMUWBUVBUXFUVCUVDAUVCUWDUXEMXEZUVEWFUXFUVGUVHAUVGUWDUXENXEZUVIWF
        YSAUVQUWDUXEQXEZUWAYRUWEUVNUXEUXAWIZUWSUXGTUWEUWCUXEUXBWIZUXFUXDUWKUWOU
        WEUXEWJZUWQXFXIUXFBYPCDUXIUXDUWJXRGIUWBUVMLUXLUXMPUXNUVSYQUXPUWPUXKUXOU
        XQXIXGWMVTXJXKAUUGXLZXSUUGVPXSYBWOEHXMZUUTXSUUGXNXOAUXRYEUUGVPYEYHWOUXS
        UVKYEUUGXNXOXP $.
    $}

    ${
      oppfdiag1a.a $e |- A = ( Base ` C ) $.
      oppfdiag1a.x $e |- ( ph -> X e. A ) $.
      $( A constant functor for opposite categories is the opposite functor of
         the constant functor for original categories.  (Contributed by Zhi
         Wang, 19-Nov-2025.) $)
      oppfdiag1a $p |- ( ph -> ( oppFunc ` ( ( 1st ` L ) ` X ) )
             = ( ( 1st ` ( O DiagFunc P ) ) ` X ) ) $=
        ( c1st cfv coppf cfunc co cres cdiag eqid fvresd eqidd oppfdiag1 eqtr3d
        diag1cl ) AHFPQQZRDCSTZUAZQUIRQHGEUBTPQQAUIUJRABCDUIFHKLMNOUIUCUHUDABCD
        EUKFGHIJKLMAUKUENOUFUG $.
    $}

    oppfdiag.f $e |- ( ph -> F = ( oppFunc |` ( D Func C ) ) ) $.
    oppfdiag.n $e |- N = ( D Nat C ) $.
    oppfdiag.g $e |- ( ph -> G = ( m e. ( D Func C ) , n e. ( D Func C )
        |-> ( _I |` ( n N m ) ) ) ) $.
    $( A diagonal functor for opposite categories is the opposite functor of
       the diagonal functor for original categories post-composed by an
       isomorphism ( ~ fucoppc ).  (Contributed by Zhi Wang, 19-Nov-2025.) $)
    oppfdiag $p |- ( ph -> ( <. F , G >. o.func ( oppFunc ` L ) )
                           = ( O DiagFunc P ) ) $=
      ( cfv vx vy vf cop coppf ccofu co c1st c2nd cdiag cfunc cfuc eqid oppcbas
      cbs fucbas coppc diagcl oppfoppc2 wbr wcel fucoppcfunc df-br sylib cofucl
      func1st2nd funcf1 ffnd ccat oppccat cv wa adantr simpr cofu1 wceq func1st
      syl oppf1 fveq1d fveq12d cres oppfdiag1 eqfnfvd funcfn2 chom cnat oppchom
      3eqtrd a1i fuchom simprl simprr funcf2 csn cxp ad2antrr eleqtrrdi func2nd
      feq2dd cofu2 oveq123d oppf2 cid cmpo diag1cl diag2 diag2cl eqtr4d eqfnovd
      opf2 opeq12d wrel relfunc 1st2nd sylancr 3eqtr4d ) AGHUDZIUETZUFUGZUHTZXT
      UITZUDZKDUJUGZUHTZYDUITZUDZXTYDAYAYEYBYFAUABUOTZYAYEAYHDKUKUGZYAAYHYIKDKU
      LUGZYAYBYHBKLYHUMZUNZDKYJYJUMZUPZAKYJXTAKCBULUGZUQTZYJXSXRABYOYPIKLYPUMZA
      BCYOINOPYOUMZURZUSZAGHYPYJUKUGZUTXRUUAVAZAEFCBKYOYPYJGHJDMLYRYQYMRQSPOVBZ
      GHUUAVCVDZVEZVFZVGVHAYHYIYEAYHYIKYJYEYFYLYNAKYJYDAKDYJYDYDUMZABVIVAZKVIVA
      ZOBKLVJZVRACVIVAZDVIVAZPCDMVJZVRYMURZVFZVGVHAUAVKZYHVAZVLZUUPYATZUUPXSUHT
      ZTZXRUHTZTZUUPIUHTZTZGTZUUPYETZUURYHKYPYJXSXRUUPYLAXSKYPUKUGVAZUUQYTVMAUU
      BUUQUUDVMAUUQVNZVOAUVCUVFVPUUQAUVAUVEUVBGAYPYJGHUUCVQAUUPUUTUVDABYOIYSVSZ
      VTZWAVMUURYHBCDGIKUUPLMNAUUHUUQOVMAUUKUUQPVMAGUECBUKUGZWBVPUUQQVMYKUVIWCW
      IWDAUAUBYHYHYBYFAYHKYJYAYBYLUUFWEAYHKYJYEYFYLUUOWEAUUQUBVKZYHVAZVLZVLZUCU
      VMUUPBWFTZUGZUUPUVMYBUGZUUPUVMYFUGZUVPUVRUUSUVMYATDKWGUGZUGZUVSUVPUUPUVMK
      WFTZUGZUVRUWBUVSUWDUVRVPUVPBUVQKUUPUVMUVQUMZLWHZWJZUVPYHKYJYAYBUWCUWAUUPU
      VMYLUWCUMZDKYJUWAYMUWAUMWKZAYAYBKYJUKUGZUTUVOUUFVMAUUQUVNWLZAUUQUVNWMZWNW
      TVHUVPUVRUVGUVMYETUWAUGZUVTUVPUWDUVRUWMUVTUWGUVPYHKYJYEYFUWCUWAUUPUVMYLUW
      HUWIAYEYFUWJUTUVOUUOVMUWKUWLWNWTVHUVPUCVKZUVRVAZVLZUWNUVSTZCUOTZUWNWOWPZU
      WNUVTTUWPUWQUWNUUPUVMXSUITUGZTZUVAUVMUUTTZXRUITZUGZTZUWNUVMUUPIUITUGZTZUV
      EUVMUVDTZHUGZTZUWSUWPYHKYPUWNYJXSXRUWCUUPUVMYLAUVHUVOUWOYTWQAUUBUVOUWOUUD
      WQUVPUUQUWOUWKVMZUVPUVNUWOUWLVMZUWHUWPUWNUVRUWDUVPUWOVNZUWFWRZXAAUXEUXJVP
      UVOUWOAUXAUXGUXDUXIAUVAUVEUXBUXHUXCHAYPYJGHUUCWSUVKAUVMUUTUVDUVJVTXBAUWNU
      WTUXFABYOIUUPUVMYSXCVTWAWQUWPEFUVLUVLUXGUWSHJUVEUXHAHEFUVLUVLXDFVKEVKJUGW
      BXEVPUVOUWOSWQUWPYHBCUVEIUUPNAUUHUVOUWOOWQZAUUKUVOUWOPWQZYKUXKUVEUMXFUWPY
      HBCUXHIUVMNUXOUXPYKUXLUXHUMXFUWPYHUWRBCUWNUVQIUVMUUPNYKUWRUMZUWEUXOUXPUXL
      UXKUXMXGUWPYHUWRBCUWNUVQIJUVMUUPNYKUXQUWEUXOUXPUXLUXKUXMRXHXKWIUWPYHUWRKD
      UWNUWCYDUUPUVMUUGYLUWRCDMUXQUNUWHUWPUUHUUIUXOUUJVRUWPUUKUULUXPUUMVRUXKUXL
      UXNXGXIWDXJXLAUWJXMZXTUWJVAXTYCVPKYJXNZUUEXTUWJXOXPAUXRYDUWJVAYDYGVPUXSUU
      NYDUWJXOXPXQ $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Thin categories
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $c ThinCat $.

  $( Extend class notation with the class of thin categories. $)
  cthinc $a class ThinCat $.

  ${
    $d B b c f g h x y $.  $d C b c f g h x y $.  $d H b c f g h x y $.
    $( Definition of the class of thin categories, or posetal categories, whose
       hom-sets each contain at most one morphism.  Example 3.26(2) of [Adamek]
       p. 33.  "ThinCat" was taken instead of "PosCat" because the latter might
       mean the category of posets.  (Contributed by Zhi Wang, 17-Sep-2024.) $)
    df-thinc $a |- ThinCat = { c e. Cat |
        [. ( Base ` c ) / b ]. [. ( Hom ` c ) / h ].
            A. x e. b A. y e. b E* f f e. ( x h y ) } $.

    isthinc.b $e |- B = ( Base ` C ) $.
    isthinc.h $e |- H = ( Hom ` C ) $.
    $( The predicate "is a thin category".  (Contributed by Zhi Wang,
       17-Sep-2024.) $)
    isthinc $p |- ( C e. ThinCat <->
            ( C e. Cat /\ A. x e. B A. y e. B E* f f e. ( x H y ) ) ) $=
      ( vh vb vc cv co wcel wmo wral chom cfv cbs wceq wsbc ccat cthinc eqtr4di
      cvv fvexd fveq2 wa adantr wb raleq raleqbi1dv ad2antlr oveq eleq2d mobidv
      2ralbidv adantl bitrd sbcied2 df-thinc elrab2 ) ELZALZBLZILZMZNZEOZBJLZPZ
      AVJPZIKLZQRZUAZJVMSRZUAVCVDVEFMZNZEOZBCPACPZKDUBUCVMDTZVOVTJVPCUEWAVMSUFW
      AVPDSRCVMDSUGGUDWAVJCTZUHZVLVTIVNFUEWCVMQUFWAVNFTWBWAVNDQRFVMDQUGHUDUIWCV
      FFTZUHVLVIBCPZACPZVTWBVLWFUJWAWDVKWEAVJCVIBVJCUKULUMWDWFVTUJWCWDVIVSABCCW
      DVHVREWDVGVQVCVDVEVFFUNUOUPUQURUSUTUTABEIJKVAVB $.

    $( A thin category is a category in which all hom-sets have cardinality
       less than or equal to the cardinality of ` 1o ` .  (Contributed by Zhi
       Wang, 17-Sep-2024.) $)
    isthinc2 $p |- ( C e. ThinCat <->
            ( C e. Cat /\ A. x e. B A. y e. B ( x H y ) ~<_ 1o ) ) $=
      ( vf cthinc wcel ccat cv co wmo wral wa c1o cdom wbr isthinc modom2 bitri
      2ralbii anbi2i ) DIJDKJZHLALBLEMZJHNZBCOACOZPUEUFQRSZBCOACOZPABCDHEFGTUHU
      JUEUGUIABCCHUFUAUCUDUB $.

    $( A thin category is a category in which, given a pair of objects ` x `
       and ` y ` and any two morphisms ` f , g ` from ` x ` to ` y ` , the
       morphisms are equal.  (Contributed by Zhi Wang, 17-Sep-2024.) $)
    isthinc3 $p |- ( C e. ThinCat <-> ( C e. Cat /\
      A. x e. B A. y e. B A. f e. ( x H y ) A. g e. ( x H y ) f = g ) ) $=
      ( cthinc wcel ccat cv co wmo wral wa weq isthinc moel 2ralbii anbi2i
      bitri ) DJKDLKZEMAMBMGNZKEOZBCPACPZQUDEFRFUEPEUEPZBCPACPZQABCDEGHISUGUIUD
      UFUHABCCEFUETUAUBUC $.
  $}

  ${
    $d C f x y $.
    $( A thin category is a category.  (Contributed by Zhi Wang,
       17-Sep-2024.) $)
    thinccat $p |- ( C e. ThinCat -> C e. Cat ) $=
      ( vf vx vy cthinc wcel ccat cv chom cfv wmo cbs wral eqid isthinc simplbi
      co ) AEFAGFBHCHDHAIJZQFBKDALJZMCSMCDSABRSNRNOP $.

    thinccatd.c $e |- ( ph -> C e. ThinCat ) $.
    $( A thin category is a category (deduction form).  (Contributed by Zhi
       Wang, 24-Sep-2024.) $)
    thinccatd $p |- ( ph -> C e. Cat ) $=
      ( cthinc wcel ccat thinccat syl ) ABDEBFECBGH $.
  $}

  $( A thin category is a category.  (Contributed by Zhi Wang, 17-Sep-2024.) $)
  thincssc $p |- ThinCat C_ Cat $=
    ( vc cthinc ccat cv thinccat ssriv ) ABCADEF $.

  ${
    $d B w y z $.  $d B x y z $.  $d F k l $.  $d G l $.  $d H f k w $.
    $d H k l $.  $d H f x y z $.  $d X f k w $.  $d X k l $.  $d X f w z $.
    $d Y k l $.  $d Y k w $.  $d k ph $.  $d ph z $.
    isthincd2lem1.1 $e |- ( ph -> X e. B ) $.
    isthincd2lem1.2 $e |- ( ph -> Y e. B ) $.
    isthincd2lem1.3 $e |- ( ph -> F e. ( X H Y ) ) $.
    isthincd2lem1.4 $e |- ( ph -> G e. ( X H Y ) ) $.
    ${
      isthincd2lem1.5 $e |- ( ph ->
                              A. x e. B A. y e. B E* f f e. ( x H y ) ) $.
      $( Lemma for ~ isthincd2 and ~ thincmo2 .  (Contributed by Zhi Wang,
         17-Sep-2024.) $)
      isthincd2lem1 $p |- ( ph -> F = G ) $=
        ( vk cv wceq wral wcel vl vz vw wmo oveq1 eleq2d mobidv oveq2 cbvral2vw
        co sylib nfv eleq1w cbvmow bitrid wa eqidd rspc2vd mpd moel eqeq1 eqeq2
        ) APQZUAQZRZUAIJHUJZSPVFSZFGRZAVCVFTZPUDZVGAEQZUBQZUCQZHUJZTZEUDZUCDSUB
        DSZVJAVKBQZCQZHUJZTZEUDZCDSBDSVQOWBVPVKVLVSHUJZTZEUDBCUBUCDDVRVLRZWAWDE
        WEVTWCVKVRVLVSHUEUFUGVSVMRZWDVOEWFWCVNVKVSVMVLHUHUFUGUIUKAVJVKIVMHUJZTZ
        EUDZVPUBUCIJDDDVLIRZVOWHEWJVNWGVKVLIVMHUEUFUGWIVCWGTZPUDVMJRZVJWHWKEPWH
        PULWKEULEPWGUMUNWLWKVIPWLWGVFVCVMJIHUHUFUGUOKAWJUPDUQLURUSPUAVFUTUKAVHF
        VDRVEPUAFGVFVFVFVCFVDVAVDGFVBMAVCFRUPVFUQNURUS $.
    $}

    ${
      $d B f $.  $d C f x y $.
      thincmo2.b $e |- B = ( Base ` C ) $.
      thincmo2.h $e |- H = ( Hom ` C ) $.
      thincmo2.c $e |- ( ph -> C e. ThinCat ) $.
      $( Morphisms in the same hom-set are identical.  (Contributed by Zhi
         Wang, 17-Sep-2024.) $)
      thincmo2 $p |- ( ph -> F = G ) $=
        ( vx vy vf wcel cv cthinc co wmo wral isthinc simprbi syl isthincd2lem1
        ccat ) APQBRDEFGHIJKLACUASZRTPTQTFUBSRUCQBUDPBUDZOUJCUISUKPQBCRFMNUEUFU
        GUH $.
    $}
  $}

  ${
    $d B g $.  $d C g $.  $d F g $.  $d H g $.  $d X g $.  $d Y g $.
    $d g ph $.
    thinchom.x $e |- ( ph -> X e. B ) $.
    thinchom.y $e |- ( ph -> Y e. B ) $.
    thinchom.f $e |- ( ph -> F e. ( X H Y ) ) $.
    thinchom.b $e |- B = ( Base ` C ) $.
    thinchom.h $e |- H = ( Hom ` C ) $.
    thinchom.c $e |- ( ph -> C e. ThinCat ) $.
    $( A non-empty hom-set of a thin category is given by its element.
       (Contributed by Zhi Wang, 20-Oct-2025.) $)
    thinchom $p |- ( ph -> ( X H Y ) = { F } ) $=
      ( vg co cv wcel wa adantr simpr cthinc thincmo2 eqsnd ) ANFGEOZDANPZUDQZR
      BCUEDEFGAFBQUFHSAGBQUFISAUFTADUDQUFJSKLACUAQUFMSUBJUC $.
  $}

  ${
    $d B f g x y $.  $d C f g x y $.  $d H f g x y $.  $d X f g x y $.
    $d Y f g x y $.  $d f g ph $.
    thincmo.c $e |- ( ph -> C e. ThinCat ) $.
    thincmo.x $e |- ( ph -> X e. B ) $.
    thincmo.y $e |- ( ph -> Y e. B ) $.
    ${
      thincmo.b $e |- B = ( Base ` C ) $.
      thincmo.h $e |- H = ( Hom ` C ) $.
      $( There is at most one morphism in each hom-set.  (Contributed by Zhi
         Wang, 21-Sep-2024.) $)
      thincmo $p |- ( ph -> E* f f e. ( X H Y ) ) $=
        ( vg cv co wcel wa weq wal adantr wi simprl simprr thincmo2 ex alrimivv
        wmo cthinc eleq1w mo4 sylibr ) ADNZFGEOZPZMNZUMPZQZDMRZUAZMSDSUNDUGAUSD
        MAUQURAUQQBCULUOEFGAFBPUQITAGBPUQJTAUNUPUBAUNUPUCKLACUHPUQHTUDUEUFUNUPD
        MDMUMUIUJUK $.

      $( Alternate proof of ~ thincmo .  (Contributed by Zhi Wang,
         21-Sep-2024.)  (Proof modification is discouraged.)
         (New usage is discouraged.) $)
      thincmoALT $p |- ( ph -> E* f f e. ( X H Y ) ) $=
        ( vx vy cv co wcel wmo wral wceq cthinc ccat isthinc simprbi syl oveq12
        wi wa eleq2d mobidv rspc2gv syl2anc mpd ) ADOZMOZNOZEPZQZDRZNBSMBSZUNFG
        EPZQZDRZACUAQZUTHVDCUBQUTMNBCDEKLUCUDUEAFBQGBQUTVCUGIJUSVCMNFGBBUOFTUPG
        TUHZURVBDVEUQVAUNUOFUPGEUFUIUJUKULUM $.
    $}

    thincn0eu.b $e |- ( ph -> B = ( Base ` C ) ) $.
    thincn0eu.h $e |- ( ph -> H = ( Hom ` C ) ) $.
    $( At most one morphism in each hom-set (deduction form).  (Contributed by
       Zhi Wang, 21-Sep-2024.) $)
    thincmod $p |- ( ph -> E* f f e. ( X H Y ) ) $=
      ( cv co wcel wmo chom cfv eleqtrd eqid thincmo oveqd eleq2d mobidv mpbird
      cbs ) ADMZFGENZOZDPUGFGCQRZNZOZDPACUFRZCDUJFGHAFBUMIKSAGBUMJKSUMTUJTUAAUI
      ULDAUHUKUGAEUJFGLUBUCUDUE $.

    $( In a thin category, a hom-set being non-empty is equivalent to having a
       unique element.  (Contributed by Zhi Wang, 21-Sep-2024.) $)
    thincn0eu $p |- ( ph ->
                ( ( X H Y ) =/= (/) <-> E! f f e. ( X H Y ) ) ) $=
      ( co c0 wne cv wcel weu wa sylibr wex wmo n0 biimpi thincmod df-eu expcom
      anim12i euex impbid1 ) AFGEMZNOZDPUKQZDRZULAUNULASUMDUAZUMDUBZSUNULUOAUPU
      LUODUKUCZUDABCDEFGHIJKLUEUHUMDUFTUGUNUOULUMDUIUQTUJ $.
  $}

  ${
    $d B f g h z $.  $d C f g h z $.  $d E f g h z $.  $d F f g h z $.
    $d H f g h z $.  $d M f g h z $.  $d X f g h z $.  $d Y f g h z $.
    $d f g h ph z $.
    thincid.c $e |- ( ph -> C e. ThinCat ) $.
    thincid.b $e |- B = ( Base ` C ) $.
    thincid.h $e |- H = ( Hom ` C ) $.
    thincid.x $e |- ( ph -> X e. B ) $.
    ${
      thincid.i $e |- .1. = ( Id ` C ) $.
      thincid.f $e |- ( ph -> F e. ( X H X ) ) $.
      $( In a thin category, a morphism from an object to itself is an identity
         morphism.  (Contributed by Zhi Wang, 24-Sep-2024.) $)
      thincid $p |- ( ph -> F = ( .1. ` X ) ) $=
        ( cfv thinccatd catidcl thincmo2 ) ABCEGDNFGGKKMABCDFGIJLACHOKPIJHQ $.
    $}

    thincmon.y $e |- ( ph -> Y e. B ) $.
    ${
      thincmon.m $e |- M = ( Mono ` C ) $.
      $( In a thin category, all morphisms are monomorphisms.  Example 7.33(9)
         of [Adamek] p. 110.  The converse does not hold.  See ~ grptcmon .
         (Contributed by Zhi Wang, 24-Sep-2024.) $)
      thincmon $p |- ( ph -> ( X M Y ) = ( X H Y ) ) $=
        ( vg vz vh co cv wcel wral vf cop cco cfv wceq w3a simpr1 adantr simpr2
        wi wa simpr3 cthinc thincmo2 a1d ralrimivvva thinccatd ismon2 mpbiran2d
        eqid eqrdv ) AUAFGEQZFGDQZAUARZVBSVDVCSVDNRZORZFUBGCUCUDZQZQVDPRZVHQUEZ
        VEVIUEZUJZPVFFDQZTNVMTOBTAVLONPBVMVMAVFBSZVEVMSZVIVMSZUFZUKZVKVJVRBCVEV
        IDVFFAVNVOVPUGAFBSVQKUHAVNVOVPUIAVNVOVPULIJACUMSVQHUHUNUOUPAOBCVGNPVDDE
        FGIJVGUTMACHUQKLURUSVA $.
    $}

    ${
      thincepi.e $e |- E = ( Epi ` C ) $.
      $( In a thin category, all morphisms are epimorphisms.  The converse does
         not hold.  See ~ grptcepi .  (Contributed by Zhi Wang,
         24-Sep-2024.) $)
      thincepi $p |- ( ph -> ( X E Y ) = ( X H Y ) ) $=
        ( vg vz vh co cv wcel wral vf cop cco cfv wceq w3a adantr simpr1 simpr2
        wi wa simpr3 cthinc thincmo2 a1d ralrimivvva thinccatd isepi2 mpbiran2d
        eqid eqrdv ) AUAFGDQZFGEQZAUARZVBSVDVCSNRZVDFGUBORZCUCUDZQZQPRZVDVHQUEZ
        VEVIUEZUJZPGVFEQZTNVMTOBTAVLONPBVMVMAVFBSZVEVMSZVIVMSZUFZUKZVKVJVRBCVEV
        IEGVFAGBSVQLUGAVNVOVPUHAVNVOVPUIAVNVOVPULIJACUMSVQHUGUNUOUPAOBCVGNPDVDE
        FGIJVGUTMACHUQKLURUSVA $.
    $}
  $}

  ${
    $d .x. f g k u v w z $.  $d .x. g k l u v w z $.  $d .x. f g w x y z $.
    $d B u v w z $.  $d B w x y z $.  $d F k l $.  $d G l $.
    $d H f g k u v w z $.  $d H g k l u v w z $.  $d H f g w x y z $.
    $d X k l u v w $.  $d Y k l u v $.  $d Z k l u $.  $d v w y z $.
    isthincd2lem2.1 $e |- ( ph -> X e. B ) $.
    isthincd2lem2.2 $e |- ( ph -> Y e. B ) $.
    isthincd2lem2.3 $e |- ( ph -> Z e. B ) $.
    isthincd2lem2.4 $e |- ( ph -> F e. ( X H Y ) ) $.
    isthincd2lem2.5 $e |- ( ph -> G e. ( Y H Z ) ) $.
    isthincd2lem2.6 $e |- ( ph -> A. x e. B A. y e. B A. z e. B
                       A. f e. ( x H y ) A. g e. ( y H z )
                        ( g ( <. x , y >. .x. z ) f ) e. ( x H z ) ) $.
    $( Lemma for ~ isthincd2 .  (Contributed by Zhi Wang, 17-Sep-2024.) $)
    isthincd2lem2 $p |- ( ph -> ( G ( <. X , Y >. .x. Z ) F ) e. ( X H Z ) ) $=
      ( vl vk vw vv vu cv cop wcel wral wceq oveq1 opeq1 oveq1d eleq12d ralbidv
      co oveqd raleqbidv oveq2 opeq2 eleq1d cbvral2vw bitrdi cbvral3vw sylib wi
      rspc3v syl3anc mpd rspc2v syl2anc ) AUAUFZUBUFZLMUGZNFUPZUPZLNKUPZUHZUAMN
      KUPZUIZUBLMKUPZUIZJIVOUPZVQUHZAVLVMUCUFZUDUFZUGZUEUFZFUPZUPZWEWHKUPZUHZUA
      WFWHKUPZUIZUBWEWFKUPZUIZUEEUIUDEUIUCEUIZWBAHUFZGUFZBUFZCUFZUGZDUFZFUPZUPZ
      WTXCKUPZUHZHXAXCKUPZUIZGWTXAKUPZUIZDEUICEUIBEUIWQTXKWPWRWSWEXAUGZXCFUPZUP
      ZWEXCKUPZUHZHXHUIZGWEXAKUPZUIWRWSWGXCFUPZUPZXOUHZHWFXCKUPZUIZGWOUIZBCDUCU
      DUEEEEWTWEUJZXIXQGXJXRWTWEXAKUKYEXGXPHXHYEXEXNXFXOYEXDXMWRWSYEXBXLXCFWTWE
      XAULUMUQWTWEXCKUKUNUOURXAWFUJZXQYCGXRWOXAWFWEKUSYFXPYAHXHYBXAWFXCKUKYFXNX
      TXOYFXMXSWRWSYFXLWGXCFXAWFWEUTUMUQVAURURXCWHUJZYDWRWSWIUPZWKUHZHWMUIZGWOU
      IWPYGYCYJGWOYGYAYIHYBWMXCWHWFKUSYGXTYHXOWKYGXSWIWRWSXCWHWGFUSUQXCWHWEKUSU
      NURUOYIWLWRVMWIUPZWKUHGHUBUAWOWMWSVMUJYHYKWKWSVMWRWIUSVAWRVLUJYKWJWKWRVLV
      MWIUKVAVBVCVDVEALEUHMEUHNEUHWQWBVFOPQWPWBVLVMLWFUGZWHFUPZUPZLWHKUPZUHZUAW
      MUIZUBLWFKUPZUIVLVMVNWHFUPZUPZYOUHZUAMWHKUPZUIZUBWAUIUCUDUELMNEEEWELUJZWN
      YQUBWOYRWELWFKUKUUDWLYPUAWMUUDWJYNWKYOUUDWIYMVLVMUUDWGYLWHFWELWFULUMUQWEL
      WHKUKUNUOURWFMUJZYQUUCUBYRWAWFMLKUSUUEYPUUAUAWMUUBWFMWHKUKUUEYNYTYOUUEYMY
      SVLVMUUEYLVNWHFWFMLUTUMUQVAURURWHNUJZUUCVTUBWAUUFUUAVRUAUUBVSWHNMKUSUUFYT
      VPYOVQUUFYSVOVLVMWHNVNFUSUQWHNLKUSUNURUOVGVHVIAIWAUHJVSUHWBWDVFRSVRWDVLIV
      OUPZVQUHUBUAIJWAVSVMIUJVPUUGVQVMIVLVOUSVAVLJUJUUGWCVQVLJIVOUKVAVJVKVI $.
  $}

  ${
    $d B y $.  $d C f x y $.  $d f ph x y $.
    isthincd.b $e |- ( ph -> B = ( Base ` C ) ) $.
    isthincd.h $e |- ( ph -> H = ( Hom ` C ) ) $.
    isthincd.t $e |- ( ( ph /\ ( x e. B /\ y e. B ) )
            -> E* f f e. ( x H y ) ) $.
    ${
      isthincd.c $e |- ( ph -> C e. Cat ) $.
      $( The predicate "is a thin category" (deduction form).  (Contributed by
         Zhi Wang, 17-Sep-2024.) $)
      isthincd $p |- ( ph -> C e. ThinCat ) $=
        ( ccat wcel cv cfv co wmo wral raleqbidv eqid chom cbs ralrimivva oveqd
        cthinc eleq2d mobidv mpbid isthinc sylanbrc ) AELMFNZBNZCNZEUAOZPZMZFQZ
        CEUBOZRZBURRZEUEMKAUKULUMGPZMZFQZCDRZBDRUTAVCBCDDJUCAVDUSBDURHAVCUQCDUR
        HAVBUPFAVAUOUKAGUNULUMIUDUFUGSSUHBCUREFUNURTUNTUIUJ $.
    $}

    $d .1. f g k w x z $.  $d .x. f g k w x y z $.  $d B f g k w x y z $.
    $d C f g k w x y z $.  $d H f g k w x y z $.  $d f g k ph w x y z $.
    isthincd2.o $e |- ( ph -> .x. = ( comp ` C ) ) $.
    isthincd2.c $e |- ( ph -> C e. V ) $.
    isthincd2.ps $e |- ( ps <-> ( ( x e. B /\ y e. B /\ z e. B ) /\
            ( f e. ( x H y ) /\ g e. ( y H z ) ) ) ) $.
    isthincd2.1 $e |- ( ( ph /\ y e. B ) -> .1. e. ( y H y ) ) $.
    isthincd2.2 $e |- ( ( ph /\ ps ) ->
       ( g ( <. x , y >. .x. z ) f ) e. ( x H z ) ) $.
    $( The predicate " ` C ` is a thin category" without knowing ` C ` is a
       category (deduction form).  The identity arrow operator is also provided
       as a byproduct.  (Contributed by Zhi Wang, 17-Sep-2024.) $)
    isthincd2 $p |- ( ph -> ( C e. ThinCat
                  /\ ( Id ` C ) = ( y e. B |-> .1. ) ) ) $=
      ( vw vk cthinc wcel ccid cfv cmpt wceq ccat cv co w3a wa 3an4anass anbi1i
      3anbi1i 3anass an4 3bitri df-3an anbi2i 3bitr4i bitr4i cop simpr1l syldan
      simpr1r simpr31 sylbir ralrimivva ralrimivvva isthincd2lem2 isthincd2lem1
      wral bianass adantr wmo sylan2b simpr2l simpr32 3ad2antr1 simpr2r simpr33
      sylan2br iscatd2 simpld isthincd simprd jca ) AGUDUEGUFUGDFIUHUIZACDFGJLN
      OPAGUJUEZWKABUBUKZFUEZUCUKZEUKZWMLULUEZUMZCDEUBFGHIJKUCLMNOQRWRCUKZFUEZDU
      KZFUEZUNZWPFUEZWNUNZUNZJUKZWSXALULZUEZKUKZXAWPLULZUEZWQUMZUNZXCXEXMUMZWTX
      BXDUMZWNUNZXIXLUNZWQUNZUNZXFXSUNWRXNXQXFXSWTXBXDWNUOUPWRXPXRUNZWNWQUMYAWN
      WQUNUNXTBYAWNWQSUQYAWNWQURXPXRWNWQUSUTXMXSXFXIXLWQVAVBVCXCXEXMVAVDZTWRAXO
      IXGWSXAVEZXAHULULZXGUIYBAXOUNZCDFJYDXGLWSXAWTXBXEXMAVFZWTXBXEXMAVHZYECDEF
      HJKXGILWSXAXAYFYGYGXIXLWQXCXEAVIZAXOXBIXAXALULUEYGTVGZAXJXGYCWPHULULZWSWP
      LULUEZKXKVOJXHVOZEFVODFVOCFVOXOAYLCDEFFFAXPUNZYKJKXHXKYMXRUNABUNYKBXPXRAS
      VPUAVJVKVLVQZVMYHAXIJVRZDFVOCFVOXOAYOCDFFPVKVQZVNVSWRAXOXJIXAXAVEWPHULULZ
      XJUIYBYECDFJYQXJLXAWPYGXDWNXCXMAVTZYECDEFHJKIXJLXAXAWPYGYGYRYIXIXLWQXCXEA
      WAZYNVMYSYPVNVSAWNBYKWQUAWBZWRAXOWOXJXAWPVEWMHULULZXGYCWMHULULZWOYJWSWPVE
      WMHULULZUIYBYECDFJUUBUUCLWSWMYFXDWNXCXMAWCZYECDEFHJKXGUUALWSXAWMYFYGUUDYH
      YECDEFHJKXJWOLXAWPWMYGYRUUDYSXIXLWQXCXEAWDZYNVMYNVMYECDEFHJKYJWOLWSWPWMYF
      YRUUDXOAWRYKYBYTWEUUEYNVMYPVNVSWFZWGWHAWLWKUUFWIWJ $.
  $}

  ${
    $d C f x y $.  $d O f x y $.
    oppcthin.o $e |- O = ( oppCat ` C ) $.
    $( The opposite category of a thin category is thin.  (Contributed by Zhi
       Wang, 29-Sep-2024.) $)
    oppcthin $p |- ( C e. ThinCat -> O e. ThinCat ) $=
      ( vx vy vf cthinc wcel cbs cfv chom wceq eqid oppcbas a1i cv wa wmo ccat
      co eqidd simpl simprr simprl thincmo oppchom eleq2i mobii sylibr thinccat
      oppccat syl isthincd ) AGHZDEAIJZBFBKJZUOBIJLUNUOABCUOMZNOUNUPUAUNDPZUOHZ
      EPZUOHZQZQZFPZUTURAKJZTZHZFRVDURUTUPTZHZFRVCUOAFVEUTURUNVBUBUNUSVAUCUNUSV
      AUDUQVEMZUEVIVGFVHVFVDAVEBURUTVJCUFUGUHUIUNASHBSHAUJABCUKULUM $.
  $}

  ${
    $d B f g x y z $.  $d C f g x y z $.  $d H f g x y z $.  $d O f g x y z $.
    $d f g ph x y z $.
    oppcthinco.o $e |- O = ( oppCat ` C ) $.
    oppcthinco.c $e |- ( ph -> C e. ThinCat ) $.
    ${
      oppcthinco.1 $e |- ( ph -> ( Homf ` C ) = ( Homf ` O ) ) $.
      $( If the opposite category of a thin category has the same base and
         hom-sets as the original category, then it has the same composition
         operation as the original category.  (Contributed by Zhi Wang,
         16-Oct-2025.) $)
      oppcthinco $p |- ( ph -> ( comf ` C ) = ( comf ` O ) ) $=
        ( vg vf vx vy vz cfv wceq cv co wral wcel wa eqid homfeqval cop cco cbs
        ccomf chom w3a simplr1 simplr2 simplr3 oppcco cthinc ad2antrr thinccatd
        simprr chomf oppchom eqtrdi eleqtrd simprl eleqtrrd thincmo2 ralrimivva
        catcocl eqtr2d ralrimivvva eqidd homfeqbas comfeq mpbird ) ABUDLCUDLMGN
        ZHNZINZJNZUAZKNZBUBLZOOZVJVKVNVOCUBLZOOZMZGVMVOBUELZOZPHVLVMWAOZPZKBUCL
        ZPJWEPIWEPAWDIJKWEWEWEAVLWEQZVMWEQZVOWEQZUFZRZVTHGWCWBWJVKWCQZVJWBQZRZR
        ZVSVKVJVOVMUAVLVPOOZVQWNWEBVPVKVJCVLVMVOWESZVPSZDWFWGWHAWMUGZWFWGWHAWMU
        HZWFWGWHAWMUIZUJWNWEBWOVQWAVLVOWRWTWNWOVOVLWAOZVLVOWAOZWNWEBVPVJVKWAVOV
        MVLWPWASZWQWNBABUKQWIWMEULZUMZWTWSWRWNVJWBVOVMWAOZWJWKWLUNZWNWBVMVOCUEL
        ZOXFWNWEBCWAXHVMVOWPXCXHSZABUOLCUOLMWIWMFULZWSWTTBWACVMVOXCDUPUQURWNVKW
        CVMVLWAOZWJWKWLUSZWNWCVLVMXHOXKWNWEBCWAXHVLVMWPXCXIXJWRWSTBWACVLVMXCDUP
        UQURVCWNXBVLVOXHOXAWNWEBCWAXHVLVOWPXCXIXJWRWTTBWACVLVOXCDUPUQUTWNWEBVPV
        KVJWAVLVMVOWPXCWQXEWRWSWTXLXGVCWPXCXDVAVDVBVEAIJKWEBCVRVPHGWAWQVRSXCAWE
        VFABCFVGFVHVI $.
    $}

    oppcthinendc.b $e |- B = ( Base ` C ) $.
    oppcthinendc.h $e |- H = ( Hom ` C ) $.
    oppcthinendc.1 $e |- ( ( ph /\ ( x e. B /\ y e. B ) )
                        -> ( x =/= y -> ( x H y ) = (/) ) ) $.
    $( The opposite category of a thin category whose morphisms are all
       endomorphisms has the same base, hom-sets ( ~ oppcendc ) and composition
       operation as the original category.  (Contributed by Zhi Wang,
       16-Oct-2025.) $)
    oppcthinendc $p |- ( ph -> ( comf ` C ) = ( comf ` O ) ) $=
      ( oppcendc oppcthinco ) AEGHIABCDEFGHJKLMN $.

    $( Alternate proof of ~ oppcthinendc .  (Contributed by Zhi Wang,
       16-Oct-2025.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    oppcthinendcALT $p |- ( ph -> ( comf ` C ) = ( comf ` O ) ) $=
      ( vg cfv wceq co wral wcel wa c0 vf vz ccomf cop cco eqid simplr1 simplr2
      w3a simplr3 oppcco wne simpll jca simprl ne0d necon1d imp syl21anc simprr
      cv wi neeq1 oveq1 eqeq1d imbi12d anassrs ralrimiva adantlr simplr rspcdva
      neeq2 oveq2 syl2anc equcomd opeq1d oveq12d oveq1d eleqtrd oveq2d eleqtrrd
      mpd eqtrd cthinc syl thincmo2 oveq123d ralrimivva ralrimivvva cbs oppcbas
      eqtr2d a1i oppcendc comfeq mpbird ) AEUCNGUCNOMVAZUAVAZBVAZCVAZUDZUBVAZEU
      ENZPZPZWQWRXAXBGUENZPPZOZMWTXBFPZQUAWSWTFPZQZUBDQCDQBDQAXKBCUBDDDAWSDRZWT
      DRZXBDRZUIZSZXHUAMXJXIXPWRXJRZWQXIRZSZSZXGWRWQXBWTUDZWSXCPZPXEXTDEXCWRWQG
      WSWTXBJXCUFZHXLXMXNAXSUGZXLXMXNAXSUHZXLXMXNAXSUJZUKXTWRWQWQWRYBXDXTYAXAWS
      XBXCXTXBWSWTXTBUBXTWSWTXBXTAXLXMSZXJTULZWSWTOZAXOXSUMZXTXLXMYDYEUNXTXJWRX
      PXQXRUOZUPAYGSZYHYIYLWSWTXJTLUQURUSZXTXITULWTXBOZXTXIWQXPXQXRUTZUPXTWTXBX
      ITXTWSXBULZWSXBFPZTOZVBZWTXBULZXITOZVBBDWTYIYPYTYRUUAWSWTXBVCYIYQXITWSWTX
      BFVDVEVFXTAXNYSBDQYJYFAXNSZYSBDUUBXLSWSWTULZXJTOZVBZYSCDXBYNUUCYPUUDYRWTX
      BWSVLYNXJYQTWTXBWSFVMVEVFAXLUUECDQXNAXLSUUECDAXLXMUUELVGVHVIAXNXLVJVKVHVN
      YEVKUQWBZWCZVOVPUUGVQXTDEWRWQFWTWTYEYEXTWRXJWTWTFPZYKXTWSWTWTFYMVRVSXTWQX
      IUUHYOXTWTXBWTFUUFVTWAJKXTAEWDRYJIWEWFZXTUAMUUIVOWGWLWHWIABCUBDEGXFXCUAMF
      YCXFUFKDEWJNOAJWMDGWJNOADEGHJWKWMABCDEFGHJKLWNWOWP $.
  $}

  ${
    $d C f x y $.  $d D f x y $.  $d V f x y $.  $d W f x y $.  $d f ph x y $.
    thincpropd.1 $e |- ( ph -> ( Homf ` C ) = ( Homf ` D ) ) $.
    thincpropd.2 $e |- ( ph -> ( comf ` C ) = ( comf ` D ) ) $.
    thincpropd.3 $e |- ( ph -> C e. V ) $.
    thincpropd.4 $e |- ( ph -> D e. W ) $.
    $( Two structures with the same base, hom-sets and composition operation
       are either both thin categories or neither.  (Contributed by Zhi Wang,
       16-Oct-2025.) $)
    thincpropd $p |- ( ph -> ( C e. ThinCat <-> D e. ThinCat ) ) $=
      ( vf vx vy ccat wcel cv chom cfv wral wa eqid co wmo cthinc catpropd wceq
      chomf adantr simprl simprr homfeqval eleq2d 2ralbidva homfeqbas raleqbidv
      cbs mobidv raleqdv bitrd anbi12d isthinc 3bitr4g ) ABMNZJOZKOZLOZBPQZUAZN
      ZJUBZLBUOQZRKVJRZSCMNZVCVDVECPQZUAZNZJUBZLCUOQZRZKVQRZSBUCNCUCNAVBVLVKVSA
      BCDEFGHIUDAVKVPLVJRZKVJRVSAVIVPKLVJVJAVDVJNZVEVJNZSZSZVHVOJWDVGVNVCWDVJBC
      VFVMVDVEVJTZVFTZVMTZABUFQCUFQUEWCFUGAWAWBUHAWAWBUIUJUKUPULAVTVRKVJVQABCFU
      MZAVPLVJVQWHUQUNURUSKLVJBJVFWEWFUTKLVQCJVMVQTWGUTVA $.
  $}

  ${
    $d C f x y $.  $d D f x y $.  $d J f x y $.  $d f ph x y $.
    subthinc.1 $e |- D = ( C |`cat J ) $.
    subthinc.j $e |- ( ph -> J e. ( Subcat ` C ) ) $.
    subthinc.c $e |- ( ph -> C e. ThinCat ) $.
    $( A subcategory of a thin category is thin.  (Contributed by Zhi Wang,
       30-Sep-2024.) $)
    subthinc $p |- ( ph -> D e. ThinCat ) $=
      ( vx vy vf cdm cfv cthinc eqid cv wcel wa co wss adantr cbs eqidd subcss1
      subcfn rescbas reschom csn wex wmo csubc cxp simprl simprr subcss2 sseldd
      chom wfn thincmo mosssn2 sylib sstr2 eximdv sylc sylibr subccat isthincd
      ) AHIDKKZCJDABUALZBCVGDMEVHNZGABVGDFAVGUBUDZAVHBVGDFVJVIUCZUEAVHBCVGDMEVI
      GVJVKUFAHOZVGPZIOZVGPZQZQZVLVNDRZJOZUGZSZJUHZVSVRPJUIVQVRVLVNBUPLZRZSZWDV
      TSZJUHZWBVQBVGWCDVLVNADBUJLPVPFTADVGVGUKUQVPVJTWCNZAVMVOULZAVMVOUMZUNVQVS
      WDPJUIWGVQVHBJWCVLVNABMPVPGTVQVGVHVLAVGVHSVPVKTZWIUOVQVGVHVNWKWJUOVIWHURJ
      JWDUSUTWEWFWAJVRWDVTVAVBVCJJVRUSVDABCDEFVEVF $.
  $}

  ${
    $d B m w x y z $.  $d C m $.  $d E m $.  $d F m w x y z $.  $d G m w z $.
    $d H m w x y z $.  $d J m w x y z $.  $d K m w z $.  $d m ph w z $.
    functhinclem1.b $e |- B = ( Base ` D ) $.
    functhinclem1.c $e |- C = ( Base ` E ) $.
    functhinclem1.h $e |- H = ( Hom ` D ) $.
    functhinclem1.j $e |- J = ( Hom ` E ) $.
    functhinclem1.e $e |- ( ph -> E e. ThinCat ) $.
    functhinclem1.f $e |- ( ph -> F : B --> C ) $.
    functhinclem1.k $e |- K = ( x e. B , y e. B |->
        ( ( x H y ) X. ( ( F ` x ) J ( F ` y ) ) ) ) $.
    functhinclem1.1 $e |- ( ( ph /\ ( z e. B /\ w e. B ) )
               -> ( ( ( F ` z ) J ( F ` w ) ) = (/) -> ( z H w ) = (/) ) ) $.
    $( Lemma for ~ functhinc .  Given the object part, there is only one
       possible morphism part such that the mapped morphism is in its
       corresponding hom-set.  (Contributed by Zhi Wang, 1-Oct-2024.) $)
    functhinclem1 $p |- ( ph -> ( ( G e. _V /\ G Fn ( B X. B ) /\
      A. z e. B A. w e. B ( z G w ) : ( z H w ) --> ( ( F ` z ) J ( F ` w ) ) )
      <-> G = K ) ) $=
      ( vm cvv wcel cxp wfn cv co cfv wf wral w3a wceq simpl simpr2 simpr3 eqid
      wa c0 adantlr cthinc ad2antrr simprl ffvelcdmd simprr thincmo mofeu oveq1
      wi fveq2 oveq1d xpeq12d oveq2 oveq2d ovex xpex ovmpo adantl eqeq2d bitr4d
      2ralbidva wb simpr fnmpoi eqfnov2 sylancl biimpa syl21anc cbs fvexi mpoex
      cmpo eqeltri eleq1 mpbiri fneq1 biimpar 3jca impbida ) AKUDUEZKFFUFZUGZDU
      HZEUHZLUIZXDJUJZXEJUJZMUIZXDXEKUIZUKZEFULDFULZUMZKNUNZAXMUSAXCXLXNAXMUOAX
      AXCXLUPAXAXCXLUQAXCUSZXLXNXOXLXJXDXENUIZUNZEFULDFULZXNXOXKXQDEFFXOXDFUEZX
      EFUEZUSZUSZXKXJXFXIUFZUNXQYBUCXFXIXJYCYCURAYAXIUTUNXFUTUNVJXCUBVAYBGIUCMX
      GXHAIVBUEXCYASVCYBFGXDJAFGJUKXCYATVCZXOXSXTVDVEYBFGXEJYDXOXSXTVFVEPRVGVHY
      BXPYCXJYAXPYCUNXOBCXDXEFFBUHZCUHZLUIZYEJUJZYFJUJZMUIZUFZYCNXDYFLUIZXGYIMU
      IZUFYEXDUNZYGYLYJYMYEXDYFLVIYNYHXGYIMYEXDJVKVLVMYFXEUNZYLXFYMXIYFXEXDLVNY
      OYIXHXGMYFXEJVKVOVMUAXFXIXDXELVPXGXHMVPVQVRVSVTWAWBXOXCNXBUGZXNXRWCAXCWDB
      CFFYKNUAYGYJYEYFLVPYHYIMVPVQWEZDEFFKNWFWGWAZWHWIAXNUSZXAXCXLXNXAAXNXANUDU
      ENBCFFYKWMUDUABCFFYKFHWJOWKZYTWLWNKNUDWOWPVSXNXCAXNXCYPYQXBKNWQWPVSZYSAXC
      XNXLAXNUOUUAAXNWDXOXLXNYRWRWIWSWT $.
  $}

  ${
    $d B x y $.  $d F x y $.  $d H x y $.  $d J x y $.  $d X x y $.
    $d Y x y $.
    functhinclem2.x $e |- ( ph -> X e. B ) $.
    functhinclem2.y $e |- ( ph -> Y e. B ) $.
    functhinclem2.1 $e |- ( ph -> A. x e. B A. y e. B
        ( ( ( F ` x ) J ( F ` y ) ) = (/) -> ( x H y ) = (/) ) ) $.
    $( Lemma for ~ functhinc .  (Contributed by Zhi Wang, 1-Oct-2024.) $)
    functhinclem2 $p |- ( ph ->
            ( ( ( F ` X ) J ( F ` Y ) ) = (/) -> ( X H Y ) = (/) ) ) $=
      ( wcel cv cfv co c0 wceq wi wral simpl fveq2d simpr oveq12d eqeq1d oveq12
      wa imbi12d rspc2gv imp syl21anc ) AHDMZIDMZBNZEOZCNZEOZGPZQRZUNUPFPZQRZSZ
      CDTBDTZHEOZIEOZGPZQRZHIFPZQRZSZJKLULUMUGVCVJVBVJBCHIDDUNHRZUPIRZUGZUSVGVA
      VIVMURVFQVMUOVDUQVEGVMUNHEVKVLUAUBVMUPIEVKVLUCUBUDUEVMUTVHQUNHUPIFUFUEUHU
      IUJUK $.
  $}

  ${
    $d F n $.  $d F x y $.  $d H x y $.  $d J n $.  $d J x y $.  $d X n $.
    $d X x y $.  $d Y n $.  $d Y x y $.  $d ph x y $.
    functhinclem3.x $e |- ( ph -> X e. B ) $.
    functhinclem3.y $e |- ( ph -> Y e. B ) $.
    functhinclem3.m $e |- ( ph -> M e. ( X H Y ) ) $.
    functhinclem3.g $e |- ( ph -> G = ( x e. B , y e. B |->
            ( ( x H y ) X. ( ( F ` x ) J ( F ` y ) ) ) ) ) $.
    functhinclem3.1 $e |- ( ph
              -> ( ( ( F ` X ) J ( F ` Y ) ) = (/) -> ( X H Y ) = (/) ) ) $.
    functhinclem3.2 $e |- ( ph -> E* n n e. ( ( F ` X ) J ( F ` Y ) ) ) $.
    $( Lemma for ~ functhinc .  The mapped morphism is in its corresponding
       hom-set.  (Contributed by Zhi Wang, 1-Oct-2024.) $)
    functhinclem3 $p |- ( ph ->
        ( ( X G Y ) ` M ) e. ( ( F ` X ) J ( F ` Y ) ) ) $=
      ( co cfv wf cxp wceq cv wa simprl simprr oveq12d fveq2d xpeq12d wcel ovex
      cvv xpex a1i ovmpod eqid mofeu mpbird ffvelcdmd ) AKLHSZKFTZLFTZISZJKLGSZ
      AVAVDVEUAVEVAVDUBZUCABCKLDDBUDZCUDZHSZVGFTZVHFTZISZUBVFGUMPAVGKUCZVHLUCZU
      EUEZVIVAVLVDVOVGKVHLHAVMVNUFZAVMVNUGZUHVOVJVBVKVCIVOVGKFVPUIVOVHLFVQUIUHU
      JMNVFUMUKAVAVDKLHULVBVCIULUNUOUPAEVAVDVEVFVFUQQRURUSOUT $.
  $}

  ${
    functhinc.b $e |- B = ( Base ` D ) $.
    functhinc.c $e |- C = ( Base ` E ) $.
    functhinc.h $e |- H = ( Hom ` D ) $.
    functhinc.j $e |- J = ( Hom ` E ) $.
    functhinc.d $e |- ( ph -> D e. Cat ) $.
    functhinc.e $e |- ( ph -> E e. ThinCat ) $.
    functhinc.f $e |- ( ph -> F : B --> C ) $.
    functhinc.k $e |- K = ( x e. B , y e. B |->
        ( ( x H y ) X. ( ( F ` x ) J ( F ` y ) ) ) ) $.
    functhinc.1 $e |- ( ph -> A. z e. B A. w e. B
        ( ( ( F ` z ) J ( F ` w ) ) = (/) -> ( z H w ) = (/) ) ) $.
    ${
      $d B b c m n p $.  $d B b c m n u v $.  $d B b c w z $.  $d B u v x y $.
      $d C p $.  $d E p $.  $d F p $.  $d F u v x y $.  $d F w z $.
      $d G a b c m n p $.  $d G a b c m n u v $.  $d H n p $.  $d H n u v $.
      $d H w z $.  $d H u v x y $.  $d J p $.  $d J u v x y $.  $d J w z $.
      $d K a b c m n p $.  $d K a b c m n u v $.  $d a b c m n p ph $.
      $d a b c w z $.  $d ph u v $.
      functhinclem4.1 $e |- .1. = ( Id ` D ) $.
      functhinclem4.i $e |- I = ( Id ` E ) $.
      functhinclem4.x $e |- .x. = ( comp ` D ) $.
      functhinclem4.o $e |- O = ( comp ` E ) $.
      $( Lemma for ~ functhinc .  Other requirements on the morphism part are
         automatically satisfied.  (Contributed by Zhi Wang, 1-Oct-2024.) $)
      functhinclem4 $p |- ( ( ph /\ G = K ) -> A. a e. B
                   ( ( ( a G a ) ` ( .1. ` a ) ) = ( I ` ( F ` a ) ) /\
       A. b e. B A. c e. B A. m e. ( a H b ) A. n e. ( b H c )
       ( ( a G c ) ` ( n ( <. a , b >. .x. c ) m ) ) =
       ( ( ( b G c ) ` n )
         ( <. ( F ` a ) , ( F ` b ) >. O ( F ` c ) )
                                               ( ( a G b ) ` m ) ) ) ) $=
        ( vv vu vp wceq wa cv cfv co cop wral cthinc ad2antrr adantr ffvelcdmda
        wcel wf simpr ccat catidcl cmpo simplr oveq1 fveq2 oveq1d xpeq12d oveq2
        oveq2d cbvmpov eqtri eqtrdi functhinclem2 thincmo functhinclem3 thincid
        c0 wi ad4antr simplrr ffvelcdmd simplrl simprl simprr catcocl thinccatd
        cxp thincmo2 ralrimivva jca ralrimiva ) AOSUTZVAZUAVBZJVCZXHXHOVDVCZXHN
        VCZQVCUTZLVBZKVBZXHUBVBZVEUCVBZIVDVDZXHXPOVDVCZXMXOXPOVDVCZXNXHXOOVDVCZ
        XKXONVCZVEXPNVCZTVDVDZUTZLXOXPPVDZVFKXHXOPVDZVFZUCFVFUBFVFZVAUAFXGXHFVK
        ZVAZXLYHYJGMQXJRXKAMVGVKZXFYIUIVHZUEUGXGFGXHNAFGNVLZXFUJVIVJZUNYJUQURFU
        SNOPRXIXHXHXGYIVMZYOYJFHJPXHUDUFUMAHVNVKZXFYIUHVHYOVOYJOSUQURFFUQVBZURV
        BZPVDZYQNVCZYRNVCZRVDZXAZVPZAXFYIVQSBCFFBVBZCVBZPVDZUUENVCZUUFNVCZRVDZX
        AZVPUUDUKBCUQURFFUUKUUCYQUUFPVDZYTUUIRVDZXAUUEYQUTZUUGUULUUJUUMUUEYQUUF
        PVRUUNUUHYTUUIRUUEYQNVSVTWAUUFYRUTZUULYSUUMUUBUUFYRYQPWBUUOUUIUUAYTRUUF
        YRNVSWCWAWDWEWFZYJDEFNPRXHXHYOYOADVBZNVCEVBZNVCRVDWKUTUUQUURPVDWKUTWLEF
        VFDFVFZXFYIULVHWGYJGMUSRXKXKYLYNYNUEUGWHWIWJYJYGUBUCFFYJXOFVKZXPFVKZVAZ
        VAZYDKLYFYEUVCXNYFVKZXMYEVKZVAZVAZGMXRYCRXKYBYJXKGVKUVBUVFYNVHZUVGFGXPN
        AYMXFYIUVBUVFUJWMZYJUUTUVAUVFWNZWOZUVGUQURFUSNOPRXQXHXPYJYIUVBUVFYOVHZU
        VJUVGFHIXNXMPXHXOXPUDUFUOAYPXFYIUVBUVFUHWMUVLYJUUTUVAUVFWPZUVJUVCUVDUVE
        WQZUVCUVDUVEWRZWSYJOUUDUTUVBUVFUUPVHZUVGDEFNPRXHXPUVLUVJAUUSXFYIUVBUVFU
        LWMZWGUVGGMUSRXKYBAYKXFYIUVBUVFUIWMZUVHUVKUEUGWHWIUVGGMTXTXSRXKYAYBUEUG
        UPYJMVNVKUVBUVFYJMYLWTVHUVHUVGFGXONUVIUVMWOZUVKUVGUQURFUSNOPRXNXHXOUVLU
        VMUVNUVPUVGDEFNPRXHXOUVLUVMUVQWGUVGGMUSRXKYAUVRUVHUVSUEUGWHWIUVGUQURFUS
        NOPRXMXOXPUVMUVJUVOUVPUVGDEFNPRXOXPUVMUVJUVQWGUVGGMUSRYAYBUVRUVSUVKUEUG
        WHWIWSUEUGUVRXBXCXCXDXE $.
    $}

    $d F a b c f g $.  $d F c u v w z $.  $d F u v x y $.  $d G a b c f g $.
    $d G c u v $.  $d H a b c f g $.  $d H c u v w z $.  $d H u v x y $.
    $d J a b c w z $.  $d J c u v w z $.  $d J u v x y $.  $d K a b c f g $.
    $d K c u v $.  $d B a b c f g $.  $d B c u v w z $.  $d B u v x y $.
    $d D a b c f g $.  $d E a b c f g $.  $d a b c f g ph $.  $d ph u v $.
    $( A functor to a thin category is determined entirely by the object part.
       The hypothesis "functhinc.1" is related to a monotone function if
       preorders induced by the categories are considered ( ~ catprs2 ), and
       can be obtained from ~ funcf2 , ~ f002 , and ~ ralrimivva .
       (Contributed by Zhi Wang, 1-Oct-2024.) $)
    functhinc $p |- ( ph -> ( F ( D Func E ) G <-> G = K ) ) $=
      ( va vg vf vb vc vv vu cfunc co wbr wceq cv ccid cfv cop cco wral wa c1st
      cxp c2nd cmap cixp wcel w3a eqid thinccatd isfunc 3anass mpbirand cvv wfn
      wf bitrdi funcf2lem simprl simprr c0 wi functhinclem2 functhinclem1 bitrd
      adantr bitrid anbi1d functhinclem4 mpbiran3d ) AJKHIUKULUMZKNUNZUDUOZHUPU
      QZUQWMWMKULUQWMJUQZIUPUQZUQUNUEUOZUFUOZWMUGUOZURUHUOZHUSUQZULULWMWTKULUQW
      QWSWTKULUQWRWMWSKULUQWOWSJUQURWTJUQIUSUQZULULUNUEWSWTLULUTUFWMWSLULUTUHFU
      TUGFUTVAUDFUTZAWKKUHFFVCZWTVBUQJUQWTVDUQJUQMULWTLUQVEULVFVGZXCVAZWLXCVAAW
      KFGJVPZXFUAAWKXGXEXCVHXGXFVAAUDUGUHFGHXAWNUFUEIJKLWPMXBOPQRWNVIZWPVIZXAVI
      ZXBVIZSAITVJVKXGXEXCVLVQVMAXEWLXCXEKVNVGKXDVOUIUOZUJUOZLULXLJUQXMJUQMULXL
      XMKULVPUJFUTUIFUTVHAWLUIUJUHFJKLMVRABCUIUJFGHIJKLMNOPQRTUAUBAXLFVGZXMFVGZ
      VAZVADEFJLMXLXMAXNXOVSAXNXOVTADUOZJUQEUOZJUQMULWAUNXQXRLULWAUNWBEFUTDFUTX
      PUCWFWCWDWGWHWEABCDEFGHXAWNUFUEIJKLWPMNXBUDUGUHOPQRSTUAUBUCXHXIXJXKWIWJ
      $.
  $}

  ${
    $d C f g h x y $.  $d D f g h x y $.  $d f g h ph x y $.
    functhincfun.d $e |- ( ph -> C e. Cat ) $.
    functhincfun.e $e |- ( ph -> D e. ThinCat ) $.
    $( A functor to a thin category is determined entirely by the object part.
       (Contributed by Zhi Wang, 16-Oct-2025.) $)
    functhincfun $p |- ( ph -> Fun ( C Func D ) ) $=
      ( vf vg vh vx vy co cv wbr wa wceq wi wal cfv eqid wcel wrel wfun relfunc
      cfunc cbs chom cxp cmpo simprl ccat adantr cthinc funcf1 c0 simprr funcf2
      simplrl f002 ralrimivva functhinc mpbid eqtr4d ex alrimivv alrimiv dffun2
      biimpri sylancr ) ABCUDKZUAZFLZGLZVIMZVKHLZVIMZNZVLVNOZPZHQGQZFQZVIUBZBCU
      CAVSFAVRGHAVPVQAVPNZVLIJBUERZWCILZJLZBUFRZKZWDVKRWEVKRCUFRZKZUGUHZVNWBVMV
      LWJOAVMVOUIZWBIJIJWCCUERZBCVKVLWFWHWJWCSZWLSZWFSZWHSZABUJTVPDUKZACULTVPEU
      KZWBWCWLBCVKVLWMWNWKUMZWJSZWBWIUNOWGUNOPIJWCWCWBWDWCTZWEWCTZNZNZWGWIWDWEV
      LKXDWCBCVKVLWFWHWDWEWMWOWPAVMVOXCUQWBXAXBUIWBXAXBUOUPURUSZUTVAWBVOVNWJOAV
      MVOUOWBIJIJWCWLBCVKVNWFWHWJWMWNWOWPWQWRWSWTXEUTVAVBVCVDVEWAVJVTNFGHVIVFVG
      VH $.
  $}

  ${
    $d B f x y $.  $d C f x y $.  $d D f x y $.  $d F f x y $.  $d G f x y $.
    $d H f x y $.  $d J f x y $.  $d X x y $.  $d Y x y $.
    fullthinc.b $e |- B = ( Base ` C ) $.
    fullthinc.j $e |- J = ( Hom ` D ) $.
    fullthinc.h $e |- H = ( Hom ` C ) $.
    fullthinc.d $e |- ( ph -> D e. ThinCat ) $.
    ${
      fullthinc.f $e |- ( ph -> F ( C Func D ) G ) $.
      $( A functor to a thin category is full iff empty hom-sets are mapped to
         empty hom-sets.  (Contributed by Zhi Wang, 1-Oct-2024.) $)
      fullthinc $p |- ( ph -> ( F ( C Full D ) G
                        <-> A. x e. B A. y e. B ( ( x H y ) = (/) ->
                ( ( F ` x ) J ( F ` y ) ) = (/) ) ) ) $=
        ( vf co c0 wceq wa cthinc wcel cfunc wbr cful cv cfv wi wral wb isfull2
        foeq2 fo00 simprbi biimtrdi com12 2ralimi simplbiim adantl simplr wn wo
        wfo csn wex wf wne weu simprl simprr funcf2 adantr simpr neqned fdomne0
        imor syl2anc simprd cbs simplll eqid ffvelcdmd eqidd chom a1i thincn0eu
        funcf1 mpbid eusn sylib simpld foconst feq3 anbi1d foeq3 imbi12d mpbiri
        exlimiv imp syl12anc f00 biimpri imbitrrid jaodan ex ralimdvva sylanbrc
        sylan2b impbida ) AFUAUBZGHEFUCQUDZGHEFUEQUDZBUFZCUFZIQZRSZXMGUGZXNGUGZ
        JQZRSZUHZCDUIBDUIZUJNOXJXKTZXLYBXLYBYCXLXKXOXSXMXNHQZVCZCDUIBDUIZYBBCDE
        FGHIJKLMUKZYEYABCDDXPYEXTXPYERXSYDVCZXTXORXSYDULZYHYDRSZXTXSYDUMZUNUOUP
        UQURUSYCYBTXKYFXLXJXKYBUTYCYBYFYCYAYEBCDDYCXMDUBZXNDUBZTZTZYAYEYAYOXPVA
        ZXTVBYEXPXTVPYOYPYEXTYOYPTZXSPUFZVDZSZPVEZXOXSYDVFZYDRVGZYEYQYRXSUBPVHZ
        UUAYQXSRVGZUUDYQUUCUUEYQUUBXORVGUUCUUETYOUUBYPYODEFGHIJXMXNKMLXJXKYNUTZ
        YCYLYMVIZYCYLYMVJZVKZVLZYQXORYOYPVMVNYDXOXSVOVQZVRYQFVSUGZFPJXQXRXJXKYN
        YPVTYQDUULXMGYQDUULEFGHKUULWAYOXKYPUUFVLWGZYOYLYPUUGVLWBYQDUULXNGUUMYOY
        MYPUUHVLWBYQUULWCJFWDUGSYQLWEWFWHPXSWIWJUUJYQUUCUUEUUKWKUUAUUBUUCTZYEYT
        UUNYEUHZPYTUUOXOYSYDVFZUUCTZXOYSYDVCZUHXOYRYDWLYTUUNUUQYEUURYTUUBUUPUUC
        XSYSXOYDWMWNXSYSXOYDWOWPWQWRWSWTYOXTTZXPYJXTYEUUSYJXPUUSXORYDVFZYJXPTUU
        SUUBUUTYOUUBXTUUIVLXTUUBUUTUJYOXSRXOYDWMUSWHXOYDXAWJZVRUUSYJXPUVAWKYOXT
        VMXPYJXTTZYEUVBYEXPYHYHUVBYKXBYIXCWSWTXDXHXEXFWSYGXGXIVQ $.
    $}

    ${
      fullthinc2.f $e |- ( ph -> F ( C Full D ) G ) $.
      fullthinc2.x $e |- ( ph -> X e. B ) $.
      fullthinc2.y $e |- ( ph -> Y e. B ) $.
      $( A full functor to a thin category maps empty hom-sets to empty
         hom-sets.  (Contributed by Zhi Wang, 1-Oct-2024.) $)
      fullthinc2 $p |- ( ph -> ( ( X H Y ) = (/) <->
                ( ( F ` X ) J ( F ` Y ) ) = (/) ) ) $=
        ( co c0 wceq vx vy cfv wcel cv wral cful cfunc fullfunc ssbri fullthinc
        wi wbr syl mpbid oveq12 eqeq1d simpl fveq2d oveq12d imbi12d rspc2gv imp
        wa simpr syl21anc funcf2 f002 impbid ) AIJGRZSTZIEUCZJEUCZHRZSTZAIBUDZJ
        BUDZUAUEZUBUEZGRZSTZVREUCZVSEUCZHRZSTZULZUBBUFUABUFZVKVOULZPQAEFCDUGRZU
        MZWGOAUAUBBCDEFGHKLMNAWJEFCDUHRZUMOWIWKEFCDUIUJUNZUKUOVPVQVDWGWHWFWHUAU
        BIJBBVRITZVSJTZVDZWAVKWEVOWOVTVJSVRIVSJGUPUQWOWDVNSWOWBVLWCVMHWOVRIEWMW
        NURUSWOVSJEWMWNVEUSUTUQVAVBVCVFAVJVNIJFRABCDEFGHIJKMLWLPQVGVHVI $.
    $}
  $}

  ${
    $d C f x y $.  $d D f x y $.  $d F f x y $.  $d G f x y $.  $d f ph x y $.
    thincfth.c $e |- ( ph -> C e. ThinCat ) $.
    thincfth.f $e |- ( ph -> F ( C Func D ) G ) $.
    $( A functor from a thin category is faithful.  (Contributed by Zhi Wang,
       1-Oct-2024.) $)
    thincfth $p |- ( ph -> F ( C Faith D ) G ) $=
      ( vx vy vf co wbr cv chom cfv wral wcel wa adantr eqid cfunc wf1 cbs cfth
      wmo wf cthinc simprl simprr thincmo funcf2 f1mo syl2anc ralrimivva isfth2
      sylanbrc ) ADEBCUAKLZHMZIMZBNOZKZURDOUSDOCNOZKZURUSEKZUBZIBUCOZPHVFPDEBCU
      DKLGAVEHIVFVFAURVFQZUSVFQZRZRZJMVAQJUEVAVCVDUFVEVJVFBJUTURUSABUGQVIFSAVGV
      HUHZAVGVHUIZVFTZUTTZUJVJVFBCDEUTVBURUSVMVNVBTZAUQVIGSVKVLUKJVAVCVDULUMUNH
      IVFBCDEUTVBVMVNVOUOUP $.
  $}

  ${
    $d C a f w x y z $.  $d H a f w x y z $.  $d J a f w x y z $.
    $d R a f w x y z $.  $d S a f w z $.  $d X a f w x y z $.
    $d Y a f w x y z $.  $d a f ph w x y z $.
    thincciso.c $e |- C = ( CatCat ` U ) $.
    thincciso.b $e |- B = ( Base ` C ) $.
    thincciso.r $e |- R = ( Base ` X ) $.
    thincciso.s $e |- S = ( Base ` Y ) $.
    thincciso.h $e |- H = ( Hom ` X ) $.
    thincciso.j $e |- J = ( Hom ` Y ) $.
    thincciso.u $e |- ( ph -> U e. V ) $.
    thincciso.x $e |- ( ph -> X e. B ) $.
    thincciso.y $e |- ( ph -> Y e. B ) $.
    thincciso.xt $e |- ( ph -> X e. ThinCat ) $.
    thincciso.yt $e |- ( ph -> Y e. ThinCat ) $.
    $( Two thin categories are isomorphic iff the induced preorders are
       order-isomorphic.  Example 3.26(2) of [Adamek] p. 33.  Note that
       "thincciso.u" is redundant thanks to ~ elbasfv .  (Contributed by Zhi
       Wang, 16-Oct-2024.) $)
    thincciso $p  |- ( ph -> ( X ( ~=c ` C ) Y <-> E. f (
    A. x e. R A. y e. R ( ( x H y ) = (/) <-> ( ( f ` x ) J ( f ` y ) ) = (/) )
    /\ f : R -1-1-onto-> S ) ) ) $=
      ( va vz vw ccic cfv wbr cv ciso co wcel c0 wceq wb wral wf1o wa eqid ccat
      wex catccat syl cic cxp cmpo cop cvv opex a1i cful cfth cin c1st wi biimp
      2ralimi ad2antrl cthinc adantr cfunc thinccatd wf simprr biimpr functhinc
      f1of mpbiri fullthinc mpbird df-br sylib thincfth elind fvexi mpoex op1st
      vex cbs f1oeq1 ax-mp sylibr jca catciso biimpar syldan eleq1 spcedv fvexd
      ex exlimdv c2nd wrel relfull biimpa simpld elin1d 1st2ndbr fullfunc ssbri
      sylancr mpbid simprl funcf2 f002 ralrimivva 2ralbiim simprd fveq1 oveq12d
      sylanbrc eqeq1d bibi2d 2ralbidv anbi12d impbid bitr4d ) AMNEUIUJUKUFULZMN
      EUMUJZUNZUOZUFVDZBULZCULZJUNZUPUQZUUFIULZUJZUUGUUJUJZKUNZUPUQZURZCFUSBFUS
      ZFGUUJUTZVAZIVDZADEUFUUBMNUUBVBZPAHLUOEVCUOUAEHLOVEVFUBUCVGAUUSUUEAUURUUE
      IAUURUUEAUURVAZUUDUUJUGUHFFUGULZUHULZJUNUVBUUJUJUVCUUJUJKUNVHZVIZVJZUUCUO
      ZUFVKUVFUVFVKUOUVAUUJUVEVLVMAUURUVFMNVNUNZMNVOUNZVPZUOZFGUVFVQUJZUTZVAZUV
      GUVAUVKUVMUVAUVHUVIUVFUVAUUJUVEUVHUKZUVFUVHUOUVAUVOUUIUUNVRZCFUSBFUSZUUPU
      VQAUUQUUOUVPBCFFUUIUUNVSVTWAUVABCFMNUUJUVEJKQTSANWBUOZUURUEWCZUVAUUJUVEMN
      WDUNZUKUVEUVEUQUVEVBZUVAUGUHBCFGMNUUJUVEJKUVEQRSTUVAMAMWBUOUURUDWCZWEUVSU
      VAUUQFGUUJWFAUUPUUQWGZFGUUJWJVFUWAUUPUUNUUIVRZCFUSBFUSAUUQUUOUWDBCFFUUIUU
      NWHVTWAWIWKZWLWMUUJUVEUVHWNWOUVAUUJUVEUVIUKUVFUVIUOUVAMNUUJUVEUWBUWEWPUUJ
      UVEUVIWNWOWQUVAUUQUVMUWCUVLUUJUQUVMUUQURUUJUVEIXAUGUHFFUVDFMXBQWRZUWFWSWT
      FGUVLUUJXCXDXEXFAUVGUVNADEFGHUVFUUBLMNOPQRUAUBUCUUTXGXHXIUUAUVFUUCXJXKXMX
      NAUUDUUSUFAUUDUUSAUUDVAZUURUUIUUFUUAVQUJZUJZUUGUWHUJZKUNZUPUQZURZCFUSBFUS
      ZFGUWHUTZVAIVKUWHUWGUUAVQXLUWGUWNUWOUWGUUIUWLVRCFUSBFUSZUWLUUIVRZCFUSBFUS
      UWNUWGUWHUUAXOUJZUVHUKZUWPUWGUVHXPUUAUVHUOUWSMNXQUWGUVHUVIUUAUWGUUAUVJUOZ
      UWOAUUDUWTUWOVAADEFGHUUAUUBLMNOPQRUAUBUCUUTXGXRZXSXTUUAUVHYAYDZUWGBCFMNUW
      HUWRJKQTSAUVRUUDUEWCUWGUWSUWHUWRUVTUKZUXBUVHUVTUWHUWRMNYBYCVFZWLYEUWGUWQB
      CFFUWGUUFFUOZUUGFUOZVAZVAZUUHUWKUUFUUGUWRUNUXHFMNUWHUWRJKUUFUUGQSTUWGUXCU
      XGUXDWCUWGUXEUXFYFUWGUXEUXFWGYGYHYIUUIUWLBCFFYJYNUWGUWTUWOUXAYKXFUUJUWHUQ
      ZUUPUWNUUQUWOUXIUUOUWMBCFFUXIUUNUWLUUIUXIUUMUWKUPUXIUUKUWIUULUWJKUUFUUJUW
      HYLUUGUUJUWHYLYMYOYPYQFGUUJUWHXCYRXKXMXNYSYT $.
  $}

  ${
    $d C f x y $.  $d F f x y $.  $d H f x y $.  $d J f x y $.  $d R f x y $.
    $d S f $.  $d U f $.  $d V f $.  $d X f x y $.  $d Y f x y $.
    $d f ph x y $.
    thinccisod.c $e |- C = ( CatCat ` U ) $.
    thinccisod.r $e |- R = ( Base ` X ) $.
    thinccisod.s $e |- S = ( Base ` Y ) $.
    thinccisod.h $e |- H = ( Hom ` X ) $.
    thinccisod.j $e |- J = ( Hom ` Y ) $.
    thinccisod.u $e |- ( ph -> U e. V ) $.
    thinccisod.x $e |- ( ph -> X e. U ) $.
    thinccisod.y $e |- ( ph -> Y e. U ) $.
    thinccisod.xt $e |- ( ph -> X e. ThinCat ) $.
    thinccisod.yt $e |- ( ph -> Y e. ThinCat ) $.
    thinccisod.f $e |- ( ph -> F : R -1-1-onto-> S ) $.
    thinccisod.1 $e |- ( ( ph /\ ( x e. R /\ y e. R ) ) ->
            ( ( x H y ) = (/) <-> ( ( F ` x ) J ( F ` y ) ) = (/) ) ) $.
    $( Two thin categories are isomorphic if the induced preorders are
       order-isomorphic (deduction form).  Example 3.26(2) of [Adamek] p. 33.
       (Contributed by Zhi Wang, 22-Sep-2025.) $)
    thinccisod $p  |- ( ph -> X ( ~=c ` C ) Y ) $=
      ( vf ccic cfv wbr cv co c0 wceq wb wral wf1o wa wex cvv wf f1of syl fvexd
      cbs eqeltrid fexd ralrimivva fveq1 oveq12d eqeq1d bibi2d 2ralbidv anbi12d
      jca f1oeq1 spcedv eqid ccat cin thinccatd elind eleqtrrd thincciso mpbird
      catcbas ) ALMDUGUHUIBUJZCUJZIUKULUMZWFUFUJZUHZWGWIUHZJUKZULUMZUNZCEUOBEUO
      ZEFWIUPZUQZUFURAWQWHWFHUHZWGHUHZJUKZULUMZUNZCEUOBEUOZEFHUPZUQUFUSHAEFUSHA
      XDEFHUTUDEFHVAVBAELVDUHUSOALVDVCVEVFAXCXDAXBBCEEUEVGUDVNWIHUMZWOXCWPXDXEW
      NXBBCEEXEWMXAWHXEWLWTULXEWJWRWKWSJWFWIHVHWGWIHVHVIVJVKVLEFWIHVOVMVPABCDVD
      UHZDEFGUFIJKLMNXFVQZOPQRSALGVRVSZXFAGVRLTALUBVTWAAXFDGKNXGSWEZWBAMXHXFAGV
      RMUAAMUCVTWAXIWBUBUCWCWD $.
  $}

  ${
    $d B f x y $.  $d C f x y $.  $d F f x y $.  $d I f x y $.  $d U f x y $.
    $d V f x y $.  $d X f x y $.  $d Y f x y $.  $d f ph x y $.
    thincciso2.c $e |- C = ( CatCat ` U ) $.
    thincciso2.b $e |- B = ( Base ` C ) $.
    thincciso2.u $e |- ( ph -> U e. V ) $.
    thincciso2.x $e |- ( ph -> X e. B ) $.
    thincciso2.y $e |- ( ph -> Y e. B ) $.
    ${
      thincciso2.i $e |- I = ( Iso ` C ) $.
      thincciso2.f $e |- ( ph -> F e. ( X I Y ) ) $.
      ${
        thincciso2.yt $e |- ( ph -> Y e. ThinCat ) $.
        $( Categories isomorphic to a thin category are thin.  Example 3.26(2)
           of [Adamek] p. 33.  Note that "thincciso2.u" is redundant thanks to
           ~ elbasfv .  (Contributed by Zhi Wang, 18-Oct-2025.) $)
        thincciso2 $p |- ( ph -> X e. ThinCat ) $=
          ( vf cfv wcel vx vy cbs chom eqidd cv wa co c1o cdom wbr wmo c1st cen
          c2nd wf1o wral cfunc cful cfth wrel relfull relin1 ax-mp eqid catciso
          cin mpbid simpld 1st2ndbr sylancr isffth2 simprd r19.21bi anasss ovex
          sylib cthinc adantr funcf1 ffvelcdmda adantrr adantrl thincmo endomtr
          f1oen syl modom2 syl2anc sylibr funcrcl2 isthincd ) AUAUBHUCSZHRHUDSZ
          AWMUEAWNUEAUAUFZWMTZUBUFZWMTZUGZUGZWOWQWNUHZUIUJUKZRUFZXATRULWTXAWOEU
          MSZSZWQXDSZIUDSZUHZUNUKZXHUIUJUKZXBWTXAXHWOWQEUOSZUHZUPZXIAWPWRXMAWPU
          GXMUBWMAXMUBWMUQZUAWMAXDXKHIURUHUKZXNUAWMUQZAXDXKHIUSUHZHIUTUHZVGZUKZ
          XOXPUGAXSVAZEXSTZXTXQVAYAHIVBXQXRVCVDAYBWMIUCSZXDUPZAEHIFUHTYBYDUGPAB
          CWMYCDEFGHIJKWMVEZYCVEZLMNOVFVHVIEXSVJVKUAUBWMHIXDXKWNXGYEWNVEXGVEZVL
          VQZVMVNVNVOXAXHXLWOWQWNVPWFWGWTXCXHTRULXJWTYCIRXGXEXFAIVRTWSQVSAWPXEY
          CTWRAWMYCWOXDAWMYCHIXDXKYEYFAXOXPYHVIZVTZWAWBAWRXFYCTWPAWMYCWQXDYJWAW
          CYFYGWDRXHWHVQXAXHUIWEWIRXAWHWJAHIXDXKYIWKWL $.
      $}

      ${
        thincciso3.xt $e |- ( ph -> X e. ThinCat ) $.
        $( Categories isomorphic to a thin category are thin.  Example 3.26(2)
           of [Adamek] p. 33.  Note that "thincciso2.u" is redundant thanks to
           ~ elbasfv .  (Contributed by Zhi Wang, 18-Oct-2025.) $)
        thincciso3 $p |- ( ph -> Y e. ThinCat ) $=
          ( cfv co wcel cinv eqid ccat catccat syl invf ffvelcdmd thincciso2 )
          ABCDEHICUARZSZRFGIHJKLNMOAHIFSIHFSEUJABCFUIHIKUIUBADGTCUCTLCDGJUDUEMN
          OUFPUGQUH $.
      $}
    $}

    thincciso4.i $e |- ( ph -> X ( ~=c ` C ) Y ) $.
    $( Two isomorphic categories are either both thin or neither.  Note that
       "thincciso2.u" is redundant thanks to ~ elbasfv .  (Contributed by Zhi
       Wang, 18-Oct-2025.) $)
    thincciso4 $p |- ( ph -> ( X e. ThinCat <-> Y e. ThinCat ) ) $=
      ( vf cthinc wcel wa cfv adantr ad2antrr cv ciso co wex ccic wbr eqid ccat
      catccat syl cic mpbid simpr simplr thincciso3 exlimddv thincciso2 impbida
      ) AFOPZGOPZAUSQZNUAZFGCUBRZUCPZUTNAVDNUDZUSAFGCUERUFVEMABCNVCFGVCUGZIADEP
      ZCUHPJCDEHUIUJKLUKULZSVAVDQBCDVBVCEFGHIAVGUSVDJTAFBPZUSVDKTAGBPZUSVDLTVFV
      AVDUMAUSVDUNUOUPAUTQZVDUSNAVEUTVHSVKVDQBCDVBVCEFGHIAVGUTVDJTAVIUTVDKTAVJU
      TVDLTVFVKVDUMAUTVDUNUQUPUR $.
  $}

  ${
    $d C f x y $.
    $( Any structure with an empty set of objects is a thin category.
       (Contributed by Zhi Wang, 17-Sep-2024.) $)
    0thincg $p |- ( ( C e. V /\ (/) = ( Base ` C ) ) -> C e. ThinCat ) $=
      ( vf vx vy wcel c0 cbs cfv wceq wa ccat cv chom co wral cthinc 0catg eqid
      wmo ral0 raleq mpbii adantl isthinc sylanbrc ) ABFZGAHIZJZKALFCMDMEMANIZO
      FCTEUHPZDUHPZAQFABRUIULUGUIUKDGPULUKDUAUKDGUHUBUCUDDEUHACUJUHSUJSUEUF $.
  $}

  $( The empty category (see ~ 0cat ) is thin.  (Contributed by Zhi Wang,
     17-Sep-2024.) $)
  0thinc $p |- (/) e. ThinCat $=
    ( c0 cvv wcel cbs cfv wceq cthinc 0ex base0 0thincg mp2an ) ABCAADEFAGCHIAB
    JK $.

  ${
    $d B f i y $.  $d C f i x y $.  $d F f $.  $d H f i $.  $d I i $.
    $d f i ph x y $.
    indcthing.b $e |- ( ph -> B = ( Base ` C ) ) $.
    indcthing.h $e |- ( ph -> H = ( Hom ` C ) ) $.
    indcthing.c $e |- ( ph -> C e. Cat ) $.
    ${
      indcthing.i $e |- ( ( ph /\ ( x e. B /\ y e. B ) )
        -> ( x H y ) = { F } ) $.
      $( An indiscrete category, i.e., a category where all hom-sets have
         exactly one morphism, is thin.  (Contributed by Zhi Wang,
         11-Nov-2025.) $)
      indcthing $p |- ( ph -> C e. ThinCat ) $=
        ( vf cv wcel wa co wmo csn wceq eqid mosn eleq2d mobidv mpbiri isthincd
        ax-mp ) ABCDELGHIABMZDNCMZDNOOZLMZUGUHGPZNZLQUJFRZNZLQZUMUMSUOUMTLUMFUA
        UFUIULUNLUIUKUMUJKUBUCUDJUE $.
    $}

    ${
      discthing.i $e |- ( ( ph /\ ( x e. B /\ y e. B ) )
        -> ( x H y ) = if ( x = y , { I } , (/) ) ) $.
      $( A discrete category, i.e., a category where all morphisms are identity
         morphisms, is thin.  Example 3.26(1) of [Adamek] p. 33.  (Contributed
         by Zhi Wang, 11-Nov-2025.) $)
      discthing $p |- ( ph -> C e. ThinCat ) $=
        ( vi cv wcel wa wmo wceq c0 eleq2w2 mobidv co csn cif eqid mosn mp1i wn
        mo0 ifbothda eleq2d mpbird isthincd ) ABCDELFHIABMZDNCMZDNOOZLMZUMUNFUA
        ZNZLPUPUMUNQZGUBZRUCZNZLPZUSUPUTNZLPZUPRNZLPZVCUOUTRUTVAQVDVBLLUTVASTRV
        AQVFVBLLRVASTUTUTQVEUOUSOUTUDLUTGUEUFRRQVGUOUSUGORUDLRUHUFUIUOURVBLUOUQ
        VAUPKUJTUKJUL $.
    $}
  $}

  ${
    $d .<_ f g x y z $.  $d B f g x y z $.  $d C f g x y z $.
    $d f g ph x y z $.
    indthinc.b $e |- ( ph -> B = ( Base ` C ) ) $.
    ${
      indthinc.h $e |- ( ph -> ( ( B X. B ) X. { 1o } ) = ( Hom ` C ) ) $.
      indthinc.o $e |- ( ph -> (/) = ( comp ` C ) ) $.
      indthinc.c $e |- ( ph -> C e. V ) $.
      $( An indiscrete category in which all hom-sets have exactly one morphism
         is a thin category.  Constructed here is an indiscrete category where
         all morphisms are ` (/) ` .  This is a special case of ~ prsthinc ,
         where ` .<_ = ( B X. B ) ` .  This theorem also implies a functor from
         the category of sets to the category of small categories.
         (Contributed by Zhi Wang, 17-Sep-2024.)  (Proof shortened by Zhi Wang,
         19-Sep-2024.) $)
      indthinc $p |- ( ph
                   -> ( C e. ThinCat /\ ( Id ` C ) = ( y e. B |-> (/) ) ) ) $=
        ( vx vz vf vg cv wcel c1o co wa c0 wceq w3a cxp csn cop cfv eqidd f1omo
        wmo df-ov eleq2i mobii sylibr biid id ancli ovconst2 0lt1o eleq2 mpbiri
        1oex 3syl adantl a1i 0ov oveqi eqtri 3adant2 3eltr4d ad2antrl isthincd2
        ) AJNZCOZBNZCOZKNZCOZUAZLNZVKVMCCUBZPUCUBZQZOZMNZVMVOVTQORZRZJBKCDSSLMV
        TEFGAVLVNRRZVRVKVMUDZVTUEZOZLUHWBLUHWFLVSVTWGWFVTUFUGWBWILWAWHVRVKVMVTU
        IUJUKULHIWEUMVNSVMVMVTQZOZAVNVNVNRWJPTZWKVNVNVNUNUOCCPVMVMUTUPWLWKSPOZU
        QWJPSURUSVAVBVQWCVRWGVOSQZQZVKVOVTQZOAWDVQSPWOWPWMVQUQVCWOSTVQWOWCVRSQS
        WNSWCVRWGVOVDVEWCVRVDVFVCVLVPWPPTVNCCPVKVOUTUPVGVHVIVJ $.

      $( An alternate proof of ~ indthinc assuming more axioms including
         ~ ax-pow and ~ ax-un .  (Contributed by Zhi Wang, 17-Sep-2024.)
         (Proof modification is discouraged.)  (New usage is discouraged.) $)
      indthincALT $p |- ( ph
                   -> ( C e. ThinCat /\ ( Id ` C ) = ( y e. B |-> (/) ) ) ) $=
        ( vf cv wcel c1o co wa c0 cdom 1oex ovconst2 wceq vx vz w3a cxp csn wmo
        vg wbr cvv domrefg ax-mp eqbrtrdi modom2 sylibr adantl biid ancli 0lt1o
        id eleq2 mpbiri 3syl cop a1i 0ov oveqi eqtri 3adant2 ad2antrl isthincd2
        3eltr4d ) AUAKZCLZBKZCLZUBKZCLZUCZJKZVLVNCCUDMUEUDZNZLZUGKZVNVPVTNLOZOZ
        UABUBCDPPJUGVTEFGVMVOOZWBJUFZAWFWAMQUHWGWFWAMMQCCMVLVNRSMUILMMQUHRMUIUJ
        UKULJWAUMUNUOHIWEUPVOPVNVNVTNZLZAVOVOVOOWHMTZWIVOVOVOUSUQCCMVNVNRSWJWIP
        MLZURWHMPUTVAVBUOVRWCVSVLVNVCZVPPNZNZVLVPVTNZLAWDVRPMWNWOWKVRURVDWNPTVR
        WNWCVSPNPWMPWCVSWLVPVEVFWCVSVEVGVDVMVQWOMTVOCCMVLVPRSVHVKVIVJ $.
    $}

    ${
      prsthinc.h $e |- ( ph -> ( .<_ X. { 1o } ) = ( Hom ` C ) ) $.
      prsthinc.o $e |- ( ph -> (/) = ( comp ` C ) ) $.
      prsthinc.l $e |- ( ph -> .<_ = ( le ` C ) ) $.
      prsthinc.p $e |- ( ph -> C e. Proset ) $.
      $( Preordered sets as categories.  Similar to example 3.3(4.d) of
         [Adamek] p. 24, but the hom-sets are not pairwise disjoint.  One can
         define a functor from the category of prosets to the category of small
         thin categories.  See ~ catprs and ~ catprs2 for inducing a preorder
         from a category.  Example 3.26(2) of [Adamek] p. 33 indicates that it
         induces a bijection from the equivalence class of isomorphic small
         thin categories to the equivalence class of order-isomorphic
         preordered sets.  (Contributed by Zhi Wang, 18-Sep-2024.) $)
      prsthinc $p |- ( ph
                   -> ( C e. ThinCat /\ ( Id ` C ) = ( y e. B |-> (/) ) ) ) $=
        ( vf cv wcel c1o co wa c0 wbr breqd a1i w3a csn cxp cproset cop cfv wmo
        vx vz vg eqidd f1omo df-ov eleq2i mobii sylibr biid 0lt1o wceq cple cbs
        eleq2d eqid prsref sylan sylbida biimpar syldan cvv 1oex wne ovconstbrd
        1n0 mpbid eleqtrrid 0ov oveqi eqtri eqeltri simpl adantr biimpa adantrr
        3anbi123d simprrl elovconstbrd biimpd simprrr prstr syl112anc isthincd2
        sylc biimprd ) AUHLZCMZBLZCMZUILZCMZUAZKLZWNWPENUBUCZOZMZUJLZWPWRXBOMZP
        ZPZUHBUICDQQKUJXBUDFGAWOWQPPZXAWNWPUEZXBUFZMZKUGXDKUGXIKEXBXJXIXBUKULXD
        XLKXCXKXAWNWPXBUMUNUOUPHJXHUQAWQPZQNWPWPXBOZURXMWPWPERZXNNUSAWQWPWPDUTU
        FZRZXOAWQWPDVAUFZMZXQACXRWPFVBZADUDMZXSXQJXRDXPWPXRVCZXPVCZVDVEVFAXOXQA
        EXPWPWPISVGVHXMWPWPEXBVINXMXBUKNVIMZXMVJTNQVKZXMVMTVLVNVOAXHPZXEXAXJWRQ
        OZOZNWNWRXBOZYHQNYHXEXAQOQYGQXEXAXJWRVPVQXEXAVPVRURVSYFWNWRERZYINUSYFAW
        NWRXPRZYJAXHVTZYFYAWNXRMZXSWRXRMZUAZWNWPXPRZWPWRXPRZYKAYAXHJWAAWTYOXGAW
        TYOAWOYMWQXSWSYNACXRWNFVBXTACXRWRFVBWDWBWCYFAWNWPERZYPYLYFWNWPEXBXANYFX
        BUKZAWTXDXFWEWFAYRYPAEXPWNWPISWGWLYFAWPWRERZYQYLYFWPWREXBXENYSAWTXDXFWH
        WFAYTYQAEXPWPWRISWGWLXRDXPWNWPWRYBYCWIWJAYJYKAEXPWNWRISWMWLYFWNWREXBVIN
        YSYDYFVJTYEYFVMTVLVNVOWK $.
    $}
  $}

  ${
    $d U f p x y z $.  $d f ph y z $.
    setcthin.c $e |- ( ph -> C = ( SetCat ` U ) ) $.
    setcthin.u $e |- ( ph -> U e. V ) $.
    setcthin.x $e |- ( ph -> A. x e. U E* p p e. x ) $.
    $( A category of sets all of whose objects contain at most one element is
       thin.  (Contributed by Zhi Wang, 20-Sep-2024.) $)
    setcthin $p |- ( ph -> C e. ThinCat ) $=
      ( vy vz vf cfv eqid cv wcel wa wmo mobidv adantr csetc chom setcbas eqidd
      cthinc co wf weq elequ2 wral simprr rspcdva mofmo simprl elsetchom mpbird
      syl ccat setccat isthincd eqeltrd ) ACDUAMZUEGAJKDVBLVBUBMZAVBDEVBNZHUCAV
      CUDAJOZDPZKOZDPZQZQZLOZVEVGVCUFPZLRVEVGVKUGZLRZVJFOZVGPZFRZVNVJVOBOPZFRZV
      QBDVGBKUHVRVPFBKFUISAVSBDUJVIITAVFVHUKZULFVEVGLUMUQVJVLVMLVJVBDVKVCEVEVGV
      DADEPZVIHTVCNAVFVHUNVTUOSUPAWAVBURPHVBDEVDUSUQUTVA $.
  $}

  ${
    $d x y z $.
    $( The category ` ( SetCat `` 2o ) ` is thin.  A special case of
       ~ setcthin .  (Contributed by Zhi Wang, 20-Sep-2024.) $)
    setc2othin $p |- ( SetCat ` 2o ) e. ThinCat $=
      ( vx vz vy c2o csetc cfv cthinc wcel wtru cvv eqidd 2oex a1i wmo wral csn
      cv c0 wceq wo cpr wex elpri 0ex sneq eqeq2d spcev orim2i mo0sn 3syl df2o2
      biimpri eleq2s rgen setcthin mptru ) DEFZGHIAUQDJBIUQKDJHILMBQAQZHBNZADOI
      USADUSURRRPZUAZDURVAHURRSZURUTSZTVBURCQZPZSZCUBZTZUSURRUTUCVCVGVBVFVCCRUD
      VDRSVEUTURVDRUEUFUGUHUSVHBCURUIULUJUKUMUNMUOUP $.
  $}

  ${
    thincsect.c $e |- ( ph -> C e. ThinCat ) $.
    thincsect.b $e |- B = ( Base ` C ) $.
    thincsect.x $e |- ( ph -> X e. B ) $.
    thincsect.y $e |- ( ph -> Y e. B ) $.
    ${
      thincsect.s $e |- S = ( Sect ` C ) $.
      ${
        thincsect.h $e |- H = ( Hom ` C ) $.
        $( In a thin category, one morphism is a section of another iff they
           are pointing towards each other.  (Contributed by Zhi Wang,
           24-Sep-2024.) $)
        thincsect $p |- ( ph -> ( F ( X S Y ) G
                         <-> ( F e. ( X H Y ) /\ G e. ( Y H X ) ) ) ) $=
          ( co wcel wa cfv adantr wbr cop cco ccid wceq thinccatd issect df-3an
          w3a eqid bitrdi cthinc ccat simprl simprr catcocl thincid mpbiran3d )
          AEFHIDPUAZEHIGPQZFIHGPQZRZFEHIUBHCUCSZPPZHCUDSZSUEZAUSUTVAVFUIVBVFRAB
          CDVCVEEFGHIKOVCUJZVEUJZNACJUFZLMUGUTVAVFUHUKAVBRZBCVEVDGHACULQVBJTKOA
          HBQVBLTZVHVJBCVCEFGHIHKOVGACUMQVBVITVKAIBQVBMTVKAUTVAUNAUTVAUOUPUQUR
          $.
      $}

      $( In a thin category, ` F ` is a section of ` G ` iff ` G ` is a section
         of ` F ` .  Example 7.25(4) of [Adamek] p. 108.  (Contributed by Zhi
         Wang, 24-Sep-2024.) $)
      thincsect2 $p |- ( ph -> ( F ( X S Y ) G <-> G ( Y S X ) F ) ) $=
        ( chom cfv co wcel wa wbr thincsect wb ancom a1i eqid 3bitr4d ) AEGHCNO
        ZPQZFHGUFPQZRZUHUGRZEFGHDPSFEHGDPSUIUJUAAUGUHUBUCABCDEFUFGHIJKLMUFUDZTA
        BCDFEUFHGIJLKMUKTUE $.

      thincinv.n $e |- N = ( Inv ` C ) $.
      $( In a thin category, ` F ` is an inverse of ` G ` iff ` F ` is a
         section of ` G ` .  Example 7.20(7) of [Adamek] p. 107.  (Contributed
         by Zhi Wang, 24-Sep-2024.) $)
      thincinv $p |- ( ph -> ( F ( X N Y ) G <-> F ( X S Y ) G ) ) $=
        ( co wbr thinccatd isinv thincsect2 biimpa mpbiran3d ) AEFHIGPQEFHIDPQZ
        FEIHDPQZABCDEFGHIKOACJRLMNSAUCUDABCDEFHIJKLMNTUAUB $.
    $}

    $d C f g $.  $d F f g $.  $d H f g $.  $d I f g $.  $d X f g $.
    $d Y f g $.  $d f g ph $.
    thinciso.h $e |- H = ( Hom ` C ) $.
    ${
      thinciso.i $e |- I = ( Iso ` C ) $.
      thinciso.f $e |- ( ph -> F e. ( X H Y ) ) $.
      $( In a thin category, ` F : X --> Y ` is an isomorphism iff there is a
         morphism from ` Y ` to ` X ` .  (Contributed by Zhi Wang,
         25-Sep-2024.) $)
      thinciso $p |- ( ph -> ( F e. ( X I Y ) <-> ( Y H X ) =/= (/) ) ) $=
        ( vg co wcel wa wtru cv csect cfv wbr wrex c0 wne eqid thinccatd dfiso3
        simprl ad2antrr cthinc thincsect mpbir2and jca reximdva0 reximddv rexn0
        trud adantl impbida bitr4d ) ADGHFQRPUAZDHGCUBUCZQUDZDVDGHVEQUDZSZPHGEQ
        ZUEZVIUFUGZABCVEPDEFGHJMNVEUHZACIUIKLOUJAVKVJAVKSZTVHPVIVMVDVIRZTSZSZVF
        VGVPVFVNDGHEQRZVMVNTUKZAVQVKVOOULZVPBCVEVDDEHGACUMRVKVOIULZJAHBRVKVOLUL
        ZAGBRVKVOKULZVLMUNUOVPVGVQVNVSVRVPBCVEDVDEGHVTJWBWAVLMUNUOUPATPVIAVNSUT
        UQURVJVKAVHPVIUSVAVBVC $.
    $}

    $( In a thin category, two objects are isomorphic iff there are morphisms
       between them in both directions.  (Contributed by Zhi Wang,
       25-Sep-2024.) $)
    thinccic $p |- ( ph -> ( X ( ~=c ` C ) Y <->
                ( ( X H Y ) =/= (/) /\ ( Y H X ) =/= (/) ) ) ) $=
      ( vf cfv co wcel wex c0 wne wa adantr ciso ccic wbr eqid thinccatd isohom
      sselda cthinc simpr thinciso biadanid exbidv cic anbi1i 19.41v bitr4i a1i
      cv wb n0 3bitr4d ) ALURZEFCUAMZNZOZLPVBEFDNZOZFEDNQRZSZLPZEFCUBMUCVFQRZVH
      SZAVEVILAVEVGVHAVDVFVBABCDVCEFHKVCUDZACGUEZIJUFUGAVGSBCVBDVCEFACUHOVGGTHA
      EBOVGITAFBOVGJTKVMAVGUIUJUKULABCLVCEFVMHVNIJUMVLVJUSAVLVGLPZVHSVJVKVOVHLV
      FUTUNVGVHLUOUPUQVA $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Terminal categories
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $c TermCat $.

  $( Extend class notation with the class of terminal categories. $)
  ctermc $a class TermCat $.

  ${
    $d B c $.  $d C c x $.
    $( Definition of the proper class ( ~ termcnex ) of terminal categories, or
       final categories, i.e., categories with exactly one object and exactly
       one morphism, the latter of which is an identity morphism ( ~ termcid ).
       These are exactly the thin categories with a singleton base set.
       Example 3.3(4.c) of [Adamek] p. 24.

       As the name indicates, ` TermCat ` is the class of all terminal objects
       in the category of small categories ( ~ termcterm3 ). ` TermCat ` is
       also the class of categories to which all categories have exactly one
       functor ( ~ dftermc2 ).  See also ~ dftermc3 where ` TermCat ` is
       defined as categories with exactly one disjointified arrow.

       Unlike ~ https://ncatlab.org/nlab/show/terminal+category , we reserve
       the term "trivial category" for ` ( SetCat `` 1o ) ` , justified by
       ~ setc1oterm .

       Followed directly from the definition, terminal categories are thin
       ( ~ termcthin ).  The opposite category of a terminal category is
       "almost" itself ( ~ oppctermco ).  Any category ` C ` is isomorphic to
       the category of functors from a terminal category to the category ` C `
       ( ~ diagcic ).

       Having defined the terminal category, we can then use it to define the
       universal property of initial ( ~ dfinito4 ) and terminal objects
       ( ~ dftermo4 ).  The universal properties provide an alternate proof of
       ~ initoeu1 , ~ termoeu1 , ~ initoeu2 , and ~ termoeu2 .  Since terminal
       categories are terminal objects, all terminal categories are mutually
       isomorphic ( ~ termcciso ).

       The dual concept is the initial category, or the empty category (Example
       7.2(3) of [Adamek] p. 101).  See ~ 0catg , ~ 0thincg , ~ func0g ,
       ~ 0funcg , and ~ initc .

       (Contributed by Zhi Wang, 16-Oct-2025.) $)
    df-termc $a |- TermCat = { c e. ThinCat | E. x ( Base ` c ) = { x } } $.

    istermc.b $e |- B = ( Base ` C ) $.
    $( The predicate "is a terminal category".  A terminal category is a thin
       category with a singleton base set.  (Contributed by Zhi Wang,
       16-Oct-2025.) $)
    istermc $p |- ( C e. TermCat <-> ( C e. ThinCat /\ E. x B = { x } ) ) $=
      ( vc cv cbs cfv csn wex cthinc ctermc fveqeq2 exbidv eqeq1i exbii bitr4di
      wceq df-termc elrab2 ) EFZGHAFIZRZAJZBUBRZAJZECKLUACRZUDCGHZUBRZAJUFUGUCU
      IAUACUBGMNUEUIABUHUBDOPQAEST $.

    $d B x $.
    $( The predicate "is a terminal category".  A terminal category is a thin
       category with exactly one object.  (Contributed by Zhi Wang,
       16-Oct-2025.) $)
    istermc2 $p |- ( C e. TermCat <-> ( C e. ThinCat /\ E! x x e. B ) ) $=
      ( ctermc wcel cthinc cv csn wceq wex wa weu istermc eusn anbi2i bitr4i )
      CEFCGFZBAHZIJAKZLRSBFAMZLABCDNUATRABOPQ $.

    $( The predicate "is a terminal category".  A terminal category is a thin
       category whose base set is equinumerous to ` 1o ` .  Consider ~ en1b ,
       ~ map1 , and ~ euen1b .  (Contributed by Zhi Wang, 16-Oct-2025.) $)
    istermc3 $p |- ( C e. TermCat <-> ( C e. ThinCat /\ B ~~ 1o ) ) $=
      ( vx ctermc wcel cthinc cv csn wceq wex wa c1o cen wbr istermc en1 anbi2i
      bitr4i ) BEFBGFZADHIJDKZLTAMNOZLDABCPUBUATDAQRS $.
  $}

  ${
    $d C x $.  $d ph x $.
    $( A terminal category is a thin category.  (Contributed by Zhi Wang,
       16-Oct-2025.) $)
    termcthin $p |- ( C e. TermCat -> C e. ThinCat ) $=
      ( vx ctermc wcel cthinc cbs cfv cv csn wceq wex eqid istermc simplbi ) AC
      DAEDAFGZBHIJBKBOAOLMN $.

    termcthind.c $e |- ( ph -> C e. TermCat ) $.
    $( A terminal category is a thin category (deduction form).  (Contributed
       by Zhi Wang, 16-Oct-2025.) $)
    termcthind $p |- ( ph -> C e. ThinCat ) $=
      ( ctermc wcel cthinc termcthin syl ) ABDEBFECBGH $.

    $( A terminal category is a category (deduction form).  (Contributed by Zhi
       Wang, 16-Oct-2025.) $)
    termccatd $p |- ( ph -> C e. Cat ) $=
      ( termcthind thinccatd ) ABABCDE $.
  $}

  ${
    $d C x $.
    termcbas.c $e |- ( ph -> C e. TermCat ) $.
    termcbas.b $e |- B = ( Base ` C ) $.
    $( The base of a terminal category is a singleton.  (Contributed by Zhi
       Wang, 16-Oct-2025.) $)
    termcbas $p |- ( ph -> E. x B = { x } ) $=
      ( cthinc wcel cv csn wceq wex ctermc wa istermc sylib simprd ) ADGHZCBIJK
      BLZADMHRSNEBCDFOPQ $.

    $d B x $.
    $( The object of a terminal category.  (Contributed by Zhi Wang,
       17-Nov-2025.) $)
    termco $p |- ( ph -> U. B e. B ) $=
      ( vx cv csn wceq cuni wcel termcbas unieq unisnv eqtrdi vsnid eqeltrdi id
      wex eleqtrrd exlimiv syl ) ABFGZHZIZFSBJZBKZAFBCDELUEUGFUEUFUDBUEUFUCUDUE
      UFUDJUCBUDMFNOFPQUERTUAUB $.

    $d B x y z $.  $d C x y z $.  $d X x y z $.  $d Y x y z $.  $d ph x y z $.
    termcbasmo.x $e |- ( ph -> X e. B ) $.
    $( The base of a terminal category is given by its object.  (Contributed by
       Zhi Wang, 20-Oct-2025.) $)
    termcbas2 $p |- ( ph -> B = { X } ) $=
      ( vx cv csn wceq termcbas wa simpr wcel adantr eleqtrd elsni sneqd syl
      eqtr4d exlimddv ) ABHIZJZKZBDJZKHAHBCEFLAUEMZBUDUFAUENZUGDUDOZUFUDKUGDBUD
      ADBOUEGPUHQUIDUCDUCRSTUAUB $.

    termcbasmo.y $e |- ( ph -> Y e. B ) $.
    $( Two objects in a terminal category are identical.  (Contributed by Zhi
       Wang, 16-Oct-2025.) $)
    termcbasmo $p |- ( ph -> X = Y ) $=
      ( vx vy vz cv wceq eqeq1 eqeq2 wcel wmo wral csn wex termcbas exlimiv syl
      mosn moel sylib rspc2dv ) AJMZKMZNZDENDUJNJKDEBBUIDUJOUJEDPAUIBQJRZUKKBSJ
      BSABLMZTNZLUAULALBCFGUBUNULLJBUMUEUCUDJKBUFUGHIUH $.

    termcid.h $e |- H = ( Hom ` C ) $.
    $( All hom-sets of a terminal category are non-empty.  (Contributed by Zhi
       Wang, 17-Oct-2025.) $)
    termchomn0 $p |- ( ph -> -. ( X H Y ) = (/) ) $=
      ( ccid cfv co wcel c0 wceq wn eqid termccatd catidcl termcbasmo eleqtrd
      oveq2d n0i syl ) AECLMZMZEFDNZOUIPQRAUHEEDNUIABCUGDEHKUGSACGTIUAAEFEDABCE
      FGHIJUBUDUCUIUHUEUF $.

    termcid.f $e |- ( ph -> F e. ( X H Y ) ) $.
    ${
      termchommo.x $e |- ( ph -> Z e. B ) $.
      termchommo.y $e |- ( ph -> W e. B ) $.
      termchommo.f $e |- ( ph -> G e. ( Z H W ) ) $.
      $( All morphisms of a terminal category are identical.  (Contributed by
         Zhi Wang, 16-Oct-2025.) $)
      termchommo $p |- ( ph -> F = G ) $=
        ( co termcbasmo oveq12d eleqtrrd termcthind thincmo2 ) ABCDEFHIMNPAEJGF
        THIFTSAHJIGFABCHJKLMQUAABCIGKLNRUAUBUCLOACKUDUE $.
    $}

    termcid.i $e |- .1. = ( Id ` C ) $.
    $( The morphism of a terminal category is an identity morphism.
       (Contributed by Zhi Wang, 16-Oct-2025.) $)
    termcid $p |- ( ph -> F = ( .1. ` X ) ) $=
      ( termcthind co termcbasmo oveq2d eleqtrrd thincid ) ABCDEFGACIPJMKOAEGHF
      QGGFQNAGHGFABCGHIJKLRSTUA $.

    $( The morphism of a terminal category is an identity morphism.
       (Contributed by Zhi Wang, 16-Oct-2025.) $)
    termcid2 $p |- ( ph -> F = ( .1. ` Y ) ) $=
      ( cfv termcid termcbasmo fveq2d eqtrd ) AEGDPHDPABCDEFGHIJKLMNOQAGHDABCGH
      IJKLRST $.
  $}

  ${
    $d .1. f $.  $d B f $.  $d C f $.  $d H f $.  $d X f $.  $d Y f $.
    $d f ph $.
    termchom.c $e |- ( ph -> C e. TermCat ) $.
    termchom.b $e |- B = ( Base ` C ) $.
    termchom.x $e |- ( ph -> X e. B ) $.
    termchom.y $e |- ( ph -> Y e. B ) $.
    termchom.h $e |- H = ( Hom ` C ) $.
    termchom.i $e |- .1. = ( Id ` C ) $.
    $( The hom-set of a terminal category is a singleton of the identity
       morphism.  (Contributed by Zhi Wang, 20-Oct-2025.) $)
    termchom $p |- ( ph -> ( X H Y ) = { ( .1. ` X ) } ) $=
      ( vf cv co wcel csn wceq adantr cfv c0 wn wex termchomn0 neq0 sylib simpr
      wa ctermc termcthind thinchom termcid sneqd eqtrd exlimddv ) ANOZFGEPZQZU
      RFDUAZRZSNAURUBSUCUSNUDABCEFGHIJKLUENURUFUGAUSUIZURUQRVAVBBCUQEFGAFBQUSJT
      ZAGBQUSKTZAUSUHZILVBCACUJQUSHTZUKULVBUQUTVBBCDUQEFGVFIVCVDLVEMUMUNUOUP $.

    termchom2.z $e |- ( ph -> Z e. B ) $.
    $( The hom-set of a terminal category is a singleton of the identity
       morphism.  (Contributed by Zhi Wang, 21-Oct-2025.) $)
    termchom2 $p |- ( ph -> ( X H Y ) = { ( .1. ` Z ) } ) $=
      ( co cfv csn termchom termcbasmo fveq2d sneqd eqtrd ) AFGEPFDQZRHDQZRABCD
      EFGIJKLMNSAUDUEAFHDABCFHIJKOTUAUBUC $.
  $}

  ${
    $d A p x $.
    $( The category of one set, either a singleton set or an empty set, is
       terminal.  (Contributed by Zhi Wang, 18-Oct-2025.) $)
    setcsnterm $p |- ( SetCat ` { { A } } ) e. TermCat $=
      ( vx csn csetc cfv ctermc wcel cthinc c1o cen wbr wtru cvv eqidd snex a1i
      vp cv wceq mptru wmo wral velsn mosn sylbi rgen setcthin cbs eqid setcbas
      ensn1 istermc3 mpbir2an ) ACZCZDEZFGUPHGZUOIJKUQLBUPUOMQLUPNUOMGLUNOPZQRB
      RZGQUAZBUOUBLUTBUOUSUOGUSUNSUTBUNUCQUSAUDUEUFPUGTUNAOUKUOUPUOUPUHESLUPUOM
      UPUIURUJTULUM $.

    $( The category ` ( SetCat `` 1o ) ` , i.e., the _trivial category_, is
       terminal.  (Contributed by Zhi Wang, 18-Oct-2025.) $)
    setc1oterm $p |- ( SetCat ` 1o ) e. TermCat $=
      ( c1o csetc cfv cvv csn ctermc df1o2 vsn eqtr4i fveq2i setcsnterm eqeltri
      c0 sneqi ) ABCDEZEZBCFAPBAMEPGOMHNIJDKL $.
  $}

  ${
    $d B x y $.  $d F x y $.  $d f g v z $.  $d ph x y $.
    funcsetc1o.1 $e |- .1. = ( SetCat ` 1o ) $.
    $( The base of the trivial category.  (Contributed by Zhi Wang,
       22-Oct-2025.) $)
    setc1obas $p |- 1o = ( Base ` .1. ) $=
      ( c1o cbs cfv wceq wtru cvv wcel 1oex a1i setcbas mptru ) CADEFGACHBCHIGJ
      KLM $.

    $( Set of morphisms of the trivial category.  (Contributed by Zhi Wang,
       22-Oct-2025.) $)
    setc1ohomfval $p |- { <. (/) , (/) , 1o >. } = ( Hom ` .1. ) $=
      ( vx vy c0 c1o csn cop cfv cvv wcel wceq 0ex cv cmap co wtru csetc eqtr4i
      df1o2 cotp chom df-ot sneqi 1oex cmpo fveq2i eqtri p0ex setchomfval mptru
      a1i eqid oveq2 oveq1 0map0sn0 eqtrdi mposn mp3an ) EEFUAZGEEHFHZGZAUBIZUT
      VAEEFUCUDEJKZVDFJKVCVBLMMUECDEEDNZCNZOPZVEEOPZJFVCJJVCCDEGZVIVGUFLQCDAVIV
      CJAFRIVIRIBFVIRTUGUHVIJKQUIULVCUMUJUKVFEVEOUNVEELVHEEOPZFVEEEOUOVJVIFUPTS
      UQURUSS $.

    $( Composition in the trivial category.  (Contributed by Zhi Wang,
       22-Oct-2025.) $)
    setc1ocofval $p |- { <. <. (/) , (/) >. , (/) ,
                         { <. (/) , (/) , (/) >. } >. } = ( comp ` .1. ) $=
      ( vv vz vg vf c0 csn cfv cvv wcel wceq 0ex cv cmap cmpo eqid eqtrdi eqidd
      co cop cotp cco df-ot sneqi opex snex c2nd c1st ccom cxp wtru csetc df1o2
      c1o fveq2i eqtri a1i setccofval mptru xpsn mpoeq123i op2ndd oveq2d op1std
      oveq12d 0map0sn0 mpoeq123dv oveq1 coeq1 co01 mposn mp3an eqtr4di eqtr4i )
      GGUAZGGGGUBZHZUBZHVPGUAZVRUAZHZAUCIZVSWAVPGVRUDUEVPJKGJKZVRJKWCWBLGGUFMVQ
      UGCDVPGEFDNZCNZUHIZOTZWGWFUIIZOTZENZFNZUJZPZEFWEGOTZGHZWMPZJVRWCJJWCCDWPW
      PUKZWPWNPZCDVPHZWPWNPWCWSLULDCAWCWPFEJAUOUMIWPUMIBUOWPUMUNUPUQWPJKULGUGUR
      WCQUSUTCDWRWPWNWTWPWNGGMMVAWPQWNQVBUQWFVPLZEFWHWJWMWOWPWMXAWGGWEOGGWFMMVC
      ZVDXAWJGGOTZWPXAWGGWIGOXBGGWFMMVEVFVGRXAWMSVHWEGLZWQVTHZVRXDWQEFWPWPWMPZX
      EXDEFWOWPWMWPWPWMXDWOXCWPWEGGOVIVGRXDWPSXDWMSVHWDWDWDXFXELMMMEFGGWMGJGXFJ
      JXFQWKGLWMGWLUJGWKGWLVJWLVKRWLGLGSVLVMRVQVTGGGUDUEVNVLVMVO $.

    ${
      setc1oid.i $e |- I = ( Id ` .1. ) $.
      $( The identity morphism of the trivial category.  (Contributed by Zhi
         Wang, 22-Oct-2025.) $)
      setc1oid $p |- ( I ` (/) ) = (/) $=
        ( cfv cid cres wceq wtru c1o cvv wcel 1oex a1i 0lt1o setcid mptru eqtri
        c0 res0 ) SBEZFSGZSUAUBHIAJBKSCDJKLIMNSJLIONPQFTR $.
    $}

    funcsetc1o.f $e |- F = ( ( 1st ` ( .1. DiagFunc C ) ) ` (/) ) $.
    funcsetc1o.c $e |- ( ph -> C e. Cat ) $.
    $( The functor to the trivial category.  The converse is also true due to
       reverse closure.  (Contributed by Zhi Wang, 22-Oct-2025.) $)
    funcsetc1ocl $p |- ( ph -> F e. ( C Func .1. ) ) $=
      ( c1o cdiag co c0 eqid ctermc wcel csetc cfv setc1oterm eqeltri termccatd
      a1i setc1obas 0lt1o diag1cl ) AHCBDCBIJZKUDLACCMNACHOPMEQRTSGCEUAKHNAUBTF
      UC $.

    funcsetc1o.b $e |- B = ( Base ` C ) $.
    funcsetc1o.h $e |- H = ( Hom ` C ) $.
    $( Value of the functor to the trivial category.  The converse is also true
       because ` F ` would be the empty set if ` C ` were not a category; and
       the empty set cannot equal an ordered pair of two sets.  (Contributed by
       Zhi Wang, 22-Oct-2025.) $)
    funcsetc1o $p |- ( ph -> F = <. ( B X. 1o ) ,
          ( x e. B , y e. B |-> ( ( x H y ) X. 1o ) ) >. ) $=
      ( c0 csn cxp cfv c1o wcel a1i cv co ccid cmpo cop cdiag eqid ctermc csetc
      setc1oterm eqeltri termccatd setc1obas 0lt1o diag1a df1o2 xpeq2i setc1oid
      wceq wa sneqi eqtr4i mpoeq3ia opeq12i eqtr4di ) AGDNOZPZBCDDBUAZCUAZHUBZN
      FUCQZQZOZPZUDZUEDRPZBCDDVJRPZUDZUEABCRDFEVKHGFEUFUBZNVSUGAFFUHSAFRUIQUHIU
      JUKTULKFIUMNRSAUNTJLMVKUGZUOVPVGVRVORVFDUPUQBCDDVQVNVQVNUSVHDSVIDSUTRVMVJ
      RVFVMUPVLNFVKIVTURVAVBUQTVCVDVE $.
  $}

  ${
    $d .1. f x y $.  $d C f x y $.  $d F f x y $.  $d I f x y $.
    $d f ph x y $.
    isinito2.1 $e |- .1. = ( SetCat ` 1o ) $.
    isinito2.f $e |- F = ( ( 1st ` ( .1. DiagFunc C ) ) ` (/) ) $.
    ${
      isinito2lem.c $e |- ( ph -> C e. Cat ) $.
      isinito2lem.i $e |- ( ph -> I e. ( Base ` C ) ) $.
      $( The predicate "is an initial object" of a category, using universal
         property.  (Contributed by Zhi Wang, 23-Oct-2025.) $)
      isinito2lem $p |- ( ph -> ( I e. ( InitO ` C )
                              <-> I ( F ( C UP .1. ) (/) ) (/) ) ) $=
        ( vf vx vy cfv wcel c0 co wral wceq c1o a1i cinito c1st c2nd cop cup cv
        wbr chom weu cbs cotp csn wreu wtru wa reutru eqeq1 reubidv ralsn cdiag
        0ex wb ctermc csetc setc1oterm eqeltri termccatd setc1obas 0lt1o diag11
        eqid adantr opeq2d ccat simpr oveq12d snex ovsn2 eqtrdi ad2antrr simplr
        ccid diag12 setc1oid eqidd oveq123d eqtr2di tbtru sylib reubidva oveq2d
        bitr2id 1oex df1o2 raleqdv bitr4d bitrid ralbidva isinito setc1ohomfval
        eqtri setc1ocofval funcsetc1ocl func1st2nd eleqtrrid 3bitr4d up1st2ndb
        isup ) AEBUAMNZEODUBMZDUCMZUDOBCUEPZPUGZEODOXLPUGAJUFZEKUFZBUHMZPZNZJUI
        ZKBUJMZQLUFZXNEXOXKPMZOOEXJMZUDZXOXJMZOOUDZOOOOUKZULZUKULZPZPZRZJXQUMZL
        OYEOOSUKULZPZQZKXTQXIXMAXSYPKXTXSUNJXQUMZAXOXTNZUOZYPJXQUPYSYQYMLOULZQZ
        YPUUAOYKRZJXQUMZYSYQYMUUCLOVAYAORYLUUBJXQYAOYKUQURUSYSUUBUNJXQYSXRUOZUU
        BUUBUNVBUUDYKOOYHPOUUDYBOOOYJYHYSYJYHRXRYSYJYFOYIPYHYSYDYFYEOYIYSYCOOAY
        CORYRASXTCBDCBUTPZOEUUEVKZACCVCNZACSVDMVCFVEVFZTVGZHCFVHZOSNZAVITZGXTVK
        ZIVJZVLVMYSSXTCBDUUEOXOUUFACVNNYRUUIVLABVNNZYRHVLUUJUUKYSVITGUUMAYRVOVJ
        ZVPYFOYHYGVQVRVSVLUUDYBOCWBMZMOUUDSXTCBUUQXNXPDUUEOEXOUUFUUDCUUGUUDUUHT
        VGAUUOYRXRHVTUUJUUKUUDVITGUUMAEXTNYRXRIVTXPVKZUUQVKZAYRXRWAYSXRVOWCCUUQ
        FUUSWDVSUUDOWEWFOOOVAVRWGUUBWHWIWJWLYSYMLYOYTYSYOOOYNPZYTYSYEOOYNUUPWKU
        UTSYTOOSWMVRZWNXAVSWOWPWQWRAXTBJXPEKUUMUURHIWSAKXTSBLJCXJXKXPYNOYIOEUUM
        UUJUURCFWTCFXBUULABCDABCDFGHXCZXDIAOSOYCYNPZVIAUVCUUTSAYCOOYNUUNWKUVAVS
        XEXHXFABCDOOEUVBXGWP $.
    $}

    $( The predicate "is an initial object" of a category, using universal
       property.  (Contributed by Zhi Wang, 23-Oct-2025.) $)
    isinito2 $p |- ( I e. ( InitO ` C )
                 <-> I ( F ( C UP .1. ) (/) ) (/) ) $=
      ( cinito cfv wcel c0 cup co wbr initorcl cbs eqid initoo2 isinito2lem ibi
      c1st c2nd id up1st2nd uprcl2 funcrcl2 uprcl4 ibir impbii ) DAGHIZDJCJABKL
      LMZUIUJUIABCDEFADNAOHZADUKPZQRSUJUIUJABCDEFUJABCTHZCUAHZUJABUMUNJJDUJABCJ
      JDUJUBUCZUDUEUJUKABUMUNJJDUOULUFRUGUH $.

    $( The predicate "is an initial object" of a category, using universal
       property.  (Contributed by Zhi Wang, 23-Oct-2025.) $)
    isinito3 $p |- ( I e. ( InitO ` C )
                 <-> I e. dom ( F ( C UP .1. ) (/) ) ) $=
      ( vy cinito cfv wcel c0 cup co cdm wrel wbr relup c1o eqid ctermc releldm
      isinito2 biimpi sylancr cv wex releldmb ax-mp wceq c1st cotp csn up1st2nd
      wb c2nd setc1ohomfval uprcl5 cbs cdiag csetc setc1oterm eqeltri termccatd
      id a1i uprcl2 funcrcl2 setc1obas uprcl3 uprcl4 diag11 oveq2d ovsn2 eqtrdi
      1oex eleqtrd el1o sylib breqtrd sylibr exlimiv sylbi impbii ) DAHIJZDCKAB
      LMMZNJZWDWEOZDKWEPZWFABCKQZWDWHABCDEFUBZUCDKWEUAUDWFDGUEZWEPZGUFZWDWGWFWM
      UNWIGDWEUGUHWLWDGWLWHWDWLDWKKWEWLVDZWLWKRJWKKUIWLWKKDCUJIZIZKKRUKULZMZRWL
      ABWOCUOIZWQWKKDWLABCWKKDWNUMZBEUPUQWLWRKKWQMRWLWPKKWQWLRAURIZBACBAUSMZKDX
      BSWLBBTJWLBRUTITEVAVBVEVCWLABWOWSWLABWOWSWKKDWTVFVGBEVHZWLRABWOWSWKKDWTXC
      VIFXASZWLXAABWOWSWKKDWTXDVJVKVLKKRVOVMVNVPWKVQVRVSWJVTWAWBWC $.
  $}

  ${
    $d c d e f x $.
    $( An alternate definition of ~ df-inito using universal property.  See
       also the "Equivalent formulations" section of
       ~ https://en.wikipedia.org/wiki/Initial_and_terminal_objects .
       (Contributed by Zhi Wang, 23-Oct-2025.) $)
    dfinito4 $p |- InitO = ( c e. Cat |-> [_ ( SetCat ` 1o ) / d ]_
              [_ ( ( 1st ` ( d DiagFunc c ) ) ` (/) ) / f ]_
              dom ( f ( c UP d ) (/) ) ) $=
      ( ve vx cinito ccat c1o cfv c0 cv cdiag c1st cup cdm csb wceq csbex eqid
      co csetc cmpt wral wb initofn ovex dmex fnmpti eqfnfv mp2an wcel isinito3
      wfn eqriv fvex fvexd wa simpl oveq2d simpr fvoveq1d fveq1d eqtrd oveq123d
      cvv eqidd dmeqd csbied csbie eqtr4i oveq2 fveq2d oveq1 csbeq12dv csbeq2dv
      oveqd fvmpt eqtr4id mprgbir ) FBGCHUAIZAJCKZBKZLTZMIZIZAKZJWBWANTZTZOZPZP
      ZUBZQZDKZFIZWNWLIZQZDGFGUMWLGUMWMWQDGUCUDUEBGWKWLCVTWJAWEWIWHWFJWGUFUGRRW
      LSZUHDGFWLUIUJWNGUKWOCVTAJWAWNLTZMIZIZWFJWNWANTZTZOZPZPZWPWOJVTWNLTMIZIZJ
      WNVTNTZTZOZXFEWOXKWNVTXHEKVTSXHSULUNCVTXEXKHUAUOWAVTQZAXAXDXKVEXLJWTUPXLW
      FXAQZUQZXCXJXNWFXHJJXBXIXNWAVTWNNXLXMURZUSXNWFXAXHXLXMUTXNJWTXGXNWAVTWNML
      XOVAVBVCXNJVFVDVGVHVIVJBWNWKXFGWLWBWNQZCVTWJXEXPAWEWIXAXDXPJWDWTXPWCWSMWB
      WNWALVKVLVBXPWHXCXPWGXBWFJWBWNWANVMVPVGVNVOWRCVTXEAXAXDXCWFJXBUFUGRRVQVRV
      S $.
  $}

  ${
    $d d f o $.
    $( An alternate definition of ~ df-termo using universal property.  See
       also the "Equivalent formulations" section of
       ~ https://en.wikipedia.org/wiki/Initial_and_terminal_objects .
       (Contributed by Zhi Wang, 23-Oct-2025.) $)
    dftermo4 $p |- TermO = ( c e. Cat |->
              [_ ( oppCat ` c ) / o ]_ [_ ( SetCat ` 1o ) / d ]_
              [_ ( ( 1st ` ( d DiagFunc o ) ) ` (/) ) / f ]_
              dom ( f ( o UP d ) (/) ) ) $=
      ( ctermo ccat cv coppc cfv cinito cmpt c1o csetc c0 cdiag co csb wcel cvv
      csbex c1st cup cdm dftermo2 wceq eqid oppccat ovex dmex dfinito4 mpteq2ia
      fvmpts sylancl eqtri ) ECFCGZHIZJIZKCFBUPDLMIZANDGZBGZOPUAIIZAGZNUTUSUBPZ
      PZUCZQZQZQZKCUDCFUQVHUOFRUPFRVHSRUQVHUEUOUPUPUFUGBUPVGDURVFAVAVEVDVBNVCUH
      UITTTBUPVGFJSABDUJULUMUKUN $.
  $}

  ${
    $d C x $.  $d D x $.  $d V x $.  $d W x $.  $d ph x $.
    termcpropd.1 $e |- ( ph -> ( Homf ` C ) = ( Homf ` D ) ) $.
    termcpropd.2 $e |- ( ph -> ( comf ` C ) = ( comf ` D ) ) $.
    termcpropd.3 $e |- ( ph -> C e. V ) $.
    termcpropd.4 $e |- ( ph -> D e. W ) $.
    $( Two structures with the same base, hom-sets and composition operation
       are either both terminal categories or neither.  (Contributed by Zhi
       Wang, 16-Oct-2025.) $)
    termcpropd $p |- ( ph -> ( C e. TermCat <-> D e. TermCat ) ) $=
      ( vx cthinc wcel cbs cfv wceq wex wa ctermc eqid istermc cv csn homfeqbas
      thincpropd eqeq1d exbidv anbi12d 3bitr4g ) ABKLZBMNZJUAUBZOZJPZQCKLZCMNZU
      KOZJPZQBRLCRLAUIUNUMUQABCDEFGHIUDAULUPJAUJUOUKABCFUCUEUFUGJUJBUJSTJUOCUOS
      TUH $.
  $}

  ${
    $d C x $.  $d O x $.  $d ph x $.
    oppcterm.o $e |- O = ( oppCat ` C ) $.
    oppcterm.c $e |- ( ph -> C e. TermCat ) $.
    $( The opposite category of a terminal category has the same base and
       hom-sets as the original category.  (Contributed by Zhi Wang,
       16-Oct-2025.) $)
    oppctermhom $p |- ( ph -> ( Homf ` C ) = ( Homf ` O ) ) $=
      ( vx cbs cfv cv csn wceq wex chomf eqid termcbas id oppcmndc exlimiv syl
      ) ABGHZFIZJKZFLBMHCMHKZAFTBETNZOUBUCFUBTBCUADUDUBPQRS $.

    $( The opposite category of a terminal category has the same base, hom-sets
       and composition operation as the original category.  Note that ` C = O `
       cannot be proved because ` C ` might not even be a function.  For
       example, let ` C ` be ` ( { <. ( Base `` ndx ) , { (/) } >. , `
       ` <. ( Hom `` ndx ) , ( ( _V X. _V ) X. { { (/) } } ) >. } u. `
       ` { <. ( comp `` ndx ) , { (/) } >. , <. ( comp `` ndx ) , 2o >. } ) ` ;
       it should be a terminal category, but the opposite category is not
       itself.  See the definitions ~ df-oppc and ~ df-sets .  (Contributed by
       Zhi Wang, 16-Oct-2025.) $)
    oppctermco $p |- ( ph -> ( comf ` C ) = ( comf ` O ) ) $=
      ( termcthind oppctermhom oppcthinco ) ABCDABEFABCDEGH $.

    $( The opposite category of a terminal category is a terminal category.
       (Contributed by Zhi Wang, 16-Oct-2025.) $)
    oppcterm $p |- ( ph -> O e. TermCat ) $=
      ( ctermc wcel cvv oppctermhom oppctermco coppc fvexi a1i termcpropd mpbid
      ) ABFGCFGEABCFHABCDEIABCDEJECHGACBKDLMNO $.
  $}

  ${
    functermclem.1 $e |- ( ( ph /\ K R L ) -> K = F ) $.
    functermclem.2 $e |- ( ph -> ( F R L <-> L = G ) ) $.
    $( Lemma for ~ functermc .  (Contributed by Zhi Wang, 17-Oct-2025.) $)
    functermclem $p |- ( ph -> ( K R L <-> ( K = F /\ L = G ) ) ) $=
      ( wbr wceq wa simpr eqbrtrrd biimpa syldan simprl biimpar adantrl eqbrtrd
      jca impbida ) AEFBIZECJZFDJZKZAUBKZUCUDGAUBCFBIZUDUFECFBGAUBLMAUGUDHNOTAU
      EKECFBAUCUDPAUDUGUCAUGUDHQRSUA $.
  $}

  ${
    $d B w x y z $.  $d C w z $.  $d D w z $.  $d E w z $.  $d F w x y z $.
    $d G w z $.  $d H w x y z $.  $d J w x y z $.  $d K w z $.  $d L w z $.
    $d ph w z $.
    functermc.d $e |- ( ph -> D e. Cat ) $.
    functermc.e $e |- ( ph -> E e. TermCat ) $.
    functermc.b $e |- B = ( Base ` D ) $.
    functermc.c $e |- C = ( Base ` E ) $.
    functermc.h $e |- H = ( Hom ` D ) $.
    functermc.j $e |- J = ( Hom ` E ) $.
    functermc.f $e |- F = ( B X. C ) $.
    functermc.g $e |- G = ( x e. B , y e. B |->
        ( ( x H y ) X. ( ( F ` x ) J ( F ` y ) ) ) ) $.
    $( Functor to a terminal category.  (Contributed by Zhi Wang,
       17-Oct-2025.) $)
    functermc $p |- ( ph -> ( K ( D Func E ) L <-> ( K = F /\ L = G ) ) ) $=
      ( vz vw cfunc co wbr wf wceq wa simpr funcf1 cv csn wex termcbas feq3 cxp
      wb vex fconst2 xpeq2 eqtrid eqeq2d bitr4id bitrd biimpa syldan termcthind
      exlimiv syl fconst feq1d mpbiri cfv wcel ctermc adantr ffvelcdmda adantrr
      c0 wi adantrl termchomn0 pm2.21d ralrimivva functhinc functermclem ) AFGU
      DUEZHILMALMWHUFZDELUGZLHUHZAWIUIDEFGLMPQAWIUJUKAWJWKAEUBULZUMZUHZUBUNZWJW
      KURZAUBEGOQUOZWNWPUBWNWJDWMLUGZWKEWMDLUPWNWRLDWMUQZUHWKDWLLUBUSZUTWNHWSLW
      NHDEUQWSTEWMDVAVBZVCVDVEVIVJVFVGABCUBUCDEFGHMJKIPQRSNAGOVHAWODEHUGZWQWNXB
      UBWNXBDWMWSUGZDWLWTVKWNXBDEWSUGXCWNDEHWSXAVLEWMDWSUPVEVMVIVJZUAAWLHVNZUCU
      LZHVNZKUEVTUHZWLXFJUEVTUHZWAUBUCDDAWLDVOZXFDVOZUIZUIZXHXIXMEGKXEXGAGVPVOX
      LOVQQAXJXEEVOXKADEWLHXDVRVSAXKXGEVOXJADEXFHXDVRWBSWCWDWEWFWG $.

    $( Functor to a terminal category.  (Contributed by Zhi Wang,
       17-Oct-2025.) $)
    functermc2 $p |- ( ph -> ( D Func E ) = { <. F , G >. } ) $=
      ( cvv vz vw cfunc co cop csn relfunc cxp cbs fvexi xpex eqeltri cfv mpoex
      cv cmpo relsnop wbr wceq wa functermc wcel brsnop mp2an bitr4di eqbrrdiv
      wb ) AUAUBFGUCUDZHIUEUFZFGUGHIHDEUHTRDEDFUINUJZEGUIOUJUKULZIBCDDBUOZCUOZJ
      UDVLHUMVMHUMKUDUHZUPTSBCDDVNVJVJUNULZUQAUAUOZUBUOZVHURVPHUSVQIUSUTZVPVQVI
      URZABCDEFGHIJKVPVQLMNOPQRSVAHTVBITVBVSVRVGVKVOHITTVPVQVCVDVEVF $.
  $}

  ${
    $d C f x y $.  $d D f x y $.  $d ph x y $.
    functermceu.c $e |- ( ph -> C e. Cat ) $.
    functermceu.d $e |- ( ph -> D e. TermCat ) $.
    $( There exists a unique functor to a terminal category.  (Contributed by
       Zhi Wang, 17-Oct-2025.) $)
    functermceu $p |- ( ph -> E! f f e. ( C Func D ) ) $=
      ( vx vy cfunc co cv csn wceq wcel cbs cfv cxp chom cvv eqid wex cmpo opex
      weu cop a1i functermc2 sneq eqeq2d spcedv eusn sylibr ) ABCIJZDKZLZMZDUAU
      NUMNDUDAUPUMBOPZCOPZQZGHUQUQGKZHKZBRPZJUTUSPVAUSPCRPZJQUBZUEZLZMDSVEVESNA
      USVDUCUFAGHUQURBCUSVDVBVCEFUQTURTVBTVCTUSTVDTUGUNVEMUOVFUMUNVEUHUIUJDUMUK
      UL $.
  $}

  ${
    $d B x y $.  $d C x y $.  $d D x y $.  $d F x y $.  $d G x y $.
    $d H x y $.  $d X x y $.  $d Y x y $.  $d ph x y $.
    fulltermc.b $e |- B = ( Base ` C ) $.
    fulltermc.h $e |- H = ( Hom ` C ) $.
    fulltermc.d $e |- ( ph -> D e. TermCat ) $.
    ${
      fulltermc.f $e |- ( ph -> F ( C Func D ) G ) $.
      $( A functor to a terminal category is full iff all hom-sets of the
         source category are non-empty.  (Contributed by Zhi Wang,
         17-Oct-2025.) $)
      fulltermc $p |- ( ph -> ( F ( C Full D ) G
                        <-> A. x e. B A. y e. B -. ( x H y ) = (/) ) ) $=
        ( co cv c0 wceq cfv wral wcel cful chom wi wn eqid termcthind fullthinc
        wbr wa wb cbs ctermc adantr ffvelcdmda adantrr adantrl termchomn0 biimt
        funcf1 syl con34b bitr4di 2ralbidva bitr4d ) AGHEFUANUHBOZCOZINPQZVEGRZ
        VFGRZFUBRZNPQZUCZCDSBDSVGUDZCDSBDSABCDEFGHIVJJVJUEZKAFLUFMUGAVMVLBCDDAV
        EDTZVFDTZUIZUIZVMVKUDZVMUCZVLVRVSVMVTUJVRFUKRZFVJVHVIAFULTVQLUMWAUEZAVO
        VHWATVPADWAVEGADWAEFGHJWBMUSZUNUOAVPVIWATVOADWAVFGWCUNUPVNUQVSVMURUTVGV
        KVAVBVCVD $.
    $}

    fulltermc2.f $e |- ( ph -> F ( C Full D ) G ) $.
    fulltermc2.x $e |- ( ph -> X e. B ) $.
    fulltermc2.y $e |- ( ph -> Y e. B ) $.
    $( Given a full functor to a terminal category, the source category must
       not have empty hom-sets.  (Contributed by Zhi Wang, 17-Oct-2025.)
       (Proof shortened by Zhi Wang, 6-Nov-2025.) $)
    fulltermc2 $p |- ( ph -> -. ( X H Y ) = (/) ) $=
      ( vx vy co c0 wceq cv wn oveq1 eqeq1d notbid oveq2 cful wbr wral fullfunc
      cfunc ssbri syl fulltermc mpbid rspc2dv ) APUAZQUAZGRZSTZUBZHIGRZSTZUBHUR
      GRZSTZUBPQHIBBUQHTZUTVEVFUSVDSUQHURGUCUDUEURITZVEVCVGVDVBSURIHGUFUDUEAEFC
      DUGRZUHZVAQBUIPBUIMAPQBCDEFGJKLAVIEFCDUKRZUHMVHVJEFCDUJULUMUNUONOUP $.
  $}

  ${
    $d C d f $.  $d E d f $.  $d U d f $.  $d V d f $.  $d d f ph $.
    termcterm.e $e |- E = ( CatCat ` U ) $.
    ${
      termcterm.u $e |- ( ph -> U e. V ) $.
      termcterm.c $e |- ( ph -> C e. U ) $.
      termcterm.t $e |- ( ph -> C e. TermCat ) $.
      $( A terminal category is a terminal object of the category of small
         categories.  (Contributed by Zhi Wang, 17-Oct-2025.) $)
      termcterm $p |- ( ph -> C e. ( TermO ` E ) ) $=
        ( vf vd cfv wcel cv co weu ccat eqid adantr mpbird ctermo chom cbs wral
        wa cfunc simpr wceq catcbas eleqtrd elin2d ctermc functermceu termccatd
        cin elind eleqtrrd catchom eleq2d eubidv ralrimiva catccat syl istermo
        ) ABDUALMJNZKNZBDUBLZOZMZJPZKDUCLZUDAVJKVKAVFVKMZUEZVJVEVFBUFOZMZJPVMVF
        BJVMCQVFVMVFVKCQUOZAVLUGZAVKVPUHVLAVKDCEFVKRZGUIZSUJUKABULMVLISUMVMVIVO
        JVMVHVNVEVMVKDCVGEVFBFVRACEMZVLGSVGRZVQABVKMVLABVPVKACQBHABIUNUPVSUQZSU
        RUSUTTVAAVKDJVGBKVRWAAVTDQMGDCEFVBVCWBVDT $.
    $}

    ${
      termcterm2. $e |- ( ph -> ( U i^i TermCat ) =/= (/) ) $.
      termcterm2.t $e |- ( ph -> C e. ( TermO ` E ) ) $.
      $( A terminal object of the category of small categories is a terminal
         category.  (Contributed by Zhi Wang, 18-Oct-2025.)  (Proof shortened
         by Zhi Wang, 23-Oct-2025.) $)
      termcterm2 $p |- ( ph -> C e. TermCat ) $=
        ( vd vf ctermc cin wcel wa cbs cfv c1o cen cvv eqid syl cv c0 wne sylib
        wex n0 cthinc wbr simpr elin2d termcthind ctermo adantr termoo2 elbasfv
        ccatc ccat elin1d termccatd elind eleqtrrd termorcl termcterm termoeu1w
        catcbas thincciso4 mpbird ciso co weu termoeu1 euex c1st wf1o cful cfth
        catciso simplbda fvex f1oen exlimddv istermc3 simprd syl2anc sylanbrc
        entr ) AHUAZCJKZLZBJLZHAWHUBUCWIHUEFHWHUFUDAWIMZBUGLZBNOZPQUHZWJWKWLWGU
        GLZWKWGWKCJWGAWIUIZUJZUKWKDNOZDCRBWGEWRSZWKBWRLZCRLWKBDULOLZWTAXAWIGUMZ
        WRDBWSUNTZWRDUPBCEWSUOTZXCWKWGCUQKWRWKCUQWGWKCJWGWPURZWKWGWQUSUTWKWRDCR
        EWSXDVEVAZWKBWGDWKXADUQLXBDBVBTZXBWKWGCDREXDXEWQVCZVDVFVGWKWMWGNOZQUHZX
        IPQUHZWNWKIUAZBWGDVHOZVILZXJIWKXNIVJXNIUEWKBWGDIXGXBXHVKXNIVLTWKXNMWMXI
        XLVMOZVNZXJWKXNXLBWGVOVIBWGVPVIKLXPWKWRDWMXICXLXMRBWGEWSWMSZXISZXDXCXFX
        MSVQVRWMXIXOBNVSVTTWAWKWOXKWKWGJLWOXKMWQXIWGXRWBUDWCWMXIPWFWDWMBXQWBWEW
        A $.
    $}

    termcterm3.u $e |- ( ph -> U e. V ) $.
    termcterm3.c $e |- ( ph -> C e. U ) $.
    termcterm3.1 $e |- ( ph -> ( SetCat ` 1o ) e. U ) $.
    $( In the category of small categories, a terminal object is equivalent to
       a terminal category.  (Contributed by Zhi Wang, 18-Oct-2025.) $)
    termcterm3 $p |- ( ph -> ( C e. TermCat <-> C e. ( TermO ` E ) ) ) $=
      ( ctermc wcel ctermo cfv wa adantr simpr termcterm cin c0 wne csetc elind
      c1o setc1oterm a1i ne0d termcterm2 impbida ) ABJKZBDLMKZAUINBCDEFACEKUIGO
      ABCKUIHOAUIPQAUJNBCDFACJRZSTUJAUKUCUAMZACJULIULJKAUDUEUBUFOAUJPUGUH $.
  $}

  ${
    termcciso.c $e |- C = ( CatCat ` U ) $.
    termcciso.b $e |- B = ( Base ` C ) $.
    termcciso.x $e |- ( ph -> X e. B ) $.
    termcciso.y $e |- ( ph -> Y e. B ) $.
    termcciso.t $e |- ( ph -> X e. TermCat ) $.
    $( A category is isomorphic to a terminal category iff it itself is
       terminal.  (Contributed by Zhi Wang, 26-Oct-2025.) $)
    termcciso $p |- ( ph -> ( Y e. TermCat <-> X ( ~=c ` C ) Y ) ) $=
      ( ctermc wcel cfv wa ccat cvv syl adantr cin ccatc elbasfv catccat ctermo
      ccic wbr catcbas eleqtrd elin1d termcterm wceq simpr termoeu1w elind ne0d
      c0 wne termoeu2 termcterm2 impbida ) AFLMZEFCUENUFZAVAOZEFCACPMZVAADQMZVD
      AEBMVEIBCUAEDGHUBRZCDQGUCRZSAECUDNMZVAAEDCQGVFADPEAEBDPTZIABCDQGHVFUGZUHU
      IZKUJZSVCFDCQGAVEVAVFSVCDPFVCFBVIAFBMVAJSABVIUKVAVJSUHUIAVAULUJUMAVBOZFDC
      GADLTZUPUQVBAVNEADLEVKKUNUOSVMEFCAVDVBVGSAVHVBVLSAVBULURUSUT $.

    $d C f $.  $d X f $.  $d Y f $.  $d f ph $.
    termccisoeu.y $e |- ( ph -> Y e. TermCat ) $.
    $( The isomorphism between terminal categories is unique.  (Contributed by
       Zhi Wang, 26-Oct-2025.) $)
    termccisoeu $p |- ( ph -> E! f f e. ( X ( Iso ` C ) Y ) ) $=
      ( cvv wcel ccat syl eleqtrd elin1d termcterm elbasfv catccat cin termoeu1
      ccatc catcbas ) AFGCEADNOZCPOAFBOUGJBCUEFDHIUAQZCDNHUBQAFDCNHUHADPFAFBDPU
      CZJABCDNHIUHUFZRSLTAGDCNHUHADPGAGBUIKUJRSMTUD $.
  $}

  ${
    $d C c d f $.
    $( If there exists a unique functor from both the category itself and the
       trivial category, then the category is terminal.  Note that the converse
       also holds, so that it is a biconditional.  See the proof of ~ termc for
       hints.  See also ~ eufunc and ~ euendfunc2 for some insights on why two
       categories are sufficient.  (Contributed by Zhi Wang, 18-Oct-2025.)
       (Proof shortened by Zhi Wang, 20-Oct-2025.) $)
    termc2 $p |- ( A. d e. ( { C , ( SetCat ` 1o ) } i^i Cat )
                             E! f f e. ( d Func C ) -> C e. TermCat ) $=
      ( cv cfunc co wcel weu c1o cfv ccat cin wral eqid ctermc a1i wtru cvv syl
      csetc cpr ccatc c0 wne fvex prid2 setc1oterm elini ne0ii ctermo cen wb wi
      wbr termccatd mptru wceq oveq1 eleq2d eubidv rspcv euen1b sylibr chom cbs
      ax-mp prex catcbas eqcomi catccat wex funcrcl simprd exlimiv sylbi prid1g
      euex elind istermo wa simpr adantr catchom ralbidva bitrd ibir termcterm2
      ) BDZCDZAEFZGZBHZCAITJZUAZKLZMZAWNWNUBJZWQNZWNOLZUCUDWPWMWSWMWNOAWMITUEUF
      ZUGUHUIPWPAWQUJJGZWPWMAEFZIUKUNZXAWPULWPWHXBGZBHZXCWMWOGWPXEUMWMWNKWTWMKG
      ZQWMWMOGQUGPUOUPUHWLXECWMWOWIWMUQZWKXDBXGWJXBWHWIWMAEURUSUTVAVFBXBVBZVCXC
      XAWHWIAWQVDJZFZGZBHZCWOMWPXCWOWQBXIACWQVEJZWOXMWOUQQXMWQWNRWRXMNWNRGZQAWM
      VGZPVHUPVIZXINZWQKGZXCXNXRXOWQWNRWRVJVFPXCWNKAXCAKGZAWNGXCXEXSXHXEXDBVKXS
      XDBVQXDXSBXDXFXSWMAWHVLVMVNSVOZAWMKVPSXTVRZVSXCXLWLCWOXCWIWOGZVTZXKWKBYCX
      JWJWHYCWOWQWNXIRWIAWRXPXNYCXOPXQXCYBWAXCAWOGYBYAWBWCUSUTWDWESWFWG $.

    $( Alternate definition of ` TermCat ` .  See also ~ df-termc .
       (Contributed by Zhi Wang, 18-Oct-2025.) $)
    termc $p |- ( C e. TermCat <-> A. d e. Cat E! f f e. ( d Func C ) ) $=
      ( ctermc wcel cv cfunc co weu ccat wral simpr simpl functermceu ralrimiva
      wa c1o csetc cfv cpr cin wss wi inss2 ssralv ax-mp termc2 syl impbii ) AD
      EZBFCFZAGHEBIZCJKZUJULCJUJUKJEZPUKABUJUNLUJUNMNOUMULCAQRSTZJUAZKZUJUPJUBU
      MUQUCUOJUDULCUPJUEUFABCUGUHUI $.

    $( Alternate definition of ` TermCat ` .  See also ~ df-termc and
       ~ dftermc3 .  (Contributed by Zhi Wang, 18-Oct-2025.) $)
    dftermc2 $p |- TermCat = { c | A. d e. Cat E! f f e. ( d Func c ) } $=
      ( cv cfunc co wcel weu ccat wral ctermc termc eqabi ) ADCDBDZEFGAHCIJBKNA
      CLM $.
  $}

  ${
    $d C f $.  $d D f $.
    eufunc.f $e |- ( ph -> E! f f e. ( C Func D ) ) $.
    eufunc.a $e |- A = ( Base ` C ) $.
    eufunc.0 $e |- ( ph -> A =/= (/) ) $.
    eufunc.b $e |- B = ( Base ` D ) $.
    $( If there exists a unique functor from a non-empty category, then the
       base of the target category is at most a singleton.  (Contributed by Zhi
       Wang, 19-Oct-2025.) $)
    eufunclem $p |- ( ph -> B ~<_ 1o ) $=
      ( cfunc co cdom wbr c1o c1st cfv wcel ccat syl cen cdiag wf1 eqid wex weu
      cv euex c2nd wrel relfunc 1st2ndbr mpan funcrcl3 exlimiv funcrcl2 diag1f1
      ovex f1dom euen1b sylibr domentr syl2anc ) ACDEKLZMNZVDOUANZCOMNACVDEDUBL
      ZPQZUCVEACBEDVGVGUDAFUGZVDRZFUEZESRZAVJFUFZVKGVJFUHTZVJVLFVJDEVIPQZVIUIQZ
      VDUJVJVOVPVDNDEUKVIVDULUMZUNUOTAVKDSRZVNVJVRFVJDEVOVPVQUPUOTJHIUQCVDVHDEK
      URUSTAVMVFGFVDUTVACVDOVBVC $.

    $d A f $.  $d B f $.  $d B x $.
    $( If there exists a unique functor from a non-empty category, then the
       base of the target category is a singleton.  (Contributed by Zhi Wang,
       19-Oct-2025.) $)
    eufunc $p |- ( ph -> E! x x e. B ) $=
      ( cv wcel wex wmo weu c0 wne wceq cfunc co wi euex wa simpr simpl func0g2
      ex exlimiv 3syl imp mteqand n0 sylib c1o cdom wbr eufunclem modom2 sylibr
      df-eu sylanbrc ) ABLDMZBNZVCBOZVCBPADQRVDADQCQJADQSZCQSZAGLZEFTUAMZGPVIGN
      VFVGUBZHVIGUCVIVJGVIVFVGVIVFUDCDEFVHIKVIVFUEVIVFUFUGUHUIUJUKULBDUMUNADUOU
      PUQVEACDEFGHIJKURBDUSUTVCBVAVB $.
  $}

  ${
    idfudiag1lem.1 $e |- ( ph -> ( _I |` A ) = ( A X. { B } ) ) $.
    idfudiag1lem.2 $e |- ( ph -> A =/= (/) ) $.
    $( Lemma for ~ idfudiag1bas and ~ idfudiag1 .  (Contributed by Zhi Wang,
       19-Oct-2025.) $)
    idfudiag1lem $p |- ( ph -> A = { B } ) $=
      ( csn cxp crn cid cres rnresi rneqd eqtr3id c0 wne wceq rnxp syl eqtrd )
      ABBCFZGZHZTABIBJZHUBBKAUCUADLMABNOUBTPEBTQRS $.
  $}

  ${
    $d B f p x y z $.  $d C f p x y z $.  $d I f p x y z $.  $d K f p x y z $.
    $d L f p x y z $.  $d X f p x y z $.  $d f p ph x y z $.
    idfudiag1.i $e |- I = ( idFunc ` C ) $.
    idfudiag1.l $e |- L = ( C DiagFunc C ) $.
    idfudiag1.c $e |- ( ph -> C e. Cat ) $.
    idfudiag1.b $e |- B = ( Base ` C ) $.
    idfudiag1.x $e |- ( ph -> X e. B ) $.
    idfudiag1.k $e |- K = ( ( 1st ` L ) ` X ) $.
    idfudiag1.e $e |- ( ph -> I = K ) $.
    $( If the identity functor of a category is the same as a constant functor
       to the category, then the base is a singleton.  (Contributed by Zhi
       Wang, 19-Oct-2025.) $)
    idfudiag1bas $p |- ( ph -> B = { X } ) $=
      ( vp vy vz cxp cv cfv cid cres chom cmpt cop csn co ccid cmpo wceq diag1a
      eqid idfuval 3eqtr3d cvv wcel cbs fvexi resiexg ax-mp xpex mptex syl ne0d
      opth1 idfudiag1lem ) ABGAUABUBZOBBRZUAOSCUCTZTUBZUDZUEZBGUFRZPQBBPSQSVIUG
      GCUHTZTUFRUIZUEZUJVGVMUJADEVLVPNAOBCVIDHKJVIULZUMAPQBBCCVNVIEFGIJJKLMKVQV
      NULUKUNVGVKVMVOBUOUPVGUOUPBCUQKURZBUOUSUTOVHVJBBVRVRVAVBVEVCABGLVDVF $.

    $( If the identity functor of a category is the same as a constant functor
       to the category, then the category is terminal.  (Contributed by Zhi
       Wang, 19-Oct-2025.) $)
    idfudiag1 $p |- ( ph -> C e. TermCat ) $=
      ( vy vz wcel wceq cfv cvv vx vf vp cthinc cv csn wex ctermc cbs a1i eqidd
      chom wa co ccid wmo cxp cid cres cmpt cmpo cop fveq2 df-ov eqtr4di mpompt
      reseq2d ovex resiexg mp1i ovmpt4d eqid idfuval diag1a 3eqtr3d fvexi ax-mp
      xpex opth simprbi syl snex eqtr3d ccat adantr simprl catidcl idfudiag1bas
      mptex eleqtrd simprr eqtr4d oveq2d ne0d idfudiag1lem mosn isthincd eqeq2d
      elsni sneq spcedv istermc sylanbrc ) ACUDQBUAUEZUFZRZUAUGCUHQAOPBCUBCULSZ
      BCUISRAKUJAXGUKAOUEZBQZPUEZBQZUMZUMZXHXJXGUNZGCUOSZSZUFZRUBUEXNQUBUPXMXNX
      PXMXHXJUCBBUQZURUCUEZXGSZUSZUTZUNURXNUSZXNXQUQZAOPBBYCYBTYBOPBBYCVARAOPUC
      BBYAYCXSXHXJVBZRZXTXNURYFXTYEXGSXNXSYEXGVCXHXJXGVDVEVGVFUJXNTQYCTQXMXHXJX
      GVHZXNTVIVJVKAOPBBYDYBTAURBUSZYBVBZBGUFZUQZOPBBYDVAZVBZRZYBYLRZADEYIYMNAU
      CBCXGDHKJXGVLZVMAOPBBCCXOXGEFGIJJKLMKYPXOVLZVNVOYNYHYKRYOYHYBYKYLBTQYHTQB
      CUIKVPZBTVIVQUCXRYABBYRYRVRWIVSVTWAYDTQXMXNXQYGXPWBVRUJVKWCXMXNXHXOSZXMYS
      XHXHXGUNXNXMBCXOXGXHKYPYQACWDQXLJWEAXIXKWFZWGXMXHXJXHXGXMXHGXJXMXHYJQXHGR
      XMXHBYJYTABYJRZXLABCDEFGHIJKLMNWHZWEZWJXHGWSWAXMXJYJQXJGRXMXJBYJAXIXKWKUU
      CWJXJGWSWAWLWMWJWNWOUBXNXPWPWAJWQAXFUUAUABGLUUBXDGRXEYJBXDGWTWRXAUABCKXBX
      C $.
  $}

  ${
    $d B g x $.  $d C f g x $.  $d g ph x $.
    euendfunc.f $e |- ( ph -> E! f f e. ( C Func C ) ) $.
    euendfunc.b $e |- B = ( Base ` C ) $.
    euendfunc.0 $e |- ( ph -> B =/= (/) ) $.
    $( If there exists a unique endofunctor (a functor from a category to
       itself) for a non-empty category, then the category is terminal.  This
       partially explains why two categories are sufficient in ~ termc2 .
       (Contributed by Zhi Wang, 20-Oct-2025.) $)
    euendfunc $p |- ( ph -> C e. TermCat ) $=
      ( vx vg cv wcel wex sylib wa cfv eqid syl wceq wi cvv ctermc c0 wne cidfu
      n0 cdiag co c1st cfunc ccat weu adantr euex funcrcl simpld exlimiv idfucl
      simpr diag1cl wal wmo eumo eleq1w mo4 simpl eleq1d anbi12d eqeq12 imbi12d
      fvex spc2gv mp2an mp2and idfudiag1 exlimddv ) AHJZBKZCUAKHABUBUCVQHLGHBUE
      MAVQNZBCCUDOZVPCCUFUGZUHOZOZVTVPVSPZVTPZVRDJZCCUIUGZKZDLZCUJKZVRWGDUKZWHA
      WJVQEULZWGDUMQWGWIDWGWIWICCWEUNUOUPQZFAVQURZWBPZVRVSWFKZWBWFKZVSWBRZVRWIW
      OWLCVSWCUQQVRBCCWBVTVPWDWLWLFWMWNUSVRWGIJZWFKZNZWEWRRZSZIUTDUTZWOWPNZWQSZ
      VRWGDVAZXCVRWJXFWKWGDVBQWGWSDIDIWFVCVDMVSTKWBTKXCXESCUDVJVPWAVJXBXEDIVSWB
      TTWEVSRZWRWBRZNZWTXDXAWQXIWGWOWSWPXIWEVSWFXGXHVEVFXIWRWBWFXGXHURVFVGWEVSW
      RWBVHVIVKVLQVMVNVO $.
  $}

  ${
    $d C f $.
    $( If there exists a unique endofunctor (a functor from a category to
       itself) for a category, then it is either initial (empty) or terminal.
       (Contributed by Zhi Wang, 20-Oct-2025.) $)
    euendfunc2 $p |- ( ( C Func C ) ~~ 1o ->
                       ( ( Base ` C ) = (/) \/ C e. TermCat ) ) $=
      ( vf cfunc co c1o cen wbr cbs cfv c0 wceq ctermc wcel wn wa cv weu euen1b
      birani eqid simpr neqned euendfunc ex orrd ) AACDZEFGZAHIZJKZALMZUGUINZUJ
      UGUKOZUHABUGBPUFMBQUKBUFRSUHTULUHJUGUKUAUBUCUDUE $.
  $}

  ${
    $d C a b c f g x y $.
    $( There exists a unique disjointified arrow in a terminal category.
       (Contributed by Zhi Wang, 20-Oct-2025.) $)
    termcarweu $p |- ( C e. TermCat -> E! a a e. ( Arrow ` C ) ) $=
      ( vb vx ctermc wcel cv carw cfv wceq wb wal eqid wa cotp co adantr adantl
      simpr termcbasmo wex weu cbs csn termcbas ccid choma chom termccatd vsnid
      id eleqtrrid catidcl elhomai2 cdoma ccoda c2nd arwdmcd arwdm arwcd arwhom
      oteq123d eqtrd homarw sselid eqeltrd impbida alrimiv bibi2d albidv spcedv
      termchommo eqeq2 exlimddv eu6im syl ) AEFZBGZAHIZFZVRCGZJZKZBLZCUAZVTBUBV
      QAUCIZDGZUDZJZWEDVQDWFAVQUKZWFMZUEVQWINZWDVTVRWGWGWGAUFIZIZOZJZKZBLCWGWGA
      UGIZPZWOWLWFAWNWRAUHIZWGWGWRMZWKWLAVQVQWIWJQZUIZWTMZWLWGWHWFDUJVQWISULZXE
      WLWFAWMWTWGWKXDWMMXCXEUMZUNZWLWQBWLVTWPWLVTNZVRVRUOIZVRUPIZVRUQIZOZWOVTVR
      XLJWLVSAVRVSMZURRXHXIWGXJWGXKWNXHWFAXIWGWLVQVTXBQZWKVTXIWFFWLVSWFAVRXMWKU
      SRZWLWGWFFVTXEQZTXHWFAXJWGXNWKVTXJWFFWLVSWFAVRXMWKUTRZXPTXHWFAXKWNWTWGXIX
      JWGXNWKXOXQXDVTXKXIXJWTPFWLVSAVRWTXMXDVARXPXPWLWNWGWGWTPFVTXFQVLVBVCWLWPN
      VRWOVSWLWPSWLWOVSFWPWLWSVSWOVSAWRWGWGXMXAVDXGVEQVFVGVHWAWOJZWCWQBXRWBWPVT
      WAWOVRVMVIVJVKVNVTBCVOVP $.

    $( If a structure has a unique disjointified arrow, then the structure is a
       thin category.  (Contributed by Zhi Wang, 20-Oct-2025.) $)
    arweuthinc $p |- ( E! a a e. ( Arrow ` C ) -> C e. ThinCat ) $=
      ( vx vy vf vg vb cv cfv wcel eqidd wa weq co wral wmo cotp wceq eqid vex
      carw weu chom eqeq1 eqeq2 eumo ad2antrr moel sylib choma homarw ccat euex
      cbs wex arwrcl exlimiv syl simplrl simplrr simprl elhomai2 sselid rspc2dv
      simprr otth simp3bi ralrimivva sylibr isthincd ) BHZAUAIZJZBUBZCDAUNIZAEA
      UCIZVNVOKVNVPKVNCHZVOJZDHZVOJZLZLZEFMZFVQVSVPNZOEWDOEHZWDJZEPWBWCEFWDWDWB
      WFFHZWDJZLZLZVQVSWEQZVQVSWGQZRZWCWJBGMZWMWKGHZRBGWKWLVLVLVKWKWOUDWOWLWKUE
      WJVMBPZWNGVLOBVLOVNWPWAWIVMBUFUGBGVLUHUIWJVQVSAUJIZNZVLWKVLAWQVQVSVLSZWQS
      ZUKZWJVOAWEWQVPVQVSWTVOSZVNAULJZWAWIVNVMBUOXCVMBUMVMXCBVLAVKWSUPUQURZUGZV
      PSZVNVRVTWIUSZVNVRVTWIUTZWBWFWHVAVBVCWJWRVLWLXAWJVOAWGWQVPVQVSWTXBXEXFXGX
      HWBWFWHVEVBVCVDWMCCMDDMWCVQVSVQVSWEWGCTDTETVFVGURVHEFWDUHVIXDVJ $.

    $( If a structure has a unique disjointified arrow, then the structure is a
       terminal category.  (Contributed by Zhi Wang, 20-Oct-2025.) $)
    arweutermc $p |- ( E! a a e. ( Arrow ` C ) -> C e. TermCat ) $=
      ( vx vy vb cv cfv wcel weu wex wmo eqid syl wceq wral wa cotp adantr moel
      co carw cthinc cbs ctermc arweuthinc euex cdoma arwdm spcedv exlimiv ccid
      eleq1 eqeq1 eqeq2 eumo sylib choma homarw chom thinccatd catidcl elhomai2
      simprl sselid simprr rspc2dv fvex otth simp1bi ralrimivva sylibr sylanbrc
      vex df-eu istermc2 ) BFZAUAGZHZBIZAUBHZCFZAUCGZHZCIZAUDHABUEZVSWCCJZWCCKZ
      WDVSVRBJWFVRBUFVRWFBVRWCVPUGGZWBHCWBWHVQWBAVPVQLZWBLZUHZWKWAWHWBULUIUJMVS
      WADFZNZDWBOCWBOWGVSWMCDWBWBVSWCWLWBHZPZPZWAWAWAAUKGZGZQZWLWLWLWQGZQZNZWMW
      PVPEFZNZXBWSXCNBEWSXAVQVQVPWSXCUMXCXAWSUNWPVRBKZXDEVQOBVQOVSXEWOVRBUORBEV
      QSUPWPWAWAAUQGZTVQWSVQAXFWAWAWIXFLZURWPWBAWRXFAUSGZWAWAXGWJWPAVSVTWOWERUT
      ZXHLZVSWCWNVCZXKWPWBAWQXHWAWJXJWQLZXIXKVAVBVDWPWLWLXFTVQXAVQAXFWLWLWIXGUR
      WPWBAWTXFXHWLWLXGWJXIXJVSWCWNVEZXMWPWBAWQXHWLWJXJXLXIXMVAVBVDVFXBWMWMWRWT
      NWAWAWLWLWRWTCVMZXNWAWQVGVHVIMVJCDWBSVKWCCVNVLCWBAWJVOVL $.

    $( Alternate definition of ` TermCat ` .  See also ~ df-termc ,
       ~ dftermc2 .  (Contributed by Zhi Wang, 20-Oct-2025.) $)
    dftermc3 $p |- TermCat = { c | ( Arrow ` c ) ~~ 1o } $=
      ( va cv carw cfv c1o cen wbr ctermc wcel weu termcarweu arweutermc impbii
      euen1b bitr4i eqabi ) ACZDEZFGHZAIRIJZBCSJBKZTUAUBRBLRBMNBSOPQ $.
  $}

  ${
    $d A k x y z $.  $d B y z $.  $d C k x y z $.  $d D k x y z $.  $d K y z $.
    $d L k x y z $.  $d X y z $.  $d Y y z $.  $d k ph y z $.
    diag1f1o.a $e |- A = ( Base ` C ) $.
    diag1f1o.d $e |- ( ph -> D e. TermCat ) $.
    ${
      termcfuncval.k $e |- ( ph -> K e. ( D Func C ) ) $.
      termcfuncval.b $e |- B = ( Base ` D ) $.
      termcfuncval.y $e |- ( ph -> Y e. B ) $.
      termcfuncval.x $e |- X = ( ( 1st ` K ) ` Y ) $.
      ${
        termcfuncval.1 $e |- .1. = ( Id ` C ) $.
        termcfuncval.i $e |- I = ( Id ` D ) $.
        $( The value of a functor from a terminal category.  (Contributed by
           Zhi Wang, 20-Oct-2025.) $)
        termcfuncval $p |- ( ph -> ( X e. A /\ K = <. { <. Y , X >. } ,
         { <. <. Y , Y >. , { <. ( I ` Y ) , ( .1. ` X ) >. } >. } >. ) ) $=
          ( cop cfv wcel csn wceq c1st c2nd func1st2nd ffvelcdmd eqeltrid cfunc
          funcf1 co relfunc 1st2nd sylancr wf wa termcbas2 feq2d mpbid wb fsn2g
          syl simprd opeq2i sneqi eqtr4di wfn cxp funcfn2 sqxpeqd xpsng syl2anc
          wrel eqtrd fneq2d opex fnsnb sylib df-ov chom funcf2 termchom oveq12i
          eqid eqcomd a1i feq23d mpbird fvex funcid fveq2i opeq2d sneqd eqtr3id
          fsn2 opeq12d jca ) AIBUAHJISZUBZJJSZJGTZIFTZSZUBZSZUBZSZUCAIJHUDTZTZB
          PACBJXHACBEDXHHUETZNKAEDHMUFZUJZOUGUHAHXHXJSZXGAEDUIUKZVMHXNUAHXMUCED
          ULMHXNUMUNAXHWSXJXFAXHJXISZUBZWSAXIBUAZXHXPUCZAJUBZBXHUOZXQXRUPZACBXH
          UOXTXLACXSBXHACEJLNOUQZURUSAJCUAZXTYAUTOJBXHCVAVBUSVCWRXOIXIJPVDVEVFA
          XJWTWTXJTZSZUBZXFAXJWTUBZVGZXJYFUCAXJCCVHZVGYHACEDXHXJNXKVIAYIYGXJAYI
          XSXSVHZYGACXSYBVJAYCYCYJYGUCOOJJCCVKVLVNVOUSWTXJJJVPVQVRAYEXEAYDXDWTA
          YDJJXJUKZXDJJXJVSAYKXAXAYKTZSZUBZXDAYLIIDVTTZUKZUAZYKYNUCZAXAUBZYPYKU
          OZYQYRUPAYTJJEVTTZUKZXIXIYOUKZYKUOACEDXHXJUUAYOJJNUUAWDZYOWDXKOOWAAYS
          YPUUBUUCYKAUUBYSACEGUUAJJLNOOUUDRWBWEYPUUCUCAIXIIXIYOPPWCWFWGWHXAYPYK
          JGWIWOVRVCAYMXCAYLXBXAAYLXIFTXBACEGDXHXJFJNRQXKOWJIXIFPWKVFWLWMVNWNWL
          WMVNWPVNWQ $.
      $}

      diag1f1olem.l $e |- L = ( C DiagFunc D ) $.
      $( To any functor from a terminal category can an object in the target
         base be assigned.  (Contributed by Zhi Wang, 21-Oct-2025.) $)
      diag1f1olem $p |- ( ph -> ( X e. A /\ K = ( ( 1st ` L ) ` X ) ) ) $=
        ( vy cfv wceq csn vz wcel c1st cop ccid eqid termcfuncval simpld cxp cv
        chom co cmpo termcbas2 xpeq1d xpsng syl2anc adantr ctermc simprl simprr
        eqtrd termchom2 fvex xpsn eqtrdi mpoeq123dva cvv snex a1i eqidd syl3anc
        mposn opeq12d c2nd func1st2nd funcrcl3 termccatd diag1a simprd 3eqtr4rd
        wa jca ) AHBUBZFHGUCRRZSAWDFIHUDTZIIUDIEUERZRZHDUERZRZUDZTZUDTZUDZSZABC
        DEWIWGFHIJKLMNOWIUFZWGUFZUGZUHZACHTZUIZQUACCQUJZUAUJZEUKRZULZWJTZUIZUMZ
        UDWNWEFAXAWFXHWMAXAITZWTUIZWFACXIWTACEIKMNUNZUOAICUBZWDXJWFSNWSIHCBUPUQ
        VBAXHQUAXIXIWLUMZWMAQUACCXGXIXIWLXKACXISXBCUBZXKURAXNXCCUBZWBZWBZXGWHTZ
        XFUIWLXQXEXRXFXQCEWGXDXBXCIAEUSUBXPKURMAXNXOUTAXNXOVAXDUFZWQAXLXPNURVCU
        OWHWJIWGVDHWIVDVEVFVGAXLXLWLVHUBZXMWMSNNXTAWKVIVJQUAIIWLWLVHWLXMCCXMUFX
        BISWLVKXCISWLVKVMVLVBVNAQUABCDEWIXDWEGHPAEDFUCRFVORAEDFLVPVQAEKVRJWSWEU
        FMXSWPVSAWDWOWRVTWAWC $.
    $}

    diag1f1o.c $e |- ( ph -> C e. Cat ) $.
    diag1f1o.l $e |- L = ( C DiagFunc D ) $.
    $( The object part of the diagonal functor is a bijection if ` D ` is
       terminal.  So any functor from a terminal category is one-to-one
       correspondent to an object of the target base.  (Contributed by Zhi
       Wang, 21-Oct-2025.) $)
    diag1f1o $p |- ( ph -> ( 1st ` L ) : A -1-1-onto-> ( D Func C ) ) $=
      ( vy vk vx c1st cfv eqid cv wcel wex wa wceq cfunc wf1 wfo wf1o termccatd
      co cbs c0 wne weu cthinc ctermc istermc2 sylib simprd euex syl n0 diag1f1
      sylibr wf wrex f1f csn termcbas adantr fveq2 eqeq2d ad2antrr simplr vsnid
      wral simpr eleqtrrid diag1f1olem simpld rspcedvdw exlimddv dffo3 sylanbrc
      ralrimiva df-f1o ) ABDCUAUFZEMNZUBZBWCWDUCZBWCWDUDABDUGNZCDEIHADGUEFWGOZA
      JPZWGQZJRZWGUHUIAWJJUJZWKADUKQZWLADULQZWMWLSGJWGDWHUMUNUOWJJUPUQJWGURUTUS
      ZABWCWDVAZKPZLPZWDNZTZLBVBZKWCVLWFAWEWPWOBWCWDVCUQAXAKWCAWQWCQZSZWGWIVDZT
      ZXAJAXEJRXBAJWGDGWHVEVFXCXESZWTWQWIWQMNNZWDNZTZLXGBWRXGTWSXHWQWRXGWDVGVHX
      FXGBQZXIXFBWGCDWQEXGWIFAWNXBXEGVIAXBXEVJWHXFWIXDWGJVKXCXEVMVNXGOIVOZVPXFX
      JXIXKUOVQVRWALKBWCWDVSVTBWCWDWBVT $.
  $}

  ${
    termcnatval.c $e |- ( ph -> C e. TermCat ) $.
    termcnatval.n $e |- N = ( C Nat D ) $.
    termcnatval.a $e |- ( ph -> A e. ( F N G ) ) $.
    termcnatval.b $e |- B = ( Base ` C ) $.
    termcnatval.x $e |- ( ph -> X e. B ) $.
    termcnatval.r $e |- R = ( A ` X ) $.
    $( Value of natural transformations for a terminal category.  (Contributed
       by Zhi Wang, 21-Oct-2025.) $)
    termcnatval $p |- ( ph -> A = { <. X , R >. } ) $=
      ( cfv cop csn wfn wceq c1st c2nd nat1st2nd natfn termcbas2 fneq2d wcel wb
      mpbid fnsnbg syl opeq2i sneqi eqtr4di ) ABJJBQZRZSZJFRZSABJSZTZBURUAZABCT
      VAABCDEGUBQGUCQHUBQHUCQILABDEGHILMUDNUEACUTBACDJKNOUFUGUJAJCUHVAVBUIOJBCU
      KULUJUSUQFUPJPUMUNUO $.
  $}

  ${
    $d A f m z $.  $d C f m z $.  $d D f m z $.  $d H f m z $.  $d L f m z $.
    $d N f m z $.  $d X f m z $.  $d Y f m z $.  $d f m ph z $.
    diag2f1o.l $e |- L = ( C DiagFunc D ) $.
    diag2f1o.a $e |- A = ( Base ` C ) $.
    diag2f1o.h $e |- H = ( Hom ` C ) $.
    diag2f1o.x $e |- ( ph -> X e. A ) $.
    diag2f1o.y $e |- ( ph -> Y e. A ) $.
    diag2f1o.n $e |- N = ( D Nat C ) $.
    diag2f1o.d $e |- ( ph -> D e. TermCat ) $.
    ${
      diag2f1olem.m $e |- ( ph -> M e.
                            ( ( ( 1st ` L ) ` X ) N ( ( 1st ` L ) ` Y ) ) ) $.
      diag2f1olem.b $e |- B = ( Base ` D ) $.
      diag2f1olem.z $e |- ( ph -> Z e. B ) $.
      diag2f1olem.f $e |- F = ( M ` Z ) $.
      $( Lemma for ~ diag2f1o .  (Contributed by Zhi Wang, 21-Oct-2025.) $)
      diag2f1olem $p |- ( ph -> ( F e. ( X H Y )
                               /\ M = ( ( X ( 2nd ` L ) Y ) ` F ) ) ) $=
        ( co wcel c2nd cfv wceq c1st nat1st2nd natcl natrcl2 funcrcl3 termccatd
        diag11 oveq12d eleqtrd eqeltrid cop csn termcnatval cxp diag2 termcbas2
        eqid xpeq1d xpsng syl2anc 3eqtrd eqtr4d jca ) AFKLGUEZUFZIFKLHUGUHUEUHZ
        UIAFMIUHZVMUDAVPMKHUJUHZUHZUJUHZUHZMLVQUHZUJUHZUHZGUEVMAICEDVSVRUGUHZGW
        BWAUGUHZJMSAIEDVRWAJSUAUKZUBPUCULAVTKWCLGABCDEVRHKMNAEDVSWDAIEDVSWDWBWE
        JSWFUMUNZAETUOZOQVRVFUBUCUPABCDEWAHLMNWGWHORWAVFUBUCUPUQURUSZAIMFUTVAZV
        OAICEDFVRWAJMTSUAUBUCUDVBAVOCFVAZVCMVAZWKVCZWJABCDEFGHKLNOUBPWGWHQRWIVD
        ACWLWKACEMTUBUCVEVGAMCUFVNWMWJUIUCWIMFCVMVHVIVJVKVL $.
    $}

    diag2f1o.c $e |- ( ph -> C e. Cat ) $.
    $( If ` D ` is terminal, the morphism part of a diagonal functor is
       bijective functions from hom-sets into sets of natural transformations.
       (Contributed by Zhi Wang, 21-Oct-2025.) $)
    diag2f1o $p |- ( ph -> ( X ( 2nd ` L ) Y ) : ( X H Y ) -1-1-onto->
     ( ( ( 1st ` L ) ` X ) N ( ( 1st ` L ) ` Y ) ) ) $=
      ( vz cfv wcel vm vf co c1st c2nd wf1 wfo wf1o cbs termccatd cv wex c0 wne
      eqid weu cthinc ctermc wa istermc2 sylib simprd euex n0 sylibr diag2f1 wf
      syl wceq wrex wral f1f termcbas adantr fveq2 eqeq2d ad2antrr simplr vsnid
      csn simpr eleqtrrid diag2f1olem simpld rspcedvdw exlimddv ralrimiva dffo3
      sylanbrc df-f1o ) AHIEUCZHFUDSZSIWLSGUCZHIFUESUCZUFZWKWMWNUGZWKWMWNUHABDU
      ISZCDEFGHIJKWQUOZLQADPUJMNARUKZWQTZRULZWQUMUNAWTRUPZXAADUQTZXBADURTZXCXBU
      SPRWQDWRUTVAVBWTRVCVHRWQVDVEOVFZAWKWMWNVGZUAUKZUBUKZWNSZVIZUBWKVJZUAWMVKW
      PAWOXFXEWKWMWNVLVHAXKUAWMAXGWMTZUSZWQWSVTZVIZXKRAXORULXLARWQDPWRVMVNXMXOU
      SZXJXGWSXGSZWNSZVIZUBXQWKXHXQVIXIXRXGXHXQWNVOVPXPXQWKTZXSXPBWQCDXQEFXGGHI
      WSJKLAHBTXLXOMVQAIBTXLXONVQOAXDXLXOPVQAXLXOVRWRXPWSXNWQRVSXMXOWAWBXQUOWCZ
      WDXPXTXSYAVBWEWFWGUBUAWKWMWNWHWIWKWMWNWJWI $.
  $}

  ${
    $d C x y $.  $d D x y $.  $d L x y $.  $d Q x y $.  $d ph x y $.
    diagffth.c $e |- ( ph -> C e. Cat ) $.
    diagffth.d $e |- ( ph -> D e. TermCat ) $.
    diagffth.q $e |- Q = ( D FuncCat C ) $.
    ${
      diagffth.l $e |- L = ( C DiagFunc D ) $.
      $( The diagonal functor is a fully faithful functor from a category ` C `
         to the category of functors from a terminal category to ` C ` .
         (Contributed by Zhi Wang, 21-Oct-2025.) $)
      diagffth $p |- ( ph -> L e. ( ( C Full Q ) i^i ( C Faith Q ) ) ) $=
        ( vx vy cfv co wcel wbr cv wral wa eqid adantr c1st c2nd cop cful cfunc
        cfth cin wrel wceq relfunc termccatd diagcl 1st2nd chom cnat func1st2nd
        sylancr wf1o cbs simprl simprr ctermc ccat diag2f1o ralrimivva sylanbrc
        fuchom isffth2 df-br sylib eqeltrd ) AEEUALZEUBLZUCZBDUDMBDUFMUGZABDUEM
        ZUHEVPNEVNUIBDUJABCDEIFACGUKHULZEVPUMUQAVLVMVOOZVNVONAVLVMVPOJPZKPZBUNL
        ZMVSVLLVTVLLCBUOMZMVSVTVMMURZKBUSLZQJWDQVRABDEVQUPAWCJKWDWDAVSWDNZVTWDN
        ZRZRWDBCWAEWBVSVTIWDSZWASZAWEWFUTAWEWFVAWBSZACVBNWGGTABVCNWGFTVDVEJKWDB
        DVLVMWAWBWHWICBDWBHWJVGVHVFVLVMVOVIVJVK $.
    $}

    diagciso.e $e |- E = ( CatCat ` U ) $.
    diagciso.u $e |- ( ph -> U e. V ) $.
    diagciso.c $e |- ( ph -> C e. U ) $.
    diagciso.1 $e |- ( ph -> Q e. U ) $.
    ${
      diagciso.i $e |- I = ( Iso ` E ) $.
      diagciso.l $e |- L = ( C DiagFunc D ) $.
      $( The diagonal functor is an isomorphism from a category ` C ` to the
         category of functors from a terminal category to ` C ` .

         It is provable that the inverse of the diagonal functor is the mapped
         object by the transposed curry of ` ( D evalF C ) ` , i.e.,
         ` U. ran ( 1st `` ( <. D , Q >. curryF ( ( D evalF C ) `
         ` o.func ( D swapF Q ) ) ) ) ` .

         (Contributed by Zhi Wang, 21-Oct-2025.) $)
      diagciso $p |- ( ph -> L e. ( C I Q ) ) $=
        ( co cfv wcel cful cfth cin cbs c1st wf1o diagffth eqid diag1f1o fucbas
        cfunc ccat elind catcbas eleqtrrd termccatd fuccat catciso mpbir2and )
        AHBDGSUAHBDUBSBDUCSUDUABUETZCBULSZHUFTUGABCDHJKLRUHAVABCHVAUIZKJRUJAFUE
        TZFVAVBEHGIBDMVDUIZVCCBDLUKNABEUMUDZVDAEUMBOJUNAVDFEIMVENUOZUPADVFVDAEU
        MDPACBDLACKUQJURUNVGUPQUSUT $.
    $}

    $( Any category ` C ` is isomorphic to the category of functors from a
       terminal category to ` C ` .  See also the "Properties" section of
       ~ https://ncatlab.org/nlab/show/terminal+category .  Therefore the
       number of categories isomorphic to a non-empty category is at least the
       number of singletons, so large ( ~ snnex ) that these isomorphic
       categories form a proper class.  (Contributed by Zhi Wang,
       21-Oct-2025.) $)
    diagcic $p |- ( ph -> C ( ~=c ` E ) Q ) $=
      ( cfv eqid wcel ccat elind eleqtrrd cbs cdiag co ciso catccat syl catcbas
      cin termccatd fuccat diagciso brcici ) AFUAOZFBCUBUCZFUDOZBDUOPZUMPZAEGQF
      RQLFEGKUEUFABERUHZUMAERBMHSAUMFEGKUQLUGZTADURUMAERDNACBDJACIUIHUJSUSTABCD
      EFUOUNGHIJKLMNUPUNPUKUL $.
  $}

  ${
    $d C a b f g x y $.  $d D a b f g x y $.  $d F a b f g x $.
    $d Q a b f g x y $.  $d V a b f g x $.  $d a b f g ph x y $.
    funcsn.q $e |- Q = ( C FuncCat D ) $.
    ${
      funcsn.f $e |- ( ph -> F e. V ) $.
      funcsn.c $e |- ( ph -> ( C Func D ) = { F } ) $.
      funcsn.d $e |- ( ph -> D e. ThinCat ) $.
      $( The category of one functor to a thin category is terminal.
         (Contributed by Zhi Wang, 17-Nov-2025.) $)
      funcsn $p |- ( ph -> Q e. TermCat ) $=
        ( vf va vb wcel co cv wceq cfv eqid wa vg vx cthinc csn wex ctermc cnat
        cfunc cbs fucbas a1i chom fuchom wral c1st c2nd simprl nat1st2nd simprr
        wmo natfn natrcl2 funcf1 ffvelcdmda natrcl3 adantr simpr natcl ad2antrr
        cop thincmo2 eqfnfvd ralrimivva moel sylibr snidg syl eleqtrrd funcrcl2
        func1st2nd thinccatd fuccat isthincd eqeq2d spcedv istermc sylanbrc
        sneq ) ADUCNBCUHOZKPZUDZQZKUEDUFNAKUAWIDLBCUGOZWIDUIRQABCDGUJZUKWMDULRQ
        ABCDWMGWMSZUMUKALPZWJUAPZWMOZNZLUTZWJWINWQWINTAWPMPZQZMWRUNLWRUNWTAXBLM
        WRWRAWSXAWRNZTZTZUBBUIRZWPXAXEWPXFBCWJUORZWJUPRZWQUORZWQUPRZWMWOXEWPBCW
        JWQWMWOAWSXCUQURZXFSZVAXEXAXFBCXGXHXIXJWMWOXEXABCWJWQWMWOAWSXCUSURZXLVA
        XEUBPZXFNZTZCUIRZCXNWPRXNXARCULRZXNXGRXNXIRXEXFXQXNXGXEXFXQBCXGXHXLXQSZ
        XEWPBCXGXHXIXJWMWOXKVBVCVDXEXFXQXNXIXEXFXQBCXIXJXLXSXEWPBCXGXHXIXJWMWOX
        KVEVCVDXPWPXFBCXGXHXRXIXJWMXNWOXEWPXGXHVJXIXJVJWMOZNXOXKVFXLXRSZXEXOVGZ
        VHXPXAXFBCXGXHXRXIXJWMXNWOXEXAXTNXOXMVFXLYAYBVHXSYAACUCNXDXOJVIVKVLVMLM
        WRVNVOVFABCDGABCEUOREUPRABCEAEEUDZWIAEFNEYCNHEFVPVQIVRVTVSACJWAWBWCAWLW
        IYCQKFEHIWJEQWKYCWIWJEWHWDWEKWIDWNWFWG $.
    $}

    fucterm.c $e |- ( ph -> C e. Cat ) $.
    fucterm.d $e |- ( ph -> D e. TermCat ) $.
    $( The category of functors to a terminal category is terminal.
       (Contributed by Zhi Wang, 17-Nov-2025.) $)
    fucterm $p |- ( ph -> Q e. TermCat ) $=
      ( vx vy cbs cfv cxp cv chom co cmpo cop cvv wcel eqid opex a1i functermc2
      termcthind funcsn ) ABCDBJKZCJKZLZHIUFUFHMZIMZBNKZOUIUHKUJUHKCNKZOLPZQZRE
      UNRSAUHUMUAUBAHIUFUGBCUHUMUKULFGUFTUGTUKTULTUHTUMTUCACGUDUE $.
  $}

  ${
    $d C a b f g $.  $d D a b f g $.  $d Q a b f g $.  $d V a b f g $.
    $d a b f g ph $.
    0fucterm.c $e |- ( ph -> C e. V ) $.
    0fucterm.b $e |- ( ph -> (/) = ( Base ` C ) ) $.
    0fucterm.d $e |- ( ph -> D e. Cat ) $.
    0fucterm.q $e |- Q = ( C FuncCat D ) $.
    $( The category of functors from an initial category is terminal.
       (Contributed by Zhi Wang, 17-Nov-2025.) $)
    0fucterm $p |- ( ph -> Q e. TermCat ) $=
      ( vf va vb wcel co cv wceq cfv wa c0 wfn cthinc cfunc csn wex ctermc cnat
      cbs fucbas a1i chom eqid fuchom wral wmo c1st c2nd simprl nat1st2nd natfn
      vg ad2antrr fneq2d mpbird sylib simprr eqtr4d ralrimivva moel sylibr ccat
      fn0 0catg syl2anc fuccat isthincd cop cvv opex 0funcg sneq eqeq2d istermc
      spcedv sylanbrc ) ADUAMBCUBNZJOZUCZPZJUDDUEMAJUTWEDKBCUFNZWEDUGQPABCDIUHZ
      UIWIDUJQPABCDWIIWIUKZULUIAWFWEMUTOZWEMRZRZKOZLOZPZLWFWLWINZUMKWRUMWOWRMZK
      UNWNWQKLWRWRWNWSWPWRMZRZRZWOSWPXBWOSTZWOSPXBXCWOBUGQZTXBWOXDBCWFUOQZWFUPQ
      ZWLUOQZWLUPQZWIWKXBWOBCWFWLWIWKWNWSWTUQURXDUKZUSXBSXDWOASXDPZWMXAGVAZVBVC
      WOVKVDXBWPSTZWPSPXBXLWPXDTXBWPXDBCXEXFXGXHWIWKXBWPBCWFWLWIWKWNWSWTVEURXIU
      SXBSXDWPXKVBVCWPVKVDVFVGKLWRVHVIABCDIABEMXJBVJMFGBEVLVMHVNVOAWHWESSVPZUCZ
      PJVQXMXMVQMASSVRUIABCEFGHVSWFXMPWGXNWEWFXMVTWAWCJWEDWJWBWD $.
  $}

  ${
    $d B f g $.  $d C f g $.  $d I f g $.  $d U f g $.  $d X f g $.
    $d Y f g $.  $d f g ph $.
    termfucterm.c $e |- C = ( CatCat ` U ) $.
    termfucterm.b $e |- B = ( Base ` C ) $.
    termfucterm.i $e |- I = ( Iso ` C ) $.
    termfucterm.x $e |- ( ph -> X e. B ) $.
    termfucterm.xt $e |- ( ph -> X e. TermCat ) $.
    termfucterm.y $e |- ( ph -> Y e. B ) $.
    termfucterm.yt $e |- ( ph -> Y e. TermCat ) $.
    $( All functors between two terminal categories are isomorphisms.
       (Contributed by Zhi Wang, 17-Nov-2025.) $)
    termfucterm $p |- ( ph -> ( X Func Y ) = ( X I Y ) ) $=
      ( vg co wcel wa cfv eqid vf cfunc cv wex ccic ctermc termcciso mpbid ccat
      wbr cicrcl2 syl adantr cfuc termccatd fucterm ad2antrr fucbas simplr cful
      cic fullfunc cfth cin cbs c1st wf1o simpr simpld elin1d sselid termcbasmo
      catcisoi eqeltrd exlimddv impbida eqrdv ) AUAFGUBPZFGEPZAUAUCZVRQZVTVSQZA
      WARZOUCZVSQZWBOAWEOUDZWAAFGCUESUJZWFAGUFQWGNABCDFGHIKMLUGUHZABCOEFGJIAWGC
      UIQWHCFGUKULKMVAUHUMWCWERZVTWDVSWIVRFGUNPZVTWDAWJUFQWAWEAFGWJWJTZAFLUONUP
      UQFGWJWKURAWAWEUSWIFGUTPZVRWDFGVBZWIWLFGVCPZWDWIWDWLWNVDZQFVESZGVESZWDVFS
      VGWICWPWQDWDEFGHWPTZWQTZJWCWEVHZVMVIVJVKVLWTVNVOAWBRZWLVRVTWMXAWLWNVTXAVT
      WOQWPWQVTVFSVGXACWPWQDVTEFGHWRWSJAWBVHVMVIVJVKVPVQ $.
  $}

  ${
    cofuterm.f $e |- ( ph -> F e. ( C Func D ) ) $.
    cofuterm.g $e |- ( ph -> G e. ( D Func E ) ) $.
    cofuterm.k $e |- ( ph -> K e. ( C Func E ) ) $.
    cofuterm.e $e |- ( ph -> E e. TermCat ) $.
    $( Post-compose with a functor to a terminal category.  (Contributed by Zhi
       Wang, 17-Nov-2025.) $)
    cofuterm $p |- ( ph -> ( G o.func F ) = K ) $=
      ( cfunc co cfuc ccofu eqid c1st cfv c2nd func1st2nd fucterm fucbas cofucl
      funcrcl2 termcbasmo ) ABDLMBDNMZFEOMGABDUFUFPZABCEQRESRABCEHTUDKUABDUFUGU
      BABCDEFHIUCJUE $.
  $}

  ${
    $d A k $.  $d B k $.  $d C k $.  $d D k $.  $d E k $.  $d F k $.  $d G k $.
    $d X k $.  $d Y k $.  $d k ph $.
    uobeqterm.a $e |- A = ( Base ` D ) $.
    uobeqterm.b $e |- B = ( Base ` E ) $.
    uobeqterm.x $e |- ( ph -> X e. A ) $.
    uobeqterm.y $e |- ( ph -> Y e. B ) $.
    uobeqterm.f $e |- ( ph -> F e. ( C Func D ) ) $.
    uobeqterm.g $e |- ( ph -> G e. ( C Func E ) ) $.
    uobeqterm.d $e |- ( ph -> D e. TermCat ) $.
    uobeqterm.e $e |- ( ph -> E e. TermCat ) $.
    $( Universal objects and terminal categories.  (Contributed by Zhi Wang,
       17-Nov-2025.) $)
    uobeqterm $p |- ( ph -> dom ( F ( C UP D ) X )
                          = dom ( G ( C UP E ) Y ) ) $=
      ( co wcel vk cpr ccatc cfv ciso cup cdm wceq ccic wbr wex ctermc cbs eqid
      cv ccat cin prid1g syl termccatd elind cvv a1i catcbas eleqtrrd termcciso
      prex prid2g mpbid catccat cic wa cfunc cful fullfunc cfth c1st wf1o simpr
      adantr catcisoi simpld elin1d sselid cofuterm func1st2nd funcf1 ffvelcdmd
      c2nd termcbasmo uobeq3 exlimddv ) AUAUOZEFEFUBZUCUDZUEUDZSTZGIDEUFSSUGHJD
      FUFSSUGUHUAAEFWOUIUDUJZWQUAUKAFULTZWRRAWOUMUDZWOWNEFWOUNZWTUNZAEWNUPUQZWT
      AWNUPEAEULTEWNTQEFULURUSAEQUTVAAWTWOWNVBXAXBWNVBTZAEFVGVCZVDZVEZAFXCWTAWN
      UPFAWSFWNTREFULVHUSAFRUTVAXFVEZQVFVIAWTWOUAWPEFWPUNZXBAXDWOUPTXEWOWNVBXAV
      JUSXGXHVKVIAWQVLZBDEWOWNFGHWPWMIJKAIBTWQMVTZAGDEVMSTWQOVTZXJDEFGWMHXLXJEF
      VNSZEFVMSWMEFVOXJXMEFVPSZWMXJWMXMXNUQTBCWMVQUDZVRXJWOBCWNWMWPEFXAKLXIAWQV
      SZWAWBWCWDZAHDFVMSTWQPVTAWSWQRVTZWEXJCFIXOUDJXRLXJBCIXOXJBCEFXOWMWIUDKLXJ
      EFWMXQWFWGXKWHAJCTWQNVTWJXAXIXPWKWL $.
  $}

  ${
    $d .1. m $.  $d C m $.  $d F m $.  $d I m $.  $d X m $.  $d m ph $.
    isinito4.1 $e |- ( ph -> .1. e. TermCat ) $.
    isinito4.x $e |- ( ph -> X e. ( Base ` .1. ) ) $.
    ${
      isinito4.f $e |- ( ph -> F e. ( C Func .1. ) ) $.
      $( The predicate "is an initial object" of a category, using universal
         property.  (Contributed by Zhi Wang, 17-Nov-2025.) $)
      isinito4 $p |- ( ph -> ( I e. ( InitO ` C )
                           <-> I e. dom ( F ( C UP .1. ) X ) ) ) $=
        ( cinito cfv wcel c0 c1o co c1st cup cdm eqid a1i csetc cdiag setc1obas
        isinito3 cbs c2nd func1st2nd funcrcl2 funcsetc1ocl setc1oterm uobeqterm
        0lt1o ctermc eleq2d bitrid ) EBJKLEMNUAKZBUBOPKKZMBUPQOORZLAEDFBCQOORZL
        BUPUQEUPSZUQSZUDAURUSEANCUEKZBUPCUQDMFUPUTUCVBSMNLAULTHABUPUQUTVAABCDPK
        DUFKABCDIUGUHUIIUPUMLAUJTGUKUNUO $.
    $}

    isinito4a.f $e |- F = ( ( 1st ` ( .1. DiagFunc C ) ) ` X ) $.
    $( The predicate "is an initial object" of a category, using universal
       property.  (Contributed by Zhi Wang, 17-Nov-2025.) $)
    isinito4a $p |- ( ph -> ( I e. ( InitO ` C )
                          <-> I e. dom ( F ( C UP .1. ) X ) ) ) $=
      ( cinito cfv wcel cup co cdm ccat wa anim2i adantr eqid uobrcl simpld cbs
      initorcl ctermc cdiag termccatd simpr diag1cl isinito4 pm5.21nd ) AEBJKLZ
      EDFBCMNNOLZABPLZQZULUNABEUDRUMUNAUMUNCPLBCDFEUAUBRUOBCDEFACUELUNGSZAFCUCK
      ZLUNHSZUOUQCBDCBUFNZFUSTUOCUPUGAUNUHUQTURIUIUJUK $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Preordered sets as thin categories
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $c ProsetToCat $.

  $( Class function defining preordered sets as categories. $)
  cprstc $a class ProsetToCat $.

  ${
    $d C f x y z $.  $d H f $.  $d K k x y z $.  $d X f $.  $d Y f $.
    $d ph f x y z $.
    $( Definition of the function converting a preordered set to a category.
       Justified by ~ prsthinc .

       This definition is somewhat arbitrary.  Example 3.3(4.d) of [Adamek]
       p. 24 demonstrates an alternate definition with pairwise disjoint
       hom-sets.  The behavior of the function is defined entirely, up to
       isomorphism ( ~ thincciso ), by ~ prstcnid , ~ prstchom , and
       ~ prstcthin .  Other important properties include ~ prstcbas ,
       ~ prstcleval , ~ prstcle , ~ prstcocval , ~ prstcoc , ~ prstchom2 , and
       ~ prstcprs .  Use those instead.

       Note that the defining property ~ prstchom is equivalent to ~ prstchom2
       given ~ prstcthin .  See ~ thincn0eu for justification.

       "ProsetToCat" was taken instead of "ProsetCat" because the latter might
       mean the category of preordered sets (classes).  However, "ProsetToCat"
       seems too long.  (Contributed by Zhi Wang, 20-Sep-2024.)
       (New usage is discouraged.) $)
    df-prstc $a |- ProsetToCat = ( k e. Proset |-> ( ( k sSet
          <. ( Hom ` ndx ) , ( ( le ` k ) X. { 1o } ) >. ) sSet
          <. ( comp ` ndx ) , (/) >. ) ) $.

    prstcnid.c $e |- ( ph -> C = ( ProsetToCat ` K ) ) $.
    prstcnid.k $e |- ( ph -> K e. Proset ) $.
    $( Lemma for ~ prstcnidlem and ~ prstcthin .  (Contributed by Zhi Wang,
       20-Sep-2024.)  (New usage is discouraged.) $)
    prstcval $p |- ( ph -> C = ( ( K sSet
                      <. ( Hom ` ndx ) , ( ( le ` K ) X. { 1o } ) >. ) sSet
                  <. ( comp ` ndx ) , (/) >. ) ) $=
      ( vk cprstc cfv cnx chom cple c1o csn cxp cop csts co cco cproset wceq c0
      wcel cv fveq2 xpeq1d opeq2d oveq12d oveq1d df-prstc ovex fvmpt syl eqtrd
      id ) ABCGHZCIJHZCKHZLMZNZOZPQZIRHUAOZPQZDACSUBUOVCTEFCFUCZUPVDKHZURNZOZPQ
      ZVBPQVCSGVDCTZVHVAVBPVIVDCVGUTPVIUNVIVFUSUPVIVEUQURVDCKUDUEUFUGUHFUIVAVBP
      UJUKULUM $.

    ${
      prstcnid.e $e |- E = Slot ( E ` ndx ) $.
      prstcnid.no $e |- ( E ` ndx ) =/= ( comp ` ndx ) $.
      $( Lemma for ~ prstcnid and ~ prstchomval .  (Contributed by Zhi Wang,
         20-Sep-2024.)  (New usage is discouraged.) $)
      prstcnidlem $p |- ( ph -> ( E ` C ) = ( E ` ( K sSet
                       <. ( Hom ` ndx ) , ( ( le ` K ) X. { 1o } ) >. ) ) ) $=
        ( cfv cnx chom cple c1o csn cxp cop csts co cco c0 prstcval setsnid
        fveq2d eqtr4di ) ABCIDJKIDLIMNOPQRZJSIZTPQRZCIUECIABUGCABDEFUAUCTUFCUEG
        HUBUD $.

      prstcnid.nh $e |- ( E ` ndx ) =/= ( Hom ` ndx ) $.
      $( Components other than ` Hom ` and ` comp ` are unchanged.
         (Contributed by Zhi Wang, 20-Sep-2024.) $)
      prstcnid $p |- ( ph -> ( E ` K ) = ( E ` C ) ) $=
        ( cfv cnx chom cple c1o csn cxp cop csts co setsnid prstcnidlem eqtr4id
        ) ADCJDKLJZDMJNOPZQRSCJBCJUDUCCDGITABCDEFGHUAUB $.
    $}

    ${
      prstcbas.b $e |- ( ph -> B = ( Base ` K ) ) $.
      $( The base set is unchanged.  (Contributed by Zhi Wang, 20-Sep-2024.) $)
      prstcbas $p |- ( ph -> B = ( Base ` C ) ) $=
        ( cbs cfv baseid cnx chom wne slotsbhcdif simp2i simp1i prstcnid eqtrd
        cco ) ABDHICHIGACHDEFJKHIZKLIZMZTKSIZMZUAUCMZNOUBUDUENPQR $.
    $}

    ${
      prstcle.l $e |- ( ph -> .<_ = ( le ` K ) ) $.
      $( Value of the less-than-or-equal-to relation is unchanged.
         (Contributed by Zhi Wang, 20-Sep-2024.)  (Proof shortened by AV,
         12-Nov-2024.) $)
      prstcleval $p |- ( ph -> .<_ = ( le ` C ) ) $=
        ( cple cfv pleid cnx cco wne chom slotsdifplendx2 simpli prstcnid eqtrd
        simpri ) ADCHIBHIGABHCEFJKHIZKLIMZTKNIMZOPUAUBOSQR $.

      $( Value of the less-than-or-equal-to relation is unchanged.
         (Contributed by Zhi Wang, 20-Sep-2024.) $)
      prstcle $p |- ( ph -> ( X .<_ Y <-> X ( le ` C ) Y ) ) $=
        ( cple cfv prstcleval breqd ) ADBJKEFABCDGHILM $.
    $}

    ${
      prstcoc.oc $e |- ( ph -> ._|_ = ( oc ` K ) ) $.
      $( Orthocomplementation is unchanged.  (Contributed by Zhi Wang,
         20-Sep-2024.)  (Proof shortened by AV, 12-Nov-2024.) $)
      prstcocval $p |- ( ph -> ._|_ = ( oc ` C ) ) $=
        ( coc cfv ocid cnx cco chom slotsdifocndx simpli simpri prstcnid eqtrd
        wne ) ADCHIBHIGABHCEFJKHIZKLISZTKMISZNOUAUBNPQR $.

      $( Orthocomplementation is unchanged.  (Contributed by Zhi Wang,
         20-Sep-2024.) $)
      prstcoc $p |- ( ph -> ( ._|_ ` X ) = ( ( oc ` C ) ` X ) ) $=
        ( coc cfv prstcocval fveq1d ) AEDBIJABCDFGHKL $.
    $}

    ${
      prstchomval.l $e |- ( ph -> .<_ = ( le ` C ) ) $.
      $( Hom-sets of the constructed category which depend on an arbitrary
         definition.  (Contributed by Zhi Wang, 20-Sep-2024.)
         (New usage is discouraged.) $)
      prstchomval $p |- ( ph ->
              ( .<_ X. { 1o } ) = ( Hom ` C ) ) $=
        ( chom cfv cnx cple c1o csn cxp cop homid wne cproset wcel cvv csts cbs
        co cco slotsbhcdif simp3i prstcnidlem wceq fvex snex xpex sylancl eqidd
        setsid prstcleval eqtr4d xpeq1d 3eqtr2rd ) ABHICJHIZCKIZLMZNZOUAUCHIZVB
        DVANABHCEFPJUBIZUSQVDJUDIZQUSVEQUEUFUGACRSVBTSVBVCUHFUTVACKUILUJUKRVBHT
        CPUNULAUTDVAAUTBKIDABCUTEFAUTUMUOGUPUQUR $.
    $}

    $( The category is a preordered set.  (Contributed by Zhi Wang,
       20-Sep-2024.) $)
    prstcprs $p |- ( ph -> C e. Proset ) $=
      ( vx vy vz cproset wcel cv cple cfv wbr wa wral cvv eqidd cprstc isprsd
      wi cbs prstcbas prstcleval fvex eqeltrdi bitr4d mpbird ) ABIJZCIJZEAUIFKZ
      UKCLMZNUKGKZULNUMHKZULNOUKUNULNUAOHCUBMZPGUOPFUOPUJAFGHUOBULQAUOBCDEAUORZ
      UCABCULDEAULRZUDABCSMQDCSUEUFTAFGHUOCULIUPUQETUGUH $.

    $( The preordered set is equipped with a thin category.  (Contributed by
       Zhi Wang, 20-Sep-2024.) $)
    prstcthin $p |- ( ph -> C e. ThinCat ) $=
      ( vy cthinc wcel ccid cfv c0 wceq cple eqidd cnx cop csts co cco cvv cmpt
      cbs prstchomval chom c1o csn cxp ovex ccoid setsid mp2an prstcval eqtr4id
      0ex fveq2d prstcprs prsthinc simpld ) ABGHBIJFBUBJZKUALAFUSBBMJZAUSNABCUT
      DEAUTNZUCAKCOUDJCMJUEUFUGPZQRZOSJKPQRZSJZBSJVCTHKTHKVELCVBQUHUNTKSTVCUIUJ
      UKABVDSABCDEULUOUMVAABCDEUPUQUR $.

    ${
      prstchom.l $e |- ( ph -> .<_ = ( le ` C ) ) $.
      prstchom.e $e |- ( ph -> H = ( Hom ` C ) ) $.
      ${
        prstchom.x $e |- ( ph -> X e. ( Base ` C ) ) $.
        prstchom.y $e |- ( ph -> Y e. ( Base ` C ) ) $.
        $( Hom-sets of the constructed category are dependent on the preorder.

           Note that prstchom.x and prstchom.y are redundant here due to our
           definition of ` ProsetToCat ` .  However, this should not be assumed
           as it is definition-dependent.  Therefore, the two hypotheses are
           added for explicitness.  (Contributed by Zhi Wang, 20-Sep-2024.) $)
        prstchom $p |- ( ph -> ( X .<_ Y <-> ( X H Y ) =/= (/) ) ) $=
          ( cvv c1o chom cfv csn cxp a1i prstchomval wcel 1oex wne ovconstbrn0d
          eqtr4d c0 1n0 ) AFGECNOACBPQEORSKABDEHIJUAUFONUBAUCTOUGUDAUHTUE $.

        $( Hom-sets of the constructed category are dependent on the preorder.

           Note that prstchom.x and prstchom.y are redundant here due to our
           definition of ` ProsetToCat ` ( see ~ prstchom2ALT ).  However, this
           should not be assumed as it is definition-dependent.  Therefore, the
           two hypotheses are added for explicitness.  (Contributed by Zhi
           Wang, 21-Sep-2024.) $)
        prstchom2 $p |- ( ph -> ( X .<_ Y <-> E! f f e. ( X H Y ) ) ) $=
          ( wbr co c0 wne cv wcel weu prstchom prstcthin eqidd thincn0eu bitrd
          cbs cfv ) AGHFOGHDPZQRCSUITCUAABDEFGHIJKLMNUBABUGUHZBCDGHABEIJUCMNAUJ
          UDLUEUF $.
      $}

      $( Hom-sets of the constructed category are dependent on the preorder.
         This proof depends on the definition ~ df-prstc .  See ~ prstchom2 for
         a version that does not depend on the definition.  (Contributed by Zhi
         Wang, 20-Sep-2024.)  (Proof modification is discouraged.)
         (New usage is discouraged.) $)
      prstchom2ALT $p |- ( ph -> ( X .<_ Y <-> E! f f e. ( X H Y ) ) ) $=
        ( wbr cv wcel c1o cvv a1i c0 wne weu cen wceq ovex chom cfv prstchomval
        co wa csn cxp eqtr4d 1n0 ovconstbrd biimpa eqeng mpsyl euen1b sylib wex
        1oex euex n0 sylibr ovconstbrn0d biimpar sylan2 impbida ) AGHFMZCNGHDUH
        ZOZCUAZAVIUIZVJPUBMZVLVJQOVMVJPUCZVNGHDUDAVIVOAGHFDQPADBUEUFFPUJUKLABEF
        IJKUGULZPQOAVARZPSTAUMRZUNUOVJPQUPUQCVJURUSVLAVJSTZVIVLVKCUTVSVKCVBCVJV
        CVDAVIVSAGHFDQPVPVQVRVEVFVGVH $.
    $}

    oduoppcbas.d $e |- ( ph -> D = ( ProsetToCat ` ( ODual ` K ) ) ) $.
    oduoppcbas.o $e |- O = ( oppCat ` C ) $.
    $( The dual of a preordered set and the opposite category have the same set
       of objects.  (Contributed by Zhi Wang, 22-Sep-2025.) $)
    oduoppcbas $p |- ( ph -> ( Base ` D ) = ( Base ` O ) ) $=
      ( cbs cfv codu cproset wcel eqid oduprs syl wceq odubas prstcbas oppcbas
      a1i eqcomd eqtrdi ) ACJKZBJKZEJKAUEBDFGADJKZUEAUGCDLKZHADMNUHMNGUHDUHOZPQ
      UGUHJKRAUGUHDUIUGOSUBTUCTUFBEIUFOUAUD $.

    ${
      $d C x y $.  $d D x y $.  $d K x y $.  $d O x y $.  $d U x y $.
      $d V x y $.  $d ph x y $.
      oduoppcciso.u $e |- ( ph -> U e. V ) $.
      oduoppcciso.d $e |- ( ph -> D e. U ) $.
      oduoppcciso.o $e |- ( ph -> O e. U ) $.
      $( The dual of a preordered set and the opposite category are
         category-isomorphic.  Example 3.6(1) of [Adamek] p. 25.  (Contributed
         by Zhi Wang, 22-Sep-2025.) $)
      oduoppcciso $p |- ( ph -> D ( ~=c ` ( CatCat ` U ) ) O ) $=
        ( cfv eqid wcel co c0 wceq vx vy ccatc cbs cid cres chom cproset oduprs
        codu prstcthin cthinc oppcthin wf1o f1oi oduoppcbas f1oeq3d mpbii cv wa
        syl cple wbr wne wb oduleg adantl cprstc adantr eqidd prstcleval simprl
        simprr prstchom oppcbas eqtr4di eleqtrd 3bitr3d fvresi ad2antrl oveq12d
        necon4bid ad2antll oppchom eqtrdi eqeq1d bitr4d thinccisod ) AUAUBDUCOZ
        CUDOZFUDOZDUEWJUFZCUGOZFUGOZGCFWIPWJPWKPWMPWNPLMNACEUJOZJAEUHQZWOUHQZIW
        OEWOPZUIZVAUKABULQFULQABEHIUKBFKUMVAAWJWJWLUNWJWKWLUNWJUOAWJWKWJWLABCEF
        HIJKUPZUQURAUAUSZWJQZUBUSZWJQZUTZUTZXAXCWMRZSTXCXABUGOZRZSTXAWLOZXCWLOZ
        WNRZSTXFXGSXISXFXAXCWOVBOZVCZXCXAEVBOZVCZXGSVDXISVDXEXNXPVEAXAXCWOXMXOE
        WJWJWRXOPXMPVFVGXFCWMWOXMXAXCACWOVHOTXEJVIZXFWPWQAWPXEIVIZWSVAZXFCWOXMX
        QXSXFXMVJVKXFWMVJAXBXDVLZAXBXDVMZVNXFBXHEXOXCXAABEVHOTXEHVIZXRXFBEXOYBX
        RXFXOVJVKXFXHVJXFXCWJBUDOZYAAWJYCTXEAWJWKYCWTYCBFKYCPVOVPVIZVQXFXAWJYCX
        TYDVQVNVRWBXFXLXISXFXLXAXCWNRXIXFXJXAXKXCWNXBXJXATAXDWJXAVSVTXDXKXCTAXB
        WJXCVSWCWABXHFXAXCXHPKWDWEWFWGWH $.
    $}

$(
    The following cannot be proved without using discouraged theorems such as
    ~ prstchomval .
    @( The dual of a preordered set and the opposite category have the same set
       of objects, morphisms, and compositions.  Example 3.6(1) of [Adamek]
       p. 25.  (Contributed by Zhi Wang, XX-Sep-2025.) @)
    oduoppc @p |- ( ph -> ( ( Homf ` D ) = ( Homf ` O )
                         /\ ( comf ` D ) = ( comf ` O ) ) ) @=
      (  ) ? @.
$)
  $}

$(
    The following cannot be proved without using discouraged theorems such as
    ~ prstchomval .
  @( The correspondence between order dual and opposite category.  Example
     3.6(1) of [Adamek] p. 25.  (Contributed by Zhi Wang, XX-Sep-2025.) @)
  oduoppccom @p |- ( ProsetToCat o. ( ODual |` Proset ) )
                   = ( ODual o. ( oppCat o. ProsetToCat ) ) @=
    (  ) ? @.
$)

  ${
    $d B x y $.  $d C x y $.  $d ph x y $.
    postc.c $e |- ( ph -> C = ( ProsetToCat ` K ) ) $.
    postc.k $e |- ( ph -> K e. Proset ) $.
    ${
      $d K x y $.
      $( The converted category is a poset iff the original proset is a poset.
         (Contributed by Zhi Wang, 26-Sep-2024.) $)
      postcpos $p |- ( ph -> ( K e. Poset <-> C e. Poset ) ) $=
        ( vx vy cbs cfv cproset prstcprs eqidd prstcbas cv cple wb wcel prstcle
        wbr wa adantr pospropd ) AFGCHIZCBJJEABCDEKAUCLZAUCBCDEUDMAFNZGNZCOIZSU
        EUFBOISPUEUCQUFUCQTABCUGUEUFDEAUGLRUAUB $.

      $( Alternate proof of ~ postcpos .  (Contributed by Zhi Wang,
         25-Sep-2024.)  (Proof modification is discouraged.)
         (New usage is discouraged.) $)
      postcposALT $p |- ( ph -> ( K e. Poset <-> C e. Poset ) ) $=
        ( vx vy cv cple cfv wbr wa wi cbs wral cpo wcel eqidd prstcle eqid baib
        weq prstcbas anbi12d imbi1d raleqbidvv cproset ispos2 prstcprs 3bitr4d
        wb syl ) AFHZGHZCIJZKZUNUMUOKZLZFGUBZMZGCNJZOZFVAOZUMUNBIJZKZUNUMVDKZLZ
        USMZGBNJZOZFVIOZCPQZBPQZAVBVJFVAVIAVABCDEAVARUCZAUTVHGVAVIVNAURVGUSAUPV
        EUQVFABCUOUMUNDEAUORZSABCUOUNUMDEVOSUDUEUFUFACUGQZVLVCUKEVLVPVCFGVACUOV
        ATUOTUHUAULABUGQZVMVKUKABCDEUIVMVQVKFGVIBVDVITVDTUHUAULUJ $.
    $}

    postc.b $e |- B = ( Base ` C ) $.
    $( The converted category is a poset iff no distinct objects are
       isomorphic.  (Contributed by Zhi Wang, 25-Sep-2024.) $)
    postc $p |- ( ph -> ( C e. Poset <-> A. x e. B A. y e. B
                                   ( x ( ~=c ` C ) y -> x = y ) ) ) $=
      ( wcel cv cfv wbr wa wceq wi wral cproset eqid co cpo cple ccic wb ispos2
      prstcprs baib syl chom wne cprstc adantr prstcthin simprl simprr thinccic
      c0 eqidd cbs eleqtrdi prstchom anbi12d bitr4d imbi1d 2ralbidva ) AEUAJZBK
      ZCKZEUBLZMZVHVGVIMZNZVGVHOZPZCDQBDQZVGVHEUCLMZVMPZCDQBDQAERJZVFVOUDAEFGHU
      FVFVRVOBCDEVIIVISUEUGUHAVQVNBCDDAVGDJZVHDJZNZNZVPVLVMWBVPVGVHEUILZTUQUJZV
      HVGWCTUQUJZNVLWBDEWCVGVHWBEFAEFUKLOWAGULZAFRJWAHULZUMIAVSVTUNZAVSVTUOZWCS
      UPWBVJWDVKWEWBEWCFVIVGVHWFWGWBVIURZWBWCURZWBVGDEUSLZWHIUTZWBVHDWLWIIUTZVA
      WBEWCFVIVHVGWFWGWJWKWNWMVAVBVCVDVEVC $.
  $}

  ${
    $d B b x $.
    $( A singlegon is an element of the class of singlegons.  The converse
       ( ~ basrestermcfolem ) also holds.  This is trivial if ` B ` is ` b `
       ( ~ abid ).  (Contributed by Zhi Wang, 20-Oct-2025.) $)
    discsntermlem $p |- ( E. x B = { x } -> B e. { b | E. x b = { x } } ) $=
      ( cv csn wceq wex cab wcel cvv wb vsnex eleq1 mpbiri exlimiv eqeq1 exbidv
      elabg syl ibir ) BADEZFZAGZBCDZUAFZAGZCHIZUCBJIZUGUCKUBUHAUBUHUAJIALBUAJM
      NOUFUCCBJUDBFUEUBAUDBUAPQRST $.

    $( An element of the class of singlegons is a singlegon.  The converse
       ( ~ discsntermlem ) also holds.  This is trivial if ` B ` is ` b `
       ( ~ abid ).  (Contributed by Zhi Wang, 20-Oct-2025.) $)
    basrestermcfolem $p |- ( B e. { b | E. x b = { x } } -> E. x B = { x } ) $=
      ( cv csn wceq wex cab wcel eqeq1 exbidv elabg ibi ) BCDZADEZFZAGZCHZIBOFZ
      AGZQTCBRNBFPSANBOJKLM $.
  $}

  ${
    discthin.k $e |- K = { <. ( Base ` ndx ) , B >.
                         , <. ( le ` ndx ) , ( _I |` B ) >. } $.
    discthin.c $e |- C = ( ProsetToCat ` K ) $.
    $( A discrete category (a category whose only morphisms are the identity
       morphisms) can be constructed for any base set.  (Contributed by Zhi
       Wang, 20-Oct-2025.) $)
    discbas $p |- ( B e. V -> B = ( Base ` C ) ) $=
      ( wcel cprstc cfv wceq a1i cpo cproset resipos posprs resiposbas prstcbas
      syl ) ADGZABCBCHIJSFKSCLGCMGACDENCORACDEPQ $.

    $( A discrete category (a category whose only morphisms are the identity
       morphisms) is thin.  (Contributed by Zhi Wang, 20-Oct-2025.) $)
    discthin $p |- ( B e. V -> C e. ThinCat ) $=
      ( wcel cprstc cfv wceq a1i cpo cproset resipos posprs syl prstcthin ) ADG
      ZBCBCHIJRFKRCLGCMGACDENCOPQ $.

    $d B b x $.  $d C b x $.  $d K b $.
    $( A discrete category (a category whose only morphisms are the identity
       morphisms) with a singlegon base is terminal.  Corollary of example
       3.3(4)(c) of [Adamek] p. 24 and example 3.26(1) of [Adamek] p. 33.
       (Contributed by Zhi Wang, 20-Oct-2025.) $)
    discsnterm $p |- ( E. x B = { x } -> C e. TermCat ) $=
      ( vb cv csn wceq wex cthinc cbs cfv ctermc cab discsntermlem discthin cvv
      wcel syl wb elex discbas eqeq1d exbidv 3syl ibi eqid istermc sylanbrc ) B
      AHIZJZAKZCLTZCMNZULJZAKZCOTUNBGHULJAKGPZTZUOABGQZBCDUSEFRUAUNURUNUTBSTZUN
      URUBVABUSUCVBUMUQAVBBUPULBCDSEFUDUEUFUGUHAUPCUPUIUJUK $.
  $}

  ${
    $d a b c x $.
    $( The base function restricted to the class of terminal categories maps
       the class of terminal categories onto the class of singletons.
       (Contributed by Zhi Wang, 20-Oct-2025.) $)
    basrestermcfo $p |- ( Base |` TermCat )
                        : TermCat -onto-> { b | E. x b = { x } } $=
      ( vc va ctermc cbs cnx cfv cv cop cple cid cres cpr cprstc wceq wcel eqid
      wex syl csn id termcbas discsntermlem basrestermcfolem discsnterm discbas
      cab basfn slotresfo ) ECFGFHDIZJGKHLUKMJNZOHZBIAIUAZPASBUHZDUICIZEQZUPFHZ
      UNPASURUOQUQAURUPUQUBURRUCAURBUDTUKUOQUKUNPASUMEQAUKBUEAUKUMULULRZUMRZUFT
      UKUMULUOUSUTUGUJ $.

    $( The class of all terminal categories is a proper class.  Therefore both
       the class of all thin categories and the class of all categories are
       proper classes.  Note that ~ snnex is equivalent to ` sngl _V e/ _V ` .
       (Contributed by Zhi Wang, 20-Oct-2025.) $)
    termcnex $p |- TermCat e/ _V $=
      ( vb vx ctermc cv csn wceq wex cab cbs cres snnex basrestermcfo fonex ) C
      ADBDEFBGAHICJABKBALM $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Monoids as categories
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $c MndToCat $.

  $( Class function defining monoids as categories. $)
  cmndtc $a class MndToCat $.

  ${
    $d B x y $.  $d M m x $.  $d X x y $.  $d Y x y $.  $d m ph $.
    $( Definition of the function converting a monoid to a category.  Example
       3.3(4.e) of [Adamek] p. 24.

       The definition of the base set is arbitrary.  The whole extensible
       structure becomes the object here (see ~ mndtcbasval ), instead of just
       the base set, as is the case in Example 3.3(4.e) of [Adamek] p. 24.

       The resulting category is defined entirely, up to isomorphism, by
       ~ mndtcbaseu , ~ mndtchom , ~ mndtcco .  Use those instead.

       See example 3.26(3) of [Adamek] p. 33 for more on isomorphism.

       "MndToCat" was taken instead of "MndCat" because the latter might mean
       the category of monoids.  (Contributed by Zhi Wang, 22-Sep-2024.)
       (New usage is discouraged.) $)
    df-mndtc $a |- MndToCat = ( m e. Mnd |-> { <. ( Base ` ndx ) , { m } >. ,
          <. ( Hom ` ndx ) , { <. m , m , ( Base ` m ) >. } >. ,
          <. ( comp ` ndx ) , { <. <. m , m , m >. , ( +g ` m ) >. } >. } ) $.

    mndtcbaseu.c $e |- ( ph -> C = ( MndToCat ` M ) ) $.
    mndtcbaseu.m $e |- ( ph -> M e. Mnd ) $.
    $( Value of the category built from a monoid.  (Contributed by Zhi Wang,
       22-Sep-2024.)  (New usage is discouraged.) $)
    mndtcval $p |- ( ph -> C = { <. ( Base ` ndx ) , { M } >. ,
          <. ( Hom ` ndx ) , { <. M , M , ( Base ` M ) >. } >. ,
          <. ( comp ` ndx ) , { <. <. M , M , M >. , ( +g ` M ) >. } >. } ) $=
      ( vm cmndtc cfv cnx cbs csn cop cotp cplusg ctp cmnd wceq opeq2d oteq123d
      fveq2 chom cco wcel cv sneq id sneqd opeq12d tpeq123d df-mndtc tpex fvmpt
      syl eqtrd ) ABCGHZIJHZCKZLZIUAHZCCCJHZMZKZLZIUBHZCCCMZCNHZLZKZLZOZDACPUCU
      OVJQEFCUPFUDZKZLZUSVKVKVKJHZMZKZLZVDVKVKVKMZVKNHZLZKZLZOVJPGVKCQZVMURVQVC
      WBVIWCVLUQUPVKCUERWCVPVBUSWCVOVAWCVKCVKCVNUTWCUFZWDVKCJTSUGRWCWAVHVDWCVTV
      GWCVRVEVSVFWCVKCVKCVKCWDWDWDSVKCNTUHUGRUIFUJURVCVIUKULUMUN $.

    mndtcbaseu.b $e |- ( ph -> B = ( Base ` C ) ) $.
    $( The base set of the category built from a monoid.  (Contributed by Zhi
       Wang, 22-Sep-2024.)  (New usage is discouraged.) $)
    mndtcbasval $p |- ( ph -> B = { M } ) $=
      ( cbs cfv cnx csn cop chom cotp cco cplusg ctp mndtcval cvv c1 fveq2d cdc
      wcel wceq snex c5 catstr baseid snsstp1 strfv mp1i 3eqtr4d ) ACHIJHIDKZLZ
      JMIDDDHINKZLZJOIDDDNDPILKZLZQZHIZBUMACUSHACDEFRUAGUMSUCUMUTUDADUEUMUSHSTT
      UFUBLUQUMUOUGUHUNUPURUIUJUKUL $.

    $( The category built from a monoid contains precisely one object.
       (Contributed by Zhi Wang, 22-Sep-2024.) $)
    mndtcbaseu $p |- ( ph -> E! x x e. B ) $=
      ( cv csn wceq wex wcel weu cmnd mndtcbasval sneq eqeq2d spcedv eusn
      sylibr ) ACBIZJZKZBLUBCMBNAUDCEJZKBOEGACDEFGHPUBEKUCUECUBEQRSBCTUA $.

    mndtchom.x $e |- ( ph -> X e. B ) $.
    $( Lemma for ~ mndtchom and ~ mndtcco .  (Contributed by Zhi Wang,
       22-Sep-2024.)  (New usage is discouraged.) $)
    mndtcob $p |- ( ph -> X = M ) $=
      ( csn wcel wceq mndtcbasval eleqtrd wb elsng syl mpbid ) AEDJZKZEDLZAEBSI
      ABCDFGHMNAEBKTUAOIEDBPQR $.

    mndtchom.y $e |- ( ph -> Y e. B ) $.
    $( Two objects in a category built from a monoid are identical.
       (Contributed by Zhi Wang, 24-Sep-2024.) $)
    mndtcobeq $p |- ( ph -> X = Y ) $=
      ( vx vy cv wceq wral wcel weu wmo mndtcbaseu eumo moel biimpi 3syl eqeq12
      wi rspc2gv syl2anc mpd ) ALNZMNZOZMBPLBPZEFOZAUJBQZLRUOLSZUMALBCDGHITUOLU
      AUPUMLMBUBUCUDAEBQFBQUMUNUFJKULUNLMEFBBUJEUKFUEUGUHUI $.

    ${
      mndtchom.h $e |- ( ph -> H = ( Hom ` C ) ) $.
      $( The only hom-set of the category built from a monoid is the base set
         of the monoid.  (Contributed by Zhi Wang, 22-Sep-2024.)  (Proof
         shortened by Zhi Wang, 22-Oct-2025.) $)
      mndtchom $p |- ( ph -> ( X H Y ) = ( Base ` M ) ) $=
        ( co cbs cfv csn chom cnx cop cotp cco cplusg ctp c1 c5 mndtcval catstr
        cvv cdc homid snsstp2 wcel snex eqid strfv3 eqtrd mndtcob oveq123d fvex
        a1i ovsn2 eqtrdi ) AFGDNEEEEEOPZUAZQZNVDAFEGEDVFADCRPZVFMAVGVFSOPEQZTZS
        RPVFTZSUBPEEEUAEUCPTQZTZUDCRUIUEUEUFUJTACEHIUGVKVHVFUHUKVIVJVLULVFUIUMA
        VEUNVAVGUOUPUQABCEFHIJKURABCEGHIJLURUSEEVDEOUTVBVC $.
    $}

    mndtcco.z $e |- ( ph -> Z e. B ) $.
    mndtcco.o $e |- ( ph -> .x. = ( comp ` C ) ) $.
    $( The composition of the category built from a monoid is the monoid
       operation.  (Contributed by Zhi Wang, 22-Sep-2024.) $)
    mndtcco $p |- ( ph -> ( <. X , Y >. .x. Z ) = ( +g ` M ) ) $=
      ( cop cfv csn cco cnx co cotp cplusg cbs chom ctp cvv cdc mndtcval catstr
      c1 ccoid snsstp3 wcel snex a1i eqid strfv3 eqtrd mndtcob opeq12d oveq123d
      c5 df-ov df-ot fveq2i otex fvex fvsn 3eqtr2i eqtrdi ) AFGPZHDUAEEPZEEEEUB
      ZEUCQZPZRZUAZVOAVLVMHEDVQADCSQZVQOAVSVQTUDQERZPZTUEQEEEUDQUBRZPZTSQVQPZUF
      CSUGUKUKVCUHPACEIJUIVQVTWBUJULWAWCWDUMVQUGUNAVPUOUPVSUQURUSAFEGEABCEFIJKL
      UTABCEGIJKMUTVAABCEHIJKNUTVBVRVMEPZVQQVNVQQVOVMEVQVDVNWEVQEEEVEVFVNVOEEEV
      GEUCVHVIVJVK $.

    mndtcco2.o2 $e |- ( ph -> .o. = ( <. X , Y >. .x. Z ) ) $.
    $( The composition of the category built from a monoid is the monoid
       operation.  (Contributed by Zhi Wang, 22-Sep-2024.) $)
    mndtcco2 $p |- ( ph -> ( G .o. F ) = ( G ( +g ` M ) F ) ) $=
      ( cplusg cfv cop co mndtcco eqtrd oveqd ) AJGTUAZFEAJHIUBKDUCUGSABCDGHIKL
      MNOPQRUDUEUF $.
  $}

  ${
    $d C f g k w x y z $.  $d M f g k w x z $.  $d X f g k w x y z $.
    $d f g k ph w x y z $.
    mndtccat.c $e |- ( ph -> C = ( MndToCat ` M ) ) $.
    mndtccat.m $e |- ( ph -> M e. Mnd ) $.
    $( Lemma for ~ mndtccat and ~ mndtcid .  (Contributed by Zhi Wang,
       22-Sep-2024.) $)
    mndtccatid $p |- ( ph -> ( C e. Cat /\ ( Id ` C ) =
                ( y e. ( Base ` C ) |-> ( 0g ` M ) ) ) ) $=
      ( cv cfv wcel wa co eqidd eqid adantr wceq mndtchom mndtcco oveqd eleqtrd
      cop vx vz vw vf vg vk cbs chom w3a cco c0g cmndtc fvexd eqeltrd biid cmnd
      cvv mndidcl syl simpr cplusg simpr1l simpr1r simpr31 mndlid syl2anc eqtrd
      eleqtrrd simpr2l simpr32 mndrid syl3anc 3eltr4d simpr33 syl13anc oveq123d
      mndcl simpr2r mndass 3eqtr4d iscatd2 ) AUAGZCUGHZIZBGZWCIZJZUBGZWCIZUCGZW
      CIZJZUDGZWBWECUHHZKZIZUEGZWEWHWNKZIZUFGZWHWJWNKZIZUIZUIZUABUBUCWCCCUJHZDU
      KHZUDUEUFWNUQAWCLAWNLAXELACDULHZUQEADULUMUNXDUOAWFJZXFDUGHZWEWEWNKAXFXIIZ
      WFADUPIZXJFXIDXFXIMZXFMZURUSNXHWCCWNDWEWEACXGOZWFENAXKWFFNXHWCLAWFUTZXOXH
      WNLPVHAXDJZXFWMWBWETZWEXEKZKXFWMDVAHZKZWMXPXRXSXFWMXPWCCXEDWBWEWEAXNXDENZ
      AXKXDFNZXPWCLZWDWFWLXCAVBZWDWFWLXCAVCZYEXPXELZQRXPXKWMXIIZXTWMOYBXPWMWOXI
      WPWSXBWGWLAVDXPWCCWNDWBWEYAYBYCYDYEXPWNLZPSZXIXSDWMXFXLXSMZXMVEVFVGXPWQXF
      WEWETWHXEKZKWQXFXSKZWQXPYKXSWQXFXPWCCXEDWEWEWHYAYBYCYEYEWIWKWGXCAVIZYFQRX
      PXKWQXIIZYLWQOYBXPWQWRXIWPWSXBWGWLAVJXPWCCWNDWEWHYAYBYCYEYMYHPSZXIXSDWQXF
      XLYJXMVKVFVGXPWQWMXSKZXIWQWMXQWHXEKZKZWBWHWNKXPXKYNYGYPXIIYBYOYIXIXSDWQWM
      XLYJVQVLXPYQXSWQWMXPWCCXEDWBWEWHYAYBYCYDYEYMYFQRZXPWCCWNDWBWHYAYBYCYDYMYH
      PVMXPWTWQXSKZWMXSKZWTYPXSKZWTWQWEWHTWJXEKZKZWMXQWJXEKZKWTYRWBWHTWJXEKZKXP
      XKWTXIIYNYGUUAUUBOYBXPWTXAXIWPWSXBWGWLAVNXPWCCWNDWHWJYAYBYCYMWIWKWGXCAVRZ
      YHPSYOYIXIXSDWTWQWMXLYJVSVOXPUUDYTWMWMUUEXSXPWCCXEDWBWEWJYAYBYCYDYEUUGYFQ
      XPUUCXSWTWQXPWCCXEDWEWHWJYAYBYCYEYMUUGYFQRXPWMLVPXPWTWTYRYPUUFXSXPWCCXEDW
      BWHWJYAYBYCYDYMUUGYFQXPWTLYSVPVTWA $.

    $( The function value is a category.  (Contributed by Zhi Wang,
       22-Sep-2024.) $)
    mndtccat $p |- ( ph -> C e. Cat ) $=
      ( vy ccat wcel ccid cfv cbs c0g cmpt wceq mndtccatid simpld ) ABGHBIJFBKJ
      CLJMNAFBCDEOP $.

    ${
      mndtcid.b $e |- ( ph -> B = ( Base ` C ) ) $.
      mndtcid.x $e |- ( ph -> X e. B ) $.
      mndtcid.i $e |- ( ph -> .1. = ( Id ` C ) ) $.
      $( The identity morphism, or identity arrow, of the category built from a
         monoid is the identity element of the monoid.  (Contributed by Zhi
         Wang, 22-Sep-2024.) $)
      mndtcid $p |- ( ph -> ( .1. ` X ) = ( 0g ` M ) ) $=
        ( vx c0g cfv cbs cvv ccid cmpt ccat wceq wcel mndtccatid eqtrd cv eqidd
        simprd wa eleqtrd fvexd fvmptd ) ALFEMNZUKCONZDPADCQNZLULUKRZKACSUAUMUN
        TALCEGHUBUFUCALUDFTUGUKUEAFBULJIUHAEMUIUJ $.
    $}

    ${
      oppgoppchom.d $e |- ( ph -> D = ( MndToCat ` ( oppG ` M ) ) ) $.
      oppgoppchom.o $e |- O = ( oppCat ` C ) $.
      oppgoppchom.x $e |- ( ph -> X e. ( Base ` D ) ) $.
      oppgoppchom.y $e |- ( ph -> Y e. ( Base ` O ) ) $.
      ${
        oppgoppchom.h $e |- ( ph -> H = ( Hom ` D ) ) $.
        oppgoppchom.j $e |- ( ph -> J = ( Hom ` O ) ) $.
        $( The converted opposite monoid has the same hom-set as that of the
           opposite category.  Example 3.6(2) of [Adamek] p. 25.  (Contributed
           by Zhi Wang, 21-Sep-2025.) $)
        oppgoppchom $p |- ( ph -> ( X H X ) = ( Y J Y ) ) $=
          ( co cfv cbs chom coppg wceq eqid oppgbas a1i oppcbas eqcomi mndtchom
          eqidd cmnd wcel oppgmnd syl 3eqtr4rd oppchom eqtr4di oveqd eqtr4d ) A
          HHDRZIIGUASZRZIIERAUTIIBUASZRZVBAFTSZFUBSZTSZVDUTVEVGUCAVEFVFVFUDZVEU
          DUEUFAGTSZBVCFIIJKVIBTSZUCAVJVIVJBGMVJUDUGUHUFOOAVCUJUIACTSZCDVFHHLAF
          UKULVFUKULKFVFVHUMUNAVKUJNNPUIUOBVCGIIVCUDMUPUQAEVAIIQURUS $.
      $}

      ${
        oppgoppcco.o $e |- ( ph -> .x. = ( comp ` D ) ) $.
        oppgoppcco.x $e |- ( ph -> .xb = ( comp ` O ) ) $.
        $( The converted opposite monoid has the same composition as that of
           the opposite category.  Example 3.6(2) of [Adamek] p. 25.
           (Contributed by Zhi Wang, 22-Sep-2025.) $)
        oppgoppcco $p |- ( ph -> ( <. X , X >. .x. X ) =
                  ( <. Y , Y >. .xb Y ) ) $=
          ( co cfv eqid cop cco ctpos cplusg cbs wceq oppcbas a1i eqidd mndtcco
          eqcomi tposeqd oppccofval coppg cmnd wcel oppgmnd oppgplusfval eqtrdi
          syl 3eqtr4rd oveqd eqtr4d ) AHHUAHERZIIUAZIGUBSZRZVEIDRAVEIBUBSZRZUCF
          UDSZUCZVGVDAVIVJAGUESZBVHFIIIJKVLBUESZUFAVMVLVMBGMVMTUGUKZUHOOOAVHUIU
          JULAVLBVHGIIIVNVHTMOOOUMAVDFUNSZUDSZVKACUESZCEVOHHHLAFUOUPVOUOUPKFVOV
          OTZUQUTAVQUINNNPUJVJVPFVOVJTVRVPTURUSVAADVFVEIQVBVC $.
      $}

      $( The converted opposite monoid has the same identity morphism as that
         of the opposite category.  Example 3.6(2) of [Adamek] p. 25.
         (Contributed by Zhi Wang, 22-Sep-2025.) $)
      oppgoppcid $p |- ( ph -> ( ( Id ` D ) ` X ) = ( ( Id ` O ) ` Y ) ) $=
        ( c0g cfv ccid wceq eqid cbs wcel coppg oppgid a1i eqcomi ccat mndtccat
        oppcbas oppcid syl mndtcid cmnd oppgmnd eqidd 3eqtr4rd ) ADNOZDUAOZNOZG
        EPOZOFCPOZOUOUQQADUPUOUPRZUORUBUCAESOZBURDGHIVABSOZQAVBVAVBBEKVBRUGUDUC
        MABUETURBPOZQABDHIUFVCBEKVCRUHUIUJACSOZCUSUPFJADUKTUPUKTIDUPUTULUIAVDUM
        LAUSUMUJUN $.
    $}

$(
    The following is not true yet because base set of converted category
    depends on the original monoid in the current definition.
    @{
      oppgtoppc.o @e |- O = ( oppG ` M ) @.
      oppgtoppc.d @e |- ( ph -> D = ( MndToCat ` O ) ) @.
      @( An opposite monoid is converted to an opposite category.  Example
         3.6(2) of [Adamek] p. 25.  (Contributed by Zhi Wang, XX-Sep-2025.) @)
      oppgtoppc @p |- ( ph -> D = ( oppCat ` C ) ) @=
        (  ) ? @.
    @}
$)
  $}

  ${
    $d B f g h z $.  $d C f g h z $.  $d E f g h z $.  $d G f g h z $.
    $d H f g h z $.  $d M f g h z $.  $d X f g h z $.  $d Y f g h z $.
    $d f g h ph z $.
    grptcmon.c $e |- ( ph -> C = ( MndToCat ` G ) ) $.
    grptcmon.g $e |- ( ph -> G e. Grp ) $.
    grptcmon.b $e |- ( ph -> B = ( Base ` C ) ) $.
    grptcmon.x $e |- ( ph -> X e. B ) $.
    grptcmon.y $e |- ( ph -> Y e. B ) $.
    grptcmon.h $e |- ( ph -> H = ( Hom ` C ) ) $.
    ${
      grptcmon.m $e |- ( ph -> M = ( Mono ` C ) ) $.
      $( All morphisms in a category converted from a group are monomorphisms.
         (Contributed by Zhi Wang, 23-Sep-2024.) $)
      grptcmon $p |- ( ph -> ( X M Y ) = ( X H Y ) ) $=
        ( cfv co wcel eqid ad2antrr vf vg vz vh cmon chom cop cco wceq wral cbs
        cv wi grpmndd mndtccat eleqtrd ismon2 w3a cplusg cmndtc simpr1 eleqtrrd
        wa cmnd eqidd mndtcco2 eqeq12d wb simpr2 mndtchom simpr3 simplr grplcan
        cgrp syl13anc bitrd biimpd ralrimivvva mpbiran3d eqrdv oveqd 3eqtr4d )
        AGHCUEPZQZGHCUFPZQZGHFQGHEQAUAWDWFAUAULZWDRWGWFRZWGUBULZUCULZGUGHCUHPZQ
        ZQZWGUDULZWLQZUIZWIWNUIZUMZUDWJGWEQZUJUBWSUJUCCUKPZUJAUCWTCWKUBUDWGWEWC
        GHWTSWESWKSWCSACDIADJUNZUOAGBWTLKUPAHBWTMKUPUQAWHVCZWRUCUBUDWTWSWSXBWJW
        TRZWIWSRZWNWSRZURZVCZWPWQXGWPWGWIDUSPZQZWGWNXHQZUIZWQXGWMXIWOXJXGBCWKWI
        WGDWJGWLHACDUTPUIWHXFITZADVDRWHXFXATZABWTUIWHXFKTZXGWJWTBXBXCXDXEVAXNVB
        ZAGBRWHXFLTZAHBRWHXFMTZXGWKVEZXGWLVEZVFXGBCWKWNWGDWJGWLHXLXMXNXOXPXQXRX
        SVFVGXGDVNRZWIDUKPZRWNYARWGYARXKWQVHAXTWHXFJTXGWIWSYAXBXCXDXEVIXGBCWEDW
        JGXLXMXNXOXPXGWEVEZVJZUPXGWNWSYAXBXCXDXEVKYCUPXGWGWFYAAWHXFVLXGBCWEDGHX
        LXMXNXPXQYBVJUPYAXHDWIWNWGYASXHSVMVOVPVQVRVSVTAFWCGHOWAAEWEGHNWAWB $.
    $}

    ${
      grptcepi.e $e |- ( ph -> E = ( Epi ` C ) ) $.
      $( All morphisms in a category converted from a group are epimorphisms.
         (Contributed by Zhi Wang, 23-Sep-2024.) $)
      grptcepi $p |- ( ph -> ( X E Y ) = ( X H Y ) ) $=
        ( cfv co wcel eqid ad2antrr vf vg vz vh cepi chom cop cco wceq wral cbs
        cv wi grpmndd mndtccat eleqtrd isepi2 w3a cplusg cmndtc simpr1 eleqtrrd
        wa cmnd eqidd mndtcco2 eqeq12d wb simpr2 mndtchom simpr3 simplr grprcan
        cgrp syl13anc bitrd biimpd ralrimivvva mpbiran3d eqrdv oveqd 3eqtr4d )
        AGHCUEPZQZGHCUFPZQZGHDQGHFQAUAWDWFAUAULZWDRWGWFRZUBULZWGGHUGUCULZCUHPZQ
        ZQZUDULZWGWLQZUIZWIWNUIZUMZUDHWJWEQZUJUBWSUJUCCUKPZUJAUCWTCWKUBUDWCWGWE
        GHWTSWESWKSWCSACEIAEJUNZUOAGBWTLKUPAHBWTMKUPUQAWHVCZWRUCUBUDWTWSWSXBWJW
        TRZWIWSRZWNWSRZURZVCZWPWQXGWPWIWGEUSPZQZWNWGXHQZUIZWQXGWMXIWOXJXGBCWKWG
        WIEGHWLWJACEUTPUIWHXFITZAEVDRWHXFXATZABWTUIWHXFKTZAGBRWHXFLTZAHBRWHXFMT
        ZXGWJWTBXBXCXDXEVAXNVBZXGWKVEZXGWLVEZVFXGBCWKWGWNEGHWLWJXLXMXNXOXPXQXRX
        SVFVGXGEVNRZWIEUKPZRWNYARWGYARXKWQVHAXTWHXFJTXGWIWSYAXBXCXDXEVIXGBCWEEH
        WJXLXMXNXPXQXGWEVEZVJZUPXGWNWSYAXBXCXDXEVKYCUPXGWGWFYAAWHXFVLXGBCWEEGHX
        LXMXNXOXPYBVJUPYAXHEWIWNWGYASXHSVMVOVPVQVRVSVTADWCGHOWAAFWEGHNWAWB $.
    $}
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Categories with at most one object and at most two morphisms
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    2arwcatlem1.x $e |- ( X H X ) = { .0. , .1. } $.
    $( Lemma for ~ 2arwcat .  (Contributed by Zhi Wang, 5-Nov-2025.) $)
    2arwcatlem1 $p |- ( ( ( ( x = X /\ y = X ) /\ ( z = X /\ w = X ) )
      /\ ( ( f = .0. \/ f = .1. ) /\ ( g = .0. \/ g = .1. )
        /\ ( k = .0. \/ k = .1. ) ) )
         <-> ( ( x e. { X } /\ y e. { X } ) /\ ( z e. { X } /\ w e. { X } )
        /\ ( f e. ( x H y ) /\ g e. ( y H z ) /\ k e. ( z H w ) ) ) ) $=
      ( cv wcel wa co w3a wceq wo velsn csn df-3an anbi12i anbi1i simpll simplr
      cpr oveq12d eqtrdi eleq2d simprl simprr 3anbi123d vex elpr bitrdi pm5.32i
      3anbi123i 3bitrri ) AMZJUAZNZBMZVANZOZCMZVANZDMZVANZOZFMZUTVCIPZNZGMZVCVF
      IPZNZHMZVFVHIPZNZQZQVEVJOZVTOUTJRZVCJRZOZVFJRZVHJRZOZOZVTOWHVKKRVKERSZVNK
      RVNERSZVQKRVQERSZQZOVEVJVTUBWAWHVTVEWDVJWGVBWBVDWCAJTBJTUCVGWEVIWFCJTDJTU
      CUCUDWHVTWLWHVTVKKEUGZNZVNWMNZVQWMNZQWLWHVMWNVPWOVSWPWHVLWMVKWHVLJJIPZWMW
      HUTJVCJIWBWCWGUEWBWCWGUFZUHLUIUJWHVOWMVNWHVOWQWMWHVCJVFJIWRWDWEWFUKZUHLUI
      UJWHVRWMVQWHVRWQWMWHVFJVHJIWSWDWEWFULUHLUIUJUMWNWIWOWJWPWKVKKEFUNUOVNKEGU
      NUOVQKEHUNUOURUPUQUS $.
  $}

  ${
    2arwcatlem2.a $e |- ( ph -> A = X ) $.
    2arwcatlem2.b $e |- ( ph -> B = Y ) $.
    2arwcatlem2.c $e |- ( ph -> C = Z ) $.
    2arwcatlem2.f $e |- ( ph -> ( F = .0. \/ F = .1. ) ) $.
    2arwcatlem2.1 $e |- ( ph -> ( .1. ( <. X , Y >. .x. Z ) .1. ) = .1. ) $.
    ${
      2arwcatlem2.0 $e |- ( ph -> ( .1. ( <. X , Y >. .x. Z ) .0. ) = .0. ) $.
      $( Lemma for ~ 2arwcat .  (Contributed by Zhi Wang, 5-Nov-2025.) $)
      2arwcatlem2 $p |- ( ph -> ( .1. ( <. A , B >. .x. C ) F ) = F ) $=
        ( cop co wceq opeq12d oveq12d oveqd adantr simpr 3eqtr4d mpjaodan eqtrd
        wa oveq2d ) AFGBCRZDESZSFGHIRZKESZSZGAULUNFGAUKUMDKEABHCILMUANUBUCAGJTZ
        UOGTGFTZAUPUIZFJUNSZJUOGAUSJTUPQUDURGJFUNAUPUEZUJUTUFAUQUIZFFUNSZFUOGAV
        BFTUQPUDVAGFFUNAUQUEZUJVCUFOUGUH $.
    $}

    2arwcatlem3.0 $e |- ( ph -> ( .0. ( <. X , Y >. .x. Z ) .1. ) = .0. ) $.
    $( Lemma for ~ 2arwcat .  (Contributed by Zhi Wang, 5-Nov-2025.) $)
    2arwcatlem3 $p |- ( ph -> ( F ( <. A , B >. .x. C ) .1. ) = F ) $=
      ( cop co wceq opeq12d oveq12d oveqd wa adantr simpr oveq1d mpjaodan eqtrd
      3eqtr4d ) AGFBCRZDESZSGFHIRZKESZSZGAULUNGFAUKUMDKEABHCILMUANUBUCAGJTZUOGT
      GFTZAUPUDZJFUNSZJUOGAUSJTUPQUEURGJFUNAUPUFZUGUTUJAUQUDZFFUNSZFUOGAVBFTUQP
      UEVAGFFUNAUQUFZUGVCUJOUHUI $.

    2arwcatlem4.0 $e |- ( ph -> ( .1. ( <. X , Y >. .x. Z ) .0. ) = .0. ) $.
    2arwcatlem4.00 $e |- ( ph -> ( .0. ( <. X , Y >. .x. Z ) .0. )
                           e. { .0. , .1. } ) $.
    2arwcatlem4.g $e |- ( ph -> ( G = .0. \/ G = .1. ) ) $.
    $( Lemma for ~ 2arwcat .  (Contributed by Zhi Wang, 5-Nov-2025.) $)
    2arwcatlem4 $p |- ( ph -> ( G ( <. A , B >. .x. C ) F ) e. { .0. , .1. } )
       $=
      ( cop co opeq12d oveq12d oveqd wceq wcel wa simpr simplr ad2antrr eqeltrd
      cpr eqtrd cvv ovex eqeltrrdi prid1g syl wo adantr mpjaodan prid2g ) AHGBC
      UBZDEUCZUCHGIJUBZLEUCZUCZKFUNZAVFVHHGAVEVGDLEABICJMNUDOUEUFAGKUGZVIVJUHZG
      FUGZAVKUIZHKUGZVLHFUGZVNVOUIZVIKKVHUCZVJVQHKGKVHVNVOUJAVKVOUKUEAVRVJUHVKV
      OTULUMVNVPUIZVIKVJVSVIFKVHUCZKVSHFGKVHVNVPUJAVKVPUKUEAVTKUGVKVPSULUOAKVJU
      HZVKVPAKUPUHWAAKVTUPSFKVHUQURKFUPUSUTZULUMAVOVPVAZVKUAVBVCAVMUIZVOVLVPWDV
      OUIZVIKVJWEVIKFVHUCZKWEHKGFVHWDVOUJAVMVOUKUEAWFKUGVMVORULUOAWAVMVOWBULUMW
      DVPUIZVIFVJWGVIFFVHUCZFWGHFGFVHWDVPUJAVMVPUKUEAWHFUGVMVPQULUOAFVJUHZVMVPA
      FUPUHWIAFWHUPQFFVHUQURKFUPVDUTULUMAWCVMUAVBVCPVCUM $.
  $}

  ${
    2arwcatlem5.1 $e |- ( ph -> ( .1. .x. .0. ) = .0. ) $.
    2arwcatlem5.2 $e |- ( ph -> ( .0. .x. .1. ) = .0. ) $.
    2arwcatlem5.3 $e |- ( ph -> ( .0. .x. .0. ) e. { .0. , .1. } ) $.
    $( Lemma for ~ 2arwcat .  (Contributed by Zhi Wang, 5-Nov-2025.) $)
    2arwcatlem5 $p |- ( ph -> ( ( .0. .x. .0. ) .x. .0. )
                              = ( .0. .x. ( .0. .x. .0. ) ) ) $=
      ( co wceq wa simpr oveq1d oveq2d eqtr4d adantr 3eqtr4d cpr wcel wo ovex
      elpr sylib mpjaodan ) ADDBHZDIZUDDBHZDUDBHZIUDCIZAUEJZUFUDUGUIUDDDBAUEKZL
      UIUDDDBUJMNAUHJZCDBHZDCBHZUFUGAULUMIUHAULDUMEFNOUKUDCDBAUHKZLUKUDCDBUNMPA
      UDDCQRUEUHSGUDDCDDBTUAUBUC $.
  $}

  ${
    $d .0. f g k w x z $.  $d .1. f g k w x z $.  $d .x. f g k w x y z $.
    $d C f g k w x y z $.  $d H f g k w x y z $.  $d X f g k w x y z $.
    $d f g k ph w x y z $.
    2arwcat.b $e |- ( ph -> { X } = ( Base ` C ) ) $.
    2arwcat.h $e |- ( ph -> H = ( Hom ` C ) ) $.
    2arwcat.x $e |- ( ph -> .x. = ( comp ` C ) ) $.
    2arwcat.1 $e |- ( X H X ) = { .0. , .1. } $.
    2arwcat.2 $e |- ( ph -> ( .1. ( <. X , X >. .x. X ) .1. ) = .1. ) $.
    2arwcat.3 $e |- ( ph -> ( .1. ( <. X , X >. .x. X ) .0. ) = .0. ) $.
    2arwcat.4 $e |- ( ph -> ( .0. ( <. X , X >. .x. X ) .1. ) = .0. ) $.
    2arwcat.5 $e |- ( ph -> ( .0. ( <. X , X >. .x. X ) .0. )
                                e. { .0. , .1. } ) $.
    $( The condition for a structure with at most one object and at most two
       morphisms being a category.  "2arwcat.2" to "2arwcat.5" are also
       necessary conditions if ` X ` , ` .0. ` , and ` .1. ` are all sets, due
       to ~ catlid , ~ catrid , and ~ catcocl .  (Contributed by Zhi Wang,
       5-Nov-2025.) $)
    2arwcat $p |- ( ph -> ( C e. Cat /\ ( Id ` C ) = ( y e. { X } |-> .1. ) ) )
    $=
      ( wceq wa co oveq12d vx vz vw vf vg vk cv wo w3a csn cvv cop chom cfv cpr
      wcel ovex eqeltrrdi prid2g syl eleqtrrdi df-ov fveq1d eleqtrd 2arwcatlem1
      eqtrid elfv2ex adantr velsn id eqtrdi sylbi adantl eleqtrrd simpld simprd
      simprll simprr1 2arwcatlem2 simprlr simprr2 2arwcatlem3 2arwcatlem4 simpr
      2arwcatlem5 ad4antr simplr ad2antrr 3eqtr4d eqidd opeq12d oveqd ad3antrrr
      eqeltrrd elpr sylib oveq1d eqtrd 3eqtr4rd mpjaodan oveq2d eqtr4d oveq123d
      simprr3 iscatd2 ) AUAUGZGQZBUGZGQZRZUBUGZGQZUCUGZGQZRZRZUDUGZHQZXQEQZUHZU
      EUGZHQZYAEQZUHZUFUGZHQZYEEQZUHZUIZRZUABUBUCGUJZCDEUDUEUFFUKIJKAEGGULZCUMU
      NZUNZUPCUKUPAEGGFSZYNAEHEUOZYOAEUKUPEYPUPZAEEEYLGDSZSZUKMEEYRUQURHEUKUSUT
      ZLVAAYOYLFUNYNGGFVBAYLFYMJVCVFVDECYLUMVGUTUABUBUCEUDUEUFFGHLVEAXHYKUPZREY
      PXHXHFSZAYQUUAYTVHUUAUUBYPQZAUUAXIUUCBGVIXIUUBYOYPXIXHGXHGFXIVJZUUDTLVKVL
      VMVNAYJRZXFXHXHDEXQGGHGUUEXGXIAXJXOYIVQZVOZUUEXGXIUUFVPZUUHXTYDYHXPAVRZAY
      SEQYJMVHZAEHYRSHQYJNVHZVSUUEXHXHXKDEYAGGHGUUHUUHUUEXLXNAXJXOYIVTZVOZXTYDY
      HXPAWAZUUJAHEYRSHQYJOVHZWBUUEYAXQXFXHULZXKDSZSZYPXFXKFSZUUEXFXHXKDEXQYAGG
      HGUUGUUHUUMUUIUUJUUOUUKAHHYRSZYPUPYJPVHZUUNWCZUUEUUSYOYPUUEXFGXKGFUUGUUMT
      LVKVNUUEYEYAYRSZXQYRSZYEYAXQYRSZYRSZYEYAXHXKULZXMDSZSZXQUUPXMDSZSYEUURXFX
      KULZXMDSZSUUEXRUVDUVFQZXSUUEXRRZYBUVMYCUVNYBRZYFUVMYGUVOYFRZUUTHYRSZHUUTY
      RSZUVDUVFAUVQUVRQYJXRYBYFAYREHNOPWEWFUVPUVCUUTXQHYRUVPYEHYAHYRUVOYFWDZUVN
      YBYFWGZTUVNXRYBYFUUEXRWDWHZTUVPYEHUVEUUTYRUVSUVPYAHXQHYRUVTUWATTWIUVOYGRZ
      EUVEYRSZUVEUVFUVDUUEUWCUVEQXRYBYGUUEGGGDEUVEGGHGUUEGWJZUWDUWDUUEUVEYPUPUV
      EHQUVEEQUHUUEUURUVEYPUUEUUQYRYAXQUUEUUPYLXKGDUUEXFGXHGUUGUUHWKZUUMTWLZUVB
      WNUVEHEYAXQYRUQWOWPUUJUUKVSWMUWBYEEUVEYRUVOYGWDZWQUWBUVCYAXQYRUWBUVCEYAYR
      SZYAUWBYEEYAYRUWGWQUUEUWHYAQXRYBYGUUEGGGDEYAGGHGUWDUWDUWDUUNUUJUUKVSWMWRW
      QWSUUEYHXRYBXTYDYHXPAXDZWHWTUVNYCRZUVDYEXQYRSUVFUWJUVCYEXQYRUWJUVCYEEYRSZ
      YEUWJYAEYEYRUVNYCWDZXAUUEUWKYEQXRYCUUEGGGDEYEGGHGUWDUWDUWDUWIUUJUUOWBWHWR
      WQUWJUVEXQYEYRUWJUVEEXQYRSZXQUWJYAEXQYRUWLWQUUEUWMXQQXRYCUUEGGGDEXQGGHGUW
      DUWDUWDUUIUUJUUKVSWHWRXAXBUUEYDXRUUNVHWTUUEXSRZUVCEYRSZUVCUVDUVFUUEUWOUVC
      QXSUUEGGGDEUVCGGHGUWDUWDUWDUUEUVCYPUPUVCHQUVCEQUHUUEGGGDEYAYEGGHGUWDUWDUW
      DUUNUUJUUOUUKUVAUWIWCUVCHEYEYAYRUQWOWPUUJUUOWBVHUWNXQEUVCYRUUEXSWDZXAUWNU
      VEYAYEYRUWNUVEYAEYRSZYAUWNXQEYAYRUWPXAUUEUWQYAQXSUUEGGGDEYAGGHGUWDUWDUWDU
      UNUUJUUOWBVHWRXAWIUUIWTUUEUVIUVCXQXQUVJYRUUEUUPYLXMGDUWEUUEXLXNUULVPZTUUE
      UVHYRYEYAUUEUVGYLXMGDUUEXHGXKGUUHUUMWKUWRTWLUUEXQWJXCUUEYEYEUURUVEUVLYRUU
      EUVKYLXMGDUUEXFGXKGUUGUUMWKUWRTUUEYEWJUWFXCWIXE $.
  $}

  ${
    $d .x. y $.  $d C y $.  $d F f g $.  $d F y $.  $d G f g $.  $d G y $.
    $d H f g $.  $d H y $.  $d V f g $.  $d V y $.  $d X y $.
    incat.c $e |- C = { <. ( Base ` ndx ) , { X } >. ,
                    <. ( Hom ` ndx ) , { <. X , X , H >. } >. ,
                    <. ( comp ` ndx ) , { <. <. X , X >. , X , .x. >. } >. } $.
    incat.h $e |- H = { F , G } $.
    incat.x $e |- .x. = ( f e. H , g e. H |-> ( f i^i g ) ) $.
    $( Constructing a category with at most one object and at most two
       morphisms.  If ` X ` is a set then ` C ` is the category ` A ` in
       Exercise 3G of [Adamek] p. 45.  (Contributed by Zhi Wang,
       5-Nov-2025.) $)
    incat $p |- ( ( F C_ G /\ G e. V )
               -> ( C e. Cat /\ ( Id ` C ) = ( y e. { X } |-> G ) ) ) $=
      ( wcel wa wceq a1i cvv cin ineq12 wss cop cotp csn snex catbas cathomfval
      cbs cfv chom cco catcofval co cpr prex eqeltri ovsn2 eqtri cv mpoex inidm
      cmpo eqtrdi adantl prid2g eleqtrrdi ovmpod sseqin2 birani sylan9eqr ssexg
      prid1g syl dfss2 eqeltrd 2arwcat ) FGUAZGINZOZABJJUBZJCUCZUDZGJJHUCZUDZJF
      JUDZBUHUIPVSWEBWBWDKJUEUFQWDBUJUIPVSWEBWBWDKWCUEUGQWBBUKUIPVSWEBWBWDKWAUE
      ULQJJWDUMHFGUNZJJHHWFRLFGUOUPZUQLURVSDEGGHHDUSZEUSZSZGVTJWBUMZHWKDEHHWJVB
      ZPVSWKCWLVTJCCWLRMDEHHWJWGWGUTUPUQMURQZWHGPZWIGPZOZWJGPVSWPWJGGSGWHGWIGTG
      VAVCVDVRGHNVQVRGWFHFGIVELVFVDZWQWQVGVSDEGFHHWJFWKHWMWNWIFPZOVSWJGFSZFWHGW
      IFTVQWSFPVRFGVHVIVJWQVSFWFHVSFRNFWFNFGIVKFGRVLVMZLVFZXAVGVSDEFGHHWJFWKHWM
      WHFPZWOOVSWJFGSZFWHFWIGTVQXCFPVRFGVNVIVJXAWQXAVGVSFFWKUMFWFVSDEFFHHWJFWKH
      WMXBWROZWJFPVSXDWJFFSFWHFWIFTFVAVCVDXAXAXAVGWTVOVP $.
  $}

  ${
    $d .x. y $.  $d C a b c m n $.  $d C y $.  $d D a b c m n $.  $d E c m n $.
    $d H p q $.  $d J n $.  $d J p q $.  $d f g $.
    setc1onsubc.c $e |- C = { <. ( Base ` ndx ) , { (/) } >. ,
              <. ( Hom ` ndx ) , { <. (/) , (/) , 2o >. } >. ,
              <. ( comp ` ndx ) , { <. <. (/) , (/) >. , (/) , .x. >. } >. } $.
    setc1onsubc.x $e |- .x. = ( f e. 2o , g e. 2o |-> ( f i^i g ) ) $.
    setc1onsubc.e $e |- E = ( SetCat ` 1o ) $.
    setc1onsubc.j $e |- J = ( Homf ` E ) $.
    setc1onsubc.s $e |- S = 1o $.
    setc1onsubc.h $e |- H = ( Homf ` C ) $.
    setc1onsubc.i $e |- .1. = ( Id ` C ) $.
    setc1onsubc.d $e |- D = ( C |`cat J ) $.
    $( Construct a category with one object and two morphisms and prove that
       category ` ( SetCat `` 1o ) ` satisfies all conditions for a subcategory
       but the compatibility of identity morphisms, showing the necessity of
       the latter condition in defining a subcategory.  Exercise 4A of [Adamek]
       p. 58.  (Contributed by Zhi Wang, 6-Nov-2025.) $)
    setc1onsubc $p |- ( C e. Cat /\ J Fn ( S X. S ) /\
    ( J C_cat H /\ -. A. x e. S ( .1. ` x ) e. ( x J x ) /\ D e. Cat ) ) $=
      ( c0 vy vp vq va vb vc vm vn ccat wcel cxp wfn cssc wbr cv cfv co wral wn
      w3a ccid csn c1o cmpt wceq wss cvv wa 0ss 1oex c2o df2o3 incat simpli cbs
      mp2an setc1obas eqtri homffn ssid cpr snsspr1 cotp wtru setc1ohomfval a1i
      0lt1o homfval mptru ovsn2 3eqtri cop snex catbas cathomfval 0ex snid 2oex
      df1o2 3sstr4i oveq1 sseq12d ralsn oveq2 bitri mpbir eqtr3i isssc mpbir2an
      ralbidv wb con0 1on eqeltrri onirri wrex biid rexeqbii rexnal fveq2 fvmpt
      simpri ax-mp eqtrdi oveq12 anidms eleq12d notbid rexsn mpbi csetc eqeltri
      3bitr3ri velsn oveq12d eleq2d bitrdi cin oveq123d 3pm3.2i termccatd simp1
      ctermc setc1oterm catcofval setc1ocofval 3anbi123i anbi1i anbi12d pm5.32i
      simp2 simp3 prid1 eleqtrri ineq12 0in ovmpoa eqtr4i simpl1 simpl2 opeq12d
      simpl3 cmpo mpoex simprr simprl 3eqtr4a sylbi adantll resccat ) BUIUJZKDD
      UKULKJUMUNZAUOZFUPZUVMUVMKUQZUJZADURUSZCUIUJZUTUVKBVAUPZUATVBZVCVDZVEZTVC
      VFVCVGUJUVKUWBVHVCVIVJUABEGHTVCVKVGTLVLMVMVPZVNDIKODVCIVOUPZPINVQZVRVSUVL
      UVQUVRUVLUVTUVTVFZUBUOZUCUOZKUQZUWGUWHJUQZVFZUCUVTURZUBUVTURZUVTVTZUWMTTK
      UQZTTJUQZVFZUVTTVCWAZUWOUWPTVCWBUWOTTTTVCWCVBZUQZVCUVTUWOUWTVEWDVCIKUWSTT
      OUWEINWETVCUJWDWGWFZUXAWHWITTVCVJWJWSWKZUWPTTTTVKWCZVBZUQZVKUWRUWPUXEVEWD
      UVTBJUXDTTQUVTBTTWLZTEWCZVBZUXDLTWMZWNZUVTBUXHUXDLUXCWMWOTUVTUJZWDTWPWQZW
      FZUXMWHWITTVKWRWJVLWKWTUWMTUWHKUQZTUWHJUQZVFZUCUVTURZUWQUWLUXQUBTWPUWGTVE
      ZUWKUXPUCUVTUXRUWIUXNUWJUXOUWGTUWHKXAUWGTUWHJXAXBXJXCUXPUWQUCTWPUWHTVEUXN
      UWOUXOUWPUWHTTKXDUWHTTJXDXBXCXEXFUVLUWFUWMVHXKWDUBUCUVTUVTKJVGKUVTUVTUKZU
      LWDUVTIKOVCUVTUWDWSUWEXGZVSWFJUXSULWDUVTBJQUXJVSWFUVTVGUJWDUXIWFXHWIXIUVT
      UVTUJZUSZUVQUVTVCUVTXLWSXMXNXOUVPUSZADXPUYCAUVTXPUVQUYBUYCUYCADUVTDVCUVTP
      WSVRUYCXQXRUVPADXSUYCUYBATWPUVMTVEZUVPUYAUYDUVNUVTUVOUVTUYDUVNTFUPZUVTUVM
      TFXTUXKUYEUVTVEUXLUATVCUVTUVTFVCUVTVEUAUOTVEWSWFFUVSUWARUVKUWBUWCYBVRUXIY
      AYCYDUYDUVOUWOUVTUYDUVOUWOVEUVMTUVMTKYEYFUXBYDYGYHYIYMYJUVRIUIUJZIVCYKUPZ
      UINUYGUIUJWDUYGUYGUUCUJWDUUDWFUUAWIYLZUVRUYFXKWDUDUEUFUVTBCUVTUXFTTTTWCZV
      BZWCVBZUXHUGUHIKUISUXJUXTOUVTBUXHUXDLUXGWMUUEINUUFUDUOZUVTUJZUEUOZUVTUJZU
      FUOZUVTUJZUTZUGUOZUYLUYNKUQZUJZUHUOZUYNUYPKUQZUJZVHZVUBUYSUYLUYNWLZUYPUXH
      UQZUQZVUBUYSVUFUYPUYKUQZUQZVEZWDUYRVUEVHZUYLTVEZUYNTVEZUYPTVEZUTZUYSTVEZV
      UBTVEZVHZVHZVUKVULVUPVUEVHVUTUYRVUPVUEUYMVUMUYOVUNUYQVUOUDTYNUETYNUFTYNUU
      GUUHVUPVUEVUSVUPVUAVUQVUDVURVUPVUAUYSUVTUJVUQVUPUYTUVTUYSVUPUYTUWOUVTVUPU
      YLTUYNTKVUMVUNVUOUUBVUMVUNVUOUUKZYOUXBYDYPUGTYNYQVUPVUDVUBUVTUJVURVUPVUCU
      VTVUBVUPVUCUWOUVTVUPUYNTUYPTKVVAVUMVUNVUOUULYOUXBYDYPUHTYNYQUUIUUJXEVUTTT
      EUQZTTUYJUQZVUHVUJVVBTVVCTVKUJZVVDVVBTVETUWRVKTVCWPUUMVLUUNZVVEGHTTVKVKGU
      OZHUOZYRZTEVVFTVEVVGTVEVHVVHTTYRTVVFTVVGTUUOTUUPYDMWPUUQVPTTTWPWJUURVUTVU
      BTUYSTVUGEVUTVUGUXFTUXHUQEVUTVUFUXFUYPTUXHVUTUYLTUYNTVUMVUNVUOVUSUUSVUMVU
      NVUOVUSUUTUVAZVUMVUNVUOVUSUVBZYOUXFTEEGHVKVKVVHUVCVGMGHVKVKVVHWRWRUVDYLWJ
      YDVUPVUQVURUVEZVUPVUQVURUVFZYSVUTVUBTUYSTVUIUYJVUTVUIUXFTUYKUQUYJVUTVUFUX
      FUYPTUYKVVIVVJYOUXFTUYJUYIWMWJYDVVKVVLYSUVGUVHUVIUYFWDUYHWFUWFWDUWNWFUVJW
      IXFYTYT $.
    $( $j usage 'setc1onsubc' avoids 'ax-reg'; $)
  $}

  ${
    $d C c j s x $.  $d J j s x $.  $d S s x $.
    cnelsubclem.1 $e |- J e. _V $.
    cnelsubclem.2 $e |- S e. _V $.
    cnelsubclem.3 $e |- ( C e. Cat /\ J Fn ( S X. S ) /\
          ( J C_cat ( Homf ` C ) /\ -. A. x e. S
            ( ( Id ` C ) ` x ) e. ( x J x ) /\ ( C |`cat J ) e. Cat ) ) $.
    $( Lemma for ~ cnelsubc .  (Contributed by Zhi Wang, 6-Nov-2025.) $)
    cnelsubclem $p |- E. c e. Cat E. j E. s ( j Fn ( s X. s ) /\
      ( j C_cat ( Homf ` c ) /\ -. A. x e. s ( ( Id ` c ) ` x ) e. ( x j x )
      /\ ( c |`cat j ) e. Cat ) ) $=
      ( ccat wcel cv cfv cssc co wral wn cresc wex cxp wfn wbr ccid w3a wa wrex
      chomf simp1i simp2i simp3i id sqxpeqd fneq2d raleq notbid 3anbi2d anbi12d
      wceq spcev fneq1 breq1 eleq2d ralbidv oveq2 eleq1d 3anbi123d exbidv mp2an
      oveq syl fveq2 breq2d fveq1d oveq1 anbi2d 2exbidv rspcev ) BKLZDMZFMZWAUA
      ZUBZVTBUHNZOUCZAMZBUDNZNZWFWFVTPZLZAWAQZRZBVTSPZKLZUEZUFZFTZDTZWCVTGMZUHN
      ZOUCZWFWSUDNZNZWILZAWAQZRZWSVTSPZKLZUEZUFZFTDTZGKUGVSECCUAZUBZEWDOUCZWHWF
      WFEPZLZACQZRZBESPZKLZUEZJUIXMYAWRVSXMYAJUJVSXMYAJUKXMYAUFZEWBUBZXNXPAWAQZ
      RZXTUEZUFZFTZWRYGYBFCIWACUSZYCXMYFYAYIWBXLEYIWACYIULUMUNYIYEXRXNXTYIYDXQX
      PAWACUOUPUQURUTWQYHDEHVTEUSZWPYGFYJWCYCWOYFWBVTEVAYJWEXNWLYEWNXTVTEWDOVBY
      JWKYDYJWJXPAWAYJWIXOWHWFWFVTEVJVCVDUPYJWMXSKVTEBSVEVFVGURVHUTVKVIXKWRGBKW
      SBUSZXJWPDFYKXIWOWCYKXAWEXFWLXHWNYKWTWDVTOWSBUHVLVMYKXEWKYKXDWJAWAYKXCWHW
      IYKWFXBWGWSBUDVLVNVFVDUPYKXGWMKWSBVTSVOVFVGVPVQVRVI $.
  $}

  ${
    $d c f g j s x $.
    $( Remark 4.2(2) of [Adamek] p. 48.  There exists a _category_ satisfying
       all conditions for a subcategory but the compatibility of identity
       morphisms.  Therefore such condition in ~ df-subc is necessary.  A
       stronger statement than ~ nelsubc3 .  (Contributed by Zhi Wang,
       6-Nov-2025.) $)
    cnelsubc $p |- E. c e. Cat E. j E. s ( j Fn ( s X. s ) /\
      ( j C_cat ( Homf ` c ) /\ -. A. x e. s ( ( Id ` c ) ` x ) e. ( x j x )
      /\ ( c |`cat j ) e. Cat ) ) $=
      ( vf vg cnx cbs cfv c0 csn cop chom c2o cotp cco cv c1o chomf eqid cin co
      cmpo ctp csetc fvex 1oex cresc ccid setc1onsubc cnelsubclem ) AGHIJKLGMIJ
      JNOKLGPIJJLJEFNNEQFQUAUCZOKLUDZRBRUEIZSIZCDUNSUFUGAUMUMUOUHUBZRULUMUIIZEF
      UNUMSIZUOUMTULTUNTUOTRTURTUQTUPTUJUK $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Kan extensions and related concepts
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Kan extensions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $c Lan $.
  $c Ran $.

  $( Class function defining the (local) left Kan extension. $)
  clan $a class Lan $.

  $( Class function defining the (local) right Kan extension. $)
  cran $a class Ran $.

$(
  @{
    @d c d e f g p s @.
    @( Definition of the (local) left Kan extension.
       ` ( F ( <. C , D >. Lan E ) X ) ` becomes
       ` <" C D E "> Lan <. F , X >. ` in this definition.  (Contributed by Zhi
       Wang, 3-Nov-2025.) @)
    df-lan @a |- Lan = ( s e. _V , p e. _V |->
            [_ ( s ` 0 ) / c ]_ [_ ( s ` 1 ) / d ]_ [_ ( s ` 2 ) / e ]_
            ( ( <. d , e >. -o.F ( 1st ` p ) )
              ( ( d FuncCat e ) UP ( c FuncCat e ) ) ( 2nd ` p ) ) ) @.

    @( Definition of the (local) right Kan extension.  The dual concept of
       ~ df-lan .  (Contributed by Zhi Wang, 3-Nov-2025.) @)
    df-ran @a |- Ran = ( s e. _V , p e. _V |->
            [_ ( s ` 0 ) / c ]_ [_ ( s ` 1 ) / d ]_ [_ ( s ` 2 ) / e ]_
            ( ( ( f e. _V , g e. _V |-> <. f , tpos g >. ) `
                ( <. d , e >. -o.F ( 1st ` p ) ) )
              ( ( oppCat ` ( d FuncCat e ) ) UP ( oppCat ` ( c FuncCat e ) ) )
              ( 2nd ` p ) ) ) @.
  @}

  @{
    @d c d e p s @.
    @( The domain of ` Lan ` is a relation.  (Contributed by Zhi Wang,
       3-Nov-2025.) @)
    reldmlan @p |- Rel dom Lan @=
      ( vs vp vc vd ve cvv cc0 cv cfv c1 cop c1st cprcof c2nd cfuc cup csb clan
      c2 co df-lan reldmmpo ) ABFFCGAHZIDJUCIESUCIDHZEHZKBHZLIMTUFNIUDUEOTCHUEO
      TPTTQQQREABCDUAUB @.
  @}

  @{
    @d C d e @.  @d D e @.  @d K c d e p s @.  @d P c d e p s @.
    @d Q c d e p s @.  @d R c d e p s @.  @d S c d e p s @.  @d X c d e p s @.
    @d c d e p ph s @.
    lanfvalg.s @e |- ( ph -> S e. V ) @.
    lanfvalg.p @e |- ( ph -> P e. W ) @.
    lanfvalg.c @e |- ( ph -> ( S ` 0 ) = C ) @.
    lanfvalg.d @e |- ( ph -> ( S ` 1 ) = D ) @.
    lanfvalg.e @e |- ( ph -> ( S ` 2 ) = E ) @.
    lanfvalg.f @e |- ( ph -> ( 1st ` P ) = F ) @.
    lanfvalg.x @e |- ( ph -> ( 2nd ` P ) = X ) @.
    lanfvalg.k @e |- ( ph -> ( <. D , E >. -o.F F ) = K ) @.
    lanfvalg.q @e |- Q = ( D FuncCat E ) @.
    lanfvalg.r @e |- R = ( C FuncCat E ) @.
    @( Value of the set of left Kan extensions.  (Contributed by Zhi Wang,
       3-Nov-2025.) @)
    lanfvalg @p |- ( ph -> ( S Lan P ) = ( K ( Q UP R ) X ) ) @=
      ( vs vp vc vd ve cvv cc0 cv cfv c1 cop c1st cprcof c2nd cfuc cup csb clan
      c2 co cmpo wceq df-lan a1i wa fvexd simprl fveq1d adantr simplrl ad2antrr
      eqtrd simplr simpr oveq12d eqtr4di simpllr opeq12d simprd fveq2d oveq123d
      ad3antrrr ad4antr csbied2 elexd ovexd ovmpod ) AUDUEGDUIUIUFUJUDUKZULZUGU
      MWKULZUHVBWKULZUGUKZUHUKZUNZUEUKZUOULZUPVCZWRUQULZWOWPURVCZUFUKZWPURVCZUS
      VCZVCZUTZUTZUTZJMEFUSVCZVCZVAUIVAUDUEUIUIXIVDVEAUHUDUEUFUGVFVGAWKGVEZWRDV
      EZVHZVHZUFWLBXHXKUIXOUJWKVIXOWLUJGULZBXOUJWKGAXLXMVJVKAXPBVEXNPVLVOXOXCBV
      EZVHZUGWMCXGXKUIXRUMWKVIXRWMUMGULZCXRUMWKGAXLXMXQVMZVKAXSCVEXNXQQVNVOXRWO
      CVEZVHZUHWNHXFXKUIYBVBWKVIYBWNVBGULZHYBVBWKGXRXLYAXTVLVKAYCHVEXNXQYARWEVO
      YBWPHVEZVHZWTJXAMXEXJYEXBEXDFUSYEXBCHURVCEYEWOCWPHURXRYAYDVPZYBYDVQZVRUBV
      SYEXDBHURVCFYEXCBWPHURXOXQYAYDVTYGVRUCVSVRYEWTCHUNZIUPVCZJYEWQYHWSIUPYEWO
      CWPHYFYGWAYEWSDUOULZIYEWRDUOYEXLXMYBXNYDAXNXQYAVTVLWBZWCAYJIVEXNXQYAYDSWF
      VOVRAYIJVEXNXQYAYDUAWFVOYEXADUQULZMYEWRDUQYKWCAYLMVEXNXQYAYDTWFVOWDWGWGWG
      AGKNWHADLOWHAJMXJWIWJ @.
  @}

  @{
    @( The set of left Kan extensions is a relation.  (Contributed by Zhi Wang,
       3-Nov-2025.) @)
    rellan @p |- Rel ( S Lan P ) @=
      ( cvv wcel wa clan co wrel c1 cfv c2 c1st cprcof cfuc eqidd releqd mpbiri
      cop eqid c0 c2nd cc0 cup relup simpl simpr lanfvalg rel0 reldmlan pm2.61i
      wn ovprc ) BCDZACDZEZBAFGZHZUOUQIBJZKBJZRALJZMGZAUAJZURUSNGZUBBJZUSNGZUCG
      GZHVCVEVAVBUDUOUPVFUOVDURAVCVEBUSUTVACCVBUMUNUEUMUNUFUOVDOUOUROUOUSOUOUTO
      UOVBOUOVAOVCSVESUGPQUOUKZUQTHUHVGUPTBAFUIULPQUJ @.
  @}

  @{
    lanfval.c @e |- ( ph -> C e. U ) @.
    lanfval.d @e |- ( ph -> D e. V ) @.
    lanfval.e @e |- ( ph -> E e. W ) @.
    lanfval.f @e |- ( ph -> F e. Y ) @.
    lanfval.x @e |- ( ph -> X e. Z ) @.
    lanfval.k @e |- ( ph -> ( <. D , E >. -o.F F ) = K ) @.
    lanfval.q @e |- Q = ( D FuncCat E ) @.
    lanfval.r @e |- R = ( C FuncCat E ) @.
    @( Value of the set of left Kan extensions.  (Contributed by Zhi Wang,
       3-Nov-2025.) @)
    lanfval @p |- ( ph -> ( <" C D E "> Lan <. F , X >. )
                        = ( K ( Q UP R ) X ) ) @=
      ( cop cs3 cvv cword wcel s3cli a1i opex cc0 cfv wceq s3fv0 c1 s3fv1 s3fv2
      syl c2 c1st op1stg syl2anc c2nd op2ndg lanfvalg ) ABCHLUCZDEBCGUDZGHIUEUF
      ZUELVGVHUGABCGUHUIVFUEUGAHLUJUIABFUGUKVGULBUMOBCGFUNURACJUGUOVGULCUMPBCGJ
      UPURAGKUGUSVGULGUMQBCGKUQURAHMUGZLNUGZVFUTULHUMRSHLMNVAVBAVIVJVFVCULLUMRS
      HLMNVDVBTUAUBVE @.
  @}
$)

  ${
    $d c d e f p x $.
    $( Definition of the (local) left Kan extension.  Given a functor
       ` F : C --> D ` and a functor ` X : C --> E ` , the set
       ` ( F ( <. C , D >. Lan E ) X ) ` consists of left Kan extensions of
       ` X ` along ` F ` , which are universal pairs from ` X ` to the
       pre-composition functor given by ` F ` ( ~ lanval2 ).  See also
       <HTML>&sect;</HTML> 3 of Chapter X in p. 240 of Mac Lane, Saunders,
       _Categories for the Working Mathematician_, 2nd Edition, Springer
       Science+Business Media, New York, (1998) [QA169.M33 1998]; available at
       ~ https://math.mit.edu/~~hrm/palestine/maclane-categories.pdf (retrieved
       3 Nov 2025).

       A left Kan extension is in the form of ` <. L , A >. ` where the first
       component is a functor ` L : D --> E ` ( ~ lanrcl4 ) and the second
       component is a natural transformation ` A : X --> L F ` ( ~ lanrcl5 )
       where ` L F ` is the composed functor.  Intuitively, the first component
       ` L ` can be regarded as the result of an "inverse" of pre-composition;
       the source category of ` X : C --> E ` is "extended" along
       ` F : C --> D ` .

       The left Kan extension is a generalization of many categorical concepts
       such as colimit.  In <HTML>&sect;</HTML> 7 of Chapter X of _Categories
       for the Working Mathematician_, it is concluded that "the notion of Kan
       extensions subsumes all the other fundamental concepts of category
       theory".

       This definition was chosen over the other version in the commented out
       section due to its better reverse closure property.

       See ~ df-ran for the dual concept.

       (Contributed by Zhi Wang, 3-Nov-2025.) $)
    df-lan $a |- Lan = ( p e. ( _V X. _V ) , e e. _V |->
     [_ ( 1st ` p ) / c ]_ [_ ( 2nd ` p ) / d ]_
     ( f e. ( c Func d ) , x e. ( c Func e ) |->
     ( ( <. d , e >. -o.F f ) ( ( d FuncCat e ) UP ( c FuncCat e ) ) x ) ) ) $.

    $( Definition of the (local) right Kan extension.  Given a functor
       ` F : C --> D ` and a functor ` X : C --> E ` , the set
       ` ( F ( <. C , D >. Ran E ) X ) ` consists of right Kan extensions of
       ` X ` along ` F ` , which are universal pairs from the pre-composition
       functor given by ` F ` to ` X ` ( ~ ranval2 ).  The definition in
       <HTML>&sect;</HTML> 3 of Chapter X in p. 236 of Mac Lane, Saunders,
       _Categories for the Working Mathematician_, 2nd Edition, Springer
       Science+Business Media, New York, (1998) [QA169.M33 1998]; available at
       ~ https://math.mit.edu/~~hrm/palestine/maclane-categories.pdf (retrieved
       3 Nov 2025).

       A right Kan extension is in the form of ` <. L , A >. ` where the first
       component is a functor ` L : D --> E ` ( ~ ranrcl4 ) and the second
       component is a natural transformation ` A : L F --> X ` ( ~ ranrcl5 )
       where ` L F ` is the composed functor.  Intuitively, the first component
       ` L ` can be regarded as the result of an "inverse" of pre-composition;
       the source category of ` X : C --> E ` is "extended" along
       ` F : C --> D ` .

       The right Kan extension is a generalization of many categorical concepts
       such as limit.  In <HTML>&sect;</HTML> 7 of Chapter X of _Categories for
       the Working Mathematician_, it is concluded that "the notion of Kan
       extensions subsumes all the other fundamental concepts of category
       theory".

       This definition was chosen over the other version in the commented out
       section due to its better reverse closure property.

       See ~ df-lan for the dual concept.

       (Contributed by Zhi Wang, 4-Nov-2025.) $)
    df-ran $a |- Ran = ( p e. ( _V X. _V ) , e e. _V |->
     [_ ( 1st ` p ) / c ]_ [_ ( 2nd ` p ) / d ]_
     ( f e. ( c Func d ) , x e. ( c Func e ) |->
     ( ( oppFunc ` ( <. d , e >. -o.F f ) )
       ( ( oppCat ` ( d FuncCat e ) ) UP ( oppCat ` ( c FuncCat e ) ) )
       x ) ) ) $.

    $( ` Lan ` is a function on ` ( ( _V X. _V ) X. _V ) ` .  (Contributed by
       Zhi Wang, 3-Nov-2025.) $)
    lanfn $p |- Lan Fn ( ( _V X. _V ) X. _V ) $=
      ( vp ve vc vd vf vx cvv cxp cv c1st cfv c2nd cfunc co cop cprcof cfuc csb
      ovex csbex cup cmpo clan df-lan mpoex fnmpoi ) ABGGHGCAIZJKZDUGLKZEFCIZDI
      ZMNZUJBIZMNZUKUMOEIPNFIUKUMQNUJUMQNUANNZUBZRZRUCFBEACDUDCUHUQDUIUPEFULUNU
      OUJUKMSUJUMMSUETTUF $.

    $( ` Ran ` is a function on ` ( ( _V X. _V ) X. _V ) ` .  (Contributed by
       Zhi Wang, 4-Nov-2025.) $)
    ranfn $p |- Ran Fn ( ( _V X. _V ) X. _V ) $=
      ( vp ve vc vd vf vx cvv cxp cv c1st cfv c2nd cfunc co cop cfuc coppc ovex
      csb csbex cprcof coppf cup cmpo cran df-ran mpoex fnmpoi ) ABGGHGCAIZJKZD
      UILKZEFCIZDIZMNZULBIZMNZUMUOOEIUANUBKFIUMUOPNQKULUOPNQKUCNNZUDZSZSUEFBEAC
      DUFCUJUSDUKUREFUNUPUQULUMMRULUOMRUGTTUH $.

    $( The domain of ` Lan ` is a relation.  (Contributed by Zhi Wang,
       3-Nov-2025.) $)
    reldmlan $p |- Rel dom Lan $=
      ( vp ve vc vd vf vx cvv cxp cv c1st cfv c2nd cfunc co cop cprcof cfuc cup
      cmpo csb clan df-lan reldmmpo ) ABGGHGCAIZJKDUDLKEFCIZDIZMNUEBIZMNUFUGOEI
      PNFIUFUGQNUEUGQNRNNSTTUAFBEACDUBUC $.

    $( The domain of ` Ran ` is a relation.  (Contributed by Zhi Wang,
       4-Nov-2025.) $)
    reldmran $p |- Rel dom Ran $=
      ( vp ve vc vd vf vx cvv cxp cv c1st cfv c2nd cfunc cop cprcof coppf coppc
      co cfuc csb cup cmpo cran df-ran reldmmpo ) ABGGHGCAIZJKDUFLKEFCIZDIZMRUG
      BIZMRUHUINEIORPKFIUHUISRQKUGUISRQKUARRUBTTUCFBEACDUDUE $.
  $}

  ${
    $d C c d e f p x $.  $d D c d e f p x $.  $d E c d e f p x $.
    $d O c d e p $.  $d P c d e p $.  $d R c d e p $.  $d S c d e p $.
    $d U c d e p $.  $d V c d e p $.  $d W c d e p $.  $d c d e f p ph x $.
    lanfval.r $e |- R = ( D FuncCat E ) $.
    lanfval.s $e |- S = ( C FuncCat E ) $.
    lanfval.c $e |- ( ph -> C e. U ) $.
    lanfval.d $e |- ( ph -> D e. V ) $.
    lanfval.e $e |- ( ph -> E e. W ) $.
    $( Value of the function generating the set of left Kan extensions.
       (Contributed by Zhi Wang, 3-Nov-2025.) $)
    lanfval $p |- ( ph -> ( <. C , D >. Lan E ) =
                            ( f e. ( C Func D ) , x e. ( C Func E ) |->
                              ( ( <. D , E >. -o.F f ) ( R UP S ) x ) ) ) $=
      ( cvv cfunc co wceq vp ve vc vd cop cxp cv c1st cfv c2nd cprcof cfuc cmpo
      cup csb clan df-lan a1i wa fvexd simprl fveq2d wcel op1stg syl2anc adantr
      eqtrd simplrl op2ndg ad2antrr simplr simpr oveq12d simpllr simprd eqtr4di
      opeq12d oveq1d eqidd oveq123d mpoeq123dv csbied2 elexd opelxpd ovex mpoex
      ovmpod ) AUAUBCDUEZIQQUFZQUCUAUGZUHUIZUDWJUJUIZHBUCUGZUDUGZRSZWMUBUGZRSZW
      NWPUEZHUGZUKSZBUGZWNWPULSZWMWPULSZUNSZSZUMZUOZUOZHBCDRSZCIRSZDIUEZWSUKSZX
      AEFUNSZSZUMZUPQUPUAUBWIQXHUMTABUBHUAUCUDUQURAWJWHTZWPITZUSZUSZUCWKCXGXOQX
      SWJUHUTXSWKWHUHUIZCXSWJWHUHAXPXQVAVBAXTCTZXRACGVCZDJVCZYANOCDGJVDVEVFVGXS
      WMCTZUSZUDWLDXFXOQYEWJUJUTYEWLWHUJUIZDYEWJWHUJAXPXQYDVHVBAYFDTZXRYDAYBYCY
      GNOCDGJVIVEVJVGYEWNDTZUSZHBWOWQXEXIXJXNYIWMCWNDRXSYDYHVKZYEYHVLZVMYIWMCWP
      IRYJYIXPXQAXRYDYHVNVOZVMYIWTXLXAXAXDXMYIXBEXCFUNYIXBDIULSEYIWNDWPIULYKYLV
      MLVPYIXCCIULSFYIWMCWPIULYJYLVMMVPVMYIWRXKWSUKYIWNDWPIYKYLVQVRYIXAVSVTWAWB
      WBACDQQACGNWCADJOWCWDAIKPWCXOQVCAHBXIXJXNCDRWECIRWEWFURWG $.

    ranfval.o $e |- O = ( oppCat ` R ) $.
    ranfval.p $e |- P = ( oppCat ` S ) $.
    $( Value of the function generating the set of right Kan extensions.
       (Contributed by Zhi Wang, 4-Nov-2025.) $)
    ranfval $p |- ( ph -> ( <. C , D >. Ran E ) =
          ( f e. ( C Func D ) , x e. ( C Func E ) |->
            ( ( oppFunc ` ( <. D , E >. -o.F f ) ) ( O UP P ) x ) ) ) $=
      ( vp ve vc vd cop cvv cxp cv c1st cfv c2nd cfunc co cprcof coppf cfuc cup
      coppc cmpo csb cran wceq df-ran a1i wa fvexd simprl fveq2d op1stg syl2anc
      adantr eqtrd simplrl op2ndg ad2antrr simplr oveq12d simpllr simprd fveq2i
      wcel simpr eqtri eqtr4di opeq12d fvoveq1d eqidd oveq123d mpoeq123dv elexd
      csbied2 opelxpd ovex mpoex ovmpod ) AUAUBCDUEZJUFUFUGZUFUCUAUHZUIUJZUDWRU
      KUJZIBUCUHZUDUHZULUMZXAUBUHZULUMZXBXDUEZIUHZUNUMUOUJZBUHZXBXDUPUMZURUJZXA
      XDUPUMZURUJZUQUMZUMZUSZUTZUTZIBCDULUMZCJULUMZDJUEZXGUNUMUOUJZXIKEUQUMZUMZ
      USZVAUFVAUAUBWQUFXRUSVBABUBIUAUCUDVCVDAWRWPVBZXDJVBZVEZVEZUCWSCXQYEUFYIWR
      UIVFYIWSWPUIUJZCYIWRWPUIAYFYGVGVHAYJCVBZYHACHWAZDLWAZYKPQCDHLVIVJVKVLYIXA
      CVBZVEZUDWTDXPYEUFYOWRUKVFYOWTWPUKUJZDYOWRWPUKAYFYGYNVMVHAYPDVBZYHYNAYLYM
      YQPQCDHLVNVJVOVLYOXBDVBZVEZIBXCXEXOXSXTYDYSXACXBDULYIYNYRVPZYOYRWBZVQYSXA
      CXDJULYTYSYFYGAYHYNYRVRVSZVQYSXHYBXIXIXNYCYSXKKXMEUQYSXKDJUPUMZURUJZKYSXJ
      UUCURYSXBDXDJUPUUAUUBVQVHKFURUJUUDSFUUCURNVTWCWDYSXMCJUPUMZURUJZEYSXLUUEU
      RYSXACXDJUPYTUUBVQVHEGURUJUUFTGUUEUROVTWCWDVQYSXFYAXGUOUNYSXBDXDJUUAUUBWE
      WFYSXIWGWHWIWKWKACDUFUFACHPWJADLQWJWLAJMRWJYEUFWAAIBXSXTYDCDULWMCJULWMWNV
      DWO $.
  $}

  ${
    $d A f x $.  $d B f x $.  $d C f x $.  $d D f x $.  $d E f x $.
    $d F f x $.  $d V f x $.  $d f ph x $.
    lanpropd.1 $e |- ( ph -> ( Homf ` A ) = ( Homf ` B ) ) $.
    lanpropd.2 $e |- ( ph -> ( comf ` A ) = ( comf ` B ) ) $.
    lanpropd.3 $e |- ( ph -> ( Homf ` C ) = ( Homf ` D ) ) $.
    lanpropd.4 $e |- ( ph -> ( comf ` C ) = ( comf ` D ) ) $.
    lanpropd.5 $e |- ( ph -> ( Homf ` E ) = ( Homf ` F ) ) $.
    lanpropd.6 $e |- ( ph -> ( comf ` E ) = ( comf ` F ) ) $.
    lanpropd.a $e |- ( ph -> A e. V ) $.
    lanpropd.b $e |- ( ph -> B e. V ) $.
    lanpropd.c $e |- ( ph -> C e. V ) $.
    lanpropd.d $e |- ( ph -> D e. V ) $.
    lanpropd.e $e |- ( ph -> E e. V ) $.
    lanpropd.f $e |- ( ph -> F e. V ) $.
    $( If the categories have the same set of objects, morphisms, and
       compositions, then they have the same left Kan extensions.  (Contributed
       by Zhi Wang, 21-Nov-2025.) $)
    lanpropd $p |- ( ph -> ( <. A , C >. Lan E ) = ( <. B , D >. Lan F ) ) $=
      ( vf vx cfunc co cop cprcof cfuc cup cmpo clan funcpropd wceq wcel adantr
      cv wa chomf ccomf ccat funcrcl ad2antrl simprd catpropd ad2antll fucpropd
      mpbid simpld oveq12d simprl prcofpropd eqidd oveq123d mpoeq123dva lanfval
      cfv eqid 3eqtr4d ) AUAUBBDUCUDZBFUCUDZDFUEUAUOZUFUDZUBUOZDFUGUDZBFUGUDZUH
      UDZUDZUIUAUBCEUCUDZCGUCUDZEGUEVTUFUDZWBEGUGUDZCGUGUDZUHUDZUDZUIBDUEFUJUDC
      EUEGUJUDAUAUBVRVSWFWGWHWMABCDEHIJKLOPQRUKAVSWHULVTVRUMZABCFGHIJMNOPSTUKUN
      AWNWBVSUMZUPZUPZWAWIWBWBWEWLWQWCWJWDWKUHWQDEFGADUQVOEUQVOULWPKUNZADURVOEU
      RVOULWPLUNZAFUQVOGUQVOULWPMUNZAFURVOGURVOULWPNUNZWQBUSUMZDUSUMZWNXBXCUPAW
      OBDVTUTVAZVBZWQXCEUSUMXEWQDEUSHWRWSXEAEHUMWPRUNVCVFZWQXBFUSUMZWOXBXGUPAWN
      BFWBUTVDVBZWQXGGUSUMXHWQFGUSHWTXAXHAGHUMWPTUNVCVFZVEWQBCFGABUQVOCUQVOULWP
      IUNZABURVOCURVOULWPJUNZWTXAWQXBXCXDVGZWQXBCUSUMXLWQBCUSHXJXKXLACHUMWPPUNV
      CVFXHXIVEVHWQDEFGVTUSVRWRWSWTXAXEXFXHXIAWNWOVIVJWQWBVKVLVMAUBBDWCWDHUAFHH
      WCVPWDVPOQSVNAUBCEWJWKHUAGHHWJVPWKVPPRTVNVQ $.

    $( If the categories have the same set of objects, morphisms, and
       compositions, then they have the same right Kan extensions.
       (Contributed by Zhi Wang, 21-Nov-2025.) $)
    ranpropd $p |- ( ph -> ( <. A , C >. Ran E ) = ( <. B , D >. Ran F ) ) $=
      ( vf vx cfunc co cop cprcof coppf cfv cfuc coppc cmpo cran funcpropd wceq
      cv wcel adantr wa chomf ccomf ccat funcrcl ad2antrl simprd catpropd mpbid
      cup ad2antll fucpropd fveq2d simpld oveq12d simprl prcofpropd mpoeq123dva
      eqidd oveq123d eqid ranfval 3eqtr4d ) AUAUBBDUCUDZBFUCUDZDFUEUAUOZUFUDZUG
      UHZUBUOZDFUIUDZUJUHZBFUIUDZUJUHZVGUDZUDZUKUAUBCEUCUDZCGUCUDZEGUEWCUFUDZUG
      UHZWFEGUIUDZUJUHZCGUIUDZUJUHZVGUDZUDZUKBDUEFULUDCEUEGULUDAUAUBWAWBWLWMWNX
      BABCDEHIJKLOPQRUMAWBWNUNWCWAUPZABCFGHIJMNOPSTUMUQAXCWFWBUPZURZURZWEWPWFWF
      WKXAXFWHWRWJWTVGXFWGWQUJXFDEFGADUSUHEUSUHUNXEKUQZADUTUHEUTUHUNXELUQZAFUSU
      HGUSUHUNXEMUQZAFUTUHGUTUHUNXENUQZXFBVAUPZDVAUPZXCXKXLURAXDBDWCVBVCZVDZXFX
      LEVAUPXNXFDEVAHXGXHXNAEHUPXERUQVEVFZXFXKFVAUPZXDXKXPURAXCBFWFVBVHVDZXFXPG
      VAUPXQXFFGVAHXIXJXQAGHUPXETUQVEVFZVIVJXFWIWSUJXFBCFGABUSUHCUSUHUNXEIUQZAB
      UTUHCUTUHUNXEJUQZXIXJXFXKXLXMVKZXFXKCVAUPYAXFBCVAHXSXTYAACHUPXEPUQVEVFXQX
      RVIVJVLXFWDWOUGXFDEFGWCVAWAXGXHXIXJXNXOXQXRAXCXDVMVNVJXFWFVPVQVOAUBBDWJWG
      WIHUAFWHHHWGVRWIVROQSWHVRWJVRVSAUBCEWTWQWSHUAGWRHHWQVRWSVRPRTWRVRWTVRVSVT
      $.
  $}

  ${
    $d E f x $.  $d P f x $.
    $( The domain of ` ( P Lan E ) ` is a relation.  (Contributed by Zhi Wang,
       3-Nov-2025.) $)
    reldmlan2 $p |- Rel dom ( P Lan E ) $=
      ( vf vx clan co cdm wrel cop cfv c0 wceq releqd mpbiri c1st c2nd eqid cvv
      dmeqd wcel rel0 df-ov id eqtrid dm0 eqtrdi wne cfunc cprcof cfuc cup cmpo
      cv reldmmpo cxp cres wfun fvfundmfvn0 simpld lanfn fndmi eleqtrdi opelxp1
      csn 1st2nd2 3syl oveq1d fvexd opelxp2 syl lanfval eqtrd pm2.61ine ) ABEFZ
      GZHZABIZEJZKVRKLZVPKHUAVSVOKVSVOKGKVSVNKVSVNVRKABEUBVSUCUDSUEUFMNVRKUGZVP
      CDAOJZAPJZUHFZWABUHFZWBBICUMUIFDUMWBBUJFZWABUJFZUKFFZULZGZHCDWCWDWGWHWHQU
      NVTVOWIVTVNWHVTVNWAWBIZBEFWHVTAWJBEVTVQRRUOZRUOZTZAWKTAWJLVTVQEGZWLVTVQWN
      TEVQVDUPUQVQEURUSWLEUTVAVBZABWKRVCARRVEVFVGVTDWAWBWEWFRCBRRWEQWFQVTAOVHVT
      APVHVTWMBRTWOABWKRVIVJVKVLSMNVM $.

    $( The domain of ` ( P Ran E ) ` is a relation.  (Contributed by Zhi Wang,
       4-Nov-2025.) $)
    reldmran2 $p |- Rel dom ( P Ran E ) $=
      ( vf vx cran co cdm wrel cop cfv c0 wceq releqd mpbiri c1st c2nd eqid cvv
      dmeqd wcel rel0 df-ov id eqtrid dm0 eqtrdi wne cfunc cv cprcof coppf cfuc
      coppc cup cmpo reldmmpo cres wfun fvfundmfvn0 simpld ranfn fndmi eleqtrdi
      cxp csn opelxp1 1st2nd2 3syl oveq1d fvexd opelxp2 ranfval eqtrd pm2.61ine
      syl ) ABEFZGZHZABIZEJZKVTKLZVRKHUAWAVQKWAVQKGKWAVPKWAVPVTKABEUBWAUCUDSUEU
      FMNVTKUGZVRCDAOJZAPJZUHFZWCBUHFZWDBICUIUJFUKJDUIWDBULFZUMJZWCBULFZUMJZUNF
      FZUOZGZHCDWEWFWKWLWLQUPWBVQWMWBVPWLWBVPWCWDIZBEFWLWBAWNBEWBVSRRVDZRVDZTZA
      WOTAWNLWBVSEGZWPWBVSWRTEVSVEUQURVSEUSUTWPEVAVBVCZABWORVFARRVGVHVIWBDWCWDW
      JWGWIRCBWHRRWGQWIQWBAOVJWBAPVJWBWQBRTWSABWORVKVOWHQWJQVLVMSMNVN $.
  $}

  ${
    $d C f x $.  $d D f x $.  $d E f x $.  $d F f x $.  $d J f x $.
    $d K f x $.  $d O f x $.  $d P f x $.  $d R f x $.  $d S f x $.
    $d X f x $.  $d f ph x $.
    lanval.r $e |- R = ( D FuncCat E ) $.
    lanval.s $e |- S = ( C FuncCat E ) $.
    lanval.f $e |- ( ph -> F e. ( C Func D ) ) $.
    lanval.x $e |- ( ph -> X e. ( C Func E ) ) $.
    ${
      lanval.k $e |- ( ph -> ( <. D , E >. -o.F F ) = K ) $.
      $( Value of the set of left Kan extensions.  (Contributed by Zhi Wang,
         3-Nov-2025.) $)
      lanval $p |- ( ph -> ( F ( <. C , D >. Lan E ) X )
                         = ( K ( R UP S ) X ) ) $=
        ( vf vx co cprcof ccat cfv cfunc cop cv cup clan cvv c1st c2nd funcrcl2
        func1st2nd funcrcl3 lanfval wceq wa simprl oveq2d adantr simprr oveq12d
        eqtrd ovexd ovmpod ) AOPGIBCUAQBFUAQCFUBZOUCZRQZPUCZDEUDQZQHIVGQBCUBFUE
        QUFAPBCDESOFSSJKABCGUGTZGUHTZABCGLUJZUIABCVHVIVJUKABFIUGTIUHTABFIMUJUKU
        LAVDGUMZVFIUMZUNZUNZVEHVFIVGVNVEVCGRQZHVNVDGVCRAVKVLUOUPAVOHUMVMNUQUTAV
        KVLURUSLMAHIVGVAVB $.
    $}

    ranval.k $e |- ( ph -> ( <. D , E >. -o.F F ) = <. J , K >. ) $.
    ranval.o $e |- O = ( oppCat ` R ) $.
    ranval.p $e |- P = ( oppCat ` S ) $.
    $( Value of the set of right Kan extensions.  (Contributed by Zhi Wang,
       4-Nov-2025.) $)
    ranval $p |- ( ph -> ( F ( <. C , D >. Ran E ) X )
                         = ( <. J , tpos K >. ( O UP P ) X ) ) $=
      ( co vf vx cfunc cop cprcof coppf cfv cup ctpos cran ccat c1st func1st2nd
      cv cvv c2nd funcrcl2 funcrcl3 ranfval wceq wa simprl oveq2d adantr fveq2d
      eqtrd df-ov wbr prcoffunca2 oppfval eqtr3id simprr oveq12d ovexd ovmpod
      syl ) AUAUBHLBCUCTBGUCTCGUDZUAUNZUETZUFUGZUBUNZKDUHTZTIJUIUDZLWBTBCUDGUJT
      UOAUBBCDEFUKUAGKUKUKMNABCHULUGZHUPUGZABCHOUMZUQABCWDWEWFURABGLULUGLUPUGAB
      GLPUMURZRSUSAVRHUTZWALUTZVAZVAZVTWCWALWBWKVTIJUDZUFUGZWCWKVSWLUFWKVSVQHUE
      TZWLWKVRHVQUEAWHWIVBVCAWNWLUTWJQVDVFVEAWMWCUTWJAWMIJUFTZWCIJUFVGAIJEFUCTV
      HWOWCUTABCEFGHIJMWGNOQVIEFIJVJVPVKVDVFAWHWIVLVMOPAWCLWBVNVO $.
  $}

  ${
    $d C f x $.  $d D f x $.  $d E c d e f p x $.  $d F c d e f p x $.
    $d L f x $.  $d P c d e f p x $.  $d X c d e f p x $.
    $( Reverse closure for left Kan extensions.  (Contributed by Zhi Wang,
       3-Nov-2025.) $)
    lanrcl $p |- ( L e. ( F ( <. C , D >. Lan E ) X ) ->
                   ( F e. ( C Func D ) /\ X e. ( C Func E ) ) ) $=
      ( vf vx cop clan co wcel cfunc cv cfuc c0 wne wceq cvv eqid cprcof cup wa
      cmpo id ne0i cfv cxp df-ov eqeq1i oveq 0ov eqtrdi sylbir necon3i cdm cres
      wfun fvfundmfvn0 simpld lanfn fndmi eleqtrdi opelxp1 4syl opelxp2 lanfval
      csn 3syl syl oveqd eleqtrd elmpocl ) EDFABIZCJKZKZLZEDFGHABMKZACMKZBCIGNU
      AKHNBCOKZACOKZUBKKZUDZKZLDVRLFVSLUCVQEVPWDVQUEVQVOWCDFVQVPPQZVOWCRVPEUFWE
      HABVTWASGCSSVTTWATWEVNCIZJUGZPQZWFSSUHZSUHZLZVNWILZASLWGPVPPWGPRVOPRZVPPR
      VOWGPVNCJUIUJWMVPDFPKPDFVOPUKDFULUMUNUOZWHWFJUPZWJWHWFWOLJWFVHUQURWFJUSUT
      WJJVAVBVCZVNCWISVDZABSSVDVEWEWHWKWLBSLWNWPWQABSSVFVEWEWHWKCSLWNWPVNCWISVF
      VIVGVJVKVLGHVRVSWBDFWCEWCTVMVJ $.

    $( Reverse closure for right Kan extensions.  (Contributed by Zhi Wang,
       4-Nov-2025.) $)
    ranrcl $p |- ( L e. ( F ( <. C , D >. Ran E ) X ) ->
                   ( F e. ( C Func D ) /\ X e. ( C Func E ) ) ) $=
      ( vf vx cop cran co wcel cfunc cv cfv cfuc c0 wceq cvv eqid cprcof cup wa
      coppf coppc cmpo wne ne0i cxp df-ov eqeq1i oveq 0ov eqtrdi sylbir necon3i
      id cdm csn cres wfun fvfundmfvn0 simpld ranfn fndmi eleqtrdi opelxp1 4syl
      opelxp2 3syl ranfval syl oveqd eleqtrd elmpocl ) EDFABIZCJKZKZLZEDFGHABMK
      ZACMKZBCIGNUAKUDOHNBCPKZUEOZACPKZUEOZUBKKZUFZKZLDVTLFWALUCVSEVRWHVSUQVSVQ
      WGDFVSVRQUGZVQWGRVREUHWIHABWEWBWDSGCWCSSWBTWDTWIVPCIZJOZQUGZWJSSUIZSUIZLZ
      VPWMLZASLWKQVRQWKQRVQQRZVRQRVQWKQVPCJUJUKWQVRDFQKQDFVQQULDFUMUNUOUPZWLWJJ
      URZWNWLWJWSLJWJUSUTVAWJJVBVCWNJVDVEVFZVPCWMSVGZABSSVGVHWIWLWOWPBSLWRWTXAA
      BSSVIVHWIWLWOCSLWRWTVPCWMSVIVJWCTWETVKVLVMVNGHVTWAWFDFWGEWGTVOVL $.

    $( The set of left Kan extensions is a relation.  (Contributed by Zhi Wang,
       3-Nov-2025.) $)
    rellan $p |- Rel ( F ( P Lan E ) X ) $=
      ( vx vp ve vc vd vf clan co wrel c0 cv wcel cfv cfuc cvv cfunc wceq releq
      rel0 mpbiri wne wex n0 c2nd cop cprcof c1st cup relup ne0i eqtrdi necon3i
      oveq 0ov cxp cmpo csb df-lan elmpocl1 1st2nd2 syl sylbi 3syl oveq1d oveqd
      exlimiv eqid wa id eleqtrd lanrcl simpld simprd eqidd lanval eqtrd releqd
      pm2.61ine ) CDABKLZLZMZWDNWDNUAWENMUCWDNUBUDWDNUEZEOZWDPZEUFWEEWDUGWHWEEW
      HWEAUHQZBUICUJLZDWIBRLZAUKQZBRLZULLLZMWKWMWJDUMWHWDWNWHWDCDWLWIUIZBKLZLZW
      NWHWCWPCDWHAWOBKWHWFWCNUEZAWOUAZWDWGUNWCNWDNWCNUAWDCDNLNCDWCNUQCDURUOUPWR
      WGWCPZEUFWSEWCUGWTWSEWTASSUSZPWSFGXASHFOZUKQIXBUHQJEHOZIOZTLXCGOZTLXDXEUI
      JOUJLWGXDXERLXCXERLULLLUTVAVAABKWGEGJFHIVBVCASSVDVEVJVFVGVHVIZWHWLWIWKWMB
      CWJDWKVKWMVKWHCWLWITLPZDWLBTLPZWHWGWQPXGXHVLWHWGWDWQWHVMXFVNWLWIBCWGDVOVE
      ZVPWHXGXHXIVQWHWJVRVSVTWAUDVJVFWB $.

    $( The set of right Kan extensions is a relation.  (Contributed by Zhi
       Wang, 4-Nov-2025.) $)
    relran $p |- Rel ( F ( P Ran E ) X ) $=
      ( vx vp ve cran co c0 wceq cv wcel cfv cop cfuc coppc cvv cfunc eqid wrel
      vc vd vf rel0 releq mpbiri wne wex c2nd cprcof c1st ctpos relup ne0i oveq
      cup 0ov eqtrdi necon3i cxp coppf cmpo csb df-ran elmpocl1 1st2nd2 exlimiv
      n0 syl sylbi 3syl oveq1d oveqd wa id eleqtrd ranrcl simpld opex prcofelvv
      simprd a1i ranval eqtrd releqd pm2.61ine ) CDABHIZIZUAZWIJWIJKWJJUAUEWIJU
      FUGWIJUHZELZWIMZEUIWJEWIVIWMWJEWMWJAUJNZBOZCUKIZULNZWPUJNZUMOZDWNBPIZQNZA
      ULNZBPIZQNZUQIIZUAXAXDWSDUNWMWIXEWMWICDXBWNOZBHIZIZXEWMWHXGCDWMAXFBHWMWKW
      HJUHZAXFKZWIWLUOWHJWIJWHJKWICDJIJCDWHJUPCDURUSUTXIWLWHMZEUIXJEWHVIXKXJEXK
      ARRVAZMXJFGXLRUBFLZULNUCXMUJNUDEUBLZUCLZSIXNGLZSIXOXPOUDLUKIVBNWLXOXPPIQN
      XNXPPIQNUQIIVCVDVDABHWLEGUDFUBUCVEVFARRVGVJVHVKVLVMVNZWMXBWNXDWTXCBCWQWRX
      ADWTTXCTWMCXBWNSIZMZDXBBSIMZWMWLXHMXSXTVOWMWLWIXHWMVPXQVQXBWNBCWLDVRVJZVS
      ZWMXSXTYAWBWMWPXLMWPWQWROKWMWOXRCRYBWORMWMWNBVTWCWAWPRRVGVJXATXDTWDWEWFUG
      VHVKWG $.
  $}

  ${
    islan.r $e |- R = ( D FuncCat E ) $.
    islan.s $e |- S = ( C FuncCat E ) $.
    islan.k $e |- K = ( <. D , E >. -o.F F ) $.
    $( A left Kan extension is a universal pair.  (Contributed by Zhi Wang,
       3-Nov-2025.) $)
    islan $p |- ( L e. ( F ( <. C , D >. Lan E ) X ) ->
                  L e. ( K ( R UP S ) X ) ) $=
      ( cop clan co wcel cup id cfunc lanrcl simpld simprd cprcof eqcomi lanval
      wceq a1i eleqtrd ) HFIABMENOOZPZHUIGICDQOOUJRUJABCDEFGIJKUJFABSOPZIAESOPZ
      ABEFHITZUAUJUKULUMUBBEMFUCOZGUFUJGUNLUDUGUEUH $.

    $( A left Kan extension is a universal pair.  (Contributed by Zhi Wang,
       4-Nov-2025.) $)
    islan2 $p |- ( L ( F ( <. C , D >. Lan E ) X ) A ->
                   L ( K ( R UP S ) X ) A ) $=
      ( cop clan co wcel cup wbr df-br islan 3imtr4i ) IANZGJBCNFOPPZQUCHJDERPP
      ZQIAUDSIAUESBCDEFGHUCJKLMUAIAUDTIAUETUB $.

    $d C x $.  $d D x $.  $d E x $.  $d F x $.  $d K x $.  $d R x $.  $d S x $.
    $d X x $.
    $( The set of left Kan extensions is the set of universal pairs.
       Therefore, the explicit universal property can be recovered by ~ isup2
       and ~ upciclem1 .  (Contributed by Zhi Wang, 3-Nov-2025.) $)
    lanval2 $p |- ( F e. ( C Func D ) ->
                    ( F ( <. C , D >. Lan E ) X ) = ( K ( R UP S ) X ) ) $=
      ( vx cfunc co wcel cop clan cup cv adantl islan simpr simpl fucbas simprd
      wa uprcl cprcof wceq eqcomi a1i lanval eleqtrrd impbida eqrdv ) FABMNOZLF
      HABPEQNNZGHCDRNNZUPLSZUQOZUSUROZUTVAUPABCDEFGUSHIJKUATUPVAUFZUSURUQUPVAUB
      VBABCDEFGHIJUPVAUCVAHAEMNZOZUPVAGCDMNOVDVCCDGHUSAEDJUDUGUETBEPFUHNZGUIVBG
      VEKUJUKULUMUNUO $.
  $}

  ${
    isran.o $e |- O = ( oppCat ` ( D FuncCat E ) ) $.
    isran.p $e |- P = ( oppCat ` ( C FuncCat E ) ) $.
    isran.k $e |- ( ph -> ( <. D , E >. -o.F F ) = <. J , K >. ) $.
    ${
      isran.l $e |- ( ph -> L e. ( F ( <. C , D >. Ran E ) X ) ) $.
      $( A right Kan extension is a universal pair.  (Contributed by Zhi Wang,
         4-Nov-2025.) $)
      isran $p |- ( ph -> L e. ( <. J , tpos K >. ( O UP P ) X ) ) $=
        ( cop co cfuc eqid wcel cran ctpos cfunc wa ranrcl simpld simprd ranval
        cup syl eleqtrd ) AIFKBCPEUAQQZGHUBPKJDUIQQOABCDCERQZBERQZEFGHJKUMSUNSA
        FBCUCQTZKBEUCQTZAIULTUOUPUDOBCEFIKUEUJZUFAUOUPUQUGNLMUHUK $.
    $}

    ${
      isran2.l $e |- ( ph -> L ( F ( <. C , D >. Ran E ) X ) A ) $.
      $( A right Kan extension is a universal pair.  (Contributed by Zhi Wang,
         4-Nov-2025.) $)
      isran2 $p |- ( ph -> L ( <. J , tpos K >. ( O UP P ) X ) A ) $=
        ( cop co wcel wbr ctpos cup cran df-br sylib isran sylibr ) AJBQZHIUAQL
        KEUBRRZSJBUITACDEFGHIUHKLMNOAJBGLCDQFUCRRZTUHUJSPJBUJUDUEUFJBUIUDUG $.
    $}

    $d C x $.  $d D x $.  $d E x $.  $d F x $.  $d J x $.  $d K x $.  $d O x $.
    $d P x $.  $d X x $.  $d ph x $.
    ranval2.f $e |- ( ph -> F e. ( C Func D ) ) $.
    $( The set of right Kan extensions is the set of universal pairs.
       Therefore, the explicit universal property can be recovered by ~ oppcup2
       and ~ oppcup3lem .  (Contributed by Zhi Wang, 4-Nov-2025.) $)
    ranval2 $p |- ( ph -> ( F ( <. C , D >. Ran E ) X )
                        = ( <. J , tpos K >. ( O UP P ) X ) ) $=
      ( vx cop co wcel adantr cfunc cran ctpos cup cv wa cprcof wceq simpr cfuc
      isran fucbas oppcbas uprcl simprd adantl ranval eleqtrrd impbida eqrdv
      eqid ) AOFJBCPEUAQQZGHUBPZJIDUCQQZAOUDZVARZVDVCRZAVEUEBCDEFGHVDIJKLACEPFU
      FQGHPUGZVEMSAVEUHUJAVFUEZVDVCVAAVFUHVHBCDCEUIQZBEUIQZEFGHIJVIUTVJUTZAFBCT
      QRVFNSVFJBETQZRZAVFVBIDTQRVMVLIDVBJVDVLVJDLBEVJVKUKULUMUNUOAVGVFMSKLUPUQU
      RUS $.
  $}

  ${
    $d C x $.  $d D x $.  $d E x $.  $d F x $.  $d K x $.  $d O x $.  $d P x $.
    $d X x $.
    ranval3.o $e |- O = ( oppCat ` ( D FuncCat E ) ) $.
    ranval3.p $e |- P = ( oppCat ` ( C FuncCat E ) ) $.
    ranval3.k $e |- K = ( <. D , E >. -o.F F ) $.
    $( The set of right Kan extensions is the set of universal pairs.
       (Contributed by Zhi Wang, 26-Nov-2025.) $)
    ranval3 $p |- ( F e. ( C Func D ) ->
          ( F ( <. C , D >. Ran E ) X ) = ( ( oppFunc ` K ) ( O UP P ) X ) ) $=
      ( cfunc co wcel cop cfv coppf cvv simprd adantl vx cran cprcof c1st ctpos
      c2nd cup cxp wceq opex a1i prcofelvv 1st2nd2 syl ranval2 cfuc eqid fucbas
      id cv oppcbas uprcl wa ccat funcrcl simpl prcoffunca fveq2i eqtrid oveq1d
      oppfval2 eleq2d bibiad eqrdv eqtr4d ) EABLMZNZEHABODUBMMBDOZEUCMZUDPZVSUF
      PZUEOZHGCUGMZMZFQPZHWCMZVQABCDEVTWAGHIJVQVSRRUHNVSVTWAOUIVQVRVPERVQUSZVRR
      NVQBDUJUKULVSRRUMUNWGUOVQUAWFWDVQUAUTZWFNZWHWDNZHADLMZNZWIWLVQWIWEGCLMZNW
      LWKGCWEHWHWKADUPMZCJADWNWNUQZURVAZVBSTWJWLVQWJWBWMNWLWKGCWBHWHWPVBSTVQWLV
      CZWFWDWHWQWEWBHWCWQVSBDUPMZWNLMNZWEWBUIWQABWRWNDEWRUQWLDVDNZVQWLAVDNWTADH
      VESTWOVQWLVFVGWSWEVSQPWBFVSQKVHWRWNVSVKVIUNVJVLVMVNVO $.
  $}

  ${
    lanrcl2.l $e |- ( ph -> L ( F ( <. C , D >. Lan E ) X ) A ) $.
    $( Reverse closure for left Kan extensions.  (Contributed by Zhi Wang,
       4-Nov-2025.) $)
    lanrcl2 $p |- ( ph -> F e. ( C Func D ) ) $=
      ( cfunc co wcel cop clan wa wbr df-br sylib lanrcl syl simpld ) AFCDJKLZH
      CEJKLZAGBMZFHCDMENKKZLZUBUCOAGBUEPUFIGBUEQRCDEFUDHSTUA $.

    $( Reverse closure for left Kan extensions.  (Contributed by Zhi Wang,
       4-Nov-2025.) $)
    lanrcl3 $p |- ( ph -> X e. ( C Func E ) ) $=
      ( cfunc co wcel cop clan wa wbr df-br sylib lanrcl syl simprd ) AFCDJKLZH
      CEJKLZAGBMZFHCDMENKKZLZUBUCOAGBUEPUFIGBUEQRCDEFUDHSTUA $.

    $( The first component of a left Kan extension is a functor.  (Contributed
       by Zhi Wang, 4-Nov-2025.) $)
    lanrcl4 $p |- ( ph -> L e. ( D Func E ) ) $=
      ( cfunc co cfuc cop cprcof c1st cfv wcel wbr df-br eqid c2nd cup clan syl
      sylib islan sylibr up1st2nd fucbas uprcl4 ) ADEJKDELKZCELKZDEMFNKZOPUMUAP
      BHGAUKULUMBHGAGBMZUMHUKULUBKKZQZGBUORAUNFHCDMEUCKKZQZUPAGBUQRURIGBUQSUECD
      UKULEFUMUNHUKTZULTUMTUFUDGBUOSUGUHDEUKUSUIUJ $.

    lanrcl5.n $e |- N = ( C Nat E ) $.
    $( The second component of a left Kan extension is a natural
       transformation.  (Contributed by Zhi Wang, 4-Nov-2025.) $)
    lanrcl5 $p |- ( ph -> A e. ( X N ( L o.func F ) ) ) $=
      ( cop cprcof co c1st cfv ccofu cfuc wbr eqid c2nd cup islan2 syl up1st2nd
      clan fuchom uprcl5 lanrcl4 eqidd prcof1 oveq2d eleqtrd ) ABIGDELFMNZOPZPZ
      HNIGFQNZHNADERNZCERNZUOUNUAPHBIGAURUSUNBIGAGBFICDLEUFNNSGBUNIURUSUBNNSJBC
      DURUSEFUNGIURTUSTZUNTUCUDUECEUSHUTKUGUHAUPUQIHADEFGUOABCDEFGIJUIAUOUJUKUL
      UM $.
  $}

  ${
    ranrcl2.l $e |- ( ph -> L ( F ( <. C , D >. Ran E ) X ) A ) $.
    $( Reverse closure for right Kan extensions.  (Contributed by Zhi Wang,
       4-Nov-2025.) $)
    ranrcl2 $p |- ( ph -> F e. ( C Func D ) ) $=
      ( cfunc co wcel cop cran wa wbr df-br sylib ranrcl syl simpld ) AFCDJKLZH
      CEJKLZAGBMZFHCDMENKKZLZUBUCOAGBUEPUFIGBUEQRCDEFUDHSTUA $.

    $( Reverse closure for right Kan extensions.  (Contributed by Zhi Wang,
       4-Nov-2025.) $)
    ranrcl3 $p |- ( ph -> X e. ( C Func E ) ) $=
      ( cfunc co wcel cop cran wa wbr df-br sylib ranrcl syl simprd ) AFCDJKLZH
      CEJKLZAGBMZFHCDMENKKZLZUBUCOAGBUEPUFIGBUEQRCDEFUDHSTUA $.

    $( Lemma for ~ ranrcl4 and ~ ranrcl5 .  (Contributed by Zhi Wang,
       4-Nov-2025.) $)
    ranrcl4lem $p |- ( ph -> ( <. D , E >. -o.F F ) =
                     <. ( 1st ` ( <. D , E >. -o.F F ) )
                     , ( 2nd ` ( <. D , E >. -o.F F ) ) >. ) $=
      ( cop cprcof co cvv cxp wcel c1st cfv c2nd wceq cfunc ranrcl2 a1i 1st2nd2
      opex prcofelvv syl ) ADEJZFKLZMMNOUHUHPQUHRQJSAUGCDTLFMABCDEFGHIUAUGMOADE
      UDUBUEUHMMUCUF $.

    $( The first component of a right Kan extension is a functor.  (Contributed
       by Zhi Wang, 4-Nov-2025.) $)
    ranrcl4 $p |- ( ph -> L e. ( D Func E ) ) $=
      ( cfunc co cfuc coppc cfv cop cprcof c1st c2nd ctpos eqid isran2 fucbas
      ranrcl4lem oppcuprcl4 ) ADEJKDELKZCELKMNZDEOFPKZQNZUGRNZSBUEMNZHGABCDUFEF
      UHUIGUJHUJTZUFTABCDEFGHIUCIUAUKDEUEUETUBUD $.

    ranrcl5.n $e |- N = ( C Nat E ) $.
    $( The second component of a right Kan extension is a natural
       transformation.  (Contributed by Zhi Wang, 4-Nov-2025.) $)
    ranrcl5 $p |- ( ph -> A e. ( ( L o.func F ) N X ) ) $=
      ( cop cprcof co c1st cfv ccofu cfuc coppc eqid c2nd ranrcl4lem oppcuprcl5
      ctpos isran2 fuchom ranrcl4 eqidd prcof1 oveq1d eleqtrd ) ABGDELFMNZOPZPZ
      IHNGFQNZIHNACERNZSPZUPUMULUAPZUDHBDERNSPZIGABCDUQEFUMURGUSIUSTUQTZABCDEFG
      IJUBJUEUTCEUPHUPTKUFUCAUNUOIHADEFGUMABCDEFGIJUGAUMUHUIUJUK $.
  $}

  ${
    lanup.s $e |- S = ( C FuncCat E ) $.
    lanup.m $e |- M = ( D Nat E ) $.
    lanup.n $e |- N = ( C Nat E ) $.
    lanup.x $e |- .xb = ( comp ` S ) $.
    lanup.f $e |- ( ph -> F e. ( C Func D ) ) $.
    lanup.l $e |- ( ph -> L e. ( D Func E ) ) $.
    ${
      $d .xb a b l $.  $d A a b l $.  $d C a b l $.  $d D a b l $.
      $d E a b l $.  $d F a b l $.  $d L a b l $.  $d M a b l $.  $d N a b l $.
      $d S a b l $.  $d X a b l $.  $d a b l ph $.
      lanup.a $e |- ( ph -> A e. ( X N ( L o.func F ) ) ) $.
      $( The universal property of the left Kan extension; expressed
         explicitly.  (Contributed by Zhi Wang, 4-Nov-2025.) $)
      lanup $p |- ( ph -> ( L ( F ( <. C , D >. Lan E ) X ) A
        <-> A. l e. ( D Func E ) A. a e. ( X N ( l o.func F ) )
            E! b e. ( L M l ) a = ( ( b o. ( 1st ` F ) )
        ( <. X , ( L o.func F ) >. .xb ( l o.func F ) ) A ) ) ) $=
        ( cop cprcof co c1st cfv c2nd cfuc cup wbr cv wceq wreu wral cfunc clan
        ccom ccofu eqid fucbas fuchom wcel wa natrcl simpld func1st2nd funcrcl3
        syl prcoffunca eqidd prcof1 oveq2d eleqtrrd isup lanval breqd up1st2ndb
        bitrd eqcomd ad3antrrr opeq2d ad2antrr oveq12d prcof21a oveq123d eqeq2d
        simpr reubidva raleqbidva ralbidva 3bitr4d ) AIBDGUCHUDUEZUFUGZWMUHUGZU
        CLDGUIUEZEUJUEZUEUKZMULZNULZIOULZWOUEUGZBLIWNUGZUCZXAWNUGZFUEZUEZUMZNIX
        AJUEZUNZMLXEKUEZUOZODGUPUEZUOIBHLCDUCGUQUEUEZUKZWSWTHUFUGURZBLIHUSUEZUC
        ZXAHUSUEZFUEZUEZUMZNXIUNZMLXSKUEZUOZOXMUOAOXMCGUPUEZWPMNEWNWOJKBFLIDGWP
        WPUTZVACGEPVADGWPJYGQVBCGEKPRVBSALYFVCZXQYFVCZABLXQKUEZVCYHYIVDUBBCGLXQ
        KRVEVIVFZAWPEWMACDWPEGHYGACGLUFUGLUHUGACGLYKVGVHPTVJZVGUAABYJLXCKUEUBAX
        CXQLKADGHIWNUAAWNVKVLZVMVNVOAXOIBWMLWQUEZUKWRAXNYNIBACDWPEGHWMLYGPTYKAW
        MVKVPVQAWPEWMBLIYLVRVSAYEXLOXMAXAXMVCZVDZYCXJMYDXKYPXSXELKYPXEXSYPDGHXA
        WNAYOWHYPWNVKVLZVTVMYPWSYDVCZVDZYBXHNXIYSWTXIVCZVDZYAXGWSUUAXGYAUUAXBXP
        BBXFXTUUAXDXRXEXSFUUAXCXQLAXCXQUMYOYRYTYMWAWBYPXEXSUMYRYTYQWCWDUUAWTDWO
        CDUPUEZGHIXAJQYSYTWHUUAWOVKAHUUBVCYOYRYTTWAWEUUABVKWFVTWGWIWJWKWL $.
    $}

    ${
      $d A a b l $.  $d C a b l $.  $d D a b l $.  $d E a b l $.  $d F a b l $.
      $d L a b l $.  $d M b $.  $d N a b $.  $d S a b l $.  $d X a b l $.
      $d a b l ph $.
      ranup.a $e |- ( ph -> A e. ( ( L o.func F ) N X ) ) $.
      $( The universal property of the right Kan extension; expressed
         explicitly.  (Contributed by Zhi Wang, 5-Nov-2025.) $)
      ranup $p |- ( ph -> ( L ( F ( <. C , D >. Ran E ) X ) A
        <-> A. l e. ( D Func E ) A. a e. ( ( l o.func F ) N X )
            E! b e. ( l M L ) a = ( A ( <. ( l o.func F ) , ( L o.func F ) >.
                                    .xb X ) ( b o. ( 1st ` F ) ) ) ) ) $=
        ( cop cprcof co c1st cfv c2nd ctpos cfuc coppc cup wceq wreu wral cfunc
        wbr cv cran ccom ccofu eqid fucbas fuchom wcel wa natrcl syl func1st2nd
        simprd funcrcl3 cvv cxp opex prcofelvv 1st2nd2 prcoffunca2 eqidd prcof1
        a1i oveq1d eleqtrrd oppcup fveq2i breqd simpr eqcomd ad2antrr ad3antrrr
        ranval2 opeq12d prcof21a oveq123d reubidva raleqbidva ralbidva 3bitr4d
        eqeq2d ) AIBDGUCZHUDUEZUFUGZWTUHUGZUIUCLDGUJUEZUKUGZEUKUGZULUEUEZUQMURZ
        BNURZOURZIXBUEUGZXIXAUGZIXAUGZUCZLFUEZUEZUMZNXIIJUEZUNZMXKLKUEZUOZODGUP
        UEZUOIBHLCDUCGUSUEUEZUQXGBXHHUFUGUTZXIHVAUEZIHVAUEZUCZLFUEZUEZUMZNXQUNZ
        MYDLKUEZUOZOYAUOAOYACGUPUEZXCXEFMNEXAXBJKBXDLIDGXCXCVBZVCCGEPVCDGXCJYNQ
        VDCGEKPRVDSAYEYMVEZLYMVEZABYELKUEZVEYOYPVFUBBCGYELKRVGVHVJZACDXCEGHXAXB
        YNACGLUFUGLUHUGACGLYRVIVKPTAWTVLVLVMVEWTXAXBUCUMAWSCDUPUEZHVLTWSVLVEADG
        VNVTVOWTVLVLVPVHZVQUAABYQXLLKUEUBAXLYELKADGHIXAUAAXAVRVSZWAWBXDVBZXEVBW
        CAYBXFIBACDXEGHXAXBXDLUUBECGUJUEUKPWDYTTWJWEAYLXTOYAAXIYAVEZVFZYJXRMYKX
        SUUDYDXKLKUUDXKYDUUDDGHXIXAAUUCWFUUDXAVRVSZWGWAUUDXGYKVEZVFZYIXPNXQUUGX
        HXQVEZVFZYHXOXGUUIXOYHUUIBBXJYCXNYGUUIXMYFLFUUIXKYDXLYEUUDXKYDUMUUFUUHU
        UEWHAXLYEUMUUCUUFUUHUUAWIWKWAUUIBVRUUIXHDXBYSGHXIIJQUUGUUHWFUUIXBVRAHYS
        VEUUCUUFUUHTWIWLWMWGWRWNWOWPWQ $.
    $}
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Limits and colimits
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $c Limit $.
  $c Colimit $.

  $( Class function defining the limit of a diagram. $)
  clmd $a class Limit $.

  $( Class function defining the colimit of a diagram. $)
  ccmd $a class Colimit $.

  ${
    $d C c d f $.  $d D c d f $.  $d F f $.  $d X f $.
    $( A diagram of type ` D ` or a ` D ` -shaped diagram in a category ` C ` ,
       is a functor ` F : D --> C ` where the source category ` D ` , usually
       small or even finite, is called the index category or the scheme of the
       diagram.  The actual objects and morphisms in ` D ` are largely
       irrelevant; only the way in which they are interrelated matters.  The
       diagram is thought of as indexing a collection of objects and morphisms
       in ` C ` patterned on ` D ` .  Definition 11.1(1) of [Adamek] p. 193.

       A cone to a diagram, or a natural source for a diagram in a category
       ` C ` is a pair of an object ` X ` in ` C ` and a natural transformation
       from the constant functor (or constant diagram) of the object ` X ` to
       the diagram.  The second component associates each object in the index
       category with a morphism in ` C ` whose domain is ` X ` ( ~ concl ).
       The naturality guarantees that the combination of the diagram with the
       cone must commute ( ~ concom ).  Definition 11.3(1) of [Adamek] p. 193.

       A limit of a diagram ` F : D --> C ` of type ` D ` in category ` C ` is
       a universal pair from the diagonal functor ` ( C DiagFunc D ) ` to the
       diagram.  The universal pair is a cone to the diagram satisfying the
       universal property, that each cone to the diagram uniquely factors
       through the limit ( ~ islmd ).  Definition 11.3(2) of [Adamek] p. 194.

       Terminal objects ( ~ termolmd ), products, equalizers, pullbacks, and
       inverse limits can be considered as limits of some diagram; limits can
       be further generalized as right Kan extensions ( ~ lmdran ).

       "lmd" is short for "limit of a diagram".  See ~ df-cmd for the dual
       concept ( ~ lmddu , ~ cmddu ).  (Contributed by Zhi Wang,
       12-Nov-2025.) $)
    df-lmd $a |- Limit = ( c e. _V , d e. _V |-> ( f e. ( d Func c ) |->
            ( ( oppFunc ` ( c DiagFunc d ) )
              ( ( oppCat ` c ) UP ( oppCat ` ( d FuncCat c ) ) ) f ) ) ) $.

    $( A co-cone (or cocone) to a diagram (see ~ df-lmd for definition), or a
       natural sink for a diagram in a category ` C ` is a pair of an object
       ` X ` in ` C ` and a natural transformation from the diagram to the
       constant functor (or constant diagram) of the object ` X ` .  The second
       component associates each object in the index category with a morphism
       in ` C ` whose codomain is ` X ` ( ~ coccl ).  The naturality guarantees
       that the combination of the diagram with the co-cone must commute
       ( ~ coccom ).  Definition 11.27(1) of [Adamek] p. 202.

       A colimit of a diagram ` F : D --> C ` of type ` D ` in category ` C `
       is a universal pair from the diagram to the diagonal functor
       ` ( C DiagFunc D ) ` .  The universal pair is a co-cone to the diagram
       satisfying the universal property, that each co-cone to the diagram
       uniquely factors through the colimit.  ( ~ iscmd ).  Definition 11.27(2)
       of [Adamek] p. 202.

       Initial objects ( ~ initocmd ), coproducts, coequalizers, pushouts, and
       direct limits can be considered as colimits of some diagram; colimits
       can be further generalized as left Kan extensions ( ~ cmdlan ).

       "cmd" is short for "colimit of a diagram".  See ~ df-lmd for the dual
       concept ( ~ lmddu , ~ cmddu ).  (Contributed by Zhi Wang,
       12-Nov-2025.) $)
    df-cmd $a |- Colimit = ( c e. _V , d e. _V |-> ( f e. ( d Func c ) |->
            ( ( c DiagFunc d ) ( c UP ( d FuncCat c ) ) f ) ) ) $.

    $( The domain of ` Limit ` is a relation.  (Contributed by Zhi Wang,
       12-Nov-2025.) $)
    reldmlmd $p |- Rel dom Limit $=
      ( vc vd vf cvv cv cfunc cdiag coppf cfv coppc cfuc cup cmpt clmd reldmmpo
      co df-lmd ) ABDDCBEZAEZFPSRGPHICESJIRSKPJILPPMNCABQO $.

    $( The domain of ` Colimit ` is a relation.  (Contributed by Zhi Wang,
       12-Nov-2025.) $)
    reldmcmd $p |- Rel dom Colimit $=
      ( vc vd vf cvv cv cfunc co cdiag cfuc cup cmpt ccmd df-cmd reldmmpo ) ABD
      DCBEZAEZFGPOHGCEPOPIGJGGKLCABMN $.

    $( Function value of ` Limit ` .  (Contributed by Zhi Wang,
       14-Nov-2025.) $)
    lmdfval $p |- ( C Limit D ) = ( f e. ( D Func C ) |->
            ( ( oppFunc ` ( C DiagFunc D ) )
              ( ( oppCat ` C ) UP ( oppCat ` ( D FuncCat C ) ) ) f ) ) $=
      ( vc vd cvv wa clmd co cfunc cdiag coppf cfv cv coppc cfuc cup cmpt wceq
      c0 wcel simpr simpl oveq12d fveq2d oveq12 eqidd oveq123d mpteq12dv df-lmd
      ovex mptex ovmpoa wn reldmlmd ovprc ancom reldmfunc sylnbi mpteq1d eqtrdi
      mpt0 eqtr4d pm2.61i ) AFUAZBFUAZGZABHIZCBAJIZABKIZLMZCNZAOMZBAPIZOMZQIZIZ
      RZSDEABFFCENZDNZJIZVTVSKIZLMZVLVTOMZVSVTPIZOMZQIZIZRVRHVTASZVSBSZGZCWAWHV
      IVQWKVSBVTAJWIWJUBZWIWJUCZUDWKWCVKVLVLWGVPWKWDVMWFVOQWKVTAOWMUEWKWEVNOWKV
      SBVTAPWLWMUDUEUDWKWBVJLVTAVSBKUFUEWKVLUGUHUICDEUJCVIVQBAJUKULUMVGUNZVHTVR
      ABHUOUPWNVRCTVQRTWNCVITVQVGVFVEGVITSVEVFUQBAJURUPUSUTCVQVBVAVCVD $.

    $( Function value of ` Colimit ` .  (Contributed by Zhi Wang,
       12-Nov-2025.) $)
    cmdfval $p |- ( C Colimit D ) = ( f e. ( D Func C ) |->
            ( ( C DiagFunc D ) ( C UP ( D FuncCat C ) ) f ) ) $=
      ( vc vd cvv wcel wa ccmd co cfunc cdiag cv cfuc cup cmpt oveq12d c0 ovprc
      wceq simpr simpl oveq12 eqidd oveq123d mpteq12dv df-cmd ovex mptex ovmpoa
      wn reldmcmd ancom reldmfunc sylnbi mpteq1d mpt0 eqtrdi eqtr4d pm2.61i ) A
      FGZBFGZHZABIJZCBAKJZABLJZCMZABANJZOJZJZPZTDEABFFCEMZDMZKJZVMVLLJZVGVMVLVM
      NJZOJZJZPVKIVMATZVLBTZHZCVNVRVEVJWAVLBVMAKVSVTUAZVSVTUBZQWAVOVFVGVGVQVIWA
      VMAVPVHOWCWAVLBVMANWBWCQQVMAVLBLUCWAVGUDUEUFCDEUGCVEVJBAKUHUIUJVCUKZVDRVK
      ABIULSWDVKCRVJPRWDCVERVJVCVBVAHVERTVAVBUMBAKUNSUOUPCVJUQURUSUT $.

    $( Reverse closure for a limit of a diagram.  (Contributed by Zhi Wang,
       20-Nov-2025.) $)
    lmdrcl $p |- ( X e. ( ( C Limit D ) ` F ) -> F e. ( D Func C ) ) $=
      ( vf cfunc co cdiag coppf cfv cv coppc cfuc cup clmd lmdfval mptrcl ) EBA
      FGABHGIJEKALJBAMGLJNGGABOGDCABEPQ $.

    $( Reverse closure for a colimit of a diagram.  (Contributed by Zhi Wang,
       20-Nov-2025.) $)
    cmdrcl $p |- ( X e. ( ( C Colimit D ) ` F ) -> F e. ( D Func C ) ) $=
      ( vf cfunc co cdiag cv cfuc cup ccmd cmdfval mptrcl ) EBAFGABHGEIABAJGKGG
      ABLGDCABEMN $.

    $( The domain of ` ( C Limit D ) ` is a relation.  (Contributed by Zhi
       Wang, 14-Nov-2025.) $)
    reldmlmd2 $p |- Rel dom ( C Limit D ) $=
      ( vf clmd co cdm wrel cfunc relfunc cdiag coppf cfv cv coppc cfuc lmdfval
      cup ovex dmmpti releqi mpbir ) ABDEZFZGBAHEZGBAIUCUDCUDABJEKLZCMZANLBAOEN
      LQEZEUBUEUFUGRABCPSTUA $.

    $( The domain of ` ( C Colimit D ) ` is a relation.  (Contributed by Zhi
       Wang, 13-Nov-2025.) $)
    reldmcmd2 $p |- Rel dom ( C Colimit D ) $=
      ( vf ccmd co cdm wrel cfunc relfunc cdiag cv cfuc cup ovex cmdfval dmmpti
      releqi mpbir ) ABDEZFZGBAHEZGBAITUACUAABJEZCKZABALEMEZESUBUCUDNABCOPQR $.

    $( The set of limits of a diagram.  (Contributed by Zhi Wang,
       14-Nov-2025.) $)
    lmdfval2 $p |- ( ( C Limit D ) ` F )
             = ( ( oppFunc ` ( C DiagFunc D ) )
                 ( ( oppCat ` C ) UP ( oppCat ` ( D FuncCat C ) ) ) F ) $=
      ( vf clmd co cfv cdiag coppf coppc cfuc cv wcel cfunc lmdfval mptrcl eqid
      cup fucbas oppcbas uprcl simprd oveq2 ovex fvmpt eleq2d pm5.21nii eqriv )
      DCABEFZGZABHFIGZCAJGZBAKFZJGZRFZFZDLZUJMCBANFZMZUQUPMZDURUKUQUOFZUIUQCABD
      OZPUTUKULUNNFMUSURULUNUKCUQURUMUNUNQBAUMUMQSTUAUBUSUJUPUQDCVAUPURUIUQCUKU
      OUCVBUKCUOUDUEUFUGUH $.

    $( The set of colimits of a diagram.  (Contributed by Zhi Wang,
       12-Nov-2025.) $)
    cmdfval2 $p |- ( ( C Colimit D ) ` F )
             = ( ( C DiagFunc D ) ( C UP ( D FuncCat C ) ) F ) $=
      ( vf ccmd co cfv cdiag cfuc cup cv wcel cfunc cmdfval mptrcl fucbas uprcl
      eqid simprd oveq2 ovex fvmpt eleq2d pm5.21nii eqriv ) DCABEFZGZABHFZCABAI
      FZJFZFZDKZUGLCBAMFZLZULUKLZDUMUHULUJFZUFULCABDNZOUOUHAUIMFLUNUMAUIUHCULBA
      UIUIRPQSUNUGUKULDCUPUKUMUFULCUHUJTUQUHCUJUAUBUCUDUE $.
  $}

  ${
    $d A f $.  $d B f $.  $d C f $.  $d D f $.  $d V f $.  $d f ph $.
    lmdpropd.1 $e |- ( ph -> ( Homf ` A ) = ( Homf ` B ) ) $.
    lmdpropd.2 $e |- ( ph -> ( comf ` A ) = ( comf ` B ) ) $.
    lmdpropd.3 $e |- ( ph -> ( Homf ` C ) = ( Homf ` D ) ) $.
    lmdpropd.4 $e |- ( ph -> ( comf ` C ) = ( comf ` D ) ) $.
    lmdpropd.a $e |- ( ph -> A e. V ) $.
    lmdpropd.b $e |- ( ph -> B e. V ) $.
    lmdpropd.c $e |- ( ph -> C e. V ) $.
    lmdpropd.d $e |- ( ph -> D e. V ) $.
    $( If the categories have the same set of objects, morphisms, and
       compositions, then they have the same limits.  (Contributed by Zhi Wang,
       20-Nov-2025.) $)
    lmdpropd $p |- ( ph -> ( A Limit C ) = ( B Limit D ) ) $=
      ( vf co cfv coppc chomf wceq cfunc cdiag coppf cv cfuc cup cmpt funcpropd
      clmd wcel wa cvv adantr oppchomfpropd ccomf oppccomfpropd c1st c2nd simpr
      func1st2nd funcrcl2 eleqtrd funcrcl3 fveq2d fvexd uppropd diagpropd eqidd
      fucpropd oveq123d mpteq12dva lmdfval 3eqtr4g ) AODBUAPZBDUBPZUCQZOUDZBRQZ
      DBUEPZRQZUFPZPZUGOECUAPZCEUBPZUCQZVQCRQZECUEPZRQZUFPZPZUGBDUIPCEUIPAOVNWB
      WCWJADEBCFIJGHMNKLUHZAVQVNUJZUKZVPWEVQVQWAWIWMVRWFVTWHULWMBCABSQCSQTWLGUM
      ZUNWMBCWNABUOQCUOQTWLHUMZUPWMVSWGWMVSWGSWMDEBCADSQESQTWLIUMZADUOQEUOQTWLJ
      UMZWNWOWMDBVQUQQZVQURQZWMDBVQAWLUSZUTZVAZWMECWRWSWMECVQWMVQVNWCWTAVNWCTWL
      WKUMVBUTZVAZWMDBWRWSXAVCZWMECWRWSXCVCZVIZVDZUNWMVSWGXHWMVSWGUOXGVDUPWMBRV
      EWMCRVEWMVSRVEWMWGRVEVFWMVOWDUCWMBCDEWNWOWPWQXEXFXBXDVGVDWMVQVHVJVKBDOVLC
      EOVLVM $.

    $( If the categories have the same set of objects, morphisms, and
       compositions, then they have the same colimits.  (Contributed by Zhi
       Wang, 20-Nov-2025.) $)
    cmdpropd $p |- ( ph -> ( A Colimit C ) = ( B Colimit D ) ) $=
      ( vf co chomf cfv wceq adantr cfunc cdiag cv cfuc cup cmpt ccmd funcpropd
      wcel wa ccat ccomf c1st simpr func1st2nd funcrcl2 eleqtrd funcrcl3 fveq2d
      c2nd fucpropd fuccat eqeltrrd uppropd diagpropd eqidd oveq123d mpteq12dva
      eqid cmdfval 3eqtr4g ) AODBUAPZBDUBPZOUCZBDBUDPZUEPZPZUFOECUAPZCEUBPZVNCE
      CUDPZUEPZPZUFBDUGPCEUGPAOVLVQVRWBADEBCFIJGHMNKLUHZAVNVLUIZUJZVMVSVNVNVPWA
      WEBCVOVTUKABQRCQRSWDGTZABULRCULRSWDHTZWEVOVTQWEDEBCADQREQRSWDITZADULREULR
      SWDJTZWFWGWEDBVNUMRZVNUTRZWEDBVNAWDUNZUOZUPZWEECWJWKWEECVNWEVNVLVRWLAVLVR
      SWDWCTUQUOZUPZWEDBWJWKWMURZWEECWJWKWOURZVAZUSWEVOVTULWSUSWQWRWEDBVOVOVIWN
      WQVBZWEVOVTUKWSWTVCVDWEBCDEWFWGWHWIWQWRWNWPVEWEVNVFVGVHBDOVJCEOVJVK $.
  $}

  $( The set of limits of a diagram is a relation.  (Contributed by Zhi Wang,
     14-Nov-2025.) $)
  rellmd $p |- Rel ( ( C Limit D ) ` F ) $=
    ( clmd co cfv wrel cdiag coppf coppc cfuc cup relup lmdfval2 releqi mpbir )
    CABDEFZGABHEIFZCAJFZBAKEJFZLEEZGSTRCMQUAABCNOP $.

  $( The set of colimits of a diagram is a relation.  (Contributed by Zhi Wang,
     13-Nov-2025.) $)
  relcmd $p |- Rel ( ( C Colimit D ) ` F ) $=
    ( ccmd co cfv wrel cdiag cfuc cup relup cmdfval2 releqi mpbir ) CABDEFZGABH
    EZCABAIEZJEEZGAQPCKORABCLMN $.

  ${
    islmd.l $e |- L = ( C DiagFunc D ) $.
    islmd.a $e |- A = ( Base ` C ) $.
    islmd.n $e |- N = ( D Nat C ) $.
    islmd.b $e |- B = ( Base ` D ) $.
    ${
      concl.k $e |- K = ( ( 1st ` L ) ` X ) $.
      concl.x $e |- ( ph -> X e. A ) $.
      concl.y $e |- ( ph -> Y e. B ) $.
      ${
        concl.h $e |- H = ( Hom ` C ) $.
        concl.r $e |- ( ph -> R e. ( K N F ) ) $.
        $( A natural transformation from a constant functor of an object maps
           to morphisms whose domain is the object.  Therefore, the range of
           the second component of a cone are morphisms with a common domain.
           (Contributed by Zhi Wang, 13-Nov-2025.) $)
        concl $p |- ( ph -> ( R ` Y ) e. ( X H ( ( 1st ` F ) ` Y ) ) ) $=
          ( cfv c1st co nat1st2nd natcl natrcl3 funcrcl3 funcrcl2 diag11 oveq1d
          c2nd eleqtrd ) AMFUCMIUDUCZUCZMGUDUCZUCZHUELURHUEAFCEDUOIUMUCZHUQGUMU
          CZKMPAFEDIGKPUBUFZQUATUGAUPLURHABCDEIJLMNAEDUQUTAFEDUOUSUQUTKPVAUHZUI
          AEDUQUTVBUJOSRQTUKULUN $.
      $}

      ${
        coccl.h $e |- H = ( Hom ` C ) $.
        coccl.r $e |- ( ph -> R e. ( F N K ) ) $.
        $( A natural transformation to a constant functor of an object maps to
           morphisms whose codomain is the object.  Therefore, the range of the
           second component of a co-cone are morphisms with a common codomain.
           (Contributed by Zhi Wang, 13-Nov-2025.) $)
        coccl $p |- ( ph -> ( R ` Y ) e. ( ( ( 1st ` F ) ` Y ) H X ) ) $=
          ( cfv c1st co nat1st2nd natcl natrcl2 funcrcl3 funcrcl2 diag11 oveq2d
          c2nd eleqtrd ) AMFUCMGUDUCZUCZMIUDUCZUCZHUEUPLHUEAFCEDUOGUMUCZHUQIUMU
          CZKMPAFEDGIKPUBUFZQUATUGAURLUPHABCDEIJLMNAEDUOUSAFEDUOUSUQUTKPVAUHZUI
          AEDUOUSVBUJOSRQTUKULUN $.
      $}

      concom.z $e |- ( ph -> Z e. B ) $.
      concom.m $e |- ( ph -> M e. ( Y J Z ) ) $.
      concom.j $e |- J = ( Hom ` D ) $.
      concom.o $e |- .x. = ( comp ` C ) $.
      ${
        concom.r $e |- ( ph -> R e. ( K N F ) ) $.
        $( A cone to a diagram commutes with the diagram.  (Contributed by Zhi
           Wang, 13-Nov-2025.) $)
        concom $p |- ( ph -> ( R ` Z ) = ( ( ( Y ( 2nd ` F ) Z ) ` M )
                   ( <. X , ( ( 1st ` F ) ` Y ) >. .x. ( ( 1st ` F ) ` Z ) )
                             ( R ` Y ) ) ) $=
          ( cfv c2nd c1st nat1st2nd nati ccid natrcl3 funcrcl3 funcrcl2 opeq12d
          co cop diag11 oveq1d eqidd eqid diag12 oveq123d chom funcf1 ffvelcdmd
          concl catrid eqtrd opeq1d oveqd 3eqtr3d ) APFUIZLOPJUJUIZUSUIZOJUKUIZ
          UIZPVSUIZUTZPHUKUIZUIZGUSZUSZLOPHUJUIZUSUIZOFUIZVTOWCUIZUTZWDGUSZUSVP
          WHWINWJUTZWDGUSZUSAFCEDLGVSVQIWCWGMOPSAFEDJHMSUHULZTUFUGUCUDUEUMAWFVP
          NDUNUIZUIZNNUTZWDGUSZUSVPAVPVPVRWQWEWSAWBWRWDGAVTNWANABCDEJKNOQAEDWCW
          GAFEDVSVQWCWGMSWOUOZUPZAEDWCWGWTUQZRUBUATUCVAZABCDEJKNPQXAXBRUBUATUDV
          AURVBAVPVCABCDEWPLIJKNOPQXAXBRUBUATUCUFWPVDZUDUEVEVFABDGWPVPDVGUIZNWD
          RXEVDZXDXAUBUGACBPWCACBEDWCWGTRWTVHUDVIABCDEFHXEJKMNPQRSTUAUBUDXFUHVJ
          VKVLAWLWNWHWIAWKWMWDGAVTNWJXCVMVBVNVO $.
      $}

      ${
        coccom.r $e |- ( ph -> R e. ( F N K ) ) $.
        $( A co-cone to a diagram commutes with the diagram.  (Contributed by
           Zhi Wang, 13-Nov-2025.) $)
        coccom $p |- ( ph -> ( R ` Y ) = ( ( R ` Z )
        ( <. ( ( 1st ` F ) ` Y ) , ( ( 1st ` F ) ` Z ) >. .x. X )
                             ( ( Y ( 2nd ` F ) Z ) ` M ) ) ) $=
          ( cfv c2nd co c1st cop nat1st2nd nati funcrcl3 funcrcl2 diag11 oveq2d
          natrcl2 oveqd ccid opeq2d oveq12d eqid diag12 oveq123d chom ffvelcdmd
          eqidd funcf1 coccl catlid eqtrd 3eqtr3rd ) APFUIZLOPHUJUIZUKUIZOHULUI
          ZUIZPVSUIUMZPJULUIZUIZGUKZUKLOPJUJUIZUKUIZOFUIZVTOWBUIZUMZWCGUKZUKZVP
          VRWANGUKZUKWGAFCEDLGVSVQIWBWEMOPSAFEDHJMSUHUNZTUFUGUCUDUEUOAWDWLVPVRA
          WCNWAGABCDEJKNPQAEDVSVQAFEDVSVQWBWEMSWMUTZUPZAEDVSVQWNUQZRUBUATUDURZU
          SVAAWKNDVBUIZUIZWGVTNUMZNGUKZUKWGAWFWSWGWGWJXAAWIWTWCNGAWHNVTABCDEJKN
          OQWOWPRUBUATUCURVCWQVDABCDEWRLIJKNOPQWOWPRUBUATUCUFWRVEZUDUEVFAWGVJVG
          ABDGWRWGDVHUIZVTNRXCVEZXBWOACBOVSACBEDVSVQTRWNVKUCVIUGUBABCDEFHXCJKMN
          OQRSTUAUBUCXDUHVLVMVNVO $.
      $}
    $}

    $d .x. j $.  $d A a j m x $.  $d B j $.  $d C a j m x $.  $d D a j m x $.
    $d F a j m x $.  $d H j m $.  $d L a j m x $.  $d N a j m x $.
    $d R a j m x $.  $d X a j m x $.
    islmd.h $e |- H = ( Hom ` C ) $.
    islmd.x $e |- .x. = ( comp ` C ) $.
    $( The universal property of limits of a diagram.  (Contributed by Zhi
       Wang, 14-Nov-2025.) $)
    islmd $p |- ( X ( ( C Limit D ) ` F ) R <-> (
        ( X e. A /\ R e. ( ( ( 1st ` L ) ` X ) N F ) )
     /\ A. x e. A A. a e. ( ( ( 1st ` L ) ` x ) N F ) E! m e. ( x H X )
     a = ( j e. B |-> ( ( R ` j ) ( <. x , X >. .x. ( ( 1st ` F ) ` j ) ) m ) )
     ) ) $=
      ( clmd co cfv wbr coppf coppc cfuc cup wcel c1st wa cv cop cmpt wceq wreu
      wral cdiag lmdfval2 fveq2i oveq1i eqtr4i c2nd id up1st2nd eqid oppcuprcl4
      breqi ctpos cfunc wb fucbas oppcuprcl3 simpr func1st2nd funcrcl3 funcrcl2
      diagcl oppfval2 syl oveq1d breqd syl2anc ibi fuchom oppcuprcl5 jca natrcl
      cco simprd sylan2 adantl simpl oppcup csn cxp ccat ad2antrr simplrl diag2
      oveq2d diag2cl fucco adantr opeq12d eqidd vex fvconst2 oveq123d mpteq2dva
      diag11 3eqtrd eqeq2d reubidva 2ralbidva 3bitrd biadanii bitri ) NFJDEUBUC
      UDZUENFLUFUDZJDUGUDZEDUHUCZUGUDZUIUCZUCZUEZNBUJZFNLUKUDZUDZJMUCUJZULZOUMZ
      HCHUMZFUDZIUMZAUMZNUNZYNJUKUDZUDZGUCZUCZUOZUPZIYQNKUCZUQZOYQYIUDZJMUCZURA
      BURZULNFXTYFXTDEUSUCZUFUDZJYEUCYFDEJUTYAUUKJYELUUJUFPVAVBVCVIYGYLUUIYGYHY
      KYGBDYDYAUKUDZYAVDUDZFYBJNYGYBYDYAFJNYGVEVFZYBVGZQVHZYGYDYCYILVDUDZVJZMFY
      BJNYGNFYIUURUNZJYEUCZUEZYGYHJEDVKUCZUJZYGUVAVLZUUPYGUVBYDYCUULUUMFYBJNUUN
      YDVGZEDYCYCVGZVMZVNYHUVCULZYFUUTNFUVHYAUUSJYEUVHLDYCVKUCUJZYAUUSUPUVHDEYC
      LPUVHEDYSJVDUDZUVHEDJYHUVCVOVPZVQZUVHEDYSUVJUVKVRZUVFVSZDYCLVTWAWBWCZWDWE
      UVEEDYCMUVFRWFZWGWHYLYGUVAYMFYPYQNUUQUCUDZUUGYJUNJYCWJUDZUCZUCZUPZIUUEUQZ
      OUUHURABURUUIYKYHUVCUVDYKYJUVBUJUVCFEDYJJMRWIWKZUVOWLYLABUVBDYDUVROIYCYIU
      UQKMFYBJNQUVGTUVPUVRVGZYKUVCYHUWCWMYLDYCLYKYHUVCUVIUWCUVNWLVPYHYKWNZYHYKV
      OZUUOUVEWOYLUWBUUFAOBUUHYLYQBUJZYMUUHUJZULZULZUWAUUDIUUEUWJYPUUEUJZULZUVT
      UUCYMUWLUVTFCYPWPWQZUVSUCHCYOYNUWMUDZYNUUGUKUDUDZYNYJUKUDUDZUNZYTGUCZUCZU
      OUUCUWLUVQUWMFUVSUWLBCDEYPKLYQNPQSTYLDWRUJZUWIUWKYKYHUVCUWTUWCUVLWLWSZYLE
      WRUJZUWIUWKYKYHUVCUXBUWCUVMWLWSZYLUWGUWHUWKWTZYLYHUWIUWKUWEWSZUWJUWKVOZXA
      XBUWLHCEDYCUWMFUVRGUUGYJJMUVFRSUAUWDUWLBCDEYPKLMYQNPQSTUXAUXCUXDUXEUXFRXC
      YLYKUWIUWKUWFWSXDUWLHCUWSUUBUWLYNCUJZULZYOYOUWNYPUWRUUAUXHUWQYRYTGUXHUWOY
      QUWPNUXHBCDEUUGLYQYNPUWLUWTUXGUXAXEZUWLUXBUXGUXCXEZQUWLUWGUXGUXDXEUUGVGSU
      WLUXGVOZXLUXHBCDEYJLNYNPUXIUXJQUWLYHUXGUXEXEYJVGSUXKXLXFWBUXHYOXGUXGUWNYP
      UPUWLCYPYNIXHXIWMXJXKXMXNXOXPXQXRXS $.

    $d H a j m x $.
    $( The universal property of colimits of a diagram.  (Contributed by Zhi
       Wang, 13-Nov-2025.) $)
    iscmd $p |- ( X ( ( C Colimit D ) ` F ) R <-> (
        ( X e. A /\ R e. ( F N ( ( 1st ` L ) ` X ) ) )
     /\ A. x e. A A. a e. ( F N ( ( 1st ` L ) ` x ) ) E! m e. ( X H x )
     a = ( j e. B |-> ( m ( <. ( ( 1st ` F ) ` j ) , X >. .x. x ) ( R ` j ) ) )
     ) ) $=
      ( ccmd co cfv wbr cfuc cup wcel c1st wa cop cmpt wceq wreu cdiag cmdfval2
      cv wral oveq1i eqtr4i breqi c2nd id up1st2nd uprcl4 fuchom uprcl5 jca cco
      eqid cfunc natrcl adantl simpld funcrcl3 funcrcl2 diagcl up1st2ndb fucbas
      func1st2nd simpl simpr isup csn cxp ad2antrr simplrl diag2 oveq1d diag2cl
      ccat fucco adantr diag11 opeq2d oveq12d fvconst2 eqidd oveq123d mpteq2dva
      vex 3eqtrd eqeq2d reubidva 2ralbidva 3bitrd biadanii bitri ) NFJDEUBUCUDZ
      UENFLJDEDUFUCZUGUCZUCZUEZNBUHZFJNLUIUDZUDZMUCUHZUJZOUQZHCIUQZHUQZFUDZYAJU
      IUDZUDZNUKZAUQZGUCZUCZULZUMZINYFKUCZUNZOJYFXOUDZMUCZURABURZUJNFXIXLXIDEUO
      UCZJXKUCXLDEJUPLYPJXKPUSUTVAXMXRYOXMXNXQXMBDXJXOLVBUDZFJNXMDXJLFJNXMVCVDZ
      QVEXMDXJXOYQMFJNYREDXJMXJVJZRVFZVGVHXRXMNFXOYQUKJXKUCUEXSXTNYFYQUCUDZFJXP
      UKYMXJVIUDZUCZUCZUMZIYKUNZOYNURABURYOXRDXJLFJNXRDEXJLPXREDYCJVBUDZXREDJXR
      JEDVKUCZUHZXPUUHUHZXQUUIUUJUJXNFEDJXPMRVLVMVNZVTZVOZXREDYCUUGUULVPZYSVQZV
      RXRABUUHDOIXJXOYQKMFUUBJNQEDXJYSVSTYTUUBVJZUUKXRDXJLUUOVTXNXQWAZXNXQWBZWC
      XRUUFYLAOBYNXRYFBUHZXSYNUHZUJZUJZUUEYJIYKUVBXTYKUHZUJZUUDYIXSUVDUUDCXTWDW
      EZFUUCUCHCYAUVEUDZYBYDYAXPUIUDUDZUKZYAYMUIUDUDZGUCZUCZULYIUVDUUAUVEFUUCUV
      DBCDEXTKLNYFPQSTXRDWKUHZUVAUVCUUMWFZXREWKUHZUVAUVCUUNWFZXRXNUVAUVCUUQWFZX
      RUUSUUTUVCWGZUVBUVCWBZWHWIUVDHCEDXJFUVEUUBGJXPYMMYSRSUAUUPXRXQUVAUVCUURWF
      UVDBCDEXTKLMNYFPQSTUVMUVOUVPUVQUVRRWJWLUVDHCUVKYHUVDYACUHZUJZUVFXTYBYBUVJ
      YGUVTUVHYEUVIYFGUVTUVGNYDUVTBCDEXPLNYAPUVDUVLUVSUVMWMZUVDUVNUVSUVOWMZQUVD
      XNUVSUVPWMXPVJSUVDUVSWBZWNWOUVTBCDEYMLYFYAPUWAUWBQUVDUUSUVSUVQWMYMVJSUWCW
      NWPUVSUVFXTUMUVDCXTYAIXAWQVMUVTYBWRWSWTXBXCXDXEXFXGXH $.
  $}

  ${
    $d C f g m x $.  $d D f g m x $.  $d F f g m x $.  $d G f g m x $.
    $d O f g m x $.  $d P f g m x $.  $d V f g m x $.  $d W f g m x $.
    $d f g m ph x $.
    lmddu.o $e |- O = ( oppCat ` C ) $.
    lmddu.p $e |- P = ( oppCat ` D ) $.
    lmddu.g $e |- G = ( oppFunc ` F ) $.
    lmddu.c $e |- ( ph -> C e. V ) $.
    lmddu.d $e |- ( ph -> D e. W ) $.
    $( The duality of limits and colimits: limits of a diagram are colimits of
       an opposite diagram in opposite categories.  (Contributed by Zhi Wang,
       20-Nov-2025.) $)
    lmddu $p |- ( ph -> ( ( C Limit D ) ` F ) = ( ( O Colimit P ) ` G ) ) $=
      ( co coppf cfv wcel eqid syl vx vm vf vg cdiag coppc cfuc cup clmd oveq1i
      ccmd oveqi relup cv wbr simpr wa cfunc cbs c1st cnat adantr c2nd up1st2nd
      wb fucbas uprcl3 eqeltrrid funcoppc5 oppcuprcl4 fuchom uprcl5 wceq simprd
      ccat funcrcl simpld diagcl oppf1 fveq1d fveq2d oppfdiag1a eqtr2d natoppfb
      a1i eleqtrrd w3a cop cres cid cmpo simp1 fvresd eqtr4di eqidd fucoppcffth
      chom 3ad2ant1 ccofu oppfdiag wrel relfunc oppfoppc2 1st2nd sylancr oveq2d
      oppccat 3eqtr3d oppcbas func1st2nd diag1cl eqeltrd opf2 oppchom eleqtrrdi
      simp2 simp3 up1st2ndb 3bitr4d syl3anc mpbird oppcuprcl3 oppcuprcl5 bibiad
      uptr eqbrrdiv eqtr3id lmdfval2 cmdfval2 3eqtr4g ) ABCUEOZPQZEBUFQZCBUGOZU
      FQZUHOZOZGDUEOZFGDGUGOZUHOZOZEBCUIOQFGDUKOQAYQYLEGYOUHOZOZUUAUUBYPYLEGYMY
      OUHJUJULAUAUBUUCUUAGYOYLEUMGYSYRFUMAUAUNZUBUNZUUCUOZUUDUUEUUAUOZUUFAUUFUP
      ZAUUGUQZUUFUUGAUUGUPZUUIECBUROZRZUUDBUSQZRZUUEUUDYLUTQZQZECBVAOZOZRZUUFUU
      GVEZUUICBGEDIHKJACIRUUGNVBZABHRUUGMVBZUUIEPQZFDGUROZLUUIUVDGYSYRUTQZYRVCQ
      ZUUEFUUDUUIGYSYRUUEFUUDUUJVDZDGYSYSSZVFVGVHVIZUUIUUMBYSUVEUVFUUEGFUUDUVGJ
      UUMSZVJZUUIUUEFUUDUVEQZDGVAOZOUURUUIGYSUVEUVFUVMUUEFUUDUVGDGYSUVMUVHUVMSZ
      VKVLUUICBGUUPEUVLFUVMUUQDIHKJUUQSZUVNUUIUUPPQZUUDYKUTQZQZPQZUVLUUIUULUVPU
      VSVMUVIUULUUPUVRPUULUUDUUOUVQUULBYNYKUULBCYNYKYKSZUULCVORZBVORZCBEVPZVNZU
      ULUWAUWBUWCVQZYNSZVRZVSVTZWATUUIUUMBCDYKGUUDJKUVTUUIUULUWBUVIUWDTUUIUULUW
      AUVIUWETUVJUVKWBWCFUVCVMUUILWEUVAUVBWDWFUULUUNUUSWGZUUDUUEUUOYLVCQZWHZEUU
      BOUOUUDUUEUVEUVFWHZFYTOUOUUFUUGUWIUUKGYOPUUKWIZUCUDUUKUUKWJUDUNUCUNUUQOWI
      WKZYSUUOUWJYOWQQZUVEUVFUUEUUEEFUUDUWIEUWMQUVCFUWIEUUKPUULUUNUUSWLZWMLWNUW
      IUCUDCBGYNYOYSUWMUWNUUQDKJUWFYOSZUVHUVOUWIUWMWOZUWIUWNWOZUULUUNUWAUUSUWEW
      RZUULUUNUWBUUSUWDWRZWPUWIUWMUWNWHZYLWSOYRUXBUWKWSOUWLUWIBCDUCUDUWMUWNYKUU
      QGJKUVTUXAUWTUWRUVOUWSWTUWIYLUWKUXBWSUWIGYOUROZXAYLUXCRZYLUWKVMGYOXBUWIUU
      LUXDUWPUULBYNYOYKGJUWQUWGXCTZYLUXCXDXEXFUWIGYSUROZXAYRUXFRYRUWLVMGYSXBUWI
      GDYSYRYRSUWIUWBGVORUXABGJXGTUWIUWADVORUWTCDKXGTUVHVRZYRUXFXDXEXHUUKYNYOUW
      QCBYNUWFVFZXIUWPUWIGYOYLUXEXJUWIUCUDUUKUUKUUEUUEUWNUUQEUUPUWSUWPUWIUUPUVR
      UUKUWIUULUUPUVRVMUWPUWHTUWIUUMBCUVRYKUUDUVTUXAUWTUVJUULUUNUUSXPUVRSXKXLUW
      IUUEWOUULUUNUUSXQZXMUWOSUWIUUEUUREUUPUWOOUXIYNUUQYOEUUPCBYNUUQUWFUVOVKZUW
      QXNXOYEUWIGYOYLUUEEUUDUXEXRUWIGYSYRUUEFUUDUXGXRXSZXTYAAUUFUQZUULUUNUUSUUT
      UXLUUKYOYNUUOUWJUUEGEUUDUXLGYOYLUUEEUUDUUHVDZUWQUXHYBUXLUUMBYOUUOUWJUUEGE
      UUDUXMJUVJVJUXLYOYNUUOUWJUUQUUEGEUUDUXMUWQUXJYCUXKXTYDYFYGBCEYHGDFYIYJ $.

    $( The duality of limits and colimits: colimits of a diagram are limits of
       an opposite diagram in opposite categories.  (Contributed by Zhi Wang,
       20-Nov-2025.) $)
    cmddu $p |- ( ph -> ( ( C Colimit D ) ` F ) = ( ( O Limit P ) ` G ) ) $=
      ( co cfv wcel cvv a1i ccat vx vm ccmd coppf coppc clmd cdiag cup relup cv
      cfuc wbr cfunc wa c1st c2nd simpr up1st2nd fucbas uprcl3 adantr funcoppc5
      eqid fvexi eqeltrrid chomf wceq 2oppchomf ccomf 2oppccomf funcrcl oppccat
      simpld simprd fucpropd fveq2d fuccat eqeltrrd uppropd diagpropd oppfoppc2
      3syl id eqeltrid relfunc 2oppf eqcomd oveq123d pm5.21nd eqbrrdiv cmdfval2
      breqd 3eqtr4g lmddu eqtr4d ) AEBCUCOPZFUDPZGUEPZDUEPZUCOPZFGDUFOPABCUGOZE
      BCBUKOZUHOZOZWRWSUGOZWQWRWSWRUKOZUHOZOZWPWTAUAUBXDXHBXBXAEUIWRXFXEWQUIAUA
      UJZUBUJZXDULZXIXJXHULZECBUMOZQZAXKUNZXMBXBXAUOPXAUPPXJEXIXOBXBXAXJEXIAXKU
      QURCBXBXBVCZUSUTAXLUNZCBGEDIHKJACIQXLNVAABHQXLMVAXQEUDPZFDGUMOZLXQDGWRFWS
      RRWSVCZWRVCZDRQZXQDCUEKVDZSGRQZXQGBUEJVDZSXQWSWRUMOWRXFXEUOPXEUPPXJWQXIXQ
      WRXFXEXJWQXIAXLUQURWSWRXFXFVCUSUTVBVEVBXNXDXHXIXJXNXAXEEWQXCXGXNBWRXBXFTB
      VFPWRVFPVGXNBGJVHSZBVIPWRVIPVGXNBGJVJSZXNXBXFVFXNCWSBWRCVFPWSVFPVGXNCDKVH
      SZCVIPWSVIPVGXNCDKVJSZYFYGXNCTQZBTQZCBEVKZVMZXNYJDTQWSTQYMCDKVLDWSXTVLWBZ
      XNYJYKYLVNZXNYKGTQWRTQYOBGJVLGWRYAVLWBZVOZVPXNXBXFVIYQVPYOYPXNCBXBXPYMYOV
      QZXNXBXFTYQYRVRVSXNBWRCWSYFYGYHYIYOYPYMYNVTXNWQEXNXSEFXNFXRXSLXNCBGEDKJXN
      WCWAWDDGWELWFWGWHWLWIWJBCEWKWRWSWQWKWMAGDWSFWQWRRRYAXTWQVCYDAYESYBAYCSWNW
      O $.
  $}

  ${
    $d C f g x y z $.
    $( Initial objects are the object part of colimits of the empty diagram.
       (Contributed by Zhi Wang, 17-Nov-2025.) $)
    initocmd $p |- ( InitO ` C ) = dom ( (/) ( C Colimit (/) ) (/) ) $=
      ( vx cinito cfv c0 cdiag cop cfuc cup cdm ccmd wcel ccat initorcl cvv a1i
      co cv cbs eqid uobrcl simpld 0ex wceq base0 0fucterm csn opex snid fucbas
      id cfunc 0func eqtr3id eleqtrrid diagcl isinito4 pm5.21nii eqriv cmdfval2
      0cat df-ov eqtri dmeqi eqtr4i ) ACDZAEFQZEEGZAEAHQZIQQZJZEEAEKQZQZJBVFVKB
      RZVFLAMLZVNVKLZAVNNVPVOVIMLAVIVGVHVNUAUBVOAVIVGVNVHVOEAVIOEOLVOUCPEESDUDV
      OUEPVOUKZVITZUFVOVHVHUGZVISDZVHEEUHUIVOVTEAULQVSEAVIVRUJVOAVQUMUNUOVOAEVI
      VGVGTVQEMLVOVAPVRUPUQURUSVMVJVMVHVLDVJEEVLVBAEVHUTVCVDVE $.

    $( Terminal objects are the object part of limits of the empty diagram.
       (Contributed by Zhi Wang, 20-Nov-2025.) $)
    termolmd $p |- ( TermO ` C ) = dom ( (/) ( C Limit (/) ) (/) ) $=
      ( vx vy vg vf vz cfv c0 co wcel ccat coppc wceq a1i chomf eqid ccomf wral
      cv cvv ctermo cop clmd cdm termorcl wbr eldm c1st c2nd cfunc df-br lmdrcl
      wex vex sylbi func1st2nd funcrcl3 exlimiv cinito initocmd oppctermo eqriv
      ccmd coppf 2oppchomf 2oppccomf chom ral0 cbs oppcbas homfeq mpbiri comfeq
      base0 cco elex fvexd lmdpropd ctpos eqidd 0funcg2 mpbir2and oppfval tpos0
      0ex opeq2i eqtr2di fveq12d df-ov cmddu eqtrid eqtr4d dmeqd 3eqtr4a eleq2d
      0cat syl pm5.21nii dmeqi eqtr4i ) AUAGZHHUBZAHUCIZGZUDZHHXCIZUDBXAXEBSZXA
      JAKJZXGXEJZAXGUEXIXGCSZXDUFZCUMXHCXGXDBUNUGXKXHCXKHAXBUHGXBUIGXKHAXBXKXGX
      JUBZXDJXBHAUJIJXGXJXDUKAHXBXLULUOUPUQURUOXHXAXEXGXHALGZUSGZHHXMHVCIZIZUDX
      AXEXMUTXAXNMXHBXAXNAXGVAVBNXHXDXPXHXDHHVDIZXMLGZHLGZUCIZGZXPXHXBXQXCXTXHA
      XRHXSTAOGXROGMXHAXMXMPZVENAQGXRQGMXHAXMYBVFNXHHOGXSOGMXGXJHVGGZIZXGXJXSVG
      GZIMCHRZBHRYFBVHXHBCHHXSYCYEYCPZYEPHHVIGMXHVNNZHXSVIGMXHHHXSXSPZVNVJNZVKV
      LZXHHQGXSQGMDSZESZXLFSZHVOGZIIYLYMXLYNXSVOGZIIMDXJYNYCIREYDRFHRCHRZBHRYQB
      VHXHBCFHHXSYPYOEDYCYOPYPPYGYHYJYKVMVLAKVPXHXMLVQHTJXHWENZXHHLVQVRXHXQHHVS
      ZUBZXBXHHHHHUJIUFZXQYTMXHUUAHHMZUUBXHHVTZUUCXHHHHHKHKJXHWPNZYHUUDWAWBHHHH
      WCWQYSHHWDWFWGWHXHXPXBXOGYAHHXOWIXHXMHXSXBXQXRTTXRPYIHHVDWIXHALVQYRWJWKWL
      WMWNWOWRVBXFXDHHXCWIWSWT $.
  $}

  ${
    lmdran.1 $e |- ( ph -> .1. e. TermCat ) $.
    lmdran.g $e |- ( ph -> G e. ( D Func .1. ) ) $.
    lmdran.l $e |- L = ( C DiagFunc .1. ) $.
    lmdran.y $e |- ( ph -> Y = ( ( 1st ` L ) ` X ) ) $.
    $( To each limit of a diagram there is a corresponding right Kan extention
       of the diagram along a functor to a terminal category.  The morphism
       parts coincide, while the object parts are one-to-one correspondent
       ( ~ diag1f1o ).  (Contributed by Zhi Wang, 26-Nov-2025.) $)
    lmdran $p |- ( ph -> ( X ( ( C Limit D ) ` F ) M
                       <-> Y ( G ( <. D , .1. >. Ran C ) F ) M ) ) $=
      ( co cfv wcel wa c1st eqid clmd wbr cdiag coppf coppc cfuc cup cran breqi
      cop lmdfval2 cprcof cfunc cbs simpr up1st2nd fucbas oppcuprcl3 oppcuprcl4
      c2nd jca cdm c0 wne wceq adantr relfunc oppfrcllem eqnetrrd csn cres wfun
      fvfundmfvn0 simpld syl wf1o ctermc func1st2nd funcrcl3 diag1f1o f1of fdmd
      wf syldan eleqtrd oppcbas ccat termccatd diagcl oppf1 fveq1d eqtr4d eqidd
      adantrr prcofdiag prcoffunca cofuoppf oppfoppc2 diagffth ffthoppf f1oeq1d
      simprr wfo mpbird f1ofo uptr2a bibiad ranval3 breqd bitr4d bitrid ) IHEBC
      UAOPZUBIHBCUCOZUDPZEBUEPZCBUFOZUEPZUGOOZUBZAJHFECDUJBUHOOZUBZIHXLXRBCEUKU
      IAXSJHDBUJFULOZUDPZEDBUFOZUEPZXQUGOOZUBZYAAXSYGECBUMOZQZIBUNPZQZRZAXSRZYI
      YKYMYHXQXPXNSPZXNUTPZHXOEIYMXOXQXNHEIAXSUOUPZXQTZCBXPXPTZUQZURYMYJBXQYNYO
      HXOEIYPXOTZYJTZUSVAAYGRZYIYKUUBYHXQXPYCSPZYCUTPZHYEEJUUBYEXQYCHEJAYGUOUPZ
      YQYSURZUUBIGSPZVBZYJUUBIUUGPZVCVDZIUUHQZUUBJUUIVCAJUUIVEZYGNVFUUBDBUMOZJU
      UBUUMYDXQUUCUUDHYEEJUUEYETZDBYDYDTZUQZUSDBVGVHVIUUJUUKUUGIVJVKVLIUUGVMVNV
      OAYGYIUUHYJVEUUFAYIRZYJUUMUUGUUQYJUUMUUGVPZYJUUMUUGWCUUQYJBDGUUAADVQQZYIK
      VFUUQCBESPEUTPUUQCBEAYIUOVRVSZMVTZYJUUMUUGWAVOWBWDWEVAAYLRZYJUUMXOYEXQXNY
      CGUDPZHIJEYJBXOYTUUAWFUUMYDYEUUNUUPWFUVBJUUIIUVCSPZPAUULYLNVFUVBIUVDUUGUV
      BBYDGUVBBDYDGMAYIBWGQYKUUTWNZUVBDAUUSYLKVFZWHUUOWIZWJZWKWLUVBBYDXPGYBXMUV
      BBDCFYBGXMMXMTAFCDUMOQZYLLVFZUVEUVBYBWMWOUVGUVBCDYDXPBFUUOUVEYRUVJWPZWQAY
      IYKXBUVBYDXPXQYBYEUUNYQUVKWRUVBBYDYEGXOYTUUNUVBBDYDGUVEUVFUUOMWSWTUVBYJUU
      MUVDVPZYJUUMUVDXCUVBUVLUURAYIUURYKUVAWNUVBYJUUMUVDUUGUVHXAXDYJUUMUVDXEVOX
      FXGAXTYFJHAUVIXTYFVELCDXQBFYBYEEUUNYQYBTXHVOXIXJXK $.

    $( To each colimit of a diagram there is a corresponding left Kan extention
       of the diagram along a functor to a terminal category.  The morphism
       parts coincide, while the object parts are one-to-one correspondent
       ( ~ diag1f1o ).  (Contributed by Zhi Wang, 26-Nov-2025.) $)
    cmdlan $p |- ( ph -> ( X ( ( C Colimit D ) ` F ) M
                       <-> Y ( G ( <. D , .1. >. Lan C ) F ) M ) ) $=
      ( co cfv wbr wcel wa eqid ccmd cdiag cfuc cup cop clan breqi cprcof cfunc
      cmdfval2 cbs c1st c2nd simpr up1st2nd fucbas uprcl3 uprcl4 jca cdm c0 wne
      wceq adantr relfunc oppfrcllem eqnetrrd cres wfun fvfundmfvn0 simpld wf1o
      csn syl ctermc func1st2nd funcrcl3 diag1f1o f1of fdmd syldan eleqtrd ccat
      wf adantrr eqidd prcofdiag simprr prcoffunca cful cfth cin diagffth f1ofo
      wfo uptr2a bibiad lanval2 breqd bitr4d bitrid ) IHEBCUAOPZQIHBCUBOZEBCBUC
      OZUDOOZQZAJHFECDUEBUFOOZQZIHXBXEBCEUJUGAXFJHDBUEFUHOZEDBUCOZXDUDOOZQZXHAX
      FXLECBUIOZRZIBUKPZRZSZAXFSZXNXPXRXMBXDXCULPZXCUMPZHEIXRBXDXCHEIAXFUNUOZCB
      XDXDTZUPZUQXRXOBXDXSXTHEIYAXOTZURUSAXLSZXNXPYEXMXJXDXIULPZXIUMPZHEJYEXJXD
      XIHEJAXLUNUOZYCUQZYEIGULPZUTZXOYEIYJPZVAVBZIYKRZYEJYLVAAJYLVCZXLNVDYEDBUI
      OZJYEYPXJXDYFYGHEJYHDBXJXJTZUPZURDBVEVFVGYMYNYJIVMVHVIIYJVJVKVNAXLXNYKXOV
      CYIAXNSZXOYPYJYSXOYPYJVLZXOYPYJWDYSXOBDGYDADVORXNKVDZYSCBEULPEUMPYSCBEAXN
      UNVPVQZMVRZXOYPYJVSVNVTWAWBUSAXQSZXOYPBXJXDXCXIGHIJEYDYRAYOXQNVDUUDBDCFXI
      GXCMXCTAFCDUIORZXQLVDZAXNBWCRXPUUBWEZUUDXIWFWGAXNXPWHUUDCDXJXDBFYQUUGYBUU
      FWIAXNGBXJWJOBXJWKOWLRXPYSBDXJGUUBUUAYQMWMWEAXNXOYPYJWOZXPYSYTUUHUUCXOYPY
      JWNVNWEWPWQAXGXKJHAUUEXGXKVCLCDXJXDBFXIEYQYBXITWRVNWSWTXA $.
  $}

$( (End of Zhi Wang's mathbox.) $)
